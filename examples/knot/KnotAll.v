Require Import CRIS Cancel.
Require Import MemHeader MemI MemA MemIAproof.
Require Import APCHeader APC APCA APCC APCACproof.
Require Import KnotHeader KnotMainHeader KnotI KnotMainI.
Require Import KnotA KnotMainA.
Require Import KnotIAproof KnotMainIAproof.

Module KnotAll. Section KnotAll.
  Import inv_instances.
  Local Instance Γ : HRA := ##[invΓ; memΓ; KnotAΓ].
  Local Instance Σ : GRA := ##[invΣ; Γ].

  (* global environment *)
  Local Definition genv : GEnv.t := KnotGEnv.t ++ KnotMainGEnv.t.

  (* pure spc *)
  Local Definition spc_rec : string → option fspec := 
    λ fn, to_spc KnotA.KnotRecSpc fn.
  Local Definition spc_fun : string → option fspec :=
    λ fn, to_spc (KnotMainA.MainFunSpc genv spc_rec) fn.
  Local Definition spc_pure : string → option fspec :=
    λ fn, to_spc (KnotA.KnotRecSpc ++ (KnotMainA.MainFunSpc genv spc_rec)) fn.

  (* mem *)
  Local Definition csl : string → bool := λ _, false.

  Local Definition smod_src_apc : SMod.t :=
    (KnotMainA.Mod genv spc_rec) ☆ (KnotA.Mod genv spc_rec spc_fun)
    ☆ MemA.Mod ☆ (APCA.Mod spc_pure).
  Local Definition smod_src : SMod.t :=
    (KnotMainA.Mod genv spc_rec) ☆ (KnotA.Mod genv spc_rec spc_fun)
    ☆ MemA.Mod ☆ APCC.Mod.
  Local Definition ginv : invspec := λ _, True%I.
  Local Definition spc_apc : string → option fspec := spc_from smod_src_apc.
  Local Definition spc : string → option fspec := spc_from smod_src.
  Local Definition mod_cancel : HMod.t := SModCancel.to_hmod smod_src.
  Local Definition mod_src : HMod.t := SMod.to_hmod ginv spc smod_src.
  Local Definition mod_tgt : HMod.t :=
    (KnotMainI.t genv) ★ (KnotI.t genv) ★ (MemI.t csl genv).

  Local Definition main_fsp : fspec := KnotMainA.main_spec.
  Local Lemma genv_wf : GEnv.wf genv.
  Proof. cbn. prove_nodup. Qed.
  Local Definition init_cond : iProp Σ :=
    KnotMainA.InitCond ∗ (KnotA.InitCond genv) ∗ (MemA.InitCond csl genv).

  Lemma cancel_src :
    refines (mod_cancel, (init_cond ∗ main_fsp.(precond) 0 tt tt↑ tt↑)%I)
            ((mod_src, init_cond) : HMod.modc).
  Proof.
    eapply cancellation; try by econs.
    i. iIntros "%POST". iPureIntro.
    des; eauto.
  Qed.

  Lemma spc_spc_apc_eq : spc_apc = spc.
  Proof.
    unfold spc_apc, spc, spc_from, smod_src, smod_src_apc.
    extensionalities fn. ss. des_ifs; rewrite ->eq_rel_dec_correct in *.
  Qed.

  Lemma ctxr_empty (m : HMod.t) (P : iProp Σ) :
    ctx_refines (m, P) (⌽, emp%I).
  Proof.
    eapply main_adequacy.
    econs.
    { instantiate (1:=λ _ _ _, True%I). et. }
    { eauto. }
    { prove_sub_perm. }
    { prove_sub_perm. }
    ss.
  Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    eapply ctxr_refines.
    unfold mod_src, mod_tgt. rewrite !add_interp_comm.
    rewrite -(hmod_add_empty_l ((KnotMainI.t genv) ★ _ ★ _)).
    etrans; cycle 1.
    { apply ctxr_frameR. eapply ctxr_empty. }
    instantiate (1:=emp%I). instantiate (1:=APCA.t ginv spc_pure spc).
    replace (SMod.to_hmod ginv spc (KnotMainA.Mod _ _)) with (KnotMainA.t genv ginv spc_rec spc); cycle 1.
    { unfold KnotMainA.t; unseal CRIS; ss. }
    replace (SMod.to_hmod ginv spc (KnotA.Mod _ _ _)) with (KnotA.t genv ginv spc_rec spc_fun spc); cycle 1.
    { unfold KnotA.t; unseal CRIS; ss. }
    replace (SMod.to_hmod ginv spc MemA.Mod) with (MemA.t ginv spc); cycle 1.
    { unfold MemA.t; unseal CRIS; ss. }
    replace (SMod.to_hmod ginv spc APCC.Mod) with (APCC.t ginv spc); cycle 1.
    { unfold APCC.t; unseal CRIS; ss. }
    (* APC Cancellation *)
    rewrite -!hmod_add_assoc.
    etrans. { eapply ctxr_comm. }
    etrans; cycle 1. { eapply ctxr_comm. }
    etrans.
    { eapply APCAC.correct.
      { instantiate (1:=spc_apc). unfold spc_incl, APCA.Spc, spc_apc. unseal CRIS.
        prove_nodup. unfold spc_sub, to_spc. ss. des_ifs; i; rewrite ->eq_rel_dec_correct in *; des_ifs. }
      { instantiate (1:=spc_pure). unfold spc_apc, smod_src_apc, spc_pure, to_spc, spc_from, spc_sub.
        unfold KnotA.KnotRecSpc, KnotMainA.MainFunSpc. unseal CRIS. ss. i.
        des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs; revert H; unseal CRIS; ss.
      }
      { i. unfold spc_pure, to_spc, KnotA.KnotRecSpc, KnotMainA.MainFunSpc in *.
        revert H; unseal CRIS. i; ss. rewrite -> eq_rel_dec_correct in *; des_ifs.
        { eexists. unfold find_body, pure_specbody; ss. unfold KnotMainA.t, KnotA.t.
          unseal CRIS. s. unfold pure_body. rewrite spc_spc_apc_eq. refl. }
        { rewrite -> eq_rel_dec_correct in *; ss. des_ifs.
          eexists. unfold find_body, pure_specbody; ss. unfold KnotMainA.t, KnotA.t.
          unseal CRIS. s. unfold pure_body. rewrite spc_spc_apc_eq. refl. }
      }
    }
    rewrite !spc_spc_apc_eq.

    rewrite hmod_add_assoc.
    etrans. { eapply ctxr_comm. }
    etrans; cycle 1. { eapply ctxr_comm. }
    rewrite !hmod_add_assoc.

    rewrite -(hmod_add_empty_r ((KnotMainA.t _ _ _ _) ★ _ ★ _ ★ _)).
    unfold init_cond.
    etrans.
    { eapply ctxr_compose_hor; [|refl]. eapply KnotMainIA.correct; et.
      { apply genv_wf. }
      { unfold incl. i. unfold KnotMainGEnv.t in H. ss. des; ss; tauto. }
      { i. unfold spc_incl, spc_fun, KnotMainA.MainFunSpc. unseal CRIS. prove_nodup. ss. }
      { i. unfold APCA.Spc, spc. unseal CRIS. unfold spc_incl, KnotA.KnotRecSpc.
        unseal CRIS. prove_nodup.
        unfold spc_sub, to_spc, smod_src, spc_from. ss. i. des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs. }
      { i. unfold spc_sub, spc_rec, spc_pure, to_spc, spc_incl, APCA.Spc, spc_sub, to_spc.
        unseal CRIS. prove_nodup. i. inv FIND. des_ifs. rewrite ->eq_rel_dec_correct in *; des_ifs. }
      { unfold spc_sub, spc_pure, spc, spc_rec, to_spc, KnotA.KnotRecSpc, KnotMainA.MainFunSpc.
        i. revert FIND. unseal CRIS. i. ss. des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs. }
      { unfold spc_sub, spc_pure, spc, to_spc, KnotA.KnotRecSpc, KnotMainA.MainFunSpc, spc_from, smod_src.
        unseal CRIS. i. inv FIND. des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs. }
    }
    rewrite !hmod_add_empty_r hmod_addc_empty_l.
    etrans; cycle 1. { eapply ctxr_comm. }
    rewrite !hmod_add_assoc.
    eapply ctxr_frameL.

    rewrite -(hmod_add_empty_r ((KnotA.t _ _ _ _ _) ★ _ ★ _)).
    etrans.
    { eapply ctxr_compose_hor; [|refl]. eapply KnotIA.correct; et.
      { apply genv_wf. }
      { unfold KnotGEnv.t. ii; ss; des; ss; tauto. }
      { i. unfold spc_incl, KnotA.KnotRecSpc, spc_rec. unseal CRIS. split; prove_nodup.
        unfold spc_sub, KnotA.KnotRecSpc, to_spc. unseal CRIS. et. }
      { i. unfold spc_incl, APCA.Spc; unseal CRIS; prove_nodup. unfold spc_sub, spc. ss.
        i. des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs. }
      { unfold spc_sub, spc_fun, spc_pure, to_spc.
        unfold KnotMainA.MainFunSpc, KnotA.KnotRecSpc. i. unseal CRIS. revert FIND. unseal CRIS. i.
        ss. des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs. }
      { unfold spc_sub, spc_pure, spc, to_spc, smod_src ,KnotA.KnotRecSpc, KnotMainA.MainFunSpc.
        unseal CRIS. i. revert FIND; unseal CRIS; i. unfold spc_from. ss.
        des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs. }
    }
    rewrite !hmod_add_empty_r hmod_addc_empty_l.
    eapply ctxr_frameL.
    etrans.
    { eapply ctxr_frameR. eapply MemIA.correct.
      unfold spc_incl, spc_sub. split.
      { unfold MemA.Spc. unseal CRIS. prove_nodup. }
      { unfold to_spc, MemA.Spc, spc. unseal CRIS. i. ss.
        des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs. }
    }
    eapply ctxr_frameL. refl.
  Qed.

  Lemma cancel_tgt :
    refines (mod_cancel, (init_cond ∗ main_fsp.(precond) 0 tt tt↑ tt↑)%I)
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Local Definition initial_resource : Σ :=
    KnotMainA.init_res ⋅ KnotA.init_res ⋅
    ((KnotA.init_res_mem genv) ⋅ (mem_init_res csl genv)).

  Local Transparent mem_points_to_singleton_r.

  Lemma initial_resource_valid : ✓ initial_resource.
  Proof.
    dfs_solve.
    - rewrite comm auth_both_valid_discrete; split; ss.
    - unfold mem_initial_mem_r, mem_points_to_singleton_r.
      rewrite auth_both_valid_discrete. split.
      { unfold mem_init_val, _points_to_r. econs. instantiate (1:=ε).
        rewrite right_id. intros b ofs.
        des_ifs; bsimpl; des; rewrite ->?Z.leb_le, ->?Z.leb_gt, ->?Z.ltb_lt, ->?Z.ltb_ge in *; unfold length in *; try destruct decide; ss; subst; ss; unfold genv in *; ss; try destruct dec; ss.
        { do 2 (destruct b; ss; [inv Heq1; hss|]). destruct b; hss. do 2 (destruct b; ss; [inv Heq0; hss|]). rewrite nth_error_nil in Heq0. ss. }
        { do 2 (destruct b; hss). destruct b; hss. }
        { do 2 (destruct b; ss). destruct b; hss.
          rewrite discrete_fun_lookup_singleton discrete_fun_lookup_singleton_ne //. }
        { do 2 (destruct b; ss). destruct b; hss. }
        { do 2 (destruct b; ss). destruct b; hss. }
      }
      { intros b ofs. unfold mem_init_val. des_ifs. }
  Qed.

  Theorem behavioral_refinement :
    ∃ target_resource, refines_mod
      (HMod.to_mod mod_cancel initial_resource)
      (HMod.to_mod mod_tgt target_resource).
  Proof.
    move: (cancel_tgt)=>H; rewrite /refines in H; des; ss.
    destruct (H initial_resource).
    { apply initial_resource_valid. }
    { iIntros "[[IM IK] [IKM IMM]]".
      rewrite /init_cond /KnotA.InitCond /KnotMainA.InitCond /MemA.InitCond.
      rewrite /KnotMainA.init_res /KnotA.init_res /mem_init_res /KnotA.init_res_mem.
      rewrite /mem_initial_mem_r.
      rewrite /precond /= /KnotA.knot_full /KnotA.var_points_to /KnotA.knot_init /KnotA.knot_frag
        /mem_initial_mem own.Own_eq own.own_eq /own.Own_def /own.own_def.
      iFrame. iSplitL; et. rewrite /genv /KnotA.init_res_mem. ss. des_ifs. ss.
      rewrite /mem_points_to_singleton /mem_points_to_singleton_r /own.own_eq /own.Own_def /own.own_def /=. rewrite own.own_eq /own.Own_def /own.own_def. iFrame.
    }
    { econs; ss; try prove_nodup. }
    { exists x; des; eauto. }
  Qed.
End KnotAll. End KnotAll.
(* Print Assumptions KnotAll.behavioral_refinement. *)
