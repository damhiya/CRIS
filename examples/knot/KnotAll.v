Require Import CRIS Cancel.
Require Import MemHeader MemI MemA MemIAproof.
Require Import APCHeader APC APCI APCA APCC APCACproof APCIAproof.
Require Import KnotHeader KnotMainHeader KnotI KnotMainI.
Require Import KnotA KnotMainA.
Require Import KnotIAproof KnotMainIAproof.

Module KnotAll.
  Import inv_instances.
  Local Instance Γ : HRA := ##[invΓ; memΓ; KnotAΓ].
  Local Instance Σ : GRA := ##[invΣ; Γ].

  (* global environment *)
  Local Definition genv : GEnv.t := KnotGEnv.t ++ KnotMainGEnv.t.
  (* universe *)
  Local Definition u: univ_id := 1.
  (* global invariant *)
  Local Definition ginv : iProp Σ := wsim_ginv u ⊤.

  (* pure spc *)
  Local Definition spc_rec : string → option fspec := 
    to_spc KnotA.KnotRecSpc.
  Local Definition spc_fun : string → option fspec :=
    to_spc (KnotMainA.MainFunSpc genv spc_rec).
  Local Definition spc_pure : string → option fspec :=
    to_spc (KnotA.KnotRecSpc ++ (KnotMainA.MainFunSpc genv spc_rec)).

  (* mem *)
  Local Definition csl : string → bool := λ _, false.

  Local Definition smod_src : SMod.t :=
    (KnotMainA.Mod genv spc_rec) ☆ (KnotA.Mod genv spc_rec spc_fun)
    ☆ MemA.Mod ☆ APCC.Mod.
  Local Definition spc : string → option fspec := spc_from smod_src.

  Local Definition mod_cancel : HMod.t := SModCancel.to_hmod smod_src.

  Local Definition mod_src : HMod.t := SMod.to_hmod ginv spc smod_src.

  Local Definition mod_tgt : HMod.t :=
    KnotMainI.t genv ★ KnotI.t genv ★ MemI.t csl genv ★ APCI.t.

  Local Definition main_fsp : fspec := KnotMainA.main_spec.

  Local Lemma genv_wf : GEnv.wf genv.
  Proof. cbn. prove_nodup. Qed.

  Local Definition init_cond : iProp Σ :=
    KnotMainA.InitCond ∗ (KnotA.InitCond genv) ∗ (MemA.InitCond csl genv).

  Lemma cancel_src :
    refines (mod_cancel, (init_cond ∗ main_fsp.(precond) tt tt↑ tt↑)%I)
            ((mod_src, init_cond) : HMod.modc).
  Proof.
    eapply cancellation; try by econs.
    i. iIntros "%POST". iPureIntro.
    des; eauto.
  Qed.

  Ltac prove_spc :=
    rewrite /MemA.Spc /APCA.Spc /KnotA.KnotRecSpc /KnotA.KnotSpc /KnotMainA.MainFunSpc /KnotMainA.MainSpc;
    rewrite /spc /spc_pure /spc_fun /spc_rec /smod_src /spc_pure /spc_incl /spc_sub /find_body /pure_specbody /spc_from /option_map;
    rewrite /spc_fun /spc_rec /APCA.Spc /KnotA.KnotRecSpc /KnotA.KnotSpc /KnotMainA.MainFunSpc /KnotMainA.MainSpc;
    try unseal CRIS; try prove_nodup;
    ii; ss; rewrite ->!eq_rel_dec_correct in *; des_ifs; ss; eexists; ss.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    eapply ctxr_refines.
    unfold mod_src, mod_tgt. rewrite !add_interp_comm.

    replace (SMod.to_hmod _ spc (KnotMainA.Mod _ _)) with (KnotMainA.t genv u spc_rec spc); cycle 1.
    { unfold KnotMainA.t; unseal CRIS; ss. }
    replace (SMod.to_hmod _ spc (KnotA.Mod _ _ _)) with (KnotA.t genv u spc_rec spc_fun spc); cycle 1.
    { unfold KnotA.t; unseal CRIS; ss. }
    replace (SMod.to_hmod _ spc MemA.Mod) with (MemA.t u spc); cycle 1.
    { unfold MemA.t; unseal CRIS; ss. }
    replace (SMod.to_hmod _ spc APCC.Mod) with (APCC.t u spc); cycle 1.
    { unfold APCC.t; unseal CRIS; ss. }

    rewrite -!hmod_add_assoc.
    etrans. { eapply ctxr_comm. }
    etrans. 
    { rewrite !hmod_add_assoc. rewrite -hmod_addc_empty_l. eapply ctxr_cond_frameR.
      eapply APCAC.wctxr.
      { instantiate (1:=spc). prove_spc. }
      { instantiate (1:=spc_pure). prove_spc. }
      { prove_spc; rewrite /KnotMainA.t /KnotA.t /= alist_find_map_snd /o_map; unseal CRIS; ss. }
    }
    rewrite !hmod_add_assoc.
    etrans. { eapply ctxr_comm. }
    etrans.
    { rewrite !hmod_add_assoc hmod_addc_empty_l /init_cond.
      eapply ctxr_cond_frameR.
      eapply KnotMainIA.wctxr; try prove_spc.
      rewrite /genv /incl; ss. i; des; ss; tauto.
    }
    eapply ctxr_frameL.
    etrans.
    { rewrite hmod_addc_empty_l.
      eapply ctxr_cond_frameR.
      eapply KnotIA.wctxr; try prove_spc.
      rewrite /genv /incl; ss. i; des; ss; tauto.
    }
    eapply ctxr_frameL. unfold KnotIAproof.KnotIA.MemA.
    rewrite hmod_addc_empty_l.
    rewrite -hmod_addc_empty_r -[(MemI.t csl genv ★ _, emp%I)]hmod_addc_empty_r.
    eapply ctxr_compose_hor.
    { eapply MemIA.correct; prove_spc. }
    { eapply APCIA.wctxr; prove_spc. }
  Qed.

  Lemma cancel_tgt :
    refines (mod_cancel, (init_cond ∗ main_fsp.(precond) tt tt↑ tt↑)%I)
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
End KnotAll.
(* Print Assumptions KnotAll.behavioral_refinement. *)
