Require Import CRIS Cancel.
Require Import ImpPrelude.
Require Import SchI SchA SchIAproof.
Require Import RRSI RRSA RRSIAproof.
Require Import MemI MemA MemIAproof.
Require Import RRSNodeI RRSNodeA RRSNodeIAproof.
Require Import NDSMainI NDSMainA NDSMainIAproof.

Module NDSMainAll.
  Import inv_instances.

  (* mem *)
  Local Definition csl : string → bool := λ _, false.
  (* global environment - not used in this example *)
  Local Definition genv : GEnv.t := [].
  
  Local Instance Γ : HRA := ##[invΓ; concΓ; newschΓ; rrsΓ; memΓ; nodeΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ; newschΣ; rrsΣ].
  Local Definition irΓ : Γ :=
    **[ir_invΓ; ir_concΓ; SchA.ir_schΓ; RRSAS.ir_schΓ; (ir_memΓ csl genv); RRSNodeAS.ir_nodeΓ].
  Local Definition irΣ : Σ := **[irΓ; ir_invΣ; SchA.ir_schΣ; RRSAS.ir_schΣ].

  Local Lemma irΣ_valid : ✓ (irΣ ⋅ ir_own_admin).
  Proof.
    solve_ir_valid.
    - apply ir_tidRA_valid.
    - apply ir_yieldRA_valid.
    - apply SchA.ir_newtidRA_valid.
    - apply RRSAS.ir_initRA_valid.
    - apply RRSAS.ir_ctlRA_valid.
    - apply RRSAS.ir_pubRA_valid.
    - apply RRSAS.ir_newtidRA_valid.
    - apply ir_memRA_valid.
    - apply RRSNodeAS.ir_nodeRA_valid.
    - apply SchA.ir_joinRA_valid.
    - apply RRSAS.ir_invRA_valid.
  Qed.

  Local Definition sp_rrs : spl_type := (RRSNodeAS.sp ⊤) ++ MemA.sp.
  Local Definition sp_sch : spl_type := NDSMainA.sp ++ (RRSAS.sp sp_rrs ⊤) ++ sp_rrs.

  Local Definition smod_src : SMod.t :=
    (NDSMainA.smod)
      ☆ (SchA.smod sp_sch)
      ☆ (RRSA.smod sp_rrs)
      ☆ (RRSNodeA.smod ⊤)
      ☆ (MemA.smod).
  Local Definition mod_top : Mod.t := (SMod.to_mod sp_none (SMod.cancel smod_src)).
  Local Definition mod_tgt : Mod.t :=
    NDSMainI.t
      ★ SchI.t
      ★ RRSI.t
      ★ RRSNodeI.t
      ★ (MemI.t csl genv).
  
  Local Definition sp : sp_type := sp_from smod_src.
  Local Definition mod_src : Mod.t := SMod.to_mod sp smod_src.

  Local Definition init_cond : iProp Σ :=
    winv (⊤, ⊤) ∗ SchA.init_cond ∗ NDSMainA.init_cond ∗ RRSA.init_cond ∗ MemA.init_cond csl genv.

  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    refines (mod_top, init_cond ∗ TIDAUTH 0 ∗ YIELDAUTH 1)%I
            (mod_src, init_cond).
  Proof.
    eapply Cancel.cancellation. econs.
    - inv FIND; rewrite !eq_rel_dec_correct in H0; des_ifs.
    - inv FIND; rewrite !eq_rel_dec_correct in H0; des_ifs.
  Qed.

  Section SP.

    Lemma sumbool_convert (a b: string) :
      sumbool_to_bool (dec (Some a) (Some b)) = (decide (a = b)).
    Proof.
      rewrite /dec /option_Dec /AList.option_Dec_obligation_1.
      des_ifs; ss.
      { destruct (decide (b = b)); ss. }
      { destruct (decide (a = b)); ss. }
    Qed.

    Lemma spsch_in_sp : sp_incl sp_sch sp.
    Proof.
      rewrite /sp_sch /sp /smod_src.
      rewrite /NDSMainA.sp /RRSAS.sp /sp_rrs /RRSNodeAS.sp /MemA.sp. unseal CRIS.
      prove_nodup.
      i. ss. rewrite /sp_from /to_sp.
      rewrite /NDSMainA.smod /SchA.smod /RRSA.smod /RRSNodeA.smod /MemA.smod /=.
      rewrite !sumbool_convert in H. rewrite !sumbool_convert.
      destruct (decide (fn = RRSHeader.RRSHdr.init)); subst; [by inv H|ss].
      destruct (decide (fn = RRSHeader.RRSHdr._spawn)); subst; [by inv H|ss].
      destruct (decide (fn = RRSHeader.RRSHdr.spawn)); subst; [by inv H|ss].
      destruct (decide (fn = RRSHeader.RRSHdr.yield)); subst; [by inv H|ss].
      destruct (decide (fn = RRSHeader.RRSHdr.yield_global)); subst; [by inv H|ss].
      destruct (decide (fn = RRSHeader.RRSHdr.get_tid)); subst; [by inv H|ss].
      destruct (decide (fn = RRSNodeHeader.RRSNodeHdr.f_main)); subst; [by inv H|ss].
      destruct (decide (fn = RRSNodeHeader.RRSNodeHdr.f)); subst; [by inv H|ss].
      destruct (decide (fn = MemHeader.MemHdr.alloc)); subst; [by inv H|ss].
      destruct (decide (fn = MemHeader.MemHdr.free)); subst; [by inv H|ss].
      destruct (decide (fn = MemHeader.MemHdr.load)); subst; [by inv H|ss].
      destruct (decide (fn = MemHeader.MemHdr.cmp)); subst; [by inv H|ss].
      destruct (decide (fn = MemHeader.MemHdr.cas)); subst; [by inv H|ss].
      destruct (decide (fn = MemHeader.MemHdr.store)); subst; [by inv H|ss].
    Qed.

    Lemma sprrs_in_spsch : spl_sub sp_rrs sp_sch.
    Proof.
      rewrite /spl_sub /sp_sch /sp_rrs. i.
      rewrite /RRSNodeAS.sp /MemA.sp /= in H. revert H. unseal CRIS.
      i; ss. rewrite !eq_rel_dec_correct in H.
      des_ifs; rewrite /NDSMainA.sp /RRSAS.sp /RRSNodeAS.sp /MemA.sp; unseal CRIS; ss.
    Qed.

    Lemma sch_in_sp : sp_incl (SchA.sp sp_sch ⊤) sp.
    Proof.
      rewrite /sp_incl /sp /SchA.sp /sp_sch /sp_rrs /sp_from /to_sp /smod_src.
      rewrite /NDSMainA.sp /RRSAS.sp /sp_rrs /RRSNodeAS.sp /MemA.sp /sp_sch. unseal CRIS.
      prove_nodup. ss. intros fn fsp. rewrite !sumbool_convert. i.
      destruct (decide (fn = RRSHeader.RRSHdr.init)); subst; [by inv H|ss].
      destruct (decide (fn = RRSHeader.RRSHdr._spawn)); subst; [by inv H|ss].
      destruct (decide (fn = RRSHeader.RRSHdr.spawn)); subst; [by inv H|ss].
      destruct (decide (fn = RRSHeader.RRSHdr.yield)); subst; [by inv H|ss].
      destruct (decide (fn = RRSHeader.RRSHdr.yield_global)); subst; [by inv H|ss].
      destruct (decide (fn = RRSHeader.RRSHdr.get_tid)); subst; [by inv H|ss].
      destruct (decide (fn = RRSNodeHeader.RRSNodeHdr.f_main)); subst; [by inv H|ss].
      destruct (decide (fn = RRSNodeHeader.RRSNodeHdr.f)); subst; [by inv H|ss].
      destruct (decide (fn = MemHeader.MemHdr.alloc)); subst; [by inv H|ss].
      destruct (decide (fn = MemHeader.MemHdr.free)); subst; [by inv H|ss].
      destruct (decide (fn = MemHeader.MemHdr.load)); subst; [by inv H|ss].
      destruct (decide (fn = MemHeader.MemHdr.cmp)); subst; [by inv H|ss].
      destruct (decide (fn = MemHeader.MemHdr.cas)); subst; [by inv H|ss].
      destruct (decide (fn = MemHeader.MemHdr.store)); subst; [by inv H|ss].
      rewrite /NDSMainA.sp /RRSAS.sp /sp_rrs /RRSNodeAS.sp /MemA.sp /sp_sch. unseal CRIS.
      destruct (decide (fn = SchHeader.SchHdr._spawn)); subst; [by inv H|ss].
      destruct (decide (fn = SchHeader.SchHdr.spawn)); subst; [by inv H|ss].
      destruct (decide (fn = SchHeader.SchHdr.yield)); subst; [by inv H|ss].
      destruct (decide (fn = SchHeader.SchHdr.get_tid)); subst; [by inv H|ss].
      destruct (decide (fn = SchHeader.SchHdr.join)); subst; [by inv H|ss].
    Qed.

    Lemma rrs_in_spsch : spl_sub (RRSAS.sp sp_rrs ⊤) sp_sch.
    Proof.
      rewrite /spl_sub /RRSAS.sp /sp_sch /sp_rrs.
      rewrite /NDSMainA.sp /SchA.sp /RRSAS.sp /RRSNodeAS.sp /MemA.sp. unseal CRIS.
      ss. intros fn fsp. rewrite !eq_rel_dec_correct. des_ifs.
    Qed.

    Lemma node_in_sprrs : spl_sub (RRSNodeAS.sp ⊤) sp_rrs.
    Proof.
      rewrite /spl_sub /RRSNodeAS.sp /sp_sch /sp_rrs.
      rewrite /NDSMainA.sp /SchA.sp /RRSAS.sp /RRSNodeAS.sp /MemA.sp. unseal CRIS.
      ss. intros fn fsp. rewrite !eq_rel_dec_correct. des_ifs.
    Qed.

    Lemma rrs_in_sp : sp_incl (RRSAS.sp sp_rrs ⊤) sp.
    Proof.
      rewrite /sp_incl /sp /SchA.sp /sp_sch /sp_rrs /sp_from /to_sp /smod_src.
      rewrite /NDSMainA.sp /RRSAS.sp /sp_rrs /RRSNodeAS.sp /MemA.sp /sp_sch. unseal CRIS.
      prove_nodup. ss. intros fn fsp. rewrite !sumbool_convert. i.
      destruct (decide (fn = RRSHeader.RRSHdr.init)); subst; [by inv H|ss].
      destruct (decide (fn = RRSHeader.RRSHdr._spawn)); subst; [by inv H|ss].
      destruct (decide (fn = RRSHeader.RRSHdr.spawn)); subst; [by inv H|ss].
      destruct (decide (fn = RRSHeader.RRSHdr.yield)); subst; [by inv H|ss].
      destruct (decide (fn = RRSHeader.RRSHdr.yield_global)); subst; [by inv H|ss].
      destruct (decide (fn = RRSHeader.RRSHdr.get_tid)); subst; [by inv H|ss].
    Qed.

  End SP.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    eapply ctxr_refines.
    rewrite /mod_src /mod_tgt /smod_src !add_interp_comm.

    etrans; cycle 1.
    { ctxr_rotate. do 4 ctxr_drop. eapply NDSMainIAproof.ctxr.
      { eapply spsch_in_sp. }
      { eapply sprrs_in_spsch. }
      { eapply sch_in_sp. }
      { eapply rrs_in_spsch. }
      { eapply node_in_sprrs. }
    }

    etrans; cycle 1.
    { ctxr_rotate. do 4 ctxr_drop. eapply SchIA.ctxr.
      { eapply sch_in_sp. }
      { eapply spsch_in_sp. }
    }

    etrans; cycle 1.
    { ctxr_rotate. do 4 ctxr_drop. eapply RRSIA.ctxr.
      { eapply sch_in_sp. }
      { eapply rrs_in_sp. }
      { eapply spsch_in_sp. }
      { eapply sprrs_in_spsch. }
    }

    etrans; cycle 1.
    { do 2 ctxr_rotate. do 4 ctxr_drop. eapply MemIA.ctxr. }

    etrans; cycle 1.
    { do 2 ctxr_drop. ctxr_rotate. eapply RRSNodeIAproof.ctxr; cycle 1.
      { eapply spsch_in_sp. }
      { eapply sprrs_in_spsch. }
      { eapply sch_in_sp. }
      { eapply rrs_in_spsch. }
      { eapply node_in_sprrs. }
      { set_solver. }
    }

    etrans; cycle 1.
    { do 2 ctxr_drop. do 2 ctxr_rotate. ctxr_refl. }

    rewrite /init_cond.
    rewrite /NDSMainA.t /SchA.t /RRSA.t /RRSNodeA.t /MemA.t. unseal CRIS.

    eapply ctxr_cond_strengthen.
    iIntros "(? & ? & ? & ? & ?)". iFrame.
  Qed.

  Lemma top_tgt :
    refines (mod_top, init_cond ∗ TIDAUTH 0 ∗ YIELDAUTH 1)%I
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Lemma tgt_wf:
    Mod.wf mod_tgt.
  Proof.
    rewrite /mod_tgt /NDSMainI.t /SchI.t /RRSI.t /RRSNodeI.t /MemI.t.
    unseal CRIS. prove_nodup.
  Qed.

  Lemma init_cond_valid:
    ∃ rs, ✓ rs ∧ (Own rs ⊢ |==> init_cond ∗ TIDAUTH 0 ∗ YIELDAUTH 1).
  Proof.
    exists (irΣ ⋅ ir_own_admin). split.
    - apply irΣ_valid.
    - simplify_res.
      { rewrite make_own_admin; iFrame.
        rewrite /RRSAS.ir_invRA /RRSNodeAS.ir_nodeRA /ir_memRA.
        rewrite /RRSAS.ir_tidRA /RRSAS.ir_pubRA /RRSAS.ir_initRA.
        rewrite /RRSAS.ir_ctlRA /ir_yieldRA /ir_tidRA.
        rewrite /NDSMainA.init_cond /RRSA.init_cond /MemA.init_cond.
        rewrite /RRSAS.InitRRS /RRSNodeAS.full_val /RRSAS.init_inv.
        rewrite /TidTokenAuth /YieldTokenAuth.
        rewrite /RRSAS.rrinv /RRSAS.Pending /RRSAS.Control.
        rewrite /RRSNodeAS.full_val_r /mem_init_auth.
        rewrite /RRSAS.init_tid /RRSAS.init_pub.
        iDestruct "H30" as "[? ?]".
        unseal RRSHeader.RRS. unseal "Node". unseal "Conc".
        rewrite /RRSAS.rrinv_admin_r /RRSAS.init_invmap /RRSAS.rrinv_r.
        iFrame. ss.
        rewrite dom_empty elements_empty /= !right_id.
        rewrite -{1}Qp.half_half -dfrac_op_own. rewrite fmap_empty.
        rewrite gmap_view.gmap_view_auth_dfrac_op.
        iDestruct "H10" as "[? ?]".
        iFrame. iPureIntro. esplits; ss. }
      all: solve_res.
  Qed.

  Theorem behavioral_refinement :
    ∃ src_res tgt_res, refines_lmod
      (Mod.to_lmod mod_top src_res)
      (Mod.to_lmod mod_tgt tgt_res).
  Proof.
    move: (top_tgt)=>H; rewrite /refines in H; des; ss.
    hexploit H; eauto using tgt_wf. clear H; intros [WF H].
    pose proof init_cond_valid as IV. des.
    destruct (H rs); des; et.
    rewrite IV0 /init_cond {1}winv_split_empty. iIntros ">[[[? ?] ?] ?]". iFrame. eauto.
  Qed.
(*SLOW*)End NDSMainAll.
(* Print Assumptions NDSMainAll.behavioral_refinement. *)
