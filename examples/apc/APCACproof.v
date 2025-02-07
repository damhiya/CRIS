Require Import CRIS.

Require Import NormITree.
Require Import APCHeader APC APCA APCC.

Set Implicit Arguments.

Module APCAC. Section APCAC.
  Import APCA.
  Context {Σ: GRA}.
  Notation iProp := (iProp Σ).

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp :=
    (λ _ _ _, True)%I.

  (* context *)
  Variable md: HMod.t.

  Variable ginv : invspec.
  Variable SpcC : string → option fspec.
  Variable SpcA : string → option fspec.
  Variable SpcPure : string → option fspec.

  Hypothesis APCInSpcA : spc_incl APCA.Spc SpcA.
  Hypothesis PureInSpcA : spc_sub SpcPure SpcA.
  Hypothesis PureIsPure :
    ∀ fn pfsp, 
      SpcPure fn = Some pfsp 
      → ∃ scp, find_body md fn = Some (pure_specbody scp ginv SpcA SpcPure pfsp).

  Local Notation APCC := (APCC.t ginv SpcC).
  Local Notation APCA := (APCA.t ginv SpcPure SpcA).
  Local Notation APCCMod := (APCC ★ md).
  Local Notation APCAMod := (APCA ★ md).
  Local Notation IstFull := (IstProd (IstSB APCC.(HMod.scopes) Ist) IstEq).

  Local Transparent _APC.

  Lemma simF_apc :
    HSim.sim_fun open APCCMod APCAMod IstFull APCName.apc.
  Proof.
    init_simF.
    steps_l. iDestruct "ASM" as "%"; des; subst.
    steps_r. force_r q. force_r (q↑). force_r. iSplitR; et. hss. steps_r.

    (* normalize itree - remove all interpretations and sandboxes except APC *)
    (* SRC *)
    bind_expand_l.
    (* TGT *)
    bind_expand_r.

    (* add meaningless return in src *)
    set (itr:=(ITree.bind _ _)).
    eapply isim_congruence_src.
    { instantiate (1:=Ret ();;; itr). rewrite bind_ret_l. refl. }

    iApply isim_bind. iSplitL; cycle 1.
    { iIntros (? ? ? ? ?) "R".
      instantiate (1:=(λ nths '(st_src, _) '(st_tgt, _), IstFull nths st_src st_tgt)%I).
      subst itr. steps_r. force_l. steps_l. forces_l. iSplitR; et. step. iSplit; et. }
    clear itr.

    (* well founded induction on depth ordinal *)
    iApply isim_reset. iStopProof. 
    generalize scopes st_tgt st_src nths. revert q0. pattern q. set (GOAL:=λ _, _).
    revert q. apply (well_founded_induction Ord.lt_well_founded).
    i. subst GOAL. ss. iIntros (? ? ? ? ?) "IST".

    (* well founded induction on width ordinal *)
    iApply isim_reset. iStopProof. 
    generalize st_tgt0 st_src0 nths0. pattern q0. set (GOAL:=λ _, _).
    revert q0. apply (well_founded_induction Ord.lt_well_founded).
    i. subst GOAL. ss. iIntros (? ? ?) "IST".
    
    rewrite unfold_APC. steps_r. des_ifs. { step. iFrame. }
    steps_r. des.
    
    (* inlining *)
    unfold is_Some in *. des. dup q3. apply PureInSpcA in q3. rewrite q3 in G. inv G; ss.
    apply PureIsPure in q8. ss. destruct q8. unfold find_body in H1.
    hide_itree_l; prep; iApply isim_inline_tgt_simpl.
    { subst FLT. rewrite map_app. apply alist_find_comm.
      { rewrite map_app. rewrite !map_fst_map_map_snd_refl.
        apply nodup_comm. rewrite -map_app. eauto. }
      apply alist_find_app. et. }
    s; show_itree.

    unfold pure_specbody, interp_sb_hp, HoareFun. steps_r.
    force_r q5. forces_r. iSplitR "IST"; et.

    steps_r. hss. iDestruct "GRT" as "%". hss.

    (* inlining *)
    inline_r. steps_r. force_r q9. forces_r. iSplitR; et. steps_r.

    (* normalize itree *)
    bind_expand_r.

    (* add meaningless return in src *)
    set (itr:=(λ _: unit, _)).
    eapply isim_congruence_src.
    { instantiate (1:=Ret ();;; Ret ()). grind. }

    iApply isim_bind. iSplitL; cycle 1.
    { iIntros (? ? ? ? ?) "R". instantiate (1:=(λ nths '(st_src, _) '(st_tgt, _), IstFull nths st_src st_tgt)%I).
      subst itr. steps_r. forces_r. iSplitL "GRT"; et.
      steps_r. forces_r. iSplitL "GRT"; et. steps_r. iApply isim_reset. iStopProof. eapply H0; et. }
    clear itr. iApply isim_reset. iStopProof. eapply H; et. hss.
    Unshelve. all: ss.
  Qed.

  Theorem sim : HSim.t open APCCMod APCAMod emp%I IstFull.
  Proof.
    init_sim.
    - iIntros "_". iExists [], [], _, _. 
      iSplit; ss.
      iSplit; [iSplit|]; eauto.
      iPureIntro. split; prove_scope.
    - eapply simF_apc; eauto.
  Qed.

  Theorem correct :
    ∀ Pmd, ctx_refines
      (APCCMod, Pmd)
      (APCAMod, Pmd).
  Proof.
    intro Pmd.
    rewrite -(hmod_addc_empty_l APCCMod) -(hmod_addc_empty_l APCAMod).
    rewrite -(hmod_add_empty_r APCCMod) -(hmod_add_empty_r APCAMod).
    eapply ctxr_compose_hor; [|refl].
    eapply main_adequacy.
    apply sim.
  Qed.

End APCAC. End APCAC.