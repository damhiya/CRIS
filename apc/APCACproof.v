Require Import CRIS.

Require Import NormITree.
Require Import APCHeader APC APCA APCC.

Set Implicit Arguments.

Module APCAC. Section APCAC.
  Import APCA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ :=
    (λ _ _ _, True)%I.

  (* context *)
  Context (md : HMod.t).
  Context (u : univ_id).
  Context (spc_c spc_a spc_pure : string → option fspec).
  Context (APCInSpcA : spc_incl APCA.Spc spc_a).
  Context (PureInSpcA : spc_sub spc_pure spc_a).
  Context (PureIsPure :
            ∀ fn pfsp, 
            spc_pure fn = Some pfsp 
              → ∃ scopes, find_body md fn = Some (pure_specbody scopes u spc_a pfsp)).

  Local Definition APCC := (APCC.t u spc_c).
  Local Definition APCA := (APCA.t u spc_pure spc_a).
  Local Definition APCCMod := (APCC ★ md).
  Local Definition APCAMod := (APCA ★ md).
  Local Definition IstFull := (IstProd (IstSB APCC.(HMod.scopes) Ist) IstEq).

  Local Transparent _APC.

  Lemma simF_apc :
    HSim.sim_fun open APCCMod APCAMod IstFull APCName.apc.
  Proof.
    init_simF u 0.
    (* init_simF. *)
    steps_l. iDestruct "ASM" as "%"; des; subst.
    steps_r. force_r q. force_r (q↑). force_r. iSplitR; et. hss. steps_r.

    (* normalize itree - remove all interpretations and sandboxes except APC *)
    (* SRC *)
    wbind_expand_l.
    (* TGT *)
    wbind_expand_r. steps_r.

    (* add meaningless return in src *)
    set (itr:=(ITree.bind _ _)).
    eapply wsim_congruence_src.
    { instantiate (1:=Ret ();;; itr). rewrite bind_ret_l. refl. }

    iApply wsim_bind. iSplitL; cycle 1.
    { iIntros (? ? ? ? ?) "R".
      instantiate (1:=(λ nths '(st_src, _) '(st_tgt, _), IstFull nths st_src st_tgt)%I).
      subst itr. steps_r. force_l. steps_l. forces_l. iSplitR; et. step. iSplit; et. }
    clear itr.

    (* well founded induction on depth ordinal *)
    iApply wsim_reset. iStopProof. 
    generalize scopes st_tgt st_src nths. revert q0. pattern q. set (GOAL:=λ _, _).
    revert q. apply (well_founded_induction Ord.lt_well_founded).
    i. subst GOAL. ss. iIntros (? ? ? ? ?) "IST".

    (* well founded induction on width ordinal *)
    iApply wsim_reset. iStopProof. 
    generalize st_tgt0 st_src0 nths0. pattern q0. set (GOAL:=λ _, _).
    revert q0. apply (well_founded_induction Ord.lt_well_founded).
    i. subst GOAL. ss. iIntros (? ? ?) "IST".

    rewrite unfold_APC. steps_r. des_ifs. { step. iFrame. }
    steps_r.

    (* manually do what wsim_unwrapN_tgt does *)
    unfold unwrapN. des_ifs. 2:{ unfold triggerNB. steps_r. des_ifs. }
    rename Heq into G, f into q3. steps_r. 
    
    (* inlining *)
    unfold is_Some in *. des. dup grt. apply PureInSpcA in grt. rewrite grt in G. inv G; ss.
    apply PureIsPure in grt1. ss. destruct grt1. unfold find_body in H1.
    hide_itree_l; prep; iApply wsim_inline_tgt.
    { subst FLT. rewrite map_app. apply alist_find_comm.
      { rewrite map_app. rewrite !map_fst_map_map_snd_refl.
        apply nodup_comm. rewrite -map_app. eauto. }
      apply alist_find_app. et. }
    s; show_itree.

    unfold pure_specbody, interp_sb_hp, HoareFun. steps_r.
    force_r q4. forces_r. iSplitR "IST"; et.

    steps_r. unfold pure_body.
    (* manually do what wsim_unwrapN_tgt does *)
    step_r. hss. steps_r. rename q7 into q8, q6 into q7.

    steps_r. iDestruct "GRT" as "%". hss.

    (* inlining *)
    inline_r. steps_r. force_r q7. forces_r. iSplitR; et. steps_r.

    (* manually do what wsim_unwrapN_tgt does *)
    hss. steps_r.

    (* normalize itree *)
    wbind_expand_r.

    (* add meaningless return in src *)
    set (itr:=(λ _: unit, _)). steps_r.
    eapply wsim_congruence_src.
    { instantiate (1:=Ret ();;; Ret ()). grind. }

    iApply wsim_bind. iSplitL; cycle 1.
    { iIntros (? ? ? ? ?) "R". instantiate (1:=(λ nths '(st_src, _) '(st_tgt, _), IstFull nths st_src st_tgt)%I).
      subst itr. steps_r. forces_r. iSplitL "GRT"; et.
      steps_r. forces_r. iSplitL "GRT"; et. steps_r. iApply wsim_reset. iStopProof. eapply H0; et. }
    clear itr. iApply wsim_reset. iStopProof. eapply H; et.
    Unshelve. all: ss.
  (*FAST*)Qed.

  Theorem sim : HSim.t open APCCMod APCAMod emp%I IstFull.
  Proof.
    init_sim.
    - iIntros "_". iExists [], [], _, _. 
      iSplit; ss.
      iSplit; [iSplit|]; eauto.
      iPureIntro. split; prove_scope.
    - eapply simF_apc; eauto.
  Qed.
End APCAC.

Section ctxr.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.

  Definition ctxr (md : HMod.t) (u : univ_id) (spc_c spc_a spc_pure : string → option fspec)
      (APCInSpcA : spc_incl APCA.Spc spc_a)
      (PureInSpcA : spc_sub spc_pure spc_a)
      (PureIsPure : 
                  ∀ fn pfsp, 
                    spc_pure fn = Some pfsp 
                    → ∃ scopes, find_body md fn = Some (pure_specbody scopes u spc_a pfsp)) :
    ctx_refines
      ((APCC.t u spc_c)           ★ md, emp%I)
      ((APCA.t u spc_pure spc_a)  ★ md, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End ctxr. End APCAC.