Require Import CRIS.
Require Import APCHeader APC APCA APCC.

Require Import ltac2_lib.

Set Implicit Arguments.

Module APCAC. Section APCAC.
  Import APCA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Definition Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ :=
    (λ _ _, True)%I.

  (* context *)
  Context (md : Mod.t).
  Context (sp_c sp_a sp_pure : specmap).
  Context (APCInSpA : APCA.sp ⊆ sp_a).
  Context (PureInSpA : sp_pure ⊆ sp_a).
  Context (PureIsPure :
            ∀ fn fsp,
            sp_pure.1 !! (fid fn) = Some fsp
            → ∃ msk, (find_body md fn = Some (Some (pure_specbody sp_a msk (Some fsp))))
              ∧ (∀ arg, msk _ (subevent _ (Call APCHdr.apc arg)) = true)
              ∧ (∀ X, msk _ (subevent _ (Take X)) = true)
              ∧ (∀ X, msk _ (subevent _ (Choose X)) = true)
              ∧ (∀ X, msk _ (subevent _ (Assume X)) = true)
              ∧ (∀ X, msk _ (subevent _ (Guarantee X)) = true)).

  Local Notation APCC := (APCC.t sp_c).
  Local Notation APCA := (APCA.t sp_pure sp_a).
  Local Notation APCCMod := (APCC ★ md).
  Local Notation APCAMod := (APCA ★ md).
  Local Notation IstFull := (IstProd (IstSB APCC.(Mod.scopes) Ist) IstEq).

  Local Transparent _APC.

  Lemma simF_apc : ISim.sim_fun open APCCMod APCAMod IstFull (fid APCHdr.apc).
  Proof using _crisG PureIsPure PureInSpA APCInSpA.
    (** Due to arbitrary module, manual starting up is required **)
    iStartSim. rewrite /apc_body.

    steps_l. iDestruct "ASM" as "%"; des; subst. rename _q into o.
    steps_r. force_r o. force_r (o↑). force_r. iSplitR; et. steps_r.

    (* normalize itree - remove all interpretations and sandboxes except APC *)
    unfold APC at 1. steps_r. rename _q into o'.

    (* add meaningless return in src *)
    prepend_ret_l ().

    iApply wsim_bind. iSplitL; cycle 1.
    { iIntros (? ? ? ?) "R".
      instantiate (1:=(λ '(st_src, _) '(st_tgt, _), IstFull st_src st_tgt)%I).
      steps_r. force_l. steps_l. forces_l. iSplitR; et. step. iSplit; et.
    }

    (* well founded induction on depth ordinal *)
    iApply wsim_reset. iStopProof. 
    generalize st_tgt st_src. revert o'. pattern o. set (GOAL:=λ _, _).
    revert o. apply (well_founded_induction Ord.lt_well_founded).
    i. subst GOAL. ss. iIntros (? ? ?) "IST".

    (* well founded induction on width ordinal *)
    iApply wsim_reset. iStopProof. 
    generalize st_tgt0 st_src0. pattern o'. set (GOAL:=λ _, _).
    revert o'. apply (well_founded_induction Ord.lt_well_founded).
    i. subst GOAL. ss. iIntros (? ?) "IST".

    rewrite unfold_APC. steps_r. des_ifs. { step. iFrame. }
    steps_r. rename _q into o, _q2 into o', _q1 into fn, _q0 into LT.

    rewrite /is_Some in GRT. des.
    dup PureInSpA. rename PureInSpA0 into PIS. simpl_sp. steps_r.

    (* inlining *)
    hexploit PureIsPure; eauto. i. des. rewrite /find_body in H1.
    rename _q into x', _q0 into arg.
    destruct (Mod.fnsems md !! fid fn) eqn:M; cycle 1.
    { rewrite lookup_fmap M in H1. ss. }
    destruct o0; ss; cycle 1.
    { rewrite lookup_fmap M in H1. ss. }
    destruct p; ss. inv H1.
    
    inline_r.
    rewrite /pure_specbody lookup_fmap M in H8. ss. inv H8.
    eapply (func_ext_rev arg) in H7. rewrite /SB.sandbox_body /= in H7.
    rewrite /SB.sandbox_body H7 /SModTr.trans_fnsem /SModTr.HoareFun.

    steps_r. rewrite H3. steps_r. force_r x'. steps_r. rewrite H3.
    steps_r. force_r (_↑). steps_r. rewrite H5. steps_r. forces_r. iSplitL "GRT"; eauto.
    steps_r. rewrite /pure_body /cfunN. hss. steps_r.
    erewrite lookup_weaken; try eapply APCInSpA; cycle 1.
    { simpl_map. refl. }
    steps_r. rewrite H4. steps_r. rewrite H4. steps_r. rewrite H6. steps_r.
    iDestruct "GRT" as "%" ; des; subst; hss.
    rewrite H2. steps_r.

    (* inlining *)
    inline_r.
    ss. rewrite /SModTr.trans_fnsem. ss.
    forces_r. iSplitR; eauto. steps_r.
    rewrite /apc_body. unfold APC at 1. steps_r.

    (* add meaningless return in src *)
    prepend_ret_l ().

    iApply wsim_bind. iSplitL; cycle 1.
    { iIntros (? ? ? ?) "R".
      instantiate (1:=(λ '(st_src, _) '(st_tgt, _), IstFull st_src st_tgt)%I).
      steps_r. rewrite H3. steps_r. forces_r. steps_r. rewrite H5. steps_r.
      forces_r. iSplitL "GRT"; eauto.
      steps_r. rewrite H4. steps_r. rewrite H6. steps_r.
      force_r (tt↑). steps_r. force_r. iSplitL "GRT"; eauto. steps_r.
      iApply wsim_reset. iStopProof. eapply H0; et. }
    iApply wsim_reset. iStopProof. eapply H; et.

    Unshelve. all: ss.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open APCCMod APCAMod APCC.init_cond IstFull.
  Proof using _crisG PureIsPure PureInSpA APCInSpA.
    init_sim.
    - eapply simF_apc.
    - iIntros "_". do 4 iExists _. esplits; eauto.
  Qed.
End APCAC.

Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma ctxr (md : Mod.t) (sp_c sp_a sp_pure : specmap)
    (APCInSpA : APCA.sp ⊆ sp_a)
    (PureInSpA : sp_pure ⊆ sp_a)
    (PureIsPure :
            ∀ fn fsp,
            sp_pure.1 !! (fid fn) = Some fsp
            → ∃ msk, (find_body md fn = Some (Some (pure_specbody sp_a msk (Some fsp))))
              ∧ (∀ arg, msk _ (subevent _ (Call APCHdr.apc arg)) = true)
              ∧ (∀ X, msk _ (subevent _ (Take X)) = true)
              ∧ (∀ X, msk _ (subevent _ (Choose X)) = true)
              ∧ (∀ X, msk _ (subevent _ (Assume X)) = true)
              ∧ (∀ X, msk _ (subevent _ (Guarantee X)) = true)) :
    ctx_refines
      ((APCC.t sp_c)          ★ md, emp%I)
      ((APCA.t sp_pure sp_a)  ★ md, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End ctxr. End APCAC.
