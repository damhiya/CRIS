Require Import CRIS.
Require Import APCHeader APC APCA APCC.

Require Import ltac2_lib.

Set Implicit Arguments.

Module APCAC. Section APCAC.
  Import APCA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Definition Ist : alist key Any.t → alist key Any.t → iProp Σ :=
    (λ _ _, True)%I.

  (* context *)
  Context (md : Mod.t).
  Context (sp_c sp_a : sp_type).
  Context (sp_pure : spl_type).
  Context (APCInSpA : sp_incl APCA.Sp sp_a).
  Context (PureInSpA : sp_incl sp_pure sp_a).
  Context (PureIsPure :
            ∀ fn pfsp,
            alist_find (Some fn) sp_pure = Some pfsp
            → ∃ msk scp, (find_body md fn = Some (pure_specbody sp_a true msk scp pfsp)) ∧ msk (Some APCHdr.apc) = true).

  Local Definition APCC := (APCC.t sp_c).
  Local Definition APCA := (APCA.t sp_pure sp_a).
  Local Definition APCCMod := (APCC ★ md).
  Local Definition APCAMod := (APCA ★ md).
  Local Definition IstFull := (IstProd (IstSB APCC.(Mod.scopes) Ist) IstEq).

  Local Transparent _APC.

  Lemma simF_apc : ISim.sim_fun open APCCMod APCAMod APCC.init_cond IstFull (Some APCHdr.apc).
  Proof using _crisG PureIsPure PureInSpA APCInSpA.
    init_simF.
    (* init_simF. *)
    steps_l. iDestruct "ASM" as "%"; des; subst. rename _q into o.
    steps_r. wforce_r o. wforce_r (o↑). wforce_r. iSplitR; et. hss. steps_r.

    (* normalize itree - remove all interpretations and sandboxes except APC *)
    unfold APC at 1. steps_r. rename _q into o'.

    (* add meaningless return in src *)
    add_ret_l ().

    iApply wsim_bind. iSplitL; cycle 1.
    { iIntros (? ? ? ?) "R".
      instantiate (1:=(λ '(st_src, _) '(st_tgt, _), IstFull st_src st_tgt)%I).
      wsteps_r. force_l. steps_l. forces_l. iSplitR; et. step. iSplit; et. }

    (* well founded induction on depth ordinal *)
    iApply wsim_reset. iStopProof. 
    generalize scopes st_tgt st_src. revert o'. pattern o. set (GOAL:=λ _, _).
    revert o. apply (well_founded_induction Ord.lt_well_founded).
    i. subst GOAL. ss. iIntros (? ? ? ?) "IST".

    (* well founded induction on width ordinal *)
    iApply wsim_reset. iStopProof. 
    generalize st_tgt0 st_src0. pattern o'. set (GOAL:=λ _, _).
    revert o'. apply (well_founded_induction Ord.lt_well_founded).
    i. subst GOAL. ss. iIntros (? ?) "IST".

    rewrite unfold_APC. steps_r. des_ifs. { step. iFrame. }
    steps_r. rename _q into o, _q2 into o', _q1 into fn, _q0 into LT.

    rewrite /is_Some in grt. des.
    dup PureInSpA. rename PureInSpA0 into PIS.
    assert (SP: sp_a fn = x1).
    { apply PIS; eauto. }
    rewrite SP. destruct x1; cycle 1.
    { (* inlining *)
      hexploit PureIsPure; eauto. i. des. rewrite /find_body in H1. inline_r.
      { unfold FLT. rewrite map_app. apply alist_find_comm.
        { rewrite map_app. rewrite !map_fst_map_map_snd_refl.
          apply nodup_comm. rewrite -map_app. eauto. }
        { apply alist_find_app. apply H1. }
      }
      unfold pure_specbody, SB.sandbox_body, SModTr.trans_ktree, SModTr.trans_body, SModTr.HoareFun.
      steps_r; ss. rewrite /pure_body /cfunN. hss. steps_r.
      iDestruct "GRT" as "%"; des; hss. rename _q into o'.

      (* inlining *)
      inline_r. force_r o'. steps_r. forces_r. iSplitR; eauto. hss. steps_r.
      
      (* normalize itree *)
      unfold APC at 1. steps_r.
      
      (* add meaningleses return in src *)
      add_ret_l ().
      iApply wsim_bind. iSplitL; cycle 1.
      { iIntros (? ? ? ?) "R".
        instantiate (1:=(λ '(st_src, _) '(st_tgt, _), IstFull st_src st_tgt)%I).
        steps_r. forces_r. iSplitL "GRT"; eauto.
        steps_r. iApply wsim_reset. iStopProof. eapply H0; et. }
      steps_r. iApply wsim_reset. iStopProof. eapply H; et.
    }

    (* inlining *)
    hexploit PureIsPure; eauto. i. des. rewrite /find_body in H1.
    steps_r. rename _q into x', _q0 into ret'.
    inline_r.
    { unfold FLT. rewrite map_app. apply alist_find_comm.
      { rewrite map_app. rewrite !map_fst_map_map_snd_refl.
        apply nodup_comm. rewrite -map_app. eauto. }
      { apply alist_find_app. apply H1. }
    }

    unfold pure_specbody, SB.sandbox_body, SModTr.trans_ktree, SModTr.trans_body, SModTr.HoareFun. ss.
    force_r x'. steps_r. force_r (_↑). steps_r. forces_r. iSplitL "GRT"; eauto.
    steps_r. rewrite /pure_body /cfunN. hss. steps_r.
    iDestruct "GRT" as "%"; des; hss.

    (* inlining *)
    inline_r. force_r. steps_r. forces_r. iSplitR; eauto. hss. steps_r.
    
    (* normalize itree *)
    unfold APC at 1. steps_r. 
    
    (* add meaningless return in src *)
    add_ret_l ().

    iApply wsim_bind. iSplitL; cycle 1.
    { iIntros (? ? ? ?) "R".
      instantiate (1:=(λ '(st_src, _) '(st_tgt, _), IstFull st_src st_tgt)%I).
      steps_r. forces_r. iSplitL "GRT"; eauto.
      steps_r. force_r (tt↑). steps_r. force_r. iSplitL "GRT"; eauto. steps_r. iApply wsim_reset. iStopProof. eapply H0; et. }
    steps_r. iApply wsim_reset. iStopProof. eapply H; et.

    Unshelve. all: ss.
  (*SLOW*)Qed.

  Theorem sim : ISim.t open APCCMod APCAMod APCC.init_cond IstFull.
  Proof using _crisG PureIsPure PureInSpA APCInSpA.
    init_sim.
    - split; eauto. iIntros "_". iModIntro.
      iSplit; ss. iPureIntro. split; prove_scope.
    - eapply simF_apc.
  Qed.
End APCAC.

Section ctxr.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Definition ctxr (md : Mod.t) (sp_c sp_a : sp_type) (sp_pure : spl_type)
      (APCInSpA : sp_incl APCA.Sp sp_a)
      (PureInSpA : sp_incl sp_pure sp_a)
      (PureIsPure :
        ∀ fn pfsp,
          alist_find (Some fn) sp_pure = Some pfsp
          → ∃ msk scp, (find_body md fn = Some (pure_specbody sp_a true msk scp pfsp)) ∧ msk (Some APCHdr.apc) = true) :
    ctx_refines
      ((APCC.t sp_c)          ★ md, emp%I)
      ((APCA.t sp_pure sp_a)  ★ md, emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End ctxr. End APCAC.
