Require Import CRIS.
Require Import PFMemHeader PFMemI PFMemA HistoryRA AtomicRA.
Require Import base Time TView View Cell Memory Global Time.
Require Import PFMemIAproof.

Section spawn.
  Import PFMemIA.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !histG, !atomicG}.

  Context (sp : specmap).
  Context (syn : Threads.syntax).
  Context (size : list Z).

  Definition MA := (PFMemA.t sp).
  Definition MI := (PFMemI.t syn size).

  Lemma simF_spawn : ISim.sim_fun open MA MI (init_cond syn size) Ist (Some PFMemHdr.spawn).
  Proof.
    init_simF. steps_l. iDestruct "ASM" as "[[-> TV] ->]". hss_r. steps_r.
    rename _q2 into 𝓥, _q1 into tid.
    iDestruct "IST" as "[% [% [% [[-> [% [% [%WF [% [%PFG %PFL]]]]]] [HA [TA HFA]]]]]]". hss_r.
    steps_r. hss_r. steps_r. destruct _q as [tid_new Hnin].
    iPoseProof (tview_both_valid with "TA TV") as "[% [% [%FIND %]]]"; rewrite FIND. steps_r.
    iMod (tview_auth_alloc _ tid_new with "TA") as "[TA TVnew]"; eauto.
    { rewrite IdentMap.mem_find in Hnin; des_ifs; eauto. }
    force_l (tid_new↑). steps_l. force_l (tid_new↑). steps_l.
    remember [(_, _)] as st_tgt'.
    iAssert (Ist st_src st_tgt')%I with "[- TV TVnew]" as "IST".
    { iExists _, _, _; iSplit; first iPureIntro.
      { split; first subst; ss.
        split; eauto.
        split; eauto.
        split.
        { inv WF; econs; ss. eapply Threads.spawn_wf; eauto. }
        split; ss.
        split; ss.
        intros ???; rewrite IdentMap.gsspec; des_ifs; last by apply PFL.
        case; intros -> <-; econs; ss.
      }
      iFrame "HA HFA TA".
    }
    force_l. iSplitR "IST".
    { iSplit; last done. iFrame "TV TVnew"; ss. }
    steps_l. step. iSplitR; done.
  Qed.
End spawn.