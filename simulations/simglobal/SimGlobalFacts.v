Require Import Coqlib.
Require Import ITreelib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import Mod Mod2STS.
Require Import Skeleton.
Require Import PCM.
Require Import Coq.Relations.Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From Ordinal Require Import Ordinal Arithmetic.
Require Import SimSTS SimGlobal.

Set Implicit Arguments.

Section ADEQUACY.

  Theorem adequacy_global_itree ps pt itr_src itr_tgt
          (SIM : simg eq ps pt itr_src itr_tgt)
    :
      Beh.of_program (@compile_itree itr_tgt)
      <1=
      Beh.of_program (@compile_itree itr_src).
  Proof.
    unfold Beh.of_program. ss.
    i. eapply adequacy_aux; eauto. clear x0 PR.
    instantiate (1:= smj_leb smj_top pt).
    instantiate (1:= smj_leb smj_top ps).
    generalize itr_tgt at 1 as md_tgt. generalize itr_src at 1 as md_src.
    i. ginit.
    revert ps pt itr_src itr_tgt SIM. gcofix CIH. i.
    
    pattern ps, pt, itr_src, itr_tgt.
    eapply simg_ind, SIM. i.
    depdes PR; i; subst.
    { gstep. econs. eapply sim_fin; ss; cbn; des_ifs. }
    { gstep. econs. eapply sim_vis; try sfby ss. i.
      eapply step_trigger_io_iff in STEP. des. subst. inv STEP0.
      esplits.
      + eapply step_trigger_io; et.
      + guclo sim_flagC_spec. econs; [gbase; eapply CIH, SIM0|..]; eauto.
    }
    { guclo sim_indC_spec. eapply sim_demonic_src; try sfby ss.
      esplits.
      + eapply step_tau; et.
      + guclo sim_flagC_spec. econs; [eapply gpaco4_mon; [eapply SIM0|..]|..]; et; ss.
    }
    { guclo sim_indC_spec. eapply sim_demonic_tgt; try sfby ss. i.
      eapply step_tau_iff in STEP. des. subst.
      guclo sim_flagC_spec. econs; [eapply gpaco4_mon; [eapply SIM1|..]|..]; et; ss.
    }
    { des. guclo sim_indC_spec. eapply sim_demonic_src; try sfby ss.
      esplits.
      + eapply step_trigger_choose; et.
      + guclo sim_flagC_spec. econs; [eapply gpaco4_mon; [eapply SIM1|..]|..]; et; ss.
    }
    { guclo sim_indC_spec. eapply sim_demonic_tgt; try sfby ss.
      i. eapply step_trigger_choose_iff in STEP. des. subst.
      guclo sim_flagC_spec. econs; [eapply gpaco4_mon; [eapply SIM0|..]|..]; et; ss.
    }
    { guclo sim_indC_spec. eapply sim_angelic_src; try sfby ss.
      i. eapply step_trigger_take_iff in STEP. des. subst.
      guclo sim_flagC_spec. econs; [eapply gpaco4_mon; [eapply SIM0|..]|..]; et; ss.
    }
    { des. guclo sim_indC_spec. eapply sim_angelic_tgt; try sfby ss.
      esplits.
      + eapply step_trigger_take; et.
      + guclo sim_flagC_spec. econs; [eapply gpaco4_mon; [eapply SIM1|..]|..]; et; ss.
    }

    pclearbot. clear ps pt itr_src itr_tgt SIM.
    guclo sim_flagC_spec. econs; cycle 1.
    { instantiate (1:= smj_leb smj_mid ps1).
      unfold smj_leb. destruct ps0, ps1; ss; destruct b, b0; ss. }
    { instantiate (1:= smj_leb smj_mid pt1).
      unfold smj_leb. destruct pt0, pt1; ss; destruct b, b0; ss. }
    clear DECS DECT ps0 pt0.
    rename ps1 into ps, pt1 into pt, SIM0 into SIM, itr_src0 into itr_src, itr_tgt0 into itr_tgt.

    pattern ps, pt, itr_src, itr_tgt.
    eapply simg_ind, SIM. i.
    depdes PR; i; subst.
    { gstep. econs. eapply sim_fin; ss; cbn; des_ifs. }
    { gstep. econs. eapply sim_vis; try sfby ss. i.
      eapply step_trigger_io_iff in STEP. des. subst. inv STEP0.
      esplits.
      + eapply step_trigger_io; et.
      + guclo sim_flagC_spec. econs; [gbase; eapply CIH, SIM0|..]; eauto.
    }
    { guclo sim_indC_spec. eapply sim_demonic_src; try sfby ss.
      esplits.
      + eapply step_tau; et.
      + guclo sim_flagC_spec. econs; [eapply gpaco4_mon; [eapply SIM0|..]|..]; et; ss.
    }
    { guclo sim_indC_spec. eapply sim_demonic_tgt; try sfby ss. i.
      eapply step_tau_iff in STEP. des. subst.
      guclo sim_flagC_spec. econs; [eapply gpaco4_mon; [eapply SIM1|..]|..]; et; ss.
    }
    { des. guclo sim_indC_spec. eapply sim_demonic_src; try sfby ss.
      esplits.
      + eapply step_trigger_choose; et.
      + guclo sim_flagC_spec. econs; [eapply gpaco4_mon; [eapply SIM1|..]|..]; et; ss.
    }
    { guclo sim_indC_spec. eapply sim_demonic_tgt; try sfby ss.
      i. eapply step_trigger_choose_iff in STEP. des. subst.
      guclo sim_flagC_spec. econs; [eapply gpaco4_mon; [eapply SIM0|..]|..]; et; ss.
    }
    { guclo sim_indC_spec. eapply sim_angelic_src; try sfby ss.
      i. eapply step_trigger_take_iff in STEP. des. subst.
      guclo sim_flagC_spec. econs; [eapply gpaco4_mon; [eapply SIM0|..]|..]; et; ss.
    }
    { des. guclo sim_indC_spec. eapply sim_angelic_tgt; try sfby ss.
      esplits.
      + eapply step_trigger_take; et.
      + guclo sim_flagC_spec. econs; [eapply gpaco4_mon; [eapply SIM1|..]|..]; et; ss.
    }

    unfold smj_leb in *.
    gstep. econs. eapply sim_progress.
    - gbase. eapply CIH in SIM0.
      destruct ps1, pt1; ss. destruct b, b0; ss.
    - destruct ps0; ss. destruct b; ss. destruct ps1; ss. destruct b; ss.
    - destruct pt0; ss. destruct b; ss. destruct pt1; ss. destruct b; ss.
  Qed.

  Section MAIN.
    
    Theorem adequacy_global (ms_src ms_tgt : ModSem.t) ps pt
      (SIM : simg eq ps pt (@ModSem.initial_itr ms_src) (@ModSem.initial_itr ms_tgt))
      :
      Beh.of_program (@ModSem.compile ms_tgt) <1= Beh.of_program (@ModSem.compile ms_src).
    Proof.
      eapply adequacy_global_itree. eapply SIM.
    Qed.
  End MAIN.
  
End ADEQUACY.
