Require Import Coqlib.
Require Import ITreelib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModuleInternal Mod.
Require Import Skeleton.
Require Import PCM.
Require Import Coq.Relations.Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From Ordinal Require Import Ordinal Arithmetic.
Require Import SimSTS SimGlobal.

Set Implicit Arguments.

Section ADEQUACY.
  Context {CONFS CONFT: EMSConfig}.
  Hypothesis (FINSAME: (@finalize CONFS) = (@finalize CONFT)).

  Theorem adequacy_global_itree itr_src itr_tgt
          (SIM: simg eq false false itr_src itr_tgt)
    :
      Beh.of_program (@compile_itree CONFT itr_tgt)
      <1=
      Beh.of_program (@compile_itree CONFS itr_src).
  Proof.
    unfold Beh.of_program. ss.
    remember false as o_src0 in SIM at 1.
    remember false as o_tgt0 in SIM at 1. clear Heqo_src0 Heqo_tgt0.
    i. eapply adequacy_aux; et.
    instantiate (1:=o_tgt0). instantiate (1:=o_src0). clear x0 PR.
    generalize itr_tgt at 1 as md_tgt.
    generalize itr_src at 1 as md_src. i. ginit.
    revert o_src0 o_tgt0 itr_src itr_tgt SIM. gcofix CIH.
    i. induction SIM using simg_ind; i; clarify.
    { gstep. destruct (finalize r_tgt) eqn:T.
      { eapply sim_fin; ss; cbn; des_ifs; rewrite FINSAME in *; clarify. }
      { eapply sim_angelic_src.
        { cbn. des_ifs; rewrite FINSAME in *; clarify. }
        i. exfalso. inv STEP.
      }
    }
    { gstep. eapply sim_vis; ss. i.
      eapply step_trigger_io_iff in STEP. des. clarify.
      esplits.
      { eapply step_trigger_io; et. }
      { gbase. eapply CIH. hexploit SIM; et. }
    }
    { guclo sim_indC_spec. eapply sim_indC_demonic_src; ss.
      esplits; eauto. eapply step_tau; et.
    }
    { guclo sim_indC_spec. eapply sim_indC_demonic_tgt; ss. i.
      eapply step_tau_iff in STEP. des. clarify.
    }
    { des. guclo sim_indC_spec. eapply sim_indC_demonic_src; ss.
      esplits; eauto. eapply step_trigger_choose; et.
    }
    { guclo sim_indC_spec. eapply sim_indC_demonic_tgt; ss.
      i.  eapply step_trigger_choose_iff in STEP. des. clarify.
      hexploit (SIM x); et. i. des. esplits; eauto.
    }
    { guclo sim_indC_spec. eapply sim_indC_angelic_src; ss. i.
      eapply step_trigger_take_iff in STEP. des. clarify.
      hexploit (SIM x); et. i. des. esplits; et.
    }
    { des. guclo sim_indC_spec. eapply sim_indC_angelic_tgt; ss.
      esplits; eauto. eapply step_trigger_take; et.
    }
    { gstep. eapply sim_progress; eauto. gbase. auto. }
  Qed.

  Section MAIN.
    Variable md_src md_tgt: Mod.t.
    Let ms_src: ModSem.t := md_src.(Mod.enclose).
    Let ms_tgt: ModSem.t := md_tgt.(Mod.enclose).
    Hypothesis (SIM: simg eq false false (@ModSem.initial_itr ms_src CONFS (Some (Mod.wf md_src))) (@ModSem.initial_itr ms_tgt CONFT (Some (Mod.wf md_tgt)))).

    Theorem adequacy_global: Beh.of_program (@Mod.compile _ CONFT md_tgt) <1= Beh.of_program (@Mod.compile _ CONFS md_src).
    Proof.
      eapply adequacy_global_itree. eapply SIM.
    Qed.
  End MAIN.
  
End ADEQUACY.
