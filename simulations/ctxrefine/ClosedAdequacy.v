Require Import Coqlib AList.
Require Export sflib.
Require Export ITreelib.
Require Import Any.

Require Import IRed.
Require Import STS.
Require Import Behavior Skeleton.
Require Import PCM IPM.

Require Import ModSim ModSimFacts.
Require Import HPSim HPSimFacts.

Require Import HMod Mod HMod2Mod Events.
Require Import SubPerm.

Require Import ISim ISimFacts.
Require Import CtxRefine.
Require Import ITactics IModL.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Set Implicit Arguments.

Section CLOSED.
  Context `{Σ: GRA.t}.

  Ltac hstep := guclo hpsimC_spec; econs; econs; eauto; econs; eauto.

  Lemma _hpsim_close fls flt Ist my_tid dummy:
    @_hpsim _ fls flt Ist my_tid dummy false <9= @_hpsim _ fls flt Ist my_tid dummy true.
  Proof.
    i. ss. 
    eapply _hpsim_tarski; eauto. i. 
    econs. ii. exploit IN; eauto. i. des.
    esplits; eauto. clear IN.
    destruct x9; ss; econs; eauto.
  Qed.

  Lemma hpsim_close
    fl_src fl_tgt Ist my_tid
    ps pt nths st_src st_tgt itr_src itr_tgt fmr
    (SIM: hpsim_body fl_src fl_tgt Ist my_tid false ps pt nths (st_src, itr_src) (st_tgt, itr_tgt) fmr)
  :
    hpsim_body fl_src fl_tgt Ist my_tid true ps pt nths (st_src, itr_src) (st_tgt, itr_tgt) fmr.
  Proof.
    ginit. s. revert_until my_tid. gcofix CIH. i.
    exploit SIM; s; i; eauto.
    clear SIM. rename x0 into SIM.
    remember (st_src, itr_src). remember (st_tgt, itr_tgt).
    move SIM before CIH. revert_until SIM. punfold SIM.
    pattern ps, pt, nths, p, p0, fmr.
    eapply _hpsim_tarski, SIM; i. clear SIM fmr. rename fmr0 into fmr.
    guclo hpsim_wfC_spec. econs. i. 
    exploit IN; i; des; eauto. clear IN.
    destruct x0; i; des; inv Heqp; try inv Heqp0; clarify; hstep.
    - eapply K; try refl; eauto. eapply alist_upd_nodup; eauto. 
    - eapply K; try refl; eauto. eapply alist_upd_nodup; eauto.
    - pclearbot. gfinal. right. eapply paco8_mon_bot; eauto.
      i. eapply _hpsim_close. eauto.
  Qed. 

  Theorem closed_adequacy (ms mt: HMod.t) IC Ist
    (SIM: HSim.t true ms mt IC Ist)
    :
    refines (ms, IC) (mt, const(emp%I)).
  Proof.
    split.
    { s. apply SIM. }
    ii. hexploit (HSim.sim_modsem SIM); eauto.
    { eapply Sk.equiv_incl in EQV. etrans; eauto. refl. }
    i. ss. des. exists ε.
    esplits; eauto.
    { eapply URA.wf_unit. } 
    { eapply hssim_wf; eauto. }
    ii. subst. eapply adequacy_modsem, PR.
    - replace rs with (rs ⋅ ε); [|r_solve]. 
      eapply hssim_adequacy; eauto.
      + r_solve. eauto.
      + eapply Own_iProp; eauto. 
      + eapply hssim_wf; eauto.
    - inv WFM. econs. ss. unfold map_snd.
      rewrite !List.map_map. eapply eq_ind; [apply wf_fns|].
      f_equal. extensionalities. destruct H0. ss.
  Qed.
End CLOSED.
