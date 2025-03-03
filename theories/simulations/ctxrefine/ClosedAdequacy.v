Require Import Common.

Require Import ModSim ModSimFacts.
Require Import HPSim HPSimFacts.

Require Import HMod Mod HMod2Mod Events.
Require Import SubPerm.

Require Import ISim ISimFacts.
Require Import CtxRefine.
Require Import ITactics.
Require Import syn_invariants.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Set Implicit Arguments.

Ltac hstep := guclo hpsimC_spec; econs; econs; eauto; econs; eauto.

Lemma _hpsim_close `{Σ: GRA} fls flt Ist:
  @_hpsim _ open fls flt Ist <10= @_hpsim _ closed fls flt Ist.
Proof.
  i. ss. 
  eapply _hpsim_tarski; eauto. i. 
  econs. ii. exploit IN; eauto. i. des.
  esplits; eauto. clear IN.
  destruct x10; ss; econs; eauto.
Qed.

Lemma hpsim_close `{Σ: GRA}
  fl_src fl_tgt Ist
  ps pt nths st_src st_tgt itr_src itr_tgt fmr
  (SIM: hpsim_body open fl_src fl_tgt Ist ps pt nths (st_src, itr_src) (st_tgt, itr_tgt) fmr)
:
  hpsim_body closed fl_src fl_tgt Ist ps pt nths (st_src, itr_src) (st_tgt, itr_tgt) fmr.
Proof.
  ginit. s. revert_until Ist. gcofix CIH. i.
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
  - pclearbot. gfinal. right. eapply paco9_mon_bot; eauto.
    i. eapply _hpsim_close. eauto.
Qed. 

Lemma valid_solve_eq `{Σ: GRA} (a b : Σ) :
  ✓ a -> a ≡ b -> ✓ b.
Proof.
  i. rewrite <- H0. eauto.
Qed.

Lemma Own_equiv `{Σ: GRA} (a b : Σ):
  a ≡ b -> Own a ⊢ Own b.
Proof.
  i. eapply Own_extends, Some_included_total, Some_included_refl.
  symmetry. eauto.
Qed.

Theorem closed_adequacy `{Σ: GRA} (ms mt: HMod.t) IC Ist P
  (SIM: HSim.t closed ms mt IC Ist)
  :
  refines (ms, IC ∗ P)%I (mt, P).
Proof.
  ii. eapply Own_split in SRC; eauto. des.
  i. ss. des. exists a2.
  esplits; eauto.
  { eapply cmra_valid_op_r. eapply valid_solve_eq; eauto. }
  { eapply hsim_wf; eauto. }
  ii. subst. eapply adequacy_modsem, PR.
  - eapply hsim_adequacy; try eapply SRC0; eauto.
    + rewrite -Own_op. eapply Own_equiv. 
      etrans; eauto. rewrite comm; ss.
    + eapply hsim_wf; eauto.
  - inv WFM. econs. ss. unfold map_snd.
    rewrite !List.map_map. eapply eq_ind; [apply wf_fns|].
    f_equal. extensionalities. destruct H. ss.
Qed.

Theorem closed_adequacy2 `{Σ: GRA} (ms mt: HMod.t) P
  (SIM: HSim.t closed ms mt emp%I IstEq)
  :
  refines (ms, P) (mt, P).
Proof.
  ii. ss. des. exists rs.
  esplits; eauto.
  { eapply hsim_wf; eauto. }
  ii. subst. eapply adequacy_modsem, PR.
  - eapply hsim_adequacy; auto.
    + iIntros "H". iFrame. iApply Own_unit. 
    + eapply hsim_wf; eauto.
    + inv SIM. econs; eauto. iIntros "_".
      iApply sim_initial; eauto.
  - inv WFM. econs. ss. unfold map_snd.
    rewrite !List.map_map. eapply eq_ind; [apply wf_fns|].
    f_equal. extensionalities. destruct H. ss.
Qed.
