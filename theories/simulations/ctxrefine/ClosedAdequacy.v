Require Import Common.
From iris.proofmode Require Import proofmode.

Require Import Mod.
Require Import LSim LSimFacts.
Require Import ISim ISimInit ISimFacts.
Require Import CtxRefine.
Require Import ITactics.
Require Import syn_invariants.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Set Implicit Arguments.

(* Ltac mstep := guclo msimC_spec; econs; econs; eauto; econs; eauto. *)

(* Lemma _msim_close `{Σ: GRA} fls flt Ist: *)
(*   @_msim _ fls flt Ist <10= @_msim _ closed fls flt Ist. *)
(* Proof. *)
(*   i. ss.  *)
(*   eapply _msim_tarski; eauto. i.  *)
(*   econs. ii. exploit IN; eauto. i. des. *)
(*   esplits; eauto. clear IN. *)
(*   destruct x10; ss; try by econs; eauto. *)
(* Qed. *)

(* Lemma msim_close `{Σ: GRA} *)
(*   fl_src fl_tgt Ist *)
(*   ps pt nths st_src st_tgt itr_src itr_tgt fmr *)
(*   (SIM: msim_body open fl_src fl_tgt Ist ps pt nths (st_src, itr_src) (st_tgt, itr_tgt) fmr) *)
(* : *)
(*   msim_body closed fl_src fl_tgt Ist ps pt nths (st_src, itr_src) (st_tgt, itr_tgt) fmr. *)
(* Proof. *)
(*   ginit. s. revert_until Ist. gcofix CIH. i. *)
(*   remember (st_src, itr_src). remember (st_tgt, itr_tgt). *)
(*   move SIM before CIH. revert_until SIM. punfold SIM. *)
(*   pattern ps, pt, nths, p, p0, fmr. *)
(*   eapply _msim_tarski, SIM; i. clear SIM fmr. rename fmr0 into fmr. *)
(*   guclo msim_wfC_spec. econs. i. *)
(*   guclo msim_nodupC_spec. econs. i. *)
(*   exploit IN; i; des; eauto. clear IN. *)
(*   destruct x0; i; des; try by inv Heqp; try inv Heqp0; clarify; mstep. *)
(*   { guclo msimC_spec. econs. econs; et. econs; et. i. *)
(*     hexploit K; et. i; des. esplits; et. } *)
(*   pclearbot. gstep. econs. ii. esplits; et. econs; et. *)
(*   gfinal. right. eapply paco9_mon_bot; eauto using _msim_close. *)
(* Qed.  *)

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

Theorem closed_adequacy `{Σ: GRA} (ms mt: Mod.t) IC Ist P
  (SIM: ISim.t closed ms mt IC Ist)
  :
  refines (ms, IC ∗ P)%I (mt, P).
Proof.
  split.
  { eapply ISim_wf; eauto. }
  ii. eapply Own_split in SRC; eauto. des.
  i. ss. des. exists a2.
  esplits; eauto.
  { eapply cmra_valid_op_r. eapply valid_solve_eq; eauto. }
  ii. subst. eapply lsim_adequacy, PR.
  - eapply ISim_adequacy; try eapply SRC0; eauto.
    + rewrite -Own_op. eapply Own_equiv. 
      etrans; eauto. rewrite comm; ss.
    + eapply ISim_wf; eauto.
  - dup WFM. inv WFM. econs. ss. unfold map_snd.
    rewrite !List.map_map.
    eapply sub_perm_nodup in wf_fns; [|eapply SIM; et].
    eapply eq_ind; [apply wf_fns|].
    f_equal; et. extensionalities. destruct H; et.
Qed.

Theorem closed_adequacy_emp `{Σ: GRA} (ms mt: Mod.t) P
  (SIM: ISim.t closed ms mt emp%I IstEq)
  :
  refines (ms, P) (mt, P).
Proof.
  eapply (closed_adequacy P) in SIM.
  ii. exploit SIM; et. i; des. esplits; et.
  i. exploit x1; et. ss. rewrite -bi.emp_sep_1. et.
Qed.
