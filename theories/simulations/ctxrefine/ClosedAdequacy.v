Require Import Common.
From iris.proofmode Require Import proofmode.

Require Import Mod.
Require Import LSim LSimFacts.
Require Import ISim ISimFacts.
Require Import CtxRefine.
Require Import ITactics.
Require Import syn_invariants.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Set Implicit Arguments.

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

Section ADEQUACY.
Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

Theorem closed_adequacy (ms mt: Mod.t) IC Ist P
  (SIM: ISim.t closed ms mt IC Ist)
  :
  refines (ms, IC ∗ P)%I (mt, P).
Proof using.
  split.
  { eapply ISim_wf; eauto. }
  ii. ss. eapply Own_split in SRC; eauto. des.
  eapply Own_split in SRC1; et; des; cycle 1.
  { eapply Own_wand_valid, WFR. rewrite SRC Own_op. iIntros "[_ ?]". iFrame; et. }
  rewrite winv_split_empty in SRC0.
  eapply Own_split in SRC0; et; des; cycle 1.
  { eapply Own_wand_valid, WFR. rewrite SRC Own_op. iIntros "[? _]". iFrame; et. }
  exists (a4 ⋅ a3).
  esplits; eauto.
  { eapply Own_wand_valid, WFR. rewrite SRC SRC1 SRC0 !Own_op.
    iIntros "[[? ?] [? ?]]". iFrame. et. }
  { rewrite Own_op SRC4 SRC3. et. }
  ii. eapply lsim_adequacy, PR.
  - eapply ISim_adequacy; et.
    + instantiate (1:= a0⋅a5). rewrite SRC SRC0 SRC1 !Own_op.
      iIntros "[[? ?] [? ?]]". iFrame.
    + rewrite Own_op SRC2 SRC5. et.
    + eapply ISim_wf; eauto.
  - dup WFM. inv WFM. econs. ss. unfold map_snd.
    rewrite !List.map_map.
    eapply sub_perm_nodup in wf_fns; [|eapply SIM; et].
    eapply eq_ind; [apply wf_fns|].
    f_equal; et. extensionalities. destruct H; et.
Qed.

Theorem closed_adequacy_emp (ms mt: Mod.t) P
  (SIM: ISim.t closed ms mt emp%I IstEq)
  :
  refines (ms, P) (mt, P).
Proof using.
  eapply (closed_adequacy P) in SIM.
  ii. exploit SIM; et. i; des. esplits; et.
  i. exploit x1; et. ss. rewrite -bi.emp_sep_1. et.
Qed.

End ADEQUACY.
