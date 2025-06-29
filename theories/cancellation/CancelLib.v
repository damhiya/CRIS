Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import SMod.

Set Implicit Arguments.

Section CancelLib.
  Context `{Σ: GRA}.

  Definition sp_from (md: SMod.t) : sp_type :=
    to_sp (List.map (map_snd (fst ∘ snd)) md.(SMod.fnsems)).

  Definition smod_wf (md: SMod.t) :=
    ∀ fn msk scp fspo bd
      (FIND: alist_find (Some fn) (SMod.fnsems md) = Some (false, msk, scp, (fspo, bd))),
    fspo = None.

  Definition valid_param (md: SMod.t) img msk scp :=
    ∃ fno sbd, alist_find fno (SMod.fnsems md) = Some (img, msk, scp, sbd).

  Definition has_real_spec (md: SMod.t) (fn: string) : Prop :=
    ∃ msk scp, valid_param md false msk scp ∧ msk fn.

  Definition valid_sp (md: SMod.t) (sp: sp_type) : Prop :=
    sp_imply (sp_from md) sp ∧
    ∀ fn (NS: has_real_spec md fn), sp fn = None.
  
  Definition Forall2i X Y (R: nat -> X -> Y -> Prop) (xs: list X) (ys: list Y) :=
    length xs = length ys ∧
    ∀ i x y (EQx: xs !! i = Some x) (EQy: ys !! i = Some y),
      R i x y.

  Lemma Forall2i_nth
    X Y (xs: list X) (ys: list Y) (R: nat -> X -> Y -> Prop) i
    (REL: Forall2i R xs ys)
    (NTH: i < List.length xs)
    :
    ∃ x y,
    xs !! i = Some x /\
    ys !! i = Some y /\
    R i x y.
  Proof using.
    destruct REL. revert_until xs. induction xs; i.
    - destruct ys; ss. destruct i; try nia.
    - destruct ys; ss. destruct i; s. { esplits; et. }
      eapply (IHxs ys (λ i, R (S i))); et; nia.
  Qed.

  Lemma valid_solve (a b c: Σ) :
    ✓ a -> a ≡  b ⋅ c -> ✓ b.
  Proof using.
    i. eapply cmra_valid_op_l. setoid_rewrite <- H0. eauto.
  Qed.

  Lemma valid_extends (r a b: Σ):
    b ≼ a -> ✓(r ⋅ a) -> ✓ (r ⋅ b).
  Proof using.
    i. apply cmra_mono_l with (z:=r) in H.
    eapply cmra_valid_included; eauto.
  Qed.

  Lemma Own_bupd_valid (r a b: Σ):
    (Own r ⊢|==> Own a ∗ Own b) -> ✓ r -> ✓ (a ⋅ b).
  Proof using.
    i. eapply Own_wand_valid with (a1 := r); eauto.
    iIntros "H". iApply Own_op. iStopProof. eauto.
  Qed.

  Lemma list_lookup_length {X} (x: X) l:
    (l ++ [x]) !! (base.length l) = Some x.
  Proof using.
    eapply lookup_snoc_Some; right; eauto.
  Qed.

End CancelLib.
