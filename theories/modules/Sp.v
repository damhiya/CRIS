Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import FSpec.

Set Implicit Arguments.

Create HintDb sp.
Hint Rewrite (Seal.sealing_eq "sp") : sp.

Section HEADER.

  Context `{Σ: GRA}.

  Definition spl_type := alist (option string) (option fspec).
  Definition sp_type := (string -> option fspec).

  Definition to_sp (l : spl_type) : sp_type :=
    (fun fn => or_else (alist_find (Some fn) l) (Some fspec_bot)).

  Definition sp_none : sp_type := (const None).

  Variant fn_has_spec (sp : sp_type) (fn : string) (fsp : fspec) : Prop :=
    | fn_has_spec_intro
        (WEAK : fspec_imply (fspec_flat (sp fn)) fsp).
  Hint Constructors fn_has_spec : core.

  Lemma fn_has_weaker_spec (sp : sp_type) (fn : string) (fsp0 fsp1 : fspec)
      (SPEC : fn_has_spec sp fn fsp0)
      (WEAK : fspec_imply fsp0 fsp1) :
    fn_has_spec sp fn fsp1.
  Proof using. inv SPEC. econs; eauto. etrans; eauto. Qed.

  Definition sp_imply (sp0 sp1 : sp_type) : Prop :=
    ∀ fn, fspec_imply (fspec_flat (sp0 fn)) (fspec_flat (sp1 fn)).

  Global Program Instance sp_imply_PreOrder : PreOrder sp_imply.
  Next Obligation. ii. exists x1. esplits; et. Qed.
  Next Obligation.
    ii. exploit H0; et. i; des. exploit H; et. i; des.
    exists x2. split; ii.
    - rewrite PRE PRE0. iIntros ">>H". et.
    - rewrite POST0 POST. iIntros ">>H". et.
  Qed.

  Definition sp_sub (sp0 sp: sp_type) : Prop :=
    ∀ fn, sp0 fn = Some fspec_bot ∨ sp0 fn = sp fn.

  Definition sp_incl (l : spl_type) (sp : sp_type) : Prop :=
    List.NoDup (List.map fst l) ∧
    (∀ fn fsp, alist_find (Some fn) l = Some fsp → sp fn = fsp).

  Lemma sp_sub_imply sp0 sp
    (SUB: sp_sub sp0 sp)
    :
    sp_imply sp0 sp.
  Proof.
    r; i. destruct (SUB fn); rewrite H; s.
    - eapply fspec_bot_strongest.
    - refl.
  Qed.

  Lemma sp_incl_sub l sp
    (INCL: sp_incl l sp)
    :
    sp_sub (to_sp l) sp.
  Proof.
    r. i. r in INCL. des. rewrite /to_sp.
    destruct (alist_find (Some fn) l) eqn: E; s; et.
    erewrite INCL0; et.
  Qed.

  Lemma incl_sp_sub :
    ∀ sp0 sp1 (NODUP : List.NoDup (List.map fst sp1)) (INCL : List.incl sp0 sp1),
      sp_sub (to_sp sp0) (to_sp sp1).
  Proof using.
    r; i. rewrite /to_sp.
    destruct (alist_find (Some fn) sp0) eqn:E; ss; et.
    eapply alist_find_some in E.
    eapply alist_find_some_iff in NODUP; et.
    rewrite NODUP. et.
  Qed.

  Lemma app_imply : ∀ sp0 sp1, sp_sub (to_sp sp0) (to_sp (sp0 ++ sp1)) .
  Proof using.
    r; i. rewrite /to_sp.
    destruct (alist_find (Some fn) sp0) eqn: E; et.
    right. s. rewrite alist_find_app_o E. et.
  Qed.

End HEADER.
