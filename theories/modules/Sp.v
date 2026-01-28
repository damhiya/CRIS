(* TODO : Can sp and spl be a same type i.e. gmap? If possible, unify them into single types
and maybe define ⊆ relations on them so that sp_incl and the variants are notationally simple *)
Require Import Common FSpec.
From iris.proofmode Require Import proofmode.

Variant speckey : Type :=
| speckey_fn (fn : string)
| speckey_entry
| speckey_concE.
Global Instance speckey_eq_dec : EqDecision speckey.
Proof. solve_decision. Qed.
Global Instance speckey_countable : Countable speckey.
Proof.
  refine (inj_countable'
   (λ k, match k with speckey_fn fn => Some (Some fn) | speckey_entry => Some None | _ => None end)
   (λ k,
    match k with
    | Some (Some fn) => speckey_fn fn
    | Some None => speckey_entry
    | _ => speckey_concE end) _).
   by intros [].
Qed.

Global Notation specmap := (gmap speckey fspec).

Section sp.
  Context `{Σ : GRA}.

  (* Definition spl_type : Type := alist speckey (option fspec). *)

  (* Definition to_sp (l : spl_type) : specmap :=
    λ k, or_else (alist_find k l) (Some fspec_bot). *)

  (* Definition sp_none : specmap := const None. *)

  (* Variant fn_has_spec (sp : specmap) (fn : string) (fsp : fspec) : Prop :=
  | fn_has_spec_intro (WEAK : ⊢ fspec_imply (fspec_flat (sp !! (speckey_fn fn))) fsp).
  Hint Constructors fn_has_spec : core. *)

  (* Variant fn_has_spec_in (spl : spl_type) (fn : string) (fsp : fspec) : Prop :=
  | fn_has_spec_in_intro
      fsp_real
      (SPEC: alist_find (speckey_fn fn) spl = Some fsp_real)
      (WEAK : fspec_imply (fspec_flat fsp_real) fsp).
  Hint Constructors fn_has_spec_in : core. *)

  (* Lemma fn_has_weaker_spec (sp : specmap) (fn : string) (fsp0 fsp1 : fspec)
      (SPEC : fn_has_spec sp fn fsp0)
      (WEAK : ⊢ fspec_imply fsp0 fsp1) :
    fn_has_spec sp fn fsp1.
  Proof using. inv SPEC. econs; eauto. etrans; eauto. Qed. *)

  (* Lemma fn_has_weaker_spec_in (spl : spl_type) (fn : string) (fsp0 fsp1 : fspec)
      (SPEC : fn_has_spec_in spl fn fsp0)
      (WEAK : fspec_imply fsp0 fsp1) :
    fn_has_spec_in spl fn fsp1.
  Proof using. inv SPEC. econs; eauto. etrans; eauto. Qed. *)

  (* Definition sp_imply (sp0 sp1 : specmap) : Prop :=
    ∀ fn, fspec_imply (fspec_flat (sp0 !! (speckey_fn fn))) (fspec_flat (sp1 !! (speckey_fn fn))). *)

  (* Global Program Instance sp_imply_PreOrder : PreOrder sp_imply.
  Next Obligation. ii. exists x1. esplits; et. Qed.
  Next Obligation.
    intros x y z Hxy Hyz fn z1. exploit Hyz; et; intros [y1 [Hypre Hypost]].
    exploit Hxy; et; intros [x1 [Hxpre Hxpost]].
    exists x1. split; ii.
    - rewrite Hypre Hxpre. iIntros ">>H". et.
    - rewrite Hxpost Hypost. iIntros ">>H". et.
  Qed. *)

  (* Commented out since fspec_imply' erased *)
  (* Definition sp_imply' (sp0 sp1 : specmap) : Prop :=
    ∀ fn, fspec_imply' (fspec_flat (sp0 fn)) (fspec_flat (sp1 fn)).

  Global Program Instance sp_imply'_PreOrder : PreOrder sp_imply'.
  Next Obligation. ii. refl. Qed.
  Next Obligation.
    intros x y z Hxy Hyz fn. specialize (Hxy fn); specialize (Hyz fn).
    destruct (x fn), (y fn), (z fn); ss; try by etrans; et.
    destruct f, f0; ss. etrans; et.
  Qed. *)

  (* Definition sp_sub (sp0 sp : specmap) : Prop :=
    ∀ fn, sp0 fn = Some fspec_bot ∨ sp0 fn = sp fn. *)

  (* Definition spl_sub (spl0 spl : spl_type) : Prop :=
    ∀ fno fsp, alist_find fno spl0 = Some fsp → alist_find fno spl = Some fsp. *)

  (* Definition sp_incl (l : spl_type) (sp : specmap) : Prop :=
    NoDup (l.*1) ∧
    (∀ fn fsp, alist_find (speckey_fn fn) l = Some fsp → sp (speckey_fn fn) = fsp). *)

  (* Lemma sp_incl_to_sp (l : spl_type) :
    NoDup (l.*1) → sp_incl l (to_sp l).
  Proof.
    intros ?; split; first done.
    induction l as [|[??]?]; ss; intros ??; rewrite eq_rel_dec_correct; des_ifs; ss; ii; clarify.
    { rewrite /to_sp; ss; destruct dec; ss. }
    { rewrite /to_sp; s; rewrite eq_rel_dec_correct; des_ifs; ss; clarify.
      rewrite H0; ss.
    }
  Qed. *)

  (* Lemma sp_sub_imply sp0 sp
    (SUB: sp_sub sp0 sp)
    :
    sp_imply sp0 sp.
  Proof.
    r; i. destruct (SUB fn); rewrite H; s.
    - eapply fspec_bot_strongest.
    - refl.
  Qed. *)

  (* Lemma sp_incl_sub l sp
    (INCL: sp_incl l sp)
    :
    sp_sub (to_sp l) sp.
  Proof.
    r. i. r in INCL. des. rewrite /to_sp.
    destruct (alist_find (Some fn) l) eqn: E; s; et.
    erewrite INCL0; et.
  Qed. *)

  (* Lemma incl_sp_sub :
    ∀ sp0 sp1 (NODUP : List.NoDup (List.map fst sp1)) (INCL : List.incl sp0 sp1),
      sp_sub (to_sp sp0) (to_sp sp1).
  Proof using.
    r; i. rewrite /to_sp.
    destruct (alist_find (Some fn) sp0) eqn:E; ss; et.
    eapply alist_find_some in E.
    eapply alist_find_some_iff in NODUP; et.
    rewrite NODUP. et.
  Qed. *)

  (* Lemma app_imply : ∀ sp0 sp1, sp_sub (to_sp sp0) (to_sp (sp0 ++ sp1)) .
  Proof using.
    r; i. rewrite /to_sp.
    destruct (alist_find (Some fn) sp0) eqn: E; et.
    right. s. rewrite alist_find_app_o E. et.
  Qed. *)

End sp.
