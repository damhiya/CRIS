Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import FSpec.

Set Implicit Arguments.

Create HintDb sp.
Hint Rewrite (Seal.sealing_eq "sp") : sp.

Section HEADER.

  Context `{Σ: GRA}.

  Definition sp_type := string -> option fspec.

  Definition to_sp (l : alist string fspec) : sp_type :=
    fun fn => alist_find fn l.

  Definition sp_none : string → option fspec :=
    λ _, Some fspec_none.

  (* Definition to_sp_context (spu : list string) (spk : alist string fspec) := *)
  (*   to_sp (List.map (fun fn => (fn, fspec_trivial)) spu ++ spk). *)

  (* Definition to_closed_sp (l : alist string fspec) : sp_type := *)
  (*   fun fn => match alist_find fn l with *)
  (*             | Some fsp => Some fsp *)
  (*             | _ => Some fspec_trivial *)
  (*             end. *)

  Variant fn_has_spec (sp : sp_type) (fn : string) (fsp : fspec) : Prop :=
  | fn_has_spec_intro fsp1
      (FIND : sp fn = Some fsp1)
      (WEAK : fspec_weaker fsp fsp1).
  Hint Constructors fn_has_spec : core.

  Lemma fn_has_spec_weaker (sp : sp_type) (fn : string) (fsp0 fsp1 : fspec)
      (SPEC : fn_has_spec sp fn fsp1)
      (WEAK : fspec_weaker fsp0 fsp1) :
    fn_has_spec sp fn fsp0.
  Proof using. inv SPEC. econs; eauto. etrans; eauto. Qed.

  Definition sp_sub (sp0 sp1 : sp_type) : Prop :=
    ∀ fn fsp (FIND : sp0 fn = Some fsp), sp1 fn = Some fsp.

  Definition sp_incl (spl : alist string fspec) (gsp : sp_type) : Prop :=
    List.NoDup (List.map fst spl) ∧ sp_sub (to_sp spl) gsp.

  Global Program Instance sp_sub_PreOrder : PreOrder sp_sub.
  Next Obligation.
  Proof using. ii. ss. Qed.
  Next Obligation.
  Proof using. ii. eapply H0, H, FIND. Qed.

  Lemma incl_to_sp sp0 sp1 (INCL : List.incl sp0 sp1)
        (NODUP : List.NoDup (List.map fst sp1)) :
      sp_sub (to_sp sp0) (to_sp sp1).
  Proof using.
    unfold to_sp. ii.
    eapply alist_find_some in FIND. eapply INCL in FIND.
    eapply alist_find_some_iff in FIND; et.
  Qed.

  Definition sp_weaker (sp0 sp1 : sp_type) : Prop :=
    ∀ fn fsp0 (FINDTGT : sp0 fn = Some fsp0),
      ∃ fsp1, (<<FINDSRC : sp1 fn = Some fsp1>>) ∧ (<<WEAKER : fspec_weaker fsp0 fsp1>>).

  Global Program Instance sp_weaker_PreOrder : PreOrder sp_weaker.
  Next Obligation. ii. esplits; eauto. refl. Qed.
  Next Obligation.
    ii. r in H. r in H0. exploit H; et. intro T; des.
    exploit H0; et. intro U; des. esplits; eauto. etrans; et.
  Qed.

  Lemma sp_sub_weaker : sp_sub <2= sp_weaker.
  Proof using.
    ii. eapply PR in FINDTGT. esplits; et. refl.
  Qed.

  Lemma incl_sp_sub :
    ∀ sp0 sp1 (NODUP : List.NoDup (List.map fst sp1)) (INCL : List.incl sp0 sp1),
      sp_sub (to_sp sp0) (to_sp sp1).
  Proof using.
    unfold to_sp.
    ii. eapply alist_find_some in FIND.
    destruct (alist_find fn sp1) eqn:T.
    { eapply alist_find_some in T.
      eapply INCL in FIND.
      destruct (classic (fsp = f)).
      { subst. esplits; et. }
      exfalso.
      eapply NoDup_inj_aux in NODUP; revgoals.
      { eapply T. }
      { eapply FIND. }
      { ii; clarify. }
      ss.
    }
    eapply alist_find_none in T; et. exfalso. et.
  Qed.

  Lemma incl_weaker :
    ∀ sp0 sp1 (NODUP : List.NoDup (List.map fst sp1)) (INCL : List.incl sp0 sp1),
      sp_weaker (to_sp sp0) (to_sp sp1).
  Proof using. i. eapply sp_sub_weaker. eapply incl_sp_sub; et. Qed.

  Lemma app_sub : ∀ sp0 sp1, sp_sub (to_sp sp0) (to_sp (sp0 ++ sp1)).
  Proof using. unfold to_sp. ii. eapply alist_find_app in FIND. esplits; eauto. Qed.

  Lemma app_weaker : ∀ sp0 sp1, sp_weaker (to_sp sp0) (to_sp (sp0 ++ sp1)).
  Proof using. i. eapply sp_sub_weaker. eapply app_sub. Qed.

  (* Lemma to_sp_context_sub spu spk spall *)
  (*     (INCL : List.incl spk spall) *)
  (*     (NODUP : List.NoDup (spu ++ (List.map fst spall))) : *)
  (*   sp_sub (to_sp_context spu spk) (to_closed_sp spall). *)
  (* Proof using. *)
  (*   unfold to_sp_context, to_sp, to_closed_sp. ii. *)
  (*   rewrite alist_find_app_o in FIND.  *)
  (*   destruct (alist_find fn (List.map (fun fn => (fn, fspec_trivial)) spu)) eqn:EQ; clarify. *)
  (*   { eapply alist_find_some in EQ. eapply in_map_iff in EQ. des. clarify. *)
  (*     des_ifs. exfalso. eapply alist_find_some in Heq. *)
  (*     eapply NoDup_app_disjoint in NODUP; et. *)
  (*     eapply in_map with (f:=fst) in Heq. ss. } *)
  (*   { eapply alist_find_some in FIND. eapply INCL in FIND. *)
  (*     eapply alist_find_some_iff in FIND; et. *)
  (*     rewrite FIND; et. eapply nodup_app_r; et. } *)
  (*   Unshelve. exact string_Dec. *)
  (* Qed. *)

  (* Lemma to_closed_sp_weaker sp : sp_sub (to_sp sp) (to_closed_sp sp). *)
  (* Proof using. unfold to_closed_sp, to_sp. ii. rewrite FIND. auto. Qed. *)

  (* Lemma incl_to_closed_sp sp0 sp1 (INCL : List.incl sp0 sp1) (NODUP : List.NoDup (List.map fst sp1)) : *)
  (*   sp_sub (to_sp sp0) (to_closed_sp sp1). *)
  (* Proof using. *)
  (*   unfold to_sp, to_closed_sp. ii. *)
  (*   eapply alist_find_some in FIND. eapply INCL in FIND. *)
  (*   eapply alist_find_some_iff in FIND; et. *)
  (*   rewrite FIND. et. *)
  (* Unshelve. exact string_Dec. *)
  (* Qed. *)

End HEADER.

(* Ltac sp_tac := *)
(*   match goal with *)
(*   | [ |- to_sp_context _ _ _ = _ ] => *)
(*     unfold to_sp_context, to_sp; *)
(*     autounfold with sp; autorewrite with sp; simpl *)
(*   | [ |- to_sp ?xs _ = _ ] => *)
(*     unfold to_sp; *)
(*     autounfold with sp; autorewrite with sp; simpl *)
(*   | [ |- to_closed_sp ?xs _ = _ ] => *)
(*     unfold to_closed_sp; *)
(*     autounfold with sp; autorewrite with sp; simpl *)
(*   | [ |- alist_find _ ?xs = _ ] => *)
(*     match type of xs with *)
(*     | (list (string * fspec)) => *)
(*       autounfold with sp; autorewrite with sp; simpl *)
(*     end *)
(*   | [H : alist_find _ ?xs = _ |- _ ] => *)
(*     match type of xs with *)
(*     | (list (string * fspec)) => *)
(*       autounfold with sp in H; autorewrite with sp in H; simpl in H *)
(*     end *)
(*   | [H : to_sp_context _ _ _ = _ |- _ ] => *)
(*     unfold to_sp_context, to_sp in H; *)
(*     autounfold with sp in H; autorewrite with sp in H; simpl in H *)
(*   | [H : to_sp ?xs _ = _ |- _ ] => *)
(*     unfold to_sp in H; *)
(*     autounfold with sp in H; autorewrite with sp in H; simpl in H *)
(*   | [H : to_closed_sp ?xs _ = _ |- _ ] => *)
(*     unfold to_closed_sp in H; *)
(*     autounfold with sp in H; autorewrite with sp in H; simpl in H *)
(*   end. *)

(* Ltac sp_sub_tac := *)
(*   i; eapply incl_to_sp; *)
(*   [ autounfold with sp; autorewrite with sp; ii; ss; des; clarify; auto| *)
(*     autounfold with sp; autorewrite with sp; (hrepeat do 1 econs); ii; ss; des; ss]. *)

(* Ltac sp_context_sub_tac := *)
(*   i; eapply to_sp_context_sub; *)
(*   [ autounfold with sp; autorewrite with sp; ii; ss; des; clarify; auto| *)
(*     autounfold with sp; autorewrite with sp; (hrepeat do 1 econs); ii; ss; des; ss]. *)

(* Ltac ors_tac := hrepeat do 1 ((try by (ss; left; ss)); right). *)
