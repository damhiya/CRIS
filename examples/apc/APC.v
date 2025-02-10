Require Import CRIS.

Require Import APCHeader.

Set Implicit Arguments.

Section wrapper.

  Context {Σ: GRA}.
  Notation iProp := (iProp Σ).

  (* fspec is only about args, varg is always ordinal *)
  Definition fspec_apc {X : Type} (o: X → Ord.t) (DPQ: X → (Any.t → iProp) * (Any.t → iProp)) : fspec :=
    mk_fspec (λ _ x y a, (((fst ∘ DPQ) x a: iProp) ∗ ⌜∃ vo: Ord.t, y = vo↑ ∧ ((o x) <= vo)%ord⌝)%I)
             (λ _ x _ a, (((snd ∘ DPQ) x a: iProp))%I).

  Definition pure_body : Any.t → itree hmodE Any.t :=
    cfunN (λ dep_ord: Ord.t, trigger (Call APCName.apc dep_ord↑);;; Ret ()).

End wrapper.

Section apc.

  Context {Σ: GRA}.

  Variable dep_ord: Ord.t.
  Variable SpcPure: string → option fspec.

  Program Fixpoint _APC (wid_ord: Ord.t) {wf Ord.lt wid_ord}: itree hmodE () :=
    break <- trigger (Choose _);;
    if break: bool
    then Ret tt
    else
      (* width ordinal *)
      wid_next <- trigger (Choose Ord.t);;
      trigger (Choose (wid_next < wid_ord)%ord);;;
      'fn:_ <- trigger (Choose _);;
      (* depth ordinal *)
      o <- trigger (Choose Ord.t);;
      guarantee (is_Some (SpcPure fn) ∧ (o < dep_ord)%ord);;;
      trigger (Call fn o↑);;;
      _APC wid_next
  .
  Next Obligation. ii. auto.  Qed.
  Next Obligation. eapply Ord.lt_well_founded. Qed.

  Definition APC: itree hmodE unit :=
    wid_ord <- trigger (Choose _);;
    _APC wid_ord
  .

  Lemma unfold_APC wid_ord:
    _APC wid_ord
    =
    break <- trigger (Choose _);;
    if break: bool
    then Ret tt
    else
      (* horizontal ordinal *)
      wid_next <- trigger (Choose Ord.t);;
      trigger (Choose (wid_next < wid_ord)%ord);;;
      'fn:_ <- trigger (Choose _);;
      o <- trigger (Choose Ord.t);;
      guarantee (is_Some (SpcPure fn) ∧ (o < dep_ord)%ord);;;
      trigger (Call fn o↑);;;
      _APC wid_next.
  Proof.
    i. unfold _APC. rewrite Fix_eq; eauto.
    { ii. repeat f_equal. extensionality break. destruct break; ss.
      do 7 (repeat f_equal; extensionalities). eapply H. }
  Qed.
  Global Opaque _APC.

End apc.

Section aux.
  Context {Σ: GRA}.

  Lemma map_fst_map_map_snd_refl {A B C} (f: B → C) (l: list (A * B)):
    map fst (map (map_snd f) l) = map fst l.
  Proof.
    induction l; ss.
    destruct a; ss. f_equal; et.
  Qed.

  Definition find_body md fn :=
    alist_find fn (map (map_snd (λ (kb : list string * (Any.t → itree hmodE Any.t)) (arg : Any.t), HMod.sandbox (fst kb) ((snd kb) arg))) (HMod.fnsems md)).

  Definition pure_specbody scopes ginv spc fsp :=
    (λ arg : Any.t,
      HMod.sandbox scopes
        (interp_sb_hp ginv spc
           {| fsb_fspec := fsp; fsb_body := pure_body |} arg)).

  Definition pure: itree hmodE Any.t :=
    o <- trigger (Choose Ord.t);;
    trigger (Call APCName.apc o↑).

End aux.