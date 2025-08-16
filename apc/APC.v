Require Import CRIS.

Require Import APCHeader.

Set Implicit Arguments.

Section FSPEC.

  Context {Σ: GRA}.
  
  (* fspec is only about args, varg is always ordinal *)
  Definition fspec_apc {X : Type} (o: X → Ord.t) (DPQ: X → (Any.t → iProp Σ) * (Any.t → iProp Σ)) : fspec :=
    mk_fspec (λ x y a, (((fst ∘ DPQ) x a: iProp Σ) ∗ ⌜∃ vo: Ord.t, y = vo↑ ∧ ((o x) <= vo)%ord⌝)%I)
             (λ x _ a, (((snd ∘ DPQ) x a: iProp Σ))%I).

  Definition pure_body : Any.t → itree crisE Any.t :=
    cfunN (λ dep_ord: Ord.t, trigger (Call APCHdr.apc dep_ord↑);;; Ret ()).

End FSPEC.

Section apc.

  Context {Σ: GRA}.  

  Variable dep_ord: Ord.t.
  Variable SpPure: spl_type.

  Program Fixpoint _APC (wid_ord: Ord.t) {wf Ord.lt wid_ord}: itree crisE () :=
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
      guarantee (is_Some (alist_find (Some fn) SpPure) ∧ (o < dep_ord)%ord);;;
      trigger (Call fn o↑);;;
      _APC wid_next
  .
  Next Obligation. ii. auto.  Defined.
  Next Obligation. eapply Ord.lt_well_founded. Qed.

  Definition APC: itree crisE unit :=
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
      guarantee (is_Some (alist_find (Some fn) SpPure) ∧ (o < dep_ord)%ord);;;
      trigger (Call fn o↑);;;
      _APC wid_next.
  Proof using.
    i. unfold _APC. rewrite Fix_eq; eauto.
    { ii. repeat f_equal. extensionality break. destruct break; ss.
      do 7 (repeat f_equal; extensionalities). eapply H. }
  Qed.
  Global Opaque _APC.

End apc.

Section aux.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Lemma map_fst_map_map_snd_refl {A B C} (f: B → C) (l: list (A * B)):
    map fst (map (map_snd f) l) = map fst l.
  Proof using.
    induction l; ss.
    destruct a; ss. f_equal; et.
  Qed.

  Definition find_body md fn :=
    alist_find (Some fn) (map (map_snd SB.sandbox_body) (Mod.fnsems md)).

  Definition pure_specbody sp img msk scp fspo :=
    (λ arg : Any.t,
      SB.sandbox_body
        (SModTr.trans_ktree sp (img, msk, scp, (fspo, pure_body))) arg).

  Definition pure: itree crisE Any.t :=
    o <- trigger (Choose Ord.t);;
    trigger (Call APCHdr.apc o↑).

End aux.
