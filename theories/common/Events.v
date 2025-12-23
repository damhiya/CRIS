Require Import Coqlib.
Require Export ITreelib.
Require Export AList.
Require Import Any.

Require Import base_logic.
Require Import own.
(* TODO : delete this dependency after gra mod *)

Set Implicit Arguments.

Variant coreE : Type -> Type :=
| Choose (X : Type) : coreE X
| Take X : coreE X
| IO {I : Type} {O : Type} (fn : string) (args : I) : coreE O.

Variant stateE (V : Type) : Type :=
| SUpdate (run : Any.t -> Any.t * V) : stateE V.

Variant callE : Type -> Type :=
| Call (fn : string) (args : Any.t) : callE Any.t
| Spawn (fn : string) (args : Any.t) : callE nat
| Yield (tid : nat) : callE unit
| GetTid : callE nat.

Definition sPut x : stateE unit := SUpdate (fun _ => (x, tt)).
Definition sGet : stateE Any.t := SUpdate (fun x => (x, x)).

Definition lmodE : Type -> Type := callE +' stateE +' coreE.

Section EVENTS_HMOD.
  Context {Σ : GRA}.

  Definition key := (string * string)%type.

  Global Program Instance dec_key `{Dec string} : Dec key.
  Next Obligation.
    intro DEC. i. destruct a0, a1.
    destruct (DEC s0 s2).
    - subst. destruct (DEC s s1).
      + subst. left. refl.
      + right. ii. apply n. inv H.
    - right. ii. apply n. inv H.
  Defined.

  Definition sf (s : string) (f : string) := (s,f).

  Variant pgE : Type -> Type :=
  | SPut (k : key) (v : Any.t) : pgE unit
  | SGet (k : key) : pgE Any.t.

  Variant agE : Type -> Type :=
  | Assume (P : iProp Σ) : agE unit
  | AssumeRes (r : Σ) : agE unit
  | Guarantee (P : iProp Σ) : agE unit.

  Definition crisE := agE +' callE +' pgE +' coreE.
End EVENTS_HMOD.

Section WRAP.
  Context {E : Type -> Type}.
  Context `{coreE -< E}.

  Definition assumeK {R} (P : Prop) (itr : itree E R) := vis (Take P) (fun _ => itr).

  Definition guaranteeK {R} (P : Prop) (itr : itree E R) := vis (Choose P) (fun _ => itr).

  Definition assume (P : Prop) : itree E unit := trigger (Take P) ;;; Ret tt.

  Definition guarantee (P : Prop) : itree E unit := trigger (Choose P) ;;; Ret tt.

  Definition unwrapUK {X R} (x : option X) (ktr : X -> itree E R) : itree E R :=
    match x with
    | Some x => ktr x
    | None => v <- trigger (Take False);; match v: False with end
    end.

  Definition unwrapNK {X R} (x : option X) (ktr : X -> itree E R) : itree E R :=
    match x with
    | Some x => ktr x
    | None => v <- trigger (Choose False);; match v: False with end
    end.

  Definition unwrapU {X} (x : option X) : itree E X :=
    match x with
    | Some x => Ret x
    | None => v <- trigger (Take False);; match v: False with end
    end.

  Definition unwrapN {X} (x : option X) : itree E X :=
    match x with
    | Some x => Ret x
    | None => v <- trigger (Choose False);; match v: False with end
    end.

  Definition triggerUB {A} : itree E A := unwrapU None.

  Definition triggerNB {A} : itree E A := unwrapN None.

  Definition unleftU {X Y} (xy : X + Y) : itree E X :=
    match xy with
    | inl x => Ret x
    | inr y => triggerUB
    end.

  Definition unleftN {X Y} (xy : X + Y) : itree E X :=
    match xy with
    | inl x => Ret x
    | inr y => triggerNB
    end.

  Definition unrightU {X Y} (xy : X + Y) : itree E Y :=
    match xy with
    | inl x => triggerUB
    | inr y => Ret y
    end.

  Definition unrightN {X Y} (xy : X + Y) : itree E Y :=
    match xy with
    | inl x => triggerNB
    | inr y => Ret y
    end.

  Lemma assume_assumeK (P : Prop) :
    assume P = assumeK P (Ret tt).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma assumeK_assume {R} (P : Prop) (itr : itree E R) :
    assumeK P itr = assume P;;; itr.
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma assumeK_bind {U T} (P : Prop) (k1 : itree E U) (k2 : U -> itree E T) :
    (assumeK P k1 >>= k2) = assumeK P (k1 >>= k2).
  Proof using.
    eapply observe_eta; ss.
  Qed.

  Lemma guarantee_guaranteeK (P : Prop) :
    guarantee P = guaranteeK P (Ret tt).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma guaranteeK_guarantee {R} (P : Prop) (k : itree E R) :
    guaranteeK P k = guarantee P;;; k.
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma guaranteeK_bind {U T} (P : Prop) (k1 : itree E U) (k2 : U -> itree E T) :
    (guaranteeK P k1 >>= k2) = guaranteeK P (k1 >>= k2).
  Proof using.
    eapply observe_eta; ss.
  Qed.

  Lemma unwrapU_unwrapUK {X} (x : option X) :
    unwrapU x = unwrapUK x (fun x => Ret x).
  Proof using.
    eapply observe_eta; ss.
  Qed.

  Lemma unwrapUK_unwrapU {X R} (x : option X) (k : X -> itree E R) :
    unwrapUK x k = unwrapU x >>= k.
  Proof using.
    eapply observe_eta; destruct x; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma unwrapUK_bind {X U T} (x : option X) (k1 : X -> itree E U) (k2 : U -> itree E T) :
    (unwrapUK x k1 >>= k2) = unwrapUK x (fun x => k1 x >>= k2).
  Proof using.
    eapply observe_eta; destruct x; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma unwrapN_unwrapNK {X} (x : option X) :
    unwrapN x = unwrapNK x (fun x => Ret x).
  Proof using.
    eapply observe_eta; ss.
  Qed.

  Lemma unwrapNK_unwrapN {X R} (x : option X) (k : X -> itree E R) :
    unwrapNK x k = unwrapN x >>= k.
  Proof using.
    eapply observe_eta; destruct x; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma unwrapNK_bind {X U T} (x : option X) (k1 : X -> itree E U) (k2 : U -> itree E T) :
    (unwrapNK x k1 >>= k2) = unwrapNK x (fun x => k1 x >>= k2).
  Proof using.
    eapply observe_eta; destruct x; ss. f_equal. extensionality x. ss.
  Qed.
End WRAP.

Notation "f '?'" := (unwrapU f) (at level 9).
Notation "f '!'" := (unwrapN f) (at level 9).
Notation "s ↯ f" := (sf s f) (at level 9).

Section FancyReal.
  Context `{Σ: GRA}.

  Definition CRIS_FancyReal := "CRIS-FancyReal".
  Global Opaque CRIS_FancyReal.

  (* Epilogue for propheciable specification: extracts the exact resource from precondition *)
  Definition RealUpdate {X} pre post : itree crisE unit :=
    Seal.sealing CRIS_FancyReal (
      pr <- trigger (Choose Σ);;
      trigger (Guarantee (∀ (x : X), pre x ==∗ Own pr ∗ post x));;;
      trigger (AssumeRes pr)).

  Definition RealUpdateK {X R} pre post ktr : itree crisE R :=
    @RealUpdate X pre post >>= ktr.

  Lemma RealUpdate_RealUpdateK {X} pre post :
    @RealUpdate X pre post = RealUpdateK pre post (λ x, Ret x).
  Proof using. rewrite /RealUpdateK. by ired. Qed.

  Lemma RealUpdateK_RealUpdate {X R} pre post k :
    @RealUpdateK X R pre post k = RealUpdate pre post >>= k.
  Proof using. refl. Qed.

  Lemma RealUpdateK_bind
      {X R1 R2} pre post
      (k1 : unit → itree crisE R1) (k2 : R1 → itree crisE R2) :
    @RealUpdateK X R1 pre post k1 >>= k2 =
    RealUpdateK pre post (λ x, k1 x >>= k2).
  Proof using. rewrite /RealUpdateK. by ired. Qed.
End FancyReal.

Section SYNTAX.
  Context `{coreE -< E, callE -< E, pgE -< E}.

  Definition cfunN {X Y} (body : X -> itree E Y) : Any.t -> itree E Any.t :=
    λ varg, varg <- varg↓!;; vret <- body varg;; Ret vret↑.

  Definition cfunU {X Y} (body : X -> itree E Y) : Any.t -> itree E Any.t :=
    λ varg, varg <- varg↓?;; vret <- body varg;; Ret vret↑.

  Definition ccallU {X Y} fn (varg : X) : itree E Y :=
    vret <- trigger (Call fn (varg↑));; vret↓?.

  Definition ccallN {X Y} (fn : string) (varg : X) : itree E Y :=
    vret <- trigger (Call fn (varg↑));; vret↓!.

  Definition cput {T} k (v : T) : itree E unit :=
    trigger (SPut k v↑).

  Definition cgetU {T} k : itree E T :=
    v <- trigger (SGet k);; v↓?.

  Definition cgetN {T} k : itree E T :=
    v <- trigger (SGet k);; (v↓!).
End SYNTAX.

Lemma case_itrL R (itr : itree lmodE R) :
  (exists r, itr = Ret r) \/
  (exists itr', itr = tau;; itr') \/
  (exists V (e : coreE V) ktr, itr = v <- trigger e;; ktr v) \/
  (exists V run ktr, itr = v <- trigger (@SUpdate V run);; ktr v) \/
  (exists V (e : callE V) ktr, itr = v <- trigger e;; ktr v).
Proof.
  ides itr; eauto.
  right. right. destruct e as [e | [e | e] ].
  - do 2 right. esplits. rewrite bind_trigger. eauto.
  - destruct e. right. left. esplits. rewrite bind_trigger. eauto.
  - left. esplits. rewrite bind_trigger. eauto.
Qed.

Lemma case_itrH `{Σ : GRA} R (itrH : itree crisE R) :
  (exists v, itrH = Ret v) \/
  (exists itrH', itrH = tau;; itrH') \/
  (exists P itrH', itrH = (trigger (Assume P);;; itrH')) \/
  (exists r itrH', itrH = (trigger (AssumeRes r) >>= itrH')) \/
  (exists P itrH', itrH = (trigger (Guarantee P);;; itrH')) \/
  (exists R (c : callE R) ktrH', itrH = (trigger c >>= ktrH')) \/
  (exists R (s : pgE R) ktrH', itrH = (trigger s >>= ktrH')) \/
  (exists R (e : coreE R) ktrH', itrH = (trigger e >>= ktrH')).
Proof using.
  ides itrH; eauto.
  right; right.
  destruct e; [destruct a|destruct s; [|destruct s]].
  - left. exists P, (k()). unfold trigger. rewrite bind_vis.
    repeat f_equal. extensionality x. destruct x. rewrite bind_ret_l. eauto.
  - do 1 right; left. exists r, k. unfold trigger. rewrite bind_vis.
    repeat f_equal. extensionality x. rewrite bind_ret_l. eauto.
  - do 2 right; left. exists P, (k()). unfold trigger. rewrite bind_vis.
    repeat f_equal. extensionality x. destruct x. rewrite bind_ret_l. eauto.
  - do 3 right; left. exists X, c, k. unfold trigger. rewrite bind_vis.
    repeat f_equal. extensionality x. rewrite bind_ret_l. eauto.
  - do 4 right; left. exists X, p, k. unfold trigger. rewrite bind_vis.
    repeat f_equal. extensionality x. rewrite bind_ret_l. eauto.
  - do 5 right. exists X, c, k. unfold trigger. rewrite bind_vis.
    repeat f_equal. extensionality x. rewrite bind_ret_l. eauto.
Qed.

Section MASK.
  Context `{Σ: GRA}.

  Definition emask : Type := ∀ X, crisE X → bool.

  Definition img_msk (msk: emask): Prop :=
    (∀ T, msk _ (subevent _ (Take T)) = true)
    ∧ (∀ T, msk _ (subevent _ (Choose T)) = true)
    ∧ (∀ P, msk _ (subevent _ (Assume P)) = true)
    ∧ (∀ P, msk _ (subevent _ (AssumeRes P)) = true)
    ∧ (∀ P, msk _ (subevent _ (Guarantee P)) = true).

  Definition msk_scp (scp : gmultiset string) : emask :=
    λ X e,
      match e with
      | inl1 _ => true
      | inr1 (inl1 _) => true
      | inr1 (inr1 (inl1 (SPut k v))) => decide (k ∈ scp)
      | inr1 (inr1 (inl1 (SGet k))) => decide (k ∈ scp)
      | inr1 (inr1 (inr1 _)) => true
      end.

  Definition call_msk (msk: emask): Prop :=
    ∀ fn x y,
      msk _ (subevent _ (Call fn x)) = msk _ (subevent _ (Call fn y))
      ∧ msk _ (subevent _ (Spawn fn x)) = msk _ (subevent _ (Spawn fn y)).
End MASK.
