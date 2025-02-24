Require Import Common.
Require Import HMod.

Set Implicit Arguments.

Section FSPEC.
  Context {Σ : GRA}.
  Notation iProp := (iProp Σ).

  Record fspec : Type := mk_fspec {
    meta : Type;
    (*** meta-variable → virtual arg → physical arg → iProp ***)
    precond : meta → Any.t → Any.t → iProp; 
    (*** meta-variable → virtual ret → physical ret → iProp ***)
    postcond : meta → Any.t → Any.t → iProp; 
  }.

  Record fspecbody : Type := mk_specbody {
    fsb_fspec :> fspec;
    fsb_body : Any.t → itree hmodE Any.t;
  }.

  Definition fspec_trivial : fspec :=
    mk_fspec (meta:=unit)
             (λ _ argh argl, (⌜argh = argl⌝ : iProp)%I)
             (λ _ reth retl, (⌜reth = retl⌝ : iProp)%I).

  Definition fbody_trivial : Any.t → itree hmodE Any.t :=
    λ _, trigger (Choose _).

  Definition fspec_virtual (M VA VR : Type)
      (precond: M → VA → Any.t → iProp)
      (postcond: M → VR → Any.t → iProp) :=
    mk_fspec (meta:=M)
      (λ x varg arg, (∃ va: VA, ⌜varg = va↑⌝ ∗ precond x va arg)%I)
      (λ x vret ret, (∃ vr: VR, ⌜vret = vr↑⌝ ∗ postcond x vr ret)%I).

  Definition fspec_simple {X : Type} (DPQ: X → (Any.t → iProp) * (Any.t → iProp)) : fspec :=
    mk_fspec (λ x y a, (((fst ∘ DPQ) x a: iProp) ∗ ⌜y = a⌝)%I)
             (λ x z a, (((snd ∘ DPQ) x a: iProp) ∗ ⌜z = a⌝)%I).

  Definition fspec_simple_tid {X : Type}
      (DPQ: X → (Any.t → iProp) * (Any.t → iProp)) : fspec :=
    mk_fspec (λ x y a, (((fst ∘ DPQ) x a: iProp) ∗ ⌜y = a⌝)%I)
             (λ x z a, (((snd ∘ DPQ) x a: iProp) ∗ ⌜z = a⌝)%I).

  Definition fspec_false : fspec := {|
    meta := Empty_set;
    precond := λ _ _ _, False%I;
    postcond := λ _ _ _, False%I; 
  |}.
  
  Definition app_fspec (fspecs : list fspec) : fspec := {|
    meta := { i : nat & (nth i fspecs fspec_false).(meta) };
    precond := λ '(existT i meta_i), (nth i fspecs fspec_false).(precond) meta_i;
    postcond := λ '(existT i meta_i), (nth i fspecs fspec_false).(postcond) meta_i 
  |}.
End FSPEC.

Arguments precond : simpl never.
Arguments postcond : simpl never.

Section HOARE.

  Context `{Σ: GRA}.

  Definition ginv_emp : iProp Σ := emp%I.

  Variable ginv : iProp Σ.
  Variable stb: string → option fspec.

  Definition HoareCall (fsp: fspec): string → Any.t → (itree hmodE) Any.t 
    := 
    λ fn varg,
      x <- trigger (Choose fsp.(meta));; 

      (*** precondition ***)
      arg <- trigger (Choose Any.t);;
      trigger (Guarantee (fsp.(precond) x varg arg));;;

      (*** call ***)
      ret <- trigger (Call fn arg);;

      (*** postcondition ***)
      vret <- trigger (Take Any.t);;
      trigger (Assume (fsp.(postcond) x vret ret));;;

      Ret vret.

  Definition HoareYield (tid: nat) : itree hmodE unit :=
    trigger (Guarantee ginv);;;
    trigger (Yield tid);;;
    trigger (Assume ginv).

  Definition HoareSpawn (fsp: fspec) (fn: string) (varg: Any.t) : itree hmodE nat :=
    x <- trigger (Choose fsp.(meta));; 
    arg <- trigger (Choose Any.t);;
    tid <- trigger (Spawn fn arg);;
    trigger (Guarantee (ginv ==∗ fsp.(precond) x varg arg));;;
    HoareYield tid;;;
    Ret tid.
  
  Definition handle_schE_hmodE : schE ~> itree hmodE :=
    λ _ e,
      match e in schE T return itree hmodE T with
      | Spawn fn arg =>
          fsp <- (stb fn)!;;
          HoareSpawn fsp fn arg
      | Yield tid =>
          HoareYield tid
      end.
  
  Definition handle_callE_hmodE: callE ~> itree hmodE :=
    λ _ '(Call fn varg), 
        fsp <- (stb fn)!;;
        HoareCall fsp fn varg.

  Definition interp_smod R (it : itree hmodE R) : itree hmodE R :=
    interp (case_ (bif:=sum1) trivial_Handler
           (case_ (bif:=sum1) handle_schE_hmodE
           (case_ (bif:=sum1) handle_callE_hmodE
            trivial_Handler))) it.

  Definition HoareFun {X: Type}
      (P: X → Any.t → Any.t → iProp Σ)
      (Q: X → Any.t → Any.t → iProp Σ)
      (body: Any.t → itree hmodE Any.t): Any.t → itree hmodE Any.t :=
    λ arg,
      x <- trigger (Take X);;

      varg <- trigger (Take _);;
      trigger (Assume (P x varg arg));;; (*** precondition ***)

      vret <- interp_smod (body varg);;

      ret <- trigger (Choose Any.t);;
      trigger (Guarantee (Q x vret ret));;; (*** postcondition ***)

      Ret ret.
  
  Definition interp_sb_hp (sb: fspecbody): (Any.t → itree hmodE Any.t) :=
    let fs: fspec := sb.(fsb_fspec) in
    HoareFun fs.(precond) fs.(postcond) sb.(fsb_body).

End HOARE.

Notation "↧ it" := (interp_smod _ _ it) (at level 59, only printing).

Module SModRed.
Section RED.

  Context `{Σ : GRA}.

  Lemma interp_bind
        (R S: Type)
        ginv stb
        (s : itree hmodE R) (k : R → itree hmodE S)
    :
      interp_smod ginv stb (s >>= k)
      =
      st <- interp_smod ginv stb s;; interp_smod ginv stb (k st).
  Proof.
    unfold interp_smod in *. grind.
  Qed.

  Lemma interp_tau
        (U : Type)
        (t : itree _ U)
        ginv stb
    :
      interp_smod ginv stb (tau;; t)
      =
      tau;; (interp_smod ginv stb t).
  Proof.
    unfold interp_smod in *. grind.
  Qed.

  Lemma interp_ret
        (U: Type)
        (t: U)
        ginv stb
    :
      interp_smod ginv stb (Ret t)
      =
      Ret t.
  Proof.
    unfold interp_smod in *. grind.
  Qed.

  Lemma interp_vis_ag {X R} ginv stb (e : agE X) (ktr : X -> itree hmodE R) :
    interp_smod ginv stb (vis e ktr) = vis e (fun x => tau;; interp_smod ginv stb (ktr x)).
  Proof.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma interp_vis_sch {X R} ginv stb (e : schE X) (ktr : X -> itree hmodE R) :
    interp_smod ginv stb (vis e ktr) = x <- handle_schE_hmodE ginv stb e;; tau;; interp_smod ginv stb (ktr x).
  Proof.
    eapply bisim_is_eq. unfold interp_smod. rewrite interp_vis. reflexivity.
  Qed.

  Lemma interp_vis_call {X R} ginv stb (e : callE X) (ktr : X -> itree hmodE R) :
    interp_smod ginv stb (vis e ktr) = x <- handle_callE_hmodE stb e;; tau;; interp_smod ginv stb (ktr x).
  Proof.
    eapply bisim_is_eq. unfold interp_smod. rewrite interp_vis. reflexivity.
  Qed.

  Lemma interp_vis_pg {X R} ginv stb (e : pgE X) (ktr : X -> itree hmodE R) :
    interp_smod ginv stb (vis e ktr) = vis e (fun x => tau;; interp_smod ginv stb (ktr x)).
  Proof.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma interp_vis_core {X R} ginv stb (e : coreE X) (ktr : X -> itree hmodE R) :
    interp_smod ginv stb (vis e ktr) = vis e (fun x => tau;; interp_smod ginv stb (ktr x)).
  Proof.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma interp_assumeK {R} ginv stb P (itr : itree hmodE R) :
    interp_smod ginv stb (assumeK P itr) = assumeK P (tau;; interp_smod ginv stb itr).
  Proof.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma interp_guaranteeK {R} ginv stb P (itr : itree hmodE R) :
    interp_smod ginv stb (guaranteeK P itr) = guaranteeK P (tau;; interp_smod ginv stb itr).
  Proof.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma interp_unwrapUK {X R} ginv stb x (ktr : X -> itree hmodE R) :
    interp_smod ginv stb (unwrapUK x ktr) = unwrapUK x (fun x => interp_smod ginv stb (ktr x)).
  Proof.
    destruct x; ss.
    eapply observe_eta; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma interp_unwrapNK {X R} ginv stb x (ktr : X -> itree hmodE R) :
    interp_smod ginv stb (unwrapNK x ktr) = unwrapNK x (fun x => interp_smod ginv stb (ktr x)).
  Proof.
    destruct x; ss.
    eapply observe_eta; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma interp_sch
        (R: Type)
        (i: schE R)
        ginv stb
    :
      interp_smod ginv stb (trigger i)
      =
      r <- handle_schE_hmodE ginv stb i;; tau;; Ret r.
  Proof.
    unfold interp_smod in *. rewrite interp_trigger. grind.
  Qed.
  
  Lemma interp_call
        (R: Type)
        (i: callE R)
        ginv stb
    :
      interp_smod ginv stb (trigger i)
      =
      r <- handle_callE_hmodE stb i;; tau;; Ret r.
  Proof.
    unfold interp_smod in *. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_pg
        (R: Type)
        (i: pgE R)
        ginv stb
    :
      interp_smod ginv stb (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof.
    unfold interp_smod. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_core
        (R: Type)
        (i: coreE R)
        ginv stb
    :
      interp_smod ginv stb (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof.
    unfold interp_smod. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_ag {A} (e: agE A)
        ginv stb
    :
      interp_smod ginv stb (trigger e)
      =
      x <- trigger e ;; tau;; Ret x.
  Proof.
    unfold interp_smod. rewrite interp_trigger. grind.
  Qed.
  
  Lemma interp_unwrapU 
        (R: Type)
        (i: option R)
        ginv stb
    :
      interp_smod ginv stb (@unwrapU hmodE _ _ i)
      =
      r <- (unwrapU i);; Ret r.
  Proof.
    unfold interp_smod, unwrapU in *. des_ifs; grind.
    unfold triggerUB in *. rewrite unfold_interp. grind.
  Qed.

  Lemma interp_unwrapN
        (R: Type)
        (i: option R)
        ginv stb
    :
      interp_smod ginv stb (@unwrapN hmodE _ _ i)
      =
      r <- (unwrapN i);; Ret r.
  Proof.
    unfold interp_smod, unwrapN in *. des_ifs; grind.
    unfold triggerNB in *. rewrite unfold_interp. grind.
  Qed.
  
  Lemma interp_asm
        ginv stb P
    : 
      interp_smod ginv stb (assume P)
      =
      r <- assume P;; tau;; Ret r.
  Proof.
    unfold assume. rewrite interp_bind. rewrite interp_core. grind. rewrite interp_ret. refl.
  Qed. 

  Lemma interp_guar
        ginv stb P
    : 
      interp_smod ginv stb (guarantee P)
      =
      r <- guarantee P;; tau;; Ret r.
  Proof.
    unfold guarantee. rewrite interp_bind. rewrite interp_core. grind. rewrite interp_ret. refl.
  Qed.

End RED. End SModRed.
