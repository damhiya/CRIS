Require Import Common.
Require Import HMod FSpec.

Set Implicit Arguments.

Arguments precond : simpl never.
Arguments postcond : simpl never.

Section HOARE.

  Context `{Σ: GRA}.

  Variable ginv : iProp Σ.
  Variable sp: string → option fspec.

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
          fsp <- (sp fn)!;;
          HoareSpawn fsp fn arg
      | Yield tid =>
          HoareYield tid
      end.
  
  Definition handle_callE_hmodE: callE ~> itree hmodE :=
    λ _ '(Call fn varg), 
        fsp <- (sp fn)!;;
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

Module SRed.
Section RED.

  Context `{Σ : GRA}.

  Lemma bind
        (R S: Type)
        ginv sp
        (s : itree hmodE R) (k : R → itree hmodE S)
    :
      interp_smod ginv sp (s >>= k)
      =
      st <- interp_smod ginv sp s;; interp_smod ginv sp (k st).
  Proof using.
    unfold interp_smod in *. grind.
  Qed.

  Lemma tau
        (U : Type)
        (t : itree _ U)
        ginv sp
    :
      interp_smod ginv sp (tau;; t)
      =
      tau;; (interp_smod ginv sp t).
  Proof using.
    unfold interp_smod in *. grind.
  Qed.

  Lemma ret
        (U: Type)
        (t: U)
        ginv sp
    :
      interp_smod ginv sp (Ret t)
      =
      Ret t.
  Proof using.
    unfold interp_smod in *. grind.
  Qed.

  Lemma vis_ag {X R} ginv sp (e : agE X) (ktr : X -> itree hmodE R) :
    interp_smod ginv sp (vis e ktr) = vis e (fun x => tau;; interp_smod ginv sp (ktr x)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma vis_sch {X R} ginv sp (e : schE X) (ktr : X -> itree hmodE R) :
    interp_smod ginv sp (vis e ktr) = x <- handle_schE_hmodE ginv sp e;; tau;; interp_smod ginv sp (ktr x).
  Proof using.
    eapply bisim_is_eq. unfold interp_smod. rewrite interp_vis. reflexivity.
  Qed.

  Lemma vis_call {X R} ginv sp (e : callE X) (ktr : X -> itree hmodE R) :
    interp_smod ginv sp (vis e ktr) = x <- handle_callE_hmodE sp e;; tau;; interp_smod ginv sp (ktr x).
  Proof using.
    eapply bisim_is_eq. unfold interp_smod. rewrite interp_vis. reflexivity.
  Qed.

  Lemma vis_pg {X R} ginv sp (e : pgE X) (ktr : X -> itree hmodE R) :
    interp_smod ginv sp (vis e ktr) = vis e (fun x => tau;; interp_smod ginv sp (ktr x)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma vis_core {X R} ginv sp (e : coreE X) (ktr : X -> itree hmodE R) :
    interp_smod ginv sp (vis e ktr) = vis e (fun x => tau;; interp_smod ginv sp (ktr x)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma assumeK {R} ginv sp P (itr : itree hmodE R) :
    interp_smod ginv sp (assumeK P itr) = assumeK P (tau;; interp_smod ginv sp itr).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma guaranteeK {R} ginv sp P (itr : itree hmodE R) :
    interp_smod ginv sp (guaranteeK P itr) = guaranteeK P (tau;; interp_smod ginv sp itr).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma unwrapUK {X R} ginv sp x (ktr : X -> itree hmodE R) :
    interp_smod ginv sp (unwrapUK x ktr) = unwrapUK x (fun x => interp_smod ginv sp (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma unwrapNK {X R} ginv sp x (ktr : X -> itree hmodE R) :
    interp_smod ginv sp (unwrapNK x ktr) = unwrapNK x (fun x => interp_smod ginv sp (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma sch
        (R: Type)
        (i: schE R)
        ginv sp
    :
      interp_smod ginv sp (trigger i)
      =
      r <- handle_schE_hmodE ginv sp i;; tau;; Ret r.
  Proof using.
    unfold interp_smod in *. rewrite interp_trigger. grind.
  Qed.
  
  Lemma call
        (R: Type)
        (i: callE R)
        ginv sp
    :
      interp_smod ginv sp (trigger i)
      =
      r <- handle_callE_hmodE sp i;; tau;; Ret r.
  Proof using.
    unfold interp_smod in *. rewrite interp_trigger. grind.
  Qed.

  Lemma pg
        (R: Type)
        (i: pgE R)
        ginv sp
    :
      interp_smod ginv sp (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof using.
    unfold interp_smod. rewrite interp_trigger. grind.
  Qed.

  Lemma core
        (R: Type)
        (i: coreE R)
        ginv sp
    :
      interp_smod ginv sp (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof using.
    unfold interp_smod. rewrite interp_trigger. grind.
  Qed.

  Lemma ag {A} (e: agE A)
        ginv sp
    :
      interp_smod ginv sp (trigger e)
      =
      x <- trigger e ;; tau;; Ret x.
  Proof using.
    unfold interp_smod. rewrite interp_trigger. grind.
  Qed.
  
  Lemma unwrapU 
        (R: Type)
        (i: option R)
        ginv sp
    :
      interp_smod ginv sp (@unwrapU hmodE _ _ i)
      =
      r <- (unwrapU i);; Ret r.
  Proof using.
    unfold interp_smod, unwrapU in *. des_ifs; grind.
    unfold triggerUB in *. rewrite unfold_interp. grind.
  Qed.

  Lemma unwrapN
        (R: Type)
        (i: option R)
        ginv sp
    :
      interp_smod ginv sp (@unwrapN hmodE _ _ i)
      =
      r <- (unwrapN i);; Ret r.
  Proof using.
    unfold interp_smod, unwrapN in *. des_ifs; grind.
    unfold triggerNB in *. rewrite unfold_interp. grind.
  Qed.
  
  Lemma asm
        ginv sp P
    : 
      interp_smod ginv sp (assume P)
      =
      r <- assume P;; tau;; Ret r.
  Proof using.
    unfold assume. rewrite bind. rewrite core. grind. rewrite ret. refl.
  Qed. 

  Lemma guar
        ginv sp P
    : 
      interp_smod ginv sp (guarantee P)
      =
      r <- guarantee P;; tau;; Ret r.
  Proof using.
    unfold guarantee. rewrite bind. rewrite core. grind. rewrite ret. refl.
  Qed.

End RED. End SRed.
