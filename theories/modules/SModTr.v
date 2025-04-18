Require Import Common.
Require Import HMod FSpec.

Set Implicit Arguments.

Arguments precond : simpl never.
Arguments postcond : simpl never.

Module SModTr.
Section HOARE.

  Context `{Σ: GRA}.

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

  Definition HoareSpawn (fsp: fspec) (fn: string) (varg: Any.t) : itree hmodE nat :=
    x <- trigger (Choose fsp.(meta));; 
    arg <- trigger (Choose Any.t);;
    tid <- trigger (Spawn fn arg);;
    trigger (Guarantee (fsp.(precond) x varg arg));;;
    trigger (Yield tid);;;
    Ret tid.
  
  Definition handle_schE_hmodE : schE ~> itree hmodE :=
    λ _ e,
      match e in schE T return itree hmodE T with
      | Spawn fn arg =>
          fsp <- (sp fn)!;;
          HoareSpawn fsp fn arg
      | Yield tid =>
          trigger (Yield tid)
      end.
  
  Definition handle_callE_hmodE: callE ~> itree hmodE :=
    λ _ '(Call fn varg), 
        fsp <- (sp fn)!;;
        HoareCall fsp fn varg.

  Definition trans R (it : itree hmodE R) : itree hmodE R :=
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

      vret <- trans (body varg);;

      ret <- trigger (Choose Any.t);;
      trigger (Guarantee (Q x vret ret));;; (*** postcondition ***)

      Ret ret.
  
  Definition trans_ktree (sb: fspecbody): (Any.t → itree hmodE Any.t) :=
    let fs: fspec := sb.(fsb_fspec) in
    HoareFun fs.(precond) fs.(postcond) sb.(fsb_body).

End HOARE.
End SModTr.

Notation "↧ it" := (SModTr.trans _ it) (at level 59, only printing).

Module SRed.
Section RED.

  Context `{Σ : GRA}.

  Lemma bind
        (R S: Type)
        sp
        (s : itree hmodE R) (k : R → itree hmodE S)
    :
      SModTr.trans sp (s >>= k)
      =
      st <- SModTr.trans sp s;; SModTr.trans sp (k st).
  Proof using.
    unfold SModTr.trans in *. grind.
  Qed.

  Lemma tau
        (U : Type)
        (t : itree _ U)
        sp
    :
      SModTr.trans sp (tau;; t)
      =
      tau;; (SModTr.trans sp t).
  Proof using.
    unfold SModTr.trans in *. grind.
  Qed.

  Lemma ret
        (U: Type)
        (t: U)
        sp
    :
      SModTr.trans sp (Ret t)
      =
      Ret t.
  Proof using.
    unfold SModTr.trans in *. grind.
  Qed.

  Lemma vis_ag {X R} sp (e : agE X) (ktr : X -> itree hmodE R) :
    SModTr.trans sp (vis e ktr) = vis e (fun x => tau;; SModTr.trans sp (ktr x)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma vis_sch {X R} sp (e : schE X) (ktr : X -> itree hmodE R) :
    SModTr.trans sp (vis e ktr) = x <- SModTr.handle_schE_hmodE sp e;; tau;; SModTr.trans sp (ktr x).
  Proof using.
    eapply bisim_is_eq. unfold SModTr.trans. rewrite interp_vis. reflexivity.
  Qed.

  Lemma vis_call {X R} sp (e : callE X) (ktr : X -> itree hmodE R) :
    SModTr.trans sp (vis e ktr) = x <- SModTr.handle_callE_hmodE sp e;; tau;; SModTr.trans sp (ktr x).
  Proof using.
    eapply bisim_is_eq. unfold SModTr.trans. rewrite interp_vis. reflexivity.
  Qed.

  Lemma vis_pg {X R} sp (e : pgE X) (ktr : X -> itree hmodE R) :
    SModTr.trans sp (vis e ktr) = vis e (fun x => tau;; SModTr.trans sp (ktr x)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma vis_core {X R} sp (e : coreE X) (ktr : X -> itree hmodE R) :
    SModTr.trans sp (vis e ktr) = vis e (fun x => tau;; SModTr.trans sp (ktr x)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma assumeK {R} sp P (itr : itree hmodE R) :
    SModTr.trans sp (assumeK P itr) = assumeK P (tau;; SModTr.trans sp itr).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma guaranteeK {R} sp P (itr : itree hmodE R) :
    SModTr.trans sp (guaranteeK P itr) = guaranteeK P (tau;; SModTr.trans sp itr).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma unwrapUK {X R} sp x (ktr : X -> itree hmodE R) :
    SModTr.trans sp (unwrapUK x ktr) = unwrapUK x (fun x => SModTr.trans sp (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma unwrapNK {X R} sp x (ktr : X -> itree hmodE R) :
    SModTr.trans sp (unwrapNK x ktr) = unwrapNK x (fun x => SModTr.trans sp (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma sch
        (R: Type)
        (i: schE R)
        sp
    :
      SModTr.trans sp (trigger i)
      =
      r <- SModTr.handle_schE_hmodE sp i;; tau;; Ret r.
  Proof using.
    unfold SModTr.trans in *. rewrite interp_trigger. grind.
  Qed.
  
  Lemma call
        (R: Type)
        (i: callE R)
        sp
    :
      SModTr.trans sp (trigger i)
      =
      r <- SModTr.handle_callE_hmodE sp i;; tau;; Ret r.
  Proof using.
    unfold SModTr.trans in *. rewrite interp_trigger. grind.
  Qed.

  Lemma pg
        (R: Type)
        (i: pgE R)
        sp
    :
      SModTr.trans sp (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof using.
    unfold SModTr.trans. rewrite interp_trigger. grind.
  Qed.

  Lemma core
        (R: Type)
        (i: coreE R)
        sp
    :
      SModTr.trans sp (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof using.
    unfold SModTr.trans. rewrite interp_trigger. grind.
  Qed.

  Lemma ag {A} (e: agE A)
        sp
    :
      SModTr.trans sp (trigger e)
      =
      x <- trigger e ;; tau;; Ret x.
  Proof using.
    unfold SModTr.trans. rewrite interp_trigger. grind.
  Qed.
  
  Lemma unwrapU 
        (R: Type)
        (i: option R)
        sp
    :
      SModTr.trans sp (@unwrapU hmodE _ _ i)
      =
      r <- (unwrapU i);; Ret r.
  Proof using.
    unfold SModTr.trans, unwrapU in *. des_ifs; grind.
    unfold triggerUB in *. rewrite unfold_interp. grind.
  Qed.

  Lemma unwrapN
        (R: Type)
        (i: option R)
        sp
    :
      SModTr.trans sp (@unwrapN hmodE _ _ i)
      =
      r <- (unwrapN i);; Ret r.
  Proof using.
    unfold SModTr.trans, unwrapN in *. des_ifs; grind.
    unfold triggerNB in *. rewrite unfold_interp. grind.
  Qed.
  
  Lemma asm
        sp P
    : 
      SModTr.trans sp (assume P)
      =
      r <- assume P;; tau;; Ret r.
  Proof using.
    unfold assume. rewrite bind. rewrite core. grind. rewrite ret. refl.
  Qed. 

  Lemma guar
        sp P
    : 
      SModTr.trans sp (guarantee P)
      =
      r <- guarantee P;; tau;; Ret r.
  Proof using.
    unfold guarantee. rewrite bind. rewrite core. grind. rewrite ret. refl.
  Qed.

End RED. End SRed.
