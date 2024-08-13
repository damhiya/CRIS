Require Import Coqlib.
Require Import sflib.
Require Import ITreelib.
Require Import AList.
Require Import Skeleton.
Require Import STS Behavior.
Require Import Any.
Require Import Program.
Require Import ITree2STS.
Require Import Events.

Set Implicit Arguments.

Section ADD.
  Definition RUN : Type := forall V, (Any.t -> Any.t * V) -> (Any.t -> Any.t * V).

  Definition run_l: RUN := 
    fun V run st =>
      match Any.split st with
      | Some (a, b) => let (a', v) := run a in (Any.pair a' b, v)
      | None => run tt↑
      end.

  Definition run_r: RUN := 
    fun V run st =>
      match Any.split st with
      | Some (a, b) => let (b', v) := run b in (Any.pair a b', v)
      | None => run tt↑
      end.

End ADD.

Module ModSem.
Section MODSEM.

  Record t: Type := mk {
    initial_st : Any.t;
    fnsems : alist gname (Any.t -> itree modE Any.t);
  }.

  Record wf (ms: t): Prop := mk_wf {
    wf_fnsems: NoDup (List.map fst ms.(fnsems));
  }.

  Definition empty: t := {|
    initial_st := tt↑;
    fnsems := [];
  |}.

  Definition init (body: itree modE Any.t) : t := {|
    initial_st := tt↑;
    fnsems := [("CCR_init", fun _ => body)];
  |}.

  Section ADD.
    Definition emb_ : RUN -> (forall T, modE T -> modE T) :=
      fun run_ch T es =>
        match es with
        | inr1 (inl1 (SUpdate run)) => inr1 (inl1 (SUpdate (run_ch T run)))
        | _ => es
        end.

    Definition emb_l := emb_ run_l.
    Definition emb_r := emb_ run_r.

    Definition trans_l '(fn, f): gname * (Any.t -> itree _ Any.t) :=
      (fn, (fun args => translate (emb_ run_l) (f args))).

    Definition trans_r '(fn, f) : gname * (Any.t -> itree _ Any.t) :=
      (fn, (fun args => translate (emb_ run_r) (f args))).

    Definition add_fnsems ms1 ms2 : alist gname (Any.t -> itree _ Any.t) :=
      (List.map trans_l ms1.(fnsems)) ++ (List.map trans_r ms2.(fnsems)).

    Definition add ms1 ms2: t :=
    {|
      initial_st := Any.pair (initial_st ms1) (initial_st ms2); 
      fnsems := add_fnsems ms1 ms2;
    |}.

  End ADD.

  Section COMPILE.
    Variable ms: t.

    Definition prog: callE ~> itree modE :=
      fun _ '(Call fn args) =>
        sem <- (alist_find fn ms.(fnsems))?;;
        rv <- (sem args);;
        Ret rv.  

    Definition initial_itr (P: Prop): itree coreE Any.t :=
      assume P;;; (snd <$> interp_modE prog (prog (Call "CCR_init" ()↑)) (initial_st ms)).

    Definition compile P: semantics:=
      compile_itree (initial_itr P).

    Lemma initial_itr_not_wf P
          (WF: ~ P)
          tr
      :
        Beh.of_program (compile_itree (initial_itr P)) tr.
    Proof.
      eapply Beh.ub_top. pfold. econsr; ss; et. rr. ii; ss.
      unfold initial_itr, assume in *. rewrite bind_bind in STEP.
      eapply step_trigger_take_iff in STEP. des. subst. ss.
    Qed.

    Lemma compile_not_wf P
          (WF: ~ P)
          tr
      :
        Beh.of_program (compile P) tr.
    Proof.
      eapply initial_itr_not_wf; et.
    Qed.
    
  End COMPILE.
End MODSEM.
End ModSem.


Module Mod.
Section MOD.
  Context `{Sk.ld}.

  Record t: Type := mk {
    get_modsem: Sk.t -> ModSem.t;
    sk: Sk.t;
    enclose: ModSem.t := (get_modsem (Sk.canon sk));
  }
  .
  
  Definition wf (md: t): Prop := (<<WF: ModSem.wf md.(enclose)>> /\ <<SK: Sk.wf (md.(sk))>>).

  Definition empty: t := {|
    get_modsem := fun _ => ModSem.empty;
    sk := Sk.unit;
  |}.

  Definition init (body: itree modE Any.t) : t := {|
    get_modsem := fun _ => ModSem.init body;
    sk := Sk.unit;
  |}.

  Definition compile (md: t): semantics :=
    compile_itree (ModSem.initial_itr md.(enclose) (wf md)).

  Definition add (md0 md1: t): t := {|
    get_modsem := fun sk =>
                    ModSem.add (md0.(get_modsem) sk) (md1.(get_modsem) sk);
    sk := Sk.add md0.(sk) md1.(sk);
  |}
  .

  Fixpoint add_list (xs: list t): t :=
    match xs with
    | [] => empty
    | x::[] => x
    | x::l => add x (add_list l)
    end.

End MOD.
End Mod.

Global Existing Instance Sk.gdefs.
Arguments Sk.unit: simpl never.
Arguments Sk.add: simpl never.
Arguments Sk.wf: simpl never.
Coercion Sk.load_skenv: Sk.t >-> SkEnv.t.
Global Opaque Sk.load_skenv.

(* Can this be generalized? *)
Section TRANSL.
  Import ModSem.

  Lemma fst_trans_l : forall x, fst (trans_l x) = fst x.
  Proof. i. destruct x. ss. Qed.
  
  Lemma fst_trans_r : forall x, fst (trans_r x) = fst x.
  Proof. i. destruct x. ss. Qed.
  
  Lemma fun_fst_trans_l : 
    (fun x : string * (Any.t -> itree modE Any.t) => fst (trans_l x)) = (fun x : string * (Any.t -> itree modE Any.t) => fst x).
  Proof.
    extensionality x. rewrite fst_trans_l. et.
  Qed.
  
  Lemma fun_fst_trans_r : 
    (fun x : string * (Any.t -> itree modE Any.t) => fst (trans_r x)) = (fun x : string * (Any.t -> itree modE Any.t) => fst x).
  Proof.
    extensionality x. rewrite fst_trans_r. et.
  Qed.
  
  Lemma fun_fst_trans_l_l :
    (fun x : string * (Any.t -> itree modE Any.t) => fst (trans_l (trans_l x))) = (fun x : string * (Any.t -> itree modE Any.t) => fst x).
  Proof.
    extensionality x. rewrite ! fst_trans_l. et.
  Qed.
  
  Lemma fun_fst_trans_l_r :
    (fun x : string * (Any.t -> itree modE Any.t) => fst (trans_l (trans_r x))) = (fun x : string * (Any.t -> itree modE Any.t) => fst x).
  Proof.
    extensionality x. rewrite fst_trans_l. rewrite fst_trans_r. et.
  Qed.
  
  Lemma fun_fst_trans_r_l:
    (fun x : string * (Any.t -> itree modE Any.t) => fst (trans_r (trans_l x))) = (fun x : string * (Any.t -> itree modE Any.t) => fst x).
  Proof.
    extensionality x. rewrite fst_trans_r. rewrite fst_trans_l. et.
  Qed.
  
  Lemma fun_fst_trans_r_r:
    (fun x : string * (Any.t -> itree modE Any.t) => fst (trans_r (trans_r x))) = (fun x : string * (Any.t -> itree modE Any.t) => fst x).
  Proof.
    extensionality x. rewrite ! fst_trans_r. et.
  Qed.

End TRANSL.


Section LEMMAS.
  (* TODO: Generalize 'emb_' and 'modE' to cover both Mod / HMod. *)
  Import ModSem.


  Lemma translate_emb_bind
    A B
    (run_: RUN)
    (itr: itree modE A) (ktr: A -> itree modE B)
  :
    translate (emb_ run_) (itr >>= ktr) = a <- (translate (emb_ run_) itr);; (translate (emb_ run_) (ktr a))
  .
  Proof. rewrite (bisim_is_eq (translate_bind _ _ _)). et. Qed.

  Lemma translate_emb_tau
    A
    run_
    (itr: itree modE A)
  :
    translate (emb_ run_) (tau;; itr) = tau;; (translate (emb_ run_) itr)
  .
  Proof. rewrite (bisim_is_eq (translate_tau _ _)). et. Qed.

  Lemma translate_emb_ret
      A
      (a: A)
      (run_: RUN)
  :
    translate (emb_ run_) (Ret a) = Ret a
  .
  Proof. rewrite (bisim_is_eq (translate_ret _ _)). et. Qed.

  Lemma translate_emb_callE
      run_ fn args
  :
    translate (emb_ run_) (trigger (Call fn args)) =
    trigger (Call fn args)
  .
  Proof. 
    unfold trigger. 
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss. 
    do 2 f_equal. extensionalities. apply translate_emb_ret. 
  Qed.

  Lemma translate_emb_sE
      T 
      (run_: RUN)
      (run : Any.t -> Any.t * T)
  :
    translate (emb_ run_) (trigger (SUpdate run)) = trigger (SUpdate (run_ T run))
  .
  Proof. 
    unfold trigger. 
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). 
    do 2 f_equal. extensionalities. apply translate_emb_ret. 
  Qed.

  Lemma translate_emb_coreE
      T
      (run_: RUN) 
      (e: coreE T)
    :
      translate (emb_ run_) (trigger e) = trigger e.
  Proof.
    unfold trigger.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    do 2 f_equal.
    extensionalities. rewrite translate_emb_ret. et.
  Qed.

  Lemma translate_emb_triggerUB
    T run_
  
  :
    translate (emb_ run_) (triggerUB: itree _ T) = triggerUB
  .
  Proof. 
    unfold triggerUB. rewrite translate_emb_bind. f_equal.
    { apply translate_emb_coreE. }
    extensionalities. ss.
  Qed.

  Lemma translate_emb_triggerNB
    T run_
  :
    translate (emb_ run_) (triggerNB: itree _ T) = triggerNB
  .
  Proof.
    unfold triggerNB. rewrite translate_emb_bind. f_equal. 
    { apply translate_emb_coreE. }
    extensionalities. ss.
  Qed.
  
  Lemma translate_emb_unwrapU
    R run_ (r: option R)
  :
    translate (emb_ run_) (unwrapU r) = unwrapU r
  .
  Proof.
    unfold unwrapU. destruct r.
    - apply translate_emb_ret.
    - apply translate_emb_triggerUB.
  Qed.

  Lemma translate_emb_unwrapN
    R run_ (r: option R)
  :
    translate (emb_ run_) (unwrapN r) = unwrapN r
  .
  Proof.
    unfold unwrapN. destruct r.
    - apply translate_emb_ret.
    - apply translate_emb_triggerNB.
  Qed.

  Lemma translate_emb_assume
    run_ P
  :
    translate (emb_ run_) (assume P) = assume P
  .
  Proof.
    unfold assume. rewrite translate_emb_bind.
    rewrite translate_emb_coreE. f_equal.
    extensionalities.
    rewrite translate_emb_ret. et.
  Qed.

  Lemma translate_emb_guarantee
    run_ P
  :
    translate (emb_ run_) (guarantee P) = guarantee P
  .
  Proof.
    unfold guarantee. rewrite translate_emb_bind.
    rewrite translate_emb_coreE. f_equal.
    extensionalities.
    rewrite translate_emb_ret. et.
  Qed.

  Lemma translate_emb_ext
    T run_ (itr0 itr1: itree _ T)
    (EQ: itr0 = itr1)
  :
    translate (emb_ run_) itr0 = translate (emb_ run_) itr1
  .
  Proof. subst. refl. Qed.
  

End LEMMAS.
