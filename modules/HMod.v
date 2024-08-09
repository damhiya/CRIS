Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Export AList.
Require Import Skeleton.
Require Import Any.
Require Import Mod.
Require Import Translate.
Require Import PCM IPM.
Require Import Red IRed.

Set Implicit Arguments.

Module HModSem.
Section HMODSEM.
  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    fnsems : alist gname (Any.t -> itree hmodE Any.t);
    initial_st : Any.t;
    initial_cond: iProp;
  }.

  Definition transl (tr: (Any.t -> itree hmodE Any.t) -> Any.t -> itree modE Any.t) (ms: t): ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, bd) => (fn, tr bd)) ms.(fnsems);
    ModSem.initial_st := r <- cond_to_st ms.(initial_cond);;  Ret (Any.pair ms.(initial_st) r↑)
  |}.

  Definition to_mod (ms: t): ModSem.t := transl (interp_hp_fun) ms.
  (* TODO: define other compilations which are required to prove WET. *)


  (**** Linking ****)

  (* TODO: 
    Can 'modE' and 'hmodE' share the 'translate' lemmas? 
    (Definition of emb_ required to prove all lemmas)
  *)
  Definition emb_ : RUN -> (forall T, hmodE T -> hmodE T) :=
    fun run_ch T es =>
      match es with
      | inr1 (inr1 (inl1 (SUpdate run))) => inr1 (inr1 (inl1 (SUpdate (run_ch T run))))
      | _ => es
      end.

  Definition emb_l := emb_ run_l.
  Definition emb_r := emb_ run_r.

  Definition trans_l '(fn, f): gname * (Any.t -> itree _ Any.t) :=
    (fn, (fun args => translate (emb_ run_l) (f args))).

  Definition trans_r '(fn, f) : gname * (Any.t -> itree _ Any.t) :=
    (fn, (fun args => translate (emb_ run_r) (f args))).
  
  Definition add_fnsems ms1 ms2: alist gname (Any.t -> itree _ Any.t) :=
    (List.map trans_l ms1.(fnsems)) ++ (List.map trans_r ms2.(fnsems)).
  
  Definition add ms1 ms2: t := {|
    fnsems := add_fnsems ms1 ms2;
    initial_st := Any.pair (initial_st ms1) (initial_st ms2);
    initial_cond := (initial_cond ms1) ∗ (initial_cond ms2);
  |}.

End HMODSEM.

Section RED.
  Context `{Σ: GRA.t}.

  Lemma translate_emb_bind
    A B
    run_
    (itr: itree hmodE A) (ktr: A -> itree hmodE B)
  :
    translate (HModSem.emb_ run_) (itr >>= ktr) = a <- (translate (HModSem.emb_ run_) itr);; (translate (HModSem.emb_ run_) (ktr a))
  .
  Proof. rewrite (bisim_is_eq (translate_bind _ _ _)). et. Qed.

  Lemma translate_emb_tau
    A
    run_
    (itr: itree hmodE A)
  :
    translate (HModSem.emb_ run_) (tau;; itr) = tau;; (translate (HModSem.emb_ run_) itr)
  .
  Proof. rewrite (bisim_is_eq (translate_tau _ _)). et. Qed.

  Lemma translate_emb_ret
      A (a: A) run_
  :
    translate (HModSem.emb_ run_) (Ret a) = Ret a
  .
  Proof. rewrite (bisim_is_eq (translate_ret _ _)). et. Qed.

  Lemma translate_emb_callE
      run_ fn args
  :
    translate (HModSem.emb_ run_) (trigger (Call fn args)) =
    trigger (Call fn args)
  .
  Proof. 
    unfold trigger. 
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss. 
    do 2 f_equal. extensionalities. apply translate_emb_ret. 
  Qed.

  Lemma translate_emb_sE
      T run_
      (run : Any.t -> Any.t * T)
  :
    translate (HModSem.emb_ run_) (trigger (SUpdate run)) = trigger (SUpdate (run_ T run))
  .
  Proof. 
    unfold trigger. 
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). 
    do 2 f_equal. extensionalities. apply translate_emb_ret. 
  Qed.

  Lemma translate_emb_coreE
      T run_ 
      (e: coreE T)
    :
      translate (HModSem.emb_ run_) (trigger e) = trigger e.
  Proof.
    unfold trigger.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    do 2 f_equal.
    extensionalities. rewrite translate_emb_ret. et.
  Qed.

  Lemma translate_emb_triggerUB
    T run_
  :
    translate (HModSem.emb_ run_) (triggerUB: itree _ T) = triggerUB
  .
  Proof. 
    unfold triggerUB. rewrite translate_emb_bind. f_equal.
    { apply translate_emb_coreE. }
    extensionalities. ss.
  Qed.

  Lemma translate_emb_triggerNB
    T run_
  :
    translate (HModSem.emb_ run_) (triggerNB: itree _ T) = triggerNB
  .
  Proof.
    unfold triggerNB. rewrite translate_emb_bind. f_equal. 
    { apply translate_emb_coreE. }
    extensionalities. ss.
  Qed.
  
  Lemma translate_emb_unwrapU
    R run_ (r: option R)
  :
    translate (HModSem.emb_ run_) (unwrapU r) = unwrapU r
  .
  Proof.
    unfold unwrapU. destruct r.
    - apply translate_emb_ret.
    - apply translate_emb_triggerUB.
  Qed.

  Lemma translate_emb_unwrapN
    R run_ (r: option R)
  :
    translate (HModSem.emb_ run_) (unwrapN r) = unwrapN r
  .
  Proof.
    unfold unwrapN. destruct r.
    - apply translate_emb_ret.
    - apply translate_emb_triggerNB.
  Qed.

  Lemma translate_emb_assume
    run_ P
  :
    translate (HModSem.emb_ run_) (trigger (Assume P)) = trigger (Assume P)
  .
  Proof.
    unfold trigger.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    do 2 f_equal.
    extensionalities. rewrite translate_emb_ret. et.
  Qed.

  Lemma translate_emb_guarantee
    run_ P
  :
    translate (HModSem.emb_ run_) (trigger (Guarantee P)) = trigger (Guarantee P)
  .
  Proof.
    unfold trigger.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    do 2 f_equal.
    extensionalities. rewrite translate_emb_ret. et.
  Qed.

  Lemma translate_emb_asm
    run_ P
  :
    translate (HModSem.emb_ run_) (assume P) = assume P
  .
  Proof.
    unfold assume, trigger.
    rewrite translate_emb_bind.
    rewrite translate_emb_ret.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    do 3 f_equal.
    extensionalities. rewrite translate_emb_ret. et.
  Qed.

  Lemma translate_emb_guar
    run_ P
  :
    translate (HModSem.emb_ run_) (guarantee P) = guarantee P
  .
  Proof.
    unfold guarantee, trigger.
    rewrite translate_emb_bind.
    rewrite translate_emb_ret.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    do 3 f_equal.
    extensionalities. rewrite translate_emb_ret. et.
  Qed.
  
  Lemma translate_emb_ext
    T run_ (itr0 itr1: itree _ T)
    (EQ: itr0 = itr1)
  :
    translate (HModSem.emb_ run_) itr0 = translate (HModSem.emb_ run_) itr1
  .
  Proof. subst. refl. Qed.
  


End RED.

End HModSem.

Module HMod.
Section HMOD.
  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    get_modsem: Sk.t -> HModSem.t;
    sk: Sk.t;
  }.

  Definition transl (tr: Sk.t -> (Any.t -> itree hmodE Any.t) -> Any.t -> itree modE Any.t) (md: t): Mod.t := {|
    Mod.get_modsem := fun sk => HModSem.transl (tr sk) (md.(get_modsem) sk);
    Mod.sk := md.(sk);
  |}. 

  Definition to_mod (md: t): Mod.t := transl (fun _ => interp_hp_fun) md.

  Definition add (md0 md1: t): t := {|
    get_modsem := fun sk => HModSem.add (md0.(get_modsem) sk) (md1.(get_modsem) sk);
    sk := Sk.add md0.(sk) md1.(sk);
  |}.
    
End HMOD.
End HMod.

Section HModRefl.
  Context `{Σ: GRA.t}.

  Lemma unfold_iter_eq (E : Type -> Type) (A B : Type) (f : A -> itree E (A + B)) (x : A)
    :
    ITree.iter f x = lr <- f x;;
                     match lr with
                     | inl l => tau;; ITree.iter f l
                     | inr r => Ret r
                     end.
  Proof.
    eapply bisim_is_eq. eapply unfold_iter.
  Qed.

  Lemma combine_quant A (B: A -> Type) (P: forall a (b: B a), Prop)
      (PR: forall (ab: sigT B), P (projT1 ab) (projT2 ab)):
    forall a b, P a b.
  Proof. i. eapply (PR (existT a b)). Qed.

  Definition IstEq: Any.t -> Any.t -> iProp :=
    fun st_src st_tgt => ⌜ st_src = st_tgt ⌝%I.

  Definition IstProd (IstL IstR : Any.t -> Any.t -> iProp) : Any.t -> Any.t -> iProp :=
    fun st_src st_tgt => (∃ st_srcL st_tgtL st_srcR st_tgtR,
      ⌜st_src = Any.pair st_srcL st_srcR /\ st_tgt = Any.pair st_tgtL st_tgtR⌝ ∗
      IstL st_srcL st_tgtL ∗ IstR st_srcR st_tgtR)%I.

  Lemma ist_eq_run_r A (run: _ -> (_ * A)) Ist st_src st_tgt:
    IstProd Ist IstEq st_src st_tgt -∗
      (⌜(run_r run st_src).2 = (run_r run st_tgt).2⌝ ∗
      IstProd Ist IstEq (run_r run st_src).1 (run_r run st_tgt).1).
  Proof.
    iIntros "IST". iDestruct "IST" as (? ? ? ?) "(% & IST & %)". des; subst.
    unfold run_r. rewrite !Any.pair_split. destruct (run st_tgtR).
    iSplitR; eauto.
    iExists _,_,_,_. eauto.
  Qed.
  
End HModRefl.



Section AUX.
  Context `{Σ: GRA.t}.
  Global Program Instance translate_emb_rdb: red_database (mk_box (@translate)) :=
    mk_rdb
    0
    (mk_box HModSem.translate_emb_bind)
    (mk_box HModSem.translate_emb_tau)
    (mk_box HModSem.translate_emb_ret)
    (mk_box HModSem.translate_emb_sE)
    (mk_box HModSem.translate_emb_sE)
    (mk_box HModSem.translate_emb_callE)
    (mk_box HModSem.translate_emb_coreE)
    (mk_box HModSem.translate_emb_triggerUB)
    (mk_box HModSem.translate_emb_triggerNB)
    (mk_box HModSem.translate_emb_unwrapU)
    (mk_box HModSem.translate_emb_unwrapN)
    (mk_box HModSem.translate_emb_assume)
    (mk_box HModSem.translate_emb_guarantee)
    (mk_box HModSem.translate_emb_ext).

End AUX.
