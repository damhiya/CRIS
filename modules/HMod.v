Require Import Coqlib AList.
Require Import sflib.
Require Import ITreelib.
Require Import Any.
Require Import EventsRed Events.
Require Import IRed.
Require Import STS Behavior.
Require Import PCM IPM.
Require Import Skeleton Mod.
Require Export HMod2Mod.

Set Implicit Arguments.

Definition fnsems_keys {T} (fn: gname) (fnsems: alist gname ((list string) * T)) :=
  match (alist_find fn fnsems) with
  | Some (keys, body) => keys
  | None => []
  end.

Module HModSem.
Section HMODSEM.
  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    fnsems : alist gname (list string * (Any.t -> itree hmodE Any.t));
    initial_st : alist string Any.t;
    initial_cond: iProp;
    well_scoped:
      forall fn, incl (fnsems_keys fn fnsems) (List.map fst initial_st);
  }.

  Record wf (ms: t): Prop := mk_wf {
    wf_fns: List.NoDup (List.map fst ms.(fnsems));                                 
    wf_keys: List.NoDup (List.map fst ms.(initial_st));
  }.

  (**** Linking ****)

  Program Definition add ms1 ms2: t := {|
    fnsems := ms1.(fnsems) ++ ms2.(fnsems);
    initial_st := ms1.(initial_st) ++ ms2.(initial_st);
    initial_cond := (initial_cond ms1) ∗ (initial_cond ms2);
  |}.
  Next Obligation.
    ii. unfold fnsems_keys in H. des_ifs. 
    rewrite alist_find_app_o in Heq. des_ifs.
    {
      hexploit (ms1.(well_scoped) fn a). 
      { unfold fnsems_keys. des_ifs. }
      i. rewrite List.map_app. eapply in_or_app. eauto.
    }
    {
      hexploit (ms2.(well_scoped) fn a). 
      { unfold fnsems_keys. des_ifs. }
      i. rewrite List.map_app. eapply in_or_app. eauto.
    }
  Qed.

  (**** Wrapper ****)

  Definition wrap keys : forall T, hmodE T -> hmodE T :=
    (fun T e =>
       match e with
       | inr1 (inr1 (inl1 (SPut k v))) =>
           if existsb (eqb k) keys then e else inr1 (inr1 (inr1 (Choose T)))
       | inr1 (inr1 (inl1 (SGet k))) =>
           if existsb (eqb k) keys then e else inr1 (inr1 (inr1 (Choose T)))
       | _ => e
       end).

  Definition wrap_body (kb: list string * (Any.t -> itree hmodE Any.t)) :=
    fun arg => translate (wrap kb.1) (kb.2 arg).
  
  Definition wrap_pgE keys : pgE ~> itree hmodE :=
    (fun _ e =>
       match e with
       | SPut k v => if existsb (eqb k) keys then trigger (SPut k v) else (Ret tt↑)
       | SGet k => if existsb (eqb k) keys then trigger (SGet k) else (Ret tt↑)
       end).

  Definition to_mod (ms: t) (r: Σ): ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, kb) => (fn, interp_hp_fun (wrap_body kb))) ms.(fnsems);
    ModSem.initial_st := Any.pair (alist_encode ms.(initial_st)) r↑;
  |}.

End HMODSEM.
End HModSem.

Module HMod.
Section HMOD.
  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    get_modsem: Sk.t -> HModSem.t;
    sk: Sk.t;
  }.

  Definition add (md0 md1: t): t := {|
    get_modsem := fun sk => HModSem.add (md0.(get_modsem) sk) (md1.(get_modsem) sk);
    sk := Sk.add md0.(sk) md1.(sk);
  |}.

  Definition to_mod (md: t) (r: Σ): Mod.t := {|
    Mod.get_modsem := fun sk => HModSem.to_mod (md.(get_modsem) sk) r;
    Mod.sk := md.(sk);
  |}.
  
End HMOD.
End HMod.

Section HModProd.
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

  Definition IstEq keys: alist string Any.t -> alist string Any.t -> iProp :=
    fun st_src st_tgt => ⌜st_src = st_tgt ∧ incl keys (List.map fst st_src)⌝%I.

  Definition IstProd (IstL IstR : alist string Any.t -> alist string Any.t -> iProp) : alist string Any.t -> alist string Any.t -> iProp :=
    fun st_src st_tgt => (∃ st_srcL st_tgtL st_srcR st_tgtR,
      ⌜st_src = st_srcL ++ st_srcR /\ st_tgt = st_tgtL ++ st_tgtR⌝ ∗
      IstL st_srcL st_tgtL ∗ IstR st_srcR st_tgtR)%I.

End HModProd.


Module HModWrap.
Section RED.
  Context `{Σ: GRA.t}.

  Lemma transl_bind
    A B
    keys
    (itr: itree hmodE A) (ktr: A -> itree hmodE B)
    :
    translate (HModSem.wrap keys) (itr >>= ktr) = a <- (translate (HModSem.wrap keys) itr);; (translate (HModSem.wrap keys) (ktr a))
  .
  Proof. rewrite (bisim_is_eq (translate_bind _ _ _)); eauto. Qed.

  Lemma transl_tau
    A
    keys
    (itr: itree hmodE A)
  :
    translate (HModSem.wrap keys) (tau;; itr) = tau;; (translate (HModSem.wrap keys) itr)
  .
  Proof. rewrite (bisim_is_eq (translate_tau _ _)); eauto. Qed.

  Lemma transl_ret
      A (a: A) keys
  :
    translate (HModSem.wrap keys) (Ret a) = Ret a
  .
  Proof. rewrite (bisim_is_eq (translate_ret _ _)); eauto. Qed.

  Lemma transl_call
    keys fn args
  :
  translate (HModSem.wrap keys) (trigger (Call fn args)) = trigger (Call fn args)
  .
  Proof.
    unfold trigger. rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    do 2 f_equal. extensionalities. rewrite transl_ret. eauto.
  Qed.

  Lemma transl_put
    keys k v
  :
  translate (HModSem.wrap keys) (trigger (SPut k v)) =
    if existsb (eqb k) keys then trigger (SPut k v) else trigger (Choose Any.t)
  .
  Proof.
    unfold trigger. rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    des_ifs; s; do 2 f_equal; extensionalities; rewrite transl_ret; eauto.
  Qed.

  Lemma transl_get
    keys k
  :
  translate (HModSem.wrap keys) (trigger (SGet k)) =
    if existsb (eqb k) keys then trigger (SGet k) else trigger (Choose Any.t)
  .
  Proof.
    unfold trigger. rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    des_ifs; s; do 2 f_equal; extensionalities; rewrite transl_ret; eauto.
  Qed.
  
  Lemma transl_core
    T keys
    (e: coreE T)
    :
    translate (HModSem.wrap keys) (trigger e) = trigger e.
  Proof.
    unfold trigger. rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    des_ifs; s; do 2 f_equal; extensionalities; rewrite transl_ret; eauto.
  Qed.

  Lemma transl_Assume
    keys P
  :
    translate (HModSem.wrap keys) (trigger (Assume P)) = trigger (Assume P)
  .
  Proof.
    unfold trigger.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    do 2 f_equal.
    extensionalities. rewrite transl_ret. et.
  Qed.

  Lemma transl_Guarantee
    keys P
  :
    translate (HModSem.wrap keys) (trigger (Guarantee P)) = trigger (Guarantee P)
  .
  Proof.
    unfold trigger.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    do 2 f_equal.
    extensionalities. rewrite transl_ret. et.
  Qed.
  
(*  
  Lemma transl_triggerUB
    T keys
  :
    translate (HModSem.wrap keys) (triggerUB: itree _ T) = triggerUB
  .
  Proof.
    unfold triggerUB. rewrite transl_bind. f_equal.
    { apply transl_coreE. }
    extensionalities. ss.
  Qed.

  Lemma transl_triggerNB
    T keys
  :
    translate (HModSem.wrap keys) (triggerNB: itree _ T) = triggerNB
  .
  Proof.
    unfold triggerNB. rewrite transl_bind. f_equal.
    { apply transl_coreE. }
    extensionalities. ss.
  Qed.

  Lemma transl_unwrapU
    R keys (r: option R)
  :
    translate (HModSem.wrap keys) (unwrapU r) = unwrapU r
  .
  Proof.
    unfold unwrapU. destruct r.
    - apply transl_ret.
    - apply transl_triggerUB.
  Qed.

  Lemma transl_unwrapN
    R keys (r: option R)
  :
    translate (HModSem.wrap keys) (unwrapN r) = unwrapN r
  .
  Proof.
    unfold unwrapN. destruct r.
    - apply transl_ret.
    - apply transl_triggerNB.
  Qed.

  Lemma transl_asm
    keys P
  :
    translate (HModSem.wrap keys) (assume P) = assume P
  .
  Proof.
    unfold assume, trigger.
    rewrite transl_bind.
    rewrite transl_ret.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    do 3 f_equal.
    extensionalities. rewrite transl_ret. et.
  Qed.

  Lemma transl_guar
    keys P
  :
    translate (HModSem.wrap keys) (guarantee P) = guarantee P
  .
  Proof.
    unfold guarantee, trigger.
    rewrite transl_bind.
    rewrite transl_ret.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    do 3 f_equal.
    extensionalities. rewrite transl_ret. et.
  Qed.

  Lemma transl_ext
    T keys (itr0 itr1: itree _ T)
    (EQ: itr0 = itr1)
  :
    translate (HModSem.wrap keys) itr0 = translate (HModSem.wrap keys) itr1
  .
  Proof. subst. refl. Qed.
 *)
  
End RED.
End HModWrap.

(* Section RDB. *)
(*   Context `{Σ: GRA.t}. *)

(*   Global Program Instance transl_rdb: red_database (mk_box (@translate)) := *)
(*     mk_rdb *)
(*     0 *)
(*     (mk_box HModRed.transl_bind) *)
(*     (mk_box HModRed.transl_tau) *)
(*     (mk_box HModRed.transl_ret) *)
(*     (mk_box HModRed.transl_putE) *)
(*     (mk_box HModRed.transl_getE) *)
(*     (mk_box HModRed.transl_callE) *)
(*     (mk_box HModRed.transl_coreE) *)
(*     (mk_box HModRed.transl_triggerUB) *)
(*     (mk_box HModRed.transl_triggerNB) *)
(*     (mk_box HModRed.transl_unwrapU) *)
(*     (mk_box HModRed.transl_unwrapN) *)
(*     (mk_box HModRed.transl_assume) *)
(*     (mk_box HModRed.transl_guarantee) *)
(*     (mk_box HModRed.transl_ext). *)

(* End RDB. *)
