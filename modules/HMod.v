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

  (* TODO: move to a right place *)
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

Module HModSem.
Section HMODSEM.
  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    scopes : list string;
    fnsems : alist gname (list string * (Any.t -> itree hmodE Any.t));
    initial_st : alist key Any.t;
    initial_cond: iProp;
    well_scoped_fns:
      forall fn, incl (fnsems_scopes fn fnsems) scopes;
    well_scoped_init:
      incl (List.map (fst ∘ fst) initial_st) scopes;
  }.

  Record wf (ms: t): Prop := mk_wf {
    wf_fns: List.NoDup (List.map fst ms.(fnsems));
    wf_scopes: List.NoDup ms.(scopes);
  }.

  (**** Linking ****)

  Program Definition add ms1 ms2: t := {|
    fnsems := ms1.(fnsems) ++ ms2.(fnsems);
    scopes := ms1.(scopes) ++ ms2.(scopes);
    initial_st := ms1.(initial_st) ++ ms2.(initial_st);
    initial_cond := (initial_cond ms1) ∗ (initial_cond ms2);
  |}.
  Next Obligation.
    ii. unfold fnsems_scopes in H. des_ifs. 
    rewrite alist_find_app_o in Heq. des_ifs.
    {
      hexploit (ms1.(well_scoped_fns) fn a). 
      { unfold fnsems_scopes. des_ifs. }
      i. eapply in_or_app. eauto.
    }
    {
      hexploit (ms2.(well_scoped_fns) fn a). 
      { unfold fnsems_scopes. des_ifs. }
      i. eapply in_or_app. eauto.
    }
  Qed.
  Next Obligation.
    ii. destruct ms1, ms2. ss.
    rewrite map_app in H. apply in_or_app. apply in_app_or in H.
    destruct H; eauto.
  Qed.

  (**** Sandboxing ****)

  Definition handle_sandbox scopes : hmodE -< hmodE :=
    (fun T e =>
       match e with
       | inr1 (inr1 (inl1 (SPut (s,f) v))) =>
           if existsb (eqb s) scopes then e else inr1 (inr1 (inr1 (Choose T)))
       | inr1 (inr1 (inl1 (SGet (s,f)))) =>
           if existsb (eqb s) scopes then e else inr1 (inr1 (inr1 (Choose T)))
       | _ => e
       end).

  Definition sandbox {T} scopes (itr: itree hmodE T) :=
    translate (handle_sandbox scopes) itr.

  Definition sandbox_body (kb: list string * (Any.t -> itree hmodE Any.t)) :=
    fun arg => sandbox kb.1 (kb.2 arg).
  
  Definition to_mod (ms: t) (r: Σ): ModSem.t := {|
    ModSem.fnsems := List.map (map_snd (interp_hp_fun ∘ sandbox_body)) ms.(fnsems);
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

Module HModSB.
Section RED.
  Context `{Σ: GRA.t}.

  Lemma transl_bind
    A B
    scopes
    (itr: itree hmodE A) (ktr: A -> itree hmodE B)
    :
    HModSem.sandbox scopes (itr >>= ktr) = a <- (HModSem.sandbox scopes itr);; (HModSem.sandbox scopes (ktr a))
  .
  Proof. unfold HModSem.sandbox. rewrite (bisim_is_eq (translate_bind _ _ _)); eauto. Qed.

  Lemma transl_tau
    A
    scopes
    (itr: itree hmodE A)
  :
    HModSem.sandbox scopes (tau;; itr) = tau;; (HModSem.sandbox scopes itr)
  .
  Proof. unfold HModSem.sandbox. rewrite (bisim_is_eq (translate_tau _ _)); eauto. Qed.

  Lemma transl_ret
      A (a: A) scopes
  :
    HModSem.sandbox scopes (Ret a) = Ret a
  .
  Proof. unfold HModSem.sandbox. rewrite (bisim_is_eq (translate_ret _ _)); eauto. Qed.

  Lemma transl_call
    scopes fn args
  :
  HModSem.sandbox scopes (trigger (Call fn args)) = trigger (Call fn args)
  .
  Proof.
    unfold HModSem.sandbox, trigger.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    do 2 f_equal. extensionalities.
    rewrite (bisim_is_eq (translate_ret _ _)); eauto.
  Qed.

  Lemma transl_put
    scopes k v
  :
  HModSem.sandbox scopes (trigger (SPut k v)) =
    if existsb (eqb k.1) scopes then trigger (SPut k v) else trigger (Choose Any.t)
  .
  Proof.
    unfold HModSem.sandbox, trigger. destruct k. s.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    des_ifs; s; do 2 f_equal; extensionalities;
      rewrite (bisim_is_eq (translate_ret _ _)); eauto.
  Qed.

  Lemma transl_get
    scopes k
  :
  HModSem.sandbox scopes (trigger (SGet k)) =
    if existsb (eqb k.1) scopes then trigger (SGet k) else trigger (Choose Any.t)
  .
  Proof.
    unfold HModSem.sandbox, trigger. destruct k. s.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    des_ifs; s; do 2 f_equal; extensionalities;
      rewrite (bisim_is_eq (translate_ret _ _)); eauto.
  Qed.
  
  Lemma transl_core
    T scopes
    (e: coreE T)
    :
    HModSem.sandbox scopes (trigger e) = trigger e.
  Proof.
    unfold HModSem.sandbox, trigger.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    des_ifs; s; do 2 f_equal; extensionalities;
      rewrite (bisim_is_eq (translate_ret _ _)); eauto.
  Qed.

  Lemma transl_Assume
    scopes P
  :
    HModSem.sandbox scopes (trigger (Assume P)) = trigger (Assume P)
  .
  Proof.
    unfold HModSem.sandbox, trigger.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    do 2 f_equal. extensionalities.
    rewrite (bisim_is_eq (translate_ret _ _)); eauto.
  Qed.

  Lemma transl_Guarantee
    scopes P
  :
    HModSem.sandbox scopes (trigger (Guarantee P)) = trigger (Guarantee P)
  .
  Proof.
    unfold HModSem.sandbox, trigger.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    do 2 f_equal. extensionalities.
    rewrite (bisim_is_eq (translate_ret _ _)); eauto.
  Qed.

  Lemma transl_unwrapU
    R scopes (r: option R)
  :
    HModSem.sandbox scopes (unwrapU r) = unwrapU r
  .
  Proof.
    unfold unwrapU. destruct r.
    - apply transl_ret.
    - unfold triggerUB. rewrite/__ !transl_bind !transl_core.
      f_equal. extensionalities. ss.
  Qed.

  Lemma transl_unwrapN
    R scopes (r: option R)
  :
    HModSem.sandbox scopes (unwrapN r) = unwrapN r
  .
  Proof.
    unfold unwrapN. destruct r.
    - apply transl_ret.
    - unfold triggerNB. rewrite/__ !transl_bind !transl_core.
      f_equal. extensionalities. ss.
  Qed.

  Lemma transl_asm
    scopes P
  :
    HModSem.sandbox scopes (assume P) = assume P
  .
  Proof.
    unfold assume. rewrite/__ transl_bind transl_core transl_ret. eauto.
  Qed.

  Lemma transl_guar
    scopes P
  :
    HModSem.sandbox scopes (guarantee P) = guarantee P
  .
  Proof.
    unfold guarantee. rewrite/__ transl_bind transl_core transl_ret. eauto.
  Qed.
  
(*  
  Lemma transl_triggerUB
    T scopes
  :
    HModSem.sandbox scopes (triggerUB: itree _ T) = triggerUB
  .
  Proof.
    unfold triggerUB. rewrite transl_bind. f_equal.
    { apply transl_coreE. }
    extensionalities. ss.
  Qed.

  Lemma transl_triggerNB
    T scopes
  :
    HModSem.sandbox scopes (triggerNB: itree _ T) = triggerNB
  .
  Proof.
    unfold triggerNB. rewrite transl_bind. f_equal.
    { apply transl_coreE. }
    extensionalities. ss.
  Qed.

  Lemma transl_ext
    T scopes (itr0 itr1: itree _ T)
    (EQ: itr0 = itr1)
  :
    HModSem.sandbox scopes itr0 = HModSem.sandbox scopes itr1
  .
  Proof. subst. refl. Qed.
 *)
  
End RED.
End HModSB.

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
