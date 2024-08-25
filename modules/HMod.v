Require Import Coqlib AList.
Require Import sflib.
Require Import ITreelib.
Require Import Any.
Require Import EventsRed Events.
Require Import IRed.
Require Import STS Behavior.
Require Import PCM IPM.
Require Import Skeleton Mod.
Require Import PropExtensionality.
Require Export HMod2Mod.

Set Implicit Arguments.

Module HModSem.
Section HMODSEM.
  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    scopes : list string;
    fnsems : alist gname (list string * (Any.t -> itree hmodE Any.t));
    initial_st : alist key Any.t;
    
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

  Program Definition empty : t := {|
    scopes := [];
    fnsems := [];
    initial_st := [];
  |}.
  Next Obligation. ii; ss. Qed.
  Next Obligation. ii; ss. Qed.

  Program Definition add ms1 ms2: t := {|
    fnsems := ms1.(fnsems) ++ ms2.(fnsems);
    scopes := ms1.(scopes) ++ ms2.(scopes);
    initial_st := ms1.(initial_st) ++ ms2.(initial_st);
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
    modsem: Sk.t -> HModSem.t;
    sk: Sk.t;
  }.

  Definition tp : Type := (t * iProp)%type.

  Definition empty := {|
    modsem := const (HModSem.empty);
    sk := []
  |}.
  
  Definition add (md0 md1: t): t := {|
    modsem := fun sk => HModSem.add (md0.(modsem) sk) (md1.(modsem) sk);
    sk := Sk.add md0.(sk) md1.(sk);
  |}.

  Definition to_mod (md: t) (r: Σ): Mod.t := {|
    Mod.modsem := fun sk => HModSem.to_mod (md.(modsem) sk) r;
    Mod.sk := md.(sk);
  |}.

  Definition get_scopes (md: t) : Sk.t -> list string :=
    fun sk => (md.(modsem) sk).(HModSem.scopes).
  
End HMOD.
End HMod.

Section PROPERTIES.
  
  Context `{Σ: GRA.t}.

  Lemma iprop'_extensionality (P Q: iProp'):
    iProp_pred P = iProp_pred Q -> P = Q.
  Proof.
    i. destruct P, Q. ss. revert iProp_mono iProp_mono0.
    rewrite H. i. f_equal. apply proof_irrelevance.
  Qed.

  Lemma iprop_sepconj_assoc (P Q R: iProp):
    ((P ∗ Q) ∗ R)%I = (P ∗ (Q ∗ R))%I.
  Proof.
    unfold iProp, bi_car, bi_sep, Sepconj. unseal "iProp".
    apply iprop'_extensionality. s.
    extensionality r. apply propositional_extensionality.
    split; i.
    - des. subst. exists a0, (b0 ⋅ b). esplits; eauto.
      rewrite URA.add_assoc. eauto.
    - des. subst. exists (a ⋅ a0), b0. esplits; eauto.
      rewrite URA.add_assoc. eauto.
  Qed.

  Lemma iprop_add_empty_l (P: iProp):
    (emp ∗ P)%I = P.
  Proof.
    unfold iProp, bi_car, bi_sep, Sepconj, bi_emp, Emp. unseal "iProp".
    apply iprop'_extensionality. s.
    extensionality r. apply propositional_extensionality.
    split; i.
    - des. subst. eapply iProp_mono; eauto.
      rr. esplits; eauto. rewrite URA.add_comm. eauto.
    - exists ε, r. esplits; eauto.
      rewrite URA.unit_idl. eauto.
  Qed.

  Lemma iprop_add_empty_r (P: iProp):
    (P ∗ emp)%I = P.
  Proof.
    unfold iProp, bi_car, bi_sep, Sepconj, bi_emp, Emp. unseal "iProp".
    apply iprop'_extensionality. s.
    extensionality r. apply propositional_extensionality.
    split; i.
    - des. subst. eapply iProp_mono; eauto.
      rr. esplits; eauto.
    - exists r, ε. esplits; eauto.
      rewrite URA.add_comm. rewrite URA.unit_idl. eauto.
  Qed.

  Lemma hmodsem_extensionality (ms1 ms2: HModSem.t)
    (SCOPE: HModSem.scopes ms1 = HModSem.scopes ms2)
    (FNSEM: HModSem.fnsems ms1 = HModSem.fnsems ms2)
    (INITS: HModSem.initial_st ms1 = HModSem.initial_st ms2)
    (* (INITC: HModSem.initial_cond ms1 = HModSem.initial_cond ms2) *)
    :
    ms1 = ms2.
  Proof.
    destruct ms1, ms2; ss. subst. f_equal; apply proof_irrelevance.
  Qed.
  
  Lemma hmodsem_add_assoc (ms1 ms2 ms3: HModSem.t):
    HModSem.add (HModSem.add ms1 ms2) ms3 = HModSem.add ms1 (HModSem.add ms2 ms3).
  Proof.
    destruct ms1, ms2, ms3.
    apply hmodsem_extensionality; s; try rewrite app_assoc; eauto.
    (* destruct initial_cond, initial_cond0, initial_cond1; ss. *)
    (* rewrite iprop_sepconj_assoc. eauto. *)
  Qed.

  Lemma hmodsem_add_empty_l ms:
    HModSem.add HModSem.empty ms = ms.
  Proof.
    destruct ms. apply hmodsem_extensionality; s; eauto.    
  Qed.

  Lemma hmodsem_add_empty_r ms:
    HModSem.add ms HModSem.empty = ms.
  Proof.
    destruct ms. apply hmodsem_extensionality; s; try rewrite app_nil_r; eauto.
  Qed.

  Lemma hmod_add_assoc (md1 md2 md3: HMod.t):
    HMod.add (HMod.add md1 md2) md3 = HMod.add md1 (HMod.add md2 md3).
  Proof.
    destruct md1, md2, md3. unfold HMod.add. s. f_equal.
    - extensionalities. rewrite hmodsem_add_assoc. eauto.
    - unfold Sk.add. rewrite app_assoc. eauto.
  Qed.

  Lemma hmod_add_empty_l md:
    HMod.add HMod.empty md = md.
  Proof.
    destruct md. unfold HMod.add. s. f_equal.
    extensionalities. apply hmodsem_add_empty_l.
  Qed.

  Lemma hmod_add_empty_r md:
    HMod.add md HMod.empty = md.
  Proof.
    destruct md. unfold HMod.add. s. f_equal.
    - extensionalities. apply hmodsem_add_empty_r.
    - destruct sk; ss. unfold Sk.add. s. rewrite app_nil_r. eauto.
  Qed.
  
End PROPERTIES.

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
    if existsb (eqb k.1) scopes then trigger (SPut k v) else trigger (Choose _)
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
