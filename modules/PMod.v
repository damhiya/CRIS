Require Import Coqlib.
Require Import sflib.
Require Import ITreelib.
Require Import AList.
Require Import Skeleton.
Require Import Any.
Require Import PCM IPM.
Require Import Events HMod.

Set Implicit Arguments.

Module PModSem.
Section PMODSEM.

  Context `{Σ : GRA.t}.

  Record t : Type := mk {
    scopes : list string;
    fnsems : alist gname (list string * (Any.t -> itree pmodE Any.t));
    initial_st : alist key Any.t;
    well_scoped_fns:
      forall fn, incl (fnsems_scopes fn fnsems) scopes;
    well_scoped_init:
      incl (state_scopes initial_st) scopes;
    nodup_fns:
      List.NoDup scopes -> List.NoDup (List.map fst initial_st);
  }.

  Definition transl {R} (itr : itree pmodE R) : itree hmodE R :=
    translate inr1 itr.

  Program Definition to_hmod (ms : t) : HModSem.t := {|
    HModSem.scopes := ms.(scopes);                                                    
    HModSem.fnsems := List.map (map_snd (λ kb, (kb.1, (λ i, transl (kb.2 i))))) ms.(fnsems);
    HModSem.initial_st := ms.(initial_st);
  |}.
  Next Obligation.
    i. destruct ms. s. ii.
    eapply well_scoped_fns0. instantiate (1:=fn).
    unfold fnsems_scopes, map_snd in *.
    rewrite alist_find_map in H.
    unfold o_map in *. des_ifs.
  Qed.
  Next Obligation. i. destruct ms. s. eauto. Qed.
  Next Obligation. i. destruct ms. eauto. Qed.

End PMODSEM.
End PModSem.

Module PMod.
Section PMOD.

  Context `{Σ : GRA.t}.

  Record t : Type := mk {
    modsem : Sk.t -> PModSem.t;
    sk : Sk.t;
  }.

  Definition to_hmod (md:t) : HMod.t := {|
    HMod.modsem := fun sk => PModSem.to_hmod (md.(modsem) sk);
    HMod.sk := md.(sk);
 |}.
    
End PMOD.
End PMod.

Notation "↟ it" := (PModSem.transl it) (at level 60, only printing).

Module PModRed.
Section RED.

  Context `{Σ : GRA.t}.

(* itree reduction *)
  Lemma transl_bind
        (R S : Type)
        (s : itree pmodE R) (k : R -> itree pmodE S)
    :
    PModSem.transl (s >>= k)
    =
    st <- PModSem.transl s;; PModSem.transl (k st).
  Proof.
    unfold PModSem.transl. rewrite (bisim_is_eq (translate_bind _ _ _)). eauto.
  Qed.

  Lemma transl_tau
        (U : Type)
        (t : itree _ U)
    :
      PModSem.transl (tau;; t)
      =
      tau;; (PModSem.transl t).
  Proof.
    unfold PModSem.transl. rewrite (bisim_is_eq (translate_tau _ _)). eauto.
  Qed.

  Lemma transl_ret
        (U : Type)
        (t : U)
    :
      PModSem.transl (Ret t)
      =
      Ret t.
  Proof.
    unfold PModSem.transl. rewrite (bisim_is_eq (translate_ret _ _)). eauto.
  Qed.

  Lemma transl_call
        (R : Type)
        (i : callE R)
    :
      PModSem.transl (trigger i)
      =
      trigger i.
  Proof.
    unfold PModSem.transl. unfold trigger.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)).
    do 2 f_equal. extensionalities.
    rewrite (bisim_is_eq (translate_ret _ _)). eauto.
  Qed.

  Lemma transl_sch
        (R : Type)
        (i : schE R)
    :
      PModSem.transl (trigger i)
      =
      trigger i.
  Proof.
    unfold PModSem.transl. unfold trigger.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)).
    do 2 f_equal. extensionalities.
    rewrite (bisim_is_eq (translate_ret _ _)). eauto.
  Qed.
  
  Lemma transl_pg
        (R : Type)
        (i : pgE R)
    :
      PModSem.transl (trigger i)
      =
      trigger i.
  Proof.
    unfold PModSem.transl. unfold trigger.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)).
    do 2 f_equal. extensionalities.
    rewrite (bisim_is_eq (translate_ret _ _)). eauto.
  Qed.

  Lemma transl_core
        (R : Type)
        (i : coreE R)
    :
      PModSem.transl (trigger i)
      =
      trigger i.
  Proof.
    unfold PModSem.transl. unfold trigger.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)).
    do 2 f_equal. extensionalities.
    rewrite (bisim_is_eq (translate_ret _ _)). eauto.
  Qed.  

  Lemma transl_unwrapU 
        (R : Type)
        (i : option R)
    :
    PModSem.transl (@unwrapU pmodE _ _ i)
    =
    unwrapU i.
  Proof.
    rewrite /unwrapU. des_ifs.
    - rewrite transl_ret; eauto.
    - rewrite /triggerUB !transl_bind !transl_core.
      f_equal; eauto. extensionalities. des_ifs.
  Qed.

  Lemma transl_unwrapN
        (R : Type)
        (i : option R)
    :
      PModSem.transl (@unwrapN pmodE _ _ i)
      =
      unwrapN i.
  Proof.
    rewrite /unwrapN. des_ifs.
    - rewrite transl_ret; eauto.
    - rewrite /triggerNB !transl_bind !transl_core.
      f_equal; eauto. extensionalities. des_ifs.
  Qed.

  Lemma transl_asm
        P
    : 
      PModSem.transl (assume P)
      =
      assume P.
  Proof.
    rewrite /assume !transl_bind !transl_core !transl_ret. eauto.
  Qed. 

  Lemma transl_guar
        P
    : 
      PModSem.transl (guarantee P)
      =
      guarantee P.
  Proof.
    rewrite /guarantee !transl_bind !transl_core !transl_ret. eauto.
  Qed.
  
(*  
  Lemma transl_triggerUB
        (R : Type)
    :
      PModSem.transl (triggerUB)
      =
      triggerUB (A:=R).
  Proof.
    rewrite /triggerUB !transl_bind !transl_core.
    f_equal; eauto. extensionalities. des_ifs.
  Qed.  

  Lemma transl_triggerNB
        (R : Type)
    :
    PModSem.transl (triggerNB)
    =
    triggerNB (A:=R).
  Proof.
    rewrite /triggerNB !transl_bind !transl_core.
    f_equal; eauto. extensionalities. des_ifs.
  Qed.


 *)
  
End RED.
End PModRed.
