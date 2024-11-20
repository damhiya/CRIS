Require Import Coqlib.
Require Import sflib.
Require Import ITreelib.
Require Import AList.
Require Import Behavior.
Require Import Events SMod HMod Mod.
Require Import SMod2HMod HMod2Mod.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Any.
Require Export STB.
Require Import ModSim.

Set Implicit Arguments.

(******* Rename each section into proper name  *******)


Module SModSemElim.
Section ELIM.
  Import SModSem.
  Context `{Σ: GRA.t}.
  Variable ginv: invspec.
  Variable stb: gname -> option fspec.

  Program Definition to_elim (ms: t): HModSem.t := {|
    HModSem.scopes := ms.(scopes);
    HModSem.fnsems := List.map (map_snd (λ ksb, (ksb.1, fsb_body ksb.2))) (ms.(fnsems));
    HModSem.initial_st := ms.(initial_st);
  |}.
  Next Obligation.
    i. destruct ms. ss. ii. unfold fnsems_scopes in *. unfold map_snd in*.
    rewrite! alist_find_map in H. specialize (well_scoped_fns0 fn a).
    des_ifs; ss. inv Heq. eauto.
  Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.

End ELIM.
End SModSemElim.

Module SModElim.
Section ELIM.
  Import SMod.
  Context `{Σ: GRA.t}.
  Variable ginv: Sk.t -> invspec.
  Variable stb: Sk.t -> gname -> option fspec.

  Definition to_elim (md: t) := {|
    HMod.modsem := fun sk => SModSemElim.to_elim (md.(modsem) sk);
    HMod.sk := md.(sk);
  |}.

End ELIM.
End SModElim.


(* 
Section CANCEL.
  Context `{Σ: GRA.t}.
  Variable ginv: invspec.
  Variable stb: gname -> option fspec.

  Section ELIM.
    (* Interp- every event by trivial_Handler gives eliminated itree *)
    Definition interp_smod_elim: itree hmodE ~> itree hmodE :=
      interp ((case_ (bif:=sum1) (trivial_Handler)
             (case_ (bif:=sum1) (trivial_Handler)
             (case_ (bif:=sum1) (trivial_Handler)
              trivial_Handler)))).

    Definition interp_sb_hp_elim (body: Any.t -> itree hmodE Any.t): Any.t -> itree hmodE Any.t :=
      (@interp_smod_elim _) ∘ body.

  End ELIM.

End CANCEL.

Module ElimRed.
Section RED.
  Context `{Σ: GRA.t}.
  Variable ginv: invspec.

  Lemma interp_bind
        (R S: Type)
        (s : itree hmodE R) (k : R -> itree hmodE S)
    :
      interp_smod_elim (s >>= k)
      =
      st <- interp_smod_elim s;; interp_smod_elim (k st).
  Proof.
    unfold interp_smod_elim in *. grind.
  Qed.

  Lemma interp_tau
        (U: Type)
        (t : itree _ U)
    :
      interp_smod_elim (tau;; t)
      =
      tau;; (interp_smod_elim t).
  Proof.
    unfold interp_smod_elim in *. grind.
  Qed.

  Lemma interp_ret
        (U: Type)
        (t: U)
        
    :
      interp_smod_elim (Ret t)
      =
      Ret t.
  Proof.
    unfold interp_smod_elim in *. grind.
  Qed.

  Lemma interp_sch
        (R: Type)
        (i: schE R)
    :
      interp_smod_elim (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof.
    unfold interp_smod_elim in *. rewrite interp_trigger. grind.
  Qed.
  
  Lemma interp_call
        (R: Type)
        (i: callE R)
    :
      interp_smod_elim (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof.
    unfold interp_smod_elim in *. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_pg
        (R: Type)
        (i: pgE R)        
    :
      interp_smod_elim (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof.
    unfold interp_smod_elim. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_core
        (R: Type)
        (i: coreE R)
        
    :
      interp_smod_elim (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof.
    unfold interp_smod_elim. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_ag {A} (e: agE A)
        
    :
      interp_smod_elim (trigger e)
      =
      x <- trigger e ;; tau;; Ret x.
  Proof.
    unfold interp_smod_elim. rewrite interp_trigger. grind.
  Qed.
  
  Lemma interp_unwrapU 
        (R: Type)
        (i: option R)
        
    :
      interp_smod_elim (@unwrapU hmodE _ _ i)
      =
      r <- (unwrapU i);; Ret r.
  Proof.
    unfold interp_smod_elim, unwrapU in *. des_ifs; grind.
    unfold triggerUB in *. rewrite unfold_interp. grind.
  Qed.

  Lemma interp_unwrapN
        (R: Type)
        (i: option R)
        
    :
      interp_smod_elim (@unwrapN hmodE _ _ i)
      =
      r <- (unwrapN i);; Ret r.
  Proof.
    unfold interp_smod_elim, unwrapN in *. des_ifs; grind.
    unfold triggerNB in *. rewrite unfold_interp. grind.
  Qed.
  
  Lemma interp_asm
        P
    : 
      interp_smod_elim (assume P)
      =
      r <- assume P;; tau;; Ret r.
  Proof.
    unfold assume. rewrite interp_bind. rewrite interp_core. grind. rewrite interp_ret. refl.
  Qed. 

  Lemma interp_guar
        P
    : 
      interp_smod_elim (guarantee P)
      =
      r <- guarantee P;; tau;; Ret r.
  Proof.
    unfold guarantee. rewrite interp_bind. rewrite interp_core. grind. rewrite interp_ret. refl.
  Qed.

End RED.
End ElimRed. *)
