
Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Export AList.
Require Import Any.
Require Import BasicEvents.
Require Import Red IRed.

Section RED.
  (* itree reduction lemmas *)
  Section ES.
    Lemma interp_modE_bind
          A B
          (itr: itree modE A) (ktr: A -> itree modE B)
          (prog: callE ~> itree modE)
          st0
      :
        interp_modE prog (v <- itr ;; ktr v) st0 =
        '(st1, v) <- interp_modE prog (itr) st0 ;; interp_modE prog (ktr v) st1.

    Proof. unfold interp_modE, interp_stateE. des_ifs. grind. Qed.

    Lemma interp_modE_tau
          (prog: callE ~> itree modE)
          A
          (itr: itree modE A)
          st0
      :
        interp_modE prog (tau;; itr) st0 = tau;; interp_modE prog itr st0.
    Proof. unfold interp_modE, interp_stateE. des_ifs. grind. Qed.

    Lemma interp_modE_ret
          T
          prog st0 (v: T)
      :
        interp_modE prog (Ret v: itree modE _) st0 = Ret (st0, v).
    Proof. unfold interp_modE, interp_stateE. des_ifs. grind. Qed.

    Lemma interp_modE_callE
          p st0 T
          (* (e: modE Σ) *)
          (e: callE T)
      :
        interp_modE p (trigger e) st0 = tau;; (interp_modE p (p _ e) st0).
    Proof. unfold interp_modE, interp_stateE. des_ifs. grind. Qed.

    Lemma interp_modE_stateE
          p st0
          (* (e: modE Σ) *)
          T
          (e: stateE T)
      :
        interp_modE p (trigger e) st0 =
        '(st1, r) <- handle_stateE e st0;;
        tau;; tau;;
        Ret (st1, r).
    Proof.
      unfold interp_modE, interp_stateE. grind.
    Qed.

    Lemma interp_modE_coreE
          p st0
          T
          (e: coreE T)
      :
        interp_modE p (trigger e) st0 = r <- trigger e;; tau;; tau;; Ret (st0, r).
    Proof.
      unfold interp_modE, interp_stateE. grind.
      unfold pure_state. grind.
    Qed.

    Lemma interp_modE_triggerUB
          (prog: callE ~> itree modE)
          st0
          A
      :
        (interp_modE prog (triggerUB) st0: itree coreE (_ * A)) = triggerUB.
    Proof.
      unfold interp_modE, interp_stateE, pure_state, triggerUB. grind.
    Qed.

    Lemma interp_modE_triggerNB
          (prog: callE ~> itree modE)
          st0
          A
      :
        (interp_modE prog (triggerNB) st0: itree coreE (_ * A)) = triggerNB.
    Proof.
      unfold interp_modE, interp_stateE, pure_state, triggerNB. grind.
    Qed. 
    
    Lemma interp_modE_unwrapU
          prog R st0 (r: option R)
      :
        interp_modE prog (unwrapU r) st0 = r <- unwrapU r;; Ret (st0, r).
    Proof.
      unfold unwrapU. des_ifs.
      - rewrite interp_modE_ret. grind.
      - rewrite interp_modE_triggerUB. unfold triggerUB. grind.
    Qed.

    Lemma interp_modE_unwrapN
          prog R st0 (r: option R)
      :
        interp_modE prog (unwrapN r) st0 = r <- unwrapN r;; Ret (st0, r).
    Proof.
      unfold unwrapN. des_ifs.
      - rewrite interp_modE_ret. grind.
      - rewrite interp_modE_triggerNB. unfold triggerNB. grind.
    Qed.

    Lemma interp_modE_assume
          prog st0 (P: Prop)
      :
        interp_modE prog (assume P) st0 = assume P;;; tau;; tau;; Ret (st0, tt).
    Proof.
      unfold assume.
      repeat (try rewrite interp_modE_bind; try rewrite bind_bind). grind.
      rewrite interp_modE_coreE.
      repeat (try rewrite interp_modE_bind; try rewrite bind_bind). grind.
      rewrite interp_modE_ret.
      refl.
    Qed.

    Lemma interp_modE_guarantee
          prog st0 (P: Prop)
      :
        interp_modE prog (guarantee P) st0 = guarantee P;;; tau;; tau;; Ret (st0, tt).
    Proof.
      unfold guarantee.
      repeat (try rewrite interp_modE_bind; try rewrite bind_bind). grind.
      rewrite interp_modE_coreE.
      repeat (try rewrite interp_modE_bind; try rewrite bind_bind). grind.
      rewrite interp_modE_ret.
      refl.
    Qed.    

    Lemma interp_modE_ext
          prog R (itr0 itr1: itree _ R) st0
      : 
        itr0 = itr1 -> interp_modE prog itr0 st0 = interp_modE prog itr1 st0.
    Proof. i; subst; refl. Qed.    

    Global Program Instance interp_modE_rdb: red_database (mk_box (@interp_modE)) :=
      mk_rdb
        1
        (mk_box interp_modE_bind)
        (mk_box interp_modE_tau)
        (mk_box interp_modE_ret)
        (mk_box interp_modE_stateE)
        (mk_box interp_modE_stateE)
        (mk_box interp_modE_callE)
        (mk_box interp_modE_coreE)
        (mk_box interp_modE_triggerUB)
        (mk_box interp_modE_triggerNB)
        (mk_box interp_modE_unwrapU)
        (mk_box interp_modE_unwrapN)
        (mk_box interp_modE_assume)
        (mk_box interp_modE_guarantee)
        (mk_box interp_modE_ext).
        
  End ES.

  Section TAKE.

    Lemma interp_takeE_bind
          A B
          (itr: itree takeE A) (ktr: A -> itree takeE B)
      :
        interp_takeE (v <- itr ;; ktr v) = 
        v <- interp_takeE itr;; interp_takeE (ktr v).
    Proof. 
      unfold interp_takeE. grind. 
    Qed.

    Lemma interp_takeE_ret
          T (v: T)
      :
        interp_takeE (Ret v: itree takeE _) = Ret v.
    Proof. 
      unfold interp_takeE. grind. 
    Qed.

    Lemma interp_takeE_tau
          T (itr: itree takeE T)
      :
        interp_takeE (tau;; itr) = tau;; interp_takeE itr.
    Proof. 
      unfold interp_takeE. grind. 
    Qed.

    Lemma interp_takeE_take
          X (e: takeE X)
      :
        interp_takeE (trigger e) = (handle_takeE e) >>= (fun r => tau;; Ret r).
    Proof.
      unfold interp_takeE. rewrite interp_trigger. grind.
    Qed.

  End TAKE.
End RED.

