Require Import Common.

Require Import Mod2ITree.

Module StRed.
  Lemma ret
        E A st0 v
    :
      @interp_stateE E A (Ret v) st0 = Ret (st0, v)
  .
  Proof. 
    unfold interp_stateE. grind.
  Qed.
  
  Lemma tau
        A (itr: itree (stateE +' coreE) A)
        st0 
    :
      interp_stateE _ (tau;; itr) st0 = tau;; interp_stateE _ itr st0
  .
  Proof. 
    unfold interp_stateE. grind. 
  Qed.

  Lemma bind
        A B
        (itr: itree (stateE +' coreE) A)
        (ktr: A -> itree (stateE +' coreE) B)
        st0
    :
      interp_stateE B (v <- itr ;; ktr v) st0 =
      '(st1, v):_ <- interp_stateE A (itr) st0 ;; interp_stateE B (ktr v) st1.
  Proof.
    unfold interp_stateE. grind. destruct x. grind.
  Qed.
  
  Lemma state
        E st0 T e
    :
      @interp_stateE E T (trigger e) st0 =
      '(st1, r):_ <- handle_stateE _ e st0;;
      tau;; Ret (st1, r).
  Proof.
    unfold interp_stateE. grind. destruct x. grind.
  Qed.

  Lemma core
        st0 T
        (e: coreE T)
    :
      @interp_stateE (coreE) _ (trigger e) st0 = r <- trigger e;; tau;; Ret (st0, r)
  .
  Proof.
    unfold interp_stateE. grind.
    unfold Mod2ITree.pure_state. grind.
  Qed.

  Lemma triggerUB
        st0 A
    :
      (@interp_stateE (stateE +' coreE) A (triggerUB) st0) = triggerUB
  .
  Proof.
    unfold interp_stateE, Mod2ITree.pure_state, triggerUB. grind.
  Qed.
  
  Lemma triggerNB
        st0 A
    :
      (@interp_stateE (stateE +' coreE) A (triggerNB) st0) = triggerNB
  .
  Proof.
    unfold interp_stateE, Mod2ITree.pure_state, triggerNB. grind.
  Qed.  

End StRed.
