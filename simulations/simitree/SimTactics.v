Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import Mod Translate.
Require Import SimModSem.
Require Import STB.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
Require Import Red IRed.

Set Implicit Arguments.

#[export] Hint Resolve sim_itree_mon: paco.
#[export] Hint Resolve cpn8_wcompat: paco.



Ltac ired_l := try (prw _red_gen 2 1 0).
Ltac ired_r := try (prw _red_gen 1 1 0).

Ltac ired_both := ired_l; ired_r.



(* "safe" simulation constructors *)
Section SIM.
  Variable world: Type.

  Let st_local: Type := (Any.t).
  Let W: Type := (Any.t) * (Any.t).

  Variable wf: world -> W -> Prop.
  Variable le: relation world.

  Variable fl_src fl_tgt: alist gname (Any.t -> itree modE Any.t).


  Variant _safe_sim_itree
          (r g: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree modE R_src -> st_local * itree modE R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree modE R_src -> st_local * itree modE R_tgt -> Prop :=
  | safe_sim_itree_ret
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      v_src v_tgt
      (RET: RR st_src0 st_tgt0 v_src v_tgt)
    :
      _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt))
  | safe_sim_itree_call
      i_src0 i_tgt0 w st_src0 st_tgt0
      fn varg k_src k_tgt
      (SIM: exists w0,
          (<<WF: wf w0 (st_src0, st_tgt0)>>) /\
          (<<K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
              r _ _ RR true true w (st_src1, k_src vret) (st_tgt1, k_tgt vret)>>))
    :
      _safe_sim_itree r g RR i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
                      (st_tgt0, trigger (Call fn varg) >>= k_tgt)

  | safe_sim_itree_io
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      I O fn (varg: I) k_src k_tgt
      (K: forall (vret: O),
          r _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, trigger (IO fn varg) >>= k_src)
                      (st_tgt0, trigger (IO fn varg) >>= k_tgt)

  | safe_sim_itree_tau_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: r _ _ RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)

  | safe_sim_itree_tau_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | safe_sim_itree_choose_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: forall (x: X), r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, i_src)
                      (st_tgt0, trigger (Choose X) >>= k_tgt)
                      
  | safe_sim_itree_take_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: forall (x: X), r _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
                      (st_tgt0, i_tgt)
  
  | safe_sim_itree_supdate_src
    i_src0 i_tgt0 w0 st_src0 st_tgt0
    X k_src i_tgt
    (run: st_local -> st_local * X)
    (K: r _ _ RR true i_tgt0 w0 (fst (run st_src0), k_src (snd (run st_src0))) (st_tgt0, i_tgt))
  :
    _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, trigger (SUpdate run) >>= k_src)
                    (st_tgt0, i_tgt)

  | safe_sim_itree_supdate_tgt
    i_src0 i_tgt0 w0 st_src0 st_tgt0
    X i_src k_tgt
    (run: st_local -> st_local * X)
    (K: r _ _ RR i_src0 true w0 (st_src0, i_src) (fst (run st_tgt0), k_tgt (snd (run st_tgt0))))
  :
    _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, i_src)
                    (st_tgt0, trigger (SUpdate run) >>= k_tgt)

  | safe_sim_itree_inline_src
      i_src0 i_tgt0 w st_src st_tgt
      f fn varg k_src i_tgt
      (FUN: alist_find fn fl_src = Some f)
      (K: r _ _ RR true i_tgt0 w (st_src, (f varg) >>= k_src) (st_tgt, i_tgt))
    :
      _safe_sim_itree r g RR i_src0 i_tgt0 w (st_src, trigger (Call fn varg) >>= k_src)
                      (st_tgt, i_tgt)
  | safe_sim_itree_inline_tgt
      i_src0 i_tgt0 w st_src st_tgt
      f fn varg i_src k_tgt
      (FUN: alist_find fn fl_tgt = Some f)
      (K: r _ _ RR i_src0 true w (st_src, i_src) (st_tgt, (f varg) >>= k_tgt))
    :
      _safe_sim_itree r g RR i_src0 i_tgt0 w (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt)  
  .

  Lemma safe_sim_sim r g:
    @_safe_sim_itree (gpaco8 (_sim_itree wf le fl_src fl_tgt) (cpn8 (_sim_itree wf le fl_src fl_tgt)) r g) (gpaco8 (_sim_itree wf le fl_src fl_tgt) (cpn8 (_sim_itree wf le fl_src fl_tgt)) g g)
    <8=
    gpaco8 (_sim_itree wf le fl_src fl_tgt) (cpn8 (_sim_itree wf le fl_src fl_tgt)) r g.
  Proof.
    i. eapply sim_itreeC_spec. inv PR; try by (econs; eauto).
    des. econs; eauto.
  Qed.

End SIM.

Ltac prep := ired_both.

Ltac _force_l :=
  prep;
  match goal with
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, unwrapN ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, guarantee ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_both; apply sim_itreeC_spec; eapply sim_itreeC_choose_src; [exists name]|contradict name]; cycle 1

  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, ITree.bind (interp _ guarantee ?P) _ (_, _))) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_both; apply sim_itreeC_spec; eapply sim_itreeC_choose_src; [exists name]|contradict name]; cycle 1

   (* TODO: handle interp_hCallE_tgt better and remove this case *)
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, ITree.bind (interp _ (guarantee ?P )) _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_both; apply sim_itreeC_spec; eapply sim_itreeC_choose_src; [exists name]|contradict name]; cycle 1; clear name

  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_tgt; apply sim_itreeC_spec; econs; unseal i_tgt
  end
.

Ltac _force_r :=
  prep;
  match goal with
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, unwrapU ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, assume ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    destruct (classic P) as [name|name]; [ired_both; apply sim_itreeC_spec; eapply sim_itreeC_take_tgt; [exists name]|contradict name]; cycle 1

  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_src; apply sim_itreeC_spec; econs; unseal i_src
  end
.

Ltac _step :=
  match goal with
  (*** blacklisting ***)
  (* | [ |- (gpaco5 (_sim_itree wf) _ _ _ _ (_, trigger (Choose _) >>= _) (_, ?i_tgt)) ] => idtac *)
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, triggerUB >>= _) (_, _)) ] =>
    unfold triggerUB; ired_l; _step; done
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|unfold triggerUB; ired_both; _force_l; ss; fail]
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, assume ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    ired_both; apply sim_itreeC_spec; eapply sim_itreeC_take_src; intro name

  (*** blacklisting ***)
  (* | [ |- (gpaco5 (_sim_itree wf) _ _ _ _ (_, _) (_, trigger (Take _) >>= _)) ] => idtac *)
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, triggerNB >>= _) (_, _)) ] =>
    unfold triggerNB; ired_r; _step; done
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, unwrapN ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|unfold triggerNB; ired_both; _force_r; ss; fail]
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, guarantee ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    ired_both; apply sim_itreeC_spec; eapply sim_itreeC_choose_tgt; intro name
 
  | _ => (*** default ***)
    eapply safe_sim_sim; econs; i
  end;
  match goal with
  | [ |- exists (_: unit), _ ] => esplits; [eauto|..]; i
  | [ |- exists _, _ ] => fail 1
  | _ => idtac
  end
.

Ltac _step_safe :=
  match goal with
  (*** blacklisting ***)
  (* | [ |- (gpaco5 (_sim_itree wf) _ _ _ _ (_, trigger (Choose _) >>= _) (_, ?i_tgt)) ] => idtac *)
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, triggerUB >>= _) (_, _)) ] =>
    unfold triggerUB; ired_l; _step; done
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|unfold triggerUB; ired_both; _force_l; ss; fail]
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, assume ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    ired_both; apply sim_itreeC_spec; eapply sim_itreeC_take_src; intro name

  (*** blacklisting ***)
  (* | [ |- (gpaco5 (_sim_itree wf) _ _ _ _ (_, _) (_, trigger (Take _) >>= _)) ] => idtac *)
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, triggerNB >>= _) (_, _)) ] =>
    unfold triggerNB; ired_r; _step; done
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, unwrapN ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|unfold triggerNB; ired_both; _force_r; ss; fail]
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, guarantee ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    ired_both; apply sim_itreeC_spec; eapply sim_itreeC_choose_tgt; intro name
 
  (*** blacklisting ***)
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, trigger (Call _ _) >>= _) (_, _)) ] =>
    try (eapply safe_sim_sim; econs 2); try (eapply safe_sim_sim; econs 5); try (eapply safe_sim_sim; econs 6); try (eapply safe_sim_sim; econs 9) 

  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, trigger (Call _ _) >>= _)) ] =>
    try (eapply safe_sim_sim; econs 2); try (eapply safe_sim_sim; econs 4); try (eapply safe_sim_sim; econs 7); try (eapply safe_sim_sim; econs 8) 

  | _ => (*** default ***)
    eapply safe_sim_sim; econs; i
  end;
  match goal with
  | [ |- exists (_: unit), _ ] => esplits; [eauto|..]; i
  | [ |- exists _, _ ] => fail 1
  | _ => idtac
  end
.


Ltac _steps := repeat ((*** pre processing ***) prep; try _step; (*** post processing ***) simpl).
Ltac steps := repeat ((*** pre processing ***) prep; try _step; (*** post processing ***) simpl; des_ifs_safe).

Ltac _steps_safe := repeat ((*** pre processing ***) prep; try _step_safe; (*** post processing ***) simpl).
Ltac steps_safe := repeat ((*** pre processing ***) prep; try _step_safe; (*** post processing ***) simpl; des_ifs_safe).

Ltac force_l := _force_l.
Ltac force_r := _force_r.



Notation "wf n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' src1 '------------------------------------------------------------------' src2 tgt2"
  :=
    (gpaco8 (_sim_itree wf _ _ _) _ _ _ _ _ _ _ _ n ((Any.pair src0 src1), src2) (tgt0, tgt2))
      (at level 100,
       format "wf  n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' src1 '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' ").

Notation "wf n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' src1 tgt1 '------------------------------------------------------------------' src2 tgt2"
  :=
    (gpaco8 (_sim_itree wf _ _ _) _ _ _ _ _ _ _ _ n ((Any.pair src0 src1), src2) ((Any.pair tgt0 tgt1), tgt2))
      (at level 100,
       format "wf  n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' src1 '//' tgt1 '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' ").

Notation "wf n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' '------------------------------------------------------------------' src2 tgt2"
  :=
    (gpaco8 (_sim_itree wf _ _ _) _ _ _ _ _ _ _ _ n (src0, src2) (tgt0, tgt2))
      (at level 100,
       format "wf  n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' ").

