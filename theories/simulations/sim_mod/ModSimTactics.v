Require Import Common.
Require Import Mod.
Require Import ModSim.

Set Implicit Arguments.

#[export] Hint Resolve sim_itree_mon : paco.
#[export] Hint Resolve cpn8_wcompat : paco.



Ltac ired_l := try (prw _red_gen 2 1 0).
Ltac ired_r := try (prw _red_gen 1 1 0).

Ltac ired_both := ired_l; ired_r.

Ltac prep := ired_both.
  
Ltac _force_l :=
  prep;
  match goal with
  | [ |- (gpaco9 (_sim_itree _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, unwrapN ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco9 (_sim_itree _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, guarantee ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_both; apply sim_itreeC_spec; eapply sim_itree_choose_src; [exists name]|contradict name]; cycle 1

  | [ |- (gpaco9 (_sim_itree _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, ITree.bind (interp _ guarantee ?P) _ (_, _))) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_both; apply sim_itreeC_spec; eapply sim_itree_choose_src; [exists name]|contradict name]; cycle 1

   (* TODO : handle interp_hCallE_tgt better and remove this case *)
  | [ |- (gpaco9 (_sim_itree _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, ITree.bind (interp _ (guarantee ?P )) _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_both; apply sim_itreeC_spec; eapply sim_itree_choose_src; [exists name]|contradict name]; cycle 1; clear name

  | [ |- (gpaco9 (_sim_itree _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_tgt; apply sim_itreeC_spec; econs; unseal i_tgt
  end
.

Ltac _force_r :=
  prep;
  match goal with
  | [ |- (gpaco9 (_sim_itree _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, _) (_, unwrapU ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco9 (_sim_itree _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, _) (_, assume ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    destruct (classic P) as [name|name]; [ired_both; apply sim_itreeC_spec; eapply sim_itree_take_tgt; [exists name]|contradict name]; cycle 1

  | [ |- (gpaco9 (_sim_itree _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_src; apply sim_itreeC_spec; econs; unseal i_src
  end
.

Ltac _step :=
  match goal with
  (*** blacklisting ***)
  (* | [ |- (gpaco5 (_sim_itree wf) _ _ _ _ (_, trigger (Choose _) >>= _) (_, ?i_tgt)) ] => idtac *)
  | [ |- (gpaco9 (_sim_itree _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, triggerUB >>= _) (_, _)) ] =>
    unfold triggerUB; ired_l; _step; done
  | [ |- (gpaco9 (_sim_itree _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|unfold triggerUB; ired_both; _force_l; ss; fail]
  | [ |- (gpaco9 (_sim_itree _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, assume ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    ired_both; apply sim_itreeC_spec; eapply sim_itree_take_src; intro name

  (*** blacklisting ***)
  (* | [ |- (gpaco5 (_sim_itree wf) _ _ _ _ (_, _) (_, trigger (Take _) >>= _)) ] => idtac *)
  | [ |- (gpaco9 (_sim_itree _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, triggerNB >>= _) (_, _)) ] =>
    unfold triggerNB; ired_r; _step; done
  | [ |- (gpaco9 (_sim_itree _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, _) (_, unwrapN ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|unfold triggerNB; ired_both; _force_r; ss; fail]
  | [ |- (gpaco9 (_sim_itree _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, _) (_, guarantee ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    ired_both; apply sim_itreeC_spec; eapply sim_itree_choose_tgt; intro name
 
  | _ => (*** default ***)
    ired_both; apply sim_itreeC_spec; econs; i
    (* eapply safe_sim_sim; econs; i *)
  end;
  match goal with
  | [ |- exists (_ : unit), _ ] => esplits; [eauto|..]; i
  | [ |- exists _, _ ] => fail 1
  | _ => idtac
  end
.

Ltac steps := (hrepeat do 1 (*** pre processing ***) prep; _step; (*** post processing ***) simpl; des_ifs_safe); prep.
Ltac step := ((*** pre processing ***) prep; _step; (*** post processing ***) simpl; des_ifs_safe).

Ltac force_l := _force_l.
Ltac force_r := _force_r.

Tactic Notation "hide" constr(tm) integer(occ) :=
  let tmp := fresh "tmp" in let TMP := fresh "TMP" in
  set (xxx := tm) at occ; remember xxx as tmp eqn : TMP;
  unfold xxx in *; clear xxx; guardH TMP.
Ltac unhide :=
  unguard; subst.

Notation "'☏' wf n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' src1 '------------------------------------------------------------------' src2 tgt2"
  :=
    (gpaco9 (_sim_itree wf _ _ _ _ _) _ _ _ _ _ _ _ _ _ n ((Any.pair src0 src1), src2) (tgt0, tgt2))
      (at level 100, only printing,
       format "'☏' wf n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' src1 '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' ").

Notation "'☏' wf n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' src1 tgt1 '------------------------------------------------------------------' src2 tgt2"
  :=
    (gpaco9 (_sim_itree wf _ _ _ _ _) _ _ _ _ _ _ _ _ _ n ((Any.pair src0 src1), src2) ((Any.pair tgt0 tgt1), tgt2))
      (at level 100, only printing,
       format "'☏' wf n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' src1 '//' tgt1 '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' ").

Notation "'☏' wf n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' '------------------------------------------------------------------' src2 tgt2"
  :=
    (gpaco9 (_sim_itree wf _ _ _ _ _) _ _ _ _ _ _ _ _ _ n (src0, src2) (tgt0, tgt2))
      (at level 100, only printing,
       format "'☏' wf n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' ").

