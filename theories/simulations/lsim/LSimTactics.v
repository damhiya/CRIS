Require Import Common.
Require Import LMod.
Require Import LSim.

Set Implicit Arguments.

#[export] Hint Resolve lsim_mon : paco.
#[export] Hint Resolve cpn8_wcompat : paco.



Ltac ired_s := try (prw _red_gen 2 1 0).
Ltac ired_t := try (prw _red_gen 1 1 0).

Ltac ired_both := ired_s; ired_t.

Ltac prep := ired_both.
  
Ltac _force_s :=
  prep;
  match goal with
  | [ |- (gpaco9 (_lsim _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, unwrapN ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco9 (_lsim _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, guarantee ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_both; apply lsimC_spec; eapply lsim_choose_src; [exists name]|contradict name]; cycle 1

  | [ |- (gpaco9 (_lsim _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, ITree.bind (interp _ guarantee ?P) _ (_, _))) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_both; apply lsimC_spec; eapply lsim_choose_src; [exists name]|contradict name]; cycle 1

   (* TODO : handle interp_hCallE_tgt better and remove this case *)
  | [ |- (gpaco9 (_lsim _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, ITree.bind (interp _ (guarantee ?P )) _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_both; apply lsimC_spec; eapply lsim_choose_src; [exists name]|contradict name]; cycle 1; clear name

  | [ |- (gpaco9 (_lsim _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_tgt; apply lsimC_spec; econs; unseal i_tgt
  end
.

Ltac _force_t :=
  prep;
  match goal with
  | [ |- (gpaco9 (_lsim _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, _) (_, unwrapU ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco9 (_lsim _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, _) (_, assume ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    destruct (classic P) as [name|name]; [ired_both; apply lsimC_spec; eapply lsim_take_tgt; [exists name]|contradict name]; cycle 1

  | [ |- (gpaco9 (_lsim _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_src; apply lsimC_spec; econs; unseal i_src
  end
.

Ltac _step :=
  match goal with
  (*** blacklisting ***)
  (* | [ |- (gpaco5 (_lsim wf) _ _ _ _ (_, trigger (Choose _) >>= _) (_, ?i_tgt)) ] => idtac *)
  | [ |- (gpaco9 (_lsim _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, triggerUB >>= _) (_, _)) ] =>
    unfold triggerUB; ired_s; _step; done
  | [ |- (gpaco9 (_lsim _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|unfold triggerUB; ired_both; _force_s; ss; fail]
  | [ |- (gpaco9 (_lsim _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, assume ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    ired_both; apply lsimC_spec; eapply lsim_take_src; intro name

  (*** blacklisting ***)
  (* | [ |- (gpaco5 (_lsim wf) _ _ _ _ (_, _) (_, trigger (Take _) >>= _)) ] => idtac *)
  | [ |- (gpaco9 (_lsim _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, triggerNB >>= _) (_, _)) ] =>
    unfold triggerNB; ired_t; _step; done
  | [ |- (gpaco9 (_lsim _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, _) (_, unwrapN ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|unfold triggerNB; ired_both; _force_t; ss; fail]
  | [ |- (gpaco9 (_lsim _ _ _ _ _ _) _ _ _ _ _ _ _ _ _ _ (_, _) (_, guarantee ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    ired_both; apply lsimC_spec; eapply lsim_choose_tgt; intro name
 
  | _ => (*** default ***)
    ired_both; apply lsimC_spec; econs; i
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

Ltac force_s := _force_s.
Ltac force_t := _force_t.

Tactic Notation "hide" constr(tm) integer(occ) :=
  let tmp := fresh "tmp" in let TMP := fresh "TMP" in
  set (xxx := tm) at occ; remember xxx as tmp eqn : TMP;
  unfold xxx in *; clear xxx; guardH TMP.
Ltac unhide :=
  unguard; subst.

Notation "'☏--' wf '--' n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' src1 '------------------------------------------------------------------' src2 tgt2"
  :=
    (gpaco9 (_lsim _ _ wf _ _ _) _ _ _ _ _ _ _ _ _ n ((Any.pair src0 src1), src2) (tgt0, tgt2))
      (at level 100, only printing,
       format "'☏--' wf '--' n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' src1 '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' ").

Notation "'☏--' wf '--' n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' src1 tgt1 '------------------------------------------------------------------' src2 tgt2"
  :=
    (gpaco9 (_lsim _ _ wf _ _ _) _ _ _ _ _ _ _ _ _ n ((Any.pair src0 src1), src2) ((Any.pair tgt0 tgt1), tgt2))
      (at level 100, only printing,
       format "'☏--' wf '--' n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' src1 '//' tgt1 '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' ").

Notation "'☏--' wf '--' n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' '------------------------------------------------------------------' src2 tgt2"
  :=
    (gpaco9 (_lsim _ _ wf _ _ _) _ _ _ _ _ _ _ _ _ n (src0, src2) (tgt0, tgt2))
      (at level 100, only printing,
       format "'☏--' wf '--' n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' ").

