Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef.
Require Import ModSim.
Require Import STB.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
Require Import Red IRed.
Require Import ProofMode.
Require Import Invariant.

Require Import HPSim.

Set Implicit Arguments.

#[export] Hint Resolve _hpsim_mon: paco.
#[export] Hint Resolve cpn7_wcompat: paco.




(********************************* DEPRECATED *******************************************)


Section SIM.
  Context `{Σ: GRA.t}.

  Variable fl_src: alist gname (Any.t -> itree hAGEs Any.t).
  Variable fl_tgt: alist gname (Any.t -> itree hAGEs Any.t).
  Variable I: Any.t -> Any.t -> iProp.

  Variant _safe_hpsim
    (hpsim: forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop)
    {R} {RR: Any.t * R -> Any.t * R -> iProp}: bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop := 
  | safe_hpsim_ret
      p_src p_tgt st_src st_tgt fmr
      v_src v_tgt
      (* Note: (INV: Own fmr ⊢ #=> I st_src st_tgt) is required only for the funtion end. *)
      (RET: Own fmr ⊢ #=> RR (st_src,v_src) (st_tgt,v_tgt))
    :
      _safe_hpsim hpsim p_src p_tgt (st_src, Ret v_src) (st_tgt, Ret v_tgt) fmr
  | safe_hpsim_call
      p_src p_tgt st_src st_tgt fmr
      fn varg k_src k_tgt FR
      (INV: Own fmr ⊢ #=> (I st_src st_tgt ∗ FR))
      (K: forall vret st_src0 st_tgt0 fmr0 
          (WF: URA.wf fmr0)
          (INV: Own fmr0 ⊢ #=> (I st_src0 st_tgt0 ∗ FR)),
          hpsim _ RR true true (st_src0, k_src vret) (st_tgt0, k_tgt vret) fmr0)				
    :
      _safe_hpsim hpsim p_src p_tgt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, trigger (Call fn varg) >>= k_tgt) fmr
  | safe_hpsim_syscall
      p_src p_tgt st_src st_tgt fmr
      fn varg rvs k_src k_tgt
      (K: forall vret, 
          hpsim _ RR true true (st_src, k_src vret) (st_tgt, k_tgt vret) fmr)
    :
      _safe_hpsim hpsim p_src p_tgt (st_src, trigger (Syscall fn varg rvs) >>= k_src) (st_tgt, trigger (Syscall fn varg rvs) >>= k_tgt) fmr

  | safe_hpsim_tau_src
      p_src p_tgt st_src st_tgt fmr
      i_src i_tgt
      (K: hpsim _ RR true p_tgt (st_src, i_src) (st_tgt, i_tgt) fmr)
    :
      _safe_hpsim hpsim p_src p_tgt (st_src, tau;; i_src) (st_tgt, i_tgt) fmr

  | safe_hpsim_tau_tgt
      p_src p_tgt st_src st_tgt fmr
      i_src i_tgt
      (K: hpsim _ RR p_src true (st_src, i_src) (st_tgt, i_tgt) fmr)
    :
      _safe_hpsim hpsim p_src p_tgt (st_src, i_src) (st_tgt, tau;; i_tgt) fmr

  | safe_hpsim_choose_tgt
      p_src p_tgt st_src st_tgt fmr
      X i_src k_tgt
      (K: forall (x: X), hpsim _ RR p_src true (st_src, i_src) (st_tgt, k_tgt x) fmr)
    :
      _safe_hpsim hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (Choose X) >>= k_tgt) fmr

  | safe_hpsim_take_src
      p_src p_tgt st_src st_tgt fmr
      X k_src i_tgt
      (K: forall (x: X), hpsim _ RR true p_tgt (st_src, k_src x) (st_tgt, i_tgt) fmr)
    :
      _safe_hpsim hpsim p_src p_tgt (st_src, trigger (Take X) >>= k_src) (st_tgt, i_tgt) fmr

  | safe_hpsim_supdate_src
      p_src p_tgt st_src st_tgt fmr
      X x st_src0 k_src i_tgt
      (run: Any.t -> Any.t * X)
      (RUN: run st_src = (st_src0, x))
      (K: hpsim _ RR true p_tgt (st_src0, k_src x) (st_tgt, i_tgt) fmr)
    :
      _safe_hpsim hpsim p_src p_tgt (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt) fmr

  | safe_hpsim_supdate_tgt
      p_src p_tgt st_src st_tgt fmr
      X x st_tgt0 i_src k_tgt
      (run: Any.t -> Any.t * X)
      (RUN: run st_tgt = (st_tgt0, x))
      (K: hpsim _ RR p_src true (st_src, i_src) (st_tgt0, k_tgt x) fmr)
    :
      _safe_hpsim hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt) fmr

  | safe_hpsim_assume_src
      p_src p_tgt st_src st_tgt fmr
      iP k_src i_tgt FMR
      (CUR: Own fmr ⊢ #=> FMR)
      (K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> (iP ∗ FMR)),
          hpsim _ RR true p_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
    :
      _safe_hpsim hpsim p_src p_tgt (st_src, trigger (Assume iP) >>= k_src) (st_tgt, i_tgt) fmr

  | safe_hpsim_guarantee_tgt
      p_src p_tgt st_src st_tgt fmr
      iP i_src k_tgt FMR
      (CUR: Own fmr ⊢ #=> FMR)
      (K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> (iP ∗ FMR)),
          hpsim _ RR p_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0)
    :
    _safe_hpsim hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (Guarantee iP) >>= k_tgt) fmr
  .


  Lemma safe_hpsim_spec:
    _safe_hpsim <8= gupaco7 (@_hpsim Σ fl_src fl_tgt I false) (cpn7 (@_hpsim Σ fl_src fl_tgt I false)).
  Proof.
    i. eapply hpsimC_spec. depdes PR; try by (econs; et).
  Qed.

End SIM.

(* TACTICS *)

Context `{Σ: GRA.t}.


Ltac hp_ired_l := try (prw _red_gen 3 1 0).
Ltac hp_ired_r := try (prw _red_gen 2 1 0).

Ltac hprep := hp_ired_l; hp_ired_r.

Ltac _hp_force_l :=
  hprep;
  match goal with
  | [ |- (gpaco7 (_hpsim _ _ _) _ _ _ _ _ _ _ (_, unwrapN ?ox >>= _) (_, _) _) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco7 (_hpsim _ _ _) _ _ _ _ _ _ _ (_, guarantee ?P >>= _) (_, _) _) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [hprep; guclo hpsimC_spec; eapply hpsimC_choose_src; [exists name]|contradict name]; cycle 1

  | [ |- (gpaco7 (_hpsim _ _ _) _ _ _ _ _ _ _ (_, ITree.bind (interp _ guarantee ?P) _ (_, _)) (_, _) _) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [hprep; guclo hpsimC_spec; eapply hpsimC_choose_src; [exists name]|contradict name]; cycle 1

   (* TODO: handle interp better and remove this case *)
  | [ |- (gpaco7 (_hpsim _ _ _) _ _ _ _ _ _ _ (_, ITree.bind (interp _ (guarantee ?P )) _) (_, _) _) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [hprep; guclo hpsimC_spec; eapply hpsimC_choose_src; [exists name]|contradict name]; cycle 1; clear name

  | [ |- (gpaco7 (_hpsim _ _ _) _ _ _ _ _ _ _ (_, ?i_src) (_, ?i_tgt) _) ] =>
    seal i_tgt; guclo hpsimC_spec; econs; unseal i_tgt
  end
.

Ltac _hp_force_r :=
  hprep;
  match goal with
  | [ |- (gpaco7 (_hpsim _ _ _) _ _ _ _ _ _ _ (_, _) (_, unwrapU ?ox >>= _) _) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco7 (_hpsim _ _ _) _ _ _ _ _ _ _ (_, _) (_, assume ?P >>= _) _) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    destruct (classic P) as [name|name]; [hprep; guclo hpsimC_spec; eapply hpsimC_take_tgt; [exists name]|contradict name]; cycle 1

  | [ |- (gpaco7 (_hpsim _ _ _) _ _ _ _ _ _ _ (_, ?i_src) (_, ?i_tgt) _) ] =>
    seal i_src; guclo hpsimC_spec; econs; unseal i_src
  end
.

Ltac _hp_step :=
  match goal with
  (*** blacklisting ***)
  | [ |- (gpaco7 (_hpsim _ _ _) _ _ _ _ _ _ _ (_, triggerUB >>= _) (_, _) _) ] =>
    unfold triggerUB; hp_ired_l; _hp_step; done
  | [ |- (gpaco7 (_hpsim _ _ _) _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) (_, _) _) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|unfold triggerUB; hprep; _hp_force_l; ss; fail]
  | [ |- (gpaco7 (_hpsim _ _ _) _ _ _ _ _ _ _ (_, assume ?P >>= _) (_, _) _) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    hprep; guclo hpsimC_spec; eapply hpsimC_take_src; intro name

  (*** blacklisting ***)
  | [ |- (gpaco7 (_hpsim _ _ _) _ _ _ _ _ _ _ (_, triggerNB >>= _) (_, _) _) ] =>
    unfold triggerNB; hp_ired_r; _hp_step; done
  | [ |- (gpaco7 (_hpsim _ _ _) _ _ _ _ _ _ _ (_, _) (_, unwrapN ?ox >>= _) _) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|unfold triggerNB; hprep; _hp_force_r; ss; fail]
  | [ |- (gpaco7 (_hpsim _ _ _) _ _ _ _ _ _ _ (_, _) (_, guarantee ?P >>= _) _) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    hprep; guclo hpsimC_spec; eapply hpsimC_choose_tgt; intro name
 
  | _ => (*** default ***)
    guclo safe_hpsim_spec; econs; i
  end;
  match goal with
  | [ |- exists (_: Σ), _ ] => esplits; [eauto|..]; i
  | [ |- exists _, _ ] => fail 1
  | _ => idtac
  end
.

Ltac _hp_steps := repeat ((*** pre processing ***) hprep; try _hp_step; (*** post processing ***) simpl).
Ltac hsteps := repeat ((*** pre processing ***) hprep; try _hp_step; (*** post processing ***) simpl; des_ifs_safe).

Ltac hforce_l := _hp_force_l.
Ltac hforce_r := _hp_force_r.

Ltac inline_l := try (guclo hpsimC_spec; eapply hpsimC_inline_src; [et|]).
Ltac inline_r := try (guclo hpsimC_spec; eapply hpsimC_inline_tgt; [et|]).
Ltac inline := inline_l; inline_r.

Section TEST.
  Context `{Σ: GRA.t}.
  Variable srcs0: Any.t.
  Variable tgts0: Any.t.
  Variable I: Any.t -> Any.t -> iProp.

  (* Require Import HTactics. *)

  Definition HRET: itree hAGEs Any.t := Ret tt↑.

  Let fl_src: alist gname (Any.t -> itree hAGEs Any.t) := [("f", (fun (_ :Any.t) => Ret tt↑))].
  Let fl_tgt: alist gname (Any.t -> itree hAGEs Any.t) := [("g", (fun (_ :Any.t) => Ret tt↑))].

  Goal gpaco7 (@_hpsim Σ fl_src fl_tgt I false) (cpn7 (@_hpsim Σ fl_src fl_tgt I false)) bot7 bot7 Any.t (fun _ _ => ⌜True⌝%I) false false
       (srcs0, triggerUB >>= idK) (tgts0, triggerUB >>= idK) ε. 
  Proof. 
    hsteps.
  Qed.

  Goal gpaco7 (@_hpsim Σ fl_src fl_tgt I false) (cpn7 (@_hpsim Σ fl_src fl_tgt I false)) bot7 bot7 Any.t (fun _ _ => ⌜True⌝%I) false false
       (srcs0, triggerNB >>= idK) (tgts0, triggerNB >>= idK) ε.
  Proof.
    hsteps.
  Qed.

  Goal gpaco7 (@_hpsim Σ fl_src fl_tgt I false) (cpn7 (@_hpsim Σ fl_src fl_tgt I false)) bot7 bot7 Any.t (fun _ _ => ⌜True⌝%I) false false
       (srcs0, trigger (Call "f" tt↑) >>= idK) (tgts0, trigger (Call "g" tt↑) >>= idK) ε.
  Proof.
    inline. hsteps. et.
    (* inline_l. inline_r. hsteps. et.  *)
  Qed.

  Section LINKING.
    (* Variable ms0 ms1 mt0 mt1: HMod.t. *)

    Definition mss0: HModSem.t := {|
      HModSem.fnsems := [("f0", (fun _ => Ret tt↑))];
      HModSem.initial_st := tt↑
    |}.

    Definition mss1: HModSem.t := {|
      HModSem.fnsems := [("f1", (fun _ => Ret tt↑)); ("main", (fun _ => trigger (Call "f0" tt↑) >>= (fun _ => trigger (Call "f1" tt↑))))];
      HModSem.initial_st := tt↑
    |}.

    Definition mtt0: HModSem.t := {|
      HModSem.fnsems := [("f0", (fun _ => Ret tt↑))];
      HModSem.initial_st := tt↑
    |}.

    Definition mtt1: HModSem.t := {|
      HModSem.fnsems := [("f1", (fun _ => Ret tt↑)); ("main", (fun _ => trigger (Call "f0" tt↑) >>= (fun _ => trigger (Call "f1" tt↑))))];
      HModSem.initial_st := tt↑
    |}.

    Definition ms0 := {|
      HMod.get_modsem := fun _ => mss0;
      HMod.sk := Sk.unit;
    |}.

    Definition ms1 := {|
      HMod.get_modsem := fun _ => mss1;
      HMod.sk := Sk.unit;
    |}.

    Definition mt0 := {|
      HMod.get_modsem := fun _ => mtt0;
      HMod.sk := Sk.unit;
    |}.

    Definition mt1 := {|
      HMod.get_modsem := fun _ => mtt1;
      HMod.sk := Sk.unit;
    |}.


    Goal HModR.sim (HMod.add ms0 ms1) (HMod.add mt0 mt1).
    Proof.
      econs; ss.
      ii. econs. 
      econs.
      { econs; ss.
        grind. ginit. hsteps. et.  
      }
      econs.
      {
        econs; ss. 
        grind. ginit. hsteps. et. 
      }
      econs; et.
      econs; ss.
      grind. ginit. hprep. inline. hprep. inline. hsteps; et.
      ss. uipropall. refl.
    Qed.

  End LINKING.


  Section MULT.
    Require Import Coqlib.
    Require Import ImpPrelude.
    Require Import Skeleton.
    Require Import PCM.
    Require Import ModSem Behavior.
    Require Import Relation_Definitions.
  
    Require Import MultHeader Mult0 Mult1.
    Require Import Relation_Operators.
    Require Import RelationPairs.
    From ITree Require Import
         Events.MapDefault.
    From ExtLib Require Import
         Core.RelDec
         Structures.Maps
         Data.Map.FMapAList.
    
    Require Import STB ProofMode.
    
    Set Implicit Arguments.
    
    Local Open Scope nat_scope.
    Context `{@GRA.inG fRA Σ}.
    Context `{@GRA.inG gRA Σ}.
    Context `{@GRA.inG hRA Σ}.
  
    Variable GlobalStb: Sk.t -> gname -> option fspec.
    Variable o: ord.
  
    Definition MultH0 := SMod.to_hmod (GlobalStb (Mult0.SMult.(SMod.sk))) o Mult0.SMult.
    Definition MultH1 := SMod.to_hmod (GlobalStb (Mult1.SMult.(SMod.sk))) o Mult1.SMult.
  
    Lemma test_hmod : HModR.sim MultH1 MultH0.
    Proof.
    econs; et. i. econs; cycle 1.
    { instantiate (1:= (fun _ _ => ⌜True⌝%I)). ss. rr. uipropall. }
    remember (HModSemPair.fl_src (HMod.get_modsem MultH1 sk)). clear Heqa.
    remember (HModSemPair.fl_tgt (HMod.get_modsem MultH0 sk)). clear Heqa0.
    econs.
    {
      econs; et. ii; clarify.
      unfold fun_spec_hp, body_spec_hp, interp_hEs_hAGEs. 
      grind.
      ginit. hsteps. unfold hpsim_end. et.  
    }
    econs.
    {
      econs; et. ii; clarify.
      grind. ginit.
      unfold ccallU. grind. unfold fun_spec_hp, body_spec_hp. hsteps.
      rewrite interp_hAGEs_bind. rewrite interp_hAGEs_call. 
      unfold handle_callE_hAGEs. grind.
      unfold unwrapN. des_ifs; hsteps.
      unfold HoareCall. hsteps. grind. { instantiate (1:= ⌜True⌝ ∗ ⌜Any.upcast Vundef = Any.upcast Vundef⌝). et. }
      hforce_l. hsteps. hforce_l. grind. hforce_l; et. 
      hsteps; et.
      hforce_r. hforce_r; et. i. hsteps.
      unfold unwrapU. des_ifs; cycle 1.
      { rewrite !interp_hAGEs_bind. grind. rewrite interp_hAGEs_triggerUB. hsteps. } 
      grind. rewrite !interp_hAGEs_bind. rewrite interp_hAGEs_call.
      unfold handle_callE_hAGEs. grind.
      unfold unwrapN. des_ifs; hsteps.
      unfold HoareCall. hsteps; et.
      hforce_l. hsteps. hforce_l. hsteps. hforce_l; et. i. hsteps; et.
      hforce_r. hforce_r; et. i. hsteps. des_ifs; cycle 1.
      { rewrite interp_hAGEs_bind. grind. rewrite interp_hAGEs_triggerUB. hsteps. } 
      grind. rewrite interp_hAGEs_ret. hsteps.
    }
    econs; et.
    {
      econs; et. ii; clarify.
      grind. ginit.
      unfold fun_spec_hp, body_spec_hp.
      rewrite interp_hAGEs_bind.
      unfold interp_hEs_hAGEs. rewrite interp_trigger. grind.
      unfold HoareAPC. grind.
      hsteps. hforce_l. instantiate (1:= x).
      remember ε as fmr. rewrite Heqfmr in INV. clear Heqfmr.
      remember true. clear Heqb.
      revert fmr x st_src st_tgt b. gcofix CIH. i.
      rewrite !unfold_APC.
      hsteps. hforce_l. instantiate (1:= x0).
      destruct x0.
      { hsteps. et. }
      unfold guarantee. hsteps. hforce_l. hforce_l; et. hsteps. hforce_l. instantiate (1:= (s, t)). hsteps.
      unfold unwrapN. des_ifs; clarify. hsteps.
      unfold HoareCall. hsteps; et. hforce_l. hforce_l. hforce_l; et. i.
      hsteps; et. { instantiate (1:= ⌜True⌝%I). et. }
      hforce_r. hforce_r; et. i. hsteps.
      eapply hpsim_progress_flag.
      gfinal. left. eapply CIH.
    }

  Qed.

  End MULT.

End TEST.