Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM IPM IFacts.
Require Import Events Behavior.
Require Import Relation_Definitions.

(*** TODO : export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import STB.

Require Import ISim ITactics SMod HMod PMod Events.
Require Import Mod ModSim ModSimFacts.
Require Import CellHeader CellASpec CellA CellI.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module CellIA.
Section SIMMODSEM.
  Context `{Σ : GRA.t}.
  Context `{_M : CellRA.t (Σ:=Σ)}.

  Variable idx : nat.

  Variable GI : Sk.t -> invspec.
  Variable StbG : Sk.t -> gname -> option fspec.
  (* Hypothesis CellInStb : forall sk, stb_incl (CellAS.Stb idx) (StbG sk). *)

  Import CellAS.

  Lemma pending_unique:
    pending idx -∗ pending idx -∗ False%I.
  Proof.
    unfold pending. unseal "ccr". unfold pending_r.
    iIntros "H0 H1". iCombine "H0 H1" as "H". iOwnWf "H" as WF. exfalso.
    rr in WF. ur in WF. unseal "ra". des. ur in WF. specialize (WF idx).
    des_ifs. apply Excl.wf in WF. ss.
  Qed.

  Lemma cell_unique v v':
    cell idx v -∗ cell idx v' -∗ False%I.
  Proof.
    unfold cell, auth. unseal "ccr". unfold cell_r, cellraw_r.
    iIntros "H0 H1". iCombine "H0 H1" as "H". iOwnWf "H" as WF. exfalso.
    rr in WF. ur in WF. unseal "ra". des. ur in WF0.
    ur in WF0. specialize (WF0 idx). ur in WF0. des_ifs.
  Qed.

  Lemma cell_auth_get v v':
    cell idx v' -∗ auth idx v -∗ ⌜v = v'⌝%I.
  Proof.
    unfold cell, auth. unseal "ccr". unfold cell_r, auth_r, cellraw_r.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H" as WF. iPureIntro. rr in WF. ur in WF. unseal "ra". des.
    rr in WF0. ur in WF0. unseal "ra". des.
    rr in WF0. des. ur in WF0. eapply equal_f with (x:=idx) in WF0.
    ur in WF0. des_ifs.
  Qed.

  Lemma cell_auth_set v v':
    cell idx v -∗ auth idx v -∗ |==> cell idx v' ∗ auth idx v'.
  Proof.
    unfold cell, auth. unseal "ccr".
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iPoseProof (OwnM_Upd with "H") as "H".
    { instantiate (1:= (cell_r idx v') ⋅ (auth_r idx v')).
      unfold cell_r, auth_r, cellraw_r.
      rr. intros ctx WF. ur in WF. ur. unseal "ra". des_ifs. des. split; auto.
      ur in WF0. ur. des_ifs. des. rr in WF0. des. split.
      { rr. exists ctx. ur in WF0. ur. extensionality n.
        eapply equal_f with (x:=n) in WF0. ur in WF0. ur.
        des_ifs; rewrite ->?fn_lookup_insert, ?fn_lookup_insert_ne; eauto.
      }
      { ur. i. rr. ur. unseal "ra". des_ifs. }
    }
    iMod "H". iDestruct "H" as "[H0 H1]". iFrame. auto.
  Qed.

  Definition Ist : Sk.t -> nat -> alist key Any.t -> alist key Any.t -> iProp :=
    (fun _ _ st_src st_tgt =>
       ∃vany v, ⌜st_tgt = [(CellI.v_cv idx, vany)]⌝ ∗
       ((cell idx v ∗ auth idx v)
        ∨
        (⌜vany = v↑⌝ ∗ pending idx ∗ auth idx v)))%I.

  Local Notation CellI := (CellI.t idx).
  Local Notation CellA := (CellA.t idx GI StbG).

  Lemma simF_get:
    HSim.sim_fun CellA CellI Ist (CellName.get idx).
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "((% & C) & %)". subst. hss.
    iDestruct "IST" as (vany v0) "(% & [(C' & A)|(% & P & A)])".
    { iExFalso. iApply (cell_unique with "C' C"). }
    subst. hss. rename q into v.

    iPoseProof (cell_auth_get with "C A") as "%". subst.

    steps_r. hss. steps_r.    
    forces_l. steps_l. forces_l.
    iSplitL "C". { eauto. }

    step. iSplit; eauto.
    iExists _, _. iSplit; eauto. iRight. iFrame; eauto.
  Qed.

  Lemma simF_set:
    HSim.sim_fun CellA CellI Ist (CellName.set idx).
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "((% & [P|C]) & %)";
      subst; hss; rename z into v, z0 into v'; unfold Ist.
    { iDestruct "IST" as (vany v0) "(% & [(C & A)|(% & P' & A)])"; cycle 1.
      { iExFalso. iApply (pending_unique with "P' P"). }
      des; subst. hss.

      iMod (cell_auth_set with "C A") as "(C & A)".

      steps_r. hss.
      forces_l. steps_l. forces_l.
      iSplitL "C". { eauto. }

      step.
      iSplit; eauto.
      iExists _, _. iSplit; eauto. iRight. iFrame; eauto.
    }

    iDestruct "IST" as (vany v0) "(% & [(C' & A)|(% & P & A)])".
    { iExFalso. iApply (cell_unique with "C' C"). }
    subst. hss.

    iPoseProof (cell_auth_get with "C A") as "%". subst.
    iMod (cell_auth_set with "C A") as "(C & A)".

    steps_r. hss.
    forces_l. steps_l. forces_l.
    iSplitL "C". { eauto. }

    step.
    iSplit; eauto.
    iExists _, _. iSplit; eauto. iRight. iFrame; eauto.
  Qed.

  Theorem sim : HSim.t CellA CellI (CellA.InitCond idx) Ist.
  Proof.
    init_sim.
    - iIntros "H". iDestruct "H" as (v) "(C & A)".
      repeat iExists _. iSplit; eauto. iLeft. iFrame.
    - apply simF_get.
    - apply simF_set.
  Qed.

End SIMMODSEM.
End CellIA.
