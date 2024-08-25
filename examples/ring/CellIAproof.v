Require Import Coqlib ITreelib sflib.
Require Import SMod ModSim.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM IPM IFacts.
Require Import Events Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import STB.

Require Import ISim HMod Events.
Require Import Mod ModSimFacts.
Require Import CellHeader CellASpec CellA CellI.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module CellIA.
Section SIMMODSEM.
  Context `{Σ: GRA.t}.
  Context `{_M: CellRA.t (Σ:=Σ)}.

  Variable idx: nat.
  
  Variable StbG: Sk.t -> gname -> option fspec.
  (* Hypothesis CellInStb: forall sk, stb_incl (CellAS.Stb idx) (StbG sk). *)

  Import CellAS.

  Lemma pending_unique:
    pending idx -∗ pending idx -∗ False%I.
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H" as WF. exfalso.
    rr in WF. ur in WF. unseal "ra". des. ur in WF. specialize (WF idx).
    unfold CellAS.pending_r in WF. des_ifs. apply Excl.wf in WF. ss.
  Qed.

  Lemma cell_unique v v':
    cell idx v -∗ cell idx v' -∗ False%I.
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
  Admitted.

  Lemma cell_auth_get v v':
    cell idx v' -∗ auth idx v -∗ ⌜v = v'⌝%I.
  Proof.
  Admitted.

  Lemma cell_auth_set v v':
    cell idx v -∗ auth idx v -∗ |==> cell idx v' ∗ auth idx v'.
  Proof.
  Admitted.

  Definition Ist: Sk.t -> alist key Any.t -> alist key Any.t -> iProp :=
    (fun _ st_src st_tgt =>
       ∃vany v, ⌜st_tgt = [(CellI.v_cv idx, vany)]⌝ ∗
       ((cell idx v ∗ auth idx v)
        ∨
        (⌜vany = v↑⌝ ∗ pending idx ∗ auth idx v)))%I.

  Local Notation CellIMod := (CellI.t idx).
  Local Notation CellAMod := (CellA.t idx StbG).

  Lemma simF_get:
    HModR.sim_fun CellAMod CellIMod Ist (CellName.get idx).
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "((% & C) & %)".
    subst. hss. rename q into v. unfold Ist.
    iDestruct "IST" as (vany v0) "(% & [(C' & A)|(% & P & A)])".
    { iExFalso. iApply (cell_unique with "C' C"). }
    subst. hss.

    iPoseProof (cell_auth_get with "C A") as "%". subst.

    steps_r. hss. steps_r.    
    apc_l. steps_l.
    force_l. steps_l. force_l. force_l.
    iSplitL "C". { eauto. }

    step. iSplitL; [|eauto].
    iExists _, _. iSplitL ""; eauto. iRight. iFrame; eauto.
  Qed.
  
  Lemma simF_set:
    HModR.sim_fun CellAMod CellIMod Ist (CellName.set idx).
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "((% & [P|C]) & %)";
      subst; hss; rename q0 into v, q1 into v'; unfold Ist.
    { iDestruct "IST" as (vany v0) "(% & [(C & A)|(% & P' & A)])"; cycle 1.
      { iExFalso. iApply (pending_unique with "P' P"). }
      des; subst. hss.
      
      iMod (cell_auth_set with "C A") as "(C & A)".

      steps_r. hss.
      apc_l. steps_l. force_l. steps_l. force_l. force_l.
      iSplitL "C". { eauto. }

      step.
      iSplitL; eauto.
      iExists _, _. iSplitL ""; eauto. iRight. iFrame; eauto.
    }

    iDestruct "IST" as (vany v0) "(% & [(C' & A)|(% & P & A)])".
    { iExFalso. iApply (cell_unique with "C' C"). }
    subst. hss.

    iPoseProof (cell_auth_get with "C A") as "%". subst.
    iMod (cell_auth_set with "C A") as "(C & A)".

    steps_r. hss.
    apc_l. steps_l. force_l. steps_l. force_l. force_l.
    iSplitL "C". { eauto. }

    step.
    iSplitL; [|eauto].
    iExists _, _. iSplitL ""; eauto. iRight. iFrame; eauto.
  Qed.

  Theorem sim: HModR.sim CellAMod CellIMod (CellA.InitCond idx) Ist.
  Proof.
    init_sim.
    - iIntros "H". iDestruct "H" as (v) "(C & A)".
      repeat iExists _. iSplitL ""; eauto. iLeft. iFrame.
    - apply simF_get.
    - apply simF_set.
  Qed.

End SIMMODSEM.
End CellIA.
