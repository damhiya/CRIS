Require Import Coqlib ITreelib sflib.
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

Require Import ISim ITactics SMod HMod PMod Events.
Require Import Mod ModSim ModSimFacts.
Require Import CellioHeader CellioA CellioI.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module CellioIA.
Module CellioIA.
  Context `{Σ: GRA.t}.
  Context `{_M: CellioRA.t (Σ:=Σ)}.

  Variable GI: Sk.t -> invspec.
  Variable StbG: Sk.t -> gname -> option fspec.

  Import CellioR.

  Lemma cell_unique v v':
    cell v -∗ cell v' -∗ False%I.
  Proof.
    unfold cell, auth. unseal "ccr". unfold cell_r, cellraw_r.
    iIntros "H0 H1". iCombine "H0 H1" as "H". iOwnWf "H" as WF. exfalso.
    rr in WF. ur in WF. unseal "ra". ur in WF. des_ifs.
  Qed.

  Lemma cell_auth_get v v':
    cell v' -∗ auth v -∗ ⌜v = v'⌝%I.
  Proof.
    unfold cell, auth. unseal "ccr". unfold cell_r, auth_r, cellraw_r.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H" as WF. iPureIntro. rr in WF. ur in WF. unseal "ra". des.
    rr in WF. des. ur in WF. des_ifs.
  Qed.

  Lemma cell_auth_set v v':
    cell v -∗ auth v -∗ |==> cell v' ∗ auth v'.
  Proof.
    unfold cell, auth. unseal "ccr".
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iPoseProof (OwnM_Upd with "H") as "H".
    { instantiate (1:= (cell_r v') ⋅ (auth_r v')).
      unfold cell_r, auth_r, cellraw_r.
      rr. intros ctx WF. unseal "ra".
      ur in WF. ur. des_ifs. des. rr in WF. des. split.
      { rr. exists ctx. ur in WF. ur. 
        des_ifs; rewrite ->?fn_lookup_insert, ?fn_lookup_insert_ne; eauto.
      }
      { rr. ur. unseal "ra". des_ifs. }
    }
    iMod "H". iDestruct "H" as "[H0 H1]". iFrame. auto.
  Qed.

  Definition Ist: Sk.t -> nat -> alist key Any.t -> alist key Any.t -> iProp :=
    (fun _ _ st_src st_tgt =>
       ∃ v, ⌜st_tgt = [(CellioI.v_cv, v↑)]⌝ ∗ auth v)%I.

  Local Notation CellioI := (CellioI.t).
  Local Notation CellioA := (CellioA.t GI StbG).

  Lemma simF_set:
    HSim.sim_fun CellioA CellioI Ist CellioName.set.
  Proof.
    init_simF. unfold CellioI.set.

    steps_l. iDestruct "ASM" as "%"; subst.
    iDestruct "IST" as (v) "(% & AUTH)". subst.

    step.

    iPoseProof (cell_auth_get with "ASM' AUTH") as "%"; subst.
    iMod (cell_auth_set with "ASM' AUTH") as "(C & A)".

    steps_r. hss. steps_l. forces_l.
    iSplitL "C"; eauto.
    
    steps_l. forces_l.
    iSplitL ""; eauto.

    step.
    iSplitL ""; eauto.
    iExists _. iFrame. eauto.
  Qed.
  
  Lemma simF_get:
    HSim.sim_fun CellioA CellioI Ist CellioName.get.
  Proof.
    init_simF. unfold CellioI.get.

    steps_l. iDestruct "ASM" as "%"; subst.
    iDestruct "IST" as (v) "(% & AUTH)". subst.

    iPoseProof (cell_auth_get with "ASM' AUTH") as "%"; subst.

    steps_r. hss. steps_r. forces_l.
    iSplitL "ASM'"; eauto.
    
    steps_l. forces_l.
    iSplitL ""; eauto.

    step.
    iSplitL ""; eauto.
    iExists _. iFrame. eauto.
  Qed.
  
  Theorem sim: HSim.t CellioA CellioI CellioA.InitCond Ist.
  Proof.
    init_sim.
    - iIntros "H". iExists _. iFrame. eauto.
    - apply simF_set.
    - apply simF_get.
  Qed.

End CellioIA.
End CellioIA.
