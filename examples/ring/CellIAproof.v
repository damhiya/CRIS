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
  
  Variable StbA: Sk.t -> gname -> option fspec.
  Hypothesis CellInStb: forall sk, stb_incl (to_stb (CellAS.Stb idx)) (StbA sk).

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

  Definition Ist: Any.t -> Any.t -> iProp :=
    (fun st_src st_tgt =>
       ∃ v,
       (cell idx v ∗ auth idx v)
       ∨ 
       (pending idx ∗ auth idx v ∗ ⌜st_tgt = v↑⌝))%I.
  
  Local Notation CellAMod := (CellA.t idx StbA).
  Local Notation CellIMod := (CellI.t idx).

  (* Lemma simF_init: *)
  (*   HModR.sim_fun CellAMod CellIMod Ist (CellName.init idx). *)
  (* Proof. *)
  (*   init_simF. *)

  (*   st_l. iDestruct "ASM" as "((% & P) & %)". *)
  (*   subst. hss. unfold Ist. *)
  (*   iDestruct "IST" as "[(C & A) | (P' & _)]"; des; subst; cycle 1. *)
  (*   { iExFalso. iApply (pending_unique with "P' P"). } *)

  (*   st_r. force_l. st_l. force_l. force_l. *)
  (*   iSplitL "C". *)
  (*   { eauto. } *)

  (*   st. *)
  (*   iSplitL; eauto. *)
  (*   iRight. iFrame. eauto. *)
  (* Qed. *)

  Lemma simF_get:
    HModR.sim_fun CellAMod CellIMod Ist (CellName.get idx).
  Proof.
    init_simF.

    st_l. iDestruct "ASM" as "((% & C) & %)".
    subst. hss. rename y0 into v. unfold Ist.
    iDestruct "IST" as (v')"[(C0 & _)|(P & A & %)]".
    { iExFalso. iApply (cell_unique with "C0 C"). }
    subst. hss.

    iPoseProof (cell_auth_get with "C A") as "%". subst.

    st_r. force_l. st_l. force_l. force_l.
    iSplitL "C". { eauto. }

    st. iSplitL; [|eauto].
    iExists _. iRight. iFrame. eauto.
  Qed.
  
  Lemma simF_set:
    HModR.sim_fun CellAMod CellIMod Ist (CellName.set idx).
  Proof.
    init_simF.
    
    st_l. hss. iDestruct "ASM" as "((% & [P|C]) & %)"; subst; hss.
    { iDestruct "IST" as (v')"[(C & A)|(P' & A & %)]"; des; subst; cycle 1.
      { iExFalso. iApply (pending_unique with "P' P"). }

      iPoseProof (cell_auth_get with "C A") as "%". subst.
      iMod (cell_auth_set with "C A") as "(C & A)".

      st_r. force_l. st_l. force_l. force_l.
      iSplitL "C". { eauto. }

      st.
      iSplitL; eauto.
      iExists _. iRight. iFrame. eauto.
    }
      
    iDestruct "IST" as (v')"[(C' & A)|(P & A & %)]".
    { iExFalso. iApply (cell_unique with "C' C"). }
    subst. hss.

    iPoseProof (cell_auth_get with "C A") as "%". subst.
    iMod (cell_auth_set with "C A") as "(C & A)".
    
    st_r. force_l. st_l. force_l. force_l.
    iSplitL "C". { eauto. }

    st. iSplitL; [|eauto].
    iExists _. iRight. iFrame. eauto.
  Qed.

  Theorem sim: HModR.sim CellAMod CellIMod Ist.
  Proof.
    init_sim.
    - iIntros "X". iDestruct "X" as (v) "(C & A)".
      iSplitL ""; eauto.
      unfold Ist. iExists _. iLeft. iFrame.
    - use_simF simF_get.
    - use_simF simF_set.
  Qed.

End SIMMODSEM.
End CellIA.
