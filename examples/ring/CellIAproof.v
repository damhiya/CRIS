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
Require Import Mem1 STB.

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
       (cell idx 0 ∗ auth idx 0)
       ∨ 
       (pending idx ∗ ∃ v, auth idx v ∗ ⌜st_tgt = v↑⌝))%I.
  
  Local Notation CellAMod := (CellA.t idx StbA).
  Local Notation CellIMod := (CellI.t idx).

  Lemma alist_find_eq `{RelDec K} V (k: K) (v:V) l:
    alist_find k ((k,v) :: l) = Some v.
  Proof.
  Admitted.

  Lemma alist_find_neq `{RelDec K} V (k k': K) (v:V) l
    (NEQ: k <> k')                   
    :
    alist_find k ((k',v) :: l) = alist_find k l.
  Proof.
  Admitted.
  
  Lemma simF_init:
    HModR.sim_fun CellAMod CellIMod Ist (CellName.init idx).
  Proof.
    (* simF_init CellA.unfold CellI.unfold CellA.init CellI.init. *)
    unfold HModR.sim_fun; i.
    rewrite// [in alist_find _ _]CellA.unfold. simpl HModSem.fnsems.
    erewrite alist_find_eq.
    rewrite// [in alist_find _ _]CellI.unfold. simpl HModSem.fnsems.
    unfold CellI.fnsems.
    erewrite alist_find_eq.
    unfold CellA.init. s.
    unfold interp_sb_hp. s.
    unfold HoareFun. s.
    unfold cfunU. unfold CellI.init.
    i. iIntros "IST".

    (* SRC: handle the IST of Cell and the precond of init *)
    st_l. hss. iDestruct "ASM" as "((% & P) & %)".
    subst. hss. unfold Ist.
    iDestruct "IST" as "[(C & A) | (P' & _)]"; des; subst; cycle 1.
    { iExFalso. iApply (pending_unique with "P P'"). }

    st_r. force_l. st_l. force_l. force_l.
    iSplitL "C".
    { eauto. }

    st.
    iSplitL; eauto.
    iRight. iFrame. eauto.
  Qed.

  Lemma simF_get:
    HModR.sim_fun CellAMod CellIMod Ist (CellName.get idx).
  Proof.
    (* simF_init MapA.unfold MapM.unfold MapA.get MapM.get. *)
    unfold HModR.sim_fun; i.
    rewrite// [in alist_find _ _]CellA.unfold. simpl HModSem.fnsems.
    erewrite alist_find_neq; cycle 1.
    { ii. depdes H0. }
    erewrite alist_find_eq.
    rewrite// [in alist_find _ _]CellI.unfold. simpl HModSem.fnsems.
    unfold CellI.fnsems.
    erewrite alist_find_neq; cycle 1.
    { ii. depdes H0. }
    erewrite alist_find_eq.
    unfold CellA.get. s.
    unfold interp_sb_hp. s.
    unfold HoareFun. s.
    unfold cfunU. unfold CellI.get.
    i. iIntros "IST".

    (* SRC: handle the IST of Map and the precond of get *)
    st_l. hss. iDestruct "ASM" as "((% & C) & %)".
    subst. hss. rename y into v. unfold Ist.
    iDestruct "IST" as "[(C0 & _)|(P & IST)]".
    { iExFalso. iApply (cell_unique with "C0 C"). }
    iDestruct "IST" as (v') "(A & %)". subst. hss.

    iPoseProof (cell_auth_get with "C A") as "%". subst.

    st_r. force_l. st_l. force_l. force_l.
    iSplitL "C". { eauto. }

    st. iSplitL; [|eauto].
    iRight. iFrame. eauto.
  Qed.
  
  Lemma simF_set:
    HModR.sim_fun CellAMod CellIMod Ist (CellName.set idx).
  Proof.
    unfold HModR.sim_fun; i.
    rewrite// [in alist_find _ _]CellA.unfold. simpl HModSem.fnsems.
    erewrite alist_find_neq; cycle 1.
    { ii. depdes H0. }
    erewrite alist_find_neq; cycle 1.
    { ii. depdes H0. }
    erewrite alist_find_eq.
    rewrite// [in alist_find _ _]CellI.unfold. simpl HModSem.fnsems.
    unfold CellI.fnsems.
    erewrite alist_find_neq; cycle 1.
    { ii. depdes H0. }
    erewrite alist_find_neq; cycle 1.
    { ii. depdes H0. }
    erewrite alist_find_eq.
    unfold CellA.set. s.
    unfold interp_sb_hp. s.
    unfold HoareFun. s.
    unfold cfunU. unfold CellI.set.
    i. iIntros "IST".

    (* SRC: handle the IST of Cell and the precond of set *)
    st_l. hss. iDestruct "ASM" as "((% & C) & %)".
    subst. hss. rename y0 into v, y1 into v0. unfold Ist.
    iDestruct "IST" as "[(C0 & _)|(P & IST)]".
    { iExFalso. iApply (cell_unique with "C0 C"). }
    iDestruct "IST" as (v') "(A & %)". subst. hss.

    iPoseProof (cell_auth_get with "C A") as "%". subst.
    iMod (cell_auth_set with "C A") as "(C & A)".
    
    st_r. force_l. st_l. force_l. force_l.
    iSplitL "C". { eauto. }

    st. iSplitL; [|eauto].
    iRight. iFrame. eauto.
  Qed.
  
  (* Theorem sim: HModR.sim CellAMod CellIMod Ist. *)
  (* Proof. *)
  (*   econs; ss. i. econs; ss. *)
  (*   { *)
  (*     iIntros "[H0 H1]". iFrame. *)
  (*     iExists _, _, _, _; iSplitR; eauto; iSplitL; eauto. *)
  (*     iLeft; eauto. *)
  (*   } *)
  (*   { rewrite CellM.unfold. rewrite CellI.unfold. ss. i. des_ifs. } *)
  (*   rewrite CellM.unfold. rewrite CellI.unfold. ss. *)
  (*   i. des_ifs. *)
  (*   - esplits; eauto. ii. subst. iIntros "IST".  *)
  (*     iApply simF_init. eauto. *)
  (*   - esplits; eauto. ii. subst. iIntros "IST".  *)
  (*     iApply simF_get. eauto. *)
  (*   - esplits; eauto. ii. subst. iIntros "IST". *)
  (*     iApply simF_set. eauto.  *)
  (*   - esplits; eauto. ii. subst. iIntros "IST".  *)
  (*     iApply simF_set_by_user. eauto. *)
  (*   - unfold Mem in *. rewrite HMem_unfold in *. ss. *)
  (*     des_ifs; esplits; eauto; ii; subst;  *)
  (*     iIntros "IST"; iApply isim_reflR; eauto. *)
  (* Qed. *)

End SIMMODSEM.
End CellIA.
