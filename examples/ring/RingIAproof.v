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
Require Import CellHeader CellASpec CellA RingHeader RingA RingASpec CtrlI.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module RingIA.
Section SIMMODSEM.
  Context `{Σ: GRA.t}.
  Context `{_M: CellRA.t (Σ:=Σ)}.

  Variable max_size : nat.

  Variable StbA: Sk.t -> gname -> option fspec.
  Hypothesis RingInStb: forall sk, stb_incl (to_stb RingAS.Stb) (StbA sk).
  Hypothesis CellInStb: forall sk idx (LT: idx < max_size), stb_incl (to_stb (CellAS.Stb idx)) (StbA sk).

  Import CellAS.

  Local Notation RingAMod := (RingA.t max_size StbA).
  Local Notation CtrlIMod := (CtrlI.t max_size).
  Local Notation CellAMod := (fun i => CellA.t max_size StbA).

  Variable HMod_empty: HMod.t.

  Fixpoint CellGroup (i: nat) : HMod.t :=
    match i with
    | 0 => HMod_empty
    | S i' => HMod.add (CellAMod i') (CellGroup i')
    end.

  Local Notation RingIMod := (HMod.add CtrlIMod (CellGroup max_size)).

  Print rotate.

  Definition rotate_rev {T} n (l: list T) :=
    drop ((strings.length l)-(n mod strings.length l)) l ++ take ((strings.length l)-(n mod strings.length l)) l.

  Lemma rotate_rev_inv {T} n (l: list T):
    rotate_rev n (rotate n l) = l.
  Proof. admit. Admitted.

  Lemma rotate_rev_id {T} (l: list T):
    rotate_rev 0 l = l.
  Proof. admit. Admitted.
  
  Definition Ist: Any.t -> Any.t -> iProp :=
    (fun st_src st_tgt =>
       ((∃ (sz:nat) (q q': list Z) (hd tl: nat) cell_state,
         ⌜st_src = (sz, q)↑ /\ List.length q = sz /\ sz < max_size /\
          st_tgt = Any.pair (hd,tl)↑ cell_state /\ hd-tl = sz /\
          List.length (q ++ q') = max_size⌝ ∗
          [∗ list] i↦x ∈ rotate_rev tl (q++q'), (CellAS.pending i ∨ CellAS.cell (i mod max_size) x))))%I.

  Variable fl: alist string (Any.t → itree hmodE Any.t).
  Variable fr: alist string (Any.t → itree hmodE Any.t).
  
  Lemma simF_init:
    HModR.sim_fun RingAMod RingIMod Ist RingName.init.
  Proof.
    cut (forall sk, isim_fsem Ist fl fr
     (λ '(st_src0, v_src) '(st_tgt0, v_tgt), Ist st_src0 st_tgt0 ** ⌜v_src = v_tgt⌝)
     (interp_sb_hp (StbA sk) {| fsb_fspec := fspec_trivial; fsb_body :=  cfunU RingA.init |})
     (fun args => translate (HModSem.emb_ run_l) (cfunU CtrlI.init args))).
    { admit. }
    unfold interp_sb_hp, HoareFun, cfunU, ccallU; s;
    unfold RingA.init, CtrlI.init.
    ii; subst; iIntros "IST".

    (* init_simF. *)

    st_l. iDestruct "ASM" as "%". subst. hss.

    st_r. force_l. st_l. force_l.
    iSplitL "". { eauto. }

    st.
    iSplitL; eauto. unfold Ist.
    iDestruct "IST" as (sz q q' hd tl cell_state) "(% & CS)".
    des; subst.
    iExists 0, [], (rotate_rev tl (q++q')%list), 0, 0, cell_state. s.
    replace (rotate_rev 0 (rotate_rev tl (q ++ q'))) with
      (rotate_rev tl (q ++ q')) by admit.
    iFrame. hss.
    iPureIntro. esplits; eauto; try nia.
    admit.
  Admitted.

  Lemma simF_get:
    HModR.sim_fun CellAMod CellIMod Ist (CellName.get idx).
  Proof.
    init_simF.

    st_l. iDestruct "ASM" as "((% & C) & %)".
    subst. hss. rename y0 into v. unfold Ist.
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
    init_simF.
    
    st_l. hss. iDestruct "ASM" as "((% & C) & %)".
    subst. hss. rename y1 into v, y2 into v0. unfold Ist.
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

  Theorem sim: HModR.sim CellAMod CellIMod Ist.
  Proof.
    init_sim.
    - unfold Ist. eauto.
    - use_simF simF_init.
    - use_simF simF_get.
    - use_simF simF_set.
  Qed.

End SIMMODSEM.
End RingIA.
