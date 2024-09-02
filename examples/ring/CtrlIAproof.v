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

Require Import ISim ITactics HMod PMod SMod Events.
Require Import Mod ModSimFacts.
Require Import CellHeader CellASpec CellA RingHeader RingA RingASpec CtrlI.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module CtrlIA.
Section SIMMODSEM.
  Context `{Σ: GRA.t}.
  Context `{_M: CellRA.t (Σ:=Σ)}.

  Variable max_size : nat.

  Variable GI: Sk.t -> invspec.
  Variable StbR: Sk.t -> gname -> option fspec.
  Variable StbC: Sk.t -> gname -> option fspec.
  (* Hypothesis RingInStb: forall sk, stb_incl RingAS.Stb (StbR sk). *)
  (* Hypothesis CellInStb: forall sk idx (LT: idx < max_size), stb_incl (CellAS.Stb idx) (StbR sk). *)

  Local Notation CellA := (fun idx => CellA.t idx GI StbC).

  Definition CellG start len : HMod.t :=
    HMod.addL (List.map CellA (seq start len)).

  Local Notation RingA := ((RingA.t max_size GI StbR) ★ (CellG 0 max_size)).
  Local Notation RingI := ((CtrlI.t max_size)         ★ (CellG 0 max_size)).

  Lemma cellgroup_split idx start len (RANGE: start <= idx < start + len):
    CellG start len =
      (CellG start (idx-start)) ★ (CellA idx) ★
        (CellG (S idx) (start + len - idx - 1)).
  Proof.
    unfold CellG.
    assert (EQ: seq start len =
                seq start (idx-start) ++ seq idx (S (start + len - idx - 1))).
    { etrans; [|etrans]; cycle 1.
      - apply (seq_app (idx-start) (start + len - idx) start).
      - f_equal. f_equal; nia.
      - f_equal. nia.
    }
    rewrite/__ EQ map_app hmod_addL_app. eauto.
  Qed.

  Lemma big_sepL_mod {T} (Φ: nat -> T -> iProp) (l: list T):
    ([∗ list] i↦x ∈ l, Φ (i mod List.length l) x) -∗
    ([∗ list] i↦x ∈ l, Φ i x).
  Proof.
    iIntros "H". iApply (big_sepL_impl with "H").
    iModIntro. iIntros (? ?) "% H".
    eapply eq_ind; try iAssumption. f_equal.
    destruct (lookup_lt_is_Some l k).
    eauto using Nat.mod_small.
  Qed.

  Lemma mod_add_ex (a b c: nat)
    (NEQ: c ≠ 0)
    (EX: exists x, a = b + x * c):
    a mod c = b mod c.
  Proof. destruct EX. subst. eapply Nat.mod_add; eauto. Qed.

  Lemma big_sepL_rotate {T} (Φ: nat -> T -> iProp) n (l: list T):
    ([∗ list] i↦x ∈ l, Φ ((n+i) mod List.length l) x) -∗
    ([∗ list] i↦x ∈ rotate (List.length l - n mod List.length l) l, Φ i x).
  Proof.
    destruct (Nat.eq_decidable (List.length l) 0) as [|LENL].
    { destruct l; ss. }
    iIntros "H". iApply big_sepL_mod. rewrite rotate_length.

    destruct (Nat.eq_decidable (n mod List.length l) 0) as [|LENN].
    { rewrite/__ H0 Nat.sub_0_r.
      unfold rotate. rewrite Nat.mod_same; eauto.
      rewrite/__ drop_0 take_0 app_nil_r.
      eapply eq_ind; try iAssumption. f_equal. extensionalities. f_equal.
      rewrite Nat.add_mod; eauto. rewrite/__ H0 Nat.mod_mod; eauto.
    }
    assert (LE:= Nat.mod_upper_bound n _ LENL).

    iApply big_sepL_app. rewrite drop_length.
    rewrite Nat.mod_small; try nia.
    iPoseProof ((big_sepL_take_drop _ l (List.length l - n mod List.length l)) with "H") as "[H1 H2]".
    iSplitL "H2";
      (eapply eq_ind; try iAssumption; f_equal; extensionalities; f_equal).
    - eapply mod_add_ex; eauto.
      rewrite/__ {1}(Nat.div_mod_eq n (List.length l)).
      exists (S (n / List.length l)). nia.
    - eapply mod_add_ex; eauto.
      rewrite/__ {1}(Nat.div_mod_eq n (List.length l)).
      exists (n / List.length l). nia.
  Qed.

  Definition Ist: Sk.t -> nat -> alist key Any.t -> alist key Any.t -> iProp :=
    (fun _ _ st_src st_tgt =>
     ∃ (q q': list Z) (hd tl: nat),
       ⌜st_src = [(RingA.v_que, q↑)] /\ st_tgt = [(CtrlI.v_hd,hd↑);(CtrlI.v_tl,tl↑)] /\
       hd = (tl + List.length q)%nat /\ List.length (q ++ q') = max_size⌝ ∗
       ([∗ list] i↦x ∈ q, CellAS.cell ((tl+i) mod max_size) x) ∗
       ([∗ list] i↦x ∈ q', (CellAS.pending ((hd+i) mod max_size) ∨ CellAS.cell ((hd+i) mod max_size) x)))%I.

  Notation IstFull := (IstProd (IstSB (RingA.t max_size GI StbR) Ist) IstEq).

  Lemma simF_init:
    HSim.sim_fun RingA RingI IstFull RingName.init.
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "%". subst. hss. destruct q, q1.
    iDestruct "IST" as (? ? ? ?) "(% & (% & IST) & %)". des; subst.
    iDestruct "IST" as (? ? ? ?) "(% & LIVE & FREE)". des; subst. hss.

    steps_r. hss.
    force_l. force_l.
    iSplitL "". { eauto. }

    step.
    iSplit; eauto.
    iExists [_], [_;_], st_tgtR, st_tgtR.
    do 3 (iSplit; eauto).
    iExists [], (rotate (max_size - tl mod max_size) (q++q')%list), 0, 0.
    iSplit.
    { iPureIntro. esplits; eauto. s. rewrite rotate_length. eauto. }

    iSplit; eauto. rewrite <-H5.
    iApply big_sepL_rotate. iApply big_sepL_app.
    iSplitL "LIVE".
    + iApply (big_sepL_impl with "LIVE").
      iModIntro. iIntros (k x) "% LIVE". iRight. s.
      rewrite Nat.mod_mod; eauto.
      rewrite app_length. apply lookup_lt_Some in H0. nia.
    + iApply (big_sepL_impl with "FREE").
      iModIntro. iIntros (k x) "% FREE". s.
      rewrite Nat.add_assoc.
      rewrite Nat.mod_mod; eauto.
      rewrite app_length. apply lookup_lt_Some in H0. nia.
  Qed.

  Lemma simF_get_size:
    HSim.sim_fun RingA RingI IstFull RingName.get_size.
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "%". subst. hss. destruct q, q1.
    iDestruct "IST" as (? ? ? ?) "(% & (% & IST) & %)". des; subst.
    iDestruct "IST" as (? ? ? ?) "(% & LIVE & FREE)". des; subst. hss.

    steps_r. hss. steps_r. hss. steps_r.
    force_l. force_l.
    iSplitL "". { eauto. }

    step.
    iSplit. { iPureIntro. f_equal. nia. }
    iExists [_], [_;_], st_tgtR, st_tgtR.
    do 3 (iSplit; eauto).
    repeat iExists _. iFrame. eauto.
  Qed.

  Lemma simF_enqueue:
    HSim.sim_fun RingA RingI IstFull RingName.enqueue.
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "%". subst. hss. destruct q.
    iDestruct "IST" as (? ? ? ?) "(% & (% & IST) & %)". des; subst.
    iDestruct "IST" as (? ? ? ?) "(% & LIVE & FREE)". des; subst. hss.

    steps_r. hss. steps_r. hss. steps_r.
    rewrite minus_plus. des_ifs; cycle 1.
    { step. ss. }

    steps_l. hss.

    apply Nat.ltb_lt in Heq. rewrite app_length in H6.
    assert (UBND:= Nat.mod_upper_bound (tl + List.length q) max_size).
    rewrite (@cellgroup_split ((tl+ List.length q) mod max_size)) in *; try nia.
    inline_r.

    steps_r.
    destruct q'; [ss; nia|].
    force_r. instantiate (1:= (_,_)). force_r. force_r.
    iDestruct "FREE" as "(Q & FREE)".
    rewrite !Nat.add_0_r in *.
    iSplitL "Q".
    { iFrame. eauto. }

    steps_r. apc_r. steps_r.  rename q1 into z'.
    iDestruct "GRT" as "((% & CELL) & %)". subst. hss.
    steps_r. hss. force_l. force_l.
    iSplitL ""; eauto.

    step.
    iSplit; eauto.
    iExists [_], [_;_], st_tgtR, st_tgtR.
    do 3 (iSplit; eauto).
    iExists (q++[z']), q', ((tl + List.length q)+1), tl.
    iSplitL "".
    { iPureIntro. esplits; eauto.
      - rewrite app_length. s. nia.
      - rewrite !app_length. s. nia.
    }
    iSplitL "LIVE CELL".
    + iApply big_sepL_app. iFrame. s. rewrite Nat.add_0_r. eauto.
    + iApply (big_sepL_impl with "FREE").
      iModIntro. iIntros (k x FIND) "H".
      rewrite <-!Nat.add_assoc. eauto.
  Qed.

  Lemma simF_dequeue:
    HSim.sim_fun RingA RingI IstFull RingName.dequeue.
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "%". subst. hss. destruct q.
    iDestruct "IST" as (? ? ? ?) "(% & (% & IST) & %)". des; subst.
    iDestruct "IST" as (? ? ? ?) "(% & LIVE & FREE)". des; subst. hss.

    steps_r. hss. steps_r. hss. steps_r.
    destruct q; ss.
    { rewrite/__ Nat.add_0_r Nat.sub_diag. s. step. ss. }
    replace (tl + S(List.length q) - tl) with (S(List.length q)) by nia. s.
    rewrite !app_length in *.

    steps_l. hss.
    assert (UBND:= Nat.mod_upper_bound tl max_size).
    rewrite (@cellgroup_split (tl mod max_size)) in *; try nia.

    inline_r.

    force_r. force_r. force_r.
    iDestruct "LIVE" as "(Q & LIVE)".
    rewrite !Nat.add_0_r in *.
    iSplitL "Q". { iFrame. eauto. }

    steps_r. apc_r. steps_r.
    iDestruct "GRT" as "((% & CELL) & %)". subst. hss.
    steps_r. hss. force_l. force_l.
    iSplitL ""; eauto.

    step.
    iSplit; eauto.
    iExists [_], [_;_], st_tgtR, st_tgtR.
    do 3 (iSplit; eauto).
    iExists q, (q'++[z]), (tl + S(List.length q)), (S tl).
    iSplit.
    { iPureIntro. esplits; eauto; try nia.
      - repeat f_equal. nia.
      - rewrite !app_length. s. nia.
    }
    iSplitL "LIVE".
    + iApply (big_sepL_impl with "LIVE").
      iModIntro. iIntros (k x FIND) "H".
      rewrite/__ Nat.add_succ_r. eauto.
    + iApply big_sepL_app. iFrame. s. iSplitR ""; eauto.
      iRight. eapply eq_ind; try iAssumption. f_equal.
      erewrite <-mod_add_ex; eauto; try nia.
      exists 1. nia.
  Qed.

  Theorem sim: HSim.t RingA RingI (RingA.InitCond max_size) IstFull.
  Proof.
    init_sim.
    - iIntros "R". iExists [_], [_;_], _, _.
      do 2 (iSplit; eauto).
      iSplitR. { iPureIntro. esplits; s; prove_scope. }
      iExists [], (replicate max_size 0%Z), 0, 0.
      s. iSplitR; eauto.
      { iPureIntro. esplits; s; eauto using replicate_length. }
      iSplit; eauto.
      iApply (big_sepL_impl with "R").
      iModIntro. iIntros (? ? FIND) "P".
      iLeft. rewrite Nat.mod_small; eauto.
      eapply lookup_replicate_1. eauto.
    - apply simF_init.
    - apply simF_get_size.
    - apply simF_enqueue.
    - apply simF_dequeue.
  Qed.

End SIMMODSEM.
End CtrlIA.
