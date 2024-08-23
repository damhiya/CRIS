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
Require Import CellHeader CellASpec CellA RingHeader RingA RingASpec CtrlI.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module RingIA.
Section SIMMODSEM.
  Context `{Σ: GRA.t}.
  Context `{_M: CellRA.t (Σ:=Σ)}.
  
  Variable max_size : nat.

  Variable StbG: Sk.t -> gname -> option fspec.
  Hypothesis RingInStb: forall sk, stb_incl RingAS.Stb (StbG sk).
  Hypothesis CellInStb: forall sk idx (LT: idx < max_size), stb_incl (CellAS.Stb idx) (StbG sk).

  Local Notation CellAMod := (fun idx => CellA.t idx StbG).

  Fixpoint CellGroup start len : HMod.t :=
    match len with
    | 0 => HMod.empty
    | S len' => HMod.add (CellAMod start) (CellGroup (S start) len')
    end.

  Local Notation RingAMod := (HMod.add (RingA.t max_size StbG) (CellGroup 0 max_size)).
  Local Notation RingIMod := (HMod.add (CtrlI.t max_size) (CellGroup 0 max_size)).

  Lemma cellgroup_split idx start len (RANGE: start <= idx < start + len):
    CellGroup start len =
    HMod.add (CellGroup start (idx-start)) (HMod.add (CellAMod idx) (CellGroup (S idx) (start + len - idx - 1))).
  Proof.
    revert idx start RANGE.
    induction len; i; [nia|].
    assert (TOTAL:= Nat.lt_total start idx); des; try nia; cycle 1.
    - subst. rewrite Nat.sub_diag. s.
      rewrite hmod_add_empty_l.
      repeat f_equal. nia.
    - destruct idx; ss; try nia.
      rewrite Nat.sub_succ_l; try nia.
      s. rewrite (IHlen (S idx)); try nia.
      s. rewrite hmod_add_assoc.  do 4 f_equal. nia.
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
  
  Definition Ist: Sk.t -> alist key Any.t -> alist key Any.t -> iProp :=
    (fun _ st_src st_tgt =>
     ∃ (q q': list Z) (hd tl: nat),
       ⌜st_src = [(RingA.v_que, q↑)] /\ st_tgt = [(CtrlI.v_hd,hd↑);(CtrlI.v_tl,tl↑)] /\
       hd = (tl + List.length q)%nat /\ List.length (q ++ q') = max_size⌝ ∗
       ([∗ list] i↦x ∈ q, CellAS.cell ((tl+i) mod max_size) x) ∗
       ([∗ list] i↦x ∈ q', (CellAS.pending ((hd+i) mod max_size) ∨ CellAS.cell ((hd+i) mod max_size) x)))%I.

  Definition IstFull :=
    IstProdMod (HMod.get_scopes (RingA.t max_size StbG)) (HMod.get_scopes (CellGroup 0 max_size)) Ist IstEq.

  Lemma simF_init:
    HModR.sim_fun RingAMod RingIMod IstFull RingName.init.
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "%". subst. hss. destruct q, q1.
    iDestruct "IST" as (? ? ? ?) "(% & IST & %)". des; subst.
    iDestruct "IST" as (? ? ? ?) "(% & LIVE & FREE)". des; subst. hss.

    steps_r. hss.
    force_l. force_l.
    iSplitL "". { eauto. }

    step.
    iSplit; eauto.
    repeat iExists _. iSplitL ""; cycle 1.
    - iSplit; eauto. unfold Ist.
      iExists [], (rotate (max_size - tl mod max_size) (q++q')%list), 0, 0.
      iSplitL "".
      { iPureIntro. esplits; eauto. s. rewrite rotate_length. eauto. }
      iSplitL ""; eauto.
      subst. iApply big_sepL_rotate. iApply big_sepL_app.
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
    - eauto.
  Qed.

  Lemma simF_get_size:
    HModR.sim_fun RingAMod RingIMod IstFull RingName.get_size.
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "%". subst. hss. destruct q, q1.
    iDestruct "IST" as (? ? ? ?) "(% & IST & %)". des; subst.
    iDestruct "IST" as (? ? ? ?) "(% & LIVE & FREE)". des; subst. hss.

    steps_r. hss. steps_r. hss. steps_r.
    force_l. force_l.
    iSplitL "". { eauto. }

    step.
    iSplit; cycle 1.
    { iPureIntro. f_equal. nia. }
    repeat iExists _. iSplitL ""; cycle 1.
    - iSplit; eauto. unfold Ist.
      repeat iExists _. iFrame. eauto.
    - eauto.
  Qed.

  Lemma simF_enqueue:
    HModR.sim_fun RingAMod RingIMod IstFull RingName.enqueue.
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "%". subst. hss. destruct q.
    iDestruct "IST" as (? ? ? ?) "(% & IST & %)". des; subst.
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
    repeat iExists _. iSplitL ""; cycle 1.
    - iSplit; eauto. unfold Ist.
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
    - iPureIntro. esplits; eauto.
      erewrite cellgroup_split; eauto.
      nia.
  Qed.

  Lemma simF_dequeue:
    HModR.sim_fun RingAMod RingIMod IstFull RingName.dequeue.
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "%". subst. hss. destruct q.
    iDestruct "IST" as (? ? ? ?) "(% & IST & %)". des; subst.
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
    repeat iExists _. iSplitL ""; cycle 1.
    - iSplit; eauto. unfold Ist.
      iExists q, (q'++[z]), (tl + S(List.length q)), (S tl).
      iSplitL "".
      { iPureIntro. esplits; eauto; try nia.
        rewrite !app_length. s. nia.
      }
      iSplitL "LIVE".
      + iApply (big_sepL_impl with "LIVE").
        iModIntro. iIntros (k x FIND) "H".
        rewrite/__ Nat.add_succ_r. eauto.
      + iApply big_sepL_app. iFrame. s. iSplitR ""; eauto.
        iRight. eapply eq_ind; try iAssumption. f_equal.
        erewrite <-mod_add_ex; eauto; try nia.
        exists 1. nia.
    - iPureIntro. esplits; eauto.
      + s. repeat f_equal. nia.
      + erewrite cellgroup_split; eauto.
        nia.
  Qed.

Require Import LAuto.  

Ltac prove_sub_perm :=
  s; repeat unfold_hmod; s; Lauto_normalize;
  match goal with
    [|-sub_perm ?x ?y] =>
      match x with
      | _ ++ _ => idtac
      | _ => rewrite/__ /x
      end;
      match y with
      | _ ++ _ => idtac
      | _ => rewrite/__ /y
      end
  end;
  Lauto_normalize;
  match goal with
    [|-sub_perm ?x ?y] =>
      replace (sub_perm x y) with (sub_perm (x++[]) (y++[])) by (rewrite !app_nil_r; eauto)
  end;
  repeat first [eapply sub_perm_cancel_head|eapply sub_perm_remove_head];
  eapply sub_perm_refl.


Lemma mod_sim_refl_r A B C Ist
  (SK: HMod.sk A = HMod.sk B)
  :
  HModR.sim (HMod.add A C) (HMod.add B C) (IstProdMod (HMod.get_scopes A) (HMod.get_scopes B) Ist IstEq).
Proof.
  econs; cycle 1.
  { ss. rewrite SK. eauto. }
  econs.
  - s.
  
    

    
  
  
Qed.  

  
  Theorem sim: HModR.sim RingAMod RingIMod IstFull.
  Proof.

(* Ltac init_sim := let TMP := fresh "_tmp_" in *)
  econs; s;
  [econs;
   [repeat unfold_hmod; ss
   |prove_sub_perm
   |repeat unfold_hmod; ss; try nia
   |repeat unfold_hmod; ss; i; des_ifs; eauto
   |ii;
    match goal with [FIND: alist_find _ _ = Some _ |-_] =>
      let TMP := fresh "FIND_IN" in
      assert (TMP:=FIND);
      revert FIND
    end;
    repeat (
      match goal with [FIND: alist_find _ _ = Some _ |-_] =>
        apply alist_find_some in FIND;
        s in FIND; apply in_app_or in FIND
      end; des
    );
    i;
    try match goal with [IN: In _ _ |- _] =>
      revert IN; unfold_hmod; i; simpl in IN; des; try inv IN
      end;
    try by (esplits;
      [ s; simpl HModSem.fnsems; repeat unfold_hmod; 
        alist_find_simpl fnsems_nodup; refl
      | eapply isim_reflR; [prove_nodup|ii; ss; des; eauto]])
   ]
  |repeat unfold_hmod; ss; eauto].

    (* init_sim. *)
    - iIntros "H".
      iPoseProof (HModSem.add_oiprop_split with "H") as "(R & CG)". s.
      iSplitL "CG".
      { iApply HModSem.add_oiprop_merge. s. iFrame. }
      repeat iExists _. iSplitL ""; cycle 1.
      + iSplitR ""; eauto. unfold Ist.
        iExists [], (replicate max_size 0%Z), 0, 0.
        iSplitL ""; eauto.
        * iPureIntro. esplits; eauto. s. rewrite replicate_length. eauto.
        * s. iSplitL ""; eauto.
          iApply (big_sepL_impl with "R").
          iModIntro. iIntros (? ? FIND) "P".
          iLeft. rewrite Nat.mod_small; eauto.
          eapply lookup_replicate_1. eauto.
      + iPureIntro. esplits; ss; eauto.
        * unfold RingA.t. unseal "ccr". ss.
        * eapply HModSem.well_scoped_init.
    - eapply simF_init; eauto.
    - eapply simF_get_size; eauto.
    - eapply simF_enqueue; eauto.
    - eapply simF_dequeue; eauto.
    - 

      





      unfold Ist. induction max_size; s.
      + iIntros "_". iSplitL ""; eauto. unfold IstProd.
        repeat iExists _. iSplitL ""; cycle 1.
        * iSplitR ""; eauto.
          iExists [], [], 0, 0. s. eauto.
        * rewrite app_nil_r.
          iPureIntro. esplits; ss; eauto.
      + iIntros "H". unfold CellA.t. unseal "ccr". s.
        
          
     
    - use_simF simF_init.
    - use_simF simF_get.
    - use_simF simF_set.
  Qed.

End SIMMODSEM.
End RingIA.
