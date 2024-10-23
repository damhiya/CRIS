Require Import Coqlib ITreelib sflib.
Require Import MapHeader MapI MapM MapMSpec SMod ModSim.
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
Require Import MemA STB.

Require Import ISim HMod PMod Events ITactics.
Require Import Mod ModSimFacts.

Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module MapIM.
Section SIMMODSEM.
  Context `{_W: CtxWD.t}.
  Context `{_M: MapMR.t (Γ:=Γ)}.
  Context `{@GRA.inG memRA Γ}.  
  
  Lemma pending_unique:
    MapMS.pending -∗ MapMS.pending -∗ False%I.
  Proof.
    Local Transparent MapMS.pending.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H" as WF. exfalso.
    rr in WF. ur in WF. unseal "ra". des. ur in WF. ss.
  Qed.
  
  Definition fun_to_list (f: Z -> Z) (sz: nat) : list val :=
    map (fun i:nat => Vint (f i)) (seq 0 sz).

  Lemma repeat_fun_to_list (n: nat):
    repeat (Vint 0) n = fun_to_list (λ _, 0%Z) n.
  Proof.
    unfold fun_to_list. induction n; eauto.
    replace (S n) with (n+1) by nia.
    rewrite ->repeat_app, seq_app, map_app, IHn. eauto.
  Qed.

  Lemma fun_to_list_lookup (f: Z -> Z) (sz: nat) (i: nat)
    (LT: i < sz)
    :
    fun_to_list f sz !! i = Some (Vint (f i)).
  Proof.
    unfold fun_to_list.
    rewrite ->list_lookup_fmap, lookup_seq_lt; try nia. eauto.
  Qed.

  Lemma fun_to_list_update (f: Z -> Z) (sz: nat) (i: nat) (v: Z)
    :
    <[i := Vint v]> (fun_to_list f sz) = fun_to_list (<[Z.of_nat i := v]> f) sz.
  Proof.
    unfold fun_to_list. revert i. induction sz; i; eauto.
    replace (S sz) with (sz + 1) by nia.
    rewrite ->!seq_app, !map_app.
    assert (CASE: i < sz \/ i >= sz) by nia.
    des.
    - rewrite insert_app_l; cycle 1.
      { rewrite ->map_length, seq_length. nia. }
      rewrite IHsz. s. do 3 f_equal.
      rewrite fn_lookup_insert_ne; eauto. nia.
    - assert (Iadd: length (map (λ i0 : nat, Vint (f i0)) (seq 0 sz)) + (i - sz) = i).
      { rewrite ->map_length, seq_length. nia. }
      s. rewrite -IHsz -{1 2}Iadd -{4}(app_nil_r (seq 0 sz)) map_app. 
      rewrite ->!insert_app_r, <-app_assoc. f_equal. s.
      assert (CASE': i = sz \/ i > sz) by nia.
      des; subst.
      + rewrite ->fn_lookup_insert, Nat.sub_diag. eauto.
      + rewrite ->fn_lookup_insert_ne; try nia.
        destruct (i-sz) eqn: EQ; try nia. eauto.
  Qed.

  Definition Ist: Sk.t -> nat -> alist key Any.t -> alist key Any.t -> iProp :=
    fun _ _ st_src st_tgt =>
      ((⌜st_src = [(MapM.v_size,0%Z↑);(MapM.v_map,(fun (_: Z) => 0%Z)↑)] /\
         st_tgt = [(MapI.v_hptr,Vnullptr↑)]⌝)
        ∨
        (MapMS.pending ∗ ∃ blk ofs (f: Z -> Z) (sz: Z), 
         ⌜st_src = [(MapM.v_size,sz↑);(MapM.v_map,f↑)] /\
          st_tgt = [(MapI.v_hptr,(Vptr blk ofs)↑)]⌝ 
          ∗ (blk, ofs) |-> (fun_to_list f (Z.to_nat sz)))
       )%I.

  Variable ginv: Sk.t -> invspec.
  Variable StbMap: Sk.t -> gname -> option fspec.
  Hypothesis MapInStbMap: forall sk, stb_incl MapMS.Stb (StbMap sk).
  Variable StbMem: Sk.t -> gname -> option fspec.

  Local Notation MemA := (MemA.t ginv StbMem).
  Local Notation MapM := (MapM.t ginv StbMap).
  Local Notation MapMMod := (MapM ★ MemA).
  Local Notation MapIMod := (MapI.t ★ MemA).
  Local Notation IstFull := (IstProd (IstSB MapM Ist) IstEq).

  (**********)

  Lemma simF_init:
    HSim.sim_fun MapMMod MapIMod IstFull MapName.init.
  Proof.
    init_simF.

    (* SRC: handle the IST of Map and the precond of init *)
    steps_l. iDestruct "ASM" as "((% & P0) & %)". des. subst. hss. inv G0. 
    iDestruct "IST" as (? ? ? ?) "(%& (% & [%|(P & IST)]) &%)";    
      [|iDestruct "IST" as (? ? ? ?) "M"];
      des; subst; cycle 1.
    { iExFalso. iApply (pending_unique with "P P0"). }
    rename q into sz.
    
    (* SRC: prove the postcond of init *)
    forces_l. iSplitL ""; eauto.
    steps_r.
    
    (* TGT: inline alloc *)
    inline_r.

    (* TGT: prove the precond of alloc *)
    step_r. forces_r.
    iSplit; eauto.

    (* TGT: handle the postcond of alloc *)
    steps_r. iDestruct "GRT" as "[GRT %]". 
    iDestruct "GRT" as (?) "(% & POINTS)". subst. hss.

    (* prepare and start an induction *)
    steps_r. hss.
    replace (repeat Vundef sz) with (repeat (Vint 0) (sz-sz) ++ repeat Vundef sz); cycle 1.
    { rewrite Nat.sub_diag. eauto. }
    rewrite// -[X in ITree.iter _ X](Z.sub_diag (sz%Z)).
    iStopProof. cut (sz <= sz); [|lia].
    generalize sz at 1 4 5 11. intros n.
    induction n; i; iIntros "(PD & PTS)".

    (* Base case *)
    {
      (* TGT: unwind the loop *)
      rewrite unfold_iter_eq. des_ifs; try nia. steps_r.
      (* prove the IST of Map *)
      step. repeat (iSplit; eauto).
      iExists [_;_], [_], _, _.
      do 3 (iSplit; eauto).
      iRight. iFrame. iExists _, _, _, _. iSplitR; eauto.
      rewrite ->app_nil_r, Nat.sub_0_r, repeat_fun_to_list, Nat2Z.id. eauto.
    }

    (* Inductive case *)
    {
      (* TGT: unwind the loop *)
      rewrite unfold_iter_eq. des_ifs; try nia.
      (* TGT: compute the input to store *)
      unfold scale_int at 1. des_ifs; cycle 1.
      { exfalso. eapply n0. eapply Z.divide_factor_r. }
      s. steps_r.
      
      (* TGT: inline store *)
      inline_r.

      (* TGT: prove the precond of store *)
      step_r. force_r (_, (sz - S n)%Z, _).
      force_r ([Vptr _ (sz - (S n))%Z; _]↑).
      forces_r.
      iPoseProof (big_sepL_insert_acc with "PTS") as "(PT & CTN)".
      { instantiate (2:= (sz - (S n))).
        rewrite lookup_app_r; rewrite repeat_length; try nia.
        rewrite Nat.sub_diag. s. eauto.
      }
      rewrite ->!Z.add_0_l, Zpos_P_of_succ_nat, <-Nat2Z.inj_succ, Nat2Z.inj_sub; try nia.
      iSplitL "PT".
      { iSplitL; cycle 1.
        { iPureIntro. do 3 f_equal. rewrite Z.div_mul; nia. }
        iExists _. iFrame.
        iPureIntro. do 3 f_equal. rewrite Z.div_mul; nia.
      }

      (* TGT: handle the postcond of store *)
      steps_r. iDestruct "GRT" as "((GRT & %) & %)". subst.
      iSpecialize ("CTN" $! (Vint 0)). iPoseProof ("CTN" with "GRT") as "PTS".
      rewrite ->!Zpos_P_of_succ_nat, <-!Nat2Z.inj_succ.
      replace (sz - S n + 1)%Z with (sz - n)%Z by nia.

      (* apply the induction hypothesis and complete *)
      hss. steps_r.
      iApply IHn; try nia. iFrame.
      rewrite repeat_update.
      eapply eq_ind; [iAssumption |].
      do 3 f_equal. nia.
    }
  Qed.

  Lemma simF_get:
    HSim.sim_fun MapMMod MapIMod IstFull MapName.get.
  Proof.
    init_simF.

    (* SRC: handle the IST of Map and the precond of get *)
    steps_l. iDestruct "ASM" as "(% & %)". subst. hss. inv G0.
    iDestruct "IST" as (? ? ? ?) "(%& (% & [%|(P & IST)]) &%)";    
      [|iDestruct "IST" as (? ? ? ?) "(% & M)"];
      des; subst; hss.
    { nia. }
    rename q2 into idx.
    
    (* SRC: prove the postcond of get *)
    forces_l. iSplitL "". { eauto. }

    (* TGT: compute the input to load *)
    steps_r. hss. steps_r.
    unfold scale_int. des_ifs; cycle 1.
    { exfalso. eapply n. eapply Z.divide_factor_r. }
    s. steps_r. rewrite Z_div_mult; try nia.

    (* TGT: inline load *)
    inline_r.

    (* TGT: prove the precond of load *)
    step_r. force_r (_, (ofs + _)%Z, _). forces_r.
    iPoseProof (big_sepL_lookup_acc with "M") as "(IP & M)".
    { apply fun_to_list_lookup with (i:=Z.to_nat idx). nia. }
    rewrite Z2Nat.id; try nia.
    iSplitL "IP"; eauto.
    
    (* TGT: handle the postcond of load *)
    steps_r. iDestruct "GRT" as "[[GRT %] %]". subst. hss. steps_r.

    (* prove the IST of Map *)
    step. repeat (iSplit; eauto).
    iExists [_;_], [_], _, _.
    do 3 (iSplit; eauto).
    iRight. iFrame. iExists _, _, _, _. iSplit; eauto.
    iPoseProof ("M" with "GRT") as "M". iFrame.
  Qed.

  Lemma simF_set:
    HSim.sim_fun MapMMod MapIMod IstFull MapName.set.
  Proof.
    init_simF.

    (* SRC: handle the IST of Map and the precond of set *)
    steps_l. iDestruct "ASM" as "(% & %)". subst. hss. inv G0. 
    iDestruct "IST" as (? ? ? ?) "(%& (% & [%|(P & IST)]) &%)";    
      [|iDestruct "IST" as (? ? ? ?) "(% & M)"];
      des; subst; hss.
    { nia. }
    rename z1 into idx, z2 into v.

    (* SRC: prove the postcond of set *)
    forces_l. iSplitL "". { eauto. }

    (* TGT: compute the input to store *)
    steps_r. hss. steps_r.
    unfold scale_int. des_ifs; cycle 1.
    { exfalso. eapply n. eapply Z.divide_factor_r. }
    rewrite Z_div_mult; try nia.
    s. steps_r.

    (* TGT: inline load *)
    inline_r.

    (* TGT: prove the precond of store *)
    step_r. force_r (_, _, _). forces_r.
    iPoseProof (big_sepL_insert_acc with "M") as "(IP & M)".
    { apply fun_to_list_lookup with (i:=Z.to_nat idx). nia. }
    rewrite Z2Nat.id; try nia.
    iSplitL "IP". { eauto. }

    (* TGT: handle the postcond of load *)
    steps_r. iDestruct "GRT" as "[[GRT %] %]". subst. hss. steps_r.

    (* prove the IST of Map *)
    step. repeat (iSplit; eauto).
    iExists [_;_], [_], _, _.
    do 3 (iSplit; eauto).
    iRight. iFrame. iExists _, _, _, _. iSplit; eauto.
    iPoseProof ("M" with "GRT") as "M".
    rewrite ->fun_to_list_update, Z2Nat.id; try nia. iFrame.
  Qed.

  Lemma simF_set_by_user:
    HSim.sim_fun MapMMod MapIMod IstFull MapName.set_by_user.
  Proof.
    init_simF.

    (* SRC: handle the IST of Map and the precond of set_by_user *)
    steps_l. iDestruct "ASM" as "(% & %)". subst. hss. inv G0. hss.
    rename q2 into k.

    (* process an input *)
    steps_r. step.
    
    (* SRC: prove the precond of set *)
    steps_l. force_l (_,_); s. forces_l.
    iSplitL "". { iFrame. eauto. }

    (* make a call to set *)
    call "IST"; [eauto|].

    (* SRC: handle the postcond of set *)
    steps_l. iDestruct "ASM" as "(_ & %)". subst. hss. steps_r.

    (* SRC: prove the postcond of set_by_user *)
    forces_l. iSplitL "". { eauto. }

    (* prove the IST of Map *)
    step. eauto.
  Qed.

  Theorem sim:
    HSim.t MapMMod MapIMod MapM.InitCond IstFull.
  Proof.
    init_sim.
    - iIntros "_". iExists _,_,[],[]. iSplit.
      { rewrite !app_nil_r. eauto. }
      iSplit; [iSplit|]; eauto.
      + iPureIntro. split; prove_scope.
      + iLeft. eauto.
    - eapply simF_init; eauto.
    - eapply simF_get; eauto.
    - eapply simF_set; eauto.
    - eapply simF_set_by_user; eauto.
  Qed.

End SIMMODSEM.
End MapIM.

