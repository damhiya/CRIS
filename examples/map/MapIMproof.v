Require Import Coqlib ITreelib sflib.
Require Import MapHeader MapI MapM SMod ModSim.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM IPM.
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


Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section SIMMODSEM.
  Context `{_M: MapRA.t}.
  Context `{@GRA.inG memRA Γ}. 
        
  Variable GlobalStbM: Sk.t -> gname -> option fspec.
  Hypothesis STBINCLM: forall sk, stb_incl (to_stb MemStb) (GlobalStbM sk).
  Hypothesis STB_setM: forall sk, (GlobalStbM sk) "set" = Some set_specM.

  Lemma pending0_unique:
    pending0 -∗ pending0 -∗ False%I.
  Proof.
    Local Transparent pending0.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H" as WF. exfalso.
    rr in WF. ur in WF. unseal "ra". des. ur in WF. ss.
  Qed.
  
  Definition fun_to_list (f: Z -> Z) (sz: nat) : list val :=
    map (fun i:nat => Vint (f i)) (seq 0 sz).

  Lemma repeat_update {A} i n (v v' w: A):
    <[i:=v]> (repeat v i ++ v' :: repeat w n) = repeat v (i+1) ++ repeat w n.
  Proof.
    replace i with (length (repeat v i) + 0) at 1; cycle 1.
    { rewrite repeat_length. nia. }
    rewrite ->insert_app_r, repeat_app, <-app_assoc. eauto.
  Qed.

  Lemma repeat_fun_to_list (n: nat):
    repeat (Vint 0) n = fun_to_list (λ _ : Z, 0%Z) n.
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
  
  Let Mem := HMem (fun _ => false).

  Definition Ist: Any.t -> Any.t -> iProp :=
    fun st_src st_tgt =>
       ((⌜st_src = (fun (_: Z) => 0%Z, 0%Z)↑ /\ st_tgt = Vnullptr↑⌝)
        ∨
        (pending0 ∗ ∃ blk ofs (f: Z -> Z) (sz: Z), 
            ⌜st_src = (f, sz)↑ /\  st_tgt = (Vptr blk ofs)↑⌝ 
            ∗ (blk, ofs) |-> (fun_to_list f (Z.to_nat sz)))
       )%I.

  Lemma simF_init:
    HModR.sim_fun
      (HMod.add (MapM.HMap GlobalStbM) Mem) (HMod.add MapI.Map Mem)
      (IstProd Ist IstEq) "init".
  Proof.
    simF_init MapM.HMap_unfold MapI.Map_unfold initF MapI.initF.

    (* SRC: handle the IST of Map and the precond of init *)
    st_l. hss. iDestruct "ASM" as "(W & (%Y & %M & P0) & %X)".
    subst. hss. rename y0 into u, y1 into ℓ, x into sz.
    iDestruct "IST" as (? ? ? ?) "(%& [%|(P & _)] &%)"; des; subst; cycle 1.
    { iExFalso. iApply (pending0_unique with "P P0"). }
    hss. st_l.

    (* SRC: prove the postcond of init *)
    force_l. st_l. force_l.
    iSplitL "W". { iFrame. eauto. }
    
    (* TGT: inline alloc *)
    inline_r. s.

    (* TGT: prove the precond of alloc *)
    st_r. force_r. st_r. force_r. st_r. force_r.
    iSplitR; eauto.
    st_r.
    
    (* TGT: handle the body of alloc *)
    apc_r. hss. rename y into ord.
    
    (* TGT: handle the postcond of alloc *)
    st_r. iDestruct "GRT" as "[GRT %]".
    iDestruct "GRT" as ( ? ) "(% & POINTS)". subst.
    st_r. hss.

    (* prepare and start an induction *)
    replace (repeat Vundef sz) with (repeat (Vint 0) (sz-sz) ++ repeat Vundef sz); cycle 1.
    { rewrite Nat.sub_diag. eauto. }
    rewrite// -[X in ITree.iter _ X](Z.sub_diag (sz%Z)).
    iStopProof. cut (sz <= sz); [|lia].
    generalize sz at 1 4 5 11. intros n.
    induction n; i; iIntros "(PD & PTS)".

    (* Base case *)
    {
      (* TGT: unwind the loop *)
      rewrite unfold_iter_eq. st_r. des_ifs; try nia. st_r.
      (* prove the IST of Map *)
      st. repeat (iSplit; eauto); repeat iExists _; repeat (iSplit; eauto).
      iRight. iFrame. iExists _, _, _, _. iSplitR; eauto.
      rewrite ->app_nil_r, Nat.sub_0_r, repeat_fun_to_list, Nat2Z.id. eauto.
    }

    (* Inductive case *)
    {
      (* TGT: unwind the loop *)
      rewrite unfold_iter_eq. st_r. des_ifs; try nia. st_r.
      (* TGT: compute the input to store *)
      unfold scale_int at 1. des_ifs; cycle 1.
      { exfalso. eapply n0. eapply Z.divide_factor_r. }
      st_r.

      (* TGT: inline store *)
      inline_r. s.

      (* TGT: prove the precond of store *)
      st_r. force_r. instantiate (1:= (_, (sz - S n)%Z, _)).
      st_r. force_r. instantiate (3:= [Vptr _ (sz - (S n))%Z; _]↑).
      st_r. force_r.
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
      st_r.

      (* TGT: handle the body of store *)
      apc_r. hss. rename y into ord'.

      (* TGT: handle the postcond of store *)
      st_r. iDestruct "GRT" as "[[GRT %] %]". subst. st_r.
      iSpecialize ("CTN" $! (Vint 0)). iPoseProof ("CTN" with "GRT") as "PTS".
      rewrite ->!Zpos_P_of_succ_nat, <-!Nat2Z.inj_succ.
      replace (sz - S n + 1)%Z with (sz - n)%Z by nia.

      (* apply the induction hypothesis and complete *)
      iApply IHn; try nia. iFrame.
      rewrite repeat_update.
      eapply eq_ind; [iAssumption |].
      do 3 f_equal. nia.
    }
  Qed.

  Lemma simF_get:
    HModR.sim_fun
      (HMod.add (MapM.HMap GlobalStbM) Mem) (HMod.add MapI.Map Mem)
      (IstProd Ist IstEq) "get".
  Proof.
    simF_init MapM.HMap_unfold MapI.Map_unfold getF MapI.getF.

    (* SRC: handle the IST of Map and the precond of get *)
    st_l. hss. iDestruct "ASM" as "(W & % & %)".
    subst. hss. rename y0 into u, y1 into ℓ, y3 into idx.
    iDestruct "IST" as (? ? ? ?) "(%& [%|(P & IST)] &%)";
      [|iDestruct "IST" as (? ? ? ?) "(% & M)"];
      des; subst; hss; st_l.
    { nia. }

    (* SRC: prove the postcond of get *)
    force_l. st_l. force_l.
    iSplitL "W". { eauto. }
    st_l.

    (* TGT: compute the input to load *)
    st_r. hss. st_r. 
    unfold scale_int. des_ifs; cycle 1.
    { exfalso. eapply n. eapply Z.divide_factor_r. }
    st_r. rewrite Z_div_mult; try nia.

    (* TGT: inline load *)
    inline_r. s.

    (* TGT: prove the precond of load *)
    st_r. force_r. instantiate (1:= (_, (ofs + _)%Z, _)).
    st_r. force_r. st_r. force_r.
    iPoseProof (big_sepL_lookup_acc with "M") as "(IP & M)".
    { apply fun_to_list_lookup with (i:=Z.to_nat idx). nia. }
    rewrite Z2Nat.id; try nia.
    iSplitL "IP"; eauto.
    st_r.
    
    (* TGT: handle the body of load *)
    apc_r. rename y into ord.

    (* TGT: handle the postcond of load *)
    st_r. iDestruct "GRT" as "[[GRT %] %]". subst. st_r.

    (* prove the IST of Map *)
    st. repeat (iSplit; eauto); repeat iExists _; repeat (iSplit; eauto).
    iRight. iFrame. iExists _, _, _, _.
    iPoseProof ("M" with "GRT") as "M". iFrame. eauto.
  Qed.

  Lemma simF_set:
    HModR.sim_fun
      (HMod.add (MapM.HMap GlobalStbM) Mem) (HMod.add MapI.Map Mem)
      (IstProd Ist IstEq) "set".
  Proof.
    simF_init MapM.HMap_unfold MapI.Map_unfold setF MapI.setF.

    (* SRC: handle the IST of Map and the precond of set *)
    st_l. hss. iDestruct "ASM" as "(W & % & %)".
    subst. hss. rename y0 into u, y1 into ℓ, y4 into idx, y5 into v.
    iDestruct "IST" as (? ? ? ?) "(%& [%|(P & IST)] &%)";      
      [|iDestruct "IST" as (? ? ? ?) "(% & M)"];
      des; subst; hss; st_l.
    { nia. }

    (* SRC: prove the postcond of set *)
    force_l. st_l. force_l.
    iSplitL "W". { eauto. }
    st_l.

    (* TGT: compute the input to store *)
    st_r. hss. st_r. 
    unfold scale_int. des_ifs; cycle 1.
    { exfalso. eapply n. eapply Z.divide_factor_r. }
    st_r. rewrite Z_div_mult; try nia.

    (* TGT: inline load *)
    inline_r. s.

    (* TGT: prove the precond of store *)
    st_r. force_r. instantiate (1:= (_, _, _)).
    st_r. force_r. st_r. force_r.
    iPoseProof (big_sepL_insert_acc with "M") as "(IP & M)".
    { apply fun_to_list_lookup with (i:=Z.to_nat idx). nia. }
    rewrite Z2Nat.id; try nia.
    iSplitL "IP". { eauto. }
    st_r.

    (* TGT: handle the body of store *)
    apc_r. rename y into ord.
    
    (* TGT: handle the postcond of load *)
    st_r. iDestruct "GRT" as "[[GRT %] %]". subst. st_r.

    (* prove the IST of Map *)
    st. repeat (iSplit; eauto); repeat iExists _; repeat (iSplit; eauto).
    iRight. iFrame. iExists _, _, _, _.
    iPoseProof ("M" with "GRT") as "M".
    rewrite ->fun_to_list_update, Z2Nat.id; try nia.
    eauto.
  Qed.

  Lemma simF_set_by_user:
    HModR.sim_fun
      (HMod.add (MapM.HMap GlobalStbM) Mem) (HMod.add MapI.Map Mem)
      (IstProd Ist IstEq) "set_by_user".
  Proof.
    simF_init MapM.HMap_unfold MapI.Map_unfold set_by_userF MapI.set_by_userF.

    (* SRC: handle the IST of Map and the precond of set_by_user *)
    st_l. hss. iDestruct "ASM" as "(W & % & %)".
    subst. hss. rename y0 into u, y1 into ℓ, y3 into idx.

    (* process an input *)
    st_r. st. hss.
    
    (* SRC: prove the precond of set *)
    rewrite STB_setM. st_l. unfold HoareCall.
    st_l. force_l. instantiate (1:= mk_meta _ _ (_, _)).
    st_l. force_l. st_l. force_l.
    iSplitL "W". { iFrame. eauto. }
    st_l.

    (* make a call to set *)
    call; [eauto|].

    (* SRC: handle the postcond of set *)
    st_l. iDestruct "ASM" as "(W & _ & %)". subst. hss.

    (* SRC: prove the postcond of set_by_user *)
    force_l. st_l. force_l. iSplitL "W". { eauto. }

    (* prove the IST of Map *)
    st. eauto.
  Qed.
  
  Theorem sim: HModR.sim (HMod.add (MapM.HMap GlobalStbM) Mem) (HMod.add MapI.Map Mem) (IstProd Ist IstEq).
  Proof.
    sim_init.
    - iIntros "[H0 H1]". iFrame.
      iExists _, _, _, _; iSplitR; eauto; iSplitL; eauto.
      iLeft; eauto.
    - iApply simF_init. eauto.
    - iApply simF_get. eauto.
    - iApply simF_set. eauto.
    - iApply simF_set_by_user. eauto.
    - iApply isim_reflR. eauto.
    - iApply isim_reflR. eauto.
    - iApply isim_reflR. eauto.
    - iApply isim_reflR. eauto.
    - iApply isim_reflR. eauto.
  Qed.

  
End SIMMODSEM.
