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

Require Import ISim HMod PMod Events.
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
  
  Variable StbM: Sk.t -> gname -> option fspec.
  Hypothesis MapInStb: forall sk, stb_incl (to_stb MapMS.Stb) (StbM sk).

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

  Local Notation MapMMod := (HMod.add (MapM.t StbM) (MemA.t (fun _ => false) StbM)).
  Local Notation MapIMod := (HMod.add MapI.t (MemA.t (fun _ => false) StbM)).
  
  Definition Ist: alist key Any.t -> alist key Any.t -> iProp :=
    fun st_src st_tgt =>
      ((⌜st_src = [(MapM.v_size,0%nat↑);(MapM.v_map,(fun (_: Z) => 0%Z, 0%Z)↑)] /\
         st_tgt = [(MapI.v_hptr,Vnullptr↑)]⌝)
        ∨
        (MapMS.pending ∗ ∃ blk ofs (f: Z -> Z) (sz: Z), 
         ⌜st_src = [(MapM.v_size,sz↑);(MapM.v_map,f↑)] /\
          st_tgt = [(MapI.v_hptr,(Vptr blk ofs)↑)]⌝ 
          ∗ (blk, ofs) |-> (fun_to_list f (Z.to_nat sz)))
       )%I.


  (**********)
  (* Temporary Tactic Designs *)

  Require Import ITacticsInternal.

  (* minimal version of 'ired' in itreelib. *)
  Tactic Notation "ired" "in" ident(H) := 
    repeat (try rewrite subst_bind in H; try rewrite bind_bind in H; 
            try rewrite bind_ret_l in H; try rewrite bind_ret_r in H; 
            try rewrite bind_tau in H; try rewrite interp_ret in H;
            try rewrite interp_tau in H; try rewrite interp_bind in H;
            cbn in H).

  Tactic Notation "_unwrapS" ident(IT) :=
    try rewrite! SModRed.interp_bind in IT;
    match IT with
    | interp_smod _ _ _ =>
      ired in IT; rewrite SModRed.interp_bind in IT
    | (interp_smod _ _ (trigger (Call _ _)) >>= _) =>
      rewrite SModRed.interp_call in IT
    | (interp_smod _ _ (trigger (SPut _ _)) >>= _) =>
      rewrite SModRed.interp_pg in IT
    | (interp_smod _ _ (trigger (SGet _)) >>= _) =>
      rewrite SModRed.interp_pg in IT
    | (interp_smod _ _ (trigger (Choose _)) >>= _) =>
      rewrite SModRed.interp_core in IT
    | (interp_smod _ _ (trigger (Take _)) >>= _) =>
      rewrite SModRed.interp_core in IT   
    | (interp_smod _ _ (trigger (IO _ _)) >>= _) =>
      rewrite SModRed.interp_core in IT     
    | (interp_smod _ _ (trigger (Assume _)) >>= _) =>
      rewrite SModRed.interp_Assume in IT
    | (interp_smod _ _ (trigger (Guarantee _)) >>= _) =>
      rewrite SModRed.interp_Guarantee in IT
    | _ =>
      try rewrite SModRed.interp_tau in IT; 
      try rewrite SModRed.interp_ret in IT; simpl in IT;
      try rewrite! SModRed.interp_bind in IT      
    end.

  Tactic Notation "_unwrapP" ident(IT) :=
    try rewrite! PModRed.transl_bind in IT;
    match IT with
    | translate _ _ =>
      ired in IT; rewrite! PModRed.transl_bind in IT 
    | ((translate _ (trigger (Call _ _))) >>= _) =>
      rewrite PModRed.transl_call in IT
    | ((translate _ (trigger (SPut _ _))) >>= _) => 
      rewrite PModRed.transl_pg in IT
    | ((translate _ (trigger (SGet _))) >>= _) => 
      rewrite PModRed.transl_pg in IT
    | ((translate _ (trigger (Choose _))) >>= _) => 
      rewrite PModRed.transl_core in IT
    | ((translate _ (trigger (Take _))) >>= _) => 
      rewrite PModRed.transl_core in IT
    | ((translate _ (trigger (IO _ _))) >>= _) => 
      rewrite PModRed.transl_core in IT
    | _ => 
      try rewrite PModRed.transl_tau in IT; 
      try rewrite PModRed.transl_ret in IT; simpl in IT;
      try rewrite! PModRed.transl_bind in IT
    end.

  (* These '_unwrap's are missing some of patterns such as below: *)
  (* e.g. translate _ _ => _ (Whole itree is bound in a single translate) *)
  (* Missing patterns should be put in right places to not mess up the unwrapping order *)

  Tactic Notation "_unwrap" constr(itr) :=
    let IT := fresh "__IT" in 
    match itr with
    | ((translate _ (trigger (Call _ _))) >>= _) =>
      rewrite HModWrap.transl_call
    | ((translate _ (trigger (SPut _ _))) >>= _) => 
      rewrite HModWrap.transl_put
    | ((translate _ (trigger (SGet _))) >>= _) => 
      rewrite HModWrap.transl_get
    | ((translate _ (trigger (Choose _))) >>= _) => 
      rewrite HModWrap.transl_core
    | ((translate _ (trigger (Take _))) >>= _) => 
      rewrite HModWrap.transl_core
    | ((translate _ (trigger (IO _ _))) >>= _) => 
      rewrite HModWrap.transl_core
    | ((translate _ (trigger (Assume _))) >>= _) => 
      rewrite HModWrap.transl_Assume
    | ((translate _ (trigger (Guarantee _))) >>= _) => 
      rewrite HModWrap.transl_Guarantee
    | (translate _ (interp_smod _ _ (?itr0) >>= _) >>= _) =>
      set (IT := itr0); _unwrapS IT; unfold IT; clear IT; grind
    | ((translate _ (PModSem.transl (?itr1) >>= _)) >>= _) =>
      set (IT := itr1); _unwrapP IT; unfold IT; clear IT; grind 
    | _ => 
      grind; try rewrite HModWrap.transl_tau;
      try rewrite HModWrap.transl_ret; simpl
    end.

    
  Ltac unwrap_l :=
    let IT := fresh "__IT" in 
    match goal with
    | [|- _ (_ (_, ?itr_src) (_, ?itr_tgt))] =>
      set (IT := itr_tgt); 
      try rewrite! HModWrap.transl_bind; _unwrap itr_src;
      unfold IT; clear IT
    end.

  Ltac unwrap_r :=
    let IT := fresh "__IT" in 
    match goal with
    | [|- _ (_ (_, ?itr_src) (_, ?itr_tgt))] => 
      set (IT := itr_src); 
      try rewrite! HModWrap.transl_bind; _unwrap itr_tgt;
      unfold IT; clear IT
    end.    

  Ltac unwrap := unwrap_l; unwrap_r.

  Ltac force_l := try (unwrap_l; _force_l).
  Ltac force_r := try (unwrap_r; _force_r).

  Ltac step := repeat
    (unwrap; try _step; simpl; des_pairs).

  Ltac step_l := let IT := fresh "__IT" in
    match goal with [|- _ (_ (_, _) (_, ?itgt))] => set (IT := itgt) end;
    repeat (unwrap_l; try _step; simpl; des_pairs);
    unfold IT; clear IT.

  Ltac step_r := let IT := fresh "__IT" in
    match goal with [|- _ (_ (_, ?isrc) (_, _))] => set (IT := isrc) end;
    repeat (unwrap_r; try _step; simpl; des_pairs);
    unfold IT; clear IT.

  Ltac apc_r :=
    rewrite SModRed.interp_apc;
    step_r; unfold HoareAPC; step_r; rewrite unfold_APC; step_r;
    match goal with [b: bool|-_] => destruct b end;
    [|unfold guarantee, triggerNB; step_r;
      match goal with [v: void|-_] => destruct v end].

    
  (**********)

  Lemma simF_init:
    HModR.sim_fun MapMMod MapIMod (IstProd [MapM.scope] [MemA.scope] Ist IstEq) MapName.init.
  Proof.
    init_simF.
    unfold HModSem.wrap_body; simpl.
    step_l. iDestruct "ASM" as "(W & (%Y & %M & P0) & %X)". subst. hss. step_l.
    unfold cput. step_l.

    let IT := fresh "__IT" in 
    match goal with
    | [|- _ (_ (_, ?itr_src) (_, ?itr_tgt))] => 
      set (IT := itr_src)
    end.
    ired in __IT.
    rewrite <- HModWrap.transl_bind in __IT.

    match __IT with
    | ((translate _ _) >>= _) =>
      try rewrite! SModRed.interp_bind in __IT
    end.

    (* unwrap tactic is missing some of bind patterns
      or handling some patterns in wrong order. *)

    rewrite SModRed.interp_bind. 

    step_r. hss. step_r. 

    rewrite PModRed.transl_bind.
    rewrite PModRed.transl_call.
    unwrap_r. step_r.
    
    (* SRC: handle the IST of Map and the precond of init *)
    st_l. hss. iDestruct "ASM" as "(W & (%Y & %M & P0) & %X)".
    subst. hss. rename y1 into u, y2 into ℓ, x into sz.
    iDestruct "IST" as (? ? ? ?) "(%& [%|(P & _)] &%)"; des; subst; cycle 1.
    { iExFalso. iApply (pending_unique with "P P0"). }
    hss. st_l.

    (* SRC: prove the postcond of init *)
    force_l. st_l. force_l.
    iSplitL "W". { iFrame. eauto. }
    
    (* TGT: inline alloc *)
    inline_r.

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
    HModR.sim_fun MapMMod MapIMod (IstProd Ist IstEq) MapName.get.
  Proof.
    init_simF.

    (* SRC: handle the IST of Map and the precond of get *)
    st_l. hss. iDestruct "ASM" as "(W & % & %)".
    subst. hss. rename y1 into u, y2 into ℓ, y4 into idx.
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
    inline_r.

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
    HModR.sim_fun MapMMod MapIMod (IstProd Ist IstEq) MapName.set.
  Proof.
    init_simF.

    (* SRC: handle the IST of Map and the precond of set *)
    st_l. hss. iDestruct "ASM" as "(W & % & %)".
    subst. hss. rename y1 into u, y2 into ℓ, y5 into idx, y6 into v.
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
    inline_r.

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
    HModR.sim_fun MapMMod MapIMod (IstProd Ist IstEq) MapName.set_by_user.
  Proof.
    init_simF.

    (* SRC: handle the IST of Map and the precond of set_by_user *)
    st_l. hss. iDestruct "ASM" as "(W & % & %)".
    subst. hss. rename y1 into u, y2 into ℓ, y4 into idx.

    (* process an input *)
    st_r. st. hss.
    
    (* SRC: prove the precond of set *)
    unfold_stb MapInStb MapMS.Stb.
    st_l. unfold HoareCall.
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

  
  Theorem sim: HModR.sim MapMMod MapIMod (IstProd Ist IstEq).
  Proof.
    init_sim.
    - iIntros "(_& H)". iFrame.
      iExists _, _, _, _; iSplitR; eauto; iSplitL; eauto.
      iLeft; eauto.
    - use_simF simF_init.
    - use_simF simF_get.
    - use_simF simF_set.
    - use_simF simF_set_by_user.
    - refl_simF.
  Qed.

End SIMMODSEM.
End MapIM.
 
