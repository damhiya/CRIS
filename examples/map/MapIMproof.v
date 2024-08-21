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

  Local Notation MapMMod := (HMod.add (MapM.t StbM) (MemA.t (fun _ => false) StbM)).
  Local Notation MapIMod := (HMod.add MapI.t (MemA.t (fun _ => false) StbM)).
  
  Definition Ist: alist key Any.t -> alist key Any.t -> iProp :=
    fun st_src st_tgt =>
      ((⌜st_src = [(MapM.v_size,0%Z↑);(MapM.v_map,(fun (_: Z) => 0%Z)↑)] /\
         st_tgt = [(MapI.v_hptr,Vnullptr↑)]⌝)
        ∨
        (MapMS.pending ∗ ∃ blk ofs (f: Z -> Z) (sz: Z), 
         ⌜st_src = [(MapM.v_size,sz↑);(MapM.v_map,f↑)] /\
          st_tgt = [(MapI.v_hptr,(Vptr blk ofs)↑)]⌝ 
          ∗ (blk, ofs) |-> (fun_to_list f (Z.to_nat sz)))
       )%I.

  (**********)

  Lemma simF_init:
    HModR.sim_fun MapMMod MapIMod (IstProd [MapM.scope] [MemA.scope] Ist IstEq)
      MapName.init.
  Proof.
    init_simF; unfold HModSem.sandbox_body; simpl.

    (* SRC: handle the IST of Map and the precond of init *)
    steps_l. iDestruct "ASM" as "(W & (%Y & %M & P0) & %X)". subst. hss. inv G0.
    rename q0 into u, q1 into ℓ, x into sz.
    iDestruct "IST" as (? ? ? ?) "(%& [%|(P & IST)] &%)";
      [|iDestruct "IST" as (? ? ? ?) "(% & M)"];
      des; subst; cycle 1.
    { iExFalso. iApply (pending_unique with "P P0"). }
    hss.

    (* SRC: prove the postcond of init *)
    force_l. force_l. iSplitL "W".
    { iFrame. eauto. }
    steps_r.
    
    (* TGT: inline alloc *)
    inline_r.

    (* TGT: prove the precond of alloc *)
    force_r. force_r. force_r.
    iSplitL ""; eauto.

    (* apc *)
    apc_r.

    (* TGT: handle the postcond of alloc *)
    steps_r. iDestruct "GRT" as "[GRT %]". 
    iDestruct "GRT" as ( ? ) "(% & POINTS)". subst. hss.

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
      repeat iExists _. iSplitR; cycle 1.
      - iSplitL; eauto.
        iRight. iFrame. iExists _, _, _, _. iSplitR; eauto.
        rewrite ->app_nil_r, Nat.sub_0_r, repeat_fun_to_list, Nat2Z.id. eauto.
      - hss.
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
      force_r. instantiate (1:= (_, (sz - S n)%Z, _)).
      force_r. instantiate (3:= [Vptr _ (sz - (S n))%Z; _]↑).
      force_r.
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

      (* TGT: handle the body of store *)
      apc_r.

      (* TGT: handle the postcond of store *)
      steps_r. iDestruct "GRT" as "[[GRT %] %]". subst.
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
    HModR.sim_fun MapMMod MapIMod (IstProd [MapM.scope] [MemA.scope] Ist IstEq)
      MapName.get.
  Proof.
    init_simF.

    (* SRC: handle the IST of Map and the precond of get *)
    steps_l. iDestruct "ASM" as "(W & % & %)". subst. hss. inv G0.
    rename q0 into u, q1 into ℓ, q3 into idx, q4 into sz, q5 into f.
    iDestruct "IST" as (? ? ? ?) "(%& [%|(P & IST)] &%)";
      [|iDestruct "IST" as (? ? ? ?) "(% & M)"];
      des; subst; hss.
    { nia. }

    (* SRC: prove the postcond of get *)
    force_l. force_l.
    iSplitL "W". { eauto. }

    (* TGT: compute the input to load *)
    steps_r. hss. steps_r.
    unfold scale_int. des_ifs; cycle 1.
    { exfalso. eapply n. eapply Z.divide_factor_r. }
    s. steps_r. rewrite Z_div_mult; try nia.

    (* TGT: inline load *)
    inline_r.

    (* TGT: prove the precond of load *)
    force_r. instantiate (1:= (_, (ofs + _)%Z, _)).
    force_r. force_r.
    iPoseProof (big_sepL_lookup_acc with "M") as "(IP & M)".
    { apply fun_to_list_lookup with (i:=Z.to_nat idx). nia. }
    rewrite Z2Nat.id; try nia.
    iSplitL "IP"; eauto.
    
    (* TGT: handle the body of load *)
    apc_r.

    (* TGT: handle the postcond of load *)
    steps_r. iDestruct "GRT" as "[[GRT %] %]". subst. hss. steps_r.

    (* prove the IST of Map *)
    step. repeat (iSplit; eauto).
    repeat iExists _. iSplitR; cycle 1.
    - iSplitL; eauto.
      iRight. iFrame. iExists _, _, _, _. iSplitR; eauto.
      iPoseProof ("M" with "GRT") as "M". iFrame.
    - hss.
  Qed.

  Lemma simF_set:
    HModR.sim_fun MapMMod MapIMod (IstProd [MapM.scope] [MemA.scope] Ist IstEq)
      MapName.set.
  Proof.
    init_simF.

    (* SRC: handle the IST of Map and the precond of set *)
    steps_l. iDestruct "ASM" as "(W & % & %)". subst. hss. inv G0. 
    rename q0 into u, q1 into ℓ, q4 into idx, q3 into sz, q5 into v, q6 into f.
    iDestruct "IST" as (? ? ? ?) "(%& [%|(P & IST)] &%)";      
      [|iDestruct "IST" as (? ? ? ?) "(% & M)"];
      des; subst; hss.
    { nia. }

    (* SRC: prove the postcond of set *)
    force_l. force_l.
    iSplitL "W". { eauto. }

    (* TGT: compute the input to store *)
    steps_r. hss. steps_r.
    unfold scale_int. des_ifs; cycle 1.
    { exfalso. eapply n. eapply Z.divide_factor_r. }
    rewrite Z_div_mult; try nia.
    s. steps_r.

    (* TGT: inline load *)
    inline_r.

    (* TGT: prove the precond of store *)
    force_r. instantiate (1:= (_, _, _)). force_r. force_r.
    iPoseProof (big_sepL_insert_acc with "M") as "(IP & M)".
    { apply fun_to_list_lookup with (i:=Z.to_nat idx). nia. }
    rewrite Z2Nat.id; try nia.
    iSplitL "IP". { eauto. }

    (* TGT: handle the body of store *)
    apc_r.
    
    (* TGT: handle the postcond of load *)
    steps_r. iDestruct "GRT" as "[[GRT %] %]". subst. hss. steps_r.

    (* prove the IST of Map *)
    step. repeat (iSplit; eauto).
    repeat iExists _. iSplitR; cycle 1.
    - iSplitL; eauto.
      iRight. iFrame. iExists _, _, _, _. iSplitR; eauto.
      iPoseProof ("M" with "GRT") as "M".
      rewrite ->fun_to_list_update, Z2Nat.id; try nia. iFrame.
    - hss.
  Qed.

  Lemma simF_set_by_user:
    HModR.sim_fun MapMMod MapIMod (IstProd [MapM.scope] [MemA.scope] Ist IstEq)
      MapName.set_by_user.
  Proof.
    init_simF.

    (* SRC: handle the IST of Map and the precond of set_by_user *)
    steps_l. iDestruct "ASM" as "(W & % & %)". subst. hss. inv G0.
    rename q0 into u, q1 into ℓ, q3 into idx.

    (* process an input *)
    steps_r. step.
    
    (* SRC: prove the precond of set *)

    steps_l.
    (* TODO: fix the problem with finding a spec  *)
    
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
 


  (*  
  Tactic Notation "_unwrapS" constr(itr) :=
    match itr with
    | (interp_smod _ _ (trigger (Choose _))) =>
      rewrite SModRed.interp_core 
    | (interp_smod _ _ (trigger (Choose _)) >>= _) =>
      rewrite SModRed.interp_core
    | (interp_smod _ _ (trigger (Take _))) =>
      rewrite SModRed.interp_core          
    | (interp_smod _ _ (trigger (Take _)) >>= _) =>
      rewrite SModRed.interp_core    
    | (interp_smod _ _ (trigger (IO _ _))) =>
      rewrite SModRed.interp_core      
    | (interp_smod _ _ (trigger (IO _ _)) >>= _) =>
      rewrite SModRed.interp_core
    | (interp_smod _ _ (trigger (Call _ _))) =>
      rewrite SModRed.interp_call 
    | (interp_smod _ _ (trigger (Call _ _)) >>= _) =>
      rewrite SModRed.interp_call 
    | (interp_smod _ _ (trigger (SPut _ _))) =>
      rewrite SModRed.interp_pg       
    | (interp_smod _ _ (trigger (SPut _ _)) >>= _) =>
      rewrite SModRed.interp_pg 
    | (interp_smod _ _ (trigger (SGet _))) =>
      rewrite SModRed.interp_pg       
    | (interp_smod _ _ (trigger (SGet _)) >>= _) =>
      rewrite SModRed.interp_pg 
    | (interp_smod _ _ (trigger (Assume _))) =>
      rewrite SModRed.interp_Assume             
    | (interp_smod _ _ (trigger (Assume _)) >>= _) =>
      rewrite SModRed.interp_Assume 
    | (interp_smod _ _ (trigger (Guarantee _))) =>
      rewrite SModRed.interp_Guarantee
    | (interp_smod _ _ (trigger (Guarantee _)) >>= _) =>
      rewrite SModRed.interp_Guarantee        
    | _ =>
      grind;
      try rewrite SModRed.interp_tau; 
      try rewrite SModRed.interp_ret; simpl;
      try rewrite! SModRed.interp_bind       
    end.
 *)


  (* rewrite SModRed.interp_apc; *)
  (* st_r; unfold HoareAPC; st_r; rewrite unfold_APC; st_r; *)
  (* match goal with [b: bool|-_] => destruct b end; *)
  (* [|unfold guarantee, triggerNB; st_r; *)
  (*   match goal with [v: void|-_] => destruct v end]. *)

  
  
  (* Tactic Notation "_unwrapS" constr(itr) := *)
  (*   match itr with *)
  (*   | trigger (Choose _) => *)
  (*     rewrite SModRed.interp_core  *)
  (*   | trigger (Take _) => *)
  (*     rewrite SModRed.interp_core           *)
  (*   | trigger (IO _ _) => *)
  (*     rewrite SModRed.interp_core       *)
  (*   | trigger (Call _ _) => *)
  (*     rewrite SModRed.interp_call  *)
  (*   | trigger (SPut _ _) => *)
  (*     rewrite SModRed.interp_pg        *)
  (*   | trigger (SGet _) => *)
  (*     rewrite SModRed.interp_pg        *)
  (*   | trigger (Assume _) => *)
  (*     rewrite SModRed.interp_Assume              *)
  (*   | trigger (Guarantee _) => *)
  (*       rewrite SModRed.interp_Guarantee *)
  (*   | trigger APC => *)
  (*       rewrite SModRed.interp_apc *)
  (*   | _ => fail *)
  (*   end. *)

  (* Tactic Notation "_unwrapP" constr(itr) := *)
  (*   match itr with *)
  (*   | trigger (Choose _) =>  *)
  (*     rewrite PModRed.transl_core       *)
  (*   | trigger (Take _) =>  *)
  (*     rewrite PModRed.transl_core         *)
  (*   | trigger (IO _ _) =>  *)
  (*     rewrite PModRed.transl_core        *)
  (*   | trigger (Call _ _) => *)
  (*     rewrite PModRed.transl_call  *)
  (*   | trigger (SPut _ _) =>  *)
  (*     rewrite PModRed.transl_pg       *)
  (*   | trigger (SGet _) =>  *)
  (*     rewrite PModRed.transl_pg  *)
  (*   | _ =>  *)
  (*     grind; *)
  (*     try rewrite PModRed.transl_tau;  *)
  (*     try rewrite PModRed.transl_ret; simpl; *)
  (*     try rewrite! PModRed.transl_bind *)
  (*   end. *)


  (* Tactic Notation "__unwrap" constr(itr) := *)
  (*   match itr with *)
  (*   | interp_smod _ _ ?itr1 => *)
  (*       _unwrapS itr1 *)
  (*   | (interp_smod _ _ ?itr1) >>= _ => *)
  (*       _unwrapS itr1 *)
  (*   | (PModSem.transl ?itr1) => *)
  (*       _unwrapP itr1 *)
  (*   | (PModSem.transl ?itr1) >>= _ => *)
  (*       _unwrapP itr1 *)
  (*   | (HModSem.sandbox _ ?itr1) => *)
  (*       _unwrapSB itr1 *)
  (*   | (HModSem.sandbox _ ?itr1) >>= _ => *)
  (*       _unwrapSB itr1 *)
  (*   | _=> *)
  (*       _unwrapSB itr *)
  (*   end. *)
    

  
  
  (* Tactic Notation "_unwrap" constr(itr) := *)
  (*   match itr with *)
  (*   | translate _ (?itr0) => __unwrap itr0 *)
  (*   | (translate _ (?itr0)) >>= _  => __unwrap itr0 *)
  (*   | _ => *)
  (*     grind *)
  (*   end. *)

  (* Ltac unwrap_l := *)
  (*   let IT := fresh "__IT" in  *)
  (*   match goal with *)
  (*   | [|- _ (_ (_, ?itr_src) (_, ?itr_tgt))] => *)
  (*     set (IT := itr_tgt);  *)
  (*     try rewrite! HModSB.transl_bind; _unwrap itr_src; *)
  (*     unfold IT; clear IT *)
  (*   end. *)

  (* Ltac unwrap_r := *)
  (*   let IT := fresh "__IT" in  *)
  (*   match goal with *)
  (*   | [|- _ (_ (_, ?itr_src) (_, ?itr_tgt))] =>  *)
  (*     set (IT := itr_src);  *)
  (*     try rewrite! HModSB.transl_bind; _unwrap itr_tgt; *)
  (*     unfold IT; clear IT *)
  (*   end.     *)

  (* Ltac unwrap := unwrap_l; unwrap_r. *)

  (* Ltac force_l := try (unwrap_l; _force_l). *)
  (* Ltac force_r := try (unwrap_r; _force_r). *)



  (* Ltac step := repeat *)
  (*   (unwrap; try _step; simpl; des_pairs). *)

  (* Ltac step_l := let IT := fresh "__IT" in *)
  (*   match goal with [|- _ (_ (_, _) (_, ?itgt))] => set (IT := itgt) end; *)
  (*   repeat (unwrap_l; try _step; simpl; des_pairs); *)
  (*   unfold IT; clear IT. *)

  (* Ltac step_r := let IT := fresh "__IT" in *)
  (*   match goal with [|- _ (_ (_, ?isrc) (_, _))] => set (IT := isrc) end; *)
  (*   repeat (unwrap_r; try _step; simpl; des_pairs); *)
  (*   unfold IT; clear IT. *)

  (* Ltac apc_r := *)
  (*   rewrite SModRed.interp_apc; *)
  (*   step_r; unfold HoareAPC; step_r; rewrite unfold_APC; step_r; *)
  (*   match goal with [b: bool|-_] => destruct b end; *)
  (*   [|unfold guarantee, triggerNB; step_r; *)
  (*     match goal with [v: void|-_] => destruct v end]. *)

  (* (* Lemma transl_unwrapN *) *)
  (* (*   R scopes (r: option R) *) *)
  (* (* : *) *)
  (* (*   translate (HModSem.sandbox scopes) (unwrapN r) = unwrapN r *) *)
  (* (* . *) *)
  (* (* Proof. Admitted. *) *)
