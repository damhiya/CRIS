Require Import CRIS.

Require Import MemA.
Require Import MapHeader MapI MapM.
Require Import wpsim_tactics.

Set Implicit Arguments.

Local Open Scope nat_scope.

(* Auxiliary lemmas *)
Definition fun_to_list (f : Z → Z) (sz : nat) : list val :=
  List.map (λ i : nat, Vint (f i)) (seq 0 sz).

Lemma fun_to_list_repeat (n : nat) : fun_to_list (λ _, 0%Z) n = repeat (Vint 0) n.
Proof.
  rewrite /fun_to_list.
  induction n; eauto.
  replace (S n) with (n+1) by nia.
  rewrite seq_app /= map_app /= IHn repeat_app; ss.
Qed.

Lemma fun_to_list_lookup (f : Z → Z) (sz : nat) (i : nat) (LT : i < sz) :
  fun_to_list f sz !! i = Some (Vint (f i)).
Proof.
  rewrite /fun_to_list list_lookup_fmap lookup_seq_lt; try nia; eauto.
Qed.

Lemma fun_to_list_update (f : Z → Z) (sz : nat) (i : nat) (v : Z) :
  <[i := Vint v]> (fun_to_list f sz) = fun_to_list (<[Z.of_nat i := v]> f) sz.
Proof.
  unfold fun_to_list. revert i. induction sz; i; eauto.
  replace (S sz) with (sz + 1) by nia.
  rewrite !seq_app !map_app.
  assert (CASE : i < sz \/ i >= sz) by nia.
  des.
  - rewrite insert_app_l; cycle 1.
    { rewrite length_map length_seq. nia. }
    rewrite IHsz. s. do 3 f_equal.
    rewrite fn_lookup_insert_ne; eauto. nia.
  - assert (Iadd : List.length (List.map (λ i0 : nat, Vint (f i0)) (seq 0 sz)) + (i - sz) = i).
    { rewrite length_map length_seq. nia. }
    s. rewrite -IHsz -{1 2}Iadd -{4}(app_nil_r (seq 0 sz)) map_app. 
    rewrite !insert_app_r -app_assoc. f_equal. s.
    assert (CASE' : i = sz \/ i > sz) by nia.
    des; subst.
    + rewrite fn_lookup_insert Nat.sub_diag. eauto.
    + rewrite fn_lookup_insert_ne; try nia.
      destruct (i-sz) eqn : EQ; try nia. eauto.
Qed.

Lemma repeat_update {A} i n (v v' w : A):
  <[i:=v]> (repeat v i ++ v' :: repeat w n) = repeat v (i+1) ++ repeat w n.
Proof.
  replace i with (List.length (repeat v i) + 0) at 1; cycle 1.
  { rewrite repeat_length. nia. }
  rewrite ->insert_app_r, repeat_app, <-app_assoc. eauto.
Qed.

(* Simulation proof *)
Module MapIM. Section MapIM.
  Import MapMS.
  Context `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ, !MapMGΓ Γ, !memGΓ Γ}.
  Notation iProp := (iProp Σ).

  (* Context (n : level).
  Definition a : SRFSyn.t n := (∃ b : τ{⇣ Any.t}, ⌜b = b⌝)%SRF. *)

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp :=
    (λ _ st_src st_tgt,
      ⌜st_src = [(MapM.v_size, 0%Z↑); (MapM.v_map, (λ _ : Z, 0%Z)↑)]
        ∧ st_tgt = [(MapI.v_hptr, Vnullptr↑)]⌝
      ∨ pending
        ∗ ∃ blk ofs (f : Z → Z) (sz : Z),
          ⌜st_src = [(MapM.v_size,sz↑);(MapM.v_map,f↑)]
            ∧ st_tgt = [(MapI.v_hptr,(Vptr blk ofs)↑)]⌝
          ∗ (blk, ofs) |-> (fun_to_list f (Z.to_nat sz)))%I.

  Context (υ : univ_id) (n : level) (ginv : invspec).
  Context (SpcMap SpcMem : string → option fspec).
  Hypothesis MapInSpcMap : spc_incl (MapMS.Spc υ n) SpcMap.

  Local Notation MemA := (MemA.t ginv SpcMem).
  Local Notation MapM := (MapM.t υ n ginv SpcMap).
  Local Notation MapMMod := (MapM ★ MemA).
  Local Notation MapIMod := (MapI.t ★ MemA).
  Local Notation IstFull := (IstProd (IstSB MapM.(HMod.scopes) Ist) IstEq).

  Lemma simF_init : HSim.sim_fun open MapMMod MapIMod IstFull MapName.init.
  Proof.
    (* initialize wpsim *)
    unshelve init_wpsim; first exact 1%positive.

    (* preprocess given assumptions *)
    iDestruct "ASM" as "[[[-> %] P] ->]". hss.
    w_steps_l.

    (* SRC: handle the IST of Map and the precond of init *)
    iDestruct "IST" as (????) "([-> ->] & (% & [% | (P' & IST)]) & %)";
      [|iDestruct "IST" as (????) "M"];
      hss; cycle 1.
    { iExFalso. iApply (pending_unique with "P P'"). }
    rename q into sz.

    (* SRC: prove the postcond of init *)
    w_force_l (Vundef ↑).
    w_force_l; iSplitL ""; first done.

    (* TGT : inline alloc *)
    w_steps_r. w_inline_r.

    (* TGT: prove the precond of alloc *)
    w_step_r. w_force_r sz. w_force_r ([Vint sz] ↑).
    w_force_r; iSplit; first done.

    (* TGT: handle the postcond of alloc *)
    w_steps_r. iDestruct "GRT" as "[[%b [-> PTS]] ->]".
    hss. w_steps_r. hss.

    (* prepare and start an induction *)
    replace (repeat Vundef sz) with (repeat (Vint 0) (sz-sz) ++ repeat Vundef sz); cycle 1.
    { rewrite Nat.sub_diag. eauto. }
    rewrite // -[X in ITree.iter _ X](Z.sub_diag (sz%Z)).
    iStopProof. cut (sz <= sz); [|lia].
    generalize sz at 1 4 5 11. intros n'.
    induction n'; i; iIntros "(PD & PTS)".

    (* Base case *)
    { (* TGT : unwind the loop *)
      unfold_iter_r. des_ifs; try nia. w_steps_r.

      (* prove the IST of Map *)
      w_step. repeat (iSplit; eauto).
      iExists [_;_], [_], _, _.
      repeat iSplit; eauto.
      iRight. iFrame. iExists _, _, _, _. iSplitR; eauto.
      rewrite app_nil_r Nat.sub_0_r fun_to_list_repeat Nat2Z.id //=.
    }

    (* Inductive case *)
    { (* TGT : unwind the loop *)
      unfold_iter_r. des_ifs; try nia.
      (* TGT : compute the input to store *)
      unfold scale_int at 1. des_ifs; cycle 1.
      { exfalso. eapply n0. eapply Z.divide_factor_r. }
      s. w_steps_r.
      
      (* TGT : inline store *)
      w_inline_r. w_steps_r.

      (* TGT: prove the precond of store *)
      w_force_r (_, (sz - S n')%Z, _).
      w_force_r ([Vptr _ (sz - (S n'))%Z; _]↑).
      w_force_r.
      iPoseProof (big_sepL_insert_acc with "PTS") as "(PT & CTN)".
      { instantiate (2:= (sz - (S n'))).
        rewrite lookup_app_r; rewrite repeat_length; try nia.
        rewrite Nat.sub_diag. s. eauto.
      }
      rewrite !Z.add_0_l Nat2Z.inj_sub; try nia.
      (* , Zpos_P_of_succ_nat, <-Nat2Z.inj_succ, Nat2Z.inj_sub; try nia. *)
      iSplitL "PT".
      { iSplitL; cycle 1.
        { iPureIntro. do 3 f_equal. rewrite Z.div_mul; nia. }
        iExists Vundef. iFrame.
        iPureIntro. do 3 f_equal. rewrite Z.div_mul; nia.
      }

      (* TGT: handle the postcond of store *)
      w_steps_r. iDestruct "GRT" as "[[GRT ->] ->]". hss.
      iSpecialize ("CTN" $! (Vint 0)). iPoseProof ("CTN" with "GRT") as "PTS".
      (* rewrite -> !Zpos_P_of_succ_nat, <-!Nat2Z.inj_succ. *)
      replace (sz - S n' + 1)%Z with (sz - n')%Z by nia.

      (* apply the induction hypothesis and complete *)
      w_steps_r.
      iApply IHn'; try nia. iFrame.
      rewrite repeat_update.
      eapply eq_ind; [iAssumption |].
      do 3 f_equal. nia.
    }
  Qed.

  Lemma simF_get : HSim.sim_fun open MapMMod MapIMod IstFull MapName.get.
  Proof.
    init_wpsim.

    (* SRC: handle the IST of Map and the precond of get *)
    iDestruct "ASM" as "[-> ->]". hss.
    w_steps_l.
    iDestruct "IST" as (? ? ? ?) "(%& (% & [%|(P & IST)]) &%)";
      [|iDestruct "IST" as (? ? ? ?) "(% & M)"];
      des; hss.
    { nia. }
    rename q0 into sz.
    rename q into idx.
    
    (* SRC: prove the postcond of get *)
    w_force_l. w_force_l. iSplitL "". { eauto. }

    (* TGT : compute the input to load *)
    w_steps_r. hss. w_steps_r.
    unfold scale_int. des_ifs; cycle 1.
    { exfalso. eapply n0. eapply Z.divide_factor_r. }
    s. w_steps_r. rewrite Z_div_mult; try nia.

    (* TGT : inline load *)
    w_inline_r.

    (* TGT: prove the precond of load *)
    w_step_r. w_force_r (_, (ofs + _)%Z, _). w_force_r. w_force_r.
    iPoseProof (big_sepL_lookup_acc with "M") as "(IP & M)".
    { apply fun_to_list_lookup with (i:=Z.to_nat idx). nia. }
    rewrite Z2Nat.id; try nia.
    iSplitL "IP"; eauto.
    
    (* TGT: handle the postcond of load *)
    w_steps_r. iDestruct "GRT" as "[[GRT ->] ->]". hss. w_steps_r.

    (* prove the IST of Map *)
    w_step. repeat (iSplit; eauto).
    iExists [_;_], [_], _, _.
    do 3 (iSplit; eauto).
    iRight. iFrame. iExists _, _, _, _. iSplit; eauto.
    iPoseProof ("M" with "GRT") as "M". iFrame.
    Unshelve. exact 1%positive.
  Qed.

  Lemma simF_set : HSim.sim_fun open MapMMod MapIMod IstFull MapName.set.
  Proof.
    init_wpsim.
    destruct q as [k v]; s; iDestruct "ASM" as "[-> ->]".

    (* SRC: handle the IST of Map and the precond of set *)
    w_steps_l. hss. inv G0.
    iDestruct "IST" as (? ? ? ?) "(%& (% & [%|(P & IST)]) &%)";
      [|iDestruct "IST" as (? ? ? ?) "(% & M)"];
      des; hss.
    { nia. }
    rename q1 into idx.

    (* TGT : compute the input to store *)
    w_steps_r. hss. w_steps_r.
    unfold scale_int. des_ifs; cycle 1.
    { exfalso. eapply n0. eapply Z.divide_factor_r. }
    rewrite Z_div_mult; try nia.
    s. w_steps_r.

    (* TGT : inline load *)
    w_inline_r.

    (* TGT: prove the precond of store *)
    w_step_r. w_force_r (blk, (ofs + idx)%Z, _). w_force_r. w_force_r.
    iPoseProof (big_sepL_insert_acc with "M") as "(IP & M)".
    { apply fun_to_list_lookup with (i:=Z.to_nat idx). hss. nia. }
    rewrite Z2Nat.id; try nia.
    iSplitL "IP". { eauto. }

    (* TGT: handle the postcond of load *)
    w_steps_r. iDestruct "GRT" as "[[GRT ->] ->]". hss. w_steps_r.

    (* SRC: prove the postcond of set *)
    w_force_l. w_force_l. iSplitL "". { eauto. }

    (* prove the IST of Map *)
    w_step. repeat (iSplit; eauto).
    iExists [_;_], [_], _, _.
    do 3 (iSplit; eauto).
    iRight. iFrame. iExists _, _, _, _. iSplit; eauto.
    iPoseProof ("M" with "GRT") as "M".
    rewrite -> fun_to_list_update, Z2Nat.id; try nia. iFrame.
    Unshelve. exact 1%positive.
  Qed.

  Lemma simF_set_by_user : HSim.sim_fun open MapMMod MapIMod IstFull MapName.set_by_user.
  Proof.
    init_wpsim.
    iDestruct "ASM" as "[-> ->]".

    (* SRC: handle the IST of Map and the precond of set_by_user *)
    hss. w_steps_l. rename q into k.

    (* process an input *)
    w_steps_r. w_step.
    
    (* SRC: prove the precond of set *)
    w_steps_l. w_force_l (_,_); s. w_force_l. w_force_l.
    iSplitL "". { eauto. }

    (* make a call to set *)
    w_steps_r. w_call "IST".

    (* SRC: handle the postcond of set *)
    w_steps_l. iDestruct "ASM" as "(_ & ->)". hss.

    (* SRC: prove the postcond of set_by_user *)
    w_force_l. w_force_l. iSplitL "". { eauto. }

    (* prove the IST of Map *)
    w_steps_r. hss. w_steps_r. w_step. eauto.
    Unshelve. exact 1%positive.
  Qed.

  Theorem sim : HSim.t open MapMMod MapIMod MapM.InitCond IstFull.
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
End MapIM. End MapIM.