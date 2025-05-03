Require Import CRIS.
Require Import MemHeader MemA MemI.
Require Import ImpPrelude.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section AUX.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_memG: !memG}.

  Fixpoint is_list (ll: val) (xs: list val): iProp Σ :=
    match xs with
    | [] => (⌜ll = Vnullptr⌝)%I
    | xhd :: xtl =>
      (∃ lhd ltl, ⌜ll = Vptr (lhd, 0%Z)⌝ ∗ (lhd, 0%Z) |-> [xhd; ltl] ∗ is_list ltl xtl)%I
    end.

  Lemma unfold_is_list ll xs:
    is_list ll xs = 
    match xs with
    | [] => (⌜ll = Vnullptr⌝)%I
    | xhd :: xtl =>
      (∃ lhd ltl, ⌜ll = Vptr (lhd, 0%Z)⌝ ∗ (lhd, 0%Z) |-> [xhd; ltl] ∗ is_list ltl xtl)%I
    end.
  Proof using. destruct xs; ss. Qed.

  Lemma unfold_is_list_cons ll xhd xtl:
    is_list ll (xhd :: xtl) =
    (∃ lhd ltl, ⌜ll = Vptr (lhd, 0%Z)⌝ ∗ (lhd, 0%Z) |-> [xhd; ltl] ∗ is_list ltl xtl)%I.
  Proof using. eapply unfold_is_list. Qed.

  Lemma is_list_wf ll xs:
    (is_list ll xs) -∗ (⌜(ll = Vnullptr) ∨ (match ll with | Vptr (_, 0%Z) => True | _ => False end)⌝).
  Proof using.
    iIntros "L". destruct xs; ss; et.
    { iPure "L" as L. iPureIntro. et. }
    iDestruct "L" as (? ?) "(% & P & L)".
    iPureIntro; right; subst; ss.
  Qed.

End AUX.

Ltac Ztac := all_once_fast ltac:(fun H => first[apply Z.leb_le in H|apply Z.ltb_lt in H|apply Z.leb_gt in H|apply Z.ltb_ge in H|idtac]).

Section AUX2.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_memG: !memG}.
  
  Lemma repeat_nth_some
  X (x: X) sz ofs
  (IN: ofs < sz)
  :
  nth_error (repeat x sz) ofs = Some x
  .
  Proof using _memG.
    ginduction sz; ii; ss.
    - lia.
    - destruct ofs; ss. exploit IHsz; et. lia.
  Qed.

  Lemma repeat_nth_none
    X (x: X) sz ofs
    (IN: ~(ofs < sz))
    :
    nth_error (repeat x sz) ofs = None
    .
  Proof using.
    generalize dependent ofs. induction sz; ii; ss.
    - destruct ofs; ss.
    - destruct ofs; ss. { lia. } hexploit (IHsz ofs); et. lia.
  Qed.

  Lemma nth_error_empty
    {X: Type} ofs
    :
    nth_error ([]: list X) ofs = None.
  Proof using.
    unfold nth_error. destruct ofs; ss.
  Qed.

  Lemma Z2nat_lt (x0: Z) (sz : nat)
    (ZLT: (x0 < sz)%Z)
    (SZ: (0 < sz))
  :
    (Z.to_nat x0 < sz).
  Proof using.
    induction sz.
    - lia.
    - induction x0.
      * ss.
      * ss. 
      assert (Z.succ sz = sz + 1)%Z. ss.  
      apply Z2Nat.inj_lt in ZLT; try lia.
      * ss.
  Qed.

  Lemma Z_ne_le (z1 : Z) (z2 : Z)
    (NE: z1 ≠ z2)
    (LE: (z1 <=? z2)%Z)
  :
    (z1 < z2)%Z.
  Proof using.
    apply Z.leb_le in LE.
    destruct (Z.eq_dec z1 z2) as [Heq | Hneq].
  - (* Case: z1 = z2 (contradiction) *)
    contradiction.
  - (* Case: z1 ≠ z2 *)
    lia.
  Qed. (* Use NE and LE to conclude (z1 < z2)%Z *)

End AUX2.

Section RA.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_memG: !memG}.

  Definition mem_wf (m0: Mem.t): Prop :=
    forall b ofs v, m0.(Mem.cnts) b ofs = Some v -> <<NB: b < m0.(Mem.nb)>>
  .

  Definition sim_loc (loc_res: option (frac_valO)) (v: option val) : Prop :=
    match loc_res, v with
    | Some (q, Excl v'), Some v'' => q = 1%Qp ∧ v' = v''
    | None, None => True
    | _, _ => False
    end.

  Lemma mem_alloc γ (mem_src : _memRA) mem_tgt blk sz pad
    (BLK: blk = Mem.nb mem_tgt + pad)
    (WF: mem_wf mem_tgt)
    (SIM: ∀ b ofs, sim_loc (mem_src b ofs) (Mem.cnts mem_tgt b ofs))
  :
    own γ ((● mem_src): memRA)
    ⊢ |==> own γ ((● (mem_src ⋅ _points_to_r (blk, 0%Z) 1 (repeat Vundef sz))): memRA)
           ∗ own γ ((◯ _points_to_r (blk, 0%Z) 1 (repeat Vundef sz)): memRA).
  Proof using _memG.
    iIntros "S".
    iAssert _ with "[S]" as "B".
    { iApply (own_update with "S"). apply auth_update_alloc.
      instantiate (1:=_points_to_r (blk, 0%Z) 1 (repeat Vundef sz)).
      instantiate (1:=mem_src ⋅ _points_to_r (blk, 0%Z) 1 (repeat Vundef sz)).
      apply local_update_discrete.
      ii. split; ii; rewrite ! discrete_fun_lookup_op; rewrite /_points_to_r; ss; des_ifs.
      - bsimpl. des. des_sumbool. subst. hexploit (SIM (Mem.nb mem_tgt + pad) x0).
        intro T. unfold sim_loc in T.
        des_ifs. des. hss. exploit WF; et. i; des. lia.
      - rewrite right_id. specialize (H x x0); et.
      - rewrite right_id. specialize (H x x0); et.
      - i. destruct mz. 
        { ss. rewrite left_id in H0. specialize (H0 x x0).
          rewrite !discrete_fun_lookup_op H0 comm //. des_ifs. }
        { ss. specialize (H0 x x0). rewrite H0 left_id //. des_ifs. }
      - rewrite right_id. destruct mz.
        { ss. rewrite left_id in H0. specialize (H0 x x0).
          rewrite !discrete_fun_lookup_op H0 comm //. des_ifs. rewrite right_id //. }
        { ss. specialize (H0 x x0). rewrite H0 left_id //. des_ifs. }
      - rewrite right_id. destruct mz.
        { ss. rewrite left_id in H0. specialize (H0 x x0).
          rewrite !discrete_fun_lookup_op H0 comm //. des_ifs. rewrite right_id //. }
        { ss. specialize (H0 x x0). rewrite H0 left_id //. des_ifs.
          destruct dec; bsimpl; des; Ztac; ss; try nia. }
    }
    iDestruct "B" as ">[B W]". iFrame; et.
  Qed.

  Lemma split_points_to_r blk ofs q a l :
    _points_to_r (blk, ofs) q (a :: l)
    ≡ (_points_to_r (blk, ofs) q [a]) ⋅ (_points_to_r (blk, (ofs+1)%Z) q l).
  Proof using _memG.
    intros b o. rewrite !discrete_fun_lookup_op. ss.
    destruct (dec b blk).
    - subst. destruct (dec o ofs).
      + subst. ss. des_ifs; bsimpl; des; Ztac; try nia.
        { rewrite right_id. rewrite ->Z.sub_diag in *. ss. inv Heq0. ss. }
        { rewrite ->Z.sub_diag in *; ss. }
        { rewrite ->Z.sub_diag in *; ss. }
      + des_ifs; bsimpl; des; Ztac; try nia.
        { rewrite left_id. replace (o - (ofs + 1))%Z with (o - ofs - 1)%Z  in Heq3 by nia.
          replace (Z.to_nat (o - ofs)) with (S (Z.to_nat (o - ofs - 1))) in Heq0 by nia.
          ss. rewrite Heq0 in Heq3. inv Heq3. ss. }
        { replace (o - (ofs + 1))%Z with (o - ofs - 1)%Z  in Heq3 by nia.
          replace (Z.to_nat (o - ofs)) with (S (Z.to_nat (o - ofs - 1))) in Heq0 by nia.
          ss. rewrite Heq0 in Heq3. inv Heq3. }
        { replace (o - (ofs + 1))%Z with (o - ofs - 1)%Z  in Heq3 by nia.
          replace (Z.to_nat (o - ofs)) with (S (Z.to_nat (o - ofs - 1))) in Heq0 by nia.
          ss. rewrite Heq0 in Heq3. inv Heq3. }
    - des_ifs.
  Qed.

  Lemma points_to_singleton blk ofs q a :
    _points_to_r (blk, ofs) q [a]
    ≡ (discrete_fun_singleton blk (discrete_fun_singleton ofs (Some (q, Excl a)))).
  Proof using _memG.
    intros b o. ss. des_ifs; destruct dec; bsimpl; des; Ztac; try nia.
    - replace o with ofs in * by nia. rewrite Z.sub_diag in Heq0. ss. inv Heq0.
      rewrite !discrete_fun_lookup_singleton //.
    - replace o with ofs in * by nia. rewrite Z.sub_diag in Heq0. ss.
    - subst. rewrite discrete_fun_lookup_singleton discrete_fun_lookup_singleton_ne; [eauto|nia].
    - subst. rewrite discrete_fun_lookup_singleton discrete_fun_lookup_singleton_ne; [eauto|nia].
    - rewrite discrete_fun_lookup_singleton_ne; eauto.
  Qed.

  Local Transparent mem_points_to_singleton_r.

  Lemma points_to_transform blk ofs q l :
    own base_γ ((◯ _points_to_r (blk, ofs) q l): memRA)
    ⊢ [∗ list] i↦v ∈ l, (blk, (ofs + i)%Z) |={q}=> v.
  Proof using _memG.
    gen ofs. induction l.
    - iIntros; eauto.
    - i. rewrite split_points_to_r. iIntros "[P L]".
      rewrite big_sepL_cons. rewrite points_to_singleton.
      iPoseProof (IHl with "L") as "L".
      set (λ _ _, _). set (λ _ _, _).
      assert (y = y0).
      { extensionalities. subst y y0. ss.
        replace (ofs + 1 + H)%Z with (ofs + S H)%Z by nia. refl. }
      rewrite H. iFrame. unfold mem_points_to_singleton, mem_points_to_singleton_r; ss.
      rewrite Z.add_0_r. iFrame.
  Qed. 

End RA.

Module MemIA. Section MemIA.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_memG: !memG}.

  Context (csl : string → bool).
  Context (genv : GEnv.t).
  Context (sp : string → option fspec).
  Context (MemInSpMem: sp_incl MemA.sp sp).

  Definition Ist: nat -> alist key Any.t -> alist key Any.t -> iProp Σ :=
    fun _ st_src st_tgt =>
      ( (∃ (mem_tgt: Mem.t) (memk_src: _memRA),
        (⌜(<<TGT: st_tgt = [(MemI.v_mem, mem_tgt↑)] >>) ∧
        (<<SIM: forall (b: mblock) (ofs: Z),
              sim_loc (memk_src b ofs) (mem_tgt.(Mem.cnts) b ofs)>>) ∧
        (<<WFTGT: mem_wf mem_tgt>>)⌝)
      ∗
        (own base_γ ((● (memk_src : _memRA)): memRA))
      ))%I.

  Local Definition MemA := (MemA.t sp).
  Local Definition MemI := (MemI.t csl genv).
  Local Definition IstFull := (IstProd (IstSB MemA.(HMod.scopes) Ist) IstEq).

  Lemma simF_alloc : HSim.sim_fun open MemA MemI IstFull MemHdr.alloc.
  Proof using MemInSpMem.
    init_simF.
    steps_l.
    iDestruct "ASM" as "(% & %)". des; subst; hss.

    steps_r.  iDestruct "IST" as (? ? ? ?) "(% & [% IST] & %)".
    unfold Ist. iDestruct "IST" as (? ?) "[% B]". des; subst; hss.
    steps_r. des_ifs.
    2:{ rewrite andb_false_iff in Heq. des; des_sumbool; nia. }

    steps_r. unfold alist_upd, _alist_upd. ss.
    rename q0 into pad. rename q into sz. set (blk := Mem.nb mem_tgt + pad).
    iPoseProof (own_valid with "B") as "%".
    iPoseProof (mem_alloc with "B") as ">B"; et.
    iDestruct "B" as "[BLK WHT]".
    forces_l. iSplitL "WHT". 
    { instantiate (1:= (Vptr (blk, 0%Z)) ↑). instantiate (1:= (Vptr (blk, 0%Z)) ↑). iSplitL; et.
      iExists blk. iSplitR; et. instantiate (1:=sz). instantiate (1:=pad).
      iPoseProof (points_to_transform with "WHT") as "WHT". iFrame. }
    steps_l.
    step. iSplit; et.
    iExists st_srcL, [_], st_tgtR, st_tgtR. iSplit; et; iSplit; et.
    iSplit; et. iExists _, _. iFrame. esplits; et. iPureIntro. splits; et.
    - ii. destruct (mem_tgt.(Mem.cnts) blk ofs) eqn:E.
      { exfalso. exploit WFTGT; et. i; des. lia. }
      ss. exploit SIM; et. instantiate (2:= blk). instantiate (1:= ofs).
      rewrite E. intro U. unfold sim_loc in U. des_ifs.
      rewrite /_points_to_r. rewrite !discrete_fun_lookup_op.
      destruct (AList.dec b blk); subst; ss.
      * rewrite repeat_length. rewrite Z.add_0_l.
        unfold AList.update. des_ifs_safe. rewrite Heq0.
        rewrite left_id. des_ifs; bsimpl; hss; des_sumbool.
        rewrite repeat_nth_some in Heq2.
        hss. Ztac; nia. Ztac.
        rewrite repeat_nth_some in Heq2; ss; nia.
        subst blk; ss.
      * unfold AList.update in *. destruct (dec blk b); subst; ss.
        des_ifs; bsimpl; destruct dec; des; subst; ss; rewrite right_id; eauto.
    - clear - WFTGT. ii. ss. 
      unfold AList.update in *. des_ifs. exploit WFTGT; et. i; des. r; lia.
  (*SLOW*)Qed.

  Lemma simF_free : HSim.sim_fun open MemA MemI IstFull MemHdr.free.
  Proof using MemInSpMem.
    init_simF.
  
    steps_l. iDestruct "ASM" as "((% & % & P) & %)". des; subst; hss.
    steps_r.
    
    iDestruct "IST" as (? ? ? ?) "(% & [% IST] & %)".
    unfold Ist. iDestruct "IST" as (? ?) "[% B]". des; subst; hss.
    steps_r.
    rename q1 into b. rename q2 into ofs.
  
    iCombine "B P" as "P". 
    iPoseProof (own_valid with "P") as "%WF".
    assert (HIT: memk_src b ofs ≡ Some (1%Qp, Excl v)).
    { clear - WF.
      dup WF. rewrite auth_both_valid_discrete in WF. ss. des.
      
      unfold included in *. des.
      specialize (WF b ofs). 
      iris_tac.
      rewrite ->!discrete_fun_lookup_singleton in *.
      unfold base.length in WF. ss.
      destruct z.
      - des_ifs; bsimpl; des; des_sumbool; hss; iris_tac. 
        destruct c. specialize (WF1 b ofs). rewrite WF in WF1.
        rewrite Some_op_opM in WF1.
        ss. cmra_tac. destruct c. ss. 
        cmra_tac. iris_tac.  
      - rewrite right_id //.
    }
    (* memory after free *)
    set (memk_src1 := fun _b _ofs => if eq_dec _b b && eq_dec _ofs ofs 
                                     then (ε)
                                     else memk_src _b _ofs).
  
    assert (✓ (memk_src1: _memRA)).
    { clear -WF. subst memk_src1. ii. des_ifs. ss.
      apply cmra_valid_op_l in WF. iris_tac. apply WF.
    }
  
    hexploit (SIM b ofs). intro B.
    unfold Mem.free. des_ifs; unfold sim_loc in B; des_ifs; inv HIT. hss.
    steps_r.
  
    iAssert _ with "[P]" as "P".
    { (* update resource according to freeing *)
      iApply (own_update with "P").
      eapply auth_update_dealloc. hss.
      instantiate (1:=memk_src1).
      apply local_update_discrete.
      i. ss. split. ss. 
      destruct mz.
      { ss. subst memk_src1. rewrite left_id. intros b0 ofs0.
        specialize (H3 b0 ofs0). des_ifs; bsimpl; des; des_sumbool; subst.
        { rewrite !discrete_fun_lookup_op in H3.
          des_ifs. rewrite (@UIP _ _ _ e eq_refl) in H3. ss.
          rewrite discrete_fun_lookup_singleton in H3.
          destruct (c b ofs); ss. destruct c0; ss.
          rewrite -Some_op -pair_op frac_op in H3.
          specialize (H1 b ofs). rewrite H3 in H1. inv H1.
        }
        { rewrite !discrete_fun_lookup_op in H3. des_ifs. rewrite H3 left_id //. }
        { rewrite !discrete_fun_lookup_op in H3. des_ifs.
          { ss. rewrite discrete_fun_lookup_singleton_ne in H3; et. rewrite H3 left_id //. }
          { rewrite H3 left_id //. }
        }
      }
      { ss. subst memk_src1. intros b0 ofs0.
        specialize (H3 b0 ofs0). des_ifs; bsimpl; des; des_sumbool; subst.
        { des_ifs. }
        { des_ifs. ss. rewrite discrete_fun_lookup_singleton_ne in H3; et. }
      }
    }
    iMod "P".
    
    force_l. steps_l. forces_l. iSplitR; et. steps_l.
    step. iSplit; et.
  
    iFrame. iExists st_srcL, [_], st_tgtR, st_tgtR. iSplit; et. iSplit; et.
    iSplit; et. iExists _. iFrame. iPureIntro. esplits; et.
    - i. destruct (classic (b = b0 ∧ ofs = ofs0)); des; clarify.
      + unfold AList.update. ss. subst memk_src1. des_ifs.
        bsimpl; des_sumbool; ss.
      + unfold AList.update. ss. subst memk_src1. des_ifs; bsimpl; des; des; des_sumbool; ss; clarify.
    - ii. ss. unfold AList.update in *. des_ifs; et.
  (*SLOW*)Qed.

  Lemma sim_load fls flt υ ν r g ps pt nths st_s st_t bofs q v:
    IstFull nths st_s st_t ∗ bofs |={q}=> v
    ⊢ wsim fls flt IstFull None υ ν ⊤ r g _ _
      (fun nths '(st_s,_) '(st_t,r) => IstFull nths st_s st_t ∗ bofs |={q}=> v ∗ ⌜r = v⌝)
      ps pt nths (st_s, Ret ()) (st_t, HModTr.sandbox mask_all MemI.scopes (PModTr.trans (MemI.load [Vptr bofs]))).
  Proof using MemInSpMem.
    intros. iIntros "(IST & P)".
    unfold MemI.load. destruct bofs as [b ofs].

    steps_r. iDestruct "IST" as (? ? ? ?) "(% & [% IST] & %)".
    unfold Ist. iDestruct "IST" as (? ?) "[% B]". des; subst; hss.
    steps_r.

    iCombine "B P" as "P". iPoseProof (own_valid with "P") as "%WF". 
    assert (HIT: memk_src b ofs ≡ Some (q%Qp, Excl v)).
    { clear - WF.
      dup WF. rewrite auth_both_valid_discrete in WF. ss. des.
      unfold included in *. des.
      specialize (WF b ofs). 
      iris_tac.
      rewrite ->!discrete_fun_lookup_singleton in *.
      destruct (z b ofs).
      - destruct c. specialize (WF1 b ofs). rewrite WF in WF1. inv WF1; ss.
      - rewrite right_id //.
    }
    des. hexploit (SIM b ofs). intro T. 
    
    iDestruct "P" as "[BLK WHT]".
    unfold sim_loc in T. des_ifs; bsimpl; des; des_sumbool; Ztac; inv HIT. hss.
    steps_r.
    step. iFrame. iSplit; et.
    iExists _, [_], _, _. repeat iSplit; et.
  (*SLOW*)Qed.

  Lemma simF_load : HSim.sim_fun open MemA MemI IstFull MemHdr.load.
  Proof using MemInSpMem.
    init_simF.

    steps_l. iDestruct "ASM" as "([% P] & %)". subst; hss.
    rename q5 into b, q6 into ofs.

    add_ret_l (). red_ret_r. rewrite PRed.bind SBRed.bind.
    iApply wsim_bind. iSplitL "IST P".
    { iApply sim_load; eauto; iFrame. }
    clear nths NODS st_src NODD st_tgt.
    iIntros (nths st_s r_s st_t r). hss.
    iIntros "(IST & P & <-)".
    
    force_l. steps_l. forces_l. iSplitL "P"; iFrame; et. steps_l.
    step. iFrame. eauto.
  (*SLOW*)Qed.

  Lemma sim_store fls flt υ ν r g ps pt nths st_s st_t bofs v_old v:
    IstFull nths st_s st_t ∗ bofs ↦ v_old
    ⊢ wsim fls flt IstFull None υ ν ⊤ r g _ _
      (fun nths '(st_s,_) '(st_t,r) => IstFull nths st_s st_t ∗ bofs ↦ v ∗ ⌜r = Vint 0⌝)
      ps pt nths (st_s, Ret ()) (st_t, HModTr.sandbox mask_all MemI.scopes (PModTr.trans (MemI.store [Vptr bofs; v]))).
  Proof using MemInSpMem.
    intros. iIntros "(IST & P)".
    unfold MemI.store. destruct bofs as [b ofs].

    steps_r. iDestruct "IST" as (? ? ? ?) "(% & [% IST] & %)".
    unfold Ist. iDestruct "IST" as (? ?) "[% B]". des; subst; hss.
    steps_r.

    iCombine "B P" as "P". 
    iPoseProof (own_valid with "P") as "%WF".
    assert (HIT: memk_src b ofs ≡ Some(1%Qp, Excl v_old)).
    { clear - WF.
      dup WF. rewrite auth_both_valid_discrete in WF. ss. des.
      
      unfold included in *. des.
      specialize (WF b ofs). 
      iris_tac.
      rewrite ->!discrete_fun_lookup_singleton in *.
      destruct (z b ofs).
      - destruct c. specialize (WF1 b ofs). rewrite WF in WF1. inv WF1; ss.
      - rewrite right_id //.
    }
    hexploit (SIM b ofs). intro T.  

    (* memory after storing *)
    set (memk_src1 := 
      fun _b _ofs => if Nat.eq_dec _b b && Z.eq_dec _ofs ofs 
                     then (Some(1%Qp, Excl v)) 
                     else (memk_src _b _ofs)).
    assert (WF': ✓ (memk_src1 : _memRA)).
    { clear -WF. subst memk_src1.  ii. dup WF. rewrite auth_both_valid_discrete in WF.
      ss. des. des_ifs. bsimpl; ss; des; subst; apply WF1. }
    
    iAssert _ with "[P]" as "P".
    { (* update resource according to storing *)
      iApply (own_update with "P"). ss.
      apply auth_update with (a':=memk_src1) (b':=_points_to_r (b, ofs) 1%Qp [v]).
      apply local_update_discrete. 
      ss; des_ifs; des; subst.
      clear - WF WF'. ii. ss. split. hss.
      destruct mz; ss. 
      - intros b0 ofs0. rewrite !discrete_fun_lookup_op. subst memk_src1. ss.
        des_ifs; bsimpl; ss; des; subst; des_sumbool;
        hss; Ztac; try rewrite Z.sub_diag in Heq1;
        try rewrite left_id; try lia; hss; try hexploit (H0 x x0); i; try rewrite H1;
        try rewrite ! discrete_fun_lookup_op;
        try rewrite unfold_points_to_r; des_ifs; hss;
        bsimpl; des; des_sumbool; Ztac; hss; try rewrite Z.sub_diag in Heq0; ss; hss; try rewrite left_id; try lia; ss.
        { rewrite H0 in H.
          hexploit (H b ofs). i. rewrite ! discrete_fun_lookup_op in H1.
          des_ifs. rewrite (@UIP _ _ _ e eq_refl) in H1. ss.
          rewrite discrete_fun_lookup_singleton in H1. destruct (c b ofs); inv H1; ss. }
        { hexploit (H0 b0 ofs0). i. rewrite !discrete_fun_lookup_op in H1.
          des_ifs. rewrite H1 left_id //. }
        { hexploit (H0 b0 ofs0). i. rewrite !discrete_fun_lookup_op in H1.
          des_ifs. rewrite H1 left_id //. }
        { hexploit (H0 b0 ofs0). i. rewrite !discrete_fun_lookup_op in H1.
          des_ifs. rewrite H1 left_id //. }
        { hexploit (H0 b0 ofs0). i. rewrite !discrete_fun_lookup_op in H1.
          des_ifs; ss.
          { rewrite H1 discrete_fun_lookup_singleton_ne // left_id //. }
          { rewrite H1 left_id //. }
        }
        { hexploit (H0 b0 ofs0). i. rewrite !discrete_fun_lookup_op in H1.
          des_ifs. rewrite H1 left_id //. }
        { hexploit (H0 b0 ofs0). i. rewrite !discrete_fun_lookup_op in H1.
          des_ifs; ss.
          { rewrite H1 discrete_fun_lookup_singleton_ne // left_id //. }
          { rewrite H1 left_id //. }
        }
      - unfold discrete_fun_singleton, discrete_fun_insert. des_ifs; ss; des_ifs; ss;
        subst memk_src1; ss; des_ifs; bsimpl; des; des_sumbool; Ztac; hss; 
        try rewrite Z.sub_diag in Heq0; ss; hss; try lia; 
        try hexploit (H0 x x0); i; try rewrite H1; intros b0 ofs0; des_ifs; hss; 
        bsimpl; des; des_sumbool; Ztac; hss; try rewrite Z.sub_diag in Heq0; ss; hss; try lia.
        { rewrite Z.sub_diag in Heq1. ss. inv Heq1; ss. }
        { rewrite Z.sub_diag in Heq1; ss. }
        { hexploit (H0 b0 ofs0). i. des_ifs. }
        { hexploit (H0 b0 ofs0). i. des_ifs. }
        { hexploit (H0 b0 ofs0). i. des_ifs. }
        { hexploit (H0 b0 ofs0). i. des_ifs. ss. rewrite discrete_fun_lookup_singleton_ne in H1; et. }
        { hexploit (H0 b0 ofs0). i. des_ifs. }
        { hexploit (H0 b0 ofs0). i. des_ifs. ss. rewrite discrete_fun_lookup_singleton_ne in H1; et. }
    }

    iMod "P". iDestruct "P" as "[BLK WHT]".
    unfold Mem.store. des_ifs; unfold sim_loc in T; des_ifs; inv HIT.
    steps_r. step.
    iFrame. iSplitR "WHT".
    { iExists _, [_], _, _. repeat iSplit; et.
      iExists _. iPureIntro. esplits; et.
      - i. cbn. des_ifs; bsimpl; des; des_sumbool; subst memk_src1; ss; des_ifs; bsimpl; des; des_sumbool; try nia.
      - ii. r. cbn in *. 
    unfold sim_loc in T. des_ifs; bsimpl; des; des_sumbool; try nia; subst; exploit WFTGT; et.
    }
    iPoseProof (points_to_transform with "WHT") as "WHT".
    ss. rewrite Z.add_0_r. iDestruct "WHT" as "[WHT _]"; et.
  (*SLOW*)Qed.

  Lemma simF_store : HSim.sim_fun open MemA MemI IstFull MemHdr.store.
  Proof using MemInSpMem.
    init_simF.

    steps_l. iDestruct "ASM" as "((% & % & P) & %)". subst; hss.
    rename q3 into b, q4 into ofs.

    add_ret_l (). red_ret_r. rewrite PRed.bind SBRed.bind.
    iApply wsim_bind. iSplitL "IST P".
    { iApply sim_store; eauto; iFrame. }
    clear nths NODS st_src NODD st_tgt.
    iIntros (nths st_s r_s st_t r). hss.
    iIntros "(IST & P & ->)".
    
    force_l. steps_l. forces_l. iSplitL "P"; et.
    step. eauto.
  (*SLOW*)Qed.

  Lemma simF_cmp : HSim.sim_fun open MemA MemI IstFull MemHdr.cmp.
  Proof using MemInSpMem.
    init_simF.
    
    steps_l. destruct q. destruct x.
    { (* cmp spec 0 *)
      ss. unfold precond. ss. destruct m. destruct p. destruct p. cbn.
      iDestruct "ASM" as "([% P] & %)". subst; hss.
      rename n into b, z into ofs.
      
      steps_r. 

      steps_r. iDestruct "IST" as (? ? ? ?) "(% & [% IST] & %)".
      unfold Ist. iDestruct "IST" as (? ?) "[% B]". des; subst; hss.
      steps_r.

      iCombine "B P" as "P". iPoseProof (own_valid with "P") as "%WF".
      assert (HIT: ∃ q, memk_src b ofs ≡ Some (q, Excl v)).
      { clear - WF.
        dup WF. rewrite auth_both_valid_discrete in WF. ss. des.
        unfold included in *. des.
        unfold cmra.op in WF. unfold cmra_op in WF. hss. unfold ucmra_op in WF.
        hss. 
        unfold discrete_fun_op_instance in WF. 
        specialize (WF b ofs). 
        rewrite ! discrete_fun_lookup_op in WF.
        rewrite !discrete_fun_lookup_singleton in WF.
        destruct (z b ofs).
        - destruct c. specialize (WF1 b ofs). rewrite WF in WF1. inv WF1; ss.
        - rewrite right_id in WF. eauto.
      }
      des. hexploit (SIM b ofs). intro T.  unfold sim_loc in T.

      des_ifs; bsimpl; des; des_sumbool; unfold Mem.valid_ptr, is_some in *; des_ifs.
      - steps_r. force_l. steps_l. forces_l.
        iDestruct "P" as "[P Q]".
        iSplitL "Q".
        { iFrame. iSplit; et. }
        steps_l. step. iSplit; et.
        { iFrame. iExists _, [_], _, _. repeat iSplit; et. }
      - inv HIT.
    }

    destruct x.
    { (* cmp spec 1 *)
      ss. unfold precond. ss. destruct m. destruct p. destruct p. cbn.
      iDestruct "ASM" as "([% P] & %)". subst; hss.
      rename n into b, z into ofs.
      
      steps_r.

      steps_r. iDestruct "IST" as (? ? ? ?) "(% & [% IST] & %)".
      unfold Ist. iDestruct "IST" as (? ?) "[% B]". des; subst; hss.
      steps_r.

      iCombine "B P" as "P". iPoseProof (own_valid with "P") as "%WF".
      assert (HIT: ∃ q, memk_src b ofs ≡ Some(q, Excl v)).
      { clear - WF.
        dup WF. rewrite auth_both_valid_discrete in WF. ss. des.
        unfold included in *. des.
        unfold cmra.op in WF. unfold cmra_op in WF. hss. unfold ucmra_op in WF.
        hss. 
        unfold discrete_fun_op_instance in WF. 
        specialize (WF b ofs). 
        rewrite ! discrete_fun_lookup_op in WF.
        rewrite !discrete_fun_lookup_singleton in WF.
        destruct (z b ofs).
        - destruct c. specialize (WF1 b ofs). rewrite WF in WF1. inv WF1; ss.
        - rewrite right_id in WF. eauto.
      }
      des. hexploit (SIM b ofs). intro T.  unfold sim_loc in T.

      des_ifs; bsimpl; des; des_sumbool; unfold Mem.valid_ptr, is_some in *; des_ifs.
      - steps_r. force_l. steps_l. forces_l. iDestruct "P" as "[P Q]".
        iSplitL "Q". { iFrame. iSplit; et. }
        steps_l. step. iSplit; et.
        { iFrame. iExists _, [_], _, _. repeat iSplit; et. }
      - inv HIT.
    }

    destruct x.
    { (* cmp spec 2 *)
      ss. unfold precond. ss. destruct m. do 6 destruct p. cbn.
      iDestruct "ASM" as "((% & P0 & P1) & %)". des_safe; subst; hss.
      rename n0 into b0, z0 into ofs0, n into b1, z into ofs1.
      rename q1 into q0, q into q1, v0 into v0, v into v1.

      steps_r. iDestruct "IST" as (? ? ? ?) "(% & [% IST] & %)".
      unfold Ist. iDestruct "IST" as (? ?) "[% B]". des_safe; subst; hss.
      steps_r.

      iCombine "B P0" as "P0". iPoseProof (own_valid with "P0") as "%WF".
      assert (HIT: ∃ q, memk_src b0 ofs0 ≡ Some (q, Excl v0)).
      { clear - WF.
        dup WF. rewrite auth_both_valid_discrete in WF. ss. des.
        inv WF. specialize (H b0 ofs0). 
        rewrite ! discrete_fun_lookup_op in H.
        rewrite !discrete_fun_lookup_singleton in H.
        destruct (x b0 ofs0).
        - destruct c. specialize (WF1 b0 ofs0). rewrite H in WF1. inv WF1; ss.
        - eexists. rewrite H right_id //.
      }
      des_safe. hexploit (SIM b0 ofs0). intro T.  unfold sim_loc in T.
      
      iDestruct "P0" as "[B P0]".
      iCombine "B P1" as "P1". iPoseProof (own_valid with "P1") as "%WF1". 
      assert (HIT1: ∃ q, memk_src b1 ofs1 ≡ Some (q, Excl v1)).
      { clear - WF1.
        dup WF1. rewrite auth_both_valid_discrete in WF1. ss. des.
        inv WF1. specialize (H b1 ofs1). 
        rewrite ! discrete_fun_lookup_op in H.
        rewrite !discrete_fun_lookup_singleton in H.
        destruct (x b1 ofs1).
        - destruct c. specialize (WF2 b1 ofs1). rewrite H in WF2. inv WF2; ss.
        - eexists. rewrite H right_id //.
      }
      des_safe. hexploit (SIM b1 ofs1). intro H.  unfold sim_loc in H.

      iDestruct "P1" as "[B P1]".
      des_ifs_safe; bsimpl; des_safe; des_sumbool; unfold Mem.valid_ptr, is_some in *; des_ifs_safe.

      des_ifs; bsimpl; des_safe; des_sumbool; des; ss; inv HIT.
      { steps_r. des_ifs; bsimpl; des; des_sumbool; ss. 
        { force_l; steps_l; forces_l. iSplitL "P0 P1"; iFrame; et.
          steps_r. steps_l. step. iSplit; et. iFrame; try (iExists _, [_], _, _; repeat iSplit; et). }
        { force_l; steps_l; forces_l. iSplitL "P0 P1"; iFrame; et.
          steps_r. steps_l. step. iSplit; et. iFrame; try (iExists _, [_], _, _; repeat iSplit; et). }
      }
      { steps_r. des_ifs; bsimpl; des; des_sumbool; ss. 
        { force_l; steps_l; forces_l. iSplitL "P0 P1"; iFrame; et.
          steps_r. steps_l. step. iSplit; et. iFrame; try (iExists _, [_], _, _; repeat iSplit; et). }
        { force_l; steps_l; forces_l. iSplitL "P0 P1"; iFrame; et.
          steps_r. steps_l. step. iSplit; et. iFrame; try (iExists _, [_], _, _; repeat iSplit; et). }
      }
    }

    destruct x.
    { (* cmp spec 3 *)
      ss. unfold precond. ss. destruct m. destruct p. destruct p. cbn.
      iDestruct "ASM" as "([% P] & %)". subst; hss.
      rename n into b, z into ofs.

      steps_r. iDestruct "IST" as (? ? ? ?) "(% & [% IST] & %)".
      unfold Ist. iDestruct "IST" as (? ?) "[% B]". des; subst; hss.
      steps_r.

      iCombine "B P" as "P". iPoseProof (own_valid with "P") as "%WF".
      assert (HIT: ∃ q, memk_src b ofs ≡ Some (q, Excl v)).
      { clear - WF.
        dup WF. rewrite auth_both_valid_discrete in WF. ss. des.
        inv WF. specialize (H b ofs). 
        rewrite ! discrete_fun_lookup_op in H.
        rewrite !discrete_fun_lookup_singleton in H.
        destruct (x b ofs).
        - destruct c. specialize (WF1 b ofs). rewrite H in WF1. inv WF1; ss.
        - eexists. rewrite H right_id //.
      }
      des. hexploit (SIM b ofs). intro T.  unfold sim_loc in T. 

      des_ifs; bsimpl; des; des_sumbool; unfold Mem.valid_ptr, is_some in *; des_ifs.
      - steps_r. destruct dec; destruct dec; try congruence. steps_r.
        iDestruct "P" as "[BLK WHT]".

        steps_r. force_l; steps_l; forces_l. iSplitL "WHT"; iFrame; et.
        step. iSplit; et.
        { iFrame. iExists _, [_], _, _. repeat iSplit; et. }
      - inversion HIT.
    }

    destruct x.
    { (* cmp spec 4 *)
      ss. unfold precond. ss. destruct m.
      iDestruct "ASM" as "(% & %)". subst; hss.
      
      steps_r. 

      steps_r. iDestruct "IST" as (? ? ? ?) "(% & [% IST] & %)".
      unfold Ist. iDestruct "IST" as (? ?) "[% B]". des; subst; hss.

      steps_r. force_l; steps_l; forces_l. iSplitR. iFrame; et.
      step. iSplit; et.
      { iFrame. iExists _, [_], _, _. repeat iSplit; et. }
    }

    destruct x; ss.
  (*SLOW*)Qed.

  Lemma simF_cas : HSim.sim_fun open MemA MemI IstFull MemHdr.cas.
  Proof using MemInSpMem.
    init_simF.

    steps_l. destruct q.
    destruct x; [|destruct x; [| des_ifs]]; ss; unfold precond; 
    ss; destruct m; destruct p; destruct p; try destruct p; ss.

    { (* cas spec 0 - when cas succeeded *)
      iDestruct "ASM" as "([% P] & %)"; subst; hss.
      rename n into b, z into ofs, v0 into v_old, v into v_new.
      steps_r.

      inline_r. hss. red_ret_r. rewrite PRed.bind SBRed.bind. ired. add_ret_l ().
      iApply wsim_bind. iSplitL "IST P".
      { iApply sim_load; eauto; iFrame. }
      clear nths NODS st_src NODD st_tgt.
      iIntros (nths st_s r_s st_t r). hss.
      iIntros "(IST & P & ->)".

      steps_r. hss. steps_r. des_ifs.

      inline_r. hss. red_ret_r. rewrite PRed.bind SBRed.bind. ired. add_ret_l ().
      iApply wsim_bind. iSplitL "IST P".
      { iApply sim_store; eauto; iFrame. }
      clear nths st_s st_t.
      iIntros (nths st_s r_s st_t r). hss.
      iIntros "(IST & P & ->)".

      steps_r. hss. steps_r.
      force_l. steps_l. forces_l. iSplitL "P"; iFrame; et.

      step. eauto.
    }
    { (* cas spec 1 - when cas failed *)
      iDestruct "ASM" as "([% P] & %)"; des; subst; hss.
      rename n into b, z into ofs, v into v_real, v1 into v_old, v0 into v_new.
      steps_r.

      inline_r. hss. red_ret_r. rewrite PRed.bind SBRed.bind. ired. add_ret_l ().
      iApply wsim_bind. iSplitL "IST P".
      { iApply sim_load; eauto; iFrame. }
      clear nths NODS st_src NODD st_tgt.
      iIntros (nths st_s r_s st_t r). hss.
      iIntros "(IST & P & ->)".

      steps_r. hss. steps_r. des_ifs.
      force_l. steps_l. forces_l. iSplitL "P"; iFrame; et.

      step. eauto.
    }
  (*SLOW*)Qed.

  Theorem sim : HSim.t open MemA MemI (MemA.init_cond csl genv) IstFull.
  Proof using MemInSpMem.
    init_sim.
    - rewrite /IstFull /MemA /MemI. unfold_hmod. s.
      iIntros "P". iExists [], [_], [], []. repeat iSplit; et. et. { iPureIntro. ss. }
      iExists _, _. iFrame. iPureIntro. esplits; et.
      + ii. unfold mem_init_val, sim_loc. des_ifs; hss; uo. des_ifs; hss; ii; try econs; des_ifs; hss.
        des_ifs; hss. destruct ofs; ss. des_ifs. hss. des_ifs; hss. des_ifs. des_ifs.          
      + unfold Mem.load_mem, mem_wf. ii. cbn. uo. r. unfold Mem.cnts in H. des_ifs.
        destruct (nth_error genv b) eqn:E; ss. destruct p. r. gen genv. induction b.
        * i. destruct genv0; ss. nia.
        * i. apply nth_error_Some. rewrite E. ss.  
    - apply simF_alloc.
    - apply simF_free.
    - apply simF_load.
    - apply simF_store.
    - apply simF_cmp.
    - apply simF_cas.
  (*SLOW*)Qed.
End MemIA.

Section ctxr.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_memG: !memG}.

  Theorem ctxr csl genv (sp : string → option fspec)
      (MemInSpMem: sp_incl MemA.sp sp) :
    ctx_refines
      (MemA.t sp, MemA.init_cond csl genv)
      (MemI.t csl genv, emp%I).
  Proof using. eapply main_adequacy, sim; eauto. Qed.
End ctxr. End MemIA.
