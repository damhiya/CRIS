From CRIS Require Import CRIS MemHeader MemA MemI ImpPrelude.
From iris.algebra Require Import auth excl agree csum functions dfrac_agree.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section AUX.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
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
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_memG: !memG}.
  
  Lemma repeat_nth_some X (x: X) sz ofs (IN: ofs < sz) :
    nth_error (repeat x sz) ofs = Some x.
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
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_memG: !memG}.

  Definition mem_wf (m0: Mem.t): Prop :=
    forall b ofs v, m0.(Mem.cnts) b ofs = Some v -> b < m0.(Mem.nb)
  .

  Definition sim_mem (mem_s: _memRA) (mem_t: Mem.t) : Prop :=
    ∀ b ofs,
    (mem_s b ofs = None ∧ Mem.cnts mem_t b ofs = None) ∨
    (∃ v, mem_s b ofs = Some (to_frac_agree 1 v) ∧
          Mem.cnts mem_t b ofs = Some v).

  Definition mem_ra_upd (mem: _memRA) b ofs r : _memRA :=
    fun b0 ofs0 =>
      if dec b b0 && dec ofs ofs0 then r else mem b0 ofs0.

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
    ≡ (discrete_fun_singleton blk (discrete_fun_singleton ofs (Some (to_frac_agree q a)))).
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

  Lemma to_frac_agree_inv A q (v: leibnizO A) f
    (EQ: to_frac_agree q v ≡ f)
    :
    f.1 = DfracOwn q ∧ ∃ tl, f.2.(agree_car) = v :: tl.
  Proof.
    rr in EQ. des. ss. rr in EQ. rewrite EQ; split; et.
    specialize (EQ0 0). rr in EQ0. des.
    edestruct EQ0; s; eauto using elem_of_list.
    des. ss. destruct (agree_car f.2) eqn: E.
    - rewrite E in H. rr in H. inv H.
    - exists l. f_equal. rr in H0. depdes H0. rewrite E in EQ1.
      edestruct (EQ1 o); eauto using elem_of_list. des.
      rr in H1. depdes H1. rr in H0. depdes H0; ss. rr in H0. depdes H0.
  Qed.

  Lemma to_frac_full_valid_inv A c (v: leibnizO A)
    (VALID: ✓ (Some (to_frac_agree 1 v) ⋅ c))
    :
    c = None.
  Proof.
    destruct c; et. rewrite -?Some_op in VALID.
    rr in VALID. des. ss. exfalso. eapply dfrac_full_exclusive; et.
  Qed.

  Lemma mem_ra_alloc γ (mem_src : _memRA) mem_tgt blk sz pad
    (SIM: sim_mem mem_src mem_tgt)
    (BLK: blk = Mem.nb mem_tgt + pad)
    (WF: mem_wf mem_tgt)
    :
    own γ ((● mem_src): memRA)
    ⊢ |==>
    own γ ((● (mem_src ⋅ _points_to_r (blk, 0%Z) 1 (repeat Vundef sz))): memRA)
    ∗ own γ ((◯ _points_to_r (blk, 0%Z) 1 (repeat Vundef sz)): memRA).
  Proof using _memG.
    iIntros "P". rewrite -own_op.
    iApply (own_update with "P"). apply auth_update_alloc.
    apply local_update_discrete. i. rewrite H0.
    split; cycle 1.
    - destruct mz; simpl opM in *.
      + rewrite left_id (comm _ c). et.
      + rewrite left_id. et.
    - rewrite -H0. ii. rewrite !discrete_fun_lookup_op /_points_to_r.
      destruct (dec _ _); s; cycle 1.
      { rewrite right_id. apply H. }
      hexploit (SIM blk x0). i; subst; des; rewrite H1.
      + des_ifs.
      + exploit WF; et. nia.
  Qed.

  Lemma mem_ra_lookup (mem_s: _memRA) mem_t b ofs q v
    (SIM: sim_mem mem_s mem_t)
    :
    own base_γ (● mem_s) ∗ (b, ofs) |={ q }=> v
    ⊢
    ⌜mem_s b ofs ≡ Some (to_frac_agree 1 v) ∧
     Mem.cnts mem_t b ofs = Some v⌝.
  Proof.
    iIntros "P". rewrite -own_op.
    iPoseProof (own_valid with "P") as "%WF".
    dup WF. rewrite auth_both_valid_discrete in WF. ss. des.
    unfold included in *. des. specialize (WF b ofs). iris_tac.
    rewrite ->!discrete_fun_lookup_singleton in *.
    destruct (SIM b ofs); des; rewrite H in WF.
    { destruct (z b ofs); ss; rewrite -?Some_op ?right_id in WF; inv WF. }
    rewrite -WF. destruct (z b ofs); rr in WF; depdes WF.
    - assert (EXT: to_frac_agree q v ≼ to_frac_agree 1 v0) by (rewrite H1; et).
      eapply dfrac_agree_included in EXT. des; subst. rr in EXT0. subst. et.
    - eapply to_frac_agree_inv in H1. ss. des. depdes H2. et.
  Qed.

  Lemma mem_ra_update v_new v (mem_s: _memRA) mem_t b ofs
    (SIM: sim_mem mem_s mem_t)
    :
    own base_γ (● mem_s) ∗ (b, ofs) |={ 1 }=> v
    ⊢ |==>
    own base_γ (● mem_ra_upd mem_s b ofs (Some (to_frac_agree 1 v_new))) ∗ (b, ofs) |={ 1 }=> v_new.
  Proof.
    iIntros "P".
    iPoseProof ((mem_ra_lookup _ _ _ _ SIM) with "P") as "%H"; iFrame.
    des. clear H0.
    rewrite -!own_op. iApply (own_update with "P").
    apply auth_update, local_update_discrete. s. i.
    rewrite /mem_ra_upd. split; ii.
    { des_ifs. eapply H0. }
    destruct (dec b x); s; subst; cycle 1.
    - rewrite (H1 x x0). destruct mz; s;
        try rewrite !discrete_fun_lookup_op;
        rewrite !discrete_fun_lookup_singleton_ne; et.
    - destruct (dec ofs x0); s; subst; cycle 1.
      + rewrite (H1 x x0). destruct mz; s;
          try rewrite !discrete_fun_lookup_op;
          rewrite !discrete_fun_lookup_singleton;
          rewrite !discrete_fun_lookup_singleton_ne; et.
      + specialize (H1 x x0). revert H1.
        destruct mz; s;
          try rewrite !discrete_fun_lookup_op;
          rewrite !discrete_fun_lookup_singleton; et.
        i. specialize (H0 x x0). rewrite H1 in H0.
        eapply to_frac_full_valid_inv in H0. rewrite H0 right_id. et.
  Qed.

  Lemma mem_ra_free (mem_s : _memRA) mem_t b ofs v
    (SIM: sim_mem mem_s mem_t)
    (WF: mem_wf mem_t)
    :
    own base_γ (● mem_s) ∗ (b, ofs) |={ 1 }=> v
    ⊢ |==>
    own base_γ (● mem_ra_upd mem_s b ofs None).
  Proof using _memG.
    iIntros "P". rewrite -own_op. iApply (own_update with "P").
    eapply auth_update_dealloc, local_update_discrete.
    i. split.
    { ii. rewrite /mem_ra_upd. des_ifs. apply H. }
    ss. ii. dup H. rewrite H0 in H. rewrite /mem_ra_upd.
    specialize (H x x0). specialize (H0 x x0). specialize (H1 x x0).
    destruct mz; ss; try rewrite !discrete_fun_lookup_op in H, H0 |- *.
    - destruct dec; ss; subst; cycle 1.
      { rewrite discrete_fun_lookup_singleton_ne in H0; et. }
      rewrite discrete_fun_lookup_singleton in H, H0.
      destruct dec; ss; subst; cycle 1.
      { rewrite discrete_fun_lookup_singleton_ne in H0; et. }
      rewrite discrete_fun_lookup_singleton in H, H0.
      apply to_frac_full_valid_inv in H. rewrite H. et.
    - destruct dec; ss; subst; cycle 1.
      { rewrite discrete_fun_lookup_singleton_ne in H0; et. }
      rewrite discrete_fun_lookup_singleton in H, H0.
      destruct dec; ss.
      rewrite discrete_fun_lookup_singleton_ne in H0; et.
  Qed.

  Lemma mem_ra_cmp (mem_s: _memRA) mem_t p0 q0 v0 p1 q1 v1 succ
    (SIM: sim_mem mem_s mem_t)
    (CMP: MemSpec.compare_val p0 p1 = Vint succ)
    :
    (own base_γ (● mem_s) ∗ MemSpec.val_r p0 q0 v0 ∗ MemSpec.val_r p1 q1 v1)
    ⊢
    ⌜Mem.vcmp mem_t p0 p1 = Some (dec succ 1 : bool)⌝.
  Proof.
    iIntros "(B & P1 & P2)".
    destruct p0, p1; try destruct blkofs; try destruct blkofs0; ss.
    - des_ifs.
    - iPoseProof (mem_ra_lookup with "[B P2]") as "%"; et; iFrame.
      specialize (SIM n0 z). des; subst; ss.
      + rewrite SIM in H. r in H. depdes H.
      + rewrite SIM0. iPureIntro. des_ifs.
    - destruct n; ss.
    - iPoseProof (mem_ra_lookup with "[B P1]") as "%"; et; iFrame.
      specialize (SIM n0 z). des; subst; ss.
      + rewrite SIM in H. rr in H. depdes H.
      + rewrite SIM0. iPureIntro. des_ifs.
    - iPoseProof (mem_ra_lookup with "[B P1]") as "%"; et; iFrame.
      iPoseProof (mem_ra_lookup with "[B P2]") as "%"; et; iFrame.
      dup SIM. specialize (SIM n z). des; subst; ss.
      { rewrite SIM in H. rr in H. depdes H. }
      specialize (SIM0 n0 z0). des; subst; ss.
      { rewrite SIM0 in H0. rr in H0. depdes H0. }
      rewrite SIM1 SIM2. s. des_ifs.
  Qed.

End RA.

Module MemIP. Section MemIP.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_memG: !memG}.

  Context (csl : string → bool).
  Context (genv : GEnv.t).

  Definition Ist: nat -> alist key Any.t -> alist key Any.t -> iProp Σ :=
    fun _ st_src st_tgt =>
      ( (∃ (mem_tgt: Mem.t) (mem_src: _memRA),
        ⌜st_tgt = [(MemI.v_mem, mem_tgt↑)] ∧
         sim_mem mem_src mem_tgt ∧
         mem_wf mem_tgt⌝
      ∗
         ( |==> own base_γ (● mem_src) )
      ))%I.

  Local Definition MemP := (MemP.t).
  Local Definition MemI := (MemI.t csl genv).
  Local Definition IstFull := (IstProd (IstSB MemP.(Mod.scopes) Ist) IstEq).

  Definition mem_get (mem: _memRA) b ofs :=
    match or_else (mem b ofs) (to_frac_agree 1 Vundef) with
    | (_,v) => or_else (nth_error v.(agree_car) 0) Vundef
    end.

  Lemma mem_get_sound mem b ofs v
    (HIT : mem b ofs ≡ Some (to_frac_agree 1 v))
    :
    mem_get mem b ofs = v.
  Proof.
    rr in HIT. depdes HIT. rewrite /mem_get -x. s. destruct x0.
    symmetry in H. eapply to_frac_agree_inv in H. des. ss. subst.
    rewrite H0. et.
  Qed.
  
  Lemma simF_alloc : ISim.sim_fun open MemP MemI (MemP.init_cond csl genv) IstFull (Some MemHdr.alloc).
  Proof using.
    init_simF.
    iDestruct "IST" as (? ? ? ?) "(% & [% [% [% [% >B]]]] & %)". des; subst; hss.
    unfold MemP.alloc, fspec_proph.
    step_l; step_r.

    asmproph_simple (Z.to_nat (or_else (pargs [Tint] (or_else (arg↓) [])) 0%Z)).
    { iApply precise_pure. }

    iDestruct "ASM" as "[% %]". subst; hss. rewrite Nat2Z.id. iSplit; et.
    steps_r. des_ifs.
    2:{ rewrite andb_false_iff in Heq. des; des_sumbool; try nia. }

    hss. steps_r.
    rename x' into size, q into pad. set (blk := Mem.nb mem_tgt + pad).
    iPoseProof (own_valid with "B") as "%".
    iPoseProof (mem_ra_alloc with "B") as ">B"; et.
    iDestruct "B" as "[BLK WHT]".

    force_l ((Vptr (blk, 0%Z)) ↑). force_l. iSplitL "WHT".
    { iExists blk. iSplit; et.
      iPoseProof (points_to_transform with "WHT") as "WHT". iFrame. }
    steps_l.
    step. iSplit; et.
    iExists _, [_], _, _. repeat (iSplit; et).
    iExists _, _. iFrame. iPureIntro.
    esplits; et; ii; cycle 1.
    { ss. unfold update in *. des_ifs. exploit H4; et. nia. }
    
    destruct (mem_tgt.(Mem.cnts) blk ofs) eqn:E.
    { exfalso. exploit H4; et. nia. }
    ss. hexploit (H3 blk ofs); et.
    rewrite E. intro U. des; ss.
    rewrite !discrete_fun_lookup_op.
    destruct (AList.dec b blk); subst; ss.
    - rewrite repeat_length. rewrite Z.add_0_l.
      unfold AList.update. des_ifs_safe. rewrite U left_id.
      Ztac. destruct (dec _ _); ss.
      destruct ((_ <=? _)%Z && (_ <? _)%Z) eqn: E0; et.
      rewrite repeat_nth_some; et.
      bsimpl; des; des_sumbool. Ztac. nia.
    - unfold update in *. destruct (dec blk b); subst; ss.
      des_ifs; bsimpl; destruct dec; des; subst; ss; rewrite right_id; eauto.
  (*SLOW*)Qed.

  Lemma simF_free : ISim.sim_fun open MemP MemI (MemP.init_cond csl genv) IstFull (Some MemHdr.free).
  Proof using.
    init_simF.
    iDestruct "IST" as (? ? ? ?) "(% & [% [% [% [% >B]]]] & %)". des; subst; hss.

    unfold MemP.free, fspec_proph.

    destruct (or_else (pargs [Tptr] (or_else (arg↓) [])) (0,0%Z)) as [b ofs] eqn: EQ.
    step_l; step_r.
    asmproph_simple (b, ofs, mem_get mem_src b ofs); s.
    { iApply precise_sep. iSplit; [iApply precise_pure | iApply precise_own]. }

    destruct x' as [[b' ofs'] v']. s.
    iDestruct "ASM" as "[% P]". des; subst; hss.

    iPoseProof (mem_ra_lookup with "[B P]") as "%HIT"; et; iFrame. des.
    iSplit. { erewrite mem_get_sound; et. }

    steps_r. hss. steps_r. rewrite HIT0. steps_r.
    force_l. force_l. iSplit; et. step. repeat (iSplit; et).
    iExists st_srcL, [_], _, _. repeat (iSplit; et).
    iExists _, (mem_ra_upd mem_src b ofs None). iSplit; cycle 1.
    { iMod (mem_ra_free with "[B P]") as "H"; et; iFrame. }
    iPureIntro. esplits; et.
    - ii. s. rewrite /mem_ra_upd /update.
      destruct dec; ss; subst. des_ifs. left. et.
    - rewrite /update. ii. ss. destruct dec; ss; subst; et.
  (*SLOW*)Qed.

  Lemma simF_load : ISim.sim_fun open MemP MemI (MemP.init_cond csl genv) IstFull (Some MemHdr.load).
  Proof using.
    init_simF.
    iDestruct "IST" as (? ? ? ?) "(% & [% [% [% [% >B]]]] & %)". des; subst; hss.

    unfold MemP.load, fspec_proph.

    destruct (or_else (pargs [Tptr] (or_else (arg↓) []))(0,0%Z)) as [b ofs] eqn: EQ.
    step_l; step_r.
    asmproph_standard.
    iExists (⌜arg = [Vptr (b,ofs)]↑ ∧
              mem_tgt.(Mem.cnts) b ofs = Some (mem_get mem_src b ofs)⌝
             ∗ own base_γ (● mem_src))%I.
    iExists (λ ret, ⌜ret = (mem_get mem_src b ofs)↑⌝%I).
    iSplit.
    { iApply precise_sep; iSplit; [iApply precise_pure|iApply precise_own]. }
    iSplitL "B".
    { iIntros (?). destruct x as [[[b0 ofs0] ] ]. s. iIntros "[% P]". subst. hss.
      iPoseProof (mem_ra_lookup with "[B P]") as "%"; et; iFrame. des.
      rewrite H1. erewrite mem_get_sound; et.
    }

    iIntros "[% B]". des; subst; hss.
    steps_r. hss. steps_r. rewrite H1. s. steps_r.
    force_l. force_l. iSplit; et. step. iSplit; et.
    iExists _, [_], _, _. repeat (iSplit; et). iExists _, _. iSplit; et.
  (*SLOW*)Qed.

  Lemma simF_store : ISim.sim_fun open MemP MemI (MemP.init_cond csl genv) IstFull (Some MemHdr.store).
  Proof using.
    init_simF.
    iDestruct "IST" as (? ? ? ?) "(% & [% [% [% [% >B]]]] & %)". des; subst; hss.

    unfold MemP.store, fspec_proph.

    destruct (or_else(pargs [Tptr; Tuntyped] (or_else (arg↓) [])) (0,0%Z,Vundef))
      as [[b ofs] v_new] eqn: EQ.
    step_l; step_r.
    asmproph_simple (b, ofs, mem_get mem_src b ofs, v_new); ss.
    { iApply precise_sep. iSplit; [iApply precise_pure | iApply precise_own]. }
    destruct x' as [[[b' ofs'] v'] v_new']. ss.
    iDestruct "ASM" as "(% & P)". subst; hss.
    iPoseProof (mem_ra_lookup with "[B P]") as "%"; et; iFrame. des.
    erewrite mem_get_sound; et. iSplit; et.

    steps_r. hss. steps_r. rewrite H1. steps_r.

    iMod (mem_ra_update with "[B P]") as "[B P]"; et; iFrame.
    force_l. force_l. iSplitL "P"; et. step. repeat (iSplit; et).
    iExists st_srcL, [_], _, _. repeat (iSplit; et).
    iExists _, (mem_ra_upd mem_src b ofs _). iSplit; et.
    iPureIntro. esplits; et.
    - ii. s. rewrite /mem_ra_upd /update.
      destruct dec; ss; subst. des_ifs. right. et.
    - ii. ss. destruct dec; ss; subst; et.
  (*SLOW*)Qed.

  Lemma simF_cmp : ISim.sim_fun open MemP MemI (MemP.init_cond csl genv) IstFull (Some MemHdr.cmp).
  Proof using.
    init_simF.
    iDestruct "IST" as (? ? ? ?) "(% & [% [% [% [% >B]]]] & %)". des; subst; hss.

    step_l; step_r.
    unfold MemP.cmp, fspec_proph.

    destruct (or_else (pargs [Tuntyped; Tuntyped] (or_else (arg↓) []))(Vundef,Vundef)) as [p1 p2] eqn: EQ.
    asmproph_standard.
    iExists (⌜arg = [p1; p2]↑ ∧ MemSpec.compare_val p1 p2 ≠ Vundef ∧
              Mem.vcmp mem_tgt p1 p2 ≠ None⌝ ∗
             own base_γ (● mem_src))%I.
    iExists (λ ret, ⌜ret = (MemSpec.compare_val p1 p2)↑⌝%I).
    iSplit.
    { iApply precise_sep; iSplit; [iApply precise_pure|iApply precise_own]. }
    iSplitL "B".
    { iIntros (?). destruct x as [[[[[[arg0 q0] v0] arg1] q1] v1] succ]. s.
      iIntros "[% [P1 P2]]". des. subst. hss. iModIntro.
      rewrite -(assoc (∗))%I. iSplit.
      { iSplit; et. rewrite H1. iSplit; et.
        iPoseProof (mem_ra_cmp with "[B P1 P2]") as "%"; et; [iFrame|].
        rewrite H. et.
      }
      rewrite H1. iFrame; et.
    }      

    iIntros "[% B]". des; subst; hss.
    steps_r. hss. steps_r. destruct (Mem.vcmp mem_tgt p1 p2) as [r|] eqn: E; ss.
    steps_r. force_l. force_l. iSplit; et. step. iSplit.
    { destruct p1, p2; depdes E; try destruct blkofs; try destruct blkofs0; ss;
        try by destruct n; ss; des_ifs. }
    iExists _, [_], _, _. repeat (iSplit; et). iExists _, _. iSplit; et.
  (*SLOW*)Qed.

  Lemma simF_cas : ISim.sim_fun open MemP MemI (MemP.init_cond csl genv) IstFull (Some MemHdr.cas).
  Proof using.
    init_simF.
    iDestruct "IST" as (? ? ? ?) "(% & [% [% [% [% >B]]]] & %)". des; subst; hss.

    unfold MemP.cas, fspec_proph.
    
    destruct (or_else (pargs [Tptr; Tuntyped; Tuntyped] (or_else (arg↓) [])) ((0,0%Z),(Vundef,Vundef))) as [[b ofs] [v_old v_new]] eqn: EQ.
    set (v_cur := mem_get mem_src b ofs).
    set (is_succ := dec (MemSpec.compare_val v_cur v_old) (Vint 1) : bool).
    set (v_upd := if is_succ then v_new else v_cur).

    step_l; step_r.
    asmproph_standard.
    iExists (⌜arg = [Vptr (b,ofs); v_old; v_new]↑ ∧
              Mem.cnts mem_tgt b ofs = Some v_cur ∧
              Mem.vcmp mem_tgt v_cur v_old = Some is_succ⌝ ∗
             own base_γ (● (mem_ra_upd mem_src b ofs (Some (to_frac_agree 1 v_upd)))))%I.
    iExists (λ ret, ⌜ret = v_cur↑⌝%I).
    iSplit.
    { iApply precise_sep; iSplit; [iApply precise_pure|iApply precise_own]. }
    iSplitL "B".
    { iIntros (?).
      destruct x as [[[[[[[[[b' ofs'] v_cur']q0]v0]v_old']q1]v1]v_new']succ]. s.
      iIntros "[% [P [V1 V2]]]". des. subst. hss.
      iPoseProof (mem_ra_lookup with "[B P]") as "%"; et; [iFrame|]. des.
      iPoseProof (mem_ra_cmp with "[B V1 V2]") as "%"; et; [iFrame|].
      iMod ((mem_ra_update v_upd) with "[B P]") as "[B P]"; et; [iFrame|].
      subst v_cur v_upd is_succ. erewrite mem_get_sound; et.
      rewrite H1 H2 H6. des_ifs; iFrame; et.
      exfalso. eapply n. destruct dec; ss. depdes e. et.
    }

    iIntros "[% B]". des; subst; hss. steps_r.
    inline_r. repeat (steps_r; hss). rewrite H1. steps_r; hss. steps_r.
    inline_r. repeat (steps_r; hss). rewrite H2. steps_r; hss. steps_r.

    add_ret_l (). iApply wsim_bind.
    instantiate (1:= λ nths0 '(st_s,_) '(st_t,_), ⌜nths0 = _ ∧ st_s = _ ∧
      st_t = (_, (or_else (Mem.store mem_tgt (b,ofs) v_upd) mem_tgt)↑) :: _⌝%I).
    iSplitL "".
    { des_ifs; cycle 1.
      - step. iPureIntro; esplits; et. repeat f_equal.
        rewrite H1. s. destruct mem_tgt. f_equal. extensionalities b' ofs'.
        des_ifs. bsimpl; des; des_sumbool. subst. et.
      - rewrite /ccallU. steps_r. inline_r. repeat (steps_r; hss). rewrite H1. steps_r. hss. steps_r.
        step. et.
    }
    iIntros (? ? _ ? _ ?) "%". des; subst.

    steps_r. do 2 force_l. iSplit; et. steps_l. step. iSplit; et. rewrite H1; s.
    iExists _, [_], _, _. repeat (iSplit; et). iExists _, _.
    iFrame. iSplit; et. iPureIntro; esplits; et.
    - ii. rewrite /mem_ra_upd. s. des_ifs; et.
    - ii. ss. des_ifs; et. bsimpl; des; des_sumbool; subst. eapply H4; et.
  (*SLOW*)Qed.

  Theorem sim : ISim.t open MemP MemI (MemP.init_cond csl genv) IstFull.
  Proof using.
    init_sim.
    - rewrite /IstFull /MemP /MemI. unfold_mod. s. splits; eauto.
      iIntros "P". iExists [], [_], [], [].
      repeat iSplit; et.
      { iPureIntro. ss. }
      iExists _, _. iFrame. iPureIntro. esplits; et.
      + ii. rewrite /mem_init_val /Mem.load_mem.
        uo; des_ifs; bsimpl; des; des_sumbool; subst; ss;
          rewrite ?Heq0 ?Heq1 ?Heq2; des_ifs; et.
      + ii. revert H. rewrite /Mem.load_mem; uo; s. des_ifs.
        i. inv H. eapply nth_error_Some. unfold Mem.load_mem in H1; ss.
        destruct (nth_error genv b); ss.
    - apply simF_alloc.
    - apply simF_free.
    - apply simF_load.
    - apply simF_store.
    - apply simF_cmp.
    - apply simF_cas.
  (*SLOW*)Qed.

  Theorem ctxr :
    ctx_refines
      (MemP, MemP.init_cond csl genv)
      (MemI, emp%I).
  Proof using. eapply main_adequacy, sim; eauto. Qed.
End MemIP. End MemIP.

Module MemPA. Section MemPA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_memG: !memG}.

  (* TODO: updating lemmas or tactic is required, but now we use custom tactic. *)
  Local Opaque SModTr.trans_ktree.
  Ltac prove_proph_sim :=
    s; et; ii;
    match goal with
    | H:_ |- _ => revert H; alist_find_simpl; i; depdes H
    end; alist_find_simpl; esplits; et; eapply isim_fsem_proph_to_normal; i; iIntros;
    rewrite SRed.fbody_trivial /fbody_trivial SRed.core; iIntros; steps_r; forces_l; step; eauto.

  Theorem sim sp : ISim.t open (MemA.t sp) MemP.t emp%I IstEq.
  Proof using.
    init_sim; prove_proph_sim.
  (*SLOW*)Qed.

  Theorem ctxr sp:
    ctx_refines
      (MemA.t sp, emp%I)
      (MemP.t, emp%I).
  Proof using. eapply main_adequacy, sim; eauto. Qed.
End MemPA. End MemPA.

Module MemIA. Section MemIA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_memG: !memG}.

  Theorem ctxr csl genv sp :
    ctx_refines
      (MemA.t sp, MemA.init_cond csl genv)
      (MemI.t csl genv, emp%I).
  Proof using.
    etrans; cycle 1.
    { eapply MemIP.ctxr. }
    etrans; cycle 1.
    { ctxr_norm. eapply MemPA.ctxr. }
    eapply ctxr_cond_strengthen; et.
  Qed.
End MemIA. End MemIA.
