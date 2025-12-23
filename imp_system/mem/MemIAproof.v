From CRIS Require Import CRIS MemHeader MemA MemI ImpPrelude.
From iris.algebra Require Import auth excl agree csum functions dfrac_agree.

Local Open Scope nat_scope.

Section AUX.
  Context `{!crisG Γ Σ α β τ _S _I, !memG}.

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

Ltac Ztac := all_once_fast
  ltac:(fun H =>
    first[apply Z.leb_le in H|apply Z.ltb_lt in H|apply Z.leb_gt in H|apply Z.ltb_ge in H|idtac]).

Section AUX2.
  Lemma repeat_nth_some X (x: X) sz ofs (IN: ofs < sz) :
    nth_error (repeat x sz) ofs = Some x.
  Proof using.
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

  Definition mem_wf (m : Mem.t) : Prop := ∀ b ofs v, m.(Mem.cnts) b ofs = Some v → b < m.(Mem.nb).

  Definition sim_mem (mem_s : _memRA) (mem_t : Mem.t) : Prop :=
    ∀ b ofs,
      (mem_s b ofs = None ∧ Mem.cnts mem_t b ofs = None) ∨
      (∃ v, mem_s b ofs = Some (to_dfrac_agree (DfracOwn 1) v) ∧
        Mem.cnts mem_t b ofs = Some v).

  Definition mem_ra_upd (mem : _memRA) b ofs r : _memRA :=
    λ b0 ofs0, if bool_decide (b = b0 ∧ ofs = ofs0) then r else mem b0 ofs0.

  Lemma split_points_to_r blk ofs q a l :
    _points_to_r (blk, ofs) q (a :: l)
    ≡ (_points_to_r (blk, ofs) q [a]) ⋅ (_points_to_r (blk, (ofs + 1)%Z) q l).
  Proof using.
    intros b o. rewrite !discrete_fun_lookup_op /=.
    repeat case_bool_decide; des; simplify_eq; try nia; ss.
    { destruct (decide (o = ofs)); subst; [|nia]; rewrite ?Z.sub_diag //=. }
    { rewrite left_id. replace (o - (ofs + 1))%Z with (o - ofs - 1)%Z by nia.
      replace (Z.to_nat (o - ofs)) with (S (Z.to_nat (o - ofs - 1))) by nia.
      ss.
    }
  Qed.

  Lemma points_to_singleton blk ofs q a :
    _points_to_r (blk, ofs) q [a]
    ≡ (discrete_fun_singleton blk (discrete_fun_singleton ofs (Some (to_dfrac_agree q a)))).
  Proof using.
    intros b o; ss.
    ss; case_bool_decide; des; simplify_eq; ss.
    { destruct (decide (o = ofs)); subst; try nia.
      rewrite Z.sub_diag /= ?discrete_fun_lookup_singleton //.
    }
    apply not_and_or in H; des; try by rewrite discrete_fun_lookup_singleton_ne //.
    destruct (decide (b = blk)); subst;
      [rewrite discrete_fun_lookup_singleton discrete_fun_lookup_singleton_ne //; ii; clarify; nia
      |rewrite discrete_fun_lookup_singleton_ne //].
  Qed.

  Local Transparent mem_points_to_singleton_r.

  Lemma points_to_transform blk ofs q l :
    own base_γ ((◯ _points_to_r (blk, ofs) (DfracOwn q) l): memRA)
    ⊢ [∗ list] i↦v ∈ l, (blk, (ofs + i)%Z) ↦{q} v.
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
    (EQ: to_dfrac_agree q v ≡ f)
    :
    f.1 = q ∧ ∃ tl, f.2.(agree_car) = v :: tl.
  Proof using.
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
    (VALID: ✓ (Some (to_dfrac_agree (DfracOwn 1) v) ⋅ c))
    :
    c = None.
  Proof using.
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
    own γ ((● (mem_src ⋅ _points_to_r (blk, 0%Z) (DfracOwn 1) (repeat Vundef sz))): memRA)
    ∗ own γ ((◯ _points_to_r (blk, 0%Z) (DfracOwn 1) (repeat Vundef sz)): memRA).
  Proof using _memG.
    iIntros "P". rewrite -own_op.
    iApply (own_update with "P"). apply auth_update_alloc.
    apply local_update_discrete. i. rewrite H0.
    split; cycle 1.
    - destruct mz; simpl opM in *.
      + rewrite left_id (comm _ c). et.
      + rewrite left_id. et.
    - rewrite -H0. ii. rewrite !discrete_fun_lookup_op /_points_to_r.
      case_bool_decide; s; cycle 1.
      { rewrite right_id. apply H. }
      hexploit (SIM blk x0). i; subst; des; rewrite H1; clarify.
      + rewrite H2; case_match; ss.
      + exploit WF; et. nia.
  Qed.

  Lemma mem_ra_lookup (mem_s: _memRA) mem_t b ofs q v
    (SIM: sim_mem mem_s mem_t)
    :
    own base_γ (● mem_s) ∗ (b, ofs) ↦{q} v
    ⊢
    ⌜mem_s b ofs ≡ Some (to_dfrac_agree (DfracOwn 1%Qp) v) ∧
     Mem.cnts mem_t b ofs = Some v⌝.
  Proof using.
    iIntros "P". rewrite -own_op.
    iPoseProof (own_valid with "P") as "%WF".
    dup WF. rewrite auth_both_valid_discrete in WF. ss. des.
    unfold included in *. des. specialize (WF b ofs). iris_tac.
    rewrite ->!discrete_fun_lookup_singleton in *.
    destruct (SIM b ofs); des; rewrite H in WF.
    { destruct (z b ofs); ss; rewrite -?Some_op ?right_id in WF; inv WF. }
    rewrite -WF. destruct (z b ofs); rr in WF; depdes WF.
    - assert (EXT: to_dfrac_agree (DfracOwn q) v ≼ to_dfrac_agree (DfracOwn 1) v0) by (rewrite H1; et).
      eapply dfrac_agree_included in EXT. des; subst. rr in EXT0. subst. et.
    - eapply to_frac_agree_inv in H1. ss. des. depdes H2. et.
  Qed.

  Lemma mem_ra_update v_new v (mem_s: _memRA) mem_t b ofs :
    sim_mem mem_s mem_t →
    own base_γ (● mem_s) ∗ (b, ofs) ↦{1} v ⊢
    |==> own base_γ (● mem_ra_upd mem_s b ofs (Some (to_dfrac_agree (DfracOwn 1) v_new))) ∗
      (b, ofs) ↦{1} v_new.
  Proof using.
    iIntros "%SIM [Auth Frag]".
    iPoseProof ((mem_ra_lookup _ _ _ _ _ _ SIM) with "[Auth Frag]") as "[%H %_]"; iFrame.
    rewrite -own_op.
    iApply (own_update_2 with "Auth Frag").
    rewrite /mem_points_to_singleton_r /= auth_update //; apply discrete_fun_local_update.
    intros b2; apply discrete_fun_local_update; intros o2.
    destruct (decide (b2 = b)); subst.
    { destruct (decide (o2 = ofs)); subst.
      { rewrite H ?discrete_fun_lookup_singleton /mem_ra_upd; case_bool_decide; [|naive_solver].
        apply option_local_update, exclusive_local_update; ss.
      }
      rewrite ?discrete_fun_lookup_singleton /mem_ra_upd; case_bool_decide; [naive_solver|].
      rewrite ?discrete_fun_lookup_singleton_ne //.
    }
    rewrite ?discrete_fun_lookup_singleton_ne /mem_ra_upd //.
    case_bool_decide; [naive_solver|]; ss.
  Qed.

  Lemma mem_ra_free (mem_s : _memRA) mem_t b ofs v :
    sim_mem mem_s mem_t →
    mem_wf mem_t →
    own base_γ (● mem_s) ∗ (b, ofs) ↦{1} v ⊢
    |==> own base_γ (● mem_ra_upd mem_s b ofs None).
  Proof using _memG.
    iIntros "% % [Auth Frag]".
    iApply (own_update_2 with "Auth Frag").
    rewrite /mem_points_to_singleton_r auth_update_dealloc //=.
    apply discrete_fun_local_update; intros b1; apply discrete_fun_local_update; intros o1.
    destruct (decide (b1 = b)); subst.
    { rewrite discrete_fun_lookup_singleton.
      destruct (decide (o1 = ofs)); subst.
      { rewrite ?discrete_fun_lookup_singleton /mem_ra_upd; case_bool_decide; [|naive_solver].
        apply delete_option_local_update; eauto; apply _.
      }
      rewrite discrete_fun_lookup_singleton_ne // /mem_ra_upd; case_bool_decide; [naive_solver|ss].
    }
    rewrite /mem_ra_upd; case_bool_decide; [naive_solver|].
    rewrite discrete_fun_lookup_singleton_ne; ss; eauto.
  Qed.

  Lemma mem_ra_cmp (mem_s: _memRA) mem_t p0 q0 v0 p1 q1 v1 succ
    (SIM: sim_mem mem_s mem_t)
    (CMP: MemSpec.compare_val p0 p1 = Vint succ)
    :
    (own base_γ (● mem_s) ∗ MemSpec.val_r p0 q0 v0 ∗ MemSpec.val_r p1 q1 v1)
    ⊢
    ⌜Mem.vcmp mem_t p0 p1 = Some (bool_decide (succ = 1))⌝.
  Proof using.
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
      rewrite SIM1 SIM2. s.
      repeat case_bool_decide; ss; des; simplify_eq.
  Qed.

End RA.

Module MemIA. Section MemIA.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !memG}.

  Context (csl : string → bool).
  Context (genv : GEnv.t).
  Context (sp: specmap).

  Definition Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ :=
    λ st_src st_tgt,
      ((∃ (mem_tgt : Mem.t) (mem_src : _memRA),
      ⌜st_tgt = {[MemI.v_mem := Some mem_tgt↑]} ∧ sim_mem mem_src mem_tgt ∧ mem_wf mem_tgt⌝ ∗
      ( |==> own base_γ (● mem_src))))%I.

  Local Definition MemA := (MemA.t sp).
  Local Definition MemI := (MemI.t csl genv).
  Local Definition IstFull := (IstProd (IstSB MemA.(Mod.scopes) Ist) IstEq).

  Definition mem_get (mem: _memRA) b ofs :=
    match or_else (mem b ofs) (to_dfrac_agree (DfracOwn 1) Vundef) with
    | (_,v) => or_else (nth_error v.(agree_car) 0) Vundef
    end.

  Lemma mem_get_sound mem b ofs v
      (HIT : mem b ofs ≡ Some (to_dfrac_agree (DfracOwn 1) v)) :
    mem_get mem b ofs = v.
  Proof using.
    rr in HIT. depdes HIT. rewrite /mem_get -x. s. destruct x0.
    symmetry in H1. eapply to_frac_agree_inv in H1. des. ss. subst.
    rewrite H2. et.
  Qed.

  Ltac init_simF :=
    rewrite /ISim.sim_fun; simplify_map_eq; intros ??; eexists; split; first refl;
    iIntros (arg st_src st_tgt) "IST"; iApply wsim_isim;
    rewrite /SB.sandbox_body /=.
    (* /SModTr.trans_fnsem /=. *)
  Local Definition state : Type := gmap key (option Any.t).
  Local Definition post (R_s R_t : Type) : Type := state * R_s → state * R_t → iProp Σ.

  Local Definition rel : Type := ∀ R_s R_t : Type,
    post R_s R_t → bool → bool → state * itree crisE R_s → state * itree crisE R_t → iProp Σ.

  (* TEMP *)
  Ltac simplify_msk msk :=
    (* try match goal with
    | H :  context [msk _ _ = _] |- _ => rewrite H
    end; *)
    lazymatch goal with
    | [ |- match ?P with true => _ | false => _ end] =>
        let r := eval vm_compute in P in
        change P with r in *
    end.


Tactic Notation "red_bind" tactic(tac) :=
  lazymatch goal with
  | [ |- @ITree.bind _ _ _ ?itr _ = _ ] =>
      lazymatch itr with
      | Ret _ => etransitivity; [ eapply bind_ret_l | s; tac ]
      | Tau _ => eapply bind_tau
      | vis _ _ => eapply vis_bind
      | assumeK _ _ => eapply assumeK_bind
      | guaranteeK _ _ => eapply guaranteeK_bind
      | unwrapUK _ _ => eapply unwrapUK_bind
      | unwrapNK _ _ => eapply unwrapNK_bind
      | RealUpdateK _ _ _ => eapply RealUpdateK_bind
      (* | SBRed.putSB _ _ _ _ _ _ => eapply SBRed.putSB_bind
      | SBRed.getSB _ _ _ _ _ => eapply SBRed.getSB_bind
      | SBRed.callSB _ _ _ _ _ _ => eapply SBRed.callSB_bind
      | SBRed.spawnSB _ _ _ _ _ _ => eapply SBRed.spawnSB_bind *)
      | @ITree.bind _ _ _ _ _ => eapply bind_bind
      | _ => reflexivity
      end
  end.

Tactic Notation "red_SB" tactic(tac) :=
  lazymatch goal with
  | [ |- @SB.sandbox ?Σ ?msk ?R ?itr = _ ] =>
      lazymatch itr with
      | Ret _ =>
          eapply SBRed.ret
      | Tau _ =>
          eapply SBRed.tau
      | vis _ ?k =>
          etransitivity; [eapply SBRed.vis | s; tac ]
      (* | assumeK _ _ =>
          eapply SBRed.assumeK *)
      (* | guaranteeK _ _ =>
          eapply SBRed.guaranteeK *)
      (* | unwrapUK _ _ =>
          eapply SBRed.unwrapUK *)
      (* | unwrapNK _ _ =>
          eapply SBRed.unwrapNK *)
      (* | RealUpdateK _ _ _ =>
          eapply SBRed.ruK *)
      | @ITree.bind _ _ _ _ _ =>
          eapply SBRed.bind
      | _ =>
          reflexivity
      end
  end.

(* Ltac unfold_sp_exact sp name :=
  try match goal with
      [ H : sp_incl _ sp |- _ ] =>
        let RW := fresh "_RW" in
        let ND := fresh "_ND" in
        edestruct H as [ND RW];
        erewrite (RW name);
        [| revert ND; unfold to_sp;
           match goal with [|-context[alist_find _ ?x]] => rewrite /x end;
           unseal CRIS; i;
           alist_find_simpl;
           refl];
        simpl unwrapN; clear ND RW
    end. *)

Tactic Notation "red_S" tactic(tac) :=
  lazymatch goal with
  | [ |- @SModTr.trans ?Γ ?Σ ?α ?β ?τ ?_S ?_I ?_crisG ?concG ?sp ?N ?stid ?R ?itr = _ ] =>
      lazymatch itr with
      | Ret _ =>
          eapply SRed.ret
      | Tau _ =>
          eapply SRed.tau
      | vis (Assume _) _ =>
          eapply SRed.vis_agE
      | vis (AssumeRes _) _ =>
          eapply SRed.vis_agE
      | vis (Guarantee _) _ =>
          eapply SRed.vis_agE
      | vis (Spawn ?fn _) _ =>
          etransitivity;
          [ eapply SRed.vis_spawn
          | unfold SModTr.HoareSpawn;
            tac
          ]
      | vis (Yield _) _ =>
          etransitivity;
          [ eapply SRed.vis_yield
          | tac
          ]
      | vis GetTid _ =>
          etransitivity;
          [ eapply SRed.vis_gettid
          | tac
          ]
      | vis (Call ?fn _) _ =>
          etransitivity;
          [ eapply SRed.vis_call
          | unfold SModTr.HoareCall;
            tac
          ]
      | vis (SPut _ _) _ =>
          eapply SRed.vis_pgE
      | vis (SGet _) _ =>
          eapply SRed.vis_pgE
      | vis (Choose _) _ =>
          eapply SRed.vis_coreE
      | vis (Take _) _ =>
          eapply SRed.vis_coreE
      | vis (IO _ _) _ =>
          eapply SRed.vis_coreE
      (* | assumeK _ _ =>
          eapply SRed.assumeK
      | guaranteeK _ _ =>
          eapply SRed.guaranteeK
      | unwrapUK _ _ =>
          eapply SRed.unwrapUK
      | unwrapNK _ _ =>
          eapply SRed.unwrapNK *)
      (* | RealUpdateK _ _ _ =>
          eapply SRed.ruK *)
      | @ITree.bind _ _ _ _ _ =>
          eapply SRed.bind
      | _ =>
          reflexivity
      end
  end.

Ltac _hnorm_itr :=
  lazymatch goal with
  | |- match bool_decide ?P with | true => ?A | false => ?B end = _ =>
      tryif is_closed_term P
      then
        let r := eval vm_compute in (bool_decide P) in
        change (bool_decide P) with r in *;
        s; _hnorm_itr
      else reflexivity
  | [ |- Ret _ = _ ] =>
      reflexivity
  | [ |- Tau _ = _ ] =>
      reflexivity
  | [ |- vis _ _ = _ ] =>
      reflexivity
  | [ |- @ITree.bind ?E ?T ?U ?itr ?ktr = _ ] =>
      etransitivity;
      [ let itr' := fresh "itr" in
        cong (fun (itr' : itree E T) => @ITree.bind E T U itr' ktr); _hnorm_itr
      | red_bind (do 1 _hnorm_itr) ]
  (* | [ |- @SB.sandbox ?Σ ?R ?img ?imports ?scopes ?itr = _ ] =>
      etransitivity;
      [ cong (@SB.sandbox Σ R img imports scopes); _hnorm_itr | red_SB ] *)
  | [ |- @SB.sandbox ?Σ ?msk ?R ?itr = _ ] =>
      etransitivity;
      [ cong (@SB.sandbox Σ msk R); _hnorm_itr | red_SB (do 1 _hnorm_itr) ]
  (* | [ |- @SModTr.trans ?Γ ?Σ ?α ?β ?τ ?_S ?_I ?_crisG ?concG ?img ?sp ?R ?itr = _ ] =>
      etransitivity;
      [ cong (@SModTr.trans Γ Σ α β τ _S _I _crisG concG img sp R); _hnorm_itr
      | red_S (do 1 _hnorm_itr) ] *)
  | [ |- @SModTr.trans ?Γ ?Σ ?α ?β ?τ ?_S ?_I ?_crisG ?concG ?sp ?N ?stid ?R ?itr = _ ] =>
      etransitivity;
      [ cong (@SModTr.trans Γ Σ α β τ _S _I _crisG concG sp N stid R); _hnorm_itr
      | red_S (do 1 _hnorm_itr) ]
  | [ |- trigger _ = _ ] =>
      eapply trigger_vis
  (* | [ |- assume _ = _ ] =>
      eapply assume_assumeK
  | [ |- guarantee _ = _ ] =>
      eapply guarantee_guaranteeK *)
  (* | [ |- unwrapU _ = _ ] =>
      eapply unwrapU_unwrapUK
  | [ |- unwrapN _ = _ ] =>
      eapply unwrapN_unwrapNK *)
  | [ |- RealUpdate _ _ = _ ] =>
      eapply RealUpdate_RealUpdateK
  | [ |- SModTr.HoareCall _ _ _ = _ ] =>
      unfold SModTr.HoareCall;
      _hnorm_itr
  | [ |- fbody_trivial _ = _ ] =>
      unfold fbody_trivial;
      _hnorm_itr
  | [ |- cput _ _ = _ ] =>
      unfold cput;
      _hnorm_itr
  | [ |- cgetU _ = _ ] =>
      unfold cgetU;
      _hnorm_itr
  | [ |- cgetN _ = _ ] =>
      unfold cgetN;
      _hnorm_itr
  | [ |- cfunU _ _ = _ ] =>
      unfold cfunU;
      _hnorm_itr
  | [ |- cfunN _ _ = _ ] =>
      unfold cfunN;
      _hnorm_itr
  | [ |- ccallU _ _ = _ ] =>
      unfold ccallU;
      _hnorm_itr
  | [ |- ccallN _ _ = _ ] =>
      unfold ccallN;
      _hnorm_itr
  | [ |- triggerUB = _ ] =>
      unfold triggerUB;
      _hnorm_itr
  | [ |- triggerNB = _ ] =>
      unfold triggerNB;
      _hnorm_itr
  | [ |- ?itr = _ ] =>
      reflexivity
  end.

Ltac hnorm_itr :=
  etransitivity;
  [ _hnorm_itr
  | s;
    lazymatch goal with
    | |- Ret _ = _ =>
        reflexivity
    | |- Tau _ = _ =>
        reflexivity
    | |- vis _ _ = _ =>
        rewrite ?resum_to_subevent ?subevent_subevent;
        eapply vis_trigger
    | |- assumeK _ _ = _ =>
        eapply assumeK_assume
    | |- guaranteeK _ _ = _ =>
        eapply guaranteeK_guarantee
    | |- unwrapUK _ _ = _ =>
        eapply unwrapUK_unwrapU
    | |- unwrapNK _ _ = _ =>
        eapply unwrapNK_unwrapN
    | |- RealUpdateK _ _ _ = _ =>
        eapply RealUpdateK_RealUpdate
    (* | [ |- SBRed.putSB _ _ _ _ _ _ = _ ] =>
        eapply SBRed.putSB_SPut *)
    (* | [ |- SBRed.getSB _ _ _ _ _ = _ ] =>
        eapply SBRed.getSB_SGet *)
    (* | [ |- SBRed.callSB _ _ _ _ _ _ = _ ] =>
        eapply SBRed.callSB_Call *)
    (* | [ |- SBRed.spawnSB _ _ _ _ _ _ = _ ] =>
        eapply SBRed.spawnSB_Spawn *)
    | [ |- _ = _ ] =>
        reflexivity
    end
  ].
Ltac replace_l :=
  lazymatch goal with
  | [ |- environments.envs_entails ?env (?rel (?st_src, ?itr_src) (?st_tgt, ?itr_tgt)) ] =>
      refine (eq_ind_r (fun itr_src' => environments.envs_entails env (rel (st_src, itr_src') (st_tgt, itr_tgt))) _ _); cycle 1
  end.

Ltac replace_r :=
  lazymatch goal with
  | [ |- environments.envs_entails ?env (?rel (?st_src, ?itr_src) (?st_tgt, ?itr_tgt)) ] =>
      refine (eq_ind_r (fun itr_tgt' => environments.envs_entails env (rel (st_src, itr_src) (st_tgt, itr_tgt'))) _ _); cycle 1
  end.

Ltac norm_l := replace_l; [s; hnorm_itr|].
Ltac norm_r := replace_r; [s; hnorm_itr|].

Tactic Notation "norm_l" "with" tactic(tac) :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  norm_l;
  tac;
  show_until marker.

Tactic Notation "norm_r" "with" tactic(tac) :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  norm_r;
  tac;
  show_until marker.

Tactic Notation "norm" "with" tactic(tac) :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  norm_l;
  norm_r;
  tac;
  show_until marker.

  Tactic Notation "iwcase" tactic(itac) tactic(wtac) :=
    match goal with
    | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _) ] => itac
    | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _) ] => wtac
    end.

  Lemma map_Forall_union_with `{Countable K} {V} (m1 m2 : gmap K (option V)) :
    map_Forall (const is_Some) (union_with (λ _ _, Some None) m1 m2) →
    map_Forall (const is_Some) m1 ∧ map_Forall (const is_Some) m2.
  Proof.
    rewrite ?map_Forall_lookup => Hwf; split; intros i v Hi; move: (Hwf i v);
      rewrite lookup_union_with Hi; repeat destruct (_ !! i) as [[|]|]; ss; clarify; eauto.
  Qed.

  Lemma lookup_union_with_l `{Countable K} {V} (m1 m2 : gmap K (option V)) (k : K) (v : V):
    map_Forall (const is_Some) (union_with (λ _ _, Some None) m1 m2) →
    m1 !! k = Some (Some v) →
    union_with (λ _ _, Some None) m1 m2 !! k = Some (Some v).
  Proof.
    intros Hwf Hm1; rewrite lookup_union_with Hm1; destruct (m2 !! k) as [[|]|] eqn : Hm2; ss;
      apply map_Forall_lookup in Hwf; move: (Hwf k None); rewrite lookup_union_with Hm1 Hm2;
      move => /(_ eq_refl) [? ?] //.
  Qed.

  Lemma lookup_union_with_r `{Countable K} {V} (m1 m2 : gmap K (option V)) (k : K) (v : V):
    map_Forall (const is_Some) (union_with (λ _ _, Some None) m1 m2) →
    m2 !! k = Some (Some v) →
    union_with (λ _ _, Some None) m1 m2 !! k = Some (Some v).
  Proof.
    intros Hwf Hm2; rewrite lookup_union_with Hm2; destruct (m1 !! k) as [[|]|] eqn : Hm1; ss;
      apply map_Forall_lookup in Hwf; move: (Hwf k None); rewrite lookup_union_with Hm1 Hm2;
      move => /(_ eq_refl) [? ?] //.
  Qed.

  Lemma insert_union_with_l `{Countable K} {V} (m1 m2 : gmap K (option V)) (k : K) v :
    map_Forall (const is_Some) (union_with (λ _ _, Some None) m1 m2) →
    is_Some (m1 !! k) →
    <[k := v]> (union_with (λ _ _, Some None) m1 m2) =
    union_with (λ _ _, Some None) (<[k := v]> m1) m2.
  Proof.
    intros Hwf [? Hm1]; apply insert_union_with_l.
    destruct (m2 !! k) as [[|]|] eqn : Hm2; ss;
      apply map_Forall_lookup in Hwf; move: (Hwf k None); rewrite lookup_union_with Hm1 Hm2;
      move => /(_ eq_refl) [? ?] //.
  Qed.

  Lemma insert_union_with_r `{Countable K} {V} (m1 m2 : gmap K (option V)) (k : K) v :
    map_Forall (const is_Some) (union_with (λ _ _, Some None) m1 m2) →
    is_Some (m2 !! k) →
    <[k := v]> (union_with (λ _ _, Some None) m1 m2) =
    union_with (λ _ _, Some None) m1 (<[k := v]> m2).
  Proof.
    intros Hwf [? Hm2]; apply insert_union_with_r.
    destruct (m1 !! k) as [[|]|] eqn : Hm1; ss;
      apply map_Forall_lookup in Hwf; move: (Hwf k None); rewrite lookup_union_with Hm1 Hm2;
      move => /(_ eq_refl) [? ?] //.
  Qed.

Ltac is_key_in k m :=
  match m with
  | {[ k := _ ]} => idtac
  | <[ k := _ ]> _ => idtac
  | <[ _ := _ ]> ?rest => is_key_in k rest
  | union_with _ ?l ?r => first [ is_key_in k l | is_key_in k r ]
  | _ => fail "Key not syntactically found"
  end.

Ltac solve_map_lookup_symbolic NODT :=
  match goal with
  | [ |- union_with ?f ?l ?r !! ?k = _ ] =>
      tryif is_key_in k l 
      then (
        eapply lookup_union_with_l;
        [eauto|eapply map_Forall_union_with in NODT as [NODT _]];
        solve_map_lookup_symbolic NODT
      )
      else (
        eapply lookup_union_with_r;
        [eauto|eapply map_Forall_union_with in NODT as [_ NODT]];
        solve_map_lookup_symbolic NODT
      )
  | [ |- <[ ?k' := ?v ]> ?m !! ?k = _ ] =>
      (* Case: Insert *)
      tryif unify k' k
      then (rewrite lookup_insert; reflexivity)
      else (
        rewrite lookup_insert_ne; [|let Hc := fresh "" in intro Hc; inversion Hc; done];
        solve_map_lookup_symbolic NODT
      )
  | [ |- {[ ?k' := ?v ]} !! ?k = _ ] =>
      (* Case: Singleton *)
      unify k' k; apply lookup_singleton
  | |- ?A => 
      (* idtac "Leaf reached or structure unknown";  *) fail
  end.

Ltac state_lookup_simpl NOD :=
  let GOAL := fresh "GOAL" in
  set (a := _ !! _); pattern a; subst a;
  match goal with [|- ?G _] => set (GOAL := G) end;
  eapply (eq_ind_r GOAL); [|solve_map_lookup_symbolic NOD];
  rewrite /GOAL /=; clear GOAL.

(* TODO : the complexity of this tactic is terrible - make it better *)
Ltac state_insert_simpl NODT :=
  let GOAL := fresh "GOAL" in
  set (a := <[_:=_]> _); pattern a; subst a;
  match goal with [|- ?G _] => set (GOAL := G) end;
  eapply (eq_ind_r GOAL);
  [|
    match goal with
    | [ |- <[?k:=?v]> (union_with ?f ?l ?r) = _ ] =>
        tryif is_key_in k l
        then (
          etransitivity;
          [ eapply insert_union_with_l;
            [ eauto
            | eapply map_Forall_union_with in NODT as [NODT _];
              eexists; state_lookup_simpl NODT; reflexivity
            ]
          | eapply map_Forall_union_with in NODT as [NODT _]; 
            state_insert_simpl NODT ]
        )
        else (
          etransitivity;
          [ eapply insert_union_with_r;
            [ eauto
            | eapply map_Forall_union_with in NODT as [_ NODT];
              eexists; state_lookup_simpl NODT; reflexivity
            ]
          | eapply map_Forall_union_with in NODT as [_ NODT]; 
            state_insert_simpl NODT ]
        )
    | [ |- <[?k:=_]>{[?k':=?v]} = _ ] => (* Case: Singleton *)
        unify k' k; apply insert_singleton
    | [ |- <[?k:=_]>(<[?k':=?v]>?m) = _ ] => (* Case: Insert *)
        tryif unify k' k
        then (rewrite insert_insert; reflexivity)
        else (
          rewrite insert_ne; [|let Hc := fresh "" in intro Hc; inversion Hc; done];
          state_insert_simpl NODT
        )
    
    | |- ?A => 
        (* idtac "Leaf reached or structure unknown";  *) fail
    end
  ];
  rewrite /GOAL //=; clear GOAL.

(* Ltac state_insert_simpl NOD :=
  let GOAL := fresh "GOAL" in
  set (a := <[_:=_]> _); pattern a; subst a;
  match goal with [|- ?G _] => set (GOAL := G) end;
  eapply (eq_ind_r GOAL); [|solve_map_insert_symbolic NOD];
  rewrite /GOAL /=; clear GOAL. *)

Ltac _wstep_l :=
  match goal with
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, tau;; _) _) ] =>
      iApply wsim_tau_src
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, Ret _ >>= _) _) ] =>
      rewrite bind_ret_l
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _) _) ] =>
      let name := fresh "_q" in iApply wsim_take_src; iIntros (name)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Assume ?P) >>= _) _) ] =>
      unfold_pre_post_term P; iApply wsim_assume_src; iIntrosFresh "ASM"
      (* first [
        tcsearch constr:(WP P)
          ltac:(fun c =>
            iApply (wsim_assume_src_WP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i:=c)); simpl);
        match goal with
        | [ |- environments.envs_entails _ (?P' -∗ _)] =>
          unfold_pre_post_term P'; iIntrosFresh "ASM"
        end
      | unfold_pre_post_term P; iApply wsim_assume_src; iIntrosFresh "ASM"
      ] *)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (AssumeRes _) >>= _) _) ] =>
      iApply wsim_assume_res_src; iIntrosFresh "ASM"
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, assume _ >>= _) _) ] =>
      let name := fresh "asm" in iApply wsim_asm_src; iIntros (name)
  (* | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, (SB.sandbox _ _ _ (trigger (SPut _ _))) >>= _) _) ] =>
      iApply wsim_nodup_src; iIntros (?); iApply wsim_sput_src_sandbox; [s;eauto|alist_upd_simpl]
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, (SB.sandbox _ _ _ (trigger (SGet _))) >>= _) _) ] =>
      let name := fresh "NODS" in
      iApply wsim_nodup_src; iIntros (name); iApply wsim_sget_src_sandbox; [s;eauto|alist_find_simpl]; clear name *)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) _) ] =>
      let name := fresh "_q" in
      iApply wsim_unwrapU_src; iIntros (name) "%";
      match goal with [ H: ?x = Some _ |- _ ] => let G := fresh "G" in rename H into G; try rewrite -> G in * end
  end.

Ltac wstep_l_core :=
  _wstep_l; try alist_find_simpl; s; des_pairs; s.

Ltac wstep_l :=
  norm_l with do 1 try wstep_l_core.

Ltac wsteps_l :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  norm_l;
  (hrepeat (do 1 wstep_l_core; norm_l));
  show_until marker.

Ltac _wstep_r :=
  match goal with
  (** tgt **)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, tau;; _)) ] =>
      iApply wsim_tau_tgt
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, Ret _ >>= _) ) ] =>
      rewrite bind_ret_l
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose _) >>= _) ) ] =>
      let name := fresh "_q" in iApply wsim_choose_tgt; iIntros (name)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _) ) ] =>
      unfold_pre_post_term P; iApply wsim_guarantee_tgt; iIntrosFresh "GRT"
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, guarantee _ >>= _)) ] =>
      let name := fresh "grt" in iApply wsim_guar_tgt; iIntros (name)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (SGet _) >>= _)) ] =>
      let NODT := fresh "NODT" in
      iApply wsim_nodup_tgt; iIntros (NODT);
      iApply wsim_sget_tgt; state_lookup_simpl NODT; clear NODT
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (SPut _ _) >>= _)) ] =>
      let NODT := fresh "NODT" in
      iApply wsim_nodup_tgt; iIntros (NODT);
      iApply wsim_sput_tgt; state_insert_simpl NODT; clear NODT
  end.

Ltac wstep_r_core :=
  _wstep_r; s; des_pairs; s.

Ltac wstep_r :=
  norm_r with do 1 try wstep_r_core.

Ltac wsteps_r :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  norm_r;
  (hrepeat (do 1 wstep_r_core; norm_r));
  show_until marker.

Ltac _wstep :=
  match goal with
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, Ret _) (_, Ret _))] =>
      iApply wsim_unfold; iIntros "?"; iApply wsim_ret; iFrame
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (IO _ _) >>= _) (_, trigger (IO _ _) >>= _))] =>
      iApply wsim_io; iIntros "%"
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger GetTid >>= _) (_, trigger GetTid >>= _))] =>
      iApply wsim_gettid; iIntros "%"
  end.

Ltac wstep :=
  norm with do 1 _wstep; s; des_pairs; s.

Ltac _wforce_l :=
  match goal with
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose ?T) >>= _) _) ] =>
      iApply wsim_choose_src
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _) _) ] =>
      unfold_pre_post_term P; iApply wsim_guarantee_src
      (* first [
        tcsearch constr:(WP P)
          ltac:(fun c =>
          iApply (wsim_guarantee_src_WP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i:=c)); [try set_solver|try set_solver|simpl WP_space]);
        match goal with
        | [ |- environments.envs_entails _ (?P' ∗ _)] =>
          unfold_pre_post_term P'
        end
      | unfold_pre_post_term P; iApply wsim_guarantee_src
      ] *)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, unwrapN _ >>= _) _) ] =>
      iApply wsim_unwrapN_src
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, guarantee _ >>= _) _) ] =>
      iApply wsim_guar_src
  end.

Ltac wforce_l_core :=
  norm_l with do 1 _wforce_l.

Tactic Notation "wforce_l" :=
  wforce_l_core; [..|try iExists _].

Tactic Notation "wforce_l" uconstr(p) :=
  wforce_l_core; [..|iExists p].

Ltac wforces_l :=
  hrepeat do 1 wforce_l.

Ltac _wforce_r :=
  match goal with
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _)) ] =>
      iApply wsim_take_tgt
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Assume ?P) >>= _)) ] =>
      (* first [
        tcsearch constr:(WP P)
          ltac:(fun c =>
            unshelve iApply (wsim_assume_tgt_WP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i:=c)); s;
            [first [apply nclose_subseteq|try set_solver]
            |first [apply nclose_subseteq|try set_solver]
            |simpl WP_space]
          );
        match goal with
        | [ |- environments.envs_entails _ (?P' ∗ _)] =>
          unfold_pre_post_term P'
        end
      | unfold_pre_post_term P; iApply wsim_assume_tgt ] *)
    unfold_pre_post_term P; iApply wsim_assume_tgt
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (AssumeRes _) >>= _)) ] =>
      iApply wsim_assume_res_tgt
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, assume _ >>= _)) ] =>
      iApply wsim_asm_tgt
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, RealUpdate ?P ?Q >>= _)) ] =>
      unfold_pre_post_term P; unfold_pre_post_term Q; iApply wsim_ru_tgt_simple
  end
.

Ltac wforce_r_core :=
  norm_r with do 1 _wforce_r; s.

Tactic Notation "wforce_r" :=
  wforce_r_core; try (iExists _).

Tactic Notation "wforce_r" uconstr(p) :=
  wforce_r_core; iExists p.

Ltac wforces_r :=
  hrepeat do 1 wforce_r.

Ltac winline_l :=
  norm_l with
    do 1 iApply wsim_inline_src; [try prove_inline_cond|unfold_cris_defs].

Ltac winline_r :=
  norm_r with
    do 1 iApply wsim_inline_tgt; [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs].

Ltac wcall hyps :=
  (norm with do 1 iApply wsim_call); [try prove_sb_cond|
  iSplitL hyps; [try done| iIntros "% % %"; iIntrosFresh "IST"];
  move_aux].

Ltac wspawn :=
  (norm with do 1 iApply wsim_spawn); [try prove_sb_cond|].

Ltac wyield hyps :=
  (norm with do 1 iApply wsim_yield);
  iSplitL hyps; [try done| iIntros "% %"; iIntrosFresh "IST"];
  move_aux.

Ltac wby_coind CIH :=
  iApply wsim_progress; iApply wsim_base; iIntrosFresh "I";
  iApply CIH.

Ltac winit_simF :=
  initialize_simF;
  iApply wsim_isim;
  try (
      iDestruct "IST" as "[% [W [TID IST]]]"; des; subst;
      iApply wsim_init_winv; iSplitL "W"; [et; fail|]; hss_copset;
      hrepeat do 1 (unfold_mod; s)).

  Ltac step_l := iwcase (do 1 istep_l) (do 1 wstep_l).
  Ltac steps_l := iwcase (do 1 isteps_l) (do 1 wsteps_l).

  Ltac step_r := iwcase (do 1 istep_r) (do 1 wstep_r).
  Ltac steps_r := iwcase (do 1 isteps_r) (do 1 wsteps_r).

  Ltac step := iwcase (do 1 istep) (do 1 wstep).

  Tactic Notation "force_l" := iwcase (do 1 iforce_l) (do 1 wforce_l).
  Tactic Notation "force_l" uconstr(p) := iwcase (do 1 iforce_l p) (do 1 wforce_l p).
  Ltac forces_l := iwcase (do 1 iforces_l) (do 1 wforces_l).

  Tactic Notation "force_r" := iwcase (do 1 iforce_r) (do 1 wforce_r).
  Tactic Notation "force_r" uconstr(p) := iwcase (do 1 iforce_r p) (do 1 wforce_r p).
  Ltac forces_r := iwcase (do 1 iforces_r) (do 1 wforces_r).

  Ltac inline_l := iwcase (do 1 iinline_l) (do 1 winline_l).
  Ltac inline_r := iwcase (do 1 iinline_r) (do 1 winline_r).
  Ltac unfold_cris_defs :=
    rewrite /SB.sandbox_body; s;
    (hrepeat do 1 match goal with |- context[cfunU ?x] => rewrite {1}/x end);
    rewrite /cfunU;
    (hrepeat do 1 match goal with |- context[cfunN ?x] => rewrite {1}/x end);
    rewrite /cfunN;
    rewrite /SModTr.trans_fnsem.
  (* TEMP *)

  Lemma wsim_HoareFun_src fsp msk fbd arg fl_src fl_tgt Ist RR r g ps pt st_src st_tgt itr_tgt :
    (∀ N tid x varg, TID tid -∗
      YIELD tid -∗
      precond fsp (N, tid) x varg arg -∗
      wsim fl_src fl_tgt Ist (↑N, ↑N) r g Any.t Any.t
        (λ src tgt, TID tid ∗ YIELD tid ∗ winv (↑N, ↑N) ∗
          ∃ ret, postcond fsp (N, tid) x src.2 ret ∗ RR (src.1, ret) tgt) true pt
        (st_src, SB.sandbox msk (fbd N tid varg))
        (st_tgt, itr_tgt)) ⊢
    wsim fl_src fl_tgt Ist (∅, ∅) r g Any.t Any.t RR ps pt
      (st_src, SB.sandbox msk (SModTr.HoareFun (Some fsp) fbd arg))
      (st_tgt, itr_tgt).
  Proof.
    iIntros "sim".
    rewrite /SModTr.HoareFun.
    norm_l. des_if; step_l; ss. destruct _q as [N tid].
    steps_l. des_if; step_l; ss. rename _q into m.
    steps_l. des_if; step_l; ss. rename _q into varg.
    steps_l. des_if; step_l; ss.
    iDestruct "ASM" as "[? [? W]]"; iApply wsim_fold; iFrame "W".
    steps_l. des_if; step_l; ss. steps_l.
    rewrite {2}(bind_ret_r_rev itr_tgt).
    iPoseProof ("sim" with "[$] [$] [$]") as "sim".
    iApply wsim_bind; iFrame "sim".
    clear dependent st_src st_tgt.
    iIntros (st_src r_s st_tgt r_t) "[? [? [W [%ret [Post RR]]]]]".
    steps_l. des_ifs; steps_l; ss.
    force_l ret. steps_l. des_ifs; steps_l; ss.
    forces_l. iFrame. steps_l. des_ifs; steps_l; ss. force_l. iFrame "Post". step.
  Qed.

  Ltac iStartSim := init_simF; unfold_cris_defs; iApply wsim_HoareFun_src; eauto; ss.

  Lemma simF_alloc : ISim.sim_fun open MemA MemI IstFull (Some MemHdr.alloc).
  Proof using.
    iStartSim.
    iIntros (N tid x varg) "TID YIELD PRE".
    unfold_pre_post.
    iDestruct "PRE" as "[-> [-> %]]".
    steps_r. rewrite Any.upcast_downcast. steps_r.

    iDestruct "IST" as (? ? ? ?) "([-> ->] & [% [% [% [[-> %] >B]]]] & ->)"; des.
    steps_r. rewrite Any.upcast_downcast. steps_r. case_bool_decide; [|lia]. steps_r.

    rename _q into pad.
    set (blk := Mem.nb mem_tgt + pad).
    iPoseProof (own_valid with "B") as "%".
    iPoseProof (mem_ra_alloc with "B") as ">B"; et.
    iDestruct "B" as "[BLK WHT]". iPoseProof (points_to_transform with "WHT") as "WHT".

    force_l ((Vptr (blk, 0%Z)) ↑). step.
    iExists _.
    repeat (iSplit; first done).
    iExists _, _, _, _; iSplit; [iPureIntro; split; refl|iSplit; eauto].
    repeat (iSplit; eauto).
    iExists _; iSplit; eauto.
    iPureIntro; esplits; eauto; cycle 1.
    { ii; ss. unfold update in *. rewrite /mem_wf in H6. des_ifs. exploit H6; eauto. nia. }

    intros blk' ofs'; rewrite ?discrete_fun_lookup_op /= Z.add_0_l Z.sub_0_r repeat_length.
    destruct (mem_tgt.(Mem.cnts) blk ofs') eqn:E.
    { exfalso. exploit H6; et. nia. }
    ss. hexploit (H5 blk ofs'); et.
    rewrite E. intro U. des; ss.

    case_bool_decide as Hblkofs; [destruct Hblkofs as [Hblk Hofs]|].
    { rewrite repeat_nth_some; [subst|lia]; rewrite U left_id; right; esplits; eauto.
      rewrite /update; destruct (dec _ _); ss; case_bool_decide; ss.
    }
    rewrite right_id /update; destruct (_ blk' ofs') eqn : ?; hexploit (H5 blk' ofs');
        i; des; destruct (dec _ _); ss; try case_bool_decide; naive_solver.
  (*SLOW*)Qed.

  Lemma simF_free : ISim.sim_fun open MemA MemI IstFull (Some MemHdr.free).
  Proof using.
    iStartSim.
    iIntros (N tid [[blk ofs] v] varg) "?? Pre"; unfold_pre_post.
    iDestruct "Pre" as "[-> [-> ↦]]".
    iDestruct "IST" as (? ? ? ?) "([-> ->] & [% [% [% [[-> %] >B]]]] & ->)"; des.

    steps_l.
    steps_r. rewrite Any.upcast_downcast /=. steps_r. rewrite Any.upcast_downcast /=.
    steps_r.

    iPoseProof (mem_ra_lookup with "[B ↦]") as "[%HIT ->]"; et; iFrame. steps_r.

    force_l. iMod (mem_ra_free with "[B ↦]") as "H"; et; iFrame.
    step. iExists _; repeat (iSplit; et).
    iExists _, _, _, _; repeat (iSplit; et).
    iExists _; iSplit; eauto.
    iPureIntro. esplits; eauto.
    - ii. s. rewrite /mem_ra_upd /update.
      repeat destruct dec; case_bool_decide; des; ss; subst; naive_solver.
    - rewrite /update. ii. ss. repeat destruct dec; ss; subst; et.
  (*SLOW*)Qed.

  Lemma simF_load : ISim.sim_fun open MemA MemI (MemA.init_cond csl genv) IstFull (Some MemHdr.load).
  Proof using.
    init_simF.
    iDestruct "IST" as (? ? ? ?) "(% & [% [% [% [% >B]]]] & %)". des; subst; hss.

    steps_l. iDestruct "ASM" as "[[-> PTS] ->]".
    rename _q5 into blk, _q6 into ofs, _q4 into q, _q2 into val. hss_r. steps_r. hss_r. steps_r.
    iPoseProof (mem_ra_lookup with "[B PTS]") as "%"; et; iFrame. des.
    rewrite H3. steps_r.

    forces_l. iFrame "PTS". iSplit; eauto. step.
    repeat (iSplit; et). iExists _, [_], _, _. repeat (iSplit; et). iExists _, _. iSplit; et.
  (*SLOW*)Qed.

  Lemma simF_store : ISim.sim_fun open MemA MemI (MemA.init_cond csl genv) IstFull (Some MemHdr.store).
  Proof using.
    init_simF.
    iDestruct "IST" as (? ? ? ?) "(% & [% [% [% [% >B]]]] & %)". des; subst; hss.

    steps_l. iDestruct "ASM" as "[[-> PT]->]". hss_r. steps_r. hss_r. steps_r.
    iPoseProof (mem_ra_lookup with "[B PT]") as "%"; et; iFrame. des.
    rewrite H3. steps_r.
    (* erewrite mem_get_sound; et. iSplit; et. *)

    iMod (mem_ra_update with "[B PT]") as "[B PT]"; et; iFrame.
    forces_l. iFrame "PT". iSplit; et. step. iSplit; et.

    iExists st_srcL, [_], _, _. repeat (iSplit; et).
    iExists _, (mem_ra_upd mem_src _ _ _). iSplit; et.
    iPureIntro. esplits; et.
    - ii. s. rewrite /mem_ra_upd /update.
      destruct dec; ss; subst. des_ifs. right. et.
    - ii. ss. destruct dec; ss; subst; et.
  (*SLOW*)Qed.

  Lemma simF_cmp : ISim.sim_fun open MemA MemI (MemA.init_cond csl genv) IstFull (Some MemHdr.cmp).
  Proof using.
    init_simF.
    iDestruct "IST" as (? ? ? ?) "(% & [% [% [% [% >B]]]] & %)". des; subst; hss.

    steps_l. iDestruct "ASM" as "[[[-> %Hcmp] [P1 P2]] ->]". hss_r. steps_r. hss_r. steps_r.
    iMod ("P2" with "P1") as (????) "(P0 & P1 & P)".
    iPoseProof (mem_ra_cmp with "[B P0 P1]") as "%"; et; iFrame.
    iMod ("P" with "[P0 P1]") as "P"; iFrame.

    destruct (Mem.vcmp mem_tgt _q5 _q6) as [r|] eqn: E; ss. inv H1.
    steps_r. forces_l. iFrame "P". iSplit; et. step. iSplit.
    { destruct _q5, _q6; depdes E; try destruct blkofs; try destruct blkofs0; ss;
        try by destruct n; ss; des_ifs.
    }
    iExists _, [_], _, _. repeat (iSplit; et). iExists _, _. iSplit; et.
  (*SLOW*)Qed.

  Lemma simF_cas : ISim.sim_fun open MemA MemI (MemA.init_cond csl genv) IstFull (Some MemHdr.cas).
  Proof using.
    init_simF.

    iDestruct "IST" as (? ? ? ?) "(% & [% [% [% [% >B]]]] & %)". des; subst; hss.
    steps_l. iDestruct "ASM" as "[[[-> %Hcmp] [PT [P1 P2]]] ->]".
    rename _q10 into v_cur, _q11 into blk, _q12 into ofs, _q8 into v_cmp, _q6 into v_new.
    hss_r. steps_r.
    (* rename q14 into q, q12 into v. *)

    iMod ("P2" with "P1") as (????) "(P1 & P2 & P)".
    iPoseProof (mem_ra_lookup with "[B PT]") as "%"; et; [iFrame|]. des.
    iPoseProof (mem_ra_cmp with "[B P1 P2]") as "%"; et; [iFrame|].
    iMod ("P" with "[P1 P2]") as "P"; iFrame.

    inline_r. do 3 (steps_r; hss). rewrite H3. steps_r; hss. steps_r.
    inline_r. do 3 (steps_r; hss). rewrite H4. steps_r; hss. steps_r.

    set (is_succ := dec (MemSpec.compare_val v_cur v_cmp) (Vint 1) : bool).
    set (v_upd := if is_succ then v_new else v_cur).
    iMod ((mem_ra_update v_upd) with "[B PT]") as "[B PT]"; et; [iFrame|].

    des_ifs.
    { des_sumbool; subst.
      steps_r. inline_r. hss_r. steps_r. hss_r. steps_r. rewrite H3. steps_r. hss_r. steps_r.
      forces_l. subst is_succ v_upd. des_ifs; des_sumbool; ss. iFrame "PT P". iSplit; eauto.
      step. iSplit; eauto.
      iExists _, [_], _, _. repeat (iSplit; et). iExists _, _. iFrame "B". iSplit; eauto.
      iPureIntro; esplits; eauto.
      - ii. rewrite /mem_ra_upd. s. des_ifs; et.
      - ii. ss. des_ifs; et. bsimpl; des; des_sumbool; subst. eapply H6; et.
    }
    { des_sumbool; subst.
      steps_r.
      forces_l. subst is_succ v_upd. rewrite ?Hcmp; des_ifs; des_sumbool; clarify.
      iFrame "PT P". iSplit; eauto.
      step. iSplit; eauto.
      iExists _, [_], _, _. repeat (iSplit; et). iExists _, _. iFrame "B". iSplit; eauto.
      iPureIntro; esplits; eauto.
      rewrite /mem_ra_upd; ii; des_ifs; bsimpl; des; des_sumbool; subst; right; esplits; eauto.
    }
  (*SLOW*)Qed.

  Theorem sim : ISim.t open MemA MemI (MemA.init_cond csl genv) IstFull.
  Proof using.
    init_sim.
    - rewrite /IstFull /MemA /MemI. unfold_mod. s. splits; eauto.
      iIntros "P". iExists [], [_], [], [].
      repeat iSplit; et.
      { iPureIntro. ss. }
      iExists _, _. iFrame. iPureIntro. esplits; et.
      + ii. rewrite /mem_init_val /Mem.load_mem.
        uo; des_ifs; bsimpl; des; des_sumbool; subst; ss;
          rewrite ?Heq0 ?Heq1 ?Heq2; des_ifs; et.
      + ii. revert H1. rewrite /Mem.load_mem; uo; s. des_ifs.
        i. inv H1. eapply nth_error_Some. unfold Mem.load_mem in H3; ss.
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
      (MemA, MemA.init_cond csl genv)
      (MemI, emp%I).
  Proof using. eapply main_adequacy, sim; eauto. Qed.
End MemIA. End MemIA.

(* Module MemIA. Section MemIA.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !memG}.

  Theorem sim_real_to_hoare : ISim.t open MemA.t MemP.t emp%I IstEq.
  Proof using.
    init_sim; et;
      (init_simF; iDestruct "IST" as "->"; steps_r;
       iApply wsim_eqit_src; [|iApply (wsim_lat_real_to_hoare _ fbody_trivial)];
       rewrite ?SRed.core ?SBRed.choose; refl).
  Qed.

  Theorem ctxr csl genv :
    ctx_refines
      (MemA.t, MemA.init_cond csl genv)
      (MemI.t csl genv, emp%I).
  Proof using.
    etrans; cycle 1.
    { eapply MemIP.ctxr. }
    { rewrite mod_addc_empty_l. eapply ctxr_cond_frameR_simpl.
      eapply main_adequacy, sim_real_to_hoare. }
  Qed.
End MemIA. End MemIA. *)
