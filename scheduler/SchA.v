Require Import CRIS.
Require Import SchHeader SchI.
Require Import CallFilter.
From iris Require Import frac_auth.

Set Implicit Arguments.

Local Open Scope Qp.

Section SchRA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Canonical Structure SynDepO : ofe := leibnizO {n & GTerm.t n}.

  Definition thst := (SAny.t -d> SAny.t -d> optionUR (agreeR SynDepO)).
  Definition fragreeUR := optionUR (prodR fracR (agreeR thst)).
  Definition threadsF := nat -d> fragreeUR.
  Definition threadsRA := authUR threadsF.

  Definition tidRA := nat -d> optionUR fracR.

  Class schG `{!crisG Γ Σ α β τ _S _I} := {
      sch_inG_tid :: inG tidRA Γ;
      sch_inG_ths :: inG threadsRA Σ;
  }.
  Definition schΓ : HRA := #[tidRA].
  Definition schΣ : GRA := #[threadsRA].
  Global Instance subG_schG : subG schΓ Γ → subG schΣ Σ → schG.
  Proof using. solve_inG. Defined.
End SchRA.
Hint Unfold sch_inG_tid sch_inG_ths subG_schG : GRA_index.

Module SchAS. Section SchAS.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_schG: !schG}.

  (** thread **)
  Definition token_pending_r: threadsRA :=
    ◯ ((λ n, ε): threadsF).

  Definition token_quarter_r (tid: nat) (st: SAny.t → SAny.t → SynDepO): threadsRA :=
    ◯ ((λ n, if (tid =? n) then Some (1/4, to_agree (λ vs s, Some (to_agree (st vs s)))) else ε): threadsF).
  Definition token_th (tid: nat) (st: SAny.t → SAny.t → SynDepO): iProp Σ :=
    own base_γ (token_quarter_r tid st).

  Definition token_half_r (tid: nat) (st: SAny.t → SAny.t → SynDepO): threadsRA :=
    ◯ ((λ n, if (tid =? n) then Some (1/2, to_agree (λ vs s, Some (to_agree (st vs s)))) else ε): threadsF).
  Definition token_half (tid: nat) (st: SAny.t → SAny.t → SynDepO): iProp Σ :=
    Seal.sealing "SchA" (own base_γ (token_half_r tid st)).

  Definition token_three_quarter_r (tid: nat) (st: SAny.t → SAny.t → SynDepO): threadsRA := 
    ◯ ((λ n, if (tid =? n) then Some (3/4, to_agree (λ vs s, Some (to_agree (st vs s)))) else ε): threadsF).
  Definition token_three_quarter (tid: nat) (st: SAny.t → SAny.t → SynDepO): iProp Σ := 
    Seal.sealing "SchA"
      (own base_γ (token_three_quarter_r tid st)).

  Definition token_one_r (tid: nat) (st: SAny.t → SAny.t → SynDepO): threadsRA := 
    ◯ ((λ n, if (tid =? n) then Some (1, to_agree (λ vs s, Some (to_agree (st vs s)))) else ε): threadsF).
  Definition token_one (tid: nat) (st: SAny.t → SAny.t → SynDepO): iProp Σ := 
    Seal.sealing "SchA"
      (own base_γ (token_one_r tid st)).

  Definition idle (tid: nat): iProp Σ := 
    Seal.sealing "SchA" (own base_γ token_pending_r).
  Definition active (tid: nat) (st: SAny.t → SAny.t → SynDepO): iProp Σ := 
    Seal.sealing "SchA" (own base_γ (token_quarter_r tid st)).
  Definition done (tid: nat) (st: SAny.t → SAny.t → SynDepO): iProp Σ := 
    Seal.sealing "SchA" (own base_γ (token_three_quarter_r tid st)).
  Definition joined (tid: nat) (st: SAny.t → SAny.t → SynDepO): iProp Σ := 
    Seal.sealing "SchA" (own base_γ (token_one_r tid st)).

  (** tid **)
  Definition tid_admin_r (otid: option nat) : tidRA :=
    match otid with
    | Some tid =>
        (λ t, if t =? tid then ε else Some 1)
    | None =>
        (λ t, Some 1)
    end.
  Definition tid_user_r (q: Qp) (tid: nat) : tidRA :=
    (λ t, if t =? tid then Some q else ε).

  Definition tid_admin (otid: option nat) : iProp Σ :=
    Seal.sealing "SchA" (own base_γ (tid_admin_r otid)).
  Definition tid_user (q: Qp) (tid: nat) : iProp Σ :=
    Seal.sealing "SchA" (own base_γ (tid_user_r q tid)).

  (** initial resource *)
  Definition ir_threadsRA : DRA_mk threadsRA := 
    ● ((λ tid: nat, if tid =? 0 then Some (1, to_agree (λ _ _, (Some (to_agree (existT 0 ⊤%SAT))))) else None): threadsF)
    ⋅ ◯ ((λ tid: nat, if tid =? 0 then Some (1/4, to_agree (λ _ _, (Some (to_agree (existT 0 ⊤%SAT))))) else None): threadsF).
  Definition ir_threadsRA_valid : ✓ ir_threadsRA.
  Proof using.
    rewrite /ir_threadsRA. apply auth_both_valid_discrete. split.
    { exists (λ tid: nat, if tid =? 0 then Some (3/4, to_agree (λ _ _, (Some (to_agree (existT 0 ⊤%SAT))))) else None).
      intros i; des_ifs; rewrite discrete_fun_lookup_op.
      { eapply Nat.eqb_eq in Heq; subst; des_ifs.
        rewrite -Some_op -pair_op frac_op; repeat f_equiv; ss.
        { rewrite Qp.quarter_three_quarter //. }
        { rr; ii; split; ii; esplits; eauto; try set_solver. }
      }
      { rewrite Nat.eqb_neq in Heq. des_ifs; rewrite Nat.eqb_eq in Heq0; ss. }
    }
    { intros i; des_ifs; ss. }
  Qed.

  Definition ir_tidRA : DRA_mk tidRA :=
    tid_admin_r None.
  Lemma ir_tidRA_valid : ✓ (ir_tidRA). intro i; ss. Qed.

  Definition ir_schΓ : schΓ :=
    *[Some ir_tidRA].

  Definition ir_schΣ : schΣ :=
    *[Some ir_threadsRA].

  Definition init_threads : iProp Σ := 
    Seal.sealing "SchA" (own base_γ ir_threadsRA).

  Definition init_tid_r : tidRA := tid_admin_r (Some 0).
  Definition init_tid : iProp Σ := Seal.sealing "SchA" (own base_γ init_tid_r)%I.

  Section RA.

    Lemma fragree_incl_false x:
      (Some x: fragreeUR) ≼ (None: fragreeUR) → False.
    Proof using.
      i. inv H. destruct x0.
      - rewrite -Some_op in H0. inv H0.
      - rewrite right_id in H0. inv H0.
    Qed.

    Lemma split_thread (ths: threadsF) tid:
      ths ≡ ((λ n, if (tid =? n) then ths tid else ε): threadsF) ⋅ ((λ n, if (tid =? n) then ε else ths n): threadsF).
    Proof using.
      intros x.
      rewrite discrete_fun_lookup_op. des_ifs.
      - rewrite Nat.eqb_eq in Heq. subst. rewrite right_id. ss.
      - rewrite left_id. ss.
    Qed.

    Lemma token_quarter_quarter tid (Q: SAny.t → SAny.t → SynDepO):
      token_half_r tid Q ≡ (token_quarter_r tid Q) ⋅ (token_quarter_r tid Q).
    Proof using.
      unfold token_half_r, token_quarter_r.
      rewrite -auth_frag_op. f_equiv.
      intros x. rewrite discrete_fun_lookup_op. des_ifs.
      rewrite -Some_op -pair_op frac_op Qp.quarter_quarter agree_idemp //.
    Qed.

    Lemma token_quarter_half tid (Q: SAny.t → SAny.t → SynDepO):
      token_three_quarter_r tid Q ≡ (token_quarter_r tid Q) ⋅ (token_half_r tid Q).
    Proof using.
      unfold token_half_r, token_quarter_r, token_three_quarter_r.
      rewrite -auth_frag_op. f_equiv. intros x. 
      rewrite discrete_fun_lookup_op. des_ifs.
      rewrite -Some_op -pair_op frac_op //.
      replace (1/4+1/2) with (3/4) by compute_done.
      rewrite agree_idemp //.
    Qed.

    Lemma token_half_half tid (Q: SAny.t → SAny.t → SynDepO):
      token_one_r tid Q ≡ (token_half_r tid Q) ⋅ (token_half_r tid Q).
    Proof using.
      unfold token_one_r, token_half_r.
      rewrite -auth_frag_op. f_equiv. intros x.
      rewrite discrete_fun_lookup_op. des_ifs.
      rewrite -Some_op -pair_op frac_op Qp.half_half agree_idemp //.
    Qed.

    Lemma shot_thread (ths_b ths_w: threadsF) tid (Q: SAny.t → SAny.t → SynDepO)
      (IDLE: ths_b tid = None ∧ ths_w tid = None)
      (VLD: ✓ ths_b ∧ ✓ ths_w)
    :
      ● ths_b ⋅ ◯ ths_w
      ~~> ● ((λ n, if (tid =? n) then Some (1, to_agree (λ vs s, Some (to_agree (Q vs s)))) else ths_b n): threadsF)
          ⋅ ◯ ths_w 
          ⋅ (token_half_r tid Q)
          ⋅ (token_quarter_r tid Q)
          ⋅ (token_quarter_r tid Q).
    Proof using.
      rewrite -assoc -token_quarter_quarter -assoc -token_half_half -assoc.
      rewrite -auth_frag_op.
      apply auth_update.
      rewrite local_update_discrete.
      ii. split.
      - intros x. des_ifs.
      - destruct mz; ss.
        + intros x.
          do 2 rewrite discrete_fun_lookup_op. 
          rewrite -assoc (comm _ _ (c x)) assoc.
          specialize (H0 x). rewrite discrete_fun_lookup_op in H0. rewrite -H0.
          des_ifs; [|rewrite right_id //]. rewrite Nat.eqb_eq in Heq. subst. des.
          rewrite IDLE. ss.
        + intros x. rewrite discrete_fun_lookup_op. des_ifs; [|rewrite right_id //].
          des. rewrite Nat.eqb_eq in Heq. subst. rewrite IDLE0. ss.
    Qed.

    Lemma tid_admin_none_user q t :
      tid_admin None ∗ tid_user q t ⊢ False.
    Proof using.
      rewrite /tid_admin /tid_user. unseal "SchA".
      iIntros "[A U]". iCombine "A U" gives %wf.
      rewrite /tid_admin_r /tid_user_r in wf.
      specialize (wf t). rewrite discrete_fun_lookup_op in wf.
      rewrite Nat.eqb_refl -Some_op frac_op in wf. exfalso.
      apply (proj1 (Some_valid _)), (proj1 (frac_valid _)) in wf.
      eapply Qp.lt_nge; eauto using Qp.lt_add_l.
    Qed.

    Lemma tid_admin_some_user q t0 t1 :
      tid_admin (Some t0) ∗ tid_user q t1 ⊢ ⌜t0 = t1⌝.
    Proof using.
      rewrite /tid_admin /tid_user. unseal "SchA".
      iIntros "[F U]". iCombine "F U" gives %wf.
      rewrite /tid_admin_r /tid_user_r in wf.
      specialize (wf t1). rewrite discrete_fun_lookup_op in wf.
      rewrite Nat.eqb_refl in wf.
      des_ifs.
      - rewrite Nat.eqb_eq in Heq. subst. eauto.
      - rewrite Nat.eqb_neq in Heq. rewrite -Some_op frac_op in wf. exfalso.
        apply (proj1 (Some_valid _)), (proj1 (frac_valid _)) in wf.
        eapply Qp.lt_nge; eauto using Qp.lt_add_l.
    Qed.

    Lemma tid_admin_none_split_r t :
      (tid_admin_r (Some t): tidRA) ⋅ (tid_user_r 1 t: tidRA) = (tid_admin_r None: tidRA).
    Proof using.
      rewrite /tid_admin_r /tid_user_r. extensionalities x.
      rewrite !discrete_fun_lookup_op. des_ifs.
    Qed.

    Lemma tid_admin_some_user_merge t :
      tid_admin (Some t) ∗ tid_user 1 t ⊢ tid_admin None.
    Proof using.
      iIntros "[A U]".
      iPoseProof (tid_admin_some_user with "[A U]") as "%"; iFrame. des.
      rewrite /tid_admin /tid_user. unseal "SchA".
      iCombine "A U" as "AU".
      rewrite tid_admin_none_split_r; eauto.
    Qed.

    Lemma tid_admin_none_split t :
      tid_admin None ⊢ tid_admin (Some t) ∗ tid_user 1 t.
    Proof using.
      iIntros "N".
      rewrite /tid_admin /tid_user. unseal "SchA".
      rewrite -(tid_admin_none_split_r t); eauto.
      iDestruct "N" as "[A U]". iFrame.
    Qed.

    Lemma tid_user_shrink q0 q tid
      (LE: q ≤ q0)
      :
      tid_user q0 tid ⊢ tid_user q tid.
    Proof.
      rewrite /tid_user /tid_user_r. unseal "SchA".
      eapply own_mono.
      destruct (q0 - q) eqn: E.
      - exists (λ t : nat, if t =? tid then Some q1 else ε).
        ii. rewrite discrete_fun_lookup_op. des_ifs.
        apply Qp.sub_Some in E. subst. et.
      - eapply Qp.sub_None in E. exists ε. rewrite right_id.
        ii. des_ifs. eapply Qp.le_lteq in LE. eapply Qp.le_ngt in E.
        des; subst; ss.
    Qed.
    
    Lemma tid_user_merge (q0 q1: Qp) tid
      :
      tid_user q0 tid ∗ tid_user q1 tid ⊢ tid_user (q0+q1) tid.
    Proof.
      rewrite /tid_user /tid_user_r. unseal "SchA".
      rewrite -own_op. eapply own_mono. exists ε. rewrite right_id.
      ii. rewrite discrete_fun_lookup_op. des_ifs.
    Qed.

    Lemma tid_user_split (q0 q1: Qp) tid
      :
      tid_user (q0+q1) tid ⊢ tid_user q0 tid ∗ tid_user q1 tid.
    Proof.
      rewrite /tid_user /tid_user_r. unseal "SchA".
      rewrite -own_op. eapply own_mono. exists ε. rewrite right_id.
      ii. rewrite discrete_fun_lookup_op. des_ifs.
    Qed.

    (* need to update the definition [tid_user] *)
    Lemma tid_user_unique (q0 q1: Qp) tid0 tid1
      :
      tid_user q0 tid0 ∗ tid_user q1 tid1 ⊢ ⌜tid0 = tid1⌝.
    Proof.
    Admitted.
    
  End RA.

  (* Scheduler specifications *)
  Section SPEC.
    Variable sp_user : spl_type.
    Variable E_full : coPset.
    
    (* TODO : clarify with WP tc *)
    Definition fspec_spawnable fn
      (pre : SAny.t → SAny.t → iProp Σ) (postS: SAny.t → SAny.t -> SynDepO) : Prop
      :=
      ∃ fsp, alist_find (Some fn) sp_user = Some (Some fsp) ∧
      fspec_imply fsp
        (fspec_winv E_full
           (fspec_virtual
              (λ (my_tid: nat) (varg: SAny.t) arg,
                tid_user 1 my_tid ∗ ∃ sarg, ⌜arg = sarg↑⌝ ∗ pre varg sarg)%I
              (λ (my_tid: nat) (vret: SAny.t) ret,
                tid_user 1 my_tid ∗ ∃ sret, ⌜ret = sret↑⌝ ∗ interp_cond (postS vret sret)))%I)
    .

    Definition _spawn_spec : fspec := 
      fspec_virtual
        (λ '(my_tid, pre, postS) varg arg,
            ∃ fvarg farg fn,
              ⌜varg = ((my_tid, fn, fvarg) : nat * string * SAny.t)
              ∧ arg = ((my_tid, fn, farg) : nat * string * SAny.t)↑
              ∧ fspec_spawnable fn pre postS⌝
                  ∗ pre fvarg farg ∗ token_half my_tid postS)%I
        (λ _ (_: SAny.t) _, False%I)
    .

    Definition spawn_spec q : fspec :=
      fspec_winv E_full
        (fspec_virtual
          (λ '(my_tid, pre, postS) varg arg,
            tid_user q my_tid ∗
            ∃ fvarg farg fn,
              ⌜varg = ((fn, fvarg): string * SAny.t) 
              ∧ arg = ((fn, farg): string * SAny.t)↑
              ∧ fspec_spawnable fn pre postS⌝
              ∗ pre fvarg farg)%I
          (λ '(my_tid, pre, postS) vret ret,
            tid_user q my_tid ∗
            ∃ tid: nat,
              ⌜vret = tid ∧ ret = tid↑⌝ ∗ token_th tid postS)%I)
    .

    Definition yield_spec q : fspec :=
      fspec_winv E_full
        (fspec_simple (λ my_tid,
          ((λ varg, ⌜varg = tt↑⌝ ∗ tid_user q my_tid),
           (λ vret, ⌜vret = tt↑⌝ ∗ tid_user q my_tid)
          ))
        )%I.

    Definition join_spec q : fspec :=
      fspec_winv E_full
        (fspec_virtual
          (λ '(tid, postS, my_tid) varg arg,
            ⌜arg = tid↑ ∧ varg = tid⌝ ∗ tid_user q my_tid ∗ token_th tid postS)
          (λ '(tid, postS, my_tid) vret ret, 
            (∃ vsret sret, ⌜vret = (Some vsret) ∧ ret = (Some sret)↑⌝
              ∗ tid_user q my_tid ∗ interp_cond (postS vsret sret)))%I
        )%I.

    Definition get_tid_spec q : fspec :=
      fspec_simple
        (λ (tid: nat),
          ((λ varg, (⌜varg = tt↑⌝ ∗ tid_user q tid)),
           (λ vret, (⌜vret = tid↑⌝ ∗ tid_user q tid))))%I.

    Definition sp q : spl_type :=
      Seal.sealing CRIS 
        [(Some SchHdr._spawn,  Some _spawn_spec);
         (Some SchHdr.spawn,   Some (spawn_spec q));
         (Some SchHdr.yield,   Some (yield_spec q));
         (Some SchHdr.join,    Some (join_spec q));
         (Some SchHdr.get_tid, Some (get_tid_spec q))].

  End SPEC.
End SchAS. End SchAS.

Module SchA. Section SchA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_schG: !schG}.

  Definition scopes := ["Sch"].
  Definition v_internal := "Sch" ↯ "internal".

  Definition check_internal : itree crisE unit :=
    _internal <- cgetU v_internal;;
    assume (_internal = true);;;
    cput v_internal false
  .

  Definition trigger_Yield (nxt_tid: nat) : itree crisE unit :=
    cput v_internal true;;;
    SchI.trigger_Yield nxt_tid;;;
    check_internal
  .
  
  Definition fnsems sp_user : fnsems_type :=
    [(Some SchHdr._spawn, (true, wmask_all, scopes, (Some (SchAS._spawn_spec sp_user ⊤),   (cfunN (SchI._spawn check_internal)))));
     (Some SchHdr.spawn,  (true, wmask_all, scopes, (Some (SchAS.spawn_spec sp_user ⊤ 1),  (cfunN SchI.spawn))));
     (Some SchHdr.yield,  (true, wmask_all, scopes, (Some (SchAS.yield_spec ⊤ 1),          (cfunN (SchI.yield trigger_Yield)))));
     (Some SchHdr.join,   (true, wmask_all, scopes, (Some (SchAS.join_spec ⊤ 1),           (cfunN SchI.join))));
     (Some SchHdr.get_tid,(true, wmask_all, scopes, (Some (SchAS.get_tid_spec 1),          (cfunN SchI.get_tid))))].

  Program Definition Mod sp_user : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems sp_user;
    SMod.initial_st := (v_internal, false↑) :: SchI.Mod.(SMod.initial_st);
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond : iProp Σ := SchAS.init_threads ∗ SchAS.init_tid.
  
  Definition t sp sp_user :=
    Seal.sealing CRIS (SMod.to_mod sp (Mod sp_user)).

End SchA. End SchA.
