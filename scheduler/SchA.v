Require Import CRIS.
Require Import SchHeader.
Require Import CallFilter.
From iris Require Import frac_auth.

Set Implicit Arguments.

Local Open Scope Qp.

Section SchRA.
  Context `{!sinvG Γ Σ α β τ _I _S}.

  Canonical Structure SynDepO : ofe := leibnizO {n & GTerm.t n}.

  Definition thst : ucmra := (SAny.t -d> SAny.t -d> optionUR (agreeR SynDepO)).
  Definition fragreeUR := optionUR (prodR fracR (agreeR thst)).
  Definition threadsF := nat -d> fragreeUR.
  Definition threadsRA := authUR threadsF.

  Definition tidRA : ucmra := nat -d> excl' unit.

  Class schG `{!sinvG Γ Σ α β τ _I _S} := {
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
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_schG: !schG}.

  (** thread **)
  Definition token_pending_r (tid: nat): threadsRA :=
    ◯ ((λ n, if (tid =? n) then None else ε): threadsF).

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
    Seal.sealing "SchA" (own base_γ (token_pending_r tid)).
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
        (λ t, if t =? tid then ε else Excl' tt)
    | None =>
        (λ t, Excl' tt)
    end.
  Definition tid_user_r (tid: nat) : tidRA :=
    (λ t, if t =? tid then Excl' tt else ε).

  Definition tid_admin (otid: option nat) : iProp Σ :=
    Seal.sealing "SchA" (own base_γ (tid_admin_r otid)).
  Definition tid_user (tid: nat): iProp Σ :=
    Seal.sealing "SchA" (own base_γ (tid_user_r tid)).

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

    Lemma tid_admin_none_user t :
      tid_admin None ∗ tid_user t ⊢ False.
    Proof using.
      rewrite /tid_admin /tid_user. unseal "SchA".
      iIntros "[A U]". iCombine "A U" gives %wf.
      rewrite /tid_admin_r /tid_user_r in wf.
      specialize (wf t). rewrite discrete_fun_lookup_op in wf.
      des_ifs; try rewrite Nat.eqb_neq // in Heq0.
      rewrite Nat.eqb_neq // in Heq.
    Qed.

    Lemma tid_admin_some_user t0 t1 :
      tid_admin (Some t0) ∗ tid_user t1 ⊢ ⌜t0 = t1⌝.
    Proof using.
      rewrite /tid_admin /tid_user. unseal "SchA".
      iIntros "[F U]". iCombine "F U" gives %wf.
      rewrite /tid_admin_r /tid_user_r in wf.
      specialize (wf t1). rewrite discrete_fun_lookup_op in wf.
      des_ifs; try rewrite Nat.eqb_neq // in Heq1; try rewrite Nat.eqb_neq // in Heq0.
      rewrite Nat.eqb_eq in Heq; subst; eauto.
    Qed.

    Lemma tid_admin_none_split_r t :
      (tid_admin_r (Some t): tidRA) ⋅ (tid_user_r t: tidRA) = (tid_admin_r None: tidRA).
    Proof using.
      rewrite /tid_admin_r /tid_user_r. extensionalities x.
      rewrite !discrete_fun_lookup_op. des_ifs.
    Qed.

    Lemma tid_admin_some_user_merge t :
      tid_admin (Some t) ∗ tid_user t ⊢ tid_admin None.
    Proof using.
      iIntros "[A U]".
      iPoseProof (tid_admin_some_user with "[A U]") as "%"; iFrame. des.
      rewrite /tid_admin /tid_user. unseal "SchA".
      iCombine "A U" as "AU".
      rewrite tid_admin_none_split_r; eauto.
    Qed.

    Lemma tid_admin_none_split t :
      tid_admin None ⊢ tid_admin (Some t) ∗ tid_user t.
    Proof using.
      iIntros "N".
      rewrite /tid_admin /tid_user. unseal "SchA".
      rewrite -(tid_admin_none_split_r t); eauto.
      iDestruct "N" as "[A U]". iFrame.
    Qed.

  End RA.

  (* Scheduler specifications *)
  Section SPEC.
    (* Variable υ : univ_id. *)
    Context (E_sch : coPset).
    Context (sp_user : string → option fspec).

    (* TODO : clarify with WP tc *)
    (* Definition fspec_spawnable (u : univ_id) (fsp : fspec)
        (pre : SAny.t → SAny.t → iProp Σ) (postS: SAny.t → SAny.t → SynDepO) : Prop :=
      fspec_weaker
        (fspec_wsim u (fspec_virtual 
          (λ (tid: nat) (varg: SAny.t) arg,
            tid_user tid ∗ ∃ sarg, ⌜arg = sarg↑⌝ ∗ pre varg sarg)%I
          (λ (tid: nat) (vret: SAny.t) ret,
            tid_user tid ∗ ∃ sret, ⌜ret = sret↑⌝ ∗ interp_cond (postS vret sret)))%I)
        fsp. *)

    Definition _spawn_spec : fspec := 
      fspec_wsim E_sch
        (fspec_virtual
          (λ '(my_tid, pa_tid, fargs, fvargs, pre, postS, fn) varg arg,
            (⌜varg = ((pa_tid, fn, fvargs) : nat * string * SAny.t) ∧
              arg = ((pa_tid, fn, fargs) : nat * string * SAny.t)↑ ∧
              is_Some (sp_user fn)⌝ ∗
              (* ∧ fspec_spawnable υ (find_fsp sp_user fn) pre postS⌝ *)
            pre fvargs fargs ∗ token_half my_tid postS ∗ tid_user my_tid)%I)
          (λ _ (_: SAny.t) _, False%I)
        ).

    Definition spawn_spec : fspec :=
      fspec_wsim E_sch
        (fspec_virtual
          (λ '(my_tid, fargs, fvargs, pre, postS, fn) varg arg,
            (⌜varg = ((fn, fvargs): string * SAny.t) ∧
              arg = ((fn, fargs): string * SAny.t)↑ ∧
              is_Some (sp_user fn)⌝ ∗
              (* (fspec_spawnable υ (find_fsp sp_user fn) pre postS) *)
             pre fvargs fargs ∗ tid_user my_tid)%I)
          (λ '(my_tid, fargs, fvargs, pre, postS, fn) vret ret,
            ((∃ tid: nat, ⌜vret = tid ∧ ret = tid↑⌝ ∗ (token_th tid postS)) ∗ tid_user my_tid)%I))
    .

    Definition yield_spec: fspec :=
      fspec_wsim E_sch
        (fspec_simple (λ (tid: nat),
          ((λ varg, ⌜varg = tt↑⌝ ∗ tid_user tid),
           (λ vret, ⌜vret = tt↑⌝ ∗ tid_user tid)
          ))
        )%I.

    Definition join_spec: fspec :=
      fspec_wsim E_sch
        (fspec_virtual
          (λ '(tid, postS, my_tid) varg arg,
            ⌜arg = tid↑ ∧ varg = tid⌝ ∗ token_th tid postS ∗ tid_user my_tid)
          (λ '(tid, postS, my_tid) vret ret, 
            (∃ vsret sret, ⌜ret = (Some sret)↑ ∧ vret = (Some vsret)⌝
              ∗ interp_cond (postS vsret sret)) ∗ tid_user my_tid)%I
        )%I.

    Definition get_tid_spec: fspec :=
      fspec_wsim E_sch
        (fspec_simple
          (λ (tid: nat),
            ((λ varg, (⌜varg = tt↑⌝ ∗ tid_user tid)),
            (λ vret, (⌜vret = tid↑⌝ ∗ tid_user tid))))
        )%I.

    Definition sp : alist string fspec :=
      Seal.sealing CRIS 
        [(SchHdr._spawn, _spawn_spec);
         (SchHdr.spawn, spawn_spec);
         (SchHdr.yield, yield_spec);
         (SchHdr.join, join_spec);
         (SchHdr.get_tid, get_tid_spec)].

  End SPEC.
End SchAS. End SchAS.

Module SchA. Section SchA.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_schG: !schG}.

  Definition scopes := ["Sch"].
  Definition v_internal := "Sch" ↯ "internal".

  Definition trigger_Yield (nxt_tid: nat) : itree hmodE unit :=
    cput v_internal true;;;
    trigger (Yield nxt_tid);;;
    _internal <- cgetU v_internal;;
    assume (_internal = true);;;
    cput v_internal false
  .

  Definition _spawn : (nat * string * SAny.t) → itree hmodE unit :=
    λ '(pa_tid, fn, args),
      trigger_Yield pa_tid;;;
      trigger (Call fn args↑);;;
      Sch.terminate.

  Definition spawn : (string * SAny.t) → itree hmodE nat :=
    λ '(fn, args),
      my_tid <- trigger (Choose nat);;
      tid <- trigger (Spawn SchHdr._spawn (my_tid, fn, args)↑);;
      _internal <- cgetU v_internal;;
      assume (_internal = true);;;
      cput v_internal false;;;
      Ret tid.

  Definition yield: unit → itree hmodE unit :=
    λ _,
      tid <- trigger (Choose nat);;
      trigger_Yield tid.

  Definition join: nat → itree hmodE (option SAny.t) :=
    λ _,
      Sch.yield;;;
      trigger (Choose (option SAny.t)).

  Definition fnsems E_sch sp_user :=
    [(SchHdr._spawn, (wmask_all, scopes, mk_specbody (SchAS._spawn_spec E_sch sp_user) (cfunN _spawn)));
     (SchHdr.spawn,  (wmask_all, scopes, mk_specbody (SchAS.spawn_spec E_sch sp_user) (cfunU spawn)));
     (SchHdr.yield,  (wmask_all, scopes, mk_specbody (SchAS.yield_spec E_sch) (cfunU yield)));
     (SchHdr.join,   (wmask_all, scopes, mk_specbody (SchAS.join_spec E_sch) (cfunU join)))].

  Program Definition Mod E_sch sp_user : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems E_sch sp_user;
    SMod.initial_st := [(v_internal, false↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond : iProp Σ := SchAS.init_threads ∗ SchAS.init_tid.
  
  Definition t E_sch sp_global sp_user :=
    Seal.sealing CRIS (SMod.to_hmod sp_global (Mod E_sch sp_user)).
End SchA. End SchA.

Module SchAPure. Section SchAPure.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_schG: !schG}.
                    
  Definition scopes := ["Tid"].

  Definition fnsems υ :=
    [(SchHdr.get_tid, (wmask_all, scopes, mk_specbody (SchAS.get_tid_spec υ) fbody_trivial))].

    Program Definition Mod υ : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems υ;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.


  Definition InitCond : iProp Σ := SchAS.init_threads ∗ SchAS.init_tid.
  
  Definition t υ sp_global :=
    Seal.sealing CRIS (SMod.to_hmod sp_global (Mod υ)).

  (* Lemmas *)

  Lemma elim_filter msk u sp_s:
    ctx_refines
      (t u sp_s, emp%I)
      (CFilter.filter msk (t u sp_s), emp%I).
  Proof.
  Admitted.
    (* eapply main_adequacy with (Ist := fun _ _ _ => emp%I).
    init_sim; et.
    (* initialize_simF; iApply wsim_isim. *)
    init_simF.

    steps_l. forces_r. iSplitL "ASM"; et.
    steps_r. forces_l. iSplitL "GRT"; et.
    step; et.
  Qed. *)
  
End SchAPure. End SchAPure.

(* Default fspec for functions to be linked to the scheduler *)
Definition fspec_sch `{!sinvG Γ Σ α β τ _I _S, !schG} (E_sch : coPset) (fsp : fspec) : fspec :=
  fspec_wsim E_sch
    (mk_fspec (meta := nat * (meta fsp))
      (λ '(tid, x) varg arg,
        SchAS.tid_user tid ∗ fsp.(precond) x varg arg)%I
      (λ '(tid, x) vret ret,
        SchAS.tid_user tid ∗ fsp.(postcond) x vret ret)%I).