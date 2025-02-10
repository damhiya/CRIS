Require Import CRIS.

Require Import SchHeader SchGInv.
Require Import wpsim.

Set Implicit Arguments.

Local Open Scope Qp.

Definition sch_ginv `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ}
    (υ : positive) (n : level) : invspec :=
  λ _, wpsim_ginv υ n ⊤.

Section SchRA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.

  Canonical Structure SynDepO : ofe := leibnizO {n & SRFSyn.t n}.

  Definition thst: ucmra := (SAny.t -d> optionUR (agreeR SynDepO)).
  Definition fragreeUR := optionUR (prodR fracR (agreeR thst)).
  Definition threadsF := (discrete_funUR (λ _: nat, fragreeUR)).
  Definition threadsRA := authUR threadsF.

  Class SchAGΣ (Σ: GRA) := { #[global] RA_inG :: inG threadsRA Σ }.
  Definition SchAΣ : GRA := #[threadsRA].
End SchRA.

Module SchAS. Section SchAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !SchAGΣ Σ}.

  Definition initial_threads_r: threadsRA := 
    ● ((λ tid: nat, if tid =? 0 then Some (1, to_agree (λ _, (Some (to_agree (existT 0 ⊤%SRF))))) else None): threadsF)
    ⋅ ◯ ((λ tid: nat, if tid =? 0 then Some (1/4, to_agree (λ _, (Some (to_agree (existT 0 ⊤%SRF))))) else None): threadsF).
  Definition initial_threads: iProp Σ := 
    Seal.sealing "SchA"
      (own base_γ initial_threads_r).

  Definition token_pending_r (tid: nat): threadsRA :=
    ◯ ((λ n, if (tid =? n) then None else ε): threadsF).

  Definition token_quarter_r (tid: nat) (st: SAny.t → SynDepO): threadsRA := 
    ◯ ((λ n, if (tid =? n) then Some (1/4, to_agree (λ s, Some (to_agree (st s)))) else ε): threadsF).
  Definition token_th (tid: nat) (st: SAny.t → SynDepO): iProp Σ :=
    own base_γ (token_quarter_r tid st).

  Definition token_half_r (tid: nat) (st: SAny.t → SynDepO): threadsRA := 
    ◯ ((λ n, if (tid =? n) then Some (1/2, to_agree (λ s, Some (to_agree (st s)))) else ε): threadsF).
  Definition token_half (tid: nat) (st: SAny.t → SynDepO): iProp Σ := 
    Seal.sealing "SchA"
      (own base_γ (token_half_r tid st)).

  Definition token_three_quarter_r (tid: nat) (st: SAny.t → SynDepO): threadsRA := 
    ◯ ((λ n, if (tid =? n) then Some (3/4, to_agree (λ s, Some (to_agree (st s)))) else ε): threadsF).
  Definition token_three_quarter (tid: nat) (st: SAny.t → SynDepO): iProp Σ := 
    Seal.sealing "SchA"
      (own base_γ (token_three_quarter_r tid st)).

  Definition token_one_r (tid: nat) (st: SAny.t → SynDepO): threadsRA := 
    ◯ ((λ n, if (tid =? n) then Some (1, to_agree (λ s, Some (to_agree (st s)))) else ε): threadsF).
  Definition token_one (tid: nat) (st: SAny.t → SynDepO): iProp Σ := 
    Seal.sealing "SchA"
      (own base_γ (token_one_r tid st)).

  Definition idle (tid: nat): iProp Σ := 
    Seal.sealing "SchA" (own base_γ (token_pending_r tid)).
  Definition active (tid: nat) (st: SAny.t → SynDepO): iProp Σ := 
    Seal.sealing "SchA" (own base_γ (token_quarter_r tid st)).
  Definition done (tid: nat) (st: SAny.t → SynDepO): iProp Σ := 
    Seal.sealing "SchA" (own base_γ (token_three_quarter_r tid st)).
  Definition joined (tid: nat) (st: SAny.t → SynDepO): iProp Σ := 
    Seal.sealing "SchA" (own base_γ (token_one_r tid st)).

  Section RA.

    Lemma fragree_incl_false x:
      (Some x: fragreeUR) ≼ (None: fragreeUR) → False.
    Proof.
      i. inv H. destruct x0.
      - rewrite -Some_op in H0. inv H0.
      - rewrite right_id in H0. inv H0.
    Qed.

    Lemma split_thread (ths: threadsF) tid:
      ths ≡ ((λ n, if (tid =? n) then ths tid else ε): threadsF) ⋅ ((λ n, if (tid =? n) then ε else ths n): threadsF).
    Proof.
      intros x.
      rewrite discrete_fun_lookup_op. des_ifs.
      - rewrite Nat.eqb_eq in Heq. subst. rewrite right_id. ss.
      - rewrite left_id. ss.
    Qed.

    Lemma token_quarter_quarter tid (Q: SAny.t → SynDepO):
      token_half_r tid Q ≡ (token_quarter_r tid Q) ⋅ (token_quarter_r tid Q).
    Proof.
      unfold token_half_r, token_quarter_r.
      rewrite -auth_frag_op. f_equiv.
      intros x. rewrite discrete_fun_lookup_op. des_ifs.
      rewrite -Some_op -pair_op frac_op Qp.quarter_quarter agree_idemp //.
    Qed.

    Lemma token_quarter_half tid (Q: SAny.t → SynDepO):
      token_three_quarter_r tid Q ≡ (token_quarter_r tid Q) ⋅ (token_half_r tid Q).
    Proof.
      unfold token_half_r, token_quarter_r, token_three_quarter_r.
      rewrite -auth_frag_op. f_equiv. intros x. 
      rewrite discrete_fun_lookup_op. des_ifs.
      rewrite -Some_op -pair_op frac_op //.
      replace (1/4+1/2) with (3/4) by compute_done.
      rewrite agree_idemp //.
    Qed.

    Lemma token_half_half tid (Q: SAny.t → SynDepO):
      token_one_r tid Q ≡ (token_half_r tid Q) ⋅ (token_half_r tid Q).
    Proof.
      unfold token_one_r, token_half_r.
      rewrite -auth_frag_op. f_equiv. intros x.
      rewrite discrete_fun_lookup_op. des_ifs.
      rewrite -Some_op -pair_op frac_op Qp.half_half agree_idemp //.
    Qed.

    Lemma shot_thread (ths_b ths_w: threadsF) tid (Q: SAny.t → SynDepO)
      (IDLE: ths_b tid = None ∧ ths_w tid = None)
      (VLD: ✓ ths_b ∧ ✓ ths_w)
    :
      ● ths_b ⋅ ◯ ths_w
      ~~> ● ((λ n, if (tid =? n) then Some (1, to_agree (λ s, Some (to_agree (Q s)))) else ths_b n): threadsF)
          ⋅ ◯ ths_w 
          ⋅ (token_half_r tid Q)
          ⋅ (token_quarter_r tid Q)
          ⋅ (token_quarter_r tid Q).
    Proof.
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

  End RA.

  Variable υ : univ_id.
  Variable n : level.
  Variable Spc_user : string -> option fspec.

  Section SPEC.
    (* TODO : clarify with WP tc *)
    Definition fspec_spawnable (univ : positive) (n : level) (fsp : fspec) (tid : nat) (m : meta fsp)
        (vargs args : Any.t) (pre : iProp Σ) (postS: SAny.t -> SynDepO) : Prop :=
      ((wpsim_ginv univ n ⊤ ∗ pre ⊢ (precond fsp tid m vargs args))%I ∧
      (∀ ret: Any.t, 
        ((∃ vret, postcond fsp tid m vret ret)%I ⊢
          (wpsim_ginv univ n ⊤ ∗ ∃ sret: SAny.t, (⌜ret = sret↑⌝ ∗ interp_cond (postS sret))))%I)).

    Definition _spawn_spec : fspec :=
      wp_fspec υ n
        (fspec_virtual
          (λ my_tid '(mid, fargs, fvargs, pre, postS, existT fn m) varg arg,
            (⌜varg = ((mid, fn, fvargs) : nat * string * SAny.t) 
              ∧ arg = ((mid, fn, fargs) : nat * string * SAny.t)↑ 
              ∧ is_Some (Spc_user fn)
              ∧ fspec_spawnable υ n (find_fsp Spc_user fn) my_tid m fvargs↑ fargs↑ pre postS⌝
            ∗ pre ∗ (token_half my_tid postS))%I)
          (λ _ _ (_: SAny.t) _, (False)%I))
    .

    Definition spawn_spec : fspec :=
      wp_fspec υ n
        (fspec_virtual
          (λ _ '(fargs, fvargs, pre, postS, existT fn m) varg arg,
            (⌜varg = ((fn, fvargs): string * SAny.t) 
              ∧ arg = ((fn, fargs): string * SAny.t)↑
              ∧ is_Some (Spc_user fn)
              ∧ ∀ tid, fspec_spawnable υ n (find_fsp Spc_user fn) tid m fvargs↑ fargs↑ pre postS⌝
             ∗ pre)%I)
          (fun _ '(fargs, fvargs, pre, postS, existT fn m) vret ret => 
            (∃ tid: nat, ⌜vret = tid ∧ ret = tid↑⌝ ∗ (token_th tid postS))%I))
    .

    Definition yield_spec: fspec :=
      wp_fspec υ n
        (fspec_simple (λ (_: unit), ((λ varg, ⌜varg = tt↑⌝), (λ vret, ⌜vret = tt↑⌝))))%I.

    Definition join_spec: fspec :=
      wp_fspec υ n
        (fspec_simple
          (λ '(tid, postS),
            ((λ varg, (⌜varg = tid↑⌝ ∗ token_th tid postS)),
            (λ vret, (∃ ret, ⌜vret = (Some ret)↑⌝ ∗ interp_cond (postS ret)))))
        )%I.

    Definition spc : alist string fspec :=
      Seal.sealing CRIS 
        [(SchName._spawn, _spawn_spec);
         (SchName.spawn, spawn_spec);
         (SchName.yield, yield_spec);
         (SchName.join, join_spec)].

  End SPEC.
End SchAS. End SchAS.

Module SchA. Section SchA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !SchAGΣ Σ}.

  Variable univ: positive.
  Variable Spc: string -> option fspec.

  Definition _spawn : (nat * string * SAny.t) -> itree hmodE unit :=
    fun '(mtid, fn, args) =>
      trigger (Yield mtid);;;
      trigger (Call fn args↑);;;
      Sch.terminate
  .

  Definition spawn : (string * SAny.t) -> itree hmodE nat :=
    fun '(fn, args) =>
      mid <- trigger Tid;;
      tid <- trigger (Spawn SchName._spawn (mid, fn, args)↑);;
      Ret tid
  .

  Definition yield: unit -> itree hmodE unit :=
    fun _ =>
      tid <- trigger (Choose nat);;
      trigger (Yield tid)
  .

  Definition join: nat -> itree hmodE (option SAny.t) :=
    fun _ =>
      Sch.yield;;;
      trigger (Choose (option SAny.t))
  .

    Definition scopes := ["Sch"].

    Definition fnsems υ n Spc_user :=
      [(SchName._spawn, (scopes, mk_specbody (SchAS._spawn_spec υ n Spc_user) (cfunN _spawn)));
       (SchName.spawn, (scopes, mk_specbody (SchAS.spawn_spec υ n Spc_user) (cfunU spawn)));
       (SchName.yield, (scopes, mk_specbody (SchAS.yield_spec υ n) (cfunU yield)));
       (SchName.join, (scopes, mk_specbody (SchAS.join_spec υ n) (cfunU join)))].

    Program Definition Mod υ n Spc_user : SMod.t := {|
      SMod.scopes := scopes;
      SMod.fnsems := fnsems υ n Spc_user;
      SMod.initial_st := [];
    |}.
    Solve All Obligations with prove_scope.
    Next Obligation. prove_nodup. Qed.

    Definition InitCond : iProp Σ := SchAS.initial_threads.
    
    Definition t υ n Spc_global Spc_user :=
      Seal.sealing CRIS (SMod.to_hmod (sch_ginv υ n) Spc_global (Mod υ n Spc_user)).
End SchA. End SchA.
