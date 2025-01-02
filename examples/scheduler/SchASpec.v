(* Require Import CRIS.

Require Import SchHeader SchGInv.

Set Implicit Arguments.

Local Open Scope Qp.

Module SchAS. Section Sch.
  Context `{!sinvGS Σ Γ α β τ}.

  Canonical Structure SynDepO : ofe := leibnizO (sigT (λ n, SRFSyn.t n)).

  Definition thst: ucmra := (SAny.t -d> optionUR (agreeR SynDepO)).
  Definition fragreeUR := optionUR (prodR fracR (agreeR thst)).
  Definition threadsF := (discrete_funUR (λ _: nat, fragreeUR)).
  Definition threadsRA := authUR threadsF.

  (* Class GpreΓ (Γ : HRA) := {
    #[global] RA_inG :: inG threadsRA Γ;
  }. *)
  (* Class G (Γ: HRA.t) := { #[global] RA_inG :: GRA.inG threadsRA Γ }. *)
  (* Context `{!G Γ}. *)

  Notation iProp := (iProp Σ).

  Definition initial_threads_r: threadsRA := 
    ● ((λ tid: nat,
      if tid =? 0
      then Some (1, to_agree (λ _, (Some (to_agree (existT 0 ⊤%SRF)))))
      else None): threadsF)
    ⋅ ◯ ((λ tid: nat,
        if tid =? 0
        then Some (1/4, to_agree (λ _, (Some (to_agree (existT 0 ⊤%SRF)))))
        else None): threadsF).
  Definition initial_threads: iProp := 
    Seal.sealing "SchA"
      OwnM initial_threads_r.

  Definition token_pending_r (tid: nat): threadsRA :=
    ◯ ((λ n, if (tid =? n) then None else ε): threadsF).

  Definition token_quarter_r (tid: nat) (st: SAny.t → SynDepO): threadsRA := 
    ◯ ((λ n, if (tid =? n) then Some (1/4, to_agree (λ s, Some (to_agree (st s)))) else ε): threadsF).
  Definition token_th (tid: nat) (st: SAny.t → SynDepO): iProp := OwnM (token_quarter_r tid st).

  Definition token_half_r (tid: nat) (st: SAny.t → SynDepO): threadsRA := 
    ◯ ((λ n, if (tid =? n) then Some (1/2, to_agree (λ s, Some (to_agree (st s)))) else ε): threadsF).
  Definition token_half (tid: nat) (st: SAny.t → SynDepO): iProp := 
    Seal.sealing "SchA"
      (OwnM (token_half_r tid st)).

  Definition token_three_quarter_r (tid: nat) (st: SAny.t → SynDepO): threadsRA := 
    ◯ ((λ n, if (tid =? n) then Some (3/4, to_agree (λ s, Some (to_agree (st s)))) else ε): threadsF).
  Definition token_three_quarter (tid: nat) (st: SAny.t → SynDepO): iProp := 
    Seal.sealing "SchA"
      (OwnM (token_three_quarter_r tid st)).

  Definition token_one_r (tid: nat) (st: SAny.t → SynDepO): threadsRA := 
    ◯ ((λ n, if (tid =? n) then Some (1, to_agree (λ s, Some (to_agree (st s)))) else ε): threadsF).
  Definition token_one (tid: nat) (st: SAny.t → SynDepO): iProp := 
    Seal.sealing "SchA"
      (OwnM (token_one_r tid st)).

  Definition idle (tid: nat): iProp := 
    Seal.sealing "SchA" (OwnM (token_pending_r tid)).
  Definition active (tid: nat) (st: SAny.t → SynDepO): iProp := 
    Seal.sealing "SchA" (OwnM (token_quarter_r tid st)).
  Definition done (tid: nat) (st: SAny.t → SynDepO): iProp := 
    Seal.sealing "SchA" (OwnM (token_three_quarter_r tid st)).
  Definition joined (tid: nat) (st: SAny.t → SynDepO): iProp := 
    Seal.sealing "SchA" (OwnM (token_one_r tid st)).

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

  Variable univ: positive.

  Section SPEC.

    Definition fspec_spawnable (univ: positive) (fsp: fspec) (tid: nat) (m: meta fsp) (vargs args: Any.t) (pre: iProp) (postS: SAny.t -> SynDepO): Prop :=
      (((∃ n, closed_universe univ n ⊤) ∗ pre
          ⊢ (precond fsp tid m vargs args))%I
      ∧ (∀ ret: Any.t, 
          ((∃ vret, postcond fsp tid m vret ret)%I 
            ⊢ (∃ sret: SAny.t, ((∃ n, closed_universe univ n ⊤) ∗ ⌜ret = sret↑⌝ 
               ∗ interp_cond (postS sret))))%I)).

    Definition _spawn_spec (sk: Sk.t) (StbFun: Sk.t -> gname -> option fspec): fspec :=
      wfspec_inv univ 
        (fspec_virtual
          (fun my_tid '(mid, fargs, fvargs, pre, postS, existT fn m) varg arg =>
            (⌜varg = ((mid, fn, fvargs) : nat * gname * SAny.t) 
              ∧ arg = ((mid, fn, fargs) : nat * gname * SAny.t)↑ 
              ∧ is_Some (StbFun sk fn)
              ∧ fspec_spawnable univ (find_fsp sk StbFun fn) my_tid m fvargs↑ fargs↑ pre postS⌝
            ∗ pre ∗ (token_half my_tid postS))%I)
          (fun _ _ (_: SAny.t) _ => (False)%I))
    .

    Definition spawn_spec (sk: Sk.t) (StbFun: Sk.t -> gname -> option fspec): fspec :=
      wfspec_inv univ
        (fspec_virtual
          (fun _ '(fargs, fvargs, pre, postS, existT fn m) varg arg => 
            (⌜varg = ((fn, fvargs): gname * SAny.t) 
              ∧ arg = ((fn, fargs): gname * SAny.t)↑
              ∧ is_Some (StbFun sk fn)
              ∧ ∀ tid, fspec_spawnable univ (find_fsp sk StbFun fn) tid m fvargs↑ fargs↑ pre postS⌝
             ∗ pre)%I)
          (fun _ '(fargs, fvargs, pre, postS, existT fn m) vret ret => 
            (∃ tid: nat, ⌜vret = tid ∧ ret = tid↑⌝ ∗ (token_th tid postS))%I))
    .

    Definition yield_spec: fspec :=
      wfspec_inv univ
        (fspec_simple (fun (_: unit) =>
          ((fun varg => (⌜varg = tt↑⌝)%I),
           (fun vret => (⌜vret = tt↑⌝)%I))))
    .

    Definition join_spec: fspec :=
      wfspec_inv univ
        (fspec_simple (fun '(tid, postS) =>
          ((fun varg => (⌜varg = tid↑⌝ ∗ (token_th tid postS))%I),
            (fun vret => (∃ ret, ⌜vret = (Some ret)↑⌝ ∗ interp_cond (postS ret))%I))))
    .

    Definition Stb (sk: Sk.t) (StbFun: Sk.t -> gname -> option fspec): alist gname fspec :=
      Seal.sealing "ccr" 
        [(SchName._spawn, _spawn_spec sk StbFun);
         (SchName.spawn, spawn_spec sk StbFun);
         (SchName.yield, yield_spec);
         (SchName.join, join_spec)].

    Lemma Stb_nodup sk StbFun: List.NoDup (List.map fst (Stb sk StbFun)).
    Proof.
      unfold Stb. unseal "ccr". prove_nodup.
    Qed.

  End SPEC.

End Sch.
End SchAS. *)
