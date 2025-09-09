Require Import CRIS.
Require Import SchHeader SchI.
Require Import CallFilter.
From iris Require Import frac_auth dfrac_agree gmap_view.

Local Open Scope Qp.
Section SchRA.
  Context `{!crisG Γ Σ α β τ _S _I}.

  (* Canonical Structure SynDepO : ofe := leibnizO {n & GTerm.t n}. *)

  Definition joinRA :=
    gmap_viewUR nat (agreeR (SAny.t -d> SAny.t -d> leibnizO {n & GTerm.t n}))%type.
  Definition newtidRA := gmap_viewUR nat (agreeR nat).

  Class newschG `{!crisG Γ Σ α β τ _S _I} := {
    inG_join :: inG joinRA Σ;
    inG_tid :: inG newtidRA Γ;
  }.
  Definition newschΓ : HRA := #[newtidRA].
  Definition newschΣ : GRA := #[joinRA].
  Global Instance subG_newschG : subG newschΓ Γ → subG newschΣ Σ → newschG.
  Proof using. solve_inG. Defined.

  Context `{!concG, !newschG}.
  (* Join-related predicates *)
  Definition JoinFrag dq mtid postS : iProp Σ :=
    own base_γ (gmap_view_frag mtid (DfracOwn (dq)%Qp) (to_agree postS)).
  Definition JoinHandle mtid postS : iProp Σ :=
    JoinFrag (1/4) mtid postS.
  Definition JoinAuth m : iProp Σ :=
    own base_γ (gmap_view_auth (DfracOwn 1) m).

  (* Thread-id-related predicates *)
  Definition Tid (mtid stid : nat) : iProp Σ :=
    own base_γ (gmap_view_frag mtid (DfracOwn 1) (to_agree stid)) ∗
    TID stid ∗ YIELD stid.
  Definition TidAuth (m : gmap nat nat) : iProp Σ :=
    own base_γ (gmap_view_auth (DfracOwn 1) (to_agree <$> m)).

  Lemma Tid_Auth_Tid (m : gmap nat nat) (mtid stid : nat) :
    TidAuth m ∗ own base_γ (gmap_view_frag mtid (DfracOwn 1) (to_agree stid)) -∗
    ⌜m !! mtid = Some stid⌝.
  Proof.
    iIntros "[A F]"; iCombine "A" "F" gives %WF%gmap_view_both_dfrac_valid_discrete_total.
    destruct WF as [? [_ [_ [Hlookup [_ Hin]]]]]; rewrite lookup_fmap in Hlookup.
    destruct (m !! mtid) as [stid2|]; ss; inv Hlookup.
    eapply to_agree_included in Hin; inv Hin; done.
  Qed.
End SchRA.
Hint Unfold inG_join inG_tid subG_newschG : GRA_index.

(* Section SchRA.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Canonical Structure SynDepO : ofe := leibnizO {n & GTerm.t n}.

  Definition thst := (SAny.t -d> SAny.t -d> optionUR (agreeR SynDepO)).
  Definition fragreeUR := optionUR (prodR fracR (agreeR thst)).
  Definition threadsF := nat -d> fragreeUR.
  Definition threadsRA := authUR threadsF.
  
  Definition tidF := nat -d> optionUR fracR.
  Definition tidA := optionUR (dfrac_agreeR (optionO natO)).
  Definition tidRA := prodR tidF tidA.

  Class schG `{!crisG Γ Σ α β τ _S _I} := {
    sch_inG_tid :: inG tidRA Γ;
    sch_inG_ths :: inG threadsRA Σ;
  }.
  Definition schΓ : HRA := #[tidRA].
  Definition schΣ : GRA := #[threadsRA].
  Global Instance subG_schG : subG schΓ Γ → subG schΣ Σ → schG.
  Proof using. solve_inG. Defined.
End SchRA.
Hint Unfold sch_inG_tid sch_inG_ths subG_schG : GRA_index. *)

Module SchA. Section SchA.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !newschG}.

  (** thread **)
  (* Definition token_pending_r : threadsRA := ◯ ((λ n, ε) : threadsF).

  Definition token_quarter_r (tid : nat) (st: SAny.t → SAny.t → SynDepO) : threadsRA :=
    ◯ ((λ n, if (tid =? n) then Some (1/4, to_agree (λ vs s, Some (to_agree (st vs s)))) else ε) : threadsF).
  Definition token_th (tid : nat) (st : SAny.t → SAny.t → SynDepO): iProp Σ :=
    own base_γ (token_quarter_r tid st).

  Definition token_half_r (tid : nat) (st : SAny.t → SAny.t → SynDepO) : threadsRA :=
    ◯ ((λ n, if (tid =? n) then Some (1/2, to_agree (λ vs s, Some (to_agree (st vs s)))) else ε): threadsF).
  Definition token_half (tid : nat) (st : SAny.t → SAny.t → SynDepO): iProp Σ :=
    Seal.sealing SCH (own base_γ (token_half_r tid st)).

  Definition token_three_quarter_r (tid : nat) (st : SAny.t → SAny.t → SynDepO) : threadsRA := 
    ◯ ((λ n, if (tid =? n) then Some (3/4, to_agree (λ vs s, Some (to_agree (st vs s)))) else ε): threadsF).
  Definition token_three_quarter (tid : nat) (st : SAny.t → SAny.t → SynDepO) : iProp Σ := 
    Seal.sealing SCH (own base_γ (token_three_quarter_r tid st)).

  Definition token_one_r (tid : nat) (st : SAny.t → SAny.t → SynDepO) : threadsRA := 
    ◯ ((λ n, if (tid =? n) then Some (1, to_agree (λ vs s, Some (to_agree (st vs s)))) else ε): threadsF).
  Definition token_one (tid : nat) (st : SAny.t → SAny.t → SynDepO) : iProp Σ := 
    Seal.sealing SCH (own base_γ (token_one_r tid st)).

  Definition idle (tid : nat) : iProp Σ :=  Seal.sealing SCH (own base_γ token_pending_r).
  Definition active (tid : nat) (st : SAny.t → SAny.t → SynDepO) : iProp Σ := 
    Seal.sealing SCH (own base_γ (token_quarter_r tid st)).
  Definition done (tid : nat) (st : SAny.t → SAny.t → SynDepO) : iProp Σ := 
    Seal.sealing SCH (own base_γ (token_three_quarter_r tid st)).
  Definition joined (tid : nat) (st : SAny.t → SAny.t → SynDepO) : iProp Σ := 
    Seal.sealing SCH (own base_γ (token_one_r tid st)).

  (** tid **)
  Definition tid_admin_r (otid : option nat) : tidF :=
    match otid with
    | Some tid => λ t, if t =? tid then ε else Some 1
    | None => λ t, Some 1
    end.
  Definition tid_user_r (q : Qp) (tid : nat) : tidF :=
    (λ t, if t =? tid then Some q else ε).

  Definition tid_frag_r (q: Qp) (otid: option nat) : tidA := Some (to_frac_agree q otid).

  Definition tid_admin (otid: option nat) : iProp Σ :=
    Seal.sealing SCH (own base_γ ((tid_admin_r otid, match otid with
                                                        | Some tid => None
                                                        | None => tid_frag_r 1 None
                                                        end): tidRA)).
  Definition tid_user (q: Qp) (tid: nat) : iProp Σ :=
    Seal.sealing SCH (own base_γ ((tid_user_r q tid, tid_frag_r q (Some tid)): tidRA)). *)

  (** initial resource *)
  Definition ir_joinRA : DRA_mk joinRA := 
    (gmap_view_auth (DfracOwn 1) {[0 := (to_agree (λ _ _, existT 0 ⊥))]})%SAT.
  Lemma ir_joinRA_valid : ✓ ir_joinRA.
  Proof. rewrite /ir_joinRA; apply gmap_view_auth_valid. Qed.

  Definition ir_newtidRA : DRA_mk newtidRA := 
    (gmap_view_auth (DfracOwn 1) {[0 := (to_agree 0)]})%SAT.
  Lemma ir_newtidRA_valid : ✓ ir_newtidRA.
  Proof. rewrite /ir_joinRA; apply gmap_view_auth_valid. Qed.

  Definition ir_schΓ : newschΓ := *[Some ir_newtidRA].
  Definition ir_schΣ : newschΣ := *[Some ir_joinRA].

(*   
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
    (tid_admin_r None, tid_frag_r 1 None).
  Lemma ir_tidRA_valid : ✓ (ir_tidRA). econs; ss. Qed.

  Definition ir_schΓ : schΓ := *[Some ir_tidRA].
  Definition ir_schΣ : schΣ := *[Some ir_threadsRA].

  Definition init_threads : iProp Σ := own base_γ ir_threadsRA.
  Definition init_tid : iProp Σ := Seal.sealing SCH (own base_γ (tid_admin_r (Some 0), None))%I.

  Section RA.

    Lemma fragree_incl_false x :
      (Some x : fragreeUR) ≼ (None : fragreeUR) → False.
    Proof using.
      i. inv H1. destruct x0.
      - rewrite -Some_op in H2. inv H2.
      - rewrite right_id in H2. inv H2.
    Qed.

    Lemma split_thread (ths : threadsF) tid :
      ths ≡
      ((λ n, if (tid =? n) then ths tid else ε): threadsF) ⋅ (λ n, if (tid =? n) then ε else ths n).
    Proof using.
      intros x.
      rewrite discrete_fun_lookup_op. des_ifs.
      - rewrite Nat.eqb_eq in Heq. subst. rewrite right_id. ss.
      - rewrite left_id. ss.
    Qed.

    Lemma token_quarter_quarter tid (Q : SAny.t → SAny.t → SynDepO) :
      token_half_r tid Q ≡ (token_quarter_r tid Q) ⋅ (token_quarter_r tid Q).
    Proof using.
      unfold token_half_r, token_quarter_r.
      rewrite -auth_frag_op. f_equiv.
      intros x. rewrite discrete_fun_lookup_op. des_ifs.
      rewrite -Some_op -pair_op frac_op Qp.quarter_quarter agree_idemp //.
    Qed.

    Lemma token_quarter_half tid (Q : SAny.t → SAny.t → SynDepO) :
      token_three_quarter_r tid Q ≡ (token_quarter_r tid Q) ⋅ (token_half_r tid Q).
    Proof using.
      unfold token_half_r, token_quarter_r, token_three_quarter_r.
      rewrite -auth_frag_op. f_equiv. intros x. 
      rewrite discrete_fun_lookup_op. des_ifs.
      rewrite -Some_op -pair_op frac_op //.
      replace (1/4+1/2) with (3/4) by compute_done.
      rewrite agree_idemp //.
    Qed.

    Lemma token_half_half tid (Q : SAny.t → SAny.t → SynDepO) :
      token_one_r tid Q ≡ (token_half_r tid Q) ⋅ (token_half_r tid Q).
    Proof using.
      unfold token_one_r, token_half_r.
      rewrite -auth_frag_op. f_equiv. intros x.
      rewrite discrete_fun_lookup_op. des_ifs.
      rewrite -Some_op -pair_op frac_op Qp.half_half agree_idemp //.
    Qed.

    Lemma shot_thread (ths_b ths_w : threadsF) tid (Q : SAny.t → SAny.t → SynDepO)
      (IDLE : ths_b tid = None ∧ ths_w tid = None)
      (VLD : ✓ ths_b ∧ ✓ ths_w)
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
          specialize (H2 x). rewrite discrete_fun_lookup_op in H2. rewrite -H2.
          des_ifs; [|rewrite right_id //]. rewrite Nat.eqb_eq in Heq. subst. des.
          rewrite IDLE. ss.
        + intros x. rewrite discrete_fun_lookup_op. des_ifs; [|rewrite right_id //].
          des. rewrite Nat.eqb_eq in Heq. subst. rewrite IDLE0. ss.
    Qed.

    Lemma make_tid_admin :
      own base_γ SchA.ir_tidRA ⊢ SchA.tid_admin None.
    Proof.
      rewrite /tid_admin. unseal SCH. et.
    Qed.

    Lemma tid_admin_none_user q t :
      tid_admin None ∗ tid_user q t ⊢ False.
    Proof using.
      rewrite /tid_admin /tid_user. unseal SCH.
      iIntros "[A U]". iCombine "A U" gives %wf.
      rewrite /tid_admin_r /tid_user_r /tid_frag_r in wf.
      rewrite -pair_op pair_valid in wf; des; ss.
      specialize (wf t). rewrite discrete_fun_lookup_op in wf.
      rewrite Nat.eqb_refl -Some_op frac_op in wf. exfalso.
      apply (proj1 (Some_valid _)), (proj1 (frac_valid _)) in wf.
      eapply Qp.lt_nge; eauto using Qp.lt_add_l.
    Qed.

    Lemma tid_admin_some_user q t0 t1 :
      tid_admin (Some t0) ∗ tid_user q t1 ⊢ ⌜t0 = t1⌝.
    Proof using.
      rewrite /tid_admin /tid_user. unseal SCH.
      iIntros "[F U]". iCombine "F U" gives %wf.
      rewrite /tid_admin_r /tid_user_r /tid_frag_r in wf.
      rewrite -pair_op pair_valid in wf; des; ss.
      specialize (wf t1). rewrite discrete_fun_lookup_op in wf.
      rewrite Nat.eqb_refl in wf.
      des_ifs.
      - rewrite Nat.eqb_eq in Heq. subst. eauto.
      - rewrite Nat.eqb_neq in Heq. rewrite -Some_op frac_op in wf. exfalso.
        apply (proj1 (Some_valid _)), (proj1 (frac_valid _)) in wf.
        eapply Qp.lt_nge; eauto using Qp.lt_add_l.
    Qed.

    Lemma tid_admin_none_split_r t :
      (tid_admin_r (Some t): tidF) ⋅ (tid_user_r 1 t: tidF) = (tid_admin_r None: tidF).
    Proof using.
      rewrite /tid_admin_r /tid_user_r. extensionalities x.
      rewrite !discrete_fun_lookup_op. des_ifs.
    Qed.

    Lemma tid_frag_update_r ot0 ot1 :
      tid_frag_r 1 ot0 ~~> tid_frag_r 1 ot1.
    Proof using.
      rewrite /tid_frag_r.
      eapply option_update, cmra_update_exclusive; ss.
    Qed.

    Lemma tid_admin_some_user_merge t :
      tid_admin (Some t) ∗ tid_user 1 t ⊢ |==> tid_admin None.
    Proof using.
      iIntros "[A U]".
      iPoseProof (tid_admin_some_user with "[A U]") as "%"; iFrame. des.
      rewrite /tid_admin /tid_user. unseal SCH.
      iCombine "A U" as "AU".
      rewrite tid_admin_none_split_r; eauto.
      iPoseProof (own_update with "AU") as ">AU".
      { instantiate (1:=(tid_admin_r None, _)). eapply prod_update; s; [refl|].
        rewrite left_id. eapply (tid_frag_update_r _ None). }
      iFrame; eauto.
    Qed.

    Lemma tid_admin_none_split t :
      tid_admin None ⊢ |==> tid_admin (Some t) ∗ tid_user 1 t.
    Proof using.
      iIntros "N".
      rewrite /tid_admin /tid_user. unseal SCH.
      rewrite -(tid_admin_none_split_r t); eauto.
      iPoseProof (own_update with "N") as ">N".
      { instantiate (1 := (tid_admin_r (Some t) ⋅ tid_user_r 1 t, _)).
        eapply prod_update; s; [refl|].
        eapply (tid_frag_update_r _ (Some t)). }
      replace (tid_admin_r (Some t) ⋅ tid_user_r 1 t, tid_frag_r 1 (Some t))
        with ((tid_admin_r (Some t), None) ⋅ (tid_user_r 1 t, tid_frag_r 1 (Some t))) by ss.
      iDestruct "N" as "[A U]". iFrame; eauto.
    Qed.

    Lemma tid_admin_none :
      own base_γ SchA.ir_tidRA ⊢ SchA.tid_admin None.
    Proof using.
      rewrite /SchA.tid_admin. unseal SCH. et.
    Qed.
    Lemma tid_admin_some tid :
      own base_γ (SchA.tid_admin_r (Some tid), None) ⊢ SchA.tid_admin (Some tid).
    Proof using.
      rewrite /SchA.tid_admin. unseal SCH. et.
    Qed.
    
    Lemma tid_user_shrink q0 q tid
      (LE: q ≤ q0)
      :
      tid_user q0 tid ⊢ tid_user q tid.
    Proof.
      rewrite /tid_user /tid_user_r /tid_frag_r. unseal SCH.
      eapply own_mono.
      destruct (q0 - q) eqn: E.
      - exists (λ t : nat, if t =? tid then Some q1 else ε, Some (to_frac_agree q1 (Some tid))).
        split; ss.
        + ii. rewrite discrete_fun_lookup_op. des_ifs.
          apply Qp.sub_Some in E. subst. et.
        + rewrite -Some_op /to_frac_agree /to_dfrac_agree. f_equiv.
          rewrite -pair_op agree_idemp. f_equiv.
          rewrite dfrac_op_own. f_equiv.
          eapply Qp.sub_Some; eauto.
      - eapply Qp.sub_None in E. exists (ε, ε). rewrite -pair_op !right_id.
        split; ss.
        + ii. des_ifs. eapply Qp.le_lteq in LE. eapply Qp.le_ngt in E.
          des; subst; ss.
        + repeat f_equiv. eapply Qp.le_lteq in LE. eapply Qp.le_ngt in E.
          des; subst; ss.
    Qed.
    
    Lemma tid_user_merge (q0 q1: Qp) tid
      :
      tid_user q0 tid ∗ tid_user q1 tid ⊢ tid_user (q0+q1) tid.
    Proof.
      rewrite /tid_user /tid_user_r. unseal SCH.
      rewrite -own_op. eapply own_mono. exists (ε, ε). rewrite -!pair_op !right_id.
      split; ss.
      - ii. rewrite discrete_fun_lookup_op. des_ifs.
      - rewrite /tid_frag_r -Some_op /to_frac_agree /to_dfrac_agree.
        f_equiv. rewrite -pair_op agree_idemp //.
    Qed.

    Lemma tid_user_split (q0 q1: Qp) tid
      :
      tid_user (q0+q1) tid ⊢ tid_user q0 tid ∗ tid_user q1 tid.
    Proof.
      rewrite /tid_user /tid_user_r. unseal SCH.
      rewrite -own_op. eapply own_mono. exists (ε, ε). rewrite -!pair_op !right_id.
      split; ss.
      - ii. rewrite discrete_fun_lookup_op. des_ifs.
      - rewrite /tid_frag_r -Some_op /to_frac_agree /to_dfrac_agree.
        f_equiv. rewrite -pair_op agree_idemp //.
    Qed.

    (* need to update the definition [tid_user] *)
    Lemma tid_user_unique (q0 q1: Qp) tid0 tid1
      :
      tid_user q0 tid0 ∗ tid_user q1 tid1 ⊢ ⌜tid0 = tid1⌝.
    Proof.
      rewrite /tid_user /tid_user_r /tid_frag_r. unseal SCH.
      iIntros "[U U0]". iCombine "U U0" gives %wf.
      rewrite -pair_op in wf. destruct wf as [wf0 wf]; ss.
      rewrite -Some_op Some_valid in wf.
      rewrite /to_frac_agree /to_dfrac_agree -pair_op in wf.
      destruct wf as [wf1 wf]; ss.
      rewrite to_agree_op_valid in wf. inv wf. eauto.
    Qed.
    
  End RA. *)

  (* Scheduler specifications *)
  Section SPEC.
    Variable sp_user : spl_type.
    Variable E_full : coPset.

    Definition fspec_spawnable fsp
        (pre : SAny.t → SAny.t → iProp Σ)
        (postS : SAny.t → SAny.t → leibnizO {n & GTerm.t n}) : Prop :=
      fspec_imply fsp
        (fspec_winv E_full
           (fspec_virtual (λ '(mtid, stid),
              ((λ (varg : SAny.t) arg,
                Tid mtid stid ∗ ∃ sarg, ⌜arg = sarg↑⌝ ∗ pre varg sarg)%I,
               (λ (vret : SAny.t) ret,
                Tid mtid stid ∗ ∃ sret, ⌜ret = sret↑⌝ ∗ interp_cond (postS vret sret)))%I))).

    Definition fn_spawnable fn
        (pre : SAny.t -d> SAny.t -d> iProp Σ)
        (postS : SAny.t -d> SAny.t -d> leibnizO {n & GTerm.t n}) : Prop :=
      ∃ meta1 pre1 post1,
        alist_find (Some fn) sp_user = Some (Some (@fspec_call _ meta1 pre1 post1)) ∧
      fspec_spawnable (@fspec_call _ meta1 pre1 post1) pre postS.

    Definition inner_spawn_spec : fspec := 
      fspec_spawn
        (λ '(stid, (pre, postS)) varg arg,
          ∃ (fvarg farg : SAny.t) (fn : string) (mtid : nat),
            ⌜varg = (fn, fvarg)↑ ∧ arg = (fn, farg)↑ ∧ fn_spawnable fn pre postS⌝ ∗
            pre fvarg farg ∗
            JoinFrag (3/4)%Qp mtid postS ∗
            own base_γ (gmap_view_frag mtid (DfracOwn 1) (to_agree stid)))%I
        (λ _ vret _, ∃ (vr : SAny.t), ⌜vret = vr↑⌝ ∗ False)%I.

    Definition spawn_spec : fspec :=
      fspec_virtual (λ '(pre, postS),
        ((λ varg arg,
          ∃ fvarg farg fn,
            ⌜varg = ((fn, fvarg) : string * SAny.t) ∧
             arg = ((fn, farg) : string * SAny.t)↑ ∧
             fn_spawnable fn pre postS⌝ ∗
            pre fvarg farg)%I,
          (λ vret ret,
            ∃ tid, ⌜vret = tid ∧ ret = tid↑⌝ ∗ JoinHandle tid postS)%I)).

    Definition yield_spec : fspec :=
      fspec_winv E_full
        (fspec_simple (λ '(mtid, stid),
          ((λ varg, ⌜varg = tt↑⌝ ∗ Tid mtid stid),
           (λ vret, ⌜vret = tt↑⌝ ∗ Tid mtid stid))))%I.

    Definition join_spec : fspec :=
      fspec_winv E_full
        (fspec_virtual (λ '(mtid, stid, tid, postS),
          ((λ varg arg,
            ⌜arg = tid↑ ∧ varg = tid⌝ ∗ Tid mtid stid ∗ JoinHandle tid postS),
           (λ vret ret, 
            (∃ vsret sret, ⌜vret = (Some vsret) ∧ ret = (Some sret)↑⌝ ∗
            Tid mtid stid ∗ interp_cond (postS vsret sret)))))%I).

    Definition get_tid_spec : fspec :=
      fspec_simple (λ '(mtid, stid),
        ((λ varg, (⌜varg = tt↑⌝ ∗ Tid mtid stid)),
         (λ vret, (⌜vret = mtid↑⌝ ∗ Tid mtid stid))))%I.

    Definition sp : spl_type :=
      Seal.sealing CRIS 
        [(Some SchHdr._spawn,  Some inner_spawn_spec);
         (Some SchHdr.spawn,   Some spawn_spec);
         (Some SchHdr.yield,   Some yield_spec);
         (Some SchHdr.join,    Some join_spec);
         (Some SchHdr.get_tid, Some get_tid_spec)].
  End SPEC.

  Definition scopes := [SCH].

  Definition v_ths := SCH ↯ "ths".
  Definition v_tid := SCH ↯ "tid".

  Definition inner_spawn : string * SAny.t → itree crisE unit :=
    λ '(fn, arg),
      'rv : SAny.t <- ccallN fn arg;; (* call the user function *)
      'ths : thpool <- cgetN v_ths;;
      'tid : nat <- cgetN v_tid;;
      match ths !! tid with
      | Some (stid, _) =>
          let ths2 := <[tid := (stid, Some rv)]> ths in
          cput v_ths ths2;;; (* save the return value *)
          Sch.terminate
      | _ => triggerNB
      end.

  Definition spawn : string * SAny.t → itree crisE nat :=
    λ '(fn, arg),
      'ths : thpool <- cgetN v_ths;;
      let new_tid : nat := length ths in
      new_stid <- trigger (Spawn SchHdr._spawn (fn, arg)↑);;
      cput v_ths (ths ++ [(new_stid, None)]);;;
      Ret (length ths).

  Definition yield : unit → itree crisE unit :=
    λ _,
      (* sanity check *)
      'ths : thpool <- cgetN v_ths;;
      tid <- trigger GetTid;;
      'mtid : nat <- cgetN v_tid;;
      match ths !! mtid with
      | Some (stid, _) => if (decide (stid = tid)) then Ret () else triggerNB
      | None => triggerNB
      end;;;
      '(exist _ (mtid, stid) _) : _ <- trigger (Choose {p : nat * nat | ths.*1 !! p.1 = Some p.2});;
      cput v_tid mtid;;;
      trigger (Yield stid).

  Definition join : nat → itree crisE (option SAny.t) :=
    λ tid,
      (* possibly infinite loop while waiting for the thread to terminate *)
      orv <- (iterC (λ _,
        'ths : thpool <- cgetN v_ths;;
        match ths !! tid with
        | None => Ret (inr None)
        | Some (_, Some rv) => Ret (inr (Some rv))
        | Some (_, None) => '() : _ <- ccallN SchHdr.yield tt;; Ret (inl tt)
        end
      ) tt);;
      Ret orv.

  Definition get_tid : unit → itree crisE nat :=
    λ _, cgetN v_tid.

  (* Definition v_internal := SCH ↯ "internal". *)

  (* Definition check_internal : itree crisE unit :=
    _internal <- cgetU v_internal;;
    assume (_internal = true);;;
    cput v_internal false
  . *)

  (* Definition trigger_Yield (nxt_tid: nat) : itree crisE unit :=
    cput v_internal true;;;
    SchI.trigger_Yield nxt_tid;;;
    check_internal
  . *)

  Definition fnsems sp_user : fnsems_type :=
    [(Some SchHdr._spawn,
      (true, wmask_all, scopes, (Some (inner_spawn_spec sp_user ⊤), (cfunN inner_spawn))));
     (Some SchHdr.spawn,
      (true, wmask_all, scopes, (Some (spawn_spec sp_user ⊤),       (cfunN spawn))));
     (Some SchHdr.yield,
      (true, wmask_all, scopes, (Some (yield_spec ⊤),               (cfunN yield))));
     (Some SchHdr.join,
      (true, wmask_all, scopes, (Some (join_spec ⊤),                (cfunN join))));
     (Some SchHdr.get_tid,
      (true, wmask_all, scopes, (Some (get_tid_spec),           (cfunN get_tid))))].

  Program Definition smod sp_user : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems sp_user;
    SMod.initial_st := SchI.smod.(SMod.initial_st);
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond : iProp Σ := own base_γ ir_newtidRA ∗ own base_γ ir_joinRA.
  (* Definition init_cond : iProp Σ := SchA.init_threads ∗ SchA.init_tid. *)
  
  Definition t sp sp_user := Seal.sealing CRIS (SMod.to_mod sp (smod sp_user)).
End SchA. End SchA.

(* Section FSPEC_SCH.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !schG}.

  Definition fspec_sch q_full (fsp : fspec) : fspec :=
    fspec_call
      (λ '(my_tid, x) varg arg, SchA.tid_user q_full my_tid ∗ precond fsp x varg arg)%I
      (λ '(my_tid, x) vret ret, SchA.tid_user q_full my_tid ∗ postcond fsp x vret ret)%I.

  Definition icond_sch q_full (I: iProp Σ) : iProp Σ :=
    SchA.tid_user q_full 0 ∗ I.
End FSPEC_SCH.

Global Arguments SchA.init_threads : simpl never. *)