Require Import CRIS.
Require Import SchHeader SchI.
From iris Require Export frac_auth dfrac_agree gmap_view.

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

  Definition PYIP (x: nat * nat) : iProp Σ :=
    own base_γ (gmap_view_frag x.1 (DfracOwn 1) (to_agree x.2)).

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

Module SchA. Section SchA.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !newschG}.

  (** initial resource *)
  Definition ir_joinRA : DRA_mk joinRA := 
    (gmap_view_auth (DfracOwn 1) {[0 := (to_agree (λ _ _, existT 0 ⊥))]})%SAT.
  Lemma ir_joinRA_valid : ✓ ir_joinRA.
  Proof. rewrite /ir_joinRA; apply gmap_view_auth_valid. Qed.

  Definition ir_newtidRA : DRA_mk newtidRA := 
    (gmap_view_auth (DfracOwn 1) {[0 := (to_agree 0)]} ⋅
    gmap_view_frag 0 (DfracOwn 1) (to_agree 0))%SAT.
  Lemma ir_newtidRA_valid : ✓ ir_newtidRA.
  Proof.
    rewrite /ir_joinRA /ir_newtidRA.
    apply gmap_view_both_valid; esplits; eauto; ss.
  Qed.

  Definition ir_schΓ : newschΓ := *[Some ir_newtidRA].
  Definition ir_schΣ : newschΣ := *[Some ir_joinRA].

  (* Scheduler specifications *)
  Section SPEC.
    Context (sp_user : specmap).

  Definition fspec_winv (fsp : fspec) : fspec :=
    fspec_mk (meta := meta fsp)
      (λ '(N, stid) x varg arg, winv (↑N, ↑N) ∗ precond fsp (N, stid) x varg arg)%I
      (λ '(N, stid) x vret ret, winv (↑N, ↑N) ∗ postcond fsp (N, stid) x vret ret)%I.

    Definition fspec_spawnable fsp
        (pre : SAny.t → SAny.t → iProp Σ)
        (postS : SAny.t → SAny.t → leibnizO {n & GTerm.t n}) : Prop :=
      fspec_imply fsp
        (fspec_winv
           (fspec_virtual (λ '(mtid, stid),
              ((λ (varg : SAny.t) arg,
                Tid mtid stid ∗ ∃ sarg, ⌜arg = sarg↑⌝ ∗ pre varg sarg)%I,
               (λ (vret : SAny.t) ret,
                Tid mtid stid ∗ ∃ sret, ⌜ret = sret↑⌝ ∗ interp_cond (postS vret sret)))%I))).

    Definition fn_spawnable fn
        (pre : SAny.t -d> SAny.t -d> iProp Σ)
        (postS : SAny.t -d> SAny.t -d> leibnizO {n & GTerm.t n}) : Prop :=
      ∃ fsp, sp_user !! (speckey_fn fn) = Some fsp ∧ fspec_spawnable fsp pre postS.

    Definition inner_spawn_spec : fspec := 
      fspec_mk
        (λ '(N, stid) '(pre, postS) varg arg,
          ∃ (fvarg farg : SAny.t) (fn : string) (mtid : nat),
            ⌜varg = (fn, fvarg)↑ ∧ arg = (fn, farg)↑ ∧ fn_spawnable fn pre postS⌝ ∗
            winv (↑N, ↑N) ∗ TID(stid) ∗ YIELD(stid) ∗
            pre fvarg farg ∗
            JoinFrag (3/4)%Qp mtid postS ∗
            own base_γ (gmap_view_frag mtid (DfracOwn 1) (to_agree stid)))%I
        (λ _ _ vret _, ∃ (vr : SAny.t), ⌜vret = vr↑⌝ ∗ False)%I.

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
      fspec_winv
        (fspec_mk
          (λ '(N, stid) mtid varg arg, ⌜arg = varg ∧ varg = tt↑⌝ ∗ Tid mtid stid)
          (λ '(N, stid) mtid vret ret, ⌜ret = vret ∧ vret = tt↑⌝ ∗ Tid mtid stid))%I.

    Definition join_spec : fspec :=
      fspec_winv
        (fspec_mk
          (λ '(N, stid) '(mtid, tid, postS) varg arg,
            ⌜arg = tid↑ ∧ varg = tid↑⌝ ∗ Tid mtid stid ∗ JoinHandle tid postS)
          (λ '(N, stid) '(mtid, tid, postS) vret ret, 
            (∃ vsret sret, ⌜vret = (Some vsret)↑ ∧ ret = (Some sret)↑⌝ ∗
            Tid mtid stid ∗ interp_cond (postS vsret sret))))%I.

    Definition get_tid_spec : fspec :=
      fspec_mk
        (λ '(_, stid) mtid varg arg, ⌜varg = tt↑ ∧ arg = varg⌝ ∗ Tid mtid stid)%I
        (λ '(_, stid) mtid vret ret, ⌜vret = mtid↑ ∧ ret = vret⌝ ∗ Tid mtid stid)%I.

    Definition sp : specmap :=
      {[speckey_fn SchHdr._spawn := inner_spawn_spec;
        speckey_fn SchHdr.spawn :=  spawn_spec;
        speckey_fn SchHdr.yield :=  yield_spec;
        speckey_fn SchHdr.join :=   join_spec;
        speckey_fn SchHdr.get_tid := get_tid_spec]}.
  End SPEC.

  (* Module definition *)
  Definition scopes : gmultiset string := {[+SCH+]}.

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

  Definition fnsems (sp_user : specmap) : gmap (option string) (option (emask * (option fspec * fbody))) :=
    {[Some SchHdr._spawn :=
        Some (msk_scp scopes msk_true, (Some (inner_spawn_spec sp_user), cfunN inner_spawn));
      Some SchHdr.spawn :=
        Some (msk_scp scopes msk_true, (Some (spawn_spec sp_user), cfunN spawn));
      Some SchHdr.yield :=
        Some (msk_scp scopes msk_true, (Some yield_spec, cfunN yield));
      Some SchHdr.join :=
        Some (msk_scp scopes msk_true, (Some join_spec, cfunN join));
      Some SchHdr.get_tid :=
        Some (msk_scp scopes msk_true, (Some get_tid_spec, cfunN get_tid))]}.

  Program Definition smod sp_user : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems sp_user;
    SMod.initial_st := SchI.smod.(SMod.initial_st);
  |}.
  Solve All Obligations with (i; try done).
  Next Obligation. i; rewrite ?omap_insert /= omap_empty. mod_tac scope_solver. Qed.
  Next Obligation. i. rewrite /SchI.smod /=. mod_tac scope_solver. Qed.

  Definition init_cond : iProp Σ :=
    TidAuth {[0 := 0]} ∗ own base_γ ir_joinRA.

  Definition t sp sp_user := SMod.to_mod sp (smod sp_user).
End SchA. End SchA.

(* Section FSPEC_SCH.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !newschG}.

  Definition fspec_sch E (fsp : fspec) : fspec :=
    fspec_winv E
      (fspec_call
        (λ '(mtid, stid, x) varg arg, Tid mtid stid ∗ precond fsp x varg arg)
        (λ '(mtid, stid, x) vret ret, Tid mtid stid ∗ postcond fsp x vret ret))%I.
End FSPEC_SCH. *)
