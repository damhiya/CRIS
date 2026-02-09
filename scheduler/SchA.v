Require Import CRIS.
Require Import SchHeader SchI.
From iris Require Export frac_auth dfrac_agree gmap_view.

Definition joinRA `{α : GAT.t} :=
  gmap_viewUR nat (agreeR (SAny.t -d> SAny.t -d> leibnizO {n & GTerm.t n}))%type.
Definition newtidRA := gmap_viewUR nat (agreeR nat).

Class schGpreS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] inG_join :: inG joinRA Σ;
  #[local] inG_tid :: inG newtidRA Γ;
}.
Class schGS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] schGS_schGpreS :: schGpreS;
  join_name : gname;
  tid_name : gname
}.

Definition newschΓ : HRA := #[newtidRA].
Definition newschΣ `{Γ : HRA, α : GAT.t} : GRA := #[joinRA].
Global Instance subG_schGpreS `{!crisG Γ Σ α β τ _S _I} :
  subG newschΓ Γ → subG newschΣ Σ → schGpreS.
Proof using. solve_inG. Defined.

Local Existing Instances schGS_schGpreS inG_join inG_tid.

Section SchRA.
  Context `{!crisG Γ Σ α β τ _S _I, !concGS, !schGS}.

  (* Join-related predicates *)
  Definition JoinFrag dq mtid postS : iProp Σ :=
    own join_name (gmap_view_frag mtid (DfracOwn (dq)%Qp) (to_agree postS) : joinRA).
  Definition JoinHandle mtid postS : iProp Σ :=
    JoinFrag (1/4) mtid postS.
  Definition JoinAuth m : iProp Σ :=
    own join_name (gmap_view_auth (DfracOwn 1) m : joinRA).

  (* Thread-id-related predicates *)
  Definition TidFrag (mtid stid : nat) : iProp Σ :=
    own tid_name (gmap_view_frag mtid (DfracOwn 1) (to_agree stid)).
  Definition Tid (mtid stid : nat) : iProp Σ :=
    own tid_name (gmap_view_frag mtid (DfracOwn 1) (to_agree stid)) ∗
    TID stid ∗ YIELD stid.
  Definition TidAuth (m : gmap nat nat) : iProp Σ :=
    own tid_name (gmap_view_auth (DfracOwn 1) (to_agree <$> m)).

  Definition PYIP (x: nat * nat) : iProp Σ :=
    own tid_name (gmap_view_frag x.1 (DfracOwn 1) (to_agree x.2)).

  Lemma Tid_Auth_Tid (m : gmap nat nat) (mtid stid : nat) :
    TidAuth m ∗ TidFrag mtid stid -∗
    ⌜m !! mtid = Some stid⌝.
  Proof.
    iIntros "[A F]"; iCombine "A" "F" gives %WF%gmap_view_both_dfrac_valid_discrete_total.
    destruct WF as [? [_ [_ [Hlookup [_ Hin]]]]]; rewrite lookup_fmap in Hlookup.
    destruct (m !! mtid) as [stid2|]; ss; inv Hlookup.
    eapply to_agree_included in Hin; inv Hin; done.
  Qed.
End SchRA.

Definition fspec_sch `{!crisG Γ Σ α β τ _S _I, !concGS, !schGS}
    (E : coPset) (fsp : fspec) : fspec :=
  fspec_winv E
    (fspec_mk
      (λ '(stid, mtid, x) varg arg, Tid mtid stid ∗ precond fsp x varg arg)
      (λ '(stid, mtid, x) vret ret, Tid mtid stid ∗ postcond fsp x vret ret))%I.

Module SchA. Section SchA.
  Context `{!crisG Γ Σ α β τ _S _I, !concGS, !schGS}.
  Context (sp_user : specmap).

  Definition fspec_spawnable fsp
      (pre : SAny.t → SAny.t → iProp Σ)
      (postS : SAny.t → SAny.t → leibnizO {n & GTerm.t n}) : iProp Σ :=
    fspec_imply fsp
      (fspec_sch ⊤
        (fspec_mk (meta:=unit)
          (λ _ varg arg,
            ∃ (sarg svarg : SAny.t), ⌜varg = svarg↑ ∧ arg = sarg↑⌝ ∗ pre svarg sarg)
          (λ _ vret ret,
            ∃ (sret svret : SAny.t), ⌜vret = svret↑ ∧ ret = sret↑⌝ ∗
              interp_cond (postS svret sret))))%I.

  Definition fn_spawnable fn
      (pre : SAny.t -d> SAny.t -d> iProp Σ)
      (postS : SAny.t -d> SAny.t -d> leibnizO {n & GTerm.t n}) : iProp Σ :=
    ∃ fsp, ⌜sp_user !! (speckey_fn fn) = Some fsp⌝ ∗ fspec_spawnable fsp pre postS.

  Lemma fspec_sch_spawnable E1 E2 (fsp1 fsp2 : fspec) :
    E1 ⊆ E2 →
    fspec_imply fsp1 fsp2 -∗ fspec_imply (fspec_sch E1 fsp1) (fspec_sch E2 fsp2).
  Proof.
    iIntros "% S %P2 %Q2 [%x2 [-> ->]]"; destruct x2 as [[stid mtid] x2].
    iPoseProof ("S" with "[]") as "[%P1 [%Q1 [[%x1 [-> ->]] S]]]"; first (iPureIntro).
    { exists x2; split; ss. }
    iExists _, _; iSplit; first iPureIntro.
    { exists (stid, mtid, x1); split; ss. }
    iIntros (varg arg) "[W [$ P]]".
    iMod ("S" $! varg arg with "P") as "[$ S]".
    replace E2 with ((E2 ∖ E1) ∪ E1); last (rewrite difference_union_L //; set_solver).
    iPoseProof (winv_split with "W") as "[W $]"; [set_solver|set_solver|].
    iIntros "!> %vret %ret [W2 [$ P]]"; iSplitR "S P"; last by iApply "S".
    iMod (winv_merge with "[-]") as "[$ ?]"; iFrame; auto.
  Qed.

  Definition inner_spawn_spec : fspec := 
    fspec_mk
      (λ (_ : unit) varg arg,
        ∃ stid pre postS (fvarg farg : SAny.t) (fn : string) (mtid : nat),
          ⌜varg = (fn, fvarg)↑ ∧ arg = (fn, farg)↑⌝ ∗
          fn_spawnable fn pre postS ∗
          winv (⊤, ⊤) ∗ Tid mtid stid ∗
          pre fvarg farg ∗
          JoinFrag (3/4)%Qp mtid postS)%I
      (λ _ vret _, ∃ (vr : SAny.t), ⌜vret = vr↑⌝ ∗ False)%I.

  (* TODO : make spawn_spec incremental *)
  Definition spawn_spec : fspec :=
    fspec_mk
      (λ '(pre, postS) varg arg,
        ∃ fvarg farg fn,
          ⌜varg = ((fn, fvarg) : string * SAny.t)↑ ∧ arg = ((fn, farg) : string * SAny.t)↑⌝ ∗
          fn_spawnable fn pre postS ∗ pre fvarg farg)%I
      (λ '(pre, postS) vret ret,
        ∃ tid, ⌜vret = tid↑ ∧ ret = tid↑⌝ ∗ JoinHandle tid postS)%I.

  Definition yield_spec (E : coPset) : fspec :=
    fspec_sch E
      (fspec_mk
        (λ (_ : ()) varg arg, ⌜arg = varg ∧ varg = tt↑⌝)
        (λ _ vret ret, ⌜ret = vret ∧ vret = tt↑⌝))%I.

  Definition join_spec (E : coPset) : fspec :=
    fspec_sch E
      (fspec_mk
        (λ postS varg arg,
          ∃ tid, ⌜arg = tid↑ ∧ varg = tid↑⌝ ∗ JoinHandle tid postS)
        (λ postS vret ret, 
          (∃ vsret sret, ⌜vret = (Some vsret)↑ ∧ ret = (Some sret)↑⌝ ∗
          interp_cond (postS vsret sret))))%I.

  Definition get_tid_spec : fspec :=
    fspec_mk
      (λ '(mtid, stid) varg arg, ⌜varg = tt↑ ∧ arg = varg⌝ ∗ Tid mtid stid)%I
      (λ '(mtid, stid) vret ret, ⌜vret = mtid↑ ∧ ret = vret⌝ ∗ Tid mtid stid)%I.

  Definition sp (E : coPset) : specmap :=
    {[speckey_fn SchHdr._spawn :=  fspec_to_rel inner_spawn_spec;
      speckey_fn SchHdr.spawn :=   fspec_to_rel spawn_spec;
      speckey_fn SchHdr.yield :=   fspec_to_rel (yield_spec E);
      speckey_fn SchHdr.join :=    fspec_to_rel (join_spec E);
      speckey_fn SchHdr.get_tid := fspec_to_rel get_tid_spec]}.

  (* Module definition *)
  Definition scopes : list string := [SCH].

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

  Definition fnsems (E : coPset) : fnsemmap :=
    {[Some SchHdr._spawn :=
        Some (msk_scp scopes msk_true, (fsp_some (inner_spawn_spec), cfunN inner_spawn));
      Some SchHdr.spawn :=
        Some (msk_scp scopes msk_true, (fsp_some (spawn_spec), cfunN spawn));
      Some SchHdr.yield :=
        Some (msk_scp scopes msk_true, (fsp_some (yield_spec E), cfunN yield));
      Some SchHdr.join :=
        Some (msk_scp scopes msk_true, (fsp_some (join_spec E), cfunN join));
      Some SchHdr.get_tid :=
        Some (msk_scp scopes msk_true, (fsp_some get_tid_spec, cfunN get_tid))]}.

  Program Definition smod (E : coPset) : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems E;
    SMod.initial_st := SchI.smod.(SMod.initial_st);
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ :=
    TidAuth {[0 := 0]} ∗
    JoinAuth {[0 := to_agree (λ _ _ : SAny.t, existT 0 emp%SAT)]}.

  (* Scheduler module itself has fixed namespace to ⊤, with specmap namespaces variable *)
  Definition t sp : Mod.t := SMod.to_mod sp (smod ⊤).
End SchA. End SchA.

Lemma sch_alloc `{!crisG Γ Σ α β τ Hsub Hinv, !schGpreS} :
  ⊢ o=> ∃ (_ : schGS), SchA.init_cond ∗ TidFrag 0 0.
Proof.
  iMod (own_alloc
    (gmap_view_auth (DfracOwn 1) {[0 := to_agree 0]} ⋅
      gmap_view_frag 0 (DfracOwn 1) (to_agree 0))) as "[%γt T]".
  { apply gmap_view_both_dfrac_valid_discrete; esplits; ss. split; ss. }
  iMod (own_alloc
    (gmap_view_auth (DfracOwn 1) {[0 := to_agree (λ _ _ : SAny.t, existT 0 emp%SAT)]} : joinRA))
  as "[%γj J]".
  { apply gmap_view_auth_valid. }
  pose (Build_schGS _ _ _ _ _ _ _ _ _ γj γt) as Hsch.
  rewrite own_op; iExists Hsch; iDestruct "T" as "[$ $]"; iFrame.
  done.
Qed.