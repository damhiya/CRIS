Require Import CRIS.

Require Import Imp.
Require Import AddHeader AddI AddA.
Require Import RepeatHeader RepeatA.
Require Import APCHeader APC APCA.

Set Implicit Arguments.

Module AddIA. Section AddIA.
  Import AddAS APC APCA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Notation iProp := (iProp Σ).

  Variable genv: GEnv.t.
  Variable ginv: invspec.
  Variable Spc: string → option fspec.
  Variable SpcPure: string -> option fspec.
  Variable SpcPureFun: string -> option fspec.

  (* GEnv Hypothesis *)
  Hypothesis GEnvWF: GEnv.wf genv.
  Hypothesis GEnvIncl: incl AddGEnv.t genv.

  (* SPC Hypothesis *)
  Hypothesis APCInSpcPure: spc_incl APCA.Spc SpcPure.
  Hypothesis SpcPureInSpc: spc_sub SpcPure Spc.
  Hypothesis repeatInSpcPure: SpcPure RepeatName.repeat = Some (RepeatAS.repeat_spec SpcPureFun genv).
  Hypothesis succInSpcPureFun: SpcPureFun AddName.succ = Some AddAS.succ_spec.

  (* Modules *)
  Local Notation APCA := (APCA.t ginv SpcPure Spc).
  Local Notation RepeatA := (RepeatA.t ginv genv Spc SpcPureFun).
  Local Notation RepeatAMod := (RepeatA ★ APCA).
  Local Notation AddI := (AddI.t genv).
  Local Notation AddA := (AddA.t ginv Spc).
  Local Notation AddIMod := (AddI ★ RepeatAMod).
  Local Notation AddAMod := (AddA ★ RepeatAMod).

  (* IST *)
  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp :=
    (λ _ st_src st_tgt, emp%I).
  Local Notation IstFull := (IstProd (IstSB AddA.(HMod.scopes) Ist) IstEq).

  (* tactic to simplify meta/precond/postcond for fspecs *)
  Ltac _fspec_simpl_core := unfold SMod2HMod.meta, SMod2HMod.precond, SMod2HMod.postcond in *; simpl in *.
  Tactic Notation "fspec_simpl" := _fspec_simpl_core.
  Tactic Notation "fspec_simpl" constr(p) := try (depdes p); _fspec_simpl_core.

  (* auxiliary fn_has_spec-related lemma *)
  Lemma fn_has_spec_trivial :
    ∀ Spc fn fsp,
        Spc fn = Some fsp → fn_has_spec Spc fn fsp.
  Proof.
    ii. do 2 (econs; et). by split; r; iIntros; iModIntro.
  Qed.

  (* helper lemma for simF_add proof *)
  Lemma _add_succ_repeat_fun:
    ∀ n m, add_fun (Z.of_nat n) m = RepeatAS.repeat_fun succ_fun n m.
  Proof.
    rewrite /add_fun /succ_fun.
    induction n; ii; ss.
    assert ((S n + m)%Z = (n + (m + 1)))%Z as -> by lia. ss.
  Qed.

  Lemma add_succ_repeat_fun:
    ∀ n m, (0 ≤ n)%Z → add_fun n m = RepeatAS.repeat_fun succ_fun (Z.to_nat n) m.
  Proof.
    ii. rewrite -{1}(Z2Nat.id n); et.
    apply (_add_succ_repeat_fun (Z.to_nat n) m).
  Qed.

  Lemma simF_succ : HSim.sim_fun open AddAMod AddIMod IstFull AddName.succ.
  Proof.
    (* Simulation Start *)
    init_simF.

    (* SRC: handle the precond of succ *)
    steps_l. rename q into n.
    iDestruct "ASM" as "%". hss. steps_l.

    (* TGT: steps tgt *)
    steps_r.

    (* SRC: unfold APC to skip *)
    force_l. iSplit. { iPureIntro. apply SpcPureInSpc. apply APCInSpcPure. unfold APCA.Spc. unseal CRIS. et. }
    steps_l. forces_l. iSplit; et.
    inline_l. steps_l. iDestruct "ASM" as "%". hss.
    steps_l. unfold APC. force_l. steps_l. rewrite unfold_APC. force_l true. steps_l.
    forces_l. iSplit; et. steps_l. forces_l. iSplit; et.

    (* prove the IST *)
    step. by iSplit.
    Unshelve. et. exact (0↑).
  Qed.

  Lemma simF_add : HSim.sim_fun open AddAMod AddIMod IstFull AddName.add.
  Proof.
    (* succ is in somewhere at CEnv *)
    pose proof (@CEnv.incl_incl_env AddGEnv.t genv) as INCLENV.
    eapply INCLENV in GEnvIncl; et.
    pose proof (@GEnvIncl AddName.succ Gfun↑) as SS.
    hexploit SS; [left; ss|intros]. des. clear SS INCLENV.
    apply CEnv.load_genv_wf in GEnvWF.
    pose proof (GEnvWF AddName.succ blk) as GEnvWF. apply GEnvWF in FIND as FIND'.

    (* Simulation Start *)
    init_simF.

    (* SRC: handle the precond of add *)
    steps_l. rename q1 into n, q2 into m.
    iDestruct "ASM" as "%". hss. steps_l.

    (* TGT: handle input *)
    steps_r. rewrite FIND. hss. steps_r.

    (* SRC: unfold APC for repeat *)
    force_l. iSplit. { iPureIntro. apply SpcPureInSpc. apply APCInSpcPure. unfold APCA.Spc. unseal CRIS. et. }
    steps_l. forces_l. iSplit; et.
    inline_l. steps_l. iDestruct "ASM" as "%". hss.
    steps_l. unfold APC. force_l 1. steps_l. rewrite unfold_APC. force_l false. steps_l. force_l 0. steps_l.
    assert (LT: (0 < 1)%ord). { apply OrdArith.lt_from_nat; lia. }
    force_l LT. steps_l. force_l RepeatName.repeat. steps_l. force_l (Ord.omega + (Z.to_nat n))%ord. steps_l.
    assert (PO: is_Some (SpcPure RepeatName.repeat) ∧ ((Ord.omega + (Z.to_nat n)) < q)%ord). { split; et. eapply Ord.lt_le_lt; et. apply OrdArith.lt_add_r. apply OrdArith.lt_from_nat. lia. }
    force_l PO. steps_l. force_l. iSplit; et. steps_l.

    (* SRC: prove the precond of repeat *)
    pose proof (fn_has_spec_trivial SpcPure _ repeatInSpcPure) as Hrepeat_has_spec. inv Hrepeat_has_spec.
    specialize (WEAK my_tid (Z.to_nat n, m, succ_fun)). des.
    force_l x_tgt. force_l ([Vptr blk 0; Vint n; Vint m] ↑).
    iPoseProof ((PRE (Ord.omega + Z.to_nat n)%ord↑ [Vptr blk 0; Vint n; Vint m]↑) with "[]") as ">PRE".
    { iPureIntro. split.
      - exists AddName.succ, blk. rewrite Z2Nat.id; et. hrepeat split; et. unfold_intrange_64; des_ifs_safe; hrepeat destruct Z_le_gt_dec; ss; try lia.
        (* succ has sufficient spec *)
        econs; et. unfold succ_spec, fspec_weaker. fspec_simpl.
        ii. exists x_src. split; r; ii; iIntros; iModIntro; hss.
        iPureIntro. split; ss. exists vo. split; et. eapply Ord.le_trans; et. apply Ord.lt_le. apply Ord.omega_upperbound.
      - exists (Ord.omega + (Z.to_nat n))%ord. split; et. apply Ord.le_refl. }
    force_l. iSplitL "PRE"; et.

    (* make a call to repeat *)
    call "IST"; et.

    (* SRC: handle the postcond of repeat *)
    steps_l. iMod ((POST q0 vret) with "ASM") as "%". hss.
    steps_r. hss. steps_r.

    (* SRC: unfold APC to skip *)
    rewrite unfold_APC. force_l true. steps_l. 
    force_l. force_l. iSplit; et. steps_l. forces_l. iSplit; et.

    (* prove the IST *)
    step. iSplit; et. 
    iPureIntro. do 2 f_equal.
    apply add_succ_repeat_fun; et.
    Unshelve. et.
  Qed.

  Theorem sim : HSim.t open AddAMod AddIMod AddA.InitCond IstFull.
  Proof.
    init_sim.
    - iIntros "_". repeat iExists []. iSplit; eauto.
      repeat (iSplit; eauto); iPureIntro; prove_scope.
    - apply simF_succ; et.
    - apply simF_add; et.
  Qed.

  Theorem correct :
    ctx_refines
      (AddA ★  RepeatA ★  APCA, AddA.InitCond)
      (AddI ★  RepeatA ★  APCA, emp%I).
  Proof.
    eapply main_adequacy.
    apply sim.
  Qed.
End AddIA. End AddIA.