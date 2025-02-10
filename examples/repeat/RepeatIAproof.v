Require Import CRIS.

Require Import RepeatHeader RepeatI RepeatA.
Require Import APCHeader APC APCA.

Set Implicit Arguments.

Module RepeatIA. Section RepeatIA.
  Import RepeatAS APC APCA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Notation iProp := (iProp Σ).

  Variable genv: GEnv.t.
  Variable ginv: invspec.
  Variable Spc: string → option fspec.
  Variable SpcPure: string → option fspec.
  Variable SpcPureFun: string → option fspec. (* SpcPureFun stores fspecs which repeat use *)

  (* SPC Hypothesis *)
  Hypothesis APCInSpcPure: spc_incl APCA.Spc SpcPure.
  Hypothesis SpcPureInSpc: spc_sub SpcPure Spc.
  Hypothesis SpcPureFunInSpcPure: spc_sub SpcPureFun SpcPure.
  Hypothesis repeatInSpcPure: SpcPure RepeatName.repeat = Some (RepeatAS.repeat_spec SpcPureFun genv). (* to avoid recursive definition of SpcPure *)

  (* Modules *)
  Local Notation APCA := (APCA.t ginv Spc SpcPure).
  Local Notation RepeatI := (RepeatI.t genv).
  Local Notation RepeatA := (RepeatA.t ginv genv Spc SpcPureFun).
  Local Notation RepeatIMod := (RepeatI ★ APCA).
  Local Notation RepeatAMod := (RepeatA ★ APCA).

  (* IST *)
  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp :=
    (λ _ st_src st_tgt, emp%I).
  Local Notation IstFull := (IstProd (IstSB RepeatA.(HMod.scopes) Ist) IstEq).

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

  Lemma simF_repeat : HSim.sim_fun open RepeatAMod RepeatIMod IstFull RepeatName.repeat.
  Proof.
    (* Simulation Start *)
    init_simF.

    (* SRC: handle the precond of repeat *)
    steps_l. rename q2 into f_sem, q3 into n, q4 into x.
    iDestruct "ASM" as "%". hss. dup H3. inv H3. steps_l.

    (* TGT: handle input *)
    steps_r. force_r. steps_r.

    (* case analysis: n *)
    destruct n as [|n'].

    (* CASE: n is 0 *)
    {
      (* TGT: steps tgt *)
      hss. steps_r.

      (* SRC: unfold APC to skip *)
      forces_l. iSplit. { iPureIntro. apply SpcPureInSpc. apply APCInSpcPure. unfold APCA.Spc. unseal CRIS. et. }
      steps_l. forces_l. iSplit; et.
      inline_l. steps_l. iDestruct "ASM" as "%". hss.
      steps_l. unfold APC. force_l. steps_l. rewrite unfold_APC. force_l true. steps_l.
      forces_l. iSplit; et. steps_l. forces_l. iSplit; et.

      (* prove the IST *)
      step. by iSplit.
    }

    (* n is S n' *)
    {
      (* TGT: load fn from function pointer *)
      destruct (Z_lt_le_dec (S n') 1) eqn:E; try lia.
      rewrite H2. hss. steps_r.

      (* SRC: unfold APC for fn *)
      force_l. iSplit. { iPureIntro. apply SpcPureInSpc. apply APCInSpcPure. unfold APCA.Spc. unseal CRIS. et. }
      steps_l. fspec_simpl. forces_l. iSplit; et.
      inline_l. fspec_simpl. steps_l. iDestruct "ASM" as "%". hss.
      steps_l. unfold APC. force_l 2. steps_l. rewrite unfold_APC. force_l false. steps_l. force_l 1. steps_l.
      assert (LT: (1 < 2)%ord). { apply OrdArith.lt_from_nat; lia. }
      force_l LT. steps_l. force_l fn. steps_l. force_l (OrdArith.add Ord.omega (n':nat)%ord). steps_l.
      assert (PO: is_Some (Spc fn) ∧ ((Ord.omega + n') < q)%ord). { split; et. eapply Ord.lt_le_lt; et. apply OrdArith.lt_add_r. apply OrdArith.lt_from_nat. lia. }
      force_l PO. steps_l. force_l. iSplit; et. steps_l. 

      (* SRC: prove the precond of fn *)
      specialize (WEAK my_tid x). des. fspec_simpl fsp1.
      force_l x_tgt. force_l ([Vint x]↑).
      iPoseProof ((PRE (OrdArith.add Ord.omega (n':nat)%ord)↑ [Vint x]↑) with "[]") as ">PRE".
      { iSplit; et. iExists (OrdArith.add Ord.omega (n':nat)%ord). iSplit; et. iPureIntro. apply OrdArith.add_base_l. }
      force_l. iSplitR "IST"; et.

      (* make a call to fn *)
      call "IST"; et.

      (* SRC: handle the postcond of fn *)
      steps_l.
      iPoseProof ((POST q0 vret) with "ASM") as ">%". hss.

      (* TGT: steps tgt *)
      steps_r. hss. steps_r.

      (* SRC: unfold APC for repeat *)
      rewrite unfold_APC. force_l false. steps_l. force_l 0. steps_l. 
      assert (LT': (0 < 1)%ord). { apply OrdArith.lt_from_nat; lia. }
      force_l LT'. steps_l. force_l RepeatName.repeat. steps_l. force_l (OrdArith.add Ord.omega (n':nat)%ord). steps_l.
      assert (PO': is_Some (Spc RepeatName.repeat) ∧ ((Ord.omega + n') < q)%ord); et.
      force_l PO'. steps_l. force_l. iSplit; et. steps_l.

      (* SRC: prove the precond of repeat *)
      pose proof (fn_has_spec_trivial _ _ repeatInSpcPure) as Hrepeat_has_spec. inv Hrepeat_has_spec.
      specialize (WEAK my_tid (n', (f_sem x), f_sem)). des.
      force_l x_tgt0. force_l ([Vptr fptr 0; Vint n'; Vint (f_sem x)] ↑).
      iPoseProof ((PRE0 (OrdArith.add Ord.omega (n':nat)%ord)↑ [Vptr fptr 0; Vint n'; Vint (f_sem x)]↑) with "[]") as ">PRE".
      { iPureIntro. split.
        - exists fn, fptr. hrepeat split; et. unfold_intrange_64; des_ifs_safe; hrepeat destruct Z_le_gt_dec; ss; try lia.
        - exists (Ord.omega + n')%ord. split; et. apply Ord.le_refl. }
      force_l. iSplitL "PRE"; et.

      (* make a call to repeat *)
      assert (S n' - 1 = n')%Z as -> by lia.
      call "IST"; et.

      (* SRC: handle the postcond of repeat *)
      steps_l. iMod ((POST0 q1 vret) with "ASM") as "%". hss.
      steps_r. hss. steps_r.

      (* SRC: unfold APC to skip *)
      rewrite unfold_APC. force_l true. steps_l.
      forces_l. iSplit; et. steps_l. forces_l. iSplit; et.

      (* prove the IST *)
      step. by iSplit.
    }
    Unshelve. all: et. exact (0↑).
  Qed.

  Theorem sim : HSim.t open RepeatAMod RepeatIMod RepeatA.InitCond IstFull.
  Proof.
    init_sim.
    - iIntros "_". repeat iExists [].
      repeat (iSplit; eauto); iPureIntro; ss.
    - apply simF_repeat; eauto.
  Qed.

  Theorem correct :
    ctx_refines
      (RepeatA  ★  APCA, RepeatA.InitCond)
      ((RepeatI.t genv) ★  APCA, emp%I).
  Proof.
    eapply main_adequacy.
    eapply RepeatIA.sim; et.
  Qed.
End RepeatIA. End RepeatIA.