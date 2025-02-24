Require Import CRIS.

Require Import RepeatHeader RepeatI RepeatA.
Require Import APCHeader APC APCA APCTactics.

Set Implicit Arguments.

Module RepeatIA. Section RepeatIA.
  Import RepeatAS APC APCA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Notation iProp := (iProp Σ).

  Variable genv: GEnv.t.
  Variable Spc: string → option fspec.
  Variable SpcPure: string → option fspec.
  Variable SpcPureFun: string → option fspec. (* SpcPureFun stores fspecs which repeat use *)

  (* SPC Hypothesis *)
  Hypothesis APCInSpcPure: spc_incl APCA.Spc SpcPure.
  Hypothesis SpcPureInSpc: spc_sub SpcPure Spc.
  Hypothesis SpcPureFunInSpcPure: spc_sub SpcPureFun SpcPure.
  Hypothesis repeatInSpcPure: SpcPure RepeatName.repeat = Some (RepeatAS.repeat_spec SpcPureFun genv). (* to avoid recursive definition of SpcPure *)

  (* Modules *)
  Local Notation APCA := (APCA.t SpcPure Spc).
  Local Notation RepeatI := (RepeatI.t genv).
  Local Notation RepeatA := (RepeatA.t genv Spc SpcPureFun).
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
  (* Lemma fn_has_spec_trivial :
    ∀ Spc fn fsp,
        Spc fn = Some fsp → fn_has_spec Spc fn fsp.
  Proof.
    ii. do 2 (econs; et). by split; r; iIntros; iModIntro.
  Qed. *)

  Lemma simF_repeat : HSim.sim_fun open RepeatAMod RepeatIMod IstFull RepeatName.repeat.
  Proof.
    (* Simulation Start *)
    init_simF.

    (* SRC: handle the precond of repeat *)
    steps_l. rename q2 into f_sem, q3 into n, q4 into x.
    iDestruct "ASM" as "%". hss. dup H3. inv H3. steps_l.

    (* TGT: handle input *)
    steps_r. unfold assume. force_r. steps_r.

    (* case analysis: n *)
    destruct n as [|n'].

    (* CASE: n is 0 *)
    {
      (* TGT: steps tgt *)
      hss. steps_r.

      (* SRC: unfold APC *)
      forces_l. iSplit. { iPureIntro. apply SpcPureInSpc. apply APCInSpcPure. unfold APCA.Spc. unseal CRIS. et. }
      steps_l. forces_l. iSplit; et. inline_l. steps_l. iDestruct "ASM" as "%". hss.
      steps_l. unfold APC. force_l. steps_l.

      (* SRC: change to skip *)
      apc_l. steps_l. forces_l. iSplit; et. steps_l. forces_l. iSplit; et.

      (* prove the IST *)
      step. by iSplit.
    }

    (* CASE: n is S n' *)
    {
      (* TGT: load fn from function pointer *)
      destruct (Z_lt_le_dec (S n') 1) eqn:E; try lia.
      rewrite H2. hss. steps_r.

      (* SRC: unfold APC *)
      force_l. iSplit. { iPureIntro. apply SpcPureInSpc. apply APCInSpcPure. unfold APCA.Spc. unseal CRIS. et. }
      steps_l. fspec_simpl. forces_l. iSplit; et. steps_l.
      inline_l. fspec_simpl. steps_l. iDestruct "ASM" as "%". hss.
      steps_l. unfold APC. force_l 2. steps_l.

      (* call apc with fn *)
      apc_call_weaker "IST"; et.
      { instantiate (1:= 1%ord). apply OrdArith.lt_from_nat. lia. }
      { eapply Ord.lt_le_lt; et. apply OrdArith.lt_add_r. instantiate (1:=n'). apply OrdArith.lt_from_nat. lia. }
      { unfold precond. ss. do 2 (iSplit; et). iExists (Ord.omega + n')%ord. iSplit; et. iPureIntro. apply OrdArith.add_base_l. }
      iDestruct "ISTPOST" as "[IST %]". unfold postcond. subst.

      (* TGT: steps tgt *)
      steps_r. hss. steps_r. assert (S n' - 1 = n')%Z as -> by lia.

      (* call apc with repeat *)
      apc_call "IST"; et.
      { instantiate (1 := 0%ord). apply OrdArith.lt_from_nat; lia. }
      { eapply Ord.lt_le_lt; et. apply OrdArith.lt_add_r. instantiate (1:= n'). apply OrdArith.lt_from_nat; lia. }
      { unfold precond. ss. iFrame. instantiate (1:= (n', (f_sem x), f_sem)). iPureIntro. split.
        - exists fn, fptr. hrepeat split; et. unfold_intrange_64; des_ifs_safe; hrepeat destruct Z_le_gt_dec; ss; try lia.
        - exists (Ord.omega + n')%ord. split; et. apply Ord.le_refl. }
      unfold postcond. ss.
      iDestruct "ISTPOST" as "[IST %]". subst.

      (* TGT: steps tgt *)
      steps_r. hss. steps_r.

      (* SRC: change to skip *)
      apc_l. steps_l. forces_l. iSplit; et. steps_l. forces_l. iSplit; et.

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
