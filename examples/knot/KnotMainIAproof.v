Require Import CRIS.

Require Import KnotHeader KnotMainHeader KnotMainI KnotMainA KnotA KnotI KnotIAproof.
Require Import APCHeader APC APCA.

Set Implicit Arguments.

Module KnotMainIA. Section KnotMainIA.
  Import KnotA KnotMainA APCA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !KnotAGΓ Γ, !memGΓ Γ}.
  Notation iProp := (iProp Σ).

  Variable genv: GEnv.t.
  Variable ginv: invspec.
  Variable SpcRec: string → option fspec.
  Variable SpcFun: string → option fspec.
  Variable SpcPure: string → option fspec.
  Variable Spc: string → option fspec.

  Definition Ist: nat -> alist key Any.t -> alist key Any.t -> iProp :=
    λ _ _ _, True%I.

  (* GEnv Hypothesis *)
  Hypothesis GEnvWF: GEnv.wf genv.
  Hypothesis GEnvIncl: incl KnotMainGEnv.t genv.

  (* Spec Hypothesis *)
  Hypothesis MainInFun: spc_incl (MainFunSpc genv SpcRec) SpcFun.
  Hypothesis KnotInSpc: spc_incl KnotRecSpc Spc.
  Hypothesis APCInSpc: spc_incl APCA.Spc Spc.

  (* Pure Hypothesis *)
  Hypothesis RecInSpcPure: spc_sub SpcRec SpcPure.
  Hypothesis PureInGlobal : spc_sub SpcPure Spc.

  Local Notation APCA := (APCA.t ginv SpcPure Spc).
  Local Notation MemA := (MemA.t ginv Spc).
  Local Notation KnotA := (KnotA.t genv ginv SpcRec SpcFun SpcPure Spc).
  Local Notation KnotAMod := (KnotA ★ MemA ★ APCA).
  Local Notation KnotMainA := (KnotMainA.t genv ginv SpcRec SpcPure Spc).
  Local Notation KnotMainI := (KnotMainI.t genv).
  Local Notation KnotMainAMod := (KnotMainA ★ KnotAMod).
  Local Notation KnotMainIMod := (KnotMainI ★ KnotAMod).
  Local Notation IstFull := (IstProd (IstSB KnotMainA.(HMod.scopes) Ist) IstEq).
  
  (*************)

  Lemma simF_fib:
    HSim.sim_fun open KnotMainAMod KnotMainIMod IstFull KnotMainName.fib.
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "[[% INV] %]". des; subst. hss.
    steps_r. inv H3. des. force_r. iSplitR; et.
    force_r; et. des_ifs.
    { (* base case *)
      steps_r. steps_l. forces_l. iSplitR; et.
      inline_l. steps_l.
      iDestruct "ASM" as "%"; des; subst; hss. steps_l.
      unfold apc_body, APC. force_l 0. steps_l. rewrite unfold_APC.
      force_l true. steps_l. forces_l. iSplitR; et. steps_l.
      forces_l. iSplitL "INV"; iFrame; et.
      assert (q1 >= 0)%Z by nia. assert (q1 = 1 \/ q1 = 0) by nia. assert (Z.of_nat (Fib q1) = 1)%Z.
      { des; subst; reflexivity. }
      rewrite H3. step. iSplit; et.
    }
    { (* recursive call *)
      steps_r. steps_l. forces_l. iSplitR; et.
      inline_l. steps_l.
      iDestruct "ASM" as "%"; des; subst; hss. steps_l. unfold apc_body, APC.
      force_l 2. steps_l.
      
      (* first call - rec(n - 1) *)
      rewrite unfold_APC. force_l false. steps_l.
      force_l 1. steps_l. assert (LT: (1 < 2)%ord).
      { apply OrdArith.lt_from_nat. ss. } force_l LT. steps_l.
      inv SPEC. unfold fspec_weaker, mrec_spec in WEAK; ss.
      dup WEAK. specialize (WEAK my_tid (q1 - 1)). des.
      force_l fn. steps_l. force_l (2 * (q1 - 1) + 1)%ord. steps_l.
      assert (PO: is_Some (SpcPure fn) ∧ (2 * (q1 - 1) + 1 < q)%ord).
      { split; et.
        eapply Ord.lt_le_lt; [|et]. rewrite -!OrdArith.mult_from_nat -OrdArith.add_from_nat. apply OrdArith.lt_from_nat. nia. }
      force_l PO. unfold is_Some in PO; des. steps_l. force_l. iSplitR.
      { iPureIntro. apply PureInGlobal. et. }
      steps_l. apply RecInSpcPure in FIND. rewrite PO in FIND. inv FIND.
      force_l x_tgt. force_l ([Vint (q1 - 1)]↑).
      unfold mrec_spec, fspec_apc, precond, postcond in *; ss.
      specialize (PRE (2 * (q1 - 1) + 1)%ord↑ [Vint (q1 - 1)]↑). iPoseProof (PRE with "[INV]") as ">PRE".
      { iFrame. iSplit; et. iSplit; et.
        { iPureIntro. repeat f_equal. nia. }
        { iPureIntro. unfold intrange_64 in *.
          bsimpl; des; split; des_sumbool; repeat destruct Z_le_gt_dec; unfold min_64, max_64, modulus_64_half in *; try nia; ss. }
        { iPureIntro. eexists; esplits; et. refl. } }
      force_l. iSplitL "PRE"; et.
      call "IST"; et. steps_r. steps_l.
      specialize (POST q0 vret). iPoseProof (POST with "[ASM]") as ">POST"; iFrame.
      iDestruct "POST" as "[% INV]". subst; hss. steps_r.

      (* second call - rec(n - 2) *)
      rewrite unfold_APC. force_l false. steps_l.
      force_l 0. steps_l. assert (LT1: (0 < 1)%ord).
      { apply OrdArith.lt_from_nat. ss. } force_l LT1. steps_l.
      unfold fspec_weaker, mrec_spec in WEAK0; ss.
      specialize (WEAK0 my_tid (q1 - 2)). des.
      force_l fn. steps_l. force_l (2 * (q1 - 1))%ord. steps_l.
      assert (PO2: is_Some (SpcPure fn) ∧ (2 * (q1 - 1) < q)%ord).
      { split; et. eapply Ord.lt_le_lt; [|et].
        rewrite -!OrdArith.mult_from_nat. eapply OrdArith.lt_from_nat. nia. }
      force_l PO2. des. steps_l. force_l. iSplitR.
      { iPureIntro. apply PureInGlobal. et. }
      steps_l. force_l x_tgt0. force_l ([Vint (q1 - 2)]↑).
      unfold mrec_spec, fspec_apc, precond, postcond in *; ss.
      specialize (PRE0 (2 * (q1 - 1))%ord↑ [Vint (q1 - 2)]↑). iPoseProof (PRE0 with "[INV]") as ">PRE".
      { iFrame. iSplit; et. iSplit; et.
        { iPureIntro. repeat f_equal. nia. }
        { iPureIntro. unfold intrange_64 in *.
          bsimpl; des; split; des_sumbool; repeat destruct Z_le_gt_dec; unfold min_64, max_64, modulus_64_half in *; try nia; ss. }
        { iPureIntro. eexists; esplits; et. rewrite -!OrdArith.mult_from_nat -OrdArith.add_from_nat. eapply OrdArith.le_from_nat. nia. } }
      force_l. iSplitL "PRE"; et.
      call "IST"; et. steps_r. steps_l.
      specialize (POST0 q3 vret). iPoseProof (POST0 with "[ASM]") as ">POST"; iFrame.
      iDestruct "POST" as "[% INV]". subst; hss. steps_r.

      (* stop APC *)
      rewrite unfold_APC. force_l true. steps_l. forces_l. iSplitR; et.
      steps_l. forces_l. iSplitL "INV"; et. step. iSplit; et.
      iPureIntro. repeat f_equal. rewrite unfold_fib; nia.
    }
    Unshelve. all: ss. exact (0↑).
  Qed.

  Lemma simF_main:
    HSim.sim_fun open KnotMainAMod KnotMainIMod IstFull KnotMainName.main.
  Proof.
    init_simF.

    (* SKINCL *)
    pose proof (@CEnv.incl_incl_env KnotMainGEnv.t genv) as INCLENV.
    unfold KnotMainGEnv.t in GEnvIncl; ss.
    eapply INCLENV in GEnvIncl; et. unfold CEnv.incl_env in GEnvIncl.
    specialize (@GEnvIncl KnotMainName.fib Gfun↑) as SF.
    hexploit SF; [left; ss|intro SKINCL_F].
    des. clear SF INCLENV. inv KnotInSpc.

    (* SKWF *)
    apply CEnv.load_genv_wf in GEnvWF. unfold CEnv.wf in GEnvWF.
    specialize (GEnvWF KnotMainName.fib blk). apply GEnvWF in FIND; et. apply GEnvWF in FIND as FINDF.

    steps_l. destruct q; ss. iDestruct "ASM" as "[[% FG] %]". des; subst. hss.

    steps_r. force_r. iSplitR; et. inline_r. steps_r. force_r Fib. forces_r. iSplitL "FG"; et.
    { iFrame. iSplit; et. iPureIntro. eexists. esplits; et. econs; esplits; et.
      eapply fn_has_spec_weaker.
      { econs; [|refl]. apply MainInFun. unfold MainFunSpc. unseal CRIS. ss. }
      { unfold fspec_weaker, precond, postcond, fun_gen, fib_spec, fun_gen, fib_spec, fspec_apc; ss. 
        ii. exists (x_src, (knot_frag (Some Fib))%I). split; red.
        { i. iIntros "[[% FG] %]". unfold precond, fun_gen, fib_spec; ss.
          des; subst; hss. iModIntro. iSplit; et. iSplit; et; cycle 1.
          iPureIntro. exists fb. esplits; et. inv H5. econs; et. eapply fn_has_spec_weaker; et.
          unfold fspec_weaker, precond, postcond, fun_gen, fib_spec, fun_gen, fib_spec, fspec_apc; ss.
          ii. eexists. split; red.
          { red. instantiate (1:=(_, x_src0)). ss. iIntros; iFrame; et. }
          { i. ss. iIntros; et. } 
        }
        { i. ss. iIntros; et. }
      }
    }
    steps_r. iDestruct "GRT" as "[[% FG] %]"; des; subst; hss. steps_r. inv H3.
    force_r. iSplitR; et. force_l 30%ord. steps_l. inv SPEC. force_l.
    forces_l. iSplitR; et.
    inline_l. steps_l. iDestruct "ASM" as "%"; des; subst; hss. steps_l. unfold apc_body, APC.
    force_l 1. steps_l. rewrite unfold_APC. force_l false. steps_l. force_l 0. steps_l.
    assert (LT: (0 < 1)%ord). { eapply OrdArith.lt_from_nat; et. } force_l LT. steps_l.
    force_l fn. steps_l. force_l 29. steps_l.
    assert (PO: is_Some (SpcPure fn) ∧ (29 < 30)%ord).
    { split; et. eapply OrdArith.lt_from_nat; nia. }
    force_l PO. steps_l. unfold is_Some in PO; des.
    force_l. iSplitR. { iPureIntro. apply PureInGlobal. et. }
    steps_l. apply RecInSpcPure in FIND0. rewrite FIND0 in PO. inv PO.
    unfold fspec_weaker in WEAK. unfold rec_spec, fspec_apc in WEAK.
    specialize (WEAK my_tid (Fib, 10)). unfold precond, postcond in WEAK. des; ss.
    force_l x_tgt. force_l ([Vint 10]↑). specialize (PRE (Ord.from_nat 29)↑ ([Vint 10]↑)); ss.
    iPoseProof (PRE with "[FG]") as ">PRE".
    { iFrame. iSplit; et. iPureIntro. eexists; esplits; ss.
      rewrite -OrdArith.mult_from_nat -OrdArith.add_from_nat. apply OrdArith.le_from_nat; nia. }
    force_l. iSplitL "PRE"; et. call "IST"; et. steps_l. rewrite unfold_APC.
    force_l true. steps_l. steps_r. specialize (POST q vret). iPoseProof (POST with "[ASM]") as ">POST"; iFrame.
    forces_l. iSplitR; et. unfold postcond, rec_spec, fspec_apc; ss. iDestruct "POST" as "[% FG]"; subst; hss.
    steps_r. steps_l. forces_l. steps_l. forces_l. iSplitR; et. step. iSplitR; et.
    Unshelve. all: ss.
  Qed.

  Theorem sim : HSim.t open KnotMainAMod KnotMainIMod KnotMainA.InitCond IstFull.
  Proof.
    init_sim.
    - iIntros "IC". iExists [], [], [], []. do 4 (iSplit; et); iPureIntro; ss.
    - eapply simF_fib; et.
    - eapply simF_main; et.
  Qed.

  Theorem correct :
    ctx_refines
      ((KnotMainA ★ KnotAMod), KnotMainA.InitCond)
      (((KnotMainI.t genv) ★ KnotAMod), emp%I).
  Proof.
    eapply main_adequacy.
    eapply KnotMainIA.sim; et.
  Qed.

End KnotMainIA. End KnotMainIA.
