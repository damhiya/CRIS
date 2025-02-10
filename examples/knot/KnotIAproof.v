Require Import CRIS.

Require Import KnotHeader KnotI KnotA MemHeader APCHeader APC APCA.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module KnotIA. Section KnotIA.
  Import KnotA APC APCA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !memGΓ Γ, !KnotAGΓ Γ}.
  Notation iProp := (iProp Σ).

  Variable genv: GEnv.t.
  Variable ginv: invspec.
  Variable SpcRec: string -> option fspec.
  Variable SpcFun: string -> option fspec.
  Variable Spc: string -> option fspec.
  Variable SpcMem: string -> option fspec.
  Variable SpcPure: string → option fspec.

  Definition inv : iProp :=
    (∃ (f': optionO (natO -d> natO)) (fb': val),
        (⌜∀ f (EQ: f' ≡ (Some f: optionO (natO -d> natO))),
            ∃ fb,
              (<<BLK: fb' = Vptr fb 0>>) /\
              (<<FN: fb_has_spec genv SpcFun fb (fun_gen genv SpcRec f)>>)⌝)
          ∗ (knot_full f')
          ∗ (var_points_to genv KnotName._f fb'))%I.

  Definition Ist: nat -> alist key Any.t -> alist key Any.t -> iProp :=
    λ _ _ _, inv.

  (* GEnv Hypothesis *)
  Hypothesis GEnvWF: GEnv.wf genv.
  Hypothesis GEnvIncl: incl KnotGEnv.t genv.

  (* SPC Hypothesis *)
  Hypothesis RecInSpc: spc_incl KnotRecSpc SpcRec.
  Hypothesis MemInSpc: spc_incl MemA.Spc Spc.
  Hypothesis APCInSpc: spc_incl APCA.Spc Spc.

  (* Pure SPC Hypothesis *)
  Hypothesis Pures:
    ∀ fn M msr DPQ,
      SpcPure fn = Some (@fspec_apc _ _ msr DPQ)
      → Spc fn = Some (@fspec_apc _ M msr DPQ).
  Hypothesis FunInPure: spc_sub SpcFun SpcPure.
  Hypothesis PureInSpc : spc_sub SpcPure Spc.

  Local Notation APCA := (APCA.t ginv SpcPure Spc).
  Local Notation MemA := (MemA.t ginv SpcMem).
  Local Notation KnotA := (KnotA.t genv ginv SpcRec SpcFun Spc).
  Local Notation KnotAMod := (KnotA ★ MemA ★ APCA).
  Local Notation KnotIMod := ((KnotI.t genv) ★ MemA ★ APCA).
  Local Notation IstFull := (IstProd (IstSB KnotA.(HMod.scopes) Ist) IstEq).
  
  (*************)

  Lemma simF_rec:
    HSim.sim_fun open KnotAMod KnotIMod IstFull KnotName.rec.
  Proof.
    init_simF.

    (* SKINCL - SkEnv id2blk *)
    pose proof (@CEnv.incl_incl_env KnotGEnv.t genv) as INCLENV.
    (* unfold KnotIMod in GEnvIncl; ss. apply (incl_app_inv KnotGEnv _) in GEnvIncl. des. *)
    unfold KnotGEnv.t in GEnvIncl.
    eapply INCLENV in GEnvIncl; et. unfold CEnv.incl_env in GEnvIncl.
    specialize (@GEnvIncl KnotName._f (Gvar 0%Z)↑) as SF.
    specialize (@GEnvIncl KnotName.rec Gfun↑) as SR.
    hexploit SF; [right; right; left; ss|intro SKINCL_F].
    hexploit SR; [right; left; ss|intro SKINCL_REC]. des. clear SF SR INCLENV.

    (* SKWF - SkEnv blk2id *)
    apply CEnv.load_genv_wf in GEnvWF. unfold CEnv.wf in GEnvWF.
    specialize (GEnvWF KnotName.rec blk). apply GEnvWF in FIND; et. apply GEnvWF in FIND as FINDR.

    (* Simulation Start *)
    (* SRC: precondition *)
    steps_l. iDestruct "ASM" as "((%Y & FG) & %Q)"; des; subst; hss. steps_r.
    iDestruct "IST" as (? ? ? ?) "(%ST & [% IST] & %E)"; des; subst.
    iDestruct "IST" as (? ?) "(% & FL & VF)".

    (* RA: Set _f as a funciton pointer whose spec is "_f_spec" *)
    iPoseProof (knot_ra_merge with "FL FG") as "%".
    symmetry in H2. specialize (H1 q1 H2). des; subst.
    rename q1 into _f_spec.
    
    (* TGT: get a block of _f *)
    force_r. iSplitR; et.
    unfold var_points_to. des_ifs.
    (* iDestruct "VF" as "[VF _]". *)

    (* TGT: load the function at the block of _f by inlining "load" *)
    inline_r. steps_r.
    force_r. instantiate (1:=(blk0, 0%Z, (Vptr fb 0), 1%Qp)). force_r.
    force_r. iSplitL "VF"; iFrame; et.
    steps_r. iDestruct "GRT" as "((VF & %) & %)". des; subst. hss.
    steps_r. inv H2. steps_l.

    (* TGT: get blocks of the function pointer and "rec" *)
    dup FN. inv FN. des. force_r. iSplitR; et.
    force_r. iSplitR; et.

    (* SRC: unfold APC *)
    force_l vo. force_l. force_l. iSplitR; et.
    inline_l. unfold apc_spec. steps_l. iDestruct "ASM" as "%"; subst; hss.
    steps_l. unfold apc_body, APC.
    force_l 1. steps_l. rewrite unfold_APC. force_l false. steps_l. force_l 0. steps_l. 
    assert (LT: (0 < 1)%ord). { apply OrdArith.lt_from_nat. nia. }
    force_l LT. steps_l. inv FN0. des. inv SPEC.
    
    unfold fspec_weaker in WEAK; ss. specialize (WEAK my_tid q2). des; ss.
    force_l fn. steps_l. force_l (2 * q2)%ord. steps_l.
    assert (PO: is_Some (SpcPure fn) ∧ (2 * q2 < q)%ord).
    { split; et.
      eapply Ord.lt_le_lt; et. rewrite -OrdArith.mult_from_nat -OrdArith.add_from_nat. apply OrdArith.lt_from_nat. nia. }
    force_l PO. steps_l. unfold is_Some in PO. des. force_l. iSplitR; et.
    apply FunInPure in FIND0. rewrite FIND0 in PO. inv PO.
    steps_l. force_l x_tgt.
    (* precondition *)
    specialize (PRE ((2 * q2)%ord↑) [Vptr blk 0; Vint q2]↑). unfold fun_gen, fspec_apc, precond in PRE; ss. des.
    iPoseProof (PRE with "[FG]") as ">PRE".
    { iFrame. iSplit; et.
      { iPureIntro. eexists; esplits; et. econs; et. econs; [|refl]. apply RecInSpc. unfold KnotRecSpc. unseal CRIS. ss. }
      { iPureIntro. eexists; esplits; et. refl. } }
    forces_l. iSplitL "PRE"; et.
    call "FL VF"; iFrame.
    { iExists _, _, _, _. repeat (iSplit; et). iExists _. iSplit; et.
      { iPureIntro. i. esplits; et. econs; et. inv EQ; et. }
      { unfold var_points_to. rewrite Heq. iFrame. } }
    steps_l.
    (* postcondition *)
    specialize (POST q0 vret).
    iPoseProof (POST with "ASM") as ">POST". unfold postcond, fun_gen, fspec_apc; ss.
    iDestruct "POST" as "[% FG]".
    
    rewrite unfold_APC. force_l true. steps_l. forces_l. iSplitR; et.
    steps_l. steps_r. hss. steps_r. forces_l. iSplitL "FG"; iFrame; et.
    step. iFrame; et.
    Unshelve. all: ss.
  Qed.

  Lemma simF_knot:
    HSim.sim_fun open KnotAMod KnotIMod IstFull KnotName.knot.
  Proof.
    init_simF.

    (* SKINCL *)
    pose proof (@CEnv.incl_incl_env KnotGEnv.t genv) as INCLENV.
    unfold KnotGEnv.t in GEnvIncl. eapply INCLENV in GEnvIncl; et. unfold CEnv.incl_env in GEnvIncl.
    specialize (@GEnvIncl KnotName._f (Gvar 0%Z)↑) as SF.
    specialize (@GEnvIncl KnotName.rec Gfun↑) as SR.
    hexploit SF; [right; right; left; ss|intro SKINCL_F].
    hexploit SR; [right; left; ss|intro SKINCL_REC]. des. clear SF SR INCLENV.

    (* SKWF *)
    apply CEnv.load_genv_wf in GEnvWF. unfold CEnv.wf in GEnvWF.
    specialize (GEnvWF KnotName.rec blk). apply GEnvWF in FIND; et. apply GEnvWF in FIND as FINDR.

    (* SRC: precondition *)
    steps_l. 
    rename q into new_spec.
    iDestruct "ASM" as "((%FB & [%old OLD]) & %Q)". des; subst. hss. steps_r.
    iDestruct "IST" as (? ? ? ?) "(%ST & [% IST] & %E)"; des; subst.
    iDestruct "IST" as (? ?) "(% & FL & VF)".

    (* RA: unify the infomation of f_spec *)
    iPoseProof (knot_ra_merge with "FL OLD") as "%". symmetry in H2.
    assert (REFL: knot_full f' ⊢ knot_full old). { iIntros "F". rewrite /knot_full H2. ss. }
    iPoseProof (REFL with "FL") as "FL".
    unfold var_points_to. des_ifs. ss.
    (* iDestruct "VF" as "[VF _]". *)
    
    (* TGT: save a function by calling "store" *)
    steps_r. inline_r. steps_r.
    force_r. instantiate (1:=(blk0, 0%Z, Vptr fb 0)). force_r. force_r. iSplitL "VF".
    { iSplit; et. }
    steps_r. iDestruct "GRT" as "[[VF %] %]"; des; subst.

    (* RA: update spec *)
    iApply isim_upd. iCombine "FL OLD" as "SPEC".
    iPoseProof (auth_excl_both_update with "SPEC") as ">SPEC".
    iModIntro. iDestruct "SPEC" as "[FL FG]".

    (* finish reasoning *)
    steps_l. force_l. steps_l. force_l. force_l.
    iSplitL "FG"; iFrame; et.
    { iSplit; et. iPureIntro. eexists. esplit; et. econs; et. econs; [|refl].
      apply RecInSpc. unfold KnotRecSpc. unseal CRIS. ss. }
    hss. steps_r. force_r. iSplitR; et.
    steps_r. step. iSplit; et.

    (* check IST *)
    inv FB0. des.
    iExists _, _, _, _. iSplit; et. iSplit; et. iSplit; et. unfold Ist, inv.
    iExists (Some new_spec), _. iSplit; iFrame; et.
    { iPureIntro. ii. eexists. esplits; et. econs; et. inv EQ. et. }
    { unfold var_points_to. des_ifs. }
  Qed.

  Theorem sim : HSim.t open KnotAMod KnotIMod (KnotA.InitCond genv) IstFull.
  Proof.
    init_sim.
    - iIntros "[VF FL]". iExists [], [], _, _. iSplit; et. iSplit; et.
      iSplit; et.
      { iPureIntro. split; ss. }
      { unfold Ist, inv. iExists None, _. iSplit; iFrame; et. iPureIntro. ii. inv EQ. }
    - apply simF_rec; et.
    - apply simF_knot; et.
  Qed.

  Theorem correct :
    ctx_refines
      (KnotA   ★ (MemA.t ginv SpcMem) ★ APCA, KnotA.InitCond genv)
      ((KnotI.t genv) ★ (MemA.t ginv SpcMem) ★ APCA, emp%I).
  Proof.
    eapply main_adequacy.
    eapply KnotIA.sim; et.
  Qed.

End KnotIA. End KnotIA.
