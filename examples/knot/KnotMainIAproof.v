Require Import CRIS.

Require Import KnotHeader KnotMainHeader KnotMainI KnotMainA KnotA KnotI KnotIAproof.
Require Import APCHeader APC APCA APCTactics.

Set Implicit Arguments.

Module KnotMainIA. Section KnotMainIA.
  Import KnotA KnotMainA APCA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !KnotAGΓ Γ, !memGΓ Γ}.
  Notation iProp := (iProp Σ).

  Variable genv: GEnv.t.
  Variable u: univ_id.
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

  Local Notation APCA := (APCA.t u SpcPure Spc).
  Local Notation MemA := (MemA.t u Spc).
  Local Notation KnotA := (KnotA.t genv u SpcRec SpcFun Spc).
  Local Notation KnotAMod := (KnotA ★ MemA ★ APCA).
  Local Notation KnotMainA := (KnotMainA.t genv u SpcRec Spc).
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
      steps_r. steps_l. forces_l. iSplitR; et. steps_l.
      inline_l. steps_l.
      iDestruct "ASM" as "%"; des; subst; hss. steps_l.
      unfold apc_body, APC. force_l 0. steps_l. 
      (* SRC: change to skip *)
      apc_l. steps_l. forces_l. iSplitR; et. steps_l.
      forces_l. iSplitL "INV"; iFrame; et.
      assert (q1 >= 0)%Z by nia. assert (q1 = 1 \/ q1 = 0) by nia. assert (Z.of_nat (Fib q1) = 1)%Z.
      { des; subst; reflexivity. }
      rewrite H3. step. iSplit; et.
    }
    { (* recursive call *)
      steps_r. steps_l. forces_l. iSplitR; et. steps_l.
      inline_l. steps_l.
      iDestruct "ASM" as "%"; des; subst; hss. steps_l. unfold apc_body, APC.
      force_l 2. steps_l.
      
      (* first call - rec(n - 1) *)
      dup SPEC. inv SPEC.
      apc_call_weaker "IST INV"; et.
      { instantiate (1 := 1). apply OrdArith.lt_from_nat. ss. }
      { instantiate (1 := (2 * (q1 - 1) + 1)%ord). eapply Ord.lt_le_lt; [|et]. rewrite -!OrdArith.mult_from_nat -OrdArith.add_from_nat. apply OrdArith.lt_from_nat. nia. }
      { unfold precond. ss. instantiate (1:= (q1 - 1) ). iFrame. iSplit; et. iSplit; et.
        - iPureIntro. repeat f_equal. nia.
        - iPureIntro. unfold intrange_64 in *.
          bsimpl; des; split; des_sumbool; repeat destruct Z_le_gt_dec; unfold min_64, max_64, modulus_64_half in *; try nia; ss.
        - iPureIntro. eexists; esplits; et. refl. 
      }
      iDestruct "ISTPOST" as "[IST [% INV]]". subst. steps_r. hss. steps_r.

      (* second call - rec(n - 2) *)
      apc_call_weaker "IST INV"; et.
      { instantiate (1:=0). apply OrdArith.lt_from_nat. ss. }
      { instantiate (1 := (2 * (q1 - 1))%ord). eapply Ord.lt_le_lt; [|et]. rewrite -!OrdArith.mult_from_nat. eapply OrdArith.lt_from_nat. nia. }
      { iFrame. instantiate (1:= (q1 - 2)). iSplit; et. iSplit; et.
        - iPureIntro. repeat f_equal. nia.
        - iPureIntro. unfold intrange_64 in *.
          bsimpl; des; split; des_sumbool; repeat destruct Z_le_gt_dec; unfold min_64, max_64, modulus_64_half in *; try nia; ss.
        - iPureIntro. eexists; esplits; et. rewrite -!OrdArith.mult_from_nat -OrdArith.add_from_nat. eapply OrdArith.le_from_nat. nia.
      }
      iDestruct "ISTPOST" as "[IST [% INV]]". subst. steps_r. hss. steps_r.

      apc_l. steps_l. forces_l. iSplit; et. steps_l. forces_l. iFrame. iSplit; et.

      step. iSplit; et.
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

    steps_r. force_r. iSplitR; et. steps_r. inline_r. steps_r. force_r Fib. forces_r. iSplitL "FG"; et.
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
    force_r. iSplitR; et. steps_r. unfold pure. steps_l.
    force_l 30%ord. steps_l. inv SPEC. force_l.
    forces_l. iSplitR; et. steps_l.
    inline_l. steps_l. iDestruct "ASM" as "%"; des; subst; hss. steps_l. unfold apc_body, APC.
    force_l 1. steps_l. 
    
    apc_call_weaker "IST FG"; et.
    { instantiate (1:=0). eapply OrdArith.lt_from_nat; et. }
    { instantiate (1:= 29). eapply OrdArith.lt_from_nat; nia. }
    { unfold precond. ss. instantiate (1:=(Fib, 10)). iFrame. iSplit; et. iPureIntro. eexists; esplits; ss.
      rewrite -OrdArith.mult_from_nat -OrdArith.add_from_nat. apply OrdArith.le_from_nat; nia. }
    iDestruct "ISTPOST" as "[IST [% FG]]". subst. steps_r. hss. steps_r.

    apc_l. steps_l. forces_l. iSplit; et. steps_l. force_l. steps_l. forces_l. iSplit; et.
    step. iSplitR; et.
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
