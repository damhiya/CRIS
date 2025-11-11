Require Import CRIS.
Require Import SchHeader SchA SchTactics.
Require Import ImpPrelude MemHeader MemA MemTactics.
Require Import IncrementHeader IncrementI IncrementA.

Module IncrementIA. Section IncrementIA.
  Context `{!crisG Γ Σ α β τ _S _I, !memG, !concG, !newschG}.

  Local Definition IstFull := (IstProd (IstSB IncrementA.t.(Mod.scopes) IstTrue) IstEq).
  Local Definition MA := (IncrementA.t ★ (MemA.t sp_none)).
  Local Definition MI := (IncrementI.t ★ (MemA.t sp_none)).

  Lemma increment_simF : ISim.sim_fun open MA MI True%I IstFull (Some IncrementHdr.increment).
  Proof.
    init_simF.
    steps_l. destruct _q; ss. destruct _q; ss. destruct v; ss. inv G0. hss.
    destruct _q0 as [blk ofs].

    steps_r.
    sch_yield_rr.
    steps_r. sch_yield_rr.
    sch_yield_l.
    norm_l. norm_r.

    iApply wsim_reset.
    iStopProof. revert st_src. combine_quant st_tgt.
    eapply wsim_coind.
    iIntros (g' _ CIH [st_t st_s]) "%GG' /=".
    destruct_quant CIH.

    unfold_iterC_l. unfold_iterC_r.
    steps_l. steps_r.
    sch_yield_rr.
    Unshelve. all: try exact 0.

    sch_yield_l. steps_l. rename _q into v.

    steps_r. inline_r. force_r (blk, ofs, 1%Qp, Vint v). steps_r.
    forces_r. iFrame "ASM". iSplit; eauto.
    steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss_r. steps_r.

    force_l false. steps_l. force_l; iFrame "PT". steps_l. sch_yield_l. steps_l.
    unfold_iterC_l. steps_l.

    sch_yield_rr. steps_r.
    sch_yield_rr. steps_r.

    sch_yield_l. steps_l. rename _q into v'.
    iApply (wsim_mem_cas _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ emp%I with "ASM");
        [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs|..]; eauto.
    { des_ifs. }
    { iIntros "_"; iExists _, _, _, _; ss. }
    iIntros "H _".
    Unshelve. all: try exact 0; try exact 1%Qp; try exact (Vint 0).

    steps_r. hss_r. steps_r.
    destruct (dec v' v) as [?|Heq]; [subst; ss|ss].
    { force_l true. steps_l. force_l; iFrame "H"; steps_l.
      sch_yield_rr. steps_r.
      sch_yield_rr; steps_r.
      case_decide; [|ss].
      steps_r.
      sch_yield_l. steps_l. step. iSplit; done.
    }
    { force_l false.
      forces_l. iFrame "H". steps_l.
      sch_yield_rr; steps_r.
      sch_yield_rr; steps_r.
      case_decide; first clarify.
      steps_r.
      sch_yield_l. steps_l.
      iApply wsim_progress. iApply wsim_base.
      iIntros "?". iApply (CIH). iFrame.
    }
    Unshelve. all: eauto.
  (*SLOW*)Qed.
End IncrementIA. End IncrementIA.
