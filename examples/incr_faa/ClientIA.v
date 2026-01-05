Require Import CRIS.
Require Export ClientI ClientA FaaA SchA MemA.
Require Import SchTactics MemTactics.
From iris Require Import frac_auth numbers.

Require Import Common Mod ltac2_lib.

Program Global Instance fspec_winv_precond
    `{!crisG Γ Σ α β τ _S _I, !concG, !newschG} (fsp : fspec) N stid m arg varg :
  WP (precond (fspec_sch fsp) (N, stid) m arg varg) :=
  {| WP_space := ↑N; WP_remainder := Tid m.1 stid ∗ (precond fsp (N, m.1) m.2 arg varg) |}.
Next Obligation. intros; destruct m; iSplit; iIntros "[$ $]". Qed.

Program Global Instance fspec_winv_postcond
    `{!crisG Γ Σ α β τ _S _I, !concG, !newschG} (fsp : fspec) N stid m arg varg :
  WP (postcond (fspec_sch fsp) (N, stid) m arg varg) :=
  {| WP_space := ↑N; WP_remainder := Tid m.1 stid ∗ (postcond fsp (N, m.1) m.2 arg varg) |}.
Next Obligation. intros; destruct m; iSplit; iIntros "[$ $]". Qed.

Ltac simpl_sp :=
  match goal with
  | H : ?sp1 ⊆ ?sp2 |- context [?sp2 !! ?key] =>
    unshelve erewrite (lookup_weaken sp1 sp2 key _ _ H);
    [|rewrite /sp1; simpl_map; reflexivity|]
  end.

(* Proof of refinement between ClientA.t and ClientI.t *)
Module ClientIA. Section ClientIA.
  Import ClientA.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !memG, !newschG, !incrG}.

  Context (sp_user sp : specmap).
  Context (Hclient : ClientA.sp ⊆ sp_user).
  Context (Hsch : SchA.sp sp_user ⊆ sp).

  Local Definition IstFull := (IstProd (IstSB (ClientA.t sp).(Mod.scopes) IstTrue) IstEq).
  Local Definition MA := (ClientA.t sp ★ MemA.t sp).
  Local Definition MI := ((ClientI.t ★ FaaA.t) ★ MemA.t sp).

  Lemma f_spawnable γ v bofs :
    SchA.fn_spawnable sp_user (IncrHdr.incr)
      (λ N varg arg,
        ⌜varg = arg ∧ varg = ([Vptr bofs]↑↑)⌝
        ∗ counter γ (1/2) v
        ∗ incr_inv 0 N γ bofs)%I
      (λ vret ret,
        existT 0 ((⌜vret = ret ∧ vret = tt↑↑⌝ ∗ counter_syn γ (1/2) (v + 2))%SAT)).
  Proof using Hclient.
    eexists; split.
    { simpl_sp. refl. }
    intros [N ?] mtid; exists (mtid, (bofs, v, γ)); unfold_pre_post; split; i.
    - iIntros "[$ [$ [% [% [[-> ->] [[-> ->] [$ $]]]]]]]". done.
    - iIntros "[$ [$ [[-> ->] ?]]] !>". iExists _, _; iSplitR; eauto.
      SL_red. iSplitR; eauto.
  Qed.

  Ltac sch_yield_ir H1 H2 :=
    iApply (wsim_yield_tgt); [ss|ss|simpl_map; simpl_sp]; iFrame H1; iFrame H2;
      iSplit; [try done|clear_st; iIntros (??) H1;
      let H2' := eval compute in ("[_ " ++ H2 ++ "]")%string in iIntros H2'].

  Lemma incr_simF : ISim.sim_fun open MA MI IstFull (Some IncrHdr.incr).
  Proof using Hsch Hclient.
    iStartSim.

    steps_l. destruct _q as [N stid].
    steps_l. destruct _q as [mtid [[[blk ofs] v]]]; s.
    iDestruct "ASM" as "[TID [[-> ->] [C #INV]]]". hss_l; hss_r.

    steps_l. steps_r. hss_l. hss_r. steps_l. steps_r.
    rewrite /ClientI.incr /ClientA.incr /=; steps_r. steps_l.

    sch_yield_ir "IST" "TID".

    (* tgt inline - faa *)
    steps_r. inline_r. steps_r. hss_r. steps_r.
    sch_yield_ir "IST" "TID".

    rewrite /incr_inv.
    iInv "INV" as "I" "IA". SL_red.
    iDestruct "I" as (x) "PT". SL_red. iDestruct "PT" as "[PT CA]".

    (* operational atomicity here *)
    forces_r; iFrame "PT"; steps_r.

    iMod (counter_incr 1 with "[C CA]") as "[C CA]"; first iFrame.
    iMod ("IA" with "[GRT CA]") as "_".
    { iExists (x + 1)%Z; SL_red; ss; iFrame. }
    sch_yield_ir "IST" "TID".

    rewrite /incr_inv.
    iInv "INV" as "I" "IA". SL_red.
    iDestruct "I" as (y) "PT". SL_red. iDestruct "PT" as "[PT CA]".

    (* operational atomicity here *)
    forces_r; iFrame "PT"; steps_r.

    iMod (counter_incr 1 with "[C CA]") as "[C CA]"; first iFrame.
    iMod ("IA" with "[GRT CA]") as "_".
    { iExists (y + 1)%Z; SL_red; ss; iFrame. }
    sch_yield_ir "IST" "TID".

    steps_r; hss_r; steps_r.
    sch_yield_ir "IST" "TID".
    steps_r.

    sch_yield_l. steps_l. forces_l. iFrame "TID".
    iSplitL "C".
    { iFrame. replace (v + 1 + 1)%Z with (v + 2)%Z by lia. iFrame. eauto. }
    steps_l. step. iFrame. done.
(*SLOW*)Qed.

  Lemma main_simF : ISim.sim_fun open MA MI IstFull None.
  Proof using Hsch Hclient.
    iStartSim.

    steps_l. destruct _q as [N stid]. steps_l. destruct _q as [mtid []]; s.
    iDestruct "ASM" as "[TID ->]".
    rewrite /main /ClientI.main.

    (* src/tgt yield *)
    steps_r. steps_l.
    sch_yield_ir "IST" "TID".

    (* tgt alloc *)
    steps_r.
    iApply wsim_mem_alloc; [ss|ss|].
    iIntros (blk) "[map _]". steps_r; hss_r; steps_r.
    sch_yield_ir "IST" "TID". steps_r.
    sch_yield_ir "IST" "TID". steps_r.

    (* tgt store *)
    iApply (wsim_mem_store with "map"); [ss|].
    iIntros "map". steps_r. hss_r. steps_r.
    sch_yield_ir "IST" "TID". steps_r.
    sch_yield_l. force_l (Vptr (blk, 0%Z)). steps_l. sch_yield_l. steps_l.

    (* spawn *)
    iMod (own_alloc ((●F 0%Z ⋅ ◯F{1} 0%Z))) as "[%γc [A F]]".
    { apply frac_auth_valid; ss. }
    iMod (inv_alloc (ccounter_syn 0 γc (blk, 0%Z)) _ _ _ (N_main N) with "[map A]") as "#I"; eauto.
    { apply nclose_subseteq. }
    { rewrite /ccounter_syn; SL_red; iExists 0; SL_red; iFrame. }
    iPoseProof (counter_op with "[F]") as "[F1 F2]".
    { rewrite -Qp.half_half -{2}(Z.add_0_r 0%Z). iApply "F". }

    iCombine "F1 I" as "F1". iCombine "F2 I" as "F2".

    (* src/tgt spawns *)
    rewrite /Sch.spawn; steps_r; steps_l. simpl_sp.
    force_l (_, _); forces_l; iSplitL "F1".
    { iExists _, _, _; iSplit.
      { iPureIntro; split; [done|split; [done|]]. eapply f_spawnable. }
      ss. iFrame; iSplit; eauto.
    }
    steps_l. call "IST". clear_st. iIntros (ret st_src st_tgt) "IST".
    steps_l. iDestruct "ASM" as "[% [[-> ->] Handle]]". hss_l. steps_l.
    steps_r. hss_r. steps_r.
    sch_yield_ir "IST" "TID".
    sch_yield_l.

    rewrite /Sch.spawn; steps_r; steps_l. simpl_sp.
    force_l (_, _); forces_l; iSplitL "F2".
    { iExists _, _, _; iSplit.
      { iPureIntro; split; [done|split; [done|]]. eapply f_spawnable. }
      ss. iFrame; iSplit; eauto.
    }
    steps_l. call "IST". clear_st. iIntros (ret st_src st_tgt) "IST".
    steps_l. iDestruct "ASM" as "[% [[-> ->] Handle2]]". hss_l. steps_l.
    steps_r. hss_r. steps_r.
    sch_yield_ir "IST" "TID".
    sch_yield_l.

    rewrite /Sch.join; steps_r; steps_l. simpl_sp.
    force_l (_, _); forces_l. iFrame "TID Handle"; iSplit; [eauto|]. steps_l.
    call "IST". clear_st. iIntros (ret st_src st_tgt) "IST".
    steps_l. iDestruct "ASM" as "[TID [% [% [[-> ->] ASM]]]]".
    SL_red. iDestruct "ASM" as "[[-> ->] Q]".
    hss_l. steps_l. steps_r. hss_r. steps_r.
    sch_yield_ir "IST" "TID".
    sch_yield_l.

    rewrite /Sch.join; steps_r; steps_l. simpl_sp.
    force_l (_, _); forces_l. iFrame "TID Handle2"; iSplit; [eauto|]. steps_l.
    call "IST". clear_st. iIntros (ret st_src st_tgt) "IST".
    steps_l. iDestruct "ASM" as "[TID [% [% [[-> ->] ASM]]]]".
    SL_red. iDestruct "ASM" as "[[-> ->] Q2]".
    hss_l. steps_l. steps_r. hss_r. steps_r.
    sch_yield_ir "IST" "TID".

    iInv "I" as "INV" "INVA"; iEval (SL_red) in "INV"; iDestruct "INV" as "[%x INV]".
    iEval (SL_red) in "INV". iDestruct "INV" as "[PT C]".
    iCombine "C Q Q2" as "C" gives %[_ WF%frac_auth_agree]. inv WF; ss.
    iDestruct "C" as "[CA CF]".

    steps_r.
    iApply (wsim_mem_load with "[PT]"); [ss|ss|].
    iIntros "PT". steps_r. hss_r. steps_r.

    iMod ("INVA" with "[CA PT]") as "_".
    { SL_red. iExists _; SL_red; iFrame. }

    sch_yield_ir "IST" "TID". steps_r.
    sch_yield_ir "IST" "TID". 
    sch_yield_l; steps_l.

    step.
    steps_l. steps_r.
    sch_yield_ir "IST" "TID".
    sch_yield_l. steps_l. forces_l. iFrame "TID"; iSplit; eauto.
    step. iFrame. done.
(*SLOW*)Qed.

  Lemma sim : ISim.t open MA MI emp%I IstFull.
  Proof using Hsch Hclient.
    init_sim.
    { eapply incr_simF. }
    { eapply main_simF. }
    { iIntros "_"; iExists _, _, _, _; iSplit; eauto. }
  Qed.
End ClientIA.

Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !memG, !newschG, !incrG}.

  Definition ctxr (sp_user sp : specmap) :
    ClientA.sp ⊆ sp_user →
    (SchA.sp sp_user) ⊆ sp →
    ctx_refines
      (ClientA.t sp ★ MemA.t sp, emp%I)
      (ClientI.t    ★ FaaA.t ★ (MemA.t sp), emp%I).
  Proof using.
    etrans; cycle 1. { do 2 ctxr_rotate. ctxr_refl. }
    eset (GRP := ClientI.t ★ _).
    etrans; cycle 1. { ctxr_rotate. ctxr_refl. }
    do 2 ctxr_rotate.
    eapply main_adequacy, sim; eauto.
  Qed.
End ctxr. End ClientIA.
