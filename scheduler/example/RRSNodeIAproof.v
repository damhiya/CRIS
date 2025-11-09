Require Import CRIS.
Require Import SchHeader SchA SchTactics.
Require Import RRSHeader RRSA.
Require Import MemHeader MemA.
Require Import RRSNodeHeader RRSNodeI RRSNodeA RRSTactics.
Require Import ltac2_lib.

Module RRSNodeIA. Section RRSNodeIA.
  Import RRSNodeAS.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG}.
  Context `{_schG: !SchA.newschG}.
  Context `{_rrsG: !RRSA.rrsG}.
  Context `{_memG: !MemA.memG}.
  Context `{_nodeG: !RRSNodeA.nodeG}.

  Context (E: coPset) (Hsub : ↑N_node ⊆ E).
  Context (sp: sp_type).
  Context (sp_sch_user sp_user: spl_type).
  Context (Hschglob: sp_incl sp_sch_user sp).
  Context (Hschrrs: spl_sub sp_user sp_sch_user).
  Context (Hsch: sp_incl (SchA.sp sp_sch_user E) sp).
  Context (Hrrs: spl_sub (RRSAS.sp sp_user E snd SchA.PYIP) sp_sch_user).
  Context (Hnode: spl_sub (RRSNodeAS.sp E) sp_user).

  Local Definition IstFull := (IstProd (IstSB (RRSNodeA.t E sp).(Mod.scopes) IstTrue) IstEq).
  Local Definition init_cond := RRSNodeA.init_cond.
  Local Definition MA := (RRSNodeA.t E sp ★ (MemA.t sp) ★ (RRSA.t SchHdr.yield sp sp_user snd SchA.PYIP)).
  Local Definition MI := (RRSNodeI.t ★ (MemA.t sp) ★ (RRSA.t SchHdr.yield sp sp_user snd SchA.PYIP)).

  Lemma f_spawnable n b Invs
    (RNG: 0 < n < size Invs)
    (INV: forall m, m < size Invs -> Invs !! m = Some (existT 0 (x_value_tid m))) :
    RRSAS.fn_spawnable_rr sp_user E RRSNodeHdr.f n (f_precond (b, 0%Z)) Invs.
  Proof using Hnode.
    econs; econs.
    { eapply Hnode. rewrite /RRSNodeAS.sp. unseal CRIS. ss. }
    { rr; ss. i; hss. destruct x1 as [[mtid stid] ssch]. eexists (existT n _).
      Unshelve.
      2:{ ss. destruct n; try nia. ss. exact (mtid, stid, ssch, (b, 0%Z), Invs). }
      destruct n; try nia.
      esplits.
      { iIntros (??) "[WI (% & -> & (tidF & RRIP & ((% & % & RRI & % & INV) & % & % & FPRE)))]"; hss.
        iPoseProof (RRSAS.rrinv_prev_subset with "[RRIP RRI]") as "%SUB"; iFrame.
        hexploit (INV (pred_rr (S n) (size Invs'))).
        { eapply map_subseteq_size in SUB as SZ.
          erewrite <-(pred_rr_subst (S n) (size Invs) (size Invs')); eauto.
          eapply pred_rr_upperbound; eauto. }
        intros INVS.
        hexploit (INV (S n)); try nia. intros INVS0.
        eapply lookup_weaken in SUB as SUB0; try eapply INVS; eauto.
        eapply lookup_weaken in SUB as SUB1; try eapply INVS0; eauto.
        rewrite SUB0 in H0. inv H0.
        iFrame; eauto. }
      { iIntros (??). iIntros "[WI (% & tidF & % & % & % & POST)]"; hss.
        iFrame; eauto. }
    }
  Qed.

  Lemma simF_main : ISim.sim_fun open MA MI init_cond IstFull (Some RRSNodeHdr.f_main).
  Proof using Hsub Hschglob Hschrrs Hsch Hrrs Hnode.
    init_simF.

    steps_l.
    rename _q1 into stid, _q2 into ssch.
    iDestruct "ASM" as "((-> & tidF & RRI & F) & ->)"; hss.

    (** alloc **)
    steps_r. inline_r. steps_r.
    forces_r. iSplit; eauto; ss.
    { instantiate (1:=[Vint 1]↑). instantiate (1:=1). iPureIntro; esplits; eauto; ss. }
    ss. steps_r. iDestruct "GRT" as "[[% (-> & PT & _)] %]".
    replace (0 + 0%nat)%Z with 0%Z by nia.
    steps_r; hss_r. steps_r.
    steps_l.

    assert (rrs_in_sp : sp_incl (RRSAS.sp sp_user E snd PYIP) sp).
    { rewrite /RRSAS.sp. unseal CRIS. econs; [prove_nodup|].
      i. eapply Hschglob. eapply Hrrs. rewrite /RRSAS.sp. unseal CRIS. eauto. }

    rrs_yield_ir.

    (** store **)
    steps_r. inline_r. steps_r. forces_r. iSplitL "PT"; eauto; ss.
    { instantiate (2 := (b, 0%Z, Vundef, Vint 0)); ss. iFrame; eauto. }
    ss. steps_r. iDestruct "GRT" as "[[PT ->] %]".
    steps_r; hss_r. steps_r.

    rrs_yield_ir. rrs_yield_l. steps_l.

    (** invariant *)
    iPoseProof (full_merge with "F") as "[H H0]".
    iMod (inv_alloc (ex_x_points_to (b, 0%Z)) with "[PT H0]") as "#I"; eauto.
    { SL_red. iExists (Vint 0). SL_red; iFrame. rewrite /half_val. unseal "Node". iFrame. }

    (** 1st spawn **)
    force_l (0, stid, ssch, RRSNodeAS.f_precond (b, 0%Z), {[0 := existT 0 (x_value_tid 0)]}, existT 0 (x_value_tid 1)).
    steps_l. forces_l; ss. iSplitL "RRI TID".
    { iExists _. iFrame. iFrame "I". iSplit; eauto.
      do 3 iExists _. iSplit; eauto.
      iPureIntro. esplits; eauto.
      eapply f_spawnable.
      { split.
        { vm_compute. refl. }
        { rewrite map_size_insert. des_ifs; nia. }
      }
      { i. assert (m = 0 ∨ m = 1).
        { vm_compute in H. nia. }
        { des; subst; ss. }
      }
    }

    steps_l; steps_r. call "IST".
    steps_l. rewrite map_size_insert map_size_empty lookup_empty.
    iDestruct "ASM" as (?) "[% [tidF [RRI [% %]]]]"; des; subst; hss.
    steps_r; hss. steps_r.

    rrs_yield_ir. rrs_yield_l. steps_l.

    (** 2nd spawn **)
    steps_l; steps_r. set (Invs := _ : gmap nat InvO).
    force_l (0, stid, ssch, RRSNodeAS.f_precond (b, 0%Z), Invs, existT 0 (x_value_tid 2)).

    subst Invs. steps_l. forces_l; ss. iSplitL "RRI TID".
    { iExists _. iFrame. iFrame "I". iSplit; eauto.
      do 3 iExists _. iSplit; eauto.
      iPureIntro. esplits; eauto.
      eapply f_spawnable.
      { split; eauto. vm_compute. econs. refl. }
      { i. vm_compute in H. do 3 (destruct m; ss); nia. }
    }

    steps_l; steps_r. call "IST".
    steps_l. rewrite !map_size_insert map_size_empty lookup_empty.
    rewrite lookup_insert_ne // lookup_empty.
    iDestruct "ASM" as (?) "[% [tidF [RRI [% %]]]]"; des; subst; hss.
    steps_r; hss. steps_r.

    rrs_yield_ir. rrs_yield_l. steps_l.

    (** Round-Robin yield *)
    unfold RRS.yield. unseal "RRS". steps_r. steps_l.

    set (Invs := _ : gmap nat InvO).
    force_l (0, stid, ssch, Invs). subst Invs. forces_l. iSplitL "RRI TID H".
    { iFrame. repeat iSplit; eauto. iExists _.
      do 2 (rewrite lookup_insert_ne; eauto).
      rewrite lookup_insert. iSplit; eauto.
      SL_red. rewrite /half_val. unseal "Node". iFrame. }

    steps_l; steps_r. call" IST".
    steps_l. steps_r. iDestruct "ASM" as "((% & tidF & % & % & RRI & % & INV) & ->)"; hss.

    forces_l. iSplitL "tidF"; eauto.
    step; eauto.
  (*SLOW*)Qed.

  Lemma unit_nat_neq (TEQ: @eq Type nat unit) : False.
  Proof.
    set (a:=1). set (b:=2).
    assert (a = b).
    { gen a. gen b. rewrite TEQ. i; hss. }
    subst a b. inv H.
  Qed.

  Lemma simF_f : ISim.sim_fun open MA MI init_cond IstFull (Some RRSNodeHdr.f).
  Proof using Hsub Hschglob Hschrrs Hsch Hrrs Hnode.
    init_simF.

    steps_l. depdes _q. rename x into mtid'. destruct p as [[[[mtid stid] ssch] [blk ofs]] Invs].
    iDestruct "ASM" as "(WI & % & % & tidF & RRIP & RRI & [% | HALF] & % & % & % & [% #inv])"; des; hss.
    steps_l; steps_r; hss. steps_r. SL_red. destruct mtid as [|mtid]; ss.

    assert (rrs_in_sp : sp_incl (RRSAS.sp sp_user E snd PYIP) sp).
    { rewrite /RRSAS.sp. unseal CRIS. econs; [prove_nodup|].
      i. eapply Hschglob. eapply Hrrs. rewrite /RRSAS.sp. unseal CRIS. eauto. }

    iApply wsim_fold; iFrame.
    rrs_yield_ir. steps_r.

    (** Open invariant **)
    rewrite /inv_x_points_to /ex_x_points_to.
    iInv "inv" as "PT" "CLOSE". SL_red. iDestruct "PT" as (?) "PT". SL_red. iDestruct "PT" as "[PT HALF0]".
    iPoseProof (RRSNodeAS.half_match with "[HALF HALF0]") as "%PREV".
    { rewrite /half_val. unseal "Node". iFrame. }
    rewrite PREV.
    
    inline_r. steps_r. forces_r. instantiate (1 := (blk, ofs, 1%Qp, _)); ss.
    iSplitL "PT"; iFrame; eauto.
    steps_r. iDestruct "GRT" as "[[PT ->] %]".
    steps_r; hss. steps_r.

    (** Close invariant **)
    iMod ("CLOSE" with "[PT HALF0]") as "_".
    { iExists _. SL_red. rewrite /half_val. unseal "Node". iFrame. }

    rrs_yield_ir. steps_r.

    inline_r. steps_r. force_r (S mtid, stid, ssch).
    forces_r. iSplitL "TID"; iFrame; eauto.
    steps_r; hss_r. steps_r.
    rewrite SBRed.get. rewrite /RRSI.RRSI.v_tid /= String.eqb_refl. ss.
    iApply wsim_sget_tgt. rewrite /or_else. steps_r. destruct (alist_find (RRS ↯ "tid") st_tgt) eqn:F; cycle 1.
    { rewrite F. steps_r. destruct (@Any.downcast nat tt↑) eqn:A; steps_r; ss.
      iDestruct "GRT" as "[[-> tid] <-]"; hss.
      exfalso. eapply unit_nat_neq; eauto. }
      
    rewrite F. steps_r. destruct (@Any.downcast nat t) eqn:A; steps_r; ss.
    iDestruct "GRT" as "[[% tidF] %]"; hss. steps_r.

    do 3 (rrs_yield_ir; steps_r).

    (** Open invariant **)
    rewrite /inv_x_points_to /ex_x_points_to.
    iInv "inv" as "PT" "CLOSE". SL_red. iDestruct "PT" as (?) "PT". SL_red. iDestruct "PT" as "[PT HALF0]".
    iPoseProof (RRSNodeAS.half_match with "[HALF HALF0]") as "%PREV".
    { rewrite /half_val. unseal "Node". iFrame. }
    rewrite PREV.

    inline_r. steps_r.  forces_r.
    instantiate (1 := (blk, ofs, Vint _, Vint _)); ss.
    iSplitL "PT"; iFrame; eauto. steps_r.
    iDestruct "GRT" as "[[PT ->] %]". steps_r; hss_r. steps_r.
    replace (S mtid - mtid)%Z with 1%Z by nia.

    (** Close invariant **)
    iCombine "HALF HALF0" as "FULL".
    iPoseProof (full_update (Vint mtid) (Vint (mtid + 1)) with "[FULL]") as ">FULL".
    { rewrite /full_val; unseal "Node"; iFrame. }
    iPoseProof (full_merge with "FULL") as "[HALF HALF0]".
    iMod ("CLOSE" with "[PT HALF0]") as "_".
    { iExists _. SL_red. rewrite /half_val. unseal "Node". iFrame. }

    rrs_yield_ir. rrs_yield_l. steps_l; steps_r.
    step. steps_r. steps_l.
    rrs_yield_ir. rrs_yield_l. steps_l; steps_r.

    unfold RRS.yield. unseal "RRS". steps_l.
    force_l (mtid + 1, stid, ssch, Invs').
    forces_l. iSplitL "TID RRI HALF".
    { replace (mtid + 1)%Z with (Z.of_nat (S mtid)) by nia.
      replace (mtid + 1) with (S mtid) by nia.
      iSplit; eauto. iFrame. iSplit; eauto. iExists _; iSplit; eauto. SL_red.
      rewrite /half_val. unseal "Node". iFrame. }
     
    steps_l. steps_r. call "IST".
    steps_l. iDestruct "ASM" as "[(% & tidF & % & % & RRI & % & INV) %]"; hss.
    steps_r. forces_l. replace (mtid + 1) with (S mtid) by nia.
    iFrame. iSplit; eauto.
    step. iFrame; eauto.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MA MI init_cond IstFull.
  Proof using Hsub Hschglob Hschrrs Hsch Hrrs Hnode.
    init_sim.
    - split; eauto. iIntros "_". iSplit; eauto. iPureIntro. split; ss.
    - eapply simF_main.
    - eapply simF_f.
  Qed.

End RRSNodeIA. End RRSNodeIA.

Section ctxr.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG}.
  Context `{_schG: !SchA.newschG}.
  Context `{_rrsG: !RRSA.rrsG}.
  Context `{_memG: !MemA.memG}.
  Context `{_nodeG: !RRSNodeA.nodeG}.

  Lemma ctxr E (Hsub : ↑RRSNodeAS.N_node ⊆ E) sp sp_sch_user sp_user
    (Hschglob: sp_incl sp_sch_user sp)
    (Hschrrs: spl_sub sp_user sp_sch_user)
    (Hsch: sp_incl (SchA.sp sp_sch_user E) sp)
    (Hrrs: spl_sub (RRSAS.sp sp_user E snd SchA.PYIP) sp_sch_user)
    (Hnode: spl_sub (RRSNodeAS.sp E) sp_user) :
    ctx_refines
      ((RRSNodeA.t E sp ★ (MemA.t sp) ★ (RRSA.t SchHdr.yield sp sp_user snd SchA.PYIP)), RRSNodeA.init_cond)
      ((RRSNodeI.t      ★ (MemA.t sp) ★ (RRSA.t SchHdr.yield sp sp_user snd SchA.PYIP)), emp%I).
  Proof using. eapply main_adequacy, (RRSNodeIA.sim E Hsub sp sp_sch_user); eauto. Qed.

End ctxr.
