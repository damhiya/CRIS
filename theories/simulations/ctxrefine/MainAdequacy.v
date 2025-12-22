Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import LMod Mod SMod Sp.
Require Import LSim LSimFacts MSim MSimFacts MSimCommon.
Require Import ISim ISimFacts ClosedAdequacy TacticsInit.
Require Import CtxRefine.

(** This file contains the main lemma of CRIS, namely ISim.t implies ctx_refines. *)

Lemma inv_sandbox_ktr `{Σ : GRA} {X Y} x msk (ktr : _ → itree crisE Y) (e : crisE X) :
  SB.sandbox msk (trigger e >>= ktr) = trigger e >>= ktr →
  SB.sandbox msk (ktr x) = ktr x.
Proof.
  rewrite SBRed.bind SBRed.vis; des_ifs; ss.
  { rewrite ?bind_vis; intros H; depdes H; eapply equal_f in x; eauto.
    revert x; rewrite SBRed.ret; ired; eauto.
  }
  { rewrite bind_trigger bind_vis. intros H; depdes H; ss. }
Qed.

Lemma inv_sandbox_event `{Σ : GRA} {X Y} (x: X) msk (ktr : _ → itree crisE Y) (e : crisE X) :
  SB.sandbox msk (trigger e >>= ktr) = trigger e >>= ktr →
  SB.sandbox msk (ktr x) = ktr x ∧ msk X e.
Proof.
  rewrite SBRed.bind SBRed.vis; des_ifs; ss.
  { rewrite ?bind_vis; intros H; depdes H; eapply equal_f in x; eauto.
    revert x; rewrite SBRed.ret; ired; eauto.
  }
  { rewrite bind_trigger bind_vis. intros H; depdes H; ss. }
Qed.

Lemma inv_sandbox_tau `{Σ : GRA} {X} msk (ktr : itree crisE X) :
  (SB.sandbox msk (tau;; ktr) = tau;; ktr) →
  SB.sandbox msk ktr = ktr.
Proof. rewrite SBRed.tau; grind. Qed.

Lemma sandbox_well_scoped `{Σ : GRA} {A} (msk0 msk1 : emask) (itr : itree crisE A) :
  (∀ X e, msk0 X e → msk1 X e) →
  SB.sandbox msk1 (SB.sandbox msk0 itr) = SB.sandbox msk0 itr.
Proof.
  intros Hmsk; apply bisim_is_eq; revert itr; ginit; gcofix CIH; intros itr.
  ides itr.
  { rewrite !SBRed.ret; gstep; econs; eauto. }
  { rewrite !SBRed.tau; gstep; econs; eauto.
    gbase; eauto.
  }
  { rewrite !SBRed.vis; des_ifs.
    { rewrite SBRed.vis; des_ifs.
      { gstep; econs; intros v; eauto.
        gbase; eauto.
      }
      { apply Hmsk in Heq; bsimpl; clarify. }
    }
    { rewrite SBRed.vis; des_ifs; gstep; econs; ii; ss. }
  }
Qed.

Ltac mstep := guclo msimC_spec; econs; econs; eauto; econs; eauto.

Local Lemma Own_Ist `{Σ : GRA} FR fmr scp scp_ctx Ist st_src st_tgt :
  ✓ fmr →
  (Own fmr ⊢ |==> IstProd (IstSB scp Ist) (IstSB scp_ctx IstEq) st_src st_tgt ∗ FR) →
  ∃ st_srcL st_tgtL st_ctx,
    st_src = union_with (const (const (Some None))) st_srcL st_ctx ∧
    st_tgt = union_with (const (const (Some None))) st_tgtL st_ctx ∧
    (set_map fst (dom st_srcL)) ⊆ dom scp ∧
    (set_map fst (dom st_tgtL)) ⊆ dom scp ∧
    (set_map fst (dom st_ctx)) ⊆ dom scp_ctx ∧
    (Own fmr ⊢ |==> Ist st_srcL st_tgtL ∗ FR).
Proof.
  intros Hfmr2val Hfmr2.
  eapply Own_bupd_split in Hfmr2 as [fmr21 [fmr22 [Hfmr2 [Hfmr21 Hfmr22]]]]; eauto.
  eapply Own_general_soundness in Hfmr21; eauto; cycle 1.
  { eapply Own_wand_valid; [iIntros "F"; iMod (Hfmr2 with "F") as "[$ _]"|]; done. }
  rewrite /IstProd /IstSB /IstEq in Hfmr21; uPred.unseal_in Hfmr21.
  destruct Hfmr21 as [st_srcL [st_tgtL [st_srcR [st_tgtR Hfmr21]]]].    
  destruct Hfmr21 as [? [fmr212 [Hfmr21 [[-> ->] Hfmr212]]]].
  destruct Hfmr212 as [fmr2121 [fmr2122 [Hfmr212 [Hfmr2121 Hfmr2122]]]].
  destruct Hfmr2121 as [? [fmr21212 [Hfmr2121 [[?] Hfmr21212]]]].
  destruct Hfmr2122 as [? [? [Hfmr2122 [[?] []]]]].
  eapply Own_general_completeness in Hfmr21212.
  esplits; eauto.
  rewrite Hfmr2 Hfmr21 Hfmr212 Hfmr2121 ?Own_op Hfmr21212 Hfmr22.
  iIntros "> [[? [[? ?] ?]] ?]"; by iFrame.
Qed.

Lemma msim_ctx
    `{Σ : GRA} contextual ms mt ctx
    Ist RR
    ps pt st_src st_tgt st_ctx itr_src itr_tgt fmr :
  Mod.scopes ms ⊆ Mod.scopes mt →
  (set_map fst (dom st_src)) ⊆ (dom (Mod.scopes mt)) →
  (set_map fst (dom st_tgt)) ⊆ (dom (Mod.scopes mt)) →
  (set_map fst (dom st_ctx)) ⊆ (dom (Mod.scopes ctx)) →
  SB.sandbox (msk_scp (Mod.scopes mt) msk_true) itr_src = itr_src →
  SB.sandbox (msk_scp (Mod.scopes mt) msk_true) itr_tgt = itr_tgt →
  Mod.wf (ms ★ ctx) →
  Mod.wf (mt ★ ctx) →
  msim open
    ((λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems ms))
    ((λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems mt))
    Ist (ist_with_eq RR) ps pt (st_src, itr_src) (st_tgt, itr_tgt) fmr →
  @msim _ contextual
    ((λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems (ms ★ ctx)))
    ((λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems (mt ★ ctx)))
    (IstProd (IstSB (Mod.scopes mt) Ist) (IstSB (Mod.scopes ctx) IstEq)) Any.t Any.t
    (ist_with_eq (IstProd (IstSB (Mod.scopes mt) RR) (IstSB (Mod.scopes ctx) IstEq))) ps pt
    (union_with (const (const (Some None))) st_src st_ctx, itr_src) 
    (union_with (const (const (Some None))) st_tgt st_ctx, itr_tgt) fmr.
Proof.
  ginit.
  intros ?????? Hwfs Hwft.
  move Hwfs at top. move Hwft at top.
  revert_until RR. gcofix CIH.
  intros ps pt st_src st_tgt st_ctx itr_src itr_tgt fmr Hscopest ? ? ? Hsbs Hsbt Hsim.
  remember (st_src, itr_src) as ss. remember (st_tgt, itr_tgt) as st.
  move Hsim before CIH. revert_until Hsim. punfold Hsim.
  pattern ps, pt, ss, st, fmr.
  eapply _msim_tarski, Hsim; clear Hsim fmr; intros ???? fmr Hin ????? ?????? -> ->.
  guclo msim_wfC_spec. econs. intros Hval.
  guclo msim_nodupC_spec; econs; intros Hfs Hft Hss Hst; hexploit Hin; ss.
  { move: Hfs; rewrite ?map_Forall_lookup => Hfs i x; move: Hfs => /(_ i x) /=.
    rewrite ?lookup_fmap lookup_union_with.
    destruct (_ ms !! i) as [[[? ?]|]|]; destruct (_ ctx !! i); ss; i; clarify.
  }
  { move: Hft; rewrite ?map_Forall_lookup => Hft i x; move: Hft => /(_ i x) /=.
    rewrite ?lookup_fmap lookup_union_with.
    destruct (_ mt !! i) as [[[? ?]|]|]; destruct (_ ctx !! i); ss; i; clarify.
  }
  { move: Hss; rewrite ?map_Forall_lookup => Hss i x; move: Hss => /(_ i x) /=.
    rewrite ?lookup_fmap lookup_union_with.
    destruct (st_src !! i) as [[|]|]; destruct (st_ctx !! i); ss; i; clarify.
  }
  { move: Hst; rewrite ?map_Forall_lookup => Hst i x; move: Hst => /(_ i x) /=.
    rewrite ?lookup_fmap lookup_union_with.
    destruct (st_tgt !! i) as [[|]|]; destruct (st_ctx !! i); ss; i; clarify.
  }

  clear Hin; intros Hin.
  destruct Hin as [fmr1 [Hin Hfmr]]; eauto.
  inv Hin; try by (mstep; eauto using inv_sandbox_ktr, inv_sandbox_tau).
  { mstep; rewrite RET; iIntros "> [-> $] !>"; iSplit; [done|iExists _, _; iSplit; eauto]. }
  { mstep.
    { instantiate (1:=FR). rewrite INV; iIntros "> [$ $] !>"; iExists _, _; iSplit; eauto. }
    intros ? st_src2 st_tgt2 fmr2 Hfmr2.
    guclo msim_wfC_spec; econs; intros Hfmr2val.
    hexploit Own_Ist; eauto; intros [? [? [? [-> [-> [? [? [? ?]]]]]]]].
    eapply K; eauto using inv_sandbox_ktr.
  }
  { mstep; cycle 1.
    { eapply K; eauto using inv_sandbox_ktr.
      ired. rewrite SBRed.bind; ired.
      assert (Hf : SB.sandbox (msk_scp (Mod.scopes mt) msk_true) (f varg) = f varg).
      { move: FUN; rewrite lookup_fmap; destruct (_ ms !! _) as [[[fnmsk ?]|]|] eqn : Hfn; ss.
        i; clarify; eapply sandbox_well_scoped; eauto.
        intros ? e; depdes e; ss. depdes s; ss. depdes s; ss.
        depdes p; ss; hexploit (Mod.well_scoped_fns ms); rewrite map_Forall_lookup =>
          /(_ (Some fn) (fnmsk, f0)); rewrite lookup_omap Hfn => /(_ eq_refl);
          [intros [Hkey ?]|intros [? Hkey]] => /Hkey; case_decide as Hin2; ss;
          intros Hin; eapply gmultiset_elem_of_subseteq in Hscopest; eauto.
      }
      rewrite Hf; grind.
      rewrite SBRed.tau; ired; grind; eauto using inv_sandbox_ktr.
    }
    revert FUN; intros [[f2|] [? FUN]]%lookup_fmap_Some; ss; clarify.
    move : FUN => /(Mod.lookup_add_l); move /(_ ctx Hwfs) => /=; rewrite lookup_fmap => -> //=.
  }
  { mstep; cycle 1.
    { eapply K; eauto using inv_sandbox_ktr.
      ired. rewrite SBRed.bind; ired.
      assert (Hf : SB.sandbox (msk_scp (Mod.scopes mt) msk_true) (f varg) = f varg).
      { move: FUN; rewrite lookup_fmap; destruct (_ mt !! _) as [[[fnmsk ?]|]|] eqn : Hfn; ss.
        i; clarify; eapply sandbox_well_scoped; eauto.
        intros ? e; depdes e; ss. depdes s; ss. depdes s; ss.
        depdes p; ss; hexploit (Mod.well_scoped_fns mt); rewrite map_Forall_lookup =>
          /(_ (Some fn) (fnmsk, f0)); rewrite lookup_omap Hfn => /(_ eq_refl);
          [intros [Hkey ?]|intros [? Hkey]] => /Hkey; case_decide; ss;
          intros Hin; eapply elem_of_submseteq in Hin; eauto.
      }
      rewrite Hf; grind.
      rewrite SBRed.tau; ired; grind; eauto using inv_sandbox_ktr.
    }
    revert FUN; intros [[f2|] [? FUN]]%lookup_fmap_Some; ss; clarify.
    move : FUN => /(Mod.lookup_add_l); move /(_ ctx Hwft) => /=; rewrite lookup_fmap => -> //=.
  }
  { mstep.
    eapply inv_sandbox_event in Hsbs as [Hktr Hmsk]; ss; case_decide; ss.
    rewrite insert_union_with_l.
    { eapply K; eauto. rewrite dom_insert_L; set_solver. }
    rewrite not_elem_of_dom_1 //.
    assert (Mod.scopes ctx ## Mod.scopes mt); [|set_solver].
    intros x Hxc Hxt; hexploit (Mod.wf_scopes _ Hwft x); rewrite ?elem_of_multiplicity in Hxc, Hxt.
    rewrite multiplicity_disj_union; lia.
  }
  { mstep.
    eapply inv_sandbox_event in Hsbt as [Hktr Hmsk]; ss; case_decide; ss.
    rewrite insert_union_with_l.
    { eapply K; eauto. rewrite dom_insert_L; set_solver. }
    rewrite not_elem_of_dom_1 //.
    assert (Mod.scopes ctx ## Mod.scopes mt); [|set_solver].
    intros x Hxc Hxt; hexploit (Mod.wf_scopes _ Hwft x); rewrite ?elem_of_multiplicity in Hxc, Hxt.
    rewrite multiplicity_disj_union; lia.
  }
  { mstep. eapply K; eauto using inv_sandbox_ktr.
    eapply inv_sandbox_event in Hsbs as [Hktr Hmsk]; ss; case_decide; ss.
    rewrite lookup_union_with (not_elem_of_dom_1 st_ctx); [destruct (_ !! _); ss|].
    assert (Mod.scopes ctx ## Mod.scopes mt); [|set_solver].
    intros x Hxc Hxt; hexploit (Mod.wf_scopes _ Hwft x); rewrite ?elem_of_multiplicity in Hxc, Hxt.
    rewrite multiplicity_disj_union; lia.
  }
  { mstep. eapply K; eauto using inv_sandbox_ktr.
    eapply inv_sandbox_event in Hsbt as [Hktr Hmsk]; ss; case_decide; ss.
    rewrite lookup_union_with (not_elem_of_dom_1 st_ctx); [destruct (_ !! _); ss|].
    assert (Mod.scopes ctx ## Mod.scopes mt); [|set_solver].
    intros x Hxc Hxt; hexploit (Mod.wf_scopes _ Hwft x); rewrite ?elem_of_multiplicity in Hxc, Hxt.
    rewrite multiplicity_disj_union; lia.
  }
  { mstep.
    { instantiate (1:=FR). rewrite INV; iIntros "> [$ $] !>"; iExists _, _; iSplit; eauto. }
    intros st_src2 st_tgt2 fmr2 Hfmr2.
    guclo msim_wfC_spec; econs; intros Hfmr2val.
    hexploit Own_Ist; eauto; intros [? [? [? [-> [-> [? [? [? ?]]]]]]]].
    eapply K; eauto using inv_sandbox_ktr.
  }
  { gstep. econs. econs. econs; eauto. econs; eauto.
    gbase. pclearbot. eapply CIH; try refl; eauto.
  }
  Unshelve. all: try exact (()↑).
Qed.

Lemma isim_ctx `{Σ : GRA} contextual RR fs ft ms mt ctx Ist arg st_src st_tgt st_ctx :
  (set_map fst (dom st_src)) ⊆ dom (Mod.scopes mt) →
  (set_map fst (dom st_tgt)) ⊆ dom (Mod.scopes mt) →
  (set_map fst (dom st_ctx)) ⊆ dom (Mod.scopes ctx) →
  Mod.scopes ms ⊆ Mod.scopes mt →
  Mod.wf (ms ★ ctx) →
  Mod.wf (mt ★ ctx) →
  (∃ fno, Mod.fnsems ms !! fno = Some (Some fs) ∧ Mod.fnsems mt !! fno = Some (Some ft)) →
  isim open
    ((λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems ms))
    ((λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems mt))
    Ist ibot ibot (ist_with_eq RR) false false
    (st_src, SB.sandbox_body fs arg)
    (st_tgt, SB.sandbox_body ft arg) ⊢
  @isim _ contextual
    ((λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems (ms ★ ctx)))
    ((λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems (mt ★ ctx)))
    (IstProd (IstSB (Mod.scopes mt) Ist) (IstSB (Mod.scopes ctx) IstEq))
    ibot ibot Any.t Any.t
    (ist_with_eq (IstProd (IstSB (Mod.scopes mt) RR) (IstSB (Mod.scopes ctx) IstEq)))
    false false
    (union_with (const (const (Some None))) st_src st_ctx, SB.sandbox_body fs arg)
    (union_with (const (const (Some None))) st_tgt st_ctx, SB.sandbox_body ft arg).
Proof.
  intros Hsrc Htgt Hctx Hscp Hwfs Hwft Hin.
  apply entails_pointwise => r Hsim.
  eapply isim_init in Hsim; eauto.
  eapply gpaco8_mon in Hsim; try apply iunlift_ibot.
  eapply gpaco8_init in Hsim; eauto with paco.
  eapply isim_final, gpaco8_final; eauto with paco; right.
  eapply paco8_mon_bot; eauto.
  destruct fs as [msks bds]; destruct ft as [mskt bdt].
  eapply msim_ctx; eauto.
  { destruct Hin as [fno [Hins Hint]].
    eapply sandbox_well_scoped; ss.
    intros ? s; depdes s; ss; depdes s; ss; depdes s; ss.
    depdes p; ss; hexploit (Mod.well_scoped_fns ms); rewrite map_Forall_lookup =>
      /(_ fno (msks, bds)); rewrite lookup_omap Hins => /(_ eq_refl);
      [intros [Hkey ?]|intros [? Hkey]] => /Hkey; case_decide as Hin2; ss;
      intros Hin; eapply gmultiset_elem_of_subseteq in Hscp; eauto.
  }
  { destruct Hin as [fno [Hins Hint]].
    eapply sandbox_well_scoped; ss.
    intros ? s; depdes s; ss; depdes s; ss; depdes s; ss.
    depdes p; ss; hexploit (Mod.well_scoped_fns mt); rewrite map_Forall_lookup =>
      /(_ fno (mskt, bdt)); rewrite lookup_omap Hint => /(_ eq_refl);
      [intros [Hkey ?]|intros [? Hkey]] => /Hkey; case_decide; ss;
      intros Hin; eapply elem_of_submseteq in Hin; eauto.
  }
Qed.

Section ADEQUACY.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma ISim_ctx contextual (ms mt ctx : Mod.t) IC Ist : 
    ISim.t open ms mt IC Ist →
    ISim.t contextual (ms ★ ctx) (mt ★ ctx) IC
      (IstProd (IstSB mt.(Mod.scopes) Ist) (IstSB ctx.(Mod.scopes) IstEq)).
  Proof using.
    intros Hsim; apply ISim.t_strong; intros Hwftctx.
    hexploit Mod.add_wf; eauto; intros [Hwft Hwfctx].
    hexploit ISim_wf; eauto; intros Hwfs.
    pose Hsim as Hsim'; destruct Hsim' as [Hscp Hic Hsimfun].
    econs; intros _.
    { hexploit Hscp; eauto.
      do 2 (etrans; first apply gmultiset_disj_union_mono; eauto).
    }
    { rewrite Hic //; iIntros "$"; iExists _, _; iSplit; eauto.
      iSplit; eauto.
      { iPureIntro; split; [|destruct mt; ss].
        etrans; first apply (Mod.well_scoped_init).
        intros ?; rewrite ?gmultiset_elem_of_dom; hexploit Hscp; eauto.
        i; eapply gmultiset_elem_of_subseteq; eauto.
      }
      iSplit; [iPureIntro; split; destruct ctx; ss|ss].
    }
    intros fno; move: Hsimfun => /(_ Hwft fno).
    rewrite /ISim.sim_fun ?lookup_fmap /= ?lookup_union_with.
    destruct (_ ms !! fno) as [[[fmsk fbd]|]|] eqn: Hfnoms; ss.
    { move => /= /(_ Hwfs Hwft) [? [? Hsimfun]].
      destruct (_ mt !! fno) as [[[fmskt fbdt]|]|] eqn : Hfnomt; ss; clarify.
      destruct (_ ctx !! fno) as [|]; ss; intros ??; esplits; eauto.
      iIntros (arg st_src st_tgt) "[% [% [% [% [[-> ->] [[[% %] IST] [[% _] ->]]]]]]] W".
      iApply isim_ctx; eauto.
      iApply (Hsimfun arg _ _ with "IST W").
    }
    { exfalso; move: (Mod.wf_fns ms Hwfs).
      rewrite map_Forall_lookup => /(_ fno None Hfnoms) [??] //.
    }
    { destruct (_ ctx !! fno) as [[[fmsk fbd]|]|] eqn : Hfnoctx; ss.
      { intros _ ? ?.
        destruct (_ mt !! fno) eqn : Hmt; ss.
        { exfalso; move: (Mod.wf_fns _ Hwftctx); rewrite map_Forall_lookup => /(_ fno None) /=.
          rewrite lookup_union_with Hmt Hfnoctx //= => /(_ eq_refl) => [[??]] //.
        }
        eexists; split; [done|].
        apply isim_reflR; eauto.
        { intros ???? Hkey; hexploit (Mod.well_scoped_fns ctx fno (fmsk, fbd)).
          { rewrite lookup_omap Hfnoctx //. }
          intros [Hmsk _]; move: Hmsk => /(_ k v Hkey) ?; split.
          { iIntros "[% ->]"; iSplit; [rewrite ?dom_insert_L|eauto]; iPureIntro.
            split; set_solver.
          }
          enough (Mod.scopes mt ## Mod.scopes ctx); [set_solver|].
          intros x Hin%(gmultiset_elem_of_subseteq _ (Mod.scopes mt)) => HinC //.
          hexploit (Mod.wf_scopes _ Hwftctx x); rewrite ?elem_of_multiplicity in Hin, HinC.
          rewrite multiplicity_disj_union; lia.
        }
        { intros ??? Hkey; hexploit (Mod.well_scoped_fns ctx fno (fmsk, fbd)).
          { rewrite lookup_omap Hfnoctx //. }
          intros [_ Hmsk]; move: Hmsk => /(_ k Hkey) ?; split.
          { iIntros "[% ->] //". }
          enough (Mod.scopes mt ## Mod.scopes ctx); [set_solver|].
          intros x Hin%(gmultiset_elem_of_subseteq _ (Mod.scopes mt)) => HinC //.
          hexploit (Mod.wf_scopes _ Hwftctx x); rewrite ?elem_of_multiplicity in Hin, HinC.
          rewrite multiplicity_disj_union; lia.
        }
      }
      { exfalso; move: (Mod.wf_fns ctx Hwfctx).
        rewrite map_Forall_lookup => /(_ fno None Hfnoctx) [??] //.
      }
    }
  Qed.

  Theorem main_adequacy (ms mt : Mod.t) IC Ist :
    ISim.t open ms mt IC Ist →
    ctx_refines (ms, IC) (mt, emp%I).
  Proof using.
    intros Hsim [ctx ctxcond]; ss.
    eapply ISim_ctx with (ctx := ctx) in Hsim.
    eapply closed_adequacy with (P := ctxcond) in Hsim.
    intros Hwfm%Hsim; ss; split; [des; ss|]. intros ???%Hwfm; eauto.
    des; esplits; eauto; rewrite -bi.emp_sep_1 //.
  Qed.
End ADEQUACY.
