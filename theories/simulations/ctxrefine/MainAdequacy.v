From CRIS.common Require Import Common ConcRA.
From iris.proofmode Require Import proofmode.
From CRIS.modules Require Import LMod Mod SMod Sp.
From CRIS.simulations.msim Require Import MSim MSimFacts MSimCommon ISim ISimFacts ISimAdequacy TacticsInit.
From CRIS.simulations.ctxrefine Require Import CtxRefine ClosedAdequacy.

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
  SB.sandbox msk (ktr x) = ktr x ∧ (msk X e ∨ SB.msk_default X e).
Proof.
  rewrite SBRed.bind SBRed.vis; des_ifs; ss.
  { rewrite ?bind_vis; intros H; depdes H; eapply equal_f in x; eauto.
    revert x; rewrite SBRed.ret; ired; bsimpl; eauto.
  }
  { rewrite bind_trigger bind_vis. intros H; depdes H; ss. }
Qed.

Lemma inv_sandbox_tau `{Σ : GRA} {X} msk (ktr : itree crisE X) :
  (SB.sandbox msk (tau;; ktr) = tau;; ktr) →
  SB.sandbox msk ktr = ktr.
Proof. rewrite SBRed.tau; grind. Qed.

Ltac mstep := guclo msimC_spec; econs; econs; eauto; econs; eauto.

Local Lemma Own_Ist `{Σ : GRA} FR fmr scp scp_ctx Ist st_src st_tgt :
  ✓ fmr →
  (Own fmr ⊢ |==> IstProd (IstSB scp Ist) (IstSB scp_ctx IstEq) st_src st_tgt ∗ FR) →
  ∃ st_srcL st_tgtL st_ctx,
    st_src = union_with uwnd st_srcL st_ctx ∧
    st_tgt = union_with uwnd st_tgtL st_ctx ∧
    (set_map fst (dom st_srcL)) ⊆@{gset string} list_to_set scp ∧
    (set_map fst (dom st_tgtL)) ⊆@{gset string} list_to_set scp ∧
    (set_map fst (dom st_ctx)) ⊆@{gset string} list_to_set scp_ctx ∧
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
  Mod.scopes ms ⊆+ Mod.scopes mt →
  (set_map fst (dom st_src)) ⊆@{gset string} (list_to_set (Mod.scopes mt)) →
  (set_map fst (dom st_tgt)) ⊆@{gset string} (list_to_set (Mod.scopes mt)) →
  (set_map fst (dom st_ctx)) ⊆@{gset string} (list_to_set (Mod.scopes ctx)) →
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
    (union_with uwnd st_src st_ctx, itr_src) 
    (union_with uwnd st_tgt st_ctx, itr_tgt) fmr.
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
        i; clarify; eapply sandbox_sandbox; eauto.
        intros ? e; depdes e; ss. depdes s; ss. depdes s; ss.
        depdes p; ss; hexploit (Mod.well_scoped_fns ms); rewrite map_Forall_lookup =>
          /(_ (funid fn) (fnmsk, f0)); rewrite lookup_omap Hfn => /(_ eq_refl);
          [intros [Hkey ?]|intros [? Hkey]] => /Hkey; case_decide as Hin2; ss;
          intros Hin; eapply elem_of_submseteq in Hscopest; eauto.
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
        i; clarify; eapply sandbox_sandbox; eauto.
        intros ? e; depdes e; ss. depdes s; ss. depdes s; ss.
        depdes p; ss; hexploit (Mod.well_scoped_fns mt); rewrite map_Forall_lookup =>
          /(_ (funid fn) (fnmsk, f0)); rewrite lookup_omap Hfn => /(_ eq_refl);
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
    eapply inv_sandbox_event in Hsbs as [Hktr Hmsk]; bsimpl; des; ss; case_decide; ss.
    rewrite insert_union_with_l.
    { eapply K; eauto. rewrite dom_insert_L; set_solver. }
    rewrite not_elem_of_dom_1 //.
    assert (Mod.scopes ctx ## Mod.scopes mt); [|set_solver].
    intros x Hxc Hxt; hexploit (Mod.wf_scopes _ Hwft).
    rewrite /= sorting.merge_sort_Permutation NoDup_app; i; des; naive_solver.
  }
  { mstep.
    eapply inv_sandbox_event in Hsbt as [Hktr Hmsk]; bsimpl; des; ss; case_decide; ss.
    rewrite insert_union_with_l.
    { eapply K; eauto. rewrite dom_insert_L; set_solver. }
    rewrite not_elem_of_dom_1 //.
    assert (Mod.scopes ctx ## Mod.scopes mt); [|set_solver].
    intros x Hxc Hxt; hexploit (Mod.wf_scopes _ Hwft).
    rewrite /= sorting.merge_sort_Permutation NoDup_app; i; des; naive_solver.
  }
  { mstep. eapply K; eauto using inv_sandbox_ktr.
    eapply inv_sandbox_event in Hsbs as [Hktr Hmsk]; bsimpl; des; ss; case_decide; ss.
    rewrite lookup_union_with (not_elem_of_dom_1 st_ctx); [destruct (_ !! _); ss|].
    assert (Mod.scopes ctx ## Mod.scopes mt); [|set_solver].
    intros x Hxc Hxt; hexploit (Mod.wf_scopes _ Hwft).
    rewrite /= sorting.merge_sort_Permutation NoDup_app; i; des; naive_solver.
  }
  { mstep. eapply K; eauto using inv_sandbox_ktr.
    eapply inv_sandbox_event in Hsbt as [Hktr Hmsk]; bsimpl; des; ss; case_decide; ss.
    rewrite lookup_union_with (not_elem_of_dom_1 st_ctx); [destruct (_ !! _); ss|].
    assert (Mod.scopes ctx ## Mod.scopes mt); [|set_solver].
    intros x Hxc Hxt; hexploit (Mod.wf_scopes _ Hwft).
    rewrite /= sorting.merge_sort_Permutation NoDup_app; i; des; naive_solver.
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
  Mod.scopes ms ⊆+ Mod.scopes mt →
  (set_map fst (dom st_src)) ⊆@{gset string} list_to_set (Mod.scopes mt) →
  (set_map fst (dom st_tgt)) ⊆@{gset string} list_to_set (Mod.scopes mt) →
  (set_map fst (dom st_ctx)) ⊆@{gset string} list_to_set (Mod.scopes ctx) →
  Mod.wf (ms ★ ctx) →
  Mod.wf (mt ★ ctx) →
  (∃ fno, Mod.fnsems ms !! fno = Some (Some fs) ∧ Mod.fnsems mt !! fno = Some (Some ft)) →
  isim open
    ((λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems ms))
    ((λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems mt))
    Ist ibot (ist_with_eq RR) false false
    (st_src, SB.sandbox_body fs arg)
    (st_tgt, SB.sandbox_body ft arg) ⊢
  @isim _ contextual
    ((λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems (ms ★ ctx)))
    ((λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems (mt ★ ctx)))
    (IstProd (IstSB (Mod.scopes mt) Ist) (IstSB (Mod.scopes ctx) IstEq))
    ibot Any.t Any.t
    (ist_with_eq (IstProd (IstSB (Mod.scopes mt) RR) (IstSB (Mod.scopes ctx) IstEq)))
    false false
    (union_with uwnd st_src st_ctx, SB.sandbox_body fs arg)
    (union_with uwnd st_tgt st_ctx, SB.sandbox_body ft arg).
Proof.
  intros Hscp Hsrc Htgt Hctx Hwfs Hwft Hin.
  apply entails_pointwise => r _ Hsim.
  eapply isim_init in Hsim; eauto.
  eapply gpaco8_mon in Hsim; try apply iunlift_ibot; eauto.
  eapply gpaco8_init in Hsim; eauto with paco.
  eapply isim_final, gpaco8_final; eauto with paco; right.
  eapply paco8_mon_bot; eauto.
  destruct fs as [msks bds]; destruct ft as [mskt bdt].
  eapply msim_ctx; eauto.
  { destruct Hin as [fno [Hins Hint]].
    eapply sandbox_sandbox; ss.
    intros ? s; depdes s; ss; depdes s; ss; depdes s; ss.
    depdes p; ss; hexploit (Mod.well_scoped_fns ms); rewrite map_Forall_lookup =>
      /(_ fno (msks, bds)); rewrite lookup_omap Hins => /(_ eq_refl);
      [intros [Hkey ?]|intros [? Hkey]] => /Hkey; case_decide as Hin2; ss;
      intros Hin; eapply elem_of_submseteq in Hscp; eauto.
  }
  { destruct Hin as [fno [Hins Hint]].
    eapply sandbox_sandbox; ss.
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
    hexploit Mod.add_wf_inv; eauto; intros [Hwft [Hwfctx [Hdom Hnd]]].
    hexploit ISim_wf; eauto; intros Hwfs.
    assert (Hwfsctx : Mod.wf (ms ★ ctx)).
    { apply Mod.add_wf; eauto.
      { intros i His Htctx; eapply ISim_dom in His; eauto. }
      { inv Hsim; hexploit sim_scopes; eauto; intros [? temp]%submseteq_Permutation.
        rewrite temp comm assoc NoDup_app in Hnd; des; rewrite comm //.
      }
    }
    pose Hsim as Hsim'; destruct Hsim' as [Hscp Hnodup Hic Hsimfun].
    econs; intros _.
    { hexploit Hscp; eauto.
      rewrite /= !sorting.merge_sort_Permutation; i; eapply submseteq_app; eauto.
    }
    { eapply Hwfsctx. }
    { rewrite Hic //; iIntros "$"; iExists _, _; iSplit; eauto.
      iSplit; eauto.
      { iPureIntro; split; [|destruct mt; ss].
        etrans; first apply (Mod.well_scoped_init).
        intros ?; rewrite ?elem_of_list_to_set; hexploit Hscp; eauto.
        i; eapply elem_of_submseteq; eauto.
      }
      iSplit; [iPureIntro; split; destruct ctx; ss|ss].
    }
    intros fno WFS WFT; move: Hsimfun => /(_ Hwft fno).
    rewrite /ISim.sim_fun ?lookup_fmap /= ?lookup_union_with.
    destruct (_ ms !! fno) as [[[fmsk fbd]|]|] eqn: Hfnoms; ss.
    { move => /= /(_ Hwfs Hwft) [? [? Hsimfun]].
      destruct (_ mt !! fno) as [[[fmskt fbdt]|]|] eqn : Hfnomt; ss; clarify.
      destruct (_ ctx !! fno) as [|] eqn : Hctx.
      { exfalso; apply elem_of_dom_2 in Hctx, Hfnomt; set_solver. }
      ss; esplits; eauto.
      iIntros (arg st_src st_tgt) "[% [% [% [% [[-> ->] [[[% %] IST] [[% _] ->]]]]]]] W".
      iApply isim_ctx; eauto.
      iApply (Hsimfun arg _ _ with "IST W").
    }
    { exfalso. eapply Hwfs in Hfnoms. rr in Hfnoms. des; ss. }

    destruct (_ ctx !! fno) as [[[fmsk fbd]|]|] eqn : Hfnoctx; ss.
    intros _.
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
      intros x Hin%(elem_of_subseteq _ (Mod.scopes mt)) => HinC //.
      hexploit (Mod.wf_scopes _ Hwftctx).
      rewrite /= sorting.merge_sort_Permutation NoDup_app; i; des; naive_solver.
    }
    { intros ??? Hkey; hexploit (Mod.well_scoped_fns ctx fno (fmsk, fbd)).
      { rewrite lookup_omap Hfnoctx //. }
      intros [_ Hmsk]; move: Hmsk => /(_ k Hkey) ?; split.
      { iIntros "[% ->] //". }
      enough (Mod.scopes mt ## Mod.scopes ctx); [set_solver|].
      intros x Hin%(elem_of_subseteq _ (Mod.scopes mt)) => HinC //.
      hexploit (Mod.wf_scopes _ Hwftctx).
      rewrite /= sorting.merge_sort_Permutation NoDup_app; i; des; naive_solver.
    }
  Qed.

  Theorem main_adequacy (Mt Ms : Mod.t) IC Ist :
    ISim.t open Ms Mt IC Ist ->
    IC ⊢ ctx_refines Mt Ms.
  Proof.
    iIntros (SIM) "H %Ctx".
    iApply ISim_closed_adequacy.
    { eapply ISim_ctx. eapply SIM. }
    done.
  Qed.

End ADEQUACY.
