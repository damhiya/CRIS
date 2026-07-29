From CRIS.common Require Import Common ConcRA.
From CRIS.modules Require Import LMod Mod SMod Sp.
From CRIS.simulations.msim Require Import MSim MSimFacts MSimCommon ISim TacticsCommon ITactics SimNotations.
From iris.proofmode Require Import proofmode.
From stdpp Require Import base list.

Section ISIM_FRAME.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma isim_ist_frame ctx Ist P Rs Rt RR fl_src fl_tgt
      ps pt (sti_s: _ * itree crisE Rs) (sti_t: _ * itree crisE Rt) :
    P ∗ isim ctx fl_src fl_tgt Ist ibot RR ps pt sti_s sti_t ⊢
    isim ctx fl_src fl_tgt
      (λ x y, P ∗ Ist x y)%I ibot (λ x y, P ∗ RR x y) ps pt sti_s sti_t.
  Proof using.
    eapply entails_pointwise. intros res _ H.
    destruct sti_s, sti_t. eapply isim_final.
    destruct (classic (✓ res)); [| gstep; econs; ii; ss].
    eapply Own_split in H; et; des.
    eapply isim_init in H2; et.
    gfinal. right.
    eapply paco8_mon; [eapply msim_ist_frame|]; ss.
    - ginit. eapply gpaco8_mon; eauto using iunlift_ibot.
    - rewrite H Own_op H1. et.
  Qed.
End ISIM_FRAME.

Section ISIM_REFL.
  Context `{!crisG Γ Σ α β τ _S _I}.

  (* Reflexivity of the isim relation *)
  Lemma isim_refl g ctx Ist fl_src fl_tgt msk ps pt st_src st_tgt {R} (it : itree crisE R) :
    (∀ st_src st_tgt k v,
      msk _ (subevent _ (SPut k v)) = true →
      Ist st_src st_tgt ⊢ Ist (<[k := Some v]> st_src) (<[k := Some v]> st_tgt)) →
    (∀ st_src st_tgt k,
      msk _ (subevent _ (SGet k)) = true →
      Ist st_src st_tgt ⊢ ⌜st_src !! k = st_tgt !! k⌝) →
    Ist st_src st_tgt ⊢
    isim ctx fl_src fl_tgt Ist g (ist_with_eq Ist) ps pt
      (st_src, SB.sandbox msk it)
      (st_tgt, SB.sandbox msk it).
  Proof using.
    intros Hset Hget.
    revert it. combine_quant st_tgt. combine_quant st_src. combine_quant ps. combine_quant pt.
    eapply isim_coind. intros g0 _ CIH [pt [ps [st_src [st_tgt it]]]].
    destruct_quant CIH. iIntros "IST /=".
    assert (CASE := case_itrH it); des; subst.
    - istep. iFrame. done.
    - istep_s. istep_t. iby_coind CIH; eauto.
    - istep_s; istep_t. des_if.
      { istep_s. iforce_t; iFrame "ASM". iby_coind CIH. eauto. }
      { istep_s; ss. }
    - istep_s; istep_t; des_if.
      { istep_s. iforce_t; iFrame "ASM". iby_coind CIH. eauto. }
      { istep_s; ss. }
    - istep_s; istep_t; des_if.
      { istep_t. iforce_s; iFrame. iby_coind CIH. eauto. }
      { istep_s; ss. }
    - depdes c.
      { istep_s. istep_t. des_if.
        { icall "IST" as (???) "IST"; et. iby_coind CIH; eauto. }
        { isteps_s; ss. }
      }
      { istep_s; istep_t. des_if.
        { istep. iby_coind CIH; done. }
        { isteps_s. ss. }
      }
      { cNormS; cNormT. des_if.
        { iyield "IST" as (??) "IST". iby_coind CIH. eauto. }
        { isteps_s. ss. }
      }
      { cNormS; cNormT. des_if.
        { istep. iby_coind CIH. eauto. }
        { isteps_s. ss. }
      }
    - depdes s.
      { istep_s; istep_t.
        rewrite ?resum_to_subevent ?subevent_subevent.
        specialize (Hset st_src st_tgt k v); destruct (msk _ _); [cNormS; cNormT|istep_s; ss].
        iApply isim_sput_src. iApply isim_sput_tgt.
        iby_coind CIH. iApply Hset; eauto.
      }
      { istep_s; istep_t.
        rewrite ?resum_to_subevent ?subevent_subevent.
        specialize (Hget st_src st_tgt k); destruct (msk _ _); [cNormS; cNormT|istep_s; ss].
        iApply isim_sget_src. iApply isim_sget_tgt. iPoseProof (Hget with "IST") as "->"; eauto.
        iby_coind CIH; eauto.
      }
    - destruct e.
      + istep_s; istep_t; des_if; [cNormS; cNormT|istep_s; ss].
        istep_t. iforce_s. cNormS; cNormT; iby_coind CIH; eauto.
      + istep_s; istep_t; des_if; [cNormS; cNormT|istep_s; ss].
        istep_s. iforce_t. cNormS; cNormT; iby_coind CIH; eauto.
      + istep_s; istep_t; des_if; [cNormS; cNormT|istep_s; ss].
        istep. cNormS; cNormT; iby_coind CIH; eauto.
  Qed.

  Lemma isim_reflL
      (ctx : contextuality) (fl_src fl_tgt : gmap fname (option fbody))
      (msk : emask) (scopesR : list string) (EqL Ist : ist_type Σ) itr :
    (∀ st_src st_tgt k v, msk _ (subevent _ (SPut k v)) = true →
       (EqL st_src st_tgt ⊢ EqL (<[k := Some v]> st_src) (<[k := Some v]> st_tgt)) ∧
      k.1 ∉ scopesR) →
    (∀ st_src st_tgt k, msk _ (subevent _ (SGet k)) = true →
      (EqL st_src st_tgt ⊢ ⌜st_src !! k = st_tgt !! k⌝) ∧
      k.1 ∉ scopesR) →
    ⊢ isim_fsem fl_src fl_tgt (IstProd EqL (IstSB scopesR Ist)) ctx
        (SB.sandbox_body (msk, itr)) (SB.sandbox_body (msk, itr)).
  Proof using.
    intros Hset Hget. rewrite /isim_fsem.
    iIntros "!#" (arg st_src st_tgt) "IST _".
    rewrite /SB.sandbox_body /=. iStopProof.
    eapply isim_refl; eauto.
    - intros st_src0 st_tgt0 k v Htrue.
      iIntros "[% [% [% [% [[-> ->] [ISTL [[%Hscopesr %Hscopesr2] ISTR]]]]]]]".
      eapply Hset in Htrue as [-> Hnin].
      iExists _, _, _, _; iFrame "ISTL ISTR".
      iPureIntro; split; eauto.
      rewrite ?insert_union_with_l // not_elem_of_dom_1 //.
      { intros Hk; enough (k.1 ∈ scopesR); [set_solver|].
        revert Hscopesr2 => /(_ k.1); rewrite elem_of_map elem_of_list_to_set.
        intros H'; apply H'; esplits; eauto.
      }
      { intros Hk; enough (k.1 ∈ scopesR); [set_solver|].
        revert Hscopesr => /(_ k.1); rewrite elem_of_map elem_of_list_to_set.
        intros H'; apply H'; esplits; eauto.
      }
    - intros st_src0 st_tgt0 k Htrue.
      iIntros "[% [% [% [% [[-> ->] [ISTL [[%Hsrc %Htgt] ISTR]]]]]]]".
      eapply Hget in Htrue as [-> Hnin]; iPoseProof "ISTL" as "%Heq".
      iPureIntro; rewrite ?lookup_union_with Heq.
      rewrite (not_elem_of_dom_1 st_srcR); cycle 1.
      { intros Hk; enough (k.1 ∈ scopesR); [set_solver|].
        revert Hsrc => /(_ k.1); rewrite elem_of_map elem_of_list_to_set.
        intros H'; apply H'; esplits; eauto.
      }
      rewrite (not_elem_of_dom_1 st_tgtR); cycle 1.
      { intros Hk; enough (k.1 ∈ scopesR); [set_solver|].
        revert Htgt => /(_ k.1); rewrite elem_of_map elem_of_list_to_set.
        intros H'; apply H'; esplits; eauto.
      }
      ss.
  Qed.

  Lemma isim_reflR
      (fl_src fl_tgt : gmap fname (option fbody))
      (ctx : contextuality) (msk : emask) (scopesL : list string)
      (EqR Ist : ist_type Σ) itr :
    (∀ st_src st_tgt k v, msk _ (subevent _ (SPut k v)) = true →
      (EqR st_src st_tgt ⊢ EqR (<[k := Some v]> st_src) (<[k := Some v]> st_tgt)) ∧
      k.1 ∉ scopesL) →
    (∀ st_src st_tgt k, msk _ (subevent _ (SGet k)) = true →
      (EqR st_src st_tgt ⊢ ⌜st_src !! k = st_tgt !! k⌝) ∧
      k.1 ∉ scopesL) →
    ⊢ isim_fsem fl_src fl_tgt (IstProd (IstSB scopesL Ist) EqR) ctx
        (SB.sandbox_body (msk, itr)) (SB.sandbox_body (msk, itr)).
  Proof using.
    intros Hset Hget. rewrite /isim_fsem.
    iIntros "!#" (arg st_src st_tgt) "IST _".
    rewrite /SB.sandbox_body /=. iStopProof.
    eapply isim_refl; eauto.
    - intros st_src0 st_tgt0 k v Htrue.
      iIntros "[% [% [% [% [[-> ->] [[[%Hsrc %Htgt] ISTL] ISTR]]]]]]".
      eapply Hset in Htrue as [-> Hnin].
      iExists _, _, _, _; iFrame "ISTL ISTR".
      iPureIntro; split; eauto.
      rewrite ?insert_union_with_r // not_elem_of_dom_1 //.
      { intros Hk; enough (k.1 ∈ scopesL); [set_solver|].
        revert Htgt => /(_ k.1); rewrite elem_of_map elem_of_list_to_set.
        intros H'; apply H'; esplits; eauto.
      }
      { intros Hk; enough (k.1 ∈ scopesL); [set_solver|].
        revert Hsrc => /(_ k.1); rewrite elem_of_map elem_of_list_to_set.
        intros H'; apply H'; esplits; eauto.
      }
    - intros st_src0 st_tgt0 k Htrue.
      iIntros "[% [% [% [% [[-> ->] [[[%Hsrc %Htgt] ISTL] ISTR]]]]]]".
      eapply Hget in Htrue as [-> Hnin]; iPoseProof "ISTR" as "%Heq".
      iPureIntro; rewrite ?lookup_union_with Heq.
      rewrite (not_elem_of_dom_1 st_srcL); cycle 1.
      { intros Hk; enough (k.1 ∈ scopesL); [set_solver|].
        revert Hsrc => /(_ k.1); rewrite elem_of_map elem_of_list_to_set.
        intros H'; apply H'; esplits; eauto.
      }
      rewrite (not_elem_of_dom_1 st_tgtL); cycle 1.
      { intros Hk; enough (k.1 ∈ scopesL); [set_solver|].
        revert Htgt => /(_ k.1); rewrite elem_of_map elem_of_list_to_set.
        intros H'; apply H'; esplits; eauto.
      }
      ss.
  Qed.

  Lemma ISim_refl (ctx : contextuality) (M : Mod.t) :
    ⊢ ISim.t ctx M M IstEq.
  Proof.
    rewrite /ISim.t. iIntros (WF).
    iSplit.
    { iPureIntro. split; first done. destruct WF; done. }
    iSplit.
    { done. }
    iIntros (fn). rewrite /ISim.sim_fun.
    iIntros "%WFS %WFT" (fs) "%Hfs".
    rewrite lookup_fmap in Hfs.
    destruct (Mod.fnsems M !! fn) as [[[fmsk fbdy]|]|] eqn:Hc; ss.
    clarify. iExists (SB.sandbox_body (fmsk, fbdy)).
    iSplit; first by rewrite /sandbox_fnsemmap lookup_fmap Hc.
    rewrite /isim_fsem. iIntros "!#" (arg st_src st_tgt) "IST WINV".
    iApply isim_refl; et.
    - intros. iIntros "->". et.
    - intros. iIntros "->". et.
  Qed.

  Lemma ISim_reflL
      (ctx : contextuality) (A B C : Mod.t) (init_cond : iProp Σ)
      (scopes : list string) (Ist : ist_type Σ) :
    (∀ fn, fn ∈ dom (Mod.fnsems A) →
      ⊢ ISim.sim_fun
          ctx (C ★ A) (C ★ B) (IstProd IstEq (IstSB scopes Ist)) fn) →
    Mod.scopes A ⊆+ scopes → scopes ⊆+ Mod.scopes B →
    dom (Mod.fnsems A) ⊆ dom (Mod.fnsems B) →
    (Mod.wf B → map_Forall (const is_Some) (Mod.fnsems A)) →
    (init_cond ⊢
      (IstProd IstEq (IstSB scopes Ist) (Mod.initial_st (C ★ A)) (Mod.initial_st (C ★ B)))) →
    init_cond ⊢
      ISim.t ctx (C ★ A) (C ★ B) (IstProd IstEq (IstSB scopes Ist)).
  Proof using.
    intros Hsim Hscp Hscp2 Hfns Hnodup Hval.
    rewrite /ISim.t. iIntros "INIT" (WFT).
    iSplit.
    { iPureIntro. split.
      { rewrite /= !sorting.merge_sort_Permutation.
        apply submseteq_app; etrans; eauto. }
      apply Mod.add_wf_inv in WFT. des. specialize (Hnodup WFT0).
      eapply map_Forall_union_with.
      { set_solver. }
      split; et. apply WFT.
    }
    iSplitL "INIT".
    { iApply Hval. done. }
    iIntros (fn).
    destruct (decide (fn ∈ dom (Mod.fnsems A))) as [Hin|Hnin].
    { iApply Hsim. done. }
    apply not_elem_of_dom in Hnin.
    rewrite /ISim.sim_fun.
    iIntros "%WFS %WFT2" (fs) "%Hsrc".
    rewrite lookup_fmap lookup_union_with Hnin in Hsrc.
    destruct (Mod.fnsems C !! fn)
      as [[[fmsksrc fbdysrc]|]|] eqn:Hc; ss.
    clarify.
    destruct (Mod.fnsems B !! fn) as [fnt|] eqn:Hb.
    { exfalso. inv WFT2.
      rewrite map_Forall_lookup in wf_fns.
      hexploit (wf_fns fn).
      { rewrite lookup_union_with Hc Hb //=. }
      intros []; done.
    }
    iExists (SB.sandbox_body (fmsksrc, fbdysrc)).
    iSplit.
    { iPureIntro.
      rewrite /sandbox_fnsemmap lookup_fmap lookup_union_with Hc Hb //. }
    iApply isim_reflL; ss.
      { intros ???? Hmsk; split; [iIntros "-> //"|].
        hexploit (Mod.well_scoped_fns C); rewrite map_Forall_lookup.
        intros Hsi; hexploit (Hsi fn (fmsksrc, fbdysrc)).
        { clarify; rewrite lookup_omap Hc //. }
        intros Htrue; apply Htrue in Hmsk.
        enough (scopes ## Mod.scopes C); [set_solver|].
        intros x Hin%(elem_of_subseteq _ (Mod.scopes B)) => HinC //.
        { hexploit (Mod.wf_scopes _ WFT); rewrite /Mod.add /= sorting.merge_sort_Permutation.
          rewrite NoDup_app; i; naive_solver.
        }
        intros a; eapply elem_of_submseteq in a; eauto.
      }
      { intros ??? Hmsk; split; [iIntros "-> //"|].
        hexploit (Mod.well_scoped_fns C); rewrite map_Forall_lookup.
        intros Hsi; hexploit (Hsi fn (fmsksrc, fbdysrc)).
        { clarify; rewrite lookup_omap Hc //. }
        intros Htrue; apply Htrue in Hmsk.
        enough (scopes ## Mod.scopes C); [set_solver|].
        intros x Hin%(elem_of_subseteq _ (Mod.scopes B)) => HinC //.
        { hexploit (Mod.wf_scopes _ WFT); rewrite /Mod.add /= sorting.merge_sort_Permutation.
          rewrite NoDup_app; i; naive_solver.
        }
        intros a; eapply elem_of_submseteq in a; eauto.
      }
  Qed.

  Lemma ISim_reflR
      (ctx : contextuality) (A B C : Mod.t) (init_cond : iProp Σ)
      (scopes : list string) (Ist : ist_type Σ) :
    (∀ fn, fn ∈ dom (Mod.fnsems A) →
      ⊢ ISim.sim_fun
          ctx (A ★ C) (B ★ C) (IstProd (IstSB scopes Ist) IstEq) fn) →
    Mod.scopes A ⊆+ scopes → scopes ⊆+ Mod.scopes B →
    dom (Mod.fnsems A) ⊆ dom (Mod.fnsems B) →
    (Mod.wf B → map_Forall (const is_Some) (Mod.fnsems A)) →
    (init_cond ⊢
      (IstProd (IstSB scopes Ist) IstEq (Mod.initial_st (A ★ C)) (Mod.initial_st (B ★ C)))) →
    init_cond ⊢
      ISim.t ctx (A ★ C) (B ★ C) (IstProd (IstSB scopes Ist) IstEq).
  Proof using.
    intros Hsim Hscp Hscp2 Hfns Hnodup Hval.
    rewrite /ISim.t. iIntros "INIT" (WFT).
    iSplit.
    { iPureIntro. split.
      { rewrite /= !sorting.merge_sort_Permutation.
        apply submseteq_app; etrans; eauto. }
      apply Mod.add_wf_inv in WFT. des. specialize (Hnodup WFT).
      eapply map_Forall_union_with.
      { set_solver. }
      split; et. apply WFT0.
    }
    iSplitL "INIT".
    { iApply Hval. done. }
    iIntros (fn).
    destruct (decide (fn ∈ dom (Mod.fnsems A))) as [Hin|Hnin].
    { iApply Hsim. done. }
    apply not_elem_of_dom in Hnin.
    rewrite /ISim.sim_fun.
    iIntros "%WFS %WFT2" (fs) "%Hsrc".
    rewrite lookup_fmap lookup_union_with Hnin in Hsrc.
    destruct (Mod.fnsems C !! fn)
      as [[[fmsksrc fbdysrc]|]|] eqn:Hc; ss.
    clarify.
    destruct (Mod.fnsems B !! fn) as [fnt|] eqn:Hb.
    { exfalso. inv WFT2.
      rewrite map_Forall_lookup in wf_fns.
      hexploit (wf_fns fn).
      { rewrite lookup_union_with Hc Hb //=. }
      intros []; done.
    }
    iExists (SB.sandbox_body (fmsksrc, fbdysrc)).
    iSplit.
    { iPureIntro.
      rewrite /sandbox_fnsemmap lookup_fmap lookup_union_with Hc Hb //. }
    iApply isim_reflR; ss.
      { intros ???? Hmsk; split; [iIntros "-> //"|].
        hexploit (Mod.well_scoped_fns C); rewrite map_Forall_lookup.
        intros Hsi; hexploit (Hsi fn (fmsksrc, fbdysrc)).
        { clarify; rewrite lookup_omap Hc //. }
        intros Htrue; apply Htrue in Hmsk.
        enough (scopes ## Mod.scopes C); [set_solver|].
        intros x Hin%(elem_of_subseteq _ (Mod.scopes B)) => HinC //.
        { hexploit (Mod.wf_scopes _ WFT); rewrite /Mod.add /= sorting.merge_sort_Permutation.
          rewrite NoDup_app; i; naive_solver.
        }
        intros a; eapply elem_of_submseteq in a; eauto.
      }
      { intros ??? Hmsk; split; [iIntros "-> //"|].
        hexploit (Mod.well_scoped_fns C); rewrite map_Forall_lookup.
        intros Hsi; hexploit (Hsi fn (fmsksrc, fbdysrc)).
        { clarify; rewrite lookup_omap Hc //. }
        intros Htrue; apply Htrue in Hmsk.
        enough (scopes ## Mod.scopes C); [set_solver|].
        intros x Hin%(elem_of_subseteq _ (Mod.scopes B)) => HinC //.
        { hexploit (Mod.wf_scopes _ WFT); rewrite /Mod.add /= sorting.merge_sort_Permutation.
          rewrite NoDup_app; i; naive_solver.
        }
        intros a; eapply elem_of_submseteq in a; eauto.
      }
  Qed.
End ISIM_REFL.

(* Section LAT.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Lemma isim_lat_real_to_img
      peeking img fsp lbody_s lbody_t body_s body_t fl_s fl_t msk scp ps pt st arg
      (EQITL: eqit eq false true
              (SB.sandbox true msk scp (SModTr.trans img sp_none lbody_s))
              (SB.sandbox false msk scp (SModTr.trans img sp_none lbody_t)))
      (EQIT: eqit eq false true
              (SB.sandbox true msk scp (SModTr.trans img sp_none (body_s arg)))
              (SB.sandbox false msk scp (SModTr.trans img sp_none (body_t arg))))
    :
    ⊢
    isim open fl_s fl_t IstEq ibot ibot (ist_with_eq IstEq) ps pt
      (st, SB.sandbox true msk scp (SModTr.trans img sp_none (lat_img peeking fsp lbody_s body_s arg)))
      (st, SB.sandbox false msk scp (SModTr.trans img sp_none (lat_real peeking fsp lbody_t body_t arg))).
  Proof using.
    destruct fsp as [m pre post].
    iApply isim_reset. clear ps pt. iStopProof. revert st.
    eapply isim_coind. intros g Hg CIH st. iIntros. destruct_quant CIH.
    rewrite /lat_img /lat_real.
    unfoldIterS. unfoldIterT. rewrite {1}/lat_img_body {1}/lat_real_body.
    cNormS. cNormT. iApply isim_bind. iSplitL "".
    { iApply isim_eqit_tgt; et.
      iApply isim_refl; et; i; iIntros "%"; subst; et.
    }
    iIntros (????) "%"; des; subst.
    isteps_s. isteps_t.
    destruct (peeking); cycle 1.
    {
      isteps_s. isteps_t.
      iApply isim_bind. iSplitL "".
      { iApply isim_eqit_tgt; et.
        iApply isim_refl; et; i; iIntros "%"; subst; et.
      }

      iIntros (????) "%"; des; subst.
      isteps_s. isteps_t.
      iforce_t. iFrame. iIntros "GRT".
      iforce_s. iFrame. isteps_s. isteps_t.
      istep; et.
    }

    isteps_t. destruct _q0.
    { iforce_t. iFrame. iIntros "GRT".
      iforce_s true. isteps_s. iforce_s. iFrame. isteps_s. isteps_t.
      iby_coind CIH; et.
    }

    iforce_s false. isteps_s. isteps_t.
    iApply isim_bind. iSplitL "".
    { iApply isim_eqit_tgt; et.
      iApply isim_refl; et; i; iIntros "%"; subst; et.
    }

    iIntros (????) "%"; des; subst.
    isteps_s. isteps_t.
    iforce_t. iFrame. iIntros "GRT".
    iforce_s. iFrame. isteps_s. isteps_t.
    istep; et.
  Qed.

  Lemma isim_lat_img_to_hoare fsp img body_s body_t fl_s fl_t msk scp ps pt st arg
    (EQIT: eqit eq false true
            (SB.sandbox true msk scp (body_s arg))
            (SB.sandbox true msk scp (SModTr.trans img sp_none (body_t arg))))
    :
    ⊢
    isim open fl_s fl_t IstEq ibot ibot (ist_with_eq IstEq) ps pt
      (st, SB.sandbox true msk scp (SModTr.HoareFun (Some (to_fspec fsp)) body_s arg))
      (st, SB.sandbox true msk scp (SModTr.trans img sp_none (lat_img false fsp (Ret ()) body_t arg))).
  Proof using.
    iIntros. isteps_s. rewrite /lat_img /lat_img_body. unfoldIterT. isteps_t.
    destruct fsp. destruct PHY as [P1 P2]. iPoseProof (P1 with "ASM") as "->".
    iforces_r. iFrame. isteps_t.
    iApply isim_bind. iSplitL "".
    { iApply isim_eqit_tgt; et.
      iApply isim_refl; et; i; iIntros "%"; subst; et.
    }
    iIntros (?????). des; subst.
    isteps_t. iforces_l. iFrame.
    istep. et.
  Qed.

  Lemma isim_lat_real_to_hoare fsp img body_s body_t fl_s fl_t msk scp ps pt st arg
    (EQIT: eqit eq false true
            (SB.sandbox true msk scp (body_s arg))
            (SB.sandbox false msk scp (SModTr.trans img sp_none (body_t arg))))
    :
    ⊢
    isim open fl_s fl_t IstEq ibot ibot (ist_with_eq IstEq) ps pt
      (st, SB.sandbox true msk scp (SModTr.HoareFun (Some (to_fspec fsp)) body_s arg))
      (st, SB.sandbox false msk scp (SModTr.trans img sp_none (lat_real false fsp (Ret ()) body_t arg))).
  Proof using.
    iIntros. isteps_s. rewrite /lat_real /lat_real_body. unfoldIterT. isteps_t.
    destruct fsp. destruct PHY as [P1 P2]. iPoseProof (P1 with "ASM") as "->".
    iApply isim_bind. iSplitL "".
    { iApply isim_eqit_tgt; et.
      iApply isim_refl; et; i; iIntros "%"; subst; et.
    }
    iIntros (????) "%"; des; subst.
    isteps_s. isteps_t.
    iforce_t. iFrame. iIntros "GRT".
    iforces_l. iFrame.
    isteps_s. isteps_t. istep; et.
  Qed.
End LAT. *)
