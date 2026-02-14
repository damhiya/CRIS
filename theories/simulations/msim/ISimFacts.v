From iris.proofmode Require Import proofmode.
Require Import Common ConcRA.
Require Import LMod Mod SMod Sp.
Require Import LSim LSimTactics MSim MSimFacts MSimCommon ISim TacticsCommon ITactics SimNotations.

Section ISIM_FRAME.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma isim_ist_frame ctx Ist P Rs Rt RR fl_src fl_tgt
      ps pt (sti_s: _ * itree crisE Rs) (sti_t: _ * itree crisE Rt) :
    P ∗ isim ctx fl_src fl_tgt Ist ibot ibot RR ps pt sti_s sti_t ⊢
    isim ctx fl_src fl_tgt
      (λ x y, P ∗ Ist x y)%I ibot ibot (λ x y, P ∗ RR x y) ps pt sti_s sti_t.
  Proof using.
    eapply entails_pointwise. i.
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
  Lemma isim_refl r g ctx Ist fl_src fl_tgt msk ps pt st_src st_tgt {R} (it : itree crisE R) :
    (∀ st_src st_tgt k v,
      msk _ (subevent _ (SPut k v)) = true →
      Ist st_src st_tgt ⊢ Ist (<[k := Some v]> st_src) (<[k := Some v]> st_tgt)) →
    (∀ st_src st_tgt k,
      msk _ (subevent _ (SGet k)) = true →
      Ist st_src st_tgt ⊢ ⌜st_src !! k = st_tgt !! k⌝) →
    Ist st_src st_tgt ⊢
    isim ctx fl_src fl_tgt Ist r g (ist_with_eq Ist) ps pt
      (st_src, SB.sandbox msk it)
      (st_tgt, SB.sandbox msk it).
  Proof using.
    intros Hset Hget. revert it.
    combine_quant st_tgt. combine_quant st_src. combine_quant ps. combine_quant pt.
    eapply isim_coind.
    intros g0 _ CIH [pt [ps [st_src [st_tgt it]]]].
    destruct_quant CIH. iIntros "IST /=".
    assert (CASE := case_itrH it); des; subst.
    - istep. iFrame. done.
    - istep_l. istep_r. iby_coind CIH; eauto.
    - istep_l; istep_r. des_if.
      { istep_l. iforce_r; iFrame "ASM". iby_coind CIH. eauto. }
      { istep_l; ss. }
    - istep_l; istep_r; des_if.
      { istep_l. iforce_r; iFrame "ASM". iby_coind CIH. eauto. }
      { istep_l; ss. }
    - istep_l; istep_r; des_if.
      { istep_r. iforce_l; iFrame. iby_coind CIH. eauto. }
      { istep_l; ss. }
    - depdes c.
      { istep_l. istep_r. des_if.
        { norm_l; norm_r. iApply isim_call. iSplitL "IST"; eauto.
          iIntros (???) "IST"; iby_coind CIH; eauto.
        }
        { isteps_l; ss. }
      }
      { istep_l; istep_r. des_if.
        { norm_l; norm_r. iApply isim_spawn. iIntros "%"; iby_coind CIH; done. }
        { isteps_l. ss. }
      }
      { norm_l; norm_r. des_if.
        { iyield "IST". iby_coind CIH. eauto. }
        { isteps_l. ss. }
      }
      { norm_l; norm_r. des_if.
        { norm_l; norm_r. iApply isim_gettid; iIntros "%"; iby_coind CIH. eauto. }
        { isteps_l. ss. }
      }
    - depdes s.
      { istep_l; istep_r.
        rewrite ?resum_to_subevent ?subevent_subevent.
        specialize (Hset st_src st_tgt k v); destruct (msk _ _); [norm_l; norm_r|istep_l; ss].
        iApply isim_sput_src. iApply isim_sput_tgt.
        iby_coind CIH. iApply Hset; eauto.
      }
      { istep_l; istep_r.
        rewrite ?resum_to_subevent ?subevent_subevent.
        specialize (Hget st_src st_tgt k); destruct (msk _ _); [norm_l; norm_r|istep_l; ss].
        iApply isim_sget_src. iApply isim_sget_tgt. iPoseProof (Hget with "IST") as "->"; eauto.
        iby_coind CIH; eauto.
      }
    - destruct e.
      + istep_l; istep_r; des_if; [norm_l; norm_r|istep_l; ss].
        istep_r. iforce_l. norm_l; norm_r; iby_coind CIH; eauto.
      + istep_l; istep_r; des_if; [norm_l; norm_r|istep_l; ss].
        istep_l. iforce_r. norm_l; norm_r; iby_coind CIH; eauto.
      + istep_l; istep_r; des_if; [norm_l; norm_r|istep_l; ss].
        istep. norm_l; norm_r; iby_coind CIH; eauto.
  Qed.

  Lemma isim_reflL
      (ctx : contextuality) (fl_src fl_tgt : gmap (option string) (option fbody))
      (msk : emask) (scopesR : list string) (EqL Ist : ist_type Σ) itr :
    (∀ st_src st_tgt k v, msk _ (subevent _ (SPut k v)) = true →
       (EqL st_src st_tgt ⊢ EqL (<[k := Some v]> st_src) (<[k := Some v]> st_tgt)) ∧
      k.1 ∉ scopesR) →
    (∀ st_src st_tgt k, msk _ (subevent _ (SGet k)) = true →
      (EqL st_src st_tgt ⊢ ⌜st_src !! k = st_tgt !! k⌝) ∧
      k.1 ∉ scopesR) →
    isim_fsem fl_src fl_tgt (IstProd EqL (IstSB scopesR Ist)) ctx
      (SB.sandbox_body (msk, itr)) (SB.sandbox_body (msk, itr)).
  Proof using.
    intros Hset Hget arg st_src st_tgt; rewrite /SB.sandbox_body /=.
    iIntros "IST _". iStopProof.
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
      (fl_src fl_tgt : gmap (option string) (option fbody))
      (ctx : contextuality) (msk : emask) (scopesL : list string)
      (EqR Ist : ist_type Σ) itr :
    (∀ st_src st_tgt k v, msk _ (subevent _ (SPut k v)) = true →
      (EqR st_src st_tgt ⊢ EqR (<[k := Some v]> st_src) (<[k := Some v]> st_tgt)) ∧
      k.1 ∉ scopesL) →
    (∀ st_src st_tgt k, msk _ (subevent _ (SGet k)) = true →
      (EqR st_src st_tgt ⊢ ⌜st_src !! k = st_tgt !! k⌝) ∧
      k.1 ∉ scopesL) →
    isim_fsem fl_src fl_tgt (IstProd (IstSB scopesL Ist) EqR) ctx
      (SB.sandbox_body (msk, itr)) (SB.sandbox_body (msk, itr)).
  Proof using.
    intros Hset Hget arg st_src st_tgt; rewrite /SB.sandbox_body /=.
    iIntros "IST _". iStopProof.
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

  Lemma ISim_reflL
      (ctx : contextuality) (A B C : Mod.t) (init_cond : iProp Σ)
      (scopes : list string) (Ist : ist_type Σ) :
    (∀ fn, fn ∈ dom (Mod.fnsems A) →
      ISim.sim_fun ctx (C ★ A) (C ★ B) (IstProd IstEq (IstSB scopes Ist)) fn) →
    Mod.scopes A ⊆+ scopes →
    scopes ⊆+ Mod.scopes B →
    dom (Mod.fnsems A) ⊆ dom (Mod.fnsems B) →
    (init_cond ⊢
      (IstProd IstEq (IstSB scopes Ist) (Mod.initial_st (C ★ A)) (Mod.initial_st (C ★ B)))) →
    ISim.t ctx (C ★ A) (C ★ B) init_cond (IstProd IstEq (IstSB scopes Ist)).
  Proof using.
    intros Hsim Hscp Hscp2 Hfns Hval; econs; intros Hwf.
    { rewrite /= !sorting.merge_sort_Permutation; apply submseteq_app; etrans; eauto. }
    { rr; rewrite ?lookup_fmap ?lookup_union_with; ss. }
    { rewrite /ISim.sim_fun.
      intros fn; rewrite lookup_fmap lookup_union_with.
      destruct (Mod.fnsems C !! fn) as [fnc|] eqn : Hc; cycle 1.
      { destruct (_ A !! fn) eqn : Ha; ss; clarify.
        hexploit (Hsim fn); [eapply elem_of_dom; eauto|].
        rewrite /ISim.sim_fun; intros Hsim2; hexploit Hsim2; eauto.
        rewrite lookup_fmap /= lookup_union_with Hc Ha /=; des_ifs.
      }
      destruct (_ A !! fn) eqn : Ha; ss.
      { hexploit (Hsim fn); [apply elem_of_dom; eauto|]; rewrite /ISim.sim_fun; intros Hsim2.
        hexploit Hsim2; eauto; rewrite lookup_fmap /= lookup_union_with Hc Ha //=.
      }
      destruct fnc as [[fmsksrc fbdysrc]|]; ss; cycle 1.
      { inv Hwf; rewrite map_Forall_lookup in wf_fns.
        hexploit (wf_fns fn None); [|intros Hf; inv Hf].
        rewrite lookup_union_with Hc /=.
        destruct (_ B !! fn) eqn : Hb; ss.
      }
      intros Hwftgt.
      rewrite lookup_fmap lookup_union_with Hc; destruct (_ B !! fn) eqn : Hb; ss.
      { inv Hwftgt; rewrite map_Forall_lookup in wf_fns; hexploit (wf_fns fn).
        { rewrite lookup_union_with Hc Hb //=. }
        intros []; done.
      }
      eexists _; split; first refl.
      eapply isim_reflL; ss.
      { intros ???? Hmsk; split; [iIntros "-> //"|].
        hexploit (Mod.well_scoped_fns C); rewrite map_Forall_lookup.
        intros Hsi; hexploit (Hsi fn (fmsksrc, fbdysrc)).
        { clarify; rewrite lookup_omap Hc //. }
        intros Htrue; apply Htrue in Hmsk.
        enough (scopes ## Mod.scopes C); [set_solver|].
        intros x Hin%(elem_of_subseteq _ (Mod.scopes B)) => HinC //.
        { hexploit (Mod.wf_scopes _ Hwf); rewrite /Mod.add /= sorting.merge_sort_Permutation.
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
        { hexploit (Mod.wf_scopes _ Hwf); rewrite /Mod.add /= sorting.merge_sort_Permutation.
          rewrite NoDup_app; i; naive_solver.
        }
        intros a; eapply elem_of_submseteq in a; eauto.
      }
    }
  Qed.

  Lemma ISim_reflR
      (ctx : contextuality) (A B C : Mod.t) (init_cond : iProp Σ)
      (scopes : list string) (Ist : ist_type Σ) :
    (∀ fn, fn ∈ dom (Mod.fnsems A) →
      ISim.sim_fun ctx (A ★ C) (B ★ C) (IstProd (IstSB scopes Ist) IstEq) fn) →
    Mod.scopes A ⊆+ scopes →
    scopes ⊆+ Mod.scopes B →
    dom (Mod.fnsems A) ⊆ dom (Mod.fnsems B) →
    (init_cond ⊢
      (IstProd (IstSB scopes Ist) IstEq (Mod.initial_st (A ★ C)) (Mod.initial_st (B ★ C)))) →
    ISim.t ctx (A ★ C) (B ★ C) init_cond (IstProd (IstSB scopes Ist) IstEq).
  Proof using.
    intros Hsim Hscp Hscp2 Hfns Hval; econs; intros Hwf.
    { rewrite /= !sorting.merge_sort_Permutation; apply submseteq_app; etrans; eauto. }
    { rr; rewrite ?lookup_fmap ?lookup_union_with; ss. }
    { rewrite /ISim.sim_fun.
      intros fn; rewrite lookup_fmap lookup_union_with.
      destruct (Mod.fnsems C !! fn) as [fnc|] eqn : Hc; cycle 1.
      { destruct (_ A !! fn) eqn : Ha; ss; clarify.
        hexploit (Hsim fn); [eapply elem_of_dom; eauto|].
        rewrite /ISim.sim_fun; intros Hsim2; hexploit Hsim2; eauto.
        rewrite lookup_fmap /= lookup_union_with Hc Ha /=; des_ifs.
      }
      destruct (_ A !! fn) eqn : Ha; ss.
      { hexploit (Hsim fn); [apply elem_of_dom; eauto|]; rewrite /ISim.sim_fun; intros Hsim2.
        hexploit Hsim2; eauto; rewrite lookup_fmap /= lookup_union_with Hc Ha //=.
      }
      destruct fnc as [[fmsksrc fbdysrc]|]; ss; cycle 1.
      { inv Hwf; rewrite map_Forall_lookup in wf_fns.
        hexploit (wf_fns fn None); [|intros Hf; inv Hf].
        rewrite lookup_union_with Hc /=.
        destruct (_ B !! fn) eqn : Hb; ss.
      }
      intros Hwftgt.
      rewrite lookup_fmap lookup_union_with Hc; destruct (_ B !! fn) eqn : Hb; ss.
      { inv Hwftgt; rewrite map_Forall_lookup in wf_fns; hexploit (wf_fns fn).
        { rewrite lookup_union_with Hc Hb //=. }
        intros []; done.
      }
      eexists _; split; first refl.
      eapply isim_reflR; ss.
      { intros ???? Hmsk; split; [iIntros "-> //"|].
        hexploit (Mod.well_scoped_fns C); rewrite map_Forall_lookup.
        intros Hsi; hexploit (Hsi fn (fmsksrc, fbdysrc)).
        { clarify; rewrite lookup_omap Hc //. }
        intros Htrue; apply Htrue in Hmsk.
        enough (scopes ## Mod.scopes C); [set_solver|].
        intros x Hin%(elem_of_subseteq _ (Mod.scopes B)) => HinC //.
        { hexploit (Mod.wf_scopes _ Hwf); rewrite /Mod.add /= sorting.merge_sort_Permutation.
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
        { hexploit (Mod.wf_scopes _ Hwf); rewrite /Mod.add /= sorting.merge_sort_Permutation.
          rewrite NoDup_app; i; naive_solver.
        }
        intros a; eapply elem_of_submseteq in a; eauto.
      }
    }
  Qed.
End ISIM_REFL.

Section ISIM_ADEQUACY.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Lemma ISim_wf contextual ms mt cond Ist :
    ISim.t contextual ms mt cond Ist → Mod.wf mt → Mod.wf ms.
  Proof using.
    intros [Hscp Hinit Hsim] Ht; pose proof Ht as Ht0; inv Ht; econs.
    { rewrite map_Forall_lookup; intros i x Hx.
      rewrite /ISim.sim_fun in Hsim; hexploit (Hsim Ht0 i); eauto.
      rewrite lookup_fmap Hx /=; destruct x; ss.
    }
    { eapply submseteq_Permutation in Hscp; eauto.
      destruct Hscp as [? Hscp]; rewrite Hscp NoDup_app in wf_scopes; by des.
    }
  Qed.

  Lemma ISim_match contextual ms mt cond Ist fn :
    ISim.t contextual ms mt cond Ist →
    Mod.wf mt →
    fn ∈ dom (Mod.fnsems ms) →
    fn ∈ dom (Mod.fnsems mt).
  Proof using.
    intros Hsim Hwf [? Hin]%elem_of_dom; eapply ISim_wf in Hwf as Hwfsrc; eauto.
    rewrite elem_of_dom.
    destruct (_ mt !! fn) eqn : Ht; ss.
    destruct Hsim; hexploit (sim_fnsems Hwf fn); eauto.
    rewrite /ISim.sim_fun ?lookup_fmap Ht Hin /=.
    des_ifs; ss; intros H; clarify; hexploit H; eauto; i; des; clarify.
  Qed.

  (* ISim.t implies lsim_mod *)
  Lemma ISim_adequacy (ms mt : Mod.t) (rs rt : Σ) (IC : iProp Σ) Ist
      (SUB : Own rs ⊢ |==> Own rt ∗ (IC ∗ winv (∅,∅)))
      (WF : ✓ rs)
      (WFT : Mod.wf mt)
      (SIM : ISim.t closed ms mt IC Ist) :
    lsim_mod (Mod.to_lmod ms rs) (Mod.to_lmod mt rt).
  Proof using.
    hexploit ISim_wf; eauto; intros WFS.
    dup SIM. dup WFS. dup WFT. destruct SIM0, WFS0, WFT0.
    econs; ss.
    - ii; subst; eauto.
    - instantiate (1 := Σ).
      instantiate (2 := interp_inv (λ x y, winv (∅, ∅) ∗ Ist x y)%I).
      instantiate (1 := ε).
      ii; inv WF0. econs; eauto.
      iIntros "H". iMod (MRS with "H") as "H". iModIntro.
      unfold ctx_sem. rewrite big_opL_app. s. rewrite ?right_id; eauto.
    - intros it_src Hsrc; rewrite ?lookup_fmap lookup_omap in Hsrc.
      hexploit (sim_fnsems WFT None); rewrite /ISim.sim_fun.
      rewrite ?lookup_fmap lookup_omap; destruct (_ ms !! None) as [[p|]|] eqn : Hsrc2; ss; clarify.
      intros Hsim; hexploit Hsim; eauto; clear Hsim; intros [ft [Htgt Hsim]].
      destruct (_ mt !! None) as [[pt|]|] eqn : Htgt2; ss; clarify.
      eexists; split; first refl.

      intros arg; exists ε, ε.
      specialize (Hsim arg (Mod.initial_st ms) (Mod.initial_st mt)).
      eapply lsim_mon_rr.
      { instantiate (1:= interp_inv IstTrue). et. }

      exploit Own_bupd_split; et. i; des.
      exploit Own_split; i; des; et.
      { eapply Own_wand_valid, WF. rewrite x0. iIntros ">[_ ?]". et. }

      eapply msim_adequacy; eauto.
      + f_equal. instantiate (1:=(λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems ms)).
        apply map_eq; intros i; rewrite ?lookup_omap ?lookup_fmap lookup_omap.
        destruct (_ ms !! i); ss.
      + f_equal. instantiate (1:=(λ v : option _, SB.sandbox_body <$> v) <$> (Mod.fnsems mt)).
        apply map_eq; intros i; rewrite ?lookup_omap ?lookup_fmap lookup_omap.
        destruct (_ mt !! i); ss.
      + eapply map_Forall_fmap, map_Forall_impl; eauto; intros ? [[??]|]; ss; intros H; inv H.
      + eapply map_Forall_fmap, map_Forall_impl; eauto; intros ? [[??]|]; ss; intros H; inv H.
      + destruct ms; ss; apply nodup_init; eauto.
      + destruct mt; ss; apply nodup_init; eauto.
      + eapply le_mine_refl. et.
      + ginit. eapply isim_init.
        * iIntros "P". iApply isim_mono; cycle 1; i.
          { iApply isim_ist_frame; et. }
          { instantiate (1:= (ist_with_eq Ist)). s.
            iIntros "[? [? ?]]". iFrame. }
        * instantiate (1:= a0 ⋅ a3). rewrite !Own_op x4 x5.
          iIntros "[H I]".
          iPoseProof (winv_split_empty with "[I]") as "[I I']"; et; iFrame.
          iApply (Hsim with "[H]"); et. iApply sim_initial; done.
        * eauto using iunlift_ibot.
        * eauto using iunlift_ibot.
      + rewrite x0 x1 x3 !Own_op -Own_unit. iIntros ">[? [? ?]]"; iFrame. et.
    - intros fn fs; rewrite ?lookup_fmap lookup_omap.
      destruct (_ ms !! _) as [[[msks its]|]|] eqn : Hms; ss; i; clarify.
      hexploit (sim_fnsems WFT (Some fn)); eauto.
      rewrite /ISim.sim_fun ?lookup_fmap Hms /= ?lookup_fmap lookup_omap.
      intros H; hexploit H; clear H; eauto.
      destruct (_ mt !! _) as [[[mskt itt]|]|] eqn : Hmt; try by (i; des; clarify).
      intros [? [? Hsim]]; clarify; ss.
      eexists; split; first done.
      intros tid ??? arg ??. inv SIMMRS. specialize (Hsim arg st_src st_tgt).
      eapply msim_adequacy; eauto; cycle 4.
      { apply le_mine_refl. ii; eauto. }
      { ginit; cycle 2; i.
        eapply gpaco8_mon with (r := iunlift ibot) (rg:= iunlift ibot); eauto using iunlift_ibot.
        eapply isim_init; eauto.
        iIntros "H". iApply isim_upd. iMod (MR with "H") as "[I H]".
        iPoseProof (Hsim with "[H]") as "SIM"; cycle 2; s; et.
        iPoseProof (winv_split_empty with "[I]") as "[I I']"; et.
        iPoseProof ("SIM" with "I") as "SIM".
        iModIntro. iApply isim_mono; cycle 1; i.
        { iApply isim_ist_frame; et. iFrame. }
        { s. iIntros "[? [? ?]]". iFrame. }
      }
      { f_equal. apply map_eq; intros i; rewrite ?lookup_omap ?lookup_fmap lookup_omap.
        destruct (_ ms !! i); ss.
      }
      { f_equal. apply map_eq; intros i; rewrite ?lookup_omap ?lookup_fmap lookup_omap.
        destruct (_ mt !! i); ss.
      }
      { eapply map_Forall_fmap, map_Forall_impl; eauto; intros ? [[??]|]; ss; intros H; inv H. }
      { eapply map_Forall_fmap, map_Forall_impl; eauto; intros ? [[??]|]; ss; intros H; inv H. }
  Qed.
End ISIM_ADEQUACY.

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
    unfold_iter_l. unfold_iter_r. rewrite {1}/lat_img_body {1}/lat_real_body.
    norm_l. norm_r. iApply isim_bind. iSplitL "".
    { iApply isim_eqit_tgt; et.
      iApply isim_refl; et; i; iIntros "%"; subst; et.
    }
    iIntros (????) "%"; des; subst.
    isteps_l. isteps_r.
    destruct (peeking); cycle 1.
    {
      isteps_l. isteps_r.
      iApply isim_bind. iSplitL "".
      { iApply isim_eqit_tgt; et.
        iApply isim_refl; et; i; iIntros "%"; subst; et.
      }

      iIntros (????) "%"; des; subst.
      isteps_l. isteps_r.
      iforce_r. iFrame. iIntros "GRT".
      iforce_l. iFrame. isteps_l. isteps_r.
      istep; et.
    }

    isteps_r. destruct _q0.
    { iforce_r. iFrame. iIntros "GRT".
      iforce_l true. isteps_l. iforce_l. iFrame. isteps_l. isteps_r.
      iby_coind CIH; et.
    }

    iforce_l false. isteps_l. isteps_r.
    iApply isim_bind. iSplitL "".
    { iApply isim_eqit_tgt; et.
      iApply isim_refl; et; i; iIntros "%"; subst; et.
    }

    iIntros (????) "%"; des; subst.
    isteps_l. isteps_r.
    iforce_r. iFrame. iIntros "GRT".
    iforce_l. iFrame. isteps_l. isteps_r.
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
    iIntros. isteps_l. rewrite /lat_img /lat_img_body. unfold_iter_r. isteps_r.
    destruct fsp. destruct PHY as [P1 P2]. iPoseProof (P1 with "ASM") as "->".
    iforces_r. iFrame. isteps_r.
    iApply isim_bind. iSplitL "".
    { iApply isim_eqit_tgt; et.
      iApply isim_refl; et; i; iIntros "%"; subst; et.
    }
    iIntros (?????). des; subst.
    isteps_r. iforces_l. iFrame.
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
    iIntros. isteps_l. rewrite /lat_real /lat_real_body. unfold_iter_r. isteps_r.
    destruct fsp. destruct PHY as [P1 P2]. iPoseProof (P1 with "ASM") as "->".
    iApply isim_bind. iSplitL "".
    { iApply isim_eqit_tgt; et.
      iApply isim_refl; et; i; iIntros "%"; subst; et.
    }
    iIntros (????) "%"; des; subst.
    isteps_l. isteps_r.
    iforce_r. iFrame. iIntros "GRT".
    iforces_l. iFrame.
    isteps_l. isteps_r. istep; et.
  Qed.
End LAT. *)
