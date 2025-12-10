From iris.proofmode Require Import proofmode.
Require Import Common ConcRA.
Require Import LMod Mod SMod Sp.
Require Import LSim LSimTactics MSim MSimFacts MSimCommon ISim TacticsCommon ITactics ISimNotations.

Tactic Notation "red_SB" :=
  lazymatch goal with
  | [ |- @SB.sandbox ?Σ ?msk ?R ?itr = _ ] =>
      lazymatch itr with
      | Ret _ =>
          eapply SBRed.ret
      | Tau _ =>
          eapply SBRed.tau
      | vis (Assume _) _ =>
          eapply SBRed.vis
      | vis (AssumeRes _) _ =>
          eapply SBRed.vis
      | vis (Guarantee _) _ =>
          eapply SBRed.vis
      | vis (Spawn _ _) _ =>
          eapply SBRed.vis
      | vis (Yield _) _ =>
          eapply SBRed.vis
      | vis GetTid _ =>
          eapply SBRed.vis
      | vis (Call _ _) _ =>
          eapply SBRed.vis
      | vis (SPut _ _) _ =>
          eapply SBRed.vis
      | vis (SGet _) _ =>
          eapply SBRed.vis
      | vis (Choose _) _ =>
          eapply SBRed.vis
      | vis (Take _) _ =>
          eapply SBRed.vis
      | vis (IO _ _) _ =>
          eapply SBRed.vis
      (* | assumeK _ _ =>
          eapply SBRed.assumeK *)
      (* | guaranteeK _ _ =>
          eapply SBRed.guaranteeK *)
      (* | unwrapUK _ _ =>
          eapply SBRed.unwrapUK *)
      (* | unwrapNK _ _ =>
          eapply SBRed.unwrapNK *)
      (* | RealUpdateK _ _ _ =>
          eapply SBRed.ruK *)
      | @ITree.bind _ _ _ _ _ =>
          eapply SBRed.bind
      | _ =>
          reflexivity
      end
  end.

Ltac _hnorm_itr :=
  lazymatch goal with
  | [ |- Ret _ = _ ] =>
      reflexivity
  | [ |- Tau _ = _ ] =>
      reflexivity
  | [ |- vis _ _ = _ ] =>
      reflexivity
  | [ |- @ITree.bind ?E ?T ?U ?itr ?ktr = _ ] =>
      etransitivity;
      [ let itr' := fresh "itr" in cong (fun (itr' : itree E T) => @ITree.bind E T U itr' ktr); _hnorm_itr | red_bind (do 1 _hnorm_itr) ]
  | [ |- @SB.sandbox ?Σ ?R ?img ?imports ?scopes ?itr = _ ] =>
      etransitivity;
      [ cong (@SB.sandbox Σ R img imports scopes); _hnorm_itr | red_SB ]
  | [ |- @SB.sandbox ?Σ ?msk ?R ?itr = _ ] =>
      etransitivity;
      [ cong (@SB.sandbox Σ msk R); _hnorm_itr | red_SB]
  | [ |- @SModTr.trans ?Γ ?Σ ?α ?β ?τ ?_S ?_I ?_crisG ?concG ?img ?sp ?R ?itr = _ ] =>
      etransitivity;
      [ cong (@SModTr.trans Γ Σ α β τ _S _I _crisG concG img sp R); _hnorm_itr
      | red_S (do 1 _hnorm_itr) ]
  | [ |- trigger _ = _ ] =>
      eapply trigger_vis
  | [ |- assume _ = _ ] =>
      eapply assume_assumeK
  | [ |- guarantee _ = _ ] =>
      eapply guarantee_guaranteeK
  | [ |- unwrapU _ = _ ] =>
      eapply unwrapU_unwrapUK
  | [ |- unwrapN _ = _ ] =>
      eapply unwrapN_unwrapNK
  | [ |- RealUpdate _ _ = _ ] =>
      eapply RealUpdate_RealUpdateK
  | [ |- SModTr.HoareCall _ _ _ = _ ] =>
      unfold SModTr.HoareCall;
      _hnorm_itr
  | [ |- fbody_trivial _ = _ ] =>
      unfold fbody_trivial;
      _hnorm_itr
  | [ |- cput _ _ = _ ] =>
      unfold cput;
      _hnorm_itr
  | [ |- cgetU _ = _ ] =>
      unfold cgetU;
      _hnorm_itr
  | [ |- cgetN _ = _ ] =>
      unfold cgetN;
      _hnorm_itr
  | [ |- cfunU _ _ = _ ] =>
      unfold cfunU;
      _hnorm_itr
  | [ |- cfunN _ _ = _ ] =>
      unfold cfunN;
      _hnorm_itr
  | [ |- ccallU _ _ = _ ] =>
      unfold ccallU;
      _hnorm_itr
  | [ |- ccallN _ _ = _ ] =>
      unfold ccallN;
      _hnorm_itr
  | [ |- triggerUB = _ ] =>
      unfold triggerUB;
      _hnorm_itr
  | [ |- triggerNB = _ ] =>
      unfold triggerNB;
      _hnorm_itr
  | [ |- ?itr = _ ] =>
      reflexivity
  end.

Ltac hnorm_itr :=
  etransitivity;
  [ _hnorm_itr
  | s;
    lazymatch goal with
    | [ |- Ret _ = _ ] =>
        reflexivity
    | [ |- Tau _ = _ ] =>
        reflexivity
    | [ |- vis _ _ = _ ] =>
        rewrite ?resum_to_subevent ?subevent_subevent;
        eapply vis_trigger
    | [ |- assumeK _ _ = _ ] =>
        eapply assumeK_assume
    | [ |- guaranteeK _ _ = _ ] =>
        eapply guaranteeK_guarantee
    | [ |- unwrapUK _ _ = _ ] =>
        eapply unwrapUK_unwrapU
    | [ |- unwrapNK _ _ = _ ] =>
        eapply unwrapNK_unwrapN
    | [ |- RealUpdateK _ _ _ = _ ] =>
        eapply RealUpdateK_RealUpdate
    (* | [ |- SBRed.putSB _ _ _ _ _ _ = _ ] =>
        eapply SBRed.putSB_SPut *)
    (* | [ |- SBRed.getSB _ _ _ _ _ = _ ] =>
        eapply SBRed.getSB_SGet *)
    (* | [ |- SBRed.callSB _ _ _ _ _ _ = _ ] =>
        eapply SBRed.callSB_Call *)
    (* | [ |- SBRed.spawnSB _ _ _ _ _ _ = _ ] =>
        eapply SBRed.spawnSB_Spawn *)
    | [ |- _ = _ ] =>
        reflexivity
    end
  ].
Ltac norm_l := replace_l; [s; hnorm_itr|].
Ltac norm_r := replace_r; [s; hnorm_itr|].

Tactic Notation "norm_l" "with" tactic(tac) :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  norm_l;
  tac;
  show_until marker.

Tactic Notation "norm_r" "with" tactic(tac) :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  norm_r;
  tac;
  show_until marker.

Tactic Notation "norm" "with" tactic(tac) :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  norm_l;
  norm_r;
  tac;
  show_until marker.

Ltac _iforce_r :=
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _)) ] =>
      iApply isim_take_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, trigger (Assume ?P) >>= _)) ] =>
      unfold_pre_post_term P; iApply isim_assume_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, assume _ >>= _)) ] =>
      iApply isim_asm_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, unwrapU _ >>= _)) ] =>
      iApply isim_unwrapU_tgt; iExists _
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, trigger (AssumeRes _) >>= _)) ] =>
      iApply isim_assume_res_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, RealUpdate ?P ?Q >>= _)) ] =>
      unfold_pre_post_term P; unfold_pre_post_term Q; iApply isim_ru_tgt_simple
  end.

Ltac iforce_r_core :=
  norm_r with do 1 _iforce_r; s.

Tactic Notation "iforce_r" :=
  iforce_r_core; try (iExists _).

Tactic Notation "iforce_r" uconstr(p) :=
  iforce_r_core; iExists p.

Ltac _iforce_l :=
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, trigger (Choose ?T) >>= _) _) ] =>
      iApply isim_choose_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _) _) ] =>
      unfold_pre_post_term P; iApply isim_guarantee_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, unwrapN _ >>= _) _) ] =>
      iApply isim_unwrapN_src; iExists _
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, guarantee _ >>= _) _) ] =>
      iApply isim_guar_src
  end.

Ltac iforce_l_core :=
  norm_l with do 1 _iforce_l; s.

Tactic Notation "iforce_l" :=
  iforce_l_core; [..|try iExists _].

Tactic Notation "iforce_l" uconstr(p) :=
  iforce_l_core; [..|iExists p].


Ltac istep_l := norm_l with do 1 try istep_l_core.
Ltac istep_r := norm_r with do 1 try istep_r_core.
Ltac istep := norm with do 1 _istep; s; des_pairs; s.

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
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.

  (* Reflexivity of the isim relation *)
  Lemma isim_refl r g ctx Ist fl_src fl_tgt msk
    ps pt st_src st_tgt {R} (it: itree crisE R)
    (* (EQGET : ∀ st_src st_tgt (k : key) (IN: In k.1)
                (NODS: List.NoDup (map fst st_src))
                (NODT: List.NoDup (map fst st_tgt)),
        Ist st_src st_tgt ⊢ ⌜alist_find k st_src = alist_find k st_tgt⌝)
    (EQSET : ∀ st_src st_tgt (k : key) v (IN: In k.1)
                (NODS: List.NoDup (map fst st_src))
                (NODT: List.NoDup (map fst st_tgt)),
        Ist st_src st_tgt ⊢ Ist (alist_upd k v st_src) (alist_upd k v st_tgt))  *)
    :
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
        rewrite resum_to_subevent ?subevent_subevent.
        specialize (Hset st_src st_tgt k v); destruct (msk _ _); [norm_l; norm_r|istep_l; ss].
        iApply isim_sput_src. iApply isim_sput_tgt.
        iby_coind CIH. iApply Hset; eauto.
      }
      { istep_l; istep_r.
        rewrite resum_to_subevent ?subevent_subevent.
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
      iIntros "[% [% [% [% [[-> ->] [ISTL [%Hscopesr ISTR]]]]]]]".
      eapply Hset in Htrue as [-> Hnin].
      iExists _, _, _, _; iFrame "ISTL ISTR".
      iPureIntro; split; eauto.
      rewrite ?insert_union_with_l // not_elem_of_dom_1 //; des; set_solver.
    - intros st_src0 st_tgt0 k Htrue.
      iIntros "[% [% [% [% [[-> ->] [ISTL [%Hscopesr ISTR]]]]]]]".
      eapply Hget in Htrue as [-> Hnin]; iPoseProof "ISTL" as "%Heq".
      iPureIntro; rewrite ?lookup_union_with Heq.
      rewrite (not_elem_of_dom_1 st_srcR); [|set_solver].
      rewrite (not_elem_of_dom_1 st_tgtR); [ss|set_solver].
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
      iIntros "[% [% [% [% [[-> ->] [[%Hscopesl ISTL] ISTR]]]]]]".
      eapply Hset in Htrue as [-> Hnin].
      iExists _, _, _, _; iFrame "ISTR ISTL".
      iPureIntro; split; eauto.
      rewrite ?insert_union_with_r // not_elem_of_dom_1 //; des; set_solver.
    - intros st_src0 st_tgt0 k Htrue.
      iIntros "[% [% [% [% [[-> ->] [[%Hscopesr ISTL] ISTR]]]]]]".
      eapply Hget in Htrue as [-> Hnin]; iPoseProof "ISTR" as "%Heq".
      iPureIntro; rewrite ?lookup_union_with Heq.
      rewrite (not_elem_of_dom_1 st_srcL); [|set_solver].
      rewrite (not_elem_of_dom_1 st_tgtL); [ss|set_solver].
  Qed.

  Lemma ISim_reflL
      (ctx : contextuality) (A B C : Mod.t) (init_cond : iProp Σ)
      (scopes : list string) (Ist : ist_type Σ) :
    (∀ fn, fn ∈ dom (Mod.fnsems A) →
      ISim.sim_fun ctx (Mod.add C A) (Mod.add C B) (IstProd IstEq (IstSB scopes Ist)) fn) →
    Mod.scopes A ⊆+ scopes →
    scopes ⊆+ Mod.scopes B →
    dom (Mod.fnsems A) ⊆ dom (Mod.fnsems B) →
    (init_cond ⊢
      (IstProd IstEq (IstSB scopes Ist) (Mod.initial_st (C ★ A)) (Mod.initial_st (C ★ B)))) →
    ISim.t ctx (Mod.add C A) (Mod.add C B) init_cond (IstProd IstEq (IstSB scopes Ist)).
  Proof using.
    intros Hsim Hscp Hscp2 Hfns Hval; econs; intros Hwf.
    { do 2 (etrans; first apply submseteq_skips_l; eauto). }
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
      intros Hwfsrc Hwftgt.
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
        intros x Hin%(elem_of_submseteq _ (Mod.scopes B)) HinC => //.
        inv Hwf; ss; apply NoDup_app in wf_scopes; des; naive_solver.
      }
      { intros ??? Hmsk; split; [iIntros "-> //"|].
        hexploit (Mod.well_scoped_fns C); rewrite map_Forall_lookup.
        intros Hsi; hexploit (Hsi fn (fmsksrc, fbdysrc)).
        { clarify; rewrite lookup_omap Hc //. }
        intros Htrue; apply Htrue in Hmsk.
        enough (scopes ## Mod.scopes C); [set_solver|].
        intros x Hin%(elem_of_submseteq _ (Mod.scopes B)) HinC => //.
        inv Hwf; ss; apply NoDup_app in wf_scopes; des; naive_solver.
      }
    }
  Qed.

  Lemma ISim_reflR
      (ctx : contextuality) (A B C : Mod.t) (init_cond : iProp Σ)
      (scopes : list string) (Ist : ist_type Σ) :
    (∀ fn, fn ∈ dom (Mod.fnsems A) →
      ISim.sim_fun ctx (A ★ C) (B ★ C) (IstProd IstEq (IstSB scopes Ist)) fn) →
    Mod.scopes A ⊆+ scopes →
    scopes ⊆+ Mod.scopes B →
    dom (Mod.fnsems A) ⊆ dom (Mod.fnsems B) →
    (init_cond ⊢
      (IstProd IstEq (IstSB scopes Ist) (Mod.initial_st (A ★ C)) (Mod.initial_st (B ★ C)))) →
    ISim.t ctx (A ★ C) (B ★ C) init_cond (IstProd IstEq (IstSB scopes Ist)).
  Proof using.
    intros Hsim Hscp Hscp2 Hfns Hval; econs; intros Hwf.
    { do 2 (etrans; first apply submseteq_skips_r; eauto). }
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
      intros Hwfsrc Hwftgt.
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
        intros x Hin%(elem_of_submseteq _ (Mod.scopes B)) HinC => //.
        inv Hwf; ss; apply NoDup_app in wf_scopes; des; naive_solver.
      }
      { intros ??? Hmsk; split; [iIntros "-> //"|].
        hexploit (Mod.well_scoped_fns C); rewrite map_Forall_lookup.
        intros Hsi; hexploit (Hsi fn (fmsksrc, fbdysrc)).
        { clarify; rewrite lookup_omap Hc //. }
        intros Htrue; apply Htrue in Hmsk.
        enough (scopes ## Mod.scopes C); [set_solver|].
        intros x Hin%(elem_of_submseteq _ (Mod.scopes B)) HinC => //.
        inv Hwf; ss; apply NoDup_app in wf_scopes; des; naive_solver.
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
      intros Hnone; rewrite map_Forall_lookup in wf_fns; eapply wf_fns in Hnone; ss.
    }
    { apply submseteq_Permutation in Hscp as [? Hscp]; eauto.
      rewrite Hscp NoDup_app in wf_scopes; des; done.
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

  Lemma ISim_adequacy (ms mt : Mod.t) (rs rt : Σ) (IC : iProp Σ) Ist
      (SUB : Own rs ⊢ |==> Own rt ∗ (IC ∗ winv (∅,∅)))
      (WF : ✓ rs)
      (WFS : Mod.wf ms)
      (WFT : Mod.wf mt)
      (SIM : ISim.t closed ms mt IC Ist) :
    lsim_mod (Mod.to_lmod ms rs) (Mod.to_lmod mt rt).
  Proof using.
    dup SIM. dup WFS. dup WFT. destruct SIM0, WFS0, WFT0.
    econs; ss.
    - ii; subst; eauto.
    (* - instantiate (1:= interp_inv (λ x y, winv (∅, ∅) ∗ Ist x y)%I).
      inv WF0. econs; eauto.
      rewrite MR. iIntros ">[I H]". iFrame. iModIntro.
      iApply sim_mon; eauto. *)
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
      (* rewrite !alist_find_map_snd in FIND.
      destruct (alist_find _ _) eqn: FINDSRC; ss. inv FIND.
      exploit (sim_fnsems WFT None); et. i; des.
      rewrite !alist_find_map_snd x0. s. esplits; et.
      destruct f as [[[img msk] scp] bd].
      destruct ft as [[[img0 msk0] scp0] bd0].
      i. exists ε, ε. *)

      specialize (Hsim arg (Mod.initial_st ms) (Mod.initial_st mt)).
      rewrite /ModTr.trans_fnsem /SB.sandbox_body.
      eapply lsim_mon_rr.
      { instantiate (1:= interp_inv IstTrue). et. }
      (* assert (NDS:= ms.(Mod.nodup_init) wf_scopes).
      assert (NDT:= mt.(Mod.nodup_init) wf_scopes0). *)

      exploit Own_bupd_split; et. i; des.
      exploit Own_split; i; des; et.
      { eapply Own_wand_valid, WF. rewrite x0. iIntros ">[_ ?]". et. }

      eapply msim_adequacy; et.
      + rewrite /ModTr.trans_fnsem; f_equal.
        Search fmap omap. instantiate (1:=List.map (map_snd SB.sandbox_body) (Mod.fnsems ms)).
        rewrite map_map fst_map_snd. et.
      + instantiate (1:=List.map (map_snd SB.sandbox_body) (Mod.fnsems mt)).
        rewrite map_map fst_map_snd. et.
      + rewrite map_map. f_equal. extensionalities. destruct H. et.
      + rewrite map_map. f_equal. extensionalities. destruct H. et.
      + eapply le_mine_refl. et.
      + ginit. eapply isim_init.
        * iIntros "P". iApply isim_mono; cycle 1; i.
          { iApply isim_ist_frame; et. }
          { instantiate (1:= (ist_with_eq IstTrue)). s.
            iIntros "[? [? ?]]". iFrame. }
        * instantiate (1:= a0 ⋅ a3). rewrite !Own_op x6 x7.
          iIntros "[H I]".
          iPoseProof (winv_split_empty with "[I]") as "[I I']"; et; iFrame.
          iApply (x1 with "[H]"); et. iSplit; et.
        * eauto using iunlift_ibot.
        * eauto using iunlift_ibot.
      + rewrite x2 x3 x5 !Own_op -Own_unit. iIntros ">[? [? ?]]"; iFrame. et.
    - move: FIND; rewrite ?alist_find_map_snd /o_map; intros FIND.
      clear sim_initial. des_ifs; cycle 1.
      { eapply alist_find_fst_some, sub_perm_incl in Heq0; [|apply sim_match]; et.
        eapply alist_find_fst_in in Heq0. des. rewrite Heq0 in Heq. ss.
      }
      esplits; eauto.
      exploit sim_fnsems; eauto using alist_find_fst_some, Mod.wf.
      ii. des; subst.
      rewrite Heq in x0. inv x0. inv SIMMRS.
      eapply msim_adequacy; eauto; cycle 4.
      { apply le_mine_refl. ii; eauto. }
      { ginit; cycle 2; i.
        eapply gpaco8_mon with (r := iunlift ibot) (rg:= iunlift ibot); eauto using iunlift_ibot.
        eapply isim_init; eauto.
        iIntros "H". iApply isim_upd. iMod (MR with "H") as "[I H]".
        iPoseProof (x1 with "[H]") as "SIM"; cycle 2; s; et.
        iPoseProof (winv_split_empty with "[I]") as "[I I']"; et.
        iPoseProof ("SIM" with "I") as "SIM".
        iModIntro. iApply isim_mono; cycle 1; i.
        { iApply isim_ist_frame; et. iFrame. }
        { s. iIntros "[? [? ?]]". iFrame. }
      }
      { rewrite List.map_map.
        eapply eq_ind; [apply wf_fns|].
        f_equal. extensionalities. destruct H; eauto.
      }
      { rewrite List.map_map.
        eapply eq_ind; [apply wf_fns0|].
        f_equal. extensionalities. destruct H; eauto.
      }
      { rewrite List.map_map. f_equal. extensionalities. destruct H. eauto. }
      { rewrite List.map_map. f_equal. extensionalities. destruct H. eauto. }
  Unshelve. eapply option_Dec, string_Dec.
  Qed.
End ISIM_ADEQUACY.

(* Section LAT.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I, !concG}.

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
    iDestruct "ASM" as "[P %]"; subst.
    iforces_r. iFrame. isteps_r.
    iApply isim_bind. iSplitL "".
    { iApply isim_eqit_tgt; et.
      iApply isim_refl; et; i; iIntros "%"; subst; et.
    }
    iIntros (?????). des; subst.
    isteps_r. iforces_l. iFrame.
    iSplit; et. istep. et.
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
    iDestruct "ASM" as "[P %]"; subst.
    iApply isim_bind. iSplitL "".
    { iApply isim_eqit_tgt; et.
      iApply isim_refl; et; i; iIntros "%"; subst; et.
    }
    iIntros (????) "%"; des; subst.
    isteps_l. isteps_r.
    iforce_r. iFrame. iIntros "GRT".
    iforces_l. iFrame. iSplit; et.
    isteps_l. isteps_r. istep; et.
  Qed.
End LAT. *)
