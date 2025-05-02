Require Import Common.
From iris.proofmode Require Export proofmode.
Require Import HMod ISim ISimInit.
Require Export CtxRefine CtxRefineFacts ClosedAdequacy MainAdequacy.

Module CFilter. Section CFilter.
  Context `{Σ: GRA}.

  Definition handler (fns: list string) : ∀ T, hmodE T -> (itree hmodE T + {X: Type & hmodE X * (X -> itree hmodE T)})%type :=
    λ T e, inr
      match e with
      | inr1 (inl1 (Call fn args)) =>
          if existsb (String.eqb fn) fns
          then existT _ (e, fun v => Ret v)
          else existT _ (subevent _ (Take False), fun v => Ret (False_rect _ v))
      | inr1 (inl1 (Spawn fn args)) =>
          if existsb (String.eqb fn) fns
          then existT _ (e, fun v => Ret v)
          else existT _ (subevent _ (Take False), fun v => Ret (False_rect _ v))
      | _ => existT _ (e, fun v => Ret v)
      end.

  Definition filter_itree fns (code: Any.t -> itree hmodE Any.t) :
    Any.t -> itree hmodE Any.t
    :=
    fun x => interpV (handler fns) (code x).

  Program Definition filter fns (m: HMod.t) : HMod.t :=
    {|HMod.scopes := m.(HMod.scopes)
    ; HMod.fnsems := List.map (map_snd (map_snd (filter_itree fns))) m.(HMod.fnsems)
    ; HMod.initial_st := m.(HMod.initial_st)
    |}.
  Next Obligation.
    ii. eapply (m.(HMod.well_scoped_fns) fn). unfold fnsems_scopes in *.
    rewrite !alist_find_map_snd in H. des_ifs; eauto.
  Qed.
  Next Obligation. ii. eapply (m.(HMod.well_scoped_init)). eauto. Qed.
  Next Obligation. ii. eapply (m.(HMod.nodup_fns)). eauto. Qed.

  (* Key theorems *)

  Lemma sim_filter_intro fns (m: HMod.t):
    HSim.t open (filter fns m) m emp%I IstEq.
  Proof.
    econs; s; et; try rewrite List.map_map fst_map_snd; try refl.
    ii. unfold filter in FIND. ss.
    rewrite alist_find_map_snd in FIND. unfold o_map in FIND.
    destruct (alist_find fn _); ss. inv FIND. destruct p as [sc bd].
    esplits; eauto.

    r. r. i. subst y. unfold HModTr.sandbox_body, filter_itree. s.
    generalize (bd x) as itr. clear bd x NODS NODD.
    combine_quant st_src; combine_quant st_tgt; combine_quant nths.
    eapply isim_coind.
    iIntros (g' [nths [st_tgt [st_ssrc itr]]] MON) "[IST #CIH]".
    
    assert (CASE:= case_itrH itr). des; subst; s.
    - rewrite interpV_ret. step; et.
    - rewrite interpV_tau. steps_l. steps_r. by_coind "CIH"; et.
    - rewrite interpV_bind interpV_trigger. s. rewrite subevent_subevent.
      steps_l. force_r. iSplitL "ASM"; et. steps_r. by_coind "CIH"; et.
    - rewrite interpV_bind interpV_trigger. s. rewrite subevent_subevent.
      steps_r. force_l. iSplitL "GRT"; et. steps_l. by_coind "CIH"; et.
    - rewrite interpV_bind interpV_trigger. s. destruct c; s.
      + des_ifs; depdes H0; rewrite subevent_subevent; cycle 1.
        { steps_l. ss. }
        call "IST"; et. steps_l. steps_r. by_coind "CIH"; et.
      + des_ifs; depdes H0; rewrite subevent_subevent; cycle 1.
        { steps_l. ss. }
        step; et. steps_l. steps_r. by_coind "CIH"; et.
      + rewrite subevent_subevent.
        yield "IST"; et. steps_l. steps_r. by_coind "CIH"; et.
    - rewrite interpV_bind interpV_trigger. s. rewrite subevent_subevent.
      destruct s.
      + ired. rewrite !SBRed.bind !SBRed.put. des_ifs; cycle 1.
        { steps_l. ss. }
        iApply isim_sput_src. iApply isim_sput_tgt.
        steps_l. by_coind "CIH"; et.
        iPoseProof "IST" as "%"; subst. et.
      + ired. rewrite !SBRed.bind !SBRed.get. des_ifs; cycle 1.
        { steps_l. ss. }
        iApply isim_sget_src. iApply isim_sget_tgt.
        steps_l. steps_r. iPoseProof "IST" as "%"; subst.
        by_coind "CIH"; et.
    - rewrite interpV_bind interpV_trigger. s. rewrite subevent_subevent.
      destruct e.
      + steps_r. force_l q. steps_l. by_coind "CIH"; et.
      + steps_l. force_r q. steps_r. by_coind "CIH"; et.
      + step. steps_l. steps_r. by_coind "CIH"; et.
  Qed.
  
  Lemma sim_filter_elim fns (m: HMod.t)
    (SUB: incl (List.map fst m.(HMod.fnsems)) fns)
    :
    HSim.t closed m (filter fns m) emp%I IstEq.
  Proof.
    econs; s; et; try rewrite List.map_map fst_map_snd; try refl.
    ii. unfold filter. s.
    rewrite alist_find_map_snd. unfold o_map. rewrite FIND.
    destruct fs as [sc bd]. esplits; eauto.

    r. r. i. subst y. unfold HModTr.sandbox_body, filter_itree. s.
    generalize (bd x) as itr. clear x NODS NODD.
    combine_quant st_src; combine_quant st_tgt; combine_quant nths.
    eapply isim_coind.
    iIntros (g' [nths [st_tgt [st_ssrc itr]]] MON) "[IST #CIH]".
    
    assert (CASE:= case_itrH itr). des; subst; s.
    - rewrite interpV_ret. step; et.
    - rewrite interpV_tau. steps_l. steps_r. by_coind "CIH"; et.
    - rewrite interpV_bind interpV_trigger. s. rewrite subevent_subevent.
      steps_l. force_r. iSplitL "ASM"; et. steps_r. by_coind "CIH"; et.
    - rewrite interpV_bind interpV_trigger. s. rewrite subevent_subevent.
      steps_r. force_l. iSplitL "GRT"; et. steps_l. by_coind "CIH"; et.
    - rewrite interpV_bind interpV_trigger. s. destruct c; s.
      + des_ifs; depdes H0; rewrite subevent_subevent.
        { call "IST"; et. steps_l. steps_r. by_coind "CIH"; et. }
        steps_l. iApply isim_call_none; et; cycle 1.
        { steps_l. ss. }
        rewrite alist_find_map_snd. unfold o_map.
        des_ifs. exfalso.
        eapply alist_find_some, in_map, SUB in Heq. ss.
        rewrite (proj2 (@existsb_exists _ _ _)) in Heq0; ss.
        eauto using String.eqb_refl.
      + des_ifs; depdes H0; rewrite subevent_subevent.
        { step. steps_l. steps_r. by_coind "CIH"; et. }
        steps_l. iApply isim_spawn_none; et; cycle 1.
        { steps_l. ss. }
        rewrite alist_find_map_snd. unfold o_map.
        des_ifs. exfalso.
        eapply alist_find_some, in_map, SUB in Heq. ss.
        rewrite (proj2 (@existsb_exists _ _ _)) in Heq0; ss.
        eauto using String.eqb_refl.
      + rewrite subevent_subevent.
        yield "IST"; et. steps_l. steps_r. by_coind "CIH"; et.
    - rewrite interpV_bind interpV_trigger. s. rewrite subevent_subevent.
      destruct s.
      + ired. rewrite !SBRed.bind !SBRed.put. des_ifs; cycle 1.
        { steps_l. ss. }
        iApply isim_sput_src. iApply isim_sput_tgt.
        steps_r. by_coind "CIH"; et.
        iPoseProof "IST" as "%"; subst. et.
      + ired. rewrite !SBRed.bind !SBRed.get. des_ifs; cycle 1.
        { steps_l. ss. }
        iApply isim_sget_src. iApply isim_sget_tgt.
        steps_r. iPoseProof "IST" as "%"; subst.
        by_coind "CIH"; et.
    - rewrite interpV_bind interpV_trigger. s. rewrite subevent_subevent.
      destruct e.
      + steps_r. force_l q. steps_l. by_coind "CIH"; et.
      + steps_l. force_r q. steps_r. by_coind "CIH"; et.
      + step. steps_l. steps_r. by_coind "CIH"; et.
  Qed.

  Corollary filter_intro fns (m: HMod.t):
    ctx_refines (filter fns m, emp)%I (m, emp)%I.
  Proof.
    eapply main_adequacy, sim_filter_intro.
  Qed.

  Corollary filter_elim fns (m: HMod.t)
    (SUB: incl (List.map fst m.(HMod.fnsems)) fns)
    :
    refines (m, emp)%I (filter fns m, emp)%I.
  Proof.
    eapply closed_adequacy2, sim_filter_elim. eauto.
  Qed.

End CFilter. End CFilter.

