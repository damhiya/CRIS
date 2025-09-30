Require Import CRIS.
Require Import LMod.
Require Import GSim GSimFacts GSimTactics.
Require Import SchHeader SchI SchA.
From CRIS.helping Require Import Header HelpingOn HelpingOff HelpingAux.

Ltac unfold_trans :=
  rewrite /ModTr.trans_ktree /SB.sandbox_body /SB.sandbox
    /ModTr.trans /SModTr.trans_ktree /SModTr.trans /=.

Section Helping.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !newschG}.
  (* sp, module name for the helping module *)
  Context (sp : sp_type) (mn : string).
  Context {jobID retID : Type} (jobs : jobID → itree Helping.pureE retID).
  Context (msk : string → bool). (* mask for the user module *)

  Definition mod_on :=  (HelpingOn.t mn jobs sp)  ★ (CFilter.filter msk SchI.t).
  Definition mod_off := (HelpingOff.t mn jobs sp) ★ (CFilter.filter msk SchI.t).

  Lemma get_tid_run_neq : SchHdr.get_tid ≠ Helping.run mn.
  Proof.
    rewrite /SchHdr.get_tid /Helping.run; destruct (decide (String.length mn = 7)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.get_tid" = 11) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (3 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Lemma get_tid_help_neq : SchHdr.get_tid ≠ Helping.help mn.
  Proof.
    rewrite /SchHdr.get_tid /Helping.help; destruct (decide (String.length mn = 6)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.get_tid" = 11) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (3 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Lemma yield_run_neq : SchHdr.yield ≠ Helping.run mn.
  Proof.
    rewrite /SchHdr.yield /Helping.run; destruct (decide (String.length mn = 5)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.yield" = 9) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (3 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Lemma yield_help_neq : SchHdr.yield ≠ Helping.help mn.
  Proof.
    rewrite /SchHdr.yield /Helping.help; destruct (decide (String.length mn = 4)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.yield" = 9) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (0 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Lemma join_run_neq : SchHdr.join ≠ Helping.run mn.
  Proof.
    rewrite /SchHdr.join /Helping.run; destruct (decide (String.length mn = 4)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.join" = 8) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (1 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Lemma join_help_neq : SchHdr.join ≠ Helping.help mn.
  Proof.
    rewrite /SchHdr.join /Helping.help; destruct (decide (String.length mn = 3)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.join" = 8) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (1 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Notation prog_s ctx rs := (LMod.prog
    (Mod.to_lmod
      ((SMod.to_mod sp (HelpingOff.Mod mn jobs)
      ★ CFilter.filter msk (SMod.to_mod sp_none SchI.smod)) ★ ctx) rs)).
  Notation prog_t ctx rs := (LMod.prog
    (Mod.to_lmod
      ((SMod.to_mod sp (HelpingOn.Mod mn jobs sp)
      ★ CFilter.filter msk (SMod.to_mod sp_none SchI.smod)) ★ ctx) rs)).

  Definition run_s : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(true, wmask_all, HelpingOff.scopes mn)
      (tau;; ⇓smod(false, sp) (HelpingOff.run jobs x))).
  Definition run_t : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(true, wmask_all, HelpingOn.scopes mn)
      (tau;; ⇓smod(false, sp) (HelpingOn.run mn jobs x))).

  Definition help_s : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(true, wmask_all, HelpingOff.scopes mn)
      (tau;; ⇓smod(false, sp) (HelpingOff.help x))).
  Definition help_t : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(true, wmask_all, HelpingOn.scopes mn)
      (tau;; ⇓smod(false, sp) (HelpingOn.help mn jobs sp x))).

  Definition yield : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes)
      (tau;; ⇓smod(false, sp_none) (cfunU SchI.yield x))).
  Definition inner_spawn : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes)
      (tau;; ⇓smod(false, sp_none) (cfunU SchI.inner_spawn x))).
  Definition spawn : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes)
      (tau;; ⇓smod(false, sp_none) (cfunU SchI.spawn x))).
  Definition join : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes)
      (tau;; ⇓smod(false, sp_none) (cfunU SchI.join x))).
  Definition get_tid : Any.t → itree lmodE Any.t := λ x,
    ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes)
      (tau;; ⇓smod(false, sp_none) (cfunU SchI.get_tid x))).

  Lemma no_help_prog fn ctx rs :
    fn ≠ Helping.run mn →
    fn ≠ Helping.help mn →
    prog_s ctx rs fn = prog_t ctx rs fn.
  Proof.
    intros ??.
    rewrite /LMod.prog /=;
    repeat (
      match goal with
      | |- context [dec ?a ?b] => destruct (dec a b); ss; clarify
      end); esplits; eauto.
  Qed.

  Lemma prog_fn fn ctx rs :
    Mod.wf ((HelpingOn.t mn jobs sp ★ CFilter.filter msk SchI.t) ★ ctx) →
    (fn = Helping.run mn ∧ prog_s ctx rs fn = Some run_s ∧ prog_t ctx rs fn = Some run_t) ∨
    (fn = Helping.help mn ∧ prog_s ctx rs fn = Some help_s ∧ prog_t ctx rs fn = Some help_t) ∨
    prog_s ctx rs fn = prog_t ctx rs fn ∧
    ((fn = SchHdr.yield ∧ prog_s ctx rs fn = Some yield) ∨
     (fn = SchHdr.join ∧ prog_s ctx rs fn = Some join) ∨
     (fn = SchHdr._spawn ∧ prog_s ctx rs fn = Some inner_spawn) ∨
     (fn = SchHdr.spawn ∧ prog_s ctx rs fn = Some spawn) ∨
     (fn = SchHdr.get_tid ∧ prog_s ctx rs fn = Some get_tid) ∨
     (Some fn ∉ List.map fst (Mod.fnsems ((HelpingOn.t mn jobs sp) ★ (CFilter.filter msk SchI.t))) ∧
     (prog_s ctx rs fn = None ∨
     ∃ itr_ctx img1 msk1 scp1, (prog_s ctx rs fn =
      Some (λ x, ⇓cris (⇓sb(img1, msk1, scp1) (itr_ctx x))) ∧
      (scp1 ## (SchI.scopes ++ HelpingOff.scopes mn)))))).
  Proof.
    intros WF.
    destruct (decide (fn = Helping.run mn)).
    { subst; left.
      rewrite /LMod.prog /= /run_s /run_t; destruct (dec _ _); last clarify; ss.
    }
    destruct (decide (fn = Helping.help mn)).
    { subst; right; left.
      rewrite /LMod.prog /=; destruct (dec _ _) as [e|e]; clarify; ss.
      { rewrite /Helping.help /Helping.run in e; inv e. }
      destruct (dec _ _); clarify; ss.
    }
    right; right. split; first apply no_help_prog; eauto.
    destruct (decide (fn = SchHdr.yield)).
    { left; subst; split; ss.
      rewrite /LMod.prog /=; destruct (dec _ _) as [e|e]; ss; eauto; clarify; ss.
      rewrite /LMod.prog /=; destruct (dec _ _) as [?|?]; ss; eauto; clarify; ss.
    }
    right.
    destruct (decide (fn = SchHdr.join)).
    { left; subst; split; ss.
      rewrite /LMod.prog /=; destruct (dec _ _) as [?|?]; ss; eauto; clarify; ss.
      rewrite /LMod.prog /=; destruct (dec _ _) as [?|?]; ss; eauto; clarify; ss.
    }
    right.
    destruct (decide (fn = SchHdr._spawn)).
    { left; subst; split; ss.
      rewrite /LMod.prog /=; destruct (dec _ _) as [?|?]; ss; eauto; clarify; ss.
      rewrite /LMod.prog /=; destruct (dec _ _) as [?|?]; ss; eauto; clarify; ss.
    }
    right.
    destruct (decide (fn = SchHdr.spawn)).
    { left; subst; split; ss.
      rewrite /LMod.prog /=; destruct (dec _ _) as [?|?]; ss; eauto; clarify; ss.
      rewrite /LMod.prog /=; destruct (dec _ _) as [?|?]; ss; eauto; clarify; ss.
    }
    right.
    destruct (decide (fn = SchHdr.get_tid)).
    { left; subst; split; ss.
      rewrite /LMod.prog /=; destruct (dec _ _) as [?|?]; ss; eauto; clarify; ss.
      rewrite /LMod.prog /=; destruct (dec _ _) as [e|e]; ss; eauto; clarify; ss.
    }
    right.
    rewrite /LMod.prog /=.
    repeat (destruct (dec _ _) as [e|e]; ss; [inv e; by clarify|clear e]).
    rewrite /HelpingOn.t /SchI.t; unseal CRIS; ss.
    split.
    { set_solver. }
    rewrite alist_find_map_snd.
    destruct (alist_find (Some fn) (Mod.fnsems ctx)) as [[[[img1 msk1] scp1] itr_fn]|] eqn : Hfn.
    { right; ss. esplits; eauto; ss.
      hexploit (Mod.well_scoped_fns ctx (Some fn)); ss.
      rewrite /fnsems_scopes Hfn /=; intros Hin.
      apply elem_of_disjoint; intros x Hinctx%elem_of_list_In%Hin%elem_of_list_In Hinsch.
      hexploit (Mod.wf_scopes); eauto; rewrite /Mod.scopes /=.
      intros Hnodup; eapply (NoDup_app_disjoint _ _ Hnodup x); eauto.
      { eapply elem_of_list_In. rewrite /Mod.scopes /SchI.t /HelpingOn.t; unseal CRIS; ss.
        revert Hinsch; rewrite /HelpingOn.scopes /SchI.scopes; ss.
        set_solver.
      }
      { eapply elem_of_list_In, Hinctx; eauto. }
    }
    left; ss.
  Qed.

  Lemma prog_fn_ctx fn ctx rs :
    Mod.wf ((HelpingOn.t mn jobs sp ★ CFilter.filter msk SchI.t) ★ ctx) →
    (Some fn ∉ List.map fst (Mod.fnsems ((HelpingOn.t mn jobs sp) ★ (CFilter.filter msk SchI.t)))) →
    (prog_s ctx rs fn = None ∨
     ∃ itr_ctx img1 msk1 scp1,
      prog_t ctx rs fn = prog_s ctx rs fn ∧
      prog_s ctx rs fn =
        Some (λ x, ⇓cris (⇓sb(img1, msk1, scp1) (itr_ctx x))) ∧
        (scp1 ## (SchI.scopes ++ HelpingOff.scopes mn))).
  Proof.
    intros ? NIN; hexploit (prog_fn fn ctx rs); eauto; intros CASE.
    revert NIN; rewrite /HelpingOn.t /SchI.t; unseal CRIS; ss.
    destruct CASE as [[-> ?]|CASE]; first set_solver.
    destruct CASE as [[-> ?]|[-> CASE]]; first set_solver.
    destruct CASE as [[-> ?]|CASE]; first set_solver.
    destruct CASE as [[-> ?]|CASE]; first set_solver.
    destruct CASE as [[-> ?]|CASE]; first set_solver.
    destruct CASE as [[-> ?]|CASE]; first set_solver.
    destruct CASE as [[-> ?]|CASE]; first set_solver.
    i; des; eauto. right; esplits; eauto.
  Qed.

  Lemma prog_s_prog_t fn ctx rs itr :
    Mod.wf ((HelpingOn.t mn jobs sp ★ CFilter.filter msk SchI.t) ★ ctx) →
    prog_s ctx rs fn = Some itr →
    (prog_t ctx rs fn = Some itr ∨
     (fn = Helping.run mn ∧ itr = run_s ∧ prog_t ctx rs fn = Some run_t) ∨
     (fn = Helping.help mn ∧ itr = help_s ∧ prog_t ctx rs fn = Some help_t)).
  Proof.
    intros ? Hs; hexploit (prog_fn fn ctx rs); eauto.
    i; des; clarify; eauto; left; rewrite -H4 //.
  Qed.

  Lemma yield_unfold :
    @Sch.yield crisE _ _ =
    tau;; b <- trigger (Choose (option bool));;
    match b with
    | None => Ret tt
    | Some false => Sch.yield
    | Some true => trigger (Call SchHdr.yield tt↑);;; Sch.yield
    end.
  Proof.
    rewrite {1}/Sch.yield; unseal SCH; rewrite unfold_iterC.
    repeat f_equal. ired. repeat f_equal. extensionalities b. destruct b as [[|]|]; ss.
    { ired. f_equal. extensionalities x. rewrite /Sch.yield; unseal SCH; ss. }
    { ired. rewrite /Sch.yield; unseal SCH; ss. }
    { ired. done. }
  Qed.

  Definition reqmap_rel
      (tl : list (itree lmodE Any.t * itree lmodE Any.t * option (nat * (option retID * jobID))))
      (reqmap : gmap nat (option retID * jobID)) : Prop :=
    NoDup (omap id tl.*2).*1 ∧
    (∀ stid rid jid bo,
      (tl.*2 !! stid = Some (Some (rid, (bo, jid))) → reqmap !! rid = Some (bo, jid))) ∧
    (∀ rid jid, reqmap !! rid = Some (None, jid) →
      ∃ stid, tl.*2 !! stid = Some (Some (rid, (None, jid)))).

  Lemma reqmap_rel_id stid es0 es1 r tl reqmap :
    tl !! stid = Some (es0, r) →
    reqmap_rel tl reqmap →
    reqmap_rel (<[stid:=(es1, r)]> tl) reqmap.
  Proof.
    intros [tl1 [tl2 [-> Hlen]]]%elem_of_list_split_length.
    rewrite -(Nat.add_0_r stid); subst stid; rewrite /reqmap_rel insert_app_r ?fmap_app; cbn.
    rewrite ?omap_app ?fmap_app; cbn; destruct r; eauto.
  Qed.

  Lemma reqmap_rel_Some tl reqmap stid rid b jid es :
    tl !! stid = Some (es, Some (rid, (b, jid))) →
    reqmap_rel tl reqmap →
    reqmap !! rid = Some (b, jid).
  Proof.
    rewrite /reqmap_rel; intros Hin [Hnodup [Hrel1 Hrel2]].
    apply (Hrel1 stid rid jid b). rewrite list_lookup_fmap Hin; eauto.
  Qed.

  Lemma reqmap_rel_Some_2 tl reqmap (i_s i_t : itree lmodE Any.t) rid jid :
    reqmap_rel tl reqmap →
    reqmap !! rid = Some (None, jid) →
    ∃ stid i_s i_t, tl !! stid = Some (i_s, i_t, Some (rid, (None, jid))).
  Proof.
    rewrite /reqmap_rel; intros [? [? Hsome]] [stid Hstid]%Hsome; exists stid.
    apply list_lookup_fmap_inv in Hstid as [[[? ?] [[? [? ?]]|]] [? ?]]; ss.
    clarify; esplits; eauto.
  Qed.

  Lemma reqmap_rel_delete_true tl stid rid jid es0 es1 reqmap (ret : retID) :
    tl !! stid = Some (es0, Some (rid, (None, jid))) →
    reqmap_rel tl reqmap →
    reqmap_rel (<[stid := (es1, None)]> tl) (<[rid := (Some ret, jid)]> reqmap).
  Proof.
    intros Hin [Hnodup [Hrel1 Hrel2]]; eapply lookup_lt_Some in Hin as Hlen; split.
    { revert Hin; intros [tl1 [tl2 [-> ?]]]%elem_of_list_split_length.
      rewrite -(Nat.add_0_r stid); subst stid; rewrite /reqmap_rel insert_app_r ?fmap_app; cbn.
      rewrite ?omap_app ?fmap_app; cbn.
      revert Hnodup; rewrite cons_app Permutation_app_swap_app; cbn.
      rewrite ?fmap_app ?omap_app ?fmap_app. apply NoDup_cons.
    }
    split.
    { intros stid1 rid1 jid1 b1 Hstid1.
      rewrite list_lookup_fmap in Hstid1.
      destruct (decide (stid = stid1)); subst.
      { rewrite list_lookup_insert // in Hstid1. }
      rewrite list_lookup_insert_ne // in Hstid1.
      rewrite lookup_insert_ne; [eapply Hrel1; rewrite list_lookup_fmap; eauto|].
      ii; clarify.
      revert Hin; intros [tl1 [tl2 [-> ->]]]%elem_of_list_split_length.
      revert Hnodup; rewrite cons_app Permutation_app_swap_app; cbn.
      intros Hnodup; apply NoDup_cons in Hnodup; apply Hnodup.
      apply elem_of_list_fmap; exists (rid1, (b1, jid1)); split; ss.
      apply elem_of_list_omap; exists (Some (rid1, (b1, jid1))); split; ss.
      rewrite -list_lookup_fmap in Hstid1.
      apply list_lookup_fmap_inv in Hstid1 as [[[? ?] ?] [? Hstid]]; ss; clarify.
      apply lookup_app_Some in Hstid; des; ss.
      { rewrite fmap_app; apply elem_of_app; left.
        apply elem_of_list_fmap; esplits; [|apply elem_of_list_lookup]; eauto; ss.
      }
      rewrite lookup_cons in Hstid0; des_ifs; first lia.
      rewrite fmap_app; apply elem_of_app; right.
      apply elem_of_list_fmap; esplits; [|apply elem_of_list_lookup]; eauto; ss.
    }
    intros rid1 jid1; destruct (decide (rid1 = rid)).
    { subst; rewrite lookup_insert; i; clarify. }
    rewrite lookup_insert_ne //; intros [stid1 Hstid1]%Hrel2.
    exists stid1; rewrite list_fmap_insert /= list_lookup_insert_ne //.
    ii; clarify.
    rewrite list_lookup_fmap Hin /= in Hstid1; clarify.
  Qed.

  Lemma reqmap_rel_delete_true_2 tl stid rid jid es0 es1 reqmap ret :
    tl !! stid = Some (es0, Some (rid, (None, jid))) →
    reqmap_rel tl reqmap →
    reqmap_rel (<[stid := (es1, Some (rid, (Some ret, jid)))]> tl) (<[rid := (Some ret, jid)]> reqmap).
  Proof.
    intros Hin [Hnodup [Hrel1 Hrel2]]; eapply lookup_lt_Some in Hin as Hlen; split.
    { revert Hin; intros [tl1 [tl2 [-> ?]]]%elem_of_list_split_length.
      rewrite -(Nat.add_0_r stid); subst stid; rewrite /reqmap_rel insert_app_r ?fmap_app; cbn.
      revert Hnodup; rewrite ?fmap_app ?omap_app ?fmap_app //; cbn.
    }
    split.
    { intros stid1 rid1 jid1 b1 Hstid1.
      rewrite list_lookup_fmap in Hstid1.
      destruct (decide (stid = stid1)); subst.
      { rewrite list_lookup_insert //= in Hstid1; clarify. rewrite lookup_insert //. }
      rewrite list_lookup_insert_ne // in Hstid1.
      rewrite lookup_insert_ne; [eapply Hrel1; rewrite list_lookup_fmap; eauto|].
      ii; clarify.
      revert Hin; intros [tl1 [tl2 [-> ->]]]%elem_of_list_split_length.
      revert Hnodup; rewrite cons_app Permutation_app_swap_app; cbn.
      intros Hnodup; apply NoDup_cons in Hnodup; apply Hnodup.
      apply elem_of_list_fmap; exists (rid1, (b1, jid1)); split; ss.
      apply elem_of_list_omap; exists (Some (rid1, (b1, jid1))); split; ss.
      rewrite -list_lookup_fmap in Hstid1.
      apply list_lookup_fmap_inv in Hstid1 as [[[? ?] ?] [? Hstid]]; ss; clarify.
      apply lookup_app_Some in Hstid; des; ss.
      { rewrite fmap_app; apply elem_of_app; left.
        apply elem_of_list_fmap; esplits; [|apply elem_of_list_lookup]; eauto; ss.
      }
      rewrite lookup_cons in Hstid0; des_ifs; first lia.
      rewrite fmap_app; apply elem_of_app; right.
      apply elem_of_list_fmap; esplits; [|apply elem_of_list_lookup]; eauto; ss.
    }
    intros rid1 jid1; destruct (decide (rid1 = rid)).
    { subst; rewrite lookup_insert; i; clarify. }
    rewrite lookup_insert_ne //; intros [stid1 Hstid1]%Hrel2.
    exists stid1; rewrite list_fmap_insert /= list_lookup_insert_ne //.
    ii; clarify.
    rewrite list_lookup_fmap Hin /= in Hstid1; clarify.
  Qed.

  Lemma reqmap_rel_delete_false tl stid rid jid es0 es1 reqmap ret :
    tl !! stid = Some (es0, Some (rid, (Some ret, jid))) →
    reqmap_rel tl reqmap →
    reqmap_rel (<[stid := (es1, None)]> tl) (reqmap).
  Proof.
    intros Hin [Hnodup [Hrel1 Hrel2]].
    split.
    { revert Hin; intros [tl1 [tl2 [-> Hlen]]]%elem_of_list_split_length.
      rewrite -(Nat.add_0_r stid); subst stid; rewrite /reqmap_rel insert_app_r ?fmap_app; cbn.
      rewrite ?omap_app ?fmap_app; cbn.
      revert Hnodup; rewrite cons_app Permutation_app_swap_app; cbn.
      rewrite ?fmap_app ?omap_app fmap_app. apply NoDup_cons.
    }
    split.
    { intros stid' ??? Hstid'; eapply (Hrel1 stid'); eauto.
      rewrite list_fmap_insert /= in Hstid'.
      apply lookup_lt_Some in Hstid' as Hlen'. rewrite length_insert in Hlen'.
      destruct (decide (stid = stid')); subst.
      { rewrite list_lookup_insert // in Hstid'; ss. }
      rewrite list_lookup_insert_ne // in Hstid'.
    }
    intros ?? [stid' Hlookup]%Hrel2; exists stid'.
    rewrite list_fmap_insert /= list_lookup_insert_ne ?Hlookup //.
    ii; clarify.
    rewrite list_lookup_fmap Hin //= in Hlookup.
  Qed.

  Lemma reqmap_rel_insert_false tl reqmap rid jid ret :
    rid ∉ (dom reqmap) →
    reqmap_rel tl reqmap →
    reqmap_rel tl (<[rid:=(Some ret, jid)]> reqmap).
  Proof.
    intros Hrid [? [Hrel1 Hrel2]]; split; first done.
    split.
    { intros ???? Hstid%Hrel1.
      rewrite lookup_insert_ne //.
      ii; clarify; apply elem_of_dom_2 in Hstid; eauto.
    }
    intros rid1.
    destruct (decide (rid = rid1)); subst; [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
    ii; clarify.
  Qed.

  Lemma reqmap_rel_insert_true tl reqmap stid es0 es1 rid jid :
    rid ∉ (dom reqmap) →
    tl !! stid = Some (es0, None) →
    reqmap_rel tl reqmap →
    reqmap_rel (<[stid:=(es1, Some (rid, (None, jid)))]> tl) (<[rid:=(None, jid)]> reqmap).
  Proof.
    intros Hrid Hin [Hnodup [Hrel1 Hrel2]]; eapply lookup_lt_Some in Hin as Hlen; split.
    { rewrite insert_take_drop //.
      rewrite ?fmap_app ?omap_app ?fmap_app; cbn.
      rewrite cons_app Permutation_app_swap_app.
      eapply take_drop_middle in Hin as Hmid; rewrite -Hmid in Hnodup; clear Hmid.
      revert Hnodup; rewrite ?fmap_app ?omap_app fmap_app; cbn.
      intros ?; apply NoDup_cons; split; eauto.
      rewrite -fmap_app -omap_app -fmap_app.
      intros [[? [? ?]] [? Hrid2]]%elem_of_list_fmap; ss; clarify.
      apply elem_of_list_omap in Hrid2 as [[[? [? ?]] |] [Hrid2 ?]]; ss; clarify.
      apply elem_of_list_fmap in Hrid2 as [[? [[? [? ?]] |]] [? Hrid2]]; ss; clarify.
      apply Hrid, elem_of_dom.
      assert (Hlem : (p, Some (n0, (o0, j0))) ∈ tl).
      { eapply take_drop_middle in Hin as Hmid; rewrite -Hmid; clear Hmid. set_solver. }
      apply elem_of_list_lookup in Hlem as [i Hlem].
      hexploit (Hrel1 i); cycle 1.
      { intros ->; ss. }
      rewrite list_lookup_fmap Hlem //.
    }
    split.
    { intros stid1 ? ? ?; destruct (decide (stid1 = stid)); subst.
      { rewrite list_lookup_fmap list_lookup_insert /=; i; clarify; rewrite lookup_insert //. }
      rewrite list_fmap_insert list_lookup_insert_ne //; intros Hcont%Hrel1.
      rewrite lookup_insert_ne //.
      ii; clarify.
      apply Hrid, elem_of_dom; eauto.
    }
    intros rid1.
    destruct (decide (rid = rid1)); subst; [rewrite lookup_insert|rewrite lookup_insert_ne]; eauto.
    { ii; clarify. exists stid; rewrite list_fmap_insert list_lookup_insert // length_fmap //. }
    intros ? [??]%Hrel2; exists x; rewrite list_fmap_insert list_lookup_insert_ne //.
    ii; clarify.
    rewrite list_lookup_fmap Hin /= in H1; clarify.
  Qed.

  Lemma reqmap_rel_append tl reqmap es :
    reqmap_rel tl reqmap →
    reqmap_rel (tl ++ [(es, None)]) reqmap.
  Proof.
    rewrite /reqmap_rel ?fmap_app ?omap_app ?fmap_app app_nil_r; cbn.
    intros [? [Hrel1 Hrel2]]; split; first done.
    split.
    { intros ????; rewrite lookup_app_Some; intros [?%Hrel1|[??%list_lookup_singleton_Some]]; eauto.
      des; clarify.
    }
    { intros ?? [stid Hstid]%Hrel2; apply lookup_lt_Some in Hstid as Hlen.
      exists stid; rewrite lookup_app_l //.
    }
  Qed.

  Definition inner_spawn_pend (arg : Any.t) ktr : itree lmodE Any.t :=
    tau;;
    x <- ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes)
      (⇓smod(false, sp_none) (
        'arg : SAny.t <- (arg↓)?;;
        'x1 : thpool <- (cgetU SchI.v_ths);;
        'x2 : nat <- (cgetU SchI.v_tid);;
        r <-
          (match x1 !! x2 with
          | Some (stid, _) =>
              cput SchI.v_ths (<[x2 := (stid, Some arg)]> x1);;;
              Sch.terminate
          | None => triggerUB
          end);;
        Ret (r↑))));;
    ktr x.

  Definition join_pend (arg : Any.t) stid ktr : itree lmodE Any.t :=
    tau;;
    x <- ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes)
      (⇓smod(false, sp_none) (
        'arg : () <- (arg↓)?;;
        x_3 <- iterC (λ _ : (),
          'x_1 : thpool <- cgetU SchI.v_ths;;
          match x_1 !! stid with
          | Some (_, Some rv) => Ret (inr (Some rv))
          | Some (_, None) =>
              '() : _ <- ccallU SchHdr.yield tt;; Ret (inl ())
          | None => Ret (inr None)
          end
        ) ();;
        Ret (x_3↑))));;
    ktr x.

  Definition helpee_pend_s
      (j : jobID) k
      (fspo : option fspec) (x_fsp : fspec_option_meta fspo)
      : itree lmodE Any.t :=
    tau;;
    r <- ⇓cris (⇓sb(true, wmask_all, HelpingOff.scopes mn) (
      HoareCall_epilogue fspo x_fsp ()↑;;;
      ⇓smod(false, sp) (𝒴;;; r <- Helping.trans (jobs j);; 𝒴;;; Ret r↑)
    ));;
    k r.

  Definition helpee_pend_t
      (tid_stid_cur : nat) (j : jobID) k
      (fspo : option fspec) (x_fsp : fspec_option_meta fspo)
      : itree lmodE Any.t :=
    tau;;
    r <- ⇓cris (⇓sb(true, wmask_all, HelpingOff.scopes mn) (
      HoareCall_epilogue fspo x_fsp ()↑;;;
      ⇓smod(false, sp) (𝒴;;; r <- HelpingOn.try_run mn jobs tid_stid_cur;; 𝒴;;; Ret r↑)
    ));; (k r).

  Inductive help_rel : itree lmodE Any.t → itree lmodE Any.t → option (nat * (option retID * jobID)) → Prop :=
  | help_rel_ret ret : help_rel (Ret ret) (Ret ret) None
  | help_rel_eq itr_s itr_t (k_s k_t : Any.t → _) itr img msk scp :
      itr_t = ModTr.trans (SB.sandbox img msk scp itr) >>= k_t →
      itr_s = ModTr.trans (SB.sandbox img msk scp itr) >>= k_s →
      scp ## (SchI.scopes ++ HelpingOff.scopes mn) →
      (∀ ret, itr ≠ Ret ret) →
      (∀ ret, help_rel (k_s ret) (k_t ret) None) →
      help_rel itr_s itr_t None
  | help_rel_loop itr_s itr_t ktr_t ktr_s x (ret : Any.t) :
      itr_t = (tau;;
        x_ <- ⇓cris(⇓sb(true, wmask_all, HelpingOn.scopes mn)
          (x_2 <- HoareCall_epilogue (sp SchHdr.yield) x (()↑);;
          ⇓smod(false, sp) (Ret x_2;;; 𝒴;;; Ret (ret))));;
        ktr_t x_) →
      itr_s = (tau;;
        x_ <- ⇓cris(⇓sb(true, wmask_all, HelpingOn.scopes mn)
          (x_2 <- HoareCall_epilogue (sp SchHdr.yield) x (()↑);;
          ⇓smod(false, sp) (Ret x_2;;; 𝒴;;; Ret (ret))));;
        ktr_s x_) →
      (∀ ret, help_rel (ktr_s ret) (ktr_t ret) None) →
      help_rel itr_s itr_t None
  | help_rel_helpee_done tid jid itr_s itr_t x k_s k_t ret :
      itr_t = helpee_pend_t tid jid k_t (sp SchHdr.yield) x →
      itr_s = (tau;;
        x_ <- ⇓cris(⇓sb(true, wmask_all, HelpingOn.scopes mn)
          (x_2 <- HoareCall_epilogue (sp SchHdr.yield) x (()↑);;
          ⇓smod(false, sp) (Ret x_2;;; 𝒴;;; Ret (ret↑))));;
        k_s x_) →
      (∀ ret, help_rel (k_s ret) (k_t ret) None) →
      help_rel itr_s itr_t (Some (tid, (Some ret, jid)))
  | help_rel_helpee_pend tid jid itr_s itr_t k_s k_t x_fsp :
      itr_s = helpee_pend_s jid k_s (sp SchHdr.yield) x_fsp →
      itr_t = helpee_pend_t tid jid k_t (sp SchHdr.yield) x_fsp →
      (∀ ret, help_rel (k_s ret) (k_t ret) None) →
      help_rel itr_s itr_t (Some (tid, (None, jid)))
  | help_rel_call itr_s itr_t ktr_t ktr_s ktr_t1 ktr_s1 ctx rs fn arg :
      Some fn ∈ List.map fst (Mod.fnsems ((HelpingOn.t mn jobs sp) ★ (CFilter.filter msk SchI.t))) →
      Mod.wf ((HelpingOn.t mn jobs sp ★ CFilter.filter msk SchI.t) ★ ctx) →
      prog_t ctx rs fn = Some ktr_t →
      prog_s ctx rs fn = Some ktr_s →
      itr_t = ktr_t arg >>= ktr_t1 →
      itr_s = ktr_s arg >>= ktr_s1 →
      (∀ ret, help_rel (ktr_s1 ret) (ktr_t1 ret) None) →
      help_rel itr_s itr_t None
  | help_rel_inner_spawn itr_s itr_t (arg : Any.t) ktr_s ktr_t :
      itr_t = inner_spawn_pend arg ktr_t →
      itr_s = inner_spawn_pend arg ktr_s →
      (∀ ret, help_rel (ktr_s ret) (ktr_t ret) None) →
      help_rel itr_s itr_t None
  | help_rel_join itr_s itr_t (arg : Any.t) ktr_s ktr_t tid :
      itr_t = join_pend arg tid ktr_t →
      itr_s = join_pend arg tid ktr_s →
      (∀ ret, help_rel (ktr_s ret) (ktr_t ret) None) →
      help_rel itr_s itr_t None
  | help_rel_terminate itr_s itr_t ktr_s ktr_t :
      itr_s =
        (x <- ⇓cris (⇓sb( false, wmask_and msk wmask_all, SchI.scopes)
          (⇓smod( false, sp_none) (x_ <- Sch.terminate;; Ret x_↑)));;
        ktr_s x) →
      itr_t =
        (x <- ⇓cris (⇓sb( false, wmask_and msk wmask_all, SchI.scopes)
          (⇓smod( false, sp_none) (x_ <- Sch.terminate;; Ret x_↑)));;
        ktr_t x) →
      (∀ ret, help_rel (ktr_s ret) (ktr_t ret) None) →
      help_rel itr_s itr_t None.

  Lemma gsim_Yield_tgt r g RR p_s p_t tid_s tid_t tp_s tp_t
      img_c img_c' msk_c scp_c k_s k_t (k_s1 k_t1 : Any.t → itree _ Any.t) ctx rs
      (ths : list (nat * option SAny.t)) (tid_cur_s tid_cur_t : nat) st_ctx (res : Σ) reqs :
    ✓ res →
    tid_s < length tp_s →
    tid_t < length tp_t →
    gpaco7 _gsim (cpn7 _gsim) g g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top smj_top
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_s ctx rs))
          (tid_s, <[tid_s :=
            x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c', sp)(𝒴;;; k_s)));;
            k_s1 x]> tp_s))
        (Any.pair
          (ModTr.alist_encode ((SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (tid_cur_s ↑)) :: st_ctx))
          (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_t ctx rs))
          (tid_t, <[tid_t :=
            x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c', sp) k_t));; k_t1 x]> tp_t))
        (Any.pair
          (ModTr.alist_encode ((HelpingOn.v_reqs mn, reqs)
          :: (SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (tid_cur_t ↑)) :: st_ctx))
          (res↑))) →
    ((∃ ro_s, ths !! tid_cur_s = Some (tid_s, ro_s)) →
      ∃ ro_t, ths !! tid_cur_t = Some (tid_t, ro_t) ∧
      (∀ mtidn_t stidn_t, ths.*1 !! mtidn_t = Some stidn_t →
        ∃ mtidn_s stidn_s, ths.*1 !! mtidn_s = Some stidn_s ∧
          ∀ (res1 : Σ) x, ✓ res1 →
          gpaco7 _gsim (cpn7 _gsim) g g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top smj_top
            (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (prog_s ctx rs))
                (stidn_s, <[tid_s := tau;;
                  x_ <- ⇓cris (⇓sb(img_c, msk_c, scp_c)
                    (x_2 <- HoareCall_epilogue (sp SchHdr.yield) x (()↑);;
                    (⇓smod(img_c', sp) (Ret x_2;;; 𝒴;;; k_s))));; k_s1 x_]> tp_s))
              (Any.pair
                (ModTr.alist_encode ((SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (mtidn_s ↑)) :: st_ctx))
                (res1 ↑)))
            (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (prog_t ctx rs))
                (stidn_t, <[tid_t := tau;;
                  x_ <- ⇓cris (⇓sb(img_c, msk_c, scp_c)
                    (x_2 <- HoareCall_epilogue (sp SchHdr.yield) x (()↑);;
                    (⇓smod(img_c', sp) (Ret x_2;;; 𝒴;;; k_t))));; k_t1 x_]> tp_t))
              (Any.pair
                (ModTr.alist_encode
                  ((HelpingOn.v_reqs mn, reqs)
                  :: (SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (mtidn_t ↑)) :: st_ctx))
                (res1 ↑))))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_s ctx rs))
          (tid_s, <[tid_s :=
            x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c', sp)(𝒴;;; k_s)));;
            k_s1 x]> tp_s))
        (Any.pair
          (ModTr.alist_encode ((SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (tid_cur_s ↑)) :: st_ctx))
          (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_t ctx rs))
          (tid_t, <[tid_t :=
            x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c', sp) (𝒴;;; k_t)));;
            k_t1 x]> tp_t))
        (Any.pair
          (ModTr.alist_encode ((HelpingOn.v_reqs mn, reqs)
          :: (SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (tid_cur_t ↑)) :: st_ctx))
          (res↑))).
  Proof.
    intros Hres Hlen_s Hlen_t Hk1 Hk2; revert Hk1; rewrite yield_unfold; ired.
    revert res Hres.
    gcofix CIH.
    intros res Hres Hk1.
    replace_r; [rewrite interpV_tau //|].
    eapply gsim_tau_tgt; [rewrite list_lookup_insert //|rewrite list_insert_insert].
    rewrite interpV_tau.
    eapply gsim_tau_src; [rewrite list_lookup_insert //|rewrite list_insert_insert].
    zprogress.
    replace_r; [rewrite interpV_bind interpV_trigger //=|]; ired.
    eapply gsim_Choose_tgt; [rewrite list_lookup_insert // length_insert //|].
    intros [[|]|]; cycle 1; rewrite list_insert_insert.
    {
      ired. rewrite interpV_bind interpV_trigger //=; ired.
      eapply gsim_Choose_src; [rewrite list_lookup_insert //|].
      exists (Some false); rewrite list_insert_insert.
      rewrite yield_unfold; ired.
      guclo flagC_spec; econs; [instantiate (1:=p_s)|instantiate (1:=p_t)|].
      { destruct p_s as [[|]|]; rr; ss; eauto. }
      { destruct p_t as [[|]|]; rr; ss; eauto. }
      gbase. eapply CIH; eauto.
    }
    {
      clear CIH.
      ired. rewrite interpV_bind interpV_trigger //=; ired.
      eapply gsim_Choose_src; [rewrite list_lookup_insert //|].
      exists (Some false); rewrite list_insert_insert. ired.
      rewrite {1}yield_unfold. ired.
      eapply gpaco7_mon; first apply Hk1; eauto.
    }
    ired. rewrite interpV_bind interpV_trigger //=; ired.
    eapply gsim_Choose_src; [rewrite list_lookup_insert //|].
    exists (Some true); rewrite list_insert_insert. ired.

    iter_l; rewrite list_lookup_insert //=; step_l; norm_l.
    rewrite list_insert_insert.
    iter_r; rewrite list_lookup_insert //=; step_r; norm_r.
    rewrite list_insert_insert.

    rewrite !HoareCall_unfold; ired.
    eapply gsim_HoareCall_prologue_both;
      [rewrite list_lookup_insert //
      |rewrite list_lookup_insert //
      |ss
      |].
    intros res1 [x arg] Hres1.
    rewrite ?list_insert_insert. ired.

    iter_l; rewrite list_lookup_insert //=.
    iter_r; rewrite list_lookup_insert //=.
    destruct (msk_c _); cycle 1; ss.
    { step_l; ss. }
    step_l; step_r; norm_l; norm_r; rewrite {1 3}/LMod.prog /=; destruct (dec _ _) as [e|e]; ss.
    { inv e; exfalso; eapply yield_run_neq; eauto. }
    clear e; destruct (dec _ _) as [e|e].
    { ss. inv e; exfalso; eapply yield_help_neq; eauto. }
    ss; clear e. norm_l. rewrite list_insert_insert. ss.
    norm_r. rewrite list_insert_insert. ss.

    rewrite /ModTr.trans_ktree /ModTr.trans /SB.sandbox_body /SB.sandbox /SModTr.trans /=.
    eapply gsim_tau_tgt; [rewrite list_lookup_insert //|rewrite list_insert_insert].
    eapply gsim_tau_src; [rewrite list_lookup_insert //|rewrite list_insert_insert].
    rewrite /SchI.yield /cfunU.
    destruct (arg ↓) eqn : Harg; cycle 1.
    { ss; iter_l; rewrite list_lookup_insert //=.
      destruct (excluded_middle_informative _); step_l; ss.
    }
    ss. ired.

    replace_r; [rewrite interpV_bind //|]. ired.
    eapply gsim_s_cgetU_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
    { rewrite String.eqb_refl //. }
    esplits; eauto.
    rewrite ?list_insert_insert. ired.

    replace_l; [rewrite interpV_bind //|]. ired.
    eapply gsim_s_cgetU_src; [rewrite list_lookup_insert // length_fmap //| |]; s.
    { rewrite String.eqb_refl //. }
    esplits; eauto.
    rewrite ?list_insert_insert. ired.

    iter_l; rewrite list_lookup_insert //=. step_l; norm_l.
    rewrite list_insert_insert.
    iter_r; rewrite list_lookup_insert //=; step_r; norm_r.
    rewrite list_insert_insert.

    iter_l; rewrite list_lookup_insert //=. step_l; norm_l.
    rewrite list_insert_insert.
    iter_r; rewrite list_lookup_insert //=; step_r; norm_r.
    rewrite list_insert_insert. ired.

    replace_r; [rewrite interpV_bind //|]. ired.
    eapply gsim_s_cgetU_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
    { rewrite String.eqb_refl //. }
    esplits; eauto.
    rewrite ?list_insert_insert. ired.

    replace_l; [rewrite interpV_bind //|]. ired.
    eapply gsim_s_cgetU_src; [rewrite list_lookup_insert // length_fmap //| |]; s.
    { rewrite String.eqb_refl //. }
    esplits; eauto.
    rewrite ?list_insert_insert. ired.

    destruct (ths !! tid_cur_s) as [[stid_cur_s reto_s]|] eqn : Htid_cur_s; cycle 1.
    { rewrite Htid_cur_s /=.
      ss; iter_l; rewrite list_lookup_insert //=.
      destruct (excluded_middle_informative _); step_l; ss.
    }
    rewrite Htid_cur_s //=.
    destruct (decide (stid_cur_s = tid_s)); subst; cycle 1.
    { ss; iter_l; rewrite list_lookup_insert //=.
      destruct (excluded_middle_informative _); step_l; ss.
    }
    hexploit Hk2; eauto; clear Hk2; intros [? [Htid_t Hk2]].
    rewrite Htid_t; case_decide; clarify; ired.

    replace_r; [rewrite interpV_bind interpV_trigger //=|]; ired.
    eapply gsim_Choose_tgt; [rewrite list_lookup_insert // length_insert //|].
    intros [[mtidn stidn] Hmtidn]; rewrite list_insert_insert; ired; ss.

    replace_l; [rewrite interpV_bind interpV_trigger //=|]; ired.
    eapply gsim_Choose_src; [rewrite list_lookup_insert // length_insert //|].
    specialize (Hk2 mtidn stidn Hmtidn); destruct Hk2 as [mtidn_s [stidn_s [Htid_s Hk3]]].
    unshelve eexists.
    { exists (mtidn_s, stidn_s); ss; eauto. }
    rewrite list_insert_insert; ired; ss.

    ired. replace_r; [rewrite interpV_bind //|]. ired.
    eapply gsim_s_cput_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
    { rewrite String.eqb_refl //. }
    rewrite ?list_insert_insert.
    rewrite /alist_upd /=; destruct (dec _ _) as [e|e]; ss; clarify; clear e.

    ired. replace_l; [rewrite interpV_bind //|]. ired.
    eapply gsim_s_cput_src; [rewrite list_lookup_insert // length_fmap //| |]; s.
    { rewrite String.eqb_refl //. }
    rewrite ?list_insert_insert.
    rewrite /alist_upd /=; destruct (dec _ _) as [e|e]; ss; clarify; clear e.

    iter_l; rewrite list_lookup_insert //=. step_l; norm_l.
    rewrite list_insert_insert. hss.
    iter_l; rewrite list_lookup_insert //=. step_l; norm_l.
    rewrite list_insert_insert. ired.
    iter_r; rewrite list_lookup_insert //=. step_r; norm_r.
    rewrite list_insert_insert. hss.
    iter_r; rewrite list_lookup_insert //=. step_r; norm_r.
    rewrite list_insert_insert. ired.
    rewrite ?interpV_ret. ired.
    eapply gpaco7_mon; first eapply Hk3; eauto.
  (*SLOW*)Qed.

  Lemma gsim_Yield_both r g RR p_s p_t tid_s tid_t tp_s tp_t
      img_c img_c' msk_c scp_c k_s k_t (k_s1 k_t1 : Any.t → itree _ Any.t) ctx rs
      (ths : list (nat * option SAny.t)) (tid_cur_s tid_cur_t : nat) st_ctx (res : Σ) reqs :
    ✓ res →
    tid_s < length tp_s →
    tid_t < length tp_t →
    gpaco7 _gsim (cpn7 _gsim) g g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top smj_top
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_s ctx rs))
          (tid_s, <[tid_s :=
            x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c', sp) k_s));; k_s1 x]>
            tp_s))
        (Any.pair
          (ModTr.alist_encode ((SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (tid_cur_s ↑)) :: st_ctx))
          (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_t ctx rs))
          (tid_t, <[tid_t :=
            x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c', sp) k_t));; k_t1 x]>
            tp_t))
        (Any.pair
          (ModTr.alist_encode ((HelpingOn.v_reqs mn, reqs)
          :: (SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (tid_cur_t ↑)) :: st_ctx))
          (res↑))) →
    ((∃ ro_s, ths !! tid_cur_s = Some (tid_s, ro_s)) →
      ∃ ro_t, ths !! tid_cur_t = Some (tid_t, ro_t) ∧
      (∀ mtidn_t stidn_t, ths.*1 !! mtidn_t = Some stidn_t →
        ∃ mtidn_s stidn_s, ths.*1 !! mtidn_s = Some stidn_s ∧
          ∀ (res1 : Σ) x, ✓ res1 →
          gpaco7 _gsim (cpn7 _gsim) g g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top smj_top
            (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (prog_s ctx rs))
                (stidn_s, <[tid_s := tau;;
                  x_ <- ⇓cris (⇓sb(img_c, msk_c, scp_c)
                    (x_2 <- HoareCall_epilogue (sp SchHdr.yield) x (()↑);;
                    (⇓smod(img_c', sp) (Ret x_2;;; 𝒴;;; k_s))));; k_s1 x_]> tp_s))
              (Any.pair
                (ModTr.alist_encode ((SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (mtidn_s ↑)) :: st_ctx))
                (res1 ↑)))
            (LModTr.interp_stateE Any.t
              (iterV (LModTr.handle_callE (prog_t ctx rs))
                (stidn_t, <[tid_t := tau;;
                  x_ <- ⇓cris (⇓sb(img_c, msk_c, scp_c)
                    (x_2 <- HoareCall_epilogue (sp SchHdr.yield) x (()↑);;
                    (⇓smod(img_c', sp) (Ret x_2;;; 𝒴;;; k_t))));; k_t1 x_]> tp_t))
              (Any.pair
                (ModTr.alist_encode
                  ((HelpingOn.v_reqs mn, reqs)
                  :: (SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (mtidn_t ↑)) :: st_ctx))
                (res1 ↑))))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_s ctx rs))
          (tid_s, <[tid_s :=
            x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c', sp)(𝒴;;; k_s)));;
            k_s1 x]> tp_s))
        (Any.pair
          (ModTr.alist_encode ((SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (tid_cur_s ↑)) :: st_ctx))
          (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (prog_t ctx rs))
          (tid_t, <[tid_t :=
            x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c', sp) (𝒴;;; k_t)));;
            k_t1 x]> tp_t))
        (Any.pair
          (ModTr.alist_encode ((HelpingOn.v_reqs mn, reqs)
          :: (SchI.v_ths, (ths ↑)) :: (SchI.v_tid, (tid_cur_t ↑)) :: st_ctx))
          (res↑))).
  Proof.
    intros Hres Hlen_s Hlen_t Hk1 Hk2.
    eapply gsim_Yield_tgt; eauto.
    rewrite {1}yield_unfold. ired.
    replace_l; [rewrite interpV_tau //|]; ired.
    eapply gsim_tau_src; [rewrite list_lookup_insert //|]. rewrite list_insert_insert.

    replace_l; [rewrite interpV_bind interpV_trigger //=|]; ired.
    eapply gsim_Choose_src; [rewrite list_lookup_insert //|].
    exists (None); rewrite list_insert_insert. ired.

    eapply Hk1.
  Qed.

  Theorem helping_onoff_correct :
    ctx_refines (mod_off, emp%I) (mod_on, emp%I).
  Proof.
    rewrite /mod_off /mod_on.
    intros [ctx ctxP] WF; ss; split.
    { inv WF. econs.
      { revert wf_fns. rewrite /HelpingOff.t /HelpingOn.t /SchI.t; unseal CRIS; ss. }
      { revert wf_scopes. rewrite /HelpingOff.t /HelpingOn.t /SchI.t; unseal CRIS; ss. }
    }
    intros rs Hval Hrs; exists rs; split; [exact Hval|split; [done|]].

    intro arg; eapply (@gsim_adequacy smj_bot smj_bot).
    rewrite /LMod.compile /ITree.map /LModTr.trans /LModTr.interp_callE /=.
    rewrite !alist_find_map_snd.
    set (fnsems := (Mod.fnsems _ ++ _) ++ _).
    destruct (alist_find None fnsems) eqn: FIND; s; cycle 1.
    { s. ired. ginit. step_l. ss. }
    rewrite alist_find_app_o; des_ifs.
    { rewrite alist_find_app_o /HelpingOn.t /SchI.t in Heq; revert Heq; unseal CRIS; intros Heq.
      des_ifs; ss.
    }
    subst fnsems; rewrite alist_find_app_o in FIND; des_ifs.
    { rewrite /HelpingOff.t /SchI.t in Heq0; revert Heq0; unseal CRIS; ss. }
    rewrite FIND /ModTr.trans_ktree; ired.

    destruct f as [[[imgf mskf] scpf] f].
    assert (Hscp : scpf ## (SchI.scopes ++ HelpingOn.scopes mn)).
    { hexploit (Mod.well_scoped_fns ctx None); ss.
      rewrite /fnsems_scopes FIND /=; intros Hin.
      apply elem_of_disjoint; intros x Hinctx%elem_of_list_In%Hin%elem_of_list_In Hinsch.
      hexploit (Mod.wf_scopes WF); rewrite /Mod.scopes /=.
      intros Hnodup; eapply (NoDup_app_disjoint _ _ Hnodup x); eauto.
      { eapply elem_of_list_In. rewrite /Mod.scopes /SchI.t /HelpingOn.t; unseal CRIS; ss.
        revert Hinsch; rewrite /HelpingOn.scopes /SchI.scopes; ss.
        set_solver.
      }
      { eapply elem_of_list_In, Hinctx; eauto. }
    }

    clear Heq Heq0.
    rewrite /SB.sandbox_body /=.
    ginit. guclo bindC_spec. econs; cycle 1.
    { instantiate (1:=λ r_s r_t, r_s.2 = r_t.2). ii; gstep; ss. subst; econs; econs; ss. }
    unfold_trans.
    (* Start coinduction *)
    rewrite /HelpingOff.t /HelpingOn.t /SchI.t; unseal CRIS; ss.
    set (st_src := (_, _) :: _) at 1.
    set (st_tgt := (_, _) :: _).
    set (tp_src := (0, [_])) at 1.
    set (tp_tgt := (0, [_])).
    clear Hrs.
    cut
      (∃ (tl : list (itree lmodE Any.t * itree lmodE Any.t * option (nat * (option retID * jobID))))
        (mtid stid : nat) (ths : list (nat * option SAny.t)) st_ctx
        (reqmap : gmap nat (option retID * jobID)),
          st_src = [(SchI.SchI.v_ths, ths↑); (SchI.SchI.v_tid, mtid↑)] ++ st_ctx ∧
          st_tgt = [(HelpingOn.v_reqs mn, reqmap↑);
            (SchI.SchI.v_ths, ths↑); (SchI.SchI.v_tid, mtid↑)] ++ st_ctx ∧
          tp_src = (stid, (fst ∘ fst <$> tl)) ∧ tp_tgt = (stid, (snd ∘ fst <$> tl)) ∧
          reqmap_rel tl reqmap ∧
          ∀ i itr_s itr_t no, tl !! i = Some (itr_s, itr_t, no) →
            help_rel itr_s itr_t no ∧
            match no with
            | Some _ => ∃ stid_i ro_i, ths !! stid_i = Some (i, ro_i)
            | None => True
            end); cycle 1.
    { esplits; subst st_src st_tgt; ss; repeat f_equal; first instantiate (1:=[(_,_, None)]); ss.
      { rr; ss; split; first econs.
        split; [intros ????; rewrite ?list_lookup_singleton_Some; i; des; clarify|].
        intros ??; rewrite lookup_empty; i; clarify.
      }
      intros ???? [-> In]%list_lookup_singleton_Some; clarify.
      split; ss.
      ides (f arg).
      { rewrite ?interpV_ret; eapply help_rel_ret. }
      { eapply help_rel_eq; eauto.
        { instantiate (1:=λ a, Ret a). ired. refl. }
        { instantiate (1:=λ a, Ret a). ired. refl. }
        { ii; clarify. }
        apply help_rel_ret.
      }
      { eapply help_rel_eq; eauto.
        { instantiate (1:=λ a, Ret a). ired. refl. }
        { instantiate (1:=λ a, Ret a). ired. refl. }
        { ii; clarify. }
        apply help_rel_ret.
      }
    }
    generalize st_src, st_tgt, tp_src, tp_tgt.
    clear st_src st_tgt tp_src tp_tgt f imgf mskf scpf FIND arg Hscp.
    revert_until WF.
    gcofix CIH.
    intros rs Hrs st_s st_t tp_s tp_t.
    intros [tl [mtid [stid [ths [st_ctx [reqmap [-> [-> [-> [-> [Hreqmap Hlookup]]]]]]]]]]].

    destruct ((fst ∘ fst <$> tl) !! stid) as [i|] eqn : Htid; cycle 1.
    { iter_l. rewrite Htid. step_l. norm_l. step_l. ss. }

    apply list_lookup_fmap_inv in Htid as [[[itr_src itr_tgt] no] [-> Htid]]; s.
    destruct no as [[n [[retid|] j]]|].

    { (* Done Helpee *)
      apply lookup_lt_Some in Htid as Hstid_cur_length.
      pose proof Htid as Htid'.
      apply Hlookup in Htid' as [Hcase _]. inv Hcase.

      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      step_l; step_r; norm_l; norm_r.
      eapply gsim_HoareCall_epilogue_both;
        [rewrite list_lookup_insert // length_fmap //
        |rewrite list_lookup_insert // length_fmap //
        |ss|].
      intros res1 x1 Hres1; rewrite ?list_insert_insert. ired.

      eapply gsim_Yield_tgt; eauto;
        [rewrite length_fmap //
        |rewrite length_fmap //
        | |]; cycle 1.
      { (* coinduction *)
        intros [ro_s Hro_s]; exists ro_s; split; first done.
        intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
        clear dependent res1. intros res2 x2 Hres2.
        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase. eapply (CIH res2); try by des.

        eexists (<[stid := (_, _, (Some (n, (Some _, j))))]> tl); ss; esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split; ss. esplits; eauto.
            eapply help_rel_helpee_done; eauto.
            { rewrite /helpee_pend_t; repeat f_equal; grind. extensionalities a; grind. }
            { esplits; eauto. }
          }
        }
      }

      (* no job *)
      rewrite ?interpV_ret; ired.
      rewrite /HelpingOn.try_run; ired.

      replace_r; [rewrite interpV_bind //|]; ired.
      eapply gsim_s_cgetU_tgt;
        [rewrite list_lookup_insert // length_fmap //
        |ss; rewrite String.eqb_refl //
        |].
      esplits; eauto.
      { rewrite /alist_find ?eq_rel_dec_correct; des_ifs. }
      rewrite list_insert_insert.

      eapply reqmap_rel_Some in Hreqmap as Hsome; eauto. rewrite Hsome; clear Hsome.
      ired.

      eapply gsim_Yield_tgt; eauto;
        [rewrite length_fmap //
        |rewrite length_fmap //
        | |]; cycle 1.
      { (* coinduction *)
        intros [ro_s Hro_s]; exists ro_s; split; first done.
        intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
        clear dependent res1. intros res2 x2 Hres2.
        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase. eapply (CIH res2); try by des.

        eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_delete_false; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split; ss. esplits; eauto.
            eapply help_rel_loop; eauto.
          }
        }
      }

      (* Done helped *)
      rewrite yield_unfold; ired.
      replace_l; [rewrite interpV_tau //|].
      eapply gsim_tau_src; [rewrite list_lookup_insert // length_fmap //|].
      rewrite list_insert_insert.

      replace_l; [rewrite interpV_bind interpV_vis //|]; ired.
      eapply gsim_Choose_src; [rewrite list_lookup_insert // length_fmap //|].
      exists None; rewrite list_insert_insert.
      ired. rewrite ?interpV_ret; ired. rewrite ?interpV_ret; ired.

      eapply gsim_flag.

      gbase. eapply (CIH res1); eauto.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_delete_false; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. }
      }
    }

    { (* Pending helpee *)
      eapply Hlookup in Htid as Htid'; destruct Htid' as [Hrel Hex].
      eapply lookup_lt_Some in Htid as Htidlen.
      inv Hrel; ss.
      revert Htid; rewrite /helpee_pend_s /helpee_pend_t; intros Htid.
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      step_l; step_r; norm_l; norm_r.
      eapply gsim_HoareCall_epilogue_both;
        [rewrite list_lookup_insert // length_fmap //
        |rewrite list_lookup_insert // length_fmap //
        |ss|].
      intros res x Hres1; rewrite ?list_insert_insert.

      eapply gsim_Yield_both; eauto;
        [rewrite length_fmap //
        |rewrite length_fmap //
        | |]; cycle 1.
      { (* Yield-coinduction *)
        intros [ro_s Hro_s]; exists ro_s; split; first done.
        intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
        clear dependent res x. intros res x Hres.
        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase. eapply (CIH res); try by des.

        eexists (<[stid := (_, _, Some (n, (_, j)))]> tl); esplits; eauto.
        { rewrite list_fmap_insert //. }
        { rewrite list_fmap_insert //. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split.
            { eapply (help_rel_helpee_pend n j); eauto.
              { rewrite /helpee_pend_s. grind.
                instantiate (1:=x). repeat f_equal. extensionality a; grind.
              }
              { rewrite /helpee_pend_t. grind. repeat f_equal. extensionality a; grind. }
            }
            esplits; eauto.
          }
        }
      }

      (* tired of waiting *)
      rewrite /HelpingOn.try_run; ired.
      replace_r; [rewrite interpV_bind //|]. ired.
      eapply gsim_s_cgetU_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
      { rewrite String.eqb_refl //. }
      esplits; eauto. { destruct (dec _ _); clarify. }
      rewrite ?list_insert_insert. ired.

      eapply reqmap_rel_Some in Hreqmap as Hsome; eauto.
      rewrite Hsome; clear Hsome.

      ired.
      eapply gsim_jobs_both; try by rewrite ?length_fmap.
      clear dependent res x. hss.
      intros res ret Hres.

      ired. replace_r; [rewrite interpV_bind //|]. ired.
      eapply gsim_s_cput_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
      { rewrite String.eqb_refl //. }
      rewrite ?list_insert_insert.
      rewrite /alist_upd /=; destruct (dec _ _) as [e|e]; ss; clarify; clear e.

      eapply gsim_Yield_both; eauto;
        [rewrite length_fmap //
        |rewrite length_fmap //
        | |]; cycle 1.
      { (* Yield-coinduction *)
        intros [ro_s Hro_s]; exists ro_s; split; first done.
        intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
        clear dependent res. intros res x Hres.
        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase. eapply (CIH res); try by des.

        eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_delete_true; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split; ss.
            eapply help_rel_loop; eauto; ss.
          }
        }
      }

      rewrite ?interpV_ret; ired.

      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH res); eauto.
      eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_delete_true; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. }
      }
    }

    (* Non-helpee case *)
    apply lookup_lt_Some in Htid as Hstid_cur_length.
    pose proof Htid as Htid'.
    apply Hlookup in Htid' as [Hcase _].
    inv Hcase; cycle 2.
    { (* Done helper case *)
      eapply lookup_lt_Some in Htid as Htidlen.
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      step_l; step_r; norm_l; norm_r.
      eapply gsim_HoareCall_epilogue_both;
        [rewrite list_lookup_insert // length_fmap //
        |rewrite list_lookup_insert // length_fmap //
        |ss|].
      intros res x1 Hres1; rewrite ?list_insert_insert. ired.

      eapply gsim_Yield_both; eauto;
        [rewrite length_fmap //
        |rewrite length_fmap //
        | |]; cycle 1.
      { (* Yield-coinduction *)
        intros [ro_s Hro_s]; exists ro_s; split; first done.
        intros mtidn_t stidn_t Hmtidn_t; exists mtidn_t, stidn_t; split; first done.
        clear dependent res x1. intros res x1 Hres.

        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase. eapply (CIH res); try by des.

        eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split; ss.
            eapply (help_rel_loop); eauto.
          }
        }
      }

      (* Done helping *)
      rewrite ?interpV_ret; ired.
      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH res); try by des.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. }
      }
    }

    { (* call case *)
      eapply lookup_lt_Some in Htid as Htidlen.
      revert H3 H4.
      destruct (decide (fn = Helping.run mn)); subst.
      { (* Helping.run *)
        rewrite {1 2}/LMod.prog ?alist_find_map_snd /=.
        destruct (dec _ _) as [?|e]; [ss|clarify; clear e].
        i; clarify.

        revert Htid; unfold_trans; rewrite /SModTr.trans /HelpingOff.run /HelpingOn.run.
        intros Htid.

        eapply gsim_tau_src; [rewrite list_lookup_fmap // Htid //=|].
        eapply gsim_tau_tgt; [rewrite list_lookup_fmap // Htid //=|].
        destruct (arg↓) as [j|] eqn:Hargs ; cycle 1.
        { iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. ss. }
        ss. ired.

        (* call for help *)
        replace_r; [rewrite interpV_bind //|]. ired.
        eapply gsim_s_cgetU_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
        { rewrite String.eqb_refl //. }
        esplits; eauto.
        { des_ifs; destruct (dec _ _); clarify. }
        rewrite list_insert_insert.

        replace_r; [rewrite interpV_bind //|]. ired.
        eapply gsim_s_cput_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
        { rewrite String.eqb_refl //. }
        rewrite list_insert_insert.

        rewrite /alist_upd /_alist_upd /=.
        destruct (dec _ _) as [Heq|Heq]; ss; clear Heq.

        eapply gsim_Yield_both; eauto.
        { rewrite length_fmap //. }
        { rewrite length_fmap //. }
        { (* Self-help *)
          rewrite /HelpingOn.try_run.
          ired. replace_r; [rewrite interpV_bind //|]. ired.
          eapply gsim_s_cgetU_tgt; [rewrite list_lookup_insert //| |]; s.
          { rewrite ?length_fmap //. }
          { rewrite String.eqb_refl //. }
          esplits; eauto.
          { destruct (dec _ _); clarify. }
          rewrite list_insert_insert. ired. rewrite lookup_insert. ired.

          eapply gsim_jobs_both; try by rewrite ?length_fmap.
          intros res1 ret1 Hres1.

          ired. replace_r; [rewrite interpV_bind //|]. ired.
          eapply gsim_s_cput_tgt; [rewrite list_lookup_insert //| |]; s.
          { rewrite ?length_fmap //. }
          { rewrite String.eqb_refl //. }
          rewrite list_insert_insert.
          rewrite /alist_upd /_alist_upd eq_rel_dec_correct; des_ifs.
          rewrite insert_insert.

          eapply gsim_Yield_both; eauto.
          { rewrite length_fmap //. }
          { rewrite length_fmap //. }
          { (* immediate return of helpee *)
            rewrite ?interpV_ret; ired.

            gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.

            gbase. eapply (CIH res1); eauto.
            eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
            { rewrite list_fmap_insert //=. }
            { rewrite list_fmap_insert //=. }
            { eapply reqmap_rel_insert_false; first apply is_fresh. eapply reqmap_rel_id; eauto. }
            { intros i; destruct (decide (i = stid)); subst; cycle 1.
              { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
              { rewrite list_lookup_insert; ii; clarify. }
            }
          }

          (* appeal to coinduction *)
          intros [ro_s Htid_cur]; exists ro_s; split; first done.
          intros mtidn_t stidn_t Hn_t; exists mtidn_t, stidn_t; split; first done.
          intros res2 x Hres2; ss.

          gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
          gbase. eapply (CIH res2); eauto.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_insert_false; first apply is_fresh. eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. split; ss.
              eapply (help_rel_loop _ _ _ _ x); eauto.
            }
          }
        }

        (* Appeal to coinduction *)
        intros [ro_s Htid_cur]; exists ro_s; split; first done.
        intros mtidn_t stidn_t Hn_t; exists mtidn_t, stidn_t; split; first done.
        intros res2 x Hres2; ss.

        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase. eapply (CIH res2); eauto.

        set (rid_fresh := fresh _).
        eexists (<[stid := (_, _, Some (rid_fresh, (_, j)))]> tl); esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_insert_true; eauto; first apply is_fresh. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          {
            rewrite list_lookup_insert; ii; clarify.
            split.
            { eapply (help_rel_helpee_pend rid_fresh j); eauto.
              { rewrite /helpee_pend_s. grind.
                instantiate (1:=x).
                repeat f_equal. extensionality a; grind.
              }
              { rewrite /helpee_pend_t. grind. repeat f_equal.
                extensionality a; grind.
              }
            }
            esplits; eauto.
          }
        }
      }

      destruct (decide (fn = Helping.help mn)); subst.
      { (* Helping.help *)
        rewrite {1 2}/LMod.prog ?alist_find_map_snd /=.
        destruct (dec _ _) as [?|e]; ss; [inv e; clear e|clarify; clear e].
        destruct (dec _ _) as [e|e]; ss; clear e.
        i; clarify.

        revert Htid; unfold_trans; rewrite /SModTr.trans /HelpingOff.help /HelpingOn.help.
        intros Hstid.

        eapply gsim_tau_src; [rewrite list_lookup_fmap // Hstid //=|].
        eapply gsim_tau_tgt; [rewrite list_lookup_fmap // Hstid //=|].
        zprogress.

        (* Helper chooses tid *)
        replace_r; [rewrite interpV_bind interpV_trigger //|]. ired.
        eapply gsim_Choose_tgt; [rewrite list_lookup_insert // length_fmap //|intros rid].
        rewrite list_insert_insert.

        (* Source-helper goes to yield *)
        rewrite yield_unfold. ired.
        rewrite interpV_tau.
        eapply gsim_tau_src;
          [rewrite list_lookup_insert // length_fmap //|rewrite list_insert_insert].
        replace_l; [rewrite interpV_bind interpV_trigger //|]. ired.
        eapply gsim_Choose_src; [rewrite list_lookup_insert // length_fmap //|exists (Some true)].
        rewrite list_insert_insert. ired.

        (* Handling yield *)
        iter_l. rewrite list_lookup_insert //=; [|rewrite length_fmap //].
        step_l. norm_l. rewrite list_insert_insert.
        rewrite HoareCall_unfold. ired.
        replace_r; [rewrite interpV_bind HoareCall_prologue_sred //|].
        eapply gsim_HoareCall_prologue_both; eauto.
        { rewrite list_lookup_insert // length_fmap //. }
        { rewrite list_lookup_insert // length_fmap //. }
        intros res1 [fsp_yield varg] Hres1; rewrite ?list_insert_insert. ired.

        (* Calling yield *)
        iter_l. rewrite list_lookup_insert //=; [|rewrite length_fmap //]. step_l; norm_l.
        rewrite {1}/LMod.prog /=; destruct (dec _ _) as [e|e]; ss; [inv e|].
        { exfalso; eapply yield_run_neq; eauto. }
        clear e.
        destruct (dec _ _) as [e|e]; ss; [inv e|].
        { exfalso; eapply yield_help_neq; eauto. }
        norm_l. rewrite list_insert_insert.
        unfold_trans.
        eapply gsim_tau_src;
          [rewrite list_lookup_insert // length_fmap //|rewrite list_insert_insert].

        (* Yield entrance *)
        rewrite /cfunU /SchI.yield.
        destruct (varg↓) as [[]|] eqn : Hvarg; cycle 1.
        { ired. iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //=].
          destruct (excluded_middle_informative _); ss; step_l; ss.
        }

        ired. replace_l; [rewrite interpV_bind //|]; ired.
        eapply gsim_s_cgetU_src;
          [rewrite list_lookup_insert // length_fmap //
          |ss; rewrite String.eqb_refl //
          |].
        esplits; eauto.
        rewrite list_insert_insert.

        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
        rewrite list_insert_insert.
        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
        rewrite list_insert_insert. ired.

        ired. replace_l; [rewrite interpV_bind //|]; ired.
        eapply gsim_s_cgetU_src;
          [rewrite list_lookup_insert // length_fmap //
          |ss; rewrite String.eqb_refl //
          |].
        esplits; eauto.
        rewrite list_insert_insert.

        destruct (_ !! mtid) as [[stid2 ?]|] eqn : Hmtid; ss; cycle 1.
        { iter_l; rewrite list_lookup_insert /=; [|rewrite length_fmap //].
          destruct (excluded_middle_informative _); step_l; ss.
        }
        case_decide; subst; cycle 1.
        { iter_l; rewrite list_lookup_insert /=; [|rewrite length_fmap //].
          destruct (excluded_middle_informative _); step_l; ss.
        }
        ired.

        set (caseb :=
          match reqmap !! rid with
          | None => false
          | Some (None, _) => true
          | Some (Some _, _) => false
          end
        ).
        (* Choose the helpee! *)
        destruct caseb eqn : Hcase; cycle 1.
        { (* No Helpee *)
          ired.
          rewrite interpV_bind interpV_trigger /=. ired.
          eapply gsim_Choose_src;
            [rewrite list_lookup_insert //= length_fmap //
            |unshelve eexists].
          { exists (mtid, stid). rewrite list_lookup_fmap Hmtid //=. }
          rewrite list_insert_insert. ired.

          ired. replace_l; [rewrite interpV_bind //|]. ired.
          eapply gsim_s_cput_src; [rewrite list_lookup_insert // length_fmap //| |]; s.
          { rewrite String.eqb_refl //. }
          rewrite ?list_insert_insert.
          rewrite /alist_upd /=; destruct (dec _ _) as [e2|e2]; ss; clarify; clear e e2.

          iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
          rewrite list_insert_insert. ired.

          iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
          rewrite list_insert_insert. ired. rewrite ?interpV_ret. ired.

          iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
          rewrite list_insert_insert. ired. rewrite ?interpV_ret. ired.

          (* No helping here *)
          rewrite /HelpingOn.try_run; ired.
          replace_r; [rewrite interpV_bind HoareFun_prologue_sred //|]. ired.
          eapply gsim_HoareCall_epilogue_HoareFun_prologue;
            [rewrite list_lookup_insert // length_fmap //
            |rewrite list_lookup_insert // length_fmap //|ss|].
          intros res2 x Hres2. rewrite ?list_insert_insert /=. ired.

          ired. replace_r; [rewrite interpV_bind //|]; ired.
          eapply gsim_s_cgetU_tgt;
            [rewrite list_lookup_insert // length_fmap //
            |ss; rewrite String.eqb_refl //
            |].
          esplits; eauto. { ss; destruct (dec _ _); clarify. }
          rewrite list_insert_insert.

          destruct (reqmap !! rid) as [[[ret|]]|] eqn : Hridreqmap; cycle 1.
          { subst; clarify. }
          { ired. replace_r; [rewrite interpV_bind interpV_trigger //=|]; ired.
            eapply gsim_Choose_tgt; [rewrite list_lookup_insert // length_fmap //|ss].
          }
          clear dependent caseb. ired.

          rewrite yield_unfold; ired.
          rewrite interpV_tau.
          eapply gsim_tau_src;
            [rewrite list_lookup_insert // length_fmap //
            |rewrite list_insert_insert].
          rewrite interpV_bind interpV_vis /=; ired.
          eapply gsim_Choose_src;
            [rewrite list_lookup_insert // length_fmap //
            |exists (Some true); rewrite list_insert_insert].
          ired. rewrite interpV_ret; ired. rewrite ?interpV_ret; ired.

          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l; rewrite list_insert_insert.

          rewrite HoareCall_unfold; ired.
          replace_r; [rewrite interpV_bind HoareFun_epilogue_sred //|].
          eapply gsim_HoareCall_prologue_HoareFun_epilogue;
            [rewrite list_lookup_insert // length_fmap //
            |rewrite list_lookup_insert // length_fmap //
            |ss|].
          clear dependent res2 x. intros res2 ret2 Hres2.
          rewrite ?list_insert_insert. ired.

          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l; rewrite {1}/LMod.prog /=.
          destruct (dec _ _) as [?|e']; ss; [exfalso; hexploit yield_run_neq; ii; clarify|].
          clear e'.
          destruct (dec _ _) as [?|e]; [exfalso; hexploit yield_help_neq; ii; clarify|ss; clear e].
          norm_l. rewrite list_insert_insert.

          rewrite /ModTr.trans_ktree /ModTr.trans /SB.sandbox_body /SB.sandbox /SModTr.trans /=.
          eapply gsim_tau_src;
            [rewrite list_lookup_insert // length_fmap //
            |rewrite list_insert_insert].
          rewrite /SchI.yield /cfunU.
          destruct (ret2 ↓) as [[]|] eqn : Hret; cycle 1.
          { ss; iter_l; rewrite list_lookup_insert; [|rewrite length_fmap //].
            ss; destruct (excluded_middle_informative _); step_l; ss.
          }
          ired. clear Hret.

          ired. replace_l; [rewrite interpV_bind //|]; ired.
          eapply gsim_s_cgetU_src;
            [rewrite list_lookup_insert // length_fmap //
            |ss; rewrite String.eqb_refl //
            |].
          esplits; eauto.
          rewrite list_insert_insert.

          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l. rewrite list_insert_insert.
          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l. rewrite list_insert_insert; ired.

          ired. replace_l; [rewrite interpV_bind //|]; ired.
          eapply gsim_s_cgetU_src;
            [rewrite list_lookup_insert // length_fmap //
            |ss; rewrite String.eqb_refl //
            |].
          esplits; eauto.
          rewrite list_insert_insert.
          rewrite Hmtid; des_ifs_safe; ss. clear e. ired.

          rewrite interpV_bind interpV_trigger /=. ired.
          eapply gsim_Choose_src;
            [rewrite list_lookup_insert //= length_fmap //
            |unshelve eexists].
          { exists (mtid, stid); ss; rewrite list_lookup_fmap Hmtid //=. }
          rewrite list_insert_insert. ired.

          ired. replace_l; [rewrite interpV_bind //|]. ired.
          eapply gsim_s_cput_src; [rewrite list_lookup_insert // length_fmap //| |]; s.
          { rewrite String.eqb_refl //. }
          rewrite ?list_insert_insert.
          rewrite /alist_upd /=; destruct (dec _ _) as [e2|e2]; ss; clarify; clear e2.

          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l. rewrite list_insert_insert. ired.
          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l. rewrite list_insert_insert. ired.

          rewrite ?interpV_ret; ired.
          iter_l; rewrite list_lookup_insert //=; [|rewrite length_fmap //].
          step_l; norm_l. rewrite list_insert_insert.

          replace_r; [rewrite interpV_bind HoareCall_epilogue_sred //|].
          eapply gsim_HoareCall_epilogue_both;
            [rewrite list_lookup_insert // length_fmap //
            |rewrite list_lookup_insert // length_fmap //
            |ss
            |].
          clear dependent res1 res2.
          intros res1 x1 Hres1. ired. rewrite ?list_insert_insert.
          rewrite ?interpV_ret. ired.

          rewrite yield_unfold; ired.
          rewrite interpV_tau.
          eapply gsim_tau_src;
            [rewrite list_lookup_insert // length_fmap //
            |rewrite list_insert_insert].
          rewrite interpV_bind interpV_vis /=; ired.
          eapply gsim_Choose_src;
            [rewrite list_lookup_insert // length_fmap //
            |exists None; rewrite list_insert_insert].
          ired. rewrite interpV_ret. ired. rewrite ?interpV_ret. ired.

          gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
          gbase. eapply (CIH res1); eauto.
          eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. }
          }
          Unshelve. all: try exact smj_bot; eauto.
        }

        (* Going to helpee *)
        destruct (reqmap !! rid) as [[[|] jid]|] eqn : Hrid; ss. hss.
        pose proof Hrid as Hrid'.
        eapply reqmap_rel_Some_2 in Hrid' as [stid_helpee [i_s [i_t Hhelpee]]]; eauto.

        eapply Hlookup in Hhelpee as Hhelpee'.
        destruct Hhelpee' as [Hhelpee' [mtid_helpee Hthshelpee]].
        inv Hhelpee'; des; clarify.
        eapply lookup_lt_Some in Hhelpee as Hhelpeelen.
        assert (Hneq : stid_helpee ≠ stid) by (ii; clarify).

        ired.
        rewrite interpV_bind interpV_trigger /=. ired.
        eapply gsim_Choose_src;
          [rewrite list_lookup_insert //= length_fmap //
          |unshelve eexists].
        { exists (mtid_helpee, stid_helpee). rewrite /= list_lookup_fmap Hthshelpee //. }
        rewrite list_insert_insert; ired.

        ired. replace_l; [rewrite interpV_bind //|]. ired.
        eapply gsim_s_cput_src; [rewrite list_lookup_insert // length_fmap //| |]; s.
        { rewrite String.eqb_refl //. }
        rewrite ?list_insert_insert.
        rewrite /alist_upd /=; destruct (dec _ _) as [e2|e2]; ss; clarify; clear e e2.

        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
        rewrite list_insert_insert. ired.

        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
        rewrite list_insert_insert. ired. rewrite ?interpV_ret. ired.

        iter_l. rewrite list_lookup_insert_ne //=.
        rewrite list_lookup_fmap Hhelpee /=.
        step_l; norm_l.

        replace_r; [rewrite interpV_bind HoareFun_prologue_sred //|].
        eapply gsim_HoareCall_epilogue_HoareFun_prologue;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |rewrite list_lookup_insert // length_fmap; repeat f_equal; grind
          |ss
          |].
        clear dependent res1.
        intros res1 x1 Hres1. ired. rewrite ?list_insert_insert.

        rewrite {1}yield_unfold. ired.
        rewrite interpV_tau.
        eapply gsim_tau_src;
          [rewrite list_lookup_insert // length_insert length_fmap //|rewrite list_insert_insert].
        rewrite interpV_bind interpV_vis /=; ired.
        eapply gsim_Choose_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |exists None; rewrite list_insert_insert].
        ired. rewrite interpV_ret. ired.

        (* target proceed for helping *)
        rewrite /HelpingOn.try_run /cgetU; ired.
        replace_r; [rewrite interpV_bind interpV_vis //|]; ired.
        eapply gsim_sGet_tgt; [rewrite list_lookup_insert // length_fmap //| ss |].
        { rewrite String.eqb_refl //. }
        esplits; ss; [destruct (dec _ _); ss; clarify|].
        rewrite list_insert_insert. ired. rewrite ?interpV_ret; ired. hss. ired.

        rewrite Hrid. ired.
        eapply gsim_jobs_both;
          [rewrite length_insert length_fmap //
          |rewrite length_fmap //
          |ss
          |].
        clear dependent res1; intros res1 ret1 Hres1.

        ired; replace_r; [rewrite interpV_bind //|]. ired.
        eapply gsim_s_cput_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
        { rewrite String.eqb_refl //. }
        rewrite ?list_insert_insert.
        rewrite /alist_upd /=; destruct (dec _ _) as [e|e]; ss; clarify; clear e.

        rewrite yield_unfold; ired.
        rewrite interpV_tau.
        eapply gsim_tau_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |rewrite list_insert_insert].
        rewrite interpV_bind interpV_vis /=; ired.
        eapply gsim_Choose_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |exists (Some true); rewrite list_insert_insert].
        ired. rewrite interpV_ret; ired. rewrite ?interpV_ret; ired.

        iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
        step_l; norm_l; rewrite list_insert_insert.

        rewrite HoareCall_unfold; ired.
        replace_r; [rewrite interpV_bind HoareFun_epilogue_sred //|].
        eapply gsim_HoareCall_prologue_HoareFun_epilogue;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |rewrite list_lookup_insert // length_fmap //
          |ss|].
        clear dependent res1. intros res1 ret Hres1.
        rewrite ?list_insert_insert. ired.

        iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
        step_l; norm_l; rewrite {1}/LMod.prog /=.
        destruct (dec _ _) as [?|e']; ss; [exfalso; hexploit yield_run_neq; ii; clarify|].
        clear e'.
        destruct (dec _ _) as [?|e]; [exfalso; hexploit yield_help_neq; ii; clarify|ss; clear e].
        norm_l. rewrite list_insert_insert.

        unfold_trans.
        eapply gsim_tau_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |rewrite list_insert_insert].
        rewrite /SchI.yield /cfunU.
        destruct (ret ↓) as [[]|] eqn : Hret; cycle 1.
        { ss; iter_l; rewrite list_lookup_insert; [|rewrite length_insert length_fmap //].
          ss; destruct (excluded_middle_informative _); step_l; ss.
        }
        ired. clear Hret.

        ired. replace_l; [rewrite interpV_bind //|]; ired.
        eapply gsim_s_cgetU_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |ss; rewrite String.eqb_refl //
          |].
        esplits; eauto.
        rewrite list_insert_insert.

        iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
        step_l; norm_l. rewrite list_insert_insert.
        iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
        step_l; norm_l. rewrite list_insert_insert; ired.

        ired. replace_l; [rewrite interpV_bind //|]; ired.
        eapply gsim_s_cgetU_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |ss; rewrite String.eqb_refl //
          |].
        esplits; eauto.
        rewrite list_insert_insert.

        rewrite Hthshelpee; case_decide as H'; ss; clear H'. ired.

        rewrite interpV_bind interpV_trigger /=. ired.
        eapply gsim_Choose_src;
          [rewrite list_lookup_insert //= length_insert length_fmap //
          |unshelve eexists].
        { exists (mtid, stid); ss; rewrite list_lookup_fmap Hmtid //=. }
        rewrite list_insert_insert. ired.

        ired. replace_l; [rewrite interpV_bind //|]. ired.
        eapply gsim_s_cput_src; [rewrite list_lookup_insert // length_insert length_fmap //| |]; s.
        { rewrite String.eqb_refl //. }
        rewrite ?list_insert_insert.

        iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
        step_l; norm_l. rewrite list_insert_insert. ired.
        iter_l; rewrite list_lookup_insert //=; [|rewrite length_insert length_fmap //].
        step_l; norm_l. rewrite list_insert_insert. ired.
        rewrite ?interpV_ret; ired.

        iter_l; rewrite list_lookup_insert_ne //=.
        rewrite list_lookup_insert /=; [|rewrite length_fmap //].
        step_l; norm_l.
        rewrite list_insert_commute //.
        rewrite list_insert_insert.
        rewrite list_insert_commute //.

        replace_r; [rewrite interpV_bind HoareCall_epilogue_sred //|].
        eapply gsim_HoareCall_epilogue_both;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |rewrite list_lookup_insert // length_fmap //
          |ss
          |].
        clear dependent res1 x1.
        intros res1 x1 Hres1. ired. rewrite ?list_insert_insert.
        rewrite ?interpV_ret. ired.

        replace_l; [rewrite interpV_tau //|]; ired.
        eapply gsim_tau_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |rewrite list_insert_insert].
        rewrite interpV_bind interpV_vis /=; ired.

        eapply gsim_Choose_src;
          [rewrite list_lookup_insert // length_insert length_fmap //
          |exists None; rewrite list_insert_insert].
        ired. rewrite interpV_ret. ired. rewrite ?interpV_ret. ired.

        rewrite /alist_upd /=; destruct (dec _ _); ss; clear e.
        apply gsim_flag.
        gbase. eapply (CIH res1); eauto.
        set (i_helpee := tau;; _).
        eexists (<[stid := (ktr_s1 () ↑, ktr_t1 () ↑, None)]>
          (<[stid_helpee := (i_helpee, _, Some (rid, (_, jid)))]> tl)).
        esplits; eauto.
        { rewrite ?list_fmap_insert //=. }
        { rewrite ?list_fmap_insert //=.
          do 2 f_equal. rewrite list_insert_id //. rewrite list_lookup_fmap Hhelpee //.
        }
        { rewrite list_insert_commute //.
          eapply reqmap_rel_delete_true_2; eauto.
          { rewrite list_lookup_insert_ne //. }
          eapply reqmap_rel_id; eauto.
        }
        { intros i; destruct (decide (i = stid)).
          { subst; intros ??? Hin; rewrite list_lookup_insert in Hin; ss; clarify.
            rewrite length_insert //.
          }
          destruct (decide (i = stid_helpee)).
          { subst; intros ??? Hin; rewrite list_lookup_insert_ne // list_lookup_insert // in Hin.
            clarify; split; ss.
            eapply help_rel_helpee_done; eauto.
            esplits; eauto.
          }
          intros ??? Hin; rewrite ?list_lookup_insert_ne // in Hin; eapply Hlookup; eauto.
        }
      }

      destruct (decide (fn = SchHdr._spawn)); subst.
      { (* SchI.inner_spawn *)
        rewrite {1 2}/LMod.prog ?alist_find_map_snd /=.
        destruct (dec _ _) as [?|e]; ss; [inv e; clear e|clarify; clear e].
        destruct (dec _ _) as [e|e]; ss; [inv e; clear e|clarify; clear e].
        i; clarify.

        revert Htid; unfold_trans; rewrite /SModTr.trans /SchI.inner_spawn.
        intros Hstid.

        eapply gsim_tau_src; [rewrite list_lookup_fmap // Hstid //=|].
        eapply gsim_tau_tgt; [rewrite list_lookup_fmap // Hstid //=|].
        zprogress.

        rewrite /cfunU.
        destruct (arg ↓) as [[fn args]|] eqn : Harg; ss; ired; cycle 1.
        { replace_l; [rewrite interpV_bind interpV_trigger //|].
          eapply gsim_Take_src;
            [rewrite list_lookup_insert // ?length_fmap //; repeat f_equal; grind
            |intros x ?].
          rewrite list_insert_insert; ss.
        }
        clear Harg.
        rewrite /ccallU. ired.

        iter_l; iter_r; rewrite ?list_lookup_insert //= ?length_fmap; ss.
        step_l; step_r. norm_l; norm_r.
        rewrite ?list_insert_insert.

        destruct ((wmask_and msk wmask_all) fn) eqn : Hfn; cycle 1.
        { iter_l; rewrite list_lookup_insert /=; [rewrite Hfn /=|rewrite length_fmap //].
          step_l; ss.
        }

        iter_l; rewrite ?list_lookup_insert /=; last rewrite ?length_fmap //. rewrite Hfn /=.
        iter_r; rewrite ?list_lookup_insert /=; last rewrite ?length_fmap //. rewrite Hfn /=.
        step_l; step_r. norm_l; norm_r.
        destruct (prog_s ctx rs fn) eqn : Hfn_s; cycle 1.
        { step_l; ss. }
        destruct (prog_t ctx rs fn) eqn : Hfn_t; cycle 1.
        { eapply prog_s_prog_t in Hfn_s as Hfn_t'; des; clarify. }
        norm_l; norm_r.
        rewrite !list_insert_insert.
        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase.
        eapply (CIH rs); eauto.
        eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i1; destruct (decide (i1 = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. split; ss.
            destruct (decide (Some fn ∈
              List.map fst (Mod.fnsems ((HelpingOn.t mn jobs sp) ★ (CFilter.filter msk SchI.t))))).
            { eapply (help_rel_call _ _ _ _ _ _ ctx); eauto. intros ret; ss.
              eapply help_rel_inner_spawn; eauto.
              { rewrite /inner_spawn_pend; grind. instantiate (1:=ret); f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
              { rewrite /inner_spawn_pend; grind. f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
            }
            hexploit (prog_fn_ctx fn ctx rs); eauto.
            intros [Hs|[itr_ctx [img1 [msk1 [scp1 [Ht Hs]]]]]]; des; clarify.
            rewrite Ht Hs in Hfn_t; inv Hfn_t; ss.
            ides (itr_ctx args ↑).
            { rewrite ?interpV_ret; ired.
              eapply help_rel_inner_spawn; eauto.
              { rewrite /inner_spawn_pend; grind. f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
              { rewrite /inner_spawn_pend; grind. f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
            }
            { eapply (help_rel_eq); eauto.
              i; ss.
              eapply help_rel_inner_spawn; eauto.
              { rewrite /inner_spawn_pend; grind. instantiate (1:=ret); f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
              { rewrite /inner_spawn_pend; grind. f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
            }
            { eapply (help_rel_eq); eauto.
              i; ss.
              eapply help_rel_inner_spawn; eauto.
              { rewrite /inner_spawn_pend; grind. instantiate (1:=ret); f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
              { rewrite /inner_spawn_pend; grind. f_equal; grind.
                repeat f_equal; extensionalities a; grind.
              }
            }
          }
        }
      }

      destruct (decide (fn = SchHdr.spawn)); subst.
      { (* SchI.spawn *)
        rewrite {1 2}/LMod.prog ?alist_find_map_snd /=.
        destruct (dec _ _) as [?|e]; ss; [inv e; clear e|clarify; clear e].
        destruct (dec _ _) as [e|e]; ss; [inv e; clear e|clarify; clear e].
        i; clarify.

        revert Htid; unfold_trans; rewrite /SModTr.trans /SchI.spawn.
        intros Hstid.

        eapply gsim_tau_src; [rewrite list_lookup_fmap // Hstid //=|].
        eapply gsim_tau_tgt; [rewrite list_lookup_fmap // Hstid //=|].
        zprogress.

        rewrite /cfunU.
        destruct (arg ↓) as [[fn args]|] eqn : Harg; ss; ired; cycle 1.
        { replace_l; [rewrite interpV_bind interpV_trigger //|].
          eapply gsim_Take_src;
            [rewrite list_lookup_insert // ?length_fmap //; repeat f_equal; grind
            |intros x ?].
          rewrite list_insert_insert; ss.
        }
        clear Harg.
        rewrite /ccallU.

        ired. replace_l; [rewrite interpV_bind //|]; ired.
        eapply gsim_s_cgetU_src;
          [rewrite list_lookup_insert // length_fmap //
          |ss; rewrite String.eqb_refl //
          |].
        esplits; eauto.
        rewrite list_insert_insert.

        ired. replace_r; [rewrite interpV_bind //|]; ired.
        eapply gsim_s_cgetU_tgt;
          [rewrite list_lookup_insert // length_fmap //
          |ss; rewrite String.eqb_refl //
          |].
        esplits; eauto.
        rewrite list_insert_insert. ired.

        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
        rewrite list_insert_insert.
        iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
        rewrite list_insert_insert. ired.
        rewrite /SModTr.NativeSpawn; ired.

        destruct ((wmask_and msk wmask_all) SchHdr._spawn) eqn : Hfn; cycle 1.
        {
          iter_l; rewrite list_lookup_insert /=; [rewrite Hfn /=|rewrite length_fmap //].
          step_l; ss.
        }

        iter_l; rewrite ?list_lookup_insert /=; last rewrite ?length_fmap //. rewrite Hfn /=.
        iter_r; rewrite ?list_lookup_insert /=; last rewrite ?length_fmap //. rewrite Hfn /=.
        step_l; step_r. norm_l; norm_r.
        destruct (prog_s ctx rs SchHdr._spawn) eqn : Hfn_s; cycle 1.
        { step_l; ss. }
        destruct (prog_t ctx rs SchHdr._spawn) eqn : Hfn_t; cycle 1.
        { eapply prog_s_prog_t in Hfn_s as Hfn_t'; des; clarify. }
        norm_l; norm_r.
        rewrite !list_insert_insert. ired.

        ired. replace_r; [rewrite interpV_bind //|]. ired.
        eapply gsim_s_cput_tgt; s.
        { rewrite lookup_app list_lookup_insert // length_fmap //. }
        { ss. }
        rewrite insert_app_l // ?length_insert ?length_fmap //.
        rewrite /alist_upd /=; destruct (dec _ _) as [e|e]; ss; clarify; clear e.

        ired. replace_l; [rewrite interpV_bind //|]. ired.
        eapply gsim_s_cput_src; s.
        { rewrite lookup_app list_lookup_insert // length_fmap //. }
        { ss. }
        rewrite insert_app_l // ?length_insert ?length_fmap //.
        rewrite /alist_upd /=; destruct (dec _ _) as [e|e]; ss; clarify; clear e.
        rewrite ?list_insert_insert.
        rewrite ?interpV_ret. ired.

        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase.
        eapply (CIH rs); eauto.
        eexists ((<[stid := (_, _, None)]> tl) ++ [(i (fn, args)↑, i0 (fn, args)↑, None)]); ss.
        esplits; eauto.
        { rewrite ?fmap_app list_fmap_insert //=. }
        { rewrite ?fmap_app list_fmap_insert //=. }
        { eapply reqmap_rel_append; eauto.
          eapply reqmap_rel_id; eauto.
        }
        { intros i1; destruct (decide (i1 = length tl)); subst.
          { intros ???; rewrite lookup_app_r // ?length_insert; try lia.
            rewrite Nat.sub_diag /=; intros Heq; inv Heq.
            split; ss.
            eapply (help_rel_call _ _ _ _ (λ a, Ret a) (λ a, Ret a) ctx rs SchHdr._spawn); eauto.
            { rewrite /HelpingOn.t /SchI.t; unseal CRIS; ss; set_solver. }
            { grind. }
            { grind. }
            intros res; eapply help_rel_ret; eauto.
          }
          destruct (decide (i1 = stid)); subst.
          { intros ???; rewrite -insert_app_l // list_lookup_insert // ?length_app; try lia.
            intros EQ; clarify.
          }
          rewrite -insert_app_l // list_lookup_insert_ne //.
          intros ??? [[Hilen Hi]|[??]]%lookup_snoc_Some; last clarify.
          eapply Hlookup in Hi; des; split; eauto.
          destruct no; eauto. des; eexists _, _; rewrite lookup_app_l //.
          eapply lookup_lt_Some; eauto.
        }
      }

      destruct (decide (fn = SchHdr.join)); subst.
      { (* SchI.join *)
        rewrite {1 2}/LMod.prog ?alist_find_map_snd /=.
        destruct (dec _ _) as [?|e]; ss; [inv e; clear e|clarify; clear e].
        destruct (dec _ _) as [e|e]; ss; [inv e; clear e|clarify; clear e].
        i; clarify.

        revert Htid; unfold_trans; rewrite /SModTr.trans /SchI.join.
        intros Hstid.

        eapply gsim_tau_src; [rewrite list_lookup_fmap // Hstid //=|].
        eapply gsim_tau_tgt; [rewrite list_lookup_fmap // Hstid //=|].
        zprogress.

        rewrite /cfunU.
        destruct (arg ↓) as [?|] eqn : Harg; ss; ired; cycle 1.
        { replace_l; [rewrite interpV_bind interpV_trigger //|].
          eapply gsim_Take_src;
            [rewrite list_lookup_insert // ?length_fmap //; repeat f_equal; grind
            |intros x ?].
          rewrite list_insert_insert; ss.
        }
        clear Harg.
        rewrite unfold_iterC; ired.
        rewrite {1 2}interpV_tau.
        eapply gsim_tau_src; [rewrite list_lookup_insert // length_fmap //|].
        eapply gsim_tau_tgt; [rewrite list_lookup_insert // length_fmap //|].
        rewrite !list_insert_insert.

        replace_l; [rewrite interpV_bind //|]. ired.
        eapply gsim_s_cgetU_src; [rewrite list_lookup_insert // length_fmap //| |]; s.
        { rewrite String.eqb_refl //. }
        esplits; eauto.
        rewrite ?list_insert_insert. ired.

        replace_r; [rewrite interpV_bind //|]. ired.
        eapply gsim_s_cgetU_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
        { rewrite String.eqb_refl //. }
        esplits; eauto.
        rewrite ?list_insert_insert. ired.

        destruct (ths !! n3) as [[? [rv|]]|] eqn : Hret; rewrite Hret /=; ired.
        { (* Join-return *)
          rewrite ?interpV_ret; ired.
          gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
          gbase. eapply (CIH rs); eauto.
          eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i; destruct (decide (i = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify. }
          }
        }
        { (* Join-loop *)
          rewrite /ccallU.

          iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
          rewrite list_insert_insert.
          iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
          rewrite list_insert_insert. ired.

          destruct ((wmask_and msk wmask_all) SchHdr.yield) eqn : Hfn; cycle 1.
          { iter_l; rewrite list_lookup_insert /=; [rewrite Hfn /=|rewrite length_fmap //].
            step_l; ss.
          }

          iter_l; rewrite ?list_lookup_insert /=; last rewrite ?length_fmap //. rewrite Hfn /=.
          iter_r; rewrite ?list_lookup_insert /=; last rewrite ?length_fmap //. rewrite Hfn /=.
          step_l; step_r. norm_l; norm_r.
          destruct (prog_s ctx rs SchHdr.yield) eqn : Hfn_s; cycle 1.
          { step_l; ss. }
          destruct (prog_t ctx rs SchHdr.yield) eqn : Hfn_t; cycle 1.
          { eapply prog_s_prog_t in Hfn_s as Hfn_t'; des; clarify. }
          norm_l; norm_r.
          rewrite !list_insert_insert. ired.
          gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
          gbase. eapply (CIH rs); eauto.
          eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
          { rewrite list_fmap_insert //=. }
          { rewrite list_fmap_insert //=. }
          { eapply reqmap_rel_id; eauto. }
          { intros i1; destruct (decide (i1 = stid)); subst; cycle 1.
            { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
            { rewrite list_lookup_insert; ii; clarify.
              split; ss. eapply (help_rel_call _ _ _ _ _ _ ctx rs (SchHdr.yield)); eauto.
              { rewrite /HelpingOn.t /SchI.t; unseal CRIS; ss.
                do 4 (apply elem_of_cons; right); apply elem_of_cons; left; ss.
              }
              intros ret; ss; eapply (help_rel_join _ _ ret _ _ n3); eauto.
              { rewrite /join_pend /ccallU. grind. repeat f_equal; grind.
                extensionalities a; destruct a; grind.
              }
              { rewrite /join_pend /ccallU. grind. repeat f_equal; grind.
                extensionalities a; destruct a; grind.
              }
            }
          }
        }
        (* join-None *)
        rewrite ?interpV_ret; ired.
        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase. eapply (CIH rs); eauto.
        eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. }
        }
      }

      destruct (decide (fn = SchHdr.yield)); subst.
      { (* SchI.yield *)
        rewrite {1 2}/LMod.prog ?alist_find_map_snd /=.
        destruct (dec _ _) as [?|e]; ss; [inv e; clear e|clarify; clear e].
        destruct (dec _ _) as [e|e]; ss; [inv e; clear e|clarify; clear e].
        i; clarify.

        revert Htid; unfold_trans; rewrite /SModTr.trans /SchI.yield.
        intros Hstid.

        eapply gsim_tau_src; [rewrite list_lookup_fmap // Hstid //=|].
        eapply gsim_tau_tgt; [rewrite list_lookup_fmap // Hstid //=|].
        zprogress.

        rewrite /cfunU.
        destruct (arg ↓) eqn : Harg; cycle 1.
        { ss; iter_l; rewrite list_lookup_insert //= ?length_fmap //.
          destruct (excluded_middle_informative _); step_l; ss.
        }
        ss. ired. rewrite /cgetU /=. ired.

        replace_r; [rewrite interpV_bind interpV_vis //|]. ired.
        eapply gsim_sGet_tgt;
          [rewrite list_lookup_insert //= length_fmap //| ss | ].
        esplits; eauto. rewrite list_insert_insert.

        replace_l; [rewrite interpV_bind interpV_vis //|]. ired.
        eapply gsim_sGet_src;
          [rewrite list_lookup_insert //= length_fmap //| ss | ].
        esplits; eauto. rewrite list_insert_insert.
        rewrite ?interpV_ret. ired. hss. ired. rewrite ?interpV_ret. ired. hss. ired.

        iter_l; rewrite list_lookup_insert //= ?length_fmap //. step_l; norm_l.
        rewrite list_insert_insert.
        iter_r; rewrite list_lookup_insert //= ?length_fmap //; step_r; norm_r.
        rewrite list_insert_insert.

        iter_l; rewrite list_lookup_insert //= ?length_fmap //. step_l; norm_l.
        rewrite list_insert_insert.
        iter_r; rewrite list_lookup_insert //= ?length_fmap //; step_r; norm_r.
        rewrite list_insert_insert. ired.

        replace_r; [rewrite interpV_bind interpV_vis //|]. ired.
        eapply gsim_sGet_tgt;
          [rewrite list_lookup_insert //= length_fmap //| ss | ].
        esplits; eauto. rewrite list_insert_insert.

        replace_l; [rewrite interpV_bind interpV_vis //|]. ired.
        eapply gsim_sGet_src;
          [rewrite list_lookup_insert //= length_fmap //| ss | ].
        esplits; eauto. rewrite list_insert_insert.
        rewrite ?interpV_ret. ired. hss. ired. rewrite ?interpV_ret. ired. hss. ired.

        destruct (ths !! mtid) as [[smtid reto_s]|] eqn : Hmtid; cycle 1.
        { rewrite Hmtid /=.
          ss; iter_l; rewrite list_lookup_insert //= ?length_fmap //.
          destruct (excluded_middle_informative _); step_l; ss.
        }
        rewrite Hmtid //=.
        destruct (decide (smtid = stid)); subst; cycle 1.
        { ss; iter_l; rewrite list_lookup_insert //= ?length_fmap //.
          destruct (excluded_middle_informative _); step_l; ss.
        }

        ired.

        replace_r; [rewrite interpV_bind interpV_trigger //=|]; ired.
        eapply gsim_Choose_tgt; [rewrite list_lookup_insert // length_fmap //|].
        intros [[mtidn stidn] Hmtidn]; rewrite list_insert_insert; ired; ss.

        replace_l; [rewrite interpV_bind interpV_trigger //=|]; ired.
        eapply gsim_Choose_src; [rewrite list_lookup_insert // length_fmap //|].
        unshelve eexists (exist _ (mtidn, stidn) _); ss; eauto.
        rewrite list_insert_insert; ired; ss.

        ired. replace_r; [rewrite interpV_bind //|]. ired.
        eapply gsim_s_cput_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
        { rewrite String.eqb_refl //. }
        rewrite ?list_insert_insert.
        rewrite /alist_upd /=; destruct (dec _ _) as [e|e]; ss; clarify; clear e.

        ired. replace_l; [rewrite interpV_bind //|]. ired.
        eapply gsim_s_cput_src; [rewrite list_lookup_insert // length_fmap //| |]; s.
        { rewrite String.eqb_refl //. }
        rewrite ?list_insert_insert.
        rewrite /alist_upd /=; destruct (dec _ _) as [e|e]; ss; clarify; clear e.

        iter_l; rewrite list_lookup_insert //= ?length_fmap //. step_l; norm_l.
        rewrite list_insert_insert. hss.
        iter_l; rewrite list_lookup_insert //= ?length_fmap //. step_l; norm_l.
        rewrite list_insert_insert. hss. ired. rewrite ?interpV_ret. ired.

        iter_r; rewrite list_lookup_insert //= ?length_fmap //. step_r; norm_r.
        rewrite list_insert_insert. hss.
        iter_r; rewrite list_lookup_insert //= ?length_fmap //. step_r; norm_r.
        rewrite list_insert_insert. hss. ired. rewrite ?interpV_ret. ired.

        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase. eapply (CIH rs); eauto.
        eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. }
        }
      }

      destruct (decide (fn = SchHdr.get_tid)); subst.
      { (* SchI.get_tid *)
        rewrite {1 2}/LMod.prog ?alist_find_map_snd /=.
        destruct (dec _ _) as [?|e]; ss; [inv e; clear e|clarify; clear e].
        destruct (dec _ _) as [e|e]; ss; [inv e; clear e|clarify; clear e].
        i; clarify.

        revert Htid; unfold_trans; rewrite /SModTr.trans /SchI.get_tid.
        intros Hstid.

        eapply gsim_tau_src; [rewrite list_lookup_fmap // Hstid //=|].
        eapply gsim_tau_tgt; [rewrite list_lookup_fmap // Hstid //=|].
        zprogress.

        rewrite /cfunU.
        destruct (arg ↓) eqn : Harg; cycle 1.
        { ss; iter_l; rewrite list_lookup_insert //= ?length_fmap //.
          destruct (excluded_middle_informative _); step_l; ss.
        }
        ss. ired. rewrite /cgetU /=. ired.

        replace_r; [rewrite interpV_bind interpV_vis //|]. ired.
        eapply gsim_sGet_tgt;
          [rewrite list_lookup_insert //= length_fmap //| ss | ].
        esplits; eauto. rewrite list_insert_insert.

        replace_l; [rewrite interpV_bind interpV_vis //|]. ired.
        eapply gsim_sGet_src;
          [rewrite list_lookup_insert //= length_fmap //| ss | ].
        esplits; eauto. rewrite list_insert_insert.
        rewrite ?interpV_ret. ired. hss. ired. rewrite ?interpV_ret. ired. hss. ired.
        rewrite ?interpV_ret; ired.

        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase. eapply (CIH rs); eauto.
        eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. }
        }
      }

      exfalso; revert H1; rewrite /HelpingOn.t /SchI.t; unseal CRIS; ss.
      set_solver.
    }

    { (* inner spawn - continuation *)
      rewrite /inner_spawn_pend in Htid.
      iter_l; rewrite list_lookup_fmap Htid /=. step_l; norm_l.
      iter_r; rewrite list_lookup_fmap Htid /=. step_r; norm_r.

      destruct (arg ↓) eqn : Harg; ss; cycle 1.
      { ired; replace_l; [rewrite interpV_bind interpV_trigger //|]. ired.
        eapply gsim_Take_src; [rewrite list_lookup_insert // length_fmap //|]. ss.
      }

      ired.
      replace_r; [rewrite interpV_bind //|]. ired.
      eapply gsim_s_cgetU_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
      { rewrite String.eqb_refl //. }
      esplits; eauto.
      rewrite ?list_insert_insert. ired.

      ired.
      replace_r; [rewrite interpV_bind //|]. ired.
      eapply gsim_s_cgetU_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
      { rewrite String.eqb_refl //. }
      esplits; eauto.
      rewrite ?list_insert_insert. ired.

      ired.
      replace_l; [rewrite interpV_bind //|]. ired.
      eapply gsim_s_cgetU_src; [rewrite list_lookup_insert // length_fmap //| |]; s.
      { rewrite String.eqb_refl //. }
      esplits; eauto.
      rewrite ?list_insert_insert. ired.

      ired.
      replace_l; [rewrite interpV_bind //|]. ired.
      eapply gsim_s_cgetU_src; [rewrite list_lookup_insert // length_fmap //| |]; s.
      { rewrite String.eqb_refl //. }
      esplits; eauto.
      rewrite ?list_insert_insert. ired.

      des_ifs; cycle 1.
      { ired; replace_l; [rewrite interpV_bind interpV_trigger //|]. ired.
        eapply gsim_Take_src; [rewrite list_lookup_insert // length_fmap //|]. ss.
      }

      ired.
      replace_r; [rewrite interpV_bind //|]. ired.
      eapply gsim_s_cput_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
      { rewrite String.eqb_refl //. }
      rewrite ?list_insert_insert. ired.

      ired.
      replace_l; [rewrite interpV_bind //|]. ired.
      eapply gsim_s_cput_src; [rewrite list_lookup_insert // length_fmap //| |]; s.
      { rewrite String.eqb_refl //. }
      rewrite ?list_insert_insert. ired.

      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH rs); eauto.
      eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros stid2; destruct (decide (stid2 = stid)); subst; cycle 1.
        { intros itr_s2 itr_t2 no2; rewrite list_lookup_insert_ne //=.
          intros Hi; pose proof Hi as Hi'; revert Hi'; intros [Hi1 Hi2]%Hlookup; split; eauto.
          destruct no2 as [[tid2 [b2 jid2]]|]; ss.
          destruct Hi2 as [mtid2 [ro2 Hi2]]; apply lookup_lt_Some in Hi2 as Hlen2.
          destruct (decide (mtid2 = mtid)); subst.
          { rewrite Hi2 in Heq; clarify. exists mtid, (Some t); rewrite list_lookup_insert //. }
          exists mtid2, ro2; rewrite list_lookup_insert_ne //.
        }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          eapply help_rel_terminate; eauto.
        }
      }
    }

    { (* join - continuation*)
      rewrite /join_pend in Htid.
      iter_l; rewrite list_lookup_fmap Htid /=. step_l; norm_l.
      iter_r; rewrite list_lookup_fmap Htid /=. step_r; norm_r.

      destruct (arg ↓) eqn : Harg; ss; cycle 1.
      { ired; replace_l; [rewrite interpV_bind interpV_trigger //|]. ired.
        eapply gsim_Take_src; [rewrite list_lookup_insert // length_fmap //|]. ss.
      }

      ired.
      rewrite unfold_iterC; ired.
      rewrite {1 2}interpV_tau.
      eapply gsim_tau_src; [rewrite list_lookup_insert // length_fmap //|].
      eapply gsim_tau_tgt; [rewrite list_lookup_insert // length_fmap //|].
      rewrite !list_insert_insert.

      replace_l; [rewrite interpV_bind //|]. ired.
      eapply gsim_s_cgetU_src; [rewrite list_lookup_insert // length_fmap //| |]; s.
      { rewrite String.eqb_refl //. }
      esplits; eauto.
      rewrite ?list_insert_insert. ired.

      replace_r; [rewrite interpV_bind //|]. ired.
      eapply gsim_s_cgetU_tgt; [rewrite list_lookup_insert // length_fmap //| |]; s.
      { rewrite String.eqb_refl //. }
      esplits; eauto.
      rewrite ?list_insert_insert. ired.

      destruct (ths !! tid) as [[? [rv|]]|] eqn : Hret; rewrite Hret /=; ired.
      { (* Join-return *)
        rewrite ?interpV_ret; ired.
        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase. eapply (CIH rs); eauto.
        eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. }
        }
      }
      { (* Join-loop *)
        rewrite /ccallU.

        iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
        rewrite list_insert_insert.
        iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
        rewrite list_insert_insert. ired.

        destruct ((wmask_and msk wmask_all) SchHdr.yield) eqn : Hfn; cycle 1.
        { iter_l; rewrite list_lookup_insert /=; [rewrite Hfn /=|rewrite length_fmap //].
          step_l; ss.
        }

        iter_l; rewrite ?list_lookup_insert /=; last rewrite ?length_fmap //. rewrite Hfn /=.
        iter_r; rewrite ?list_lookup_insert /=; last rewrite ?length_fmap //. rewrite Hfn /=.
        step_l; step_r. norm_l; norm_r.
        destruct (prog_s ctx rs SchHdr.yield) eqn : Hfn_s; cycle 1.
        { step_l; ss. }
        destruct (prog_t ctx rs SchHdr.yield) eqn : Hfn_t; cycle 1.
        { eapply prog_s_prog_t in Hfn_s as Hfn_t'; des; clarify. }
        norm_l; norm_r.
        rewrite !list_insert_insert. ired.
        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase. eapply (CIH rs); eauto.
        eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i1; destruct (decide (i1 = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify.
            split; ss. eapply (help_rel_call _ _ _ _ _ _ ctx rs (SchHdr.yield)); eauto.
            { rewrite /HelpingOn.t /SchI.t; unseal CRIS; ss.
              do 4 (apply elem_of_cons; right); apply elem_of_cons; left; ss.
            }
            intros ret; ss; eapply (help_rel_join _ _ ret _ _ tid); eauto.
            { rewrite /join_pend /ccallU. grind. repeat f_equal; grind.
              extensionalities a; destruct a; grind.
            }
            { rewrite /join_pend /ccallU. grind. repeat f_equal; grind.
              extensionalities a; destruct a; grind.
            }
          }
        }
      }
      (* join-None *)
      rewrite ?interpV_ret; ired.
      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH rs); eauto.
      eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. }
      }
    }

    { (* inner_spawn - continuation*)
      revert Htid; rewrite /Sch.terminate; unseal SCH; rewrite unfold_iterC. ired.
      rewrite {1 2}interpV_tau; intros Htid.
      eapply gsim_tau_src; [rewrite list_lookup_fmap Htid //|].
      eapply gsim_tau_tgt; [rewrite list_lookup_fmap Htid //|].

      iter_l. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_l. norm_l.
      rewrite list_insert_insert.
      iter_r. rewrite list_lookup_insert /=; [|rewrite length_fmap //]. step_r. norm_r.
      rewrite list_insert_insert. ired.

      destruct ((wmask_and msk wmask_all) SchHdr.yield) eqn : Hfn; cycle 1.
      { iter_l; rewrite list_lookup_insert /=; [rewrite Hfn /=|rewrite length_fmap //].
        step_l; ss.
      }

      iter_l; rewrite ?list_lookup_insert /=; last rewrite ?length_fmap //. rewrite Hfn /=.
      iter_r; rewrite ?list_lookup_insert /=; last rewrite ?length_fmap //. rewrite Hfn /=.
      step_l; step_r. norm_l; norm_r.
      destruct (prog_s ctx rs SchHdr.yield) eqn : Hfn_s; cycle 1.
      { step_l; ss. }
      destruct (prog_t ctx rs SchHdr.yield) eqn : Hfn_t; cycle 1.
      { eapply prog_s_prog_t in Hfn_s as Hfn_t'; des; clarify. }
      norm_l; norm_r.
      rewrite !list_insert_insert. ired.
      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH rs); eauto.
      eexists (<[stid := (_, _, None)]> tl); esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i1; destruct (decide (i1 = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify.
          split; ss.
          eapply (help_rel_call _ _ _ _ _ _ ctx rs (SchHdr.yield)); eauto.
          { rewrite /HelpingOn.t /SchI.t; unseal CRIS; ss.
            do 4 (apply elem_of_cons; right); apply elem_of_cons; left; ss.
          }
          i; ss.
          eapply (help_rel_eq _ _ _ _ (tau;; Ret ret)).
          { unfold_trans; rewrite ?interpV_tau ?interpV_ret.
            instantiate (1:= λ x : Any.t,
              x <- ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes) (⇓smod(false, sp_none)
                (x <- Sch.terminate;; Ret x↑)));;
              ktr_t x).
            rewrite /Sch.terminate; unseal SCH. grind.
          }
          { unfold_trans; rewrite ?interpV_tau ?interpV_ret.
            instantiate (1:= λ x : Any.t,
              x <- ⇓cris (⇓sb(false, wmask_and msk wmask_all, SchI.scopes) (⇓smod(false, sp_none)
                (x <- Sch.terminate;; Ret x↑)));;
              ktr_s x).
            rewrite /Sch.terminate; unseal SCH. grind.
          }
          { instantiate (1:=[]); set_solver. }
          { ii; clarify. }
          i; ss.
          eapply help_rel_terminate; eauto.
        }
      }
    }

    { (* Return case *)
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      step_l; step_r; norm_l; norm_r.
      des_ifs; ss.
      { rewrite /LModTr.interp_stateE ?interp_state_ret; ired.
        gstep; econs; econs; ss.
      }
      rewrite /triggerUB; ss; step_l; ss.
    }

    rename itr into itr_c.
    rename H5 into Hscp.
    destruct (case_itrH itr_c) as [[v ->]|Hf].
    { (* return case *)
      exfalso; eapply H4; eauto.
    }
    destruct Hf as [[f' ->]|Hf].
    { (* tau case *)
      eapply gsim_tau_src; [rewrite list_lookup_fmap Htid //=; f_equal; grind|].
      eapply gsim_tau_tgt; [rewrite list_lookup_fmap Htid //=; f_equal; grind|].
      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply CIH; eauto.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          ides f'.
          { rewrite ?interpV_ret; ired; eauto. }
          { eapply help_rel_eq; eauto. }
          { eapply help_rel_eq; eauto. }
        }
      }
    }
    destruct Hf as [[P [f' ->]]|Hf].
    { (* Assume *)
      eapply gsim_Assume_src; [rewrite list_lookup_fmap Htid //=|].
      intros r_s2 -> Hr_s2.
      eapply gsim_Assume_tgt; [rewrite list_lookup_fmap Htid //=|].
      exists r_s2; esplits; try by des.
      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH r_s2); try by des.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          ides f'.
          { rewrite ?interpV_ret; ired; eauto. }
          { eapply help_rel_eq; eauto. }
          { eapply help_rel_eq; eauto. }
        }
      }
    }
    destruct Hf as [[res [f' ->]]|Hf].
    { (* AssumeRes *)
      eapply gsim_AssumeRes_src; [rewrite list_lookup_fmap Htid //=|].
      { unfold_trans. instantiate (1:=k_s). repeat f_equal. extensionalities a; destruct a; ss. }
      intros Hval.
      eapply gsim_AssumeRes_tgt; [rewrite list_lookup_fmap Htid //=|].
      { unfold_trans. instantiate (1:=k_t). repeat f_equal. extensionalities a; destruct a; ss. }
      split; first done.

      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH (res ⋅ rs)); try by des.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          ides (f' ()).
          { rewrite ?interpV_ret; ired; eauto. }
          { eapply help_rel_eq; eauto. }
          { eapply help_rel_eq; eauto. }
        }
      }
    }
    destruct Hf as [[P [f' ->]]|Hf].
    { (* Guarantee *)
      eapply gsim_Guarantee_tgt; [rewrite list_lookup_fmap Htid //=|].
      intros r2 ?.
      eapply gsim_Guarantee_src; [rewrite list_lookup_fmap Htid //=|].
      esplits; try by des.

      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH r2); try by des.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          ides (f').
          { rewrite ?interpV_ret; ired; eauto. }
          { eapply help_rel_eq; eauto. }
          { eapply help_rel_eq; eauto. }
        }
      }
    }
    destruct Hf as [[R [[fn args|fn args|tid_yield|] [k ->]]]|Hf].
    { (* call case *)
      rename msk0 into msk_c, img into img_c, scp into scp_c.
      revert Htid; unfold_trans; intros Htid.
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      ss; destruct (msk_c fn); cycle 1.
      { norm_l. step_l. ss. }
      ss.
      step_l. step_r. norm_l; norm_r.
      destruct (prog_s ctx rs fn) as [fn_s|] eqn : H_prog_s; cycle 1.
      { step_l; ss. }
      eapply prog_s_prog_t in H_prog_s as H_prog_t.
      destruct (prog_t ctx rs fn) as [fn_t|] eqn : H_prog_t'; cycle 1.
      { des; clarify. }
      norm_l; norm_r.

      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH rs); try by des.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss.
          destruct (decide (Some fn ∈
            List.map fst (Mod.fnsems ((HelpingOn.t mn jobs sp) ★ (CFilter.filter msk SchI.t))))).
          { eapply (help_rel_call _ _ _ _ _ _ ctx); eauto. intros ret; ss.
            eapply (help_rel_eq _ _ k_s k_t (tau;; k ret)); eauto.
            { grind. unfold_trans. rewrite ?interpV_tau; grind. }
            { grind. unfold_trans. rewrite ?interpV_tau; grind. }
          }
          hexploit (prog_fn_ctx fn ctx rs); eauto.
          intros [Hs|[itr_ctx [img1 [msk1 [scp1 [Ht [Hs ?]]]]]]]; clarify.
          rewrite Ht Hs in H_prog_t'; inv H_prog_t'.
          ides (itr_ctx args).
          { rewrite ?interpV_ret; ired.
            eapply (help_rel_eq _ _ k_s k_t (tau;; k r0) img_c msk_c scp_c); eauto.
            { unfold_trans. rewrite ?interpV_tau; grind. }
            { unfold_trans. rewrite ?interpV_tau; grind. }
          }
          { eapply (help_rel_eq _ _ _ _ (tau;; t)); eauto.
            ii; ss.
            eapply (help_rel_eq _ _ k_s k_t (tau;; k ret) img_c msk_c scp_c); eauto.
            { unfold_trans. rewrite ?interpV_tau; grind. }
            { unfold_trans. rewrite ?interpV_tau; grind. }
          }
          { eapply (help_rel_eq _ _ _ _ (Vis e k0)); eauto.
            ii; ss.
            eapply (help_rel_eq _ _ k_s k_t (tau;; k ret) img_c msk_c scp_c); eauto.
            { unfold_trans. rewrite ?interpV_tau; grind. }
            { unfold_trans. rewrite ?interpV_tau; grind. }
          }
        }
      }
      eauto.
    }
    { (* Spawn case *)
      rename img into img_c, msk0 into msk_c, scp into scp_c.
      revert Htid; rewrite /ModTr.trans /SB.sandbox; intros Htid.
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      destruct (msk_c fn); ss; cycle 1.
      { step_l; ss. }
      step_l. step_r. norm_l; norm_r.
      destruct (prog_s ctx rs fn) as [fn_s|] eqn : H_prog_s; cycle 1.
      { step_l; ss. }
      eapply prog_s_prog_t in H_prog_s as H_prog_t.
      destruct (prog_t ctx rs fn) as [fn_t|] eqn : H_prog_t'; cycle 1.
      { des; clarify. }
      norm_l; norm_r. ired.
      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH rs); try by des.
      eexists ((<[stid := (_, _, None)]> tl) ++ [(fn_s args, fn_t args, None)]); ss.
      esplits; eauto.
      { rewrite ?fmap_app list_fmap_insert //=. }
      { rewrite ?fmap_app list_fmap_insert //=. }
      { eapply reqmap_rel_append; eauto.
        eapply reqmap_rel_id; eauto.
      }
      { intros i; destruct (decide (i = length tl)); subst.
        { intros ???; rewrite lookup_app_r // ?length_insert; try lia.
          rewrite Nat.sub_diag /=; intros Heq; inv Heq.
          split; ss.
          destruct (decide (Some fn ∈
            List.map fst (Mod.fnsems ((HelpingOn.t mn jobs sp) ★ (CFilter.filter msk SchI.t))))).
          { eapply (help_rel_call _ _ _ _ (λ a, Ret a) (λ a, Ret a) ctx); eauto.
            { grind. }
            { grind. }
            intros ret; ss. apply help_rel_ret.
          }
          hexploit (prog_fn_ctx fn ctx rs); eauto.
          intros [Hs|[itr_ctx [img1 [msk1 [scp1 [Ht [Hs ?]]]]]]]; clarify.
          rewrite Ht Hs in H_prog_t'; inv H_prog_t'.
          ides (itr_ctx args).
          { rewrite ?interpV_ret; ired.
            apply help_rel_ret.
          }
          { eapply (help_rel_eq _ _ (λ a, Ret a) (λ a, Ret a) (tau;; t)); eauto.
            { grind. }
            { grind. }
            ii; apply help_rel_ret.
          }
          { eapply (help_rel_eq _ _ (λ a, Ret a) (λ a, Ret a) (Vis e k0)); eauto.
            { grind. }
            { grind. }
            ii; apply help_rel_ret.
          }
        }
        destruct (decide (i = stid)); subst.
        { intros ???; rewrite -insert_app_l // list_lookup_insert // ?length_app; try lia.
          intros EQ; clarify.
          split; ss.
          rewrite ?length_fmap.
          ides (k (length tl)).
          { rewrite ?interpV_ret; ired. eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (tau;; t)); eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (Vis e k0)); eauto. }
        }
        rewrite -insert_app_l // list_lookup_insert_ne //.
        intros ??? [[Hilen Hi]|[??]]%lookup_snoc_Some; last clarify.
        apply Hlookup; eauto.
      }
      eauto.
    }

    { (* Yield case *)
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      step_l; step_r. norm_l; norm_r.
      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH rs); try by des.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. ired. split; ss.
          ides (k ()).
          { rewrite ?interpV_ret; ired; eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (tau;; t)); eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (Vis e k0)); eauto. }
        }
      }
    }

    { (* GetTid case *)
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      step_l; step_r. norm_l; norm_r.
      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH rs); try by des.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss. ired.
          ides (k stid).
          { rewrite ?interpV_ret; ired; eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (tau;; t)); eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (Vis e k0)); eauto. }
        }
      }
    }

    destruct Hf as [[R [s [f' ->]]]|[R [e [f' ->]]]].
    { (* sput sget *)
      destruct s as [k v|k].
      { (* sput *)
        revert Htid; rewrite /SB.sandbox /ModTr.trans; intros Htid.
        iter_l; iter_r; rewrite ?list_lookup_fmap Htid //=.
        destruct (existsb _ scp) eqn : Hkscp; ss; cycle 1.
        { step_l; ss. }
        norm_l. step_l; norm_l.
        norm_r; step_r; norm_r. ired. hss. rewrite ?ModTr.alist_encode_decode.
        iter_l; iter_r; rewrite ?list_lookup_insert //= ?length_fmap //.
        step_l; step_r; norm_l; norm_r. ired.
        rewrite ?list_insert_insert.
        destruct (decide (k = SchI.v_ths)); subst.
        { exfalso. eapply existsb_exists in Hkscp as [? [Hin ?%String.eqb_eq]]; subst.
          revert Hscp Hin.
          rewrite /SchI.v_ths /=. intros Hscp Hin%elem_of_list_In.
          eapply elem_of_disjoint; eauto. eapply elem_of_cons; eauto.
        }
        destruct (decide (k = SchI.v_tid)); subst.
        { exfalso. eapply existsb_exists in Hkscp as [? [Hin ?%String.eqb_eq]]; subst.
          revert Hscp Hin.
          rewrite /SchI.v_tid /=. intros Hscp Hin%elem_of_list_In.
          eapply elem_of_disjoint; eauto. eapply elem_of_cons; eauto.
        }
        destruct (decide (k = HelpingOn.v_reqs mn)); subst.
        { exfalso. eapply existsb_exists in Hkscp as [? [Hin ?%String.eqb_eq]]; subst.
          revert Hscp Hin.
          rewrite /HelpingOn.v_reqs /= /HelpingOff.scopes. intros Hscp Hin%elem_of_list_In.
          eapply elem_of_disjoint; eauto. eapply elem_of_cons; right; eapply elem_of_cons; eauto.
        }
        rewrite /alist_upd /=; rewrite ?eq_rel_dec_correct; des_ifs.
        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase. eapply (CIH rs); try by des.
        eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. split; ss. ired.
            ides (f' ()).
            { rewrite ?interpV_ret; ired; eauto. }
            { eapply (help_rel_eq _ _ k_s k_t (tau;; t)); eauto. }
            { eapply (help_rel_eq _ _ k_s k_t (Vis e k0)); eauto. }
          }
        }
      }
      { (* sget *)
        revert Htid; rewrite /SB.sandbox /ModTr.trans; intros Htid.
        iter_l; iter_r; rewrite ?list_lookup_fmap Htid //=.
        destruct (existsb _ scp) eqn : Hkscp; ss; cycle 1.
        { step_l; ss. }
        norm_l. step_l; norm_l.
        norm_r; step_r; norm_r. ired. hss. rewrite ?ModTr.alist_encode_decode. ired.
        destruct (decide (k = SchI.v_ths)); subst.
        { exfalso. eapply existsb_exists in Hkscp as [? [Hin ?%String.eqb_eq]]; subst.
          revert Hscp Hin.
          rewrite /SchI.v_ths /=. intros Hscp Hin%elem_of_list_In.
          eapply elem_of_disjoint; eauto. eapply elem_of_cons; eauto.
        }
        destruct (decide (k = SchI.v_tid)); subst.
        { exfalso. eapply existsb_exists in Hkscp as [? [Hin ?%String.eqb_eq]]; subst.
          revert Hscp Hin.
          rewrite /SchI.v_tid /=. intros Hscp Hin%elem_of_list_In.
          eapply elem_of_disjoint; eauto. eapply elem_of_cons; eauto.
        }
        destruct (decide (k = HelpingOn.v_reqs mn)); subst.
        { exfalso. eapply existsb_exists in Hkscp as [? [Hin ?%String.eqb_eq]]; subst.
          revert Hscp Hin.
          rewrite /HelpingOn.v_reqs /= /HelpingOff.scopes. intros Hscp Hin%elem_of_list_In.
          eapply elem_of_disjoint; eauto. eapply elem_of_cons; right; eapply elem_of_cons; eauto.
        }
        rewrite /alist_upd /=; rewrite ?eq_rel_dec_correct; des_ifs.

        gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
        gbase. eapply (CIH rs); try by des.
        eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
        { rewrite list_fmap_insert //=. }
        { rewrite list_fmap_insert //=. }
        { eapply reqmap_rel_id; eauto. }
        { intros i; destruct (decide (i = stid)); subst; cycle 1.
          { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
          { rewrite list_lookup_insert; ii; clarify. split; ss. ired.
            ides (f' (or_else (alist_find k st_ctx) ()↑)).
            { rewrite ?interpV_ret; ired; eauto. }
            { eapply (help_rel_eq _ _ k_s k_t (tau;; t)); eauto. }
            { eapply (help_rel_eq _ _ k_s k_t (Vis e k0)); eauto. }
          }
        }
      }
    }

    destruct e as [X | X | fn args].
    { (* Choose case *)
      revert Htid; rewrite /SB.sandbox /ModTr.trans; intros Htid.
      eapply gsim_Choose_tgt;
        [rewrite ?list_lookup_fmap // Htid //=; instantiate (1:=λ a, Ret a); rewrite bind_ret_r //
        |intros x].
      eapply gsim_Choose_src;
        [rewrite ?list_lookup_fmap // Htid //=; instantiate (1:=λ a, Ret a); rewrite bind_ret_r //
        |exists x].
      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH rs); try by des.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss. ired.
          ides (f' x).
          { rewrite ?interpV_ret; ired; eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (tau;; t)); eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (Vis e k)); eauto. }
        }
      }
    }
    { (* Take case *)
      revert Htid; rewrite /SB.sandbox /ModTr.trans; intros Htid.
      eapply gsim_Take_src;
        [rewrite ?list_lookup_fmap // Htid //=; instantiate (1:=λ a, Ret a); rewrite bind_ret_r //
        |intros x ?].
      eapply gsim_Take_tgt;
        [rewrite ?list_lookup_fmap // Htid //=; instantiate (1:=λ a, Ret a); rewrite bind_ret_r //
        |exists x; split; ss].
      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH rs); try by des.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss. ired.
          ides (f' x).
          { rewrite ?interpV_ret; ired; eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (tau;; t)); eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (Vis e k)); eauto. }
        }
      }
    }
    { (* IO case *)
      iter_l; iter_r; rewrite ?list_lookup_fmap Htid /=.
      norm_l; norm_r. guclo gsim_indC_spec. econs; intros ?? ->.
      instantiate (1:=smj_top). instantiate (1:=smj_top).
      norm_l. norm_r. step_l. step_r. norm_l; norm_r. ired.
      gstep; econs; eapply gsim_progress; try instantiate (1:=smj_bot); eauto using smj_le_bot.
      gbase. eapply (CIH rs); try by des.
      eexists (<[stid := (_, _, None)]> tl); ss; esplits; eauto.
      { rewrite list_fmap_insert //=. }
      { rewrite list_fmap_insert //=. }
      { eapply reqmap_rel_id; eauto. }
      { intros i; destruct (decide (i = stid)); subst; cycle 1.
        { intros ???; rewrite list_lookup_insert_ne //=; apply Hlookup. }
        { rewrite list_lookup_insert; ii; clarify. split; ss. ired.
          ides (f' x_tgt).
          { rewrite ?interpV_ret; ired; eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (tau;; t)); eauto. }
          { eapply (help_rel_eq _ _ k_s k_t (Vis e k)); eauto. }
        }
      }
    }
  Unshelve. all: eauto.
  (*SLOW*)Qed.
End Helping.
