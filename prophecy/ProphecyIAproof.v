From stdpp Require Import base strings.
Require Import CRIS Common Mod LMod.
Require Import ProphecyHeader ProphecyI ProphecyA.
Require Import ExtendedBehavior SimGEx.
Require Import exco_stream.

Module ProphIA.

  Section ProphIA.
  Context `{_crisG: !crisG Γ Σ α β τ _I _S}.
  Context `{_prophG: !prophG}.

  Definition physical_smod (smd : SMod.t) : Prop :=
    Forall (fun entry => entry.2.2.1 = None /\ entry.2.1.1.1 = false) smd.(SMod.fnsems).

  Variable smds : list SMod.t.

  Hypothesis PHYS : Forall (fun smd => physical_smod smd) smds.

  Let md : Mod.t := Mod.addL (List.map (SMod.to_mod sp_none) smds).

  Variant _take_is_prop (coself : itree lmodE Any.t -> Prop) : itree lmodE Any.t -> Prop :=
  | take_is_prop_ret retv
  : _take_is_prop coself (Ret retv)

  | take_is_prop_tau itr
    (NEXT: coself itr)
  : _take_is_prop coself (tau;; itr)

  | take_is_prop_callE X (e : callE X) ktr
    (NEXT: forall x, coself (ktr x))
  : _take_is_prop coself (x <- trigger e;; ktr x)

  | take_is_prop_stateE X (e : stateE X) ktr
    (NEXT: forall x, coself (ktr x))
  : _take_is_prop coself (x <- trigger e;; ktr x)

  | take_is_prop_choose X ktr
    (NEXT: forall x, coself (ktr x))
  : _take_is_prop coself (x <- trigger (Choose X);; ktr x)

  | take_is_prop_take (X : Type) ktr
    (e : ∃ P : Prop, X = P)
    (NEXT: forall x : X, coself (ktr x))
  : _take_is_prop coself (p <- trigger (Take X);; ktr p)

  | take_is_prop_io I O fn (args : I) ktr
    (NEXT: forall o : O, coself (ktr o))
  : _take_is_prop coself (o <- trigger (IO fn args);; ktr o).

  Definition take_is_prop := paco1 _take_is_prop bot1.

  Lemma take_is_prop_mon : monotone1 _take_is_prop.
  Proof using.
    ii. destruct IN; des; eauto using _take_is_prop.
  Qed.

  Hint Unfold take_is_prop : core.
  Hint Constructors _take_is_prop : core.
  Hint Resolve take_is_prop_mon: paco.

  Definition thread_rel : itree lmodE Any.t -> (bool * itree lmodE Any.t) -> Prop :=
    fun itr_src '(b, itr_tgt) =>
      if b then
        (exists (fn : string) (arg : Any.t) (itr_cont : itree lmodE Any.t),
          (itr_tgt = trigger (@IO Any.t () fn arg);;; tau;; tau;; itr_cont)
          /\ itr_src = tau;; tau;; itr_cont)
        \/
        exists (fn : string) (arg : Any.t),
          (itr_tgt = trigger (@IO Any.t () fn arg);;; tau;; Ret tt↑)
          /\ itr_src = tau;; Ret tt↑
      else itr_src = itr_tgt.

  Lemma thread_rel_load
      thl_src thl_tgt
      (WF : Forall2 thread_rel thl_src thl_tgt) :
    forall n itr_src, thl_src !! n = Some itr_src -> exists bitr_tgt, <<TGTITR : thl_tgt !! n = Some bitr_tgt>> /\ <<WFITR : thread_rel itr_src bitr_tgt>>.
  Proof using Type.
    induction WF; i; ss. destruct n; ss; clarify; et.
  Qed.

  Lemma take_is_prop_load
      thl
      (WF : Forall take_is_prop thl) :
    forall n itr, thl !! n = Some itr -> <<WFITR : take_is_prop itr>>.
  Proof using Type.
    induction WF; i; ss. destruct n; ss; clarify; et.
  Qed.

  Lemma take_is_prop_bind itr ktr
      (F : take_is_prop itr)
      (S : forall x, take_is_prop (ktr x)) :
    take_is_prop (itr >>= ktr).
  Proof using Type.
    revert itr F. pcofix CIH. i. ides itr; grind.
    - eapply paco1_mon; try apply S. i. ss.
    - pfold. econs. right. apply CIH. punfold F. inv F; try itree_clarify H0.
      pclearbot. et.
    - destruct e; try destruct s.
      + rewrite vis_trigger bind_bind. pfold. econs. i. right.
        apply CIH. rewrite vis_trigger in F. punfold F. inv F; try itree_clarify H0.
        pclearbot. et.
      + rewrite vis_trigger bind_bind. pfold. econs. i. right.
        apply CIH. rewrite vis_trigger in F. punfold F. inv F; try itree_clarify H0.
        pclearbot. et.
      + destruct c.
        * rewrite vis_trigger bind_bind. pfold. econs. i. right.
          apply CIH. rewrite vis_trigger in F. punfold F. inv F; try itree_clarify H0.
          pclearbot. et.
        * rewrite vis_trigger bind_bind. pfold.
          rewrite vis_trigger in F. punfold F. inv F; try itree_clarify H0.
          econs; et. i. right. apply CIH. pclearbot. et.
        * rewrite vis_trigger bind_bind. pfold. econs. i. right.
          apply CIH. rewrite vis_trigger in F. punfold F. inv F; try itree_clarify H0.
          pclearbot. et.
  Qed.

  Lemma mod_take_is_prop i ofn r arg
    (PROG: alist_find ofn (Mod.to_lmod (md ★ ProphecyI.t) r).(LMod.fnsems) = Some i)
  :
    take_is_prop (i arg).
  Proof using PHYS.
    unfold md in PROG. induction smds; ss.
    { revert PROG. unfold ProphecyI.t, LMod.prog. unseal CRIS. ss. i.
      unfold ProphecyI.new, ProphecyI.resolve, ProphecyI.close in PROG.
      des_ifs; unfold ModTr.trans_ktree, SB.sandbox_body; ss;
        unfold SModTr.trans, SB.sandbox, ModTr.trans;
        rewrite !interpV_tau !interpV_ret; pfold; econs; left; pfold; econs. }
    unfold LMod.prog in *. ss. rewrite !map_app -app_assoc alist_find_app_o in PROG.
    inv PHYS.
    des_ifs; cycle 1. { apply IHl; et. rewrite !map_app. et. }
    clear IHl H2. clear smds md l. red in H1.
    induction a.(SMod.fnsems); ss. inv H1. des_ifs; et. clear IHf H3 f Heq1.
    destruct a0; ss; clarify. destruct f. ss. destruct p0. ss. destruct p. ss.
    destruct p. ss. des; clarify. clear.
    unfold ModTr.trans_ktree, SB.sandbox_body. hss.
    unfold ModTr.trans, SB.sandbox, SModTr.trans. rewrite !interpV_tau. pfold. econs. left.
    set (f _). generalize i. clear i. clear. pcofix CIH. i. ides i.
    - rewrite ! interpV_ret. pfold. econs.
    - rewrite ! interpV_tau. pfold. econs. right. et.
    - rewrite ! interpV_vis. rewrite !interpV_bind. destruct e; simpl.
      + destruct a; des_ifs; ss.
        * rewrite interpV_bind interpV_trigger. grind.
          rewrite interpV_bind interpV_trigger. grind.
          pfold. econs; et. i. clarify.
        * rewrite interpV_bind interpV_trigger. grind.
          rewrite interpV_bind interpV_trigger. grind.
          pfold. econs. i. left. grind. destruct (Any.split x); ss; cycle 1.
          { unfold triggerUB. grind. pfold. econs; et. i. clarify. }
          grind. unfold unwrapU. des_ifs; ss; cycle 1.
          { unfold triggerUB. grind. pfold. econs; et. i. clarify. }
          grind. unfold guarantee, assume.
          pfold. grind. econs.
          { esplits; eauto. }
          i. left. unfold ModTr.put_res. grind.
          pfold. econs. i. left. grind.
          unfold unwrapU. des_ifs; ss; cycle 1.
          { unfold triggerUB. grind. pfold. econs; et. i. clarify. }
          grind. pfold. econs. i. right. grind.
          rewrite !interpV_ret. grind.
        * rewrite interpV_bind interpV_trigger. grind.
          rewrite interpV_bind interpV_trigger. grind.
          pfold. econs. i. left. grind. unfold unwrapU. des_ifs; cycle 1.
          { unfold triggerUB. grind. pfold. econs; et. i. clarify. }
          grind. des_ifs; cycle 1.
          { unfold triggerUB. grind. pfold. econs; et. i. clarify. }
          grind. pfold. econs. i. left.
          unfold guarantee, ModTr.put_res. grind. pfold. econs. i. left.
          grind. pfold. econs. i. left. grind. unfold unwrapU. des_ifs; cycle 1.
          { unfold triggerUB. grind. pfold. econs; et. i. clarify. }
          grind. pfold. econs. i. grind. rewrite !interpV_ret. grind.
          right. et.
      + destruct s; des_ifs; try destruct p; try destruct c; ss.
        * grind. rewrite !interpV_tau bind_tau. pfold. econs. left.
          rewrite interpV_trigger. ss. des_ifs.
          all : eapply inj_pair2 in H1; eapply inj_pair2 in H0; clarify; grind; try rewrite interpV_trigger; grind.
          { pfold. econs. i. grind. right. et. }
          { rewrite interpV_bind interpV_trigger. grind. pfold. econs; et. i. clarify. }
        * rewrite !interpV_tau bind_tau. pfold. econs. left.
          rewrite interpV_trigger. ss. des_ifs.
          { eapply inj_pair2 in H0. eapply inj_pair2 in H1. clarify.
            grind. rewrite interpV_trigger. grind. pfold. econs. i. grind. right. et. }
          { eapply inj_pair2 in H0. eapply inj_pair2 in H1. clarify.
            grind. rewrite interpV_bind interpV_trigger. grind. pfold. econs; et. i. clarify. }
        * rewrite !interpV_tau bind_tau. pfold. econs. left.
          rewrite interpV_trigger. ss. des_ifs.
          grind. rewrite interpV_trigger. ss. grind. pfold. econs. i. grind. right. et.
        * grind. rewrite interpV_trigger. ss. des_ifs.
          { eapply inj_pair2 in H0. eapply inj_pair2 in H1. clarify.
            grind. rewrite interpV_trigger. grind. pfold. econs. i.
            uo. unfold or_else. des_ifs.
            - left. pfold. econs. i. right. et.
            - grind. right. et. }
          { eapply inj_pair2 in H0. eapply inj_pair2 in H1. clarify.
            rewrite interpV_bind interpV_trigger. grind. pfold. econs; et. i. clarify. }
        * grind. rewrite interpV_trigger. ss. des_ifs.
          { eapply inj_pair2 in H0. eapply inj_pair2 in H1. clarify.
            grind. rewrite interpV_trigger. grind. pfold. econs. i.
            uo. unfold or_else. des_ifs.
            - grind. right. et.
            - grind. right. et.
            - grind. right. et. }
          { eapply inj_pair2 in H0. eapply inj_pair2 in H1. clarify.
            rewrite interpV_bind interpV_trigger. grind. pfold. econs; et. i. clarify. }
        * grind. rewrite interpV_trigger. ss.
          grind. rewrite interpV_trigger. ss. grind.
          pfold. econs; et. i. right. grind.
        * rewrite interpV_bind interpV_trigger. grind.
          destruct excluded_middle_informative; ss.
          { clarify. eapply inj_pair2 in H0. clarify. eapply inj_pair2 in H0. clarify.
            rewrite interpV_bind interpV_trigger. grind. pfold. econs; et. i. grind.
            rewrite !interpV_ret. grind. right. et. }
          { clarify. apply inj_pair2 in H0.
            clarify. apply inj_pair2 in H0. clarify.
            rewrite interpV_bind interpV_trigger. grind. pfold. econs; et. i. clarify. }
        * grind. rewrite interpV_trigger. ss.
          grind. rewrite interpV_trigger. ss. grind.
          pfold. econs; et. i. right. grind.
  Qed.

  Lemma map_fst_snd {A B C: Type} (l : list (A * B)) (f: B -> C):
    List.map fst (List.map (map_snd f) l)
     = List.map fst l.
  Proof using Type. induction l. hss. hss. destruct a. hss. rewrite IHl. ss. Qed.

  Lemma mod_proph_comp_sim
      (WF : Mod.wf (md ★ ProphecyI.t)) :
    forall arg r,
      comp_sim
        (LMod.compile (Mod.to_lmod (md ★ ProphecyI.t) r) arg)
        (proph_compile (Mod.to_lmod (md ★ ProphecyI.t) r) arg).
  Proof using PHYS.
    ii.
    unfold LMod.compile, proph_compile. ss.
    unfold ITree.map.
    unfold LModTr.trans, proph_trans.
    unfold unwrapU. des_ifs; cycle 1.
    { unfold triggerUB. grind. pfold. econs. clarify. }
    ired. unfold LModTr.interp_stateE, LModTr.interp_callE, proph_interp_callE.
    assert (Forall2 thread_rel [i arg] [(false, i arg)]).
    { econs; last econs. ss. }
    assert (Forall take_is_prop [i arg]).
    { econs; last econs. eapply mod_take_is_prop; et. }
    assert (Forall take_is_prop (snd <$> [(false, i arg)])%stdpp).
    { econs; last econs. ss. eapply mod_take_is_prop; et. }
    clear Heq.
    set (Any.pair (ModTr.alist_encode (Mod.initial_st md ++ Mod.initial_st ProphecyI.t)) r↑). clearbody t. revert H H0 H1.
    generalize [i arg]. generalize [(false, i arg)].
    generalize 0. revert t. clear -WF PHYS.
    pcofix CIH. i. do 2 rewrite unfold_iterV. ss.
    destruct (l0 !! n) eqn:E; cycle 1.
    { ired. apply List.Forall2_length in H0.
      assert (l !! n = None).
      { apply lookup_ge_None_1 in E. rewrite H0 in E. apply lookup_ge_None_2 in E. ss. }
      rewrite H. unfold itreeV_itree. rewrite interp_state_tau. grind. pfold. econs.
      econs. pfold. unfold LModTr.pure_state. grind. econs. i; ss. }
    dup H0.
    eapply thread_rel_load in H0; et. des. rewrite TGTITR. destruct bitr_tgt.
    red in WFITR. destruct b. des.
    - clarify. ss. grind. pfold.
      rewrite /LModTr.pure_state. ired.
      under ( bind_extk (λ (_: unit), ITree.bind _ _) ) => m.
      { rewrite bind_ret_l. rewrite bind_tau. rewrite bind_ret_l.
        rewrite ! bind_ret_l. ss. rewrite unfold_iterV.
        ss. rewrite list_lookup_insert.
        2:{ apply lookup_lt_is_Some. et. }
        ss. rewrite bind_tau.
        rewrite interp_state_tau. rewrite bind_tau.
        over. }
      econs. ss. grind.
      rewrite list_insert_insert. right. eapply CIH.
      apply Forall2_insert. ss.
      ss.
      apply Forall_insert; ss.
      rewrite Forall_lookup in H2.
      specialize (H2 n).
      hexploit H2. { rewrite list_lookup_fmap_Some. et. } ss. i.
      punfold H. inv H; itree_clarify H4. specialize (NEXT tt).
      pclearbot. punfold NEXT. inv NEXT; try itree_clarify H0. pclearbot.
      apply NEXT0. rewrite list_fmap_insert. ss.
      apply Forall_insert; ss. rewrite Forall_lookup in H2.
      specialize (H2 n).
      hexploit H2. { rewrite list_lookup_fmap_Some. et. } ss. i.
      punfold H. inv H; itree_clarify H4. specialize (NEXT tt).
      pclearbot. punfold NEXT. inv NEXT; try itree_clarify H0. pclearbot.
      apply NEXT0.
    - clarify. ss. grind. pfold.
      rewrite /LModTr.pure_state. ired.
      under ( bind_extk (λ (_: unit), ITree.bind _ _) ) => m.
      { rewrite bind_ret_l. rewrite bind_tau. rewrite bind_ret_l.
        rewrite ! bind_ret_l. ss. rewrite unfold_iterV.
        ss. rewrite list_lookup_insert.
        2:{ apply lookup_lt_is_Some. et. }
        ss. rewrite bind_tau.
        rewrite interp_state_tau. rewrite bind_tau.
        over. }
      econs. grind. rewrite list_insert_insert. left. do 2 rewrite unfold_iterV.
      ss. rewrite -> list_lookup_insert by now apply lookup_lt_is_Some; et.
      rewrite -> list_lookup_insert by now apply lookup_lt_is_Some; et. ss. grind.
      pfold. econs. left.
      destruct (Nat.eq_dec n 0).
      + grind. pfold. econs.
      + grind. pfold. econs. i. clarify.
    - hss.
      ides (i0); hss; grind; pfold; try econs.
      + destruct (Nat.eq_dec). grind.
        (* Ret *) econs; pfold; econs.
        (* UB *) unfold triggerUB. rewrite interp_state_bind interp_state_trigger.
        grind. econs. rewrite /LModTr.pure_state.
        grind. pfold; econs. i; ss.
      + (* tau *)
        right. eapply CIH; et.
        apply Forall2_insert; et; ss.
        apply Forall_insert; et; ss.
        exploit Forall_lookup_1. apply H1. apply E.
        i. punfold x0. inv x0; et; hss; try itree_clarify H0.
        pclearbot. eapply NEXT.
        rewrite list_fmap_insert; ss.
        apply Forall_insert; et; ss.
        rewrite Forall_lookup in H2.
        exploit (H2). rewrite list_lookup_fmap_Some. et. hss.
        i. punfold x0. inv x0; et; hss; try itree_clarify H0.
        pclearbot. eapply NEXT.
      + (* Vis *) destruct e; try destruct c; try destruct s; hss; cycle 2; grind.
        3: destruct c.
        * (* Yield *)
          econs. right. eapply CIH; et.
          apply Forall2_insert; et; ss.
          apply Forall_insert; et; ss.
          exploit Forall_lookup_1. apply H1. apply E.
          i. punfold x0. inv x0; et; hss; try itree_clarify H0.
          pclearbot. ired.
          eapply NEXT.
          rewrite list_fmap_insert; ss.
          apply Forall_insert; et; ss.
          rewrite Forall_lookup in H2.
          exploit (H2). rewrite list_lookup_fmap_Some. et. hss.
          i. punfold x0. inv x0; et; hss; try itree_clarify H0.
          pclearbot. ired. eapply NEXT.
        *  (* StateE *)
          destruct s.
          ired. econs. right. eapply CIH; et.
          apply Forall2_insert; et; ss.
          apply Forall_insert; et; ss.
          exploit Forall_lookup_1. apply H1. apply E.
          i. punfold x0. inv x0; et; hss; try itree_clarify H0.
          pclearbot. ired.
          eapply NEXT.
          rewrite list_fmap_insert; ss.
          apply Forall_insert; et; ss.
          rewrite Forall_lookup in H2.
          exploit (H2). rewrite list_lookup_fmap_Some. et. hss.
          i. punfold x0. inv x0; et; hss; try itree_clarify H0.
          pclearbot. ired. eapply NEXT.
        * (* Choose *)
          ired. unfold LModTr.pure_state at 1 4.
          grind. econs. i. ired. econs. pfold; econs.
          right. eapply CIH.
          apply Forall2_insert; et; ss.
          apply Forall_insert; et; ss.
          exploit Forall_lookup_1. apply H1. apply E.
          i. punfold x1. inv x1; et; hss; try itree_clarify H0.
          pclearbot. ired.
          eapply NEXT.
          rewrite list_fmap_insert; ss.
          apply Forall_insert; et; ss.
          rewrite Forall_lookup in H2.
          exploit (H2). rewrite list_lookup_fmap_Some. et. hss.
          i. punfold x1. inv x1; et; hss; try itree_clarify H0.
          pclearbot. ired. eapply NEXT.
        * (* Take *)
          unfold LModTr.pure_state at 1 4.
          grind. exploit Forall_lookup_1. apply H1. apply E. i.
          punfold x0. rewrite <- bind_trigger in x0.
          assert (∃ (P : Prop), X = P).
          { inv x0; try itree_clarify H0. et. }
          des. hss. econs. i.
          ired. econs; pfold; econs.
          right. eapply CIH.
          apply Forall2_insert; et; ss.
          apply Forall_insert; et; ss.
          exploit Forall_lookup_1. apply H1. apply E.
          i. punfold x2. inv x2; et; hss; try itree_clarify H0.
          pclearbot. ired.
          eapply inj_pair2 in H. hss.
          rewrite list_fmap_insert; ss.
          apply Forall_insert; et; ss.
          rewrite Forall_lookup in H2.
          exploit (H2). rewrite list_lookup_fmap_Some. et. hss.
          i. punfold x2. inv x2; et; hss; try itree_clarify H0.
          pclearbot. ired.
          eapply inj_pair2 in H. hss.
        * (* IO *)
          unfold LModTr.pure_state at 1 4.
          grind. econs. i. ired.
          econs. pfold; econs; ss.
          right. eapply CIH.
          apply Forall2_insert; et; ss.
          apply Forall_insert; et; ss.
          exploit Forall_lookup_1. apply H1. apply E.
          i. punfold x1. inv x1; et; hss; try itree_clarify H0.
          pclearbot. ired. eapply NEXT.
          rewrite list_fmap_insert; ss.
          apply Forall_insert; et; ss.
          rewrite Forall_lookup in H2.
          exploit (H2). rewrite list_lookup_fmap_Some. et. hss.
          i. punfold x1. inv x1; et; hss; try itree_clarify H0.
          pclearbot. ired. eapply NEXT.
        * (* Call *)
          econs.
          destruct (alist_find _ _) eqn:EE; cycle 1.
          { hss. unfold triggerUB.
            rewrite interp_state_bind.
            grind. unfold LModTr.pure_state. grind.
            econs. pfold. econs. i. ss. }
          grind. right. eapply CIH.
          { apply Forall2_insert; et; ss.
            unfold thread_rel. destruct decide; et.
            left. rewrite map_app in EE. apply alist_find_comm in EE; cycle 1.
            { rewrite -map_app List.map_map.
              inv WF. ss. set fst in wf_fns.
              replace (fst ∘ _) with y; et.
              extensionalities; destruct H; et. }
            revert EE. unfold ProphecyI.t. unseal CRIS. ss.
            unfold ProphecyI.new, ProphecyI.resolve, ProphecyI.close.
            unfold ModTr.trans_ktree, SB.sandbox_body.
            unfold ModTr.trans, SB.sandbox, SModTr.trans, SModTr.trans_ktree.
            i. des; clarify; ss; clarify; rewrite !interpV_tau !SRed.ret !interpV_ret; grind; et. }
          { apply Forall_insert; et. apply take_is_prop_bind.
            eapply mod_take_is_prop; et. i. pfold. econs. left.
            eapply Forall_lookup_1 in H2; cycle 1.
            { rewrite list_lookup_fmap. rewrite -> TGTITR. ss. }
            punfold H2. inv H2; try itree_clarify H0. grind.
            pclearbot. et. }
          { rewrite list_fmap_insert. apply Forall_insert; et.
            eapply Forall_lookup_1 in H1; [|et].
            punfold H1. inv H1; try itree_clarify H0. pclearbot.
            destruct decide; ss.
            - pfold. econs. i. left. apply take_is_prop_bind.
              eapply mod_take_is_prop; et. i. pfold. econs. left. grind.
            - apply take_is_prop_bind. eapply mod_take_is_prop; et.
              i. pfold. econs. left. grind. }
        * (* Spawn *)
          econs.
          destruct (alist_find _ _) eqn:EE; cycle 1.
          { hss. unfold triggerUB.
            rewrite interp_state_bind.
            grind. unfold LModTr.pure_state. grind.
            econs. pfold. econs. i. ss. }
          grind. right. eapply CIH.
          { apply Forall2_app.
            { apply Forall2_insert; et; ss. apply Forall2_length in H3. rewrite H3; ss. }
            econs; last econs. destruct decide; ss.
            right. rewrite map_app in EE. apply alist_find_comm in EE; cycle 1.
            { rewrite -map_app List.map_map.
              inv WF. ss. set fst in wf_fns.
              replace (fst ∘ _) with y; et.
              extensionalities; destruct H; et. }
            revert EE. unfold ProphecyI.t. unseal CRIS. ss.
            unfold ProphecyI.new, ProphecyI.resolve, ProphecyI.close.
            unfold ModTr.trans_ktree, SB.sandbox_body.
            unfold ModTr.trans, SB.sandbox, SModTr.trans, SModTr.trans_ktree.
            i. des; clarify; ss; clarify; rewrite !interpV_tau !SRed.ret !interpV_ret; grind; et. }
          { eapply Forall_lookup_1 in E; et. punfold E.
            inv E; try itree_clarify H0. pclearbot. grind.
            apply Forall_app. split. apply Forall_insert; et.
            econs; last econs. eapply mod_take_is_prop; et. }
          { eapply Forall_lookup_1 in E; et. punfold E.
            inv E; try itree_clarify H0. pclearbot. grind.
            rewrite fmap_app. ss. apply Forall_app.
            rewrite list_fmap_insert. ss. split.
            apply Forall_insert; et. econs; last econs.
            destruct decide; ss.
            - pfold. econs. i. left. eapply mod_take_is_prop; et.
            - eapply mod_take_is_prop; et. }
          Unshelve. all : et.
  Qed.

  Lemma prophecy_tgt_exbeh_exists
      (WF : Mod.wf (md ★ ProphecyI.t)) :
    forall arg r tr
      (BEH: Beh.of_itree (LMod.compile (Mod.to_lmod (md ★ ProphecyI.t) r) arg) tr),
      exists extr, tr_extr_relation tr extr /\ ExBeh.of_itree (proph_compile (Mod.to_lmod (md ★ ProphecyI.t) r) arg) extr.
  Proof using PHYS.
    i. eapply comp_sim_tgt_extr_exists; et. apply mod_proph_comp_sim. et.
  Qed.

  Let proph_newI := (ModTr.trans_ktree ∘ SB.sandbox_body ∘ (SModTr.trans_ktree sp_none)) (false, wmask_all, ["Prophecy"], (None, ProphecyI.new)).
  Let proph_resolveI := (ModTr.trans_ktree ∘ SB.sandbox_body ∘ (SModTr.trans_ktree sp_none)) (false, wmask_all, ["Prophecy"], (None, ProphecyI.resolve)).
  Let proph_closeI := (ModTr.trans_ktree ∘ SB.sandbox_body ∘ (SModTr.trans_ktree sp_none)) (false, wmask_all, ["Prophecy"], (None, ProphecyI.close)).

  Let proph_newA sp := (ModTr.trans_ktree ∘ SB.sandbox_body ∘ (SModTr.trans_ktree sp)) (true, wmask_all, ["Prophecy"], (Some ProphecyA.new_spec, fbody_trivial)).
  Let proph_resolveA sp := (ModTr.trans_ktree ∘ SB.sandbox_body ∘ (SModTr.trans_ktree sp)) (true, wmask_all, ["Prophecy"], (Some ProphecyA.resolve_spec, fbody_trivial)).
  Let proph_closeA sp := (ModTr.trans_ktree ∘ SB.sandbox_body ∘ (SModTr.trans_ktree sp)) (true, wmask_all, ["Prophecy"], (Some ProphecyA.close_spec, fbody_trivial)).

  Variant _wf_sim (coself : itree lmodE Any.t -> (bool * itree lmodE Any.t) -> Prop) : itree lmodE Any.t -> (bool * itree lmodE Any.t) -> Prop :=
  | wf_ret retv
  : _wf_sim coself (Ret retv) (false, Ret retv)

  | wf_tau itr_src itr_tgt
    (NEXT: coself itr_src (false, itr_tgt))
  : _wf_sim coself (tau;; itr_src) (false, tau;; itr_tgt)

  | wf_coreE X (e : coreE X) ktr_src ktr_tgt
    (NEXT: forall x, coself (ktr_src x) (false, ktr_tgt x))
  : _wf_sim coself (x <- trigger e;; ktr_src x) (false, x <- trigger e;; ktr_tgt x)

  | wf_callE X (e : callE X) ktr_src ktr_tgt
    (NEXT: forall x, coself (ktr_src x) (false, ktr_tgt x))
  : _wf_sim coself (x <- trigger e;; ktr_src x) (false, x <- trigger e;; ktr_tgt x)

  | wf_prophecy_new sp arg ktr_src ktr_tgt
    (NEXT: coself (ktr_src tt↑) (false, ktr_tgt tt↑))
    : _wf_sim coself (x <- proph_newA sp arg;; ktr_src x)
        (true, trigger (IO (O:=()) (ProphecyName.new) arg);;;
         x <- proph_newI arg;; ktr_tgt x)

  | wf_prophecy_resolve sp arg ktr_src ktr_tgt
    (NEXT: coself (ktr_src tt↑) (false, ktr_tgt tt↑))
    : _wf_sim coself (x <- proph_resolveA sp arg;; ktr_src x)
        (true, trigger (IO (O:=()) (ProphecyName.resolve) arg);;;
         x <- proph_resolveI arg;; ktr_tgt x)

  | wf_prophecy_close sp arg ktr_src ktr_tgt
    (NEXT: coself (ktr_src tt↑) (false, ktr_tgt tt↑))
    : _wf_sim coself (x <- proph_closeA sp arg;; ktr_src x)
        (true, trigger (IO (O:=()) (ProphecyName.close) arg);;;
         x <- proph_closeI arg;; ktr_tgt x)

  | wf_sget key ktr_src ktr_tgt
    (NEXT: forall x, coself (ktr_src x) (false, ktr_tgt x))
  : _wf_sim coself (x <- (itreeV_itree (ModTr.handle_crisE (||SGet key|)%sum));; ktr_src x) (false, x <- (itreeV_itree (ModTr.handle_crisE (||SGet key|)%sum));; ktr_tgt x)

  | wf_sput key a ktr_src ktr_tgt
    (NEXT: coself (ktr_src tt) (false, ktr_tgt tt))
  : _wf_sim coself (x <- (itreeV_itree (ModTr.handle_crisE (||SPut key a|)%sum));; ktr_src x) (false, x <- (itreeV_itree (ModTr.handle_crisE (||SPut key a|)%sum));; ktr_tgt x)

  | wf_Guarantee iP ktr_src ktr_tgt
    (NEXT: coself (ktr_src tt) (false, ktr_tgt tt))
  : _wf_sim coself (x <- (itreeV_itree (ModTr.handle_crisE (Guarantee iP|)%sum));; ktr_src x) (false, x <- (itreeV_itree (ModTr.handle_crisE (Guarantee iP|)%sum));; ktr_tgt x)

  | wf_AssumePrecise r ktr_src ktr_tgt
    (NEXT: coself (ktr_src tt) (false, ktr_tgt tt))
  : _wf_sim coself (x <- (itreeV_itree (ModTr.handle_crisE (AssumeRes r|)%sum));; ktr_src x) (false, x <- (itreeV_itree (ModTr.handle_crisE (AssumeRes r|)%sum));; ktr_tgt x).

  Definition wf_sim := paco2 _wf_sim bot2.


  Lemma wf_sim_mon : monotone2 _wf_sim.
  Proof using.
    ii. destruct IN; des; eauto using _wf_sim.
  Qed.

  Hint Constructors _wf_sim : core.
  Hint Resolve wf_sim_mon: paco.

  Lemma thread_list_load_relation
      thl_src thl_tgt
      (WF : Forall2 wf_sim thl_src thl_tgt) :
    forall n itr_src, thl_src !! n = Some itr_src -> exists itr_tgt, <<TGTITR : thl_tgt !! n = Some itr_tgt>> /\ <<WFITR : wf_sim itr_src itr_tgt>>.
  Proof using Type.
    induction WF; i; ss. destruct n; ss; clarify; et.
  Qed.

  Lemma wf_sim_bind itrs itrt ktrs ktrt
      (L1 : wf_sim itrs (false, itrt))
      (L2 : forall x, wf_sim (ktrs x) (false, ktrt x)) :
    wf_sim (itrs >>= ktrs) (false, itrt >>= ktrt).
  Proof using Type.
    Local Opaque itreeV_itree.
    depgen itrs. depgen itrt. pcofix CIH. i. punfold L1. inv L1.
    - ired. apply pacobot2. apply L2.
    - ired. pfold. econs. right. apply CIH. pclearbot. et.
    - ired. pfold. econs. right. apply CIH. pclearbot. apply NEXT.
    - ired. pfold. econs. right. apply CIH. pclearbot. apply NEXT.
    - ired. pfold. econs. right. apply CIH. pclearbot. apply NEXT.
    - ired. pfold. econs. right. apply CIH. pclearbot. apply NEXT.
    - ired. pfold. econs. right. apply CIH. pclearbot. apply NEXT.
    - rewrite 2! bind_bind. pfold. econs. i.
      right. apply CIH. pclearbot. apply NEXT.
    Local Transparent itreeV_itree.
  Qed.

  Lemma pmod_fun_wf_sim fn i args
    (FIND: alist_find fn
             (List.map (map_snd (ModTr.trans_ktree ∘ SB.sandbox_body)%stdpp)
                (Mod.fnsems md)) = Some i) :
      wf_sim (i args) (false, i args).
  Proof using PHYS.
    revert i FIND. unfold md. induction smds; ss.
    rewrite !map_app alist_find_app_o. i. inv PHYS. des_ifs; et. clear IHl H2 l md smds.
    red in H1. revert i H1 Heq. induction a.(SMod.fnsems); ss. i. inv H1.
    des_ifs; et. destruct a0; ss; clarify. destruct f0; ss. destruct p0; ss.
    destruct p; ss. destruct p; ss. des; clarify.
    clear. unfold SB.sandbox_body. ss.
    unfold ModTr.trans_ktree. unfold ModTr.trans, SB.sandbox, SModTr.trans.
    rewrite !interpV_tau. pfold. econs. left. generalize (f0 args). clear. pcofix CIH. i.
    ides i.
    { rewrite ! interpV_ret. pfold. econs. }
    { rewrite ! interpV_tau. pfold. econs. right. et. }
    rewrite interpV_vis. rewrite !interpV_bind.
    destruct e as [e|[e|[e|e]]]; simpl.
    - rewrite bind_ret_r interpV_trigger /=.
      des_ifs; clexteq;
        rewrite interpV_bind bind_bind interpV_trigger.
      + ss. rewrite bind_bind. pfold. econs. clarify.
      + pfold. apply wf_AssumePrecise. rewrite interpV_ret bind_ret_l. right. et.
      + pfold. apply wf_Guarantee. rewrite interpV_ret bind_ret_l. right. et.
    - des_ifs; ss;
        rewrite !interpV_tau bind_tau; pfold; econs; left;
        rewrite interpV_trigger; ss; des_ifs; clexteq;
        rewrite interpV_bind interpV_trigger; ss;
        grind; pfold; econs; clarify; right; grind;
        rewrite interpV_ret; grind.
    - rewrite bind_ret_r interpV_trigger; ss.
      des_ifs; clexteq;
        rewrite interpV_bind bind_bind interpV_trigger.
      + pfold. econs. rewrite interpV_ret bind_ret_l. right. et.
      + ss. rewrite bind_bind. pfold. econs. clarify.
      + pfold. econs. i. rewrite interpV_ret bind_ret_l. right. et.
      + ss. rewrite bind_bind. pfold. econs. clarify.
    - rewrite bind_ret_r interpV_trigger; ss.
      des_ifs; clexteq;
        rewrite interpV_bind bind_bind interpV_trigger /= bind_ret_r;
        pfold; econs; clarify; i;
        rewrite interpV_ret bind_ret_l; right; et.
  Qed.

  Fixpoint stream_app {A} (prefix : list A) (s : stream A) : stream A :=
    match prefix with
    | [] => s
    | h :: t => sfold (scons h (stream_app t s))
    end.

  Fixpoint stream_firstn {A} (i : nat) (s : stream A) : list A :=
    match i with
    | O => []
    | S i' =>
        let '(sfold (scons h t)) := s in
        h :: (stream_firstn i' t)
    end.

  Fixpoint nth {A} (x : stream A) (i : nat) : A :=
    match x with
    | sfold (scons h x') =>
        match i with
        | O => h
        | S n => nth x' n
        end
    end.

  Lemma firstn_reverse {A} n (l : list A) x (LE : n ≤ List.length l) :
    Prophecy.firstn (λ i, nth (stream_app l x) i) n = reverse (firstn n l).
  Proof using Type.
    revert l x LE. induction n; ss. i.
    assert (nth_error l n <> None).
    { rewrite nth_error_Some. nia. }
    destruct nth_error eqn:E; ss.
    replace (take (S n) l) with (take n l ++ [a]).
    2:{ clear - E. revert l a E. induction n; ss; i; des_ifs.
        ss. f_equal. rewrite IHn; et. }
    rewrite reverse_app. ss. rewrite IHn; try nia. f_equal.
    clear - E. revert l x a E. induction n; ss; i.
    { des_ifs. ss. inv Heq. et. }
    des_ifs. ss. inv Heq. apply IHn. et.
  Qed.

  Lemma firstn_length {A} (l : list A) x :
    Prophecy.firstn (λ i, nth (stream_app l x) i) (List.length l) = reverse l.
  Proof using Type. rewrite firstn_reverse; try nia. rewrite firstn_all //. Qed.

  Lemma stream_app_cons {A} (l : list A) a x :
    stream_app l (sfold (scons a x)) = stream_app (l ++ [a]) x.
  Proof using Type. revert a x. induction l; ss. i. do 2 f_equal. et. Qed.

  Definition consistent_sany (Pr : Prophecy.t) (sl: list SAny.t) (p : Prophecy.Pro Pr) :=
    exists l : list (Prophecy.Obs Pr),
      sl = List.map SAny.upcast l /\ Prophecy.consistent Pr l p.

  CoFixpoint stream_map {A B} (f : A -> B) (x : stream A) : stream B :=
    match x with
    | sfold (scons hd tl) => sfold (scons (f hd) (stream_map f tl))
    end.

  Lemma consistent_sany_equiv t obs_seq p
    (COV : forall i, Prophecy.consistent t (Prophecy.firstn obs_seq i) p) :
    forall i,
    exists l,
      List.map SAny.upcast l = Prophecy.firstn (λ n, (obs_seq n)↑↑) i
      /\ Prophecy.consistent t l p.
  Proof using Type.
    i. exists (Prophecy.firstn obs_seq i). split; et.
    induction i; ss. f_equal. et.
  Qed.

  Hint Constructors _extrace_obs_stream_relation : core.
  Hint Resolve extrace_obs_stream_relation_mon : paco.

  Lemma src_mod_wf sp (WF : Mod.wf (md ★ ProphecyI.t)) :
    Mod.wf (md ★ (ProphecyA.t sp)).
  Proof using smds.
    inv WF. ss. rewrite !map_app in wf_fns.
    replace (Mod.scopes ProphecyI.t) with (Mod.scopes (ProphecyA.t sp)) in wf_scopes by now do 2 (unfold_mod; ss); et.
    replace (List.map fst (Mod.fnsems ProphecyI.t)) with (List.map fst (Mod.fnsems (ProphecyA.t sp))) in wf_fns by now do 2 (unfold_mod; ss).
    econs; et. ss. rewrite !map_app //.
  Qed.

  Lemma adequacy_aux sp rs_src rs_tgt rs_proph rs_prog_tgt rs_prog_src proph_map free_ids extr thidx thl_src thl_tgt pstore
    (WFMODT : Mod.wf (md ★ ProphecyI.t))
    (VALID : ✓ rs_src)
    (REQ : rs_src ~~> rs_tgt ⋅ rs_proph)
    (RS : rs_proph ≡ (own.iRes_singleton base_γ (has_proph_auth_r free_ids proph_map) ⋅ own.iRes_singleton base_γ (free_id_auth_r free_ids)))
    (WF : Forall2 wf_sim thl_src thl_tgt)
    (INV :
      forall id (NOTFREE : ~(free_ids id)),
        exists obs_str,
        let p := proph_map id in
        extrace_obs_stream_relation id (projT1 p) extr obs_str
        /\ forall i', consistent_sany (projT1 p)
                       (Prophecy.firstn (λ i, nth (stream_app (reverse (List.map SAny.upcast (snd (projT2 p)))) (stream_map SAny.upcast obs_str)) i) i')
                       (fst (projT2 p)))
    (TBEH :
      paco2 ExBeh._of_itreeF bot2
        (x_ <-
           interp_state (case_ LModTr.handle_stateE LModTr.pure_state)
             (iterV
                (proph_handle_callE
                   (LMod.prog
                      (Mod.to_lmod (md ★ ProphecyI.t) rs_prog_tgt)))
                (thidx, thl_tgt)) (Any.pair pstore (rs_tgt : Σ) ↑);; Ret x_.2) extr) :

    simg_ex false false extr
      (x <-
         LModTr.interp_stateE Any.t
           (iterV
              (LModTr.handle_callE
                 (LMod.prog (Mod.to_lmod (md ★ (ProphecyA.t sp)) rs_prog_src)))
              (thidx, thl_src)) (Any.pair pstore rs_src ↑);; Ret x.2)
      (x <-
         LModTr.interp_stateE Any.t
           (iterV
              (proph_handle_callE
                 (LMod.prog (Mod.to_lmod (md ★ ProphecyI.t) rs_prog_tgt)))
              (thidx, thl_tgt)) (Any.pair pstore (rs_tgt : Σ) ↑);; Ret x.2).
  Proof using PHYS.
    Local Opaque wsimg.
    hexploit src_mod_wf; et. intro WFMODS.
    move WFMODS at top. move WFMODT at top.
    move rs_proph at bottom. move rs_tgt at bottom. revert_until proph_closeA. pcofix CIH. i.
    revert TBEH. set (ITree.bind _ _). set (ITree.bind _ _).
    assert (wsimg r false false extr i0 i); et. unfold i0, i. clearbody i i0.
    rewrite /LModTr.interp_stateE unfold_iterV /itreeV_itree {1}/LModTr.handle_callE.
    destruct (thl_src !! thidx) as [itr_src|] eqn: SRCITR; [|grind; steps_l; clearub].
    hexploit thread_list_load_relation; et; i; des.
    assert (LEN : thidx < base.length thl_src).
    { apply lookup_lt_is_Some. et. }
    rewrite /LModTr.interp_stateE unfold_iterV /itreeV_itree {1}/proph_handle_callE TGTITR .
    punfold WFITR. inv WFITR; ss; pclearbot.
    (* case : return *)
    - grind. steps_r. steps_l. des_ifs; grind. { apply wsimg_ret. }
      clearub.
    (* case : tau *)
    - grind. steps_r. steps_l. endsim; cycle 1.
      + i. hexploit INV; et. i. des. esplits; et. punfold H0.
        inv H0. fclarify. pclearbot. et.
      + apply Forall2_insert; et.
    (* case : coreE *)
    - grind. destruct e; ss; grind; unfold LModTr.pure_state at 1 3; grind.
      + steps_r. steps_l. exists x. grind. steps_r. steps_l. endsim.
        * apply Forall2_insert; et. apply NEXT.
        * i. hexploit INV; et. i. des. esplits; et.
          punfold H0. inversion H0. clexteq. pclearbot.
          apply (f_equal (fun y => y 0%fin)) in H5. clarify.
          punfold STEP. inversion STEP. fclarify. pclearbot. et.
      + steps_l. steps_r. exists p. grind. steps_l. steps_r. endsim.
        * apply Forall2_insert; et. apply NEXT.
        * i. hexploit INV; et. i. des. esplits; et.
          punfold H0. inversion H0. fclarify. pclearbot.
          punfold STEP. inversion STEP. fclarify. pclearbot. et.
      + apply wsimg_io_normal. i. clarify. rename extr' into extr.
        grind. steps_r. steps_l. endsim.
        * apply Forall2_insert; et. apply NEXT.
        * i. hexploit INV; et. i. des. esplits; et.
          punfold H0. inversion H0.
          apply inj_pair2 in H6. apply inj_pair2 in H7.
          clarify. fclarify. pclearbot.
          punfold STEP. inversion STEP. fclarify. pclearbot. et.
    (* case : callE *)
    - grind. destruct e; ss; grind.
      + steps_l. steps_r. unfold unwrapU. destruct alist_find eqn:E; [|clearub].
        grind. destruct decide.
        (* case : proph call *)
        * des_ifs; cycle 1.
          { rewrite !map_app in Heq. rewrite alist_find_app_o in Heq.
            des_ifs. exfalso. revert Heq. unfold_mod. ss.
            unfold rel_dec. ss. do 3 (destruct dec; ss). i. des; clarify. }
          grind. endsim; cycle 1.
          { i. hexploit INV; et. i. clear o. des. esplits; et.
            punfold H0. inversion H0. fclarify. pclearbot. et. }
          apply Forall2_insert; et. clear -Heq E o NEXT WFMODS WFMODT.
          inv WFMODS. inv WFMODT. ss.
          set (Mod.fnsems md) as fns in *.
          revert E. unfold_mod. ss. rewrite !map_app. ss. i.
          revert Heq. unfold_mod. ss. rewrite !map_app. ss. i.
          revert wf_fns. unfold_mod; ss. rewrite !map_app. ss. i.
          apply alist_find_comm in E; cycle 1.
          { rewrite map_app !List.map_map //=. erewrite map_ext; et. i.
            destruct a; ss. }
          apply alist_find_comm in Heq; cycle 1.
          { rewrite map_app !List.map_map //=. erewrite map_ext; et. i.
            destruct a; ss. }
          des; clarify; ss; clarify.
          { pfold. econs. left. pfold. econs. left. grind. }
          { pfold. econs. left. pfold. econs. left. grind. }
          { pfold. econs. left. pfold. econs. left. grind. }
        (* case : normal call *)
        * rewrite !map_app in E. rewrite alist_find_app_o in E.
          destruct alist_find eqn:E0 in E; clarify; cycle 1.
          { exfalso. revert E. unfold_mod. ss. unfold rel_dec. ss. i.
            do 3 (try destruct dec; ss); clarify; apply n; et. }
          rewrite !map_app alist_find_app_o E0. grind. endsim.
          { apply Forall2_insert; et. apply wf_sim_bind.
            { eapply pmod_fun_wf_sim; et. }
            i. pfold. econs. left. grind. }
          i. hexploit INV; et. i. des. esplits; et.
          punfold H0. inversion H0. fclarify. pclearbot. et.
      + steps_l. steps_r. unfold unwrapU. destruct alist_find eqn:E; [|clearub].
        grind. destruct decide.
        (* case : proph spawn *)
        * des_ifs; cycle 1.
          { rewrite !map_app in Heq. rewrite alist_find_app_o in Heq.
            des_ifs. exfalso. revert Heq. unfold_mod. ss.
            unfold rel_dec. ss. do 3 (destruct dec; ss). i. des; clarify. }
          grind. endsim; cycle 1.
          { i. hexploit INV; et. i. clear o. des. esplits; et.
            punfold H0. inversion H0. fclarify. pclearbot. et. }
          apply Forall2_app.
          { apply Forall2_insert; et.
            erewrite Forall2_length; et. apply NEXT. }
          econs; last econs.
          rewrite -(bind_ret_r (i1 args)) -(bind_ret_r (trigger _;;;_)) bind_bind.
          clear -Heq E o NEXT WFMODS WFMODT.
          inv WFMODS. inv WFMODT. ss.
          set (Mod.fnsems md) as fns in *.
          revert E. unfold_mod. ss. rewrite !map_app. ss. i.
          revert Heq. unfold_mod. ss. rewrite !map_app. ss. i.
          revert wf_fns. unfold_mod; ss. rewrite !map_app. ss. i.
          apply alist_find_comm in E; cycle 1.
          { rewrite map_app !List.map_map //=. erewrite map_ext; et. i.
            destruct a; ss. }
          apply alist_find_comm in Heq; cycle 1.
          { rewrite map_app !List.map_map //=. erewrite map_ext; et. i.
            destruct a; ss. }
          des; clarify; ss; clarify.
          { pfold. econs. left. pfold. econs. }
          { pfold. econs. left. pfold. econs. }
          { pfold. econs. left. pfold. econs. }
        (* case : normal spawn *)
        * rewrite !map_app in E. rewrite alist_find_app_o in E.
          destruct alist_find eqn:E0 in E; clarify; cycle 1.
          { exfalso. revert E. unfold_mod. ss. unfold rel_dec. ss. i.
            do 3 (try destruct dec; ss); clarify; apply n; et. }
          rewrite !map_app alist_find_app_o E0. grind. endsim.
          { apply Forall2_app; cycle 1.
            { econs; last econs. eapply pmod_fun_wf_sim; et. }
            apply Forall2_insert; et. erewrite Forall2_length; et.
            apply NEXT. }
          i. hexploit INV; et. i. des. esplits; et.
          punfold H0. inversion H0. fclarify. pclearbot. et.
      + steps_l. steps_r. endsim.
        * apply Forall2_insert; et. apply NEXT.
        * i. hexploit INV; et. i. des. esplits; et.
          punfold H0. inv H0. fclarify. pclearbot. et.
    - grind. unfold LModTr.pure_state at 1 3. grind.
      apply wsimg_io_proph. i. clarify. rename extr' into extr.
      steps_l. grind. steps_l. steps_r.
      unfold proph_newI, ProphecyI.new, ProphecyA.new_spec, fspec_simple.
      unfold precond, postcond. destruct p. ss.
      unfold cfunU, SB.sandbox_body, SB.sandbox, ModTr.trans_ktree, ModTr.trans, SModTr.trans.
      simpl. rewrite !interpV_bind !interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl.
      rewrite bind_ret_r. grind. rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et.
      grind. unfold LModTr.pure_state at 1. grind. steps_l. grind.
      steps_l. rewrite !list_insert_insert.
      simpl. rewrite !interpV_bind !interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl. grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_l. grind.
      rewrite !list_insert_insert. rewrite Any.pair_split. grind.
      rewrite Any.upcast_downcast. grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_l. grind. steps_l.
      rewrite !list_insert_insert.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_l. grind. steps_l.
      rewrite !list_insert_insert.
      des.
      assert (Own p0 ⊢ ⌜arg = i1↑⌝).
      { iIntros "A". iPoseProof (p2 with "A") as ">[[[A B] C] D]". iFrame. }
      apply Own_pure_soundness in H; et. clarify.
      rewrite !SRed.ret.
      assert (Own p0 ⊢ |==> ((⌜i1 ↑ = i1 ↑⌝ ∗ free_id (λ y : Prophecy.ID, y = i1)) ∗ ⌜p = i1 ↑⌝) ∗ Own (rs_tgt ⋅ rs_proph)).
      { iIntros "A". iPoseProof (p2 with "A") as ">[A B]". iFrame.
        iStopProof. apply Own_Upd. et. }
      clear p2. rename H into p2. rewrite /free_id in p2.
      assert (✓ (free_id_r (λ y : Prophecy.ID, y = i1) ⋅ free_id_auth_r free_ids)).
      { eapply Own_pure_soundness; et.
        iIntros "A". iPoseProof (p2 with "A") as ">[[[A B] C] [D E]]".
        rewrite RS. iDestruct "E" as "[E F]".
        rewrite own.own_eq /own.own_def own.Own_eq /own.Own_def.
        iCombine "B F" as "B". rewrite -own.iRes_singleton_op.
        replace uPred_ownM with own.Own_def by et.
        rewrite -own.Own_eq.
        iPoseProof (Own_valid with "B") as "%".
        rewrite -uPred.discrete_valid.
        iApply own.iRes_singleton_validI.
        rewrite uPred.discrete_valid. et. }
      assert (free_ids i1).
      { unfold free_id_auth_r, free_id_r in H.
        specialize (H i1). discrete_fun_tac.
        destruct excluded_middle_informative; clarify.
        destruct excluded_middle_informative; clarify.
        rewrite comm auth_both_valid_discrete in H. des.
        red in H. des. destruct z. { rewrite -Some_op in H. inv H. }
        inv H. }
      clear H. rename H0 into FREE.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_l.
      rewrite Any.pair_split. grind. rewrite !list_insert_insert.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_l.
      rewrite !list_insert_insert. unfold fbody_trivial.
      rewrite /SModTr.trans interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl.
      rewrite bind_ret_r. rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_l.
      exists (tt↑). grind. rewrite !list_insert_insert. steps_l.
      rewrite !interpV_bind interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl.
      rewrite bind_ret_r. grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_l. grind. steps_l.
      exists (tt↑). grind. rewrite !list_insert_insert. steps_l.
      rewrite !interpV_bind interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl. grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_l.
      rewrite Any.pair_split. grind. rewrite !list_insert_insert.
      rewrite Any.upcast_downcast. grind.
      destruct (extrace_has_obs_stream extr i1 t).
      pose proof (t.(Prophecy.coverage) (nth x)). des.
      set proph_map' :=
        λ i,
          if excluded_middle_informative (i = i1)
          then existT t (p3, [])
          else proph_map i.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_l.
      exists (rs_tgt ⋅ (own.iRes_singleton base_γ (has_proph_auth_r (Ensembles.Subtract _ free_ids i1) proph_map')
                ⋅ own.iRes_singleton base_γ (free_id_auth_r (Ensembles.Subtract _ free_ids i1)))).
      grind. steps_l. rewrite !list_insert_insert.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_l.
      assert
        (Own p0 ⊢ |==>
           ((∃ p4 : Prophecy.Pro t, ⌜tt ↑ = tt ↑⌝ ∗
             has_proph i1 (existT t (p4, []))) ∗ ⌜
              tt ↑ = tt ↑⌝) ∗
           Own
           (rs_tgt ⋅ (own.iRes_singleton base_γ
              (has_proph_auth_r
                 (Ensembles.Subtract Prophecy.ID free_ids i1) proph_map')
              ⋅ own.iRes_singleton base_γ
              (free_id_auth_r
                 (Ensembles.Subtract Prophecy.ID free_ids i1))))).
      { iIntros "A". iPoseProof (p2 with "A") as ">[[[_ B] _] [D E]]".
        rewrite RS. iDestruct "E" as "[E F]".
        iAssert (own base_γ (has_proph_auth_r free_ids proph_map)) with "[E]" as "E".
        { rewrite own.Own_eq own.own_eq /own.own_def /own.Own_def //=. }
        iAssert (own base_γ (free_id_auth_r free_ids)) with "[F]" as "F".
        { rewrite own.Own_eq own.own_eq /own.own_def /own.Own_def //=. }
        iAssert ( |==> (own base_γ (has_proph_auth_r (Ensembles.Subtract _ free_ids i1) proph_map') ∗ has_proph i1 (existT t (p3, []))))%I with "[E]" as ">[E G]"; cycle 1.
        iAssert ( |==> (own base_γ (free_id_auth_r (Ensembles.Subtract _ free_ids i1))))%I with "[B F]" as ">B"; cycle 1.
        { iFrame. iModIntro. iSplit; et.
          rewrite own.own_eq /own.own_def own.Own_eq /own.Own_def.
          iCombine "D E B" as "E". iFrame. }
        - iCombine "B F" as "B". iStopProof.
          apply own_update. unfold free_id_r, free_id_auth_r.
          apply discrete_fun_update. i. discrete_fun_tac.
          destruct excluded_middle_informative; cycle 1.
          { do 2 destruct excluded_middle_informative; try done.
            { exfalso. apply n0. red. red. split; et. ii. inv H1. }
            exfalso. do 2 red in s. des. apply n0. apply s. }
          subst. destruct excluded_middle_informative; clarify.
          destruct excluded_middle_informative; clarify.
          { inv s. exfalso. apply H2. econs. }
          apply (@auth_update_dealloc _ (optionUR (exclR unitO))).
          set (Some (@Excl (ofe_car unitO) ())) at 1.
          replace o with (Excl' () ⋅ ε).
          apply cancel_local_update_unit.
          { typeclasses eauto. }
          rewrite right_id. et.
        - unfold has_proph.
          iAssert
            ( |==>
               own base_γ
               ((has_proph_auth_r (Ensembles.Subtract Prophecy.ID free_ids i1)
                  proph_map') ⋅
               (has_proph_r i1 (existT t (p3, [])))))%I with "[E]" as ">[E G]"; cycle 1.
          { iModIntro. iFrame. }
          iStopProof.
          apply own_update. unfold has_proph_r, has_proph_auth_r.
          apply discrete_fun_update. i. discrete_fun_tac.
          destruct (decide (a = i1)); cycle 1.
          { rewrite discrete_fun_lookup_singleton_ne; et.
            rewrite right_id. unfold proph_map'.
            destruct (excluded_middle_informative (a = i1)); clarify.
            des_ifs; exfalso; cycle 1. { inv s. }
            apply n1. split; et. ii. apply n. inv H1. }
          subst. destruct excluded_middle_informative; clarify.
          rewrite discrete_fun_lookup_singleton.
          destruct excluded_middle_informative.
          { exfalso. inv s. apply H2. econs. }
          unfold proph_map'.
          destruct excluded_middle_informative; clarify.
          apply (@auth_update_alloc _ (optionUR (exclR ProphInstO))).
          apply alloc_option_local_update. done. }
      assert
        (✓ (rs_tgt ⋅ (own.iRes_singleton base_γ
              (has_proph_auth_r
                 (Ensembles.Subtract Prophecy.ID free_ids i1) proph_map')
              ⋅ own.iRes_singleton base_γ
              (free_id_auth_r
                 (Ensembles.Subtract Prophecy.ID free_ids i1))))).
      { assert
          (p0 ~~>
             (rs_tgt ⋅ (own.iRes_singleton base_γ
                (has_proph_auth_r
                   (Ensembles.Subtract Prophecy.ID free_ids i1) proph_map')
                ⋅ own.iRes_singleton base_γ
                (free_id_auth_r
                   (Ensembles.Subtract Prophecy.ID free_ids i1))))).
        { apply Own_bupd_update. iIntros "A".
          iPoseProof (H1 with "A") as ">[A B]". iModIntro. iFrame. }
        rewrite cmra_valid_validN. i.
        specialize (H2 n ε). ss. apply H2. clear H2. revert n.
        rewrite -cmra_valid_validN. et. }
      exists (conj H2 H1).
      grind. rewrite list_insert_insert. step_l.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_l.
      rewrite Any.pair_split. grind. rewrite !list_insert_insert.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_l.
      rewrite !list_insert_insert. rewrite !interpV_ret. grind.
      rewrite !interpV_tau !interpV_ret. grind.
      rewrite (@unfold_iterV _ _ _ (proph_handle_callE _)). simpl.
      rewrite !list_lookup_insert; [| erewrite <- Forall2_length; et].
      ss. grind. steps_r.
      rewrite !list_insert_insert.
      apply wsimg_endsim. i. eapply CIH. et.
      { apply Forall2_insert; et. }
      4:{ refl. }
      2:{ refl. }
      3:{ apply WFMODS. }
      2:{ et. }
      i. destruct (decide (id = i1)); cycle 1.
      { assert (~ free_ids id). { ii. apply NOTFREE. split; et. ii. inv H5. }
        apply INV in H4. des.
        replace (proph_map' id) with (proph_map id) by now unfold proph_map'; des_ifs.
        esplits; et.
        punfold H4. inversion H4.
        { subst. apply inj_pair2 in H9. rewrite H9 in H11.
          destruct r1, ret. apply inj_pair2 in H11.
          apply (f_equal (fun y => y 0%fin)) in H11; clarify. pclearbot.
          punfold STEP. inversion STEP. clexteq.
          apply (f_equal (fun y => y 0%fin)) in H7; clarify. pclearbot.
          punfold STEP0. inversion STEP0. clexteq.
          apply (f_equal (fun y => y 0%fin)) in H7; clarify. pclearbot.
          et. }
        { exfalso. apply NE. left. clexteq. split; et. }
        { exfalso. apply NE. et. }
        { exfalso. apply NE. et. } }
      subst. clear H1 H2 H3. unfold proph_map'.
      destruct excluded_middle_informative; clarify. ss.
      punfold H. inversion H. clarify. clexteq.
      apply (f_equal (fun y => y 0%fin)) in H2. clarify. pclearbot.
      esplits; et. i. red.
      eapply consistent_sany_equiv with (i:=i') in H0.
      des. esplits; et. rewrite H0.
      f_equal. extensionalities. clear. revert x.
      induction H2; ss; i; des_ifs.
    - grind. unfold LModTr.pure_state at 1 3. grind.
      apply wsimg_io_proph. i. clarify. rename extr' into extr.
      steps_l. grind. steps_l. steps_r.
      unfold proph_resolveI, ProphecyI.resolve, ProphecyA.resolve_spec, fspec_simple.
      unfold precond, postcond. destruct p. ss. destruct s, p, p. ss.
      unfold cfunU, SB.sandbox_body, SB.sandbox, ModTr.trans_ktree, ModTr.trans, SModTr.trans.
      simpl. rewrite !SRed.ret. grind.
      rewrite !interpV_bind !interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl.
      rewrite bind_ret_r. grind. rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et.
      grind. unfold LModTr.pure_state at 1. grind. steps_l. grind.
      steps_l. rewrite !list_insert_insert.
      simpl. rewrite !interpV_bind !interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl. grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_l. grind.
      rewrite !list_insert_insert. rewrite Any.pair_split. grind.
      rewrite Any.upcast_downcast. grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_l. grind. steps_l.
      rewrite !list_insert_insert.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_l. grind. steps_l.
      rewrite !list_insert_insert.
      des.
      assert (Own p1 ⊢ ⌜arg = (i1, o↑↑)↑⌝).
      { iIntros "A". iPoseProof (p3 with "A") as ">[[[A B] C] D]". iFrame. }
      apply Own_pure_soundness in H; et. clarify.
      assert (Own p1 ⊢ |==> ((⌜(i1, o ↑↑) ↑ = (i1, o ↑↑) ↑⌝ ∗ has_proph i1 (existT x (p, l))) ∗ ⌜p0 = (i1, o ↑↑) ↑⌝) ∗ Own (rs_tgt ⋅ rs_proph)).
      { iIntros "A". iPoseProof (p3 with "A") as ">[A B]". iFrame.
        iStopProof. apply Own_Upd. et. }
      clear p3. rename H into p3. rewrite RS /has_proph in p3.
      assert (✓ (has_proph_r i1 (existT x (p, l)) ⋅ has_proph_auth_r free_ids proph_map)).
      { eapply Own_pure_soundness; et.
        iIntros "A". iPoseProof (p3 with "A") as ">[[[A B] C] [D E]]".
        iDestruct "E" as "[E F]".
        rewrite own.own_eq /own.own_def own.Own_eq /own.Own_def.
        iCombine "B E" as "B". rewrite -own.iRes_singleton_op.
        replace uPred_ownM with own.Own_def by et.
        rewrite -own.Own_eq.
        iPoseProof (Own_valid with "B") as "%".
        rewrite -uPred.discrete_valid.
        iApply own.iRes_singleton_validI.
        rewrite uPred.discrete_valid. et. }
      assert (~ free_ids i1).
      { unfold has_proph_auth_r, has_proph_r in H.
        specialize (H i1). discrete_fun_tac.
        rewrite discrete_fun_lookup_singleton in H.
        destruct excluded_middle_informative; clarify.
        rewrite comm auth_both_valid_discrete in H. des.
        red in H. des. destruct z. { rewrite -Some_op in H. inv H. }
        inv H. }
      assert (proph_map i1 = existT x (p, l)).
      { specialize (H i1).
        unfold has_proph_r, has_proph_auth_r in H.
        discrete_fun_tac. des_ifs.
        rewrite discrete_fun_lookup_singleton in H.
        rewrite comm auth_both_valid_discrete in H. des.
        red in H. des. destruct z. { rewrite -Some_op in H. inv H. }
        inv H. et. }
      clear H. rename H0 into FREE. rename H1 into PROPH.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_l.
      rewrite Any.pair_split. grind. rewrite !list_insert_insert.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_l.
      rewrite !list_insert_insert. unfold fbody_trivial.
      rewrite /SModTr.trans interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl.
      rewrite bind_ret_r.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_l. grind. steps_l.
      exists (tt↑). grind. rewrite !list_insert_insert. steps_l.
      rewrite !interpV_bind interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl.
      rewrite bind_ret_r. grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_l. grind. steps_l.
      exists (tt↑). grind. rewrite !list_insert_insert. steps_l.
      rewrite !interpV_bind interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl. grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_l.
      rewrite Any.pair_split. grind. rewrite !list_insert_insert.
      rewrite Any.upcast_downcast. grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_l.
      set proph_map' :=
        λ i,
          if excluded_middle_informative (i = i1)
          then existT x (p, o :: l)
          else proph_map i.
      exists
        (rs_tgt
           ⋅ (own.iRes_singleton base_γ
                (has_proph_auth_r free_ids proph_map')
                ⋅ own.iRes_singleton base_γ (free_id_auth_r free_ids))).
      grind. step_l. rewrite list_insert_insert.
      hexploit INV; et. i. des.
      punfold H. inversion H.
      { exfalso. des; clarify. }
      all: cycle 1.
      { exfalso. apply inj_pair2 in H3. rewrite H3 in H5. destruct r1, ret.
        fclarify.
        apply (f_equal (@Any.downcast (Prophecy.ID * SAny.t))) in H3.
        rewrite !Any.upcast_downcast in H3. clarify. }
      { exfalso. apply NE. right. split; et.
        clexteq. exists i1, (o↑↑). rewrite PROPH. ss. et. }
      { exfalso. apply NE. et. }
      { exfalso. apply NE. et. }
      apply inj_pair2 in H3. rewrite H3 in H5. destruct r1, ret.
      apply (f_equal (@Any.downcast (Prophecy.ID * SAny.t))) in H3.
      rewrite !Any.upcast_downcast in H3. fclarify. pclearbot.
      replace (stream_map SAny.upcast (sfold (scons o0 obs))) with (sfold (scons (o0↑↑) (stream_map SAny.upcast obs))) in H0.
      2:{
        assert (forall {T} (s : stream T), s = match s with sfold (scons hd tl) => sfold (scons hd tl) end).
        { i. destruct s. destruct s. refl. }
        rewrite (H1 _ (stream_map SAny.upcast (sfold (scons o0 obs)))).
        ss. }
      rewrite H2 in H0. clear H2 H. clear o0. clear H4. pclearbot.
      rewrite stream_app_cons in H0. dup PROPH.
      apply (f_equal (projT1)) in PROPH0. ss. clarify.
      assert (projT2 (proph_map i1) = (p, l)).
      { destruct (proph_map i1). ss.
        apply inj_pair2 in PROPH. et. }
      rewrite H in H0. ss.
      clear H. replace (reverse (List.map SAny.upcast l) ++ [o↑↑]) with (reverse (List.map SAny.upcast (o :: l))) in H0; cycle 1.
      { ss. rewrite cons_app reverse_app. et. }
      dup H0. specialize (H0 (List.length (reverse (List.map SAny.upcast (o :: l))))).
      rewrite firstn_length reverse_involutive in H0.
      rename H1 into CONS. rename H0 into CCC. dup CCC.
      red in CCC0. des.
      assert (l0 = o :: l).
      { clear -CCC0. revert CCC0. generalize (o :: l).
        induction l0; ss; i. { destruct l0; ss. }
        destruct l1; ss. inv CCC0.
        apply (f_equal (@SAny.downcast (Prophecy.Obs (projT1 (proph_map i1))))) in H0.
        rewrite !SAny.upcast_downcast in H0. clarify. f_equal. et. }
      rewrite H in CCC1. clear CCC0 H l0.

      assert
        (Own p1 ⊢ |==>
           ((⌜tt ↑ = tt ↑ /\ Prophecy.consistent (projT1 (proph_map i1)) (o :: l) p⌝ ∗
             has_proph i1 (existT (projT1 (proph_map i1)) (p, o :: l))) ∗ ⌜tt ↑ = tt ↑⌝) ∗
           Own
           (rs_tgt ⋅
              (own.iRes_singleton base_γ (has_proph_auth_r free_ids proph_map')
              ⋅ own.iRes_singleton base_γ (free_id_auth_r free_ids)))).
      { iIntros "A". iPoseProof (p3 with "A") as ">[[[A B] C] [D E]]".
        iDestruct "E" as "[E F]".
        iAssert (own base_γ (has_proph_auth_r free_ids proph_map)) with "[E]" as "E".
        { rewrite own.Own_eq own.own_eq /own.own_def /own.Own_def //=. }
        iAssert (own base_γ (free_id_auth_r free_ids)) with "[F]" as "F".
        { rewrite own.Own_eq own.own_eq /own.own_def /own.Own_def //=. }
        iAssert ( |==> (own base_γ (has_proph_auth_r free_ids proph_map') ∗ has_proph i1 (existT (projT1 (proph_map i1)) (p, o :: l))))%I with "[E B]" as ">[E G]"; cycle 1.
        { iFrame. iModIntro. iSplit; et.
          rewrite own.own_eq /own.own_def own.Own_eq /own.Own_def.
          iCombine "D E F" as "E". iFrame. }
        unfold has_proph.
        iAssert
          ( |==>
              own base_γ
              ((has_proph_auth_r free_ids proph_map') ⋅
                 (has_proph_r i1 (existT (projT1 (proph_map i1)) (p, o::l)))))%I with "[B E]" as ">[B E]"; cycle 1.
        { iModIntro. iFrame. }
        iCombine "E B" as "B". iStopProof.
        apply own_update. unfold has_proph_r, has_proph_auth_r.
        apply discrete_fun_update. i. do 2 discrete_fun_tac.
        destruct (decide (a = i1)); cycle 1.
        { rewrite !discrete_fun_lookup_singleton_ne; et.
          rewrite !right_id. unfold proph_map'.
          destruct (excluded_middle_informative (a = i1)); clarify. }
        subst. destruct excluded_middle_informative; clarify.
        rewrite !discrete_fun_lookup_singleton. unfold proph_map'.
        destruct excluded_middle_informative; clarify.
        rewrite - PROPH.
        apply (@auth_update _ (optionUR (exclR ProphInstO))).
        apply option_local_update. apply replace_local_update.
        { typeclasses eauto. } done. }
      assert
        (✓ (rs_tgt ⋅
              (own.iRes_singleton base_γ
                 (has_proph_auth_r free_ids proph_map')
                 ⋅
                 own.iRes_singleton base_γ
                   (free_id_auth_r free_ids)))).
      { assert
          (p1 ~~>
             (rs_tgt ⋅
                (own.iRes_singleton base_γ
                   (has_proph_auth_r free_ids proph_map')
                ⋅ own.iRes_singleton base_γ
                   (free_id_auth_r free_ids)))).
        { apply Own_bupd_update. iIntros "A".
          iPoseProof (H with "A") as ">[A B]". iModIntro. iFrame. }
        rewrite cmra_valid_validN. i.
        specialize (H0 n ε). ss. apply H0. clear H0. revert n.
        rewrite -cmra_valid_validN. et. }
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_l.
      exists (conj H0 H). grind. steps_l. rewrite !list_insert_insert.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_l.
      rewrite !list_insert_insert.
      rewrite Any.pair_split. grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_l.
      rewrite !list_insert_insert.
      rewrite !interpV_ret. grind.
      rewrite (@unfold_iterV _ _ _ (proph_handle_callE _)). simpl.
      rewrite !list_lookup_insert; [| erewrite <- Forall2_length; et].
      ss. grind. steps_r.
      rewrite !list_insert_insert.
      rewrite !interpV_ret bind_ret_l.
      apply wsimg_endsim. i. eapply CIH. et.
      { apply Forall2_insert; et. }
      5:{ apply WFMODS. }
      4:{ refl. }
      3:{ et. }
      2:{ refl. }
      i. destruct (decide (id = i1)); cycle 1.
      { apply INV in NOTFREE. des.
        replace (proph_map' id) with (proph_map id) by now unfold proph_map'; des_ifs.
        esplits; et.
        punfold NOTFREE. inversion NOTFREE.
        { exfalso. des; clarify. }
        { exfalso. clexteq.
          apply (f_equal (@Any.downcast (Prophecy.ID * SAny.t))) in H4.
          rewrite !Any.upcast_downcast in H4. clarify. }
        { subst. apply inj_pair2 in H4.
          apply (f_equal (@Any.downcast (Prophecy.ID * SAny.t))) in H4.
          rewrite !Any.upcast_downcast in H4.
          inversion H4. subst. destruct r1. fclarify. pclearbot.
          punfold STEP0. inv STEP0. fclarify. pclearbot.
          punfold STEP1. inv STEP1. fclarify. pclearbot.
          et. }
        { subst. clexteq. exfalso. apply NE. right. split; et. }
        { exfalso. clexteq. }
        { exfalso. apply NE. et. } }
      subst. clear H H0 H1. unfold proph_map'.
      destruct excluded_middle_informative; clarify. ss.
      esplits; et. punfold STEP. inv STEP. fclarify. pclearbot.
      punfold STEP0. inv STEP0. fclarify. pclearbot. et.
    - grind. unfold LModTr.pure_state at 1 3. grind.
      apply wsimg_io_proph. i. clarify. rename extr' into extr.
      steps_l. grind. steps_l. steps_r.
      unfold proph_closeI, ProphecyI.close, ProphecyA.close_spec, fspec_simple.
      unfold precond, postcond. destruct p. ss.
      unfold cfunU, SB.sandbox_body, SB.sandbox, ModTr.trans_ktree, ModTr.trans, SModTr.trans.
      simpl. rewrite !interpV_bind !interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl.
      rewrite bind_ret_r. grind. rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et.
      grind. unfold LModTr.pure_state at 1. grind. steps_l. grind.
      steps_l. rewrite !list_insert_insert.
      simpl. rewrite !interpV_bind !interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl. grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_l. grind.
      rewrite !list_insert_insert. rewrite Any.pair_split. grind.
      rewrite Any.upcast_downcast. grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_l. grind. steps_l.
      rewrite !list_insert_insert.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_l. grind. steps_l.
      rewrite !list_insert_insert. des.
      assert (Own p0 ⊢ ⌜arg = i1↑⌝).
      { iIntros "A". destruct s as [? [? ?]].
        iPoseProof (p2 with "A") as "> [[[% ?] %] ?]"; clarify.
      }
      apply Own_pure_soundness in H; et. clarify.
      rewrite !SRed.ret. grind.
      destruct s as [x [p' l]].
      assert (Own p0 ⊢
        |==> ((⌜i1 ↑ = i1 ↑⌝ ∗ has_proph i1 (existT x (p', l))) ∗ ⌜p = i1 ↑⌝) ∗ Own (rs_tgt ⋅ rs_proph)).
      { iIntros "A". iPoseProof (p2 with "A") as ">[A B]". iFrame.
        iStopProof. apply Own_Upd. et. }
      clear p2. rename H into p3.
      assert (✓ (has_proph_r i1 (existT x (p', l)) ⋅ has_proph_auth_r free_ids proph_map)).
      { eapply Own_pure_soundness; et.
        iIntros "A". iPoseProof (p3 with "A") as ">[[[A B] C] [D E]]".
        rewrite RS. iDestruct "E" as "[E F]".
        unfold has_proph.
        rewrite own.own_eq /own.own_def own.Own_eq /own.Own_def.
        iCombine "B E" as "B". rewrite -own.iRes_singleton_op.
        replace uPred_ownM with own.Own_def by et.
        rewrite -own.Own_eq.
        iPoseProof (Own_valid with "B") as "%".
        rewrite -uPred.discrete_valid.
        iApply own.iRes_singleton_validI.
        rewrite uPred.discrete_valid. et. }
      assert (~ free_ids i1).
      { unfold has_proph_auth_r, has_proph_r in H.
        specialize (H i1). discrete_fun_tac.
        rewrite discrete_fun_lookup_singleton in H.
        destruct excluded_middle_informative; clarify.
        rewrite comm auth_both_valid_discrete in H. des.
        red in H. des. destruct z. { rewrite -Some_op in H. inv H. }
        inv H. }
      assert (proph_map i1 = existT x (p', l)).
      { specialize (H i1).
        unfold has_proph_r, has_proph_auth_r in H.
        discrete_fun_tac. des_ifs.
        rewrite discrete_fun_lookup_singleton in H.
        rewrite comm auth_both_valid_discrete in H. des.
        red in H. des. destruct z. { rewrite -Some_op in H. inv H. }
        inv H. et. }
      clear H. rename H0 into FREE. rename H1 into PROPH.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_l.
      rewrite Any.pair_split. grind. rewrite !list_insert_insert.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_l.
      rewrite !list_insert_insert. unfold fbody_trivial.
      rewrite /SModTr.trans interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl.
      rewrite bind_ret_r.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_l. grind. steps_l.
      exists (tt↑). grind. rewrite !list_insert_insert. steps_l.
      rewrite !interpV_bind interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl.
      rewrite bind_ret_r. grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_l. grind. steps_l.
      exists (tt↑). grind. rewrite !list_insert_insert. steps_l.
      rewrite !interpV_bind interpV_trigger. simpl.
      rewrite bind_ret_r interpV_trigger. simpl. grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_l.
      rewrite Any.pair_split. grind. rewrite !list_insert_insert.
      rewrite Any.upcast_downcast. grind.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_l.
      exists (rs_tgt ⋅ (own.iRes_singleton base_γ (has_proph_auth_r (Ensembles.Add _ free_ids i1) proph_map)
                ⋅ own.iRes_singleton base_γ (free_id_auth_r (Ensembles.Add _ free_ids i1)))).
      grind. steps_l. rewrite !list_insert_insert.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind.
      unfold LModTr.pure_state at 1. grind. steps_l.
      assert
        (Own p0 ⊢ |==>
           ((⌜tt ↑ = tt ↑⌝ ∗
             free_id (λ y, y = i1)) ∗ ⌜
              tt ↑ = tt ↑⌝) ∗
           Own
           (rs_tgt ⋅ (own.iRes_singleton base_γ
              (has_proph_auth_r
                 (Ensembles.Add Prophecy.ID free_ids i1) proph_map)
              ⋅ own.iRes_singleton base_γ
              (free_id_auth_r
                 (Ensembles.Add Prophecy.ID free_ids i1))))).
      { iIntros "A". iPoseProof (p3 with "A") as ">[[[A B] C] [D E]]".
        rewrite RS. iDestruct "E" as "[E F]".
        unfold has_proph.
        iAssert (own base_γ (has_proph_auth_r free_ids proph_map)) with "[E]" as "E".
        { rewrite own.Own_eq own.own_eq /own.own_def /own.Own_def //=. }
        iAssert (own base_γ (free_id_auth_r free_ids)) with "[F]" as "F".
        { rewrite own.Own_eq own.own_eq /own.own_def /own.Own_def //=. }
        iAssert ( |==> (own base_γ (has_proph_auth_r (Ensembles.Add _ free_ids i1) proph_map)))%I with "[E B]" as ">E"; cycle 1.
        iAssert ( |==> own base_γ
                          ((free_id_auth_r (Ensembles.Add _ free_ids i1))
                          ⋅(free_id_r (λ y, y = i1))))%I with "[F]" as ">[B F]"; cycle 1.
        { iFrame. iModIntro. iSplit; et.
          rewrite own.own_eq /own.own_def own.Own_eq /own.Own_def.
          iCombine "D E B" as "E". iFrame. }
        - iStopProof.
          apply own_update. unfold free_id_r, free_id_auth_r.
          apply discrete_fun_update. i. discrete_fun_tac.
          destruct (excluded_middle_informative (a = i1)); cycle 1.
          { rewrite right_id.
            do 2 destruct excluded_middle_informative; try done.
            { exfalso. apply n0. econs. et. }
            exfalso. inv a0. inv H. }
          subst.
          do 2 destruct excluded_middle_informative; clarify; cycle 1.
          { exfalso. apply n0. econs 2. econs. }
          apply (@auth_update_alloc _ (optionUR (exclR unitO))).
          apply alloc_option_local_update. done.
        - iCombine "B E" as "B".
          iStopProof.
          apply own_update. unfold has_proph_r, has_proph_auth_r.
          apply discrete_fun_update. i. discrete_fun_tac.
          destruct (decide (a = i1)); cycle 1.
          { rewrite discrete_fun_lookup_singleton_ne; et.
            rewrite left_id.
            do 2 destruct excluded_middle_informative; try done.
            { exfalso. apply n0. econs. et. }
            exfalso. inv a0. inv H. }
          subst. destruct excluded_middle_informative; clarify.
          rewrite discrete_fun_lookup_singleton.
          destruct excluded_middle_informative; cycle 1.
          { exfalso. apply n0. econs 2. econs. }
          rewrite PROPH. rewrite comm.
          apply (@auth_update_dealloc _ (optionUR (exclR ProphInstO))).
          set (Some (@Excl (ofe_car ProphInstO) (existT x (p', l)))) at 1.
          replace o with (Some (@Excl (ofe_car ProphInstO) (existT x (p', l))) ⋅ ε) at 1.
          apply cancel_local_update_unit.
          { typeclasses eauto. }
          rewrite right_id. et. }
      assert
        (✓ (rs_tgt ⋅ (own.iRes_singleton base_γ
              (has_proph_auth_r
                 (Ensembles.Add Prophecy.ID free_ids i1) proph_map)
              ⋅ own.iRes_singleton base_γ
              (free_id_auth_r
                 (Ensembles.Add Prophecy.ID free_ids i1))))).
      { assert
          (p0 ~~>
             (rs_tgt ⋅ (own.iRes_singleton base_γ
                (has_proph_auth_r
                   (Ensembles.Add Prophecy.ID free_ids i1) proph_map)
                ⋅ own.iRes_singleton base_γ
                (free_id_auth_r
                   (Ensembles.Add Prophecy.ID free_ids i1))))).
        { apply Own_bupd_update. iIntros "A".
          iPoseProof (H with "A") as ">[A B]". iModIntro. iFrame. }
        rewrite cmra_valid_validN. i.
        specialize (H0 n ε). ss. apply H0. clear H0. revert n.
        rewrite -cmra_valid_validN. et. }
      exists (conj H0 H).
      grind. rewrite list_insert_insert. step_l.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_l.
      rewrite Any.pair_split. grind. rewrite !list_insert_insert.
      rewrite unfold_iterV. simpl.
      rewrite !list_lookup_insert; et. grind. steps_l.
      rewrite !list_insert_insert. rewrite !interpV_ret. grind.
      rewrite (@unfold_iterV _ _ _ (proph_handle_callE _)). simpl.
      rewrite !list_lookup_insert; [| erewrite <- Forall2_length; et].
      ss. grind. steps_r.
      rewrite !list_insert_insert.
      rewrite !interpV_ret bind_ret_l.
      apply wsimg_endsim. i. eapply CIH. et.
      { apply Forall2_insert; et. }
      5:{ apply WFMODS. }
      4:{ refl. }
      3:{ et. }
      2:{ refl. }
      i. hexploit INV. { instantiate (1:=id). ii. apply NOTFREE. econs. et. }
      i. des. assert (NEQ: i1 <> id). { ii. apply NOTFREE. econs 2. clarify. }
      esplits; et.
      punfold H2. inversion H2.
      { subst. apply inj_pair2 in H7. rewrite H7 in H9.
        destruct r1, ret. fclarify. pclearbot.
        punfold STEP. inversion STEP. fclarify. pclearbot.
        punfold STEP0. inversion STEP0. fclarify. pclearbot. et. }
      { exfalso. apply NE. left. clexteq. split; et. }
      { exfalso. apply NE. et. }
      { exfalso. apply NE. et. }
    - grind. steps_r. steps_l. rewrite !Any.pair_split. grind.
      endsim. { apply Forall2_insert; et. apply NEXT. }
      i. hexploit INV; et. i. des. esplits; et. punfold H0. inv H0.
      fclarify. pclearbot. et.
    - grind. steps_r. steps_l. rewrite !Any.pair_split. grind.
      do 2 rewrite unfold_iterV. grind.
      rewrite !list_lookup_insert; et; cycle 1.
      { erewrite <- Forall2_length; et. }
      grind. steps_r. steps_l. rewrite !list_insert_insert.
      endsim. { apply Forall2_insert; et. }
      i. hexploit INV; et. i. des. esplits; et. punfold H0. inv H0.
      fclarify. pclearbot.
      punfold STEP. inv STEP. fclarify. pclearbot. et.
    - grind. steps_r. steps_l. rewrite !Any.pair_split. grind.
      rewrite !Any.upcast_downcast. grind.
      do 2 rewrite unfold_iterV. grind.
      rewrite !list_lookup_insert; et; cycle 1.
      { erewrite <- Forall2_length; et. }
      grind. unfold LModTr.pure_state at 1 4. grind.
      steps_r. steps_l. exists (x ⋅ rs_proph). grind.
      steps_r. steps_l. rewrite !list_insert_insert.
      do 2 rewrite unfold_iterV. grind.
      rewrite !list_lookup_insert; et; cycle 1.
      { erewrite <- Forall2_length; et. }
      grind. unfold LModTr.pure_state at 1 4. grind.
      steps_r. steps_l. move x0 at bottom.
      assert (Own (rs_tgt ⋅ rs_proph) ⊢ |==> iP ∗ Own (x ⋅ rs_proph)).
      { iIntros "[A B]". des. iPoseProof (x1 with "A") as ">[A C]".
        iCombine "C B" as "B". iModIntro. iFrame. }
      assert (Own (rs_tgt ⋅ rs_proph) ⊢ |==> Own (x ⋅ rs_proph)).
      { iIntros "A". iPoseProof (H with "A") as ">[B C]". iModIntro. et. }
      assert (✓ (x ⋅ rs_proph)).
      { apply Own_bupd_update in H0.
        assert (rs_src ~~> x ⋅ rs_proph). { etrans; et. }
        red in H1. rewrite cmra_valid_validN. i.
        specialize (H1 n ε). ss. apply H1. clear H1. revert n.
        rewrite -cmra_valid_validN //=. }
      esplits. Unshelve. all: et. all: cycle 1.
      { split; et. iIntros "A". eapply Own_Upd in REQ.
        iPoseProof (REQ with "A") as ">A". iApply H. et. }
      grind. steps_l. steps_r.
      rewrite !list_insert_insert.
      do 2 rewrite unfold_iterV. grind.
      rewrite !list_lookup_insert; et; cycle 1.
      { erewrite <- Forall2_length; et. }
      grind. steps_r. steps_l. rewrite !Any.pair_split. grind.
      rewrite !list_insert_insert.
      do 2 rewrite unfold_iterV. grind.
      rewrite !list_lookup_insert; et; cycle 1.
      { erewrite <- Forall2_length; et. }
      grind. steps_r. steps_l. rewrite !list_insert_insert.
      endsim. { apply Forall2_insert; et. }
      2:{ refl. }
      clear H H0 H1 H2.
      i. hexploit INV; et. i. des. esplits; et. punfold H. inv H.
      fclarify. pclearbot.
      punfold STEP. inversion STEP. clexteq.
      apply (f_equal (fun y => y 0%fin)) in H3; clarify. pclearbot.
      punfold STEP0. inversion STEP0. clexteq.
      apply (f_equal (fun y => y 0%fin)) in H1; clarify. pclearbot.
      punfold STEP1. inversion STEP1. clexteq.
      apply (f_equal (fun y => y 0%fin)) in H3; clarify. pclearbot.
      punfold STEP2. inv STEP2. fclarify. pclearbot.
      punfold STEP3. inv STEP3. fclarify. pclearbot.
      punfold STEP2. inv STEP2. fclarify. pclearbot. et.
    - grind. steps_r. steps_l. rewrite !Any.pair_split. grind.
      rewrite !Any.upcast_downcast. grind.
      do 2 rewrite unfold_iterV. grind.
      rewrite !list_lookup_insert; et; cycle 1.
      { erewrite <- Forall2_length; et. }
      grind. unfold LModTr.pure_state at 1 4. grind.
      steps_l. steps_r. unshelve eexists.
      { rewrite comm. eapply cmra_discrete_total_update.
        { etrans; last apply cmra_update_op_l; apply REQ. }
        rewrite comm //.
      }
      grind.
      steps_r. steps_l. rewrite !list_insert_insert.
      do 2 rewrite unfold_iterV. grind.
      rewrite !list_lookup_insert; et; cycle 1.
      { erewrite <- Forall2_length; et. }
      grind.
      steps_l; steps_r.
      rewrite !Any.pair_split /=; grind.
      rewrite !list_insert_insert.
      do 2 rewrite unfold_iterV. grind.
      rewrite !list_lookup_insert; et; cycle 1.
      { erewrite <- Forall2_length; et. }
      grind.
      steps_r. steps_l.
      rewrite !list_insert_insert.
      endsim. { apply Forall2_insert; et. }
      2:{ rewrite REQ assoc //. }
      i. hexploit INV; et. i. des. esplits; et. clear - H0.
      punfold H0. inv H0. fclarify. pclearbot.
      punfold STEP. inversion STEP. clexteq.
      apply (f_equal (fun y => y 0%fin)) in H1; clarify. pclearbot.
      punfold STEP0. inversion STEP0. clexteq.
      apply (f_equal (fun y => y 0%fin)) in H0; clarify. pclearbot.
      punfold STEP1. inversion STEP1. clexteq.
      apply (f_equal (fun y => y 0%fin)) in H0; clarify. pclearbot.
      punfold STEP2. inv STEP2. fclarify. pclearbot.
      punfold STEP3. pfold. eauto.
  Qed.

  (* we can't give an prophecy value in initial state *)
  (* prophecy's invariant is that prophecy value should consistent with full prophecy call behavior *)
  (* prophecy module can't expect full program's behavior locally *)
  (* If prophecy value is given in initial state, context module cannot be parameterized and should have expected behavior *)
  Theorem adequacy_refines_mod sp
      (r_src r_tgt r_proph : Σ)
      (WFMODT : Mod.wf (md ★ ProphecyI.t))
      (WFR : ✓ r_src)
      (REQ : r_src ~~> r_tgt ⋅ r_proph)
      (RS : r_proph ≡ (own.iRes_singleton base_γ (has_proph_auth_r (Ensembles.Full_set _) (fun _ => dummy_prophinst)) ⋅ own.iRes_singleton base_γ (free_id_auth_r (Ensembles.Full_set _)))) :
    refines_lmod (Mod.to_lmod (md ★ (ProphecyA.t sp)) r_src)
      (Mod.to_lmod (md ★ ProphecyI.t) r_tgt).
  Proof using PHYS.
    ii. apply prophecy_tgt_exbeh_exists in PR; et. des.
    pose proof (extrace_has_obs_stream extr).
    revert PR0. unfold LMod.compile. unfold proph_compile.
    remember (alist_find None _). set (alist_find None _).
    assert (o = o0).
    { rewrite Heqo. unfold o0, Mod.to_lmod, LMod.prog. ss.
      rewrite !map_app. rewrite !alist_find_app_o.
      set (Mod.fnsems _). do 2 (unfold_mod; ss). }
    rewrite -H0. clear o0 H0. destruct o; simpl; cycle 1.
    { i. unfold triggerUB. rewrite bind_bind.
      pfold. econs. econs. i. clarify. }
    rewrite !bind_ret_l. unfold ITree.map. i.
    eapply simg_ex_adequacy; et.
    replace (Mod.initial_st ProphecyI.t) with (Mod.initial_st (ProphecyA.t sp)) in PR0; cycle 1.
    { do 2 (unfold_mod; ss). }
    eapply adequacy_aux; et; cycle 1.
    { i. exfalso. apply NOTFREE. ss. }
    econs; last econs. eapply pmod_fun_wf_sim.
    rewrite Heqo. unfold LMod.prog. ss.
    rewrite !map_app alist_find_app_o. des_ifs; et.
    exfalso. unfold LMod.prog in Heqo. ss.
    rewrite !map_app alist_find_app_o in Heqo. des_ifs; et.
    symmetry in Heqo. apply alist_find_some in Heqo.
    revert Heqo. unfold_mod. ss. i. des; clarify.
  Qed.

  Theorem adequacy_refines sp (P : iProp Σ):
    refines (md ★ (ProphecyA.t sp), (P ∗ ProphecyA.initial_cond)%I) (md ★ ProphecyI.t, P).
  Proof using PHYS.
    ii. ss. split; [apply src_mod_wf; et|].
    i. rewrite assoc in SRC. apply Own_bupd_split in SRC; et. des.
    rewrite -Own_op in SRC. apply Own_bupd_update in SRC. dup SRC.
    red in SRC. specialize (SRC 0 None). dup WFR. rewrite cmra_valid_validN in WFR.
    specialize (WFR 0). apply SRC in WFR. apply cmra_discrete_valid in WFR.
    ss.
    unfold ProphecyA.initial_cond, has_proph_auth, free_id_auth in SRC1.
    assert (Own a2 ⊢ Own (own.iRes_singleton base_γ (has_proph_auth_r (Ensembles.Full_set Prophecy.ID) (λ _ : Prophecy.ID, dummy_prophinst)) ⋅ own.iRes_singleton base_γ (free_id_auth_r (Ensembles.Full_set Prophecy.ID)))).
    { iIntros "A". iPoseProof (SRC1 with "A") as "[A B]".
      rewrite own.own_eq /own.own_def. iCombine "A B" as "B".
      rewrite own.Own_eq /own.Own_def. et. }
    rewrite own.Own_eq /own.Own_def in H.
    apply uPred.ownM_general_soundness in H. red in H.
    rewrite upred.uPred_ownM_unseal in H. unfold upred.uPred_ownM_def in H.
    red in H. des. rewrite H in SRC2. rewrite H in WFR. rewrite comm in WFR, SRC2.
    rewrite -assoc in WFR, SRC2. exists (z⋅ a1). splits.
    - apply cmra_valid_op_r in WFR. et.
    - iIntros "[A B]". iModIntro. iApply SRC0. et.
    - rewrite comm in SRC2.
      eapply adequacy_refines_mod; et.
    - eapply cmra_valid_op_r. et.
  Qed.

  End ProphIA.

End ProphIA.
