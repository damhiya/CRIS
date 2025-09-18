Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics.
Require Import MInline MInlineIntro MInlineElim ElimRel.

Lemma cancel_spawn `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG} md sp fn args :
  CANCEL_GOAL md sp (NativeSpawnE fn args) (HoareSpawnE fn args (sp fn)).
Proof.
  r; i. assert (VP0:=VP). destruct VP0 as [VP1 VP2]. r in VP1.
  rewrite /sp_from /to_sp in VP1. setoid_rewrite alist_find_map_snd in VP1.
  ziter_l. ziter_r. rewrite x0 x1 /=. zstep_l.
  rewrite !alist_find_map_snd.
  destruct (alist_find (Some fn) (SMod.fnsems md)) eqn: FIND; rewrite !FIND; cycle 1.
  { s. zstep_l. }
  destruct f as [[msk scp] [fspo bd]].
  assert (WFSCP: incl scp (SMod.scopes md)).
  { etrans; [|apply SMod.well_scoped_fns].
    rewrite /fnsems_scopes. erewrite FIND. refl.
  }

  destruct (sp fn) eqn: E; s; cycle 1.
  { des. specialize (VP2 fn). rewrite E /sp_from /to_sp alist_find_map_snd FIND /= in VP2.
    destruct fspo; ss. destruct f; ss. r in VP0. hexploit VP0; eauto. i; ss. }
  { (* the spawnee has a non-trivial spec *)
    destruct f.
    { ired. zstep_r. }
    destruct fspo; cycle 1.
    { des. r in VP0. hexploit VP0; eauto; i; ss. }
    destruct f.
    { des. specialize (VP2 fn). rewrite E /sp_from /to_sp alist_find_map_snd FIND // in VP2. }
    ired. ziter_l. zstep_l.
    do 2 zstep_r.
    ziter_r; zstep_r.
    ziter_r; do 2 zstep_r.
    ziter_r; zstep_r.
    ziter_r; zstep_r.
    rewrite !alist_find_map_snd FIND /=. ired.
    ziter_r; zstep_r.
    ziter_r; zstep_r.
    ziter_r; zstep_r.
    rewrite YieldToken_gen in RS.
    hexploit (Own_bupd_split).
    { iIntros "S". iPoseProof (RS with "S") as ">(D & R & TA & T & [YA NY] & Y & W)".
      iModIntro. iCombine "D TA T YA Y W" as "P". iCombine "R NY" as "Q".
      iSplitL "P"; [iApply "P"|iApply "Q"]. }
    { eauto. }
    intros [r_t1 [r_t2 [Hr_t [Hr_t1 Hr_t2]]]].
    exists r_t2. zstep_r.
    ziter_r; zstep_r.
    assert (RES: ✓ r_t2 ∧ (Own r_t2 ⊢ |==> YIELD (length tgts) ∗ Own r_t)).
    { split; eauto.
      { eapply Own_wand_valid; [iIntros "S"; iMod (Hr_t with "S") as "[_ $]"; done|eauto]. }
      { rewrite Hr_t2 EQLEN2 EQLEN. iIntros "[$ $]"; done. }
    }
    exists RES.
    zstep_r.
    do 4 (ziter_r; zstep_r).
    ziter_r; do 2 zstep_r.
    ziter_r; do 2 zstep_r.
    do 3 (ziter_r; zstep_r).
    zprogress. gbase.
    des; hexploit (Own_bupd_split); et.
    intros [r_t3 [r_t4 [Hr_t3 [Hr_t4 Hr_t5]]]].
    eapply CIH; eauto.
    { rewrite -!insert_app_l; try lia.
      instantiate (1:=<[cid:=ε]>(rs_diff ++ [r_t3])).
      econs; first (rewrite !length_insert !length_app /=; lia).
      econs; first (rewrite !length_insert !length_app /=; lia).
      intros i ???; destruct (decide (i = cid)).
      { subst; rewrite ?list_lookup_insert; try (rewrite length_app /=; lia).
        do 3 (intros INV; inv INV).
        econs; eauto. rewrite -EQLEN; eapply KTR.
      }
      rewrite !list_lookup_insert_ne //.
      destruct (decide (i < length srcs)).
      { rewrite !lookup_app_l; try lia. ii; eapply REL; eauto. }
      destruct (decide (i = length srcs)); cycle 1.
      { rewrite ?lookup_ge_None_2; ss; rewrite ?length_app /=; lia. }
      subst; rewrite list_lookup_length EQLEN list_lookup_length -EQLEN -EQLEN2 list_lookup_length.
      do 3 (intros INV; inv INV).

      rewrite /ModTr.trans_ktree !sandbox_inline_commute /SB.sandbox_body; try by eauto.
      rewrite /SModTr.trans_ktree /SModTr.trans_body.
      replace (SModTr.HoareFun (Some _)) with (Seal.sealing "temp" (SModTr.HoareFun (Some (fspec_spawn precond0 postcond0)))); cycle 1.
      { unseal "temp". refl. }
      ss. unseal "temp".
      rewrite (@MIRed_HoareFun _ _ _ _ _ _ _ _ _ md sp msk scp bd (Some (fspec_spawn precond0 postcond0)) x3 fn meta0 precond0 postcond0); eauto.
      rewrite SBRed.tau MIRed.tau.
      hexploit (VP1 fn); rewrite FIND /=; revert E; intros ->; ss; intros Himp.
      hexploit (Himp (length tgts) x); intros [x' [PRE ?]].
      eapply thread_rel_spawn; eauto.
      { destruct rs_diff; ss. }
      { iIntros "X //". iPoseProof (Hr_t4 with "X") as "X".
        rewrite EQLEN2 EQLEN. unfold FSpec.precond, FSpec.postcond in *.
        iMod (PRE with "X") as "X"; done.
      }
      { ss; eapply elim_rel_cancel; eauto. }
    }
    rewrite insert_app_l; last lia.
    rewrite Hr_t Hr_t1 Hr_t3 Hr_t5 list_insert_id // big_sepL_app /= right_id last_length.
    iIntros ">(($ & $) & >[$ $])"; done.
  }
      (* Experimental *)
      (* rewrite interpV_bind.
      set (ktr := λ x8, interpV _ _).
      eapply (eq_ind ktr); cycle 1.
      { subst ktr; extensionalities x8; destruct x8.
        rewrite interpV_bind.
        (* Set Printing All. *)
        instantiate (1:= λ x,
          vret <- interpV ModTr.handle_hmodE (inline_body (sandboxed_prog (SMod.to_hmod sp md)) (SB.sandbox img msk scp (SModTr.trans (if img then sp else sp_none) (bd x.2))));;
          interpV ModTr.handle_hmodE (elim_spawnee_postcond (fspo_post fspo) x.1 vret)).
        ss.
      }
        subst ktr.
      }
      eapply eq_ind; cycle 1.
        2:{ }
      } *)
      (* econs; eauto; cycle 1.
      { rewrite (bind_ret_r_rev (interpV _ _)) //. }
      hexploit (VP1 fn); rewrite FIND /=; revert E; destruct img0; ss; intros ->; ss; intros Himp.
      hexploit (Himp x); intros [x' [PRE ?]].
      pfold; eapply (elim_rel_spawnee_pre sp _ x'); last refl; ss; cycle 1.
      { destruct fspo; ss; iIntros "X //". iApply PRE; iApply Hr_t1; done. }
      left. ginit.
      guclo elim_rel_bindC_spec; rewrite (bind_ret_r_rev (inline_body _ _)); econs; eauto.
      { gfinal; right. eapply elim_rel_cancel; eauto. r; esplits; eauto. }
      intros ?; gfinal; right; pfold; rewrite (bind_ret_r_rev (elim_spawnee_postcond _ _ _)).
      eapply elim_rel_spawnee_post; eauto.
    }
    rewrite insert_app_l; last lia.
    rewrite list_insert_id // big_sepL_app /= right_id RS Hr_t Hr_t2.
    iIntros "> [$ > [$ $]]"; done.
  } *)
  (* { (* fn has a trivial spec in sp *) *)
  (*   ired. zstep_r. *)
  (*   ziter_l; zstep_l. *)
  (*   rewrite !alist_find_map_snd FIND /=; ired. *)
  (*   ziter_r; zstep_r. *)
  (*   zprogress. gbase. *)
  (*   eapply CIH. *)
  (*   { rewrite -!insert_app_l; try lia. *)
  (*     instantiate (1:=<[cid:=ε]>(rs_diff ++ [ε])). *)
  (*     econs; first (rewrite !length_insert !length_app /=; lia). *)
  (*     econs; first (rewrite !length_insert !length_app /=; lia). *)
  (*     intros i ???; destruct (decide (i = cid)). *)
  (*     { subst; rewrite ?list_lookup_insert; try (rewrite length_app /=; lia). *)
  (*       do 3 (intros INV; inv INV). *)
  (*       econs; eauto. rewrite -EQLEN; eapply KTR. *)
  (*     } *)
  (*     rewrite !list_lookup_insert_ne //. *)
  (*     destruct (decide (i < length srcs)). *)
  (*     { rewrite !lookup_app_l; try lia. ii; eapply REL; eauto. } *)
  (*     destruct (decide (i = length srcs)); cycle 1. *)
  (*     { rewrite ?lookup_ge_None_2; ss; rewrite ?length_app /=; lia. } *)
  (*     subst; rewrite list_lookup_length EQLEN list_lookup_length -EQLEN -EQLEN2 list_lookup_length. *)
  (*     do 3 (intros INV; inv INV). *)
  (*     rewrite /ModTr.trans_ktree !sandbox_inline_commute /SB.sandbox_body //=. *)
  (*     rewrite (MIRed_HoareFun _ _ fn) //= if_simpl SBRed.tau MIRed.tau. *)
  (*     (* econs; eauto; cycle 1. *)
  (*     { rewrite bind_ret_r //. } *) *)
  (*     (* rewrite !sandbox_inline_commute //. *)
  (*     rewrite !if_simpl /SB.sandbox_body /= (MIRed_HoareFun _ _ fn) //. *) *)

  (*     assert (Himpl : fspec_imply (fspec_flat fspo) fspec_trivial). *)
  (*     { hexploit (VP1 fn); rewrite FIND /=; intros Himpl. *)
  (*       destruct img0. *)
  (*       { rewrite E in Himpl; ss. } *)
  (*       { etrans; eauto. } *)
  (*     } *)
  (*     hexploit (Himpl ()); intros [? [PRE ?]]. *)
  (*     eapply thread_rel_spawn; eauto. *)
  (*     { destruct rs_diff; ss. } *)
  (*     { destruct fspo; ss. *)
  (*       { iIntros "X //". iApply PRE; done. } *)
  (*       { iIntros "X //". } *)
  (*     } *)
  (*     { ss; eapply elim_rel_cancel; eauto. } *)
  (*   } *)
  (*   { eauto. } *)
  (*   { rewrite insert_app_l; last lia. *)
  (*     rewrite list_insert_id // big_sepL_app /= right_id RS. *)
  (*     iIntros "> [$ $] !>"; iApply Own_unit. *)
  (*   } *)
  (* } *)
(*SLOW*)Qed.
