Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics CancelTactics.
Require Import MInline MInlineIntro MInlineElim ElimRel.

Local Ltac sil := iter_l; rewrite ?lookup_app_l ?length_insert // !list_lookup_insert ?length_insert //.
Local Ltac snl := norm_l; rewrite -?insert_app_l //= !list_insert_insert ?bind_ret_l.
Local Ltac sir :=
  match goal with
  | [ EQLEN : length _ = length _ |- _ ] => iter_r; rewrite ?lookup_app_l ?length_insert // !list_lookup_insert ?length_insert // -EQLEN //
  end.
Local Ltac snr := norm_r; rewrite -?insert_app_l //= !list_insert_insert ?bind_ret_l.

Lemma cancel_spawn `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG} md sp fn args :
  CANCEL_GOAL md sp (NativeSpawnE fn args) (HoareSpawnE fn args (sp fn)).
Proof.
  r; i. subst.
  (* rewrite /sp_from /to_sp in WFS. setoid_rewrite alist_find_map_snd in WFS. *)
  iter_l. iter_r. rewrite x0 x1 /=. step_l. norm_l.
  rewrite /LMod.prog /Mod.to_lmod /= !alist_find_map_snd.

  destruct (alist_find (Some fn) (SMod.fnsems md)) eqn: FIND; rewrite !FIND; cycle 1.
  { s. step_l. i; ss. }
  destruct f as [[[img msk] scp] [fspo bd]].
  assert (WFSCP: incl scp (SMod.scopes md)).
  { etrans; [|apply SMod.well_scoped_fns].
    rewrite /fnsems_scopes. erewrite FIND. refl.
  }

  assert (EQ: sp_from md fn = fspo).
  { rewrite /sp_from /to_sp alist_find_map_snd /= FIND //. }
  rewrite !EQ /=.
  r in WFS. hexploit WFS; eauto; i; ss; des; subst img.
  destruct fspo; ss. destruct f.
  { ired. step_r. i; ss. }

  ired. norm_l. norm_r.
  step_r. i. step_r. norm_r.

  sil. step_l. snl.
  
  ziter_l. ziter_r. rewrite x0 x1 /=. zstep_l.
  rewrite !alist_find_map_snd.
  destruct (alist_find (Some fn) (SMod.fnsems md)) eqn: FIND; rewrite !FIND; cycle 1.
  { s. zstep_l. }
  destruct f as [[[img msk] scp] [fspo bd]].
  assert (WFSCP: incl scp (SMod.scopes md)).
  { etrans; [|apply SMod.well_scoped_fns].
    rewrite /fnsems_scopes. erewrite FIND. refl.
  }

  assert (EQ: sp_from md fn = fspo).
  { rewrite /sp_from /to_sp alist_find_map_snd /= FIND //. }
  rewrite !EQ /=.
  r in WFS. hexploit WFS; eauto; i; ss; des; subst img.
  destruct fspo; ss. destruct f.
  { ired. zstep_r. }
    
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
  { iIntros "S". iPoseProof (RS with "S") as ">(D & R & TA & [YA NY])".
    iModIntro. iCombine "D TA YA" as "P". iCombine "R NY" as "Q".
    iSplitL "P"; [iApply "P"|iApply "Q"]. }
  { eauto. }
  intros [r_t1 [r_t2 [Hr_t [Hr_t1 Hr_t2]]]].
  exists r_t2. zstep_r.
  ziter_r; zstep_r.
  assert (RES: ✓ r_t2 ∧ (Own r_t2 ⊢ |==> YIELD (length tgts) ∗ Own r_t)).
  { split; eauto.
    { eapply Own_wand_valid; [iIntros "S"; iMod (Hr_t with "S") as "[_ $]"; done|eauto]. }
    { rewrite Hr_t2 EQLEN2 -EQLEN. iIntros "[$ $]"; done. }
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
    replace (SModTr.HoareFun) with (Seal.sealing "temp" (SModTr.HoareFun)); cycle 1.
    { unseal "temp". refl. }
    ss. unseal "temp".
    rewrite (@MIRed_HoareFun _ _ _ _ _ _ _ _ _ md (sp_from md) true msk scp bd (Some (fspec_spawn precond postcond)) x3 (Some fn) meta precond postcond); eauto.
    rewrite SBRed.tau MIRed.tau.
    (* hexploit (VP1 fn); rewrite FIND /=; revert E; intros ->; ss; intros Himp. *)
    (* hexploit (Himp (length tgts) x); intros [x' [PRE ?]]. *)
    eapply thread_rel_spawn; eauto.
    { destruct rs_diff; ss. }
    { rewrite EQLEN2. ii; subst; ss. }
    { rewrite EQLEN2 EQLEN. iIntros "X //". iPoseProof (Hr_t4 with "X") as "X"; done. }
    { ss; eapply elim_rel_cancel; eauto. }
  }
  rewrite insert_app_l; last lia.
  rewrite Hr_t Hr_t1 Hr_t3 Hr_t5 list_insert_id // big_sepL_app /= right_id last_length.
  iIntros ">(($ & $) & >[$ $])"; done.
(*SLOW*)Qed.
