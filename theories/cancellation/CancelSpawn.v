Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics CancelTactics.
Require Import MInline MInlineIntro MInlineElim ElimRel.

Local Ltac sil := iter_l; rewrite ?lookup_app_l ?length_insert // !list_lookup_insert ?length_insert //.
Local Ltac snl := norm_l; rewrite -?insert_app_l //= !list_insert_insert ?bind_ret_l.
Local Ltac sir :=
  match goal with
  | [ EQLEN : length _ = length _ |- _ ] => iter_r; rewrite ?lookup_app_l -?EQLEN //= ?length_insert -?EQLEN //= !list_lookup_insert ?length_insert //= ?last_length //= -?EQLEN //=; [..|try nia]
  end.
Local Ltac snr :=
    match goal with
    | [ EQLEN : length _ = length _ |- _ ] => norm_r; rewrite -?insert_app_l -?EQLEN //= !list_insert_insert ?bind_ret_l; [..|try nia]
    end.

Lemma cancel_spawn `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG} md sp 
  (X: Type) (PQ: X → (Any.t → iProp Σ) * (Any.t → iProp Σ)) N mm
  fn args :
  CANCEL_GOAL md sp PQ N mm
    (HoareSpawnE None false fn args N) 
    (HoareSpawnE (SMod.conc_sp_from md !! speckey_fn fn) true fn args N).
Proof.
  r; i. subst.
  (* rewrite /sp_from /to_sp in WFS. setoid_rewrite alist_find_map_snd in WFS. *)
  iter_l. iter_r. rewrite x0 x1 /=. step_l. norm_l.
  rewrite /LMod.prog /Mod.to_lmod /=.
  rewrite !lookup_fmap !lookup_omap !lookup_fmap.

  destruct (SMod.fnsems md !! Some fn) eqn:FIND; cycle 1.
  { s. step_l. i; ss. }
  destruct o; ss; cycle 1.
  { s. step_l. i; ss. }

  destruct p as [msk [fspo bd]]. ss.
  destruct fspo; ss; cycle 1.
  { s. exfalso. r in WFS. hexploit WFS; eauto; i; des. inv H1. }
  ired. norm_l. norm_r.
  assert (FIND0: SMod.conc_sp_from md !! (speckey_fn fn) = Some f).
  { rewrite /SMod.conc_sp_from. rewrite lookup_insert_ne //.
    rewrite /SMod.sp_from. rewrite lookup_kmap_Some. exists (Some fn).
    esplits; eauto. rewrite lookup_omap !lookup_fmap lookup_omap FIND //. }
  rewrite FIND0. ired.

  step_r. i. step_r. norm_r.
  guardH EQLEN2.

  sil. step_l. snl.
  sir. step_r. snr.
  sir. step_r. i. step_r. snr.
  sir. step_r. snr.
  sir. step_r. snr.
  rewrite !lookup_fmap !lookup_omap !lookup_fmap FIND /=. norm_r.
  sir. step_r. snr.
  sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l Any.upcast_downcast /= !bind_ret_l.

  rewrite YieldToken_gen in RS.
  hexploit (Own_bupd_split).
  { iIntros "S". iPoseProof (RS with "S") as ">(D & R & TA & [YA NY])".
    iModIntro. iCombine "D TA YA" as "P". iCombine "R NY" as "Q".
    iSplitL "P"; [iApply "P"|iApply "Q"]. }
  { eauto. }
  intros [r_t1 [r_t2 [Hr_t [Hr_t1 Hr_t2]]]].

  sir. step_r. exists r_t2. step_r. snr.
  sir. step_r.
  assert (RES: ✓ r_t2 ∧ (Own r_t2 ⊢ |==> YIELD (length srcs) ∗ Own r_t)).
  { split; eauto.
    { eapply Own_wand_valid; [iIntros "S"; iMod (Hr_t with "S") as "[_ $]"; done|eauto]. }
    { rewrite Hr_t2 EQLEN2. iIntros "[$ $]"; done. }
  }
  exists RES. step_r. snr.
  sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l.
  sir. step_r. snr.
  sir. step_r. snr.
  sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l Any.upcast_downcast /= !bind_ret_l.
  sir. step_r. i. step_r. snr.
  sir. step_r. i. step_r. snr.
  sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l.
  sir. step_r. snr.
  sir. step_r. snr.

  gstep; econs; econsr; try exact smj_lt_mid_top.
  gbase.

  unguardH EQLEN2.
  des; hexploit (Own_bupd_split); eauto.
  intros [r_t3 [r_t4 [Hr_t3 [Hr_t4 Hr_t5]]]].
  eapply CIH; eauto.
  { instantiate (1:=<[cid:=ε]>(rs_diff ++ [r_t3])).
    econs; first (rewrite !length_insert !length_app /=; lia).
    econs; first (rewrite !length_insert !length_app /=; lia).
    intros i ???; destruct (decide (i = cid)).
    { subst; rewrite ?list_lookup_insert; try (rewrite length_app /=; lia).
      do 3 (intros INV; inv INV).
      econs; eauto. eapply KTR.
    }
    rewrite !list_lookup_insert_ne //.
    destruct (decide (i < length srcs)).
    { rewrite !lookup_app_l; try lia. ii; eapply REL; eauto. }
    destruct (decide (i = length srcs)); cycle 1.
    { rewrite ?lookup_ge_None_2; ss; rewrite ?length_app /=; lia. }
    subst; rewrite list_lookup_length EQLEN list_lookup_length -EQLEN -EQLEN2 list_lookup_length.
    do 3 (intros INV; inv INV).

    destruct f; ss. r in WFS. hexploit WFS; eauto. i; des.
    exploit (Mod.well_scoped_fns (SMod.to_mod (SMod.conc_sp_from md) md) (Some fn)); eauto.
    { rewrite lookup_omap lookup_fmap FIND. ss. }
    i; ss.
    rewrite /ModTr.trans_fnsem !sandbox_inline_commute /SB.sandbox_body; cycle 1; try by eauto.
    rewrite /SModTr.trans_fnsem /SModTr.trans_fnsem.
    replace (SModTr.HoareFun) with (Seal.sealing "temp" (SModTr.HoareFun)); cycle 1.
    { unseal "temp". refl. }
    ss. unseal "temp".
    rewrite (@MIRed_HoareFun _ _ _ _ _ _ _ _ _ md (SMod.conc_sp_from md) msk bd (Some (fspec_mk meta precond postcond)) x3 (Some fn) meta precond postcond); cycle 1; eauto.
    rewrite SBRed.tau MIRed.tau.
    (* hexploit (VP1 fn); rewrite FIND /=; revert E; intros ->; ss; intros Himp. *)
    (* hexploit (Himp (length tgts) x); intros [x' [PRE ?]]. *)
    eapply thread_rel_spawn; eauto.
    { destruct rs_diff; ss. }
    { rewrite EQLEN2. ii; subst; ss. }
    { rewrite EQLEN2. iIntros "X //". iPoseProof (Hr_t4 with "X") as "X"; done. }
    { ss; eapply elim_rel_cancel; eauto. }
  }
  
  rewrite insert_app_l; last lia.
  rewrite Hr_t Hr_t1 Hr_t3 Hr_t5 list_insert_id // big_sepL_app /= right_id last_length.
  iIntros ">(($ & $) & >[$ $])"; done.
(*SLOW*)Qed.
