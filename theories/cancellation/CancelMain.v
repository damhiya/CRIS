Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics.
Require Import MInline MInlineIntro MInlineElim.
Require Import ElimRel.

Set Implicit Arguments.

Module MainSMod. Section MainSMod.

  Context `{!crisG Γ Σ α β τ _S _I, !concG}.

  Definition trans_ktree (fno: option string) sp (sb : fnsem_type (option fspec * fbody)) : fnsem_type fbody :=
    map_snd (λ '(fsp,bd), SModTr.trans_body (is_some sb.2.1, if sb.1.1.1 then sp else sp_none, if is_some fno then fsp else None) bd) sb.

  Definition map_fnsems sp (fnsems: fnsems_type) :=
    List.map (λ '(fno, fnsem), (fno, trans_ktree fno sp fnsem)) fnsems.

  Lemma alist_find_map_fnsems fn sp fnsems :
    alist_find fn (map_fnsems sp fnsems) = o_map (alist_find fn fnsems) (λ fnsem, trans_ktree fn sp fnsem).
  Proof.
    rewrite /map_fnsems.
    destruct (alist_find fn fnsems) eqn:E; ss; des_ifs; induction fnsems; ss; des_ifs; try (destruct o; ss); try (rewrite IHfnsems; ss); rewrite eq_rel_dec_correct in Heq0; des_ifs.
  Qed.

  Program Definition to_mod (sp : sp_type) (ms : SMod.t) : Mod.t := {|
    Mod.scopes := ms.(SMod.scopes);
    Mod.fnsems := map_fnsems sp ms.(SMod.fnsems);
    Mod.initial_st := ms.(SMod.initial_st);
    |}.
  Next Obligation.
    i. destruct ms. ss. ii. unfold fnsems_scopes in *.
    rewrite alist_find_map_fnsems in H0.
    specialize (well_scoped_fns fn a).
    destruct (alist_find fn fnsems) eqn: E; ss.
    destruct f. et.
  Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.

End MainSMod. End MainSMod.

Module CancelMain. Section CancelMain.

Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG}.

Lemma main_smod_find_some_eq md fn :
  alist_find (Some fn) (MainSMod.map_fnsems (sp_from md) (SMod.fnsems md)) =
    alist_find (Some fn) (map (map_snd (SModTr.trans_ktree (sp_from md))) (SMod.fnsems md)).
Proof.
  rewrite alist_find_map_snd MainSMod.alist_find_map_fnsems.
  destruct (alist_find (Some fn) (SMod.fnsems md)); ss.
Qed.

Lemma main_smod_sandboxed_prog_eq md :
  sandboxed_prog (MainSMod.to_mod (sp_from md) md) = sandboxed_prog (SMod.to_mod (sp_from md) md).
Proof.
  eapply func_ext. i.
  rewrite /sandboxed_prog.
  eapply func_ext. i.
  rewrite main_smod_find_some_eq /SMod.to_mod /=. refl.
Qed.

Lemma main_smod_lmod_prog_eq md rs :
  LMod.prog (Mod.to_lmod (MInline.inline (MainSMod.to_mod (sp_from md) md)) rs) =
    LMod.prog (Mod.to_lmod (MInline.inline (SMod.to_mod (sp_from md) md)) rs).
Proof.
  eapply func_ext. i.
  rewrite /LMod.prog /Mod.to_lmod /=.
  rewrite !alist_find_map_snd MainSMod.alist_find_map_fnsems.
  destruct (alist_find (Some x) (SMod.fnsems md)); ss.
  rewrite /inline_fsem main_smod_sandboxed_prog_eq.
  rewrite /MainSMod.trans_ktree; ss.
Qed.


Inductive cancel_main_inv md (cid: nat) (src tgt : list (itree lmodE Any.t)) :=
| cancel_main_intro itr msk scp
    (CID: cid < length src)
    (LEN: length src = length tgt)
    (SRC0: src !! 0 = Some itr)
    (TGT0: tgt !! 0 =
             Some
               (st <- itr;;
                ModTr.trans
                  (inline_body (sandboxed_prog (SMod.to_mod (sp_from md) md))
                     (interpV (SB.handle_sandbox true msk scp) (ret <- trigger (Choose Any.t);; trigger (Guarantee ⌜st = ret⌝);;; Ret ret)))))
    (OTH: ∀ cid, cid <> 0 → src !! cid = tgt !! cid)
  : cancel_main_inv md cid src tgt.

Lemma cancel_main_aux md rs src tgt cid ps pt (INV: cancel_main_inv md cid src tgt)
  (VALID: ✓ rs) :
  gsim cancel_eq ps pt
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline (SMod.to_mod (sp_from md) md)) rs))) (cid, src))
       (Any.pair (ModTr.alist_encode (SMod.initial_st md)) rs ↑))
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline (SMod.to_mod (sp_from md) md)) rs))) (cid, tgt))
       (Any.pair (ModTr.alist_encode (SMod.initial_st md)) rs ↑)).
Proof.
  ginit. revert INV ps pt. revert cid src tgt. gcofix CIH; i.
  destruct (decide (cid < length src)); cycle 1.
  { dup n. inv INV. eapply not_lt in n. eapply lookup_ge_None in n.
    ziter_l; rewrite n; zstep_l. }
  destruct (decide (cid = 0)).
  { subst. inv INV.
    ides itr.
    - ziter_r; rewrite TGT0 /=; zstep_r.
      ziter_l; rewrite SRC0 /=; zstep_l.
      zstep_r. ziter_r. zstep_r.
      ziter_r. zstep_r. ired. ziter_r. zstep_r. zstep_r.
      ziter_r. zstep_r. zstep_r. ziter_r. zstep_r.
      ziter_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r.
      zstep. des.
      assert (I: Own rs ⊢ ⌜r0 = x⌝).
      { rewrite x2. iIntros ">[$ _]". }
      eapply Own_pure_soundness in I; eauto; subst.
      econs; esplits; eauto; rewrite Any.pair_split; ss.
    - ziter_l; rewrite SRC0 /=; zstep_l.
      ziter_r; rewrite TGT0 /=; zstep_r.
      gstep. econs. econs; try exact smj_lt_mid_top.
      gbase. eapply CIH. econs; eauto.
      { rewrite length_insert //. }
      { rewrite !length_insert //. }
      { rewrite list_lookup_insert //. }
      { rewrite list_lookup_insert // -LEN //. }
      { i. rewrite !list_lookup_insert_ne //. eapply OTH; eauto. }
    - admit.
  }
  eapply lookup_lt_is_Some in l. rewrite /is_Some in l. des.
  inv INV. specialize (OTH cid). hexploit OTH; eauto; i.
  ides x.
  - ziter_l; rewrite l /=; zstep_l.
    ziter_r; rewrite -H l /=; zstep_r. des_ifs. zstep_l.
  - ziter_l; rewrite l /=; zstep_l.
    ziter_r; rewrite -H l /=; zstep_r.
Admitted.
      
Lemma cancel_main md rs
  (WFS: SMod.wf md)
  (WF: Mod.wf (SMod.to_mod sp_none (SMod.cancel md)))
  (VALID: ✓ rs)
  :  
  refines_lmod
    (Mod.to_lmod (MInline.inline (MainSMod.to_mod (sp_from md) md)) rs)
    (Mod.to_lmod (MInline.inline (SMod.to_mod (sp_from md) md)) rs).
Proof using.
  r. intro arg. eapply gsim_adequacy.
  instantiate (1:= smj_top). instantiate (1:= smj_top).
  unfold LMod.compile. s. rewrite /ITree.map /LModTr.trans /LModTr.interp_callE.

  rewrite !alist_find_map_snd.
  rewrite !MainSMod.alist_find_map_fnsems.
  destruct (alist_find None (SMod.fnsems md)) eqn: FIND; cycle 1.
  { s. ired. ginit. gstep. econs. econs. ss. }
  s. ired. rewrite /ModTr.trans_ktree.
  destruct f as [[[img msk] scp] [fspo bd]]. s.
  assert (SCP: incl scp (SMod.scopes md)).
  { ii. eapply SMod.well_scoped_fns. rewrite /fnsems_scopes. erewrite FIND. et. }
  erewrite !sandbox_inline_commute; et.
  rewrite /SB.sandbox_body. s.

  ginit. guclo bindC_spec. econs; cycle 1.
  { instantiate (1:=cancel_eq). i. gstep. econs. econs.
    destruct SIM. des. et. }

  r in WFS. hexploit WFS; eauto; i; des; ss.
  hexploit H1; eauto; i; subst; ss.
  
  ziter_l. zstep_l. ziter_l. zstep_l.
  exploit WFS; et. i; des; subst; ss.

  rewrite main_smod_sandboxed_prog_eq.
  rewrite main_smod_lmod_prog_eq.
  
  ziter_r. zstep_r. exists tt. zstep_r.
  ziter_r. zstep_r. ziter_r. zstep_r. exists arg. zstep_r.
  ziter_r. zstep_r. ziter_r. zstep_r. ired.
  ziter_r. zstep_r. exists rs. zstep_r.
  ziter_r. zstep_r. unshelve eexists.
  { split; eauto. }
  zstep_r. ziter_r. zstep_r.
  ziter_r. zstep_r. ziter_r. zstep_r.

  set (temp:=interpV _ _) at 2.
  set (itr:=_:itree crisE Any.t) in temp at 2.
  replace temp with (SB.sandbox true msk scp itr); cycle 1.
  { subst itr temp; refl. }
  subst temp itr. rewrite SBRed.bind MIRed.bind Red.bind /SB.sandbox.

  remember (ModTr.trans (inline_body (sandboxed_prog (SMod.to_mod (sp_from md) md)) (interpV (SB.handle_sandbox true msk scp) (SModTr.trans true (sp_from md) (bd arg))))) as itr.

  gfinal. right.
  eapply cancel_main_aux; eauto.
  econs; eauto.
  i. assert (LE: cid >= 1) by nia. dup LE.
  replace 1 with (length [itr]) in LE by ss.
  eapply lookup_ge_None in LE.

Admitted.
