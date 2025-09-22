Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics.
Require Import MInline MInlineIntro MInlineElim ElimRel.
Require Import CancelCore CancelPG CancelAG CancelSpawn CancelPre CancelPost.

Set Implicit Arguments.

Module Cancel. Section Cancel.

Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG}.

Lemma cancel_elim md (r_i r_s r_t: Σ) rs_diff srcs tgts cid st ps pt
  (WFS: SMod.wf md)
  (WF: Mod.wf (SMod.to_mod sp_none (SMod.cancel md)))
  (REL: Forall3i (thread_rel (sp_from md)) rs_diff srcs tgts)
  (WFR: ✓ r_s)
  (RS: Own r_s ⊢ |==> ([∗ list] i ∈ rs_diff, Own i) ∗ Own r_t ∗
         (* TID *) TidTokenAuth cid ∗ TidToken cid ∗
         (* YIELD *) YieldTokenAuth (length rs_diff) ∗ YieldToken cid ∗
         (* WINV *) winv (⊤, ⊤))
  :
  gsim cancel_eq ps pt
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
              (SMod.to_mod sp_none (SMod.cancel md))) r_i))) (cid, srcs))
       (Any.pair (ModTr.alist_encode st) r_s ↑))
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
              (SMod.to_mod (sp_from md) md)) r_i))) (cid, tgts))
       (Any.pair (ModTr.alist_encode st) r_t ↑)).
Proof using.
  ginit. move WFS at top. move WF at top.
  revert_until r_i. gcofix CIH. i.
  destruct (decide (cid < length srcs)) as [Hcid|]; cycle 1.
  { ziter_l. erewrite (proj2 (lookup_ge_None srcs cid)); try nia.
    s. zstep_l. zstep_l.
  }
  inversion REL as [Hlenxy [Hlenyz Hrel]].
  exploit (@Forall3i_nth _ _ _ cid); eauto; try lia; clear REL.
  intros [r_diff [i_s [i_t [Hdiff [Hs [Ht Hcidrel]]]]]]; ss.

  inversion_clear Hcidrel; subst; cycle 1.
  {
    (* ziter_l; rewrite Hs /=. zstep_l. ziter_l. zstep_l. *)
    (* ziter_r; rewrite Ht /= /elim_spawnee_precond. *)
    (* zstep_r. exists cid. ired. zstep_r. *)
    (* ziter_r. zstep_r. *)
    (* ziter_r. zstep_r. ired. *)
    (* ziter_r. zstep_r. *)
    (* hexploit (Own_bupd_split). *)
    (* { iIntros "S"; iPoseProof (RS with "S") as ">(D & R & TA & T & YA & Y & W)". *)
    (*   iCombine "D TA YA" as "P". iCombine "T Y W" as "TKN". iCombine "TKN R" as "Q". *)
    (*   iModIntro. iSplitL "P"; [iApply "P"|iApply "Q"]. } *)
    (* { eauto. } *)
    (* intros [r_s1 [r_s2 [Hr_s [Hr_s1 Hr_s2]]]]. *)
    (* exists r_s2; ired. zstep_r. *)
    (* ziter_r. zstep_r. *)
    (* unshelve eexists. *)
    (* { split; [eapply Own_wand_valid; [iIntros "S"; iMod (Hr_s with "S") as "[_ $]"; done|done]|]. *)
    (*   rewrite Hr_s2. eapply bupd_intro. *)
    (* } *)
    (* ired. zstep_r. *)
    (* ziter_r. zstep_r. *)
    (* ziter_r. zstep_r. *)
    (* ziter_r. zstep_r. *)
    (* ziter_r. zstep_r. exists x; ired. zstep_r. *)
    (* ziter_r. zstep_r. *)
    (* ziter_r. zstep_r. exists varg. ired. zstep_r. *)
    (* ziter_r. zstep_r. *)
    (* ziter_r. zstep_r. ired. *)
    (* ziter_r. zstep_r. exists r_diff. ired. zstep_r. *)


    
    (* exists r_diff; ired. zstep_r. *)
    (* exists x; ired. zstep_r. *)
    (* ziter_r. zstep_r. *)
    (* ziter_r. zstep_r. exists varg. ired. zstep_r. *)
    (* ziter_r. zstep_r. *)
    (* ziter_r. zstep_r. *)
    (* ziter_r. zstep_r. *)
    (* hexploit (Own_bupd_split); first apply RS; eauto. *)
    (* intros [r_s1 [r_s2 [Hr_s [Hr_s1 Hr_s2]]]]; exists (r_t ⋅ r_diff). ired. zstep_r. *)
    (* ziter_r. zstep_r. eexists. zstep_r. *)
    (* ziter_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r. *)
    (* eapply Hkey; eauto; cycle 1. *)
    (* { econs; cycle 3. *)
    (*   { rewrite interpV_bind; refl. } *)
    (*   { by ii. } *)
    (*   { eauto. } *)
    (*   { rewrite /ModTr.trans //. } *)
    (* } *)
    (* { rewrite Hr_s Hr_s1 Hr_s2 Own_op. *)
    (*   iIntros "> [RS $]"; iPoseProof (big_sepL_insert_acc with "RS") as "[$ RS]"; eauto. *)
    (*   iModIntro; iApply "RS"; iApply Own_unit. *)
    (* } *)
    (* Unshelve. *)
    (* { split; *)
    (*     [eapply Own_wand_valid; *)
    (*      [iIntros "S"; rewrite Own_op; iMod (RS with "S") as "[S $]"|] *)
    (*     | rewrite Own_op; iIntros "[$ D]"; rewrite H2]; try done. *)
    (*   iPoseProof (big_sepL_lookup_acc with "S") as "[$ S]"; eauto. *)
    (* } *)
    (* { zstep_r. ziter_r. zstep_r. *)
    (*   eapply Hkey; eauto; cycle 1. *)
    (*   { econs; eauto. *)
    (*     rewrite bind_ret_r /ModTr.trans. *)
    (*     hexploit (Own_bupd_split r_diff (⌜ arg = varg ⌝)). *)
    (*     { rewrite H2; iIntros "> $"; iModIntro; iApply Own_unit. } *)
    (*     { eapply Own_wand_valid; [iIntros "S"; iMod (RS with "S") as "[S _]"|]; eauto. *)
    (*       iPoseProof (big_sepL_lookup_acc with "S") as "[$ ?]"; eauto. *)
    (*     } *)
    (*     intros [? [? [? [Harg%Own_pure_soundness ?]]]]; subst; ss. *)
    (*     eapply Own_wand_valid; [iIntros "S"; iMod (RS with "S") as "[S _]"|]; eauto. *)
    (*     iPoseProof (big_sepL_lookup_acc with "S") as "[S ?]"; eauto. *)
    (*     iMod (H0 with "S") as "[$ ?]"; done. *)
    (*   } *)
    (*   { rewrite RS. *)
    (*     iIntros "> [S $]"; iPoseProof (big_sepL_insert_acc with "S") as "[_ S]"; eauto. *)
    (*     iModIntro; iApply "S"; iApply Own_unit. *)
    (*   } *)
    (* } *)
    admit.
  }

  
  assert (Hkey :
    ∀ itr_s itr_t st (r_s r_t: Σ) r_diff tid,
    ✓ r_s →
    (Own r_s ⊢ |==> ([∗ list] i ∈ <[cid := r_diff]> rs_diff, Own i) ∗ Own r_t ∗
       (* TID *) TidTokenAuth tid ∗ TidToken tid ∗
       (* YIELD *) YieldTokenAuth (length (<[cid := r_diff]> rs_diff)) ∗ YieldToken tid ∗
       (* WINV *) winv (⊤, ⊤)) →
    cid < List.length srcs →
    thread_rel (sp_from md) cid r_diff itr_s itr_t →
    gpaco7 _gsim (cpn7 _gsim) bot7 r (Any.t * Any.t)%type
      (Any.t * Any.t)%type cancel_eq smj_top smj_top
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
          (SMod.to_mod sp_none (SMod.cancel md))) r_i)))
              (tid, <[cid:=itr_s]> srcs))
       (Any.pair (ModTr.alist_encode st) r_s ↑))
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
              (SMod.to_mod (sp_from md) md)) r_i)))
              (tid, <[cid:=itr_t]> tgts))
       (Any.pair (ModTr.alist_encode st) r_t ↑))).
  { i. zprogress.
    gbase. eapply CIH; et.
    split.
    { rewrite !length_insert. et. }
    split.
    { rewrite !length_insert. et. }
    i. destruct (classic (cid = i)); cycle 1.
    { rewrite list_lookup_insert_ne in H3; et.
      rewrite list_lookup_insert_ne in H4; et.
      rewrite list_lookup_insert_ne in H5; et.
    }
    subst. rewrite !list_lookup_insert in H3, H4, H5; et; cycle 1.
    { rewrite -Hlenyz. et. }
    { rewrite Hlenxy. et. }
    inv H3. done.
  }
  
  punfold REL; depdes REL; ii; subst; pclearbot.
  - ziter_l; rewrite Hs /=; zstep_l.
  - ziter_l; rewrite Hs /=; zstep_l; ziter_l; zstep_l.
  - ziter_r; rewrite Ht /=; zstep_r.
  - ziter_l; rewrite Hs /=.
    ziter_r; rewrite Ht /=. destruct cid; s; cycle 1.
    { zstep_l. zstep_l. }
    specialize (RET eq_refl). subst. s. zstep_l. zstep_r.
    gstep. econs. econs.
    r. esplits; et; hss.
  - ziter_l. ziter_r. rewrite Hs Ht /=. zstep_l. zstep_r. eapply Hkey; et.
    { rewrite list_insert_id //. }
    { econs; eauto. }
  - eapply cancel_core; eauto.
  - eapply cancel_pg; eauto.
  - eapply cancel_ag; eauto.
  - admit.
    (* ziter_l. ziter_r. rewrite Hs Ht /=. zstep_l. zstep_r. eapply Hkey; eauto. *)
    (* { rewrite list_insert_id //. } *)
    (* { econs; eauto; eapply H. } *)
  - eapply cancel_spawn; et.
  - eapply cancel_pre; et.
  - eapply cancel_post; et.
  - admit.
  - admit.
  - admit.
    (* ziter_r. rewrite Ht /=; zstep_r. *)
    (* exists tt. zstep_r. ziter_r. zstep_r. *)
    (* ziter_r. zstep_r. exists varg. zstep_r. *)
    (* ziter_r. zstep_r. ziter_r. zstep_r. ired. *)
    (* ziter_r. zstep_r. exists r_t. zstep_r. *)
    (* ziter_r. zstep_r. unshelve eexists. *)
    (* { split; eauto. admit. } *)
    (* ired. ziter_r. zstep_r. zstep_r. *)
    (* ziter_r. zstep_r. ziter_r. zstep_r. *)
    (* eapply Hkey; et. *)
Admitted.
(* (*SLOW*) Qed. *)

Lemma cancel_main md rs rt
  (WFS: SMod.wf md)
  (WF: Mod.wf (SMod.to_mod sp_none (SMod.cancel md)))
  (VALID: ✓ rs)
  (RES: Own rs ⊢ |==> Own rt ∗ TidTokenAuth 0 ∗ TidToken 0 ∗ YieldTokenAuth 0)
  :  
  refines_lmod
    (Mod.to_lmod (MInline.inline (SMod.to_mod sp_none (SMod.cancel md))) rs)
    (Mod.to_lmod (MInline.inline (SMod.to_mod (sp_from md) md)) rt).
Proof using.
  r. intro arg. eapply gsim_adequacy.
  instantiate (1:= smj_top). instantiate (1:= smj_top).
  unfold LMod.compile. s. rewrite /ITree.map /LModTr.trans /LModTr.interp_callE.  

  rewrite !alist_find_map_snd.
  destruct (alist_find None (SMod.fnsems md)) eqn: FIND; rewrite FIND; cycle 1.
  { s. ired. ginit. gstep. econs. econs. ss. }
  s. ired. rewrite /ModTr.trans_ktree.
  destruct f as [[[img msk] scp] [fspo bd]]. s.
  assert (SCP: incl scp (SMod.scopes md)).
  { ii. eapply SMod.well_scoped_fns. rewrite /fnsems_scopes. erewrite FIND. et. }
  erewrite !sandbox_inline_commute; et.
  (* erewrite sandbox_inline_commute; et. *)
  rewrite /SB.sandbox_body. s.
 
  ginit. guclo bindC_spec. econs; cycle 1.
  { instantiate (1:=λ vrs vrt, cancel_eq vrs vrt). i. gstep. econs. econs.
    destruct SIM. des. et. }
  ziter_l. zstep_l. ziter_l. zstep_l.
  exploit WFS; et. i; des; subst; ss.

  gfinal. right.
  replace (SModTr.HoareFun) with (Seal.sealing "temp" SModTr.HoareFun); cycle 1.
  { unseal "temp". ss. }
  hexploit x2; eauto; i; subst; ss.

  eapply (cancel_elim rs rt (rs_diff:=[ε])); eauto.
  { econs; et.
    split; ss.
    i. destruct i; ss. inv H0. 
    (* exploit WFS; et. i. subst. *)
    set (itrS:=_:itree lmodE Any.t).
    set (itrT:=_:itree lmodE Any.t) at 2.
    replace itrS with
      (ModTr.trans
         (inline_body (sandboxed_prog (SMod.to_mod sp_none (SMod.cancel md)))
            (SB.sandbox true msk scp(SModTr.trans false sp_none (ret <- bd arg;; tau;; tau;; Ret ret))))); cycle 1.
    { subst itrS. rewrite SRed.bind SBRed.bind MIRed.bind Red.bind.
      rewrite {1}/SB.sandbox. f_equal.
      extensionalities. rewrite SRed.tau SRed.ret SBRed.tau SBRed.ret MIRed.tau MIRed.ret.
      rewrite !Red.tau Red.ret.
      { repeat f_equal.
    econs; et; cycle 1.
    { set (INLINE := inline_body _).
      set (ktr := λ ret, tau;; Ret ret).
      rewrite bind_ret_r.
      replace ktr with ModTr.trans (λ ret, INLINE (tau;; Ret ret))).
      rewrite bind_ret_r. et. }

    rewrite /SB.sandbox. rewrite {1}/SModTr.trans.

    eapply elim_rel_cancel; et.
  }
  ss; rewrite right_id -Own_op left_id; iIntros "$"; done.
Unshelve. all: exact smj_top.
(*SLOW*)Qed.

End Cancel.

Section Cancel.
Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

(*** Final Theorem ***)
Theorem cancellation md sp P
  (WFS: SMod.wf md)
  (VP: valid_sp md sp)
  (WF: Mod.wf (SMod.to_mod sp_none (SMod.cancel md)))
  :
  refines (SMod.to_mod sp_none (SMod.cancel md), P)
          (SMod.to_mod sp md, P).
Proof using. 
  etrans.
  { eapply inline_elim. }
  etrans; cycle 1.
  { eapply inline_intro. }
  ii; split.
  {
    inv WFM. econs; eauto. s.
    repeat rewrite List.map_map fst_map_snd.
    repeat rewrite List.map_map fst_map_snd in wf_fns. eauto.
  }
  inv WFM. s; i. exists rs. esplits; et.
  eapply cancel_main; eauto.
(*SLOW*)Qed.

End Cancel. End Cancel.
