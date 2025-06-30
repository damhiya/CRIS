Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import SModTr HModTr ModTr SMod HMod Mod.
Require Import ITactics TacticsCommon SimGlobal SimGlobalFacts CtxRefine ClosedAdequacy.
Require Import HModInline HModInlineIntro HModInlineElim ElimRel.
Require Import SimGlobal SimGTactics.
Require Import CancelSpawn CancelCore CancelPG CancelAG CancelPre CancelPost.

Set Implicit Arguments.

Module Cancel. Section Cancel.

Context `{Σ: GRA}.

Lemma cancel_elim md sp (rs0 r_s r_t: Σ) srcs tgts cid st ps pt
  (WFS: smod_wf md)
  (VP: valid_sp md sp)
  (WF: HMod.wf (SMod.to_hmod sp_none (SMod.cancel md)))
  (REL: Forall2i (thread_rel sp) srcs tgts)
  (WFR: ✓ r_s)
  (RS: Own r_s ⊢ |==> Own r_t)
  :
  simg cancel_eq ps pt
    (ModTr.interp_stateE Any.t
       (iterV (ModTr.handle_callE (Mod.prog (HMod.to_mod (HModInline.inline
              (SMod.to_hmod sp_none (SMod.cancel md))) rs0))) (cid, srcs))
       (Any.pair (HModTr.alist_encode st) r_s ↑))
    (ModTr.interp_stateE Any.t
       (iterV (ModTr.handle_callE (Mod.prog (HMod.to_mod (HModInline.inline
              (SMod.to_hmod sp md)) rs0))) (cid, tgts))
       (Any.pair (HModTr.alist_encode st) r_t ↑)).
Proof.
  ginit. move WFS at top. move WF at top. move VP at top.
  revert_until rs0. gcofix CIH. i.
  destruct (classic (cid < length srcs)); cycle 1.
  { ziter_l. erewrite (proj2 (lookup_ge_None srcs cid)); try nia.
    s. zstep_l. zstep_l. }
  rename H into LEN. exploit Forall2i_nth; eauto. i. des. ss.
  rename x into src, y into tgt. depdes x2.
  destruct REL as [EQLEN REL].

  assert(KEY: ∀ itrS' itrT' st (r_s r_t: Σ) tid
                 (WFR: ✓ r_s)
                 (RS: Own r_s ⊢ |==> Own r_t)
                 (LEN: cid < List.length srcs)
                 (REL: elim_rel sp itrS' itrT'),
  gpaco7 _simg (cpn7 _simg) bot7 r (Any.t * Any.t)%type
    (Any.t * Any.t)%type cancel_eq smj_top smj_top
    (ModTr.interp_stateE Any.t
       (iterV (ModTr.handle_callE (Mod.prog (HMod.to_mod (HModInline.inline
              (SMod.to_hmod sp_none (SMod.cancel md))) rs0)))
              (tid, <[cid:=interpV HModTr.handle_hmodE itrS']> srcs))
       (Any.pair (HModTr.alist_encode st) r_s ↑))
    (ModTr.interp_stateE Any.t
       (iterV (ModTr.handle_callE (Mod.prog (HMod.to_mod (HModInline.inline
              (SMod.to_hmod sp md)) rs0)))
              (tid, <[cid:=x_ <- interpV HModTr.handle_hmodE itrT';; k x_]> tgts))
       (Any.pair (HModTr.alist_encode st) r_t ↑))).
  {
    i. zprogress.
    gbase. eapply CIH; et.
    econs. { rewrite !length_insert. et. }
    i. destruct (classic (cid = i)); cycle 1.
    { rewrite list_lookup_insert_ne in EQx; et.
      rewrite list_lookup_insert_ne in EQy; et. }
    subst. rewrite !list_lookup_insert in EQx, EQy; et; cycle 1.
    { rewrite -EQLEN. et. }
    inv EQx. econs; et.
  }

  punfold REL0. depdes REL0; ii; subst; pclearbot.
  - ziter_r. rewrite x1. s. zstep_r.
  - ziter_l. rewrite x0. s. zstep_l.
  - ziter_l. rewrite x0. s. zstep_l. ziter_l. zstep_l.
  - ziter_l. ziter_r. rewrite x0 x1. s. destruct cid; s; cycle 1.
    { zstep_l. zstep_l. }
    specialize (RET eq_refl). subst. s. zstep_l. zstep_r.
    gstep. econs. econs.
    r. esplits; et; hss.
  - ziter_l. ziter_r. rewrite x0 x1. s. zstep_l. zstep_r. eapply KEY; et.
  - eapply cancel_core; et.
  - eapply cancel_pg; et.
  - eapply cancel_ag; et.
  - ziter_l. ziter_r. rewrite x0 x1. s. zstep_l. zstep_r. eapply KEY, KTR; et.
  - eapply cancel_spawn; et.
  - eapply cancel_pre; et.
  - eapply cancel_post; et.
Unshelve. all: try exact smj_top.
(*SLOW*)Qed.

Lemma cancel_main md sp rs
  (WFS: smod_wf md)
  (VP: valid_sp md sp)
  (WF: HMod.wf (SMod.to_hmod sp_none (SMod.cancel md)))
  (VALID: ✓ rs)
  :  
  refines_mod
    (HMod.to_mod (HModInline.inline (SMod.to_hmod sp_none (SMod.cancel md))) rs)
    (HMod.to_mod (HModInline.inline (SMod.to_hmod sp md)) rs).
Proof.
  r. intro arg. eapply adequacy_global.
  instantiate (1:= smj_top). instantiate (1:= smj_top).
  unfold Mod.compile. s. rewrite /ITree.map /ModTr.trans /ModTr.interp_callE.  

  rewrite !alist_find_map_snd.
  destruct (alist_find None (SMod.fnsems md)) eqn: FIND; rewrite FIND; cycle 1.
  { s. ired. ginit. gstep. econs. econs. ss. }
  s. ired. rewrite /HModTr.trans_ktree.
  destruct f as [[[img msk] scp] [fspo bd]]. s.
  assert (SCP: incl scp (SMod.scopes md)).
  { ii. eapply SMod.well_scoped_fns. rewrite /fnsems_scopes. erewrite FIND. et. }
  erewrite sandbox_inline_commute; et.
  erewrite sandbox_inline_commute; et.
  rewrite /SB.sandbox_body. s.

  ginit. guclo bindC_spec. econs; cycle 1.
  { instantiate (1:=cancel_eq). i. gstep. econs. econs.
    destruct SIM. des. et. }
  gfinal. right.

  eapply cancel_elim; et. econs; et.
  i. destruct i; ss. inv EQx.
  exploit WFS; et. i. subst.
  rewrite !if_prod_comm !if_simpl.
  econs; et; cycle 1.
  { rewrite bind_ret_r. et. }

  s. eapply elim_rel_cancel; try r; et.
Unshelve. all: exact smj_top.
(*SLOW*)Qed.

(*** Final Theorem ***)
Theorem cancellation md sp P
  (WFS: smod_wf md)
  (VP: valid_sp md sp)
  (WF: HMod.wf (SMod.to_hmod sp_none (SMod.cancel md)))
  :
  refines (SMod.to_hmod sp_none (SMod.cancel md), P)
          (SMod.to_hmod sp md, P).
Proof. 
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
