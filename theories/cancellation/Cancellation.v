Require Import Common.
From iris.proofmode Require Import proofmode.

Require Import SModTr HModTr ModTr SMod HMod Mod.
Require Import ITactics TacticsCommon SimGlobal SimGlobalFacts CtxRefine ClosedAdequacy.
Require Import CancelLib HModInline HModInlineIntro HInlineElim ElimRel.
Require Import SimGlobal SimGTactics.

Set Implicit Arguments.

(* Require Import SModCancel. *)
(* Require Import CancelLib InlineIntro InlineElim. *)
(* Require Import CancelRet CancelCore CancelPG. *)
(* Require Import CancelAssume CancelAssume CancelAssumePrecise CancelGuarantee. *)
(* Require Import CancelHead CancelTail CancelSpawn CancelYield. *)

(* Section CancelDef. *)
(*   Context `{Σ: GRA}. *)

(*   Definition CANCEL_GOAL md *)
(*     (R: ∀ x0 x1, (x0→x1→Prop)→smj→smj→itree coreE x0→itree coreE x1→Prop) *)
(*     (rs0 rt0: Σ) ps pt srcs tgts cid st (rs rt: Σ) : Prop := *)
(*     R Any.t Any.t eq ps pt *)
(*     (x <- *)
(*      ModTr.interp_stateE Any.t *)
(*        (iterV *)
(*           (ModTr.handle_callE *)
(*              (Mod.prog *)
(*                 (HMod.to_mod *)
(*                    (HModInline.inline *)
(*                       (SModCancel.to_hmod md)) rs0))) *)
(*           (cid, srcs)) (Any.pair st rs ↑);; Ret x.2) *)
(*     (x <- *)
(*      ModTr.interp_stateE Any.t *)
(*        (iterV *)
(*           (ModTr.handle_callE *)
(*              (Mod.prog *)
(*                 (HMod.to_mod *)
(*                    (HModInline.inline *)
(*                       (SMod.to_hmod (sp_from md) *)
(*                          md)) rt0))) *)
(*           (cid, tgts)) (Any.pair st rt ↑);; Ret x.2). *)

(*   Definition cancel_term md X (meta: X) Q (itrT: itree hmodE Any.t) := *)
(*     (vret <- itrT;; *)
(*      inline_hp (prog *)
(*           (SMod.to_hmod *)
(*              (sp_from md) md)) *)
(*        (ret <- trigger (Choose Any.t);; *)
(*         trigger (Guarantee (Q meta vret ret));;; Ret ret)) *)
(*   . *)

(* End CancelDef. *)

Module Cancel. Section Cancel.

Context `{Σ: GRA}.

Variant thread_rel md tid src tgt : Prop :=
| thread_rel_body itrS itrT (k: Any.t → itree modE Any.t)
    (RET: tid = 0 -> k = λ x, Ret x)
    (REL: @elim_rel Σ (sp_from md) Any.t itrS itrT)
    (SRC: src = HModTr.trans itrS)
    (TGT: tgt = HModTr.trans itrT >>= k)
.

Lemma cancel_elim md (rs rs0: Σ) srcs tgts cid st ps pt
  (WFS: sp_wf md)
  (WF: HMod.wf (SMod.to_hmod sp_none (SMod.cancel md)))
  (REL: Forall2i (thread_rel md) srcs tgts)
  (* (WFR: ✓ rs) *)
  (* (LEN: cid < List.length srcs) *)
  :
  simg eq ps pt
    (ModTr.interp_stateE Any.t
       (iterV
          (ModTr.handle_callE
             (Mod.prog
                (HMod.to_mod
                   (HModInline.inline (SMod.to_hmod sp_none (SMod.cancel md)))
                   rs)))
          (cid, srcs))
       (Any.pair (HModTr.alist_encode st) rs0 ↑))
    (ModTr.interp_stateE Any.t
       (iterV
          (ModTr.handle_callE
             (Mod.prog
                (HMod.to_mod (HModInline.inline (SMod.to_hmod (sp_from md) md))
                   rs)))
          (cid, tgts))
       (Any.pair (HModTr.alist_encode st) rs0 ↑)).
Proof.
  ginit. move WFS at top. move WF at top.
  revert_until WFS. gcofix CIH. i.
  destruct (classic (cid < length srcs)); cycle 1.
  { ziter_l. erewrite (proj2 (lookup_ge_None srcs cid)); try nia.
    s. zstep_l. zstep_l. }
  rename H into LEN. exploit Forall2i_nth; eauto. i. des. ss.
  rename x into src, y into tgt. depdes x2.
  destruct REL as [EQLEN REL].

  assert(KEY: ∀ itrS' itrT' st (rs0: Σ) tid
                (REL: elim_rel (sp_from md) itrS' itrT'),
  gpaco7 _simg (cpn7 _simg) bot7 r (Any.t * Any.t)%type
    (Any.t * Any.t)%type eq smj_top smj_top
    (ModTr.interp_stateE Any.t
       (iterV
          (ModTr.handle_callE
             (Mod.prog
                (HMod.to_mod
                   (HModInline.inline (SMod.to_hmod sp_none (SMod.cancel md)))
                   rs)))
          (tid, <[cid:=interpV HModTr.handle_hmodE itrS']> srcs))
       (Any.pair (HModTr.alist_encode st) rs0 ↑))
    (ModTr.interp_stateE Any.t
       (iterV
          (ModTr.handle_callE
             (Mod.prog
                (HMod.to_mod (HModInline.inline (SMod.to_hmod (sp_from md) md))
                   rs)))
          (tid, <[cid:=x_ <- interpV HModTr.handle_hmodE itrT';; k x_]> tgts))
       (Any.pair (HModTr.alist_encode st) rs0 ↑))).
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
    gstep. econs. econs. et.
  - ziter_l. ziter_r. rewrite x0 x1. s. zstep_l. zstep_r. eapply KEY; et.
  - destruct e.
    + ziter_l. ziter_r. rewrite x0 x1. s. do 2 zstep_r. zstep_l. eexists. zstep_l.
      eapply KEY, KTR; et.
    + ziter_l. ziter_r. rewrite x0 x1. s. do 2 zstep_l. zstep_r. eexists. zstep_r.
      eapply KEY, KTR; et.
    + ziter_l. ziter_r. rewrite x0 x1. s. zstep. zstep_l. zstep_r. subst.
      eapply KEY, KTR; et.
  - destruct e.
    + ziter_l. ziter_r. rewrite x0 x1. s. zstep_l. zstep_r. ss.
      ziter_l. zstep_l. ziter_r. zstep_r. rewrite !HModTr.alist_encode_decode.
      eapply KEY, KTR; et.
    + ziter_l. ziter_r. rewrite x0 x1. s. zstep_l. zstep_r. ss. ired.
      eapply KEY, KTR; et.
  - destruct e.
    + ziter_l. ziter_r. rewrite x0 x1. s. zstep_l. zstep_r. ss. ired. hss. ired.
      ziter_l. do 2 zstep_l. ziter_r. zstep_r. eexists. zstep_r.
      ziter_l. do 2 zstep_l. ziter_r. zstep_r. eexists. zstep_r.
      ziter_l. zstep_l. ziter_r. zstep_r.
      ziter_l. zstep_l. ziter_r. zstep_r.
      eapply KEY, KTR; et.
    + ziter_l. ziter_r. rewrite x0 x1. s. zstep_l. zstep_r. ss. ired. hss. ired.
      ziter_r. do 2 zstep_r. ziter_l. zstep_l. eexists. zstep_l.
      ziter_r. do 2 zstep_r. ziter_l. zstep_l. eexists. zstep_l.
      ziter_r. do 2 zstep_r. ziter_l. zstep_l. eexists. zstep_l.
      ziter_l. do 2 zstep_l. ziter_r. zstep_r. eexists. zstep_r.
      ziter_l. zstep_l. ziter_r. zstep_r.
      ziter_l. zstep_l. ziter_r. zstep_r.
      eapply KEY, KTR; et.
    + ziter_l. ziter_r. rewrite x0 x1. s. zstep_l. zstep_r. ss. ired. hss. ired.
      ziter_r. do 2 zstep_r. ziter_l. zstep_l. eexists. zstep_l.
      ziter_r. do 2 zstep_r. ziter_l. zstep_l. eexists. zstep_l.
      ziter_l. zstep_l. ziter_r. zstep_r.
      ziter_l. zstep_l. ziter_r. zstep_r.
      eapply KEY, KTR; et.
  - ziter_l. ziter_r. rewrite x0 x1. s. zstep_l. zstep_r.
    eapply KEY, KTR; et.
  - ziter_l. ziter_r. rewrite x0 x1. s. zstep_l. zstep_r.
    rewrite !alist_find_map_snd.
    destruct (alist_find fn (SMod.fnsems md)) eqn: FIND; rewrite FIND; cycle 1.
    { s. zstep_l. }
    s.
    
    





    rewrite -(list_insert_id tgts cid _ x1).
    ziter_l. rewrite x0. s. zstep_l.
    eapply IHREL0; et; try rewrite !length_insert; et.

      



      
    
    


    
(*SLOW*)Qed.

Lemma cancel_main md rs
    (WFSP: sp_wf md)
    (WF: HMod.wf (SMod.to_hmod sp_none (SMod.cancel md)))
    (VALID: ✓ rs)
  :  
  refines_mod
    (HMod.to_mod (HModInline.inline (SMod.to_hmod sp_none (SMod.cancel md))) rs)
    (HMod.to_mod (HModInline.inline (SMod.to_hmod (sp_from md) md)) rs).
Proof.
  r. intro arg. eapply adequacy_global.
  instantiate (1:= smj_top). instantiate (1:= smj_top).
  unfold Mod.compile. s. rewrite /ITree.map /ModTr.trans /ModTr.interp_callE.  
  destruct (SMod.initial_code md) eqn: INIT; cycle 1.
  { s. rewrite /triggerUB. s. ginit. ziter_l. zstep_l. }
  destruct o; cycle 1.
  { s. rewrite /triggerUB. s. ginit. ziter_l. zstep_l. }

  s. rewrite /HModTr.trans_ktree.
  destruct f as [[msk scp][img bd]]. s.
  assert (SCP: incl scp (SMod.scopes md)).
  { ii. eapply SMod.well_scoped_initcode. rewrite INIT. et. }
  erewrite sandbox_inline_commute; et.
  erewrite sandbox_inline_commute; et.
  rewrite /SB.sandbox_body. s.

  ginit. guclo bindC_spec. econs; cycle 1.
  { instantiate (1:=eq). i. gstep. econs. econs. subst. et. }
  gfinal. right.
  
  eapply cancel_elim; et. econs; [|econs].
  econs; et; cycle 1.
  { rewrite bind_ret_r. et. }
  destruct img; s; cycle 1.
  - eapply (@elim_rel_refl _ false); et.
    left. esplits; et.
  - eapply (@elim_rel_refl _ true); et.
    left. esplits; et.
Unshelve. all: exact smj_top.
(*SLOW*)Qed.

(*** Final Theorem ***)
Theorem cancellation md P
  (WFSP: sp_wf md)
  (WF: HMod.wf (SMod.to_hmod sp_none (SMod.cancel md)))
  :
  refines (SMod.to_hmod sp_none (SMod.cancel md), P)
          (SMod.to_hmod (sp_from md) md, P).
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
