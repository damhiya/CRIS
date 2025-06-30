Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import SModTr HModTr ModTr SMod HMod Mod.
Require Import ITactics TacticsCommon SimGlobal SimGlobalFacts CtxRefine ClosedAdequacy.
Require Import HModInline HModInlineIntro HModInlineElim ElimRel.
Require Import SimGlobal SimGTactics.

Lemma cancel_post `{Σ: GRA} md sp:
  ∀ (rs0: Σ) r_s r_t srcs tgts cid st ps pt vret X X' x x' Qo Qo' itrS ktrT k
    (r: ∀ x x0, (x→x0→Prop)→smj→smj→itree coreE x→itree coreE x0→Prop)
    (WFS: smod_wf md)
    (VP: valid_sp md sp)
    (WF: HMod.wf (SMod.to_hmod sp_none (SMod.cancel md)))
    (KEY: ∀ itrS' itrT' st (r_s r_t: Σ) tid
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
          (Any.pair (HModTr.alist_encode st) r_t ↑)))
    (EQLEN : length srcs = length tgts)
    (REL : ∀ i x y, srcs !! i = Some x → tgts !! i = Some y → thread_rel sp i x y)
    (WFR : ✓ r_s)
    (RS : Own r_s ⊢ |==> Own r_t)
    (LEN : cid < length srcs)
    (x0 : srcs !! cid = Some (HModTr.trans (tau;; tau;; itrS)))
    (x1 : tgts !! cid = Some (x <- HModTr.trans (x <- elim_postcond Qo Qo' x x' vret;; ktrT x);; k x))
    (RET : cid = 0 → k = λ x : Any.t, Ret x)
    (KTR :
    ∃ Q : X → Any.t → Any.t → iProp Σ,
      (Qo = Some Q
       ∨ Qo = None ∧ Q = λ (_ : X) (varg arg : Any.t), ⌜varg = arg⌝%I)
      ∧ ∃ Q' : X' → Any.t → Any.t → iProp Σ,
          (Qo' = Some Q'
           ∨ Qo' = None ∧ Q' = λ (_ : X') (varg arg : Any.t), ⌜varg = arg⌝%I)
          ∧ (∀ ret : Any.t, Q' x' vret ret ⊢ |==> Q x vret ret)
            ∧ upaco3 (elim_rel_def sp) bot3 Any.t itrS (ktrT vret)),

  gpaco7 _simg (cpn7 _simg) bot7 r (Any.t * Any.t)%type 
    (Any.t * Any.t)%type cancel_eq ps pt
    (ModTr.interp_stateE Any.t
       (iterV (ModTr.handle_callE (Mod.prog (HMod.to_mod (HModInline.inline
              (SMod.to_hmod sp_none (SMod.cancel md))) rs0))) (cid, srcs))
       (Any.pair (HModTr.alist_encode st) r_s ↑))
    (ModTr.interp_stateE Any.t
       (iterV (ModTr.handle_callE (Mod.prog (HMod.to_mod (HModInline.inline
              (SMod.to_hmod sp md)) rs0))) (cid, tgts))
       (Any.pair (HModTr.alist_encode st) r_t ↑)).
Proof.
  i. ziter_l. ziter_r. rewrite x0 x1. s. zstep_l. ziter_l. zstep_l.
  move KTR at bottom. des_safe.
  destruct KTR0; subst; des_safe.
  {
    zstep_r. zstep_r.
    ziter_r. zstep_r. ziter_r. zstep_r.
    ziter_r. zstep_r. zstep_r. ziter_r. zstep_r. zstep_r.
    ziter_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r.
    ziter_r. zstep_r. ziter_r. zstep_r.

    des; subst.
    {
      ziter_r. zstep_r. eexists. zstep_r.
      ziter_r. zstep_r. ziter_r. zstep_r.
      ziter_r. zstep_r. eexists r_t. zstep_r.
      ziter_r. zstep_r. unshelve eexists.
      { split; eauto using Own_wand_valid.
        iIntros "H". iMod (x5 with "H") as "[P O]". rewrite KTR1. iFrame. 
      }
      zstep_r.
      ziter_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r.

      pclearbot. eapply KEY; et.
    }
    {
      assert (vret = x2).
      { eapply Own_pure_soundness; try apply WFR.
        rewrite RS. iIntros ">H". iMod (x5 with "H") as "[P O]".
        rewrite KTR1. iMod "P" as "P"; et.
      }
      des. subst.
      ired. pclearbot. eapply KEY; et.
      rewrite RS. iIntros ">H". iMod (x5 with "H") as "[P O]". iFrame. et.
    }
  }
  {
    s. zstep_r.
    des; subst.      
    {
      ziter_r. zstep_r.
      ziter_r. zstep_r. eexists. zstep_r.
      ziter_r. zstep_r. ziter_r. zstep_r.
      ziter_r. zstep_r. eexists r_t. zstep_r.
      ziter_r. zstep_r. unshelve eexists.
      { split; eauto using Own_wand_valid.
        iIntros "H". iFrame. iApply KTR1. et.
      }
      zstep_r.
      ziter_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r.

      pclearbot. eapply KEY; et.
    }
    {
      ziter_r. zstep_r.
      pclearbot. eapply KEY; et.
    }
  }
Unshelve. all: try exact smj_top.
(*SLOW*)Qed.
