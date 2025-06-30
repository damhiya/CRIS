Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import SModTr HModTr ModTr SMod HMod Mod.
Require Import ITactics TacticsCommon SimGlobal SimGlobalFacts CtxRefine ClosedAdequacy.
Require Import HModInline HModInlineIntro HModInlineElim ElimRel.
Require Import SimGlobal SimGTactics.

Lemma cancel_ag `{Σ: GRA} md sp R (e : agE R):
  CANCEL_GOAL md sp (trigger e) (trigger e).
Proof.
  r; i. destruct e.
  + ziter_l. ziter_r. rewrite x0 x1. s. zstep_l. zstep_r. ss. ired. hss. ired.
    ziter_l. do 2 zstep_l. ziter_r. zstep_r. eexists. zstep_r.
    ziter_l. do 2 zstep_l. ziter_r. zstep_r. eexists. zstep_r.
    ziter_l. zstep_l. ziter_r. zstep_r.
    ziter_l. zstep_l. ziter_r. zstep_r.
    des. eapply KEY, KTR; et.
  + ziter_l. ziter_r. rewrite x0 x1. s. zstep_l. zstep_r. ss. ired. hss. ired.
    ziter_r. do 2 zstep_r. ziter_l. zstep_l. eexists. zstep_l.
    ziter_r. do 2 zstep_r. ziter_l. zstep_l. eexists. zstep_l.
    ziter_r. do 2 zstep_r. ziter_l. zstep_l. eexists. zstep_l.
    ziter_l. do 2 zstep_l. ziter_r. zstep_r. eexists. zstep_r.
    ziter_l. zstep_l. ziter_r. zstep_r.
    ziter_l. zstep_l. ziter_r. zstep_r.
    des. eapply KEY, KTR; et.
  + ziter_l. ziter_r. rewrite x0 x1. s. zstep_l. zstep_r. ss. ired. hss. ired.
    ziter_r. do 2 zstep_r. ziter_l. zstep_l. eexists. zstep_l.
    ziter_r. do 2 zstep_r. ziter_l. zstep_l. eexists. zstep_l.
    ziter_l. zstep_l. ziter_r. zstep_r.
    ziter_l. zstep_l. ziter_r. zstep_r.
    des. eapply KEY, KTR; et.
Unshelve. all: et; try exact smj_top.
- des; et. split; et. rewrite RS in x3.
  iIntros "H". iMod (x3 with "H") as "[P O]". iFrame. et.
- rewrite RS. iIntros ">H". iApply x3. et.
- des; et. split; et. rewrite RS.
  iIntros ">H". iApply x3. et.
(*SLOW*)Qed.
