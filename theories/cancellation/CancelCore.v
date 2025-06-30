Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import SModTr HModTr ModTr SMod HMod Mod.
Require Import ITactics TacticsCommon SimGlobal SimGlobalFacts CtxRefine ClosedAdequacy.
Require Import HModInline HModInlineIntro HModInlineElim ElimRel.
Require Import SimGlobal SimGTactics.

Lemma cancel_core `{Σ: GRA} md sp R (e : coreE R):
  CANCEL_GOAL md sp (trigger e) (trigger e).
Proof.
  r; i. destruct e.
  + ziter_l. ziter_r. rewrite x0 x1. s. do 2 zstep_r. zstep_l. eexists. zstep_l.
    eapply KEY, KTR; et.
  + ziter_l. ziter_r. rewrite x0 x1. s. do 2 zstep_l. zstep_r. eexists. zstep_r.
    eapply KEY, KTR; et.
  + ziter_l. ziter_r. rewrite x0 x1. s. zstep. zstep_l. zstep_r. subst.
    eapply KEY, KTR; et.
Unshelve. all: exact smj_top.
(*SLOW*)Qed.
