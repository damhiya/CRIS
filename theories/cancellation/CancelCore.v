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
  + ziter_l. ziter_r. rewrite x0 x1. s. do 2 czstep_r. czstep_l. eexists. czstep_l.
    eapply KEY; et.
    { rewrite list_insert_id //. }
    { econs; eauto; eapply KTR. }
  + ziter_l. ziter_r. rewrite x0 x1. s. do 2 czstep_l. czstep_r. eexists. czstep_r.
    eapply KEY; et.
    { rewrite list_insert_id //. }
    { econs; eauto; eapply KTR. }
  + ziter_l. ziter_r. rewrite x0 x1. s. zstep. czstep_l. czstep_r. subst.
    eapply KEY; et.
    { rewrite list_insert_id //. }
    { econs; eauto; eapply KTR. }
Unshelve. all: exact smj_top.
(*SLOW*)Qed.
