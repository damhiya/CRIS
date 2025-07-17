Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import SModTr HModTr ModTr SMod HMod Mod.
Require Import ITactics TacticsCommon SimGlobal SimGlobalFacts CtxRefine ClosedAdequacy.
Require Import HModInline HModInlineIntro HModInlineElim ElimRel.
Require Import SimGlobal SimGTactics.

Lemma cancel_pg `{Σ: GRA} md sp R (e : pgE R):
  CANCEL_GOAL md sp (trigger e) (trigger e).
Proof.
  r; i. destruct e.
  + ziter_l. ziter_r. rewrite x0 x1. s. czstep_l. czstep_r. ss.
    ziter_l. czstep_l. ziter_r. czstep_r. rewrite !HModTr.alist_encode_decode.
    eapply KEY; et.
    { rewrite list_insert_id //. }
    { econs; eauto; eapply KTR. }
  + ziter_l. ziter_r. rewrite x0 x1. s. czstep_l. czstep_r. ss. ired.
    eapply KEY; et.
    { rewrite list_insert_id //. }
    { econs; eauto; eapply KTR. }
Unshelve. all: exact smj_top.
(*SLOW*)Qed.
