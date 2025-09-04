(* Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics.
Require Import MInline MInlineIntro MInlineElim ElimRel.

Lemma cancel_core `{Σ: GRA} md sp R (e : coreE R):
  CANCEL_GOAL md sp (trigger e) (trigger e).
Proof.
  r; i. destruct e.
  + ziter_l. ziter_r. rewrite x0 x1. s. do 2 zstep_r. zstep_l. eexists. zstep_l.
    eapply KEY; et.
    { rewrite list_insert_id //. }
    { econs; eauto; eapply KTR. }
  + ziter_l. ziter_r. rewrite x0 x1. s. do 2 zstep_l. zstep_r. eexists. zstep_r.
    eapply KEY; et.
    { rewrite list_insert_id //. }
    { econs; eauto; eapply KTR. }
  + ziter_l. ziter_r. rewrite x0 x1. s. zstep. zstep_l. zstep_r. subst.
    eapply KEY; et.
    { rewrite list_insert_id //. }
    { econs; eauto; eapply KTR. }
Unshelve. all: exact smj_top.
(*SLOW*)Qed. *)
