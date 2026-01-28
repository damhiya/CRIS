Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics CancelTactics.
Require Import MInline MInlineIntro MInlineElim ElimRel.

Lemma cancel_core `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG} md sp
  (X: Type) (PQ: X → (Any.t → iProp Σ) * (Any.t → iProp Σ)) mm
  R (e : coreE R):
  CANCEL_GOAL md sp PQ mm (trigger e) (trigger e).
Proof.
  r; i. destruct e.
  + iter_l. iter_r. rewrite x0 x1. s. step_r. i. step_r. step_l. exists x. step_l.
    norm_l. norm_r. rewrite !bind_ret_l.
    eapply KEY; et.
    { rewrite list_insert_id //. }
    { econs; eauto; eapply KTR. }
  + iter_l. iter_r. rewrite x0 x1. s. step_l. i. step_r. exists x. step_l. step_r.
    norm_l. norm_r. rewrite !bind_ret_l.
    eapply KEY; et.
    { rewrite list_insert_id //. }
    { econs; eauto; eapply KTR. }
  + iter_l. iter_r. rewrite x0 x1. s. norm_l. norm_r. step_l. i. subst.
    norm_l. norm_r. step_l. step_r. norm_l. norm_r. rewrite !bind_ret_l.
    eapply KEY; et.
    { rewrite list_insert_id //. }
    { econs; eauto; eapply KTR. }
Unshelve. all: exact smj_top.
(*SLOW*)Qed.
