Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics.
Require Import MInline MInlineIntro MInlineElim ElimRel.

Lemma cancel_pg `{Σ: GRA} md sp R (e : pgE R):
  CANCEL_GOAL md sp (trigger e) (trigger e).
Proof.
  r; i. destruct e.
  + ziter_l. ziter_r. rewrite x0 x1. s. zstep_l. zstep_r. ss.
    ziter_l. zstep_l. ziter_r. zstep_r. rewrite !ModTr.alist_encode_decode.
    eapply KEY; et.
    { rewrite list_insert_id //. }
    { econs; eauto; eapply KTR. }
  + ziter_l. ziter_r. rewrite x0 x1. s. zstep_l. zstep_r. ss. ired.
    eapply KEY; et.
    { rewrite list_insert_id //. }
    { econs; eauto; eapply KTR. }
(*SLOW*)Qed.
