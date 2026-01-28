Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics CancelTactics.
Require Import MInline MInlineIntro MInlineElim ElimRel.

Lemma cancel_pg `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG} md sp 
  (X: Type) (PQ: X → (Any.t → iProp Σ) * (Any.t → iProp Σ)) mm
  R (e : pgE R):
  CANCEL_GOAL md sp PQ mm (trigger e) (trigger e).
Proof.
  r; i. destruct e.
  + iter_l. iter_r. rewrite x0 x1; s. step_l. step_r. norm_l. norm_r.
    rewrite !Any.pair_split /= !ModTr.state_encode_decode //.
    iter_l; iter_r; rewrite !list_lookup_insert -?EQLEN //; norm_l; norm_r; step_l; step_r.
    norm_l; norm_r. rewrite !list_insert_insert !bind_ret_l.
    eapply KEY; et.
    { ii. destruct (decide (i = k0)).
      { subst. rewrite lookup_insert in H. inv H; ss. }
      { rewrite lookup_insert_ne // in H. eauto. }
    }
    { rewrite list_insert_id //. }
    { econs; eauto; eapply KTR. }
  + iter_l. iter_r. rewrite x0 x1; s. step_l; step_r. norm_l; norm_r.
    rewrite !Any.pair_split /=. rewrite !bind_ret_l.
    eapply KEY; et.
    { rewrite list_insert_id //. }
    { econs; eauto; eapply KTR. }
(*SLOW*)Qed.
