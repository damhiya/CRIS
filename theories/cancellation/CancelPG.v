Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics.
Require Import MInline MInlineIntro MInlineElim ElimRel.

Lemma cancel_pg `{_crisG: !crisG Γ Σ α β τ _S _I} md sp R (e : pgE R) :
  CANCEL_GOAL md sp (trigger e) (trigger e).
Proof.
  r; i. destruct e.
  + giter_s. giter_t. s. rewrite x0 x1; s. gstep_s. gstep_t. gcNormS. gcNormT.
    rewrite !Any.pair_split /= !ModTr.state_encode_decode //.
    giter_s; giter_t. s. rewrite !list_lookup_insert -?EQLEN //; gcNormS; gcNormT; gstep_s; gstep_t.
    gcNormS; gcNormT. rewrite !list_insert_insert !bind_ret_l.
    eapply KEY; et.
    { ii. destruct (decide (i = k)).
      { subst. rewrite lookup_insert in H. inv H; ss. }
      { rewrite lookup_insert_ne // in H. eauto. }
    }
    { rewrite list_insert_id //. }
    { econs; eauto; eapply KTR. }
  + giter_s. giter_t. rewrite /= x0 x1; s. gstep_s; gstep_t. gcNormS; gcNormT.
    rewrite !Any.pair_split /=. rewrite !bind_ret_l.
    eapply KEY; et.
    { rewrite list_insert_id //. }
    { econs; eauto; eapply KTR. }
(*SLOW*)Qed.
