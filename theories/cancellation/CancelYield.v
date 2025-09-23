Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics.
Require Import MInline MInlineIntro MInlineElim ElimRel.

Lemma cancel_yield `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG} md sp tid :
  CANCEL_GOAL md sp (NativeYieldE tid) (HoareYieldE tid).
Proof.
  r; i. subst.
  ziter_l; ziter_r. rewrite x0 x1 /=. zstep_l.
  zstep_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r. ired.
  ziter_r. zstep_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r. zstep_r.
  ziter_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r.

  destruct (decide (tid < length rs_diff)); cycle 1.
  {
    ziter_l. destruct (<[cid:=_]> srcs !! tid) eqn:FIND.
    { eapply lookup_lt_Some in FIND. rewrite length_insert in FIND. nia. }
    { zstep_l. zstep_l. }
  }
  destruct (decide (tid = cid)); subst.
  {
    ziter_l. zstep_l. ziter_r. zstep_r. ziter_r. zstep_r. ired.
    ziter_r. zstep_r. exists r_t. zstep_r. ziter_r. zstep_r. unshelve eexists; ired.
    { admit. }
    zstep_r. ziter_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r.
    eapply KEY with (r_diff:=ε); eauto.
    { rewrite length_insert list_insert_id //. }
    { eapply thread_rel_body; eauto. eapply KTR. }
  }
  { do 2 dup l. rename l into SRC, l0 into TGT, l1 into RES.
    rewrite EQLEN2 in SRC. rewrite EQLEN2 EQLEN in TGT.
    Search (_ < length _ → _ !! _ = Some _).
    eapply lookup_lt_Some
  }
Admitted.
