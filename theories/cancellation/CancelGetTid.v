Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics.
Require Import MInline MInlineIntro MInlineElim ElimRel.

Lemma cancel_gettid `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG} md sp :
  CANCEL_GOAL md sp NativeGetTidE HoareGetTidE.
Proof.
  r; i. subst.
  ziter_l; ziter_r. rewrite x0 x1 /=. zstep_l.
  zstep_r. zstep_r. ziter_l. zstep_l.
  ziter_r. zstep_r. ziter_r. zstep_r. ired.
  ziter_r. zstep_r. zstep_r. ziter_r. zstep_r. zstep_r.
  ziter_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r.
  ziter_r. zstep_r. ziter_r. zstep_r.
  ziter_r. zstep_r. ired. ziter_r. zstep_r. exists r_t. zstep_r.
  ziter_r. zstep_r. unshelve eexists.
  { des; split; eauto.
    { eapply Own_wand_valid with (a1 := r_s); eauto. rewrite RS.
      iIntros ">[_ [$ _]]"; eauto. }
    rewrite x5. iIntros ">[$ $]". iPureIntro. sym.
    eapply Own_pure_soundness with (a:=r_s); eauto.
    iIntros "S". iPoseProof (RS with "S") as ">[_ [T [TA _]]]".
    iPoseProof (x5 with "T") as ">[T _]".
    iApply (TidToken_agree with "[T]"); iFrame.
  }
  ired. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r.
  eapply KEY with (r_diff:=ε); eauto.
  { rewrite length_insert list_insert_id //. }
  { econs; eauto. eapply KTR. }
(*SLOW*)Qed.
