Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics.
Require Import MInline MInlineIntro MInlineElim ElimRel.

Lemma cancel_ag `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG} md sp R (e : agE R):
  CANCEL_GOAL md sp (trigger e) (trigger e).
Proof.
  r; i. destruct e.
  + ziter_l; rewrite x0 /=; zstep_l. ired.
    ziter_r; rewrite x1 /=; zstep_r. ired. hss.
    ziter_l; do 2 zstep_l; ziter_l; do 2 zstep_l.
    ziter_l; zstep_l; ziter_l; zstep_l; des.
    hexploit (Own_bupd_split); eauto.
    intros [x5 [x6 [Himpl [Hx5 Hx6]]]].
    ziter_r; zstep_r; exists (r_t ⋅ x5). zstep_r; ziter_r; zstep_r.
    eexists; zstep_r; ziter_r; zstep_r; ziter_r; zstep_r.
    eapply KEY; des; eauto.
    { rewrite list_insert_id //= Himpl Own_op. iIntros "> [$ X]"; rewrite Hx6 RS //. }
    { econs; eauto; eapply KTR. }
  + ziter_l; rewrite x0 /=. zstep_l; ired; hss.
    ziter_l; zstep_l. zstep_l.
    ziter_l; zstep_l. ziter_l; zstep_l.
    ziter_r; rewrite x1 /=; zstep_r; ired; hss.
    ziter_r; zstep_r. unshelve eexists.
    { eapply Own_wand_valid; last apply x.
      rewrite !Own_op RS; iIntros "[$ > [_ [$ [_ _]]]] //".
    }
    zstep_r.
    ziter_r; zstep_r. ziter_r; zstep_r.
    eapply KEY; eauto.
    { rewrite list_insert_id // ?Own_op RS; iIntros "[$ > [$ $]]"; done. }
    { econs; eauto; eapply KTR. }
  + ziter_r; rewrite x1 /=; zstep_r; ired; hss.
    ziter_r; do 2 zstep_r. ziter_r; do 2 zstep_r.
    ziter_r; zstep_r. ziter_r; zstep_r.
    hexploit Own_bupd_split; eauto; intros [r_s1 [r_s2 [Hr_s [Hr_s1 Hr_s2]]]].
    hexploit Own_split; try eapply Hr_s2; eauto.
    { eapply Own_wand_valid; [iIntros "X"; iMod (Hr_s with "X") as "[_ $]"; eauto|eauto]. }
    intros [r_s3 [r_s4 [Hr_s3 [Hr_s4 Hr_s5]]]].
    ziter_l; rewrite x0 /=; zstep_l; ired; hss.
    ziter_l; zstep_l; exists (r_s1 ⋅ (x ⋅ r_s4)).
    zstep_l. ziter_l; zstep_l; eexists; zstep_l.
    ziter_l; zstep_l. ziter_l; zstep_l.
    eapply KEY; eauto.
    { eapply Own_wand_valid.
      { rewrite !Own_op. iIntros "X"; iMod (Hr_s with "X") as "[$ X2]". rewrite Hr_s3 Own_op.
        iDestruct "X2" as "[X2 $]". iPoseProof (Hr_s4 with "X2") as "X".
        iMod (x4 with "X") as "[? $]"; done.
      }
      done.
    }
    { rewrite list_insert_id // !Own_op Hr_s1 Hr_s5; eapply bupd_intro. }
    { econs; eauto; eapply KTR. }
Unshelve.
{ split; first eapply Own_wand_valid.
  { rewrite Own_op. iIntros "X"; iMod (Himpl with "X") as "[$ X]"; rewrite Hx6.
    iMod (RS with "X") as "[? [$ [_ _]]]"; done.
  }
  { done. }
  rewrite Own_op; rewrite Hx5 comm; iIntros "[$ $]"; done.
}
{ split; first eapply Own_wand_valid.
  { rewrite !Own_op; iIntros "X"; iMod (Hr_s with "X") as "[$ X]"; rewrite Hr_s3 Own_op Hr_s4.
    iDestruct "X" as "[X $]". iMod (x4 with "X") as "[? $]"; done.
  }
  { done. }
  { rewrite !Own_op; iIntros "X"; iMod (Hr_s with "X") as "[$ X]"; rewrite Hr_s3 Own_op Hr_s4.
    iDestruct "X" as "[X $]". iMod (x4 with "X") as "[? $]"; done.
  }
}
(*SLOW*)Qed.
