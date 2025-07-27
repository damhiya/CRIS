Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics.
Require Import MInline MInlineIntro MInlineElim ElimRel.

Lemma cancel_ag `{Σ: GRA} md sp R (e : agE R):
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
  + ziter_r; rewrite x1 /=; zstep_r; ired; hss.
    ziter_r; do 2 zstep_r; ziter_r; zstep_r; zstep_r; ziter_r; do 2 zstep_r.
    hexploit (Own_bupd_split); first (eapply RS); eauto.
    intros [r_s1 [r_s2 [Hr_S [Hr_s1 Hr_s2]]]].
    hexploit (Own_bupd_split); first eapply x4.
    { eapply Own_wand_valid; first (etrans; last eapply bupd_intro); eauto.
      hexploit Own_bupd_valid; eauto using cmra_valid_op_r.
    }
    intros [r_t1 [r_t2 [Hr_t [Hr_t1 Hr_t2]]]].
    ziter_l; rewrite x0 /=. zstep_l; ired; hss.
    ziter_l; zstep_l. exists x.
    zstep_l; ziter_l; zstep_l.
    exists (r_s1 ⋅ x3). zstep_l. ziter_l. zstep_l.
    eexists. zstep_l. ziter_l. do 2 zstep_l. ziter_l. zstep_l.
    ziter_l. zstep_l.
    ziter_r. zstep_r. eexists. zstep_r. ziter_r; zstep_r. ziter_r; zstep_r.
    eapply KEY; eauto.
    { rewrite list_insert_id // ?Own_op Hr_s1; iIntros "[$ [$ $]]"; done. }
    { econs; eauto; eapply KTR. }
  + ziter_r; rewrite x1 /=; zstep_r; ired; hss.
    ziter_r; do 2 zstep_r. ziter_r; do 2 zstep_r.
    ziter_r; zstep_r. ziter_r; zstep_r.
    hexploit Own_bupd_split; eauto; intros [r_s1 [r_s2 [Hr_s [Hr_s1 Hr_s2]]]].
    ziter_l; rewrite x0 /=; zstep_l; ired; hss.
    ziter_l; zstep_l; exists (r_s1 ⋅ x).
    zstep_l. ziter_l; zstep_l; eexists; zstep_l.
    ziter_l; zstep_l. ziter_l; zstep_l.
    eapply KEY; eauto.
    { eapply Own_wand_valid.
      { rewrite Own_op. iIntros "X"; iMod (Hr_s with "X") as "[$ X2]".
        iPoseProof (Hr_s2 with "X2") as "X"; iMod (x4 with "X") as "[? $]"; done.
      }
      done.
    }
    { rewrite list_insert_id // Own_op Hr_s1; eapply bupd_intro. }
    { econs; eauto; eapply KTR. }
Unshelve.
{ split; first eapply Own_wand_valid.
  { rewrite Own_op. iIntros "X"; iMod (Himpl with "X") as "[$ X]"; rewrite Hx6.
    iMod (RS with "X") as "[? $]"; done.
  }
  { done. }
  rewrite Own_op; rewrite Hx5 comm; iIntros "[$ $]"; done.
}
{ rewrite Hr_S Own_op; iIntros "> [$ S]"; rewrite Hr_s2 Hr_t Hr_t1 Hr_t2 //. }
{ revert x5; rewrite (comm _ r_s1 x3) assoc; eauto using cmra_valid_op_l. }
{ split; first eapply Own_wand_valid.
  { rewrite Own_op; iIntros "X"; iMod (Hr_s with "X") as "[$ X]"; rewrite Hr_s2.
    iMod (x4 with "X") as "[? $]"; done.
  }
  { done. }
  { rewrite Own_op; iIntros "X"; iMod (Hr_s with "X") as "[$ X]"; rewrite Hr_s2.
    iMod (x4 with "X"); done.
  }
}
(*SLOW*)Qed.
