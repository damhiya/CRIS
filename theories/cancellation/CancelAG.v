Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics CancelTactics.
Require Import MInline MInlineIntro MInlineElim ElimRel.

(* before CancelTactics : 26.12s *)
(* after CancelTactics : 14.60s *)

Local Ltac sil := iter_l; rewrite !list_lookup_insert ?length_insert //.
Local Ltac snl := norm_l; rewrite !list_insert_insert !bind_ret_l.
Local Ltac sir :=
  match goal with
  | [ EQLEN : length _ = length _ |- _ ] => iter_r; rewrite !list_lookup_insert ?length_insert -EQLEN //
  end.
Local Ltac snr := norm_r; rewrite !list_insert_insert !bind_ret_l.

Lemma cancel_ag `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG} md sp R (e : agE R):
  CANCEL_GOAL md sp (trigger e) (trigger e).
Proof.
  r; i. destruct e.
  + iter_l; rewrite x0 /=; step_l. norm_l.
    iter_r; rewrite x1 /=; step_r. norm_r.
    rewrite !Any.pair_split /= !bind_ret_l !Any.upcast_downcast /= !bind_ret_l.

    sil. step_l. i. step_l. snl.
    sil. step_l. i. step_l. snl.
    sil. step_l. snl. rewrite Any.pair_split /= !bind_ret_l.
    sil. step_l. snl.

    des. hexploit (Own_bupd_split); eauto.
    intros [x5 [x6 [Himpl [Hx5 Hx6]]]].

    sir. step_r. exists (r_t ⋅ x5). step_r. snr.
    sir. step_r.
    unshelve eexists; ired.
    { 
      split; first eapply Own_wand_valid.
      { rewrite Own_op. iIntros "X"; iMod (Himpl with "X") as "[$ X]"; rewrite Hx6.
        iMod (RS with "X") as "[? [$ [_ _]]]"; done.
      }
      { done. }
      rewrite Own_op; rewrite Hx5 comm; iIntros "[$ $]"; done.
    }
    step_r. norm_r. rewrite !list_insert_insert.
    sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l.
    sir. step_r. snr.

    eapply KEY; des; eauto.
    { rewrite list_insert_id //= Himpl Own_op. iIntros "> [$ X]"; rewrite Hx6 RS //. }
    { econs; eauto; eapply KTR. }
  + iter_l. rewrite x0 /=. step_l. norm_l.
    iter_r. rewrite x1 /=. step_r. norm_r.
    rewrite !Any.pair_split /= !bind_ret_l !Any.upcast_downcast /= !bind_ret_l.
    sil. step_l. i. step_l. snl.
    sil. step_l. snl. rewrite Any.pair_split /= !bind_ret_l.
    sil. step_l. snl.

    sir. step_r.
    unshelve eexists; ired.
    { eapply Own_wand_valid; last apply x.
      rewrite !Own_op RS; iIntros "[$ > [_ [$ [_ _]]]] //".
    }
    step_r. norm_r. rewrite !list_insert_insert.
    sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l.
    sir. step_r. snr.
    
    eapply KEY; eauto.
    { rewrite list_insert_id // ?Own_op RS. iIntros "[$ > $]"; done. }
    { econs; eauto; eapply KTR. }
  + iter_l. rewrite x0 /=. step_l. norm_l.
    iter_r. rewrite x1 /=. step_r. norm_r.
    rewrite !Any.pair_split /= !bind_ret_l !Any.upcast_downcast /= !bind_ret_l.
    sir. step_r. i. step_r. snr.
    sir. step_r. i. step_r. snr.
    sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l.
    sir. step_r. snr.

    hexploit Own_bupd_split; eauto. intros [r_s1 [r_s2 [Hr_s [Hr_s1 Hr_s2]]]].
    hexploit Own_split; try eapply Hr_s2; eauto.
    { eapply Own_wand_valid; [iIntros "X"; iMod (Hr_s with "X") as "[_ $]"; eauto|eauto]. }
    intros [r_s3 [r_s4 [Hr_s3 [Hr_s4 Hr_s5]]]].

    sil. step_l. exists (r_s1 ⋅ (x ⋅ r_s4)). step_l. snl.
    sil. step_l.
    unshelve eexists; ired.
    { des. split; first eapply Own_wand_valid.
      { rewrite !Own_op; iIntros "X"; iMod (Hr_s with "X") as "[$ X]"; rewrite Hr_s3 Own_op Hr_s4.
        iDestruct "X" as "[X $]". iMod (x4 with "X") as "[? $]"; done.
      }
      { done. }
      { rewrite !Own_op; iIntros "X"; iMod (Hr_s with "X") as "[$ X]"; rewrite Hr_s3 Own_op Hr_s4.
        iDestruct "X" as "[X $]". iMod (x4 with "X") as "[? $]"; done.
      }
    } 
    step_l. norm_l. rewrite !list_insert_insert.
    sil. step_l. snl. rewrite Any.pair_split /= !bind_ret_l.
    sil. step_l. snl.
    
    eapply KEY; eauto.
    { des. eapply Own_wand_valid.
      { rewrite !Own_op. iIntros "X"; iMod (Hr_s with "X") as "[$ X2]". rewrite Hr_s3 Own_op.
        iDestruct "X2" as "[X2 $]". iPoseProof (Hr_s4 with "X2") as "X".
        iMod (x4 with "X") as "[? $]"; done.
      }
      done.
    }
    { rewrite list_insert_id // !Own_op Hr_s1 Hr_s5. eapply bupd_intro. }
    { econs; eauto; eapply KTR. }
(*SLOW*)Qed.
