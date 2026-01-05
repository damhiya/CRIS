Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics CancelTactics.
Require Import MInline MInlineIntro MInlineElim ElimRel.

Local Ltac sil := iter_l; rewrite !list_lookup_insert ?length_insert //.
Local Ltac snl := norm_l; rewrite !list_insert_insert ?bind_ret_l.
Local Ltac sir :=
  match goal with
  | [ EQLEN : length _ = length _ |- _ ] => iter_r; rewrite !list_lookup_insert ?length_insert -EQLEN //
  end.
Local Ltac snr := norm_r; rewrite !list_insert_insert ?bind_ret_l.

Lemma cancel_gettid `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG} md sp 
  (X: Type) (PQ: X → (Any.t → iProp Σ) * (Any.t → iProp Σ)) N mm stid :
  CANCEL_GOAL md sp PQ N mm (HoareGetTidE false stid) (HoareGetTidE true stid).
Proof.
  r; i. subst.

  iter_l. rewrite x0 /=. step_l. norm_l.
  iter_r. rewrite x1 /=. step_r. norm_r. rewrite !bind_ret_l.

  sil. step_l. snl. rewrite Any.pair_split /= !bind_ret_l Any.upcast_downcast /= !bind_ret_l.
  sir. step_r. i. step_r. snr.
  (* sir. step_r. i. *)
  (* sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l Any.upcast_downcast /= !bind_ret_l. *)
  (* sir. step_r. i. step_r. snr. *)
  sir. step_r. i. step_r. snr.
  sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l.
  sir. step_r. snr.
  sir. step_r. snr.
  sir. step_r. snr.
  sir. step_r. snr.
  sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l Any.upcast_downcast /= !bind_ret_l.
  sir. step_r. exists r_t. step_r. snr.
  sir. step_r. unshelve eexists; ired.
  { des; split; eauto.
    { eapply Own_wand_valid with (a1 := r_s); eauto. rewrite RS.
      iIntros ">[_ [$ _]]"; eauto. }
    rewrite x4. iIntros ">[$ $]". iPureIntro. sym.
    eapply Own_pure_soundness with (a:=r_s); eauto.
    iIntros "S". iPoseProof (RS with "S") as ">[_ [T [TA _]]]".
    iPoseProof (x4 with "T") as ">[T _]".
    iApply (TidToken_agree with "[T]"); iFrame.
  }
  step_r. snr.
  sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l.
  sir. step_r. snr.
  sir. step_r. snr.
  eapply KEY with (r_diff:=ε); eauto.
  { rewrite length_insert list_insert_id //. }
  { econs; eauto. eapply KTR. }
(*SLOW*)Qed.
