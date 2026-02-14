Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics GSimAux.
Require Import MInline MInlineIntro MInlineElim ElimRel.
Local Ltac gnorm_itr :=
  match goal with
  | |- context [?A] =>
      match type of A with
      | itree crisE Any.t => pattern A; eapply eq_ind; [|symmetry; hnorm_itr]
      end
  end.

Lemma cancel_gettid `{_crisG: !crisG Γ Σ α β τ _S _I} md sp :
  CANCEL_GOAL md sp (HoareGetTidE false) (HoareGetTidE true).
Proof.
  r; i. subst.
  ss. rewrite /ModTr.trans in x1 x0.
  eapply gsim_Choose_tgt; [rewrite x1; do 2 f_equal; hnorm_itr|]. intros tid. s. ghnorm_r.
  eapply gsim_tau_tgt; [lookup_tac; try lia; do 2 f_equal|]. rewrite list_insert_insert.
  eapply gsim_Guarantee_tgt; [lookup_tac; try lia; do 2 f_equal; hnorm_itr|].
  rewrite list_insert_insert. intros rt2 Hrt2. ghnorm_r.
  eapply gsim_tau_tgt; [lookup_tac; try lia; do 2 f_equal|]. rewrite list_insert_insert.
  eapply gsim_GetTid_src; [rewrite x0; do 2 f_equal; hnorm_itr|]. s. ghnorm_l.
  eapply gsim_tau_src; [lookup_tac; try lia; do 2 f_equal|]. rewrite list_insert_insert. ghnorm_l.
  eapply gsim_GetTid_tgt; [lookup_tac; try lia; do 2 f_equal; hnorm_itr|].
  rewrite list_insert_insert. ghnorm_r.
  eapply gsim_tau_tgt; [lookup_tac; try lia; do 2 f_equal|]. rewrite list_insert_insert.
  eapply gsim_Assume_tgt; [lookup_tac; try lia; do 2 f_equal; hnorm_itr|].
  rewrite list_insert_insert.
  exists r_t. splits.
  { eapply Own_wand_valid with (a1 := r_s); eauto. rewrite RS. iIntros ">[_ [$ _]]"; eauto. }
  { destruct Hrt2 as [? Hrt2]; rewrite Hrt2.
    iIntros ">[$ $]". iPureIntro. symmetry.
    eapply Own_pure_soundness with (a:=r_s); eauto.
    iIntros "S". iPoseProof (RS with "S") as ">[_ [T [TA _]]]".
    iPoseProof (Hrt2 with "T") as ">[T _]". iApply (TidToken_agree with "[T]"); iFrame.
  }
  ghnorm_r.
  eapply gsim_tau_tgt; [lookup_tac; try lia; do 2 f_equal|]. rewrite list_insert_insert.
  ghnorm_r.

  eapply KEY with (r_diff:=ε); eauto.
  { rewrite length_insert list_insert_id //. }
  { econs; eauto. eapply KTR. }
(*SLOW*)Qed.
