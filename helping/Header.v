Require Import CRIS.

Module Helping. Section Helping.
  Context `{Σ : GRA}.
  Context (mn : string).

  Definition run  := mn +:+ ".run".
  Definition help  := mn +:+ ".help".

  Definition pureE := agE +' coreE.

  Definition trans {R} (itr: itree pureE R) : itree crisE R :=
    translate (case_ (bif:=sum1) subevent subevent) itr.

  Lemma trans_bind {R1 R2} (itr : itree pureE R1) (ktr : R1 → itree pureE R2) :
    trans (x <- itr;; ktr x) = x <- trans itr;; trans (ktr x).
  Proof.
    rewrite /trans (bisim_is_eq (translate_bind _ _ _)) //.
  Qed.

  Lemma trans_take {X R} (ktr : X → itree pureE R) :
    trans (x <- trigger (Take X);; ktr x) = x <- trigger (Take X);; trans (ktr x).
  Proof.
    rewrite trans_bind; f_equal.
    rewrite /trans ?trigger_vis (bisim_is_eq (unfold_translate _ _)) /case_ /=.
    rewrite /resum /ReSum_id /id_ /Id_IFun /=.
    do 2 f_equal. extensionalities x. rewrite (bisim_is_eq (translate_ret _ _)) //.
  Qed.

  Lemma trans_choose {X R} (ktr : X → itree pureE R) :
    trans (x <- trigger (Choose X);; ktr x) = x <- trigger (Choose X);; trans (ktr x).
  Proof.
    rewrite trans_bind; f_equal.
    rewrite /trans ?trigger_vis (bisim_is_eq (unfold_translate _ _)) /case_ /=.
    rewrite /resum /ReSum_id /id_ /Id_IFun /=.
    do 2 f_equal. extensionalities x. rewrite (bisim_is_eq (translate_ret _ _)) //.
  Qed.

  Lemma trans_Assume {P R} (ktr : () → itree pureE R) :
    trans (x <- trigger (Assume P);; ktr x) = x <- trigger (Assume P);; trans (ktr x).
  Proof.
    rewrite trans_bind; f_equal.
    rewrite /trans ?trigger_vis (bisim_is_eq (unfold_translate _ _)) /case_ /=.
    rewrite /resum /ReSum_id /id_ /Id_IFun /=.
    do 2 f_equal. extensionalities x. rewrite (bisim_is_eq (translate_ret _ _)) //.
  Qed.

  Lemma trans_Guarantee {P R} (ktr : () → itree pureE R) :
    trans (x <- trigger (Guarantee P);; ktr x) = x <- trigger (Guarantee P);; trans (ktr x).
  Proof.
    rewrite trans_bind; f_equal.
    rewrite /trans ?trigger_vis (bisim_is_eq (unfold_translate _ _)) /case_ /=.
    rewrite /resum /ReSum_id /id_ /Id_IFun /=.
    do 2 f_equal. extensionalities x. rewrite (bisim_is_eq (translate_ret _ _)) //.
  Qed.

  Lemma trans_ret {R} (r : R) : trans (Ret r) = Ret r.
  Proof. rewrite /trans (bisim_is_eq (translate_ret _ _)) //. Qed.
  Definition exports := [run; help].
End Helping. End Helping.