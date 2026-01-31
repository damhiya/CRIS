Require Import CRIS.
Require Import SchHeader.

Module Helping. Section Helping.
  Context `{Σ : GRA}.
  Context (mn : string).

  Definition run  := "★" +:+ mn.
  Definition help := "☆" +:+ mn.
  Definition yield := "∘" +:+ mn.

  (* Definition pureE := agE +' coreE.

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
  Proof. rewrite /trans (bisim_is_eq (translate_ret _ _)) //. Qed. *)
  Definition exports : gset string := {[run; help]}.
End Helping. End Helping.

(* Section names.
  Context (mn : string).

  Lemma get_tid_run_neq : SchHdr.get_tid ≠ Helping.run mn.
  Proof.
    rewrite /SchHdr.get_tid /Helping.run; destruct (decide (String.length mn = 7)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.get_tid" = 11) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (3 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Lemma get_tid_help_neq : SchHdr.get_tid ≠ Helping.help mn.
  Proof.
    rewrite /SchHdr.get_tid /Helping.help; destruct (decide (String.length mn = 6)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.get_tid" = 11) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (3 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Lemma yield_run_neq : SchHdr.yield ≠ Helping.run mn.
  Proof.
    rewrite /SchHdr.yield /Helping.run; destruct (decide (String.length mn = 5)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.yield" = 9) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (3 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Lemma yield_help_neq : SchHdr.yield ≠ Helping.help mn.
  Proof.
    rewrite /SchHdr.yield /Helping.help; destruct (decide (String.length mn = 4)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.yield" = 9) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (0 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Lemma join_run_neq : SchHdr.join ≠ Helping.run mn.
  Proof.
    rewrite /SchHdr.join /Helping.run; destruct (decide (String.length mn = 4)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.join" = 8) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (1 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Lemma join_help_neq : SchHdr.join ≠ Helping.help mn.
  Proof.
    rewrite /SchHdr.join /Helping.help; destruct (decide (String.length mn = 3)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.join" = 8) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (1 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Lemma spawn_run_neq : SchHdr.spawn ≠ Helping.run mn.
  Proof.
    rewrite /SchHdr.spawn /Helping.run; destruct (decide (String.length mn = 5)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.spawn" = 9) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (2 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Lemma spawn_help_neq : SchHdr.spawn ≠ Helping.help mn.
  Proof.
    rewrite /SchHdr.spawn /Helping.help; destruct (decide (String.length mn = 4)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch.spawn" = 9) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (0 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Lemma _spawn_run_neq : SchHdr._spawn ≠ Helping.run mn.
  Proof.
    rewrite /SchHdr._spawn /Helping.run; destruct (decide (String.length mn = 6)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch._spawn" = 10) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (1 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.

  Lemma _spawn_help_neq : SchHdr._spawn ≠ Helping.help mn.
  Proof.
    rewrite /SchHdr._spawn /Helping.help; destruct (decide (String.length mn = 5)) as [Hlen|];
      cycle 1.
    { assert (Hlen : String.length "Sch._spawn" = 10) by ss.
      intros Heq; rewrite Heq string_length_app in Hlen; ss; lia.
    }
    rewrite -get_correct; intros Hfalse; specialize (Hfalse (1 + String.length mn)).
    rewrite -(append_correct2 _ _) Hlen in Hfalse; ss.
  Qed.
End names. *)