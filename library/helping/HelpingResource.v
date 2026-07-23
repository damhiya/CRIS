From CRIS.common Require Import CRIS.
From CRIS.helping Require Export HelpingHeader.
From iris.algebra Require Import gmap_view coPset.

(* Public resources used by the helping module and its clients. *)
Class helpingGpreS `{!crisG Γ Σ α β τ _S _I} := HelpingG {
  #[local] helping_inG :: inG (prodR
    (optionR coPset_disjUR)
    (optionR (gmap_viewR nat (agreeR (leibnizO help_state))))) Γ;
  #[local] tokenG :: inG (exclR unitO) Γ;
}.
Global Hint Mode helpingGpreS - - - - - - - - : typeclass_instances.

Definition helpingΓ := #[
  prodR (optionR coPset_disjUR)
    (optionR (gmap_viewR nat (agreeR (leibnizO help_state))));
  exclR unitO
].

Global Instance subG_helpingpreS `{!crisG Γ Σ α β τ _S _I} :
  subG helpingΓ Γ → helpingGpreS.
Proof using. solve_inG. Qed.

Class helpingGS `{!crisG Γ Σ α β τ _S _I} := HelpingGS {
  #[local] helpingG :: helpingGpreS;
  help_name : gname;
}.

Section resource.
  Context `{!crisG Γ Σ α β τ _S _I, !helpingGS}.

  Definition Help (reqid : nat) (df : dfrac) (st : help_state) : iProp Σ :=
    own help_name
      (None, Some (gmap_view_frag
        (V := agreeR $ leibnizO _) reqid df (to_agree st))).

  Definition syn_Help n (reqid : nat) (df : dfrac) (st : help_state) : GTerm.t n :=
    sown help_name
      (None, Some (gmap_view_frag
        (V := agreeR $ leibnizO _) reqid df (to_agree st))).

  Global Instance SLRed_Help n reqid df st :
    SLRed n (syn_Help n reqid df st) (Help reqid df st).
  Proof. solve_sl_red. Qed.

  Definition HelpPend (reqid : nat) (N : option namespace) (arg : SAny.t) : iProp Σ :=
    Help reqid (DfracOwn 1) (Pend N arg).

  Definition syn_HelpPend n (reqid : nat) (N : option namespace) (arg : SAny.t) : GTerm.t n :=
    syn_Help n reqid (DfracOwn 1) (Pend N arg).

  Global Instance SLRed_HelpPend n reqid N arg :
    SLRed n (syn_HelpPend n reqid N arg) (HelpPend reqid N arg).
  Proof. solve_sl_red. Qed.

  Definition HelpDone (reqid : nat) (ret : SAny.t) : iProp Σ :=
    Help reqid DfracDiscarded (Done ret).

  Definition syn_HelpDone n (reqid : nat) (ret : SAny.t) : GTerm.t n :=
    syn_Help n reqid DfracDiscarded (Done ret).

  Global Instance SLRed_HelpDone n reqid ret :
    SLRed n (syn_HelpDone n reqid ret) (HelpDone reqid ret).
  Proof. solve_sl_red. Qed.

  Lemma Help_persist reqid q st :
    Help reqid (DfracOwn q) st ==∗ Help reqid DfracDiscarded st.
  Proof.
    rewrite /Help own_update; [iIntros "> $ //"|apply prod_update; [reflexivity|]].
    apply option_update, gmap_view_frag_persist.
  Qed.

  Global Instance HelpDone_persistent reqid ret : Persistent (HelpDone reqid ret).
  Proof. apply _. Qed.
End resource.
