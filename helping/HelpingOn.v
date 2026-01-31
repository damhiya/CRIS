Require Import CRIS SchHeader.
Require Import SchI.
From iris.algebra Require Import gmap_view.
From CRIS.helping Require Import Header.
From stdpp Require Import fin_sets.

Section HoareCall.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.
  (* HoareCall Lemmas *)
  Definition fspec_option_meta (fspo : option fspec_rel) : Type :=
    match fspo with
    | Some fsp => FSpec fsp
    | None => unit
    end.

  Definition HoareCall_prologue fspo (varg : Any.t)
      : itree crisE (fspec_option_meta fspo * Any.t) :=
    (match fspo as fspo return itree crisE (fspec_option_meta fspo * Any.t) with
    | Some fsp =>
        PQ <- trigger (Choose (FSpec fsp));;
        arg <- trigger (Choose Any.t);;
        trigger (Guarantee ((Precond PQ) varg arg));;;
        Ret (PQ, arg)
    | None => Ret (tt, varg)
    end).

  Definition HoareCall_epilogue fspo (x : fspec_option_meta fspo) (pret : Any.t)
      : itree crisE Any.t :=
    (match fspo as fspo return fspec_option_meta fspo → itree crisE Any.t with
    | Some fsp =>
        λ x,
          vret <- trigger (Take Any.t);;
          trigger (Assume ((Postcond x) vret pret));;;
          Ret vret
    | None => λ _, Ret pret
    end) x.

  Lemma HoareCall_unfold (sp : specmap) (fn : string) :
    SModTr.HoareCall (sp !! speckey_fn fn) fn ()↑ =
    xarg <- HoareCall_prologue (sp !! speckey_fn fn) (()↑);;
    ret <- trigger (Call fn xarg.2);;
    HoareCall_epilogue (sp !! speckey_fn fn) xarg.1 ret.
  Proof using.
    rewrite /SModTr.HoareCall /HoareCall_prologue /HoareCall_epilogue; case_match; grind.
  Qed.

  Definition HoareFun_prologue fspo parg : itree crisE (fspec_option_meta fspo * Any.t) :=
    (match fspo as fspo return itree crisE (fspec_option_meta fspo * Any.t) with
    | Some fsp =>
        PQ <- trigger (Take (FSpec fsp));;
        varg <- trigger (Take Any.t);;
        trigger (Assume ((Postcond PQ) varg parg));;;
        Ret (PQ, varg)
    | None => Ret (tt, parg)
    end).

  Definition HoareFun_epilogue fspo (x : fspec_option_meta fspo) (vret : Any.t)
      : itree crisE Any.t :=
    (match fspo as fspo return fspec_option_meta fspo → itree crisE Any.t with
    | Some fsp =>
        λ x,
          pret <- trigger (Choose Any.t);;
          trigger (Guarantee ((Precond x) vret pret));;;
          Ret pret
    | None => λ _, Ret vret
    end) x.
End HoareCall.

(* Helping module *)
Module HelpingOn. Section HelpingOn.
  Context `{!crisG Γ Σ α β τ _S _I, !concG} {jobID retID : Type}.

  Context (mn : string).
  Context (jobcode : jobID → itree crisE retID).

  Definition scopes : gmultiset string := {[+mn+]}.
  Definition v_reqs : key := (mn, "reqs").

  Definition msk_pure : emask := λ X e,
    match e with
    | inl1 _ => true
    | inr1 (inl1 _) => false
    | inr1 (inr1 (inl1 _)) => false
    | inr1 (inr1 (inr1 _)) => true
    end.

  Definition try_run (tid : nat) : itree crisE retID :=
    'reqs : gmap nat (option retID * jobID) <- cgetU v_reqs;;
    match reqs !! tid with
    | Some (None, jid) =>
        r <- SB.sandbox msk_pure (jobcode jid);;
        cput v_reqs (<[tid := (Some r, jid)]> reqs);;;
        Ret r
    | Some (Some retid, jid) => Ret retid
    | None => triggerNB
    end.

  Definition run : Any.t → itree crisE Any.t :=
    λ arg,
      'jid : jobID <- arg↓?;;
      'reqs : gmap nat (option retID * jobID) <- cgetU v_reqs;;
      let tid := fresh (dom reqs) in
      cput v_reqs (<[tid := (None, jid)]> reqs);;;
      𝒴;;; r <- try_run tid;; 𝒴;;; Ret (r↑).

  Definition help (sp : specmap) : Any.t → itree crisE Any.t :=
    λ _,
      tid <- trigger (Choose nat);;
      xarg <- HoareCall_prologue (sp !! speckey_fn SchHdr.yield) (() ↑);;
      x <- HoareFun_prologue (sp !! speckey_fn SchHdr.yield) (() ↑);;
      try_run tid;;;
      HoareFun_epilogue (sp !! speckey_fn SchHdr.yield) x.1 (() ↑);;;
      HoareCall_epilogue (sp !! speckey_fn SchHdr.yield) xarg.1 (() ↑);;;
      Ret ()↑.

  Definition fnsems (sp : specmap) : fnsemmap :=
    {[Some (Helping.run mn) := Some (msk_scp scopes msk_true, (None, run));
      Some (Helping.help mn) := Some (msk_scp scopes msk_true, (None, help sp))]}.

  Program Definition Mod (sp : specmap) : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems sp;
    SMod.initial_st := {[v_reqs := Some (∅ : gmap nat (option retID * jobID))↑]};
  |}.
  Solve All Obligations with mod_tac.

  (* Definition sp (sp : specmap) : specmap := 
    match sp !! speckey_fn SchHdr.yield with
    | Some fsp => <[speckey_fn (Helping.yield mn) := fsp]> sp
    | None => ∅
    end.
  Lemma sp_helping_yield sp1 :
    (sp sp1) !! speckey_fn SchHdr.yield = sp1 !! speckey_fn SchHdr.yield.
  Proof. rewrite /sp; destruct (sp1 !! _) eqn : ?; ss; rewrite lookup_insert_ne; ss. Qed.

  Lemma sp_yield sp1 :
    (sp sp1) !! speckey_fn (Helping.yield mn) = sp1 !! speckey_fn SchHdr.yield.
  Proof. rewrite /sp; destruct (sp1 !! _) eqn : ?; ss; rewrite lookup_insert; ss. Qed. *)

  Definition t sp : Mod.t := SMod.to_mod sp (Mod sp).
End HelpingOn. End HelpingOn.

Module HelpingDummy. Section HelpingDummy.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.
  Context (mn : string).
  Definition scopes : gmultiset string := {[+mn+]}.

  Definition fnsems : fnsemmap :=
    {[Some (Helping.run mn) := Some (msk_scp scopes msk_true, (None, λ _, triggerNB));
      Some (Helping.help mn) := Some (msk_scp scopes msk_true, (None, λ _, triggerNB))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ Mod.
End HelpingDummy. End HelpingDummy.