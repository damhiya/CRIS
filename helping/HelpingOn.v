Require Import CRIS SchHeader.
From iris.algebra Require Import gmap_view.
From CRIS.helping Require Import Header.
From stdpp Require Import fin_sets.

Section HoareCall.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.

  Definition fspec_option_meta (fspo : option fspec) : Type :=
    match fspo with
    | Some fsp => meta fsp
    | None => unit
    end.

  Definition HoareCall_prologue fspo varg : itree crisE (fspec_option_meta fspo * Any.t) :=
    Seal.sealing "Help"
    (match fspo as fspo return itree crisE (fspec_option_meta fspo * Any.t) with
    | Some (@fspec_call _ meta pre post) =>
        x <- trigger (Choose meta);;
        arg <- trigger (Choose Any.t);;
        trigger (Guarantee (pre x varg arg));;;
        Ret (x, arg)
    | Some _ => triggerNB
    | None => Ret (tt, varg)
    end).

  Definition HoareCall_epilogue fspo (x : fspec_option_meta fspo) (pret : Any.t)
      : itree crisE Any.t :=
    Seal.sealing "Help"
    (match fspo as fspo return fspec_option_meta fspo → itree crisE Any.t with
    | Some (@fspec_call _ meta pre post) =>
        λ x,
          vret <- trigger (Take Any.t);;
          trigger (Assume (post x vret pret));;;
          Ret vret
    | Some _ => λ _, triggerNB
    | None => λ _, Ret pret
    end) x.

  Lemma HoareCall_unfold fspo :
    SModTr.HoareCall SchHdr.yield (()↑) fspo =
    xarg <- HoareCall_prologue fspo (()↑);;
    ret <- trigger (Call SchHdr.yield xarg.2);;
    HoareCall_epilogue fspo xarg.1 ret.
  Proof.
    rewrite /SModTr.HoareCall /HoareCall_prologue /HoareCall_epilogue; unseal "Help".
    destruct fspo as [[|]|]; ss.
    { ired. f_equal. extensionalities x. ired. f_equal. extensionalities arg. ired. f_equal.
      extensionalities t. f_equal. extensionalities a. unseal "Help". done. }
    { ired. f_equal. extensionalities; ss. }
    { ired. erewrite <-bind_ret_r at 1. f_equal. extensionalities a. unseal "Help". done. }
  Qed.

  Definition HoareFun_prologue fspo parg : itree crisE (fspec_option_meta fspo * Any.t) :=
    Seal.sealing "Help"
    (match fspo as fspo return itree crisE (fspec_option_meta fspo * Any.t) with
    | Some (@fspec_call _ meta pre post) =>
        x <- trigger (Take meta);;
        varg <- trigger (Take Any.t);;
        trigger (Assume (post x varg parg));;;
        Ret (x, varg)
    | Some _ => triggerNB
    | None => Ret (tt, parg)
    end).

  Definition HoareFun_epilogue fspo (x : fspec_option_meta fspo) (vret : Any.t)
      : itree crisE Any.t :=
    Seal.sealing "Help"
    (match fspo as fspo return fspec_option_meta fspo → itree crisE Any.t with
    | Some (@fspec_call _ meta pre post) =>
        λ x,
          pret <- trigger (Choose Any.t);;
          trigger (Guarantee (pre x vret pret));;;
          Ret pret
    | Some _ => λ _, triggerNB
    | None => λ _, Ret vret
    end) x.
End HoareCall.

(* Helping module *)
Module HelpingOn. Section HelpingOn.
  Context `{!crisG Γ Σ α β τ _S _I, !concG} {jobID retID : Type}.

  Context (mn : string).
  Context (jobcode : jobID → itree Helping.pureE retID).

  Definition scopes := [mn].
  Definition v_reqs := mn ↯ "reqs".

  Definition try_run (tid : nat) : itree crisE retID :=
    'reqs : gmap nat (option retID * jobID) <- cgetU v_reqs;;
    match reqs !! tid with
    | Some (None, jid) =>
        r <- Helping.trans (jobcode jid);;
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

  Definition help (sp : sp_type) : Any.t → itree crisE Any.t :=
    λ _,
      tid <- trigger (Choose nat);;
      xarg <- HoareCall_prologue (sp SchHdr.yield) (() ↑);;
      x <- HoareFun_prologue (sp SchHdr.yield) (() ↑);;
      try_run tid;;;
      HoareFun_epilogue (sp SchHdr.yield) x.1 (() ↑);;;
      HoareCall_epilogue (sp SchHdr.yield) xarg.1 (() ↑);;;
      Ret ()↑.

  Definition fnsems (sp : sp_type) : alist (option string) (fnsem_type (option fspec * fbody)) :=
    [(Some (Helping.run mn),  (true, wmask_all, scopes, (None, run)));
     (Some (Helping.help mn), (true, wmask_all, scopes, (None, help sp)))].

  Program Definition Mod (sp : sp_type) : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems sp;
    SMod.initial_st := [(v_reqs, (∅ : gmap nat (option retID * jobID))↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t sp : Mod.t := Seal.sealing CRIS (SMod.to_mod sp (Mod sp)).
End HelpingOn. End HelpingOn.
  