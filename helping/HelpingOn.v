Require Import CRIS SchHeader.
From iris.algebra Require Import gmap_view.
From CRIS.helping Require Import Header.
From stdpp Require Import fin_sets.

(* Resource algebra for the helping module *)
(* Class helpingG `{!crisG Γ Σ α β τ _S _I} (jobID : Type) := {
  helping_tokG :: inG (gmap_viewR nat (agreeR (leibnizO jobID))) Γ
}.
Definition helpingΓ (jobID : Type) : HRA :=
  #[gmap_viewR nat (agreeR (leibnizO jobID))].
Global Instance subG_helpingΓ `{!crisG Γ Σ α β τ _S _I} (jobID : Type) :
  subG (helpingΓ jobID) Γ → helpingG jobID.
Proof. solve_inG. Defined.
Hint Unfold subG_helpingΓ : GRA_index.

Section resource.
  Context `{!crisG Γ Σ α β τ _S _I, !helpingG jobID}.

  Definition helping_tok (tid : nat) (jid : jobID) : iProp Σ :=
    own base_γ (gmap_view_frag (V:=agreeR $ leibnizO jobID) tid (DfracOwn 1) (to_agree jid)).
End resource. *)
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
  Context `{!crisG Γ Σ α β τ _S _I, !concG} {jobID : Type}.

  Context (mn : string).
  Context (jobcode : jobID → itree Helping.pureE unit).

  Definition scopes := [mn].
  Definition v_reqs := mn ↯ "reqs".

  Definition try_run (tid : nat) : itree crisE Any.t :=
    'reqs : gmap nat (bool * jobID) <- cgetU v_reqs;;
    match reqs !! tid with
    | Some (true, jid) =>
        cput v_reqs (<[tid := (false, jid)]> reqs);;;
        Helping.trans (jobcode jid);;;
        Ret ()↑
    | _ => Ret ()↑
    end.

  Definition run : Any.t → itree crisE Any.t :=
    λ arg,
      'jid : jobID <- arg↓?;;
      'reqs : gmap nat (bool * jobID) <- cgetU v_reqs;;
      let tid := fresh (dom reqs) in
      cput v_reqs (<[tid := (true, jid)]> reqs);;;
      𝒴;;; try_run tid;;; 𝒴;;; Ret ()↑.

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
    SMod.initial_st := [(v_reqs, (∅ : gmap nat (bool * jobID))↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t sp : Mod.t := Seal.sealing CRIS (SMod.to_mod sp (Mod sp)).
End HelpingOn. End HelpingOn.
