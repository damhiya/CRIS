Require Import CRIS SchHeader.
Require Import HelpingHeader.

Set Implicit Arguments.

Module HelpingOff.
Section HelpingOff.
  Context `{Σ: GRA}.

  Definition scopes := [Helping.mn].

  Definition run: Any.t -> itree hmodE Any.t :=
    fun arg =>
      '(f,a): (string*SAny.t) <- arg↓?;;
      𝒴;;;
      trigger (Call f a↑);;;
      Ret ()↑.

  Definition help: Any.t -> itree hmodE Any.t :=
    fun _ =>
      𝒴;;;
      Ret ()↑.
      
  Definition fnsems :=
    [(Helping.run,  (scopes, mk_specbody fspec_trivial run));
     (Helping.help, (scopes, mk_specbody fspec_trivial help))].

  Program Definition Mod: SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t sp := Seal.sealing CRIS (SMod.to_hmod sp Mod).  
  
End HelpingOff.
End HelpingOff.
