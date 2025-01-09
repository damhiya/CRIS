(* Require Import CRIS.

Require Import CellioHeader.

Set Implicit Arguments.

Module CellioA. Section CellioA.
  Class G (Γ : HRA.t) := { #[local] RA_inG :: GRA.inG (excl_authR ZO) Γ}.
  Context `{!sinvG Σ Γ α β τ, !G Γ}.
  Local Notation iProp := (iProp Σ).

  Definition auth (v : Z) : iProp :=
    Seal.sealing "CellioA"
      (OwnM (●E v)).

  Definition cell (v : Z) : iProp :=
    Seal.sealing "CellioA"
      OwnM (◯E v).

  Lemma cell_auth_get v v':
    cell v' -∗ auth v -∗ ⌜v = v'⌝.
  Proof.
    rewrite /cell /auth; unseal "CellioA". 
    iIntros "P P'"; iCombine "P P'" as "P" gives %wf.
    by apply excl_auth_agree in wf.
  Qed.

  Lemma cell_auth_set v v':
    cell v -∗ auth v -∗ |==> cell v' ∗ auth v'.
  Proof.
    rewrite /cell /auth; unseal "CellioA".
    iIntros "C AU". iCombine "C AU" as "H".
    iMod (OwnM_Upd with "H") as "[C AU]"; last by (iModIntro; iSplitL "AU"). 
    rewrite comm; apply excl_auth_update.
  Qed.

  Definition set: Any.t -> itree hmodE Any.t :=
    λ _,
      x <- trigger (Take Z);;
      trigger (Assume (CellioA.cell x));;;
      i <- trigger (@IO _ Z "Input" tt);;
      trigger (Guarantee (CellioA.cell i));;;
      Ret tt↑.
  
  Definition get: Any.t -> itree hmodE Any.t :=
    λ _,
      x <- trigger (Take Z);;
      trigger (Assume (CellioA.cell x));;;
      trigger (Guarantee (CellioA.cell x));;;
      Ret x↑.

  Definition scopes := [CellioName.mn].
  
  Definition fnsems : alist string (list string * fspecbody) :=
    [(CellioName.set, (scopes, mk_specbody fspec_trivial set));
     (CellioName.get, (scopes, mk_specbody fspec_trivial get))].

  Program Definition Sem : SModSem.t := {|
    SModSem.scopes := scopes;
    SModSem.fnsems := fnsems;
    SModSem.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod : SMod.t := {|
    SMod.modsem := λ _, Sem;
    SMod.sk := CellioSK.t;
  |}.

  Definition InitCond : Sk.t -> iProp :=
    λ _, CellioA.auth 0.

  Variable ginv: Sk.t -> invspec.
  Variable GlobalStb: Sk.t -> string -> option fspec.
  Definition t := Seal.sealing "ccr" (SMod.to_hmod ginv GlobalStb Mod).
End CellioA. End CellioA. *)
