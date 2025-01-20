Require Import CRIS.
Require Import CellioHeader InputHeader.

Set Implicit Arguments.

Local Definition RA : ucmra :=
  authUR (optionUR (exclR ZO)).
Class CellioAGΓ (Γ : HRA) := {
  #[local] RA_inG :: inG RA Γ;
}.
Definition CellioAΓ : HRA := #[RA].
Global Instance subG_GΓ {Γ : HRA} : subG CellioAΓ Γ → CellioAGΓ Γ.
Proof. solve_inG. Qed.

Module CellioA. Section CellioA.
  Context `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ, !CellioAGΓ Γ}.

  Definition auth (v : Z) : iProp Σ :=
    own base_γ (●E v).

  Definition cell (v : Z) : iProp Σ :=
    own base_γ (◯E v).

  Lemma cell_auth_get v v':
    cell v -∗ auth v' -∗ ⌜v = v'⌝.
  Proof.
    rewrite /cell /auth.
    iIntros "P P'"; iCombine "P P'" as "P" gives %wf.
    by apply excl_auth_agree in wf.
  Qed.

  Lemma cell_auth_set v v':
    cell v -∗ auth v ==∗ cell v' ∗ auth v'.
  Proof.
    rewrite /cell /auth.
    iIntros "C AU". iCombine "C AU" as "H".
    iMod (own_update with "H") as "[C AU]"; last by (iModIntro; iSplitL "AU"). 
    rewrite comm; apply excl_auth_update.
  Qed.

  Definition set: Any.t -> itree hmodE Any.t :=
    λ _,
      x <- trigger (Take Z);;
      trigger (Assume (CellioA.cell x));;;
      (* i <- trigger (@IO _ Z "Input" tt);; *)
      'i: Z <- ccallU InputName.input tt;;
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

  Definition InitCond : Sk.t -> iProp Σ :=
    λ _, CellioA.auth 0.

  Variable ginv: Sk.t -> invspec.
  Variable GlobalStb: Sk.t -> string -> option fspec.
  Definition t := Seal.sealing CRIS (SMod.to_hmod ginv GlobalStb Mod).
End CellioA. End CellioA.
