Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader CannonMainI CannonA CannonHeader.

Set Implicit Arguments.

Module MainAS. Section MainAS.
  Import CannonAS.
  Context `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ, !CannonAGΓ Γ}.
  Local Existing Instance cannon_inG.
  Definition init_res : Σ := own.iRes_singleton 1%positive (◯E tt).

  Definition main_spec : fspec :=
    fspec_simple (λ _ : unit,
      ((λ arg, ⌜arg = tt↑⌝ ∗ Ball),
      (λ ret, ⌜ret = tt↑⌝))
    )%I.

  Definition Stb : alist string fspec :=
    Seal.sealing CRIS [(MainName.main, main_spec)].

  Lemma Stb_nodup: List.NoDup (List.map fst Stb).
  Proof. unfold Stb. unseal CRIS. prove_nodup. Qed.
End MainAS. End MainAS.

Module MainA. Section MainA.
  Import CannonAS.
  Context `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ, !CannonAGΓ Γ}.

  Variable num_fire : nat.

  Definition scopes := ["Main"].

  Fixpoint main_repeat (n : nat) : itree hmodE unit :=
    match n with
    | 0 => Ret tt
    | S n' =>
      'r : Z <- ccallU CannonName.fire ([] : list val);;
      _ <- trigger (@IO _ void "print" [r]↑);;
      main_repeat n'
    end.

  Definition main : list val → itree hmodE unit :=
    λ _, main_repeat num_fire.

  Definition fnsems :=
    [(MainName.main, (scopes, mk_specbody MainAS.main_spec (cfunU main)))].

  Program Definition Sem : SModSem.t := {|
    SModSem.scopes := scopes;
    SModSem.fnsems := fnsems;
    SModSem.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod : SMod.t := {|
    SMod.modsem := λ _, Sem;
    SMod.sk := MainSK.t;
  |}.

  Definition init_cond : Sk.t → iProp Σ := λ _, True%I.

  Definition t ginv Stb := Seal.sealing CRIS (SMod.to_hmod ginv Stb Mod).
End MainA. End MainA.
