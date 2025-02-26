Require Import CRIS.
Require Import Imp.
Require Import ImpPrelude.
Require Import RepeatHeader.
Require Import APCHeader APC.

Set Implicit Arguments.

(* Define Specification *)
Module RepeatAS. Section RepeatAS.

  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Notation iProp := (iProp Σ).

  Variable genv: GEnv.t.
  Variable SpcPure: string → option fspec.

  (* mathematical repeat *)
  Fixpoint repeat_fun A (f: A → A) (n: nat) (a: A): A :=
    match n with
    | 0 => a
    | S n' => repeat_fun f n' (f a)
    end.

  Definition repeat_spec (genv: GEnv.t) : fspec :=
    fspec_apc (λ '(n, x, f_sem), OrdArith.add Ord.omega (n:nat)%ord)
      (λ '(n, x, f_sem),
        ((λ arg, ⌜∃ (fn:string) (fptr:mblock), arg = [Vptr fptr 0; Vint (Z.of_nat n); Vint x]↑
                        ∧ (intrange_64 (Z.of_nat n))
                        ∧ CEnv.blk2id (CEnv.load_genv genv) fptr = Some fn
                        ∧ fn_has_spec SpcPure fn
                            (fspec_apc
                              (λ _, Ord.omega)
                              (λ x, 
                                ((λ varg, ⌜varg = [Vint x]↑⌝%I),
                                (λ vret, ⌜vret = (Vint (f_sem x))↑⌝%I))
                              )
                            )
                      ⌝%I),
          (λ ret, ⌜ret = (Vint (repeat_fun f_sem n x))↑⌝%I))).

  Definition Spc: alist string fspec :=
    Seal.sealing CRIS [(RepeatName.repeat, repeat_spec genv)].

  Lemma Spc_nodup : List.NoDup (List.map fst Spc).
  Proof. by rewrite /Spc; unseal CRIS; prove_nodup. Qed.

End RepeatAS. End RepeatAS.

(* Define Module *)
Module RepeatA. Section RepeatA.

  Definition scopes := [RepeatName.mn].

  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.

  Definition fnsems genv SpcPure :=
    [(RepeatName.repeat, (scopes, mk_specbody (RepeatAS.repeat_spec SpcPure genv) pure_body))].

  Program Definition Mod genv SpcPure : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems genv SpcPure;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition InitCond : iProp Σ := emp%I.

  Definition t genv u Spc SpcPure := Seal.sealing CRIS (SMod.to_hmod (wsim_ginv u ⊤) Spc (Mod genv SpcPure)).
End RepeatA. End RepeatA.
