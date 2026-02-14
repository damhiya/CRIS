Require Export CRIS.
Require Export SMod Mod.
Require Import ImpPrelude.

Module SchHdr.
  Definition _spawn := "Sch._spawn".
  Definition spawn := "Sch.spawn".
  Definition yield := "Sch.yield".
  Definition join := "Sch.join".
  Definition get_tid := "Sch.get_tid".
End SchHdr.

Definition SCH : string := "sch".
Global Opaque SCH.

(* Wrapping fspecs *)
Section FSpec.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition sfunN {X Y} `{coreE -< E} `{callE -< E} `{pgE -< E}
      (body : X -> itree E Y) : SAny.t -> itree E SAny.t :=
    λ varg, varg <- varg↓↓!;; vret <- body varg;; Ret vret↑↑.

  Definition sfunU {X Y} `{coreE -< E} `{callE -< E} `{pgE -< E}
      (body : X -> itree E Y) : SAny.t -> itree E SAny.t :=
    λ varg, varg <- varg↓↓?;; vret <- body varg;; Ret vret↑↑.

  Definition interp_cond (s : {n & GTerm.t n}) :=
    match s with
    | existT n p => ⟦ p ⟧
    end.
End FSpec.

Module Sch. Section Sch.
  Context `{E : Type → Type, coreE -< E, callE -< E}.

  Definition spawn (fnarg : string * SAny.t) : itree E nat :=
    'tid : nat <- ccallU SchHdr.spawn fnarg;; Ret tid.

  Definition yield : itree E unit :=
    Seal.sealing SCH
     (iterC ((λ (_: unit),
        b <- trigger (Choose (option bool));;
        match b with
        | None => Ret (inr tt: () + ())
        | Some false => Ret (inl tt: () + ())
        | Some true => 
            trigger (Call SchHdr.yield tt↑);;;
            Ret (inl tt: () + ())
        end)) tt).

  Definition terminate : itree E unit :=
    Seal.sealing SCH
      (iterC ((λ (_: unit),
        trigger (Call SchHdr.yield tt↑);;;
        Ret (inl tt: () + ())
      )) tt).

  Definition join (tid : nat) : itree E SAny.t :=
    ors <- ccallU SchHdr.join tid;; ors?.
End Sch. End Sch.

Notation 𝒴 := (Sch.yield).

Lemma yield_unfold `{E : Type → Type, coreE -< E, callE -< E} :
  @Sch.yield E _ _ =
  tau;; b <- trigger (Choose (option bool));;
  match b with
  | None => Ret tt
  | Some false => Sch.yield
  | Some true => trigger (Call SchHdr.yield tt↑);;; Sch.yield
  end.
Proof using.
  rewrite {1}/Sch.yield; unseal SCH; rewrite unfold_iterC.
  repeat f_equal. ired. repeat f_equal. extensionalities b. destruct b as [[|]|]; ss.
  { ired. f_equal. extensionalities x. rewrite /Sch.yield; unseal SCH; ss. }
  { ired. rewrite /Sch.yield; unseal SCH; ss. }
  { ired. done. }
Qed.

Definition atomic_body `{Σ : GRA}
    (fsp : fspec)
    (body : meta fsp → Any.t → itree crisE Any.t)
    : Any.t → itree crisE Any.t :=
  λ arg,
    x <- trigger (Take (meta fsp));;
    trigger (Assume (precond fsp x arg arg));;;
    𝒴;;; ret <- body x arg;; 𝒴;;;
    trigger (Guarantee (postcond fsp x ret ret));;;
    Ret ret.
