Require Export Common.
Require Export SMod Mod.
Require Import ImpPrelude.

Module NDSHdr.
  Definition init := "NDS.init".
  Definition _spawn := "NDS._spawn".
  Definition spawn := "NDS.spawn".
  Definition yield := "NDS.yield".
  Definition yield_global := "NDS.yield_global".
  Definition join := "NDS.join".
  Definition get_tid := "NDS.get_tid".
End NDSHdr.

Definition NDS : string := "NDS".
Global Opaque NDS.

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

Module NDS. Section NDS.
  Import Events.

  Context `{E : Type → Type, coreE -< E, callE -< E}.

  Definition spawn (fnarg : string * SAny.t) : itree E nat :=
    'tid : nat <- ccallU NDSHdr.spawn fnarg;; Ret tid.

  Definition yield : itree E unit :=
    Seal.sealing NDS
     (iterC ((λ (_: unit),
        b <- trigger (Choose (option bool));;
        match b with
        | None => Ret (inr tt: () + ())
        | Some false => Ret (inl tt: () + ())
        | Some true => 
            trigger (Call NDSHdr.yield tt↑);;;
            Ret (inl tt: () + ())
        end)) tt).

  Definition terminate : itree E unit :=
    Seal.sealing NDS
      (iterC ((λ (_: unit),
        trigger (Call NDSHdr.yield tt↑);;;
        Ret (inl tt: () + ())
      )) tt).

  Definition join (tid : nat) : itree E SAny.t :=
    'ors: option SAny.t <- ccallU NDSHdr.join tid;;
    rs <- ors?;;
    Ret rs.
End NDS. End NDS.

Notation 𝒩𝒴 := (NDS.yield).
