Require Export Common.
Require Export SMod HMod PMod.
Require Import ImpPrelude.

Module SchHdr.
  Definition _spawn := "Sch._spawn".
  Definition spawn := "Sch.spawn".
  Definition yield := "Sch.yield".
  Definition join := "Sch.join".
  Definition get_tid := "Sch.get_tid".
End SchHdr.

(* Wrapping fspecs *)
Section FSpec.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.

  Variable univ: positive.
  Variable SpFun: string → option fspec.

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

  (* Definition wfspec_thread: fspec → fspec := (wfspec_inv) ∘ (wfspec_type SAny.t SAny.t). *)

  Definition find_fsp (fn : string) : fspec :=
    match (SpFun fn) with
    | Some fsp => fsp
    | None => fspec_trivial
    end.
End FSpec.

Module Sch. Section Sch.
  Import Events.

  Context {E : Type → Type}.
  Context `{coreE -< E, callE -< E}.

  Definition spawn : (string * SAny.t) → itree E nat :=
    Seal.sealing "Sch"
      (λ fnarg,
        'tid: nat <- ccallU SchHdr.spawn fnarg;;
        Ret tid).

  Definition yield : itree E unit :=
    Seal.sealing "Sch"
      (ITree.iter ((fun (_: unit) =>
        b <- trigger (Choose bool);;
        if b: bool
        then Ret (inr tt: () + ())
        else
          '():_ <- ccallU SchHdr.yield tt;;
          Ret (inl tt: () + ())
      )) tt).

  Definition terminate : itree E unit :=
    Seal.sealing "Sch"
      (ITree.iter ((fun (_: unit) =>
        '():_ <- ccallU SchHdr.yield tt;;
        Ret (inl tt: () + ())
      )) tt).

  Definition join : nat → itree E SAny.t :=
    Seal.sealing "Sch"
      (λ tid,
        'ors: option SAny.t <- ccallU SchHdr.join tid;;
        rs <- ors?;;
        Ret rs).
End Sch. End Sch.

Notation 𝒴 := (Sch.yield).
(* Notation "x <- t1 ;;𝒴 t2" := (ITree.bind t1 (fun x => (Sch.yield ;;; t2)))
  ( at level 62, t1 at next level, right associativity) : itree_scope.
Notation "t1 ;;;𝒴 t2" := (ITree.bind t1 (fun _ => (Sch.yield ;;;t2)))
  (at level 62, right associativity) : itree_scope.
Notation "' p : T <- t1 ;;𝒴 t2" :=
  (ITree.bind t1 (fun x_ : T => match x_ with p => (Sch.yield ;;; t2) end))
  (at level 62, T at next level, t1 at next level, p pattern, right associativity) : itree_scope. *)
