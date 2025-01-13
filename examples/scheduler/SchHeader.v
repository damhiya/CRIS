Require Import CRIS.
Require Import ImpPrelude.

Module SchName.

Definition _spawn := "Sch._spawn".
Definition spawn := "Sch.spawn".
Definition yield := "Sch.yield".
Definition join := "Sch.join".

End SchName.

Module SchSK.
  Definition t : Sk.t := 
    [(SchName._spawn, Gfun↑);
     (SchName.spawn, Gfun↑);
     (SchName.yield, Gfun↑);
     (SchName.join, Gfun↑)].
End SchSK.

(* Wrapping fspecs *)
Section FSpec.
  Context `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ}.
  Notation iProp := (iProp Σ).

  Variable univ: positive.

  (* fspec wrapping functions - TODO: move them to a proper file *)
  Definition wfspec_inv (univ : positive) (fsp : fspec) : fspec :=
    mk_fspec (meta := (fsp).(meta))
      (fun tid x varg arg =>
        (∃ n, wsats univ n ⊤) ∗ fsp.(precond) tid x varg arg)%I
      (fun tid x vret ret =>
        (∃ n, wsats univ n ⊤) ∗ fsp.(postcond) tid x vret ret)%I.

  Definition wfspec_type (A R : Type) (fsp : fspec) : fspec :=
    mk_fspec (meta := (fsp).(meta))
      (fun tid x varg arg =>
        ⌜∃ sarg: A, arg = sarg↑⌝ ∗ fsp.(precond) tid x varg arg)%I
      (fun tid x vret ret =>
        ⌜∃ sret: R, ret = sret↑⌝ ∗ fsp.(postcond) tid x vret ret)%I.

  Definition interp_cond (s : {n & SRFSyn.t n}) :=
    match s with
    | existT n p => ⟦ p ⟧
    end.

  Definition wfspec_thread: fspec → fspec := (wfspec_inv univ) ∘ (wfspec_type SAny.t SAny.t).

  Definition find_fsp (sk: Sk.t) (StbFun: Sk.t -> gname -> option fspec) (fn : gname) : fspec :=
    match (StbFun sk fn) with
    | Some fsp => fsp
    | None => fspec_trivial
    end.
End FSpec.

Module Sch.
  Definition spawn {E} `{coreE -< E} `{Events.callE -< E}: (gname * SAny.t) → itree E nat :=
    Seal.sealing "Sch"
      (λ fnarg,
        'tid: nat <- ccallU SchName.spawn fnarg;;
        Ret tid)
  .

  Definition yield {E} `{coreE -< E} `{Events.callE -< E}: itree E unit :=
    Seal.sealing "Sch"
      (ITree.iter ((fun (_: unit) =>
        b <- trigger (Choose bool);;
        if b: bool
        then Ret (inr tt: () + ())
        else
          '():_ <- ccallU SchName.yield tt;;
          Ret (inl tt: () + ())
      )) tt)
  .

  Definition terminate {E} `{coreE -< E, Events.callE -< E}: itree E unit :=
    Seal.sealing "Sch"
      (ITree.iter ((fun (_: unit) =>
        '():_ <- ccallU SchName.yield tt;;
        Ret (inl tt: () + ())
      )) tt)
  .

  Definition join {E} `{coreE -< E, Events.callE -< E} (R: Type): nat → itree E R :=
    Seal.sealing "Sch"
      (λ tid,
        'ora: option SAny.t <- ccallU SchName.join tid;;
        ra <- ora?;;
        rv <- (ra↓↓)?;;
        Ret rv)
  .
End Sch.
