Require Export CRIS.
Require Export SMod Mod.

Module SchHdr.
  Definition _spawn := mk_fnsig "Sch._spawn" (string * SAny.t) ().
  Definition spawn := mk_fnsig "Sch.spawn" (string * SAny.t) nat.
  Definition yield := mk_fnsig "Sch.yield" () ().
  Definition join := mk_fnsig "Sch.join" nat (option SAny.t).

  Definition exports : gset string :=
    {[ fn_name spawn; fn_name yield; fn_name join ]}.
End SchHdr.

Definition SCH : string := "sch".
Global Opaque SCH.

(* Wrapping fspecs *)
Section FSpec.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition sfunN XY `{coreE -< E} `{callE -< E} `{pgE -< E}
      (body : XY.1 -> itree E XY.2) : SAny.t -> itree E SAny.t :=
    λ varg, varg <- varg↓↓!;; vret <- body varg;; Ret vret↑↑.

  Definition sfunU XY `{coreE -< E} `{callE -< E} `{pgE -< E}
      (body : XY.1 -> itree E XY.2) : SAny.t -> itree E SAny.t :=
    λ varg, varg <- varg↓↓?;; vret <- body varg;; Ret vret↑↑.

  Definition interp_cond (s : {n & GTerm.t n}) :=
    match s with
    | existT n p => ⟦ p ⟧
    end.
End FSpec.

Module Sch. Section Sch.
  Context `{coreE -< E, callE -< E}.

  Definition spawn (fnarg : string * SAny.t) : itree E nat :=
    'tid : nat <- ccallU SchHdr.spawn fnarg;; Ret tid.

  Definition choose_optbool : itree E (option bool) := trigger (Choose (option bool)).

  Definition yield : itree E unit :=
    Seal.sealing SCH
     (iterC ((λ (_: unit),
        b <- choose_optbool;;
        match b with
        | None => Ret (inr tt: () + ())
        | Some false => Ret (inl tt: () + ())
        | Some true => 
            trigger (Call (fn_name SchHdr.yield) tt↑);;;
            Ret (inl tt: () + ())
        end)) tt).

  Definition terminate : itree E unit :=
    Seal.sealing SCH
      (iterC ((λ (_: unit),
        trigger (Call (fn_name SchHdr.yield) tt↑);;;
        Ret (inl tt: () + ())
      )) tt).

  Definition join (tid : nat) : itree E SAny.t :=
    ors <- ccallU SchHdr.join tid;; ors?.
End Sch. End Sch.

Notation 𝒴 := (Sch.yield).

Lemma yield_unfold `{coreE -< E, callE -< E} :
  @Sch.yield E _ _ =
  tau;; b <- trigger (Choose (option bool));;
  match b with
  | None => Ret tt
  | Some false => Sch.yield
  | Some true => trigger (Call (fn_name SchHdr.yield) tt↑);;; Sch.yield
  end.
Proof using.
  rewrite {1}/Sch.yield; unseal SCH; rewrite unfold_iterC.
  repeat f_equal. ired. repeat f_equal. extensionalities b. destruct b as [[|]|]; ss.
  { ired. f_equal. extensionalities x. rewrite /Sch.yield; unseal SCH; ss. }
  { ired. rewrite /Sch.yield; unseal SCH; ss. }
  { ired. done. }
Qed.

Definition yield_iter `{E : Type → Type, coreE -< E, callE -< E} {I R}
    (body : I → itree E (I + R)) (arg : I) : itree E R :=
  ret <- ITree.iter (λ arg : I, 𝒴;;; body arg) arg;; 𝒴;;; Ret ret.

Definition unfold_yield_iter `{E : Type → Type, coreE -< E, callE -< E} {I R}
    (body : I → itree E (I + R)) (arg : I) :
  yield_iter body arg =
  𝒴;;; ret <- body arg;;
  match ret with
  | inl i => tau;; yield_iter body i
  | inr ret => 𝒴;;; Ret ret
  end.
Proof.
  rewrite {1}/yield_iter unfold_iter_eq; etrans; first hnorm_itr; grind.
  case_match; etrans; try hnorm_itr; grind; rewrite /yield_iter /=.
Qed.
