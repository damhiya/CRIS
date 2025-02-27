Require Export Common.
Require Export SMod HMod PMod.
Require Import ImpPrelude.

Module SchName.
  Definition _spawn := "Sch._spawn".
  Definition spawn := "Sch.spawn".
  Definition yield := "Sch.yield".
  Definition join := "Sch.join".
End SchName.

(* Wrapping fspecs *)
Section FSpec.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Notation iProp := (iProp Σ).

  Variable univ: positive.
  Variable StbFun: string → option fspec.

  Definition sfunN {X Y} `{coreE -< E} `{callE -< E} `{pgE -< E}
      (body : X -> itree E Y) : SAny.t -> itree E SAny.t :=
    λ varg, varg <- varg↓↓!;; vret <- body varg;; Ret vret↑↑.

  Definition sfunU {X Y} `{coreE -< E} `{callE -< E} `{pgE -< E}
      (body : X -> itree E Y) : SAny.t -> itree E SAny.t :=
    λ varg, varg <- varg↓↓?;; vret <- body varg;; Ret vret↑↑.

  Definition wfspec_type (A R : Type) (fsp : fspec) : fspec :=
    mk_fspec (meta := (fsp).(meta))
      (fun x varg arg =>
        ⌜∃ sarg: A, arg = sarg↑⌝ ∗ fsp.(precond) x varg arg)%I
      (fun x vret ret =>
        ⌜∃ sret: R, ret = sret↑⌝ ∗ fsp.(postcond) x vret ret)%I.

  Definition interp_cond (s : {n & SRFSyn.t n}) :=
    match s with
    | existT n p => ⟦ p ⟧
    end.

  (* Definition wfspec_thread: fspec → fspec := (wfspec_inv) ∘ (wfspec_type SAny.t SAny.t). *)

  Definition find_fsp (fn : string) : fspec :=
    match (StbFun fn) with
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
        'tid: nat <- ccallU SchName.spawn fnarg;;
        Ret tid).

  Definition yield : itree E unit :=
    Seal.sealing "Sch"
      (ITree.iter ((fun (_: unit) =>
        b <- trigger (Choose bool);;
        if b: bool
        then Ret (inr tt: () + ())
        else
          '():_ <- ccallU SchName.yield tt;;
          Ret (inl tt: () + ())
      )) tt).

  Definition terminate : itree E unit :=
    Seal.sealing "Sch"
      (ITree.iter ((fun (_: unit) =>
        '():_ <- ccallU SchName.yield tt;;
        Ret (inl tt: () + ())
      )) tt).

  Definition join (R : Type) : nat → itree E R :=
    Seal.sealing "Sch"
      (λ tid,
        'ora: option SAny.t <- ccallU SchName.join tid;;
        ra <- ora?;;
        rv <- (ra↓↓)?;;
        Ret rv).

  Definition spawnK {R} (fnarg : string * SAny.t) (k : nat → itree E R) : itree E R :=
    'tid : nat <- ccallU SchName.spawn fnarg;;
    k tid.

  Definition yieldK {R} (k : itree E R) : itree E R :=
    yield;;; k.

  Definition joinK {R R'} (tid : nat) (k : R → itree E R') : itree E R' :=
    'r : R <- join R tid;;
    k r.

  Lemma spawn_spawnK fnargs : spawn fnargs = spawnK fnargs (λ x, Ret x).
  Proof. rewrite /spawnK /spawn; unseal "Sch". ss. Qed.

  Lemma yield_yieldK : yield = yieldK (Ret tt).
  Proof.
    rewrite /yieldK. rewrite {1} (bind_ret_r_rev yield). f_equal; ss.
    extensionalities x; destruct x; ss.
  Qed.

  Lemma join_joinK R tid : join R tid = joinK tid (λ x, Ret x).
  Proof.
    rewrite /joinK /join; unseal "Sch". grind. rewrite {1}(bind_ret_r_rev (unwrapU _)).
    f_equal. extensionalities y; grind.
  Qed.
End Sch.
Section Sch.
  Context {Σ : GRA}.

  Definition yieldK_S {R} ginv stb (k : itree hmodE R) : itree hmodE R :=
    interp_smod ginv stb yield;;; k.

  Definition yieldK_S_SB {R} ginv stb scopes (k : itree hmodE R) : itree hmodE R :=
    HMod.sandbox scopes (interp_smod ginv stb yield);;; k.

  Lemma yieldK_bind {R R'} (k1 : itree hmodE R) (k2 : R → itree hmodE R') :
    yieldK k1 >>= k2 = yieldK (k1 >>= k2).
  Proof. rewrite /yieldK; grind. Qed.

  Lemma yieldK_S_SB_yield {R} ginv stb scopes (k : itree hmodE R) :
    yieldK_S_SB ginv stb scopes k = HMod.sandbox scopes (interp_smod ginv stb yield);;; k.
  Proof. ss. Qed.

  Lemma yieldK_interp_smod {R} ginv stb (k : itree hmodE R) :
    interp_smod ginv stb (yieldK k) = yieldK_S ginv stb (interp_smod ginv stb k).
  Proof. rewrite /yieldK /yieldK_S SModRed.interp_bind; ss. Qed.

  Lemma yieldK_S_transl {R} scopes ginv stb (k : itree hmodE R) :
    HMod.sandbox scopes (yieldK_S ginv stb k)
    = yieldK_S_SB ginv stb scopes (HMod.sandbox scopes k).
  Proof. rewrite /yieldK_S /yieldK_S_SB HModSB.transl_bind //. Qed.

  Definition spawnK_S {R} ginv stb fnargs (k : nat → itree hmodE R) : itree hmodE R :=
    x <- interp_smod ginv stb (spawn fnargs);; k x.

  Definition spawnK_S_SB {R} ginv stb scopes fnargs (k : nat → itree hmodE R) : itree hmodE R :=
    x <- HMod.sandbox scopes (interp_smod ginv stb (spawn fnargs));; k x.

  Lemma spawnK_bind {R R'}
      (fnarg : string * SAny.t) (k1 : nat → itree hmodE R) (k2 : R → itree hmodE R') :
    spawnK fnarg k1 >>= k2 = spawnK fnarg (λ n, (k1 n) >>= k2).
  Proof. rewrite /spawnK. grind. Qed.

  Lemma spawnK_S_SB_spawn {R} ginv stb scopes fnarg (k : nat → itree hmodE R) :
    spawnK_S_SB ginv stb scopes fnarg k
    = HMod.sandbox scopes (interp_smod ginv stb (spawn fnarg)) >>= k.
  Proof. ss. Qed.

  Lemma spawnK_interp_smod {R} ginv stb fnargs (k : nat → itree hmodE R) :
    interp_smod ginv stb (spawnK fnargs k)
    = spawnK_S ginv stb fnargs (λ x, interp_smod ginv stb (k x)).
  Proof. rewrite /spawnK_S /spawnK /spawn SModRed.interp_bind; unseal "Sch". grind. Qed.

  Lemma spawnK_S_transl {R} ginv stb scopes fnargs (k : nat → itree hmodE R) :
    HMod.sandbox scopes (spawnK_S ginv stb fnargs k)
    = spawnK_S_SB ginv stb scopes fnargs (λ x, HMod.sandbox scopes (k x)).
  Proof. rewrite /spawnK_S_SB /spawnK_S /spawn; unseal "Sch"; rewrite HModSB.transl_bind; ss. Qed.

  Definition joinK_S {R R'} ginv stb tid (k : R' → itree hmodE R) : itree hmodE R :=
    x <- interp_smod ginv stb (join R' tid);; k x.

  Definition joinK_S_SB {R R'} ginv stb scopes tid (k : R' → itree hmodE R) : itree hmodE R :=
    x <- HMod.sandbox scopes (interp_smod ginv stb (join R' tid));; k x.

  Lemma joinK_bind {R R1 R2} (tid : nat) (k1 : R → itree hmodE R1) (k2 : R1 → itree hmodE R2) :
    joinK tid k1 >>= k2 = joinK tid (λ x, k1 x >>= k2).
  Proof. rewrite /joinK; grind. Qed.

  Lemma joinK_S_SB_join {R R'} ginv stb scopes tid (k : R' → itree hmodE R) :
    joinK_S_SB ginv stb scopes tid k
    = HMod.sandbox scopes (interp_smod ginv stb (join R' tid)) >>= k.
  Proof. ss. Qed.

  Lemma joinK_interp_smod {R R'} ginv stb tid (k : R' → itree hmodE R) :
    interp_smod ginv stb (joinK tid k)
    = joinK_S ginv stb tid (λ x, interp_smod ginv stb (k x)).
  Proof. rewrite /joinK_S /joinK /join SModRed.interp_bind; unseal "Sch". grind. Qed.

  Lemma joinK_S_transl {R R'} ginv stb scopes tid (k : R' → itree hmodE R) :
    HMod.sandbox scopes (joinK_S ginv stb tid k)
    = joinK_S_SB ginv stb scopes tid (λ x, HMod.sandbox scopes (k x)).
  Proof. rewrite /joinK_S_SB /joinK_S /join; unseal "Sch"; rewrite HModSB.transl_bind; ss. Qed.
End Sch. End Sch.

Notation "x <- t1 ||; t2" := (ITree.bind t1 (fun x => (Sch.yield ;;; t2)))
  ( at level 62, t1 at next level, right associativity) : itree_scope.
Notation "t1 ||;; t2" := (ITree.bind t1 (fun _ => (Sch.yield ;;;t2)))
  (at level 62, right associativity) : itree_scope.
Notation "' p : T <- t1 ||; t2" :=
  (ITree.bind t1 (fun x_ : T => match x_ with p => (Sch.yield ;;; t2) end))
  (at level 62, T at next level, t1 at next level, p pattern, right associativity) : itree_scope.