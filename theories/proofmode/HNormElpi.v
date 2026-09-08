From elpi Require Import elpi.
From CRIS.common Require Import Common.
From CRIS.proofmode Require Import HNormClasses HNorm HNormInstances.
From CRIS.proofmode Require Export HNormElpiRules.

(** Experimental, opt-in implementation; [hnorm_itr] remains unchanged.

    Each HNorm class has a native Elpi predicate.  Registration compiles
    instance conclusions and premises to clauses of those predicates.
    Normalization builds an equality proof entirely in Elpi, with one final
    refinement, instead of opening Rocq goals for each context/reduction.

    Rule application is structural, up to alpha equivalence.  Rocq is used
    for the explicit [simpl] stage and final proof checking, not conversion
    during rule search.  Itree rules are applied only at the head.

    Register later instances with:
      Elpi HNormElpi.Register HNormExpand HNormReduce.
    A lemma with an HNorm conclusion can also be registered by name.
    [Hint Extern] tactics are not translated.
    Other class premises must be determined by inputs or supplied locally.

    See HNormElpiTests.v and HNormElpiBench.v for tests and timings. *)
Module HNormElpi.
  (* [simpl] preserves the type.  The assembled equality proof is checked
     below, so there is no need to check this intermediate term again. *)
  Ltac simplify_term X := let Y := eval simpl in X in exact_no_check Y.

  Lemma context_eq {A B} x (K : B -> A) v
      (H : HNormContext x K v) v' rhs :
    v = v' -> K v' = rhs -> x = rhs.
  Proof. intros EQ EQ'. destruct H as [->]. rewrite EQ. exact EQ'. Qed.

  Lemma context_cong {A B} (K : B -> A) v v' rhs :
    v = v' -> K v' = rhs -> K v = rhs.
  Proof. intros -> EQ. exact EQ. Qed.
End HNormElpi.

Elpi Tactic hnorm_itr_elpi.
Elpi Accumulate Db hnorm.elpi.db.
Elpi Accumulate lp:{{
  pred hn-goal-context o:goal-ctx.
  pred hn-stable-context o:bool.

  pred hn-reflexive i:term.
  hn-reflexive {{ @eq_refl lp:_A lp:_X }}.

  % Structural children of a simplified term are already simplified.
  % Inputs/contexts containing unification variables are not cached.
  kind hn-input type.
  type hn-clean hn-input.
  type hn-dirty hn-input.

  pred hn-child i:hn-input, i:term, i:term, o:hn-input.
  hn-child hn-clean X V hn-clean :-
    coq.safe-dest-app X _ Args,
    std.mem Args Candidate, same_term Candidate V, !.

  % Preserve Rocq's simplification directives without reopening the caller's
  % proof goals.  The synthetic goal only returns the simplified term.
  pred hn-simpl i:term, i:term, o:term.
  hn-simpl A X Y :-
    hn-goal-context Ctx,
    declare-evar Ctx Raw A Y,
    coq.unify-eq Y Y ok,
    coq.ltac.call-simple-ltac1 "HNormElpi.simplify_term"
      (goal Ctx Raw A Y [trm X]) [] ok.

  pred hn-normalize i:term, i:term, o:term, o:term.
  hn-normalize A X Y Proof :-
    hn-simpl A X S,
    if (hn-stable-context tt, ground_term S)
      (Ready = hn-clean) (Ready = hn-dirty),
    hn-step A S Ready Y Proof.

  pred hn-step i:term, i:term, i:hn-input, o:term, o:term.
  % Leave certificate-determined proof arguments for final type inference.
  % Repeating them here copies growing subterms at every recursive step.
  % This does not affect matching, and final refinement checks every hole.
  hn-step A X Ready Y Proof :-
    if (hn-expand X _ E EP)
      (hn-descend A E hn-dirty Y DP,
       Proof = {{ @HNormExpand_apply _ _ _ lp:EP _ lp:DP }})
      (hn-descend A X Ready Y Proof).

  pred hn-descend i:term, i:term, i:hn-input, o:term, o:term.
  hn-descend A X Ready Y Proof :-
    if (hn-context X _ B K V CP)
      (if (hn-child Ready X V ChildReady)
         (hn-step B V ChildReady W IP)
         (hn-normalize B V W IP),
       hn-contract B A K W Y OP,
       % Most contexts are definitional.  Avoid duplicating their input and
       % certificate in the proof; retain the general case for local rules.
       coq.mk-app K [V] KV0,
       hd-beta-zeta-reduce KV0 KV,
       if (X == KV)
         (if (hn-reflexive IP)
            (Proof = OP)
            (Proof = {{ @HNormElpi.context_cong lp:A lp:B lp:K _
                          _ _ lp:IP lp:OP }}))
         (Proof =
           {{ @HNormElpi.context_eq lp:A lp:B _ lp:K _ lp:CP
                _ _ lp:IP lp:OP }}))
      (Y = X, Proof = {{ @eq_refl lp:A lp:X }}).

  pred hn-contract i:term, i:term, i:term, i:term, o:term, o:term.
  hn-contract _A B K X Y Proof :-
    if (hn-reduce K X _ _ Z Continue RP)
      (R = {{ @HNormReduce_equal _ _ _ _ _ _ lp:RP }},
       if (Continue = {{ true }})
         (hn-normalize B Z Y NP,
          if (hn-reflexive NP)
            (Proof = R)
            (Proof = {{ @eq_trans lp:B _ _ _ lp:R lp:NP }}))
         (Y = Z, Proof = R))
      (coq.mk-app K [X] Y, Proof = {{ @eq_refl lp:B lp:Y }}).

  pred hn-finalize i:term, i:term, o:term, o:term.
  hn-finalize A X Y Proof :-
    if (hn-finish X _ Y FP)
      (Proof = {{ @HNormFinish_equal _ _ _ lp:FP }})
      (Y = X, Proof = {{ @eq_refl lp:A lp:X }}).

  pred hn-run i:goal, o:list sealed-goal.
  hn-run (goal Ctx _ {{ @eq lp:A lp:X _ }} _ _ as G) GS :-
    if (ground_term Ctx) (Stable = tt) (Stable = ff),
    hn-stable-context Stable ==>
    hn-goal-context Ctx ==>
    hn-load-context Ctx LocalRules,
    LocalRules ==>
    @no-tc! ==>
    hn-normalize A X H HP,
    hn-finalize A H _Y FP,
    if (hn-reflexive FP)
      (Proof = HP)
      (Proof = {{ @eq_trans lp:A _ _ _ lp:HP lp:FP }}),
    coq.ltac.refine.typecheck Proof G GS.

  solve G GS :-
    if (hn-run G GS) true
      (coq.ltac.fail _ "hnorm_itr_elpi could not normalize this equality").
}}.

Ltac hnorm_itr_elpi := elpi hnorm_itr_elpi.
