From CRIS.proofmode Require Import HNormClasses.
From CRIS.common Require Import Common.

(*** head normalization tactic ***)
(*
  itree term        t
  ktree term        k
  stuck term        s ::= opaque term
                        | s >>= k
                        | ↥ s
                        | ↧ s
                        | ░ s
  head normal term  v ::= Ret x
                        | Tau t
                        | vis e k
                        | assumeK P t
                        | guaranteeK P t
                        | unwrapUK x k
                        | unwrapNK x k
                        | RealUpdateK pre post k
                        | s
 *)

(* Opaque ReSum blocks instance resolution occasionally *)
Typeclasses Transparent ReSum.

(* Keep the wrapper heads distinct from their generic [Vis]/[bind] forms
   during typeclass search.  In particular, [unwrapUK] and [unwrapNK] stay
   transparent so their [Some] cases can reduce to [Ret]. *)
Typeclasses Opaque assumeK guaranteeK RealUpdateK.

Module HNorm.
  (* Only reuse [simpl] on immutable inputs.  A local definition or class
     hypothesis containing an evar can change during instance resolution.
     Check the input and local environment once, not at every tree node. *)
  Ltac stable_input x :=
    tryif multimatch goal with
          | H := ?v : ?T |- _ => first [has_evar v | has_evar T]
          | H : ?T |- _ => has_evar T
          end
    then fail 0
    else tryif has_evar x then fail 0 else idtac.

  Ltac direct_arg parent child :=
    lazymatch parent with
    | ?f ?x => first [constr_eq x child | direct_arg f child]
    end.

  (* [ready] only follows exact arguments of the initially simplified term.
     Expansion, a context that constructs its child, or a continued reduction
     invalidates it: these can introduce fresh beta/let redexes.

     The apply lemmas have a fixed arrangement of output holes.  Explicitly
     shelving them with [simple refine] avoids the dependency scans performed
     by ordinary [refine].  Instance lookup still uses [tc_solve]. *)
  Ltac normalize := simpl; step false
  with step ready :=
    tryif simple notypeclasses refine (HNormExpand_apply _ _);
      [shelve|tc_solve|] then
      descend false
    else descend ready
  with descend ready :=
    lazymatch goal with
    | |- ?x = _ =>
        tryif simple notypeclasses refine (HNormContext_apply _ _ _);
          [shelve|shelve|shelve|tc_solve|shelve|] then
          lazymatch goal with
          | |- HNormContextRes ?K ?b ?b' ?rhs =>
              simple notypeclasses refine
                {| HNormContextRes_goal1 := _; HNormContextRes_goal2 := _ |};
              [ tryif constr_eq ready true; direct_arg x b
                then step true else normalize
              | tryif simple notypeclasses refine
                  (@HNormReduce_apply _ _ K b' _ _ _ _ _);
                  [shelve|shelve|tc_solve|] then
                  lazymatch goal with
                  | |- HNormReduceRes ?b true ?rhs =>
                      simple notypeclasses refine
                        {| HNormReduceRes_goal1 := _ |}; normalize
                  | |- HNormReduceRes ?b false ?rhs =>
                      simple notypeclasses refine
                        {| HNormReduceRes_goal1 := _ |}; reflexivity
                  end
                else reflexivity
              ]
          end
        else reflexivity
    end.

  Ltac core :=
    simpl;
    lazymatch goal with
    | |- ?x = _ =>
        tryif stable_input x then step true else step false
    end.
End HNorm.

Ltac _hnorm_itr := HNorm.core.
Ltac hnorm_itr :=
  etransitivity;
  [ _hnorm_itr
  | try (simple notypeclasses refine (HNormFinish_apply _ _);
      [shelve|tc_solve|]);
    reflexivity
  ].
