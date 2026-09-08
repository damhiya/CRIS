From elpi Require Import elpi.
From CRIS.common Require Import Common.
From CRIS.proofmode Require Import HNormClasses HNormInstances.
From CRIS.modules Require Import ModTr LModTr SModTr Sandbox.

(** The HNorm classes specify proofs; registration compiles their instances
    to native Elpi predicates. Rule execution does not reconstruct class
    goals or invoke Rocq's typeclass resolver. Inputs are matched structurally,
    up to renaming bound variables, without conversion or unfolding. *)
Module HNormElpiRules.
  Lemma expand_trigger {E X} (e : E X) :
    HNormExpand (ITree.trigger e) (Vis e (fun x => Ret x)).
  Proof. constructor. reflexivity. Qed.

  (* The general rules leave a known-None unwrap wrapper, whose reduction
     used to depend on conversion during instance lookup. *)
  Lemma expand_triggerUB `{coreE -< E} {A} :
    HNormExpand (triggerUB : itree E A)
      (vis (Take False)
        (fun v => Ret v >>= fun x => match x : False with end)).
  Proof.
    constructor. unfold triggerUB, unwrapU, ITree.trigger. apply bind_vis.
  Qed.

  Lemma expand_triggerNB `{coreE -< E} {A} :
    HNormExpand (triggerNB : itree E A)
      (vis (Choose False)
        (fun v => Ret v >>= fun x => match x : False with end)).
  Proof.
    constructor. unfold triggerNB, unwrapN, ITree.trigger. apply bind_vis.
  Qed.
End HNormElpiRules.

Elpi Db hnorm.elpi.db lp:{{
  pred hn-expand i:term, o:term, o:term, o:term.
  pred hn-context i:term, o:term, o:term, o:term, o:term, o:term.
  pred hn-reduce i:term, i:term, o:term, o:term, o:term, o:term, o:term.
  pred hn-finish i:term, o:term, o:term, o:term.
  pred hn-bool i:term, o:term, o:term.

  pred hn-evidence i:term, o:term.
  pred hn-registered i:gref.
  pred hn-priority o:int.

  % An explicit computation rule for lambda-valued masks.  Matching remains
  % structural: only an actual lambda application takes this step.  Local
  % HNormBool hypotheses are installed before this global rule.
  hn-bool (app [Head, Arg | Args]) Y P :-
    not (var Head), Head = fun _ _ Body,
    coq.mk-app (Body Arg) Args Reduced,
    hn-bool Reduced Y P.

  % Rocq-Elpi represents type ascriptions as identity lets.  Erase just
  % those annotations, not ordinary lets, beta redexes, or definitions.
  pred hn-uncast i:term, o:term.
  hn-uncast T U :-
    (pi n ty v f r\
      copy (let n ty v f) r :-
        (pi x\ same_term (f x) x), !, copy v r) =>
    copy T U.

  % These translations run during registration/context loading only.
  % Context and Reduce are unique: commit after their premises succeed.
  pred hn-native-clause i:term, i:term, i:list prop, o:prop.
  hn-native-clause {{ @HNormExpand lp:A lp:X lp:Y }} P Ps
    (hn-expand X A Y P :- std.do! Ps).
  hn-native-clause {{ @HNormContext lp:A lp:B lp:X lp:K lp:V }} P Ps
    (hn-context X A B K V P :- std.do! Ps, !).
  hn-native-clause {{ @HNormReduce lp:A lp:B lp:K lp:X lp:Y lp:C }} P Ps
    (hn-reduce K X A B Y C P :- std.do! Ps, !).
  hn-native-clause {{ @HNormFinish lp:A lp:X lp:Y }} P Ps
    (hn-finish X A Y P :- std.do! Ps).
  hn-native-clause {{ HNormBool lp:X lp:Y }} P Ps
    (hn-bool X Y P :- std.do! Ps).

  pred hn-premise-code i:term, i:term, o:prop.
  hn-premise-code {{ @HNormExpand lp:A lp:X lp:Y }} P
    (hn-expand X A Y P) :- !.
  hn-premise-code {{ @HNormContext lp:A lp:B lp:X lp:K lp:V }} P
    (hn-context X A B K V P) :- !.
  hn-premise-code {{ @HNormReduce lp:A lp:B lp:K lp:X lp:Y lp:C }} P
    (hn-reduce K X A B Y C P) :- !.
  hn-premise-code {{ @HNormFinish lp:A lp:X lp:Y }} P
    (hn-finish X A Y P) :- !.
  hn-premise-code {{ HNormBool lp:X lp:Y }} P
    (hn-bool X Y P) :- !.
  hn-premise-code T P (hn-evidence T P).

  pred hn-class i:term.
  hn-class T :- coq.safe-dest-app T (global GR) _, coq.TC.class? GR.

  pred hn-build i:term, i:term, i:list prop, o:prop.
  hn-build (prod _ A F) P Ps (pi x\ Clause x) :- !,
    pi x\ sigma PX Code\
      coq.mk-app P [x] PX,
      if (hn-class A)
        (hn-premise-code A x Code,
         hn-build (F x) PX [if (var x) Code true | Ps] (Clause x))
        (hn-build (F x) PX Ps (Clause x)).
  hn-build (let _ _ V F) P Ps Clause :- !,
    hn-build (F V) P Ps Clause.
  hn-build T P Ps Clause :-
    std.rev Ps Premises,
    hn-native-clause T P Premises Clause.

  pred hn-native-conclusion i:term.
  hn-native-conclusion (prod _ _ Body) :- !,
    pi x\ hn-native-conclusion (Body x).
  hn-native-conclusion (let _ _ Value Body) :- !,
    hn-native-conclusion (Body Value).
  hn-native-conclusion T :- hn-native-clause T _ [] _.

  pred hn-local i:term, i:term, o:prop.
  hn-local P Ty Clause :-
    if (hn-native-conclusion Ty)
      (hn-uncast Ty Raw, hn-build Raw P [] Clause)
      (Clause = hn-evidence Ty P).

  pred hn-load-context i:goal-ctx, o:prop.
  hn-load-context [] true.
  hn-load-context [decl P _ Ty | Ctx] (Clause, Rest) :-
    hn-local P Ty Clause,
    hn-load-context Ctx Rest.
  hn-load-context [def P _ Ty _ | Ctx] (Clause, Rest) :-
    hn-local P Ty Clause,
    hn-load-context Ctx Rest.

  pred hn-anchor-end.
  :name "hn-rule-end" hn-anchor-end.
}}.

Elpi Command HNormElpi.Register.
Elpi Accumulate Db hnorm.elpi.db.
Elpi Accumulate lp:{{
  % Keep priority buckets ordered across subsequent registration commands.
  kind hn-position type.
  type hn-end hn-position.
  type hn-before int -> hn-position.

  pred hn-next i:int, i:list prop, o:hn-position.
  hn-next _ [] hn-end.
  hn-next P [hn-priority Q | Priorities] Position :-
    hn-next P Priorities Rest,
    if (Q > P)
      (if (Rest = hn-before R, R < Q)
         (Position = Rest) (Position = hn-before Q))
      (Position = Rest).

  pred hn-anchor i:hn-position, o:string.
  hn-anchor hn-end "hn-rule-end".
  hn-anchor (hn-before P) Name :-
    Name is "hn-priority-" ^ {calc (int_to_string P)}.

  pred hn-add-priority i:int, o:string.
  hn-add-priority P Name :-
    hn-anchor (hn-before P) Name,
    if (hn-priority P)
      true
      (std.findall (hn-priority _) Priorities,
       hn-next P Priorities Position,
       hn-anchor Position Next,
       coq.elpi.accumulate _ "hnorm.elpi.db"
         (clause Name (before Next) (hn-priority P))).

  pred hn-add i:tc-instance.
  hn-add (tc-instance GR Priority) :-
    hn-add-priority Priority Anchor,
    coq.env.typeof GR Annotated,
    hn-uncast Annotated Ty,
    hn-build Ty (global GR) [] Clause,
    coq.elpi.accumulate _ "hnorm.elpi.db"
      (clause _ (after Anchor) Clause),
    coq.elpi.accumulate _ "hnorm.elpi.db"
      (clause _ _ (hn-registered GR)).

  pred hn-add-list i:list tc-instance.
  hn-add-list [].
  hn-add-list [(tc-instance GR Priority as Instance) | Instances] :-
    if (hn-registered GR)
      (hn-add-list Instances)
      (hn-add Instance,
       hn-priority Priority => hn-registered GR => hn-add-list Instances).

  pred hn-instances i:list argument, o:list tc-instance.
  hn-instances [] [].
  hn-instances [str Name | Args] Instances :-
    coq.locate Name GR,
    if (coq.TC.class? GR)
      (coq.TC.db-for GR Here)
      (Here = [tc-instance GR 0]),
    hn-instances Args Rest,
    std.append Here Rest Instances.

  main Args :-
    hn-instances Args Instances,
    % Insertion is at the front of each bucket: reverse to retain precedence.
    std.rev Instances Reversed,
    hn-add-list Reversed.
}}.

Elpi HNormElpi.Register
  HNormElpiRules.expand_trigger
  HNormElpiRules.expand_triggerUB HNormElpiRules.expand_triggerNB.
Elpi HNormElpi.Register
  HNormBool HNormExpand HNormContext HNormReduce HNormFinish.
