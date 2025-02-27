(* NOTE : opening this file with VsCoq 2 will immediately crash the language server - use vscoq legacy instead *)
From Ltac2 Require Import Ltac2.

Ltac2 or t0 t1 :=
  fun x =>
    match! 'True with
    | True => t0 x
    | _ => t1 x
    end.

Ltac2 Type exn ::= [ TCSearchSuccess (constr) | TCSearchFail ].

Ltac2 evar t n :=
  let u := open_constr:(_: ltac:(exact_no_check $t)) in
  match Constr.Unsafe.kind u with
  | Constr.Unsafe.Cast v _ _ =>
      Std.pose n u;
      v
  | _ => Control.throw Init.Assertion_failure
  end
.

Ltac2 unshelve_evar e n :=
  let v := evar e (Some n) in
  match Constr.Unsafe.kind v with
  | Constr.Unsafe.Evar e _ =>
      Control.new_goal e
  | _ => Control.throw Init.Assertion_failure
  end
.

Ltac2 unshelve_evar1 e n :=
  (ltac1:(e n|- unshelve evar (n: e))) (Ltac1.of_constr e) (Ltac1.of_ident n)
.

Ltac2 multiverse_execute tac :=
  let l := Array.make 1 (None: constr option) in
  Control.plus
    (fun _ =>
       let v := tac () in
       Array.set l 0 (Some v);
       Control.zero (Tactic_failure None)
    )
    (fun _ =>
       match Array.get l 0 with
       | Some c => c
       | None => Control.zero (Tactic_failure None)
       end).

Ltac2 tcsearch e :=
  multiverse_execute
    (fun _ =>
       let n := Fresh.in_goal ident:(_TC_) in
       unshelve_evar e n > [|typeclasses_eauto];
       Std.eval_unfold [(Std.VarRef n, Std.AllOccurrences)] (Control.hyp n)).

Ltac2 tcsearch_alt e :=
  Control.plus
    (fun _ =>
       let n := Fresh.in_goal ident:(_TC_) in
       unshelve_evar e n > [|once typeclasses_eauto];
       Control.zero (TCSearchSuccess (Std.eval_unfold [(Std.VarRef n, Std.AllOccurrences)] (Control.hyp n)))
    )
    (fun e =>
       match e with
       | TCSearchSuccess c => c
       | _ => Control.zero e
       end
    )
.

Module TEST. Section TEST.
  Variable A: Type.
  Variable a b: A.

  Class Foo (n: nat) := mk_Foo {}.
  Global Instance foo: Foo 3 := mk_Foo _.

  Class Bar (a: A) := mk_Bar { Bar_contents: A; }.

  Instance bar: Bar a := mk_Bar _ b.

  Goal True.
    (* time (let _ := tcsearch_alt constr:(Foo 3) in ()).
    time (let _ := tcsearch_alt constr:(Bar a) in ()).
    time (do 100 (let _ := tcsearch constr:(Bar a) in ())). *)
    exact I.
  Qed.
End TEST. End TEST.

Ltac message :=
  ltac2:(e |-
           let e := Option.get (Ltac1.to_constr e) in
           Message.print (Message.of_constr e))
.

Ltac tcsearch :=
  ltac2:(e k |-
           let e := Option.get (Ltac1.to_constr e) in
           let v := tcsearch e in
           Ltac1.apply k [Ltac1.of_constr v] Ltac1.run)
.