Require Import Common.

Require Export Mod2ITree.

Set Implicit Arguments.

Section ADD.

  Definition RUN : Type := forall V, (Any.t -> Any.t * V) -> (Any.t -> Any.t * V).

  Definition run_l : RUN := 
    fun _ run st =>
      match Any.split st with
      | Some (a, b) => let (a', v) := run a in (Any.pair a' b, v)
      | None => run tt↑
      end.

  Definition run_r : RUN := 
    fun _ run st =>
      match Any.split st with
      | Some (a, b) => let (b', v) := run b in (Any.pair a b', v)
      | None => run tt↑
      end.

End ADD.

Module Mod.

  Record t : Type := mk {
    initial_st : Any.t;
    fnsems : alist string (Any.t -> itree modE Any.t);
  }.

  Record wf (ms : t) : Prop := mk_wf {
    wf_fnsems : List.NoDup (List.map fst ms.(fnsems));
  }.

  Definition empty: t := {|
    initial_st := tt↑;
    fnsems := [];
  |}.

  Section COMPILE.

    Variable ms: t.

    Definition init_fun := "CRIS_init".

    Definition prog: callE ~> itree modE :=
      fun _ '(Call fn args) =>
        sem <- (alist_find fn ms.(fnsems))!;;
        sem args.

    Definition compile : itree coreE Any.t :=
      snd <$> interp_modE prog (prog (Call init_fun ()↑)) (initial_st ms).

  End COMPILE.
End Mod.