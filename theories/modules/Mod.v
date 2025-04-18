Require Import Common.

Require Export ModTr.

Set Implicit Arguments.

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
        sem <- (alist_find fn ms.(fnsems))?;;
        sem args.

    Definition compile : itree coreE Any.t :=
      snd <$> ModTr.trans prog (prog (Call init_fun ()↑)) (initial_st ms).

  End COMPILE.
End Mod.
