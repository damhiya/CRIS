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

    Definition prog: string -> option (Any.t -> itree modE Any.t) :=
      fun fn => alist_find fn ms.(fnsems).

    Definition compile : itree coreE Any.t :=
      bd <- (prog init_fun)?;;
      snd <$> ModTr.trans prog (bd ()↑) (initial_st ms).

  End COMPILE.
End Mod.
