Require Import Common.

Require Export ModTr.

Set Implicit Arguments.

Module Mod.

  Record t : Type :=
    mk {
        fnsems : alist string (Any.t -> itree modE Any.t);
        initial_st : Any.t;
        initial_code : Any.t -> itree modE Any.t;
      }.

  Record wf (ms : t) : Prop := mk_wf {
    wf_fnsems : List.NoDup (List.map fst ms.(fnsems));
  }.

  Section COMPILE.

    Variable ms: t.

    Definition prog: string -> option (Any.t -> itree modE Any.t) :=
      fun fn => alist_find fn ms.(fnsems).

    Definition compile : Any.t -> itree coreE Any.t :=
      λ arg,
      snd <$> ModTr.trans prog (initial_code ms arg) (initial_st ms).

  End COMPILE.
End Mod.
