Require Import CRIS.

Require Import SchInvariants.

Set Implicit Arguments.

Section GINV.

  Context `{_W: sinvG}.

  Definition sch_ginv (univ: positive): Sk.t -> invspec :=
    fun _ _ => (∃ n, wsats univ n ⊤)%I.

End GINV.
