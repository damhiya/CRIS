From CRIS.common Require Export Common Fn.
From CRIS.modules Require Export LModTr.

Module LMod.
  Record t : Type := mk {
    fnsems : gmap fname (Any.t → itree lmodE Any.t);
    initial_st : lstateT;
  }.

  (* Record wf (ms : t) : Prop := mk_wf {
    wf_fnsems : map_Forall (const is_Some) (fnsems ms);
  }. *)

  Definition prog (ms : t) : string → option (Any.t → itree lmodE Any.t) :=
    λ fn, (fnsems ms) !! (funid fn).

  Definition compile (ms : t) : Any.t → itree coreE Any.t := λ arg,
    bd <- ((fnsems ms) !! entry)? ;;
    snd <$> LModTr.trans (prog ms) (bd arg) (initial_st ms).
End LMod.
