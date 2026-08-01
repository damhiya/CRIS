From CRIS.common Require Export Common Fn.
From CRIS.modules Require Export LModTr.

Module LMod.
  Record t (Σ : Type) : Type := mk {
    fnsems : gmap fname (Any.t → itree (lmodE Σ) Any.t);
    initial_st : lstateT Σ;
  }.

  Arguments fnsems {Σ} _.
  Arguments initial_st {Σ} _.

  (* Record wf (ms : t) : Prop := mk_wf {
    wf_fnsems : map_Forall (const is_Some) (fnsems ms);
  }. *)

  Definition prog {Σ} (ms : t Σ) : string → option (Any.t → itree (lmodE Σ) Any.t) :=
    λ fn, (fnsems ms) !! (funid fn).

  Definition compile {Σ} (ms : t Σ) : Any.t → itree coreE Any.t := λ arg,
    bd <- ((fnsems ms) !! entry)? ;;
    snd <$> LModTr.trans (prog ms) (bd arg) (initial_st ms).
End LMod.
