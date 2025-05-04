Require Import Common.
Require Import HMod SMod.
Require Export PModTr.

Set Implicit Arguments.

Module PMod.
Section PMOD.

  Context `{Σ : GRA}.

  Record t : Type := mk {
    scopes : list string;
    fnsems : alist string ((string->bool) * list string * (Any.t -> itree pmodE Any.t));
    initial_st : alist key Any.t;

    well_scoped_fns:
      forall fn, incl (fnsems_scopes fn fnsems) scopes;
    well_scoped_init:
      incl (state_scopes initial_st) scopes;
    nodup_fns:
      List.NoDup scopes -> List.NoDup (List.map fst initial_st);
  }.

  Program Definition to_hmod (ms : t) : HMod.t := {|
    HMod.scopes := ms.(scopes);                                                    
    HMod.fnsems := List.map (map_snd (λ kb, (kb.1, (λ i, PModTr.trans (kb.2 i))))) ms.(fnsems);
    HMod.initial_st := ms.(initial_st);
  |}.
  Next Obligation.
    i. destruct ms. s. ii.
    eapply well_scoped_fns0. instantiate (1:=fn).
    unfold fnsems_scopes, map_snd in *.
    rewrite alist_find_map in H.
    unfold o_map in *. des_ifs.
  Qed.
  Next Obligation. i. destruct ms. s. eauto. Qed.
  Next Obligation. i. destruct ms. eauto. Qed.

  Definition wrap_trivial_spec (body: Any.t -> itree pmodE Any.t): fspecbody := {|
    fsb_fspec := fspec_trivial;
    fsb_body := λ i, PModTr.trans (body i);
  |}.
  
  Program Definition to_smod (ms: t) : SMod.t := {|
    SMod.scopes := ms.(scopes);
    SMod.fnsems := List.map (map_snd (λ kb, (kb.1, wrap_trivial_spec kb.2))) ms.(fnsems);
    SMod.initial_st := ms.(initial_st);
  |}.
  Next Obligation.
  i. destruct ms. s. ii.
  eapply well_scoped_fns0. instantiate (1:=fn).
  unfold fnsems_scopes, map_snd in *.
  rewrite alist_find_map in H.
  unfold o_map in *. des_ifs.
  Qed.
  Next Obligation. i. destruct ms. s. eauto. Qed.
  Next Obligation. i. destruct ms. eauto. Qed.

End PMOD.
End PMod.
