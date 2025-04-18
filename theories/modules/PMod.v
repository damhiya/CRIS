Require Import Common.
Require Import HMod SMod.
Require Export PModTr.

Set Implicit Arguments.

Module PMod.
Section PMOD.

  Context `{Σ : GRA}.

  Record t : Type := mk {
    scopes : list string;
    fnsems : alist string (list string * (Any.t -> itree pmodE Any.t));
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

Module PMWrap.
  (*
    The parameter 'ar' determines
    whether we accept calls to the functions in the list 'fns',
    or we reject calls to the functions in the list 'fns'.
   *)

  Definition handler_call (ar: bool) (fns: list string) : Handler callE pmodE :=
    fun _ e =>
      match e with
      | Call fn args =>
          let in_fns := existsb (eqb fn) fns in
          if (ar && negb in_fns) || (negb ar && in_fns)
          then triggerUB
          else trigger (Call fn args)
      end.

  Definition handler_sch (ar: bool) (fns: list string) : Handler schE pmodE :=
    fun _ e =>
      match e with
      | Spawn fn args =>
          let in_fns := existsb (eqb fn) fns in
          if (ar && negb in_fns) || (negb ar && in_fns)
          then triggerUB
          else trigger (Spawn fn args)
      | Yield tid => trigger (Yield tid)
      end.

  Definition wrap (ar: bool) (fns: list string) (code: Any.t -> itree pmodE Any.t) :
    Any.t -> itree pmodE Any.t
    :=
    fun x => interp
      (case_ (bif:=sum1) (handler_sch ar fns)
      (case_ (bif:=sum1) (handler_call ar fns)
      (case_ (bif:=sum1) trivial_Handler
         trivial_Handler))) (code x).

  Program Definition pmod (ar: bool) fns (m: PMod.t) : PMod.t :=
    {|PMod.scopes := m.(PMod.scopes)
    ; PMod.fnsems := List.map (map_snd (map_snd (wrap ar fns))) m.(PMod.fnsems)
    ; PMod.initial_st := m.(PMod.initial_st)
    |}.
  Next Obligation.
    ii. eapply (m.(PMod.well_scoped_fns) fn). unfold fnsems_scopes in *.
    rewrite !alist_find_map_snd in H. des_ifs; eauto.
  Qed.
  Next Obligation. ii. eapply (m.(PMod.well_scoped_init)). eauto. Qed.
  Next Obligation. ii. eapply (m.(PMod.nodup_fns)). eauto. Qed.

End PMWrap.
