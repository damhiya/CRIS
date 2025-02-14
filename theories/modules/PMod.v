Require Import Common.
Require Import SMod HMod.

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

  Definition handle_core: coreE ~> itree hmodE :=
    fun T e =>
      match e return itree hmodE T with
      | Take X => if excluded_middle_informative (∃ P: Prop, X = P)
                  then trigger e
                  else triggerUB
      | _ => trigger e
      end.

  Definition interp {R} (itr: itree pmodE R) : itree hmodE R
    :=
    interp
      (case_ (bif:=sum1) trivial_Handler
      (case_ (bif:=sum1) trivial_Handler
      (case_ (bif:=sum1) trivial_Handler
         handle_core)))
      itr.

  Program Definition to_hmod (ms : t) : HMod.t := {|
    HMod.scopes := ms.(scopes);                                                    
    HMod.fnsems := List.map (map_snd (λ kb, (kb.1, (λ i, interp (kb.2 i))))) ms.(fnsems);
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
    fsb_body := λ i, interp (body i);
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

Notation "↥ it" := (PMod.interp it) (at level 60, only printing).

Module PModRed.
Section RED.

  Context `{Σ : GRA}.

(* itree reduction *)
  Lemma interp_bind
        (R S: Type)
        (s : itree pmodE R) (k : R -> itree pmodE S)
    :
    PMod.interp (s >>= k)
    =
    st <- PMod.interp s;; PMod.interp (k st).
  Proof.
    unfold PMod.interp. grind.
  Qed.

  Lemma interp_tau
        (U: Type)
        (t : itree _ U)
    :
      PMod.interp (tau;; t)
      =
      tau;; (PMod.interp t).
  Proof.
    unfold PMod.interp. grind.
  Qed.

  Lemma interp_ret
        (U: Type)
        (t: U)
    :
      PMod.interp (Ret t)
      =
      Ret t.
  Proof.
    unfold PMod.interp. grind.
  Qed.

  Lemma interp_call
        (R: Type)
        (i: callE R)
    :
      PMod.interp (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof.
    unfold PMod.interp. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_sch
        (R: Type)
        (i: schE R)
    :
      PMod.interp (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof.
    unfold PMod.interp. rewrite interp_trigger. grind.
  Qed.
  
  Lemma interp_pg
        (R: Type)
        (i: pgE R)
    :
      PMod.interp (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof.
    unfold PMod.interp. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_take
        (P: Prop)
    :
      PMod.interp (trigger (Take P))
      =
      r <- trigger (Take P);; tau;; Ret r.
  Proof.
    unfold PMod.interp, PMod.handle_core.
    rewrite interp_trigger. grind.
    exfalso. eauto.
  Qed.
  
  Lemma interp_choose
        (X: Type)
    :
      PMod.interp (trigger (Choose X))
      =
      r <- trigger (Choose X);; tau;; Ret r.
  Proof.
    unfold PMod.interp, PMod.handle_core.
    rewrite interp_trigger. grind.
  Qed.

  Lemma interp_io
        I O fn args
    :
      PMod.interp (trigger (@IO I O fn args))
      =
      r <- trigger (IO fn args);; tau;; Ret r.
  Proof.
    unfold PMod.interp, PMod.handle_core.
    rewrite interp_trigger. grind.
  Qed.
  
  Lemma interp_unwrapU 
        (R: Type)
        (i: option R)
    :
    PMod.interp (@unwrapU pmodE _ _ i)
    =
    unwrapU i.
  Proof.
    rewrite /unwrapU. des_ifs.
    - rewrite interp_ret; eauto.
    - rewrite /triggerUB !interp_bind !interp_take. grind.
  Qed.

  Lemma interp_unwrapN
        (R: Type)
        (i: option R)
    :
      PMod.interp (@unwrapN pmodE _ _ i)
      =
      unwrapN i.
  Proof.
    rewrite /unwrapN. des_ifs.
    - rewrite interp_ret; eauto.
    - rewrite /triggerNB !interp_bind !interp_choose. grind.
  Qed.

  Lemma interp_asm
        P
    : 
      PMod.interp (assume P)
      =
      assume P;;; tau;; Ret ().
  Proof.
    rewrite /assume !interp_bind !interp_take !interp_ret. grind.
  Qed. 

  Lemma interp_guar
        P
    : 
      PMod.interp (guarantee P)
      =
      guarantee P;;; tau;; Ret ().
  Proof.
    rewrite /guarantee !interp_bind !interp_choose !interp_ret. grind.
  Qed.
  
End RED.
End PModRed.

Module PMWrap.

  Definition handler (fns: list string) : Handler callE pmodE :=
    fun _ e =>
      match e with
      | Call fn args =>
          if existsb (eqb fn) fns
          then trigger (Call fn args)
          else triggerUB
      end.

  Definition body (fns: list string) (code: Any.t -> itree pmodE Any.t) :
    Any.t -> itree pmodE Any.t
    :=
    fun x => interp
      (case_ (bif:=sum1) trivial_Handler
      (case_ (bif:=sum1) (handler fns)
      (case_ (bif:=sum1) trivial_Handler
         trivial_Handler))) (code x).

  Program Definition pmod fns (m: PMod.t) : PMod.t :=
    {|PMod.scopes := m.(PMod.scopes)
    ; PMod.fnsems := List.map (map_snd (map_snd (body fns))) m.(PMod.fnsems)
    ; PMod.initial_st := m.(PMod.initial_st)
    |}.
  Next Obligation.
    ii. eapply (m.(PMod.well_scoped_fns) fn). unfold fnsems_scopes in *.
    rewrite !alist_find_map_snd in H. des_ifs; eauto.
  Qed.
  Next Obligation. ii. eapply (m.(PMod.well_scoped_init)). eauto. Qed.
  Next Obligation. ii. eapply (m.(PMod.nodup_fns)). eauto. Qed.

End PMWrap.
