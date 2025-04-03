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

Module PRed.
Section RED.

  Context `{Σ : GRA}.

(* itree reduction *)
  Lemma bind
        (R S: Type)
        (s : itree pmodE R) (k : R -> itree pmodE S)
    :
    PMod.interp (s >>= k)
    =
    st <- PMod.interp s;; PMod.interp (k st).
  Proof using.
    unfold PMod.interp. grind.
  Qed.

  Lemma tau
        (U: Type)
        (t : itree _ U)
    :
      PMod.interp (tau;; t)
      =
      tau;; (PMod.interp t).
  Proof using.
    unfold PMod.interp. grind.
  Qed.

  Lemma ret
        (U: Type)
        (t: U)
    :
      PMod.interp (Ret t)
      =
      Ret t.
  Proof using.
    unfold PMod.interp. grind.
  Qed.

  Lemma vis_sch {X R} (e : schE X) (ktr : X -> itree pmodE R) :
    PMod.interp (vis e ktr) = vis e (fun x => tau;; PMod.interp (ktr x)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma vis_call {X R} (e : callE X) (ktr : X -> itree pmodE R) :
    PMod.interp (vis e ktr) = vis e (fun x => tau;; PMod.interp (ktr x)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma vis_pg {X R} (e : pgE X) (ktr : X -> itree pmodE R) :
    PMod.interp (vis e ktr) = vis e (fun x => tau;; PMod.interp (ktr x)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma vis_choose {X R} (ktr : X -> itree pmodE R) :
    PMod.interp (vis (Choose X) ktr) = vis (Choose X) (fun x => tau;; PMod.interp (ktr x)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma vis_take {X : Prop} {R} (ktr : X -> itree pmodE R) :
    PMod.interp (vis (Take X) ktr) = vis (Take X) (fun x => tau;; PMod.interp (ktr x)).
  Proof using.
    eapply observe_eta; cbn. destruct excluded_middle_informative as [H|H]; ss.
    - f_equal. extensionality x. eapply observe_eta; ss.
    - exfalso. apply H. exists X. reflexivity.
  Qed.

  Lemma vis_io {I O R} fn args (ktr : O -> itree pmodE R) :
    PMod.interp (vis (@IO I O fn args) ktr) = vis (IO fn args) (fun x => tau;; PMod.interp (ktr x)).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma assumeK {R} P (itr : itree pmodE R) :
    PMod.interp (assumeK P itr) = assumeK P (tau;; PMod.interp itr).
  Proof using.
    eapply observe_eta; cbn. destruct excluded_middle_informative as [H|H]; ss.
    - f_equal. extensionality x. eapply observe_eta; ss.
    - exfalso. apply H. exists P. reflexivity.
  Qed.

  Lemma guaranteeK {R} P (itr : itree pmodE R) :
    PMod.interp (guaranteeK P itr) = guaranteeK P (tau;; PMod.interp itr).
  Proof using.
    eapply observe_eta; ss. f_equal. extensionality x.
    eapply observe_eta; ss.
  Qed.

  Lemma unwrapUK {X R} x (ktr : X -> itree pmodE R) :
    PMod.interp (unwrapUK x ktr) = unwrapUK x (fun x => PMod.interp (ktr x)).
  Proof using.
    destruct x; ss. eapply observe_eta; cbn. destruct excluded_middle_informative as [H|H]; ss.
    - f_equal. extensionality x. eapply observe_eta; ss.
    - exfalso. apply H. exists False. reflexivity.
  Qed.

  Lemma unwrapNK {X R} x (ktr : X -> itree pmodE R) :
    PMod.interp (unwrapNK x ktr) = unwrapNK x (fun x => PMod.interp (ktr x)).
  Proof using.
    destruct x; ss.
    eapply observe_eta; ss. f_equal. extensionality x. ss.
  Qed.

  Lemma call
        (R: Type)
        (i: callE R)
    :
      PMod.interp (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof using.
    unfold PMod.interp. rewrite interp_trigger. grind.
  Qed.

  Lemma sch
        (R: Type)
        (i: schE R)
    :
      PMod.interp (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof using.
    unfold PMod.interp. rewrite interp_trigger. grind.
  Qed.
  
  Lemma pg
        (R: Type)
        (i: pgE R)
    :
      PMod.interp (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof using.
    unfold PMod.interp. rewrite interp_trigger. grind.
  Qed.

  Lemma take
        (P: Prop)
    :
      PMod.interp (trigger (Take P))
      =
      r <- trigger (Take P);; tau;; Ret r.
  Proof using.
    unfold PMod.interp, PMod.handle_core.
    rewrite interp_trigger. grind.
    exfalso. eauto.
  Qed.
  
  Lemma choose
        (X: Type)
    :
      PMod.interp (trigger (Choose X))
      =
      r <- trigger (Choose X);; tau;; Ret r.
  Proof using.
    unfold PMod.interp, PMod.handle_core.
    rewrite interp_trigger. grind.
  Qed.

  Lemma io
        I O fn args
    :
      PMod.interp (trigger (@IO I O fn args))
      =
      r <- trigger (IO fn args);; tau;; Ret r.
  Proof using.
    unfold PMod.interp, PMod.handle_core.
    rewrite interp_trigger. grind.
  Qed.
  
  Lemma unwrapU 
        (R: Type)
        (i: option R)
    :
    PMod.interp (@unwrapU pmodE _ _ i)
    =
    unwrapU i.
  Proof using.
    rewrite /unwrapU. des_ifs.
    - rewrite ret; eauto.
    - rewrite /triggerUB !bind !take. grind.
  Qed.

  Lemma unwrapN
        (R: Type)
        (i: option R)
    :
      PMod.interp (@unwrapN pmodE _ _ i)
      =
      unwrapN i.
  Proof using.
    rewrite /unwrapN. des_ifs.
    - rewrite ret; eauto.
    - rewrite /triggerNB !bind !choose. grind.
  Qed.

  Lemma asm
        P
    : 
      PMod.interp (assume P)
      =
      assume P;;; tau;; Ret ().
  Proof using.
    rewrite /assume !bind !take !ret. grind.
  Qed. 

  Lemma guar
        P
    : 
      PMod.interp (guarantee P)
      =
      guarantee P;;; tau;; Ret ().
  Proof using.
    rewrite /guarantee !bind !choose !ret. grind.
  Qed.
  
End RED.
End PRed.

Module PMWrap.
  (*
    The parameter 'ar' determines
    whether we accept calls to the functions in the list 'fns',
    or we reject calls to the functions in the list 'fns'.
   *)

  Definition handler (ar: bool) (fns: list string) : Handler callE pmodE :=
    fun _ e =>
      match e with
      | Call fn args =>
          let in_fns := existsb (eqb fn) fns in
          if (ar && negb in_fns) || (negb ar && in_fns)
          then triggerUB
          else trigger (Call fn args)
      end.

  Definition wrap (ar: bool) (fns: list string) (code: Any.t -> itree pmodE Any.t) :
    Any.t -> itree pmodE Any.t
    :=
    fun x => interp
      (case_ (bif:=sum1) trivial_Handler
      (case_ (bif:=sum1) (handler ar fns)
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
