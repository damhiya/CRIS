From stdpp Require Import base strings.
Require Import CRIS Common Mod LMod.
Require Import ProphecyHeader.
Require Import exco exco_stream.
Require Import IndefiniteDescription.

(** Prophecy inserting compilation *)
Section proph_interp.
  Import ProphecyHeader.ProphecyName.

  Definition prefix_io : string := "normal_".
  Definition prefix_proph : string := "prophecy_".

  Definition ths_state : Type := (nat * list (bool * itree lmodE Any.t))%type.

  Definition proph_handle_callE (prog: string -> option (Any.t -> itree lmodE Any.t))
      : ths_state -> itreeV (stateE +' coreE) (ths_state + Any.t) :=
    fun '(tid, ths) =>
      match base.lookup tid ths with
      | None => inl (triggerUB)
      | Some (b, itr) =>
          match observe (itr: itree lmodE Any.t) with
          | RetF rv =>
              inl (if Nat.eq_dec tid 0 then Ret (inr rv) else triggerUB)
          | TauF itr' =>
              inl (Ret (inl (tid, base.insert tid (b, itr') ths)))
          | VisF (inr1 e) k =>
              match e with
              | inr1 (IO fn args) =>
                  let fn' : string := if b : bool then prefix_proph +:+ fn
                                      else prefix_io +:+ fn in
                  inr (existT _ (subevent _ (IO fn' args), fun v => Ret (inl (tid, base.insert tid (false, k v) ths))))
              | _ =>
                  inr (existT _ (subevent _ e, fun v => Ret (inl (tid, base.insert tid (b, k v) ths))))
              end
          | VisF (inl1 e) k =>
              inl
                (match e in callE T return (T -> _) -> _ with
                 | Call fn arg =>
                     fun k =>
                       bd <- (prog fn)?;;
                       let bi :=
                         (if decide (fn = ProphecyName.new ∨ fn = ProphecyName.resolve ∨ fn = ProphecyName.close)
                          then (true, trigger (IO (O := ()) fn arg);;; x <- bd arg;; tau;; k x)
                          else (false, x <- bd arg;; tau;; k x)) in
                       Ret (inl (tid, base.insert tid bi ths))
                 | Spawn fn arg =>
                     fun k =>
                       bd <- (prog fn)?;;
                       let bi :=
                         (if decide (fn = ProphecyName.new ∨ fn = ProphecyName.resolve ∨ fn = ProphecyName.close)
                          then (true, trigger (IO (O := ()) fn arg);;; bd arg)
                          else (false, bd arg)) in
                       Ret (inl (tid, (base.insert tid (b, k (List.length ths)) ths) ++ [bi]))
                 | Yield tid' => fun k =>
                                   Ret (inl (tid', base.insert tid (b, k tt) ths))
                 end k)
          end
      end.

  Definition proph_interp_callE prog (itr0: itree lmodE Any.t)
      : itree (stateE +' coreE) Any.t :=
    iterV (proph_handle_callE prog) (0, [(false, itr0)]).

  Definition proph_trans prog (itr0: itree lmodE Any.t) (st0: Any.t): itree coreE _ :=
    LModTr.interp_stateE Any.t (proph_interp_callE prog itr0) st0.

End proph_interp.

Section proph_compile.

  Variable ms : LMod.t.

  Definition proph_compile (arg : Any.t) : itree coreE Any.t :=
    bd <- (alist_find None ms.(LMod.fnsems))? ;;
    snd <$> proph_trans (LMod.prog ms) (bd arg) (LMod.initial_st ms).

End proph_compile.

Module ExTr.

  Variant _op: Type :=
  | _done (retv : Any.t)
  | _abort
  | _hang (e: outE)
  | _interact (hd : outinE)
  | _tau
  | _choose (X:Type) (x : X)
  | _take (P:Type)
  .

  Definition _deg : _op -> Type :=
    fun op =>
      match op with
      | _done _ => fin 0
      | _abort => fin 0
      | _hang _ => fin 0
      | _interact _ => fin 1
      | _tau => fin 1
      | _choose _ _ => fin 1
      | _take _ => fin 1
      end.

  Global Instance _t : SPFU.t :=
    {| SPFU.shp := _op;
       SPFU.deg := fun op => _deg op |}.

  Definition t := ExCoU.co.

  Definition void_recT {T: Type} : fin 0 -> T.
  Proof.
    intro. inversion H.
  Qed.
  
  Definition done : Any.t -> t := fun retv => ExCoU.cfold (ExCoU.ccons (_done retv) void_recT).

  Definition abort : t := ExCoU.cfold (ExCoU.ccons _abort void_recT).

  Definition hang : outE -> t := fun oute => ExCoU.cfold (ExCoU.ccons (_hang oute) void_recT).

  Definition interact : outinE -> t -> t := fun oute tl => ExCoU.cfold (ExCoU.ccons (_interact oute) (λ _, tl)).

  Definition tau : t -> t := fun tl => ExCoU.cfold (ExCoU.ccons _tau (λ _, tl)).

  Definition choose : forall X : Type, X -> t -> t := fun X x tl => ExCoU.cfold (ExCoU.ccons (_choose X x) (λ _, tl)).

  Definition take : Type -> t -> t := fun P tl => ExCoU.cfold (ExCoU.ccons (_take P) (λ _, tl)).

  Lemma unfold_extr (extr: t) :
    extr =
    match extr with
    | ExCoU.cfold (ExCoU.ccons (_done retv) _) => done retv
    | ExCoU.cfold (ExCoU.ccons _abort _) => abort
    | ExCoU.cfold (ExCoU.ccons (_hang e) _) => hang e
    | ExCoU.cfold (ExCoU.ccons (_interact hd) args) => interact hd (args 0%fin)
    | ExCoU.cfold (ExCoU.ccons _tau args) => tau (args 0%fin)
    | ExCoU.cfold (ExCoU.ccons (_choose X x) args) => choose X x (args 0%fin)
    | ExCoU.cfold (ExCoU.ccons (_take P) args) => take P (args 0%fin)
    end.
  Proof.
    destruct extr, c, op;
    - unfold done. repeat f_equal. extensionality x. ss. depdes x.
    - unfold abort. repeat f_equal. extensionality x. ss. depdes x.
    - unfold hang. repeat f_equal. extensionality x. ss. depdes x.
    - unfold interact. repeat f_equal. extensionality x. ss.
      depdes x; auto. depdes x; auto.
    - unfold tau. repeat f_equal. extensionality x. ss.
      depdes x; auto. depdes x; auto.
    - unfold choose. repeat f_equal. extensionality y. ss. depdes y; et. depdes y.
    - unfold take. repeat f_equal. extensionality x. ss.
      depdes x; auto. depdes x; auto.
  Qed.

End ExTr.

Module ExBeh.
  Export ExTr.

  Local Notation L := (itree coreE Any.t).

  Variant _of_itreeF (coself : L -> ExTr.t -> Prop) : L -> ExTr.t -> Prop :=
  | sb_final
      retv
    : _of_itreeF coself (Ret retv) (ExTr.done retv)

  | sb_abort
      t
    : _of_itreeF coself t (ExTr.abort)

  | sb_tau
      t evs
      (STEP: coself t evs)
    :
    _of_itreeF coself (tau;; t) (ExTr.tau evs)

  | sb_hang
      I O fn args k
    :
    _of_itreeF coself (r <- trigger (@IO I O (prefix_io +:+ fn) args);; k r) (ExTr.hang (obs_out (prefix_io +:+ fn) args))

  | sb_interact
      I O fn args r evs k
      (TL: coself (k r) evs)
    :
    _of_itreeF coself (r <- trigger (@IO I O fn args);; k r) (ExTr.interact (obs_io fn args r) evs)

  | sb_choose
      X x k evs
      (STEP: coself (k x) evs)
    :
    _of_itreeF coself (x <- trigger (Choose X);; k x) (ExTr.choose X x evs)

  | sb_take
      (P : Prop) k evs
      (STEP: forall p : P, coself (k p) evs)
    :
    _of_itreeF coself (x <- trigger (Take P);; k x) (ExTr.take P evs)
  .

  Definition of_itree: _ -> _ -> Prop := paco2 _of_itreeF bot2.

  Lemma of_itree_mon: monotone2 _of_itreeF.
  Proof using.
    ii. destruct IN; des; eauto using _of_itreeF.
  Qed.

  Hint Constructors _of_itreeF : core.
  Hint Resolve of_itree_mon: paco.

  Lemma of_itree_ind
    (P: itree coreE Any.t -> ExTr.t -> Prop)
    (SIM: _of_itreeF of_itree <2= P)
    :
    of_itree <2= P.
  Proof using.
    i. punfold PR. inv PR; des; pclearbot; et.
  Qed.

End ExBeh.

Hint Constructors ExBeh._of_itreeF : core.
Hint Unfold ExBeh.of_itree : core.
Hint Resolve ExBeh.of_itree_mon: paco.
Hint Resolve cpn1_wcompat: paco.

Section ETO.

  Variant _extrace_obs_stream_relation (id : Prophecy.ID) (Pr: Prophecy.t)
    (coself: ExTr.t -> stream Pr.(Prophecy.Obs) -> Prop)
    : ExTr.t -> stream Pr.(Prophecy.Obs) -> Prop :=
  | eto_done
      retv obs
    : _extrace_obs_stream_relation id Pr coself (ExTr.done retv) obs
  | eto_abort
      obs
    : _extrace_obs_stream_relation id Pr coself (ExTr.abort) obs
  | eto_hang
      fn I args obs
    : _extrace_obs_stream_relation id Pr coself (ExTr.hang (@obs_out fn I args)) obs
  | eto_tau
      evs obs
      (STEP: coself evs obs)
    : _extrace_obs_stream_relation id Pr coself (ExTr.tau evs) obs
  | eto_choose
      X x evs obs
      (STEP: coself evs obs)
    : _extrace_obs_stream_relation id Pr coself (ExTr.choose X x evs) obs
  | eto_take
      P evs obs
      (STEP: coself evs obs)
    : _extrace_obs_stream_relation id Pr coself (ExTr.take P evs) obs
  | eto_interact_new_close_other
      fn O (id': Prophecy.ID) r evs obs
      (FNAME: fn = ProphecyName.new ∨ fn = ProphecyName.close)
      (NE: id' <> id)
      (STEP: coself evs obs)
    : _extrace_obs_stream_relation id Pr coself
        (ExTr.interact (@obs_io (prefix_proph +:+ fn) Any.t O id'↑ r) evs) obs
  | eto_interact_resolve
      O (o: Pr.(Prophecy.Obs)) r evs obs
      (STEP: coself evs obs)
    : _extrace_obs_stream_relation id Pr coself
        (ExTr.interact (@obs_io (prefix_proph +:+ ProphecyName.resolve) Any.t O (id, o↑↑)↑ r) evs)
        (sfold (scons o obs))
  | eto_interact_resolve_other
      O (id': Prophecy.ID) (o: SAny.t) r evs obs
      (NE: id' <> id)
      (STEP: coself evs obs)
    : _extrace_obs_stream_relation id Pr coself
        (ExTr.interact (@obs_io (prefix_proph +:+ ProphecyName.resolve) Any.t O (id', o)↑ r) evs) obs
  | eto_interact_proph_dummy
      fn O arg r evs obs
      (NE: ¬(((fn = ProphecyName.new ∨ fn = ProphecyName.close) ∧ ∃ (id': Prophecy.ID), arg = id'↑ ∧ id' <> id)
          ∨ (fn = ProphecyName.resolve ∧ ∃ (id': Prophecy.ID) (o: SAny.t), arg = (id', o)↑ ∧ (id' <> id ∨ ∃ (o' : Pr.(Prophecy.Obs)), o = o'↑↑))))
    : _extrace_obs_stream_relation id Pr coself
        (ExTr.interact (@obs_io (prefix_proph +:+ fn) Any.t O arg r) evs) obs
  | eto_interact_proph_wrong_type
      fn I O arg r evs obs
      (NE: I <> Any.t)
    : _extrace_obs_stream_relation id Pr coself
        (ExTr.interact (@obs_io (prefix_proph +:+ fn) I O arg r) evs) obs
  | eto_interact_else
      fn I O arg r evs obs
      (NE: ¬(∃ fn', fn = prefix_proph +:+ fn'))
      (STEP: coself evs obs)
    : _extrace_obs_stream_relation id Pr coself
        (ExTr.interact (@obs_io fn I O arg r) evs) obs.

  Definition extrace_obs_stream_relation (id: Prophecy.ID) (Pr: Prophecy.t)
    : ExTr.t -> stream Pr.(Prophecy.Obs) -> Prop
    := paco2 (_extrace_obs_stream_relation id Pr) bot2.


  Lemma extrace_obs_stream_relation_mon id Pr :
    monotone2 (_extrace_obs_stream_relation id Pr).
  Proof. ii. destruct IN; des; eauto using _extrace_obs_stream_relation. Qed.

  Hint Constructors _extrace_obs_stream_relation : core.
  Hint Resolve extrace_obs_stream_relation_mon : paco.

  (* exco *)

  Variant _eto_adeq_rel (id : Prophecy.ID) (Pr: Prophecy.t)
    (coself: ExTr.t -> _stream Pr.(Prophecy.Obs) ExTr.t -> Prop)
    : ExTr.t -> _stream Pr.(Prophecy.Obs) ExTr.t -> Prop :=
  | eto_adeq_done
      retv obs
    : _eto_adeq_rel id Pr coself (ExTr.done retv) obs
  | eto_adeq_abort
      obs
    : _eto_adeq_rel id Pr coself (ExTr.abort) obs
  | eto_adeq_hang
      fn I args obs
    : _eto_adeq_rel id Pr coself (ExTr.hang (@obs_out fn I args)) obs
  | eto_adeq_tau
      evs obs
      (STEP: coself evs obs)
    : _eto_adeq_rel id Pr coself (ExTr.tau evs) obs
  | eto_adeq_choose
      X x evs obs
      (STEP: coself evs obs)
    : _eto_adeq_rel id Pr coself (ExTr.choose X x evs) obs
  | eto_adeq_take
      P evs obs
      (STEP: coself evs obs)
    : _eto_adeq_rel id Pr coself (ExTr.take P evs) obs
  | eto_adeq_interact_other_type
      fn I O arg r evs obs
      (NE: I <> Any.t)
      (STEP: coself evs obs)
    : _eto_adeq_rel id Pr coself
        (ExTr.interact (@obs_io fn I O arg r) evs) obs
  | eto_adeq_resolve
      O (o: Pr.(Prophecy.Obs)) r evs
    : _eto_adeq_rel id Pr coself
        (ExTr.interact (@obs_io (prefix_proph +:+ ProphecyName.resolve) Any.t O (id, o↑↑)↑ r) evs)
        (scons o evs)
  | eto_adeq_interact_else
      fn O arg r evs obs
      (NE: ¬(fn = prefix_proph +:+ ProphecyName.resolve ∧ (∃ (o: Pr.(Prophecy.Obs)), arg = (id, o↑↑)↑)))
      (STEP: coself evs obs)
    : _eto_adeq_rel id Pr coself
        (ExTr.interact (@obs_io fn Any.t O arg r) evs) obs.

  Definition eto_adeq_rel (id: Prophecy.ID) (Pr: Prophecy.t)
    : ExTr.t -> _stream Pr.(Prophecy.Obs) ExTr.t -> Prop
    := paco2 (_eto_adeq_rel id Pr) bot2.

  Lemma eto_adeq_rel_mon (id: Prophecy.ID) (Pr: Prophecy.t) : monotone2 (_eto_adeq_rel id Pr).
  Proof. ii. destruct IN; des; eauto using _eto_adeq_rel. Qed.

  Hint Constructors _eto_adeq_rel: core.
  Hint Unfold eto_adeq_rel: core.
  Hint Resolve eto_adeq_rel_mon: paco.

  Variant _et_spin (id: Prophecy.ID) (Pr: Prophecy.t) (coself: ExTr.t -> Prop)
    : ExTr.t -> Prop :=
  | et_spin_tau
      evs
      (SELF: coself evs)
    : _et_spin id Pr coself (ExTr.tau evs)
  | et_spin_choose
      X x evs
      (SELF: coself evs)
    : _et_spin id Pr coself (ExTr.choose X x evs)
  | et_spin_take
      P evs
      (SELF: coself evs)
    : _et_spin id Pr coself (ExTr.take P evs)
  | et_spin_interact_other_type
      fn I O arg r evs
      (NE: I <> Any.t)
      (SELF: coself evs)
    : _et_spin id Pr coself
        (ExTr.interact (@obs_io fn I O arg r) evs)
  | et_spin_interact_else
      fn O arg r evs
      (NE: ¬(fn = prefix_proph +:+ ProphecyName.resolve ∧ ∃ (o: Pr.(Prophecy.Obs)), arg = (id, o↑↑)↑))
      (SELF: coself evs)
    : _et_spin id Pr coself
        (ExTr.interact (@obs_io fn Any.t O arg r) evs).

  Definition et_spin (id: Prophecy.ID) (Pr: Prophecy.t): ExTr.t -> Prop
    := paco1 (_et_spin id Pr) bot1.

  Lemma et_spin_mon (id: Prophecy.ID) (Pr: Prophecy.t): monotone1 (_et_spin id Pr).
  Proof. ii. inv IN; eauto using _et_spin. Qed.

  Hint Resolve et_spin_mon : paco.

  Inductive et_step (id: Prophecy.ID) (Pr: Prophecy.t)
    : ExTr.t -> Prop :=
  | et_step_done
      retv
    : et_step id Pr (ExTr.done retv)
  | et_step_abort
    : et_step id Pr (ExTr.abort)
  | et_step_hang
      fn I args
    : et_step id Pr (ExTr.hang (@obs_out fn I args))
  | et_step_resolve_this
      O (o : Pr.(Prophecy.Obs)) r evs
    : et_step id Pr
        (ExTr.interact (@obs_io (prefix_proph +:+ ProphecyName.resolve) Any.t O (id, o↑↑)↑ r) evs)
  | et_step_tau
      evs
      (STEP: et_step id Pr evs)
    : et_step id Pr (ExTr.tau evs)
  | et_step_choose
      X x evs
      (STEP: et_step id Pr evs)
    : et_step id Pr (ExTr.choose X x evs)
  | et_step_take
      P evs
      (STEP: et_step id Pr evs)
    : et_step id Pr (ExTr.take P evs)
  | et_step_interact_other_type
      fn I O arg r evs
      (NE: I <> Any.t)
      (STEP: et_step id Pr evs)
    : et_step id Pr
        (ExTr.interact (@obs_io fn I O arg r) evs)
  | et_step_interact_else
      fn O arg r evs
      (NE: ¬(fn = prefix_proph +:+ ProphecyName.resolve ∧ ∃ (o: Pr.(Prophecy.Obs)), arg = (id, o↑↑)↑))
      (STEP: et_step id Pr evs)
    : et_step id Pr
        (ExTr.interact (@obs_io fn Any.t O arg r) evs).

  Hint Constructors et_step : core.

  Lemma et_step_or_spin (id: Prophecy.ID) (Pr: Prophecy.t)
    : ∀ et, et_step id Pr et ∨ et_spin id Pr et.
  Proof.
    i. destruct (classic (et_step id Pr et)); [left; auto | right].
    revert_until Pr.
    pcofix CIH. intro. rewrite (ExTr.unfold_extr et). i. pstep.
    destruct et, c, op; try solve [exfalso; auto]; try solve [econs; right; auto].
    - exfalso. apply H0. destruct e; auto.
    - destruct hd. destruct (classic (I = Any.t)); [subst |].
      + destruct (classic ((fn = prefix_proph +:+ ProphecyName.resolve ∧ ∃ (o: Pr.(Prophecy.Obs)), args0 = (id, o↑↑)↑))).
        * des; subst. exfalso; auto.
        * apply et_spin_interact_else; auto. right. auto.
      + econs; auto. right. auto.
  Qed.

  Lemma eto_adeq_step (id: Prophecy.ID) (Pr: Prophecy.t):
    ∀ extr, { obs | eto_adeq_rel id Pr extr obs }.
  Proof.
    set (obs_dummy := (scons Pr.(Prophecy.obs_default) ExTr.abort)).
    i. eapply constructive_indefinite_description.
    destruct (et_step_or_spin id Pr extr).
    { (* et_step *)
      induction H; try solve [des; eexists; pfold; econs; et];
      destruct IHet_step; exists x; pstep; auto. }
    { (* et_spin *)
      exists obs_dummy.
      revert_until Pr. pcofix CIH. i. pfold. punfold H0.
      inv H0; econs; auto; right; apply CIH; inv SELF; done. }
    Unshelve. all: exact obs_dummy.
  Qed.

  Lemma adeq_rel_sound (id: Prophecy.ID) (Pr: Prophecy.t):
    ∀ extr obs, sclos Pr.(Prophecy.Obs) (eto_adeq_rel id Pr) extr obs
      -> extrace_obs_stream_relation id Pr extr obs.
  Proof.
    pcofix CIH. i. pfold. punfold H0. inv H0.
    inv INF; last done. punfold REL.
    inv REL; auto;
    try solve [inv STEP; last done; econs; right; apply CIH; pstep; econs; [done | auto]].
    { destruct (classic (∃ fn', fn = prefix_proph +:+ fn')).
      { (* eto_interact_proph_wrong_type *)
        des; subst; auto. }
      { (* eto_interact_else *)
        inv STEP. econs; auto. right. apply CIH. pstep. econs; [done | auto]. }}
    { inv STEP; last done. destruct (classic (∃ fn', fn = prefix_proph +:+ fn')).
      { destruct H1 as [fn' ?]. destruct (decide (fn' = ProphecyName.resolve)).
        { subst. destruct (classic (∃ (id': Prophecy.ID) (o : SAny.t), id' <> id ∧ arg = (id', o)↑)).
          { (* eto_interact_resolve_other *)
            des; subst. apply eto_interact_resolve_other; auto.
            right. apply CIH. pstep. econs; [done | auto]. }
          { (* eto_interact_proph_dummy *)
            econs. ii. des; subst; try done.
            - apply H1. exists id', o. auto.
            - destruct (decide (id' = id)); subst.
              + apply NE. split; auto. exists o'; auto.
              + apply H1. exists id', (o'↑↑); auto. }}
        { destruct (classic ((fn' = ProphecyName.new ∨ fn' = ProphecyName.close)
                            ∧ ∃ (id': Prophecy.ID), arg = id'↑ ∧ id' <> id)).
          { (* eto_interact_new_close_other *)
            des_safe. econs; auto. right. apply CIH. pstep. econs; [done | auto]. }
          { (* eto_interact_proph_dummy *)
            subst. econs. ii. des_safe. des; done. }}}
      { (* eto_interact_else *)
        econs; auto. right. apply CIH. pstep. econs; [done | auto]. }}
  Qed.

  Lemma extrace_has_obs_stream : forall extr id Pr, exists obs_str, extrace_obs_stream_relation id Pr extr obs_str.
  Proof.
    i. destruct (sclos_coind Pr.(Prophecy.Obs) (eto_adeq_step id Pr) extr).
    exists x. apply adeq_rel_sound. auto.
  Qed.

End ETO.

Section TREXTRREL.

  Variant _extr_spin (extr_spin : ExTr.t -> Prop) : ExTr.t -> Prop :=
  | extr_spin_tau t
    (SPIN : extr_spin t)
  : _extr_spin extr_spin (ExTr.tau t)
  
  | extr_spin_choose T x t
    (SPIN : extr_spin t)
  : _extr_spin extr_spin (ExTr.choose T x t)

  | extr_spin_take P t
    (SPIN : extr_spin t)
  : _extr_spin extr_spin (ExTr.take P t)

  | extr_spin_prophecy fn (arg : Any.t) extrtl
    (STEP: extr_spin extrtl)
  : _extr_spin extr_spin (ExTr.interact (obs_io (prefix_proph +:+ fn) arg tt) extrtl)
  .

  Definition extr_spin : _ -> Prop := paco1 _extr_spin bot1.

  Lemma extr_spin_mon : monotone1 _extr_spin.
  Proof using. ii. inv IN; try (sfby econs; eauto). Qed.
  
  Definition not_spin tr :=
  match tr with 
  | Tr.spin => False 
  | _ => True
  end.

  Variant _tr_extr_relationF (coself self : Tr.t -> ExTr.t -> Prop) : Tr.t -> ExTr.t -> Prop :=
  | extr_done retv 
  : _tr_extr_relationF coself self (Tr.done retv) (ExTr.done retv)
  
  | extr_abort
  : _tr_extr_relationF coself self (Tr.abort) (ExTr.abort)
  
  | extr_hang fn I (args : I)
  : _tr_extr_relationF coself self (Tr.hang (@obs_out fn I args)) (ExTr.hang (@obs_out (prefix_io +:+ fn) I args))
  
  | extr_interact fn I O (i : I) (o : O) trtl extrtl
    (TL: coself trtl extrtl)
  : _tr_extr_relationF coself self (Tr.interact (obs_io fn i o) trtl) (ExTr.interact (obs_io (prefix_io +:+ fn) i o) extrtl)
  
  | extr_case_spin extr
    (SPIN: extr_spin extr)
  : _tr_extr_relationF coself self (Tr.spin) extr

  | extr_prophecy_ind fn (arg : Any.t) extrtl tr
    (STEP: self tr extrtl)
  : _tr_extr_relationF coself self tr (ExTr.interact (obs_io (prefix_proph +:+ fn) arg tt) extrtl)
  
  | extr_tau_ind extrtl tr
    (STEP: self tr extrtl)
  : _tr_extr_relationF coself self tr (ExTr.tau extrtl)
  
  | extr_choose_ind T x extrtl tr
    (STEP: self tr extrtl)
  : _tr_extr_relationF coself self tr (ExTr.choose T x extrtl)
  
  | extr_take_ind P extrtl tr
    (STEP: self tr extrtl)
  : _tr_extr_relationF coself self tr (ExTr.take P extrtl)
  .

  Lemma _tr_extr_relationF_mon coself coself' self self'
    (COI : coself <2= coself')
    (LE : self <2= self')
    :
    _tr_extr_relationF coself self <2= _tr_extr_relationF coself' self'.
  Proof.
    i. destruct PR; des; eauto using _tr_extr_relationF.
  Qed.

  Inductive _tr_extr_relation coself tr extr : Prop :=
  | _tr_extr_intro (REL: _tr_extr_relationF coself (_tr_extr_relation coself) tr extr)
  .

  Lemma _tr_extr_relation_tarski coself P
    (SIM : _tr_extr_relationF coself P <2= P)
    :
    _tr_extr_relation coself <2= P.
  Proof.
    fix IH 3. i. inv PR; inv REL; apply SIM; econs; et.
  Qed.

  Definition tr_extr_relation: _ -> _ -> Prop := paco2 _tr_extr_relation bot2. 

  Lemma _tr_extr_relation_mon: monotone2 _tr_extr_relation.
  Proof using.
    ii. eapply _tr_extr_relation_tarski, IN. i. inv PR; eauto using _tr_extr_relation, _tr_extr_relationF.
  Qed.

  Hint Resolve _tr_extr_relation_mon : paco.
  Hint Resolve cpn2_wcompat : paco.

  Lemma tr_extr_relation_ind P
    (SIM : _tr_extr_relationF tr_extr_relation (tr_extr_relation /2\ P) <2= P)
    :
    tr_extr_relation <2= P.
  Proof.
    i. punfold PR.
    assert (SIM' : _tr_extr_relationF tr_extr_relation (tr_extr_relation /2\ P) <2= (tr_extr_relation /2\ P)).
    { i. split; eauto. pstep. econs.
      eapply _tr_extr_relationF_mon, PR0; eauto.
      i. ss. des. punfold PR1. }
    eapply _tr_extr_relation_tarski in SIM'; des; eauto.
    eapply _tr_extr_relation_mon; eauto. i. pclearbot. eauto.
  Qed.

  Definition tr_extr_relation_indC rel :=
    @_tr_extr_relationF bot2 rel.

  Lemma tr_extr_relation_indC_mon : monotone2 tr_extr_relation_indC.
  Proof.
    ii. unfold tr_extr_relation_indC in *.
    inv IN; des; eauto using _tr_extr_relationF.
  Qed.
  Hint Resolve tr_extr_relation_indC_mon : paco.

  Lemma tr_extr_relation_indC_spec:
    tr_extr_relation_indC <3= gupaco2 _tr_extr_relation (cpn2 _tr_extr_relation).
  Proof.
    eapply wrespect2_uclo; eauto with paco.
    econs; eauto with paco. i.
    inv PR; econs; des; subst; ss; eauto 7 using _tr_extr_relationF, _tr_extr_relation_mon, rclo2.
  Qed.

  Hint Constructors _tr_extr_relation : core.
  Hint Unfold tr_extr_relation : core.

  Variant _comp_sim (coself : itree coreE Any.t -> itree coreE Any.t -> Prop)
    : itree coreE Any.t -> itree coreE Any.t -> Prop :=
  | comp_ret retv
  : _comp_sim coself (Ret retv) (Ret retv)

  | comp_tau itr_src itr_tgt
    (NEXT: coself itr_src itr_tgt)
  : _comp_sim coself (tau;; itr_src) (tau;; itr_tgt)

  | comp_choose X ktr_src ktr_tgt
    (NEXT: forall x, coself (ktr_src x) (ktr_tgt x))
  : _comp_sim coself (x <- trigger (Choose X);; ktr_src x) (x <- trigger (Choose X);; ktr_tgt x)

  | comp_take (P : Prop) ktr_src ktr_tgt
    (NEXT: forall x, coself (ktr_src x) (ktr_tgt x))
  : _comp_sim coself (x <- trigger (Take P);; ktr_src x) (x <- trigger (Take P);; ktr_tgt x)

  | comp_io I O fn arg ktr_src ktr_tgt
    (NEXT: forall x, coself (ktr_src x) (ktr_tgt x))
  : _comp_sim coself
      (x <- trigger (@IO I O fn arg);; ktr_src x)
      (x <- trigger (@IO I O (prefix_io +:+ fn) arg);; ktr_tgt x)

  | comp_prophecy fn arg itr_src itr_tgt
    (NEXT: coself itr_src itr_tgt)
    : _comp_sim coself (tau;; itr_src)
        (trigger (@IO Any.t () (prefix_proph +:+ fn) arg);;; tau;; tau;; itr_tgt).

  Definition comp_sim := paco2 _comp_sim bot2.

  Lemma comp_sim_mon : monotone2 _comp_sim.
  Proof using.
    ii. destruct IN; des; eauto using _comp_sim.
  Qed.

  Hint Unfold comp_sim : core.
  Hint Constructors _comp_sim : core.
  Hint Resolve comp_sim_mon: paco.

  (* exco *)

  Definition beh_adeq_state_normal : Type := { '(itr, itr_p, tr) | comp_sim itr itr_p /\ Beh.of_itree itr tr }.

  Definition beh_adeq_cont : Type := list (ExTr._op + Prop).

  Definition beh_adeq_state : Type := beh_adeq_cont * (beh_adeq_state_normal + Tr.t).

  Inductive steps_silent (tr : Tr.t) (itrs_final : itree coreE Any.t * itree coreE Any.t)
  : (itree coreE Any.t * itree coreE Any.t) -> beh_adeq_cont -> Prop :=
  | steps_silent_ret retv
      (RET_OP : tr = Tr.done retv)
      (RET_FINAL : itrs_final = (Ret retv, Ret retv))
    : steps_silent tr itrs_final itrs_final [inl (ExTr._done retv)]

  | steps_silent_abort
      (ABORT_OP : tr = Tr.abort)
    : steps_silent tr itrs_final itrs_final [inl ExTr._abort]

  | steps_silent_hang fn I (i : I) O ktr1 ktr2
      (HANG_OP : tr = Tr.hang (obs_out fn i))
      (HANG_FINAL : itrs_final = ('r : O <- trigger (IO fn i);; ktr1 r, 'r : O <- trigger (IO (prefix_io +:+ fn) i);; ktr2 r))
    : steps_silent tr itrs_final itrs_final [inl (ExTr._hang (obs_out (prefix_io +:+ fn) i))]

  | steps_silent_interact fn I (i : I) O (o : O) ktr1 ktr2 trtl
      (INTERACT_OP : tr = Tr.interact (obs_io fn i o) trtl)
      (INTERACT_FINAL : itrs_final = ('r : O <- trigger (IO fn i);; ktr1 r, 'r : O <- trigger (IO (prefix_io +:+ fn) i);; ktr2 r))
    : steps_silent tr itrs_final itrs_final [inl (ExTr._interact (obs_io (prefix_io +:+ fn) i o))]

  | steps_silent_choose X x l ktr1 ktr2
      (SELF : steps_silent tr itrs_final (ktr1 x, ktr2 x) l)
    : steps_silent tr itrs_final (x <- trigger (Choose X);; ktr1 x, x <- trigger (Choose X);; ktr2 x) ((inl (ExTr._choose X x)) :: l)

  | steps_silent_tau l itr1 itr2
      (SELF : steps_silent tr itrs_final (itr1, itr2) l)
    : steps_silent tr itrs_final (tau;; itr1, tau;; itr2) ((inl ExTr._tau) :: l)

  | steps_silent_take_success (P : Prop) (p : P) l ktr1 ktr2
      (SELF : steps_silent tr itrs_final (ktr1 p, ktr2 p) l)
    : steps_silent tr itrs_final (p <- trigger (Take P);; ktr1 p, p <- trigger (Take P);; ktr2 p) ((inl (ExTr._take P)) :: l)

  | steps_silent_take_ub (P : Prop) (contra : ~ P) ktr1 ktr2
      (UB_FINAL : itrs_final = (p <- trigger (Take P);; ktr1 p, p <- trigger (Take P);; ktr2 p))
    : steps_silent tr itrs_final itrs_final [inr P]

  | steps_silent_proph fn args l itr1 itr2
      (SELF : steps_silent tr itrs_final (tau;; tau;; itr1, tau;; tau;; itr2) l)
    : steps_silent tr itrs_final (tau;; itr1, trigger (@IO Any.t () (prefix_proph +:+ fn) args);;; tau;; tau;; itr2) ((inl (ExTr._interact (obs_io (prefix_proph +:+ fn) args tt))) :: l).

  Definition transition (hd : ExTr._op + Prop) (cont : beh_adeq_state) : ExCoU._co beh_adeq_state :=
    match hd with
    | inl (ExTr._done retv) =>
        ExCoU.ccons (ExTr._done retv) ExTr.void_recT
    | inl ExTr._abort =>
        ExCoU.ccons ExTr._abort ExTr.void_recT
    | inl (ExTr._hang oute) =>
        ExCoU.ccons (ExTr._hang oute) ExTr.void_recT
    | inl (ExTr._interact outine) =>
        ExCoU.ccons (ExTr._interact outine) (fun _ => cont)
    | inl ExTr._tau =>
        ExCoU.ccons ExTr._tau (fun _ => cont)
    | inl (ExTr._choose X x) =>
        ExCoU.ccons (ExTr._choose X x) (fun _ => cont)
    | inl (ExTr._take P) =>
        ExCoU.ccons (ExTr._take P) (fun _ => cont)
    | inr P =>
        ExCoU.ccons (ExTr._take P) (fun _ => cont)
    end.

  Definition dummy_cont : beh_adeq_state_normal.
  Proof.
    econs. instantiate (1 := (Ret tt↑, Ret tt↑, Tr.done tt↑)).
    ss. split; pfold; econs; econs.
  Qed.

  Variant beh_adeq_rel : beh_adeq_state -> ExCoU._co beh_adeq_state -> Prop :=

  | beh_adeq_interact I O fn (args : I) retv ktr1 ktr2 itr1 itr2 hd l evs PF_before PF_after
      (STEP : steps_silent (Tr.interact (obs_io fn args retv) evs)
                ('r : O <- trigger (IO fn args);; ktr1 r, 'r : O <- trigger (IO (prefix_io +:+ fn) args);; ktr2 r)
                (itr1, itr2) (hd :: l))
    : beh_adeq_rel
        ([], inl
           (exist _ (itr1, itr2, Tr.interact (obs_io fn args retv) evs) PF_before))
        (transition hd (l, inl (exist _ (ktr1 retv, ktr2 retv, evs) PF_after)))

  | beh_adeq_hang I O fn (args : I) ktr1 ktr2 itr1 itr2 hd l PF_before
      (STEP : steps_silent (Tr.hang (obs_out fn args))
                ('r : O <- trigger (IO fn args);; ktr1 r, 'r : O <- trigger (IO (prefix_io +:+ fn) args);; ktr2 r)
                (itr1, itr2) (hd :: l))
    : beh_adeq_rel
        ([], inl
           (exist _ (itr1, itr2, Tr.hang (obs_out fn args)) PF_before))
        (transition hd (l, inl dummy_cont))

  | beh_adeq_done r itr1 itr2 hd l PF_before
      (STEP : steps_silent (Tr.done r) (Ret r, Ret r) (itr1, itr2) (hd :: l))
    : beh_adeq_rel
        ([], inl
           (exist _ (itr1, itr2, Tr.done r) PF_before))
        (transition hd (l, inl dummy_cont))

  | beh_adeq_abort itr1 itr2 PF_before
    : beh_adeq_rel
        ([], inl
           (exist _ (itr1, itr2, Tr.abort) PF_before))
        (ExCoU.ccons ExTr._abort ExTr.void_recT)

  | beh_adeq_take_ub tr (P : Prop) (FLS : ¬P) ktr_final1 ktr_final2 itr1 itr2 hd l PF_before
    (STEP : steps_silent tr
              (r <- trigger (Take P);; ktr_final1 r, r <- trigger (Take  P);; ktr_final2 r)
              (itr1, itr2) (hd :: l))
    : beh_adeq_rel
        ([], inl (exist _ (itr1, itr2, tr) PF_before))
        (transition hd (l, inr tr))

  | beh_adeq_ind hd tl state
    : beh_adeq_rel (hd :: tl, state) (transition hd (tl, state))

  | beh_adeq_proph_spin fn args itr itr_p PF PF2
    : beh_adeq_rel
        ([], inl (exist _ ((tau;; itr),
          (trigger (@IO Any.t () (prefix_proph +:+ fn) args);;; tau;; tau;; itr_p),
          Tr.spin) PF))
        (ExCoU.ccons
          (ExTr._interact (obs_io (prefix_proph +:+ fn) args tt))
          (λ _, ([], inl (exist _ (tau;; tau;; itr, tau;; tau;; itr_p, Tr.spin) PF2))))

  | beh_adeq_tau_spin itr itr_p PF PF2
    : beh_adeq_rel
        ([], inl (exist _ ((tau;; itr), (tau;; itr_p), Tr.spin) PF))
        (ExCoU.ccons ExTr._tau
          (λ _, ([], inl (exist _ (itr, itr_p, Tr.spin) PF2))))

  | beh_adeq_choose_spin X x ktr ktr_p PF PF2
    (STEP: Beh.of_itree (ktr x) Tr.spin)
    : beh_adeq_rel
        ([], inl (exist _ ((r <- trigger (Choose X);; ktr r),
          (r <- trigger (Choose X);; ktr_p r),
          Tr.spin) PF))
        (ExCoU.ccons (ExTr._choose X x)
          (λ _, ([], inl (exist _ (ktr x, ktr_p x, Tr.spin) PF2))))

  | beh_adeq_take_spin (P : Prop) (x : P) ktr ktr_p PF PF2
    : beh_adeq_rel
        ([], inl (exist _ ((r <- trigger (Take P);; ktr r),
          (r <- trigger (Take P);; ktr_p r),
          Tr.spin) PF))
        (ExCoU.ccons (ExTr._take P)
          (λ _, ([], inl (exist _ (ktr x, ktr_p x, Tr.spin) PF2))))

  | beh_adeq_ub_ret retv
    : beh_adeq_rel ([], inr (Tr.done retv)) (ExCoU.ccons (ExTr._done retv) ExTr.void_recT)

  | beh_adeq_ub_abort
    : beh_adeq_rel ([], inr Tr.abort) (ExCoU.ccons ExTr._abort ExTr.void_recT)

  | beh_adeq_ub_spin
    : beh_adeq_rel ([], inr Tr.spin) (ExCoU.ccons ExTr._tau (λ _, ([], inr Tr.spin)))

  | beh_adeq_ub_hang I fn args
    : beh_adeq_rel
        ([], inr (Tr.hang (@obs_out fn I args)))
        (ExCoU.ccons (ExTr._hang (@obs_out (prefix_io +:+ fn) I args)) ExTr.void_recT)

  | beh_adeq_ub_io I O fn args retv tr
    : beh_adeq_rel
        ([], inr (Tr.interact (@obs_io fn I O args retv) tr))
        (ExCoU.ccons (ExTr._interact (@obs_io (prefix_io +:+ fn) I O args retv)) (λ _, ([], inr tr))).

  Ltac itree_clarify_all :=
    repeat (
      try match goal with H:(@eq (itree coreE Any.t) _ _) |- _ => itree_clarify H end;
      try match goal with H:(@eq (itree coreE Any.t * itree coreE Any.t) _ _) |- _ => itree_clarify H end
    ).

  Ltac invp H := punfold H; inv H; itree_clarify_all; pclearbot.
    
  Ltac inv_of_itree BEH :=
    punfold BEH; inv BEH;
    match goal with REL:(Beh._of_itreeF _ _ _ _) |- _ => inv REL end;
    itree_clarify_all;
    try solve [match goal with SPIN:(Beh.state_spin _) |- _ => invp SPIN end].

  Ltac inv_beh_adeq :=
    match goal with REL:(beh_adeq_rel _ _) |- _ => inv REL end;
    ss; erewrite ExTr.unfold_extr; ss;
    try match goal with H:(@eq (itree coreE Any.t) _ _) |- _ => itree_clarify H end.

  Lemma beh_tau_bind itr tr
    (SIM: Beh.of_itree (tau;; itr) tr)
    : Beh.of_itree itr tr.
  Proof.
    pfold. inv_of_itree SIM.
    - econs. econs.
    - econs. econs. invp SPIN. pclearbot; done.
    - auto.
  Qed.

  Lemma beh_io_bind {I O} (args: I) (ret: O) fn ktr tr
    (SIM: Beh.of_itree ('x: O <- trigger (@IO _ O fn args);; ktr x)
            (Tr.interact (@obs_io fn I O args ret) tr))
  :
    Beh.of_itree (ktr ret) tr.
  Proof.
    remember (Tr.interact (obs_io fn args ret) tr).
    remember ('x: O <- trigger (@IO _ O fn args);; ktr x) in SIM.
    revert Heqi Heqt.
    pattern i, t.
    eapply Beh.of_itree_ind, SIM. i.
    inv PR; try (rewrite !bind_trigger in H; inv H).
    eapply inj_pair2 in H1, H2, H3, H4. subst. 
    eapply (func_ext_rev ret) in H2. rewrite -H2; eauto.
  Qed.

  Lemma steps_silent_exist tr itr itr_p
    (NS  : tr <> Tr.spin)
    (NA  : tr <> Tr.abort)
    (SIM : comp_sim itr itr_p)
    (BEH : Beh.of_itree itr tr)
    : ∃ itr' itr_p' hd tl,
      steps_silent tr (itr', itr_p') (itr, itr_p) (hd :: tl) /\
      comp_sim itr' itr_p' /\ Beh.of_itree itr' tr.
  Proof.
    depgen itr_p. revert NS NA. pattern itr, tr.
    eapply Beh.of_itree_ind; et. clear BEH tr itr.
    i. inv PR.
    { (* done *)
      invp SIM. eexists _,_,_,_. splits.
      - eapply steps_silent_ret; et.
      - pstep. econs.
      - pstep. econs. econs. }
    { destruct STEP as [BEH IH].
      invp SIM; eapply (IH NS) in NEXT; des; auto.
      { (* tau *)
        eexists _,_,_,_. splits.
        eapply steps_silent_tau; et.
        all: auto. }
      { (* proph *)
        eexists _,_,_,_. splits.
        eapply steps_silent_proph, steps_silent_tau, steps_silent_tau; et.
        all: auto. }}
    { (* hang *)
      invp SIM. eexists _,_,_,_. splits; i; try solve [inv H].
      - eapply steps_silent_hang; et.
      - pstep. econs. auto.
      - pstep. econs. econs. }
    { (* io *)
      invp SIM. eexists _,_,_,_. splits; i.
      - eapply steps_silent_interact; et.
      - pstep. econs. auto.
      - pstep. econs. econs. left. auto. }
    { (* choose *)
      des. invp SIM. hexploit STEP0; et. i. des.
      eexists _,_,_,_. splits; i.
      eapply steps_silent_choose, H.
      all: auto. }
    { (* take *)
      invp SIM. destruct (classic P).
      { (* take success *)
        specialize (STEP H). des. hexploit STEP0; et. i. des.
        eexists _,_,_,_. splits; i.
        eapply steps_silent_take_success; et.
        all: auto. }
      { (* take ub *)
        eexists _,_,_,_. splits; i.
        - eapply steps_silent_take_ub.
          + apply H.
          + refl.
        - pstep; econs. i. exfalso. auto.
        - pstep; econs; econs. i. exfalso. auto. }}
  Qed.

  Variant tr_itr_final : Tr.t -> itree coreE Any.t -> Prop :=
  | tif_ret retv
    : tr_itr_final (Tr.done retv) (Ret retv)
  | tif_abort itr
    : tr_itr_final Tr.abort itr
  | tif_hang fn I O (i : I) ktr
    : tr_itr_final (Tr.hang (obs_out fn i)) (x <- trigger (@IO I O fn i);; ktr x)
  | tif_io fn I O (i : I) (o : O) evs ktr
    : tr_itr_final (Tr.interact (obs_io fn i o) evs) (x <- trigger (@IO I O fn i);; ktr x)
  | tif_ub (P : Prop) (FLS : ~P) tr ktr
    : tr_itr_final tr (x <- trigger (Take P);; ktr x).

  Hint Constructors tr_itr_final : core.

  Lemma steps_silent_aux tr itr itr_p itr' itr_p' l
    (STEPS: steps_silent tr (itr', itr_p') (itr, itr_p) l)
    : tr_itr_final tr itr'.
  Proof.
    induction STEPS; try inv RET_FINAL; itree_clarify_all; subst; auto; econs; auto.
  Qed.

  Lemma steps_silent_aux2 tr itr itr_p itr' itr_p' l
    (SIM: comp_sim itr itr_p)
    (STEPS: steps_silent tr (itr', itr_p') (itr, itr_p) l)
    : comp_sim itr' itr_p'.
  Proof.
    remember (itr', itr_p') as itr_finals.
    remember (itr, itr_p) as itrs.
    depgen itr; depgen itr_p; depgen itr'; depgen itr_p'.
    induction STEPS; i; clarify.
    - invp SIM. eapply IHSTEPS; try refl; auto.
    - invp SIM. eapply IHSTEPS; try refl; auto.
    - invp SIM. depdes H. eapply IHSTEPS; try refl; auto.
    - invp SIM. apply (f_equal (fun y => y tt)) in x. itree_clarify x.
      eapply IHSTEPS; try refl. do 2 (pstep; econs; left). auto.
  Qed.

  Lemma steps_silent_aux3 tr itr itr_p itr' itr_p' l
    (BEH: Beh.of_itree itr' tr)
    (STEPS: steps_silent tr (itr', itr_p') (itr, itr_p) l)
    : Beh.of_itree itr tr.
  Proof.
    remember (itr', itr_p') as itr_finals.
    remember (itr, itr_p) as itrs.
    depgen itr; depgen itr_p; depgen itr'; depgen itr_p'.
    induction STEPS; i; clarify; eapply IHSTEPS in BEH; try refl.
    - pstep; econs; econs. exists x. punfold BEH.
    - pstep; econs; econs. punfold BEH.
    - pstep; econs; econs. i. punfold BEH.
      rewrite (proof_irrelevance P x p). auto.
    - apply beh_tau_bind. auto.
  Qed.

  Lemma beh_adeq_cont_add hd l st op xs args
    (TRN: transition hd (l, st) = ExCoU.ccons op xs)
    (CCL: ∀ idx : SPFU.deg op, ExCoU.cclos beh_adeq_rel (xs idx) (args idx))
    : ExCoU.cclos beh_adeq_rel (hd :: l, st) (ExCoU.cfold (ExCoU.ccons op args)).
  Proof.
    pstep; econs; cycle 1.
    - i. left. apply CCL.
    - rewrite -TRN. econs.
  Qed.

  Lemma beh_adeq_step :
    ∀ beh_st, { ext | beh_adeq_rel beh_st ext }.
  Proof.
    i. eapply constructive_indefinite_description.
    destruct beh_st. destruct b; last (eexists; econs).
    destruct s.
    { (* beh_adeq_state_normal *)
      destruct b, x, p.
      rename i into itr1, i0 into itr2, t into tr, y into PF.
      dup PF. destruct PF0 as [SIM BEH].
      destruct (classic (tr = Tr.spin)), (classic (tr = Tr.abort)); subst.
      { done. }
      { (* spin *)
        apply GSimFacts.behave_spin_spins in BEH.
        invp BEH.
        { invp SIM.
          { (* tau *)
            eexists. eapply beh_adeq_tau_spin.
            Unshelve. split; auto. pstep; econs; econs. apply SPIN. }
          { (* proph *)
            eexists. eapply beh_adeq_proph_spin.
            Unshelve. split.
            - do 2 (pstep; econs; left). apply NEXT.
            - pstep; econs; econs. do 2 (pstep; econs; left). apply SPIN. }}
        { (* choose *)
          invp SIM. destruct SPIN as [x SPIN].
          eexists. eapply beh_adeq_choose_spin.
          pstep; econs; econs. pclearbot. apply SPIN.
          Unshelve. split.
          - apply NEXT.
          - pclearbot. pstep; econs; econs. apply SPIN. }
        { (* take *)
          invp SIM. destruct (classic P).
          { (* success *)
            eexists. eapply beh_adeq_take_spin.
            Unshelve. auto. split; auto. pstep; econs; econs. apply SPIN. }
          { (* ub *)
            eexists. econs; first apply H.
            eapply steps_silent_take_ub; first apply H. refl. }}}
      { (* abort *)
        eexists. econs. }
      { rename H into NS, H0 into NA.
        hexploit steps_silent_exist; et. intros [itr' [itr_p' [hd [tl [SIL [SIM' BEH']]]]]].
        hexploit steps_silent_aux; first apply SIL; intro TIF.
        inv TIF.
        { (* ret *)
          invp SIM'. eexists. econs. apply SIL. }
        { (* hang *)
          invp SIM'. eexists. econs. apply SIL. }
        { (* io *)
          invp SIM'. eexists. econs. apply SIL.
          Unshelve. split; auto. eapply beh_io_bind. apply BEH'. }
        { (* take ub *)
          invp SIM'. eexists. eapply beh_adeq_take_ub.
          - apply FLS.
          - apply SIL. }}}
    { (* ub *)
      destruct t; try solve [eexists; econs].
      { (* hang *)
        destruct e. eexists. econs. }
      { (* io *)
        destruct hd. eexists. econs. }}
  Qed.

  Lemma beh_adeq_rel_sound1_ub_spin :
    ∀ extr, ExCoU.cclos beh_adeq_rel ([], inr Tr.spin) extr ->
      extr_spin extr.
  Proof.
    pcofix CIH. i. invp H0. inv_beh_adeq. depdes H1.
    pstep; econs. right. eapply CIH, INF.
  Qed.

  Lemma beh_adeq_rel_sound1_spin :
    ∀ itr itr_p extr PF,
      ExCoU.cclos beh_adeq_rel ([], inl ((itr, itr_p, Tr.spin) ↾ PF)) extr ->
      extr_spin extr.
  Proof.
    pcofix CIH. i. invp H0. inv REL;
    try solve [depdes H3; erewrite ExTr.unfold_extr; pstep; econs; right; eapply CIH, INF].
    clear CIH.
    rename H into TRN. remember (ExCoU.cfold _) as extr.
    assert (Hcl: ExCoU.cclos beh_adeq_rel (hd :: l, inr Tr.spin) extr).
    { rewrite Heqextr. pstep; econs; cycle 1.
      - i. left. eapply INF.
      - rewrite -TRN. econs. }
    remember (hd :: l) as l'. clear dependent args hd l op.

    depgen extr. induction STEP; i; itree_clarify_all.
    { inv ABORT_OP. }
    1,2,3,5: invp Hcl; inv_beh_adeq; depdes H4; pstep; econs; left; eapply IHSTEP, INF.
    invp Hcl. inv_beh_adeq. depdes H6.
    pstep; econs. left.
    specialize (INF 0%fin). eapply beh_adeq_rel_sound1_ub_spin in INF.
    eapply paco1_mon; first apply INF. i. inv PR.
  Qed.

  Lemma beh_adeq_rel_sound1_ub :
    ∀ tr extr, ExCoU.cclos beh_adeq_rel ([], inr tr) extr ->
      tr_extr_relation tr extr.
  Proof.
    pcofix CIH. i. invp H0. inv_beh_adeq; pstep; econs; try econs.
    - depdes H2. specialize (INF 0%fin). pstep; econs. left.
      apply beh_adeq_rel_sound1_ub_spin, INF.
    - depdes H2. right. eapply CIH, INF.
  Qed.

  Lemma beh_adeq_rel_sound1 :
    ∀ itr itr_p tr PF extr,
      ExCoU.cclos beh_adeq_rel ([], inl (exist _ (itr, itr_p, tr) PF)) extr ->
      tr_extr_relation tr extr.
  Proof.
    pcofix CIH. i. rename H0 into Hccl. invp Hccl. inv REL.
    { (* io *)
      rename H into TRN.
      hexploit beh_adeq_cont_add; [apply TRN | apply INF | intro Hcl].
      remember (ExCoU.cfold _) as extr; remember (hd :: l) as l'.
      clear dependent args hd l op.

      depgen extr. induction STEP; i; itree_clarify_all.
      { inv ABORT_OP. }
      { invp Hcl. inv_beh_adeq. depdes H4.
        pstep; econs; econs. right. eapply CIH. apply INF. }
      all: invp Hcl; inv_beh_adeq; depdes H4; pstep; econs; econs; hexploit IHSTEP; try apply INF; i; punfold H. }
    { (* hang *)
      rename H into TRN.
      hexploit beh_adeq_cont_add; [apply TRN | apply INF | intro Hcl].
      remember (ExCoU.cfold _) as extr; remember (hd :: l) as l'.
      clear dependent args hd l op.

      depgen extr. induction STEP; i; itree_clarify_all.
      { inv ABORT_OP. }
      { invp Hcl. inv_beh_adeq. pstep; econs; econs. }
      all: invp Hcl; inv_beh_adeq; depdes H4; pstep; econs; econs; hexploit IHSTEP; try apply INF; i; punfold H. }
    { (* ret *)
      rename H into TRN.
      hexploit beh_adeq_cont_add; [apply TRN | apply INF | intro Hcl].
      remember (ExCoU.cfold _) as extr; remember (hd :: l) as l'.
      clear dependent args hd l op.

      depgen extr. induction STEP; i; itree_clarify_all.
      { invp Hcl. inv_beh_adeq. pstep; econs; econs. }
      { inv ABORT_OP. }
      all: invp Hcl; inv_beh_adeq; depdes H4; pstep; econs; econs; hexploit IHSTEP; try apply INF; i; punfold H. }
    { (* abort *)
      erewrite ExTr.unfold_extr. pstep; econs; econs. }
    { (* take: ub *)
      rename H into TRN.
      hexploit beh_adeq_cont_add; [apply TRN | apply INF | intro Hcl].
      remember (ExCoU.cfold _) as extr; remember (hd :: l) as l'.
      clear dependent args hd l op.

      depgen extr. induction STEP; i; itree_clarify_all.
      { invp Hcl. inv_beh_adeq. pstep; econs; econs. }
      4: {
        invp Hcl. inv_beh_adeq. depdes H6.
        specialize (INF 0%fin). eapply beh_adeq_rel_sound1_ub in INF.
        pstep; econs; econs. punfold INF.
        eapply _tr_extr_relation_mon; first apply INF.
        i. pclearbot. left. eapply paco2_mon; first apply PR.
        i. inv PR0. }
      all: invp Hcl; inv_beh_adeq; depdes H4; pstep; econs; econs; hexploit IHSTEP; try apply INF; i; punfold H. }
    { (* proph spin *)
      depdes H4.
      erewrite ExTr.unfold_extr. pstep; econs; econs.
      eapply beh_adeq_rel_sound1_spin. pstep. econs; first econs.
      ss. i. left. apply INF. Unshelve. apply PF. }
    { (* tau spin *)
      depdes H4.
      erewrite ExTr.unfold_extr. pstep; econs; econs.
      eapply beh_adeq_rel_sound1_spin. pstep. econs; first econs.
      ss. i. left. apply INF. Unshelve. apply PF. }
    { (* choose spin *)
      depdes H4.
      erewrite ExTr.unfold_extr. pstep; econs; econs.
      eapply beh_adeq_rel_sound1_spin. pstep. econs; first (econs; apply STEP).
      ss. i. left. apply INF. Unshelve. apply PF. }
    { (* take spin *)
      depdes H4.
      erewrite ExTr.unfold_extr. pstep; econs; econs.
      eapply beh_adeq_rel_sound1_spin. pstep. econs; first (econs; apply STEP).
      ss. i. left. apply INF. Unshelve. apply PF. }
  Qed.

  Lemma beh_adeq_rel_sound2 :
    ∀ itr itr_p tr PF extr,
      ExCoU.cclos beh_adeq_rel ([], inl (exist _ (itr, itr_p, tr) PF )) extr
      -> ExBeh.of_itree itr_p extr.
  Proof.
    pcofix CIH. i. rename H0 into Hccl. invp Hccl. inv REL.
    { (* io *)
      rename H into TRN.
      hexploit beh_adeq_cont_add; [apply TRN | apply INF | intro Hcl].
      remember (ExCoU.cfold _) as extr; remember (hd :: l) as l'.
      remember (itr, itr_p) as itrs. remember (_, _) as itr_finals in STEP.
      clear dependent args hd l op PF_before0 PF_before1.
      depgen extr; depgen ktr1; depgen ktr2; depgen itr; depgen itr_p.
      induction STEP; i; itree_clarify_all; invp Hcl; inv_beh_adeq; depdes H4; pstep; econs.
      { right. eapply CIH. apply INF. }
      all: hexploit IHSTEP; try refl; splits; try apply INF; des.
      all: try solve [invp PF; apply NEXT].
      3: { invp PF. depdes H. apply NEXT. }
      5: { invp PF. apply (f_equal (fun y => y tt)) in x.
        itree_clarify x. do 2 (pstep; econs; left). auto. }
      4: { left. rewrite (proof_irrelevance P p0 p). apply H. }
      all: hexploit steps_silent_aux3; try apply STEP; auto; pstep; econs; econs; left; apply PF_after0. }
    { (* hang *)
      rename H into TRN.
      hexploit beh_adeq_cont_add; [apply TRN | apply INF | intro Hcl].
      remember (ExCoU.cfold _) as extr; remember (hd :: l) as l'.
      remember (itr, itr_p) as itrs. remember (_, _) as itr_finals in STEP.
      clear dependent args hd l op PF_before0 PF_before1.
      depgen extr; depgen ktr1; depgen ktr2; depgen itr; depgen itr_p.
      induction STEP; i; itree_clarify_all; invp Hcl; inv_beh_adeq; pstep; econs; depdes H4.
      all: hexploit IHSTEP; try refl; splits; try apply INF; des.
      all: try solve [invp PF; apply NEXT].
      3: { invp PF. depdes H. apply NEXT. }
      5: { invp PF. apply (f_equal (fun y => y tt)) in x.
        itree_clarify x. do 2 (pstep; econs; left). auto. }
      4: { left. rewrite (proof_irrelevance P p0 p). apply H. }
      all: hexploit steps_silent_aux3; try apply STEP; auto; pstep; econs; econs; left; apply PF_after0. }
    { (* ret *)
      rename H into TRN.
      hexploit beh_adeq_cont_add; [apply TRN | apply INF | intro Hcl].
      remember (ExCoU.cfold _) as extr; remember (hd :: l) as l'.
      remember (itr, itr_p) as itrs. remember (_, _) as itr_finals in STEP.
      clear dependent args hd l op PF_before0 PF_before1.
      depgen extr; depgen itr; depgen itr_p.
      induction STEP; i; itree_clarify_all; invp Hcl; inv_beh_adeq; pstep; econs; depdes H4; i.
      all: hexploit IHSTEP; try refl; splits; try apply INF; des.
      all: try solve [invp PF; apply NEXT].
      3: { invp PF. depdes H. apply NEXT. }
      5: { invp PF. apply (f_equal (fun y => y tt)) in x.
        itree_clarify x. do 2 (pstep; econs; left). auto. }
      4: { left. rewrite (proof_irrelevance P p0 p). apply H. }
      all: hexploit steps_silent_aux3; try apply STEP; auto; pstep; econs; econs; left; apply PF_after0. }
    { (* abort *)
      pstep. erewrite ExTr.unfold_extr. econs. }
    { (* take: ub *)
      rename H into TRN.
      hexploit beh_adeq_cont_add; [apply TRN | apply INF | intro Hcl].
      remember (ExCoU.cfold _) as extr; remember (hd :: l) as l'.
      remember (itr, itr_p) as itrs. remember (_, _) as itr_finals in STEP.
      clear dependent args hd l op PF_before0 PF_before1.
      depgen extr; depgen itr; depgen itr_p.
      induction STEP; i; itree_clarify_all; invp Hcl; inv_beh_adeq; pstep.
      5: { rewrite !bind_vis in H0. depdes H0. rewrite -x1. econs. i. exfalso; auto. }
      all: econs; depdes H4; i; hexploit IHSTEP; try refl; splits; try apply INF; des.
      all: try solve [invp PF; apply NEXT].
      5,7: invp PF; depdes H; apply NEXT.
      8,10: invp PF; apply (f_equal (fun y => y tt)) in x;
        itree_clarify x; do 2 (pstep; econs; left); auto.
      7: { left. rewrite (proof_irrelevance P0 p0 p). apply H. }
      all: hexploit steps_silent_aux3; try apply STEP; auto; pstep; econs; econs; i; exfalso; auto. }
    { (* proph spin *)
      depdes H4.
      erewrite ExTr.unfold_extr. pstep; econs. right. eapply CIH. apply INF. }
    { (* tau spin *)
      depdes H4.
      erewrite ExTr.unfold_extr. pstep; econs. right. eapply CIH. apply INF. }
    { (* choose spin *)
      depdes H4.
      erewrite ExTr.unfold_extr. pstep; econs. right. eapply CIH. apply INF. }
    { (* take spin *)
      depdes H4.
      erewrite ExTr.unfold_extr. pstep; econs. right.
      rewrite (proof_irrelevance P p x). eapply CIH. apply INF. }
  Qed.

  Lemma comp_sim_tgt_extr_exists
      itr itr_p tr
      (BEH : Beh.of_itree itr tr)
      (COMP_SIM : comp_sim itr itr_p) :
    exists extr : ExTr.t, tr_extr_relation tr extr ∧ ExBeh.of_itree itr_p extr.
  Proof.
    hexploit (ExCoU.clos_coind beh_adeq_step). i. destruct X.
    eexists x. split.
    - eapply beh_adeq_rel_sound1. apply c.
    - eapply beh_adeq_rel_sound2. apply c.
    Unshelve. exact itr. auto.
  Qed.

End TREXTRREL.

