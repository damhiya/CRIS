Require Import Setoid.
Require Import Paco.paco.
Require Import IndefiniteDescription.
Require Import FunctionalExtensionality.
Require Import List.
Require Import Program.
From stdpp Require Import fin.

(***

General Construction

**)

Module SPF.

  Class t: Type := {
    I: Type;
    shp: I -> Type;
    deg: forall i, shp i -> (I -> Type);
  }.

End SPF.

Module ExCo.
Section ExCo.
  
Context `{C: SPF.t}.

Notation "X >-> Y" := (forall i, X i -> Y i) (at level 100).
Notation "X ~~ Y" := (forall i, X i -> Y i -> Prop) (at level 100).

Variant _co {self: SPF.I -> Type} {i: SPF.I} : Type :=
  | ccons (op: SPF.shp i) (args: SPF.deg i op >-> self)
.
Arguments _co self: clear implicits.

CoInductive co : SPF.I -> Type :=
| cfold {i} (c: _co co i): co i
.

CoFixpoint cfix {X} (f: X >-> _co X) {i} (x: X i) : co i :=
  match f i x with
  | ccons op args => cfold (ccons op (fun _ idx => cfix f (args _ idx)))
  end.

Lemma cunfold
  {i} (c: co i)
  :
  c = match c with cfold c => cfold c end.
Proof. destruct c. eauto. Qed.

Lemma cfix_unfold
  X (f: X >-> _co X) i (x: X i)
  :
  cfix f x = match f i x with ccons op args => cfold (ccons op (fun _ idx => cfix f (args _ idx))) end.
Proof.
  rewrite (cunfold (cfix f x)). simpl.
  destruct (f _ x). eauto.
Qed.

Variant _cclos {X} (R: X ~~ _co X) (self: X ~~ co) : X ~~ co :=
| cclos_intro
    i x op xs args
    (REL: R i x (ccons op xs))
    (INF: forall j idx, self j (xs j idx) (args j idx))
  :
  _cclos R self i x (cfold (ccons op args))
.
Hint Constructors _cclos: paco.

Definition cclos {X} R i x c := paco3 (@_cclos X R) bot3 i x c.

Lemma cclos_mon X R:
  monotone3 (@_cclos X R).
Proof.
  red. intros. dependent destruction IN.
  econstructor; eauto.
Qed.

Hint Unfold cclos: paco.
Hint Resolve cclos_mon: paco.

Definition clos_choose {X} {R: X ~~ _co X}
  (STEP: forall i x, exists ci, R i x ci) i (x: X i) : _co X i.
Proof.
  specialize (STEP i x).
  eapply constructive_indefinite_description in STEP.
  destruct STEP.
  exact x0.
Defined.

Lemma clos_coind {X} {R: X ~~ _co X}
  (STEP: forall i x, exists ci: _co X i, R i x ci):
  forall i x, exists c: co i, cclos R i x c.
Proof.
  intros. exists (cfix (clos_choose STEP) x).
  revert i x. pcofix CIH. intros.
  rewrite cfix_unfold. unfold clos_choose at 1.
  destruct (constructive_indefinite_description _ _).
  destruct x0.
  pstep. econstructor; eauto.
Qed.

End ExCo.
End ExCo.

Hint Constructors ExCo._cclos: paco.
Hint Unfold ExCo.cclos: paco.
Hint Resolve ExCo.cclos_mon: paco.

Arguments ExCo._co {C} self.
Arguments ExCo.ccons {C self i} op args.
Arguments ExCo.cfold {C i} c.

Module SPF0.

  Class t: Type := {
    shp: Type;
    deg: shp -> Type;
  }.

End SPF0.

Module ExCo0.
Section ExCo0.

Context `{C: SPF0.t}.

Variant _co {self: Type} : Type :=
  | ccons (op: SPF0.shp) (args: SPF0.deg op -> self)
.
Arguments _co self: clear implicits.

CoInductive co : Type :=
| cfold (c: _co co): co
.

CoFixpoint cfix {X} (f: X -> _co X) (x: X) : co :=
  match f x with
  | ccons op args => cfold (ccons op (fun idx => cfix f (args idx)))
  end.

Lemma cunfold
  (c: co)
  :
  c = match c with cfold c => cfold c end.
Proof. destruct c. eauto. Qed.

Lemma cfix_unfold
  X (f: X -> _co X) (x: X)
  :
  cfix f x = match f x with ccons op args => cfold (ccons op (fun idx => cfix f (args idx))) end.
Proof.
  rewrite (cunfold (cfix f x)). simpl.
  destruct (f x). eauto.
Qed.

Variant _cclos {X} (R: X -> _co X -> Prop) (self: X -> co -> Prop) : X -> co -> Prop :=
| cclos_intro
    x op xs args
    (REL: R x (ccons op xs))
    (INF: forall idx, self (xs idx) (args idx))
  :
  _cclos R self x (cfold (ccons op args))
.
Hint Constructors _cclos: paco.

Definition cclos {X} R x c := paco2 (@_cclos X R) bot2 x c.

Lemma cclos_mon X R:
  monotone2 (@_cclos X R).
Proof.
  red. intros. dependent destruction IN.
  econstructor; eauto.
Qed.

Hint Unfold cclos: paco.
Hint Resolve cclos_mon: paco.

Definition clos_choose {X} {R: X -> _co X -> Prop}
  (STEP: forall x, exists ci, R x ci) (x: X) : _co X.
Proof.
  specialize (STEP x).
  eapply constructive_indefinite_description in STEP.
  destruct STEP.
  exact x0.
Defined.

Lemma clos_coind {X} {R: X -> _co X -> Prop}
  (STEP: forall x, exists ci: _co X, R x ci):
  forall x, exists c: co, cclos R x c.
Proof.
  intros. exists (cfix (clos_choose STEP) x).
  revert x. pcofix CIH. intros.
  rewrite cfix_unfold. unfold clos_choose at 1.
  destruct (constructive_indefinite_description _ _). 
  destruct x0.
  pstep. econstructor; eauto.
Qed.

End ExCo0.
End ExCo0.

Hint Constructors ExCo0._cclos: paco.
Hint Unfold ExCo0.cclos: paco.
Hint Resolve ExCo0.cclos_mon: paco.

Arguments ExCo0._co {C} self.
Arguments ExCo0.ccons {C self} op args.
Arguments ExCo0.cfold {C} c.

Section Stream.

Variable T: Type.

Variant stream_shp : Type :=
| scons_ (t: T)
.
Arguments stream_shp : clear implicits.

Definition stream_deg (op: @stream_shp) : Type :=
  match op with
  | scons_ t => fin 1
  end.
Arguments stream_deg : clear implicits.

Instance stream_spf : SPF0.t :=
  {| SPF0.shp := stream_shp
  ;  SPF0.deg := stream_deg
  |}.

Definition stream := ExCo0.co.

Definition _scons {X} (t: T) (s: X) : ExCo0._co X :=
  ExCo0.ccons (scons_ t) (fun _ => s).

Definition scons (t: T) (s: stream) : stream :=
  ExCo0.cfold (_scons t s).

Definition hd (s: stream) : T :=
  match s with
  | ExCo0.cfold (ExCo0.ccons (scons_ t) args) => t
  end.

Definition tl (s: stream) : stream :=
  match s with
  | ExCo0.cfold (ExCo0.ccons (scons_ t) args) => args (0%fin)
  end.
  
Lemma stream_unfold (s: stream):
  s = scons (hd s) (tl s).
Proof.
  destruct s, c, op. simpl. unfold scons, _scons. repeat f_equal.
  extensionality idx. repeat red in idx.
  dependent destruction idx; eauto. inversion idx.
Qed.

End Stream.

Arguments _scons {T X}.
Arguments scons {T}.

(***

Application

**)

Section Simulation.

  Variable Event: Type.
  Variable evrel: Event -> Event -> Prop.
  Variable State: Type.
  Variable step: State -> list Event -> State -> Prop.

  Definition trace := list Event.
  
  Definition inftrace := stream Event.

  Fixpoint trace_app (tr: trace) (ti: inftrace) :=
    match tr with
    | nil => ti
    | e :: tr' => scons e (trace_app tr' ti)
    end.

  Inductive star: State -> trace -> State -> Prop :=
  | star_refl s
    : star s nil s
  | star_step s tr s0 ti s'
      (STEP: step s tr s0)
      (STAR: star s0 ti s')
    : star s (tr ++ ti) s'
  .

  Lemma star_trans s tr s' tr' s''
      (STAR: star s tr s')
      (STAR': star s' tr' s''):
    star s (tr ++ tr') s''.
  Proof.
    revert tr' s'' STAR'. induction STAR; eauto.
    intros. rewrite <-app_assoc. eauto using star.
  Qed.
  
  (* Definition of a coinductive relation: [forever] *)
  
  Variant _forever (self: State -> inftrace -> Prop) : State -> inftrace -> Prop :=
    | forever_intro s tr s' ti ti'
        (NZ: tr <> nil)
        (STAR: star s tr s')
        (INF: self s' ti')
        (EQ: ti = trace_app tr ti')
      : _forever self s ti
  .
  Hint Constructors _forever: paco.

  Definition forever s ti := paco2 _forever bot2 s ti.

  Lemma forever_mon:
    monotone2 _forever.
  Proof. pmonauto. Qed.

  Hint Unfold forever: paco.
  Hint Resolve forever_mon: paco.

  (* Definition of a coinductive relation: [infrel] *)

  Variant _infrel (self: inftrace -> inftrace -> Prop) : inftrace -> inftrace -> Prop :=
    | infrel_intro trS trT tiS' tiT' tiS tiT
        (NZ: trS <> nil)
        (STAR: Forall2 evrel trS trT)
        (INF: self tiS' tiT')
        (EQ: (tiS, tiT) = (trace_app trS tiS',trace_app trT tiT'))
      : _infrel self tiS tiT
  .
  Hint Constructors _infrel: paco.

  Definition infrel tiS tiT := paco2 _infrel bot2 tiS tiT.

  Lemma infrel_mon:
    monotone2 _infrel.
  Proof. pmonauto. Qed.

  Hint Unfold infrel: paco.
  Hint Resolve infrel_mon: paco.

  (* Definition of a coinductive relation: [simul] *)
  
  Variant _simul (self: State -> State -> Prop) : State -> State -> Prop :=
    | simul_intro sS sT
        (SIM: forall trT sT' (STEP: step sT trT sT'),
          exists trS sS', star sS trS sS'
                          /\ Forall2 evrel trS trT
                          /\ self sS' sT')
      : _simul self sS sT
  .
  Hint Constructors _simul: paco.

  Definition simul sS sT := paco2 _simul bot2 sS sT.

  Lemma simul_mon:
    monotone2 _simul.
  Proof.
    econstructor. intros. destruct IN.
    edestruct SIM as [trS [sS' [? [? ?]]]]; eauto 10.
  Qed.

  Hint Unfold simul: paco.
  Hint Resolve simul_mon: paco.

  (* The main lemma reasoning about one step of a simulation *)
  Lemma simul_adequate_step
      sS sT tiT
      (SIM: simul sS sT)
      (INF: forever sT tiT):
    exists trT sT' tiT' trS  sS',
      trS <> nil /\
      tiT = trace_app trT tiT' /\
      Forall2 evrel trS trT /\
      star sS trS sS' /\
      simul sS' sT' /\
      forever sT' tiT'.
  Proof.
    punfold INF. inversion_clear INF. subst. pclearbot.
    exists tr, s', ti'.
    cut (exists trS sS', Forall2 evrel trS tr /\ star sS trS sS' /\ simul sS' s' /\ forever s' ti').
    { intros. destruct H as [? [? [? ?]]].
      exists x, x0. split; eauto.
      intro. apply NZ. subst. inversion H. eauto. }
    clear NZ. move STAR before step. revert sS SIM ti' INF0.
    induction STAR; intros.
    { exists nil, sS. do 2 (split; eauto using star). }
    
    punfold SIM. inversion_clear SIM.
    specialize (SIM0 _ _ STEP).
    destruct SIM0 as [trS [sS' [? []]]]. pclearbot.
    edestruct IHSTAR as [trS' [sS'' [? [? []]]]]; eauto.
    exists (trS ++ trS'), sS''.
    eauto 7 using Forall2_app, star_trans.
  Qed.
  
  (**
     Adequacy with the above technique
   **)

  (* We will turn the above lemma into the form appropriate for our technique. *)

  Definition adeq_state : Type :=
    trace * { '(sS,sT,tiT) | simul sS sT /\ forever sT tiT }.

  Variant adeq_rel: adeq_state -> ExCo0._co adeq_state -> Prop :=
    | adeq_rel_cons eS trS a
      :
      adeq_rel (eS::trS, a) (_scons eS (trS, a))
               
    | adeq_rel_nil trS sS sT tiT PF eS sS' sT' tiT' PF' trT
        (TIT: tiT = trace_app trT tiT')
        (EREL: Forall2 evrel (eS::trS) trT)
        (STAR: star sS (eS::trS) sS')
      :
      adeq_rel (nil, exist _ (sS, sT, tiT) PF) (_scons eS (trS, exist _ (sS', sT', tiT') PF')).
  Hint Constructors adeq_rel.

  (* convert [simul_adequate_step] into an appropriate form. *)
  Lemma simul_adequate_step':
    forall (x: adeq_state), exists sx, adeq_rel x sx.
  Proof.
    intros [tr [[[sS sT] tiT] [SIM INF]]].
    destruct tr; cycle 1.
    { exists (_scons e (tr, exist _ (sS,sT,tiT) (conj SIM INF))). eauto. }
    edestruct simul_adequate_step
        as [trT [sT' [tiT' [trS [sS' [? [? [? [? []]]]]]]]]]; eauto.
    destruct trS as [|eS trS].
    { exfalso. apply H. eauto. }
    exists (_scons eS (trS, exist _ (sS',sT',tiT') (conj H3 H4))). eauto.
  Qed.

  (* A key property about [cclos Event adeq_rel]. *)
  Lemma cclos_adeq_rel_unfold trS a s
      (REL: ExCo0.cclos adeq_rel (trS, a) s):
    exists s', s = trace_app trS s' /\ ExCo0.cclos adeq_rel (nil, a) s'.
  Proof.
    revert a s REL. induction trS; simpl; eauto.
    intros. destruct a0 as [[[sS sT] tiT] [SIM INF]]. destruct s as [[[t] ?]].
    punfold REL. dependent destruction REL. dependent destruction REL.
    specialize (INF0 (0%fin)). pclearbot.    
    specialize (IHtrS _ _ INF0). destruct IHtrS as [s' [? ?]].
    exists s'. split; eauto.
    rewrite (stream_unfold _ (ExCo0.cfold _)). simpl. rewrite H. eauto.
  Qed.
  
  Theorem simul_adequate sS sT tiT
      (SIM: simul sS sT)
      (INF: forever sT tiT):
    exists tiS: inftrace, forever sS tiS /\ infrel tiS tiT.
  Proof.
    (* Obtain an infinte trace [s] satisfying [sinf_clos Event adeq_rel] from [simul_adequate_step']. *)
    destruct (ExCo0.clos_coind simul_adequate_step' (nil, exist _ (sS, sT, tiT) (conj SIM INF))) as [s SAT].
    exists s. split; revert s sT sS tiT SIM INF SAT.

    (* prove [forever sS s] from [sinf_clos Event adeq_rel]. *)
    { pcofix CIH. intros. punfold SAT. dependent destruction SAT.
      destruct op as [eS].
      specialize (INF0 (0%fin)). pclearbot.
      dependent destruction REL.
      destruct (cclos_adeq_rel_unfold _ _ _ INF0) as [s' []].
      pstep. destruct PF'.
      econstructor; cycle 1; eauto.
      rewrite (stream_unfold _ (ExCo0.cfold _)). simpl. rewrite H. eauto.
    }

    (* prove [infrel s tiT] from [sinf_clos Event adeq_rel]. *)
    { pcofix CIH. intros. punfold SAT. dependent destruction SAT.
      destruct op as [eS].
      specialize (INF0 (0%fin)). pclearbot.
      dependent destruction REL.
      destruct (cclos_adeq_rel_unfold _ _ _ INF0) as [s' []].
      pstep. destruct PF'.
      econstructor; cycle 1; eauto.
      rewrite (stream_unfold _ (ExCo0.cfold _)). simpl. rewrite H. eauto.
    }
  Qed.

End Simulation.

