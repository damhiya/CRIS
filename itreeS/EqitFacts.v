
(** * Strong bisimulation *)

(** Because [itree] is a coinductive type, the naive [eq] relation
    is too strong: most pairs of "morally equivalent" programs
    cannot be proved equal in the [eq] sense.
[[
    (* Not provable *)
    Goal (cofix spin := Tau spin) = Tau (cofix spin := Tau spin).
    Goal (cofix spin := Tau spin) = (cofix spin2 := Tau (Tau spin2)).
]]
    As an alternative, we define a weaker, coinductive notion of equivalence,
    [eqit], which can be intuitively thought of as a form of extensional
    equality. We shall rely extensively on setoid rewriting.
 *)

(* begin hide *)
From Stdlib Require Import
     Structures.Orders (* Hint Unfold is_true *)
     Program
     Setoid
     Morphisms
     Relations.

From Paco Require Import paco.

From ITreeS Require Import
     Basics
     ITreeDefinition
     Eqit
     EqAxiom.

From CRIS Require Import sflib.

Local Open Scope itree_scope.


(** ** Coinductive reasoning with Paco *)

(** Similarly to the way we deal with cofixpoints explained in
    [Core.ITreeDefinition], coinductive properties are defined in two steps,
    as greatest fixed points of monotone relation transformers.

    - a _relation transformer_, a.k.a. _generating function_,
      is a function mapping relations to relations
      [gf : (i -> i -> Prop) -> (i -> i -> Prop)];
    - _monotonicity_ is with respect to relations ordered by set inclusion
      (a.k.a. implication, when viewed as predicates)
      [(r1 <2= r2) -> (gf r1 <2= gf r2)];
    - the Paco library provides a combinator [paco2] defining the greatest
      fixed point [paco2 gf] when [gf] is indeed monotone.

    By thus avoiding [CoInductive] to define coinductive properties,
    Paco spares us from thinking about guardedness of proof terms,
    instead encoding a form of productivity visibly in types.
 *)

(* Local Coercion is_true : bool >-> Sortclass. *)

Section eqit_eq.

Context {E: iEvent} {R: Type}.

Lemma eqitF_inv_VisF_r {sim}
    t1 (X2: Type) (e2 : E X2) (k2 : X2 -> itree E R)
  : eqitF sim t1 (VisF e2 k2) ->
    (exists k1, t1 = VisF e2 k1 /\ forall v, sim (k1 v) (k2 v)).
Proof.
  refine (fun H =>
    match H in eqitF _ _ t2 return
      match t2 return Prop with
      | VisF e2 k2 => _
      | _ => True
      end
    with
    | EqVis _ _ _ _ _ => _
    | _ => _
    end); try exact I.
  eauto.
Qed.

Lemma eqitF_inv_VisF {sim}
    (X: Type) (e : E X) (k1 : X -> itree E R) (k2 : X -> _)
  : eqitF sim (VisF e k1) (VisF e k2) ->
    forall x, sim (k1 x) (k2 x).
Proof.
  intros H. dependent destruction H. assumption.
Qed.

#[global] Instance Reflexive_eqitF (sim : itree E R -> itree E R -> Prop)
: Reflexive sim -> Reflexive (eqitF sim).
Proof.
  red. destruct x; constructor; eauto with itree.
Qed.

Lemma eq_is_bisim t1 t2:
  t1 = t2 -> @eqit E R t1 t2.
Proof.
  intros; subst. revert t2.
  ginit. gcofix CIH. gstep; intros.
  repeat red. destruct (observe t2); eauto with paco itree.
Qed.

End eqit_eq.

Hint Resolve eq_is_bisim : core.

(** ** Eta-expansion *)

Lemma itree_eta_ {E R} (t : itree E R) : t = (go (_observe t)).
Proof.
  eapply bisim_is_eq.
  ginit. gstep. red. simpl. unfold observe. destruct (_observe t); econstructor.
  - gfinal. right. eapply eq_is_bisim. eauto.
  - intros. gfinal. right. eapply eq_is_bisim. eauto.
Qed.

Lemma itree_eta {E R} (t : itree E R) : t = go (observe t).
Proof. apply itree_eta_. Qed.

Lemma simpobs {E R} {ot} {t: itree E R} (EQ: ot = observe t): t ≅ go ot.
Proof.
  subst. rewrite (itree_eta t). simpl. apply eq_is_bisim. eauto.
Qed.

Lemma bind_ret_l {E} {R S: Type} (r : R) (k : R -> itree E S) :
  ITree.bind (Ret r) k = k r.
Proof.
  rewrite (itree_eta (ITree.bind _ k)). simpl.
  setoid_rewrite <-itree_eta. eauto.
Qed.

Lemma bind_tau {E} {R U: Type} t (k: U -> itree E R) :
  ITree.bind (Tau t) k = Tau (ITree.bind t k).
Proof.
  rewrite (itree_eta (ITree.bind _ k)). simpl. reflexivity.
Qed.

Lemma bind_vis {E: iEvent} {V: Type} {R U: Type} (e: E V) (ek: V -> itree E U) (k: U -> itree E R) :
  ITree.bind (Vis e ek) k = Vis e (fun x => ITree.bind (ek x) k).
Proof.
  rewrite (itree_eta (ITree.bind _ k)). simpl. reflexivity.
Qed.

Lemma unfold_aloop {E: iEvent} {A B: Type} (f : A -> itree E (A + B)%type) (x : A) :
  ITree.iter f x =
    ITree.bind (f x) (fun lr => ITree.on_left lr l (Tau (ITree.iter f l))).
Proof.
  rewrite (itree_eta (ITree.iter _ _)).
  rewrite (itree_eta (ITree.bind _ _)).
  simpl. reflexivity.
Qed.

(* end hide *)

Section eqit_closure.

Context {E: iEvent} {R: Type}.

Inductive eqit_bind_clo (r: itree E R -> itree E R -> Prop)  :
  itree E R -> itree E R -> Prop :=
| pbc_intro_h (U: Type) t k1 k2
      (REL: forall u: U, r (k1 u) (k2 u))
  : eqit_bind_clo r (ITree.bind t k1) (ITree.bind t k2)
.
Hint Constructors eqit_bind_clo : itree.

Lemma eqit_clo_bind:
  eqit_bind_clo <3= gupaco2 eqit_ id.
Proof.
  intros rr. gcofix CIH. intros. destruct PR.
  rewrite (itree_eta t). destruct (observe t).
  - rewrite !bind_ret_l. gfinal. eauto.
  - rewrite !bind_tau. gstep. econstructor. gfinal. left.
    eapply CIH. econstructor; eauto.
  - rewrite !bind_vis. gstep. econstructor. gfinal. left.
    eapply CIH. econstructor; eauto.
Qed.

End eqit_closure.

Arguments eqit_clo_bind : clear implicits.
#[global] Hint Constructors eqit_bind_clo : itree.

(** ** Equations for core combinators *)

Notation bind_ t k :=
  match observe t with
  | RetF r => k%function r
  | VisF e ke => Vis e (fun x => ITree.bind (ke x) k)
  | TauF t => Tau (ITree.bind t k)
  end.

Lemma unfold_bind {E R S} (t : itree E R) (k : R -> itree E S)
  : ITree.bind t k = bind_ t k.
Proof.
  rewrite (itree_eta (ITree.bind _ _)). simpl.
  destruct (observe t); eauto.
  setoid_rewrite <-itree_eta. eauto.
Qed.

Lemma bind_trigger {E: iEvent} {U: Type} {R: Type} (e : E U) (k : U -> itree E R)
  : ITree.bind (ITree.trigger e) k = Vis e (fun x => k x).
Proof.
  eapply bisim_is_eq.
  rewrite unfold_bind; cbn.
  pstep.
  constructor.
  intros; red. left. rewrite bind_ret_l. apply eq_is_bisim. eauto.
Qed.

Lemma unfold_iter {E} {A B: Type} (f : A -> itree E (A + B)%type) (x : A) :
  (ITree.iter f x) = ITree.bind (f x) (fun lr => ITree.on_left lr l (Tau (ITree.iter f l))).
Proof.
  rewrite unfold_aloop. reflexivity.
Qed.

Lemma bind_ret_r {E R} :
  forall s : itree E R,
    ITree.bind s (fun x => Ret x) = s.
Proof.
  intros. eapply bisim_is_eq. revert s.
  ginit. gcofix CIH. intros.
  gstep. red. s. destruct (observe s).
  - econstructor.
  - econstructor. gfinal. eauto.
  - econstructor. intros. gfinal. eauto.
Qed.

Lemma bind_bind {E R S T} :
  forall (s : itree E R) (k : R -> itree E S) (h : S -> itree E T),
    ITree.bind (ITree.bind s k) h = ITree.bind s (fun r => ITree.bind (k r) h).
Proof.
  intros. eapply bisim_is_eq. revert s k h.
  ginit. gcofix CIH. intros.
  gstep. red. s. destruct (observe s); s.
  - unfold observe. eapply Reflexive_eqitF.
    ii. gfinal. right. eapply paco2_mon_bot; eauto.
    apply eq_is_bisim. eauto.
  - econstructor. gfinal. eauto.
  - econstructor. intros. gfinal. eauto.
Qed.

Lemma map_map {E} {R S T: Type}: forall (f : R -> S) (g : S -> T) (t : itree E R),
    ITree.map g (ITree.map f t) = ITree.map (fun x => g (f x)) t.
Proof.
  unfold ITree.map. intros. rewrite bind_bind.
  f_equal. extensionalities. apply @bind_ret_l.
Qed.

Lemma bind_map {E} {R S T: Type}: forall (f : R -> S) (k: S -> itree E T) (t : itree E R),
    ITree.bind (ITree.map f t) k = ITree.bind t (fun x => k (f x)).
Proof.
  unfold ITree.map. intros. rewrite bind_bind.
  f_equal. extensionalities. apply bind_ret_l.
Qed.

Lemma map_bind {E} {X Y Z: Type} (t: itree E X) (k: X -> itree E Y) (f: Y -> Z) :
  (ITree.map f (ITree.bind t k)) = ITree.bind t (fun x => ITree.map f (k x)).
Proof.
  unfold ITree.map. apply bind_bind.
Qed.

Lemma map_ret {E} {A B: Type} (f : A -> B) (a : A) :
  @ITree.map E _ _ f (Ret a) = Ret (f a).
Proof.
  unfold ITree.map. rewrite bind_ret_l; reflexivity.
Qed.

Lemma map_tau {E} {A B: Type} (f : A -> B) (t : itree E A) :
    @ITree.map E _ _ f (Tau t) = Tau (ITree.map f t).
Proof.
  unfold ITree.map. rewrite bind_tau; reflexivity.
Qed.

#[global] Hint Rewrite @bind_ret_l : itree.
#[global] Hint Rewrite @bind_ret_r : itree.
#[global] Hint Rewrite @bind_tau : itree.
#[global] Hint Rewrite @bind_vis : itree.
#[global] Hint Rewrite @bind_map : itree.
#[global] Hint Rewrite @map_ret : itree.
#[global] Hint Rewrite @map_tau : itree.
#[global] Hint Rewrite @bind_bind : itree.

Lemma eqit_inv_bind_ret:
  forall {E: iEvent} {X R: Type}
    (ma : itree E X) (kb : X -> itree E R) (b: R),
    ITree.bind ma kb = Ret b ->
    exists a, ma = (Ret a) /\ (kb a) = (Ret b).
Proof.
  intros. eapply eq_is_bisim in H.
  punfold H.
  unfold eqit_ in *.
  cbn in *.
  remember (observe (ITree.bind ma kb)) as otl.
  remember (RetF b) as tr.
  revert ma kb Heqotl b Heqtr.
  induction H; try discriminate.
  intros; subst.
  inv Heqtr.
  unfold observe, _observe in Heqotl; cbn in Heqotl.
  destruct (observe ma) eqn:Ema; try discriminate.
  exists r. split.
  - rewrite (itree_eta ma), Ema. eauto.
  - rewrite (itree_eta (kb r)). f_equal. eauto.
Qed.

Lemma eqit_inv_bind_vis:
  forall {E} {A B: Type} {X: Type}
    (ma : itree E A) (kab : A -> itree E B) (e : E X)
    (kxc : X -> itree E B),
    (ITree.bind ma kab) = (Vis e kxc) ->
    (exists (kxa : X -> itree E A), (ma = (Vis e kxa)) /\
       forall (x:X), (ITree.bind (kxa x) kab) = (kxc x)) \/
    (exists (a : A), ma = (Ret a) /\ (kab a) = (Vis e kxc)).
Proof.
  intros. eapply eq_is_bisim in H. punfold H. unfold eqit_ in H. cbn in *.
  remember (observe (ITree.bind ma kab)) as tl.
  remember (VisF e kxc) as tr.
  revert ma kab Heqtl kxc Heqtr.
  induction H; try discriminate. intros. pclearbot.
  assert (k1 = k2).
  { extensionalities. eapply bisim_is_eq. eapply REL. }
  subst. dependent destruction Heqtr.
  simpl in *. destruct (observe ma) eqn:Ema; try discriminate.
  - right. eexists. split.
    + rewrite (itree_eta ma), Ema. eauto.
    + rewrite (itree_eta (kab r)). f_equal. eauto.
  - dependent destruction Heqtl.
    left. eexists. split; eauto.
    rewrite (itree_eta ma), Ema. eauto.
Qed.

Lemma eqit_inv_bind_tau:
  forall {E} {A B: Type}
    (ma : itree E A) (kab : A -> itree E B) (tc: itree E B),
    (ITree.bind ma kab) = (Tau tc) ->
    (exists (ma' : itree E A), ma = (Tau ma') /\ (ITree.bind ma' kab) = tc) \/
    (exists (a : A), ma = (Ret a) /\ (kab a) = (Tau tc)).
Proof.
  intros. eapply eq_is_bisim in H. punfold H. unfold eqit_ in H. cbn in H.
  remember (observe (ITree.bind ma kab)) as tl.
  remember (TauF tc) as tr.
  revert ma kab Heqtl Heqtr.
  induction H; try discriminate; intros. pclearbot.
  eapply bisim_is_eq in REL. subst.
  dependent destruction Heqtr.
  simpl in *. destruct (observe ma) eqn:Ema; try discriminate.
  - right; exists r; split.
    + rewrite (itree_eta ma), Ema. eauto.
    + rewrite (itree_eta (kab r)). f_equal. eauto.
  - dependent destruction Heqtl.
    left. eexists. split; eauto.
    rewrite (itree_eta ma), Ema. eauto.
Qed.
