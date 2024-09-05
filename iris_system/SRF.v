Require Import Basics Program.

Local Notation level := nat.

Module PF.
  
  Class t: Type := {
    shp: Type;
    deg: shp -> forall (Prev:Type), Type;
  }.

End PF.

Coercion PF.shp: PF.t >-> Sortclass.

Module GPF.
  
  Class t: Type := __GATOM: nat -> PF.t.

  Class inG (F: PF.t) (GF: t) : Type := {
    inG_id: nat;
    inG_prf: F = GF inG_id;
  }.

End GPF.

Module SRFMSynG.
  
  Class t: Type := __GATM: GPF.t.

End SRFMSynG.

Module SRFSyn.

  Section SYNTAX.

  Context `{α: SRFMSynG.t}.

  Inductive term {Prev: Type} : Type :=
  | _lift (p: Prev) : term
  | _cur i (op: α i) (args: PF.deg op Prev -> term)
  .

  Fixpoint _t (n : level) : Type :=
    match n with
    | O => Empty_set
    | S m => term (Prev:=_t m) 
    end.

  Definition t_prev (n: level) : Type := _t n.
  
  Definition t (n : level) : Type := t_prev (S n).

  Definition lift {n} (p: t n) : t (S n) := _lift p.
  
  Fixpoint liftn k {n} (p: t n) : t (k+n) :=
    match k return t (k+n) with
    | 0 => p
    | S k' => lift (liftn k' p)
    end.
  
  End SYNTAX.

End SRFSyn.

Module SRFDom.

  Class t : Type := {
      dom: Type;
      void: dom;
    }.

End SRFDom.

Module SRFMSem.

  Section SEM.

  Context `{Δ: SRFDom.t}.
  Context `{α: SRFMSynG.t}.
  Context `{A: PF.t}.

  Class t : Type := 
    sem: forall n (op: A) (args: PF.deg op (SRFSyn.t_prev n) -> SRFSyn.t n) (Args: PF.deg op (SRFSyn.t_prev n) -> SRFDom.dom), SRFDom.dom
  .

  End SEM.
  
End SRFMSem.

Module SRFMSemG.

  Section GSEM.

  Context `{Δ: SRFDom.t}.

  Class t `{α: SRFMSynG.t}: Type := gsem : forall i, SRFMSem.t (A:= α i).

  Class inG (A: PF.t) (α: SRFMSynG.t) (B: @SRFMSem.t _ α A) (β: t) : Type := {
    inG_id: nat;
    inG_prf: existT _ A B = existT _ (α inG_id) (β inG_id);
  }.
  
  End GSEM.

End SRFMSemG.

Module SRFSem.

  Section SEM.

  Context `{Δ: SRFDom.t}.
  Context `{α: SRFMSynG.t}.
  Context `{β: @SRFMSemG.t Δ α}.

  Fixpoint _t n : SRFSyn.t_prev n -> SRFDom.dom :=
    match n with
    | O => fun _ => SRFDom.void
    | S m =>
      fix _t_aux (syn : SRFSyn.t_prev (S m)) : SRFDom.dom :=
        match syn with
        | SRFSyn._lift p => _t m p
        | SRFSyn._cur i op args => β i m op args (compose _t_aux args)
        end
    end.

  Definition t_prev n : SRFSyn.t_prev n -> SRFDom.dom := _t n.
  
  Definition t n : SRFSyn.t n -> SRFDom.dom := t_prev (S n).

  Program Definition cur `{A: PF.t} `{B: @SRFMSem.t Δ α A} `{IN: @SRFMSemG.inG _ A α B β} {n} (op: A) (args: PF.deg op (SRFSyn.t_prev n) -> SRFSyn.t n) : SRFSyn.t n.
    destruct IN. inversion inG_prf. subst.
    exact (SRFSyn._cur inG_id op args).
  Defined.
  
  End SEM.
  
End SRFSem.

Module SRFRed.
  
  Section RED.

  Context `{Δ: SRFDom.t}.
  Context `{α: SRFMSynG.t}.
  Context `{β: @SRFMSemG.t Δ α}.

  Lemma cur `{A: PF.t} `{B: @SRFMSem.t Δ α A} `{IN: @SRFMSemG.inG _ A α B β} n op args :
    SRFSem.t n (SRFSem.cur op args) = B n op args (compose (SRFSem.t n) args).
  Proof.
    destruct IN eqn: EQ. subst. dependent destruction inG_prf. reflexivity.
  Qed.

  Lemma lift_0 t :
    SRFSem.t_prev 1 (SRFSyn._lift t) = SRFDom.void.
  Proof. reflexivity. Qed.

  Lemma lift n (t: SRFSyn.t n) :
    SRFSem.t (S n) (SRFSyn.lift t) = SRFSem.t n t.
  Proof. reflexivity. Qed.

  End RED.

End SRFRed.  

Global Opaque SRFSem.cur.
Global Opaque SRFSem.t.

(** Notations *)

Declare Scope SRF_scope.
Delimit Scope SRF_scope with SRF.
Bind Scope SRF_scope with SRFSyn.t.

Local Open Scope SRF_scope.

Notation "'⟨' op ',' args '⟩'" := (SRFSem.cur op args) : SRF_scope.
Notation "⤉ P" := (SRFSyn.lift P) (at level 20) : SRF_scope.
Notation "'⟦' F ',' n '⟧'" := (SRFSem.t n F).
Notation "'⟦' F '⟧'" := (SRFSem.t _ F).

(* Simple reduction tactics. *)

Global Opaque SRFSyn.t_prev.
Global Opaque SRFSyn.t.

Ltac SRF_red := repeat (
                 try rewrite ! @SRFRed.cur;
                 try rewrite ! @SRFRed.lift;
                 change (SRFSyn.t_prev (S ?n)) with (SRFSyn.t n) in * ).

Ltac SRF_red_all := repeat (
                     try rewrite ! @SRFRed.cur in *;
                     try rewrite ! @SRFRed.lift in *;
                     change (SRFSyn.t_prev (S ?n)) with (SRFSyn.t n) in * ).
