Require Export Coqlib sflib.
Require Import Behavior.
Require Import Mod Skeleton.
  
Section CTX_REFINE.
  Context `{Sk.ld}.
  (* Contexts can be simplified as a single module (by module-linking) *)
  Definition ctx_refines (md_tgt md_src: Mod.t): Prop :=
    forall (ctx: Mod.t),
      Beh.of_program (Mod.compile (Mod.add md_tgt ctx)) <1=
      Beh.of_program (Mod.compile (Mod.add md_src ctx)).

  Definition refines_closed (md_tgt md_src: Mod.t): Prop :=
    Beh.of_program (Mod.compile md_tgt) <1= Beh.of_program (Mod.compile md_src).

  Definition ctx_refines_list (md_tgt md_src: list Mod.t): Prop :=
    ctx_refines (Mod.add_list md_tgt) (Mod.add_list md_src).

End CTX_REFINE.

Section PROPERTIES.
  Context `{Sk.ld}.

  (*** vertical composition ***)
  Global Program Instance refines_PreOrder: PreOrder ctx_refines.

  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. eapply H1. eapply H0. ss. Qed.

  Global Program Instance refines2_PreOrder: PreOrder ctx_refines_list.
  Next Obligation.
    ii. ss.
  Qed.
  Next Obligation.
    ii. eapply H0 in PR. eapply H1 in PR. eapply PR.
  Qed.

  Global Program Instance refines_closed_PreOrder: PreOrder refines_closed.
  Next Obligation. ii; ss. Qed.
  Next Obligation. ii; ss. eapply H1. eapply H0. eauto. Qed.

End PROPERTIES.

