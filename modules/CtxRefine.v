Require Export Coqlib sflib.
Require Import Behavior.
Require Import Mod Skeleton.
Require Import ModSemFacts.
  
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

  (*** horizontal composition ***)
  Theorem refines_add
        (md0_src md0_tgt md1_src md1_tgt: Mod.t)
        (SIM0: ctx_refines md0_tgt md0_src)
        (SIM1: ctx_refines md1_tgt md1_src)
    :
        <<SIM: ctx_refines (Mod.add md0_tgt md1_tgt) (Mod.add md0_src md1_src)>>
  .
  Proof. 
    ii. r in SIM0. r in SIM1. 
    pose proof ModFacts.add_comm as COMM. 
    pose proof ModFacts.add_assoc as ASSOC. 
    pose proof ModFacts.add_assoc_rev as ASSOC'. 
    r in COMM. r in ASSOC. r in ASSOC'.
    apply ASSOC'. 
    apply SIM0.
    apply ASSOC. apply COMM. apply ASSOC. apply COMM.
    apply SIM1.
    apply ASSOC. apply COMM. apply ASSOC.
    apply PR.
  Qed.

  Theorem refines_proper_r
    (mds0_src mds0_tgt: list Mod.t) (ctx: Mod.t)
    (SIM0: ctx_refines (Mod.add_list mds0_tgt) (Mod.add_list mds0_src))
  :
    <<SIM: ctx_refines (Mod.add (Mod.add_list mds0_tgt) (ctx)) (Mod.add (Mod.add_list mds0_src) (ctx))>>
  .
  Proof.
    ii. r in SIM0.
    apply ModFacts.add_assoc_rev. apply ModFacts.add_assoc in PR.
    apply SIM0. apply PR. 
  Qed.

  Theorem refines_proper_l
    (mds0_src mds0_tgt: list Mod.t) (ctx: Mod.t)
    (SIM0: ctx_refines (Mod.add_list mds0_tgt) (Mod.add_list mds0_src))
  :
    <<SIM: ctx_refines (Mod.add ctx (Mod.add_list mds0_tgt)) (Mod.add ctx (Mod.add_list mds0_src))>>
  .

  Proof.
    ii. r in SIM0.
    pose proof ModFacts.add_comm as COMM.
    apply COMM. apply COMM in PR.
    apply ModFacts.add_assoc. apply ModFacts.add_assoc_rev in PR.
    apply COMM. apply COMM in PR.
    apply SIM0. apply PR.  
  Qed.

  Lemma refines_close: ctx_refines <2= refines_closed.
  Proof. 
    ii. specialize (PR Mod.empty). ss.
    pose proof ModFacts.add_empty_r as EMP.
    r in EMP.
    apply EMP with (x0 := x2) in PR.
    2: { apply ModFacts.add_empty_rev_r. et. } 
    apply PR.
  Qed.

  Lemma refines_empty 
    (md: Mod.t)
  :
    <<SIM: ctx_refines md (Mod.add md Mod.empty)>>
  .
  Proof. 
    ii. 
    pose proof ModFacts.add_comm as COMM. 
    pose proof ModFacts.add_assoc as ASSOC. 
    apply COMM. apply COMM in PR. apply ModFacts.add_empty_rev_r in PR.
    apply ASSOC. et.
  Qed.

  Lemma refines_empty_rev
  (md: Mod.t)
  :
  <<SIM: ctx_refines (Mod.add md Mod.empty) md>>
  .
  Proof. 
    ii. 
    pose proof ModFacts.add_comm as COMM. 
    pose proof ModFacts.add_assoc_rev as ASSOC'. 
    apply COMM. apply COMM in PR. apply ASSOC' in PR. apply ModFacts.add_empty_r in PR.
    et.
  Qed.

  (*** horizontal composition ***)
   Theorem refines_list_add
         (s0 s1 t0 t1: list Mod.t)
         (SIM0: ctx_refines_list t0 s0)
         (SIM1: ctx_refines_list t1 s1)
     :
       <<SIM: ctx_refines_list [Mod.add (Mod.add_list t0) (Mod.add_list t1)] [Mod.add (Mod.add_list s0) (Mod.add_list s1)]>>
   .
   Proof.
    r. unfold ctx_refines_list. eapply refines_add; et.
   Qed.

   Corollary refines_list_pairwise
             (mds0_src mds0_tgt: list Mod.t)
             (FORALL: List.Forall2 (fun md_src md_tgt => ctx_refines_list [md_src] [md_tgt]) mds0_src mds0_tgt)
     :
       ctx_refines_list mds0_src mds0_tgt.
   Proof.
    induction FORALL; ss.
    hexploit refines_list_add.
    { eapply H0. }
    { eapply IHFORALL. }
    r. i.
    induction l, l'; et.
    { r in H1. unfold ctx_refines_list in H1. ii. apply refines_empty in PR. apply H1. unfold Mod.add_list.
      unfold Mod.add_list in PR. apply PR. }
    { r in H1. unfold ctx_refines_list in H1. ii. unfold Mod.add_list in H1 at 2 5 6. apply H1 in PR.
      unfold Mod.add_list in PR. apply refines_empty_rev in PR. apply PR. }
   Qed.

   Lemma refines_list_eq (mds0 mds1: list Mod.t)
     :
       ctx_refines_list mds0 mds1 <-> ctx_refines (Mod.add_list mds0) (Mod.add_list mds1).
   Proof.
     split.
     { ii. eapply H0. auto. }
     { ii. eapply H0. auto. }
   Qed.

End PROPERTIES.
