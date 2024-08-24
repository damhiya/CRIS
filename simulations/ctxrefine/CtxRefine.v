Require Export Coqlib sflib Any.
Require Import Behavior.
Require Import Mod Skeleton ModSimFacts.
Require Import PCM IPM HMod ISimCore HModAdequacy.
Require Import ModSim.


Section REFINE.
  Context `{Sk.ld}.

  Definition refines_mod (md_src md_tgt: Mod.t): Prop :=
    Beh.of_program (Mod.compile md_tgt) <1= Beh.of_program (Mod.compile md_src).

  (* original definition of ctx-refinement (remove if not used) *)
  Definition ctx_refines_mod (md_src md_tgt: Mod.t): Prop :=
    forall (ctx: Mod.t),
      refines_mod (Mod.add md_src ctx) (Mod.add md_tgt ctx).

End REFINE.

Section CTX_REFINE.
  (* Definition of ctx refinement in HMod Level. *)
  Context `{Σ: GRA.t}.
  Context `{Sk.ld}.

  Definition refines (md_src md_tgt: HMod.t): Prop :=
    let Ps := md_src.(HMod.get_modsem) md_src.(HMod.sk) in
    let Pt := md_tgt.(HMod.get_modsem) md_tgt.(HMod.sk) in

    forall (rs: Σ) (WFR: URA.wf rs) (WFM: Ps.(HModSem.wf)) (SRC: Ps.(HModSem.initial_cond) rs),
    exists rt, URA.wf rt /\ Pt.(HModSem.wf) /\ Pt.(HModSem.initial_cond) rt /\
    refines_mod (HMod.to_mod md_src rs) (HMod.to_mod md_tgt rt).

  Definition ctx_refines (md_src md_tgt: HMod.t): Prop :=
    forall (ctx: HMod.t),
    refines (HMod.add md_src ctx) (HMod.add md_tgt ctx).

End CTX_REFINE.

(*

Section PROPERTIES.
  Context `{Sk.ld}.

  (*** refines_mod ***)
  Global Program Instance refines_mod_PreOrder: PreOrder refines_mod.
  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. eapply H0. eapply H1. ss. Qed.

  Context `{Σ: GRA.t}.
  (* Context `{_W: CtxWD.t}. *)

  Global Program Instance refines_PreOrder: PreOrder refines.
  Next Obligation.
  (* Admitted. *)
    do 2 r. i. exists rs, SRC.   
      eapply adequacy_mod, adequacy_hmod; ss. 
      econs; ss. i. eapply hmod_sim_refl.
  Qed.
  Next Obligation.
    ii. rr in H0. rr in H1.
    specialize (H0 rs SRC). des.
    specialize (H1 rt TGT). des.
    exists rt0, TGT0.
    r. i. eapply H0. eapply H1. eauto.
  Qed.

  (*** vertical composition ***)
  Global Program Instance ctx_refines_PreOrder: PreOrder ctx_refines.

  Next Obligation. 
    do 3 r. i. exists rs, SRC. 
    eapply adequacy_mod. eapply adequacy_hmod; eauto.
    instantiate (1:= IstProd IstEq IstEq).
    econs; eauto. i. rr. eapply isim_ctx, hmod_sim_refl. 
  Qed.
  Next Obligation. 
    ii. rr in H0. rr in H1.
    specialize (H0 ctx rs SRC). des.
    specialize (H1 ctx rt TGT). des.
    exists rt0, TGT0.
    r. i. eapply H0, H1. eauto.
  Qed.

End PROPERTIES.


*)
