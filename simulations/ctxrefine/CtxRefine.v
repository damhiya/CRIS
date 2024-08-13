Require Export Coqlib sflib Any.
Require Import Behavior.
Require Import Mod Skeleton ModSimFacts.
Require Import PCM IPM HMod ISimCore.
Require Import ModSim.


Section REFINE.
  Context `{Sk.ld}.

  Definition refines_mod (md_src md_tgt: Mod.t): Prop :=
    Beh.of_program (Mod.compile md_tgt) <1= Beh.of_program (Mod.compile md_src).

End REFINE.

Section CTX_REFINE.
  (* Definition of ctx refinement in HMod Level. *)
  Context `{Σ: GRA.t}.
  Context `{Sk.ld}.

  Definition refines (md_src md_tgt: HMod.t): Prop :=
    let Ps := HModSem.initial_cond (md_src.(HMod.get_modsem) md_src.(HMod.sk)) in
    let Pt := HModSem.initial_cond (md_tgt.(HMod.get_modsem) md_tgt.(HMod.sk)) in
    (* (exists r, Ps r) /\ 
    (exists r, Pt r) /\ *)
    (forall rs rt (SRC: Ps rs) (TGT: Pt rt),
      refines_mod (HMod.to_mod md_src rs) (HMod.to_mod md_tgt rt)).

  Definition ctx_refines (md_src md_tgt: HMod.t): Prop :=
    forall (ctx: HMod.t),
      refines (HMod.add md_src ctx) (HMod.add md_tgt ctx).


  (* To be moved *)
  Theorem adequacy_hmod
      (md_src md_tgt: HMod.t) Ist
      (rs rt: Σ) 
      (SIM: HModR.sim md_src md_tgt Ist)
      (SRC: HModSem.initial_cond (md_src.(HMod.get_modsem) md_src.(HMod.sk)) rs)
      (TGT: HModSem.initial_cond (md_tgt.(HMod.get_modsem) md_tgt.(HMod.sk)) rt)
    :
      ModR.sim (HMod.to_mod md_src rs) (HMod.to_mod md_tgt rt).
  Proof.
  Admitted.

    Theorem isim_ctx
            ctx ms1 ms2 Ist
            (SIM: HModSemR.sim ms1 ms2 Ist)
        :
            HModSemR.sim (HModSem.add ms1 ctx) (HModSem.add ms2 ctx) (IstProd Ist IstEq).
    Proof.
    Admitted.
  
  Lemma hmod_sim_refl md:
       HModSemR.sim md md IstEq. 
  Proof. Admitted.

End CTX_REFINE.

Section PROPERTIES.
  Context `{Sk.ld}.

  (*** refines_mod ***)
  Global Program Instance refines_mod_PreOrder: PreOrder refines_mod.
  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. eapply H0. eapply H1. ss. Qed.

  Context `{Σ: GRA.t}.

  Global Program Instance refines_PreOrder: PreOrder refines.
  Next Obligation. Admitted.
    (* do 2 r. i.   
      eapply adequacy_mod, adequacy_hmod; ss. 
      econs; ss. i. eapply hmod_sim_refl.
  
  Qed. *)
  Next Obligation.
    ii. rr in H0. rr in H1. des.
    rr. esplits. 
    { eauto. }
    { eauto. }
    i.
    specialize (H5 rs r2 SRC H4).
    specialize (H3 r2 rt H4 TGT).
    r. i. eapply H5. eapply H3. eauto.
  Admitted.


  (*** vertical composition ***)
  Global Program Instance ctx_refines_PreOrder: PreOrder ctx_refines.

  Next Obligation. 
    do 3 r. i. eapply adequacy_mod. eapply adequacy_hmod; eauto.
    instantiate (1:= IstProd IstEq IstEq).
    econs; eauto. i. rr. eapply isim_ctx, hmod_sim_refl. 
  Qed.
  Next Obligation. do 2 r. i. 
  
  eapply H1. eapply H0. ss. Qed.

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

