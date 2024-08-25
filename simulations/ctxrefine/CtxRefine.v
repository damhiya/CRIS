Require Export Coqlib sflib Any.
Require Import Behavior.
Require Import Mod Skeleton ModSimFacts.
Require Import PCM IPM HMod ISimCore.
Require Import ModSim.


Section REFINE.

  Definition refines_modsem (ms_src ms_tgt: ModSem.t): Prop :=
    Beh.of_program (ModSem.compile ms_tgt) <1=
    Beh.of_program (ModSem.compile ms_src)
  .

  (* Definition refines_mod (md_src md_tgt: Mod.t): Prop := *)
  (*   <<EQV: Sk.equiv md_src.(Mod.sk) md_tgt.(Mod.sk) >> *)
  (*   /\ *)
  (*   <<REF:              *)
  (*     forall sk (EQV: Sk.equiv md_tgt.(Mod.sk) sk), *)
  (*     Beh.of_program (Mod.compile md_tgt sk) <1= *)
  (*     Beh.of_program (Mod.compile md_src sk) *)
  (*   >>. *)

  (* original definition of ctx-refinement (remove if not used) *)
  (* Definition ctx_refines_mod (md_src md_tgt: Mod.t): Prop := *)
  (*   forall (ctx: Mod.t), *)
  (*   refines_mod (Mod.add md_src ctx) (Mod.add md_tgt ctx). *)

End REFINE.

Section CTX_REFINE.
  (* Definition of ctx refinement in HMod Level. *)
  Context `{Σ: GRA.t}.

  Definition refines (mps: HMod.modc) (mpt: HMod.modc) : Prop :=
    let ms := mps.1 in let Ps := mps.2 in
    let mt := mpt.1 in let Pt := mpt.2 in

    <<EQV: Sk.equiv ms.(HMod.sk) mt.(HMod.sk)>> /\
    <<REF:
      forall sk (EQV: Sk.equiv mt.(HMod.sk) sk) (SKWF: Sk.wf sk)
        rs
        (WFR: URA.wf rs) (SRC: Own rs ⊢ Ps sk) 
        (WFM: HModSem.wf (ms.(HMod.modsem) sk)),
      exists rt,
        URA.wf rt /\ (Own rt ⊢ Pt sk)%I /\
        HModSem.wf (mt.(HMod.modsem) sk) /\
        refines_modsem
          (HModSem.to_mod (ms.(HMod.modsem) sk) rs)
          (HModSem.to_mod (mt.(HMod.modsem) sk) rt)>>.

  Definition ctx_refines (mps mpt: HMod.modc): Prop :=
    forall (ctx: HMod.modc),
      refines (mps.1 ★ ctx.1, mps.2 ∗∗ ctx.2)
              (mpt.1 ★ ctx.1, mpt.2 ∗∗ ctx.2).

End CTX_REFINE.

Section PROPERTIES.

  (*** refines_modsem ***)
  Global Program Instance refines_modsem_PreOrder: PreOrder refines_modsem.
  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. eapply H. eapply H0. ss. Qed.

  Context `{Σ: GRA.t}.

  Global Program Instance refines_PreOrder: PreOrder refines.
  Next Obligation.
    split.
    { rr. refl. }
    ii. exists rs. esplits; eauto. refl.
  Qed.
  Next Obligation.
    split.
    { rr. etrans. apply H. apply H0. }
    ii. destruct H, H0. des.
    hexploit (H1 sk).
    { etrans; eauto. } { eauto. } { eauto. } { eauto. } { eauto. }
    i. des.
    hexploit (H2 sk).
    { etrans; eauto. refl. } { eauto. } { eauto. } { eauto. } { eauto. }
    i; des.
    exists rt0. esplits; eauto.
    etrans; eauto.
  Qed.

  Lemma ctx_refines_refines mcs mct
    (REF: ctx_refines mcs mct)
    :
    refines mcs mct.
  Proof.
    i. specialize (REF HMod.empty_mc).
    destruct mcs, mct. ss.
    rewrite !hmod_add_empty_r in REF.
    destruct REF. split; eauto.
    ii. des. ss. hexploit H0; eauto.
    { iIntros "H". iSplit; eauto. iApply SRC. eauto. }
    i; des; esplits; eauto.
    iIntros "H". iPoseProof (H2 with "H") as "(? & _)". eauto.
  Qed.

  (*** vertical composition ***)
  
  Global Program Instance ctx_refines_PreOrder: PreOrder ctx_refines.
  Next Obligation.
    r. r. i. refl.
  Qed.
  Next Obligation.
    r. r. i. etrans.
    - apply H.
    - apply H0.
  Qed.
  
  (*** commutativity ***)
  
  Lemma ctx_refines_comm (ma mb: HMod.t) P:
    ctx_refines (HMod.add ma mb, P) (HMod.add mb ma, P).
  Proof.
  Admitted.

  (*** weakening for initial condition ***)

  Lemma ctx_refines_cond_weaken (m: HMod.t) (P Q: Sk.t -> iProp)
    (IMPL: forall sk, P sk -∗ Q sk)
    :
    ctx_refines (m, P) (m, Q).
  Proof.
    split.
    - rr. refl.
    - ii. ss. exists rs. esplits; eauto.
      + iIntros "H". iPoseProof (SRC with "H") as "(X & Y)".
        iFrame. iApply IMPL. eauto.
      + refl.
  Qed.
  
  (*** frame rules ***)

  Lemma ctx_refines_frameR ms Ps mt Pt mc
    (REFA: ctx_refines (ms, Ps) (mt, Pt))
    :
    ctx_refines (ms ★ mc, Ps) (mt ★ mc, Pt).
  Proof.
    ii. specialize (REFA (HMod.add mc ctx.1, ctx.2)). ss.
    rewrite !hmod_add_assoc in *. eauto.
  Qed.

  Lemma ctx_refines_frameL ms Ps mt Pt mc
    (REFA: ctx_refines (ms, Ps) (mt, Pt))
    :
    ctx_refines (mc ★ ms, Ps) (mc ★ mt, Pt).
  Proof.
    etrans. { eapply ctx_refines_comm. }
    etrans. { eapply ctx_refines_frameR. apply REFA. }
    apply ctx_refines_comm.
  Qed.

  (*** frame rule for initial condition ***)

  Lemma ctx_refines_cond_frameR (ms mt: HMod.t) Ps Pt Q
    (REF: ctx_refines (ms, Ps) (mt, Pt))
    :
    ctx_refines (ms, Ps ∗∗ Q)%I (mt, Pt ∗∗ Q)%I.
  Proof.
    ii. specialize (REF (ctx.1, HMod.add_c Q ctx.2)).
    destruct ctx. unfold HMod.add_c in *. ss.
    destruct REF. split; eauto.
    ii. ss. des. hexploit H0; eauto.
    { iIntros "H". iPoseProof (SRC with "H") as "((? & ?) & ?)".
      unfold HMod.add_c. iFrame. }
    i; des. esplits; eauto.
    { iIntros "H". iPoseProof (H2 with "H") as "(? & (? & ?))".
      unfold HMod.add_c. iFrame. }
  Qed.

  Lemma ctx_refines_cond_frameL (ms mt: HMod.t) Ps Pt Q
    (REF: ctx_refines (ms, Ps) (mt, Pt))
    :
    ctx_refines (ms, Q ∗∗ Ps)%I (mt, Q ∗∗ Pt)%I.
  Proof.
    etrans; [|etrans]; cycle 1.
    { apply ctx_refines_cond_frameR with (Q:=Q) in REF. apply REF. }
    { eapply ctx_refines_cond_weaken. i. iIntros "(H1 & H2)". iFrame. }
    { eapply ctx_refines_cond_weaken. i. iIntros "(H1 & H2)". iFrame. }
  Qed.
  
  (*** horizontal composition ***)

  Lemma ctx_refines_compose_hor msa Psa mta Pta msb Psb mtb Ptb
    (REFA: ctx_refines (msa, Psa) (mta, Pta))
    (REFB: ctx_refines (msb, Psb) (mtb, Ptb))
    :
    ctx_refines (msa ★ msb, Psa ∗∗ Psb)
                (mta ★ mtb, Pta ∗∗ Ptb).
  Proof.
    etrans.
    - eapply ctx_refines_frameR, ctx_refines_cond_frameR. apply REFA.
    - eapply ctx_refines_frameL, ctx_refines_cond_frameL. apply REFB. 
  Qed.

  (*** mixed composition ***)

  Lemma ctx_refines_compose_mix msa Psa mta Pta msb Psb mtb Ptb mc
    (REFA: ctx_refines (msa ★ mc, Psa) (mta ★ mc, Pta))
    (REFB: ctx_refines (msb ★ mc, Psb) (mtb ★ mc, Ptb))
    :
    ctx_refines (msa ★ msb ★ mc, Psa ∗∗ Psb)
                (mta ★ mtb ★ mc, Pta ∗∗ Ptb).
  Proof.
    etrans.
    { eapply ctx_refines_frameL, ctx_refines_cond_frameL. apply REFB. }
    etrans.
    { eapply ctx_refines_frameL, ctx_refines_comm. }
    etrans.
    { rewrite <-hmod_add_assoc.
      eapply ctx_refines_frameR, ctx_refines_cond_frameR. apply REFA. }
    rewrite hmod_add_assoc.
    apply ctx_refines_frameL, ctx_refines_comm.
  Qed.

End PROPERTIES.
