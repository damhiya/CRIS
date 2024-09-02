From stdpp Require Import coPset gmap namespaces.
Require Import sflib.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.
Require Import Coq.Logic.ClassicalEpsilon.

Require Import Coqlib PCM IPM SRF sProp World.
Local Notation univ_id := positive.
Local Notation level := nat.

Module WD.

  Section WD.

  Context `{_W: CtxSL.t}.
  Context `{_W0: @GRA.inG OwnIRA Σ}.
  Context `{_W1: @GRA.inG OwnERA Γ}.
  Context `{_W2: @GRA.inG OwnDRA Γ}.

  Variant shape : Type :=
  | _ownI (u: univ_id) (i: positive)
  | _ownI_auth (u: univ_id) (keys: list positive)
  | _ownI_rest (u: univ_id) (b: level)
  | _ownI_free (eu: univ_id)
  .

  Definition degree (s: shape) (sProp: Type) : Type :=
    match s with
    | _ownI u i => fin 1
    | _ownI_auth u keys => positive
    | _ownI_rest u b => fin 0
    | _ownI_free u => fin 0
    end.

  Global Instance syntax: PF.t := {
      shp := shape;
      deg := degree;
    }.

  Definition interp n (s: shape) : (degree s (SRFSyn.t_prev n) -> SRFSyn.t n) -> (degree s (SRFSyn.t_prev n) -> iProp) -> iProp :=
    match s with
    | _ownI u i => fun syn _ =>
        OwnI u n i (syn 0%fin)
    | _ownI_auth u keys => fun syn _ =>
        OwnI_auth u n (list_to_map (map (fun i => (i, syn i)) keys))
    | _ownI_rest u b => fun _ _ =>
        OwnI_rest u b
    | _ownI_free eu => fun _ _ =>
        OwnM (empty_worldsR eu (fun _ => (fun n => @Auth.black (_ ==> URA.agree (SRFSyn.t n))%ra (fun _ => None)) : URA.pointwise_dep _) : OwnIRA)
    end.

  Global Instance t: SRFMSem.t := interp.

  Context `{_W3: @SRFMSemG.inG _ _ _ t β}.

  Definition ownI u n i (p: SRFSyn.t n) : SRFSyn.t n :=
    ⟨ _ownI u i, fun _ => p ⟩%SRF.

  Definition ownI_auth u n (I: gmap positive (SRFSyn.t n)) : SRFSyn.t n :=
    ⟨ _ownI_auth u (map_to_list I).*1, fun i => or_else (I !! i) emp⟩%SRF.

  Definition ownI_rest u b : SRFSyn.t b :=
    ⟨ _ownI_rest u b, fun a => match a with end ⟩%SRF.

  Definition ownI_free eu {n} : SRFSyn.t n :=
    ⟨ _ownI_free eu , fun a => match a with end ⟩%SRF.

  Definition ownE (u: univ_id) {n} (E: coPset) : SRFSyn.t n :=
    (<ownm> (OwnER u E))%SRF.

  Definition ownD (u: univ_id) {n} (D: gset positive) : SRFSyn.t n :=
    (<ownm> (OwnDR u D))%SRF.

  Definition ownD_auth (u: univ_id) {n} : SRFSyn.t n :=
    (∃ D : τ{⇣gset positive}, <ownm> (OwnD_authR u D))%SRF.

  Definition inv_satall u n (I : gmap positive (SRFSyn.t n)) : SRFSyn.t n :=
    ([∗ n map] i ↦ p ∈ I, (p ∗ ownD u {[i]}) ∨ ownE u {[i]})%SRF.

  Definition wsat u n : SRFSyn.t (S n) :=
    (∃ I : τ{ST.gmapT Φ}, (⤉ ownI_auth u n I) ∗ (⤉ inv_satall u n I))%SRF.

  Definition empty_worlds (eu: univ_id) {n} : SRFSyn.t n :=
    (<ownm> (empty_worldsR eu (fun _ => Some ⊤ : CoPset.t) : OwnERA) ∗
     <ownm> (empty_worldsR eu (fun _ => Auth.black (Some ∅ : Gset.t)) : OwnDRA) ∗
     ownI_free eu).

  Definition free_universes {n} : SRFSyn.t n :=
    (∃ eu: τ{⇣ univ_id}, empty_worlds eu)%SRF.

  Fixpoint wsats u b : SRFSyn.t b :=
    match b with
    | 0 => emp%SRF
    | S n => (wsat u n ∗ ⤉ wsats u n)%SRF
    end.

  (* Interface for the user *)

  Definition world u b E : SRFSyn.t b :=
    wsats u b ∗ ownE u E ∗ ownD_auth u ∗ free_universes.

  Definition free_worlds u b : SRFSyn.t b := ownI_rest u b.

  Definition closed_world u b E : SRFSyn.t b :=
    free_worlds u b ∗ world u b E.

  Definition inv u (n : level) (N : namespace) p :=
    (∃ i: τ{⇣positive}, ⌜i ∈ (↑N : coPset)⌝ ∧ ownI u n i p)%SRF.

  Definition FUpd u b (A : SRFSyn.t b) (E1 E2 : coPset) (P : SRFSyn.t b) : SRFSyn.t b :=
    A ∗ world u b E1 -∗ |==> (A ∗ world u b E2 ∗ P).

  End WD.

End WD.

Module CtxWD.

  Class t
    `{_C: CtxSL.t}
    `{_C: @GRA.inG OwnIRA Σ}
    `{_C: @SRFMSemG.inG _ _ _ WD.t β}
    `{_C: @GRA.inG OwnERA Γ}
    `{_C: @GRA.inG OwnDRA Γ}
    := ctxWD: unit.

End CtxWD.

Module WDRed.
  Section RED.

  Context `{_C: CtxWD.t}.

  Lemma ownI_auth u n I  :
    SRFSem.t n (WD.ownI_auth u n I) = OwnI_auth u n I.
  Proof.
    unfold WD.ownI_auth. SRF_red_all. ss. unfold OwnI_auth, OwnI_authR.
    do 4 f_equal. extensionality i. f_equal.
    rewrite -{1 3}(list_to_map_to_list I).
    destruct (list_to_map (map_to_list I) !! i) eqn: EQ; cycle 1.
    - apply not_elem_of_list_to_map_2 in EQ.
      apply not_elem_of_list_to_map_1.
      rewrite map_map. ss. rewrite map_id. eauto.
    - apply elem_of_list_to_map_2 in EQ.
      apply elem_of_list_to_map_1.
      + rewrite map_map. s. rewrite map_id.
        apply NoDup_fmap_fst, NoDup_map_to_list.
        apply map_to_list_unique.
      + rewrite ->map_map, list_to_map_to_list.
        assert (L := EQ). apply elem_of_map_to_list in L.
        assert (X := EQ). apply elem_of_list_In in X.
        apply (in_map (λ x, (x.1, or_else (I !! x.1) emp%SRF))) in X. ss.
        apply elem_of_list_In.
        rewrite L in X. ss.
  Qed.

  Lemma wsat u n:
    SRFSem.t (S n) (WD.wsat u n) = wsat u n.
  Proof.
    unfold WD.wsat, wsat. SL_red. f_equal.
    extensionality I. SL_red. SRF_red.
    rewrite ownI_auth. f_equal.
    unfold WD.inv_satall, inv_satall.
    SL_red. f_equal. extensionalities i p.
    SL_red. unfold WD.ownD, WD.ownE.
    SL_red_ownm. eauto.
  Qed.

  Lemma wsats u b:
    SRFSem.t b (WD.wsats u b) = wsats u b.
  Proof.
    unfold wsats. induction b; ss.
    - SL_red. eauto.
    - SL_red. SRF_red. rewrite IHb. rewrite wsat. eauto.
  Qed.

  (* User Interface *)

  Lemma world u b E :
    SRFSem.t b (WD.world u b E) = world u b E.
  Proof.
    unfold WD.world, WD.ownE, WD.ownD, WD.ownD_auth, WD.free_universes, WD.empty_worlds, WD.ownI_free, world.
    SL_red. SL_red_ownm. rewrite wsats. f_equal. unfold OwnE. f_equal. f_equal.
    - unfold OwnD_auth. f_equal. extensionality X. SL_red_ownm. eauto.
    - unfold free_universes. f_equal. extensionality eu. ss.
      SL_red. SL_red_ownm. SRF_red. eauto.
  Qed.

  Lemma free_worlds u b :
    SRFSem.t b (WD.free_worlds u b) = free_worlds u b.
  Proof.
    unfold WD.free_worlds, free_worlds, WD.ownI_rest. SRF_red. eauto.
  Qed.

  Lemma closed_world u b E :
    SRFSem.t b (WD.closed_world u b E) = closed_world u b E.
  Proof.
    unfold WD.closed_world, closed_world. SL_red.
    rewrite ->free_worlds, world. eauto.
  Qed.

  Lemma inv u n N p :
    SRFSem.t n (WD.inv u n N p) = inv u n N p.
  Proof.
    unfold WD.inv, inv, WD.ownI. SL_red. f_equal. extensionality i.
    SL_red. SRF_red. eauto.
  Qed.

  Definition FUpd u b A E1 E2 P :
    SRFSem.t b (WD.FUpd u b A E1 E2 P) = FUpd u b ⟦A⟧ E1 E2 ⟦P⟧.
  Proof.
    Local Transparent FUpd.
    unfold WD.FUpd, FUpd. SL_red. rewrite !world. eauto.
  Qed.

  End RED.
End WDRed.

Global Opaque WD.world.
Global Opaque world.
Global Opaque WD.free_worlds.
Global Opaque free_worlds.
Global Opaque WD.inv.
Global Opaque inv.
Global Opaque WD.FUpd.
Global Opaque FUpd.

Ltac WD_red := repeat (
                   try rewrite ! @WDRed.world;
                   try rewrite ! @WDRed.free_worlds;
                   try rewrite ! @WDRed.closed_world;
                   try rewrite ! @WDRed.inv;
                   try rewrite ! @WDRed.FUpd
                 ).

Ltac WD_red_all := repeat (
                       try rewrite ! @WDRed.world in *;
                       try rewrite ! @WDRed.free_worlds in *;
                       try rewrite ! @WDRed.closed_world in *;
                       try rewrite ! @WDRed.inv in *;
                       try rewrite ! @WDRed.FUpd in *
                     ).
