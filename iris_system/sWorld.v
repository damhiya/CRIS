From stdpp Require Import coPset gmap namespaces.
Require Import sflib.
From iris Require Import bi.big_op.
Require Import Coq.Logic.ClassicalEpsilon.
Require Export World.

(* TODO : move these to separate files *)
Local Notation univ_id := positive.
Local Notation level := nat.

Section syn_inv.
  Context `{!CtxSL.t Σ Γ α β τ, !invGSΓ Γ}.

  Variant syn_inv_shape : Type :=
  | _ownI (u : univ_id) (i : positive)
  | _ownI_auth (u : univ_id) (keys : gset positive) (* TODO : gsets? *)
  | _wsat_auth (u : univ_id) (n)
  (* | _free_worlds (u : univ_id) (b : level) *)
  (* | _empty_universes (eu : univ_id) *)
  .

  Definition inv_degree (s : inv_shape) (sProp : Type) : Type :=
    match s with
    (* | _OwnI u i => fin 1
    | _OwnI_auth u keys => positive
    | _free_worlds u b => fin 0
    | _empty_universes u => fin 0 *)
    | _inv u n N p => fin 0
    | _wsats u n E => fin 0
    end.

  Global Instance inv_syntax : PF.t := {
      shp := inv_shape;
      deg := inv_degree;
    }.

  Definition inv_interp_aux n (s : inv_shape)
      : (inv_degree s (SRFSyn.t_prev n) → SRFSyn.t n) → (inv_degree s (SRFSyn.t_prev n) → iProp Σ)
        → iProp Σ :=
    match s with
    (* | _OwnI u i => fun syn _ =>
        OwnI u n i (syn 0%fin)
    | _OwnI_auth u keys => fun syn _ =>
        OwnI_auth u n (list_to_map ((fun i => (i, syn i)) <$> keys))
    | _free_worlds u b => fun _ _ =>
        free_worlds u b
    | _empty_universes eu => fun _ _ =>
        empty_universes eu *)
    | _inv u n N p => λ _ _, inv u n N p
    | _wsats u n E => λ _ _, wsats u n E
    end.

  Global Instance inv_interp : SRFIntpM.t := inv_interp_aux.

  Context `{_W3 : @SRFIntp.inG SL.domain inv_syntax α inv_interp β}.

  (* Definition OwnI u n i (p : SRFSyn.t n) : SRFSyn.t n := *)
    (* ⟨ _OwnI u i, fun _ => p ⟩%SRF. *)
  (* Definition OwnI_auth u n (I : gmap positive (SRFSyn.t n)) : SRFSyn.t n := *)
    (* ⟨ _OwnI_auth u (elements (dom I)), fun i => or_else (I !! i) emp⟩%SRF. *)
  (* Definition free_worlds u b : SRFSyn.t b := *)
    (* ⟨ _free_worlds u b, fun e => match e with end ⟩%SRF. *)
  (* Definition empty_universes eu {n} : SRFSyn.t n := *)
    (* ⟨ _empty_universes eu , fun a => match a with end ⟩%SRF. *)

  (* Definition OwnE (u : univ_id) {n} (E : coPset) : SRFSyn.t n := *)
    (* (<ownm> (OwnER u E))%SRF. *)
  (* Definition OwnD (u : univ_id) {n} (D : gset positive) : SRFSyn.t n := *)
    (* (<ownm> (OwnDR u D))%SRF. *)
  (* Definition ownD_auth (u : univ_id) {n} : SRFSyn.t n := *)
    (* (∃ D : τ{⇣gset positive}, <ownm> (OwnD_authR u D))%SRF. *)

  (* Definition inv_satall u n (I : gmap positive (SRFSyn.t n)) : SRFSyn.t n := *)
    (* ([∗ n map] i ↦ p ∈ I, (p ∗ OwnD u {[i]}) ∨ OwnE u {[i]})%SRF. *)
  (* Definition wsat u n : SRFSyn.t (S n) := *)
    (* (∃ I : τ{ST.gmapT Φ}, (⤉ OwnI_auth u n I) ∗ (⤉ inv_satall u n I))%SRF. *)
  Definition syn_wsats (u : univ_id) (n : level) (E : coPset) : SRFSyn.t n :=
    ⟨ _wsats u n E, λ e, match e with end ⟩%SRF.
  Definition syn_inv (u : univ_id) (n : level) (N : namespace) (p : SRFSyn.t n) : SRFSyn.t n :=
    ⟨ _inv u n N p, λ e, match e with end ⟩%SRF.
  (* Definition syn_fupd u b (E1 E2 : coPset) (P : iProp Σ) : SRFSyn.t n :=
    syn_wsats u b E1 ==∗ (syn_wsats u b E2 ∗ P) *)

  (* Definition empty_worlds (eu : univ_id) {n} : SRFSyn.t n := *)
    (* (<ownm> (empty_worldsR eu (fun _ => Some ⊤ : CoPset.t) : OwnERA) ∗ *)
    (* <ownm> (empty_worldsR eu (fun _ => Auth.black (Some ∅ : Gset.t)) : OwnDRA) ∗ *)
    (* ownI_free eu). *)
  (* Definition free_universes {n} : SRFSyn.t n :=
    (∃ eu : τ{⇣ univ_id}, empty_universes eu)%SRF.
  Fixpoint wsats u b : SRFSyn.t b :=
    match b with
    | 0 => emp%SRF
    | S n => (wsat u n ∗ ⤉ wsats u n)%SRF
    end. *)

  (* Interface for the user *)
  (* Definition used_worlds u b E : SRFSyn.t b := *)
    (* wsats u b ∗ OwnE u E ∗ ownD_auth u ∗ free_universes. *)
  (* Definition closed_universe u b E : SRFSyn.t b := *)
    (* used_worlds u b E ∗ free_worlds u b. *)
  (* Definition inv u (n : level) (N : namespace) p := *)
    (* (∃ i : τ{⇣positive}, ⌜i ∈ (↑N : coPset)⌝ ∧ OwnI u n i p)%SRF. *)
  (* Definition FUpd u b (A : SRFSyn.t b) (E1 E2 : coPset) (P : SRFSyn.t b) : SRFSyn.t b := *)
    (* A ∗ used_worlds u b E1 -∗ |==> (A ∗ used_worlds u b E2 ∗ P). *)
  Context (p : SRFSyn.t 0).
  Check (syn_inv 1 0 nil (syn_wsats 1 0 ⊤)).
End syn_inv.

Class sinvGS Σ Γ α β τ :=
  { #[global] sinv_CtxSL :: CtxSL.t Σ Γ α β τ;
    #[global] sinv_invGS :: invGS Σ Γ;
    #[global] sinv_intpG :: @SRFIntp.inG SL.domain inv_syntax α inv_interp β
  }.

Module WDRed. Section RED.
  Context `{!sinvGS Σ Γ α β τ}.

  Lemma wsats u n E : ⟦syn_wsats u n E⟧ = wsats u n E.
  Proof. rewrite /syn_wsats. SRF_red_all. ss. Qed.
  Lemma inv u n N p : ⟦syn_inv u n N p⟧ = inv u n N p.
  Proof. rewrite /syn_inv. SRF_red_all. ss. Qed.

    (* Context `{_C : Inv.t}. *)

    (* Lemma OwnI_auth u n I  : *)
      (* SRFSem.t n (WD.OwnI_auth u n I) = OwnI_auth u n I. *)
    (* Proof. *)
      (* rewrite /WD.OwnI_auth. SRF_red_all. ss. *)
      (* rewrite /OwnI_auth /OwnI_authR; do 5 f_equal. *)
      (* apply map_eq; intros i. *)
      (* destruct (I !! i) eqn : EI; rewrite EI. *)
      (* { rewrite -elem_of_list_to_map. *)
        (* rewrite elem_of_list_fmap; exists i; rewrite EI; ss; split; eauto; *)
          (* by rewrite elem_of_elements elem_of_dom; rewrite EI. *)
        (* eapply NoDup_fmap_fst. *)
        (* { intros ???. rewrite !elem_of_list_fmap; ii; des; clarify. } *)
        (* eapply NoDup_fmap_2; last by eapply NoDup_elements. *)
        (* ii; clarify. *)
      (* } *)
      (* { eapply not_elem_of_list_to_map_1; intros H. *)
        (* rewrite elem_of_list_fmap in H; des; clarify. *)
        (* eapply elem_of_list_fmap_2 in H0; des; clarify; ss. *)
        (* rewrite elem_of_elements elem_of_dom in H1; rewrite EI in H1; ss; inv H1. *)
      (* } *)
    (* Qed. *)

    (* Lemma wsat u n: *)
      (* SRFSem.t (S n) (WD.wsat u n) ≡ wsat u n. *)
    (* Proof. *)
      (* rewrite /WD.wsat /wsat. SL_red. *)
      (* rewrite bi.equiv_entails; split; ss; iIntros "[%I WD]"; SL_red; iDestruct "WD" as "[WD1 WD2]"; SL_red. *)
      (* { SRF_red; SL_red; rewrite OwnI_auth /inv_satall; iExists I; iFrame. *)
        (* iApply (big_sepM_impl with "WD2"); iModIntro; iIntros. rewrite /WD.OwnD /WD.OwnE; SL_red; SL_red_ownm; ss. *)
      (* } *)
      (* { iExists I; SL_red. SL_red. SRF_red. rewrite OwnI_auth; iFrame. *)
        (* SL_red; rewrite /inv_satall. iApply (big_sepM_impl with "WD2"); iModIntro; iIntros. SL_red; SL_red_ownm; ss. *)
      (* } *)
    (* Qed. *)

    (* Lemma wsats u b: *)
      (* SRFSem.t b (WD.wsats u b) ≡ wsats u b. *)
    (* Proof. *)
      (* induction b; ss. *)
      (* - SL_red. eauto. *)
      (* - rewrite @SLRed.sepconj wsat. SRF_red. rewrite IHb. by rewrite wsats_fold. *)
    (* Qed. *)

    (* User Interface *)
    (* Lemma used_worlds u b E : *)
      (* SRFSem.t b (WD.used_worlds u b E) ≡ used_worlds u b E. *)
    (* Proof. *)
      (* SL_red; rewrite wsats; rewrite bi.equiv_entails; split. *)
      (* { iIntros "[WSAT [E [[% D] [% U]]]]"; SL_red; iFrame. *)
        (* by rewrite /WD.empty_universes; SRF_red; SL_red_ownm; ss; iFrame. } *)
      (* { iIntros "[WSAT [E [[% D] [% U]]]]"; SL_red; SL_red_ownm; iFrame. *)
        (* iSplitL "D"; [iExists D|iExists eu]; last by rewrite /WD.empty_universes; SRF_red; ss; iFrame. *)
        (* SL_red; SL_red_ownm; iFrame. *)
      (* } *)
    (* Qed. *)

    (* Lemma free_worlds u b : *)
      (* SRFSem.t b (WD.free_worlds u b) = free_worlds u b. *)
    (* Proof. *)
      (* unfold free_worlds, WD.free_worlds. SRF_red. eauto. *)
    (* Qed. *)

    (* Lemma closed_universe u b E : *)
      (* SRFSem.t b (WD.closed_universe u b E) ≡ closed_universe u b E. *)
    (* Proof. *)
      (* rewrite /WD.closed_universe /closed_universe @SLRed.sepconj used_worlds free_worlds; ss. *)
    (* Qed. *)

    (* Lemma inv u n N p : *)
      (* SRFSem.t n (WD.inv u n N p) ≡ inv u n N p. *)
    (* Proof. *)
      (* rewrite /WD.inv /inv; SL_red; rewrite bi.equiv_entails; split; iIntros "[%x H]"; SL_red. *)
      (* { iExists x; rewrite /WD.OwnI; SRF_red; ss. } *)
      (* { iExists x; SL_red; rewrite /WD.OwnI; SRF_red; ss. } *)
    (* Qed. *)

    (* Lemma FUpd u b A E1 E2 P : *)
      (* SRFSem.t b (WD.FUpd u b A E1 E2 P) ≡ FUpd u b ⟦A⟧ E1 E2 ⟦P⟧. *)
    (* Proof. *)
      (* Local Transparent FUpd. *)
      (* unfold WD.FUpd, FUpd. rewrite !@SLRed.wand !@SLRed.upd @SLRed.sepconj. rewrite -> used_worlds. *)
      (* do 2 rewrite @SLRed.sepconj. rewrite used_worlds. eauto. *)
    (* Qed. *)

  End RED.
End WDRed.

(* Global Opaque WD.used_worlds. *)
(* Global Opaque WD.free_worlds. *)
(* Global Opaque WD.inv. *)
(* Global Opaque WD.FUpd. *)
(* Global Opaque used_worlds. *)
(* Global Opaque free_worlds. *)
(* Global Opaque inv. *)
(* Global Opaque FUpd. *)


Ltac WD_red := repeat (
                   try rewrite ! @WDRed.used_worlds;
                   try rewrite ! @WDRed.free_worlds;
                   try rewrite ! @WDRed.closed_universe;
                   try rewrite ! @WDRed.inv;
                   try rewrite ! @WDRed.FUpd
                 ).

Ltac WD_red_all := repeat (
                       try rewrite ! @WDRed.used_worlds in *;
                       try rewrite ! @WDRed.free_worlds in *;
                       try rewrite ! @WDRed.closed_universe in *;
                       try rewrite ! @WDRed.inv in *;
                       try rewrite ! @WDRed.FUpd in *
                     ).
