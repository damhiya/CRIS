From stdpp Require Import namespaces.
Require Import sflib.
From iris.algebra Require Import ofe auth agree coPset gset gmap_view.
From CRIS.algebra Require Import functions.
From iris Require Import bi.big_op.
Require Import Coqlib.
Require Export SRF sProp own.

Local Notation univ_id := positive.
Local Notation level := nat.

Section invariants.
  Context `{α : SRFCons.t}.

  Canonical Structure SynO n : ofe := leibnizO (SRFSyn.t n).

  Definition InvSetRA n : ucmra := gmap_viewUR positive (agreeR (SynO n)).

  (** IMPROVE : This is a temporary Proper typeclass to resolve rewrite lemmas for
      SRFSyn.t types. TC resolution fails to apply general discrete_fun_singleton_proper
      since SRFSyn.t types are also dependent on α. This can be generalized further. *)
  Global Instance discrete_fun_singleton_proper' (x : univ_id) :
    Proper
      ((≡) ==> (≡))
      (discrete_fun_singleton (B := (λ _, discrete_funUR InvSetRA)) x).
  Proof.
    intros x1 x2 H' u. destruct (decide (u = x)); last first.
    { rewrite ! discrete_fun_lookup_singleton_ne; eauto. }
    clarify; rewrite ! discrete_fun_lookup_singleton; eauto.
  Qed.

  Definition ownIRA : ucmra :=
    univ_id -d> (discrete_funUR InvSetRA).

  Definition ownERA : ucmra :=
    univ_id -d> coPset_disjUR.

  Definition ownDRA : ucmra :=
    univ_id -d> (authUR (gset_disjUR positive)).

  Class invGpreSΣ (Σ : GRA) := {
    invGS_I : inG ownIRA Σ
  }.
  Class invGpreSΓ (Γ : HRA) := {
    invGS_E : inG ownERA Γ;
    invGS_D : inG ownDRA Γ;
  }.

  Class invGSΣ (Σ : GRA) := {
    inv_preΣ : invGpreSΣ Σ;
    invariant_name : gname;
  }.
  Class invGSΓ (Γ : HRA) := {
    inv_preΓ : invGpreSΓ Γ;
    enabled_name : gname;
    disabled_name : gname;
  }.

  Class invGS (Σ : GRA) (Γ : HRA) `{!subG Γ Σ} := {
    #[global] invGS_Σ :: invGSΣ Σ;
    #[global] invGS_Γ :: invGSΓ Γ;
  }.

  Definition invΓ : HRA := #[ownERA; ownDRA].
  Definition invΣ : GRA := ##[#[ownIRA]; invΓ].

  Global Instance subG_invΣ {Σ} : subG invΣ Σ → invGpreSΣ Σ.
  Proof. solve_inG. Qed.
  Global Instance subG_invΓ {Γ} : subG invΓ Γ → invGpreSΓ Γ.
  Proof. solve_inG. Qed.
End invariants.

Section predicates.
  Context `{α : SRFCons.t, Γ : HRA, !subG Γ Σ, !invGS Σ Γ}.
  Local Existing Instances inv_preΣ inv_preΓ invGS_I invGS_E invGS_D.

  (* owns invariant *)
  Definition ownIR (u : univ_id) (n : level) (i : positive) (p : SRFSyn.t n) : ownIRA :=
    discrete_fun_singleton u
      (discrete_fun_singleton n
        (gmap_view_frag i DfracDiscarded (to_agree p))).
  Definition ownI (u : univ_id) (n : level) (i : positive) (p : SRFSyn.t n) : iProp Σ :=
    own invariant_name (ownIR u n i p).

  Global Instance ownI_persistent
    u n i p : Persistent (ownI u n i p).
  Proof. apply _. Qed.

  Definition ownI_authR (u : univ_id) (n : level) (I : gmap positive (SRFSyn.t n)) : ownIRA :=
    discrete_fun_singleton u
      (discrete_fun_singleton n
        (gmap_view_auth (DfracOwn 1) (to_agree <$> I))).
  Definition ownI_auth (u : univ_id) (n : level) (I : gmap positive (SRFSyn.t n)) :=
    own invariant_name (ownI_authR u n I).

  Definition wsat_authR u b : ownIRA :=
    discrete_fun_singleton u
      ((λ n, if (n <? b) then ε else gmap_view_auth (DfracOwn 1) ∅) : discrete_funUR InvSetRA).
  Definition wsat_auth u b : iProp Σ := own invariant_name (wsat_authR u b).

  Definition ownER (u : univ_id) (E : coPset) : ownERA :=
    discrete_fun_singleton u (CoPset E).
  Definition ownE (u : univ_id) (E : coPset) : iProp Σ :=
    own enabled_name (ownER u E).

  Definition ownDR (u : univ_id) (D : gset positive) : ownDRA :=
    discrete_fun_singleton u (◯ (GSet D)).
  Definition ownD (u : univ_id) (D : gset positive) : iProp Σ :=
    own disabled_name (ownDR u D).

  Definition ownD_authR  (u : univ_id) (D : gset positive) : ownDRA :=
    discrete_fun_singleton u (● (GSet D)).
  Definition ownD_auth (u : univ_id) : iProp Σ :=
    ∃ D, own disabled_name (ownD_authR u D).

  Lemma ownE_exploit u (E1 E2 : coPset) :
    ownE u E1 ∗ ownE u E2 ⊢ ⌜E1 ## E2⌝.
  Proof.
    iIntros "[H1 H2]". iCombine "H1 H2" gives %WF.
    by rewrite discrete_fun_singleton_op discrete_fun_singleton_valid coPset_disj_valid_op in WF.
  Qed.

  Lemma ownE_op u (E1 E2 : coPset) :
    E1 ## E2 → ownE u E1 ∗ ownE u E2 ⊣⊢ ownE u (E1 ∪ E2).
  Proof.
    intros dis; rewrite -own_op discrete_fun_singleton_op coPset_disj_union; ss.
  Qed.

  Lemma ownE_subset u (E1 E2 : coPset) :
    E1 ⊆ E2 -> ownE u E2 ⊢ ownE u E1 ∗ (ownE u E1 -∗ ownE u E2).
  Proof.
    iIntros (SUB) "E".
    rewrite (union_difference_L E1 E2); [|done].
    iPoseProof (ownE_op with "E") as "[E1 E2]"; [set_solver|].
    iFrame. iIntros "E1".
    iApply ownE_op; [set_solver|iFrame].
  Qed.
End predicates.

Section wsat.
  Context `{@SRFIntp.t (domain Σ) α, Γ : HRA, !subG Γ Σ, !invGS Σ Γ}.

  (* Notation "'⟦' F ',' n '⟧'" := (SRFSem.t (Δ := domain Σ) n F). *)
  (* Notation "'⟦' F '⟧'" := (SRFSem.t (Δ := domain Σ) _ F). *)

  Variable u : univ_id.
  Variable n : level.

  Definition inv_satall (I : gmap positive (SRFSyn.t n)) : iProp Σ :=
    [∗ map] i ↦ p ∈ I, (⟦p⟧ ∗ ownD u {[i]}) ∨ ownE u {[i]}.

  Definition wsat : iProp Σ := ∃ I, ownI_auth u n I ∗ inv_satall I.

  Lemma alloc_name φ (INF : pred_infinite φ) :
    ownD_auth u ⊢ |==> ownD_auth u ∗ ∃ i, ⌜φ i⌝ ∧ ownD u {[i]}.
  Proof.
    iIntros "[% DA]".
    rewrite (pred_infinite_set φ (C:=gset univ_id)) in INF.
    hexploit (INF D); intros [x [??]].
    iPoseProof (own_update with "DA") as "> DA".
    { by eapply discrete_fun_singleton_update, auth_update_alloc,
        gset_disj_alloc_empty_local_update, disjoint_singleton_l.
    }
    iEval (rewrite -discrete_fun_singleton_op) in "DA"; iPoseProof (own_op with "DA") as "[D1 D2]".
    iModIntro; iSplitL "D1"; iFrame.
    iPureIntro; done.
  Qed.

  Lemma wsat_ownI_alloc_gen p φ (INF : pred_infinite φ) :
    ownD_auth u ∗ wsat ⊢ |==> (∃ i, ⌜φ i⌝ ∧ ownI u n i p) ∗ ownD_auth u ∗ (⟦p⟧ -∗ wsat).
  Proof.
    iIntros "[DA [%I [IA INV]]]"; rewrite /ownI_auth /inv_satall.
    iMod (alloc_name (λ i, φ i ∧ i ∉ dom I) with "DA") as "[DA [% [% D]]]".
    { intros l; hexploit (INF (l ++ (elements (dom I)))); intros [x [H1 H2]]; exists x.
      eapply not_elem_of_app in H2; des; repeat split; eauto.
      rewrite elem_of_elements in H0; eauto.
    }
    iPoseProof (own_update with "IA") as "> IA".
    { do 2 eapply discrete_fun_singleton_update.
      eapply (gmap_view_alloc (to_agree <$> I) i (DfracOwn 1) (to_agree (A:=leibnizO _) p)); ss.
      eapply not_elem_of_dom; rewrite dom_fmap_L; des; eauto.
    }
    rewrite -?discrete_fun_singleton_op; iPoseProof (own_op with "IA") as "[I1 I2]".
    iMod (own_update with "I2") as "I2".
    { do 2 eapply discrete_fun_singleton_update; eapply gmap_view_frag_persist. }
    iModIntro; iFrame; iSplit; [iPureIntro; des; ss|iIntros "P"].
    iExists (<[i:=p]> I); iSplitL "I1".
    { rewrite -fmap_insert; iFrame. }
    iApply (big_sepM_insert _ I i p).
    { des; eapply not_elem_of_dom; eauto. }
    iFrame. iLeft; iFrame.
  Qed.

  Lemma wsat_ownI_alloc p φ (INF : pred_infinite φ) :
    ownD_auth u ∗ wsat ∗ ⟦p⟧ ⊢ |==> (∃ i, ⌜φ i⌝ ∧ ownI u n i p) ∗ ownD_auth u ∗ wsat.
  Proof.
    iIntros "(D & W & P)".
    iMod (wsat_ownI_alloc_gen with "[D W]") as "(I & D & W)". eauto. iFrame.
    iFrame. iModIntro. iApply "W". iFrame.
  Qed.

  Lemma wsat_ownI_open i p :
    ownI u n i p ∗ wsat ∗ ownE u {[i]} ⊢ |==> ⟦p⟧ ∗ wsat ∗ ownD u {[i]}.
  Proof.
    iIntros "(I & [% [AUTH SAT]] & EN)". iModIntro.
    iCombine "AUTH I" as "AUTH"; iPoseProof (own_valid with "AUTH") as "%WF".
    rewrite ?discrete_fun_singleton_op ?discrete_fun_singleton_valid in WF.
    eapply gmap_view_both_dfrac_valid_discrete_total in WF; des.
    eapply lookup_fmap_Some in WF1; des; clarify.
    hexploit (to_agree_included p x); eauto; intros Hin; apply Hin in WF3; inv WF3.
    iDestruct "AUTH" as "[AUTH I]".
    iPoseProof (big_sepM_delete with "SAT") as "[[[H1 H2]|H1] SAT]"; eauto.
    { iPoseProof (big_sepM_insert _ (delete i I) i x with "[SAT EN]") as "SAT".
      { eapply lookup_delete_None; eauto. }
      { iFrame. iRight; iFrame. }
      rewrite insert_delete; eauto. iFrame.
    }
    iPoseProof (ownE_exploit with "[EN H1]") as "%"; iFrame; set_solver.
  Qed.

  Lemma wsat_ownI_close i p :
    ownI u n i p ∗ wsat ∗ ⟦p⟧ ∗ ownD u {[i]} ⊢ |==> wsat ∗ ownE u {[i]}.
  Proof.
    iIntros "(I & [% [AUTH SAT]] & P & DIS)". iModIntro.
    iCombine "AUTH I" as "AUTH"; iPoseProof (own_valid with "AUTH") as "%WF".
    rewrite ?discrete_fun_singleton_op ?discrete_fun_singleton_valid in WF.
    eapply gmap_view_both_dfrac_valid_discrete_total in WF; des.
    eapply lookup_fmap_Some in WF1; des; clarify.
    hexploit (to_agree_included p x); eauto; intros Hin; apply Hin in WF3; inv WF3.
    iDestruct "AUTH" as "[AUTH I]".
    iPoseProof (big_sepM_delete with "SAT") as "[[[H1 H2]|H1] SAT]"; eauto.
    { iCombine "DIS H2" as "F". rewrite discrete_fun_singleton_op.
      iPoseProof (own_valid with "F") as "%WF'".
      rewrite discrete_fun_singleton_valid auth_frag_op_valid gset_disj_valid_op in WF'; set_solver.
    }
    iPoseProof (big_sepM_insert _ (delete i I) i x with "[SAT P DIS]") as "SAT".
    { eapply lookup_delete_None; eauto. }
    { iFrame. iLeft; iFrame. }
    rewrite insert_delete; eauto. iFrame.
  Qed.

  Lemma wsat_init :
    ownI_auth u n ∅ ⊢ wsat.
  Proof.
    iIntros "H"; iExists ∅; iFrame; iApply big_sepM_empty; ss.
  Qed.
End wsat.

Section wsats.
  Context `{@SRFIntp.t (domain Σ) α, Γ : HRA, !subG Γ Σ, !invGS Σ Γ}.
  Local Existing Instances inv_preΣ inv_preΓ invGS_I invGS_E invGS_D.

  Definition wsats u n E : iProp Σ :=
    wsat_auth u n ∗ ownE u E ∗ ownD_auth u ∗ [∗ list] n ∈ (seq 0 n), wsat u n.
  Definition univs u n : iProp Σ :=
    [∗ list] v ∈ (seq 0 (Pos.to_nat u)), wsats (Pos.of_nat v) n ⊤.

  Local Definition uPred_fupd_def u b (E1 E2 : coPset) (P : iProp Σ) : iProp Σ :=
    wsats u b E1 ==∗ (wsats u b E2 ∗ P).
  Local Definition uPred_fupd_aux : seal (@uPred_fupd_def). Proof. by eexists. Qed.
  Definition uPred_fupd := uPred_fupd_aux.(unseal).
  Local Definition uPred_fupd_eq : @uPred_fupd = @uPred_fupd_def := uPred_fupd_aux.(seal_eq).
  Local Lemma uPred_fupd_unseal u b : @fupd _ (uPred_fupd u b) = (uPred_fupd_def u b).
  Proof. rewrite -uPred_fupd_eq //. Qed.

  Lemma uPred_fupd_mixin u n : BiFUpdMixin (iProp Σ) (uPred_fupd u n).
  Proof.
    split.
    - rewrite /updates.fupd uPred_fupd_eq. solve_proper.
    - intros E1 E2 (E1''&->&?)%subseteq_disjoint_union_L.
      rewrite /fupd uPred_fupd_eq /uPred_fupd_def /wsats -ownE_op //.
      by iIntros "($ & ($ & $) & $ & $) !> ($ & $ & $ & $) !>".
    - rewrite /fupd uPred_fupd_eq /uPred_fupd_def /wsats /bi_except_0.
      iIntros (E1 E2 P) "[H | H]"; iFrame.
      iDestruct (uPred.later_eq with "H") as "H"; by iFrame.
    - rewrite /fupd uPred_fupd_eq /uPred_fupd_def /wsats.
      iIntros (E1 E2 P Q HPQ) "HP HwE". rewrite -HPQ. by iApply "HP".
    - rewrite /fupd uPred_fupd_eq /uPred_fupd_def /wsats. iIntros (E1 E2 E3 P) "HP HwE".
      iMod ("HP" with "HwE") as "(HA & HP)". iApply "HP"; by iFrame.
    - intros E1 E2 Ef P HE1Ef. rewrite /fupd uPred_fupd_eq /uPred_fupd_def /wsats -ownE_op //.
      iIntros "Hupd (AUTH & [E1 Ef] & D & WSAT)".
      iMod ("Hupd" with "[AUTH E1 D WSAT]") as "[($ & E2 & $ & $) P]"; iFrame.
      iPoseProof (ownE_exploit with "[Ef E2]") as "%DISJ"; first iFrame.
      iModIntro; rewrite -ownE_op //=.
      iFrame. iApply "P"; done.
    - rewrite /fupd uPred_fupd_eq /uPred_fupd_def /wsats. by iIntros (????) "[HwP $]".
  Qed.
  Global Instance uPred_bi_fupd u n : BiFUpd (iProp Σ) :=
    {| bi_fupd_mixin := (uPred_fupd_mixin u n) |}.
  Global Instance uPred_bi_bupd_fupd u n :
    @BiBUpdFUpd (iProp Σ) (uPred_bi_bupd Σ) (uPred_bi_fupd u n).
  Proof. rewrite /BiBUpdFUpd uPred_fupd_unseal. by iIntros (E P) ">? [$ $] !>". Qed.

  Notation fupd_ex u n :=
    (@fupd (bi_car (uPredI (GRAUR Σ))) (@bi_fupd_fupd _ (uPred_bi_fupd u n))) (only parsing).

  Notation "'=|' u ',' n '|={' E1 ',' E2 '}=>' P" := (fupd_ex u n E1 E2 P)%I (at level 90) : bi_scope.
  Notation "P '=|' u ',' n '|={' E1 ',' E2 '}=∗' Q" := (P -∗ =|u, n|={E1,E2}=> Q)%I (at level 90)  : bi_scope.

  Notation "'=|' u ',' n '|={' E '}=>' P" := (=|u, n|={E, E}=> P)%I (at level 90) : bi_scope.
  Notation "P '=|' u ',' n '|={' E '}=∗' Q" := (P -∗ =|u, n|={E, E}=> Q)%I (at level 90) : bi_scope.

  Local Definition inv_def u (n : level) (N : namespace) (p : SRFSyn.t n) : iProp Σ :=
    ∃ i, ⌜i ∈ (↑N : coPset)⌝ ∧ ownI u n i p.
  Local Definition inv_aux : seal (@inv_def). Proof. by eexists. Qed.
  Definition inv := inv_aux.(unseal).
  Local Definition inv_eq : @inv = @inv_def := inv_aux.(seal_eq).

  Global Instance inv_persistent u n N p : Persistent (inv u n N p).
  Proof. rewrite inv_eq /inv_def. apply _. Qed.
End wsats.

  (* Definition used_worlds u b E : iProp Σ :=
    wsats u b ∗ ownE u E ∗ ownD_auth u ∗ free_universes. *)
  (* Definition closed_universe u b E : iProp Σ :=
    used_worlds u b E ∗ wsat_auth u b. *)

  (* Lemma wsats_fold u b :
    wsats u (S b) ⊣⊢ (wsat u b ∗ wsats u b)%I.
  Proof.
    iSplit; replace (S b) with (b + 1) by lia; rewrite /wsats (seq_app b 1 0); ss;
      iIntros; by rewrite big_sepL_app big_sepL_singleton comm.
  Qed. *)

  (* Lemma free_worlds_alloc u (b b' : level) (NIN : b < b') :
    wsat_auth u b ⊢ wsat_auth u b' ∗ ([∗ list] n ∈ (seq b (b' - b)), wsat u n).
  Proof.
    rewrite /wsat_auth /wsat_authR.
    induction NIN; iIntros "FW".
    { replace (S b - b) with 1 by lia; ss.
      iEval (rewrite (discrete_fun_delete b (λ n, if n <? b then ε else gmap_view_auth (DfracOwn 1) ∅))) in "FW".
      rewrite -discrete_fun_singleton_op own_op. des_ifs; first by rewrite Nat.ltb_lt in Heq; lia.
      iDestruct "FW" as "[FW1 FW2]"; iSplitL "FW1"; last iSplitL; [|iApply wsat_init; iFrame|eauto].
      iPoseProof (ownM_extends with "FW1") as "?"; last iFrame.
      exists ε; rewrite right_id; intros i; destruct (decide (i = u)); clarify;
        [rewrite !discrete_fun_lookup_singleton|rewrite !discrete_fun_lookup_singleton_ne]; eauto.
      intros x; ss; des_ifs. 
      { rewrite Nat.ltb_ge in Heq0; lia. }
      { rewrite Nat.ltb_ge in Heq1; rewrite Nat.ltb_lt in Heq0; lia. }
      { rewrite Nat.ltb_ge in Heq0; rewrite Nat.ltb_lt in Heq1; lia. }
    }
    { iPoseProof (IHNIN with "FW") as "FW".
      iEval (rewrite (discrete_fun_delete m (λ n, if n <? m then ε else gmap_view_auth (DfracOwn 1) ∅))) in "FW".
      rewrite -discrete_fun_singleton_op own_op. des_ifs; first by rewrite Nat.ltb_lt in Heq; lia.
      iDestruct "FW" as "[[FW1 FW2] FW3]"; iPoseProof (wsat_init with "FW2") as "FW2".
      iSplitR "FW2 FW3".
      { iPoseProof (ownM_extends with "FW1") as "?"; last iFrame.
        exists ε; rewrite right_id; intros i; destruct (decide (i = u)); clarify;
          [rewrite !discrete_fun_lookup_singleton|rewrite !discrete_fun_lookup_singleton_ne]; eauto.
        intros x; ss; des_ifs. 
        { rewrite Nat.ltb_ge in Heq0; lia. }
        { rewrite Nat.ltb_ge in Heq1; rewrite Nat.ltb_lt in Heq0; lia. }
        { rewrite Nat.ltb_ge in Heq0; rewrite Nat.ltb_lt in Heq1; lia. }
      }
      replace (S m - b) with ((m - b) + 1) by lia.
      rewrite (seq_app _ 1); ss; replace (b + (m - b)) with m by lia.
      rewrite big_sepL_app; iFrame; iApply big_sepL_nil; eauto.
    }
  Qed.

  Lemma wsats_split u (b b' : level) (LE : b <= b'):
    wsats u b ∗ ([∗ list] n ∈ (seq b (b' - b)), wsat u n) ⊣⊢ wsats u b'.
  Proof.
    replace b' with (b + (b' - b)) at 2 by lia.
    rewrite /wsats (seq_app b _) /= big_sepL_app; eauto.
  Qed. *)

 (* Lemma free_worlds_nin u (b b' : level) (LE : b <= b')
    : wsat_auth u b ⊢ wsat_auth u b' ∗
                      ([∗ list] n ∈ (seq b (b' - b)), wsat u n).
  Proof.
    iIntros "R".
    destruct (le_lt_or_eq _ _ LE); subst; cycle 1.
    - replace (b'-b') with 0 by nia. s. iFrame.
    - iApply free_worlds_nin_; eauto.
  Qed.

  Lemma wsats_allocs u b b':
    b <= b' -> wsat_auth u b ∗ wsats u b ⊢ wsat_auth u b' ∗ wsats u b'.
  Proof.
    iIntros (LE) "(AUTH & SAT)".
    iPoseProof ((free_worlds_nin _ _ _ LE) with "AUTH") as "(AUTH & NEW)". iFrame.
    iPoseProof ((wsats_nin _ _ _ LE) with "[SAT NEW]") as "SAT". iFrame. iFrame.
  Qed.

  Lemma wsats_ownI_alloc_lt_gen u n b (IN : n < b) p φ
        (INF : forall (E : level -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : ownD_auth u ∗ wsats u b ⊢ |==> (∃ i, ⌜φ i⌝ ∧ ownI u n i p) ∗ ownD_auth u ∗ (⟦p⟧ -∗ wsats u b).
  Proof.
    iIntros "[DA SALL]". iPoseProof (wsats_unfold with "SALL") as "SALL".
    iPoseProof (big_sepL_lookup_acc with "SALL") as "[WSAT K]".
    { apply lookup_seq_lt; eauto. }
    iPoseProof (wsat_ownI_alloc_gen with "[DA WSAT]") as ">(RES & DA & WSAT)".
    { apply INF. } { iFrame. }
    iFrame. iModIntro. iIntros "P".
    iPoseProof ("WSAT" with "P") as "WSAT".
    iPoseProof ("K" with "WSAT") as "SALL".
    iApply wsats_fold. iFrame.
  Qed.

  Lemma wsats_ownI_alloc_lt u n b (IN : n < b) p φ
        (INF : forall (E : level -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : ownD_auth u ∗ wsats u b ∗ ⟦p⟧ ⊢
        |==> (∃ i, ⌜φ i⌝ ∧ ownI u n i p) ∗ ownD_auth u ∗ wsats u b.
  Proof.
    iIntros "(D & W & P)".
    iMod (wsats_ownI_alloc_lt_gen with "[D W]") as "(I & D & W)"; eauto. iFrame.
    iModIntro. iFrame. iApply "W". iFrame.
  Qed.

  Lemma wsats_ownI_alloc_ge_gen u b n (GE : b <= n) p φ
        (INF : forall (E : level -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : wsat_auth u b ∗ ownD_auth u ∗ wsats u b ⊢
        |==> ((∃ i, ⌜φ i⌝ ∧ ownI u n i p)
              ∗ wsat_auth u (S n) ∗ ownD_auth u ∗ (⟦p⟧ -∗ wsats u (S n))).
  Proof.
    iIntros "(AUTH & D & WSAT)".
    iPoseProof ((wsats_allocs u b (S n)) with "[AUTH WSAT]") as "[AUTH WSAT]". lia. iFrame.
    iMod ((wsats_ownI_alloc_lt_gen u n (S n)) with "[D WSAT]") as "[RES WSAT]". auto. eauto. iFrame.
    iModIntro. iFrame.
  Qed.

  Lemma wsats_ownI_alloc_ge u b n (GE : b <= n) p φ
        (INF : forall (E : level -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : wsat_auth u b ∗ ownD_auth u ∗ wsats u b ∗ ⟦p⟧ ⊢
        |==> ((∃ i, ⌜φ i⌝ ∧ ownI u n i p)
                ∗ wsat_auth u (S n) ∗ ownD_auth u ∗ wsats u (S n)).
  Proof.
    iIntros "(A & D & W & P)". iMod (wsats_ownI_alloc_ge_gen with "[A D W]") as "(I & A & D & W)".
    1,2 : eauto. iFrame.
    iFrame. iModIntro. iFrame. iApply "W". iFrame.
  Qed.

  Lemma free_worlds_ownI_le u b n i p :
    ownI u n i p ∗ wsat_auth u b ⊢ ⌜n < b⌝.
  Proof.
    iIntros "(I & AUTH)".
    unfold ownI, wsat_auth, wsat_auth.
    iCombine "AUTH I" as "AUTH".
    iPoseProof (own_valid with "AUTH") as "%WF".
    unfold wsat_authR, ownIR, maps_to_res, maps_to_res_dep in WF.
    unfold URA.add in WF. unseal "ra". ss.
    apply (pw_lookup_wf _ u) in WF. ss.
    unfold URA.add in WF. unseal "ra". ss.
    apply (pwd_lookup_wf _ n) in WF. ss.
    destruct (u =? u)%positive eqn:EQ; cycle 1.
    { apply Pos.eqb_neq in EQ. ss. }
    des_ifs.
    exfalso. unfold eq_rect_r in WF. rewrite <- Eqdep.EqdepTheory.eq_rect_eq in WF.
    unfold maps_to_res in WF. apply Auth.auth_included in WF. rename WF into EXTENDS.
    apply pw_extends in EXTENDS. specialize (EXTENDS i). des_ifs.
    clear e e0. rr in EXTENDS. des. unfold URA.add in EXTENDS; unseal "ra".
    ss. des_ifs.
  Qed. *)

  (* Lemma wsats_ownI_open u b n i p (LE : n < b) :
    ownI u n i p ∗ wsats u b ∗ ownE u {[i]} ⊢ |==> ⟦p⟧ ∗ wsats u b ∗ ownD u {[i]}.
  Proof.
    iIntros "(I & SAT & EN)".
    rewrite -(wsats_split u (S n)); last by lia.
    rewrite ?wsats_fold; iDestruct "SAT" as "((SAT1 & SAT2) & SAT3)".
    iMod (wsat_ownI_open with "[I SAT1 EN]") as "[P [WSAT D]]"; first iFrame.
    iModIntro; iFrame.
  Qed.

  Lemma wsats_ownI_close u b n i p (LE : n < b) :
    ownI u n i p -∗ wsats u b -∗ ⟦p⟧ -∗ ownD u {[i]} ==∗ wsats u b ∗ ownE u {[i]}.
  Proof.
    iIntros "#I SAT P D".
    rewrite -(wsats_split u (S n)); last by lia.
    rewrite ?wsats_fold; iDestruct "SAT" as "((SAT1 & SAT2) & SAT3)".
    iMod (wsat_ownI_close with "[I SAT1 D P]") as "[WSAT EN]"; first by iFrame; done.
    iModIntro; iFrame.
  Qed.

  Lemma closed_universe_mon {u} b b' (LE : b <= b') E:
    closed_universe u b E ⊢ closed_universe u b' E.
  Proof.
    unfold closed_universe, used_worlds. iIntros "((W & E & D & FU) & FW)". inv LE; iFrame.
    rewrite (free_worlds_alloc _ b (S m)); [|nia].
    iDestruct "FW" as "[FW L]". iCombine "W L" as "W". rewrite wsats_split; [iFrame|nia].
  Qed. *)

  (* Lemma empty_worlds_split eu:
    empty_universes eu ⊢ wsat_auth eu 0 ∗ wsats eu 0 ∗ ownE eu ⊤ ∗ ownD_auth eu ∗ empty_universes (pos_ext_0 eu) ∗ empty_universes (pos_ext_1 eu).
  Proof.
    assert (ERA : URA.extends
              ((ownER eu ⊤) ⋅
               (empty_universesR (pos_ext_0 eu) (fun _ => Some ⊤ : CoPset.t)) ⋅
               (empty_universesR (pos_ext_1 eu) (fun _ => Some ⊤ : CoPset.t)))
              (empty_universesR eu (fun _ => Some ⊤ : CoPset.t) : ownERA)).
    { unfold empty_universesR, ownER, maps_to_res.
      exists ε. ur. extensionalities k.
      destruct (excluded_middle_informative _).
      { subst.
        rewrite ->pos_ext_0_sup_false, pos_ext_1_sup_false, pos_sup_refl.
        r_solve.
      }
      destruct (pos_sup (pos_ext_0 eu) k) eqn : SUP0.
      { rewrite pos_ext_1_disj; eauto.
        erewrite pos_sup_trans; try eassumption; try apply pos_ext_0_sup_true.
        r_solve.
      }
      destruct (pos_sup (pos_ext_1 eu) k) eqn : SUP1.
      { erewrite pos_sup_trans; try eassumption; try apply pos_ext_1_sup_true.
        r_solve.
      }
      rewrite pos_sup_cases; eauto; r_solve.
      eapply Pos.eqb_neq; eauto.
    }

    assert (DRA : URA.extends
              ((ownD_authR eu ∅) ⋅
               (empty_universesR (pos_ext_0 eu) (fun _ => Auth.black (Some ∅ : Gset.t)) : ownDRA) ⋅
               (empty_universesR (pos_ext_1 eu) (fun _ => Auth.black (Some ∅ : Gset.t)) : ownDRA))
              (empty_universesR eu (fun _ => Auth.black (Some ∅ : Gset.t)) : ownDRA)).
    { unfold empty_universesR, ownD_authR, maps_to_res.
      exists ε. ur. extensionalities k.
      destruct (excluded_middle_informative _).
      { subst.
        rewrite ->pos_ext_0_sup_false, pos_ext_1_sup_false, pos_sup_refl.
        r_solve.
      }
      destruct (pos_sup (pos_ext_0 eu) k) eqn : SUP0.
      { rewrite pos_ext_1_disj; eauto.
        erewrite pos_sup_trans; try eassumption; try apply pos_ext_0_sup_true.
        r_solve.
        }
      destruct (pos_sup (pos_ext_1 eu) k) eqn : SUP1.
      { erewrite pos_sup_trans; try eassumption; try apply pos_ext_1_sup_true.
        r_solve. }
      rewrite pos_sup_cases; eauto; r_solve.
      eapply Pos.eqb_neq; eauto.
    }

    assert (IRA : URA.extends
              ((wsat_authR eu 0) ⋅
               (empty_universesR (pos_ext_0 eu) (fun _ => (fun n => @Auth.black (_ ==> URA.agree (SRFSyn.t n))%ra (fun _ => None)) : URA.pointwise_dep _) : ownIRA) ⋅
               (empty_universesR (pos_ext_1 eu) (fun _ => (fun n => @Auth.black (_ ==> URA.agree (SRFSyn.t n))%ra (fun _ => None)) : URA.pointwise_dep _) : ownIRA))
              (empty_universesR eu (fun _ => (fun n => @Auth.black (_ ==> URA.agree (SRFSyn.t n))%ra (fun _ => None)) : URA.pointwise_dep _) : ownIRA)).
    { unfold empty_universesR, wsat_authR.
      exists ε. ur. ur. extensionalities k n.
      destruct (k =? eu)%positive eqn : EQ.
      { apply Pos.eqb_eq in EQ. subst.
        rewrite ->pos_ext_0_sup_false, pos_ext_1_sup_false, pos_sup_refl. r_solve.
      }
      destruct (pos_sup (pos_ext_0 eu) k) eqn : SUP0.
      { rewrite pos_ext_1_disj; eauto.
        erewrite pos_sup_trans; try eassumption; try apply pos_ext_0_sup_true.
        r_solve.
      }
      destruct (pos_sup (pos_ext_1 eu) k) eqn : SUP1.
      { erewrite pos_sup_trans; try eassumption; try apply pos_ext_1_sup_true.
        r_solve.
      }
      rewrite pos_sup_cases; eauto. r_solve.
    }

    iIntros "(ERA & DRA & IRA)".
    iPoseProof ((ownM_extends ERA) with "ERA") as "[[NE E1] E2]".
    iPoseProof ((ownM_extends DRA) with "DRA") as "[[ND D1] D2]".
    iPoseProof ((ownM_extends IRA) with "IRA") as "[[NI I1] I2]".
    unfold wsats. s. iFrame.
    iExists ∅. eauto.
  Qed.

  Lemma closed_world_init:
    empty_universes 1 ⊢ closed_universe 1 0 ⊤.
  Proof.
    iIntros "E".
    iPoseProof (empty_worlds_split with "E") as "(F & S & E & D & L & _)".
    iFrame. iExists (pos_ext_0 1). iFrame.
  Qed.

  Lemma closed_world_mon {u} b b' (LE : b <= b') E:
    closed_universe u b E ⊢ closed_universe u b' E.
  Proof.
    unfold closed_universe, world. iIntros "(F & W & E & R)". iFrame.
    rewrite ->wsats_unfold, <-wsats_fold.
    replace b' with (b + (b'-b)) by nia.
    rewrite ->seq_app, big_sepL_app. iFrame.
    iPoseProof (free_worlds_nin with "F") as "(FI & W)"; eauto.
    replace (b+(b'-b)) with b' by nia. iFrame.
  Qed. *)

(* 
Section FANCY_UPDATE.

  Context `{!CtxSL.t Σ Γ α β τ}.
  Context `{_W0 : @GRA.inG ownIRA Σ}.
  Context `{_W1 : @GRA.inG ownERA Γ}.
  Context `{_W2 : @GRA.inG ownDRA Γ}.
  Notation iProp := (iProp Σ).

  Definition inv u (n : level) (N : namespace) p :=
    (∃ i, ⌜i ∈ (↑N : coPset)⌝ ∧ ownI u n i p)%I.

  Definition FUpd u b (A : iProp) (E1 E2 : coPset) (P : iProp) : iProp :=
    A ∗ used_worlds u b E1 ==∗ (A ∗ used_worlds u b E2 ∗ P).

  Lemma FUpd_mono u b b' A E1 E2 P (LE : b <= b') :
    FUpd u b A E1 E2 P ⊢ FUpd u b' A E1 E2 P.
  Proof.
    iIntros "FUPD (A & SAT & EN & R)".
    rewrite -(wsats_split _ b); last by lia.
    iDestruct "SAT" as "[SAT1 SAT2]"; iMod ("FUPD" with "[A SAT1 R EN]") as "(A & ((SAT & E & D) & P))"; iFrame.
    iModIntro; iCombine "SAT" "SAT2" as "SAT"; rewrite wsats_split; eauto.
  Qed.

  Lemma FUpd_mask_frame u b A E1 E2 E P (DISJ : E1 ## E):
    FUpd u b A E1 E2 P ⊢ FUpd u b A (E1 ∪ E) (E2 ∪ E) P.
  Proof.
    iIntros "FUPD (A & WSAT & E & D & U)".
    iPoseProof (ownE_disjoint _ _ _ DISJ with "E") as "(E1 & E)".
    iPoseProof ("FUPD" with "[A WSAT E1 D U]") as ">(A & (WSAT & E1 & D & U) & P)"; iFrame.
    iPoseProof (ownE_union with "[E E1]") as "EN"; iFrame.
    iModIntro; eauto.
  Qed.

  (* Lemma wsats_inv_gen u b E N n p :
    n < b ->
    wsats u b ∗ ownE u E ∗ ownD_auth u -∗ |==> inv u n N p ∗ (⟦p⟧ -∗ wsats u b) ∗ ownE u E ∗ ownD_auth u.
  Proof.
    iIntros (LT) "(WSAT & EN & DA)".
    iMod (wsats_ownI_alloc_lt_gen _ _ _ LT p (fun i => i ∈ ↑N) with "[WSAT DA]") as "(I & D & WSAT)".
    - i. des_ifs. apply iris.base_logic.lib.invariants.fresh_inv_name.
    - iFrame.
    - iModIntro. iFrame.
  Qed.

  Lemma FUpd_alloc_gen u b A E N n p :
    n < b -> (inv u n N p -∗ ⟦p⟧) ⊢ FUpd u b A E E (inv u n N p).
  Proof.
    iIntros (LT) "P (A & W & E & D & U)".
    iMod (wsats_inv_gen with "[W E D]") as "(#INV & W & E)"; eauto. iFrame.
    iPoseProof ("P" with "INV") as "P". iPoseProof ("W" with "P") as "W".
    iModIntro. iFrame. eauto.
  Qed.

  Lemma FUpd_alloc u b A E N n p :
    n < b -> ⟦p⟧ ⊢ FUpd u b A E E (inv u n N p).
  Proof.
    iIntros (LT) "P". iApply FUpd_alloc_gen. auto. iIntros. iFrame.
  Qed. *)

  Lemma FUpd_open u b A n N E (LT : n < b) (IN : ↑N ⊆ E) p :
    inv u n N p ⊢ FUpd u b A E (E∖↑N) (⟦p⟧ ∗ ((⟦p⟧) -∗ FUpd u b A (E∖↑N) E emp)).
  Proof.
    iIntros "[% (%iN & #HI)] (A & WSAT & EN & D & R)".
    rewrite {1}(union_difference_L (↑N) E); eauto.
    iPoseProof (ownE_disjoint with "EN") as "[EN EE]"; first by set_solver.
    rewrite {1}(union_difference_singleton_L i (↑N)); eauto.
    iPoseProof (ownE_disjoint with "EN") as "[EN Ei]"; first by set_solver.
    iMod (wsats_ownI_open u b n i p with "[WSAT EN]") as "(P & SAT & Di)"; [eauto|iFrame; done|].
    iModIntro; iFrame. iIntros "P [A [WSAT [E [D UNIV]]]]".
    iMod (wsats_ownI_close u b n i p with "HI WSAT P Di") as "[SAT EE]"; first by auto.
    iModIntro; iFrame.
    iPoseProof (ownE_union with "[Ei EE]") as "EE"; iFrame.
    rewrite -union_difference_singleton_L; last by eauto.
    iPoseProof (ownE_union with "[-]") as "E"; iFrame.
    rewrite -union_difference_L; by done.
  Qed.

  (* Lemma FUpd_intro u b A E P :
    (|==> P) ⊢ FUpd u b A E E P.
  Proof.
    iIntros ">P H". iModIntro. iFrame. iFrame.
  Qed.


  Lemma FUpd_intro_mask u b A E1 E2 P :
    E2 ⊆ E1 ->
    FUpd u b A E1 E1 P ⊢ FUpd u b A E1 E2 (FUpd u b A E2 E1 P).
  Proof.
    rewrite /FUpd. iIntros (HE) "H (A & WSAT & ENS & D & R)".
    iPoseProof ("H" with "[A WSAT ENS D R]") as ">(A & (WSAT & ENS & D & R) & P)". iFrame.
    iModIntro. rewrite (union_difference_L _ _ HE).
    iPoseProof (ownE_disjoint with "ENS") as "(ENS & EN)".
    { set_solver. }
    iFrame. iIntros "(A & WSAT & ENS & D & R)". iModIntro. iFrame.
    iApply ownE_union. iFrame.
  Qed.



  (* Multiverse operations *)

  Theorem FUpd_spawn_world u b A E:
    ⊢ FUpd u b A E E (∃ v, closed_universe v 0 ⊤).
  Proof.
    unfold FUpd, closed_universe, world, free_universes, wsats. s.
    iIntros "(A & S & E & D & R)". iDestruct "R" as (eu) "EW".
    iPoseProof (empty_worlds_split with "EW") as "(EW & FA & E' & D' & L' & R')".
    iFrame. iSplitL "L'"; eauto.
    iExists eu. iFrame. eauto.
  Qed.

  Lemma FUpd_send_iprop u b A E u0 b0 E0 N n p
    (LT : n < b0)
    :
    ⟦p⟧ ∗ closed_universe u0 b0 E0
    ⊢
    FUpd u b A E E (inv u0 n N p ∗ closed_universe u0 b0 E0).
  Proof.
    iIntros "(P & F0 & S0 & E0 & D0 & R0) (A & S & E & D & R)".
    iPoseProof (FUpd_alloc with "P") as "Upd"; eauto.
    iMod ("Upd" with "[A S0 E0 D0 R0]") as "(A & (S0 & E0 & D9 & R0) & I0)".
    - iFrame. iSplitL; eauto. iAssumption.
    - iFrame; eauto.
  Qed.

  Lemma FUpd_receive_iprop u b A E u0 b0 E0 N n p
    (LT : n < b0)
    (IN : ↑N ⊆ E0)
    :
    inv u0 n N p ∗ closed_universe u0 b0 E0
    ⊢
    FUpd u b A E E (⟦p⟧ ∗ closed_universe u0 b0 (E0 ∖↑N)).
  Proof.
    iIntros "(I & F0 & S0 & E0 & D0 & R0) (A & S & E & D & R)".
    iPoseProof (FUpd_open with "I") as "Upd"; eauto.
    iMod ("Upd" with "[A S0 E0 D0 R0]") as "(A & (S0 & E0 & D0 & R0) & P & _)".
    - iFrame. iSplitL; [iAssumption|eauto].
    - iFrame; eauto.
  Qed. *)

  (* Global Instance from_modal_FUpd u b A E P :
    FromModal True modality_id (FUpd u b A E E P) (FUpd u b A E E P) P.
  Proof.
    rewrite /FromModal /= /FUpd. iIntros. iModIntro. iFrame. iFrame.
  Qed. *)

  (* Global Instance from_modal_FUpd_general u b A E1 E2 P :
    FromModal (E2 ⊆ E1) modality_id P (FUpd u b A E1 E2 P) P.
  Proof.
    rewrite /FromModal /FUpd. ss.
    iIntros (HE) "P (A & WSAT & EN & D & R)". iModIntro. iFrame.
    iPoseProof ((ownE_subset _ _ _ HE) with "EN") as "(EN1 & _)". eauto.
  Qed.

  Global Instance from_modal_FUpd_wrong_mask u b A E1 E2 P :
    FromModal (pm_error "Only non-mask-changing update modalities can be introduced directly.
  Use [FUpd_mask_frame] and [FUpd_intro_mask]")
              modality_id (FUpd u b A E1 E2 P) (FUpd u b A E1 E2 P) P | 100.
  Proof.
    intros [].
  Qed. *)

  (* Global Instance elim_modal_bupd_FUpd p u b A E1 E2 P Q :
    ElimModal True p false (|==> P) P (FUpd u b A E1 E2 Q) (FUpd u b A E1 E2 Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /FUpd.
    iIntros (_) "(>P & K) I". iApply ("K" with "P"). iFrame.
  Qed. *)

  Global Instance elim_modal_FUpd_FUpd u p b b' A E1 E2 E3 P Q :
    ElimModal (b <= b') p false (FUpd u b A E1 E2 P) P (FUpd u b' A E1 E3 Q) (FUpd u b' A E2 E3 Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim.
    iIntros (LT) "(P & K) I". inv LT.
    - rewrite /FUpd.
      iMod ("P" with "I") as "(A & (WSAT & EN & R) & P)". iApply ("K" with "P"). iFrame.
    - iPoseProof (FUpd_mono _ b (S m) with "P") as "P". lia.
      rewrite /FUpd.
      iMod ("P" with "I") as "(A & (WSAT & EN & R) & P)". iApply ("K" with "P"). iFrame.
  Qed.

  Global Instance elim_modal_FUpd_FUpd_general p u b A E0 E1 E2 E3 P Q :
    ElimModal (E0 ⊆ E2) p false
              (FUpd u b A E0 E1 P)
              P
              (FUpd u b A E2 E3 Q)
              (FUpd u b A (E1 ∪ (E2 ∖ E0)) (E3) Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim. ss.
    iIntros (HE) "[M K]".
    iPoseProof (FUpd_mask_frame _ _ _ _ _ (E2 ∖ E0) with "M") as "M".
    { set_solver. }
    replace (E0 ∪ E2 ∖ E0) with E2 by (eapply union_difference_L; ss).
    iMod "M". iPoseProof ("K" with "M") as "M". iFrame.
  Qed.

  Global Instance elim_acc_FUpd
         {X : Type} u b A E1 E2 E (γ δ : X -> iProp) (mγ : X -> option iProp) (Q : iProp) :
    ElimAcc True (FUpd u b A E1 E2) (FUpd u b A E2 E1) γ δ mγ (FUpd u b A E1 E Q)
      (fun x : X => ((FUpd u b A E2 E2 (δ x)) ∗ (mγ x -∗? FUpd u b A E1 E Q))%I).
  Proof.
    iIntros (_) "Hinner >[% [Hα Hclose]]".
    iPoseProof ("Hinner" with "Hα") as "[>Hβ Hfin]".
    iPoseProof ("Hclose" with "Hβ") as ">Hγ".
    iApply "Hfin". iFrame.
  Qed.

  Global Instance into_acc_FUpd_inv u b A E n N p :
    IntoAcc (inv u n N p) (n < b /\ (↑N) ⊆ E) True
            (FUpd u b A E (E ∖ ↑N))
            (FUpd u b A (E ∖ ↑N) E)
            (fun _ : () => ⟦p⟧) (fun _ : () => ⟦p⟧) (fun _ : () => None).
  Proof.
    rewrite /IntoAcc. iIntros ((LT & iE)) "INV _". rewrite /accessor.
    iPoseProof (FUpd_open _ _ _ _ _ _ LT iE with "INV") as ">[open close]".
    iModIntro. iExists tt. iFrame.
  Qed.

  (* Global Instance elim_modal_iupd_FUpd p u b A E1 E2 P Q :
    ElimModal True p false (#=(A)=> P) P (FUpd u b A E1 E2 Q) (FUpd u b A E1 E2 Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /FUpd.
    iIntros (_) "[P K] [A I]".
    iMod ("P" with "A") as "[A P]". iApply ("K" with "P"). iFrame.
  Qed. *)

  (* Global Instance into_acc_FUpd_world u b A E n N p :
    IntoAcc (inv u n N p) (n < b /\ (↑N) ⊆ E) True
            (FUpd u b A E (E ∖ ↑N))
            (FUpd u b A (E ∖ ↑N) E)
            (fun _ : () => ⟦p⟧) (fun _ : () => ⟦p⟧) (fun _ : () => None).
  Proof.
    rewrite /IntoAcc. iIntros ((LT & iE)) "INV _". rewrite /accessor.
    iPoseProof (FUpd_open _ _ _ _ _ _ LT iE with "INV") as ">[open close]".
    iModIntro. iExists tt. iFrame.
  Qed. *)

  (* TODO:
     Needs to register the fancy update rules for multivere operations.
  *)

End FANCY_UPDATE.

Global Opaque FUpd. *)

(* Goal (nroot .@ "gil") ## (nroot .@ "hur"). *)
(* eauto with solve_ndisj. *)
