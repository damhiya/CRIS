From stdpp Require Export namespaces coPset.
Require Import sflib.
From iris.algebra Require Import ofe auth agree coPset gset gmap_view.
From iris Require Import bi.big_op.
Require Import Coqlib.
Require Import functions.
Require Export SRF sProp own.

Definition univ_id := nat.

(* Resource algebra & initial resources for invariants *)
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

  Class invGΣ (α : SRFCons.t) (Σ : GRA) := {
    #[local] invG_I :: inG ownIRA Σ
  }.
  Class invGΓ (Γ : HRA) := {
    #[local] invG_E :: inG ownERA Γ;
    #[local] invG_D :: inG ownDRA Γ;
  }.

  Class invG (α : SRFCons.t) (Σ : GRA) (Γ : HRA) := {
    #[local] invG_Σ :: invGΣ α Σ;
    #[local] invG_Γ :: invGΓ Γ;
  }.

  Definition invΓ : HRA := #[ownERA; ownDRA].
  Definition invΣ : GRA := #[ownIRA].

  Global Instance subG_invΣ {α' Σ} : subG invΣ Σ → invGΣ α' Σ.
  Proof. solve_inG. Defined.
  Global Instance subG_invΓ {Γ : HRA} : subG invΓ Γ → invGΓ Γ.
  Proof. solve_inG. Defined.
  Global Instance invG_subG {α' Σ Γ} : invGΣ α' Σ → invGΓ Γ → invG α' Σ Γ.
  Proof. i; ss. Defined.

  (* Initial resources for invariants *)
  Definition ir_ownIRA u' : DRA_mk ownIRA :=
    λ u n, if (decide (u <= u')) then gmap_view_auth (DfracOwn 1) ∅ else ε.
  Lemma ir_ownIRA_valid u : ✓ ir_ownIRA u.
  Proof.
    rewrite /ir_ownIRA; intros u' n'; des_ifs.
    { apply gmap_view_auth_valid. }
    { apply ucmra_unit_valid. }
  Qed.

  Definition ir_ownERA u' : DRA_mk ownERA :=
    λ u, if (decide (u <= u')) then CoPset ⊤ else ε.
  Lemma ir_ownERA_valid u : ✓ ir_ownERA u.
  Proof. rewrite /ir_ownERA; intros u'; des_ifs. Qed.

  Definition ir_ownDRA u' : DRA_mk ownDRA :=
    λ u, if (decide (u <= u')) then ● (GSet ∅) else ε.
  Lemma ir_ownDRA_valid u : ✓ ir_ownDRA u.
  Proof.
    rewrite /ir_ownDRA; intros u'; des_ifs.
    { apply auth_auth_valid; ss. }
    { apply ucmra_unit_valid. }
   Qed.

  Definition ir_invΓ u : invΓ :=
    *[Some (ir_ownERA u); Some (ir_ownDRA u)].
  Definition ir_invΣ u : invΣ :=
    *[Some (ir_ownIRA u)].
End invariants.
Hint Unfold invG_I invG_Σ invG_subG subG_invΣ subG_inG invG_E invG_Γ subG_invΓ invG_D : GRA_index.

Section predicates.
  Context `{!subG (Γ : HRA) Σ, !invG α Σ Γ}.
  Local Existing Instances invG_Σ invG_Γ invG_I invG_E invG_D.

  (* owns an invariant *)
  Definition ownIR (u : univ_id) (n : level) (i : positive) (p : SRFSyn.t n) : ownIRA :=
    discrete_fun_singleton u
      (discrete_fun_singleton n
        (gmap_view_frag i DfracDiscarded (to_agree p))).
  Definition ownI (u : univ_id) (n : level) (i : positive) (p : SRFSyn.t n) : iProp Σ :=
    own base_γ (ownIR u n i p).

  Global Instance ownI_persistent
    u n i p : Persistent (ownI u n i p).
  Proof. apply _. Qed.

  (* authorative resource *)
  Definition ownI_authR (u : univ_id) (n : level) (I : gmap positive (SRFSyn.t n)) : ownIRA :=
    discrete_fun_singleton u
      (discrete_fun_singleton n
        (gmap_view_auth (DfracOwn 1) (to_agree <$> I))).
  Definition ownI_auth (u : univ_id) (n : level) (I : gmap positive (SRFSyn.t n)) :=
    own base_γ (ownI_authR u n I).

  (* authorative resource for wsats *)
  Definition wsat_authR u b : ownIRA :=
    discrete_fun_singleton u
      ((λ n, if (decide (n < b)) then ε else gmap_view_auth (DfracOwn 1) ∅) : discrete_funUR InvSetRA).
  Definition wsat_auth u b : iProp Σ := own base_γ (wsat_authR u b).

  (* namespaces *)
  Definition ownER (u : univ_id) (E : coPset) : ownERA :=
    discrete_fun_singleton u (CoPset E).
  Definition ownE (u : univ_id) (E : coPset) : iProp Σ :=
    own base_γ (ownER u E).

  (* disabled *)
  Definition ownDR (u : univ_id) (D : gset positive) : ownDRA :=
    discrete_fun_singleton u (◯ (GSet D)).
  Definition ownD (u : univ_id) (D : gset positive) : iProp Σ :=
    own base_γ (ownDR u D).

  Definition ownD_authR  (u : univ_id) (D : gset positive) : ownDRA :=
    discrete_fun_singleton u (● (GSet D)).
  Definition ownD_auth (u : univ_id) : iProp Σ :=
    ∃ D, own base_γ (ownD_authR u D).

  (* predicate rules *)
  Lemma ownE_exploit u (E1 E2 : coPset) :
    ownE u E1 ∗ ownE u E2 ⊢ ⌜E1 ## E2⌝.
  Proof.
    iIntros "[H1 H2]". iCombine "H1 H2" gives %WF.
    by rewrite discrete_fun_singleton_op discrete_fun_singleton_valid coPset_disj_valid_op in WF.
  Qed.

  Lemma ownE_op u (E1 E2 : coPset) :
    E1 ## E2 → ownE u (E1 ∪ E2) ⊣⊢ ownE u E1 ∗ ownE u E2.
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
  Context `{@SRFIntp.t (domain Σ) α, !invG α Σ Γ, !subG Γ Σ}.

  Variable u : univ_id.
  Variable n : level.

  Definition inv_satall (I : gmap positive (SRFSyn.t n)) : iProp Σ :=
    [∗ map] i ↦ p ∈ I, (⟦p⟧ ∗ ownD u {[i]}) ∨ ownE u {[i]}.

  Definition wsat : iProp Σ := ∃ I, ownI_auth u n I ∗ inv_satall I.

  Lemma alloc_name φ (INF : pred_infinite φ) :
    ownD_auth u ⊢ |==> ownD_auth u ∗ ∃ i, ⌜φ i⌝ ∧ ownD u {[i]}.
  Proof.
    iIntros "[% DA]".
    rewrite (pred_infinite_set φ (C:=gset positive)) in INF.
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

  Lemma wsat_init : ownI_auth u n ∅ ⊢ wsat.
  Proof. iIntros "H"; iExists ∅; iFrame; iApply big_sepM_empty; ss. Qed.
End wsat.

Section wsats.
  Context `{@SRFIntp.t (domain Σ) α, !invG α Σ Γ, !subG Γ Σ}.
  Local Existing Instances invG_Σ invG_Γ invG_I invG_E invG_D.

  Lemma wsat_authR_valid u : ✓ (wsat_authR u 0).
  Proof.
    rewrite /wsat_authR discrete_fun_singleton_valid.
    intros i; des_ifs; [lia | apply gmap_view_auth_valid].
  Qed.

  Lemma wsat_authR_S u n : wsat_authR u n ~~> wsat_authR u (S n) ⋅ ownI_authR u n ∅.
  Proof.
    rewrite {1}/wsat_authR; etrans.
    { eapply discrete_fun_singleton_update; erewrite (discrete_fun_delete n); refl. }
    rewrite -discrete_fun_singleton_op; eapply cmra_update_op.
    { rewrite /wsat_authR; eapply discrete_fun_singleton_update, discrete_fun_update.
      intros a; des_ifs; try lia.
    }
    des_ifs; lia.
  Qed.

  Lemma wsat_authR_alloc u n n' :
    n <= n' →
    wsat_authR u n ~~> (wsat_authR u n' ⋅ ([^ (⋅) list] x ∈ (seq n (n' - n)), ownI_authR u x ∅)).
  Proof.
    intros LE; induction LE.
    { rewrite Nat.sub_diag /= right_id //. }
    { etrans; first apply IHLE.
      etrans; first eapply cmra_update_op; [eapply wsat_authR_S|refl|].
      rewrite -assoc; apply cmra_update_op; ss.
      replace (S m - n) with (S (m - n)) by lia.
      rewrite seq_S big_opL_app //=; replace (n + (m - n)) with m by lia.
      rewrite comm; eapply cmra_update_op; ss; rewrite right_id //.
    }
  Qed.

  Definition wsatl u n : iProp Σ := [∗ list] x ∈ (seq 0 n), wsat u x.

  Definition wsatl_split u n m : n < m → wsatl u m ⊣⊢ wsat u n ∗ (wsat u n -∗ wsatl u m).
  Proof.
    rewrite /wsatl; intros LT; replace m with (n + S (m - S n)) by lia.
    rewrite seq_app big_sepL_app /=.
    iSplit.
    { iIntros "[$ [$ $]] $". }
    { iIntros "[H1 H2]"; iApply "H2"; iFrame. }
  Qed.

  Lemma wsatl_mon u n n' :
    n <= n' →
    wsat_auth u n ∗ wsatl u n ==∗ wsat_auth u n' ∗ wsatl u n'.
  Proof.
    intros LE; iIntros "[AU WL]"; rewrite {1}/wsat_auth.
    iPoseProof (own_update with "AU") as "> [$ AU]"; first apply (wsat_authR_alloc _ _ n'); ss.
    iPoseProof (big_opL_own_1 with "AU") as "AU".
    rewrite {2}/wsatl; replace n' with (n + (n' - n)) at 2 by lia.
    rewrite seq_app big_sepL_app; iFrame; ss.
    iApply big_sepL_bupd; iApply (big_sepL_impl with "AU").
    iModIntro; iIntros (k x) "% A !>"; rewrite /wsat; iExists ∅; iFrame.
    rewrite /inv_satall; ss.
  Qed.

  Lemma wsatl_alloc u n : wsat_auth u 0 ==∗ wsatl u n.
  Proof.
    iIntros "A"; iMod (wsatl_mon u 0 n with "[A]") as "[A W]"; [lia|iFrame|iFrame]; ss.
    rewrite /wsatl //=.
  Qed.

  Definition wsats u n E : iProp Σ := wsat_auth u n ∗ ownE u E ∗ ownD_auth u ∗ wsatl u n.

  Lemma wsats_mon u n n' E : n <= n' → wsats u n E ==∗ wsats u n' E.
  Proof. iIntros "%LT [A [$ [$ W]]]"; iApply wsatl_mon; eauto; iFrame. Qed.

  Definition univs u n : iProp Σ := [∗ list] x ∈ (seq 0 u), wsats x n ⊤.

  Lemma univs_split u v n :
    v < u →
    univs u n ⊣⊢ univs v n ∗ wsats v n ⊤ ∗ (univs v n -∗ wsats v n ⊤ -∗ univs u n).
  Proof.
    intros LT; iSplit; last (iIntros "[H1 [H2 H3]]"; iApply ("H3" with "H1 H2")).
    iIntros "H"; rewrite {1 4}/univs.
    replace u with (v + S (u - S v)) by lia.
    rewrite seq_app /= ?big_sepL_app ?big_sepL_cons. iDestruct "H" as "[$ [$ H]]".
    iIntros "$ $"; done.
  Qed.

  Lemma univs_mon u n n' : n <= n' → univs u n ==∗ univs u n'.
  Proof.
    iIntros "%LT U"; iApply big_sepL_bupd; iApply (big_sepL_impl with "U").
    iIntros "!> %k %x %IN W"; iApply wsats_mon; eauto.
  Qed.

  (* For cancellation *)
  Lemma ir_ownIRA_cons u : ir_ownIRA (S u) ≡ wsat_authR (S u) 0 ⋅ ir_ownIRA u.
  Proof.
    rewrite (discrete_fun_delete (S u) (ir_ownIRA (S u))) comm.
    f_equiv.
    { rewrite /ir_ownIRA; des_ifs; try lia. }
    { intros x; des_ifs; ss.
      { rewrite /ir_ownIRA; des_ifs; try lia. }
      { rewrite /ir_ownIRA; des_ifs; try lia. }
    }
  Qed.
  Lemma ir_ownERA_cons u : ir_ownERA (S u) ≡ ownER (S u) ⊤ ⋅ ir_ownERA u.
  Proof.
    rewrite (discrete_fun_delete (S u) (ir_ownERA (S u))) comm.
    f_equiv.
    { rewrite /ir_ownERA; des_ifs; try lia. }
    { intros x; des_ifs; ss.
      { rewrite /ir_ownERA; des_ifs; try lia. }
      { rewrite /ir_ownERA; des_ifs; try lia. }
    }
  Qed.

  Lemma ir_ownDRA_cons u : ir_ownDRA (S u) ≡ ownD_authR (S u) ∅ ⋅ ir_ownDRA u.
  Proof.
    rewrite (discrete_fun_delete (S u) (ir_ownDRA (S u))) comm.
    f_equiv.
    { rewrite /ir_ownDRA; des_ifs; try lia. }
    { intros x; des_ifs; ss.
      { rewrite /ir_ownDRA; des_ifs; try lia. }
      { rewrite /ir_ownDRA; des_ifs; try lia. }
    }
  Qed.

  Lemma make_wsats u :
    own base_γ (ir_ownIRA u)
    ∗ own base_γ (ir_ownERA u)
    ∗ own base_γ (ir_ownDRA u)
    ⊢ univs u 0 ∗ wsats u 0 ⊤.
  Proof.
    induction u; ss; iIntros "[I [E D]]".
    { iSplitR.
      { rewrite /univs //. }
      { rewrite /wsats. iSplitL "I".
        { rewrite (discrete_fun_delete 0 (ir_ownIRA 0)); iDestruct "I" as "[_ $]". }
        { iSplitL "E".
          { rewrite (discrete_fun_delete 0 (ir_ownERA 0)); iDestruct "E" as "[_ $]". }
          { iSplitL "D"; last rewrite /wsatl //.
            rewrite (discrete_fun_delete 0 (ir_ownDRA 0)); iDestruct "D" as "[_ $]".
          }
        }
      }
    }
    rewrite ir_ownIRA_cons. iDestruct "I" as "[I1 I2]".
    rewrite ir_ownERA_cons. iDestruct "E" as "[E1 E2]".
    rewrite ir_ownDRA_cons. iDestruct "D" as "[D1 D2]".
    iSplitR "I1 E1 D1".
    { iPoseProof (IHu with "[$]") as "[A B]". rewrite {2}/univs seq_S big_opL_app /=. iFrame. }
    { rewrite /wsats. iFrame. rewrite /wsatl /= //. }
  Qed.

  (* Definitions for fancy updates & invariants *)
  Local Definition uPred_fupd_def u b (E1 E2 : coPset) (P : iProp Σ) : iProp Σ :=
    wsatl u b ∗ ownE u E1 ∗ ownD_auth u ==∗ (wsatl u b ∗ ownE u E2 ∗ ownD_auth u ∗ P).
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
      rewrite /fupd uPred_fupd_eq /uPred_fupd_def /wsats ownE_op //.
      by iIntros "[$ [[$ $] $]] !> [$ [$ $]]".
    - rewrite /fupd uPred_fupd_eq /uPred_fupd_def /wsats /bi_except_0.
      iIntros (E1 E2 P) "[H | H]"; iFrame.
      iDestruct (uPred.later_eq with "H") as "H"; by iFrame.
    - rewrite /fupd uPred_fupd_eq /uPred_fupd_def /wsats.
      iIntros (E1 E2 P Q HPQ) "HP HwE". rewrite -HPQ. by iApply "HP".
    - rewrite /fupd uPred_fupd_eq /uPred_fupd_def /wsats. iIntros (E1 E2 E3 P) "HP HwE".
      iMod ("HP" with "HwE") as "[HA [? [? HP]]]". iApply "HP"; by iFrame.
    - intros E1 E2 Ef P HE1Ef. rewrite /fupd uPred_fupd_eq /uPred_fupd_def /wsats ownE_op //.
      iIntros "Hupd [W [[E1 Ef] D]]".
      iMod ("Hupd" with "[W E1 D]") as "[$ [E2 [$ P]]]"; iFrame.
      iPoseProof (ownE_exploit with "[Ef E2]") as "%DISJ"; first iFrame.
      iModIntro; rewrite ownE_op //=.
      iFrame. iApply "P"; done.
    - rewrite /fupd uPred_fupd_eq /uPred_fupd_def /wsats. by iIntros (????) "[HwP $]".
  Qed.
  Global Instance uPred_bi_fupd u n : BiFUpd (iProp Σ) :=
    {| bi_fupd_mixin := (uPred_fupd_mixin u n) |}.
  Global Instance uPred_bi_bupd_fupd u n :
    @BiBUpdFUpd (iProp Σ) (uPred_bi_bupd Σ) (uPred_bi_fupd u n).
  Proof. rewrite /BiBUpdFUpd uPred_fupd_unseal. by iIntros (E P) ">? [$ [$ $]] !>". Qed.

  Local Definition inv_def u (n : level) (N : namespace) (p : SRFSyn.t n) : iProp Σ :=
    ∃ i, ⌜i ∈ (↑N : coPset)⌝ ∧ ownI u n i p.
  Local Definition inv_aux : seal (@inv_def). Proof. by eexists. Qed.
  Definition inv := inv_aux.(unseal).
  Local Definition inv_eq : @inv = @inv_def := inv_aux.(seal_eq).

  Global Instance inv_persistent u n N p : Persistent (inv u n N p).
  Proof. rewrite inv_eq /inv_def. apply _. Qed.
End wsats.

Notation fupd_ex u n :=
  (@fupd (bi_car (iProp _)) (@bi_fupd_fupd _ (uPred_bi_fupd u n))) (only parsing).

Notation "'=|' u ',' n '|={' E1 ',' E2 '}=>' P" := (fupd_ex u n E1 E2 P) (at level 90) : stdpp_scope.
Notation "P '=|' u ',' n '|={' E1 ',' E2 '}=∗' Q" := (P -∗ =|u, n|={E1,E2}=> Q) (at level 90) : stdpp_scope.

Notation "'=|' u ',' n '|={' E '}=>' P" := (=|u, n|={E, E}=> P) (at level 90) : stdpp_scope.
Notation "P '=|' u ',' n '|={' E '}=∗' Q" := (P -∗ =|u, n|={E, E}=> Q) (at level 90) : stdpp_scope.

Notation "'=|' u ',' n '|={' E1 ',' E2 '}=>' P" := (fupd_ex u n E1 E2 P)%I (at level 90) : bi_scope.
Notation "P '=|' u ',' n '|={' E1 ',' E2 '}=∗' Q" := (P -∗ =|u, n|={E1,E2}=> Q)%I (at level 90) : bi_scope.

Notation "'=|' u ',' n '|={' E '}=>' P" := (=|u, n|={E, E}=> P)%I (at level 90) : bi_scope.
Notation "P '=|' u ',' n '|={' E '}=∗' Q" := (P -∗ =|u, n|={E, E}=> Q)%I (at level 90) : bi_scope.

Section fancy_updates.
  Context `{@SRFIntp.t (domain Σ) α, !invG α Σ Γ, !subG Γ Σ}.
  Implicit Types n m : level.
  Implicit Types N : namespace.
  Implicit Types E : coPset.

  Lemma fupd_mon u n m E1 E2 P : n <= m → =|u, n|={E1, E2}=> P -∗ =|u, m|={E1, E2}=> P.
  Proof.
    intros LT; rewrite ?uPred_fupd_unseal /uPred_fupd_def ?inv_eq /inv_def.
    iIntros "P [W [E D]]".
    rewrite {3}/wsatl; replace m with (n + (m - n)) at 1 by lia; rewrite seq_app big_sepL_app.
    iDestruct "W" as "[WN W]"; iMod ("P" with "[WN E D]") as "[P [$ [$ $]]]"; iFrame.
    rewrite {2}/wsatl; replace m with (n + (m - n)) at 2 by lia; rewrite seq_app big_sepL_app /=.
    iFrame; done.
  Qed.
End fancy_updates.

Section inv.
  Context `{@SRFIntp.t (domain Σ) α, !invG α Σ Γ, !subG Γ Σ}.
  Implicit Types n : level.
  Implicit Types N : namespace.
  Implicit Types E : coPset.

  Lemma fresh_inv_name N : pred_infinite (.∈ (↑N:coPset)).
  Proof. apply coPset_infinite_finite, nclose_infinite. Qed.

  Lemma inv_alloc {n} (p : SRFSyn.t n) u m E N :
    n < m → ⟦p⟧ =|u, m|={E}=∗ inv u n N p.
  Proof.
    rewrite ?uPred_fupd_unseal /uPred_fupd_def ?inv_eq /inv_def.
    iIntros (LT) "P [W [E D]]".
    iPoseProof (wsatl_split u n with "W") as "[W A]"; first done.
    (* iPoseProof (wsats_split with "W") as "[? [? [D [W ?]]]]"; first done. *)
    iMod (wsat_ownI_alloc _ _ _ (.∈ (↑N : coPset)) with "[D W P]") as "[[%i [%Hi #HiP]] [? ?]]".
    { apply fresh_inv_name. }
    { iFrame. }
    rewrite {2}(wsatl_split u n); ss; iFrame.
    iModIntro; iExists _; iSplit; eauto.
  Qed.

  Lemma inv_acc u n m N (p : SRFSyn.t n) E :
    n < m → ↑N ⊆ E → inv u n N p =|u, m|={E, E∖↑N}=∗ (⟦p⟧ ∗ (⟦p⟧ =|u, m|={E∖↑N, E}=∗ True)).
  Proof.
    rewrite ?uPred_fupd_unseal /uPred_fupd_def ?inv_eq /inv_def.
    iDestruct 1 as (i) "[Hi #HiP]".
    iDestruct "Hi" as % ?%elem_of_subseteq_singleton.
    rewrite {1}(wsatl_split u n) //; iIntros "[[W R] [E D]]".
    rewrite {1}(union_difference_L (↑ N) E) // ownE_op; last set_solver.
    rewrite {1}(union_difference_L {[ i ]} (↑ N)) // ownE_op; last set_solver.
    iDestruct "E" as "[[E1 E3] E2]".
    iPoseProof (wsat_ownI_open with "[HiP W E1]") as "> [P [W D2]]"; first by iFrame.
    iPoseProof ("R" with "W") as "W"; iFrame.
    rewrite {1}(wsatl_split u n) //; iIntros "!> P [[W R] [E D]]".
    iPoseProof (wsat_ownI_close with "[W P D2]") as "> [W E2]"; first by iFrame.
    rewrite {2}(union_difference_L (↑ N) E) // ownE_op; last set_solver.
    rewrite {3}(union_difference_L {[ i ]} (↑ N)) // ownE_op; last set_solver; iFrame.
    iModIntro; iApply "R"; iFrame.
  Qed.

  Global Instance from_modal_fupd u n E1 E2 P :
    FromModal (E2 ⊆ E1) modality_id (=|u, n|={E1,E2}=> P) (=|u, n|={E1,E2}=> P) P.
  Proof.
    rewrite /FromModal ?uPred_fupd_unseal /uPred_fupd_def ?inv_eq /inv_def /=.
    iIntros (IN) "$ W !>".
    rewrite (union_difference_L E2 E1) // /wsats ownE_op; last set_solver.
    iDestruct "W" as "[$ [[$ ?] $]]".
  Qed.

  Global Instance into_acc_inv u n m E N p :
    IntoAcc (inv u n N p) (n < m ∧ (↑N ⊆ E)) True
            (fupd_ex u m E (E ∖ ↑N))
            (fupd_ex u m (E ∖ ↑N) E)
            (λ _ : (), ⟦p⟧) (λ _ : (), ⟦p⟧) (λ _ : (), None).
  Proof.
    rewrite /IntoAcc /accessor bi.exist_unit.
    iIntros ((? & ?)) "#INV _". by iApply inv_acc.
  Qed.

  Global Instance elim_modal_fupd_fupd_gen p u n m E0 E1 E2 E3 P Q :
    ElimModal (n <= m ∧ E0 ⊆ E2) p false
              (=|u, n|={E0,E1}=> P) P
              (=|u, m|={E2,E3}=> Q) (=|u, m|={E1 ∪ E2 ∖ E0, E3}=> Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim.
    iIntros ([LE SUB]) "[P K]".
    iPoseProof (fupd_mon u n m with "P") as "P"; ss.
    rewrite ?uPred_fupd_unseal /uPred_fupd_def ?inv_eq /inv_def /=.
    iIntros "[WL [E D]]".
    rewrite {2}(union_difference_L E0 E2) // (ownE_op u (E0)); last set_solver.
    iDestruct "E" as "[E1 E2]".
    iPoseProof ("P" with "[WL E1 D]") as "> [W [E [D P]]]"; first iFrame.
    iApply ("K" with "P [W E E2 D]"); iFrame.
    iPoseProof (ownE_exploit with "[E E2]") as "%D"; iFrame.
    rewrite ownE_op; ss; iFrame.
  Qed.

  Global Instance elim_modal_fupd_fupd_simple p u n m E1 E2 E3 P Q :
    ElimModal (n <= m) p false (=|u, n|={E1,E2}=> P) P (=|u, m|={E1,E3}=> Q) (=|u, m|={E2,E3}=> Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim.
    iIntros (LE) "[P K]".
    iPoseProof (fupd_mon u n m with "P") as "P"; ss.
    iMod "P". iMod ("K" with "P") as "K"; iModIntro; ss.
  Qed.
End inv.