Require Import DecimalString.
Require Import sflib.
From stdpp Require Export namespaces coPset.
From iris.algebra Require Import ofe auth agree coPset gset gmap_view csum excl.
From iris.proofmode Require Import proofmode.
From iris Require Import bi.big_op.
Require Import functions allocs.
Require Import Coqlib.
Require Export SAT sProp own precise.

Definition univ_id := nat.

(* Resource algebra & initial resources for invariants *)
Section invariants.
  Context `{Γ : HRA, Σ : GRA, α : GAT.t}.

  Canonical Structure SynO n : ofe := leibnizO (GTerm.t n).

  Definition InvSetRA n : ucmra :=
    allocsUR positive (prodR (optionUR (exclR unitO)) (agreeR (SynO n))).
(* 
  (** IMPROVE : This is a temporary Proper typeclass to resolve rewrite lemmas for
      GTerm.t types. TC resolution fails to apply general discrete_fun_singleton_proper
      since GTerm.t types are also dependent on α. This can be generalized further. *)
  Global Instance discrete_fun_singleton_proper' (x : univ_id) :
    Proper
      ((≡) ==> (≡))
      (discrete_fun_singleton (B := (λ _, discrete_funUR InvSetRA)) x).
  Proof using.
    intros x1 x2 H' u. destruct (decide (u = x)); last first.
    { rewrite ! discrete_fun_lookup_singleton_ne; eauto. }
    clarify; rewrite ! discrete_fun_lookup_singleton; eauto.
  Qed. *)

  Definition ownIRA : ucmra := discrete_funUR InvSetRA.
  Definition ownERA : ucmra := coPset_disjUR.
  Definition ownDRA : ucmra := coPset_disjUR. (* TODO : Erase *)

  Class invG := {
    #[local] invG_E :: inG ownERA Γ;
    (* #[local] invG_D :: inG ownDRA Γ; *)
    #[local] invG_I :: inG ownIRA Σ;
  }.

  (* Definition invΓ : HRA := #[ownERA; ownDRA]. *)
  Definition invΓ : HRA := #[ownERA].
  Definition invΣ : GRA := #[ownIRA].

  Global Instance subG_invG : subG invΣ Σ → subG invΓ Γ → invG.
  Proof using. solve_inG. Defined.
  
  (* Initial resources for invariants *)
  Definition ir_ownIRA : DRA_mk ownIRA := λ n, allocs_auth _ (λ i, True).
  Lemma ir_ownIRA_valid : ✓ ir_ownIRA.
  Proof using. rewrite /ir_ownIRA; intros n'; apply allocs_auth_valid. Qed.

  Definition ir_ownERA : DRA_mk ownERA := CoPset ⊤.
  Lemma ir_ownERA_valid : ✓ ir_ownERA.
  Proof using. rewrite /ir_ownERA //. Qed.

  Definition ir_ownDRA : DRA_mk ownDRA := CoPset ⊤.
  Lemma ir_ownDRA_valid : ✓ ir_ownDRA.
  Proof using. rewrite /ir_ownDRA //. Qed.

  (* Definition ir_invΓ : invΓ := *[Some (ir_ownERA); Some (ir_ownDRA)]. *)
  Definition ir_invΓ : invΓ := *[Some (ir_ownERA)].
  Definition ir_invΣ : invΣ := *[Some (ir_ownIRA)].
End invariants.
Global Arguments invG : clear implicits.
Hint Unfold invG_I invG_E subG_invG subG_inG : GRA_index.

Section predicates.
  Context `{!subG (Γ : HRA) Σ, !invG Γ Σ α}.
  Local Existing Instances invG_I invG_E.
  Implicit Types (n : level) (i : positive).

  (* owns an invariant *)
  Definition ownIR {n} i (p : GTerm.t n) : ownIRA :=
    discrete_fun_singleton n (allocs_frag i (None, (to_agree p))).
  Definition ownI {n} i (p : GTerm.t n) : iProp Σ :=
    own base_γ (ownIR i p).

  Global Instance ownI_persistent n i p : Persistent (@ownI n i p).
  Proof using. apply _. Qed.

  (* authorative resources *)
  Definition ownI_reserveR n (X : coPset) : ownIRA :=
    discrete_fun_singleton n (allocs_auth _ (λ i, i ∈ X)).
  Definition ownI_reserve n (X : coPset) : iProp Σ :=
    own base_γ (ownI_reserveR n X).
  Definition ownD {n} i p : iProp Σ :=
    own base_γ (discrete_fun_singleton n (allocs_frag i (Some (Excl ()), to_agree p))).
  (* Definition ownI_auth {n} (I : gmap positive (GTerm.t n)) : iProp Σ :=
    [∗ map] i ↦ p ∈ I, ownI i p. *)

  (* authorative resource for wsats *)
  Definition wsat_authR (b : nat) (X : coPset) : ownIRA :=
    (λ n, if (decide (n < b)) then ε else (allocs_auth _ (λ i, i ∈ X))).
  Definition wsat_auth b X : iProp Σ := own base_γ (wsat_authR b X).

  Definition ownE (E : coPset) : iProp Σ := own base_γ (CoPset E).
  (* Definition ownD (D : coPset) : iProp Σ := own base_γ (CoPset D). *)

  (* Definition ownD_auth (D : coPset) : iProp Σ :=
    ∃ X, ⌜set_infinite X ∧ X ⊆ D⌝ ∗ own base_γ (CoPset X). *)

  (* predicate rules *)
  Lemma ownE_exploit (E1 E2 : coPset) : ownE E1 ∗ ownE E2 ⊢ ⌜E1 ## E2⌝.
  Proof using. iIntros "[H1 H2]". by iCombine "H1 H2" gives %WF%coPset_disj_valid_op. Qed.
  Lemma ownE_op (E1 E2 : coPset) : E1 ## E2 → ownE (E1 ∪ E2) ⊣⊢ ownE E1 ∗ ownE E2.
  Proof using. intros dis; rewrite -own_op coPset_disj_union; ss. Qed.
  Lemma ownE_subset (E1 E2 : coPset) :
    E1 ⊆ E2 →
    ownE E2 ⊢ ownE E1 ∗ (ownE E1 -∗ ownE E2).
  Proof using.
    iIntros (SUB) "E".
    rewrite (union_difference_L E1 E2); [|done].
    iPoseProof (ownE_op with "E") as "[E1 E2]"; [set_solver|].
    iFrame. iIntros "E1".
    iApply ownE_op; [set_solver|iFrame].
  Qed.
  Lemma ownD_ownI {n} i (p : GTerm.t n) : ownD i p ⊢ ownI i p ∗ ownD i p.
  Proof using.
    rewrite /ownI /ownIR /ownD -own_op discrete_fun_singleton_op allocs_frag_op -pair_op.
    rewrite left_id agree_idemp //.
  Qed.

  Lemma ownI_reserve_pick X Y {n} (p : GTerm.t n) :
    set_infinite Y → Y ⊆ X →
    ownI_reserve n X ⊢ |==> ∃ i, ⌜i ∈ Y⌝ ∗ ownI_reserve n (X ∖ {[i]}) ∗ ownD i p.
  Proof using.
    iIntros (INF Hsub) "R".
    hexploit coPpick_elem_of; first (apply coPset_infinite_finite; done); intros Hin.
    erewrite (union_difference_singleton_L (coPpick Y) X); last set_solver.
    rewrite {1}/ownI_reserve {1}/ownI_reserveR.
    iMod (own_update with "R") as "R".
    { apply discrete_fun_singleton_update.
      eapply (allocs_alloc (Some (Excl ()), to_agree p) _ (.∈ X ∖ {[coPpick Y]}) (coPpick Y)); ss.
      { ii; set_solver. }
      { split; set_solver. }
    }
    rewrite -discrete_fun_singleton_op; iDestruct "R" as "[R $]".
    iSplitR; first (iPureIntro; set_solver).
    rewrite difference_union_distr_l_L difference_diag_L union_empty_l_L difference_twice_L //.
  Qed.
  (* Context (i : positive) (s : coPset).
  Goal ∀ i, Decision ((.∈ s) i). typeclasses eauto.
  Local Instance decision_test P k : ∀ k, Decision (P k) → ∀  *)
  Lemma ownI_reserve_split X Y {n} :
    X ∩ Y = ∅ →
    ownI_reserve n (X ∪ Y) ⊣⊢ ownI_reserve n X ∗ ownI_reserve n Y.
  Proof using.
    iIntros (?); rewrite /ownI_reserve /ownI_reserveR -own_op discrete_fun_singleton_op.
    rewrite (allocs_auth_split_2 (.∈X∪Y) (.∈X)(.∈Y)); ss.
    { ii; set_solver. }
    { ii; set_solver. }
  Qed.

  Lemma wsat_auth_split X Y n :
    X ## Y →
    wsat_auth n (X ∪ Y) ⊣⊢ wsat_auth n X ∗ wsat_auth n Y.
  Proof using.
    intros Hdisj; rewrite /wsat_auth -own_op /wsat_authR.
    f_equiv; intros i; rewrite discrete_fun_lookup_op; des_ifs.
    rewrite (allocs_auth_split_2 (.∈X∪Y) (.∈X) (.∈Y)) //=; try set_solver.
  Qed.
  Lemma wsat_auth_merge n X Y :
    wsat_auth n X ∗ wsat_auth n Y -∗ wsat_auth n (X ∪ Y).
  Proof.
    rewrite -{1}(difference_union_intersection_L X Y) wsat_auth_split; last set_solver.
    iIntros "[[W1 W2] W]".
    rewrite -difference_union_L wsat_auth_split; first iFrame; set_solver.
  Qed.
End predicates.

Section wsat.
  Context `{@GATIntp.t (domain Σ) α, !invG Γ Σ α, !subG Γ Σ}.

  Definition inv_satall {n} (I : gmap positive (GTerm.t n)) : iProp Σ :=
    [∗ map] i ↦ p ∈ I, ownI i p ∗ ((⟦p⟧ ∗ ownD i p) ∨ ownE {[i]}).

  (* world satisfaction restricted to certain namespace domains *)
  Definition wsat n (X : coPset) : iProp Σ :=
    ∃ (I : gmap positive (GTerm.t n)),
      let dom := gset_to_coPset (dom I) in
      ⌜dom ⊆ X⌝ ∗ inv_satall I ∗ ownI_reserve n (X ∖ dom).

  Lemma gset_to_coPset_union X Y : gset_to_coPset (X ∪ Y) = gset_to_coPset X ∪ gset_to_coPset Y.
  Proof using.
    unfold_leibniz; split.
    { intros ?%elem_of_gset_to_coPset%elem_of_union; rewrite elem_of_union; des; [left | right];
        apply elem_of_gset_to_coPset; done.
    }
    { intros [Hin|Hin]%elem_of_union; apply elem_of_gset_to_coPset in Hin;
        apply elem_of_gset_to_coPset, elem_of_union; eauto.
    }
  Qed.

  Lemma gset_to_coPset_empty : gset_to_coPset ∅ = ∅.
  Proof using. unfold_leibniz; ii; ss. Qed.

  Lemma gset_to_coPset_singleton i : gset_to_coPset {[i]} = {[i]}.
  Proof using.
    unfold_leibniz; split; rewrite elem_of_gset_to_coPset ?elem_of_singleton //.
  Qed.

  Lemma inv_satall_split {n} (X Y : gmap positive (GTerm.t n)) :
    X ##ₘ Y →
    inv_satall (X ∪ Y) ⊣⊢ inv_satall X ∗ inv_satall Y.
  Proof using.
    iIntros (?); iSplit.
    { iIntros "W"; iPoseProof (big_sepM_union with "W") as "[X Y]"; ss; iFrame. }
    { iIntros "[X Y]"; iApply (big_sepM_union with "[X Y]"); ss; iFrame. }
  Qed.

  Lemma wsat_split {n} X Y :
    X ∩ Y = ∅ →
    wsat n (X ∪ Y) ⊣⊢ wsat n X ∗ wsat n Y.
  Proof using.
    iIntros (Hdisj); rewrite /wsat; iSplit.
    { iIntros "[%I [%HI [IS IR]]]"; rewrite difference_union_distr_l_L ownI_reserve_split; cycle 1.
      { set_solver. }
      assert (Heq : I = filter (λ i, i.1 ∈ X) I ∪ filter (λ i, i.1 ∈ Y) I).
      { unfold_leibniz; intros i; rewrite lookup_union !map_lookup_filter.
        destruct (I !! i) as [p | ] eqn : HIi; rewrite HIi; ss.
        rewrite /guard; des_ifs; ss.
        apply elem_of_dom_2, elem_of_gset_to_coPset in HIi; set_solver.
      }
      rewrite {1}Heq; iPoseProof (inv_satall_split with "IS") as "[X Y]".
      { ii; rewrite /option_relation ?map_lookup_filter; destruct (I !! i) as [p | ]; ss.
        rewrite /guard; des_ifs; ss; clarify; set_solver.
      }
      iFrame "X Y".
      hexploit (filter_dom (.∈X) I); fold_leibniz; intros Heq'; rewrite -?Heq'; clear Heq'.
      hexploit (filter_dom (.∈Y) I); fold_leibniz; intros Heq'; rewrite -?Heq'.
      set (dom := (dom I)).
      replace (X ∖ gset_to_coPset dom) with (X ∖ gset_to_coPset (filter (.∈X) dom)); cycle 1.
      { unfold_leibniz; intros x; rewrite ?elem_of_difference ?elem_of_gset_to_coPset.
        rewrite elem_of_filter; split; i; des; eauto; split; ii; des; set_solver.
      }
      replace (Y ∖ gset_to_coPset dom) with (Y ∖ gset_to_coPset (filter (.∈Y) dom)); cycle 1.
      { unfold_leibniz; intros x; rewrite ?elem_of_difference ?elem_of_gset_to_coPset.
        rewrite elem_of_filter; split; i; des; eauto; split; ii; des; set_solver.
      }
      iDestruct "IR" as "[$ $]".
      iSplit; iPureIntro; set_unfold; intros ?; rewrite elem_of_gset_to_coPset elem_of_filter;
        i; des; ss.
    }
    iIntros "[[%IX [%HX [IS IR]]] [%IY [%HY [ISY IRY]]]]".
    iPoseProof (inv_satall_split IX IY with "[IS ISY]") as "IS"; ss.
    { apply map_disjoint_dom; intros ??%elem_of_gset_to_coPset?%elem_of_gset_to_coPset; set_solver. }
    { iFrame. }
    iFrame "IS".
    rewrite difference_union_distr_l_L {1}dom_union_L gset_to_coPset_union; iSplit.
    { iPureIntro; set_solver. }
    rewrite ownI_reserve_split; cycle 1.
    { rewrite ?dom_union_L ?gset_to_coPset_union; set_solver. }
    iSplitL "IR".
    { rewrite dom_union_L gset_to_coPset_union difference_union_distr_r_L.
      rewrite subseteq_intersection_1_L //.
      set_solver.
    }
    { rewrite dom_union_L gset_to_coPset_union difference_union_distr_r_L.
      rewrite comm_L subseteq_intersection_1_L //.
      set_solver.
    }
  Qed.
  Lemma wsat_merge n X Y :
    wsat n X ∗ wsat n Y -∗ wsat n (X ∪ Y).
  Proof using.
    rewrite -{1}(difference_union_intersection_L X Y) wsat_split; last set_solver.
    iIntros "[[W1 W2] W]".
    rewrite -difference_union_L wsat_split; first iFrame; set_solver.
  Qed.

  Lemma wsat_ownI_alloc_gen {n} X Y (p : GTerm.t n) :
    set_infinite Y → Y ⊆ X →
    wsat n X ⊢ |==> (∃ i, ⌜i ∈ Y⌝ ∗ ownI i p) ∗ (⟦p⟧ -∗ wsat n X).
  Proof using.
    iIntros (??) "[%I [% [IS IR]]]".
    set (dom := gset_to_coPset _).
    iPoseProof (ownI_reserve_pick _ (Y ∖ dom) p with "IR") as "> [%i [%Hin [IR D]]]"; ss.
    { apply difference_infinite; ss. apply gset_to_coPset_finite. }
    { apply difference_mono; ss. }
    iPoseProof (ownD_ownI with "D") as "[#I D]"; iFrame "I".
    iSplitR; first by set_solver.
    iModIntro; iIntros "P"; iExists (<[i:=p]>I).
    rewrite dom_insert_L gset_to_coPset_union difference_difference_l_L gset_to_coPset_singleton.
    iSplit; first by (iPureIntro; ss; set_solver).
    iSplitL "IS D P".
    { iApply (big_sepM_insert with "[IS D P]"); ss.
      { apply not_elem_of_dom; intros ?%elem_of_gset_to_coPset; set_solver. }
      { iFrame; iFrame "I"; iLeft; iFrame. }
    }
    rewrite union_comm_L //.
  Qed.

  Lemma wsat_ownI_alloc {n} X Y (p : GTerm.t n) :
    set_infinite Y → Y ⊆ X →
    wsat n X ∗ ⟦p⟧ ⊢ |==> (∃ i, ⌜i ∈ Y⌝ ∗ ownI i p) ∗ wsat n X.
  Proof using.
    iIntros (??) "[W P]"; iMod (wsat_ownI_alloc_gen X Y p with "W") as "[[%i [% I]] W]"; ss.
    iFrame. iModIntro; iSplit; first by set_solver. iApply "W"; done.
  Qed.

  Lemma wsat_ownI_open {n} i X (p : GTerm.t n) :
    i ∈ X →
    ownI i p ∗ wsat n X ∗ ownE {[i]} ⊢ ⟦p⟧ ∗ wsat n X ∗ ownD i p.
  Proof using.
    iIntros (Hin) "[I [[%I [% [IS IR]]] E]]".
    iCombine "I" "IR" gives %WF; rewrite /ownI_reserve /ownI_reserveR /ownIR in WF.
    rewrite discrete_fun_singleton_op discrete_fun_singleton_valid comm in WF.
    apply allocs_both_valid in WF as [Hnin _]; ss.
    assert (Hi : i ∈ gset_to_coPset (dom I)) by set_solver.
    apply elem_of_gset_to_coPset, elem_of_dom in Hi.
    destruct (I !! i) as [p'|] eqn : Hl; last inv Hi.
    iPoseProof (big_sepM_lookup_acc _ I i with "IS") as "[[I' [[P D] | E']] IS]"; first done.
    { iPoseProof ("IS" with "[I' E]") as "IS"; first by iFrame.
      iCombine "I D" gives %WF; rewrite /ownI_reserve /ownI_reserveR /ownIR in WF.
      rewrite discrete_fun_singleton_op discrete_fun_singleton_valid allocs_frag_op in WF.
      rewrite allocs_frag_valid -pair_op in WF; destruct WF as [_ WF%to_agree_op_inv]; inv WF.
      iFrame.
      by iPureIntro; set_solver.
    }
    { iPoseProof (ownE_exploit with "[E E']") as "%"; first iFrame; set_solver. }
  Qed.

  Lemma wsat_ownI_close {n} X i (p : GTerm.t n) :
    i ∈ X →
    wsat n X ∗ ⟦p⟧ ∗ ownD i p ⊢ wsat n X ∗ ownE {[i]}.
  Proof using.
    iIntros (Hin) "[[%I [% [IS IR]]] [P D]]".
    iCombine "D" "IR" gives %WF; rewrite /ownI_reserve /ownI_reserveR /ownIR in WF.
    rewrite discrete_fun_singleton_op discrete_fun_singleton_valid comm in WF.
    apply allocs_both_valid in WF as [Hnin _]; ss.
    assert (Hi : i ∈ gset_to_coPset (dom I)) by set_solver.
    apply elem_of_gset_to_coPset, elem_of_dom in Hi.
    destruct (I !! i) as [p'|] eqn : Hl; last inv Hi.
    iPoseProof (big_sepM_lookup_acc _ I i with "IS") as "[[I' [[_ D'] | E']] IS]"; first done.
    { iCombine "D" "D'" gives %WF.
      rewrite discrete_fun_singleton_op allocs_frag_op discrete_fun_singleton_valid in WF.
      rewrite allocs_frag_valid -pair_op in WF; destruct WF as [WF _]; inv WF.
    }
    { iCombine "I' D" gives %WF; rewrite /ownI_reserve /ownI_reserveR /ownIR in WF.
      rewrite discrete_fun_singleton_op discrete_fun_singleton_valid allocs_frag_op in WF.
      rewrite allocs_frag_valid -pair_op in WF; destruct WF as [_ WF%to_agree_op_inv]; inv WF.
      iPoseProof ("IS" with "[I' P D]") as "IS"; first (iFrame "I'"; iLeft; iFrame "P D").
      iFrame.
      by iPureIntro; set_solver.
    }
  Qed.

  Lemma wsat_init n X : ownI_reserve n X ⊢ wsat n X.
  Proof using.
    iIntros "R". iExists ∅; rewrite dom_empty_L gset_to_coPset_empty difference_empty_L.
    iFrame; iSplit; first by (iPureIntro; set_solver).
    iApply big_sepM_empty; ss.
  Qed.
End wsat.

Section wsats.
  Context `{@GATIntp.t (domain Σ) α, !invG Γ Σ α, !subG Γ Σ}.  
  Local Existing Instances invG_I invG_E.

  Lemma wsat_authR_valid n X : ✓ (wsat_authR n X).
  Proof using. rewrite /wsat_authR; intros i; des_ifs; apply allocs_auth_valid. Qed.

  Lemma wsat_authR_S n (X : coPset) : wsat_authR n X ~~> wsat_authR (S n) X ⋅ ownI_reserveR n X.
  Proof using.
    rewrite /wsat_authR; etrans.
    { erewrite (discrete_fun_delete n); refl. }
    eapply cmra_update_op.
    { eapply discrete_fun_update. intros a; des_ifs; try lia. }
    des_ifs; lia.
  Qed.

  Lemma wsat_authR_alloc n n' (X : coPset) :
    n <= n' →
    wsat_authR n X ~~> (wsat_authR n' X ⋅ ([^ (⋅) list] x ∈ (seq n (n' - n)), ownI_reserveR x X)).
  Proof using.
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

  Definition wsatl n X : iProp Σ := [∗ list] x ∈ (seq 0 n), wsat x X.

  Lemma wsatl_acc n m X : n < m → wsatl m X ⊣⊢ wsat n X ∗ (wsat n X -∗ wsatl m X).
  Proof using.
    rewrite /wsatl; intros LT; replace m with (n + S (m - S n)) by lia.
    rewrite seq_app big_sepL_app /=.
    iSplit.
    { iIntros "[$ [$ $]] $". }
    { iIntros "[H1 H2]"; iApply "H2"; iFrame. }
  Qed.
  Lemma wsatl_split n X Y :
    X ## Y →
    wsatl n (X ∪ Y) ⊣⊢ wsatl n X ∗ wsatl n Y.
  Proof using.
    intros ?; induction n; ss.
    { rewrite /wsatl; ss; iSplit; done. }
    { rewrite /wsatl -Nat.add_1_r seq_app ?big_sepL_app /=wsat_split; cycle 1.
      { set_solver. }
      iSplit; [iIntros "[? [[$ $] _]]"; iApply IHn; ss|iIntros "[[? [$ _]] [? [$ _]]]"].
      by iApply IHn; iFrame.
    }
  Qed.
  Lemma wsatl_merge n X Y :
    wsatl n X ∗ wsatl n Y -∗ wsatl n (X ∪ Y).
  Proof using.
    rewrite -{1}(difference_union_intersection_L X Y) wsatl_split; last set_solver.
    iIntros "[[W1 W2] W]".
    rewrite -difference_union_L wsatl_split; first iFrame; set_solver.
  Qed.

  Lemma wsatl_mon n n' (X : coPset) :
    n <= n' →
    wsat_auth n X ∗ wsatl n X ==∗ wsat_auth n' X ∗ wsatl n' X.
  Proof using.
    intros LE; iIntros "[AU WL]"; rewrite {1}/wsat_auth.
    iPoseProof (own_update with "AU") as "> [$ AU]"; first apply (wsat_authR_alloc); ss.
    iPoseProof (big_opL_own_1 with "AU") as "AU".
    rewrite {2}/wsatl; replace n' with (n + (n' - n)) at 2 by lia.
    rewrite seq_app big_sepL_app; iFrame; ss.
    iApply big_sepL_bupd; iApply (big_sepL_impl with "AU").
    iModIntro; iIntros (k x) "% A"; iApply wsat_init; ss.
  Qed.

  Definition wsats (n : level) (E : coPset) : iProp Σ := wsat_auth n E ∗ wsatl n E.

  Lemma wsats_mon n n' E : n <= n' → wsats n E ==∗ wsats n' E.
  Proof using. iIntros "% [W WL]". iApply wsatl_mon; eauto; iFrame. Qed.

  Lemma wsats_split n E1 E2 : E1 ## E2 → wsats n (E1 ∪ E2) ⊣⊢ wsats n E1 ∗ wsats n E2.
  Proof using.
    intros ?; rewrite /wsats assoc (comm _ _ (wsat_auth n E2)) assoc -assoc.
    rewrite -wsat_auth_split // -wsatl_split // (comm_L (∪)); done.
  Qed.
  Lemma wsats_merge n E1 E2 : wsats n E1 ∗ wsats n E2 -∗ wsats n (E1 ∪ E2).
  Proof using.
    rewrite -{1}(difference_union_intersection_L E1 E2) wsats_split; last set_solver.
    iIntros "[[W1 W2] W]".
    rewrite -difference_union_L wsats_split; first iFrame; set_solver.
  Qed.

  (* TODO : take care of cancellation lemmas *)
  (* For cancellation *)
  (* Lemma ir_ownIRA_cons u : ir_ownIRA (S u) ≡ wsat_authR (S u) 0 ⋅ ir_ownIRA u.
  Proof using.
    rewrite (discrete_fun_delete (S u) (ir_ownIRA (S u))) comm.
    f_equiv.
    { rewrite /ir_ownIRA; des_ifs; try lia. }
    { intros x; des_ifs; ss.
      { rewrite /ir_ownIRA; des_ifs; try lia. }
      { rewrite /ir_ownIRA; des_ifs; try lia. }
    }
  Qed.
  Lemma ir_ownERA_cons u : ir_ownERA (S u) ≡ ownER (S u) ⊤ ⋅ ir_ownERA u.
  Proof using.
    rewrite (discrete_fun_delete (S u) (ir_ownERA (S u))) comm.
    f_equiv.
    { rewrite /ir_ownERA; des_ifs; try lia. }
    { intros x; des_ifs; ss.
      { rewrite /ir_ownERA; des_ifs; try lia. }
      { rewrite /ir_ownERA; des_ifs; try lia. }
    }
  Qed.

  Lemma ir_ownDRA_cons u : ir_ownDRA (S u) ≡ ownD_authR (S u) ∅ ⋅ ir_ownDRA u.
  Proof using.
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
  Proof using.
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
  Qed. *)

  (* Definitions for fancy updates & invariants *)
  (* TODO :
    I think there is a way to hide the global masks in the invariant aceess rule
    by making E & E1 or E & E2 same - try them out and fix notations!
  *)
  Local Definition uPred_fupd_def b (E E1 E2 : coPset) (P : iProp Σ) : iProp Σ :=
    wsatl b E ∗ ownE E1 ==∗ (wsatl b E ∗ ownE E2 ∗ P).
  Local Definition uPred_fupd_aux : seal (@uPred_fupd_def). Proof using. by eexists. Qed.
  Definition uPred_fupd := uPred_fupd_aux.(unseal).
  Local Definition uPred_fupd_eq : @uPred_fupd = @uPred_fupd_def := uPred_fupd_aux.(seal_eq).
  Local Lemma uPred_fupd_unseal b E : @fupd _ (uPred_fupd b E) = (uPred_fupd_def b E).
  Proof using. rewrite -uPred_fupd_eq //. Qed.

  Lemma uPred_fupd_mixin n E : BiFUpdMixin (iProp Σ) (uPred_fupd n E).
  Proof using.
    split.
    - rewrite /updates.fupd uPred_fupd_eq. solve_proper.
    - intros E1 E2 (E1''&->&?)%subseteq_disjoint_union_L.
      rewrite /fupd uPred_fupd_eq /uPred_fupd_def ownE_op //.
      iIntros "[$ [$ $]] !> [$ $] //".
    - rewrite /fupd uPred_fupd_eq /uPred_fupd_def /wsats /bi_except_0.
      iIntros (E1 E2 P) "[H | H]"; iFrame.
      iDestruct (uPred.later_eq with "H") as "H"; by iFrame.
    - rewrite /fupd uPred_fupd_eq /uPred_fupd_def /wsats.
      iIntros (E1 E2 P Q HPQ) "HP HwE". rewrite -HPQ. by iApply "HP".
    - rewrite /fupd uPred_fupd_eq /uPred_fupd_def /wsats. iIntros (E1 E2 E3 P) "HP HwE".
      iMod ("HP" with "HwE") as "[? [? HP]]". iApply "HP"; by iFrame.
    - intros E1 E2 Ef P HE1Ef.
      rewrite /fupd uPred_fupd_eq /uPred_fupd_def ownE_op //.
      iIntros "Hupd [W [E Ef]]".
      (* iPoseProof (wsatl_split with "W") as "[W1 Wf]"; ss. *)
      iMod ("Hupd" with "[W E]") as "[W [E2 P]]"; iFrame.
      iPoseProof (ownE_exploit with "[Ef E2]") as "%DISJ"; first iFrame.
      rewrite ownE_op //; iFrame; by iApply "P".
    - rewrite /fupd uPred_fupd_eq /uPred_fupd_def /wsats. by iIntros (????) "[HwP $]".
  Qed.
  Global Instance uPred_bi_fupd n E : BiFUpd (iProp Σ) :=
    {| bi_fupd_mixin := (uPred_fupd_mixin n E) |}.
  Global Instance uPred_bi_bupd_fupd n E :
    @BiBUpdFUpd (iProp Σ) (uPred_bi_bupd Σ) (uPred_bi_fupd n E).
  Proof using. rewrite /BiBUpdFUpd uPred_fupd_unseal. by iIntros (??) ">? [$ $] !>". Qed.

  (* definition of an invariant *)
  Local Definition inv_def {n : level} (N : namespace) (p : GTerm.t n) : iProp Σ :=
    ∃ i, ⌜i ∈ (↑N : coPset)⌝ ∧ ownI i p.
  Local Definition inv_aux : seal (@inv_def). Proof using. by eexists. Qed.
  Definition inv := inv_aux.(unseal).
  Local Definition inv_eq : @inv = @inv_def := inv_aux.(seal_eq).

  Global Instance inv_persistent n N p : Persistent (inv n N p).
  Proof using. rewrite inv_eq /inv_def. apply _. Qed.

  (** Turns a pure proposition into a resource **)
  (* Definition pure_res (P : Prop) : Σ :=
    if excluded_middle_informative P
    then ε
    else own.iRes_singleton base_γ (ownER 0 ⊤ ⋅ ownER 0 ⊤).

  Lemma pure_res_spec (P : Prop) :
    Own (pure_res P) ⊣⊢ ⌜P⌝.
  Proof using.
    econs. i. rewrite /pure_res. des_ifs.
    { split; i; eapply Own_general_completeness in H1; eapply Own_general_soundness; et.
      iIntros "_". iApply Own_unit.
    }

    split; i; eapply Own_general_completeness in H1; exfalso; cycle 1.
    { eapply n, Own_pure_soundness; et. }
  
    eapply Own_wand_valid in H0; cycle 1.
    { iIntros "X". iApply H1. et. }
    assert (F := own.iRes_singleton_validI base_γ (ownER 0 ⊤ ⋅ ownER 0 ⊤)).
    assert (Own ε ⊢ ✓ (ownER 0 ⊤ ⋅ ownER 0 ⊤ ))%I.
    { iIntros "_". iApply F. et. }
    exploit (uPred_primitive.ownM_general_soundness ε (✓ (ownER 0 ⊤ ⋅ ownER 0 ⊤))); eauto using ucmra_unit_valid.
    { rr in H2. rewrite own.Own_eq /own.Own_def in H2. et. }
    intro V. rr in V. revert V. rewrite seal_eq. ss.
    rewrite /ownER discrete_fun_singleton_op discrete_fun_singleton_valid.
    intros V. eapply coPset_disj_valid_inv_l in V. des. depdes V.
    rewrite elem_of_disjoint in V0. eapply (V0 1%positive); ss.
  Qed.

  Lemma precise_pure (P: Prop) :
    ⊢ precise (⌜P⌝).
  Proof using.
    rewrite /precise. iIntros. iExists (pure_res P).
    rewrite pure_res_spec. et.
  Qed. *)
End wsats.

Notation fupd_ex n E :=
  (@fupd (bi_car (iProp _)) (@bi_fupd_fupd _ (uPred_bi_fupd n E))) (only parsing).

Notation "'=|' n ',' E '|={' E1 ',' E2 '}=>' P" := (fupd_ex n E E1 E2 P) (at level 90) : stdpp_scope.
Notation "P '=|' n ',' E '|={' E1 ',' E2 '}=∗' Q" := (P -∗ =|n, E|={E1,E2}=> Q) (at level 90) : stdpp_scope.

Notation "'=|' n ',' E '|={' E1 '}=>' P" := (=|n, E|={E1, E1}=> P) (at level 90) : stdpp_scope.
Notation "P '=|' n ',' E '|={' E1 '}=∗' Q" := (P -∗ =|n, E|={E1}=> Q) (at level 90) : stdpp_scope.

Notation "'=|' n ',' E '|={' E1 ',' E2 '}=>' P" := (fupd_ex n E E1 E2 P)%I (at level 90) : bi_scope.
Notation "P '=|' n ',' E '|={' E1 ',' E2 '}=∗' Q" := (P -∗ =|n, E|={E1,E2}=> Q)%I (at level 90) : bi_scope.

Notation "'=|' n ',' E '|={' E1 '}=>' P" := (=|n, E|={E1, E1}=> P)%I (at level 90) : bi_scope.
Notation "P '=|' n ',' E '|={' E1 '}=∗' Q" := (P -∗ =|n, E|={E1}=> Q)%I (at level 90) : bi_scope.

Section fancy_updates.
  Context `{@GATIntp.t (domain Σ) α, !invG Γ Σ α, !subG Γ Σ}.  
  Implicit Types n m : level.
  Implicit Types N : namespace.
  Implicit Types E : coPset.

  Lemma fupd_mon n m E E1 E2 P : n <= m → =|n, E|={E1, E2}=> P -∗ =|m, E|={E1, E2}=> P.
  Proof using.
    intros LT; rewrite ?uPred_fupd_unseal /uPred_fupd_def /wsats.
    iIntros "P [W E]".
    rewrite {3}/wsatl; replace m with (n + (m - n)) at 1 by lia; rewrite seq_app big_sepL_app.
    iDestruct "W" as "[WN W]"; iMod ("P" with "[WN E]") as "[P [$ $]]"; iFrame.
    rewrite /wsatl; replace m with (n + (m - n)) at 2 by lia; rewrite seq_app big_sepL_app /=.
    by iFrame.
  Qed.

  Lemma fupd_mon_namespace n Ew Ew' E1 E2 P :
    Ew' ⊆ Ew →
    =|n, Ew'|={E1, E2}=> P -∗ =|n, Ew|={E1, E2}=> P.
  Proof using.
    iIntros (?) "P"; rewrite ?uPred_fupd_unseal /uPred_fupd_def; iIntros "[W E]".
    rewrite {1}(union_difference_L Ew' Ew) // wsatl_split; last set_solver.
    iDestruct "W" as "[W' W]"; iPoseProof ("P" with "[W' E]") as "> [W' [E P]]"; iFrame.
    iPoseProof (wsatl_merge with "[W W']") as "W"; iFrame; rewrite -(union_difference_L Ew' Ew) //.
  Qed.
End fancy_updates.

Section inv.
  Context `{@GATIntp.t (domain Σ) α, !invG Γ Σ α, !subG Γ Σ}.  
  Implicit Types (n : level) (N : namespace) (E : coPset).

  (* Lemma fresh_inv_name N : pred_infinite (.∈ (↑N:coPset)).
  Proof using. apply coPset_infinite_finite, nclose_infinite. Qed. *)

  Lemma inv_alloc {n} (p : GTerm.t n) m E Ew N :
    n < m → ↑N ⊆ Ew → ⟦p⟧ =|m, Ew|={E}=∗ inv n N p.
  Proof using.
    rewrite ?uPred_fupd_unseal /uPred_fupd_def ?inv_eq /inv_def.
    iIntros (LT Hsub) "P [W E]".
    iPoseProof (wsatl_acc n with "W") as "[W A]"; first done.
    iMod (wsat_ownI_alloc Ew (↑N) p with "[W P]") as "[[%i [%Hi #HiP]] W]"; ss.
    { apply coPset_infinite_finite, nclose_infinite. }
    { iFrame. }
    rewrite {2}(wsatl_acc n); ss; iFrame.
    iModIntro; iExists _; iSplit; eauto.
  Qed.

  Lemma inv_acc {n} m N (p : GTerm.t n) (Ew E : coPset) :
    n < m → ↑N ⊆ E → E ⊆ Ew →
    inv n N p =|m, Ew|={E, E∖↑N}=∗ (⟦p⟧ ∗ (⟦p⟧ =|m, Ew|={E∖↑N, E}=∗ True)).
  Proof using.
    rewrite ?uPred_fupd_unseal /uPred_fupd_def ?inv_eq /inv_def.
    iDestruct 1 as (i) "[Hi #HiP]".
    iDestruct "Hi" as % ?%elem_of_subseteq_singleton.
    rewrite {1}(wsatl_acc n) //; iIntros "[[W ACC] E]".
    rewrite {1}(union_difference_L (↑ N) E) // ownE_op; last set_solver.
    rewrite {1}(union_difference_L {[ i ]} (↑ N)) // ownE_op; last set_solver.
    iDestruct "E" as "[[E1 E3] E2]".
    iPoseProof (wsat_ownI_open with "[HiP W E1]") as "[P [W D2]]"; try by iFrame.
    { set_solver. }
    iPoseProof ("ACC" with "W") as "W"; iFrame.
    rewrite {1}(wsatl_acc n) //; iIntros "!> P [[W R] E]".
    iPoseProof (wsat_ownI_close with "[W P D2]") as "[W E']"; try by iFrame. { set_solver. }
    rewrite {2}(union_difference_L (↑ N) E) // ownE_op; last set_solver.
    rewrite {3}(union_difference_L {[ i ]} (↑ N)) // ownE_op; last set_solver; iFrame.
    iModIntro; iApply "R"; iFrame.
  Qed.

  Global Instance from_modal_fupd n Ew E1 E2 P :
    FromModal (E2 ⊆ E1) modality_id (=|n, Ew|={E1,E2}=> P) (=|n, Ew|={E1,E2}=> P) P | 1.
  Proof using.
    rewrite /FromModal ?uPred_fupd_unseal /uPred_fupd_def ?inv_eq /inv_def /=.
    iIntros (IN) "$ W !>".
    rewrite (union_difference_L E2 E1) // /wsats ownE_op; last set_solver.
    iDestruct "W" as "[$ [$ _]]".
  Qed.

  Global Instance into_acc_inv n m Ew E N p :
    IntoAcc (inv n N p) (n < m ∧ ↑N ⊆ E ∧ E ⊆ Ew) True
            (fupd_ex m Ew E (E ∖ ↑N))
            (fupd_ex m Ew (E ∖ ↑N) E)
            (λ _ : (), ⟦p⟧) (λ _ : (), ⟦p⟧) (λ _ : (), None).
  Proof using.
    rewrite /IntoAcc /accessor bi.exist_unit.
    iIntros ((? & ?)) "#INV _". by iApply inv_acc; set_solver.
  Qed.

  Global Instance elim_modal_fupd_fupd_gen p n m Ew Ew' E0 E1 E2 E3 P Q :
    ElimModal (n <= m ∧ E0 ⊆ E2 ∧ Ew' ⊆ Ew) p false
              (=|n, Ew'|={E0,E1}=> P) P
              (=|m, Ew|={E2,E3}=> Q) (=|m, Ew|={E1 ∪ E2 ∖ E0, E3}=> Q) | 10.
  Proof using.
    rewrite /ElimModal bi.intuitionistically_if_elim.
    iIntros ([LE [SUB SUB2]]) "[P K]".
    iPoseProof (fupd_mon n m with "P") as "P"; ss.
    iPoseProof (fupd_mon_namespace _ Ew with "P") as "P"; ss.
    rewrite ?uPred_fupd_unseal /uPred_fupd_def ?inv_eq /inv_def /=.
    iIntros "[WL E]".
    rewrite {2}(union_difference_L E0 E2) // (ownE_op (E0)); last set_solver.
    iDestruct "E" as "[E1 E2]".
    iPoseProof ("P" with "[WL E1]") as "> [W [E P]]"; first iFrame.
    iApply ("K" with "P [W E E2]"); iFrame.
    iPoseProof (ownE_exploit with "[E E2]") as "%D"; iFrame.
    rewrite ownE_op; ss; iFrame.
  Qed.

  Global Instance elim_modal_fupd_fupd_simple p n m Ew E1 E2 E3 P Q :
    ElimModal (n <= m) p false
              (=|n, Ew|={E1,E2}=> P) P (=|m, Ew|={E1,E3}=> Q) (=|m, Ew|={E2,E3}=> Q).
  Proof using.
    rewrite /ElimModal bi.intuitionistically_if_elim.
    iIntros (LE) "[P K]".
    iPoseProof (fupd_mon n m with "P") as "P"; ss.
    iMod "P". iMod ("K" with "P") as "K"; iModIntro; ss.
  Qed.
End inv.

(* tactics for cancellation *)
Ltac unfold_own :=
  match goal with
  | |- Own ?R = own base_γ ?R2 =>
    rewrite own.Own_eq /own.Own_def own.own_eq /own.own_def /own.iRes_singleton; f_equal
  end.

Ltac unfold_left :=
  repeat match goal with
  | |- context [InitRes.singleton _] => rewrite InitRes.singleton_index
  | |- context [InitRes.L (discrete_fun_singleton _ _)] => rewrite ?InitRes.L_index
  | |- context [InitRes.R (discrete_fun_singleton _ _)] => rewrite ?InitRes.R_index
  end.

Ltac solve_index H := 
  eapply eq_ind; first iExact H;
  unfold_own;
  etrans;
  [unfold_left; repeat match goal with | |- ?a = _ => remove_eq a end; simpl; refl
  | etrans; cycle 1;
    [ symmetry;
      let k := fresh "k" in
      match goal with
      | |- context [inG_id ?i] => pattern i; match goal with | |- ?f ?a => set (k:=f) end
      end;
      autounfold with GRA_index
      ; subst k
      ; simpl
      ; hrepeat do 1 match goal with | |- ?a = _ => remove_eq a end
      ; simpl
    | refl
    ]
  ].

Ltac _solve_ir_valid :=
  lazymatch goal with
  | |- ✓ ( (InitRes.app _ _) ⋅ initial_resource_own_admin ) => eapply InitRes.app_valid
  | |- ✓ ( InitRes.nil ⋅ initial_resource_own_admin ) => let i := fresh "i" in intros i; inv_fin i
  | |- ✓ ( InitRes.singleton None ⋅ initial_resource_own_admin ) => eapply InitRes.singleton_none_valid
  | |- ✓ ( InitRes.singleton _ ⋅ initial_resource_own_admin ) => eapply InitRes.singleton_some_valid
  | |- ✓ ( ?r ⋅ initial_resource_own_admin ) => rewrite /r; eapply InitRes.app_valid
  end.

Ltac solve_ir_valid :=
  (hrepeat do 1 _solve_ir_valid);
  try match goal with |- ✓ ir_ownIRA _ => apply ir_ownIRA_valid end;
  try match goal with |- ✓ ir_ownERA _ => apply ir_ownERA_valid end;
  try match goal with |- ✓ ir_ownDRA _ => apply ir_ownDRA_valid end.

Ltac _unfold_res :=
  match goal with
    |- context[Own(?r ⋅ initial_resource_own_admin)] =>
      rewrite /r /InitRes.app;
      repeat (rewrite ?InitRes.L_distr ?InitRes.R_distr)
  end.

Ltac _destruct_res :=
  let CNT := fresh "CNT" in
  let Pat := fresh "Pat" in
  pose (CNT := 0);
  (hrepeat do 1
    pose (Pat := ("[H" ++ NilEmpty.string_of_uint (Nat.to_uint CNT) ++ " H" ++ NilEmpty.string_of_uint (Nat.to_uint (S CNT)) ++ "]")%string);
    compute in Pat;
    lazymatch goal with
    |- context[environments.Esnoc _ (INamed ?H) (Own (_ ⋅ _))] =>
        match goal with [_ := ?pat |-_] => iDestruct H as pat end
    end;
    clear Pat;
    match goal with [CNT := ?n |-_] => clear CNT; pose (CNT := S(S n)) end);
  clear CNT.

Ltac _clear_res :=
  hrepeat do 1 match goal with
  |- context[environments.Esnoc _ (INamed ?H) (Own ?r)] =>
     pose (RRR := r);
     lazymatch goal with
     | [_ := context[InitRes.nil] |-_] => iClear H
     | [_ := context[InitRes.singleton None] |- _] => iClear H
     end;
     clear RRR
   end.

Ltac _simplify_res :=
  try match goal with
      |- context[environments.Esnoc _ (INamed ?H) (Own ?r)] =>
      let R := fresh "R" in
      let pat := fresh "pat" in
      pose (R:=r);
      lazymatch goal with
        [_ := context[ InitRes.singleton (Some ?r) ] |-_] =>
          pose (pat := ("[" ++ H ++ "]")%string); compute in pat;
          iAssert (own base_γ r) with pat as H;
          clear R pat;
          cycle 1; [_simplify_res|]
      end
  end.

Ltac _wsats_res :=
  lazymatch goal with
  |- context[environments.Esnoc _ (INamed ?I) (own base_γ (ir_ownIRA _))] =>
  lazymatch goal with 
  |- context[environments.Esnoc _ (INamed ?E) (own base_γ (ir_ownERA _))] =>
  lazymatch goal with 
  |- context[environments.Esnoc _ (INamed ?D) (own base_γ (ir_ownDRA _))] =>
    let Pat := fresh "Pat" in      
    pose (Pat := ("[" ++ I ++ " " ++ E ++ " " ++ D ++ "]")%string);
    compute in Pat;
    (* iPoseProof (make_wsats _ with Pat) as "[U W]"; [by iFrame|]; *)
    clear Pat
  end end end.

Ltac simplify_res :=
  _unfold_res;
  iIntros "H";
  _destruct_res;
  _clear_res;
  _simplify_res;
  [try _wsats_res|..].

Ltac solve_res :=
  match goal with
    |- context[environments.Esnoc _ (INamed ?H) _] =>
      solve_index H; f_equal
  end.
 
