Require Import CRIS.
Require Import MemHeader MemA MemTactics.
Require Import SchHeader SchI SchA SchTactics.
Require Import StackHeader StackA.
Require Import PQueueHeader PQueueI.
From iris.algebra Require Import excl_auth.

Class queueG `{!crisG Γ Σ α β τ _S _I} := QueueG {
  queue_stateG :: inG (excl_authR (listO (leibnizO (val * gname)))) Γ;
}.
Definition queueΓ : HRA := #[excl_authR (listO (leibnizO (val * gname)))].
Global Instance subG_queueG `{!crisG Γ Σ α β τ _S _I} :
  subG queueΓ Γ → queueG.
Proof. solve_inG. Defined.
Hint Unfold subG_queueG queue_stateG : GRA_index.

Section definitions.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !newschG, !memG}.
  Context `{!stackG StackM.jobID StackM.retID, !queueG}.
  Context (N : namespace).

  Definition queueN : namespace := N.@"queue".

  Definition syn_queue_inv
      (n : nat) (γq : gname) (range : nat) (qb : mblock) (qofs : ptrofs)
      (entries : list (leibnizO (val * gname)))
      : GTerm.t n := (
    <own> γq (excl_auth_frag entries) ∗
    [∗ n list] i ↦ x ∈ entries, (qb, qofs + i)%Z ↦ x.1
  )%SAT.
  Definition queue_inv
      (n : nat) (γq : gname) (range : nat) (qb : mblock) (qofs : ptrofs) 
      (entries : list (leibnizO (val * gname)))
      : iProp Σ := (
    own γq (◯E entries) ∗
    [∗ list] i ↦ x ∈ entries, (qb, qofs + Z.of_nat i)%Z ↦ x.1
  )%I.
  Global Instance queue_inv_SLRed n γq range qb qofs entries :
    SLRed (syn_queue_inv n γq range qb qofs entries) (queue_inv n γq range qb qofs entries).
  Proof. rewrite /syn_queue_inv /queue_inv; econs; rewrite SLRed_eq //. Qed.

  Definition syn_is_queue (n : nat) (γq : gname) (range : nat) (q : val) : GTerm.t n := (
    ∃ (qb : τ{mblock}) (qofs : τ{ptrofs}), ⌜q = Vptr (qb, qofs)⌝ ∗
      ∃ (entries : τ{list (val * gname)}),
        syn_inv n queueN (syn_queue_inv n γq range qb qofs entries) ∗
        [∗ n list] i ↦ e ∈ entries, syn_is_stack (stackN N) e.2 e.1 n
  )%SAT.
  Definition is_queue (n : nat) (γq : gname) (range : nat) (q : val) : iProp Σ :=
    ∃ (qb : mblock) (qofs : ptrofs), ⌜q = Vptr (qb, qofs)⌝ ∗
      ∃ (entries : list (val * gname)),
        inv n queueN (syn_queue_inv n γq range qb qofs entries) ∗
        [∗ list] i ↦ e ∈ entries, is_stack (stackN N) e.2 e.1 n.
  Global Instance is_queue_SLRed n γq q range :
    SLRed (syn_is_queue n γq q range) (is_queue n γq q range).
  Proof.
    rewrite /syn_is_queue /is_queue; econs; rewrite SLRed_eq //. do 4 (f_equiv; ii); ss.
    rewrite inv_red //.
  Qed.
  Global Instance is_queue_persistent n γq q range :
    Persistent (is_queue n γq q range).
  Proof. apply _. Qed.

  Definition queue_contents (γq : gname) (range : nat) (map : list (list val)) : iProp Σ :=
    ∃ (entries : list (leibnizO (val * gname))), own γq (●E entries) ∗
      [∗ list] i ↦ e ∈ entries, stack_content e.2 (map !!! i).
End definitions.

Module PQueueA. Section PQueueA.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !newschG, !memG}.
  Context `{!stackG StackM.jobID StackM.retID, !queueG}.
  Context (N : namespace).

  Definition scopes : list string := [].

  Definition new_spec : fspec :=
    fspec_sch (↑N)
      (fspec_simple (X := nat * nat) (λ '(n, range),
        ((λ arg, ⌜arg = [Vint range]↑ ∧ 8 * range < modulus_64⌝)%Z,
         (λ ret, ∃ q γq, ⌜ret = q↑⌝ ∗
          is_queue N n γq range q ∗ queue_contents γq range (repeat [] range)))%I)).

  Definition new : Any.t → itree crisE Any.t := λ _,
    𝒴;;; fbody_trivial ()↑.

  Definition fnsems : fnsems_type :=
    [(Some PQueueHdr.new, (true, wmask_all, scopes, (Some new_spec, new)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t sp := Seal.sealing CRIS (SMod.to_mod sp Mod).
End PQueueA. End PQueueA.

Module PQueueIA. Section PQueueIA.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !newschG, !memG}.
  Context `{!stackG StackM.jobID StackM.retID, !queueG}.

  Context (N : namespace) (sp : sp_type).
  Context (Hsch : sp_incl (SchA.sp [] (↑N)) sp).

  Definition init_cond : iProp Σ := emp%I.

  Local Definition PQueueI := PQueueI.t      ★ StackA.t N sp ★ SchI.t ★ MemA.t.
  Local Definition PQueueA := PQueueA.t N sp ★ StackA.t N sp ★ SchI.t ★ MemA.t.
  Local Definition IstFull := IstProd (IstSB (Mod.scopes (PQueueA.t N sp)) IstTrue) IstEq.

  Lemma new_simF : ISim.sim_fun open PQueueA PQueueI init_cond IstFull (Some PQueueHdr.new).
  Proof.
    init_simF.
    steps_l. iDestruct "ASM" as "[TID [[-> %Hn] ->]]".
    rename _q3 into stid, _q4 into mtid, _q5 into n, _q6 into range.

    steps_r. hss_r. steps_r. sch_yield_ir. steps_r. sch_yield_ir. steps_r.
    iApply wsim_mem_alloc; [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
    { lia. }
    iIntros (queueb) "↦queue". steps_r. hss_r. steps_r. sch_yield_ir. steps_r.

    iApply wsim_yy_y. iApply wsim_bind.
    instantiate (1:=(λ '(st_src, _) '(st_tgt, _),
      IstFull st_src st_tgt ∗ Tid stid mtid ∗ winv (↑N, ↑N) ∗
      ∃ γq, is_queue N n γq range (Vptr (queueb, 0%Z)) ∗
      queue_contents γq range (repeat [] range))%I).
    iSplitL "↦queue IST TID".
    { rewrite ?Nat2Z.id. erewrite <-(bind_ret_r (SB.sandbox _ _ _ _)).
      iAssert ([∗ list] i ↦ v ∈ repeat Vundef range,
        if (decide (0%Z ≤ i)%Z)
        then (queueb, Z.of_nat i) ↦ v
        else ∃ γs stack, is_stack N γs stack n ∗ (queueb, Z.of_nat i) ↦ stack)%I
        with "[↦queue]" as "↦queue".
      { iApply (big_sepL_impl with "↦queue").
        iIntros "!> % % %"; case_decide; try iIntros "$"; lia.
      }
      set (var := range).
      rewrite {1 2 3 4}/var.
      replace (0%Z) with (range - var)%Z by lia.
      rewrite {5}Z.sub_diag.
       (* rewrite {1 3 5 6 7 8 9 10 11 12 13 14 15 17}/var. *)
      iAssert (⌜var ≤ range⌝)%I as "#Hvar"; first (iPureIntro; lia).
      generalize var. clear var. iIntros (var).
      iInduction (var) as [|var] forall (st_src st_tgt).
      { unfold_iter_r. steps_r.
        erewrite <-(bind_ret_r (SB.sandbox _ _ _ _)).
        sch_yield_l. ss.
        iMod (own_alloc (●E [] ⋅ ◯E [])) as "[%γq [●q ◯q]]"; first eauto using excl_auth_valid.
        iMod (inv_alloc (syn_queue_inv n γq range queueb 0 []) _ _ _ (queueN N) with "[◯q]")
          as "#Qinv"; eauto.
        { apply nclose_subseteq. }
        { rewrite SLRed_eq /queue_inv; iFrame; ss. }
        iApply wsim_unfold; iIntros "W". step. iFrame "IST TID W". iExists γq. iSplitR "●q".
        { iExists _, _; iSplit; first done; iExists []; ss; iSplit; iFrame; eauto. }
        iExists _; iFrame; ss.
      }

      iPoseProof "Hvar" as "%".
      unfold_iter_r. steps_r.
      (* stack allocation *)
      inline_r. force_r (stid, mtid, n). forces_r. iFrame. iSplit; eauto.
      steps_r. hss_r. steps_r. steps_l. steps_r. sch_yield_ii.
      steps_r. iDestruct "GRT" as "[TID [[%stack [%γs [-> [#is_stack stack]]]] %]]".
      hss_r. steps_r.
      iPoseProof (big_sepL_lookup_acc_impl (range - S var) Vundef with "↦queue")
        as "[↦queue ↦close]".
      { hexploit (lookup_lt_is_Some_2 (repeat Vundef range) (range - S var)).
        { rewrite repeat_length. lia. }
        destruct (repeat Vundef range !! _) eqn : Hlkn; ss; last (intros INV; inv INV).
        apply elem_of_list_lookup_2, elem_of_list_In, repeat_spec in Hlkn; clarify.
      }
      case_decide; last lia.

      iApply (wsim_mem_store with "[↦queue]");
        [try prove_inline_cond|try prove_sb_cond|..|unfold_cris_defs].
      { rewrite Nat2Z.inj_sub //. }
      iIntros "↦queue". steps_r. hss_r. steps_r.
      replace (range - S var + 1)%Z with (range - var)%Z by lia.
      iApply ("IHvar" with "[] IST TID [-]").
      { iIntros "!>"; iPureIntro; lia. }
      iApply ("↦close" with "[] [↦queue]").
      { iModIntro; iIntros (??) "%% H"; do 2 case_decide; try lia; iFrame. }
      { case_decide; try lia.
        iExists _, _; iFrame "is_stack". rewrite Nat2Z.inj_sub //; iFrame.
      }
    }

    (* continuation *)
    clear_st. iIntros (st_s _ st_t _) "[IST [TID [W [%γq [#qinv queue]]]]]".
    iApply wsim_fold; iFrame "W".
    steps_r. sch_yield_ir. steps_r.
    sch_yield_l. forces_l. iFrame. iSplit; eauto. step. iSplit; done.
  Unshelve. all: eauto.
  (*SLOW*)Qed.
End PQueueIA. End PQueueIA.

