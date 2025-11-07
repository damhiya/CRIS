Require Import CRIS.
Require Import SchHeader SchA.
Require Import RRSHeader RRSA.
Require Import MemHeader MemA.
Require Import RRSNodeHeader RRSNodeI.
Require Import CallFilter.

Set Implicit Arguments.

Section RRSNodeRA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Definition nodeRA := prodR fracR (agreeR valO).

  Class nodeG `{!crisG Γ Σ α β τ _S _I} := {
      node_inG_node :: inG nodeRA Γ;
  }.
  Definition nodeΓ : HRA := #[nodeRA].
  Global Instance subG_nodeG : subG nodeΓ Γ -> nodeG.
  Proof using. solve_inG. Defined.
End RRSNodeRA.
Hint Unfold node_inG_node subG_nodeG : GRA_index.

Local Open Scope Qp.

Module RRSNodeAS. Section RRSNodeAS.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG}.
  Context `{_schG: !SchA.newschG}.
  Context `{_rrsG: !RRSA.rrsG}.
  Context `{_memG: !MemA.memG}.
  Context `{_nodeG: !RRSNodeA.nodeG}.

  (** Define user resources and iProp **)
  Definition full_val_r v: nodeRA := (1, to_agree v).
  Definition half_val_r v: nodeRA := (1/2, to_agree v).

  Definition full_val v : iProp Σ :=
    Seal.sealing "Node" (own base_γ (full_val_r v)).
  Definition half_val v : iProp Σ :=
    Seal.sealing "Node" (own base_γ (half_val_r v)).

  Definition ir_nodeRA : DRA_mk nodeRA := (full_val_r (Vint 0)).
  Definition ir_nodeRA_valid : ✓ ir_nodeRA.
  Proof using.
    rewrite /ir_nodeRA.
    rewrite /full_val_r. econs; ss.
  Qed.

  Definition ir_nodeΓ : nodeΓ := *[Some ir_nodeRA].

  Definition init_node : iProp Σ := Seal.sealing "Node" (full_val (Vint 0)).
  
  Section RA.
    (** Prove lemmas for user resources **)
    Lemma full_merge z :
      half_val z ∗ half_val z ⊣⊢ full_val z.
    Proof.
      rewrite /half_val /full_val. unseal "Node".
      rewrite /half_val_r /full_val_r. iSplit;
      iIntros "H"; rewrite -own_op;
      rewrite -pair_op frac_op agree_idemp;
      replace (1/2 + 1/2) with 1 by compute_done; ss.
    Qed.

    Lemma full_update z0 z1 :
      full_val z0 ⊢ |==> full_val z1.
    Proof.
      rewrite /full_val /full_val_r. unseal "Node".
      iIntros "F". iPoseProof (own_update with "F") as ">F".
      { instantiate (1 := (1, to_agree z1)). eapply cmra_discrete_update.
        i. destruct mz; ss. destruct c. rewrite -pair_op pair_valid in H.
        des. eapply exclusive_l in H; ss. eapply frac_full_exclusive. }
      iFrame; eauto.
    Qed.

    Lemma half_match z0 z1 :
      half_val z0 ∗ half_val z1 ⊢ ⌜z0 = z1⌝.
    Proof.
      rewrite /half_val /half_val_r. unseal "Node".
      iIntros "[H0 H1]". iCombine "H0 H1" gives %wf.
      rewrite -pair_op pair_valid in wf; des.
      eapply to_agree_op_inv in wf0. rewrite wf0; eauto.
    Qed.
    
  End RA.

  Section FSPEC_RRSCH.
    Import RRSAS.

    Definition per_tid_fspec (fspecf: nat -> fspec) : fspec :=
      fspec_call (meta := { i : nat & meta (fspecf i) })
        (λ '(existT i meta_i), precond (fspecf i) meta_i)
        (λ '(existT i meta_i), postcond (fspecf i) meta_i).

    Definition per_tid_fspec_rrsch E {meta: Type}
      (precond postcond: nat * nat * nat * meta → Any.t → Any.t → iProp Σ) (Invf: nat -> InvO) (mtid : nat) : fspec :=
      fspec_winv E
        (fspec_call (meta := nat * nat * nat * meta * (gmap nat InvO))
           (λ '(mtid', stid, ssch, x, Invs) varg arg,
             ∃ Invs',
               ⌜mtid = mtid' ∧ Invs' !! (pred_rr mtid (size Invs')) = Some (Invf (pred_rr mtid (size Invs'))) ∧
                Invs' !! mtid = Some (Invf mtid)⌝ ∗
               Tid mtid stid ssch ∗
               RRSAS.rrinv_prev Invs ∗
               RRSAS.rrinv Invs' ∗
               (⌜mtid = 0⌝ ∨ ⟦ projT2 (Invf (pred_rr mtid (size Invs'))) ⟧) ∗
               precond (mtid, stid, ssch, x) varg arg)%I
           (λ '(mtid', stid, ssch, x, Invs) vret ret,
               ⌜mtid = mtid'⌝ ∗
               Tid mtid stid ssch ∗
               postcond (mtid', stid, ssch, x) vret ret)%I).

    Definition fspec_rrsch E {meta: Type} (Invf: nat -> InvO) (precond postcond: nat * nat * nat * meta → Any.t → Any.t → iProp Σ) : fspec :=
      per_tid_fspec (per_tid_fspec_rrsch E precond postcond Invf).

  End FSPEC_RRSCH.

  Section SPEC.
    Context (E: coPset).

    Definition N_node : namespace := (nroot .@ "Node.x").

    Definition x_points_to (loc: mblock * Z) (v: val) : GTerm.t 0 :=
      (<own> base_γ ((mem_points_to_singleton_r loc (DfracOwn 1) v): memRA))
        ∗ (<own> base_γ ((half_val_r v): nodeRA)).

    Definition ex_x_points_to loc : GTerm.t 0 :=
      (∃ (v: τ{ ⇣val }), x_points_to loc v)%SAT.

    Definition x_value_tid (tid: nat) : GTerm.t 0 :=
      (<own> base_γ ((half_val_r (Vint tid)): nodeRA)).
        
    Definition inv_x_points_to (loc: mblock * Z) : iProp Σ :=
      inv 0 N_node (ex_x_points_to loc).

    Definition f_precond loc (varg arg: SAny.t) : iProp Σ :=
      (⌜varg = tt↑↑ /\ arg = (Vptr loc)↑↑⌝ ∗ (inv_x_points_to loc))%I.

    Definition f_postcond (vret ret: SAny.t) : iProp Σ := True.

    Definition f_main_spec : fspec :=
      fspec_winv E
        (fspec_simple (λ '(stid, ssch),
          (λ varg, ⌜varg = (tt↑↑)↑⌝ ∗ RRSAS.Tid 0 stid ssch ∗ RRSAS.rrinv {[0:=existT 0 (x_value_tid 0)]} ∗ full_val (Vint 0),
           λ vret, ⌜vret = (tt↑↑)↑⌝ ∗ RRSAS.Tid 0 stid ssch)%I)).
    
    Definition f_spec : fspec :=
      fspec_rrsch E
        (λ my_tid, existT 0 (x_value_tid my_tid))
        (λ '(mtid, stid, ssch, loc) varg arg, ∃ svarg sarg, ⌜varg = svarg↑ ∧ arg = sarg↑ ∧ mtid ≠ 0⌝ ∗ f_precond loc svarg sarg)%I
        (λ '(mtid, stid, ssch, loc) vret ret, ∃ svret sret, ⌜vret = svret↑ ∧ ret = sret↑⌝ ∗ f_postcond svret sret)%I.

    Definition sp : spl_type :=
      Seal.sealing CRIS
        [(Some RRSNodeHdr.f_main, Some f_main_spec);
         (Some RRSNodeHdr.f,      Some f_spec)].
  End SPEC.
End RRSNodeAS. End RRSNodeAS.

Module RRSNodeA. Section RRSNodeA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG}.
  Context `{_schG: !SchA.newschG}.
  Context `{_rrsG: !RRSA.rrsG}.
  Context `{_memG: !MemA.memG}.
  Context `{_nodeG: !RRSNodeA.nodeG}.

  Definition scopes := [RRSNODE].

  Definition f_main : SAny.t -> itree crisE SAny.t :=
    fun _ =>
      ℛ𝒴;;; ℛ𝒴;;;
      'tid1: nat <- ccallU RRSHdr.spawn (RRSNodeHdr.f, tt↑↑);; ℛ𝒴;;;
      'tid2: nat <- ccallU RRSHdr.spawn (RRSNodeHdr.f, tt↑↑);; ℛ𝒴;;; ℛℛ;;;
      Ret (tt↑↑)
  .

  Definition f : SAny.t -> itree crisE SAny.t :=
    fun _ =>
      ℛ𝒴;;; ℛ𝒴;;; ℛ𝒴;;; ℛ𝒴;;; ℛ𝒴;;; ℛ𝒴;;; 
      trigger (@IO _ unit "print" (Vint 1));;; ℛ𝒴;;; ℛℛ;;; 
      Ret (tt↑↑).
  
  Definition fnsems E : fnsems_type :=
    [(Some RRSNodeHdr.f_main, (true, wmask_all, scopes, (Some (RRSNodeAS.f_main_spec E), (cfunN f_main))));
     (Some RRSNodeHdr.f,      (true, wmask_all, scopes, (Some (RRSNodeAS.f_spec E),      (cfunN f))))].

  Program Definition smod E : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems E;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond : iProp Σ := emp%I.
  
  Definition t E sp := Seal.sealing CRIS (SMod.to_mod sp (smod E)).

End RRSNodeA. End RRSNodeA.

