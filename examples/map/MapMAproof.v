Require Import CRIS.

Require Import MapHeader MapM MapA.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module MapMA. Section MapMA.
  Import MapAS.
  Context `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ, !MapAGΓ Γ, !MapMGΓ Γ}.

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ :=
    (λ _ st_src st_tgt,
      ∃ f sz,
        ⌜st_src = [(MapA.v_map, f↑)] ∧ st_tgt = [(MapM.v_size, sz↑); (MapM.v_map, f↑)]⌝
        ∗ (⌜f = (λ _ : Z, 0%Z) ∧ sz = 0%Z⌝
            ∗ MapMS.pending
            ∗ initial_map
          ∨ pending
            ∗ auth_allocated f
            ∗ auth_unallocated sz))%I.

  Variable ginvH : invspec.
  Variable SpcH : string → option fspec.
  Hypothesis MapInSpcH : spc_incl MapAS.Spc SpcH.

  Variable ginvL : invspec.
  Variable SpcL : string → option fspec.
  Hypothesis MapInSpcL : spc_incl MapMS.Spc SpcL.

  Local Notation MapA := (MapA.t ginvH SpcH).
  Local Notation MapM := (MapM.t ginvL SpcL).
  
  Lemma simF_init : HSim.sim_fun MapA MapM Ist false MapName.init.
  Proof.
    init_simF.

    (* SRC: handle the IST of Map and the precond of init *)
    steps_l. iDestruct "ASM" as "((% & P) & %)".
    iDestruct "IST" as (f sz) "(% & [(% & P0 & INIT) | (P' & B & U)])"; cycle 1.
    { iExFalso. iApply (pending_unique with "P P'"). }
    des. hss. rename q into sz.
    
    (* TGT: prove the precond of init *)
    step_r. forces_r. iSplitL "P0". { iFrame. eauto. }

    (* TGT: handle the postcond of init *)
    hss. steps_r. iDestruct "GRT" as "(_ & %)". hss.
    
    (* SRC: prove the postcond of init *)
    iMod (initialize with "INIT") as "(ALLOC & UNALLOC & INIT)".
    forces_l. steps_l. forces_l.
    iSplitL "INIT". { iFrame. eauto. }
    
    (* prove the IST of Map *)
    step. iSplit; eauto.
    iExists _, _. iSplitR; eauto. iRight. iFrame. 
  Qed.

  Lemma simF_get : HSim.sim_fun MapA MapM Ist false MapName.get.
  Proof.
    init_simF.

    (* SRC: handle the IST of Map and the precond of get *)
    steps_l. iDestruct "ASM" as "((% & MAP) & %)".
    iDestruct "IST" as (f sz) "(% & [(% & P0 & INIT)|(P' & B & U)])".
    { iExFalso. iApply (initial_map_points_to with "INIT MAP"). }
    des. hss. steps_l.
    rename q1 into idx, q2 into v.

    (* TGT: prove the precond of get *)
    step_r. forces_r. hss. iSplit. { iFrame. eauto. }

    (* TGT : handle the body of get *)
    steps_r. hss. steps_r.
    iPoseProof (auth_unallocated_points_to with "U MAP") as "%".
    forces_r; eauto.

    (* TGT: handle the postcond of get *)
    steps_r. hss. steps_r. iDestruct "GRT" as "(_ & %)". subst.

    (* SRC: prove the postcond of get *)
    steps_l. forces_l.
    iPoseProof (auth_allocated_get with "B MAP") as "%". subst.
    iSplitL "MAP". { iFrame. eauto. }

    (* prove the IST of Map *)
    step. iSplit; eauto.
    iExists _, _. iSplit; eauto. iRight. iFrame.
  Unshelve. lia.
  Qed.

  Lemma simF_set : HSim.sim_fun MapA MapM Ist false MapName.set.
  Proof.
    init_simF.

    (* SRC: handle the IST of Map and the precond of set *)
    steps_l. iDestruct "ASM" as "((% & MAP) & %)".
    iDestruct "IST" as (f sz) "(% & [(% & P0 & INIT)|(P' & B & U)])".
    { iExFalso. iApply (initial_map_points_to with "INIT MAP"). }
    des. hss. steps_l. hss. steps_l.
    rename q2 into v', q3 into idx, q4 into v. hss.

    (* TGT: prove the precond of set *)
    step_r. force_r (idx,v'). forces_r. iSplitR; first eauto.

    (* TGT : handle the body of set *)
    hss. steps_r. hss. steps_r.
    iPoseProof (auth_unallocated_points_to with "U MAP") as "%".
    forces_r; eauto.

    (* TGT: handle the postcond of set *)
    steps_r. hss. steps_r. iDestruct "GRT" as "(_ & %)". hss.
    
    (* SRC : prove the postcond of set *)
    iPoseProof (auth_allocated_set with "B MAP") as ">(B & MAP)".
    forces_l. iSplitL "MAP". { iFrame. eauto. }

    (* prove the IST of Map *)
    step. iSplit; eauto.
    iExists _, _. iSplit; eauto. iRight. iFrame.
  Unshelve. done.
  Qed.

  Lemma simF_set_by_user : HSim.sim_fun MapA MapM Ist false MapName.set_by_user.
  Proof.
    init_simF.

    (* SRC: handle the IST of Map and the precond of set_by_user *)
    steps_l. iDestruct "ASM" as "((% & MAP) & %)".
    hss. steps_l.
    rename q1 into idx, q2 into v.
    
    (* TGT: prove the precond of set_by_user *)
    step_r. forces_r. hss. iSplitR. { eauto. }

    (* process an input *)
    steps_r. step.

    (* TGT: handle the precond of set *)
    steps_r. iDestruct "GRT" as "%". des. hss.
    
    (* SRC: prove the precond of set *)
    steps_l. force_l (_,_,_). forces_l.
    iSplitL "MAP". { iFrame. eauto. }

    (* make a call to set *)
    call "IST". { eauto. }

    (* SRC: handle the postcond of set *)
    steps_l. iDestruct "ASM" as "((% & MAP) & %)". hss.

    (* TGT: prove the postcond of set *)
    steps_l. forces_r. iSplitR. { iFrame. eauto. }

    (* TGT: handle the postcond of set_by_user *)
    steps_r. hss. steps_r. iDestruct "GRT" as "(_ & %)". subst.
    
    (* SRC: prove the postcond of set_by_user *)
    forces_l. iSplitL "MAP". { iFrame. eauto. }

    (* prove the IST of Map *)
    step. eauto.
  Qed.

  Theorem sim : HSim.t MapA MapM MapA.InitCond Ist false.
  Proof.
    init_sim.
    - iIntros "(IST & P)"; s.
      iExists _, _. iSplit; eauto. iLeft. iFrame. eauto.
    - apply simF_init; eauto.
    - apply simF_get; eauto.
    - apply simF_set; eauto.
    - apply simF_set_by_user; eauto.
  Qed.
End MapMA. End MapMA.
