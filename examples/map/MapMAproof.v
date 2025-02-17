Require Import CRIS.

Require Import MapHeader MapM MapA.
Require Import wsim_tactics ltac2_lib.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module MapMA. Section MapMA.
  Import MapAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !MapAGΓ Γ, !MapMGΓ Γ}.
  Context `{!ModRel u_a u_m} (n : level).

  Context (ginv_s : invspec) (Spc_s : string → option fspec).
  Context (MapInSpcS : spc_incl (MapAS.Spc u_a n) Spc_s).

  Context (ginv_t : invspec) (Spc_t : string → option fspec).
  Context (MapInSpcT : spc_incl (MapMS.Spc u_m n) Spc_t).

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

  Local Notation MapA := (MapA.t u_a n ginv_s Spc_s ).
  Local Notation MapM := (MapM.t u_m n ginv_t Spc_t ).

  Lemma simF_init : HSim.sim_fun open MapA MapM Ist MapName.init.
  Proof.
    init_wsim u_a u_m n.

    w_steps_l.
    iDestruct "ASM" as "[[[-> %range] P] ->]".

    (* SRC: handle the IST of Map and the precond of init *)
    iDestruct "IST" as (f sz) "(% & [(% & P0 & INIT) | (P' & B & U)])"; cycle 1.
    { iExFalso. iApply (pending_unique with "P P'"). }
    des. hss. rename q into sz.
    
    (* TGT: prove the precond of init *)
    w_step_r. w_force_r sz. w_force_r ([Vint sz] ↑). w_force_r.
    iSplitL "P0". { iFrame. eauto. }

    (* TGT: handle the postcond of init *)
    hss. w_steps_r. iDestruct "GRT" as "(_ & %)". hss.
    
    (* SRC: prove the postcond of init *)
    iMod (initialize with "INIT") as "(ALLOC & UNALLOC & INIT)".
    w_force_l. w_steps_l. w_force_l. w_force_l.
    iSplitL "INIT". { iFrame. eauto. }
    
    (* prove the IST of Map *)
    w_step. iSplit; eauto.
    iExists _, _. iSplitR; eauto. iRight. iFrame.
  Qed.

  Lemma simF_get : HSim.sim_fun open MapA MapM Ist MapName.get.
  Proof.
    init_wsim u_a u_m n.

    w_steps_l.
    iDestruct "ASM" as "((-> & MAP) & ->)".
    rename q1 into k.

    (* SRC: handle the IST of Map and the precond of get *)
    iDestruct "IST" as (f sz) "(% & [(% & P0 & INIT)|(P' & B & U)])".
    { iExFalso. iApply (initial_map_points_to with "INIT MAP"). }
    hss. w_steps_l. hss. w_steps_l.

    (* TGT: prove the precond of get *)
    w_step_r. w_force_r k. w_force_r. w_force_r.
    iSplit; first eauto.

    (* TGT : handle the body of get *)
    hss. w_steps_r. hss. w_steps_r.
    iPoseProof (auth_unallocated_points_to with "U MAP") as "%".
    w_force_r.

    (* TGT: handle the postcond of get *)
    w_steps_r. hss. w_steps_r. iDestruct "GRT" as "(_ & <-)".

    (* SRC: prove the postcond of get *)
    w_force_l. w_force_l.
    iPoseProof (auth_allocated_get with "B MAP") as "->".
    iSplitL "MAP". { iFrame. eauto. }

    (* prove the IST of Map *)
    w_step. iSplit; eauto.
    iExists _, _. iSplit; eauto. iRight. iFrame.
    Unshelve. done.
  Qed.

  Lemma simF_set : HSim.sim_fun open MapA MapM Ist MapName.set.
  Proof.
    init_wsim u_a u_m n.

    (* SRC: handle the IST of Map and the precond of set *)
    do 2 w_step_l.
    destruct q as [[k w] v]. w_steps_l.
    iDestruct "ASM" as "((-> & MAP) & ->)".
    iDestruct "IST" as (f sz) "(% & [(% & P0 & INIT)|(P' & B & U)])".
    { iExFalso. iApply (initial_map_points_to with "INIT MAP"). }
    des. hss. w_steps_l. hss. w_steps_l. hss.

    (* TGT: prove the precond of set *)
    w_step_r. w_force_r (k, v). w_force_r. w_force_r. iSplitR; first eauto.

    (* TGT : handle the body of set *)
    hss. w_steps_r. hss. w_steps_r.
    iPoseProof (auth_unallocated_points_to with "U MAP") as "%".
    w_force_r. w_steps_r. hss. w_steps_r.

    (* TGT: handle the postcond of set *)
    iDestruct "GRT" as "(_ & <-)".
    
    (* SRC : prove the postcond of set *)
    iPoseProof (auth_allocated_set with "B MAP") as ">(B & MAP)".
    w_force_l. w_force_l. iSplitL "MAP". { iFrame. eauto. }

    (* prove the IST of Map *)
    w_step. iSplit; eauto.
    iExists _, _. iSplit; eauto. iRight. iFrame.
    Unshelve. done.
  Qed.

  Lemma simF_set_by_user : HSim.sim_fun open MapA MapM Ist MapName.set_by_user.
  Proof.
    init_wsim u_a u_m n.

    (* SRC: handle the IST of Map and the precond of set_by_user *)
    do 2 w_step_l. destruct q as [k w]. w_steps_l.
    iDestruct "ASM" as "((-> & MAP) & ->)".
    hss. w_steps_l.

    (* TGT: prove the precond of set_by_user *)
    w_step_r. w_force_r. w_force_r. w_force_r. hss. iSplitR. { eauto. }

    (* process an input *)
    w_steps_r. w_step.

    (* TGT: handle the precond of set *)
    w_steps_r. iDestruct "GRT" as "%". des. hss.
    
    (* SRC: prove the precond of set *)
    w_steps_l. w_force_l (_,_,_). w_force_l. w_force_l.
    iSplitL "MAP". { iFrame. eauto. }

    (* make a call to set *)
    w_call "IST".

    (* SRC: handle the postcond of set *)
    w_steps_l. iDestruct "ASM" as "((-> & MAP) & ->)". hss.

    (* TGT: prove the postcond of set *)
    w_steps_l. w_force_r. w_force_r. iSplitR. { iFrame. eauto. }

    (* TGT: handle the postcond of set_by_user *)
    w_steps_r. hss. w_steps_r. iDestruct "GRT" as "(_ & <-)".
    
    (* SRC: prove the postcond of set_by_user *)
    w_force_l. w_force_l. iSplitL "MAP". { iFrame. eauto. }

    (* prove the IST of Map *)
    w_step. eauto.
  Qed.

  Lemma sim : HSim.t open MapA MapM MapA.InitCond Ist.
  Proof.
    init_sim.
    - iIntros "(IST & P)"; s.
      iExists _, _. iSplit; eauto. iLeft. iFrame. eauto.
    - apply simF_init; eauto.
    - apply simF_get; eauto.
    - apply simF_set; eauto.
    - apply simF_set_by_user; eauto.
  Qed.

  End MapMA.

  Section MapMA.
    Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !MapAGΓ Γ, !MapMGΓ Γ, !memGΓ Γ}.
    Lemma wctxr n Spc_s Spc_t ginv_t ginv_s
        (MapInSpcS : ∀ υ, spc_incl (MapAS.Spc υ n) (Spc_s υ))
        (MapInSpcT : ∀ υ, spc_incl (MapMS.Spc υ n) (Spc_t υ)) :
      w_ctx_refines
        ((λ υ, MapA.t υ n ginv_s (Spc_s υ)), MapA.InitCond)
        ((λ ν, MapM.t ν n ginv_t (Spc_t ν)), emp%I).
    Proof.
      exists 1%positive; intros u v Huv; eapply main_adequacy, MapMA.sim; eauto.
      Unshelve. r; lia.
    Qed.
End MapMA. End MapMA.