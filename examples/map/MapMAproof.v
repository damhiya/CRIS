Require Import CRIS.

Require Import MapHeader MapM MapA.
Require Import wsim_tactics ltac2_lib.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module MapMA. Section MapMA.
  Import MapAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !MapAGΓ Γ, !MapMGΓ Γ}.
  Context (u_a u_m : univ_id).
  Context `(u_a > u_m).

  Context (spc_s spc_t : string → option fspec).
  Context (MapInSpcS : spc_incl (MapAS.spc u_a) spc_s).
  Context (MapInSpcT : spc_incl (MapMS.spc u_m) spc_t).

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

  Local Definition MapA := (MapA.t u_a spc_s).
  Local Definition MapM := (MapM.t u_m spc_t).

  Lemma simF_init : HSim.sim_fun open MapA MapM Ist MapName.init.
  Proof.
    winit_simF u_a u_m.

    wsteps_l.
    iDestruct "ASM" as "[[[-> %range] P] ->]".

    (* SRC: handle the IST of Map and the precond of init *)
    iDestruct "IST" as (f sz) "(% & [(% & P0 & INIT) | (P' & B & U)])"; cycle 1.
    { iExFalso. iApply (pending_unique with "P P'"). }
    des. hss. rename q into sz.
    
    (* TGT: prove the precond of init *)
    wstep_r. wforce_r sz. wforce_r ([Vint sz] ↑). wforce_r.
    iSplitL "P0". { iFrame. eauto. }

    (* TGT: handle the postcond of init *)
    hss. wsteps_r. iDestruct "GRT" as "(_ & %)". hss.
    
    (* SRC: prove the postcond of init *)
    iMod (initialize with "INIT") as "(ALLOC & UNALLOC & INIT)".
    wforce_l. wsteps_l. wforce_l. wforce_l.
    iSplitL "INIT". { iFrame. eauto. }
    
    (* prove the IST of Map *)
    wstep. iSplit; eauto.
    iExists _, _. iSplitR; eauto. iRight. iFrame.
  (*FAST*)Qed.

  Lemma simF_get : HSim.sim_fun open MapA MapM Ist MapName.get.
  Proof.
    winit_simF u_a u_m.

    wsteps_l.
    iDestruct "ASM" as "((-> & MAP) & ->)".
    rename q1 into k.

    (* SRC: handle the IST of Map and the precond of get *)
    iDestruct "IST" as (f sz) "(% & [(% & P0 & INIT)|(P' & B & U)])".
    { iExFalso. iApply (initial_map_points_to with "INIT MAP"). }
    hss. wsteps_l. hss. wsteps_l.

    (* TGT: prove the precond of get *)
    wstep_r. wforce_r k. wforce_r. wforce_r.
    iSplit; first eauto.

    (* TGT : handle the body of get *)
    hss. wsteps_r. hss. wsteps_r.
    iPoseProof (auth_unallocated_points_to with "U MAP") as "%".
    wforce_r; first eauto.

    (* TGT: handle the postcond of get *)
    wsteps_r. hss. wsteps_r. iDestruct "GRT" as "(_ & <-)".

    (* SRC: prove the postcond of get *)
    wforce_l. wforce_l.
    iPoseProof (auth_allocated_get with "B MAP") as "->".
    iSplitL "MAP". { iFrame. eauto. }

    (* prove the IST of Map *)
    wstep. iSplit; eauto.
    iExists _, _. iSplit; eauto. iRight. iFrame.
  (*FAST*)Qed.

  Lemma simF_set : HSim.sim_fun open MapA MapM Ist MapName.set.
  Proof.
    winit_simF u_a u_m.

    (* SRC: handle the IST of Map and the precond of set *)
    do 2 wstep_l.
    destruct q as [[k w] v]. wsteps_l.
    iDestruct "ASM" as "((-> & MAP) & ->)".
    iDestruct "IST" as (f sz) "(% & [(% & P0 & INIT)|(P' & B & U)])".
    { iExFalso. iApply (initial_map_points_to with "INIT MAP"). }
    des. hss. wsteps_l. hss. wsteps_l. hss.

    (* TGT: prove the precond of set *)
    wstep_r. wforce_r (k, v). wforce_r. wforce_r. iSplitR; first eauto.

    (* TGT : handle the body of set *)
    hss. wsteps_r. hss. wsteps_r.
    iPoseProof (auth_unallocated_points_to with "U MAP") as "%".
    wforce_r; first done. wsteps_r. hss. wsteps_r.

    (* TGT: handle the postcond of set *)
    iDestruct "GRT" as "(_ & <-)".
    
    (* SRC : prove the postcond of set *)
    iPoseProof (auth_allocated_set with "B MAP") as ">(B & MAP)".
    wforce_l. wforce_l. iSplitL "MAP". { iFrame. eauto. }

    (* prove the IST of Map *)
    wstep. iSplit; eauto.
    iExists _, _. iSplit; eauto. iRight. iFrame.
  (*FAST*)Qed.

  Lemma simF_set_by_user : HSim.sim_fun open MapA MapM Ist MapName.set_by_user.
  Proof.
    winit_simF u_a u_m.

    (* SRC: handle the IST of Map and the precond of set_by_user *)
    do 2 wstep_l. destruct q as [k w]. wsteps_l.
    iDestruct "ASM" as "((-> & MAP) & ->)".
    hss. wsteps_l.

    (* TGT: prove the precond of set_by_user *)
    wstep_r. wforce_r. wforce_r. wforce_r. hss. iSplitR. { eauto. }

    (* process an input *)
    wsteps_r. wstep.

    (* TGT: handle the precond of set *)
    wsteps_r. iDestruct "GRT" as "%". des. hss.
    
    (* SRC: prove the precond of set *)
    wsteps_l. wforce_l (_,_,_). wforce_l. wforce_l.
    iSplitL "MAP". { iFrame. eauto. }

    (* make a call to set *)
    wcall "IST".

    (* SRC: handle the postcond of set *)
    wsteps_l. iDestruct "ASM" as "((-> & MAP) & ->)". hss.

    (* TGT: prove the postcond of set *)
    wsteps_l. wforce_r. wforce_r. iSplitR. { iFrame. eauto. }

    (* TGT: handle the postcond of set_by_user *)
    wsteps_r. hss. wsteps_r. iDestruct "GRT" as "(_ & <-)".
    
    (* SRC: prove the postcond of set_by_user *)
    wforce_l. wforce_l. iSplitL "MAP". { iFrame. eauto. }

    (* prove the IST of Map *)
    wstep. eauto.
  (*FAST*)Qed.

  Lemma sim : HSim.t open MapA MapM MapA.init_cond Ist.
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
  Lemma ctxr u_s u_t spc_s spc_t
      (LE : u_s > u_t)
      (MapInSpcS : spc_incl (MapAS.spc u_s) spc_s)
      (MapInSpcT : spc_incl (MapMS.spc u_t) spc_t) :
    ctx_refines
      (MapA.t u_s spc_s, MapA.init_cond)
      (MapM.t u_t spc_t, emp%I).
  Proof. eapply main_adequacy, MapMA.sim; eauto. Qed.
End MapMA. End MapMA.