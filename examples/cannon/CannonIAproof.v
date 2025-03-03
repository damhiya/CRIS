Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader CannonI CannonA.

Set Implicit Arguments.
Local Open Scope nat_scope.

Module CannonIA. Section CannonIA.
  Import CannonAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !CannonAGΓ Γ}.

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ :=
    (λ _ st_s st_t,
      (⌜st_s = [(CannonA.v_lv, 1%Z↑)] /\ st_t = [(CannonI.v_lv, 1%Z↑)]⌝ ∗
      (Ready ∨ Fired))
    )%I.

  Variable u: univ_id.
  Variable SpcCannon : string -> option fspec.
  
  Local Definition CannonAMod := (CannonA.t u SpcCannon).
  Local Definition CannonIMod := (CannonI.t).

  Lemma simF_fire : HSim.sim_fun open CannonAMod CannonIMod Ist CannonName.fire.
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "((%Y & B) & %Q)". subst. hss.
    unfold Ist. iDestruct "IST" as "[[% %] [R | F]]"; cycle 1. 
    (* already fired *)
    { iExFalso. iApply FiredBall. iFrame. }

    steps_r. force_r. iSplitR.
    { iPureIntro. rewrite Any.upcast_downcast. et. }
    steps_r. change (1 `div` 1)%Z with 1%Z.
    step. steps_l. force_l. force_l. instantiate (1:=(1%Z)↑). iSplitR; et.
    steps_r. ss.
  Qed.

  Theorem sim : HSim.t open CannonAMod CannonIMod CannonA.init_cond Ist.
  Proof.
    init_sim.
    - iIntros "IC". unfold Ist, CannonA.init_cond. iSplitR; et.
    - eapply simF_fire; eauto.
  Qed.

  Theorem correct :
    ctx_refines
      (CannonAMod, CannonA.init_cond)
      (CannonIMod, emp%I).
  Proof.
    eapply main_adequacy.
    apply sim.
  Qed.
End CannonIA. End CannonIA.
