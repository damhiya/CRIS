Require Import CRIS Cancel.

Require Import MutHeader MutMainHeader MutFA MutGA MutMainA.
Require Import MutFI MutGI MutMainI.
Require Import MutIAproof MutMainIAproof.

Module MutAll. Section MutAll.
  Import inv_instances.
  Local Instance Γ : HRA := ##[invΓ].
  Local Instance Σ : GRA := ##[invΣ; Γ].

  Local Definition smod_src : SMod.t := MutMainA.Mod ☆ MutFA.Mod ☆ MutGA.Mod.
  Local Definition ginv : invspec := λ _, True%I.
  Local Definition stb : string → option fspec := spc_global smod_src.
  Local Definition mod_cancel : HMod.t := SModCancel.to_hmod smod_src.
  Local Definition mod_src : HMod.t := SMod.to_hmod ginv stb smod_src.
  Local Definition mod_tgt : HMod.t := MutMainI.t ★ MutFI.t ★ MutGI.t.

  Local Definition main_fsp : fspec := MutMainA.main_spec.
  Local Definition init_cond : iProp Σ := MutFA.InitCond ∗ MutGA.InitCond.

  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    refines (mod_cancel, (init_cond ∗ main_fsp.(precond) 0 tt tt↑ tt↑)%I)
            ((mod_src, init_cond) : HMod.modc).
  Proof.
    eapply cancellation; try by econs.
    i. iIntros "%POST". iPureIntro.
    des; eauto.
  Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    eapply ctxr_refines.
    (* rewrite -[(mod_tgt, _)]hmod_addc_empty_r. *)
    unfold mod_src, mod_tgt. rewrite !add_interp_comm.
    rewrite -hmod_add_assoc.
    etrans.
    { rewrite -hmod_addc_empty_l. eapply ctxr_cond_frameR. eapply ctxr_frameR.
      replace (SMod.to_hmod ginv stb MutMainA.Mod) with (MutMainA.t ginv stb); cycle 1.
      { unfold MutMainA.t. unseal CRIS. ss. }
      replace (SMod.to_hmod ginv stb MutFA.Mod) with (MutFA.t ginv stb); cycle 1.
      { unfold MutFA.t. unseal CRIS. ss. }
      apply MutMainIA.correct.
    }
    rewrite hmod_add_assoc hmod_addc_empty_l.
    eapply ctxr_frameL.
    replace (SMod.to_hmod ginv stb MutGA.Mod) with (MutGA.t ginv stb); cycle 1.
    { unfold MutGA.t. unseal CRIS. ss. }
    apply MutIA.correct.
  Qed.

  Lemma cancel_tgt :
    refines (mod_cancel, (init_cond ∗ main_fsp.(precond) 0 tt tt↑ tt↑)%I)
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Local Definition initial_resource : Σ := ε.
  Lemma initial_resource_valid : ✓ initial_resource.
  Proof. econs. Qed.

  Theorem behavioral_refinement :
    ∃ target_resource, refines_mod
      (HMod.to_mod mod_cancel initial_resource)
      (HMod.to_mod mod_tgt target_resource).
  Proof.
    move: (cancel_tgt)=>H; rewrite /refines in H; des; ss.
    destruct (H initial_resource).
    { apply initial_resource_valid. }
    { iIntros; iSplit; et. }
    { econs; ss; try prove_nodup. }
    { exists x; des; eauto. }
  Qed.
End MutAll. End MutAll.
(* Print Assumptions MutAll.behavioral_refinement. *)
