Require Import CRIS.
Require Import ImpPrelude.
Require Import ElimRel SModCancel Cancellation.
Require Import CannonI CannonMainI.
Require Import CannonA CannonASpec CannonMainA CannonMainASpec.
Require Import CannonIAproof CannonMainIAproof.

Set Implicit Arguments.

Module CannonAll.
Section C.
  Definition Γ : HRA := ##[invΓ; CannonAS.GΓ].
  Local Existing Instance Γ.

  Definition τ : Typ.t :=
    fun _ => ST.t.
  Local Existing Instance τ.

  Definition α : SRFCons.t :=
    fun n => 
      match n with
      | 0 => SL.syntax
      | _ => inv_syntax
      end.
  Local Existing Instance α.

  Definition Σ : GRA := ##[invΣ; Γ].
  Local Existing Instance Σ.

  Local Instance subG_GΓ : subG Γ Σ.
  Proof. Admitted. 

  Local Instance invGS_GΓ: invGS Σ Γ.
  Proof. Admitted.

  Definition β : SRFIntp.t :=
    fun n => 
      match n with
      | 0 => SL.t
      | _ => (@inv_interp α Γ Σ subG_GΓ _) 
      end.

  Local Instance sinvGS_: sinvGS Σ Γ α β τ.
  Proof. Admitted.

  Local Instance asdf: CannonAS.GS Γ.
  Proof. Admitted.

  Definition Mod := (@CannonA.Mod Σ Γ α β τ sinvGS_ _) ☆ (@MainA.Mod Σ Γ α β τ sinvGS_ _ 1).

  Definition ginv0 : invspec := fun _ => True%I.
  Definition ginv : Sk.t -> invspec := fun _ => ginv0.

  Definition stb := stb_global Mod.

  Definition md_cancel := SModCancel.to_hmod Mod.
  Definition md_src := SMod.to_hmod ginv stb Mod.
  Definition md_tgt := CannonI.t ★ (MainI.t 1).

  Definition mainfsp : fspec := (@MainAS.main_spec Σ Γ α β τ _ _).

  Definition InitCond: Sk.t -> iProp Σ := 
    (@CannonA.InitCond Σ Γ α β τ sinvGS_ _) ∗∗ (@MainA.InitCond Σ Γ α β τ sinvGS_ _).

  (* Apply cancellation to linked spec module *)
  Lemma cancel meta: 
    refines (md_cancel, InitCond ∗∗ (fun _ => mainfsp.(precond) 0 meta tt↑ tt↑)) 
            (md_src, InitCond).
  Proof.
    eapply cancellation; try by econs.
    i. iIntros "%POST". iPureIntro.
    des; eauto.
  Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma correct:
    refines (md_src, InitCond) (md_tgt, const(emp)%I).
  Proof.
    eapply ctxr_refines. 
    rewrite -[(md_tgt, _)]hmod_addc_empty_r.
    unfold md_src, md_tgt. rewrite add_interp_comm.
    eapply ctxr_compose_hor.
    { 
      replace (SMod.to_hmod ginv stb CannonA.Mod)
      with (@CannonA.t Σ Γ α β τ sinvGS_ _ ginv stb); cycle 1.
      { unfold CannonA.t. unseal "ccr". ss. }
      eapply CannonIA.correct.
    }
    {
      replace (SMod.to_hmod ginv stb (MainA.Mod 1))
      with (@MainA.t Σ Γ α β τ sinvGS_ _ 1 ginv stb); cycle 1.
      { unfold MainA.t. unseal "ccr". ss. }
      eapply CannonMainIA.correct.
      i. econs.
      { unfold CannonAS.Stb. unseal "ccr". econs. ss. econs. }
      unfold stb_sub, stb, stb_global, Mod, to_stb.
      unfold CannonAS.Stb. unseal "ccr". i. ss.
      destruct (fn ?[ eq ] CannonHeader.CannonName.fire); ss.
    }
  Qed.

  Theorem final:
    ∃meta, refines (md_cancel, InitCond ∗∗ (fun _ => mainfsp.(precond) 0 meta tt↑ tt↑))
            (md_tgt, const(emp)%I).
  Proof.
    exists tt.
    etrans.
    - eapply cancel.
    - eapply correct.
  Qed.

End C.
End CannonAll.