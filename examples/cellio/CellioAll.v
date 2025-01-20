Require Import CRIS Cancel.
Require Import ImpPrelude.
Require Import CellioHeader MainHeader InputHeader FooHeader.
Require Import CellioA CellioI MainA MainI InputA.
Require Import InputASpec FooASpec.
Require Import CellioIAproof MainIAproof.

Module CellioAll. Section CellioAll.
  Import inv_instances.
  Local Instance Γ : HRA := ##[invΓ; CellioAΓ].
  Local Instance Σ : GRA := ##[invΣ; Γ].
  
  (* Definition stb_add stb0 stb1: Sk.t -> string -> option fspec :=
    fun sk fn =>
      match stb0 sk fn, stb1 sk fn with
      | Some fsp, None => Some fsp
      | None, Some fsp => Some fsp
      | _, _ => None
      end. *)

  Local Definition smod_src : SMod.t := MainA.Mod ☆ CellioA.Mod ☆ InputA.Mod.
  Local Definition ginv : Sk.t → invspec := λ _ _, True%I.
  Local Definition stb : Sk.t → string → option fspec := stb_global smod_src.
  Local Definition mod_cancel : HMod.t := SModCancel.to_hmod smod_src.
  Local Definition mod_src : HMod.t := SMod.to_hmod ginv stb smod_src.
  Local Definition mod_tgt : HMod.t := MainI.t ★ CellioI.t ★ (InputA.t ginv stb).

  Local Definition main_fsp : fspec := fspec_trivial.
  Local Definition init_cond : Sk.t → iProp Σ := MainA.InitCond ∗∗ CellioA.InitCond ∗∗ InputA.InitCond.
  Local Definition skeleton : Sk.t := Sk.add CellioSK.t MainSK.t.

  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    refines (mod_cancel, init_cond ∗∗ (λ _, main_fsp.(precond) 0 tt tt↑ tt↑)) 
            ((mod_src, init_cond) : HMod.modc).
  Proof.
    eapply cancellation; try by econs.
    i. iIntros "%POST". iPureIntro.
    des; eauto.
  Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, const(emp)%I).
  Proof.
    (* consider identical modules in src/tgt as context (InputA) *)
    eapply ctxr_refines.
    rewrite -[(_, const (emp%I))]hmod_addc_empty_r /init_cond -hmod_addc_assoc.
    rewrite /mod_src /mod_tgt !add_interp_comm -!hmod_add_assoc /InputA.t.
    unseal CRIS. eapply ctxr_frameR, ctxr_cond_frameR.
    (* solve by transitivity:
      MainI ★ CellioI ⊆ MainI ★ CellioA ⊆ MainA ★ CellioA 
    *)
    etrans.
    {
      (* MainI ★ CellioA ⊆ MainA ★ CellioA *)
      rewrite -[(SMod.to_hmod _ _ MainA.Mod)](Seal.sealing_eq CRIS) -[(SMod.to_hmod _ _ CellioA.Mod)](Seal.sealing_eq CRIS).
      instantiate (1:= (MainI.t ★ (CellioA.t ginv stb), (const(emp%I)) ∗∗ CellioA.InitCond)).
      eapply ctxr_cond_frameR, main_adequacy, MainIA.sim.
      {
        admit. 
      }
      {
        i. rewrite /InputAS.Stb. unseal CRIS. econs; first prove_nodup.
        ii; rewrite -FIND /stb /stb_global /smod_src //=. des_ifs; ss; des_ifs.
      }
    }
    (* MainI ★ CellioI ⊆ MainI ★ CellioA 
      by CellioI ⊆ctx CellioA *)
    rewrite -[(_, const (emp%I))]hmod_addc_empty_r.
    eapply ctxr_frameL, ctxr_cond_frameL, main_adequacy, CellioIA.sim. 
    i. rewrite /InputAS.Stb. unseal CRIS. econs; first prove_nodup.
    ii; rewrite -FIND /stb /stb_global /smod_src //=.
    des_ifs; ss; des_ifs.
  (* Qed. *)
  Admitted.

  Lemma cancel_tgt :
    refines (mod_cancel, init_cond ∗∗ (λ _, main_fsp.(precond) 0 tt tt↑ tt↑))
            (mod_tgt, const(emp)%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Local Definition initial_resource : Σ := MainAS.init_res ⋅ CellioAS.init_res.
  Lemma initial_resource_valid : ✓ initial_resource.
  Proof.
    rewrite /initial_resource /MainAS.init_res /CellioAS.init_res -own.iRes_singleton_op.
    apply discrete_fun_singleton_valid, allocs.allocs_frag_valid,
      cmra_transport_valid, excl_auth_valid.
  Qed.

  Theorem behavioral_refinement :
    ∃ target_resource, refines_modsem
      (HModSem.to_mod ((HMod.modsem mod_cancel) skeleton) initial_resource)
      (HModSem.to_mod ((HMod.modsem mod_tgt) skeleton) target_resource).
  Proof.
    move: (cancel_tgt)=>H; rewrite /refines in H; des; ss.
    destruct (REF skeleton initial_resource).
    { rewrite /CellioI.t /MainI.t /skeleton; unseal CRIS; ss. }
    { rewrite /skeleton /CellioSK.t /MainSK.t; ss; econs; ii; ss; des; ss; prove_nodup. }
    { apply initial_resource_valid. }
    { iIntros "I"; rewrite /init_cond /CellioA.init_cond /MainA.init_cond /HMod.addc.
      rewrite /precond /= /CellioAS.Ready /CellioAS.Ball
        own.Own_eq own.own_eq /own.Own_def /own.own_def.
      iDestruct "I" as "[I1 I2]"; iFrame. iSplit; iPureIntro; ss.
    }
    { econs; ss; try prove_nodup. }
    { exists x; des; eauto. }
  Qed.
End CellioAll. End CellioAll.
Print Assumptions CellioAll.behavioral_refinement.