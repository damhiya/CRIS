Require Import CRIS Cancel.
Require Import ImpPrelude.
Require Import CellioHeader MainHeader InputHeader FooHeader.
Require Import CellioA CellioI MainA MainI InputA FooA.
Require Import CellioIAproof MainIAproof.

Module CellioAll. Section CellioAll.
  Import inv_instances.  
  Local Instance Γ : HRA := ##[invΓ; CellioAΓ].
  Local Instance Σ : GRA := ##[invΣ; Γ].
  Variable foo: Any.t -> itree hmodE Any.t.
  Local Definition smod_src : SMod.t := MainA.Mod ☆ CellioA.Mod ☆ InputA.Mod ☆ (FooA.Mod foo).
  Local Definition ginv : Sk.t → invspec := λ _ _, True%I.
  Local Definition stb : Sk.t → string → option fspec := stb_global smod_src.
  Local Definition mod_cancel : HMod.t := SModCancel.to_hmod smod_src.
  Local Definition mod_src : HMod.t := SMod.to_hmod ginv stb smod_src.
  Local Definition mod_tgt : HMod.t := MainI.t ★ CellioI.t ★ (InputA.t ginv stb) ★ (FooA.t foo ginv stb).

  Local Definition main_fsp : fspec := fspec_trivial.
  Local Definition init_cond : Sk.t → iProp Σ := MainA.InitCond ∗∗ CellioA.InitCond ∗∗ InputA.InitCond ∗∗ FooA.InitCond.
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
    (* consider identical modules in src/tgt as context (InputA, FooA) *)
    eapply ctxr_refines.
    rewrite -[(_, const (emp%I))]hmod_addc_empty_r /init_cond -!hmod_addc_assoc.
    rewrite /mod_src /mod_tgt !add_interp_comm -!hmod_add_assoc /FooA.t.
    unseal CRIS. eapply ctxr_frameR, ctxr_cond_frameR.
    rewrite -[(_, const (emp%I))]hmod_addc_empty_r /InputA.t.
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
        i. rewrite /FooAS.Stb. unseal CRIS. econs; first prove_nodup.
        ii; rewrite -FIND /stb /stb_global /smod_src //=. des_ifs; ss; des_ifs.
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
  Qed.

  Lemma cancel_tgt :
    refines (mod_cancel, init_cond ∗∗ (λ _, main_fsp.(precond) 0 tt tt↑ tt↑))
            (mod_tgt, const(emp)%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Local Definition initial_resource : Σ := MainA.InitRes ⋅ CellioA.InitRes ⋅ InputA.InitRes ⋅ FooA.InitRes.

  Lemma initial_resource_valid : ✓ initial_resource.
  Proof.
    rewrite /initial_resource /CellioA.InitRes !right_id left_id /own.iRes_singleton.
    apply discrete_fun_singleton_valid, allocs.allocs_frag_valid, cmra_transport_valid. 
    unfold "●E". apply auth_auth_valid. econs.  
  Qed.

  Theorem behavioral_refinement :
    ∃ target_resource, refines_modsem
      (HModSem.to_mod ((HMod.modsem mod_cancel) skeleton) initial_resource)
      (HModSem.to_mod ((HMod.modsem mod_tgt) skeleton) target_resource).
  Proof.
    move: (cancel_tgt)=>H; rewrite /refines in H; des; ss.
    destruct (REF skeleton initial_resource).
    { rewrite /CellioI.t /MainI.t /InputA.t /FooA.t /skeleton; unseal CRIS; ss. }
    { rewrite /skeleton /CellioSK.t /MainSK.t; ss; econs; ii; ss; des; ss; prove_nodup. }
    { apply initial_resource_valid. }
    { iIntros "I"; rewrite /init_cond /CellioA.InitCond /MainA.InitCond /InputA.InitCond /FooA.InitCond /HMod.addc.
      rewrite /precond /= /CellioA.auth 
       own.Own_eq own.own_eq /own.Own_def /own.own_def. 
      iDestruct "I" as "[[[_ I] _] _]"; iFrame. 
      iSplit; iPureIntro; ss.
    }
    { econs; ss; try prove_nodup. }
    { exists x; des; eauto. }
  Qed.
End CellioAll. End CellioAll.
(* Print Assumptions CellioAll.behavioral_refinement. *)
