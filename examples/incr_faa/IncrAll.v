Require Import CRIS Cancel SMod.
Require Import MemI MemA MemIAproof ImpPrelude.
Require Import SchHeader SchI SchA SchIAproof SchTactics.
Require Import FaaHeader ClientI ClientA ClientIA FaaI FaaA FaaIA.

Module ClientAll.
  Import inv_instances.

  Local Definition csl : string → bool := λ _, false.
  Local Definition genv : GEnv.t := GEnv.unit.

  Local Instance Γ : HRA := ##[invΓ; concΓ; memΓ; newschΓ; incrΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ; newschΣ].

  Definition irΓ : Γ :=
    **[ir_invΓ; ir_concΓ; ir_memΓ csl genv; SchA.ir_schΓ; *[None]].
  Definition irΣ : Σ :=
    **[irΓ; ir_invΣ; SchA.ir_schΣ].

  Lemma irΣ_valid : ✓ (irΣ ⋅ ir_own_admin).
  Proof.
    solve_ir_valid.
    - apply ir_tidRA_valid.
    - apply ir_yieldRA_valid.
    - apply ir_memRA_valid.
    - apply SchA.ir_newtidRA_valid.
    - apply SchA.ir_joinRA_valid.
  Qed.

  (* source module *)
  Local Definition sp_user_s : specmap := ClientA.sp nroot.
  Local Definition smod_src : SMod.t := (ClientA.smod nroot) ☆ (SchA.smod ⊤ sp_user_s).
  Local Definition mod_top : Mod.t := SMod.to_mod ∅ (SMod.cancel smod_src).
  Local Definition mod_tgt : Mod.t := ClientI.t ★ FaaI.t ★ (MemI.t csl genv) ★ (SchI.t).

  Local Definition sp : specmap := SMod.conc_sp_from smod_src.
  Local Definition mod_src : Mod.t := SMod.to_mod sp smod_src.

  Local Definition SchInSp : (SchA.sp sp_user_s ⊤) ⊆ sp.
  Proof.
    repeat try eapply insert_subseteq_l; last apply map_empty_subseteq;
      rewrite lookup_insert_ne // lookup_kmap_Some; eexists (Some _); split; ss.
  Qed.
  Local Definition UserInSp : sp_user_s ⊆ sp.
  Proof.
    repeat try eapply insert_subseteq_l; last apply map_empty_subseteq;
      rewrite lookup_insert_ne // lookup_kmap_Some; eexists (Some _); split; ss.
  Qed.
  Local Definition MainInSp : (ClientA.sp nroot) ⊆ sp_user_s.
  Proof. by reflexivity. Qed.
  (* Local Definition MemInSp : sp_incl MemA.sp sp.
  Proof.
    ii; rewrite /sp /SchAS.sp /MemA.sp /ClientA.sp; unseal CRIS; split; [prove_nodup|ii].
    ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
  Qed. *)

  Local Definition init_cond : iProp Σ :=
    MemA.init_cond csl genv ∗ SchA.init_cond.
  (* Local Definition main_fsp : fspec := ClientA.main_spec ⊤ 1%Qp. *)

  Lemma mod_top_wf : Mod.wf mod_top.
  Proof.
    rewrite /mod_top SMod.cancel_add SMod.to_mod_add. eapply Mod.add_wf.
    { econs; eauto.
      rewrite /ClientA.smod /= /ClientA.fnsems !fmap_insert !fmap_empty; mod_tac ss.
    }
    { econs; eauto.
      { rewrite /SchA.smod /= /SchA.fnsems !fmap_insert !fmap_empty; mod_tac ss. }
      { ss; rewrite /SchA.scopes; multiset_solver. }
    }
    { set_solver. }
    { set_solver. }
  Qed.
  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    refines
      (mod_top, init_cond ∗ TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤) ∗ emp ∗ TIDAUTH 0 ∗ YIELDAUTH 1)%I
      (mod_src, init_cond).
  Proof.
    eapply Cancel.cancellation.
    { apply SMod.cancellable_add; r; rewrite /= /ClientA.fnsems /SchA.fnsems; mod_tac ss. }
    { apply mod_top_wf. }
    { assert (Ht : SMod.conc_sp_from smod_src !! speckey_entry =
        fsp_some (fspec_sch (↑nroot) fspec_trivial)); last (rewrite Ht; clear Ht).
      { rewrite lookup_insert_ne // lookup_kmap_Some; exists None; split; ss. }
       eexists _, _; splits.
      { ss; exists (0, 0, tt); split; refl. }
      { rewrite !nclose_nroot. iIntros "[$ [$ [$ ?]]]"; ss. admit. }
      { unfold_pre_post. iIntros "% % [_ [_ $]]". }
    }
  Admitted.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    eapply ctxr_refines.
    rewrite /mod_src /mod_tgt /smod_src.

    (* abstraction of Sch *)
    etrans; cycle 1.
    { do 3 ctxr_drop.
      eapply SchIA.ctxr.
      - apply SchInSp.
      - apply UserInSp.
      - rewrite dom_insert elem_of_union; left; apply elem_of_singleton; ss.
    }

    (* abstraction of Mem *)
    etrans; cycle 1.
    { do 3 ctxr_rotate. do 3 ctxr_drop.
      eapply MemIA.ctxr.
    }

    (* abstraction of Faa *)
    etrans; cycle 1.
    { do 2 ctxr_drop.
      eapply main_adequacy, FaaIA.sim.
    }
    rewrite /FaaIA.FaaIA.MA.
    
    (* abstraction of Incr *)
    etrans; cycle 1.
    { ctxr_drop.
      eapply ClientIA.ctxr; cycle 2.
      - apply MainInSp.
      - rewrite nclose_nroot. apply SchInSp.
    }

    etrans; cycle 1.
    { ctxr_rotate. ctxr_refl. }

    (* elimination of mem *)
    etrans; cycle 1.
    { do 2 ctxr_rotate. do 2 ctxr_drop. eapply CFilter.elim_module. }
    rewrite -mod_add_empty_r.

    rewrite /SchIAproof.SchIA.SchAMod.
    rewrite /SchA.t /ClientA.t /MemA.t.
    unseal CRIS.
    ctxr_rotate.
    rewrite SMod.to_mod_add /init_cond //.
  (*SLOW*)Qed.

  Lemma top_tgt :
    refines (mod_top, init_cond ∗ TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤) ∗ emp ∗ TIDAUTH 0 ∗ YIELDAUTH 1)%I
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Lemma tgt_wf : Mod.wf mod_tgt.
  Proof.
    rewrite /mod_tgt; eapply Mod.add_wf.
    { econs; eauto.
      rewrite /ClientA.smod /= /ClientA.fnsems !fmap_insert !fmap_empty; mod_tac ss.
    }
    { eapply Mod.add_wf.
      { econs; eauto.
      rewrite /ClientA.smod /= /ClientA.fnsems !fmap_insert !fmap_empty; mod_tac ss.
      }
      { eapply Mod.add_wf.
        { econs; eauto.
          { rewrite /ClientA.smod /= /ClientA.fnsems !fmap_insert !fmap_empty; mod_tac ss. }
          { ss; rewrite /MemI.scopes; multiset_solver. }
        }
        { econs; eauto.
          { rewrite /= !fmap_insert !fmap_empty; mod_tac ss. }
          { ss; rewrite /SchI.scopes; multiset_solver. }
        }
        { set_solver. }
        { set_solver. }
      }
      { rewrite Mod.dom_fnsems_add; set_solver. }
      { set_solver. }
    }
    { rewrite !Mod.dom_fnsems_add; set_solver. }
    { set_solver. }
  Qed.

  Lemma init_cond_valid:
    ∃ rs, ✓ rs ∧ (Own rs ⊢ |==> init_cond ∗ TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤) ∗ emp ∗ TIDAUTH 0 ∗ YIELDAUTH 1).
  Proof.
    exists (irΣ ⋅ ir_own_admin). split.
    - apply irΣ_valid.
    - simplify_res.
      { rewrite make_own_admin.
        iDestruct "H24" as "[H24 Htid]". iFrame.
        rewrite /MemA.init_cond /ir_memRA; iDestruct "H26" as "[$ _]".
        iPoseProof (make_sys_init with "[$] [$]") as "[$ [$ [$ $]]]". done.
      }
    all: solve_res.
  Qed.

  Theorem behavioral_refinement :
    ∃ src_res tgt_res, refines_lmod
      (Mod.to_lmod mod_top src_res)
      (Mod.to_lmod mod_tgt tgt_res).
  Proof.
    move: (top_tgt)=>H; rewrite /refines in H; des; ss.
    hexploit H; eauto using tgt_wf. clear H; intros [WF H].
    assert (IV:= init_cond_valid). des.
    destruct (H rs); des; et.
    rewrite IV0 /init_cond.
    rewrite {1}winv_split_empty. iIntros ">[[$ $] [$ [$ [[? ?] ?]]]]". iFrame. done.
  (*SLOW*)Qed.
End ClientAll.
