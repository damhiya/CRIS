Require Import CRIS Cancel.
Require Import PFMemHeader PFMemA base HistoryRA AtomicRA PFMemA PFMemI PFMemIA.
Require Import SystemHeader SystemI SystemA SystemIA SystemTactics.
Require Import MPI MPA MPIA.
Require Import Language.

Module MPAll.
  Import inv_instances.

  Definition lang := Language.mk (λ _ : (), tt) (const False) (λ _ : ProgramEvent.t, λ _ _, True).
  Definition syn : Threads.syntax := IdentMap.singleton 1%positive (existT lang tt).
  Definition init : Configuration.t := Configuration.init syn [].

  Local Instance Γ : HRA := ##[invΓ; concΓ; histΓ; atomicΓ; sysΓ; one_shotΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ].

  Definition irΓ : Γ := **[ir_invΓ; ir_concΓ; PFMemA.ir_histΓ; *[None]; ir_sysΓ; *[None]].
  Definition irΣ : Σ := **[irΓ; ir_invΣ].

  Lemma irΣ_valid : ✓ (irΣ ⋅ ir_own_admin).
  Proof.
    solve_ir_valid.
    - apply ir_tidRA_valid.
    - apply ir_yieldRA_valid.
    - apply PFMemA.ir_viewR_valid.
    - apply PFMemA.ir_histR_valid.
    - apply PFMemA.ir_hist_freeableUR_valid.
    - apply ir_sysRA_valid.
  Qed.

  (* source module *)
  Local Definition sp_user_s : specmap := MPA.sp.
  Local Definition smod_src : SMod.t := (MPA.Mod) ☆ (SystemA.Mod sp_user_s ⊤) ☆ (PFMemA.smod).
  Local Definition mod_top : Mod.t := SMod.to_mod ∅ (SMod.cancel smod_src).
  Local Definition mod_tgt : Mod.t := MPI.t ★ (SystemI.t) ★ (PFMemI.t syn []).

  Local Definition sp : specmap := SMod.conc_sp_from smod_src.
  Local Definition mod_src : Mod.t := SMod.to_mod sp smod_src.

  Local Definition SchInSp : (SystemA.sp sp_user_s ⊤) ⊆ sp.
  Proof.
    repeat try eapply insert_subseteq_l; last apply map_empty_subseteq;
      rewrite lookup_insert_ne // lookup_kmap_Some; eexists (Some _); split; ss.
  Qed.

  Local Definition UserInSp : sp_user_s ⊆ sp.
  Proof.
    repeat try eapply insert_subseteq_l; last apply map_empty_subseteq;
      rewrite lookup_insert_ne // lookup_kmap_Some; eexists (Some _); split; ss.
  Qed.

  Local Definition MainInSp : (MPA.sp) ⊆ sp_user_s. Proof. refl. Qed.

  Lemma mod_top_wf : Mod.wf mod_top.
  Proof.
    rewrite /mod_top ?SMod.cancel_add ?SMod.to_mod_add. eapply Mod.add_wf.
    { econs; eauto.
      rewrite /MPA.Mod /= /MPA.fnsems /Mod.fnsems /= !fmap_insert !fmap_empty; mod_tac ss.
    }
    { econs; eauto.
      { eapply Mod.add_wf.
        { econs; eauto.
          { rewrite /SystemA.Mod /= /SystemA.fnsems /Mod.fnsems /=
              !fmap_insert !fmap_empty; mod_tac ss. }
          { rewrite /= /SystemA.scopes; multiset_solver. }
        }
        { econs; eauto.
          { rewrite /PFMemA.smod /= /PFMemA.fnsems /Mod.fnsems /=
              !fmap_insert !fmap_empty; mod_tac ss. }
          { rewrite /= /PFMemA.scopes; multiset_solver. }
        }
        { set_solver. }
        { set_solver. }
      }
      { rewrite /=; i; rewrite multiplicity_disj_union /SystemA.scopes /PFMemA.scopes.
        multiset_solver.
      }
    }
    { rewrite !Mod.dom_fnsems_add; set_solver. }
    { set_solver. }
  Qed.

  Local Definition init_cond : iProp Σ := PFMemA.init_cond ∗ SystemA.init_cond [].

  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    refines
      (mod_top,
        init_cond ∗ TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤) ∗
        tview_sys_gen 1 1 0 (TView.init []) ∗ TIDAUTH 0 ∗ YIELDAUTH 1)%I
      (mod_src, init_cond).
  Proof.
    eapply Cancel.cancellation.
    { apply SMod.cancellable_add; last apply SMod.cancellable_add; r;
        rewrite /= /MPA.fnsems /SystemA.fnsems /PFMemA.fnsems; mod_tac ss.
    }
    { apply mod_top_wf. }
    { assert (Ht : SMod.conc_sp_from smod_src !! speckey_entry =
       fsp_some (MPA.main_spec)); last (rewrite Ht; clear Ht).
      { rewrite lookup_insert_ne // lookup_kmap_Some; exists None; split; ss. }
       eexists _, _; splits.
      { ss; exists tt; split; refl. }
      { iIntros "[$ [$ [$ $]]]"; ss. }
      { unfold_pre_post. iIntros "% % [_ [% _]] //". }
    }
  Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    eapply ctxr_refines.
    rewrite /mod_src /mod_tgt /smod_src !SMod.to_mod_add.

    (* abstraction of Mem *)
    etrans; cycle 1.
    { do 2 ctxr_drop.
      eapply PFMemIA.ctxr.
    }

    (* abstraction of Sch *)
    etrans; cycle 1.
    { ctxr_drop.
      eapply SystemIA.ctxr.
      - apply UserInSp.
      - apply SchInSp.
      - rewrite dom_insert elem_of_union; left; apply elem_of_singleton; ss.
    }

    (* abstraction of MP *)
    etrans; cycle 1.
    { ctxr_norm. eapply MPIA.ctxr.
      - apply SchInSp.
      - apply MainInSp.
    }
    
    eapply ctxr_cond_strengthen.
    { iIntros "[? [? ?]]". iFrame. }
  (*SLOW*)Qed.

  Lemma top_tgt :
    refines
      (mod_top, init_cond ∗ TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤) ∗
        tview_sys_gen 1 1 0 (TView.init []) ∗ TIDAUTH 0 ∗ YIELDAUTH 1)%I
      (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Lemma tgt_wf : Mod.wf mod_tgt.
  Proof.
    rewrite /mod_top ?SMod.cancel_add ?SMod.to_mod_add. eapply Mod.add_wf.
    { econs; eauto.
      rewrite /MPA.Mod /= /MPA.fnsems /Mod.fnsems /= !fmap_insert !fmap_empty; mod_tac ss.
    }
    { econs; eauto.
      { eapply Mod.add_wf.
        { econs; eauto.
          { rewrite /SystemA.Mod /= /SystemA.fnsems /Mod.fnsems /=
              !fmap_insert !fmap_empty; mod_tac ss. }
          { rewrite /= /SystemI.scopes; multiset_solver. }
        }
        { econs; eauto.
          { rewrite /PFMemI.t /= /PFMemI.fnsems /Mod.fnsems /=
              !fmap_insert !fmap_empty; mod_tac ss. }
          { rewrite /= /PFMemI.scopes; multiset_solver. }
        }
        { set_solver. }
        { set_solver. }
      }
      { rewrite /=; i; rewrite multiplicity_disj_union /SystemI.scopes /PFMemI.scopes.
        multiset_solver.
      }
    }
    { rewrite !Mod.dom_fnsems_add; set_solver. }
    { set_solver. }
  Qed.
  Hint Unfold sys_inG subG_sysG : GRA_index.
  Lemma init_cond_valid :
    ∃ rs, ✓ rs ∧ (Own rs ⊢ |==> init_cond ∗ TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤) ∗
        tview_sys_gen 1 1 0 (TView.init []) ∗ TIDAUTH 0 ∗ YIELDAUTH 1).
  Proof.
    exists (irΣ ⋅ ir_own_admin). split.
    - apply irΣ_valid.
    - simplify_res.
      { rewrite make_own_admin.
        iDestruct "H22" as "[H22 Htid]". iFrame.
        iPoseProof (PFMemA.make_init_cond with "[$]") as "[$ ?]".
        rewrite big_sepM_singleton; iFrame.
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
    rewrite IV0.
    rewrite {1}winv_split_empty. iIntros ">[$ [$ [$ [[$ $] $]]]]". done.
  (*SLOW*)Qed.
End MPAll.
