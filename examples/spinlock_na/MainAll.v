Require Import CRIS.
Require Import LockHeader LockI LockA LockIA MainI MainA MainIA.
Require Import ImpPrelude MemI MemA MemIAproof.
Require Import SchHeader SchI SchA SchIAproof.
Require Import Cancel.

(* Cancellation *)
Module MainAll.
  Import inv_instances.

  (* initialization parameters for memory module *)
  Local Definition csl : string → bool := λ _, false.
  Local Definition genv : GEnv.t := GEnv.unit.

  (* HRA & GRA *)
  Local Instance Γ : HRA := ##[invΓ; concΓ; memΓ; newschΓ; spinlockΓ; spinlockmainΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ; newschΣ].

  (* initial resources for HRA & GRA *)
  Definition irΓ : Γ :=
    **[ir_invΓ; ir_concΓ; ir_memΓ csl genv; SchA.ir_schΓ; LockA.ir; MainA.ir].
  Definition irΣ : Σ :=
    **[irΓ; ir_invΣ; SchA.ir_schΣ].

  (* validity lemma for the initial resource irΣ *)
  Lemma irΣ_valid : ✓ (irΣ ⋅ ir_own_admin).
  Proof.
    solve_ir_valid.
    - apply ir_tidRA_valid.
    - apply ir_yieldRA_valid.
    - apply ir_memRA_valid.
    - apply SchA.ir_newtidRA_valid.
    - apply SchA.ir_joinRA_valid.
  Qed.

  (* sp of source module (scheduler spec excluded) *)
  Local Definition sp_user : specmap := MainA.sp ⊤.

  (* the source SMod *)
  Local Definition smod_src : SMod.t := MainA.smod nroot ☆ SchA.smod ⊤ sp_user.
  (* the top-level module after cancellation *)
  Local Definition mod_top : Mod.t := SMod.to_mod ∅ (SMod.cancel smod_src).
  (* the target module *)
  Local Definition mod_tgt : Mod.t := SpinLockMainI.t ★ SpinLockI.t ★ MemI.t csl genv ★ SchI.t .

  (* the source sp *)
  Local Definition sp : specmap := SMod.conc_sp_from smod_src.
  (* the source Mod *)
  Local Definition mod_src : Mod.t := SMod.to_mod sp smod_src.

  (* Local Definition sp_t : specmap := to_sp (SchA.sp nil ⊤). *)
  Lemma mod_top_wf : Mod.wf mod_top.
  Proof.
    rewrite /mod_top SMod.cancel_add SMod.to_mod_add. eapply Mod.add_wf.
    { econs; eauto.
      rewrite /MainA.smod /= /MainA.fnsems !fmap_insert !fmap_empty; mod_tac ss.
    }
    { econs; eauto.
      { rewrite /SchA.smod /= /SchA.fnsems !fmap_insert !fmap_empty; mod_tac ss. }
      { ss; rewrite /SchA.scopes; multiset_solver. }
    }
    { set_solver. }
    { set_solver. }
  Qed.
  (* initial condition for the source *)
  Local Definition init_cond : iProp Σ := (MemA.init_cond csl genv ∗ SchA.init_cond)%I.

  (* Some assumptions on sp inclusion *)
  Lemma SchInSp : (SchA.sp sp_user ⊤) ⊆ sp.
  Proof.
    repeat try eapply insert_subseteq_l; last apply map_empty_subseteq;
      rewrite lookup_insert_ne // lookup_kmap_Some; eexists (Some _); split; ss.
  Qed.

  (* Lemma SchInSp_t : (SchA.sp [] ⊤) ⊆ sp_s.
  Proof.
    rewrite /sp_t /SchA.sp /sp_from /to_sp. unseal CRIS.
    split; first prove_nodup.
    ii; s in H. by repeat (destruct (dec _ _); s in H; [depdes e; depdes H; et|]).
  Qed. *)

  Lemma MainInSp : MainA.sp ⊤ ⊆ sp_user.
  Proof.
    repeat try eapply insert_subseteq_l; last apply map_empty_subseteq. rewrite lookup_insert //.
  Qed.

  Lemma UserInSp : sp_user ⊆ sp.
  Proof.
    repeat try eapply insert_subseteq_l; last apply map_empty_subseteq;
      rewrite lookup_insert_ne // lookup_kmap_Some; eexists (Some _); split; ss.
    rewrite !lookup_omap !lookup_fmap !lookup_omap lookup_union_with /MainA.fnsems /SchA.fnsems;
    simpl_map; ss.
    rewrite nclose_nroot //.
  Qed.

  (* Refinement between smod_cancel and smod_src *)
  Lemma cancel_src :
    refines (mod_top, init_cond ∗ TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤) ∗ TidFrag 0 0 ∗ TIDAUTH 0 ∗ YIELDAUTH 1)%I
            (mod_src, init_cond).
  Proof.
    eapply Cancel.cancellation.
    { apply SMod.cancellable_add; r; rewrite /= /MainA.fnsems /SchA.fnsems; mod_tac ss. }
    { apply mod_top_wf. }
    { assert (Ht : SMod.conc_sp_from smod_src !! speckey_entry =
        fsp_some (fspec_sch (↑nroot) fspec_trivial)); last (rewrite Ht; clear Ht).
      { rewrite lookup_insert_ne // lookup_kmap_Some; exists None; split; ss. }
       eexists _, _; splits.
      { ss; exists (0, 0, tt); split; refl. }
      { rewrite !nclose_nroot. iIntros "[$ [$ [$ $]]]"; ss. }
      { unfold_pre_post. iIntros "% % [_ [_ $]]". }
    }
  Qed.

  (* Refinement between smod_src and mod_tgt *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    apply ctxr_refines.
    rewrite /mod_src /smod_src /mod_tgt /init_cond.

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

    (* abstraction of SpinLock *)
    etrans; cycle 1.
    { do 2 ctxr_drop.
      eapply LockIA.ctxr; cycle 1.
      - apply SchInSp.
      - set_solver.
    }

    (* abstraction of SpinLockMain *)
    etrans; cycle 1.
    { ctxr_drop.
      rewrite -nclose_nroot.
      eapply MainIA.ctxr; rewrite ?nclose_nroot.
      - apply SchInSp.
      - apply SchInSp.
      - apply MainInSp.
    }

    (* elimination of Mem *)
    etrans; cycle 1.
    { do 3 ctxr_drop. eapply CFilter.elim_module. }
    rewrite -mod_add_empty_r.

    (* elimination of SpinLock *)
    etrans; cycle 1.
    { do 2 ctxr_drop. eapply CFilter.elim_module. }
    rewrite -mod_add_empty_r.

    etrans; cycle 1.
    { ctxr_rotate. refl. }

    rewrite /MainA.t /SchA.t. unseal CRIS.
    rewrite SMod.to_mod_add.
    eapply ctxr_cond_strengthen; et.
  (*SLOW*)Qed.

  (* source Mod ⊆ source SMod ⊆ cancelled Mod *)
  Lemma cancel_tgt :
    refines (mod_top, init_cond ∗ TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤) ∗ TidFrag 0 0 ∗ TIDAUTH 0 ∗ YIELDAUTH 1)%I
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
      rewrite /MainA.smod /= /MainA.fnsems !fmap_insert !fmap_empty; mod_tac ss.
    }
    { eapply Mod.add_wf.
      { econs; eauto.
      rewrite /MainA.smod /= /MainA.fnsems !fmap_insert !fmap_empty; mod_tac ss.
      }
      { eapply Mod.add_wf.
        { econs; eauto.
          { rewrite /MainA.smod /= /MainA.fnsems !fmap_insert !fmap_empty; mod_tac ss. }
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

  Lemma init_cond_valid :
    ∃ rs, ✓ rs ∧ (Own rs ⊢ |==> init_cond ∗ TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤) ∗ TidFrag 0 0 ∗ TIDAUTH 0 ∗ YIELDAUTH 1).
  Proof.
    exists (irΣ ⋅ ir_own_admin). split.
    - apply irΣ_valid.
    - simplify_res.
      { rewrite make_own_admin; iFrame.
        iDestruct "H28" as "[H24 Htid]". iFrame.
        rewrite /MemA.init_cond /ir_memRA; iDestruct "H30" as "[$ _]".
        iPoseProof (make_sys_init with "[$] [$]") as "[$ [$ [$ $]]]". done.
      }
    all: solve_res.
  Qed.

  (* tgt Mod ⊆ cancelled Mod *)
  Theorem behavioral_refinement :
    ∃ src_res tgt_res, refines_lmod
      (Mod.to_lmod mod_top src_res)
      (Mod.to_lmod mod_tgt tgt_res).
  Proof.
    move: (cancel_tgt)=>H; rewrite /refines in H; des; ss.
    hexploit H; eauto using tgt_wf. clear H; intros [WF H].
    assert (IV:= init_cond_valid). des.
    destruct (H rs); des; et.
    rewrite IV0 /init_cond {1}winv_split_empty.
    iIntros ">[[$ $] [$ [$ [[? ?] ?]]]]". iFrame. done.
  (*SLOW*)Qed.
End MainAll.
