Require Import CRIS.
Require Import ImpPrelude MemI MemA MemIAproof.
Require Import SpinLockHeader SpinLockI SpinLockA SpinLockIAProof.
Require Import SpinLockMainHeader SpinLockMainI SpinLockMainA.
(* SpinLockMainIAProof. *)
Require Import SchHeader SchI SchA SchIAproof.
Require Import ElimRel SModCancel Cancellation.

(* From iris Require Import frac_auth numbers. *)
Module SpinLockAll.
  Local Existing Instances invG_Σ invG_Γ invG_I invG_E invG_D.

  Instance τ : TypG.t := λ _, ST.t.
  Instance typG : CtxST.t τ. Proof. econs. econs. instantiate (1:=0); ss. Qed.

  Local Instance Γ : HRA := ##[invΓ; memΓ; SchAΓ; SpinLockΓ; SpinLockMainAΓ].
  Local Instance α : SRFCons.t :=
    λ n,
      match n with
      | 0 => SL.syntax
      | _ => inv_syntax
      end.
  Local Instance Σ : GRA := ##[invΣ; SchAΣ; Γ].
  Local Instance sub : subG Γ Σ.
  Proof. do 2 apply subG_app_r. apply subG_refl. Defined.
  Local Instance invG : invG α Σ Γ.
  Proof. econs. { econs. exists 0%fin. ss. } { econs. { exists 0%fin. ss. } { exists 1%fin. ss. } } Defined.
  Instance β : SRFIntp.t :=
    λ n,
      match n with
      | 0 => SL.interp
      | _ => inv_interp
      end.
  Local Instance intpG : SRFIntp.inG (@SL.syntax τ Γ) α (@SL.interp τ α Γ Σ _) β.
  Proof. econs; instantiate (1:=0); ss. Qed.

  Local Instance invintpG : SRFIntp.inG inv_syntax α inv_interp β.
  Proof. econs; instantiate (1:=1); ss. Qed.

  Local Instance sinvg : sinvG Σ Γ α β τ.
  Proof. econs; econs; try typeclasses eauto. Qed.

  Local Instance memΓ : memGΓ Γ.
  Proof. econs. exists 2%fin; ss. Defined.

  Local Instance SchAΓ : SchAGΓ Γ.
  Proof. econs. exists 3%fin; ss. Defined.

  Local Instance SpinLockAGΓ : SpinLockAGΓ Γ.
  Proof. econs. exists 4%fin; ss. Defined.

  Local Instance SpinLockMainAGΓ : SpinLockMainAGΓ Γ.
  Proof. econs. exists 5%fin; ss. Defined.

  Local Instance SchAΣ : SchAGΣ Σ.
  Proof. econs. exists 1%fin; ss. Defined.

  (* building the target module *)
  Local Definition csl : string → bool := λ _, false.
  Local Definition genv : GEnv.t := GEnv.unit.
  Local Definition mod_tgt : HMod.t := SpinLockMainI.t ★ MemI.t csl genv ★ SchI.t ★ SpinLockI.t.

  (* building the source module *)
  Local Definition u : univ_id := 1.

  Local Definition spc_user_s : string → option fspec :=
    to_spc (SpinLockMainAS.spc u ++ MemA.Spc ++ SpinLockAS.spc u).

  Local Definition smod_src : SMod.t :=
    SpinLockMainA.Mod u ☆ MemA.Mod ☆ SchA.Mod u spc_user_s ☆ SpinLockA.Mod u.
  Local Definition spc_s : string → option fspec :=
    spc_from smod_src.
  Local Definition mod_src : HMod.t := SMod.to_hmod (wsim_ginv u ⊤) spc_s smod_src.
  Local Definition init_cond : iProp Σ := (MemA.InitCond csl genv ∗ SchA.InitCond)%I.

  (* source module after cancellation *)
  Local Definition smod_cancel : HMod.t := SModCancel.to_hmod smod_src.

  (* Refinement between smod_cancel and smod_src *)
  Local Definition main_fsp : fspec := SpinLockMainAS.main_spec u.
  Lemma cancel_src :
    refines (smod_cancel, init_cond ∗ main_fsp.(precond) tt tt↑ tt↑)%I
            (mod_src,     init_cond).
  Proof. eapply cancellation; try by econs. i. unfold_pre_post. iIntros "[_ [-> ->]]". done. Qed.

  (* Refinement between smod_src and mod_tgt *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    (* apply ctxr_refines.
    rewrite /mod_src /smod_src /mod_tgt /init_cond ?add_interp_comm.
    replace (SMod.to_hmod _ _ (SpinLockMainA.Mod _)) with (SpinLockMainA.t u spc_s); cycle 1.
    { unfold_hmod; ss. }
    replace (SMod.to_hmod _ _ (MemA.Mod)) with (MemA.t u spc_s); cycle 1.
    { unfold_hmod; ss. }
    replace (SMod.to_hmod _ _ (SpinLockA.Mod _)) with (SpinLockA.t u spc_s); cycle 1.
    { unfold_hmod; ss. }

    etrans.
    { do 2 eapply ctxr_frameL. eapply ctxr_comm. }
    do 2 rewrite -hmod_add_assoc.
    etrans.
    { eapply ctxr_frameR.
      rewrite hmod_add_assoc -hmod_addc_empty_l.
      etrans; first eapply ctxr_cond_frameR.
      { eapply SpinLockMainIA.wctxr; eauto.
        { instantiate (1:=spc_user_s).
          rewrite /spc_user_s /SchAS.spc /spc_s /smod_src; unseal CRIS. split; first prove_nodup.
          ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
        }
        { rewrite /spc_user_s /SchAS.spc /spc_s /smod_src; unseal CRIS. split; first prove_nodup.
          ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
        }
        { rewrite /spc_user_s /MemA.Spc /spc_s /smod_src; unseal CRIS. split; first prove_nodup.
          ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
        }
      }
      rewrite hmod_addc_empty_l. refl.
    }
    rewrite hmod_add_assoc. eapply ctxr_frameL.
    etrans.
    { eapply ctxr_frameR. rewrite -hmod_addc_empty_l. eapply ctxr_cond_frameR.
      etrans; first eapply ctxr_comm.
      eapply SpinLockIA.wctxr.
      { rewrite /spc_user_s /SchAS.spc /spc_s /smod_src; unseal CRIS. split; first prove_nodup.
        ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
      }
      { rewrite /spc_user_s /spc_s /smod_src /MemA.Spc; unseal CRIS. split; first prove_nodup.
        ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
      }
    }
    rewrite hmod_add_assoc.
    etrans; first eapply ctxr_comm. rewrite -hmod_add_assoc. eapply ctxr_frameR.
    etrans.
    { rewrite hmod_addc_empty_l. eapply ctxr_frameR, ctxr_cond_frameR. eapply MemIA.wctxr.
      rewrite /MemA.Spc; unseal CRIS.
      split; first prove_nodup. ii; ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
    }
    eapply ctxr_frameL.
    etrans.
    { replace (SMod.to_hmod _ _ (SchA.Mod _ _)) with (SchA.t u spc_s spc_user_s); cycle 1.
      { unfold_hmod; ss. }
      rewrite hmod_addc_empty_l.
      eapply SchIA.wctxr.
      { rewrite /spc_user_s /SchAS.spc /spc_s /smod_src; unseal CRIS. split; first prove_nodup.
        ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
      }
      { rewrite /spc_user_s /SchAS.spc /spc_s /smod_src /MemA.Spc; unseal CRIS.
        ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
      }
    }
    refl. *)
  Admitted.

  Lemma cancel_tgt :
    refines (smod_cancel, (init_cond ∗ (main_fsp).(precond) tt tt↑ tt↑)%I)
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Import rListNotations.
  Local Definition initial_resource_list : res_list :=
    [ownIRA_resource u; ownERA_resource u; ownDRA_resource u;
     SchAS.tidRA_resource; SchAS.threadsRA_resource; memRA_resource csl genv]%res_list.

  Local Definition initial_resource : Σ := 
    (op_res_list initial_resource_list) ⋅ initial_resource_own_admin.

  Ltac dfs_solve :=
    econs; [repeat (intros [C | C]; [inv C|]; revert C); intros []|].
    
  Lemma initial_resource_valid : ✓ initial_resource.
  Proof.
    apply op_res_list_valid.
    repeat dfs_solve. econs.
  Qed.

  Theorem behavioral_refinement :
    ∃ target_resource, refines_mod
      (HMod.to_mod smod_cancel initial_resource)
      (HMod.to_mod mod_tgt target_resource).
  Proof.
    move: (cancel_tgt)=>H; rewrite /refines in H; ss.
    destruct (H initial_resource).
    { apply initial_resource_valid. }
    { iIntros "H". iPoseProof (big_bang with "H") as "[O H]".
      iDestruct "H" as "[H1 [H2 [H3 [H4 [H5 [H6 _]]]]]]"; iFrame.
      iPoseProof (ownI_initial_gen with "[$]") as "[U W]".
      iPoseProof (SchAS.tid_admin_none_split with "[H4]") as "[H3 H4]".
      { rewrite /SchAS.tid_admin; unseal "SchA"; ss. }
      iFrame. des_ifs. unfold_pre_post. iSplitL.
      { iSplitR "H5".
        { iDestruct "H6" as "[$ $]". }
        { rewrite /SchAS.initial_threads. unseal "SchA". done. }
      }
      iSplit; eauto.
    }
    { econs; ss; prove_nodup. }
    { exists x; des; eauto. }
  Qed.
End SpinLockAll.

Module SpinLockAllFail.
  Import inv_instances.
  (* Local Instance Γ : HRA := ##[invΓ; memΓ; SchAΓ; SpinLockΓ; SpinLockMainAΓ].
  Local Instance Σ : GRA := ##[invΣ; SchAΣ; Γ]. *)

  (* building the target module *)
  (* Local Definition csl : string → bool := λ _, false.
  Local Definition genv : GEnv.t := GEnv.unit.
  Local Definition mod_tgt : HMod.t := SpinLockMainI.t ★ MemI.t csl genv ★ SchI.t ★ SpinLockI.t.

  (* building the source module *)
  Local Definition u : univ_id := 1.

  Local Definition spc_user_s : string → option fspec :=
    to_spc (SpinLockMainAS.spc u ++ MemA.Spc ++ SpinLockAS.spc u).

  Local Definition smod_src : SMod.t :=
    SpinLockMainA.Mod u ☆ MemA.Mod ☆ SchA.Mod u spc_user_s ☆ SpinLockA.Mod u.
  Local Definition spc_s : string → option fspec :=
    spc_from smod_src.
  Local Definition mod_src : HMod.t := SMod.to_hmod (wsim_ginv u ⊤) spc_s smod_src.
  Local Definition init_cond : iProp Σ := (MemA.InitCond csl genv ∗ SchA.InitCond)%I.

  (* source module after cancellation *)
  Local Definition smod_cancel : HMod.t := SModCancel.to_hmod smod_src.

  (* Refinement between smod_cancel and smod_src *)
  Local Definition main_fsp : fspec := SpinLockMainAS.main_spec u.
  Lemma cancel_src :
    refines (smod_cancel, init_cond ∗ main_fsp.(precond) tt tt↑ tt↑)%I
            (mod_src,     init_cond).
  Proof. eapply cancellation; try by econs. i. unfold_pre_post. iIntros "[_ [-> ->]]". done. Qed.

  (* Refinement between smod_src and mod_tgt *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    (* apply ctxr_refines.
    rewrite /mod_src /smod_src /mod_tgt /init_cond ?add_interp_comm.
    etrans.
    { do 2 eapply ctxr_frameL. eapply ctxr_comm. }
    do 2 rewrite -hmod_add_assoc.
    etrans.
    { eapply ctxr_frameR.
      replace (SMod.to_hmod _ _ (SpinLockMainA.Mod _)) with (SpinLockMainA.t u spc_s); cycle 1.
      { unfold_hmod; ss. }
      replace (SMod.to_hmod _ _ (MemA.Mod)) with (MemA.t u spc_s); cycle 1.
      { unfold_hmod; ss. }
      replace (SMod.to_hmod _ _ (SpinLockA.Mod _)) with (SpinLockA.t u spc_s); cycle 1.
      { unfold_hmod; ss. }
      rewrite hmod_add_assoc -hmod_addc_empty_l.
      etrans; first eapply ctxr_cond_frameR.
      { eapply SpinLockMainIA.wctxr; eauto.
        { instantiate (1:=spc_user_s).
          rewrite /spc_user_s /SchAS.spc /spc_s /smod_src; unseal CRIS. split; first prove_nodup.
          ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
        }
        { rewrite /spc_user_s /SchAS.spc /spc_s /smod_src; unseal CRIS. split; first prove_nodup.
          ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
        }
        { rewrite /spc_user_s /MemA.Spc /spc_s /smod_src; unseal CRIS. split; first prove_nodup.
          ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
        }
      }
      rewrite hmod_addc_empty_l. refl.
    }
    rewrite hmod_add_assoc. eapply ctxr_frameL.
    etrans.
    { eapply ctxr_frameR. rewrite -hmod_addc_empty_l. eapply ctxr_cond_frameR.
      etrans; first eapply ctxr_comm.
      eapply SpinLockIA.wctxr.
      { rewrite /spc_user_s /SchAS.spc /spc_s /smod_src; unseal CRIS. split; first prove_nodup.
        ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
      }
      { rewrite /spc_user_s /spc_s /smod_src /MemA.Spc; unseal CRIS. split; first prove_nodup.
        ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
      }
    }
    rewrite hmod_add_assoc.
    etrans; first eapply ctxr_comm. rewrite -hmod_add_assoc. eapply ctxr_frameR.
    etrans.
    { rewrite hmod_addc_empty_l. eapply ctxr_frameR, ctxr_cond_frameR. eapply MemIA.wctxr.
      rewrite /MemA.Spc; unseal CRIS.
      split; first prove_nodup. ii; ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
    }
    eapply ctxr_frameL.
    etrans.
    { replace (SMod.to_hmod _ _ (SchA.Mod _ _)) with (SchA.t u spc_s spc_user_s); cycle 1.
      { unfold_hmod; ss. }
      rewrite hmod_addc_empty_l.
      eapply SchIA.wctxr.
      { rewrite /spc_user_s /SchAS.spc /spc_s /smod_src; unseal CRIS. split; first prove_nodup.
        ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
      }
      { rewrite /spc_user_s /SchAS.spc /spc_s /smod_src /MemA.Spc; unseal CRIS.
        ii. ss; des_ifs; rewrite ->eq_rel_dec_correct in *; des_ifs.
      }
    }
    refl. *)
  Admitted.

  Lemma cancel_tgt :
    refines (smod_cancel, (init_cond ∗ (main_fsp).(precond) tt tt↑ tt↑)%I)
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Import rListNotations.
  Local Definition initial_resource_list : res_list :=
    [ownIRA_resource u; ownERA_resource u; ownDRA_resource u; SchAS.tidRA_resource; SchAS.threadsRA_resource]%res_list.
  (* discrete_fun_singleton γ .. ⋅ discrete_fun_singleton γ1 .. *)
  Local Definition initial_resource : Σ := 
    (op_res_list initial_resource_list) ⋅ initial_resource_own_admin.

  Ltac solve_eq_index :=
    match goal with
    | H : eq_index ?r ?r2 |- _ => revert H; autounfold with GRA_index; intros H; rewrite /eq_index in H
    end; des_ifs;
    match goal with
    | H1 : @eq (inG _ _) ?a _, H2 : @eq (inG _ _) ?b _ |- _ =>
        let H := fresh "H" in assert (H : inG_id a = inG_id b) by rewrite H1 H2 //=;
        repeat match goal with
        | H : inG_id ?a = inG_id ?b |- _ => rewrite /a /b in H
        end;
        (* rewrite /a /b in H *)
        revert H; autounfold with GRA_index; inv_instances.solve_in_subG_goal;
        rewrite /eq_rec_r /eq_rec /= /subG_inG -!eq_rect_eq //=
    end.
  Ltac solve_nin_aux :=
    match goal with
    | H : r_In ?RES (r_cons ?RA ?RES' ?tl) |- _ => destruct H as [EQ | IN]; [solve_eq_index| solve_nin_aux]
    | H : r_In ?RES (r_nil) |- _ => inv H
    end.
  Ltac solve_nin := ii; solve_nin_aux.
  Ltac dfs_solve :=
    match goal with
    | |- r_NoDup (r_cons ?RA ?RES ?tl) => econs; [solve_nin|dfs_solve]
    | |- r_NoDup (r_nil) => econs
    end.
  Hint Unfold sProp.in_subG_obligation_1 in_subG subG_invΣ subG_invΓ invG_subG invΓ invΣ invG_Σ invG_Γ invG_D invG_E invG_I SchAΣ : GRA_index.
  Hint Unfold ownIRA_resource ownERA_resource ownDRA_resource SchAS.tidRA_resource SchAS.threadsRA_resource : GRA_index. *)

  Definition resource : Type := {A : DRA & {a : A | ✓ a}}.
  Inductive res_list : Type :=
  | r_nil : res_list
  | r_cons (a : resource) (l : res_list) : res_list.

  Definition fin_split n1 : ∀ n2 (i : fin (n1 + n2)), fin n1 + fin n2.
  Proof.
    induction n1 as [|n1'].
    { intros n2 i. exact (inr i). }
    { intros n2 i. inv i.
       (* change (S n1' + n2) as (S (n1' + n2))   remember  *)
      { exact (inl Fin.F1). }
      { specialize (IHn1' _ H0). destruct IHn1'.
        { left. exact (FS t). }
        { right. exact t. }
      }
    }
  Defined.

  From iris Require Import csum.
  Module GRAs.
    (* Program Definition cons (A : DRA) (Σ : GRA) : GRA :=
      GRA_mk (S (@GRA_len Σ)) (fin_S_inv _ A (@GRA_lookup Σ)). *)

    (* Definition cons_res {A : DRA} {Σ : GRA} (a : A) (r : Σ) : cons A Σ.
    Proof.
      destruct Σ. intros i γ. depdes i.
      { destruct (decide (γ = base_γ)).
        { exact (Some (Cinr a)). }
        { refine (Some (Cinl (Excl ()))). }
      }
      { exact (r i γ). }
    Defined. *)

    Definition singleton_res {A : DRA} (a : A) : GRAs.singleton A.
    Proof. Admitted.

    Definition app_res {Σ1 Σ2 : GRA} (r1 : Σ1) (r2 : Σ2) : GRAs.app Σ1 Σ2.
    Proof.
      intros i. eapply fin_add_inv with (i:=i).
      { intros i1. specialize (r1 i1). simpl in r1. admit. }
    Admitted.

    Lemma singleton_res_valid {A : DRA} (a : A)
        (VALID : ✓ a) :
      ✓ singleton_res a.
    Proof. Admitted.

    Definition app_res_valid {Σ1 Σ2 : GRA} (r1 : Σ1) (r2 : Σ2)
        (VALID1 : ✓ r1)
        (VALID2 : ✓ r2) :
      ✓ app_res r1 r2.
    Proof. Admitted.
  End GRAs.

  (* Fixpoint op_res_list (l : res_list) : {Σ : GRA & Σ} :=
    match l with
    | r_nil => existT GRAs.nil ε
    | r_cons (existT A (exist _ a _)) tl => 
      let '(existT Σ_tl r_tl) := op_res_list tl in
        existT (GRAs.cons A Σ_tl) (GRAs.cons_res a r_tl)
    end. *)

  Local Instance Γ : HRA := ##[invΓ].
  (* 
  Definition app_res_list (l1 l2 : res_list) : {Σ : GRA & Σ}

  Lemma op_res_list_valid (l : res_list) :
    let '(existT Σ r) := op_res_list l in
    ✓ (r ⋅ (@initial_resource_own_admin Σ)).
  Proof.
  Admitted. *)
  Local Instance Σ : GRA := ##[invΣ; Γ].

  Definition ownIRA_resource u : DRA_mk ownIRA :=
    ownI_initial u.
  Lemma ownIRA_resource_valid u : ✓ (ownIRA_resource u). apply ownI_initial_valid. Qed.

  Definition ownDRA_resource u : DRA_mk ownDRA :=
    ownD_initial u.
  Lemma ownDRA_resource_valid u : ✓ (ownDRA_resource u). apply ownD_initial_valid. Qed.

  Definition ownERA_resource u : DRA_mk ownERA :=
    ownE_initial u.
  Lemma ownERA_resource_valid u : ✓ (ownERA_resource u). apply ownE_initial_valid. Qed.

  Definition initial_resource' : Σ :=
    GRAs.app_res
      (GRAs.app_res
        (GRAs.singleton_res (ownIRA_resource 1))
        (ε : GRAs.nil))
      (GRAs.app_res
        (GRAs.app_res
          (GRAs.app_res
            (GRAs.singleton_res (ownERA_resource 1))
            (GRAs.app_res
              (GRAs.singleton_res (ownDRA_resource 1))
              (ε : GRAs.nil)))
          (ε : GRAs.nil))
        (ε : GRAs.nil)).
  (* Check (initial_resource' : Σ'). *)

    (* GRAs.app
      (GRAs.app
        (IRA)
        GRAs.nil)
      (GRAs.app
        (GRAs.app
          (GRAs.app
            (ERA)
            (GRAs.app
              (DRA)
              GRAs.nil))
          GRAs.nil)
        GRAs.nil) *)
  
  (* Check initial_resource'. *)

  (* Goal Σ' =##[ ##[ {|
    DRA_RA := @ownIRA (@α Γ);
    DRA_discrete :=
      @discrete_funR_cmra_discrete univ_id
        (λ _ : univ_id, @discrete_funUR level (@InvSetRA (@α Γ)))
        (λ _ : univ_id,
           @discrete_funR_cmra_discrete level 
             (@InvSetRA (@α Γ))
             (λ i0 : level,
                @gmap_view.gmap_view_cmra_discrete positive
                  Pos.eq_dec pos_countable
                  (agreeR (@SynO (@α Γ) i0))
                  (@agree_cmra_discrete 
                     (@SynO (@α Γ) i0)
                     (@discrete_ofe_discrete
                        (@SRFSyn.t (@α Γ) i0)
                        (@equivL (@SRFSyn.t (@α Γ) i0))
                        (@eq_equivalence (@SRFSyn.t (@α Γ) i0))))))
  |}];
##[ ##[ {|
    DRA_RA := ownERA;
    DRA_discrete :=
      @discrete_funR_cmra_discrete univ_id
        (λ _ : univ_id, coPset.coPset_disjUR)
        (λ _ : univ_id, coPset.coPset_disj_cmra_discrete)
  |};
{|
DRA_RA := ownDRA;
DRA_discrete :=
  @discrete_funR_cmra_discrete univ_id
    (λ _ : univ_id,
       authUR
         (@gset.gset_disjUR positive Pos.eq_dec pos_countable))
    (λ _ : univ_id,
       @auth_cmra_discrete
         (@gset.gset_disjUR positive Pos.eq_dec pos_countable)
         (@gset.gset_disj_cmra_discrete positive Pos.eq_dec
            pos_countable))
|}]]].
           (* refl. *)
    (* rewrite /Σ' /invΣ /Γ' /invΓ. *)
  f_equal.
  rewrite /invΣ.
  f_equal. Set Printing All. refl.
    (* existT (DRA_mk ownIRA) (exist _ (ownI_initial u) (ownI_initial_valid u)). *)
  Definition ownERA_resource u : resource :=
    existT (DRA_mk ownERA) (exist _ (ownE_initial u) (ownE_initial_valid u)).
  Definition ownDRA_resource u : resource :=
    existT (DRA_mk ownDRA) (exist _ (ownD_initial u) (ownD_initial_valid u)).

  Local Definition initial_resource_list' : res_list :=
    r_cons (ownIRA_resource u) (r_cons (ownERA_resource u) (r_cons (ownDRA_resource u) r_nil)).


  Check projT2 (op_res_list initial_resource_list') : Σ'.
  
  Local Instance Γ : HRA := ##[invΓ; memΓ; SchAΓ; SpinLockΓ; SpinLockMainAΓ].
  Local Instance Σ : GRA := ##[invΣ; SchAΣ; Γ].

  Definition threadsRA_resource : resource :=
    existT (DRA_mk trhead) (exist _ (ownD_initial u) (ownD_initial_valid u)).

  Proof.
  Local Definition initial_resource_list' : res_list :=
    r_cons (ownIRA_resource u) r_nil.
    [ownIRA_resource u; ownERA_resource u; ownDRA_resource u; SchAS.tidRA_resource; SchAS.threadsRA_resource]%res_list.
  (* discrete_fun_singleton γ .. ⋅ discrete_fun_singleton γ1 .. *)
  Local Definition initial_resource : Σ := 
    (op_res_list initial_resource_list) ⋅ initial_resource_own_admin. *)
  Theorem behavioral_refinement :
    ∃ target_resource, refines_mod
      (HMod.to_mod smod_cancel initial_resource)
      (HMod.to_mod mod_tgt target_resource).
  Proof.
    move: (cancel_tgt)=>H; rewrite /refines in H; ss.
    destruct (H initial_resource).
    { apply op_res_list_valid. rewrite /initial_resource_list.
      econs.
      { ii. destruct H0.
        { rewrite /eq_index /ownIRA_resource /ownERA_resource in H0.
          des_ifs.
          match goal with
          | H1 : @eq (inG _ _) ?a _, H2 : @eq (inG _ _) ?b _ |- _ =>
              let H := fresh "H" in assert (H : inG_id a = inG_id b) by rewrite H1 H2 //=;
              repeat match goal with
              | H : inG_id ?a = inG_id ?b |- _ => rewrite /a /b in H
              end;
              (* rewrite /a /b in H *)
              revert H; autounfold with GRA_index; inv_instances.solve_in_subG_goal;
              rewrite /eq_rec_r /eq_rec /= /subG_inG -!eq_rect_eq //=
          end.
        }
    
    Σ := (A, Some a) :: (B, Some b) :: ... :: nil
    Σ := [A; B; C; ..]
          vm_compute invariants.ownIRA_resource_obligation_1 in Heq.

           } }
    dfs_solve. }
    { iIntros "H". iPoseProof (big_bang with "H") as "[O H]".
      iPoseProof (ownI_initial_gen with "[H]") as "[U W]".
      { rewrite /initial_resource_list; s. des_ifs. rename inG_id into i.
        assert (H' : inG_id invariants.ownIRA_resource_obligation_1 = i).
        { rewrite Heq; ss. }
        revert H'. rewrite /invariants.ownIRA_resource_obligation_1 /invG_I. autounfold with GRA_index.
        rewrite inG_id_subG_inG subG_app_l_inG_id /eq_rec_r /eq_rec -eq_rect_eq.
        intros H'; ss.
        iDestruct "H" as "[H1 [H2 [H3 _]]]"; iFrame.
        eapply eq_ind; first iExact "H1".
        f_equiv. ss.
      }
      iFrame. unfold_pre_post. iSplitL.
      { rewrite /init_cond. admit. }
      admit.
    }
    { econs; ss; prove_nodup. }
    { exists x; des; eauto. }
     
  Admitted.