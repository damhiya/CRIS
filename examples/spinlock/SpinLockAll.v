Require Import CRIS.
Require Import ImpPrelude MemI MemA MemIAproof.
Require Import SpinLockHeader SpinLockI SpinLockA SpinLockIAProof.
Require Import SpinLockMainHeader SpinLockMainI SpinLockMainA SpinLockMainIAProof.
Require Import SchHeader SchI SchA SchIAproof.
Require Import ElimRel SModCancel Cancellation.

Ltac gen_eq a :=
  match a with context [?t] =>
    lazymatch t with
    | eq_refl => fail
    | _ =>
      let T := type of t in
      match (eval simpl in T) with
      | _ = _ => generalize t
      end
    end
  end.

Ltac gen_prop a :=
  match a with context [?t] =>
    let T := type of t in
    match (eval simpl in T) with
    | Prop => generalize t
    end
  end.

Ltac remove_eq_aux :=
  let e := fresh "E" in
  intros e;
  match goal with
  | H : @eq ?A ?b _ |- _ => replace H with (@eq_refl A b)
  end; last apply UIP; clear e.

Ltac remove_eq a := gen_eq a; remove_eq_aux.

From iris Require Import csum.

Module InitRes.
  Definition nil : GRAs.nil.
  Proof. intros i; inv i. Defined.

  Definition singleton {A : DRA} (a : option A) : GRAs.singleton A.
  Proof.
    intros i γ. inv_fin i.
    { destruct (decide (γ = base_γ)).
      { destruct a as [a|].
        { ss. exact (Some (Cinr a)). }
        { ss. exact (Some (Cinl (Excl ()))). }
      }
      { exact None. }
    }
    { intros i. inv i. }
  Defined.

  Definition R_prf {Σ1 Σ2 : GRA} (i2 : gid Σ2) :
    @eq cmra
    (allocs.allocsUR positive (@GRA_lookup Σ2 i2))
    (allocs.allocsUR positive (@GRA_lookup (GRAs.app Σ1 Σ2) (Fin.R (@GRA_len Σ1) i2))).
  Proof. rewrite /GRAs.app /= fin_add_inv_r; refl. Qed.

  Definition L_prf {Σ1 Σ2 : GRA} (i1 : gid Σ1) :
    @eq cmra
    (allocs.allocsUR positive (@GRA_lookup Σ1 i1))
    (allocs.allocsUR positive (@GRA_lookup (GRAs.app Σ1 Σ2) (Fin.L (@GRA_len Σ2) i1))).
  Proof. rewrite /GRAs.app /= fin_add_inv_l; refl. Qed.

  Definition R {Σ1 Σ2 : GRA} (r2 : Σ2) : GRAs.app Σ1 Σ2.
  Proof.
    intros i. eapply fin_add_inv with (i:=i).
    { intros i1 g. exact ε. }
    { intros i2. refine (cmra_transport (R_prf i2) (r2 i2)). }
  Defined.

  Definition L {Σ1 Σ2 : GRA} (r1 : Σ1) : GRAs.app Σ1 Σ2.
  Proof.
    intros i. eapply fin_add_inv with (i:=i).
    { intros i1. refine (cmra_transport (L_prf i1) (r1 i1)). }
    { intros i2 g. exact ε. }
  Defined.

  Lemma R_distr {Σ1 Σ2 : GRA} (r1 r2 : Σ2) : @R Σ1 Σ2 (r1 ⋅ r2) = @R Σ1 Σ2 r1 ⋅ @R Σ1 Σ2 r2.
  Proof.
    extensionalities i; apply fin_add_inv with (i:=i); clear i.
    { intros i1; rewrite /R ?discrete_fun_lookup_op ?fin_add_inv_l //. }
    { intros i2. rewrite /R discrete_fun_lookup_op fin_add_inv_r.
      rewrite !fin_add_inv_r cmra_transport_op //.
    }
  Qed.

  Lemma L_distr {Σ1 Σ2 : GRA} (r1 r2 : Σ1) : @L Σ1 Σ2 (r1 ⋅ r2) = @L Σ1 Σ2 r1 ⋅ @L Σ1 Σ2 r2.
  Proof.
    extensionalities i; apply fin_add_inv with (i:=i); clear i.
    { intros i1. rewrite /L discrete_fun_lookup_op fin_add_inv_l.
      rewrite !fin_add_inv_l cmra_transport_op //.
    }
    { intros i2; rewrite /L ?discrete_fun_lookup_op ?fin_add_inv_r //. }
  Qed.

  Definition app {Σ1 Σ2 : GRA} (r1 : Σ1) (r2 : Σ2) : GRAs.app Σ1 Σ2 :=
    @L Σ1 Σ2 r1 ⋅ @R Σ1 Σ2 r2.

  Lemma singleton_some_valid {A : DRA} (a : A)
      (VALID : ✓ a) :
    ✓ (singleton (Some a) ⋅ initial_resource_own_admin).
  Proof.
    intros i γ. inv_fin i; ss; des_ifs.
    { rewrite ?discrete_fun_lookup_op /singleton /initial_resource_own_admin.
      des_ifs. ss. rewrite left_id /allocs.allocs_auth; des_ifs; ss.
    }
    { intros i; inv i. }
  Qed.

  Lemma singleton_none_valid {A : DRA} :
    ✓ (@singleton A None ⋅ initial_resource_own_admin).
  Proof.
    intros i γ. inv_fin i; ss; des_ifs.
    { rewrite ?discrete_fun_lookup_op /singleton /initial_resource_own_admin.
      des_ifs; ss; rewrite left_id /allocs.allocs_auth; des_ifs.
    }
    { intros i; inv i. }
  Qed.

  Definition app_valid {Σ1 Σ2 : GRA} (r1 : Σ1) (r2 : Σ2)
      (VALID1 : ✓ (r1 ⋅ initial_resource_own_admin))
      (VALID2 : ✓ (r2 ⋅ initial_resource_own_admin)) :
    ✓ (app r1 r2 ⋅ initial_resource_own_admin).
  Proof.
    intros i; apply fin_add_inv with (i:=i).
    { intros i1. rewrite /app ?discrete_fun_lookup_op.
      rewrite /L fin_add_inv_l /R fin_add_inv_l right_id.
      rewrite /initial_resource_own_admin.
      match goal with | |- ?A => gen_eq A end.
      rewrite /GRAs.app /= fin_add_inv_l. remove_eq_aux. ss.
    }
    { intros i2. rewrite /app ?discrete_fun_lookup_op.
      rewrite /L fin_add_inv_r /R fin_add_inv_r left_id.
      rewrite /initial_resource_own_admin.
      match goal with | |- ?A => gen_eq A end.
      rewrite /GRAs.app /= fin_add_inv_r. remove_eq_aux. ss.
    }
  Qed.

  Lemma singleton_index {A : DRA} (a : A) :
    singleton (Some a) = discrete_fun_singleton 0%fin (allocs.allocs_frag base_γ a).
  Proof.
    extensionalities i g. inv_fin i; ss; des_ifs.
    { rewrite ?discrete_fun_lookup_singleton //=. }
    { rewrite discrete_fun_lookup_singleton /= /allocs.allocs_frag discrete_fun_lookup_singleton_ne //. }
    { intros i; inv i. }
  Qed.

  Lemma L_index {Σ1 Σ2 : GRA} (i : fin (@GRA_len Σ1)) r :
    @L Σ1 Σ2 (discrete_fun_singleton i r)
    = discrete_fun_singleton (Fin.L (@GRA_len Σ2) i) (cmra_transport (@L_prf Σ1 Σ2 i) r).
  Proof.
    rewrite /L. extensionalities i1.
    apply fin_add_inv with (i:=i1); cycle 1.
    { intros i2; ss.
      match goal with | |- fin_add_inv ?P ?H1 ?H2 ?r = _ => rewrite (fin_add_inv_r P H1 H2 _) end.
      rewrite discrete_fun_lookup_singleton_ne; ss.
      ii. eapply Fin.L_R_neq; eauto.
    }
    { intros i2; ss.
      destruct (decide (i = i2)).
      { subst.
        match goal with | |- fin_add_inv ?P ?H1 ?H2 ?r = _ => rewrite (fin_add_inv_l P H1 H2 _) end.
        rewrite ?discrete_fun_lookup_singleton //.
      }
      { match goal with | |- fin_add_inv ?P ?H1 ?H2 ?r = _ => rewrite (fin_add_inv_l P H1 H2 _) end.
        rewrite ?discrete_fun_lookup_singleton_ne //.
        { match goal with | |- ?a => gen_eq a end.
          rewrite /GRAs.app /= fin_add_inv_l. remove_eq_aux. ss.
        }
        { ii. apply Fin.L_inj in H. ss. }
      }
    }
  Qed.

  Lemma R_index {Σ1 Σ2 : GRA} (i : fin (@GRA_len Σ2)) r :
    @R Σ1 Σ2 (discrete_fun_singleton i r)
    = discrete_fun_singleton (Fin.R (@GRA_len Σ1) i) (cmra_transport (@R_prf Σ1 Σ2 i) r).
  Proof.
    rewrite /R. extensionalities i1.
    apply fin_add_inv with (i:=i1); cycle 1.
    { intros i2; ss.
      match goal with | |- fin_add_inv ?P ?H1 ?H2 ?r = _ => rewrite (fin_add_inv_r P H1 H2 _) end.
      destruct (decide (i = i2)).
      { subst. rewrite ?discrete_fun_lookup_singleton //.
      }
      { rewrite ?discrete_fun_lookup_singleton_ne //.
        { match goal with | |- ?a => gen_eq a end.
          rewrite /GRAs.app /= fin_add_inv_r. remove_eq_aux. ss.
        }
        { ii. apply Fin.R_inj in H. ss. }
      }
    }
    { intros i2; ss.
      match goal with | |- fin_add_inv ?P ?H1 ?H2 ?r = _ => rewrite (fin_add_inv_l P H1 H2 _) end.
      rewrite discrete_fun_lookup_singleton_ne; ss.
      ii. eapply Fin.L_R_neq; eauto.
    }
  Qed.
End InitRes.
Notation "*[ ]" := InitRes.nil (format "*[ ]").
Notation "*[ Σ1 ; .. ; Σn ]" :=
  (InitRes.app (InitRes.singleton Σ1) .. (InitRes.app (InitRes.singleton Σn) InitRes.nil) ..).
Notation "**[ Σ1 ; .. ; Σn ]" := (InitRes.app Σ1 .. (InitRes.app Σn InitRes.nil) ..).

Ltac unfold_own :=
  match goal with
  | |- Own ?R = own base_γ ?R2 =>
    rewrite own.Own_eq /own.Own_def own.own_eq /own.own_def /own.iRes_singleton; f_equal
  end.

Ltac unfold_left :=
  repeat match goal with
  | |- context [InitRes.singleton _] => rewrite InitRes.singleton_index
  | |- context [InitRes.L (discrete_fun_singleton _ _)] => rewrite ?InitRes.L_index
  | |- context [InitRes.R (discrete_fun_singleton _ _)] => rewrite ?InitRes.R_index
  end.

Hint Unfold invG_I invG_Σ invG_subG subG_invΣ subG_inG : GRA_index.
Hint Unfold sProp.in_subG_obligation_1 in_subG invG_E invG_Γ subG_invΓ invG_D : GRA_index.

Ltac solve_index H := 
  eapply eq_ind; first iExact H;
  unfold_own;
  etrans;
  [unfold_left; repeat match goal with | |- ?a = _ => remove_eq a end; simpl; refl
  | etrans; cycle 1;
    [ symmetry;
      let k := fresh "k" in
      match goal with
      | |- context [inG_id ?i] => pattern i; match goal with | |- ?f ?a => set (k:=f) end
      end;
      autounfold with GRA_index
      ; subst k
      ; simpl
      ; hrepeat do 1 match goal with | |- ?a = _ => remove_eq a end
      ; simpl
    | refl
    ]
  ].

Lemma ir_own_admin {Σ : GRA} : Own initial_resource_own_admin ⊢ own_admin.
Proof.
  rewrite own.own_admin_eq /own.own_admin_def.
  iIntros "H". iExists (⊤ ∖ {[base_γ]}).
  iSplit.
  { iPureIntro. eapply difference_infinite, singleton_finite. eapply top_infinite. }
  { rewrite /initial_resource_own_admin own.Own_eq /own.Own_def. iFrame. }
Qed.

Module SpinLockAll.
  Import inv_instances.
  Local Definition u : univ_id := 1.

  Local Definition csl : string → bool := λ _, false.
  Local Definition genv : GEnv.t := GEnv.unit.

  Local Instance Γ : HRA := ##[invΓ; memΓ; SchAΓ; SpinLockΓ; SpinLockMainAΓ].

  Definition IRownIRA : DRA_mk ownIRA :=
    ownI_initial u.
  Lemma IRownIRA_valid : ✓ (IRownIRA). eapply (ownI_initial_valid u). Qed.

  Local Instance Σ : GRA := ##[invΣ; SchAΣ; Γ].

  Definition IRownDRA : DRA_mk ownDRA :=
    ownD_initial u.
  Lemma IRownDRA_valid : ✓ (IRownDRA). eapply ownD_initial_valid. Qed.

  Definition IRownERA : DRA_mk ownERA :=
    ownE_initial u.
  Lemma IRownERA_valid : ✓ (IRownERA). eapply ownE_initial_valid. Qed.

  Definition IRmemRA : DRA_mk memRA :=
    mem_initial_mem_r csl genv.
  Lemma IRmemRA_valid : ✓ (IRmemRA).
  Proof. pose proof (mem_initial_valid csl genv). rewrite /IRmemRA. eapply cmra_valid_op_l; eauto. Qed.

  Definition IRthreadsRA : DRA_mk threadsRA :=
    SchAS.threadsRA_initial.
  Lemma IRthreadsRA_valid : ✓ (IRthreadsRA). apply SchAS.threadsRA_initial_valid. Qed.

  Definition IRtidRA : DRA_mk tidRA :=
    SchAS.tidRA_initial.
  Lemma IRtidRA_valid : ✓ (IRtidRA). apply SchAS.tidRA_initial_valid. Qed.

  Definition IRinvΓ : invΓ :=
    *[Some (IRownERA); Some (IRownDRA)].
  Definition IRmemΓ : memΓ :=
    *[Some IRmemRA].
  Definition IRSchAΓ : SchAΓ :=
    *[Some IRtidRA].

  Definition IRΓ : Γ :=
    **[IRinvΓ; IRmemΓ; IRSchAΓ; *[None]; *[None]].

  Definition IRΣ : Σ :=
    **[*[Some (IRownIRA)]; *[Some IRthreadsRA]; IRΓ].

  Lemma IRΣ_valid : ✓ (IRΣ ⋅ initial_resource_own_admin).
  Proof.
    eapply InitRes.app_valid.
    { apply InitRes.app_valid.
      { apply InitRes.singleton_some_valid, IRownIRA_valid. }
      { intros i; inv_fin i. }
    }
    apply InitRes.app_valid.
    { apply InitRes.app_valid.
      { apply InitRes.singleton_some_valid, IRthreadsRA_valid. }
      { intros i; inv_fin i. }
    }
    apply InitRes.app_valid.
    { apply InitRes.app_valid.
      { apply InitRes.app_valid.
        { apply InitRes.singleton_some_valid, IRownERA_valid. }
        { apply InitRes.app_valid.
          { apply InitRes.singleton_some_valid, IRownDRA_valid. }
          { intros i; inv_fin i. }
        }
      }
      apply InitRes.app_valid.
      { apply InitRes.app_valid.
        { apply InitRes.singleton_some_valid, IRmemRA_valid. }
        { intros i; inv_fin i. }
      }
      apply InitRes.app_valid.
      { apply InitRes.app_valid.
        { apply InitRes.singleton_some_valid, IRtidRA_valid. }
        { intros i; inv_fin i. }
      }
      apply InitRes.app_valid.
      { apply InitRes.app_valid.
        { apply InitRes.singleton_none_valid. }
        { intros i; inv_fin i. }
      }
      apply InitRes.app_valid.
      { apply InitRes.app_valid.
        { apply InitRes.singleton_none_valid. }
        { intros i; inv_fin i. }
      }
      { intros i; inv_fin i. }
    }
    { intros i; inv_fin i. }
  Qed.

  (* building the target module *)
  Local Definition mod_tgt : HMod.t := SpinLockMainI.t ★ MemI.t csl genv ★ SchI.t ★ SpinLockI.t.

  (* building the source module *)
  Local Definition spc_user_s : string → option fspec :=
    to_spc (SpinLockMainAS.spc u ++ MemA.Spc ++ SpinLockAS.spc u).

  Local Definition smod_src : SMod.t :=
    SpinLockMainA.Mod u ☆ MemA.Mod ☆ SchA.Mod u spc_user_s ☆ SpinLockA.Mod u.
  Local Definition spc_s : string → option fspec :=
    spc_from smod_src.
  Local Definition mod_src : HMod.t := SMod.to_hmod (wsim_ginv u ⊤) spc_s smod_src.
  Local Definition init_cond : iProp Σ := (MemA.InitCond csl genv ∗ SchA.InitCond)%I.
  Definition a : invG α Σ Γ. apply _. Defined.

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
    apply ctxr_refines.
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
    refl.
  Qed.

  Lemma cancel_tgt :
    refines (smod_cancel, (init_cond ∗ (main_fsp).(precond) tt tt↑ tt↑)%I)
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Notation "'L'" := InitRes.L (at level 50, only printing).
  Notation "'R'" := InitRes.R (at level 50, only printing).

  Hint Unfold SchA.RA_inG SchA.RA_inG0 SchA.subG_GΣ SchA.subG_GΓ : GRA_index.

  Theorem behavioral_refinement :
    ∃ target_resource, refines_mod
      (HMod.to_mod smod_cancel (IRΣ ⋅ initial_resource_own_admin))
      (HMod.to_mod mod_tgt target_resource).
  Proof.
    move: (cancel_tgt)=>H; rewrite /refines in H; ss.
    destruct (H ((IRΣ ⋅ initial_resource_own_admin))).
    { apply IRΣ_valid. }
    { rewrite /IRΣ /InitRes.app.
      try (repeat rewrite ?InitRes.L_distr ?InitRes.R_distr).
      iIntros "[[[I _] [[THS _] [[[E [D _]] [[M _] [[TID _] _]]] _]]] O]".
      iPoseProof (ownI_initial_gen u with "[I E D]") as "[U W]".
      { iSplitL "I".
        { solve_index "I". f_equal. }
        iSplitL "E".
        { solve_index "E". f_equal. }
        { solve_index "D". f_equal. }
      }
      iAssert (SchAS.tid_admin None) with "[TID]" as "TID".
      { rewrite /SchAS.tid_admin. unseal "SchA". solve_index "TID". f_equal. }
      iPoseProof (SchAS.tid_admin_none_split 0 with "TID") as "[H1 H2]".
      { iSplitR "U W O H2"; cycle 1.
        { iPoseProof (ir_own_admin with "O") as "$". unfold_pre_post; iFrame. iSplit; eauto. }
        rewrite /init_cond. iSplitL "M".
        { rewrite /MemA.InitCond /mem_initial_mem. solve_index "M". f_equal. }
        iSplitL "THS".
        { rewrite /SchAS.initial_threads. unseal "SchA". rewrite /IRthreadsRA /SchAS.threadsRA_initial.
          solve_index "THS". f_equal.
        }
        { iFrame. }
      }
    }
    { econs; ss; prove_nodup. }
    { exists x; des; eauto. }
  Qed.
End SpinLockAll.