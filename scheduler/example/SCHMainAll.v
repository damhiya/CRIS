Require Import CRIS Cancel.
Require Import ImpPrelude.
Require Import SchI SchA SchIAproof.
Require Import RRSI RRSA RRSIAproof.
Require Import NDSI NDSA NDSIAproof.
Require Import MemI MemA MemIAproof.
Require Import DetMem HybridMem MemDHProof.
Require Import RRSNodeI RRSNodeA RRSNodeIAproof.
Require Import NDSNodeI NDSNodeA NDSNodeIAproof.
Require Import SCHMainI SCHMainA SCHMainIAproof.

Module SCHMainAll.
  Import inv_instances.

  (* mem *)
  Local Definition csl : string → bool := λ _, false.
  (* global environment - not used in this example *)
  Local Definition genv : GEnv.t := [].
  
  Local Instance Γ : HRA := ##[invΓ; concΓ; newschΓ; rrsΓ; ndsΓ; MemLib.memΓ; memΓ; nodeΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ; newschΣ; rrsΣ; ndsΣ].
  Local Definition irΓ : Γ :=
    **[ir_invΓ; ir_concΓ; SchA.ir_schΓ; RRSAS.ir_schΓ; NDSA.ir_ndsΓ; (MemLib.ir_memΓ); (ir_memΓ csl genv); RRSNodeAS.ir_nodeΓ].
  Local Definition irΣ : Σ := **[irΓ; ir_invΣ; SchA.ir_schΣ; RRSAS.ir_schΣ; NDSA.ir_ndsΣ].

  Local Lemma irΣ_valid : ✓ (irΣ ⋅ ir_own_admin).
  Proof.
    solve_ir_valid.
    - apply ir_tidRA_valid.
    - apply ir_yieldRA_valid.
    - apply SchA.ir_newtidRA_valid.
    - apply RRSAS.ir_initRA_valid.
    - apply RRSAS.ir_ctlRA_valid.
    - apply RRSAS.ir_pubRA_valid.
    - apply RRSAS.ir_newtidRA_valid.
    - apply NDSA.ir_initRA_valid.
    - apply NDSA.ir_ctlRA_valid.
    - apply NDSA.ir_pubRA_valid.
    - apply NDSA.ir_tidRA_valid.
    - apply MemLib.ir_memRA_valid.
    - apply ir_memRA_valid.
    - apply RRSNodeAS.ir_nodeRA_valid.
    - apply SchA.ir_joinRA_valid.
    - apply RRSAS.ir_invRA_valid.
    - apply NDSA.ir_joinRA_valid.
  Qed.

  Local Definition sp_rrs : specmap := RRSNodeAS.sp ⊤.
  Local Definition sp_nds : specmap := NDSNodeA.sp ⊤.
  Local Definition sp_sch : specmap :=
    (SCHMainA.sp ⊤)
    ∪ (RRSAS.sp sp_rrs ⊤ snd SchA.PYIP)
    ∪ (NDSA.sp sp_nds ⊤ _ snd SchA.PYIP)
    ∪ sp_rrs
    ∪ sp_nds.

  Local Definition smod_src : SMod.t :=
    (SCHMainA.smod ⊤)
      ☆ (SchA.smod ⊤ sp_sch)
      ☆ (RRSA.smod SchHeader.SchHdr.yield sp_rrs ⊤ snd SchA.PYIP)
      ☆ (NDSA.smod SchHeader.SchHdr.yield ⊤ sp_nds _ snd SchA.PYIP)
      ☆ (RRSNodeA.smod ⊤)
      ☆ (NDSNodeA.smod ⊤).

  Local Definition mod_top : Mod.t := (SMod.to_mod ∅ (SMod.cancel smod_src)).
  Local Definition mod_tgt : Mod.t :=
    SCHMainI.t
      ★ SchI.t
      ★ (RRSI.t SchHeader.SchHdr.yield)
      ★ (NDSI.t SchHeader.SchHdr.yield)
      ★ RRSNodeI.t
      ★ NDSNodeI.t
      ★ (MemI.t csl genv)
      ★ DetMem.t.
  
  Local Definition sp : specmap := SMod.conc_sp_from smod_src.
  Local Definition mod_src : Mod.t := SMod.to_mod sp smod_src.

  Local Definition init_cond : iProp Σ :=
    SchA.init_cond ∗ RRSA.init_cond ∗ NDSA.init_cond ∗ HybMem.init_cond ∗ MemA.init_cond csl genv.

  Lemma init_cond_valid:
    ∃ rs, ✓ rs ∧ (Own rs ⊢ |==> init_cond ∗ TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤) ∗ SCHMainA.init_cond ∗ TIDAUTH 0 ∗ YIELDAUTH 1).
  Proof.
    exists (irΣ ⋅ ir_own_admin). split.
    - apply irΣ_valid.
    - simplify_res.
      { rewrite make_own_admin.

        rewrite /ir_tidRA /ir_yieldRA.
        iMod (own_update with "H62") as "H62".
        { instantiate (1 := ((λ x : nat, if decide (x = 0) then Excl' () else None): nat -d> optionUR (exclR unitO)) ⋅ ((λ x : nat, if decide (x < 1) then None else Excl' ())): nat -d> optionUR (exclR unitO)).
          eapply discrete_fun_update. i. rewrite discrete_fun_lookup_op.
          destruct a; case_decide; clarify.
        }

        iDestruct "H62" as "[H620 H621]".
        iDestruct "H60" as "[H600 H601]".
        iAssert (TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤) ∗ TIDAUTH 0 ∗ YIELDAUTH 1)%I with "[H600 H601 H620 H621 U W H1]" as "($ & $ & $ & $ & $)".
        { rewrite /TidTokenAuth /YieldTokenAuth /TidToken /YieldToken. unseal "Conc". iFrame; eauto. }

        rewrite /init_cond /SCHMainA.init_cond.
        iDestruct "H58" as "[H580 H581]".
        iAssert (SchA.init_cond)%I with "[H580 H16]" as "$".
        { iFrame; eauto. }

        iDestruct "H14" as "[H140 H141]".
        rewrite {1}/RRSAS.rrinv_admin_r.
        rewrite -{1}Qp.half_half -dfrac_op_own. rewrite fmap_empty.
        rewrite gmap_view.gmap_view_auth_dfrac_op.
        iDestruct "H140" as "[H1400 H1401]".

        rewrite /NDSA.ir_initRA. rewrite -{3}Qp.half_half -frac_op csum.Cinl_op.
        iDestruct "H42" as "[H420 H421]".

        iSplitR "H36 H1400 H50 H52 H420 H44 H581 H141"; cycle 1.
        { rewrite /RRSAS.InitRRS.
          rewrite /RRSAS.rrinv /RRSAS.Pending /RRSAS.Control. unseal RRSHeader.RRS.
          rewrite own_op.
          iFrame "H1400 H50". rewrite /RRSAS.rrinv_r.
          rewrite dom_empty elements_empty /=.
          rewrite /RRSNodeAS.full_val. unseal "Node". iFrame.
          rewrite /NDSA.InitNDS /NDSA.Pending /NDSA.Control. unseal NDSHeader.NDS. iFrame.
          rewrite /TidToken /YieldToken. unseal "Conc". iFrame; eauto.
        }

        iSplitL "H1401 H56 H54".
        { rewrite /RRSA.init_cond. rewrite /RRSAS.init_inv /RRSAS.init_tid /RRSAS.init_pub.
          unseal RRSHeader.RRS. iFrame. rewrite /RRSAS.rrinv. unseal RRSHeader.RRS.
          rewrite own_op. iFrame. eauto. }

        iSplitL "H48 H46 H12 H421".
        { iFrame; eauto. }

        
        iSplitR "H38"; cycle 1.
        { rewrite /HybMem.init_cond. rewrite /MemLib.mem_init_auth /MemLib.mem_init_frag.
          rewrite /MemLib.ir_memRA. iDestruct "H38" as "[H380 H381]".
          iFrame. eauto. }
        { rewrite /MemA.init_cond. rewrite /mem_init_auth /mem_init_frag.
          rewrite /ir_memRA. iDestruct "H40" as "[H400 H401]".
          iFrame. eauto. }        
      }
      13:{ Import MemLib. solve_res. }
      Import Mem. all: solve_res.
  (*SLOW*)Qed.

  Ltac ctac :=
    rewrite /=;
    match goal with
    | [ |- map_Forall _ (?X _) ] => rewrite /X; mod_tac ss
    | [ |- map_Forall _ (?X _ _) ] => rewrite /X; mod_tac ss
    | [ |- map_Forall _ (?X _ _ _) ] => rewrite /X; mod_tac ss
    | [ |- map_Forall _ (?X _ _ _ _) ] => rewrite /X; mod_tac ss
    | [ |- map_Forall _ (?X _ _ _ _ _) ] => rewrite /X; mod_tac ss
    end.

  Lemma cancellable_src : SMod.cancellable smod_src.
  Proof. do 5 (eapply SMod.cancellable_add; r; [ctac|]). ctac. Qed.

  Ltac _wtac_1 :=
    lazymatch goal with
    | [ |- map_Forall _ (Mod.fnsems (SMod.to_mod _ (SMod.cancel (?X _)))) ] => rewrite /X /=
    | [ |- map_Forall _ (Mod.fnsems (SMod.to_mod _ (SMod.cancel (?X _ _)))) ] => rewrite /X /=
    | [ |- map_Forall _ (Mod.fnsems (SMod.to_mod _ (SMod.cancel (?X _ _ _)))) ] => rewrite /X /=
    | [ |- map_Forall _ (Mod.fnsems (SMod.to_mod _ (SMod.cancel (?X _ _ _ _)))) ] => rewrite /X /=
    | [ |- map_Forall _ (Mod.fnsems (SMod.to_mod _ (SMod.cancel (?X _ _ _ _ _)))) ] => rewrite /X /=
    end;
    rewrite /Mod.fnsems /=;
    lazymatch goal with
    | [ |- map_Forall _ (_ <$> (mbind _ <$> (?X _))) ] => rewrite /X !fmap_insert !fmap_empty; mod_tac ss
    | [ |- map_Forall _ (_ <$> (mbind _ <$> (?X _ _))) ] => rewrite /X !fmap_insert !fmap_empty; mod_tac ss
    | [ |- map_Forall _ (_ <$> (mbind _ <$> (?X _ _ _))) ] => rewrite /X !fmap_insert !fmap_empty; mod_tac ss
    | [ |- map_Forall _ (_ <$> (mbind _ <$> (?X _ _ _ _))) ] => rewrite /X !fmap_insert !fmap_empty; mod_tac ss
    | [ |- map_Forall _ (_ <$> (mbind _ <$> (?X _ _ _ _ _))) ] => rewrite /X !fmap_insert !fmap_empty; mod_tac ss
    end.
  Ltac _wtac_2 :=
    ss;
    lazymatch goal with
    | [ |- ∀ _, _ _ ?X <= _ ] => rewrite /X
    | _ => idtac
    end; multiset_solver.
  Ltac wtac := econs; [_wtac_1|_wtac_2].
  Ltac solv := rewrite ?dom_union_with ?dom_fmap; set_solver.
    
  Local Transparent SCH.
  Local Transparent NDSHeader.NDS.
  Local Transparent RRSHeader.RRS.

  Lemma wf_top : Mod.wf mod_top.
  Proof.
    rewrite /mod_top !SMod.cancel_add !SMod.to_mod_add.
    eapply Mod.add_wf; [wtac| |solv|solv].
    eapply Mod.add_wf; [wtac| |solv|solv].
    eapply Mod.add_wf; [wtac| |solv|solv].
    eapply Mod.add_wf; [wtac| |solv|solv].
    eapply Mod.add_wf; [wtac| |solv|solv].
    wtac.
  Qed.

  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    refines (mod_top, init_cond ∗ TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤) ∗ SCHMainA.init_cond ∗ TIDAUTH 0 ∗ YIELDAUTH 1)%I
            (mod_src, init_cond).
  Proof.
    eapply Cancel.cancellation.
    { eapply cancellable_src. }
    { eapply wf_top. }
    { assert (Ht : SMod.conc_sp_from smod_src !! speckey_entry =
        fsp_some (SCHMainA.main_spec ⊤)); last (rewrite Ht; clear Ht).
      { rewrite lookup_insert_ne // lookup_kmap_Some; exists None; split; ss. }
      exists (precond (SCHMainA.main_spec ⊤) tt), (postcond (SCHMainA.main_spec ⊤) tt); splits.
      { ss. exists (). esplits; refl. }
      { iIntros "(T & Y & W & A & B & C & D)". iFrame. iModIntro. eauto. }
      { i. iIntros "(W & % & _)". eauto. }
    }
  (*SLOW*)Qed.

  Section SP.

    Ltac single :=
      repeat try eapply insert_subseteq_l; last apply map_empty_subseteq;
      rewrite lookup_insert_ne // lookup_kmap_Some; eexists (Some _); split; ss.
    Ltac entry :=
      repeat try eapply insert_subseteq_l; last apply map_empty_subseteq;
      rewrite lookup_insert_ne // lookup_kmap_Some; eexists None; split; ss.

    Lemma spsch_in_sp : sp_sch ⊆ sp.
    Proof.
      do 4 (eapply map_union_least; [|single]). entry.
    (*SLOW*)Qed.

    Lemma sch_in_sp : (SchA.sp sp_sch ⊤) ⊆ sp.
    Proof. single. Qed.

    Lemma rrs_in_spsch : (RRSAS.sp sp_rrs ⊤ snd SchA.PYIP) ⊆ sp_sch.
    Proof.
      rewrite /sp_sch /SCHMainA.sp /sp_nds /NDSNodeA.sp /RRSAS.sp /NDSA.sp.
      repeat try eapply insert_subseteq_l; last apply map_empty_subseteq;
        rewrite !lookup_union;
        repeat (rewrite lookup_insert_ne; [|by (intros F; inv F)]);
        rewrite lookup_insert;
        repeat (rewrite lookup_insert_ne; [|intros F; inv F]);
        rewrite !lookup_empty; ss.
    Qed.

    Lemma nds_in_spsch : (NDSA.sp sp_nds ⊤ _ snd SchA.PYIP) ⊆ sp_sch.
    Proof.
      rewrite /sp_sch /SCHMainA.sp /sp_nds /NDSNodeA.sp /RRSAS.sp /NDSA.sp.
      repeat try eapply insert_subseteq_l; last apply map_empty_subseteq;
        rewrite !lookup_union;
        repeat (rewrite lookup_insert_ne; [|by (intros F; inv F)]);
        rewrite lookup_insert;
        repeat (rewrite lookup_insert_ne; [|intros F; inv F]);
        rewrite !lookup_empty; ss.
    Qed.

    Lemma rrsnode_in_sprrs : (RRSNodeAS.sp ⊤) ⊆ sp_rrs.
    Proof. by reflexivity. Qed.

    Lemma ndsnode_in_sprrs : (NDSNodeA.sp ⊤) ⊆ sp_nds.
    Proof. by reflexivity. Qed.

    Lemma sprrs_in_sp : sp_rrs ⊆ sp.
    Proof. single. Qed.

    Lemma spnds_in_sp : sp_nds ⊆ sp.
    Proof. single. Qed.

    Lemma yield_in_sp : sp !! (speckey_fn SchHeader.SchHdr.yield) = fsp_some (SchA.yield_spec ⊤).
    Proof. rewrite lookup_insert_ne // lookup_kmap_Some; eexists (Some _); split; ss. Qed.

    Lemma yield_spec_cond :
      ⊢ fspec_imply (SchA.yield_spec ⊤)
          (fspec_winv ⊤
             (fspec_mk 
                (λ x varg arg, 
                  TID (snd x) ∗ YIELD (snd x) ∗ PYIP x ∗ ⌜varg = arg ∧ varg = tt↑⌝)
                (λ x vret ret, 
                  TID (snd x) ∗ YIELD (snd x) ∗ PYIP x ∗ ⌜vret = ret ∧ vret = tt↑⌝))%I).
    Proof.
      iIntros (??) "[%x [%Hpre %Hpost]]"; ss.
      destruct x as [mtid stid].
      iExists (precond (SchA.yield_spec ⊤) (stid, mtid, tt)), (postcond (SchA.yield_spec ⊤) (stid, mtid, tt)).
      iSplit.
      { iPureIntro. exists (stid, mtid, tt). esplits; eauto. }
      iIntros (??) "PRE". iModIntro. iSplitL "PRE".
      { subst P1. iDestruct "PRE" as "(W & T & Y & P & %)"; des; subst; hss. iFrame; eauto. }
      iIntros (??) "POST". iModIntro.
      subst Q1. iDestruct "POST" as "(W & (tid & T & Y) & %)"; des; subst; hss. iFrame; eauto.
    Qed.
  End SP.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    eapply ctxr_refines.
    rewrite /mod_src /mod_tgt /smod_src.

    etrans; cycle 1.
    { ctxr_rotate. do 7 ctxr_drop. eapply SCHMainIAproof.ctxr.
      { eapply spsch_in_sp. }
      { eapply sch_in_sp. }
      { eapply rrs_in_spsch. }
      { eapply nds_in_spsch. }
      { eapply rrsnode_in_sprrs. }
      { eapply ndsnode_in_sprrs. }
    }

    etrans; cycle 1.
    { ctxr_rotate. do 7 ctxr_drop. eapply SchIA.ctxr.
      { eapply sch_in_sp. }
      { eapply spsch_in_sp. }
      { unfold sp, SMod.conc_sp_from; rewrite dom_insert; eapply elem_of_union_l; set_solver. }
    }

    etrans; cycle 1.
    { ctxr_rotate. do 7 ctxr_drop. eapply RRSIA.ctxr.
      { eapply yield_in_sp. }
      { etrans; [eapply rrs_in_spsch| eapply spsch_in_sp]. }
      { eapply sprrs_in_sp. }
      { eapply yield_spec_cond. }
      { unfold sp, SMod.conc_sp_from; rewrite dom_insert; eapply elem_of_union_l; set_solver. }
    }

    etrans; cycle 1.
    { ctxr_rotate. do 7 ctxr_drop. eapply NDSIA.ctxr.
      { eapply yield_in_sp. }
      { etrans; [eapply nds_in_spsch| eapply spsch_in_sp]. }
      { eapply spnds_in_sp. }
      { eapply yield_spec_cond. }
      { unfold sp, SMod.conc_sp_from; rewrite dom_insert; eapply elem_of_union_l; set_solver. }
    }

    etrans; cycle 1.
    { do 3 ctxr_rotate. do 7 ctxr_drop. eapply MemIA.ctxr. }

    etrans; cycle 1.
    { ctxr_rotate. do 7 ctxr_drop. eapply MemDH.ctxr. }
    
    etrans; cycle 1.
    { do 2 ctxr_drop. do 3 (ctxr_rotate; ctxr_drop). ctxr_rotate. eapply RRSNodeIAproof.ctxr; cycle 1.
      { etrans; [eapply rrs_in_spsch|eapply spsch_in_sp]. }
      { eapply rrsnode_in_sprrs. }
      { eapply sprrs_in_sp. }
    }

    etrans; cycle 1.
    { do 3 ctxr_drop. do 2 ctxr_rotate. do 3 ctxr_drop. eapply NDSNodeIAproof.ctxr; cycle 1.
      { etrans; [eapply nds_in_spsch|eapply spsch_in_sp]. }
      { eapply ndsnode_in_sprrs. }
      { eapply spnds_in_sp. }
    }

    etrans; cycle 1.
    { do 4 ctxr_drop. ctxr_rotate. do 3 ctxr_drop. eapply CFilter.elim_module. }

    etrans; cycle 1.
    { do 6 ctxr_drop. ctxr_rotate. ctxr_drop. eapply CFilter.elim_module. }

    rewrite -!mod_add_empty_r.

    etrans; cycle 1.
    { do 2 ctxr_drop. do 2 ctxr_rotate. ctxr_drop. ctxr_rotate. ctxr_refl. }

    rewrite /init_cond.
    rewrite !SMod.to_mod_add /init_cond.
    rewrite /SCHMainA.t /SchA.t /RRSA.t /NDSA.t /RRSNodeA.t /NDSNodeA.t.

    eapply ctxr_cond_strengthen.
    iIntros "(? & ? & ? & ? & ?)". iFrame.
  (*SLOW*)Qed.

  Lemma top_tgt :
    refines (mod_top, init_cond ∗ TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤) ∗ SCHMainA.init_cond ∗ TIDAUTH 0 ∗ YIELDAUTH 1)%I
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Ltac _ttac_1 :=
    lazymatch goal with
    | [ |- map_Forall _ (Mod.fnsems (?X)) ] => rewrite /X /=
    | [ |- map_Forall _ (Mod.fnsems (?X _)) ] => rewrite /X /=
    | [ |- map_Forall _ (Mod.fnsems (?X _ _)) ] => rewrite /X /=
    end;
    rewrite /Mod.fnsems /=;
    lazymatch goal with
    | [ |- map_Forall _ (_ <$> (?X)) ] => rewrite /X !fmap_insert !fmap_empty; mod_tac ss
    | [ |- map_Forall _ (_ <$> (?X _)) ] => rewrite /X !fmap_insert !fmap_empty; mod_tac ss
    | [ |- map_Forall _ (_ <$> (?X _ _)) ] => rewrite /X !fmap_insert !fmap_empty; mod_tac ss
    end.
  Ltac _ttac_2 :=
    ss;
    lazymatch goal with
    | [ |- ∀ _, _ _ ?X <= _ ] => rewrite /X
    | _ => idtac
    end; multiset_solver.
  Ltac ttac := econs; [_ttac_1|_ttac_2].
  Ltac tolv := rewrite ?dom_union_with ?dom_fmap; set_solver.

  Lemma tgt_wf: Mod.wf mod_tgt.
  Proof.
    rewrite /mod_tgt.
    eapply Mod.add_wf; [ttac| |tolv|tolv].
    eapply Mod.add_wf; [ttac| |tolv|tolv].
    eapply Mod.add_wf; [ttac| |tolv|tolv].
    eapply Mod.add_wf; [ttac| |tolv|tolv].
    eapply Mod.add_wf; [ttac| |tolv|tolv].
    eapply Mod.add_wf; [ttac| |tolv|tolv].
    eapply Mod.add_wf; [ttac| |tolv|tolv].
    ttac.
  Qed.

  Theorem behavioral_refinement :
    ∃ src_res tgt_res, refines_lmod
      (Mod.to_lmod mod_top src_res)
      (Mod.to_lmod mod_tgt tgt_res).
  Proof.
    move: (top_tgt)=>H; rewrite /refines in H; des; ss.
    hexploit H; eauto using tgt_wf. clear H; intros [WF H].
    pose proof init_cond_valid as IV. des.
    destruct (H rs); des; et.
    rewrite IV0 /init_cond /SCHMainA.init_cond {1}winv_split_empty.
    iIntros ">((? & ? & ? & ? & ?) & ? & ? & (? & ?) & (? & ? & ? & ?) & ? & ?)". iFrame. eauto.
  Qed.
(*SLOW*)End SCHMainAll.
(* Print Assumptions SCHMainAll.behavioral_refinement. *)
