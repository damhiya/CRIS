Require Import Coqlib AList.
Require Export sflib.
Require Export ITreelib.
Require Import Any.

Require Import IRed.
Require Import STS.
Require Import Behavior Skeleton.
Require Import PCM IPM.

Require Import ModSim ModSimFacts.
Require Import HPSim HPSimFacts.

Require Import HMod Mod HMod2Mod Events.

Require Import ISim.
Require Import CtxRefine.

Require Import World sWorld.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Set Implicit Arguments.


(**** TODO: State theorem & lemmas required for proof's transitivity. ****)
(* To be moved or merged to another file *)

Section ADEQUACY.

  Context `{Σ: GRA.t}.

  Theorem hmodr_adequacy (ms mt: HMod.t) IC Ist
    (SIM: HModR.sim ms mt IC Ist)
    :
    ctx_refines (ms,IC) (mt, fun _ => emp%I).
  Proof.
  Admitted.

End ADEQUACY.

(*

Section ADEQUACY.
  (* Context `{_W: CtxWD.t}. *)
  Context `{Σ: GRA.t}.

  Lemma Own_upd_specify
        r P 
        (UPD: Own r ⊢ #=> P) 
        (WF: URA.wf r):
    exists r0, P r0 /\ URA.updatable r r0.
  Proof.
    uiprop in UPD. specialize (UPD r WF).
    hexploit UPD; [refl|]. i. des.
    esplits; eauto.
  Qed.

  Theorem adequacy_hmod
      (md_src md_tgt: HMod.t) Ist
      (rs rt: Σ) 
      (* (WF: URA.wf rs) *)
      (* (SRC: forall sk, 
        HModSem.initial_cond (md_src.(HMod.get_modsem) sk) rs) *)
      (* (TGT: forall sk,
        HModSem.initial_cond (md_tgt.(HMod.get_modsem) sk) rt) *)
      (SRC: HModSem.initial_cond (md_src.(HMod.get_modsem) md_src.(HMod.sk)) rs)
      (TGT: HModSem.initial_cond (md_tgt.(HMod.get_modsem) md_tgt.(HMod.sk)) rt)
      (SIM: HModR.sim md_src md_tgt Ist)
    :
      ModR.sim (HMod.to_mod md_src rs) (HMod.to_mod md_tgt rt).
  Proof.
    (* inv SIM. des.
    econs; eauto. i. specialize (sim_modsem sk SKINCL SKWF).
    specialize (SRC sk). specialize (TGT sk). 
    des. inv sim_modsem.
    econs; ss.
    - instantiate (1:= eq). eapply base.PreOrder_instance_0.
    - instantiate (1:= interp_inv Ist).
      exists ε. econs; eauto.
      {
        iIntros "H". eapply iProp_Own in SRC. iPoseProof (SRC with "H") as "H".
        iPoseProof (sim_initial with "H") as "[TGT IST]".
        admit.
      }
      admit.
    - rewrite! List.map_length. eauto.
    - i. rewrite alist_find_map in *. unfold o_map in *. des_ifs.
      eapply sim_miss in Heq0. clarify.
    - i. rewrite alist_find_map in *. unfold o_map in *. des_ifs; cycle 1.
      { eapply sim_fnsems in Heq0. des. clarify. }
      esplits; eauto.
      ii. subst. inv SIMMRS. eapply hpsim_adequacy; eauto; cycle 1.
      { r_solve. eauto. }
      { instantiate (1:= mr). r_solve. eauto. }
      ginit. apply gpaco7_mon with (r := iunlift ibot) (rg := iunlift ibot); eauto using iunlift_ibot.
      guclo hpsim_wfC_spec. econs. i.
      eapply Own_upd_specify in MR; eauto. des.
      guclo hpsim_updateC_spec. econs. econs. instantiate (1:= r0).
      esplits; eauto using Own_Upd.
      eapply isim_init; cycle 1. { eapply iProp_Own. eauto. }
      hexploit sim_fnsems; eauto. i. des.
      assert (i = ft). { rewrite Heq in H1. inv H1. eauto. }
      subst. do 2 r in H2. hexploit (H2 y y); eauto. *)
      
  
(*     
    - instantiate (1:= eq). eapply base.PreOrder_instance_0.
    - ss. unfold cond_to_st, handle_init_cond, assume_init. grind.
      ginit. 
      gstep. econs; eauto. i. grind. econs; eauto. i. econs; eauto. i. (* run src to the end *)
      assert (Own x ⊢ HModSem.initial_cond (HMod.get_modsem md_tgt sk) **
      Ist (HModSem.initial_st (HMod.get_modsem md_src sk)) (HModSem.initial_st (HMod.get_modsem md_tgt sk))).
      { iIntros "H". iApply isim_initial. iApply x1. eauto. }
      eapply iProp_sepconj in H; cycle 1. { eapply URA.wf_mon. eauto. }
      des.
      econs; eauto. instantiate (1:= p). grind. econs; eauto. { r_solve. do 2 eapply URA.wf_mon. eauto. } 
      econs; eauto. { eapply iProp_Own. eauto. }
      econs. exists (ε: Σ). instantiate (1:= interp_inv Ist). hss. 
      econs; eauto.
      { instantiate (1:= q). r_solve. rewrite URA.add_comm. eauto. }
      eapply iProp_Own in H1. iIntros "H". iApply (H1 with "H").
    - eapply Forall2_apply_Forall2; eauto.
      i. destruct a, b. inv H. econs; ss. ii. do 3 r in H1.
        specialize (H1 x y H). inv SIMMRS. s.
        specialize (H1 st_src st_tgt).
        eapply hpsim_adequacy; [et|et| |r_solve;et|]; cycle 1.
        { instantiate (1:= mr). r_solve. eauto. }
        ginit. guclo hpsim_wfC_spec. econs. i.
        eapply Own_upd_specify in MR; eauto. des.
        eapply Own_Upd in MR0.
        guclo hpsim_updateC_spec. econs. econs.
        instantiate (1:= r0). esplits; eauto.
        eapply iProp_Own in MR. eapply isim_init in H1; eauto.
        eapply gpaco7_mon; eauto using iunlift_ibot. *)

  Admitted.

  (* Theorem adequacy_hmod
      (md_src md_tgt: HMod.t) Ist
      (SIM: HModR.sim md_src md_tgt Ist)
    :
      ModR.sim (HMod.to_mod md_src) (HMod.to_mod md_tgt).
  Proof.
    inv SIM. des.
    econs; eauto. i. specialize (sim_modsem sk SKINCL SKWF). 
    des. inv sim_modsem.
    econs; swap 2 3.
    - instantiate (1:= eq). eapply base.PreOrder_instance_0.
    - ss. unfold cond_to_st, handle_init_cond, assume_init. grind.
      ginit. 
      gstep. econs; eauto. i. grind. econs; eauto. i. econs; eauto. i. (* run src to the end *)
      assert (Own x ⊢ HModSem.initial_cond (HMod.get_modsem md_tgt sk) **
      Ist (HModSem.initial_st (HMod.get_modsem md_src sk)) (HModSem.initial_st (HMod.get_modsem md_tgt sk))).
      { iIntros "H". iApply isim_initial. iApply x1. eauto. }
      eapply iProp_sepconj in H; cycle 1. { eapply URA.wf_mon. eauto. }
      des.
      econs; eauto. instantiate (1:= p). grind. econs; eauto. { r_solve. do 2 eapply URA.wf_mon. eauto. } 
      econs; eauto. { eapply iProp_Own. eauto. }
      econs. exists (ε: Σ). instantiate (1:= interp_inv Ist). hss. 
      econs; eauto.
      { instantiate (1:= q). r_solve. rewrite URA.add_comm. eauto. }
      eapply iProp_Own in H1. iIntros "H". iApply (H1 with "H").
    - eapply Forall2_apply_Forall2; eauto.
      i. destruct a, b. inv H. econs; ss. ii. do 3 r in H1.
        specialize (H1 x y H). inv SIMMRS. s.
        specialize (H1 st_src st_tgt).
        eapply hpsim_adequacy; [et|et| |r_solve;et|]; cycle 1.
        { instantiate (1:= mr). r_solve. eauto. }
        ginit. guclo hpsim_wfC_spec. econs. i.
        eapply Own_upd_specify in MR; eauto. des.
        eapply Own_Upd in MR0.
        guclo hpsim_updateC_spec. econs. econs.
        instantiate (1:= r0). esplits; eauto.
        eapply iProp_Own in MR. eapply isim_init in H1; eauto.
        eapply gpaco7_mon; eauto using iunlift_ibot.
  Qed. *)

End ADEQUACY.

Section HPSIM.
  Context `{Σ: GRA.t}.
  Import HModSem.

  Definition addf f1 f2 : alist gname (Any.t -> itree _ Any.t) :=
    (List.map trans_l f1) ++ (List.map trans_r f2).

  Lemma IstProdEq 
        Ist stl str stc
    :
        Ist stl str
      -∗
        IstProd Ist IstEq (Any.pair stl stc) (Any.pair str stc).
  Proof.
    iIntros "H". unfold IstProd, IstEq. iExists stl, str, _, _.
    iFrame. iPureIntro. esplits; eauto.
  Qed.

  Ltac hstep := guclo hpsimC_spec; econs; econs; eauto; econs; eauto.

  (* Not necessary if you can prove isim_ctx_aux directly. *)
  Theorem hpsim_ctx
          fl_src fl_tgt fl_ctx Ist
          ps pt st_src st_tgt st_ctx itr_src itr_tgt
          fmr stl str
          (SIM: hpsim_body fl_src fl_tgt Ist ps pt (st_src, itr_src) (st_tgt, itr_tgt) fmr)
          (SRC: stl = Any.pair st_src st_ctx)
          (TGT: str = Any.pair st_tgt st_ctx)
      :
          hpsim_body (addf fl_src fl_ctx) (addf fl_tgt fl_ctx) (IstProd Ist IstEq) 
          ps pt (stl, translate (emb_ run_l) itr_src) (str, translate (emb_ run_l) itr_tgt) fmr.
  Proof.
    revert_until Σ. ginit. gcofix CIH. i.
    remember (st_src, itr_src). remember (st_tgt, itr_tgt).
    move SIM before Σ. revert_until SIM. punfold SIM.
    pattern ps, pt, p, p0, fmr.
    eapply _hpsim_tarski, SIM; i. clear SIM fmr. rename fmr0 into fmr.
    guclo hpsim_wfC_spec. econs. i. 
    exploit IN; i; des; eauto.
    destruct x0; i; des; inv Heqp; try inv Heqp0.
    - rewrite! translate_emb_ret. hstep.
      iIntros "H". iPoseProof (RET with "H") as ">[H %]".
      iModIntro. iSplit; eauto. iApply IstProdEq. eauto.
    - rewrite! translate_emb_bind. rewrite! translate_emb_callE. hstep.
      { 
        instantiate (1:= FR). iIntros "H". iPoseProof (INV with "H") as ">[H FR]".
        iModIntro. iFrame. iApply IstProdEq. eauto.
      }
      (* 
        Property about Any.pair is not restored without Own fmr1. 
      *)
      i. guclo hpsim_wfC_spec. econs. i.
 
      eapply K; eauto; admit.
    - rewrite! translate_emb_bind. rewrite! translate_emb_coreE. hstep.
    - rewrite! translate_emb_bind. rewrite translate_emb_callE. hstep.
      { unfold addf. apply alist_find_app. unfold trans_l. rewrite alist_find_map. unfold o_map. rewrite FUN. et. }
      s. (* put Ret ();;; Ret x back into translate () *) admit.
    - rewrite! translate_emb_bind. admit.
    - rewrite! translate_emb_tau. hstep.
    - rewrite! translate_emb_tau. hstep.
    - rewrite! translate_emb_bind. rewrite! translate_emb_coreE. hstep.
    - rewrite! translate_emb_bind. rewrite! translate_emb_coreE. hstep.
    - rewrite! translate_emb_bind. rewrite! translate_emb_coreE. hstep.
    - rewrite! translate_emb_bind. rewrite! translate_emb_coreE. hstep.
    - rewrite! translate_emb_bind. rewrite! translate_emb_sE. hstep. hss. des_ifs.
    - rewrite! translate_emb_bind. rewrite! translate_emb_sE. hstep. hss. des_ifs.
    - rewrite! translate_emb_bind. rewrite translate_emb_assume. hstep.
    - rewrite! translate_emb_bind. rewrite translate_emb_guarantee. hstep.
    - rewrite! translate_emb_bind. rewrite translate_emb_guarantee. hstep.
    - rewrite! translate_emb_bind. rewrite translate_emb_assume. hstep.
    - gstep. econs. econs. econs; eauto. econs; eauto. 
      gbase. pclearbot. eapply CIH; eauto.
  Admitted.


          
          

End HPSIM.

Section SIM.
  Context `{Σ: GRA.t}.
  (* Context `{_W: CtxWD.t}. *)
  Section HMODSEM.
    Import HModSem.

    Ltac cq := apply combine_quant.

    Lemma any_pair_inv 
          a0 a1 b0 b1
          (PAIR: Any.pair a0 a1 = Any.pair b0 b1)
        :
           a0 = b0 /\ a1 = b1.
    Proof.
      destruct (Any.split (Any.pair a0 a1)) eqn:E; cycle 1.
      { rewrite Any.pair_split in E. inv E. }
      destruct p. hexploit E. i.
      rewrite PAIR in H. 
      rewrite Any.pair_split in *. inv E. inv H.
      esplits; eauto.  
    Qed.


    Lemma isim_ctx_aux
          s i i0 st_src st_tgt st_ctx
          y fl_src fl_tgt fl_ctx Ist
          (IN: In (s, i) fl_src /\ In (s, i0) fl_tgt)
          (SIM: Ist st_src st_tgt
                ⊢ isim Ist fl_src fl_tgt ibot ibot 
                    (λ '(st_src, v_src) '(st_tgt, v_tgt), Ist st_src st_tgt ** ⌜v_src = v_tgt⌝) 
                    false false (st_src, i y) (st_tgt, i0 y))
      :
        IstProd Ist IstEq (Any.pair st_src st_ctx) (Any.pair st_tgt st_ctx)
        ⊢ isim (IstProd Ist IstEq)
          (addf fl_src fl_ctx) (addf fl_tgt fl_ctx) 
          ibot ibot
          (λ '(st_src0, v_src) '(st_tgt0, v_tgt), IstProd Ist IstEq st_src0 st_tgt0 ** ⌜v_src = v_tgt⌝) 
          false false 
          (Any.pair st_src st_ctx, translate (emb_ run_l) (i y)) (Any.pair st_tgt st_ctx, translate (emb_ run_l) (i0 y)).
    Proof.
      iIntros "H". iDestruct "H" as (? ? ? ?) "(% & IST & %)".
      des. eapply any_pair_inv in H, H1. des. subst. clear H0.
      remember (Any.pair st_srcL st_tgtR).
      remember (Any.pair st_tgtL st_tgtR).
      iPoseProof (SIM with "IST") as "SIM".
      Local Transparent isim. iStopProof. uiprop. i.
      eapply gpaco7_mon; cycle 1.
      { instantiate (1:= bot7). i. inv PR. }
      { instantiate (1:= bot7). i. inv PR. }
      gfinal. right. eapply hpsim_ctx; eauto.
      ginit. eapply gpaco7_mon; eauto using iunlift_ibot.
    Qed.

    Theorem isim_ctx
            ctx ms1 ms2 Ist
            (SIM: HModSemR.sim ms1 ms2 Ist)
        :
            HModSemR.sim (HModSem.add ms1 ctx) (HModSem.add ms2 ctx) (IstProd Ist IstEq).
    Proof.
      inv SIM. 
      econs; ss.
      { 
        iIntros "[H C]". iPoseProof (sim_initial with "H") as "[H I]". iFrame.
        unfold IstProd, IstEq. 
        iExists (initial_st ms1), (initial_st ms2).
        iFrame. iPureIntro. esplits; eauto.    
      }
      { 
        unfold add_fnsems. rewrite! List.app_length. rewrite! List.map_length.
        f_equal. ss.
      }
      {
        i. unfold add_fnsems in MISS. rewrite alist_find_app_o in MISS. des_ifs.
        admit.
      }
      i. unfold add_fnsems in FIND. rewrite alist_find_app_o in FIND. des_ifs.
      { (* find in ms1 *)
        admit.
      }
      { (* find in ctx *)
        admit.
      } 
    Admitted.
  End HMODSEM.

  Theorem sim_ctx_hmod
        ctx md1 md2 Ist
        (SIM: HModR.sim md1 md2 Ist)
      :
        HModR.sim (HMod.add md1 ctx) (HMod.add md2 ctx) (IstProd Ist IstEq).
  Proof.
    inv SIM.
    econs; et.
    - i. ss. hexploit (sim_modsem sk); et.
      2: { ii. des. r. eapply isim_ctx. eauto. }
      unfold Sk.incl, Sk.add in *. i. ss.
      apply SKINCL.
      rewrite in_app_iff. et.
    - r. ss. unfold Sk.add. ss.
      rewrite sim_sk. et.
  Qed.
End SIM.

*)
