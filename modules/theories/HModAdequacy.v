Require Import Coqlib AList.
Require Export sflib.
Require Export ITreelib.
Require Import Any.

Require Import IRed.
Require Import STS.
Require Import Behavior Skeleton.
Require Import PCM IPM.

Require Import SimInitial SimModSem SimModSemFacts0 ModSemFacts SimModSemFacts.
Require Import HPSim HPSimFacts.

Require Import HMod Mod Events BasicEvents.

Require Import ISim.


Require Import World sWorld.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Set Implicit Arguments.


(**** TODO: State theorem & lemmas required for proof's transitivity. ****)
(* To be moved or merged to another file *)

Section ADEQUACY.
  Context `{_W: CtxWD.t}.

  Theorem adequacy_hmod
      (md_src md_tgt: HMod.t) Ist
      (SIM: HModPair.sim md_src md_tgt Ist)
    :
      ModPair.sim (HMod.to_mod md_src) (HMod.to_mod md_tgt).
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
      { instantiate (1:= q). r_solve. replace (q ⋅ p) with (p ⋅ q);[eauto|r_solve]. }
      eapply iProp_Own in H1. iIntros "H". iApply (H1 with "H").
    - eapply Forall2_apply_Forall2; eauto.
      i. destruct a, b. inv H. econs; ss. ii. do 3 r in H1.
        specialize (H1 x y H). inv SIMMRS. s.
        specialize (H1 st_src st_tgt).
        eapply hpsim_adequacy; [et|et| |r_solve;et|]; cycle 1.
        { instantiate (1:= mr). r_solve. eauto. }
        ginit. eapply isim_init in H1.
        { ss. (* iunlift ibot <7= bot7. *) admit. }
        instantiate (1:= mr). admit.
        (* update modality diff. Can we fix isim_init? *)
  Admitted.

  Section HMODSEM.
    Import HModSem.

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
          (List.map trans_l fl_src ++ List.map trans_r fl_ctx)
          (List.map trans_l fl_tgt ++ List.map trans_r fl_ctx) 
          ibot ibot
          (λ '(st_src0, v_src) '(st_tgt0, v_tgt), IstProd Ist IstEq st_src0 st_tgt0 ** ⌜v_src = v_tgt⌝) 
          false false 
          (Any.pair st_src st_ctx, translate (emb_ run_l) (i y)) (Any.pair st_tgt st_ctx, translate (emb_ run_l) (i0 y)).
    Proof.
      iIntros "H". iEval (unfold IstProd) in "H". 
      iDestruct "H" as (? ? ? ?) "(% & H & %)". des. subst.      
    Admitted.


    Theorem isim_ctx
            ctx ms1 ms2 Ist
            (SIM: HModSemPair.sim ms1 ms2 Ist)
        :
            HModSemPair.sim (HModSem.add ms1 ctx) (HModSem.add ms2 ctx) (IstProd Ist IstEq).
    Proof.
      inv SIM. 
      econs; ss; cycle 1.
      { 
        iIntros "[H C]". iPoseProof (isim_initial with "H") as "[H I]". iFrame.
        unfold IstProd, IstEq. 
        iExists (initial_st ms1), (initial_st ms2).
        iFrame. iPureIntro. esplits; eauto.    
      }
      unfold add_fnsems, trans_l, trans_r.
      apply Forall2_app; eapply Forall2_apply_Forall2; eauto; cycle 1.
      - instantiate (1:= eq). induction (fnsems ctx); eauto.
      - i. subst. econs; eauto. ii; subst. 
        destruct b. ss. eapply isim_reflR.
      - i. destruct H. r in H. do 3 r in H0.
        destruct a, b. econs; eauto. ss. subst. ss.
        ii. subst. s. 
        iIntros "H". 
        iEval (unfold IstProd) in "H".
        iDestruct "H" as (? ? ? ?) "(% & I & %)". des. subst.
        iApply isim_ctx_aux; eauto.
        unfold IstProd, IstEq. iExists st_srcL, st_tgtL. iFrame.
        iPureIntro. esplits; eauto.
    Qed.

  Theorem sim_ctx_hmod
        ctx md1 md2 Ist
        (SIM: HModPair.sim md1 md2 Ist)
      :
        HModPair.sim (HMod.add md1 ctx) (HMod.add md2 ctx) (IstProd Ist IstEq).
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

  End HMODSEM.

End ADEQUACY.