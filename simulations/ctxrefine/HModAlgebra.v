Require Export Coqlib sflib Any.
Require Import Behavior.
Require Import Mod Skeleton Events.
(* Require Import CtxRefine. *)
Require Import PCM IPM HMod HPSim ISim HModAdequacy.
Require Import ModSimAlgebra ModSimFacts.

Set Implicit Arguments.

Module HModAlgebra.
  Import HModSem HModRed.
  
  Section LEMMA.
    Context `{Σ: GRA.t}.

    Record wf (ms: t): Prop := mk_wf {
      wf_fnsems: NoDup (List.map fst ms.(fnsems));
    }.

    Lemma fst_trans_l : forall x, fst (trans_l x) = fst x.
    Proof. i. destruct x. ss. Qed.
  
    Lemma fst_trans_r : forall x, fst (trans_r x) = fst x.
    Proof. i. destruct x. ss. Qed.

    Lemma fun_fst_trans_l : 
      (fun x : string * (Any.t -> itree hmodE Any.t) => fst (trans_l x)) = (fun x : string * (Any.t -> itree hmodE Any.t) => fst x).
    Proof.
      extensionality x. rewrite fst_trans_l. et.
    Qed.

    Lemma fun_fst_trans_r : 
      (fun x : string * (Any.t -> itree hmodE Any.t) => fst (trans_r x)) = (fun x : string * (Any.t -> itree hmodE Any.t) => fst x).
    Proof.
      extensionality x. rewrite fst_trans_r. et.
    Qed.

    Lemma fun_fst_trans_l_l :
      (fun x : string * (Any.t -> itree hmodE Any.t) => fst (trans_l (trans_l x))) = (fun x : string * (Any.t -> itree hmodE Any.t) => fst x).
    Proof.
      extensionality x. rewrite ! fst_trans_l. et.
    Qed.

    Lemma fun_fst_trans_l_r :
      (fun x : string * (Any.t -> itree hmodE Any.t) => fst (trans_l (trans_r x))) = (fun x : string * (Any.t -> itree hmodE Any.t) => fst x).
    Proof.
      extensionality x. rewrite fst_trans_l. rewrite fst_trans_r. et.
    Qed.

    Lemma fun_fst_trans_r_l:
      (fun x : string * (Any.t -> itree hmodE Any.t) => fst (trans_r (trans_l x))) = (fun x : string * (Any.t -> itree hmodE Any.t) => fst x).
    Proof.
      extensionality x. rewrite fst_trans_r. rewrite fst_trans_l. et.
    Qed.

    Lemma fun_fst_trans_r_r:
      (fun x : string * (Any.t -> itree hmodE Any.t) => fst (trans_r (trans_r x))) = (fun x : string * (Any.t -> itree hmodE Any.t) => fst x).
    Proof.
      extensionality x. rewrite ! fst_trans_r. et.
    Qed.

    Lemma translate_emb_cmpE
          A (run_0 run_1: RUN)
          (itr: itree hmodE A)
    :
          translate ((emb_ run_1) >>> (emb_ run_0)) itr = translate (emb_ run_0) (translate (emb_ run_1) itr).
    Proof.
      rewrite (bisim_is_eq (translate_cmpE _ _ _ _ _ _ _)). et. 
    Qed.

  End LEMMA.

  Section COMM.
    Context `{Σ: GRA.t}.

    Definition comm_Ist: Any.t -> Any.t -> iProp :=
      fun s t =>
        (∃ a b, ⌜s = Any.pair a b⌝ ∗ ⌜t = Any.pair b a⌝)%I.

    Lemma comm_ist_run_0 A (run: _ -> (_ * A)) st_src st_tgt:
          comm_Ist st_src st_tgt -∗
          (⌜(run_l run st_src).2 = (run_r run st_tgt).2⌝ ∗
          comm_Ist (run_l run st_src).1 (run_r run st_tgt).1).
    Proof.
      iIntros "%". des; subst.
      unfold run_l, run_r. hss. destruct (run x).
      iPureIntro. esplits; eauto.
    Qed.

    Lemma comm_ist_run_1 A (run: _ -> (_ * A)) st_src st_tgt:
          comm_Ist st_src st_tgt -∗
          (⌜(run_r run st_src).2 = (run_l run st_tgt).2⌝ ∗
          comm_Ist (run_r run st_src).1 (run_l run st_tgt).1).
    Proof.
      iIntros "%". des; subst.
      unfold run_l, run_r. hss. destruct (run x0).
      iPureIntro. esplits; eauto.
    Qed.
        
    Theorem add_comm
      ms0 ms1
      (WF: wf (add ms1 ms0))
    :
      HModSemR.sim (add ms1 ms0) (add ms0 ms1) comm_Ist.
    Proof.
      econs; ss.
      { iIntros "[H0 H1]". iFrame. eauto. }
      { unfold add_fnsems. rewrite! List.app_length. rewrite! List.map_length. nia. }
      { 
        unfold add_fnsems. i. rewrite alist_find_app_o in MISS. des_ifs.
        rewrite alist_find_app_o. des_ifs.
        {
          exfalso. 
          eapply alist_find_fst_none in MISS. 
          eapply alist_find_fst_some in Heq0. 
          rewrite List.map_map in *.
          rewrite fun_fst_trans_r in MISS. rewrite fun_fst_trans_l in Heq0.
          eapply MISS, Heq0.
        }
        eapply alist_find_fst_none in Heq. rewrite List.map_map in Heq.
        rewrite fun_fst_trans_l in Heq. eapply alist_find_fst_notin in Heq.
        eapply alist_find_fst_notin. rewrite List.map_map.
        rewrite fun_fst_trans_r. eapply alist_find_fst_none. eauto.
      }
      i. unfold add_fnsems in *. rewrite alist_find_app_o in FIND. des_ifs.
      {
        unfold trans_l in Heq. rewrite alist_find_map in Heq. unfold o_map in Heq.
        des_ifs. exists (trans_r (fn, i)).2.
        esplits. 
        {
          rewrite alist_find_app_o. des_ifs; cycle 1.
          { s. unfold trans_r. rewrite alist_find_map. unfold o_map. des_ifs. }
          exfalso. eapply NoDup_app_disjoint.
          - inv WF. ss. unfold add_fnsems in wf_fnsems0.
            rewrite List.map_app in wf_fnsems0. eapply wf_fnsems0. 
          - eapply alist_find_fst_some in Heq0. rewrite List.map_map.
            rewrite fun_fst_trans_l. eapply Heq0.
          - eapply alist_find_fst_some in Heq. rewrite List.map_map in *.
            rewrite fun_fst_trans_l in Heq. rewrite fun_fst_trans_r. eauto.
        }
        s. ii. subst.
        (* coinduction pattern is exactly same as isim_reflR. *)
        revert st_src st_tgt. apply combine_quant.
        generalize (i y). apply combine_quant.
        eapply isim_coind. i. destruct a as [itr [st_src st_tgt]]. s.
        iIntros "(#(_ & CIH) & IST)".
        assert (CASE := case_itrH _ itr); des; subst.
        - st. eauto.
        - st. CIH.
        - st. force_r. iFrame. CIH.
        - st. force_l. iFrame. CIH.
        - destruct c. st. call; eauto. CIH.
        - destruct s. st. iPoseProof (comm_ist_run_0 with "IST") as "(%EQ & IST)".
          rewrite <- EQ. CIH.
        - destruct e; st; force_l; force_r; CIH.
      }
      {
        unfold trans_r in FIND. rewrite alist_find_map in FIND. unfold o_map in FIND.
        des_ifs. exists (trans_l (fn, i)).2.
        esplits.
        {
          rewrite alist_find_app_o. des_ifs.
          { rewrite <- Heq1. unfold trans_l. rewrite alist_find_map. unfold o_map. des_ifs. }
          exfalso. eapply alist_find_fst_none in Heq1. eapply Heq1.
          rewrite List.map_map. rewrite fun_fst_trans_l.
          eapply alist_find_fst_some. eapply Heq0.
        }
        s. ii. subst. 
        (* coinduction pattern is exactly same as isim_reflR. *)
        revert st_src st_tgt. apply combine_quant.
        generalize (i y). apply combine_quant.
        eapply isim_coind. i. destruct a as [itr [st_src st_tgt]]. s.
        iIntros "(#(_ & CIH) & IST)".
        assert (CASE := case_itrH _ itr); des; subst.
        - st. eauto.
        - st. CIH.
        - st. force_r. iFrame. CIH.
        - st. force_l. iFrame. CIH.
        - destruct c. st. call; eauto. CIH.
        - destruct s. st. iPoseProof (comm_ist_run_1 with "IST") as "(%EQ & IST)".
          rewrite <- EQ. CIH.
        - destruct e; st; force_l; force_r; CIH.
      }
    Qed. 

  End COMM.

  Section ASSOC.
    Context `{Σ: GRA.t}.

    Definition assoc_Ist: Any.t -> Any.t -> iProp :=
      fun s t =>
        (∃ a b c, ⌜s = Any.pair a (Any.pair b c)⌝ ∗ ⌜t = Any.pair (Any.pair a b) c⌝)%I.

    Lemma assoc_ist_run_0 A (run: _ -> (_ * A)) st_src st_tgt:
          assoc_Ist st_src st_tgt -∗
          (⌜(run_l run st_src).2 = (run_l (run_l run) st_tgt).2⌝ ∗
          assoc_Ist (run_l run st_src).1 (run_l (run_l run) st_tgt).1).
    Proof.
      iIntros "%". des; subst.
      unfold run_l, run_r. hss. destruct (run x).
      iPureIntro. esplits; eauto.
    Qed.

    Lemma assoc_ist_run_1 A (run: _ -> (_ * A)) st_src st_tgt:
          assoc_Ist st_src st_tgt -∗
          (⌜(run_r (run_l run) st_src).2 = (run_l (run_r run) st_tgt).2⌝ ∗
          assoc_Ist (run_r (run_l run) st_src).1 (run_l (run_r run) st_tgt).1).
    Proof.
      iIntros "%". des; subst.
      unfold run_l, run_r. hss. destruct (run x0).
      iPureIntro. esplits; eauto.
    Qed.

    Lemma assoc_ist_run_2 A (run: _ -> (_ * A)) st_src st_tgt:
          assoc_Ist st_src st_tgt -∗
          (⌜(run_r (run_r run) st_src).2 = (run_r run st_tgt).2⌝ ∗
          assoc_Ist (run_r (run_r run) st_src).1 (run_r run st_tgt).1).
    Proof.
      iIntros "%". des; subst.
      unfold run_l, run_r. hss. destruct (run x1).
      iPureIntro. esplits; eauto.
    Qed.    

    Theorem add_assoc
            ms0 ms1 ms2
            (WF: wf (add ms0 (add ms1 ms2)))
      :
      HModSemR.sim (add ms0 (add ms1 ms2)) (add (add ms0 ms1) ms2) assoc_Ist.
    Proof.
      econs; ss.
      { iIntros "(H0 & H1 & H2)". iFrame. eauto 6. }
      { 
        unfold add_fnsems. s. unfold add_fnsems. rewrite! List.app_length.
        rewrite! List.map_app. rewrite! List.app_length. 
        rewrite! List.map_length. nia. 
      }
      { 
        unfold add_fnsems. s. unfold add_fnsems. rewrite! List.map_app.
        rewrite! List.map_map. 
        i. rewrite alist_find_app_o in MISS. des_ifs.
        rewrite alist_find_app_o in MISS. des_ifs.
        rewrite alist_find_app_o. des_ifs.
        {
          exfalso. 
          eapply alist_find_fst_none in Heq, Heq0. 
          eapply alist_find_fst_some in Heq1. rewrite List.map_app in Heq1.
          rewrite! List.map_map in *. eapply in_app_or in Heq1.
          rewrite fun_fst_trans_l in Heq.
          rewrite fun_fst_trans_r_l in Heq0.
          rewrite fun_fst_trans_l_l in Heq1.
          rewrite fun_fst_trans_l_r in Heq1.
          destruct Heq1; eauto.
        }
        eapply alist_find_fst_none in MISS. rewrite List.map_map in MISS.
        rewrite fun_fst_trans_r_r in MISS. eapply alist_find_fst_notin in MISS.
        eapply alist_find_fst_notin. rewrite List.map_map.
        rewrite fun_fst_trans_r. eapply alist_find_fst_none. eauto.
      }

      i. unfold add_fnsems in *. ss. unfold add_fnsems in *.
      rewrite alist_find_app_o in FIND. des_ifs.
      {
        unfold trans_l in Heq. rewrite alist_find_map in Heq. unfold o_map in Heq.
        des_ifs. exists (trans_l (trans_l (fn, i))).2.
        esplits. 
        { 
          rewrite alist_find_app_o. des_ifs.
          {
            rewrite List.map_app in Heq. rewrite alist_find_app_o in Heq. des_ifs.
            { 
              rewrite <- Heq1. unfold trans_l. rewrite alist_find_map. unfold o_map.
              rewrite alist_find_map. unfold o_map. des_ifs.
            }
            {
              exfalso. eapply NoDup_app_disjoint.
              - inv WF. ss. unfold add_fnsems in wf_fnsems0. 
                rewrite List.map_app in wf_fnsems0. eauto.
              - eapply alist_find_fst_some in Heq0. rewrite List.map_map.
                rewrite fun_fst_trans_l. eauto.
              - s. unfold add_fnsems. rewrite List.map_map. rewrite List.map_app.
                eapply in_or_app. left. rewrite List.map_map.
                rewrite fun_fst_trans_r_l.
                unfold trans_l in Heq. rewrite alist_find_map in Heq. unfold o_map in Heq.
                unfold trans_r in Heq. rewrite alist_find_map in Heq. unfold o_map in Heq.
                des_ifs. eapply alist_find_fst_some. eauto.
            }    
          }
          {
            exfalso. eapply alist_find_fst_none in Heq. eapply Heq.
            rewrite! List.map_app. eapply in_or_app. left.
            rewrite! List.map_map. rewrite fun_fst_trans_l_l.
            eapply alist_find_fst_some. eauto.   
          }
        }
        s. ii. subst.
        revert st_src st_tgt. apply combine_quant.
        generalize (i y). apply combine_quant.
        eapply isim_coind. i. destruct a as [itr [st_src st_tgt]]. s.
        iIntros "(#(_ & CIH) & IST)".
        assert (CASE := case_itrH _ itr); des; subst.
        - st. eauto.
        - st. CIH.
        - st. force_r. iFrame. CIH.
        - st. force_l. iFrame. CIH.
        - destruct c. rewrite! translate_emb_bind. st. 
          rewrite! translate_emb_callE. call; eauto. CIH.
          (* TODO: trans (trans ) pattern not handled in 'st'. *) 
        - destruct s. st. iPoseProof (assoc_ist_run_0 with "IST") as "(%EQ & IST)".
          rewrite <- EQ. CIH.
        - destruct e; rewrite! translate_emb_bind; rewrite! translate_emb_coreE; st; force_l; force_r; CIH.
          (* TODO: trans (trans ) pattern not handled in 'st'. *) 
      }

      rewrite List.map_app in FIND. rewrite alist_find_app_o in FIND. des_ifs.      
      {
        unfold trans_r in Heq0. rewrite alist_find_map in Heq0. unfold o_map in Heq0.
        unfold trans_l in Heq0. rewrite alist_find_map in Heq0. unfold o_map in Heq0.
        des_ifs. exists (trans_l (trans_r (fn, i0))).2.
        esplits.
        { 
          rewrite alist_find_app_o. des_ifs.
          {
            rewrite List.map_app in Heq1. rewrite alist_find_app_o in Heq1. des_ifs.
            {
              exfalso. eapply alist_find_fst_none in Heq. eapply Heq.
              rewrite List.map_map. rewrite fun_fst_trans_l.
              eapply alist_find_fst_some in Heq2. rewrite! List.map_map in Heq2.
              rewrite fun_fst_trans_l_l in Heq2. eauto. 
            }
            {
              rewrite <- Heq1. unfold trans_l. rewrite alist_find_map. unfold o_map.
              unfold trans_r. rewrite alist_find_map. unfold o_map. des_ifs.
            }
          }
          {
            exfalso. rewrite List.map_app in Heq1. eapply alist_find_fst_none in Heq1.
            eapply Heq1. rewrite List.map_app. eapply in_or_app. right.
            rewrite! List.map_map. rewrite fun_fst_trans_l_r.
            eapply alist_find_fst_some. eauto.
          }
        }
        s. ii. subst.
        Local Ltac CIH := 
        iApply isim_progress; iApply isim_base;
        match goal with [|- context[_ ?R _ _ _ (?st_src, _ _ (_ ?itr)) (?st_tgt, _)]] =>
          iApply ("CIH" $! (@existT _ (λ _, _) itr (@existT _ (λ _, _) st_src st_tgt))); eauto
        end.  
        revert st_src st_tgt. apply combine_quant.
        generalize (i0 y). apply combine_quant.
        eapply isim_coind. i. destruct a as [itr [st_src st_tgt]]. s.
        iIntros "(#(_ & CIH) & IST)".
        assert (CASE := case_itrH _ itr); des; subst.
        - st. eauto.
        - st. CIH.
        - st. rewrite! translate_emb_assume. st. force_r. iFrame. CIH.
        - st. rewrite! translate_emb_guarantee. st. force_l. iFrame. CIH.
        - destruct c. rewrite! translate_emb_bind. st. 
          rewrite! translate_emb_callE. call; eauto. CIH.
        - destruct s. st. iPoseProof (assoc_ist_run_1 with "IST") as "(%EQ & IST)".
          rewrite <- EQ. CIH.
        - destruct e; rewrite! translate_emb_bind; rewrite! translate_emb_coreE; st; force_l; force_r; CIH.
      }
      
      {
        unfold trans_r in FIND. rewrite alist_find_map in FIND. unfold o_map in FIND.
        unfold trans_l in FIND. rewrite alist_find_map in FIND. unfold o_map in FIND.
        des_ifs. exists (trans_r (fn, i0)).2.
        esplits.
        { 
          rewrite alist_find_app_o. des_ifs.
          {
            exfalso. rewrite List.map_app in Heq1. rewrite alist_find_app_o in Heq1.
            des_ifs.
            - eapply alist_find_fst_some in Heq3. eapply alist_find_fst_none in Heq.
              eapply Heq. rewrite! List.map_map in *. rewrite fun_fst_trans_l.
              rewrite fun_fst_trans_l_l in Heq3. eauto.
            - eapply alist_find_fst_some in Heq1. eapply alist_find_fst_none in Heq0.
              eapply Heq0. rewrite! List.map_map in *. rewrite fun_fst_trans_r_l.
              rewrite fun_fst_trans_l_r in Heq1. eauto.     
          } 
          { unfold trans_r. rewrite alist_find_map. unfold o_map. des_ifs. }
        }

        s. ii. subst.
        revert st_src st_tgt. apply combine_quant.
        generalize (i0 y). apply combine_quant.
        eapply isim_coind. i. destruct a as [itr [st_src st_tgt]]. s.
        iIntros "(#(_ & CIH) & IST)".
        assert (CASE := case_itrH _ itr); des; subst.
        - st. eauto.
        - st. CIH.
        - st. force_r. iFrame. CIH.
        - st. force_l. iFrame. CIH.
        - destruct c. rewrite! translate_emb_bind. st. 
          rewrite! translate_emb_callE. call; eauto. CIH.
        - destruct s. st. iPoseProof (assoc_ist_run_2 with "IST") as "(%EQ & IST)".
          rewrite <- EQ. CIH.
        - destruct e; rewrite! translate_emb_bind; rewrite! translate_emb_coreE; st; force_l; force_r; CIH.
      }
    Qed.
      
  End ASSOC.

End HModAlgebra.


(* Ltac CIH :=
iApply isim_progress; iApply isim_base;
match goal with [|- context[_ ?R _ _ _ (?st_src, _ _ ?itr) (?st_tgt, _)]] =>
  iApply ("CIH" $! (@existT _ (λ _, _) itr (@existT _ (λ _, _) st_src st_tgt))); eauto
end. *)