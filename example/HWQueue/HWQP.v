Require Export CRIS ImpPrelude HWQHeader SchHeader MemHeader ProphecyHeader HelpingHeader HWQI.
Require Import CallFilter ProphecyI SchTactics.

(* Prophecy-inserted intermediate module, HWQP *)
Module HWQP. Section HWQP.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !concGS}.
  Context (mn : string).

  Definition new_queue : list val → itree crisE val := λ sz,
    𝒴;;; sz <- (pargs [Tint] sz)?;;
    𝒴;;; 'q : val <- ccallU MemHdr.alloc [Vint (2 + sz)];;
    𝒴;;; '(qblk, qofs) : _ <- (pargs [Tptr] [q])?;;
    𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (qblk, qofs); Vint sz];;
    𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (qblk, qofs + 1)%Z; Vint 0];;
    𝒴;;; ITree.iter (λ (x : nat), (* initialization *)
      𝒴;;;
        if Nat.ltb x (Z.to_nat sz) 
        then 
          '_ : val <- ccallU MemHdr.store [Vptr (qblk, qofs + 2 + x)%Z; Vint 0];; Ret (inl (S x))
        else
          Ret (inr ())) 0;;;
    𝒴;;; trigger (Call (ProphecyName.new mn) ("hwq", q↑↑)↑);;; Ret q.

  Definition fnsems : fnsemmap :=
    {[fid HWQHdr.new_queue # (msk_real (msk_scp [] msk_true), (None, cfunU new_queue));
      fid HWQHdr.enqueue   # (msk_real (msk_scp [] msk_true), (None, cfunU (HWQI.enqueue)));
      fid HWQHdr.dequeue   # (msk_real (msk_scp [] msk_true), (None, fbody_trivial))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := [];
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ Mod.
End HWQP. End HWQP.

Module HWQIP. Section HWQIP.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !concGS}.
  Context (mn : string).

  Local Definition IstFull := IstProd (IstSB (Mod.scopes (HWQP.t mn)) IstEq) IstEq.
  Lemma ctxr :
    let fns mn := ProphecyName.exports mn ∪ Helping.exports mn in
    ctx_refines
      (HWQP.t mn                      ★ ProphecyI.t mn, emp)%I
      (CFilter.filter (fns mn) HWQI.t ★ ProphecyI.t mn, emp)%I.
  Proof using.
    apply main_adequacy with (Ist:=IstFull).
    init_sim.
    { iStartSim.
      steps_l. destruct Any.downcast as [sz|]; steps_l; ss. steps_r.
      rewrite /HWQP.new_queue /HWQI.new_queue.
      steps_l. steps_r. sch_yield_rr "IST".
      { case_bool_decide as Hcase; first done. exfalso; apply Hcase; split; ss. set_solver. }
      sch_yield_l. steps_l.
      destruct sz as [|[sz| | ] [|]]; steps_l; ss. steps_r.
      sch_yield_rr "IST".
      { case_bool_decide as Hcase; first done. exfalso; apply Hcase; split; ss. set_solver. }
      sch_yield_l. steps_l.
      iApply wsim_call; iFrame; clear_st; iIntros (ret st_src st_tgt) "IST".
      steps_l; steps_r; destruct Any.downcast as [|]; steps_l; ss. steps_r.
      sch_yield_rr "IST".
      { case_bool_decide as Hcase; first done. exfalso; apply Hcase; split; ss. set_solver. }
      sch_yield_l. steps_l.
      destruct v as [ | [blk ofs] | ]; steps_l; ss; steps_r.
      sch_yield_rr "IST".
      { case_bool_decide as Hcase; first done. exfalso; apply Hcase; split; ss. set_solver. }
      sch_yield_l. steps_l.
      iApply wsim_call; iFrame; clear_st; iIntros (? st_src st_tgt) "IST".
      steps_l; steps_r; destruct Any.downcast as [|]; steps_l; ss. steps_r.
      sch_yield_rr "IST".
      { case_bool_decide as Hcase; first done. exfalso; apply Hcase; split; ss. set_solver. }
      sch_yield_l. steps_l.
      iApply wsim_call; iFrame; clear_st; iIntros (? st_src st_tgt) "IST".
      steps_l; steps_r; destruct Any.downcast as [|]; steps_l; ss. steps_r.
      sch_yield_rr "IST".
      { case_bool_decide as Hcase; first done. exfalso; apply Hcase; split; ss. set_solver. }
      sch_yield_l.
      norm_l. norm_r.
      replace 0 with (Z.to_nat sz - Z.to_nat sz) by lia.
      assert (Z.to_nat sz ≤ Z.to_nat sz) as Hsz by lia.
      revert Hsz. generalize (Z.to_nat sz) at 1 5 8 as n.
      clear_st. intros n Hn. iInduction n as [|n] "IH_loop" forall (Hn st_src st_tgt).
      { replace (Z.to_nat sz - 0) with (Z.to_nat sz) by lia.
        unfold_iter_l. unfold_iter_r.
        rewrite Nat.ltb_irrefl.
        steps_r. sch_yield_rr "IST".
        { case_bool_decide as Hcase; first done. exfalso; apply Hcase; split; ss. set_solver. }
        sch_yield_rr "IST".
        { case_bool_decide as Hcase; first done. exfalso; apply Hcase; split; ss. set_solver. }
        sch_yield_l. steps_l. sch_yield_l. steps_l. inline_l. rewrite /ProphecyI.new. steps_l.
        step. iFrame. auto.
      }
      unfold_iter_l. unfold_iter_r.
      destruct Nat.ltb eqn : Heqb; last (apply Nat.ltb_ge in Heqb; lia).
      steps_l. steps_r.
      sch_yield_rr "IST".
      { case_bool_decide as Hcase; first done. exfalso; apply Hcase; split; ss. set_solver. }
      sch_yield_l. steps_l.
      iApply wsim_call; iFrame; clear_st; iIntros (? st_src st_tgt) "IST".
      steps_l. steps_r. destruct Any.downcast; steps_l; ss. steps_r.
      replace (S (Z.to_nat sz - S n)) with (Z.to_nat sz - n) by lia.
      iApply "IH_loop"; iFrame. by iPureIntro; lia.
    }
    { iStartSim. steps_l. steps_r. destruct Any.downcast; steps_l; ss. steps_r.
      rewrite /HWQI.enqueue. steps_l. steps_r.
      sch_yield_rr "IST".
       { case_bool_decide as Hcase; first done. exfalso; apply Hcase; split; ss; set_solver. }
      sch_yield_l. steps_l. destruct pargs as [[[? ?] [? ?]]|]; last steps_l; ss.
      steps_l. steps_r.
      sch_yield_rr "IST".
       { case_bool_decide as Hcase; first done. exfalso; apply Hcase; split; ss; set_solver. }
      sch_yield_l. steps_l.
      iApply wsim_call; iFrame; clear_st; iIntros (? st_src st_tgt) "IST".
      steps_l; steps_r; destruct Any.downcast as [|]; steps_l; ss. steps_r.
      sch_yield_rr "IST".
       { case_bool_decide as Hcase; first done. exfalso; apply Hcase; split; ss; set_solver. }
      sch_yield_l. steps_l.
      rewrite /MemHdr.faa. steps_l; steps_r.
      destruct pargs; steps_l; ss. steps_r.
      sch_yield_rr "IST".
       { case_bool_decide as Hcase; first done. exfalso; apply Hcase; split; ss; set_solver. }
      sch_yield_l. steps_l.
      iApply wsim_call; iFrame; clear_st; iIntros (? st_src st_tgt) "IST".
      steps_l; steps_r; destruct Any.downcast as [|]; steps_l; ss. steps_r.
      destruct pargs; steps_l; ss. steps_r.
      iApply wsim_call; iFrame; clear_st; iIntros (? st_src st_tgt) "IST".
      steps_l; steps_r; destruct Any.downcast as [|]; steps_l; ss. steps_r.
      sch_yield_rr "IST".
       { case_bool_decide as Hcase; first done. exfalso; apply Hcase; split; ss; set_solver. }
      sch_yield_l. steps_l.
      destruct pargs; steps_l; ss. steps_r.
      sch_yield_rr "IST".
       { case_bool_decide as Hcase; first done. exfalso; apply Hcase; split; ss; set_solver. }
      sch_yield_l. steps_l.
      case_match; last first.
      { steps_l; steps_r.
        sch_yield_rr "IST".
        { case_bool_decide as Hcase; first done. exfalso; apply Hcase; split; ss; set_solver. }
        sch_yield_l. steps_l.
        iApply wsim_reset.
        iStopProof. revert st_src; combine_quant st_tgt; eapply wsim_coind.
        intros ??? []; iIntros "IST". destruct_quant CIH.
        unfold_iter_l; unfold_iter_r.
        steps_l; steps_r.
        sch_yield_rr "IST".
        { case_bool_decide as Hcase; first done. exfalso; apply Hcase; split; ss; set_solver. }
        sch_yield_l. steps_l.
        by_coind CIH. iFrame.
      }
      steps_l; steps_r.
      sch_yield_rr "IST".
      { case_bool_decide as Hcase; first done. exfalso; apply Hcase; split; ss; set_solver. }
      sch_yield_l. steps_l.
      iApply wsim_call; iFrame; clear_st; iIntros (? st_src st_tgt) "IST".
      steps_l; steps_r; destruct Any.downcast as [|]; steps_l; ss. steps_r.
      sch_yield_rr "IST".
      { case_bool_decide as Hcase; first done. exfalso; apply Hcase; split; ss; set_solver. }
      sch_yield_l. steps_l.
      step. iFrame. done.
    }
    { init_simF. steps_l. steps_r. force_l _. step. iFrame. done. }
    iIntros "_"; iExists _, _, _, _. repeat iSplit; eauto.
  Qed.
End HWQIP. End HWQIP.