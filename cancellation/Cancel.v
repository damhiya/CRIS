Require Import Coqlib.
Require Import sflib.
Require Import ITreelib.
Require Import STS.
Require Import AList.
Require Import Behavior.
Require Import SMod2HMod HMod2Mod.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Any.
Require Export STB.
Require Import HPSim ISim ISimClosed.
Require Import ModSimFacts.
Require Import MainAdequacy CtxRefine ClosedAdequacy.
Require Import Events SMod HMod Mod.

Set Implicit Arguments.





(* Inlining every function call in HMod. *)
Section INTERP.
  Context `{Σ: GRA.t}.

  Definition handle_callE (prog: callE ~> itree hmodE): itree hmodE Any.t -> itree hmodE (_ + Any.t)
  :=
    fun itr =>
      match observe (itr: itree hmodE Any.t) with
      | RetF rv => Ret (inr rv)
      | TauF itr' => tau;; Ret (inl itr')
      | VisF (inr1 (inr1 (inr1 (inr1 e)))) k =>
          v <- trigger e;; Ret (inl (k v))
      | VisF (inr1 (inr1 (inr1 (inl1 e)))) k => 
          v <- trigger e;; Ret (inl (k v))
      | VisF (inr1 (inr1 (inl1 c))) k =>
          Ret (inl (x <- prog _ c;; tau;; (k x)))
      | VisF (inr1 (inl1 e)) k =>
          v <- trigger e;; Ret (inl (k v))
      | VisF (inl1 e) k =>
          v <- trigger e;; Ret (inl (k v))
      end.

  Definition interp_hpI (prog: callE ~> itree hmodE) (itr: itree hmodE Any.t)
    : itree hmodE Any.t
    :=
    ITree.iter (handle_callE prog) itr.

  Definition interp_hpI_fun (prog: callE ~> itree hmodE) (body: Any.t -> itree hmodE Any.t)
    : Any.t -> itree hmodE Any.t
    :=
    fun args =>
      interp_hpI prog (body args).

  Definition prog (ms: HModSem.t) : callE ~> itree hmodE :=
    fun _ '(Call fn args) =>
      '(_, body) <- (alist_find fn ms.(HModSem.fnsems))!;;
      body args.
      (* lbody <- (alist_find fn ms.(HModSem.fnsems))!;; *)
      (* HModSem.sandbox_body lbody args. *)
    
End INTERP.


Module HIRed.
  Section RED.
    Context `{Σ: GRA.t}.

    Variable ms: HModSem.t.
  
    (* Lemma bisim_iter_handle_bind i k:
      ITree.iter (handle_callE (prog ms)) (i >>= k)
      ≅
      x <- (ITree.iter (handle_callE (prog ms)) i);; ITree.iter (handle_callE (prog ms)) (k x).
    Proof.
      ginit. revert i k. gcofix CIH. i.
      ides i.
      - grind. rewrite/__ [_ _ (Ret _)]unfold_iter_eq. grind.
        gfinal. right. eapply paco2_mon_bot; eauto.
        apply Reflexive_eqit. auto.
      - grind. rewrite! unfold_iter_eq. grind.
        gstep. econs. gstep. econs. gbase. eapply CIH.
      - rewrite! unfold_iter_eq.
        destruct e.
        {
          grind. rewrite! bind_trigger. gstep. econs. i.
          r. grind. gstep. econs. gbase. eauto.
        }
        destruct p.
        {
          grind. rewrite! bind_trigger. gstep. econs. i.
          r. grind. gstep. econs. gbase. eauto.  
        }
        destruct s.
        {
          grind. gstep. econs.
          eapply eqit_clo_trans; eauto.
          econs; cycle 1.
          { refl. }
          { eapply CIH. }
          { instantiate (1:= eq). i. subst. refl. }
          { i. subst. refl. }
          grind. 
          replace (` x : X <- prog m c;; (tau;; ITree.subst k (k0 x)))
          with (` r0 : X <- prog m c;; ` x : Any.t <- (tau;; k0 r0);; k x) by grind.
          refl.
        } 
        destruct s.
        {
          grind. rewrite! bind_trigger. gstep. econs. i.
          r. grind. gstep. econs. gbase. eauto.
        }
        grind. rewrite! bind_trigger. gstep. econs. i.
        r. grind. gstep. econs. gbase. eauto.
    Qed. *)

    Lemma iter_handle_bind i k:
      ITree.iter (handle_callE (prog ms)) (i >>= k)
      =
      x <- (ITree.iter (handle_callE (prog ms)) i);; ITree.iter (handle_callE (prog ms)) (k x).
    Proof. 
    Admitted.
      (* eapply bisim_is_eq. apply bisim_iter_handle_bind. *)
    (* Qed. *)
        
    Lemma ret 
      prog (x: Any.t)
    :
      interp_hpI prog (Ret x) = Ret x.
    Proof.
      rewrite/interp_hpI unfold_iter_eq. grind.
    Qed.

    Lemma tau
      prog t
    :
      interp_hpI prog (tau;; t) = tau;; tau;; interp_hpI prog t.
    Proof.
      rewrite/interp_hpI unfold_iter_eq. grind.
    Qed.

    Lemma bind
      itr ktr
    :
      interp_hpI (prog ms) (itr >>= ktr)
      =
      x <- interp_hpI (prog ms) itr;; interp_hpI (prog ms) (ktr x).
    Proof.
      rewrite/interp_hpI iter_handle_bind. refl.
    Qed.

    Lemma bind_sch
      X prog (e: schE X) ktr
    :
      interp_hpI prog (x <- trigger e;; ktr x) 
      =
      x <- trigger e;; tau;; interp_hpI prog (ktr x).
    Proof.
      rewrite/interp_hpI unfold_iter_eq. grind.
    Qed.

    Lemma bind_core
      X prog (e: coreE X) ktr
    :
      interp_hpI prog (x <- trigger e;; ktr x) 
      =
      x <- trigger e;; tau;; interp_hpI prog (ktr x).
    Proof.
      rewrite/interp_hpI unfold_iter_eq. grind.
    Qed.

    Lemma bind_pg
      X prog (e: pgE X) ktr
    :
      interp_hpI prog (x <- trigger e;; ktr x) 
      =
      x <- trigger e;; tau;; interp_hpI prog (ktr x).
    Proof.
      rewrite/interp_hpI unfold_iter_eq. grind.
    Qed.

    Lemma bind_ag
      X prog (e: agE X) ktr
    :
      interp_hpI prog (x <- trigger e;; ktr x) 
      =
      x <- trigger e;; tau;; interp_hpI prog (ktr x).
    Proof.
      rewrite/interp_hpI unfold_iter_eq. grind.
    Qed.

    Lemma call
      prog ktr (fn: string) arg 
    :
      interp_hpI prog (trigger (Call fn arg) >>= ktr)
      =
      tau;; interp_hpI prog (x <- prog Any.t (resum IFun Any.t (Call fn arg));; tau;; ITree.subst ktr (Ret x)).
    Proof.
      rewrite/interp_hpI unfold_iter_eq. ired. refl.
    Qed.

  End RED.
End HIRed.

(* elimI: call-inlined HMod. *)
(* elimIC: inlined & cancelled *)
(* elimC : call remaining, cancelled *)
Module HModSemAux.
  Section AUX.
    Context `{Σ: GRA.t}.
    Import HModSem.

    Program Definition to_elimI (ms: HModSem.t): HModSem.t := {|
      HModSem.scopes := ms.(scopes);
      HModSem.fnsems := List.map (map_snd (λ ksb, (ksb.1, interp_hpI_fun (prog ms) ksb.2))) (ms.(fnsems));
      HModSem.initial_st := ms.(initial_st);
    |}.
    Next Obligation.
      i. depdes ms. ss. ii. unfold fnsems_scopes in *. unfold map_snd in*.
      rewrite! alist_find_map in H. unfold o_map in H.
      des_ifs; ss. inv Heq0.
      specialize (well_scoped_fns0 fn a).
      des_ifs; ss. inv Heq. eauto.
    Qed.
    Next Obligation. ii. destruct ms. ss. eauto. Qed.
    Next Obligation. ii. destruct ms. ss. eauto. Qed.

    (* Definition to_elim ms := to_hmod ((interp_sb_hp_elim) ∘ fsb_body) ms. *)

  End AUX.
End HModSemAux.

Module HModAux.
  Section AUX.
    Context `{Σ: GRA.t}.
    Import HMod.

    Definition to_elimI (md: t) := {|
      HMod.modsem := fun sk => HModSemAux.to_elimI (md.(modsem) sk);
      HMod.sk := md.(sk);
    |}.

  End AUX.
End HModAux.


Section CANCEL.
  Context `{Σ: GRA.t}.

  Variable md: HMod.t.
  Variable ginv: Sk.t -> invspec.
  Variable stb: Sk.t -> gname -> option fspec.

  Let sk: Sk.t := HMod.sk md.
  (* Let ms (sk0: Sk.t) (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0) :=  *)
    (* HMod.modsem md sk0. *)
    
  (* (COND: forall sk0 (EQV: Sk.equiv sk sk0) (SKWF: Sk.wf sk0), 
  exists fsp m rt,
    (stb sk0 "CCR_init" = Some fsp) /\
    (forall rs (WF: URA.wf rs) (SRC: Own rs -∗ (Ps sk0)), URA.wf (rs ⋅ rt)) /\ 
    (Own rt ⊢ (Pt sk0) ∗ (fsp.(precond) 0 m tt↑ tt↑)) /\
    (∀ m vret ret, (fsp.(postcond) 0 m vret ret) -∗ ⌜vret = ret⌝)
) *)

  Lemma alist_find_elimI
      ms fn fs scopes
      (FINDS: alist_find fn (HModSem.fnsems (HModSemAux.to_elimI ms)) = Some (scopes, fs))
    :
    exists ft, fs = interp_hpI_fun (prog ms) ft.
  Proof.
  Admitted. 


  Definition bindRR {R} Ist CIH : nat -> alist key Any.t * R-> alist key Any.t * R -> iProp :=
    fun nths '(st0, ret0) '(st1, ret1) => ((⌜ret0 = ret1⌝ ∗ Ist nths st0 st1) ∗ □CIH)%I.

    (* (⌜v_src = v_tgt⌝ ∗ Ist nths st_src st_tgt))%I *)


  Lemma cancel0 IC
    scopes fs ft
    (MAIN: 
      ∀sk0 (SKINCL: incl (HMod.sk md) sk0) (SKWF: Sk.wf sk0),
        (alist_find "CRIS_main" (HModSem.fnsems (HModSemAux.to_elimI (HMod.modsem md sk0)))
          = Some (scopes, fs)) /\
        (alist_find "CRIS_main" (HModSem.fnsems (HMod.modsem md sk0))
          = Some (scopes, ft)) /\
        (fs = interp_hpI_fun (prog (HMod.modsem md sk0)) ft))
  :
    HSimC.t (HModAux.to_elimI md) md IC IstEq.
  Proof.
    econs; ss. i. r.
    econs; ss; try refl.
    { iIntros "_". iPureIntro. ss. }
    { rewrite map_length. ss. }
    { i. rewrite/__ map_map_compose fst_map_snd in IN. ss. }
    specialize (MAIN sk0 SKINCL SKWF). des.
    econs. esplits; eauto.
    assert ((scopes, fs) = fs0).
    { rewrite/HModSemAux.to_elimI MAIN in FIND. inv FIND. ss. }
    subst fs0. 
    ii. subst.
    (* iIntros "%". subst. *)
    unfold HModSem.sandbox_body, interp_hpI_fun. s.
    (* unfold HModSem.sandbox at 3 4. *)
    (* iIntros "%". subst. iStopProof. *)

    generalize scopes at 1. intros scopesS.
    generalize scopes. intros scopesT.
    (* Should be scopesT ⊆ scopesS *)

    generalize (ft y) as it. clear MAIN MAIN0 FIND ft y.
    generalize false at 1 as ps.
    generalize false at 1 as pt. intros pt ps.

    (* remember (λ (nths0 : nat) '(st_src, v_src) '(st_tgt0, v_tgt), ⌜v_src = v_tgt⌝ ∗ *)
    (* IstEq sk0 nths0 st_src st_tgt0)%I as RR. *)
    revert NODD. apply combine_quant.
    revert NODS. apply combine_quant.
    revert st_tgt. apply combine_quant_dep.
    revert st_src. apply combine_quant_dep.
    revert scopesT. apply combine_quant.
    revert scopesS. apply combine_quant_dep.
    (* revert HeqRR. apply combine_quant_dep. *)
    (* revert RR. apply combine_quant_dep. *)


    (* revert st_src. apply combine_quant_dep. *)
    revert pt. apply combine_quant_dep.
    revert ps. apply combine_quant_dep.
    revert nths. apply combine_quant.
    eapply isim_coind. i.

    (* unfold HModSem.sandbox. *)
    (* remember (
      □ ((∀ (R : Type) (RR : nat → alist key Any.t * R → alist key Any.t * R → iProp) 
      (ps pt : bool) (nths0 : nat) (src tgt : alist key Any.t * itree hmodE R),
      ibot RR ps pt nths0 src tgt -∗ g0 R RR ps pt nths0 src tgt) ∗
   (∀ a0 : nat *
           {_ : bool &
           {_ : bool &
           {_ : list string &
           (list string *
            {a3 : list (key * Any.t) &
            {a4 : list (key * Any.t) &
            NoDup (List.map fst a3) * (NoDup (List.map fst a4) * itree hmodE Any.t)}})%type}}},
      IstEq sk0 a0.1 (projT1 (projT2 (projT2 (projT2 a0.2))).2)
        (projT1 (projT2 (projT2 (projT2 (projT2 a0.2))).2)) -∗
      g0 Any.t
        (λ (nths : nat) '(st_src, v_src) '(st_tgt, v_tgt), ⌜v_src = v_tgt⌝ ∗
           IstEq sk0 nths st_src st_tgt) (projT1 a0.2) (projT1 (projT2 a0.2)) a0.1
        (projT1 (projT2 (projT2 (projT2 a0.2))).2,
        translate (HModSem.handle_sandbox (projT1 (projT2 (projT2 a0.2))))
          (interp_hpI (prog (HMod.modsem md sk0))
             (projT2 (projT2 (projT2 (projT2 (projT2 a0.2))).2)).2.2))
        (projT1 (projT2 (projT2 (projT2 (projT2 a0.2))).2),
        translate (HModSem.handle_sandbox (projT2 (projT2 (projT2 a0.2))).1)
          (projT2 (projT2 (projT2 (projT2 (projT2 a0.2))).2)).2.2)))
    )%I. *)

    (* rewrite Heqb. *)

    destruct a as [nths [ps [pt [scopeS [scopeT [st_src [st_tgt [NODS [NODD it]]]]]]]]]. s.
    iIntros "(#(_ & CIH) & Ist)".
    
    
    assert (CASE := case_itrH _ it); des; subst.
    - rewrite HIRed.ret. step. eauto.
    - rewrite HIRed.tau. steps_l. steps_r. by_coind "CIH". eauto.
    - rewrite HIRed.bind_ag. steps_l. force_r. iFrame. by_coind "CIH". eauto.
    - rewrite HIRed.bind_ag. steps_r. force_l. iFrame. steps_l. by_coind "CIH". eauto.
    - rewrite HIRed.bind_sch. depdes s.
      + step. steps_l. by_coind "CIH". auto.
      + rewrite/__ !HModSB.transl_bind !HModSB.transl_sch.
        iApply isim_yield. iFrame. iIntros (? ? ? ? ?) "IST".
        steps_l. by_coind "CIH". auto.
      + steps_l. steps_r. by_coind "CIH". auto.
    - destruct c. rewrite HIRed.call. steps_l. 
      rewrite/__ HModSB.transl_bind HModSB.transl_call.

      destruct (alist_find fn (HModSem.fnsems (HMod.modsem md sk0))) eqn:FIND; cycle 1.
      { 
        (* rewrite/__ HModSB.transl_bind HModSB.transl_call. *)
        iApply isim_call_none; ss.
        { rewrite/__ alist_find_map_snd FIND. ss. }
        unfold triggerNB. steps_r. ss.
      }
      destruct p. iApply isim_inline_tgt.
      { rewrite/__ alist_find_map_snd FIND. ss. }
      s. ired. rewrite/__ HIRed.bind HModSB.transl_bind.
      iApply isim_bind; cycle 1.
      {
        unfold HModSem.sandbox.
        instantiate (1:= bindRR IstEq0 _).
        (* instantiate (1:= EqRR ). *)
        (* by_coind "CIH".   *)
        admit.
      }
      i. iIntros "[[% IST] #CIH]". des. subst.
      rewrite HIRed.tau. steps_l. steps_r. ired.
      (* by_coind "CIH". auto. *)
      admit.
    - admit.
    - rewrite HIRed.bind_core. depdes e.
      + steps_r. force_l. steps_l.
        instantiate (1:= q). by_coind "CIH". eauto.
      + steps_l. force_r. instantiate (1:= q).
        by_coind "CIH". auto.
      + step. steps_l. by_coind "CIH". auto.
    



    assert (FINDT:= alist_find_elimI).
    specialize (FINDT _ _ _ _ FIND). des.
    esplits. 
    { instantiate (1:= (l, ft)). }

    



End CANCEL.