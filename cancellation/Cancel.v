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
Require Import MainAdequacy CtxRefine CtxRefineFacts ClosedAdequacy.
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
      lbody <- (alist_find fn ms.(HModSem.fnsems))!;;
      HModSem.sandbox_body lbody args.
      
  Definition interp_hpI_fbody (ms: HModSem.t)
    : (list string * (Any.t -> itree hmodE Any.t)) -> (list string * (Any.t -> itree hmodE Any.t))
    :=
    fun '(k, b) => (k, interp_hpI_fun (prog ms) b).

  Definition wrap_sandbox scopeS: list string * (Any.t -> itree hmodE Any.t) -> list string * (Any.t -> itree hmodE Any.t)
    := 
    fun kb => (scopeS, HModSem.sandbox_body kb).

  Definition wrap_elimI ms: list string * (Any.t -> itree hmodE Any.t) -> list string * (Any.t -> itree hmodE Any.t)
    :=
    fun kb => interp_hpI_fbody ms (wrap_sandbox ms.(HModSem.scopes) kb). 

End INTERP.


Module HIRed.
  Section RED.
    Context `{Σ: GRA.t}.

    Variable ms: HModSem.t.

    Lemma iter_handle_bind i k:
      ITree.iter (handle_callE (prog ms)) (i >>= k)
      =
      x <- (ITree.iter (handle_callE (prog ms)) i);; ITree.iter (handle_callE (prog ms)) (k x).
    Proof. 
      eapply bisim_is_eq.
      eapply (@gpaco2_init _ _ _ _ (eqitC eq false false)); eauto with paco.
      revert i k. gcofix CIH. i.
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
          guclo eqit_clo_trans; eauto.
          econs; cycle 1.
          { refl. }
          { gbase. eapply CIH. }
          { instantiate (1:= eq). i. subst. refl. }
          { i. subst. refl. }
          grind. 
          replace (` x : X <- prog ms c;; (tau;; ITree.subst k (k0 x)))
          with (` r0 : X <- prog ms c;; ` x : Any.t <- (tau;; k0 r0);; k x) by grind.
          refl.
        } 
        destruct s.
        {
          grind. rewrite! bind_trigger. gstep. econs. i.
          r. grind. gstep. econs. gbase. eauto.
        }
        grind. rewrite! bind_trigger. gstep. econs. i.
        r. grind. gstep. econs. gbase. eauto.
      Unshelve. eauto with paco.
    Qed.
        
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

Section CANCEL.
  Context `{Σ: GRA.t}.

  Definition bindRR {R} Ist P : nat -> alist key Any.t * R-> alist key Any.t * R -> iProp :=
    fun nths '(st0, ret0) '(st1, ret1) => (⌜ret0 = ret1⌝ ∗ Ist nths st0 st1 ∗ P)%I.

  Definition progI fl : callE ~> itree hmodE :=
    fun _ '(Call fn args) =>
      lbody <- (alist_find fn fl)!;;
      lbody args.

  Lemma iter_bind_I fl i k:
    ITree.iter (handle_callE (progI fl)) (i >>= k)
    =
    x <- (ITree.iter (handle_callE (progI fl)) i);; ITree.iter (handle_callE (progI fl)) (k x).
  Proof. 
  Admitted.

  Lemma bind_I
    fl itr ktr
  :
    interp_hpI (progI fl) (itr >>= ktr)
    =
    x <- interp_hpI (progI fl) itr;; interp_hpI (progI fl) (ktr x).
  Proof.
    rewrite/interp_hpI iter_bind_I. refl.
  Qed.

  Lemma isim_RR_frame
      fls flt my_tid is_closed r g nths
      {R} Ist (P: iProp)
      ps pt sti_src sti_tgt
    :
      (P ∗ @isim _ fls flt Ist my_tid is_closed r g R 
            (fun nths '(sts, vs) '(stt, vt) => ⌜vs = vt⌝ ∗ Ist nths sts stt)%I
            ps pt nths sti_src sti_tgt)  
      ⊢ isim fls flt Ist my_tid is_closed r g 
         (bindRR Ist P) ps pt nths sti_src sti_tgt.
  Proof.
    Local Transparent isim.
    remember (λ (nths0 : nat) '(sts, vs) '(stt, vt), ⌜vs = vt⌝ ∗ Ist nths0 sts stt)%I.
    uiprop. i. des. subst. rename H1 into SIM. 
    unfold bindRR.
    
  Admitted.


  Lemma cancelI
      fl my_tid nths
      ps pt
      st_src st_tgt (itr: itree hmodE Any.t)
    :
    IstEq0 nths st_src st_tgt
    ⊢ isim fl fl IstEq0 my_tid true ibot ibot
       (fun nths '(st_src, v_src) '(st_tgt, v_tgt) => (⌜v_src = v_tgt⌝ ∗ IstEq0 nths st_src st_tgt)%I)
       ps pt nths (st_src, interp_hpI (progI fl) itr) (st_tgt, itr).
  Proof.
    revert itr.
    revert st_tgt. apply combine_quant.
    revert st_src. apply combine_quant.
    revert pt. apply combine_quant.
    revert ps. apply combine_quant.
    revert nths. apply combine_quant.
    eapply isim_coind. i.

    destruct a as [nths [ps [pt [st_src [st_tgt it]]]]]. s.
    iIntros "(#(_ & CIH) & Ist)".
    
    assert (CASE := case_itrH _ it); des; subst.
    - rewrite/__ HIRed.ret. step. eauto.
    - rewrite/__ HIRed.tau. steps_l. steps_r. by_coind "CIH". eauto.
    - rewrite/__ HIRed.bind_ag. 
      steps_l. force_r. iFrame. by_coind "CIH". eauto.
    - rewrite/__ HIRed.bind_ag. 
      steps_r. force_l. iFrame. steps_l. by_coind "CIH". eauto.
    - rewrite/__ HIRed.bind_sch. depdes s.
      + step. steps_l. by_coind "CIH". auto.
      + iApply isim_yield. iFrame. iIntros (? ? ? ? ?) "IST".
        steps_l. by_coind "CIH". auto.
      + steps_l. steps_r. by_coind "CIH". auto.
    - destruct c. rewrite/__ HIRed.call. steps_l. 

      destruct (alist_find fn fl) eqn:FIND; cycle 1.
      { iApply isim_call_none; ss. unfold triggerNB. steps_r. ss. }
      iApply isim_inline_tgt; eauto.
      s. ired. rewrite/__ bind_I.
      remember (
        ∀ a : nat * (bool * (bool * (alist key Any.t * (alist key Any.t * itree hmodE Any.t)))),
          IstEq0 a.1 a.2.2.2.1 a.2.2.2.2.1 -∗
          g0 Any.t (λ (nths0 : nat) '(st_src0, v_src) '(st_tgt0, v_tgt), ⌜v_src = v_tgt⌝ ∗ IstEq0 nths0 st_src0 st_tgt0) a.2.1 a.2.2.1 a.1
            (a.2.2.2.1, interp_hpI (progI fl) a.2.2.2.2.2) (a.2.2.2.2.1, a.2.2.2.2.2)
      )%I.
      iApply isim_bind; cycle 1.
      {
        instantiate (1:= (fun nths '(st_src, v_src) '(st_tgt, v_tgt) => (⌜v_src = v_tgt⌝ ∗ IstEq0 nths st_src st_tgt ∗ □b)%I)).
        iApply isim_RR_frame. iSplitR; eauto.
        rewrite Heqb. by_coind "CIH". eauto.
      }
      i. iIntros "(% & IST & #CIH)". des. subst.
      rewrite HIRed.tau. steps_l. steps_r. ired.
      by_coind "CIH". auto.
    - iDestruct "Ist" as "%". depdes s.
      + rewrite/__ HIRed.bind_pg. iApply isim_sput_src. iApply isim_sput_tgt. steps_l.
        by_coind "CIH". iPureIntro. subst. eauto.
      + rewrite/__ HIRed.bind_pg. iApply isim_sget_src. iApply isim_sget_tgt. steps_l.
        subst. unfold or_else. des_ifs; by_coind "CIH"; eauto.
    - rewrite HIRed.bind_core. depdes e.
      + steps_r. force_l. steps_l.
        instantiate (1:= q). by_coind "CIH". eauto.
      + steps_l. force_r. instantiate (1:= q).
        by_coind "CIH". auto.
      + step. steps_l. by_coind "CIH". auto.
  Qed.

End CANCEL.


(* elimI: call-inlined HMod. *)
(* elimIC: inlined & cancelled *)
(* elimC : call remaining, cancelled *)
Module HModSemAux.
  Section AUX.
    Context `{Σ: GRA.t}.
    Import HModSem.

    Program Definition to_elimI (ms: HModSem.t): HModSem.t := {|
      HModSem.scopes := ms.(scopes);
      HModSem.fnsems := List.map (map_snd (wrap_elimI ms)) (ms.(fnsems));
      (* HModSem.fnsems := List.map (map_snd (λ ksb, (ksb.1, interp_hpI_fun (prog ms) ksb.2))) (ms.(fnsems)); *)
      HModSem.initial_st := ms.(initial_st);
    |}.
    Next Obligation.
      i. depdes ms. ss. ii. unfold fnsems_scopes in *. unfold map_snd in*.
      rewrite! alist_find_map in H. unfold o_map in H.
      des_ifs; ss. 
      (* inv Heq0.
      specialize (well_scoped_fns0 fn a).
      des_ifs; ss. inv Heq. eauto. *)
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

  Let sk: Sk.t := HMod.sk md.

  Lemma cancel_call
  :
    refines (HModAux.to_elimI md, const(emp%I)) (md, const(emp%I)).
  Proof.
    eapply closed_adequacy.
    instantiate (1:= IstEq).
    econs; ss. i. r.
    econs; ss; try refl.
    { iIntros "_". iPureIntro. ss. }
    { rewrite map_length. ss. }
    { i. rewrite/__ map_map_compose fst_map_snd in IN. ss. }
    ii. hexploit FIND. i. destruct fs.

    unfold HModSemAux.to_elimI in H. s in H.
    rewrite/__ alist_find_map_snd /o_map in H. des_ifs.
    rename p into ft. exists ft.
    esplits; eauto.
    ii. subst. destruct ft.
    assert(SCP := (HMod.modsem md sk0).(HModSem.well_scoped_fns)).
    specialize (SCP fn). rewrite/fnsems_scopes Heq in SCP.
    remember (HModSem.scopes (HMod.modsem md sk0)) as scopeS. i.
    rename l into scopeT. 
    unfold HModSem.sandbox_body, interp_hpI_fun. s.
    generalize false at 1 as ps.
    generalize false at 1 as pt. intros pt ps.
    generalize (i y) as it. clear Heq IN fn FIND i y NODD NODS.
    revert st_tgt. apply combine_quant_dep.
    revert st_src. apply combine_quant_dep.
    revert SCP. apply combine_quant.
    revert scopeT. apply combine_quant_dep.
    revert HeqscopeS. apply combine_quant.
    revert scopeS. apply combine_quant_dep.
    revert pt. apply combine_quant.
    revert ps. apply combine_quant.
    revert nths. apply combine_quant.
    eapply isim_coind. i.

    destruct a as [nths [ps [pt [scopeS [HeqscopeS [scopeT [SCP [st_src [st_tgt it]]]]]]]]]. s.
    iIntros "(#(_ & CIH) & Ist)".
    
    assert (CASE := case_itrH _ it); des; subst.
    - rewrite/__ HModSB.transl_ret HIRed.ret. step. eauto.
    - rewrite/__ HModSB.transl_tau HIRed.tau. steps_l. steps_r. by_coind "CIH". eauto.
    - rewrite/__ HModSB.transl_bind HModSB.transl_ag HIRed.bind_ag. steps_l. force_r. iFrame. by_coind "CIH". eauto.
    - rewrite/__ HModSB.transl_bind HModSB.transl_ag HIRed.bind_ag. steps_r. force_l. iFrame. steps_l. by_coind "CIH". eauto.
    - rewrite/__ HModSB.transl_bind HModSB.transl_sch HIRed.bind_sch. depdes s.
      + step. steps_l. by_coind "CIH". auto.
      + rewrite/__ !HModSB.transl_bind !HModSB.transl_sch.
        iApply isim_yield. iFrame. iIntros (? ? ? ? ?) "IST".
        steps_l. by_coind "CIH". auto.
      + steps_l. steps_r. by_coind "CIH". auto.
    - destruct c. rewrite/__ HModSB.transl_bind HModSB.transl_call HIRed.call. steps_l. 
      destruct (alist_find fn (HModSem.fnsems (HMod.modsem md sk0))) eqn:FIND; cycle 1.
      { 
        iApply isim_call_none; ss.
        { rewrite/__ alist_find_map_snd FIND. ss. }
        unfold triggerNB. steps_r. ss.
      }
      destruct p. iApply isim_inline_tgt.
      { rewrite/__ alist_find_map_snd FIND. ss. }
      s. ired. rewrite/__ HIRed.bind HModSB.transl_bind.
      iStopProof.
      match goal with
      | [|-context[(□ ?P)%I]] => remember (□P)%I
      end.
      rewrite Heqb. iIntros "[#CIH Ist]". 
      iApply isim_bind; cycle 1.
      {
        instantiate (1:= bindRR IstEq0 b). 
        iApply isim_RR_frame. rewrite Heqb.  
        iSplitR; eauto. by_coind "CIH". eauto.  
      }
      i. rewrite Heqb. iIntros "(% & IST & #CIH)". des. subst.
      rewrite/__ HIRed.tau. steps_l. steps_r. ired.
      by_coind "CIH". auto.
    - depdes s.
      + rewrite/__ !HModSB.transl_bind !HModSB.transl_put. des_ifs; cycle 1. 
        { steps_r. rewrite HIRed.bind_core. force_l. steps_l. instantiate (1:= q). by_coind "CIH". eauto. }
        rewrite/__ HIRed.bind_pg HModSB.transl_bind HModSB.transl_put. des_ifs; cycle 1.
        { 
          exfalso. eapply existsb_exists in Heq. des. 
          eapply SCP in Heq. assert (XEQ:= existsb_exists). hdes.
          rewrite XEQ1 in Heq0; ss; eauto.
        } 
        iApply isim_sput_src. iApply isim_sput_tgt.
        steps_l. by_coind "CIH". iDestruct "Ist" as "%". subst. eauto.
      + rewrite/__ !HModSB.transl_bind !HModSB.transl_get. des_ifs; cycle 1.
        { steps_r. rewrite HIRed.bind_core. force_l. steps_l. instantiate (1:= q). by_coind "CIH". eauto. }
        rewrite/__ HIRed.bind_pg HModSB.transl_bind HModSB.transl_get. des_ifs; cycle 1.
        { 
          exfalso. eapply existsb_exists in Heq. des. 
          eapply SCP in Heq. assert (XEQ:= existsb_exists). hdes.
          rewrite XEQ1 in Heq0; ss; eauto.
        } 
        iApply isim_sget_src. iApply isim_sget_tgt.
        steps_l. iDestruct "Ist" as "%". subst. 
        by_coind "CIH". eauto.
    - rewrite/__ HModSB.transl_bind HModSB.transl_core HIRed.bind_core. depdes e.
      + steps_r. force_l. steps_l.
        instantiate (1:= q). by_coind "CIH". eauto.
      + steps_l. force_r. instantiate (1:= q).
        by_coind "CIH". auto.
      + step. steps_l. by_coind "CIH". auto.
    Unshelve. all: eauto.
    {
      assert(SCP0 := (HMod.modsem md sk0).(HModSem.well_scoped_fns)).
      specialize (SCP0 fn). rewrite/fnsems_scopes FIND in SCP0. eauto.
    }
  Qed.
      
  Lemma cancel_call_rev
  :
    refines (md, const(emp%I)) (HModAux.to_elimI md, const(emp%I)).
  Proof.
    eapply closed_adequacy.
    instantiate (1:= IstEq).
    econs; ss. i. r.
    econs; ss; try refl.
    { iIntros "_". iPureIntro. ss. }
    { rewrite map_length. ss. }
    { i. rewrite/__ map_map_compose fst_map_snd. ss. }
    ii. exists (wrap_elimI (HMod.modsem md sk0) fs).
    esplits.
    { rewrite/__ alist_find_map_snd /o_map. des_ifs. }
    ii. subst. destruct fs.
    assert(SCP := (HMod.modsem md sk0).(HModSem.well_scoped_fns)).
    specialize (SCP fn). rewrite/fnsems_scopes FIND in SCP.
    remember (HModSem.scopes (HMod.modsem md sk0)) as scopeS. i.
    rename l into scopeT. 
    unfold wrap_elimI. s. unfold HModSem.sandbox_body, interp_hpI_fun. s.
    generalize false at 1 as ps.
    generalize false at 1 as pt. intros pt ps.
    generalize (i y) as it. clear IN fn FIND i y NODD NODS.
    revert st_tgt. apply combine_quant_dep.
    revert st_src. apply combine_quant_dep.
    revert SCP. apply combine_quant.
    revert scopeT. apply combine_quant_dep.
    revert HeqscopeS. apply combine_quant.
    revert scopeS. apply combine_quant_dep.
    revert pt. apply combine_quant.
    revert ps. apply combine_quant.
    revert nths. apply combine_quant.
    eapply isim_coind. i.

    destruct a as [nths [ps [pt [scopeS [HeqscopeS [scopeT [SCP [st_src [st_tgt it]]]]]]]]]. s.
    iIntros "(#(_ & CIH) & Ist)".
    
    assert (CASE := case_itrH _ it); des; subst.
    - rewrite/__ HModSB.transl_ret HIRed.ret. step. eauto.
    - rewrite/__ HModSB.transl_tau HIRed.tau. steps_l. steps_r. by_coind "CIH". eauto.
    - rewrite/__ HModSB.transl_bind HModSB.transl_ag HIRed.bind_ag. steps_l. force_r. iFrame. steps_r. by_coind "CIH". eauto.
    - rewrite/__ HModSB.transl_bind HModSB.transl_ag HIRed.bind_ag. steps_r. force_l. iFrame. by_coind "CIH". eauto.
    - rewrite/__ HModSB.transl_bind HModSB.transl_sch HIRed.bind_sch. depdes s.
      + step. steps_r. by_coind "CIH". auto.
      + rewrite/__ !HModSB.transl_bind !HModSB.transl_sch.
        iApply isim_yield. iFrame. iIntros (? ? ? ? ?) "IST".
        steps_r. by_coind "CIH". auto.
      + steps_l. steps_r. by_coind "CIH". auto.
    - destruct c. rewrite/__ HModSB.transl_bind HModSB.transl_call HIRed.call. steps_r. 
      destruct (alist_find fn (HModSem.fnsems (HMod.modsem md sk0))) eqn:FIND; cycle 1.
      { s. unfold triggerNB. ired. rewrite HIRed.bind_core. steps_r. ss. }
      destruct p. iApply isim_inline_src.
      { rewrite/__ alist_find_map_snd FIND. ss. }
      s. ired. rewrite/__ HIRed.bind HModSB.transl_bind.
      iStopProof.
      match goal with
      | [|-context[(□ ?P)%I]] => remember (□P)%I
      end.
      rewrite Heqb. iIntros "[#CIH Ist]". 
      iApply isim_bind; cycle 1.
      {
        instantiate (1:= bindRR IstEq0 b). 
        iApply isim_RR_frame. rewrite Heqb.  
        iSplitR; eauto. by_coind "CIH". eauto.  
      }
      i. rewrite Heqb. iIntros "(% & IST & #CIH)". des. subst.
      rewrite/__ HIRed.tau. steps_l. steps_r. ired.
      by_coind "CIH". auto.
    - depdes s.
      + rewrite/__ !HModSB.transl_bind !HModSB.transl_put. des_ifs; cycle 1. 
        { rewrite HIRed.bind_core. steps_r. force_l. instantiate (1:= q). by_coind "CIH". eauto. }
        rewrite/__ HIRed.bind_pg HModSB.transl_bind HModSB.transl_put. des_ifs; cycle 1.
        { 
          exfalso. eapply existsb_exists in Heq. des. 
          eapply SCP in Heq. assert (XEQ:= existsb_exists). hdes.
          rewrite XEQ1 in Heq0; ss; eauto.
        } 
        iApply isim_sput_src. iApply isim_sput_tgt.
        steps_r. by_coind "CIH". iDestruct "Ist" as "%". subst. eauto.
      + rewrite/__ !HModSB.transl_bind !HModSB.transl_get. des_ifs; cycle 1.
        { rewrite HIRed.bind_core. steps_r. force_l. instantiate (1:= q). by_coind "CIH". eauto. }
        rewrite/__ HIRed.bind_pg HModSB.transl_bind HModSB.transl_get. des_ifs; cycle 1.
        { 
          exfalso. eapply existsb_exists in Heq. des. 
          eapply SCP in Heq. assert (XEQ:= existsb_exists). hdes.
          rewrite XEQ1 in Heq0; ss; eauto.
        } 
        iApply isim_sget_src. iApply isim_sget_tgt.
        steps_r. iDestruct "Ist" as "%". subst. 
        by_coind "CIH". eauto.
    - rewrite/__ HModSB.transl_bind HModSB.transl_core HIRed.bind_core. depdes e.
      + steps_r. force_l. instantiate (1:= q). by_coind "CIH". eauto.
      + steps_l. force_r. steps_r. instantiate (1:= q). by_coind "CIH". auto.
      + step. steps_r. by_coind "CIH". auto.
    Unshelve. all: try refl; eauto.
    {
      assert(SCP0 := (HMod.modsem md sk0).(HModSem.well_scoped_fns)).
      specialize (SCP0 fn). rewrite/fnsems_scopes FIND in SCP0. eauto.
    }
  Qed.

End CANCEL.