Require Import Coqlib.
Require Import Behavior.
Require Import AList.
Require Import SMod2HMod SMod2HModAux.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Any.
Require Export STB.
Require Import ModSim ISim HPSim.
Require Import CtxRefine CtxRefineFacts MainAdequacy ClosedAdequacy.
Require Import SimGlobal SimGlobalFacts.
Require Import SMod HMod Mod Events.
Require Import HModInline ElimRel.
Require Import Mod2ITree StRed.
Require Import CancelDef CancelCall CancelCallRev.
Require Import CancelAux0 CancelAux1 CancelAux2 CancelAux3.


Set Implicit Arguments.


Section CANCEL.
  Context `{Σ: GRA.t}.
  Variable ginv: Sk.t -> invspec.
  Variable stb: Sk.t -> gname -> option fspec.
  Variable md: SMod.t.
  Notation iProp := (iProp Σ).

  Let sk: Sk.t := SMod.sk md.
  Let ms (sk0: Sk.t) (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0) := 
    SMod.modsem md sk0.
  Let sbtb (sk0: Sk.t) (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0): alist gname (list string * fspecbody) := 
    (ms SKINCL SKWF).(SModSem.fnsems).
  Let _stb (sk0: Sk.t) (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0): alist gname (list string * fspec) := 
    List.map (map_snd (fun '(fn, fs) => (fn, fs.(fsb_fspec)))) (sbtb SKINCL SKWF).

  Hypothesis STBCOMPLETE:
    forall 
      sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
      fn scfsp (FIND: alist_find fn (_stb SKINCL SKWF) = Some scfsp), stb sk0 fn = Some scfsp.2.
  Hypothesis STBSOUND:
    forall 
      sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
      fn (FIND: alist_find fn (_stb SKINCL SKWF) = None),
      (<<NONE: stb sk0 fn = None>>).

  Let md_src: HMod.t := SModAux.to_hmod md.
  Let md_tgt: HMod.t := SMod.to_hmod ginv stb md.

  Import CancelTAC.

  Lemma cancel_aux rs0 rt0 sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0):
    ∀ rs rt srcs tgts cid st ps pt
       (WF: ✓ rs)       
       (LEN: cid < List.length srcs)
       (REL: Forall2i (thread_rel ginv stb md sk0 cid) 0 srcs tgts)
       (UPD: Own rs ==∗ Own rt)
       ,
       gpaco7 _simg (cpn7 _simg) bot7 bot7 Any.t Any.t eq ps pt
       (x <-
         interp_stateE Any.t
           (ITree.iter
              (handle_schE_callE
                 (ModSem.prog
                    (HModSem.to_mod
                       (HModSemAux.inline
                         (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0)))
              (cid, srcs))
         (Any.pair st rs↑);; Ret x.2)
         (x <-
         interp_stateE Any.t
           (ITree.iter
              (handle_schE_callE
                 (ModSem.prog
                    (HModSem.to_mod
                       (HModSemAux.inline
                         (SModSem.to_hmod (ginv sk0) 
                            (stb sk0) (SMod.modsem md sk0))) rt0))) 
              (cid, tgts))
         (Any.pair st rt↑);; Ret x.2).
  Proof.
    i. exploit Forall2i_nth; eauto. i. des.
    rename x into src, y into tgt.
    depdes x2.
    hexploit REL. i. eapply Forall2i_len in H. des.
    assert (cid < List.length tgts). { rewrite <- H. eauto. }
    assert (RELS: forall k x y (NEQ: cid ≠ k)
                    (LKX: srcs !! k = Some x)
                    (LKY: tgts !! k = Some y),
                      thread_rel ginv stb md sk0 cid k x y). 
    { i. eapply Forall2i_forall in REL; eauto. }
    clear REL. rename REL0 into REL. unfold elim_rel in REL.
    revert_until SKWF. s. gcofix CIH. i.
    _iter. _iter. rewrite x7 x8. subst. ired.
    destruct (Nat.eq_dec cid cid); ss. grind.
    assert (✓ rt). { eapply Own_wand_valid with (a1:=rs); eauto. } 
    punfold REL.  
    pattern itrS, itrT. depdes REL; ired.
    - hide_l. _coreA.
    - eapply cancel_main_ret; eauto. 
    - eapply cancel_main_tau; eauto.
    - eapply cancel_main_core; eauto.
    - eapply cancel_main_pg; eauto. 
    - eapply cancel_main_asm; eauto.
    - eapply cancel_main_grt; eauto.
    - eapply cancel_main_tid; eauto.
    - eapply cancel_main_head; eauto.
    - eapply cancel_main_tail; eauto.
    - eapply cancel_main_spawn; eauto.
    - eapply cancel_main_yield; eauto.
  Qed.

  Lemma fsb_find_spec fn l fsp fbody (sk0: Sk.t)
    (SKINCL: incl sk sk0) 
    (SKWF: Sk.wf sk0) 
    (FIND: alist_find fn (sbtb SKINCL SKWF) = Some (l, {|fsb_fspec := fsp; fsb_body := fbody|}))
  :
    alist_find fn (_stb SKINCL SKWF) = Some (l, fsp).
  Proof.
    unfold sbtb, _stb.
    rewrite alist_find_map_snd/o_map FIND. ss.
  Qed. 

  Lemma stb_find_fsb fn fsp l fspec fbody (sk0: Sk.t)
    (SKINCL: incl sk sk0) 
    (SKWF: Sk.wf sk0) 
    (STB: stb sk0 fn = Some fsp)
    (FIND: alist_find fn (sbtb SKINCL SKWF) = Some (l, {|fsb_fspec:= fspec; fsb_body := fbody|}))
  :
    fsp = fspec.
  Proof.
    specialize (STBCOMPLETE SKINCL SKWF fn).
    eapply fsb_find_spec, STBCOMPLETE in FIND; ss.
    rewrite FIND in STB. inv STB. ss. 
  Qed.

  Lemma cancel_main 
      P sk0 fsp meta rs rt r
      (EQV: Sk.equiv sk sk0) (SKWF: Sk.wf sk0)
      (WF: HModSem.wf (md_src.(HMod.modsem) sk0))
      (STB: stb sk0 "CRIS_init" = Some fsp)
      (VALID: ✓ rs)
      (EQUIV: rs ≡ r ⋅ rt)
      (PRE: Own r ⊢ fsp.(precond) 0 meta tt↑ tt↑)
      (SAT: Own rt ⊢ P sk0)
      (POST: ∀ vret ret, (fsp.(postcond) 0 meta vret ret) -∗ ⌜vret = ret⌝)
    :  
      refines_modsem
        (HModSem.to_mod ((HModAux.inline md_src).(HMod.modsem) sk0) rs)
        (HModSem.to_mod ((HModAux.inline md_tgt).(HMod.modsem) sk0) rt).
  Proof.
    r. eapply adequacy_global.
    instantiate (1:= smj_top).
    instantiate (1:= smj_top).
    unfold ModSem.compile. s. unfold ITree.map.
    destruct (alist_find "CRIS_init" (SModSem.fnsems (SMod.modsem md sk0))) eqn:E; cycle 1.
    {
      rewrite !alist_find_map/o_map E. s.
      unfold interp_modE at 2.
      rewrite/interp_schE_callE unfold_iter_eq /handle_schE_callE.
      grind. rewrite StRed.bind. grind.
      destruct (resum IFun False (Choose False)) eqn:V.
      { inv V. }
      depdes c; inv V. resub.
      rewrite [interp_stateE _ _ _]StRed.core. grind.
      ginit. st. i. ss.
    }
    rewrite !alist_find_map/o_map E. s. 
    erewrite !wrap_elimI_well_scoped; cycle 1.
    { unfold SModSem.to_hmod. s. rewrite alist_find_map_snd. instantiate (1:= "CRIS_init"). rewrite E. ss. }
    { unfold SModSemAux.to_hmod. s. rewrite alist_find_map_snd. instantiate (1:= "CRIS_init"). rewrite E. ss. }
    ired. destruct p. s.
    unfold HModSem.sandbox_body, interp_hp_fun. s.
    unfold inline_hp_fun, interp_sb_hp. s.
    unfold HoareFun.
    
    unfold interp_modE, interp_schE_callE. 
    destruct f.
    assert (SKINCL: incl sk sk0). { eapply Sk.equiv_incl. eauto. }
    pose proof (stb_find_fsb SKINCL SKWF STB E). subst.
    hide_l.
    ginit.
    rewrite !HModSB.transl_bind HModSB.transl_sch HIRed.bind_sch interp_hp_bind. s.
    rewrite interp_hp_tid. ired.
    _iter. _tau. st. _iter. _tau. st. st.
    rewrite interp_hp_tau. _iter. _tau. st. st.
    rewrite HModSB.transl_bind HModSB.transl_core HIRed.bind_core interp_hp_bind interp_hp_core. ired.
    _iter. _core. st. exists meta. st. ired. 
    _tau. st. _iter. _tau. st. st.
    rewrite interp_hp_tau. _iter. _tau. st. st.
    rewrite HModSB.transl_bind HModSB.transl_core HIRed.bind_core interp_hp_bind interp_hp_core. ired.
    _iter. _core. st. exists (tt↑). st. ired.
    _iter. _tau. st. st. st.
    rewrite interp_hp_tau. _iter. _tau. st. st.
    rewrite HModSB.transl_bind HModSB.transl_ag HIRed.bind_ag interp_hp_bind interp_hp_Assume. ired.
    _iter. _core. st. exists r. st. ired. _tau. st. 
    _iter. _sget. ired. _tau. st. st.
    hss. ired. hss. ired.
    _iter. _core. st.
    assert (V: ✓(r ⋅ rt)). { eapply valid_solve_eq; eauto. }
    exists V. ired. _tau. st. st. 
    _iter. _core. st. exists PRE. ired.
    _iter. _tau. st. st. _supd. _iter. _supd.
    _iter. _tau. st. st. rewrite interp_hp_tau. _iter. _tau. st. st.
    
    (* CRIS_init's precond all executed. *)
    reveal ITREE. 
    eapply cancel_aux; eauto; cycle 1.
    { eapply Own_equiv in EQUIV. iIntros "H". iModIntro. iApply EQUIV. eauto. }
    econs; eauto using Forall2i.
    econs; s; eauto; try rewrite bind_ret_l; ss.
    { i. specialize (POST vret ret). auto. }
    { eapply elim_rel_refl; eauto. }
    rewrite HModSB.transl_bind HIRed.bind. 
    do 2 f_equal. extensionalities.
    rewrite HModSB.transl_bind HModSB.transl_core. do 2 f_equal.
    extensionalities.
    rewrite HModSB.transl_bind HModSB.transl_ag. do 2 f_equal.
    extensionalities.
    rewrite HModSB.transl_ret. ss.
  Qed.
  
  (*** Final Theorem ***)
  Theorem cancellation P fsp meta
      (STB: ∀sk0 (EQV: Sk.equiv sk sk0) (SKWF: Sk.wf sk0), stb sk0 "CRIS_init" = Some fsp)
      (POST: ∀sk0 (EQV: Sk.equiv sk sk0) (SKWF: Sk.wf sk0) vret ret, 
                (fsp.(postcond) 0 meta vret ret) -∗ ⌜vret = ret⌝)
    :
    refines (md_src, P ∗∗ (fun _ => fsp.(precond) 0 meta tt↑ tt↑)) (md_tgt, P).
  Proof. 
    etrans.
    { eapply cancel_call_rev. }
    etrans; cycle 1.
    { eapply cancel_call. }
    r. esplits; ss.
    ii. eapply Own_split in SRC; eauto. des.
    exists a1. esplits; eauto.
    { eapply cmra_valid_op_l, valid_solve_eq; eauto. }
    {
      inv WFM. econs; eauto. s.
      do 2 rewrite List.map_map fst_map_snd.
      do 2 rewrite List.map_map fst_map_snd in wf_fns. eauto.
    }
    eapply cancel_main; eauto.
    {
      inv WFM. econs; eauto. s.
      rewrite List.map_map fst_map_snd.
      do 2 rewrite List.map_map fst_map_snd in wf_fns. eauto.
    }
    etrans; eauto. r_solve.
  Qed.
    
End CANCEL.

(* total 4min 38sec*)
