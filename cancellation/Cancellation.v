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
Require Import HModInline Cancel ElimRel.
Require Import Mod2ITree StRed.

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

  Let md_src: HMod.t := HModAux.inline (SModAux.to_hmod md). 
  Let md_tgt: HMod.t := HModAux.inline (SMod.to_hmod ginv stb md).
  
  Let ms_src: HModSem.t := HMod.modsem md_src (md_src.(HMod.sk)).
  Let ms_tgt: HModSem.t := HMod.modsem md_tgt (md_tgt.(HMod.sk)).

  Ltac hide_l := let IT := fresh "ITREE" in
    match goal with 
      | [|- simg _ _ _ ?it _] => set (IT := it) 
      | [|- gpaco7 _ _ _ _ _ _ _ _ _ ?it _] => set (IT := it)
      end; try unfold IT at 2; move IT at top.

  Ltac hide_r := let IT := fresh "ITREE" in
    match goal with 
      | [|- simg _ _ _ _ ?it] => set (IT := it) 
      | [|- gpaco7 _ _ _ _ _ _ _ _ _ _ ?it] => set (IT := it)
      end; try unfold IT at 2; move IT at top.

  Ltac reveal ITR := unfold ITR; clear ITR.

  Ltac st := prep; guclo simg_indC_spec; econs; try instantiate (1:= smj_top).
  Ltac _iter := rewrite unfold_iter_eq; ired.
  Ltac _iterI := rewrite/__ [ITree.iter (handle_callE _) _]unfold_iter_eq; ired.
  Ltac _tau := rewrite/__ !StRed.interp_tau.
  Ltac _core := rewrite/__ StRed.interp_bind StRed.interp_core; prep.
  Ltac _coreH := rewrite/__ HModSB.transl_bind HModSB.transl_core interp_hp_bind interp_hp_core; prep.
  Ltac _asm := rewrite/__ HModSB.transl_bind HModSB.transl_ag interp_hp_bind interp_hp_Assume/handle_Assume /mget_res; prep.
  Ltac _grt := rewrite/__ HModSB.transl_bind HModSB.transl_ag interp_hp_bind interp_hp_Assume/handle_Guarantee /mget_res; prep.
  Ltac _sget := rewrite/sGet !StRed.interp_bind [interp_stateE Any.t _ _]StRed.interp_st/handle_stateE. 
  Ltac __supd := rewrite/sPut /sGet !StRed.interp_bind [interp_stateE _ _ _]StRed.interp_st/handle_stateE. 
  Ltac _supd := __supd; grind; try rewrite list_insert_insert; _tau; st; st; hss; ired; hss; ired.
  Ltac _ub := rewrite/triggerUB !StRed.interp_bind StRed.interp_core; st; i; ss.
  Ltac iterL := _iter; rewrite/__ list_lookup_insert;[|auto]; ired.
  Ltac ls := rewrite !list_insert_insert.

  Ltac _coreA := _core; st; i; st; grind; _tau; st.
  Ltac _coreE x := _core; st; exists x; st; grind; _tau; st.

  Inductive Forall3i X Y Z (R: nat -> X -> Y -> Z -> Prop): nat -> list X -> list Y -> list Z -> Prop :=
  | Forall3i_nil i: Forall3i R i [] [] []
  | Forall3i_cons
      i x y z xs ys zs
      (REL: R i x y z)
      (TAIL: Forall3i R (S i) xs ys zs):
      Forall3i R i (x :: xs) (y :: ys) (z :: zs).

  Lemma Forall3i_len 
    X Y Z (R: nat -> X -> Y -> Z -> Prop) i xs ys zs
    (REL: Forall3i R i xs ys zs)
  :
    List.length xs = List.length ys /\ List.length xs = List.length zs.
  Proof.
    induction REL; s; eauto.
    des. esplits; eauto.
  Qed.

  Lemma Forall3i_nth
    X Y Z (R: nat -> X -> Y -> Z -> Prop) (i k: nat) 
    (xs: list X) (ys: list Y) (zs: list Z)
    (REL: Forall3i R i xs ys zs)
    (NTH: k < List.length xs)
  :
    ∃ x y z,
    xs !! k = Some x /\
    ys !! k = Some y /\
    zs !! k = Some z /\
    R (i + k) x y z.
  Proof.
    revert k NTH.
    induction REL; s; i; eauto.
    - nia.
    - destruct k; s.
      + replace (i + 0) with i by nia. eauto 7.
      + replace (i + S k) with (S i + k) by nia.
      eapply IHREL; nia.
  Qed.
  
  Lemma Forall3i_forall:
      ∀ X Y Z (R: nat -> X -> Y -> Z -> Prop) i xs ys zs
        (RELS: forall k x y z 
                (LKX: xs !! k = Some x)
                (LKY: ys !! k = Some y)
                (LKZ: zs !! k = Some z),
              R (i + k) x y z)
        (EQLEN1: List.length xs = List.length ys)
        (EQLEN2: List.length xs = List.length zs)
        ,
      @Forall3i X Y Z R i xs ys zs. 
  Proof. Admitted.

  Variant thread_rel sk0 (cid tid: nat) (fr: Σ) src tgt : Prop :=
  | thread_rel_init scopes fsp fbody m varg arg
      (NOC: ~ Nat.eq_dec tid cid)
      (FR: Own fr ⊢ (ginv sk0 tid) -∗ fsp.(precond) tid m varg arg)
      (SRC: src = interp_hp (HModSem.sandbox scopes (fbody varg)))
      (TGT: tgt = interp_hp (HModSem.sandbox scopes (HoareFun (ginv sk0) (stb sk0)
                    fsp.(precond) fsp.(postcond) fbody arg)))
  | thread_rel_body (Q: Any.t -> Any.t -> iProp) p itrS itrT
      (ELIM: elim_rel ginv stb md _ _ eq p itrS itrT)
      (SRC: src = interp_hp itrS)
      (TGT: tgt =
        (interp_hp
            ((if Nat.eq_dec tid cid then Ret tt else trigger (Assume (ginv sk0 tid)));;;
              vret <- itrT;; 
              (inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)))
                ( ret <- trigger (Choose Any.t);;
                  trigger (Guarantee (Q vret ret));;;
                  Ret ret)))))
  .

  (* Lemma wf_fold_lookup cid (mr fr: Σ) frs
        (LEN: cid < strings.length frs)
        (WF: URA.wf (mr ⋅ foldl (λ r1 r2 : Σ, r1 ⋅ r2) ε frs))
        (LK: frs !! cid = Some fr)
      :
        URA.wf (mr ⋅ fr).
  Proof.
    exploit nth_split. { apply LEN. }
    instantiate (1:= fr). 
    i. des. symmetry in x1.
    exploit (list_lookup_middle l1 l2 fr cid). { apply x1. }
    i. eapply nth_lookup_Some in LK. rewrite LK in x0.
    rewrite/__ x0 in WF.
    assert (foldl (λ r1 r2 : Σ, r1 ⋅ r2) ε (l1 ++ fr :: l2) = fr ⋅ foldl (λ r1 r2 : Σ, r1 ⋅ r2) (foldl (λ r1 r2 : Σ, r1 ⋅ r2) ε l1) l2).
    {
      rewrite foldl_app. s. 
      Search URA.wf.
      
    }

    eapply URA.wf_mon.
    
    instantiate (1:= ).  *)

  (* Let progS sk0 r :=  ModSem.prog (HModSem.to_mod (SModSemAux.to_hmod (SMod.modsem md sk0)) r). *)
  (* Let progT sk0 r :=  ModSem.prog (HModSem.to_mod (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)) r). *)



  
  Lemma cancel_aux sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0):
    ∀ rs frs fr mr srcs tgts ps pt cid st
       (* progS progT
       (PRS: progS = ModSem.prog (HModSem.to_mod (SModSemAux.to_hmod (SMod.modsem md sk0)) rs))
       (PRT: progT = ModSem.prog (HModSem.to_mod (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)) (rs ⋅ mr))) *)
       (WF: ✓ rs)       
       (LEN: cid < List.length frs)
       (FR: fr ≡ (foldl (fun r1 r2 => r1 ⋅ r2) ε frs))
       (WF: ✓ (rs ⋅ mr ⋅ fr))
       (* (RET: ∀fsp m vret ret (MAIN: stb sk0 "CCR_init" = Some fsp), (fsp.(postcond) 0 m vret ret -∗ ⌜vret = ret⌝)) *)
       (REL: Forall3i (thread_rel sk0 cid) 0 frs srcs tgts),
       gpaco7 _simg (cpn7 _simg) bot7 bot7 Any.t Any.t eq ps pt
       (x <-
         interp_stateE Any.t
           (ITree.iter
              (handle_schE_callE
                 (* (progS sk0 rs)) *)
                 (ModSem.prog
                    (HModSem.to_mod
                       (HModSemAux.inline
                         (SModSemAux.to_hmod (SMod.modsem md sk0))) rs)))
              (cid, srcs))
         (Any.pair st rs↑);; Ret x.2)
         (x <-
         interp_stateE Any.t
           (ITree.iter
              (handle_schE_callE
                (* (progT sk0 (rs ⋅ mr))) *)
                 (ModSem.prog
                    (HModSem.to_mod
                       (HModSemAux.inline
                         (SModSem.to_hmod (ginv sk0) 
                            (stb sk0) (SMod.modsem md sk0))) (rs ⋅ mr)))) 
              (cid, tgts))
         (Any.pair st (fr ⋅ (rs ⋅ mr))↑);; Ret x.2).
  Proof.
    (* gcofix CIH. i.
    exploit Forall3i_nth; eauto. i. des.
    rename x into fr, y into src, z into tgt.
    depdes x3.
    { exfalso. apply NOC. s. destruct Nat.eq_dec; eauto. nia. }
    hexploit REL. i. eapply Forall3i_len in H. des.
    assert (cid < List.length srcs). { rewrite <- H. eauto. }
    assert (cid < List.length tgts). { rewrite <- H0. eauto. }

    rewrite !unfold_iter_eq. unfold handle_schE_callE at 1 3.
    rewrite/__ x1 x2. s. grind.
    punfold ELIM. 
    pattern p, itrS, itrT. eapply elim_rel_tarski, ELIM. i.
    clear ELIM. *)
  Admitted.
    (* { *)
      (* hide_r. grind.  *)
      (* _core. st. exists (ε, ε, rs). st. ired. _tau. st. *)
      (* iterL. _supd. *)
      (* iterL. _core. st. assert (Own (ε ⋅ rs) -∗ |==> Own (ε ⋅ ε ⋅ rs)) by (r_solve; eauto). *)
      (* exists H3. st. ired. _tau. st. rewrite list_insert_insert. *)
      (* iterL. _core. st. assert (Own ε -∗ True) by auto.  *)
      (* exists H4. st. ired. rewrite list_insert_insert. _tau. st. *)
      (* iterL. _supd. iterL. _supd. iterL.   *)
      (* destruct (Nat.eq_dec cid 0); [|_ub]. ired. *)
      (* rewrite/__ StRed.interp_ret. ired. *)
(*  *)
      (* reveal ITREE. ired. *)
      (* _coreA. *)
      (* iterL. rewrite list_insert_insert. _tau. st. st. *)
      (* iterL. _coreA. rewrite list_insert_insert.  *)
      (* iterL. _supd. iterL. _coreA. rewrite list_insert_insert. *)
      (* iterL. _coreA. rewrite list_insert_insert.  *)
      (* iterL. _supd. iterL. _supd. iterL. _tau. st. st. rewrite list_insert_insert. *)
      (* iterL. _coreA. rewrite list_insert_insert. *)
      (* iterL. _supd. iterL. _coreA. rewrite list_insert_insert. *)
      (* iterL. _coreA. rewrite list_insert_insert.  *)
      (* iterL. _supd. iterL. _supd. iterL. *)
      (* rewrite/__ StRed.interp_ret. grind. *)
      (* Q v x -> v = x *)
      (* admit. *)
    (* } *)
    (* {  *)
      (* grind. *)
      (* assert (CASE := case_itrH _ itr). des.  *)
      (* { admit. } *)
      (* { admit. } *)
      (* { admit. } *)
      (* { admit. } *)
      (* { admit. } *)
      (* {  *)
        (* subst. depdes c.  *)
        (* hide_l.  *)
        (*  *)
        (* grind. _coreA. *)
        (* iterL. _supd. iterL. _coreA. rewrite list_insert_insert.  *)
        (* iterL. _coreA. rewrite list_insert_insert. *)
        (* iterL. _supd. iterL. _supd. *)
        (* iterL. rewrite list_insert_insert. _tau. st. *)
(*  *)
        (* assert (FINDT: alist_find fn *)
        (* (List.map (map_snd (interp_hp_fun ∘ HModSem.sandbox_body)) *)
           (* (List.map (map_snd (λ ksb : list string * fspecbody, (ksb.1, interp_sb_hp (ginv sk0) (stb sk0) ksb.2))) *)
              (* (SModSem.fnsems (SMod.modsem md sk0)))) *)
        (* = *)
        (* Some ( *)
          (* (interp_hp_fun ∘ HModSem.sandbox_body) (l, interp_sb_hp (ginv sk0) (stb sk0) {| fsb_fspec := f; fsb_body := fbody |}) *)
        (* )). *)
        (* { rewrite/__ !alist_find_map_snd /o_map x4. ss. } *)
(*  *)
        (* admit. *)
      (* } *)
      (* admit. *)
    (* } *)
    (* { *)
      (* grind. *)
      (* hide_l. _tau. st. depdes Heq. eapply inj_pair2 in x. subst. ired. *)
      (* iterL. rewrite list_insert_insert. _tau. st. st. *)
      (* iterL. _coreA. rewrite list_insert_insert.  *)
      (* iterL. rewrite list_insert_insert. _tau. st. st.  *)
      (* iterL. _coreA. rewrite list_insert_insert. *)
      (* iterL. rewrite list_insert_insert. _tau. st. st.  *)
      (* iterL. _coreA. rewrite list_insert_insert.  *)
      (* iterL. _supd. iterL. _coreA. rewrite list_insert_insert. *)
      (* iterL. _coreA. rewrite list_insert_insert.  *)
      (* iterL. _supd. iterL. _supd. iterL. rewrite list_insert_insert. _tau. st. st. *)
      (* iterL. rewrite list_insert_insert. _tau. st. *)
      (* iterL. rewrite list_insert_insert. _tau. st. st. *)
      (* iterL. _coreE x. rewrite list_insert_insert. *)
      (* iterL. rewrite list_insert_insert. _tau. st. st. *)
      (* iterL. _coreE v. rewrite list_insert_insert. *)
      (* iterL. rewrite list_insert_insert. _tau. st. st. *)
      (* iterL. _coreE c0. rewrite list_insert_insert. *)
      (* iterL. _supd. iterL.  *)
      (* assert (WFC: URA.wf (c0 ⋅ c1 ⋅ c)). { admit. }  *)
      (* _coreE WFC. rewrite list_insert_insert. *)
      (* iterL. _coreE x5. rewrite list_insert_insert. *)
      (* iterL. rewrite list_insert_insert. _tau. st. st. *)
      (* admit. *)
    (* } *)
    (* { admit. } *)

  (* Admitted. *)

  Lemma fsb_find_spec fn l fsp fbody (sk0: Sk.t)
    (SKINCL: incl sk sk0) 
    (SKWF: Sk.wf sk0) 
    (FIND: alist_find fn (sbtb SKINCL SKWF) = Some (l, {|fsb_fspec := fsp; fsb_body := fbody|}))
  :
    alist_find fn (_stb SKINCL SKWF) = Some (l, fsp).
  Proof.
    unfold sbtb, _stb.
    rewrite/__ alist_find_map_snd/o_map FIND. ss.
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

  Lemma valid_solve (a b c: Σ) :
    ✓ a -> a ≡  b ⋅ c -> ✓ b.
  Proof.
    i. eapply cmra_valid_op_l. setoid_rewrite <- H0. eauto.
  Qed.

  Lemma valid_solve_eq (a b : Σ) :
    ✓ a -> a ≡ b -> ✓ b.
  Proof.
    i. rewrite <- H0. eauto.
  Qed.

  Theorem cancellation Ps Pt
    (COND: forall sk0 (EQV: Sk.equiv sk sk0) (SKWF: Sk.wf sk0), 
      exists fsp m rt,
        (stb sk0 "CCR_init" = Some fsp) /\
        (forall rs (WF: ✓ rs) (SRC: Own rs ⊢ (Ps sk0)), ✓ (rs ⋅ rt)) /\ 
        (Own rt ⊢ (Pt sk0) ∗ (fsp.(precond) 0 m tt↑ tt↑)) /\
        (∀ m vret ret, (fsp.(postcond) 0 m vret ret) -∗ ⌜vret = ret⌝)
    )
  :
    refines (md_src, Ps) (md_tgt, Pt).
  Proof.
    econs. { s. r. refl. }
    ii. ss. specialize (COND sk0 EQV SKWF). des.
    (* resoure *)
    specialize (COND0 rs WFR SRC).
    eapply Own_split in COND1; cycle 1. 
    { eapply cmra_valid_op_r. eauto. }
    des. subst.
    exists (rs ⋅ a1). esplits; eauto.
    { eapply (@valid_solve (rs ⋅ rt) _ a2); r_solve; eauto. } 
    { iIntros "[_ P]". iStopProof. eauto. }
    {
      inv WFM. econs; eauto.
      rewrite/SModSem.to_hmod !map_map_compose !fst_map_snd.
      rewrite/SModSemAux.to_hmod !map_map_compose !fst_map_snd in wf_fns. 
      ss.
    }
    r. eapply adequacy_global_itree.
    instantiate (1:= smj_top).
    instantiate (1:= smj_top).
    unfold ModSem.compile. s. unfold ITree.map.
    (* remember (alist_encode (SModSem.initial_st (SMod.modsem md sk0))) as st. *)
    destruct (alist_find "CCR_init" (SModSem.fnsems (SMod.modsem md sk0))) eqn:E; cycle 1.
    {
      rewrite/__ !alist_find_map/o_map E. s.
      unfold interp_modE at 2.
      rewrite/interp_schE_callE unfold_iter_eq /handle_schE_callE.
      grind. rewrite/__ StRed.interp_bind. grind.
      destruct (resum IFun False (Choose False)) eqn:V.
      { inv V. }
      depdes c; inv V. resub.
      rewrite/__ [interp_stateE _ _ _]StRed.interp_core. grind.
      ginit. guclo simg_indC_spec. econs. i. ss.
    }
    rewrite/__ !alist_find_map/o_map E. s. 
    erewrite !wrap_elimI_well_scoped; cycle 1.
    { unfold SModSem.to_hmod. s. rewrite alist_find_map_snd. instantiate (1:= "CCR_init"). rewrite E. ss. }
    { unfold SModSemAux.to_hmod. s. rewrite alist_find_map_snd. instantiate (1:= "CCR_init"). rewrite E. ss. }
    ired. destruct p. s.
    unfold HModSem.sandbox_body, interp_hp_fun. s.
    unfold inline_hp_fun, interp_sb_hp. s.
    unfold HoareFun.
    
    unfold interp_modE, interp_schE_callE. 
    (* _coreH. *)
    destruct f.
    assert (SKINCL: incl sk sk0). { eapply Sk.equiv_incl. eauto. }
    pose proof (stb_find_fsb SKINCL SKWF COND E). subst.
    hide_l.
    ginit.
    rewrite/__ !HModSB.transl_bind HModSB.transl_sch HIRed.bind_sch interp_hp_bind. s.
    rewrite interp_hp_tid. ired.
    _iter. _tau. st. _iter. _tau. st. st.
    rewrite interp_hp_tau. _iter. _tau. st. st.
    rewrite/__ HModSB.transl_bind HModSB.transl_core HIRed.bind_core interp_hp_bind interp_hp_core. ired.
    _iter. _core. st. exists m. st. ired. 
    _tau. st. _iter. _tau. st. st.
    rewrite interp_hp_tau. _iter. _tau. st. st.
    rewrite/__ HModSB.transl_bind HModSB.transl_core HIRed.bind_core interp_hp_bind interp_hp_core. ired.
    _iter. _core. st. exists (tt↑). st. ired.
    _iter. _tau. st. st. st.
    rewrite interp_hp_tau. _iter. _tau. st. st.
    rewrite/__ HModSB.transl_bind HModSB.transl_ag HIRed.bind_ag interp_hp_bind interp_hp_Assume. ired.
    _iter. _core. st. exists a2. st. ired. _tau. st. 
    _iter. _sget. ired. _tau. st. st.
    hss. ired. hss. ired.
    _iter. _core. st.
    assert (✓ (a2 ⋅ (rs ⋅ a1))). 
    { 
      eapply (@valid_solve _ _ ε COND0). r_solve.
      setoid_rewrite COND1. r_solve.
    }
    exists H. ired. _tau. st. st. 
    _iter. _core. st. exists COND4. ired.
    _iter. _tau. st. st. _supd. _iter. _supd.
    _iter. _tau. st. st. rewrite interp_hp_tau. _iter. _tau. st. st.
    
    (* CCR_main's precond all executed. *)
    reveal ITREE. 
    eapply cancel_aux; eauto.
    { instantiate (1:= [a2]). ss. }
    { s. r_solve. }
    { eapply (valid_solve_eq H). r_solve. }
    econs; eauto using Forall3i.
    econs 2; s; eauto; cycle 1. 
    {
      rewrite/__ HModSB.transl_bind HIRed.bind. 
      instantiate (1:= postcond fsb_fspec 0 m).
      instantiate (1:= inline_hp _ (HModSem.sandbox l (interp_smod (ginv sk0) (stb sk0) (fsb_body tt↑)))).
      ired. repeat f_equal. 
      extensionalities.
      rewrite/__ HModSB.transl_bind HModSB.transl_core. do 2 f_equal.
      extensionalities.
      rewrite/__ HModSB.transl_bind HModSB.transl_ag. f_equal.
      extensionalities.
      rewrite HModSB.transl_ret. ss.
    }
    eapply elim_rel_refl; eauto.
    Unshelve. 
      { eapply smj_top. }
      { apply true. } 
  Qed.
  
  (*** Final Theorem ***)
  (* Theorem cancellation P: *)
    (* refines (md_src, (fun _ => emp)%I) (md_tgt, P). *)
  (* Proof. Admitted. *)

End CANCEL.
