Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import AList.
Require Import SMod HMod Mod Events.
Require Import SMod2HMod SMod2HModElim Mod2STS.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Any.
Require Export STB.
Require Import ModSim ISim HPSim.
Require Import CtxRefine CtxRefineFacts MainAdequacy ClosedAdequacy.
Require Import SimGlobal SimGlobalFacts.
(* Require Import CancelAPC. *)

Set Implicit Arguments.

Section CANCEL.
  Context `{Σ: GRA.t}.
  Variable ginv: Sk.t -> invspec.
  Variable stb: Sk.t -> gname -> option fspec.

  Variable md: SMod.t.

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

  Lemma stb_in_alist_find
        sk0 fn fsp
        (SKINCL: incl sk sk0) 
        (SKWF: Sk.wf sk0)
        (SOME: stb sk0 fn = Some fsp)
      :
        exists l fbody, 
          alist_find fn (SModSem.fnsems (SMod.modsem md sk0)) = Some (l, {|fsb_fspec :=fsp; fsb_body := fbody|}).
  Proof.
    destruct (alist_find fn (_stb SKINCL SKWF)) eqn: FIND; cycle 1.
    { eapply STBSOUND in FIND. des. clarify. }
    unfold _stb, sbtb, ms in FIND.
    rewrite/__ alist_find_map_snd/o_map in FIND. des_ifs.
    destruct p0, f. exists l, fsb_body. repeat f_equal.
    assert (alist_find fn (_stb SKINCL SKWF) = Some (l, fsb_fspec)).
    { rewrite/_stb alist_find_map_snd /o_map /sbtb /ms Heq. ss. }
    eapply STBCOMPLETE in H. ss. rewrite SOME in H. inv H. ss.
  Qed.

  Let md_elim: HMod.t := SModElim.to_elim md. 
  Let md_tgt: HMod.t := SMod.to_hmod ginv stb md.
  
  Let ms_elim: HModSem.t := HMod.modsem md_elim (md_elim.(HMod.sk)).
  Let ms_tgt: HModSem.t := HMod.modsem md_tgt (md_tgt.(HMod.sk)).

  (* Sk.t lemmas *)
  (* sk0: list (string * Any.t) *)
  (* SKINCL: incl (SMod.sk md) sk0 *)
  (* SKWF: Sk.wf sk0 *)

  Definition hmod_elim_head X P : Any.t -> itree hmodE ((nat * X * nat * X) * Any.t)
    :=
    fun varg =>               
      my_tid <- trigger Tid;;
      x <- trigger (Choose X);; 
      arg <- trigger (Choose Any.t);;
      trigger (Guarantee (P my_tid x varg arg));;;
      my_tid' <- trigger Tid;;
      x' <- trigger (Take X);;
      varg' <- trigger (Take _);;
      trigger (Assume (P my_tid' x' varg' arg));;;
      Ret ((my_tid, x, my_tid', x'), varg').

  Definition hmod_elim_tail X Q : (nat * X * nat * X) -> Any.t -> itree hmodE Any.t
    :=
    fun '(my_tid, x, my_tid', x') vret' =>
      ret <- trigger (Choose Any.t);;
      trigger (Guarantee (Q my_tid' x' vret' ret));;;
      vret <- trigger (Take Any.t);;
      trigger (Assume (Q my_tid x vret ret));;;
      Ret vret.
      
  Inductive hmod_elim_rel: itree hmodE Any.t -> itree hmodE Any.t -> Prop
    :=
  | hmod_elim_rel_base v
    :
    hmod_elim_rel (Ret v) (Ret v)

  | hmod_elim_rel_add itr ktrS ktrT
      (ITR: forall (v: Any.t), hmod_elim_rel (ktrS v) (ktrT v))
    :
    hmod_elim_rel (itr >>= ktrS) (itr >>= ktrT)

  | hmod_elim_rel_head X P v src tgt ktrS ktrT
      (KTR: forall m v, hmod_elim_rel (ktrS v) (ktrT (m,v)))
      (EQS: src = ktrS v)
      (EQT: tgt = (@hmod_elim_head X P v) >>= ktrT)
    :
    hmod_elim_rel src tgt
                  
  | hmod_elim_rel_tail X Q m v src tgt ktrS ktrT
      (KTR: forall v, hmod_elim_rel (ktrS v) (ktrT v))
      (EQS: src = ktrS v)
      (EQT: tgt = (@hmod_elim_tail X Q m v) >>= ktrT)
    :
    hmod_elim_rel src tgt
  .

  (*** ***) 
  Variant thread_rel sk0 (cid tid: nat) (fr: Σ) src tgt : Prop :=
  | thread_rel_init scopes fsp fbody m varg arg
      (NOC: ~ Nat.eq_dec tid cid)
      (FR: Own fr ⊢ (ginv sk0 tid) -∗ fsp.(precond) tid m varg arg)
      (SRC: src = 
        (interp_hp (HModSem.sandbox scopes (interp_smod_elim (fbody varg))) ε)
        >>= hp_fun_tail)
      (TGT: tgt =
        (interp_hp
             (HModSem.sandbox scopes (HoareFun (ginv sk0) (stb sk0)
                  fsp.(precond) fsp.(postcond) fbody arg)) ε) 
        >>= hp_fun_tail)
  | thread_rel_body (Q: Any.t -> Any.t -> iProp) itrS itrT
      (ELIM: hmod_elim_rel itrS itrT)
      (SRC: src = (interp_hp itrS ε) >>= hp_fun_tail)
      (TGT: tgt =
        (interp_hp
         ((if Nat.eq_dec tid cid then Ret tt else trigger (Assume (ginv sk0 tid)));;;
           vret <- itrT;; 
           ret <- trigger (Choose Any.t);;
           trigger (Guarantee (Q vret ret));;;
           Ret ret) fr)
        >>= hp_fun_tail)
  .

  (*** ***) 
  (* Variant thread_rel sk0 (cid tid: nat) (fr: Σ) src tgt : Prop := *)
  (* | thread_rel_init scopes fsp fbody m varg arg *)
  (*     (NOC: ~ Nat.eq_dec tid cid) *)
  (*     (FR: Own fr ⊢ (ginv sk0 tid) -∗ fsp.(precond) tid m varg arg) *)
  (*     (SRC: src =  *)
  (*       (interp_hp (HModSem.sandbox scopes (interp_smod_elim (fbody varg))) ε) *)
  (*       >>= hp_fun_tail) *)
  (*     (TGT: tgt = *)
  (*       (interp_hp *)
  (*            (HModSem.sandbox scopes (HoareFun (ginv sk0) (stb sk0) *)
  (*                 fsp.(precond) fsp.(postcond) fbody arg)) ε)  *)
  (*       >>= hp_fun_tail) *)
  (* | thread_rel_body scopes fsp m itr *)
  (*     (SRC: src = *)
  (*       (interp_hp (HModSem.sandbox scopes (interp_smod_elim itr)) ε) *)
  (*       >>= hp_fun_tail) *)
  (*     (TGT: tgt = *)
  (*       (interp_hp *)
  (*         (HModSem.sandbox scopes  *)
  (*           (  *)
  (*             (if Nat.eq_dec tid cid then Ret tt  *)
  (*             else trigger (Assume (ginv sk0 tid)) );;; *)
  (*             vret <- interp_smod (ginv sk0) (stb sk0) itr;;  *)
  (*             ret <- trigger (Choose Any.t);; *)
  (*             trigger (Guarantee (fsp.(postcond) tid m vret ret));;; *)
  (*             Ret ret)) fr) *)
  (*       >>= hp_fun_tail) *)
  (* . *)

  Lemma fsb_find_spec fn l fsp fbody sk0
    (SKINCL: incl sk sk0) 
    (SKWF: Sk.wf sk0) 
    (FIND: alist_find fn (sbtb SKINCL SKWF) = Some (l, {|fsb_fspec := fsp; fsb_body := fbody|}))
  :
    alist_find fn (_stb SKINCL SKWF) = Some (l, fsp).
  Proof.
    unfold sbtb, _stb.
    rewrite/__ alist_find_map_snd/o_map FIND. ss.
  Qed. 

  Lemma stb_find_fsb fn fsp l fspec fbody sk0
    (SKINCL: incl sk sk0) 
    (SKWF: Sk.wf sk0) 
    (STB: stb sk0 fn = Some fsp)
    (FIND: alist_find fn (sbtb SKINCL SKWF) = Some (l, {|fsb_fspec:= fspec; fsb_body := fbody|}))
  :
    fsp = fspec.
  Proof.
    specialize (STBCOMPLETE SKINCL SKWF fn).
    eapply fsb_find_spec, STBCOMPLETE in FIND. ss.
    rewrite FIND in STB. inv STB. ss. 
  Qed.

  (* Lemma fsb_meta_eq fsp fbody:
    meta  *)
  Lemma interp_st
        E st0 T e
    :
      @interp_stateE E T (trigger e) st0 =
      '(st1, r) <- handle_stateE _ e st0;;
      tau;; Ret (st1, r).
  Proof.
    unfold interp_stateE. grind. destruct x. grind.
  Qed.

  Lemma interp_ret
        E A st0 v
    :
      @interp_stateE E A (Ret v) st0 = Ret (st0, v)
  .
  Proof. 
    unfold interp_stateE. grind.
  Qed.


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
  Ltac _iter := rewrite unfold_iter_eq; grind.
  Ltac _tau := rewrite/__ !StRed.interp_tau.
  Ltac _core := rewrite/__ StRed.interp_bind StRed.interp_core; prep.
  Ltac _coreH := rewrite/__ HModSB.transl_bind HModSB.transl_core interp_hp_bind interp_hp_core; prep.
  Ltac _asm := rewrite/__ HModSB.transl_bind HModSB.transl_ag interp_hp_bind interp_hp_Assume/handle_Assume /mget_res; prep.
  Ltac _grt := rewrite/__ HModSB.transl_bind HModSB.transl_ag interp_hp_bind interp_hp_Assume/handle_Guarantee /mget_res; prep.
  (* Ltac _sget := rewrite/sGet !StRed.interp_bind [interp_stateE Any.t _ _]interp_st/handle_stateE.  *)
  Ltac __supd := rewrite/sPut /sGet !StRed.interp_bind [interp_stateE _ _ _]interp_st/handle_stateE. 
  Ltac _supd := __supd; grind; try rewrite list_insert_insert; _tau; st; st; hss; grind; hss; grind.
  Ltac _ub := rewrite/triggerUB !StRed.interp_bind StRed.interp_core; st; i; ss.


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

  Lemma cancel_aux sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0):
    ∀ rs frs mr srcs tgts ps pt cid st
      (WF: URA.wf rs)       
      (LEN: cid < List.length frs)
      (WF: URA.wf (rs ⋅ mr ⋅ (foldl (fun r1 r2 => r1 ⋅ r2) ε frs)))
      (REL: Forall3i (thread_rel sk0 cid) 0 frs srcs tgts),
      gpaco7 _simg (cpn7 _simg) bot7 bot7 Any.t Any.t eq ps pt
      (x <-
        interp_stateE Any.t
          (ITree.iter
             (handle_schE_callE
                (ModSem.prog
                   (HModSem.to_mod
                      (SModSemElim.to_elim (SMod.modsem md sk0)) rs)))
             (cid, srcs))
        (Any.pair st rs↑);; Ret x.2)
      (x <-
        interp_stateE Any.t
          (ITree.iter
             (handle_schE_callE
                (ModSem.prog
                   (HModSem.to_mod
                      (SModSem.to_hmod (ginv sk0) 
                         (stb sk0) (SMod.modsem md sk0)) mr))) 
             (cid, tgts))
        (Any.pair st (rs ⋅ mr)↑);; Ret x.2).
  Proof.
    gcofix CIH. i.
    exploit Forall3i_nth; eauto. i. des.
    rename x into fr, y into src, z into tgt.
    depdes x3.
    { exfalso. apply NOC. s. destruct Nat.eq_dec; eauto. nia. }
    hexploit REL. i. eapply Forall3i_len in H. des.
    assert (cid < List.length srcs). { rewrite <- H. eauto. }
    assert (cid < List.length tgts). { rewrite <- H0. eauto. }

    rewrite !unfold_iter_eq. unfold handle_schE_callE at 1 3.
    rewrite/__ x1 x2. subst. s. grind.
    
    depdes ELIM.
    { grind.
    }
    {
    }
    {
    }
    {
    }

    
    
    
    
    
    assert (CASE := case_itrS itr). des. 

    { admit. }
    { admit. }
    { admit. }
    { admit. }

    

    (* RET *)
    (* {
      subst.
      destruct (Nat.eq_dec cid 0); cycle 1.
      {
        (* eapply list_lookup_insert in H1.

        hide_r. grind. _core. st.
        exists (ε, ε, ε). st. grind.
        _tau. st. rewrite unfold_iter_eq. 
        unfold mget_res, sGet at 1. 
        grind. rewrite/__ H1. grind. _supd.
        _iter. rewrite/__ list_insert_insert H1. grind.
        _core. st. eexists. st. grind. _tau. st.
        _iter. rewrite/__ list_insert_insert H1. grind.
        _core. st. eexists. st. grind. _tau. st. 
        unfold mget_res, mput_res, guarantee.
        _iter. rewrite/__ list_insert_insert H1. grind. _supd.
        _iter. rewrite/__ list_insert_insert H1. grind. _supd.
        _iter. rewrite/__ list_insert_insert H1. grind. _ub. *)
        admit.
      }
      subst cid. grind.
      hide_r. (* execute src *)
      eapply list_lookup_insert in H1.
      _core. st. exists (ε, ε, ε). st. grind. _tau. st.
      _iter. rewrite/__ H1. grind. _supd.
      _iter. rewrite/__ list_insert_insert H1. grind.
      _core. st. eexists. st. grind. _tau. st.
      _iter. rewrite/__ list_insert_insert H1. grind.
      _core. st. eexists. st. grind. _tau. st.
      _iter. rewrite/__ list_insert_insert H1. grind. _supd.
      _iter. rewrite/__ list_insert_insert H1. grind. _supd.
      _iter. rewrite/__ list_insert_insert H1. grind.
      rewrite/__ interp_ret. grind.
      (* src end *)
      hide_l.
      reveal ITREE. (* execute tgt*)
      _core. st. i. st. grind. _tau. st.
      _iter. rewrite list_lookup_insert;[|apply H2].
      grind. _tau. st. st. 
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2].
      grind. _core. st. i. st. grind.
      _tau. st. 
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind. _supd.
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind. 
      _core. st. i. st. grind. _tau. st.
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind. 
      _core. st. i. st. grind. _tau. st.
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind. _supd.
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind. _supd.
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind. 
      _tau. st. st.
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind. 
      _core. st. i. st. grind. _tau. st.
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind. _supd.
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind. 
      _core. st. i. st. grind. _tau. st. 
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind. 
      _core. st. i. st. grind. _tau. st. 
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind. _supd. 
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind. _supd. 
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind. 
      rewrite/__ interp_ret. grind.
      reveal ITREE0.
      st.


      (* eapply list_lookup_insert in H2. *)

      (* rewrite H2. grind.  *)

      admit.

      (* (<<RET: forall ret_src ret_tgt r
      (WFR: URA.wf r)
      (POST: main_fsp.(postcond) None x ret_src ret_tgt r),
ret_src = ret_tgt>>) *)
    } *)

    (* TAU - Proved *)
    (* {
      subst.
      (* hexploit REL. i. eapply Forall3i_len in H. des.
      assert (cid < List.length srcs). { rewrite <- H. eauto. }
      assert (cid < List.length tgts). { rewrite <- H0. eauto. } *)
      (* eapply list_lookup_insert in H1, H2. *)

      hide_r. grind. _tau. st. st. hide_l.
      reveal ITREE.
      grind. _tau. st. st.
      
      (* gstep. econs. grind. econs 4. econs. econs. *)
    
      reveal ITREE0.
      instantiate (1:= smj_top).
      instantiate (1:= smj_top).
      gstep. econs. econs; cycle 1.
      { unfold smj_ltb. instantiate (1:= smj_bot). ss. }
      { unfold smj_ltb. instantiate (1:= smj_bot). ss. }
      gbase. eapply CIH; eauto.
      move REL at bottom.

      eapply Forall3i_forall.
      {
        i. destruct (Nat.eq_dec k cid).
        {
          subst k. rewrite list_lookup_insert in LKY; [|apply H1].
          rewrite list_lookup_insert in LKZ; [|apply H2].
          depdes LKY. econs 2.
          {
            instantiate (1:= itrS'). 
            generalize (interp_smod_elim itrS') as itrS''. i.
            unfold HModSem.sandbox. instantiate (1:= scopes).
            generalize (translate (HModSem.handle_sandbox scopes) itrS'') as itrS'''.
            i. f_equal.
          }
          {
            unfold HModSem.sandbox. 
            destruct (Nat.eq_dec (0 + cid) cid); try nia.
            grind.
          }
        }
        eapply Forall3i_nth in REL; cycle 1.
        { eapply lookup_lt_is_Some. econs. eauto. }
        des. assert (cid ≠ k) by nia.
        rewrite (list_lookup_insert_ne srcs cid k _ H3) in LKY.
        rewrite (list_lookup_insert_ne tgts cid k _ H3) in LKZ.
        rewrite LKX in REL. 
        rewrite LKY in REL0. 
        rewrite LKZ in REL1.
        depdes REL REL0 REL1. apply REL2. 
      }
      { rewrite/__ H insert_length. ss. }
      { rewrite/__ H0 insert_length. ss. }
    } *)

    (* ASM *)
    (* {
      subst.
      (* execute src *)
      hide_r. grind. _core. st. i. st. grind. _tau. st.
      _iter. rewrite/__ list_lookup_insert;[|apply H1]. grind. _supd.
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H1]. grind.
      _core. st. i. st. rewrite !bind_ret_l. _tau. st.
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H1]. grind.
      _core. st. i. st. grind. _tau. st.
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H1]. grind.
      _tau. st. st.
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H1]. grind.
      _tau. st. st.
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H1]. grind.
      reveal ITREE. hide_l. move ITREE at top.
      grind. _core. st. exists x. st. grind. _tau. st.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind. _supd.
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind.
      _core. st. (* WF???? *)

    } *)

    (* GRT *)
    (* {
      subst.
      (* execute tgt *)
      hide_l. grind. _core. st. i. st. grind. _tau. st.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind. _supd.
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind.
      _core. st. i. st. rewrite !bind_ret_l. _tau. st.
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind.
      _core. st. i. st. grind. _tau. st.
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind. _supd.
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind. _supd.
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind.
      _tau. st. st.
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind.
      _tau. st. st.

      reveal ITREE. hide_r. move ITREE at top.
      grind. _core. st. exists (c0, c1, c). st. grind. _tau. st.
      _iter. rewrite/__ list_lookup_insert;[|apply H1]. grind. _supd.
      _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H1]. grind.
      _core. st. (* WF???? *)

    } *)

    (* SCH *)
    { admit. }

    (* CALL *)
    (* { admit. } *)
    {
      subst. depdes c.
      hide_l.
      rewrite/__ !SModRed.interp_bind SModRed.interp_call. s.
      destruct (stb sk0 fn) eqn:STBFN; s; cycle 1.
      {
        rewrite/triggerNB !HModSB.transl_bind HModSB.transl_core !interp_hp_bind interp_hp_core. grind.
        _core. st. i. ss.
      }
      grind. _core. st. i. rename x into m0. st. grind. _tau. st.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind.
      rewrite list_insert_insert. _tau. st. st.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind.
      (* precond *)
      _core. st. intro arg. st. grind.
      rewrite list_insert_insert. _tau. st.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind.
      rewrite list_insert_insert. _tau. st. st.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind.
      _core. st. i. st. grind. 
      rewrite list_insert_insert. _tau. st. 
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind. _supd.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind.
      _core. st. intro RECONF. st. grind. 
      rewrite list_insert_insert. _tau. st.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind.
      _core. st. intros PRECOND. st. grind. 
      rewrite list_insert_insert. _tau. st.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind. _supd.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind. _supd.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind.
      rewrite list_insert_insert. _tau. st. st.
      (* call - tgt *)
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind.
      _core. st. i. st. grind. 
      rewrite list_insert_insert. _tau. st.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind. _supd.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind.
      _core. st. intros RECONF0. st. grind. 
      rewrite list_insert_insert. _tau. st.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind.
      _core. st. i. st. grind.
      rewrite list_insert_insert. _tau. st.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind. _supd.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind. _supd.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind.
      rewrite list_insert_insert. _tau. st. 
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind.
      exploit (stb_in_alist_find SKINCL SKWF). { apply STBFN. }
      i. des.
      assert (FINDT: alist_find fn
      (List.map (map_snd (interp_hp_fun ∘ HModSem.sandbox_body))
         (List.map (map_snd (λ ksb : list string * fspecbody, (ksb.1, interp_sb_hp (ginv sk0) (stb sk0) ksb.2)))
            (SModSem.fnsems (SMod.modsem md sk0))))
      =
      Some (
        (interp_hp_fun ∘ HModSem.sandbox_body) (l, interp_sb_hp (ginv sk0) (stb sk0) {| fsb_fspec := f; fsb_body := fbody |})
      )).
      { rewrite/__ !alist_find_map_snd /o_map x4. ss. }
      (* function body inlined (tgt) *)
      rewrite FINDT. grind. 
      _core. st. exists m0. st. grind. rewrite list_insert_insert.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind. 
      rewrite list_insert_insert. _tau. do 3 st.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind. 
      _core. st. exists args. st. grind. 
      rewrite list_insert_insert. _tau. st.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind. 
      rewrite list_insert_insert. _tau. st. st.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind. 
      _core. st. exists c0. st. grind. 
      rewrite list_insert_insert. _tau. st.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind. _supd.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind. 
      _core. st. assert (URA.wf (c0 ⋅ ε ⋅ c2)). { admit. } exists H3. st. grind. 
      rewrite list_insert_insert. _tau. st.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind. 
      _core. st. exists PRECOND. st. grind. 
      rewrite list_insert_insert. _tau. st.
      _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind. 
      rewrite list_insert_insert. _tau. st. st.

      (* call - src *)
      reveal ITREE. hide_r. move ITREE at top.
      rewrite/__ ElimRed.interp_bind ElimRed.interp_call !HModSB.transl_bind HModSB.transl_call.
      rewrite/__ !interp_hp_bind interp_hp_call. grind.
      _core. st. exists (ε, ε, rs). st. grind. _tau. st.
      _iter. rewrite/__ list_lookup_insert;[|apply H1]. grind. _supd.
      _iter. rewrite/__ list_lookup_insert;[|apply H1]. grind.
      assert (Own (ε ⋅ rs) ⊢|==> Own (ε ⋅ ε ⋅ rs)). { r_solve; eauto. }
      _core. st. exists H4. st. grind. 
      rewrite list_insert_insert. _tau. st.
      _iter. rewrite/__ list_lookup_insert;[|apply H1]. grind.
      _core. st. assert (Own ε ⊢ True) by eauto. exists H5. st. grind.
      rewrite list_insert_insert. _tau. st.
      _iter. rewrite/__ list_lookup_insert;[|apply H1]. grind. _supd.
      _iter. rewrite/__ list_lookup_insert;[|apply H1]. grind. _supd.
      _iter. rewrite/__ list_lookup_insert;[|apply H1]. grind.
      rewrite list_insert_insert. _tau. st.
      assert (FINDS: alist_find fn
      (List.map (map_snd (interp_hp_fun ∘ HModSem.sandbox_body))
         (List.map (map_snd (λ ksb : list string * fspecbody, (ksb.1, interp_sb_hp_elim (fsb_body ksb.2))))
            (SModSem.fnsems (SMod.modsem md sk0))))
      =
      Some (
        (interp_hp_fun ∘ HModSem.sandbox_body) (l, interp_sb_hp_elim fbody)
      )).
      { rewrite/__ !alist_find_map_snd /o_map x4. ss. }
      rewrite FINDS. grind. 
      unfold interp_hp_fun, interp_hp_body, HModSem.sandbox_body, interp_sb_hp_elim. 
      grind.

      reveal ITREE.
      
      gstep. econs. econs; cycle 1.
      { unfold smj_ltb. instantiate (1:= smj_bot). ss. }
      { unfold smj_ltb. instantiate (1:= smj_bot). ss. }
      gbase. eapply CIH; eauto.
      move REL at bottom.

    }



    (* PG - Proved *)
    { admit. }
    (* { 
      subst. depdes s.
      (* sPut *)
      { 
        hide_r. move ITREE at top. 
        grind.
        rewrite/__ ElimRed.interp_bind ElimRed.interp_pg !HModSB.transl_bind  HModSB.transl_put.
        destruct (existsb (String.eqb k.1) scopes) eqn:SCP; cycle 1.
        {
          (* key not exists *)
          grind. _core. st. exists tt. st. grind. _tau. st.
          _iter. rewrite/__ list_lookup_insert;[|apply H1]. grind.
          _tau. st. st.
          _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H1]. grind.
          _tau. st. st.
          reveal ITREE. hide_l. move ITREE at top. grind.
          rewrite/__ !SModRed.interp_bind SModRed.interp_pg !HModSB.transl_bind HModSB.transl_put.
          rewrite SCP. grind.
          _core. st. i. st. grind. _tau. st.
          _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind.
          _tau. st. st.
          _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind.
          _tau. st. st.
          
          reveal ITREE.
          gstep. econs. econs; cycle 1.
          { unfold smj_ltb. instantiate (1:= smj_bot). ss. }
          { unfold smj_ltb. instantiate (1:= smj_bot). ss. }
          gbase. eapply CIH; eauto.
          move REL at bottom.
    
          eapply Forall3i_forall; cycle 1.
          { rewrite/__ H !insert_length. ss. }
          { rewrite/__ H0 !insert_length. ss. }


          i. destruct (Nat.eq_dec k0 cid).
          {
            subst k0. rewrite/__ list_insert_insert list_lookup_insert in LKY; [|apply H1].
            rewrite/__ list_insert_insert list_lookup_insert in LKZ; [|apply H2].
            depdes LKY LKZ. econs 2.
            { grind. }
            { 
              destruct (Nat.eq_dec (0 + cid) cid); try nia.
              destruct x.
              instantiate (1:= m). grind.
              f_equal. rewrite/__ HModSB.transl_bind.
              grind.
            }
          }
          eapply Forall3i_nth in REL; cycle 1.
          { eapply lookup_lt_is_Some. econs. eauto. }
          des. assert (cid ≠ k0) by nia.
          rewrite/__ list_insert_insert (list_lookup_insert_ne srcs cid k0 _ H3) in LKY.
          rewrite/__ list_insert_insert (list_lookup_insert_ne tgts cid k0 _ H3) in LKZ.
          rewrite LKX in REL. 
          rewrite LKY in REL0. 
          rewrite LKZ in REL1.
          depdes REL REL0 REL1. apply REL2.
        }

        grind. _supd. 
        _iter. rewrite/__ list_lookup_insert;[|apply H1]. grind. _supd.
        _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H1]. grind.
        _tau. st. st.
        _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H1]. grind.
        _tau. st. st.
        reveal ITREE. hide_l. move ITREE at top.
        grind. 
        rewrite/__ !SModRed.interp_bind SModRed.interp_pg !HModSB.transl_bind HModSB.transl_put SCP.
        grind. _supd.
        _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind. _supd.
        _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind.
        _tau. st. st.
        _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind.
        _tau. st. st.

        reveal ITREE.
        instantiate (1:= smj_top).
        instantiate (1:= smj_top).
        gstep. econs. econs; cycle 1.
        { unfold smj_ltb. instantiate (1:= smj_bot). ss. }
        { unfold smj_ltb. instantiate (1:= smj_bot). ss. }
        gbase. eapply CIH; eauto.
        move REL at bottom.
  
        eapply Forall3i_forall; cycle 1.
        { rewrite/__ H !insert_length. ss. }
        { rewrite/__ H0 !insert_length. ss. }


        i. destruct (Nat.eq_dec k0 cid).
        {
          subst k0. rewrite/__ list_insert_insert list_lookup_insert in LKY; [|apply H1].
          rewrite/__ list_insert_insert list_lookup_insert in LKZ; [|apply H2].
          depdes LKY LKZ. econs 2.
          { grind. }
          { 
            destruct (Nat.eq_dec (0 + cid) cid); try nia.
            instantiate (1:= m). grind.
            f_equal. rewrite/__ HModSB.transl_bind. grind.
          }
        }
        eapply Forall3i_nth in REL; cycle 1.
        { eapply lookup_lt_is_Some. econs. eauto. }
        des. assert (cid ≠ k0) by nia.
        rewrite/__ list_insert_insert (list_lookup_insert_ne srcs cid k0 _ H3) in LKY.
        rewrite/__ list_insert_insert (list_lookup_insert_ne tgts cid k0 _ H3) in LKZ.
        rewrite LKX in REL. 
        rewrite LKY in REL0. 
        rewrite LKZ in REL1.
        depdes REL REL0 REL1. apply REL2.
      }

      (* sGet *)
      { 
        hide_l. move ITREE at top. 
        grind.
        rewrite/__ !SModRed.interp_bind SModRed.interp_pg !HModSB.transl_bind HModSB.transl_get.
        destruct (existsb (String.eqb k.1) scopes) eqn:SCP; cycle 1.
        {
          (* key not exists *)
          grind. _core. st. i. st. grind. _tau. st.
          _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind.
          _tau. st. st.
          _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind.
          _tau. st. st.
          reveal ITREE. hide_r. move ITREE at top. grind.
          rewrite/__ ElimRed.interp_bind ElimRed.interp_pg !HModSB.transl_bind  HModSB.transl_get.
          rewrite SCP. grind.
          _core. st. exists x. st. grind. _tau. st.
          _iter. rewrite/__ list_lookup_insert;[|apply H1]. grind.
          _tau. st. st.
          _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H1]. grind.
          _tau. st. st.
          
          reveal ITREE.
          instantiate (1:= smj_top).
          instantiate (1:= smj_top).
          gstep. econs. econs; cycle 1.
          { unfold smj_ltb. instantiate (1:= smj_bot). ss. }
          { unfold smj_ltb. instantiate (1:= smj_bot). ss. }
          gbase. eapply CIH; eauto.
          move REL at bottom.
    
          eapply Forall3i_forall; cycle 1.
          { rewrite/__ H !insert_length. ss. }
          { rewrite/__ H0 !insert_length. ss. }


          i. destruct (Nat.eq_dec k0 cid).
          {
            subst k0. rewrite/__ list_insert_insert list_lookup_insert in LKY; [|apply H1].
            rewrite/__ list_insert_insert list_lookup_insert in LKZ; [|apply H2].
            depdes LKY LKZ. econs 2.
            { grind. }
            { 
              destruct (Nat.eq_dec (0 + cid) cid); try nia.
              instantiate (1:= m). grind.
              f_equal. rewrite/__ HModSB.transl_bind.
              grind.
            }
          }
          eapply Forall3i_nth in REL; cycle 1.
          { eapply lookup_lt_is_Some. econs. eauto. }
          des. assert (cid ≠ k0) by nia.
          rewrite/__ list_insert_insert (list_lookup_insert_ne srcs cid k0 _ H3) in LKY.
          rewrite/__ list_insert_insert (list_lookup_insert_ne tgts cid k0 _ H3) in LKZ.
          rewrite LKX in REL. 
          rewrite LKY in REL0. 
          rewrite LKZ in REL1.
          depdes REL REL0 REL1. apply REL2.
        }

        grind. _supd. 
        _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind. 
        _tau. st. st.
        _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind.
        _tau. st. st. grind.
        reveal ITREE. hide_r. move ITREE at top.
        grind. 
        rewrite/__ ElimRed.interp_bind ElimRed.interp_pg !HModSB.transl_bind HModSB.transl_get SCP.
        grind. _supd.
        _iter. rewrite/__ list_lookup_insert;[|apply H1]. grind.
        _tau. st. st.
        _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H1]. grind.
        _tau. st. st. grind.

        reveal ITREE.
        instantiate (1:= smj_top).
        instantiate (1:= smj_top).
        gstep. econs. econs; cycle 1.
        { unfold smj_ltb. instantiate (1:= smj_bot). ss. }
        { unfold smj_ltb. instantiate (1:= smj_bot). ss. }
        gbase. eapply CIH; eauto.
        move REL at bottom.
  
        eapply Forall3i_forall; cycle 1.
        { rewrite/__ H !insert_length. ss. }
        { rewrite/__ H0 !insert_length. ss. }


        i. destruct (Nat.eq_dec k0 cid).
        {
          subst k0. rewrite/__ list_insert_insert list_lookup_insert in LKY; [|apply H1].
          rewrite/__ list_insert_insert list_lookup_insert in LKZ; [|apply H2].
          depdes LKY LKZ. econs 2.
          { grind. }
          { 
            destruct (Nat.eq_dec (0 + cid) cid); try nia.
            instantiate (1:= m). grind.
            f_equal. rewrite/__ HModSB.transl_bind. grind.
          }
        }
        eapply Forall3i_nth in REL; cycle 1.
        { eapply lookup_lt_is_Some. econs. eauto. }
        des. assert (cid ≠ k0) by nia.
        rewrite/__ list_insert_insert (list_lookup_insert_ne srcs cid k0 _ H3) in LKY.
        rewrite/__ list_insert_insert (list_lookup_insert_ne tgts cid k0 _ H3) in LKZ.
        rewrite LKX in REL. 
        rewrite LKY in REL0. 
        rewrite LKZ in REL1.
        depdes REL REL0 REL1. apply REL2.
      }
    } *)

    (* CORE - Proved *)
    { admit. }
    (* {
      subst.
      rewrite/__ ElimRed.interp_bind ElimRed.interp_core !HModSB.transl_bind  HModSB.transl_core.
      rewrite/__ SModRed.interp_bind SModRed.interp_core !HModSB.transl_bind  HModSB.transl_core.
      depdes e0.
      {
        hide_l. grind.
        _core. st. i. st. grind. _tau. st.
        _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind.
        _tau. st. st. 
        _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind.   
        _tau. st. st. 
        reveal ITREE. hide_r. grind.
        _core. st. exists x. st. grind. _tau. st.
        _iter. rewrite/__ list_lookup_insert;[|apply H1]. grind.
        _tau. st. st. 
        _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H1]. grind.   
        _tau. st. st.    
        reveal ITREE.
        instantiate (1:= smj_top).
        instantiate (1:= smj_top).
        gstep. econs. econs; cycle 1.
        { unfold smj_ltb. instantiate (1:= smj_bot). ss. }
        { unfold smj_ltb. instantiate (1:= smj_bot). ss. }
        gbase. eapply CIH; eauto.
        move REL at bottom.
        eapply Forall3i_forall; cycle 1.
        { rewrite/__ H !insert_length. ss. }
        { rewrite/__ H0 !insert_length. ss. }
        i. destruct (Nat.eq_dec k cid).
        {
          subst k. rewrite/__ list_insert_insert list_lookup_insert in LKY; [|apply H1].
          rewrite/__ list_insert_insert list_lookup_insert in LKZ; [|apply H2].
          depdes LKY LKZ. econs 2.
          { grind. }
          { 
            destruct (Nat.eq_dec (0 + cid) cid); try nia.
            instantiate (1:= m). grind.
            f_equal. rewrite/__ HModSB.transl_bind. grind.
          }
        }
        eapply Forall3i_nth in REL; cycle 1.
        { eapply lookup_lt_is_Some. econs. eauto. }
        des. assert (cid ≠ k) by nia.
        rewrite/__ list_insert_insert (list_lookup_insert_ne srcs cid k _ H3) in LKY.
        rewrite/__ list_insert_insert (list_lookup_insert_ne tgts cid k _ H3) in LKZ.
        rewrite LKX in REL. 
        rewrite LKY in REL0. 
        rewrite LKZ in REL1.
        depdes REL REL0 REL1. apply REL2.
      }
      {
        hide_r. grind.
        _core. st. i. st. grind. _tau. st.
        _iter. rewrite/__ list_lookup_insert;[|apply H1]. grind.
        _tau. st. st. 
        _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H1]. grind.   
        _tau. st. st. 
        reveal ITREE. hide_l. grind.
        _core. st. exists x. st. grind. _tau. st.
        _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind.
        _tau. st. st. 
        _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind.   
        _tau. st. st.    
        reveal ITREE.
        instantiate (1:= smj_top).
        instantiate (1:= smj_top).
        gstep. econs. econs; cycle 1.
        { unfold smj_ltb. instantiate (1:= smj_bot). ss. }
        { unfold smj_ltb. instantiate (1:= smj_bot). ss. }
        gbase. eapply CIH; eauto.
        move REL at bottom.
        eapply Forall3i_forall; cycle 1.
        { rewrite/__ H !insert_length. ss. }
        { rewrite/__ H0 !insert_length. ss. }
        i. destruct (Nat.eq_dec k cid).
        {
          subst k. rewrite/__ list_insert_insert list_lookup_insert in LKY; [|apply H1].
          rewrite/__ list_insert_insert list_lookup_insert in LKZ; [|apply H2].
          depdes LKY LKZ. econs 2.
          { grind. }
          { 
            destruct (Nat.eq_dec (0 + cid) cid); try nia.
            instantiate (1:= m). grind.
            f_equal. rewrite/__ HModSB.transl_bind. grind.
          }
        }
        eapply Forall3i_nth in REL; cycle 1.
        { eapply lookup_lt_is_Some. econs. eauto. }
        des. assert (cid ≠ k) by nia.
        rewrite/__ list_insert_insert (list_lookup_insert_ne srcs cid k _ H3) in LKY.
        rewrite/__ list_insert_insert (list_lookup_insert_ne tgts cid k _ H3) in LKZ.
        rewrite LKX in REL. 
        rewrite LKY in REL0. 
        rewrite LKZ in REL1.
        depdes REL REL0 REL1. apply REL2.
      }
      {
        grind. _core. _core. st. i. subst.
        st. st. grind.
        _tau. st. st.
        hide_l.
        _iter. rewrite/__ list_lookup_insert;[|apply H2]. grind.
        _tau. st. st. 
        _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H2]. grind.   
        _tau. st. st. 
        reveal ITREE. hide_r. grind.
        _iter. rewrite/__ list_lookup_insert;[|apply H1]. grind.
        _tau. st. st. 
        _iter. rewrite/__ list_insert_insert list_lookup_insert;[|apply H1]. grind.   
        _tau. st. st.
        reveal ITREE.
        instantiate (1:= smj_top).
        instantiate (1:= smj_top).
        gstep. econs. econs; cycle 1.
        { unfold smj_ltb. instantiate (1:= smj_bot). ss. }
        { unfold smj_ltb. instantiate (1:= smj_bot). ss. }
        gbase. eapply CIH; eauto.
        move REL at bottom.
        eapply Forall3i_forall; cycle 1.
        { rewrite/__ H !insert_length. ss. }
        { rewrite/__ H0 !insert_length. ss. }
        i. destruct (Nat.eq_dec k cid).
        {
          subst k. rewrite/__ list_insert_insert list_lookup_insert in LKY; [|apply H1].
          rewrite/__ list_insert_insert list_lookup_insert in LKZ; [|apply H2].
          depdes LKY LKZ. econs 2.
          { instantiate (1:= (ktrS' x_tgt)). grind. }
          { 
            destruct (Nat.eq_dec (0 + cid) cid); try nia.
            instantiate (1:= m). grind.
            f_equal. rewrite/__ HModSB.transl_bind. grind.
          }
        }
        eapply Forall3i_nth in REL; cycle 1.
        { eapply lookup_lt_is_Some. econs. eauto. }
        des. assert (cid ≠ k) by nia.
        rewrite/__ list_insert_insert (list_lookup_insert_ne srcs cid k _ H3) in LKY.
        rewrite/__ list_insert_insert (list_lookup_insert_ne tgts cid k _ H3) in LKZ.
        rewrite LKX in REL. 
        rewrite LKY in REL0. 
        rewrite LKZ in REL1.
        depdes REL REL0 REL1. apply REL2.
      }
    } *)


  Admitted.

  

  Theorem cancellation P 
    (COND: forall sk0 (EQV: Sk.equiv sk sk0) (SKWF: Sk.wf sk0), 
      exists fsp m rt,
        (stb sk0 "CCR_init" = Some fsp) /\
        (URA.wf rt) /\ 
        (Own rt ⊢ (P sk0) ∗ (fsp.(precond) m tt↑ tt↑))
    )
  :
    refines (md_elim, const(emp%I)) (md_tgt, P).
  Proof.
    econs. { s. r. refl. }
    ii. ss. specialize (COND sk0 EQV SKWF). des.
    (* resoure *)
    eapply iProp_sepconj in COND1; [|et]. des. subst.
    exists p. esplits; eauto. 
    { eapply URA.wf_mon; eauto. }
    { eapply iProp_Own. eauto. }
    { inv WFM. econs; eauto. admit. }
    r. eapply adequacy_global_itree.
    instantiate (1:= smj_top).
    instantiate (1:= smj_top).
    unfold ModSem.initial_itr. s. unfold ITree.map.
    (* remember (alist_encode (SModSem.initial_st (SMod.modsem md sk0))) as st. *)
    destruct (alist_find "CCR_init" (SModSem.fnsems (SMod.modsem md sk0))) eqn:E; cycle 1.
    {
      rewrite/__ !alist_find_map/o_map E. s.
      unfold interp_modE at 2.
      rewrite/interp_schE_callE unfold_iter_eq /handle_schE_callE.
      grind. rewrite/__ StRed.interp_bind. grind.
      destruct (resum IFun void (Choose void)) eqn:V.
      { inv V. }
      depdes c; inv V. resub.
      rewrite/__ [interp_stateE _ _ _]StRed.interp_core. grind.
      ginit. guclo simg_indC_spec. econs. i. ss.
    }
    rewrite/__ !alist_find_map/o_map E. s.
    destruct p0. unfold HModSem.sandbox_body, interp_hp_fun. s.
    unfold interp_sb_hp_elim, interp_sb_hp, interp_hp_body.
    unfold interp_modE, interp_schE_callE. grind.
    unfold HoareFun.
    _coreH. hide_l. _iter. _core.
    destruct f.
    assert (SKINCL: incl sk sk0). { eapply Sk.equiv_incl. eauto. }
    pose proof (stb_find_fsb SKINCL SKWF COND E). subst.

    (* Executing main's precondition. Try to simplify with tactics. *)
    ginit. st. exists m.
    st. grind. _tau. st. _iter. _tau. st. st. 
    _coreH. _iter. _core. st. exists (tt↑). grind.
    _tau. st. st. _iter. _tau. st. st. 
    _asm. _iter. _core. st.
    (* take resource for precond. *)
    exists q. st. grind. _tau. st.
    _iter. _sget. grind. _tau. st. st. 
    hss. grind. hss. grind.
    unfold assume. _iter. 
    _core. st.  
    assert (URA.wf (q ⋅ ε ⋅ p)). { r_solve. rewrite URA.add_comm. eauto. }
    exists H. grind.
    _tau. st. st. _iter. _core. st. 
    eapply iProp_Own in COND3. exists COND3. grind.
    _iter. _tau. do 4 st.

    (* CCR_main's precond all executed. *)
    instantiate (1:= smj_top). unfold ITREE. clear ITREE.
    eapply cancel_aux; eauto.
    { instantiate (1:= [q]). eauto. }
    { s. r_solve. eauto. }
    econs; eauto using Forall3i.
    econs 2; eauto. grind. repeat f_equal. r_solve.
    Unshelve. all: eapply smj_top.
  Admitted.
    cut (
      ∀ frs mr srcs tgts ps pt cid st
        (LEN: cid < List.length frs)
        (WF: URA.wf (mr ⋅ (foldl (fun r1 r2 => r1 ⋅ r2) ε frs)))
        (REL: Forall3i (thread_rel sk0 cid) 0 frs srcs tgts),
        gpaco7 _simg (cpn7 _simg) bot7 bot7 Any.t Any.t eq ps pt
        (x <-
          interp_stateE Any.t
            (ITree.iter
               (handle_schE_callE
                  (ModSem.prog
                     (HModSem.to_mod
                        (SModSemElim.to_elim (SMod.modsem md sk0)) rs)))
               (cid, srcs))
          (Any.pair st rs↑);; Ret x.2)
        (x <-
          interp_stateE Any.t
            (ITree.iter
               (handle_schE_callE
                  (ModSem.prog
                     (HModSem.to_mod
                        (SModSem.to_hmod (ginv sk0) 
                           (stb sk0) (SMod.modsem md sk0)) mr))) 
               (cid, tgts))
          (Any.pair st mr↑);; Ret x.2)
    ).
    {
      i. eapply H; eauto.
      { instantiate (1:= [q]). eauto. }
      { s. r_solve. eauto. }
      econs; eauto using Forall3i.
      econs 2; eauto. grind. repeat f_equal. r_solve.
    }
    
    



  
  Admitted.




  (*** Final Theorem ***)
  Theorem cancellation P:
    refines (md_src, (fun _ => emp)%I) (md_tgt, P).
  Proof. Admitted.

End CANCEL.
