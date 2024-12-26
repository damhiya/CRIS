Require Import Common.
Require Import SMod2HMod HMod2Mod Mod2ITree SMod HMod Mod Skeleton.
Require Import SimGlobal.
Require Import SModCancel HModInline ElimRel StRed CancelDef.

(* Spawn *)

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
    (ms sk0 SKINCL SKWF).(SModSem.fnsems).
  Let _stb (sk0: Sk.t) (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0): alist gname (list string * fspec) := 
    List.map (map_snd (fun '(fn, fs) => (fn, fs.(fsb_fspec)))) (sbtb sk0 SKINCL SKWF).

  Hypothesis STBCOMPLETE:
    forall 
      sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
      fn scfsp (FIND: alist_find fn (_stb sk0 SKINCL SKWF) = Some scfsp), stb sk0 fn = Some scfsp.2.
  Hypothesis STBSOUND:
    forall 
      sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
      fn (FIND: alist_find fn (_stb sk0 SKINCL SKWF) = None),
      (<<NONE: stb sk0 fn = None>>).

  Let md_src: HMod.t := SModCancel.to_hmod md.
  Let md_tgt: HMod.t := SMod.to_hmod ginv stb md.

  Import CancelTAC.



  Lemma cancel_main_spawn
    sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
    X (meta: X) (rs0 rt0 rs rt: Σ) Q (cid tid: nat) st ps pt l fn f args
    srcs tgts ktrS ktrT
    (STB: stb sk0 fn = Some f)
    (LENS: cid < base.length srcs)
    (LENT: cid < base.length tgts)
    (LEN: base.length srcs = base.length tgts)
    (WFS: ✓ rs)
    (WFT: ✓ rt)
    (UPD: Own rs ==∗ Own rt)
    (RET: ∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝)
    (KTR: ∀ (x: nat), upaco3 (@elim_rel_def _ ginv stb sk0 _) bot3 l (ktrS x) (ktrT x))
    (RELS: ∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel ginv stb md sk0 cid k x y)
    (r: ∀ x x0 : Type, (x → x0 → Prop) → smj → smj → itree coreE x → itree coreE x0 → Prop)
    (CIH: ∀ (rs rt : Σ) (srcs tgts : list (itree modE Any.t)) (cid : nat) (st : Any.t) (ps pt : smj),
          ✓ rs → cid < base.length srcs → (Own rs ==∗ Own rt) 
          → ∀ src tgt : itree modE Any.t,
            srcs !! cid = Some src → tgts !! cid = Some tgt
            → ∀ (X : Type) (meta : X) (Q : nat → X → Any.t → Any.t → iProp) (l : list (nat * {X0 : Type & X0})) (itrS itrT : itree hmodE Any.t),
              (∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝) 
              → paco3 (@elim_rel_def _ ginv stb sk0 _)  bot3 l itrS itrT
              → src = (if Nat.eq_dec cid cid then Ret () else tau;; Ret ());;; interp_hp itrS
              → tgt = interp_hp ((if Nat.eq_dec cid cid then Ret () else yield_post ginv sk0);;; vret <- itrT;; inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret))
              → base.length srcs = base.length tgts
              → cid < base.length tgts
              → (∀ (k : nat) (x y : itree modE Any.t), cid ≠ k → srcs !! k = Some x → tgts !! k = Some y → thread_rel ginv stb md sk0 cid k x y)
              → r Any.t Any.t eq ps pt
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemInline.inline (SModSemCancel.to_hmod (SMod.modsem md sk0))) rs0))) (cid, srcs)) (Any.pair st rs ↑);; Ret x.2)
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemInline.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) (cid, tgts)) (Any.pair st rt ↑);; Ret x.2))
  : 
  gpaco7 _simg (cpn7 _simg) bot7 r Any.t Any.t eq ps pt
  (x <- interp_stateE Any.t (tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemInline.inline (SModSemCancel.to_hmod (SMod.modsem md sk0))) rs0)))
    (cid, <[cid:=tau;; interp_hp (tau;; trigger (Yield (base.length srcs));;; ktrS (base.length srcs))]> srcs ++ 
            [sem <- (alist_find fn (List.map (map_snd (interp_hp_fun ∘ HModSem.sandbox_body))
                    (List.map (map_snd (wrap_elimI (SModSemCancel.to_hmod (SMod.modsem md sk0))))
                    (List.map (map_snd (λ ksb : list string * fspecbody, (ksb.1, interp_sb_hp_cancel ksb.2))) (SModSem.fnsems (SMod.modsem md sk0)))))) !;; sem args])) (Any.pair st rs ↑);; Ret x.2)
  (x <- interp_stateE Any.t
    (x_ <- trigger (|resum IFun (SMod2HMod.meta f) (Choose (SMod2HMod.meta f)))%sum;;
      x_0 <- Ret (inl
        (cid, <[cid:=lr <- ITree.subst (λ x : SMod2HMod.meta f, Ret (inl (vret <-
                              ITree.subst (λ x0 : nat, ktrT x0)
                                (ITree.subst
                                   (λ x0 : SMod2HMod.meta f,
                                      tau;; arg <- trigger (Choose Any.t);;
                                            (tau;; tid <- trigger (Spawn fn arg);;
                                                   (tau;; trigger (Guarantee (ginv sk0 tid -∗ precond f tid x0 args arg));;; (tau;; HoareYieldE (ginv sk0) tid;;; Ret tid))))
                                   (Ret x));;
                              inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)))
                                (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret)))) (Ret x_);;
                   match lr with
                   | inl l0 => tau;; interp_hp l0
                   | inr r0 => Ret r0
                   end]> tgts));;
      match x_0 with
      | inl l0 => tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemInline.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) l0
      | inr r0 => Ret r0
      end) (Any.pair st rt ↑);; Ret x.2).
  Proof.
    hide_l. _coreA.
    iterT 2. iterL. _coreA. ls.
    iterT 2. iterL. tau 1. ls. 
    rewrite !length_insert. 
    rewrite <- insert_app_l; eauto.
    assert (cid <
    base.length
      (tgts ++
       [' sem : (Any.t → itree modE Any.t) <-
        (alist_find fn
           (List.map (map_snd (interp_hp_fun ∘ HModSem.sandbox_body))
              (List.map (map_snd (wrap_elimI (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))))
                 (List.map (map_snd (λ ksb : list string * fspecbody, (ksb.1, interp_sb_hp (ginv sk0) (stb sk0) ksb.2)))
                    (SModSem.fnsems (SMod.modsem md sk0)))))) !;; sem x0])).
    { rewrite length_app. nia. }
    iterT 2. iterL. _supd.
    iterL. _coreA. ls. iterL. _coreA. ls.
    iterL. _supd. iterL. _supd.
    iterT 2. iterL. _supd. 
    iterL. _coreA. ls. iterL. _coreA. ls.
    iterL. _supd. iterL. _supd.
    iterT 2. iterL. tau 1. ls.    
    reveal ITREE. hide_r. tau 1. 
    rewrite -insert_app_l; eauto. 
    assert (cid <
    base.length
      (srcs ++
       [' sem : (Any.t → itree modE Any.t) <-
        (alist_find fn
           (List.map (map_snd (interp_hp_fun ∘ HModSem.sandbox_body))
              (List.map (map_snd (wrap_elimI (SModSemCancel.to_hmod (SMod.modsem md sk0))))
                 (List.map (map_snd (λ ksb : list string * fspecbody, (ksb.1, interp_sb_hp_cancel ksb.2))) (SModSem.fnsems (SMod.modsem md sk0)))))) !;; 
        sem args])).
    { rewrite length_app. nia. }
    iterT 2.
    iterL. tau 1. ls. 
    hexploit stb_in_alist_find; eauto. i. des.
    reveal ITREE. 
    rewrite !alist_find_map_snd !H1. s.
    erewrite wrap_elimI_well_scoped; cycle 1.
    {
      instantiate (1:= fn).
      s. unfold interp_sb_hp_cancel. s.
      rewrite alist_find_map_snd H1. ss.
    }
    erewrite wrap_elimI_well_scoped; cycle 1.
    {
      instantiate (1:= fn).
      s. unfold interp_sb_hp. s.
      rewrite alist_find_map_snd H1. ss.
    }
    ired.
    unfold interp_hp_fun, inline_hp_fun, HModSem.sandbox_body. s. 
    unfold interp_sb_hp, interp_sb_hp_cancel. s.
    hide_l. _iter.
    rewrite list_lookup_insert_ne; try nia. 
    rewrite list_lookup_length. ired. tau 1.
    assert (forall x, base.length tgts < base.length (tgts ++ [x])). { i. rewrite length_app. s. nia. }
    hexploit (Own_bupd_split rt); eauto. i. des.
    hexploit (Own_bupd_split x1); eauto. 
    {
      hexploit (Own_wand_valid rt (a1 ⋅ x1)); eauto.
      {
        iIntros "H". iPoseProof (H3 with "H") as ">[H0 H1]".
        iPoseProof (H5 with "H1") as "H1". 
        iModIntro. rewrite Own_op. iFrame.
      }
      i. eapply cmra_valid_op_r. eauto. 
    }  
    i. des.
    iterT 2. iterL. _coreE x. ls.
    iterT 2. iterL. _coreE args. ls.
    iterT 2. iterL. _coreE (a0 ⋅ a1). ls. iterL. _supd. 
    assert (UPD': Own rs ==∗ Own (a0 ⋅ a1 ⋅ x3)). 
    {  
      iIntros "H". iPoseProof (UPD with "H") as ">H".
      iPoseProof (H3 with "H") as ">[H0 H1]".
      iPoseProof (H5 with "H1") as "H1".
      iPoseProof (H6 with "H1") as ">[H1 H2]".
      iPoseProof (H8 with "H2") as "H2".
      iModIntro. rewrite !Own_op. iFrame.
    }
    assert (✓(a0 ⋅ a1 ⋅ x3)). 
    { eapply Own_wand_valid with (a1 := rs); eauto. }
    iterL. _coreE H9. ls. 
    assert (Own (a0 ⋅ a1) ⊢ precond f (base.length tgts) x args x0).
    {
      iIntros "[H0 H1]".  
      iPoseProof (H7 with "H0") as "H0".
      iPoseProof (H4 with "H1") as "H1".
      iApply "H1". eauto.
    } 
    iterL. _coreE H10. ls.
    iterL. _supd. iterL. _supd.
    iterT 2.
    reveal ITREE. prb. gbase. pclearbot. rewrite LEN.
    eapply CIH; try (rewrite !length_insert !length_app; s; nia); swap 6 8.
    { auto. }
    { auto. }
    {
      rewrite list_lookup_insert_ne; try nia. 
      rewrite -LEN list_lookup_length. f_equal.
    }
    {
      rewrite list_lookup_insert; eauto.
      rewrite length_insert length_app. s. nia. 
    }
    { i. nia. }
    {
      instantiate (1:= x). instantiate (1:= postcond f).
      instantiate (1:= inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) 
                       (HModSem.sandbox l0 (interp_smod (ginv sk0) (stb sk0) (fbody args)))).        
      des_ifs. rewrite bind_ret_l. f_equal.
      rewrite (bisim_is_eq (translate_bind _ _ _)).
      rewrite -HIRed.bind. 
      do 3 f_equal. extensionalities.
      match goal with [|-(?itr = _)] => set itr end.
      eassert (i = HModSem.sandbox l0 _). { unfold i. f_equal. }
      rewrite H12 HModSB.transl_bind HModSB.transl_core. 
      f_equal. extensionalities.
      rewrite HModSB.transl_bind HModSB.transl_ag.
      f_equal. extensionalities.
      rewrite HModSB.transl_ret. eauto.
    }
    { grind. }
    { eapply elim_rel_refl; eauto. } 
    i. rewrite list_lookup_insert_ne in H13; eauto.
    destruct (Nat.eq_dec cid k).
    {
      subst k. rewrite list_lookup_insert in H12; cycle 1.
      { rewrite length_app. s. nia. }
      rewrite list_lookup_insert in H13; cycle 1.
      { rewrite length_app. s. nia. }
      inv H12. econs; eauto; cycle 1.
      { destruct (Nat.eq_dec cid (base.length tgts)); try nia. grind. }
      {
        destruct (Nat.eq_dec cid (base.length tgts)); try nia.
        instantiate (1:= ktrT (base.length tgts)).
        unfold yield_post. ired. rewrite -interp_hp_tau. 
        do 6 f_equal. extensionalities. grind.
      }
      eapply KTR.
    }
    rewrite !list_lookup_insert_ne in H12, H13; try nia.
    eapply lookup_snoc_Some in H12, H13. des; try nia.
    specialize (RELS k x5 y n H15 H14).
    inv RELS. econs; eauto; des_ifs.
  Qed.

End CANCEL.

(* 59 sec *)
