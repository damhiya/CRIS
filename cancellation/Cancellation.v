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
  Ltac prb := gstep; econs; econs; try instantiate (1:= smj_bot); try instantiate (1:= smj_bot); eauto.  
  Ltac prm := gstep; econs; econs; try instantiate (1:= smj_mid); try instantiate (1:= smj_mid); eauto.  
  Ltac _iter := rewrite unfold_iter_eq; ired.
  Ltac _iterI := rewrite/__ [ITree.iter (handle_callE _) _]unfold_iter_eq; ired.
  Ltac _tau := rewrite/__ !StRed.tau.
  Ltac _core := rewrite/__ StRed.bind StRed.core; prep.
  Ltac _coreH := rewrite/__ HModSB.transl_bind HModSB.transl_core interp_hp_bind interp_hp_core; prep.
  Ltac _asm := rewrite/__ HModSB.transl_bind HModSB.transl_ag interp_hp_bind interp_hp_Assume/handle_Assume /mget_res; prep.
  Ltac _grt := rewrite/__ HModSB.transl_bind HModSB.transl_ag interp_hp_bind interp_hp_Assume/handle_Guarantee /mget_res; prep.
  Ltac _sget := rewrite/sGet !StRed.bind [interp_stateE Any.t _ _]StRed.state/handle_stateE. 
  (* Ltac __supd := rewrite/sPut /sGet !StRed.bind [interp_stateE _ _ _]StRed.state/handle_stateE.  *)
  Ltac ls := rewrite !list_insert_insert.
  Ltac __supd := rewrite/__ !StRed.bind StRed.state. 
  Ltac _supd := __supd; grind; try ls; _tau; st; st; try (rewrite Any.pair_split; ired); try (rewrite Any.upcast_downcast; ired).
  Ltac _ub := rewrite/triggerUB !StRed.bind StRed.core; st; i; ss.
  Ltac iterL := _iter; rewrite/__ list_lookup_insert;[|try rewrite !length_insert; auto]; ired.

  Tactic Notation "tau" integer(n) := _tau; do n st.
  Tactic Notation "iterT" integer(n) := do n (iterL; ls; tau 2).
  Ltac _coreA := _core; st; i; st; grind; _tau; st.
  Ltac _coreE x := _core; st; exists x; st; grind; _tau; st.

  Inductive Forall2i X Y (R: nat -> X -> Y -> Prop): nat -> list X -> list Y -> Prop :=
  | Forall2i_nil i: Forall2i R i [] []
  | Forall2i_cons
      i x y xs ys
      (REL: R i x y)
      (TAIL: Forall2i R (S i) xs ys):
      Forall2i R i (x :: xs) (y :: ys).

  Lemma Forall2i_len 
    X Y (R: nat -> X -> Y -> Prop) i xs ys
    (REL: Forall2i R i xs ys)
  :
    List.length xs = List.length ys.
  Proof.
    induction REL; s; eauto.
  Qed.

  Lemma Forall2i_nth
    X Y (R: nat -> X -> Y -> Prop) (i k: nat) 
    (xs: list X) (ys: list Y)
    (REL: Forall2i R i xs ys)
    (NTH: k < List.length xs)
  :
    ∃ x y,
    xs !! k = Some x /\
    ys !! k = Some y /\
    R (i + k) x y.
  Proof.
    revert k NTH.
    induction REL; s; i; eauto.
    - nia.
    - destruct k; s.
      + replace (i + 0) with i by nia. eauto 7.
      + replace (i + S k) with (S i + k) by nia.
      eapply IHREL; nia.
  Qed.

  Lemma Forall2i_forall:
      ∀ X Y (R: nat -> X -> Y -> Prop) i xs ys
        (RELS: forall k x y
                (LKX: xs !! k = Some x)
                (LKY: ys !! k = Some y),
              R (i + k) x y)
        (EQLEN1: List.length xs = List.length ys)
        ,
      @Forall2i X Y R i xs ys. 
  Proof. Admitted.

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

  Inductive valid_stack: list (nat * nat * {X: Type & (X * X)%type}) -> Prop
    :=
    | valid_stack_base: valid_stack []

    | valid_stack_cons n X (x: X) tl (TL: valid_stack tl):
      valid_stack ((n, n, existT X (x, x))::tl)
    .

  Definition yield_post sk0: itree hmodE _ :=
      tau;; tau;; r <- trigger Tid;; x <- (tau;; trigger (Assume (ginv sk0 r)));; tau;; Ret ().

  (* no more fr? *)
  (* Variant thread_rel sk0 (cid tid: nat) (fr: Σ) src tgt : Prop :=
  | thread_rel_init scopes fsp fbody m varg arg
      (NOC: tid ≠ cid)
      (* (NOC: ~ Nat.eq_dec tid cid) *)
      (FR: Own fr ⊢ (ginv sk0 tid) -∗ fsp.(precond) tid m varg arg)
      (SRC: src = interp_hp (HModSem.sandbox scopes (fbody varg)))
      (TGT: tgt = interp_hp (HModSem.sandbox scopes (HoareFun (ginv sk0) (stb sk0)
                    fsp.(precond) fsp.(postcond) fbody arg)))
  | thread_rel_body (Q: Any.t -> Any.t -> iProp) l itrS itrT
      (STACK: valid_stack l)
      (REL: @elim_rel _ ginv stb sk0 _ l itrS itrT)
      (SRC: src = interp_hp itrS)
      (TGT: tgt =
        (interp_hp
            ((if Nat.eq_dec tid cid then Ret tt else yield_post sk0);;;
            (* ((if Nat.eq_dec tid cid then Ret tt else trigger (Assume (ginv sk0 tid)));;; *)
              vret <- itrT;; 
              (inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)))
                ( ret <- trigger (Choose Any.t);;
                  trigger (Guarantee (Q vret ret));;;
                  Ret ret)))))
  . *)

  Variant thread_rel sk0 (cid tid: nat) src tgt : Prop :=
  | thread_rel_init scopes fsp fbody fr m varg arg
      (NOC: tid ≠ cid)
      (FR: Own fr ⊢ (ginv sk0 tid) -∗ fsp.(precond) tid m varg arg)
      (SRC: src = interp_hp (HModSem.sandbox scopes (fbody varg)))
      (TGT: tgt = interp_hp (HModSem.sandbox scopes (HoareFun (ginv sk0) (stb sk0)
                    fsp.(precond) fsp.(postcond) fbody arg)))
  | thread_rel_body (Q: Any.t -> Any.t -> iProp) l itrS itrT
      (* Q should give vret = ret if cid = 0. (return of main function)*)
      (STACK: valid_stack l)
      (REL: @elim_rel _ ginv stb sk0 _ l itrS itrT)
      (SRC: src = tau;; interp_hp itrS)
      (TGT: tgt =
        (interp_hp
            ((if Nat.eq_dec tid cid then Ret tt else yield_post sk0);;; tau;;
            (* ((if Nat.eq_dec tid cid then Ret tt else trigger (Assume (ginv sk0 tid)));;; *)
              vret <- itrT;; 
              (inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)))
                ( ret <- trigger (Choose Any.t);;
                  trigger (Guarantee (Q vret ret));;;
                  Ret ret)))))
  .

  (* H6: Own a1 ⊢ ginv sk0 (base.length tgts) -∗ precond f (base.length tgts) x args x0
  H7: Own a2 ⊢ Own x1
  k: nat
  x3: Σ
  y, z: itree modE Any.t
  NEQ: cid ≠ k
  LKX: (frs ++ [ε]) !! k = Some x3
  LKY:
    (srcs ++
     [` sem : (Any.t → itree modE Any.t) <-
      (alist_find fn
         (List.map (map_snd (interp_hp_fun <*> HModSem.sandbox_body))
            (List.map (map_snd (wrap_elimI (SModSemAux.to_hmod (SMod.modsem md sk0))))
               (List.map (map_snd (λ ksb : list string * fspecbody, (ksb.1, fsb_body ksb.2))) (SModSem.fnsems (SMod.modsem md sk0)))))) !;; sem args]) !! k = 
    Some y
  LKZ:
    (tgts ++
     [` sem : (Any.t → itree modE Any.t) <-
      (alist_find fn
         (List.map (map_snd (interp_hp_fun <*> HModSem.sandbox_body))
            (List.map (map_snd (wrap_elimI (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))))
               (List.map (map_snd (λ ksb : list string * fspecbody, (ksb.1, interp_sb_hp (ginv sk0) (stb sk0) ksb.2))) (SModSem.fnsems (SMod.modsem md sk0)))))) !;; 
      sem x0]) !! k = Some z *)

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

  Lemma valid_extends (r a b: Σ):
    b ≼ a -> ✓(r ⋅ a) -> ✓ (r ⋅ b).
  Proof.
    i. apply cmra_mono_l with (z:=r) in H.
    eapply cmra_valid_included; eauto.
  Qed.

  Lemma Own_bupd_valid (r a b: Σ):
    (Own r ⊢|==> Own a ∗ Own b) -> ✓ r -> ✓ (a ⋅ b).
  Proof.
    i. eapply Own_wand_valid with (a1 := r); eauto.
    iIntros "H". iApply Own_op. iStopProof. eauto.
  Qed.

  Lemma extends_Own
        (a b : Σ)
        (OWN: Own b ⊢ Own a) 
    :
      a ≼ b.
  Proof. Admitted.

  Lemma cancel_aux rs0 rt0 sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0):
    ∀ rs rt srcs tgts cid st ps pt
       (WF: ✓ rs)       
       (LEN: cid < List.length srcs)
       (REL: Forall2i (thread_rel sk0 cid) 0 srcs tgts)
       (UPD: Own rs ==∗ Own rt)
       ,
       gpaco7 _simg (cpn7 _simg) bot7 bot7 Any.t Any.t eq ps pt
       (x <-
         interp_stateE Any.t
           (ITree.iter
              (handle_schE_callE
                 (* (progS sk0 rs)) *)
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
                (* (progT sk0 (rs ⋅ mr))) *)
                 (ModSem.prog
                    (HModSem.to_mod
                       (HModSemAux.inline
                         (SModSem.to_hmod (ginv sk0) 
                            (stb sk0) (SMod.modsem md sk0))) rt0))) 
              (cid, tgts))
         (Any.pair st rt↑);; Ret x.2).
  Proof. 
    (* gcofix CIH.  *)
    i. exploit Forall2i_nth; eauto. i. des.
    rename x into src, y into tgt.
    depdes x2; [nia|].
    hexploit REL. i. eapply Forall2i_len in H. des.
    assert (cid < List.length tgts). { rewrite <- H. eauto. }

    assert (RELS: forall k x y (NEQ: cid ≠ k)
                    (LKX: srcs !! k = Some x)
                    (LKY: tgts !! k = Some y),
                    (* (LKZ: tgts !! k = Some z), *)
                      thread_rel sk0 cid k x y). 
    { admit. }

    (* Need to keep some information about other threads before remove REL. *)
    clear REL. rename REL0 into REL. unfold elim_rel in REL.
    
    (* _iter. _iter. rewrite x0 x1. grind. clear x0 x1 e. *)

    revert_until SKWF. s. gcofix CIH. i.

    _iter. _iter. rewrite x7 x8. grind.


    assert (✓ rt). { eapply cmra_valid_included; eauto. admit. } 
    (* _iter. _iter. rewrite x7 x8. grind. *)

    punfold REL. 
    pattern itrS, itrT. depdes REL.
    - ired. hide_l. _coreA.
    - (* ret *)
      (* ired. des_ifs; cycle 1.
      { unfold triggerUB. ired. _coreA. }
      ired. _core. st. i. st. ired. _tau. st. 
      iterL. _tau. st. st. iterL. _tau. st. st. ls. 
      iterL. _supd.
      iterL. _core. st. i. st. ired. _tau. st.
      iterL. _core. st. i. st. ired. _tau. st.
      iterL. _supd. iterL. _supd.
      iterL. _tau. st. st. iterL. _tau. st. st.
      iterL. rewrite !StRed.ret. ired. st. *)
      (* Q should give v1 = x *)
      admit. 

    - (* tau *)
      (* ired. _tau. do 4 st. prb.
      gbase. pclearbot. iterL. iterL. 
      eapply CIH; eauto; try (rewrite !length_insert; nia); try (rewrite list_lookup_insert; grind).
      i. rewrite !list_lookup_insert_ne in LKX, LKY; eauto. *)
      admit.

    - (* core *)
      (* ired. depdes e0.
      + hide_l. _coreA. iterT 3.
        reveal ITREE. hide_r. _coreE x. iterT 1.
        reveal ITREE. prb. gbase. pclearbot.
        eapply CIH; eauto; try (rewrite length_insert; nia); try (rewrite list_lookup_insert; grind).
        i. rewrite !list_lookup_insert_ne in LKX, LKY; eauto.
      + hide_r. _coreA. iterT 1.
        reveal ITREE. hide_l. _coreE x. iterT 3. 
        reveal ITREE. prb. gbase. pclearbot.
        eapply CIH; eauto; try (rewrite length_insert; nia); try (rewrite list_lookup_insert; grind).
        i. rewrite !list_lookup_insert_ne in LKX, LKY; eauto.
      + hide_l. _core. reveal ITREE. hide_r. _core. reveal ITREE. st. i. subst. 
        hide_l. st. ired. tau 1. iterT 3.
        reveal ITREE. hide_r. st. ired. tau 1. iterT 1.
        reveal ITREE. prb. gbase. pclearbot.
        eapply CIH; eauto; try (rewrite length_insert; nia); try (rewrite list_lookup_insert; grind).
        i. rewrite !list_lookup_insert_ne in LKX, LKY; eauto. *)
      admit.
    - (* put/get *)
      (* ired. depdes e0.
      + hide_l. grind. _supd. iterL. _supd. iterT 3.
        reveal ITREE. hide_r. 
        grind. _supd. iterL. _supd. iterT 1.
        reveal ITREE. prb. gbase. pclearbot.
        eapply CIH; eauto; try (rewrite length_insert; nia); try (rewrite list_lookup_insert; grind).
        i. rewrite !list_lookup_insert_ne in LKX, LKY; eauto.
      + hide_l. grind. _supd. iterT 3.
        reveal ITREE. hide_r.
        grind. _supd. iterT 1.
        reveal ITREE. prb. gbase. pclearbot.
        eapply CIH; eauto; try (rewrite length_insert; nia); try (rewrite list_lookup_insert; grind).
        i. rewrite !list_lookup_insert_ne in LKX, LKY; eauto. *)
      admit.
    - (* Assume *)
      (* ired. hide_r. _coreA.
      iterL. _supd. 
      iterL. _coreA. iterL. _coreA.
      iterL. _supd. iterL. _supd.
      iterT 1.
      reveal ITREE. hide_l. _coreE x.
      assert (✓ (x ⋅ rt)). { eapply valid_extends; eauto. }
      iterL. _supd. iterL. _coreE H. ls.
      iterL. _coreE x1. ls. 
      iterL. _supd. iterL. _supd.
      iterT 3.
      reveal ITREE. prb. gbase. pclearbot.
      eapply CIH; eauto; try (rewrite !length_insert; nia); try (rewrite list_lookup_insert; grind).
      { eapply cmra_mono_l; eauto. }
      i. rewrite !list_lookup_insert_ne in LKX, LKY; eauto. *)
      admit.
    - (* Guarantee *)
      (* ired. hide_l. _supd.
      iterL. _coreA. iterL. _coreA.
      iterL. _supd. iterL. _supd. iterT 3.
      reveal ITREE. hide_r. _supd.
      assert (Own rs ==∗ P ∗ Own x).
      {
        iIntros "H". iApply x0. iStopProof.
        eapply Own_extends; eauto.
      }
      iterL. _coreE x. iterL. _coreE H.
      iterL. _supd. iterL. _supd. iterT 1.
      reveal ITREE. prb. gbase. pclearbot.
      eapply CIH; eauto; try (rewrite !length_insert; nia); try (rewrite list_lookup_insert; grind).
      { 
        hexploit Own_bupd_split; eauto. i. des.
        eapply Own_bupd_valid in H2; eauto.
        eapply Own_pure_soundness with (x:=a2).
        { eapply cmra_valid_op_r, Own_wand_valid; eauto. }
        iIntros "H". iApply Own_valid. iStopProof. eauto.
      }
      i. rewrite !list_lookup_insert_ne in LKX, LKY; eauto. *)
      admit.
    - (* Tid *)
      (* ired. hide_l. tau 1. iterT 3. 
      reveal ITREE. hide_r. tau 1. iterT 1. 
      reveal ITREE. prb. gbase. pclearbot.
      eapply CIH; eauto; try (rewrite length_insert; eauto); try (rewrite list_lookup_insert; grind).
      i. rewrite !list_lookup_insert_ne in LKX, LKY; eauto. *)
      admit.
    - (* head *)
      (* ired. hide_r. tau 2.
      reveal ITREE. hide_l. tau 1.
      iterT 2. iterL. _coreA. ls.
      iterT 2. iterL. _coreA. ls.
      iterT 2. iterL. _supd. 
      iterL. _coreA. iterL. _coreA. ls.
      iterL. _supd. iterL. _supd.
      iterT 3. iterL. ls. tau 1.
      iterT 2. iterL. _coreE x. ls.
      iterT 2. iterL. _coreE varg. ls.
      iterT 2.
      hexploit (Own_bupd_split rt); eauto.
      i. des.
      iterL. _coreE a1. ls.
      iterL. _supd.
      assert (✓ (a1 ⋅ x1)). 
      { 
        eapply Own_bupd_valid in H2; eauto. 
        eapply valid_extends with (a := a2); eauto.
        eapply extends_Own; eauto.
      }
      iterL. _coreE H5. ls.
      iterL. _coreE H3. ls.
      iterL. _supd. iterL. _supd.
      iterT 2. 
      reveal ITREE. prb. gbase. pclearbot.
      eapply CIH with (l:= _ :: l); eauto; try (rewrite !length_insert; nia); 
      try (eapply KTR); try (rewrite list_lookup_insert; grind).
      { admit. }
      { econs; eauto. }
      i. rewrite !list_lookup_insert_ne in LKX, LKY; eauto. *)
      admit.
    - (* tail *)
      (* ired. hide_r. tau 2. 
      reveal ITREE. hide_l. _coreA.
      iterT 2. iterL. _supd.
      iterL. _coreA. ls.
      iterL. _coreA. ls.
      iterL. _supd. iterL. _supd.
      iterT 4.
      iterL. _coreE vret.
      iterT 2.
      hexploit (Own_bupd_split rt); eauto.
      i. des.
      inv STACK. eapply inj_pair2 in H9, H10. subst x3 m'. rename tid' into tid.
      iterL. _coreE a1. ls.
      iterL. _supd.
      assert (✓ (a1 ⋅ x0)). 
      { 
        eapply Own_bupd_valid in H2; eauto. 
        eapply valid_extends with (a := a2); eauto.
        eapply extends_Own; eauto.
      }
      iterL. _coreE H5. ls.
      iterL. _coreE H3. ls.
      iterL. _supd. iterL. _supd.
      iterT 3. 
      reveal ITREE. prb. gbase. pclearbot. 
      eapply CIH; eauto; try (rewrite !length_insert; nia); try (rewrite list_lookup_insert; grind).
      { admit. }
      i. rewrite !list_lookup_insert_ne in LKX, LKY; eauto. *)
      admit.
    - (* spawn *)
      ired. hide_l. _coreA.
      iterT 2. iterL. _coreA. ls.
      iterT 2. iterL. tau 1. ls. 
      rewrite !length_insert. 
      rewrite <- insert_app_l; eauto.
      assert (cid <
      base.length
        (tgts ++
         [` sem : (Any.t → itree modE Any.t) <-
          (alist_find fn
             (List.map (map_snd (interp_hp_fun <*> HModSem.sandbox_body))
                (List.map (map_snd (wrap_elimI (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))))
                   (List.map (map_snd (λ ksb : list string * fspecbody, (ksb.1, interp_sb_hp (ginv sk0) (stb sk0) ksb.2)))
                      (SModSem.fnsems (SMod.modsem md sk0)))))) !;; sem x0])).
      { rewrite length_app. nia. }
      iterT 2. iterL. _supd.
      iterL. _coreA. ls. iterL. _coreA. ls.
      iterL. _supd. iterL. _supd.
      iterT 3.
      reveal ITREE. hide_r. tau 1. 
      rewrite <- insert_app_l; eauto.
      iterL; cycle 1. { rewrite length_app. nia. }
      tau 2. ls.
      reveal ITREE.
      assert (base.length srcs = base.length tgts) by nia.
      rewrite !H3. 
      hexploit (Own_bupd_split rt); eauto.
      i. des. prb. gbase. pclearbot.
      eapply CIH; eauto; try (rewrite !length_insert !length_app; s; nia).
      { admit. }
      { 
        rewrite list_lookup_insert; eauto.  
        rewrite length_app. nia.
      }
      { rewrite list_lookup_insert; grind. }
      i. rewrite !list_lookup_insert_ne in LKX, LKY; eauto.
      (*
        k < cid -> RELS.
        k > cid (new thread) -> thread_rel case 1. (* modify the definition *)
      *)
      admit.
    - (* yield *)
      ired. hide_r. tau 1.
      
      reveal ITREE. hide_l.
      _supd. iterL. _coreA. ls. iterL. _coreA. ls.
      iterL. _supd. iterL. _supd.
      iterT 2. iterL. tau 1. ls.  
      hexploit (Own_bupd_split rt); eauto. i. des.
      assert (✓ (a1 ⋅ x)). 
      { 
        eapply Own_bupd_valid in H2; eauto. 
        eapply valid_extends with (a := a2); eauto.
        eapply extends_Own; eauto.
      }
      destruct (classic (cid = tid)).
      {
        (* subst tid.
        iterT 2. iterL. tau 1. iterT 2.
        iterL. _coreE a1. iterL. _supd.
        iterL. _coreE H5. ls.
        iterL. _coreE H3. ls.
        iterL. _supd. iterL. _supd. iterT 3.
        reveal ITREE. hide_r. iterT 1. reveal ITREE.
        (* iterL. iterL.  *)
        prb. gbase. pclearbot. 
        eapply CIH; try (rewrite !length_insert; eauto); try (rewrite list_lookup_insert; grind).
        { admit. }
        { admit. }
        { admit. }
        { admit. } *)
        admit.
      }
      destruct (classic (tid < base.length srcs)); cycle 1.
      {
        (* reveal ITREE. 
        hide_r. eapply Nat.le_ngt, lookup_ge_None_2 in H3.
        _iter. rewrite list_lookup_insert_ne; [|et]. rewrite H3.
        s. unfold triggerUB. ired. _coreA. *)
        admit.
      } 
      exploit lookup_lt_is_Some_2; eauto. i. inv x2.
      exploit (lookup_lt_is_Some_2 tgts tid); [nia|]. i. inv x3.
      assert (tid < base.length tgts) by nia.
      hexploit RELS; eauto. i. 
      depdes H11.
      {
        (* new thread *)
        subst. rename x into mr'.
        erewrite <- list_lookup_insert_ne in H8; eauto.
        erewrite <- list_lookup_insert_ne in H9; eauto.
        _iter. rewrite H9. ired. tau 1.
        iterT 1. iterL. _coreE m. ls. 
        iterT 1. iterL. _coreE varg. ls.
        specialize (FR rt mr' x0). des.
        iterT 1. iterL. _coreE (a1 ⋅ fr). ls. iterL. _supd.
        (* 
        Own fr ⊢ ginv -∗ precond 
          -> ginv ⊢ precond ?
        *)
      admit.
      }
      (* another yield *)
      destruct (Nat.eq_dec tid cid); try nia.
      subst. erewrite <- list_lookup_insert_ne in H9; eauto. 
      _iter. rewrite H9. ired. tau 2.
      iterT 1. iterL. tau 1. iterT 2.
      iterL. _coreE a1. ls. iterL. _supd.
      iterL. _coreE H5. ls. iterL. _coreE H3. ls.
      iterL. _supd. iterL. _supd. iterT 2.
      erewrite <- list_lookup_insert_ne in H8; eauto. 
      reveal ITREE. prb. gbase. pclearbot. 
      eapply CIH; try (rewrite !length_insert; eauto); try (rewrite list_lookup_insert; grind); eauto.
      { admit. }
      { rewrite length_insert. nia. }
      { des_ifs. grind. }
      (**)
      i.
      
      
      
      erewrite <-list_lookup_insert_ne in H7, H8; try eapply H2. rewrite H7 H8. ired.
      hide_l. destruct (Nat.eq_dec tid cid); try nia.
      unfold yield_post. ired. tau 2.
      assert (tid < base.length tgts) by nia.
      iterT 1. iterL. tau 1. iterT 2.
      iterL. _coreE a1. ls. iterL. _supd.
      assert (✓ (a1 ⋅ x)).
      { 
        eapply Own_bupd_valid in H3; eauto. 
        eapply valid_extends with (a := a2); eauto.
        eapply extends_Own; eauto.
      }
      iterL. _coreE H10. ls. 
      iterL. _coreE H4. ls.
      iterL. _supd. iterL. _supd. 
      iterT 2. iterL. reveal ITREE.

      prm. gbase. pclearbot. 

      eapply CIH; try (rewrite !length_insert; eauto); try (rewrite list_lookup_insert; grind); try nia; eauto.
      { admit. }
      i. rewrite list_lookup_insert_ne in LKY; eauto.
      destruct (classic (cid = k)).
      {
        subst k. 
        rewrite list_lookup_insert in LKX; eauto. 
        rewrite list_lookup_insert in LKY; eauto. inv LKX.
        LKY; eauto.

      }

      { rewrite list_lookup_insert_ne; eauto. }
      { rewrite list_lookup_insert_ne; eauto. }
      { et. }
      { rewrite length_insert. ss. }
      { ss.}
      i.
      destruct (classic (cid = k)).
      {
        subst k.  
        econs 2; eauto; cycle 1.
        {
          rewrite list_lookup_insert in LKY; eauto.
          instantiate (1:= (tau;; ktrS ())). inv LKY.
          rewrite interp_hp_tau. refl.
        }
        {
          rewrite list_lookup_insert in LKZ; eauto.
          instantiate (1:= Q).
          instantiate (1:= (tau;; ktrT tt)).
          inv LKZ. des_ifs. rewrite -interp_hp_tau. 
          unfold yield_post. grind. repeat f_equal.
          extensionalities. ired. repeat f_equal.
          extensionalities. destruct H9. grind.
        }
        clear -KTR.
        ginit. gstep. econs. gfinal. right. eauto. 
      }
      rewrite list_lookup_insert_ne in LKY; eauto.
      rewrite list_lookup_insert_ne in LKZ; eauto.
      hexploit RELS; eauto. i.
      inv H9.
      { econs; eauto. }
      econs 2; eauto. des_ifs.
      admit.

  Admitted.

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

  (* Theorem cancellation P P
    (COND: forall sk0 (EQV: Sk.equiv sk sk0) (SKWF: Sk.wf sk0), 
      exists fsp m rt,
        (stb sk0 "CCR_init" = Some fsp) /\
        (forall rs (WF: ✓ rs) (SRC: Own rs ⊢ (P sk0)), ✓ (rs ⋅ rt)) /\ 
        (Own rt ⊢ (P sk0) ∗ (fsp.(precond) 0 m tt↑ tt↑)) /\
        (∀ m vret ret, (fsp.(postcond) 0 m vret ret) -∗ ⌜vret = ret⌝)
    )
  : *)

  Theorem cancellation 
      P sk0 mr fsp meta r
      (EQV: Sk.equiv sk sk0) (SKWF: Sk.wf sk0)
      (WF: HModSem.wf (md_src.(HMod.modsem) sk0))
      (STB: stb sk0 "CCR_init" = Some fsp)
      (VALID: ✓ (r ⋅ mr))
      (PRE: Own r ⊢ fsp.(precond) 0 meta tt↑ tt↑)
      (SAT: Own mr ⊢ P sk0)
      (POST: ∀ m vret ret, (fsp.(postcond) 0 m vret ret) -∗ ⌜vret = ret⌝)
    :  
      refines_modsem
        (HModSem.to_mod (md_src.(HMod.modsem) sk0) (r ⋅ mr))
        (HModSem.to_mod (md_tgt.(HMod.modsem) sk0) mr).
  Proof.
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
      grind. rewrite/__ StRed.bind. grind.
      destruct (resum IFun False (Choose False)) eqn:V.
      { inv V. }
      depdes c; inv V. resub.
      rewrite/__ [interp_stateE _ _ _]StRed.core. grind.
      ginit. st. i. ss.
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
    pose proof (stb_find_fsb SKINCL SKWF STB E). subst.
    hide_l.
    ginit.
    rewrite/__ !HModSB.transl_bind HModSB.transl_sch HIRed.bind_sch interp_hp_bind. s.
    rewrite interp_hp_tid. ired.
    _iter. _tau. st. _iter. _tau. st. st.
    rewrite interp_hp_tau. _iter. _tau. st. st.
    rewrite/__ HModSB.transl_bind HModSB.transl_core HIRed.bind_core interp_hp_bind interp_hp_core. ired.
    _iter. _core. st. exists meta. st. ired. 
    _tau. st. _iter. _tau. st. st.
    rewrite interp_hp_tau. _iter. _tau. st. st.
    rewrite/__ HModSB.transl_bind HModSB.transl_core HIRed.bind_core interp_hp_bind interp_hp_core. ired.
    _iter. _core. st. exists (tt↑). st. ired.
    _iter. _tau. st. st. st.
    rewrite interp_hp_tau. _iter. _tau. st. st.
    rewrite/__ HModSB.transl_bind HModSB.transl_ag HIRed.bind_ag interp_hp_bind interp_hp_Assume. ired.
    _iter. _core. st. exists r. st. ired. _tau. st. 
    _iter. _sget. ired. _tau. st. st.
    hss. ired. hss. ired.
    _iter. _core. st.
    (* { eapply (@valid_solve_eq _ _ COND0). r_solve. } *)
    exists VALID. ired. _tau. st. st. 
    _iter. _core. st. exists PRE. ired.
    _iter. _tau. st. st. _supd. _iter. _supd.
    _iter. _tau. st. st. rewrite interp_hp_tau. _iter. _tau. st. st.
    
    (* CCR_main's precond all executed. *)
    reveal ITREE. 
    eapply cancel_aux; eauto.
    (* { instantiate (1:= [a2]). ss. } *)
    (* { s. r_solve. admit. } *)
    (* { eapply (valid_solve_eq H). r_solve. } *)
    econs; eauto using Forall2i.
    econs 2; s; eauto; cycle 2.
    { 
      rewrite bind_ret_l HModSB.transl_bind HIRed.bind. 
      repeat f_equal. extensionalities.
      rewrite HModSB.transl_bind HModSB.transl_core. do 2 f_equal.
      extensionalities.
      rewrite HModSB.transl_bind HModSB.transl_ag. do 2 f_equal.
      extensionalities.
      rewrite HModSB.transl_ret. ss.
    } 
    { instantiate (1:= []). econs. }
    eapply elim_rel_refl; eauto.
  Qed.
  
  (*** Final Theorem ***)
  (* Theorem cancellation P: *)
    (* refines (md_src, (fun _ => emp)%I) (md_tgt, P). *)
  (* Proof. Admitted. *)

End CANCEL.
