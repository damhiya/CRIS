Require Import Common.
Require Import SMod2HMod HMod2Mod Mod2ITree SMod HMod Mod Skeleton.
Require Import SimGlobal.
Require Import SMod2HModAux HModInline ElimRel StRed CancelDef.

(* Trivial Cases *)

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

  Let md_src: HMod.t := SModAux.to_hmod md.
  Let md_tgt: HMod.t := SMod.to_hmod ginv stb md.

  Import CancelTAC.

  Lemma cancel_main_ret
    sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
    r X (meta: X) (rs0 rt0 rs rt: Σ) v  Q cid st ps pt
    (srcs tgts: list (itree modE Any.t))
    (WFT: ✓ rt)
    (LENS: cid < base.length srcs)
    (LENT: cid < base.length tgts)
    (RET: ∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝)
  :
  gpaco7 _simg (cpn7 _simg) bot7 r Any.t Any.t eq ps pt
  (x <-
   interp_stateE Any.t
     (x_ <- (if Nat.eq_dec cid 0 then Ret (inr v) else triggerUB);;
      match x_ with
      | inl l => tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) l
      | inr r0 => Ret r0
      end) (Any.pair st rs ↑);; Ret x.2)
  (x <-
   interp_stateE Any.t
     (x_ <- trigger (Choose Any.t)%sum;;
      x_0 <-
      Ret
        (inl
           (cid,
            <[cid:=lr <-
                   ITree.subst
                     (λ x : Any.t,
                        Ret
                          (inl
                             (ITree.subst
                                (λ lr : itree hmodE Any.t + Any.t,
                                   match lr with
                                   | inl l => tau;; ITree.iter (handle_callE (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)))) l
                                   | inr r0 => Ret r0
                                   end) (ITree.subst (λ v0 : Any.t, Ret (inl (ITree.subst (λ ret : Any.t, trigger (Guarantee (Q cid meta v ret));;; Ret ret) (Ret v0)))) (Ret x)))))
                     (Ret x_);; match lr with
                                | inl l => tau;; interp_hp l
                                | inr r0 => Ret r0
                                end]> tgts));;
      match x_0 with
      | inl l => tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) l
      | inr r0 => Ret r0
      end) (Any.pair st rt ↑);; Ret x.2)
  .
  Proof. 
    hide_r. des_ifs; cycle 1.
    { unfold triggerUB. ired. _coreA. }
    ired. reveal ITREE.
    _coreA. iterT 2. 
    iterL. _supd. iterL. _coreA. ls.
    iterL. _coreA. ls. iterL. _supd. iterL. _supd.
    iterT 2. iterL. rewrite !StRed.ret. ired. st.
    hexploit Own_bupd_split; eauto. i. des.
    specialize (RET v x ltac:(refl)).
    eapply Own_pure_soundness with (x := a1).
    {
      eapply Own_bupd_valid in WFT; eauto.
      eapply cmra_valid_op_l; eauto.
    }
    etrans; eauto.
  Qed.

  Lemma cancel_main_tau
    sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
    X (meta: X) (rs0 rt0 rs rt: Σ) Q cid st ps pt l
    srcs tgts itrS itrT
    (LENS: cid < base.length srcs)
    (LENT: cid < base.length tgts)
    (LEN: base.length srcs = base.length tgts)
    (WF: ✓ rs)
    (UPD: Own rs ==∗ Own rt)
    (RET: ∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝)
    (ITR: upaco3 (@elim_rel_def _ ginv stb sk0 _) bot3 l itrS itrT)
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
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) (cid, srcs)) (Any.pair st rs ↑);; Ret x.2)
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) (cid, tgts)) (Any.pair st rt ↑);; Ret x.2))
  :
  gpaco7 _simg (cpn7 _simg) bot7 r Any.t Any.t eq ps pt
  (x <- interp_stateE Any.t (tau;; tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0)))
    (cid, <[cid:=interp_hp itrS]> srcs)) (Any.pair st rs ↑);; Ret x.2)
  (x <- interp_stateE Any.t (tau;; tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0)))
    (cid, <[cid:=interp_hp (vret <- itrT;; inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret))]> tgts)) (Any.pair st rt ↑);; Ret x.2).
  Proof.
    tau 4. prb. gbase. pclearbot. 
    eapply CIH; eauto; try (rewrite !length_insert; nia); try (rewrite list_lookup_insert; grind).
    i. rewrite !list_lookup_insert_ne in H0, H1; eauto.
  Qed.
  
  Lemma cancel_main_core
    sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
    X (meta: X) (rs0 rt0 rs rt: Σ) Q cid st ps pt l R (e:coreE R)
    srcs tgts ktrS ktrT
    (LENS: cid < base.length srcs)
    (LENT: cid < base.length tgts)
    (LEN: base.length srcs = base.length tgts)
    (WF: ✓ rs)
    (UPD: Own rs ==∗ Own rt)
    (RET: ∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝)
    (KTR: ∀ v : R, upaco3 (@elim_rel_def _ ginv stb sk0 _) bot3 l (ktrS v) (ktrT v))
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
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) (cid, srcs)) (Any.pair st rs ↑);; Ret x.2)
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) (cid, tgts)) (Any.pair st rt ↑);; Ret x.2))
  :
  gpaco7 _simg (cpn7 _simg) bot7 r Any.t Any.t eq ps pt
  (x <- interp_stateE Any.t 
    (x_ <- trigger e;;
      x_0 <- Ret (inl (cid, <[cid:=lr <- ITree.subst (λ x : R, Ret (inl (ITree.subst ktrS (Ret x)))) (Ret x_);; 
                              match lr with
                              | inl l0 => tau;; interp_hp l0
                              | inr r0 => Ret r0
                              end]> srcs));;
      match x_0 with
      | inl l0 => tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) l0
      | inr r0 => Ret r0
      end) (Any.pair st rs ↑);; Ret x.2)
  (x <- interp_stateE Any.t
    (x_ <- trigger e;;
      x_0 <- Ret (inl (cid, <[cid:=lr <- ITree.subst (λ x : R, Ret (inl (vret <- ITree.subst (λ a : R, ktrT a) (Ret x);;
                                                                                  inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)))
                                                                                  (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret)))) (Ret x_);;
                              match lr with
                              | inl l0 => tau;; interp_hp l0
                              | inr r0 => Ret r0
                              end]> tgts));;
      match x_0 with
      | inl l0 => tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) l0
      | inr r0 => Ret r0
      end) (Any.pair st rt ↑);; Ret x.2).
  Proof.
  depdes e.
  - hide_l. _coreA. iterT 1.
    reveal ITREE. hide_r. _coreE x. iterT 1.
    reveal ITREE. prb. gbase. pclearbot.
    eapply CIH; eauto; try (rewrite !length_insert; nia); try (rewrite list_lookup_insert; grind).
    i. rewrite !list_lookup_insert_ne in H0, H1; eauto.
  - hide_r. _coreA. iterT 1.
    reveal ITREE. hide_l. _coreE x. iterT 1. 
    reveal ITREE. prb. gbase. pclearbot.
    eapply CIH; eauto; try (rewrite !length_insert; nia); try (rewrite list_lookup_insert; grind).
    i. rewrite !list_lookup_insert_ne in H0, H1; eauto.
  - hide_l. _core. reveal ITREE. hide_r. _core. reveal ITREE. st. instantiate (1:= smj_top). i. subst. 
    hide_l. st. ired. tau 1. iterT 1.
    reveal ITREE. hide_r. st. ired. tau 1. iterT 1.
    reveal ITREE. prb. gbase. pclearbot.
    eapply CIH; eauto; try (rewrite !length_insert; nia); try (rewrite list_lookup_insert; grind).
    i. rewrite !list_lookup_insert_ne in H0, H1; eauto.
  Qed.

  Lemma cancel_main_pg
    sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
    X (meta: X) (rs0 rt0 rs rt: Σ) Q cid st ps pt l R (e:pgE R)
    srcs tgts ktrS ktrT
    (LENS: cid < base.length srcs)
    (LENT: cid < base.length tgts)
    (LEN: base.length srcs = base.length tgts)
    (WF: ✓ rs)
    (UPD: Own rs ==∗ Own rt)
    (RET: ∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝)
    (KTR: ∀ v : R, upaco3 (@elim_rel_def _ ginv stb sk0 _) bot3 l (ktrS v) (ktrT v))
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
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) (cid, srcs)) (Any.pair st rs ↑);; Ret x.2)
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) (cid, tgts)) (Any.pair st rt ↑);; Ret x.2))
  :
  gpaco7 _simg (cpn7 _simg) bot7 r Any.t Any.t eq ps pt
  (x <- interp_stateE Any.t
    (x_ <- match _observe 
                          (match observe (ITree.map (λ x : R, inl (ITree.subst ktrS (Ret x))) (handle_pgE e)) with
                          | RetF r0 => 
                            match r0 with
                            | inl l0 => tau;; interp_hp l0
                            | inr r1 => Ret r1
                            end
                          | TauF t => tau;; lr <- t;; 
                            match lr with
                            | inl l0 => tau;; interp_hp l0
                            | inr r0 => Ret r0
                            end
                          | @VisF _ _ _ X0 e1 h => Vis e1 (λ x : X0, lr <- h x;; 
                            match lr with
                            | inl l0 => tau;; interp_hp l0
                            | inr r0 => Ret r0
                            end)
                          end) 
           with
          | RetF rv => if Nat.eq_dec cid 0 then Ret (inr rv) else triggerUB
          | TauF itr' => tau;; Ret (inl (cid, <[cid:=itr']> srcs))
          | @VisF _ _ _ X0 e1 k =>
            match e1 with
            | (e2|)%sum =>
                match e2 in (schE T) return ((T → itree modE Any.t) → itree (stateE +' coreE) (nat * list (itree modE Any.t) + Any.t)) with
                | Spawn fn arg =>
                    λ k0 : nat → itree modE Any.t,
                      Ret
                        (inl
                           (cid,
                            <[cid:=k0 (base.length srcs)]> srcs ++
                            [sem <-
                             (alist_find fn
                                (List.map (map_snd (interp_hp_fun ∘ HModSem.sandbox_body))
                                   (List.map (map_snd (wrap_elimI (SModSemAux.to_hmod (SMod.modsem md sk0))))
                                      (List.map (map_snd (λ ksb : list string * fspecbody, (ksb.1, interp_sb_hp_aux ksb.2))) (SModSem.fnsems (SMod.modsem md sk0)))))) !;; 
                             sem arg]))
                | Yield tid' => λ k0 : () → itree modE Any.t, Ret (inl (tid', <[cid:=k0 ()]> srcs))
                | Tid => λ k0 : nat → itree modE Any.t, Ret (inl (cid, <[cid:=k0 cid]> srcs))
                end k
            | (|s)%sum =>
                match s with
                | (e2|)%sum => Ret (inl (cid, <[cid:=x <- ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0) e2;; (tau;; k x)]> srcs))
                | (|e2)%sum => v <- trigger e2;; Ret (inl (cid, <[cid:=k v]> srcs))
                end
            end
          end;;
          match x_ with
          | inl l0 => tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) l0
          | inr r0 => Ret r0
          end) (Any.pair st rs ↑);; Ret x.2)
  (x <-
   interp_stateE Any.t
     (x_ <-
      match
        _observe
          match
            observe
              (ITree.map
                 (λ x : R,
                    inl
                      (vret <- ITree.subst (λ a : R, ktrT a) (Ret x);;
                       inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)))
                         (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret))) (handle_pgE e))
          with
          | RetF r0 => match r0 with
                       | inl l0 => tau;; interp_hp l0
                       | inr r1 => Ret r1
                       end
          | TauF t => tau;; lr <- t;; match lr with
                                      | inl l0 => tau;; interp_hp l0
                                      | inr r0 => Ret r0
                                      end
          | @VisF _ _ _ X0 e1 h => Vis e1 (λ x : X0, lr <- h x;; match lr with
                                                                 | inl l0 => tau;; interp_hp l0
                                                                 | inr r0 => Ret r0
                                                                 end)
          end
      with
      | RetF rv => if Nat.eq_dec cid 0 then Ret (inr rv) else triggerUB
      | TauF itr' => tau;; Ret (inl (cid, <[cid:=itr']> tgts))
      | @VisF _ _ _ X0 e1 k =>
          match e1 with
          | (e2|)%sum =>
              match e2 in (schE T) return ((T → itree modE Any.t) → itree (stateE +' coreE) (nat * list (itree modE Any.t) + Any.t)) with
              | Spawn fn arg =>
                  λ k0 : nat → itree modE Any.t,
                    Ret
                      (inl
                         (cid,
                          <[cid:=k0 (base.length tgts)]> tgts ++
                          [sem <-
                           (alist_find fn
                              (List.map (map_snd (interp_hp_fun ∘ HModSem.sandbox_body))
                                 (List.map (map_snd (wrap_elimI (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))))
                                    (List.map (map_snd (λ ksb : list string * fspecbody, (ksb.1, interp_sb_hp (ginv sk0) (stb sk0) ksb.2))) (SModSem.fnsems (SMod.modsem md sk0))))))
                           !;; sem arg]))
              | Yield tid' => λ k0 : () → itree modE Any.t, Ret (inl (tid', <[cid:=k0 ()]> tgts))
              | Tid => λ k0 : nat → itree modE Any.t, Ret (inl (cid, <[cid:=k0 cid]> tgts))
              end k
          | (|s)%sum =>
              match s with
              | (e2|)%sum =>
                  Ret
                    (inl
                       (cid, <[cid:=x <- ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0) e2;; (tau;; k x)]> tgts))
              | (|e2)%sum => v <- trigger e2;; Ret (inl (cid, <[cid:=k v]> tgts))
              end
          end
      end;;
      match x_ with
      | inl l0 => tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) l0
      | inr r0 => Ret r0
      end) (Any.pair st rt ↑);; Ret x.2).
  Proof.
    depdes e.
    - hide_l. grind. _supd. iterL. _supd. iterT 1.
      reveal ITREE. hide_r. 
      grind. _supd. iterL. _supd. iterT 1.
      reveal ITREE. prb. gbase. pclearbot.
      eapply CIH; eauto; try (rewrite !length_insert; nia); try (rewrite list_lookup_insert; grind).
      i. rewrite !list_lookup_insert_ne in H0, H1; eauto.
    - hide_l. grind. _supd. iterT 1.
      reveal ITREE. hide_r.
      grind. _supd. iterT 1.
      reveal ITREE. prb. gbase. pclearbot.
      eapply CIH; eauto; try (rewrite !length_insert; nia); try (rewrite list_lookup_insert; grind).
      i. rewrite !list_lookup_insert_ne in H0, H1; eauto.
  Qed.

  Lemma cancel_main_asm
    sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
    X (meta: X) (rs0 rt0 rs rt: Σ) Q cid st ps pt l P
    srcs tgts ktrS ktrT
    (LENS: cid < base.length srcs)
    (LENT: cid < base.length tgts)
    (LEN: base.length srcs = base.length tgts)
    (WF: ✓ rs)
    (UPD: Own rs ==∗ Own rt)
    (RET: ∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝)
    (KTR: upaco3 (@elim_rel_def _ ginv stb sk0 _) bot3 l (ktrS ()) (ktrT ()))
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
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) (cid, srcs)) (Any.pair st rs ↑);; Ret x.2)
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) (cid, tgts)) (Any.pair st rt ↑);; Ret x.2))
  :
  gpaco7 _simg (cpn7 _simg) bot7 r Any.t Any.t eq ps pt
  (x <-
   interp_stateE Any.t
     (x_ <- trigger (Take Σ);;
      x_0 <-
      Ret
        (inl
           (cid,
            <[cid:=lr <-
                   ITree.subst (λ x : (), Ret (inl (ITree.subst ktrS (Ret x))))
                     (ITree.subst (λ r0 : Σ, mr <- mget_res;; assume (✓ (r0 ⋅ mr));;; assume (Own r0 ⊢ P);;; mput_res (r0 ⋅ mr)) (Ret x_));;
                   match lr with
                   | inl l0 => tau;; interp_hp l0
                   | inr r0 => Ret r0
                   end]> srcs));;
      match x_0 with
      | inl l0 => tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) l0
      | inr r0 => Ret r0
      end) (Any.pair st rs ↑);; Ret x.2)
  (x <-
   interp_stateE Any.t
     (x_ <- trigger (Take Σ);;
      x_0 <-
      Ret
        (inl
           (cid,
            <[cid:=lr <-
                   ITree.subst
                     (λ x : (),
                        Ret
                          (inl
                             (vret <- ITree.subst (λ a : (), ktrT a) (Ret x);;
                              inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)))
                                (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret))))
                     (ITree.subst (λ r0 : Σ, mr <- mget_res;; assume (✓ (r0 ⋅ mr));;; assume (Own r0 ⊢ P);;; mput_res (r0 ⋅ mr)) (Ret x_));;
                   match lr with
                   | inl l0 => tau;; interp_hp l0
                   | inr r0 => Ret r0
                   end]> tgts));;
      match x_0 with
      | inl l0 => tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) l0
      | inr r0 => Ret r0
      end) (Any.pair st rt ↑);; Ret x.2).
  Proof.
    hide_r. _coreA. iterL. _supd. 
    iterL. _coreA. iterL. _coreA.
    iterL. _supd. iterL. _supd. iterT 1.
    reveal ITREE. hide_l. _coreE x.
    assert (UPD': Own(x ⋅ rs) ==∗ Own (x ⋅ rt)).
    { iIntros "[H0 H1]". iSplitL "H0"; eauto.
      iApply UPD; eauto.
    }
    assert (✓ (x ⋅ rt)). 
    { 
      hexploit Own_bupd_valid; eauto.
      iIntros "H". iPoseProof (UPD' with "H") as ">[H0 H1]".
      iModIntro. iFrame.
    }
    iterL. _supd. iterL. _coreE H. ls.
    iterL. _coreE x1. ls. 
    iterL. _supd. iterL. _supd.
    iterT 1.
    reveal ITREE. prb. gbase. pclearbot.
    eapply CIH; eauto; try (rewrite !length_insert; nia); try (rewrite list_lookup_insert; grind).
    i. rewrite !list_lookup_insert_ne in H1, H2; eauto.
  Qed.




  Lemma cancel_main_grt
    sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
    X (meta: X) (rs0 rt0 rs rt: Σ) Q cid st ps pt l P
    srcs tgts ktrS ktrT
    (LENS: cid < base.length srcs)
    (LENT: cid < base.length tgts)
    (LEN: base.length srcs = base.length tgts)
    (WF: ✓ rs)
    (UPD: Own rs ==∗ Own rt)
    (RET: ∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝)
    (KTR: upaco3 (@elim_rel_def _ ginv stb sk0 _) bot3 l (ktrS ()) (ktrT ()))
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
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) (cid, srcs)) (Any.pair st rs ↑);; Ret x.2)
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) (cid, tgts)) (Any.pair st rt ↑);; Ret x.2))
  :
  gpaco7 _simg (cpn7 _simg) bot7 r Any.t Any.t eq ps pt
  (x <-
   interp_stateE Any.t
     (x_ <- trigger sGet;;
      x_0 <-
      Ret
        (inl
           (cid,
            <[cid:=lr <-
                   ITree.subst (λ x : (), Ret (inl (ITree.subst ktrS (Ret x))))
                     (ITree.subst (λ mr : Σ, mr' <- trigger (Choose Σ);; guarantee (Own mr ==∗ P ∗ Own mr');;; mput_res mr')
                        (ITree.subst (λ st0 : Any.t, x_0 <- (Any.split st0) ?;; (let (_, mr) := x_0 in (mr ↓) ?)) (Ret x_)));;
                   match lr with
                   | inl l0 => tau;; interp_hp l0
                   | inr r0 => Ret r0
                   end]> srcs));;
      match x_0 with
      | inl l0 => tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) l0
      | inr r0 => Ret r0
      end) (Any.pair st rs ↑);; Ret x.2)
  (x <-
   interp_stateE Any.t
     (x_ <- trigger sGet;;
      x_0 <-
      Ret
        (inl
           (cid,
            <[cid:=lr <-
                   ITree.subst
                     (λ x : (),
                        Ret
                          (inl
                             (vret <- ITree.subst (λ a : (), ktrT a) (Ret x);;
                              inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0)))
                                (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta vret ret));;; Ret ret))))
                     (ITree.subst (λ mr : Σ, mr' <- trigger (Choose Σ);; guarantee (Own mr ==∗ P ∗ Own mr');;; mput_res mr')
                        (ITree.subst (λ st0 : Any.t, x_0 <- (Any.split st0) ?;; (let (_, mr) := x_0 in (mr ↓) ?)) (Ret x_)));;
                   match lr with
                   | inl l0 => tau;; interp_hp l0
                   | inr r0 => Ret r0
                   end]> tgts));;
      match x_0 with
      | inl l0 => tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) l0
      | inr r0 => Ret r0
      end) (Any.pair st rt ↑);; Ret x.2).
  Proof.
      ired. hide_l. _supd.
      iterL. _coreA. iterL. _coreA.
      iterL. _supd. iterL. _supd. iterT 1.
      reveal ITREE. hide_r. _supd.
      assert (Own rs ==∗ P ∗ Own x).
      {
        iIntros "H". iPoseProof (UPD with "H") as ">H". 
        iApply x0; eauto.
      }
      iterL. _coreE x. iterL. _coreE H.
      iterL. _supd. iterL. _supd. iterT 1.
      reveal ITREE. prb. gbase. pclearbot.
      eapply CIH; eauto; try (rewrite !length_insert; nia); try (rewrite list_lookup_insert; grind).
      { 
        hexploit Own_bupd_split; eauto. i. des.
        eapply Own_bupd_valid in H0; eauto.
        eapply Own_pure_soundness with (x:=a2).
        { eapply cmra_valid_op_r, Own_wand_valid; eauto. }
        iIntros "H". iApply Own_valid. iStopProof. eauto.
      }
      i. rewrite !list_lookup_insert_ne in H1, H2; eauto.
  Qed.

  Lemma cancel_main_tid
    sk0 (SKINCL: incl sk sk0) (SKWF: Sk.wf sk0)
    X (meta: X) (rs0 rt0 rs rt: Σ) Q cid st ps pt l
    srcs tgts ktrS ktrT
    (LENS: cid < base.length srcs)
    (LENT: cid < base.length tgts)
    (LEN: base.length srcs = base.length tgts)
    (WF: ✓ rs)
    (UPD: Own rs ==∗ Own rt)
    (RET: ∀ vret ret : Any.t, cid = 0 → Q cid meta vret ret ⊢ ⌜vret = ret⌝)
    (KTR: ∀ (tid: nat), upaco3 (@elim_rel_def _ ginv stb sk0 _) bot3 l (ktrS tid) (ktrT tid))
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
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0))) (cid, srcs)) (Any.pair st rs ↑);; Ret x.2)
                  (x <- interp_stateE Any.t (ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0))) (cid, tgts)) (Any.pair st rt ↑);; Ret x.2))
  :
  gpaco7 _simg (cpn7 _simg) bot7 r Any.t Any.t eq ps pt
  (x <- interp_stateE Any.t (tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSemAux.to_hmod (SMod.modsem md sk0))) rs0)))
    (cid, <[cid:=tau;; interp_hp (ktrS cid)]> srcs)) (Any.pair st rs ↑);; Ret x.2)
  (x <- interp_stateE Any.t (tau;; ITree.iter (handle_schE_callE (ModSem.prog (HModSem.to_mod (HModSemAux.inline (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) rt0)))
    (cid, <[cid:=tau;; interp_hp (x_ <- ktrT cid;; inline_hp (prog (SModSem.to_hmod (ginv sk0) (stb sk0) (SMod.modsem md sk0))) (ret <- trigger (Choose Any.t);; trigger (Guarantee (Q cid meta x_ ret));;; Ret ret))]> tgts)) (Any.pair st rt ↑);; Ret x.2).
  Proof.
    hide_l. tau 1. iterT 1. 
    reveal ITREE. hide_r. tau 1. iterT 1. 
    reveal ITREE. prb. gbase. pclearbot.
    eapply CIH; eauto; try (rewrite !length_insert; eauto); try (rewrite list_lookup_insert; grind).
    i. rewrite !list_lookup_insert_ne in H0, H1; eauto.
  Qed.

End CANCEL.

(* 57 sec *)
