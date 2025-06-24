Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import ModSim Sandbox HMod.

Variant contextuality : Type := 
| open 
| closed.

Section IST.

  Context `{Σ: GRA}.

  Definition Ist_monotone (Ist: nat → alist key Any.t → alist key Any.t → iProp Σ) : Prop :=
    ∀ nths nths' (LE : nths <= nths') st_src st_tgt,
      Ist nths st_src st_tgt ⊢ Ist nths' st_src st_tgt.

  Definition IstProd (IstL IstR : nat -> alist key Any.t -> alist key Any.t -> iProp Σ) :=
  fun nths (st_src st_tgt : alist key Any.t) =>
    (∃ st_srcL st_tgtL st_srcR st_tgtR,
     ⌜st_src = st_srcL ++ st_srcR /\ st_tgt = st_tgtL ++ st_tgtR⌝ ∗
     IstL nths st_srcL st_tgtL ∗ IstR nths st_srcR st_tgtR)%I.

  Definition IstSB scopes (Ist : nat -> alist key Any.t -> alist key Any.t -> iProp Σ) :=
    fun nths st_src st_tgt =>
      (⌜incl (HMod.state_scopes st_src) scopes ∧
         incl (HMod.state_scopes st_tgt) scopes⌝
           ∗ Ist nths st_src st_tgt)%I.

  Definition IstEq : nat -> alist key Any.t -> alist key Any.t -> iProp Σ :=
    (fun _ st_src st_tgt => ⌜st_src = st_tgt⌝)%I.

  Definition ist_with_eq (Ist : nat -> alist key Any.t -> alist key Any.t -> iProp Σ) {R} :=
    fun nths '(st_src, v_src) '(st_tgt, v_tgt) =>
      (⌜v_src = (v_tgt: R)⌝ ∗ Ist nths st_src st_tgt)%I.

  Definition IstTrue : nat → alist key Any.t → alist key Any.t → iProp Σ
    := λ _ _ _, True%I.

  Definition IstFalse : nat → alist key Any.t → alist key Any.t → iProp Σ
    := λ _ _ _, False%I.

End IST.

Section HSIM.

  Context `{Σ : GRA}.
  Variable contextual: contextuality.
  Variable fl_src : alist (option string) (Any.t → itree hmodE Any.t).
  Variable fl_tgt : alist (option string) (Any.t → itree hmodE Any.t).
  Variable Ist : nat → alist key Any.t → alist key Any.t → iProp Σ.
  Variable my_tid : nat.

  (* Note : iProp-style definition of hsupd (λ fmr, Own fmr ⊢ ∃ fmr0, |==> ⌜P fmr0⌝)
      incurs positivity problem when defining _hsim. *)
  Definition hsupd (P : Σ → Prop) : Σ → Prop :=
    λ fmr, ✓ fmr → ∃ fmr0, P fmr0 ∧ (Own fmr ⊢ |==> Own fmr0).

  Variant _hsim'
      (hsimc : ∀ Rs Rt (RR : nat → alist key Any.t * Rs → alist key Any.t * Rt → iProp Σ),
          bool → bool → nat → alist key Any.t * itree hmodE Rs → alist key Any.t * itree hmodE Rt → Σ → Prop)
      {Rs Rt} {RR : nat → alist key Any.t * Rs → alist key Any.t * Rt → iProp Σ}
      (hsimi : bool → bool → nat → alist key Any.t * itree hmodE Rs → alist key Any.t * itree hmodE Rt → Σ → Prop)
    : bool → bool → nat → alist key Any.t * itree hmodE Rs → alist key Any.t * itree hmodE Rt → Σ → Prop :=

  | hsim_ret
      (HSIM_RET : True)
      ps pt nths st_src st_tgt fmr
      v_src v_tgt
      (RET : Own fmr ⊢ |==> RR nths (st_src,v_src) (st_tgt,v_tgt))
    :
    _hsim' hsimc hsimi ps pt nths (st_src, Ret v_src) (st_tgt, Ret v_tgt) fmr

  | hsim_call
      (HSIM_CALL : True)
      ps pt nths st_src st_tgt fmr
      fn varg k_src k_tgt FR
      (INV : Own fmr ⊢ |==> (Ist nths st_src st_tgt ∗ FR))
      (K : ∀ vret nths0 st_src0 st_tgt0 fmr0
            (NODS : List.NoDup (List.map fst st_src0))
            (NODD : List.NoDup (List.map fst st_tgt0))
            (INV : Own fmr0 ⊢ |==> (Ist nths0 st_src0 st_tgt0 ∗ FR)),
        hsimi true true nths0 (st_src0, k_src vret) (st_tgt0, k_tgt vret) fmr0)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, trigger (Call fn varg) >>= k_tgt) fmr

  | hsim_io
      (HSIM_IO : True)
      ps pt nths st_src st_tgt fmr
      I O fn (varg : I) k_src k_tgt
      (K : ∀ (vret : O), hsimi true true nths (st_src, k_src vret) (st_tgt, k_tgt vret) fmr)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, trigger (IO fn varg) >>= k_src) (st_tgt, trigger (IO fn varg) >>= k_tgt) fmr

  | hsim_inline_src
      (HSIM_INLINE_SRC : True)
      ps pt nths st_src st_tgt fmr
      fn f varg k_src i_tgt
      (FUN : alist_find (Some fn) fl_src = Some f)
      (K : hsimi true pt nths (st_src, f varg >>= (λ ret, tau;; Ret ret) >>= k_src) (st_tgt, i_tgt) fmr)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt) fmr

  | hsim_inline_tgt
      (HSIM_INLINE_TGT : True)
      ps pt nths st_src st_tgt fmr
      fn f varg i_src k_tgt
      (FUN : alist_find (Some fn) fl_tgt = Some f)
      (K : hsimi ps true nths (st_src, i_src) (st_tgt, f varg >>= (λ ret, tau;; Ret ret) >>= k_tgt) fmr)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt) fmr

  | hsim_tau_src
      (HSIM_TAU_SRC : True)
      ps pt nths st_src st_tgt fmr
      i_src i_tgt
      (K : hsimi true pt nths (st_src, i_src) (st_tgt, i_tgt) fmr)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, tau;; i_src) (st_tgt, i_tgt) fmr

  | hsim_tau_tgt
      (HSIM_TAU_TGT : True)
      ps pt nths st_src st_tgt fmr
      i_src i_tgt
      (K : hsimi ps true nths (st_src, i_src) (st_tgt, i_tgt) fmr)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, i_src) (st_tgt, tau;; i_tgt) fmr

  | hsim_take_src
      (HSIM_TAKE_SRC : True)
      ps pt nths st_src st_tgt fmr
      X k_src i_tgt
      (K : ∀ (x : X), hsimi true pt nths (st_src, k_src x) (st_tgt, i_tgt) fmr)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, trigger (Take X) >>= k_src) (st_tgt, i_tgt) fmr
            
  | hsim_choose_tgt
      (HSIM_CHOOSE_TGT : True)
      ps pt nths st_src st_tgt fmr
      X i_src k_tgt
      (K : ∀ (x : X), hsimi ps true nths (st_src, i_src) (st_tgt, k_tgt x) fmr)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, i_src) (st_tgt, trigger (Choose X) >>= k_tgt) fmr

  | hsim_choose_src
      (HSIM_CHOOSE_SRC : True)
      ps pt nths st_src st_tgt fmr
      X x k_src i_tgt
      (K : hsimi true pt nths (st_src, k_src x) (st_tgt, i_tgt) fmr)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, trigger (Choose X) >>= k_src) (st_tgt, i_tgt) fmr

  | hsim_take_tgt
      (HSIM_TAKE_TGT : True)
      ps pt nths st_src st_tgt fmr
      X x i_src k_tgt
      (K : hsimi ps true nths (st_src, i_src) (st_tgt, k_tgt x) fmr)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, i_src) (st_tgt, trigger (Take X) >>= k_tgt) fmr

  | hsim_sput_src
      (HSIM_SPUT_SRC : True)
      ps pt nths st_src st_src0 st_tgt fmr
      k_src i_tgt
      k v
      (run : st_src0 = alist_upd k v st_src)
      (K : hsimi true pt nths (st_src0, k_src tt) (st_tgt, i_tgt) fmr)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, trigger (SPut k v) >>= k_src) (st_tgt, i_tgt) fmr

  | hsim_sput_tgt
      (HSIM_SPUT_SRC : True)
      ps pt nths st_src st_tgt st_tgt0 fmr
      i_src k_tgt 
      k v
      (run : st_tgt0 = alist_upd k v st_tgt)
      (K : hsimi ps true nths (st_src, i_src) (st_tgt0, k_tgt tt) fmr)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, i_src) (st_tgt, trigger (SPut k v) >>= k_tgt) fmr

  | hsim_sget_src
      (HSIM_SPUT_SRC : True)
      ps pt nths st_src st_tgt fmr
      k_src i_tgt
      k v
      (run : v = or_else (alist_find k st_src) tt↑)
      (K : hsimi true pt nths (st_src, k_src v) (st_tgt, i_tgt) fmr)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, trigger (SGet k) >>= k_src) (st_tgt, i_tgt) fmr
 
  | hsim_sget_tgt
      (HSIM_SPUT_SRC : True)
      ps pt nths st_src st_tgt fmr
      i_src k_tgt 
      k v
      (run : v = or_else (alist_find k st_tgt) tt↑)
      (K : hsimi ps true nths (st_src, i_src) (st_tgt, k_tgt v) fmr)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, i_src) (st_tgt, trigger (SGet k) >>= k_tgt) fmr
 
  | hsim_assume_src
      (HSIM_ASSUME_SRC : True)
      ps pt nths st_src st_tgt fmr
      iP k_src i_tgt FMR
      (CUR : Own fmr ⊢ |==> FMR)
      (K : ∀ fmr0 (NEW : Own fmr0 ⊢ |==> (iP ∗ FMR)),
          hsimi true pt nths (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, trigger (Assume iP) >>= k_src) (st_tgt, i_tgt) fmr

  | hsim_assume_precise_src
      (HSIM_ASSUME_PRECISE_SRC : True)
      ps pt nths st_src st_tgt fmr
      iP k_src i_tgt FMR
      (CUR : Own fmr ⊢ |==> precise iP ∗ FMR)
      (K : ∀ fmr0 (NEW : Own fmr0 ⊢ |==> iP ∗ FMR),
          hsimi true pt nths (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, trigger (AssumePrecise iP) >>= k_src) (st_tgt, i_tgt) fmr

  | hsim_guarantee_tgt
      (HSIM_GUARANTEE_TGT : True)
      ps pt nths st_src st_tgt fmr
      iP i_src k_tgt FMR
      (CUR : Own fmr ⊢ |==> FMR)
      (K : ∀ fmr0 (NEW : Own fmr0 ⊢ |==> (iP ∗ FMR)),
          hsimi ps true nths (st_src, i_src) (st_tgt, k_tgt tt) fmr0)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, i_src) (st_tgt, trigger (Guarantee iP) >>= k_tgt) fmr
            
  | hsim_guarantee_src
      (HSIM_GUARANTEE_SRC : True)
      ps pt nths st_src st_tgt fmr
      iP k_src i_tgt FMR
      (CUR : Own fmr ⊢ |==> (iP ∗ FMR))
      (K : ∀ fmr0 (NEW : Own fmr0 ⊢ |==> FMR),
          hsimi true pt nths (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, trigger (Guarantee iP) >>= k_src) (st_tgt, i_tgt) fmr

  | hsim_assume_tgt
      (HSIM_ASSUME_TGT : True)
      ps pt nths st_src st_tgt fmr
      iP i_src k_tgt FMR
      (CUR : Own fmr ⊢ |==> (iP ∗ FMR))
      (K : ∀ fmr0 (NEW : Own fmr0 ⊢ |==> FMR),
          hsimi ps true nths (st_src, i_src) (st_tgt, k_tgt tt) fmr0)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, i_src) (st_tgt, trigger (Assume iP) >>= k_tgt) fmr

  | hsim_assume_precise_tgt
      (HSIM_ASSUME_PRECISE_TGT : True)
      ps pt nths st_src st_tgt fmr
      iP i_src k_tgt FMR
      (CUR : Own fmr ⊢ |==> FMR)
      (K : ∀ fmr0 (VALID: ✓ fmr0) (NEW : Own fmr0 ⊢ |==> precise iP ∗ FMR),
           exists FMR0,
             (Own fmr0 ⊢ |==> iP ∗ FMR0) ∧
             ∀ fmr1 (NEW1: Own fmr1 ⊢ |==> FMR0),
             hsimi ps true nths (st_src, i_src) (st_tgt, k_tgt tt) fmr1)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, i_src) (st_tgt, trigger (AssumePrecise iP) >>= k_tgt) fmr

    | hsim_assume_precise_both
      (HSIM_ASSUME_PRECISE_BOTH : True)
      ps pt nths st_src st_tgt fmr
      iP k_src k_tgt
      (K : hsimi true true nths (st_src, k_src tt) (st_tgt, k_tgt tt) fmr)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, trigger (AssumePrecise iP) >>= k_src) (st_tgt, trigger (AssumePrecise iP) >>= k_tgt) fmr

    | hsim_spawn
      (HSIM_SPAWN : True)
      ps pt nths st_src st_tgt fmr
      fn arg k_src k_tgt
      (K : hsimi true true (S nths) (st_src, k_src nths) (st_tgt, k_tgt nths) fmr)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, trigger (Spawn fn arg) >>= k_src) (st_tgt, trigger (Spawn fn arg) >>= k_tgt) fmr

  | hsim_yield
      (HSIM_YIELD : True)
      ps pt nths st_src st_tgt fmr
      tid k_src k_tgt FR
      (INV : Own fmr ⊢ |==> (Ist nths st_src st_tgt ∗ FR))
      (K : ∀ nths0 st_src0 st_tgt0 fmr0
          (NODS : List.NoDup (List.map fst st_src0))
          (NODD : List.NoDup (List.map fst st_tgt0))
          (INV : Own fmr0 ⊢ |==> (Ist nths0 st_src0 st_tgt0 ∗ FR)),
        hsimi true true nths0 (st_src0, k_src tt) (st_tgt0, k_tgt tt) fmr0)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, trigger (Yield tid) >>= k_src) (st_tgt, trigger (Yield tid) >>= k_tgt) fmr

  | hsim_call_none
      (HSIM_CALL_NONE: True)
      ps pt nths st_src st_tgt fmr
      fn varg k_src i_tgt
      (CLOSED: contextual = closed)
      (FUN: alist_find (Some fn) fl_src = None)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt) fmr

  | hsim_spawn_none
      (HSIM_SPAWN_NONE: True)
      ps pt nths st_src st_tgt fmr
      fn varg k_src i_tgt
      (CLOSED: contextual = closed)
      (FUN: alist_find (Some fn) fl_src = None)
    :
    _hsim' hsimc hsimi ps pt nths (st_src, trigger (Spawn fn varg) >>= k_src) (st_tgt, i_tgt) fmr
           
  | hsim_progress
      (HSIM_PROGRESS : True)
      nths sti_src sti_tgt fmr
      (SIM : hsimc Rs Rt RR false false nths sti_src sti_tgt fmr)
    :
    _hsim' hsimc hsimi true true nths sti_src sti_tgt fmr.

  Global Arguments _hsim' hsimc {Rs Rt} RR hsimi.

  Inductive _hsim hsim Rs Rt RR ps pt nths sti_src sti_tgt fmr : Prop :=
  | hsim_intro
      (IN :
        ∀ (NODFS : List.NoDup (List.map fst fl_src))
          (NODFT : List.NoDup (List.map fst fl_tgt))
          (NODS : List.NoDup (List.map fst sti_src.1))
          (NODD : List.NoDup (List.map fst sti_tgt.1)),
        hsupd (@_hsim' hsim Rs Rt RR (@_hsim hsim Rs Rt RR) ps pt nths sti_src sti_tgt) fmr).

  Definition hsim {Rs Rt} RR := paco9 _hsim bot9 Rs Rt RR.

  Lemma _hsim_tarski hsim Rs Rt RR rel
      (FIX : ∀ ps pt nths sti_src sti_tgt fmr
             (IN : ∀ (NODFS : List.NoDup (List.map fst fl_src))
                     (NODFT : List.NoDup (List.map fst fl_tgt))
                     (NODS : List.NoDup (List.map fst sti_src.1))
                     (NODD : List.NoDup (List.map fst sti_tgt.1)),
                 hsupd (@_hsim' hsim Rs Rt RR rel ps pt nths sti_src sti_tgt) fmr),
        rel ps pt nths sti_src sti_tgt fmr) :
    _hsim hsim Rs Rt RR <6= rel.
  Proof using.
    fix self 7. i.
    destruct PR. apply FIX. i. intros wf.
    specialize (IN NODFS NODFT NODS NODD wf); des.
    exists fmr0; split; eauto.
    destruct IN;
      try by econs; et; i; hexploit K; et; i; des; esplits;
      eauto using @_hsim' with paco.
  Qed.

  Lemma hsupd_mon P Q r (IN : hsupd P r) (LE : P <1= Q) : hsupd Q r.
  Proof using. by intros wf; specialize (IN wf); inv IN; exists x; split; des; eauto. Qed.

  Lemma _hsim'_mon r r' Rs Rt RR s s'
      ps pt nths sti_src sti_tgt fmr
      (REL : @_hsim' r Rs Rt RR s ps pt nths sti_src sti_tgt fmr)
      (LEr : r <9= r')
      (LEs : s <6= s') :
    @_hsim' r' Rs Rt RR s' ps pt nths sti_src sti_tgt fmr.
  Proof using. 
    ii. destruct REL.
    all: try by econs; et; i; hexploit K; et; i; des; esplits; eauto using _hsim'.
  Qed.

  Lemma _hsim_mon : monotone9 _hsim.
  Proof using.
    ii. eapply _hsim_tarski, IN.
    i. econs. eauto using hsupd_mon, _hsim'_mon.
  Qed.

  Lemma _hsim_mon_auto r r' Rs Rt RR
      ps pt nths sti_src sti_tgt fmr
      (REL : _hsim r Rs Rt RR ps pt nths sti_src sti_tgt fmr)
      (LEr : r <9= r') :
    _hsim r' Rs Rt RR ps pt nths sti_src sti_tgt fmr.
  Proof using. eapply _hsim_mon; eauto. Qed.

  Hint Constructors _hsim' _hsim : core.
  Hint Unfold hsim : core.
  Hint Resolve _hsim_mon : paco.
  Hint Resolve hsupd_mon _hsim'_mon _hsim_mon_auto : paco.
  Hint Resolve cpn9_wcompat : paco.

  Definition hsim_body ps pt nths sti_src sti_tgt fmr :=
    @hsim _ _ (@ist_with_eq _ Ist Any.t) ps pt nths sti_src sti_tgt fmr.

  Lemma hsupd_incl P : P <1= hsupd P.
  Proof using.
    ii; esplits; eauto.
  Qed.
  
  Lemma hsupd_merge P r (REL : hsupd (hsupd P) r) : hsupd P r.
  Proof using.
    intros wf; specialize (REL wf); destruct REL as [r1 [??]].
    hexploit Own_wand_valid; eauto.
    intros wf1; hexploit (H wf1); intros [fmr0 [??]]; exists fmr0; esplits; eauto.
    iIntros "R"; iPoseProof (H0 with "R") as "> R1"; iApply H2; done.
  Qed.

  Lemma hsupd_update P r r' (IN : hsupd P r) (UPD : r' ~~> r) :
    hsupd P r'.
  Proof using.
    dup UPD; rewrite cmra_discrete_update in UPD; specialize (UPD (Some ε)); ss; rewrite ?right_id in UPD.
    intros wfr'; hexploit (IN (UPD wfr')); i; des; eexists; split; eauto.
    iIntros "H"; iPoseProof (Own_Upd with "H") as "> H"; first eauto.
    iApply H0; done.
  Qed.

  Lemma hsupd_extends P r r' (IN : hsupd P r) (UPD : r ≼ r') :
    hsupd P r'.
  Proof using. eapply hsupd_update; eauto; eapply cmra_update_included; eauto. Qed.

  Lemma hsupd_wf P r (IN : ✓ r → hsupd P r) :
    hsupd P r.
  Proof using. intros wf; hexploit (IN wf wf); i; des; clarify; esplits; eauto. Qed.

  Lemma _hsim_flag_mon r Rs Rt RR (ps pt ps' pt' : bool) nths st_src st_tgt fmr
      (SIM : _hsim r Rs Rt RR ps pt nths st_src st_tgt fmr)
      (LES : ps → ps')
      (LET : pt → pt') :
    _hsim r Rs Rt RR ps' pt' nths st_src st_tgt fmr.
  Proof using.
    move SIM before r. revert_until SIM.
    pattern ps, pt, nths, st_src, st_tgt, fmr.
    eapply _hsim_tarski, SIM. i. econs.
    ii. specialize (IN NODFS NODFT NODS NODD H). des.
    destruct IN;
      try by esplits; et; econs; et; i; hexploit K; et; i; des; esplits; et.
    
    hexploit LES; eauto; i. hexploit LET; eauto; i.
    destruct ps', pt'; try discriminate. 
    econs; esplits; eauto.
  Qed.

  Lemma hsim_flag_mon Rs Rt RR (ps pt ps' pt' : bool) nths st_src st_tgt fmr
      (SIM : @hsim Rs Rt RR ps pt nths st_src st_tgt fmr)
      (LES : ps → ps')
      (LET : pt → pt') :
    hsim RR ps' pt' nths st_src st_tgt fmr.
  Proof using.
    move SIM before RR. revert_until SIM. pcofix CIH. i.
    pstep. eapply _hsim_flag_mon; eauto.
    eapply paco9_mon_bot in SIM; eauto. punfold SIM.
  Qed.

  Lemma hsim_progress_flag Rs Rt RR r g nths st_src st_tgt fmr
      (SIM : gpaco9 _hsim (cpn9 _hsim) g g Rs Rt RR false false nths st_src st_tgt fmr) :
    gpaco9 _hsim (cpn9 _hsim) r g Rs Rt RR true true nths st_src st_tgt fmr.
  Proof using.
    gstep. econs. r; esplits; eauto.
  Qed.

  (**
     hsimC
   **)
  
  Definition hsimC hsim Rs Rt RR ps pt nths sti_src sti_tgt fmr :=
    hsupd (@_hsim' hsim Rs Rt RR (hsim Rs Rt RR) ps pt nths sti_src sti_tgt) fmr.
  
  Lemma hsimC_mon : monotone9 hsimC.
  Proof using.
    ii. specialize (IN H). des.
    destruct IN;
      try by econs; esplits; et; econs; et; i; hexploit K; et; i; des; eauto.
  Qed.

  Lemma hsimC_spec : hsimC <10= gupaco9 _hsim (cpn9 _hsim).
  Proof using.
    eapply wrespect9_uclo; eauto with paco.
    econs; eauto using hsimC_mon; i.
    econs. ii. destruct PR; eauto. des. esplits; eauto.
    eapply _hsim'_mon; eauto using rclo9, _hsim_mon_auto; i.
  Qed.

  (**
     hsim_flagC
   **)
  
  Variant hsim_flagC 
      (r : ∀ (Rs Rt : Type) (RR : nat → (alist key Any.t) * Rs → (alist key Any.t) * Rt → iProp Σ),
        bool → bool → nat → (alist key Any.t) * itree hmodE Rs → (alist key Any.t) * itree hmodE Rt → Σ → Prop)
      Rs Rt RR ps1 pt1 nths st_src st_tgt fmr : Prop :=
  | hsim_flagC_intro ps0 pt0
    (SIM : r Rs Rt RR ps0 pt0 nths st_src st_tgt fmr)
    (SRC : ps0 = true → ps1 = true)
    (TGT : pt0 = true → pt1 = true).

  Lemma hsim_flagC_mon r1 r2 (LE : r1 <9= r2) :
    hsim_flagC r1 <9= hsim_flagC r2.
  Proof using. ii. destruct PR; econs; et. Qed.

  Hint Resolve hsim_flagC_mon : paco.
  
  Lemma hsim_flagC_spec : hsim_flagC <10= gupaco9 _hsim (cpn9 _hsim).
  Proof using.
    eapply wrespect9_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    eauto using _hsim_flag_mon, _hsim_mon_auto, rclo9.
  Qed.

  Lemma hsim_flag_down Rs Rt RR r g ps pt nths st_src st_tgt fmr
      (SIM : gpaco9 _hsim (cpn9 _hsim) r g Rs Rt RR false false nths st_src st_tgt fmr) :
    gpaco9 _hsim (cpn9 _hsim) r g Rs Rt RR ps pt nths st_src st_tgt fmr.
  Proof using. 
    guclo hsim_flagC_spec. econs; et. 
  Qed.

  (**
     hsim_bindC
   **)

  Variant hsim_bindC
      (r : ∀ Rs Rt (RR : nat → (alist key Any.t) * Rs → (alist key Any.t) * Rt → iProp Σ),
        bool → bool → nat → (alist key Any.t) * itree hmodE Rs → (alist key Any.t) * itree hmodE Rt → Σ → Prop)
    : ∀ Rs Rt (RR : nat → (alist key Any.t) * Rs → (alist key Any.t) * Rt → iProp Σ),
        bool → bool → nat → (alist key Any.t) * itree hmodE Rs → (alist key Any.t) * itree hmodE Rt → Σ → Prop :=
  | hsim_bindC_intro
      ps pt nths Qs Qt QQ st_src st_tgt i_src i_tgt fmr
      (SIM : r Qs Qt QQ ps pt nths (st_src, i_src) (st_tgt, i_tgt) fmr)
      Rs Rt RR k_src k_tgt
      (SIMK : ∀ nths0 st_src0 st_tgt0 vret_src vret_tgt fmr0
          (RET : Own fmr0 ⊢ |==> QQ nths0 (st_src0, vret_src) (st_tgt0, vret_tgt)),
        r Rs Rt RR false false nths0 (st_src0, k_src vret_src) (st_tgt0, k_tgt vret_tgt) fmr0)
    :
    hsim_bindC r Rs Rt RR ps pt nths (st_src, i_src >>= k_src) (st_tgt, i_tgt >>= k_tgt) fmr.

  Lemma hsim_bindC_mon r1 r2 (LEr : r1 <9= r2) : hsim_bindC r1 <9= hsim_bindC r2.
  Proof using. ii. destruct PR; econs; et. Qed.

  (* Local Hint Resolve Own_wand_valid : core. *)
  Lemma hsim_bindC_wrespectful : wrespectful9 _hsim hsim_bindC.
  Proof using.
    econs; eauto using hsim_bindC_mon; i.
    destruct PR. apply GF in SIM.
    remember (st_src, i_src) as sti_src. remember (st_tgt, i_tgt) as sti_tgt.
    move SIM before GF. revert_until SIM.
    pattern ps, pt, nths, sti_src, sti_tgt, fmr.
    eapply _hsim_tarski, SIM. econs. i. apply hsupd_merge.
    econs; esplits; eauto.
    subst. specialize (IN NODFS NODFT NODS NODD H). des.
    depdes IN; grind;
      try (by rr; i; esplits; eauto with paco);
      try (by do 2 (econs; esplits; eauto with paco);
              repeat rewrite <-bind_bind;
              eauto 7 using rclo9, hsim_bindC).
    - exploit SIMK; eauto.
      i. apply GF in x0. eapply (_hsim_flag_mon _ _ _ _ _  _ ps0 pt0) in x0; try by i; clarify.
      destruct x0. eapply hsupd_update in IN; eauto.
      eapply _hsim_mon_auto; eauto using rclo9.
      eapply Own_bupd_update; eauto.
    - esplits; et. econs; et. i. hexploit K; et; i; des. esplits; et.
  Qed.

  Lemma hsim_bindC_spec : hsim_bindC <10= gupaco9 _hsim (cpn9 _hsim).
  Proof using.
    intros. eapply wrespect9_uclo; eauto with paco.
    apply hsim_bindC_wrespectful.
  Qed.

  (**
     hsim_extendC
   **)

  Variant hsim_extendC
    (r : ∀ Rs Rt (RR : nat → (alist key Any.t) * Rs → (alist key Any.t) * Rt → iProp Σ), bool → bool → nat → (alist key Any.t) * itree hmodE Rs → (alist key Any.t) * itree hmodE Rt → Σ → Prop) :
    ∀ Rs Rt (RR : nat → (alist key Any.t) * Rs → (alist key Any.t) * Rt → iProp Σ), bool → bool → nat → (alist key Any.t) * itree hmodE Rs → (alist key Any.t) * itree hmodE Rt → Σ → Prop :=
  | hsim_extendC_intro
      ps pt nths Rs Rt RR sti_src sti_tgt fmr fmr'
      (SIM : r Rs Rt RR ps pt nths sti_src sti_tgt fmr)
      (EXT : fmr ≼ fmr') :
    hsim_extendC r Rs Rt RR ps pt nths sti_src sti_tgt fmr'.

  Lemma hsim_extendC_mon r1 r2 (LEr : r1 <9= r2) : hsim_extendC r1 <9= hsim_extendC r2.
  Proof using. ii. destruct PR; econs; et. Qed.

  Lemma hsim_extendC_compatible :
    compatible9 _hsim hsim_extendC.
  Proof using.
    econs; eauto using hsim_extendC_mon.
    intros. destruct PR. destruct SIM. econs. i.
    eapply hsupd_extends; eauto.
    eapply _hsim_mon_auto; eauto.
    i. econs; eauto; refl.
  Qed.
  
  Lemma hsim_extendC_spec : hsim_extendC <10= gupaco9 _hsim (cpn9 _hsim).
  Proof using.
    intros. gclo. econs; eauto using hsim_extendC_compatible.
    eapply hsim_extendC_mon, PR; eauto with paco.
  Qed.

  (**
     hsim_wfC
   **)

  Variant hsim_wfC (r : ∀ Rs Rt (RR : nat → (alist key Any.t) * Rs → (alist key Any.t) * Rt → iProp Σ), bool → bool → nat → (alist key Any.t) * itree hmodE Rs → (alist key Any.t) * itree hmodE Rt → Σ → Prop):
    ∀ Rs Rt (RR : nat → (alist key Any.t) * Rs → (alist key Any.t) * Rt → iProp Σ), bool → bool → nat → (alist key Any.t) * itree hmodE Rs → (alist key Any.t) * itree hmodE Rt → Σ → Prop :=
  | hsim_wfC_intro
      ps pt nths Rs Rt RR sti_src sti_tgt fmr
      (SIM : ✓ fmr → r Rs Rt RR ps pt nths sti_src sti_tgt fmr) :
    hsim_wfC r Rs Rt RR ps pt nths sti_src sti_tgt fmr.

  Lemma hsim_wfC_mon r1 r2 (LEr : r1 <9= r2) : hsim_wfC r1 <9= hsim_wfC r2 .
  Proof using. ii. destruct PR. econs; eauto using hsupd_mon. Qed.

  Lemma hsim_wfC_compatible : compatible9 _hsim hsim_wfC.
  Proof using.
    econs; eauto using hsim_wfC_mon.
    i. destruct PR. econs. i. eapply hsupd_wf. i.
    eapply _hsim_mon_auto; eauto 10 using hsim_wfC, hsupd_incl with paco.
  Qed.
  
  Lemma hsim_wfC_spec : hsim_wfC <10= gupaco9 _hsim (cpn9 _hsim).
  Proof using.
    intros. gclo. econs; eauto using hsim_wfC_compatible.
    eapply hsim_wfC_mon, PR; eauto with paco.
  Qed.
  
  (**
     hsim_updateC
   **)

  Variant hsim_updateC (r : ∀ Rs Rt (RR : nat → (alist key Any.t) * Rs → (alist key Any.t) * Rt → iProp Σ), bool → bool → nat → (alist key Any.t) * itree hmodE Rs → (alist key Any.t) * itree hmodE Rt → Σ → Prop):
    ∀ Rs Rt (RR : nat → (alist key Any.t) * Rs → (alist key Any.t) * Rt → iProp Σ), bool → bool → nat → (alist key Any.t) * itree hmodE Rs → (alist key Any.t) * itree hmodE Rt → Σ → Prop :=
  | hsim_updateC_intro
      ps pt nths Rs Rt RR sti_src sti_tgt fmr
      (SIM : hsupd (r Rs Rt RR ps pt nths sti_src sti_tgt) fmr) :
    hsim_updateC r Rs Rt RR ps pt nths sti_src sti_tgt fmr.

  Lemma hsim_updateC_mon r1 r2 (LEr : r1 <9= r2) : hsim_updateC r1 <9= hsim_updateC r2.
  Proof using. ii. destruct PR. econs; eauto using hsupd_mon. Qed.

  Lemma hsim_updateC_compatible : compatible9 _hsim hsim_updateC.
  Proof using.
    econs; eauto using hsim_updateC_mon.
    i. destruct PR. econs. i. eapply hsupd_merge.
    eapply hsupd_mon; eauto.
    i. destruct PR.
    eauto 10 using hsim_updateC, hsupd_incl with paco.
  Qed.
  
  Lemma hsim_updateC_spec : hsim_updateC <10= gupaco9 _hsim (cpn9 _hsim).
  Proof using.
    intros. gclo. econs; eauto using hsim_updateC_compatible.
    eapply hsim_updateC_mon, PR; eauto with paco.
  Qed.
  
  (**
     hsim_frameC
   **)

  Variant hsim_frameC
      (r : ∀ Rs Rt (RR : nat → (alist key Any.t) * Rs → (alist key Any.t) * Rt → iProp Σ), bool → bool → nat → (alist key Any.t) * itree hmodE Rs → (alist key Any.t) * itree hmodE Rt → Σ → Prop) :
    ∀ Rs Rt (RR : nat → (alist key Any.t) * Rs → (alist key Any.t) * Rt → iProp Σ), bool → bool → nat → (alist key Any.t) * itree hmodE Rs → (alist key Any.t) * itree hmodE Rt → Σ → Prop :=
  | hsim_frameC_intro
      ps pt nths Rs Rt RR sti_src sti_tgt fmr fmrc (CTX : iProp Σ)
      (SIM : r Rs Rt (fun n s t => CTX -∗ RR n s t)%I ps pt nths sti_src sti_tgt fmr)
      (UPD : Own fmrc ⊢ |==> (Own fmr ∗ CTX)) :
    hsim_frameC r Rs Rt RR ps pt nths sti_src sti_tgt fmrc.

  Lemma hsim_frameC_mon r1 r2 (LEr : r1 <9= r2) : hsim_frameC r1 <9= hsim_frameC r2.
  Proof using. ii. destruct PR. econs; eauto using hsupd_mon. Qed.
  
  Lemma hsim_frameC_compatible : compatible9 _hsim hsim_frameC.
  Proof using.
    econs; first by eauto using hsim_frameC_mon. ii.
    destruct PR. move SIM before r. revert_until SIM.
    pattern ps, pt, nths, sti_src, sti_tgt, fmr.
    eapply _hsim_tarski, SIM. i. econs. i.
    econs; esplits; eauto.
    exploit IN; eauto.
    { eapply Own_wand_valid; last by eauto. iIntros "O"; iMod (UPD with "O") as "[O1 O2]"; done. }
    i. des.
    assert (Own fmrc ⊢ |==> (Own fmr1 ∗ CTX)).
    { iIntros "H". iPoseProof (UPD with "H") as "H". iMod "H" as "[F C]".
      iFrame. iApply Own_Upd; eauto.
      by eapply Own_bupd_update; eauto.
    }

    depdes x0; grind; try by econs; eauto.
    - econs; eauto.
      iIntros "H". iPoseProof (UPD with "H") as "H". iMod "H" as "[HO HC]".
      iPoseProof (Own_Upd with "HO") as "HO".
      { eapply Own_bupd_update; eauto. }
      iMod "HO". iPoseProof (RET with "HO") as "HO". iMod "HO". iApply "HO". eauto.
    - econs; eauto.
      + instantiate (1:= (FR ∗ CTX)%I).
        iIntros "H". iPoseProof (UPD with "H") as "H". iMod "H" as "[H HCTX]".
        iFrame. iPoseProof (Own_Upd with "H") as "H"; eauto.
        { eapply Own_bupd_update; eauto. }
        iMod "H". iPoseProof (INV with "H") as "H". eauto.
      + i. econs. i. apply hsupd_merge. ii. esplits; eauto.
        rewrite assoc in INV0. hexploit (Own_bupd_split fmr2); eauto; i; des.
        eapply (K _ _ _ _ a1); eauto.
        { iIntros "?"; iApply H3; iFrame; done. }
        { iIntros "H"; iPoseProof (H2 with "H") as "> [H1 H2]"; iModIntro; iFrame. iApply H4; done. }

    - econs; eauto. i.
      econs. i. apply hsupd_merge. ii. esplits; eauto.
      rewrite assoc in NEW. hexploit (Own_bupd_split fmr2); eauto. i; des.
      eapply (K a1); eauto.
      { iIntros "H1"; iPoseProof (H3 with "H1") as "[P H1]". iMod (CUR with "H1") as "?"; iModIntro; iFrame. }
      { iIntros "H2"; iPoseProof (H2 with "H2") as "> [H1 H2]"; iPoseProof (H4 with "H2") as "?"; iModIntro; iFrame. }

    - hexploit Own_bupd_split; try apply CUR; et.
      { eapply Own_wand_valid in H; et. iIntros "H".
        iMod (H0 with "H") as "[H _]". et. }
      i; des.
      econs; [et|..].
      { instantiate (1:= (Own a2 ∗ CTX)%I).
        iIntros "H". iMod (H0 with "H") as "[H C]".
        iMod (H1 with "H") as "[A1 A2]".
        iPoseProof (H2 with "A1") as "A1". iFrame. et.
      }
      i. econs. i. apply hsupd_merge. ii. esplits; eauto.
      rewrite assoc in NEW. hexploit (Own_bupd_split fmr2); eauto. i; des.
      hexploit (Own_split a0); eauto.
      { eapply Own_wand_valid in H4; et. iIntros "H".
        iMod (H5 with "H") as "[H _]". et. }
      i; des.
      eapply (K (a2 ⋅ a4)); et.
      { iIntros "[A2 A4]". iSplitL "A4"; [iApply H9; et | iApply H3; et]. }
      { iIntros "H". iMod (H5 with "H") as "[H A3]". rewrite H8.
        iDestruct "H" as "[A4 A5]".
        iSplitR "A3"; [|iApply H7; et].
        iSplitR "A4"; et. iApply H10. et.
      }
      
    - econs; eauto. i.
      econs. i. apply hsupd_merge. ii. esplits; eauto.
      rewrite assoc in NEW. hexploit (Own_bupd_split fmr2); eauto. i; des.
      eapply (K a1); eauto.
      { iIntros "H1"; iPoseProof (H3 with "H1") as "[P H1]". iMod (CUR with "H1") as "?"; iModIntro; iFrame. }
      { iIntros "H2"; iPoseProof (H2 with "H2") as "> [H1 H2]"; iPoseProof (H4 with "H2") as "?"; iModIntro; iFrame. }

    - econs; eauto.
      { instantiate (1:= (FMR ∗ CTX)%I).
        iIntros "H". iPoseProof (H0 with "H") as "H". iMod "H" as "[F C]".
        iFrame. iStopProof; eauto. }
      i. econs. i. apply hsupd_merge. ii. esplits; eauto.
      hexploit (Own_bupd_split fmr2); eauto; i; des.
      eapply (K a1); eauto.
      { iIntros "H". iModIntro; iApply H3; done. }
      { iIntros "H". iPoseProof (H2 with "H") as "H". iMod "H" as "[HP HQ]".
        iFrame. iModIntro; iApply H4; done.
      }

    - econs; eauto.
      { instantiate (1:= (FMR ∗ CTX)%I).
        iIntros "H". iPoseProof (H0 with "H") as "H". iMod "H" as "[F C]".
        iFrame. iStopProof; eauto. }
      i. econs. i. apply hsupd_merge. ii. esplits; eauto.
      hexploit (Own_bupd_split fmr2); eauto; i; des.
      eapply (K a1); eauto.
      { iIntros "H". iModIntro; iApply H3; done. }
      { iIntros "H". iPoseProof (H2 with "H") as "H". iMod "H" as "[HP HQ]".
        iFrame. iModIntro; iApply H4; done.
      }

    - econs; et. i.
      hexploit (Own_bupd_split fmr2); et; i; des.
      assert (VALID2: ✓ (a1 ⋅ fmr1)).
      { eapply Own_wand_valid in VALID; et.
        rewrite H1 H3 Own_op. iIntros ">[? [? _]]". iFrame. et. }
      hexploit (K (a1 ⋅ fmr1)); et; i; des.
      { rewrite Own_op H2 CUR. iIntros "[? >?]". iFrame. et. }
      eapply Own_bupd_split in H4; et. i; des.
      
      clear K. rename H5 into K.
      eexists. esplits; cycle 1.
      + i. eapply K; cycle 1.
        * rewrite NEW1. iIntros ">H". iModIntro. iApply "H".
        * rewrite -H7. et.
      + rewrite H1 H3 assoc -(Own_op a1 fmr1) H4 H6.
        iIntros ">[>[P A] C]". iFrame. et.

    - econs; eauto.
      + instantiate (1:= (FR ∗ CTX)%I).
        iIntros "C"; iPoseProof (H0 with "C") as "> [H1 CTX]"; iPoseProof (INV with "H1") as ">?".
        iModIntro; iFrame; done.
      + i. econs. i. apply hsupd_merge. ii. esplits; eauto.
        rewrite assoc in INV0. exploit (Own_bupd_split fmr2); eauto; i; des.
        eapply (K _ _ _ a1); eauto.
        { iIntros "H2"; iModIntro; iApply x2; done. }
        { iIntros "H2"; iPoseProof (x0 with "H2") as "> [H1 H2]"; iPoseProof (x3 with "H2") as "?".
          iModIntro; iFrame.
        }

    - eauto using hsim_frameC with paco.
  Qed.

  Lemma hsim_frameC_spec : hsim_frameC <10= gupaco9 _hsim (cpn9 _hsim).
  Proof using.
    intros. gclo. econs; eauto using hsim_frameC_compatible.
    eapply hsim_frameC_mon, PR; eauto with paco.
  Qed.

  (**
     hsim_eqitC_src
   **)

  Variant hsim_eqitC_src
    (r : ∀ Rs Rt (RR : nat → (alist key Any.t) * Rs → (alist key Any.t) * Rt → iProp Σ), bool → bool → nat → (alist key Any.t) * itree hmodE Rs → (alist key Any.t) * itree hmodE Rt → Σ → Prop) :
    ∀ Rs Rt (RR : nat → (alist key Any.t) * Rs → (alist key Any.t) * Rt → iProp Σ), bool → bool → nat → (alist key Any.t) * itree hmodE Rs → (alist key Any.t) * itree hmodE Rt → Σ → Prop :=
  | hsim_eqitC_src_intro
      ps pt nths Rs Rt RR fmr st_src isrc0 isrc1 sti_tgt 
      (EQIT: eqit eq false true isrc0 isrc1)
      (SIM : r Rs Rt RR ps pt nths (st_src, isrc0) sti_tgt fmr)
    :
    hsim_eqitC_src r Rs Rt RR ps pt nths (st_src, isrc1) sti_tgt fmr.

  Lemma hsim_eqitC_src_mon r1 r2 (LEr : r1 <9= r2) : hsim_eqitC_src r1 <9= hsim_eqitC_src r2.
  Proof using. ii. destruct PR. econs; eauto using hsupd_mon. Qed.

  Lemma hsim_eqitC_src_compatible : compatible9 _hsim hsim_eqitC_src.
  Proof using.
    econs; first by eauto using hsim_eqitC_src_mon. unfold rel9. ii.
    destruct PR. remember (st_src, isrc0) as sti_src0.
    move SIM before r. revert_until SIM.
    pattern Rs, Rt, RR, ps, pt, nths, sti_src0, sti_tgt, fmr.
    eapply _hsim_tarski, SIM. i.
    econs. ii. subst. specialize (IN NODFS NODFT NODS NODD H). des.
    esplits; eauto.
    punfold EQIT. subst. rr in EQIT.
    remember (observe isrc0) as otgt0. remember (observe isrc1) as otgt1.
    move EQIT before r. revert_until EQIT.
    assert (EQIT_TAU:= @eqit_Tau). hdes. clear EQIT_TAU0.
    induction EQIT; i; subst; pclearbot.
    - ides isrc0. ides isrc1. eapply _hsim'_mon; eauto; i.
      + destruct x6. econs; eauto using eqit_refl.
      + ss. destruct x3. eauto using eqit_refl.
    - ides isrc0. ides isrc1.
      inv IN; try itree_clarify H5; eauto using _hsim', hsim_eqitC_src.
      + eapply hsim_assume_precise_tgt; et. i. hexploit K; et. i; des.
        esplits; et.
    - ides isrc0. ides isrc1. depdes H1.
      Local Hint Unfold eqit: core.
      inv IN; try itree_clarify H5;
        try (assert (REL' := bind_ret_l_forall (fun v t => _ t (k0 v)) k_src REL);
             s in REL');
        try(match goal with [|-context[vis ?e ?k]] =>
            replace (vis e k) with (x <- trigger e;; k x)
                              by (rewrite bind_vis; repeat f_equal;
                                  extensionalities; ired; eauto; fail)
            end);
      eauto using _hsim', hsim_eqitC_src, eqit_Vis.
      + eapply hsim_inline_src; eauto. eapply K; eauto.
        eapply eqit_bind; eauto using eqit_refl.
      + econs; et. i. hexploit K; et. i; des.
        esplits; eauto using _hsim', hsim_eqitC_src, eqit_Vis.
    - ides isrc0.
    - ides isrc1. destruct sti_tgt0 as [st_tgt itgt0].
      eapply hsim_tau_src; eauto.
      eapply _hsim_flag_mon with (ps:=ps0) (pt:=pt0); eauto.
      econs. econs. eauto.
  Qed.

  Lemma hsim_eqitC_src_spec : hsim_eqitC_src <10= gupaco9 _hsim (cpn9 _hsim).
  Proof using.
    intros. gclo. econs; eauto using hsim_eqitC_src_compatible.
    eapply hsim_eqitC_src_mon, PR; eauto with paco.
  Qed.

  (**
     hsim_eqitC_tgt
   **)

  Variant hsim_eqitC_tgt
    (r : ∀ Rs Rt (RR : nat → (alist key Any.t) * Rs → (alist key Any.t) * Rt → iProp Σ), bool → bool → nat → (alist key Any.t) * itree hmodE Rs → (alist key Any.t) * itree hmodE Rt → Σ → Prop) :
    ∀ Rs Rt (RR : nat → (alist key Any.t) * Rs → (alist key Any.t) * Rt → iProp Σ), bool → bool → nat → (alist key Any.t) * itree hmodE Rs → (alist key Any.t) * itree hmodE Rt → Σ → Prop :=
  | hsim_eqitC_tgt_intro
      ps pt nths Rs Rt RR fmr sti_src st_tgt itgt0 itgt1
      (EQIT: eqit eq false true itgt0 itgt1)
      (SIM : r Rs Rt RR ps pt nths sti_src (st_tgt, itgt0) fmr)
    :
    hsim_eqitC_tgt r Rs Rt RR ps pt nths sti_src (st_tgt, itgt1) fmr.

  Lemma hsim_eqitC_tgt_mon r1 r2 (LEr : r1 <9= r2) : hsim_eqitC_tgt r1 <9= hsim_eqitC_tgt r2.
  Proof using. ii. destruct PR. econs; eauto using hsupd_mon. Qed.

  Lemma hsim_eqitC_tgt_compatible : compatible9 _hsim hsim_eqitC_tgt.
  Proof using.
    econs; first by eauto using hsim_eqitC_tgt_mon. unfold rel9. ii.
    destruct PR. remember (st_tgt, itgt0) as sti_tgt0.
    move SIM before r. revert_until SIM.
    pattern Rs, Rt, RR, ps, pt, nths, sti_src, sti_tgt0, fmr.
    eapply _hsim_tarski, SIM. i.
    econs. ii. subst. specialize (IN NODFS NODFT NODS NODD H). des.
    esplits; eauto.
    punfold EQIT. subst. rr in EQIT.
    remember (observe itgt0) as otgt0. remember (observe itgt1) as otgt1.
    move EQIT before r. revert_until EQIT.
    assert (EQIT_TAU:= @eqit_Tau). hdes. clear EQIT_TAU0.
    induction EQIT; i; subst; pclearbot.
    - ides itgt0. ides itgt1. eapply _hsim'_mon; eauto; i.
      + destruct x7. econs; eauto using eqit_refl.
      + ss. destruct x4. eauto using eqit_refl.
    - ides itgt0. ides itgt1.
      depdes IN; try itree_clarify x; eauto using _hsim', hsim_eqitC_tgt.
    - ides itgt0. ides itgt1. depdes H1.
      Local Hint Unfold eqit: core.
      inv IN; try itree_clarify H6;
        try (assert (REL' := bind_ret_l_forall (fun v t => _ t (k0 v)) k_tgt REL);
             s in REL');
        try(match goal with [|-context[vis ?e ?k]] =>
            replace (vis e k) with (x <- trigger e;; k x)
                              by (rewrite bind_vis; repeat f_equal;
                                  extensionalities; ired; eauto; fail)
            end);
      eauto using _hsim', hsim_eqitC_tgt, eqit_Vis.
      + eapply hsim_inline_tgt; eauto. eapply K; eauto.
        eapply eqit_bind; eauto using eqit_refl.
      + econs; et; i. hexploit K; et; i; des. esplits; et.
    - ides itgt0.
    - ides itgt1. destruct sti_src0 as [st_src isrc0].
      eapply hsim_tau_tgt; eauto.
      eapply _hsim_flag_mon with (ps:=ps0) (pt:=pt0); eauto.
      econs. econs. eauto.
  Qed.

  Lemma hsim_eqitC_tgt_spec : hsim_eqitC_tgt <10= gupaco9 _hsim (cpn9 _hsim).
  Proof using.
    intros. gclo. econs; eauto using hsim_eqitC_tgt_compatible.
    eapply hsim_eqitC_tgt_mon, PR; eauto with paco.
  Qed.

  (**
     hsim_nodupC
   **)

  Variant hsim_nodupC (r : ∀ Rs Rt (RR : nat → (alist key Any.t) * Rs → (alist key Any.t) * Rt → iProp Σ), bool → bool → nat → (alist key Any.t) * itree hmodE Rs → (alist key Any.t) * itree hmodE Rt → Σ → Prop):
    ∀ Rs Rt (RR : nat → (alist key Any.t) * Rs → (alist key Any.t) * Rt → iProp Σ), bool → bool → nat → (alist key Any.t) * itree hmodE Rs → (alist key Any.t) * itree hmodE Rt → Σ → Prop :=
  | hsim_nodupC_intro
      ps pt nths Rs Rt RR sti_src sti_tgt fmr
      (SIM : ∀ (NODFS : List.NoDup (List.map fst fl_src))
               (NODFT : List.NoDup (List.map fst fl_tgt))
               (NODS : List.NoDup (List.map fst sti_src.1))
               (NODD : List.NoDup (List.map fst sti_tgt.1)),
             r Rs Rt RR ps pt nths sti_src sti_tgt fmr) :
    hsim_nodupC r Rs Rt RR ps pt nths sti_src sti_tgt fmr.

  Lemma hsim_nodupC_mon r1 r2 (LEr : r1 <9= r2) : hsim_nodupC r1 <9= hsim_nodupC r2.
  Proof using. ii. destruct PR. econs; eauto using hsupd_mon. Qed.

  Lemma hsim_nodupC_compatible : compatible9 _hsim hsim_nodupC.
  Proof using.
    econs; eauto using hsim_nodupC_mon.
    i. destruct PR. econs. ii.
    edestruct SIM; eauto. edestruct IN; des; eauto.
    esplits; eauto.
    eapply _hsim'_mon; eauto using hsim_nodupC, _hsim_mon.
  Qed.
  
  Lemma hsim_nodupC_spec : hsim_nodupC <10= gupaco9 _hsim (cpn9 _hsim).
  Proof using.
    intros. gclo. econs; eauto using hsim_nodupC_compatible.
    eapply hsim_nodupC_mon, PR; eauto with paco.
  Qed.

End HSIM.

Hint Resolve _hsim_mon : paco.
Hint Resolve cpn9_wcompat : paco.
