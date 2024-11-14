Require Import Coqlib sflib ITreelib.
Require Import Behavior.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Any.
Require Import Events STB ModSim.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.

From ExtLib Require Import
     Data.Map.FMapAList.

Require Import Red IRed.

Section HPSIM.

  Context `{Σ : GRA.t}.
  Notation iProp := (iProp Σ).

  Variable fl_src : alist gname (Any.t → itree hmodE Any.t).
  Variable fl_tgt : alist gname (Any.t → itree hmodE Any.t).
  Variable Ist : nat → alist key Any.t → alist key Any.t → iProp.
  Variable my_tid : nat.

  (* Note : iProp-style definition of hsupd incurs positivity problem when defining _hpsim. *)
  Definition hsupd (P : Σ → Prop) : Σ → Prop :=
    λ fmr, ✓ fmr → ∃ fmr0, P fmr0 ∧ (Own fmr ⊢ |==> Own fmr0).
    (* λ fmr, Own fmr ⊢ ∃ fmr0, |==> ⌜P fmr0⌝. *)

  (* Definition dummy_term (with_dummy: bool) : itree hmodE unit :=
    if with_dummy then trigger (Guarantee True) else Ret tt. *)
  
  Variant _hpsim'
    (hpsimc : ∀ R (RR : nat → alist key Any.t * R → alist key Any.t * R → iProp),
        bool → bool → nat → alist key Any.t * itree hmodE R → alist key Any.t * itree hmodE R → Σ → Prop)
    {R} {RR : nat → alist key Any.t * R → alist key Any.t * R → iProp}
    (hpsimi : bool → bool → nat → alist key Any.t * itree hmodE R → alist key Any.t * itree hmodE R → Σ → Prop)
    : bool → bool → nat → alist key Any.t * itree hmodE R → alist key Any.t * itree hmodE R → Σ → Prop :=

  | hpsim_ret
      (HPSIM_RET : True)
      ps pt nths st_src st_tgt fmr
      v_src v_tgt
      (RET : Own fmr ⊢ |==> RR nths (st_src,v_src) (st_tgt,v_tgt))
    :
    _hpsim' hpsimc hpsimi ps pt nths (st_src, Ret v_src) (st_tgt, Ret v_tgt) fmr

  | hpsim_call
      (HPSIM_CALL : True)
      ps pt nths st_src st_tgt fmr
      fn varg k_src k_tgt FR
      (INV : Own fmr ⊢ |==> (Ist nths st_src st_tgt ∗ FR))
      (K : ∀ vret nths0 st_src0 st_tgt0 fmr0
            (NODS : List.NoDup (List.map fst st_src0))
            (NODD : List.NoDup (List.map fst st_tgt0))
            (INV : Own fmr0 ⊢ |==> (Ist nths0 st_src0 st_tgt0 ∗ FR)),
        hpsimi true true nths0 (st_src0, k_src vret) (st_tgt0, k_tgt vret) fmr0)
    :
    _hpsim' hpsimc hpsimi ps pt nths (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, trigger (Call fn varg) >>= k_tgt) fmr

  | hpsim_io
      (HPSIM_IO : True)
      ps pt nths st_src st_tgt fmr
      I O fn (varg : I) k_src k_tgt
      (K : ∀ (vret : O), hpsimi true true nths (st_src, k_src vret) (st_tgt, k_tgt vret) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt nths (st_src, trigger (IO fn varg) >>= k_src) (st_tgt, trigger (IO fn varg) >>= k_tgt) fmr

  | hpsim_inline_src
      (HPSIM_INLINE_SRC : True)
      ps pt nths st_src st_tgt fmr
      fn f varg k_src i_tgt
      (FUN : alist_find fn fl_src = Some f)
      (K : hpsimi true pt nths (st_src, f varg >>= (λ ret, tau;; tau;; k_src ret)) (st_tgt, i_tgt) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt nths (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_inline_tgt
      (HPSIM_INLINE_TGT : True)
      ps pt nths st_src st_tgt fmr
      fn f varg i_src k_tgt
      (FUN : alist_find fn fl_tgt = Some f)
      (K : hpsimi ps true nths (st_src, i_src) (st_tgt, f varg >>= (λ ret, tau;; tau;; k_tgt ret)) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt nths (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt) fmr

  | hpsim_tau_src
      (HPSIM_TAU_SRC : True)
      ps pt nths st_src st_tgt fmr
      i_src i_tgt
      (K : hpsimi true pt nths (st_src, i_src) (st_tgt, i_tgt) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt nths (st_src, tau;; i_src) (st_tgt, i_tgt) fmr

  | hpsim_tau_tgt
      (HPSIM_TAU_TGT : True)
      ps pt nths st_src st_tgt fmr
      i_src i_tgt
      (K : hpsimi ps true nths (st_src, i_src) (st_tgt, i_tgt) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt nths (st_src, i_src) (st_tgt, tau;; i_tgt) fmr

  | hpsim_take_src
      (HPSIM_TAKE_SRC : True)
      ps pt nths st_src st_tgt fmr
      X k_src i_tgt
      (K : ∀ (x : X), hpsimi true pt nths (st_src, k_src x) (st_tgt, i_tgt) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt nths (st_src, trigger (Take X) >>= k_src) (st_tgt, i_tgt) fmr
            
  | hpsim_choose_tgt
      (HPSIM_CHOOSE_TGT : True)
      ps pt nths st_src st_tgt fmr
      X i_src k_tgt
      (K : ∀ (x : X), hpsimi ps true nths (st_src, i_src) (st_tgt, k_tgt x) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt nths (st_src, i_src) (st_tgt, trigger (Choose X) >>= k_tgt) fmr

  | hpsim_choose_src
      (HPSIM_CHOOSE_SRC : True)
      ps pt nths st_src st_tgt fmr
      X x k_src i_tgt
      (K : hpsimi true pt nths (st_src, k_src x) (st_tgt, i_tgt) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt nths (st_src, trigger (Choose X) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_take_tgt
      (HPSIM_TAKE_TGT : True)
      ps pt nths st_src st_tgt fmr
      X x i_src k_tgt
      (K : hpsimi ps true nths (st_src, i_src) (st_tgt, k_tgt x) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt nths (st_src, i_src) (st_tgt, trigger (Take X) >>= k_tgt) fmr

  | hpsim_sput_src
      (HPSIM_SPUT_SRC : True)
      ps pt nths st_src st_src0 st_tgt fmr
      k_src i_tgt
      k v
      (run : st_src0 = alist_upd k v st_src)
      (K : hpsimi true pt nths (st_src0, k_src tt) (st_tgt, i_tgt) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt nths (st_src, trigger (SPut k v) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_sput_tgt
      (HPSIM_SPUT_SRC : True)
      ps pt nths st_src st_tgt st_tgt0 fmr
      i_src k_tgt 
      k v
      (run : st_tgt0 = alist_upd k v st_tgt)
      (K : hpsimi ps true nths (st_src, i_src) (st_tgt0, k_tgt tt) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt nths (st_src, i_src) (st_tgt, trigger (SPut k v) >>= k_tgt) fmr

  | hpsim_sget_src
      (HPSIM_SPUT_SRC : True)
      ps pt nths st_src st_tgt fmr
      k_src i_tgt
      k v
      (run : v = or_else (alist_find k st_src) tt↑)
      (K : hpsimi true pt nths (st_src, k_src v) (st_tgt, i_tgt) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt nths (st_src, trigger (SGet k) >>= k_src) (st_tgt, i_tgt) fmr
 
  | hpsim_sget_tgt
      (HPSIM_SPUT_SRC : True)
      ps pt nths st_src st_tgt fmr
      i_src k_tgt 
      k v
      (run : v = or_else (alist_find k st_tgt) tt↑)
      (K : hpsimi ps true nths (st_src, i_src) (st_tgt, k_tgt v) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt nths (st_src, i_src) (st_tgt, trigger (SGet k) >>= k_tgt) fmr
 
  | hpsim_assume_src
      (HPSIM_ASSUME_SRC : True)
      ps pt nths st_src st_tgt fmr
      iP k_src i_tgt FMR
      (CUR : Own fmr ⊢ |==> FMR)
      (K : ∀ fmr0 (NEW : Own fmr0 ⊢ |==> (iP ∗ FMR)),
          hpsimi true pt nths (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
    :
    _hpsim' hpsimc hpsimi ps pt nths (st_src, trigger (Assume iP) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_guarantee_tgt
      (HPSIM_GUARANTEE_TGT : True)
      ps pt nths st_src st_tgt fmr
      iP i_src k_tgt FMR
      (CUR : Own fmr ⊢ |==> FMR)
      (K : ∀ fmr0 (NEW : Own fmr0 ⊢ |==> (iP ∗ FMR)),
          hpsimi ps true nths (st_src, i_src) (st_tgt, k_tgt tt) fmr0)
    :
    _hpsim' hpsimc hpsimi ps pt nths (st_src, i_src) (st_tgt, trigger (Guarantee iP) >>= k_tgt) fmr
            
  | hpsim_guarantee_src
      (HPSIM_GUARANTEE_SRC : True)
      ps pt nths st_src st_tgt fmr
      iP k_src i_tgt FMR
      (CUR : Own fmr ⊢ |==> (iP ∗ FMR))
      (K : ∀ fmr0 (NEW : Own fmr0 ⊢ |==> FMR),
          hpsimi true pt nths (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
    :
    _hpsim' hpsimc hpsimi ps pt nths (st_src, trigger (Guarantee iP) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_assume_tgt
      (HPSIM_ASSUME_TGT : True)
      ps pt nths st_src st_tgt fmr
      iP i_src k_tgt FMR
      (CUR : Own fmr ⊢ |==> (iP ∗ FMR))
      (K : ∀ fmr0 (NEW : Own fmr0 ⊢ |==> FMR),
          hpsimi ps true nths (st_src, i_src) (st_tgt, k_tgt tt) fmr0)
    :
    _hpsim' hpsimc hpsimi ps pt nths (st_src, i_src) (st_tgt, trigger (Assume iP) >>= k_tgt) fmr

  | hpsim_spawn
      (HPSIM_SPAWN : True)
      ps pt nths st_src st_tgt fmr
      fn arg k_src k_tgt
      (K : hpsimi true true (S nths) (st_src, k_src nths) (st_tgt, k_tgt nths) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt nths (st_src, trigger (Spawn fn arg) >>= k_src) (st_tgt, trigger (Spawn fn arg) >>= k_tgt) fmr

  | hpsim_yield
      (HPSIM_YIELD : True)
      ps pt nths st_src st_tgt fmr
      tid k_src k_tgt FR
      (INV : Own fmr ⊢ |==> (Ist nths st_src st_tgt ∗ FR))
      (K : ∀ nths0 st_src0 st_tgt0 fmr0
          (NODS : List.NoDup (List.map fst st_src0))
          (NODD : List.NoDup (List.map fst st_tgt0))
          (INV : Own fmr0 ⊢ |==> (Ist nths0 st_src0 st_tgt0 ∗ FR)),
        hpsimi true true nths0 (st_src0, k_src tt) (st_tgt0, k_tgt tt) fmr0)				
    :
    _hpsim' hpsimc hpsimi ps pt nths (st_src, trigger (Yield tid) >>= k_src) (st_tgt, trigger (Yield tid) >>= k_tgt) fmr
        
  | hpsim_tid_src
      (HPSIM_TID_SRC : True)
      ps pt nths st_src st_tgt fmr
      k_src i_tgt
      (K : hpsimi true pt nths (st_src, k_src my_tid) (st_tgt, i_tgt) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt nths (st_src, trigger Tid >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_tid_tgt
      (HPSIM_TID_TGT : True)
      ps pt nths st_src st_tgt fmr
      i_src k_tgt
      (K : hpsimi ps true nths (st_src, i_src) (st_tgt, k_tgt my_tid) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt nths (st_src, i_src) (st_tgt, trigger Tid >>= k_tgt) fmr

  | hpsim_progress
      (HPSIM_PROGRESS : True)
      nths sti_src sti_tgt fmr
      (SIM : hpsimc R RR false false nths sti_src sti_tgt fmr)
    :
    _hpsim' hpsimc hpsimi true true nths sti_src sti_tgt fmr.
  Global Arguments _hpsim' hpsimc {R} RR hpsimi.

  Inductive _hpsim hpsim R RR ps pt nths sti_src sti_tgt fmr : Prop :=
  | hpsim_intro
      (IN : hsupd (@_hpsim' hpsim R RR (@_hpsim hpsim R RR) ps pt nths sti_src sti_tgt) fmr).

  Definition hpsim {R} RR := paco8 _hpsim bot8 R RR.

  Lemma _hpsim_tarski hpsim R RR rel
      (FIX : ∀ ps pt nths sti_src sti_tgt fmr
          (IN : hsupd (@_hpsim' hpsim R RR rel ps pt nths sti_src sti_tgt) fmr),
        rel ps pt nths sti_src sti_tgt fmr) :
    _hpsim hpsim R RR <6= rel.
  Proof.
    fix self 7. i.
    destruct PR. apply FIX. intros wf. specialize (IN wf); des.
    exists fmr0; split; eauto.
    destruct IN; try by esplits; eauto using @_hpsim' with paco.
  Qed.

  Lemma hsupd_mon P Q r (IN : hsupd P r) (LE : P <1= Q) : hsupd Q r.
  Proof. by intros wf; specialize (IN wf); inv IN; exists x; split; des; eauto. Qed.

  Lemma _hpsim'_mon r r' R RR s s'
      ps pt nths sti_src sti_tgt fmr
      (REL : @_hpsim' r R RR s ps pt nths sti_src sti_tgt fmr)
      (LEr : r <8= r')
      (LEs : s <6= s') :
    @_hpsim' r' R RR s' ps pt nths sti_src sti_tgt fmr.
  Proof. ii. destruct REL; des; esplits; eauto; econs; esplits; eauto. Qed.
  
  Lemma _hpsim_mon : monotone8 _hpsim.
  Proof.
    ii. eapply _hpsim_tarski, IN.
    i. econs. eauto using hsupd_mon, _hpsim'_mon.
  Qed.

  Lemma _hpsim_mon_auto r r' R RR
      ps pt nths sti_src sti_tgt fmr
      (REL : _hpsim r R RR ps pt nths sti_src sti_tgt fmr)
      (LEr : r <8= r') :
    _hpsim r' R RR ps pt nths sti_src sti_tgt fmr.
  Proof. eapply _hpsim_mon; eauto. Qed.

  Hint Constructors _hpsim' _hpsim : core.
  Hint Unfold hpsim : core.
  Hint Resolve _hpsim_mon : paco.
  Hint Resolve hsupd_mon _hpsim'_mon _hpsim_mon_auto : paco.
  Hint Resolve cpn8_wcompat : paco.

  Definition hpsim_tail : nat → (alist key Any.t) * Any.t → (alist key Any.t) * Any.t → iProp :=
    fun nths '(st_src, v_src) '(st_tgt, v_tgt) => (⌜v_src = v_tgt⌝ ∗ Ist nths st_src st_tgt)%I.

  Definition hpsim_body ps pt nths sti_src sti_tgt fmr :=
    ∀ (NODFS : List.NoDup (List.map fst fl_src))
      (NODFT : List.NoDup (List.map fst fl_tgt))
      (NODS : List.NoDup (List.map fst sti_src.1))
      (NODD : List.NoDup (List.map fst sti_tgt.1)),
    @hpsim _ hpsim_tail ps pt nths sti_src sti_tgt fmr.

  Definition hpsim_fun (i_src : itree hmodE Any.t) (i_tgt : itree hmodE Any.t) : Prop :=
    ∀ nths st_src st_tgt fmr (INV : Own fmr ⊢ |==> Ist nths st_src st_tgt),
      hpsim_body false false nths (st_src, i_src) (st_tgt, i_tgt) fmr.

  Lemma case_itrH R (itrH : itree hmodE R) :
    (exists v, itrH = Ret v) \/
    (exists itrH', itrH = tau;; itrH') \/
    (exists P itrH', itrH = (trigger (Assume P);;; itrH')) \/
    (exists P itrH', itrH = (trigger (Guarantee P);;; itrH')) \/
    (exists R (s : schE R) ktrH', itrH = (trigger s >>= ktrH')) \/
    (exists R (c : callE R) ktrH', itrH = (trigger c >>= ktrH')) \/
    (exists R (s : pgE R) ktrH', itrH = (trigger s >>= ktrH')) \/
    (exists R (e : coreE R) ktrH', itrH = (trigger e >>= ktrH')).
  Proof.
    ides itrH; eauto.
    right; right.
    destruct e; [destruct a|destruct p; [|destruct s; [|destruct s]]].
    - left. exists P, (k()). unfold trigger. rewrite bind_vis.
      repeat f_equal. extensionality x. destruct x. rewrite bind_ret_l. eauto.
    - right; left. exists P, (k()). unfold trigger. rewrite bind_vis.
      repeat f_equal. extensionality x. destruct x. rewrite bind_ret_l. eauto.
    - do 2 right; left. exists X, s, k. unfold trigger. rewrite bind_vis.
      repeat f_equal. extensionality x. rewrite bind_ret_l. eauto.
    - do 3 right; left. exists X, c, k. unfold trigger. rewrite bind_vis.
      repeat f_equal. extensionality x. rewrite bind_ret_l. eauto.
    - do 4 right; left. exists X, p, k. unfold trigger. rewrite bind_vis.
      repeat f_equal. extensionality x. rewrite bind_ret_l. eauto.
    - do 5 right. exists X, c, k. unfold trigger. rewrite bind_vis.
      repeat f_equal. extensionality x. rewrite bind_ret_l. eauto.
  Qed.

  Lemma hsupd_incl P : P <1= hsupd P.
  Proof.
    ii; esplits; eauto.
  Qed.
  
  Lemma hsupd_merge P r (REL : hsupd (hsupd P) r) : hsupd P r.
  Proof.
    intros wf; specialize (REL wf); destruct REL as [r1 [??]].
    hexploit Own_wand_valid; eauto.
    intros wf1; hexploit (H wf1); intros [fmr0 [??]]; exists fmr0; esplits; eauto.
    iIntros "R"; iPoseProof (H0 with "R") as "> R1"; iApply H2; done.
  Qed.

  Lemma hsupd_update P r r' (IN : hsupd P r) (UPD : r' ~~> r) :
    hsupd P r'.
  Proof.
    dup UPD; rewrite cmra_discrete_update in UPD; specialize (UPD (Some ε)); ss; rewrite ?right_id in UPD.
    intros wfr'; hexploit (IN (UPD wfr')); i; des; eexists; split; eauto.
    iIntros "H"; iPoseProof (Own_Upd with "H") as "> H"; first eauto.
    iApply H0; done.
  Qed.

  Lemma hsupd_extends P r r' (IN : hsupd P r) (UPD : r ≼ r') :
    hsupd P r'.
  Proof. eapply hsupd_update; eauto; eapply cmra_update_included; eauto. Qed.

  Lemma hsupd_wf P r (IN : ✓ r -> hsupd P r) :
    hsupd P r.
  Proof. intros wf; hexploit (IN wf wf); i; des; clarify; esplits; eauto. Qed.

  Lemma _hpsim_flag_mon r R RR (ps pt ps' pt' : bool) nths st_src st_tgt fmr
      (SIM : _hpsim r R RR ps pt nths st_src st_tgt fmr)
      (LES : ps -> ps')
      (LET : pt -> pt') :
    _hpsim r R RR ps' pt' nths st_src st_tgt fmr.
  Proof.
    move SIM before r. revert_until SIM.
    pattern ps, pt, nths, st_src, st_tgt, fmr.
    eapply _hpsim_tarski, SIM. i. econs.
    ii. specialize (IN H). des. destruct IN;
      try by esplits; eauto; try by econs; esplits; eauto.
    hexploit LES; eauto; i. hexploit LET; eauto; i.
    destruct ps', pt'; try discriminate. 
    econs; esplits; eauto.
  Qed.

  Lemma hpsim_flag_mon R RR (ps pt ps' pt' : bool) nths st_src st_tgt fmr
      (SIM : @hpsim R RR ps pt nths st_src st_tgt fmr)
      (LES : ps -> ps')
      (LET : pt -> pt') :
    hpsim RR ps' pt' nths st_src st_tgt fmr.
  Proof.
    move SIM before RR. revert_until SIM. pcofix CIH. i.
    pstep. eapply _hpsim_flag_mon; eauto.
    eapply paco8_mon_bot in SIM; eauto. punfold SIM.
  Qed.

  Lemma hpsim_progress_flag R RR r g nths st_src st_tgt fmr
      (SIM : gpaco8 _hpsim (cpn8 _hpsim) g g R RR false false nths st_src st_tgt fmr) :
    gpaco8 _hpsim (cpn8 _hpsim) r g R RR true true nths st_src st_tgt fmr.
  Proof.
    gstep. econs. r; esplits; eauto.
  Qed.

  Definition hpsimC hpsim R RR ps pt nths sti_src sti_tgt fmr :=
    hsupd (@_hpsim' hpsim R RR (hpsim R RR) ps pt nths sti_src sti_tgt) fmr.
  
  Lemma hpsimC_mon : monotone8 hpsimC.
  Proof.
    ii. specialize (IN H). des.
    destruct IN; econs; esplits; eauto; try by esplits; eauto.
  Qed.

  Lemma hpsimC_spec : hpsimC <9= gupaco8 _hpsim (cpn8 _hpsim).
  Proof.
    eapply wrespect8_uclo; eauto with paco.
    econs; eauto using hpsimC_mon; i.
    econs. ii. destruct PR; eauto. des. esplits; eauto.
    eapply _hpsim'_mon; eauto using rclo8, _hpsim_mon_auto; i.
  Qed.

  Variant hpsim_flagC 
      (r : ∀ (R : Type) (RR : nat -> (alist key Any.t) * R -> (alist key Any.t) * R -> iProp),
        bool -> bool -> nat -> (alist key Any.t) * itree hmodE R -> (alist key Any.t) * itree hmodE R -> Σ -> Prop)
      R RR ps1 pt1 nths st_src st_tgt fmr : Prop :=
  | hpsim_flagC_intro ps0 pt0
    (SIM : r R RR ps0 pt0 nths st_src st_tgt fmr)
    (SRC : ps0 = true -> ps1 = true)
    (TGT : pt0 = true -> pt1 = true).

  Lemma hpsim_flagC_mon r1 r2 (LE : r1 <8= r2) :
    hpsim_flagC r1 <8= hpsim_flagC r2.
  Proof. ii. destruct PR; econs; et. Qed.

  Hint Resolve hpsim_flagC_mon : paco.
  
  Lemma hpsim_flagC_spec : hpsim_flagC <9= gupaco8 _hpsim (cpn8 _hpsim).
  Proof.
    eapply wrespect8_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    eauto using _hpsim_flag_mon, _hpsim_mon_auto, rclo8.
  Qed.

  Lemma hpsim_flag_down R RR r g ps pt nths st_src st_tgt fmr
      (SIM : gpaco8 _hpsim (cpn8 _hpsim) r g R RR false false nths st_src st_tgt fmr) :
    gpaco8 _hpsim (cpn8 _hpsim) r g R RR ps pt nths st_src st_tgt fmr.
  Proof. 
    guclo hpsim_flagC_spec. econs; et. 
  Qed.

  Variant hpsim_bindC
      (r : ∀ R (RR : nat -> (alist key Any.t) * R -> (alist key Any.t) * R -> iProp), bool -> bool -> nat -> (alist key Any.t) * itree hmodE R -> (alist key Any.t) * itree hmodE R -> Σ -> Prop) :
    ∀ R (RR : nat -> (alist key Any.t) * R -> (alist key Any.t) * R -> iProp),
      bool -> bool -> nat -> (alist key Any.t) * itree hmodE R -> (alist key Any.t) * itree hmodE R -> Σ -> Prop :=
  | hpsim_bindC_intro
      ps pt nths Q QQ st_src st_tgt i_src i_tgt fmr
      (SIM : r Q QQ ps pt nths (st_src, i_src) (st_tgt, i_tgt) fmr)
      R RR k_src k_tgt
      (SIMK : ∀ nths0 st_src0 st_tgt0 vret_src vret_tgt fmr0
          (RET : Own fmr0 ⊢ |==> QQ nths0 (st_src0, vret_src) (st_tgt0, vret_tgt)),
        r R RR false false nths0 (st_src0, k_src vret_src) (st_tgt0, k_tgt vret_tgt) fmr0)
    :
    hpsim_bindC r R RR ps pt nths (st_src, i_src >>= k_src) (st_tgt, i_tgt >>= k_tgt) fmr.

  Lemma hpsim_bindC_mon r1 r2 (LEr : r1 <8= r2) : hpsim_bindC r1 <8= hpsim_bindC r2.
  Proof. ii. destruct PR; econs; et. Qed.

  Lemma hpsim_bindC_wrespectful : wrespectful8 _hpsim hpsim_bindC.
  Proof.
    (* econs; eauto using hpsim_bindC_mon; i. *)
    (* destruct PR. apply GF in SIM. *)
    (* remember (st_src, i_src) as sti_src. remember (st_tgt, i_tgt) as sti_tgt. *)
    (* move SIM before GF. revert_until SIM. *)
    (* pattern ps, pt, nths, sti_src, sti_tgt, fmr. *)
    (* eapply _hpsim_tarski, SIM. econs. apply hsupd_merge. *)
    (* econs; esplits; eauto. *)
    (* specialize (IN H); des. *)
    (* depdes IN; grind; *)
      (* try (by rr; i; esplits; eauto with paco); *)
      (* try (by do 2 (econs; esplits; eauto with paco); *)
              (* repeat rewrite <-bind_bind; *)
              (* eauto 10 using rclo8, hpsim_bindC). *)

    (* exploit SIMK; eauto. *)
    (* i. apply GF in x0. eapply (_hpsim_flag_mon _ _ _ _ _ _ ps0 pt0) in x0; try by i; clarify. *)

    (* destruct x0. eapply hsupd_update in IN; eauto. *)
    (* eapply _hpsim_mon_auto; eauto using rclo8. *)
    (* eapply Own_bupd_update; eauto. *)
  (* Qed. *)
  Admitted.

  Lemma hpsim_bindC_spec : hpsim_bindC <9= gupaco8 _hpsim (cpn8 _hpsim).
  Proof.
    intros. eapply wrespect8_uclo; eauto with paco.
    apply hpsim_bindC_wrespectful.
  Qed.


  Variant hpsim_extendC
    (r : ∀ R (RR : nat -> (alist key Any.t) * R -> (alist key Any.t) * R -> iProp), bool -> bool -> nat -> (alist key Any.t) * itree hmodE R -> (alist key Any.t) * itree hmodE R -> Σ -> Prop) :
    ∀ R (RR : nat -> (alist key Any.t) * R -> (alist key Any.t) * R -> iProp), bool -> bool -> nat -> (alist key Any.t) * itree hmodE R -> (alist key Any.t) * itree hmodE R -> Σ -> Prop :=
  | hpsim_extendC_intro
      ps pt nths R RR sti_src sti_tgt fmr fmr'
      (SIM : r R RR ps pt nths sti_src sti_tgt fmr)
      (EXT : fmr ≼ fmr') :
    hpsim_extendC r R RR ps pt nths sti_src sti_tgt fmr'.

  Lemma hpsim_extendC_mon r1 r2 (LEr : r1 <8= r2) : hpsim_extendC r1 <8= hpsim_extendC r2.
  Proof. ii. destruct PR; econs; et. Qed.

  Lemma hpsim_extendC_compatible :
    compatible8 _hpsim hpsim_extendC.
  Proof.
    econs; eauto using hpsim_extendC_mon.
    intros. destruct PR. destruct SIM. econs.
    eapply hsupd_extends; eauto.
    eapply _hpsim_mon_auto; eauto.
    i. econs; eauto; refl.
  Qed.
  
  Lemma hpsim_extendC_spec : hpsim_extendC <9= gupaco8 _hpsim (cpn8 _hpsim).
  Proof.
    intros. gclo. econs; eauto using hpsim_extendC_compatible.
    eapply hpsim_extendC_mon, PR; eauto with paco.
  Qed.


  Variant hpsim_wfC (r : ∀ R (RR : nat -> (alist key Any.t) * R -> (alist key Any.t) * R -> iProp), bool -> bool -> nat -> (alist key Any.t) * itree hmodE R -> (alist key Any.t) * itree hmodE R -> Σ -> Prop):
    ∀ R (RR : nat -> (alist key Any.t) * R -> (alist key Any.t) * R -> iProp), bool -> bool -> nat -> (alist key Any.t) * itree hmodE R -> (alist key Any.t) * itree hmodE R -> Σ -> Prop :=
  | hpsim_wfC_intro
      ps pt nths R RR sti_src sti_tgt fmr
      (SIM : ✓ fmr -> r R RR ps pt nths sti_src sti_tgt fmr) :
    hpsim_wfC r R RR ps pt nths sti_src sti_tgt fmr.

  Lemma hpsim_wfC_mon r1 r2 (LEr : r1 <8= r2) : hpsim_wfC r1 <8= hpsim_wfC r2 .
  Proof. ii. destruct PR. econs; eauto using hsupd_mon. Qed.

  Lemma hpsim_wfC_compatible : compatible8 _hpsim hpsim_wfC.
  Proof.
    econs; eauto using hpsim_wfC_mon.
    i. destruct PR. econs. eapply hsupd_wf. i.
    eapply _hpsim_mon_auto; eauto 10 using hpsim_wfC, hsupd_incl with paco.
  Qed.
  
  Lemma hpsim_wfC_spec : hpsim_wfC <9= gupaco8 _hpsim (cpn8 _hpsim).
  Proof.
    intros. gclo. econs; eauto using hpsim_wfC_compatible.
    eapply hpsim_wfC_mon, PR; eauto with paco.
  Qed.
  

  Variant hpsim_updateC (r : ∀ R (RR : nat -> (alist key Any.t) * R -> (alist key Any.t) * R -> iProp), bool -> bool -> nat -> (alist key Any.t) * itree hmodE R -> (alist key Any.t) * itree hmodE R -> Σ -> Prop):
    ∀ R (RR : nat -> (alist key Any.t) * R -> (alist key Any.t) * R -> iProp), bool -> bool -> nat -> (alist key Any.t) * itree hmodE R -> (alist key Any.t) * itree hmodE R -> Σ -> Prop :=
  | hpsim_updateC_intro
      ps pt nths R RR sti_src sti_tgt fmr
      (SIM : hsupd (r R RR ps pt nths sti_src sti_tgt) fmr) :
    hpsim_updateC r R RR ps pt nths sti_src sti_tgt fmr.

  Lemma hpsim_updateC_mon r1 r2 (LEr : r1 <8= r2) : hpsim_updateC r1 <8= hpsim_updateC r2.
  Proof. ii. destruct PR. econs; eauto using hsupd_mon. Qed.

  Lemma hpsim_updateC_compatible : compatible8 _hpsim hpsim_updateC.
  Proof.
    econs; eauto using hpsim_updateC_mon.
    i. destruct PR. econs. eapply hsupd_merge.
    eapply hsupd_mon; eauto.
    i. destruct PR.
    eauto 10 using hpsim_updateC, hsupd_incl with paco.
  Qed.
  
  Lemma hpsim_updateC_spec : hpsim_updateC <9= gupaco8 _hpsim (cpn8 _hpsim).
  Proof.
    intros. gclo. econs; eauto using hpsim_updateC_compatible.
    eapply hpsim_updateC_mon, PR; eauto with paco.
  Qed.
  

  Variant hpsim_frameC
      (r : ∀ R (RR : nat -> (alist key Any.t) * R -> (alist key Any.t) * R -> iProp), bool -> bool -> nat -> (alist key Any.t) * itree hmodE R -> (alist key Any.t) * itree hmodE R -> Σ -> Prop) :
    ∀ R (RR : nat -> (alist key Any.t) * R -> (alist key Any.t) * R -> iProp), bool -> bool -> nat -> (alist key Any.t) * itree hmodE R -> (alist key Any.t) * itree hmodE R -> Σ -> Prop :=
  | hpsim_frameC_intro
      ps pt nths R RR sti_src sti_tgt fmr fmrc (CTX : iProp)
      (SIM : r R (fun n s t => CTX -∗ RR n s t)%I ps pt nths sti_src sti_tgt fmr)
      (UPD : Own fmrc ⊢ |==> (Own fmr ∗ CTX)) :
    hpsim_frameC r R RR ps pt nths sti_src sti_tgt fmrc.

  Lemma hpsim_frameC_mon r1 r2 (LEr : r1 <8= r2) : hpsim_frameC r1 <8= hpsim_frameC r2.
  Proof. ii. destruct PR. econs; eauto using hsupd_mon. Qed.
  
  Lemma hpsim_frameC_compatible : compatible8 _hpsim hpsim_frameC.
  Proof.
    econs; first by eauto using hpsim_frameC_mon. ii.
    destruct PR. move SIM before r. revert_until SIM.
    pattern ps, pt, nths, sti_src, sti_tgt, fmr.
    eapply _hpsim_tarski, SIM. i. econs.
    econs; esplits; eauto.
    exploit IN.
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
      + i. econs. apply hsupd_merge. ii. esplits; eauto.
        rewrite assoc in INV0. hexploit (Own_bupd_split fmr2); eauto; i; des.
        eapply (K _ _ _ _ a1); eauto.
        { iIntros "?"; iApply H3; iFrame; done. }
        { iIntros "H"; iPoseProof (H2 with "H") as "> [H1 H2]"; iModIntro; iFrame. iApply H4; done. }
    - econs; eauto. i.
      econs. apply hsupd_merge. ii. esplits; eauto.
      rewrite assoc in NEW; hexploit (Own_bupd_split fmr2); eauto; i; des.
      eapply (K a1); eauto.
      { iIntros "H1"; iPoseProof (H3 with "H1") as "[P H1]". iMod (CUR with "H1") as "?"; iModIntro; iFrame. }
      { iIntros "H2"; iPoseProof (H2 with "H2") as "> [H1 H2]"; iPoseProof (H4 with "H2") as "?"; iModIntro; iFrame. }
    - econs; eauto. i.
      econs. apply hsupd_merge. ii. esplits; eauto.
      rewrite assoc in NEW; hexploit (Own_bupd_split fmr2); eauto; i; des.
      eapply (K a1); eauto.
      { iIntros "H1"; iPoseProof (H3 with "H1") as "[P H1]". iMod (CUR with "H1") as "?"; iModIntro; iFrame. }
      { iIntros "H2"; iPoseProof (H2 with "H2") as "> [H1 H2]"; iPoseProof (H4 with "H2") as "?"; iModIntro; iFrame. }
    - econs; eauto.
      { instantiate (1:= (FMR ∗ CTX)%I).
        iIntros "H". iPoseProof (H0 with "H") as "H". iMod "H" as "[F C]".
        iFrame. iStopProof; eauto. }
      i. econs. apply hsupd_merge. ii. esplits; eauto.
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
      i. econs. apply hsupd_merge. ii. esplits; eauto.
      hexploit (Own_bupd_split fmr2); eauto; i; des.
      eapply (K a1); eauto.
      { iIntros "H". iModIntro; iApply H3; done. }
      { iIntros "H". iPoseProof (H2 with "H") as "H". iMod "H" as "[HP HQ]".
        iFrame. iModIntro; iApply H4; done.
      }
    - econs; eauto.
      + instantiate (1:= (FR ∗ CTX)%I).
        iIntros "C"; iPoseProof (H0 with "C") as "> [H1 CTX]"; iPoseProof (INV with "H1") as ">?".
        iModIntro; iFrame; done.
      + i. econs. apply hsupd_merge. ii. esplits; eauto.
        rewrite assoc in INV0. exploit (Own_bupd_split fmr2); eauto; i; des.
        eapply (K _ _ _ a1); eauto.
        { iIntros "H2"; iModIntro; iApply x2; done. }
        { iIntros "H2"; iPoseProof (x0 with "H2") as "> [H1 H2]"; iPoseProof (x3 with "H2") as "?".
          iModIntro; iFrame.
        }
    - eauto using hpsim_frameC with paco.
  Qed.
  
  Lemma hpsim_frameC_spec : hpsim_frameC <9= gupaco8 _hpsim (cpn8 _hpsim).
  Proof.
    intros. gclo. econs; eauto using hpsim_frameC_compatible.
    eapply hpsim_frameC_mon, PR; eauto with paco.
  Qed.

  (* TODO : currently not used. Maybe these need to be in the adequacy *)
  (* Definition hpsim_fsem : relation (Any.t -> itree hmodE Any.t) :=
    (eq ==> hpsim_fun)%signature.

  Definition hpsim_fnsem : relation (string * (Any.t -> itree hmodE Any.t)) :=
    RelProd eq hpsim_fsem. *)

End HPSIM.

Hint Resolve _hpsim_mon : paco.
Hint Resolve cpn8_wcompat : paco.