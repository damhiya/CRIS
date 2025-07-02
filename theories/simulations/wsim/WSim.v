Require Import Common.
Require Import ISim SMod SModTr HMod HModSim.
Require Import TacticsCommon.
From iris.proofmode Require Import proofmode.
From stdpp Require Import coPset.

Section ginv.
  Context `{!crisG  Γ Σ α β τ _S _I}.

  Definition wsim_ginv (Ep : option (coPset * coPset)) : iProp Σ :=
    match Ep with
    | Some (Ew, E) => own_admin ∗ ownE E ∗ (∃ n, wsats n Ew)
    | None => emp
    end.

  Lemma wsim_ginv_merge Ew1 Ew2 E1 E2 :
    wsim_ginv (Some (Ew1, E1)) ∗ wsim_ginv (Some (Ew2, E2)) ==∗
    wsim_ginv (Some (Ew1 ∪ Ew2, E1 ∪ E2)) ∗ ⌜Ew1 ## Ew2 ∧ E1 ## E2⌝.
  Proof.
    iIntros "[[O [E1 [%n1 W1]]] [_ [E2 [%n2 W2]]]]".
    iPoseProof (ownE_exploit with "[E1 E2]") as "%"; first iFrame.
    iPoseProof (wsats_exploit with "[W1 W2]") as "%"; first iFrame.
    iMod (wsats_mon _ (max n1 n2) with "W1") as "W1"; first lia.
    iMod (wsats_mon _ (max n1 n2) with "W2") as "W2"; first lia.
    iPoseProof (ownE_op with "[E1 E2]") as "E"; cycle 1; first iFrame; ss.
    iPoseProof (wsats_merge with "[W1 W2]") as "W"; iFrame.
    do 2 (rewrite {1}comm_L; iFrame); ss.
  Qed.

  Lemma wsim_ginv_split Ew1 Ew2 E1 E2 :
    Ew1 ## Ew2 → E1 ## E2 →
    wsim_ginv (Some (Ew1 ∪ Ew2, E1 ∪ E2)) -∗
    wsim_ginv (Some (Ew1, E1)) ∗ wsim_ginv (Some (Ew2, E2)).
  Proof.
    iIntros (??) "[O [E [% W]]]"; iPoseProof (own_admin_split with "O") as "[$ $]".
    rewrite ownE_op //; iDestruct "E" as "[$ $]".
    rewrite wsats_split //; iDestruct "W" as "[$ $]".
  Qed.

  Definition fspec_wsim (E : coPset) (fsp : fspec) : fspec :=
    mk_fspec (meta := fsp.(meta))
      (λ x varg arg, wsim_ginv (Some (E, E)) ∗ fsp.(precond) x varg arg)%I
      (λ x vret ret, wsim_ginv (Some (E, E)) ∗ fsp.(postcond) x vret ret)%I.
End ginv.

(* Typeclass definition to streamline assume/guarantee processing *)
Class WP `{!crisG Γ Σ α β τ _S _I} (P : iProp Σ) := mk_WP {
  WP_space : coPset;
  WP_remainder : iProp Σ;
  WP_iff : P ∗-∗ wsim_ginv (Some (WP_space, WP_space)) ∗ WP_remainder
}.
Arguments mk_WP {_ _ _ _ _ _ _ _ _} _ _ _.
Arguments WP_remainder {_ _ _ _ _ _ _ _} [_] _.
Arguments WP_space {_ _ _ _ _ _ _ _} [_] _.
Arguments WP_iff {_ _ _ _ _ _ _ _} [_] _.

Program Global Instance WP_refl E `{!crisG Γ Σ α β τ _S _I}
  : WP (wsim_ginv (Some (E, E))) := mk_WP E True _.
Next Obligation. ii; iSplit; first iIntros "$"; iIntros "[$ _]". Qed.

Program Global Instance fspec_wsim_precond `{!crisG Γ Σ α β τ _S _I} (fsp : fspec) E m arg varg :
  WP (precond (fspec_wsim E fsp) m arg varg) :=
  {| WP_space := E; WP_remainder := (precond fsp m arg varg) |}.
Next Obligation. intros; iSplit; iIntros "[$ $]". Qed.

Program Global Instance fspec_wsim_postcond `{!crisG Γ Σ α β τ _S _I} (fsp : fspec) E m arg varg :
  WP (postcond (fspec_wsim E fsp) m arg varg) :=
  {| WP_space := E; WP_remainder := (postcond fsp m arg varg) |}.
Next Obligation. intros; iSplit; iIntros "[$ $]". Qed.

Section wsim.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Local Definition state : Type := alist key Any.t.
  Local Definition post (R_s R_t : Type) : Type := nat → state * R_s → state * R_t → iProp Σ.
  Local Definition rel : Type := ∀ R_s R_t : Type,
    post R_s R_t → bool → bool → nat → state * itree hmodE R_s → state * itree hmodE R_t → iProp Σ.

  Local Definition wsim_def fl_s fl_t Ist stid Ep r g R_s R_t RR ps pt nths st_s st_t : iProp Σ :=
    wsim_ginv Ep -∗
    @isim Σ open fl_s fl_t Ist stid r g R_s R_t RR ps pt nths st_s st_t.
  Local Definition wsim_aux : seal (@wsim_def). Proof using. by eexists. Qed.
  Definition wsim := wsim_aux.(unseal).
  Local Definition wsim_eq : @wsim = @wsim_def := wsim_aux.(seal_eq).
  Local Ltac unseal := rewrite wsim_eq /wsim_def.

  Context (fl_s fl_t : alist (option string) (Any.t → itree hmodE Any.t)).
  Context (Ist : nat → alist key Any.t → alist key Any.t → iProp Σ).
  Context (stid: nat).  
  Context (R_s R_t : Type).

  Local Notation sim Ep r g := (wsim fl_s fl_t Ist stid Ep r g R_s R_t).

  Context (Ep : option (coPset * coPset)).
  Context (r g : rel).
  Context (RR : post R_s R_t).
  Context (ps pt : bool).
  Context (nths : nat).
  Context (st_s st_t : state).

  (* Basic simulation rules *)
  Lemma wsim_ret rs rt :
    RR nths (st_s, rs) (st_t, rt) ⊢
    sim Ep r g RR ps pt nths (st_s, Ret rs) (st_t, Ret rt).
  Proof using. unseal; iIntros "RR I". by iApply isim_ret. Qed.

  Lemma wsim_call fn arg k_s k_t :
    Ist nths st_s st_t ∗
    (∀ ret nths' st_s' st_t'
      (NODS : List.NoDup (List.map fst st_s'))
      (NODD : List.NoDup (List.map fst st_t'))
      (NTHS: nths <= nths'),
      Ist nths' st_s' st_t' -∗
      sim Ep r g RR true true nths' (st_s', k_s ret) (st_t', k_t ret)) ⊢
    sim Ep r g RR ps pt nths
      (st_s, trigger (Call fn arg) >>= k_s) (st_t, trigger (Call fn arg) >>= k_t).
  Proof using.
    unseal; iIntros "[IST CONT] I".
    rewrite -isim_call; iFrame.
    iIntros (???????) "IST". iApply ("CONT" with "[] [] [] [IST]"); et; iFrame.
  Qed.

  Lemma wsim_call_sandbox k_s k_t fn arg img_src img_tgt (msk_src msk_tgt:_→bool) scp_src scp_tgt:
    (msk_src fn → msk_tgt fn) →
    Ist nths st_s st_t ∗
    (∀ ret nths' st_s' st_t'
      (NODS : List.NoDup (List.map fst st_s'))
      (NODD : List.NoDup (List.map fst st_t'))
      (NTHS: nths <= nths'),
      Ist nths' st_s' st_t' -∗
      sim Ep r g RR true true nths' (st_s', k_s ret) (st_t', k_t ret)) ⊢
    sim Ep r g RR ps pt nths
      (st_s, SB.sandbox img_src msk_src scp_src (trigger (Call fn arg)) >>= k_s)
      (st_t, SB.sandbox img_tgt msk_tgt scp_tgt (trigger (Call fn arg)) >>= k_t).
  Proof using.
    i. unseal. iIntros "[IST RR] I". iApply isim_call_sandbox; et. iFrame.
    iIntros (? ? ? ? ? ? ?) "IST".
    iSpecialize ("RR" $! vret nths0 _ _ NODS NODD NTHS).
    iApply ("RR" with "IST I").
  Qed.

  Lemma wsim_io fn I O (arg : I) k_s k_t :
    (∀ (ret : O),
      sim Ep r g RR true true nths (st_s, k_s ret) (st_t, k_t ret)) ⊢
    sim Ep r g RR ps pt nths
      (st_s, trigger (IO fn arg) >>= k_s)
      (st_t, trigger (IO fn arg) >>= k_t).
  Proof using. unseal; iIntros "RR I". iApply isim_io. iIntros (ret); iApply "RR"; iFrame. Qed.

  Lemma wsim_tau_src i_s i_t :
    sim Ep r g RR true pt nths (st_s, i_s) (st_t, i_t) ⊢
    sim Ep r g RR ps pt nths (st_s, tau;; i_s) (st_t, i_t).
  Proof using. unseal; iIntros "RR I". iApply isim_tau_src; iApply "RR"; iFrame. Qed.

  Lemma wsim_tau_tgt i_s i_t :
    sim Ep r g RR ps true nths (st_s, i_s) (st_t, i_t) ⊢
    sim Ep r g RR ps pt nths (st_s, i_s) (st_t, tau;; i_t).
  Proof using. unseal; iIntros "RR I". iApply isim_tau_tgt; iApply "RR"; iFrame. Qed.

  Lemma wsim_inline_src fn arg f_s k_s i_t :
    alist_find (Some fn) fl_s = Some f_s →
    sim Ep r g RR true pt nths
      (st_s, x <- (ret <- (f_s arg);; (tau;; Ret ret));; (k_s x))
      (st_t, i_t)
    ⊢
    sim Ep r g RR ps pt nths (st_s, trigger (Call fn arg) >>= k_s) (st_t, i_t).
  Proof using. i; unseal; iIntros "RR I". iApply isim_inline_src; eauto. iApply "RR"; iFrame. Qed.

  Lemma wsim_inline_src_sandbox fn arg f_s k_s i_t img (msk:_→bool) scp:
    alist_find (Some fn) fl_s = Some f_s →
    sim Ep r g RR true pt nths
      (st_s, x <- (ret <- (f_s arg);; (tau;; Ret ret));; (k_s x))
      (st_t, i_t) ⊢
    sim Ep r g RR ps pt nths (st_s, SB.sandbox img msk scp (trigger (Call fn arg)) >>= k_s) (st_t, i_t).
  Proof using.
    i. unseal. iIntros "RR I". iApply isim_inline_src_sandbox; et.
    iApply ("RR" with "I").
  Qed.

  Lemma wsim_inline_tgt fn arg i_s f_t k_t :
    alist_find (Some fn) fl_t = Some f_t →
    sim Ep r g RR ps true nths
      (st_s, i_s)
      (st_t, x <- (ret <- (f_t arg);; (tau;; Ret ret));; (k_t x))
    ⊢
    sim Ep r g RR ps pt nths (st_s, i_s) (st_t, trigger (Call fn arg) >>= k_t).
  Proof using. i; unseal; iIntros "RR I". iApply isim_inline_tgt; eauto. iApply "RR"; iFrame. Qed.

  Lemma wsim_inline_tgt_sandbox fn arg i_s f_t k_t img (msk:_→bool) scp:
    alist_find (Some fn) fl_t = Some f_t →
    (msk fn) →
    sim Ep r g RR ps true nths
      (st_s, i_s)
      (st_t, x <- (ret <- (f_t arg);; (tau;; Ret ret));; (k_t x))
    ⊢
    sim Ep r g RR ps pt nths (st_s, i_s) (st_t, SB.sandbox img msk scp (trigger (Call fn arg)) >>= k_t).
  Proof using.
    i. iIntros "ISIM". rewrite SBRed.call. des_ifs; ss. iApply wsim_inline_tgt; eauto.
  Qed.
  
  Lemma wsim_take_src X k_s i_t :
    (∀ x, sim Ep r g RR true pt nths (st_s, k_s x) (st_t, i_t)) ⊢
    sim Ep r g RR ps pt nths (st_s, trigger (Take X) >>= k_s) (st_t, i_t).
  Proof using.
    unseal; iIntros "RR I". iApply isim_take_src; eauto. iIntros (x); iApply "RR"; iFrame.
  Qed.

  Lemma wsim_take_tgt X i_s k_t :
    (∃ x, sim Ep r g RR ps true nths (st_s, i_s) (st_t, k_t x)) ⊢
    sim Ep r g RR ps pt nths (st_s, i_s) (st_t, trigger (Take X) >>= k_t).
  Proof using.
    unseal; iIntros "[%x RR] I". iApply isim_take_tgt; eauto. iExists _; iApply "RR"; iFrame.
  Qed.

  Lemma wsim_choose_src X k_s i_t :
    (∃ x, sim Ep r g RR true pt nths (st_s, k_s x) (st_t, i_t)) ⊢
    sim Ep r g RR ps pt nths (st_s, trigger (Choose X) >>= k_s) (st_t, i_t).
  Proof using.
    unseal; iIntros "[%x RR] I". iApply isim_choose_src; eauto. iExists _; iApply "RR"; iFrame.
  Qed.

  Lemma wsim_choose_tgt X i_s k_t :
    (∀ x, sim Ep r g RR ps true nths (st_s, i_s) (st_t, k_t x)) ⊢
    sim Ep r g RR ps pt nths (st_s, i_s) (st_t, trigger (Choose X) >>= k_t).
  Proof using.
    unseal; iIntros "RR I". iApply isim_choose_tgt; eauto. iIntros (x); iApply "RR"; iFrame.
  Qed.

  Lemma wsim_sput_src k v k_s i_t :
    sim Ep r g RR true pt nths (alist_upd k v st_s, k_s tt) (st_t, i_t) ⊢
    sim Ep r g RR ps pt nths (st_s, trigger (SPut k v) >>= k_s) (st_t, i_t).
  Proof using. unseal; iIntros "RR I". iApply isim_sput_src; eauto. iApply "RR"; iFrame. Qed.

  Lemma wsim_sput_tgt k v i_s k_t :
    sim Ep r g RR ps true nths (st_s, i_s) (alist_upd k v st_t, k_t tt) ⊢
    sim Ep r g RR ps pt nths (st_s, i_s) (st_t, trigger (SPut k v) >>= k_t).
  Proof using. unseal; iIntros "RR I". iApply isim_sput_tgt; eauto. iApply "RR"; iFrame. Qed.

  Lemma wsim_sget_src k k_s i_t :
    sim Ep r g RR true pt nths (st_s, k_s (or_else (alist_find k st_s) tt↑)) (st_t, i_t) ⊢
    sim Ep r g RR ps pt nths (st_s, trigger (SGet k) >>= k_s) (st_t, i_t).
  Proof using. unseal; iIntros "RR I". iApply isim_sget_src; eauto. iApply "RR"; iFrame. Qed.

  Lemma wsim_sget_tgt k i_s k_t :
    sim Ep r g RR ps true nths (st_s, i_s) (st_t, k_t (or_else (alist_find k st_t) tt↑)) ⊢
    sim Ep r g RR ps pt nths (st_s, i_s) (st_t, trigger (SGet k) >>= k_t).
  Proof using. unseal; iIntros "RR I". iApply isim_sget_tgt; eauto. iApply "RR"; iFrame. Qed.

  Lemma wsim_assume_src P k_s i_t :
    (P -∗ sim Ep r g RR true pt nths (st_s, k_s tt) (st_t, i_t)) ⊢
    sim Ep r g RR ps pt nths (st_s, trigger (Assume P) >>= k_s) (st_t, i_t).
  Proof using.
    unseal; iIntros "RR I". iApply isim_assume_src; eauto. iIntros "P".
    iApply ("RR" with "P"); iFrame.
  Qed.

  Lemma wsim_assume_precise_src P k_s i_t :
    precise P ∗
    (P -∗ sim Ep r g RR true pt nths (st_s, k_s tt) (st_t, i_t)) ⊢
    sim Ep r g RR ps pt nths (st_s, trigger (AssumePrecise P) >>= k_s) (st_t, i_t).
  Proof using.
    unseal. iIntros "[P H] I". iApply isim_assume_precise_src; eauto.
    iFrame. iIntros "P". iApply ("H" with "P I").
  Qed.

  Lemma wsim_assume_tgt P i_s k_t :
    P ∗ sim Ep r g RR ps true nths (st_s, i_s) (st_t, k_t tt) ⊢
    sim Ep r g RR ps pt nths (st_s, i_s) (st_t, trigger (Assume P) >>= k_t).
  Proof using.
    unseal; iIntros "[P RR] I". iApply isim_assume_tgt; eauto. iFrame. iApply "RR". ss.
  Qed.

  Lemma wsim_assume_precise_tgt P i_s k_t :
    (precise P -∗ P ∗ sim Ep r g RR ps true nths (st_s, i_s) (st_t, k_t tt)) ⊢
    sim Ep r g RR ps pt nths (st_s, i_s) (st_t, trigger (AssumePrecise P) >>= k_t).
  Proof using.
    unseal; iIntros "H I". iApply isim_assume_precise_tgt; eauto.
    iIntros "P". iPoseProof ("H" with "P") as "[P H]". iFrame. iApply "H". done.
  Qed.

  Lemma wsim_assume_precise_both P k_s k_t :
    (sim Ep r g RR true true nths (st_s, k_s tt) (st_t, k_t tt)) ⊢
    sim Ep r g RR ps pt nths
      (st_s, trigger (AssumePrecise P) >>= k_s)
      (st_t, trigger (AssumePrecise P) >>= k_t).
  Proof using.
    unseal. iIntros "RR I". iApply isim_assume_precise_both; eauto. by iApply "RR".
  Qed.

  Lemma wsim_guarantee_src (P : iProp Σ) k_s i_t :
    P ∗ sim Ep r g RR true pt nths (st_s, k_s tt) (st_t, i_t) ⊢
    sim Ep r g RR ps pt nths (st_s, trigger (Guarantee P) >>= k_s) (st_t, i_t).
  Proof using.
    unseal; iIntros "[P RR] I". iApply isim_guarantee_src; eauto. iFrame. iApply "RR"; ss.
  Qed.

  Lemma wsim_guarantee_tgt (P : iProp Σ) i_s k_t :
    (P -∗ sim Ep r g RR ps true nths (st_s, i_s) (st_t, k_t tt)) ⊢
    sim Ep r g RR ps pt nths (st_s, i_s) (st_t, trigger (Guarantee P) >>= k_t).
  Proof using.
    unseal; iIntros "RR I". iApply isim_guarantee_tgt; eauto.
    iIntros "P"; iApply ("RR" with "P"); done.
  Qed.

  Lemma wsim_spawn fn args k_s k_t :
    sim Ep r g RR true true (S nths) (st_s, k_s nths) (st_t, k_t nths) ⊢
    sim Ep r g RR ps pt nths
      (st_s, trigger (Spawn fn args) >>= k_s)
      (st_t, trigger (Spawn fn args) >>= k_t).
  Proof using. unseal; iIntros "C I". iApply isim_spawn; eauto. iApply "C". ss. Qed.

  Lemma wsim_spawn_sandbox fn args k_s k_t img_src img_tgt (msk_src msk_tgt:_→bool) scp_src scp_tgt:
    (msk_src fn → msk_tgt fn) →
    sim Ep r g RR true true (S nths)
      (st_s, k_s nths) (st_t, k_t nths) ⊢
    sim Ep r g RR ps pt nths
      (st_s, SB.sandbox img_src msk_src scp_src (trigger (Spawn fn args)) >>= k_s)
      (st_t, SB.sandbox img_tgt msk_tgt scp_tgt (trigger (Spawn fn args)) >>= k_t).
  Proof using.
    i. unseal. iIntros "RR I". iApply isim_spawn_sandbox; et.
    iApply ("RR" with "I").
  Qed.

  Lemma wsim_yield tid k_s k_t :
    Ist nths st_s st_t ∗
    (∀ nths' st_s' st_t' (NODS : List.NoDup (map fst st_s')) (NODT : List.NoDup (map fst st_t')) (NTHS: nths <= nths'),
      Ist nths' st_s' st_t' -∗
      sim Ep r g RR true true nths'
        (st_s', k_s stid) (st_t', k_t stid)) ⊢
    sim Ep r g RR ps pt nths
      (st_s, trigger (Yield tid) >>= k_s)
      (st_t, trigger (Yield tid) >>= k_t).
  Proof using.
    unseal; iIntros "[IST C] I". iApply isim_yield; eauto. iFrame.
    iIntros (??????) "IST"; iApply ("C" with "[] [] [] [IST] [I]"); iFrame; et.
  Qed.

  Lemma wsim_reset i_s i_t :
    sim Ep r g RR false false nths (st_s, i_s) (st_t, i_t) ⊢
    sim Ep r g RR ps pt nths (st_s, i_s) (st_t, i_t).
  Proof using. unseal; iIntros "RR I". iApply isim_reset; iApply "RR"; iFrame. Qed.

  Lemma wsim_progress i_s i_t :
    sim Ep g g RR false false nths (st_s, i_s) (st_t, i_t) ⊢
    sim Ep r g RR true true nths (st_s, i_s) (st_t, i_t).
  Proof using. unseal; iIntros "RR I". iApply isim_progress; iApply "RR"; iFrame. Qed.

  Lemma wsim_base i_s i_t :
    (wsim_ginv Ep -∗ r R_s R_t RR ps pt nths (st_s, i_s) (st_t, i_t)) ⊢
    sim Ep r g RR ps pt nths (st_s, i_s) (st_t, i_t).
  Proof using. unseal; iIntros "RR I". iApply isim_base; iRevert "I"; iFrame. Qed.

  Lemma wsim_coind A P RA_s RA_t RRA psA ptA nthsA srcA tgtA :
    (∀ (g' : rel) (a : A),
      P a -∗
      (⌜∀ R_s R_t RR ps pt nths0 src tgt,
        g R_s R_t RR ps pt nths0 src tgt -∗ g' R_s R_t RR ps pt nths0 src tgt⌝) -∗
      (□ ∀ a, (P a ∗ wsim_ginv Ep) -∗
        g' (RA_s a) (RA_t a) (RRA a) (psA a) (ptA a) (nthsA a) (srcA a) (tgtA a)) -∗
      wsim fl_s fl_t Ist stid Ep r g'
        (RA_s a) (RA_t a) (RRA a) (psA a) (ptA a) (nthsA a) (srcA a) (tgtA a)) →
    ∀ (a : A), P a ⊢
      wsim fl_s fl_t Ist stid Ep r g
        (RA_s a) (RA_t a) (RRA a) (psA a) (ptA a) (nthsA a) (srcA a) (tgtA a).
  Proof using.
    unseal; intros H a; iIntros "P I"; iCombine "P I" as "P". iStopProof.
    (* rewrite /wsim_retcond *)
    revert a. eapply isim_coind.
    intros g' a Himpl; iIntros "[[P I] #CIH]".
    iPoseProof (H with "P [] [] I") as "H".
    { instantiate (1 := g').
      iPureIntro; iIntros (????????) "G"; destruct src, tgt. iApply Himpl. iFrame.
    }
    { iModIntro; iIntros (a') "[P I]"; iSpecialize ("CIH" $! a'); destruct (srcA a'), (tgtA a').
      iApply "CIH"; iFrame.
    }
    iApply (isim_mono_knowledge with "H"); ss.
    { iIntros (????????) "H"; iModIntro; iFrame. }
    { iIntros (????????) "H !>"; destruct sti_src, sti_tgt; iFrame. }
  Qed.

  Lemma wsim_bind {Qs Qt} QQ i_s i_t k_s k_t :
    wsim fl_s fl_t Ist stid Ep r g Qs Qt QQ ps pt nths (st_s, i_s) (st_t, i_t)
    ∗ (∀ nths' st_s' r_s st_t' r_t (NTHS: nths <= nths'),
        QQ nths' (st_s', r_s) (st_t', r_t)
        -∗ sim None r g RR false false nths' (st_s', k_s r_s) (st_t', k_t r_t))%I
    ⊢ (sim Ep r g RR ps pt nths (st_s, i_s >>= k_s) (st_t, i_t >>= k_t)).
  Proof using.
    rewrite wsim.wsim_eq /wsim.wsim_def.
    iIntros "[W SIM] INV". iApply isim_bind.
    iSplitL "W INV". { iApply "W"; eauto. }
    iIntros (? ? ? ? ? ?) "Q". iSpecialize ("SIM" $! _ _ _ _ _ NTHS).
    iApply ("SIM" with "Q"). done.
  Qed.

  (* Lemmas that use WP typeclasses *)
  Lemma wsim_guarantee_src_WP `{i : !WP P} k_s i_t Ew E :
    let EP := WP_space i in
    EP ⊆ Ew → EP ⊆ E →
    (WP_remainder i ∗
    sim (Some (Ew ∖ EP, E ∖ EP)) r g RR true pt nths (st_s, k_s tt) (st_t, i_t)) ⊢
    sim (Some (Ew, E)) r g RR ps pt nths (st_s, trigger (Guarantee P) >>= k_s) (st_t, i_t).
  Proof using.
    unseal; iIntros (??) "[P SIM] I".
    iPoseProof (wsim_ginv_split (WP_space i) (Ew ∖ WP_space i) (WP_space i) (E ∖ WP_space i)
      with "[I]") as "[I1 I2]".
    { set_solver. }
    { set_solver. }
    { rewrite -?union_difference_L //. }
    iApply isim_guarantee_src; eauto.
    iSplitR "SIM I2".
    { iApply WP_iff; iFrame. }
    { iApply "SIM"; iFrame. }
  Qed.

  Lemma wsim_assume_src_WP `{i : !WP P} k_s i_t :
    let EP := WP_space i in
    let Ep' :=
      match Ep with | Some (Ew, E) => Some (Ew ∪ EP, E ∪ EP) | None => Some (EP, EP) end
    in
    (WP_remainder i -∗ sim Ep' r g RR true pt nths (st_s, k_s tt) (st_t, i_t)) ⊢
    sim Ep r g RR ps pt nths (st_s, trigger (Assume P) >>= k_s) (st_t, i_t).
  Proof using.
    unseal; iIntros "SIM I1". iApply isim_assume_src; eauto. iIntros "P".
    destruct Ep as [[??]|]; iPoseProof (WP_iff with "P") as "[I Q]";
      try iApply ("SIM" with "Q I").
    iMod (wsim_ginv_merge with "[I I1]") as "[I _]"; iFrame.
    iApply ("SIM" with "Q"); iFrame.
  Qed.

  Lemma wsim_assume_tgt_WP `{i : !WP P} i_s k_t Ew E :
    let EP := WP_space i in
    EP ⊆ Ew → EP ⊆ E →
    (WP_remainder i ∗ sim (Some (Ew ∖ EP, E ∖ EP)) r g RR ps true nths (st_s, i_s) (st_t, k_t tt)) ⊢
    sim (Some (Ew, E)) r g RR ps pt nths (st_s, i_s) (st_t, trigger (Assume P) >>= k_t).
  Proof using.
    unseal; iIntros (??) "[P SIM] [O [E [%n W]]]".
    iPoseProof (own_admin_split with "O") as "[O1 O2]". iApply isim_assume_tgt; eauto.
    rewrite /wsim_ginv {2}(union_difference_L (WP_space i) Ew) // wsats_split; last set_solver.
    rewrite {2}(union_difference_L (WP_space i) E) // ownE_op; last set_solver.
    iDestruct "W" as "[W1 W2]"; iDestruct "E" as "[E1 E2]".
    iSplitR "SIM E2 W2 O2".
    { iApply WP_iff; iFrame. }
    { iApply "SIM"; iFrame. }
  Qed.

  Lemma wsim_assume_precise_tgt_WP `{i : !WP P} i_s k_t Ew E :
    let EP := WP_space i in
    EP ⊆ Ew → EP ⊆ E →
    (precise P -∗
     WP_remainder i ∗ sim (Some (Ew ∖ EP, E ∖ EP)) r g RR ps true nths (st_s, i_s) (st_t, k_t tt)) ⊢
    sim (Some (Ew, E)) r g RR ps pt nths
      (st_s, i_s) (st_t, trigger (AssumePrecise P) >>= k_t).
  Proof using.
    unseal; i; iIntros "H [O [E [%n W]]]".
    iPoseProof (own_admin_split with "O") as "[O1 O2]". iApply isim_assume_precise_tgt; eauto.
    iIntros "P". iPoseProof ("H" with "P") as "[P SIM]".
    rewrite /wsim_ginv {1}(union_difference_L (WP_space i) Ew) // wsats_split; last set_solver.
    rewrite {1}(union_difference_L (WP_space i) E) // ownE_op; last set_solver.
    iDestruct "W" as "[W1 W2]"; iDestruct "E" as "[E1 E2]".
    iSplitR "SIM E2 W2 O2".
    { iApply WP_iff; iFrame. }
    { iApply "SIM"; iFrame. }
  Qed.

  Lemma wsim_guarantee_tgt_WP `{i : !WP P} i_s k_t :
    let EP := WP_space i in
    let Ep' :=
      match Ep with | Some (Ew, E) => Some (Ew ∪ EP, E ∪ EP) | None => Some (EP, EP) end
    in
    (WP_remainder i -∗ sim Ep' r g RR ps true nths (st_s, i_s) (st_t, k_t tt)) ⊢
    sim Ep r g RR ps pt nths (st_s, i_s) (st_t, trigger (Guarantee P) >>= k_t).
  Proof using.
    s; iIntros "SIM"; iApply wsim_guarantee_tgt; iIntros "P".
    iPoseProof (WP_iff i with "P") as "[P1 P2]".
    unseal; iIntros "I".
    iAssert ( |==> wsim_ginv
      (match Ep with
      | Some (Ew, E) => Some (Ew ∪ WP_space i, E ∪ WP_space i)
      | None => Some (WP_space i, WP_space i)
      end))%I with "[I P1]" as "> I".
    { destruct Ep as [[??]|]; ss; iPoseProof (wsim_ginv_merge with "[I P1]") as "[$ _]"; iFrame. }
    iApply ("SIM" with "P2"); ss.
  Qed.

  (* Derived lemmas *)
  Lemma wsim_unwrapU_src X (x : option X) k_s i_t :
    (∀ x', ⌜x = Some x'⌝ -∗ sim Ep r g RR ps pt nths (st_s, k_s x') (st_t, i_t)) ⊢
    sim Ep r g RR ps pt nths (st_s, unwrapU x >>= k_s) (st_t, i_t).
  Proof using.
    iIntros "H". unfold unwrapU. destruct x.
    { ired. iApply "H". auto. }
    { unseal; iIntros "P". iApply isim_triggerUB_src. }
  Qed.

  Lemma wsim_unwrapN_src X (x : option X) k_s i_t :
    (∃ x', ⌜x = Some x'⌝ ∗
      sim Ep r g RR ps pt nths
        (st_s, k_s x') (st_t, i_t)) ⊢
    sim Ep r g RR ps pt nths
      (st_s, unwrapN x >>= k_s) (st_t, i_t).
  Proof using. iIntros "H". iDestruct "H" as (x') "[% H]". subst. ired. iApply "H". Qed.

  Lemma wsim_sput_src_sandbox img msk scp k v k_s i_t :
    In k.1 scp →
    sim Ep r g RR true pt nths
      (alist_upd k v st_s, k_s tt) (st_t, i_t) ⊢
    sim Ep r g RR ps pt nths
      (st_s, SB.sandbox img msk scp (trigger (SPut k v)) >>= k_s) (st_t, i_t).
  Proof using.
    intros IN; iIntros "SIM".
    rewrite SBRed.put; des_ifs; ss.
    { iApply wsim_sput_src; ss. }
    { edestruct (existsb_exists (String.eqb k.1) scp).
      hexploit H0; ss.
      { exists k.1; split; ss. apply String.eqb_refl. }
      { i; clarify. }
    }
  Qed.

  Lemma wsim_sget_src_sandbox img msk scp k k_s i_t :
    In k.1 scp →
    sim Ep r g RR true pt nths
      (st_s, k_s (or_else (alist_find k st_s) tt↑)) (st_t, i_t) ⊢
    sim Ep r g RR ps pt nths
      (st_s, SB.sandbox img msk scp (trigger (SGet k)) >>= k_s) (st_t, i_t).
  Proof using.
    intros IN; iIntros "SIM".
    rewrite SBRed.get; des_ifs; ss.
    { iApply wsim_sget_src; ss. }
    { edestruct (existsb_exists (String.eqb k.1) scp).
      hexploit H0; ss.
      { exists k.1; split; ss. apply String.eqb_refl. }
      { i; clarify. }
    }
  Qed.

  Lemma wsim_sput_tgt_sandbox img msk scp k v i_s k_t :
    In k.1 scp →
    sim Ep r g RR ps true nths
      (st_s, i_s) (alist_upd k v st_t, k_t tt) ⊢
    sim Ep r g RR ps pt nths
      (st_s, i_s) (st_t, SB.sandbox img msk scp (trigger (SPut k v)) >>= k_t).
  Proof using.
    intros IN; iIntros "SIM".
    rewrite SBRed.put; des_ifs; ss.
    { iApply wsim_sput_tgt; ss. }
    { edestruct (existsb_exists (String.eqb k.1) scp).
      hexploit H0; ss.
      { exists k.1; split; ss. apply String.eqb_refl. }
      { i; clarify. }
    }
  Qed.

  Lemma wsim_sget_tgt_sandbox img msk scp k i_s k_t :
    In k.1 scp →
    sim Ep r g RR ps true nths
      (st_s, i_s) (st_t, k_t (or_else (alist_find k st_t) tt↑)) ⊢
    sim Ep r g RR ps pt nths
      (st_s, i_s) (st_t, SB.sandbox img msk scp (trigger (SGet k)) >>= k_t).
  Proof using.
    intros IN; iIntros "SIM".
    rewrite SBRed.get; des_ifs; ss.
    { iApply wsim_sget_tgt; ss. }
    { edestruct (existsb_exists (String.eqb k.1) scp).
      hexploit H0; ss.
      { exists k.1; split; ss. apply String.eqb_refl. }
      { i; clarify. }
    }
  Qed.

  Lemma wsim_asm_src (P : Prop) k_s i_t :
    (⌜P⌝ -∗ (sim Ep r g RR true pt nths (st_s, k_s tt) (st_t, i_t))) ⊢
    sim Ep r g RR ps pt nths (st_s, assume P >>= k_s) (st_t, i_t).
  Proof using.
    unseal; iIntros "RR I". iApply isim_asm_src; eauto.
    iIntros "%H"; iApply ("RR" $! H with "I"); iFrame.
  Qed.

  Lemma wsim_asm_tgt (P : Prop) i_s k_t :
    ⌜P⌝ ∗ sim Ep r g RR ps true nths (st_s, i_s) (st_t, k_t tt) ⊢
    sim Ep r g RR ps pt nths (st_s, i_s) (st_t, assume P >>= k_t).
  Proof using.
    unseal; iIntros "[%HP SIM] I". iApply isim_asm_tgt; eauto. iApply ("SIM" with "I").
  Qed.

  Lemma wsim_guar_src (P : Prop) k_s i_t :
    ⌜P⌝ ∗ sim Ep r g RR true pt nths (st_s, k_s tt) (st_t, i_t) ⊢
    sim Ep r g RR ps pt nths (st_s, guarantee P >>= k_s) (st_t, i_t).
  Proof using.
    unseal; iIntros "[P H] I". iApply isim_guar_src; eauto. iFrame.
    iApply ("H" with "I").
  Qed.

  Lemma wsim_guar_tgt (P : Prop) i_s k_t :
    (⌜P⌝ -∗ sim Ep r g RR ps true nths (st_s, i_s) (st_t, k_t tt)) ⊢
    sim Ep r g RR ps pt nths (st_s, i_s) (st_t, guarantee P >>= k_t).
  Proof using.
    unseal; iIntros "RR I". iApply isim_guar_tgt; eauto.
    iIntros "%H"; iApply ("RR" $! H with "I"); iFrame.
  Qed.

  Lemma wsim_nodup i_s i_t:
    (∀ (NODS : List.NoDup (List.map fst st_s))
       (NODD : List.NoDup (List.map fst st_t)),
      sim Ep r g RR ps pt nths (st_s, i_s) (st_t, i_t))
    ⊢ sim Ep r g RR ps pt nths (st_s, i_s) (st_t, i_t).
  Proof using.
    unseal; iIntros "SIM I". iApply isim_nodup; eauto.
    iIntros (????). iApply "SIM"; eauto.
  Qed.
  
  Lemma wsim_fupd m Ew E1 E2 i_s i_t :
    =|m, Ew|={E2, E1}=> sim (Some (Ew, E1)) r g RR ps pt nths (st_s, i_s) (st_t, i_t)
    ⊢ sim (Some (Ew, E2)) r g RR ps pt nths (st_s, i_s) (st_t, i_t).
  Proof using.
    unseal; iIntros "SIM [O [E [%n [WA W]]]]".
    set (nm := n `max` m).
    iPoseProof (fupd_mon _ nm with "SIM") as "SIM"; first lia.
    iMod (wsatl_mon n nm with "[WA W]") as "[WA W]"; first lia; iFrame.
    rewrite invariants.uPred_fupd_unseal /invariants.uPred_fupd_def.
    iMod ("SIM" with "[O W E]") as "[W [E [O SIM]]]"; iFrame.
    iApply "SIM"; iFrame.
  Qed.

  (* Proofmode instances *)
  Global Instance wsim_elim_upd P p i_s i_t :
    ElimModal True p false ( |==> P)%I P
      (sim Ep r g RR ps pt nths (st_s, i_s) (st_t, i_t))
      (sim Ep r g RR ps pt nths (st_s, i_s) (st_t, i_t)).
  Proof using.
    unseal.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1] HPRE".
    iApply isim_upd. iMod "H0". iModIntro.
    iApply ("H1" with "H0 HPRE").
  Qed.

  Global Instance wsim_elim_fupd_gen Ew Ew' E0 E1 E2 n P p i_s i_t :
    ElimModal
      (E0 ⊆ E2 ∧ Ew' ⊆ Ew) p false
      (=|n, Ew'|={E0, E1}=> P)
      P
      (sim (Some (Ew, E2)) r g RR ps pt nths (st_s, i_s) (st_t, i_t))
      (sim (Some (Ew, E1 ∪ (E2 ∖ E0))) r g RR ps pt nths (st_s, i_s) (st_t, i_t)) | 10.
  Proof using.
    rewrite /ElimModal bi.intuitionistically_if_elim /=.
    iIntros ([??]) "[P SIM]".
    iApply (wsim_fupd n Ew (E1 ∪ E2 ∖ E0)). iMod "P".
    iModIntro. iApply ("SIM" with "P").
  Qed.

  Global Instance elim_fupd_wsim_same_mask Ew Ew' E1 E2 n p P i_s i_t :
    ElimModal
      (E1 ⊆ E2 ∧ Ew' ⊆ Ew) p false
      (=|n, Ew|={E1}=> P)
      P
      (sim (Some (Ew, E2)) r g RR ps pt nths (st_s, i_s) (st_t, i_t))
      (sim (Some (Ew, E2)) r g RR ps pt nths (st_s, i_s) (st_t, i_t)).
  Proof using.
    rewrite /ElimModal bi.intuitionistically_if_elim.
    iIntros ([??]) "[> P SIM]"; rewrite -union_difference_L //; iApply ("SIM" with "P").
  Qed.

  Global Instance elim_fupd_wsim_simple Ew Ew' E0 E1 n P p i_s i_t :
    ElimModal
      (Ew' ⊆ Ew) p false
      (=|n, Ew'|={E0, E1}=> P)
      P
      (sim (Some (Ew, E0)) r g RR ps pt nths (st_s, i_s) (st_t, i_t))
      (sim (Some (Ew, E1)) r g RR ps pt nths (st_s, i_s) (st_t, i_t)).
  Proof using.
    rewrite /ElimModal bi.intuitionistically_if_elim.
    iIntros (?) "[> P SIM]". rewrite difference_diag_L right_id_L; iApply "SIM"; done.
  Qed.

  Global Instance wpsim_add_modal_FUpd Ew E n P i_s i_t :
    AddModal (=|n, Ew|={E}=> P) P
             (sim (Some (Ew, E)) r g RR ps pt nths (st_s, i_s) (st_t, i_t)).
  Proof using.
    unfold AddModal. iIntros "[H0 H1]". iMod "H0". iApply ("H1" with "H0").
  Qed.

  Lemma wsim_own_alloc `{!inG A Σ} (a : A) Ew E i_s i_t :
    ✓ a →
    ((∃ γ, own γ a) -∗ sim (Some (Ew, E)) r g RR ps pt nths (st_s, i_s) (st_t, i_t))
    ⊢ sim (Some (Ew, E)) r g RR ps pt nths (st_s, i_s) (st_t, i_t).
  Proof using.
    iIntros (?) "SIM".
    iMod (own_alloc a) as "O"; ss; iApply ("SIM" with "O"); iFrame.
  Qed.

  (* Primitive simulation rules *)
  Lemma wsim_isim sti_s sti_t :
    sim None r g RR ps pt nths sti_s sti_t ⊢
    @isim Σ open fl_s fl_t Ist stid r g R_s R_t RR ps pt nths sti_s sti_t.
  Proof using.
    unseal; iIntros "SIM"; ss. iApply "SIM"; et.
  Qed.

  Lemma isim_wsim sti_s sti_t :
    @isim Σ open fl_s fl_t Ist stid r g R_s R_t RR ps pt nths sti_s sti_t ⊢
    sim None r g RR ps pt nths sti_s sti_t.
  Proof using.
    unseal. iIntros "H _". et.
  Qed.

  Lemma wsim_unfold Ew E sti_s sti_t :
    (wsim_ginv (Some (Ew, E)) -∗ sim None r g RR ps pt nths sti_s sti_t) ⊢
    sim (Some (Ew, E)) r g RR ps pt nths sti_s sti_t.
  Proof using.
    unseal. iIntros "SIM PRE"; ss. iApply ("SIM" with "PRE"). done.
  Qed.

  Lemma wsim_fold Ew E sti_s sti_t :
    wsim_ginv (Some (Ew, E)) ∗ sim (Some (Ew, E)) r g RR ps pt nths sti_s sti_t ⊢
    sim None r g RR ps pt nths sti_s sti_t.
  Proof using.
    unseal. iIntros "[PRE SIM] _"; ss. iApply ("SIM" with "PRE").
  Qed.

  Lemma wsim_eqit_src i_s0 i_s1 i_t :
    eqit eq false true i_s0 i_s1 →
    sim Ep r g RR ps pt nths (st_s, i_s0) (st_t, i_t) ⊢
    sim Ep r g RR ps pt nths (st_s, i_s1) (st_t, i_t).
  Proof using.
    rewrite wsim_eq /wsim_def.
    iIntros (Heq) "S W"; iPoseProof ("S" with "W") as "S".
    iStopProof; eapply isim_eqit_src; eauto.
  Qed.

  Lemma wsim_eqit_tgt i_s i_t0 i_t1 :
    eqit eq false true i_t0 i_t1 →
    sim Ep r g RR ps pt nths (st_s, i_s) (st_t, i_t0) ⊢
    sim Ep r g RR ps pt nths (st_s, i_s) (st_t, i_t1).
  Proof using.
    rewrite wsim_eq /wsim_def.
    iIntros (?) "S W"; iPoseProof ("S" with "W") as "S"; iStopProof; eapply isim_eqit_tgt; eauto.
  Qed.
End wsim.
Global Arguments wsim_own_alloc {_ _ _ _ _ _ _ _ _ _ _ _ _} _.

(* Lemmas for prophecies *)
Section Proph.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Context (fl_s fl_t : alist (option string) (Any.t → itree hmodE Any.t)).
  Context (Ist : nat → alist key Any.t → alist key Any.t → iProp Σ).
  Context (stid: nat).  
  Context (R_s R_t : Type).

  Context (Ep : option (coPset * coPset)).
  Context (r g : rel).
  Context (RR : post R_s R_t).
  Context (ps pt : bool).
  Context (nths : nat).
  Context (st_s st_t : state).

  Local Notation sim Ep r g := (wsim fl_s fl_t Ist stid Ep r g R_s R_t).

  (** Precise Pre & Post conditions **)
  Lemma wsim_assume_proph_src {X R} Pre (Post: _ → R → _) k_s i_t :
    (∃ P Q,
      precise P ∗
      (∀ (x : X), Pre x ==∗ P ∗ (∀ ret, Q ret ==∗ Post x ret)) ∗
      (P -∗ sim Ep r g RR true pt nths (st_s, k_s Q) (st_t, i_t))) ⊢
    sim Ep r g RR ps pt nths (st_s, (AssumeProph Pre Post) >>= k_s) (st_t, i_t).
  Proof.
    rewrite wsim_eq /wsim_def.
    iIntros "[% [% [#PR [G H]]]] W".
    iApply isim_assume_proph_src. iFrame. iSplit; et.
    iIntros "P". iApply ("H" with "P W").
  Qed.

  Lemma wsim_assume_proph_src_advanced {X R} (Pre : X → _) Post k_s i_t :
    (∃ I P Q,
      I ∗ precise P ∗
      (∀ x, ∃ T, (I ∗ Pre x -∗ □ T) ∗ ((□ T) ∗ Pre x ==∗ P ∗ (∀ ret: R, Q ret ==∗ Post x ret))) ∗
      (I ∗ P -∗ sim Ep r g RR true pt nths (st_s, k_s Q) (st_t, i_t))) ⊢
    sim Ep r g RR ps pt nths (st_s, (AssumeProph Pre Post) >>= k_s) (st_t, i_t).
  Proof.
    rewrite wsim_eq /wsim_def.
    iIntros "[% [% [% [I [#PR [G H]]]]]] W".
    iApply isim_assume_proph_src_advanced. iFrame. iSplit; et.
    iIntros "P". iApply ("H" with "P W").
  Qed.

  Lemma wsim_assume_proph_src_simple {X R} Pre (Post : _ → R → _) k_s i_t :
    (∃ (x : X), precise (Pre x) ∗
      ∀ x', Pre x' -∗
        ⌜x' = x⌝ ∗
        sim Ep r g RR true pt nths (st_s, k_s (Post x)) (st_t, i_t)) ⊢
    sim Ep r g RR ps pt nths (st_s, (AssumeProph Pre Post) >>= k_s) (st_t, i_t).
  Proof.
    rewrite wsim_eq /wsim_def.
    iIntros "[% [#PR H]] W".
    iApply isim_assume_proph_src_simple. iExists _. iSplit; et.
    iIntros (?) "P". iPoseProof ("H" with "P") as "[%E' H]". subst.
    iSplit; et. iApply ("H" with "W").
  Qed.

  Lemma wsim_assume_proph_tgt {X R} Pre (Post : _ → R → _) i_s k_t :
    (∃ x: X, Pre x ∗
       ∀ Q, (∀ ret, Q ret ==∗ Post x ret) -∗
       sim Ep r g RR ps true nths (st_s, i_s) (st_t, k_t Q)) ⊢
    sim Ep r g RR ps pt nths (st_s, i_s) (st_t, (AssumeProph Pre Post) >>= k_t).
  Proof.
    rewrite wsim_eq /wsim_def.
    iIntros "[% [P H]] W".
    iApply isim_assume_proph_tgt. iExists _. iFrame.
    iIntros (?) "R". iApply ("H" with "R W").
  Qed.
End Proph.
