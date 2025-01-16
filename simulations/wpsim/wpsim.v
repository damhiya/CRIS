Require Import Common.

Require Import ISim SMod SMod2HMod HMod.
Require Import Skeleton.

From stdpp Require Import coPset.

Section wpsim.
  Context `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ}.
  Context {fl_s fl_t : alist string (Any.t → itree hmodE Any.t)}.
  Context {Ist : nat → alist key Any.t → alist key Any.t → iProp Σ}.
  Context {my_tid : nat}.
  Context {u : positive}.
  Context {n : level}.

  Local Definition state : Type := alist key Any.t.
  Local Definition post (R : Type) : Type := nat → state * R → state * R → iProp Σ.
  Local Definition rel : Type := ∀ R : Type,
    post R → bool → bool → nat → state * itree hmodE R → state * itree hmodE R → iProp Σ.

  Implicit Types r g : rel.
  Implicit Types ps pt : bool.
  Implicit Types nths : nat.
  Implicit Types E : coPset.

  (* TODO : abstraction into mixins *)
  (* TODO : hard-code nodup conditions *)
  Local Definition wpsim_pre u n E : iProp Σ := own_admin ∗ univs u n ∗ wsats u n E.
  Local Definition wpsim_retcond u n {R} (RR : post R) : post R :=
    (λ nths src tgt, RR nths src tgt ∗ wpsim_pre u n ⊤)%I.
  Local Definition wpsim_rel u n (r : rel) : rel :=
    λ R RR ps pt nths '(st_s, i_s) '(st_t, i_t),
      (∃ RR', ⌜ RR = wpsim_retcond u n RR' ⌝ ∧
      wpsim_pre u n ⊤ ∗ r R RR' ps pt nths (st_s, i_s) (st_t, i_t))%I.

  (* Simulation relation that corresponds to iris' weakest precondition *)
  (* TODO : seal *)
  Local Definition wpsim_def r g R RR ps pt nths st_s st_t E : iProp Σ :=
    wpsim_pre u n E -∗
    @isim Σ fl_s fl_t Ist my_tid false (wpsim_rel u n r) (wpsim_rel u n g)
      R (wpsim_retcond u n RR) ps pt nths st_s st_t.
  Local Definition wpsim_aux : seal (@wpsim_def). Proof. by eexists. Qed.
  Definition wpsim := wpsim_aux.(unseal).
  Local Definition wpsim_eq : @wpsim = @wpsim_def := wpsim_aux.(seal_eq).
  Local Ltac unseal := rewrite wpsim_eq /wpsim_def.

  Variant wp_meta {X : nat → Type} : Type :=
  | mk_wp_meta (n : nat) (x : X n).

  Definition wp_fspec (u : positive) (k : nat) (fsp : nat → fspec) : fspec :=
    mk_fspec (meta := @wp_meta (λ n, (fsp n).(meta)))
      (λ tid '(mk_wp_meta n x) varg arg,
        @wpsim_pre u (k + n) ⊤ ∗ (fsp n).(precond) tid x varg arg)%I
      (λ tid '(mk_wp_meta n x) vret ret,
        @wpsim_pre u (k + n) ⊤ ∗ (fsp n).(postcond) tid x vret ret)%I.

  (* Primitive simulation rules *)
  (* Mostly will not be used *)
  Lemma wpsim_ret r g R RR ps pt nths st_s st_t rs rt E :
    RR nths (st_s, rs) (st_t, rt) ⊢ wpsim r g R RR ps pt nths (st_s, Ret rs) (st_t, Ret rt) ⊤.
  Proof. unseal; iIntros "RR I". iApply isim_ret. rewrite /wpsim_retcond; iFrame. Qed.

  Lemma wpim_call r g R RR ps pt nths st_s st_t fn arg k_s k_t E :
    Ist nths st_s st_t ∗
    (∀ ret nths' st_s' st_t'
      (NODS : List.NoDup (List.map fst st_s'))
      (NODD : List.NoDup (List.map fst st_t')),
      Ist nths' st_s' st_t' -∗
      wpsim r g R RR true true nths' (st_s', k_s ret) (st_t', k_t ret) E) ⊢
    wpsim r g R RR ps pt nths
      (st_s, trigger (Call fn arg) >>= k_s) (st_t, trigger (Call fn arg) >>= k_t) E.
  Proof.
    unseal; iIntros "[IST CONT] I".
    rewrite -isim_call; iFrame.
    iIntros (??????) "IST !>"; iApply ("CONT" with "[] [] [IST]"); iFrame; try iPureIntro; ss.
  Qed.

  Lemma wpsim_io r g R RR ps pt nths st_s st_t fn I O (arg : I) k_s k_t E :
    (∀ (ret : O), wpsim r g R RR true true nths (st_s, k_s ret) (st_t, k_t ret) E) ⊢
    wpsim r g R RR ps pt nths
      (st_s, trigger (IO fn arg) >>= k_s)
      (st_t, trigger (IO fn arg) >>= k_t) E.
  Proof. unseal; iIntros "RR I". iApply isim_io. iIntros (ret); iApply "RR"; iFrame. Qed.

  Lemma wpsim_tau_src r g R RR ps pt nths st_s st_t i_s i_t E :
    wpsim r g R RR true pt nths (st_s, i_s) (st_t, i_t) E ⊢
    wpsim r g R RR ps pt nths (st_s, tau;; i_s) (st_t, i_t) E.
  Proof. unseal; iIntros "RR I". iApply isim_tau_src; iApply "RR"; iFrame. Qed.

  Lemma wpsim_tau_tgt r g R RR ps pt nths st_s st_t i_s i_t E :
    wpsim r g R RR ps true nths (st_s, i_s) (st_t, i_t) E ⊢
    wpsim r g R RR ps pt nths (st_s, i_s) (st_t, tau;; i_t) E.
  Proof. unseal; iIntros "RR I". iApply isim_tau_tgt; iApply "RR"; iFrame. Qed.

  Lemma wpsim_inline_src r g R RR ps pt nths st_s st_t fn arg f_s k_s i_t E :
    alist_find fn fl_s = Some f_s →
    wpsim r g R RR true pt nths
      (st_s, x <- (ret <- (f_s arg);; (tau;; tau;; Ret ret));; (k_s x))
      (st_t, i_t) E ⊢
    wpsim r g R RR ps pt nths (st_s, trigger (Call fn arg) >>= k_s) (st_t, i_t) E.
  Proof. i; unseal; iIntros "RR I". iApply isim_inline_src; eauto. iApply "RR"; iFrame. Qed.

  Lemma wpsim_inline_tgt r g R RR ps pt nths st_s st_t fn arg i_s f_t k_t E :
    alist_find fn fl_t = Some f_t →
    wpsim r g R RR ps true nths
      (st_s, i_s)
      (st_t, x <- (ret <- (f_t arg);; (tau;; tau;; Ret ret));; (k_t x)) E ⊢
    wpsim r g R RR ps pt nths (st_s, i_s) (st_t, trigger (Call fn arg) >>= k_t) E.
  Proof. i; unseal; iIntros "RR I". iApply isim_inline_tgt; eauto. iApply "RR"; iFrame. Qed.

  Lemma wpsim_take_src X r g R RR ps pt nths st_s st_t k_s i_t E :
    (∀ x, wpsim r g R RR true pt nths (st_s, k_s x) (st_t, i_t) E) ⊢
    wpsim r g R RR ps pt nths (st_s, trigger (Take X) >>= k_s) (st_t, i_t) E.
  Proof.
    unseal; iIntros "RR I". iApply isim_take_src; eauto. iIntros (x); iApply "RR"; iFrame.
  Qed.

  Lemma wpsim_take_tgt X r g R RR ps pt nths st_s st_t i_s k_t E :
    (∃ x, wpsim r g R RR ps true nths (st_s, i_s) (st_t, k_t x) E) ⊢
    wpsim r g R RR ps pt nths (st_s, i_s) (st_t, trigger (Take X) >>= k_t) E.
  Proof.
    unseal; iIntros "[%x RR] I". iApply isim_take_tgt; eauto. iExists _; iApply "RR"; iFrame.
  Qed.

  Lemma wpsim_choose_src X r g R RR ps pt nths st_s st_t k_s i_t E :
    (∃ x, wpsim r g R RR true pt nths (st_s, k_s x) (st_t, i_t) E) ⊢
    wpsim r g R RR ps pt nths (st_s, trigger (Choose X) >>= k_s) (st_t, i_t) E.
  Proof.
    unseal; iIntros "[%x RR] I". iApply isim_choose_src; eauto. iExists _; iApply "RR"; iFrame.
  Qed.

  Lemma wpsim_choose_tgt X r g R RR ps pt nths st_s st_t i_s k_t E :
    (∀ x, wpsim r g R RR ps true nths (st_s, i_s) (st_t, k_t x) E) ⊢
    wpsim r g R RR ps pt nths (st_s, i_s) (st_t, trigger (Choose X) >>= k_t) E.
  Proof.
    unseal; iIntros "RR I". iApply isim_choose_tgt; eauto. iIntros (x); iApply "RR"; iFrame.
  Qed.

  Lemma wpsim_sput_src k v r g R RR ps pt nths st_s st_t k_s i_t E :
    wpsim r g R RR true pt nths (alist_upd k v st_s, k_s tt) (st_t, i_t) E ⊢
    wpsim r g R RR ps pt nths (st_s, trigger (SPut k v) >>= k_s) (st_t, i_t) E.
  Proof. unseal; iIntros "RR I". iApply isim_sput_src; eauto. iApply "RR"; iFrame. Qed.

  Lemma wpsim_sput_tgt k v r g R RR ps pt nths st_s st_t i_s k_t E :
    wpsim r g R RR ps true nths (st_s, i_s) (alist_upd k v st_t, k_t tt) E ⊢
    wpsim r g R RR ps pt nths (st_s, i_s) (st_t, trigger (SPut k v) >>= k_t) E.
  Proof. unseal; iIntros "RR I". iApply isim_sput_tgt; eauto. iApply "RR"; iFrame. Qed.

  Lemma wpsim_sget_src k r g R RR ps pt nths st_s st_t k_s i_t E :
    wpsim r g R RR true pt nths (st_s, k_s (or_else (alist_find k st_s) tt↑)) (st_t, i_t) E ⊢
    wpsim r g R RR ps pt nths (st_s, trigger (SGet k) >>= k_s) (st_t, i_t) E.
  Proof. unseal; iIntros "RR I". iApply isim_sget_src; eauto. iApply "RR"; iFrame. Qed.

  Lemma wpsim_sget_tgt k r g R RR ps pt nths st_s st_t i_s k_t E :
    wpsim r g R RR ps true nths (st_s, i_s) (st_t, k_t (or_else (alist_find k st_t) tt↑)) E ⊢
    wpsim r g R RR ps pt nths (st_s, i_s) (st_t, trigger (SGet k) >>= k_t) E.
  Proof. unseal; iIntros "RR I". iApply isim_sget_tgt; eauto. iApply "RR"; iFrame. Qed.

  Lemma wpsim_assume_src (P : iProp Σ) r g R RR ps pt nths st_s st_t k_s i_t E :
    (P -∗ wpsim r g R RR true pt nths (st_s, k_s tt) (st_t, i_t) E) ⊢
    wpsim r g R RR ps pt nths (st_s, trigger (Assume P) >>= k_s) (st_t, i_t) E.
  Proof.
    unseal; iIntros "RR I". iApply isim_Assume_src; eauto. iIntros "P".
    iApply ("RR" with "P"); iFrame.
  Qed.

  Lemma wpsim_assume_tgt (P : iProp Σ) r g R RR ps pt nths st_s st_t i_s k_t E :
    P ∗ wpsim r g R RR ps true nths (st_s, i_s) (st_t, k_t tt) E ⊢
    wpsim r g R RR ps pt nths (st_s, i_s) (st_t, trigger (Assume P) >>= k_t) E.
  Proof. unseal; iIntros "[P RR] I". iApply isim_Assume_tgt; eauto. iFrame. iApply "RR". ss. Qed.

  Lemma wpsim_guarantee_src (P : iProp Σ) r g R RR ps pt nths st_s st_t k_s i_t E :
    P ∗ wpsim r g R RR true pt nths (st_s, k_s tt) (st_t, i_t) E ⊢
    wpsim r g R RR ps pt nths (st_s, trigger (Guarantee P) >>= k_s) (st_t, i_t) E.
  Proof. unseal; iIntros "[P RR] I". iApply isim_Guarantee_src; eauto. iFrame. iApply "RR"; ss. Qed.

  Lemma wpsim_guarantee_tgt (P : iProp Σ) r g R RR ps pt nths st_s st_t i_s k_t E :
    P ∗ wpsim r g R RR ps true nths (st_s, i_s) (st_t, k_t tt) E ⊢
    wpsim r g R RR ps pt nths (st_s, i_s) (st_t, trigger (Assume P) >>= k_t) E.
  Proof. unseal; iIntros "[P RR] I". iApply isim_Assume_tgt; eauto. iFrame. iApply "RR". ss. Qed.

  Lemma wpsim_spawn r g R RR ps pt nths st_s st_t fn args k_s k_t E :
    wpsim r g R RR true true (S nths) (st_s, k_s nths) (st_t, k_t nths) E ⊢
    wpsim r g R RR ps pt nths
      (st_s, trigger (Spawn fn args) >>= k_s)
      (st_t, trigger (Spawn fn args) >>= k_t) E.
  Proof. unseal; iIntros "C I". iApply isim_spawn; eauto. iApply "C". ss. Qed.

  Lemma wpsim_yield r g R RR ps pt nths st_s st_t tid k_s k_t E :
    Ist nths st_s st_t ∗
    (∀ nths' st_s' st_t' (NODS : List.NoDup (map fst st_s')) (NODT : List.NoDup (map fst st_t')),
      Ist nths' st_s' st_t' -∗
      wpsim r g R RR true true nths' (st_s', k_s tt) (st_t', k_t tt) E) ⊢
    wpsim r g R RR ps pt nths
      (st_s, trigger (Yield tid) >>= k_s)
      (st_t, trigger (Yield tid) >>= k_t) E.
  Proof.
    unseal; iIntros "[IST C] I". iApply isim_yield; eauto. iFrame.
    iIntros (?????) "IST"; iApply ("C" with "[] [] [IST] [I]"); iFrame; iPureIntro; ss.
  Qed.

  Lemma wpsim_tid_src r g R RR ps pt nths st_s st_t k_s i_t E :
    wpsim r g R RR true pt nths (st_s, k_s my_tid) (st_t, i_t) E ⊢
    wpsim r g R RR ps pt nths (st_s, trigger Tid >>= k_s) (st_t, i_t) E.
  Proof. unseal; iIntros "RR I". iApply isim_tid_src; iApply "RR"; iFrame. Qed.

  Lemma wpsim_tid_tgt r g R RR ps pt nths st_s st_t i_s k_t E :
    wpsim r g R RR ps true nths (st_s, i_s) (st_t, k_t my_tid) E ⊢
    wpsim r g R RR ps pt nths (st_s, i_s) (st_t, trigger Tid >>= k_t) E.
  Proof. unseal; iIntros "RR I". iApply isim_tid_tgt; iApply "RR"; iFrame. Qed.

  Lemma wpsim_progress r g R RR nths st_s st_t i_s i_t E :
    wpsim g g R RR false false nths (st_s, i_s) (st_t, i_t) E ⊢
    wpsim r g R RR true true nths (st_s, i_s) (st_t, i_t) E.
  Proof. unseal; iIntros "RR I". iApply isim_progress; iApply "RR"; iFrame. Qed.

  Lemma wpsim_base r g R RR ps pt nths st_s st_t i_s i_t :
    r R RR ps pt nths (st_s, i_s) (st_t, i_t) ⊢
    wpsim r g R RR ps pt nths (st_s, i_s) (st_t, i_t) ⊤.
  Proof. unseal; iIntros "RR I". iApply isim_base; iFrame. iPureIntro; ss. Qed.

  Lemma wpsim_coind (r g : rel) A P RA RRA psA ptA nthsA srcA tgtA :
    (∀ (g' : rel) (a : A),
      P a -∗
      (□ ∀ R RR ps pt nths0 src tgt, g R RR ps pt nths0 src tgt -∗ g' R RR ps pt nths0 src tgt) -∗
      (□ ∀ a, P a -∗ g' (RA a) (RRA a) (psA a) (ptA a) (nthsA a) (srcA a) (tgtA a)) -∗
      wpsim r g' (RA a) (RRA a) (psA a) (ptA a) (nthsA a) (srcA a) (tgtA a) ⊤) →
    ∀ (a : A), P a ⊢ wpsim r g (RA a) (RRA a) (psA a) (ptA a) (nthsA a) (srcA a) (tgtA a) ⊤.
  Proof.
    unseal; intros H a; iIntros "P I"; iCombine "P I" as "P". iStopProof.
    (* rewrite /wpsim_retcond *)
    revert a. eapply isim_coind.
    intros g' a Himpl; iIntros "[[P I] #CIH]".
    iPoseProof (H with "P [] [] I") as "H".
    { instantiate (1 :=
        (λ R RR ps pt nths '(st_s, i_s) '(st_t, i_t),
          wpsim_pre u n ⊤  -∗ g' R (wpsim_retcond u n RR) ps pt nths (st_s, i_s) (st_t, i_t))%I).
      iModIntro; iIntros (???????) "G"; destruct src, tgt; iIntros "I". iApply Himpl. iFrame.
      iPureIntro; ss.
    }
    { iModIntro; iIntros (a') "P"; iSpecialize ("CIH" $! a'); destruct (srcA a'), (tgtA a').
      iIntros "I"; iApply "CIH"; iFrame.
    }
    iApply (isim_mono_knowledge with "H"); ss.
    { iIntros (???????) "H"; iModIntro; iFrame. }
    { iIntros (???????) "H !>"; destruct sti_src, sti_tgt; rewrite /wpsim_rel.
      iDestruct "H" as (RR') "[-> [H1 H2]]"; iApply "H2"; iFrame.
    }
  Qed.
End wpsim.

(* Section test. *)
  (* Context `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ}. *)
  (* Context (m_s : SMod.t). *)
  (* Context (m_t : HMod.t). *)
  (* Context (ginv : Sk.t → nat → iProp Σ). *)
  (* Context (stb : Sk.t → gname → option fspec). *)
  (* Context (body_s body_t : Any.t → itree hmodE Any.t). *)
  (* Context (fl_s fl_t : alist string (Any.t → itree hmodE Any.t)). *)
  (* Context (my_tid : nat). *)
  (* Context (u : univ_id). *)
  (* Context (k : level). *)
  (* Context (spec_s : nat → fspec). *)

  (* Context (init_cond : Sk.t → iProp Σ). *)
  (* Context (Ist : Sk.t → nat → alist key Any.t → alist key Any.t → iProp Σ). *)
  (* Goal ∀ sk nths st_s st_t RR arg, *)
    (* (∀ n, *)
      (* Ist sk nths st_s st_t ⊢ *)
      (* @wpsim α Σ Γ _ _  β fl_s fl_t (Ist sk) my_tid u n ibot ibot Any.t RR false false nths *)
        (* (st_s, interp_sb_hp (ginv sk) (stb sk) (mk_specbody (spec_s (k + n)) body_s) arg) *)
        (* (st_t, body_t arg) ⊤) → *)
    (* (Ist sk nths st_s st_t ⊢ *)
    (* @isim Σ fl_s fl_t (Ist sk) my_tid false ibot ibot Any.t RR false false nths *)
      (* (st_s, interp_sb_hp (ginv sk) (stb sk) (mk_specbody (wp_fspec u k spec_s) body_s) arg) *)
      (* (st_t, body_t arg)). *)
  (* Proof. *)
    (* rewrite /interp_sb_hp /HoareFun; ss. *)
    (* ii. iIntros "IST". step_l. *)
  (* Admitted. *)
(* End test. *)
(* TODO : proofmode instances *)