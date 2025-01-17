Require Import Common.

Require Import ISim SMod SMod2HMod HMod.
Require Import Skeleton.

From stdpp Require Import coPset.

Definition wpsim_ginv (u : univ_id) (n : level) (E : coPset)
    `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ} : iProp Σ :=
  own_admin ∗ univs u n ∗ wsats u n E.

Section wpsim.
  Context `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ}.

  Local Definition state : Type := alist key Any.t.
  Local Definition post (R_s R_t : Type) : Type := nat → state * R_s → state * R_t → iProp Σ.
  Local Definition rel : Type := ∀ R_s R_t : Type,
    post R_s R_t → bool → bool → nat → state * itree hmodE R_s → state * itree hmodE R_t → iProp Σ.

  Implicit Types r g : rel.
  Implicit Types ps pt : bool.
  Implicit Types nths : nat.
  Implicit Types E : coPset.

  (* TODO : abstraction into mixins *)
  (* TODO : hard-code nodup conditions *)
  (* Local Definition wpsim_pre u n E : iProp Σ := own_admin ∗ univs u n ∗ wsats u n E. *)
  (* Local Definition wpsim_retcond υ n {R_s R_t} (RR : post R_s R_t) : post R_s R_t :=
    (λ nths src tgt, RR nths src tgt ∗ wpsim_ginv υ n ⊤)%I. *)
  Local Definition wpsim_rel υ n (r : rel) : rel :=
    λ R_s R_t RR ps pt nths '(st_s, i_s) '(st_t, i_t),
      (wpsim_ginv υ n ⊤ ∗ r R_s R_t RR ps pt nths (st_s, i_s) (st_t, i_t))%I.

  (* Simulation relation that corresponds to iris' weakest precondition *)
  Local Definition wpsim_def
      fl_s fl_t Ist my_tid (t : option bool) υ ν n E r g R_s R_t RR ps pt nths st_s st_t
      : iProp Σ :=
    (match t with
    | None => emp
    | Some false => wpsim_ginv ν n E -∗ wpsim_ginv υ n E
    | Some true => wpsim_ginv υ n E
    end) -∗
    @isim Σ fl_s fl_t Ist my_tid false (wpsim_rel υ n r) (wpsim_rel υ n g)
      R_s R_t RR ps pt nths st_s st_t.
  Local Definition wpsim_aux : seal (@wpsim_def). Proof. by eexists. Qed.
  Definition wpsim := wpsim_aux.(unseal).
  Local Definition wpsim_eq : @wpsim = @wpsim_def := wpsim_aux.(seal_eq).
  Local Ltac unseal := rewrite wpsim_eq /wpsim_def.

  Variant wp_meta {X : nat → Type} : Type :=
  | mk_wp_meta (n : nat) (x : X n).

  Definition wp_fspec (υ : positive) (k : nat) (fsp : nat → fspec) : fspec :=
    mk_fspec (meta := @wp_meta (λ n, (fsp n).(meta)))
      (λ tid '(mk_wp_meta n x) varg arg,
        wpsim_ginv υ (k + n) ⊤ ∗ (fsp n).(precond) tid x varg arg)%I
      (λ tid '(mk_wp_meta n x) vret ret,
        wpsim_ginv υ (k + n) ⊤ ∗ (fsp n).(postcond) tid x vret ret)%I.

  Section lemmas.
    Context (fl_s fl_t : alist string (Any.t → itree hmodE Any.t)).
    Context (Ist : nat → alist key Any.t → alist key Any.t → iProp Σ).
    Context (my_tid : nat).
    Context (t : option bool).
    Context (υ ν : univ_id).
    Context (n : level).
    Context (R_s R_t : Type).
    Context (RR : post R_s R_t).
    Context (ps pt : bool).
    Context (nths : nat).
    Context (st_s st_t : state).
  
    (* Primitive simulation rules *)
    Lemma wpsim_init sti_s sti_t :
      (wpsim fl_s fl_t Ist my_tid (Some true) υ ν n ⊤ ibot ibot R_s R_t RR ps pt nths sti_s sti_t ∗
      wpsim_ginv υ n ⊤) ⊢
      @isim Σ fl_s fl_t Ist my_tid false ibot ibot R_s R_t RR ps pt nths sti_s sti_t.
    Proof.
      unseal; iIntros "[SIM I]"; iPoseProof ("SIM" with "I") as "SIM".
      iPoseProof (isim_mono_knowledge with "SIM") as "SIM".
      { instantiate (1:=ibot); i; iIntros "H"; rewrite /wpsim_rel /ibot; destruct sti_src, sti_tgt.
        iDestruct "H" as "[_ []]".
      }
      { instantiate (1:=ibot); i; iIntros "H"; rewrite /wpsim_rel /ibot; destruct sti_src, sti_tgt.
        iDestruct "H" as "[_ []]".
      }
      iFrame.
    Qed.

    (* Mostly will not be used *)
    Lemma wpsim_ret r g rs rt :
      RR nths (st_s, rs) (st_t, rt) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n ⊤ r g R_s R_t RR ps pt nths (st_s, Ret rs) (st_t, Ret rt).
    Proof. unseal; iIntros "RR I". iApply isim_ret. iFrame. Qed.

    Lemma wpim_call r g E k_s k_t fn arg :
      Ist nths st_s st_t ∗
      (∀ ret nths' st_s' st_t'
        (NODS : List.NoDup (List.map fst st_s'))
        (NODD : List.NoDup (List.map fst st_t')),
        Ist nths' st_s' st_t' -∗
        wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR true true nths'
          (st_s', k_s ret) (st_t', k_t ret)) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps pt nths
        (st_s, trigger (Call fn arg) >>= k_s) (st_t, trigger (Call fn arg) >>= k_t).
    Proof.
      unseal; iIntros "[IST CONT] I".
      rewrite -isim_call; iFrame.
      iIntros (??????) "IST !>"; iApply ("CONT" with "[] [] [IST]"); iFrame; try iPureIntro; ss.
    Qed.

    Lemma wpsim_io r g fn I O (arg : I) k_s k_t E :
      (∀ (ret : O),
        wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR true true nths
          (st_s, k_s ret) (st_t, k_t ret)) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps pt nths
        (st_s, trigger (IO fn arg) >>= k_s)
        (st_t, trigger (IO fn arg) >>= k_t).
    Proof. unseal; iIntros "RR I". iApply isim_io. iIntros (ret); iApply "RR"; iFrame. Qed.

    Lemma wpsim_tau_src r g i_s i_t E :
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR true pt nths (st_s, i_s) (st_t, i_t) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps pt nths (st_s, tau;; i_s) (st_t, i_t).
    Proof. unseal; iIntros "RR I". iApply isim_tau_src; iApply "RR"; iFrame. Qed.

    Lemma wpsim_tau_tgt r g i_s i_t E :
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps true nths (st_s, i_s) (st_t, i_t) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps pt nths (st_s, i_s) (st_t, tau;; i_t).
    Proof. unseal; iIntros "RR I". iApply isim_tau_tgt; iApply "RR"; iFrame. Qed.

    Lemma wpsim_inline_src r g fn arg f_s k_s i_t E :
      alist_find fn fl_s = Some f_s →
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR true pt nths
        (st_s, x <- (ret <- (f_s arg);; (tau;; tau;; Ret ret));; (k_s x))
        (st_t, i_t) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps pt nths
        (st_s, trigger (Call fn arg) >>= k_s) (st_t, i_t).
    Proof. i; unseal; iIntros "RR I". iApply isim_inline_src; eauto. iApply "RR"; iFrame. Qed.

    Lemma wpsim_inline_tgt r g fn arg i_s f_t k_t E :
      alist_find fn fl_t = Some f_t →
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps true nths
        (st_s, i_s)
        (st_t, x <- (ret <- (f_t arg);; (tau;; tau;; Ret ret));; (k_t x)) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, trigger (Call fn arg) >>= k_t).
    Proof. i; unseal; iIntros "RR I". iApply isim_inline_tgt; eauto. iApply "RR"; iFrame. Qed.

    Lemma wpsim_take_src X r g k_s i_t E :
      (∀ x, wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR true pt nths
        (st_s, k_s x) (st_t, i_t)) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps pt nths
        (st_s, trigger (Take X) >>= k_s) (st_t, i_t).
    Proof.
      unseal; iIntros "RR I". iApply isim_take_src; eauto. iIntros (x); iApply "RR"; iFrame.
    Qed.

    Lemma wpsim_take_tgt X r g i_s k_t E :
      (∃ x,
        wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps true nths (st_s, i_s) (st_t, k_t x)) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, trigger (Take X) >>= k_t).
    Proof.
      unseal; iIntros "[%x RR] I". iApply isim_take_tgt; eauto. iExists _; iApply "RR"; iFrame.
    Qed.

    Lemma wpsim_choose_src X r g k_s i_t E :
      (∃ x,
        wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR true pt nths (st_s, k_s x) (st_t, i_t)) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps pt nths
        (st_s, trigger (Choose X) >>= k_s) (st_t, i_t).
    Proof.
      unseal; iIntros "[%x RR] I". iApply isim_choose_src; eauto. iExists _; iApply "RR"; iFrame.
    Qed.

    Lemma wpsim_choose_tgt X r g i_s k_t E :
      (∀ x,
        wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps true nths (st_s, i_s) (st_t, k_t x)) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, trigger (Choose X) >>= k_t).
    Proof.
      unseal; iIntros "RR I". iApply isim_choose_tgt; eauto. iIntros (x); iApply "RR"; iFrame.
    Qed.

    Lemma wpsim_sput_src k v r g k_s i_t E :
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR true pt nths
        (alist_upd k v st_s, k_s tt) (st_t, i_t) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps pt nths
        (st_s, trigger (SPut k v) >>= k_s) (st_t, i_t).
    Proof. unseal; iIntros "RR I". iApply isim_sput_src; eauto. iApply "RR"; iFrame. Qed.

    Lemma wpsim_sput_tgt k v r g i_s k_t E :
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps true nths
        (st_s, i_s) (alist_upd k v st_t, k_t tt) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, trigger (SPut k v) >>= k_t).
    Proof. unseal; iIntros "RR I". iApply isim_sput_tgt; eauto. iApply "RR"; iFrame. Qed.

    Lemma wpsim_sget_src k r g k_s i_t E :
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR true pt nths
        (st_s, k_s (or_else (alist_find k st_s) tt↑)) (st_t, i_t) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps pt nths
        (st_s, trigger (SGet k) >>= k_s) (st_t, i_t).
    Proof. unseal; iIntros "RR I". iApply isim_sget_src; eauto. iApply "RR"; iFrame. Qed.

    Lemma wpsim_sget_tgt k r g i_s k_t E :
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps true nths
        (st_s, i_s) (st_t, k_t (or_else (alist_find k st_t) tt↑)) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, trigger (SGet k) >>= k_t).
    Proof. unseal; iIntros "RR I". iApply isim_sget_tgt; eauto. iApply "RR"; iFrame. Qed.

    Lemma wpsim_assume_src (P : iProp Σ) r g k_s i_t E :
      (P -∗ wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR true pt nths
        (st_s, k_s tt) (st_t, i_t)) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps pt nths
        (st_s, trigger (Assume P) >>= k_s) (st_t, i_t).
    Proof.
      unseal; iIntros "RR I". iApply isim_Assume_src; eauto. iIntros "P".
      iApply ("RR" with "P"); iFrame.
    Qed.

    Lemma wpsim_assume_tgt (P : iProp Σ) r g i_s k_t E :
      P ∗ wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps true nths
        (st_s, i_s) (st_t, k_t tt) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, trigger (Assume P) >>= k_t).
    Proof. unseal; iIntros "[P RR] I". iApply isim_Assume_tgt; eauto. iFrame. iApply "RR". ss. Qed.

    Lemma wpsim_guarantee_src (P : iProp Σ) r g k_s i_t E :
      P ∗ wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR true pt nths
        (st_s, k_s tt) (st_t, i_t) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps pt nths
        (st_s, trigger (Guarantee P) >>= k_s) (st_t, i_t).
    Proof.
      unseal; iIntros "[P RR] I". iApply isim_Guarantee_src; eauto. iFrame. iApply "RR"; ss.
    Qed.

    Lemma wpsim_guarantee_tgt (P : iProp Σ) r g i_s k_t E :
      P ∗ wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps true nths
        (st_s, i_s) (st_t, k_t tt) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, trigger (Assume P) >>= k_t).
    Proof. unseal; iIntros "[P RR] I". iApply isim_Assume_tgt; eauto. iFrame. iApply "RR". ss. Qed.

    Lemma wpsim_spawn r g fn args k_s k_t E :
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR true true (S nths)
        (st_s, k_s nths) (st_t, k_t nths) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps pt nths
        (st_s, trigger (Spawn fn args) >>= k_s)
        (st_t, trigger (Spawn fn args) >>= k_t).
    Proof. unseal; iIntros "C I". iApply isim_spawn; eauto. iApply "C". ss. Qed.

    Lemma wpsim_yield r g tid k_s k_t E :
      Ist nths st_s st_t ∗
      (∀ nths' st_s' st_t' (NODS : List.NoDup (map fst st_s')) (NODT : List.NoDup (map fst st_t')),
        Ist nths' st_s' st_t' -∗
        wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR true true nths'
          (st_s', k_s tt) (st_t', k_t tt)) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps pt nths
        (st_s, trigger (Yield tid) >>= k_s)
        (st_t, trigger (Yield tid) >>= k_t).
    Proof.
      unseal; iIntros "[IST C] I". iApply isim_yield; eauto. iFrame.
      iIntros (?????) "IST"; iApply ("C" with "[] [] [IST] [I]"); iFrame; iPureIntro; ss.
    Qed.

    Lemma wpsim_tid_src r g k_s i_t E :
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR true pt nths
        (st_s, k_s my_tid) (st_t, i_t) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps pt nths
        (st_s, trigger Tid >>= k_s) (st_t, i_t).
    Proof. unseal; iIntros "RR I". iApply isim_tid_src; iApply "RR"; iFrame. Qed.

    Lemma wpsim_tid_tgt r g i_s k_t E :
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps true nths
        (st_s, i_s) (st_t, k_t my_tid) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, trigger Tid >>= k_t).
    Proof. unseal; iIntros "RR I". iApply isim_tid_tgt; iApply "RR"; iFrame. Qed.

    Lemma wpsim_progress r g i_s i_t E :
      wpsim fl_s fl_t Ist my_tid t υ ν n E g g R_s R_t RR false false nths (st_s, i_s) (st_t, i_t) ⊢
      wpsim fl_s fl_t Ist my_tid t υ ν n E r g R_s R_t RR true true nths (st_s, i_s) (st_t, i_t).
    Proof. unseal; iIntros "RR I". iApply isim_progress; iApply "RR"; iFrame. Qed.

    Lemma wpsim_base r g i_s i_t :
      r R_s R_t RR ps pt nths (st_s, i_s) (st_t, i_t) ⊢
      wpsim fl_s fl_t Ist my_tid (Some true) υ ν n ⊤ r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, i_t).
    Proof. unseal; iIntros "RR I". iApply isim_base; iFrame. Qed.

    Lemma wpsim_coind (r g : rel) A P RA_s RA_t RRA psA ptA nthsA srcA tgtA :
      (∀ (g' : rel) (a : A),
        P a -∗
        (□ ∀ R_s R_t RR ps pt nths0 src tgt,
          g R_s R_t RR ps pt nths0 src tgt -∗ g' R_s R_t RR ps pt nths0 src tgt) -∗
        (□ ∀ a, P a -∗ g' (RA_s a) (RA_t a) (RRA a) (psA a) (ptA a) (nthsA a) (srcA a) (tgtA a)) -∗
        wpsim fl_s fl_t Ist my_tid (Some true) υ ν n ⊤ r g'
          (RA_s a) (RA_t a) (RRA a) (psA a) (ptA a) (nthsA a) (srcA a) (tgtA a)) →
      ∀ (a : A), P a ⊢
        wpsim fl_s fl_t Ist my_tid (Some true) υ ν n ⊤ r g
          (RA_s a) (RA_t a) (RRA a) (psA a) (ptA a) (nthsA a) (srcA a) (tgtA a).
    Proof.
      unseal; intros H a; iIntros "P I"; iCombine "P I" as "P". iStopProof.
      (* rewrite /wpsim_retcond *)
      revert a. eapply isim_coind.
      intros g' a Himpl; iIntros "[[P I] #CIH]".
      iPoseProof (H with "P [] [] I") as "H".
      { instantiate (1 :=
          (λ R_s R_t RR ps pt nths '(st_s, i_s) '(st_t, i_t),
            wpsim_ginv υ n ⊤ -∗
            g' R_s R_t RR ps pt nths (st_s, i_s) (st_t, i_t))%I).
        iModIntro; iIntros (????????) "G"; destruct src, tgt; iIntros "I". iApply Himpl. iFrame.
      }
      { iModIntro; iIntros (a') "P"; iSpecialize ("CIH" $! a'); destruct (srcA a'), (tgtA a').
        iIntros "I"; iApply "CIH"; iFrame.
      }
      iApply (isim_mono_knowledge with "H"); ss.
      { iIntros (????????) "H"; iModIntro; iFrame. }
      { iIntros (????????) "H !>"; destruct sti_src, sti_tgt; rewrite /wpsim_rel.
        iDestruct "H" as "[H1 H2]"; iApply "H2"; iFrame.
      }
    Qed.

    (* ginv related lemmas *)
    Lemma wpsim_full_guarantee_src (P : iProp Σ) r g k_s i_t E :
      ((wpsim_ginv υ n E -∗ P) ∗
      wpsim fl_s fl_t Ist my_tid None υ ν n E r g R_s R_t RR true pt nths
        (st_s, k_s tt) (st_t, i_t)) ⊢
      wpsim fl_s fl_t Ist my_tid (Some true) υ ν n E r g R_s R_t RR ps pt nths
        (st_s, trigger (Guarantee P) >>= k_s) (st_t, i_t).
    Proof.
      unseal; iIntros "[P SIM] I". iApply isim_Guarantee_src; eauto.
      iSplitR "SIM"; iFrame. iApply "P"; iFrame. iApply "SIM"; done.
    Qed.
End lemmas. End wpsim.

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