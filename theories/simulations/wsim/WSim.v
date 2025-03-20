Require Import Common.

Require Import ISim SMod SMod2HMod HMod.

From stdpp Require Import coPset.

Definition wsim_ginv (u : univ_id) (E : coPset)
    `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ} : iProp Σ :=
  own_admin ∗ (∃ n, univs u n) ∗ (∃ n, wsats u n E).

Lemma wsim_ginv_split (υ ν : univ_id) (E : coPset)
    `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ} :
  (ν < υ) →
  wsim_ginv υ E
  ==∗ wsim_ginv ν ⊤ ∗ own_admin ∗ (∃ n, wsats υ n E) ∗ (wsim_ginv ν ⊤ ==∗ ∃ n, univs υ n).
Proof.
  iIntros "%LT [O [[%vn U] [%un W]]]".
  rewrite {1 2}/univs; replace υ with (ν + (S (υ - S ν))) by lia.
  rewrite ?seq_app /= ?big_sepL_app /=. iDestruct "U" as "[U1 [U2 U3]]".
  iMod (own_admin_split with "O") as "[O1 O2]".
  iSplitL "U1 U2 O2"; iFrame; ss.
  iIntros "!> [_ [[%n U] [%n' W]]]".
  remember ((n `max` n') `max` vn) as n''. iExists n''.
  iPoseProof (univs_mon ν n n'' with "U") as "> U"; first lia.
  iPoseProof (wsats_mon ν n' n'' with "W") as "> W"; first lia.
  iFrame. iApply big_sepL_bupd. iApply (big_sepL_impl with "U3").
  iModIntro; iIntros "%k %x %IN W"; iApply wsats_mon; last iFrame; lia.
Qed.

Class WP `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ} 
    (P : iProp Σ) (υ : univ_id) (E : coPset) := mk_WP {
  WP_remainder : iProp Σ;
  WP_iff : P ∗-∗ wsim_ginv υ E ∗ WP_remainder
}.
Arguments mk_WP {_ _ _ _ _ _ _ _} _ _ _ _ _.
Arguments WP_remainder {_ _ _ _ _ _ _ _} [_ _ _] _.
Arguments WP_iff {_ _ _ _ _ _ _ _} [_ _ _] _.

Program Global Instance WP_refl `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}
    (υ : univ_id) (E : coPset)
  : WP (wsim_ginv υ E) υ E := mk_WP (wsim_ginv υ E) υ E True _.
Next Obligation. ii; iSplit; first iIntros "$"; iIntros "[$ _]". Qed.

Section wsim.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.

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
  Local Definition wsim_pre t υ ν E : iProp Σ :=
    match t with
    | None => True
    | Some false => own_admin ∗ (∃ n, wsats υ n E) ∗ (wsim_ginv ν ⊤ ==∗ ∃ n, univs υ n)
    | Some true => wsim_ginv υ E
    end.

  Definition wsim_rel t υ ν E (r : rel) : rel :=
    λ R_s R_t RR ps pt nths '(st_s, i_s) '(st_t, i_t),
      (wsim_pre t υ ν E ∗ r R_s R_t RR ps pt nths (st_s, i_s) (st_t, i_t))%I.

  (* Simulation relation that corresponds to iris' weakest precondition *)
  Local Definition wsim_def
      fl_s fl_t Ist (t : option bool) υ ν E r g R_s R_t RR ps pt nths st_s st_t
      : iProp Σ :=
    wsim_pre t υ ν E -∗
    @isim Σ open fl_s fl_t Ist r g R_s R_t RR ps pt nths st_s st_t.
  Local Definition wsim_aux : seal (@wsim_def). Proof. by eexists. Qed.
  Definition wsim := wsim_aux.(unseal).
  Local Definition wsim_eq : @wsim = @wsim_def := wsim_aux.(seal_eq).
  Local Ltac unseal := rewrite wsim_eq /wsim_def.

  Definition w_fspec (υ : univ_id) (fsp : fspec) : fspec :=
    mk_fspec (meta := fsp.(meta))
      (λ x varg arg, wsim_ginv υ ⊤ ∗ fsp.(precond) x varg arg)%I
      (λ x vret ret, wsim_ginv υ ⊤ ∗ fsp.(postcond) x vret ret)%I.
  
  Program Global Instance wsim_fspec_precond (fsp : fspec) (υ : univ_id) m arg varg :
    WP (precond (w_fspec υ fsp) m arg varg) υ ⊤ :=
    mk_WP (precond (w_fspec υ fsp) m arg varg) υ ⊤ (precond fsp m arg varg) _.
  Next Obligation. intros; iSplit; iIntros "[$ $]". Qed.

  Program Global Instance wsim_fspec_postcond (fsp : fspec) (υ : univ_id) m arg varg :
    WP (postcond (w_fspec υ fsp) m arg varg) υ ⊤ :=
    {| WP_remainder := (postcond fsp m arg varg) |}.
  Next Obligation. intros; iSplit; iIntros "[$ $]". Qed.

  Lemma wsim_own_alloc `{!inG A Σ} (a : A) (VAL : ✓ a)
    fl_s fl_t Ist b υ ν R_s R_t RR ps pt nths r g E st_s st_t i_s i_t :
    ((∃ γ, own γ a) -∗ wsim fl_s fl_t Ist (Some b) υ ν E r g R_s R_t RR ps pt nths (st_s, i_s) (st_t, i_t))
    ⊢ wsim fl_s fl_t Ist (Some b) υ ν E r g R_s R_t RR ps pt nths (st_s, i_s) (st_t, i_t).
  Proof.
    destruct b; unseal; iIntros "SIM [O PRE]"; iMod (own_alloc a with "O") as "[O o]"; ss.
    all: iApply ("SIM" with "o"); iFrame.
  Qed.

  Section lemmas.
    Context (fl_s fl_t : alist string (Any.t → itree hmodE Any.t)).
    Context (Ist : nat → alist key Any.t → alist key Any.t → iProp Σ).

    Local Notation wsim := (wsim fl_s fl_t Ist).

    Context (t : option bool).
    Context (υ ν : univ_id).
    Context (R_s R_t : Type).
    Context (RR : post R_s R_t).
    Context (ps pt : bool).
    Context (nths : nat).
    Context (st_s st_t : state).
    
    Lemma wsim_ret r g rs rt :
      RR nths (st_s, rs) (st_t, rt) ⊢
      wsim t υ ν ⊤ r g R_s R_t RR ps pt nths (st_s, Ret rs) (st_t, Ret rt).
    Proof. unseal; iIntros "RR I". iApply isim_ret. iFrame. Qed.

    Lemma wsim_call r g E k_s k_t fn arg :
      Ist nths st_s st_t ∗
      (∀ ret nths' st_s' st_t'
        (NODS : List.NoDup (List.map fst st_s'))
        (NODD : List.NoDup (List.map fst st_t')),
        Ist nths' st_s' st_t' -∗
        wsim t υ ν E r g R_s R_t RR true true nths' (st_s', k_s ret) (st_t', k_t ret)) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, trigger (Call fn arg) >>= k_s) (st_t, trigger (Call fn arg) >>= k_t).
    Proof.
      unseal; iIntros "[IST CONT] I".
      rewrite -isim_call; iFrame.
      iIntros (??????) "IST"; iApply ("CONT" with "[] [] [IST]"); iFrame; try iPureIntro; ss.
    Qed.

    Lemma wsim_io r g fn I O (arg : I) k_s k_t E :
      (∀ (ret : O),
        wsim t υ ν E r g R_s R_t RR true true nths (st_s, k_s ret) (st_t, k_t ret)) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, trigger (IO fn arg) >>= k_s)
        (st_t, trigger (IO fn arg) >>= k_t).
    Proof. unseal; iIntros "RR I". iApply isim_io. iIntros (ret); iApply "RR"; iFrame. Qed.

    Lemma wsim_tau_src r g i_s i_t E :
      wsim t υ ν E r g R_s R_t RR true pt nths (st_s, i_s) (st_t, i_t) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths (st_s, tau;; i_s) (st_t, i_t).
    Proof. unseal; iIntros "RR I". iApply isim_tau_src; iApply "RR"; iFrame. Qed.

    Lemma wsim_tau_tgt r g i_s i_t E :
      wsim t υ ν E r g R_s R_t RR ps true nths (st_s, i_s) (st_t, i_t) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths (st_s, i_s) (st_t, tau;; i_t).
    Proof. unseal; iIntros "RR I". iApply isim_tau_tgt; iApply "RR"; iFrame. Qed.

    Lemma wsim_inline_src r g fn arg f_s k_s i_t E :
      alist_find fn fl_s = Some f_s →
      wsim t υ ν E r g R_s R_t RR true pt nths
        (st_s, x <- (ret <- (f_s arg);; (tau;; tau;; Ret ret));; (k_s x))
        (st_t, i_t) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths (st_s, trigger (Call fn arg) >>= k_s) (st_t, i_t).
    Proof. i; unseal; iIntros "RR I". iApply isim_inline_src; eauto. iApply "RR"; iFrame. Qed.

    Lemma wsim_inline_tgt r g fn arg i_s f_t k_t E :
      alist_find fn fl_t = Some f_t →
      wsim t υ ν E r g R_s R_t RR ps true nths
        (st_s, i_s)
        (st_t, x <- (ret <- (f_t arg);; (tau;; tau;; Ret ret));; (k_t x)) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths (st_s, i_s) (st_t, trigger (Call fn arg) >>= k_t).
    Proof. i; unseal; iIntros "RR I". iApply isim_inline_tgt; eauto. iApply "RR"; iFrame. Qed.

    Lemma wsim_take_src X r g k_s i_t E :
      (∀ x, wsim t υ ν E r g R_s R_t RR true pt nths
        (st_s, k_s x) (st_t, i_t)) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, trigger (Take X) >>= k_s) (st_t, i_t).
    Proof.
      unseal; iIntros "RR I". iApply isim_take_src; eauto. iIntros (x); iApply "RR"; iFrame.
    Qed.

    Lemma wsim_take_tgt X r g i_s k_t E :
      (∃ x,
        wsim t υ ν E r g R_s R_t RR ps true nths (st_s, i_s) (st_t, k_t x)) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, trigger (Take X) >>= k_t).
    Proof.
      unseal; iIntros "[%x RR] I". iApply isim_take_tgt; eauto. iExists _; iApply "RR"; iFrame.
    Qed.

    Lemma wsim_choose_src X r g k_s i_t E :
      (∃ x,
        wsim t υ ν E r g R_s R_t RR true pt nths (st_s, k_s x) (st_t, i_t)) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, trigger (Choose X) >>= k_s) (st_t, i_t).
    Proof.
      unseal; iIntros "[%x RR] I". iApply isim_choose_src; eauto. iExists _; iApply "RR"; iFrame.
    Qed.

    Lemma wsim_choose_tgt X r g i_s k_t E :
      (∀ x,
        wsim t υ ν E r g R_s R_t RR ps true nths (st_s, i_s) (st_t, k_t x)) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, trigger (Choose X) >>= k_t).
    Proof.
      unseal; iIntros "RR I". iApply isim_choose_tgt; eauto. iIntros (x); iApply "RR"; iFrame.
    Qed.

    Lemma wsim_sput_src k v r g k_s i_t E :
      wsim t υ ν E r g R_s R_t RR true pt nths
        (alist_upd k v st_s, k_s tt) (st_t, i_t) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, trigger (SPut k v) >>= k_s) (st_t, i_t).
    Proof. unseal; iIntros "RR I". iApply isim_sput_src; eauto. iApply "RR"; iFrame. Qed.

    Lemma wsim_sput_tgt k v r g i_s k_t E :
      wsim t υ ν E r g R_s R_t RR ps true nths
        (st_s, i_s) (alist_upd k v st_t, k_t tt) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, trigger (SPut k v) >>= k_t).
    Proof. unseal; iIntros "RR I". iApply isim_sput_tgt; eauto. iApply "RR"; iFrame. Qed.

    Lemma wsim_sget_src k r g k_s i_t E :
      wsim t υ ν E r g R_s R_t RR true pt nths
        (st_s, k_s (or_else (alist_find k st_s) tt↑)) (st_t, i_t) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, trigger (SGet k) >>= k_s) (st_t, i_t).
    Proof. unseal; iIntros "RR I". iApply isim_sget_src; eauto. iApply "RR"; iFrame. Qed.

    Lemma wsim_sget_tgt k r g i_s k_t E :
      wsim t υ ν E r g R_s R_t RR ps true nths
        (st_s, i_s) (st_t, k_t (or_else (alist_find k st_t) tt↑)) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, trigger (SGet k) >>= k_t).
    Proof. unseal; iIntros "RR I". iApply isim_sget_tgt; eauto. iApply "RR"; iFrame. Qed.

    Lemma wsim_assume_src (P : iProp Σ) r g k_s i_t E :
      (P -∗ wsim t υ ν E r g R_s R_t RR true pt nths
        (st_s, k_s tt) (st_t, i_t)) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, trigger (Assume P) >>= k_s) (st_t, i_t).
    Proof.
      unseal; iIntros "RR I". iApply isim_Assume_src; eauto. iIntros "P".
      iApply ("RR" with "P"); iFrame.
    Qed.

    Lemma wsim_assume_tgt (P : iProp Σ) r g i_s k_t E :
      P ∗ wsim t υ ν E r g R_s R_t RR ps true nths
        (st_s, i_s) (st_t, k_t tt) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, trigger (Assume P) >>= k_t).
    Proof. unseal; iIntros "[P RR] I". iApply isim_Assume_tgt; eauto. iFrame. iApply "RR". ss. Qed.

    Lemma wsim_guarantee_src (P : iProp Σ) r g k_s i_t E :
      P ∗ wsim t υ ν E r g R_s R_t RR true pt nths
        (st_s, k_s tt) (st_t, i_t) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, trigger (Guarantee P) >>= k_s) (st_t, i_t).
    Proof.
      unseal; iIntros "[P RR] I". iApply isim_Guarantee_src; eauto. iFrame. iApply "RR"; ss.
    Qed.

    Lemma wsim_guarantee_tgt (P : iProp Σ) r g i_s k_t E :
      (P -∗ wsim t υ ν E r g R_s R_t RR ps true nths
        (st_s, i_s) (st_t, k_t tt)) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, trigger (Guarantee P) >>= k_t).
    Proof.
      unseal; iIntros "RR I". iApply isim_Guarantee_tgt; eauto.
      iIntros "P"; iApply ("RR" with "P"); done.
    Qed.

    Lemma wsim_spawn r g fn args k_s k_t E :
      wsim t υ ν E r g R_s R_t RR true true (S nths)
        (st_s, k_s nths) (st_t, k_t nths) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, trigger (Spawn fn args) >>= k_s)
        (st_t, trigger (Spawn fn args) >>= k_t).
    Proof. unseal; iIntros "C I". iApply isim_spawn; eauto. iApply "C". ss. Qed.

    Lemma wsim_yield r g tid k_s k_t E :
      Ist nths st_s st_t ∗
      (∀ nths' st_s' st_t' (NODS : List.NoDup (map fst st_s')) (NODT : List.NoDup (map fst st_t')),
        Ist nths' st_s' st_t' -∗
        wsim t υ ν E r g R_s R_t RR true true nths'
          (st_s', k_s tt) (st_t', k_t tt)) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, trigger (Yield tid) >>= k_s)
        (st_t, trigger (Yield tid) >>= k_t).
    Proof.
      unseal; iIntros "[IST C] I". iApply isim_yield; eauto. iFrame.
      iIntros (?????) "IST"; iApply ("C" with "[] [] [IST] [I]"); iFrame; iPureIntro; ss.
    Qed.

    Lemma wsim_reset r g i_s i_t E :
      wsim t υ ν E r g R_s R_t RR false false nths (st_s, i_s) (st_t, i_t) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths (st_s, i_s) (st_t, i_t).
    Proof. unseal; iIntros "RR I". iApply isim_reset; iApply "RR"; iFrame. Qed.

    Lemma wsim_progress r g i_s i_t E :
      wsim t υ ν E g g R_s R_t RR false false nths (st_s, i_s) (st_t, i_t) ⊢
      wsim t υ ν E r g R_s R_t RR true true nths (st_s, i_s) (st_t, i_t).
    Proof. unseal; iIntros "RR I". iApply isim_progress; iApply "RR"; iFrame. Qed.

    (* Lemma wsim_base r g i_s i_t :
      r R_s R_t RR ps pt nths (st_s, i_s) (st_t, i_t) ⊢
      wsim t υ ν ⊤ r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, i_t).
    Proof. unseal; iIntros "RR I". iApply isim_base; iFrame. Qed. *)

    Lemma wsim_base_t r g i_s i_t :
      (wsim_pre t υ ν ⊤ -∗ r R_s R_t RR ps pt nths (st_s, i_s) (st_t, i_t)) ⊢
      wsim t υ ν ⊤ r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, i_t).
    Proof. unseal; iIntros "RR I". iApply isim_base; iRevert "I"; iFrame. Qed.

    Lemma wsim_coind (r g : rel) A P RA_s RA_t RRA psA ptA nthsA srcA tgtA :
      (∀ (g' : rel) (a : A),
        P a -∗
        (⌜∀ R_s R_t RR ps pt nths0 src tgt,
          g R_s R_t RR ps pt nths0 src tgt -∗ g' R_s R_t RR ps pt nths0 src tgt⌝) -∗
        (□ ∀ a, (P a ∗ wsim_pre t υ ν ⊤) -∗
          g' (RA_s a) (RA_t a) (RRA a) (psA a) (ptA a) (nthsA a) (srcA a) (tgtA a)) -∗
        wsim t υ ν ⊤ r g'
          (RA_s a) (RA_t a) (RRA a) (psA a) (ptA a) (nthsA a) (srcA a) (tgtA a)) →
      ∀ (a : A), P a ⊢
        wsim t υ ν ⊤ r g (RA_s a) (RA_t a) (RRA a) (psA a) (ptA a) (nthsA a) (srcA a) (tgtA a).
    Proof.
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

    Lemma wsim_bind r g {Qs Qt} QQ i_s i_t k_s k_t E :
      wsim t υ ν E r g Qs Qt QQ ps pt nths (st_s, i_s) (st_t, i_t)
      ∗ (∀ nths st_s' r_s st_t' r_t,
          QQ nths (st_s', r_s) (st_t', r_t)
          -∗ wsim None υ ν E r g R_s R_t RR false false nths (st_s', k_s r_s) (st_t', k_t r_t))%I
      ⊢ (wsim t υ ν E r g R_s R_t RR ps pt nths (st_s, i_s >>= k_s) (st_t, i_t >>= k_t)).
    Proof.
      rewrite wsim.wsim_eq /wsim.wsim_def /wsim.wsim_pre.
      iIntros "[W SIM] INV". iApply isim_bind.
      iSplitL "W INV". { iApply "W"; eauto. }
      iIntros (? ? ? ? ?) "Q". iApply ("SIM" with "Q"). done.
    Qed.

    (* ginv related lemmas *)
    Lemma wsim_full_guarantee_src_WP `{i : !WP P υ E} r g k_s i_t :
      (WP_remainder i ∗
      wsim None υ ν E r g R_s R_t RR true pt nths (st_s, k_s tt) (st_t, i_t)) ⊢
      wsim (Some true) υ ν E r g R_s R_t RR ps pt nths
        (st_s, trigger (Guarantee P) >>= k_s) (st_t, i_t).
    Proof.
      unseal; iIntros "[P SIM] I". iApply isim_Guarantee_src; eauto.
      iSplitR "SIM".
      { iApply WP_iff; iFrame. }
      { iApply "SIM"; done. }
    Qed.

    Lemma wsim_full_guarantee_src_upd (P : iProp Σ) r g k_s i_t E :
      ((wsim_ginv υ E ==∗ P) ∗
      wsim None υ ν E r g R_s R_t RR true pt nths
        (st_s, k_s tt) (st_t, i_t)) ⊢
      wsim (Some true) υ ν E r g R_s R_t RR ps pt nths
        (st_s, trigger (Guarantee P) >>= k_s) (st_t, i_t).
    Proof.
      unseal; iIntros "[P SIM] I".
      iPoseProof ("P" with "I") as ">P".
      iApply isim_Guarantee_src; eauto.
      iSplitR "SIM"; iFrame. iApply "SIM"; done.
    Qed.

    Lemma wsim_full_guarantee_src (P : iProp Σ) r g k_s i_t E :
      ((wsim_ginv υ E -∗ P) ∗
      wsim None υ ν E r g R_s R_t RR true pt nths
        (st_s, k_s tt) (st_t, i_t)) ⊢
      wsim (Some true) υ ν E r g R_s R_t RR ps pt nths
        (st_s, trigger (Guarantee P) >>= k_s) (st_t, i_t).
    Proof.
      unseal; iIntros "[P SIM] I". iApply isim_Guarantee_src; eauto.
      iSplitR "SIM"; iFrame. iApply "P"; iFrame. iApply "SIM"; done.
    Qed.

    Lemma wsim_full_assume_src_WP `{i : !WP P υ E} r g k_s i_t :
      (WP_remainder i -∗ wsim (Some true) υ ν E r g R_s R_t RR true pt nths
        (st_s, k_s tt) (st_t, i_t)) ⊢
      wsim None υ ν E r g R_s R_t RR ps pt nths
        (st_s, trigger (Assume P) >>= k_s) (st_t, i_t).
    Proof.
      unseal; iIntros "SIM _". iApply isim_Assume_src; eauto.
      iIntros "P". iPoseProof (WP_iff with "P") as "[I Q]".
      iApply ("SIM" with "Q I").
    Qed.

    Lemma wsim_full_assume_src (P P' : iProp Σ) r g k_s i_t E :
      ((P -∗ (wsim_ginv υ E ∗ P')) ∗
      (P' -∗ wsim (Some true) υ ν E r g R_s R_t RR true pt nths
        (st_s, k_s tt) (st_t, i_t))) ⊢
      wsim None υ ν E r g R_s R_t RR ps pt nths
        (st_s, trigger (Assume P) >>= k_s) (st_t, i_t).
    Proof.
      unseal; iIntros "[P SIM] I". iApply isim_Assume_src; eauto.
      iIntros "P'". iPoseProof ("P" with "P'") as "[GINV P]".
      iApply ("SIM" with "P GINV").
    Qed.

    Lemma wsim_full_assume_src_upd (P P' : iProp Σ) r g k_s i_t E :
      ((P ==∗ (wsim_ginv υ E ∗ P')) ∗
      (P' ==∗ wsim (Some true) υ ν E r g R_s R_t RR true pt nths
        (st_s, k_s tt) (st_t, i_t))) ⊢
      wsim None υ ν E r g R_s R_t RR ps pt nths
        (st_s, trigger (Assume P) >>= k_s) (st_t, i_t).
    Proof.
      unseal; iIntros "[P SIM] I". iApply isim_Assume_src; eauto.
      iIntros "P'". iPoseProof ("P" with "P'") as ">[GINV P]".
      iPoseProof ("SIM" with "P") as ">SIM".
      iApply ("SIM" with "GINV").
    Qed.

    Lemma wsim_full_assume_tgt_WP `{i : !WP P υ E} r g i_s k_t :
      (WP_remainder i ∗
      wsim None υ ν E r g R_s R_t RR ps true nths
        (st_s, i_s) (st_t, k_t tt)) ⊢
      wsim (Some true) υ ν E r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, trigger (Assume P) >>= k_t).
    Proof.
      unseal; iIntros "[P SIM] I". iApply isim_Assume_tgt; eauto.
      iSplitR "SIM"; iFrame.
      { iApply WP_iff; iFrame. }
      { iApply "SIM"; done. }
    Qed.

    Lemma wsim_full_guarantee_tgt_WP `{i : !WP P υ E} r g i_s k_t :
      (WP_remainder i -∗
      wsim (Some true) υ ν E r g R_s R_t RR ps true nths
        (st_s, i_s) (st_t, k_t tt)) ⊢
      wsim None υ ν E r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, trigger (Guarantee P) >>= k_t).
    Proof.
      unseal. iIntros "SIM I".
      iApply isim_Guarantee_tgt; iIntros "P"; iPoseProof (WP_iff with "P") as "[P1 P2]".
      iSpecialize ("SIM" with "P2 P1").
      iApply "SIM"; iFrame.
    Qed.

    Lemma wsim_half_assume_tgt_WP `{i : !WP P ν ⊤, υ > ν} r g i_s k_t E :
      (WP_remainder i ∗
      wsim (Some false) υ ν E r g R_s R_t RR ps true nths
        (st_s, i_s) (st_t, k_t tt)) ⊢
      wsim (Some true) υ ν E r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, trigger (Assume P) >>= k_t).
    Proof.
      unseal; iIntros "[P SIM] I".
      iPoseProof (wsim_ginv_split with "I") as "> [I1 I2]".
      { eapply H. }
      iApply isim_Assume_tgt; eauto.
      iSplitL "P I1".
      { iApply (WP_iff i); iFrame. }
      { iApply "SIM"; iFrame. }
    Qed.

    Lemma wsim_half_guarantee_tgt_WP `{i : !WP P ν ⊤, υ > ν} r g i_s k_t E :
      (WP_remainder i -∗
      wsim (Some true) υ ν E r g R_s R_t RR ps true nths
        (st_s, i_s) (st_t, k_t tt)) ⊢
      wsim (Some false) υ ν E r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, trigger (Guarantee P) >>= k_t).
    Proof.
      unseal. iIntros "SIM I".
      iApply isim_Guarantee_tgt; iIntros "P"; iPoseProof (WP_iff with "P") as "[P1 P2]".
      iSpecialize ("SIM" with "P2").
      iDestruct "I" as "[O [W I]]". iPoseProof ("I" with "P1") as "> I".
      iApply "SIM"; iFrame.
    Qed.

    (* Derived lemmas *)
    Lemma wsim_unwrapU_src r g X (x : option X) k_s i_t E :
      (∀ x', ⌜x = Some x'⌝ -∗
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, k_s x') (st_t, i_t)) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, unwrapU x >>= k_s) (st_t, i_t).
    Proof.
      iIntros "H". unfold unwrapU. destruct x.
      { hred_l. iApply "H". auto. }
      { unseal; iIntros "P". iApply isim_triggerUB_src. }
    Qed.

    Lemma wsim_unwrapN_src r g X (x : option X) k_s i_t E :
      (∃ x', ⌜x = Some x'⌝ ∗
        wsim t υ ν E r g R_s R_t RR ps pt nths
          (st_s, k_s x') (st_t, i_t)) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, unwrapN x >>= k_s) (st_t, i_t).
    Proof. iIntros "H". iDestruct "H" as (x') "[% H]". subst. hred_l. iApply "H". Qed.

    Lemma wsim_sput_src_sandbox scopes k v r g k_s i_t E :
      In k.1 scopes →
      wsim t υ ν E r g R_s R_t RR true pt nths
        (alist_upd k v st_s, k_s tt) (st_t, i_t) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, HMod.sandbox scopes (trigger (SPut k v)) >>= k_s) (st_t, i_t).
    Proof.
      intros IN; iIntros "SIM".
      rewrite SBRed.put; des_ifs; ss.
      { iApply wsim_sput_src; ss. }
      { edestruct (existsb_exists (String.eqb k.1) scopes).
        hexploit H0; ss.
        { exists k.1; split; ss. apply String.eqb_refl. }
        { i; clarify. }
      }
    Qed.

    Lemma wsim_sget_src_sandbox scopes k r g k_s i_t E :
      In k.1 scopes →
      wsim t υ ν E r g R_s R_t RR true pt nths
        (st_s, k_s (or_else (alist_find k st_s) tt↑)) (st_t, i_t) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, HMod.sandbox scopes (trigger (SGet k)) >>= k_s) (st_t, i_t).
    Proof.
      intros IN; iIntros "SIM".
      rewrite SBRed.get; des_ifs; ss.
      { iApply wsim_sget_src; ss. }
      { edestruct (existsb_exists (String.eqb k.1) scopes).
        hexploit H0; ss.
        { exists k.1; split; ss. apply String.eqb_refl. }
        { i; clarify. }
      }
    Qed.

    Lemma wsim_sput_tgt_sandbox scopes k v r g i_s k_t E :
      In k.1 scopes →
      wsim t υ ν E r g R_s R_t RR ps true nths
        (st_s, i_s) (alist_upd k v st_t, k_t tt) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, HMod.sandbox scopes (trigger (SPut k v)) >>= k_t).
    Proof.
      intros IN; iIntros "SIM".
      rewrite SBRed.put; des_ifs; ss.
      { iApply wsim_sput_tgt; ss. }
      { edestruct (existsb_exists (String.eqb k.1) scopes).
        hexploit H0; ss.
        { exists k.1; split; ss. apply String.eqb_refl. }
        { i; clarify. }
      }
    Qed.

    Lemma wsim_sget_tgt_sandbox scopes k r g i_s k_t E :
      In k.1 scopes →
      wsim t υ ν E r g R_s R_t RR ps true nths
        (st_s, i_s) (st_t, k_t (or_else (alist_find k st_t) tt↑)) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, HMod.sandbox scopes (trigger (SGet k)) >>= k_t).
    Proof.
      intros IN; iIntros "SIM".
      rewrite SBRed.get; des_ifs; ss.
      { iApply wsim_sget_tgt; ss. }
      { edestruct (existsb_exists (String.eqb k.1) scopes).
        hexploit H0; ss.
        { exists k.1; split; ss. apply String.eqb_refl. }
        { i; clarify. }
      }
    Qed.

    Lemma wsim_asm_src (P : Prop) r g k_s i_t E :
      (∀ _ : P, (wsim t υ ν E r g R_s R_t RR true pt nths
        (st_s, k_s tt) (st_t, i_t))) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, assume P >>= k_s) (st_t, i_t).
    Proof.
      unseal; iIntros "RR I". iApply isim_asm_src; eauto.
      iIntros "%H"; iApply ("RR" $! H with "I"); iFrame.
    Qed.

    Lemma wsim_asm_tgt (P : Prop) r g i_s k_t E :
      P →
      wsim t υ ν E r g R_s R_t RR ps true nths
        (st_s, i_s) (st_t, k_t tt) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, assume P >>= k_t).
    Proof.
      intros H; unseal; iIntros "P I". iApply isim_asm_tgt; eauto. iApply ("P" with "I").
    Qed.

    Lemma wsim_guar_src (P : Prop) r g k_s i_t E :
      P →
      wsim t υ ν E r g R_s R_t RR true pt nths
        (st_s, k_s tt) (st_t, i_t) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, guarantee P >>= k_s) (st_t, i_t).
    Proof.
      intros H; unseal; iIntros "P I". iApply isim_guar_src; eauto. iApply ("P" with "I").
    Qed.

    Lemma wsim_guar_tgt (P : Prop) r g i_s k_t E :
      (∀ _ : P, wsim t υ ν E r g R_s R_t RR ps true nths
        (st_s, i_s) (st_t, k_t tt)) ⊢
      wsim t υ ν E r g R_s R_t RR ps pt nths
        (st_s, i_s) (st_t, guarantee P >>= k_t).
    Proof.
      unseal; iIntros "RR I". iApply isim_guar_tgt; eauto.
      iIntros "%H"; iApply ("RR" $! H with "I"); iFrame.
    Qed.

    Lemma wsim_fupd m E1 E2 b r g i_s i_t :
      =|υ, m|={E2, E1}=> wsim (Some b) υ ν E1 r g R_s R_t RR ps pt nths (st_s, i_s) (st_t, i_t)
      ⊢ wsim (Some b) υ ν E2 r g R_s R_t RR ps pt nths (st_s, i_s) (st_t, i_t).
    Proof.
      unseal; rewrite ?{2}invariants.uPred_fupd_unseal /invariants.uPred_fupd_def.
      iIntros "SIM P"; ss. rewrite /wsim_ginv.
      destruct b; iDestruct "P" as "[O [H1 H2]]".
      { iDestruct "H2" as "[%nw [WA [E [D WL]]]]". iDestruct "H1" as "[%nu U]".
        iPoseProof (fupd_mon υ m (m `max` nw) with "SIM") as "SIM"; first lia.
        rewrite ?invariants.uPred_fupd_unseal /invariants.uPred_fupd_def.
        iMod (wsatl_mon υ nw (m `max` nw) with "[WL WA]") as "[WA WL]"; first lia; iFrame.
        iPoseProof ("SIM" with "[WL E D]") as "> [WL [E [D SIM]]]"; first iFrame.
        iApply "SIM"; iFrame.
      }
      { iDestruct "H1" as "[%nw [WA [E [D WL]]]]".
        iPoseProof (fupd_mon υ m (m `max` nw) with "SIM") as "SIM"; first lia.
        rewrite ?invariants.uPred_fupd_unseal /invariants.uPred_fupd_def.
        iMod (wsatl_mon υ nw (m `max` nw) with "[WL WA]") as "[WA WL]"; first lia; iFrame.
        iPoseProof ("SIM" with "[WL E D]") as "> [WL [E [D SIM]]]"; first iFrame.
        iApply "SIM"; iFrame.
      }
    Qed.

    (* Proofmode instances *)
    Global Instance wsim_elim_upd r g P p i_s i_t E :
      ElimModal True p false ( |==> P)%I P
        (wsim t υ ν E r g R_s R_t RR ps pt nths (st_s, i_s) (st_t, i_t))
        (wsim t υ ν E r g R_s R_t RR ps pt nths (st_s, i_s) (st_t, i_t)).
    Proof.
      unseal.
      unfold ElimModal. rewrite bi.intuitionistically_if_elim.
      i. iIntros "[H0 H1] HPRE".
      iApply isim_upd. iMod "H0". iModIntro.
      iApply ("H1" with "H0 HPRE").
    Qed.

    Global Instance wpsim_elim_fupd_gen b E0 E1 E2 y r g P p i_s i_t :
      ElimModal
        (E0 ⊆ E2) p false
        (=|υ, y|={E0, E1}=> P)
        P
        (wsim (Some b) υ ν E2 r g R_s R_t RR ps pt nths (st_s, i_s) (st_t, i_t))
        (wsim (Some b) υ ν (E1 ∪ (E2 ∖ E0)) r g R_s R_t RR ps pt nths (st_s, i_s) (st_t, i_t)) | 10.
    Proof.
      rewrite /ElimModal bi.intuitionistically_if_elim.
      intros SUB. iIntros "[H0 H1]".
      iApply (wsim_fupd y).
      iMod "H0". iPoseProof ("H1" with "H0") as "H".
      iModIntro. iFrame.
    Qed.

    Global Instance wpsim_elim_fupd_same_mask b E1 E2 n r g P p i_s i_t :
      ElimModal
        (E1 ⊆ E2) p false
        (=|υ, n|={E1}=> P)
        P
        (wsim (Some b) υ ν E2 r g R_s R_t RR ps pt nths (st_s, i_s) (st_t, i_t))
        (wsim (Some b) υ ν E2 r g R_s R_t RR ps pt nths (st_s, i_s) (st_t, i_t)).
    Proof.
      rewrite /ElimModal bi.intuitionistically_if_elim.
      iIntros "%SUB [H0 H1]".
      iApply (wsim_fupd n).
      iMod "H0". iPoseProof ("H1" with "H0") as "H".
      iModIntro. rewrite -union_difference_L; ss.
    Qed.

    Global Instance wpsim_elim_fupd_simple b E0 E1 n r g P p i_s i_t :
      ElimModal
        True p false
        (=|υ, n|={E0, E1}=> P)
        P
        (wsim (Some b) υ ν E0 r g R_s R_t RR ps pt nths (st_s, i_s) (st_t, i_t))
        (wsim (Some b) υ ν E1 r g R_s R_t RR ps pt nths (st_s, i_s) (st_t, i_t)).
    Proof.
      rewrite /ElimModal bi.intuitionistically_if_elim.
      iIntros "_ [H0 H1]".
      iApply (wsim_fupd n).
      iMod "H0". iPoseProof ("H1" with "H0") as "H".
      iModIntro. iFrame.
    Qed.
    
    Global Instance wpsim_add_modal_FUpd b E n r g P i_s i_t :
      AddModal (=|υ, n|={E}=> P)
               P
               (wsim (Some b) υ ν E r g R_s R_t RR ps pt nths (st_s, i_s) (st_t, i_t)).
    Proof.
      unfold AddModal. iIntros "[H0 H1]". iMod "H0". iApply ("H1" with "H0").
    Qed.

    (* Primitive simulation rules *)
    Lemma wsim_init sti_s sti_t :
      wsim None υ ν ⊤ ibot ibot R_s R_t RR ps pt nths sti_s sti_t ⊢
      @isim Σ open fl_s fl_t Ist ibot ibot R_s R_t RR ps pt nths sti_s sti_t.
    Proof.
      unseal; iIntros "SIM"; ss; iPoseProof ("SIM" with "[]") as "SIM"; first done.
      iPoseProof (isim_mono_knowledge with "SIM") as "SIM".
      { instantiate (1:=ibot); i; iIntros "H"; rewrite /wsim_rel /ibot; destruct sti_src, sti_tgt.
        iDestruct "H" as "[]".
      }
      { instantiate (1:=ibot); i; iIntros "H"; rewrite /wsim_rel /ibot; destruct sti_src, sti_tgt.
        iDestruct "H" as "[]".
      }
      iFrame.
    Qed.

    Lemma wsim_split sti_s sti_t :
      (wsim_pre t υ ν ⊤ -∗ wsim None υ ν ⊤ ibot ibot R_s R_t RR ps pt nths sti_s sti_t) ⊢
      wsim t υ ν ⊤ ibot ibot R_s R_t RR ps pt nths sti_s sti_t.
    Proof.
      unseal.
      iIntros "SIM PRE"; ss. iApply ("SIM" with "PRE"). done.
    Qed.

    Lemma wsim_merge sti_s sti_t :
      wsim_pre t υ ν ⊤ ∗ wsim t υ ν ⊤ ibot ibot R_s R_t RR ps pt nths sti_s sti_t ⊢
      wsim None υ ν ⊤ ibot ibot R_s R_t RR ps pt nths sti_s sti_t.
    Proof.
      unseal.
      iIntros "[PRE SIM] _"; ss. iApply ("SIM" with "PRE").
    Qed.
End lemmas. End wsim.