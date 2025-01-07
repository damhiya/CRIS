Require Import Common.

Require Import ISim.
Require Export invariants.

From stdpp Require Import coPset.
Section wpsim.
  (* Context `{@SRFIntp.t (domain Σ) α, Γ : HRA, !subG Γ Σ, !invGS Σ Γ}. *)
  Context `{!sinvGS Σ Γ α β τ}.
  Context {fl_s fl_t : alist string (Any.t → itree hmodE Any.t)}.
  Context {Ist : nat → alist key Any.t → alist key Any.t → iProp Σ}.
  Context {my_tid : nat}.

  Local Definition state : Type := alist key Any.t.
  Local Definition post (R : Type) : Type := nat → state * R → state * R → iProp Σ.
  Local Definition rel : Type := ∀ R : Type,
    post R → bool → bool → nat → state * itree hmodE R → state * itree hmodE R → iProp Σ.

  Implicit Types r g : rel.
  Implicit Types ps pt : bool.
  Implicit Types nths : nat.
  Implicit Types u : univ_id.
  Implicit Types n : level.
  Implicit Types E : coPset.

  (* TODO : abstraction into mixins *)
  (* Simulation relation that corresponds to iris' weakest precondition *)
  (* TODO : seal *)
  Local Definition wpsim_def r g R RR ps pt nths st_s st_t u n E : iProp Σ :=
    univs u n ∗ wsats u n E -∗ @isim Σ fl_s fl_t Ist my_tid false r g R RR ps pt nths st_s st_t.
  Local Definition wpsim_aux : seal (@wpsim_def). Proof. by eexists. Qed.
  Definition wpsim := wpsim_aux.(unseal).
  Local Definition wpsim_eq : @wpsim = @wpsim_def := wpsim_aux.(seal_eq).
  Local Ltac unseal := rewrite wpsim_eq /wpsim_def.

  (* Mostly will not be used *)
  Lemma wpsim_ret r g R RR ps pt nths st_s st_t rs rt u n E :
    RR nths (st_s, rs) (st_t, rt) ⊢ wpsim r g R RR ps pt nths (st_s, Ret rs) (st_t, Ret rt) u n ⊤.
  Proof. unseal; iIntros "RR INV". iApply isim_ret; done. Qed.

  Lemma wpim_call r g R RR ps pt nths st_s st_t fn arg k_s k_t u n E :
    Ist nths st_s st_t ∗
    (∀ ret nths' st_s' st_t'
      (NODS : List.NoDup (List.map fst st_s'))
      (NODD : List.NoDup (List.map fst st_t')),
      Ist nths' st_s' st_t' -∗
      wpsim r g R RR true true nths' (st_s', k_s ret) (st_t', k_t ret) u n E) ⊢
    wpsim r g R RR ps pt nths
      (st_s, trigger (Call fn arg) >>= k_s) (st_t, trigger (Call fn arg) >>= k_t) u n E.
  Proof.
    unseal; iIntros "[IST CONT] INV".
    rewrite -isim_call; iFrame.
    iIntros (??????) "IST !>"; iApply ("CONT" with "[] [] [IST]"); iFrame; try iPureIntro; ss.
  Qed.

  Lemma wpsim_io r g R RR ps pt nths st_s st_t fn I O (arg : I) k_s k_t u n E :
    (∀ (ret : O), wpsim r g R RR true true nths (st_s, k_s ret) (st_t, k_t ret) u n E) ⊢
    wpsim r g R RR ps pt nths
      (st_s, trigger (IO fn arg) >>= k_s)
      (st_t, trigger (IO fn arg) >>= k_t) u n E.
  Proof. unseal; iIntros "RR INV". iApply isim_io. iIntros (ret); iApply "RR"; iFrame. Qed.

  Lemma wpsim_tau_src r g R RR ps pt nths st_s st_t i_s i_t u n E :
    wpsim r g R RR true pt nths (st_s, i_s) (st_t, i_t) u n E ⊢
    wpsim r g R RR ps pt nths (st_s, tau;; i_s) (st_t, i_t) u n E.
  Proof. unseal; iIntros "RR INV". iApply isim_tau_src; iApply "RR"; iFrame. Qed.

  Lemma wpsim_tau_tgt r g R RR ps pt nths st_s st_t i_s i_t u n E :
    wpsim r g R RR ps true nths (st_s, i_s) (st_t, i_t) u n E ⊢
    wpsim r g R RR ps pt nths (st_s, i_s) (st_t, tau;; i_t) u n E.
  Proof. unseal; iIntros "RR INV". iApply isim_tau_tgt; iApply "RR"; iFrame. Qed.

  Lemma wpsim_inline_src r g R RR ps pt nths st_s st_t fn arg f_s k_s i_t u n E
      (FIND : alist_find fn fl_s = Some f_s):
    wpsim r g R RR true pt nths
      (st_s, x <- (ret <- (f_s arg);; (tau;; tau;; Ret ret));; (k_s x))
      (st_t, i_t) u n E ⊢
    wpsim r g R RR ps pt nths (st_s, trigger (Call fn arg) >>= k_s) (st_t, i_t) u n E.
  Proof. unseal; iIntros "RR INV". iApply isim_inline_src; eauto. iApply "RR"; iFrame. Qed.

  Lemma wpsim_inline_tgt r g R RR ps pt nths st_s st_t fn arg i_s f_t k_t u n E
      (FIND : alist_find fn fl_t = Some f_t):
    wpsim r g R RR ps true nths
      (st_s, i_s)
      (st_t, x <- (ret <- (f_t arg);; (tau;; tau;; Ret ret));; (k_t x)) u n E ⊢
    wpsim r g R RR ps pt nths (st_s, i_s) (st_t, trigger (Call fn arg) >>= k_t) u n E.
  Proof. unseal; iIntros "RR INV". iApply isim_inline_tgt; eauto. iApply "RR"; iFrame. Qed.

  Lemma wpsim_take_src X r g R RR ps pt nths st_s st_t k_s i_t u n E :
    (∀ x, wpsim r g R RR true pt nths (st_s, k_s x) (st_t, i_t) u n E) ⊢
    wpsim r g R RR ps pt nths (st_s, trigger (Take X) >>= k_s) (st_t, i_t) u n E.
  Proof.
    unseal; iIntros "RR INV". iApply isim_take_src; eauto. iIntros (x); iApply "RR"; iFrame.
  Qed.

  Lemma wpsim_take_tgt X r g R RR ps pt nths st_s st_t i_s k_t u n E :
    (∃ x, wpsim r g R RR ps true nths (st_s, i_s) (st_t, k_t x) u n E) ⊢
    wpsim r g R RR ps pt nths (st_s, i_s) (st_t, trigger (Take X) >>= k_t) u n E.
  Proof.
    unseal; iIntros "[%x RR] INV". iApply isim_take_tgt; eauto. iExists _; iApply "RR"; iFrame.
  Qed.

  Lemma wpsim_choose_src X r g R RR ps pt nths st_s st_t k_s i_t u n E :
    (∃ x, wpsim r g R RR true pt nths (st_s, k_s x) (st_t, i_t) u n E) ⊢
    wpsim r g R RR ps pt nths (st_s, trigger (Choose X) >>= k_s) (st_t, i_t) u n E.
  Proof.
    unseal; iIntros "[%x RR] INV". iApply isim_choose_src; eauto. iExists _; iApply "RR"; iFrame.
  Qed.

  Lemma wpsim_choose_tgt X r g R RR ps pt nths st_s st_t i_s k_t u n E :
    (∀ x, wpsim r g R RR ps true nths (st_s, i_s) (st_t, k_t x) u n E)
    ⊢ wpsim r g R RR ps pt nths (st_s, i_s) (st_t, trigger (Choose X) >>= k_t) u n E.
  Proof.
    unseal; iIntros "RR INV". iApply isim_choose_tgt; eauto. iIntros (x); iApply "RR"; iFrame.
  Qed.
End wpsim.
(* TODO : proofmode instances *)