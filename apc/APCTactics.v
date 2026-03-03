Require Import CRIS.
Require Import APCHeader APC APCA.

(* useful apc lemmas - require IST *)
Section LEMMAS.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Local Definition state : Type := gmap key (option Any.t).
  Local Definition post (R_s R_t : Type) : Type := state * R_s → state * R_t → iProp Σ.
  Local Definition rel : Type := ∀ R_s R_t : Type,
    post R_s R_t → bool → bool → state * itree crisE R_s → state * itree crisE R_t → iProp Σ.

  Context (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t))).
  Context (Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ).
  Context (R_s R_t : Type).
  Context (RR : post R_s R_t).
  Context (ps pt : bool).
  Context (st_src st_tgt : state).

  Lemma wsim_apc_src
    (E : coPset) (r g : rel) (k_src : () -> itree crisE R_s) (i_tgt : itree crisE R_t)
    (msk_s : emask) (sp_s sp_pure : specmap) (ow od : Ord.t) :
    wsim fl_s fl_t Ist (E, E) r g R_s R_t RR true pt (st_src, k_src ()) (st_tgt, i_tgt) ⊢
    wsim fl_s fl_t Ist (E, E) r g R_s R_t RR ps pt
      (st_src, ((SB.sandbox msk_s (SModTr.trans sp_s (_APC od sp_pure ow))) >>= k_src))
      (st_tgt, i_tgt).
  Proof using.
    iIntros "ISIM". rewrite unfold_APC.
    cStepsS. case_match; cStepsS; ss. cForceS true. cStepsS. iFrame.
  Qed.

  Lemma wsim_apc_src_call_tgt_weaker
    (E : coPset) (r g : rel) (k_src : () → itree crisE R_s) (k_tgt: Any.t -> itree crisE R_t)
    (msk_s : emask) (sp_s sp_pure : specmap)
    (fn: string) args fsp' fsp X (spec_arg: X) o P Q
    (ow_src ow_fn od_src od_fn : Ord.t)
    (WIDTH: (ow_fn < ow_src)%ord)
    (DEPTH: (od_fn < od_src)%ord)
    (SpPureInSp: sp_pure ⊆ sp_s)
    (fnInSpPure: sp_pure.1 !! (fid fn) = Some fsp')
    (WEAK: ⊢ fspec_imply fsp' fsp)
    (fspIsfspecapc: fsp = (@fspec_apc Σ X o (λ x, (P x, Q x))))
    :
    (((P spec_arg args ∗ ⌜∃ vo : Ord.t, od_fn ↑ = vo ↑ ∧ (o spec_arg <= vo)%ord⌝) ∗ (Ist st_src st_tgt)) ∗
     (∀ st_src0 st_tgt0 (ret: Any.t),
        ((Ist st_src0 st_tgt0) ∗ (Q spec_arg ret))
        -∗ wsim fl_s fl_t Ist (E, E) r g R_s R_t RR false false
             (st_src0, ((SB.sandbox msk_s (SModTr.trans sp_s (_APC od_src sp_pure ow_fn))) >>= k_src))
             (st_tgt0, k_tgt ret)))
    ⊢
      wsim fl_s fl_t Ist (E, E) r g R_s R_t RR ps pt
        (st_src, (SB.sandbox msk_s (SModTr.trans sp_s (_APC od_src sp_pure ow_src))) >>= k_src)
        (st_tgt, (trigger (Call fn args)) >>= k_tgt).
  Proof using.
    (* intros Hchoose Htake Hguarantee Hassume Hcall. *)
    iIntros "[[[PRE %] IST] ISIM]".
    des. set_marker m. hide_ihyps. rewrite unfold_APC. show_until m.
    cStepsS. case_match; last by cStepsS. cForceS false.
    cStepsS. case_match; last by cStepsS. cForceS ow_fn.
    cStepsS. case_match; last by cStepsS. cForceS WIDTH.
    cStepsS. case_match; last by cStepsS. cForceS fn.
    cStepsS. case_match; last by cStepsS. cForceS od_fn. cStepsS.
    cForceS. iSplit; et. cStepsS.
    erewrite lookup_weaken; [..|apply SpPureInSp]; et.
    cStepsS. case_match; last by cStepsS.
    iPoseProof (WEAK with "") as "WEAK".
    iSpecialize ("WEAK" with "[]").
    { instantiate (1 := (λ _ a, (Q spec_arg a)%I)).
      instantiate (1 := (λ x a, (P spec_arg a ∗ ⌜∃ vo0, x = vo0 ↑ ∧ (o spec_arg <= vo0)%ord⌝))%I).
      subst fsp. rewrite /fspec_apc. ss. iPureIntro. exists spec_arg. ss. }
    iDestruct "WEAK" as "(%pre & %post & %Hfsp & POST)".
    cForceS (FSpec_mk _ _ Hfsp).
    cStepsS. case_match; last by cStepsS. cForceS args.
    iSpecialize ("POST" $! od_fn↑ args with "[PRE]").
    { iFrame. iPureIntro. esplits; eauto. }
    iDestruct "POST" as ">[PRE POST]".
    cStepsS. case_match; last by cStepsS. cForceS; iSplitL "PRE"; eauto.
    cStepsS. case_match; last by cStepsS. cStepsT. cCall "IST". iIntros (???) "IST".
    cStepsS. case_match; last by cStepsS. cStepsS. case_match; last by cStepsS.
    cStepsS. iPoseProof ("POST" with "ASM") as ">POST".
    iApply wsim_reset. iSpecialize ("ISIM" $! st_s' st_t' ret). cStepsT.
    iApply "ISIM"; iFrame.
  Qed.

  Lemma wsim_apc_src_call_tgt
    (E : coPset) (r g : rel) (k_src : () → itree crisE R_s) (k_tgt: Any.t -> itree crisE R_t)
    (msk_s : emask) (sp_s sp_pure : specmap)
    (fn: string) args fsp X (spec_arg: X) o P Q
    (ow_src ow_fn od_src od_fn : Ord.t)
    (WIDTH: (ow_fn < ow_src)%ord)
    (DEPTH: (od_fn < od_src)%ord)
    (SpPureInSp: sp_pure ⊆ sp_s)
    (fnInSpPure: sp_pure.1 !! (fid fn) = Some fsp)
    (fspIsfspecapc: fsp = (@fspec_apc Σ X o (λ x, (P x, Q x))))
    :
    (((P spec_arg args ∗ ⌜∃ vo : Ord.t, od_fn ↑ = vo ↑ ∧ (o spec_arg <= vo)%ord⌝) ∗ (Ist st_src st_tgt)) ∗
     (∀ st_src0 st_tgt0 (ret: Any.t),
        ((Ist st_src0 st_tgt0) ∗ (Q spec_arg ret))
        -∗ wsim fl_s fl_t Ist (E, E) r g R_s R_t RR false false
             (st_src0, ((SB.sandbox msk_s (SModTr.trans sp_s (_APC od_src sp_pure ow_fn))) >>= k_src))
             (st_tgt0, k_tgt ret)))
    ⊢
      wsim fl_s fl_t Ist (E, E) r g R_s R_t RR ps pt
        (st_src, (SB.sandbox msk_s (SModTr.trans sp_s (_APC od_src sp_pure ow_src))) >>= k_src)
        (st_tgt, (trigger (Call fn args)) >>= k_tgt).
  Proof using.
    eapply wsim_apc_src_call_tgt_weaker; et. 
    eapply fspec_imply_refl.
  Qed.

End LEMMAS.

Ltac apcCallWeak hyps :=
  iApply wsim_apc_src_call_tgt_weaker; [ | | |simpl_sp| | |]; ss.

Ltac apcS :=
  iApply wsim_apc_src; ss.

Ltac apcCall hyps :=
  iApply wsim_apc_src_call_tgt; [ | | |simpl_sp| |iSplitL hyps]; ss.
