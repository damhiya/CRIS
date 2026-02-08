Require Import CRIS.
Require Import APCHeader APC APCA.

Set Implicit Arguments.

Import APC.

(* useful apc lemmas - require IST *)

Section LEMMAS.

  Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concGS}.

  Local Definition state : Type := gmap key (option Any.t).
  Local Definition post (R_s R_t : Type) : Type := state * R_s → state * R_t → iProp Σ.
  Local Definition rel : Type := ∀ R_s R_t : Type,
    post R_s R_t → bool → bool → state * itree crisE R_s → state * itree crisE R_t → iProp Σ.

  Context (fl_s fl_t : gmap (option string) (option (Any.t → itree crisE Any.t))).
  Context (Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ).
  Context (R_s R_t : Type).
  Context (RR : post R_s R_t).
  Context (ps pt : bool).
  Context (st_src st_tgt : state).

  Lemma wsim_apc_src
    (E : coPset) (r g : rel) (k_src : () -> itree crisE R_s) (i_tgt : itree crisE R_t)
    (msk_s msk_t : emask) (sp_s sp_t sp_pure : specmap) (ow od : Ord.t) :
    (∀ X, msk_s _ (subevent _ (Choose X))) ->
    wsim fl_s fl_t Ist (E, E) r g R_s R_t RR true pt (st_src, k_src ()) (st_tgt, i_tgt) ⊢
    wsim fl_s fl_t Ist (E, E) r g R_s R_t RR ps pt
      (st_src, ((SB.sandbox msk_s (SModTr.trans sp_s (_APC od sp_pure ow))) >>= k_src))
      (st_tgt, i_tgt).
  Proof using.
    intros Hchoose. iIntros "ISIM". rewrite unfold_APC.
    steps_l. rewrite Hchoose. force_l true. steps_l. iFrame.
  Qed.

  Lemma wsim_apc_src_call_tgt_weaker
    (E : coPset) (r g : rel) (k_src : () → itree crisE R_s) (k_tgt: Any.t -> itree crisE R_t)
    (msk_s msk_t : emask) (sp_s sp_t sp_pure : specmap) (ow od : Ord.t)
    (fn: string) args fsp' fsp X (spec_arg: X) o P Q
    (ow_src ow_fn od_src od_fn : Ord.t)
    (WIDTH: (ow_fn < ow_src)%ord)
    (DEPTH: (od_fn < od_src)%ord)
    (SpPureInSp: sp_pure ⊆ sp_s)
    (fnInSpPure: sp_pure !! speckey_fn fn = Some fsp')
    (WEAK: ⊢ fspec_imply fsp' fsp)
    (fspIsfspecapc: fsp = (@fspec_apc Σ X o (λ x, (P x, Q x))))
    :
    (∀ X, msk_s _ (subevent _ (Choose X))) ->
    (∀ X, msk_s _ (subevent _ (Take X))) ->
    (∀ X, msk_s _ (subevent _ (Guarantee X))) ->
    (∀ X, msk_s _ (subevent _ (Assume X))) ->
    (msk_s _ (subevent _ (Call fn args)) = msk_t _ (subevent _ (Call fn args))) ->
    (((P spec_arg args ∗ ⌜∃ vo : Ord.t, od_fn ↑ = vo ↑ ∧ (o spec_arg <= vo)%ord⌝) ∗ (Ist st_src st_tgt)) ∗
     (∀ st_src0 st_tgt0 (vret ret: Any.t),
        ((Ist st_src0 st_tgt0) ∗ (Q spec_arg ret))
        -∗ wsim fl_s fl_t Ist (E, E) r g R_s R_t RR false false
             (st_src0, ((SB.sandbox msk_s (SModTr.trans sp_s (_APC od_src sp_pure ow_fn))) >>= k_src))
             (st_tgt0, k_tgt ret)))
    ⊢
      wsim fl_s fl_t Ist (E, E) r g R_s R_t RR ps pt
        (st_src, (SB.sandbox msk_s (SModTr.trans sp_s (_APC od_src sp_pure ow_src))) >>= k_src)
        (st_tgt, (SB.sandbox msk_t (trigger (Call fn args))) >>= k_tgt).
  Proof using.
    intros Hchoose Htake Hguarantee Hassume Hcall. iIntros "[[[PRE %] IST] ISIM]".
    des. set_marker m. hide_ihyps. rewrite unfold_APC. show_until m.
    steps_l. rewrite Hchoose. force_l false. steps_l. rewrite Hchoose.
    force_l ow_fn. steps_l. rewrite Hchoose. force_l WIDTH. steps_l.
    rewrite Hchoose. force_l fn. steps_l. rewrite Hchoose. force_l od_fn. steps_l.
    assert (PO: (is_Some (sp_pure !! speckey_fn fn) ∧ (od_fn < od_src)%ord)); et.
    unfold guarantee. steps_l. rewrite Hchoose. force_l PO. steps_l.
    erewrite lookup_weaken; eauto. steps_l. rewrite Hchoose.
    iPoseProof (WEAK with "") as "WEAK".
    iSpecialize ("WEAK" with "[]").
    { instantiate (1 := (λ _ a, (Q spec_arg a)%I)).
      instantiate (1 := (λ x a, (P spec_arg a ∗ ⌜∃ vo0, x = vo0 ↑ ∧ (o spec_arg <= vo0)%ord⌝))%I).
      subst fsp. rewrite /fspec_apc. ss. iPureIntro. exists spec_arg. ss. }
    iDestruct "WEAK" as "(%pre & %post & %Hfsp & POST)".
    force_l (FSpec_mk _ _ Hfsp). steps_l. rewrite Hchoose. force_l args. steps_l.
    rewrite Hguarantee. iSpecialize ("POST" $! od_fn↑ args with "[PRE]").
    { iFrame. iPureIntro. esplits; eauto. }
    iDestruct "POST" as ">[PRE POST]".
    force_l; iSplitL "PRE"; eauto. steps_l.
    steps_r. des_ifs; cycle 1.
    { steps_l; ss. }
    steps_l. steps_r. call "IST". iIntros (???) "IST".
    steps_l. steps_r. rewrite Htake. steps_l. rewrite Hassume. steps_l.
    iPoseProof ("POST" with "ASM") as ">POST".
    iApply wsim_reset. iSpecialize ("ISIM" $! st_s' st_t' (tt↑) ret).
    iApply "ISIM"; iFrame.
  Qed.

  Lemma wsim_apc_src_call_tgt
    (E : coPset) (r g : rel) (k_src : () → itree crisE R_s) (k_tgt: Any.t -> itree crisE R_t)
    (msk_s msk_t : emask) (sp_s sp_t sp_pure : specmap) (ow od : Ord.t)
    (fn: string) args fsp X (spec_arg: X) o P Q
    (ow_src ow_fn od_src od_fn : Ord.t)
    (WIDTH: (ow_fn < ow_src)%ord)
    (DEPTH: (od_fn < od_src)%ord)
    (SpPureInSp: sp_pure ⊆ sp_s)
    (fnInSpPure: sp_pure !! speckey_fn fn = Some fsp)
    (fspIsfspecapc: fsp = (@fspec_apc Σ X o (λ x, (P x, Q x))))
    :
    (∀ X, msk_s _ (subevent _ (Choose X))) ->
    (∀ X, msk_s _ (subevent _ (Take X))) ->
    (∀ X, msk_s _ (subevent _ (Guarantee X))) ->
    (∀ X, msk_s _ (subevent _ (Assume X))) ->
    (msk_s _ (subevent _ (Call fn args)) = msk_t _ (subevent _ (Call fn args))) ->
    (((P spec_arg args ∗ ⌜∃ vo : Ord.t, od_fn ↑ = vo ↑ ∧ (o spec_arg <= vo)%ord⌝) ∗ (Ist st_src st_tgt)) ∗
     (∀ st_src0 st_tgt0 (vret ret: Any.t),
        ((Ist st_src0 st_tgt0) ∗ (Q spec_arg ret))
        -∗ wsim fl_s fl_t Ist (E, E) r g R_s R_t RR false false
             (st_src0, ((SB.sandbox msk_s (SModTr.trans sp_s (_APC od_src sp_pure ow_fn))) >>= k_src))
             (st_tgt0, k_tgt ret)))
    ⊢
      wsim fl_s fl_t Ist (E, E) r g R_s R_t RR ps pt
        (st_src, (SB.sandbox msk_s (SModTr.trans sp_s (_APC od_src sp_pure ow_src))) >>= k_src)
        (st_tgt, (SB.sandbox msk_t (trigger (Call fn args))) >>= k_tgt).
  Proof using.
    eapply wsim_apc_src_call_tgt_weaker; et. 
    eapply fspec_imply_refl.
  Qed.

End LEMMAS.

(*** TODO : create appropriate tactics for handling APC ***)

(* Ltac _prep_macro := *)
(*   ired; *)
(*   match goal with *)
(*   | [|- context[SB.sandbox _ _ _ (SModTr.trans _ _ (_APC _ _ _)) >>= _]] => fail 1 *)
(*   | [|- context[SB.sandbox _ _ _ (SModTr.trans _ _ (_APC _ _ _) >>= _)]] => *)
(*       rewrite// [in SB.sandbox _ _ _ (SModTr.trans _ _ (_APC _ _ _) >>= _)] SBRed.bind *)
(*   | [|- context[SModTr.trans _ _ (_APC _ _ _ >>= _)]] => *)
(*       rewrite// [in (SModTr.trans _ _ (_APC _ _ _ >>= _))] SRed.bind; _prep_macro *)
(*   end. *)

(* Ltac prep_macro_l := *)
(*   let marker := fresh "MARKER" in *)
(*   set_marker marker; *)
(*   hide_ihyps; *)
(*   only_itree_l; *)
(*   try _prep_macro; ired; *)
(*   show_until marker.   *)

(* Ltac prep_macro_r := *)
(*   let marker := fresh "MARKER" in *)
(*   set_marker marker; *)
(*   hide_ihyps; *)
(*   only_itree_r; *)
(*   try _prep_macro; ired; *)
(*   show_until marker. *)

(* Ltac prep_macro := *)
(*   let marker := fresh "MARKER" in *)
(*   set_marker marker; *)
(*   hide_ihyps; *)
(*   only_itree_l; try _prep_macro; ired; show_itree; *)
(*   only_itree_r; try _prep_macro; ired; show_itree; *)
(*   show_until marker. *)

(* Ltac apc_l := *)
(*   prep_macro_l; *)
(*   iApply wsim_apc_src; des_pairs; s. *)

(* (** TODO: updating apc tactics is required *) *)

(* Ltac apc_call hyps := *)
(*   prep_macro_l; norm_r; *)
(*   iApply wsim_apc_src_call_tgt; des_pairs; s; *)
(*   [| | | | |try prove_sb_cond|try prove_sb_cond| |iSplitL hyps; [ |iIntros "% % % %"; iIntrosFresh "ISTPOST"]]. *)

(* Ltac apc_call_weaker hyps := *)
(*   prep_macro_l; norm_r; *)
(*   iApply wsim_apc_src_call_tgt_weaker; des_pairs; s; *)
(*   [| | | | | |try prove_sb_cond|try prove_sb_cond| |iSplitL hyps; [ |iIntros "% % % %"; iIntrosFresh "ISTPOST"]]. *)
