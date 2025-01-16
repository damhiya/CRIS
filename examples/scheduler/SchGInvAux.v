(* Require Import CRIS.

Require Import SchGInv SchHeader SchASpec.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section MACROAUX.

  Context `{_W: @sinvG Σ Γ α β τ, !SchAS.G Γ}.
  Notation iProp := (iProp Σ).

  (** Sch.spawn LEMMA *)

  Lemma isim_mspawn_hp
    fl fr Ist r g {R} RR my_tid ps pt nths st_src st_tgt k_src k_tgt scp_src scp_tgt invspc
    (StbFun StbSch: Sk.t → string → option fspec) (univ: positive)
    (sk: Sk.t) (fvarg farg: SAny.t) (pre: iProp) (postS: SAny.t → {n & SRFSyn.t n}) 
    (fn: string) (fsp: fspec) (m: meta fsp)
    (FINDF: StbFun sk fn = Some fsp)
    (FINDS: StbSch sk SchName.spawn = Some (SchAS.spawn_spec univ sk StbFun))
    (SPWN: ∀ tid, SchAS.fspec_spawnable univ fsp tid m fvarg↑ farg↑ pre postS)
    :
      (((Ist nths st_src st_tgt) ∗ (∃ n, closed_universe univ n ⊤) ∗ pre) ∗
      (∀ nths0 st_src0 st_tgt0 tid,
        ((Ist nths0 st_src0 st_tgt0) ∗ (∃ n, closed_universe univ n ⊤) ∗ (SchAS.token_th tid postS))
        -∗ @isim Σ fl fr Ist my_tid false r g R RR true true nths0 
              (st_src0, k_src tid)
              (st_tgt0, k_tgt tid)))
    ⊢
      (isim fl fr Ist my_tid false r g RR ps pt nths 
        (st_src, (HModSem.sandbox scp_src (interp_smod invspc (StbSch sk) (Sch.spawn (fn, fvarg)))) >>= k_src)
        (st_tgt, (HModSem.sandbox scp_tgt (PModSem.interp (Sch.spawn (fn, farg)))) >>= k_tgt)).
  Proof.
    iIntros "[(IST & W & PRE) ISIM]". rewrite !/Sch.spawn /ccallU. unseal "Sch".
    force_l. iSplitR; et. unfold HoareCall. steps_l. force_l.
    Unshelve.
    2:{ split.
      - exact (farg, fvarg, pre, postS).
      - exists fn. unfold find_fsp. rewrite FINDF. exact m. }
    force_l ((fn, farg)↑). force_l. iSplitL "PRE W".
    { iFrame. revert SPWN. revert m. generalize FINDF. unfold find_fsp. rewrite FINDF. i.
      rewrite (@UIP _ _ _ FINDF0 eq_refl). erewrite <-rew_swap; et. }
    
    call "IST"; et. iModIntro.
    
    steps_l. steps_r. iDestruct "ASM" as "(W & (% & % & % & % & TKN))". des; subst; hss.
    steps_r. iApply "ISIM". iFrame.
  Qed.

  Lemma isim_mspawn_hh
    fl fr Ist r g {R} RR my_tid ps pt nths st_src st_tgt k_src k_tgt scp_src scp_tgt invspc_src invspc_tgt
    (stbf stb_src stb_tgt: Sk.t → string → option fspec) (univ: positive)
    (sk: Sk.t) (fvarg: SAny.t) (fn: string) (fsp: fspec) (m: meta fsp)
    (FIND: stbf sk fn = Some fsp)
    (SPWNS: stb_src sk SchName.spawn = Some (SchAS.spawn_spec univ sk stbf))
    (SPWNT: stb_tgt sk SchName.spawn = Some (SchAS.spawn_spec univ sk stbf))
    :
      ((Ist nths st_src st_tgt) ∗
      (∀ nths0 st_src0 st_tgt0 tid,
        (Ist nths0 st_src0 st_tgt0)
        -∗ @isim Σ fl fr Ist my_tid false r g R RR true true nths0 
              (st_src0, k_src tid)
              (st_tgt0, k_tgt tid)))
    ⊢
      (isim fl fr Ist my_tid false r g RR ps pt nths 
        (st_src, (HModSem.sandbox scp_src (interp_smod invspc_src (stb_src sk) (Sch.spawn (fn, fvarg))))>>= k_src)
        (st_tgt, (HModSem.sandbox scp_tgt (interp_smod invspc_tgt (stb_tgt sk) (Sch.spawn (fn, fvarg)))) >>= k_tgt)).
  Proof.
    iIntros "[IST ISIM]". rewrite !/Sch.spawn !/ccallU. unseal "Sch".
    
    steps_r. inv SPWNT. ss. iDestruct "GRT" as "[W [% [% GRT]]]". hss.
    destruct q0. destruct p. destruct p. destruct p. destruct s.
    iDestruct "GRT" as "((% & % & [% %] & %) & PRE)". des; subst; hss.

    forces_l. iSplit; et. steps_l. forces_l. iSplitL "PRE W".
    { iFrame. iExists _. iSplit; et. Unshelve.
      2:{ split; [exact (t, t0, b, o)|]. exists x. ss. }
      2:exact ((x, t)↑). ss. iSplit; et. }

    call "IST"; et. iModIntro.

    steps_l. iDestruct "ASM" as "[W (% & % & % & [% %] & TKN)]". subst; hss.

    forces_r. iSplitL "TKN W". { iFrame; et. }
    steps_r. hss. steps_r. iApply "ISIM". iFrame.
  Qed.

  (** YIELD LEMMA **)

  Lemma isim_myield_tgt_hp
    fl fr Ist r g {R} RR my_tid ps pt nths st_src st_tgt k_src k_tgt scp_src scp_tgt invspc stb univ
    (SPC: stb SchName.yield = Some (SchAS.yield_spec univ))
    :
    bi_entails
      (((Ist nths st_src st_tgt) ∗ (∃ n, closed_universe univ n ⊤)) ∗
      (∀ nths0 st_src0 st_tgt0,
        ((Ist nths0 st_src0 st_tgt0) ∗ (∃ n, closed_universe univ n ⊤))
        -∗ @isim Σ fl fr Ist my_tid false r g R RR false true nths0 
              (st_src0, (HModSem.sandbox scp_src (interp_smod invspc stb (Sch.yield))) >>= k_src) 
              (st_tgt0, k_tgt tt)))
      (isim fl fr Ist my_tid false r g RR ps pt nths 
        (st_src, (HModSem.sandbox scp_src (interp_smod invspc stb (Sch.yield))) >>= k_src) 
        (st_tgt, (HModSem.sandbox scp_tgt (PModSem.interp (Sch.yield))) >>= k_tgt)).
  Proof.
    iIntros "[[IST W] ISIM]". rewrite !/Sch.yield. unseal "Sch".
    rewrite !unfold_iter_eq. grind. prep. iApply isim_reset.
    iStopProof. revert st_tgt.
    combine_quant st_src.
    combine_quant nths.
    combine_quant ps.
    combine_quant pt.
    eapply isim_coind. ii. destruct a as [pt [ps [nths [st_src st_tgt]]]].
    iIntros "((IST & W & ISIM) & #CIH)".

    grind. prep. iApply isim_reset. steps_r. destruct q.
    {
      steps_r.
      iApply (isim_mono_knowledge with "[ISIM W IST]").
      - instantiate (1:=r). et.
      - instantiate (1:=g). ii. destruct sti_src, sti_tgt. iIntros "G". iModIntro. 
        iApply H0. et.
      - iApply "ISIM"; iFrame.
    }

    force_l. instantiate (1:=false). steps_l. unfold ccallU. force_l. iSplitR; et.
    unfold HoareCall. steps_l. forces_l. iSplitL "W"; et.
    call "IST"; et. iModIntro. steps_l. iDestruct "ASM" as "(W & % & %)". subst; hss. steps_r. hss. steps_r. steps_l.

    rewrite !unfold_iter_eq. grind. prep. prep. by_coind "CIH"; iFrame; et.

    Unshelve. all: ss.
  Qed.

  Lemma isim_myield_tgt_hh
    fl fr Ist r g {R} RR my_tid ps pt nths st_src st_tgt k_src k_tgt scp_src scp_tgt invspc stb univ
    (SPC: stb SchName.yield = Some (SchAS.yield_spec univ))
    :
    bi_entails
      ((Ist nths st_src st_tgt) ∗
      (∀ nths0 st_src0 st_tgt0,
        (Ist nths0 st_src0 st_tgt0)
        -∗ @isim Σ fl fr Ist my_tid false r g R RR false true nths0 
              (st_src0, (HModSem.sandbox scp_src (interp_smod invspc stb (Sch.yield))) >>= k_src) 
              (st_tgt0, k_tgt tt)))
      (isim fl fr Ist my_tid false r g RR ps pt nths 
        (st_src, (HModSem.sandbox scp_src (interp_smod invspc stb (Sch.yield))) >>= k_src) 
        (st_tgt, (HModSem.sandbox scp_tgt (interp_smod invspc stb (Sch.yield))) >>= k_tgt)).
  Proof.
    iIntros "[IST ISIM]". rewrite !/Sch.yield. unseal "Sch".
    rewrite !unfold_iter_eq. grind. prep. iApply isim_reset.
    iStopProof. revert st_tgt.
    combine_quant st_src.
    combine_quant nths.
    combine_quant ps.
    combine_quant pt.
    eapply isim_coind. ii. destruct a as [pt [ps [nths [st_src st_tgt]]]].
    iIntros "((IST & ISIM) & #CIH)".

    grind. prep. iApply isim_reset. steps_r. destruct q.
    {
      steps_r.
      iApply (isim_mono_knowledge with "[ISIM IST]").
      - instantiate (1:=r). et.
      - instantiate (1:=g). ii. destruct sti_src, sti_tgt. iIntros "G". iModIntro. 
        iApply H0. et.
      - iApply "ISIM"; iFrame.
    }

    steps_r. inv SPC. ss. unfold precond. ss. iDestruct "GRT" as "[W %]". des; subst; hss.

    force_l. instantiate (1:=false). steps_l. unfold ccallU. force_l. iSplitR; et.
    unfold HoareCall. steps_l. forces_l. iSplitL "W"; et.
    call "IST"; et. iModIntro.
    
    steps_l. iDestruct "ASM" as "(W & % & %)". subst; hss. steps_r. hss. steps_r. steps_l.

    forces_r. iSplitL "W"; et. steps_r. hss. steps_r.

    rewrite !unfold_iter_eq. grind. prep. prep. by_coind "CIH"; iFrame; et.

    Unshelve. all: ss.
  Qed.

  Lemma isim_myield_src
    fl fr Ist r g {R} RR my_tid ps pt nths st_src st_tgt k_src i_tgt scp_src invspc stb univ
    (SPC: stb SchName.yield = Some (SchAS.yield_spec univ))
    :
    bi_entails
      (((Ist nths st_src st_tgt) ∗ (∃ n, closed_universe univ n ⊤)) ∗
      (∀ nths0 st_src0 st_tgt0,
        ((Ist nths0 st_src0 st_tgt0) ∗ (∃ n, closed_universe univ n ⊤))
        -∗ @isim Σ fl fr Ist my_tid false r g R RR true false nths0 
              (st_src0, k_src tt) 
              (st_tgt0, i_tgt)))
      (isim fl fr Ist my_tid false r g RR ps pt nths 
        (st_src, (HModSem.sandbox scp_src (interp_smod invspc stb (Sch.yield))) >>= k_src) 
        (st_tgt, i_tgt)).
  Proof.
    iIntros "[[IST W] ISIM]". rewrite !/Sch.yield. unseal "Sch".
    rewrite !unfold_iter_eq. grind. prep. iApply isim_reset.
    force_l. instantiate (1:=true). steps_l. iApply "ISIM"; iFrame.
  Qed.

  (* Sch.join lemmas *)
  Lemma isim_mjoin_hp
    fl fr Ist r g {R} RR my_tid ps pt nths st_src st_tgt RT (k_src k_tgt: RT → itree hmodE R) scp_src scp_tgt invspc tid sk
    (StbSch: Sk.t → string → option fspec) (univ: positive) (postS: SAny.t → {n & SRFSyn.t n})
    (FINDS: StbSch sk SchName.join = Some (SchAS.join_spec univ))
    :
      (((Ist nths st_src st_tgt) ∗ (∃ n, closed_universe univ n ⊤) ∗ (SchAS.token_th tid postS)) ∗
      (∀ nths0 st_src0 st_tgt0 (ret: RT),
        ((Ist nths0 st_src0 st_tgt0) ∗ (∃ n, closed_universe univ n ⊤) ∗ (interp_cond (postS ret↑↑)))
        -∗ @isim Σ fl fr Ist my_tid false r g R RR true true nths0 
              (st_src0, k_src ret)
              (st_tgt0, k_tgt ret)))
    ⊢
      (isim fl fr Ist my_tid false r g RR ps pt nths 
        (st_src, (HModSem.sandbox scp_src (interp_smod invspc (StbSch sk) (Sch.join RT tid))) >>= k_src)
        (st_tgt, (HModSem.sandbox scp_tgt (PModSem.interp (Sch.join RT tid))) >>= k_tgt)).
  Proof.
    iIntros "[(IST & W & TKN) ISIM]". rewrite !/Sch.join !/ccallU. unseal "Sch".
    force_l. iSplitR; et. unfold HoareCall. steps_l. force_l (tid, postS).
    force_l (tid↑). force_l. iSplitL "TKN W"; iFrame; et.
    call "IST"; et. iModIntro.
    
    steps_l. steps_r. iDestruct "ASM" as "(W & [% [% POST]] & %)". des; subst; hss.
    steps_r. apply SAny.downcast_upcast in G0. r in G0. subst.
    rewrite SAny.upcast_downcast. hss. steps_r.
    
    iApply "ISIM". iFrame.
  Qed.

  Lemma isim_mjoin_hh
    fl fr Ist r g {R} RR my_tid ps pt nths st_src st_tgt RT (k_src k_tgt: RT → itree hmodE R) scp_src scp_tgt invspc_src invspc_tgt (sk: Sk.t) univ stb_src stb_tgt tid
    (JOINS: stb_src sk SchName.join = Some (SchAS.join_spec univ))
    (JOINT: stb_tgt sk SchName.join = Some (SchAS.join_spec univ))
    :
      ((Ist nths st_src st_tgt) ∗
      (∀ nths0 st_src0 st_tgt0 (ret: RT),
        (Ist nths0 st_src0 st_tgt0)
        -∗ @isim Σ fl fr Ist my_tid false r g R RR true true nths0 
              (st_src0, k_src ret)
              (st_tgt0, k_tgt ret)))
    ⊢
      (isim fl fr Ist my_tid false r g RR ps pt nths 
        (st_src, (HModSem.sandbox scp_src (interp_smod invspc_src (stb_src sk) (Sch.join RT tid)))>>= k_src)
        (st_tgt, (HModSem.sandbox scp_tgt (interp_smod invspc_tgt (stb_tgt sk) (Sch.join RT tid))) >>= k_tgt)).
  Proof.
    iIntros "[IST ISIM]". rewrite !/Sch.join !/ccallU. unseal "Sch".
    
    steps_r. inv JOINT. ss. iDestruct "GRT" as "[W PRE]". unfold precond. hss.
    destruct q0. ss. iDestruct "PRE" as "[[% TKN] %]". des; subst; hss.

    forces_l. iSplit; et. steps_l. force_l (n, o). forces_l. iSplitL "TKN W"; iFrame; et.
    
    call "IST"; et. iModIntro.

    steps_l. iDestruct "ASM" as "[W [[% [% POST]] %]]". subst; hss.
    apply SAny.downcast_upcast in G1. r in G1. subst.

    forces_r. iSplitL "POST W". { iFrame; et. }
    steps_r. hss. steps_r. rewrite SAny.upcast_downcast. hss. steps_r.
    iApply "ISIM". iFrame.
  Qed.

End MACROAUX.

Ltac _prep_macro_l :=
  prep; match goal with
  | [|- context[interp_smod _ _ (Sch.spawn _ >>= _)]] =>
      rewrite// [in (interp_smod _ _ (Sch.spawn _ >>= _))] SModRed.interp_bind; _prep_macro_l
  | [|- context[HModSem.sandbox _ (interp_smod _ _ (Sch.spawn _) >>= _)]] =>
      rewrite// [in HModSem.sandbox _ (interp_smod _ _ (Sch.spawn _) >>= _)] HModSB.transl_bind
  | [|- context[interp_smod _ _ (Sch.yield >>= _)]] =>
      rewrite// [in (interp_smod _ _ (Sch.yield >>= _))] SModRed.interp_bind; _prep_macro_l
  | [|- context[HModSem.sandbox _ (interp_smod _ _ (Sch.yield) >>= _)]] =>
      rewrite// [in HModSem.sandbox _ (interp_smod _ _ (Sch.yield) >>= _)] HModSB.transl_bind
  | [|- context[interp_smod _ _ (Sch.join _ _ >>= _)]] =>
      rewrite// [in (interp_smod _ _ (Sch.join _ _ >>= _))] SModRed.interp_bind; _prep_macro_l
  | [|- context[HModSem.sandbox _ (interp_smod _ _ (Sch.join _ _) >>= _)]] =>
      rewrite// [in HModSem.sandbox _ (interp_smod _ _ (Sch.join _ _) >>= _)] HModSB.transl_bind
  end; prep.

Ltac _prep_macro_r :=
  prep; match goal with
  | [|- context[PModSem.interp (Sch.spawn _ >>= _)]] =>
      rewrite// [in (PModSem.interp (Sch.spawn _ >>= _))] PModRed.interp_bind; _prep_macro_r
  | [|- context[HModSem.sandbox _ (PModSem.interp (Sch.spawn _) >>= _)]] =>
      rewrite// [in HModSem.sandbox _ (PModSem.interp (Sch.spawn _) >>= _)] HModSB.transl_bind
  | [|- context[PModSem.interp (Sch.yield >>= _)]] =>
      rewrite// [in (PModSem.interp (Sch.yield >>= _))] PModRed.interp_bind; _prep_macro_r
  | [|- context[HModSem.sandbox _ (PModSem.interp (Sch.yield) >>= _)]] =>
      rewrite// [in HModSem.sandbox _ (PModSem.interp (Sch.yield) >>= _)] HModSB.transl_bind
  | [|- context[PModSem.interp (Sch.join _ _ >>= _)]] =>
      rewrite// [in (PModSem.interp (Sch.join _ _ >>= _))] PModRed.interp_bind; _prep_macro_r
  | [|- context[HModSem.sandbox _ (PModSem.interp (Sch.join _ _) >>= _)]] =>
      rewrite// [in HModSem.sandbox _ (PModSem.interp (Sch.join _ _) >>= _)] HModSB.transl_bind
  end; prep.

Ltac prep_macro :=
  let marker := fresh "MARKER" in
  hide_itree_r marker; try _prep_macro_l; show_itree marker;
  hide_itree_l marker; try _prep_macro_r; show_itree marker.

Ltac yield_r hyps :=
  prep_macro;
  first [
    iApply isim_myield_tgt_hp; des_pairs; s;
    [|iSplitL hyps; [|iIntros "% % %"; iIntrosFresh "[IST W]"]] |
    iApply isim_myield_tgt_hh; des_pairs; s;
    [|iSplitL hyps; [|iIntros "% % %"; iIntrosFresh "IST"]]].

Ltac yield_l hyps :=
  prep_macro;
  iApply isim_myield_src; des_pairs; s;
  [|iSplitL hyps; [ |iIntros "% % %"; iIntrosFresh "[IST W]"]].

Ltac spawn hyps :=
  prep_macro;
  first [
    iApply isim_mspawn_hp; des_pairs; s;
    [| | |iSplitL hyps; [|iIntros "% % % %"; iIntrosFresh "[IST [W TKN]]"]] |
    iApply isim_mspawn_hh; des_pairs; s;
    [| | |iSplitL hyps; [|iIntros "% % % %"; iIntrosFresh "IST"]]].

Ltac join hyps :=
  prep_macro;
  first [
    iApply isim_mjoin_hp; des_pairs; s;
    [|iSplitL hyps; [|iIntros "% % % %"; iIntrosFresh "[IST [W POST]]"]] |
    iApply isim_mjoin_hh; des_pairs; s;
    [| |iSplitL hyps; [|iIntros "% % % %"; iIntrosFresh "IST"]]]. *)
