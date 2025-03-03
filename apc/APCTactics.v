Require Import CRIS.
Require Import APCHeader APC APCA.
Require Import NormITree.

Set Implicit Arguments.

Import APC.

(* useful apc lemmas - require IST *)

Lemma isim_apc_src `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}
  contextual fl fr Ist r g {Rs Rt} RR ps pt nths st_src st_tgt k_src i_tgt u spc spc_pure
  scopes (ow od: Ord.t)
  :
    (@isim Σ contextual fl fr Ist r g Rs Rt RR true pt nths
      (st_src, k_src ())
      (st_tgt, i_tgt))
  ⊢
    (@isim Σ contextual fl fr Ist r g Rs Rt RR ps pt nths 
      (st_src, ((HMod.sandbox scopes (interp_smod (wsim_ginv u ⊤) spc (_APC od spc_pure ow))) >>= k_src))
      (st_tgt, i_tgt)).
Proof.
  iIntros "ISIM".
  rewrite unfold_APC. force_l true. steps_l.
  iFrame.
Qed.

Lemma isim_apc_tgt `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}
  contextual fl fr Ist r g {Rs Rt} RR ps pt nths st_src st_tgt i_src i_tgt u spc spc_pure
  scopes (ow_src ow_tgt od_src od_tgt : Ord.t)
  (WIDTH: (ow_tgt < ow_src)%ord)
  (DEPTH: (od_tgt <= od_src)%ord)
  :
    ((Ist nths st_src st_tgt) ∗
      (∀ nths0 st_src0 st_tgt0 ow_src_nxt,
        (Ist nths0 st_src0 st_tgt0)
        -∗ @isim Σ contextual fl fr Ist r g Rs Rt RR false false nths0
            (st_src0, ((HMod.sandbox scopes (interp_smod (wsim_ginv u ⊤) spc (_APC od_src spc_pure ow_src_nxt)));;; i_src))
            (st_tgt0, i_tgt)))
  ⊢
    (@isim Σ contextual fl fr Ist r g Rs Rt RR ps pt nths 
      (st_src, ((HMod.sandbox scopes (interp_smod (wsim_ginv u ⊤) spc (_APC od_src spc_pure ow_src)));;; i_src))
      (st_tgt, ((HMod.sandbox scopes (interp_smod (wsim_ginv u ⊤) spc (_APC od_tgt spc_pure ow_tgt)));;; i_tgt))).
Proof.
  iIntros "[IST ISIM]". iApply isim_reset. iStopProof.
  revert nths st_src. apply combine_quant.
  revert WIDTH. apply combine_quant.
  revert st_tgt. apply combine_quant.
  revert ow_src. apply combine_quant_dep.
  revert ow_tgt. apply combine_quant_dep.
  apply isim_coind. i. iIntros "[[IST ISIM] #CIH]".
  destruct a as [ow_tgt [ow_src [st_tgt [WIDTH [nths st_src]]]]]; ss.
  set_marker marker. hide_ihyps. hide_itree_l.
  rewrite !unfold_APC.
  show_until marker.
  steps_r. des_ifs.
  { (* break *)
    steps_r. iApply isim_reset. iPoseProof ("ISIM" $! nths st_src st_tgt ow_src) as "ISIM".
    iApply (isim_mono_knowledge with "[ISIM IST CIH]").
    { instantiate (1:=r). et. }
    { instantiate (1:=g). ii. destruct sti_src, sti_tgt. iIntros "G". iModIntro. iApply H; iFrame. }
    iApply "ISIM"; iFrame.
  }
  { (* continue *)
    steps_r. set_marker marker. hide_ihyps. hide_itree_r.
    rewrite !unfold_APC. show_until marker.
    
    force_l false. steps_l. force_l ow_tgt. steps_l.
    force_l WIDTH. steps_l. force_l q1. steps_l. force_l q2. steps_l.
    assert (PO: is_Some (spc_pure q1) ∧ (q2 < od_src)%ord).
    { des. split; eauto. eapply Ord.lt_le_lt; eauto. }
    unfold guarantee. force_l PO. steps_l. force_l. iSplitR; et.
    steps_l. force_l q4. force_l q5. force_l. iSplitL "GRT"; et.
    call "IST"; iFrame.
    steps_l. forces_r. iSplitL "ASM"; iFrame. steps_r.
    ITacticsCore.by_coind "CIH".
    iFrame.
  }
  Unshelve. eauto.
Qed.

Lemma isim_apc_src_call_tgt `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}
  contextual fl fr Ist r g {Rs Rt} RR ps pt nths st_src st_tgt k_src k_tgt u spc spc_pure
  scopes fn args fsp (spec_arg: meta fsp) (ow_src ow_fn od_src od_fn : Ord.t)
  (WIDTH: (ow_fn < ow_src)%ord)
  (DEPTH: (od_fn < od_src)%ord)
  (SpcPureInSpc: spc_sub spc_pure spc)
  (fnInSpcPure: spc_pure fn = Some fsp)
  :
  (((precond fsp spec_arg od_fn ↑ args) ∗ (Ist nths st_src st_tgt)) ∗
    (∀ nths0 st_src0 st_tgt0 vret ret,
      (Ist nths0 st_src0 st_tgt0) ∗ (postcond fsp spec_arg vret ret) 
      -∗ @isim Σ contextual fl fr Ist r g Rs Rt RR false false nths0
          (st_src0, ((HMod.sandbox scopes (interp_smod (wsim_ginv u ⊤) spc (_APC od_src spc_pure ow_fn))) >>= k_src))
          (st_tgt0, k_tgt ret)))
  ⊢
    (@isim Σ contextual fl fr Ist r g Rs Rt RR ps pt nths 
      (st_src, ((HMod.sandbox scopes (interp_smod (wsim_ginv u ⊤) spc (_APC od_src spc_pure ow_src))) >>= k_src))
      (st_tgt, (trigger (Call fn args) >>= k_tgt))).
Proof.
  iIntros "[[PRE IST] ISIM]".
  rewrite (unfold_APC _ _ ow_src). force_l false. steps_l.
  force_l ow_fn. steps_l. force_l WIDTH. steps_l.
  force_l fn. steps_l. force_l od_fn. steps_l.
  assert (PO: (is_Some (spc_pure fn) ∧ (od_fn < od_src)%ord)); et.
  unfold guarantee. force_l PO. steps_l.
  assert (spc fn = Some fsp); et. force_l. iSplit; et.
  steps_l.
  force_l spec_arg.
  force_l args.
  force_l. iSplitL "PRE"; et.
  call "IST"; et. steps_r. steps_l.
  iApply isim_reset.
  iApply "ISIM". iFrame.
Qed.

Lemma isim_apc_src_call_tgt_weaker `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}
  contextual fl fr Ist r g {Rs Rt} RR ps pt nths st_src st_tgt k_src k_tgt u spc spc_pure
  scopes fn args fsp' fsp (spec_arg: meta fsp) o P Q (ow_src ow_fn od_src od_fn : Ord.t)
  (WIDTH: (ow_fn < ow_src)%ord)
  (DEPTH: (od_fn < od_src)%ord)
  (SpcPureInSpc: spc_sub spc_pure spc)
  (fnInSpcPure: spc_pure fn = Some fsp')
  (WEAK: fspec_weaker fsp fsp')
  (fspIsfspecapc: fsp = @fspec_apc _ (meta fsp) o (λ x, (P x, Q x)))
  :
  (((precond fsp spec_arg od_fn ↑ args) ∗ (Ist nths st_src st_tgt)) ∗
    (∀ nths0 st_src0 st_tgt0 vret ret,
      (Ist nths0 st_src0 st_tgt0) ∗ (postcond fsp spec_arg vret ret)
      -∗ @isim Σ contextual fl fr Ist r g Rs Rt RR false false nths0
          (st_src0, ((HMod.sandbox scopes (interp_smod (wsim_ginv u ⊤) spc (_APC od_src spc_pure ow_fn))) >>= k_src))
          (st_tgt0, k_tgt ret)))
  ⊢
    (@isim Σ contextual fl fr Ist r g Rs Rt RR ps pt nths
      (st_src, ((HMod.sandbox scopes (interp_smod (wsim_ginv u ⊤) spc (_APC od_src spc_pure ow_src))) >>= k_src))
      (st_tgt, (trigger (Call fn args) >>= k_tgt))).
Proof.
  iIntros "[[PRE IST] ISIM]".
  rewrite (unfold_APC _ _ ow_src). force_l false. steps_l.
  force_l ow_fn. steps_l. force_l WIDTH. steps_l.
  force_l fn. steps_l. force_l od_fn. steps_l.
  assert (PO: (is_Some (spc_pure fn) ∧ (od_fn < od_src)%ord)); et.
  unfold guarantee. force_l PO. steps_l.
  assert (spc fn = Some fsp'); et. force_l. iSplit; et.
  steps_l.
  specialize (WEAK spec_arg). des.
  force_l x_tgt.
  force_l args.
  iPoseProof ((PRE od_fn ↑ args) with "PRE") as ">PRE".
  force_l. iSplitL "PRE"; et.
  call "IST"; et. steps_r. steps_l.
  iPoseProof ((POST q vret) with "ASM") as ">POST".
  iApply isim_reset.
  iApply "ISIM". iFrame.
Qed.

(* useful apc lemmas cont. - don't require IST *)

Lemma isim_apc_tgt_noist `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}
  contextual fl fr Ist r g {Rs Rt} RR ps pt nths st_src st_tgt i_src i_tgt u
  (spc spc_pure: string → option fspec) (od ow: Ord.t) (scopes: list string)
  (SUB: spc_sub spc_pure spc)
  (SUBA: spc_incl APCA.Spc spc)
  (FIND: alist_find APCName.apc fr = Some (HMod.sandbox_body (APCA.scopes, interp_sb_hp (wsim_ginv u ⊤) spc
      {| fsb_fspec := APCA.apc_spec; fsb_body := cfunN (APCA.apc_body spc_pure) |})))
  (BODY: ∀ fn fsp, spc_pure fn = Some fsp 
          → ∃ scopes, alist_find fn fr = Some (pure_specbody scopes u spc fsp))
  :
    (@isim Σ contextual fl fr Ist r g Rs Rt RR false false nths
      (st_src, i_src)
      (st_tgt, i_tgt))
  ⊢
    (@isim Σ contextual fl fr Ist r g Rs Rt RR ps pt nths 
      (st_src, i_src)
      (st_tgt, ((HMod.sandbox scopes (interp_smod (wsim_ginv u ⊤) spc (_APC od spc_pure ow)));;; i_tgt))).
Proof.
  iIntros "ISIM".

  set (E:=environments.envs_entails _).
  apply isim_congruence_src with (Ret ();;; i_src).
  { rewrite bind_ret_l. refl. }
  subst E.
  iApply isim_bind. iSplitR; cycle 1.
  { iIntros (? ? ? ? ?) "IST".
    instantiate (1:=(λ nths0 '(st_src0, ret_src) '(st_tgt0, ret_tgt),
      ⌜nths0 = nths ∧ st_src0 = st_src ∧ st_tgt0 = st_tgt⌝)%I).
    iDestruct "IST" as "%"; des; subst; hss.
  }

  (* well founded induction on depth ordinal *)
  iApply isim_reset. iStopProof.
  generalize scopes.
  revert ow. pattern od. set (GOAL:=λ _, _).
  revert od. apply (well_founded_induction Ord.lt_well_founded).
  i. subst GOAL. ss. iIntros (? ?) "_".

  (* well founded induction on width ordinal *)
  iApply isim_reset. iStopProof.
  (* generalize st_tgt0 st_src0 nths0. *)
  pattern ow. set (GOAL:=λ _, _).
  revert ow. apply (well_founded_induction Ord.lt_well_founded).
  i. subst GOAL. ss. iIntros "_".

  rewrite unfold_APC. steps_r. des_ifs.
  { (* break *)
    step. iPureIntro. split; et.
  }
  { (* continue *)
    steps_r.      
    unfold is_Some in *. des. dup grt. apply BODY in grt. des.
    inline_r.
    unfold pure_specbody, interp_sb_hp; ss. steps_r.
    unfold pure_specbody, interp_sb_hp in q3; ss.
    apply SUB in grt1. rewrite grt1 in G. inv G.
    unfold HoareFun. steps_r. force_r q4. steps_r.
    forces_r. iSplitL "GRT"; et.
    steps_r. unfold pure_body, cfunN. hss. steps_r.
    iDestruct "GRT" as "%"; des; subst; hss.
    inline_r.
    unfold HMod.sandbox_body, interp_sb_hp, HoareFun; hss.
    steps_r. force_r q6. force_r (q6↑). forces_r. iSplitR; et. hss.
    steps_r. hss. unfold APCA.apc_body, APC. steps_r.

    bind_expand_r.
    apply isim_congruence_src with (Ret ();;; Ret ()).
    { rewrite bind_ret_l. refl. }
    iApply isim_bind. iSplitL.
    { iApply isim_reset. iStopProof. eapply H. eauto. }

    iIntros (? ? ? ? ?) "IST". iDestruct "IST" as "%"; des; subst; hss.
    steps_r. forces_r. iSplitL; iFrame.
    steps_r. forces_r. iSplitL; iFrame.
    steps_r. iApply isim_reset. iStopProof. eapply H0. eauto.
  }
  Unshelve. eauto.
Qed.

Ltac _prep_macro :=
  ired;
  match goal with
  | [|- context[HMod.sandbox _ (interp_smod _ _ (_APC _ _ _)) >>= _]] => fail 1
  | [|- context[HMod.sandbox _ (interp_smod _ _ (_APC _ _ _) >>= _)]] =>
      rewrite// [in HMod.sandbox _ (interp_smod _ _ (_APC _ _ _) >>= _)] SBRed.bind
  | [|- context[interp_smod _ _ (_APC _ _ _ >>= _)]] =>
      rewrite// [in (interp_smod _ _ (_APC _ _ _ >>= _))] SRed.bind; _prep_macro
  | [|- context[HMod.sandbox _ (PMod.interp (_APC _ _ _)) >>= _]] => fail 1
  | [|- context[HMod.sandbox _ (PMod.interp (_APC _ _ _) >>= _)]] =>
      rewrite// [in HMod.sandbox _ (PMod.interp (_APC _ _ _) >>= _)] SBRed.bind
  | [|- context[PMod.interp (_APC _ _ _ >>= _)]] =>
      rewrite// [in (PMod.interp (_APC _ _ _ >>= _))] PRed.bind; _prep_macro
  end.

Ltac prep_macro_l :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_r;
  try _prep_macro; ired;
  show_until marker.  

Ltac prep_macro_r :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_l;
  try _prep_macro; ired;
  show_until marker.

Ltac prep_macro :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_r; try _prep_macro; ired; show_itree;
  hide_itree_l; try _prep_macro; ired; show_itree;
  show_until marker.

Ltac apc_l :=
  prep_macro_l;
  iApply isim_apc_src; des_pairs; s.

Ltac apc_r hyps :=
  prep_macro_r;
  iApply isim_apc_tgt; des_pairs; s;
  [| |iSplitL hyps; [|iIntros "% % % %"; iIntrosFresh "IST"]].

Ltac apc_call hyps :=
  prep_macro_l; (hrepeat do 1 hnorm_r);
  iApply isim_apc_src_call_tgt; des_pairs; s;
  [| | | |iSplitL hyps; [ |iIntros "% % % % %"; iIntrosFresh "ISTPOST"]].

Ltac apc_call_weaker hyps :=
  prep_macro_l; (hrepeat do 1 hnorm_r);
  iApply isim_apc_src_call_tgt_weaker; des_pairs; s;
  [| | | | | | iSplitL hyps; [ |iIntros "% % % % %"; iIntrosFresh "ISTPOST"]].

Ltac apc_tgt_noist :=
  prep_macro_r;
  iApply isim_apc_tgt_noist; des_pairs; s.
