Require Import CRIS.
Require Import APCHeader APC APCA.

Set Implicit Arguments.

Import APC.

(* useful apc lemmas - require IST *)

Section LEMMAS.

Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

Lemma wsim_apc_src
    fl fr Ist cP r g {Rs Rt} RR ps pt nths st_src st_tgt k_src i_tgt sp sp_pure
    img mask scopes (ow od: Ord.t) :
  wsim fl fr Ist cP r g Rs Rt RR true pt nths (st_src, k_src ()) (st_tgt, i_tgt) ⊢
  wsim fl fr Ist cP r g Rs Rt RR ps pt nths
    (st_src, ((SB.sandbox img mask scopes (SModTr.trans sp (_APC od sp_pure ow))) >>= k_src))
    (st_tgt, i_tgt).
Proof using.
  iIntros "ISIM". rewrite unfold_APC. force_l true. steps_l. iFrame.
Qed.

(*
Lemma wsim_apc_tgt
  fl fr Ist is_closed u0 u1 r g {Rs Rt} RR ps pt nths st_src st_tgt i_src i_tgt sp sp_pure
  scopes (ow_src ow_tgt od_src od_tgt : Ord.t)
  (WIDTH: (ow_tgt < ow_src)%ord)
  (DEPTH: (od_tgt <= od_src)%ord)
  :
    ((Ist nths st_src st_tgt) ∗
      (∀ nths0 st_src0 st_tgt0 ow_src_nxt,
        (Ist nths0 st_src0 st_tgt0)
        -∗ wsim fl fr Ist is_closed u0 u1 ⊤ r g Rs Rt RR false false nths0
            (st_src0, ((HMod.sandbox scopes (interp_smod sp (_APC od_src sp_pure ow_src_nxt)));;; i_src))
            (st_tgt0, i_tgt)))
  ⊢
    (wsim fl fr Ist is_closed u0 u1 ⊤ r g Rs Rt RR ps pt nths 
      (st_src, ((HMod.sandbox scopes (interp_smod sp (_APC od_src sp_pure ow_src)));;; i_src))
      (st_tgt, ((HMod.sandbox scopes (interp_smod sp (_APC od_tgt sp_pure ow_tgt)));;; i_tgt))).
Proof using.
  iIntros "[IST ISIM]". iApply wsim_reset.
  iStopProof.
  revert nths st_src. apply combine_quant.
  revert WIDTH. apply combine_quant.
  revert st_tgt. apply combine_quant.
  revert ow_src. apply combine_quant_dep.
  revert ow_tgt. apply combine_quant_dep.
  eapply wsim_coind. i. iIntros "(IST & ISIM) %MON #CIH".
  destruct a as [ow_tgt [ow_src [st_tgt [WIDTH [nths st_src]]]]]; ss.
  destruct_quant.
  set_marker marker. hide_ihyps. only_itree_r.
  rewrite !unfold_APC.
  show_until marker.
  steps_r. des_ifs.
  { (* break *)
    steps_r. iApply wsim_reset. iPoseProof ("ISIM" $! nths st_src st_tgt ow_src) as "ISIM".
    rewrite wsim.wsim_eq /wsim.wsim_def /wsim.wsim_pre. iIntros "W".
    iApply (isim_mono_knowledge with "[ISIM IST CIH W]").
    { et. }
    { instantiate (1:=g). ii. destruct sti_src, sti_tgt. iIntros "G". iModIntro. rewrite /wsim.wsim_rel. iDestruct "G" as "[I G]". iFrame. iApply MON; iFrame. }
    iApply ("ISIM" with "IST"); iFrame.
  }
  { (* continue *)
    w_steps_r. set_marker marker. hide_ihyps. only_itree_l.
    rewrite !unfold_APC. show_until marker.
    
    w_force_l false. w_steps_l. w_force_l ow_tgt. w_steps_l.
    w_force_l WIDTH. w_steps_l. w_force_l q1. w_steps_l. w_force_l q2. w_steps_l.
    assert (PO: is_Some (sp_pure q1) ∧ (q2 < od_src)%ord).
    { des. split; eauto. eapply Ord.lt_le_lt; eauto. }
    unfold guarantee. w_force_l PO. w_steps_l.
    destruct (sp q1). 2:{ w_steps_r. des_ifs. }
    hss. w_steps_l. w_steps_r. w_force_l.
    w_steps_l. w_force_l q4. w_steps_l. w_force_l. iSplitL "GRT"; et. w_steps_l.
    w_call "IST"; iFrame.
    w_steps_l. w_forces_r. iSplitL "ASM"; iFrame. w_steps_r.
    by_coind "CIH".
    iFrame.
  }
  Unshelve. eauto.
Qed.
*)

Lemma wsim_apc_src_call_tgt_weaker
  fl fr Ist Ep r g {Rs Rt} RR ps pt nths st_src st_tgt k_src k_tgt sp sp_pure
  img_t (msk_s msk_t:_→bool) sc_s sc_t (fn: string) args fsp' fsp X (spec_arg: X) o P Q (ow_src ow_fn od_src od_fn : Ord.t)
  (WIDTH: (ow_fn < ow_src)%ord)
  (DEPTH: (od_fn < od_src)%ord)
  (SpPureInSp: sp_incl sp_pure sp)
  (fnInSpPure: alist_find (Some fn) sp_pure = Some (Some fsp'))
  (WEAK: fspec_imply fsp' fsp)
  (fspIsfspecapc: fsp = (@fspec_apc Σ X o (λ x, (P x, Q x))))
  :
  msk_s fn → msk_t fn →
  (((P spec_arg args ∗ ⌜∃ vo : Ord.t, od_fn ↑ = vo ↑ ∧ (o spec_arg <= vo)%ord⌝) ∗ (Ist nths st_src st_tgt)) ∗
    (∀ nths0 st_src0 st_tgt0 (vret ret: Any.t),
      ((Ist nths0 st_src0 st_tgt0) ∗ (Q spec_arg ret))
      -∗ wsim fl fr Ist Ep r g Rs Rt RR false false nths0
          (st_src0, ((SB.sandbox true msk_s sc_s (SModTr.trans sp (_APC od_src sp_pure ow_fn))) >>= k_src))
          (st_tgt0, k_tgt ret)))
  ⊢
    wsim fl fr Ist Ep r g Rs Rt RR ps pt nths
      (st_src, (SB.sandbox true msk_s sc_s (SModTr.trans sp (_APC od_src sp_pure ow_src))) >>= k_src)
      (st_tgt, (SB.sandbox img_t msk_t sc_t (trigger (Call fn args))) >>= k_tgt).
Proof using.
  i. iIntros "[[[PRE %] IST] ISIM]".
  des. set_marker m. hide_ihyps. rewrite unfold_APC. show_until m.
  force_l false. steps_l. force_l ow_fn. steps_l. force_l WIDTH. steps_l.
  force_l fn. steps_l. force_l od_fn. steps_l.
  assert (PO: (is_Some (alist_find (Some fn) sp_pure) ∧ (od_fn < od_src)%ord)); et. 
  unfold guarantee. force_l PO. steps_l.
  assert (sp fn = Some fsp').
  { apply SpPureInSp. eauto. }
  rewrite H3. des. rewrite /fspec_imply in WEAK. hss.
  specialize (WEAK spec_arg). des.
  force_l x0. force_l args. steps_l.
  iPoseProof ((PRE vo ↑ args) with "[PRE]") as ">PRE". { unfold precond, fspec_apc; ss. iFrame. by iExists _. }
  iApply wsim_guarantee_src. iFrame. steps_l.

  call "IST"; et.
  steps_l. iApply wsim_reset.
  iPoseProof ((POST q ret) with "ASM") as ">POST".
  iSpecialize ("ISIM" $! nths' st_s' st_t' q ret).
  iApply "ISIM". iFrame.
Qed.

Lemma wsim_apc_src_call_tgt
  fl fr Ist cP r g {Rs Rt} RR ps pt nths st_src st_tgt k_src k_tgt sp (sp_pure : spl_type)
  img_t (msk_s msk_t:_→bool) sc_s sc_t fn args fsp X (spec_arg: X) o P Q (ow_src ow_fn od_src od_fn : Ord.t)
  (WIDTH: (ow_fn < ow_src)%ord)
  (DEPTH: (od_fn < od_src)%ord)
  (SpPureInSp: sp_incl sp_pure sp)
  (fnInSpPure: alist_find (Some fn) sp_pure = Some (Some fsp))
  (fspIsfspecapc: fsp = (@fspec_apc Σ X o (λ x, (P x, Q x))))
  :
  msk_s fn → msk_t fn →
  (((P spec_arg args ∗ ⌜∃ vo : Ord.t, od_fn ↑ = vo ↑ ∧ (o spec_arg <= vo)%ord⌝) ∗ (Ist nths st_src st_tgt)) ∗
    (∀ nths0 st_src0 st_tgt0 (vret ret: Any.t),
      ((Ist nths0 st_src0 st_tgt0) ∗ (Q spec_arg ret))
      -∗ wsim fl fr Ist cP r g Rs Rt RR false false nths0
          (st_src0, ((SB.sandbox true msk_s sc_s (SModTr.trans sp (_APC od_src sp_pure ow_fn))) >>= k_src))
          (st_tgt0, k_tgt ret)))
  ⊢
    wsim fl fr Ist cP r g Rs Rt RR ps pt nths
      (st_src, (SB.sandbox true msk_s sc_s (SModTr.trans sp (_APC od_src sp_pure ow_src))) >>= k_src)
      (st_tgt, (SB.sandbox img_t msk_t sc_t (trigger (Call fn args))) >>= k_tgt).
Proof using.
  eapply wsim_apc_src_call_tgt_weaker; et. 
  do 2 (econs; et).
Qed.

(* useful apc lemmas cont. - don't require IST *)

(*
Lemma wsim_apc_tgt_noist
  is_closed fl fr Ist u0 u1 cP r g {Rs Rt} RR ps pt nths st_src st_tgt i_src i_tgt
  (sp sp_pure: string → option fspec) (od ow: Ord.t) (scopes: list string)
  (SUB: sp_sub sp_pure sp)
  (SUBA: sp_incl APCA.Sp sp)
  (FIND: alist_find APCHdr.apc fr = Some (HModTr.sandbox_body (APCA.scopes, interp_sb_hp (wsim_ginv u0 cP) sp
      {| fsb_fspec := APCA.apc_spec; fsb_body := cfunN (APCA.apc_body sp_pure) |})))
  (BODY: ∀ fn fsp, sp_pure fn = Some fsp 
          → ∃ sc, alist_find fn fr = Some (pure_specbody sc u0 sp fsp))
  :
    (wsim fl fr Ist is_closed u0 u1 cP r g Rs Rt RR false false nths
      (st_src, i_src)
      (st_tgt, i_tgt))
  ⊢
    (wsim fl fr Ist is_closed u0 u1 cP r g Rs Rt RR ps pt nths 
      (st_src, i_src)
      (st_tgt, ((HModTr.sandbox scopes (SModTr.trans (wsim_ginv u1 cP) sp (_APC od sp_pure ow)));;; i_tgt))).
  Proof using.
  iIntros "ISIM".
  set (E:=environments.envs_entails _).
  apply wsim_congruence_src with (Ret ();;; i_src).
  { rewrite bind_ret_l. refl. }
  subst E.
  iApply wsim_bind. iSplitR; cycle 1.
  { iIntros (? ? ? ? ?) "IST".
    instantiate (1:=(λ nths0 '(st_src0, ret_src) '(st_tgt0, ret_tgt),
      ⌜nths0 = nths ∧ st_src0 = st_src ∧ st_tgt0 = st_tgt⌝)%I).
    iDestruct "IST" as "%"; des; subst; hss.
  }

  (* well founded induction on depth ordinal *)
  iApply wsim_reset. iStopProof.
  generalize scopes.
  revert ow. pattern od. set (GOAL:=λ _, _).
  revert od. apply (well_founded_induction Ord.lt_well_founded).
  i. subst GOAL. ss. iIntros (? ?) "_".

  (* well founded induction on width ordinal *)
  iApply wsim_reset. iStopProof.
  (* generalize st_tgt0 st_src0 nths0. *)
  pattern ow. set (GOAL:=λ _, _).
  revert ow. apply (well_founded_induction Ord.lt_well_founded).
  i. subst GOAL. ss. iIntros "_".

  rewrite unfold_APC. steps_r. des_ifs.
  { (* break *)
    steps_r. 
    rewrite wsim.wsim_eq /wsim.wsim_def /wsim.wsim_pre. iIntros "_".
    step. iPureIntro. split; et.
  }
  { (* continue *)
    steps_r.

    unfold is_Some in *. des. dup grt. apply BODY in grt. des.
    apply SUB in grt1. rewrite grt1. hss. steps_r.
    iApply wsim_inline_tgt; eauto.
    unfold pure_specbody, interp_sb_hp; ss. steps_r.
    unfold pure_specbody, interp_sb_hp in q3; ss.
    unfold HoareFun. steps_r. force_r q3. steps_r.
    forces_r. iSplitL "GRT"; et.
    steps_r. unfold pure_body, cfunN. hss. steps_r.
    iDestruct "GRT" as "%"; des; subst; hss.
    iApply wsim_inline_tgt; eauto.
    unfold HModTr.sandbox_body, interp_sb_hp, HoareFun; hss.
    steps_r. force_r q5. force_r (q5↑). forces_r. iSplit; et.
    steps_r. hss. unfold APCA.apc_body, APC. steps_r.

    wbind_expand_r.
    apply wsim_congruence_src with (Ret ();;; Ret ()).
    { rewrite bind_ret_l. refl. }
    iApply wsim_bind. iSplitL.
    { iApply wsim_reset. iStopProof. instantiate (1:=(λ (nths0 : nat) '(st_src0, _) '(st_tgt0, _), ⌜nths0 = nths ∧ st_src0 = st_src ∧ st_tgt0 = st_tgt⌝%I)). specialize (H q5 grt0 q2 APCA.scopes). 
    Unset Printing Notations. move H at bottom. eapply H. eauto. }

    iIntros (? ? ? ? ?) "IST". iDestruct "IST" as "%"; des; subst; hss.
    w_steps_r. w_forces_r. iSplitL; iFrame.
    w_steps_r. w_forces_r. iSplitL; iFrame.
    w_steps_r. iApply wsim_reset. iStopProof. eapply H0. eauto.
  }
  Unshelve. eauto.
Qed.
*)

End LEMMAS.

Ltac _prep_macro :=
  ired;
  match goal with
  | [|- context[SB.sandbox _ _ _ (SModTr.trans _ _ (_APC _ _ _)) >>= _]] => fail 1
  | [|- context[SB.sandbox _ _ _ (SModTr.trans _ _ (_APC _ _ _) >>= _)]] =>
      rewrite// [in SB.sandbox _ _ _ (SModTr.trans _ _ (_APC _ _ _) >>= _)] SBRed.bind
  | [|- context[SModTr.trans _ _ (_APC _ _ _ >>= _)]] =>
      rewrite// [in (SModTr.trans _ _ (_APC _ _ _ >>= _))] SRed.bind; _prep_macro
  end.

Ltac prep_macro_l :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_l;
  try _prep_macro; ired;
  show_until marker.  

Ltac prep_macro_r :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_r;
  try _prep_macro; ired;
  show_until marker.

Ltac prep_macro :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_l; try _prep_macro; ired; show_itree;
  only_itree_r; try _prep_macro; ired; show_itree;
  show_until marker.

Ltac apc_l :=
  prep_macro_l;
  iApply wsim_apc_src; des_pairs; s.

(* Ltac apc_r hyps :=
  prep_macro_r;
  iApply wsim_apc_tgt; des_pairs; s;
  [| |iSplitL hyps; [|iIntros "% % % %"; iIntrosFresh "IST"]]. *)

Ltac apc_call hyps :=
  prep_macro_l; (hrepeat do 1 norm_r);
  iApply wsim_apc_src_call_tgt; des_pairs; s;
  [| | | | |try prove_sb_cond|try prove_sb_cond|iSplitL hyps; [ |iIntros "% % % % %"; iIntrosFresh "ISTPOST"]].

Ltac apc_call_weaker hyps :=
  prep_macro_l; (hrepeat do 1 norm_r);
  iApply wsim_apc_src_call_tgt_weaker; des_pairs; s;
  [| | | | | |try prove_sb_cond|try prove_sb_cond|iSplitL hyps; [ |iIntros "% % % % %"; iIntrosFresh "ISTPOST"]].

(* Ltac apc_tgt_noist :=
  prep_macro_r;
  iApply wsim_apc_tgt_noist; des_pairs; s. *)
