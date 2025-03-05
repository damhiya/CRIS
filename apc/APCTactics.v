Require Import CRIS.
Require Import APCHeader APC APCA.
Require Import NormITree.
Require Import wsim wsim_tactics.

Set Implicit Arguments.

Import APC.

(* useful apc lemmas - require IST *)

Lemma wsim_apc_src `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}
  is_closed fl fr Ist u0 u1 cP r g {Rs Rt} RR ps pt nths st_src st_tgt k_src i_tgt spc spc_pure
  scopes ginv (ow od: Ord.t)
  :
    (wsim fl fr Ist is_closed u0 u1 cP r g Rs Rt RR true pt nths
      (st_src, k_src ())
      (st_tgt, i_tgt))
  ⊢
    (wsim fl fr Ist is_closed u0 u1 cP r g Rs Rt RR ps pt nths
      (st_src, ((HMod.sandbox scopes (interp_smod ginv spc (_APC od spc_pure ow))) >>= k_src))
      (st_tgt, i_tgt)).
Proof.
  iIntros "ISIM".
  rewrite unfold_APC. wforce_l true. wsteps_l.
  iFrame.
Qed.

Lemma wsim_apc_tgt `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}
  fl fr Ist is_closed u0 u1 cP r g {Rs Rt} RR ps pt nths st_src st_tgt i_src i_tgt spc spc_pure
  scopes ginv (ow_src ow_tgt od_src od_tgt : Ord.t)
  (WIDTH: (ow_tgt < ow_src)%ord)
  (DEPTH: (od_tgt <= od_src)%ord)
  :
    ((Ist nths st_src st_tgt) ∗
      (∀ nths0 st_src0 st_tgt0 ow_src_nxt,
        (Ist nths0 st_src0 st_tgt0)
        -∗ wsim fl fr Ist is_closed u0 u1 cP r g Rs Rt RR false false nths0
            (st_src0, ((HMod.sandbox scopes (interp_smod ginv spc (_APC od_src spc_pure ow_src_nxt)));;; i_src))
            (st_tgt0, i_tgt)))
  ⊢
    (wsim fl fr Ist is_closed u0 u1 cP r g Rs Rt RR ps pt nths 
      (st_src, ((HMod.sandbox scopes (interp_smod ginv spc (_APC od_src spc_pure ow_src)));;; i_src))
      (st_tgt, ((HMod.sandbox scopes (interp_smod ginv spc (_APC od_tgt spc_pure ow_tgt)));;; i_tgt))).
Proof.
  (* generalize is_closed, cP *)
  (* TODO: refactor proof by carefully using isim_mono_knowledge *)
  (* iIntros "[IST ISIM]". iApply wsim_reset.
  iStopProof.
  revert nths st_src. apply combine_quant.
  revert WIDTH. apply combine_quant.
  revert st_tgt. apply combine_quant.
  revert ow_src. apply combine_quant_dep.
  revert ow_tgt. apply combine_quant_dep.
  eapply wsim_coind. i. iIntros "(IST & ISIM) #CIH".
  destruct a as [ow_tgt [ow_src [st_tgt [WIDTH [nths st_src]]]]]; ss.
  set_marker marker. hide_ihyps. hide_itree_l.
  rewrite !unfold_APC.
  show_until marker.
  w_steps_r. des_ifs.
  { (* break *)
    w_steps_r. iApply wsim_reset. iPoseProof ("ISIM" $! nths st_src st_tgt ow_src) as "ISIM".
    rewrite wsim.wsim_eq /wsim.wsim_def /wsim.wsim_pre. iIntros "W".
    iApply (isim_mono_knowledge with "[ISIM IST CIH W]").
    { instantiate (1:=wsim.wsim_rel u0 r). et. }
    { instantiate (1:=wsim.wsim_rel u0 g). ii. destruct sti_src, sti_tgt. iIntros "G". iModIntro. rewrite /wsim.wsim_rel. iDestruct "G" as "[I G]". iFrame. iApply MON; iFrame. }
    iApply ("ISIM" with "IST"); iFrame.
  }
  { (* continue *)
    w_steps_r. set_marker marker. hide_ihyps. hide_itree_r.
    rewrite !unfold_APC. show_until marker.
    
    w_force_l false. w_steps_l. w_force_l ow_tgt. w_steps_l.
    w_force_l WIDTH. w_steps_l. w_force_l q1. w_steps_l. w_force_l q2. w_steps_l.
    assert (PO: is_Some (spc_pure q1) ∧ (q2 < od_src)%ord).
    { des. split; eauto. eapply Ord.lt_le_lt; eauto. }
    unfold guarantee. w_force_l PO. w_steps_l.
    destruct (spc q1). 2:{ w_steps_r. des_ifs. }
    hss. w_steps_l. w_steps_r. w_force_l.
    w_steps_l. w_force_l q4. w_steps_l. w_force_l. iSplitL "GRT"; et. w_steps_l.
    w_call "IST"; iFrame.
    w_steps_l. w_forces_r. iSplitL "ASM"; iFrame. w_steps_r.
    by_coind "CIH".
    iFrame.
  }
  Unshelve. eauto.
Qed. *)
Admitted.

Lemma wsim_apc_src_call_tgt_weaker `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}
  fl fr Ist is_closed u0 u1 cP r g {Rs Rt} RR ps pt nths st_src st_tgt k_src k_tgt spc spc_pure
  scopes ginv fn args fsp' fsp X (spec_arg: X) o P Q (ow_src ow_fn od_src od_fn : Ord.t)
  (WIDTH: (ow_fn < ow_src)%ord)
  (DEPTH: (od_fn < od_src)%ord)
  (SpcPureInSpc: spc_sub spc_pure spc)
  (fnInSpcPure: spc_pure fn = Some fsp')
  (WEAK: fspec_weaker fsp fsp')
  (fspIsfspecapc: fsp = (@fspec_apc Σ X o (λ x, (P x, Q x))))
  :
  (((P spec_arg args ∗ ⌜∃ vo : Ord.t, od_fn ↑ = vo ↑ ∧ (o spec_arg <= vo)%ord⌝) ∗ (Ist nths st_src st_tgt)) ∗
    (∀ nths0 st_src0 st_tgt0 (vret ret: Any.t),
      ((Ist nths0 st_src0 st_tgt0) ∗ (Q spec_arg ret))
      -∗ wsim fl fr Ist is_closed u0 u1 cP r g Rs Rt RR false false nths0
          (st_src0, ((HMod.sandbox scopes (interp_smod ginv spc (_APC od_src spc_pure ow_fn))) >>= k_src))
          (st_tgt0, k_tgt ret)))
  ⊢
    (wsim fl fr Ist is_closed u0 u1 cP r g Rs Rt RR ps pt nths
      (st_src, ((HMod.sandbox scopes (interp_smod ginv spc (_APC od_src spc_pure ow_src))) >>= k_src))
      (st_tgt, (trigger (Call fn args) >>= k_tgt))).
Proof.
  iIntros "[[[PRE %] IST] ISIM]".
  des. set_marker m. hide_ihyps. rewrite unfold_APC. show_until m.
  wforce_l false. wsteps_l. wforce_l ow_fn. wsteps_l. wforce_l WIDTH. wsteps_l.
  wforce_l fn. wsteps_l. wforce_l od_fn. wsteps_l.
  assert (PO: (is_Some (spc_pure fn) ∧ (od_fn < od_src)%ord)); et. 
  unfold guarantee. wforce_l PO. wsteps_l.
  assert (spc fn = Some fsp'); et. wforce_l. iSplit; et. wsteps_l.
  specialize (WEAK spec_arg). des.
  wforce_l x_tgt. wforce_l args. wsteps_l.
  iPoseProof ((PRE od_fn ↑ args) with "[PRE]") as ">PRE". { unfold precond, fspec_apc; ss. iFrame. by iExists _. }
  wforce_l. iFrame. wsteps_l.
  wcall "IST"; et.
  wsteps_l. iApply wsim_reset.
  iPoseProof ((POST q ret) with "ASM") as ">POST".
  iSpecialize ("ISIM" $! nths' st_s' st_t' q ret).
  iApply "ISIM". iFrame.
Qed.

Lemma wsim_apc_src_call_tgt `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}
  fl fr Ist is_closed u0 u1 cP r g {Rs Rt} RR ps pt nths st_src st_tgt k_src k_tgt spc spc_pure
  scopes ginv fn args fsp X (spec_arg: X) o P Q (ow_src ow_fn od_src od_fn : Ord.t)
  (WIDTH: (ow_fn < ow_src)%ord)
  (DEPTH: (od_fn < od_src)%ord)
  (SpcPureInSpc: spc_sub spc_pure spc)
  (fnInSpcPure: spc_pure fn = Some fsp)
  (fspIsfspecapc: fsp = (@fspec_apc Σ X o (λ x, (P x, Q x))))
  :
  (((P spec_arg args ∗ ⌜∃ vo : Ord.t, od_fn ↑ = vo ↑ ∧ (o spec_arg <= vo)%ord⌝) ∗ (Ist nths st_src st_tgt)) ∗
    (∀ nths0 st_src0 st_tgt0 (vret ret: Any.t),
      ((Ist nths0 st_src0 st_tgt0) ∗ (Q spec_arg ret))
      -∗ wsim fl fr Ist is_closed u0 u1 cP r g Rs Rt RR false false nths0
          (st_src0, ((HMod.sandbox scopes (interp_smod ginv spc (_APC od_src spc_pure ow_fn))) >>= k_src))
          (st_tgt0, k_tgt ret)))
  ⊢
    (wsim fl fr Ist is_closed u0 u1 cP r g Rs Rt RR ps pt nths
      (st_src, ((HMod.sandbox scopes (interp_smod ginv spc (_APC od_src spc_pure ow_src))) >>= k_src))
      (st_tgt, (trigger (Call fn args) >>= k_tgt))).
Proof.
  eapply wsim_apc_src_call_tgt_weaker; et. 
  do 2 (econs; et).
Qed.

(* useful apc lemmas cont. - don't require IST *)

Lemma wsim_apc_tgt_noist `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}
  is_closed fl fr Ist u0 u1 cP r g {Rs Rt} RR ps pt nths st_src st_tgt i_src i_tgt
  (spc spc_pure: string → option fspec) (od ow: Ord.t) (scopes: list string)
  (SUB: spc_sub spc_pure spc)
  (SUBA: spc_incl APCA.Spc spc)
  (FIND: alist_find APCName.apc fr = Some (HMod.sandbox_body (APCA.scopes, interp_sb_hp (wsim_ginv u0 cP) spc
      {| fsb_fspec := APCA.apc_spec; fsb_body := cfunN (APCA.apc_body spc_pure) |})))
  (BODY: ∀ fn fsp, spc_pure fn = Some fsp 
          → ∃ scp, alist_find fn fr = Some (pure_specbody scp u0 spc fsp))
  :
    (wsim fl fr Ist is_closed u0 u1 cP r g Rs Rt RR false false nths
      (st_src, i_src)
      (st_tgt, i_tgt))
  ⊢
    (wsim fl fr Ist is_closed u0 u1 cP r g Rs Rt RR ps pt nths 
      (st_src, i_src)
      (st_tgt, ((HMod.sandbox scopes (interp_smod (wsim_ginv u1 cP) spc (_APC od spc_pure ow)));;; i_tgt))).
  Proof.
  (* do well-founded induction twice? (due to wsim_ginv u0 cP)*)
  (* iIntros "ISIM".
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

  rewrite unfold_APC. wsteps_r. des_ifs.
  { (* break *)
    wsteps_r. 
    rewrite wsim.wsim_eq /wsim.wsim_def /wsim.wsim_pre. iIntros "_".
    step. iPureIntro. split; et.
  }
  { (* continue *)
    wsteps_r.

    unfold is_Some in *. des. dup grt. apply BODY in grt. des.
    apply SUB in grt1. rewrite grt1. hss. wsteps_r.
    iApply wsim_inline_tgt; eauto.
    unfold pure_specbody, interp_sb_hp; ss. wsteps_r.
    unfold pure_specbody, interp_sb_hp in q3; ss.
    unfold HoareFun. wsteps_r. wforce_r q3. wsteps_r.
    wforces_r. iSplitL "GRT"; et.
    wsteps_r. unfold pure_body, cfunN. hss. wsteps_r.
    iDestruct "GRT" as "%"; des; subst; hss.
    iApply wsim_inline_tgt; eauto.
    unfold HMod.sandbox_body, interp_sb_hp, HoareFun; hss.
    wsteps_r. wforce_r q5. wforce_r (q5↑). wforces_r. iSplit; et.
    wsteps_r. hss. unfold APCA.apc_body, APC. wsteps_r.

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
Qed. *)
Admitted.

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
  iApply wsim_apc_src; des_pairs; s.

Ltac apc_r hyps :=
  prep_macro_r;
  iApply wsim_apc_tgt; des_pairs; s;
  [| |iSplitL hyps; [|iIntros "% % % %"; iIntrosFresh "IST"]].

Ltac apc_call hyps :=
  prep_macro_l; (hrepeat do 1 hnorm_r);
  iApply wsim_apc_src_call_tgt; des_pairs; s;
  [| | | | |iSplitL hyps; [ |iIntros "% % % % %"; iIntrosFresh "ISTPOST"]].

Ltac apc_call_weaker hyps :=
  prep_macro_l; (hrepeat do 1 hnorm_r);
  iApply wsim_apc_src_call_tgt_weaker; des_pairs; s;
  [| | | | | | iSplitL hyps; [ |iIntros "% % % % %"; iIntrosFresh "ISTPOST"]].

Ltac apc_tgt_noist :=
  prep_macro_r;
  iApply wsim_apc_tgt_noist; des_pairs; s.
