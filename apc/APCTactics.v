Require Import CRIS.
Require Import APCHeader APC APCA.

Set Implicit Arguments.

Import APC.

(* useful apc lemmas - require IST *)

Section LEMMAS.

Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG}.

Lemma wsim_apc_src
    fl fr Ist cP r g {Rs Rt} RR ps pt st_src st_tgt k_src i_tgt spimg sp sp_pure
    img mask scopes (ow od: Ord.t) :
  wsim fl fr Ist cP r g Rs Rt RR true pt (st_src, k_src ()) (st_tgt, i_tgt) ⊢
  wsim fl fr Ist cP r g Rs Rt RR ps pt
    (st_src, ((SB.sandbox img mask scopes (SModTr.trans spimg sp (_APC od sp_pure ow))) >>= k_src))
    (st_tgt, i_tgt).
Proof using. iIntros "ISIM". rewrite unfold_APC. force_l true. steps_l. iFrame. Qed.

Lemma wsim_apc_src_call_tgt_weaker
  fl fr Ist Ep r g {Rs Rt} RR ps pt st_src st_tgt k_src k_tgt spimg sp sp_pure
  img_t (msk_s msk_t : _ → bool) sc_s sc_t (fn: string) args fsp' fsp X (spec_arg: X) o P Q
  (ow_src ow_fn od_src od_fn : Ord.t)
  (WIDTH: (ow_fn < ow_src)%ord)
  (DEPTH: (od_fn < od_src)%ord)
  (SpPureInSp: sp_incl sp_pure sp)
  (fnInSpPure: alist_find (Some fn) sp_pure = Some fsp')
  (CallSpec: negb (is_spawn_ospec fsp'))
  (WEAK: fspec_imply (fspec_flat fsp') fsp)
  (fspIsfspecapc: fsp = (@fspec_apc Σ X o (λ x, (P x, Q x))))
  :
  msk_s (Some fn) → msk_t (Some fn) →
  (((P spec_arg args ∗ ⌜∃ vo : Ord.t, od_fn ↑ = vo ↑ ∧ (o spec_arg <= vo)%ord⌝) ∗ (Ist st_src st_tgt)) ∗
    (∀ st_src0 st_tgt0 (vret ret: Any.t),
      ((Ist st_src0 st_tgt0) ∗ (Q spec_arg ret))
      -∗ wsim fl fr Ist Ep r g Rs Rt RR false false
          (st_src0, ((SB.sandbox true msk_s sc_s (SModTr.trans spimg sp (_APC od_src sp_pure ow_fn))) >>= k_src))
          (st_tgt0, k_tgt ret)))
  ⊢
    wsim fl fr Ist Ep r g Rs Rt RR ps pt
      (st_src, (SB.sandbox true msk_s sc_s (SModTr.trans spimg sp (_APC od_src sp_pure ow_src))) >>= k_src)
      (st_tgt, (SB.sandbox img_t msk_t sc_t (trigger (Call fn args))) >>= k_tgt).
Proof using.
  i. iIntros "[[[PRE %] IST] ISIM]".
  des. set_marker m. hide_ihyps. rewrite unfold_APC. show_until m.
  force_l false. steps_l. force_l ow_fn. steps_l. force_l WIDTH. steps_l.
  force_l fn. steps_l. force_l od_fn. steps_l.
  assert (PO: (is_Some (alist_find (Some fn) sp_pure) ∧ (od_fn < od_src)%ord)); et.
  unfold guarantee. force_l PO. steps_l.
  assert (sp fn = fsp').
  { apply SpPureInSp. eauto. }
  rewrite H3. destruct fsp'; ss; [destruct f;ss|].
  { des. rewrite /fspec_imply in WEAK. hss.
    exploit WEAK. { exists spec_arg; et. } i; des.
    force_l (FSpec_mk _ _ _ ValidSP). force_l args. steps_l.
    iPoseProof ((PRE vo ↑ args) with "[PRE]") as ">PRE". { unfold precond, fspec_apc; ss. iFrame. by iExists _. }
    iApply wsim_guarantee_src. iFrame. steps_l.

    call "IST"; et. norm_r.
    steps_l. iApply wsim_reset.
    iPoseProof ((WEAK0 _q ret) with "ASM") as ">POST".
    iSpecialize ("ISIM" $! st_s' st_t' _q ret).
    iApply "ISIM". iFrame.
  }
  { des; rewrite /fspec_imply in WEAK; hss.
    exploit WEAK. { exists spec_arg; et. } i; des. rr in ValidSP; des; subst.
    specialize (PRE (vo↑) args). rewrite /fspec_apc /fspec_trivial /precond in PRE; ss.
    iPoseProof (PRE with "[PRE]") as ">%".
    { iFrame. iPureIntro; eauto. }
    subst. call "IST".
    iPoseProof (WEAK0 with "[]") as ">POST"; eauto.
    rewrite /fspec_apc /postcond; ss.
    iApply wsim_reset.
    norm_l. norm_r. iSpecialize ("ISIM" $! st_s' st_t' (tt↑) ret).
    iApply "ISIM". iFrame.
  }
Qed.

Lemma wsim_apc_src_call_tgt
  fl fr Ist cP r g {Rs Rt} RR ps pt st_src st_tgt k_src k_tgt spimg sp (sp_pure : spl_type)
  img_t (msk_s msk_t : _ → bool) sc_s sc_t fn args fsp X (spec_arg: X) o P Q
  (ow_src ow_fn od_src od_fn : Ord.t)
  (WIDTH: (ow_fn < ow_src)%ord)
  (DEPTH: (od_fn < od_src)%ord)
  (SpPureInSp: sp_incl sp_pure sp)
  (fnInSpPure: alist_find (Some fn) sp_pure = Some (Some fsp))
  (CallSpec: negb (is_spawn_ospec (Some fsp)))
  (fspIsfspecapc: fsp = (@fspec_apc Σ X o (λ x, (P x, Q x))))
  :
  msk_s (Some fn) → msk_t (Some fn) →
  (((P spec_arg args ∗ ⌜∃ vo : Ord.t, od_fn ↑ = vo ↑ ∧ (o spec_arg <= vo)%ord⌝) ∗ (Ist st_src st_tgt)) ∗
    (∀ st_src0 st_tgt0 (vret ret: Any.t),
      ((Ist st_src0 st_tgt0) ∗ (Q spec_arg ret))
      -∗ wsim fl fr Ist cP r g Rs Rt RR false false
          (st_src0, ((SB.sandbox true msk_s sc_s (SModTr.trans spimg sp (_APC od_src sp_pure ow_fn))) >>= k_src))
          (st_tgt0, k_tgt ret)))
  ⊢
    wsim fl fr Ist cP r g Rs Rt RR ps pt
      (st_src, (SB.sandbox true msk_s sc_s (SModTr.trans spimg sp (_APC od_src sp_pure ow_src))) >>= k_src)
      (st_tgt, (SB.sandbox img_t msk_t sc_t (trigger (Call fn args))) >>= k_tgt).
Proof using.
  eapply wsim_apc_src_call_tgt_weaker; et. 
  ii. esplits; et.
Qed.

(* useful apc lemmas cont. - don't require IST *)

(*
Lemma wsim_apc_tgt_noist
  is_closed fl fr Ist u0 u1 cP r g {Rs Rt} RR ps pt nths st_src st_tgt i_src i_tgt
  (sp sp_pure: sp_type) (od ow: Ord.t) (scopes: list string)
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

(** TODO: updating apc tactics is required *)

Ltac apc_call hyps :=
  prep_macro_l; norm_r;
  iApply wsim_apc_src_call_tgt; des_pairs; s;
  [| | | | |try prove_sb_cond|try prove_sb_cond| |iSplitL hyps; [ |iIntros "% % % %"; iIntrosFresh "ISTPOST"]].

Ltac apc_call_weaker hyps :=
  prep_macro_l; norm_r;
  iApply wsim_apc_src_call_tgt_weaker; des_pairs; s;
  [| | | | | |try prove_sb_cond|try prove_sb_cond| |iSplitL hyps; [ |iIntros "% % % %"; iIntrosFresh "ISTPOST"]].

(* Ltac apc_tgt_noist :=
  prep_macro_r;
  iApply wsim_apc_tgt_noist; des_pairs; s. *)
