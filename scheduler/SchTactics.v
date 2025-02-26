Require Import CRIS wsim_tactics SchHeader SchA.

Section wsim.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !SchAGΣ Σ}.

  Local Definition state : Type := alist key Any.t.
  Local Definition post (R_s R_t : Type) : Type := nat → state * R_s → state * R_t → iProp Σ.
  Local Definition rel : Type := ∀ R_s R_t : Type,
    post R_s R_t → bool → bool → nat → state * itree hmodE R_s → state * itree hmodE R_t → iProp Σ.

  Implicit Types r g : rel.
  Implicit Types ps pt : bool.
  Implicit Types nths : nat.
  Implicit Types E : coPset.

  Context (fl_s fl_t : alist string (Any.t → itree hmodE Any.t)).
  Context (Ist : nat → alist key Any.t → alist key Any.t → iProp Σ).
  Context (t : option bool).
  Context (υ ν : univ_id).
  Context (E : coPset).
  Context (R_s R_t : Type).
  Context (RR : post R_s R_t).
  Context (ps pt : bool).
  Context (nths : nat).
  Context (st_s st_t : state).

  Lemma wsim_yield_tgt r g scp_s scp_t ginv spc spc_user k_s k_t
      (SchInSpc : spc_incl (SchAS.spc υ spc_user) spc) :
    Ist nths st_s st_t ∗
    (∀ nths st_s st_t,
      Ist nths st_s st_t -∗
      wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR false true nths
        (st_s, (HMod.sandbox scp_s (interp_smod ginv spc Sch.yield)) >>= k_s)
        (st_t, k_t tt))
    ⊢ wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR ps pt nths
      (st_s, (HMod.sandbox scp_s (interp_smod ginv spc Sch.yield)) >>= k_s)
      (st_t, (HMod.sandbox scp_t (PMod.interp Sch.yield)) >>= k_t).
  Proof.
    rewrite !wsim.wsim_eq /wsim.wsim_def.
    iIntros "SIM P".
    rewrite /Sch.yield; unseal "Sch".
    iApply isim_reset. iStopProof.
    revert nths. combine_quant st_s. combine_quant st_t.
    eapply isim_coind.
    iIntros (g' [st_s' [st_t' nths']]) "%MON [[[IST SIM] P] #CIH]". s.

    unfold_iter_r.
    steps_r. destruct q.
    { steps_r. iPoseProof ("SIM" with "IST P") as "SIM".
      iPoseProof (isim_mono_knowledge with "SIM") as "SIM"; cycle 2.
      { iApply "SIM". }
      { iIntros (????????) "$"; done. }
      { iIntros (????????) "P !>"; iApply MON; ss. }
    }

    steps_r.
    unfold_iter_l; steps_l.
    force_l false; steps_l.
    forces_l. iSplitL "P"; first (ss; eauto).
    steps_l. call "IST"; ss.
    steps_l. iDestruct "ASM" as "[P [-> ->]]". hss. steps_l.
    steps_r. hss. steps_r.
    iApply isim_progress; iApply isim_base.
    iSpecialize ("CIH" $! _);
    (hrepeat do 1 first[instantiate (1:= (_,_))|instantiate (1:= existT _ _)]); s;
    iApply "CIH".
    iFrame.
    Unshelve. done.
  Qed.

  Lemma wsim_yield_src r g scp_s ginv spc spc_user k_s i_t
      (SchInSpc : spc_incl (SchAS.spc υ spc_user) spc) :
    wsim fl_s fl_t Ist (Some true) υ ν E r g R_s R_t RR true pt nths
      (st_s, k_s tt)
      (st_t, i_t)
    ⊢ wsim fl_s fl_t Ist (Some true) υ ν E r g R_s R_t RR ps pt nths
      (st_s, (HMod.sandbox scp_s (interp_smod ginv spc Sch.yield)) >>= k_s)
      (st_t, i_t).
  Proof.
    iIntros "SIM".
    rewrite /Sch.yield; unseal "Sch".
    unfold_iter_l; wsteps_l.
    wforce_l true; wsteps_l. iApply "SIM".
  Qed.

  Lemma wsim_spawn fn args fn_spec (x : meta fn_spec) (P : iProp Σ) (Q : SAny.t → SynDepO)
      r g scp_s scp_t ginv spc spc_user k_s k_t
      (SchInSpc : spc_incl (SchAS.spc υ spc_user) spc)
      (CalleeInSpc : spc_user fn = Some fn_spec)
      (Spawnable : SchAS.fspec_spawnable υ fn_spec x args↑ args↑ P Q) :
    Ist nths st_s st_t ∗
    P ∗
    (∀ tid nths st_s st_t,
        Ist nths st_s st_t
        -∗ SchAS.token_th tid Q
        -∗ wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR true true nths
            (st_s, k_s tid) (st_t, k_t tid))
    ⊢ wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR ps pt nths
      (st_s, (HMod.sandbox scp_s (interp_smod ginv spc (Sch.spawn (fn, args)))) >>= k_s)
      (st_t, (HMod.sandbox scp_t (PMod.interp (Sch.spawn (fn, args)))) >>= k_t).
  Proof.
    iIntros "(I & P & SIM)". rewrite /Sch.spawn; unseal "Sch".
    wsteps_l. wforces_l. iSplitL "P".
    { iExists _; iSplit; eauto.
      Unshelve.
      2:{ split; first exact (args, args, P, Q).
          exists fn. rewrite /find_fsp CalleeInSpc; exact x.
      }
      2:{ exact ((fn, args)↑). }
      { ss; iFrame; iPureIntro. do 3 split; eauto.
        rewrite /find_fsp. generalize (CalleeInSpc). rewrite CalleeInSpc.
        intros H; rewrite (UIP_refl _ _ H) /eq_rect_r /=. done.
      }
    }
    wsteps_l. wsteps_r. wcall "I". wsteps_l. wsteps_r.
    iDestruct "ASM" as "[%vr [-> [%tid [[-> ->] TKN]]]]". hss. wsteps_r.
    iApply ("SIM" with "IST TKN").
  Qed.

  Lemma wsim_join tid (Q : SAny.t → SynDepO) R
      r g scp_s scp_t ginv spc spc_user k_s k_t
      (SchInSpc : spc_incl (SchAS.spc υ spc_user) spc) :
    Ist nths st_s st_t ∗
    SchAS.token_th tid Q ∗
    (∀ nths st_s st_t ret,
        Ist nths st_s st_t
        -∗ interp_cond (Q ret↑↑)
        -∗ wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR true true nths
            (st_s, k_s ret) (st_t, k_t ret))
    ⊢ wsim fl_s fl_t Ist (Some true) υ ν ⊤ r g R_s R_t RR ps pt nths
      (st_s, (HMod.sandbox scp_s (interp_smod ginv spc (Sch.join R tid))) >>= k_s)
      (st_t, (HMod.sandbox scp_t (PMod.interp (Sch.join R tid))) >>= k_t).
  Proof.
    iIntros "(IST & TK & SIM)". rewrite /Sch.join; unseal "Sch".
    wsteps_l. wforce_l (tid, Q). wsteps_l. wforce_l (tid↑). wsteps_l. wforce_l.
    iFrame; iSplit; eauto. wsteps_l.

    wsteps_r. wcall "IST". wsteps_l. iDestruct "ASM" as "[[%ret' [-> Q]] ->]". hss.
    wsteps_r. hss. wsteps_r.
    apply SAny.downcast_upcast in G0. inv G0. rewrite SAny.upcast_downcast. hss. wstep_r.
    iApply ("SIM" with "IST Q").
  Qed.
End wsim.

Local Ltac _prep_macro :=
  ired;
  match goal with
  | [|- context[HMod.sandbox _ (interp_smod _ _ (Sch.spawn _)) >>= _]] => fail 1
  | [|- context[HMod.sandbox _ (interp_smod _ _ (Sch.spawn _) >>= _)]] =>
      rewrite// [in HMod.sandbox _ (interp_smod _ _ (Sch.spawn _) >>= _)] HModSB.transl_bind
  | [|- context[interp_smod _ _ (Sch.spawn _ >>= _)]] =>
      rewrite// [in (interp_smod _ _ (Sch.spawn _ >>= _))] SModRed.interp_bind; _prep_macro
  | [|- context[HMod.sandbox _ (interp_smod _ _ (Sch.yield)) >>= _]] => fail 1
  | [|- context[HMod.sandbox _ (interp_smod _ _ (Sch.yield) >>= _)]] =>
      rewrite// [in HMod.sandbox _ (interp_smod _ _ (Sch.yield) >>= _)] HModSB.transl_bind
  | [|- context[interp_smod _ _ (Sch.yield >>= _)]] =>
      rewrite// [in (interp_smod _ _ (Sch.yield >>= _))] SModRed.interp_bind; _prep_macro
  | [|- context[HMod.sandbox _ (interp_smod _ _ (Sch.join _ _)) >>= _]] => fail 1
  | [|- context[HMod.sandbox _ (interp_smod _ _ (Sch.join _ _) >>= _)]] =>
      rewrite// [in HMod.sandbox _ (interp_smod _ _ (Sch.join _ _) >>= _)] HModSB.transl_bind
  | [|- context[interp_smod _ _ (Sch.join _ _ >>= _)]] =>
      rewrite// [in (interp_smod _ _ (Sch.join _ _ >>= _))] SModRed.interp_bind; _prep_macro
  | [|- context[HMod.sandbox _ (PMod.interp (Sch.spawn _)) >>= _]] => fail 1
  | [|- context[HMod.sandbox _ (PMod.interp (Sch.spawn _) >>= _)]] =>
      rewrite// [in HMod.sandbox _ (PMod.interp (Sch.spawn _) >>= _)] HModSB.transl_bind
  | [|- context[PMod.interp (Sch.spawn _ >>= _)]] =>
      rewrite// [in (PMod.interp (Sch.spawn _ >>= _))] PModRed.interp_bind; _prep_macro
  | [|- context[HMod.sandbox _ (PMod.interp (Sch.yield)) >>= _]] => fail 1
  | [|- context[HMod.sandbox _ (PMod.interp (Sch.yield) >>= _)]] =>
      rewrite// [in HMod.sandbox _ (PMod.interp (Sch.yield) >>= _)] HModSB.transl_bind
  | [|- context[PMod.interp (Sch.yield >>= _)]] =>
      rewrite// [in (PMod.interp (Sch.yield >>= _))] PModRed.interp_bind; _prep_macro
  | [|- context[HMod.sandbox _ (PMod.interp (Sch.join _ _)) >>= _]] => fail 1
  | [|- context[HMod.sandbox _ (PMod.interp (Sch.join _ _) >>= _)]] =>
      rewrite// [in HMod.sandbox _ (PMod.interp (Sch.join _ _) >>= _)] HModSB.transl_bind
  | [|- context[PMod.interp (Sch.join _ _ >>= _)]] =>
      rewrite// [in (PMod.interp (Sch.join _ _ >>= _))] PModRed.interp_bind; _prep_macro
  end.

Local Ltac prep_macro_l :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_r;
  try _prep_macro; ired;
  show_until marker.  

Local Ltac prep_macro_r :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_l;
  try _prep_macro; ired;
  show_until marker.

Local Ltac prep_macro :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_r; try _prep_macro; ired; show_itree;
  hide_itree_l; try _prep_macro; ired; show_itree;
  show_until marker.

Ltac sch_yield_l :=
  prep_macro; iApply wsim_yield_src; first eassumption.

Ltac sch_yield_r :=
  prep_macro; iApply wsim_yield_tgt; first eassumption.

Ltac sch_spawn :=
  prep_macro; iApply wsim_spawn; first eassumption.

Ltac sch_join :=
  prep_macro; iApply wsim_join; first eassumption.








(* Section MACROAUX. *)
(*   Import SchAS. *)
(*   Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !SchAGΣ Σ}. *)
(*   Notation iProp := (iProp Σ). *)

(*   (** Sch.spawn *) *)

(*   Lemma isim_mspawn_hp *)
(*     n contextual fl fr Ist r g {Rs Rt} RR my_tid ps pt nths st_src st_tgt k_src k_tgt scp_src scp_tgt invspc *)
(*     (Stb: string → option fspec) (univ: positive) *)
(*     (fvarg farg: SAny.t) (pre: iProp) (postS: SAny.t → {n & SRFSyn.t n})  *)
(*     (fn: string) (fsp: fspec) (m: meta fsp) *)
(*     (FINDF: Stb fn = Some fsp) *)
(*     (FINDS: Stb SchName.spawn = Some (SchAS.spawn_spec univ n Stb)) *)
(*     (SPWN: ∀ tid, SchAS.fspec_spawnable univ n fsp tid m fvarg↑ farg↑ pre postS) *)
(*     : *)
(*       (((Ist nths st_src st_tgt) ∗ (∃ n, wsats univ n ⊤) ∗ pre) ∗ *)
(*       (∀ nths0 st_src0 st_tgt0 tid, *)
(*         ((Ist nths0 st_src0 st_tgt0) ∗ (∃ n, wsats univ n ⊤) ∗ (SchAS.token_th tid postS)) *)
(*         -∗ @isim Σ contextual fl fr Ist my_tid r g Rs Rt RR true true nths0  *)
(*               (st_src0, k_src tid) *)
(*               (st_tgt0, k_tgt tid))) *)
(*     ⊢ *)
(*       (isim contextual fl fr Ist my_tid r g RR ps pt nths  *)
(*         (st_src, (HMod.sandbox scp_src (interp_smod invspc Stb (Sch.spawn (fn, fvarg)))) >>= k_src) *)
(*         (st_tgt, (HMod.sandbox scp_tgt (PMod.interp (Sch.spawn (fn, farg)))) >>= k_tgt)). *)
(*   Proof. *)
(*     iIntros "[(IST & W & PRE) ISIM]". rewrite !/Sch.spawn /ccallU. unseal "Sch". *)
(*     force_l. iSplitR; et. unfold HoareCall. steps_l. force_l. *)
(*     Unshelve. *)
(*     2:{ split. *)
(*       - exact (farg, fvarg, pre, postS). *)
(*       - exists fn. unfold find_fsp. rewrite FINDF. exact m. } *)
(*     force_l ((fn, farg)↑). force_l. iSplitL "PRE W". *)
(*     { iFrame. revert SPWN. revert m. generalize FINDF. unfold find_fsp. rewrite FINDF. i. *)
(*       rewrite (@UIP _ _ _ FINDF0 eq_refl). erewrite <-rew_swap; et. } *)
    
(*     call "IST"; et. *)
    
(*     steps_l. steps_r. iDestruct "ASM" as "(W & (% & % & % & % & TKN))". des; subst; hss. *)
(*     steps_r. iApply "ISIM". iFrame. *)
(*   Qed. *)

(*   Lemma isim_mspawn_hh *)
(*     contextual fl fr Ist r g Rs Rt RR my_tid ps pt nths st_src st_tgt k_src k_tgt scp_src scp_tgt invspc_src invspc_tgt *)
(*     (stbf stb_src stb_tgt: string → option fspec) (univ: positive) *)
(*     (fvarg: SAny.t) (fn: string) (fsp: fspec) (m: meta fsp) *)
(*     (FIND: stbf fn = Some fsp) *)
(*     (SPWNS: stb_src SchName.spawn = Some (SchAS.spawn_spec univ stbf)) *)
(*     (SPWNT: stb_tgt SchName.spawn = Some (SchAS.spawn_spec univ stbf)) *)
(*     : *)
(*       ((Ist nths st_src st_tgt) ∗ *)
(*       (∀ nths0 st_src0 st_tgt0 tid, *)
(*         (Ist nths0 st_src0 st_tgt0) *)
(*         -∗ @isim Σ contextual fl fr Ist my_tid r g Rs Rt RR true true nths0  *)
(*               (st_src0, k_src tid) *)
(*               (st_tgt0, k_tgt tid))) *)
(*     ⊢ *)
(*       (isim contextual fl fr Ist my_tid r g RR ps pt nths  *)
(*         (st_src, (HMod.sandbox scp_src (interp_smod invspc_src stb_src (Sch.spawn (fn, fvarg))))>>= k_src) *)
(*         (st_tgt, (HMod.sandbox scp_tgt (interp_smod invspc_tgt stb_tgt (Sch.spawn (fn, fvarg)))) >>= k_tgt)). *)
(*   Proof. *)
(*     iIntros "[IST ISIM]". rewrite !/Sch.spawn !/ccallU. unseal "Sch". *)
    
(*     steps_r. inv SPWNT. ss. iDestruct "GRT" as "[W [% [% GRT]]]". hss. *)
(*     destruct q0. destruct p. destruct p. destruct p. destruct s. *)
(*     iDestruct "GRT" as "((% & % & [% %] & %) & PRE)". des; subst; hss. *)

(*     forces_l. iSplit; et. steps_l. forces_l. iSplitL "PRE W". *)
(*     { iFrame. iExists _. iSplit; et. Unshelve. *)
(*       2:{ split; [exact (t, t0, b, o)|]. exists x. ss. } *)
(*       2:exact ((x, t)↑). ss. iSplit; et. } *)

(*     call "IST"; et. *)

(*     steps_l. iDestruct "ASM" as "[W (% & % & % & [% %] & TKN)]". subst; hss. *)

(*     forces_r. iSplitL "TKN W". { iFrame; et. } *)
(*     steps_r. hss. steps_r. iApply "ISIM". iFrame. *)
(*   Qed. *)

(*   (** Sch.yield **) *)

(*   Lemma isim_myield_tgt_hp *)
(*     contextual fl fr Ist r g {Rs Rt} RR my_tid ps pt nths st_src st_tgt k_src k_tgt scp_src scp_tgt invspc stb univ *)
(*     (SPC: stb SchName.yield = Some (SchAS.yield_spec univ)) *)
(*     : *)
(*     bi_entails *)
(*       (((Ist nths st_src st_tgt) ∗ (∃ n, wsats univ n ⊤)) ∗ *)
(*       (∀ nths0 st_src0 st_tgt0, *)
(*         ((Ist nths0 st_src0 st_tgt0) ∗ (∃ n, wsats univ n ⊤)) *)
(*         -∗ @isim Σ contextual fl fr Ist my_tid r g Rs Rt RR false true nths0  *)
(*               (st_src0, (HMod.sandbox scp_src (interp_smod invspc stb (Sch.yield))) >>= k_src)  *)
(*               (st_tgt0, k_tgt tt))) *)
(*       (isim contextual fl fr Ist my_tid r g RR ps pt nths  *)
(*         (st_src, (HMod.sandbox scp_src (interp_smod invspc stb (Sch.yield))) >>= k_src)  *)
(*         (st_tgt, (HMod.sandbox scp_tgt (PMod.interp (Sch.yield))) >>= k_tgt)). *)
(*   Proof. *)
(*     iIntros "[[IST W] ISIM]". rewrite !/Sch.yield. unseal "Sch". *)
(*     rewrite !unfold_iter_eq. grind. prep. iApply isim_reset. *)
(*     iStopProof. revert st_tgt. *)
(*     combine_quant st_src. *)
(*     combine_quant nths. *)
(*     combine_quant ps. *)
(*     combine_quant pt. *)
(*     eapply isim_coind. ii. destruct a as [pt [ps [nths [st_src st_tgt]]]]. *)
(*     iIntros "((IST & W & ISIM) & #CIH)". *)

(*     grind. prep. iApply isim_reset. steps_r. destruct q. *)
(*     { *)
(*       steps_r. *)
(*       iApply (isim_mono_knowledge with "[ISIM W IST]"). *)
(*       - instantiate (1:=r). et. *)
(*       - instantiate (1:=g). ii. destruct sti_src, sti_tgt. iIntros "G". iModIntro.  *)
(*         iApply H. et. *)
(*       - iApply "ISIM"; iFrame. *)
(*     } *)

(*     force_l. instantiate (1:=false). steps_l. unfold ccallU. force_l. iSplitR; et. *)
(*     unfold HoareCall. steps_l. forces_l. iSplitL "W"; et. *)
(*     call "IST"; et. steps_l. iDestruct "ASM" as "(W & % & %)". subst; hss. steps_r. hss. steps_r. steps_l. *)

(*     rewrite !unfold_iter_eq. grind. prep. prep. by_coind "CIH"; iFrame; et. *)

(*     Unshelve. all: ss. *)
(*   Qed. *)

(*   Lemma isim_myield_tgt_hh *)
(*     contextual fl fr Ist r g {Rs Rt} RR my_tid ps pt nths st_src st_tgt k_src k_tgt scp_src scp_tgt invspc stb univ *)
(*     (SPC: stb SchName.yield = Some (SchAS.yield_spec univ)) *)
(*     : *)
(*     bi_entails *)
(*       ((Ist nths st_src st_tgt) ∗ *)
(*       (∀ nths0 st_src0 st_tgt0, *)
(*         (Ist nths0 st_src0 st_tgt0) *)
(*         -∗ @isim Σ contextual fl fr Ist my_tid r g Rs Rt RR false true nths0  *)
(*               (st_src0, (HMod.sandbox scp_src (interp_smod invspc stb (Sch.yield))) >>= k_src)  *)
(*               (st_tgt0, k_tgt tt))) *)
(*       (isim contextual fl fr Ist my_tid r g RR ps pt nths  *)
(*         (st_src, (HMod.sandbox scp_src (interp_smod invspc stb (Sch.yield))) >>= k_src)  *)
(*         (st_tgt, (HMod.sandbox scp_tgt (interp_smod invspc stb (Sch.yield))) >>= k_tgt)). *)
(*   Proof. *)
(*     iIntros "[IST ISIM]". rewrite !/Sch.yield. unseal "Sch". *)
(*     rewrite !unfold_iter_eq. grind. prep. iApply isim_reset. *)
(*     iStopProof. revert st_tgt. *)
(*     combine_quant st_src. *)
(*     combine_quant nths. *)
(*     combine_quant ps. *)
(*     combine_quant pt. *)
(*     eapply isim_coind. ii. destruct a as [pt [ps [nths [st_src st_tgt]]]]. *)
(*     iIntros "((IST & ISIM) & #CIH)". *)

(*     grind. prep. iApply isim_reset. steps_r. destruct q. *)
(*     { *)
(*       steps_r. *)
(*       iApply (isim_mono_knowledge with "[ISIM IST]"). *)
(*       - instantiate (1:=r). et. *)
(*       - instantiate (1:=g). ii. destruct sti_src, sti_tgt. iIntros "G". iModIntro.  *)
(*         iApply H. et. *)
(*       - iApply "ISIM"; iFrame. *)
(*     } *)

(*     steps_r. inv SPC. ss. unfold precond. ss. iDestruct "GRT" as "[W %]". des; subst; hss. *)

(*     force_l. instantiate (1:=false). steps_l. unfold ccallU. force_l. iSplitR; et. *)
(*     unfold HoareCall. steps_l. forces_l. iSplitL "W"; et. *)
(*     call "IST"; et. *)
    
(*     steps_l. iDestruct "ASM" as "(W & % & %)". subst; hss. steps_r. hss. steps_r. steps_l. *)

(*     forces_r. iSplitL "W"; et. steps_r. hss. steps_r. *)

(*     rewrite !unfold_iter_eq. grind. prep. prep. by_coind "CIH"; iFrame; et. *)

(*     Unshelve. all: ss. *)
(*   Qed. *)

(*   Lemma isim_myield_src *)
(*     contextual fl fr Ist r g {Rs Rt} RR my_tid ps pt nths st_src st_tgt k_src i_tgt scp_src invspc stb univ *)
(*     (SPC: stb SchName.yield = Some (SchAS.yield_spec univ)) *)
(*     : *)
(*     bi_entails *)
(*       (((Ist nths st_src st_tgt) ∗ (∃ n, wsats univ n ⊤)) ∗ *)
(*       (∀ nths0 st_src0 st_tgt0, *)
(*         ((Ist nths0 st_src0 st_tgt0) ∗ (∃ n, wsats univ n ⊤)) *)
(*         -∗ @isim Σ contextual fl fr Ist my_tid r g Rs Rt RR true false nths0  *)
(*               (st_src0, k_src tt)  *)
(*               (st_tgt0, i_tgt))) *)
(*       (isim contextual fl fr Ist my_tid r g RR ps pt nths  *)
(*         (st_src, (HMod.sandbox scp_src (interp_smod invspc stb (Sch.yield))) >>= k_src)  *)
(*         (st_tgt, i_tgt)). *)
(*   Proof. *)
(*     iIntros "[[IST W] ISIM]". rewrite !/Sch.yield. unseal "Sch". *)
(*     rewrite !unfold_iter_eq. grind. prep. iApply isim_reset. *)
(*     force_l. instantiate (1:=true). steps_l. iApply "ISIM"; iFrame. *)
(*   Qed. *)

(*   (* Sch.join *) *)
  
(*   Lemma isim_mjoin_hp *)
(*     contextual fl fr Ist r g {Rs Rt} RR my_tid ps pt nths st_src st_tgt RT (k_src: RT → itree hmodE Rs) (k_tgt: RT → itree hmodE Rt) *)
(*     scp_src scp_tgt invspc tid *)
(*     (Stb: string → option fspec) (univ: positive) (postS: SAny.t → {n & SRFSyn.t n}) *)
(*     (FINDS: Stb SchName.join = Some (SchAS.join_spec univ)) *)
(*     : *)
(*       (((Ist nths st_src st_tgt) ∗ (∃ n, wsats univ n ⊤) ∗ (SchAS.token_th tid postS)) ∗ *)
(*       (∀ nths0 st_src0 st_tgt0 (ret: RT), *)
(*         ((Ist nths0 st_src0 st_tgt0) ∗ (∃ n, wsats univ n ⊤) ∗ (interp_cond (postS ret↑↑))) *)
(*         -∗ @isim Σ contextual fl fr Ist my_tid r g Rs Rt RR true true nths0  *)
(*               (st_src0, k_src ret) *)
(*               (st_tgt0, k_tgt ret))) *)
(*     ⊢ *)
(*       (isim contextual fl fr Ist my_tid r g RR ps pt nths  *)
(*         (st_src, (HMod.sandbox scp_src (interp_smod invspc Stb (Sch.join RT tid))) >>= k_src) *)
(*         (st_tgt, (HMod.sandbox scp_tgt (PMod.interp (Sch.join RT tid))) >>= k_tgt)). *)
(*   Proof. *)
(*     iIntros "[(IST & W & TKN) ISIM]". rewrite !/Sch.join !/ccallU. unseal "Sch". *)
(*     force_l. iSplitR; et. unfold HoareCall. steps_l. force_l (tid, postS). *)
(*     force_l (tid↑). force_l. iSplitL "TKN W"; iFrame; et. *)
(*     call "IST"; et. *)
    
(*     steps_l. steps_r. iDestruct "ASM" as "(W & [% [% POST]] & %)". des; subst; hss. *)
(*     steps_r. apply SAny.downcast_upcast in G0. r in G0. subst. *)
(*     rewrite SAny.upcast_downcast. hss. steps_r. *)
    
(*     iApply "ISIM". iFrame. *)
(*   Qed. *)

(*   Lemma isim_mjoin_hh *)
(*     contextual fl fr Ist r g {Rs Rt} RR my_tid ps pt nths st_src st_tgt RT (k_src: RT → itree hmodE Rs) (k_tgt: RT → itree hmodE Rt) *)
(*     scp_src scp_tgt invspc_src invspc_tgt univ stb_src stb_tgt tid *)
(*     (JOINS: stb_src SchName.join = Some (SchAS.join_spec univ)) *)
(*     (JOINT: stb_tgt SchName.join = Some (SchAS.join_spec univ)) *)
(*     : *)
(*       ((Ist nths st_src st_tgt) ∗ *)
(*       (∀ nths0 st_src0 st_tgt0 (ret: RT), *)
(*         (Ist nths0 st_src0 st_tgt0) *)
(*         -∗ @isim Σ contextual fl fr Ist my_tid r g Rs Rt RR true true nths0  *)
(*               (st_src0, k_src ret) *)
(*               (st_tgt0, k_tgt ret))) *)
(*     ⊢ *)
(*       (isim contextual fl fr Ist my_tid r g RR ps pt nths  *)
(*         (st_src, (HMod.sandbox scp_src (interp_smod invspc_src stb_src (Sch.join RT tid)))>>= k_src) *)
(*         (st_tgt, (HMod.sandbox scp_tgt (interp_smod invspc_tgt stb_tgt (Sch.join RT tid))) >>= k_tgt)). *)
(*   Proof. *)
(*     iIntros "[IST ISIM]". rewrite !/Sch.join !/ccallU. unseal "Sch". *)
    
(*     steps_r. inv JOINT. ss. iDestruct "GRT" as "[W PRE]". unfold precond. hss. *)
(*     destruct q0. ss. iDestruct "PRE" as "[[% TKN] %]". des; subst; hss. *)

(*     forces_l. iSplit; et. steps_l. force_l (n, o). forces_l. iSplitL "TKN W"; iFrame; et. *)
    
(*     call "IST"; et. *)

(*     steps_l. iDestruct "ASM" as "[W [[% [% POST]] %]]". subst; hss. *)
(*     apply SAny.downcast_upcast in G1. r in G1. subst. *)

(*     forces_r. iSplitL "POST W". { iFrame; et. } *)
(*     steps_r. hss. steps_r. rewrite SAny.upcast_downcast. hss. steps_r. *)
(*     iApply "ISIM". iFrame. *)
(*   Qed. *)

(* End MACROAUX. *)

(* Local Ltac _prep_macro_l := *)
(*   prep; match goal with *)
(*   | [|- context[interp_smod _ _ (Sch.spawn _ >>= _)]] => *)
(*       rewrite// [in (interp_smod _ _ (Sch.spawn _ >>= _))] SModRed.interp_bind; _prep_macro_l *)
(*   | [|- context[HMod.sandbox _ (interp_smod _ _ (Sch.spawn _) >>= _)]] => *)
(*       rewrite// [in HMod.sandbox _ (interp_smod _ _ (Sch.spawn _) >>= _)] HModSB.transl_bind *)
(*   | [|- context[interp_smod _ _ (Sch.yield >>= _)]] => *)
(*       rewrite// [in (interp_smod _ _ (Sch.yield >>= _))] SModRed.interp_bind; _prep_macro_l *)
(*   | [|- context[HMod.sandbox _ (interp_smod _ _ (Sch.yield) >>= _)]] => *)
(*       rewrite// [in HMod.sandbox _ (interp_smod _ _ (Sch.yield) >>= _)] HModSB.transl_bind *)
(*   | [|- context[interp_smod _ _ (Sch.join _ _ >>= _)]] => *)
(*       rewrite// [in (interp_smod _ _ (Sch.join _ _ >>= _))] SModRed.interp_bind; _prep_macro_l *)
(*   | [|- context[HMod.sandbox _ (interp_smod _ _ (Sch.join _ _) >>= _)]] => *)
(*       rewrite// [in HMod.sandbox _ (interp_smod _ _ (Sch.join _ _) >>= _)] HModSB.transl_bind *)
(*   end; prep. *)

(* Local Ltac _prep_macro_r := *)
(*   prep; match goal with *)
(*   | [|- context[PMod.interp (Sch.spawn _ >>= _)]] => *)
(*       rewrite// [in (PMod.interp (Sch.spawn _ >>= _))] PModRed.interp_bind; _prep_macro_r *)
(*   | [|- context[HMod.sandbox _ (PMod.interp (Sch.spawn _) >>= _)]] => *)
(*       rewrite// [in HMod.sandbox _ (PMod.interp (Sch.spawn _) >>= _)] HModSB.transl_bind *)
(*   | [|- context[PMod.interp (Sch.yield >>= _)]] => *)
(*       rewrite// [in (PMod.interp (Sch.yield >>= _))] PModRed.interp_bind; _prep_macro_r *)
(*   | [|- context[HMod.sandbox _ (PMod.interp (Sch.yield) >>= _)]] => *)
(*       rewrite// [in HMod.sandbox _ (PMod.interp (Sch.yield) >>= _)] HModSB.transl_bind *)
(*   | [|- context[PMod.interp (Sch.join _ _ >>= _)]] => *)
(*       rewrite// [in (PMod.interp (Sch.join _ _ >>= _))] PModRed.interp_bind; _prep_macro_r *)
(*   | [|- context[HMod.sandbox _ (PMod.interp (Sch.join _ _) >>= _)]] => *)
(*       rewrite// [in HMod.sandbox _ (PMod.interp (Sch.join _ _) >>= _)] HModSB.transl_bind *)
(*   end; prep. *)

(* Local Ltac prep_macro := *)
(*   let marker := fresh "MARKER" in *)
(*   hide_itree_r marker; try _prep_macro_l; show_itree marker; *)
(*   hide_itree_l marker; try _prep_macro_r; show_itree marker. *)

(* Ltac yield_r hyps := *)
(*   prep_macro; *)
(*   first [ *)
(*     iApply isim_myield_tgt_hp; des_pairs; s; *)
(*     [|iSplitL hyps; [|iIntros "% % %"; iIntros "[IST W]"]] | *)
(*     iApply isim_myield_tgt_hh; des_pairs; s; *)
(*     [|iSplitL hyps; [|iIntros "% % %"; iIntros "IST"]]]. *)

(* Ltac yield_l hyps := *)
(*   prep_macro; *)
(*   iApply isim_myield_src; des_pairs; s; *)
(*   [|iSplitL hyps; [ |iIntros "% % %"; iIntros "[IST W]"]]. *)

(* Ltac spawn hyps := *)
(*   prep_macro; *)
(*   first [ *)
(*     iApply isim_mspawn_hp; des_pairs; s; *)
(*     [| | |iSplitL hyps; [|iIntros "% % % %"; iIntros "[IST [W TKN]]"]] | *)
(*     iApply isim_mspawn_hh; des_pairs; s; *)
(*     [| | |iSplitL hyps; [|iIntros "% % % %"; iIntros "IST"]]]. *)

(* Ltac join hyps := *)
(*   prep_macro; *)
(*   first [ *)
(*     iApply isim_mjoin_hp; des_pairs; s; *)
(*     [|iSplitL hyps; [|iIntros "% % % %"; iIntros "[IST [W POST]]"]] | *)
(*     iApply isim_mjoin_hh; des_pairs; s; *)
(*     [| |iSplitL hyps; [|iIntros "% % % %"; iIntros "IST"]]]. *)
