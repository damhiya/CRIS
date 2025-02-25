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
  Context (my_tid : nat).
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
      wsim fl_s fl_t Ist my_tid (Some true) υ ν ⊤ r g R_s R_t RR false true nths
        (st_s, (HMod.sandbox scp_s (interp_smod ginv spc Sch.yield)) >>= k_s)
        (st_t, k_t tt))
    ⊢ wsim fl_s fl_t Ist my_tid (Some true) υ ν ⊤ r g R_s R_t RR ps pt nths
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
    wsim fl_s fl_t Ist my_tid (Some true) υ ν E r g R_s R_t RR true pt nths
      (st_s, k_s tt)
      (st_t, i_t)
    ⊢ wsim fl_s fl_t Ist my_tid (Some true) υ ν E r g R_s R_t RR ps pt nths
      (st_s, (HMod.sandbox scp_s (interp_smod ginv spc Sch.yield)) >>= k_s)
      (st_t, i_t).
  Proof.
    iIntros "SIM".
    rewrite /Sch.yield; unseal "Sch".
    unfold_iter_l; w_steps_l.
    w_force_l true; w_steps_l. iApply "SIM".
  Qed.

  Lemma wsim_spawn fn args fn_spec (x : meta fn_spec) (P : iProp Σ) (Q : SAny.t → SynDepO)
      r g scp_s scp_t ginv spc spc_user k_s k_t
      (SchInSpc : spc_incl (SchAS.spc υ spc_user) spc)
      (CalleeInSpc : spc_user fn = Some fn_spec)
      (Spawnable : ∀ tid, SchAS.fspec_spawnable υ fn_spec tid x args↑ args↑ P Q) :
    Ist nths st_s st_t
    -∗ P
    -∗ (∀ tid nths st_s st_t,
        Ist nths st_s st_t
        -∗ SchAS.token_th tid Q
        -∗ wsim fl_s fl_t Ist my_tid (Some true) υ ν ⊤ r g R_s R_t RR true true nths
            (st_s, k_s tid) (st_t, k_t tid))
    -∗ wsim fl_s fl_t Ist my_tid (Some true) υ ν ⊤ r g R_s R_t RR ps pt nths
      (st_s, (HMod.sandbox scp_s (interp_smod ginv spc (Sch.spawn (fn, args)))) >>= k_s)
      (st_t, (HMod.sandbox scp_t (PMod.interp (Sch.spawn (fn, args)))) >>= k_t).
  Proof.
    iIntros "I P SIM". rewrite /Sch.spawn; unseal "Sch".
    w_steps_l. w_forces_l. iSplitL "P".
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
    w_steps_l. w_steps_r. w_call "I". w_steps_l. w_steps_r.
    iDestruct "ASM" as "[%vr [-> [%tid [[-> ->] TKN]]]]". hss. w_steps_r.
    iApply ("SIM" with "IST TKN").
  Qed.

  Lemma wsim_join tid (Q : SAny.t → SynDepO) R
      r g scp_s scp_t ginv spc spc_user k_s k_t
      (SchInSpc : spc_incl (SchAS.spc υ spc_user) spc) :
    Ist nths st_s st_t
    -∗ SchAS.token_th tid Q
    -∗ (∀ nths st_s st_t ret,
        Ist nths st_s st_t
        -∗ interp_cond (Q ret↑↑)
        -∗ wsim fl_s fl_t Ist my_tid (Some true) υ ν ⊤ r g R_s R_t RR true true nths
            (st_s, k_s ret) (st_t, k_t ret))
    -∗ wsim fl_s fl_t Ist my_tid (Some true) υ ν ⊤ r g R_s R_t RR ps pt nths
      (st_s, (HMod.sandbox scp_s (interp_smod ginv spc (Sch.join R tid))) >>= k_s)
      (st_t, (HMod.sandbox scp_t (PMod.interp (Sch.join R tid))) >>= k_t).
  Proof.
    iIntros "IST TK SIM". rewrite /Sch.join; unseal "Sch".
    w_steps_l. w_force_l (tid, Q). w_steps_l. w_force_l (tid↑). w_steps_l. w_force_l.
    iFrame; iSplit; eauto. w_steps_l.

    w_steps_r. w_call "IST". w_steps_l. iDestruct "ASM" as "[[%ret' [-> Q]] ->]". hss.
    w_steps_r. hss. w_steps_r.
    apply SAny.downcast_upcast in G0. inv G0. rewrite SAny.upcast_downcast. hss. w_step_r.
    iApply ("SIM" with "IST Q").
  Qed.
End wsim.

Ltac _prep_macro_l :=
  prep; match goal with
  | [|- context[interp_smod _ _ (Sch.spawn _ >>= _)]] =>
      rewrite// [in (interp_smod _ _ (Sch.spawn _ >>= _))] SModRed.interp_bind; _prep_macro_l
  | [|- context[HMod.sandbox _ (interp_smod _ _ (Sch.spawn _) >>= _)]] =>
      rewrite// [in HMod.sandbox _ (interp_smod _ _ (Sch.spawn _) >>= _)] HModSB.transl_bind
  | [|- context[interp_smod _ _ (Sch.yield >>= _)]] =>
      rewrite// [in (interp_smod _ _ (Sch.yield >>= _))] SModRed.interp_bind; _prep_macro_l
  | [|- context[HMod.sandbox _ (interp_smod _ _ (Sch.yield) >>= _)]] =>
      rewrite// [in HMod.sandbox _ (interp_smod _ _ (Sch.yield) >>= _)] HModSB.transl_bind
  | [|- context[interp_smod _ _ (Sch.join _ _ >>= _)]] =>
      rewrite// [in (interp_smod _ _ (Sch.join _ _ >>= _))] SModRed.interp_bind; _prep_macro_l
  | [|- context[HMod.sandbox _ (interp_smod _ _ (Sch.join _ _) >>= _)]] =>
      rewrite// [in HMod.sandbox _ (interp_smod _ _ (Sch.join _ _) >>= _)] HModSB.transl_bind
  end.

  Ltac _prep_macro_r :=
  prep; match goal with
  | [|- context[PMod.interp (Sch.spawn _ >>= _)]] =>
      rewrite// [in (PMod.interp (Sch.spawn _ >>= _))] PModRed.interp_bind; _prep_macro_r
  | [|- context[HMod.sandbox _ (PMod.interp (Sch.spawn _) >>= _)]] =>
      rewrite// [in HMod.sandbox _ (PMod.interp (Sch.spawn _) >>= _)] HModSB.transl_bind
  | [|- context[PMod.interp (Sch.yield >>= _)]] =>
      rewrite// [in (PMod.interp (Sch.yield >>= _))] PModRed.interp_bind; _prep_macro_r
  | [|- context[HMod.sandbox _ (PMod.interp (Sch.yield) >>= _)]] =>
      rewrite// [in HMod.sandbox _ (PMod.interp (Sch.yield) >>= _)] HModSB.transl_bind
  | [|- context[PMod.interp (Sch.join _ _ >>= _)]] =>
      rewrite// [in (PMod.interp (Sch.join _ _ >>= _))] PModRed.interp_bind; _prep_macro_r
  | [|- context[HMod.sandbox _ (PMod.interp (Sch.join _ _) >>= _)]] =>
      rewrite// [in HMod.sandbox _ (PMod.interp (Sch.join _ _) >>= _)] HModSB.transl_bind
  end.
Ltac prep_macro :=
  let marker := fresh "MARKER" in
  hide_itree_r marker; try _prep_macro_l; show_itree marker;
  hide_itree_l marker; try _prep_macro_r; show_itree marker.