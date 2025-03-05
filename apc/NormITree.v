Require Import CRIS.
Require Import wsim.
  
(* Lemma isim_congruence f fl fr Ist tid is_closed r g {Rs Rt} RR ps pt nths st_src st_tgt s0 s1 t0 t1
  (EQS: s0 = s1)
  (EQT: t0 = t1)
:
  (f (@isim Σ fl fr Ist tid is_closed r g Rs Rt RR ps pt nths (st_src, s0) (st_tgt, t0)): Prop)
  → (f (@isim Σ fl fr Ist tid is_closed r g Rs Rt RR ps pt nths (st_src, s1) (st_tgt, t1)): Prop).
Proof. subst; eauto. Qed. *)

Lemma isim_congruence_tgt Γ' f is_closed fl fr Ist r g Rs Rt RR ps pt nths sti_src st_tgt t0 t1
  (EQ: t0 = t1):
  f (@isim Γ' is_closed fl fr Ist r g Rs Rt RR ps pt nths sti_src (st_tgt, t0) ) ->
  (f (@isim Γ' is_closed fl fr Ist r g Rs Rt RR ps pt nths sti_src (st_tgt, t1) ): Prop).
Proof.
  subst. eauto.
Qed.

Lemma isim_congruence_src Γ' is_closed f fl fr Ist r g Rs Rt RR ps pt nths sti_tgt st_src t0 t1
  (EQ: t0 = t1):
  f (@isim Γ' is_closed fl fr Ist r g Rs Rt RR ps pt nths (st_src, t0) sti_tgt ) ->
  (f (@isim Γ' is_closed fl fr Ist r g Rs Rt RR ps pt nths (st_src, t1) sti_tgt): Prop).
Proof.
  subst. eauto.
Qed.

Lemma wsim_congruence_tgt `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}
  f fl fr Ist u0 u1 cP is_closed r g Rs Rt RR ps pt nths sti_src st_tgt t0 t1
  (EQ: t0 = t1):
  f (wsim fl fr Ist is_closed u0 u1 cP r g Rs Rt RR ps pt nths sti_src (st_tgt, t0) ) ->
  (f (wsim fl fr Ist is_closed u0 u1 cP r g Rs Rt RR ps pt nths sti_src (st_tgt, t1) ): Prop).
Proof.
  subst. eauto.
Qed.

Lemma wsim_congruence_src `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}
  f fl fr Ist u0 u1 cP is_closed r g Rs Rt RR ps pt nths st_src sti_tgt t0 t1
  (EQ: t0 = t1):
  f (wsim fl fr Ist is_closed u0 u1 cP r g Rs Rt RR ps pt nths (st_src, t0) sti_tgt) ->
  (f (wsim fl fr Ist is_closed u0 u1 cP r g Rs Rt RR ps pt nths (st_src, t1) sti_tgt): Prop).
Proof.
  subst. eauto.
Qed.

Lemma wsim_bind `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}
  fl fr Ist is_closed u0 u1 cP r g ps pt {Rs Rt Qs Qt} RR QQ nths st_src st_tgt i_src i_tgt k_src k_tgt :
  wsim fl fr Ist None u0 u1 cP r g Qs Qt QQ ps pt nths (st_src, i_src) (st_tgt, i_tgt)
  ∗ (∀ nths0 st_src0 ret_src st_tgt0 ret_tgt,
      QQ nths0 (st_src0, ret_src) (st_tgt0, ret_tgt)
      -∗ wsim fl fr Ist is_closed u0 u1 cP r g Rs Rt RR false false nths0 (st_src0, k_src ret_src) (st_tgt0, k_tgt ret_tgt))%I
  ⊢ (wsim fl fr Ist is_closed u0 u1 cP r g Rs Rt RR ps pt nths (st_src, i_src >>= k_src) (st_tgt, i_tgt >>= k_tgt)).
Proof.
  rewrite wsim.wsim_eq /wsim.wsim_def /wsim.wsim_pre. des_ifs.
  { iIntros "[W SIM] INV". iApply isim_bind.
    iSplitL "W". { iApply "W"; eauto. }
    iIntros (? ? ? ? ?) "Q". iApply ("SIM" with "Q"). iFrame. }
  { iIntros "[W SIM] INV". iApply isim_bind.
    iSplitL "W". { iApply "W"; eauto. }
    iIntros (? ? ? ? ?) "Q". iApply ("SIM" with "Q"). iFrame. }
  { iIntros "[W SIM] INV". iApply isim_bind.
    iSplitL "W". { iApply "W"; eauto. }
    iIntros (? ? ? ? ?) "Q". iApply ("SIM" with "Q"). iFrame. }
Qed.

Lemma bind_equal {E : Type → Type} {T U : Type} t0 k0 t1 k1:
  t0 = t1 → k0 = k1 → @ITree.bind E T U t0 k0 = @ITree.bind E T U t1 k1.
Proof.
  ii. subst. reflexivity.
Qed.

Ltac _bind_expand :=
  _prep;
  rewrite ?SRed.bind ?PRed.bind ?SBRed.bind ?bind_bind;
  try ((eapply bind_equal);[|extensionalities];_bind_expand);
  eauto.

Ltac bind_expand_r := 
  hide_itree_l;
  rewrite ?PRed.bind ?SBRed.bind ?bind_bind;
  eapply isim_congruence_tgt;
  _bind_expand;
  show_itree.

Ltac bind_expand_l := 
  hide_itree_r;
  rewrite ?SRed.bind ?SBRed.bind ?bind_bind;
  eapply isim_congruence_src;
  _bind_expand;
  show_itree.

Ltac wbind_expand_r := 
  hide_itree_l;
  rewrite ?PRed.bind ?HRed.bind ?bind_bind;
  eapply wsim_congruence_tgt;
  _bind_expand;
  show_itree.

Ltac wbind_expand_l := 
  hide_itree_r;
  rewrite ?SRed.bind ?HRed.bind ?bind_bind;
  eapply wsim_congruence_src;
  _bind_expand;
  show_itree.