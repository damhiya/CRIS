Require Import CRIS.
  
Section ISIM.

  (* Lemma isim_congruence f fl fr Ist tid is_closed r g {Rs Rt} RR ps pt nths st_src st_tgt s0 s1 t0 t1
    (EQS: s0 = s1)
    (EQT: t0 = t1)
  :
    (f (@isim Σ fl fr Ist tid is_closed r g Rs Rt RR ps pt nths (st_src, s0) (st_tgt, t0)): Prop)
    → (f (@isim Σ fl fr Ist tid is_closed r g Rs Rt RR ps pt nths (st_src, s1) (st_tgt, t1)): Prop).
  Proof. subst; eauto. Qed. *)

  Lemma isim_congruence_tgt Γ' f fl fr Ist my_tid is_closed r g Rs Rt RR ps pt nths sti_src st_tgt t0 t1
    (EQ: t0 = t1):
    f (@isim Γ' fl fr Ist my_tid is_closed r g Rs Rt RR ps pt nths sti_src (st_tgt, t0) ) ->
    (f (@isim Γ' fl fr Ist my_tid is_closed r g Rs Rt RR ps pt nths sti_src (st_tgt, t1) ): Prop).
  Proof.
    subst. eauto.
  Qed.

  Lemma isim_congruence_src Γ' f fl fr Ist my_tid is_closed r g Rs Rt RR ps pt nths sti_tgt st_src t0 t1
    (EQ: t0 = t1):
    f (@isim Γ' fl fr Ist my_tid is_closed r g Rs Rt RR ps pt nths (st_src, t0) sti_tgt ) ->
    (f (@isim Γ' fl fr Ist my_tid is_closed r g Rs Rt RR ps pt nths (st_src, t1) sti_tgt): Prop).
  Proof.
    subst. eauto.
  Qed.

  Lemma bind_equal {E : Type → Type} {T U : Type} t0 k0 t1 k1:
    t0 = t1 → k0 = k1 → @ITree.bind E T U t0 k0 = @ITree.bind E T U t1 k1.
  Proof.
    ii. subst. reflexivity.
  Qed.

End ISIM.

Ltac _bind_expand :=
  _prep;
  rewrite ?SModRed.interp_bind ?PModRed.interp_bind ?HModSB.transl_bind ?bind_bind;
  try ((eapply bind_equal);[|extensionalities];_bind_expand);
  eauto.

Ltac bind_expand_r := 
  hide_itree_l;
  rewrite ?PModRed.interp_bind ?HModSB.transl_bind ?bind_bind;
  eapply isim_congruence_tgt;
  _bind_expand;
  show_itree.

Ltac bind_expand_l := 
  hide_itree_r;
  rewrite ?SModRed.interp_bind ?HModSB.transl_bind ?bind_bind;
  eapply isim_congruence_src;
  _bind_expand;
  show_itree.