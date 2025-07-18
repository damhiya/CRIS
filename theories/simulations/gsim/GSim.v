Require Import Common.

Set Implicit Arguments.

Definition smj : Type := option bool.

Definition smj_top :smj := Some true.
Definition smj_mid :smj := Some false.
Definition smj_bot :smj := None.

Definition smj_ltb (m1 m2 : smj) : bool :=
  match m1, m2 with
  | None, Some _ => true
  | Some false, Some true => true
  | _, _ => false
  end.

Definition smj_leb m1 m2 :=
  negb (smj_ltb m2 m1).

Definition smj_le m1 m2 :=
  m1 = m2 \/ smj_ltb m1 m2.

Hint Unfold smj_le : core.

Lemma smj_ltb_trans m1 m2 m3
    (LT1 : smj_ltb m1 m2)
    (LT2 : smj_ltb m2 m3) :
  smj_ltb m1 m3.
Proof. destruct m1, m2, m3; ss; des_ifs. Qed.

Lemma smj_lt_mid_top :
  smj_ltb smj_mid smj_top.
Proof. ss. Qed.

Lemma smj_le_bot m :
  smj_le smj_bot m.
Proof. destruct m as [[] | ]; ss; eauto. Qed.

Variant gsim_def
    (gsim : forall R0 R1 (RR : R0 -> R1 -> Prop), smj -> smj -> (itree coreE R0) -> (itree coreE R1) -> Prop)
    {R0 R1} (RR : R0 -> R1 -> Prop)           
    (self :  smj -> smj -> (itree coreE R0) -> (itree coreE R1) -> Prop)
    : smj -> smj -> (itree coreE R0) -> (itree coreE R1) -> Prop :=

  | gsim_ret ps pt r_src r_tgt
      (SIM : RR r_src r_tgt)
  : gsim_def gsim RR self ps pt (Ret r_src) (Ret r_tgt)

  | gsim_io ps pt ps0 pt0
      I O ktr_src0 ktr_tgt0 fn (varg : I)
      (SIM : forall (x_src x_tgt : O) (EQ : x_src = x_tgt), self ps0 pt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  : gsim_def gsim RR self ps pt (trigger (IO fn varg) >>= ktr_src0) (trigger (IO fn varg) >>= ktr_tgt0)

  | gsim_tauL ps pt ps0
      itr_src0 itr_tgt0
      (SIM : self ps0 pt itr_src0 itr_tgt0)
  : gsim_def gsim RR self ps pt (tau;; itr_src0) (itr_tgt0)

  | gsim_tauR ps pt pt0
      itr_src0 itr_tgt0
      (SIM : self ps pt0 itr_src0 itr_tgt0)
  : gsim_def gsim RR self ps pt (itr_src0) (tau;; itr_tgt0)

  | gsim_chooseL ps pt ps0
      X ktr_src0 itr_tgt0
      (SIM : exists x, self ps0 pt (ktr_src0 x) itr_tgt0)
  : gsim_def gsim RR self ps pt (trigger (Choose X) >>= ktr_src0) (itr_tgt0)

  | gsim_chooseR ps pt pt0
      X itr_src0 ktr_tgt0
      (SIM : forall x, self ps pt0 itr_src0 (ktr_tgt0 x))
  : gsim_def gsim RR self ps pt (itr_src0) (trigger (Choose X) >>= ktr_tgt0)

  | gsim_takeL ps pt ps0
      X ktr_src0 itr_tgt0
      (SIM : forall x, self ps0 pt (ktr_src0 x) itr_tgt0)
  : gsim_def gsim RR self ps pt (trigger (Take X) >>= ktr_src0) (itr_tgt0)

  | gsim_takeR ps pt pt0
      X itr_src0 ktr_tgt0
      (SIM : exists x, self ps pt0 itr_src0 (ktr_tgt0 x))
  : gsim_def gsim RR self ps pt (itr_src0) (trigger (Take X) >>= ktr_tgt0)

  | gsim_progress ps pt ps0 pt0
      itr_src itr_tgt
      (SIM : gsim _ _ RR ps0 pt0 itr_src itr_tgt)
      (DECS : smj_ltb ps0 ps)
      (DECT : smj_ltb pt0 pt)
  : gsim_def gsim RR self ps pt itr_src itr_tgt
.

Lemma gsim_def_mon gsim gsim' R_src R_tgt RR P P'
  (LESIM : gsim <7= gsim')
  (LE : P <4= P')
  :
  @gsim_def gsim R_src R_tgt RR P <4= gsim_def gsim' RR P'.
Proof.
  i. destruct PR; des; eauto using gsim_def.
Qed.

Inductive _gsim gsim {R0 R1} RR ps pt isrc itgt : Prop :=
| _gsim_intro (SIM : @gsim_def gsim R0 R1 RR (_gsim gsim RR) ps pt isrc itgt)
.

Lemma gsim_tarski
    (gsim : forall R0 R1 (RR : R0 -> R1 -> Prop), smj -> smj -> (itree coreE R0) -> (itree coreE R1) -> Prop)
    R0 R1 (RR : R0 -> R1 -> Prop)
    (P : smj -> smj -> (itree coreE R0) -> (itree coreE R1) -> Prop)
    (SIM : gsim_def gsim RR P <4= P)
  :
  _gsim gsim RR <4= P.
Proof.
  fix IH 5. i. inv PR; inv SIM0; eapply SIM; des; econs; try eapply IH; eauto.
Qed.

Definition gsim : forall R0 R1 (RR : R0 -> R1 -> Prop),  smj -> smj -> (itree coreE R0) -> (itree coreE R1) -> Prop :=
  paco7 _gsim bot7.

Lemma gsim_mon : monotone7 _gsim.
Proof.
  ii. eapply gsim_tarski, IN. i. inv PR; eauto using _gsim, gsim_def.
Qed.
Hint Resolve gsim_mon : paco.
Hint Resolve cpn7_wcompat : paco.

Lemma gsim_ind
    R0 R1 (RR : R0 -> R1 -> Prop)
    (P : smj -> smj -> (itree coreE R0) -> (itree coreE R1) -> Prop)
    (SIM : gsim_def gsim RR (gsim RR /4\ P) <4= P)
  :
  gsim RR <4= P.
Proof.
  i. punfold PR.
  assert (SIM' : gsim_def gsim RR (gsim RR /4\ P) <4= (gsim RR /4\ P)).
  { i. split; eauto. pstep. econs.
    eapply gsim_def_mon, PR0; eauto.
    i. ss. des. punfold PR1. }

  eapply gsim_tarski in SIM'; des; eauto.
  eapply gsim_mon; eauto. i. pclearbot. eauto.
Qed.

Definition gsim_indC gsim {R0 R1} RR :=
  @gsim_def bot7 R0 R1 RR (gsim R0 R1 RR).

Lemma gsim_indC_mon : monotone7 gsim_indC.
Proof.
  ii. unfold gsim_indC in *.
  inv IN; des; eauto using gsim_def.
Qed.
Hint Resolve gsim_indC_mon : paco.

Lemma gsim_indC_spec:
  gsim_indC <8= gupaco7 _gsim (cpn7 _gsim).
Proof.
  eapply wrespect7_uclo; eauto with paco.
  econs; eauto with paco. i.
  inv PR; econs; des; subst; ss; eauto 7 using gsim_def, gsim_mon, rclo7.
Qed.

Hint Constructors _gsim : core.
Hint Unfold gsim : core.

Variant flagC (r : forall S0 S1 (SS : S0 -> S1 -> Prop),  smj -> smj -> (itree coreE S0) -> (itree coreE S1) -> Prop):
  forall S0 S1 (SS : S0 -> S1 -> Prop),  smj -> smj -> (itree coreE S0) -> (itree coreE S1) -> Prop :=
  | flagC_intro
      ps0 ps1 pt0 pt1 R0 R1 (RR : R0 -> R1 -> Prop) itr_src itr_tgt
      (SRC : smj_le ps0 ps1)
      (TGT : smj_le pt0 pt1)
      (SIM : r _ _ RR ps0 pt0 itr_src itr_tgt)
    :
    flagC r RR ps1 pt1 itr_src itr_tgt
.
Hint Constructors flagC : core.

Lemma flagC_mon
  r1 r2
  (LE : r1 <7= r2)
  :
  flagC r1 <7= flagC r2
.
Proof. ii. destruct PR; econs; et. Qed.
Hint Resolve flagC_mon : paco.

Lemma flagC_wrespectful : wrespectful7 (_gsim) flagC.
Proof.
  econs; eauto with paco.
  ii. inv PR. 
  clarify. csc.
  eapply GF in SIM.
  move SIM before GF. revert_until SIM.
  pattern ps0, pt0, x5, x6.
  eapply gsim_tarski, SIM. i.
  inv PR; des; econs; econs; i; subst; ss; eauto 7 using rclo7.
  - destruct SRC; subst; eauto using smj_ltb_trans.
  - destruct TGT; subst; eauto using smj_ltb_trans.
Qed.

Lemma flagC_spec : flagC <8= gupaco7 (_gsim) (cpn7 (_gsim)).
Proof.
  intros. eapply wrespect7_uclo; eauto with paco. eapply flagC_wrespectful.
Qed.

Lemma gsim_flag
  r R0 R1 RR itr_src itr_tgt ps0 pt0 ps1 pt1
  (SIM : @_gsim r R0 R1 RR ps0 pt0 itr_src itr_tgt)
  (SRC : smj_le ps0 ps1)
  (TGT : smj_le pt0 pt1)
  :
  @_gsim r R0 R1 RR ps1 pt1 itr_src itr_tgt.
Proof.
  move SIM before r. revert_until SIM.
  pattern ps0, pt0, itr_src, itr_tgt.
  eapply gsim_tarski, SIM. i.
  inv PR; des; econs; econs; i; subst; ss; eauto 7 using rclo7.
  - destruct SRC; subst; eauto using smj_ltb_trans.
  - destruct TGT; subst; eauto using smj_ltb_trans.
Qed.

Variant bindR (r s : forall S0 S1 (SS : S0 -> S1 -> Prop),  smj -> smj -> (itree coreE S0) -> (itree coreE S1) -> Prop):
  forall S0 S1 (SS : S0 -> S1 -> Prop), smj -> smj -> (itree coreE S0) -> (itree coreE S1) -> Prop :=
  | bindR_intro ps pt
      R0 R1 RR
      (i_src : itree coreE R0) (i_tgt : itree coreE R1)
      (SIM : r _ _ RR ps pt i_src i_tgt)

      S0 S1 SS
      (k_src : ktree coreE R0 S0) (k_tgt : ktree coreE R1 S1)
      (SIMK : forall vret_src vret_tgt (SIM : RR vret_src vret_tgt), s _ _ SS smj_bot smj_bot (k_src vret_src) (k_tgt vret_tgt))
    :
    bindR r s SS ps pt (ITree.bind i_src k_src) (ITree.bind i_tgt k_tgt)
.

Hint Constructors bindR : core.

Lemma bindR_mon
  r1 r2 s1 s2
  (LEr : r1 <7= r2) (LEs : s1 <7= s2)
  :
  bindR r1 s1 <7= bindR r2 s2
.
Proof. ii. destruct PR; econs; et. Qed.

Definition bindC r := bindR r r.
Hint Unfold bindC : core.

Lemma bindC_wrespectful : wrespectful7 (_gsim) bindC.
Proof.
  econs.
  { ii. eapply bindR_mon; eauto. }
  i. inv PR. csc. eapply GF in SIM.
  move SIM before GF. revert_until SIM.
  pattern x3, x4, i_src, i_tgt.
  eapply gsim_tarski, SIM. i.
  inv PR; des; i; subst; ss; grind;
    eauto 7 using gsim_mon, gsim_flag, gsim_def, rclo7, smj_le_bot.

  econs. econs; eauto.
  econs 2; eauto 7 using gsim_mon, gsim_flag, gsim_def, rclo7, smj_le_bot.
Qed.

Lemma bindC_spec : bindC <8= gupaco7 (_gsim) (cpn7 (_gsim)).
Proof.
  intros. eapply wrespect7_uclo; eauto with paco. eapply bindC_wrespectful.
Qed.

Hint Constructors _gsim: core.
Hint Unfold gsim: core.
Hint Resolve gsim_mon: paco.
Hint Constructors flagC: core.
Hint Resolve flagC_mon: paco.
Hint Constructors bindR: core.
Hint Unfold bindC: core.
Hint Unfold gsim_indC: core.
Hint Resolve gsim_indC_mon: paco.
Hint Resolve cpn7_wcompat: paco.
