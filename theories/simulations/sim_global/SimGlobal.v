Require Import Common.

Set Implicit Arguments.

Definition smj : Type := option bool.

Definition smj_top :smj := None.
Definition smj_mid :smj := Some true.
Definition smj_bot :smj := Some false.

Definition smj_ltb (m1 m2 : smj) : bool :=
  match m1, m2 with
  | Some _, None => true
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

Variant simg_def
    (simg : forall R0 R1 (RR : R0 -> R1 -> Prop), smj -> smj -> (itree coreE R0) -> (itree coreE R1) -> Prop)
    {R0 R1} (RR : R0 -> R1 -> Prop)           
    (self :  smj -> smj -> (itree coreE R0) -> (itree coreE R1) -> Prop)
    : smj -> smj -> (itree coreE R0) -> (itree coreE R1) -> Prop :=

  | simg_ret ps pt r_src r_tgt
      (SIM : RR r_src r_tgt)
  : simg_def simg RR self ps pt (Ret r_src) (Ret r_tgt)

  | simg_io ps pt ps0 pt0
      I O ktr_src0 ktr_tgt0 fn (varg : I)
      (SIM : forall (x_src x_tgt : O) (EQ : x_src = x_tgt), self ps0 pt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  : simg_def simg RR self ps pt (trigger (IO fn varg) >>= ktr_src0) (trigger (IO fn varg) >>= ktr_tgt0)

  | simg_tauL ps pt ps0
      itr_src0 itr_tgt0
      (SIM : self ps0 pt itr_src0 itr_tgt0)
  : simg_def simg RR self ps pt (tau;; itr_src0) (itr_tgt0)

  | simg_tauR ps pt pt0
      itr_src0 itr_tgt0
      (SIM : self ps pt0 itr_src0 itr_tgt0)
  : simg_def simg RR self ps pt (itr_src0) (tau;; itr_tgt0)

  | simg_chooseL ps pt ps0
      X ktr_src0 itr_tgt0
      (SIM : exists x, self ps0 pt (ktr_src0 x) itr_tgt0)
  : simg_def simg RR self ps pt (trigger (Choose X) >>= ktr_src0) (itr_tgt0)

  | simg_chooseR ps pt pt0
      X itr_src0 ktr_tgt0
      (SIM : forall x, self ps pt0 itr_src0 (ktr_tgt0 x))
  : simg_def simg RR self ps pt (itr_src0) (trigger (Choose X) >>= ktr_tgt0)

  | simg_takeL ps pt ps0
      X ktr_src0 itr_tgt0
      (SIM : forall x, self ps0 pt (ktr_src0 x) itr_tgt0)
  : simg_def simg RR self ps pt (trigger (Take X) >>= ktr_src0) (itr_tgt0)

  | simg_takeR ps pt pt0
      X itr_src0 ktr_tgt0
      (SIM : exists x, self ps pt0 itr_src0 (ktr_tgt0 x))
  : simg_def simg RR self ps pt (itr_src0) (trigger (Take X) >>= ktr_tgt0)

  | simg_progress ps pt ps0 pt0
      itr_src itr_tgt
      (SIM : simg _ _ RR ps0 pt0 itr_src itr_tgt)
      (DECS : smj_ltb ps0 ps)
      (DECT : smj_ltb pt0 pt)
  : simg_def simg RR self ps pt itr_src itr_tgt
.

Lemma simg_def_mon simg simg' R_src R_tgt RR P P'
  (LESIM : simg <7= simg')
  (LE : P <4= P')
  :
  @simg_def simg R_src R_tgt RR P <4= simg_def simg' RR P'.
Proof.
  i. destruct PR; des; eauto using simg_def.
Qed.

Inductive _simg simg {R0 R1} RR ps pt isrc itgt : Prop :=
| _simg_intro (SIM : @simg_def simg R0 R1 RR (_simg simg RR) ps pt isrc itgt)
.

Lemma simg_tarski
    (simg : forall R0 R1 (RR : R0 -> R1 -> Prop), smj -> smj -> (itree coreE R0) -> (itree coreE R1) -> Prop)
    R0 R1 (RR : R0 -> R1 -> Prop)
    (P : smj -> smj -> (itree coreE R0) -> (itree coreE R1) -> Prop)
    (SIM : simg_def simg RR P <4= P)
  :
  _simg simg RR <4= P.
Proof.
  fix IH 5. i. inv PR; inv SIM0; eapply SIM; des; econs; try eapply IH; eauto.
Qed.

Definition simg : forall R0 R1 (RR : R0 -> R1 -> Prop),  smj -> smj -> (itree coreE R0) -> (itree coreE R1) -> Prop :=
  paco7 _simg bot7.

Lemma simg_mon : monotone7 _simg.
Proof.
  ii. eapply simg_tarski, IN. i. inv PR; eauto using _simg, simg_def.
Qed.
Hint Resolve simg_mon : paco.
Hint Resolve cpn7_wcompat : paco.

Lemma simg_ind
    R0 R1 (RR : R0 -> R1 -> Prop)
    (P : smj -> smj -> (itree coreE R0) -> (itree coreE R1) -> Prop)
    (SIM : simg_def simg RR (simg RR /4\ P) <4= P)
  :
  simg RR <4= P.
Proof.
  i. punfold PR.
  assert (SIM' : simg_def simg RR (simg RR /4\ P) <4= (simg RR /4\ P)).
  { i. split; eauto. pstep. econs.
    eapply simg_def_mon, PR0; eauto.
    i. ss. des. punfold PR1. }

  eapply simg_tarski in SIM'; des; eauto.
  eapply simg_mon; eauto. i. pclearbot. eauto.
Qed.

Definition simg_indC simg {R0 R1} RR :=
  @simg_def bot7 R0 R1 RR (simg R0 R1 RR).

Lemma simg_indC_mon : monotone7 simg_indC.
Proof.
  ii. unfold simg_indC in *.
  inv IN; des; eauto using simg_def.
Qed.
Hint Resolve simg_indC_mon : paco.

Lemma simg_indC_spec:
  simg_indC <8= gupaco7 _simg (cpn7 _simg).
Proof.
  eapply wrespect7_uclo; eauto with paco.
  econs; eauto with paco. i.
  inv PR; econs; des; subst; ss; eauto 7 using simg_def, simg_mon, rclo7.
Qed.

Hint Constructors _simg : core.
Hint Unfold simg : core.

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

Lemma flagC_wrespectful : wrespectful7 (_simg) flagC.
Proof.
  econs; eauto with paco.
  ii. inv PR. 
  
     

  
  clarify. csc.
  eapply GF in SIM.
  move SIM before GF. revert_until SIM.
  pattern ps0, pt0, x5, x6.
  eapply simg_tarski, SIM. i.
  inv PR; des; econs; econs; i; subst; ss; eauto 7 using rclo7.
  - destruct SRC; subst; eauto using smj_ltb_trans.
  - destruct TGT; subst; eauto using smj_ltb_trans.
Qed.

Lemma flagC_spec : flagC <8= gupaco7 (_simg) (cpn7 (_simg)).
Proof.
  intros. eapply wrespect7_uclo; eauto with paco. eapply flagC_wrespectful.
Qed.

Lemma simg_flag
  r R0 R1 RR itr_src itr_tgt ps0 pt0 ps1 pt1
  (SIM : @_simg r R0 R1 RR ps0 pt0 itr_src itr_tgt)
  (SRC : smj_le ps0 ps1)
  (TGT : smj_le pt0 pt1)
  :
  @_simg r R0 R1 RR ps1 pt1 itr_src itr_tgt.
Proof.
  move SIM before r. revert_until SIM.
  pattern ps0, pt0, itr_src, itr_tgt.
  eapply simg_tarski, SIM. i.
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

Lemma bindC_wrespectful : wrespectful7 (_simg) bindC.
Proof.
  econs.
  { ii. eapply bindR_mon; eauto. }
  i. inv PR. csc. eapply GF in SIM.
  move SIM before GF. revert_until SIM.
  pattern x3, x4, i_src, i_tgt.
  eapply simg_tarski, SIM. i.
  inv PR; des; i; subst; ss; grind;
    eauto 7 using simg_mon, simg_flag, simg_def, rclo7, smj_le_bot.

  econs. econs; eauto.
  econs 2; eauto 7 using simg_mon, simg_flag, simg_def, rclo7, smj_le_bot.
Qed.

Lemma bindC_spec : bindC <8= gupaco7 (_simg) (cpn7 (_simg)).
Proof.
  intros. eapply wrespect7_uclo; eauto with paco. eapply bindC_wrespectful.
Qed.

Hint Constructors _simg: core.
Hint Unfold simg: core.
Hint Resolve simg_mon: paco.
Hint Constructors flagC: core.
Hint Resolve flagC_mon: paco.
Hint Constructors bindR: core.
Hint Unfold bindC: core.
Hint Unfold simg_indC: core.
Hint Resolve simg_indC_mon: paco.
Hint Resolve cpn7_wcompat: paco.
