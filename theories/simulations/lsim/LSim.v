Require Export LMod.

(** lsim is a local simulation relation between modules, with primitive rules for
  events like call, yield, etc. lsim is further abstracted to msim, and so on. You
  would not like to delve into the definitions unless for changing the metatheory *)
(* wsim → isim → msim → lsim → gsim *)
Section LSIM.
  Context (fl_src fl_tgt : gmap fname (Any.t → itree lmodE Any.t)).
  Context {world : Type} (winit : world) (wf : list world → Any.t * Any.t → Prop).
  Context (wle : relation world) (le_refl : Reflexive wle) (le_trans : Transitive wle).
  Context (my_tid : nat).

  Definition le_mine (w w' : list world) : Prop :=
    List.length w <= List.length w' ∧
    ∀ wi, w !! my_tid = Some wi → ∃ wi', w' !! my_tid = Some wi' ∧ wle wi wi'.

  Definition le_others (w w' : list world) : Prop :=
    List.length w = List.length w' ∧
    ∀ i, i ≠ my_tid → w !! i = w' !! i.

  Variant lsim_def
    (lsim : ∀ R_src R_tgt (RR : list world → Any.t → Any.t → R_src → R_tgt → Prop),
      bool → bool → list world → Any.t * itree lmodE R_src → Any.t * itree lmodE R_tgt → Prop)
    {R_src} {R_tgt} (RR : list world → Any.t → Any.t → R_src → R_tgt → Prop)
    (self : bool → bool → list world → Any.t * itree lmodE R_src → Any.t * itree lmodE R_tgt → Prop)
    : bool → bool → list world → Any.t * itree lmodE R_src → Any.t * itree lmodE R_tgt → Prop :=
  | lsim_ret
      ps pt w w0 st_src st_tgt
      v_src v_tgt
      (WLE : le_others w w0)
      (RET : RR w0 st_src st_tgt v_src v_tgt) :
    lsim_def lsim RR self ps pt w (st_src, Ret v_src) (st_tgt, Ret v_tgt)

  | lsim_call
      ps pt w w0 st_src st_tgt
      fn varg k_src k_tgt
      (WLE : le_others w w0)
      (WF : wf w0 (st_src, st_tgt))
      (K : ∀ w1 vret st_src0 st_tgt0 (WLE : le_mine w0 w1) (WF : wf w1 (st_src0, st_tgt0)),
          self true true w1 (st_src0, k_src vret) (st_tgt0, k_tgt vret)) :
    lsim_def lsim RR self ps pt w 
      (st_src, trigger (Call fn varg) >>= k_src)
      (st_tgt, trigger (Call fn varg) >>= k_tgt)

  | lsim_io
      ps pt w st_src st_tgt
      I O fn (varg : I) k_src k_tgt
      (K : ∀ (vret : O), self true true w (st_src, k_src vret) (st_tgt, k_tgt vret)) :
    lsim_def lsim RR self ps pt w
      (st_src, trigger (IO fn varg) >>= k_src)
      (st_tgt, trigger (IO fn varg) >>= k_tgt)

  | lsim_inline_src
      ps pt w st_src st_tgt
      f fn varg k_src i_tgt
      (FUN : fl_src !! (fid fn) = Some f)
      (K : self true pt w (st_src, x <- f varg;; tau;; k_src x) (st_tgt, i_tgt)) :
    lsim_def lsim RR self ps pt w
      (st_src, trigger (Call fn varg) >>= k_src)
      (st_tgt, i_tgt)

  | lsim_inline_tgt
      ps pt w st_src st_tgt
      f fn varg i_src k_tgt
      (FUN : fl_tgt !! (fid fn) = Some f)
      (K : self ps true w (st_src, i_src) (st_tgt, x <- f varg;; tau;; k_tgt x)) :
    lsim_def lsim RR self ps pt w
      (st_src, i_src)
      (st_tgt, trigger (Call fn varg) >>= k_tgt)

  | lsim_tau_src
      ps pt w st_src st_tgt
      i_src i_tgt
      (K : self true pt w (st_src, i_src) (st_tgt, i_tgt)) :
    lsim_def lsim RR self ps pt w (st_src, tau;; i_src) (st_tgt, i_tgt)

  | lsim_tau_tgt
      ps pt w st_src st_tgt
      i_src i_tgt
      (K : self ps true w (st_src, i_src) (st_tgt, i_tgt)) :
    lsim_def lsim RR self ps pt w (st_src, i_src) (st_tgt, tau;; i_tgt)

  | lsim_choose_src
      ps pt w st_src st_tgt
      X x k_src i_tgt
      (K : self true pt w (st_src, k_src x) (st_tgt, i_tgt)) :
    lsim_def lsim RR self ps pt w
      (st_src, trigger (Choose X) >>= k_src)
      (st_tgt, i_tgt)

  | lsim_choose_tgt
      ps pt w st_src st_tgt
      X i_src k_tgt
      (K : ∀ (x : X), self ps true w (st_src, i_src) (st_tgt, k_tgt x)) :
    lsim_def lsim RR self ps pt w (st_src, i_src)
      (st_tgt, trigger (Choose X) >>= k_tgt)

  | lsim_take_src
      ps pt w st_src st_tgt
      X k_src i_tgt
      (K : ∀ (x : X), self true pt w (st_src, k_src x) (st_tgt, i_tgt)) :
    lsim_def lsim RR self ps pt w (st_src, trigger (Take X) >>= k_src)
      (st_tgt, i_tgt)

  | lsim_take_tgt
      ps pt w st_src st_tgt
      X x i_src k_tgt
      (K : self ps true w (st_src, i_src) (st_tgt, k_tgt x)) :
    lsim_def lsim RR self ps pt w (st_src, i_src)
      (st_tgt, trigger (Take X) >>= k_tgt)

  | lsim_supdate_src
      ps pt w st_src st_tgt
      X k_src i_tgt
      (run : Any.t → Any.t * X)
      (K : self true pt w (fst (run st_src), k_src (snd (run st_src))) (st_tgt, i_tgt)) :
    lsim_def lsim RR self ps pt w (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt)

  | lsim_supdate_tgt
      ps pt w st_src st_tgt
      X i_src k_tgt
      (run : Any.t → Any.t * X)
      (K : self ps true w (st_src, i_src) (fst (run st_tgt), k_tgt (snd (run st_tgt)))) :
    lsim_def lsim RR self ps pt w (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt)

  | lsim_spawn
      ps pt w st_src st_tgt
      fn varg k_src k_tgt
      (K : ∀ tid, self true true (w++[winit]) (st_src, k_src tid) (st_tgt, k_tgt tid)) :
    lsim_def lsim RR self ps pt w
      (st_src, trigger (Spawn fn varg) >>= k_src)
      (st_tgt, trigger (Spawn fn varg) >>= k_tgt)

  | lsim_yield
      ps pt w w0 st_src st_tgt
      tid k_src k_tgt
      (WLE : le_others w w0)
      (WF : wf w0 (st_src, st_tgt))
      (K : ∀ w1 st_src0 st_tgt0 (WLE : le_mine w0 w1) (WF : wf w1 (st_src0, st_tgt0)),
          self true true w1 (st_src0, k_src ()) (st_tgt0, k_tgt ())) :
    lsim_def lsim RR self ps pt w (st_src, trigger (Yield tid) >>= k_src)
      (st_tgt, trigger (Yield tid) >>= k_tgt)

  | lsim_gettid
      ps pt w st_src st_tgt
      k_src k_tgt
      (K : ∀ (tid : nat), self true true w (st_src, k_src tid) (st_tgt, k_tgt tid)) :
    lsim_def lsim RR self ps pt w
      (st_src, trigger GetTid >>= k_src)
      (st_tgt, trigger GetTid >>= k_tgt)

  | lsim_call_none
      ps pt w st_src st_tgt
      fn varg k_src i_tgt
      (FUN: fl_src !! (fid fn) = None) :
    lsim_def lsim RR self ps pt w
      (st_src, trigger (Call fn varg) >>= k_src)
      (st_tgt, i_tgt)

  | lsim_spawn_none
      ps pt w st_src st_tgt
      fn varg k_src i_tgt
      (FUN: fl_src !! (fid fn) = None) :
    lsim_def lsim RR self ps pt w
      (st_src, trigger (Spawn fn varg) >>= k_src)
      (st_tgt, i_tgt)

  | lsim_progress
      w w0 st_src st_tgt
      i_src i_tgt
      (WLE : le_others w w0)
      (SIM : lsim _ _ RR false false w0 (st_src, i_src) (st_tgt, i_tgt)) :
    lsim_def lsim RR self true true w (st_src, i_src) (st_tgt, i_tgt).

  Inductive _lsim lsim {R_src} {R_tgt} RR ps pt w src tgt : Prop :=
  | _lsim_intro (SAT : @lsim_def lsim R_src R_tgt RR (_lsim lsim RR) ps pt w src tgt).

  Definition final_rel RR w0 w1 (st_src st_tgt ret_src ret_tgt : Any.t) :=
    le_mine w0 w1 ∧ RR w1 (st_src, st_tgt) ∧ ret_src = ret_tgt.

  Definition lsim RR w0 ps pt w src tgt :=
    paco8 _lsim bot8 _ _ (final_rel RR w0) ps pt w src tgt.

  Lemma lsim_def_mon lsim lsim' R_src R_tgt RR P P'
      (LESIM : lsim <8= lsim')
      (LE : P <5= P') :
    @lsim_def lsim R_src R_tgt RR P <5= lsim_def lsim' RR P'.
  Proof using. i. destruct PR; eauto using lsim_def. Defined.

  Lemma lsim_tarski lsim R_src R_tgt RR P
      (SIM : @lsim_def lsim R_src R_tgt RR P <5= P) :
    _lsim lsim RR <5= P.
  Proof using.
    fix IH 6. i. destruct PR. eapply SIM.
    eapply lsim_def_mon, SAT; i.
    - apply PR.
    - eapply IH, PR.
  Qed.

  Lemma lsim_mon : monotone8 _lsim.
  Proof using.
    ii. eapply lsim_tarski; eauto.
    econs; inv PR.
    all: eauto using lsim_def.
  Qed.

  Hint Constructors _lsim: core.
  Hint Unfold lsim: core.
  Hint Resolve lsim_mon : paco.
  Hint Resolve cpn8_wcompat : paco.

  Lemma le_mine_refl : Reflexive le_mine.
  Proof using le_refl. ii. eexists; eauto. Qed.

  Lemma le_mine_trans : Transitive le_mine.
  Proof using le_trans.
    intros x y z Hxy Hyz; destruct Hxy as [Hxy1 Hxy2], Hyz as [Hyz1 Hyz2]; split; try nia.
    intros wi Hx; eapply Hxy2 in Hx as [wi' [Hy ?]]; eapply Hyz2 in Hy; des; eauto.
  Qed.

  Lemma le_others_refl : Reflexive le_others.
  Proof using. rr. esplits; eauto. Qed.

  Lemma le_others_trans : Transitive le_others.
  Proof using.
    rr. unfold le_others. i; des. split; i.
    - etrans; eauto.
    - etrans; try apply H2; eauto.
  Qed.

  Lemma le_others_inc w1 w2 x :
    le_others w1 w2 → le_others (w1++[x]) (w2++[x]).
  Proof using.
    i. rdes H. split.
    - rewrite !length_app. nia.
    - i. assert (i < List.length w1 \/ i >= List.length w1) by nia; des.
      + rewrite !lookup_app_l; try nia. eauto.
      + rewrite !lookup_app_r; try nia. f_equal. nia.
  Qed.

  Lemma lsim_wmon self R_src R_tgt RR w1 w2 ps pt src tgt
      (SIM : @_lsim self R_src R_tgt RR ps pt w2 src tgt)
      (WLE : le_others w1 w2) :
    _lsim self RR ps pt w1 src tgt.
  Proof using.
    move SIM before RR. revert_until SIM.
    pattern ps, pt, w2, src, tgt.
    eapply lsim_tarski, SIM.
    i. econs. inv PR; eauto using lsim_def, le_others_refl, le_others_trans.
    econs. i; eapply K.
    destruct WLE. split.
    { rewrite !length_app. s. nia. }
    i. assert (CASE : i < List.length w1 \/ i = List.length w1 \/ i > List.length w1) by nia. des.
    - rewrite !lookup_app_l; try nia. eauto.
    - rewrite !(list_lookup_middle _ [] winit); try nia. eauto.
    - rewrite !lookup_ge_None_2; eauto; rewrite length_app; s; try nia.
  Qed.

  Lemma lsim_ind
      R_src R_tgt RR P
      (SIM : @lsim_def (paco8 _lsim bot8) R_src R_tgt RR (paco8 _lsim bot8 R_src R_tgt RR /5\ P) <5= P) :
    paco8 _lsim bot8 _ _ RR <5= P.
  Proof using.
    i. punfold PR.
    assert (SIM' : lsim_def (paco8 _lsim bot8) RR (paco8 _lsim bot8 R_src R_tgt RR /5\ P) <5= (paco8 _lsim bot8 R_src R_tgt RR /5\ P)).
    { i. split; eauto. pstep. econs.
      eapply lsim_def_mon, PR0; eauto.
      i. ss. des. punfold PR1.
    }
    eapply lsim_tarski in SIM'; des; eauto.
    eapply lsim_mon; eauto. i. pclearbot. eauto.
  Qed.

  Lemma lsim_mon_rr RR RR'
      (LER: RR <2= RR') :
    lsim RR <6= lsim RR'.
  Proof.
    pcofix CIH. i.
    punfold PR. eapply lsim_tarski, PR. i. pstep. econs.
    depdes PR0; pclearbot; try by econs; et; i; pstep_reverse.
    econs; et. r; r in RET; des. subst; esplits; et.
  Qed.

  Definition lsim_indC lsim {R_src R_tgt} RR :=
    @lsim_def bot8 R_src R_tgt RR (lsim R_src R_tgt RR).

  Lemma lsim_indC_mon : monotone8 lsim_indC.
  Proof using.
    ii. inv IN; try (sfby des; econs; et).
  Qed.
  Hint Resolve lsim_indC_mon : paco.

  Lemma lsim_indC_spec : lsim_indC <9= gupaco8 (_lsim) (cpn8 _lsim).
  Proof using.
    eapply wrespect8_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR; econs.
    { econs 1; eauto. }
    { econs 2; eauto. i. eapply lsim_mon; et. i. eapply rclo8_base. et. }
    { econs 3; eauto. i. eapply lsim_mon; et. i. eapply rclo8_base. eauto. }
    { econs 4; et. eapply lsim_mon; et. eapply rclo8_base. }
    { econs 5; et. eapply lsim_mon; et. eapply rclo8_base. }
    { econs 6; eauto. eapply lsim_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 7; eauto. eapply lsim_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 8; eauto. des. esplits; eauto. eapply lsim_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 9; eauto. i. eapply lsim_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 10; eauto. i. eapply lsim_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 11; eauto. des. esplits; eauto. eapply lsim_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 12; eauto. des. esplits; eauto. eapply lsim_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 13; eauto. des. esplits; eauto. eapply lsim_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 14; eauto. des. esplits; eauto. eapply lsim_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 15; eauto. des. esplits; eauto. eapply lsim_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 16; eauto. des. esplits; eauto. eapply lsim_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 17; eauto. }
    { econs 18; eauto. }
    { ss. }
  Qed.

  Definition lsimC
      (r g : ∀ (R_src R_tgt : Type) (RR : list world → Any.t → Any.t → R_src → R_tgt → Prop),
        bool → bool → list world → Any.t * itree lmodE R_src → Any.t * itree lmodE R_tgt → Prop)
      {R_src R_tgt} RR :=
    @lsim_def bot8 R_src R_tgt RR (r R_src R_tgt RR).

  Lemma lsimC_spec_aux : lsimC <10= gpaco8 (_lsim) (cpn8 _lsim).
  Proof using.
    i. inv PR.
    { gstep. econs; econs 1; eauto. }
    { guclo lsim_indC_spec. econs 2; et. i. gbase. et. }
    { guclo lsim_indC_spec. econs 3; et. i. gbase. et. }
    { guclo lsim_indC_spec. econs 4; eauto. gbase. eauto. }
    { guclo lsim_indC_spec. econs 5; eauto. gbase. eauto. }
    { guclo lsim_indC_spec. econs 6; eauto. gbase. eauto. }
    { guclo lsim_indC_spec. econs 7; eauto. gbase. eauto. }
    { guclo lsim_indC_spec. econs 8; eauto. des. esplits; eauto. gbase. eauto. }
    { guclo lsim_indC_spec. econs 9; eauto. gbase. eauto. }
    { guclo lsim_indC_spec. econs 10; eauto. gbase. eauto. }
    { guclo lsim_indC_spec. econs 11; eauto. des. esplits; eauto. gbase. eauto. }
    { guclo lsim_indC_spec. econs 12; eauto. gbase. eauto. }
    { guclo lsim_indC_spec. econs 13; eauto. gbase. eauto. }
    { guclo lsim_indC_spec. econs 14; eauto. gbase. eauto. }
    { guclo lsim_indC_spec. econs 15; eauto. gbase. eauto. }
    { guclo lsim_indC_spec. econs 16; eauto. gbase. eauto. }
    { guclo lsim_indC_spec. econs 17; eauto. }
    { guclo lsim_indC_spec. econs 18; eauto. }
    { guclo lsim_indC_spec. econs 19; eauto. }
  Qed.

  Lemma lsimC_spec r g :
    @lsimC (gpaco8 (_lsim) (cpn8 _lsim) r g) (gpaco8 (_lsim) (cpn8 _lsim) g g) <8=
    gpaco8 (_lsim) (cpn8 _lsim) r g.
  Proof using.
    i. eapply gpaco8_gpaco; [eauto with paco|].
    eapply gpaco8_mon.
    { eapply lsimC_spec_aux. eauto. }
    { auto. }
    { i. eapply gupaco8_mon; eauto. }
  Qed.

  Lemma lsim_progress_flag R0 R1 RR w r g st_src st_tgt
        (SIM : gpaco8 _lsim (cpn8 _lsim) g g R0 R1 RR false false w st_src st_tgt) :
      gpaco8 _lsim (cpn8 _lsim) r g R0 R1 RR true true w st_src st_tgt.
  Proof using.
    gstep. destruct st_src, st_tgt. econs; econs; eauto using le_others_refl.
  Qed.

  Lemma lsim_flag_mon lsim R_src R_tgt RR ps0 pt0 ps1 pt1 w st_src st_tgt
      (SIM : @_lsim lsim R_src R_tgt RR ps0 pt0 w st_src st_tgt)
      (SRC : ps0 = true → ps1 = true)
      (TGT : pt0 = true → pt1 = true) :
    _lsim lsim RR ps1 pt1 w st_src st_tgt.
  Proof using.
    move SIM before lsim. revert_until SIM.
    pattern ps0, pt0, w,  st_src, st_tgt.
    eapply lsim_tarski, SIM.
    i. econs. inv PR; eauto using lsim_def.
    exploit SRC; auto. exploit TGT; auto. i. clarify. econs; eauto.
  Qed.

  Definition sim_fsem : relation (Any.t → itree lmodE Any.t) :=
    λ it_src it_tgt,
      ∀ w mrs_src mrs_tgt arg
        (TID : my_tid < List.length w)
        (SIMMRS : wf w (mrs_src, mrs_tgt)),
        lsim wf w false false w (mrs_src, it_src arg) (mrs_tgt, it_tgt arg).

  Variant lflagC (r : ∀ (R_src R_tgt : Type)
    (RR : list world → Any.t → Any.t → R_src → R_tgt → Prop),
      bool → bool → list world → Any.t * itree lmodE R_src → Any.t * itree lmodE R_tgt → Prop)
    {R_src R_tgt} (RR : list world → Any.t → Any.t → R_src → R_tgt → Prop)
    : bool → bool → list world → Any.t * itree lmodE R_src → Any.t * itree lmodE R_tgt → Prop :=
  | lflagC_intro
      ps0 ps1 pt0 pt1 w0 w1 st_src st_tgt
      (SIM : r _ _ RR ps0 pt0 w0 st_src st_tgt)
      (WLE : le_others w1 w0)
      (SRC : ps0 = true → ps1 = true)
      (TGT : pt0 = true → pt1 = true) :
    lflagC r RR ps1 pt1 w1 st_src st_tgt.

  Lemma lflagC_mon r1 r2 (LE : r1 <8= r2) : @lflagC r1 <8= @lflagC r2.
  Proof using. ii. destruct PR; econs; et. Qed.

  Hint Resolve lflagC_mon : paco.

  Lemma lflagC_spec : lflagC <9= gupaco8 (_lsim) (cpn8 _lsim).
  Proof using.
    eapply wrespect8_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    eapply GF in SIM.
    revert x3 x4 x5 WLE SRC TGT.
    pattern ps0, pt0, w0, x6, x7.
    eapply lsim_tarski, SIM.
    i. econs. inv PR;
      eauto using lsim_def, lsim_wmon, le_others_refl, le_others_trans, le_others_inc.
    exploit SRC; auto. exploit TGT; auto. i. clarify.
    econs; cycle 1; eauto using rclo8, le_others_trans.
  Qed.

  Lemma lsim_flag_down R0 R1 RR r g w st_src st_tgt ps pt
      (SIM : gpaco8 _lsim (cpn8 _lsim) r g R0 R1 RR false false w st_src st_tgt) :
    gpaco8 _lsim (cpn8 _lsim) r g R0 R1 RR ps pt w st_src st_tgt.
  Proof using. guclo lflagC_spec. econs; eauto using le_others_refl. Qed.

  Lemma lsim_bot_flag_up w0 w st_src st_tgt ps pt
      (SIM : paco8 _lsim bot8 _ _ (final_rel wf w0) true true w st_src st_tgt) :
    paco8 _lsim bot8 _ _ (final_rel wf w0) ps pt w st_src st_tgt.
  Proof using.
    ginit. remember true in SIM at 1. remember true in SIM at 1.
    clear Heqb Heqb0. revert w st_src st_tgt ps pt b b0 SIM.
    gcofix CIH.
    i. revert ps pt. pattern b, b0, w, st_src, st_tgt.
    eapply lsim_ind, SIM. i.
    inv PR; ss; i; clarify.
    all: try (by guclo lsim_indC_spec; hdes; econs; eauto).
    eapply lsim_flag_down. gfinal. right.
    eapply paco8_mon.
    - punfold SIM0. pstep. eapply lsim_wmon; eauto using le_others_refl.
    - ss.
  Qed.

  Variant lbindR
      (r s : ∀ S_src S_tgt (SS : list world → Any.t → Any.t → S_src → S_tgt → Prop),
        bool → bool → list world → Any.t * itree lmodE S_src → Any.t * itree lmodE S_tgt → Prop)
    : ∀ S_src S_tgt (SS : list world → Any.t → Any.t → S_src → S_tgt → Prop),
      bool → bool → list world → Any.t * itree lmodE S_src → Any.t * itree lmodE S_tgt → Prop :=
  | lbindR_intro
      ps pt w R_src R_tgt RR (st_src st_tgt : Any.t)
      (i_src : itree lmodE R_src) (i_tgt : itree lmodE R_tgt)
      S_src S_tgt SS (k_src : ktree lmodE R_src S_src) (k_tgt : ktree lmodE R_tgt S_tgt)

      (SIM : r R_src R_tgt RR ps pt w (st_src, i_src) (st_tgt, i_tgt))
      (SIMK : ∀ w0 st_src0 st_tgt0 vret_src vret_tgt (SIM : RR w0 st_src0 st_tgt0 vret_src vret_tgt),
        s _ _ SS false false w0 (st_src0, k_src vret_src) (st_tgt0, k_tgt vret_tgt)) :
    lbindR r s _ _ SS ps pt w (st_src, ITree.bind i_src k_src) (st_tgt, ITree.bind i_tgt k_tgt).
  Hint Constructors lbindR : core.

  Lemma lbindR_mon r1 r2 s1 s2 (LEr : r1 <8= r2) (LEs : s1 <8= s2) :
    lbindR r1 s1 <8= lbindR r2 s2.
  Proof using. ii. destruct PR; econs; et. Qed.

  Definition lbindC r := lbindR r r.
  Hint Unfold lbindC : core.
  Hint Resolve lbindR_mon : paco.

  Lemma lbindC_wrespectful : wrespectful8 (_lsim) lbindC.
  Proof using.
    econs; eauto with paco.
    i. inv PR; csc.
    remember (st_src, i_src). remember(st_tgt, i_tgt).
    move SIM before GF. revert_until SIM. eapply GF in SIM.
    pattern x3, x4, x5, p, p0.
    eapply lsim_tarski, SIM.
    i. inv PR; clarify; grind; try econs.
    all: try by econs; eauto with arith.
    - exploit SIMK; eauto. i.
      eapply lsim_flag_mon with (ps0 := false) (pt0 := false); ss.
      eapply lsim_mon.
      + eapply lsim_wmon; eauto.
      + eauto using rclo8.
    - econs; eauto.
      exploit K; et. i. rewrite ->bind_bind in *.
      erewrite equal_f; eauto. do 3 eapply f_equal.
      extensionalities. rewrite bind_tau. eauto.
    - econs; eauto.
      exploit K; et. i. rewrite ->!bind_bind in *.
      erewrite f_equal; eauto. do 2 eapply f_equal.
      extensionalities. rewrite bind_tau. eauto.
    - econs; eauto. eapply rclo8_clo_base. eauto.
  Qed.

  Lemma lbindC_spec : lbindC <9= gupaco8 (_lsim) (cpn8 _lsim).
  Proof using. intros. eapply wrespect8_uclo; eauto with paco. eapply lbindC_wrespectful. Qed.
End LSIM.

Hint Resolve lsim_mon : paco.
Hint Resolve cpn8_wcompat : paco.

Section LSim.
  Variable (ms_src ms_tgt : LMod.t).

  Let fl_src := ms_src.(LMod.fnsems).
  Let fl_tgt := ms_tgt.(LMod.fnsems).
  Let st_src := ms_src.(LMod.initial_st).
  Let st_tgt := ms_tgt.(LMod.initial_st).

  Inductive lsim_mod : Type := mk {
    world : Type;
    winit : world;
    wf : list world → Any.t * Any.t → Prop;
    wle : world → world → Prop;
    wle_refl : Reflexive wle;
    wle_trans : Transitive wle;
    wf_winit : ∀ w st_src st_tgt (WF : wf w (st_src,st_tgt)), wf (w ++ [winit]) (st_src, st_tgt);
    sim_initial :
      ∀ it_src, fl_src !! entry = Some it_src →
        (∃ it_tgt, fl_tgt !! entry = Some it_tgt ∧
        ∀ arg, ∃ w0 w,
          lsim fl_src fl_tgt winit wf wle 0 top2 [w0] false false [w]
            (st_src, it_src arg) (st_tgt, it_tgt arg));
    sim_fnsems:
      ∀ fn fs, fl_src !! fid fn = Some fs →
        ∃ ft, fl_tgt !! fid fn = Some ft ∧
          ∀ my_tid, sim_fsem fl_src fl_tgt winit wf wle my_tid fs ft;
  }.

  Lemma wf_sim_miss :
    lsim_mod →
    ∀ fn, fl_tgt !! fn = None → fl_src !! fn = None.
  Proof using.
    intros Hsim fn. destruct (fl_src !! fn) eqn: EQ; eauto.
    destruct fn.
    - apply Hsim in EQ as [ft [Hft Hftsim]]; rewrite Hft; ss.
    - exploit (sim_initial Hsim); et; i; des; clarify.
  Qed.
End LSim.
