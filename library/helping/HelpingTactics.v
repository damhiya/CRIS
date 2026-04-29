Require Import CRIS.
Require Export HelpingOn HelpingOff.
Require Import SchHeader SchTactics SchI SchA.
From iris.algebra Require Import gmap_view coPset.

(* Resource algebra for the helping module *)
Class helpingGpreS `{!crisG Γ Σ α β τ _S _I} := HelpingG {
  #[local] helping_inG :: inG (prodR
    (optionR coPset_disjUR)
    (optionR (gmap_viewR nat (agreeR (leibnizO help_state))))) Γ;
  #[local] tokenG :: inG (exclR unitO) Γ;
}.
Global Hint Mode helpingGpreS - - - - - - - - : typeclass_instances.
Definition helpingΓ := #[
  prodR (optionR coPset_disjUR) (optionR (gmap_viewR nat (agreeR (leibnizO help_state))));
  exclR unitO
].
Global Instance subG_helpingpreS `{!crisG Γ Σ α β τ _S _I} : subG helpingΓ Γ → helpingGpreS.
Proof using. solve_inG. Qed.

Class helpingGS `{!crisG Γ Σ α β τ _S _I} := HelpingGS {
  #[local] helpingG :: helpingGpreS;
  help_name : gname;
}.

Section resource.
  Context `{!crisG Γ Σ α β τ _S _I, !helpingGS}.

  Definition Help (reqid : nat) (df : dfrac) (st : help_state) : iProp Σ :=
    own help_name
      (None, Some (gmap_view_frag (V:=agreeR $ leibnizO _) reqid df (to_agree st))).
  Definition syn_Help n (reqid : nat) (df : dfrac) (st : help_state) : GTerm.t n :=
    sown help_name
      (None, Some (gmap_view_frag (V:=agreeR $ leibnizO _) reqid df (to_agree st))).
  Global Instance SLRed_Help n reqid df st :
    SLRed n (syn_Help n reqid df st) (Help reqid df st).
  Proof. solve_sl_red. Qed.

  Definition HelpPend (reqid : nat) (N : option namespace) (arg : SAny.t) :=
    Help reqid (DfracOwn 1) (Pend N arg).
  Definition syn_HelpPend n (reqid : nat) (N : option namespace) (arg : SAny.t) :=
    syn_Help n reqid (DfracOwn 1) (Pend N arg).
  Global Instance SLRed_HelpPend n reqid N arg :
    SLRed n (syn_Help n reqid N arg) (Help reqid N arg).
  Proof. solve_sl_red. Qed.

  Definition HelpDone (reqid : nat) (ret : SAny.t) :=
    Help reqid (DfracDiscarded) (Done ret).
  Definition syn_HelpDone n (reqid : nat) (ret : SAny.t) :=
    syn_Help n reqid (DfracDiscarded) (Done ret).
  Global Instance SLRed_HelpDone n reqid ret :
    SLRed n (syn_HelpDone n reqid ret) (HelpDone reqid ret).
  Proof. solve_sl_red. Qed.

  Lemma Help_persist (reqid : nat) (q : frac) (st : help_state) :
    Help reqid (DfracOwn q) st ==∗ Help reqid DfracDiscarded st.
  Proof.
    rewrite /Help own_update; [iIntros "> $ //"|apply prod_update; [reflexivity|]].
    apply option_update, gmap_view_frag_persist.
  Qed.

  Global Instance Help_persistent tid ret : Persistent (Help tid DfracDiscarded (Done ret)).
  Proof. apply _. Qed.

  Definition syn_HelpAuth n (reqmap : gmap nat help_state) : GTerm.t n :=
    (sown help_name (None,
      Some (gmap_view_auth (DfracOwn 1)
        (to_agree <$> reqmap : gmap nat (agreeR (leibnizO help_state))))))%SAT.
  Definition HelpAuth (reqmap : gmap nat help_state) : iProp Σ :=
    own help_name (None,
      Some (gmap_view_auth (DfracOwn 1)
        (to_agree <$> reqmap : gmap nat (agreeR (leibnizO help_state))))).
  Global Instance SLRed_HelpAuth n reqmap :
    SLRed n (syn_HelpAuth n reqmap) (HelpAuth reqmap).
  Proof. solve_sl_red. Qed.

  Definition hinv_ownE (E : coPset) : iProp Σ := own help_name (Some (CoPset E), None).
  Definition syn_hinv_ownE {n : level} (E : coPset) : GTerm.t n :=
    sown help_name (Some (CoPset E), None).
  Global Instance SLRed_hinv_ownE n E :
    SLRed n (syn_hinv_ownE E) (hinv_ownE E).
  Proof. solve_sl_red. Qed.

  Lemma hinv_ownE_exploit (E1 E2 : coPset) : hinv_ownE E1 ∗ hinv_ownE E2 ⊢ ⌜E1 ## E2⌝.
  Proof.
    iIntros "[H1 H2]". iCombine "H1 H2" gives %[WF _]%pair_valid.
    by rewrite /= -Some_op Some_valid coPset_disj_valid_op in WF.
  Qed.
  Lemma hinv_ownE_op (E1 E2 : coPset) : E1 ## E2 →
    hinv_ownE (E1 ∪ E2) ⊣⊢ hinv_ownE E1 ∗ hinv_ownE E2.
  Proof using. intros dis; rewrite -own_op -pair_op -Some_op coPset_disj_union; ss. Qed.
  Lemma hinv_ownE_subset (E1 E2 : coPset) :
    E1 ⊆ E2 →
    hinv_ownE E2 ⊢ hinv_ownE E1 ∗ (hinv_ownE E1 -∗ hinv_ownE E2).
  Proof using.
    iIntros (SUB) "E".
    rewrite (union_difference_L E1 E2); [|done].
    iPoseProof (hinv_ownE_op with "E") as "[E1 E2]"; [set_solver|].
    iFrame. iIntros "E1".
    iApply hinv_ownE_op; [set_solver|iFrame].
  Qed.

  (* designated state invariant for modules that use the helping module *)
  Definition IstHelp_gen (Ist : ist_type Σ) (mn : string) (E : coPset) : ist_type Σ :=
    IstProd
      (IstSB [mn]
        (λ st_s st_t,
          hinv_ownE E ∗
          ∃ (st_s2 : gmap key (option Any.t)) (m : gmap nat help_state),
            ⌜st_s = {[HelpingOn.v_reqs mn # m↑]} +# st_s2⌝ ∗ HelpAuth m ∗
            Ist st_s2 st_t)%I) IstEq.
  Definition IstHelp (mn : string) (E : coPset) : ist_type Σ :=
    IstHelp_gen IstTrue mn E.

  Definition help_init_cond : iProp Σ :=
    HelpAuth ∅ ∗ hinv_ownE ⊤.

  (* a variant of cancellable invariants to streamline invariant opening/closing in helping *)
  Definition hinv {n : level} (N : namespace) (γ : gname) (P : GTerm.t n) : iProp Σ :=
    inv n N (sown γ (Excl ()) ∗ P ∨ syn_hinv_ownE (↑N))%SAT.
  Definition syn_hinv {n : level} (N : namespace) (γ : gname) (P : GTerm.t n) : GTerm.t n :=
    syn_inv N (sown γ (Excl ()) ∗ P ∨ syn_hinv_ownE (↑N))%SAT.
  Global Instance SLRed_hinv n N γ P :
    SLRed n (syn_hinv N γ P) (hinv N γ P).
  Proof. solve_sl_red. Qed.

  Global Instance hinv_persistent {n : level} N γ (P : GTerm.t n) : Persistent (hinv N γ P).
  Proof. rewrite /hinv; apply _. Qed.

  Lemma hinv_excl_alloc : ⊢ o=> ∃ γ, own γ (Excl ()).
  Proof. iApply own_alloc; ss. Qed.

  Lemma hinv_alloc `(P : GTerm.t n) Ew E N :
    ↑N ⊆ Ew →
    ⟦P⟧ =|S n, Ew|={E}=∗ ∃ γ, hinv N γ P.
  Proof.
    iIntros (?) "HP". iMod hinv_excl_alloc as "[%γ Hexcl]"; iExists γ.
    iApply inv_alloc; ss.
    rewrite SPropBi.or_red_base; iLeft. rewrite SPropBi.sep_red_base SPropiProp.own_red; iFrame.
  Qed.

  (* If we own the namespace of the invariant, then we can open the invariant atomically. *)
  Lemma hinv_acc {n : level} Ew E F N γ (P : GTerm.t n) :
    ↑N ⊆ E → ↑N ⊆ F → E ⊆ Ew →
    hinv N γ P -∗
    hinv_ownE F =|S n, Ew|={E, E∖↑N}=∗ ⟦P⟧ ∗ hinv_ownE (F∖↑N) ∗
      (⟦P⟧ -∗ hinv_ownE (F∖↑N) =|S n, Ew|={E∖↑N,E}=∗ hinv_ownE F) ∧
      (=|S n, Ew|={E∖↑N, E}=> (⟦P⟧ -∗ hinv_ownE (F∖↑N) =|S n, Ew|={E}=∗ hinv_ownE F)).
  Proof.
    iIntros (???) "#Hinv HE".
    iInv "Hinv" as "[[Hexcl $]|HE2]" "close"; cycle 1.
    { iPoseProof (hinv_ownE_exploit with "[HE HE2]") as "%Hcont"; iFrame.
      pose proof (nclose_infinite N) as HN; rewrite -coPset_infinite_finite in HN.
      specialize (HN []) as [i [Hi _]]; set_solver.
    }
    rewrite [F as X in hinv_ownE X](union_difference_L (↑N) F) //.
    rewrite (hinv_ownE_op (↑N)); last set_solver. 
    iDestruct "HE" as "[HN $]".
    iModIntro; iSplit.
    { iIntros "P $"; iFrame. iMod ("close" with "[-]") as "_"; eauto with iFrame. }
    iMod ("close" with "[HN]") as "_"; first eauto with iFrame.
    iIntros "!> P HE2".
    iInv "Hinv" as "[[Hexcl' _] | HE]" "Hclose".
    { iCombine "Hexcl" "Hexcl'" gives %[]. }
    iFrame. iApply ("Hclose" with "[-]"); first eauto with iFrame.
  Qed.

  Global Instance into_inv_hinv N γ `{P : GTerm.t n} : IntoInv (hinv N γ P) N := {}.

  Global Instance into_acc_hinv Ist Ew E F N γ mn st_s st_t `{p : GTerm.t n} (P : iProp Σ) :
    SLRed n p P →
    IntoAcc (X:=unit) (hinv N γ p)
            (↑N ⊆ E ∧ E ⊆ Ew) (⌜↑N ⊆ F⌝ ∗ IstHelp_gen Ist mn F st_s st_t)
            (fupd_ex (S n) Ew E (E∖↑N)) bupd
            (λ _, IstHelp_gen Ist mn (F∖↑N) st_s st_t ∗ P)%I (λ _, emp)%I
            (λ _, Some
              ((P -∗ ∀ st_s st_t,
                IstHelp_gen Ist mn (F∖↑N) st_s st_t =|S n, Ew|={E∖↑N, E}=∗
                  IstHelp_gen Ist mn F st_s st_t) ∧
              (=|S n, Ew|={E∖↑N, E}=>
                (P -∗ ∀ st_s st_t, IstHelp_gen Ist mn (F∖↑N) st_s st_t =|S n, Ew|={E}=∗
                  IstHelp_gen Ist mn F st_s st_t))))%I.
  Proof.
    rewrite /IntoAcc /accessor bi.exist_unit /=.
    iIntros (<- [? ?]) "#Hinv [% [% [% [% [% [$ [[$ [HE IST]] $]]]]]]]".
    iMod (hinv_acc with "Hinv HE") as "[$ [HE Close]]"; eauto. iFrame "HE IST".
    iIntros "!> _ !>"; iFrame.
    iSplit; [iDestruct "Close" as "[Close _]"|iDestruct "Close" as "[_ > Close]"].
    { iIntros "P * [% [% [% [% [$ [[$ [HE $]] $]]]]]]". iApply ("Close" with "[$] [$]"). }
    iIntros "!> P * [% [% [% [% [$ [[$ [HE $]] $]]]]]]". iApply ("Close" with "[$] [$]").
  Qed.

  Lemma HelpAuth_Help reqmap reqid df st :
    HelpAuth reqmap -∗ Help reqid df st -∗ ⌜reqmap !! reqid = Some st⌝.
  Proof.
    iIntros "● ◯".
    iCombine "● ◯" gives %[_ WF]; rewrite /= -Some_op Some_valid in WF.
    eapply gmap_view_both_dfrac_valid_discrete in WF as [? [? [_ [WF [_ INCL]]]]].
    eapply Some_pair_included_r in INCL as INCL.
    rewrite lookup_fmap_Some in WF; destruct WF as [? [<- Hwf]]; rewrite Hwf.
    rewrite Some_included_total to_agree_included_L in INCL; clarify.
  Qed.

  Lemma Help_update reqmap reqid st1 st2 :
    HelpAuth reqmap -∗ Help reqid (DfracOwn 1) st1 ==∗
    HelpAuth (<[reqid := st2]> reqmap) ∗ Help reqid (DfracOwn 1) st2.
  Proof.
    rewrite /HelpAuth /Help; iIntros "● ◯".
    iPoseProof (HelpAuth_Help with "● ◯") as "%".
    iMod (own_update_2 with "● ◯") as "[$ $]"; eauto.
    eapply prod_update; ss; rewrite -!Some_op; eapply option_update.
    etrans; first eapply gmap_view_replace.
    { instantiate (1:=to_agree st2); ss. }
    rewrite fmap_insert //.
  Qed.
End resource.

Lemma help_alloc `{!crisG Γ Σ α β τ Hsub Hinv, !helpingGpreS} :
  ⊢ o=> ∃ (_ : helpingGS), help_init_cond.
Proof.
  iMod (own_alloc ((Some (CoPset ⊤), None) ⋅ (None, Some (gmap_view_auth (DfracOwn 1) ∅))))
    as "[%γh [? ?]]".
  { rewrite -pair_op left_id right_id; split; ss. apply Some_valid, gmap_view_auth_valid. }
  pose (HelpingGS _ _ _ _ _ _ _ _ _ γh) as Ht.
  by iExists Ht; iFrame.
Qed.

Section help.
  Context `{!crisG Γ Σ α β τ _S _I, !helpingGS}.

  Local Notation state := (gmap key (option Any.t)).
  Local Notation post R_s R_t := (state * R_s → state * R_t → iProp Σ).

  Context (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t))).
  Context (R_s R_t : Type) (RR : post R_s R_t).

  (* Helping related context *)
  Context (jobs : SAny.t → itree crisE (SAny.t + SAny.t)).
  Context (mn : string) (sp : specmap).

  Lemma wsim_helping_run
      (ps pt : bool)
      (st_src st_tgt : state)
      (N : option namespace)
      (Ist : ist_type Σ)
      (F : coPset)
      (parg : SAny.t)
      k_s k_t E1 E2 r g :
    fl_s !! funid (Helping.run mn) =
      Some (Some (SB.sandbox_body
        (msk_scp (HelpingOn.scopes mn) msk_true, (SModTr.trans_fnsem sp (None, HelpingOn.run mn jobs))))) →
    IstHelp_gen Ist mn F st_src st_tgt -∗
    (∀ st_src2 reqid, IstHelp_gen Ist mn F st_src2 st_tgt -∗ HelpPend reqid N parg -∗
      wsim fl_s fl_t (IstHelp_gen Ist mn F) (E1, E2) r g R_s R_t RR true pt
        (st_src2,
          x <- SB.sandbox (msk_scp (HelpingOn.scopes mn) msk_true) (
            SModTr.trans sp (𝒴@{N};;; HelpingOn.try_run mn jobs reqid));;
          tau;; k_s x)
        (st_tgt, k_t)) -∗
    wsim fl_s fl_t (IstHelp_gen Ist mn F) (E1, E2) r g R_s R_t RR ps pt
      (st_src, x <- (trigger (Call (Helping.run mn) (N, parg)↑));; k_s x)
      (st_tgt, k_t).
  Proof.
    iIntros (Hfind) "IST K".
    cInlineS. cStepsS. rewrite /HelpingOn.run. cStepsS.
    iDestruct "IST" as "[% [% [% [% [[-> ->] [[%Hscp [HE [%st_s2 [%m [-> [Help● IST]]]]]] ->]]]]]]".
    cStepsS.
    iMod (own_update _ _ ((None, _) ⋅ (None, _)) with "Help●") as "[Help● Help◯]".
    { eapply prod_update; ss.
      etransitivity; first apply option_update.
      { eapply (gmap_view_alloc _ (fresh (dom m)) (DfracOwn 1)); eauto.
        { apply not_elem_of_dom. rewrite dom_fmap. apply is_fresh. }
        { rewrite dfrac_valid; eauto. }
        { instantiate (1:=(to_agree (Pend N parg))); ss. }
      }
      rewrite Some_op //.
    }
    rewrite -fmap_insert.
    replace_s; last (iApply ("K" with "[HE Help● IST] [$]"); iFrame).
    { symmetry; etrans; first hnorm_itr; grind. }
    iPureIntro; esplits; try by des.
    revert Hscp; rewrite !dom_union_with !dom_insert_L; by i; des.
  Qed.

  Lemma wsim_helping_pend_try_run
      (reqid : nat) (N : option namespace) (arg : SAny.t)
      (Ist : ist_type Σ) (F : coPset)
      (st_src st_tgt : state) (ps pt : bool)
      (ktr_s : Any.t → itree crisE R_s)
      {R} (itr_t : itree crisE R) (ktr_t : R → itree crisE R_t)
      E1 E2 r g :
    HelpPend reqid N arg -∗
    IstHelp_gen Ist mn F st_src st_tgt -∗
    (∀ st_src2,
      IstHelp_gen Ist mn F st_src2 st_tgt -∗
      wsim fl_s fl_t (IstHelp_gen Ist mn ⊤) (E1, E2) r g SAny.t R
        (λ '(st_s, r_s) '(st_t, r_t),
          IstHelp_gen Ist mn F st_s st_t ∗ winv (E1, E2) ∗
          (∀ st_src st_tgt,
            HelpDone reqid r_s -∗
            IstHelp_gen Ist mn F st_src st_tgt -∗
            wsim fl_s fl_t (IstHelp_gen Ist mn ⊤) (E1, E2) r g R_s R_t RR true false
              (st_src, ktr_s r_s↑) (st_tgt, ktr_t r_t)))
        true pt
          (st_src2, ⇓sbox(msk_scp (HelpingOn.scopes mn) msk_true)
            (⇓smod(sp) (ITree.iter (λ arg, 𝒴@{N};;; ⇓sbox(msk_pure) (jobs arg)) arg)))
          (st_tgt, itr_t)) -∗
    wsim fl_s fl_t (IstHelp_gen Ist mn ⊤) (E1, E2) r g R_s R_t RR ps pt
      (st_src,
        x_ <- ⇓sbox(msk_scp (HelpingOn.scopes mn) msk_true)
          (⇓smod(sp) (HelpingOn.try_run mn jobs reqid));;
        ktr_s x_)
      (st_tgt, itr_t >>= ktr_t).
  Proof.
    iIntros "Pend IST K".
    iDestruct "IST" as "[% [% [% [% [[-> ->] [[%Hscp [HE [%st_s2 [%m [-> [Help● IST]]]]]] ->]]]]]]".
    rewrite /HelpingOn.try_run. cStepsS.
    iPoseProof (HelpAuth_Help with "Help● Pend") as "%Hlookup"; rewrite Hlookup /=. cStepsS.
    iPoseProof (Help_update m reqid _ InProgress with "Help● Pend") as ">[Help● Help◯]".
    iAssert (IstHelp_gen Ist mn F _ _) with "[HE Help● IST]" as "IST".
    { iFrame; iPureIntro; ss; esplits; ss; last by des.
      move: Hscp; rewrite !dom_union_with !dom_insert_L; by i; des.
    }
    cBind _ "K IST" as (????) "Q".
    { iApply "K"; iFrame. }
    simpl. iDestruct "Q" as "[IST [W K]]".
    clear_st. clear dependent m. clear_st.
    iDestruct "IST" as "[% [% [% [% [[-> ->] [[%Hscp [HE [%st_s2 [%m [-> [Help● IST]]]]]] ->]]]]]]".
    cStepsS.
    iPoseProof (HelpAuth_Help with "Help● Help◯") as "%Hlookup".
    iPoseProof (Help_update m reqid _ (Done r_s) with "Help● Help◯") as ">[Help● Help◯]".
    iPoseProof (Help_persist with "Help◯") as "> Help◯".
    iAssert (IstHelp_gen Ist mn F _ _) with "[HE Help● IST]" as "IST".
    { iFrame; iPureIntro; ss; esplits; ss; last by des.
      move: Hscp; rewrite !dom_union_with !dom_insert_L; by i; des.
    }
    iApply wsim_fold; iFrame "W". iApply ("K" with "Help◯ IST").
  Qed.

  Lemma wsim_HelpDone_try_run
      (req_id : nat) (ret : SAny.t)
      (Ist : ist_type Σ) (F : coPset)
      (st_src st_tgt : state)
      (ps pt : bool)
      k_s k_t E1 E2 r g :
    HelpDone req_id ret -∗
    IstHelp_gen Ist mn F st_src st_tgt -∗
    (IstHelp_gen Ist mn F st_src st_tgt -∗
      wsim fl_s fl_t (IstHelp_gen Ist mn ⊤) (E1, E2) r g R_s R_t RR true pt (st_src, k_s ret↑) (st_tgt, k_t)) -∗
    wsim fl_s fl_t (IstHelp_gen Ist mn ⊤) (E1, E2) r g R_s R_t RR ps pt
      (st_src,
        x_ <- ⇓sbox(msk_scp (HelpingOn.scopes mn) msk_true)
          (⇓smod(sp) (HelpingOn.try_run mn jobs req_id));; k_s x_)
      (st_tgt, k_t).
  Proof.
    iIntros "#Done IST K".
    rewrite /HelpingOn.try_run /=. cStepsS.
    iDestruct "IST" as "[% [% [% [% [[-> ->] [[%Hscp [HE [%st_s2 [%m [-> [Help● IST]]]]]] ->]]]]]]".
    cStepsS. iPoseProof (HelpAuth_Help with "Help● Done") as "->". cStepsS.
    iAssert (IstHelp_gen Ist mn F _ _) with "[HE Help● IST]" as "IST".
    { iFrame; iPureIntro; ss; esplits; ss; last by des.
      move: Hscp; rewrite !dom_union_with !dom_insert_L; by i; des.
    }
    iApply ("K" with "IST").
  Qed.

  Lemma wsim_helping_help
      (reqid : nat) (N N2 : namespace) (E : coPset) (arg : SAny.t)
      (Ist : ist_type Σ) (F : coPset)
      r g
      (st_src st_tgt : WSim.state)
      (ps pt : bool)
      (ktr_s : Any.t → itree crisE R_s)
      {R} (itr_t : itree crisE R) (ktr_t : R → itree crisE R_t) :
    HelpPend reqid (Some N2) arg -∗
    IstHelp_gen Ist mn F st_src st_tgt -∗
    (∃ n, ∀ st_src, IstHelp_gen Ist mn F st_src st_tgt =|n, ↑N|={E, ↑N}=∗
      wsim fl_s fl_t (IstHelp_gen Ist mn ⊤) (↑N2, ↑N2) r g SAny.t R
      (λ '(st_s, r_s) '(st_t, r_t),
        ∃ F, IstHelp_gen Ist mn F st_s st_t ∗ winv (↑N2, ↑N2) ∗
        (∀ st_src st_tgt,
          HelpDone reqid r_s -∗
          (IstHelp_gen Ist mn F) st_src st_tgt -∗
          wsim fl_s fl_t (IstHelp_gen Ist mn ⊤) (↑N, ↑N) r g R_s R_t RR true false
            (st_src, ktr_s ()↑) (st_tgt, ktr_t r_t)))
      true pt
        (st_src, ⇓sbox(msk_scp (HelpingOn.scopes mn) msk_true)
          (⇓smod(sp) (ITree.iter (λ arg, 𝒴@{Some N2};;; ⇓sbox(msk_pure) (jobs arg)) arg)))
        (st_tgt, itr_t)) -∗
    wsim fl_s fl_t (IstHelp_gen Ist mn ⊤) (↑N, E) r g R_s R_t RR ps pt
      (st_src,
        x_ <- ⇓sbox(msk_scp (HelpingOn.scopes mn) msk_true)
          (⇓smod(sp) (HelpingOn.help mn jobs (Some N)↑));; ktr_s x_)
      (st_tgt, itr_t >>= ktr_t).
  Proof.
    iIntros "Tkn IST [%n SIM]".
    rewrite /HelpingOn.help. cStepsS. cForceS reqid.
    iDestruct "IST" as "[% [% [% [% [[-> ->] [[%Hscp [HE [%st_s2 [%m [-> [Help● IST]]]]]] ->]]]]]]".
    cStepsS. iPoseProof (HelpAuth_Help with "Help● Tkn") as "->". cStepsS.
    iMod (Help_update m reqid _ (InProgress) with "Help● Tkn") as "[Help● Help◯]".
    iMod ("SIM" with "[HE Help● IST]") as "SIM".
    { iFrame; repeat iExists _; iPureIntro; do 2 split; ss. split; last (eexists; eauto).
      move: Hscp; rewrite !dom_union_with !dom_insert_L; i; des; split; eauto.
    }
    cForceS; iSplit; first done. cStepsS.
    cBind _ "SIM" as (????) "[%F2 Q]". iDestruct "Q" as "[IST [W K]]".
    iApply wsim_fold; iFrame "W".
    cForceS. iSplit; first done. cStepsS. clear dependent m; clear_st.
    iDestruct "IST" as "[% [% [% [% [[-> ->] [[%Hscp [HE [%st_s2 [%m [-> [Help● IST]]]]]] ->]]]]]]".
    cStepsS.
    iMod (Help_update m reqid _ (Done r_s) with "Help● Help◯") as "[Help● Help◯]".
    iAssert (IstHelp_gen Ist mn F2 _ _) with "[HE Help● IST]" as "IST".
    { iFrame; iPureIntro; ss; esplits; ss; last by des.
      move: Hscp; rewrite !dom_union_with !dom_insert_L; by i; des.
    }
    iMod (Help_persist with "Help◯") as "Help◯".
    iApply ("K" with "Help◯ IST").
  Qed.

  (*
  Lemma wsim_helping_help2
      `{!schGS} (st_src st_tgt : state)
      (ps pt : bool) k_s k_t E r g (req_id : nat) x arg (mtid stid : nat) :
    sp.1 !! (fid SchHdr.yield) = fsp_some (SchA.yield_spec E) →
    Tid mtid stid -∗
    HelpPend req_id x -∗
    (∃ n, =| n, E |={ E, ∅ }=> Ist st_src st_tgt ∗
      (wsim fl_s fl_t Ist (E, ∅) r g SAny.t ()
        (λ '(st_s, r_s) '(st_t, r_t), ⌜st_s = st_src ∧ st_t = st_tgt⌝ ∗ winv (E, ∅) ∗
          (∀ st_src st_tgt,
            HelpDone req_id r_s -∗
            Ist st_src st_tgt =| n, E |={ ∅, E }=∗
            (Tid mtid stid -∗
            wsim fl_s fl_t Ist (E, E) r g R_s R_t RR true false
              (st_src, k_s ()↑) (st_tgt, k_t))))
        true pt
          (st_src, SB.sandbox (msk_scp (HelpingOn.scopes mn) msk_true)
            (SModTr.trans sp (SB.sandbox msk_pure (jobs x))))
          (st_tgt, Ret ()))) -∗
    wsim fl_s fl_t Ist (E, E) r g R_s R_t RR ps pt
      (st_src,
        x_ <- SB.sandbox (msk_scp (HelpingOn.scopes mn) msk_true)
          (SModTr.trans sp (HelpingOn.help mn jobs sp arg));; k_s x_)
      (st_tgt, k_t).
  Proof using Hist.
    iIntros (Hsp) "TID Tkn [%n SIM]".
    rewrite /HelpingOn.help Hsp.
    cForceS req_id. cForceS (stid, mtid, tt). cForcesS. iFrame. iSplit; eauto.
    cStepsS. destruct _q as [[stid1 mtid1] []]. iDestruct "ASM" as "[TID [_ ->]]".
    iMod ("SIM") as "[IST SIM]".
    iApply (wsim_helping_pend_try_run with "Tkn IST").
    appendRetS. appendRetT. cBind _ "SIM" as (sts1 stt1 rets []) "[[-> ->] [? SIM]]".
    iApply wsim_fold; iFrame.
    cStep; iFrame. iSplit; first auto.
    clear_st. iIntros (st_src st_tgt) "Tkn IST".
    iMod ("SIM" $! st_src st_tgt with "Tkn IST") as "SIM".
    cForcesS. iFrame. iSplit; eauto.
    cStepsS. iDestruct "ASM" as "[TID [_ ->]]". iApply ("SIM" with "[$]"); done.
  Qed. *)

  (* Lemma IstHelp_split (q : Qp) :
    (q < 1)%Qp →
    IstHelp Ist st_src st_tgt -∗
    (∃ reqmap, HelpAuth q reqmap ∗ (HelpAuth q reqmap -∗ IstHelp Ist st_src st_tgt)).
  Proof.
    iIntros (Hq) "[% [% [% [% [% [Help● IST]]]]]]".
    assert (Hr : (∃ r, 1 - q = Some r)%Qp).
    { destruct (1 - q)%Qp as [r'|] eqn : Hq'; first eauto.
      apply Qp.sub_None in Hq'. exfalso. apply (StrictOrder_Asymmetric _ q 1%Qp); eauto.
      apply Qp.le_lteq in Hq'; des; subst; eauto.
    }
    destruct Hr as [r Hr%Qp.sub_Some]; rewrite Hr {1}/HelpAuth.
    rewrite -dfrac_op_own.
    iExists reqmap; iDestruct "Help●" as "[$ H]".
    iIntros "H2"; iCombine "H" "H2" as "H"; rewrite comm -Hr; iFrame; iExists _; ss.
  Qed.

  Lemma IstHelp_done req_id job_id (reqmap : gmap nat help_state) (ret : SAny.t) :
    HelpPend req_id job_id -∗
    IstHelp Ist ((HelpingOn.v_reqs mn, reqmap↑) :: st_src) st_tgt ==∗
    HelpDone req_id ret ∗
    IstHelp Ist
      ((HelpingOn.v_reqs mn, (<[req_id := (Some ret, job_id)]> reqmap)↑) :: st_src) st_tgt.
  Proof.
    iIntros "Help [% [% [% [% [% [Help● IST]]]]]]".
    iMod (own_update_2 with "Help● Help") as "[Help● Help]".
    { eapply gmap_view_replace. instantiate (1:=(to_agree (Some ret, job_id))); done. }
    iMod (own_update with "Help") as "$".
    { eapply gmap_view_frag_persist. }
    iExists _, _, _, _; iModIntro; iSplit; first done.
    rewrite -fmap_insert; iFrame "Help●"; done.
  Qed.

  (* TODO : modify helping so that we do not see cput after job execution *)
  Lemma wsim_helping_try_run (req_id : nat) (parg : SAny.t) k_s k_t E1 E2 r g img_t msk_t scp_t :
    HelpPend req_id parg -∗
    IstHelp Ist st_src st_tgt -∗
    (∀ (reqmap : gmap nat help_state) st_src0,
      HelpPend req_id parg -∗
      IstHelp Ist ((HelpingOn.v_reqs mn, reqmap↑) :: st_src0) st_tgt -∗
      wsim fl_s fl_t (IstHelp Ist) (E1, E2) r g R_s R_t RR true pt
        ((HelpingOn.v_reqs mn, reqmap↑) :: st_src0,
          x_ <- SB.sandbox true wmask_all (HelpingOn.scopes mn) (SModTr.trans true sp
            (r <- Helping.trans (jobs parg);;
            (cput (HelpingOn.v_reqs mn) (<[req_id := (Some r, parg)]> reqmap));;;
            Ret (r)));;
          x_0 <- SB.sandbox true wmask_all (HelpingOn.scopes mn) (SModTr.trans true sp
            (𝒴;;; Ret (x_↑)));;
          x_1 <- (tau;; Ret x_0);;
          x_2 <- (SB.sandbox img_t msk_t scp_t (Ret x_1));; k_s x_2)
        (st_tgt, k_t)) -∗
    wsim fl_s fl_t (IstHelp Ist) (E1, E2) r g R_s R_t RR ps pt
      (st_src,
        x_ <- SB.sandbox (msk_scp (HelpingOn.scopes mn) msk_true)
          (SModTr.trans sp (HelpingOn.help mn jobs sp arg));; k_s x_)
      (st_tgt, k_t).
  Proof.
    iIntros "Help IST K".
    iDestruct "IST" as "[% [% [% [% [[-> ->] [Help● IST]]]]]]".
    rewrite /HelpingOn.try_run.
    cStepsS. rename _q into reqmap.
    iCombine "Help●" "Help" gives %[v' [? [_ [WF [_ EQ]]]]]%gmap_view_both_dfrac_valid_discrete.
    apply lookup_fmap_Some in WF as [[ro parg'] [? Hlookup]]; clarify.
    rewrite Hlookup. apply Some_pair_included in EQ as [_ EQ].
    rewrite Some_included_total to_agree_included in EQ; inv EQ; clarify.
    iApply ("K" $! reqmap st_src1 with "Help"). iFrame. eauto.
  Qed. *)
End help.
