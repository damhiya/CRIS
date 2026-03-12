Require Export SModTr.
Require Import SchTactics.

(* specification for atomic LAIS *)
Record fspec_atomic `{Σ : GRA} : Type := mk_fspec_atomic {
  meta_priv : Type;
  meta_pub : Type;
  pre_priv : meta_priv → Any.t → iProp Σ;
  pre_pub : meta_priv → meta_pub → Any.t → iProp Σ;
  post_pub : meta_priv → meta_pub → Any.t → iProp Σ;
  post_priv : meta_priv → meta_pub → Any.t → iProp Σ;
}.
Global Arguments mk_fspec_atomic {Σ} _ _ _ _ _.

Notation "<<{ x arg ',' P '|' x_in ',' α '|' ret ',' β '|' Q }>>" :=
  ({|
    pre_priv := λ x arg, P;
    pre_pub := λ x x_in arg, α;
    post_pub := λ x x_in ret, β;
    post_priv := λ x x_in ret, Q;
  |})
  (at level 20, P, α, β, Q at level 200, x binder, x_in binder).

Definition fspec_sch_atomic `{!crisG Γ Σ α β τ Hsub Hinv, !schGS}
    (N : namespace) (fspa : fspec_atomic) : fspec_atomic := 
  <<{ '(((mtid, stid), x) : (nat * nat) * meta_priv fspa) arg,
    winv (↑N, ↑N) ∗ Tid mtid stid ∗ pre_priv fspa x arg |
    (x_in : meta_pub fspa),
    pre_pub fspa x x_in arg |
    ret,
      post_pub fspa x x_in ret |
      winv (↑N, ↑N) ∗ Tid mtid stid ∗ post_priv fspa x x_in ret
  }>>%I.

Notation "<{ x arg ',' P '|' x_in ',' α '|' ret ',' β '|' Q }> @ N" :=
  (fspec_sch_atomic N {|
    pre_priv := λ x arg, P;
    pre_pub := λ x x_in arg, α;
    post_pub := λ x x_in ret, β;
    post_priv := λ x x_in ret, Q;
  |})%I
  (at level 20, P, α, β, Q at level 200, x binder, x_in binder).


(* wrapper for fspec_atomic, similar to HoareFun in SModTr.v,
   but delivers the meta-variable to the body *)
Definition atomic_fun `{Σ : GRA}
    (fsp : fspec_atomic) (body : meta_priv fsp → Any.t → itree crisE (Any.t * meta_pub fsp))
    : fbody :=
  λ arg,
    x <- trigger (Take (meta_priv fsp));;
    trigger (Assume (pre_priv fsp x arg));;; (* private precondition *)
    '(ret, x2) : _ <- body x arg;;
    trigger (Guarantee (post_priv fsp x x2 ret));;; Ret ret. (* private postcondition *)

(* core atomic update point, which has the 'abort' facility as in Iris *)
Definition atomic_update `{Σ : GRA} (fsp : fspec_atomic)
    : meta_priv fsp → Any.t → itree crisE (Any.t * meta_pub fsp) :=
  λ x arg,
    ITree.iter (λ _ : (),
      𝒴;;;
        x_in <- trigger (Take (meta_pub fsp));;
        trigger (Assume (pre_pub fsp x x_in arg));;; (* public precondition *)
        ret <- trigger (Choose (() + Any.t));;
        match ret with
        | inl _ =>
          trigger (Guarantee (pre_pub fsp x x_in arg));;;
          Ret (inl tt) (* public precondition - abort *)
        | inr ret =>
          trigger (Guarantee (post_pub fsp x x_in ret));;; (* public postcondition *)
          𝒴;;; Ret (inr (ret, x_in))
        end
    ) tt.

Lemma unfold_atomic_update `{Σ : GRA} (fsp : fspec_atomic) (x : meta_priv fsp) (arg : Any.t) :
  atomic_update fsp x arg =
  𝒴;;;
    x_in <- trigger (Take (meta_pub fsp));;
    trigger (Assume (pre_pub fsp x x_in arg));;; (* public precondition *)
    ret <- trigger (Choose (() + Any.t));;
    match ret with
    | inl _ =>
      trigger (Guarantee (pre_pub fsp x x_in arg));;;
      tau;; atomic_update fsp x arg
    | inr ret =>
      trigger (Guarantee (post_pub fsp x x_in ret));;; (* public postcondition *)
      𝒴;;; Ret (ret, x_in)
    end.
Proof.
  rewrite {1}/atomic_update unfold_iter_eq; etrans; first hnorm_itr; grind.
  destruct x3; etrans; first hnorm_itr; grind.
Qed.

(* Lemmas for atomic_fun *)
Lemma atomic_fun_src
    `{!crisG Γ Σ α β τ Hinv Hsub}
    (fsp : fspec_atomic)
    (body : meta_priv fsp → Any.t → itree crisE (Any.t * meta_pub fsp))
    (arg : Any.t)
    (E1 E2 : coPset)
    (fls flt : gmap fname (option fbody))
    (Ist : ist_type Σ) (msk_s : emask) (sp : specmap)
    r g R_t RR ps pt sts stt itt :
  (∀ x , pre_priv fsp x arg -∗
    wsim fls flt Ist (E1, E2) r g _ R_t
      (λ '(sts, rets) '(stt, rett),
        post_priv fsp x rets.2 rets.1 ∗ winv (E1, E2) ∗
        wsim fls flt Ist (E1, E2) r g _ _ RR true false (sts, Ret rets.1) (stt, Ret rett))
      true pt (sts, SB.sandbox msk_s (SModTr.trans sp (body x arg))) (stt, itt)) ⊢
  wsim fls flt Ist (E1, E2) r g Any.t R_t RR ps pt
    (sts, SB.sandbox msk_s (SModTr.trans sp (atomic_fun fsp body arg))) (stt, itt).
Proof.
  iIntros "SIM".
  rewrite /atomic_fun.
  cStepS. case_match; cStepsS; ss. case_match; cStepsS; ss.
  rename _q into x. cStepsS. iPoseProof ("SIM" with "ASM") as "SIM".
  appendRetT. iApply wsim_bind. iFrame "SIM".
  clear_st. iIntros (st_src ret_src st_tgt ret_tgt) "[P [W SIM]]".
  iApply wsim_fold; iFrame "W".
  cStepS; case_match; cStepS; ss; clarify.
  cStepS; case_match; cStepS; ss; clarify.
  cForceS; iFrame "P". cStepsS. iApply "SIM".
Qed.

Lemma atomic_fun_src_sch
    `{!crisG Γ Σ α β τ Hinv Hsub, !schGS}
    (fsp : fspec_atomic)
    (N : namespace)
    (body : _ → Any.t → itree crisE (Any.t * meta_pub fsp))
    (arg : Any.t)
    (fls flt : gmap fname (option fbody))
    (Ist : ist_type Σ) (msk_s : emask) (sp : specmap)
    r g R_t RR ps pt sts stt itt :
  (∀ mtid stid (x : meta_priv fsp),
    Tid mtid stid -∗
    pre_priv fsp x arg -∗
    wsim fls flt Ist (↑N, ↑N) r g _ R_t
      (λ '(sts, rets) '(stt, rett),
        winv (↑N, ↑N) ∗ Tid mtid stid ∗ post_priv fsp x rets.2 rets.1 ∗
        wsim fls flt Ist (∅, ∅) r g _ _ RR true false (sts, Ret rets.1) (stt, Ret rett))
      true pt (sts, SB.sandbox msk_s (SModTr.trans sp (body ((mtid, stid), x) arg))) (stt, itt)) ⊢
  wsim fls flt Ist (∅, ∅) r g Any.t R_t RR ps pt
    (sts, SB.sandbox msk_s (SModTr.trans sp (atomic_fun (fspec_sch_atomic N fsp) body arg))) (stt, itt).
Proof.
  iIntros "SIM".
  rewrite /atomic_fun.
  cStepS. case_match; cStepsS; ss. case_match; cStepsS; ss.
  destruct _q as [[mtid stid] x]. iDestruct "ASM" as "[W [TID Pre]]".
  iApply wsim_fold; iFrame "W".
  iPoseProof ("SIM" with "TID Pre") as "SIM".
  appendRetT. iApply wsim_bind. iFrame "SIM".
  clear_st. iIntros (st_src ret_src st_tgt ret_tgt) "[W [TID [Post SIM]]]".
  cStepS; case_match; cStepS; ss; clarify.
  cStepS; case_match; cStepS; ss; clarify.
  cForceS; iFrame. cStepsS. iApply "SIM".
Qed.

Lemma atomic_fun_tgt
    `{!crisG Γ Σ α β τ Hinv Hsub}
    (fsp : fspec_atomic)
    (body : meta_priv fsp → Any.t → itree crisE (Any.t * meta_pub fsp)) (arg : Any.t)
    (E1 E2 : coPset)
    (fls flt : gmap fname (option fbody))
    (Ist : ist_type Σ) (msk_s msk_t : emask) (sp_s sp_t : specmap)
    r g R_s R_t RR ps pt sts ktt stt kts :
  (∀ X, msk_t _ (subevent _ (Take X))) →
  (∀ P, msk_t _ (subevent _ (Assume P))) →
  (∀ P, msk_t _ (subevent _ (Guarantee P))) →
  (∃ (x : meta_priv fsp), pre_priv fsp x arg ∗
    wsim fls flt Ist (E1, E2) r g _ _
      (λ '(sts, rets) '(stt, rett),
        winv (E1, E2) ∗
        (post_priv fsp x rett.2 rett.1 -∗
        wsim fls flt Ist (E1, E2) r g R_s R_t RR false true
          (sts, SB.sandbox msk_s (SModTr.trans sp_s Sch.yield) >>= kts)
          (stt, ktt rett.1)))
      ps true
      (sts, x <- SB.sandbox msk_s (SModTr.trans sp_s Sch.yield);; Ret x) 
      (stt, SB.sandbox msk_t (SModTr.trans sp_t (body x arg)))) -∗
  wsim fls flt Ist (E1, E2) r g R_s R_t RR ps pt
    (sts, SB.sandbox msk_s (SModTr.trans sp_s Sch.yield) >>= kts)
    (stt, SB.sandbox msk_t (SModTr.trans sp_t (atomic_fun fsp body arg)) >>= ktt).
Proof.
  iIntros (Htake Hassume Hguarantee) "[%x [Pre Cont]]".
  rewrite /atomic_fun.
  cStepT. rewrite Htake /=. cForceT x. cStepsT. rewrite Hassume. cStepsT. cForceT; iFrame "Pre".
  cStepsT. iApply wsim_yy_y. iApply wsim_bind; iSplitL "Cont".
  { appendRetS; iFrame. }
  clear_st. iIntros (st_s _ st_t [r_t x_in]) "[W Cont]". cStepsT. rewrite Hguarantee. cStepsT.
  iApply wsim_fold; iFrame "W". iPoseProof ("Cont" with "GRT") as "Cont". iFrame.
Qed.

(* Lemmas for atomic_updates *)
Lemma atomic_update_src
    `{!crisG Γ Σ α β τ Hinv Hsub, !schGS}
    (fsp : fspec_atomic) (x : meta_priv fsp) (arg : Any.t)
    (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ)
    (ps pt : bool) st_src st_tgt
    (Es : coPset) r g
    {Rt Rt1} (itt : itree crisE Rt1) (ktt : Rt1 → itree crisE Rt)
    RR
    (msk_s : emask)
    (sp_s : specmap) :
  (∀ x2, pre_pub fsp x x2 arg -∗
    (wsim fl_s fl_t Ist (Es, Es) r g Any.t Rt1
      (λ '(sts, _) '(stt, rett),
        winv (Es, Es) ∗
        ((pre_pub fsp x x2 arg ∗
          wsim fl_s fl_t Ist (Es, Es) r g _ Rt RR true false
            (sts, SB.sandbox msk_s (SModTr.trans sp_s (atomic_update fsp x arg)))
            (stt, ktt rett)) ∨
        (∃ rets, post_pub fsp x x2 rets ∗
          wsim fl_s fl_t Ist (Es, Es) r g _ Rt RR true false
            (sts, SB.sandbox msk_s (SModTr.trans sp_s Sch.yield);;; Ret (rets, x2))
            (stt, ktt rett))))
      true pt
      (st_src, Ret tt↑)
      (st_tgt, itt))) ⊢
  wsim fl_s fl_t Ist (Es, Es) r g _ Rt RR ps pt
    (st_src, SB.sandbox msk_s (SModTr.trans sp_s (atomic_update fsp x arg)))
    (st_tgt, itt >>= ktt).
Proof using.
  iIntros "SIM". rewrite {2}unfold_atomic_update. cNormS. sYieldS.
  cStepsS. case_match; cStepsS; ss. case_match; cStepsS; ss.
  case_match; cStepsS; ss.
  prependRetS (tt↑). iApply wsim_bind. iSplitL.
  { iApply "SIM"; iFrame. }
  s. clear_st. iIntros (? ? ? ?) "[W [[Pre Cont]|[%rets [Post Cont]]]]".
  { cForceS (inl tt). cStepsS. case_match; cStepsS; ss.
    cForceS; iFrame "Pre". cStepsS. iApply wsim_fold. iFrame.
  }
  cForceS (inr rets). cStepsS. case_match; cStepsS; ss. cForceS; iFrame "Post". cStepsS.
  iApply wsim_fold. iFrame "W". eapply eq_ind; first iApply "Cont".
  repeat f_equal; grind; extensionalities; sym; etrans; first hnorm_itr; ss.
Qed.

Lemma atomic_update_tgt
    `{!crisG Γ Σ α β τ Hinv Hsub, !schGS}
    (fsp : fspec_atomic) (x : meta_priv fsp) (arg : Any.t)
    (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ)
    (ps pt : bool) st_src st_tgt
    (Es : coPset) r g
    {R_s} (kts : _ → itree crisE R_s)
    RR
    (msk_s msk_t : emask)
    (sp_s sp_t : specmap) :
  (∀ X, msk_t _ (subevent _ (Take X)) = true) →
  (∀ P, msk_t _ (subevent _ (Assume P)) = true) →
  (wsim fl_s fl_t Ist (Es, Es) r g _ _
    (λ '(st_s, ret_s) '(st_t, ret_t), winv (Es, Es) ∗
      wsim fl_s fl_t Ist (Es, Es) r g _ _ RR false false
        (st_s, (SB.sandbox msk_s (SModTr.trans sp_s Sch.yield)) >>= kts)
        (st_t, Ret (ret_t)))
    ps pt
    (st_src, x <- SB.sandbox msk_s (SModTr.trans sp_s Sch.yield);; Ret x)
    (st_tgt, SB.sandbox msk_t (SModTr.trans sp_t (atomic_update fsp x arg))))
        ⊢
  wsim fl_s fl_t Ist (Es, Es) r g R_s (Any.t * meta_pub fsp) RR ps pt
    (st_src, SB.sandbox msk_s (SModTr.trans sp_s Sch.yield) >>= kts)
    (st_tgt, SB.sandbox msk_t (SModTr.trans sp_t (atomic_update fsp x arg))).
Proof using.
  iIntros (Htake Hassume) "SIM".
  iApply wsim_yy_y. appendRetT. iApply wsim_bind. iSplitL "SIM".
  { appendRetS. iApply "SIM". }
  clear_st. iIntros (st_s [] st_t [ret_t x_in]) "[W SIM]".
  iApply wsim_fold; iFrame "W". iApply "SIM".
Qed.

Lemma atomic_update_yield_ir
    `{!crisG Γ Σ α β τ Hinv Hsub, !schGS}
    (fsp : fspec_atomic) (x : meta_priv fsp) (arg : Any.t)
    (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ)
    (R_t : Type) RR
    (ps pt : bool) st_src st_tgt
    (Es : coPset) r g
    (k_t : () → itree crisE R_t)
    (msk_s msk_t : emask)
    (sp_s sp_t : specmap)
    (mtid stid : nat) :
  sp_s.1 !! fid SchHdr.yield = fsp_some (SchA.yield_spec Es) →
  sp_t.1 !! fid SchHdr.yield = None →
  (∀ X, msk_t _ (subevent _ (Choose X))) →
  (msk_t _ (subevent _ (Call SchHdr.yield ()↑))) →
  Ist st_src st_tgt ∗ Tid mtid stid ∗
  (∀ st_src st_tgt,
    Ist st_src st_tgt -∗ Tid mtid stid -∗
    wsim fl_s fl_t Ist (Es, Es) r g _ R_t RR true true
      (st_src, (SB.sandbox msk_s (SModTr.trans sp_s (atomic_update fsp x arg))))
      (st_tgt, k_t tt)) ⊢
  wsim fl_s fl_t Ist (Es, Es) r g _ R_t RR ps pt
    (st_src, (SB.sandbox msk_s (SModTr.trans sp_s (atomic_update fsp x arg))))
    (st_tgt, (SB.sandbox msk_t (SModTr.trans sp_t 𝒴)) >>= k_t).
Proof using.
  iIntros (????) "[IST [TID SIM]]".
  rewrite /atomic_update; unfoldIterS; cStepsS.
  sYieldIR "IST" "TID". iPoseProof ("SIM" with "IST TID") as "SIM".
  eapply eq_ind; first iApply "SIM".
  repeat f_equal. rewrite unfold_iter_eq.
  etrans; first hnorm_itr; f_equal.
Qed.

Lemma atomic_update_yield_rr
    `{!crisG Γ Σ α β τ Hinv Hsub, !schGS}
    (fsp : fspec_atomic) (x : meta_priv fsp) (arg : Any.t)
    (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ)
    (Rt : Type) RR
    (ps pt : bool) st_src st_tgt
    (Es : coPset) r g
    (k_t : () → itree crisE Rt)
    (msk_s msk_t : emask)
    (sp_s sp_t : specmap) :
  sp_s.1 !! fid SchHdr.yield = None →
  sp_t.1 !! fid SchHdr.yield = None →
  (∀ X, msk_t _ (subevent _ (Choose X))) →
  (msk_t _ (subevent _ (Call SchHdr.yield ()↑))) →
  Ist st_src st_tgt ∗
  (∀ st_src st_tgt,
    Ist st_src st_tgt -∗
    wsim fl_s fl_t Ist (Es, Es) r g _ Rt RR true true
      (st_src, (SB.sandbox msk_s (SModTr.trans sp_s (atomic_update fsp x arg))))
      (st_tgt, k_t tt)) ⊢
  wsim fl_s fl_t Ist (Es, Es) r g _ Rt RR ps pt
    (st_src, SB.sandbox msk_s (SModTr.trans sp_s (atomic_update fsp x arg)))
    (st_tgt, SB.sandbox msk_t (SModTr.trans sp_t 𝒴) >>= k_t).
Proof using.
  iIntros (????) "[IST SIM]".
  rewrite /atomic_update; unfoldIterS; cStepsS.
  sYieldRR "IST". iPoseProof ("SIM" with "IST") as "SIM".
  eapply eq_ind; first iApply "SIM".
  repeat f_equal. rewrite unfold_iter_eq.
  etrans; first hnorm_itr; f_equal.
Qed.

Lemma atomic_update_yield_ii
    `{!crisG Γ Σ α β τ Hinv Hsub, !schGS}
    (fsp : fspec_atomic) (x : meta_priv fsp) (arg : Any.t)
    (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ)
    (Rt : Type) RR
    (ps pt : bool) st_src st_tgt
    (E Es Et : coPset) r g
    (k_t : () → itree crisE Rt)
    (msk_s msk_t : emask)
    (sp_s sp_t : specmap) :
  sp_s.1 !! fid SchHdr.yield = fsp_some (SchA.yield_spec Es) →
  sp_t.1 !! fid SchHdr.yield = fsp_some (SchA.yield_spec Et) →
  img_msk msk_t →
  (∀ fn arg, msk_t _ (subevent _ (Call fn arg)) = true) →
  Et ⊆ Es →
  E = Es ∖ Et →
  Ist st_src st_tgt ∗
  (∀ st_src st_tgt,
    Ist st_src st_tgt -∗
    wsim fl_s fl_t Ist (E, E) r g _ Rt RR true true
      (st_src, (SB.sandbox msk_s (SModTr.trans sp_s (atomic_update fsp x arg))))
      (st_tgt, k_t tt)) ⊢
  wsim fl_s fl_t Ist (E, E) r g _ Rt RR ps pt
    (st_src, SB.sandbox msk_s (SModTr.trans sp_s (atomic_update fsp x arg)))
    (st_tgt, SB.sandbox msk_t (SModTr.trans sp_t 𝒴) >>= k_t).
Proof using.
  iIntros (??????) "[IST SIM]".
  rewrite /atomic_update; unfoldIterS; cStepsS.
  sYieldII "IST". iPoseProof ("SIM" with "IST") as "SIM".
  eapply eq_ind; first iApply "SIM".
  repeat f_equal. rewrite unfold_iter_eq.
  etrans; first hnorm_itr; f_equal.
Qed.
