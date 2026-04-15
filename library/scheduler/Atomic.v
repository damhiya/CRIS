Require Export SModTr atomic.
Require Import SchTactics.

Notation "'⇓sbox(' msk ')'" := (SB.sandbox msk) (only parsing).
Notation "'⇓smod(' sp ')'" := (SModTr.trans sp) (only parsing).

Program Global Instance fspec_winv `{!crisG Γ Σ α β τ _S _I} P E
  : WP (winv (E, E) ∗ P) := {| WP_space := E; WP_remainder := P |}.
Next Obligation. intros; iSplit; iIntros "[$ $]". Qed.

(* wrapper for atomic_fspec, similar to HoareFun in SModTr.v,
   but delivers the meta-variable to the body *)
Definition atomic_fun `{!crisG Γ Σ α β τ Hsub Hinv, !schGS} {X X2 : Type}
    (N : namespace)
    (P : X → iProp Σ)
    (body : X → itree crisE (Any.t * X2))
    (Q : X → X2 → Any.t → iProp Σ)
    : itree crisE Any.t :=
  '((mtid, stid), x) : _ <- trigger (Take ((nat * nat) * X));;
  trigger (Assume (winv (↑N, ↑N) ∗ Tid mtid stid ∗ P x));;; (* private precondition *)
  '(ret, x2) : _ <- body x;;
  trigger (Guarantee (winv (↑N, ↑N) ∗ Tid mtid stid ∗ Q x x2 ret));;; Ret ret. (* private postcondition *)

Notation "'{{{' ∀∀ x ',' P '}}}' body '{{{' ∀∀ x2 ',' 'RET' ret ',' Q '}}}' '@' N" :=
  (atomic_fun N (λ x, P) (λ x, body) (λ x x2 ret, Q))%I
  (at level 20, N, P, body, Q at level 200, x binder, x2 binder, ret binder,
   format "'{{{'  ∀∀  x ,  '/' P '}}}'  '/' body  '/' '{{{'  ∀∀  x2 ,  '/' 'RET'  ret ,  '/' Q  '}}}' '@'  N").
Notation "'{{{' P '}}}' body '{{{' ∀∀ x2 ',' 'RET' ret ',' Q '}}}' '@' N" :=
  (atomic_fun N (λ _, P) (λ _, body) (λ _ x2 ret, Q) )%I
  (at level 20, N, P, body, Q at level 200, x2 binder, ret binder,
   format "'{{{' P '}}}'  '/' body  '/' '{{{'  ∀∀  x2 ,  '/' 'RET'  ret ,  '/' Q  '}}}' '@'  N").
Notation "'{{{' ∀∀ x ',' P '}}}' body '{{{' 'RET' ret ',' Q '}}}' '@' N" :=
  (atomic_fun N (λ x, P) (λ x, body) (λ x _ ret, Q))%I
  (at level 20, N, P, body, Q at level 200, x binder, ret binder,
   format "'{{{'  ∀∀  x ,  '/' P '}}}'  '/' body  '/' '{{{'  'RET'  ret ,  '/' Q  '}}}' '@'  N").
Notation "'{{{' ∀∀ x ',' P '}}}' body '{{{' ∀∀ x2 ',' Q '}}}' '@' N" :=
  (atomic_fun N (λ x, P) (λ x, body) (λ x x2 _, Q))%I
  (at level 20, N, P, body, Q at level 200, x binder, x2 binder,
   format "'{{{'  ∀∀  x ,  '/' P '}}}'  '/' body  '/' '{{{'  ∀∀  x2 ,  '/' Q  '}}}' '@'  N").
Notation "'{{{' ∀∀ x ',' P '}}}' body '{{{' Q '}}}' '@' N" :=
  (atomic_fun N (λ x, P) (λ x, body) (λ x _ _, Q))%I
  (at level 20, N, P, body, Q at level 200, x binder,
   format "'{{{'  ∀∀  x ,  '/' P '}}}'  '/' body  '/' '{{{'  Q  '}}}' '@'  N").
Notation "'{{{' P '}}}' body '{{{' ∀∀ x2 ',' Q '}}}' '@' N" :=
  (atomic_fun N (λ _, P) (λ _, body) (λ _ x2 _, Q))%I
  (at level 20, N, P, body, Q at level 200, x2 binder,
   format "'{{{' P '}}}'  '/' body  '/' '{{{'  ∀∀  x2 ,  '/' Q  '}}}' '@'  N").
Notation "'{{{' P '}}}' body '{{{' 'RET' ret ',' Q '}}}' '@' N" :=
  (atomic_fun N (λ _, P) (λ _, body) (λ _ _ ret, Q) )%I
  (at level 20, N, P, body, Q at level 200, ret binder,
   format "'{{{' P '}}}'  '/' body  '/' '{{{'  'RET'  ret ,  '/' Q  '}}}' '@'  N").
Notation "'{{{' P '}}}' body '{{{' Q '}}}' '@' N" :=
  (atomic_fun N (λ _, P) (λ _, body) (λ _ _ _, Q) )%I
  (at level 20, N, P, body, Q at level 200,
   format "'{{{' P '}}}'  '/' body  '/' '{{{'  Q  '}}}' '@'  N").

(* core atomic update point, which has the 'abort' facility as in Iris *)
Definition atomic_try `{Σ : GRA} {X : Type}
    (αP : X → iProp Σ)
    (αQ : X → Any.t → iProp Σ)
    : itree crisE (() + Any.t * X) :=
  x2 <- trigger (Take X);;
  trigger (Assume (αP x2));;; (* public precondition *)
  ret <- trigger (Choose (() + Any.t));;
  match ret with
  | inl _ =>
    trigger (Guarantee (αP x2));;; Ret (inl tt) (* public precondition - abort *)
  | inr ret =>
    trigger (Guarantee (αQ x2 ret));;; Ret (inr (ret, x2)) (* public postcondition *)
  end.

Definition atomic_update_sem `{Σ : GRA} {X2 : Type}
    (αP : X2 → iProp Σ)
    (αQ : X2 → Any.t → iProp Σ)
    : itree crisE (Any.t * X2) :=
  yield_iter (λ _, atomic_try αP αQ) tt.

Notation "'<<{' ∀∀ x , αP , ∃∃ ret , αQ '}>>'" :=
  (atomic_update_sem (λ x, αP) (λ x ret, αQ))
  (at level 20, αP, αQ at level 200, x binder, ret binder).
Notation "'<<{' ∀∀ x , αP , αQ '}>>'" :=
  (atomic_update_sem (λ x, αP) (λ x _, αQ))
  (at level 20, αP, αQ at level 200, x binder).
Notation "'<<{' αP , ∃∃ ret , αQ '}>>'" :=
  (atomic_update_sem (λ _, αP) (λ _ ret, αQ))
  (at level 20, αP, αQ at level 200, ret binder).
Notation "'<<{' αP , αQ '}>>'" :=
  (atomic_update_sem (λ _, αP) (λ _ _, αQ))
  (at level 20, αP, αQ at level 200).

Lemma unfold_atomic_update_sem `{Σ : GRA} {X2 : Type}
    (αP : X2 → iProp Σ)
    (αQ : X2 → Any.t → iProp Σ) :
  atomic_update_sem αP αQ =
    𝒴;;;
    x2 <- trigger (Take X2);;
    trigger (Assume (αP x2));;;
    ret <- trigger (Choose (() + Any.t));;
    match ret with
    | inl _ => trigger (Guarantee (αP x2));;; tau;; atomic_update_sem αP αQ
    | inr ret => trigger (Guarantee (αQ x2 ret));;; 𝒴;;; Ret (ret, x2)
    end.
Proof.
  rewrite {1}/atomic_update_sem unfold_yield_iter /atomic_try; grind. case_match; grind.
Qed.

Lemma atomic_fun_src `{!crisG Γ Σ α β τ Hinv Hsub, !schGS} {X X2 : Type}
    (P : X → iProp Σ)
    (body : _ → itree crisE (Any.t * X2)) (Q : X → X2 → Any.t → iProp Σ) (N : namespace)
    (fls flt : gmap fname (option fbody))
    (Ist : ist_type Σ)
    (E1 E2 : coPset)
    r g R_t RR ps pt
    sts (msk_s : emask) (sp_s : specmap)
    stt itt :
  (∀ mtid stid x,
    Tid mtid stid -∗
    P x -∗
    wsim fls flt Ist (E1 ∪ ↑N, E2 ∪ ↑N) r g _ R_t
      (λ '(sts, rets) '(stt, rett),
        o=> winv (E1 ∪ ↑N, E2 ∪ ↑N) ∗ Tid mtid stid ∗ Q x rets.2 rets.1 ∗ RR (sts, rets.1) (stt, rett))
      true pt
      (sts, ⇓sbox(msk_s) (⇓smod(sp_s) (body x))) (stt, itt)) -∗
  wsim fls flt Ist (E1, E2) r g Any.t R_t RR ps pt
    (sts, ⇓sbox(msk_s) (⇓smod(sp_s) ({{{ ∀∀ x, P x }}} body x {{{ ∀∀ x2, RET ret, Q x x2 ret }}} @ N)))
    (stt, itt).
Proof.
  iIntros "SIM".
  rewrite /atomic_fun.
  cStepS. case_match; cStepsS; ss. case_match; cStepsS; ss. destruct p as [mtid stid].
  cStepsS; case_match; cStepsS; ss. iDestruct "ASM" as "[TID P]".
  iPoseProof ("SIM" with "TID P") as "SIM".
  appendRetT. cBind _ "SIM" as (st_src [ret_s x2_s] st_tgt ret_t) ">[W [TID [Q RR]]]".
  cStepS; case_match; cStepsS; ss. iApply wsim_fold; iFrame. cForceS. iFrame.
  cStep; iFrame.
Qed.

Lemma atomic_fun_tgt `{!crisG Γ Σ α β τ Hinv Hsub, !schGS} {X X2 : Type}
    (mtid stid : nat)
    (P : X → iProp Σ)
    (body : X → itree crisE (Any.t * X2))
    (Q : X → X2 → Any.t → iProp Σ)
    (N : namespace)
    (fls flt : gmap fname (option fbody))
    (Ist : ist_type Σ)
    (E_s : coPset)
    r g R_s R_t RR ps pt
    sts (its : itree crisE R_s)
    (msk_t : emask) (sp_t : specmap) stt ktr_t :
  (∀ X, msk_t _ (subevent _ (Take X))) →
  (∀ P, msk_t _ (subevent _ (Assume P))) →
  ↑N ⊆ E_s →
  Tid mtid stid -∗
  (∃ x_t, P x_t ∗
    wsim fls flt Ist (E_s ∖ ↑N, E_s ∖ ↑N) r g R_s _ RR ps true
      (sts, its)
      (stt, '(ret_t, x2_t) : _ <- ⇓sbox(msk_t) (⇓smod(sp_t) (body x_t));;
        trigger (Guarantee (winv (↑N, ↑N) ∗ Tid mtid stid ∗ Q x_t x2_t ret_t));;;
        ktr_t ret_t)) -∗
  wsim fls flt Ist (E_s, E_s) r g R_s R_t RR ps pt
    (sts, its)
    (stt,
      ⇓sbox(msk_t) (⇓smod(sp_t) (({{{ ∀∀ x, P x }}} body x {{{ ∀∀ x2, RET ret, Q x x2 ret }}} @ N))) >>=
      ktr_t).
Proof.
  iIntros (Ht Ha ?) "TID [%x_t [P Sim]]".
  rewrite /atomic_fun.
  cStepT. rewrite Ht /=. cForceT ((mtid, stid), x_t). cStepsT.
  rewrite Ha. cStepsT. cForceT; iFrame "TID P".
  cStepsT. cShowT. replace_t; [|iFrame].
  symmetry; etrans; first hnorm_itr; grind.
  symmetry; etrans; first hnorm_itr; grind. rewrite orb_true_r.
  etrans; first hnorm_itr; grind. hnorm_itr.
Qed.

Lemma atomic_update_sem_tgt `{!crisG Γ Σ α β τ Hinv Hsub, !schGS} {X X2 : Type}
    (P : X → iProp Σ)
    (αP : X → X2 → iProp Σ)
    (αQ : X → X2 → Any.t → iProp Σ)
    (Q : X → X2 → Any.t → iProp Σ)
    (N : namespace)
    (x_t : X)
    (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ)
    (ps pt : bool) st_src st_tgt
    (E : coPset) (mtid stid : nat)
    r g {R_s R_t} RR
    (ktr_s : _ → itree crisE R_s) (ktr_t : _ → itree crisE R_t)
    (msk_s msk_t : emask)
    (sp_s sp_t : specmap) :
  sp_s.1 !! fid SchHdr.yield = fsp_some (SchA.yield_spec E) →
  sp_t.1 !! fid SchHdr.yield = fsp_some (SchA.yield_spec (↑N)) →
  img_msk msk_t →
  (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
  ↑N ⊆ E →
  Ist st_src st_tgt -∗
  Tid mtid stid -∗
  P x_t -∗
  (∃ n,
    AU <{ ∃∃ (x2_t : X2), αP x_t x2_t }>
      @ n, E ∖ ↑N, E ∖ ↑N, ∅
      <{ ∀∀ ret, αQ x_t x2_t ret,
        COMM ∀ st_src st_tgt,
          Ist st_src st_tgt -∗ Tid mtid stid -∗
          Q x_t x2_t ret -∗
          wsim fl_s fl_t Ist (E, E) r g R_s R_t RR true true
            (st_src, ⇓sbox(msk_s) (⇓smod(sp_s) 𝒴) >>= ktr_s)
            (st_tgt, ktr_t ret) }>)%I -∗
  wsim fl_s fl_t Ist (E, E) r g R_s R_t RR ps pt
    (st_src, ⇓sbox(msk_s) (⇓smod(sp_s) 𝒴) >>= ktr_s)
    (st_tgt, ⇓sbox(msk_t) (⇓smod(sp_t) ((
      {{{ ∀∀ x, P x }}}
        <<{ ∀∀ x2, αP x x2, ∃∃ ret, αQ x x2 ret }>>
      {{{ ∀∀ x2, RET ret, Q x x2 ret }}} @ N))) >>= ktr_t).
Proof using.
  iIntros (? ? [Ht [Hc [Ha [? ?]]]] ? ?) "IST TID Pre [%n AU]".
  iApply (atomic_fun_tgt with "TID"); ss; iFrame "Pre".
  iApply wsim_reset. cCoind CIH g2 Hg2 with st_src st_tgt. iIntros "[IST AU]".
  rewrite /atomic_update_sem unfold_yield_iter.
  sYieldII "IST". rewrite /atomic_try. cStepsT. rewrite Ht /=.
  iMod ("AU") as "AU"; iMod ("AU" $! tt with "[$]") as "[%x2_t [Pre AU]]".
  cForceT x2_t. cStepsT. rewrite Ha /=.
  cForceT; iFrame "Pre". cStepsT. rewrite orb_true_r. cStepsT. case_match.
  { cStepT. rewrite orb_true_r. cStepsT. iMod ("AU" with "GRT") as "[_ AU]". cByCoind CIH. iFrame. }
  cStepsT. rewrite orb_true_r. cStepsT. iMod ("AU" with "GRT") as "[% [_ > AU]]".
  sYieldII "IST". cStepsT. iDestruct "GRT" as "[TID Q]". iApply wsim_mono_knowledge; last first.
  { iApply ("AU" with "[$] [$] [$]"). }
  { iIntros (???????) "?"; iApply Hg2; done. }
  { auto. }
Qed.

Lemma atomic_update_sem_both `{!crisG Γ Σ α β τ Hinv Hsub, !schGS} {X_s X X2 : Type}
    (αP_s : X_s → iProp Σ)
    (αQ_s : X_s → Any.t → iProp Σ)
    (P : X → iProp Σ)
    (αP : X → X2 → iProp Σ)
    (αQ : X → X2 → Any.t → iProp Σ)
    (Q : X → X2 → Any.t → iProp Σ)
    (N : namespace)
    (x_t : X)
    (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ)
    (ps pt : bool) st_src st_tgt
    (E : coPset) (mtid stid : nat)
    r g {R_s R_t} RR
    (ktr_s : _ → itree crisE R_s)
    (ktr_t : _ → itree crisE R_t)
    (msk_s msk_t : emask)
    (sp_s sp_t : specmap) :
  sp_s.1 !! fid SchHdr.yield = fsp_some (SchA.yield_spec E) →
  sp_t.1 !! fid SchHdr.yield = fsp_some (SchA.yield_spec (↑N)) →
  img_msk msk_t →
  (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
  ↑N ⊆ E →
  Ist st_src st_tgt -∗
  Tid mtid stid -∗
  P x_t -∗
  (∃ n,
    AU <{ ∀∀ x_s, αP_s x_s, ∃∃ (x2_t : X2), αP x_t x2_t }>
      @ n, E ∖ ↑N, E ∖ ↑N, ∅
      <{ ∀∀ ret, αQ x_t x2_t ret,
        ∃∃ ret_s, αQ_s x_s ret_s,
        COMM ∀ st_src st_tgt,
          Ist st_src st_tgt -∗ Tid mtid stid -∗
          Q x_t x2_t ret -∗
          wsim fl_s fl_t Ist (E, E) r g R_s R_t RR true true
            (st_src, ⇓sbox(msk_s) (⇓smod(sp_s) 𝒴);;; ktr_s (ret_s, x_s))
            (st_tgt, ktr_t ret) }>)%I -∗
  wsim fl_s fl_t Ist (E, E) r g R_s R_t RR ps pt
    (st_src, ⇓sbox(msk_s) (⇓smod(sp_s) (<<{ ∀∀ x2, αP_s x2, ∃∃ ret, αQ_s x2 ret }>>)) >>= ktr_s)
    (st_tgt, ⇓sbox(msk_t) (⇓smod(sp_t)
      ({{{ ∀∀ x, P x }}} <<{ ∀∀ x2, αP x x2, ∃∃ ret, αQ x x2 ret }>>
      {{{ ∀∀ x2, RET ret, Q x x2 ret }}} @ N)) >>= ktr_t).
Proof using.
  iIntros (? ? [Ht [Hc [Ha [? ?]]]] ? ?) "IST TID Pre [%n AU]".
  iApply (atomic_fun_tgt with "TID"); auto; iFrame "Pre".
  iApply wsim_reset. cCoind CIH g2 Hg2 with st_src st_tgt. iIntros "[IST AU]".
  rewrite /atomic_update_sem unfold_yield_iter. replace_t; [rewrite unfold_yield_iter //|].
  sYieldII "IST". sYieldS. rewrite /atomic_try.
  cStepS. case_match; cStepsS; ss.
  cStepS. case_match; cStepsS; ss.
  iMod ("AU") as "AU"; iMod ("AU" with "[$]") as "[%x2_t [Pre AU]]".
  cStepsT. rewrite Ht /=. cForceT x2_t. cStepsT. rewrite Ha /=. cForceT; iFrame "Pre".
  cStepsT. rewrite ?orb_true_r. cStepsT. case_match.
  { cStepT. rewrite orb_true_r. cStepsT. iMod ("AU" with "GRT") as "[Post AU]".
    cForceS (inl tt); cStepsS. case_match; cStepsS; ss. cForceS; iFrame. cStepsS.
    cByCoind CIH. iFrame.
  }
  cStepsT. rewrite orb_true_r. cStepsT. iMod ("AU" with "GRT") as "[%ret_s [Post > AU]]".
  cForceS (inr ret_s). cStepsS. case_match; cStepsS; ss. cForceS; iFrame; cStepsS.
  sYieldII "IST". cStepsT. iDestruct "GRT" as "[TID Q]". iApply wsim_mono_knowledge; last first.
  { cShowS. eapply eq_ind; first iApply ("AU" with "[$] [$] [$]"). repeat f_equal.
    extensionalities; symmetry; etransitivity; first hnorm_itr; reflexivity.
  }
  { iIntros (???????) "?"; iApply Hg2; done. }
  { auto. }
Qed.

Lemma atomic_update_sem_both2 `{!crisG Γ Σ α β τ Hinv Hsub, !schGS} {X_s X_t : Type}
    (αP_s : X_s → iProp Σ)
    (αQ_s : X_s → Any.t → iProp Σ)
    (αP : X_t → iProp Σ)
    (αQ : X_t → Any.t → iProp Σ)
    (N : namespace)
    (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ)
    (ps pt : bool) st_src st_tgt
    (E E_s : coPset)
    r g {R_s R_t} RR
    (ktr_s : _ → itree crisE R_s)
    (ktr_t : _ → itree crisE R_t)
    (msk_s msk_t : emask)
    (sp_s sp_t : specmap) :
  sp_s.1 !! fid SchHdr.yield = fsp_some (SchA.yield_spec E_s) →
  sp_t.1 !! fid SchHdr.yield = fsp_some (SchA.yield_spec (↑N)) →
  img_msk msk_t →
  (msk_t _ (subevent _ (Call SchHdr.yield.1 ()↑))) →
  ↑N ⊆ E_s →
  E = E_s ∖ ↑N →
  Ist st_src st_tgt -∗
  (∃ n,
    AU <{ ∀∀ x_s, αP_s x_s, ∃∃ (x2_t : X_t), αP x2_t }>
      @ n, E, E, ∅
      <{ ∀∀ ret, αQ x2_t ret,
        ∃∃ ret_s, αQ_s x_s ret_s,
        COMM ∀ st_src st_tgt,
          Ist st_src st_tgt -∗
          wsim fl_s fl_t Ist (E, E) r g R_s R_t RR true true
            (st_src, ⇓sbox(msk_s) (⇓smod(sp_s) 𝒴);;; ktr_s (ret_s, x_s))
            (st_tgt, ktr_t (ret, x2_t)) }>)%I -∗
  wsim fl_s fl_t Ist (E, E) r g R_s R_t RR ps pt
    (st_src, ⇓sbox(msk_s) (⇓smod(sp_s) (<<{ ∀∀ x2, αP_s x2, ∃∃ ret, αQ_s x2 ret }>>)) >>= ktr_s)
    (st_tgt, ⇓sbox(msk_t) (⇓smod(sp_t)
      (<<{ ∀∀ x2, αP x2, ∃∃ ret, αQ x2 ret }>>)) >>= ktr_t).
Proof using.
  iIntros (? ? [Ht [Hc [Ha [? ?]]]] ? ? ?) "IST [%n AU]".
  iApply wsim_reset. cCoind CIH g2 Hg2 with st_src st_tgt. iIntros "[IST AU]".
  rewrite /atomic_update_sem unfold_yield_iter. replace_t; [rewrite unfold_yield_iter //|].
  cStepS. cStepT. sYieldII "IST". sYieldS. rewrite /atomic_try.
  cStepS. case_match; cStepsS; ss.
  cStepS. case_match; cStepsS; ss.
  iMod ("AU") as "AU"; iMod ("AU" with "[$]") as "[%x2_t [Pre AU]]".
  cStepsT. rewrite Ht /=. cForceT x2_t. cStepsT. rewrite Ha /=. cForceT; iFrame "Pre".
  cStepsT. rewrite ?orb_true_r. cStepsT. case_match.
  { cStepT. rewrite orb_true_r. cStepsT. iMod ("AU" with "GRT") as "[Post AU]".
    cForceS (inl tt); cStepsS. case_match; cStepsS; ss. cForceS; iFrame. cStepsS.
    cByCoind CIH. iFrame.
  }
  clear dependent CIH. cStepsT. rewrite orb_true_r. cStepsT.
  iMod ("AU" with "GRT") as "[%ret_s [Post > AU]]".
  cForceS (inr ret_s). cStepsS. case_match; cStepsS; ss. cForceS; iFrame; cStepsS.
  sYieldII "IST". iApply wsim_mono_knowledge; last first.
  { cShowS. eapply eq_ind; first iApply ("AU" with "[$]"). repeat f_equal.
    extensionalities; symmetry; etransitivity; first hnorm_itr; reflexivity.
  }
  { iIntros (???????) "?"; iApply Hg2; done. }
  { auto. }
Qed.

Lemma yield_iter_prepend_yield_src
    `{!crisG Γ Σ α β τ Hinv Hsub, !schGS}
    {I R : Type} (body : I → itree _ (I + R)) (arg : I)
    (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ)
    (ps pt : bool) st_src st_tgt
    (Es : coPset) r g
    {R_t} RR
    (msk_s : emask)
    (sp_s : specmap)
    (itr_t : itree crisE R_t) :
  wsim fl_s fl_t Ist (Es, Es) r g _ R_t RR ps pt
    (st_src, ⇓sbox(msk_s) (⇓smod(sp_s) Sch.yield);;;
      ⇓sbox(msk_s) (⇓smod(sp_s) (yield_iter body arg)))
    (st_tgt, itr_t) ⊢
  wsim fl_s fl_t Ist (Es, Es) r g _ R_t RR ps pt
    (st_src, ⇓sbox(msk_s) (⇓smod(sp_s) (yield_iter body arg)))
    (st_tgt, itr_t).
Proof using.
  iIntros "SIM". rewrite unfold_yield_iter. cNormS. iApply wsim_yy_y.
  eapply eq_ind; first iApply "SIM".
  repeat f_equal; extensionalities; etrans; first hnorm_itr; auto.
Qed.

Lemma atomic_update_sem_prepend_yield_src
    `{!crisG Γ Σ α β τ Hinv Hsub, !schGS} {X2 : Type}
    (αP : X2 → iProp Σ)
    (αQ : X2 → Any.t → iProp Σ)
    (fl_s fl_t : gmap fname (option (Any.t → itree crisE Any.t)))
    (Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ)
    (ps pt : bool) st_src st_tgt
    (Es : coPset) r g
    {R_t} RR
    (msk_s : emask)
    (sp_s : specmap)
    (itr_t : itree crisE R_t) :
  wsim fl_s fl_t Ist (Es, Es) r g _ R_t RR ps pt
    (st_src, ⇓sbox(msk_s) (⇓smod(sp_s) Sch.yield);;;
      ⇓sbox(msk_s) (⇓smod(sp_s) (atomic_update_sem αP αQ)))
    (st_tgt, itr_t) ⊢
  wsim fl_s fl_t Ist (Es, Es) r g _ R_t RR ps pt
    (st_src, ⇓sbox(msk_s) (⇓smod(sp_s) (atomic_update_sem αP αQ)))
    (st_tgt, itr_t).
Proof using.
  iIntros "SIM". rewrite /atomic_update_sem. iApply yield_iter_prepend_yield_src. auto.
Qed.

Ltac aStep :=
  match goal with
  | |- environments.envs_entails _
      (wsim _ _ _ _ _ _ _ _ _ _ _
        (_, ITree.bind (SB.sandbox ?msk (SModTr.trans ?sp (atomic_update_sem ?αP ?αQ))) ?ktr)
        (_, ITree.bind (SB.sandbox ?msk_t (SModTr.trans ?sp_t (atomic_update_sem ?αP_t ?αQ_t))) ?ktr_t)) =>
    iApply (atomic_update_sem_both2 αP αQ αP_t αQ_t with "IST");
      [ simpl_map; simpl_sp; ss | simpl_map; simpl_sp; ss
      | ss | ss | try (solve_ndisj || set_solver) | try (solve_ndisj || set_solver) | ]
  end.

Ltac aStepS :=
  match goal with
  | |- environments.envs_entails _
      (wsim _ _ _ _ _ _ _ _ _ _ _
        (_, (SB.sandbox ?msk (SModTr.trans ?sp (atomic_fun ?N ?P ?body ?Q)))) (_, _)) =>
    iApply (atomic_fun_src P body Q N); simpl_set
  end.

Tactic Notation "aForceT" "with" constr(H1) :=
  match goal with
  | |- environments.envs_entails _ 
      (wsim _ _ _ _ _ _ _ _ _ _ _
        (_, _)
        (_, SB.sandbox ?msk (SModTr.trans ?sp (atomic_fun ?N ?P ?body ?Q)))) =>
    appendRetT; iApply (atomic_fun_tgt with H1); [solve_msk|solve_msk|try solve_ndisj|..|simpl_set]
  | |- environments.envs_entails _ 
      (wsim _ _ _ _ _ _ _ _ _ _ _
        (_, _)
        (_, ITree.bind (SB.sandbox ?msk (SModTr.trans ?sp (atomic_fun ?N ?P ?body ?Q))) _)) =>
    iApply (atomic_fun_tgt with H1); [solve_msk|solve_msk|try solve_ndisj|..|simpl_set]
  | |- environments.envs_entails _ 
    (wsim _ _ _ _ _ _ _ _ _ _ _
      (_, ITree.bind (SB.sandbox _ (SModTr.trans _ Sch.yield)) _)
      (_, ITree.bind (SB.sandbox ?msk (SModTr.trans ?sp (atomic_fun ?N ?P (λ x, atomic_update_sem ?αP ?αQ) ?Q))) _)) =>
    iApply (atomic_update_sem_tgt with H1);
      [simpl_map; simpl_sp; ss|simpl_map; simpl_sp; ss|ss|ss|try solve_ndisj|auto|]
  end.

Ltac aUnfoldS :=
  replace_s; [
    match goal with
    | |- context[iterC ?body ?arg] => 
      rewrite (unfold_iterC body arg) //
    | |- context[yield_iter ?body ?arg] =>
      rewrite (unfold_yield_iter body arg) //
    | |- context[ITree.iter ?body ?arg] =>
      rewrite (unfold_iter_eq body arg) //
    | |- context[atomic_update_sem ?αP ?αQ] =>
      rewrite (unfold_atomic_update_sem αP αQ) //
    end
  | ].

Ltac aUnfoldT :=
  replace_t; [
    match goal with
    | |- context[iterC ?body ?arg] => 
      rewrite (unfold_iterC body arg) //
    | |- context[yield_iter ?body ?arg] =>
      rewrite (unfold_yield_iter body arg) //
    | |- context[ITree.iter ?body ?arg] =>
      rewrite (unfold_iter_eq body arg) //
    | |- context[atomic_update_sem ?αP ?αQ] =>
      rewrite (unfold_atomic_update_sem αP αQ) //
    end
  | ].

Ltac aAddY :=
  match goal with
  | |- environments.envs_entails _
      (wsim _ _ _ _ _ _ _ _ _ _ _
        (_, ITree.bind (SB.sandbox ?msk (SModTr.trans ?sp Sch.yield)) _) (_, _)) =>
    iApply wsim_yy_y
  | |- environments.envs_entails _
      (wsim _ _ _ _ _ _ _ _ _ _ _
        (_, (SB.sandbox ?msk (SModTr.trans ?sp (atomic_update_sem ?αP ?αQ)))) (_, _)) =>
    iApply (atomic_update_sem_prepend_yield_src αP αQ)
  end.
