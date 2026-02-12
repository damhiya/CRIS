Require Import Common ConcRA.
From iris.proofmode Require Import proofmode.
Require Import LMod Mod SMod Sp.
Require Import LSim LSimTactics MSim MSimFacts ISim TacticsCommon ITactics SimNotations ISimFacts WSim.

Set Implicit Arguments.

Section LAT.
  Context `{!crisG Γ Σ α β τ _S _I, !concGS}.

  (* Lemma wsim_lat_real_to_img peeking img fsp lbody_s lbody_t body_s body_t fl_s fl_t msk scp ps pt st arg
    (EQITL: eqit eq false true 
             (SB.sandbox true msk scp (SModTr.trans img sp_none lbody_s))
             (SB.sandbox false msk scp (SModTr.trans img sp_none lbody_t)))
    (EQIT: eqit eq false true 
             (SB.sandbox true msk scp (SModTr.trans img sp_none (body_s arg)))
             (SB.sandbox false msk scp (SModTr.trans img sp_none (body_t arg))))
    :
    ⊢
    wsim fl_s fl_t IstEq (∅,∅) ibot ibot _ _ (ist_with_eq IstEq) ps pt
      (st, SB.sandbox true msk scp (SModTr.trans img sp_none (lat_img peeking fsp lbody_s body_s arg)))
      (st, SB.sandbox false msk scp (SModTr.trans img sp_none (lat_real peeking fsp lbody_t body_t arg))).
  Proof using. iIntros. iApply isim_wsim. iIntros "W". iApply isim_lat_real_to_img; et. Qed.

  Lemma wsim_lat_img_to_hoare img fsp body_s body_t fl_s fl_t msk scp ps pt st arg
    (EQIT: eqit eq false true
            (SB.sandbox true msk scp (body_s arg))
            (SB.sandbox true msk scp (SModTr.trans img sp_none (body_t arg))))
    :
    ⊢
    wsim fl_s fl_t IstEq (∅,∅) ibot ibot _ _ (ist_with_eq IstEq) ps pt
      (st, SB.sandbox true msk scp (SModTr.HoareFun (Some (to_fspec fsp)) body_s arg))
      (st, SB.sandbox true msk scp (SModTr.trans img sp_none (lat_img false fsp (Ret ()) body_t arg))).
  Proof using. iIntros. iApply isim_wsim. iIntros "W". iApply isim_lat_img_to_hoare; et. Qed.

  Lemma wsim_lat_real_to_hoare img fsp body_s body_t fl_s fl_t msk scp ps pt st arg
    (EQIT: eqit eq false true
            (SB.sandbox true msk scp (body_s arg))
            (SB.sandbox false msk scp (SModTr.trans img sp_none (body_t arg))))
    :
    ⊢
    wsim fl_s fl_t IstEq (∅,∅) ibot ibot _ _ (ist_with_eq IstEq) ps pt
      (st, SB.sandbox true msk scp (SModTr.HoareFun (Some (to_fspec fsp)) body_s arg))
      (st, SB.sandbox false msk scp (SModTr.trans img sp_none (lat_real false fsp (Ret ()) body_t arg))).
  Proof using. iIntros. iApply isim_wsim. iIntros "W". iApply isim_lat_real_to_hoare; et. Qed. *)
End LAT.
