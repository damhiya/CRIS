Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics.
Require Import MInline MInlineIntro MInlineElim ElimRel.

Lemma cancel_post `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG} md sp:
  ∀ (rs0 : Σ) r_s r_t srcs tgts cid st ps pt vret (X X': Type) (x: X) (x': X') Q Q' itrS ktrT k rs_diff
    (r : ∀ x x0, (x→x0→Prop)→smj→smj→itree coreE x→itree coreE x0→Prop)
    (WFS: SMod.cancellable md)
    (* (WF: Mod.wf (SMod.to_mod sp_none (SMod.cancel md))) *)
    (KEY: ∀ itr_s itr_t st (r_s r_t r_diff : Σ)
             (WFR: ✓ r_s)
             (RS: Own r_s ⊢ |==> ([∗ list] i ∈ <[cid:=r_diff]> rs_diff, Own i) ∗ Own r_t ∗
                      TIDAUTH cid ∗ YIELDAUTH (length (<[cid:=r_diff]> rs_diff)))
             (LEN: cid < List.length srcs)
             (REL: thread_rel sp cid cid r_diff itr_s itr_t),
     gpaco7 _gsim (cpn7 _gsim) bot7 r (Any.t * Any.t)%type
       (Any.t * Any.t)%type cancel_eq smj_top smj_top
       (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                 (SMod.to_mod sp_none (SMod.cancel md))) rs0)))
                 (cid, <[cid:=itr_s]> srcs))
          (Any.pair (ModTr.alist_encode st) r_s ↑))
       (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                 (SMod.to_mod sp md)) rs0)))
                 (cid, <[cid:=itr_t]> tgts))
          (Any.pair (ModTr.alist_encode st) r_t ↑)))
    (EQLEN2 : length rs_diff = length srcs)
    (EQLEN : length srcs = length tgts)
    (REL : ∀ i x y z, rs_diff !! i = Some z →
      srcs !! i = Some x → tgts !! i = Some y → thread_rel sp cid i z x y)
    (WFR : ✓ r_s)
    (RS : Own r_s ⊢ |==> ([∗ list] i ∈ rs_diff, Own i) ∗ Own r_t ∗
              TIDAUTH cid ∗ YIELDAUTH (length rs_diff))
    (LEN : cid < length srcs)
    (x2 : rs_diff !! cid = Some ε)
    (x0 : srcs !! cid = Some (ModTr.trans (tau;; tau;; itrS)))
    (x1 : tgts !! cid = Some (x <- ModTr.trans (x <- elim_postcond Q Q' x x' vret;; ktrT x);; k x))
    (RET : cid = 0 → k = main_post)
    (KTR :
      (∀ ret : Any.t, Q' x' vret ret ⊢ |==> Q x vret ret)
      ∧ upaco4 (elim_rel_def sp) bot4 Any.t ε itrS (ktrT vret)),

  gpaco7 _gsim (cpn7 _gsim) bot7 r (Any.t * Any.t)%type 
    (Any.t * Any.t)%type cancel_eq ps pt
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
              (SMod.to_mod sp_none (SMod.cancel md))) rs0))) (cid, srcs))
       (Any.pair (ModTr.alist_encode st) r_s ↑))
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
              (SMod.to_mod sp md)) rs0))) (cid, tgts))
       (Any.pair (ModTr.alist_encode st) r_t ↑)).
Proof.
  i. ziter_l. ziter_r. rewrite x0 x1 /=.
  zstep_l. ziter_l. zstep_l.
  move KTR at bottom. des_safe.
  destruct KTR0; subst; des_safe.
  { zstep_r. zstep_r.
    ziter_r. zstep_r. ziter_r. zstep_r.
    ziter_r. zstep_r. zstep_r. ziter_r. zstep_r. zstep_r.
    ziter_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r.
    ziter_r. zstep_r. ziter_r. zstep_r.

    des; subst.
    { ziter_r. zstep_r. eexists. zstep_r.
      ziter_r. zstep_r. ziter_r. zstep_r.
      ziter_r. zstep_r. eexists r_t. zstep_r.
      ziter_r. zstep_r. unshelve eexists.
      { split; [eapply Own_wand_valid; [iIntros "S"; iMod (RS with "S") as "[_ [$ [_ _]]]"|]|]; try done.
        iIntros "H". iMod (x6 with "H") as "[P O]". rewrite KTR. iFrame. 
      }
      zstep_r.
      ziter_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r.

      pclearbot. eapply KEY; et.
      { rewrite list_insert_id //. }
      { econs; eauto; eapply KTR1. }
    }
  }
(*SLOW*)Qed.
