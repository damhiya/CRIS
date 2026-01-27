Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics.
Require Import MInline MInlineIntro MInlineElim ElimRel.

Lemma cancel_post `{Σ: GRA} md sp:
  ∀ (rs0 : Σ) r_s r_t srcs tgts cid st ps pt vret Qo Qo' itrS ktrT k rs_diff
    (r : ∀ x x0, (x→x0→Prop)→smj→smj→itree coreE x→itree coreE x0→Prop)
    (WFS: SMod.wf md)
    (VP: valid_sp md sp)
    (WF: Mod.wf (SMod.to_mod sp_none (SMod.cancel md)))
    (KEY: ∀ itr_s itr_t st (r_s r_t r_diff : Σ) tid
             (WFR: ✓ r_s)
             (RS: Own r_s ⊢ |==> ([∗ list] i ∈ <[cid:=r_diff]> rs_diff, Own i) ∗ Own r_t)
             (LEN: cid < List.length srcs)
             (REL: thread_rel sp cid r_diff itr_s itr_t),
     gpaco7 _gsim (cpn7 _gsim) bot7 r (Any.t * Any.t)%type
       (Any.t * Any.t)%type cancel_eq smj_top smj_top
       (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                 (SMod.to_mod sp_none (SMod.cancel md))) rs0)))
                 (tid, <[cid:=itr_s]> srcs))
          (Any.pair (ModTr.alist_encode st) r_s ↑))
       (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                 (SMod.to_mod sp md)) rs0)))
                 (tid, <[cid:=itr_t]> tgts))
          (Any.pair (ModTr.alist_encode st) r_t ↑)))
    (EQLEN2 : length rs_diff = length srcs)
    (EQLEN : length srcs = length tgts)
    (REL : ∀ i x y z, rs_diff !! i = Some z →
      srcs !! i = Some x → tgts !! i = Some y → thread_rel sp i z x y)
    (WFR : ✓ r_s)
    (RS : Own r_s ⊢ |==> ([∗ list] i ∈ rs_diff, Own i) ∗ Own r_t)
    (LEN : cid < length srcs)
    (x2 : rs_diff !! cid = Some ε)
    (x0 : srcs !! cid = Some (ModTr.trans (tau;; tau;; itrS)))
    (x1 : tgts !! cid = Some (x <- ModTr.trans (x <- elim_postcond Qo Qo' vret;; ktrT x);; k x))
    (RET : cid = 0 → k = λ x : Any.t, Ret x)
    (KTR :
    ∃ Q : Any.t → Any.t → iProp Σ,
      (Qo = Some Q
       ∨ Qo = None ∧ Q = λ (varg arg : Any.t), ⌜varg = arg⌝%I)
      ∧ ∃ Q' : Any.t → Any.t → iProp Σ,
          (Qo' = Some Q'
           ∨ Qo' = None ∧ Q' = λ (varg arg : Any.t), ⌜varg = arg⌝%I)
          ∧ (∀ ret : Any.t, Q' vret ret ⊢ |==> Q vret ret)
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
  i. ziter_l. ziter_r. rewrite x0 x1 /=. zstep_l. ziter_l. zstep_l.
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
      { split; [eapply Own_wand_valid; [iIntros "S"; iMod (RS with "S") as "[_ $]"|]|]; try done.
        iIntros "H". iMod (x5 with "H") as "[P O]". rewrite KTR1. iFrame. 
      }
      zstep_r.
      ziter_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r.

      pclearbot. eapply KEY; et.
      { rewrite list_insert_id //. }
      { econs; eauto; eapply KTR1. }
    }
    { assert (vret = x).
      { eapply Own_pure_soundness; try apply WFR.
        rewrite RS. iIntros ">[? H]". iMod (x5 with "H") as "[P O]".
        rewrite KTR1. iMod "P" as "P"; et.
      }
      des. subst.
      ired. pclearbot. eapply KEY; et.
      rewrite RS list_insert_id //. iIntros ">[$ H]". iMod (x5 with "H") as "[P O]". iFrame. et.
      econs; eauto; eapply KTR1.
    }
  }
  {
    s. zstep_r.
    des; subst.      
    { ziter_r. zstep_r.
      ziter_r. zstep_r. eexists. zstep_r.
      ziter_r. zstep_r. ziter_r. zstep_r.
      ziter_r. zstep_r. eexists r_t. zstep_r.
      ziter_r. zstep_r. unshelve eexists.
      { split; [eapply Own_wand_valid; [iIntros "S"; iMod (RS with "S") as "[_ $]"|]|]; try done.
        iIntros "H". iFrame. iApply KTR1. et.
      }
      zstep_r.
      ziter_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r.

      pclearbot. eapply KEY; et.
      { rewrite list_insert_id //. }
      { econs; eauto; eapply KTR1. }
    }
    { ziter_r. zstep_r.
      pclearbot. eapply KEY; et.
      { rewrite list_insert_id //. }
      { econs; eauto; eapply KTR1. }
    }
  }
(*SLOW*)Qed.
