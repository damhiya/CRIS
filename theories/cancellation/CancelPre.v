Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics.
Require Import MInline MInlineIntro MInlineElim ElimRel.

Lemma cancel_pre `{Σ : GRA} md sp:
  ∀ (rs0 : Σ) r_s r_t rs_diff srcs tgts cid st ps pt varg fspo fspo' itrS ktrT k
    (r: ∀ x x0, (x→x0→Prop)→smj→smj→itree coreE x→itree coreE x0→Prop)
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
    (REL : ∀ i z x y, rs_diff !! i = Some z →
      srcs !! i = Some x → tgts !! i = Some y → thread_rel sp i z x y)
    (WFR : ✓ r_s)
    (RS : Own r_s ⊢ |==> ([∗ list] i ∈ rs_diff, Own i) ∗ Own r_t)
    (LEN : cid < length srcs)
    (x2 : rs_diff !! cid = Some ε)
    (x0 : srcs !! cid = Some (ModTr.trans (tau;; tau;; tau;; itrS)))
    (x1 : tgts !! cid = Some (x <- ModTr.trans (x <- elim_precond fspo fspo' varg;; ktrT x);; k x))
    (RET : cid = 0 → k = λ x : Any.t, Ret x)
    (KTR :∀ P Q (VS: fspec_flat fspo P Q), ∃ P' Q', fspec_flat fspo' P' Q' ∧
            (∀ arg : Any.t, P varg arg ⊢ |==> P' varg arg)
            ∧ upaco4 (elim_rel_def sp) bot4 Any.t ε (itrS) (ktrT (if fspo then Some Q else None, if fspo' then Some Q' else None, varg))),

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
  i. ziter_l. ziter_r. rewrite x0 x1. s. zstep_l.
  move KTR at bottom.
  destruct fspo as [fsp|]; des; subst.
  { zstep_r. zstep_r.
    ziter_r. zstep_r. ziter_r. zstep_r. zstep_r.
    ziter_r. zstep_r. ziter_r. zstep_r.
    ziter_r. zstep_r. zstep_r.
    ziter_r. zstep_r. zstep_r.
    ziter_r. zstep_r. ziter_r. zstep_r.
    ziter_r. zstep_r. ziter_r. zstep_r.
    destruct x. des. ss. specialize (KTR _ _ related). des. destruct fspo' as [fsp'|].
    { ziter_r. zstep_r. exists (mk_FSpec _ _ _ KTR). zstep_r.
      ziter_r. zstep_r. ziter_r. zstep_r. eexists. zstep_r.
      ziter_r. zstep_r. ziter_r. zstep_r.
      ziter_r. zstep_r. eexists r_t. zstep_r.
      ziter_r. zstep_r. unshelve eexists.
      { split; [eapply Own_wand_valid; [iIntros "S"; iMod (RS with "S") as "[_ $]"|]|]; try done.
        iIntros "H". iMod (x6 with "H") as "[P O]". rewrite KTR0. iFrame. 
      }
      zstep_r. 
      ziter_r. zstep_r. ired.
      ziter_r. zstep_r. ziter_r. zstep_r.
      ziter_l. zstep_l. ziter_l. zstep_l.

      pclearbot. eapply KEY; et.
      { rewrite RS list_insert_id //. }
      (* { rewrite list_insert_id // RS. } *)
      { eapply thread_rel_body; eauto. }
    }
    { rr in KTR. des; subst.
      assert (varg = x3).
      { eapply Own_pure_soundness; try apply WFR.
        rewrite RS. iIntros ">[_ H]". iMod (x6 with "H") as "[P O]".
        rewrite KTR0. iMod "P" as "P"; et.
      }
      des. subst. ired.
      ziter_r. zstep_r. ziter_r. zstep_r.
      ziter_l. zstep_l. ziter_l. zstep_l.
      pclearbot. eapply KEY; et.
      { rewrite RS list_insert_id //. iIntros ">[$ H]". iMod (x6 with "H") as "[P O]". iFrame. et. }
      { econs; eauto. }
    }
  }
  { s. zstep_r. exploit KTR; [rr; esplits; et; exact ()|].
    clear KTR. i; des. destruct fspo' as [fsp'|]; ss.
    { ziter_r. zstep_r. exists (mk_FSpec _ _ _ x3). zstep_r.
      ziter_r. zstep_r. ziter_r. zstep_r. eexists. zstep_r.
      ziter_r. zstep_r. ziter_r. zstep_r.
      ziter_r. zstep_r. eexists r_t. zstep_r.
      ziter_r. zstep_r. unshelve eexists.
      { split; [eapply Own_wand_valid; [iIntros "S"; iMod (RS with "S") as "[_ $]"|]|]; try done.
        iIntros "H". iFrame. iApply x4. et.
      }
      zstep_r.
      ziter_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r.
      ziter_l. zstep_l. ziter_l. zstep_l.
      pclearbot. eapply KEY; et.
      { rewrite list_insert_id //. }
      { econs; eauto. }
    }
    { rr in x3. des; subst.
      ired. ziter_r. zstep_r. ziter_r. zstep_r.
      ziter_l. zstep_l. ziter_l. zstep_l.
      pclearbot. eapply KEY; et.
      { rewrite list_insert_id //. }
      { econs; eauto. }
    }
  }
  Unshelve. exact ().
(*SLOW*)Qed.
