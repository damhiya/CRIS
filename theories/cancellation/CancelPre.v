Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import SModTr HModTr ModTr SMod HMod Mod.
Require Import ITactics TacticsCommon SimGlobal SimGlobalFacts CtxRefine ClosedAdequacy.
Require Import HModInline HModInlineIntro HModInlineElim ElimRel.
Require Import SimGlobal SimGTactics.

Lemma cancel_pre `{Σ : GRA} md sp:
  ∀ (rs0 : Σ) r_s r_t rs_diff srcs tgts cid st ps pt varg X X' Po Po' itrS ktrT k
    (r: ∀ x x0, (x→x0→Prop)→smj→smj→itree coreE x→itree coreE x0→Prop)
    (WFS: smod_wf md)
    (VP: valid_sp md sp)
    (WF: HMod.wf (SMod.to_hmod sp_none (SMod.cancel md)))
    (KEY: ∀ itr_s itr_t st (r_s r_t r_diff : Σ) tid
             (WFR: ✓ r_s)
             (RS: Own r_s ⊢ |==> ([∗ list] i ∈ <[cid:=r_diff]> rs_diff, Own i) ∗ Own r_t)
             (LEN: cid < List.length srcs)
             (REL: thread_rel sp cid r_diff itr_s itr_t),
     gpaco7 _simg (cpn7 _simg) bot7 r (Any.t * Any.t)%type
       (Any.t * Any.t)%type cancel_eq smj_top smj_top
       (ModTr.interp_stateE Any.t
          (iterV (ModTr.handle_callE (Mod.prog (HMod.to_mod (HModInline.inline
                 (SMod.to_hmod sp_none (SMod.cancel md))) rs0)))
                 (tid, <[cid:=itr_s]> srcs))
          (Any.pair (HModTr.alist_encode st) r_s ↑))
       (ModTr.interp_stateE Any.t
          (iterV (ModTr.handle_callE (Mod.prog (HMod.to_mod (HModInline.inline
                 (SMod.to_hmod sp md)) rs0)))
                 (tid, <[cid:=itr_t]> tgts))
          (Any.pair (HModTr.alist_encode st) r_t ↑)))
    (EQLEN2 : length rs_diff = length srcs)
    (EQLEN : length srcs = length tgts)
    (REL : ∀ i z x y, rs_diff !! i = Some z →
      srcs !! i = Some x → tgts !! i = Some y → thread_rel sp i z x y)
    (WFR : ✓ r_s)
    (RS : Own r_s ⊢ |==> ([∗ list] i ∈ rs_diff, Own i) ∗ Own r_t)
    (LEN : cid < length srcs)
    (x2 : rs_diff !! cid = Some ε)
    (x0 : srcs !! cid = Some (HModTr.trans (tau;; tau;; tau;; itrS)))
    (x1 : tgts !! cid = Some (x <- HModTr.trans (x <- elim_precond Po Po' varg;; ktrT x);; k x))
    (RET : cid = 0 → k = λ x : Any.t, Ret x)
    (KTR :
    ∃ P : X → Any.t → Any.t → iProp Σ,
      (Po = inl P
       ∨ ∃ x : X,
           X = ()%type
           ∧ Po = inr x ∧ P = λ (_ : X) (varg arg : Any.t), ⌜varg = arg⌝%I)
      ∧ ∃ P' : X' → Any.t → Any.t → iProp Σ,
          (Po' = inl P'
           ∨ ∃ x' : X',
               X' = ()%type
               ∧ Po' = inr x'
                 ∧ P' = λ (_ : X') (varg arg : Any.t), ⌜varg = arg⌝%I)
          ∧ ∀ x : X,
              ∃ x' : X',
                (∀ arg : Any.t, P x varg arg ⊢ |==> P' x' varg arg)
                ∧ upaco4 (elim_rel_def sp) bot4 Any.t ε (itrS) (ktrT (x, x', varg))),

  gpaco7 _simg (cpn7 _simg) bot7 r (Any.t * Any.t)%type 
    (Any.t * Any.t)%type cancel_eq ps pt
    (ModTr.interp_stateE Any.t
       (iterV (ModTr.handle_callE (Mod.prog (HMod.to_mod (HModInline.inline
              (SMod.to_hmod sp_none (SMod.cancel md))) rs0))) (cid, srcs))
       (Any.pair (HModTr.alist_encode st) r_s ↑))
    (ModTr.interp_stateE Any.t
       (iterV (ModTr.handle_callE (Mod.prog (HMod.to_mod (HModInline.inline
              (SMod.to_hmod sp md)) rs0))) (cid, tgts))
       (Any.pair (HModTr.alist_encode st) r_t ↑)).
Proof.
  i. ziter_l. ziter_r. rewrite x0 x1. s. czstep_l.
  move KTR at bottom. des_safe.
  destruct KTR; subst; des_safe.
  { czstep_r. czstep_r.
    ziter_r. czstep_r. ziter_r. czstep_r. czstep_r.
    ziter_r. czstep_r. ziter_r. czstep_r.
    ziter_r. czstep_r. czstep_r.
    ziter_r. czstep_r. czstep_r.
    ziter_r. czstep_r. ziter_r. czstep_r.
    ziter_r. czstep_r. ziter_r. czstep_r.

    specialize (KTR1 x). des; subst.
    { ziter_r. czstep_r. exists x'. czstep_r.
      ziter_r. czstep_r. ziter_r. czstep_r. eexists. czstep_r.
      ziter_r. czstep_r. ziter_r. czstep_r.
      ziter_r. czstep_r. eexists r_t. czstep_r.
      ziter_r. czstep_r. unshelve eexists.
      { split; [eapply Own_wand_valid; [iIntros "S"; iMod (RS with "S") as "[_ $]"|]|]; try done.
        iIntros "H". iMod (x6 with "H") as "[P O]". rewrite KTR1. iFrame. 
      }
      czstep_r. 
      ziter_r. czstep_r. ired.
      ziter_r. czstep_r. ziter_r. czstep_r.
      ziter_l. czstep_l. ziter_l. czstep_l.

      pclearbot. eapply KEY; et.
      { rewrite RS list_insert_id //. }
      (* { rewrite list_insert_id // RS. } *)
      { eapply thread_rel_body; eauto. }
    }
    { destruct x', x'0.
      assert (varg = x3).
      { eapply Own_pure_soundness; try apply WFR.
        rewrite RS. iIntros ">[_ H]". iMod (x6 with "H") as "[P O]".
        rewrite KTR1. iMod "P" as "P"; et.
      }
      des. subst. ired.
      ziter_r. czstep_r. ziter_r. czstep_r.
      ziter_l. czstep_l. ziter_l. czstep_l.
      pclearbot. eapply KEY; et.
      { rewrite RS list_insert_id //. iIntros ">[$ H]". iMod (x6 with "H") as "[P O]". iFrame. et. }
      { econs; eauto. }
    }
  }
  { s. czstep_r.
    specialize (KTR1 ()). des; subst.      
    { ziter_r. czstep_r. exists x'. czstep_r.
      ziter_r. czstep_r. ziter_r. czstep_r. eexists. czstep_r.
      ziter_r. czstep_r. ziter_r. czstep_r.
      ziter_r. czstep_r. eexists r_t. czstep_r.
      ziter_r. czstep_r. unshelve eexists.
      { split; [eapply Own_wand_valid; [iIntros "S"; iMod (RS with "S") as "[_ $]"|]|]; try done.
        iIntros "H". iFrame. iApply KTR1. et.
      }
      czstep_r.
      ziter_r. czstep_r. ziter_r. czstep_r. ziter_r. czstep_r.
      ziter_l. czstep_l. ziter_l. czstep_l.
      pclearbot. destruct x. eapply KEY; et.
      { rewrite list_insert_id //. }
      { econs; eauto. }
    }
    { destruct x, x', x'0.
      ired. ziter_r. czstep_r. ziter_r. czstep_r.
      ziter_l. czstep_l. ziter_l. czstep_l.
      pclearbot. eapply KEY; et.
      { rewrite list_insert_id //. }
      { econs; eauto. }
    }
  }
(*SLOW*)Qed.
