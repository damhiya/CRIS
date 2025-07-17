Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import SModTr HModTr ModTr SMod HMod Mod.
Require Import ITactics TacticsCommon SimGlobal SimGlobalFacts CtxRefine ClosedAdequacy.
Require Import HModInline HModInlineIntro HModInlineElim ElimRel.
Require Import SimGlobal SimGTactics.

Lemma cancel_post `{Σ: GRA} md sp:
  ∀ (rs0 : Σ) r_s r_t srcs tgts cid st ps pt vret X X' x x' Qo Qo' itrS ktrT k rs_diff
    (r : ∀ x x0, (x→x0→Prop)→smj→smj→itree coreE x→itree coreE x0→Prop)
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
    (REL : ∀ i x y z, rs_diff !! i = Some z →
      srcs !! i = Some x → tgts !! i = Some y → thread_rel sp i z x y)
    (WFR : ✓ r_s)
    (RS : Own r_s ⊢ |==> ([∗ list] i ∈ rs_diff, Own i) ∗ Own r_t)
    (LEN : cid < length srcs)
    (x2 : rs_diff !! cid = Some ε)
    (x0 : srcs !! cid = Some (HModTr.trans (tau;; tau;; itrS)))
    (x1 : tgts !! cid = Some (x <- HModTr.trans (x <- elim_postcond Qo Qo' x x' vret;; ktrT x);; k x))
    (RET : cid = 0 → k = λ x : Any.t, Ret x)
    (KTR :
    ∃ Q : X → Any.t → Any.t → iProp Σ,
      (Qo = Some Q
       ∨ Qo = None ∧ Q = λ (_ : X) (varg arg : Any.t), ⌜varg = arg⌝%I)
      ∧ ∃ Q' : X' → Any.t → Any.t → iProp Σ,
          (Qo' = Some Q'
           ∨ Qo' = None ∧ Q' = λ (_ : X') (varg arg : Any.t), ⌜varg = arg⌝%I)
          ∧ (∀ ret : Any.t, Q' x' vret ret ⊢ |==> Q x vret ret)
            ∧ upaco4 (elim_rel_def sp) bot4 Any.t ε itrS (ktrT vret)),

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
  i. ziter_l. ziter_r. rewrite x0 x1 /=. czstep_l. ziter_l. czstep_l.
  move KTR at bottom. des_safe.
  destruct KTR0; subst; des_safe.
  { czstep_r. czstep_r.
    ziter_r. czstep_r. ziter_r. czstep_r.
    ziter_r. czstep_r. czstep_r. ziter_r. czstep_r. czstep_r.
    ziter_r. czstep_r. ziter_r. czstep_r. ziter_r. czstep_r.
    ziter_r. czstep_r. ziter_r. czstep_r.

    des; subst.
    { ziter_r. czstep_r. eexists. czstep_r.
      ziter_r. czstep_r. ziter_r. czstep_r.
      ziter_r. czstep_r. eexists r_t. czstep_r.
      ziter_r. czstep_r. unshelve eexists.
      { split; [eapply Own_wand_valid; [iIntros "S"; iMod (RS with "S") as "[_ $]"|]|]; try done.
        iIntros "H". iMod (x6 with "H") as "[P O]". rewrite KTR1. iFrame. 
      }
      czstep_r.
      ziter_r. czstep_r. ziter_r. czstep_r. ziter_r. czstep_r.

      pclearbot. eapply KEY; et.
      { rewrite list_insert_id //. }
      { econs; eauto; eapply KTR1. }
    }
    { assert (vret = x3).
      { eapply Own_pure_soundness; try apply WFR.
        rewrite RS. iIntros ">[? H]". iMod (x6 with "H") as "[P O]".
        rewrite KTR1. iMod "P" as "P"; et.
      }
      des. subst.
      ired. pclearbot. eapply KEY; et.
      rewrite RS list_insert_id //. iIntros ">[$ H]". iMod (x6 with "H") as "[P O]". iFrame. et.
      econs; eauto; eapply KTR1.
    }
  }
  {
    s. czstep_r.
    des; subst.      
    { ziter_r. czstep_r.
      ziter_r. czstep_r. eexists. czstep_r.
      ziter_r. czstep_r. ziter_r. czstep_r.
      ziter_r. czstep_r. eexists r_t. czstep_r.
      ziter_r. czstep_r. unshelve eexists.
      { split; [eapply Own_wand_valid; [iIntros "S"; iMod (RS with "S") as "[_ $]"|]|]; try done.
        iIntros "H". iFrame. iApply KTR1. et.
      }
      czstep_r.
      ziter_r. czstep_r. ziter_r. czstep_r. ziter_r. czstep_r.

      pclearbot. eapply KEY; et.
      { rewrite list_insert_id //. }
      { econs; eauto; eapply KTR1. }
    }
    { ziter_r. czstep_r.
      pclearbot. eapply KEY; et.
      { rewrite list_insert_id //. }
      { econs; eauto; eapply KTR1. }
    }
  }
(*SLOW*)Qed.
