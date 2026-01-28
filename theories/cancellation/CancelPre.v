Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics CancelTactics.
Require Import MInline MInlineIntro MInlineElim ElimRel.

Local Ltac sil := iter_l; rewrite !list_lookup_insert ?length_insert //.
Local Ltac snl := norm_l; rewrite !list_insert_insert ?bind_ret_l.
Local Ltac sir :=
  match goal with
  | [ EQLEN : length _ = length _ |- _ ] => iter_r; rewrite !list_lookup_insert ?length_insert -EQLEN //
  end.
Local Ltac snr := norm_r; rewrite !list_insert_insert ?bind_ret_l.

(* before canceltactics : 23s *)
(* after canceltactics : 13s *)

Lemma cancel_pre `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG} md sp
  (X: Type) (PQ: X → (Any.t → iProp Σ) * (Any.t → iProp Σ)) mm :
  ∀ (rs0 : Σ) r_s r_t rs_diff srcs tgts cid st ps pt varg X X' P P' itrS ktrT k
    (r: ∀ x x0, (x→x0→Prop)→smj→smj→itree coreE x→itree coreE x0→Prop)
    (WFS: SMod.cancellable md)
    (MAIN: sp !! speckey_entry = Some (fspec_simple PQ))
    (KEY: ∀ itr_s itr_t st (r_s r_t r_diff : Σ)
             (WFR: ✓ r_s) (WFST: map_Forall (const is_Some) st)
             (RS: Own r_s ⊢ |==> ([∗ list] i ∈ <[cid:=r_diff]> rs_diff, Own i) ∗ Own r_t ∗
                      TIDAUTH cid ∗ YIELDAUTH (length (<[cid:=r_diff]> rs_diff)))
             (LEN: cid < List.length srcs)
             (REL: thread_rel PQ mm sp cid cid r_diff itr_s itr_t),
     gpaco7 _gsim (cpn7 _gsim) bot7 r (Any.t * Any.t)%type
       (Any.t * Any.t)%type cancel_eq smj_top smj_top
       (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                 (SMod.to_mod ∅ (SMod.cancel md))) rs0)))
                 (cid, <[cid:=itr_s]> srcs))
          (Any.pair (ModTr.state_encode st) r_s ↑))
       (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
                 (SMod.to_mod sp md)) rs0)))
                 (cid, <[cid:=itr_t]> tgts))
          (Any.pair (ModTr.state_encode st) r_t ↑)))
    (EQLEN2 : length rs_diff = length srcs)
    (EQLEN : length srcs = length tgts)
    (REL : ∀ i z x y, rs_diff !! i = Some z →
      srcs !! i = Some x → tgts !! i = Some y → thread_rel PQ mm sp cid i z x y)
    (WFR : ✓ r_s)
    (WFST: map_Forall (const is_Some) st)
    (RS : Own r_s ⊢ |==> ([∗ list] i ∈ rs_diff, Own i) ∗ Own r_t ∗
              TIDAUTH cid ∗ YIELDAUTH (length rs_diff))
    (LEN : cid < length srcs)
    (x2 : rs_diff !! cid = Some ε)
    (x0 : srcs !! cid = Some (ModTr.trans (tau;; tau;; tau;; itrS)))
    (x1 : tgts !! cid = Some (x <- ModTr.trans (x <- elim_precond P P' varg;; ktrT x);; k x))
    (RET : cid = 0 → k = main_post PQ mm)
    (KTR :
      ∀ x : X, ∃ (x' : X'),
        (∀ arg : Any.t, P x varg arg ⊢ |==> P' x' varg arg)
        ∧ upaco4 (elim_rel_def sp) bot4 Any.t ε (itrS) (ktrT (x, x', varg))),

  gpaco7 _gsim (cpn7 _gsim) bot7 r (Any.t * Any.t)%type 
    (Any.t * Any.t)%type cancel_eq ps pt
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
              (SMod.to_mod ∅ (SMod.cancel md))) rs0))) (cid, srcs))
       (Any.pair (ModTr.state_encode st) r_s ↑))
    (LModTr.interp_stateE Any.t
       (iterV (LModTr.handle_callE (LMod.prog (Mod.to_lmod (MInline.inline
              (SMod.to_mod sp md)) rs0))) (cid, tgts))
       (Any.pair (ModTr.state_encode st) r_t ↑)).
Proof.
  i. iter_l. rewrite x0 /=. step_l. norm_l.
  iter_r. rewrite x1 /=. step_r. i. step_r. norm_r.
  rewrite !bind_ret_l.

  specialize (KTR x). des.

  sir. step_r. snr.
  sir. step_r. i. step_r. snr.
  sir. step_r. snr.
  sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l Any.upcast_downcast /= !bind_ret_l.
  sir. step_r. i. step_r. snr.
  sir. step_r. i. step_r. snr.
  sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l.
  sir. step_r. snr.
  sir. step_r. snr.
  (* sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l Any.upcast_downcast /= !bind_ret_l.
  sir. step_r. i. step_r. snr.
  sir. step_r. i. step_r. snr.
  sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l.
  sir. step_r. snr.
  sir. step_r. snr.
  sir. step_r. snr.
  sir. step_r. exists (N, stid). step_r. snr. *)
  sir. step_r. snr.
  sir. step_r. exists x'. step_r. snr.
  sir. step_r. snr.
  sir. step_r. exists varg. step_r. snr.
  sir. step_r. snr.
  sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l Any.upcast_downcast /= !bind_ret_l.

  des.
  assert (RTV: ✓ r_t).
  { eapply (Own_wand_valid r_s); eauto. iIntros "S"; iMod (RS with "S") as "[_ [$ [_ _]]]"; eauto. }
  
  (* assert (RES: Own r_t ⊢ |==> (((TID stid ∗ YIELD stid ∗ winv (⊤, ⊤)) ∗ Own x6) ∗ P x varg x3)).
  { rewrite x9 x8. iIntros ">[($ & $ & $) >[$ $]]"; eauto. }
  hexploit (Own_bupd_split r_t); [eapply RES|eauto|].
  i; des. *)
  
  sir. step_r. exists r_t. step_r. snr.
  sir. step_r. unshelve eexists; ired.
  { split; eauto.
    rewrite x6 KTR. iIntros "> [>$ $] //". }
  step_r. snr.
  sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l.
  sir. step_r. snr.
  sir. step_r. snr.
  (* sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l Any.upcast_downcast /= !bind_ret_l.
  sir. step_r. exists r_t. step_r. snr.
  sir. step_r. unshelve eexists.
  { split; eauto. rewrite H H1 KTR. iIntros ">[$ >$]"; eauto. }
  step_r. snr.
  sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l.
  sir. step_r. snr.
  sir. step_r. snr. *)

  sil. step_l. snl.
  sil. step_l. snl.
  
  pclearbot. eapply KEY; et.
  { rewrite RS list_insert_id //. }
  { eapply thread_rel_body; eauto. }
(*SLOW*)Qed.
