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

Lemma cancel_post `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG} md sp
  (X: Type) (PQ: X → (Any.t → iProp Σ) * (Any.t → iProp Σ)) N mm stid :
  ∀ (rs0 : Σ) r_s r_t srcs tgts cid st ps pt vret (X X': Type) (x: X) (x': X') Q Q' itrS ktrT k rs_diff
    (r : ∀ x x0, (x→x0→Prop)→smj→smj→itree coreE x→itree coreE x0→Prop)
    (WFS: SMod.cancellable md)
    (MAIN: sp !! speckey_entry = Some (fspec_simple PQ))
    (* (WF: Mod.wf (SMod.to_mod sp_none (SMod.cancel md))) *)
    (KEY: ∀ itr_s itr_t st (r_s r_t r_diff : Σ)
             (WFR: ✓ r_s) (WFST: map_Forall (const is_Some) st)
             (RS: Own r_s ⊢ |==> ([∗ list] i ∈ <[cid:=r_diff]> rs_diff, Own i) ∗ Own r_t ∗
                      TIDAUTH cid ∗ YIELDAUTH (length (<[cid:=r_diff]> rs_diff)))
             (LEN: cid < List.length srcs)
             (REL: thread_rel PQ N mm sp cid cid r_diff itr_s itr_t),
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
    (REL : ∀ i x y z, rs_diff !! i = Some z →
      srcs !! i = Some x → tgts !! i = Some y → thread_rel PQ N mm sp cid i z x y)
    (WFR : ✓ r_s)
    (WFST: map_Forall (const is_Some) st)
    (RS : Own r_s ⊢ |==> ([∗ list] i ∈ rs_diff, Own i) ∗ Own r_t ∗
              TIDAUTH cid ∗ YIELDAUTH (length rs_diff))
    (LEN : cid < length srcs)
    (x2 : rs_diff !! cid = Some ε)
    (x0 : srcs !! cid = Some (ModTr.trans (tau;; tau;; itrS)))
    (x1 : tgts !! cid = Some (x <- ModTr.trans (x <- elim_postcond Q Q' N N stid stid x x' vret;; ktrT x);; k x))
    (RET : cid = 0 → k = main_post PQ N mm)
    (KTR :
      (∀ ret : Any.t, Q' (N, stid) x' vret ret ⊢ |==> Q (N, stid) x vret ret)
      ∧ upaco4 (elim_rel_def N sp) bot4 Any.t ε itrS (ktrT vret)),

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
  i. iter_l. iter_r. rewrite x0 x1 /=. step_l. norm_l. norm_r.
  sil. step_l. snl. step_r. i. ired. step_r. norm_r.

  sir. step_r. snr.
  sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l Any.upcast_downcast /= !bind_ret_l.
  sir. step_r. i. step_r. snr.
  sir. step_r. i. step_r. snr.
  sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l.
  sir. step_r. snr.
  sir. step_r. snr.
  (* sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l Any.upcast_downcast /= !bind_ret_l. *)
  (* sir. step_r. i. step_r. snr. *)
  (* sir. step_r. i. step_r. snr. *)
  (* sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l.
  sir. step_r. snr.
  sir. step_r. snr. *)
  sir. step_r. snr.
  sir. step_r. snr.
  sir. step_r. exists vret. step_r. snr.

  des.
  assert (RTV: ✓ r_t).
  { eapply (Own_wand_valid r_s); eauto. iIntros "S"; iMod (RS with "S") as "[_ [$ [_ _]]]"; eauto. }
  
  assert (RES: Own r_t ⊢ |==> ((Own x4) ∗ Q' (N, stid) x' vret x3)).
  { rewrite x6. iIntros ">[$ $]"; eauto. }
  hexploit (Own_bupd_split r_t); [eapply RES|eauto|].
  i; des.

  sir. step_r. snr.
  sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l Any.upcast_downcast /= !bind_ret_l.
  sir. step_r. exists r_t. step_r. snr.
  sir. step_r. unshelve eexists; ired.
  { split; eauto.
    (* { eapply (Own_wand_valid r_t); eauto. rewrite H. iIntros ">[_ $]"; eauto. } *)
    rewrite RES. iIntros "> [$ ?]"; rewrite KTR; eauto. }
  step_r. snr.
  sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l.
  sir. step_r. snr.
  sir. step_r. snr.
  (* sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l Any.upcast_downcast /= !bind_ret_l.
  sir. step_r. exists r_t. step_r. snr.
  sir. step_r. unshelve eexists; ired.
  { des; split; [eapply Own_wand_valid; [iIntros "S"; iMod (RS with "S") as "[_ [$ [_ _]]]"|]|]; try done.
    rewrite H H1 KTR. iIntros ">[$ >$]"; eauto. }
  step_r. snr.
  sir. step_r. snr. rewrite Any.pair_split /= !bind_ret_l.
  sir. step_r. snr.
  sir. step_r. snr. *)

  des; pclearbot. eapply KEY; et.
  { rewrite list_insert_id //. }
  { econs; eauto; eapply KTR1. }
(*SLOW*)Qed.
