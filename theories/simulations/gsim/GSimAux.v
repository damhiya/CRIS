From CRIS.common Require Export Common ConcRA.
From CRIS.modules Require Export FSpec Sp.
From CRIS.modules Require Export SMod Mod LMod.
From CRIS.simulations.msim Require Export Tactics.
From CRIS.simulations.gsim Require Import GSim GSimTactics.
From iris.proofmode Require Export proofmode.
From stdpp Require Export base list.

(* This file contains auxilliary lemmas for proving HelpOn ≼ HelpOff. *)
Notation "'⇓cris'" := (interpV (ModTr.handle_crisE)).
Notation "'⇓sb(' m ')'" := (SB.sandbox m).
Notation "'⇓smod(' sp ')'" := (SModTr.trans sp).

Local Ltac ghnorm_itr :=
  match goal with
  | |- context [?A] =>
      match type of A with
      | itree crisE Any.t => pattern A; eapply eq_ind; [|symmetry; hnorm_itr]
      end
  end.

Ltac lookup_tac :=
  match goal with
  | H : ?l !! ?i = _ |- (_ <$> ?l) !! ?i = _ => rewrite list_lookup_fmap H //
  | |- <[?i := _]> _ !! ?i = _ => rewrite list_lookup_insert; [|rewrite ?length_insert ?length_fmap //]
  end.
Ltac ghcNormS := greplace_s; [ghnorm_itr; refl|].
Ltac ghcNormT := greplace_t; [ghnorm_itr; refl|].

Section props.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Lemma gsim_flag r g RR p_s p_t p_s1 p_t1 i_s i_t :
    smj_le p_s1 p_s →
    smj_le p_t1 p_t →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s1 p_t1
      i_s i_t →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      i_s i_t.
  Proof using. guclo flagC_spec; econs; eauto. Qed.

  Lemma gsim_tau_src r g RR p_s p_t st_s itr_t prog_s tid_s tp_s k :
    tp_s !! tid_s = Some (⇓cris (tau;; k)) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR smj_top p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := (⇓cris k)]> tp_s)) st_s)
      itr_t →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      itr_t.
  Proof using. intros Hi ?. giter_s. s. rewrite Hi; ss. gstep_s. gcNormS. done. Qed.

  Lemma gsim_tau_tgt r g RR p_s p_t itr_s st_t prog_t tid_t tp_t k :
    tp_t !! tid_t = Some (⇓cris (tau;; k)) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s smj_top
      itr_s
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris k]> tp_t)) st_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      itr_s
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof using. intros Hi ?. giter_t; rewrite /= Hi; ss. gstep_t; gcNormT. done. Qed.

  Lemma gsim_Choose_src r g RR p_s p_t st_s prog_s tid_s tp_s X k itr_t :
    tp_s !! tid_s = Some (⇓cris (x <- trigger (Choose X);; k x)) →
    (∃ (x : X),
      gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := ⇓cris (k x)]> tp_s)) st_s)
        itr_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      itr_t.
  Proof using.
    intros Hi [x Hk]; giter_s; s; rewrite Hi /=; gstep_s; exists x; gsteps_s.
    by (ired; eapply Hk).
  Qed.

  Lemma gsim_Choose_tgt r g RR p_s p_t st_t prog_t tid_t tp_t X k itr_s :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (Choose X);; k x)) →
    (∀ (x : X),
      gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s smj_top
        itr_s
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_t)
            (tid_t, <[tid_t := ⇓cris (k x)]> tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      itr_s
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof using.
    intros Hi Hk; giter_t; s; rewrite Hi /=; gstep_t; intros x; gsteps_t.
    by ired.
  Qed.

  Lemma gsim_Take_src r g RR p_s p_t st_s prog_s tid_s tp_s X k itr_t :
    tp_s !! tid_s = Some (⇓cris (x <- trigger (Take X);; k x)) →
    (∀ (x : X),
      gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := ⇓cris (k x)]> tp_s)) st_s)
        itr_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      itr_t.
  Proof using.
    intros Hi Hk; giter_s; s; rewrite Hi /=; gstep_s; intros x; gsteps_s.
    by (ired).
  Qed.

  Lemma gsim_Take_tgt r g RR p_s p_t st_t prog_t tid_t tp_t X k itr_s :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (Take X);; k x)) →
    (∃ (x : X),
      gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s smj_top
        itr_s
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_t)
            (tid_t, <[tid_t := ⇓cris (k x)]> tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      itr_s
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof using.
    intros Hi [x Hk]; giter_t; s; rewrite Hi /=; gstep_t; exists x; gsteps_t.
    by ired.
  Qed.

  Lemma gsim_IO {I O} r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      fn (args : I) k_s k_t :
    tp_s !! tid_s = Some (⇓cris (x <- trigger (IO fn args);; k_s x)) →
    tp_t !! tid_t = Some (⇓cris (x <- trigger (IO fn args);; k_t x)) →
    (∀ (ret : O),
      gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR smj_top smj_top
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := ⇓cris (k_s ret)]> tp_s)) st_s)
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_t)
            (tid_t, <[tid_t := ⇓cris (k_t ret)]> tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof using.
    intros His Hit ?; giter_t; giter_s; s; rewrite His Hit /=.
    gcNormS; gcNormT. gstep_s. intros ? ? ->.
    gstep_s. gstep_t. by ired.
  Unshelve. eauto.
  Qed.

  Lemma gsim_Call_src r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t fn args k :
    tp_s !! tid_s = Some (⇓cris (x <- trigger (Call fn args);; k x)) →
    (gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR smj_top p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := bd <- (prog_s fn)?;; x <- (bd args);; ⇓cris (tau;; k x)]> tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof using.
    intros Hi Hk.
    giter_s. rewrite /= Hi; ss. gstep_s. ired.
    greplace_s; [|apply Hk].
    do 4 f_equal. destruct (prog_s); ss; grind.
    { do 3 f_equal; grind. rewrite interpV_tau //. }
    { rewrite unfold_iterV /=; rewrite list_lookup_insert /=; grind.
      by apply lookup_lt_is_Some.
    }
  Qed.

  Lemma gsim_Call_tgt r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t fn args k :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (Call fn args);; k x)) →
    (gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s smj_top
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := bd <- (prog_t fn)?;; x <- (bd args);; ⇓cris (tau;; k x)]> tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof using.
    intros Hi Hk.
    giter_t. rewrite /= Hi; ss. gstep_t. ired.
    greplace_t; [|apply Hk].
    do 4 f_equal. destruct (prog_t); ss; grind.
    { do 3 f_equal; grind. rewrite interpV_tau //. }
    { rewrite unfold_iterV /=; rewrite list_lookup_insert /=; grind.
      by apply lookup_lt_is_Some.
    }
  Qed.

  Lemma gsim_Spawn_src r g RR p_s p_t itr_t st_s prog_s tid_s tp_s fn args k :
    tp_s !! tid_s = Some (⇓cris (x <- trigger (Spawn fn args);; k x)) →
    (gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR smj_top p_t
      (LModTr.interp_stateE Any.t
        (bd <- (prog_s fn)?;;
        iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k (List.length tp_s))]> tp_s ++ [bd args])) st_s)
      itr_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      itr_t.
  Proof using.
    intros Hi Hk.
    giter_s. rewrite /= Hi; ss. gstep_s. ired.
    greplace_s; [|apply Hk].
    do 1 f_equal. grind.
  Qed.

  Lemma gsim_Spawn_tgt r g RR p_s p_t itr_s st_t prog_t tid_t tp_t fn args k :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (Spawn fn args);; k x)) →
    (gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s smj_top
      (itr_s)
      (LModTr.interp_stateE Any.t
        (bd <- (prog_t fn)?;;
        iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k (List.length tp_t))]> tp_t ++ [bd args])) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (itr_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof using.
    intros Hi Hk.
    giter_t. rewrite /= Hi; ss. gstep_t. ired.
    greplace_t; [|apply Hk].
    do 1 f_equal. grind.
  Qed.

  Lemma gsim_GetTid_src r g RR p_s p_t itr_t st_s prog_s tid_s tp_s k :
    tp_s !! tid_s = Some (⇓cris (x <- trigger GetTid;; k x)) →
    (gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR smj_top p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k (tid_s))]> tp_s)) st_s)
      itr_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      itr_t.
  Proof using. intros Hi Hk. giter_s. rewrite /= Hi; ss. gstep_s. by ired. Qed.

  Lemma gsim_GetTid_tgt r g RR p_s p_t itr_s st_t prog_t tid_t tp_t k :
    tp_t !! tid_t = Some (⇓cris (x <- trigger GetTid;; k x)) →
    (gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s smj_top
      (itr_s)
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k (tid_t))]> tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (itr_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof using. intros Hi Hk. giter_t. rewrite /= Hi; ss. gstep_t. by ired. Qed.

  Lemma gsim_Yield_src r g RR p_s p_t itr_t st_s prog_s tid_s tid_s2 tp_s k :
    tp_s !! tid_s = Some (⇓cris (x <- trigger (Yield tid_s2);; k x)) →
    (gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR smj_top p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s)
          (tid_s2, <[tid_s := ⇓cris (k ())]> tp_s)) st_s)
      itr_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      itr_t.
  Proof using. intros Hi Hk. giter_s. rewrite /= Hi; ss. gstep_s. by ired. Qed.

  Lemma gsim_Yield_tgt r g RR p_s p_t itr_s st_t prog_t tid_t tid_t2 tp_t k :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (Yield tid_t2);; k x)) →
    (gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s smj_top
      (itr_s)
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t)
          (tid_t2, <[tid_t := ⇓cris (k ())]> tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (itr_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof using. intros Hi Hk. giter_t. rewrite /= Hi; ss. gstep_t. by ired. Qed.

  Lemma gsim_SGet_tgt r g RR p_s p_t itr_s st_t prog_t tid_t tp_t key k r_t :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (SGet key);; k x)) →
    map_Forall (const is_Some) st_t →
    (gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s smj_top
      itr_s
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k (default ()↑ (mjoin (st_t !! key))))]> tp_t))
        (st_t, r_t))) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      itr_s
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t))
        (st_t, r_t)).
  Proof using.
    intros Hin ? ?.
    giter_t; rewrite /= Hin; ss. gsteps_t. cSimpl. ired. eauto.
  Qed.

  Lemma gsim_SGet_src r g RR p_s p_t itr_t st_s prog_s tid_s tp_s key k r_s :
    tp_s !! tid_s = Some (⇓cris (x <- trigger (SGet key);; k x)) →
    map_Forall (const is_Some) st_s →
    (gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR smj_top p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k (default ()↑ (mjoin (st_s !! key))))]> tp_s))
        (st_s, r_s))
      itr_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s))
        (st_s, r_s))
      itr_t.
  Proof using.
    intros Hin ? ?.
    giter_s; rewrite /= Hin; ss. gsteps_s. cSimpl. ired. eauto.
  Qed.

  Lemma gsim_SPut_tgt r g RR p_s p_t itr_s st_t prog_t tid_t tp_t key val k r_t :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (SPut key val);; k x)) →
    map_Forall (const is_Some) st_t →
    (gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s smj_top
      itr_s
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k ())]> tp_t))
        (<[key := Some val]> st_t, r_t))) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      itr_s
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t))
        (st_t, r_t)).
  Proof using.
    intros Hin ? ?; eapply lookup_lt_Some in Hin as ?.
    giter_t; rewrite /= Hin; ss. gsteps_t. cSimpl.
    giter_t; rewrite /= list_lookup_insert //=. gsteps_t. ired.
    rewrite list_insert_insert //.
  Qed.

  Lemma gsim_SPut_src r g RR p_s p_t itr_t st_s prog_s tid_s tp_s key val k r_s :
    tp_s !! tid_s = Some (⇓cris (x <- trigger (SPut key val);; k x)) →
    map_Forall (const is_Some) st_s →
    (gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR smj_top p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k ())]> tp_s))
        (<[key := Some val]> st_s, r_s))
      itr_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s))
        (st_s, r_s))
      itr_t.
  Proof using.
    intros Hin ? ?; eapply lookup_lt_Some in Hin as ?.
    giter_s; rewrite /= Hin; ss. gsteps_s. cSimpl.
    giter_s; rewrite /= list_lookup_insert //=. gsteps_s. ired.
    rewrite list_insert_insert //.
  Qed.

  Lemma gsim_Assume_src r g RR p_s p_t st_s prog_s tid_s tp_s k P r_s itr_t :
    tp_s !! tid_s = Some (⇓cris (x <- trigger (Assume P);; k x)) →
    (∀ r_s2,
      ✓ r_s2 ∧ (Own r_s2 ⊢ |==> P ∗ Own r_s) →
      gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := ⇓cris (k ())]> tp_s))
          (st_s, r_s2))
        itr_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (st_s, r_s))
      itr_t.
  Proof using.
    intros Hi Hk; pose proof Hi as Hlen; eapply lookup_lt_Some in Hlen.
    giter_s; rewrite /= Hi; ss.
    gsteps_s. cSimpl. ired. cSimpl. ired.
    giter_s. rewrite /= list_lookup_insert //=. gstep_s. intros r_s2.
      gsteps_s. ired. rewrite list_insert_insert.
    giter_s. rewrite /= list_lookup_insert //=. gstep_s. intros Hr_s2.
      gsteps_s. ired. rewrite list_insert_insert.
    giter_s. rewrite /= list_lookup_insert //=. gstep_s.
      gsteps_s. ired. cSimpl. ired. rewrite list_insert_insert.
    giter_s. rewrite /= list_lookup_insert //=. gstep_s.
      gsteps_s. ired. rewrite list_insert_insert.
    eapply Hk; done.
  Qed.

  Lemma gsim_Assume_tgt r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t k P r_t :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (Assume P);; k x)) →
    (∃ r_t2,
      ✓ r_t2 ∧ (Own r_t2 ⊢ |==> P ∗ Own r_t) ∧
      gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s smj_top
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_t)
            (tid_t, <[tid_t := ⇓cris (k ())]> tp_t))
          (st_t, r_t2))) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (st_t, r_t)).
  Proof using.
    intros Hin [r_t2 [Hr_t2 Hk]]; pose proof Hin as Hlen; eapply lookup_lt_Some in Hlen.
    giter_t; rewrite /= Hin /=. gstep_t. gsteps_t. cSimpl. ired. cSimpl. ired.
    giter_t. rewrite /= list_lookup_insert //=. gstep_t. exists r_t2.
      gsteps_t. rewrite list_insert_insert //=. ired.
    giter_t. rewrite /= list_lookup_insert //=. gstep_t. unshelve eexists; eauto; ss.
      gsteps_t. rewrite list_insert_insert //=. ired.
    giter_t. rewrite /= list_lookup_insert //=. gsteps_t.
      rewrite list_insert_insert //=. ired. cSimpl. ired.
    giter_t. rewrite /= list_lookup_insert //=. gsteps_t.
      rewrite list_insert_insert //=. ired. eauto.
  Qed.

  Lemma gsim_AssumeRes_src r g RR p_s p_t st_s prog_s tid_s tp_s k r_s r_s2 itr_t :
    tp_s !! tid_s =
      Some (⇓cris (x <- trigger (AssumeRes r_s2);; k x)) →
    (✓ (r_s2 ⋅ r_s) →
      gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := ⇓cris (k ())]> tp_s))
          (st_s, r_s2 ⋅ r_s))
        itr_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (st_s, r_s))
      itr_t.
  Proof using.
    intros Hin Hk; pose proof Hin as Hlen; eapply lookup_lt_Some in Hlen.
    giter_s; rewrite /= Hin /=. gstep_s; ss. gcNormS. cSimpl. ired. cSimpl. ired.
    giter_s; rewrite /= list_lookup_insert //=. gstep_s; ss.
      intros Hval. gcNormS. gstep_s. gcNormS. rewrite list_insert_insert.
    giter_s; rewrite /= list_lookup_insert //=. gstep_s; ss.
      gcNormS. ired. cSimpl. ired. rewrite list_insert_insert.
    giter_s; rewrite /= list_lookup_insert //=. gstep_s; ss.
      gcNormS. ired. rewrite list_insert_insert.
    eapply Hk; done.
  Qed.

  Lemma gsim_AssumeRes_tgt r g RR p_s p_t st_t prog_s tid_t tp_t k r_t r_t2 itr_s :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (AssumeRes r_t2);; k x)) →
    (✓ (r_t2 ⋅ r_t) ∧
      gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s smj_top
        itr_s
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_t, <[tid_t := ⇓cris (k ())]> tp_t))
          (st_t, r_t2 ⋅ r_t))) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      itr_s
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_t, tp_t)) (st_t, r_t)).
  Proof using.
    intros Hin [Hval Hk]; pose proof Hin as Hlen; eapply lookup_lt_Some in Hlen.
    giter_t; rewrite /= Hin /=. gstep_t; ss. gcNormT. cSimpl. ired. cSimpl. ired.
    giter_t; rewrite /= list_lookup_insert //=.
      gstep_t; ss. exists Hval. gsteps_t. rewrite list_insert_insert. ired.
    giter_t; rewrite /= list_lookup_insert //=.
      gsteps_t; ss. rewrite list_insert_insert. ired. cSimpl. ired.
    giter_t; rewrite /= list_lookup_insert //=.
      gsteps_t; ss. rewrite list_insert_insert. ired.
    eapply Hk; done.
  Qed.

  Lemma gsim_Guarantee_src r g RR p_s p_t st_s prog_s tid_s tp_s k P r_s itr_t :
    tp_s !! tid_s = Some (⇓cris (x <- trigger (Guarantee P);; k x)) →
    (∃ r_s2,
      ✓ r_s2 ∧ (Own r_s ⊢ |==> P ∗ Own r_s2) ∧
      gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := ⇓cris (k ())]> tp_s))
          (st_s, r_s2))
        itr_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (st_s, r_s))
      itr_t.
  Proof using.
    intros Hi [r_s2 Hk]; pose proof Hi as Hlen; eapply lookup_lt_Some in Hlen.
    giter_s; rewrite /= Hi; ss.
    gsteps_s. cSimpl. ired. cSimpl. ired.
    giter_s. rewrite /= list_lookup_insert //=. gstep_s. exists r_s2.
      gsteps_s. ired. rewrite list_insert_insert.
    giter_s. rewrite /= list_lookup_insert //=. gstep_s. unshelve eexists; eauto.
      gsteps_s. ired. rewrite list_insert_insert.
    giter_s. rewrite /= list_lookup_insert //=. gstep_s.
      gsteps_s. ired. cSimpl. ired. rewrite list_insert_insert.
    giter_s. rewrite /= list_lookup_insert //=. gstep_s.
      gsteps_s. ired. rewrite list_insert_insert.
    eauto.
  Qed.

  Lemma gsim_Guarantee_tgt r g RR p_s p_t itr_s st_t prog_t tid_t tp_t k P r_t :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (Guarantee P);; k x)) →
    (∀ r_t2,
      ✓ r_t2 ∧ (Own r_t ⊢ |==> P ∗ Own r_t2) →
      gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s smj_top
        itr_s
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_t)
            (tid_t, <[tid_t := ⇓cris (k ())]> tp_t))
          (st_t, r_t2))) →
    gpaco7 _gsim (cpn7 _gsim) r g (lstateT Σ * Any.t)%type (lstateT Σ * Any.t)%type RR p_s p_t
      itr_s
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (st_t, r_t)).
  Proof using.
    intros Hin ?; pose proof Hin as Hlen; eapply lookup_lt_Some in Hlen.
    giter_t; rewrite /= Hin /=. gstep_t. gsteps_t. cSimpl. ired. cSimpl. ired.
    giter_t. rewrite /= list_lookup_insert //=. gstep_t. intros ?.
      gsteps_t. rewrite list_insert_insert //=. ired.
    giter_t. rewrite /= list_lookup_insert //=. gstep_t. i.
      gsteps_t. rewrite list_insert_insert //=. ired.
    giter_t. rewrite /= list_lookup_insert //=. gsteps_t.
      rewrite list_insert_insert //=. ired. cSimpl. ired.
    giter_t. rewrite /= list_lookup_insert //=. gsteps_t.
      rewrite list_insert_insert //=. ired.
    eauto.
  Qed.
End props.
