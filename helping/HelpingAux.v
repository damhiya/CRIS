Require Import CRIS.
Require Import LMod.
Require Import GSim GSimFacts GSimTactics.
Require Import SchHeader SchI SchA.
From CRIS.helping Require Import Header HelpingOn HelpingOff.

(* This file contains auxilliary lemmas for proving HelpOn ≼ HelpOff. *)
Notation "'⇓cris'" := (interpV (ModTr.handle_crisE)).
Notation "'⇓sb(' m ')'" := (SB.sandbox m).
Notation "'⇓smod(' sp ',' N ',' stid ')'" := (SModTr.trans sp N stid).

Local Ltac gnorm_itr :=
  match goal with
  | |- context [?A] =>
      match type of A with
      | itree crisE Any.t => pattern A; eapply eq_ind; [|symmetry; hnorm_itr]
      end
  end.

Ltac lookup_tac :=
  match goal with
  | H : ?l !! ?i = _ |- (_ <$> ?l) !! ?i = _ => rewrite list_lookup_fmap H //
  | |- <[?i := _]> _ !! ?i = _ => rewrite list_lookup_insert; [|rewrite ?length_fmap //]
  end.
Ltac ghnorm_l := replace_l; [gnorm_itr; refl|].
Ltac ghnorm_r := replace_r; [gnorm_itr; refl|].

Section props.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !newschG}.

  Lemma gsim_flag r g RR p_s p_t p_s1 p_t1 i_s i_t :
    smj_le p_s1 p_s →
    smj_le p_t1 p_t →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s1 p_t1
      i_s i_t →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      i_s i_t.
  Proof using. guclo flagC_spec; econs; eauto. Qed.

  Lemma gsim_tau_src r g RR p_s p_t st_s itr_t prog_s tid_s tp_s k :
    tp_s !! tid_s = Some (⇓cris (tau;; k)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := (⇓cris k)]> tp_s)) st_s)
      itr_t →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      itr_t.
  Proof using. intros Hi ?. giter_l. s. rewrite Hi; ss. gstep_l. gnorm_l. done. Qed.

  Lemma gsim_tau_tgt r g RR p_s p_t itr_s st_t prog_t tid_t tp_t k :
    tp_t !! tid_t = Some (⇓cris (tau;; k)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
      itr_s
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris k]> tp_t)) st_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      itr_s
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof using. intros Hi ?. giter_r; rewrite /= Hi; ss. gstep_r; gnorm_r. done. Qed.

  Lemma gsim_Choose_src r g RR p_s p_t st_s prog_s tid_s tp_s X k itr_t :
    tp_s !! tid_s = Some (⇓cris (x <- trigger (Choose X);; k x)) →
    (∃ (x : X),
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := ⇓cris (k x)]> tp_s)) st_s)
        itr_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      itr_t.
  Proof using.
    intros Hi [x Hk]; giter_l; s; rewrite Hi /=; gstep_l; exists x; gsteps_l.
    by (ired; eapply Hk).
  Qed.

  Lemma gsim_Choose_tgt r g RR p_s p_t st_t prog_t tid_t tp_t X k itr_s :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (Choose X);; k x)) →
    (∀ (x : X),
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
        itr_s
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_t)
            (tid_t, <[tid_t := ⇓cris (k x)]> tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      itr_s
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof using.
    intros Hi Hk; giter_r; s; rewrite Hi /=; gstep_r; intros x; gsteps_r.
    by ired.
  Qed.

  Lemma gsim_Take_src r g RR p_s p_t st_s prog_s tid_s tp_s X k itr_t :
    tp_s !! tid_s = Some (⇓cris (x <- trigger (Take X);; k x)) →
    (∀ (x : X),
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := ⇓cris (k x)]> tp_s)) st_s)
        itr_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      itr_t.
  Proof using.
    intros Hi Hk; giter_l; s; rewrite Hi /=; gstep_l; intros x; gsteps_l.
    by (ired).
  Qed.

  Lemma gsim_Take_tgt r g RR p_s p_t st_t prog_t tid_t tp_t X k itr_s :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (Take X);; k x)) →
    (∃ (x : X),
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
        itr_s
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_t)
            (tid_t, <[tid_t := ⇓cris (k x)]> tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      itr_s
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof using.
    intros Hi [x Hk]; giter_r; s; rewrite Hi /=; gstep_r; exists x; gsteps_r.
    by ired.
  Qed.

  Lemma gsim_Call_src r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t fn args k :
    tp_s !! tid_s = Some (⇓cris (x <- trigger (Call fn args);; k x)) →
    (gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := bd <- (prog_s fn)?;; x <- (bd args);; ⇓cris (tau;; k x)]> tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof using.
    intros Hi Hk.
    giter_l. rewrite /= Hi; ss. gstep_l. ired.
    replace_l; [|apply Hk].
    do 4 f_equal. destruct (prog_s); ss; grind.
    { do 3 f_equal; grind. rewrite interpV_tau //. }
    { rewrite unfold_iterV /=; rewrite list_lookup_insert /=; grind.
      by apply lookup_lt_is_Some.
    }
  Qed.

  Lemma gsim_Call_tgt r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t fn args k :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (Call fn args);; k x)) →
    (gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := bd <- (prog_t fn)?;; x <- (bd args);; ⇓cris (tau;; k x)]> tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof using.
    intros Hi Hk.
    giter_r. rewrite /= Hi; ss. gstep_r. ired.
    replace_r; [|apply Hk].
    do 4 f_equal. destruct (prog_t); ss; grind.
    { do 3 f_equal; grind. rewrite interpV_tau //. }
    { rewrite unfold_iterV /=; rewrite list_lookup_insert /=; grind.
      by apply lookup_lt_is_Some.
    }
  Qed.

  Lemma gsim_Spawn_src r g RR p_s p_t itr_t st_s prog_s tid_s tp_s fn args k :
    tp_s !! tid_s = Some (⇓cris (x <- trigger (Spawn fn args);; k x)) →
    (gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
      (LModTr.interp_stateE Any.t
        (bd <- (prog_s fn)?;;
        iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k (length tp_s))]> tp_s ++ [bd args])) st_s)
      itr_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      itr_t.
  Proof using.
    intros Hi Hk.
    giter_l. rewrite /= Hi; ss. gstep_l. ired.
    replace_l; [|apply Hk].
    do 1 f_equal. grind.
  Qed.

  Lemma gsim_Spawn_tgt r g RR p_s p_t itr_s st_t prog_t tid_t tp_t fn args k :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (Spawn fn args);; k x)) →
    (gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
      (itr_s)
      (LModTr.interp_stateE Any.t
        (bd <- (prog_t fn)?;;
        iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k (length tp_t))]> tp_t ++ [bd args])) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (itr_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof using.
    intros Hi Hk.
    giter_r. rewrite /= Hi; ss. gstep_r. ired.
    replace_r; [|apply Hk].
    do 1 f_equal. grind.
  Qed.

  Lemma gsim_GetTid_src r g RR p_s p_t itr_t st_s prog_s tid_s tp_s k :
    tp_s !! tid_s = Some (⇓cris (x <- trigger GetTid;; k x)) →
    (gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k (tid_s))]> tp_s)) st_s)
      itr_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      itr_t.
  Proof using. intros Hi Hk. giter_l. rewrite /= Hi; ss. gstep_l. by ired. Qed.

  Lemma gsim_GetTid_tgt r g RR p_s p_t itr_s st_t prog_t tid_t tp_t k :
    tp_t !! tid_t = Some (⇓cris (x <- trigger GetTid;; k x)) →
    (gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
      (itr_s)
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k (tid_t))]> tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (itr_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof using. intros Hi Hk. giter_r. rewrite /= Hi; ss. gstep_r. by ired. Qed.

  Lemma gsim_Yield_src r g RR p_s p_t itr_t st_s prog_s tid_s tid_s2 tp_s k :
    tp_s !! tid_s = Some (⇓cris (x <- trigger (Yield tid_s2);; k x)) →
    (gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s)
          (tid_s2, <[tid_s := ⇓cris (k ())]> tp_s)) st_s)
      itr_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      itr_t.
  Proof using. intros Hi Hk. giter_l. rewrite /= Hi; ss. gstep_l. by ired. Qed.

  Lemma gsim_Yield_tgt r g RR p_s p_t itr_s st_t prog_t tid_t tid_t2 tp_t k :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (Yield tid_t2);; k x)) →
    (gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
      (itr_s)
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t)
          (tid_t2, <[tid_t := ⇓cris (k ())]> tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (itr_s)
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof using. intros Hi Hk. giter_r. rewrite /= Hi; ss. gstep_r. by ired. Qed.

  Lemma gsim_SGet_tgt r g RR p_s p_t itr_s st_t prog_t tid_t tp_t key k r_t :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (SGet key);; k x)) →
    map_Forall (const is_Some) st_t →
    (gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
      itr_s
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k (default ()↑ (mjoin (st_t !! key))))]> tp_t))
        (Any.pair (ModTr.state_encode st_t) r_t))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      itr_s
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t))
        (Any.pair (ModTr.state_encode st_t) r_t)).
  Proof using.
    intros Hin ? ?.
    giter_r; rewrite /= Hin; ss. gsteps_r. hss. ired.
    rewrite ModTr.state_encode_decode //.
  Qed.

  Lemma gsim_SGet_src r g RR p_s p_t itr_t st_s prog_s tid_s tp_s key k r_s :
    tp_s !! tid_s = Some (⇓cris (x <- trigger (SGet key);; k x)) →
    map_Forall (const is_Some) st_s →
    (gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k (default ()↑ (mjoin (st_s !! key))))]> tp_s))
        (Any.pair (ModTr.state_encode st_s) r_s))
      itr_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s))
        (Any.pair (ModTr.state_encode st_s) r_s))
      itr_t.
  Proof using.
    intros Hin ? ?.
    giter_l; rewrite /= Hin; ss. gsteps_l. hss. ired.
    rewrite ModTr.state_encode_decode //.
  Qed.

  Lemma gsim_SPut_tgt r g RR p_s p_t itr_s st_t prog_t tid_t tp_t key val k r_t :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (SPut key val);; k x)) →
    map_Forall (const is_Some) st_t →
    (gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
      itr_s
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k ())]> tp_t))
        (Any.pair (ModTr.state_encode (<[key := Some val]> st_t)) r_t))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      itr_s
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t))
        (Any.pair (ModTr.state_encode st_t) r_t)).
  Proof using.
    intros Hin ? ?; eapply lookup_lt_Some in Hin as ?.
    giter_r; rewrite /= Hin; ss. gsteps_r. hss.
    rewrite ModTr.state_encode_decode //.
    giter_r; rewrite /= list_lookup_insert //=. gsteps_r. ired.
    rewrite list_insert_insert //.
  Qed.

  Lemma gsim_SPut_src r g RR p_s p_t itr_t st_s prog_s tid_s tp_s key val k r_s :
    tp_s !! tid_s = Some (⇓cris (x <- trigger (SPut key val);; k x)) →
    map_Forall (const is_Some) st_s →
    (gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k ())]> tp_s))
        (Any.pair (ModTr.state_encode (<[key := Some val]> st_s)) r_s))
      itr_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s))
        (Any.pair (ModTr.state_encode st_s) r_s))
      itr_t.
  Proof using.
    intros Hin ? ?; eapply lookup_lt_Some in Hin as ?.
    giter_l; rewrite /= Hin; ss. gsteps_l. hss.
    rewrite ModTr.state_encode_decode //.
    giter_l; rewrite /= list_lookup_insert //=. gsteps_l. ired.
    rewrite list_insert_insert //.
  Qed.

  Lemma gsim_Assume_src r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t k P r_s :
    tp_s !! tid_s = Some (⇓cris (x <- trigger (Assume P);; k x)) →
    (∀ r_s2,
      ✓ r_s2 ∧ (Own r_s2 ⊢ |==> P ∗ Own r_s) →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := ⇓cris (k ())]> tp_s))
          (Any.pair st_s (r_s2↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (Any.pair st_s (r_s↑)))
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof using.
    intros Hi Hk; pose proof Hi as Hlen; eapply lookup_lt_Some in Hlen.
    giter_l; rewrite /= Hi; ss.
    gsteps_l. hss. ired. hss. ired.
    giter_l. rewrite /= list_lookup_insert //=. gstep_l. intros r_s2.
      gsteps_l. ired. rewrite list_insert_insert.
    giter_l. rewrite /= list_lookup_insert //=. gstep_l. intros Hr_s2.
      gsteps_l. ired. rewrite list_insert_insert.
    giter_l. rewrite /= list_lookup_insert //=. gstep_l.
      gsteps_l. ired. hss. ired. rewrite list_insert_insert.
    giter_l. rewrite /= list_lookup_insert //=. gstep_l.
      gsteps_l. ired. rewrite list_insert_insert.
    eapply Hk; done.
  Qed.

  Lemma gsim_Assume_tgt r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t k P r_t :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (Assume P);; k x)) →
    (∃ r_t2,
      ✓ r_t2 ∧ (Own r_t2 ⊢ |==> P ∗ Own r_t) ∧
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_t)
            (tid_t, <[tid_t := ⇓cris (k ())]> tp_t))
          (Any.pair st_t (r_t2↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (Any.pair st_t (r_t↑))).
  Proof using.
    intros Hin [r_t2 [Hr_t2 Hk]]; pose proof Hin as Hlen; eapply lookup_lt_Some in Hlen.
    giter_r; rewrite /= Hin /=. gstep_r. gsteps_r. hss. ired. hss. ired.
    giter_r. rewrite /= list_lookup_insert //=. gstep_r. exists r_t2.
      gsteps_r. rewrite list_insert_insert //=. ired.
    giter_r. rewrite /= list_lookup_insert //=. gstep_r. unshelve eexists; eauto; ss.
      gsteps_r. rewrite list_insert_insert //=. ired.
    giter_r. rewrite /= list_lookup_insert //=. gsteps_r.
      rewrite list_insert_insert //=. ired. hss. ired.
    giter_r. rewrite /= list_lookup_insert //=. gsteps_r.
      rewrite list_insert_insert //=. ired. eauto.
  Qed.

  Lemma gsim_AssumeRes_src r g RR p_s p_t st_s prog_s tid_s tp_s k r_s r_s2 itr_t :
    tp_s !! tid_s =
      Some (⇓cris (x <- trigger (AssumeRes r_s2);; k x)) →
    (✓ (r_s2 ⋅ r_s) →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := ⇓cris (k ())]> tp_s))
          (Any.pair st_s ((r_s2 ⋅ r_s)↑)))
        itr_t) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (Any.pair st_s (r_s↑)))
      itr_t.
  Proof using.
    intros Hin Hk; pose proof Hin as Hlen; eapply lookup_lt_Some in Hlen.
    giter_l; rewrite /= Hin /=. gstep_l; ss. gnorm_l. hss. ired. hss. ired.
    giter_l; rewrite /= list_lookup_insert //=. gstep_l; ss.
      intros Hval. gnorm_l. gstep_l. gnorm_l. rewrite list_insert_insert.
    giter_l; rewrite /= list_lookup_insert //=. gstep_l; ss.
      gnorm_l. ired. hss. ired. rewrite list_insert_insert.
    giter_l; rewrite /= list_lookup_insert //=. gstep_l; ss.
      gnorm_l. ired. rewrite list_insert_insert.
    eapply Hk; done.
  Qed.

  Lemma gsim_AssumeRes_tgt r g RR p_s p_t st_t prog_s tid_t tp_t k r_t r_t2 itr_s :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (AssumeRes r_t2);; k x)) →
    (✓ (r_t2 ⋅ r_t) ∧
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
        itr_s
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_t, <[tid_t := ⇓cris (k ())]> tp_t))
          (Any.pair st_t ((r_t2 ⋅ r_t)↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      itr_s
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_t, tp_t)) (Any.pair st_t (r_t↑))).
  Proof using.
    intros Hin [Hval Hk]; pose proof Hin as Hlen; eapply lookup_lt_Some in Hlen.
    giter_r; rewrite /= Hin /=. gstep_r; ss. gnorm_r. hss. ired. hss. ired.
    giter_r; rewrite /= list_lookup_insert //=.
      gstep_r; ss. exists Hval. gsteps_r. rewrite list_insert_insert. ired.
    giter_r; rewrite /= list_lookup_insert //=.
      gsteps_r; ss. rewrite list_insert_insert. ired. hss. ired.
    giter_r; rewrite /= list_lookup_insert //=.
      gsteps_r; ss. rewrite list_insert_insert. ired.
    eapply Hk; done.
  Qed.

  Lemma gsim_Guarantee_src r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t k P r_s :
    tp_s !! tid_s = Some (⇓cris (x <- trigger (Guarantee P);; k x)) →
    (∃ r_s2,
      ✓ r_s2 ∧ (Own r_s ⊢ |==> P ∗ Own r_s2) ∧
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := ⇓cris (k ())]> tp_s))
          (Any.pair st_s (r_s2↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (Any.pair st_s (r_s↑)))
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof using.
    intros Hi [r_s2 Hk]; pose proof Hi as Hlen; eapply lookup_lt_Some in Hlen.
    giter_l; rewrite /= Hi; ss.
    gsteps_l. hss. ired. hss. ired.
    giter_l. rewrite /= list_lookup_insert //=. gstep_l. exists r_s2.
      gsteps_l. ired. rewrite list_insert_insert.
    giter_l. rewrite /= list_lookup_insert //=. gstep_l. unshelve eexists; eauto.
      gsteps_l. ired. rewrite list_insert_insert.
    giter_l. rewrite /= list_lookup_insert //=. gstep_l.
      gsteps_l. ired. hss. ired. rewrite list_insert_insert.
    giter_l. rewrite /= list_lookup_insert //=. gstep_l.
      gsteps_l. ired. rewrite list_insert_insert.
    eauto.
  Qed.

  Lemma gsim_Guarantee_tgt r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t k P r_t :
    tp_t !! tid_t = Some (⇓cris (x <- trigger (Guarantee P);; k x)) →
    (∀ r_t2,
      ✓ r_t2 ∧ (Own r_t ⊢ |==> P ∗ Own r_t2) →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_t)
            (tid_t, <[tid_t := ⇓cris (k ())]> tp_t))
          (Any.pair st_t (r_t2↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (Any.pair st_t (r_t↑))).
  Proof using.
    intros Hin ?; pose proof Hin as Hlen; eapply lookup_lt_Some in Hlen.
    giter_r; rewrite /= Hin /=. gstep_r. gsteps_r. hss. ired. hss. ired.
    giter_r. rewrite /= list_lookup_insert //=. gstep_r. intros ?.
      gsteps_r. rewrite list_insert_insert //=. ired.
    giter_r. rewrite /= list_lookup_insert //=. gstep_r. i.
      gsteps_r. rewrite list_insert_insert //=. ired.
    giter_r. rewrite /= list_lookup_insert //=. gsteps_r.
      rewrite list_insert_insert //=. ired. hss. ired.
    giter_r. rewrite /= list_lookup_insert //=. gsteps_r.
      rewrite list_insert_insert //=. ired.
    eauto.
  Qed.

  (* HoareCall Lemmas *)
  Definition fspec_option_meta (fspo : option fspec) : Type :=
    match fspo with
    | Some fsp => meta fsp
    | None => unit
    end.

  Definition HoareCall_prologue fspo (varg : Any.t) N stid
      : itree crisE (fspec_option_meta fspo * Any.t) :=
    (match fspo as fspo return itree crisE (fspec_option_meta fspo * Any.t) with
    | Some (fspec_mk pre post) =>
        x <- trigger (Choose _);;
        arg <- trigger (Choose Any.t);;
        trigger (Guarantee (pre (N, stid) x varg arg));;;
        Ret (x, arg)
    | None => Ret (tt, varg)
    end).

  Definition HoareCall_epilogue fspo (x : fspec_option_meta fspo) (pret : Any.t) N stid
      : itree crisE Any.t :=
    (match fspo as fspo return fspec_option_meta fspo → itree crisE Any.t with
    | Some (fspec_mk pre post) =>
        λ x,
          vret <- trigger (Take Any.t);;
          trigger (Assume (post (N, stid) x vret pret));;;
          Ret vret
    | None => λ _, Ret pret
    end) x.

  Lemma HoareCall_unfold (sp : specmap) (fn : string) N stid :
    SModTr.HoareCall (sp !! speckey_fn fn) fn ()↑ N stid =
    xarg <- HoareCall_prologue (sp !! speckey_fn fn) (()↑) N stid;;
    ret <- trigger (Call fn xarg.2);;
    HoareCall_epilogue (sp !! speckey_fn fn) xarg.1 ret N stid.
  Proof using.
    rewrite /SModTr.HoareCall /HoareCall_prologue /HoareCall_epilogue; case_match; grind.
  Qed.

  Lemma gsim_HoareCall_prologue_both r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      scp fsp k_s k_t (res : Σ) arg N stid :
    tp_s !! tid_s =
      Some (⇓cris (x <- ⇓sb(msk_scp scp msk_true) (HoareCall_prologue fsp arg N stid);; k_s x)) →
    tp_t !! tid_t =
      Some (⇓cris (x <- ⇓sb(msk_scp scp msk_true) (HoareCall_prologue fsp arg N stid);; k_t x)) →
    ✓ res →
    (∀ (res1 : Σ) x, ✓ res1 →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k_s x)]> tp_s))
          (Any.pair st_s (res1↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k_t x)]> tp_t))
          (Any.pair st_t (res1↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (Any.pair st_s (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (Any.pair st_t (res↑))).
  Proof using.
    rewrite /HoareCall_prologue.
    intros Hin_s Hin_t Hres Hk.
    eapply lookup_lt_Some in Hin_s as ?.
    eapply lookup_lt_Some in Hin_t as ?.
    destruct fsp as [[meta pre post] | ]; cycle 1.
    { revert Hin_s; gnorm_itr; i; revert Hin_t; gnorm_itr; i.
      specialize (Hk res ((), arg) Hres); revert Hk; rewrite ?list_insert_id //=.
    }
    eapply gsim_Choose_tgt; [rewrite Hin_t; do 2 f_equal; hnorm_itr|]. intros x.
    eapply gsim_Choose_tgt; [lookup_tac; do 2 f_equal; hnorm_itr|].
      intros varg. rewrite list_insert_insert. gnorm_r.
    eapply gsim_Guarantee_tgt; [lookup_tac; do 2 f_equal; hnorm_itr|].
      intros res2 Hres2. rewrite list_insert_insert. ghnorm_r.
    eapply gsim_Choose_src; [rewrite Hin_s; do 2 f_equal; hnorm_itr|]. exists x.
    eapply gsim_Choose_src; [lookup_tac; do 2 f_equal; hnorm_itr|].
      exists varg. rewrite list_insert_insert. ghnorm_l.
    eapply gsim_Guarantee_src; [lookup_tac; do 2 f_equal; hnorm_itr|].
      exists res2; splits; try by des. rewrite list_insert_insert. ghnorm_l.
    eapply gsim_flag; last eapply (Hk res2 (x, varg)).
    { destruct p_s as [[|]|]; rr; ss; eauto. }
    { destruct p_t as [[|]|]; rr; ss; eauto. }
    by des.
  Qed.

  Lemma gsim_HoareCall_epilogue_both r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      scp fsp k_s k_t (res : Σ) x arg N stid :
    tp_s !! tid_s =
      Some (⇓cris (x <- ⇓sb(msk_scp scp msk_true) (HoareCall_epilogue fsp x arg N stid);; k_s x)) →
    tp_t !! tid_t =
      Some (⇓cris (x <- ⇓sb(msk_scp scp msk_true) (HoareCall_epilogue fsp x arg N stid);; k_t x)) →
    ✓ res →
    (∀ (res1 : Σ) x, ✓ res1 →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := ⇓cris (k_s x)]> tp_s))
          (Any.pair st_s (res1↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := ⇓cris (k_t x)]> tp_t))
          (Any.pair st_t (res1↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (Any.pair st_s (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (Any.pair st_t (res↑))).
  Proof using.
    rewrite /HoareCall_epilogue.
    intros Hin_s Hin_t Hres Hk.
    eapply lookup_lt_Some in Hin_s as ?.
    eapply lookup_lt_Some in Hin_t as ?.
    destruct fsp as [[meta pre post] | ]; cycle 1.
    { revert Hin_s; gnorm_itr; i; revert Hin_t; gnorm_itr; i.
      specialize (Hk res (arg) Hres); revert Hk; rewrite ?list_insert_id //=.
    }
    eapply gsim_Take_src; [rewrite Hin_s; do 2 f_equal; hnorm_itr|]. intros varg.
    eapply gsim_Take_tgt; [rewrite Hin_t; do 2 f_equal; hnorm_itr|]. exists varg.
    eapply gsim_Assume_src; [lookup_tac; do 2 f_equal; hnorm_itr|].
      intros res2 Hres2. rewrite list_insert_insert. gnorm_l.
    eapply gsim_Assume_tgt; [lookup_tac; do 2 f_equal; hnorm_itr|].
      exists res2; splits; try by des. rewrite list_insert_insert. ghnorm_l; ghnorm_r.
    eapply gsim_flag; last eapply (Hk res2 (varg)).
    { destruct p_s as [[|]|]; rr; ss; eauto. }
    { destruct p_t as [[|]|]; rr; ss; eauto. }
    by des.
  Qed.

  Lemma gsim_jobs_both {retID} r g RR st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      sp N stid k_s k_t (res : Σ) job mn :
    tid_s < length tp_s →
    tid_t < length tp_t →
    ✓ res →
    (∀ (res1 : Σ) (ret : retID), ✓ res1 →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_bot smj_bot
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s :=
            ⇓cris (k_s ret)]> tp_s))
          (Any.pair st_s (res1↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t :=
            ⇓cris (k_t ret)]> tp_t))
          (Any.pair st_t (res1↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_bot smj_bot
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s,
        <[tid_s :=
          ⇓cris (x <- ⇓sb(msk_scp (HelpingOn.scopes mn) msk_true) (⇓smod(sp, N, stid) (⇓sb(HelpingOn.msk_pure) job));; k_s x)]>
        tp_s)) (Any.pair st_s (res↑)))
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t,
        <[tid_t :=
          ⇓cris (x <- ⇓sb(msk_scp (HelpingOff.scopes mn) msk_true) (⇓smod(HelpingOn.sp mn sp, N, stid) (⇓sb(HelpingOn.msk_pure) job));; k_t x)]>
        tp_t)) (Any.pair st_t (res↑))).
  Proof using.
    intros Hlen_s Hlen_t Hres Hk.
    revert Hres Hk; generalize job res. clear job res.
    gcofix CIH.
    intros job res Hres Hk.
    ides job.
    { ghnorm_l; ghnorm_r.
      eapply gpaco7_mon; eauto.
    }
    {
      eapply gsim_tau_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      rewrite list_insert_insert.
      eapply gsim_tau_tgt; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      rewrite list_insert_insert.
      zprogress with smj_bot smj_bot _ _. gbase. eauto.
    }
    destruct e as [e|e]; rewrite !vis_trigger.
    { destruct e as [P|res1|P].
      { eapply gsim_Assume_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
        intros res1 Hres1; rewrite list_insert_insert.
        eapply gsim_Assume_tgt; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
        exists res1; splits; (try by des); rewrite list_insert_insert.
        ghnorm_l; ghnorm_r.
        zprogress with smj_bot smj_bot _ _. gbase. eapply CIH; try by des.
      }
      { eapply gsim_AssumeRes_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
        intros ?; rewrite list_insert_insert.
        eapply gsim_AssumeRes_tgt; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
        splits; (try by des); rewrite list_insert_insert.
        ghnorm_l; ghnorm_r.
        zprogress with smj_bot smj_bot _ _. gbase. eapply CIH; try by des.
      }
      { eapply gsim_Guarantee_tgt; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
        intros res1 Hres1; rewrite list_insert_insert.
        eapply gsim_Guarantee_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
        exists res1; splits; (try by des); rewrite list_insert_insert.
        ghnorm_l; ghnorm_r.
        zprogress with smj_bot smj_bot _ _. gbase. eapply CIH; try by des.
      }
    }
    destruct e as [e|e].
    { ghnorm_l. ghnorm_l.
      eapply gsim_Take_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      ss.
    }
    destruct e as [e|e].
    { ghnorm_l. ghnorm_l.
      eapply gsim_Take_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      ss.
    }
    destruct e as [X|X|I O fn args]; rewrite -!subevent_right !subevent_subevent.
    { eapply gsim_Choose_tgt; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      intros x; rewrite list_insert_insert.
      eapply gsim_Choose_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      exists x; rewrite list_insert_insert.
      ghnorm_l; ghnorm_r.
      zprogress with smj_bot smj_bot _ _. gbase. eapply CIH; try by des.
    }
    { eapply gsim_Take_src; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      intros x; rewrite list_insert_insert.
      eapply gsim_Take_tgt; [rewrite list_lookup_insert //; do 2 f_equal; hnorm_itr|].
      exists x; rewrite list_insert_insert.
      ghnorm_l; ghnorm_r.
      zprogress with smj_bot smj_bot _ _. gbase. eapply CIH; try by des.
    }
    { giter_l; giter_r.
      rewrite /= ?list_lookup_insert //=. gnorm_l; gnorm_r.
      gstep_l. instantiate (1:=smj_top).
      intros ? ? <-. gsteps_l; gsteps_r. rewrite ?list_insert_insert. ired.
      zprogress with smj_bot smj_bot _ _. gbase. eapply CIH; try by des.
    }
  Qed.
  (* Lemma gsim_Guarantee_src r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c k (k_2 : Any.t → _) r_s P :
    tp_s !! tid_s =
      Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (trigger (Guarantee P);;; k));; k_2 x) →
    (∃ r_s2, (✓ r_s2 ∧ (Own r_s ⊢ |==> P ∗ Own r_s2)) ∧
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_top p_t
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_s)
            (tid_s, <[tid_s := x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) k);; k_2 x]> tp_s))
          (Any.pair st_s (r_s2↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t)) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (Any.pair st_s (r_s↑)))
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) st_t).
  Proof using.
    intros Hin [r_s2 [Hr_s2 Hk]]; pose proof Hin as Hlen; eapply lookup_lt_Some in Hlen.
    iter_l; rewrite Hin; ss.
    step_l; ss. gnorm_l. hss. ired. hss. ired.
    iter_l. rewrite list_lookup_insert //=. step_l. exists r_s2. step_l. gnorm_l.
    rewrite list_insert_insert //=. ired.
    iter_l. rewrite list_lookup_insert //=. step_l. unshelve eexists; eauto. step_l. gnorm_l.
    rewrite list_insert_insert //=. ired.
    iter_l. rewrite list_lookup_insert //=. step_l. gnorm_l.
    rewrite list_insert_insert //=. ired. hss. ired.
    iter_l. rewrite list_lookup_insert //=. step_l. gnorm_l.
    rewrite list_insert_insert //=. ired.
    eapply Hk; done.
  Qed.

  Lemma gsim_Guarantee_tgt r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c k (k_2 : Any.t → _) r_t P :
    tp_t !! tid_t =
      Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (trigger (Guarantee P);;; k));; k_2 x) →
    (∀ r_t2, (✓ r_t2 ∧ (Own r_t ⊢ |==> P ∗ Own r_t2)) →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s smj_top
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
        (LModTr.interp_stateE Any.t
          (iterV (LModTr.handle_callE prog_t)
            (tid_t, <[tid_t := x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) k);; k_2 x]> tp_t))
          (Any.pair st_t (r_t2↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) st_s)
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t))
        (Any.pair st_t (r_t↑))).
  Proof using.
    intros Hin Hk; pose proof Hin as Hlen; eapply lookup_lt_Some in Hlen.
    iter_r; rewrite Hin; ss.
    step_r; ss. gnorm_r. hss. ired. hss. ired.
    iter_r. rewrite list_lookup_insert //=. step_r. intros r_t2. gnorm_r. step_r. gnorm_r.
    rewrite list_insert_insert //=. ired.
    iter_r. rewrite list_lookup_insert //=. step_r. intros Hr_t2. step_r. gnorm_r.
    rewrite list_insert_insert //=. ired.
    iter_r. rewrite list_lookup_insert //=. step_r. gnorm_r.
    rewrite list_insert_insert //=. ired. hss. ired.
    iter_r. rewrite list_lookup_insert //=. step_r. gnorm_r.
    rewrite list_insert_insert //=. ired.
    apply Hk; done.
  Qed. *)

  (* Context (sp : sp_type).

  Lemma HoareCall_prologue_sred img_c fsp arg :
    ⇓smod(img_c, sp) (HoareCall_prologue fsp arg) = HoareCall_prologue fsp arg.
  Proof using.
    rewrite /HoareCall_prologue; unseal "Help"; destruct fsp as [[fsp | fsp] |].
    { repeat (rewrite interpV_bind interpV_trigger /=; grind).
      rewrite interpV_ret //.
    }
    { rewrite /triggerNB /= interpV_bind interpV_trigger /=; grind. }
    { rewrite interpV_ret //. }
  Qed.

  Lemma HoareCall_epilogue_sred img_c fsp arg x :
    ⇓smod(img_c, sp) (HoareCall_epilogue fsp x arg) = HoareCall_epilogue fsp x arg.
  Proof using.
    rewrite /HoareCall_epilogue; unseal "Help"; destruct fsp as [[fsp | fsp] |].
    { repeat (rewrite interpV_bind interpV_trigger /=; grind).
      rewrite interpV_ret //.
    }
    { rewrite /triggerNB /= interpV_bind interpV_trigger /=; grind. }
    { rewrite interpV_ret //. }
  Qed.

  Lemma HoareFun_prologue_sred img_c fsp arg :
    ⇓smod(img_c, sp) (HoareFun_prologue fsp arg) = HoareFun_prologue fsp arg.
  Proof using.
    rewrite /HoareFun_prologue; unseal "Help"; destruct fsp as [[fsp | fsp] |].
    { repeat (rewrite interpV_bind interpV_trigger /=; grind).
      rewrite interpV_ret //.
    }
    { rewrite /triggerNB /= interpV_bind interpV_trigger /=; grind. }
    { rewrite interpV_ret //. }
  Qed.

  Lemma HoareFun_epilogue_sred img_c fsp arg x :
    ⇓smod(img_c, sp) (HoareFun_epilogue fsp x arg) = HoareFun_epilogue fsp x arg.
  Proof using.
    rewrite /HoareFun_epilogue; unseal "Help"; destruct fsp as [[fsp | fsp] |].
    { repeat (rewrite interpV_bind interpV_trigger /=; grind).
      rewrite interpV_ret //.
    }
    { rewrite /triggerNB /= interpV_bind interpV_trigger /=; grind. }
    { rewrite interpV_ret //. }
  Qed.

  Lemma gsim_HoareCall_prologue_both r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c fsp k_s k_t (k_s1 k_t1 : Any.t → itree _ Any.t) (res : Σ) arg :
    tp_s !! tid_s =
      Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (x <- HoareCall_prologue fsp arg;; k_s x));; k_s1 x) →
    tp_t !! tid_t =
      Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (x <- HoareCall_prologue fsp arg;; k_t x));; k_t1 x) →
    ✓ res →
    (∀ (res1 : Σ) x, ✓ res1 →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (k_s x));; k_s1 x]> tp_s))
          (Any.pair st_s (res1↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (k_t x));; k_t1 x]> tp_t))
          (Any.pair st_t (res1↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (Any.pair st_s (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (Any.pair st_t (res↑))).
  Proof using.
    intros Hin_s Hin_t Hres Hk.
    pose proof Hin_s as Hlen_s; eapply lookup_lt_Some in Hlen_s.
    pose proof Hin_t as Hlen_t; eapply lookup_lt_Some in Hlen_t.
    destruct fsp as [[fsp | fsp] | ]; cycle 1.
    { iter_l; iter_r; rewrite Hin_s Hin_t /HoareCall_prologue; unseal "Help". ss. step_r; ss. }
    { revert Hin_s Hin_t; rewrite /HoareCall_prologue; unseal "Help"; ired.
      intros Hin_s Hin_t.
      specialize (Hk res ((), arg) Hres); revert Hk; rewrite ?list_insert_id //=.
    }
    { iter_l; iter_r; rewrite Hin_s Hin_t /HoareCall_prologue; unseal "Help". ss.
      step_r; intros fsp2; step_l; exists fsp2. step_l; step_r. gnorm_l; gnorm_r. ired.
      eapply gsim_Choose_tgt; [rewrite list_lookup_insert; grind|]. intros varg.
      rewrite list_insert_insert.
      eapply gsim_Choose_src; [rewrite list_lookup_insert; grind|]. exists varg.
      rewrite list_insert_insert. ired.
      eapply gsim_Guarantee_tgt; [rewrite list_lookup_insert; grind|]. intros r_t2 Hr_t2.
      rewrite list_insert_insert.
      eapply gsim_Guarantee_src; [rewrite list_lookup_insert; grind|]. exists r_t2; split; ss.
      rewrite list_insert_insert. ired.
      guclo flagC_spec; econs; last eapply (Hk r_t2 (fsp2, varg)).
      { destruct p_s as [[|]|]; rr; ss; eauto. }
      { destruct p_t as [[|]|]; rr; ss; eauto. }
      by des.
    }
  Qed.

  Lemma gsim_HoareCall_epilogue_both r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c msk_c scp_c fsp k_s k_t (k_s1 k_t1 : Any.t → itree _ Any.t) (res : Σ) arg x :
    tp_s !! tid_s =
      Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (x <- HoareCall_epilogue fsp arg x;; k_s x));;
        k_s1 x) →
    tp_t !! tid_t =
      Some (x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (x <- HoareCall_epilogue fsp arg x;; k_t x));;
        k_t1 x) →
    ✓ res →
    (∀ (res1 : Σ) x, ✓ res1 →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (k_s x));; k_s1 x]> tp_s))
          (Any.pair st_s (res1↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (k_t x));; k_t1 x]> tp_t))
          (Any.pair st_t (res1↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (Any.pair st_s (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (Any.pair st_t (res↑))).
  Proof using.
    intros Hin_s Hin_t Hres Hk.
    pose proof Hin_s as Hlen_s; eapply lookup_lt_Some in Hlen_s.
    pose proof Hin_t as Hlen_t; eapply lookup_lt_Some in Hlen_t.
    destruct fsp as [[fsp | fsp] | ]; cycle 1.
    { iter_l; iter_r; rewrite Hin_s Hin_t /HoareCall_epilogue; unseal "Help". ss. step_r; ss. }
    { revert Hin_s Hin_t; rewrite /HoareCall_epilogue; unseal "Help"; ired.
      intros Hin_s Hin_t.
      specialize (Hk res x Hres); revert Hk; rewrite ?list_insert_id //=.
    }
    { revert Hin_s Hin_t; rewrite /HoareCall_epilogue; unseal "Help"; ired.
      intros Hin_s Hin_t.
      eapply gsim_Take_src; [rewrite Hin_s //|intros y ?].
      eapply gsim_Take_tgt; [rewrite Hin_t //|eexists y; eauto].
      split; first done. ired.
      eapply gsim_Assume_src; [rewrite list_lookup_insert //|].
      intros res2 -> Hres2.
      eapply gsim_Assume_tgt; [rewrite list_lookup_insert //|].
      exists res2; splits; try by des.
      rewrite ?list_insert_insert.
      guclo flagC_spec; econs; last eapply (Hk res2).
      { destruct p_s as [[|]|]; rr; ss; eauto. }
      { destruct p_t as [[|]|]; rr; ss; eauto. }
      by des.
    }
  Qed.

  Lemma gsim_HoareCall_epilogue_HoareFun_prologue
      r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      msk_c scp_c fsp k_s k_t (k_s1 k_t1 : Any.t → itree _ Any.t) (res : Σ) pret x :
    tp_s !! tid_s =
      Some (x <- ⇓cris (⇓sb(true, msk_c, scp_c) (x <- HoareCall_epilogue fsp x pret;; k_s x));;
        k_s1 x) →
    tp_t !! tid_t =
      Some (x <- ⇓cris (⇓sb(true, msk_c, scp_c) (x <- HoareFun_prologue fsp pret;; k_t x));;
        k_t1 x) →
    ✓ res →
    (∀ (res1 : Σ) ret, ✓ res1 →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := x <- ⇓cris (⇓sb(true, msk_c, scp_c) (k_s ret));; k_s1 x]> tp_s))
          (Any.pair st_s (res1↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := x <- ⇓cris (⇓sb(true, msk_c, scp_c) (k_t (x, ret)));; k_t1 x]> tp_t))
          (Any.pair st_t (res1↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (Any.pair st_s (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (Any.pair st_t (res↑))).
  Proof using.
    intros Hin_s Hin_t Hres Hk.
    pose proof Hin_s as Hlen_s; eapply lookup_lt_Some in Hlen_s.
    pose proof Hin_t as Hlen_t; eapply lookup_lt_Some in Hlen_t.
    destruct fsp as [[fsp | fsp] | ]; cycle 1.
    { iter_l; iter_r; rewrite Hin_s Hin_t /HoareCall_epilogue /HoareFun_prologue; unseal "Help".
      ss. step_r; ss.
    }
    { revert Hin_s Hin_t; rewrite /HoareCall_epilogue /HoareFun_prologue; unseal "Help"; ired.
      intros Hin_s Hin_t. destruct x.
      specialize (Hk res pret Hres); revert Hk; rewrite ?list_insert_id //=.
    }
    { iter_l; iter_r; rewrite Hin_s Hin_t /HoareCall_epilogue /HoareFun_prologue; unseal "Help".
      ss.
      step_l. intros varg. gnorm_l. step_l. gnorm_l. ired.
      step_r. exists x. gnorm_r. step_r. gnorm_r. ired.
      eapply gsim_Take_tgt; [rewrite list_lookup_insert //|exists varg; split; first eauto].
      rewrite list_insert_insert.

      eapply gsim_Assume_src; [rewrite list_lookup_insert //|].
      intros r_s2 _ Hr_s2. rewrite list_insert_insert. ired.
      eapply gsim_Assume_tgt; [rewrite list_lookup_insert //|].
      exists r_s2; esplits; try by (des; eauto). rewrite list_insert_insert.
      
      guclo flagC_spec; econs.
      { instantiate (1:=p_s). destruct p_s as [[|]|]; rr; ss; eauto. }
      { instantiate (1:=p_t). destruct p_t as [[|]|]; rr; ss; eauto. }
      eapply Hk; by des.
    }
  Qed.

  Lemma gsim_HoareCall_prologue_HoareFun_epilogue
      r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      msk_c scp_c fsp k_s k_t (k_s1 k_t1 : Any.t → itree _ Any.t) (res : Σ) pret x :
    tp_s !! tid_s =
      Some (x <- ⇓cris (⇓sb(true, msk_c, scp_c) (x <- HoareCall_prologue fsp pret;; k_s x));;
        k_s1 x) →
    tp_t !! tid_t =
      Some (x <- ⇓cris (⇓sb(true, msk_c, scp_c) (x <- HoareFun_epilogue fsp x pret;; k_t x));;
        k_t1 x) →
    ✓ res →
    (∀ (res1 : Σ) ret, ✓ res1 →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := x <- ⇓cris (⇓sb(true, msk_c, scp_c) (k_s (x, ret)));; k_s1 x]> tp_s))
          (Any.pair st_s (res1↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := x <- ⇓cris (⇓sb(true, msk_c, scp_c) (k_t ret));; k_t1 x]> tp_t))
          (Any.pair st_t (res1↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_s) (tid_s, tp_s)) (Any.pair st_s (res↑)))
      (LModTr.interp_stateE Any.t
        (iterV (LModTr.handle_callE prog_t) (tid_t, tp_t)) (Any.pair st_t (res↑))).
  Proof using.
    intros Hin_s Hin_t Hres Hk.
    pose proof Hin_s as Hlen_s; eapply lookup_lt_Some in Hlen_s.
    pose proof Hin_t as Hlen_t; eapply lookup_lt_Some in Hlen_t.
    destruct fsp as [[fsp | fsp] | ]; cycle 1.
    { iter_l; iter_r; rewrite Hin_s Hin_t /HoareCall_prologue /HoareFun_epilogue; unseal "Help".
      ss. step_r; ss.
    }
    { revert Hin_s Hin_t; rewrite /HoareCall_prologue /HoareFun_epilogue; unseal "Help"; ired.
      intros Hin_s Hin_t. destruct x.
      specialize (Hk res pret Hres); revert Hk; rewrite ?list_insert_id //=.
    }
    { iter_l; iter_r; rewrite Hin_s Hin_t /HoareCall_prologue /HoareFun_epilogue; unseal "Help".
      ss.
      step_r. intros vret. gnorm_r. step_r. gnorm_r. ired.
      step_l. exists x. gnorm_l. step_l. gnorm_l. ired.
      eapply gsim_Choose_src; [rewrite list_lookup_insert //|exists vret; split; first eauto].
      rewrite list_insert_insert.

      eapply gsim_Guarantee_tgt; [rewrite list_lookup_insert //|].
      intros r_t2 Hr_t2. rewrite list_insert_insert. ired.
      eapply gsim_Guarantee_src; [rewrite list_lookup_insert //|].
      exists r_t2; esplits; try by (des; eauto). rewrite list_insert_insert.
      
      guclo flagC_spec; econs.
      { instantiate (1:=p_s). destruct p_s as [[|]|]; rr; ss; eauto. }
      { instantiate (1:=p_t). destruct p_t as [[|]|]; rr; ss; eauto. }
      eapply Hk; by des.
    }
  Qed.

  Lemma gsim_jobs_both {retID} r g RR p_s p_t st_s st_t prog_s prog_t tid_s tid_t tp_s tp_t
      img_c img_c' msk_c scp_c k_s k_t (k_s1 k_t1 : Any.t → itree _ Any.t) (res : Σ) job :
    tid_s < length tp_s →
    tid_t < length tp_t →
    ✓ res →
    (∀ (res1 : Σ) (ret : retID), ✓ res1 →
      gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR smj_bot smj_bot
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s)
          (tid_s, <[tid_s := x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c', sp) (k_s ret)));; k_s1 x]> tp_s))
          (Any.pair st_s (res1↑)))
        (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t)
          (tid_t, <[tid_t := x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c', sp) (k_t ret)));; k_t1 x]> tp_t))
          (Any.pair st_t (res1↑)))) →
    gpaco7 _gsim (cpn7 _gsim) r g (Any.t * Any.t)%type (Any.t * Any.t)%type RR p_s p_t
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_s) (tid_s,
        <[tid_s :=
          x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c', sp) (x <- Helping.trans job;; k_s x)));; k_s1 x]>
        tp_s)) (Any.pair st_s (res↑)))
      (LModTr.interp_stateE Any.t (iterV (LModTr.handle_callE prog_t) (tid_t,
        <[tid_t :=
          x <- ⇓cris (⇓sb(img_c, msk_c, scp_c) (⇓smod(img_c', sp) (x <- Helping.trans job;; k_t x)));; k_t1 x]>
        tp_t)) (Any.pair st_t (res↑))).
  Proof using.
    intros Hlen_s Hlen_t Hres Hk.
    apply gsim_flag.
    revert Hres; generalize job res. clear job res.
    gcofix CIH.
    intros job res Hres.
    ides job.
    {
      rewrite /Helping.trans (bisim_is_eq (translate_ret _ _)); grind.
      eapply gpaco7_mon; eauto.
    }
    {
      rewrite /Helping.trans (bisim_is_eq (translate_tau _ _)); fold (Helping.trans t).
      ired.
      eapply gsim_tau_src; [rewrite list_lookup_insert //|rewrite list_insert_insert].
      { rewrite interpV_tau //. }
      eapply gsim_tau_tgt; [rewrite list_lookup_insert //|rewrite list_insert_insert].
      { rewrite interpV_tau //. }
      zprogress.
      apply gsim_flag.
      gbase. eapply CIH; eauto using list_lookup_insert.
    }
    { (* agE *)
      destruct e as [|].
      { destruct a as [P | res2 | P].
        { rewrite /Helping.trans (bisim_is_eq (translate_vis _ _ _ _)). ired.
          eapply gsim_Assume_src; [rewrite list_lookup_insert //=|rewrite list_insert_insert].
          { instantiate (1:=k_s1). rewrite vis_bind interpV_vis.
            repeat f_equal; grind. extensionalities a; destruct a. grind.
          }
          intros r_s2 -> Hr_s2.
          eapply gsim_Assume_tgt; [rewrite list_lookup_insert //=|rewrite list_insert_insert].
          { instantiate (1:=k_t1). rewrite vis_bind interpV_vis.
            repeat f_equal; grind. extensionalities a; destruct a. grind.
          }
          exists r_s2; esplits; try by des.
          zprogress.
          apply gsim_flag.
          gbase. eapply CIH; eauto using list_lookup_insert.
          by des.
        }
        { rewrite /Helping.trans (bisim_is_eq (translate_vis _ _ _ _)). ired.
          eapply gsim_AssumeRes_src; [rewrite list_lookup_insert //=|rewrite list_insert_insert].
          { instantiate (1:=k_s1). rewrite vis_bind interpV_vis.
            repeat f_equal; grind. extensionalities a; destruct a. grind.
          }
          intros Hres2.
          eapply gsim_AssumeRes_tgt; [rewrite list_lookup_insert //=|rewrite list_insert_insert].
          { instantiate (1:=k_t1). rewrite vis_bind interpV_vis.
            repeat f_equal; grind. extensionalities a; destruct a. grind.
          }
          split; first done.
          zprogress.
          apply gsim_flag.
          gbase. eapply CIH; eauto using list_lookup_insert.
        }
        { rewrite /Helping.trans (bisim_is_eq (translate_vis _ _ _ _)). ired.
          eapply gsim_Guarantee_tgt; [rewrite list_lookup_insert //=|rewrite list_insert_insert].
          { instantiate (1:=k_t1). rewrite vis_bind interpV_vis.
            repeat f_equal; grind. extensionalities a; destruct a. grind.
          }
          intros r_t2 Hr_t2.
          eapply gsim_Guarantee_src; [rewrite list_lookup_insert //=|rewrite list_insert_insert].
          { instantiate (1:=k_s1). rewrite vis_bind interpV_vis.
            repeat f_equal; grind. extensionalities a; destruct a. grind.
          }
          exists r_t2; split; first done.
          zprogress.
          apply gsim_flag.
          gbase. eapply CIH; eauto using list_lookup_insert.
          by des.
        }
      }
      { (* coreE *)
        destruct c as [X | X | fn args].
        { rewrite /Helping.trans (bisim_is_eq (translate_vis _ _ _ _)). ired.
          eapply gsim_Choose_tgt;
            [rewrite list_lookup_insert //=|intros x; rewrite list_insert_insert].
          { instantiate (1:=k_t1). rewrite vis_bind interpV_vis; repeat f_equal; grind. }
          eapply gsim_Choose_src;
            [rewrite list_lookup_insert //=|exists x; rewrite list_insert_insert].
          { instantiate (1:=k_s1). rewrite vis_bind interpV_vis; repeat f_equal; grind. }
          zprogress.
          apply gsim_flag.
          gbase. eapply CIH; eauto using list_lookup_insert.
        }
        { rewrite /Helping.trans (bisim_is_eq (translate_vis _ _ _ _)). ired.
          eapply gsim_Take_src;
            [rewrite list_lookup_insert //=|intros x; rewrite list_insert_insert].
          { instantiate (1:=k_s1). rewrite vis_bind interpV_vis; repeat f_equal; grind. }
          intros Himg.
          eapply gsim_Take_tgt;
            [rewrite list_lookup_insert //=|exists x; rewrite list_insert_insert].
          { instantiate (1:=k_t1). rewrite vis_bind interpV_vis; repeat f_equal; grind. }
          split; first done. zprogress.
          apply gsim_flag.
          gbase. eapply CIH; eauto using list_lookup_insert.
        }
        { iter_l. rewrite list_lookup_insert //=.
          iter_r. rewrite list_lookup_insert //=.
          gnorm_l; gnorm_r.
          guclo gsim_indC_spec; econs; instantiate (1:=smj_top).
          intros ?? ->.
          step_l; step_r. gnorm_l; gnorm_r. rewrite ?list_insert_insert. ired.
          zprogress.
          apply gsim_flag.
          gbase. eapply CIH; eauto using list_lookup_insert.
        }
      }
    }
  Unshelve. exact smj_top.
  Qed. *)
End props.
