Require Import Common.
From iris.proofmode Require Import proofmode.
Require Import SModTr HModTr ModTr SMod HMod Mod.
Require Import ITactics TacticsCommon SimGlobal SimGlobalFacts CtxRefine ClosedAdequacy.
Require Import HModInline HModInlineIntro HModInlineElim ElimRel.
Require Import SimGlobal SimGTactics.

Lemma cancel_spawn `{Σ: GRA} md sp fn args:
  CANCEL_GOAL md sp (NativeSpawnE fn args) (HoareSpawnE fn args (sp fn)).
Proof.
  r; i. assert (VP0:=VP). destruct VP0 as [VP1 VP2]. r in VP1.
  rewrite /sp_from /to_sp in VP1. setoid_rewrite alist_find_map_snd in VP1.
  ziter_l. ziter_r. rewrite x0 x1. s. zstep_l.
  rewrite !alist_find_map_snd.
  destruct (alist_find (Some fn) (SMod.fnsems md)) eqn: FIND; rewrite FIND; cycle 1.
  { s. zstep_l. }
  destruct f as [[[img msk] scp] [fspo bd]].
  assert (WFSCP: incl scp (SMod.scopes md)).
  { etrans; [|apply SMod.well_scoped_fns].
    rewrite /fnsems_scopes. erewrite FIND. refl. }
  
  destruct (sp fn) eqn: E; s.
  {
    zstep_r. zstep_r.
    ziter_r. zstep_r. ziter_r. zstep_r. zstep_r.
    ziter_r. zstep_r. ziter_r. zstep_r.
    ziter_r. zstep_r. zstep_r.
    ziter_r. zstep_r. zstep_r.
    ziter_r. zstep_r. ziter_r. zstep_r.
    ziter_r. zstep_r. ziter_r. zstep_r. 

    rewrite !alist_find_map_snd FIND; s. ired.
    rewrite /HModTr.trans_ktree !sandbox_inline_commute; cycle 1.
    { destruct img; ss. }
    { destruct img; ss. }
    ziter_l. zstep_l. ziter_l. zstep_l. 
    ziter_r. zstep_r. ziter_r. zstep_r.

    rewrite if_simpl.
    destruct (classic (img = false ∨ fspo = None)); cycle 1.
    { destruct img; [|exfalso; et]. destruct fspo; [|exfalso; et].
      ziter_r. zstep_r.
      specialize (VP1 fn). rewrite FIND E in VP1. specialize (VP1 x).
      des. exists x5. zstep_r.
      ziter_r. zstep_r.
      ziter_r. zstep_r. eexists. zstep_r.
      ziter_r. zstep_r. ziter_r. zstep_r.
      ziter_r. zstep_r. eexists r_t. zstep_r.
      ziter_r. zstep_r. unshelve eexists.
      { split; eauto using Own_wand_valid.
        iIntros "H". iMod (x6 with "H") as "[P O]". iFrame. iApply PRE. et.
      }
      zstep_r. ziter_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r.

      zprogress. gbase. rewrite EQLEN. eapply CIH; et.
      split.
      { rewrite !length_insert !length_app !length_insert. s. et. }

      i. destruct (Nat.eq_dec i cid); subst.
      { rewrite lookup_app list_lookup_insert in EQx; try nia. inv EQx.
        rewrite list_lookup_insert_ne in EQy; try nia.
        rewrite lookup_app list_lookup_insert in EQy; try nia. inv EQy.
        econs; et. pstep. econs. et.
      }
      destruct (Nat.eq_dec i (length tgts)); subst.
      { rewrite list_lookup_insert in EQy; cycle 1.
        { rewrite length_app length_insert. s. nia. }
        rewrite lookup_app lookup_ge_None_2 in EQx; cycle 1.
        { rewrite length_insert. nia. }
        rewrite length_insert EQLEN Nat.sub_diag in EQx.
        inv EQx.
        econs; cycle 3.
        - rewrite /HModTr.trans interpV_bind HIRed.bind interpV_bind. refl.
        - i. nia.
        - eapply elim_rel_cancel; et. r. esplits; et.
        - refl.
      }
      rewrite lookup_app list_lookup_insert_ne in EQx; try nia.
      rewrite list_lookup_insert_ne in EQy; try nia.
      rewrite lookup_app list_lookup_insert_ne in EQy; try nia.
      destruct (srcs !! i) eqn: E0; cycle 1.
      { eapply lookup_ge_None_1 in E0.
        eapply lookup_lt_Some in EQx. ss. rewrite length_insert in EQx.
        nia.
      }
      destruct (tgts !! i) eqn: E1; cycle 1.
      { eapply lookup_ge_None_1 in E1.
        eapply lookup_lt_Some in EQy. ss. rewrite length_insert in EQy.
        nia.
      }
      inv EQx. et.
    }
    { rewrite if_prod_comm. destruct fspo.
      { exfalso. des; ss. subst. exploit WFS; et. ss. }
      rewrite !if_simpl. clear H.

      zprogress. gbase. rewrite EQLEN. eapply CIH; et; cycle 1.
      { des_safe. rewrite RS. iIntros ">H". iMod (x5 with "H") as "[P O]".
        iFrame. et. }
      split.
      { rewrite !length_app !length_insert. s. et. }

      i. destruct (Nat.eq_dec i cid); subst.
      { rewrite lookup_app list_lookup_insert in EQx; try nia. inv EQx.
        rewrite lookup_app list_lookup_insert in EQy; try nia. inv EQy.
        econs; et. pstep. econs. et.
      }
      destruct (Nat.eq_dec i (length tgts)); subst.
      { rewrite lookup_app lookup_ge_None_2 in EQx; cycle 1.
        { rewrite length_insert. nia. }
        rewrite length_insert EQLEN Nat.sub_diag in EQx.
        rewrite lookup_app lookup_ge_None_2 in EQy; cycle 1.
        { rewrite length_insert. nia. }
        rewrite length_insert Nat.sub_diag in EQy.
        inv EQx. inv EQy.
        assert (args = x2).
        { specialize (VP1 fn). rewrite FIND E in VP1. specialize (VP1 x). des; ss.
          eapply Own_pure_soundness; try apply WFR.
          rewrite RS. iIntros ">H". iMod (x6 with "H") as "[P O]".
          rewrite PRE. iMod "P" as "P". iApply "P".
        }
        subst. econs; cycle 3.
        - rewrite /SB.sandbox_body. s. erewrite bind_ret_r. refl.
        - i. nia.
        - eapply elim_rel_cancel; et. r. esplits; et.
        - rewrite /SB.sandbox_body. s. refl.
      }
      rewrite lookup_app list_lookup_insert_ne in EQx; try nia.
      rewrite lookup_app list_lookup_insert_ne in EQy; try nia.
      destruct (srcs !! i) eqn: E0; cycle 1.
      { eapply lookup_ge_None_1 in E0.
        eapply lookup_lt_Some in EQx. ss. rewrite length_insert in EQx.
        nia.
      }
      destruct (tgts !! i) eqn: E1; cycle 1.
      { eapply lookup_ge_None_1 in E1.
        eapply lookup_lt_Some in EQy. ss. rewrite length_insert in EQy.
        nia.
      }
      inv EQx. et.
    }
  }
  { zstep_r.
    rewrite !alist_find_map_snd FIND; s. ired.
    rewrite /HModTr.trans_ktree !sandbox_inline_commute; cycle 1.
    { destruct img; ss. }
    { destruct img; ss. }
    ziter_l. zstep_l. ziter_l. zstep_l. 
    ziter_r. zstep_r. ziter_r. zstep_r.

    rewrite if_simpl.
    destruct (classic (img = false ∨ fspo = None)); cycle 1.
    { destruct img; [|exfalso; et]. destruct fspo; [|exfalso; et].
      ziter_r. zstep_r.
      specialize (VP1 fn). rewrite FIND E in VP1. specialize (VP1 ()).
      des. exists x2. zstep_r.
      ziter_r. zstep_r.
      ziter_r. zstep_r. eexists. zstep_r.
      ziter_r. zstep_r. ziter_r. zstep_r.
      ziter_r. zstep_r. eexists r_t. zstep_r.
      ziter_r. zstep_r. unshelve eexists.
      { split; eauto using Own_wand_valid.
        iIntros "H". iFrame. iApply PRE. et.
      }
      zstep_r. ziter_r. zstep_r. ziter_r. zstep_r. ziter_r. zstep_r.

      zprogress. gbase. rewrite EQLEN. eapply CIH; et.
      split.
      { rewrite !length_insert !length_app !length_insert. s. et. }
      i. 

      destruct (Nat.eq_dec i cid); subst.
      { rewrite lookup_app list_lookup_insert in EQx; try nia. inv EQx.
        rewrite list_lookup_insert_ne in EQy; try nia.
        rewrite lookup_app list_lookup_insert in EQy; try nia. inv EQy.
        econs; et. pstep. econs. et.
      }
      destruct (Nat.eq_dec i (length tgts)); subst.
      { rewrite list_lookup_insert in EQy; cycle 1.
        { rewrite length_app length_insert. s. nia. }
        rewrite lookup_app lookup_ge_None_2 in EQx; cycle 1.
        { rewrite length_insert. nia. }
        rewrite length_insert EQLEN Nat.sub_diag in EQx.
        inv EQx.
        econs; cycle 3.
        - rewrite /HModTr.trans interpV_bind HIRed.bind interpV_bind. refl.
        - i. nia.
        - eapply elim_rel_cancel; et. r. esplits; et.
        - refl.
      }
      rewrite lookup_app list_lookup_insert_ne in EQx; try nia.
      rewrite list_lookup_insert_ne in EQy; try nia.
      rewrite lookup_app list_lookup_insert_ne in EQy; try nia.
      destruct (srcs !! i) eqn: E0; cycle 1.
      { eapply lookup_ge_None_1 in E0.
        eapply lookup_lt_Some in EQx. ss. rewrite length_insert in EQx.
        nia.
      }
      destruct (tgts !! i) eqn: E1; cycle 1.
      { eapply lookup_ge_None_1 in E1.
        eapply lookup_lt_Some in EQy. ss. rewrite length_insert in EQy.
        nia.
      }
      inv EQx. et.
    }
    { rewrite if_prod_comm. destruct fspo.
      { exfalso. des; ss. subst. exploit WFS; et. ss. }
      rewrite !if_simpl. clear H.

      zprogress. gbase. rewrite EQLEN. eapply CIH; et.
      split.
      { rewrite !length_app !length_insert. s. et. }

      i. destruct (Nat.eq_dec i cid); subst.
      { rewrite lookup_app list_lookup_insert in EQx; try nia. inv EQx.
        rewrite lookup_app list_lookup_insert in EQy; try nia. inv EQy.
        econs; et. pstep. econs. et.
      }
      destruct (Nat.eq_dec i (length tgts)); subst.
      { rewrite lookup_app lookup_ge_None_2 in EQx; cycle 1.
        { rewrite length_insert. nia. }
        rewrite length_insert EQLEN Nat.sub_diag in EQx.
        rewrite lookup_app lookup_ge_None_2 in EQy; cycle 1.
        { rewrite length_insert. nia. }
        rewrite length_insert Nat.sub_diag in EQy.
        inv EQx. inv EQy.
        econs; cycle 3.
        - rewrite /SB.sandbox_body. s. erewrite bind_ret_r. refl.
        - i. nia.
        - eapply elim_rel_cancel; et. r. esplits; et.
        - rewrite /SB.sandbox_body. s. refl.
      }
      rewrite lookup_app list_lookup_insert_ne in EQx; try nia.
      rewrite lookup_app list_lookup_insert_ne in EQy; try nia.
      destruct (srcs !! i) eqn: E0; cycle 1.
      { eapply lookup_ge_None_1 in E0.
        eapply lookup_lt_Some in EQx. ss. rewrite length_insert in EQx.
        nia.
      }
      destruct (tgts !! i) eqn: E1; cycle 1.
      { eapply lookup_ge_None_1 in E1.
        eapply lookup_lt_Some in EQy. ss. rewrite length_insert in EQy.
        nia.
      }
      inv EQx. et.
    }
  }
Unshelve. all: try exact smj_top.  
(*SLOW*)Qed.
