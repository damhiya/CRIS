From iris.proofmode Require Import proofmode.
Require Import Common Mod ltac2_lib.
Require Import WSim TacticsCommon TacticsInit.

Ltac _wstep_l :=
  match goal with
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, tau;; _) _) ] =>
      iApply wsim_tau_src
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, Ret _ >>= _) _) ] =>
      rewrite bind_ret_l
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _) _) ] =>
      let name := fresh "_q" in iApply wsim_take_src; iIntros (name)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Assume ?P) >>= _) _) ] =>
      first [
        tcsearch constr:(WP P)
          ltac:(fun c =>
            iApply (wsim_assume_src_WP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i:=c)); simpl);
        match goal with
        | [ |- environments.envs_entails _ (?P' -∗ _)] =>
          unfold_pre_post_term P'; iIntrosFresh "ASM"
        end
      | unfold_pre_post_term P; iApply wsim_assume_src; iIntrosFresh "ASM"
      ]
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (AssumeRes _) >>= _) _) ] =>
      iApply wsim_assume_res_src; iIntrosFresh "ASM"
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, assume _ >>= _) _) ] =>
      let name := fresh "asm" in iApply wsim_asm_src; iIntros (name)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, (SB.sandbox _ _ _ (trigger (SPut _ _))) >>= _) _) ] =>
      iApply wsim_nodup_src; iIntros (?); iApply wsim_sput_src_sandbox; [s;eauto|alist_upd_simpl]
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, (SB.sandbox _ _ _ (trigger (SGet _))) >>= _) _) ] =>
      iApply wsim_nodup_src; iIntros (?); iApply wsim_sget_src_sandbox; [s;eauto|alist_find_simpl]
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) _) ] =>
      let name := fresh "_q" in
      iApply wsim_unwrapU_src; iIntros (name) "%";
      match goal with [ H: ?x = Some _ |- _ ] => let G := fresh "G" in rename H into G; try rewrite -> G in * end
  end.

Ltac wstep_l_core :=
  _wstep_l; try alist_find_simpl; s; des_pairs; s.

Ltac wstep_l :=
  norm_l with do 1 try wstep_l_core.

Ltac wsteps_l :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  norm_l;
  (hrepeat (do 1 wstep_l_core; norm_l));
  show_until marker.

Ltac _wstep_r :=
  match goal with
  (** tgt **)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, tau;; _)) ] =>
      iApply wsim_tau_tgt
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, Ret _ >>= _) ) ] =>
      rewrite bind_ret_l
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose _) >>= _) ) ] =>
      let name := fresh "_q" in iApply wsim_choose_tgt; iIntros (name)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _) ) ] =>
      first [
        tcsearch constr:(WP P)
          ltac:(fun c =>
            iApply (wsim_guarantee_tgt_WP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i:=c)); simpl);
        match goal with
        | [ |- environments.envs_entails _ (?P' -∗ _)] =>
            unfold_pre_post_term P'; iIntrosFresh "GRT"
        end
      | unfold_pre_post_term P; iApply wsim_guarantee_tgt; iIntrosFresh "GRT"
      ]
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, guarantee _ >>= _)) ] =>
      let name := fresh "grt" in iApply wsim_guar_tgt; iIntros (name)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, (SB.sandbox _ _ _ (trigger (SPut _ _))) >>= _)) ] =>
      iApply wsim_nodup_tgt; iIntros (?); iApply wsim_sput_tgt_sandbox; [s; eauto|alist_upd_simpl]
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, (SB.sandbox _ _ _ (trigger (SGet _))) >>= _)) ] =>
      iApply wsim_nodup_tgt; iIntros (?); iApply wsim_sget_tgt_sandbox; [s; eauto|alist_find_simpl]
  end.

Ltac wstep_r_core :=
  _wstep_r; s; des_pairs; s.

Ltac wstep_r :=
  norm_r with do 1 try wstep_r_core.

Ltac wsteps_r :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  norm_r;
  (hrepeat (do 1 wstep_r_core; norm_r));
  show_until marker.

Ltac _wstep :=
  match goal with
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, Ret _) (_, Ret _))] =>
      iApply wsim_ret
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (IO _ _) >>= _) (_, trigger (IO _ _) >>= _))] =>
      iApply wsim_io; iIntros "%"
  end.

Ltac wstep :=
  norm with do 1 _wstep; s; des_pairs; s.

Ltac _wforce_l :=
  match goal with
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose ?T) >>= _) _) ] =>
      iApply wsim_choose_src
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _) _) ] =>
      first [
        tcsearch constr:(WP P)
          ltac:(fun c =>
          iApply (wsim_guarantee_src_WP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i:=c)); [try set_solver|try set_solver|simpl WP_space]);
        match goal with
        | [ |- environments.envs_entails _ (?P' ∗ _)] =>
          unfold_pre_post_term P'
        end
      | unfold_pre_post_term P; iApply wsim_guarantee_src
      ]
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, unwrapN _ >>= _) _) ] =>
      iApply wsim_unwrapN_src
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, guarantee _ >>= _) _) ] =>
      iApply wsim_guar_src
  end.

Ltac wforce_l_core :=
  norm_l with do 1 _wforce_l.

Tactic Notation "wforce_l" :=
  wforce_l_core; [..|try iExists _].

Tactic Notation "wforce_l" uconstr(p) :=
  wforce_l_core; [..|iExists p].

Ltac wforces_l :=
  hrepeat do 1 wforce_l.

Ltac _wforce_r :=
  match goal with
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _)) ] =>
      iApply wsim_take_tgt
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Assume ?P) >>= _)) ] =>
      first [
        tcsearch constr:(WP P)
          ltac:(fun c =>
            unshelve iApply (wsim_assume_tgt_WP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i:=c)); s; [try set_solver|try set_solver|simpl WP_space]
          );
        match goal with
        | [ |- environments.envs_entails _ (?P' ∗ _)] =>
          unfold_pre_post_term P'
        end
      | unfold_pre_post_term P; iApply wsim_assume_tgt
      ]
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (AssumeRes _) >>= _)) ] =>
      iApply wsim_assume_res_tgt
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, assume _ >>= _)) ] =>
      iApply wsim_asm_tgt
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, RealUpdate ?P ?Q >>= _)) ] =>
      unfold_pre_post_term P; unfold_pre_post_term Q; iApply wsim_ru_tgt_simple
  end
.

Ltac wforce_r_core :=
  norm_r with do 1 _wforce_r; s.

Tactic Notation "wforce_r" :=
  wforce_r_core; try (iExists _).

Tactic Notation "wforce_r" uconstr(p) :=
  wforce_r_core; iExists p.

Ltac wforces_r :=
  hrepeat do 1 wforce_r.

Ltac winline_l :=
  norm_l with
    do 1 iApply wsim_inline_src_sandbox; [try prove_inline_cond|unfold_cris_defs].

Ltac winline_r :=
  norm_r with
    do 1 iApply wsim_inline_tgt_sandbox; [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs].

Ltac wcall hyps :=
  (norm with do 1 iApply wsim_call_sandbox); [try prove_sb_cond|
  iSplitL hyps; [try done| iIntros "% % %"; iIntrosFresh "IST"];
  move_aux].

Ltac wspawn :=
  (norm with do 1 iApply wsim_spawn_sandbox); [try prove_sb_cond|].

Ltac wyield hyps :=
  (norm with do 1 iApply wsim_yield);
  iSplitL hyps; [try done| iIntros "% %"; iIntrosFresh "IST"];
  move_aux.

Ltac wby_coind CIH :=
  iApply wsim_progress; iApply wsim_base; iIntrosFresh "I";
  iApply CIH.

Ltac winit_simF :=
  initialize_simF;
  iApply wsim_isim;
  try (
      iDestruct "IST" as "[% [W [TID IST]]]"; des; subst;
      iApply wsim_init_winv; iSplitL "W"; [et; fail|]; hss_copset;
      hrepeat do 1 (unfold_mod; s)).

(** Special Tactics for AssumeProph in Source **)

Tactic Notation "wru_l_advanced" uconstr(P) :=
  norm_l; iApply wsim_ru_src_advanced;
  iExists P; iSplit; [try prove_precise|].

Tactic Notation "wru_l" uconstr(P) :=
  norm_l; iApply wsim_ru_src;
  iExists P; iSplit; [try prove_precise|].

Ltac wru_r :=
  norm_r; iApply wsim_ru_tgt.
