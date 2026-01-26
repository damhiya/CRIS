From iris.proofmode Require Import proofmode.
Require Import Common Mod ltac2_lib.
Require Import WSim TacticsCommon.

Ltac is_key_in k m :=
  match m with
  | {[ ?k1 := _ ]} => tryif (unify k k1) then idtac else fail
  | <[ ?k1 := _ ]> ?rest => tryif (unify k k1) then idtac else is_key_in k rest
  | union_with _ ?l ?r => first [ is_key_in k l | is_key_in k r ]
  | _ => fail
  end.

Ltac solve_map_lookup_symbolic NODT :=
  match goal with
  | [ |- union_with ?f ?l ?r !! ?k = _ ] =>
      tryif is_key_in k l 
      then (
        eapply lookup_union_with_l;
        [eauto|eapply map_Forall_union_with_inv in NODT as [NODT _]];
        solve_map_lookup_symbolic NODT
      )
      else (
        eapply lookup_union_with_r;
        [eauto|eapply map_Forall_union_with_inv in NODT as [_ NODT]];
        solve_map_lookup_symbolic NODT
      )
  | [ |- <[ ?k' := ?v ]> ?m !! ?k = _ ] =>
      (* Case: Insert *)
      tryif unify k' k
      then (rewrite lookup_insert; reflexivity)
      else (
        etransitivity;
        [eapply lookup_insert_ne; intros Hc; inv Hc|solve_map_lookup_symbolic NODT]
      )
  | [ |- {[ ?k' := ?v ]} !! ?k = _ ] =>
      (* Case: Singleton *)
      unify k' k; apply lookup_singleton
  | |- ?A => 
      (* idtac "Leaf reached or structure unknown";  *) fail
  end.

Ltac state_lookup_simpl st k NOD :=
  match goal with
  | |- context C[st !! k] =>
      let lhs := constr:(st !! k) in
      let T := type of lhs in
      let rhs := fresh "rhs" in
      let Heq := fresh "Heq" in
      evar (rhs : T);
      assert (Heq : lhs = rhs); subst rhs;
      [solve_map_lookup_symbolic NOD|rewrite Heq; clear Heq]
  end.

(* TODO : the complexity of this tactic is terrible - make it better *)
Ltac state_insert_simpl k1 v1 NODT :=
  match goal with
  | |- context C[base.insert k1 (Some v1) ?a] =>
      let lhs := constr:(base.insert k1 (Some v1) a) in
      let T := type of lhs in
      let rhs := fresh "rhs" in
      let Heq := fresh "Heq" in
      evar (rhs : T);
      assert (Heq : lhs = rhs); subst rhs;
      [ match goal with
        | [ |- <[?k:=Some ?v]> (union_with ?f ?l ?r) = _ ] =>
            tryif is_key_in k l
            then (
              etransitivity;
              [ eapply insert_union_with_l';
                [ eauto
                | eapply map_Forall_union_with_inv in NODT as [NODT _];
                  eexists; state_lookup_simpl l k NODT; reflexivity
                ]
              | eapply map_Forall_union_with_inv in NODT as [NODT _]; 
                state_insert_simpl k v NODT; reflexivity ]
            )
            else (
              etransitivity;
              [ eapply insert_union_with_r';
                [ eauto
                | eapply map_Forall_union_with_inv in NODT as [_ NODT];
                  eexists; state_lookup_simpl r k NODT; reflexivity
                ]
              | eapply map_Forall_union_with_inv in NODT as [_ NODT]; 
                state_insert_simpl k v NODT; reflexivity ]
            )
        | [ |- <[?k:=_]>{[?k':=_]} = _ ] => (* Case: Singleton *)
            unify k' k; apply insert_singleton
        | [ |- <[?k:=Some ?v]>(<[?k':=?v']>?m) = _ ] => (* Case: Insert *)
            tryif unify k' k
            then (rewrite insert_insert; reflexivity)
            else (
              rewrite (insert_commute _ k k');
              [state_insert_simpl k v NODT
              |let Hc := fresh "Hc" in intros Hc; inv Hc];
              reflexivity
            )
        
        | |- ?A => fail
        end
      |rewrite Heq; clear Heq]
  end.

Ltac simpl_set := repeat
  match goal with
  | |- context [?X ∪ ∅] => rewrite (right_id_L ∅ _ X)
  | |- context [∅ ∪ ?X] => rewrite (left_id_L ∅ _ X)
  | |- context [?A ∖ ?A] => rewrite (difference_diag_L A)
  | |- context [?A ∖ ?B ∪ ?B] => idtac "TODO"
  end.

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
          unfold_pre_post_term P'; iIntrosFresh "ASM"; simpl_set
        end
      | unfold_pre_post_term P; iApply wsim_assume_src; iIntrosFresh "ASM"
      ]
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (AssumeRes _) >>= _) _) ] =>
      iApply wsim_assume_res_src; iIntrosFresh "ASM"
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, assume _ >>= _) _) ] =>
      let name := fresh "asm" in iApply wsim_asm_src; iIntros (name)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (SPut ?k ?v) >>= _) _) ] =>
      let NODS := fresh "NODS" in
      iApply wsim_nodup_src; iIntros (NODS);
      iApply wsim_sput_src; state_insert_simpl k v NODS; clear NODS
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (?st_src, trigger (SGet ?k) >>= _) _) ] =>
      let NODS := fresh "NODS" in
      iApply wsim_nodup_src; iIntros (NODS);
      iApply wsim_sget_src; state_lookup_simpl st_src k NODS; clear NODS
  end.
Ltac wstep_l_core :=
  _wstep_l; s.

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
      unfold_pre_post_term P; iApply wsim_guarantee_tgt; iIntrosFresh "GRT"
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, guarantee _ >>= _)) ] =>
      let name := fresh "grt" in iApply wsim_guar_tgt; iIntros (name)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (?st_tgt, trigger (SGet ?k) >>= _)) ] =>
      let NODT := fresh "NODT" in
      iApply wsim_nodup_tgt; iIntros (NODT);
      iApply wsim_sget_tgt; state_lookup_simpl st_tgt k NODT; clear NODT
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (SPut ?k ?v) >>= _)) ] =>
      let NODT := fresh "NODT" in
      iApply wsim_nodup_tgt; iIntros (NODT);
      iApply wsim_sput_tgt; state_insert_simpl k v NODT; clear NODT
  end.

Ltac wstep_r_core :=
  _wstep_r; s.

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
      iApply wsim_unfold; iIntros "?"; iApply wsim_ret
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (IO _ _) >>= _) (_, trigger (IO _ _) >>= _))] =>
      iApply wsim_io; iIntros "%"
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger GetTid >>= _) (_, trigger GetTid >>= _))] =>
      iApply wsim_gettid; iIntros "%"
  end.

Ltac wstep :=
  norm with do 1 _wstep.

Ltac _wforce_l :=
  match goal with
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose ?T) >>= _) _) ] =>
      iApply wsim_choose_src
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _) _) ] =>
      first [
        tcsearch constr:(WP P)
          ltac:(fun c =>
          iApply (wsim_guarantee_src_WP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i:=c));
          [first [done|set_solver]|first [done|set_solver]|simpl WP_space]
        );
        match goal with
        | [ |- environments.envs_entails _ (?P' ∗ _)] =>
          unfold_pre_post_term P'; simpl_set
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
          iApply (wsim_assume_tgt_WP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i:=c));
          [first [done|set_solver]|first [done|set_solver]|simpl WP_space]
        );
        match goal with
        | [ |- environments.envs_entails _ (?P' ∗ _)] =>
          unfold_pre_post_term P'; simpl_set
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
    do 1 iApply wsim_inline_src; [try prove_inline_cond|unfold_cris_defs].

Ltac winline_r :=
  norm_r with
    do 1 iApply wsim_inline_tgt; [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs].

Ltac wcall hyps :=
  (norm with do 1 iApply wsim_call); iSplitL hyps; [try done|].
  (* (norm with do 1 iApply wsim_call); [try prove_sb_cond|
  iSplitL hyps; [try done| iIntros "% % %"; iIntrosFresh "IST"];
  move_aux]. *)

Ltac wspawn :=
  (norm with do 1 iApply wsim_spawn); [try prove_sb_cond|].

Ltac wyield hyps :=
  (norm with do 1 iApply wsim_yield);
  iSplitL hyps; [try done| iIntros "% %"; iIntrosFresh "IST"];
  move_aux.

Ltac wby_coind CIH :=
  iApply wsim_progress; iApply wsim_base; iIntrosFresh "I";
  iApply CIH.

(* Ltac winit_simF :=
  initialize_simF;
  iApply wsim_isim;
  try (
      iDestruct "IST" as "[% [W [TID IST]]]"; des; subst;
      iApply wsim_init_winv; iSplitL "W"; [et; fail|]; hss_copset;
      hrepeat do 1 (unfold_mod; s)). *)

(** Special Tactics for RealUpdate **)

(* Tactic Notation "wru_l_advanced" uconstr(P) := *)
(*   norm_l; iApply wsim_ru_src_advanced; *)
(*   iExists P; iSplit; [try prove_precise|]. *)

(* Ltac wru_r := *)
(*   norm_r; iApply wsim_ru_tgt. *)