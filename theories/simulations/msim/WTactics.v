From iris.proofmode Require Import proofmode.
Require Import Common ConcRA Mod ltac2_lib.
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
  | |- context [?A ∖ ?B ∪ ?B] =>
    rewrite (difference_union_L A B) (comm_L _ A B) (subseteq_union_1_L B A); [|(solve_ndisj || set_solver)]
  end.

Ltac _wstep_s :=
  match goal with
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, tau;; _) _) ] =>
      iApply wsim_tau_src
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, Ret _ >>= _) _) ] =>
      rewrite bind_ret_l
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Take (FSpec (fspec_to_rel _))) >>= _) _) ] =>
      let name := fresh "_q" in iApply wsim_take_src_fspec; iIntros (name); simpl in name
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _) _) ] =>
      let name := fresh "_q" in iApply wsim_take_src; iIntros (name)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Assume ?P) >>= _) _) ] =>
      first [
        tcsearch constr:(WP P)
          ltac:(fun c =>
            iApply (wsim_assume_src_WP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i:=c)); simpl);
        match goal with
        | [ |- environments.envs_entails _ (?P' -∗ _)] =>
          unfoldPrePost_term P'; iIntrosFresh "ASM"; simpl_set
        end
      | unfoldPrePost_term P; iApply wsim_assume_src; iIntrosFresh "ASM"
      ]
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (AssumeRes _) >>= _) _) ] =>
      iApply wsim_assume_res_src; iIntrosFresh "ASM"
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, assume _ >>= _) _) ] =>
      let name := fresh "ASM" in iApply wsim_asm_src; iIntros (name)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (SPut ?k ?v) >>= _) _) ] =>
      let NODS := fresh "NODS" in
      iApply wsim_nodup_src; iIntros (NODS);
      iApply wsim_sput_src; state_insert_simpl k v NODS; clear NODS
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (?st_src, trigger (SGet ?k) >>= _) _) ] =>
      let NODS := fresh "NODS" in
      iApply wsim_nodup_src; iIntros (NODS);
      iApply wsim_sget_src; state_lookup_simpl st_src k NODS; clear NODS
  end.

Ltac wstep_s := cNormS; try _wstep_s; s; cNormS.

Ltac wsteps_s := cNormS; hrepeat (do 1 _wstep_s; s; cNormS).

Ltac _wstep_t :=
  match goal with
  (** tgt **)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, tau;; _)) ] =>
      iApply wsim_tau_tgt
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, Ret _ >>= _) ) ] =>
      rewrite bind_ret_l
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose (FSpec (fspec_to_rel _))) >>= _) ) ] =>
      let name := fresh "_q" in iApply wsim_choose_tgt_fspec; iIntros (name); simpl in name
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose _) >>= _) ) ] =>
      let name := fresh "_q" in iApply wsim_choose_tgt; iIntros (name)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _)) ] =>
      first [
        tcsearch constr:(WP P)
          ltac:(fun c =>
            iApply (wsim_guarantee_tgt_WP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i:=c)); simpl);
        match goal with
        | [ |- environments.envs_entails _ (?P' -∗ _)] =>
          unfoldPrePost_term P'; iIntrosFresh "GRT"; simpl_set
        end
      | unfoldPrePost_term P; iApply wsim_guarantee_tgt; iIntrosFresh "GRT"
      ]
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, guarantee _ >>= _)) ] =>
      let name := fresh "GRT" in iApply wsim_guar_tgt; iIntros (name)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (?st_tgt, trigger (SGet ?k) >>= _)) ] =>
      let NODT := fresh "NODT" in
      iApply wsim_nodup_tgt; iIntros (NODT);
      iApply wsim_sget_tgt; state_lookup_simpl st_tgt k NODT; clear NODT
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (SPut ?k ?v) >>= _)) ] =>
      let NODT := fresh "NODT" in
      iApply wsim_nodup_tgt; iIntros (NODT);
      iApply wsim_sput_tgt; state_insert_simpl k v NODT; clear NODT
  end.

Ltac wstep_t := cNormT; try _wstep_t; s; cNormT.

Ltac wsteps_t := cNormT; hrepeat (do 1 _wstep_t; s; cNormT).

Ltac _wstep tac :=
  match goal with
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, Ret _) (_, Ret _))] =>
      iApply wsim_unfold; iIntrosFresh "WINV"; iApply wsim_ret
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (IO _ _) >>= _) (_, trigger (IO _ _) >>= _))] =>
      iApply wsim_io; tac
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger GetTid >>= _) (_, trigger GetTid >>= _))] =>
      iApply wsim_gettid; tac
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Spawn _ _) >>= _) (_, trigger (Spawn _ _) >>= _))] =>
      iApply wsim_spawn; tac
  end.

Tactic Notation "wstep" ident(name) :=
  cNormS; cNormT; _wstep ltac:(iIntros (name)); cNormS; cNormT.

Tactic Notation "wstep" :=
  cNormS; cNormT; _wstep ltac:(iIntros "%"); cNormS; cNormT.

Ltac _wforce_s :=
  match goal with
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose (FSpec (fspec_to_rel _))) >>= _) _) ] =>
      iApply wsim_choose_src_fspec
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose ?T) >>= _) _) ] =>
      iApply wsim_choose_src
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _) _) ] =>
      first [
        tcsearch constr:(WP P)
          ltac:(fun c =>
          iApply (wsim_guarantee_src_WP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i:=c));
          simpl WP_space; simpl WP_remainder; [try (done||set_solver)|try (done||set_solver)| ]
        );
        match goal with
        | [ |- environments.envs_entails _ (?P' ∗ _)] =>
          unfoldPrePost_term P'; simpl_set
        end
      | unfoldPrePost_term P; iApply wsim_guarantee_src
      ]
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, unwrapN _ >>= _) _) ] =>
      iApply wsim_unwrapN_src
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, guarantee _ >>= _) _) ] =>
      iApply wsim_guar_src
  end.

Tactic Notation "wforce_s" :=
  cNormS; _wforce_s; s; [..|try iExists _; cNormS].

Tactic Notation "wforce_s" uconstr(p) :=
  cNormS; _wforce_s; s; [..|iExists p; cNormS].

Ltac wforces_s :=
  cNormS; hrepeat do 1 (_wforce_s; s; [..|try iExists _; cNormS]).

Ltac _wforce_t :=
  match goal with
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Take (FSpec (fspec_to_rel _))) >>= _)) ] =>
      iApply wsim_take_tgt_fspec
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _)) ] =>
      iApply wsim_take_tgt
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Assume ?P) >>= _)) ] =>
      first [
        tcsearch constr:(WP P)
          ltac:(fun c =>
          iApply (wsim_assume_tgt_WP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i:=c));
          simpl WP_space; simpl WP_remainder; [solve_ndisj|solve_ndisj| ]
        );
        match goal with
        | [ |- environments.envs_entails _ (?P' ∗ _)] =>
          unfoldPrePost_term P'; simpl_set
        end
      | unfoldPrePost_term P; iApply wsim_assume_tgt
      ]
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (AssumeRes _) >>= _)) ] =>
      iApply wsim_assume_res_tgt
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, assume _ >>= _)) ] =>
      iApply wsim_asm_tgt
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, RealUpdate (idx_to_rel ?P ?Q) >>= _)) ] =>
      unfoldPrePost_term P; unfoldPrePost_term Q; iApply wsim_ru_tgt_simple
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ (_, RealUpdate _ >>= _)) ] =>
      iApply wsim_ru_tgt_simple_general
  end
.

Tactic Notation "wforce_t" :=
  cNormT; _wforce_t; s; [..|try iExists _; cNormT].

Tactic Notation "wforce_t" uconstr(p) :=
  cNormT; _wforce_t; s; [..|iExists p; cNormT].

Ltac wforces_t :=
  cNormT; hrepeat do 1 (_wforce_t; s; [..|try iExists _; cNormT]).

Ltac winline_s :=
  cNormS; iApply wsim_inline_src; [try prove_inline_cond|unfold_cris_defs; cNormS].

Ltac winline_t :=
  cNormT; iApply wsim_inline_tgt; [try prove_inline_cond|unfold_cris_defs; cNormT].

Tactic Notation "wcall" uconstr(hyps) "as" "(" simple_intropattern(vret) simple_intropattern(st_src) simple_intropattern(st_tgt) ")" uconstr(IST) :=
  (cNormS; cNormT; iApply wsim_call); iSplitL hyps; [try done|try clear vret; try clear st_src; try clear st_tgt; try iClear IST; iIntros (vret st_src st_tgt) IST; cNormS; cNormT].

Tactic Notation "wyield" uconstr(hyps) "as" "(" simple_intropattern(st_src) simple_intropattern(st_tgt) ")" uconstr(IST) :=
  (cNormS; cNormT; iApply wsim_yield); iSplitL hyps; [try done|try clear st_src; try clear st_tgt; try iClear IST; iIntros (st_src st_tgt) IST; cNormS; cNormT].

Ltac wby_coind CIH :=
  iApply wsim_progress; iApply wsim_base; iIntrosFresh "WINV";
  iApply CIH.

Tactic Notation "wbind" uconstr(RR) uconstr(hyps) "as" "(" simple_intropattern(st_s) simple_intropattern(r_s) simple_intropattern(st_t) simple_intropattern(r_t) ")" uconstr(Q) :=
  iApply (wsim_bind _ _ _ _ _ _ _ _ _ _ _ _ _ RR); iSplitL hyps; [et|try clear st_s; try clear r_s; try clear st_t; try clear r_t; try iClear Q; iIntros (st_s r_s st_t r_t) Q]; cNormS; cNormT.
Tactic Notation "wbind" uconstr(RR) "as" "(" simple_intropattern(st_s) simple_intropattern(r_s) simple_intropattern(st_t) simple_intropattern(r_t) ")" uconstr(Q) :=
  iApply (wsim_bind _ _ _ _ _ _ _ _ _ _ _ _ _ RR); iSplitL; [et|try clear st_s; try clear r_s; try clear st_t; try clear r_t; try iClear Q; iIntros (st_s r_s st_t r_t) Q]; cNormS; cNormT.

Tactic Notation "wIst" constr(IST) "with" constr(H) :=
  match goal with
  | |- environments.envs_entails _ (wsim _ _ ?Ist _ _ _ _ _ _ _ _ (?sts, _) (?stt, _)) =>
      iAssert (Ist sts stt)%I with H as IST
  end.
