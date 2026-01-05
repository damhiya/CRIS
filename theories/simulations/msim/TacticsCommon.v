From iris.proofmode Require Import proofmode.
Require Import Common.
Require Export LAuto.

Require Import Sp Mod SMod LMod.

(************ User Tactics **************)

Tactic Notation "cong" constr(f) :=
  refine (f_equal f _).

Lemma string_app_inv
  p s s'
  (EQ: (p ++ s = p ++ s')%string)
  :
  (s = s')%string.
Proof.
  revert_until p. induction p; i; ss.
  unfold append in EQ. depdes EQ. eauto.
Qed.

Ltac inv_string X :=
  inv X;
  (hrepeat do 1 match goal with [H: @eq string _ _|-_] =>
           apply string_app_inv in H
     end);
  ss.

(* Ltac prove_scope :=
  try unfold Mod.fnsems; try unfold SMod.fnsems; try unfold fnsems_scopes;
  s; ii; des_ifs; ss; des; ss; eauto. *)

Ltac prove_nodup :=
  (hrepeat do 1 (econs; [ii; ss; des; try match goal with [H: _ |- _] => inv_string H end|]));
  try (econs; fail).

Ltac prove_precise :=
  (hrepeat do 1 (iApply precise_sep; iSplit));
  first [iApply precise_pure|iApply precise_own|iApply precise_Own].

(* Tactic for coinduction *)

Lemma combine_quant A B (P : ∀ (a: A) (b: B), Prop)
    (PR : ∀ (ab : A * B), P (fst ab) (snd ab)) :
  ∀ a b, P a b.
Proof using. i. eapply (PR (a,b)). Qed.

Lemma combine_quant_dep A (B: A -> Type) (P: forall a (b: B a), Prop)
    (PR: ∀ (ab: sigT B), P (projT1 ab) (projT2 ab)):
  ∀ a b, P a b.
Proof using. i. eapply (PR (existT a b)). Qed.

Lemma destruct_quant {A B} (P: A*B → Prop):
  (∀ a: A*B, P a) ↔ (∀ (a:A) (b: B), P (a, b)).
Proof.
  split; i; et. destruct a; et.
Qed.

Lemma destruct_quant_dep {A} (F: A→Type) (P: sigT F → Prop):
  (∀ a: sigT F, P a) ↔ (∀ (a:A) (b: F a), P (existT a b)).
Proof.
  split; i; et. destruct a; et.
Qed.

Ltac combine_quant tm :=
  revert tm; first [apply combine_quant | apply combine_quant_dep].

Ltac destruct_quant CIH :=
  (hrepeat first [setoid_rewrite destruct_quant in CIH
                 | setoid_rewrite destruct_quant_dep in CIH]);
  simpl in CIH.

Definition CRIS := "cris".
Global Opaque CRIS.

Ltac unfold_mod :=
  match goal with
  | [|-context[?x]] => 
    match type of x with Mod.t =>
      rewrite {1}/x; try unseal CRIS
    end
  end.

Ltac unfold_cris_defs :=
  rewrite /SB.sandbox_body; s;
  (hrepeat do 1 match goal with |- context[cfunU ?x] => rewrite {1}/x end);
  rewrite /cfunU;
  (hrepeat do 1 match goal with |- context[cfunN ?x] => rewrite {1}/x end);
  rewrite /cfunN;
  rewrite /SModTr.trans_fnsem /SModTr.trans_fnsem /=.

Lemma ereplace T (x y: T):
  x = y -> x = y.
Proof. eauto. Qed.

Ltac alist_upd_simpl :=
  let GOAL := fresh "GOAL" in
  match goal with [|-context [alist_upd ?k ?v ?l]] =>
    pattern (alist_upd k v l) at 1;
    match goal with [|- ?G _] => set (GOAL := G) end;
    (* first *)
    (* [ (timeout 1 simpl alist_upd); *)
    (*   try match goal with [|- _ (alist_upd _ _ _)] => fail 2 end *)
    (* |  *)
    match l with
    | context[(k,?v0)] =>
      let TMP := fresh "_TMP" in
      match goal with [H: List.NoDup _|-_] => revert H end;
      erewrite (@ereplace _ l); [intros TMP|Lauto_prepare; Lauto_find (k,v0); refl];
      rewrite !(alist_upd_with_nodup _ _ _ _ _ TMP); clear TMP;
      Lauto_finish
    end(* ] *);
    unfold GOAL; clear GOAL
  end.

Ltac move_aux :=
  (hrepeat do 1 match goal with [H: List.NoDup _ |- _ ] => guardH H; move H at top end);
  (hrepeat do 1 match goal with [H: incl _ (Mod.scopes _ _) |- _] => guardH H; move H at top end);
  (hrepeat do 1 match goal with [H: Mod.wf _ |- _ ] => guardH H; move H at top end);
  (* (hrepeat do 1 match goal with [H: ∀ _, sp_incl _ _ |- _ ] => guardH H; move H at top end); *)
  (hrepeat do 1 match goal with [H:=_:list (_ * (Any.t -> itree crisE Any.t)) |- _ ] => guardH H; move H at top end);
  unguard.

Ltac fnsems_nodup H :=
  revert H; simpl Mod.fnsems; (hrepeat do 1 unfold_mod); simpl List.map;
  try rewrite !List.map_map; try rewrite !fst_map_snd; eauto; fail.

Ltac alist_find_simpl :=
  let GOAL := fresh "GOAL" in
  match goal with [|-context [alist_find ?k ?l]] =>
    pattern (alist_find k l) at 1;
    match goal with [|- ?G _] => set (GOAL := G) end;
    simpl Mod.fnsems; (hrepeat do 1 unfold_mod; simpl Mod.fnsems);
    match goal with [|-context [alist_find ?k ?l]] =>
      first
      [ (timeout 1 simpl alist_find at 1);
         match goal with [|- _ (Some _)] => idtac end
      | let TMP := fresh "_TMP" in
        match goal with [H: List.NoDup _|-_] =>
          eassert (TMP: List.NoDup (List.map fst l))  by (fnsems_nodup H);
          revert TMP
        end;
        erewrite (@ereplace _ l); [intros TMP
        | Lauto_normalize; try rewrite !List.map_app; simpl List.map; Lauto_prepare;
          let KV := fresh "KV" in
          match goal with [|-context[(?k',?v)]] => change k' with k; set (KV:=(k,v)); try change (k,v) with KV; Lauto_find KV end; refl];
        rewrite !alist_find_with_nodup; [|exact TMP]; clear TMP;
        Lauto_finish
      ]
    end;
    unfold GOAL; clear GOAL
  end.

(*** head normalization tactic ***)
(*
  itree term        t
  ktree term        k
  stuck term        s ::= opaque term
                        | s >>= k
                        | ↥ s
                        | ↧ s
                        | ░ s
  head normal term  v ::= Ret x
                        | Tau t
                        | vis e k
                        | assumeK P t
                        | guaranteeK P t
                        | unwrapUK x k
                        | unwrapNK x k
                        | RealUpdateK pre post k
                        | SBRed.putSB imports scopes k v cont
                        | SBRed.getSB imports scopes k cont
                        | SBRed.callSB imports scopes f a cont
                        | SBRed.spawnSB imports scopes f a cont
                        | s
 *)
Tactic Notation "red_bind" tactic(tac) :=
  lazymatch goal with
  | [ |- @ITree.bind _ _ _ ?itr _ = _ ] =>
      lazymatch itr with
      | Ret _ => etransitivity; [ eapply bind_ret_l | s; tac ]
      | Tau _ => eapply bind_tau
      | vis _ _ => eapply vis_bind
      | assumeK _ _ => eapply assumeK_bind
      | guaranteeK _ _ => eapply guaranteeK_bind
      | unwrapUK _ _ => eapply unwrapUK_bind
      | unwrapNK _ _ => eapply unwrapNK_bind
      | RealUpdateK _ _ _ => eapply RealUpdateK_bind
      | @ITree.bind _ _ _ _ _ => eapply bind_bind
      | _ => reflexivity
      end
  end.

Tactic Notation "red_SB" tactic(tac) :=
  lazymatch goal with
  | [ |- @SB.sandbox ?Σ ?msk ?R ?itr = _ ] =>
      lazymatch itr with
      | Ret _ =>
          eapply SBRed.ret
      | Tau _ =>
          eapply SBRed.tau
      | vis _ ?k =>
          etransitivity; [eapply SBRed.vis | s; tac ]
      | @ITree.bind _ _ _ _ _ =>
          eapply SBRed.bind
      | _ =>
          reflexivity
      end
  end.

(* Ltac unfold_sp_exact sp name :=
  try match goal with
      [ H : sp_incl _ sp |- _ ] =>
        let RW := fresh "_RW" in
        let ND := fresh "_ND" in
        edestruct H as [ND RW];
        erewrite (RW name);
        [| revert ND; unfold to_sp;
           match goal with [|-context[alist_find _ ?x]] => rewrite /x end;
           unseal CRIS; i;
           alist_find_simpl;
           refl];
        simpl unwrapN; clear ND RW
    end. *)

Tactic Notation "red_S" tactic(tac) :=
  lazymatch goal with
  | [ |- @SModTr.trans ?Γ ?Σ ?α ?β ?τ ?_S ?_I ?_crisG ?concG ?sp ?N ?stid ?R ?itr = _ ] =>
      lazymatch itr with
      | Ret _ =>
          eapply SRed.ret
      | Tau _ =>
          eapply SRed.tau
      | vis (Assume _) _ =>
          eapply SRed.vis_agE
      | vis (AssumeRes _) _ =>
          eapply SRed.vis_agE
      | vis (Guarantee _) _ =>
          eapply SRed.vis_agE
      | vis (Spawn ?fn _) _ =>
          etransitivity;
          [ eapply SRed.vis_spawn
          | unfold SModTr.HoareSpawn;
            tac
          ]
      | vis (Yield _) _ =>
          etransitivity;
          [ eapply SRed.vis_yield
          | tac
          ]
      | vis GetTid _ =>
          etransitivity;
          [ eapply SRed.vis_gettid
          | tac
          ]
      | vis (Call ?fn _) _ =>
          etransitivity;
          [ eapply SRed.vis_call
          | unfold SModTr.HoareCall;
            tac
          ]
      | vis (SPut _ _) _ =>
          eapply SRed.vis_pgE
      | vis (SGet _) _ =>
          eapply SRed.vis_pgE
      | vis (Choose _) _ =>
          eapply SRed.vis_coreE
      | vis (Take _) _ =>
          eapply SRed.vis_coreE
      | vis (IO _ _) _ =>
          eapply SRed.vis_coreE
      (* | RealUpdateK _ _ _ =>
          eapply SRed.ruK *)
      | @ITree.bind _ _ _ _ _ =>
          eapply SRed.bind
      | _ =>
          reflexivity
      end
  end.

Ltac _hnorm_itr :=
  lazymatch goal with
  | |- match bool_decide ?P with | true => ?A | false => ?B end = _ =>
      tryif is_closed_term P
      then
        let r := eval vm_compute in (bool_decide P) in
        change (bool_decide P) with r in *;
        s; _hnorm_itr
      else reflexivity
  | [ |- Ret _ = _ ] =>
      reflexivity
  | [ |- Tau _ = _ ] =>
      reflexivity
  | [ |- vis _ _ = _ ] =>
      reflexivity
  | [ |- @ITree.bind ?E ?T ?U ?itr ?ktr = _ ] =>
      etransitivity;
      [ let itr' := fresh "itr" in
        cong (fun (itr' : itree E T) => @ITree.bind E T U itr' ktr); _hnorm_itr
      | red_bind (do 1 _hnorm_itr) ]
  | [ |- @SB.sandbox ?Σ ?msk ?R ?itr = _ ] =>
      etransitivity;
      [ cong (@SB.sandbox Σ msk R); _hnorm_itr | red_SB (do 1 _hnorm_itr) ]
  | [ |- @SModTr.trans ?Γ ?Σ ?α ?β ?τ ?_S ?_I ?_crisG ?concG ?sp ?N ?stid ?R ?itr = _ ] =>
      etransitivity;
      [ cong (@SModTr.trans Γ Σ α β τ _S _I _crisG concG sp N stid R); _hnorm_itr
      | red_S (do 1 _hnorm_itr) ]
  | [ |- trigger _ = _ ] =>
      eapply trigger_vis
  | [ |- RealUpdate _ _ = _ ] =>
      eapply RealUpdate_RealUpdateK
  | [ |- SModTr.HoareCall _ _ _ = _ ] =>
      unfold SModTr.HoareCall;
      _hnorm_itr
  | [ |- fbody_trivial _ = _ ] =>
      unfold fbody_trivial;
      _hnorm_itr
  | [ |- cput _ _ = _ ] =>
      unfold cput;
      _hnorm_itr
  | [ |- cgetU _ = _ ] =>
      unfold cgetU;
      _hnorm_itr
  | [ |- cgetN _ = _ ] =>
      unfold cgetN;
      _hnorm_itr
  | [ |- cfunU _ _ = _ ] =>
      unfold cfunU;
      _hnorm_itr
  | [ |- cfunN _ _ = _ ] =>
      unfold cfunN;
      _hnorm_itr
  | [ |- ccallU _ _ = _ ] =>
      unfold ccallU;
      _hnorm_itr
  | [ |- ccallN _ _ = _ ] =>
      unfold ccallN;
      _hnorm_itr
  | [ |- triggerUB = _ ] =>
      unfold triggerUB;
      _hnorm_itr
  | [ |- triggerNB = _ ] =>
      unfold triggerNB;
      _hnorm_itr
  | [ |- ?itr = _ ] =>
      reflexivity
  end.

Ltac hnorm_itr :=
  etransitivity;
  [ _hnorm_itr
  | s;
    lazymatch goal with
    | |- Ret _ = _ =>
        reflexivity
    | |- Tau _ = _ =>
        reflexivity
    | |- vis _ _ = _ =>
        rewrite ?resum_to_subevent ?subevent_subevent;
        eapply vis_trigger
    | |- assumeK _ _ = _ =>
        eapply assumeK_assume
    | |- guaranteeK _ _ = _ =>
        eapply guaranteeK_guarantee
    | |- unwrapUK _ _ = _ =>
        eapply unwrapUK_unwrapU
    | |- unwrapNK _ _ = _ =>
        eapply unwrapNK_unwrapN
    | |- RealUpdateK _ _ _ = _ =>
        eapply RealUpdateK_RealUpdate
    | [ |- _ = _ ] =>
        reflexivity
    end
  ].

Ltac iIntrosFresh H :=
  iIntros H
  ||
  let H' := eval compute in (H ++ "'")%string in iIntrosFresh H'.

Ltac des_pairs :=
  (hrepeat do 1
    match goal with
    | [H: context[let () := ?x in _] |- _] =>
        match type of x with
        | () => destruct x
        | (_ * _)%type =>
            let n0 := fresh "_q" in let n1 := fresh "_q" in
            let EQ := fresh "EQq" in
            destruct x as [n0 n1] eqn: EQ
        end
    | |- context[let () := ?x in _] =>
        match type of x with
        | () => destruct x
        | (_ * _)%type =>
            let n0 := fresh "_q" in let n1 := fresh "_q" in
            let EQ := fresh "EQq" in
            destruct x as [n0 n1] eqn: EQ
        end
    end);
   subst.

Ltac unfold_pre_post_term term :=
  let TM := fresh "_term" in
  set (TM := term) at 1;
  (hrepeat do 1 match goal with
       [H := ?P |- _] =>
         match H with
           TM => match P with
                 | context[precond] => unfold precond in TM; simpl in TM
                 | context[postcond] => unfold postcond in TM; simpl in TM
                 (* | context[precondS] => unfold precondS in TM; simpl in TM *)
                 (* | context[postcondS] => unfold postcondS in TM; simpl in TM *)
                 end
         end
     end);
  subst TM.

Ltac unfold_pre_post :=
  hrepeat do 1 match goal with
  | |-context[precond] => rewrite /precond; s
  | |-context[postcond] => rewrite /postcond; s
  (* | |-context[precondS] => rewrite /precondS; s
  | |-context[postcondS] => rewrite /postcondS; s *)
  end.

Ltac set_marker marker :=
  assert (marker: True) by exact I.

Ltac hide_ihyps_env env :=
  match env with
  | environments.Enil => idtac
  | environments.Esnoc ?tl _ ?hyp =>
      hide_ihyps_env tl;
      let IHYP := fresh "IHYP" in
      set (IHYP := hyp) at 1
  end.

Ltac hide_ihyps :=
  match goal with
  | [ |- environments.envs_entails {|environments.env_intuitionistic := ?ienv; environments.env_spatial := ?env |} _] =>
      hide_ihyps_env ienv;
      hide_ihyps_env env
  end.

Ltac only_itree_l :=
  let ITREE := fresh "ITREE" in
  match goal with
  [|- _ (_ _ (_, ?it))] => first [set (ITREE := it) at 2|set (ITREE := it) at 1]
  end.

Ltac only_itree_r :=
  let ITREE := fresh "ITREE" in
  match goal with [|- _ (_ (_, ?it) _)] => set (ITREE := it) at 1 end.

Ltac show_itree :=
  match goal with [H:_|-_] => unfold H; clear H end.

Ltac show_until marker :=
  (hrepeat do 1 match goal with
      [H: _ |- _] =>
        try match H with marker => fail 3 end;
        first [unfold H; clear H | revert H]
    end);
  clear marker; i.

Ltac prove_sub_perm :=  
  i; try rewrite /Mod.scopes; s; (hrepeat do 1 unfold_mod); s;
  match goal with
    [|-sub_perm ?x ?y] =>
      match x with
      | _ :: _ => idtac
      | _ => try rewrite /x
      end;
      match y with
      | _ :: _ => idtac
      | _ => try rewrite /y
      end
  end;
  (hrepeat do 1 s;
   match goal with [|-sub_perm (?k::_) ?tgt] =>
     let key := fresh "key" in
     set (key := k);
     match tgt with
     |  context[?k'::_] =>
          change k' with key;
          eapply eq_ind; [|symmetry; Lauto_prepare; Lauto_find key; refl];
          eapply (sub_perm_cancel [key] [])
     end;
     unfold key; clear key
  end);
  apply sub_perm_nil.

(* TODO : improve *)
Ltac prove_inline_cond :=
  simpl_map; ss.

Ltac prove_sb_cond :=
  by s; i; eauto; try rewrite !mask_app; s; eauto.

(* Normalization tactics *)
Ltac replace_l :=
  lazymatch goal with
  | [ |- environments.envs_entails ?env (?rel (?st_src, ?itr_src) (?st_tgt, ?itr_tgt)) ] =>
      refine (eq_ind_r (fun itr_src' => environments.envs_entails env (rel (st_src, itr_src') (st_tgt, itr_tgt))) _ _); cycle 1
  end.

Ltac replace_r :=
  lazymatch goal with
  | [ |- environments.envs_entails ?env (?rel (?st_src, ?itr_src) (?st_tgt, ?itr_tgt)) ] =>
      refine (eq_ind_r (fun itr_tgt' => environments.envs_entails env (rel (st_src, itr_src) (st_tgt, itr_tgt'))) _ _); cycle 1
  end.

Ltac norm_l := replace_l; [s; hnorm_itr|].
Ltac norm_r := replace_r; [s; hnorm_itr|].

Tactic Notation "norm_l" "with" tactic(tac) :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  norm_l;
  tac;
  show_until marker.

Tactic Notation "norm_r" "with" tactic(tac) :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  norm_r;
  tac;
  show_until marker.

Tactic Notation "norm" "with" tactic(tac) :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  norm_l;
  norm_r;
  tac;
  show_until marker.

(* unfold tactics *)

Ltac unfold_iter_l :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_l;
  erewrite (bisim_is_eq (unfold_iter _ _));
  show_until marker.

Ltac unfold_iter_r :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_r;
  erewrite (bisim_is_eq (unfold_iter _ _));
  show_until marker.

Ltac unfold_iterC_l :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_l;
  rewrite unfold_iterC;
  show_until marker.

Ltac unfold_iterC_r :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_r;
  rewrite unfold_iterC;
  show_until marker.

(** hss, hss_l, hss_r : simplify itrees **)

Lemma copset_diff_union (E E': coPset)
  (SUB: E' ⊆ E)
  :
  (E ∖ E') ∪ E' = E.
Proof.
  eapply leibniz_equiv.
  rewrite difference_union comm subseteq_union_1; et.
Qed.

Lemma copset_union_diff (E E': coPset)
  (SUB: E ## E')
  :
  (E ∪ E') ∖ E'  = E.
Proof.
  eapply leibniz_equiv.
  rewrite difference_union_distr_l difference_diag right_id.
  rewrite difference_disjoint_L; et.
Qed.

Ltac hss_copset :=
  match goal with
  | |- context[(@union coPset coPset_union (@difference coPset coPset_difference ?E ?E') ?E')] =>
    replace ((E ∖ E') ∪ E') with E by (rewrite copset_diff_union; et; set_solver)
  | |- context[(@difference coPset coPset_difference (@union coPset coPset_union ?E ?E') ?E')] =>
    replace ((E ∪ E') ∖ E') with E by (rewrite copset_union_diff; et; set_solver)
  | |- context[(@difference coPset coPset_difference ?E ?E)] =>
    replace (E ∖ E) with (∅ : coPset) by set_solver
  | |- context[(@union coPset coPset_union ∅ ?E)] =>
    replace (∅ ∪ E) with E by set_solver
  | |- context[(@union coPset coPset_union ?E ∅)] =>
    replace (E ∪ ∅) with E by set_solver
  end.

Ltac hss_des :=
  ss; des_safe; subst;
  (hrepeat do 1 match goal with
    | [v: () |- _] => destruct v
    | [H: (_,_) = (_,_) |- _] => inv H
    end);
  ss.

Ltac hss :=
  (hrepeat do 1 match goal with
     | [|- context[environments.Esnoc _ ?H (True%I)]] => iClear H
     | [|- context[environments.Esnoc _ ?H (emp%I)]] => iClear H
     end);
  hss_des;
  try (rewrite -> !Any.pair_split in * );
  try (rewrite -> !Any.upcast_downcast in * );
  try (rewrite -> !SAny.pair_split in * );
  try (rewrite -> !SAny.upcast_downcast in * );
  (hrepeat do 1 match goal with [G: Any.downcast _ = Some _ |-_] =>
    apply Any.downcast_upcast in G; inv G; ss
   end);
  (hrepeat do 1 match goal with [G: Any.upcast _ = Any.upcast _ |-_] =>
    apply Any.upcast_inj in G; destruct G as [_ G]; red in G; depdes G; ss
   end);
  (hrepeat do 1 match goal with [G: SAny.downcast _ = Some _ |-_] =>
    apply SAny.downcast_upcast in G; inv G; ss
   end);
  (hrepeat do 1 match goal with [G: SAny.upcast _ = SAny.upcast _ |-_] =>
    apply SAny.upcast_inj in G; destruct G as [_ G]; red in G; depdes G; ss
   end);
  (hrepeat do 1 match goal with [G: Some _ = Some _ |- _] =>
    depdes G; ss
   end);
  try (rewrite -> !Any.pair_split in * );
  try (rewrite -> !Any.upcast_downcast in * );
  try (rewrite -> !SAny.pair_split in * );
  try (rewrite -> !SAny.upcast_downcast in * );
  hss_des;
  (hrepeat do 1 hss_copset);
  move_aux.

(* Ltac hss_l := only_itree_l; hss; show_itree. *)
(* Ltac hss_r := only_itree_r; hss; show_itree. *)
Ltac hss_l := 
  only_itree_l;
  match goal with
  | |- context [Any.downcast (Any.upcast ?A)] => rewrite (Any.upcast_downcast A)
  | |- context [SAny.downcast (SAny.upcast ?A)] => rewrite (SAny.upcast_downcast A)
  end; show_itree.
Ltac hss_r :=
  only_itree_r;
  match goal with
  | |- context [Any.downcast (Any.upcast ?A)] => rewrite (Any.upcast_downcast A)
  | |- context [SAny.downcast (SAny.upcast ?A)] => rewrite (SAny.upcast_downcast A)
  end; show_itree.

Ltac red_ret_l :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_l;
  rewrite ?SRed.bind ?SRed.ret SBRed.bind SBRed.ret bind_ret_l;
  show_until marker.
 
Ltac red_ret_r :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_r;
  rewrite ?SRed.bind ?SRed.ret SBRed.bind SBRed.ret bind_ret_l;
  show_until marker.

Tactic Notation "add_ret_l" uconstr(r) :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_l;
  match goal with [|-_ _ (_ (_,?t) _)] =>
    rewrite -(bind_ret_l r (fun _ => t))
  end;
  show_until marker.

Tactic Notation "add_ret_r" uconstr(r) :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_r;
  match goal with [|-_ _ (_ _ (_,?t))] =>
    rewrite -(bind_ret_l r (fun _ => t))
  end;
  show_until marker.
