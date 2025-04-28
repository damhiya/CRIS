From iris.proofmode Require Import proofmode.
Require Import Common.
Require Import LAuto.

Require Import Sp Mod SMod HMod PMod.
Require Import HModSim ISim.
(* Require Import SchHeader. *)

(************ User Tactics **************)

Ltac cong f :=
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

Ltac prove_scope :=
  try unfold HMod.fnsems; try unfold SMod.fnsems; try unfold fnsems_scopes;
  s; ii; des_ifs; ss; des; ss; eauto.

Ltac prove_nodup :=
  (hrepeat do 1 (econs; [ii; ss; des; try match goal with [H: _ |- _] => inv_string H end|]));
  try (econs; fail).

Ltac combine_quant tm :=
  revert tm; first [apply combine_quant | apply combine_quant_dep].

Definition CRIS := "cris".
Global Opaque CRIS.

Ltac unfold_hmod :=
  match goal with
  | [|-context[?x]] => 
    match type of x with HMod.t =>
      rewrite {1}/x; try unseal CRIS
    end
  end.

Lemma ereplace T (x y: T):
  x = y -> x = y.
Proof. eauto. Qed.

Ltac alist_upd_simpl :=
  match goal with
  [ |- context[alist_upd ?k ?v ?l]] =>
    match l with
    | context[(k,?v0)] =>
      let TMP := fresh "_TMP" in
      let NODUP := fresh "NODUP" in
      match goal with [H: List.NoDup _|-_] =>
        eassert (TMP: List.NoDup (List.map fst l)) by (exact H); clear H; revert TMP
      end;
      erewrite (@ereplace _ l); [intros ?|Lauto_prepare; Lauto_find (k,v0); refl];
      eassert (NODUP := alist_upd_nodup k v _ TMP); revert NODUP;
      rewrite !(alist_upd_with_nodup _ _ _ _ _ TMP); clear TMP;
      Lauto_finish; intros ?
    end
  end.

Ltac move_aux :=
  (hrepeat do 1 match goal with [H: List.NoDup _ |- _ ] => guardH H; move H at top end);
  (hrepeat do 1 match goal with [H: Ist_monotone _ |- _ ] => guardH H; move H at top end);
  (hrepeat do 1 match goal with [H: incl _ (HMod.scopes _ _) |- _] => guardH H; move H at top end);
  (hrepeat do 1 match goal with [H: HMod.wf _ |- _ ] => guardH H; move H at top end);
  (hrepeat do 1 match goal with [H: ∀ _, sp_incl _ _ |- _ ] => guardH H; move H at top end);
  (hrepeat do 1 match goal with [H:=_:list (_ * (Any.t -> itree hmodE Any.t)) |- _ ] => guardH H; move H at top end);
  unguard.

Lemma fst_map_snd {A B C} f:
  (fst ∘ @map_snd A B C f) = fst.
Proof.
  extensionalities. destruct H. s. eauto.
Qed.

Ltac fnsems_nodup H :=
  revert H; simpl HMod.fnsems; (hrepeat do 1 unfold_hmod); simpl List.map;
  try rewrite !List.map_map; try rewrite !fst_map_snd; eauto; fail.

Ltac _alist_find_simpl :=
  match goal with
  [ |- context[alist_find ?k ?l]] =>
    let TMP := fresh "_TMP" in
    match goal with [H: List.NoDup _|-_] =>
      eassert (TMP: List.NoDup (List.map fst l))  by (fnsems_nodup H);
      revert TMP
    end;
    erewrite (@ereplace _ l); [intros ?
    | Lauto_normalize; try rewrite !List.map_app; simpl List.map; Lauto_prepare;
      match goal with [|-context[(?k',?v)]] => change k' with k; Lauto_find (k,v) end; refl];
    rewrite !alist_find_with_nodup; [|exact TMP]; clear TMP;
    Lauto_finish
  end.

Tactic Notation "alist_find_simpl_with" tactic(simpl_tac) :=
  let GOAL := fresh "GOAL" in
  match goal with [|-context [alist_find ?n ?x]] =>
    pattern (alist_find n x) at 1;
    match goal with [|- ?G _] => set (GOAL := G) end
  end;
  simpl HMod.fnsems; (hrepeat do 1 unfold_hmod; simpl HMod.fnsems);
  simpl_tac;
  unfold GOAL; clear GOAL.

Ltac alist_find_simpl := alist_find_simpl_with (do 1 _alist_find_simpl).

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
                        | HModSB.putSB scopes k v t
                        | HModSB.getSB scopes k k
                        | s
 *)

Inductive _hprogress := _hprogress_intro.

Ltac _hprogress prg :=
  try instantiate (1:= _hprogress_intro) in (value of prg).

Ltac _hprogress_check prg :=
  try (instantiate (1:= _hprogress_intro) in (value of prg); fail 1).

Tactic Notation "red_bind" hyp(prg) tactic(tac) :=
  lazymatch goal with
  | [ |- @ITree.bind _ _ _ ?itr ?ktr2 = _ ] =>
      lazymatch itr with
      | Ret _ => _hprogress prg; etransitivity; [ eapply bind_ret_l | s; tac ]
      | Tau _ => _hprogress prg; eapply bind_tau
      | vis _ _ => _hprogress prg; eapply vis_bind
      | assumeK _ _ => eapply assumeK_bind
      | guaranteeK _ _ => eapply guaranteeK_bind
      | unwrapUK _ _ => eapply unwrapUK_bind
      | unwrapNK _ _ => eapply unwrapNK_bind
      | SBRed.putSB _ _ _ _ => eapply SBRed.putSB_bind
      | SBRed.getSB _ _ _ => eapply SBRed.getSB_bind
      | @ITree.bind _ _ _ _ _ => eapply bind_bind
      | _ => reflexivity
      end
  end.

Tactic Notation "red_SB" hyp(prg) :=
  lazymatch goal with
  | [ |- @HModTr.sandbox _ _ _ ?itr = _ ] =>
      lazymatch itr with
      | Ret _ =>
          _hprogress prg; eapply SBRed.ret
      | Tau _ =>
          _hprogress prg; eapply SBRed.tau
      | vis (Assume _) _ =>
          _hprogress prg; eapply SBRed.vis_ag
      | vis (Guarantee _) _ =>
          _hprogress prg; eapply SBRed.vis_ag
      | vis (Spawn _ _) _ =>
          _hprogress prg; eapply SBRed.vis_sch
      | vis (Yield _) _ =>
          _hprogress prg; eapply SBRed.vis_sch
      | vis (Call _ _) _ =>
          _hprogress prg; eapply SBRed.vis_call
      | vis (SPut _ _) _ =>
          _hprogress prg; eapply SBRed.SPut_putSB
      | vis (SGet _) _ =>
          _hprogress prg; eapply SBRed.SGet_getSB
      | vis (Choose _) _ =>
          _hprogress prg; eapply SBRed.vis_core
      | vis (Take _) _ =>
          _hprogress prg; eapply SBRed.vis_core
      | vis (IO _ _) _ =>
          _hprogress prg; eapply SBRed.vis_core
      | assumeK _ _ =>
          _hprogress prg; eapply SBRed.assumeK
      | guaranteeK _ _ =>
          _hprogress prg; eapply SBRed.guaranteeK
      | unwrapUK _ _ =>
          _hprogress prg; eapply SBRed.unwrapUK
      | unwrapNK _ _ =>
          _hprogress prg; eapply SBRed.unwrapNK
      (* | Sch.spawnK_S _ _ _ _ =>
          _hprogress prg; eapply Sch.spawnK_S_transl
      | Sch.yieldK_S _ _ _ =>
          _hprogress prg; eapply Sch.yieldK_S_transl *)
      | @ITree.bind _ _ _ _ _ =>
          _hprogress prg; eapply SBRed.bind
      (* | Sch.joinK_S _ _ _ _ =>
          _hprogress prg; eapply Sch.joinK_S_transl *)
      | _ =>
          reflexivity
      end
  end.

Ltac unfold_sp_exact sp name :=
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
    end.

Tactic Notation "red_S" hyp(prg) tactic(tac) :=
  lazymatch goal with
  | [ |- @SModTr.trans ?Σ ?stb ?R ?itr = _ ] =>
      lazymatch itr with
      | Ret _ =>
          _hprogress prg; eapply SRed.ret
      | Tau _ =>
          _hprogress prg; eapply SRed.tau
      | vis (Assume _) _ =>
          _hprogress prg; eapply SRed.vis_ag
      | vis (Guarantee _) _ =>
          _hprogress prg; eapply SRed.vis_ag
      | vis (Spawn _ _) _ =>
          _hprogress prg; etransitivity;
          [ eapply SRed.vis_spawn
          | unfold SModTr.HoareSpawn;
            tac
          ]
      | vis (Yield _) _ =>
          _hprogress prg; etransitivity;
          [ eapply SRed.vis_yield
          | tac
          ]
      | vis (Call ?fn _) _ =>
          _hprogress prg; etransitivity;
          [ eapply SRed.vis_call
          | unfold SModTr.HoareCall;
            unfold_sp_exact stb fn;
            tac
          ]
      | vis (SPut _ _) _ =>
          _hprogress prg; eapply SRed.vis_pg
      | vis (SGet _) _ =>
          _hprogress prg; eapply SRed.vis_pg
      | vis (Choose _) _ =>
          _hprogress prg; eapply SRed.vis_core
      | vis (Take _) _ =>
          _hprogress prg; eapply SRed.vis_core
      | vis (IO _ _) _ =>
          _hprogress prg; eapply SRed.vis_core
      | assumeK _ _ =>
          _hprogress prg; eapply SRed.assumeK
      | guaranteeK _ _ =>
          _hprogress prg; eapply SRed.guaranteeK
      | unwrapUK _ _ =>
          _hprogress prg; eapply SRed.unwrapUK
      | unwrapNK _ _ =>
          _hprogress prg; eapply SRed.unwrapNK
      | @ITree.bind _ _ _ _ _ =>
          _hprogress prg; eapply SRed.bind
      | _ =>
          reflexivity
      end
  end.

Tactic Notation "red_P" hyp(prg) :=
  lazymatch goal with
  | [ |- @PModTr.trans _ _ ?itr = _ ] =>
      lazymatch itr with
      | Ret _ =>
          _hprogress prg; eapply PRed.ret
      | Tau _ =>
          _hprogress prg; eapply PRed.tau
      | vis (Spawn _ _) _ =>
          _hprogress prg; eapply PRed.vis_sch
      | vis (Yield _) _ =>
          _hprogress prg; eapply PRed.vis_sch
      | vis (Call _ _) _ =>
          _hprogress prg; eapply PRed.vis_call
      | vis (SPut _ _) _ =>
          _hprogress prg; eapply PRed.vis_pg
      | vis (SGet _) _ =>
          _hprogress prg; eapply PRed.vis_pg
      | vis (Choose _) _ =>
          _hprogress prg; eapply PRed.vis_choose
      | vis (Take _) _ =>
          _hprogress prg; eapply PRed.vis_take
      | vis (IO _ _) _ =>
          _hprogress prg; eapply PRed.vis_io
      | assumeK _ _ =>
          _hprogress prg; eapply PRed.assumeK
      | guaranteeK _ _ =>
          _hprogress prg; eapply PRed.guaranteeK
      | unwrapUK _ _ =>
          _hprogress prg; eapply PRed.unwrapUK
      | unwrapNK _ _ =>
          _hprogress prg; eapply PRed.unwrapNK
      | @ITree.bind _ _ _ _ _ =>
          _hprogress prg; eapply PRed.bind
      | _ =>
          reflexivity
      end
  end.

Ltac _hnorm_itr prg :=
  lazymatch goal with
  | [ |- Ret _ = _ ] =>
      reflexivity
  | [ |- Tau _ = _ ] =>
      reflexivity
  | [ |- vis _ _ = _ ] =>
      reflexivity
  | [ |- @ITree.bind ?E ?T ?U ?itr ?ktr = _ ] =>
      etransitivity;
      [ let itr' := fresh "itr" in cong (fun itr' => @ITree.bind E T U itr' ktr); _hnorm_itr prg | red_bind prg (do 1 _hnorm_itr prg) ]
  | [ |- @HModTr.sandbox ?Σ ?R ?scopes ?itr = _ ] =>
      etransitivity;
      [ cong (@HModTr.sandbox Σ R scopes); _hnorm_itr prg | red_SB prg ]
  | [ |- @SModTr.trans ?Σ ?stb ?R ?itr = _ ] =>
      etransitivity;
      [ cong (@SModTr.trans Σ stb R); _hnorm_itr prg | red_S prg (do 1 _hnorm_itr prg) ]
  | [ |- @PModTr.trans ?Σ ?R ?itr = _ ] =>
      etransitivity;
      [ cong (@PModTr.trans Σ R); _hnorm_itr prg | red_P prg ]
  | [ |- trigger _ = _ ] =>
      eapply trigger_vis
  | [ |- assume _ = _ ] =>
      eapply assume_assumeK
  | [ |- guarantee _ = _ ] =>
      eapply guarantee_guaranteeK
  | [ |- unwrapU _ = _ ] =>
      eapply unwrapU_unwrapUK
  | [ |- unwrapN _ = _ ] =>
      eapply unwrapN_unwrapNK
  | [ |- SModTr.HoareCall _ _ _ = _ ] =>
      _hprogress prg; unfold SModTr.HoareCall;
      _hnorm_itr prg
  | [ |- SModTr.HoareSpawn _ _ _ _ = _ ] =>
      _hprogress prg; unfold SModTr.HoareSpawn;
      _hnorm_itr prg
  | [ |- fbody_trivial _ = _ ] =>
      _hprogress prg; unfold fbody_trivial;
      _hnorm_itr prg
  | [ |- cput _ _ = _ ] =>
      _hprogress prg; unfold cput;
      _hnorm_itr prg
  | [ |- cgetU _ = _ ] =>
      _hprogress prg; unfold cgetU;
      _hnorm_itr prg
  | [ |- cgetN _ = _ ] =>
      _hprogress prg; unfold cgetN;
      _hnorm_itr prg
  | [ |- cfunU _ _ = _ ] =>
      _hprogress prg; unfold cfunU;
      _hnorm_itr prg
  | [ |- cfunN _ _ = _ ] =>
      _hprogress prg; unfold cfunN;
      _hnorm_itr prg
  | [ |- ccallU _ _ = _ ] =>
      _hprogress prg; unfold ccallU;
      _hnorm_itr prg
  | [ |- ccallN _ _ = _ ] =>
      _hprogress prg; unfold ccallN;
      _hnorm_itr prg
  | [ |- triggerUB = _ ] =>
      _hprogress prg; unfold triggerUB;
      _hnorm_itr prg
  | [ |- triggerNB = _ ] =>
      _hprogress prg; unfold triggerNB;
      _hnorm_itr prg
  | [ |- ?itr = _ ] =>
      reflexivity
  end.

Ltac hnorm_itr :=
  try match goal with
  | [ |- @ITree.bind _ _ _ (trigger _) _ = _ ] => fail 2
  | [ |- @ITree.bind _ _ _ (@HModTr.sandbox _ _ _ (trigger (SPut _ _))) _ = _ ] => fail 2
  | [ |- @ITree.bind _ _ _ (@HModTr.sandbox _ _ _ (trigger (SGet _))) _ = _ ] => fail 2
  end;
  let prg := fresh "Progress" in
  epose (prg := _ : _hprogress);
  etransitivity;
  [ _hnorm_itr prg
  | _hprogress_check prg; s;
    lazymatch goal with
    | [ |- Ret _ = _ ] =>
        reflexivity
    | [ |- Tau _ = _ ] =>
        reflexivity
    | [ |- vis _ _ = _ ] =>
        eapply vis_trigger
    | [ |- assumeK _ _ = _ ] =>
        eapply assumeK_assume
    | [ |- guaranteeK _ _ = _ ] =>
        eapply guaranteeK_guarantee
    | [ |- unwrapUK _ _ = _ ] =>
        eapply unwrapUK_unwrapU
    | [ |- unwrapNK _ _ = _ ] =>
        eapply unwrapNK_unwrapN
    | [ |- SBRed.putSB _ _ _ _ = _ ] =>
        eapply SBRed.putSB_SPut
    | [ |- SBRed.getSB _ _ _ = _ ] =>
        eapply SBRed.getSB_SGet
    | [ |- _ = _ ] =>
        reflexivity
    end
  ].

Ltac iIntrosFresh H := iIntros H || iIntrosFresh (H ++ "'")%string.

Ltac des_pairs :=
  (hrepeat do 1
    match goal with
    | [H: context[let () := ?x in _] |- _] =>
        match type of x with
        | () => destruct x
        | (_ * _)%type =>
            let n0 := fresh "q" in let n1 := fresh "q" in
            let EQ := fresh "EQq" in
            destruct x as [n0 n1] eqn: EQ
        end
    | |- context[let () := ?x in _] =>
        match type of x with
        | () => destruct x
        | (_ * _)%type =>
            let n0 := fresh "q" in let n1 := fresh "q" in
            let EQ := fresh "EQq" in
            destruct x as [n0 n1] eqn: EQ
        end
    end);
   subst.

Ltac has_precond_in TM :=
  match goal with [H := ?P |- _] => match H with TM => match P with context[precond] => idtac end end end.
Ltac has_postcond_in TM :=
  match goal with [H := ?P |- _] => match H with TM => match P with context[postcond] => idtac end end end.
Ltac unfold_precond_postcond term := let TM := fresh "_term" in
  set (TM := term) at 1;
  (hrepeat do 1 (has_precond_in TM; unfold precond in TM; simpl in TM));
  (hrepeat do 1 (has_postcond_in TM; unfold postcond in TM; simpl in TM));
  subst TM;
  try rewrite -/(precond _); try rewrite -/(postcond _).

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

Ltac hide_itree_l :=
  let ITREE := fresh "ITREE" in
  match goal with [|- _ (_ (_, ?it) _)] => set (ITREE := it) at 1 end.

Ltac hide_itree_r :=
  let ITREE := fresh "ITREE" in
  match goal with
  [|- _ (_ _ (_, ?it))] => first [set (ITREE := it) at 2|set (ITREE := it) at 1]
  end.

Ltac show_itree :=
  match goal with [H:_|-_] => unfold H; clear H end.

Ltac show_until marker :=
  (hrepeat do 1 match goal with
      [H: _ |- _] =>
        try match H with marker => fail 3 end;
        first [unfold H; clear H | revert H]
    end);
  clear marker; i.

Ltac unfold_cris_defs :=
  (hrepeat do 1 match goal with
  | [|- context[{| fsb_body := cfunU ?x |}]] => rewrite {1}/x
  | [|- context[{| fsb_body := cfunN ?x |}]] => rewrite {1}/x
  | [|- context[{| fsb_body := ?x |}]] => rewrite {1}/x
  | [|- context[PModTr.trans (?x _)]] => unfold x
  | [|- context[cfunU ?x]] => rewrite {1}/x
  | [|- context[cfunN ?x]] => rewrite {1}/x
  end);
  unfold SModTr.trans_ktree, SModTr.HoareFun, cfunU, cfunN, HModTr.sandbox_body; s.  

Ltac hide_flist :=
  let FLS := fresh "FLS" in let FLT := fresh "FLT" in
  match goal with [|- context[(isim_fsem ?fls ?flt _ _)]] =>
    set (FLS := fls); set (FLT := flt)
  end.

Ltac kill_trivial :=
  match goal with |-?T => match type of T with Prop => econs; fail end end.

Ltac clear_trivials :=
  (hrepeat do 1
   lazymatch goal with H: ?T |-_ =>
     revert H; 
     try match type of T with Prop =>
       let TMP := fresh "TMP" in
       assert (TMP: T) by (econs; fail); clear TMP; intros []; []
     end
   end);
  i.

Ltac pre_simF :=
  clear_trivials;
  unfold HSim.sim_fun; i;
  match goal with [H: _|-_] => revert H end;
  hide_flist.

Ltac post_simF :=
  eexists; split; [eauto|];
  unfold_cris_defs;
  ii; subst; iIntros "IST";
  move_aux.

Ltac initialize_simF :=
  pre_simF;
  alist_find_simpl;
  let H := fresh "H" in intro H; inv H;
  alist_find_simpl;
  post_simF.

Ltac prove_sub_perm :=  
  i; try rewrite /HMod.scopes; s; (hrepeat do 1 unfold_hmod); s;
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

Ltac prove_inline_cond :=
  first [eassumption |
  match goal with [|- alist_find _ ?FL = _] =>
    rewrite /FL;
    simpl HMod.fnsems; (hrepeat do 1 unfold_hmod);
    simpl List.map; alist_find_simpl; eauto
  end].

Ltac unfold_iter_l :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_r;
  rewrite unfold_iter_eq;
  show_until marker.

Ltac unfold_iter_r :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_l;
  rewrite unfold_iter_eq;
  show_until marker.

Ltac unfold_pre_post :=
  hrepeat do 1 match goal with
  | |-context[precond] => rewrite /precond; s
  | |-context[postcond] => rewrite /postcond; s
  end.

(** hss, hss_l, hss_r : simplify itrees **)

Ltac hss_des :=
  ss; des_safe; subst;
  (hrepeat do 1 match goal with
    | [v: () |- _] => destruct v
    | [H: (_,_) = (_,_) |- _] => inv H
    end);
  ss.

Ltac hss :=
  (hrepeat do 1 match goal with [|- context[environments.Esnoc _ ?H (bi_pure True)]] => iClear H end);
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
  (hrepeat do 1 alist_upd_simpl);
  hss_des;
  move_aux.

Ltac hss_l := hide_itree_r; hss; show_itree.
Ltac hss_r := hide_itree_l; hss; show_itree.

Ltac red_ret_l :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_r;
  rewrite ?PRed.bind ?PRed.ret ?SRed.bind ?SRed.ret SBRed.bind SBRed.ret bind_ret_l;
  show_until marker.
 
Ltac red_ret_r :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_l;
  rewrite ?PRed.bind ?PRed.ret ?SRed.bind ?SRed.ret SBRed.bind SBRed.ret bind_ret_l;
  show_until marker.

Tactic Notation "add_ret_l" uconstr(r) :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_r;
  match goal with [|-_ _ (_ (_,?t) _)] =>
    rewrite -(bind_ret_l r (fun _ => t))
  end;
  show_until marker.

Tactic Notation "add_ret_r" uconstr(r) :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_l;
  match goal with [|-_ _ (_ _ (_,?t))] =>
    rewrite -(bind_ret_l r (fun _ => t))
  end;
  show_until marker.
