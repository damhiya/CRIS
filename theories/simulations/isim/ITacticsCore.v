Require Import Common.
Require Import LAuto.

Require Import Spc Mod SMod HMod PMod.
Require Import HPSim ISimCore.

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

Ltac by_coind CIH :=
  iApply isim_progress; iApply isim_base;
  iSpecialize (CIH $! _);
  (hrepeat do 1 first[instantiate (1:= (_,_))|instantiate (1:= existT _ _)]); s;
  iApply CIH.

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
      rewrite !alist_upd_with_nodup; [|exact TMP]; clear TMP;
      Lauto_finish; intros ?
    end
  end.

Ltac move_aux :=
  (hrepeat do 1 match goal with [H: List.NoDup _ |- _ ] => guardH H; move H at top end);
  (hrepeat do 1 match goal with [H: Ist_monotone _ |- _ ] => guardH H; move H at top end);
  (hrepeat do 1 match goal with [H: incl _ (HMod.scopes _ _) |- _] => guardH H; move H at top end);
  (hrepeat do 1 match goal with [H: HMod.wf _ |- _ ] => guardH H; move H at top end);
  (hrepeat do 1 match goal with [H: ∀ _, spc_incl _ _ |- _ ] => guardH H; move H at top end);
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

Ltac hss_des :=
  ss; des_safe; subst;
  (hrepeat do 1 match goal with
    | [v: () |- _] => destruct v
    | [H: (_,_) = (_,_) |- _] => inv H
    end);
  ss.

Ltac hss :=
  hss_des;
  try (rewrite -> !Any.pair_split in * );
  try (rewrite -> !Any.upcast_downcast in * );
  (hrepeat do 1 match goal with [G: Any.downcast _ = Some _ |-_] =>
    apply Any.downcast_upcast in G; inv G; ss
   end);
  (hrepeat do 1 match goal with [G: Any.upcast _ = Any.upcast _ |-_] =>
    apply Any.upcast_inj in G; destruct G as [_ G]; red in G; depdes G; ss
   end);
  (hrepeat do 1 match goal with [G: Some _ = Some _ |- _] =>
    depdes G; ss
  end);
  try (rewrite -> !Any.pair_split in * );
  try (rewrite -> !Any.upcast_downcast in * );
  (hrepeat do 1 alist_upd_simpl);
  hss_des;
  move_aux.

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
  | [ |- @ITree.bind _ _ _ ?itr _ = _ ] =>
      lazymatch itr with
      | Ret _ => _hprogress prg; etransitivity; [ eapply bind_ret_l | s; tac ]
      | Tau _ => _hprogress prg; eapply bind_tau
      | vis _ _ => _hprogress prg; eapply vis_bind
      | assumeK _ _ => eapply assumeK_bind
      | guaranteeK _ _ => eapply guaranteeK_bind
      | unwrapUK _ _ => eapply unwrapUK_bind
      | unwrapNK _ _ => eapply unwrapNK_bind
      | HModSB.putSB _ _ _ _ => eapply HModSB.putSB_bind
      | HModSB.getSB _ _ _ => eapply HModSB.getSB_bind
      | _ => reflexivity
      end
  end.

Tactic Notation "red_SB" hyp(prg) :=
  lazymatch goal with
  | [ |- @HMod.sandbox _ _ _ ?itr = _ ] =>
      lazymatch itr with
      | Ret _ =>
          _hprogress prg; eapply HModSB.transl_ret
      | Tau _ =>
          _hprogress prg; eapply HModSB.transl_tau
      | vis (Assume _) _ =>
          _hprogress prg; eapply HModSB.transl_vis_ag
      | vis (Guarantee _) _ =>
          _hprogress prg; eapply HModSB.transl_vis_ag
      | vis (Spawn _ _) _ =>
          _hprogress prg; eapply HModSB.transl_vis_sch
      | vis (Yield _) _ =>
          _hprogress prg; eapply HModSB.transl_vis_sch
      | vis Tid _ =>
          _hprogress prg; eapply HModSB.transl_vis_sch
      | vis (Call _ _) _ =>
          _hprogress prg; eapply HModSB.transl_vis_call
      | vis (SPut _ _) _ =>
          _hprogress prg; eapply HModSB.SPut_putSB
      | vis (SGet _) _ =>
          _hprogress prg; eapply HModSB.SGet_getSB
      | vis (Choose _) _ =>
          _hprogress prg; eapply HModSB.transl_vis_core
      | vis (Take _) _ =>
          _hprogress prg; eapply HModSB.transl_vis_core
      | vis (IO _ _) _ =>
          _hprogress prg; eapply HModSB.transl_vis_core
      | assumeK _ _ =>
          _hprogress prg; eapply HModSB.transl_assumeK
      | guaranteeK _ _ =>
          _hprogress prg; eapply HModSB.transl_guaranteeK
      | unwrapUK _ _ =>
          _hprogress prg; eapply HModSB.transl_unwrapUK
      | unwrapNK _ _ =>
          _hprogress prg; eapply HModSB.transl_unwrapNK
      | _ =>
          reflexivity
      end
  end.

Ltac unfold_spc_exact spc name :=
  try match goal with
      [ H : spc_incl _ spc |- _ ] =>
        let RW := fresh "_RW" in
        let ND := fresh "_ND" in
        edestruct H as [ND RW];
        erewrite (RW name);
        [| revert ND; unfold to_spc;
           match goal with [|-context[alist_find _ ?x]] => rewrite /x end;
           unseal CRIS; i;
           alist_find_simpl;
           refl];
        simpl unwrapN; clear ND RW
    end.

Tactic Notation "red_S" hyp(prg) tactic(tac) :=
  lazymatch goal with
  | [ |- @interp_smod ?Σ ?ginv ?stb ?R ?itr = _ ] =>
      lazymatch itr with
      | Ret _ =>
          _hprogress prg; eapply SModRed.interp_ret
      | Tau _ =>
          _hprogress prg; eapply SModRed.interp_tau
      | vis (Assume _) _ =>
          _hprogress prg; eapply SModRed.interp_vis_ag
      | vis (Guarantee _) _ =>
          _hprogress prg; eapply SModRed.interp_vis_ag
      | vis (Spawn _ _) _ =>
          _hprogress prg; etransitivity;
          [ eapply SModRed.interp_vis_sch
          | unfold handle_schE_hmodE;
            unfold HoareSpawn;
            tac
          ]
      | vis (Yield _) _ =>
          _hprogress prg; etransitivity;
          [ eapply SModRed.interp_vis_sch
          | unfold handle_schE_hmodE;
            unfold HoareYield;
            tac
          ]
      | vis Tid _ =>
          _hprogress prg; etransitivity;
          [ eapply SModRed.interp_vis_sch
          | unfold handle_schE_hmodE;
            tac
          ]
      | vis (Call ?fn _) _ =>
          _hprogress prg; etransitivity;
          [ eapply SModRed.interp_vis_call
          | unfold handle_callE_hmodE;
            unfold HoareCall;
            unfold_spc_exact stb fn;
            tac
          ]
      | vis (SPut _ _) _ =>
          _hprogress prg; eapply SModRed.interp_vis_pg
      | vis (SGet _) _ =>
          _hprogress prg; eapply SModRed.interp_vis_pg
      | vis (Choose _) _ =>
          _hprogress prg; eapply SModRed.interp_vis_core
      | vis (Take _) _ =>
          _hprogress prg; eapply SModRed.interp_vis_core
      | vis (IO _ _) _ =>
          _hprogress prg; eapply SModRed.interp_vis_core
      | assumeK _ _ =>
          _hprogress prg; eapply SModRed.interp_assumeK
      | guaranteeK _ _ =>
          _hprogress prg; eapply SModRed.interp_guaranteeK
      | unwrapUK _ _ =>
          _hprogress prg; eapply SModRed.interp_unwrapUK
      | unwrapNK _ _ =>
          _hprogress prg; eapply SModRed.interp_unwrapNK
      | _ =>
          reflexivity
      end
  end.

Tactic Notation "red_P" hyp(prg) :=
  lazymatch goal with
  | [ |- @PMod.interp _ _ ?itr = _ ] =>
      lazymatch itr with
      | Ret _ =>
          _hprogress prg; eapply PModRed.interp_ret
      | Tau _ =>
          _hprogress prg; eapply PModRed.interp_tau
      | vis (Spawn _ _) _ =>
          _hprogress prg; eapply PModRed.interp_vis_sch
      | vis (Yield _) _ =>
          _hprogress prg; eapply PModRed.interp_vis_sch
      | vis Tid _ =>
          _hprogress prg; eapply PModRed.interp_vis_sch
      | vis (Call _ _) _ =>
          _hprogress prg; eapply PModRed.interp_vis_call
      | vis (SPut _ _) _ =>
          _hprogress prg; eapply PModRed.interp_vis_pg
      | vis (SGet _) _ =>
          _hprogress prg; eapply PModRed.interp_vis_pg
      | vis (Choose _) _ =>
          _hprogress prg; eapply PModRed.interp_vis_choose
      | vis (Take _) _ =>
          _hprogress prg; eapply PModRed.interp_vis_take
      | vis (IO _ _) _ =>
          _hprogress prg; eapply PModRed.interp_vis_io
      | assumeK _ _ =>
          _hprogress prg; eapply PModRed.interp_assumeK
      | guaranteeK _ _ =>
          _hprogress prg; eapply PModRed.interp_guaranteeK
      | unwrapUK _ _ =>
          _hprogress prg; eapply PModRed.interp_unwrapUK
      | unwrapNK _ _ =>
          _hprogress prg; eapply PModRed.interp_unwrapNK
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
  | [ |- @HMod.sandbox ?Σ ?R ?scopes ?itr = _ ] =>
      etransitivity;
      [ cong (@HMod.sandbox Σ R scopes); _hnorm_itr prg | red_SB prg ]
  | [ |- @interp_smod ?Σ ?ginv ?stb ?R ?itr = _ ] =>
      etransitivity;
      [ cong (@interp_smod Σ ginv stb R); _hnorm_itr prg | red_S prg (do 1 _hnorm_itr prg) ]
  | [ |- @PMod.interp ?Σ ?R ?itr = _ ] =>
      etransitivity;
      [ cong (@PMod.interp Σ R); _hnorm_itr prg | red_P prg ]
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
  | [ |- HoareCall _ _ _ = _ ] =>
      _hprogress prg; unfold HoareCall;
      _hnorm_itr prg
  | [ |- HoareSpawn _ _ _ _ = _ ] =>
      _hprogress prg; unfold HoareSpawn;
      _hnorm_itr prg
  | [ |- HoareYield _ _ = _ ] =>
      _hprogress prg; unfold HoareYield;
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
    | [ |- HModSB.putSB _ _ _ _ = _ ] =>
        eapply HModSB.putSB_SPut
    | [ |- HModSB.getSB _ _ _ = _ ] =>
        eapply HModSB.getSB_SGet
    | [ |- _ = _ ] =>
        reflexivity
    end
  ].

Ltac replace_l :=
  lazymatch goal with
  | [ |- environments.envs_entails ?env (isim ?fl_src ?tl_tgt ?Ist ?my_tid ?is_closed ?r ?g ?RR ?ps ?pt ?nths (?st_src, ?itr_src) (?st_tgt, ?itr_tgt)) ] =>
      refine (eq_ind_r (fun itr_src' => environments.envs_entails env (isim fl_src tl_tgt Ist my_tid is_closed r g RR ps pt nths (st_src, itr_src') (st_tgt, itr_tgt))) _ _); cycle 1
  end.

Ltac replace_r :=
  lazymatch goal with
  | [ |- environments.envs_entails ?env (isim ?fl_src ?tl_tgt ?Ist ?my_tid ?is_closed ?r ?g ?RR ?ps ?pt ?nths (?st_src, ?itr_src) (?st_tgt, ?itr_tgt)) ] =>
      refine (eq_ind_r (fun itr_tgt' => environments.envs_entails env (isim fl_src tl_tgt Ist my_tid is_closed r g RR ps pt nths (st_src, itr_src) (st_tgt, itr_tgt'))) _ _); cycle 1
  end.

Ltac hnorm_l := replace_l; [s; hnorm_itr|].
Ltac hnorm_r := replace_r; [s; hnorm_itr|].

(***
  Step-level tactics
 ***)

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

Ltac desugar itr :=
  match itr with
  | fbody_trivial _ => rewrite {1}/itr
  | HoareCall _ _ _ => rewrite {1}/itr
  | HoareSpawn _ _ _ => rewrite {1}/itr
  | HoareYield _ _ => rewrite {1}/itr
  | cput _ _ => rewrite{1}/itr
  | cgetU _ => rewrite{1}/itr
  | cgetN _ => rewrite{1}/itr
  | triggerUB => rewrite{1}/itr
  | triggerNB => rewrite{1}/itr
  end.

Ltac _unwrapSB itr :=
  match itr with
  | Ret _ =>
      rewrite HModSB.transl_ret
  | tau;; _ =>
      rewrite HModSB.transl_tau
  | trigger (Choose _) => 
      rewrite HModSB.transl_core
  | trigger (Take _) => 
      rewrite HModSB.transl_core
  | trigger (IO _ _) => 
      rewrite HModSB.transl_core  
  | trigger (Call _ _) =>
      rewrite HModSB.transl_call
  | trigger (SPut _ _) =>
      idtac
  | trigger (SGet _) =>
      idtac
  | trigger (Assume _) => 
      rewrite HModSB.transl_ag
  | trigger (Guarantee _) => 
      rewrite HModSB.transl_ag
  | unwrapU _ =>
      rewrite HModSB.transl_unwrapU
  | unwrapN _ =>
      rewrite HModSB.transl_unwrapN
  | assume _ =>
      rewrite HModSB.transl_asm
  | guarantee _ =>
      rewrite HModSB.transl_guar
  | trigger (Spawn _ _) =>
      rewrite HModSB.transl_sch
  | trigger (Yield _) =>
      rewrite HModSB.transl_sch
  | trigger Tid =>
      rewrite HModSB.transl_sch
  | _ => fail
  end.

Ltac unwrapSB :=
  try match goal with
  | [|-context[HMod.sandbox _ ?itr]] => first [desugar itr|fail 2]
  end;
  match goal with
  | [|-context[HMod.sandbox _ (?itr >>= _)]] =>
      rewrite HModSB.transl_bind; unwrapSB
  | [|-context[HMod.sandbox _ ?itr]] => first [_unwrapSB itr|fail 2]
  end.

Ltac _unwrapS itr :=
  match itr with
  | Ret _ =>
      rewrite SModRed.interp_ret
  | tau;; _ =>
      rewrite SModRed.interp_tau
  | trigger (Choose _) => 
      rewrite SModRed.interp_core
  | trigger (Take _) => 
      rewrite SModRed.interp_core
  | trigger (IO _ _) => 
      rewrite SModRed.interp_core  
  | trigger (Call _ _) =>
      rewrite SModRed.interp_call {1}/handle_callE_hmodE
  | trigger (Spawn _ _) =>
      rewrite SModRed.interp_sch {1}/handle_schE_hmodE
  | trigger (Yield _) =>
      rewrite SModRed.interp_sch {1}/handle_schE_hmodE
  | trigger Tid =>
      rewrite SModRed.interp_sch {1}/handle_schE_hmodE
  | trigger (SPut _ _) =>
      rewrite SModRed.interp_pg
  | trigger (SGet _) =>
      rewrite SModRed.interp_pg
  | trigger (Assume _) => 
      rewrite SModRed.interp_ag
  | trigger (Guarantee _) => 
      rewrite SModRed.interp_ag
  | unwrapU _ =>
      rewrite SModRed.interp_unwrapU
  | unwrapN _ =>
      rewrite SModRed.interp_unwrapN
  | assume _ =>
      rewrite SModRed.interp_asm
  | guarantee _ =>
      rewrite SModRed.interp_guar
  | _ => fail
  end.

Ltac unwrapS :=
  try match goal with
    | [|-context[interp_smod _ _ ?itr]] => first [desugar itr|fail 2]
  end;
  match goal with
  | [|-context[interp_smod _ _ (?itr >>= _)]] =>
      rewrite SModRed.interp_bind; unwrapS
  | [|-context[interp_smod _ _ ?itr]] => first [_unwrapS itr|fail 2]
  end.

Ltac _unwrapP itr :=
  match itr with
  | Ret _ =>
      rewrite PModRed.interp_ret
  | tau;; _ =>
      rewrite PModRed.interp_tau
  | trigger (Choose _) => 
      rewrite PModRed.interp_choose
  | trigger (Take _) => 
      rewrite PModRed.interp_take
  | trigger (IO _ _) => 
      rewrite PModRed.interp_io
  | trigger (Call _ _) =>
      rewrite PModRed.interp_call
  | trigger (Spawn _ _) =>
      rewrite PModRed.interp_sch
  | trigger (Yield _) =>
      rewrite PModRed.interp_sch
  | trigger Tid =>
      rewrite PModRed.interp_sch
  | trigger (SPut _ _) =>
      rewrite PModRed.interp_pg
  | trigger (SGet _) =>
      rewrite PModRed.interp_pg
  | unwrapU _ =>
      rewrite PModRed.interp_unwrapU
  | unwrapN _ =>
      rewrite PModRed.interp_unwrapN
  | assume _ =>
      rewrite PModRed.interp_asm
  | guarantee _ =>
      rewrite PModRed.interp_guar
  | _ => fail
  end.

Ltac unwrapP :=
  try match goal with
  | [|-context[PMod.interp ?itr]] => first [desugar itr|fail 2]
  end;
  match goal with
  | [|-context[PMod.interp (?itr >>= _)]] =>
      rewrite PModRed.interp_bind; unwrapP
  | [|-context[PMod.interp ?itr]] => first [_unwrapP itr|fail 2]
  end.

Ltac has_precond_in TM :=
  match goal with [H := ?P |- _] => match H with TM => match P with context[precond] => idtac end end end.
Ltac has_postcond_in TM :=
  match goal with [H := ?P |- _] => match H with TM => match P with context[postcond] => idtac end end end.
Ltac unfold_precond_postcond term := let TM := fresh "_term" in
  set (TM := term) at 1;
  (hrepeat do 1 (has_precond_in TM; unfold precond in TM; simpl in TM));
  (hrepeat do 1 (has_postcond_in TM; unfold postcond in TM; simpl in TM));
  subst TM.

Ltac _step_l :=
  match goal with
  (******* isim ******)
  (** src **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, tau;; _) _) ] =>
      iApply isim_tau_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, Ret _ >>= _) _) ] =>
      rewrite bind_ret_l
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, (HMod.sandbox _ (trigger (SPut _ _))) >>= _) _) ] =>
      iApply isim_sput_src_sandbox; [s;eauto|]
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, (HMod.sandbox _ (trigger (SGet _))) >>= _) _) ] =>
      iApply isim_sget_src_sandbox; [s;eauto|]
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _) _) ] =>
      let name := fresh "q" in
      iApply isim_take_src; iIntros (name)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _  (_, trigger (Assume ?P) >>= _) _) ] =>
      unfold_precond_postcond P; iApply isim_Assume_src; iIntrosFresh "ASM"
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) _) ] =>
      let name := fresh "q" in
      iApply isim_unwrapU_src; iIntros (name) "%";
      match goal with [ H: ?x = Some _ |- _ ] => let G := fresh "G" in rename H into G; try rewrite -> G in * end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, assume _ >>= _) _) ] =>
      let name := fresh "asm" in iApply isim_asm_src; iIntros (name)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, trigger Tid >>= _) _) ] =>
      iApply isim_tid_src
  end.

Ltac _step_r :=
  match goal with
  (******* isim ******)
  (** tgt **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, Ret _ >>= _)) ] =>
      rewrite bind_ret_l
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, tau;; _)) ] =>
      iApply isim_tau_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, (HMod.sandbox _ (trigger (SPut _ _))) >>= _)) ] =>
      iApply isim_sput_tgt_sandbox; [s; eauto|]
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, (HMod.sandbox _ (trigger (SGet _))) >>= _)) ] =>
      iApply isim_sget_tgt_sandbox; [s; eauto|]
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose _) >>= _)) ] =>
      let name := fresh "q" in
      iApply isim_choose_tgt; iIntros (name)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _)) ] =>
      unfold_precond_postcond P; iApply isim_Guarantee_tgt; iIntrosFresh "GRT"
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, unwrapN ?ox >>= _)) ] =>
      let name := fresh "q" in
      iApply isim_unwrapN_tgt; iIntros (name) "%";
      match goal with [ H: ?x = Some _ |- _ ] => let G := fresh "G" in rename H into G; try rewrite -> G in * end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, guarantee _ >>= _)) ] =>
      let name := fresh "grt" in iApply isim_guar_tgt; iIntros (name)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger Tid >>=  _)) ] =>
      iApply isim_tid_tgt
  end.

Ltac _step :=
  match goal with
  (******* isim ******)
  (** both **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, Ret _) (_, Ret _)) ] =>
      iApply isim_ret
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (IO _ _) >>= _) (_, trigger (IO _ _) >>= _)) ] =>
      iApply isim_io; iIntros "%"
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Spawn _ _) >>= _) (_, trigger (Spawn _ _) >>= _)) ] =>
      iApply isim_spawn
  end.

Ltac _force_l :=
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose ?T) >>= _) _) ] =>
      iApply isim_choose_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _) _) ] =>
      unfold_precond_postcond P; iApply isim_Guarantee_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, unwrapN _ >>= _) _) ] =>
      iApply isim_unwrapN_src; iExists _
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, guarantee _ >>= _) _) ] =>
      iApply isim_guar_src
  end
.

Ltac _force_r :=
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _)) ] =>
      iApply isim_take_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Assume ?P) >>= _)) ] =>
      unfold_precond_postcond P; iApply isim_Assume_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, unwrapU _ >>= _)) ] =>
      iApply isim_unwrapU_tgt; iExists _
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, assume _ >>= _)) ] =>
      iApply isim_asm_tgt
  end
.

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

Ltac show_itree :=
  match goal with [H:_|-_] => unfold H; clear H end.

Ltac hide_itree_l :=
  match goal with [|- _ (_ (_, ?it) _)] => set (IT := it) at 1 end.

Ltac hide_itree_r :=
  match goal with [|- _ (_ _ (_, ?it))] => first [set (IT := it) at 2|set (IT := it) at 1] end.

Ltac show_until marker :=
  (hrepeat do 1 match goal with
      [H: _ |- _] =>
        try match H with marker => fail 3 end;
        first [unfold H; clear H | revert H]
    end);
  clear marker; i.

Ltac unfold_spc :=
  try match goal with
    [|-context[unwrapN (?spc ?name)]] =>
      try match goal with
        [H: context[spc_incl _ spc]|-_] =>
          let RW := fresh "_RW" in let ND := fresh "_ND" in
          edestruct H as [ND RW];
          erewrite (RW name);
          [|revert ND; unfold to_spc;
            match goal with [|-context[alist_find _ ?x]] => rewrite /x end;
            unseal CRIS; i;
            alist_find_simpl;
            refl];
          simpl unwrapN; clear ND RW
      end
  end.

Ltac _prep :=
  first
    [ unwrapSB
    | unwrapS; unfold_spc; unwrapSB
    | unwrapP; unwrapSB
    | idtac].

Ltac prep :=
  try rewrite !bind_bind;
  try match goal with
  | [|-context[interp_smod _ _ (?f ?arg)]] =>
    match type of arg with Any.t => rewrite {1}/f end
  | [|-context[PMod.interp (?f ?arg)]] =>
    match type of arg with Any.t => rewrite {1}/f end
  end;
  unfold ccallU, ccallN;
  try match goal with
      | [|-context[(_, HMod.sandbox _ _)]] => _prep
      | [|-context[(_, HMod.sandbox _ _ >>= _)]] => _prep
      end;
  try rewrite !bind_bind;
  try rewrite !bind_tau.

Ltac prep_l :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_r;
  prep;
  show_until marker.

Ltac prep_r :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_l;
  prep;
  show_until marker.

Ltac step_l_core :=
  _step_l; try alist_find_simpl; s; des_pairs; s.

Ltac step_l :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  (hrepeat do 1 hnorm_l);
  try step_l_core;
  show_until marker.

Ltac steps_l :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  (hrepeat do 1 tryany (do 1 hnorm_l) (do 1 step_l_core)); try hnorm_l;
  show_until marker.

Ltac step_r_core :=
  _step_r; try alist_find_simpl; s; des_pairs; s.

Ltac step_r :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  (hrepeat do 1 hnorm_r);
  try step_r_core;
  show_until marker.

Ltac steps_r :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  (hrepeat do 1 tryany (do 1 hnorm_r) (do 1 step_r_core)); try hnorm_r;
  show_until marker.

Ltac step :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  (hrepeat do 1 hnorm_l);
  (hrepeat do 1 hnorm_r);
  _step;
  s; des_pairs; s;
  show_until marker.

Ltac force_l_core :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  (hrepeat do 1 hnorm_l);
  _force_l; s;
  show_until marker.

Tactic Notation "force_l" :=
  force_l_core; try (iExists _).

Tactic Notation "force_l" uconstr(p) :=
  force_l_core; iExists p.

Ltac forces_l :=
  hrepeat do 1 force_l.

Ltac force_r_core :=
  let marker := fresh "MARKER" in
  set_marker marker;  
  hide_ihyps;
  (hrepeat do 1 hnorm_r);
  _force_r; s;
  show_until marker.

Tactic Notation "force_r" :=
  force_r_core; try (iExists _).

Tactic Notation "force_r" uconstr(p) :=
  force_r_core; iExists p.

Ltac forces_r := hrepeat do 1 force_r.

Ltac unfold_cris_defs :=
  (hrepeat do 1 match goal with
  | [|- context[{| fsb_body := cfunU ?x |}]] => rewrite {1}/x
  | [|- context[{| fsb_body := cfunN ?x |}]] => rewrite {1}/x
  | [|- context[{| fsb_body := ?x |}]] => rewrite {1}/x
  | [|- context[PMod.interp (?x _)]] => unfold x
  | [|- context[cfunU ?x]] => rewrite {1}/x
  | [|- context[cfunN ?x]] => rewrite {1}/x
  end);
  unfold interp_sb_hp, HoareFun, cfunU, cfunN, HMod.sandbox_body; s.  

Ltac prove_inline_cond :=
  match goal with [|- alist_find _ ?FL = _] =>
    rewrite /FL;
    simpl HMod.fnsems; (hrepeat do 1 unfold_hmod);
    simpl List.map; alist_find_simpl; eauto
  end.

Ltac inline_l :=
  let marker := fresh "MARKER" in
  set_marker marker;  
  hide_ihyps;
  (hrepeat do 1 hnorm_l);
  iApply isim_inline_src; [prove_inline_cond|];
  unfold_cris_defs;
  show_until marker.
  
Ltac inline_r :=
  let marker := fresh "MARKER" in
  set_marker marker;  
  hide_ihyps;
  (hrepeat do 1 hnorm_r);
  iApply isim_inline_tgt; [prove_inline_cond|];
  unfold_cris_defs;
  show_until marker.

Ltac call hyps :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  (hrepeat do 1 hnorm_l);
  (hrepeat do 1 hnorm_r);
  iApply isim_call;
  show_until marker;
  iSplitL hyps; [ |iIntros "% % % % % %"; iIntrosFresh "IST"];
  move_aux.

Ltac yield hyps :=
  let marker := fresh "MARKER" in
  set_marker marker;  
  hide_ihyps;
  (hrepeat do 1 hnorm_l);
  (hrepeat do 1 hnorm_r);
  iApply isim_yield;
  show_until marker;
  iSplitL hyps; [ |iIntros "% % % % %"; iIntrosFresh "IST"];
  move_aux.

Ltac hide_flist :=
  let FLS := fresh "FLS" in let FLT := fresh "FLT" in
  match goal with [|- context[(isim_fsem ?fls ?flt _ _)]] =>
    set (FLS := fls); set (FLT := flt)
  end.

Ltac pre_simF :=
  unfold HSim.sim_fun; i;
  match goal with [H: _|-_] => revert H end;
  hide_flist.

Ltac post_simF :=
  eexists; split; [eauto|];
  unfold_cris_defs;
  ii; subst; iIntros "IST";
  move_aux.

Ltac init_simF :=
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

(**** TODO ****)
(* A tactic to handle meta variables *)

(************ User Notations **************)

From iris.proofmode Require Import coq_tactics environments.

Global Arguments Envs _ _%_proof_scope _%_proof_scope _.
Global Arguments Enil {_}.
Global Arguments Esnoc {_} _%_proof_scope _%_string _%_I.

Local Notation world_id := positive.
Local Notation level := nat.

(*** TODO: 
          What else should be displayed? 
n          Simplify (hide) k-trees

***)

(*** isim ***)
Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------' itr_src itr_tgt"
:=
  (environments.envs_entails (Envs E1 E2 _) (isim _ _ _ _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
     format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

Notation "E1 '------------------------------------------------------------------□' st_src st_tgt '-------------------------------isim-------------------------------' itr_src itr_tgt"
:=
  (environments.envs_entails (Envs E1 Enil _) (isim _ _ _ _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
     format "E1 '------------------------------------------------------------------□' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

Notation "E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------' itr_src itr_tgt"
:=
  (environments.envs_entails (Envs Enil E2 _) (isim _ _ _ _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
     format "E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

Notation "'------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------' itr_src itr_tgt"
:=
  (environments.envs_entails (Envs Enil Enil _) (isim _ _ _ _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
     format "'------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

(* additional *) 
Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------' P '∗' 'ISIM'"
:=
  (environments.envs_entails (Envs E1 E2 _) (bi_sep P (isim _ _ _ _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
     format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' P  '∗'  'ISIM' ").

Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------' P '-∗' 'ISIM'"
:=
  (environments.envs_entails (Envs E1 E2 _) (bi_wand P (isim _ _ _ _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
     format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' P  '-∗'  'ISIM' ").
