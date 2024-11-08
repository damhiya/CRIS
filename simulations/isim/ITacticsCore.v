Require Import Coqlib ITreelib sflib.
Require Import Events STS.
Require Import Behavior.

Require Import Skeleton.
Require Import PCM IPM STB.
Require Import Any.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
Require Import Red IRed.
Require Import HPSim.
Require Import World sWorld.
Require Import ISimCore.
Require Import Events Mod SMod HMod PMod.
Require Import SubPerm.
Require Import LAuto.

From stdpp Require Import coPset gmap.

(************ User Tactics **************)

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
  repeat match goal with [H: @eq string _ _|-_] =>
           apply string_app_inv in H
    end; ss.

Ltac prove_scope :=
  try unfold HModSem.fnsems; try unfold SModSem.fnsems; try unfold fnsems_scopes;
  s; ii; des_ifs; ss; des; ss; eauto.

Ltac prove_nodup :=
  repeat (econs; [ii; ss; des; try match goal with [H: _ |- _] => inv_string H end|]); try (econs; fail).

Ltac by_coind CIH :=
  iApply isim_progress; iApply isim_base;
  iSpecialize (CIH $! _);
  repeat first[instantiate (1:= (_,_))|instantiate (1:= existT _ _)]; s;
  iApply CIH.

Ltac unfold_hmod :=
  match goal with
  | [|-context[HMod.modsem ?x _]] => rewrite/__ {1}/x; progress unseal "ccr"
  | [|-context[HMod.sk ?x]] => rewrite/__ {1}/x; progress unseal "ccr" end.

Lemma ereplace T (x y: T):
  x = y -> x = y.
Proof. eauto. Qed.

Ltac alist_upd_simpl nodup_tac :=
  match goal with
  [ |- context[alist_upd ?k ?v ?l]] =>
    match l with
    | context[(k,?v0)] =>
      let TMP := fresh "_TMP" in
      let NODUP := fresh "NODUP" in
      match goal with [H: List.NoDup _|-_] =>
        eassert (TMP: List.NoDup (List.map fst l)) by (nodup_tac H); clear H; revert TMP
      end;
      erewrite (@ereplace _ l); [intros ?|Lauto_prepare; Lauto_find (k,v0); refl];
      eassert (NODUP := alist_upd_nodup k v _ TMP); revert NODUP;
      rewrite !alist_upd_with_nodup; [|exact TMP]; clear TMP;
      Lauto_finish; intros ?
    end
  end.

Ltac trivial_nodup H :=
  exact H.

Ltac alist_find_simpl nodup_tac :=
  match goal with
  [ |- context[alist_find ?k ?l]] =>
    match l with
    | context[(k,_)] =>
      let TMP := fresh "_TMP" in
      match goal with [H: List.NoDup _|-_] =>
        eassert (TMP: List.NoDup (List.map fst l))  by (nodup_tac H);
        revert TMP
      end;
      erewrite (@ereplace _ l);
      [intros ?
      |Lauto_normalize; try rewrite !List.map_app; simpl List.map; Lauto_prepare;
       match goal with [|-context[(k,?v)]] => Lauto_find (k,v) end; refl];
      rewrite !alist_find_with_nodup; [|exact TMP]; clear TMP;
      Lauto_finish
    end
  end.
  
Lemma map_map_compose {A B C} (f: A -> B) (g: B -> C) l:
  List.map g (List.map f l) = List.map (g ∘ f) l.
Proof.
  rewrite List.map_map. refl.
Qed.

Lemma fst_map_snd {A B C} f:
  (fst ∘ @map_snd A B C f) = fst.
Proof.
  extensionalities. destruct H. s. eauto.
Qed.

Ltac fnsems_nodup H :=
  revert H; simpl HModSem.fnsems; repeat unfold_hmod; simpl List.map;
  try rewrite !map_map_compose; try rewrite !fst_map_snd; eauto; fail.

Ltac hss_des :=
  ss; des_safe; subst;
  repeat match goal with
    | [v: () |- _] => destruct v
    | [H: (_,_) = (_,_) |- _] => inv H
    end;
  ss.

Ltac hss :=
  hss_des;
  try (rewrite !Any.pair_split in * );
  try (rewrite !Any.upcast_downcast in * );
  repeat (match goal with [G: Any.downcast _ = Some _ |-_] =>
    apply Any.downcast_upcast in G; inv G; ss
   end);
  repeat (match goal with [G: Any.upcast (_:?T) = Any.upcast (_:?T) |-_] =>
    apply Any.upcast_inj in G; destruct G as [_ G]; red in G; depdes G; ss
   end);
  repeat (match goal with [G: Some _ = Some _ |- _] =>
    depdes G; ss
  end);
  try (rewrite !Any.pair_split in * );
  try (rewrite !Any.upcast_downcast in * );
  repeat (alist_upd_simpl trivial_nodup);
  hss_des.

(***
  Step-level tactics
 ***)

Ltac iIntrosFresh H := iIntros H || iIntrosFresh (H ++ "'")%string.

Ltac des_pairs :=
  repeat match goal with
    | [H: context[let () := ?x in _] |- _] => destruct x
    | |- context[let () := ?x in _] => destruct x
    | [H: context[let (_, _) := ?x in _] |- _] =>
        let n0 := fresh x in let n1 := fresh x in destruct x as [n0 n1]
    | |- context[let (_, _) := ?x in _] =>
        let n0 := fresh x in let n1 := fresh x in destruct x as [n0 n1]
    end.

Ltac desugar itr :=
  match itr with
  | fbody_trivial _ => rewrite/__ {1}/itr
  | HoareCall _ _ _ => rewrite/__ {1}/itr
  | HoareSpawn _ _ _ => rewrite/__ {1}/itr
  | HoareYield _ _ => rewrite/__ {1}/itr
  | cput _ _ => rewrite/__{1}/itr
  | cgetU _ => rewrite/__{1}/itr
  | cgetN _ => rewrite/__{1}/itr
  | triggerUB => rewrite/__{1}/itr
  | triggerNB => rewrite/__{1}/itr
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
  | [|-context[HModSem.sandbox _ ?itr]] => first [desugar itr|fail 2]
  end;
  match goal with
  | [|-context[HModSem.sandbox _ (?itr >>= _)]] =>
      rewrite HModSB.transl_bind; unwrapSB
  | [|-context[HModSem.sandbox _ ?itr]] => first [_unwrapSB itr|fail 2]
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
      rewrite/__ SModRed.interp_call {1}/handle_callE_hmodE
  | trigger (Spawn _ _) =>
      rewrite/__ SModRed.interp_sch {1}/handle_schE_hmodE
  | trigger (Yield _) =>
      rewrite/__ SModRed.interp_sch {1}/handle_schE_hmodE
  | trigger Tid =>
      rewrite/__ SModRed.interp_sch {1}/handle_schE_hmodE
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
      rewrite PModRed.transl_ret
  | tau;; _ =>
      rewrite PModRed.transl_tau
  | trigger (Choose _) => 
      rewrite PModRed.transl_core
  | trigger (Take _) => 
      rewrite PModRed.transl_core
  | trigger (IO _ _) => 
      rewrite PModRed.transl_core  
  | trigger (Call _ _) =>
      rewrite PModRed.transl_call
  | trigger (Spawn _ _) =>
      rewrite PModRed.transl_sch
  | trigger (Yield _) =>
      rewrite PModRed.transl_sch
  | trigger Tid =>
      rewrite PModRed.transl_sch
  | trigger (SPut _ _) =>
      rewrite PModRed.transl_pg
  | trigger (SGet _) =>
      rewrite PModRed.transl_pg
  | unwrapU _ =>
      rewrite PModRed.transl_unwrapU
  | unwrapN _ =>
      rewrite PModRed.transl_unwrapN
  | assume _ =>
      rewrite PModRed.transl_asm
  | guarantee _ =>
      rewrite PModRed.transl_guar
  | _ => fail
  end.

Ltac unwrapP :=
  try match goal with
  | [|-context[PModSem.transl ?itr]] => first [desugar itr|fail 2]
  end;
  match goal with
  | [|-context[PModSem.transl (?itr >>= _)]] =>
      rewrite PModRed.transl_bind; unwrapP
  | [|-context[PModSem.transl ?itr]] => first [_unwrapP itr|fail 2]
  end.

Ltac unfold_precond_postcond term := let TM := fresh "_term" in
  set (TM := term) at 1;
  repeat (unfold precond in TM; simpl in TM);
  repeat (unfold postcond in TM; simpl in TM);
  subst TM.

Ltac _step_l :=
  match goal with
  (******* isim ******)
  (** src **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, tau;; _) _) ] =>
      iApply isim_tau_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, Ret _ >>= _) _) ] =>
      rewrite bind_ret_l
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, (HModSem.sandbox _ (trigger (SPut _ _))) >>= _) _) ] =>
      iApply isim_sput_src_sandbox; [s;eauto|]
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, (HModSem.sandbox _ (trigger (SGet _))) >>= _) _) ] =>
      iApply isim_sget_src_sandbox; [s;eauto|]
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _) _) ] =>
      let name := fresh "q" in
      iApply isim_take_src; iIntros (name)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _  (_, trigger (Assume ?P) >>= _) _) ] =>
      unfold_precond_postcond P; iApply isim_Assume_src; iIntrosFresh "ASM"
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) _) ] =>
      let name := fresh "q" in
      iApply isim_unwrapU_src; iIntros (name) "%";
      match goal with [ H: ?x = Some _ |- _ ] => let G := fresh "G" in rename H into G; try rewrite G in * end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, assume _ >>= _) _) ] =>
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
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, (HModSem.sandbox _ (trigger (SPut _ _))) >>= _)) ] =>
      iApply isim_sput_tgt_sandbox; [s; eauto|]
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, (HModSem.sandbox _ (trigger (SGet _))) >>= _)) ] =>
      iApply isim_sget_tgt_sandbox; [s; eauto|]
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose _) >>= _)) ] =>
      let name := fresh "q" in
      iApply isim_choose_tgt; iIntros (name)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _)) ] =>
      unfold_precond_postcond P; iApply isim_Guarantee_tgt; iIntrosFresh "GRT"
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, unwrapN ?ox >>= _)) ] =>
      let name := fresh "q" in
      iApply isim_unwrapN_tgt; iIntros (name) "%";
      match goal with [ H: ?x = Some _ |- _ ] => let G := fresh "G" in rename H into G; try rewrite G in * end
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


Ltac hide_itree_l := let IT := fresh "ITREE" in
  match goal with [|- _ (_ ?it _)] => set (IT := it) end; try unfold IT at 2.
Ltac hide_itree_r := let IT := fresh "ITREE" in
  match goal with [|- _ (_ _ ?it)] => set (IT := it) end; first [ try (unfold IT at 2; fail 1) | unfold IT at 1].
Ltac show_itree :=
  match goal with [IT:=_ |-_] => unfold IT; clear IT end.

Ltac unfold_stb :=
  try match goal with
    [|-context[unwrapN (?stb ?sk ?name)]] =>
      try match goal with
        [H: context[stb_incl _ (stb _)]|-_] =>
          let RW := fresh "_RW" in let ND := fresh "_ND" in
          edestruct H as [ND RW];
          erewrite (RW name);
          [|revert ND; unfold to_stb;
            match goal with [|-context[alist_find _ ?x]] => rewrite/__ /x end;
            unseal "ccr"; i;
            alist_find_simpl fnsems_nodup;
            refl];
          simpl unwrapN; clear ND RW
      end
  end.

Ltac _prep :=
  first
    [ unwrapSB
    | unwrapS; unfold_stb; unwrapSB
    | unwrapP; unwrapSB
    | idtac].

Ltac prep :=
  try rewrite !bind_bind;
  try match goal with
  | [|-context[interp_smod _ _ (?f ?arg)]] =>
    match type of arg with Any.t => rewrite/__ {1}/f end
  | [|-context[PModSem.transl (?f ?arg)]] =>
    match type of arg with Any.t => rewrite/__ {1}/f end
  end;
  unfold ccallU, ccallN;
  try match goal with
      | [|-context[(_, HModSem.sandbox _ _)]] => _prep
      | [|-context[(_, HModSem.sandbox _ _ >>= _)]] => _prep
      end;
  try rewrite !bind_bind;
  try rewrite !bind_tau.

Ltac step_l :=
  hide_itree_r;
  prep; _step_l; try alist_find_simpl fnsems_nodup; des_pairs; s;
  show_itree.

Ltac steps_l := repeat step_l.

Ltac step_r :=
  hide_itree_l;
  prep; _step_r; try alist_find_simpl fnsems_nodup; des_pairs; s;
  show_itree.

Ltac steps_r := repeat step_r.

Ltac step :=
  hide_itree_r; prep; show_itree;
  hide_itree_l; prep; show_itree;
  _step; des_pairs; s.

Ltac force_l_core :=
  hide_itree_r;
  prep; _force_l; s;
  show_itree.

Tactic Notation "force_l" :=
  force_l_core; try (iExists _).

Tactic Notation "force_l" uconstr(p) :=
  force_l_core; iExists p.

Ltac forces_l := repeat force_l.

Ltac force_r_core :=
  hide_itree_l;
  prep; _force_r; s;
  show_itree.

Tactic Notation "force_r" :=
  force_r_core; try (iExists _).
  
Tactic Notation "force_r" uconstr(p) :=
  force_r_core; iExists p.

Ltac forces_r := repeat force_r.

Ltac inline_l :=
  hide_itree_r;
  prep;
  iApply isim_inline_src;
  [simpl HModSem.fnsems; repeat unfold_hmod; simpl List.map;
   alist_find_simpl fnsems_nodup; eauto|];
  unfold interp_sb_hp, HoareFun; s;
  show_itree.
  
Ltac inline_r :=
  hide_itree_l;
  prep;
  iApply isim_inline_tgt;
  [simpl HModSem.fnsems; repeat unfold_hmod; simpl List.map;
   alist_find_simpl fnsems_nodup; eauto|];
  unfold interp_sb_hp, HoareFun; s;
  show_itree.

Ltac call hyps :=
  hide_itree_r; prep; show_itree;
  hide_itree_l; prep; show_itree;
  iApply isim_call;
  iSplitL hyps; [ |iIntros "% % % % % %"; iIntrosFresh "IST"].

Ltac yield hyps :=
  hide_itree_r; prep; show_itree;
  hide_itree_l; prep; show_itree;
  iApply isim_yield;
  iSplitL hyps; [ |iIntros "% % % % %"; iIntrosFresh "IST"].

Ltac init_simF :=
  unfold HSim.sim_fun, HSSim.sim_fun; i;
  match goal with [H: _|-_] => revert H end;
  s; unfold_hmod;
  match goal with [|-context[alist_find _ ?x]] =>
    set (TMP := x); unfold_hmod; unfold TMP; clear TMP
  end;
  simpl HModSem.fnsems;
  alist_find_simpl fnsems_nodup;
  let H := fresh "TMP" in intros H; inv H;
  alist_find_simpl fnsems_nodup;
  eexists; split; [eauto|];
  repeat match goal with
  | [|- context[{| fsb_body := cfunU ?x |}]] => rewrite/__ {1}/x
  | [|- context[{| fsb_body := cfunN ?x |}]] => rewrite/__ {1}/x
  | [|- context[{| fsb_body := ?x |}]] => rewrite/__ {1}/x
  | [|- context[PModSem.transl (?x _)]] => unfold x
  | [|- context[cfunU ?x]] => rewrite/__ {1}/x
  | [|- context[cfunN ?x]] => rewrite/__ {1}/x
  end;                          
  unfold interp_sb_hp, HoareFun, cfunU, cfunN, HModSem.sandbox_body; s;
  ii; subst; iIntros "IST".

Ltac prove_sub_perm :=
  i; try rewrite /HMod.scopes; s; repeat unfold_hmod; s; Lauto_normalize;
  match goal with
    [|-sub_perm ?x ?y] =>
      match x with
      | _ ++ _ => idtac
      | _ => rewrite/__ /x
      end;
      match y with
      | _ ++ _ => idtac
      | _ => rewrite/__ /y
      end
  end;
  Lauto_normalize;
  match goal with
    [|-sub_perm ?x ?y] =>
      replace (sub_perm x y) with (sub_perm (x++[]) (y++[])) by (rewrite !app_nil_r; eauto)
  end;
  repeat first [eapply sub_perm_cancel_head|eapply sub_perm_remove_head];
  eapply sub_perm_refl.

(**** TODO ****)
(* A tactic to handle meta variables *)

(************ User Notations **************)

From iris.proofmode Require Import coq_tactics environments.

Global Arguments Envs _ _%proof_scope _%proof_scope _.
Global Arguments Enil {_}.
Global Arguments Esnoc {_} _%proof_scope _%string _%I.

Local Notation world_id := positive.
Local Notation level := nat.

(*** TODO: 
          What else should be displayed? 
          Simplify (hide) k-trees

***)

(*** isim ***)
Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------'  itr_src itr_tgt"
:=
  (environments.envs_entails (Envs E1 E2 _) (isim _ _ _ _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50,
     format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

Notation "E1 '------------------------------------------------------------------□' st_src st_tgt '-------------------------------isim-------------------------------'  itr_src itr_tgt"
:=
  (environments.envs_entails (Envs E1 Enil _) (isim _ _ _ _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50,
     format "E1 '------------------------------------------------------------------□' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

Notation "E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------'  itr_src itr_tgt"
:=
  (environments.envs_entails (Envs Enil E2 _) (isim _ _ _ _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50,
     format "E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

Notation "'------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------'  itr_src itr_tgt"
:=
  (environments.envs_entails (Envs Enil Enil _) (isim _ _ _ _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50,
     format "'------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

(* additional *) 
Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------'  P '∗' 'ISIM'"
:=
  (environments.envs_entails (Envs E1 E2 _) (bi_sep P (isim _ _ _ _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50,
     format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' P  '∗'  'ISIM' ").

Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------'  P '-∗' 'ISIM'"
:=
  (environments.envs_entails (Envs E1 E2 _) (bi_wand P (isim _ _ _ _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50,
     format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' P  '-∗'  'ISIM' ").
