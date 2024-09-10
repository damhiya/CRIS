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
  iSpecialize (CIH $! _); repeat instantiate (1:= existT _ _); s;
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

Ltac hss :=
  ss;
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
  repeat (alist_upd_simpl trivial_nodup); s.

(***
  Step-level tactics
 ***)

Ltac iIntrosFresh H := iIntros H || iIntrosFresh (H ++ "'")%string.

Ltac des_pairs :=
  repeat match goal with
    | [H: context[let (_, _) := ?x in _] |- _] =>
        let n0 := fresh x in let n1 := fresh x in destruct x as [n0 n1]
    | |- context[let (_, _) := ?x in _] =>
        let n0 := fresh x in let n1 := fresh x in destruct x as [n0 n1]
    end.

Ltac desugar itr :=
  match itr with
  | HoareBody _ _ _ => rewrite/__ {1}/itr
  | HoareCall _ _ _ _ _ => rewrite/__ {1}/itr
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
      rewrite HModSB.transl_Assume
  | trigger (Guarantee _) => 
      rewrite HModSB.transl_Guarantee
  | unwrapU _ =>
      rewrite HModSB.transl_unwrapU
  | unwrapN _ =>
      rewrite HModSB.transl_unwrapN
  | assume _ =>
      rewrite HModSB.transl_asm
  | guarantee _ =>
      rewrite HModSB.transl_guar
  | trigger (Spawn _ _) =>
      rewrite HModSB.transl_spawn
  | trigger (Yield _) =>
      rewrite HModSB.transl_yield
  | trigger Tid =>
      rewrite HModSB.transl_tid
  | HoareAPC _ _ =>
      idtac
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
      rewrite SModRed.interp_Assume
  | trigger (Guarantee _) => 
      rewrite SModRed.interp_Guarantee
  | unwrapU _ =>
      rewrite SModRed.interp_unwrapU
  | unwrapN _ =>
      rewrite SModRed.interp_unwrapN
  | assume _ =>
      rewrite SModRed.interp_asm
  | guarantee _ =>
      rewrite SModRed.interp_guar
  | trigger APC =>
      (* idtac *)
      rewrite/__ SModRed.interp_apc {1}/handle_apcE_hmodE
  | _ => fail
  end.

Ltac unwrapS :=
  try match goal with
    | [|-context[interp_smod _ _ _ ?itr]] => first [desugar itr|fail 2]
  end;
  match goal with
  | [|-context[interp_smod _ _ _ (?itr >>= _)]] =>
      rewrite SModRed.interp_bind; unwrapS
  | [|-context[interp_smod _ _ _ ?itr]] => first [_unwrapS itr|fail 2]
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
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, tau;; _) _) ] =>
      iApply isim_tau_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, Ret _ >>= _) _) ] =>
      rewrite bind_ret_l
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, (HModSem.sandbox _ (trigger (SPut _ _))) >>= _) _) ] =>
      iApply isim_sput_src_sandbox; [s;eauto|]
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, (HModSem.sandbox _ (trigger (SGet _))) >>= _) _) ] =>
      iApply isim_sget_src_sandbox; [s;eauto|]
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _) _) ] =>
      let name := fresh "q" in
      iApply isim_take_src; iIntros (name)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _  (_, trigger (Assume ?P) >>= _) _) ] =>
      unfold_precond_postcond P; iApply isim_Assume_src; iIntrosFresh "ASM"
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) _) ] =>
      let name := fresh "q" in
      iApply isim_unwrapU_src; iIntros (name) "%";
      match goal with [ H: ?x = Some _ |- _ ] => let G := fresh "G" in rename H into G; try rewrite G in * end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, assume _ >>= _) _) ] =>
      let name := fresh "asm" in iApply isim_asm_src; iIntros (name)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, trigger Tid >>= _) _) ] =>
      iApply isim_tid_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, HModSem.sandbox _ (HoareAPC _ _) >>= _) _) ] =>
      idtac
  end.

Ltac _step_r :=
  match goal with
  (******* isim ******)
  (** tgt **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, Ret _ >>= _)) ] =>
      rewrite bind_ret_l
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, tau;; _)) ] =>
      iApply isim_tau_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, (HModSem.sandbox _ (trigger (SPut _ _))) >>= _)) ] =>
      iApply isim_sput_tgt_sandbox; [s; eauto|]
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, (HModSem.sandbox _ (trigger (SGet _))) >>= _)) ] =>
      iApply isim_sget_tgt_sandbox; [s; eauto|]
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose _) >>= _)) ] =>
      let name := fresh "q" in
      iApply isim_choose_tgt; iIntros (name)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _)) ] =>
      unfold_precond_postcond P; iApply isim_Guarantee_tgt; iIntrosFresh "GRT"
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, unwrapN ?ox >>= _)) ] =>
      let name := fresh "q" in
      iApply isim_unwrapN_tgt; iIntros (name) "%";
      match goal with [ H: ?x = Some _ |- _ ] => let G := fresh "G" in rename H into G; try rewrite G in * end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, guarantee _ >>= _)) ] =>
      let name := fresh "grt" in iApply isim_guar_tgt; iIntros (name)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, trigger Tid >>=  _)) ] =>
      iApply isim_tid_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, HModSem.sandbox _ (HoareAPC _ _) >>= _)) ] =>
      idtac
  end.

Ltac _step :=
  match goal with
  (******* isim ******)
  (** both **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, Ret _) (_, Ret _)) ] =>
      iApply isim_ret
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, trigger (IO _ _) >>= _) (_, trigger (IO _ _) >>= _)) ] =>
      iApply isim_io; iIntros "%"
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, trigger (Spawn _ _) >>= _) (_, trigger (Spawn _ _) >>= _)) ] =>
      iApply isim_spawn
  end.

Ltac _force_l :=
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose ?T) >>= _) _) ] =>
      iApply isim_choose_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _) _) ] =>
      unfold_precond_postcond P; iApply isim_Guarantee_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, unwrapN _ >>= _) _) ] =>
      iApply isim_unwrapN_src; iExists _
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, guarantee _ >>= _) _) ] =>
      iApply isim_guar_src
  end
.

Ltac _force_r :=
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _)) ] =>
      iApply isim_take_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Assume ?P) >>= _)) ] =>
      unfold_precond_postcond P; iApply isim_Assume_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, unwrapU _ >>= _)) ] =>
      iApply isim_unwrapU_tgt; iExists _
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, assume _ >>= _)) ] =>
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

Ltac prep :=
  first
    [ unwrapSB
    | unwrapS; unfold_stb; unwrapSB
    | unwrapP; unwrapSB
    | idtac];
  try rewrite !bind_bind;
  try rewrite !bind_tau.

Ltac step_l :=
  hide_itree_r;
  prep; _step_l; try alist_find_simpl fnsems_nodup; des_pairs; s;
  show_itree.

Ltac step_r :=
  hide_itree_l;
  prep; _step_r; try alist_find_simpl fnsems_nodup; des_pairs; s;
  show_itree.

Ltac step :=
  hide_itree_r; prep; show_itree;
  hide_itree_l; prep; show_itree;
  _step; des_pairs; s.

Ltac force_l :=
  hide_itree_r;
  prep; _force_l; s;
  show_itree.
  
Ltac force_r :=
  hide_itree_l;
  prep; _force_r; s;
  show_itree.
  
Ltac steps_l :=
  repeat step_l.
  (* hide_itree_r; *)
  (* repeat (prep; _step_l; try alist_find_simpl fnsems_nodup; des_pairs; s); *)
  (* show_itree. *)
Ltac steps_r :=
  repeat step_r.
  (* hide_itree_l; *)
  (* repeat (prep; _step_r; try alist_find_simpl fnsems_nodup; des_pairs; s); *)
  (* show_itree. *)

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

Lemma isim_apc_tgt_remove `{Σ: GRA.t}
  fl fr Ist r g {R} RR my_tid ps pt nths st_src st_tgt i_src k_tgt scopes stb
  :
  bi_entails
    (@isim Σ fl fr Ist my_tid r g R RR ps true nths (st_src, i_src) (st_tgt, k_tgt tt))
    (isim fl fr Ist my_tid r g RR ps pt nths (st_src, i_src) (st_tgt,
         HModSem.sandbox scopes (HoareAPC stb (ord_pure Ord.O)) >>= k_tgt)).
Proof.
  iIntros "ISIM". unfold HoareAPC.
  steps_r. rewrite unfold_APC. steps_r.
  des_ifs.
  - steps_r; eauto.
  - steps_r. hss.
    iDestruct "GRT" as "(_ & % & _)".
    exfalso. destruct (q7 q4).
    + rr in H. assert (X := Ord.O_bot n).
      eapply Ord.lt_not_le; eauto.
    + rr in H. eauto.
Qed.

Ltac apc_l :=
  rewrite/__ {1}/HoareAPC; force_l; instantiate (1:= Ord.O);
  rewrite unfold_APC; force_l; instantiate (1:=true); step_l.

Ltac apc_r :=
  hide_itree_l;
  prep;
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, (HModSem.sandbox _ (HoareAPC _ _)) >>= _)) ] =>
      iApply isim_apc_tgt_remove
  end;
  show_itree.

(***
 Module-level tactics
 ***)

  Lemma alist_upd_head {K} `{Dec K} {V} (l1 l2: alist K V) (k: K) (v: V)
    (NODUP: In k (List.map fst l1))
    :
    alist_upd k v (l1 ++ l2) = alist_upd k v l1 ++ l2.
  Proof.
    unfold alist_upd.
    induction l1; ss.
    destruct a. ss. rewrite eq_rel_dec_correct. des_ifs; s.
    rewrite IHl1; eauto.
    des; eauto. exfalso. eauto.
  Qed.
  
  Lemma alist_upd_tail {K} `{Dec K} {V} (l1 l2: alist K V) (k: K) (v: V)
    (NODUP: ~ In k (List.map fst l1))
    :
    alist_upd k v (l1 ++ l2) = l1 ++ alist_upd k v l2.
  Proof.
    unfold alist_upd.
    induction l1; eauto.
    destruct a. s. rewrite eq_rel_dec_correct. des_ifs; s.
    - exfalso. apply NODUP. s. eauto.
    - rewrite IHl1; eauto.
      ii. apply NODUP. s. eauto.
  Qed.
  

Section HModProd.

  Context `{Σ: GRA.t}.

  Definition IstSB0 scopes (Ist: nat -> alist key Any.t -> alist key Any.t -> iProp) :=
    fun nths (st_src st_tgt: alist key Any.t) =>
      (⌜incl (List.map (fst ∘ fst) st_src) scopes /\
        incl (List.map (fst ∘ fst) st_tgt) scopes⌝ ∗
       Ist nths st_src st_tgt)%I.

  Definition IstSB A Ist :=
    fun (sk: Sk.t) => IstSB0 (HMod.scopes A sk) (Ist sk).

  Definition IstProd0 (IstL IstR : nat -> alist key Any.t -> alist key Any.t -> iProp) :=
    fun nths (st_src st_tgt: alist key Any.t) =>
      (∃ st_srcL st_tgtL st_srcR st_tgtR,
       ⌜st_src = st_srcL ++ st_srcR /\ st_tgt = st_tgtL ++ st_tgtR⌝ ∗
       IstL nths st_srcL st_tgtL ∗ IstR nths st_srcR st_tgtR)%I.

  Definition IstProd IstL IstR :=
    fun (sk: Sk.t) => IstProd0 (IstL sk) (IstR sk).

  Definition IstEq : Sk.t -> nat -> alist key Any.t -> alist key Any.t -> iProp :=
    fun _ _ st_src st_tgt => ⌜st_src = st_tgt⌝%I.
  
  Lemma isim_reflR Ist fl_src fl_tgt scopesL scopesR scopesF itr
    (DISJ: List.NoDup (scopesL ++ scopesR))
    (INCL: incl scopesF scopesR)
    :
    isim_fsem fl_src fl_tgt (IstProd0 (IstSB0 scopesL Ist) (IstEq []))
      (fun nths '(st_src, v_src) '(st_tgt, v_tgt) => ⌜v_src = v_tgt⌝ ∗ (IstProd0 (IstSB0 scopesL Ist) (IstEq []) nths st_src st_tgt))%I
      (HModSem.sandbox_body (scopesF,itr)) (HModSem.sandbox_body (scopesF,itr)).
  Proof.
    ii. subst. unfold HModSem.sandbox_body. s.
    generalize (itr y) as it; clear itr y.
    revert NODD. apply combine_quant.
    revert NODS. apply combine_quant.
    revert st_tgt. apply combine_quant.
    revert st_src. apply combine_quant.
    revert nths. apply combine_quant.
    eapply isim_coind. i. destruct a as [nths [st_src [st_tgt [NODS [NODD it]]]]]. s.
    iIntros "(#(_ & CIH) & IST)".
    assert (CASE := case_itrH _ it); des; subst.
    - step. iFrame. eauto.
    - steps_l. steps_r. by_coind "CIH". eauto.
    - steps_l. force_r. iFrame. by_coind "CIH". eauto.
    - steps_r. force_l. iFrame. by_coind "CIH". eauto.
    - depdes s.
      + step. by_coind "CIH". iApply IMON; [|eauto]; nia.
      + yield "IST"; eauto. by_coind "CIH". eauto.
      + steps_l. steps_r. by_coind "CIH". eauto.
    - destruct c. call "IST"; eauto. by_coind "CIH". eauto.
    - depdes s.
      + rewrite/__ !HModSB.transl_bind !HModSB.transl_put. des_ifs; cycle 1.
        { steps_r. force_l. instantiate (1:=q). by_coind "CIH". eauto. }
        iApply isim_sput_src. iApply isim_sput_tgt.
        by_coind "CIH". iClear "CIH". unfold IstProd.
        iDestruct "IST" as (? ? ? ?) "(% & (% & IST) & %)". des; subst.
        apply existsb_exists in Heq. des. apply String.eqb_eq in Heq0. subst.
        iExists st_srcL, st_tgtL, (alist_upd k v st_tgtR), (alist_upd k v _).
        iSplitR; cycle 1.
        { iFrame. eauto. }
        iPureIntro. esplits; eauto.
        * eapply alist_upd_tail. ii. 
          eapply NoDup_app_disjoint; try apply DISJ; eauto.
          eapply H0. eapply in_map in H. rewrite map_map in H. apply H.
        * eapply alist_upd_tail. ii.
          eapply NoDup_app_disjoint; try apply DISJ; eauto.
          apply H2. eapply in_map in H. rewrite map_map in H. apply H.
      + rewrite/__ !HModSB.transl_bind !HModSB.transl_get. des_ifs; cycle 1.
        { steps_r. force_l. instantiate (1:=q). by_coind "CIH". eauto. }
        iApply isim_sget_src. iApply isim_sget_tgt.
        apply existsb_exists in Heq. des. apply String.eqb_eq in Heq0. subst.
        iAssert (⌜alist_find k st_src = alist_find k st_tgt⌝ ∗
                 IstProd0 (IstSB0 scopesL Ist) (IstEq []) nths st_src st_tgt)%I
          with "[IST]" as "(% & IST)".
        { iDestruct "IST" as (? ? ? ?) "(% & (% & IST) & %)".
          des; subst. iSplitR; cycle 1.
          { repeat iExists _. iFrame. eauto. }
          rewrite alist_find_app_o; des_ifs.
          { exfalso. apply alist_find_fst_some in Heq0.
            eapply NoDup_app_disjoint; try apply DISJ; eauto.
            apply H0. eapply in_map in Heq0. rewrite map_map in Heq0. eauto.
          }
          rewrite alist_find_app_o; des_ifs.
          exfalso. apply alist_find_fst_some in Heq1.
          eapply NoDup_app_disjoint; try apply DISJ; eauto.
          apply H2. eapply in_map in Heq1. rewrite map_map in Heq1. eauto.
        }
        rewrite H. by_coind "CIH". eauto.
    - destruct e.
      + steps_r. force_l. instantiate (1:=q). by_coind "CIH". eauto.
      + steps_l. force_r. instantiate (1:=q). by_coind "CIH". eauto.
      + step. by_coind "CIH". eauto.
  Unshelve. all: eauto.
  { eapply alist_upd_nodup. eauto. }
  { eapply alist_upd_nodup. eauto. }
  Qed.

  Lemma mod_sim_reflR A B C init_cond Ist
    (INIT: ∀ sk, init_cond sk -∗
                    IstProd (IstSB A Ist) IstEq sk 1
                    (HModSem.initial_st (HMod.modsem (HMod.add A C) sk))
                    (HModSem.initial_st (HMod.modsem (HMod.add B C) sk)))
    (MON: ∀ sk nths nths' (LE: nths <= nths') st_src st_tgt,
        Ist sk nths st_src st_tgt -∗ Ist sk nths' st_src st_tgt)
    (SCOPE: ∀ sk, sub_perm (HMod.scopes B sk) (HMod.scopes A sk))
    (LEN: ∀ sk, List.length (HModSem.fnsems (HMod.modsem A sk)) =
                List.length (HModSem.fnsems (HMod.modsem B sk)))
    (* (NONE: ∀ sk fn, *)
    (*        In fn (List.map fst (HModSem.fnsems (HMod.modsem B sk))) → *)
    (*        In fn (List.map fst (HModSem.fnsems (HMod.modsem A sk)))) *)
    (SIM: ∀ sk fn
            (IN: In fn (List.map fst (HModSem.fnsems (HMod.modsem A sk)))),
          HModSemR.sim_fun (HMod.modsem (HMod.add A C) sk) (HMod.modsem (HMod.add B C) sk)
            (IstProd (IstSB A Ist) IstEq sk) fn)
    (SK: HMod.sk A = HMod.sk B)
    :
    HModR.sim (HMod.add A C) (HMod.add B C) init_cond
      (IstProd (IstSB A Ist) IstEq).
  Proof.
    econs; cycle 1.
    { rr. eapply Permutation_app_tail. rewrite SK. refl. }
    econs.
    - apply INIT.
    - i. iIntros "H". iDestruct "H" as (? ? ? ?) "(% & H & H')"; des; subst.
      do 4 (iExists _). iSplit; eauto. iFrame.
      iDestruct "H" as "(% & H)". des; subst. iSplit; eauto.
      iApply MON; [|eauto]; nia.
    - s. apply sub_perm_cancel_tail. eapply SCOPE.
    - s. rewrite !app_length. rewrite LEN. eauto.
    (* - s. i. rewrite map_app in *. apply in_or_app. apply in_app_or in IN. *)
    (*   des; eauto. *)
    - s. i. rewrite map_app in IN. apply in_app_or in IN. des.
      { eapply SIM; eauto. }
      ii. exists fs. destruct fs as [scp f].
      assert (FND: alist_find fn (HModSem.fnsems (HMod.modsem C sk))
                   = Some (scp,f)).
      { s in FIND. rewrite alist_find_app_o in FIND. des_ifs.
        exfalso. assert (ND:= HModSem.wf_fns WFS). s in ND. rewrite map_app in ND.
        eapply NoDup_app_disjoint; try apply ND; eauto.
        eapply alist_find_some, (in_map fst) in Heq. eauto.
      }

      split; cycle 1.
      { eapply isim_reflR. eauto.
        - apply WFS.
        - ii. eapply (HMod.modsem C sk). unfold fnsems_scopes. rewrite FND. eauto.
      }
      eapply alist_find_some_iff; eauto.
      apply in_or_app. right. eapply alist_find_some. eauto.    
Qed.
  
End HModProd.

Ltac init_simF :=
  unfold HModR.sim_fun, HModSemR.sim_fun; i;
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
  | [|- context[{| fsb_body := ?x |}]] => rewrite/__ {1}/x
  | [|- context[cfunU ?x]] => rewrite/__ {1}/x
  end;                          
  unfold interp_sb_hp, HoareFun, cfunU, ccallU, HModSem.sandbox_body; s;
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

Ltac init_sim :=
  first [eapply mod_sim_reflR | econs; [econs|]];
  [i; s; repeat unfold_hmod; s
  |eauto
  |try prove_sub_perm
  |repeat unfold_hmod; ss; try nia
  (* |repeat unfold_hmod; ss; des_ifs; eauto *)
  |unfold_hmod; s; i; des; subst; ss
  |repeat unfold_hmod; ss; eauto].


(**** TODO ****)
(* A tactic to handle meta variables *)
(* Tactics to handle APC. (APC in src / in tgt / ord_pure 0 / ord_pure n / ....  ) *)

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
  (environments.envs_entails (Envs E1 E2 _) (isim _ _ _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
  (* (_ _ (isim Ist _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt))) *)
    (at level 50,
     format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

Notation "E1 '------------------------------------------------------------------□' st_src st_tgt '-------------------------------isim-------------------------------'  itr_src itr_tgt"
:=
  (environments.envs_entails (Envs E1 Enil _) (isim _ _ _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
  (* (_ _ (isim Ist _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt))) *)
    (at level 50,
     format "E1 '------------------------------------------------------------------□' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

Notation "E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------'  itr_src itr_tgt"
:=
  (environments.envs_entails (Envs Enil E2 _) (isim _ _ _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
  (* (_ _ (isim Ist _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt))) *)
    (at level 50,
     format "E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

Notation "'------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------'  itr_src itr_tgt"
:=
  (environments.envs_entails (Envs Enil Enil _) (isim _ _ _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
  (* (_ _ (isim Ist _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt))) *)
    (at level 50,
     format "'------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

(* additional *) 
Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------'  P '∗' 'ISIM'"
:=
  (environments.envs_entails (Envs E1 E2 _) (bi_sep P (isim _ _ _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50,
     format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' P  '∗'  'ISIM' ").

Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------'  P '-∗' 'ISIM'"
:=
  (environments.envs_entails (Envs E1 E2 _) (bi_wand P (isim _ _ _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50,
     format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' P  '-∗'  'ISIM' ").
