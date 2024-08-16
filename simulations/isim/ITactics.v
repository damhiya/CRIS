Require Import Coqlib ITreelib sflib.
Require Import Events STS.
Require Import Behavior.

Require Import Skeleton.
Require Import PCM IPM.
Require Import Any.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
Require Import Red IRed.
Require Import HPSim.
Require Import World sWorld.
Require Import ISimCore ITacticsInternal.
Require Import Events Mod SMod HMod.

From stdpp Require Import coPset gmap.

(************ User Tactics **************)
(* Tactic Notation "simF_init" constr(LS) constr(LT) reference(FS) reference(FT) := *)
  (* unfold HModR.sim_fun; i; *)
  (* rewrite// [in alist_find _ _]LS; s; *)
  (* rewrite// [in alist_find _ _]LT; s; *)
  (* unfold FS; unfold FT; *)
  (* i; iIntros "IST"; unfold cfunU, interp_sb_hp, HoareFun, ccallU; s. *)
(* need change *)
(* Ltac sim_init := econs; eauto; ii; econs; cycle 1; [s|sim_split]. *)

(* use this to enforce the ssr_reflect rewrite: rewrite/__ rules. *)
Definition __ : Type := unit.

Ltac unfold_hmod :=
  match goal with
  | [|-context[HMod.get_modsem ?x _]] => rewrite/__ {1}/x; progress unseal "ccr"
  | [|-context[HMod.sk ?x]] => rewrite/__ {1}/x; progress unseal "ccr" end.

(***
  Step-level tactics
 ***)

Ltac st := repeat _st.

Ltac force_l := try (prep; _force_l).
Ltac force_r := try (prep; _force_r).

Ltac inline_l := prep; iApply isim_inline_src; [repeat unfold_hmod; eauto|]; unfold interp_sb_hp, HoareFun; s.
Ltac inline_r := prep; iApply isim_inline_tgt; [repeat unfold_hmod; eauto|]; unfold interp_sb_hp, HoareFun; s.

Ltac call := prep; iApply isim_call; iSplitL "IST"; [ |iIntros "% % %"; iIntrosFresh "IST"].

(* COMMENT: Should st_l, st_r be kept in here, or moved to temporary? *)
Ltac st_l := let IT := fresh "__IT" in
  match goal with [|- _ (_ (_, _) (_, ?itgt))] => set (IT := itgt) end;
  st;
  unfold IT; clear IT.
Ltac st_r := let IT := fresh "__IT" in
  match goal with [|- _ (_ (_, ?isrc) (_, _))] => set (IT := isrc) end;
  st;
  unfold IT; clear IT.

Ltac apc_r :=
  rewrite interp_hmodE_hapc;
  st_r; unfold HoareAPC; st_r; rewrite unfold_APC; st_r;
  match goal with [b: bool|-_] => destruct b end;
  [|unfold guarantee, triggerNB; st_r;
    match goal with [v: void|-_] => destruct v end].

Ltac hss :=
  ss;
  try (unfold run_l, run_r in *; rewrite !Any.pair_split in *; fold run_l run_r in * );
  try (rewrite !Any.upcast_downcast in * );
  (repeat match goal with [G: Any.downcast _ = Some _ |-_] =>
    apply Any.downcast_upcast in G; inv G; ss
   end);
  (repeat match goal with [G: Any.upcast (_:?T) = Any.upcast (_:?T) |-_] =>
    apply Any.upcast_inj in G; destruct G as [_ G]; red in G; depdes G; ss
   end);
  (repeat match goal with [G: Some _ = Some _ |- _] =>
    depdes G; ss
   end).

(***** Temporary Tactics ( Not recommended in a final proof. Use only for excersize. ) *****)
Ltac prep := cbn; ired_both.
Ltac steps := repeat _steps.
Ltac ired := repeat _ired.
Ltac choose_l := iApply isim_choose_src.
Ltac choose_r := iApply isim_choose_tgt; iIntros "%".
Ltac take_l := iApply isim_take_src; iIntros "%".
Ltac take_r := iApply isim_take_tgt.
Ltac asm_l := iApply isim_assume_src; iIntrosFresh "ASM".
Ltac asm_r := iApply isim_assume_tgt.
Ltac grt_l := iApply isim_guarantee_src.
Ltac grt_r := iApply isim_guarantee_tgt; iIntrosFresh "GRT".
Ltac choose := prep; choose_r; choose_l.
Ltac take := prep; take_l; take_r.
Ltac asm := prep; asm_l; asm_r.
Ltac grt := prep; grt_r; grt_l.

(* Need to be generalized *)
Ltac CIH :=
iApply isim_progress; iApply isim_base;
match goal with [|- context[_ ?R _ _ _ (?st_src, _ _ ?itr) (?st_tgt, _)]] =>
  iApply ("CIH" $! (@existT _ (λ _, _) itr (@existT _ (λ _, _) st_src st_tgt))); eauto
end.

(***
 Module-level tactics
 ***)

Lemma string_app_inv
  p s s'
  (EQ: (p ++ s = p ++ s')%string)
  :
  (s = s')%string.
Proof.
  revert_until p. induction p; i; ss.
  unfold append in EQ. depdes EQ. eauto.
Qed.

Lemma isim_reflR `{Σ: GRA.t} R Ist fnsems_src fnsems_tgt st_src st_tgt (itr: itree _ R):
  IstProd Ist IstEq st_src st_tgt -∗
  isim (IstProd Ist IstEq) fnsems_src fnsems_tgt ibot ibot
  (λ '(st_src, v_src) '(st_tgt, v_tgt), IstProd Ist IstEq st_src st_tgt ** ⌜v_src = v_tgt⌝) false false
  (st_src, translate (HModSem.emb_ run_r) itr)
  (st_tgt, translate (HModSem.emb_ run_r) itr).
Proof.
  revert st_src st_tgt. apply combine_quant.
  revert itr. apply combine_quant.

  eapply isim_coind. i. destruct a as [itr [st_src st_tgt]]. s.
  iIntros "(#(_ & CIH) & IST)".
  assert (CASE := case_itrH _ itr); des; subst.
  - st. eauto.
  - st. CIH.
  - st. force_r. iFrame. CIH.
  - st. force_l. iFrame. CIH.
  - destruct c. st. call; eauto. CIH.
  - destruct s. st.
    iPoseProof (ist_eq_run_r with "IST") as "(%EQ & IST)". rewrite <-EQ.
    CIH.
  - destruct e; st; force_l; force_r; CIH.
Qed.

Ltac inv_string X :=
  inv X;
  repeat match goal with [H: @eq string (_ ++ _)%string (_ ++ _)%string|-_] =>
           apply string_app_inv in H
    end; ss.

Ltac alist_find_solver :=
  match goal with [|-context[alist_find ?x]] => rewrite <-(Seal.sealing_eq "_tmp_" x) end;
  s; unfold rel_dec, Dec_RelDec, sumbool_to_bool, dec, string_Dec;
  des_ifs; unseal "_tmp_"; ss;
  repeat match goal with [H: @eq string _ _|-_] => inv_string H end;
  repeat match goal with [H: not (@eq string _ _)|-_] => clear H end.

Ltac init_simF := let TMP := fresh "_tmp_" in
  unfold HModR.sim_fun; i; s;
  unfold_hmod;
  match goal with [|-context[alist_find _ ?x]] =>
    set (TMP := x); unfold_hmod; unfold TMP; clear TMP
  end;
  alist_find_solver;
  repeat match goal with
  | [|- context[{| fsb_body := cfunU ?x |}]] => rewrite/__ {1}/x
  | [|- context[{| fsb_body := ?x |}]] => rewrite/__ {1}/x
  | [|- context[cfunU ?x]] => rewrite/__ {1}/x
  end;
  unfold interp_sb_hp, HoareFun, cfunU, ccallU; s;
  ii; subst; iIntros "IST".

Ltac init_sim := let TMP := fresh "_tmp_" in
  econs; s;
  [econs; [repeat unfold_hmod;ss|repeat unfold_hmod;ss|
           repeat unfold_hmod;ss; i; des_ifs|
    s; i; des_ifs;
    match goal with [H:_|-_] => revert H end;
    unfold_hmod;
    match goal with [|-context[alist_find _ ?x]] =>
      set (TMP := x); unfold_hmod; unfold TMP; clear TMP
    end;
    alist_find_solver]
  |repeat unfold_hmod; ss].

Ltac use_simF lem := let TMP := fresh "_tmp_" in
  intros TMP; inv TMP;
  esplits; eauto;
  eassert (X:= lem _); revert X; s;
  unfold_hmod;
  match goal with [|-context[alist_find _ ?x]] =>
    set (TMP := x); unfold_hmod; unfold TMP; clear TMP
  end;
  alist_find_solver; eauto.

Ltac refl_simF := let TMP := fresh "_tmp_" in
  repeat unfold_hmod;
  alist_find_solver; intros TMP; inv TMP; esplits; eauto;
  ii; subst; eapply isim_reflR.




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
  (environments.envs_entails (Envs E1 E2 _) (isim _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
  (* (_ _ (isim Ist _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt))) *)
    (at level 50,
     format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

Notation "E1 '------------------------------------------------------------------□' st_src st_tgt '-------------------------------isim-------------------------------'  itr_src itr_tgt"
:=
  (environments.envs_entails (Envs E1 Enil _) (isim _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
  (* (_ _ (isim Ist _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt))) *)
    (at level 50,
     format "E1 '------------------------------------------------------------------□' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

Notation "E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------'  itr_src itr_tgt"
:=
  (environments.envs_entails (Envs Enil E2 _) (isim _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
  (* (_ _ (isim Ist _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt))) *)
    (at level 50,
     format "E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

Notation "'------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------'  itr_src itr_tgt"
:=
  (environments.envs_entails (Envs Enil Enil _) (isim _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
  (* (_ _ (isim Ist _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt))) *)
    (at level 50,
     format "'------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

(* additional *) 
Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------'  P '∗' 'ISIM'"
:=
  (environments.envs_entails (Envs E1 E2 _) (bi_sep P (isim _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50,
     format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' P  '∗'  'ISIM' ").

Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------'  P '-∗' 'ISIM'"
:=
  (environments.envs_entails (Envs E1 E2 _) (bi_wand P (isim _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50,
     format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' P  '-∗'  'ISIM' ").


(****************************************************************************************************)

(* Section TEST.
Context `{CtxWD.t}.

Let Ist: Any.t -> Any.t -> iProp := fun _ _ => ⌜True⌝%I.
Let RR: (Any.t * Any.t) -> (Any.t * Any.t) -> iProp := fun _ _ => ⌜True⌝%I.
Variable iP: iProp.

Goal ⊢ ((⌜False⌝∗iP∗iP) -∗ iP ∗ isim Ist [] [] ibot ibot RR false false (tt↑, Ret tt↑) (tt↑, Ret tt↑)).
Proof. iIntros "(#A & B & C)". Unset Printing Notations.
iAssert (iP -* world 1 0 ⊤) as "H". { admit. }
iPoseProof ("H" with "B") as "B". iRevert "B". Unset Printing Notations. 
clarify. Admitted.
Goal ⌜False⌝%I ⊢ (isim Ist [] [] ibot ibot RR false false (tt↑, Ret tt↑) (tt↑, Ret tt↑)).
Proof. iIntros "#H". Admitted.
Goal ⊢ (iP -∗ isim Ist [] [] ibot ibot RR false false (tt↑, Ret tt↑) (tt↑, Ret tt↑)).
Proof. iIntros "H". Admitted.
Goal ⊢ (isim Ist [] [] ibot ibot RR false false (tt↑, trigger (Assume (⌜False⌝%I));;; Ret tt↑ >>= (fun r => Ret r)) (tt↑, Ret tt↑)).
Proof. iIntros. steps. Admitted.



Goal ⊢ ((⌜False⌝**iP) -∗ wsim Ist [] [] 1 0 ⊤ ibot ibot RR false false (tt↑, Ret tt↑) (tt↑, Ret tt↑)).
Proof. iIntros "[#A B]". clarify. Qed.
Goal ⌜False⌝%I ⊢ (wsim Ist [] [] 1 0 ⊤ ibot ibot RR false false (tt↑, Ret tt↑) (tt↑, Ret tt↑)).
Proof. iIntros "#H". Admitted.
Goal ⊢ (iP -∗ wsim Ist [] [] 1 0 ⊤ ibot ibot RR false false (tt↑, Ret tt↑) (tt↑, Ret tt↑)).
Proof. iIntros "H". Admitted.
Goal ⊢ (wsim Ist [] [] 1 0 ⊤ ibot ibot RR false false (tt↑, trigger (Assume (⌜False⌝%I));;; Ret tt↑ >>= (fun r => Ret r)) (tt↑, Ret tt↑)).
Proof. iIntros. steps. Admitted.



End TEST. *)


