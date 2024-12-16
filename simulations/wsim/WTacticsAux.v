(* 
Require Import Coqlib.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef OpenDef STB ModSim.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
Require Import Red IRed.
Require Import ProofMode Invariant.
Require Import HPSim.
Require Import World sWorld.
Require Import IProofMode.

From stdpp Require Import coPset gmap.



(* TODO : 
  Divide isim/wsim? 
  ITactics & ITacticsAux
  Choose/Take/Assume/Guarantee
  unfolding assume/guarantee
*)

Ltac ired_l := try Red.prw ltac:(IRed._red_gen) 1 2 1 0.
Ltac ired_r := try Red.prw ltac:(IRed._red_gen) 1 1 1 0.
Ltac ired_both := ired_l; ired_r.
Ltac prep := cbn; ired_both.

Ltac _force_l :=
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, guarantee ?P >>= _) (_, _)) ] =>
    prep; iApply isim_guar_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, trigger (Choose _) >>= _) (_, _)) ] =>
    iApply isim_choose_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _  (_, trigger (Guarantee _) >>= _) (_, _)) ] =>
    iApply isim_guarantee_src
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose _) >>= _) (_, _)) ] =>
    iApply wsim_choose_src
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _  (_, trigger (Guarantee _) >>= _) (_, _)) ] =>
    iApply wsim_guarantee_src
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, unwrapN ?ox >>= _) (_, _)) ] =>
      (* let tvar := fresh "tmp" in *)
      (* let thyp := fresh "TMP" in *)
      (* remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar; *)
      (* let name := fresh "G" in *)
      (* destruct (ox) eqn:name; [|exfalso]; cycle 1 *)
      idtac
      (* let name := fresh "y" in *)
      (* iApply isim_unwrapN_src; iIntros (name) "%"; *)
      (* match goal with *)
      (* | [ H : _ |- _ ] => let name := fresh "G" in rename H into name; try rewrite name in * *)
      (* end *)
  end
.

Ltac _force_r :=
match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, assume ?P >>= _)) ] =>
    prep; iApply isim_asm_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _  (_, _) (_, trigger (Take _) >>= _)) ] =>
    iApply isim_take_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _  (_, _) (_, trigger (Assume _) >>= _)) ] =>
    iApply isim_assume_tgt
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _  (_, _) (_, trigger (Take _) >>= _)) ] =>
    iApply wsim_take_tgt
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _  (_, _) (_, trigger (Assume _) >>= _)) ] =>
    iApply wsim_assume_tgt

(* | [ |- environments.envs_entails _ (@wsim _ _ _ _ _ _ _ _ _ _ (_, _) (_, unwrapU ?ox >>= _)) ] =>
    idtac
| [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ (_, _) (_, assume ?P >>= _)) ] =>
    let name := fresh "G" in
    cut (P); [intros name; iApply wsim_assume_tgt; iSplitR; [iPureIntro; exact name|]|]; cycle 1 *)
end
.

Ltac iIntrosFresh H := iIntros H || iIntrosFresh (H ++ "'")%string.

Ltac _step := 
match goal with
(******* isim ******)
(** src **)
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) (_, _)) ] =>
    let name := fresh "y" in
    iApply isim_unwrapU_src; iIntros (name) "%";
    match goal with
    | [ H : _ |- _ ] => let name := fresh "G" in rename H into name; try rewrite name in *
    end
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, tau;; _) (_, _)) ] =>
    iApply isim_tau_src
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, trigger (SUpdate _) >>= _) (_, _)) ] =>
    iApply isim_supdate_src
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, trigger (sPut _) >>= _) (_, _)) ] =>
    iApply isim_sput_src
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, trigger sGet >>= _) (_, _)) ] =>
    iApply isim_sget_src
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _) (_, _)) ] =>
    let name := fresh "y" in
    iApply isim_take_src; iIntros (name)
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _  (_, trigger (Assume _) >>= _) (_, _)) ] =>
    iApply isim_assume_src; iIntrosFresh "ASM"
(** tgt **)
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, unwrapN ?ox >>= _)) ] =>
    let name := fresh "y" in
    iApply isim_unwrapN_tgt; iIntros (name) "%";
    match goal with
    | [ H : _ |- _ ] => let name := fresh "G" in rename H into name; try rewrite name in *
    end
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, tau;; _)) ] =>
    iApply isim_tau_tgt
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, trigger (SUpdate _) >>= _)) ] =>
    iApply isim_supdate_tgt
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, trigger (sPut _) >>= _)) ] =>
    iApply isim_sput_tgt
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, trigger sGet >>= _)) ] =>
    iApply isim_sget_tgt
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, trigger (Choose _) >>= _)) ] =>
    let name := fresh "y" in
    iApply isim_choose_tgt; iIntros (name)
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, trigger (Guarantee _) >>= _)) ] =>
    iApply isim_guarantee_tgt; iIntrosFresh "GRT"  
(** both **)
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, Ret _) (_, Ret _)) ] =>
    iApply isim_ret
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, trigger (Syscall _ _ _) >>= _) (_, trigger (Syscall _ _ _) >>= _)) ] =>
    iApply isim_syscall; iIntros "%"

(******* wsim ******)
(** src **)
| [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) (_, _)) ] =>
    let name := fresh "y" in
    iApply wsim_unwrapU_src; iIntros (name) "%";
    match goal with
    | [ H : _ |- _ ] => let name := fresh "G" in rename H into name; try rewrite name in *
    end
| [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, assume ?P >>= _) (_, _)) ] =>
    unfold assume; prep; iApply wsim_take_src; iIntros "%";
    match goal with
    | [ H : _ |- _ ] => let name := fresh "G" in rename H into name
    end
| [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, tau;; _) (_, _)) ] =>
    iApply wsim_tau_src
| [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (SUpdate _) >>= _) (_, _)) ] =>
    iApply wsim_supdate_src
| [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _) (_, _)) ] =>
    let name := fresh "y" in
    iApply wsim_take_src; iIntros (name)
| [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _  (_, trigger (Assume _) >>= _) (_, _)) ] =>
    iApply wsim_assume_src; iIntrosFresh "ASM"
(** tgt **)
| [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, _) (_, unwrapN ?ox >>= _)) ] =>
    let name := fresh "y" in
    iApply wsim_unwrapN_tgt; iIntros (name) "%";
    match goal with
    | [ H : _ |- _ ] => let name := fresh "G" in rename H into name; try rewrite name in *
    end
| [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, _) (_, guarantee ?P >>= _)) ] =>
    unfold guarantee; prep; iApply wsim_choose_tgt; iIntros "%";
    match goal with
    | [ H : _ |- _ ] => let name := fresh "G" in rename H into name
    end
| [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, _) (_, tau;; _)) ] =>
    iApply wsim_tau_tgt
| [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, _) (_, trigger (SUpdate _) >>= _)) ] =>
    iApply wsim_supdate_tgt
| [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, _) (_, trigger (Choose _) >>= _)) ] =>
    let name := fresh "y" in
    iApply wsim_choose_tgt; iIntros (name)
| [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, _) (_, trigger (Guarantee _) >>= _)) ] =>
    iApply wsim_guarantee_tgt; iIntrosFresh "GRT"  
(** both **)
| [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, Ret _) (_, Ret _)) ] =>
    iApply wsim_ret
| [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Syscall _ _ _) >>= _) (_, trigger (Syscall _ _ _) >>= _)) ] =>
    iApply wsim_syscall; iIntros "%"

end.

Ltac _call :=
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, trigger (Call ?x0 ?y0) >>= _) (_, trigger (Call ?x1 ?y1) >>= _)) ] =>
    iApply isim_call
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Call ?x0 ?y0) >>= _) (_, trigger (Call ?x1 ?y1) >>= _)) ] =>
    iApply wsim_call
  end.

Ltac _inline_l := 
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, trigger (Call ?x0 ?y0) >>= _) (_, _)) ] =>
    iApply isim_inline_src
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Call ?x0 ?y0) >>= _) (_, _)) ] =>
    iApply wsim_inline_src
  end.

Ltac _inline_r := 
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, trigger  (Call ?x0 ?y0) >>= _)) ] =>
    iApply isim_inline_tgt
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, _) (_, trigger (Call ?x0 ?y0) >>= _)) ] =>
    iApply wsim_inline_tgt
  end.     

Ltac des_pairs :=
  repeat match goal with
         | [H : context[let (_, _) := ?x in _] |- _] =>
             let n0 := fresh x in let n1 := fresh x in destruct x as [n0 n1]
         | |- context[let (_, _) := ?x in _] =>
             let n0 := fresh x in let n1 := fresh x in destruct x as [n0 n1]
         end.

Ltac step :=
  prep; try _step; simpl; des_pairs.
  (* repeat (prep; try _step; simpl; des_pairs). *)

(* Tactic Notation "steps!" := repeat (prep; try _step; try call; des_pairs). *)

(* Try to add on red database*)
Ltac _ired := (
  unfold fun_spec_hp, body_spec_hp;
  try rewrite ! interp_hAGEs_bind;
  try rewrite interp_hAGEs_tau;
  try rewrite interp_hAGEs_ret;
  try rewrite interp_hAGEs_call;
  try rewrite interp_hAGEs_triggere;
  try rewrite interp_hAGEs_assume;
  try rewrite interp_hAGEs_guarantee;
  try rewrite interp_hAGEs_triggerp;
  try rewrite interp_hAGEs_triggerUB;
  try rewrite interp_hAGEs_triggerNB;
  try rewrite interp_hAGEs_unwrapU;
  try rewrite interp_hAGEs_unwrapN;
  try rewrite interp_hAGEs_Assume;
  try rewrite interp_hAGEs_Guarantee;
  try rewrite interp_hAGEs_ext
).

Ltac _steps :=
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, (interp_hEs_hAGEs _ _ _) >>= _) (_, _)) ] =>
    _ired; step
    | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, (interp_hEs_hAGEs _ _ _) >>= _)) ] =>
    _ired; step
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, (interp_hEs_hAGEs _ _ _) >>= _) (_, _)) ] =>
    _ired; step
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, _) (_, (interp_hEs_hAGEs _ _ _) >>= _)) ] =>
    _ired; step
  | _ => step
  end.

Ltac _st :=
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, (translate _ (assume _)) >>= _) (_, _)) ] =>
    prep; rewrite translate_emb_asm; iApply isim_asm_src; iIntros "%";
    match goal with
    | [ H : _ |- _ ] => let name := fresh "G" in rename H into name
    end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, (translate _ (guarantee _)) >>= _)) ] =>
    prep; rewrite translate_emb_guar; iApply isim_guar_tgt; iIntros "%";
    match goal with
    | [ H : _ |- _ ] => let name := fresh "G" in rename H into name
    end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, (translate _ (trigger (Assume _))) >>= _) (_, _)) ] =>
    rewrite translate_emb_assume; step
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, (translate _ (trigger (Assume _))) >>= _)) ] =>
    rewrite translate_emb_assume; step
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, (translate _ (trigger (Guarantee _))) >>= _) (_, _)) ] =>
    rewrite translate_emb_guarantee; step
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, (translate _ (trigger (Guarantee _))) >>= _)) ] =>
    rewrite translate_emb_guarantee; step
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, (translate _ (interp_hEs_hAGEs _ _ _)) >>= _) (_, _)) ] =>
    _ired; step
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _  (_, _) (_, (translate _ (interp_hEs_hAGEs _ _ _)) >>= _)) ] =>
    _ired; step
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, (interp_hEs_hAGEs _ _ _) >>= _) (_, _)) ] =>
    _ired; step 
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, (interp_hEs_hAGEs _ _ _) >>= _)) ] =>
    _ired; step
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, (interp_hEs_hAGEs _ _ _) >>= _) (_, _)) ] =>
    _ired; step
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, _) (_, (interp_hEs_hAGEs _ _ _) >>= _)) ] =>
    _ired; step
  | _ => step
  end.

  Ltac sim_split := econs; [econs;eauto;grind;iIntrosFresh "IST"|try sim_split; try econs]. (* Move to Aux *)


(* iApply (@...) doesn't work in this way *)
(* Ltac _take := 
  let name := fresh "x" in  
  iApply isim_take_src; iIntros "%name"; iApply (@isim_take_tgt _ _ _ _ _ name _ _ _ _ _ ).
Ltac _choose :=
  let name := fresh "x" in  
  iApply isim_choose_tgt; iIntros "%name"; iApply (@isim_choose_src _ _ _ _ _ name _ _ _ _ _ ). *) *)
