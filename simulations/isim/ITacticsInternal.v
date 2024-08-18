Require Import Coqlib ITreelib sflib.
Require Import STS.
Require Import Behavior.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Any.
Require Import Events STB ModSim.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
Require Import Red IRed.
Require Import HPSim.
Require Import World sWorld.
Require Import ISimCore HMod SMod.

From stdpp Require Import coPset gmap.

(* TODO: 
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
    | [ H: _ |- _ ] => let name := fresh "G" in rename H into name; try rewrite name in *
    end
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, tau;; _) (_, _)) ] =>
    iApply isim_tau_src
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, trigger (SPut _ _) >>= _) (_, _)) ] =>
    iApply isim_sput_src_wrap
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, trigger (SGet _) >>= _) (_, _)) ] =>
    iApply isim_sget_src_wrap
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
    | [ H: _ |- _ ] => let name := fresh "G" in rename H into name; try rewrite name in *
    end
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, tau;; _)) ] =>
    iApply isim_tau_tgt
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, trigger (SPut _ _) >>= _)) ] =>
    iApply isim_sput_tgt_wrap
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, trigger (SGet _) >>= _)) ] =>
    iApply isim_sget_tgt_wrap
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, trigger (Choose _) >>= _)) ] =>
    let name := fresh "y" in
    iApply isim_choose_tgt; iIntros (name)
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, trigger (Guarantee _) >>= _)) ] =>
    iApply isim_guarantee_tgt; iIntrosFresh "GRT"  
(** both **)
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, Ret _) (_, Ret _)) ] =>
    iApply isim_ret
| [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, trigger (IO _ _) >>= _) (_, trigger (IO _ _) >>= _)) ] =>
    iApply isim_io; iIntros "%"
end.

Ltac des_pairs :=
  repeat match goal with
         | [H: context[let (_, _) := ?x in _] |- _] =>
             let n0 := fresh x in let n1 := fresh x in destruct x as [n0 n1]
         | |- context[let (_, _) := ?x in _] =>
             let n0 := fresh x in let n1 := fresh x in destruct x as [n0 n1]
         end.

Ltac step := prep; try _step; simpl; des_pairs.

(* Try to add on red database*)
Ltac _ired := (
  (* try rewrite ! interp_hmodE_bind; *)
  (* try rewrite interp_hmodE_tau; *)
  (* try rewrite interp_hmodE_ret; *)
  (* try rewrite interp_hmodE_call; *)
  (* try rewrite interp_hmodE_triggere; *)
  (* try rewrite interp_hmodE_assume; *)
  (* try rewrite interp_hmodE_guarantee; *)
  (* try rewrite interp_hmodE_triggerp; *)
  (* try rewrite interp_hmodE_triggerUB; *)
  (* try rewrite interp_hmodE_triggerNB; *)
  (* try rewrite interp_hmodE_unwrapU; *)
  (* try rewrite interp_hmodE_unwrapN; *)
  (* try rewrite interp_hmodE_Assume; *)
  (* try rewrite interp_hmodE_Guarantee; *)
  (* try rewrite interp_hmodE_ext *)
  idtac               
).


Ltac _steps :=
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, (interp_smod _ _ _) >>= _) (_, _)) ] =>
    _ired; step
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, (interp_smod _ _ _) >>= _)) ] =>
    _ired; step
  | _ => step
  end.

Ltac _st :=
  match goal with
  (* | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, (translate _ (assume _)) >>= _) (_, _)) ] => *)
  (*   prep; rewrite HModRed.translate_wrap_asm; iApply isim_asm_src; iIntros "%"; *)
  (*   match goal with *)
  (*   | [ H: _ |- _ ] => let name := fresh "G" in rename H into name *)
  (*   end *)
  (* | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, (translate _ (guarantee _)) >>= _)) ] => *)
  (*   prep; rewrite HModRed.translate_wrap_guar; iApply isim_guar_tgt; iIntros "%"; *)
  (*   match goal with *)
  (*   | [ H: _ |- _ ] => let name := fresh "G" in rename H into name *)
  (*   end *)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, (translate _ (trigger (Assume _))) >>= _) (_, _)) ] =>
    rewrite HModWrap.transl_Assume; step
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, (translate _ (trigger (Assume _))) >>= _)) ] =>
    rewrite HModWrap.transl_Assume; step
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, (translate _ (trigger (Guarantee _))) >>= _) (_, _)) ] =>
    rewrite HModWrap.transl_Guarantee; step
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, (translate _ (trigger (Guarantee _))) >>= _)) ] =>
    rewrite HModWrap.transl_Guarantee; step
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, (translate _ (interp_smod _ _ _)) >>= _) (_, _)) ] =>
    _ired; step
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _  (_, _) (_, (translate _ (interp_smod _ _ _)) >>= _)) ] =>
    _ired; step
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, (interp_smod _ _ _) >>= _) (_, _)) ] =>
    _ired; step 
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, (interp_smod _ _ _) >>= _)) ] =>
    _ired; step
  | _ => step
  end.

  Ltac sim_split := econs; [econs;eauto;grind;iIntrosFresh "IST"|try sim_split; try econs].
