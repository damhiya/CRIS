From iris.proofmode Require Import proofmode.
Require Import Common ConcRA.
Require Import LAuto.

Require Import Sp LMod SMod Mod.
Require Import ISim TacticsCommon.

(**** TODO ****)
(* A tactic to handle meta variables *)

(************ User Notations **************)

(*** TODO: 
          What else should be displayed? 
          Simplify (hide) k-trees

***)

(***
  Step-level tactics
 ***)

Ltac _istep_s :=
  match goal with
  (******* isim ******)
  (** src **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, tau;; _) _) ] =>
      iApply isim_tau_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, Ret _ >>= _) _) ] =>
      rewrite bind_ret_l
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, trigger (Take (FSpec (fspec_to_rel _))) >>= _) _) ] =>
      let name := fresh "_q" in iApply isim_take_src_fspec; iIntros (name); simpl in name
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _) _) ] =>
      let name := fresh "_q" in
      iApply isim_take_src; iIntros (name)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _  (_, trigger (Assume ?P) >>= _) _) ] =>
      unfoldPrePost_term P; iApply isim_assume_src; iIntrosFresh "ASM"
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, trigger (AssumeRes _) >>= _) _) ] =>
      iApply isim_assume_res_src; iIntrosFresh "ASM"
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, assume _ >>= _) _) ] =>
      let name := fresh "ASM" in iApply isim_asm_src; iIntros (name)
  end.

Ltac istep_s_core :=
  _istep_s; try alist_find_simpl; s; des_pairs; s.

Ltac istep_s :=
  cNormS with do 1 try istep_s_core.

Ltac isteps_s :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  (hrepeat (do 1 cNormS; istep_s_core));
  try cNormS;
  show_until marker.

Ltac _istep_t :=
  match goal with
  (******* isim ******)
  (** tgt **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, Ret _ >>= _)) ] =>
      rewrite bind_ret_l
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, tau;; _)) ] =>
      iApply isim_tau_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose (FSpec (fspec_to_rel _))) >>= _) ) ] =>
      let name := fresh "_q" in iApply isim_choose_tgt_fspec; iIntros (name); simpl in name
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose _) >>= _)) ] =>
      let name := fresh "_q" in
      iApply isim_choose_tgt; iIntros (name)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _)) ] =>
      unfoldPrePost_term P; iApply isim_guarantee_tgt; iIntrosFresh "GRT"
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, guarantee _ >>= _)) ] =>
      let name := fresh "GRT" in iApply isim_guar_tgt; iIntros (name)
  end.

Ltac istep_t_core :=
  _istep_t; s; des_pairs; s.

Ltac istep_t :=
  cNormT with do 1 try istep_t_core.

Ltac isteps_t :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  (hrepeat (do 1 cNormT; istep_t_core));
  try cNormT;
  show_until marker.

Ltac _istep tac :=
  match goal with
  (******* isim ******)
  (** both **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, Ret _) (_, Ret _)) ] =>
      iApply isim_ret
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, trigger (IO _ _) >>= _) (_, trigger (IO _ _) >>= _)) ] =>
      iApply isim_io; tac
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, trigger GetTid >>= _) (_, trigger GetTid >>= _)) ] =>
      iApply isim_gettid; tac
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, trigger (Spawn _ _) >>= _) (_, trigger (Spawn _ _) >>= _)) ] =>
      iApply isim_spawn; tac
  end.

Tactic Notation "istep" ident(name) :=
  norm with do 1 _istep ltac:(iIntros (name)).

Tactic Notation "istep" :=
  norm with do 1 _istep ltac:(iIntros "%").

Ltac _iforce_s :=
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, trigger (Choose (FSpec (fspec_to_rel _))) >>= _) _) ] =>
      iApply isim_choose_src_fspec
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, trigger (Choose ?T) >>= _) _) ] =>
      iApply isim_choose_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _) _) ] =>
      unfoldPrePost_term P; iApply isim_guarantee_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, unwrapN _ >>= _) _) ] =>
      iApply isim_unwrapN_src; iExists _
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, guarantee _ >>= _) _) ] =>
      iApply isim_guar_src
  end
.

Ltac iforce_s_core :=
  cNormS with do 1 _iforce_s; s.

Tactic Notation "iforce_s" :=
  iforce_s_core; [..|try iExists _].

Tactic Notation "iforce_s" uconstr(p) :=
  iforce_s_core; [..|iExists p].

Ltac iforces_s :=
  hrepeat do 1 iforce_s.

Ltac _iforce_t :=
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, trigger (Take (FSpec (fspec_to_rel _))) >>= _)) ] =>
      iApply isim_take_tgt_fspec
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _)) ] =>
      iApply isim_take_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, trigger (Assume ?P) >>= _)) ] =>
      unfoldPrePost_term P; iApply isim_assume_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, assume _ >>= _)) ] =>
      iApply isim_asm_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, unwrapU _ >>= _)) ] =>
      iApply isim_unwrapU_tgt; iExists _
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, trigger (AssumeRes _) >>= _)) ] =>
      iApply isim_assume_res_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, RealUpdate (idx_to_rel ?P ?Q) >>= _)) ] =>
      unfoldPrePost_term P; unfoldPrePost_term Q; iApply isim_ru_tgt_simple
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, RealUpdate _ >>= _)) ] =>
      iApply isim_ru_tgt_simple_general
  end
.

Ltac iforce_t_core :=
  cNormT with do 1 _iforce_t; s.

Tactic Notation "iforce_t" :=
  iforce_t_core; try (iExists _).

Tactic Notation "iforce_t" uconstr(p) :=
  iforce_t_core; iExists p.

Ltac iforces_t := hrepeat do 1 iforce_t.

Ltac iinline_s :=
  cNormS with
    do 1 iApply isim_inline_src; [try prove_inline_cond|unfold_cris_defs]. 

Ltac iinline_t :=
  cNormT with
    do 1 iApply isim_inline_tgt; [try prove_inline_cond|unfold_cris_defs].

Ltac icall hyps :=
  (norm with do 1 iApply isim_call); iSplitL hyps; [try done|].

Ltac iyield hyps :=
  (norm with do 1 iApply isim_yield);
  iSplitL hyps; [try done|].

Ltac iby_coind CIH :=
  iApply isim_progress; iApply isim_base;
  iApply CIH.

Tactic Notation "ibind" uconstr(RR) :=
  iApply (isim_bind _ _ _ _ _ _ _ _ _ RR).

(** Special Tactics for RealUpdate **)

(* Tactic Notation "iru_s_advanced" uconstr(P) := *)
(*   cNormS; iApply isim_ru_src_advanced; *)
(*   iExists P; iSplit; [try prove_precise|]. *)

Tactic Notation "iru_s" uconstr(P) :=
  cNormS; iApply isim_ru_src;
  iExists P; iSplit; [try prove_precise|].

Ltac iru_t :=
  cNormT; iApply isim_ru_tgt.
