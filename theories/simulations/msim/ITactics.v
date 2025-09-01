From iris.proofmode Require Import proofmode.
Require Import Common.
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

Ltac _istep_l :=
  match goal with
  (******* isim ******)
  (** src **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, tau;; _) _) ] =>
      iApply isim_tau_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, Ret _ >>= _) _) ] =>
      rewrite bind_ret_l
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, (SB.sandbox _ _ _ (trigger (SPut _ _))) >>= _) _) ] =>
      iApply isim_nodup_src; iIntros (?); iApply isim_sput_src_sandbox; [s;eauto|alist_upd_simpl]
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, (SB.sandbox _ _ _ (trigger (SGet _))) >>= _) _) ] =>
      iApply isim_nodup_src; iIntros (?); iApply isim_sget_src_sandbox; [s;eauto|alist_find_simpl]
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _) _) ] =>
      let name := fresh "_q" in
      iApply isim_take_src; iIntros (name)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _  (_, trigger (Assume ?P) >>= _) _) ] =>
      unfold_pre_post_term P; iApply isim_assume_src; iIntrosFresh "ASM"
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) _) ] =>
      let name := fresh "_q" in
      iApply isim_unwrapU_src; iIntros (name) "%";
      match goal with [ H: ?x = Some _ |- _ ] => let G := fresh "G" in rename H into G; try rewrite -> G in * end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, assume _ >>= _) _) ] =>
      let name := fresh "asm" in iApply isim_asm_src; iIntros (name)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, trigger (AssumeRes _) >>= _) _) ] =>
      iApply isim_assume_res_src; iIntrosFresh "ASM"
  end.

Ltac istep_l_core :=
  _istep_l; try alist_find_simpl; s; des_pairs; s.

Ltac istep_l :=
  norm_l with do 1 try istep_l_core.

Ltac isteps_l :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  norm_l;
  (hrepeat (do 1 istep_l_core; norm_l));
  show_until marker.

Ltac _istep_r :=
  match goal with
  (******* isim ******)
  (** tgt **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, Ret _ >>= _)) ] =>
      rewrite bind_ret_l
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, tau;; _)) ] =>
      iApply isim_tau_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, (SB.sandbox _ _ _ (trigger (SPut _ _))) >>= _)) ] =>
      iApply isim_nodup_tgt; iIntros (?); iApply isim_sput_tgt_sandbox; [s; eauto|alist_upd_simpl]
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, (SB.sandbox _ _ _ (trigger (SGet _))) >>= _)) ] =>
      iApply isim_nodup_tgt; iIntros (?); iApply isim_sget_tgt_sandbox; [s; eauto|alist_find_simpl]
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose _) >>= _)) ] =>
      let name := fresh "_q" in
      iApply isim_choose_tgt; iIntros (name)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _)) ] =>
      unfold_pre_post_term P; iApply isim_guarantee_tgt; iIntrosFresh "GRT"
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, unwrapN ?ox >>= _)) ] =>
      let name := fresh "_q" in
      iApply isim_unwrapN_tgt; iIntros (name) "%";
      match goal with [ H: ?x = Some _ |- _ ] => let G := fresh "G" in rename H into G; try rewrite -> G in * end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, guarantee _ >>= _)) ] =>
      let name := fresh "grt" in iApply isim_guar_tgt; iIntros (name)
  end.

Ltac istep_r_core :=
  _istep_r; s; des_pairs; s.

Ltac istep_r :=
  norm_r with do 1 try istep_r_core.

Ltac isteps_r :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  norm_r;
  (hrepeat (do 1 istep_r_core; norm_r));
  show_until marker.

Ltac _istep :=
  match goal with
  (******* isim ******)
  (** both **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, Ret _) (_, Ret _)) ] =>
      iApply isim_ret
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, trigger (IO _ _) >>= _) (_, trigger (IO _ _) >>= _)) ] =>
      iApply isim_io; iIntros "%"
  end.

Ltac istep :=
  norm with do 1 _istep; s; des_pairs; s.

Ltac _iforce_l :=
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, trigger (Choose ?T) >>= _) _) ] =>
      iApply isim_choose_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _) _) ] =>
      unfold_pre_post_term P; iApply isim_guarantee_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, unwrapN _ >>= _) _) ] =>
      iApply isim_unwrapN_src; iExists _
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ (_, guarantee _ >>= _) _) ] =>
      iApply isim_guar_src
  end
.

Ltac iforce_l_core :=
  norm_l with do 1 _iforce_l; s.

Tactic Notation "iforce_l" :=
  iforce_l_core; [..|try iExists _].

Tactic Notation "iforce_l" uconstr(p) :=
  iforce_l_core; [..|iExists p].

Ltac iforces_l :=
  hrepeat do 1 iforce_l.

Ltac _iforce_r :=
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _)) ] =>
      iApply isim_take_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, trigger (Assume ?P) >>= _)) ] =>
      unfold_pre_post_term P; iApply isim_assume_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, assume _ >>= _)) ] =>
      iApply isim_asm_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, unwrapU _ >>= _)) ] =>
      iApply isim_unwrapU_tgt; iExists _
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, trigger (AssumeRes _) >>= _)) ] =>
      iApply isim_assume_res_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, RealUpdate ?P ?Q >>= _)) ] =>
      unfold_pre_post_term P; unfold_pre_post_term Q; iApply isim_ru_tgt_simple
  end
.

Ltac iforce_r_core :=
  norm_r with do 1 _iforce_r; s.

Tactic Notation "iforce_r" :=
  iforce_r_core; try (iExists _).

Tactic Notation "iforce_r" uconstr(p) :=
  iforce_r_core; iExists p.

Ltac iforces_r := hrepeat do 1 iforce_r.

Ltac iinline_l :=
  norm_l with
    do 1 iApply isim_inline_src_sandbox; [try prove_inline_cond|unfold_cris_defs]. 

Ltac iinline_r :=
  norm_r with
    do 1 iApply isim_inline_tgt_sandbox; [try prove_inline_cond|try prove_sb_cond|unfold_cris_defs].

Ltac icall hyps :=
  (norm with do 1 iApply isim_call_sandbox); [try prove_sb_cond|
  iSplitL hyps; [try done|iIntros "% % %"; iIntrosFresh "IST"];
  move_aux].

Ltac ispawn :=
  (norm with do 1 iApply isim_spawn_sandbox); [try prove_sb_cond|].

Ltac iyield hyps :=
  (norm with do 1 iApply isim_yield);
  iSplitL hyps; [try done|iIntros "% %"; iIntrosFresh "IST"];
  move_aux.

Ltac iby_coind CIH :=
  iApply isim_progress; iApply isim_base;
  iApply CIH.

(** Special Tactics for RealUpdate **)

(* Tactic Notation "iru_l_advanced" uconstr(P) := *)
(*   norm_l; iApply isim_ru_src_advanced; *)
(*   iExists P; iSplit; [try prove_precise|]. *)

Tactic Notation "iru_l" uconstr(P) :=
  norm_l; iApply isim_ru_src;
  iExists P; iSplit; [try prove_precise|].

Ltac iru_r :=
  norm_r; iApply isim_ru_tgt.
