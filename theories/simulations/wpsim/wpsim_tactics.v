Require Import CRIS ltac2_lib.
Require Export wpsim.

From iris.proofmode Require Import coq_tactics environments.
(* ● ◓ ○ *)
Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '------------------------------params------------------------------' ○ n E r g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt" :=
  (environments.envs_entails (Envs E1 E2 _) (wpsim _ _ _ _ None _ _ n E r g _ _ _ ps pt _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '------------------------------params------------------------------' '//' ○ '/' n '/' E '/' r '/' g '/' ps '/' pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//'").
Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '------------------------------params------------------------------' ◓ n E r g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt" :=
  (environments.envs_entails (Envs E1 E2 _) (wpsim _ _ _ _ (Some false) _ _ n E r g _ _ _ ps pt _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '------------------------------params------------------------------' '//' ◓ '/' n '/' E '/' r '/' g '/' ps '/' pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//'").
Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '------------------------------params------------------------------' ● n E r g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt" :=
  (environments.envs_entails (Envs E1 E2 _) (wpsim _ _ _ _ (Some true) _ _ n E r g _ _ _ ps pt _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '------------------------------params------------------------------' '//' ● '/' n '/' E '/' r '/' g '/' ps '/' pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//'").
Notation "E1 '------------------------------------------------------------------□' st_src st_tgt '------------------------------params------------------------------' ○ n E r g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt" :=
  (environments.envs_entails (Envs E1 Enil _) (wpsim _ _ _ _ None _ _ n E r g _ _ _ ps pt _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' st_src '//' st_tgt '//' '------------------------------params------------------------------' '//' ○ '/' n '/' E '/' r '/' g '/' ps '/' pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//'").
Notation "E1 '------------------------------------------------------------------□' st_src st_tgt '------------------------------params------------------------------' ◓ n E r g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt" :=
  (environments.envs_entails (Envs E1 Enil _) (wpsim _ _ _ _ (Some false) _ _ n E r g _ _ _ ps pt _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' st_src '//' st_tgt '//' '------------------------------params------------------------------' '//' ◓ '/' n '/' E '/' r '/' g '/' ps '/' pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//'").
Notation "E1 '------------------------------------------------------------------□' st_src st_tgt '------------------------------params------------------------------' ● n E r g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt" :=
  (environments.envs_entails (Envs E1 Enil _) (wpsim _ _ _ _ (Some true) _ _ n E r g _ _ _ ps pt _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' st_src '//' st_tgt '//' '------------------------------params------------------------------' '//' ● '/' n '/' E '/' r '/' g '/' ps '/' pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//'").
Notation "E2 '------------------------------------------------------------------∗' st_src st_tgt '------------------------------params------------------------------' ○ n E r g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt" :=
  (environments.envs_entails (Envs Enil E2 _) (wpsim _ _ _ _ None _ _ n E r g _ _ _ ps pt _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
      format "E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '------------------------------params------------------------------' '//' ○ '/' n '/' E '/' r '/' g '/' ps '/' pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//'").
Notation "E2 '------------------------------------------------------------------∗' st_src st_tgt '------------------------------params------------------------------' ◓ n E r g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt" :=
  (environments.envs_entails (Envs Enil E2 _) (wpsim _ _ _ _ (Some false) _ _ n E r g _ _ _ ps pt _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
      format "E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '------------------------------params------------------------------' '//' ◓ '/' n '/' E '/' r '/' g '/' ps '/' pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//'").
Notation "E2 '------------------------------------------------------------------∗' st_src st_tgt '------------------------------params------------------------------' ● n E r g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt" :=
  (environments.envs_entails (Envs Enil E2 _) (wpsim _ _ _ _ (Some true) _ _ n E r g _ _ _ ps pt _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
      format "E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '------------------------------params------------------------------' '//' ● '/' n '/' E '/' r '/' g '/' ps '/' pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//'").

(* additional *) 
Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------wsim-------------------------------' P '∗' 'WSIM'" :=
  (environments.envs_entails (Envs E1 E2 _) (bi_sep P (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------wsim-------------------------------' '//' P  '∗'  'WSIM' ").

Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------wsim-------------------------------' P '-∗' 'WSIM'" :=
  (environments.envs_entails (Envs E1 E2 _) (bi_wand P (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------wsim-------------------------------' '//' P  '-∗'  'WSIM' ").

Ltac _w_step :=
  match goal with
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, Ret _) (_, Ret _))] =>
      iApply wpsim_ret
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (IO _ _) >>= _) (_, trigger (IO _ _) >>= _))] =>
      iApply wpsim_io; iIntros "%"
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Spawn _ _) >>= _) (_, trigger (Spawn _ _) >>= _))] =>
      iApply wpsim_spawn
  end.

Ltac _w_step_l :=
  match goal with
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, tau;; _) _) ] =>
      iApply wpsim_tau_src
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, Ret _ >>= _) _) ] =>
      rewrite bind_ret_l
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger Tid >>= _) _) ] =>
      iApply wpsim_tid_src
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _) _) ] =>
      let name := fresh "q" in iApply wpsim_take_src; iIntros (name)
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ ?υ _ ?n _ _ _ _ _ _ _ _ _ (_, trigger (Assume ?P) >>= _) _) ] =>
      first [
        tcsearch constr:(WP P υ n ⊤)
          ltac:(fun c =>
            iApply (wpsim_full_assume_src_WP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i:=c)); simpl);
        match goal with
        | [ |- environments.envs_entails _ (?P' -∗ _)] =>
          unfold_precond_postcond P'; iIntrosFresh "ASM"
        end
      | unfold_precond_postcond P; iApply wpsim_assume_src; iIntrosFresh "ASM"
      ]
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, assume _ >>= _) _) ] =>
      let name := fresh "asm" in iApply wpsim_asm_src; iIntros (name)
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, (HMod.sandbox _ (trigger (SPut _ _))) >>= _) _) ] =>
      iApply wpsim_sput_src_sandbox; [s;eauto|]
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, (HMod.sandbox _ (trigger (SGet _))) >>= _) _) ] =>
      iApply wpsim_sget_src_sandbox; [s;eauto|]
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) _) ] =>
      let name := fresh "q" in
      iApply wpsim_unwrapU_src; iIntros (name) "%";
      match goal with [ H: ?x = Some _ |- _ ] => let G := fresh "G" in rename H into G; try rewrite -> G in * end
  end.

Ltac w_step_l_core :=
  _w_step_l; try alist_find_simpl; s; des_pairs; s.

Ltac w_step :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_r; prep; show_itree;
  hide_itree_l; prep; show_itree;
  _w_step;
  show_until marker.

Ltac w_step_l :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_r;
  prep;
  w_step_l_core;
  show_until marker.

Ltac w_steps_l :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_r;
  (hrepeat do 1 (prep; w_step_l_core));
  show_until marker.

Ltac _w_step_r :=
  match goal with
  (******* isim ******)
  (** tgt **)
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, tau;; _)) ] =>
      iApply wpsim_tau_tgt
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, Ret _ >>= _) ) ] =>
      rewrite bind_ret_l
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose _) >>= _) ) ] =>
      let name := fresh "q" in iApply wpsim_choose_tgt; iIntros (name)
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ ?ν ?n _ _ _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _) ) ] =>
      first [
        tcsearch constr:(WP P ν n ⊤)
          ltac:(fun c =>
            iApply (wpsim_half_guarantee_tgt_WP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i:=c)); simpl);
        match goal with
        | [ |- environments.envs_entails _ (?P' -∗ _)] =>
          unfold_precond_postcond P'; iIntrosFresh "GRT"
        end
      | unfold_precond_postcond P; iApply wpsim_guarantee_tgt; iIntrosFresh "GRT"
      ]
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, guarantee _ >>= _)) ] =>
      let name := fresh "grt" in iApply wpsim_guar_tgt; iIntros (name)
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, (HMod.sandbox _ (trigger (SPut _ _))) >>= _)) ] =>
      iApply wpsim_sput_tgt_sandbox; [s; eauto|]
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, (HMod.sandbox _ (trigger (SGet _))) >>= _)) ] =>
      iApply wpsim_sget_tgt_sandbox; [s; eauto|]
  (* 
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, unwrapN ?ox >>= _)) ] =>
      let name := fresh "q" in
      iApply isim_unwrapN_tgt; iIntros (name) "%";
      match goal with [ H: ?x = Some _ |- _ ] => let G := fresh "G" in rename H into G; try rewrite -> G in * end
*)
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger Tid >>= _)) ] =>
      iApply wpsim_tid_tgt
  end.

Ltac w_step_r_core :=
  _w_step_r; try alist_find_simpl; s; des_pairs; s.

Ltac w_step_r :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_l;
  prep;
  w_step_r_core;
  show_until marker.

Ltac w_steps_r :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_l;
  (hrepeat do 1 (prep; w_step_r_core));
  show_until marker.

Ltac _w_force_l :=
  match goal with
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose ?T) >>= _) _) ] =>
      iApply wpsim_choose_src
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ ?υ _ ?n _ _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _) _) ] =>
      first [
        tcsearch constr:(WP P υ n ⊤)
          ltac:(fun c =>
            iApply (wpsim_full_guarantee_src_WP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i:=c)); simpl);
        match goal with
        | [ |- environments.envs_entails _ (?P' ∗ _)] =>
          unfold_precond_postcond P'
        end
      | unfold_precond_postcond P; iApply wpsim_guarantee_src
      ]
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, unwrapN _ >>= _) _) ] =>
      iApply wpsim_unwrapN_src
  (* | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, guarantee _ >>= _) _) ] =>
      iApply isim_guar_src *)
  end.

Ltac w_force_l_core :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_r;
  prep;
  _w_force_l;
  show_until marker.

Tactic Notation "w_force_l" :=
  w_force_l_core; try (iExists _).

Tactic Notation "w_force_l" uconstr(p) :=
  w_force_l_core; iExists p.

Ltac _w_force_r :=
  match goal with
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _)) ] =>
      iApply wpsim_take_tgt
  | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ ?ν ?n _ _ _ _ _ _ _ _ _ _ (_, trigger (Assume ?P) >>= _)) ] =>
      first [
        tcsearch constr:(WP P ν n ⊤)
          ltac:(fun c =>
            iApply (wpsim_half_assume_tgt_WP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i:=c)); simpl);
        match goal with
        | [ |- environments.envs_entails _ (?P' ∗ _)] =>
          unfold_precond_postcond P'
        end
      | unfold_precond_postcond P; iApply wpsim_assume_tgt
      ]
  (* | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, unwrapU _ >>= _)) ] =>
      iApply isim_unwrapU_tgt; iExists _
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, assume _ >>= _)) ] =>
      iApply isim_asm_tgt *)
  end
.

Ltac w_force_r_core :=
  let marker := fresh "MARKER" in
  set_marker marker;  
  hide_ihyps;
  hide_itree_l;
  prep;
  _w_force_r; s;
  show_until marker.

Tactic Notation "w_force_r" :=
  w_force_r_core; try (iExists _).

Tactic Notation "w_force_r" uconstr(p) :=
  w_force_r_core; iExists p.

Ltac w_inline_l :=
  let marker := fresh "MARKER" in
  set_marker marker;  
  hide_ihyps;
  hide_itree_r;
  prep;
  iApply wpsim_inline_src; [prove_inline_cond|];
  unfold_cris_defs;
  show_until marker.

Ltac w_inline_r :=
  let marker := fresh "MARKER" in
  set_marker marker;  
  hide_ihyps;
  hide_itree_l;
  prep;
  iApply wpsim_inline_tgt; [prove_inline_cond|];
  unfold_cris_defs;
  show_until marker.

Ltac by_coind CIH :=
  iApply wpsim_progress; iApply wpsim_base;
  iSpecialize (CIH $! _);
  (hrepeat do 1 first[instantiate (1:= (_,_))|instantiate (1:= existT _ _)]); s; grind;
  iApply CIH.

Ltac w_call hyps :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_r; prep; show_itree;
  hide_itree_l; prep; show_itree;
  iApply wpsim_call;
  show_until marker;
  iSplitL hyps; [try done | iIntros "% % % % % %"; iIntrosFresh "IST"];
  move_aux.

Ltac yield hyps :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_r; prep; show_itree;
  hide_itree_l; prep; show_itree;
  iApply wpsim_yield
  ; show_until marker
  ; iSplitL hyps; [try done | iIntros "% % % % %"; iIntrosFresh "IST"]
  ; move_aux
  .

Ltac init_simF :=
  pre_simF;
  alist_find_simpl;
  let H := fresh "H" in intro H; inv H;
  alist_find_simpl;
  post_simF;
  step_l.

Ltac init_wpsim :=
  init_simF;
  prep_l;
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _) _)] =>
    let name := fresh "q" in let n := fresh "n" in iApply isim_take_src; iIntros (name);
      prep; let varg := fresh "varg" in iApply isim_take_src; iIntros (varg);
      prep;
      match goal with
      | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _  (_, trigger (Assume ?P) >>= _) _) ] =>
        unfold_precond_postcond P; iApply isim_Assume_src; iIntros "[I ASM]";
        iApply wpsim_init; iSplitR "I"; last iExact "I"
      end
  end.

Ltac unfold_iter_l :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_r; rewrite unfold_iter_eq; show_itree;
  show_until marker.

Ltac unfold_iter_r :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  hide_itree_l; rewrite unfold_iter_eq; show_itree;
  show_until marker.