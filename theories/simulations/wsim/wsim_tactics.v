Require Import Common HMod ITactics ltac2_lib.
Require Export wsim.

From iris.proofmode Require Import coq_tactics environments.
(* ● ◓ ○ *)
Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '------------------------------params------------------------------' ○ E r g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt" :=
  (environments.envs_entails (Envs E1 E2 _) (wsim _ _ _ None _ _ E r g _ _ _ ps pt _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '------------------------------params------------------------------' '//' ○ '/' E '/' r '/' g '/' ps '/' pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//'").
Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '------------------------------params------------------------------' ◓ E r g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt" :=
  (environments.envs_entails (Envs E1 E2 _) (wsim _ _ _ (Some false) _ _ E r g _ _ _ ps pt _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '------------------------------params------------------------------' '//' ◓ '/' E '/' r '/' g '/' ps '/' pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//'").
Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '------------------------------params------------------------------' ● E r g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt" :=
  (environments.envs_entails (Envs E1 E2 _) (wsim _ _ _ (Some true) _ _ E r g _ _ _ ps pt _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '------------------------------params------------------------------' '//' ● '/' E '/' r '/' g '/' ps '/' pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//'").
Notation "E1 '------------------------------------------------------------------□' st_src st_tgt '------------------------------params------------------------------' ○ E r g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt" :=
  (environments.envs_entails (Envs E1 Enil _) (wsim _ _ _ None _ _ E r g _ _ _ ps pt _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' st_src '//' st_tgt '//' '------------------------------params------------------------------' '//' ○ '/' E '/' r '/' g '/' ps '/' pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//'").
Notation "E1 '------------------------------------------------------------------□' st_src st_tgt '------------------------------params------------------------------' ◓ E r g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt" :=
  (environments.envs_entails (Envs E1 Enil _) (wsim _ _ _ (Some false) _ _ E r g _ _ _ ps pt _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' st_src '//' st_tgt '//' '------------------------------params------------------------------' '//' ◓ '/' E '/' r '/' g '/' ps '/' pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//'").
Notation "E1 '------------------------------------------------------------------□' st_src st_tgt '------------------------------params------------------------------' ● E r g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt" :=
  (environments.envs_entails (Envs E1 Enil _) (wsim _ _ _ (Some true) _ _ E r g _ _ _ ps pt _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' st_src '//' st_tgt '//' '------------------------------params------------------------------' '//' ● '/' E '/' r '/' g '/' ps '/' pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//'").
Notation "E2 '------------------------------------------------------------------∗' st_src st_tgt '------------------------------params------------------------------' ○ E r g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt" :=
  (environments.envs_entails (Envs Enil E2 _) (wsim _ _ _ None _ _ E r g _ _ _ ps pt _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
      format "E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '------------------------------params------------------------------' '//' ○ '/' E '/' r '/' g '/' ps '/' pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//'").
Notation "E2 '------------------------------------------------------------------∗' st_src st_tgt '------------------------------params------------------------------' ◓ E r g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt" :=
  (environments.envs_entails (Envs Enil E2 _) (wsim _ _ _ (Some false) _ _ E r g _ _ _ ps pt _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
      format "E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '------------------------------params------------------------------' '//' ◓ '/' E '/' r '/' g '/' ps '/' pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//'").
Notation "E2 '------------------------------------------------------------------∗' st_src st_tgt '------------------------------params------------------------------' ● E r g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt" :=
  (environments.envs_entails (Envs Enil E2 _) (wsim _ _ _ (Some true) _ _ E r g _ _ _ ps pt _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
      format "E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '------------------------------params------------------------------' '//' ● '/' E '/' r '/' g '/' ps '/' pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//'").

(* additional *) 
Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------wsim-------------------------------' P '∗' 'WSIM'" :=
  (environments.envs_entails (Envs E1 E2 _) (bi_sep P (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------wsim-------------------------------' '//' P  '∗'  'WSIM' ").

Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------wsim-------------------------------' P '-∗' 'WSIM'" :=
  (environments.envs_entails (Envs E1 E2 _) (bi_wand P (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------wsim-------------------------------' '//' P  '-∗'  'WSIM' ").


Ltac w_replace_l :=
  lazymatch goal with
  | [ |- environments.envs_entails ?env (wsim ?fl_src ?tl_tgt ?Ist ?t ?u ?v ?E ?r ?g ?R_s ?R_t ?RR ?ps ?pt ?nths (?st_src, ?itr_src) (?st_tgt, ?itr_tgt)) ] =>
      refine (eq_ind_r (fun itr_src' => environments.envs_entails env (wsim fl_src tl_tgt Ist t u v E r g R_s R_t RR ps pt nths (st_src, itr_src') (st_tgt, itr_tgt))) _ _); cycle 1
  end.

Ltac w_replace_r :=
  lazymatch goal with
  | [ |- environments.envs_entails ?env (wsim ?fl_src ?tl_tgt ?Ist ?t ?u ?v ?E ?r ?g ?R_s ?R_t ?RR ?ps ?pt ?nths (?st_src, ?itr_src) (?st_tgt, ?itr_tgt)) ] =>
      refine (eq_ind_r (fun itr_tgt' => environments.envs_entails env (wsim fl_src tl_tgt Ist t u v E r g R_s R_t RR ps pt nths (st_src, itr_src) (st_tgt, itr_tgt'))) _ _); cycle 1
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

Ltac w_hnorm_l := w_replace_l; [s; hnorm_itr|].
Ltac w_hnorm_r := w_replace_r; [s; hnorm_itr|].
Ltac _w_step :=
  match goal with
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, Ret _) (_, Ret _))] =>
      iApply wsim_ret
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (IO _ _) >>= _) (_, trigger (IO _ _) >>= _))] =>
      iApply wsim_io; iIntros "%"
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Spawn _ _) >>= _) (_, trigger (Spawn _ _) >>= _))] =>
      iApply wsim_spawn
  end.

Ltac _w_step_l :=
  match goal with
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, tau;; _) _) ] =>
      iApply wsim_tau_src
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, Ret _ >>= _) _) ] =>
      rewrite bind_ret_l
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _) _) ] =>
      let name := fresh "q" in iApply wsim_take_src; iIntros (name)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ ?υ _ _ _ _ _ _ _ _ _ _ (_, trigger (Assume ?P) >>= _) _) ] =>
      first [
        tcsearch constr:(WP P υ ⊤)
          ltac:(fun c =>
            iApply (wsim_full_assume_src_WP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i:=c)); simpl);
        match goal with
        | [ |- environments.envs_entails _ (?P' -∗ _)] =>
          unfold_precond_postcond P'; iIntrosFresh "ASM"
        end
      | unfold_precond_postcond P; iApply wsim_assume_src; iIntrosFresh "ASM"
      ]
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, assume _ >>= _) _) ] =>
      let name := fresh "asm" in iApply wsim_asm_src; iIntros (name)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, (HMod.sandbox _ (trigger (SPut _ _))) >>= _) _) ] =>
      iApply wsim_sput_src_sandbox; [s;eauto|]
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, (HMod.sandbox _ (trigger (SGet _))) >>= _) _) ] =>
      iApply wsim_sget_src_sandbox; [s;eauto|]
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) _) ] =>
      let name := fresh "q" in
      iApply wsim_unwrapU_src; iIntros (name) "%";
      match goal with [ H: ?x = Some _ |- _ ] => let G := fresh "G" in rename H into G; try rewrite -> G in * end
  end.

Ltac w_step_l_core :=
  _w_step_l; try alist_find_simpl; s; des_pairs; s.

Ltac w_step :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  (hrepeat do 1 w_hnorm_l);
  (hrepeat do 1 w_hnorm_r);
  _w_step;
  show_until marker.

Ltac w_step_l :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  (hrepeat do 1 w_hnorm_l);
  try w_step_l_core;
  show_until marker.

Ltac w_steps_l :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  (hrepeat do 1 tryany (do 1 w_hnorm_l) (do 1 w_step_l_core)); try w_hnorm_l;
  show_until marker.

Ltac _w_step_r :=
  match goal with
  (******* isim ******)
  (** tgt **)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, tau;; _)) ] =>
      iApply wsim_tau_tgt
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, Ret _ >>= _) ) ] =>
      rewrite bind_ret_l
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose _) >>= _) ) ] =>
      let name := fresh "q" in iApply wsim_choose_tgt; iIntros (name)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ ?ν _ _ _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _) ) ] =>
      first [
        tcsearch constr:(WP P ν ⊤)
          ltac:(fun c =>
            iApply (wsim_half_guarantee_tgt_WP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i:=c)); simpl);
        match goal with
        | [ |- environments.envs_entails _ (?P' -∗ _)] =>
          unfold_precond_postcond P'; iIntrosFresh "GRT"
        end
      | unfold_precond_postcond P; iApply wsim_guarantee_tgt; iIntrosFresh "GRT"
      ]
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, guarantee _ >>= _)) ] =>
      let name := fresh "grt" in iApply wsim_guar_tgt; iIntros (name)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, (HMod.sandbox _ (trigger (SPut _ _))) >>= _)) ] =>
      iApply wsim_sput_tgt_sandbox; [s; eauto|]
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, (HMod.sandbox _ (trigger (SGet _))) >>= _)) ] =>
      iApply wsim_sget_tgt_sandbox; [s; eauto|]
  (* 
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, unwrapN ?ox >>= _)) ] =>
      let name := fresh "q" in
      iApply isim_unwrapN_tgt; iIntros (name) "%";
      match goal with [ H: ?x = Some _ |- _ ] => let G := fresh "G" in rename H into G; try rewrite -> G in * end
*)
  end.

Ltac w_step_r_core :=
  _w_step_r; try alist_find_simpl; s; des_pairs; s.

Ltac w_step_r :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  (hrepeat do 1 w_hnorm_r);
  try w_step_r_core;
  show_until marker.

Ltac w_steps_r :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  (hrepeat do 1 tryany (do 1 w_hnorm_r) (do 1 w_step_r_core)); try w_hnorm_r;
  show_until marker.

Ltac _w_force_l :=
  match goal with
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose ?T) >>= _) _) ] =>
      iApply wsim_choose_src
  | [ |- environments.envs_entails _ (wsim _ _ _ _ ?υ _ _ _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _) _) ] =>
      first [
        tcsearch constr:(WP P υ ⊤)
          ltac:(fun c =>
            iApply (wsim_full_guarantee_src_WP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i:=c)); simpl);
        match goal with
        | [ |- environments.envs_entails _ (?P' ∗ _)] =>
          unfold_precond_postcond P'
        end
      | unfold_precond_postcond P; iApply wsim_guarantee_src
      ]
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, unwrapN _ >>= _) _) ] =>
      iApply wsim_unwrapN_src
  (* | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, guarantee _ >>= _) _) ] =>
      iApply isim_guar_src *)
  end.

Ltac w_force_l_core :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  (hrepeat do 1 w_hnorm_l);
  _w_force_l;
  show_until marker.

Tactic Notation "w_force_l" :=
  w_force_l_core; try (iExists _).

Tactic Notation "w_force_l" uconstr(p) :=
  w_force_l_core; iExists p.

Ltac w_forces_l :=
  hrepeat do 1 w_force_l.

Ltac _w_force_r :=
  match goal with
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _)) ] =>
      iApply wsim_take_tgt
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ ?ν _ _ _ _ _ _ _ _ _ _ (_, trigger (Assume ?P) >>= _)) ] =>
      first [
        tcsearch constr:(WP P ν ⊤)
          ltac:(fun c =>
            iApply (wsim_half_assume_tgt_WP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (i:=c)); simpl);
        match goal with
        | [ |- environments.envs_entails _ (?P' ∗ _)] =>
          unfold_precond_postcond P'
        end
      | unfold_precond_postcond P; iApply wsim_assume_tgt
      ]
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, assume _ >>= _)) ] =>
      iApply wsim_asm_tgt
  (* | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, unwrapU _ >>= _)) ] =>
      iApply isim_unwrapU_tgt; iExists _ *)
  end
.

Ltac w_force_r_core :=
  let marker := fresh "MARKER" in
  set_marker marker;  
  hide_ihyps;
  (hrepeat do 1 w_hnorm_r);
  _w_force_r; s;
  show_until marker.

Tactic Notation "w_force_r" :=
  w_force_r_core; try (iExists _).

Tactic Notation "w_force_r" uconstr(p) :=
  w_force_r_core; iExists p.

Ltac w_forces_r :=
  hrepeat do 1 w_force_r.

Ltac w_inline_l :=
  let marker := fresh "MARKER" in
  set_marker marker;  
  hide_ihyps;
  (hrepeat do 1 w_hnorm_l);
  iApply wsim_inline_src; [prove_inline_cond|];
  unfold_cris_defs;
  show_until marker.

Ltac w_inline_r :=
  let marker := fresh "MARKER" in
  set_marker marker;  
  hide_ihyps;
  (hrepeat do 1 w_hnorm_r);
  iApply wsim_inline_tgt; [prove_inline_cond|];
  unfold_cris_defs;
  show_until marker.

Ltac by_coind CIH :=
  iApply wsim_progress; iApply wsim_base;
  iSpecialize (CIH $! _);
  (hrepeat do 1 first[instantiate (1:= (_,_))|instantiate (1:= existT _ _)]); s; grind;
  iApply CIH.

Ltac w_call hyps :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  (hrepeat do 1 w_hnorm_l);
  (hrepeat do 1 w_hnorm_r);
  iApply wsim_call;
  show_until marker;
  iSplitL hyps; [try done | iIntros "% % % % % %"; iIntrosFresh "IST"];
  move_aux.

Ltac yield hyps :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  (hrepeat do 1 w_hnorm_l);
  (hrepeat do 1 w_hnorm_r);
  iApply wsim_yield
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

Ltac init_wsim u_src u_tgt :=
  init_simF; iApply (wsim_init _ _ _ u_src u_tgt).

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