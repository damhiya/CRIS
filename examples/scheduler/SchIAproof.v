Require Import CRIS.


Require Import SchHeader SchI SchA SchASpec wpsim.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module SchIA. Section SchIA.
  Import SchAS.
  Context `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ, !SchAGΣ Σ}.
  Notation iProp := (iProp Σ).

  Variable υ : univ_id.
  Variable n : level.
  Variable StbFun: Sk.t -> string -> option fspec.
  Variable StbSch: Sk.t -> string -> option fspec.
  Hypothesis FunInStbSch: ∀ sk, stb_sub (StbFun sk) (StbSch sk).
  Hypothesis SchInStbSch: ∀ sk, stb_incl (Stb υ n sk StbFun) (StbSch sk).

  Fixpoint ths_wf (nths: nat) (ths_tgt: SchI.thslist): Prop :=
    match ths_tgt with
    | (tid, _) :: tl => (tid < nths) ∧ (ths_wf nths tl)
    | [] => True
    end.

  Inductive sim_ths (tid: nat): 
    (option (option SAny.t)) -> fragreeUR -> fragreeUR -> option iProp -> Prop :=
  | sim_ths_idle
    :
      sim_ths tid None None None None

  | sim_ths_active Q
    : 
      sim_ths tid
        (Some None)
        (Some (1%Qp, to_agree (λ s, Some (to_agree (Q s)))))
        (Some ((1/4)%Qp, to_agree (λ s, Some (to_agree (Q s)))))
        None

  | sim_ths_done rv Q
    : 
      sim_ths tid 
        (Some (Some rv))
        (Some (1%Qp, to_agree (λ s, Some (to_agree (Q s)))))
        (Some ((3/4)%Qp, to_agree (λ s, Some (to_agree (Q s)))))
        (Some (interp_cond (Q rv)))%I

  | sim_ths_joined rv Q
    :
      sim_ths tid
        (Some (Some rv))
        (Some (1%Qp, to_agree (λ s, Some (to_agree (Q s)))))
        (Some (1%Qp, to_agree (λ s, Some (to_agree (Q s)))))
        None
  .

  (**************************)

  Section AUX.

    Lemma ths_wf_nths_none ths_tgt nths:
      ths_wf nths ths_tgt -> alist_find nths ths_tgt = None.
    Proof.
      intro WF. induction ths_tgt; ss.
      destruct a. des. des_ifs; et. ss.
      rewrite eq_rel_dec_correct in Heq. des_ifs; try nia.
    Qed.

    Lemma wf_ths_src ths_tgt (ths_src_b ths_src_w: threadsF) (ths_cond: gmap nat iProp)
      (SIM: ∀ tid, sim_ths tid (alist_find tid ths_tgt) (ths_src_b tid) (ths_src_w tid) (ths_cond !! tid))
    :
      ✓ ths_src_b ∧ ✓ ths_src_w.
    Proof.
      split; intros x; specialize (SIM x); inv SIM; ss.
    Qed.

    Lemma big_sepM_replace (m: gmap nat iProp) i (Q: iProp):
      ([∗ map] P ∈ m, P) ∗ Q
      ⊢
      [∗ map] P ∈ <[i:=Q]> m, P.
    Proof.
      iIntros "[M Q]". destruct (m !! i) eqn:L.
      - iApply big_sepM_insert_delete. iFrame. 
        iPoseProof (big_sepM_delete with "M") as "[_ D]"; et.
      - iApply big_sepM_insert; et. iFrame.
    Qed.

  End AUX.

  Section ALIST.

    (* alist lemmas *)
    Lemma alist_replace_find_None {K V} `{Dec K} (k: K) (v v': V) (l: alist K V)
      (NONE: alist_find k l = None)
    :
      (alist_replace k v' l) = l.
    Proof.
      induction l; ss. destruct a. des_ifs. f_equal. et.
    Qed.

    Lemma alist_replace_find_eq_Some {K V} `{Dec K} (k: K) (v v': V) (l: alist K V)
      (SOME: alist_find k l = Some v)
    :
      alist_find k (alist_replace k v' l) = Some v'.
    Proof.
      induction l; ss. destruct a. des_ifs.
      - rewrite eq_rel_dec_correct in Heq. des_ifs. ss. des_ifs.
        rewrite eq_rel_dec_correct in Heq0. des_ifs.
      - rewrite eq_rel_dec_correct in Heq. des_ifs. apply IHl in SOME. ss.
        rewrite eq_rel_dec_correct. des_ifs.
    Qed.

    Lemma alist_replace_find_eq_None {K V} `{Dec K} (k: K) (v v': V) (l: alist K V)
      (NONE: alist_find k l = None)
    :
      alist_find k (alist_replace k v' l) = None.
    Proof.
      induction l; ss. destruct a. des_ifs.
      rewrite alist_replace_find_None; et. ss. des_ifs.
    Qed.

    Lemma alist_replace_find_neq_Some {K V} `{Dec K} (k k': K) (v v': V) (l: alist K V) (ov: option V)
      (NEQ: k <> k')
      (SOME: alist_find k' l = ov)
    :
      alist_find k' (alist_replace k v' l) = ov.
    Proof.
      induction l; ss. destruct a. rewrite eq_rel_dec_correct. 
      rewrite eq_rel_dec_correct in SOME.
      des_ifs; ss; des_ifs; rewrite eq_rel_dec_correct in Heq1; des_ifs; et.
    Qed.

    Lemma alist_remove_find_None {K V} `{Dec K} (k: K) (l: alist K V)
      (NONE: alist_find k l = None)
    :
      alist_remove k l = l.
    Proof.
      induction l; ss. destruct a; ss. rewrite eq_rel_dec_correct in NONE.
      rewrite eq_rel_dec_correct. des_ifs. f_equal. et.
    Qed.

  End ALIST.

  (**************************)

  Definition Ist: Sk.t -> nat -> alist key Any.t -> alist key Any.t -> iProp :=
    fun sk numths st_src st_tgt =>
      (∃ ths_tgt (ths_src_b ths_src_w: SchAS.threadsF) (ths_cond: gmap nat iProp), 
          ⌜st_tgt = [(SchI.v_ths, ths_tgt↑)] 
            ∧ <<THWF: ths_wf numths ths_tgt>>
            ∧ <<SIM: (∀ tid, sim_ths tid (alist_find tid ths_tgt) (ths_src_b tid) (ths_src_w tid) (ths_cond !! tid))>>
            ∧ <<NTHS: 0 < numths>>⌝
          ∗ own base_γ (● ths_src_b)
          ∗ own base_γ (◯ ths_src_w)
          ∗ ([∗ map] tid↦P ∈ ths_cond, P))%I.

  Local Notation SchAMod := (SchAS.t υ n StbFun StbSch).
  Local Notation SchIMod := (SchI.t).
  
  (*************)
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
(* Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------wsim-------------------------------' P '∗' 'ISIM'" :=
  (environments.envs_entails (Envs E1 E2 _) (bi_sep P (isim _ _ _ _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------wsim-------------------------------' '//' P  '∗'  'ISIM' ").

Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------wsim-------------------------------' P '-∗' 'ISIM'" :=
  (environments.envs_entails (Envs E1 E2 _) (bi_wand P (isim _ _ _ _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------wsim-------------------------------' '//' P  '-∗'  'ISIM' "). *)


  Ltac hide_itree_l marker :=
    hide_itree_all marker;
    match goal with [|- _ (_ _ (_, ?it))] => try unfold it end.

  Ltac hide_itree_r marker :=
    hide_itree_all marker;
    match goal with [|- _ (_ (_, ?it) _)] => try unfold it end.

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
    | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Assume ?P) >>= _) _) ] =>
        unfold_precond_postcond P; iApply wpsim_assume_src; iIntrosFresh "ASM"
    | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, (HModSem.sandbox _ (trigger (SPut _ _))) >>= _) _) ] =>
        iApply wpsim_sput_src_sandbox; [s;eauto|]
    | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, (HModSem.sandbox _ (trigger (SGet _))) >>= _) _) ] =>
        iApply wpsim_sget_src_sandbox; [s;eauto|]
    end.
    (* 
    | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _  (_, trigger (Assume ?P) >>= _) _) ] =>
        unfold_precond_postcond P; iApply isim_Assume_src; iIntrosFresh "ASM"
    | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) _) ] =>
        let name := fresh "q" in
        iApply isim_unwrapU_src; iIntros (name) "%";
        match goal with [ H: ?x = Some _ |- _ ] => let G := fresh "G" in rename H into G; try rewrite -> G in * end
    | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ (_, assume _ >>= _) _) ] =>
        let name := fresh "asm" in iApply isim_asm_src; iIntros (name)
    end. *)

  Ltac _w_step_r :=
    match goal with
    (******* isim ******)
    (** tgt **)
    | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, tau;; _)) ] =>
        iApply wpsim_tau_tgt
    | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, Ret _ >>= _) ) ] =>
        rewrite bind_ret_l
    | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, (HModSem.sandbox _ (trigger (SPut _ _))) >>= _)) ] =>
        iApply wpsim_sput_tgt_sandbox; [s; eauto|]
    | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, (HModSem.sandbox _ (trigger (SGet _))) >>= _)) ] =>
        iApply wpsim_sget_tgt_sandbox; [s; eauto|]
    (* 
    | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose _) >>= _)) ] =>
        let name := fresh "q" in
        iApply isim_choose_tgt; iIntros (name)
    | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _)) ] =>
        unfold_precond_postcond P; iApply isim_Guarantee_tgt; iIntrosFresh "GRT"
    | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ _ (_, unwrapN ?ox >>= _)) ] =>
        let name := fresh "q" in
        iApply isim_unwrapN_tgt; iIntros (name) "%";
        match goal with [ H: ?x = Some _ |- _ ] => let G := fresh "G" in rename H into G; try rewrite -> G in * end
    | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, guarantee _ >>= _)) ] =>
        let name := fresh "grt" in iApply isim_guar_tgt; iIntros (name) *)
    | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger Tid >>= _)) ] =>
        iApply wpsim_tid_tgt
    end.

  Ltac _w_force_l :=
    match goal with
    | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Choose ?T) >>= _) _) ] =>
        iApply wpsim_choose_src
    | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Guarantee ?P) >>= _) _) ] =>
        unfold_precond_postcond P; iApply wpsim_guarantee_src
    | [ |- environments.envs_entails _ (wpsim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (_, unwrapN _ >>= _) _) ] =>
        iApply wpsim_unwrapN_src
    (* | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, guarantee _ >>= _) _) ] =>
        iApply isim_guar_src *)
    end.

  Ltac w_force_l_core := let marker := fresh "MARKER" in
    hide_itree_r marker;
    prep; _w_force_l; s;
    show_itree marker.

  Tactic Notation "w_force_l" :=
    w_force_l_core; try (iExists _).

  Tactic Notation "w_force_l" uconstr(p) :=
    w_force_l_core; iExists p.

  Ltac w_step_l :=
    let marker := fresh "MARKER" in
    hide_itree_r marker;
    prep; _w_step_l; try alist_find_simpl; s; des_pairs; s;
    show_itree marker.

  Ltac w_step_r :=
    let marker := fresh "MARKER" in
    hide_itree_l marker;
    prep; _w_step_r; try alist_find_simpl; s; des_pairs; s;
    show_itree marker.

  Ltac by_coind CIH :=
    iApply wpsim_progress; iApply wpsim_base;
    iSpecialize (CIH $! _);
    (hrepeat do 1 first[instantiate (1:= (_,_))|instantiate (1:= existT _ _)]); s;
    iApply CIH.
  (* Ltac _step :=
    match goal with
    (******* isim ******)
    (** both **)
    | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, Ret _) (_, Ret _)) ] =>
        iApply isim_ret
    | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (IO _ _) >>= _) (_, trigger (IO _ _) >>= _)) ] =>
        iApply isim_io; iIntros "%"
    | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Spawn _ _) >>= _) (_, trigger (Spawn _ _) >>= _)) ] =>
        iApply isim_spawn
  end. *)
  (* Ltac w_step := let marker := fresh "MARKER" in
    hide_itree_r marker; prep; show_itree marker;
    hide_itree_l marker; prep; show_itree marker;
    _step; s; des_pairs; s. *)

  Ltac w_call hyps := let marker := fresh "MARKER" in
    hide_itree_r marker; prep; show_itree marker;
    hide_itree_l marker; prep; show_itree marker;
    iApply wpsim_call;
    iSplitL hyps; [try done | iIntros "% % % % % %"; iIntrosFresh "IST"];
    move_nodup.

  Ltac yield hyps := let marker := fresh "MARKER" in
    hide_itree_r marker; prep; show_itree marker;
    hide_itree_l marker; prep; show_itree marker;
    iApply wpsim_yield;
    iSplitL hyps; [try done | iIntros "% % % % %"; iIntrosFresh "IST"];
    move_nodup.

  Ltac init_simF :=
    pre_simF;
    alist_find_simpl;
    let H := fresh "H" in intro H; inv H;
    alist_find_simpl;
    post_simF;
    step_l.

  Ltac init_wpsim :=
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

  Lemma simF__spawn : HSim.sim_fun SchAMod SchIMod Ist SchName._spawn.
  Proof.
    init_simF.
    prep.
    init_wpsim.

    iDestruct "ASM" as "[%va [-> ASM]]"; hss.
    w_step_l.
    rename q1 into user.
    rename q3 into synpost.
    rename q5 into pre.
    rename q7 into uservarg.
    rename q8 into callerid.
    rename q9 into userarg.
    depdes user.
    rename m into userm.
    rename x into userf.
    iDestruct "ASM" as "[[% [% [% %]]] [PRE TOKEN]]"; clarify. hss.

    (* Process yield *)
    w_step_r. prep.
    iApply wpsim_full_guarantee_src; iSplitL ""; first rewrite /sch_ginv; iFrame; eauto.
    yield "IST".
    w_step_l.
    prep. iApply wpsim_full_assume_src; iSplitL ""; first rewrite /sch_ginv; iIntros "I"; iFrame.
    { iAssert (emp)%I as "E"; first done; iApply "E". }
    iClear "I".
    do 2 w_step_l.
    do 2 w_step_r.

    (* Call the spawnee *)
    prep. inv H1. rename x into userfspec. w_force_l userfspec; iFrame.
    iSplit.
    { iPureIntro; apply FunInStbSch; ss. }
    w_step_l.

    (* Choose the metavariables *)
    do 2 w_force_l.
    prep. iApply wpsim_full_guarantee_src. iSplitL "PRE".
    Unshelve.
    3:{ exact 1%positive. (* TODO : replace with ν *) }
    3:{ clear H2. unfold find_fsp in userm. rewrite H in userm. exact userm. }
    3:{ exact (userarg↑). }
    { unfold find_fsp in *. revert userm H2. generalize H.
      rewrite H. i.
      rewrite (UIP _ _ _ H0 eq_refl). erewrite <-rew_swap; et; ss.
      unfold fspec_spawnable in H2. des.
      iIntros "I"; iApply H2; iFrame.
    }

    w_call "IST"; et.
    w_step_l. rename q into vret.
    remember (existT userf userm) as DT; clear HeqDT.
    revert userm H2. generalize H. unfold find_fsp. rewrite H.
    i; ss. rewrite (UIP _ _ _ H0 eq_refl). erewrite <- rew_swap; ss.
    unfold fspec_spawnable in H2; des.
    prep. iApply wpsim_full_assume_src; iSplitL ""; iIntros "I".
    { iPoseProof (H1 $ ret with "[I]") as "H".
      { iExists _; iFrame. }
      { iExact "H". }
    }
    iDestruct "I" as (sret) "[% POST]".

    do 3 w_step_l.
    do 2 w_step_r. hss.
    do 5 w_step_r. w_step_r. w_step_r.
    iDestruct "IST" as (? ? ? ?) "(% & THB & THW & COND)". subst; hss.
    w_step_r. w_step_r. w_step_r. w_step_r. hss.

    remember ([(SchI.v_ths, ((alist_replace my_tid (Some sret) ths_tgt): thslist) ↑)]) as st_tgt1.
    iAssert (Ist sk nths'0 st_s'0 st_tgt1) with "[TOKEN THB THW COND POST]" as "IST".
    { destruct (alist_find my_tid ths_tgt) eqn:LU; cycle 1; [|destruct o].
      { (* idle case - impossible *)
        dup SIM. specialize (SIM my_tid). rewrite LU in SIM. inv SIM.
        iExists _, _, _, _. iFrame. iPureIntro. esplits; et.
        - clear SIM0. induction ths_tgt; ss. destruct a. rewrite eq_rel_dec_correct in LU.
          rewrite eq_rel_dec_correct. des_ifs. ss. des; split; et.
        - i. destruct (classic (tid = my_tid)).
          + subst. erewrite alist_replace_find_eq_None; et. 
            rewrite -H0 -H3 -H4. econs 1; et. exact None.
          + erewrite alist_replace_find_neq_Some; et. exact None.
      }
      { (* already done case - impossible *)
        dup SIM. specialize (SIM my_tid). rewrite LU in SIM. inv SIM.
        { (* done *)
          symmetry in H6. rewrite /token_half. unseal "SchA". iCombine "TOKEN THW" gives %X.
          exfalso. rewrite auth_frag_valid in X.
          specialize (X my_tid). rewrite discrete_fun_lookup_op in X. ss.
          rewrite -H5 in X. rewrite Nat.eqb_refl in X.
          rewrite Some_valid pair_valid in X; des. ss.
        }
        { (* joined *) 
          symmetry in H6. rewrite /token_half. unseal "SchA". iCombine "TOKEN THW" gives %X.
          exfalso. rewrite auth_frag_valid in X.
          specialize (X my_tid). rewrite discrete_fun_lookup_op in X. ss.
          rewrite -H5 in X. rewrite Nat.eqb_refl in X.
          rewrite Some_valid pair_valid in X; des. ss.
        }
      }
      { (* active - only possible case *)
        dup SIM. specialize (SIM my_tid). rewrite LU in SIM. inv SIM.
        rewrite /token_half. unseal "SchA".
        iCombine "TOKEN THW" gives %THW. iCombine "TOKEN THW" as "THW".

        rewrite auth_frag_valid in THW. ss.
        specialize (THW my_tid). rewrite discrete_fun_lookup_op in THW. rewrite Nat.eqb_refl in THW.
        rewrite -H3 in THW. rewrite// -Some_op Some_valid pair_valid in THW. des; ss.
        apply agree_op_inv in THW0.

        remember (λ s: SAny.t, Some (to_agree (synpost s)))%I as POSTF.
        iAssert (interp_cond (Q sret))%I with "[POST]" as "POST".
        { subst. apply (inj to_agree) in THW0. specialize (THW0 sret). ss. inv THW0.
          apply (inj to_agree) in H7. unfold interp_cond. rewrite H7. et. }

        assert (((((λ n : nat, if my_tid =? n then Some ((1/2)%Qp, to_agree POSTF) else ε) : threadsF) ⋅ ths_src_w): threadsF) ≡ ((λ n : nat, if my_tid =? n then Some ((3/4)%Qp, to_agree (λ s: SAny.t, Some (to_agree (Q s)))) else ths_src_w n): threadsF)).
        { intros y. rewrite discrete_fun_lookup_op. des_ifs. 2:rewrite left_id //.
          rewrite Nat.eqb_eq in Heq; subst. rewrite -H3 -Some_op -pair_op frac_op -THW0 agree_idemp.
          f_equiv. f_equiv. compute_done.
        }
        rewrite H5.

        iExists _, _, _, (<[my_tid:=(interp_cond (Q sret))%I]> ths_cond).
        iFrame. iSplitR "POST COND".
        - iPureIntro. esplits; et.
          + clear SIM0. induction ths_tgt; ss. destruct a; ss.
            rewrite eq_rel_dec_correct in LU. rewrite eq_rel_dec_correct. des_ifs. ss.
            des; split; et.
          + i. destruct (classic (tid = my_tid)).
            * subst. erewrite alist_replace_find_eq_Some; et. rewrite !lookup_insert. 
              rewrite Nat.eqb_refl. rewrite -H0. econs 3; et.
            * erewrite alist_replace_find_neq_Some; et. 2:exact None.
              des_ifs; [rewrite Nat.eqb_eq in Heq; subst; ss|].
              rewrite !lookup_insert_ne; et.
        - iApply big_sepM_replace; iFrame.
      }
    }

    (* Coinduction on yield loop *)
    rewrite !/Sch.terminate /ccallU. unseal "Sch".
    clear THWF SIM NTHS Heqst_tgt1.
    iApply wpsim_reset.
    iStopProof. revert NODUP.
    combine_quant NODS1.
    combine_quant st_tgt1.
    combine_quant st_s'0.
    combine_quant nths'0.
    eapply wpsim_coind. i.
    destruct a as [nths1 [st_src1 [st_tgt1 [NODS1 NODD1]]]]. s.
    iIntros "IST _ #CIH".
    (* Check unfold_iter_eq. *)
    (* iStopProof. *)
    rewrite {2}(@unfold_iter_eq hmodE). rewrite {2}(@unfold_iter_eq pmodE).
    w_step_l. w_step_l. w_force_l tt. w_force_l.
    prep. hide_itree_r marker. prep.
    iApply wpsim_full_guarantee_src; iSplitL "".
    { unfold precond; ss. iIntros "$". ss. }
    show_itree marker.
    w_call "IST".
    w_step_l.
    hide_itree_r marker. prep.
    iApply wpsim_full_assume_src; iSplitL ""; first rewrite /sch_ginv; iIntros "I"; iFrame.
    show_itree marker.
    do 3 w_step_l. rewrite {2}/postcond; ss. iDestruct "I" as "[-> ->]". hss.
    do 3 w_step_l.
    do 2 w_step_r. hss. do 3 w_step_r.
    iApply wpsim_progress; iApply wpsim_base;
    iSpecialize ("CIH" $! _);
    (hrepeat do 1 first[instantiate (1:= (_,_))|instantiate (1:= existT _ _)]); s.
    iApply "CIH".
    done.
    Unshelve. all: ss.
  Qed.

  Lemma simF_spawn:
    HSim.sim_fun SchAMod SchIMod Ist SchName.spawn.
  Proof.
    init_simF.

    steps_l. hss. destruct q2; ss.
    iDestruct "ASM" as "[W (% & % & (% & % & [% %] & %) & PRE)]"; des; subst; hss.
    steps_r. unfold HoareSpawn. force_l (my_tid, q7, q8, q6, q4, existT x m).
    force_l ((my_tid, x, q7)↑). step. steps_r.

    iDestruct "IST" as (? ? ? ?) "(% & THB & THW & COND)". subst; hss. steps_r.

    (* create new token *)
    dup THWF. apply ths_wf_nths_none in THWF. hexploit (SIM nths). i. rewrite THWF in H. inv H.

    iCombine "THB THW" as "TH".
    iPoseProof (own_update with "TH") as "TH".
    { apply shot_thread with (Q:=q4). split; et. apply wf_ths_src in SIM. et. }
    iApply isim_upd. iMod "TH" as "[[[[THB THW] TKNH] TKNQ1] TKNQ0]". iModIntro.

    force_l. iSplitL "PRE TKNH".
    { iIntros "W". rewrite /token_half. unseal "SchA". iFrame. iPureIntro. esplits; et. }

    steps_l. forces_l. iSplitL "W"; et.

    (* build IST *)
    rewrite /alist_upd /_alist_upd /=.
    set (st_tgt0 := [(SchI.v_ths, ((alist_add nths None ths_tgt): thslist)↑)]).
    iAssert (Ist sk (S nths) st_src st_tgt0) with "[COND THB THW TKNQ1]" as "IST".
    { iCombine "THW TKNQ1" as "THW". iExists _, _, _, _. iFrame.
      iPureIntro. esplits; et.
      - clear SIM. ss. split; [nia|]. rewrite alist_remove_find_None; et.
        induction ths_tgt; ss. destruct a. rewrite eq_rel_dec_correct in THWF.
        des; des_ifs; split; [nia|et].
      - i. destruct (classic (tid = nths)).
        + subst. rewrite alist_add_find_eq. 
          rewrite !discrete_fun_lookup_op Nat.eqb_refl -H1 left_id -H4.
          econs 2; et.
        + rewrite alist_add_find_neq; et.
          rewrite discrete_fun_lookup_op.
          des_ifs; [rewrite Nat.eqb_eq in Heq; subst; ss|].
          rewrite right_id. et. }

    hide_itree_r marker; prep; hide_itree_l marker2; prep; show_itree marker; show_itree marker2.
    iApply isim_yield. iSplitL "IST"; et. iIntros (? ? ? ? ?) "IST".

    steps_l. iDestruct "ASM" as "W". rewrite /sch_ginv.
    steps_r. forces_l. iSplitL "W TKNQ0".
    { iFrame. iExists nths; iSplit; et. }

    step. iSplit; et.
  Qed.

  Lemma simF_yield:
    HSim.sim_fun SchAMod SchIMod Ist SchName.yield.
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "(W & % & %)". des; subst; hss.
    
    steps_r. iDestruct "IST" as (? ? ? ?) "(% & THB & THW & COND)". subst; hss. steps_r.
    force_l. instantiate (1:=q). steps_l. force_l. iSplitL "W"; et.
    
    (* yield *)
    do 10 prep.
    iApply isim_yield.
    iSplitL.
    { iExists _, _, _, _. iSplit; et. iFrame. }
    iIntros (? ? ? ? ?) "IST".

    steps_l. unfold sch_ginv. iDestruct "ASM" as (?) "W".
    steps_r. steps_r. force_l. steps_l. forces_l. iSplitL "W"; et.
    step. iFrame; et.
  Qed.

  Lemma simF_join:
    HSim.sim_fun SchAMod SchIMod Ist SchName.join.
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "(W & [% TKN] & %)". subst; hss.
    steps_r.

    rewrite !/Sch.yield /ccallU. unseal "Sch". grind. prep.
    rewrite PModRed.interp_bind. rewrite HModSB.transl_bind. grind.

    iApply isim_reset. iStopProof. revert NODD.
    combine_quant NODS.
    combine_quant st_tgt.
    combine_quant st_src.
    combine_quant nths.
    eapply isim_coind. i.
    destruct a as [nths [st_src [st_tgt [NODS NODD]]]]. s.
    iIntros "((IST & W & TKN) & #CIH)".

    hide_itree_l marker. rewrite unfold_iter_eq.
    hide_itree_r marker2. rewrite unfold_iter_eq.
    show_itree marker2. show_itree marker.

    iDestruct "IST" as (? ? ? ?) "(% & THB & THW & COND)". des; subst; hss.
    steps_r. hss. steps_r.

    destruct (alist_find q ths_tgt) eqn:LU; [destruct o|].
    { (* done(O) | joined(X) *)
      hexploit (SIM q). intro T. rewrite LU in T. inv T.
      { (* done(O) *)
        iClear "CIH". steps_r.
        force_l true. steps_l. force_l. steps_l.
        iPoseProof (big_sepM_delete with "COND") as "[POST COND]"; et.

        iCombine "THW TKN" gives %WF. iCombine "THW TKN" as "WF".
        rewrite auth_frag_valid in WF. specialize (WF q). ss.
        rewrite discrete_fun_lookup_op Nat.eqb_refl -H3 -Some_op Some_valid in WF.
        rewrite -pair_op pair_valid frac_op in WF. des.

        apply agree_op_inv in WF0. dup WF0.
        apply (inj to_agree) in WF0.
        iAssert (interp_cond (q2 t0))%I with "[POST]" as "POST".
        { unfold interp_cond. specialize (WF0 t0). ss. inv WF0. apply (inj to_agree) in H5.
          rewrite -H5. iApply "POST". }
        
        forces_l. iSplitL "W POST"; iFrame; et.
        assert (◯ (ths_src_w ⋅ (λ n: nat, if q =? n then Some ((1/4)%Qp, to_agree (λ s: SAny.t, Some (to_agree (q2 s)))) else ε) : threadsF) ≡ ◯ ((λ n: nat, if q =? n then Some (1%Qp, to_agree (λ s: SAny.t, Some (to_agree (Q s)))) else ths_src_w n) : threadsF)).
        { f_equiv. intros y. rewrite !discrete_fun_lookup_op.
          destruct (classic (q = y)).
          - subst. rewrite Nat.eqb_refl.
            rewrite -WF1 -H3 -Some_op -pair_op frac_op agree_idemp. do 2 f_equiv.
            compute_done.
          - des_ifs; [|rewrite right_id //]. rewrite Nat.eqb_eq in Heq. subst; ss.
        }
        rewrite H0.

        step. iSplit; et. iExists _, _, _, _. iFrame. iPureIntro.
        esplits; et. i. destruct (classic (tid = q)).
        - subst. rewrite LU -H2 Nat.eqb_refl lookup_delete. econs.
        - des_ifs; [rewrite Nat.eqb_eq in Heq; subst; ss|].
          rewrite lookup_delete_ne; et.
      }
      { (* joined(X) *)
        iCombine "THW TKN" gives %WF. exfalso.
        rewrite auth_frag_valid in WF. specialize (WF q). ss.
        rewrite discrete_fun_lookup_op -H3 Nat.eqb_refl -Some_op -pair_op frac_op in WF.
        rewrite Some_valid pair_valid in WF. des. ss.
      }
    }
    { (* active(O) *)
      set (st_tgt0 := [(SchI.v_ths, ths_tgt↑)]).
      iAssert (Ist sk nths st_src st_tgt0) with "[THB THW COND]" as "IST".
      { iExists _, _, _, _. iFrame. iPureIntro. esplits; et. }
      force_l false. steps_l. forces_l. iSplitL "W"; et.
      call "IST"; et. iModIntro. steps_l. destruct q1. steps_l.
      iDestruct "ASM" as "(W & % & %)". steps_r. hss. steps_r.
      by_coind "CIH". iFrame.
    }
    { (* idle(X) *)
      iCombine "THB TKN" gives %WF. exfalso.
      hexploit (SIM q). intro STHS. rewrite LU in STHS. inv STHS.
      apply auth_both_valid_discrete in WF. des.
      apply (discrete_fun_included_spec_1 _ _ q) in WF.
      ss. rewrite Nat.eqb_refl in WF. rewrite -H0 in WF.
      eapply fragree_incl_false. et.
    }

    Unshelve. all: ss.
  Qed.

  Theorem sim:
    HSim.t SchAMod SchIMod InitCond Ist.
  Proof.
    init_sim.
    - rewrite /InitCond /initial_threads. unseal "SchA".
      iIntros "[THB THW]". iExists _, _, _, ∅.
      iFrame. rewrite big_sepM_empty. iSplitL; et.
      iPureIntro. esplits; et; ss; [split; nia |]. i. 
      rewrite// /SchAS.initial_threads_r eq_rel_dec_correct. des_ifs.
      + rewrite lookup_empty. econs 2.
      + rewrite Nat.eqb_eq in Heq0. subst; ss.
      + rewrite lookup_empty. econs.
    - ii. iIntros "IST". iDestruct "IST" as (? ? ? ?) "(% & THB & THW & COND)". des; subst.
      iExists _, _, _, _. iFrame. iPureIntro. i. esplits; [et| |et|nia].
      clear SIM. induction ths_tgt; ss. destruct a. des. splits; [nia|]. apply IHths_tgt; et.
    - eapply simF__spawn; eauto.
    - eapply simF_spawn; eauto.
    - eapply simF_yield; eauto.
    - eapply simF_join; eauto.
  Qed.

  Theorem correct :
    ctx_refines
      (SchAS.t univ StbFun StbSch, SchAS.InitCond)
      (SchI.t, const(emp%I)).
  Proof.
    eapply main_adequacy. eapply sim; et.
  Qed.

End SchIA. End SchIA.
