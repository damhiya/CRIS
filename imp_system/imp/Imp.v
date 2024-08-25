(** * The Imp language  *)

Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import STS Behavior.
Require Import Any.
Require Import Mod Events.
Require Import AList.
Require Import SMod2HMod.
Require Import STB.
Require Import Orders.
Require Import PCM.

Set Implicit Arguments.

(* ========================================================================== *)
(** ** SkEnv *)

Fixpoint _find_idx {A} (f: A -> bool) (l: list A) (acc: nat): option (nat * A) :=
  match l with
  | [] => None
  | hd :: tl => if (f hd) then Some (acc, hd) else _find_idx f tl (S acc)
  end
.

Definition find_idx {A} (f: A -> bool) (l: list A): option (nat * A) := _find_idx f l 0.

Lemma find_idx_red {A} (f: A -> bool) (l: list A):
  find_idx f l =
  match l with
  | [] => None
  | hd :: tl =>
    if (f hd)
    then Some (0%nat, hd)
    else
      do (n, a) <- find_idx f tl;
      Some (S n, a)
  end.
Proof.
  unfold find_idx. generalize 0. induction l; ss.
  i. des_ifs; ss.
  - rewrite Heq0. ss.
  - rewrite Heq0. specialize (IHl (S n)). rewrite Heq0 in IHl. ss.
Qed.

Module AnySort.

  Module AnyT <: Typ. Definition t := Any.t. End AnyT.

  Module SkSort := AListSort AnyT.
  
  Definition sort: Sk.t -> Sk.t := SkSort.sort.

  Definition equiv_sort_eq sk0 sk1
    (WF: Sk.wf sk0)
    (EQV: Sk.equiv sk0 sk1)
    :
    sort sk0 = sort sk1.
  Proof.
    eapply SkSort.permutation_sort; eauto.
    eapply NoDupA_eq_Nodup in WF.
    unfold SkSort._Order.eqA, StringOrder.eqA.
    clear EQV sk1. revert WF.
    induction sk0; i; ss.
    - econs.
    - inv WF. econs; eauto.
      apply Forall_forall. i.
      eapply Forall_forall in HD; eauto.
      eapply in_map. eauto.
  Qed.

  Lemma sort_equiv sk:
    Sk.equiv sk (sort sk).
  Proof.
    apply SkSort.Permuted_sort.
  Qed.
  
  Lemma sort_wf sk
    (WF: Sk.wf sk):
    Sk.wf (sort sk).
  Proof.
    eapply Sk.equiv_wf; eauto. apply sort_equiv.
  Qed.

  Lemma sort_incl sk
    :
    List.incl sk (sort sk).
  Proof.
    eapply Sk.equiv_incl. apply sort_equiv.
  Qed.

  Lemma sort_incl_rev sk
    :
    List.incl (sort sk) sk.
  Proof.
    eapply Sk.equiv_incl. symmetry. apply sort_equiv.
  Qed.

End AnySort.


Module SkEnv.

  Notation mblock := nat (only parsing).
  Notation ptrofs := Z (only parsing).

  Record t: Type := mk {
    blk2id: mblock -> option gname;
    id2blk: gname -> option mblock;
  }
  .
  
  Definition wf (ske: t): Prop :=
    forall id blk, ske.(id2blk) id = Some blk <-> ske.(blk2id) blk = Some id.

  Definition load_skenv (sk0: Sk.t): t :=
    let sk := AnySort.sort sk0 in
    let n := List.length sk in
    {|
      SkEnv.blk2id := fun blk => do '(gn, _) <- (List.nth_error sk blk); Some gn;
      SkEnv.id2blk := fun id => do '(blk, _) <- find_idx (fun '(id', _) => string_dec id id') sk; Some blk
    |}
  .

  Lemma load_skenv_wf
        sk
        (WF: Sk.wf sk)
    :
      <<WF: wf (load_skenv sk)>>
  .
  Proof.
    unfold load_skenv.
    apply AnySort.sort_wf in WF. revert WF.
    generalize (AnySort.sort sk). clear sk. intros sk WF.

    r in WF.
    rr. split; i; ss.
    - uo; des_ifs.
      + f_equal. ginduction sk; ss. i. inv WF.
        rewrite find_idx_red in Heq1. des_ifs; ss.
        { des_sumbool. subst. ss. clarify. }
        des_sumbool. uo. des_ifs. destruct p. ss.
        hexploit IHsk; et.
      + exfalso. ginduction sk; ss. i. inv WF.
        rewrite find_idx_red in Heq2. des_ifs; ss.
        des_sumbool. uo. des_ifs. destruct p. ss.
        hexploit IHsk; et.
    - ginduction sk; ss.
      { i. uo. ss. destruct blk; ss. }
      i. destruct a. inv WF. uo. destruct blk; ss; clarify.
      {  rewrite find_idx_red. uo. des_ifs; des_sumbool; ss. }
      hexploit IHsk; et. i.
      rewrite find_idx_red. uo. des_ifs; des_sumbool; ss. exfalso.
      subst. clear - Heq1 H2. ginduction sk; ss. i.
      rewrite find_idx_red in Heq1. des_ifs; des_sumbool; ss; et.
      uo. des_ifs. destruct p. eapply IHsk; et.
  Qed.

  Definition incl_env (sk0: Sk.t) (skenv: t): Prop :=
    forall gn gd (IN: List.In (gn, gd) sk0),
    exists blk, <<FIND: skenv.(SkEnv.id2blk) gn = Some blk>>.

  Lemma incl_incl_env sk0 sk1
        (INCL: List.incl sk0 sk1)
    :
      incl_env sk0 (load_skenv sk1).
  Proof.
    assert (incl sk0 (AnySort.sort sk1)).
    { etrans. apply INCL. apply AnySort.sort_incl. }
    unfold load_skenv. clear INCL. revert H.
    generalize (AnySort.sort sk1). clear sk1. intros sk1 INCL.

    ii. exploit INCL; et. i. ss. uo. des_ifs; et.
    exfalso. clear - x0 Heq0. ginduction sk1; et.
    i. ss. rewrite find_idx_red in Heq0. des_ifs.
    des_sumbool. uo.  des_ifs. des; clarify.
    eapply IHsk1; et.
  Qed.

  Lemma in_env_in_sk :
    forall sk blk symb
      (FIND: blk2id (load_skenv sk) blk = Some symb),
    exists def, In (symb, def) sk.
  Proof.
    i. cut (exists def, In (symb, def) (AnySort.sort sk)).
    { i; des. eexists. apply AnySort.sort_incl_rev. eauto. }

    ss. uo. des_ifs. eapply nth_error_In in Heq0. et.
  Qed.

  Lemma in_sk_in_env :
    forall sk def symb
           (IN: In (symb, def) sk),
    exists blk, blk2id (load_skenv sk) blk = Some symb.
  Proof.
    i. apply AnySort.sort_incl in IN.
    ss. uo. eapply In_nth_error in IN. des.
    eexists. rewrite IN. et.
  Qed.

  Lemma env_range_some :
    forall sk blk
      (BLKRANGE : blk < Datatypes.length sk),
      <<FOUND : exists symb, blk2id (load_skenv sk) blk = Some symb>>.
  Proof.
    i. erewrite Permutation.Permutation_length in BLKRANGE; cycle 1.
    { apply AnySort.SkSort.sort_permutation. }
    unfold load_skenv, AnySort.sort. revert BLKRANGE.
    generalize (AnySort.SkSort.sort sk). clear sk. intros sk ?.

    depgen sk. induction blk; i; ss; clarify.
    { destruct sk; ss; clarify.
      { lia. }
      uo. destruct t0. exists t0. ss. }
    destruct sk; ss; clarify.
    { lia. }
    apply lt_S_n in BLKRANGE. eapply IHblk; eauto.
  Qed.

  Lemma env_found_range :
    forall sk symb blk
      (FOUND : id2blk (load_skenv sk) symb = Some blk),
      <<BLKRANGE : blk < Datatypes.length sk>>.
  Proof.
    i. erewrite Permutation.Permutation_length; cycle 1.
    { apply AnySort.SkSort.sort_permutation. }
    revert FOUND. unfold load_skenv, AnySort.sort.
    generalize (AnySort.SkSort.sort sk). clear sk. intros sk ?.
    
    ginduction sk; i; ss; clarify.
    uo; des_ifs. destruct p0. rewrite find_idx_red in Heq0. des_ifs.
    { apply Nat.lt_0_succ. }
    destruct blk.
    { apply Nat.lt_0_succ. }
    uo. des_ifs. destruct p. ss. clarify. apply lt_n_S. eapply IHsk; eauto.
    instantiate (1:=symb). rewrite Heq0. ss.
  Qed.
  
End SkEnv.

Coercion SkEnv.load_skenv: Sk.t >-> SkEnv.t.
Global Opaque SkEnv.load_skenv.

Section FB_HAS_SPEC.

  Context `{Σ: GRA.t}.

  Variable skenv: SkEnv.t.

  Variant fb_has_spec (stb: gname -> option fspec) (fb: mblock) (fsp: fspec): Prop :=
  | fb_has_spec_intro
      fn
      (FBLOCK: skenv.(SkEnv.blk2id) fb = Some fn)
      (SPEC: fn_has_spec stb fn fsp)
  .

  Lemma fb_has_spec_weaker (stb: gname -> option fspec) (fb: mblock) (fsp0 fsp1: fspec)
        (SPEC: fb_has_spec stb fb fsp1)
        (WEAK: fspec_weaker fsp0 fsp1)
    :
      fb_has_spec stb fb fsp0.
  Proof.
    inv SPEC. econs; eauto.
    eapply fn_has_spec_weaker; eauto.
  Qed.
  
End FB_HAS_SPEC.

(* ========================================================================== *)
(** ** Syntax *)

(** Imp manipulates a countable set of variables represented as [string]s: *)
Definition var : Set := string.

(** Expressions are made of variables, constant literals, and arithmetic operations. *)
Inductive expr : Type :=
| Var (_ : var)
| Lit (_ : Z)
| Eq (_ _ : expr)
| Lt (_ _ : expr)
| Plus  (_ _ : expr)
| Minus (_ _ : expr)
| Mult  (_ _ : expr)
.

(** function call exists only as a statement *)
Inductive stmt : Type :=
| Skip                           (* ; *)
| Assign (x : var) (e : expr)    (* x = e *)
| Seq    (a b : stmt)            (* a ; b *)
| If     (i : expr) (t e : stmt) (* if (i) then { t } else { e } *)
| CallFun (x : var) (f : gname) (args : list expr) (* x = f(args), call by name *)
| CallPtr (x : var) (p : expr) (args : list expr)  (* x = f(args), by pointer*)
| CallSys (x : var) (f : gname) (args : list expr) (* x = f(args), system call *)
| AddrOf (x : var) (X : gname)         (* x = &X *)
| Malloc (x : var) (s : expr)          (* x = malloc(s) *)
| Free (p : expr)                      (* free(p) *)
| Load (x : var) (p : expr)            (* x = *p *)
| Store (p : expr) (v : expr)          (* *p = v *)
| Cmp (x : var) (a : expr) (b : expr)  (* memory accessing equality comparison *)
.

(** information of a function *)
Record function : Type := mk_function {
  fn_params : list var;
  fn_vars : list var;     (* disjoint with fn_params *)
  fn_body : stmt
}.

(* prohibited names for Callfun/Ptr *)
Definition call_ban f :=
  rel_dec f "alloc" || rel_dec f "free" || rel_dec f "load" || rel_dec f "store" || rel_dec f "cmp" || rel_dec f "main".


(** ** Supported System Calls by Imp *)
Definition syscalls : list (string * nat) :=
  [("print", 1); ("scan", 0)].

Global Opaque syscalls.


(** ** Program *)

(** program components *)
(* declared external global variables *)
Definition extVars := list gname.
(* declared external functions with arg nums*)
Definition extFuns := list (gname * nat).
(* defined global variables *)
Definition progVars := list (gname * Z).
(* defined internal functions *)
Definition progFuns := list (gname * function).

(** Imp program *)

(* Record programL : Type := mk_programL {
  nameL : list mname;
  ext_varsL : extVars;
  ext_funsL : extFuns;
  prog_varsL : progVars;
  prog_funsL : list (mname * (gname * function));
  publicL : list gname;
  defsL : list (gname * Sk.gdef);
}. *)

Record program : Type := mk_program {
  (* name : mname; *)
  ext_vars : extVars;
  ext_funs : extFuns;
  prog_vars : progVars;
  prog_funs : progFuns;
  public : list gname :=
    let sys := List.map fst syscalls in
    let evs := ext_vars in
    let efs := List.map fst ext_funs in
    let ivs := List.map fst prog_vars in
    let ifs := List.map fst prog_funs in
    sys ++ evs ++ efs ++ ivs ++ ifs;
  defs : list (gname * gdef) :=
    let fs := (List.map (fun '(fn, _) => (fn, Gfun)) prog_funs) in
    let vs := (List.map (fun '(vn, vv) => (vn, Gvar vv)) prog_vars) in
    (List.filter (negb ∘ call_ban ∘ fst) (fs ++ vs));
}.

(* Definition lift (p : program) : programL :=
  mk_programL
    [p.(name)]
    p.(ext_vars) p.(ext_funs)
    p.(prog_vars) (List.map (fun pf => (p.(name), pf)) p.(prog_funs))
    p.(public) p.(defs).

Coercion lift : program >-> programL. *)





(* ========================================================================== *)
(** ** Semantics *)

(** Get/Set function local variables *)
Variant ImpState : Type -> Type :=
| GetVar (x : var) : ImpState val
| SetVar (x : var) (v : val) : ImpState unit.

(** Get pointer to a global variable/function *)
Variant GlobEnv : Type -> Type :=
| GetPtr (x: gname) : GlobEnv val
| GetName (p: val) : GlobEnv gname.

Section Denote.

  Context {eff : Type -> Type}.
  Context {HasGlobVar: GlobEnv -< eff}.
  Context {HasImpState : ImpState -< eff}.
  Context {HasCall : callE -< eff}.
  Context {HasEvent : coreE -< eff}.

  (** Denotation of expressions *)
  Fixpoint denote_expr (e : expr) : itree eff val :=
    match e with
    | Var v     => u <- trigger (GetVar v) ;; Ret u
    | Lit n     => tau;; Ret (Vint n)

    | Eq a b =>
      l <- denote_expr a ;; r <- denote_expr b ;;
      (if (wf_val l && wf_val r) then Ret tt else triggerUB);;;
      match l, r with
      | Vint lv, Vint rv => if (lv =? rv)%Z then Ret (Vint 1) else Ret (Vint 0)
      | _, _ => triggerUB
      end

    | Lt a b =>
      l <- denote_expr a ;; r <- denote_expr b ;;
      (if (wf_val l && wf_val r) then Ret tt else triggerUB);;;
      match l, r with
      | Vint lv, Vint rv => if (Z_lt_dec lv rv) then Ret (Vint 1) else Ret (Vint 0)
      | _, _ => triggerUB
      end

    | Plus a b  =>
      l <- denote_expr a ;; r <- denote_expr b ;; u <- (vadd l r)? ;; Ret u

    | Minus a b =>
      l <- denote_expr a ;; r <- denote_expr b ;; u <- (vsub l r)? ;; Ret u

    | Mult a b  =>
      l <- denote_expr a ;; r <- denote_expr b ;; u <- (vmul l r)? ;; Ret u

    end.

  (** Denotation of statements *)
  Definition is_true (v : val) : option bool :=
    match v with
    | Vint n => if (n =? 0)%Z then Some false else Some true
    | _ => None
    end.

  Fixpoint denote_exprs_acc (es : list expr) (acc : list val) : itree eff (list val) :=
    match es with
    | [] => Ret acc
    | e :: s =>
      v <- denote_expr e;; denote_exprs_acc s (acc ++ [v])
    end.

  Fixpoint denote_exprs (es : list expr) : itree eff (list val) :=
    match es with
    | [] => Ret []
    | e :: s =>
      v <- denote_expr e;;
      vs <- denote_exprs s;;
      Ret (v :: vs)
    end.

  Fixpoint denote_stmt (s : stmt) : itree eff val :=
    match s with
    | Skip => tau;; Ret Vundef
    | Assign x e =>
      v <- denote_expr e;; trigger (SetVar x v);;; tau;; Ret Vundef
    | Seq a b =>
      tau;; denote_stmt a;;; denote_stmt b
    | If i t e =>
      v <- denote_expr i;;
      (if (wf_val v) then Ret tt else triggerUB);;;
      `b: bool <- (is_true v)?;; tau;;
      if b then (denote_stmt t) else (denote_stmt e)

    | CallFun x f args =>
      (if (call_ban f) then triggerUB else Ret tt);;;
      eval_args <- denote_exprs args;;
      v <- ccallU f eval_args;;
      trigger (SetVar x v);;; tau;; Ret Vundef

    | CallPtr x e args =>
      (if (match e with | Var _ => true | _ => false end) then Ret tt else triggerUB);;;
      p <- denote_expr e;; f <- trigger (GetName p);;
      eval_args <- denote_exprs args;;
      v <- ccallU f eval_args;;
      trigger (SetVar x v);;; tau;; Ret Vundef

    | CallSys x f args =>
      sig <- (alist_find f syscalls)? ;;
      (if (sig =? List.length args)%nat then Ret tt else triggerUB);;;
      eval_args <- denote_exprs args;;
      (if (forallb (fun v => match v with | Vint _ => true | _ => false end) eval_args) then Ret tt else triggerUB);;;
      let eval_zs := List.map (fun v => match v with | Vint z => z | _ => 0%Z end) eval_args in
      (if (forallb intrange_64 eval_zs) then Ret tt else triggerUB);;;
      v <- trigger (IO f eval_zs);;
      trigger (SetVar x (Vint v));;; tau;; Ret Vundef

    | AddrOf x X =>
      v <- trigger (GetPtr X);; trigger (SetVar x v);;; tau;; Ret Vundef
    | Malloc x se =>
      s <- denote_expr se;;
      v <- ccallU "alloc" [s];;
      trigger (SetVar x v);;; tau;; Ret Vundef
    | Free pe =>
      p <- denote_expr pe;;
      `_: val <- ccallU "free" [p];; tau;; Ret Vundef
    | Load x pe =>
      p <- denote_expr pe;;
      (if (wf_val p) then Ret tt else triggerUB);;;
      v <- ccallU "load" [p];;
      trigger (SetVar x v);;; tau;; Ret Vundef
    | Store pe ve =>
      p <- denote_expr pe;;
      (if (wf_val p) then Ret tt else triggerUB);;;
      v <- denote_expr ve;;
      `_:val <- ccallU "store" [p; v];; tau;; Ret Vundef
    | Cmp x ae be =>
      a <- denote_expr ae;; b <- denote_expr be;;
      (if (wf_val a && wf_val b) then Ret tt else triggerUB);;;
      v <- ccallU "cmp" [a; b];;
      trigger (SetVar x v);;; tau;; Ret Vundef

    end.

End Denote.





(* ========================================================================== *)
(** ** Interpretation *)

Section Interp.

  Definition effs := GlobEnv +' ImpState +' modE.

  Definition handle_GlobEnv {eff} `{coreE -< eff} (ge: SkEnv.t) : GlobEnv ~> (itree eff) :=
    fun _ e =>
      match e with
      | GetPtr X =>
        r <- (ge.(SkEnv.id2blk) X)?;; Ret (Vptr r 0)
      | GetName p =>
        match p with
        | Vptr n 0 => x <- (ge.(SkEnv.blk2id) n)?;; Ret (x)
        | _ => triggerUB
        end
      end.

  Definition interp_GlobEnv {eff} `{coreE -< eff} (ge: SkEnv.t) : itree (GlobEnv +' eff) ~> (itree eff) :=
    interp (case_ (handle_GlobEnv ge) ((fun T e => trigger e) : eff ~> itree eff)).

  (** function local environment *)
  Definition lenv := alist var val.
  Definition handle_ImpState {eff} `{coreE -< eff} : ImpState ~> stateT lenv (itree eff) :=
    fun _ e le =>
      match e with
      | GetVar x => r <- unwrapU (alist_find x le);; Ret (le, r)
      | SetVar x v => Ret (alist_add x v le, tt)
      end.

  Definition interp_ImpState {eff} `{coreE -< eff}: itree (ImpState +' eff) ~> stateT lenv (itree eff) :=
    State.interp_state (case_ handle_ImpState pure_state).

  (* Definition interp_imp ge le (itr : itree effs val) := *)
  (*   interp_ImpState (interp_GlobEnv ge itr) le. *)

  Definition interp_imp ge : itree effs ~> stateT lenv (itree modE) :=
    fun _ itr le => interp_ImpState (interp_GlobEnv ge itr) le.

  Fixpoint init_lenv xs : lenv :=
    match xs with
    | [] => []
    | x :: t => (x, Vundef) :: (init_lenv t)
    end
  .

  Fixpoint init_args params args (acc: lenv) : option lenv :=
    match params, args with
    | [], [] => Some acc
    | x :: part, v :: argt =>
      init_args part argt (alist_add x v acc)
    | _, _ => None
    end
  .

  Lemma init_args_prop :
    forall params args acc le
      (INITSOME: init_args params args acc = Some le),
      <<INITLEN: List.length params = List.length args>>.
  Proof.
    induction params; i; ss; clarify.
    { destruct args; ss; clarify. }
    destruct args; ss; clarify. apply IHparams in INITSOME. red. rewrite INITSOME. ss.
  Qed.

  (* 'return' is a fixed register, holding the return value of this function. *)
  (* '_' is a black hole register, holding garbage *)
  Definition eval_imp (ge: SkEnv.t) (f: function) (args: list val) : itree modE val :=
    let vars := f.(fn_vars) ++ ["return"; "_"] in
    let params := f.(fn_params) in
    (if (ListDec.NoDup_dec string_dec (params ++ vars)) then Ret tt else triggerUB);;;
    match (init_args params args (init_lenv vars)) with
    | Some iargs =>
      '(_, retv) <- (interp_imp ge (tau;; (denote_stmt f.(fn_body));;; retv <- (denote_expr (Var "return")) ;; Ret retv)
                               iargs);; Ret retv
    | None => triggerUB
    end
  .

End Interp.


(* ========================================================================== *)
(**** ModSem ****)

Module ImpMod.
Section MODSEM.

  Set Typeclasses Depth 5.
  (* Instance Initial_void1 : @Initial (Type -> Type) IFun void1 := @elim_void1. (*** TODO: move to ITreelib ***) *)

  Definition modsem (m : program) (ge: SkEnv.t) : ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, f) => (fn, cfunU (eval_imp ge f))) m.(prog_funs);
    ModSem.initial_st := tt↑;
  |}.

  Definition get_mod (m : program) : Mod.t := {|
    Mod.modsem := fun ge => (modsem m (SkEnv.load_skenv ge));
    Mod.sk := List.map (update_snd Any.upcast) m.(defs);
  |}.

  Definition init : ModSem.t :=
    ModSem.init (
      rv <- ccallU "main" ([]: list val);;
      match rv with
      | Vint z =>
          if (0 <=? z)%Z && (z <? two_power_nat 32)%Z
          then Ret z↑
          else triggerUB
      | _ => triggerUB
      end
    ).

  (* Definition modsemL (mL : programL) (ge: SkEnv.t) : ModSemL.t := {|
    ModSemL.fnsems :=
      List.map (fun '(mn, (fn, f)) => (fn, fun a => transl_all mn (cfunU (eval_imp ge f) a))) mL.(prog_funsL);
    ModSemL.initial_mrs :=
      List.map (fun name => (name, tt↑)) mL.(nameL);
  |}.

  Definition get_modL (mL : programL) : ModL.t := {|
    ModL.get_modsem := fun ge => (modsemL mL (Sk.load_skenv ge));
    ModL.sk := mL.(defsL);
  |}.

  Lemma comm_imp_mod_lift :
      (compose get_modL lift) = (compose Mod.lift get_mod).
  Proof.
    unfold compose. extensionality p. unfold lift. unfold Mod.lift. unfold get_modL, get_mod.
    f_equal. unfold modsemL, modsem. ss. unfold ModSem.lift.
    ss. extensionality sk. f_equal.
    revert sk. induction (prog_funs p); i; ss; clarify.
    destruct a. unfold map_snd. f_equal.
    apply IHp0.
  Qed. *)

End MODSEM.
End ImpMod.
