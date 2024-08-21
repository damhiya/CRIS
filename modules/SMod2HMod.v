Require Import Coqlib AList.
Require Import sflib.
Require Import ITreelib.
Require Import Any.
Require Import EventsRed Events HMod.
Require Import IRed.
Require Import STS.
Require Import Behavior.
Require Import PCM IPM.

From Ordinal Require Export Ordinal Arithmetic Inaccessible.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Set Implicit Arguments.

Section ORD.
  Inductive ord: Type :=
  | ord_pure (n: Ord.t)
  | ord_top
  .

  Definition is_pure (o: ord): bool := match o with | ord_pure _ => true | _ => false end.
  
  Definition ord_lt (next cur: ord): Prop :=
    match next, cur with
    | ord_pure next, ord_pure cur => (next < cur)%ord
    | _, ord_top => True
    | _, _ => False
    end.

  Definition ord_eval (tbr: bool) (o: ord): Prop :=
    match tbr with
    | true => is_pure o
    | false => o = ord_top
    end.

End ORD.

Section FSPEC.
  Context `{Σ: GRA.t}.

  Record fspec: Type := mk_fspec {
    meta: Type;
    measure: meta -> ord;
    precond: meta -> Any.t -> Any.t -> iProp; (*** meta-variable -> new logical arg -> current logical arg -> resource arg -> Prop ***)
    postcond: meta -> Any.t -> Any.t -> iProp; (*** meta-variable -> new logical ret -> current logical ret -> resource ret -> Prop ***)
  }.

  Definition mk (X AA AR: Type) (measure: X -> ord) (precond: X -> AA -> Any.t -> iProp) (postcond: X -> AR -> Any.t -> iProp) :=
    @mk_fspec
      X
      measure
      (fun x arg_src arg_tgt => (∃ (aa: AA), ⌜arg_src = aa↑⌝ ∗ precond x aa arg_tgt)%I)
      (fun x ret_src ret_tgt => (∃ (ar: AR), ⌜ret_src = ar↑⌝ ∗ postcond x ar ret_tgt)%I).


  Definition fspec_trivial: fspec :=
    mk_fspec (meta:=unit) (fun _ => ord_top) (fun _ argh argl => (⌜argh = argl⌝: iProp)%I)
             (fun _ reth retl => (⌜reth = retl⌝: iProp)%I).

  Record fspecbody: Type := mk_specbody {
    fsb_fspec:> fspec;
    fsb_body: Any.t -> itree smodE Any.t;
  }
  .

  Definition mk_simple {X: Type} (DPQ: X -> ord * (Any.t -> iProp) * (Any.t -> iProp)): fspec :=
    mk_fspec (fst ∘ fst ∘ DPQ)
             (fun x y a => (((snd ∘ fst ∘ DPQ) x a: iProp) ∗ ⌜y = a⌝)%I)
             (fun x z a => (((snd ∘ DPQ) x a: iProp) ∗ ⌜z = a⌝)%I)
  .
  
End FSPEC.

Arguments precond: simpl never.
Arguments postcond: simpl never.

Section APC.
  Context `{Σ: GRA.t}.
  
  Definition HoareCall (tbr: bool) (ord_cur: ord) (fsp: fspec): gname -> Any.t -> (itree hmodE) Any.t 
    := 
    fun fn varg_src =>
      x <- trigger (Choose fsp.(meta));; 

      (*** precondition ***)
      varg_tgt <- trigger (Choose Any.t);;
      let ord_next := fsp.(measure) x in
      trigger (Guarantee ((fsp.(precond) x varg_src varg_tgt) ∗ ⌜ord_lt ord_next ord_cur⌝%I ∗ (⌜ord_eval tbr ord_next⌝%I)));;;

      (*** call ***)
      vret_tgt <- trigger (Call fn varg_tgt);; 

      (*** postcondition ***)
      vret_src <- trigger (Take Any.t);;
      trigger (Assume (fsp.(postcond) x vret_src vret_tgt));;;

      Ret vret_src.  

  Definition HoareCallPre
        (tbr: bool)
        (ord_cur: ord)
        (fsp: fspec): gname -> Any.t -> (itree hmodE) _ :=
  fun fn varg_src =>

    x <- trigger (Choose fsp.(meta));; 

  (*** precondition ***)
    varg_tgt <- trigger (Choose Any.t);;
    let ord_next := fsp.(measure) x in
    trigger (Guarantee ((fsp.(precond) x varg_src varg_tgt) ∗ ⌜ord_lt ord_next ord_cur⌝%I ∗ (⌜ord_eval tbr ord_next⌝%I)));;;
    Ret (x, varg_tgt).

  Definition HoareCallPost
        (tbr: bool) (ord_cur: ord) (fsp: fspec) vret_tgt x : (itree hmodE) Any.t :=
    vret_src <- trigger (Take Any.t);;
    trigger (Assume (fsp.(postcond) x vret_src vret_tgt));;;
    Ret vret_src.

  Lemma HoareCall_parse
        (tbr: bool)
        (ord_cur: ord)
        (fsp: fspec)
        (fn: gname)
        (varg_src: Any.t)
    :
      HoareCall tbr ord_cur fsp fn varg_src =
      '(x, varg_tgt) <- HoareCallPre tbr ord_cur fsp fn varg_src;;
      vret_tgt <- trigger (Call fn varg_tgt);;
      HoareCallPost tbr ord_cur fsp vret_tgt x.
  Proof.
    unfold HoareCall, HoareCallPre, HoareCallPost. grind.
  Qed.

  Variable stb: gname -> option fspec.

  Program Fixpoint _APC (at_most: Ord.t) {wf Ord.lt at_most} : ord -> itree hmodE unit :=
    fun ord_cur => 
      break <- trigger (Choose _);;
      if break: bool then Ret tt
      else
        n <- trigger (Choose Ord.t);;
        trigger (Choose (n < at_most)%ord);;;
        '(fn, varg) <- trigger (Choose _);;
        fsp <- (stb fn)ǃ;;
        _ <- HoareCall true ord_cur fsp fn varg;;
        (_APC n) _ ord_cur.
  Next Obligation. i. auto. Qed.
  Next Obligation. eapply Ord.lt_well_founded. Qed.

  Definition HoareAPC (ord_cur: ord): itree hmodE unit :=
    at_most <- trigger (Choose _);;
    _APC at_most ord_cur.

  Lemma unfold_APC: forall at_most ord_cur, 
    _APC at_most ord_cur 
    = 
    break <- trigger (Choose _);;
    if break: bool then Ret tt
    else
      n <- trigger (Choose Ord.t);;
      guarantee (n < at_most)%ord;;;
      '(fn, varg) <- trigger (Choose _);;
      fsp <- (stb fn)ǃ;;
      _ <- HoareCall true ord_cur fsp fn varg;;
      (_APC n) ord_cur.
  Proof.
    i. unfold _APC. rewrite Fix_eq; eauto.
    { repeat f_equal. extensionality break. destruct break; ss.
      repeat f_equal. extensionality n.
      unfold guarantee. rewrite bind_bind.
      repeat f_equal. extensionality p.
      rewrite bind_ret_l. repeat f_equal. extensionality x. destruct x. auto. }
    { i. replace g with f; auto. extensionality o. eapply H. }
  Qed.

  Global Opaque _APC.

End APC.

Section HOARE.
  Context `{Σ: GRA.t}.
  
  Section INTERP.
    Section SPC.
      (* spc to mid *)
      Variable stb: gname -> option fspec.

      Definition handle_apcE_hmodE (ord_cur: ord): apcE ~> itree hmodE :=
        fun _ '(APC) => HoareAPC stb ord_cur.

      Definition handle_callE_hmodE ord_cur: callE ~> itree hmodE :=
        fun _ '(Call fn arg) => 
            fsp <- (stb fn)ǃ;;
            HoareCall false ord_cur fsp fn arg.

      Definition interp_smod ord_cur: itree smodE ~> itree hmodE :=
        interp (case_ (bif:=sum1) (handle_apcE_hmodE ord_cur)
               (case_ (bif:=sum1) (trivial_Handler)
               (case_ (bif:=sum1) (handle_callE_hmodE ord_cur)
                trivial_Handler))).

      Definition HoareBody (ord_cur: ord) (body: Any.t -> itree smodE Any.t) (varg_src: Any.t) := 
        match ord_cur with
        | ord_pure _ => trigger APC;;; trigger (Choose _)
        | _ => body (varg_src)
        end.
      
      Definition HoareFun
                 {X: Type}
                 (D: X -> ord)
                 (P: X -> Any.t -> Any.t -> iProp)
                 (Q: X -> Any.t -> Any.t -> iProp)
                 (body: Any.t -> itree smodE Any.t): Any.t -> itree hmodE Any.t := fun varg_tgt =>
        x <- trigger (Take X);;

        varg_src <- trigger (Take _);;
        let ord_cur := D x in
        trigger (Assume (P x varg_src varg_tgt));;; (*** precondition ***)

        vret_src <- interp_smod ord_cur (HoareBody ord_cur body varg_src);;

        vret_tgt <- trigger (Choose Any.t);;
        trigger (Guarantee (Q x vret_src vret_tgt));;; (*** postcondition ***)

        Ret vret_tgt.

      Definition interp_sb_hp (sb: fspecbody): (Any.t -> itree hmodE Any.t) :=
        let fs: fspec := sb.(fsb_fspec) in
        (HoareFun (fs.(measure)) (fs.(precond)) (fs.(postcond)) (sb.(fsb_body))).

    End SPC.
    
    (* Section LIFT.
      (* Lifting tgt module to mid level. Not sure about the usage. *)
      Definition interp_modE_hmodE: itree modE ~> itree hmodE :=
        interp trivial_Handler.
      
      Definition lift_modE_fun (f: Any.t -> itree modE Any.t): Any.t -> itree hmodE Any.t :=
        fun x => interp_modE_hmodE (f x).
  
      Definition prog_unit: callE ~> itree modE :=
        fun _ '(Call _ _) => Ret tt↑.
    End LIFT. *)

  End INTERP.

End HOARE.

(* Module IPCNotations. *)
  (* Notation ";;; t2" := *)
  (*   (ITree.bind (trigger APC) (fun _ => t2)) *)
  (*     (at level 63, t2 at next level, right associativity) : itree_scope. *)
  (* Notation "` x : t <- t1 ;;; t2" := *)
  (*   (ITree.bind t1 (fun x : t => ;;; t2)) *)
  (*     (at level 62, t at next level, t1 at next level, x ident, right associativity) : itree_scope. *)
  (* Notation "x <- t1 ;;; t2" := *)
  (*   (ITree.bind t1 (fun x => ;;; t2)) *)
  (*     (at level 62, t1 at next level, right associativity) : itree_scope. *)
  (* Notation "' p <- t1 ;;; t2" := *)
  (*   (ITree.bind t1 (fun x_ => match x_ with p => ;;; t2 end)) *)
  (*     (at level 62, t1 at next level, p pattern, right associativity) : itree_scope. *)
(* End IPCNotations. *)

(* Export IPCNotations.  *)

Module SModRed.
Section RED.

  Context `{Σ: GRA.t}.

  Lemma interp_bind
        (R S: Type)
        stb o
        (s : itree smodE R) (k : R -> itree smodE S)
    :
      interp_smod stb o (s >>= k)
      =
      st <- interp_smod stb o s;; interp_smod stb o (k st).
  Proof.
    unfold interp_smod in *. grind.
  Qed.

  Lemma interp_tau
        (U: Type)
        (t : itree _ U)
        stb o
    :
      interp_smod stb o (tau;; t)
      =
      tau;; (interp_smod stb o t).
  Proof.
    unfold interp_smod in *. grind.
  Qed.

  Lemma interp_ret
        (U: Type)
        (t: U)
        stb o
    :
      interp_smod stb o (Ret t)
      =
      Ret t.
  Proof.
    unfold interp_smod in *. grind.
  Qed.

  Lemma interp_call
        (R: Type)
        (i: callE R)
        stb o
    :
      interp_smod stb o (trigger i)
      =
      r <- handle_callE_hmodE stb o i;; tau;; Ret r.
  Proof.
    unfold interp_smod in *. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_apc
        (R: Type)
        (i: apcE R)
        stb o
    :
      interp_smod stb o (trigger i)
      =
      (handle_apcE_hmodE stb o i) >>= (fun r => tau;; Ret r).
  Proof.
    unfold interp_smod. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_pg
        (R: Type)
        (i: pgE R)
        stb o
    :
      interp_smod stb o (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof.
    unfold interp_smod. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_core
        (R: Type)
        (i: coreE R)
        stb o
    :
      interp_smod stb o (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof.
    unfold interp_smod. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_Assume
        P
        stb o
    :
      interp_smod stb o (trigger (Assume P))
      =
      x <- trigger (Assume P) ;; tau;; Ret x.
  Proof.
    unfold interp_smod. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_Guarantee
        P
        stb o
    :
      interp_smod stb o (trigger (Guarantee P))
      =
      x <- trigger (Guarantee P);; tau;; Ret x.
  Proof.
    unfold interp_smod. rewrite interp_trigger. grind. 
  Qed.

  Lemma interp_unwrapU 
        (R: Type)
        (i: option R)
        stb o
    :
      interp_smod stb o (@unwrapU smodE _ _ i)
      =
      r <- (unwrapU i);; Ret r.
  Proof.
    unfold interp_smod, unwrapU in *. des_ifs; grind.
    unfold triggerUB in *. rewrite unfold_interp. grind.
  Qed.

  Lemma interp_unwrapN
        (R: Type)
        (i: option R)
        stb o
    :
      interp_smod stb o (@unwrapN smodE _ _ i)
      =
      r <- (unwrapN i);; Ret r.
  Proof.
    unfold interp_smod, unwrapN in *. des_ifs; grind.
    unfold triggerNB in *. rewrite unfold_interp. grind.
  Qed.
  
  Lemma interp_asm
        stb o P
    : 
      interp_smod stb o (assume P)
      =
      r <- assume P;; tau;; Ret r.
  Proof.
    unfold assume. rewrite interp_bind. rewrite interp_core. grind. rewrite interp_ret. refl.
  Qed. 

  Lemma interp_guar
        stb o P
    : 
      interp_smod stb o (guarantee P)
      =
      r <- guarantee P;; tau;; Ret r.
  Proof.
    unfold guarantee. rewrite interp_bind. rewrite interp_core. grind. rewrite interp_ret. refl.
  Qed.

(*  
  Lemma interp_triggerUB
        (R: Type)
        stb o
    :
      interp_smod stb o (triggerUB)
      =
      triggerUB (A:=R).
  Proof.
    unfold interp_smod, triggerUB in *. rewrite unfold_interp. grind.
  Qed.  

  Lemma interp_triggerNB
        (R: Type)
        stb o
    :
      interp_smod stb o (triggerNB)
      =
      triggerNB (A:=R).
  Proof.
    unfold interp_smod, triggerNB in *. rewrite unfold_interp. grind.
  Qed.

  Lemma interp_ext
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
        stb o
    :
      interp_smod stb o itr0
      =
      interp_smod stb o itr1.
  Proof. subst; et. Qed.
*)
  
End RED.
End SModRed.

(*
Global Program Instance interp_rdb `{Σ: GRA.t}: red_database (mk_box (@interp_smod)) :=
  mk_rdb
    1
    (mk_box SModRed.interp_bind)
    (mk_box SModRed.interp_tau)
    (mk_box SModRed.interp_ret)
    (mk_box SModRed.interp_call)
    (mk_box SModRed.interp_triggere)
    (mk_box SModRed.interp_triggerp)
    (mk_box SModRed.interp_triggerp)
    (mk_box SModRed.interp_triggerUB)
    (mk_box SModRed.interp_triggerNB)
    (mk_box SModRed.interp_unwrapU)
    (mk_box SModRed.interp_unwrapN)
    (mk_box SModRed.interp_Assume)
    (mk_box SModRed.interp_Guarantee)
    (mk_box SModRed.interp_ext)
.
*)
