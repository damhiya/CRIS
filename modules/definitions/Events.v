Require Import Coqlib AList.
Require Export sflib.
Require Export ITreelib.
Require Import Any.
Require Export BasicEventsRed BasicEvents.

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
             
End FSPEC.

Section PROOF.
  (* Context {myRA} `{@GRA.inG myRA Σ}. *)
  Context {Σ: GRA.t}.
  Let GURA: URA.t := GRA.to_URA Σ.
  Local Existing Instance GURA.


  Definition mput E `{sE -< E} `{eventE -< E} (mr: Σ): itree E unit :=
    st <- trigger sGet;; '(mp, _) <- ((Any.split st)?);;
    trigger (sPut (Any.pair mp mr↑))
  .

  Definition mget E `{sE -< E} `{eventE -< E}: itree E Σ :=
    st <- trigger sGet;; '(_, mr) <- ((Any.split st)?);;
    mr↓?
  .

  Definition pupdate E `{sE -< E} `{eventE -< E} {X} (run: Any.t -> Any.t * X) : itree E X :=
    trigger (SUpdate (fun st => 
      match (Any.split st) with
      | Some (x, mr) => ((Any.pair (fst (run x)) mr), snd (run x))
      | None => run tt↑
      end
    ))
  .

End PROOF.

Section HOARE.
  Context `{Σ: GRA.t}.

  Variant hAPCE: Type -> Type :=
  | hAPC: hAPCE unit.

  Variant hAGE: Type -> Type :=
  | Assume (P: iProp): hAGE unit
  | Guarantee (P: iProp): hAGE unit.

  Definition hEs := (hAGE +' hAPCE +' Es).
  Definition hAGEs := (hAGE +' Es).

  Section APC.
  
    Definition HoareCall (tbr: bool) (ord_cur: ord) (fsp: fspec): gname -> Any.t -> (itree hAGEs) Any.t 
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
          (fsp: fspec): gname -> Any.t -> (itree hAGEs) _ :=
    fun fn varg_src =>
  
      x <- trigger (Choose fsp.(meta));; 
  
    (*** precondition ***)
      varg_tgt <- trigger (Choose Any.t);;
      let ord_next := fsp.(measure) x in
      trigger (Guarantee ((fsp.(precond) x varg_src varg_tgt) ∗ ⌜ord_lt ord_next ord_cur⌝%I ∗ (⌜ord_eval tbr ord_next⌝%I)));;;
      Ret (x, varg_tgt).

    Definition HoareCallPost
          (tbr: bool) (ord_cur: ord) (fsp: fspec) vret_tgt x : (itree hAGEs) Any.t :=
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

    Program Fixpoint _APC (at_most: Ord.t) {wf Ord.lt at_most} : ord -> itree hAGEs unit :=
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

    Definition HoareAPC (ord_cur: ord): itree hAGEs unit :=
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

  Record fspecbody: Type := mk_specbody {
    fsb_fspec:> fspec;
    fsb_body: Any.t -> itree hEs Any.t;
  }
  .

  Definition mk_simple {X: Type} (DPQ: X -> ord * (Any.t -> iProp) * (Any.t -> iProp)): fspec :=
    mk_fspec (fst ∘ fst ∘ DPQ)
             (fun x y a => (((snd ∘ fst ∘ DPQ) x a: iProp) ∗ ⌜y = a⌝)%I)
             (fun x z a => (((snd ∘ DPQ) x a: iProp) ∗ ⌜z = a⌝)%I)
  .

  Section INTERP.
    Section SPC.
      (* spc to mid *)
      Variable stb: gname -> option fspec.

      Definition handle_hAPCE_hAGEs (ord_cur: ord): hAPCE ~> itree hAGEs :=
        fun _ '(hAPC) => HoareAPC stb ord_cur.

      Definition handle_callE_hAGEs ord_cur: callE ~> itree hAGEs :=
        fun _ '(Call fn arg) => 
            fsp <- (stb fn)ǃ;;
            HoareCall false ord_cur fsp fn arg.

      Definition interp_hEs_hAGEs ord_cur: itree hEs ~> itree hAGEs :=
        interp (case_ (bif:=sum1) (trivial_Handler) (case_ (bif:=sum1) (handle_hAPCE_hAGEs ord_cur)
                          (case_ (bif:=sum1) (handle_callE_hAGEs ord_cur)
                                  trivial_Handler))).    
      Definition HoareFun
                 {X: Type}
                 (D: X -> ord)
                 (P: X -> Any.t -> Any.t -> iProp)
                 (Q: X -> Any.t -> Any.t -> iProp)
                 (body: Any.t -> itree hEs Any.t): Any.t -> itree hAGEs Any.t := fun varg_tgt =>
        x <- trigger (Take X);;

        varg_src <- trigger (Take _);;
        let ord_cur := D x in
        trigger (Assume (P x varg_src varg_tgt));;; (*** precondition ***)

        vret_src <- interp_hEs_hAGEs
                            ord_cur
                               (match ord_cur with
                                | ord_pure _ => _ <- trigger hAPC;; trigger (Choose _)
                                | _ => body (varg_src)
                                end);;

        vret_tgt <- trigger (Choose Any.t);;
        trigger (Guarantee (Q x vret_src vret_tgt));;; (*** postcondition ***)

        Ret vret_tgt.

      Definition interp_sb_hp (sb: fspecbody): (Any.t -> itree hAGEs Any.t) :=
        let fs: fspec := sb.(fsb_fspec) in
        (HoareFun (fs.(measure)) (fs.(precond)) (fs.(postcond)) (sb.(fsb_body))).

      Definition body_spec_hp o (body: itree hEs Any.t): itree hAGEs Any.t :=
        interp_hEs_hAGEs o body.

      Definition fun_spec_hp o (f: Any.t -> itree hEs Any.t): Any.t -> itree hAGEs Any.t :=
        fun x => body_spec_hp o (f x).

    End SPC.

    Section MID.
      (* mid to tgt code *)
      Definition handle_sE_tgt: sE ~> itree Es :=
          (fun _ e =>
             match e with
             | SUpdate run => pupdate run
            end).
  
      Definition handle_Assume P: stateT (Σ) (itree Es) unit :=
        fun fr =>
          r <- trigger (Take Σ);;
          mr <- mget;; 
          assume (URA.wf (r ⋅ fr ⋅ mr));;;
          assume(Own r ⊢ P);;; 
          Ret (r ⋅ fr, tt).
  
      Definition handle_Guarantee P: stateT (Σ) (itree Es) unit :=
        fun fr =>
          '(r, fr', mr') <- trigger (Choose (Σ * Σ * Σ));;
          mr <- mget;;
          guarantee(Own (fr ⋅ mr) ⊢ #=> Own (r ⋅ fr' ⋅ mr'));;;
          guarantee(Own r ⊢ P);;;
          mput mr';;;
          Ret (fr', tt).

      Definition handle_hAGE_tgt: hAGE ~> stateT (Σ) (itree Es) :=
        fun _ e fr =>
          match e with
          | Assume P => handle_Assume P fr
          | Guarantee P => handle_Guarantee P fr
          end.    

      Definition interp_hp : itree hAGEs ~> stateT Σ (itree Es) :=
          interp_state 
            (case_ (bif:=sum1) (handle_hAGE_tgt)
            (case_ (bif:=sum1) ((fun T X fr => '(fr', _) <- (handle_Guarantee (True%I) fr);; x <- trigger X;; Ret (fr', x)): _ ~> stateT Σ (itree Es)) 
            (case_ (bif:=sum1) ((fun T X fr => x <- handle_sE_tgt X;; Ret (fr, x)): _ ~> stateT Σ (itree Es)) 
                               ((fun T X fr => x <- trigger X;; Ret (fr, x)): _ ~> stateT Σ (itree Es))))).

      Definition hp_fun_tail := (fun '(fr, x) => handle_Guarantee (True%I) fr ;;; Ret (x: Any.t)).
    
      Definition interp_hp_body (i: itree hAGEs Any.t) (fr: Σ) : itree Es Any.t :=
        interp_hp i fr >>= hp_fun_tail.

      Definition interp_hp_fun (f: Any.t -> itree hAGEs Any.t) : Any.t -> itree Es Any.t :=
        fun x => interp_hp_body (f x) ε.

    End MID.

    Section INIT.
      (* separate compilation path for module-state initialization. *)
      Definition assume_init {E} `{takeE -< E} (P: Prop): itree E unit := 
        trigger (BasicEvents.take P) ;;; Ret tt.

      Definition handle_init_cond P: stateT (Σ) (itree takeE) unit :=
      fun fr => (* skipped 'mget' from 'handle_Assume' *)
        r <- trigger (BasicEvents.take Σ);;
        assume_init (URA.wf (r ⋅ fr ));;;
        assume_init (Own r ⊢ P);;; 
        Ret (r ⋅ fr, tt).

      Definition cond_to_st (P: iProp): itree takeE Σ :=
        '(r, _) <- handle_init_cond P ε;; Ret r.        

    End INIT.

    (* Section LIFT.
      (* Lifting tgt module to mid level. Not sure about the usage. *)
      Definition interp_Es_hAGEs: itree Es ~> itree hAGEs :=
        interp trivial_Handler.
      
      Definition lift_Es_fun (f: Any.t -> itree Es Any.t): Any.t -> itree hAGEs Any.t :=
        fun x => interp_Es_hAGEs (f x).
  
      Definition prog_unit: callE ~> itree Es :=
        fun _ '(Call _ _) => Ret tt↑.
    End LIFT. *)

  End INTERP.

End HOARE.

Module IPCNotations.
  Notation ";;; t2" :=
    (ITree.bind (trigger hAPC) (fun _ => t2))
      (at level 63, t2 at next level, right associativity) : itree_scope.
  Notation "` x : t <- t1 ;;; t2" :=
    (ITree.bind t1 (fun x : t => ;;; t2))
      (at level 62, t at next level, t1 at next level, x ident, right associativity) : itree_scope.
  Notation "x <- t1 ;;; t2" :=
    (ITree.bind t1 (fun x => ;;; t2))
      (at level 62, t1 at next level, right associativity) : itree_scope.
  Notation "' p <- t1 ;;; t2" :=
    (ITree.bind t1 (fun x_ => match x_ with p => ;;; t2 end))
      (at level 62, t1 at next level, p pattern, right associativity) : itree_scope.
End IPCNotations.

Export IPCNotations. 



Section RED.
  (* itree reduction lemmas *)
  Context `{Σ: GRA.t}.
  Section HP.
    Lemma interp_hp_bind
          (R S: Type)
          (s : itree hAGEs R) (k : R -> itree hAGEs S)
          fmr
      :
        interp_hp (s >>= k) fmr
        =
        st <- interp_hp s fmr;; interp_hp (k st.2) st.1.
    Proof.
      unfold interp_hp in *. eapply interp_state_bind.
    Qed.

    Lemma interp_hp_body_bind
          R (s : itree hAGEs R) (k : R -> itree hAGEs Any.t) fmr
      :
        interp_hp_body (s >>= k) fmr
        =
        '(fr,r) <- interp_hp s fmr;; interp_hp_body (k r) fr.
    Proof.
      unfold interp_hp_body. rewrite interp_hp_bind. grind. destruct x. eauto.
    Qed.


    Lemma interp_hp_tau
          (U: Type)
          (t : itree _ U)
          fmr
      :
        interp_hp (tau;; t) fmr
        =
        tau;; (interp_hp t fmr).
    Proof.
      unfold interp_hp in *. eapply interp_state_tau.
    Qed.

    Lemma interp_hp_ret
          (U: Type)
          (t: U)
          fmr
      :
        interp_hp (Ret t) fmr
        =
        Ret (fmr, t).
    Proof.
      unfold interp_hp in *. eapply interp_state_ret.
    Qed.

    Lemma interp_hp_call
          (R: Type)
          (i: callE R)
          fr
      :
        interp_hp (trigger i) fr
        =
        '(fr', _) <- handle_Guarantee (True%I:iProp) fr;; r <- trigger i;; tau;; Ret (fr', r).
    Proof.
      unfold interp_hp in *. grind.
    Qed.

    Lemma interp_hp_triggers
          (R: Type)
          (i: sE R)
          fmr
      :
        interp_hp (trigger i) fmr
        =
        r <- handle_sE_tgt i;; tau;; Ret (fmr, r).
    Proof.
      unfold interp_hp. rewrite interp_state_trigger. cbn. grind.
    Qed.

    Lemma interp_hp_triggere
          (R: Type)
          (i: eventE R)
          fmr
      :
        interp_hp (trigger i) fmr
        =
        r <- trigger i;; tau;; Ret (fmr, r).
    Proof.
      unfold interp_hp. rewrite interp_state_trigger. cbn. grind.
    Qed.

    Lemma interp_hp_triggerUB
          (R: Type)
          fmr
      :
        interp_hp (triggerUB) fmr
        =
        triggerUB (A:=Σ*R).
    Proof.
      unfold interp_hp, triggerUB in *. rewrite unfold_interp_state. cbn. grind.
    Qed.

    Lemma interp_hp_triggerNB
          (R: Type)
          fmr
      :
        interp_hp (triggerNB) fmr
        =
        triggerNB (A:=Σ*R).
    Proof.
      unfold interp_hp, triggerNB in *. rewrite unfold_interp_state. cbn. grind.
    Qed.

    Lemma interp_hp_unwrapU 
          (R: Type)
          (i: option R)
          fmr
      :
        interp_hp (@unwrapU hAGEs _ _ i) fmr
        =
        r <- (unwrapU i);; Ret (fmr, r).
    Proof.
      unfold interp_hp, unwrapU in *. des_ifs.
      { etrans.
        { eapply interp_hp_ret. }
        { grind. }
      }
      { etrans.
        { eapply interp_hp_triggerUB. }
        { unfold triggerUB. grind. }
      }
    Qed.

    Lemma interp_hp_unwrapN
          (R: Type)
          (i: option R)
          fmr
      :
        interp_hp (@unwrapN hAGEs _ _ i) fmr
        =
        r <- (unwrapN i);; Ret (fmr, r).
    Proof.
      unfold interp_hp, unwrapN in *. des_ifs.
      { etrans.
        { eapply interp_hp_ret. }
        { grind. }
      }
      { etrans.
        { eapply interp_hp_triggerNB. }
        { unfold triggerNB. grind. }
      }
    Qed.

    Lemma interp_hp_Assume
          P
          fmr
      :
        interp_hp (trigger (Assume P)) fmr
        =
        x <- handle_Assume P fmr ;; tau;; Ret x.
    Proof.
      unfold interp_hp. rewrite interp_state_trigger. cbn. grind.
    Qed.

    Lemma interp_hp_Guarantee
          P
          fmr
      :
        interp_hp (trigger (Guarantee P)) fmr
        =
        x <- handle_Guarantee P fmr ;; tau;; Ret x.
    Proof.
      unfold interp_hp. rewrite interp_state_trigger. cbn. grind.
    Qed.

    Lemma interp_hp_ext
          R (itr0 itr1: itree _ R)
          (EQ: itr0 = itr1)
          fmr
      :
        interp_hp itr0 fmr
        =
        interp_hp itr1 fmr.
    Proof. subst; et. Qed.

    Global Program Instance interp_hp_rdb: red_database (mk_box (@interp_hp)) :=
      mk_rdb
        1
        (mk_box interp_hp_bind)
        (mk_box interp_hp_tau)
        (mk_box interp_hp_ret)
        (mk_box interp_hp_call)
        (mk_box interp_hp_triggere)
        (mk_box interp_hp_triggers)
        (mk_box interp_hp_triggers)
        (mk_box interp_hp_triggerUB)
        (mk_box interp_hp_triggerNB)
        (mk_box interp_hp_unwrapU)
        (mk_box interp_hp_unwrapN)
        (mk_box interp_hp_Assume)
        (mk_box interp_hp_Guarantee)
        (mk_box interp_hp_ext).

  End HP.

  (* TODO: Same lemmas for other interps ( not defined yet. ) *)

End RED.

Section RED.

  Context `{Σ: GRA.t}.

(* itree reduction *)
  Lemma interp_hAGEs_bind
        (R S: Type)
        stb o
        (s : itree hEs R) (k : R -> itree hEs S)
    :
      interp_hEs_hAGEs stb o (s >>= k)
      =
      st <- interp_hEs_hAGEs stb o s;; interp_hEs_hAGEs stb o (k st).
  Proof.
    unfold interp_hEs_hAGEs in *. grind.
  Qed.

  Lemma interp_hAGEs_tau
        (U: Type)
        (t : itree _ U)
        stb o
    :
      interp_hEs_hAGEs stb o (tau;; t)
      =
      tau;; (interp_hEs_hAGEs stb o t).
  Proof.
    unfold interp_hEs_hAGEs in *. grind.
  Qed.

  Lemma interp_hAGEs_ret
        (U: Type)
        (t: U)
        stb o
    :
      interp_hEs_hAGEs stb o (Ret t)
      =
      Ret t.
  Proof.
    unfold interp_hEs_hAGEs in *. grind.
  Qed.

  Lemma interp_hAGEs_call
        (R: Type)
        (i: callE R)
        stb o
    :
      interp_hEs_hAGEs stb o (trigger i)
      =
      r <- handle_callE_hAGEs stb o i;; tau;; Ret r.
  Proof.
    unfold interp_hEs_hAGEs in *. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_hAGEs_hapc
        (R: Type)
        (i: hAPCE R)
        stb o
    :
      interp_hEs_hAGEs stb o (trigger i)
      =
      (handle_hAPCE_hAGEs stb o i) >>= (fun r => tau;; Ret r).
  Proof.
    unfold interp_hEs_hAGEs. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_hAGEs_triggerp
        (R: Type)
        (i: sE R)
        stb o
    :
      interp_hEs_hAGEs stb o (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof.
    unfold interp_hEs_hAGEs. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_hAGEs_triggere
        (R: Type)
        (i: eventE R)
        stb o
    :
      interp_hEs_hAGEs stb o (trigger i)
      =
      r <- trigger i;; tau;; Ret r.
  Proof.
    unfold interp_hEs_hAGEs. rewrite interp_trigger. grind.
  Qed.  

  Lemma interp_hAGEs_assume
        stb o P
    : 
      interp_hEs_hAGEs stb o (assume P)
      =
      r <- assume P;; tau;; Ret r.
  Proof.
    unfold assume. rewrite interp_hAGEs_bind. rewrite interp_hAGEs_triggere. grind. rewrite interp_hAGEs_ret. refl.
  Qed. 

  Lemma interp_hAGEs_guarantee
        stb o P
    : 
      interp_hEs_hAGEs stb o (guarantee P)
      =
      r <- guarantee P;; tau;; Ret r.
  Proof.
    unfold guarantee. rewrite interp_hAGEs_bind. rewrite interp_hAGEs_triggere. grind. rewrite interp_hAGEs_ret. refl.
  Qed.

  Lemma interp_hAGEs_triggerUB
        (R: Type)
        stb o
    :
      interp_hEs_hAGEs stb o (triggerUB)
      =
      triggerUB (A:=R).
  Proof.
    unfold interp_hEs_hAGEs, triggerUB in *. rewrite unfold_interp. grind.
  Qed.  

  Lemma interp_hAGEs_triggerNB
        (R: Type)
        stb o
    :
      interp_hEs_hAGEs stb o (triggerNB)
      =
      triggerNB (A:=R).
  Proof.
    unfold interp_hEs_hAGEs, triggerNB in *. rewrite unfold_interp. grind.
  Qed.

  Lemma interp_hAGEs_unwrapU 
        (R: Type)
        (i: option R)
        stb o
    :
      interp_hEs_hAGEs stb o (@unwrapU hEs _ _ i)
      =
      r <- (unwrapU i);; Ret r.
  Proof.
    unfold interp_hEs_hAGEs, unwrapU in *. des_ifs; grind.
    eapply interp_hAGEs_triggerUB.
  Qed.

  Lemma interp_hAGEs_unwrapN
        (R: Type)
        (i: option R)
        stb o
    :
      interp_hEs_hAGEs stb o (@unwrapN hEs _ _ i)
      =
      r <- (unwrapN i);; Ret r.
  Proof.
    unfold interp_hEs_hAGEs, unwrapN in *. des_ifs; grind.
    eapply interp_hAGEs_triggerNB.
  Qed.

  Lemma interp_hAGEs_Assume
        P
        stb o
    :
      interp_hEs_hAGEs stb o (trigger (Assume P))
      =
      x <- trigger (Assume P) ;; tau;; Ret x.
  Proof.
    unfold interp_hEs_hAGEs. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_hAGEs_Guarantee
        P
        stb o
    :
      interp_hEs_hAGEs stb o (trigger (Guarantee P))
      =
      x <- trigger (Guarantee P);; tau;; Ret x.
  Proof.
    unfold interp_hEs_hAGEs. rewrite interp_trigger. grind. 
  Qed.

  Lemma interp_hAGEs_ext
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
        stb o
    :
      interp_hEs_hAGEs stb o itr0
      =
      interp_hEs_hAGEs stb o itr1.
  Proof. subst; et. Qed.

End RED.

Global Program Instance interp_hAGEs_rdb `{Σ: GRA.t}: red_database (mk_box (@interp_hEs_hAGEs)) :=
  mk_rdb
    1
    (mk_box interp_hAGEs_bind)
    (mk_box interp_hAGEs_tau)
    (mk_box interp_hAGEs_ret)
    (mk_box interp_hAGEs_call)
    (mk_box interp_hAGEs_triggere)
    (mk_box interp_hAGEs_triggerp)
    (mk_box interp_hAGEs_triggerp)
    (mk_box interp_hAGEs_triggerUB)
    (mk_box interp_hAGEs_triggerNB)
    (mk_box interp_hAGEs_unwrapU)
    (mk_box interp_hAGEs_unwrapN)
    (mk_box interp_hAGEs_Assume)
    (mk_box interp_hAGEs_Guarantee)
    (mk_box interp_hAGEs_ext)
.

