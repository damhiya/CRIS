Require Import Coqlib ITreelib sflib.
Require Import SMod ModSim.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM IPM IFacts.
Require Import Events Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import Mem1 STB.

Require Import ISim HMod Events.
Require Import Mod ModSimFacts.
Require Import CellHeader CellASpec CellA RingHeader RingA RingASpec CtrlI.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section XXX.
  Context `{Σ: GRA.t}.
Definition HModSem_empty: HModSem.t :=
  {| HModSem.fnsems := [];
     HModSem.initial_st := tt↑;
     HModSem.initial_cond := emp |}.
Definition HMod_empty: HMod.t :=
  {|HMod.get_modsem := fun _ => HModSem_empty; HMod.sk := [] |}.

(* Fixpoint hmod_addL (l: list HMod.t) : HMod.t := *)
(*   match l with *)
(*   | [] => HMod_empty *)
(*   | m :: l' => HMod.add m (hmod_addL l') *)
(*   end. *)

End XXX.


  

Module RingIA.
Section SIMMODSEM.
  Context `{Σ: GRA.t}.
  Context `{_M: CellRA.t (Σ:=Σ)}.
  
  Variable max_size : nat.

  Variable StbA: Sk.t -> gname -> option fspec.
  Hypothesis RingInStb: forall sk, stb_incl (to_stb RingAS.Stb) (StbA sk).
  Hypothesis CellInStb: forall sk idx (LT: idx < max_size), stb_incl (to_stb (CellAS.Stb idx)) (StbA sk).

  Import CellAS.

  Local Notation RingAMod := (RingA.t max_size StbA).
  Local Notation CtrlIMod := (CtrlI.t max_size).
  Local Notation CellAMod := (fun i => CellA.t i StbA).

  Fixpoint CellGroup max :=
    match max with
    | 0 => HMod_empty
    | S max' => HMod.add (CellAMod max' ) (CellGroup max')
    end.
  
  Local Notation RingIMod := (HMod.add CtrlIMod (CellGroup max_size)).

  Definition rotate_rev {T} n (l: list T) :=
    drop ((strings.length l)-(n mod strings.length l)) l ++ take ((strings.length l)-(n mod strings.length l)) l.

  Lemma rotate_rev_inv {T} n (l: list T):
    rotate_rev n (rotate n l) = l.
  Proof. admit. Admitted.

  Lemma rotate_rev_id {T} (l: list T):
    rotate_rev 0 l = l.
  Proof. admit. Admitted.
  
  Definition Ist: Any.t -> Any.t -> iProp :=
    (fun st_src st_tgt =>
       ((∃ (sz:nat) (q q': list Z) (hd tl: nat) cell_state,
         ⌜st_src = (sz, q)↑ /\ List.length q = sz /\ sz < max_size /\
          st_tgt = Any.pair (hd,tl)↑ cell_state /\ hd-tl = sz /\
          List.length (q ++ q') = max_size⌝ ∗
          [∗ list] i↦x ∈ rotate_rev tl (q++q'), (CellAS.pending i ∨ CellAS.cell (i mod max_size) x))))%I.

  Variable fl: alist string (Any.t → itree hmodE Any.t).
  Variable fr: alist string (Any.t → itree hmodE Any.t).

Ltac init_simF := let name := fresh "name" in
  unfold HModR.sim_fun; i;
  do 2 match goal with
  | [|-context[alist_find _ (_ (_ (HMod.add ?x _) _))]] => rewrite/__ {1}/x
  | [|-context[alist_find _ (_ (_ ?x _))]] => rewrite/__ {1}/x
  end;
  unseal "ccr";
  alist_find_solver;
  repeat match goal with
  | [|- context[{| fsb_body := cfunU ?x |}]] => rewrite/__ {1}/x
  | [|- context[cfunU ?x]] => rewrite/__ {1}/x
  end;
  unfold interp_sb_hp, HoareFun, cfunU, ccallU; s;
  ii; subst; iIntros "IST".

Ltac hss :=
  ss;
  try (unfold run_l, run_r in *; rewrite !Any.pair_split in *; fold run_l run_r in * );
  try (rewrite !Any.upcast_downcast in * );
  (repeat match goal with [G: Any.downcast _ = Some _ |-_] =>
    apply Any.downcast_upcast in G; inv G; ss
   end);
  (repeat match goal with [G: Any.upcast (_:?T) = Any.upcast (_:?T) |-_] =>
    apply Any.upcast_inj in G; destruct G as [_ G]; red in G; depdes G; ss
   end);
  (repeat match goal with [G: Some _ = Some _ |- _] =>
    depdes G; ss
   end).

Ltac inv_string X :=
  inv X;
  repeat match goal with [H: @eq string (_ ++ _)%string (_ ++ _)%string|-_] =>
           apply string_app_inv in H
    end; ss.

Ltac alist_find_solver :=
  match goal with [|-context[alist_find ?x]] => rewrite <-(Seal.sealing_eq "_tmp_" x) end;
  s; unfold rel_dec, Dec_RelDec, sumbool_to_bool, dec, string_Dec;
  des_ifs; unseal "_tmp_";
  repeat match goal with [H: @eq string _ _|-_] => inv_string H end;
  repeat match goal with [H: not (@eq string _ _)|-_] => clear H end.





Lemma string_app_length s1 s2:
  length (s1++s2)%string = length s1 + length s2.
Proof.
  induction s1.
  - unfold append; fold append. eauto.
  - s. fold append. rewrite IHs1. nia.
Qed.

Lemma string_app_inv_r
  p s s'
  (EQ: (s ++ p = s' ++ p)%string)
  :
  (s = s')%string.
Proof.
  revert p s' EQ. induction s; i; ss.
  { destruct s'; eauto.
    apply (f_equal length) in EQ.
    rewrite !string_app_length in EQ. ss. nia. }
  destruct s'.
  { apply (f_equal length) in EQ.
    rewrite !string_app_length in EQ. ss. nia. }
  revert EQ. unfold append; fold append. i.
  inv EQ. f_equal. eauto.
Qed.

Lemma list_ascii_of_string_app s1 s2:
  list_ascii_of_string (s1 ++ s2)%string =
    list_ascii_of_string s1 ++ list_ascii_of_string s2.
Proof.
  revert s2. induction s1; i; s; eauto.
  rewrite IHs1; eauto.
Qed.

Lemma string_of_list_ascii_app l1 l2:
  string_of_list_ascii (l1 ++ l2) =
    (string_of_list_ascii l1 ++ string_of_list_ascii l2)%string.
Proof.
  revert l2. induction l1; i; s; eauto.
  rewrite IHl1. eauto.
Qed.

(* Lemma string_app_nil s: *)
(*   (s ++ "")%string = s. *)
(* Proof. *)
(*   induction s; eauto. *)
(*   unfold append; fold append. rewrite IHs; eauto. *)
(* Qed. *)

(* Lemma string_rev_app_inv_r *)
(*   (s1 s2 s3: string) *)
(*   (EQ: string_rev_app s1 s3 = string_rev_app s2 s3) *)
(*   : *)
(*   s1 = s2. *)
(* Proof. *)
(*   revert s2 s3 EQ. induction s1; i; ss. *)
(*   - Check string_rev_app. *)

(* Qed. *)

(* string_of_list_ascii_of_string: *)
(*   ∀ s : string, string_of_list_ascii (list_ascii_of_string s) = s *)
(* list_ascii_of_string_of_list_ascii: *)
(*   ∀ s : list Ascii.ascii, list_ascii_of_string (string_of_list_ascii s) = s *)

(* Lemma string_app_rev *)
(*   (s s': string) *)
(*   : *)
(*   (string_rev (s ++ s') = string_rev s' ++ string_rev s)%string. *)
(* Proof. *)
(*   revert s'; induction s; s; i. *)
(*   { unfold append; fold append. *)
(*     unfold string_rev; s. *)
(*     Search (_++_)%string. *)
(* Qed. *)

(* Definition name_prefix (i: nat) (name: string) := *)
(*   HexString.of_nat i +:+ ":" +:+ name. *)

  Lemma string_of_nat_prefix_eq idx1 idx2 method1 method2
    (EQ: (HexString.of_nat idx1 ++ "." ++ method1 =
          HexString.of_nat idx2 ++ "." ++ method2)%string)
    :
    idx1 = idx2.
  Proof.
  Admitted.

  Lemma cell_name_neq idx idx' method
    (NEQ: idx ≠ idx') sk
    :
    alist_find (CellName.mk idx method) (List.map HModSem.trans_r
      (HModSem.fnsems (HMod.get_modsem (CellA.t idx' StbA) sk))) = None.
  Proof.
    unfold CellA.t. unseal "ccr". s.
    unfold rel_dec, Dec_RelDec, sumbool_to_bool, dec, string_Dec.
    des_ifs; exfalso; apply string_of_nat_prefix_eq in H1; ss.
  Qed.

  Fixpoint emb_rec n fns :=
    match n with
    | 0 => List.map HModSem.trans_l fns
    | S n' => List.map HModSem.trans_r (emb_rec n' fns)
    end.
  
  Lemma cell_name_find max idx method
    (LT: idx < max) sk
    :
    alist_find (CellName.mk idx method) (List.map HModSem.trans_r
      (HModSem.fnsems (HMod.get_modsem (CellGroup max) sk)))
    =
    alist_find (CellName.mk idx method) (List.map HModSem.trans_r
      (HModSem.fnsems (HMod.get_modsem (CellA.t idx StbA) sk))).
  Proof.
    revert_until max. clear -max. induction max; i.
    { nia. }
    assert (idx = max \/ idx < max) by nia. des; subst.
    { s. unfold HModSem.add_fnsems. rewrite List.map_app.
      destruct (alist_find (CellName.mk max method)
                  (List.map HModSem.trans_r
                     (HModSem.fnsems (HMod.get_modsem (CellA.t max StbA) sk)))) eqn: EQ.
      - eapply alist_find_app. rewrite List.map_map.
        
        Search alist_find.



      unfold CellA.t. unseal "ccr".
  match goal with [|-context[alist_find ?x]] => rewrite <-(Seal.sealing_eq "_tmp_" x) end.
  s; unfold rel_dec, Dec_RelDec, sumbool_to_bool, dec, string_Dec;
  des_ifs; unseal "_tmp_".
  + exfalso. inv e.
    apply (f_equal list_ascii_of_string) in H1.
    rewrite !list_ascii_of_string_app in H1.
    apply (f_equal (@rev _)) in H1.
    rewrite !rev_app_distr in H1.
    apply app_inv_head in H1.
    apply (f_equal (@rev _)) in H1.
    rewrite !rev_involutive in H1.
    apply (f_equal string_of_list_ascii) in H1.
    rewrite !string_of_list_ascii_of_string in H1.
    apply (f_equal HexString.to_nat) in H1.
    rewrite !HexString.to_nat_of_nat in H1. nia.
  + exfalso. inv e.
    apply (f_equal list_ascii_of_string) in H1.
    rewrite !list_ascii_of_string_app in H1.
    apply (f_equal (@rev _)) in H1.
    rewrite !rev_app_distr in H1. ss.
  +
    

    Search string.


    Require Import HexString.


    apply string_app_inv_r in H1.
    apply (f_equal HexString.to_nat) in H1.
    rewrite !HexString.to_nat_of_nat in H1. nia.

    
  
  

  apply string_app_inv in H1.
  
  try match goal with [H: @eq string _ _|-_] => inv_string H end.



  
  repeat match goal with [H: not (@eq string _ _)|-_] => clear H end
    
    destruct idx.
    -

    
    - destruct max_size eqn: EQ; try nia. s. rewrite EQ.
      unfold CellA.t. unseal "ccr".

  match goal with [|-context[alist_find ?x]] => rewrite <-(Seal.sealing_eq "_tmp_" x) end.
  s; unfold rel_dec, Dec_RelDec, sumbool_to_bool, dec, string_Dec.
  des_ifs; unseal "_tmp_".

  

  
  
  repeat match goal with [H: @eq string _ _|-_] => inv_string H end.


  
  repeat match goal with [H: not (@eq string _ _)|-_] => clear H end.
      
      alist_find_solver.
      
      
    
    
  Qed.

  Lemma simF_init:
    HModR.sim_fun RingAMod RingIMod Ist RingName.init.
  Proof.
    init_simF.

    st_l. iDestruct "ASM" as "%". subst. hss.
    iDestruct "IST" as (sz q q' hd tl cell_state) "(% & CS)". des; subst.

    st_r. force_l. st_l. force_l.
    iSplitL "". { eauto. }

    st.
    iSplitL; eauto.
    iExists 0, [], (rotate_rev tl (q++q')%list), 0, 0, cell_state. s.
    replace (rotate_rev 0 (rotate_rev tl (q ++ q'))) with
      (rotate_rev tl (q ++ q')) by admit.
    iFrame. hss.
    iPureIntro. esplits; eauto; try nia.
    admit.
  Admitted.

  Lemma simF_dequeue:
    HModR.sim_fun RingAMod RingIMod Ist RingName.dequeue.
  Proof.
    init_simF.

    st_l. iDestruct "ASM" as "%". subst. hss.
    iDestruct "IST" as (sz q q' hd tl cell_state) "(% & CS)". des; subst.
    st_l. st_r. hss. rewrite <-H4. destruct (hd-tl) eqn: EQ; s.
    { st. do 2 force_l. iSplitL ""; eauto.
      st. iSplitL; eauto. unfold Ist.
      iExists _,_,_,_,_,_. iFrame.
      iPureIntro. esplits; eauto. nia.
    }

    st_r.
    inline_r.
    { unfold CtrlIMod. unseal "ccr". hide_evars.
      alist_find_solver. show_evars.
      
      

  match goal with [|-context[alist_find ?x]] => rewrite <-(Seal.sealing_eq "_tmp_" x) end.
  s; unfold rel_dec, Dec_RelDec, sumbool_to_bool, dec, string_Dec.
  des_ifs. unseal "_tmp_".
  repeat match goal with [H: @eq string _ _|-_] => inv_string H end;
  repeat match goal with [H: not (@eq string _ _)|-_] => clear H end      
      alist_find_solver.

      
  Smatch goal with [|-context[alist_find ?x]] => rewrite <-(Seal.sealing_eq "_tmp_" x) end.
  s; unfold rel_dec, Dec_RelDec, sumbool_to_bool, dec, string_Dec.
  des_ifs; unseal "_tmp_".
  
  repeat match goal with [H: @eq string _ _|-_] => inv_string H end.
  repeat match goal with [H: @eq string _ _|-_] => inv_string H end.
  repeat match goal with [H: @eq string _ _|-_] => inv_string H end.
  repeat match goal with [H: @eq string _ _|-_] => inv_string H end.

  

  
  repeat match goal with [H: (_: string) ≠ _|-_] => clear H end.

      


    
    
exfalso.



    
    



    force_l. st_l. force_l.
    iSplitL "". { eauto. }
    
    st_l. iDestruct "ASM" as "((% & C) & %)".
    subst. hss. rename y0 into v. unfold Ist.
    iDestruct "IST" as "[(C0 & _)|(P & IST)]".
    { iExFalso. iApply (cell_unique with "C0 C"). }
    iDestruct "IST" as (v') "(A & %)". subst. hss.

    iPoseProof (cell_auth_get with "C A") as "%". subst.

    st_r. force_l. st_l. force_l. force_l.
    iSplitL "C". { eauto. }

    st. iSplitL; [|eauto].
    iRight. iFrame. eauto.
  Qed.
  
  Lemma simF_set:
    HModR.sim_fun CellAMod CellIMod Ist (CellName.set idx).
  Proof.
    init_simF.
    
    st_l. hss. iDestruct "ASM" as "((% & C) & %)".
    subst. hss. rename y1 into v, y2 into v0. unfold Ist.
    iDestruct "IST" as "[(C0 & _)|(P & IST)]".
    { iExFalso. iApply (cell_unique with "C0 C"). }
    iDestruct "IST" as (v') "(A & %)". subst. hss.

    iPoseProof (cell_auth_get with "C A") as "%". subst.
    iMod (cell_auth_set with "C A") as "(C & A)".
    
    st_r. force_l. st_l. force_l. force_l.
    iSplitL "C". { eauto. }

    st. iSplitL; [|eauto].
    iRight. iFrame. eauto.
  Qed.

  Theorem sim: HModR.sim CellAMod CellIMod Ist.
  Proof.
    init_sim.
    - unfold Ist. eauto.
    - use_simF simF_init.
    - use_simF simF_get.
    - use_simF simF_set.
  Qed.

End SIMMODSEM.
End RingIA.
