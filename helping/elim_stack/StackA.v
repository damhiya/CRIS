Require Import CRIS.
Require Import MemHeader MemA.
Require Import SchHeader SchA.
From CRIS.helping Require Import Header HelpingTactics.
Require Import StackHeader.

Class stackG (jobID retID : Type) `{!crisG Γ Σ α β τ _S _I} := StackG {
  stack_tokG :: inG (exclR unitO) Γ;
  stack_stateG :: inG (authR (optionUR $ exclR (listO (leibnizO val)))) Γ;
  stack_helpingG :: inG (helpingR jobID retID) Γ;
}.
Definition stackΓ (jobID retID : Type) : HRA :=
  #[exclR unitO; authR (optionUR $ exclR (listO (leibnizO val))); helpingR jobID retID].
Global Instance subG_stackG (jobID retID : Type) `{!crisG Γ Σ α β τ _S _I} :
  subG (stackΓ jobID retID) Γ → (stackG jobID retID).
Proof. solve_inG. Defined.
Hint Unfold subG_stackG stack_tokG stack_stateG : GRA_index.

Global Instance SLRed_self `{!subG (Γ : HRA) Σ, !SL.G Γ Σ α β τ} {n} (f : GTerm.t n) :
  SLRed f (⟦f, n⟧)%I | 6.
Proof. econs; SL_red; eauto. Qed.

Section definitions.
  Definition jobID : Type := nat * nat * (val * val * gname).
  Definition retID : Type := val.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !memG, !stackG jobID retID, !newschG} (N : namespace).

  Definition offerN := N .@ "offer".
  Definition stackN := N .@ "stack".

  Definition stack_content (γs : gname) (l : list (leibnizO val)) : iProp Σ :=
    (own γs (◯ Excl' l))%I.

  Lemma stack_content_exclusive γs l1 l2 :
    stack_content γs l1 -∗ stack_content γs l2 -∗ False.
  Proof.
    iIntros "Hl1 Hl2".
    iCombine "Hl1 Hl2" gives %[]%auth_frag_op_valid_1.
  Qed.

  Fixpoint syn_list_inv (l : list val) (rep : val) (n : nat) : GTerm.t n :=
    match l with
    | nil => ⌜rep = Vint 0⌝
    | v::l => ∃ (blk : τ{mblock}) (ofs : τ{ptrofs}) (rep' : τ{val}) (q0 q1 : τ{Qp}),
        ⌜rep = Vptr (blk, ofs)⌝ ∗
        (blk, ofs) ↦{q0} v ∗ (blk, ofs + 1)%Z ↦{q1} rep' ∗ syn_list_inv l rep' n
    end%SAT.

  Fixpoint list_inv (l : list val) (rep : val) (n : nat) : iProp Σ :=
    match l with
    | nil => ⌜rep = Vint 0⌝
    | v::l => ∃ (blk : mblock) (ofs : ptrofs) (rep' : val) (q0 q1 : Qp),
        ⌜rep = Vptr (blk, ofs)⌝ ∗
        (blk, ofs) ↦{q0} v ∗ (blk, ofs + 1)%Z ↦{q1} rep' ∗ list_inv l rep' n
    end%I.

  Global Instance list_inv_SLRed l n rep : SLRed (syn_list_inv l rep n) (list_inv l rep n).
  Proof. revert n rep; induction l; econs; rewrite SLRed_red //. Qed.
  Local Hint Extern 0 (environments.envs_entails _ (list_inv (_::_) _)) => simpl : core.

  Lemma list_inv_comparable l rep n :
    list_inv l rep n -∗
    list_inv l rep n ∗
    (∃ q v, MemSpec.val_r rep q v) ∗
    □ (∀ l' rep' n', list_inv l' rep' n' -∗ ∃ succ, ⌜MemSpec.compare_val rep' rep = Vint succ⌝).
  Proof.
    iIntros "L"; iAssert (⌜rep = Vint 0 ∨ ∃ b ofs, rep = Vptr (b, ofs)⌝)%I as "%".
    { destruct l; ss; first iPoseProof "L" as "%"; eauto.
      iDestruct "L" as "[% [% [% [% [% [-> ?]]]]]]"; iPureIntro; right; esplits; eauto.
    }
    iAssert (list_inv l rep n ∗ ∃ v q, MemSpec.val_r (rep) q v)%I
      with "[L]" as "[L [% [% $]]]".
    { destruct rep as [v'|v'|]; eauto. destruct v'; eauto.
      destruct l; eauto.
      { iPoseProof "L" as "%"; clarify. }
      { iDestruct "L" as "[% [% [% [% [% [% [↦ R]]]]]]]". clarify; eauto.
        iDestruct "↦" as "[↦1 ↦2]"; ss; iSplitR "↦1"; last iFrame.
        iExists _, _, _, _, _; iSplit; first done. iFrame "↦2 R".
      }
    }

    iFrame "L".
    iIntros "!> % % % L"; destruct l'; ss.
    { iPoseProof "L" as "->"; des; clarify; eauto. }
    { iPoseProof "L" as "[% [% [% [% [% [-> ?]]]]]]"; des; clarify; iPureIntro; eauto; ss.
      des_ifs; eauto.
    }
  Unshelve. all: try exact Vundef; try exact 1%Qp.
  Qed.

  Definition syn_offer_inv n γo (offer : mblock * ptrofs) (rid : nat) (jid : jobID) : GTerm.t n :=
    (∃ (offerst : τ{Z}),
      (offer.1, offer.2 + 1)%Z ↦ Vint offerst ∗
      if (decide (offerst = 0%Z))
      then offer ↦ jid.2.1.2 ∗ syn_helping_token n rid jid
      else if (decide (offerst = 1)) then syn_helping_done n rid Vundef
      else if (decide (offerst = 2)) then <own> γo (Excl ())
      else ⊥)%SAT.

  Definition offer_inv γo (offer : mblock * ptrofs) (rid : nat) (jid : jobID) : iProp Σ :=
    (∃ (offerst : Z),
      (offer.1, offer.2 + 1)%Z ↦ Vint offerst ∗
      if (decide (offerst = 0%Z))
      then offer ↦ jid.2.1.2 ∗ helping_token rid jid
      else if (decide (offerst = 1)) then helping_done rid Vundef
      else if (decide (offerst = 2)) then own γo (Excl ())
      else False)%I.
  Global Instance SLRed_offer_inv n γo offer rid jid :
    SLRed (syn_offer_inv n γo offer rid jid) (offer_inv γo offer rid jid).
  Proof.
    econs; rewrite /syn_offer_inv /offer_inv ?SLRed_red; do 2 f_equiv; ii.
    des_ifs; rewrite ?SLRed_red //.
  Qed.

  Definition syn_is_offer (γs : gname) (offer_rep : val) (n : nat) : GTerm.t n :=
    match offer_rep with
    | Vptr (offerb, offerofs) => 
      ∃ (γo : τ{gname}) (jid : τ{jobID}) (rid : τ{nat}),
        syn_inv n offerN (syn_offer_inv n γo (offerb, offerofs) rid jid)
        ∗ ⌜jid.2.2 = γs⌝
    | Vint 0 => ⊤
    | _ => ⊥
    end%SAT.

  Definition syn_stack_inv (γs : gname) (stackb : mblock) (stackofs : ptrofs) (n : nat) : GTerm.t n :=
    ((∃ (stack_rep : τ{val}) (offer_rep : τ{val}) (l : τ{list val}), <own> γs (● Excl' l) ∗
       (stackb, stackofs) ↦ stack_rep ∗ syn_list_inv l stack_rep n ∗
       (stackb, stackofs + 1)%Z ↦ offer_rep ∗ syn_is_offer γs offer_rep n) ∨
     (∃ (reqmap : τ{gmap nat (option _ * _)}), syn_helping_auth n (1/2)%Qp reqmap))%SAT.

  Definition is_stack (γs : gname) (s : val) (n : nat) : iProp Σ :=
    (∃ (stackb : mblock) (stackofs : ptrofs),
      ⌜s = Vptr (stackb, stackofs)⌝ ∗ inv n stackN (syn_stack_inv γs stackb stackofs n))%I.

  Definition new_stack_spec : fspec :=
    fspec_sch (↑N)
      (fspec_simple (λ _ : (),
        ((λ arg, ∃ (v : list val), ⌜arg = v↑⌝),
         (λ ret, ∃ v γs, ⌜ret = v↑⌝ ∗ is_stack γs v 0 ∗ stack_content γs []))%I)).

  Definition push_spec : fspec :=
    fspec_sch (↑N)
      (fspec_simple (λ '((s, v, γs) : val * val * gname),
        ((λ arg, ⌜arg = [s; v]↑⌝ ∗ is_stack γs s 0),
         (λ ret, ⌜ret = Vundef↑⌝))))%I.

  Definition pop_spec : fspec :=
    fspec_sch (↑N)
      (fspec_simple (λ '((s, γs) : val * gname),
        ((λ arg, ⌜arg = [s]↑⌝ ∗ is_stack γs s 0),
         (λ ret, True))))%I.
End definitions.

(* Temporary note : for this spec to make sense, pre/postconditions for atomic update should be
   able to depend on the choice of the metavariable of the private pre/postconditions.
   Thus, conventional Hoarefun is not usable for now. *)
Module StackM. Section StackM.
  Definition jobID : Type := nat * nat * (val * val * gname).
  Definition retID : Type := val.

  Context `{!crisG Γ Σ α β τ _S _I, !concG, !newschG, !memG, !stackG jobID retID}.
  Context (mn : string) (N : namespace).

  (* Module definitions *)
  Definition scopes : list string := [].

  Definition jobCode : jobID → itree Helping.pureE retID :=
    λ '(_, _, (_, v, γs)),
      l <- trigger (Take (list (leibnizO val)));;
      trigger (Assume (stack_content γs l));;;
      trigger (Guarantee (stack_content γs (v :: l)));;;
      Ret Vundef.

  Definition new_stack : list val → itree crisE val :=
    λ _, 𝒴;;; trigger (Choose val).

  Definition push : list val → itree crisE val := λ arg,
    x <- trigger (Take (meta (push_spec N)));;
    trigger (Assume ((precond (push_spec N)) x arg↑ arg↑));;;
    'vret : retID <- ccallU (Helping.run mn) x;;
    trigger (Guarantee ((postcond (push_spec N)) x vret↑ vret↑));;;
    Ret vret.

  Definition pop : list val → itree crisE val := λ arg,
    x <- trigger (Take (meta (pop_spec N)));;
    trigger (Assume ((precond (pop_spec N)) x arg↑ arg↑));;;
    𝒴;;;
    'b : _ <- trigger (Choose bool);;
    (if b : bool then (ccallU (Helping.help mn) ()) else Ret ());;;
    l <- trigger (Take (list (leibnizO val)));;
    trigger (Assume (stack_content x.2.2 l));;;
    trigger (Guarantee (stack_content x.2.2 (tail l)));;;
    let vret := match l with | v :: _ => v | _ => Vundef end in
    𝒴;;;
    trigger (Guarantee ((postcond (pop_spec N)) x vret↑ vret↑));;;
    Ret vret.

  Definition fnsems : fnsems_type :=
    [(Some StackHdr.new_stack, (true, wmask_all, scopes, (Some (new_stack_spec N), cfunU new_stack)));
     (Some StackHdr.push,      (true, wmask_all, scopes, (None, cfunU push)));
     (Some StackHdr.pop,       (true, wmask_all, scopes, (None, cfunU pop)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t sp := Seal.sealing CRIS (SMod.to_mod sp Mod).
End StackM. End StackM.

(* Module StackA. Section StackA.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !memG, !stackG} (N : namespace).
  (* Module definitions *)
  Definition scopes : list string := [].

  Definition new_stack : Any.t → itree crisE Any.t :=
    λ arg, ret <- lat_img false (new_stack_spec N) 𝒴 fbody_trivial arg;; 𝒴;;; Ret ret.
  Definition push : Any.t → itree crisE Any.t :=
    λ arg, ret <- lat_img true (push_spec N) 𝒴 fbody_trivial arg;; 𝒴;;; Ret ret.

  Definition fnsems : fnsems_type :=
    [(Some StackHdr.new_stack, (true, wmask_all, scopes, (None, new_stack)));
     (Some StackHdr.push,      (true, wmask_all, scopes, (None, push)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (SMod.to_mod sp_none Mod).
End StackA. End StackA. *)