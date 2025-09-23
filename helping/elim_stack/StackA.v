Require Import CRIS.
Require Import MemHeader MemA.
Require Import SchHeader.
From CRIS.helping Require Import Header.
Require Import StackHeader.

Class stackG `{!crisG Γ Σ α β τ _S _I} := StackG {
  stack_tokG :: inG (exclR unitO) Γ;
  stack_stateG :: inG (authR (optionUR $ exclR (listO (leibnizO val)))) Γ;
}.
Definition stackΓ : HRA := #[exclR unitO; authR (optionUR $ exclR (listO (leibnizO val)))].
Global Instance subG_stackG `{!crisG Γ Σ α β τ _S _I} : subG stackΓ Γ → stackG.
Proof. solve_inG. Defined.
Hint Unfold subG_stackG stack_tokG stack_stateG : GRA_index.

Class SLRed `{Σ : GRA, @GATIntp.t (domain Σ) α} {n} (f : GTerm.t n) (P : iProp Σ) := {
  SLRed_eq : ⟦f⟧ ⊣⊢ P
}.
Lemma SLRed_red `{S : SLRed n f P} : ⟦f⟧ ⊣⊢ P.
Proof. destruct S; ss. Qed.

Section instances.
  Context `{!subG (Γ : HRA) Σ, !SL.G Γ Σ α β τ}.

  Global Instance SLRed_own `{!inG M Γ, n : nat} (m : M) γ :
    SLRed (n:=n) (<own> γ m)%SAT (own γ m).
  Proof. econs; SL_red; eauto. Qed.

  Global Instance SLRed_pure {n} (P : Prop) :
    SLRed (⌜P⌝ : GTerm.t n)%SAT (⌜P⌝)%I.
  Proof. econs; SL_red; eauto. Qed.

  Global Instance SLRed_ex {A n} `{!STτ.t τ}
      (f : A → GTerm.t n) (g : A → iProp Σ) `{∀ a, SLRed (f a) (g a)} :
    SLRed (∃ a : τ{A}, f a)%SAT (∃ a, g a)%I.
  Proof.
    econs; SL_red; iSplit; iIntros "[%b H]"; iExists b; try rewrite SLRed_red //.
  Qed.

  Global Instance SLRed_and {n} (f g : GTerm.t n) P Q `{!SLRed f P, !SLRed g Q} :
    SLRed (f ∧ g)%SAT (P ∧ Q).
  Proof. econs; rewrite SLRed.and ?SLRed_red //. Qed.

  Global Instance SLRed_or {n} (f g : GTerm.t n) P Q `{!SLRed f P, !SLRed g Q} :
    SLRed (f ∨ g)%SAT (P ∨ Q).
  Proof. econs; rewrite SLRed.or ?SLRed_red //. Qed.

  Global Instance SLRed_sep {n} (f g : GTerm.t n) P Q `{!SLRed f P, !SLRed g Q} :
    SLRed (f ∗ g)%SAT (P ∗ Q).
  Proof. econs; rewrite SLRed.sepconj ?SLRed_red //. Qed.
End instances.

Section definitions.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !memG, !stackG} (N : namespace).

  Let offerN := N .@ "offer".
  Let stackN := N .@ "stack".

  Definition stack_content (γs : gname) (l : list (leibnizO val)) : iProp Σ :=
    (own γs (◯ Excl' l))%I.

  Lemma stack_content_exclusive γs l1 l2 :
    stack_content γs l1 -∗ stack_content γs l2 -∗ False.
  Proof.
    iIntros "Hl1 Hl2".
    iCombine "Hl1 Hl2" gives %[]%auth_frag_op_valid_1.
  Qed.

  (* Definition stack_elem_to_val (stack_rep : option val) : val :=
    match stack_rep with
    | None => Vint 0
    | Some l => l
    end. *)

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

  Definition syn_is_offer (γs : gname) (offer_rep : option val) (n : nat) : GTerm.t n :=
    match offer_rep with
    | None => ⊤
    | Some l => ⊤
      (* ∃ Q γo, inv offerN (offer_inv st_loc γo (stack_push_au γs v Q) Q) *)
    end%SAT.

  Definition is_offer (γs : gname) (offer_rep : option val) (n : nat) : iProp Σ :=
    match offer_rep with
    | None => True
    | Some l => True
      (* ∃ Q γo, inv offerN (offer_inv st_loc γo (stack_push_au γs v Q) Q) *)
    end%I.

  Global Instance is_offer_SLRed γs offer_rep n :
    SLRed (syn_is_offer γs offer_rep n) (is_offer γs offer_rep n).
  Proof.
    rewrite /syn_is_offer; destruct offer_rep; ss; econs; SL_red; eauto.
  Qed.

  Local Instance is_offer_persistent γs offer_rep n : Persistent (⟦syn_is_offer γs offer_rep n⟧).
  Proof. rewrite SLRed_red. destruct offer_rep as [?|]; SL_red; apply _. Qed.

  Definition offer_to_val (offer_rep : option val) : val :=
    match offer_rep with
    | None => Vint 0
    | Some l => l
    end.

  Definition syn_stack_inv (γs : gname) (stackb : mblock) (stackofs : ptrofs) (n : nat) : GTerm.t n :=
    (∃ (stack_rep : τ{val}) (offer_rep : τ{option val}) (l : τ{list val}), <own> γs (● Excl' l) ∗
       (stackb, stackofs) ↦ stack_rep ∗ syn_list_inv l stack_rep n ∗
       (stackb, stackofs + 1)%Z ↦ offer_to_val offer_rep ∗ syn_is_offer γs offer_rep n)%SAT.

  Definition stack_inv (γs : gname) (stackb : mblock) (stackofs : ptrofs) (n : nat) : iProp Σ :=
    (∃ (stack_rep : val) (offer_rep : option val) (l : list val), own γs (● Excl' l) ∗
      (stackb, stackofs) ↦ stack_rep ∗ list_inv l stack_rep n ∗
      (stackb, stackofs + 1)%Z ↦ offer_to_val offer_rep ∗ is_offer γs offer_rep n)%I.

  Global Instance stack_inv_SLRed γs stackb stackofs n :
    SLRed (syn_stack_inv γs stackb stackofs n) (stack_inv γs stackb stackofs n).
  Proof. rewrite /syn_stack_inv /stack_inv; econs; rewrite SLRed_red //. Qed.

  Definition is_stack (γs : gname) (s : val) (n : nat) : iProp Σ :=
    (∃ (stackb : mblock) (stackofs : ptrofs),
      ⌜s = Vptr (stackb, stackofs)⌝ ∗ inv n stackN (syn_stack_inv γs stackb stackofs n))%I.

  Definition new_stack_spec : fspec :=
    fspec_winv (↑N)
      (fspec_simple (λ _ : (),
        ((λ arg, ∃ (v : list val), ⌜arg = v↑⌝),
         (λ ret, ∃ v γs, ⌜ret = v↑⌝ ∗ is_stack γs v 0 ∗ stack_content γs []))%I)).

  Definition push_spec : fspec :=
    fspec_winv (↑N)
      (fspec_simple (λ '((s, v, l, γs) : val * val * list (leibnizO val) * gname),
        ((λ arg, ⌜arg = [s; v]↑⌝ ∗ is_stack γs s 0 ∗ stack_content γs l),
         (λ ret, ⌜ret = Vundef↑⌝ ∗ stack_content γs (v :: l)))%I)).
End definitions.

Module StackM. Section StackM.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !memG, !stackG} (N : namespace).
  (* Module definitions *)
  Definition scopes : list string := [].

  (* Definition jobID : Type := val.
  Definition jobCode : jobID → itree Helping.pureE unit :=
    λ v, ret <- lat_img false (push_spec N) 𝒴 (Ret ()) v;; 𝒴;;; Ret ret. *)

  Definition new_stack : Any.t → itree crisE Any.t :=
    λ arg, ret <- lat_img false (from_fspec (new_stack_spec N)) 𝒴 fbody_trivial arg;; 𝒴;;; Ret ret.
  Definition push : Any.t → itree crisE Any.t :=
    λ arg, ret <- lat_img true (from_fspec (push_spec N)) 𝒴 fbody_trivial arg;; 𝒴;;; Ret ret.

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