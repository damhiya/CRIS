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

  Definition stack_elem_to_val (stack_rep : option val) : val :=
    match stack_rep with
    | None => Vint 0
    | Some l => l
    end.

  Fixpoint list_inv (l : list val) (rep : option val) (n : nat) : GTerm.t n :=
    match l with
    | nil => ⌜rep = None⌝
    | v::l => ∃ (blk : τ{mblock}) (ofs : τ{ptrofs}) (rep' : τ{option val}),
        ⌜rep = Some (Vptr (blk, ofs))⌝ ∗
        (blk, ofs) ↦□ v ∗ (blk, ofs + 1)%Z ↦□ stack_elem_to_val rep' ∗ list_inv l rep' n
    end%SAT.

  Definition is_offer (γs : gname) (offer_rep : option val) (n : nat) : GTerm.t n :=
    match offer_rep with
    | None => ⊤
    | Some l => ⊤
      (* ∃ Q γo, inv offerN (offer_inv st_loc γo (stack_push_au γs v Q) Q) *)
    end%SAT.

  Local Instance is_offer_persistent γs offer_rep n : Persistent (⟦is_offer γs offer_rep n⟧).
  Proof. rewrite /is_offer; destruct offer_rep as [?|]; SL_red; apply _. Qed.

  Definition offer_to_val (offer_rep : option val) : val :=
    match offer_rep with
    | None => Vint 0
    | Some l => l
    end.

  Definition stack_inv (γs : gname) (stackb : mblock) (stackofs : ptrofs) (n : nat) : GTerm.t n :=
    (∃ (stack_rep offer_rep : τ{option val}) (l : τ{list val}), <own> γs (● Excl' l) ∗
       (stackb, stackofs) ↦ stack_elem_to_val stack_rep ∗ list_inv l stack_rep n ∗
       (stackb, stackofs + 1)%Z ↦ offer_to_val offer_rep ∗ is_offer γs offer_rep n)%SAT.

  Definition is_stack (γs : gname) (s : val) (n : nat) : iProp Σ :=
    (∃ (stackb : mblock) (stackofs : ptrofs),
      ⌜s = Vptr (stackb, stackofs)⌝ ∗ inv n stackN (stack_inv γs stackb stackofs n))%I.

  Definition new_stack_spec : fspecS :=
    from_fspec
      (fspec_winv (↑N)
         (fspec_simple
           (λ _ : (),
            ((λ arg, ∃ (v : list val), ⌜arg = v↑⌝),
             (λ ret, ∃ v γs, ⌜ret = v↑⌝ ∗ is_stack γs v 0 ∗ stack_content γs []))%I))).

  Definition push_spec : fspecS :=
    from_fspec
      (fspec_winv (↑N)
         (fspec_simple
           (λ '((s, v, l, γs) : val * val * list (leibnizO val) * gname),
            ((λ arg, ⌜arg = [s; v]↑⌝ ∗ is_stack γs s 0 ∗ stack_content γs l),
             (λ ret, ⌜ret = Vundef↑⌝ ∗ stack_content γs (v :: l)))%I))).
End definitions.

Module StackM. Section StackM.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !memG, !stackG} (N : namespace).
  (* Module definitions *)
  Definition scopes : list string := [].

  (* Definition jobID : Type := val.
  Definition jobCode : jobID → itree Helping.pureE unit :=
    λ v, ret <- lat_img false (push_spec N) 𝒴 (Ret ()) v;; 𝒴;;; Ret ret. *)

  Definition new_stack : Any.t → itree crisE Any.t :=
    λ arg, ret <- lat_img false (new_stack_spec N) 𝒴 fbody_trivial arg;; 𝒴;;; Ret ret.
  Definition push : Any.t → itree crisE Any.t :=
    λ arg, ret <- lat_img false (push_spec N) 𝒴 fbody_trivial arg;; 𝒴;;; Ret ret.

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

Module StackA. Section StackA.
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
End StackA. End StackA.