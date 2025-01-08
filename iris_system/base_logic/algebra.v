From iris.algebra Require Import cmra view auth agree csum list excl gmap.
From iris.algebra.lib Require Import excl_auth gmap_view dfrac_agree.
From iris.bi Require Import lib.cmra.
From CRIS.base_logic Require Import bi derived.
From iris.prelude Require Import options.

(** Internalized properties of our CMRA constructions. *)
Local Coercion uPred_holds : uPred >-> Funclass.

Section upred.
  Context {M : ucmra}.

  (* Force implicit argument M *)
  Notation "P ⊢ Q" := (bi_entails (PROP:=uPredI M) P Q).
  Notation "P ⊣⊢ Q" := (equiv (A:=uPredI M) P%I Q%I).
  Notation "⊢ Q" := (bi_emp_valid (PROP:=uPredI M) Q).

  Lemma prod_validI {A B : cmra} (x : A * B) : ✓ x ⊣⊢ ✓ x.1 ∧ ✓ x.2.
  Proof. by uPred.unseal. Qed.
  Lemma option_validI {A : cmra} (mx : option A) :
    ✓ mx ⊣⊢ match mx with Some x => ✓ x | None => True : uPred M end.
  Proof. uPred.unseal. by destruct mx. Qed.
  Lemma discrete_fun_validI {A} {B : A → ucmra} (g : discrete_fun B) :
    ✓ g ⊣⊢ ∀ i, ✓ g i.
  Proof. by uPred.unseal. Qed.

  Section gmap_cmra.
    Context `{Countable K} {A : cmra}.
    Implicit Types m : gmap K A.

    Lemma gmap_validI m : ✓ m ⊣⊢ ∀ i, ✓ (m !! i).
    Proof. by uPred.unseal. Qed.
    Lemma singleton_validI i x : ✓ ({[ i := x ]} : gmap K A) ⊣⊢ ✓ x.
    Proof.
      rewrite gmap_validI. apply: anti_symm.
      - rewrite (bi.forall_elim i) lookup_singleton option_validI. done.
      - apply bi.forall_intro=>j. destruct (decide (i = j)) as [<-|Hne].
        + rewrite lookup_singleton option_validI. done.
        + rewrite lookup_singleton_ne // option_validI.
          apply bi.True_intro.
    Qed.
  End gmap_cmra.

  Section csum_cmra.
  Context {A B : cmra}.
  Implicit Types a : A.
  Implicit Types b : B.

  Lemma csum_validI (x : csum A B) :
    ✓ x ⊣⊢ match x with
                      | Cinl a => ✓ a
                      | Cinr b => ✓ b
                      | CsumBot => False
                      end.
  Proof. uPred.unseal. by destruct x. Qed.
End csum_cmra.
End upred.


(* TODO : Import further properties from iris.base_logic.algebra if required. *)