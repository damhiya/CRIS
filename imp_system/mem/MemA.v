Require Import CRIS.

Require Import ImpPrelude.
Require Import MemHeader.

From iris.algebra Require Import excl_auth functions.

Canonical Structure valO := leibnizO val.

(* Memory resource algebra *)
(* Coercion memGS >-> inG memRA Γ is global since it can be used in other modules *)
Definition memRA := authUR (mblock -d> Z -d> optionUR (exclR valO)).
Class memGΓ (Γ : HRA) := {
  #[global] mem_inG :: inG memRA Γ;
}.
Definition memΓ : HRA := #[memRA].
Global Instance subG_memΓ {Γ} : subG memΓ Γ → memGΓ Γ.
Proof. solve_inG. Qed.

Local Arguments Z.of_nat : simpl nomatch.

Section BODY.
  Context `{!sinvG Σ Γ α β τ, !memGΓ Γ}.
  Notation iProp := (iProp Σ).

  Definition mem_points_to_singleton_r (loc : mblock * Z) (v : val) : memRA :=
    ◯ (discrete_fun_singleton loc.1 (discrete_fun_singleton loc.2 (Some (Excl v)))).
  Definition mem_points_to_singleton (loc : mblock * Z) (v : val) : iProp :=
    own base_γ (mem_points_to_singleton_r loc v).
  Definition mem_points_to : (mblock * Z) → list val → iProp :=
    λ '(blk, ofs) vs, ([∗ list] i ↦ v ∈ vs, mem_points_to_singleton (blk, ofs + i)%Z v)%I.

  Definition mem_initial_mem_r (csl : string → bool) (sk : Sk.t) : memRA :=
    ● ((λ blk ofs,
        match List.nth_error sk blk with
        | Some (g, gd) =>
          match gd↓ with
          | Some (Gvar gv) => if csl g && (decide (ofs = 0)) then Some (Excl (Vint gv)) else ε
          | _ => ε
          end
        | _ => ε
        end) : mblock -d> Z -d> optionUR (exclR valO)).
  Definition mem_initial_mem (csl : string → bool) (sk : Sk.t) : iProp :=
    own base_γ (mem_initial_mem_r csl sk).
End BODY.

Notation "loc ⤇ v" := (mem_points_to_singleton loc v) (at level 20).
Notation "loc |-> vs" := (mem_points_to loc vs) (at level 20).

Section AUX.
  Context `{!sinvG Σ Γ α β τ, !memGΓ Γ}.

  Lemma points_to_nil ptr : ptr |-> [] = emp%I.
  Proof. destruct ptr. ss. Qed.
  
  Lemma points_to_disj ptr x0 x1 : ((ptr |-> [x0]) -∗ (ptr |-> [x1]) -∗ False).
  Proof.
    destruct ptr as [blk ofs].
    iIntros "[A _] [B _]". s. iCombine "A B" as "A" gives %wf.
    rewrite -auth_frag_op ?discrete_fun_singleton_op /= auth_frag_valid discrete_fun_singleton_valid
      discrete_fun_singleton_op discrete_fun_singleton_valid -Some_op // in wf.
  Qed.

  (* Fixpoint is_list (ll : val) (xs : list val) : iProp :=
    match xs with
    | [] => (⌜ll = Vnullptr⌝ : iProp)%I
    | xhd :: xtl =>
      (∃ lhd ltl, ⌜ll = Vptr lhd 0⌝ ∗ ((lhd,0%Z) |-> [xhd; ltl])
                             ∗ is_list ltl xtl : iProp)%I
    end
  .

  Lemma unfold_is_list : forall ll xs,
      is_list ll xs =
      match xs with
      | [] => (⌜ll = Vnullptr⌝ : iProp)%I
      | xhd :: xtl =>
        (∃ lhd ltl, ⌜ll = Vptr lhd 0⌝ ∗ ((lhd,0%Z) |-> [xhd; ltl])
                               ∗ is_list ltl xtl : iProp)%I
      end
  .
  Proof.
    i. destruct xs; auto.
  Qed.

  Lemma unfold_is_list_cons : forall ll xhd xtl,
      is_list ll (xhd :: xtl) =
      (∃ lhd ltl, ⌜ll = Vptr lhd 0⌝ ∗ ((lhd,0%Z) |-> [xhd; ltl])
                             ∗ is_list ltl xtl : iProp)%I.
  Proof.
    i. eapply unfold_is_list.
  Qed.

  Lemma is_list_wf
        ll xs
    :
      (is_list ll xs) -∗ (⌜(ll = Vnullptr) \/ (match ll with | Vptr _ 0 => True | _ => False end)⌝)
  .
  Proof.
    iIntros "H0". destruct xs; ss; et.
    { iPure "H0" as H0. iPureIntro. left. et. }
    iDestruct "H0" as (lhd ltl) "(H0 & H1 & H2)".
    iPure "H0" as H0. iPureIntro. right. subst. et.
  Qed. *)

  (* Global Opaque is_list. *)
End AUX.

(* Section POINTS_TO.
  Context `{@GRA.inG memRA Σ}.

  Definition PointsTo p v := p |-> [v].
  
  Lemma points_to_conv b ofs l:
    ((b,ofs) |-> l) -∗ [∗ list] i↦v ∈ l, PointsTo (b, ofs + i)%Z v.
  Proof.
    revert b ofs. induction l; eauto; i.
    rewrite points_to_split. s.
    iIntros "(H&T)". rewrite Z.add_0_r.
    iFrame. iPoseProof (IHl with "T") as "T". clear IHl.
    eapply eq_ind. { iApply "T". }
    f_equal. extensionalities i v. do 2 f_equal. nia.
  Qed.

  Lemma points_to_conv_r b ofs l:
    ([∗ list] i↦v ∈ l, PointsTo (b, ofs + i)%Z v) -∗ ((b,ofs) |-> l).
  Proof.
    revert b ofs. induction l; i.
    { s. rewrite points_to_nil. apply OwnM_unit. }
    rewrite points_to_split. s.
    iIntros "(H&T)". rewrite Z.add_0_r. 
    iFrame. iApply IHl. clear IHl.
    eapply eq_ind. { iApply "T". }
    f_equal. extensionalities x i. do 2 f_equal. nia.
  Qed.
  
End POINTS_TO. *)



Module MemA. Section MemA.
  Context `{!sinvG Σ Γ α β τ, !memGΓ Γ}.

  Definition scopes := ["Mem"].

  Definition alloc_spec : fspec :=
    fspec_simple
      (λ sz,
        (λ varg, (⌜varg = [Vint (Z.of_nat sz)]↑ ∧ (8 * (Z.of_nat sz) < modulus_64)%Z⌝),
          λ vret, (∃ b, (⌜vret = (Vptr b 0)↑⌝) ∗ (b, 0%Z) |-> (List.repeat Vundef sz))))%I.

  Definition free_spec : fspec :=
    fspec_simple
      (λ '(b, ofs),
        (λ varg, ∃ v, ⌜varg = [Vptr b ofs]↑⌝ ∗ (b, ofs) ⤇ v,
          λ vret, ⌜vret = (Vint 0)↑⌝))%I.

  Definition load_spec : fspec :=
    fspec_simple
      (λ '(b, ofs, v),
        (λ varg, ⌜varg = [Vptr b ofs]↑⌝ ∗ (b, ofs) ⤇ v,
          λ vret, (b, ofs) ⤇ v ∗ ⌜vret = v↑⌝))%I.

  Definition store_spec: fspec :=
    fspec_simple
      (λ '(b, ofs, v_new),
        (λ varg, ∃ v_old, ⌜varg = [Vptr b ofs; v_new]↑⌝ ∗ (b, ofs) ⤇ v_old,
          λ vret, (b, ofs) ⤇ v_new ∗ ⌜vret = (Vint 0)↑⌝))%I.

  (* Is this the best way to define cmp? (points_to is not resource anymore)*)
  Definition cmp_spec: fspec :=
    fspec_simple
      (λ '(ret, res),
        (λ varg,
          res
          ∗ (⌜ret = false⌝
            ∗ (∃ b ofs v, ⌜varg = [Vptr b ofs; Vnullptr]↑⌝ ∗ (res -∗ (b, ofs) ⤇ v)
              ∨ ∃ b ofs v, ⌜varg = [Vnullptr; Vptr b ofs]↑⌝ ∗ (res -∗ (b, ofs) ⤇ v)
              ∨ ∃ b0 b1 ofs0 ofs1 v0 v1, ⌜varg = [Vptr b0 ofs0; Vptr b1 ofs1]↑⌝
                ∗ (res -∗ (b0, ofs0) ⤇ v0 ∗ (b1, ofs1) ⤇ v1))
            ∨ ⌜ret = true⌝
              ∗ ∃ b ofs v, ⌜varg = [Vptr b ofs; Vptr b ofs]↑⌝ ∗ (res -∗ (b, ofs) ⤇ v)),
          λ vret, res ∗ ⌜vret = (if ret then Vint 1 else Vint 0)↑⌝))%I.

  Definition Stb : alist string fspec :=  
    Seal.sealing "ccr"
      [(MemName.alloc, alloc_spec);
       (MemName.free,  free_spec);
       (MemName.load,  load_spec);
       (MemName.store, store_spec);
       (MemName.cmp,   cmp_spec)].

  Definition fnsems : alist string (list string * fspecbody) :=
    [(MemName.alloc, ([], mk_specbody alloc_spec fbody_trivial));
     (MemName.free,  ([], mk_specbody free_spec fbody_trivial));
     (MemName.load,  ([], mk_specbody load_spec fbody_trivial));
     (MemName.store, ([], mk_specbody store_spec fbody_trivial));
     (MemName.cmp,   ([], mk_specbody cmp_spec fbody_trivial))].

  Variable csl : string → bool.

  Program Definition Sem : SModSem.t := {|
    SModSem.scopes := scopes;
    SModSem.fnsems := fnsems;
    SModSem.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod : SMod.t := {|
    SMod.modsem := λ _, Sem;
    SMod.sk := Sk.unit;
  |}.

  Definition InitCond : Sk.t → iProp Σ :=
    λ sk, mem_initial_mem csl sk.

  Variable ginv : Sk.t → invspec.
  Variable GlobalStb : Sk.t → string → option fspec.
  Definition t : HMod.t := Seal.sealing "ccr" (SMod.to_hmod ginv GlobalStb Mod).
End MemA. End MemA.

Global Opaque MemA.mem_points_to_singleton_r.

Global Notation "loc ⤇ v" := (MemA.mem_points_to_singleton loc v) (at level 20).
Global Notation "loc |-> vs" := (MemA.mem_points_to loc vs) (at level 20).
