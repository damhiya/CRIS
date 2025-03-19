Require Import sProp.
Require Import CRIS.
Require Import MemHeader.
Set Implicit Arguments.

(* Memory resource algebra *)
(* Coercion memGS >-> inG memRA Γ is global since it can be used in other modules *)
Canonical Structure valO := leibnizO val.
Definition frac_valO := prodR fracR (exclR valO).
Definition _memRA := (mblock -d> Z -d> optionUR frac_valO).
Definition memRA := authUR _memRA.
Class memGΓ (Γ : HRA) := {
  #[global] mem_inG :: inG memRA Γ;
}.
Definition memΓ : HRA := #[memRA].
Global Instance subG_memΓ {Γ: HRA} : subG memΓ Γ → memGΓ Γ.
Proof. solve_inG. Defined.
Hint Unfold subG_memΓ mem_inG : GRA_index.

(* Initial resources for memory *)
Definition mem_init_val (csl : string → bool) genv blk ofs : option Z :=
  match List.nth_error genv blk with
  | Some (g, gd) =>
    match gd↓ with
    | Some (Gvar gv) => if negb (csl g) && (decide (ofs = 0%Z)) then Some gv else None
    | _ => None
    end
  | None => None
  end.

Definition mem_init_auth_r (csl : string → bool) (genv: GEnv.t) : memRA :=
  ● ((λ blk ofs,
      match mem_init_val csl genv blk ofs with
      | Some gv => Some (1%Qp, Excl (Vint gv))
      | _ => ε
      end) : _memRA).

Definition mem_init_frag_r (csl : string → bool) (genv : GEnv.t) : memRA :=
  ◯ ((λ blk ofs,
      match mem_init_val csl genv blk ofs with
      | Some gv => Some (1%Qp, Excl (Vint gv))
      | _ => ε
      end) : _memRA).

Definition mem_init_auth csl genv `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !memGΓ Γ} : iProp Σ :=
  own base_γ (mem_init_auth_r csl genv).

Definition mem_init_frag csl genv `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !memGΓ Γ} : iProp Σ :=
  own base_γ (mem_init_auth_r csl genv).

Definition mem_init csl genv `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !memGΓ Γ} : iProp Σ :=
  own base_γ (mem_init_auth_r csl genv ⋅ mem_init_frag_r csl genv).

Lemma mem_init_valid (csl : string → bool) (genv : GEnv.t) :
  ✓ (mem_init_auth_r csl genv ⋅ mem_init_frag_r csl genv).
Proof. rewrite /mem_init_auth_r /mem_init_frag_r auth_both_valid_discrete; split; ii; des_ifs. Qed.

Definition ir_memRA csl genv : DRA_mk memRA :=
  mem_init_auth_r csl genv ⋅ mem_init_frag_r csl genv.
Lemma ir_memRA_valid csl genv : ✓ (ir_memRA csl genv).
Proof. pose proof (mem_init_valid csl genv). rewrite /ir_memRA //. Qed.

Definition ir_memΓ csl genv : memΓ :=
  *[Some (ir_memRA csl genv)].

Local Arguments Z.of_nat : simpl nomatch.

Section MemRA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !memGΓ Γ}.
  Notation iProp := (iProp Σ).

  Definition mem_val : Type := Qp * val.

  Definition _points_to_r (loc : mblock * Z) (q: Qp) (mvs : list val): _memRA :=
    let (b, ofs) := loc in 
    fun _b _ofs => 
      if (dec _b b) && ((ofs <=? _ofs) && (_ofs <? (ofs + Z.of_nat (List.length mvs))))%Z 
      then match (List.nth_error mvs (Z.to_nat (_ofs - ofs))) with
        | Some v => Some (q, Excl v)
        | None => ε
        end
      else ε
  .

  Definition mem_points_to_singleton_r (loc : mblock * Z) (q: Qp) (v : val) : memRA :=
    ◯ (discrete_fun_singleton loc.1 (discrete_fun_singleton loc.2 (Some (q, Excl v)))).
  Definition mem_points_to_singleton (loc : mblock * Z) (q: Qp) (v : val) : iProp :=
    own base_γ ((mem_points_to_singleton_r loc q v): memRA).
  Definition mem_points_to : (mblock * Z) → Qp → list val → iProp :=
    λ '(blk, ofs) q vs, ([∗ list] i ↦ v ∈ vs, mem_points_to_singleton (blk, ofs + i)%Z q v)%I.

  Lemma mem_init_auth_r_valid (csl : string → bool) (genv : GEnv.t) blk ofs v :
    mem_init_val csl genv blk ofs = Some v →
    mem_points_to_singleton_r (blk, ofs) 1 (Vint v) ≼ mem_init_frag_r csl genv.
  Proof.
    intros H. rewrite /mem_init_auth_r /mem_points_to_singleton_r /mem_init_val; ss.
    rewrite /mem_init_frag_r. apply auth_frag_mono.
    match goal with
    | |- _ ≼ ?f' => remember f' as f
    end.
    exists ((λ blk' ofs', if (decide (blk = blk' ∧ ofs = ofs')) then ε else (f blk' ofs'))).
    intros b o; clarify; rewrite ?discrete_fun_lookup_op; des_ifs; des; clarify.
    { rewrite right_id !discrete_fun_lookup_singleton //. }
    { apply not_and_or in n; des; bsimpl; des; ss; subst; ss.
      { rewrite !discrete_fun_lookup_singleton_ne; et. }
      { destruct (dec b blk); subst; ss.
        { rewrite discrete_fun_lookup_singleton discrete_fun_lookup_singleton_ne; et. }
        { rewrite !discrete_fun_lookup_singleton_ne; et. }
      }
    }
    { apply not_and_or in n; des; bsimpl; des; ss; subst; ss.
      { rewrite !discrete_fun_lookup_singleton_ne; et. }
      { destruct (dec b blk); subst; ss.
        { rewrite discrete_fun_lookup_singleton discrete_fun_lookup_singleton_ne; et. }
        { rewrite !discrete_fun_lookup_singleton_ne; et. }
      }
    }
  Qed.
End MemRA.

Notation "loc '|={' q '}=>' v" := (mem_points_to_singleton loc q v) (at level 20).
Notation "loc ↦ v" := (mem_points_to_singleton loc 1 v) (at level 20).
Notation "loc ↦ v" := (<own> base_γ (mem_points_to_singleton_r loc 1 v))%SRF (at level 20) : SRF_scope.
Notation "loc |-> vs" := (mem_points_to loc 1 vs) (at level 20).

Module MemA. Section MemA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !memGΓ Γ}.
  Notation iProp := (iProp Σ).

  Definition scopes := ["Mem"].

  (* Function specifications *)
  Definition alloc_spec: fspec :=
      (fspec_simple (fun sz => (
                      (fun varg => (⌜varg = [Vint (Z.of_nat sz)]↑ /\ (8 * (Z.of_nat sz) < modulus_64)%Z⌝: iProp)),
                      (fun vret => (∃ b, (⌜vret = (Vptr b 0)↑⌝)
                                          ∗ (b, 0%Z) |-> (List.repeat Vundef sz)): iProp)
      )))%I.

  Definition free_spec: fspec :=
      (fspec_simple (fun '(b, ofs) => (
                      (fun varg => (∃ v, (⌜varg = [Vptr b ofs]↑⌝) ∗ (b, ofs) ↦ v)),
                      (fun vret => ⌜vret = (Vint 0)↑⌝)
      )))%I.

  Definition load_spec: fspec :=
      (fspec_simple (fun '(b, ofs, v, q) => (
                      (fun varg => (⌜varg = [Vptr b ofs]↑⌝) ∗ (b, ofs) |={q}=> v),
                      (fun vret => (b, ofs) |={q}=> v ∗ ⌜vret = v↑⌝)
      )))%I.

  Definition store_spec: fspec :=
      (fspec_simple
        (fun '(b, ofs, v_new) => (
              (fun varg => (∃ v_old, (⌜varg = [Vptr b ofs ; v_new]↑⌝) ∗ (b, ofs) ↦ v_old)),
              (fun vret => (b, ofs) ↦ v_new ∗ ⌜vret = (Vint 0)↑⌝)
      )))%I.

  Definition cmp_spec0: fspec :=
      (fspec_simple
        (fun '(b, ofs, v, q) => (
              (fun varg => (⌜varg = [Vptr b ofs; Vnullptr]↑⌝ ∗ (b, ofs) |={q}=> v)),
              (fun vret => ((b, ofs) |={q}=> v) ∗ ⌜vret = (Vint 0)↑⌝)
      )))%I.

  Definition cmp_spec1: fspec :=
      (fspec_simple
          (fun '(b, ofs, v, q) => (
              (fun varg => (⌜varg = [Vnullptr; Vptr b ofs]↑⌝ ∗ (b, ofs) |={q}=> v)),
              (fun vret => ((b, ofs) |={q}=> v) ∗ ⌜vret = (Vint 0)↑⌝)
      )))%I.
  
  Definition cmp_spec2: fspec :=
      (fspec_simple
          (fun '(b0, ofs0, v0, q0, b1, ofs1, v1, q1) => (
              (fun varg => (⌜varg = [Vptr b0 ofs0; Vptr b1 ofs1]↑ ∧ (b0 <> b1 ∨ ofs0 <> ofs1)⌝ ∗ (b0, ofs0) |={q0}=> v0 ∗ (b1, ofs1) |={q1}=> v1)),
              (fun vret => (b0, ofs0) |={q0}=> v0 ∗ (b1, ofs1) |={q1}=> v1 ∗ ⌜vret = (Vint 0)↑⌝)
      )))%I.

  Definition cmp_spec3: fspec :=
      (fspec_simple
          (fun '(b, ofs, v, q) => (
              (fun varg => (⌜varg = [Vptr b ofs; Vptr b ofs]↑⌝ ∗ (b, ofs) |={q}=> v)),
              (fun vret => (b, ofs) |={q}=> v ∗ ⌜vret = (Vint 1)↑⌝)
      )))%I.

  Definition cmp_spec4: fspec :=
      (fspec_simple
          (fun (_: unit) => (
              (fun varg => (⌜varg = [Vnullptr; Vnullptr]↑⌝)),
              (fun vret => ⌜vret = (Vint 1)↑⌝)
      )))%I.

  Definition cmp_spec: fspec :=
    app_fspec [cmp_spec0; cmp_spec1; cmp_spec2; cmp_spec3; cmp_spec4].
  
  Definition cas_spec0 : fspec :=
      (fspec_simple (fun '(b, ofs, v_old, v_new) => (
                      (fun varg => (⌜varg = [Vptr b ofs; v_old; v_new]↑⌝) ∗ (b, ofs) ↦ v_old),
                      (fun vret => ((b, ofs) ↦ v_new ∗ ⌜vret = (Vint 1)↑⌝))
      )))%I.

  Definition cas_spec1 : fspec :=
      (fspec_simple (fun '(b, ofs, v_old, v_new, v_real) => (
                      (fun varg => (⌜varg = [Vptr b ofs; v_old; v_new]↑ ∧ v_old <> v_real⌝ ∗ (b, ofs) ↦ v_real)),
                      (fun vret => ((b, ofs) ↦ v_real ∗ ⌜vret = (Vint 0)↑⌝))
      )))%I.

  Definition cas_spec : fspec := app_fspec [cas_spec0; cas_spec1].

  Definition spc : alist string fspec :=  
    Seal.sealing CRIS
      [(MemName.alloc, alloc_spec);
       (MemName.free,  free_spec);
       (MemName.load,  load_spec);
       (MemName.store, store_spec);
       (MemName.cmp,   cmp_spec);
       (MemName.cas,   cas_spec)].

  Definition fnsems : alist string (list string * fspecbody ):=
    [(MemName.alloc, (scopes, mk_specbody alloc_spec  fbody_trivial));
     (MemName.free,  (scopes, mk_specbody free_spec   fbody_trivial));
     (MemName.load,  (scopes, mk_specbody load_spec   fbody_trivial));
     (MemName.store, (scopes, mk_specbody store_spec  fbody_trivial));
     (MemName.cmp,   (scopes, mk_specbody cmp_spec    fbody_trivial));
     (MemName.cas,   (scopes, mk_specbody cas_spec    fbody_trivial))].

  (* Module definition *)
  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond csl genv : iProp := mem_init_auth csl genv.

  Definition t u Spc := Seal.sealing CRIS (SMod.to_hmod (wsim_ginv u ⊤) Spc Mod).
End MemA. End MemA.
Global Opaque mem_points_to_singleton_r.
Arguments mem_points_to_singleton_r : simpl never.