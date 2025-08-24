From CRIS Require Import CRIS MemHeader.
From iris.algebra Require Import auth excl agree csum functions dfrac_agree.
Set Implicit Arguments.

(* Memory resource algebra *)
Section MemRA.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Canonical Structure valO := leibnizO val.
  Definition frac_valO := dfrac_agreeR valO.
  Definition _memRA := (mblock -d> Z -d> optionUR frac_valO).
  Definition memRA := authUR _memRA.
  Class memG `{!crisG Γ Σ α β τ _S _I} := {
    mem_inG :: inG memRA Γ;
  }.
  Definition memΓ : HRA := #[memRA].
  Global Instance subG_memG : subG memΓ Γ → memG.
  Proof. solve_inG. Defined.
End MemRA.
Hint Unfold subG_memG mem_inG : GRA_index.

Section MEM.
  Context `{!crisG Γ Σ α β τ _S _I, !memG}.

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
        | Some gv => Some (to_frac_agree 1 (Vint gv))
        | _ => ε
        end) : _memRA).

  Definition mem_init_frag_r (csl : string → bool) (genv : GEnv.t) : memRA :=
    ◯ ((λ blk ofs,
        match mem_init_val csl genv blk ofs with
        | Some gv => Some (to_frac_agree 1 (Vint gv))
        | _ => ε
        end) : _memRA).

  Definition mem_init_auth csl genv : iProp Σ :=
    own base_γ (mem_init_auth_r csl genv).

  Definition mem_init_frag csl genv : iProp Σ :=
    own base_γ (mem_init_auth_r csl genv).

  Definition mem_init csl genv : iProp Σ :=
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

End MEM.

Local Arguments Z.of_nat : simpl nomatch.

Section MemRA.
  Context `{!crisG Γ Σ α β τ _S _I, !memG}.

  Definition mem_val : Type := Qp * val.

  Definition _points_to_r (loc : mblock * Z) (q: Qp) (mvs : list val): _memRA :=
    let (b, ofs) := loc in
    fun _b _ofs =>
      if (dec _b b) && ((ofs <=? _ofs) && (_ofs <? (ofs + Z.of_nat (List.length mvs))))%Z
      then match (List.nth_error mvs (Z.to_nat (_ofs - ofs))) with
        | Some v => Some (to_frac_agree q v)
        | None => ε
        end
      else ε.

  Definition mem_points_to_singleton_r (loc : mblock * Z) (q: Qp) (v : val) : memRA :=
    ◯ (discrete_fun_singleton loc.1 (discrete_fun_singleton loc.2 (Some (to_frac_agree q v)))).
  Definition mem_points_to_singleton (loc : mblock * Z) (q: Qp) (v : val) : iProp Σ :=
    own base_γ ((mem_points_to_singleton_r loc q v): memRA).
  Definition mem_points_to : (mblock * Z) → Qp → list val → iProp Σ :=
    λ '(blk, ofs) q vs, ([∗ list] i ↦ v ∈ vs, mem_points_to_singleton (blk, ofs + i)%Z q v)%I.

  Lemma mem_init_auth_r_valid (csl : string → bool) (genv : GEnv.t) blk ofs v :
    mem_init_val csl genv blk ofs = Some v →
    mem_points_to_singleton_r (blk, ofs) 1 (Vint v) ≼ mem_init_frag_r csl genv.
  Proof.
    intros H'. rewrite /mem_init_auth_r /mem_points_to_singleton_r /mem_init_val; ss.
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

Notation "loc '↦{' q '}' v" := (mem_points_to_singleton loc q v) (at level 20).
Notation "loc ↦ v" := (mem_points_to_singleton loc 1 v) (at level 20).
Notation "loc ↦ v" := (<own> base_γ (mem_points_to_singleton_r loc 1 v))%SAT (at level 20) : SAT_scope.
Notation "loc |-> vs" := (mem_points_to loc 1 vs) (at level 20).

Global Opaque mem_points_to_singleton_r.
Arguments mem_points_to_singleton_r : simpl never.

Module MemSpec. Section MemSpec.
  Context `{!crisG Γ Σ α β τ _S _I, !memG}.

  Definition alloc :=
    (make_fspecS (λ sz,
       (λ arg, ⌜arg = [Vint (Z.of_nat sz)]↑ /\ (8 * (Z.of_nat sz) < modulus_64)%Z⌝,
        λ ret, ∃ b, ⌜ret = (Vptr (b, 0%Z))↑⌝ ∗ (b, 0%Z) |-> List.repeat Vundef sz)))%I.

  Definition free :=
    (make_fspecS (λ '(b, ofs, v),
       (λ arg, ⌜arg = [Vptr (b, ofs)]↑⌝ ∗ (b, ofs) ↦ v,
        λ ret, ⌜ret = (Vint 0)↑⌝)))%I.

  Definition load :=
    (make_fspecS (λ '(b, ofs, q, v),
       (λ arg, ⌜arg = [Vptr (b, ofs)]↑⌝ ∗ (b, ofs) ↦{q} v,
        λ ret, (b, ofs) ↦{q} v ∗ ⌜ret = v↑⌝)))%I.

  Definition store :=
    (make_fspecS (λ '(b, ofs, v_old, v_new),
       (λ arg, ⌜arg = [Vptr (b, ofs) ; v_new]↑⌝ ∗ (b, ofs) ↦ v_old,
        λ ret, (b, ofs) ↦ v_new ∗ ⌜ret = (Vint 0)↑⌝)))%I.

  Definition val_r (arg : val) q v : iProp Σ :=
    match arg with
    | Vptr (b, ofs) => (b, ofs) ↦{q} v
    | _ => True%I
    end.

  Definition compare_val (v0 v1: val) : val :=
    match v0, v1 with
    | Vint i0, Vint i1 => Vint (if dec i0 i1 then 1 else 0)
    | Vint 0, Vptr _ => Vint 0
    | Vptr _, Vint 0 => Vint 0
    | Vptr (b0,ofs0), Vptr (b1,ofs1) =>
       if dec b0 b1 && dec ofs0 ofs1 then Vint 1 else Vint 0
    | _, _ => Vundef
    end.

  Definition cmp :=
    (make_fspecS (λ '(arg0, q0, v0, arg1, q1, v1, succ),
      (λ arg,
        ⌜arg = [arg0; arg1]↑ ∧ compare_val arg0 arg1 = Vint succ⌝ ∗
        val_r arg0 q0 v0 ∗ val_r arg1 q1 v1,
       λ ret, ⌜ret = (Vint succ)↑⌝ ∗
        val_r arg0 q0 v0 ∗ val_r arg1 q1 v1)))%I.

  Definition cas : fspecS :=
    (make_fspecS (λ '(b, ofs, v_cur, q0, v0, v_old, q1, v1, v_new, succ),
      (λ arg, ⌜arg = [Vptr (b, ofs); v_old; v_new]↑ ∧ compare_val v_cur v_old = Vint succ⌝ ∗
        (b, ofs) ↦ v_cur ∗ val_r v_cur q0 v0 ∗ val_r v_old q1 v1,
       λ ret, ⌜ret = v_cur↑⌝ ∗
        (b, ofs) ↦ (if dec succ 1 then v_new else v_cur) ∗
        val_r v_cur q0 v0 ∗ val_r v_old q1 v1)))%I.
End MemSpec. End MemSpec.

Module MemA. Section MemA.
  Context `{!crisG Γ Σ α β τ _S _I, !memG}.

  Definition scopes := ["Mem"].

  Definition sp : alist (option string) (option fspec) :=
    Seal.sealing CRIS
      [(Some MemHdr.alloc, Some (to_fspec MemSpec.alloc));
       (Some MemHdr.free,  Some (to_fspec MemSpec.free));
       (Some MemHdr.load,  Some (to_fspec MemSpec.load));
       (Some MemHdr.store, Some (to_fspec MemSpec.store));
       (Some MemHdr.cmp,   Some (to_fspec MemSpec.cmp));
       (Some MemHdr.cas,   Some (to_fspec MemSpec.cas))].

  Definition fnsems : alist (option string) (fnsem_type (option fspec * fbody)) :=
    [(Some MemHdr.alloc, (true, wmask_all, scopes, (Some (to_fspec MemSpec.alloc), fbody_trivial)));
     (Some MemHdr.free,  (true, wmask_all, scopes, (Some (to_fspec MemSpec.free), fbody_trivial)));
     (Some MemHdr.load,  (true, wmask_all, scopes, (Some (to_fspec MemSpec.load), fbody_trivial)));
     (Some MemHdr.store, (true, wmask_all, scopes, (Some (to_fspec MemSpec.store), fbody_trivial)));
     (Some MemHdr.cmp,   (true, wmask_all, scopes, (Some (to_fspec MemSpec.cmp), fbody_trivial)));
     (Some MemHdr.cas,   (true, wmask_all, scopes, (Some (to_fspec MemSpec.cas), fbody_trivial)))].

  (* Module definition *)
  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond csl genv : iProp Σ := mem_init_auth csl genv.

  Definition t := Seal.sealing CRIS (SMod.to_mod sp_none smod).
End MemA. End MemA.
