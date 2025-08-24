Require Import Common.
Require Import LMod Mod.

Definition refines_lmod (ms_src ms_tgt: LMod.t) : Prop :=
  ∀ arg,
  Beh.of_itree (LMod.compile ms_tgt arg) <1=
  Beh.of_itree (LMod.compile ms_src arg).

Section CTX_REFINE.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  
  (* Definition of ctx refinement in Mod Level. *)

  Definition refines (mps : Mod.modc) (mpt : Mod.modc) : Prop :=
    let ms := mps.1 in let Ps := mps.2 in
    let mt := mpt.1 in let Pt := mpt.2 in

    ∀ (WFM : Mod.wf mt),
      Mod.wf ms /\
      ∀ rs
        (WFR : ✓ rs) (SRC : Own rs ⊢ |==> winv (∅,∅) ∗ Ps),
        ∃ rt,
          ✓ rt /\ (Own rt ⊢ |==> winv (∅,∅) ∗ Pt)%I /\
          refines_lmod
            (Mod.to_lmod ms rs)
            (Mod.to_lmod mt rt).

  Definition ctx_refines (mps mpt : Mod.modc) : Prop :=
    ∀ (ctx : Mod.modc),
      refines (mps.1 ★ ctx.1, mps.2 ∗ ctx.2)%I
              (mpt.1 ★ ctx.1, mpt.2 ∗ ctx.2)%I.
End CTX_REFINE.
Global Instance: Params (@ctx_refines) 1 := {}.
