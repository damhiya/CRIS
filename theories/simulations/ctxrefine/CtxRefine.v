Require Import Common.
Require Import Mod HMod.

Definition refines_mod (ms_src ms_tgt: Mod.t) : Prop :=
  Beh.of_itree (Mod.compile ms_tgt) <1=
  Beh.of_itree (Mod.compile ms_src).

Section CTX_REFINE.
  (* Definition of ctx refinement in HMod Level. *)
  Context `{Σ : GRA}.

  Definition refines (mps : HMod.modc) (mpt : HMod.modc) : Prop :=
    let ms := mps.1 in let Ps := mps.2 in
    let mt := mpt.1 in let Pt := mpt.2 in

    ∀ rs
      (WFR : ✓ rs) (SRC : Own rs ⊢ Ps)
      (WFM : HMod.wf ms),
    ∃ rt,
      ✓ rt /\ (Own rt ⊢ Pt)%I /\
      HMod.wf mt /\
      refines_mod
        (HMod.to_mod ms rs)
        (HMod.to_mod mt rt).

  Definition ctx_refines (mps mpt : HMod.modc) : Prop :=
    ∀ (ctx : HMod.modc),
      refines (mps.1 ★ ctx.1, mps.2 ∗ ctx.2)%I
              (mpt.1 ★ ctx.1, mpt.2 ∗ ctx.2)%I.
End CTX_REFINE.
Global Instance: Params (@ctx_refines) 1 := {}.
