From CRIS.common Require Import Common ConcRA.
From CRIS.modules Require Import LMod Mod.

From CRIS.iris_system Require Import lib.allocs.
From iris.proofmode Require Import proofmode.

Definition refines_lmod (ms_tgt ms_src: LMod.t) : Prop :=
  Beh.of_itree (LMod.compile ms_tgt tt↑) <1=
  Beh.of_itree (LMod.compile ms_src tt↑).

Section CTX_REFINE.
  Context `{!crisG Γ Σ α β τ _S _I}.

  (* Definition of ctx refinement in Mod Level. *)
  Definition refines (mpt : Mod.modc) (mps : Mod.modc) : Prop :=
    let ms := mps.1 in let Ps := mps.2 in
    let mt := mpt.1 in let Pt := mpt.2 in

    ∀ (WFM : Mod.wf mt),
      Mod.wf ms /\
      ∀ rs
        (WFR : ✓ rs) (SRC : Own rs ⊢ |==> winv (∅,∅) ∗ Ps),
        ∃ rt,
          ✓ rt /\ (Own rt ⊢ |==> winv (∅,∅) ∗ Pt)%I /\
          refines_lmod
            (Mod.to_lmod mt rt)
            (Mod.to_lmod ms rs).

  Definition ctx_refines (mpt mps: Mod.modc) : Prop :=
    ∀ (ctx : Mod.modc),
      refines
        (mpt.1 ★ ctx.1, mpt.2 ∗ ctx.2)%I
        (mps.1 ★ ctx.1, mps.2 ∗ ctx.2)%I.
End CTX_REFINE.
Global Instance: Params (@ctx_refines) 1 := {}.
