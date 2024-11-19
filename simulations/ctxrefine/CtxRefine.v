Require Export Coqlib sflib Any.
Require Import Behavior.
Require Import Mod Skeleton ModSimFacts.
Require Import PCM IPM HMod ISimCore ISimFacts.
Require Import ModSim.


Section REFINE.

  Definition refines_modsem (ms_src ms_tgt: ModSem.t): Prop :=
    Beh.of_itree (ModSem.compile ms_tgt) <1=
    Beh.of_itree (ModSem.compile ms_src)
  .

End REFINE.

Section CTX_REFINE.
  (* Definition of ctx refinement in HMod Level. *)
  Context `{Σ : GRA.t}.

  Definition refines (mps : HMod.modc) (mpt : HMod.modc) : Prop :=
    let ms := mps.1 in let Ps := mps.2 in
    let mt := mpt.1 in let Pt := mpt.2 in

    <<EQV : Sk.equiv ms.(HMod.sk) mt.(HMod.sk)>> /\
    <<REF:
      forall sk (EQV : Sk.equiv mt.(HMod.sk) sk) (SKWF : Sk.wf sk)
        rs
        (WFR : ✓ rs) (SRC : Own rs ⊢ Ps sk) 
        (WFM : HModSem.wf (ms.(HMod.modsem) sk)),
      exists rt,
        ✓ rt /\ (Own rt ⊢ Pt sk)%I /\
        HModSem.wf (mt.(HMod.modsem) sk) /\
        refines_modsem
          (HModSem.to_mod (ms.(HMod.modsem) sk) rs)
          (HModSem.to_mod (mt.(HMod.modsem) sk) rt)>>.

  Definition ctx_refines (mps mpt : HMod.modc) : Prop :=
    forall (ctx : HMod.modc),
      refines (mps.1 ★ ctx.1, mps.2 ∗∗ ctx.2)
              (mpt.1 ★ ctx.1, mpt.2 ∗∗ ctx.2).

End CTX_REFINE.
