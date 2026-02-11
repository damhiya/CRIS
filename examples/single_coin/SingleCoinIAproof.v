Require Import CRIS.
Require Import SingleCoinIPproof SingleCoinPAproof.

Module SingleCoinIA. Section SingleCoinIA.
  Context `{!crisG Γ Σ α β τ _S _I, !concGS, !prophGS, !coinGS}.
  Context (sp : specmap).

  Local Notation CoinI := (SingleCoinI.t).
  Local Notation CoinA := (SingleCoinA.t sp).
  Local Notation ProphA := (ProphecyA.t sp).

  (* Lemma ctxr (md : Mod.t) : refines (CoinA ★ md, emp%I) (CoinI ★ md, emp%I).
  Proof.
    etr
  Qed. *)
End SingleCoinIA. End SingleCoinIA.
