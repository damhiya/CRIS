Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events.
Require Import Behavior.
Require Import HMod SMod.
Require Import Skeleton.
Require Import PCM IPM STB.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import ISim.
Require Import CannonHeader CannonASpec.
Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.
Set Implicit Arguments.

Module CannonMainAS.
Section Main.
  Import CannonAS.
  Context `{!Inv.t Σ Γ α β τ, !G Γ}.

  Definition main_spec: fspec :=
    fspec_simple (fun (_: unit) =>
        ((fun varg => (⌜varg = ([]: list val)↑⌝ ∗ Ball)%I),
        (fun vret => (⌜vret = tt↑⌝)%I))).

  Definition Stb: alist gname fspec :=
    Seal.sealing "ccr" [(MainName.main, main_spec)].

  Lemma Stb_nodup: List.NoDup (List.map fst Stb).
  Proof.
    unfold Stb. unseal "ccr". prove_nodup.
  Qed.

End Main.
End CannonMainAS.
