Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events STS.
Require Import Behavior.
Require Import HMod SMod.
Require Import Skeleton.
Require Import PCM IPM STB ITactics.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import RingHeader.

Set Implicit Arguments.

Module RingAS.
Section SPECS.
  Context `{Σ: GRA.t}.

  Definition Stb: alist gname fspec :=
    Seal.sealing "ccr" [(RingName.init, fspec_trivial);
                        (RingName.get_size, fspec_trivial);
                        (RingName.enqueue, fspec_trivial);
                        (RingName.dequeue, fspec_trivial)].

  Lemma Stb_nodup: List.NoDup (List.map fst Stb).
  Proof.
    unfold Stb. unseal "ccr". prove_nodup.
  Qed.
  

End SPECS.

Global Hint Unfold Stb: stb.

End RingAS.

Module RingRA.
  Class t
    `{Σ: GRA.t}
    := RingRA: unit.
End RingRA.

