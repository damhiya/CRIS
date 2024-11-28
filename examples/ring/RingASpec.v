Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events.
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

Module RingAS. Section RingAS.
  Context `{Σ : GRA.t}.

  Definition Stb : alist gname fspec :=
    Seal.sealing "RingAS" [(RingName.init, fspec_trivial);
                          (RingName.get_size, fspec_trivial);
                          (RingName.enqueue, fspec_trivial);
                          (RingName.dequeue, fspec_trivial)].

  Lemma Stb_nodup : List.NoDup (List.map fst Stb).
  Proof.
    unfold Stb. unseal "RingAS". prove_nodup.
  Qed.
  
End RingAS.

Global Hint Unfold Stb : stb.

End RingAS.
