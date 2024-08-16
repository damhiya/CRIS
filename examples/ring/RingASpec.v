Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events STS.
Require Import Behavior.
Require Import HMod SMod.
Require Import Skeleton.
Require Import PCM IPM STB.
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
    Seal.sealing "stb" [(RingName.init, fspec_trivial);
                        (RingName.get_size, fspec_trivial);
                        (RingName.enqueue, fspec_trivial);
                        (RingName.dequeue, fspec_trivial)].

End SPECS.

Global Hint Unfold Stb: stb.

End RingAS.

Module RingRA.
  Class t
    `{Σ: GRA.t}
    := RingRA: unit.
End RingRA.

