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
Require Import ISim.
Require Import CannonHeader.
Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.
Set Implicit Arguments.

Module CannonAS.
Section Cannon.
  Context `{_W: CtxWD.t}.

  Global Instance RA: URA.t := Auth.t (Excl.t unit).
  Context `{@GRA.inG RA Γ}.

  Definition Ready: RA := Auth.black (M:=(Excl.t _)) (Some tt).
  Definition Ball: RA := Auth.white (M:=(Excl.t _)) (Some tt).
  Definition Fired: RA := Auth.excl (M:=(Excl.t _)) (Some tt) (Some tt).

  Lemma ReadyBall: Ready ⋅ Ball = Fired.
  Proof. ur. rewrite URA.unit_idl. ss. Qed.

  Lemma FiredReady: ~ URA.wf (Fired ⋅ Ready).
  Proof. ur. ss. Qed.

  Lemma FiredBall: ~ URA.wf (Fired ⋅ Ball).
  Proof. ur. ii. des. ur in H0. red in H0. des. ur in H0. des_ifs. Qed.

  Lemma BallReady_wf: URA.wf (Ball ⋅ Ready).
  Proof.
    ur. split.
    { eexists. rewrite ! URA.unit_id. ss. }
    { ur. ss. }
  Qed.

  Definition fire_spec: fspec :=
      mk_simple (fun (_: unit) =>
          (ord_top,
            (fun varg => (⌜varg = ([]: list val)↑⌝ ∗ (OwnM (Ball)))%I),
            (fun vret => (⌜vret = (1: Z)%Z↑⌝)%I))).

  Definition Stb: alist gname fspec :=
    Seal.sealing "ccr" [(CannonName.fire, fire_spec)].

  Lemma Stb_nodup: List.NoDup (List.map fst Stb).
  Proof.
    unfold Stb. unseal "ccr". prove_nodup.
  Qed.

End Cannon.
End CannonAS.

Module CannonAR.
  Class t
    `{@GRA.inG CannonAS.RA Γ}
    := CannonARes: unit.

End CannonAR.