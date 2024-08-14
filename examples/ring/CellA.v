Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events STS.
Require Import Behavior.
Require Import SMod HMod.
Require Import Skeleton.
Require Import PCM.
Require Import STB IPM.
Require Import RingHeader.
Require Import CellHeader CellASpec.

Set Implicit Arguments.

Module CellA.
Section CELL_A.
  Context `{_W: CellRA.t}.  

  Variable idx : nat.

  Definition init : Any.t -> itree smodE Any.t := (fun _ => trigger (Choose _)).
  Definition get : Any.t -> itree smodE Any.t := (fun _ => trigger (Choose _)).
  Definition set : Any.t -> itree smodE Any.t := (fun _ => trigger (Choose _)).
  
  Definition fnsems: list (string * fspecbody) :=
    [(CellName.init idx, mk_specbody (CellAS.init_spec idx) init);
     (CellName.get idx, mk_specbody (CellAS.get_spec idx) get);
     (CellName.set idx, mk_specbody (CellAS.set_spec idx) set)].

  Definition Sem: SModSem.t := {|
    SModSem.fnsems := fnsems;
    SModSem.initial_st := tt↑;
    SModSem.initial_cond := CellAS.cell idx 0 ∗ CellAS.auth idx 0;
  |}
  .

  Definition Mod: SMod.t := {|
    SMod.get_modsem := fun _ => Sem;
    SMod.sk := CellSK.t;
  |}
  .

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition _t: HMod.t := SMod.to_hmod GlobalStb Mod.
  Definition t := _t.

  Lemma unfold: t = _t.
  Proof. eauto. Qed.

  Global Opaque t.

End CELL_A.
End CellA.
