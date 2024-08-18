Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events STS.
Require Import Behavior.
Require Import SMod HMod.
Require Import Skeleton.
Require Import PCM.
Require Import STB IPM ITactics.
Require Import RingHeader.
Require Import CellHeader CellASpec.

Set Implicit Arguments.

Module CellA.
Section CELL_A.
  Context `{_W: CellRA.t}.  

  Variable idx : nat.

  Definition get : Any.t -> itree smodE Any.t := (fun _ => trigger (Choose _)).
  Definition set : Any.t -> itree smodE Any.t := (fun _ => trigger (Choose _)).
  
  Definition fnsems : alist string (list string * fspecbody) :=
    [(CellName.get idx, ([], mk_specbody (CellAS.get_spec idx) get));
     (CellName.set idx, ([], mk_specbody (CellAS.set_spec idx) set))].

  Program Definition Sem: SModSem.t := {|
    SModSem.fnsems := fnsems;
    SModSem.initial_st := [];
    SModSem.initial_cond := ∃ v, CellAS.cell idx v ∗ CellAS.auth idx v;
  |}
  .
  Next Obligation. prove_scope. Qed.

  Definition Mod: SMod.t := {|
    SMod.get_modsem := fun _ => Sem;
    SMod.sk := CellSK.t;
  |}
  .

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition t := Seal.sealing "ccr" (SMod.to_hmod GlobalStb Mod).

End CELL_A.
End CellA.
