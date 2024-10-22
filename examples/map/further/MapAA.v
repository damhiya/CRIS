Require Import Coqlib ITreelib sflib.
Require Import ImpPrelude.
Require Import Events STS.
Require Import Behavior.
Require Import SMod HMod.
Require Import Skeleton.
Require Import PCM.
Require Import STB IPM ITactics.
Require Import MapHeader MapASpec MapMSpec.
Require Import sProp sWorld World SRF.

Set Implicit Arguments.

Module MapAA.
Section AA.
  Context `{_W : CtxWD.t}.
  Context `{_A : MapAR.t (Γ:=Γ)}.
  Context `{_M : MapMR.t (Γ:=Γ)}.

  Definition scopes := ["Map"].
  
  Definition set_by_user : list val -> itree smodE val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      v <- trigger (IO "input" ([] : list Z));;
      ccallU MapName.set [Vint k; Vint v]
  .

  Definition fnsems :=
    [(MapName.init, (scopes, mk_specbody MapAS.init_spec fbody_trivial));
     (MapName.get, (scopes,mk_specbody MapAS.get_spec fbody_trivial));
     (MapName.set, (scopes,mk_specbody MapAS.set_spec fbody_trivial));
     (MapName.set_by_user, (scopes, mk_specbody MapAS.set_by_user_spec (cfunU set_by_user)))].

  Program Definition Sem : SModSem.t := {|
    SModSem.scopes := scopes;
    SModSem.fnsems := fnsems;
    SModSem.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod : SMod.t := {|
    SMod.modsem := fun _ => Sem;
    SMod.sk := MapSK.t;
  |}
  .

  Definition InitCond : Sk.t -> iProp :=
    fun _ => emp%I.

  Variable ginv : Sk.t -> invspec.
  Variable GlobalStb : Sk.t -> gname -> option fspec.
  Definition t := Seal.sealing "ccr" (SMod.to_hmod ginv GlobalStb Mod).

End AA.
End MapAA.
