Require Import Coqlib.
Require Import sflib.
Require Import ITreelib.
Require Import AList.
Require Import Behavior.
Require Import Events SMod HMod Mod.
Require Import SMod2HMod HMod2Mod.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Any.
Require Export STB.
Require Import ModSim.

Set Implicit Arguments.

(******* Rename each section into proper name  *******)


Module SModSemAux.
Section AUX.
  Import SModSem.
  Context `{Σ: GRA.t}.
  Variable ginv: invspec.
  Variable stb: gname -> option fspec.

  Program Definition to_hmod (ms: t): HModSem.t := {|
    HModSem.scopes := ms.(scopes);
    HModSem.fnsems := List.map (map_snd (λ ksb, (ksb.1, fsb_body ksb.2))) (ms.(fnsems));
    HModSem.initial_st := ms.(initial_st);
  |}.
  Next Obligation.
    i. destruct ms. ss. ii. unfold fnsems_scopes in *. unfold map_snd in*.
    rewrite! alist_find_map in H. specialize (well_scoped_fns0 fn a).
    des_ifs; ss. inv Heq. eauto.
  Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.

End AUX.
End SModSemAux.

Module SModAux.
Section AUX.
  Import SMod.
  Context `{Σ: GRA.t}.
  Variable ginv: Sk.t -> invspec.
  Variable stb: Sk.t -> gname -> option fspec.

  Definition to_hmod (md: t) := {|
    HMod.modsem := fun sk => SModSemAux.to_hmod (md.(modsem) sk);
    HMod.sk := md.(sk);
  |}.

End AUX.
End SModAux.

