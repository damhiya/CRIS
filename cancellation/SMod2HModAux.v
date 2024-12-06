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

Section AUX.
  Context `{Σ: GRA.t}.
  Notation iProp := (iProp Σ).

  Variable ginv : invspec.
  (* Variable stb: gname -> option fspec. *)
  
  Definition Spawn_Cancel (fn: gname) (varg: Any.t) : itree hmodE nat :=
    tid <- trigger (Spawn fn varg);;
    trigger (Yield tid);;;
    Ret tid.

  Definition handle_schE_hmodE_aux : schE ~> itree hmodE :=
    fun _ e =>
      match e in schE T return itree hmodE T with
      | Spawn fn varg =>
          Spawn_Cancel fn varg
      | Yield tid =>
          trigger (Yield tid)
      | Tid => trigger Tid
      end.

  Definition interp_smod_aux R (it : itree hmodE R) : itree hmodE R :=
    interp (case_ (bif:=sum1) trivial_Handler
           (case_ (bif:=sum1) handle_schE_hmodE_aux
           (case_ (bif:=sum1) trivial_Handler
            trivial_Handler))) it.

  Definition interp_sb_hp_aux (sb: fspecbody): Any.t -> itree hmodE Any.t :=
    fun arg =>
      interp_smod_aux (sb.(fsb_body) arg).

End AUX.

Module SModSemAux.
Section AUX.
  Import SModSem.
  Context `{Σ: GRA.t}.
  Variable ginv: invspec.
  Variable stb: gname -> option fspec.

  Program Definition to_hmod (ms: t): HModSem.t := {|
    HModSem.scopes := ms.(scopes);
    HModSem.fnsems := List.map (map_snd (λ ksb, (ksb.1, interp_sb_hp_aux ksb.2))) (ms.(fnsems));
    (* HModSem.fnsems := List.map (map_snd (λ ksb, (ksb.1, fsb_body ksb.2))) (ms.(fnsems)); *)
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

