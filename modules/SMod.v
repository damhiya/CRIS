Require Import Coqlib.
Require Import sflib.
Require Import ITreelib.
Require Import AList.
Require Import Skeleton.
Require Import Any.
Require Import PCM IPM.
Require Import Events HMod.
Require Export SMod2HMod.


Set Implicit Arguments.

Module SModSem.
Section SMODSEM.

  Context `{Σ: GRA.t}.
  Variable ginv: invspec.
  Variable stb: gname -> option fspec.

  Record t: Type := mk {
    scopes: list string;
    fnsems: alist gname (list string * fspecbody);
    initial_st: alist key Any.t;
    well_scoped_fns:
      forall fn, incl (fnsems_scopes fn fnsems) scopes;
    well_scoped_init:
      incl (List.map (fst ∘ fst) initial_st) scopes;
  }.

  Program Definition to_hmod (ms: t): HModSem.t := {|
    HModSem.scopes := ms.(scopes);
    HModSem.fnsems := List.map (map_snd (λ ksb, (ksb.1, interp_sb_hp ginv stb ksb.2))) ms.(fnsems);
    HModSem.initial_st := ms.(initial_st);
  |}.
  Next Obligation.
    i. destruct ms. ss. ii. unfold fnsems_scopes in *. unfold map_snd in*.
    rewrite alist_find_map in H. specialize (well_scoped_fns0 fn a).
    des_ifs; ss. inv Heq. eauto.
  Qed.
  Next Obligation.
    ii. destruct ms. ss. eauto.
  Qed.
  
End SMODSEM.
End SModSem.

Module SMod.
Section SMOD.

  Context `{Σ: GRA.t}.
  Variable ginv: Sk.t -> invspec.
  Variable stb: Sk.t -> gname -> option fspec.

  Record t: Type := mk {
    modsem: Sk.t -> SModSem.t;
    sk: Sk.t;
  }.

  Definition to_hmod (md:t): HMod.t := {|
    HMod.modsem := fun sk => SModSem.to_hmod (ginv sk) (stb sk) (md.(modsem) sk);
    HMod.sk := md.(sk);
 |}.
    
  (* Definition get_stb (mds: list t): Sk.t -> alist gname (list string * fspec) := *)
  (*   fun sk => List.map (map_snd (map_snd fsb_fspec)) (flat_map (SModSem.fnsems ∘ (flip modsem sk)) mds). *)

  (* Definition get_sk (mds: list t): Sk.t := *)
  (*   fold_right Sk.add Sk.unit (List.map sk mds). *)

End SMOD.
End SMod.
