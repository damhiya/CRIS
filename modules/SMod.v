Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Export AList.
Require Import Skeleton.
Require Import Any.
Require Import Translate.
Require Import PCM IPM.
Require Import HMod.

Set Implicit Arguments.

Module SModSem.
Section SMODSEM.

  Context `{Σ: GRA.t}.
  Variable stb: gname -> option fspec.

  Record t: Type := mk {
    fnsems: list (gname * fspecbody);
    initial_st: Any.t;
    initial_cond: iProp;
  }.

  Definition transl (tr: fspecbody -> (Any.t -> itree hmodE Any.t)) (ms: t): HModSem.t := {|
    HModSem.fnsems := List.map (fun '(fn, sb) => (fn, tr sb)) ms.(fnsems);
    HModSem.initial_st := ms.(initial_st);
    HModSem.initial_cond := ms.(initial_cond);
  |}.

  Definition to_hmod (ms: t): HModSem.t := transl (interp_sb_hp stb) ms.

End SMODSEM.
End SModSem.


Module SMod.
Section SMOD.

  Context `{Σ: GRA.t}.
  Variable stb: Sk.t -> gname -> option fspec.

  Record t: Type := mk {
    get_modsem: Sk.t -> SModSem.t;
    sk: Sk.t;
  }.

  Definition transl (tr: Sk.t -> fspecbody -> ( Any.t -> itree hmodE Any.t)) (md: t): HMod.t := {|
    HMod.get_modsem := fun sk => SModSem.transl (tr sk) (md.(get_modsem) sk);
    HMod.sk := md.(sk);
  |}.

  Definition to_hmod (md:t): HMod.t := transl (fun sk => (interp_sb_hp (stb sk))) md.
    
  Definition get_stb (mds: list t): Sk.t -> alist gname fspec :=
    fun sk => List.map (map_snd fsb_fspec) (flat_map (SModSem.fnsems ∘ (flip get_modsem sk)) mds).

  Definition get_sk (mds: list t): Sk.t :=
    Sk.sort (fold_right Sk.add Sk.unit (List.map sk mds)).

End SMOD.
End SMod.
