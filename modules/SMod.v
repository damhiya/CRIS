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
  Variable stb: gname -> option fspec.

  Record t: Type := mk {
    fnsems: alist gname (list string * fspecbody);
    initial_st: alist string Any.t;
    initial_cond: iProp;
    well_scoped:
      forall fn k (IN: In k (fnsems_keys fn fnsems)), 
          In k (List.map fst initial_st);
  }.

  Lemma transl_well_scoped (ms: t): forall fn k,
      In k (fnsems_keys (T:=Any.t -> itree hmodE Any.t) fn
           (List.map (λ '(fn0, kv), (fn0, (fst kv, interp_sb_hp stb (snd kv)))) (fnsems ms)))
    → In k (List.map fst (initial_st ms)).
  Proof.
    destruct ms. ss. i. unfold fnsems_keys in *.
    rewrite alist_find_map in H. specialize (well_scoped0 fn k).
    destruct (alist_find fn fnsems0); ss.
    destruct p; ss. eauto.
  Qed.

  Definition to_hmod (ms: t): HModSem.t := {|
    HModSem.fnsems := List.map (map_snd (λ ksb, (ksb.1, interp_sb_hp stb ksb.2))) ms.(fnsems);
    HModSem.initial_st := ms.(initial_st);
    HModSem.initial_cond := ms.(initial_cond);
    HModSem.well_scoped := transl_well_scoped ms
  |}.

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

  Definition to_hmod (md:t): HMod.t := {|
    HMod.get_modsem := fun sk => SModSem.to_hmod (stb sk) (md.(get_modsem) sk);
    HMod.sk := md.(sk);
 |}.
    
  Definition get_stb (mds: list t): Sk.t -> alist gname (list string * fspec) :=
    fun sk => List.map (map_snd (map_snd fsb_fspec)) (flat_map (SModSem.fnsems ∘ (flip get_modsem sk)) mds).

  Definition get_sk (mds: list t): Sk.t :=
    Sk.sort (fold_right Sk.add Sk.unit (List.map sk mds)).

End SMOD.
End SMod.
