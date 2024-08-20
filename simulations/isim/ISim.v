Require Import Coqlib ITreelib sflib.
Require Import STS.
Require Import Events Behavior.
Require Import Mod.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Any.
Require Import STB ModSim.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
Require Import Red IRed.
Require Import HPSim.
Require Import World sWorld.
From stdpp Require Import coPset gmap.

Require Import HMod SMod.

Require Export ISimCore ITactics.

Set Implicit Arguments.

Section SPEC.
  Context `{_W: CtxWD.t}.

  Inductive meta_inv {X: positive -> nat -> Type} : Type :=
  | mk_meta (u: positive) (n: nat) (x: X u n).  

  Definition mk_fspec_inv (k: nat) (fsp: positive -> nat -> fspec): fspec :=
    @mk_fspec
      Σ
      (@meta_inv (fun u n => (fsp u n).(meta)))
      (fun '(mk_meta u n x) => (fsp u n).(measure) x)
      (fun '(mk_meta u n x) varg_src varg_tgt =>
         closed_world u (k+n) ⊤ ∗ (fsp u n).(precond) x varg_src varg_tgt)%I
      (fun '(mk_meta u n x) vret_src vret_tgt =>
         closed_world u (k+n) ⊤ ∗ (fsp u n).(postcond) x vret_src vret_tgt)%I.

  Definition fspec_trivial: fspec :=
    @mk_fspec 
      _
      (@meta_inv (fun _ _ => unit)) 
      (fun _ => ord_top) 
      (fun _ argh argl => (⌜argh = argl⌝: iProp)%I)
      (fun _ reth retl => (⌜reth = retl⌝: iProp)%I).

End SPEC.


Section LEMMAS.

(***** Move and rename: APC & HoareCall LEMMAS *****)

  (* Try to match bind pattern *)
  Lemma APC_start_clo Σ
    fls flt I r g ps pt {R} RR st_src k_src sti_tgt  
    at_most o stb 
  :
    @isim Σ fls flt I r g R RR true pt (st_src, _APC stb at_most o >>= (fun x => tau;; Ret x) >>= k_src) sti_tgt
  -∗  
    @isim _ fls flt I r g R RR ps pt (st_src, interp_smod stb o (trigger APC) >>= k_src) sti_tgt.
  Proof.
    unfold interp_smod. rewrite! interp_trigger. grind.
    destruct sti_tgt. unfold HoareAPC.
    iIntros "K".
    force_l. instantiate (1:= at_most).
    iApply "K".
  Qed.

  Lemma APC_stop_clo Σ
    fls flt I r g ps pt {R} RR st_src k_src sti_tgt  
    at_most o stb
  :
    @isim Σ fls flt I r g R RR true pt (st_src, k_src tt) sti_tgt
  -∗  
    @isim _ fls flt I r g R RR ps pt (st_src, _APC stb at_most o >>= (fun x => (tau;; Ret x) >>= k_src)) sti_tgt.
  Proof.
    destruct sti_tgt.
    iIntros "K".
    rewrite unfold_APC. 
    force_l. instantiate (1:= true). s. steps_l. iFrame.
  Qed.
  
  Lemma APC_step_clo Σ
    fls flt I r g ps pt {R} RR st_src k_src sti_tgt  
    at_most o stb next fn vargs fsp
    (SPEC: stb fn = Some fsp)
    (NEXT: (next < at_most)%ord)
  :
    @isim Σ fls flt I r g R RR true pt (st_src, HoareCall true o fsp fn vargs >>= (fun _ => _APC stb next o) >>= (fun x => tau;; Ret x) >>= k_src) sti_tgt
  -∗  
    @isim _ fls flt I r g R RR ps pt (st_src, _APC stb at_most o >>= (fun x => (tau;; Ret x) >>= k_src)) sti_tgt.
  Proof.
    destruct sti_tgt.
    iIntros "K". prep.
    iEval (rewrite unfold_APC).
    force_l. instantiate (1:= false). s.
    force_l. instantiate (1:= next).
    force_l. { eauto. }
    force_l. instantiate (1:= (fn, vargs)). s.
    rewrite SPEC. s. steps_l. grind.
  Qed.

  Lemma hcall_clo Σ
    fls flt I r g ps pt {R} RR st_src st_tgt k_src k_tgt
    fn varg_src varg_tgt o X (x: shelve__ X) (D: X -> ord) P Q
    (* PURE, ... *)
    (ORD: ord_lt (D x) o)
    (PURE: is_pure (D x))
  :
    (P x varg_src varg_tgt 
      ∗ I st_src st_tgt 
      ∗ (∀st_src0 st_tgt0 vret_src vret_tgt, 
             (Q x vret_src vret_tgt ∗ I st_src0 st_tgt0) 
          -∗ @isim Σ fls flt I r g R RR true true (st_src0, k_src vret_src) (st_tgt0, k_tgt vret_tgt)))
  -∗  
    @isim _ fls flt I r g R RR ps pt (st_src, HoareCall true o (mk_fspec D P Q) fn varg_src >>= k_src) (st_tgt, trigger (Call fn varg_tgt) >>= k_tgt).
  Proof.
    iIntros "(P & IST & K)".
    unfold HoareCall. prep.
    force_l. instantiate (1:= x).
    force_l. instantiate (1:= varg_tgt).
    force_l. iSplitL "P"; [eauto|]. 
    call; [eauto|].
    steps_l. iApply "K". iFrame.
  Qed.

End LEMMAS.
