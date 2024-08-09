Require Import HoareDef MultHeader Mult0 Mult1 HPSim HPSimFacts.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Require Import STB ProofMode.
Require Import HPTactics.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section HPSIM.
  Context `{@GRA.inG fRA Σ}.
  Context `{@GRA.inG gRA Σ}.
  Context `{@GRA.inG hRA Σ}.

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Variable o: ord.

  Definition MultH0 := SMod.to_hmod (GlobalStb (Mult0.SMult.(SMod.sk))) o Mult0.SMult.
  Definition MultH1 := SMod.to_hmod (GlobalStb (Mult1.SMult.(SMod.sk))) o Mult1.SMult.

  Lemma test_hmod : HModR.sim MultH1 MultH0.
  Proof.
  econs; et. i. econs; cycle 1.
  { instantiate (1:= (fun _ _ => ⌜True⌝%I)). ss. rr. uipropall. }
  remember (HModSemPair.fl_src (HMod.get_modsem MultH1 sk)). clear Heqa.
  remember (HModSemPair.fl_tgt (HMod.get_modsem MultH0 sk)). clear Heqa0.
  econs.
  {
    econs; et. ii; clarify.
    unfold fun_spec_hp, body_spec_hp, interp_hEs_hAGEs. 
    grind.
    ginit. hsteps. unfold hpsim_end. et.  
  }
  econs.
  {
    econs; et. ii; clarify.
    grind. ginit.
    unfold ccallU. grind. unfold fun_spec_hp, body_spec_hp. hsteps.
    rewrite interp_hAGEs_bind. rewrite interp_hAGEs_call. 
    unfold handle_callE_hAGEs. grind.
    unfold unwrapN. des_ifs; hsteps.
    unfold HoareCall. hsteps. grind. { instantiate (1:= ⌜True⌝ ** ⌜Any.upcast Vundef = Any.upcast Vundef⌝). et. }
    hforce_l. hsteps. hforce_l. grind. hforce_l; et. i.
    hsteps; et.
    hforce_r. hforce_r; et. i. hsteps.
    unfold unwrapU. des_ifs; cycle 1.
    { rewrite interp_hAGEs_bind. grind. rewrite interp_hAGEs_triggerUB. hsteps. } 
    grind. rewrite interp_hAGEs_bind. rewrite interp_hAGEs_call.
    unfold handle_callE_hAGEs. grind.
    unfold unwrapN. des_ifs; hsteps.
    unfold HoareCall. hsteps; et.
    hforce_l. hsteps. hforce_l. hsteps. hforce_l; et. i. hsteps; et.
    hforce_r. hforce_r; et. i. hsteps. des_ifs; cycle 1.
    { rewrite interp_hAGEs_bind. grind. rewrite interp_hAGEs_triggerUB. hsteps. } 
    grind. rewrite interp_hAGEs_ret. hsteps.
  }
  econs; et.
  {
    econs; et. ii; clarify.
    grind. ginit.
    unfold fun_spec_hp, body_spec_hp.
    rewrite interp_hAGEs_bind.
    unfold interp_hEs_hAGEs. rewrite interp_trigger. grind.
    unfold HoareAPC. grind.
    hsteps. hforce_l. instantiate (1:= x).
    remember ε as fmr. rewrite Heqfmr in INV. clear Heqfmr.
    remember true. clear Heqb.
    revert fmr x st_src st_tgt b. gcofix CIH. i.
    rewrite !unfold_APC.
    hsteps. hforce_l. instantiate (1:= x0).
    destruct x0.
    { hsteps. et. }
    unfold guarantee. hsteps. hforce_l. hforce_l; et. hsteps. hforce_l. instantiate (1:= (s, t)). hsteps.
    unfold unwrapN. des_ifs; clarify. hsteps.
    unfold HoareCall. hsteps; et. hforce_l. hforce_l. hforce_l; et. i.
    hsteps; et. { instantiate (1:= ⌜True⌝%I). et. }
    hforce_r. hforce_r; et. i. hsteps.
    eapply hpsim_progress_flag.
    gfinal. left. eapply CIH.
  }

Qed.



End HPSIM.