Require Import Coqlib sflib ITreelib.
Require Import STS.
Require Import Behavior.
Require Import Mod HMod.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Any.
Require Import Events STB ModSim.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
Require Import Red IRed.
Require Import HPSim.
Require Import Red IRed.
Require Import SubPerm.
Require Import ModSimFacts.
Require Import ISimCore CtxRefine ISimFacts.


Set Implicit Arguments.



(* Definition isim_fsem `{Σ: GRA.t} fl_src fl_tgt Ist is_closed: relation (Any.t -> itree hmodE Any.t) := *)
  (* (eq ==> (fun itr_src itr_tgt => *)
             (* forall my_tid nths st_src st_tgt *)
                    (* (IMON: forall nths nths' (LE: nths <= nths') st_src st_tgt, *)
                        (* Ist nths st_src st_tgt -∗ Ist nths' st_src st_tgt) *)
                    (* (NODS: List.NoDup (List.map fst st_src)) *)
                    (* (NODD: List.NoDup (List.map fst st_tgt)), *)
               (* Ist nths st_src st_tgt ⊢ *)
                 (* @isim Σ fl_src fl_tgt Ist my_tid is_closed ibot ibot Any.t *)
                 (* (fun nths '(st_src, v_src) '(st_tgt, v_tgt) => (⌜v_src = v_tgt⌝ ∗ Ist nths st_src st_tgt))%I *)
                 (* false false nths (st_src, itr_src) (st_tgt, itr_tgt)))%signature. *)

Module HSSimC.
  Section SIM.
    Import HModSem.
    Context `{Σ: GRA.t}.
    Variable (ms_src ms_tgt: HModSem.t).
    Variable init_cond: iProp.
    Variable Ist: nat -> alist key Any.t -> alist key Any.t -> iProp.

    Let scopes_src := ms_src.(scopes).
    Let scopes_tgt := ms_tgt.(scopes).
    Let fnsems_src := ms_src.(fnsems).
    Let fnsems_tgt := ms_tgt.(fnsems).
    Let init_src := ms_src.(initial_st).
    Let init_tgt := ms_tgt.(initial_st).


    Inductive t: Prop :=
      mk {
          sim_initial:
            init_cond ⊢ Ist 1 init_src init_tgt;
          sim_mon:
          forall nths nths' (LE: nths <= nths') st_src st_tgt,
            Ist nths st_src st_tgt -∗ Ist nths' st_src st_tgt;
          sim_scopes:
            sub_perm scopes_tgt scopes_src; 
          sim_length:
            List.length fnsems_src = List.length fnsems_tgt;
          sim_match:
            forall fn (IN: In fn (List.map fst fnsems_src)),
              In fn (List.map fst fnsems_tgt);
          sim_fnsems:
            HSSim.sim_fun true ms_src ms_tgt Ist "CRIS_main";
          (* forall fn *)
                 (* (IN: In fn (List.map fst fnsems_src)), *)
              (* sim_fun fn; *)
        }.

  End SIM.
End HSSimC.

Module HSimC.
  Section SIM.
    Context `{Σ: GRA.t}.
    Variable (md_src md_tgt: HMod.t).
    Variable init_cond : Sk.t -> iProp.
    Variable Ist: Sk.t -> nat -> alist key Any.t -> alist key Any.t -> iProp.

    Inductive t: Prop :=
      mk {
          sim_modsem:
          forall sk (SKINCL: List.incl md_tgt.(HMod.sk) sk) (SKWF: Sk.wf sk),
            <<SIM: HSSimC.t (md_src.(HMod.modsem) sk) (md_tgt.(HMod.modsem) sk) (init_cond sk) (Ist sk)>>;
          sim_sk: <<SIM: Sk.equiv md_src.(HMod.sk) md_tgt.(HMod.sk)>>;
        }.

  End SIM.
End HSimC.

Section ADEQUACY.
  Context `{Σ: GRA.t}.
(* 
  Theorem closed_adequacy2 (ms mt: HMod.t) IC Ist
    (SIM: HSimC.t ms mt IC Ist)
    :
    refines (ms, IC) (mt, const(emp%I)).
  Proof.
    split.
    { s. apply SIM. }
    ii. hexploit (HSimC.sim_modsem SIM); eauto.
    { eapply Sk.equiv_incl in EQV. etrans; eauto. refl. }
    i. ss. des. exists ε.
    esplits; eauto.
    { eapply URA.wf_unit. } 
    { eapply hssim_wf; eauto. }
    ii. subst. eapply adequacy_modsem, PR.
    - replace rs with (rs ⋅ ε); [|r_solve]. 
      eapply hssim_adequacy; eauto.
      + r_solve. eauto.
      + eapply Own_iProp; eauto. 
      + eapply hssim_wf; eauto. admit.
    - inv WFM. econs. ss. unfold map_snd.
      rewrite !List.map_map. eapply eq_ind; [apply wf_fns|].
      f_equal. extensionalities. destruct H0. ss.
  Qed. *)

End ADEQUACY.