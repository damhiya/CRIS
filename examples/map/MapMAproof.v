Require Import Coqlib ITreelib sflib.
Require Import MapHeader MapM MapA MapMSpec MapASpec SMod ModSim.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Events Behavior.
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

Require Import STB.

Require Import ISim.
Require Import HMod Mod ModSimFacts.


Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module MapMA.
Section SIMMODSEM.
  Context `{_W: CtxWD.t}.
  Context `{_M: MapMR.t (Γ:=Γ)}.
  Context `{_A: MapAR.t (Γ:=Γ)}.

  Import MapAS.
  
  Section LEMMA. 
    Local Transparent unallocated points_to initial_map black_map pending MapMS.pending.

    Lemma unallocated_alloc (sz: nat)
      :
      unallocated sz -∗ (points_to sz 0 ∗ unallocated (Z.pos (Pos.of_succ_nat sz))).
    Proof.
      unfold points_to, unallocated. iIntros "H".
      replace (unallocated_r sz) with ((points_to_r sz 0) ⋅ (unallocated_r (S sz))).
      { ss. iDestruct "H" as "[H0 H1]". iFrame. }
      unfold unallocated_r, points_to_r. ur. f_equal.
      { ur. auto. }
      { ur. unfold Auth.white. f_equal. ur. extensionality k.
        ur. des_ifs; try by (exfalso; lia).
      }
    Qed.

    Lemma initial_map_initialize sz
      :
      initial_map -∗ (black_map (fun _ => 0%Z) ∗ initial_points_tos sz ∗ unallocated sz).
    Proof.
      induction sz.
      { ss. iIntros "H". unfold initial_map.
        replace initial_map_r with ((black_map_r (fun _ => 0%Z)) ⋅ (unallocated_r 0)).
        { iDestruct "H" as "[H0 H1]". unfold initial_points_tos. s. iFrame. }
        { unfold initial_map_r, black_map_r, unallocated_r. ur. f_equal.
          { ur. auto. }
          { ur. f_equal. ur. extensionality k. ur. des_ifs. }
        }
      }
      { iIntros "H". iPoseProof (IHsz with "H") as "H". ss.
        iDestruct "H" as "(B & I & U)".
        iPoseProof (unallocated_alloc with "U") as "[M U]". iFrame.
        unfold initial_points_tos. replace (S sz) with (sz + 1) by nia.
        rewrite repeat_app. s. rewrite// big_sepL_snoc repeat_length. iFrame.
      }
    Qed.

    Lemma initial_map_no_points_to k v
      :
      initial_map -∗ points_to k v -∗ ⌜False⌝.
    Proof.
      unfold initial_map, points_to.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iOwnWf "H" as WF. exfalso. rr in WF. ur in WF. unseal "ra". des.
      rr in WF0. ur in WF0. unseal "ra". des.
      rr in WF0. des. ur in WF0. eapply equal_f with (x:=k) in WF0.
      ur in WF0. des_ifs.
    Qed.

    Lemma unallocated_range sz k v
      :
      unallocated sz -∗ points_to k v -∗ ⌜(0 <= k < sz)%Z⌝.
    Proof.
      unfold unallocated, points_to.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iOwnWf "H" as WF. iPureIntro. rr in WF. ur in WF. unseal "ra". des.
      rr in WF. ur in WF0. unseal "ra".
      rr in WF0. ur in WF0. unseal "ra". specialize (WF0 k).
      rr in WF0. ur in WF0. unseal "ra". des_ifs. lia.
    Qed.

    Lemma black_map_get f k v
      :
      black_map f -∗ points_to k v -∗ (⌜f k = v⌝).
    Proof.
      unfold black_map, points_to.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iOwnWf "H" as WF. iPureIntro. rr in WF. ur in WF. unseal "ra". des.
      rr in WF0. ur in WF0. unseal "ra". des.
      rr in WF0. des. ur in WF0. eapply equal_f with (x:=k) in WF0.
      ur in WF0. des_ifs.
    Qed.

    Lemma black_map_set f k w v
      :
      black_map f -∗ points_to k w -∗ #=> (black_map (<[k:=v]>f) ∗ points_to k v).
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iPoseProof (OwnM_Upd with "H") as "H".
      { instantiate (1:=black_map_r (<[k:=v]>f) ⋅ points_to_r k v).
        rr. intros ctx WF. ur in WF. ur. unseal "ra". des_ifs. des. split; auto.
        ur in WF0. ur. des_ifs. des. rr in WF0. des. split.
        { rr. exists ctx. ur in WF0. ur. extensionality n.
          eapply equal_f with (x:=n) in WF0. ur in WF0. ur.
          des_ifs; rewrite ->?fn_lookup_insert, ?fn_lookup_insert_ne; eauto.
        }
        { ur. i. rr. ur. unseal "ra". ss. }
      }
      iMod "H". iDestruct "H" as "[H0 H1]". iFrame. auto.
    Qed.

    Lemma pending_unique:
      pending -∗ pending -∗ False%I.
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iOwnWf "H" as WF. exfalso.
      rr in WF. ur in WF. unseal "ra". des.
      rr in WF. ur in WF. unseal "ra". ss.
    Qed.
    
  End LEMMA.

  Definition Ist: Sk.t -> alist key Any.t -> alist key Any.t -> iProp :=
    (fun _ st_src st_tgt =>
       ∃ f sz, ⌜st_src = [(MapA.v_map, f↑)] ∧ st_tgt = [(MapM.v_size, sz↑);(MapM.v_map, f↑)]⌝ ∗
       ((⌜f = (fun (_: Z) => 0%Z) ∧ sz = 0%Z⌝ ∗ MapMS.pending ∗ initial_map)
       ∨ 
       (pending ∗ black_map f ∗ unallocated sz)))%I.

  Variable StbH: Sk.t -> gname -> option fspec.
  Hypothesis MapInStbH: forall sk, stb_incl MapAS.Stb (StbH sk).

  Variable StbL: Sk.t -> gname -> option fspec.
  Hypothesis MapInStbL: forall sk, stb_incl MapMS.Stb (StbL sk).

  Local Notation MapAMod := (MapA.t StbH).
  Local Notation MapMMod := (MapM.t StbL).
  
  Lemma simF_init:
    HModR.sim_fun MapAMod MapMMod Ist MapName.init.
  Proof.
    init_simF.

    (* SRC: handle the IST of Map and the precond of init *)
    steps_l. iDestruct "ASM" as "(W & (%Y & %M & P) & %X)".
    iDestruct "IST" as (f sz) "(% & [(% & P0 & INIT)|(P' & B & U)])"; cycle 1.
    { iExFalso. iApply (pending_unique with "P P'"). }
    des; subst. hss. rename q0 into u, q1 into ℓ, x into sz'.
    
    (* TGT: prove the precond of init *)
    force_r. instantiate (1:= mk_meta _ _ _). force_r. force_r. hss.
    iSplitL "P0 W". { iFrame. eauto. }

    (* TGT: handle the postcond of init *)
    steps_r. iDestruct "GRT" as "(CW & _ & %Y)". subst. hss.
    
    (* SRC: prove the postcond of init *)
    force_l. force_l.
    iPoseProof (initial_map_initialize with "INIT") as "(BLACK & INIT & UNALLOC)".
    iSplitL "CW INIT". { iFrame. eauto. }
    
    (* prove the IST of Map *)
    step. iSplit; eauto.
    iExists _, _. iSplitL ""; eauto. iRight. iFrame. 
  Qed.

  Lemma simF_get:
    HModR.sim_fun MapAMod MapMMod Ist MapName.get.
  Proof.
    init_simF.

    (* SRC: handle the IST of Map and the precond of get *)
    steps_l. iDestruct "ASM" as "(WORLD & (% & MAP) & %)".
    iDestruct "IST" as (f sz) "(% & [(% & P0 & INIT)|(P' & B & U)])".
    { iExFalso. iApply (initial_map_no_points_to with "INIT MAP"). }
    des. subst. hss. rename q0 into u, q1 into ℓ, q3 into idx, x1 into v.

    (* TGT: prove the precond of get *)
    force_r. instantiate (1:= mk_meta _ _ _). force_r. force_r. hss.
    iSplitL "WORLD". { iFrame. eauto. }

    (* TGT: handle the body of get *)
    steps_r. hss. steps_r. hss. steps_r.
    iPoseProof (unallocated_range with "U MAP") as "%".
    force_r; eauto.

    (* TGT: handle the postcond of get *)
    steps_r. iDestruct "GRT" as "(WORLD & _ & %)". subst.

    (* SRC: prove the postcond of get *)
    force_l. force_l.
    iPoseProof (black_map_get with "B MAP") as "%". subst.
    iSplitL "WORLD MAP". { iFrame. eauto. }

    (* prove the IST of Map *)
    step. iSplitL; eauto.
    iExists _, _. iSplitL ""; eauto. iRight. iFrame.
  Qed.

  Lemma simF_set:
    HModR.sim_fun MapAMod MapMMod Ist MapName.set.
  Proof.
    init_simF.

    (* SRC: handle the IST of Map and the precond of set *)
    steps_l. iDestruct "ASM" as "(WORLD & (% & MAP) & %)".
    iDestruct "IST" as (f sz) "(% & [(% & P0 & INIT)|(P' & B & U)])".
    { iExFalso. iApply (initial_map_no_points_to with "INIT MAP"). }
    des. subst. hss.
    rename q0 into u, q1 into ℓ, q4 into idx, x3 into v, q5 into v'.

    (* TGT: prove the precond of set *)
    force_r. instantiate (1:= mk_meta _ _ (_,_)). force_r. force_r. hss.
    iSplitL "WORLD". { iFrame. eauto. }

    (* TGT: handle the body of set *)
    steps_r. hss. steps_r. hss. steps_r.
    iPoseProof (unallocated_range with "U MAP") as "%".
    force_r; eauto.

    (* TGT: handle the postcond of set *)
    steps_r. iDestruct "GRT" as "(WORLD & _ & %)". subst. hss.
    
    (* SRC: prove the postcond of set *)
    iPoseProof (black_map_set with "B MAP") as ">(B & MAP)".
    force_l. force_l.
    iSplitL "WORLD MAP". { iFrame. eauto. }

    (* prove the IST of Map *)
    step. iSplitL; eauto.
    iExists _, _. iSplitL ""; eauto. iRight. iFrame.
  Qed.

  Lemma simF_set_by_user:
    HModR.sim_fun MapAMod MapMMod Ist MapName.set_by_user.
  Proof.
    init_simF.

    (* SRC: handle the IST of Map and the precond of set_by_user *)
    steps_l. iDestruct "ASM" as "(WORLD & (% & MAP) & %)".
    subst. hss. inv G0. rename q0 into u, q1 into ℓ, q3 into idx, x1 into v.
    
    (* TGT: prove the precond of set_by_user *)
    force_r. instantiate (1:= mk_meta _ _ _). force_r. force_r. hss.
    iSplitL "WORLD". { iFrame. eauto. }

    (* process an input *)
    steps_r. step.

    (* TGT: handle the precond of set *)
    steps_r. iDestruct "GRT" as "[[WORLD [% %]] _]". subst. hss.
    
    (* SRC: prove the precond of set *)
    steps_l. force_l. instantiate (1:= mk_meta _ _ (_,_,_)). force_l. force_l.
    iSplitL "WORLD MAP". { iFrame. eauto. }

    (* make a call to set *)
    call "IST". { eauto. }

    (* SRC: handle the postcond of set *)
    steps_l. iDestruct "ASM" as "(WORLD & (% & MAP) & %)". subst. hss.

    (* TGT: prove the postcond of set *)
    force_r. force_r.
    iSplitL "WORLD". { iFrame. eauto. }

    (* TGT: handle the postcond of set_by_user *)
    steps_r. hss. steps_r. iDestruct "GRT" as "(WORLD & _ & %)". subst.
    
    (* SRC: prove the postcond of set_by_user *)
    force_l. force_l.
    iSplitL "MAP WORLD". { iFrame. eauto. }

    (* prove the IST of Map *)
    step. eauto.
  Qed.
  
  Theorem sim: HModR.sim MapAMod MapMMod MapA.InitCond Ist.
  Proof.
    init_sim.
    - iIntros "(IST & P)"; s.
      iExists _, _. iSplit; eauto. iLeft. iFrame. eauto.
    - apply simF_init.
    - apply simF_get.
    - apply simF_set.
    - apply simF_set_by_user.
  Qed.

End SIMMODSEM.
End MapMA.
