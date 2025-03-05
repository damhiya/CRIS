Require Import CRIS.

Require Import NormITree.
Require Import MutHeader MutFI MutFA MutGI MutGA.
Require Import APCHeader APC APCA.

Set Implicit Arguments.

Module MutIA. Section MutIA.
  Import MutAUX.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.

  Context (u_s u_apc: univ_id).
  Context (Spc: string -> option fspec).
  Context (SpcPure: string -> option fspec).

  Context (APCInSpc : spc_incl (APCA.Spc) Spc).
  Context (GInSpc : spc_incl (MutGA.SpcG) Spc).

  Definition Ist: nat -> alist key Any.t -> alist key Any.t -> iProp Σ :=
    λ _ _ _, (True)%I.

  Local Definition MutAMod := (MutFA.t Spc ★ APCA.t u_apc SpcPure Spc).
  Local Definition MutIMod := (MutFI.t).
  
  (*************)

  Lemma simF_mutf:
    HSim.sim_fun open MutAMod MutIMod Ist MutName.mutf.
  Proof.
    winit_simF u_s 0.

    wsteps_l. iDestruct "ASM" as "((%Y & %B) & %Q)". subst; hss.
    wsteps_r. unfold assume. wforce_r. wsteps_r.
    
    destruct q; s.
    { (* f(0) *)
      wsteps_r. wforce_l. wsteps_l.
      wforces_l. iSplitR; et. wsteps_l. 
      winline_l. wsteps_l. iDestruct "ASM" as "[-> <-]"; hss. wsteps_l.
      rewrite /APC. wforce_l q. wsteps_l. rewrite unfold_APC.
      wforce_l true. wsteps_l. wforces_l. iSplitR; eauto.
      wsteps_l. wforces_l. iSplitR; eauto.
      wstep. iFrame; et.
    }

    replace (S q - 1)%Z with (Z.of_nat q) by nia.
    wsteps_l. wforce_l vo. wsteps_l. wforces_l. iSplitR; eauto.
    winline_l. wsteps_l. iDestruct "ASM" as "[-> <-]"; hss. wsteps_l.
    rewrite /APC. wforce_l 1. wsteps_l. rewrite unfold_APC.
    wforce_l false. wsteps_l. wforce_l 0. wsteps_l.
    assert (LT: (0 < 1)%ord).
    { eapply OrdArith.lt_from_nat. nia. }
  Qed.

  (* Exactly the same as simF_mutf *)
  Lemma simF_mutg:
    HSim.sim_fun open MutAMod MutIMod Ist MutName.mutg.
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "((%Y & %B) & %Q)". subst; hss.
    steps_r. unfold assume. force_r. steps_r. 
    
    (* HOW TO PROVE: make goal simple as possible *)
    (* 1. remove if-then-else clause *)
    destruct q; s.
    { (* f(0) *)
      steps_r. steps_r. force_l. steps_l.
      forces_l. iSplitR; et. step. iFrame; et.
    }

    (* 2. normalize itree for applying bind rule easier *)
    s. bind_expand_l. bind_expand_r.

    (* 3. add meaningless return in front of the SRC itree *)
    set (itr:=(ITree.bind _ _)).
    eapply isim_congruence_src.
    { instantiate (1:=Ret (Vint (sum q))↑;;; itr). rewrite bind_ret_l. refl. }

    (* 4. apply bind rule *)
    iApply isim_bind. iSplitL; cycle 1.
    { (* 5. prove after-core part *)
      iIntros (? ? ? ? ?) "R".
      instantiate 
        (1:=(λ nths '(st_src, ret_src) '(st_tgt, ret_tgt), Ist nths st_src st_tgt 
              ∗ ⌜ret_src = (Vint (sum q))↑ ∧ ret_src = ret_tgt⌝)%I).
      iDestruct "R" as "[IST %]". des; subst; hss.
      subst itr. steps_r. hss. steps_r. force_l. steps_l. forces_l. iSplitR; et. step.
      iSplit; et. iPureIntro. repeat f_equal. nia.
    }
    clear itr.

    (* 6. simplify the goal for more clarity *)
    replace (S q - 1)%Z with (Z.of_nat q) by nia.

    (* FINALLY apply pair induction *)
    iStopProof. induction q using pair_induction.
    { (* f(0) *)
      iIntros "IST". s.

      (* add meaningless return after call for inlining *)
      set (it:=trigger _).
      eapply isim_congruence_tgt.
      { instantiate (1:=r <- it;; Ret r). grind. }
      subst it.
      
      inline_r. hss. steps_r. unfold assume. force_r. steps_r.
      step. iFrame; et.
    }
    { (* f(1) *)
      iIntros "IST". s.

      (* add meaningless return after call for inlining *)
      set (it:=trigger _).
      eapply isim_congruence_tgt.
      { instantiate (1:=r <- it;; Ret r). grind. }
      subst it.
      
      inline_r. hss. steps_r. unfold assume. force_r. steps_r.
      inline_r. hss. steps_r. unfold assume. force_r. steps_r.
      hss. steps_r. step. iFrame; et.
    }
    { (* f(S S x) *)
      iIntros "IST". clear IHq0.
      (* add meaningless return after call for inlining *)
      set (it:=trigger _).
      eapply isim_congruence_tgt.
      { instantiate (1:=r <- it;; Ret r). grind. }
      subst it.
      (* first inline *)
      inline_r. hss. steps_r. unfold assume. force_r. steps_r.
      destruct (dec ((S (S q) - 1))%Z 0%Z); [lia|]. clear n.
      (* second inline *)
      inline_r. hss. steps_r. unfold assume. force_r. steps_r.
      replace ((S (S q)) - 1)%Z with (Z.of_nat (S q)) by lia. s.
      replace (S q - 1)%Z with (Z.of_nat q) by lia.

      (* normalize itree *)
      bind_expand_r.
      (* reform SRC itree *)
      eapply isim_congruence_src.
      { instantiate (1:=
          r <- Ret (Vint (sum q))↑;;
          r <- (r↓)?;;
          r <- (vadd (Vint (S (S q) + S q)) r)?;;
          Ret r↑).
        grind. hss. grind. repeat f_equal. nia.
      }

      (* apply bind rule *)
      iApply isim_bind. iSplitL.
      { iStopProof. eapply IHq. nia. }
      (* prove after-core part *)
      iIntros (? ? ? ? ?) "R".
      iDestruct "R" as "[IST %]". des; subst; hss.
      steps_r. hss. steps_r. hss. steps_r. steps_l.
      step. iFrame; et. iPureIntro. split.
      { do 2 f_equal. nia. }
      { do 2 f_equal. nia. }
    }
    Unshelve. all: ss.
    { apply mut_max_intrange; eauto. }
    { replace (Z.of_nat (S (S q))) with (Z.of_nat (S (S (S q))) - 1)%Z by nia.
      eapply mut_max_intrange_sub1. eauto. }
    { eapply mut_max_intrange_sub1. nia. }
  Qed.

  End MutIA.   

  Theorem sim `{Σ: GRA} Spc:
    HSim.t open (MutIA.MutAMod Spc) MutIMod (MutFA.InitCond ∗ MutGA.InitCond) Ist.
  Proof.
    rewrite /MutIMod /MutAMod.
    init_sim.
    - iIntros "IC". ss.
    - repeat (unfold_hmod; s). rewrite /MutGI.scopes /MutGA.scopes.
      prove_sub_perm.
    - eapply simF_mutf; eauto.
    - eapply simF_mutg; eauto.
  Qed.

  Theorem correct `{Σ: GRA} Spc:
    ctx_refines
      (MutAMod Spc, (MutFA.InitCond ∗ MutGA.InitCond)%I)
      (MutIMod, emp%I).
  Proof.
    eapply main_adequacy.
    eapply sim.
  Qed.

End MutIA.
