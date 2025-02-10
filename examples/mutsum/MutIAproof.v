Require Import CRIS.

Require Import NormITree.
Require Import MutHeader MutFI MutFA MutGI MutGA.

Set Implicit Arguments.

Module MutIA. Section MutIA.
  Import MutAUX.
  Context {Σ: GRA}.
  Notation iProp := (iProp Σ).

  Definition Ist: nat -> alist key Any.t -> alist key Any.t -> iProp :=
    λ _ _ _, (True)%I.

  Variable ginv: invspec.
  Variable Spc: string -> option fspec.

  Local Notation MutFA := (MutFA.t ginv Spc).
  Local Notation MutGA := (MutGA.t ginv Spc).
  Local Notation MutAMod := (MutFA ★ MutGA).
  Local Notation MutIMod := (MutFI.t ★ MutGI.t).
  
  (*************)

  Lemma pair_induction (P : nat → Prop)
      (ZERO: P 0) (ONE: P 1)
      (IND: ∀ n, P n → P (S n) → P (S (S n)))
    :
      ∀ n, P n.
  Proof.
    intro n. apply proj1 with (B := (P (S n))).
    induction n; ss. des. split; eauto.
  Qed.

  Lemma simF_mutf:
    HSim.sim_fun open MutAMod MutIMod Ist MutName.mutf.
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "((%Y & %B) & %Q)". subst; hss.
    steps_r. force_r. steps_r. 
    
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
      
      inline_r. hss. steps_r. force_r. steps_r.
      step. iFrame; et.
    }
    { (* f(1) *)
      iIntros "IST". s.

      (* add meaningless return after call for inlining *)
      set (it:=trigger _).
      eapply isim_congruence_tgt.
      { instantiate (1:=r <- it;; Ret r). grind. }
      subst it.
      
      inline_r. hss. steps_r. force_r. steps_r.
      inline_r. hss. steps_r. force_r. steps_r.
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
      inline_r. hss. steps_r. force_r. steps_r.
      destruct (dec ((S (S q) - 1))%Z 0%Z); [lia|]. clear n.
      (* second inline *)
      inline_r. hss. steps_r. force_r. steps_r.
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

  (* Exactly the same as simF_mutf *)
  Lemma simF_mutg:
    HSim.sim_fun open MutAMod MutIMod Ist MutName.mutg.
  Proof.
    init_simF.

    steps_l. iDestruct "ASM" as "((%Y & %B) & %Q)". subst; hss.
    steps_r. force_r. steps_r. 
    
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
      
      inline_r. hss. steps_r. force_r. steps_r.
      step. iFrame; et.
    }
    { (* f(1) *)
      iIntros "IST". s.

      (* add meaningless return after call for inlining *)
      set (it:=trigger _).
      eapply isim_congruence_tgt.
      { instantiate (1:=r <- it;; Ret r). grind. }
      subst it.
      
      inline_r. hss. steps_r. force_r. steps_r.
      inline_r. hss. steps_r. force_r. steps_r.
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
      inline_r. hss. steps_r. force_r. steps_r.
      destruct (dec ((S (S q) - 1))%Z 0%Z); [lia|]. clear n.
      (* second inline *)
      inline_r. hss. steps_r. force_r. steps_r.
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

  Theorem sim:
    HSim.t open MutAMod MutIMod (MutFA.InitCond ∗ MutGA.InitCond) Ist.
  Proof.
    init_sim.
    - iIntros "IC". ss.
    - exists []; unfold MutFI.t, MutGI.t, MutFA, MutGA; unseal CRIS; ss.
    - unfold MutFI.t, MutGI.t in IN. revert IN. unseal CRIS. i; ss; des; ss.
      { subst. eapply simF_mutf; eauto. }
      { subst. eapply simF_mutg; eauto. }
  Qed.

  Theorem correct:
    ctx_refines
      (MutAMod, (MutFA.InitCond ∗ MutGA.InitCond)%I)
      (MutIMod, emp%I).
  Proof.
    eapply main_adequacy.
    eapply sim.
  Qed.

End MutIA. End MutIA.
