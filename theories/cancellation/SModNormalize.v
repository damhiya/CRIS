Require Import Common.
From iris.proofmode Require Import proofmode.

Require Import SMod HMod HModSim FSpec.
Require Import ISim ISimNotations ISimInit.
Require Import Tactics TacticsInit.

Set Implicit Arguments.

Module SNorm.
  Import SMod.

  Program Definition normalize `{Σ: GRA} (ms: SMod.t): SMod.t := {|
    scopes := ms.(scopes);
    fnsems := List.map (map_snd (map_snd (map_fst (Some ∘ fspec_flat)))) (ms.(fnsems));
    initial_st := ms.(initial_st);
  |}.
  Next Obligation.
    i. depdes ms. ss. ii. unfold fnsems_scopes in *.
    rewrite !alist_find_map_snd in H. specialize (well_scoped_fns0 fn).
    destruct (alist_find fn _); ss.
    destruct f as [[[img msk] scp] [fsp bd]]. et.
  Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.
End SNorm.

Lemma smod_norm_correct_main
  `{Σ: GRA} (ms: SMod.t) sp T ps pt nths img msk scp st (it: itree hmodE T)
  :
  ⊢ isim open
      (map (map_snd SB.sandbox_body)
       (HMod.fnsems (SMod.to_hmod (Some ∘ fspec_flat ∘ sp) (SNorm.normalize ms))))
      (map (map_snd SB.sandbox_body) (HMod.fnsems (SMod.to_hmod sp ms)))
      IstEq ibot ibot (ist_with_eq IstEq) ps pt nths
      (st, SB.sandbox img msk scp (SModTr.trans (Some ∘ fspec_flat ∘ sp) it))
      (st, SB.sandbox img msk scp (SModTr.trans sp it)).
Proof.
  revert it. combine_quant st. combine_quant scp. combine_quant msk.
  combine_quant img. combine_quant nths. combine_quant ps. combine_quant pt.
  eapply isim_coind. intros g0 a _.
  destruct a as [pt [ps [nths [img [msk [scp [st it]]]]]]]. destruct_quant.
  iIntros "[_ CIH]".
  assert (CASE := case_itrH it); des; subst.
  - step. et.
  - steps_l. steps_r. by_coind "CIH". et.
  - destruct img.
    + steps_l. forces_r. iFrame. steps_r. by_coind "CIH". eauto.
    + rewrite SRed.bind SBRed.bind SRed.ag SBRed.Assume. steps_l. ss.
  - steps_l. steps_r. step. steps_l. steps_r. by_coind "CIH". eauto.
  - steps_r. forces_l. iFrame. steps_l. by_coind "CIH". eauto.
  - depdes c.
    + steps_l. steps_r. destruct (sp fn).
      * steps_r. destruct f. s. forces_l. iFrame. steps_l.
        call "". ired. rewrite SBRed.bind SBRed.take.
        destruct img; cycle 1.
        { destruct (excluded_middle_informative _); s.
          - des. assert (IP:=proof_irrelevance P). rewrite -e in IP.
            specialize (IP 0↑ 1↑). eapply (f_equal Any.downcast) in IP. hss.
          - steps_l. ss.
        }
        s. steps_l. forces_r. iFrame. steps_r.
        iDestruct "IST" as "%". subst. by_coind "CIH"; et.
      * forces_l. iSplit; et. steps_l.
        call "". ired. rewrite SBRed.bind SBRed.take.
        destruct img; cycle 1.
        { destruct (excluded_middle_informative _); s.
          - des. assert (IP:=proof_irrelevance P). rewrite -e in IP.
            specialize (IP 0↑ 1↑). eapply (f_equal Any.downcast) in IP. hss.
          - steps_l. ss.
        }
        s. steps_l. iDestruct "IST" as "%". iDestruct "ASM" as "%".
        subst. by_coind "CIH"; et.
    + steps_l. steps_r.  destruct (sp fn).
      * steps_r. destruct f. s. forces_l. iFrame. steps_l.
        spawn. ired. yield "".
        steps_l. steps_r.
        iDestruct "IST" as "%". subst. by_coind "CIH"; et.
      * forces_l. iSplit; et. steps_l.
        spawn. ired.
        call "". ired. rewrite SBRed.bind SBRed.take.
        destruct img; cycle 1.
        { destruct (excluded_middle_informative _); s.
          - des. assert (IP:=proof_irrelevance P). rewrite -e in IP.
            specialize (IP 0↑ 1↑). eapply (f_equal Any.downcast) in IP. hss.
          - steps_l. ss.
        }
        s. steps_l. iDestruct "IST" as "%". iDestruct "ASM" as "%".
        subst. by_coind "CIH"; et.








      rewrite SBRed.spawn. des_ifs.
      * iApply isim_spawn. iby_coind "CIH". iApply MON; [|eauto]; nia.
      * isteps_l. ss.
    + iyield "IST"; eauto. iby_coind "CIH". eauto.
  - depdes s.
    + rewrite !SBRed.bind !SBRed.put. des_ifs; cycle 1.
      { isteps_l. ss. }
      iApply isim_nodup. iIntros (? ? ? ?).
      iApply isim_sput_src. iApply isim_sput_tgt.
      iby_coind "CIH". iApply EQSET; et.
      apply existsb_exists in Heq. des. apply String.eqb_eq in Heq0. subst. et.
    + rewrite !SBRed.bind !SBRed.get. des_ifs; cycle 1.
      { isteps_l. ss. }
      iApply isim_nodup. iIntros (? ? ? ?).
      iApply isim_sget_src. iApply isim_sget_tgt.
      apply existsb_exists in Heq. des. apply String.eqb_eq in Heq0. subst.
      iPoseProof (EQGET with "IST") as "%"; et. rewrite H.
      iby_coind "CIH". eauto.
  - destruct e.
    + isteps_r. iforce_l q. isteps_l. iby_coind "CIH". eauto.
    + destruct img.
      * isteps_l. iforce_r q. isteps_r. iby_coind "CIH". eauto.
      * rewrite SBRed.bind SBRed.take. s. des_ifs; isteps_l; ss.
        isteps_l. iforce_r q. isteps_r. iby_coind "CIH". eauto.
    + istep. iby_coind "CIH". eauto.
  
  

  

  
Qed.

Lemma smod_norm_correct `{Σ: GRA} (ms: SMod.t) sp:
  HSim.t open
    (SMod.to_hmod (Some ∘ fspec_flat ∘ sp) (SNorm.normalize ms))
    (SMod.to_hmod sp ms)
    emp%I IstEq.
Proof.
  init_sim; try refl.
  { s. eapply eq_ind; try refl.
    rewrite !map_map. f_equal. extensionalities. destruct H0. s. et.
  }
  { rewrite !alist_find_map_snd in H0 |- *. destruct (alist_find _ _); ss; et. }

  ii. revert FIND. rewrite /SNorm.normalize. s.
  rewrite !alist_find_map_snd. i. destruct (alist_find _ _) eqn:E; ss.
  inv FIND. esplits; et.
  destruct p as [[[img msk] scp] [fsp bd]]. ii; ss.
  rewrite /SB.sandbox_body /SModTr.trans_body. simpl snd. simpl fst.
  iIntros "H".
  iAssert (⌜st_src = st_tgt⌝%I) with "[H]" as "%".
  { rewrite /HSim.IstS. destruct fn; iDestruct "H" as "%"; des; subst; et. }
  subst. iClear "H".

  destruct img; s; cycle 1.
  {
    iApply isim_mono; cycle 1.
    - iApply isim_refl; i; et.
      + iIntros "%"; subst; et.
      + iIntros "%"; subst; et.
    - i. iIntros "%"; des; subst. iSplit; et.
      destruct fn; et.
  }

  rewrite /SModTr.HoareFun. destruct fsp; s.
  - steps_l. destruct f.
    forces_r. iFrame. steps_r.
    iApply isim_bind. iSplitL "".
    { iApply smod_norm_correct_main. }

    iIntros (? ? ? ? ?) "[% IST]". subst.
    steps_r. forces_l. iFrame.
    step. destruct fn; et.
  - steps_l. iDestruct "ASM" as "%". subst.
    only_itree_r. rewrite <-(bind_ret_r (_ (_ (bd arg)))). show_itree.
    iApply isim_bind. iSplitL "".
    { iApply smod_norm_correct_main. }

    iIntros (? ? ? ? ?) "[% IST]". subst.
    forces_l. iSplit; et.
    step. destruct fn; et.
Qed.
