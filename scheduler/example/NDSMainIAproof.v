Require Import CRIS.
Require Import SchHeader SchA SchTactics.
Require Import RRSHeader RRSA.
Require Import MemHeader MemA.
Require Import RRSNodeHeader RRSNodeI RRSNodeA.
Require Import NDSMainI NDSMainA.
Require Import ltac2_lib.

Module NDSMainIA. Section NDSMainIA.
  Import NDSMainA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG}.
  Context `{_schG: !SchA.newschG}.
  Context `{_rrsG: !RRSA.rrsG}.
  Context `{_memG: !MemA.memG}.
  Context `{_nodeG: !RRSNodeA.nodeG}.

  Context (E: coPset).
  Context (sp: sp_type).
  Context (sp_sch_user sp_user: spl_type).
  Context (Hschglob: sp_incl sp_sch_user sp).
  Context (Hschrrs: spl_sub sp_user sp_sch_user).
  Context (Hsch: sp_incl (SchA.sp sp_sch_user E) sp).
  Context (Hrrs: spl_sub (RRSAS.sp sp_user E) sp_sch_user).
  Context (Hnode: spl_sub (RRSNodeAS.sp E) sp_user).

  Local Definition MA := (NDSMainA.t E sp).
  Local Definition MI := (NDSMainI.t).

  Lemma simF_main : ISim.sim_fun open MA MI emp%I IstTrue None.
  Proof using Hschglob Hschrrs Hsch Hrrs Hnode.
    init_simF.

    steps_l. iDestruct "ASM" as "((-> & I & F) & ->)".
    force_l (λ svarg sarg, ⌜svarg = RRSNodeHdr.f_main↑↑ ∧ svarg = sarg⌝ ∗ RRSAS.InitRRS ∗ RRSNodeAS.full_val (Vint 0),
              λ svret sret, existT 0 (SL.pure False))%I.
    forces_l. iSplitL "I F".
    { iExists _. iSplit; eauto.  do 3 iExists _. iSplit; eauto; cycle 1.
      { iFrame. iSplit; eauto. }
      { iPureIntro. esplits; eauto. r. exists (RRSAS.init_spec sp_user E). esplits; eauto.
        { eapply Hrrs. rewrite /RRSAS.sp. unseal CRIS. ss. }
        econs. ss. Unshelve.
        2:{ ss. eexact (x1.1, x1.2, (λ (svarg sarg : SAny.t), ⌜svarg = sarg ∧ sarg = tt↑↑⌝ ∗ RRSNodeAS.full_val (Vint 0), existT 0 (RRSNodeAS.x_value_tid 0))%I). }
        esplits; eauto.
        { destruct x1 as [mtid stid]. iIntros (??) "(WI & % & % & tidF & % & % & % & I & F)"; des; subst; hss.
          rewrite /RRSAS.init_spec /fspec_sch /fspec_winv /precond /=.
          iFrame. iModIntro. iExists _. iSplit; eauto. iExists _. iPureIntro. esplits; eauto.
          rr. exists (RRSNodeAS.f_main_spec E). esplits; eauto.
          { eapply Hnode. rewrite /RRSNodeAS.sp. unseal CRIS. ss. }
          ii; ss. destruct x1 as [[mtid' stid'] ssch']. exists (stid', ssch'). esplits; eauto.
          { iIntros (??) "(WI & % & % & tidF & RRI & % & % & % & % & F)"; des; subst; hss.
            iFrame. eauto. }
          { iIntros (??) "(WI & (% & tidF) & %)"; des; subst; hss.
            rewrite /fspec_winv /fspec_virtual /postcond. iFrame.
            iModIntro. iExists (tt↑↑). iSplit; eauto. }
        }
        { iIntros (??) "(WI & tidF & % & % & X)". ss. }
      }
    }

    steps_r; steps_l; hss. call "IST". steps_l.
    iDestruct "ASM" as "(% & % & % & % & Join)"; des; subst; hss.
    forces_l. iSplitR; eauto.
    steps_r. step. iFrame; eauto.
  Qed.

  Lemma sim : ISim.t open MA MI emp%I IstTrue.
  Proof using Hschglob Hschrrs Hsch Hrrs Hnode.
    init_sim. eapply simF_main.
  Qed.

End NDSMainIA. End NDSMainIA.

Section ctxr.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG}.
  Context `{_schG: !SchA.newschG}.
  Context `{_rrsG: !RRSA.rrsG}.
  Context `{_memG: !MemA.memG}.
  Context `{_nodeG: !RRSNodeA.nodeG}.

  Lemma ctxr E sp sp_sch_user sp_user
    (Hschglob: sp_incl sp_sch_user sp)
    (Hschrrs: spl_sub sp_user sp_sch_user)
    (Hsch: sp_incl (SchA.sp sp_sch_user E) sp)
    (Hrrs: spl_sub (RRSAS.sp sp_user E) sp_sch_user)
    (Hnode: spl_sub (RRSNodeAS.sp E) sp_user) :
    ctx_refines
      (NDSMainA.t E sp, emp%I)
      (NDSMainI.t     , emp%I).
  Proof using. eapply main_adequacy, (NDSMainIA.sim E sp sp_sch_user sp_user); eauto. Qed.

End ctxr.

