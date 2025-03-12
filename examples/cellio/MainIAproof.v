Require Import CRIS.
Require Import CellioHeader CellioA MainHeader MainA MainI FooA InputA.

Set Implicit Arguments.

Module MainIA. Section MainIA.
  Import CellioA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !CellioAGΓ Γ}.

  Definition Ist: nat -> alist key Any.t -> alist key Any.t -> iProp Σ :=
    λ _ st_src st_tgt, emp%I.

  Context (spc_s: string -> option fspec).
  Context (FooInSpc: spc_incl FooAS.spc spc_s).
  Context (InputInSpc: spc_incl InputAS.spc spc_s).

  Local Definition CellioA := (CellioA.t spc_s).
  Local Definition MainA := (MainA.t spc_s).
  Local Definition IstFull := (IstProd (IstSB MainA.(HMod.scopes) Ist) IstEq).

  Lemma simF_main:
    HSim.sim_fun open MainA (MainI.t ★ CellioA) IstFull MainName.main.
  Proof. 
    winit_simF 0 0.
    
    (* Take cell(0) *)
    wsteps_l; iDestruct "ASM" as "%"; subst.

    winline_r.
    (* Give cell(0) *)
    wsteps_r. wforces_r. iSplitL ""; eauto.
    wforces_r. wsteps_r. wforces_r. iSplitL "ASM'"; eauto.

    (* Call Input() simultaneously *)
    wsteps_r. wforces_l. iSplitL "GRT"; eauto.
    wcall "IST"; eauto.
    wsteps_l. wforces_r. iSplitL "ASM"; eauto.
    wsteps_r. hss.

    (* Take cell(i) *)
    wsteps_r. iDestruct "GRT'" as "%". subst. hss.
    
    (* Call Foo.foo() simultaneously *)
    wsteps_l. wsteps_r. wforces_l. iSplitL ""; eauto.
    wcall "IST"; eauto.
    wsteps_l. iDestruct "ASM" as "%". subst. hss. wsteps_r. hss. wsteps_r.

    winline_r.
    (* Give cell(i) *)
    wstep_r. wforces_r. iSplitL ""; eauto.
    wforces_r. wsteps_r. wforces_r.
    iSplitL "GRT"; eauto.

    (* Take cell(i) *)
    wsteps_r. iDestruct "GRT'" as "%". subst. hss.

    (* Call Print(i) simultaneously *)
    wsteps_r. wstep.

    wsteps_l. wforces_l.
    iSplitL ""; eauto.

    wsteps_r. wstep. iFrame. eauto.

    Unshelve. all:(exact ()).
  Qed.

  Theorem sim :
    HSim.t open MainA (MainI.t ★ CellioA) MainA.InitCond IstFull.
  Proof.
    init_sim.
    - iIntros "_". repeat iExists []. iSplit; eauto.
      repeat (iSplit; eauto); iPureIntro; prove_scope.
    - eapply simF_main; eauto.
  Qed.
End MainIA. End MainIA.
