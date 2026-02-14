Require Import Common ConcRA.
From iris.proofmode Require Export proofmode.
Require Import TacticsCommon ITactics WTactics Tactics.
Require Import Mod ISim ISimFacts WSim SModTr.

Ltac init_sim :=
  (first
    [ eapply ISim_reflR;
      [ intros fn Hfn; set_unfold in Hfn; des; subst
      | (refl||eauto using submseteq_nil_l)
      | (refl||eauto using submseteq_nil_l)
      | try set_solver
      |]
    | econs; intros Hwf;
      [ (refl||eauto using submseteq_nil_l)
      |
      | intros fn; eapply ISim.sim_fun_strong; intros Hfn; set_unfold in Hfn; des; subst
      ]
    ]).

Ltac init_simF :=
  let wft := fresh "WFT" in
  (tryif (
    rewrite /ISim.sim_fun; simpl_map; intros wft; eexists; split; first refl
  )
  then idtac
  else (
    match goal with
    | |- ISim.sim_fun _ ?ms ?mt _ _ =>
      intros wft;
      let wfs := fresh "WFS" in
      assert (wfs : Mod.wf ms);
        [eapply Mod.add_wf_inv in wft as [? [? [? ?]]];
        apply Mod.add_wf;
          [ econs; [mod_tac | (done || prove_nodup)]
          | ss
          | try set_solver
          | (ss || prove_nodup) ]
        | ]
    end; simpl_map; eexists; split; first refl
  ));
  iIntros (arg st_src st_tgt) "IST"; iApply wsim_isim;
  rewrite /SB.sandbox_body; simpl fst; simpl snd.

Ltac iStartSim := init_simF; unfold_cris_defs.
