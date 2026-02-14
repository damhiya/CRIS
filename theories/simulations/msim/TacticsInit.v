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
      | mod_tac
      |]
    | econs; intros Hwf;
      [ (refl||eauto using submseteq_nil_l)
      | mod_tac
      |
      | intros fn; eapply ISim.sim_fun_strong; intros Hfn; set_unfold in Hfn; des; subst
      ]
    ]).

Ltac init_simF :=
  let wfs := fresh "WFS" in
  let wft := fresh "WFT" in
  rewrite /ISim.sim_fun; intros wfs wft; simpl_map; eexists; split; first refl;
  iIntros (arg st_src st_tgt) "IST"; iApply wsim_isim;
  rewrite /SB.sandbox_body; simpl fst; simpl snd.

Ltac iStartSim := init_simF; unfold_cris_defs.
