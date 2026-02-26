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
      | ((set_unfold; naive_solver) || (try set_solver))
        (* Note : tactic for showing domain inclusion of fnsemmaps first try to avoid using
        set_solver. Observed some cases where set_solver uses reflexivity and goes into an
        infinite loop in showing set inclusion, and we try to avoid this. Tactic improvment is
        required *)
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
  rewrite /SB.sandbox_body; simpl fst; simpl snd;
  rewrite /SModTr.trans_fnsem /SModTr.HoareFun /cfunU /cfunN.

Ltac iStartSim := init_simF.
