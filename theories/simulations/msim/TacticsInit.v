Require Import Common ConcRA.
From iris.proofmode Require Export proofmode.
Require Import TacticsCommon ITactics WTactics Tactics.
Require Import Mod ISim ISimFacts WSim SModTr.

Ltac cStartModSim :=
  (first
    [ eapply ISim_reflR;
      [ intros fn Hfn; (repeat rewrite Mod.dom_fnsems_add in Hfn); set_unfold in Hfn; des; subst
      | (refl||eauto using submseteq_nil_l)
      | (refl||eauto using submseteq_nil_l)
      | try mod_tac
      | try mod_tac
      |]
    | econs; intros Hwf;
      [ (refl||eauto using submseteq_nil_l)
      | try mod_tac
      |
      | intros fn; eapply ISim.sim_fun_strong; intros Hfn; (repeat rewrite Mod.dom_fnsems_add in Hfn); set_unfold in Hfn; des; subst
      ]
    ]).

Ltac cStartFunSim :=
  let wfs := fresh "WFS" in
  let wft := fresh "WFT" in
  rewrite /ISim.sim_fun; intros wfs wft; simpl_map; eexists; split; first refl;
  iIntros (arg st_src st_tgt) "IST"; iApply wsim_isim;
  rewrite /SB.sandbox_body; simpl fst; simpl snd;
  rewrite /SModTr.trans_fnsem /SModTr.HoareFun /cfunU /cfunN.

