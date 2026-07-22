From CRIS.common Require Import Common ConcRA.
From iris.proofmode Require Export proofmode.
From CRIS.simulations.msim Require Import TacticsCommon ITactics WTactics Tactics ISim ISimFacts WSim.
From CRIS.modules Require Import Mod SModTr.

Ltac cStartModSim :=
  (first
    [ eapply ISim_reflR;
      [ intros fn Hfn; (repeat rewrite Mod.dom_fnsems_add in Hfn); set_unfold in Hfn; des; subst
      | (refl||eauto using submseteq_nil_l)
      | (refl||eauto using submseteq_nil_l)
      | ((set_unfold; naive_solver) || (try timeout 1 mod_tac))
      | try timeout 1 mod_tac
      |]
    | econs; intros Hwf;
      [ (refl||eauto using submseteq_nil_l)
      | try timeout 1 mod_tac
      |
      | intros fn; eapply ISim.sim_fun_strong; intros Hfn; (repeat rewrite Mod.dom_fnsems_add in Hfn); set_unfold in Hfn; des; subst
      ]
    ]).

Ltac cStartFunSim :=
  lazymatch goal with
  | |- ISim.sim_fun ?ctx ?ms_src ?ms_tgt ?Ist ?fn =>
      let wfs := fresh "WFS" in
      let wft := fresh "WFT" in
      rewrite /ISim.sim_fun; intros wfs wft;
      first
        [ rewrite_fnsem_lookup
            (sandbox_fnsemmap (Mod.fnsems ms_src)) fn;
          eexists
        | simpl_map; eexists
        ];
      split; first prove_inline_cond;
      iIntros (arg st_src st_tgt) "IST"; iApply wsim_isim;
      rewrite /SB.sandbox_body; simpl fst; simpl snd;
      rewrite /SModTr.trans_fnsem /SModTr.HoareFun /cfunU /cfunN
  end.
