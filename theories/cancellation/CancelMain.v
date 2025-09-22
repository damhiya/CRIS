Require Import CRIS.
Require Import LMod LModTr GSim GSimFacts GSimTactics.
Require Import MInline MInlineIntro MInlineElim.
Require Import CancelCore CancelPG CancelAG CancelSpawn CancelPre CancelPost.

Set Implicit Arguments.

Module MainSMod. Section MainSMod.

  Context `{!crisG Γ Σ α β τ _S _I, !concG}.

  Definition trans_ktree (fno: option string) sp (sb : fnsem_type (option fspec * fbody)) : fnsem_type fbody :=
    map_snd (λ '(fsp,bd), SModTr.trans_body (is_some sb.2.1, if sb.1.1.1 then sp else sp_none, if is_some fno then fsp else None) bd) sb.

  Definition map_fnsems sp (fnsems: fnsems_type) :=
    List.map (λ '(fno, fnsem), (fno, trans_ktree fno sp fnsem)) fnsems.

  Lemma alist_find_map_fnsems fn sp fnsems :
    alist_find fn (map_fnsems sp fnsems) = o_map (alist_find fn fnsems) (λ fnsem, trans_ktree fn sp fnsem).
  Proof.
    rewrite /map_fnsems.
    destruct (alist_find fn fnsems) eqn:E; ss; des_ifs; induction fnsems; ss; des_ifs; try (destruct o; ss); try (rewrite IHfnsems; ss); rewrite eq_rel_dec_correct in Heq0; des_ifs.
  Qed.

  Program Definition to_mod (sp : sp_type) (ms : SMod.t) : Mod.t := {|
    Mod.scopes := ms.(SMod.scopes);
    Mod.fnsems := map_fnsems sp ms.(SMod.fnsems);
    Mod.initial_st := ms.(SMod.initial_st);
    |}.
  Next Obligation.
    i. destruct ms. ss. ii. unfold fnsems_scopes in *.
    rewrite alist_find_map_fnsems in H0.
    specialize (well_scoped_fns fn a).
    destruct (alist_find fn fnsems) eqn: E; ss.
    destruct f. et.
  Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.
  Next Obligation. ii. destruct ms. ss. eauto. Qed.

End MainSMod. End MainSMod.

Module CancelMain. Section CancelMain.

Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concG}.

Lemma cancel_main md rs
  (WFS: SMod.wf md)
  (WF: Mod.wf (SMod.to_mod sp_none (SMod.cancel md)))
  (VALID: ✓ rs)
  :  
  refines_lmod
    (Mod.to_lmod (MInline.inline false (MainSMod.to_mod (sp_from md) md)) rs)
    (Mod.to_lmod (MInline.inline false (SMod.to_mod (sp_from md) md)) rs).
Proof using.
  r. intro arg. eapply gsim_adequacy.
  instantiate (1:= smj_top). instantiate (1:= smj_top).
  unfold LMod.compile. s. rewrite /ITree.map /LModTr.trans /LModTr.interp_callE.  

  rewrite !alist_find_map_snd.
  rewrite !MainSMod.alist_find_map_fnsems.
  destruct (alist_find None (SMod.fnsems md)) eqn: FIND; cycle 1.
  { s. ired. ginit. gstep. econs. econs. ss. }
  s. ired. rewrite /ModTr.trans_ktree.
  destruct f as [[[img msk] scp] [fspo bd]]. s.
  assert (SCP: incl scp (SMod.scopes md)).
  { ii. eapply SMod.well_scoped_fns. rewrite /fnsems_scopes. erewrite FIND. et. }
  erewrite !sandbox_inline_commute; et.
  rewrite /SB.sandbox_body. s.

  ginit. guclo bindC_spec. econs; cycle 1.
  { instantiate (1:=cancel_eq). i. gstep. econs. econs.
    destruct SIM. des. et. }

  r in WFS. hexploit WFS; eauto; i; des; ss.
  hexploit H1; eauto; i; subst; ss.

  ziter_l. zstep_l. ziter_l. zstep_l.
  exploit WFS; et. i; des; subst; ss.
  
  ginit. guclo bindC_spec. econs; cycle 1.
  { instantiate (1:=cancel_eq). i. gstep. econs. econs.
    destruct SIM. des. et. }
  ziter_l. zstep_l. ziter_l. zstep_l.
  exploit WFS; et. i; des; subst; ss.
