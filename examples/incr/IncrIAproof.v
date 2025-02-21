(* Require Import CRIS.

Require Import IncrI IncrA SchA wsim_tactics wsim_sch.

Module IncrIA. Section IncrIA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !MapMGΓ Γ, !SchAGΣ Σ, !memGΓ Γ}.

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ := λ _ _ _, emp%I.

  Context (u_s u_t : univ_id) (n : level).
  Context (ginv_s : invspec) (spc_s spc_user_s spc_mem : string → option fspec).
  Context (SchInSpc : spc_incl (SchAS.spc u_s n spc_user_s) spc_s).

  Local Notation MemA := (MemA.t ginv_s spc_mem).
  Local Notation IncrA := (IncrA.t u_s n ginv_s spc_s ★ MemA).
  Local Notation IncrI := (IncrI.t ★ MemA).
  Local Notation IstFull := (IstProd (IstSB IncrA.(HMod.scopes) Ist) IstEq).

  Lemma simF_incr : HSim.sim_fun open IncrA IncrI IstFull IncrName.incr.
  Proof.
    init_wsim u_s u_t n.

    w_steps_l.
    iDestruct "ASM" as "[-> ->]". hss. rename q1 into blk, q2 into ofs.

    w_steps_l. w_steps_r.

    _prep_macro_l; _prep_macro_r.
    iApply (wsim_yield); first done.
    iSplitL "IST"; iFrame.
    clear nths. iIntros (nths st_s st_t) "IST".

    w_steps_r.
    iApply wsim_reset. iStopProof.
    revert nths. combine_quant st_s. combine_quant st_t.
    eapply wsim_coind.
    iIntros (g' [st_t [st_s nths]]) "IST #MON #CIH /=".

    unfold_iter_r.
    _prep_macro_r.
    iApply (wsim_yield); first done.
    iSplitL "IST"; iFrame.
    clear nths st_s st_t. iIntros (nths st_s st_t) "IST".

    w_inline_r.
    w_steps_r.
    (* TODO : Stuck here *)
    (* w_force_r () *)

  Admitted.
End IncrIA. End IncrIA. *)