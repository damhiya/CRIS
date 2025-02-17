Require Import CRIS.

Require Import IncrI IncrA wsim_tactics.

Module IncrIA. Section IncrIA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !MapMGΓ Γ, !memGΓ Γ}.

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ := λ _ _ _, emp%I.

  Context (u_s u_t : univ_id) (n : level).
  Context (ginv_s : invspec) (spc_s spc_mem : string → option fspec).

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
    prep_l. prep_r.
  Admitted.
End IncrIA. End IncrIA.