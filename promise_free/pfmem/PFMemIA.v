Require Import CRIS.
Require Import PFMemHeader PFMemI PFMemA HistoryRA AtomicRA.
Require Import base Time TView View Cell Memory Global Time.
Require Import
  PFMemIAproof PFMemIAInit PFMemIAAlloc PFMemIAFree PFMemIAWrite PFMemIARead
  PFMemIACAS PFMemIAFence PFMemIASpawn.

Module PFMemIA. Section PFMemIA.
  Context `{!crisG Γ Σ α β τ _S _I, !histG, !atomicG}.

  Lemma ctxr sp syn size :
    ctx_refines
      (PFMemA.t sp, True%I)
      (PFMemI.t syn size, emp%I).
  Proof using.
    eapply main_adequacy with (Ist := PFMemIA.Ist).
    init_sim.
    { split; first done. iIntros "_"; ss. admit. }
    { apply simF_alloc. }
    { apply simF_free. }
    { apply simF_read. }
    { apply simF_write. }
    { apply simF_cas. }
    { apply simF_fence. }
    (* { apply simF_init. } *)
    { apply simF_spawn. }
  Admitted.
End PFMemIA. End PFMemIA.