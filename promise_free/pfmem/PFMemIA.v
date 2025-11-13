Require Import CRIS.
Require Import PFMemHeader PFMemI PFMemA HistoryRA AtomicRA.
Require Import base Time TView View Cell Memory Global Time.
Require Import
  PFMemIAproof PFMemIAInit PFMemIAAlloc PFMemIAFree PFMemIAWrite PFMemIARead
  PFMemIACAS PFMemIAFence PFMemIASpawn.

Module PFMemIA. Section PFMemIA.
  Context `{!crisG Γ Σ α β τ _S _I, !concG, !histG, !atomicG}.

  (* Lemma hist_au *)
  Lemma ctxr sp :
    ctx_refines
      (PFMemA.t sp, PFMemA.init_cond)
      (PFMemI.t PFMemA.syn [], emp%I).
  Proof using.
    eapply main_adequacy with (Ist := PFMemIA.Ist).
    init_sim.
    { split; first done. iIntros "[TVA [HA HFA]]"; ss.
      rewrite /PFMemIA.Ist.
      iExists (Global.init []), _, (View.init []); iSplit; cycle 1.
      { iFrame. rewrite Memory.cut_init //. }
      { admit. }
    }
    { apply simF_alloc. }
    { apply simF_free. }
    { apply simF_read. }
    { apply simF_write. }
    { apply simF_cas. }
    { apply simF_fence. }
    { apply simF_spawn. }
  Admitted.
End PFMemIA. End PFMemIA.