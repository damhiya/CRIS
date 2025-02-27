Require Import CRIS.

Require Import SchHeader.
Require Import ImpPrelude.

Require Import SpinLockHeader.
Require Import MemA MemHeader.

(* Using CAS *)

(*

void acquire(int* lock) {
    int expected = 0;
    // Spin until the lock is acquired
    while (!compare_and_set(lock, &expected, 1)){
      expected = 1;
    }; // Try to set it to 1 (locked)
}

// Unlock the spinlock
void release(int *lock) {
    lock = 0;  // Set lock to 0 (unlocked)
}

*)


Module SpinLockI.
Section SPINLOCK_I.

  Context `{Σ: GRA}.  

  Definition scopes := ["Spinlock"].

  Definition new_lock: unit -> itree pmodE val := 
    fun _ =>
      Sch.yield;;;
      'locked: val <- ccallU MemName.alloc [Vint 1];;
      Sch.yield;;;
      '_: val <- ccallU MemName.store [locked; Vint 0];;
      Sch.yield;;;
      Ret locked
      .

  Definition acquire: val -> itree pmodE unit :=
    fun arg =>
      Sch.yield;;;
      _ <- (ITree.iter (fun (arg' : val) => 
        Sch.yield;;;
        'b: val <- ccallU MemName.cas [arg; Vint 0; Vint 1];;
        Sch.yield;;;
        if ((dec b (Vint 1)))
        then Ret (inr tt)
        else Ret (inl arg')
      ) arg);;
      Sch.yield;;;
      Ret tt.

  Definition release: val -> itree pmodE unit := 
    fun arg => 
      Sch.yield;;; 
      '_: val <- ccallU MemName.store [arg; Vint 0];;
      Sch.yield;;;
      Ret tt.

  Definition fnsems := 
    [(SpinLockName.new_lock, (scopes, cfunU new_lock));
    (SpinLockName.acquire, (scopes, cfunU acquire));
    (SpinLockName.release, (scopes, cfunU release))
    ].
  
  Program Definition Mod: PMod.t := {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems;
    PMod.initial_st := [];
  |}
  .
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.


  Definition t: HMod.t := Seal.sealing CRIS (PMod.to_hmod Mod).

End SPINLOCK_I.
End SpinLockI.