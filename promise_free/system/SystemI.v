Require Import CRIS.
Require Import SystemHeader PFMemHeader.

Definition tidmap : Type := gmap Ident.t nat.

Module SystemI. Section SystemI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes := ["System"].
  Definition v_tid := "System" ↯ "tid".
  Definition v_tids := "System" ↯ "tids".

  Definition _spawn
      (check_internal : itree crisE unit)
      : Ident.t * string * SAny.t → itree crisE unit :=
    λ '(my_tid, fn, arg),
      check_internal;;;
      cput v_tid my_tid;;;
      trigger (Call fn arg↑);;;
      System.terminate.

  Definition spawn
      (new_tid : tidmap → Ident.t → itree crisE Ident.t)
      : string * SAny.t → itree crisE unit :=
    λ '(fn, arg),
      'my_tid : Ident.t <- cgetU v_tid;;
      'tids : tidmap <- cgetU v_tids;;
      'new_mtid : Ident.t <- new_tid tids my_tid;;
      new_stid <- trigger (Spawn SystemHdr._spawn (new_mtid, fn, arg)↑);;
      let newtids : tidmap := <[new_mtid := new_stid]> tids in
      cput v_tids newtids.

  Definition yield (trigger_yield : Ident.t → itree crisE unit) : unit → itree crisE unit :=
    λ _,
      'tids : tidmap <- cgetU v_tids;;
      '(exist _ tid _) : _ <- trigger (Choose {tid : Ident.t | tid ∈ dom tids});;
      trigger_yield tid.

  Definition get_tid : () → itree crisE Ident.t :=
    λ _, cgetU v_tid.

  Definition alloc : nat → itree crisE Val.t :=
    λ sz,
      'tid : Ident.t <- get_tid ();;
      ccallU PFMemHdr.alloc (tid, Z.of_nat sz).

  Definition write : Loc.t * Val.t * Ordering.t → itree crisE Val.t :=
    λ '(loc, val, ord),
      'tid : Ident.t <- get_tid ();;
      ccallU PFMemHdr.write (tid, loc, val, ord).

  Definition read : Loc.t * Ordering.t → itree crisE Val.t :=
    λ '(loc, ord),
      'tid : Ident.t <- get_tid ();;
      ccallU PFMemHdr.read (tid, loc, ord).

  (* Parameterized functions *)
  Definition check_internal : itree crisE unit := Ret tt. (* skip *)

  (* provide conversion between module-tid and system-tid *)
  Definition trigger_Yield (nxt_mtid : Ident.t) : itree crisE unit :=
    'my_tid : Ident.t <- cgetU v_tid;;
    'tids : tidmap <- cgetU v_tids;;
    match tids !! nxt_mtid with
    | Some nxt_stid => 
       trigger (Yield nxt_stid);;;
       cput v_tid my_tid
    | None => triggerUB
    end.

  Definition new_tid (_ : tidmap) (tid : Ident.t) : itree crisE Ident.t :=
    ccallU PFMemHdr.spawn tid.

  Definition fnsems : alist (option string) (fnsem_type (option fspec * fbody)) :=
    [(Some SystemHdr._spawn,  (false, wmask_all, scopes, (None, cfunU (_spawn check_internal))));
     (Some SystemHdr.spawn,   (false, wmask_all, scopes, (None, cfunU (spawn new_tid))));
     (Some SystemHdr.yield,   (false, wmask_all, scopes, (None, cfunU (yield trigger_Yield))));
     (Some SystemHdr.get_tid, (false, wmask_all, scopes, (None, cfunU get_tid)));
     (Some SystemHdr.alloc,   (false, wmask_all, scopes, (None, cfunU alloc)));
     (Some SystemHdr.write,   (false, wmask_all, scopes, (None, cfunU write)));
     (Some SystemHdr.read,    (false, wmask_all, scopes, (None, cfunU read)))].

  Program Definition Mod: SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st :=
      [(v_tid, 1%positive↑); (v_tids, ({[1%positive := 0]} : tidmap)↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t : Mod.t := Seal.sealing CRIS (SMod.to_mod sp_none Mod).
End SystemI. End SystemI.
