Require Import CRIS.

Require Import SchHeader.

Set Implicit Arguments.

Definition thslist: Type := list (nat * (option SAny.t)).

Definition is_in_thslist (tid: nat) (ths: thslist) :=
  is_some (alist_find tid ths).

Module SchI. Section SchI.
  Local Open Scope string_scope.
  Context `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ}.

  Definition scopes := ["Sch"].
  Definition v_ths := "Sch" ↯ "ths".

  Definition _spawn: (nat * gname * SAny.t) -> itree pmodE unit :=
    fun '(mtid, fn, arg) =>
      trigger (Yield mtid);;;
      'rv: SAny.t <- ccallU fn arg;;
      mytid <- trigger Tid;;
      'ths: thslist <- cgetU v_ths;;
      let newths: thslist := alist_replace mytid (Some rv) ths in
      cput v_ths newths;;;
      Sch.terminate
  .

  Definition spawn: (gname * SAny.t) -> itree pmodE nat :=
    fun '(fn, arg) =>
      mtid <- trigger Tid;;
      tid <- trigger (Spawn SchName._spawn (mtid, fn, arg)↑);;
      'ths: thslist <- cgetU v_ths;;
      let newths: thslist := alist_add tid None ths in
      cput v_ths newths;;;
      trigger (Yield tid);;;
      Ret tid
  .

  Definition yield: unit -> itree pmodE unit :=
    fun _ =>
      'ths: thslist <- cgetU v_ths;;
      'ntid: nat <- trigger (Choose nat);;
      guarantee (is_in_thslist ntid ths);;;
      trigger (Yield ntid)
  .

  Definition join: nat -> itree pmodE (option SAny.t) :=
    fun tid =>
      orv <- (ITree.iter (fun _ =>
        'ths: thslist <- cgetU v_ths;;
        match alist_find tid ths with
        | None => Ret (inr None)
        | Some (Some rv) => Ret (inr (Some rv))
        | Some None =>
            '(): _ <- ccallU SchName.yield tt;;
            Ret (inl tt)
        end
      ) tt);;
      Ret orv
  .

  Definition fnsems :=
    [(SchName._spawn, (scopes, cfunU _spawn));
     (SchName.spawn, (scopes, cfunU spawn));
     (SchName.yield, (scopes, cfunU yield));
     (SchName.join, (scopes, cfunU join))].
  
  Program Definition Sem: PModSem.t :=
  {|
    PModSem.scopes := scopes;
    PModSem.fnsems := fnsems;
    PModSem.initial_st := [(v_ths, ([(0, None)]: thslist)↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod: PMod.t := 
  {|
    PMod.modsem := fun _ => Sem;
    PMod.sk := SchSK.t;
  |}.

  Definition t := Seal.sealing "ccr" (PMod.to_hmod Mod).

End SchI. End SchI.