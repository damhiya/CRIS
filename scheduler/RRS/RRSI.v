Require Import CRIS.
Require Import RRSHeader SchHeader.

Definition thpool : Type := list nat.

Module RRSI. Section RRSI.
  Context `{!crisG Γ Σ α β τ _S _I, !concG}.

  (* Context (parent_yield : string). *)

  Definition scopes := [RRS].
  Definition v_ths := RRS ↯ "ths".
  Definition v_tid := RRS ↯ "tid".
  Definition v_sch := RRS ↯ "sch".

  (* function which would be called by "spawn" of parent scheduler *)
  Definition init : string → itree crisE unit :=
    λ fn,
      (* initialize RRS with given function *)
      stid <- trigger GetTid;;
      cput v_sch stid;;;
      'ths: thpool <- cgetU v_ths;;
      new_stid <- trigger (Spawn RRSHdr._spawn (fn, tt↑↑)↑);;
      cput v_ths (ths ++ [new_stid]);;;
      cput v_tid (length ths);;;
      trigger (Yield new_stid);;;
      (* infinite global yield *)
      iterC (λ _,
        trigger (Call SchHdr.yield tt↑);;;
        'ths: thpool <- cgetU v_ths;;
        'mtid: nat <- cgetU v_tid;;
        match ths !! mtid with
        | Some stid => trigger (Yield stid);;; Ret (inl tt)
        | None => triggerUB
        end
      ) tt.

  (* spawnable function *)
  Definition inner_spawn : string * SAny.t → itree crisE unit :=
    λ '(fn, arg),
      trigger (Call fn arg↑);;;
      RRS.spin.

  Definition spawn : string * SAny.t → itree crisE nat :=
    λ '(fn, arg),
      'ths : thpool <- cgetU v_ths;;
      new_stid <- trigger (Spawn RRSHdr._spawn (fn, arg)↑);;
      cput v_ths (ths ++ [new_stid]);;;
      Ret (length ths).

  Definition yield : unit → itree crisE unit :=
    λ _,
      (* sanity checking *)
      'ths : thpool <- cgetU v_ths;;
      tid <- trigger GetTid;;
      'mtid : nat <- cgetU v_tid;;
      match ths !! mtid with
      | Some stid => if (decide (stid = tid)) then Ret () else triggerUB
      | None => triggerUB
      end;;;
      (* yield *)
      let mtid : nat := succ_rr mtid (length ths) in
      match ths !! mtid with
      | Some stid =>
          cput v_tid mtid;;;
          trigger (Yield stid)
      | None => triggerUB
      end.

  Definition yield_global : unit → itree crisE unit :=
    λ _,
      'sch: nat <- cgetU v_sch;;
      trigger (Yield sch).

  Definition get_tid : unit → itree crisE nat :=
    λ _, cgetU v_tid.

  Definition fnsems : fnsems_type :=
    [(Some RRSHdr.init,        (false, wmask_all, scopes, (None, cfunU init)));
     (Some RRSHdr._spawn,      (false, wmask_all, scopes, (None, cfunU inner_spawn)));
     (Some RRSHdr.spawn,       (false, wmask_all, scopes, (None, cfunU spawn)));
     (Some RRSHdr.yield,       (false, wmask_all, scopes, (None, cfunU yield)));
     (Some RRSHdr.yield_global,(false, wmask_all, scopes, (None, cfunU yield_global)));
     (Some RRSHdr.get_tid,     (false, wmask_all, scopes, (None, cfunU get_tid)))].

  Program Definition smod: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [(v_ths, ([] : thpool)↑); (v_tid, 0↑); (v_sch, 0↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (SMod.to_mod sp_none smod).
End RRSI. End RRSI.
