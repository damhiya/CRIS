Require Export SchHeader.
Require Import CRIS.

Definition thpool : Type := list (nat * option SAny.t).

Definition choose_index `{GRA} (ths : thpool) : itree crisE (nat * nat) :=
  '(exist _ (mtid, stid) _) : _ <- trigger (Choose {p : nat * nat | ths.*1 !! p.1 = Some p.2});;
  Ret (mtid, stid).

Module SchI. Section SchI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := ["sch"].
  Definition v_ths : key := "sch" ↯ "ths".
  Definition v_tid : key := "sch" ↯ "tid".

  Definition inner_spawn : string * SAny.t → itree crisE unit :=
    λ '(fn, arg),
      rv <- ccallU (mk_fnsig fn SAny.t SAny.t) arg;;
      'ths : thpool <- cgetU v_ths;;
      'tid : nat <- cgetU v_tid;;
      match ths !! tid with
      | Some (stid, _) =>
          let ths2 := <[tid := (stid, Some rv)]> ths in
          cput v_ths ths2;;;
          Sch.terminate
      | _ => triggerUB
      end.

  Definition spawn : string * SAny.t → itree crisE nat :=
    λ '(fn, arg),
      'ths : thpool <- cgetU v_ths;;
      new_stid <- trigger (Spawn (fn_name SchHdr._spawn) (fn, arg)↑);;
      cput v_ths (ths ++ [(new_stid, None)]);;;
      Ret (length ths).

  Definition yield : unit → itree crisE unit :=
    λ _,
      (* sanity checking *)
      'ths : thpool <- cgetU v_ths;;
      tid <- trigger GetTid;;
      'mtid : nat <- cgetU v_tid;;
      match ths !! mtid with
      | Some (stid, _) => if (decide (stid = tid)) then Ret () else triggerUB
      | None => triggerUB
      end;;;
      (* yield *)
      '(mtid, stid) : _ <- choose_index ths;;
      cput v_tid mtid;;;
      trigger (Yield stid).

  Definition join : nat → itree crisE (option SAny.t) :=
    λ tid,
      (* possibly infinite loop while waiting for the thread to terminate *)
      orv <- (iterC (λ _,
        'ths : thpool <- cgetU v_ths;;
        match ths !! tid with
        | None => Ret (inr None)
        | Some (_, Some rv) => Ret (inr (Some rv))
        | Some (_, None) => '() : _ <- ccallU SchHdr.yield tt;; Ret (inl tt)
        end
      ) tt);;
      Ret orv.

  Definition fnsems : fnsemmap :=
    {[fid SchHdr._spawn # (msk_real (msk_scp scopes msk_true), (None, cfunU inner_spawn));
      fid SchHdr.spawn # (msk_real (msk_scp scopes msk_true), (None, cfunU spawn));
      fid SchHdr.yield # (msk_real (msk_scp scopes msk_true), (None, cfunU yield));
      fid SchHdr.join # (msk_real (msk_scp scopes msk_true), (None, cfunU join))
    ]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_ths # ([(0, None)] : thpool)↑; v_tid # 0↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.

  Lemma real : Mod.real_mod t.
  Proof. real_mod_solver. Qed.
End SchI. End SchI.
