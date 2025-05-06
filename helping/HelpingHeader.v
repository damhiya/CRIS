Require Import CRIS.

Require Export ImpPrelude.

Module Helping.
Section Helping.

  Variable mn : string.
  
  Definition run  := mn +:+ ".run".
  Definition help  := mn +:+ ".help".

  Context `{Σ: GRA}.
  
  Definition pureE := agE +' coreE.

  Definition trans {R} (itr: itree pureE R) : itree hmodE R
    :=
    translate (case_ (bif:=sum1) subevent subevent) itr.

  Definition exports := [run; help].
  
End Helping.
End Helping.


(* Section RA. *)
(*   Context `{!sinvG Γ Σ α β τ _I _S}. *)

(*   Definition helpingRA : ucmra :=  optionUR (exclR (leibnizO (string * SAny.t))). *)
  
(*   Class helpingG `{!sinvG Γ Σ α β τ _I _S} := { *)
(*     helping_inG :: inG helpingRA Γ; *)
(*   }. *)
(*   Definition helpingΓ : HRA := #[helpingRA]. *)
(*   Global Instance helping_subG : subG helpingΓ Γ → helpingG. *)
(*   Proof. solve_inG. Defined. *)
(* End RA. *)
(* Hint Unfold helping_subG helping_inG : GRA_index. *)

(* Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}. *)
(* Context `{_helpingG: !helpingG}. *)

(* Definition has_fun_r f arg : helpingRA := Some (Excl (f, arg)). *)
(* Definition has_fun γ f arg : iProp Σ := own γ (has_fun_r f arg). *)

(* Definition has_none_r : helpingRA := None. *)
(* Definition has_non γ : iProp Σ := own γ has_none_r. *)
