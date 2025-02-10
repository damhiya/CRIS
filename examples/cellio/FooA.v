Require Import CRIS.
Require Import MainHeader CellioHeader InputHeader FooHeader.

Require Import CellioA MainA InputA.

Set Implicit Arguments.

Module FooAS.
Section FooAS.
  Context `{Σ: GRA}.

  Definition Spc: alist string fspec :=
    Seal.sealing CRIS [(FooName.foo, fspec_trivial)].
  
  Lemma Spc_nodup: List.NoDup (List.map fst Spc).
  Proof.
    unfold Spc. unseal CRIS. prove_nodup.
  Qed.

End FooAS. End FooAS.

Module FooA. Section FooA.
  Context `{Σ: GRA}.
  (* Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !CellioAGΓ Γ}. *)
  
  (* Unknown function body. Shouldn't call functions in local modules *)
  Variable foo: Any.t -> itree hmodE Any.t.
  (* 
    need some better idea to specify the list of local function names 
    without linking all local modules at this moment.
  *)
  (* Local Definition modules := (CellioA.t ginv Spc) ★ (MainA.t ginv Spc) ★ (InputA.t ginv Spc). *)  
  Local Definition local_fns 
    := [CellioName.set; CellioName.get; MainName.main; InputName.input].

  Local Definition handle_call: callE ~> itree hmodE :=
    λ _ '(Call fn varg), 
      match (existsb (String.eqb fn) local_fns) with
      | true => triggerUB
      | false => trigger (Call fn varg)
      end.

  Local Definition interp_body R (it : itree hmodE R) : itree hmodE R :=
    interp (case_ (bif:=sum1) trivial_Handler
           (case_ (bif:=sum1) trivial_Handler
           (case_ (bif:=sum1) handle_call
                              trivial_Handler))) it.

  Local Definition interp_fun (f : Any.t -> itree hmodE Any.t) : Any.t -> itree hmodE Any.t :=
    λ x, interp_body (f x).

  Definition scopes := [FooName.mn].
  
  Definition fnsems : alist string (list string * fspecbody) :=
    [(FooName.foo, (scopes, mk_specbody fspec_trivial (interp_fun foo)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition InitCond : iProp Σ := emp%I.

  Definition InitRes : Σ := ε.

  Definition t ginv Spc := Seal.sealing CRIS (SMod.to_hmod ginv Spc Mod).
End FooA. End FooA.
