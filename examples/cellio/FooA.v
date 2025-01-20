Require Import CRIS.
Require Import MainHeader CellioHeader InputHeader FooHeader.

Require Import CellioA MainA InputA.

Set Implicit Arguments.

Module FooA. Section FooA.
  Context `{Σ: GRA}.
  (* Context `{!invG α Σ Γ, !subHG Γ Σ, !sinvG Σ Γ α β τ, !CellioAGΓ Γ}. *)
  
  (* Unknown function body. Shouldn't call functions in local modules *)
  Variable foo: Any.t -> itree hmodE Any.t.
  (* 
    need some better idea to specify the list of local function names 
    without linking all local modules at this moment.
  *)
  (* Local Definition modules := (CellioA.t ginv GlobalStb) ★ (MainA.t ginv GlobalStb) ★ (InputA.t ginv GlobalStb). *)  
  Local Definition local_fns 
    := [CellioName.set; CellioName.get; MainName.main; InputName.input].

  Local Definition handle_call: callE ~> itree hmodE :=
    λ _ '(Call fn varg), 
      match (existsb (String.eqb fn) local_fns) with
      | true => trigger (Call fn varg)
      | false => triggerUB
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

  Program Definition Sem : SModSem.t := {|
    SModSem.scopes := scopes;
    SModSem.fnsems := fnsems;
    SModSem.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition Mod : SMod.t := {|
    SMod.modsem := λ _, Sem;
    SMod.sk := FooSK.t;
  |}.

  Definition InitCond : Sk.t -> iProp Σ :=
    λ _, emp%I.

  Definition InitRes : Σ := ε.

  Variable ginv: Sk.t -> invspec.
  Variable GlobalStb: Sk.t -> string -> option fspec.

  Definition t := Seal.sealing CRIS (SMod.to_hmod ginv GlobalStb Mod).
End FooA. End FooA.
