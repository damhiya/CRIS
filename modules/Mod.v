Require Import Coqlib.
Require Import sflib.
Require Import ITreelib.
Require Import AList.
Require Import Skeleton.
Require Import STS Behavior.
Require Import Any.
Require Import Program.
Require Import Mod2STS.
Require Import Events.

Set Implicit Arguments.

Section ADD.

  Definition RUN : Type := forall V, (Any.t -> Any.t * V) -> (Any.t -> Any.t * V).

  Definition run_l: RUN := 
    fun _ run st =>
      match Any.split st with
      | Some (a, b) => let (a', v) := run a in (Any.pair a' b, v)
      | None => run tt↑
      end.

  Definition run_r: RUN := 
    fun _ run st =>
      match Any.split st with
      | Some (a, b) => let (b', v) := run b in (Any.pair a b', v)
      | None => run tt↑
      end.

End ADD.

Module ModSem.
  Section MODSEM.

    Record t: Type := mk {
      initial_st : Any.t;
      fnsems : alist gname (Any.t -> itree modE Any.t);
    }.

    Record wf (ms: t): Prop := mk_wf {
      wf_fnsems: List.NoDup (List.map fst ms.(fnsems));
    }.

    Definition empty: t := {|
      initial_st := tt↑;
      fnsems := [];
    |}.

    Definition init (body: itree modE Any.t) : t := {|
      initial_st := tt↑;
      fnsems := [("CCR_init", fun _ => body)];
    |}.

    Section COMPILE.
    
      Variable ms: t.

      Definition prog: callE ~> itree modE :=
        fun _ '(Call fn args) =>
          sem <- (alist_find fn ms.(fnsems))?;;
          sem args.

      Definition initial_itr : itree coreE Any.t :=
        snd <$> interp_modE prog (prog (Call "CCR_init" ()↑)) (initial_st ms).

      Definition compile : semantics:=
        compile_itree (initial_itr).

    End COMPILE.
  End MODSEM.
End ModSem.
