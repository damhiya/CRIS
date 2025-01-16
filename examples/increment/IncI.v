Require Import CRIS.
Require Import ImpPrelude.

Module IncI. Section IncI.
  Definition inc : val → itree pmodE val :=
    λ args,
      '(b, ofs) : mblock * ptrofs <- (pargs [Tptr] [args])?;;
      Ret (Vptr b ofs).