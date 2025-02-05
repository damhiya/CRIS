Require Import CRIS.

Module MainName.

  Definition mn := "Main".
    
  Definition fn (method: string) :=
    mn +:+ "." +:+ method.
  
  (* Definition main := fn "main". *)
  Definition main := "CRIS_init".

End MainName.

Module MainSK.
  Definition t : Sk.t := [].
End MainSK.
