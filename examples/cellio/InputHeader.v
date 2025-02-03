Require Import CRIS.

Module InputName.

  Definition mn := "Input".
    
  Definition fn (method: string) :=
    mn +:+ "." +:+ method.
  
  Definition input := fn "input".

End InputName.
