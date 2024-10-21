Require Import Coqlib ITreelib sflib HexString.
Require Import Events Any IPM ImpPrelude IModL Skeleton.

Module FooName.

  Definition mn := "Foo".
    
  Definition fn (method: string) :=
    mn +:+ "." +:+ method.
  
  Definition foo := fn "foo".

End FooName.

Module FooSK.
  Definition t : Sk.t := [].
End FooSK.
