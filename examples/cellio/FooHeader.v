Require Import CRIS.

Module FooName.

  Definition mn := "Foo".
    
  Definition fn (method: string) :=
    mn +:+ "." +:+ method.
  
  Definition foo := fn "foo".

End FooName.
