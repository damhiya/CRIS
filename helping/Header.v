Require Import CRIS.

Module Helping. Section Helping.

  Context `{Σ: GRA}.
  Context (mn : string).

  Definition run  := mn +:+ ".run".
  Definition help  := mn +:+ ".help".

  Definition pureE := agE +' coreE.

  Definition trans {R} (itr: itree pureE R) : itree crisE R :=
    translate (case_ (bif:=sum1) subevent subevent) itr.

  Definition exports := [run; help].

End Helping. End Helping.