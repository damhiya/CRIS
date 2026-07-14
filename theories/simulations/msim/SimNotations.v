From CRIS.common Require Import Common.
From iris.proofmode Require Import coq_tactics environments.

From CRIS.simulations.msim Require Export ISim WSim.
From CRIS.modules Require Export Mod.

Global Arguments Envs _ _%_proof_scope _%_proof_scope _.
Global Arguments Enil {_}.
Global Arguments Esnoc {_} _%_proof_scope _%_string _%_I.

(***************
 Map Notations
 **************)

Notation "m1 +# m2" := (union_with uwnd m1 m2) (at level 1) : stdpp_scope.

(*** Some on RHS ***)

Notation "{[ k1 # a1 ]}" := (singletonM k1 (Some a1))
  (at level 1, format
  "{[ k1  #  a1 ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ]}" :=
  (<[ k1 := Some a1 ]> {[ k2 := Some a2 ]})
  (at level 1, format
  "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> {[ k3 := Some a3 ]})
  (at level 1, format
  "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> {[ k4 := Some a4 ]})
  (at level 1, format
  "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> {[ k5 := Some a5 ]})
  (at level 1, format
  "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> {[ k6 := Some a6 ]})
  (at level 1, format
  "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> {[ k7 := Some a7 ]})
  (at level 1, format
  "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> {[ k8 := Some a8 ]})
  (at level 1, format
  "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> {[ k9 := Some a9 ]})
  (at level 1, format
  "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ; k10 # a10 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> $
    <[ k9 := Some a9 ]> {[ k10 := Some a10 ]})
  (at level 1, format
  "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ;  ']' '/' '[' k10  #  a10 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ; k10 # a10 ; k11 # a11 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> $
    <[ k9 := Some a9 ]> $ <[ k10 := Some a10 ]> {[ k11 := Some a11 ]})
  (at level 1, format
  "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ;  ']' '/' '[' k10  #  a10 ;  ']' '/' '[' k11  #  a11 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ; k10 # a10 ; k11 # a11 ; k12 # a12 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> $
    <[ k9 := Some a9 ]> $ <[ k10 := Some a10 ]> $ <[ k11 := Some a11 ]> {[ k12 := Some a12 ]})
  (at level 1, format
  "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ;  ']' '/' '[' k10  #  a10 ;  ']' '/' '[' k11  #  a11 ;  ']' '/' '[' k12  #  a12 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ; k10 # a10 ; k11 # a11 ; k12 # a12 ; k13 # a13 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> $
    <[ k9 := Some a9 ]> $ <[ k10 := Some a10 ]> $ <[ k11 := Some a11 ]> $ <[ k12 := Some a12 ]> {[ k13 := Some a13 ]})
  (at level 1, format
                 "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ;  ']' '/' '[' k10  #  a10 ;  ']' '/' '[' k11  #  a11 ;  ']' '/' '[' k12  #  a12 ;  ']' '/' '[' k13  #  a13 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ; k10 # a10 ; k11 # a11 ; k12 # a12 ; k13 # a13 ; k14 # a14 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> $
    <[ k9 := Some a9 ]> $ <[ k10 := Some a10 ]> $ <[ k11 := Some a11 ]> $ <[ k12 := Some a12 ]> $ <[ k13 := Some a13 ]> {[ k14 := Some a14 ]})
  (at level 1, format
                 "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ;  ']' '/' '[' k10  #  a10 ;  ']' '/' '[' k11  #  a11 ;  ']' '/' '[' k12  #  a12 ;  ']' '/' '[' k13  #  a13 ;  ']' '/' '[' k14  #  a14 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ; k10 # a10 ; k11 # a11 ; k12 # a12 ; k13 # a13 ; k14 # a14 ; k15 # a15 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> $
    <[ k9 := Some a9 ]> $ <[ k10 := Some a10 ]> $ <[ k11 := Some a11 ]> $ <[ k12 := Some a12 ]> $ <[ k13 := Some a13 ]> $ <[ k14 := Some a14 ]> {[ k15 := Some a15 ]})
  (at level 1, format
                 "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ;  ']' '/' '[' k10  #  a10 ;  ']' '/' '[' k11  #  a11 ;  ']' '/' '[' k12  #  a12 ;  ']' '/' '[' k13  #  a13 ;  ']' '/' '[' k14  #  a14 ;  ']' '/' '[' k15  #  a15 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ; k10 # a10 ; k11 # a11 ; k12 # a12 ; k13 # a13 ; k14 # a14 ; k15 # a15 ; k16 # a16 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> $
    <[ k9 := Some a9 ]> $ <[ k10 := Some a10 ]> $ <[ k11 := Some a11 ]> $ <[ k12 := Some a12 ]> $ <[ k13 := Some a13 ]> $ <[ k14 := Some a14 ]> $ <[ k15 := Some a15 ]> {[ k16 := Some a16 ]})
  (at level 1, format
                 "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ;  ']' '/' '[' k10  #  a10 ;  ']' '/' '[' k11  #  a11 ;  ']' '/' '[' k12  #  a12 ;  ']' '/' '[' k13  #  a13 ;  ']' '/' '[' k14  #  a14 ;  ']' '/' '[' k15  #  a15 ;  ']' '/' '[' k16  #  a16 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ; k10 # a10 ; k11 # a11 ; k12 # a12 ; k13 # a13 ; k14 # a14 ; k15 # a15 ; k16 # a16 ; k17 # a17 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> $
    <[ k9 := Some a9 ]> $ <[ k10 := Some a10 ]> $ <[ k11 := Some a11 ]> $ <[ k12 := Some a12 ]> $ <[ k13 := Some a13 ]> $ <[ k14 := Some a14 ]> $ <[ k15 := Some a15 ]> $ <[ k16 := Some a16 ]> {[ k17 := Some a17 ]})
  (at level 1, format
                 "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ;  ']' '/' '[' k10  #  a10 ;  ']' '/' '[' k11  #  a11 ;  ']' '/' '[' k12  #  a12 ;  ']' '/' '[' k13  #  a13 ;  ']' '/' '[' k14  #  a14 ;  ']' '/' '[' k15  #  a15 ;  ']' '/' '[' k16  #  a16 ;  ']' '/' '[' k17  #  a17 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ; k10 # a10 ; k11 # a11 ; k12 # a12 ; k13 # a13 ; k14 # a14 ; k15 # a15 ; k16 # a16 ; k17 # a17 ; k18 # a18 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> $
    <[ k9 := Some a9 ]> $ <[ k10 := Some a10 ]> $ <[ k11 := Some a11 ]> $ <[ k12 := Some a12 ]> $ <[ k13 := Some a13 ]> $ <[ k14 := Some a14 ]> $ <[ k15 := Some a15 ]> $ <[ k16 := Some a16 ]> $ <[ k17 := Some a17 ]> {[ k18 := Some a18 ]})
  (at level 1, format
                 "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ;  ']' '/' '[' k10  #  a10 ;  ']' '/' '[' k11  #  a11 ;  ']' '/' '[' k12  #  a12 ;  ']' '/' '[' k13  #  a13 ;  ']' '/' '[' k14  #  a14 ;  ']' '/' '[' k15  #  a15 ;  ']' '/' '[' k16  #  a16 ;  ']' '/' '[' k17  #  a17 ;  ']' '/' '[' k18  #  a18 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ; k10 # a10 ; k11 # a11 ; k12 # a12 ; k13 # a13 ; k14 # a14 ; k15 # a15 ; k16 # a16 ; k17 # a17 ; k18 # a18 ; k19 # a19 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> $
    <[ k9 := Some a9 ]> $ <[ k10 := Some a10 ]> $ <[ k11 := Some a11 ]> $ <[ k12 := Some a12 ]> $ <[ k13 := Some a13 ]> $ <[ k14 := Some a14 ]> $ <[ k15 := Some a15 ]> $ <[ k16 := Some a16 ]> $ <[ k17 := Some a17 ]> $ <[ k18 := Some a18 ]> {[ k19 := Some a19 ]})
  (at level 1, format
                 "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ;  ']' '/' '[' k10  #  a10 ;  ']' '/' '[' k11  #  a11 ;  ']' '/' '[' k12  #  a12 ;  ']' '/' '[' k13  #  a13 ;  ']' '/' '[' k14  #  a14 ;  ']' '/' '[' k15  #  a15 ;  ']' '/' '[' k16  #  a16 ;  ']' '/' '[' k17  #  a17 ;  ']' '/' '[' k18  #  a18 ;  ']' '/' '[' k19  #  a19 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 # a1 ; k2 # a2 ; k3 # a3 ; k4 # a4 ; k5 # a5 ; k6 # a6 ; k7 # a7 ; k8 # a8 ; k9 # a9 ; k10 # a10 ; k11 # a11 ; k12 # a12 ; k13 # a13 ; k14 # a14 ; k15 # a15 ; k16 # a16 ; k17 # a17 ; k18 # a18 ; k19 # a19 ; k20 # a20 ]}" :=
  (<[ k1 := Some a1 ]> $ <[ k2 := Some a2 ]> $ <[ k3 := Some a3 ]> $ <[ k4 := Some a4 ]> $
    <[ k5 := Some a5 ]> $ <[ k6 := Some a6 ]> $ <[ k7 := Some a7 ]> $ <[ k8 := Some a8 ]> $
    <[ k9 := Some a9 ]> $ <[ k10 := Some a10 ]> $ <[ k11 := Some a11 ]> $ <[ k12 := Some a12 ]> $ <[ k13 := Some a13 ]> $ <[ k14 := Some a14 ]> $ <[ k15 := Some a15 ]> $ <[ k16 := Some a16 ]> $ <[ k17 := Some a17 ]> $ <[ k18 := Some a18 ]> $ <[ k19 := Some a19 ]> {[ k20 := Some a20 ]})
  (at level 1, format
                 "{[ '[hv' '[' k1  #  a1 ;  ']' '/' '[' k2  #  a2 ;  ']' '/' '[' k3  #  a3 ;  ']' '/' '[' k4  #  a4 ;  ']' '/' '[' k5  #  a5 ;  ']' '/' '[' k6  #  a6 ;  ']' '/' '[' k7  #  a7 ;  ']' '/' '[' k8  #  a8 ;  ']' '/' '[' k9  #  a9 ;  ']' '/' '[' k10  #  a10 ;  ']' '/' '[' k11  #  a11 ;  ']' '/' '[' k12  #  a12 ;  ']' '/' '[' k13  #  a13 ;  ']' '/' '[' k14  #  a14 ;  ']' '/' '[' k15  #  a15 ;  ']' '/' '[' k16  #  a16 ;  ']' '/' '[' k17  #  a17 ;  ']' '/' '[' k18  #  a18 ;  ']' '/' '[' k19  #  a19 ;  ']' '/' '[' k20  #  a20 ']' ']' ]}") : stdpp_scope.

(*** fspec_to_rel on RHS ***)

Notation "{[ k1 @ a1 ]}" := (singletonM (k1) (fspec_to_rel a1) : gmap fname fspec_rel)
  (at level 1, format
  "{[ k1  @  a1 ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> {[ k2 := fspec_to_rel a2 ]} : gmap fname fspec_rel)
  (at level 1, format
  "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> {[ k3 := fspec_to_rel a3 ]} : gmap fname fspec_rel)
  (at level 1, format
  "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> {[ k4 := fspec_to_rel a4 ]} : gmap fname fspec_rel)
  (at level 1, format
  "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> {[ k5 := fspec_to_rel a5 ]} : gmap fname fspec_rel)
  (at level 1, format
  "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> {[ k6 := fspec_to_rel a6 ]} : gmap fname fspec_rel)
  (at level 1, format
  "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> {[ k7 := fspec_to_rel a7 ]} : gmap fname fspec_rel)
  (at level 1, format
  "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> {[ k8 := fspec_to_rel a8 ]} : gmap fname fspec_rel)
  (at level 1, format
  "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> {[ k9 := fspec_to_rel a9 ]} : gmap fname fspec_rel)
  (at level 1, format
  "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ; k10 @ a10 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> $
    <[ k9 := fspec_to_rel a9 ]> {[ k10 := fspec_to_rel a10 ]} : gmap fname fspec_rel)
  (at level 1, format
  "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ;  ']' '/' '[' k10  @  a10 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ; k10 @ a10 ; k11 @ a11 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> $
    <[ k9 := fspec_to_rel a9 ]> $ <[ k10 := fspec_to_rel a10 ]> {[ k11 := fspec_to_rel a11 ]} : gmap fname fspec_rel)
  (at level 1, format
  "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ;  ']' '/' '[' k10  @  a10 ;  ']' '/' '[' k11  @  a11 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ; k10 @ a10 ; k11 @ a11 ; k12 @ a12 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> $
    <[ k9 := fspec_to_rel a9 ]> $ <[ k10 := fspec_to_rel a10 ]> $ <[ k11 := fspec_to_rel a11 ]> {[ k12 := fspec_to_rel a12 ]} : gmap fname fspec_rel)
  (at level 1, format
  "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ;  ']' '/' '[' k10  @  a10 ;  ']' '/' '[' k11  @  a11 ;  ']' '/' '[' k12  @  a12 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ; k10 @ a10 ; k11 @ a11 ; k12 @ a12 ; k13 @ a13 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> $
    <[ k9 := fspec_to_rel a9 ]> $ <[ k10 := fspec_to_rel a10 ]> $ <[ k11 := fspec_to_rel a11 ]> $ <[ k12 := fspec_to_rel a12 ]> {[ k13 := fspec_to_rel a13 ]} : gmap fname fspec_rel)
  (at level 1, format
                 "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ;  ']' '/' '[' k10  @  a10 ;  ']' '/' '[' k11  @  a11 ;  ']' '/' '[' k12  @  a12 ;  ']' '/' '[' k13  @  a13 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ; k10 @ a10 ; k11 @ a11 ; k12 @ a12 ; k13 @ a13 ; k14 @ a14 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> $
    <[ k9 := fspec_to_rel a9 ]> $ <[ k10 := fspec_to_rel a10 ]> $ <[ k11 := fspec_to_rel a11 ]> $ <[ k12 := fspec_to_rel a12 ]> $ <[ k13 := fspec_to_rel a13 ]> {[ k14 := fspec_to_rel a14 ]} : gmap fname fspec_rel)
  (at level 1, format
                 "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ;  ']' '/' '[' k10  @  a10 ;  ']' '/' '[' k11  @  a11 ;  ']' '/' '[' k12  @  a12 ;  ']' '/' '[' k13  @  a13 ;  ']' '/' '[' k14  @  a14 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ; k10 @ a10 ; k11 @ a11 ; k12 @ a12 ; k13 @ a13 ; k14 @ a14 ; k15 @ a15 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> $
    <[ k9 := fspec_to_rel a9 ]> $ <[ k10 := fspec_to_rel a10 ]> $ <[ k11 := fspec_to_rel a11 ]> $ <[ k12 := fspec_to_rel a12 ]> $ <[ k13 := fspec_to_rel a13 ]> $ <[ k14 := fspec_to_rel a14 ]> {[ k15 := fspec_to_rel a15 ]} : gmap fname fspec_rel)
  (at level 1, format
                 "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ;  ']' '/' '[' k10  @  a10 ;  ']' '/' '[' k11  @  a11 ;  ']' '/' '[' k12  @  a12 ;  ']' '/' '[' k13  @  a13 ;  ']' '/' '[' k14  @  a14 ;  ']' '/' '[' k15  @  a15 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ; k10 @ a10 ; k11 @ a11 ; k12 @ a12 ; k13 @ a13 ; k14 @ a14 ; k15 @ a15 ; k16 @ a16 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> $
    <[ k9 := fspec_to_rel a9 ]> $ <[ k10 := fspec_to_rel a10 ]> $ <[ k11 := fspec_to_rel a11 ]> $ <[ k12 := fspec_to_rel a12 ]> $ <[ k13 := fspec_to_rel a13 ]> $ <[ k14 := fspec_to_rel a14 ]> $ <[ k15 := fspec_to_rel a15 ]> {[ k16 := fspec_to_rel a16 ]} : gmap fname fspec_rel)
  (at level 1, format
                 "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ;  ']' '/' '[' k10  @  a10 ;  ']' '/' '[' k11  @  a11 ;  ']' '/' '[' k12  @  a12 ;  ']' '/' '[' k13  @  a13 ;  ']' '/' '[' k14  @  a14 ;  ']' '/' '[' k15  @  a15 ;  ']' '/' '[' k16  @  a16 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ; k10 @ a10 ; k11 @ a11 ; k12 @ a12 ; k13 @ a13 ; k14 @ a14 ; k15 @ a15 ; k16 @ a16 ; k17 @ a17 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> $
    <[ k9 := fspec_to_rel a9 ]> $ <[ k10 := fspec_to_rel a10 ]> $ <[ k11 := fspec_to_rel a11 ]> $ <[ k12 := fspec_to_rel a12 ]> $ <[ k13 := fspec_to_rel a13 ]> $ <[ k14 := fspec_to_rel a14 ]> $ <[ k15 := fspec_to_rel a15 ]> $ <[ k16 := fspec_to_rel a16 ]> {[ k17 := fspec_to_rel a17 ]} : gmap fname fspec_rel)
  (at level 1, format
                 "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ;  ']' '/' '[' k10  @  a10 ;  ']' '/' '[' k11  @  a11 ;  ']' '/' '[' k12  @  a12 ;  ']' '/' '[' k13  @  a13 ;  ']' '/' '[' k14  @  a14 ;  ']' '/' '[' k15  @  a15 ;  ']' '/' '[' k16  @  a16 ;  ']' '/' '[' k17  @  a17 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ; k10 @ a10 ; k11 @ a11 ; k12 @ a12 ; k13 @ a13 ; k14 @ a14 ; k15 @ a15 ; k16 @ a16 ; k17 @ a17 ; k18 @ a18 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> $
    <[ k9 := fspec_to_rel a9 ]> $ <[ k10 := fspec_to_rel a10 ]> $ <[ k11 := fspec_to_rel a11 ]> $ <[ k12 := fspec_to_rel a12 ]> $ <[ k13 := fspec_to_rel a13 ]> $ <[ k14 := fspec_to_rel a14 ]> $ <[ k15 := fspec_to_rel a15 ]> $ <[ k16 := fspec_to_rel a16 ]> $ <[ k17 := fspec_to_rel a17 ]> {[ k18 := fspec_to_rel a18 ]} : gmap fname fspec_rel)
  (at level 1, format
                 "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ;  ']' '/' '[' k10  @  a10 ;  ']' '/' '[' k11  @  a11 ;  ']' '/' '[' k12  @  a12 ;  ']' '/' '[' k13  @  a13 ;  ']' '/' '[' k14  @  a14 ;  ']' '/' '[' k15  @  a15 ;  ']' '/' '[' k16  @  a16 ;  ']' '/' '[' k17  @  a17 ;  ']' '/' '[' k18  @  a18 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ; k10 @ a10 ; k11 @ a11 ; k12 @ a12 ; k13 @ a13 ; k14 @ a14 ; k15 @ a15 ; k16 @ a16 ; k17 @ a17 ; k18 @ a18 ; k19 @ a19 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> $
    <[ k9 := fspec_to_rel a9 ]> $ <[ k10 := fspec_to_rel a10 ]> $ <[ k11 := fspec_to_rel a11 ]> $ <[ k12 := fspec_to_rel a12 ]> $ <[ k13 := fspec_to_rel a13 ]> $ <[ k14 := fspec_to_rel a14 ]> $ <[ k15 := fspec_to_rel a15 ]> $ <[ k16 := fspec_to_rel a16 ]> $ <[ k17 := fspec_to_rel a17 ]> $ <[ k18 := fspec_to_rel a18 ]> {[ k19 := fspec_to_rel a19 ]} : gmap fname fspec_rel)
  (at level 1, format
                 "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ;  ']' '/' '[' k10  @  a10 ;  ']' '/' '[' k11  @  a11 ;  ']' '/' '[' k12  @  a12 ;  ']' '/' '[' k13  @  a13 ;  ']' '/' '[' k14  @  a14 ;  ']' '/' '[' k15  @  a15 ;  ']' '/' '[' k16  @  a16 ;  ']' '/' '[' k17  @  a17 ;  ']' '/' '[' k18  @  a18 ;  ']' '/' '[' k19  @  a19 ']' ']' ]}") : stdpp_scope.
Notation "{[ k1 @ a1 ; k2 @ a2 ; k3 @ a3 ; k4 @ a4 ; k5 @ a5 ; k6 @ a6 ; k7 @ a7 ; k8 @ a8 ; k9 @ a9 ; k10 @ a10 ; k11 @ a11 ; k12 @ a12 ; k13 @ a13 ; k14 @ a14 ; k15 @ a15 ; k16 @ a16 ; k17 @ a17 ; k18 @ a18 ; k19 @ a19 ; k20 @ a20 ]}" :=
  (<[ k1 := fspec_to_rel a1 ]> $ <[ k2 := fspec_to_rel a2 ]> $ <[ k3 := fspec_to_rel a3 ]> $ <[ k4 := fspec_to_rel a4 ]> $
    <[ k5 := fspec_to_rel a5 ]> $ <[ k6 := fspec_to_rel a6 ]> $ <[ k7 := fspec_to_rel a7 ]> $ <[ k8 := fspec_to_rel a8 ]> $
    <[ k9 := fspec_to_rel a9 ]> $ <[ k10 := fspec_to_rel a10 ]> $ <[ k11 := fspec_to_rel a11 ]> $ <[ k12 := fspec_to_rel a12 ]> $ <[ k13 := fspec_to_rel a13 ]> $ <[ k14 := fspec_to_rel a14 ]> $ <[ k15 := fspec_to_rel a15 ]> $ <[ k16 := fspec_to_rel a16 ]> $ <[ k17 := fspec_to_rel a17 ]> $ <[ k18 := fspec_to_rel a18 ]> $ <[ k19 := fspec_to_rel a19 ]> {[ k20 := fspec_to_rel a20 ]} : gmap fname fspec_rel)
  (at level 1, format
                 "{[ '[hv' '[' k1  @  a1 ;  ']' '/' '[' k2  @  a2 ;  ']' '/' '[' k3  @  a3 ;  ']' '/' '[' k4  @  a4 ;  ']' '/' '[' k5  @  a5 ;  ']' '/' '[' k6  @  a6 ;  ']' '/' '[' k7  @  a7 ;  ']' '/' '[' k8  @  a8 ;  ']' '/' '[' k9  @  a9 ;  ']' '/' '[' k10  @  a10 ;  ']' '/' '[' k11  @  a11 ;  ']' '/' '[' k12  @  a12 ;  ']' '/' '[' k13  @  a13 ;  ']' '/' '[' k14  @  a14 ;  ']' '/' '[' k15  @  a15 ;  ']' '/' '[' k16  @  a16 ;  ']' '/' '[' k17  @  a17 ;  ']' '/' '[' k18  @  a18 ;  ']' '/' '[' k19  @  a19 ;  ']' '/' '[' k20  @  a20 ']' ']' ]}") : stdpp_scope.

(***************
 ISim Notations
 **************)

Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------' itr_src itr_tgt '{' RR '}'"
:=
  (environments.envs_entails (Envs E1 E2 _) (isim _ _ _ _ _ RR _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
     format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' itr_tgt '//' '{'  RR  '}'").

Notation "E1 '------------------------------------------------------------------□' st_src st_tgt '-------------------------------isim-------------------------------' itr_src itr_tgt '{' RR '}'"
:=
  (environments.envs_entails (Envs E1 Enil _) (isim _ _ _ _ _ RR _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
     format "E1 '------------------------------------------------------------------□' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' itr_tgt '//' '{'  RR  '}'").

Notation "E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------' itr_src itr_tgt '{' RR '}'"
:=
  (environments.envs_entails (Envs Enil E2 _) (isim _ _ _ _ _ RR _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
     format "E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' itr_tgt '//' '{'  RR  '}'").

Notation "'------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------' itr_src itr_tgt '{' RR '}'"
:=
  (environments.envs_entails (Envs Enil Enil _) (isim _ _ _ _ _ RR _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
     format "'------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' itr_tgt '//' '{'  RR  '}'").

(* additional *) 
Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------' P '∗' 'ISIM'"
:=
  (environments.envs_entails (Envs E1 E2 _) (bi_sep P (isim _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
     format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' P  '∗'  'ISIM' ").
Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------' P '-∗' 'ISIM'"
:=
  (environments.envs_entails (Envs E1 E2 _) (bi_wand P (isim _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
     format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' P  '-∗'  'ISIM' ").

Notation "E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------' P '∗' 'ISIM'"
:=
  (environments.envs_entails (Envs Enil E2 _) (bi_sep P (isim _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
     format "E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' P  '∗'  'ISIM' ").
Notation "E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------' P '-∗' 'ISIM'"
:=
  (environments.envs_entails (Envs Enil E2 _) (bi_wand P (isim _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
     format "E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' P  '-∗'  'ISIM' ").

Notation "E1 '------------------------------------------------------------------□' st_src st_tgt '-------------------------------isim-------------------------------' P '∗' 'ISIM'"
:=
  (environments.envs_entails (Envs E1 Enil _) (bi_sep P (isim _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
     format "E1 '------------------------------------------------------------------□' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' P  '∗'  'ISIM' ").
Notation "E1 '------------------------------------------------------------------□' st_src st_tgt '-------------------------------isim-------------------------------' P '-∗' 'ISIM'"
:=
  (environments.envs_entails (Envs E1 Enil _) (bi_wand P (isim _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
     format "E1 '------------------------------------------------------------------□' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' P  '-∗'  'ISIM' ").

Notation "'------------------------------------------------------------------□' st_src st_tgt '-------------------------------isim-------------------------------' P '∗' 'ISIM'"
:=
  (environments.envs_entails (Envs Enil Enil _) (bi_sep P (isim _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
     format "'------------------------------------------------------------------□' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' P  '∗'  'ISIM' ").
Notation "'------------------------------------------------------------------□' st_src st_tgt '-------------------------------isim-------------------------------' P '-∗' 'ISIM'"
:=
  (environments.envs_entails (Envs Enil Enil _) (bi_wand P (isim _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
     format "'------------------------------------------------------------------□' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' P  '-∗'  'ISIM' ").

(***************
 WSim Notations
 **************)

Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '------------------------------params------------------------------' Ew E g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt '{' RR '}'" :=
  (environments.envs_entails (Envs E1 E2 _) (wsim _ _ _ (Ew, E) g _ _ RR ps pt (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '------------------------------params------------------------------' '//' Ew  E  g  ps  pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' itr_tgt '//' '{'  RR  '}' ").

Notation "E1 '------------------------------------------------------------------□' st_src st_tgt '------------------------------params------------------------------' Ew E g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt '{' RR '}'" :=
  (environments.envs_entails (Envs E1 Enil _) (wsim _ _ _ (Ew, E) g _ _ RR ps pt (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' st_src '//' st_tgt '//' '------------------------------params------------------------------' '//' Ew  E  g  ps  pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' itr_tgt '//' '{'  RR  '}' ").


Notation "E2 '------------------------------------------------------------------∗' st_src st_tgt '------------------------------params------------------------------' Ew E g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt '{' RR '}'" :=
  (environments.envs_entails (Envs Enil E2 _) (wsim _ _ _ (Ew, E) g _ _ RR ps pt (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
      format "E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '------------------------------params------------------------------' '//' Ew  E  g  ps  pt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' itr_tgt '//' '{'  RR  '}' ").


Notation "'------------------------------------------------------------------∗' st_src st_tgt '------------------------------params------------------------------' Ew E g ps pt '-------------------------------wsim-------------------------------' itr_src itr_tgt '{' RR '}'" :=
  (environments.envs_entails (Envs Enil Enil _) (wsim _ _ _ (Ew, E) g _ _ RR ps pt (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50, only printing,
      format "'------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '------------------------------params------------------------------' '//' Ew  E  g  ps  pt  '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' itr_tgt '//' '{'  RR  '}' ").


(* additional *) 
Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------wsim-------------------------------' P '∗' 'WSIM'" :=
  (environments.envs_entails (Envs E1 E2 _) (bi_sep P (wsim _ _ _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------wsim-------------------------------' '//' P '∗' 'WSIM'").
Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------wsim-------------------------------' P '-∗' 'WSIM'" :=
  (environments.envs_entails (Envs E1 E2 _) (bi_wand P (wsim _ _ _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------wsim-------------------------------' '//' P  '-∗'  'WSIM' ").




Notation "E1 '------------------------------------------------------------------□' st_src st_tgt '-------------------------------wsim-------------------------------' P '∗' 'WSIM'" :=
  (environments.envs_entails (Envs E1 Enil _) (bi_sep P (wsim _ _ _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' st_src '//' st_tgt '//' '-------------------------------wsim-------------------------------' '//' P  '∗'  'WSIM' ").
Notation "E1 '------------------------------------------------------------------□' st_src st_tgt '-------------------------------wsim-------------------------------' P '-∗' 'WSIM'" :=
  (environments.envs_entails (Envs E1 Enil _) (bi_wand P (wsim _ _ _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
      format "E1 '------------------------------------------------------------------□' '//' st_src '//' st_tgt '//' '-------------------------------wsim-------------------------------' '//' P  '-∗'  'WSIM' ").




Notation "E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------wsim-------------------------------' P '∗' 'WSIM'" :=
  (environments.envs_entails (Envs Enil E2 _) (bi_sep P (wsim _ _ _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
      format "E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------wsim-------------------------------' '//' P  '∗'  'WSIM' ").
Notation "E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------wsim-------------------------------' P '-∗' 'WSIM'" :=
  (environments.envs_entails (Envs Enil E2 _) (bi_wand P (wsim _ _ _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
      format "E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------wsim-------------------------------' '//' P  '-∗'  'WSIM' ").




Notation "'------------------------------------------------------------------∗' st_src st_tgt '-------------------------------wsim-------------------------------' P '∗' 'WSIM'" :=
  (environments.envs_entails (Envs Enil Enil _) (bi_sep P (wsim _ _ _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
      format "'------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------wsim-------------------------------' '//' P  '∗'  'WSIM' ").
Notation "'------------------------------------------------------------------∗' st_src st_tgt '-------------------------------wsim-------------------------------' P '-∗' 'WSIM'" :=
  (environments.envs_entails (Envs Enil Enil _) (bi_wand P (wsim _ _ _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50, only printing,
      format "'------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------wsim-------------------------------' '//' P  '-∗'  'WSIM' ").
