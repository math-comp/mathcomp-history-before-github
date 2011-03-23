(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require ssreflect.
Require Import Arith.

Goal (forall a b, a + b = b + a).
intros.
rewrite plus_comm, plus_comm.
split.
Qed.

Section Foo.
Export ssreflect.SsrSyntax.

Goal (forall a b, a + b = b + a).
intros.
rewrite 2!plus_comm. 
split.
Qed.
End Foo.
