(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require ssreflect.
Require Import Arith.

Goal (forall a b, a + b = b + a).
intros.
rewrite plus_comm, plus_comm.
split.
Abort.

Section Foo.
Import ssreflect.SsrSyntax.

Goal (forall a b, a + b = b + a).
intros.
rewrite 2![_ + _]plus_comm. 
split.
Abort.
End Foo.

Goal (forall a b, a + b = b + a).
intros.
rewrite plus_comm, plus_comm.
split.
Abort.