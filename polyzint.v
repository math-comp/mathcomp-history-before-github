(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
Require Import ssralg poly orderedalg zmodp polydiv zint orderedzint interval.

Import GRing.Theory.
Import OrderedRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

Section PolyZintRing.

Variable R : ringType.
Implicit Types x y z: R.
Implicit Types m n : zint.
Implicit Types i j k : nat.
Implicit Types p q r : {poly R}.

Lemma coef_mulrz : forall p n i, (p *~ n)`_i = (p`_i *~ n).
Proof. by move=> p [] n i; rewrite ?NegzE (coef_negmul, coef_natmul). Qed.

Lemma polyC_mulrz : forall n, {morph (@polyC R) : c / c *~ n}.
Proof.
move=> [] n c; rewrite ?NegzE -?natmulP ?polyC_natmul //.
by rewrite polyC_opp mulrNz polyC_natmul natmulN.
Qed.

Lemma horner_mulrz : forall n (p : {poly R}) x, (p *~ n).[x] = p.[x] *~ n.
Proof. by case=> *; rewrite ?NegzE ?mulNzr ?(horner_opp, horner_mulrn). Qed.

Lemma horner_zmul : forall n x, (n%:~R : {poly R}).[x] = n%:~R.
Proof. by move=> n x; rewrite horner_mulrz hornerC. Qed.

Lemma derivMz : forall n p, (p *~ n)^`() = p^`() *~ n.
Proof. by move=> [] n p; rewrite ?NegzE -?natmulP (derivMn, derivMNn). Qed.

End PolyZintRing.

Section PolyZintOIdom.

Variable R : oIdomainType.

Lemma mulpz : forall (p : {poly R}) n, p *~ n = n%:~R *: p.
Proof.
by move=> p n; rewrite -[p *~ n]mulrzl -mul_polyC polyC_mulrz polyC1.
Qed.

End PolyZintOIdom.



