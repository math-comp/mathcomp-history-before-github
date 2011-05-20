Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop ssralg zint poly.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.

Section Ring.

Variable R : ringType.
Implicit Types x y z: R.
Implicit Types m n : zint.
Implicit Types i j k : nat.
Implicit Types p q r : {poly R}.

Lemma coef_zmul : forall p n i, (p *~ n)`_i = (p`_i *~ n).
Proof. by move=> p [] n i; rewrite ?NegzE (coef_negmul, coef_natmul). Qed.

Lemma polyC_zmul : forall n, {morph (@polyC R) : c / c *~ n}.
Proof.
move=> [] n c; rewrite ?NegzE -?natmulP ?polyC_natmul //.
by rewrite polyC_opp mulrNz polyC_natmul natmulN.
Qed.

Lemma horner_mulzr : forall n p x, (p *~ n).[x] = p.[x] *~ n.
Proof.
move=> [] n p x; rewrite ?NegzE -?natmulP ?horner_mulrn //.
by rewrite horner_opp mulrNz horner_mulrn natmulN.
Qed.

Lemma horner_zmul : forall n x, (n%:~R : {poly R}).[x] = n%:~R.
Proof. by move=> n x; rewrite horner_mulzr hornerC. Qed.

Lemma derivMz : forall n p, (p *~ n)^`() = p^`() *~ n.
Proof. by move=> [] n p; rewrite ?NegzE -?natmulP (derivMn, derivMNn). Qed.

End Ring.

