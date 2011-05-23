(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
Require Import ssralg poly orderedalg zmodp polydiv zint polyzint.
Require Import orderedzint interval.

Import GRing.Theory.
Import OrderedRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

Section PolyoIdomain.

(* This should be replaced by a 0-characteristic condition + integrality *)
Variable R : oIdomainType.

Lemma size_deriv : forall (p : {poly R}), size p^`() = (size p).-1.
Proof.
move=> p; rewrite /deriv; case e :(size p) => [| sp]; first by rewrite /= size_poly0.
case e': sp => [| sp']; first by rewrite /= size_poly0.
rewrite [_.+2.-1]/= size_poly_eq // [_.+1.-1]/= natmulP mulrz_eq0.
by rewrite -{1}e' -[sp]/(sp.+1.-1) -e lead_coef_eq0 -size_poly_eq0 e orbb.
Qed.

Lemma derivn_poly0 : forall (p : {poly R}) n, (size p <= n)%N = (p^`(n) == 0).
Proof.
move=> p n; apply/idP/idP.
   move=> Hpn; apply/eqP; apply/polyP=>i; rewrite coef_derivn.
   rewrite nth_default; first by rewrite mul0rn coef0.
   by apply: leq_trans Hpn _; apply leq_addr.
elim: n {-2}n p (leqnn n) => [m | n ihn [| m]] p.
- by rewrite leqn0; move/eqP->; rewrite derivn0 leqn0 -size_poly_eq0.
- by move=> _; apply: ihn; rewrite leq0n.
- rewrite derivSn => hmn hder; case e: (size p) => [|sp] //.
  rewrite -(prednK (ltn0Sn sp)) [(_.-1)%N]lock -e -lock -size_deriv ltnS. 
  exact: ihn.
Qed.

Lemma mu_deriv : forall x (p : {poly R}), root p x ->
  \mu_x (p^`()) = (\mu_x p - 1)%N.
Proof.
move=> x p px0; case p0: (p == 0); first  by rewrite (eqP p0) derivC mu0.
case: (@maxdivp _ p x)=> [|q qx0 [n hp]]; first by rewrite p0.
case: n hp px0 qx0 => [->|n hp px0 qx0].
  by rewrite expr0 mulr1=> ->.
have q0 : q != 0 by apply: contra qx0; move/eqP->; rewrite root0.
rewrite hp maxdivp_mu // subn1 /= !derivCE subr0 mul1r.
rewrite !natmulP mulrzAr exprS !mulrA -mulrzAl -mulr_addl.
rewrite maxdivp_mu // rootE !(horner_lin, horner_mulrz) subrr mulr0 add0r.
by rewrite mulrz_eq0 negb_or qx0.
Qed.

Lemma mu_deriv_root : forall x (p : {poly R}), p != 0 -> root p x ->
  \mu_x p  = (\mu_x (p^`()) + 1)%N.
Proof.
by move=> x p p0 rpx; rewrite mu_deriv // subn1 addn1 prednK // mu_gt0.
Qed.

End PolyoIdomain.



