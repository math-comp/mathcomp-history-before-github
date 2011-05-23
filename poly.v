(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
Require Import bigop ssralg binomial.

(******************************************************************************)
(* This file provides a library for univariate polynomials over ring          *)
(* structures; it also provides an extended theory for polynomials whose      *)
(* coefficients range over commutative rings and integral domains.            *)
(*                                                                            *)
(*           {poly R} == the type of polynomials with coefficients of type R, *)
(*                       represented as lists with a non zero last element    *)
(*                       (big endian representation); the coeficient type R   *)
(*                       must have a canonical ringType structure cR. In fact *)
(*                       {poly R} denotes the concrete type polynomial cR; R  *)
(*                       is just a phantom argument that lets type inference  *)
(*                       reconstruct the (hidden) ringType structure cR.      *)
(*          p : seq R == the big-endian sequence of coefficients of p, via    *)
(*                       the coercion polyseq: polynomial >-> seq.            *)
(*             Poly s == the polynomial with coefficient sequence s (ignoring *)
(*                       trailing zeroes).                                    *)
(* \poly_(i < n) E(i) == the polynomial of degree at most n - 1 whose         *)
(*                       coefficients are given by the general term E(i)      *)
(*   0, 1, -p, p + q, == the usual ring operations: {poly R} has a canonical  *)
(* p * q, p ^+ n, ...    ringType structure, which is commutative / integral  *)
(*                       when R is commutative / integral, respectively.      *)
(*               c%:P == the constant polynomial c                            *)
(*                 'X == the (unique) variable                                *)
(*               'X^n == a power of 'X; 'X^0 is 1, 'X^1 is convertible to 'X  *)
(*               p`_i == the coefficient of 'X^i in p; this is in fact just   *)
(*                       the ring_scope notation generic seq-indexing using   *)
(*                       nth 0%R, combined with the polyseq coercion.         *)
(*             size p == 1 + the degree of p, or 0 if p = 0 (this is the      *)
(*                       generic seq function combined with polyseq).         *)
(*        lead_coef p == the coefficient of the highest monomial in p, or 0   *)
(*                       if p = 0 (hence lead_coef p = 0 iff p = 0)           *)
(*            monic p == p is monic, i.e., lead_coef p = 1 (0 is not monic)   *)
(*             p.[x]  == the evaluation of a polynomial p at a point x using  *)
(*                       the Horner scheme                                    *)
(*                   *** The multi-rule horner_lin (resp. horner_lin_com)     *)
(*                       unwinds horner evaluation of a polynomial expression *)
(*                       (resp. in a non commutative ring, under appropriate  *)
(*                       assumptions).                                        *)
(*             p^`()  == formal derivative of p                               *)
(*             p^`(n) == formal n-derivative of p                             *)
(*            p^`N(n) == formal n-derivative of p divided by n!               *)
(*            p \Po q == polynomial composition                               *)
(*                       \sum(i < size p) p`_i *: q ^+ i                      *)
(*       com_poly p x == x and p.[x] commute; this is a sufficient condition  *)
(*                       for evaluating (q * p).[x] as q.[x] * p.[x] when R   *)
(*                       is not commutative.                                  *)
(*       com_coef p x == x commutes with all the coefficients of p (clearly,  *)
(*                       this implies com_poly p x).                          *)
(*           root p x == x is a root of p, i.e., p.[x] = 0                    *)
(*    n.-unity_root x == x is an nth root of unity, i.e., a root of 'X^n - 1  *)
(* n.-primitive_root x == x is a primitive nth root of unity, i.e., n is the  *)
(*                       least positive integer m > 0 such that x ^+ m = 1.   *)
(*                   *** The submodule poly.UnityRootTheory can be used to    *)
(*                       import selectively the part of the theory of roots   *)
(*                       of unity that doesn't mention polynomials explicitly *)
(*       map_poly f p == the image of the polynomial by the function f (which *)
(*                       should be a ring morphism).                          *)
(*     comm_ringM f u == u commutes with the image of f (i.e., with all f x)  *)
(*   horner_morph f u == the function mapping p to the value of map_poly f p  *)
(*                       at u; this is a morphism from {poly R} to the image  *)
(*                       ring of f when f is a morphism and comm_ringM f u.   *)
(*     diff_roots x y == x and y are distinct roots; if R is a field, this    *)
(*                       just means x != y, but this concept is generalized   *)
(*                       to the case where R is only a ring with units (i.e., *)
(*                       a unitRingType); in which case it means that x and y *)
(*                       commute, and that the difference x - y is a unit     *)
(*                       (i.e., has a multiplicative inverse) in R.           *)
(*                       to just x != y).                                     *)
(*       uniq_roots s == s is a sequence or pairwise distinct roots, in the   *)
(*                       sense of diff_roots p above.                         *)
(*   *** We only show that these operations and properties are transferred by *)
(*       morphisms whose domain is a field (thus ensuring injectivity).       *)
(* We prove the factor_theorem, and the max_poly_roots inequality relating    *)
(* the number of distinct roots of a polynomial and its size.                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Open Local Scope ring_scope.

Reserved Notation "{ 'poly' T }" (at level 0, format "{ 'poly'  T }").
Reserved Notation "c %:P" (at level 2, format "c %:P").
Reserved Notation "'X" (at level 0).
Reserved Notation "''X^' n" (at level 3, n at level 2, format "''X^' n").
Reserved Notation "\poly_ ( i < n ) E"
  (at level 36, E at level 36, i, n at level 50,
   format "\poly_ ( i  <  n )  E").
Reserved Notation "a ^`N ( n )" (at level 8, format "a ^`N ( n )").
Reserved Notation "n .-unity_root" (at level 2, format "n .-unity_root").
Reserved Notation "n .-primitive_root"
  (at level 2, format "n .-primitive_root").

Local Notation simp := Monoid.simpm.

(* left and right regularity -> ssalg *)
Section Ring.

Variable R : ringType.

Definition lreg a := forall b: R, a * b = 0 -> b = 0.
Definition rreg a := forall b: R, b * a = 0 -> b = 0.

Lemma lreg0 : ~ lreg 0.
Proof.
by move/(_ 1); rewrite simp=> HH; case/eqP: (nonzero1r R); exact: HH.
Qed.

Lemma rreg0 : ~ rreg 0.
Proof.
by move/(_ 1); rewrite simp=> HH; case/eqP: (nonzero1r R); exact: HH.
Qed.

Lemma lreg1 : lreg 1.
Proof. by move=> b; rewrite simp. Qed.

Lemma rreg1 : rreg 1.
Proof. by move=> b; rewrite simp. Qed.

Lemma lregM : forall a b, lreg a -> lreg b -> lreg (a * b).
Proof.
move=> a b Ra Rb c; rewrite -mulrA => Hc; exact: (Rb _ (Ra _ Hc)).
Qed.

Lemma rregM : forall a b, rreg a -> rreg b -> rreg (a * b).
Proof.
by move=> a b Ra Rb c; rewrite mulrA => Hc; exact: (Ra _ (Rb _ Hc)).
Qed.

Lemma lregX : forall a n, lreg a -> lreg (a ^+ n).
Proof.
move=> a n Ra; elim: n=> [|n IHn]; first by exact: lreg1.
by rewrite exprS; apply lregM.
Qed.

Lemma rregX : forall a n, rreg a -> rreg (a ^+ n).
Proof.
move=> a n Ra; elim: n=> [|n IHn]; first by exact: rreg1.
by rewrite exprS; apply rregM.
Qed.

End Ring.

Section IRing.

Variables (R : idomainType) (a : R).

Lemma lregP : reflect (lreg a) (a != 0).
Proof.
apply: (iffP idP) => [nz_a b |]; last by case: eqP => // ->; case/lreg0.
by move/eqP; apply: contraTeq; exact: mulf_neq0.
Qed.

Lemma rregP : reflect (rreg a) (a != 0).
Proof.
apply: (iffP idP) => [nz_a b |]; last by case: eqP => // ->; case/rreg0.
by move/eqP; apply: contraTeq => nz_b; exact: mulf_neq0.
Qed.

End IRing.

Section Polynomial.

Variable R : ringType.

(* Defines a polynomial as a sequence with <> 0 last element *)
Record polynomial := Polynomial {polyseq :> seq R; _ : last 1 polyseq != 0}.

(* Todo : block the reduction of polyseq ? *)

Canonical Structure polynomial_subType :=
  Eval hnf in [subType for polyseq by polynomial_rect].
Definition polynomial_eqMixin := Eval hnf in [eqMixin of polynomial by <:].
Canonical Structure polynomial_eqType :=
  Eval hnf in EqType polynomial polynomial_eqMixin.
Definition polynomial_choiceMixin := [choiceMixin of polynomial by <:].
Canonical Structure polynomial_choiceType :=
  Eval hnf in ChoiceType polynomial polynomial_choiceMixin.

Lemma poly_inj : injective polyseq. Proof. exact: val_inj. Qed.

Definition poly_of of phant R := polynomial.
Identity Coercion type_poly_of : poly_of >-> polynomial.

End Polynomial.

(* We need to break off the section here to let the argument scope *)
(* directives take effect.                                         *)
Bind Scope ring_scope with poly_of.
Bind Scope ring_scope with polynomial.
Arguments Scope poly_inj [_ ring_scope ring_scope _].
Notation "{ 'poly' T }" := (poly_of (Phant T)).

Section PolynomialEqChoice.

Variable R : ringType.

Canonical Structure poly_subType := Eval hnf in [subType of {poly R}].
Canonical Structure poly_eqType := Eval hnf in [eqType of {poly R}].
Canonical Structure poly_choiceType := Eval hnf in [choiceType of {poly R}].

End PolynomialEqChoice.

Section PolynomialTheory.

Variable R : ringType.

Implicit Types p q : {poly R}.

Definition lead_coef p := p`_(size p).-1.
Lemma lead_coefE : forall p, lead_coef p = p`_(size p).-1. Proof. by []. Qed.

Definition polyC c : {poly R} :=
  insubd (@Polynomial R [::] (nonzero1r _)) [:: c].

Local Notation "c %:P" := (polyC c).

(* Remember the boolean (c != 0) is coerced to 1 if true and 0 if false *)
Lemma polyseqC : forall c, c%:P = nseq (c != 0) c :> seq R.
Proof. by move=> c; rewrite val_insubd /=; case: (c == 0). Qed.

Lemma size_polyC : forall c, size c%:P = (c != 0).
Proof. by move=> c; rewrite polyseqC size_nseq. Qed.

Lemma coefC : forall c i, c%:P`_i = if i == 0%N then c else 0.
Proof. by move=> c [|[|i]]; rewrite polyseqC //=; case: eqP. Qed.

Lemma polyC_inj : injective polyC.
Proof. by move=> c1 c2 eqc12; have:= coefC c2 0; rewrite -eqc12 coefC. Qed.

Lemma lead_coefC : forall c, lead_coef c%:P = c.
Proof. by move=> c; rewrite /lead_coef polyseqC; case: eqP. Qed.

(* Extensional interpretation (poly <=> nat -> R) *)
Lemma polyP : forall p1 p2, nth 0 p1 =1 nth 0 p2 <-> p1 = p2.
Proof.
move=> p1 p2; split=> [eq_p12 | -> //]; apply: poly_inj.
without loss lt_p12: p1 p2 eq_p12 / size p1 < size p2 => [wltn|].
  case: (ltngtP (size p1) (size p2)); try by move/wltn->.
  move/(@eq_from_nth _ 0); exact.
case: p2 => p2 nz_p2 /= in lt_p12 eq_p12 *; case/eqP: nz_p2.
by rewrite (last_nth 0) -(subnKC lt_p12) /= -eq_p12 nth_default ?leq_addr.
Qed.

Lemma size1_polyC : forall p, size p <= 1 -> p = (p`_0)%:P.
Proof.
move=> p le_p_1; apply/polyP=> i; rewrite coefC.
by case: i => // i; rewrite nth_default // (leq_trans le_p_1).
Qed.

(* Builds a polynomial by extension. *)
Definition poly_cons c p : {poly R} :=
  if p is Polynomial ((_ :: _) as s) ns then
     @Polynomial R (c :: s) ns
  else c%:P.

Lemma polyseq_cons : forall c p,
  poly_cons c p = (if size p != 0%N then c :: p else c%:P) :> seq R.
Proof. by move=> c [[|c' s] ns] /=. Qed.

Lemma size_poly_cons : forall c p,
  size (poly_cons c p) =
    (if (size p == 0%N) && (c == 0) then 0%N else (size p).+1).
Proof. by move=> c [[|c' s] _] //=; rewrite size_polyC; case: eqP. Qed.

Lemma coef_cons : forall c p i,
  (poly_cons c p)`_i = if i == 0%N then c else p`_i.-1.
Proof.
by move=> c [[|c' s] _] [] //=; rewrite polyseqC; case: eqP => //= _ [].
Qed.

(* Builds a polynomial from a bare list of coefficients *)
Definition Poly := foldr poly_cons 0%:P.

Lemma PolyK : forall c s, last c s != 0 -> Poly s = s :> seq R.
Proof.
move=> _ [_|/= c s]; first by rewrite polyseqC eqxx.
elim: s c => [|c' s IHs] /= c nz_c; rewrite polyseq_cons ?IHs //.
by rewrite !(polyseqC, eqxx) // nz_c.
Qed.

Lemma polyseqK : forall p, Poly p = p.
Proof. case=> s nz_s; apply: poly_inj; exact: PolyK nz_s. Qed.

Lemma size_Poly : forall s, size (Poly s) <= size s.
Proof.
elim=> [|c s IHs] /=; first by rewrite polyseqC eqxx.
by rewrite polyseq_cons; case: ifP => // _; rewrite size_polyC; case: (~~ _).
Qed.

Lemma coef_Poly : forall s i, (Poly s)`_i = s`_i.
Proof.
by elim=> [|c s IHs] /= [|i]; rewrite !(coefC, eqxx, coef_cons) /=.
Qed.

(* Builds a polynomial from an infinite seq of coef and a bound *)
Local Notation "\poly_ ( i < n ) E" := (Poly (mkseq (fun i : nat => E) n)).

Lemma polyseq_poly : forall n E,
  E n.-1 != 0 -> \poly_(i < n) E i = mkseq [eta E] n :> seq R.
Proof.
move=> [|n] E nzE; first by rewrite polyseqC eqxx.
by rewrite (@PolyK 0) // -nth_last nth_mkseq size_mkseq /=.
Qed.

Lemma size_poly : forall n E, size (\poly_(i < n) E i) <= n.
Proof. by move=> n E; rewrite (leq_trans (size_Poly _)) ?size_mkseq. Qed.

Lemma size_poly_eq : forall n E, E n.-1 != 0 -> size (\poly_(i < n) E i) = n.
Proof. move=> n E; move/polyseq_poly->; exact: size_mkseq. Qed.

Lemma coef_poly : forall n E k,
  (\poly_(i < n) E i)`_k = (if k < n then E k else 0).
Proof.
move=> n E k; case: (ltnP k n) => ?; first by rewrite coef_Poly nth_mkseq.
by rewrite coef_Poly nth_default // size_mkseq.
Qed.

Lemma lead_coef_poly : forall n E,
  n > 0 -> E n.-1 != 0 -> lead_coef (\poly_(i < n) E i) = E n.-1.
Proof.
by case=> // n E _ nzE; rewrite /lead_coef size_poly_eq // coef_poly leqnn.
Qed.

Lemma coefK : forall p, \poly_(i < size p) p`_i = p.
Proof.
move=> p; apply/polyP=> i; rewrite coef_poly.
by case: ltnP => // le_p_i; rewrite nth_default.
Qed.

End PolynomialTheory.

Notation "{ 'poly' T }" := (poly_of (Phant T)) : type_scope.
Notation "\poly_ ( i < n ) E" := (Poly (mkseq (fun i => E) n)) : ring_scope.
Prenex Implicits polyC.
Notation "c %:P" := (polyC c) : ring_scope.

Module PolynomialZmodule.
Section PolynomialZmodule.

Variable R : ringType.

Implicit Types p q : {poly R}.

(* Zmodule structure for polynomial *)
Definition add_poly p1 p2 :=
  \poly_(i < maxn (size p1) (size p2)) (p1`_i + p2`_i).

Definition opp_poly p := \poly_(i < size p) - p`_i.

Lemma coef_add_poly : forall p1 p2 i, (add_poly p1 p2)`_i = p1`_i + p2`_i.
Proof.
move=> p1 p2 i; rewrite coef_poly /=; case: leqP => //.
by rewrite leq_maxl; case/andP; do 2!move/(nth_default 0)->; rewrite add0r.
Qed.

Lemma coef_opp_poly : forall p i, (opp_poly p)`_i = - p`_i.
Proof.
move=> p i; rewrite coef_poly /=; case: leqP => //.
by move/(nth_default 0)->; rewrite oppr0.
Qed.

Lemma add_polyA : associative add_poly.
Proof. by move=> p1 p2 p3; apply/polyP=> i; rewrite !coef_add_poly addrA. Qed.

Lemma add_polyC : commutative add_poly.
Proof. by move=> p1 p2; apply/polyP=> i; rewrite !coef_add_poly addrC. Qed.

Lemma add_poly0 : left_id 0%:P add_poly.
Proof.
by move=> p; apply/polyP=> i; rewrite coef_add_poly coefC if_same add0r.
Qed.

Lemma add_poly_opp : left_inverse 0%:P opp_poly add_poly.
Proof.
move=> p; apply/polyP=> i.
by rewrite coef_add_poly coef_opp_poly coefC if_same addNr.
Qed.

Definition mixin :=
  ZmodMixin add_polyA add_polyC add_poly0 add_poly_opp.

End PolynomialZmodule.
End PolynomialZmodule.

Canonical Structure poly_zmodType (R: ringType) :=
  Eval hnf in ZmodType {poly R} (PolynomialZmodule.mixin R).
Canonical Structure polynomial_zmodType (R: ringType) :=
  Eval hnf in [zmodType of polynomial R for (poly_zmodType R)].

Section PolynomialZmodTheory.
(* Properties of the zero polynomial *)
Variable R : ringType.

Local Notation polyC := (@polyC R).
Implicit Types p q : {poly R}.

Lemma polyC0 : 0%:P = 0 :> {poly R}. Proof. by []. Qed.

Lemma seq_poly0 : (0 : {poly R}) = [::] :> seq R.
Proof. by rewrite polyseqC eqxx. Qed.

Lemma size_poly0 : size (0 : {poly R}) = 0%N.
Proof. by rewrite seq_poly0. Qed.

Lemma coef0 : forall i, (0 : {poly R})`_i = 0.
Proof. by move=> i; rewrite coefC if_same. Qed.

Lemma lead_coef0 : lead_coef 0 = 0 :> R. Proof. exact: lead_coefC. Qed.

Lemma size_poly_eq0 : forall p, (size p == 0%N) = (p == 0).
Proof. by move=> p; rewrite size_eq0 -seq_poly0. Qed.

Lemma poly0Vpos : forall p, {p = 0} + {size p > 0}.
Proof. by move=> p; rewrite lt0n size_poly_eq0; exact: eqVneq. Qed.

Lemma polySpred : forall p, p != 0 -> size p = (size p).-1.+1.
Proof. by move=> p; rewrite -size_poly_eq0 -lt0n; move/prednK. Qed.

Lemma lead_coef_eq0 : forall p, (lead_coef p == 0) = (p == 0).
Proof.
move=> p; rewrite -size_poly_eq0 /lead_coef nth_last.
by case: p => [[|x s] /=]; move/negbTE=> // _; rewrite eqxx.
Qed.

Lemma polyC_eq0 : forall c : R, (c%:P == 0) = (c == 0).
Proof. by move=> c; rewrite -size_poly_eq0 size_polyC; case: (c == 0). Qed.

Lemma size1P : forall p,
  reflect (exists c, c != 0 /\ p = c%:P) (size p == 1%N).
Proof.
move=> p; apply: (iffP eqP) => [s1 | [c [nc0 ep]]].
  exists p`_0; move: (leqnn (size p)); rewrite {2}s1; move/size1_polyC=> e.
  by split=> //; rewrite -polyC_eq0 -e -size_poly_eq0 s1.
by rewrite ep size_polyC nc0.
Qed.
(* Todo : case analysis : size 0, 1, n.+2 *)

(* Size, leading coef, morphism properties of coef *)
Lemma leq_size_coef : forall p i,
  (forall j, i <= j -> p`_j = 0) -> size p <= i.
Proof.
move=> p i p_i_0; case: leqP => lt_i_p //; have p1_1 := ltn_predK lt_i_p.
have: p != 0 by rewrite -size_poly_eq0 -p1_1.
by rewrite -lead_coef_eq0 lead_coefE p_i_0 ?eqxx // -ltnS p1_1.
Qed.

Lemma leq_coef_size : forall p i, p`_i != 0 -> i < size p.
Proof. by move=> p i; case: leqP => //; move/(nth_default 0)->; case/eqP. Qed.

Lemma coef_add : forall p1 p2 i, (p1 + p2)`_i = p1`_i + p2`_i.
Proof. exact: PolynomialZmodule.coef_add_poly. Qed.

Lemma coef_opp : forall p i, (- p)`_i = - p`_i.
Proof. exact: PolynomialZmodule.coef_opp_poly. Qed.

Lemma coef_sub : forall p1 p2 i, (p1 - p2)`_i = p1`_i - p2`_i.
Proof. by move=> p1 p2 i; rewrite coef_add coef_opp. Qed.

Lemma coef_natmul : forall p n i, (p *+ n)`_i = p`_i *+ n.
Proof.
by move=> p n i; elim: n => [|n IHn]; rewrite ?coef0 // !mulrS coef_add IHn.
Qed.

Lemma coef_negmul : forall p n i, (p *- n)`_i = p`_i *- n.
Proof. by move=> p n i; rewrite coef_opp coef_natmul. Qed.

Lemma coef_sum : forall I r (P : pred I) (F : I -> {poly R}) k,
  (\sum_(i <- r | P i) F i)`_k = \sum_(i <- r | P i) (F i)`_k.
Proof.
move=> I r P F k.
by apply: (big_morph (fun p => p`_k)) => [p q|]; rewrite (coef0, coef_add).
Qed.

Lemma polyC_add : {morph polyC : c1 c2 / c1 + c2}.
Proof.
by move=> c1 c2; apply/polyP=> [[|i]]; rewrite coef_add !coefC ?addr0.
Qed.

Lemma polyC_opp : {morph polyC : c / - c}.
Proof.
by move=> c; apply/polyP=> [[|i]]; rewrite coef_opp !coefC ?oppr0.
Qed.

Lemma polyC_sub : {morph polyC : c1 c2 / c1 - c2}.
Proof. by move=> c1 c2; rewrite polyC_add polyC_opp. Qed.

Lemma polyC_natmul : forall n, {morph polyC : c / c *+ n}.
Proof. by elim=> // n IHn c; rewrite !mulrS polyC_add IHn. Qed.

Lemma size_opp : forall p, size (- p) = size p.
Proof.
have le_sz: forall p, size (- p) <= size p by move=> p; exact: size_poly.
by move=> p; apply/eqP; rewrite eqn_leq -{3}(opprK p) !le_sz.
Qed.

Lemma lead_coef_opp : forall p, lead_coef (- p) = - lead_coef p.
Proof. by move=> p; rewrite /lead_coef size_opp coef_opp. Qed.

Lemma size_add : forall p q, size (p + q) <= maxn (size p) (size q).
Proof. by move=> p q; exact: size_poly. Qed.

Lemma size_addl : forall p q, size p > size q -> size (p + q) = size p.
Proof.
move=> p q ltqp; rewrite size_poly_eq maxnl 1?ltnW //.
by rewrite addrC nth_default ?simp ?nth_last; case: p ltqp => [[]].
Qed.

Lemma size_sum : forall I r (P : pred I) (F : I -> {poly R}),
  size (\sum_(i <- r | P i) F i) <= \max_(i <- r | P i) size (F i).
Proof.
move=> I r P F; pose K p := [fun n => size p <= n : Prop].
apply: (big_ind2 K) => //= [|p1 n1 p2 n2 IH1 IH2]; first by rewrite size_poly0.
apply: leq_trans (size_add p1 p2) _.
by rewrite -eqn_maxl maxnAC !maxnA -maxnA (maxnl IH1) (maxnr IH2).
Qed.

Lemma lead_coef_addl : forall p q,
  size p > size q -> lead_coef (p + q) = lead_coef p.
Proof.
move=> p q ltqp; rewrite /lead_coef coef_add size_addl //.
by rewrite addrC nth_default ?simp // -ltnS (ltn_predK ltqp).
Qed.

End PolynomialZmodTheory.

Module PolynomialRing.
Section PolynomialRing.
(* And now the Ring structure. *)
Variable R : ringType.

Definition mul_poly (p1 p2 : {poly R}) :=
  \poly_(i < (size p1 + size p2).-1) (\sum_(j < i.+1) p1`_j * p2`_(i - j)).

Lemma coef_mul_poly : forall p1 p2 i,
  (mul_poly p1 p2)`_i = \sum_(j < i.+1) p1`_j * p2`_(i - j)%N.
Proof.
move=> p1 p2 i; rewrite coef_poly; case: leqP => // gtn_i.
rewrite big1 // => j _; case: (leqP (size p2) (i - j)) => [ge_j | lt_j].
  by rewrite {1}[nth]lock nth_default ?mulr0.
rewrite nth_default ?mul0r // -(leq_add2r (size p2)); move: gtn_i (lt_j).
rewrite -(ltn_predK lt_j) !addnS /= !ltnS leq_sub_add; exact: leq_trans.
Qed.

Lemma coef_mul_poly_rev : forall p1 p2 i,
  (mul_poly p1 p2)`_i = \sum_(j < i.+1) p1`_(i - j)%N * p2`_j.
Proof.
move=> p1 p2 i; rewrite coef_mul_poly (reindex_inj rev_ord_inj) /=.
by apply: eq_bigr => j _; rewrite (sub_ordK j).
Qed.

Lemma mul_polyA : associative mul_poly.
Proof.
move=> p1 p2 p3; apply/polyP=> i; rewrite coef_mul_poly coef_mul_poly_rev.
pose coef3 j k := p1`_j * (p2`_(i - j - k)%N * p3`_k).
transitivity (\sum_(j < i.+1) \sum_(k < i.+1 | k <= i - j) coef3 j k).
  apply: eq_bigr => /= j _; rewrite coef_mul_poly_rev big_distrr /=.
  by rewrite (big_ord_narrow_leq (leq_subr _ _)).
rewrite (exchange_big_dep predT) //=; apply: eq_bigr => k _.
transitivity (\sum_(j < i.+1 | j <= i - k) coef3 j k).
  apply: eq_bigl => j; rewrite -ltnS -(ltnS j) -!leq_subS ?leq_ord //.
  by rewrite -subn_gt0 -(subn_gt0 j) !subn_sub addnC.
rewrite (big_ord_narrow_leq (leq_subr _ _)) coef_mul_poly big_distrl /=.
by apply: eq_bigr => j _; rewrite /coef3 !subn_sub addnC mulrA.
Qed.

Lemma mul_1poly : left_id 1%:P mul_poly.
Proof.
move=> p; apply/polyP => i; rewrite coef_mul_poly big_ord_recl subn0.
by rewrite big1 => [|j _]; rewrite coefC !simp.
Qed.

Lemma mul_poly1 : right_id 1%:P mul_poly.
Proof.
move=> p; apply/polyP => i; rewrite coef_mul_poly_rev big_ord_recl subn0.
by rewrite big1 => [|j _]; rewrite coefC !simp.
Qed.

Lemma mul_poly_addl : left_distributive mul_poly +%R.
Proof.
move=> p1 p2 p3; apply/polyP=> i; rewrite coef_add !coef_mul_poly -big_split.
by apply: eq_bigr => j _; rewrite coef_add mulr_addl.
Qed.

Lemma mul_poly_addr : right_distributive mul_poly +%R.
Proof.
move=> p1 p2 p3; apply/polyP=> i; rewrite coef_add !coef_mul_poly -big_split.
by apply: eq_bigr => j _; rewrite coef_add mulr_addr.
Qed.

Lemma nonzero_poly1 : 1%:P != 0 :> {poly R}.
Proof. by rewrite polyC_eq0 nonzero1r. Qed.

Definition mixin :=
  RingMixin mul_polyA mul_1poly mul_poly1 mul_poly_addl mul_poly_addr
            nonzero_poly1.

End PolynomialRing.
End PolynomialRing.

Canonical Structure poly_ringType (R : ringType) :=
  Eval hnf in RingType {poly R} (PolynomialRing.mixin R).
Canonical Structure polynomial_ringType (R : ringType) :=
  Eval hnf in [ringType of polynomial R for (poly_ringType R)].

Section PolynomialRingTheory.

Variable R : ringType.
Implicit Types p q : {poly R}.
Local Notation polyC := (@polyC R).

Lemma polyC1 : 1%:P = 1 :> {poly R}. Proof. by []. Qed.

Lemma polyseq1 : (1 : {poly R}) = [:: 1] :> seq R.
Proof. by rewrite polyseqC nonzero1r. Qed.

Lemma size_poly1 : size (1 : {poly R}) = 1%N.
Proof. by rewrite polyseq1. Qed.

Lemma coef1 : forall i, (1 : {poly R})`_i = (i == 0%N)%:R.
Proof. by case=> [|i]; rewrite polyseq1 /= ?nth_nil. Qed.

Lemma lead_coef1 : lead_coef 1 = 1 :> R. Proof. exact: lead_coefC. Qed.

Lemma coef_mul : forall p1 p2 i,
  (p1 * p2)`_i = \sum_(j < i.+1) p1`_j * p2`_(i - j)%N.
Proof. exact: PolynomialRing.coef_mul_poly. Qed.

Lemma coef_mul_rev : forall p1 p2 i,
  (p1 * p2)`_i = \sum_(j < i.+1) p1`_(i - j)%N * p2`_j.
Proof. exact: PolynomialRing.coef_mul_poly_rev. Qed.

Lemma size_mul : forall p1 p2, size (p1 * p2) <= (size p1 + size p2).-1.
Proof. move=> p1 p2; exact: size_poly. Qed.

Lemma head_coef_mul : forall p q,
  (p * q)`_(size p + size q).-2 = lead_coef p * lead_coef q.
Proof.
move=> p q; pose dp := (size p).-1; pose dq := (size q).-1.
case: (poly0Vpos p) => [->|nz_p]; first by rewrite !(simp, coef0, lead_coef0).
case: (poly0Vpos q) => [->|nz_q]; first by rewrite !(simp, coef0, lead_coef0).
have ->: (size p + size q).-2 = (dp + dq)%N.
  by rewrite -(prednK nz_p) -(prednK nz_q) addnS.
have op: dp < (dp + dq).+1 by rewrite ltnS leq_addr.
rewrite coef_mul (bigD1 (Ordinal op)) ?big1 ?simp ?addKn //= => i.
rewrite -val_eqE neq_ltn /=; case/orP=> [lt_i_p | gt_i_p]; last first.
  by rewrite nth_default ?simp //; rewrite prednK in gt_i_p.
rewrite [q`__]nth_default ?simp //= -subSS -{1}addnS prednK //.
by rewrite addnC -addn_subA ?leq_addr.
Qed.

Lemma size_proper_mul : forall p q,
  lead_coef p * lead_coef q != 0 -> size (p * q) = (size p + size q).-1.
Proof.
move=> p q; rewrite -head_coef_mul.
case: (poly0Vpos p) => [-> | nz_p]; first by rewrite simp coef0 eqxx.
case: (poly0Vpos q) => [-> | nz_q]; first by rewrite simp coef0 eqxx.
rewrite coef_poly {1}prednK ?leqnn => [? | ]; first by rewrite size_poly_eq.
by rewrite -(prednK nz_p) -(prednK nz_q) addnS.
Qed.

Lemma lead_coef_proper_mul : forall p q,
  let c := lead_coef p * lead_coef q in c != 0 -> lead_coef (p * q) = c.
Proof. by move=> p q /= nz_c; rewrite -head_coef_mul -size_proper_mul. Qed.

Lemma size_prod : forall (I : finType) (P : pred I) (F : I -> {poly R}),
  size (\prod_(i | P i) F i) <=
    (\sum_(i | P i) size (F i)).+1 - #|P|.
Proof.
move => I P F.
rewrite cardE -filter_index_enum -!(big_filter _ P).
elim: (filter P _) => {P} [|i r IH].
 by rewrite !big_nil size_polyC GRing.nonzero1r.
rewrite !big_cons /= subSS.
case: (eqVneq (\prod_(j <- r) F j) 0) => [->|nProd0].
 by rewrite mulr0 size_poly0.
case: (eqVneq (F i) 0) => [->|neqFa0]; first by rewrite mul0r size_poly0.
rewrite (leq_trans (size_mul _ _)) //.
move/polySpred: neqFa0 ->.
rewrite addSn /= addSnnS.
suff: (size r <= (\sum_(j <- r) size (F j)).+1).
  by move/addn_subA <-; apply: leq_add.
apply: leqW.
apply: contraNeq nProd0.
rewrite eqb_id -ltnNge.
elim: {IH i} r => [//|i r IH /=].
rewrite !big_cons.
case (eqVneq (F i) 0) => [->|]; first by rewrite mul0r.
move/polySpred ->.
rewrite addSn -addn1 -[(size r).+1]addn1 leq_add2r.
move/(leq_ltn_trans (leq_addl _ _)).
move/IH.
move/eqP ->.
by rewrite mulr0.
Qed.

Lemma size_exp : forall p n, size (p ^+ n) <= ((size p).-1 * n).+1.
Proof.
move=> p n; case: (poly0Vpos p) => [-> | nzp].
  by case: n => [|n]; rewrite ?exprS ?mul0r size_poly0 ?size_poly1.
elim: n => [|n IHn]; first by rewrite size_poly1.
rewrite exprS (leq_trans (size_mul _ _)) //.
by rewrite -{1}(prednK nzp) mulnS -addnS leq_add2l.
Qed.

Lemma size_sign_mul : forall p n, size ((-1) ^+ n * p) = size p.
Proof.
move=> p n; rewrite -signr_odd.
by case: (odd ); rewrite ?mul1r // mulN1r size_opp.
Qed.

Lemma coef_Cmul : forall c p i, (c%:P * p)`_i = c * p`_i.
Proof.
move=> c p i; rewrite coef_mul big_ord_recl subn0.
by rewrite big1 => [|j _]; rewrite coefC !simp.
Qed.

Lemma coef_mulC : forall c p i, (p * c%:P)`_i = p`_i * c.
Proof.
move=> c p i; rewrite coef_mul_rev big_ord_recl subn0.
by rewrite big1 => [|j _]; rewrite coefC !simp.
Qed.

Lemma polyC_mul : {morph polyC : c1 c2 / c1 * c2}.
Proof.
by move=> c1 c2; apply/polyP=> [[|i]]; rewrite coef_Cmul !coefC ?simp.
Qed.

Lemma polyC_exp : forall n, {morph polyC : c / c ^+ n}.
Proof. by elim=> // n IHn c; rewrite !exprS polyC_mul IHn. Qed.

End PolynomialRingTheory.

Module PolynomialLalg.
Section PolynomialLalg.

Variable R : ringType.

Definition scale_poly a (p : {poly R}) := \poly_(i < size p) (a * p`_i).

Lemma scale_polyE : forall a p, scale_poly a p = a%:P * p.
Proof.
move=> a p; apply/polyP=> n.
have:= @leq_coef_size _ (scale_poly a p) n.
rewrite !coef_poly size_polyC.
case: (a =P 0) => /= Heq.
  rewrite Heq mul0r if_same => _; case: ltP=> Hu //.
  rewrite (eq_bigr (fun x => 0)); last by move=>*; rewrite coef0 mul0r.
  by rewrite big_const; elim: #|_|=> //= m Hm; rewrite add0r.
case: ltP=> // Hlt _.
rewrite big_ord_recl (eq_bigr (fun x => 0)); last first.
  by move=> *; rewrite coefC mul0r.
rewrite big_const coefC /= subn0.
by elim: #|_| =>  [|n1]; rewrite /= (addr0,add0r).
Qed.

Lemma scale_polyA : forall a b p,
  scale_poly a (scale_poly b p) = scale_poly (a * b) p.
Proof. by move=>*; rewrite !scale_polyE mulrA polyC_mul. Qed.

Lemma scale_1poly : left_id 1 scale_poly.
Proof. by move=> p; rewrite scale_polyE mul1r. Qed.

Lemma scale_poly_addr : forall a, {morph scale_poly a : p q / p + q}.
Proof. by move=> a p q; rewrite !scale_polyE mulr_addr. Qed.

Lemma scale_poly_addl : forall p, {morph scale_poly^~ p : a b / a + b}.
Proof. by move=> a p q; rewrite !scale_polyE polyC_add mulr_addl. Qed.

Lemma scale_poly_mull : forall a p q, scale_poly a (p * q) = scale_poly a p * q.
Proof. by move=> a p q; rewrite !scale_polyE mulrA. Qed.

Definition mixin :=
  LmodMixin scale_polyA scale_1poly scale_poly_addr scale_poly_addl.

End PolynomialLalg.
End PolynomialLalg.

Canonical Structure poly_lmodType (R: ringType) :=
  Eval hnf in LmodType R {poly R} (PolynomialLalg.mixin R).
Canonical Structure polynomial_lmodType (R : ringType) :=
  Eval hnf in [lmodType R of polynomial R for (poly_lmodType R)].
Canonical Structure poly_lalgType (R: ringType) :=
  Eval hnf in LalgType R {poly R} (@PolynomialLalg.scale_poly_mull R).
Canonical Structure polynomial_lalgType (R : ringType) :=
  Eval hnf in [lalgType R of polynomial R for (poly_lalgType R)].

Section PolynomialLalgTheory.

Variable R : ringType.

Implicit Types p q : {poly R}.

Lemma mul_polyC : forall a p, a%:P * p = a *: p.
Proof. by move=> a p; rewrite -PolynomialLalg.scale_polyE. Qed.

Lemma scale_poly1 : forall a, a *: 1 = a%:P :> {poly R}.
Proof. by move=> a; rewrite -mul_polyC mulr1. Qed.

Lemma coef_scaler : forall a p i, (a *: p)`_i = a * (p`_i).
Proof.
move=> a p i; move/implyP: (@leq_coef_size _ p i).
rewrite coef_poly implyNb; case/predU1P=> -> //.
by rewrite mulr0 if_same.
Qed.

End PolynomialLalgTheory.

Section PolynomialX.
(* Indeterminate, at last! *)
Variable R : ringType.

Implicit Types p q : {poly R}.

Definition polyX : {poly R} := Poly [:: 0; 1].

Local Notation "'X" := polyX.

Lemma polyseqX : 'X = [:: 0; 1] :> seq R.
Proof. by rewrite !polyseq_cons size_poly0 polyseq1. Qed.

Lemma size_polyX : size 'X = 2. Proof. by rewrite polyseqX. Qed.

Lemma size_factor : forall a : R, size ('X - a%:P) = 2%N.
Proof.
move=> a; rewrite size_addl size_polyX//.
by rewrite size_opp size_polyC; case: (_ != _).
Qed.

Lemma factor_eq0 : forall a, ('X - a%:P == 0) = false.
Proof. by move=> a; rewrite -size_poly_eq0 size_factor. Qed.

Lemma coefX : forall i, 'X`_i = (i == 1%N)%:R.
Proof. by move=> [|[|i]]; rewrite polyseqX //= nth_nil. Qed.

Lemma lead_coefX : lead_coef 'X = 1.
Proof. by rewrite /lead_coef polyseqX. Qed.

Lemma lead_coef_factor : forall x, lead_coef ('X - x%:P) = 1.
Proof.
by move=> x; rewrite lead_coefE size_factor coef_sub coefC coefX subr0.
Qed.

Lemma commr_polyX : forall p, GRing.comm p 'X.
Proof.
move=> p; apply/polyP=> i; rewrite coef_mul_rev coef_mul.
by apply: eq_bigr => j _; rewrite coefX commr_nat.
Qed.

Lemma coef_mulX : forall p i, (p * 'X)`_i = (if (i == 0)%N then 0 else p`_i.-1).
Proof.
move=> p i; rewrite coef_mul_rev big_ord_recl coefX ?simp.
case: i => [|i]; rewrite ?big_ord0 //= big_ord_recl polyseqX subn1 /=.
by rewrite big1 ?simp // => j _; rewrite nth_nil !simp.
Qed.

Lemma coef_Xmul : forall p i, ('X * p)`_i = (if (i == 0)%N then 0 else p`_i.-1).
Proof. by move=> p i; rewrite -commr_polyX coef_mulX. Qed.

Lemma poly_cons_def : forall p a, poly_cons a p = p * 'X + a%:P.
Proof.
move=> p a; apply/polyP=> i; rewrite coef_cons coef_add coef_mulX coefC.
by case: i => [|i]; rewrite !simp.
Qed.

Lemma size_amulX : forall p c,
   size (p * 'X + c%:P) =
     (if (size p == 0%N) && (c == 0) then 0%N else (size p).+1).
Proof. by move=> p c; rewrite -poly_cons_def size_poly_cons. Qed.

Lemma poly_ind : forall K : {poly R} -> Type,
  K 0 -> (forall p c, K p -> K (p * 'X + c%:P)) -> (forall p, K p).
Proof.
move=> K K0 Kcons p; rewrite -[p]polyseqK.
elim: {p}(p : seq R) => //= p c IHp; rewrite poly_cons_def; exact: Kcons.
Qed.

Lemma seq_mul_polyX : forall p, p != 0 -> p * 'X = 0 :: p :> seq R.
Proof.
move=> p nz_p.
by rewrite -[p * _]addr0 -poly_cons_def polyseq_cons size_poly_eq0 nz_p.
Qed.

Lemma lead_coef_mulX : forall p, lead_coef (p * 'X) = lead_coef p.
Proof.
move=> p; case: (eqVneq p 0) => [-> | nzp]; first by rewrite simp.
by rewrite /lead_coef !nth_last seq_mul_polyX.
Qed.

Local Notation "''X^' n" := ('X ^+ n).

Lemma coef_Xn : forall n i, 'X^n`_i = (i == n)%:R.
Proof.
elim=> [|n IHn] i; first exact: coef1.
by rewrite exprS coef_Xmul; case: i.
Qed.

Lemma seq_polyXn : forall n, 'X^n = ncons n 0 [:: 1] :> seq R.
Proof.
elim=> [|n IHn]; rewrite ?polyseq1 // exprSr seq_mul_polyX ?IHn //.
by rewrite -size_poly_eq0 IHn size_ncons addnS.
Qed.

Lemma size_polyXn : forall n, size 'X^n = n.+1.
Proof. by move=> n; rewrite seq_polyXn size_ncons addn1. Qed.

Lemma commr_polyXn : forall p n, GRing.comm p 'X^n.
Proof. by move=> p n; apply: commr_exp; exact: commr_polyX. Qed.

Lemma lead_coefXn : forall n, lead_coef 'X^n = 1.
Proof. by elim=> [|n IHn]; rewrite ?lead_coef1 // exprSr lead_coef_mulX. Qed.

Lemma coef_Xn_mul : forall n p i,
  ('X^n * p)`_i = if i < n then 0 else p`_(i - n).
Proof.
move=> n p; elim: n => [|n IHn] i; first by rewrite simp subn0.
by rewrite exprS -mulrA coef_Xmul; case: i.
Qed.

Lemma coef_mulXn : forall n p i,
  (p * 'X^n)`_i = if i < n then 0 else p`_(i - n).
Proof. by move=> n p i; rewrite commr_polyXn coef_Xn_mul. Qed.

(* Expansion of a polynomial as an indexed sum *)
Lemma poly_def : forall n E, \poly_(i < n) E i = \sum_(i < n) E i *: 'X^i.
Proof.
elim=> [|n IHn] E; first by rewrite big_ord0.
rewrite big_ord_recl /= poly_cons_def addrC expr0 scale_poly1; congr (_ + _).
rewrite (iota_addl 1 0) -map_comp IHn big_distrl /bump /=.
by apply: eq_bigr => i _; rewrite -scaler_mull exprSr.
Qed.

End PolynomialX.

Notation "'X" := (polyX _) : ring_scope.
Notation "''X^' n" := ('X ^+ n) : ring_scope.

Section PolynomialMonic.
(* Monic predicate *)
Variable R : ringType.

Implicit Types p q : {poly R}.

Definition monic p := lead_coef p == 1.

Lemma monicP : forall p, reflect (lead_coef p = 1) (monic p).
Proof. by move=> p; apply: (iffP eqP). Qed.

Lemma monic1 : monic 1. Proof. by rewrite /monic lead_coef1. Qed.
Lemma monicX : monic 'X. Proof. by rewrite /monic lead_coefX. Qed.
Lemma monicXn : forall n, monic 'X^n.
Proof. by move=> n; rewrite /monic lead_coefXn. Qed.

Lemma monic_neq0 : forall p, monic p -> p != 0.
Proof. move=> p; rewrite -lead_coef_eq0; move/eqP->; exact: nonzero1r. Qed.

Lemma lead_coef_monic_mul : forall p q,
  monic p -> lead_coef (p * q) = lead_coef q.
Proof.
move=> p q; move/eqP=> lp1.
case: (eqVneq q 0) => [->|nzq]; first by rewrite simp.
by rewrite lead_coef_proper_mul lp1 simp ?lead_coef_eq0.
Qed.

Lemma lead_coef_mul_monic : forall p q,
  monic q -> lead_coef (p * q) = lead_coef p.
Proof.
move=> p q; move/eqP=> lq1.
case: (eqVneq p 0) => [->|nzp]; first by rewrite simp.
by rewrite lead_coef_proper_mul lq1 simp ?lead_coef_eq0.
Qed.

Lemma size_monic_mul : forall p q,
  monic p -> q != 0 -> size (p * q) = (size p + size q).-1.
Proof.
move=> p q; move/eqP=> lp1 nzq.
by rewrite size_proper_mul // lp1 simp lead_coef_eq0.
Qed.

Lemma size_mul_monic : forall p q,
  p != 0 -> monic q -> size (p * q) = (size p + size q).-1.
Proof.
move=> p q nzp; move/eqP=> lq1.
by rewrite size_proper_mul // lq1 simp lead_coef_eq0.
Qed.

Lemma monic_mull : forall p q, monic p -> monic (p * q) = monic q.
Proof. by move=> p q mp; rewrite /monic lead_coef_monic_mul. Qed.

Lemma monic_mulr : forall p q, monic q -> monic (p * q) = monic p.
Proof. by move=> p q mq; rewrite /monic lead_coef_mul_monic. Qed.

Lemma monic_exp : forall p n, monic p -> monic (p ^+ n).
Proof.
by move=> p [|n] mp; [exact: monic1 | elim: n => // n; rewrite monic_mull].
Qed.

End PolynomialMonic.

Implicit Arguments monicP [R p].

Section PolynomialReg.
(* Some fact about regular elements *)
Variable R : ringType.

Implicit Types p q : {poly R}.

Lemma lreg_lead: forall p, lreg (lead_coef p) -> lreg p.
Proof.
move=> p H q Hpq; move: (head_coef_mul p q).
rewrite Hpq coef0; move/(@sym_equal _ _ _); move/H.
by move/eqP; rewrite lead_coef_eq0; move/eqP.
Qed.

Lemma rreg_lead: forall p, rreg (lead_coef p) -> rreg p.
Proof.
move=> p H q Hpq; move: (head_coef_mul q p).
rewrite Hpq coef0; move/(@sym_equal _ _ _); move/H.
by move/eqP; rewrite lead_coef_eq0; move/eqP.
Qed.

Lemma lreg_lead0: forall p, lreg (lead_coef p) -> p != 0.
Proof.
move=> p Hp; apply/eqP=> Hp0; case: (@lreg0 R).
by rewrite -lead_coef0 -Hp0.
Qed.

Lemma rreg_lead0: forall p, rreg (lead_coef p) -> p != 0.
Proof.
move=> p Hp; apply/eqP=> Hp0; case: (@rreg0 R).
by rewrite -lead_coef0 -Hp0.
Qed.

Lemma lreg_scale0: forall c p, lreg c -> (c *: p == 0) = (p == 0).
Proof.
move=> c p H; apply/idP/idP; last by move/eqP->; rewrite scaler0.
have Hc: c != 0 by apply/negP=> Hc; case: (@lreg0 R); rewrite -(eqP Hc).
case: (p =P 0)=> //; move/eqP=> Hp.
rewrite -lead_coef_eq0 -mul_polyC lead_coef_proper_mul lead_coefC.
   move/eqP; move/(H _)=> HH; case/eqP: Hp.
   by apply/eqP; rewrite -lead_coef_eq0 HH.
apply/eqP; move/(H _)=> HH; case/eqP: Hp.
by apply/eqP; rewrite -lead_coef_eq0 HH.
Qed.

Lemma rreg_scale0: forall c p, rreg c -> (p * c%:P == 0) = (p == 0).
Proof.
move=> c p H; apply/idP/idP; last by move/eqP->; rewrite simp.
have Hc: c != 0 by apply/negP=> Hc; case: (@rreg0 R); rewrite -(eqP Hc).
case: (p =P 0)=> //; move/eqP=> Hp.
rewrite -lead_coef_eq0 lead_coef_proper_mul lead_coefC.
   move/eqP; move/(H _)=> HH; case/eqP: Hp.
   by apply/eqP; rewrite -lead_coef_eq0 HH.
apply/eqP; move/(H _)=> HH; case/eqP: Hp.
by apply/eqP; rewrite -lead_coef_eq0 HH.
Qed.

Lemma lreg_size: forall c p, lreg c ->  size (c *: p) =  size p.
Proof.
move=> c p Hlr; case (p =P 0)=> Hp; first by rewrite Hp scaler0.
rewrite -mul_polyC size_proper_mul.
  by rewrite size_polyC; case: eqP=> // Hc; case: (@lreg0 R); rewrite -Hc.
rewrite lead_coefC; apply/eqP; move/Hlr.
by move/eqP; rewrite lead_coef_eq0=> HH; case: Hp; apply/eqP.
Qed.

Lemma rreg_size: forall c p, rreg c ->  size (p * (c%:P)) =  size p.
Proof.
move=> c p Hlr; case (p =P 0)=> Hp; first by rewrite Hp simp.
rewrite size_proper_mul.
  rewrite size_polyC; case: eqP=> // Hc; rewrite ?addnS ?simp //.
  by case: (@rreg0 R); rewrite -Hc.
rewrite lead_coefC; apply/eqP; move/Hlr.
by move/eqP; rewrite lead_coef_eq0=> HH; case: Hp; apply/eqP.
Qed.

Lemma rreg_div0: forall q r d: {poly R}, rreg (lead_coef d) ->
  size r < size d ->  (q * d + r == 0) = (q == 0) && (r == 0).
Proof.
move=> q r d Reg Hlt; apply/eqP/andP=> [Heq|]; last first.
  by case;move/eqP->; move/eqP->; rewrite !simp.
suff Hq: (q == 0) by split=> //; move/eqP: Heq; rewrite (eqP Hq) !simp.
move: Hlt.
have->: r = (-q) * d by apply: (@addrI _ (q * d)); rewrite Heq mulNr subrr.
rewrite mulNr size_opp -lead_coef_eq0.
case: eqP=> // Hq.
rewrite size_proper_mul; last first.
  by apply/negP; move/eqP;move/Reg=> Hnq; case: Hq.
case Hsq: (size q); last by rewrite ltnNge leq_addl.
by case: Hq; apply/eqP; rewrite lead_coef_eq0 -size_poly_eq0; apply/eqP.
Qed.

Lemma monic_comreg: forall p,
  monic p -> GRing.comm p (lead_coef p)%:P /\ rreg (lead_coef p).
Proof.
move=> p; rewrite /monic; move/eqP->; split; last by exact: rreg1.
by rewrite /GRing.comm !simp.
Qed.

End PolynomialReg.

(* Horner evaluation of polynomials *)

Section EvalPolynomial.

Variable R : ringType.
Implicit Types p q : {poly R}.
Implicit Types x a c : R.

Fixpoint horner s x {struct s} :=
  if s is a :: s' then horner s' x * x + a else 0.
Definition hornerp p := nosimpl horner (polyseq p).

Local Notation "p .[ x ]" := (hornerp p x) : ring_scope.

Lemma horner_cons : forall x s a, horner (a :: s) x = (horner s x) * x + a.
Proof. by []. Qed.

Lemma horner0 : forall x, (0 : {poly R}).[x] = 0.
Proof. by rewrite /hornerp seq_poly0. Qed.

Lemma hornerC : forall c x, (c%:P).[x] = c.
Proof.
by move=> *; rewrite /hornerp polyseqC; case: eqP; rewrite /= ?simp.
Qed.

Lemma hornerX : forall x, 'X.[x] = x.
Proof. by move=> x; rewrite /hornerp polyseqX /= !simp. Qed.

Lemma horner_pcons : forall p c x, (poly_cons c p).[x] = p.[x] * x + c.
Proof.
move=> p c x; rewrite /hornerp polyseq_cons.
case/polyseq: p; rewrite //= !simp; exact: hornerC.
Qed.

Lemma horner_amulX : forall p c x, (p * 'X + c%:P).[x] = p.[x] * x + c.
Proof. by move=> p c x; rewrite -poly_cons_def horner_pcons. Qed.

Lemma horner_mulX : forall p x, (p * 'X).[x] = p.[x] * x.
Proof. by move=> p x; move: (horner_amulX p 0 x); rewrite !simp. Qed.

Lemma horner_Poly : forall s x, (Poly s).[x] = horner s x.
Proof.
by move=> s x; elim: s => [|a s /= <-]; rewrite (horner0, horner_pcons).
Qed.

Lemma horner_coef : forall p x,
  p.[x] = \sum_(i < size p) p`_i * x ^+ i.
Proof.
rewrite/hornerp=> p x; elim: {p}(p : seq R) => /= [|a s ->].
  by rewrite big_ord0.
rewrite big_ord_recl simp addrC big_distrl /=.
by congr (_ + _); apply: eq_bigr => i _; rewrite -mulrA exprSr.
Qed.

Lemma horner_coef_wide : forall n p x,
  size p <= n -> p.[x] = \sum_(i < n) p`_i * x ^+ i.
Proof.
move=> n p x le_p_n.
rewrite horner_coef (big_ord_widen n (fun i => p`_i * x ^+ i)) // big_mkcond.
by apply: eq_bigr => i _; case: ltnP => // le_p_i; rewrite nth_default ?simp.
Qed.

Lemma horner_poly : forall n E x,
  (\poly_(i < n) E i).[x] = \sum_(i < n) E i * x ^+ i.
Proof.
move=> n E x; rewrite (@horner_coef_wide n) ?size_poly //.
by apply: eq_bigr => i _; rewrite coef_poly ltn_ord.
Qed.

Lemma horner_opp : forall p x, (- p).[x] = - p.[x].
Proof.
move=> p x; rewrite horner_poly horner_coef -sumr_opp /=.
by apply: eq_bigr => i _; rewrite mulNr.
Qed.

Lemma horner_add : forall p q x, (p + q).[x] = p.[x] + q.[x].
Proof.
move=> p q x; rewrite horner_poly; set m := maxn _ _.
rewrite !(@horner_coef_wide m) ?leq_maxr ?leqnn ?orbT // -big_split /=.
by apply: eq_bigr => i _; rewrite -mulr_addl.
Qed.

Lemma horner_factor : forall (a x : R), ('X - a%:P).[x] = x - a.
Proof. by move=> a x; rewrite horner_add horner_opp hornerC hornerX. Qed.

Lemma horner_sum : forall I r (P : pred I) F x,
  (\sum_(i <- r | P i) F i).[x] = \sum_(i <- r | P i) (F i).[x].
Proof.
move=> I r P F x; pose appx p := p.[x].
apply: (big_morph appx) => [p q|]; [exact: horner_add | exact: horner0].
Qed.

Lemma horner_Cmul : forall c p x, (c%:P * p).[x] = c * p.[x].
Proof.
move=> c p x; move:p.
apply:(@poly_ind R) => [|p d IHp]; first by rewrite !(simp, horner0).
rewrite mulr_addr -polyC_mul mulrA -!poly_cons_def !horner_pcons IHp.
by rewrite -mulrA -mulr_addr.
Qed.

Lemma horner_scaler : forall c p x, (c *: p).[x] = c * p.[x].
Proof. by move=>*; rewrite -mul_polyC horner_Cmul. Qed.

Lemma horner_mulrn : forall n p x, (p *+ n).[x] = p.[x] *+ n.
Proof.
elim=> [| n Hrec] p x; first by rewrite !mulr0n horner0.
by rewrite !mulrS horner_add Hrec.
Qed.

Definition com_coef p (x : R) := forall i, p`_i * x = x * p`_i.

Definition com_poly p x := x * p.[x] = p.[x] * x.

Lemma com_coef_poly : forall p x, com_coef p x -> com_poly p x.
Proof.
move=> p x com; rewrite /com_poly !horner_coef big_distrl big_distrr /=.
by apply: eq_bigr => i _; rewrite /= mulrA -com -!mulrA commr_exp.
Qed.

Lemma com_poly0 : forall x, com_poly 0 x.
Proof. by move=> *; rewrite /com_poly !horner0 !simp. Qed.

Lemma com_poly1 : forall x, com_poly 1 x.
Proof. by move=> *; rewrite /com_poly !hornerC !simp. Qed.

Lemma com_polyX : forall x, com_poly 'X x.
Proof. by move=> *; rewrite /com_poly !hornerX. Qed.

Lemma horner_mul_com : forall p q x,
  com_poly q x -> (p * q).[x] = p.[x] * q.[x].
Proof.
move=> p q x com_qx; move: p.
apply:(@poly_ind R)=> [|p c IHp]; first by rewrite !(simp, horner0).
rewrite mulr_addl -poly_cons_def horner_pcons mulr_addl -!mulrA.
rewrite com_qx -commr_polyX !mulrA -{}IHp -[_ * 'X]addr0 -poly_cons_def.
by rewrite horner_add horner_pcons simp horner_Cmul.
Qed.

Lemma horner_exp_com : forall p x n, com_poly p x -> (p ^+ n).[x] = p.[x] ^+ n.
Proof.
move=> p x n com_px; elim: n => [|n IHn]; first by rewrite hornerC.
by rewrite -addn1 !exprn_addr !expr1 -IHn horner_mul_com.
Qed.

Lemma hornerXn : forall x n, ('X^n).[x] = x ^+ n.
Proof. by move=> x n; rewrite horner_exp_com /com_poly hornerX. Qed.

Definition horner_lin_com :=
  (horner_add, horner_opp, hornerX, hornerC, horner_pcons,
   simp, horner_Cmul, horner_scaler,
   (fun p x => horner_mul_com p (com_polyX x))).

Lemma factor0 : forall c, ('X - c%:P).[c] = 0.
Proof. by move=> c; rewrite !horner_lin_com addrN. Qed.

Lemma seq_factor : forall c, 'X - c%:P = [:: - c; 1] :> seq R.
Proof.
move=> c; rewrite -['X]mul1r -polyC_opp -poly_cons_def.
by rewrite polyseq_cons size_poly1 polyseq1.
Qed.

Lemma monic_factor : forall c, monic ('X - c%:P).
Proof. by move=> c; rewrite /monic /lead_coef seq_factor. Qed.

Definition root p : pred R := fun x => p.[x] == 0.

Lemma mem_root : forall p x, x \in root p = (p.[x] == 0).
Proof. by []. Qed.

Lemma rootE : forall p x , (root p x = (p.[x] == 0))
                         * (x \in root p = (p.[x] == 0)).
Proof. by []. Qed.

Lemma rootP : forall p x, reflect (p.[x] = 0) (root p x).
Proof. by move=> p x; apply: (iffP eqP). Qed.

Lemma rootPt : forall p x, reflect (p.[x] == 0) (root p x).
Proof. by move=> p x; apply: (iffP idP). Qed.

Lemma rootPf : forall p x, reflect ((p.[x] == 0) = false) (~~root p x).
Proof. by move=> p x; apply: (iffP negPf). Qed.

Lemma root0 : forall x, root 0 x.
Proof. by move=> x; rewrite rootE ?hornerC. Qed.

Lemma root1 : forall x, ~~root 1 x.
Proof. by move=> x; rewrite rootE ?hornerC oner_eq0. Qed.

Lemma rootC : forall a x, root a%:P x = (a == 0).
Proof. by move=> a x; rewrite rootE ?hornerC. Qed.

Lemma rootX : forall x, root 'X x = (x == 0).
Proof. by move=> x; rewrite rootE hornerX. Qed.

Lemma root_opp : forall p x, root (- p) x = root p x.
Proof. by move=> p x; rewrite !rootE horner_opp eqr_oppC oppr0. Qed.

Lemma root_factor : forall a b, root ('X - b%:P) a = (a == b).
Proof. by move=> a b; rewrite rootE horner_factor subr_eq0. Qed.

Lemma root_addX : forall a b, root ('X + b%:P) a = (a == -b).
Proof. by move=> a b; rewrite -[_%:P]opprK -polyC_opp root_factor. Qed.

Theorem factor_theorem : forall p c,
  reflect (exists q, p = q * ('X - c%:P)) (root p c).
Proof.
move=> p c; apply: (iffP eqP)=> [root_p_c | [q]]; last first.
  by move->; rewrite horner_mul_com /com_poly factor0 ?simp.
suff [[d q] Hq]: exists d, p = d.1%:P + d.2 * ('X - c%:P).
  exists q; rewrite Hq.
  suff->: d = 0 by rewrite add0r.
  have eX: ('X - c%:P).[c] = 0.
    by rewrite horner_add horner_opp hornerX hornerC subrr.
  have F1: com_poly ('X - c%:P) c by rewrite /com_poly eX mul0r mulr0.
  by rewrite -root_p_c Hq horner_add horner_mul_com // hornerC eX mulr0 addr0.
move: (p); apply: poly_ind; first by exists (0,0%:P); rewrite add0r mul0r.
move=> p1 c1 [[c2 q] Hq].
have Hx: p1 * 'X = (c2 * c)%:P + ('X * q + c2%:P) * ('X - c%:P).
 by rewrite addrC mulr_addl [c2%:P * _]mulr_addr !addrA mulrN polyC_mul
             addrNK addrC -mulrA -commr_polyX Hq mulr_addl.
by exists (c1 + c2 * c, 'X * q + c2%:P); rewrite /= addrC polyC_add Hx !addrA.
Qed.

Lemma monic_prod_factors : forall rs : seq R,
  monic (\prod_(z <- rs) ('X - z%:P)).
Proof.
by move=> rs; apply big_ind=> *; rewrite (monic1, monic_factor, monic_mull).
Qed.

Lemma size_prod_factors : forall rs : seq R,
  size (\prod_(z <- rs) ('X - z%:P)) = (size rs).+1.
Proof.
elim=> [|z rs' IHrs]; rewrite (big_nil, big_cons) ?size_poly1 //.
by rewrite size_monic_mul ?monic_factor -?size_poly_eq0 ?IHrs ?seq_factor.
Qed.

Lemma size_Xn_sub_1 : forall n, n > 0 -> size ('X^n - 1 : {poly R}) = n.+1.
Proof.
by move=> n n_gt0; rewrite size_addl size_polyXn // size_opp size_poly1.
Qed.

Lemma monic_Xn_sub_1 : forall n, n > 0 -> monic ('X^n - 1 : {poly R}).
Proof.
move=> n n_gt0; rewrite /monic lead_coefE size_Xn_sub_1 // coef_sub.
by rewrite coef_Xn coef1 eqxx eqn0Ngt n_gt0 subr0.
Qed.

Definition root_of_unity n : pred R := root ('X^n - 1).
Local Notation "n .-unity_root" := (root_of_unity n) : ring_scope.

Lemma unity_rootE : forall n z, n.-unity_root z = (z ^+ n == 1).
Proof.
move=> n z; rewrite /root_of_unity rootE.
by rewrite horner_add horner_opp hornerXn hornerC subr_eq0.
Qed.

Lemma unity_rootP : forall n z, reflect (z ^+ n = 1) (n.-unity_root z).
Proof. move=> n z; rewrite unity_rootE; exact: eqP. Qed.

Definition primitive_root_of_unity n z :=
  (n > 0) && (forallb i : 'I_n, i.+1.-unity_root z == (i.+1 == n)).
Local Notation "n .-primitive_root" := (primitive_root_of_unity n) : ring_scope.

Lemma prim_order_exists : forall n z,
  n > 0 -> z ^+ n = 1 -> {m | m.-primitive_root z & (m %| n)}.
Proof.
move=> n z n_gt0 zn1.
have: exists m, (m > 0) && (z ^+ m == 1) by exists n; rewrite n_gt0 /= zn1.
case/ex_minnP=> m; case/andP=> m_gt0; move/eqP=> zm1 m_min.
exists m.
  apply/andP; split=> //; apply/forallP=> i; apply/eqP; case: i => i /=.
  rewrite leq_eqVlt unity_rootE.
  case: eqP => [-> _ | _]; first by rewrite zm1 eqxx.
  by apply: contraTF => zi1; rewrite -leqNgt m_min.
have: n %% m < m by rewrite ltn_mod.
apply: contraLR; rewrite -lt0n -leqNgt => nm_gt0; apply: m_min.
by rewrite nm_gt0 /= exprn_mod ?zn1.
Qed.

Variables (n : nat) (z : R).
Hypothesis prim_z : n.-primitive_root z.

Lemma prim_order_gt0 : n > 0. Proof. by case/andP: prim_z. Qed.
Let n_gt0 := prim_order_gt0.

Lemma prim_expr_order : z ^+ n = 1.
Proof.
case/andP: prim_z => _; rewrite -(prednK n_gt0); move/forallP; move/(_ ord_max).
by rewrite unity_rootE eqxx; do 2!move/eqP.
Qed.

Lemma prim_expr_mod : forall i, z ^+ (i %% n) = z ^+ i.
Proof. move=> i; exact: exprn_mod prim_expr_order. Qed.

Lemma prim_order_dvd : forall i, (n %| i) = (z ^+ i == 1).
Proof.
move=> i; move: n_gt0; rewrite -prim_expr_mod /dvdn -(ltn_mod i).
case: {i}(i %% n)%N => [|i] lt_i; first by rewrite !eqxx.
case/andP: prim_z => _; move/forallP; move/(_ (Ordinal (ltnW lt_i))).
by move/eqP; rewrite unity_rootE eqn_leq andbC leqNgt lt_i.
Qed.

Lemma eq_prim_root_expr : forall i j, (z ^+ i == z ^+ j) = (i == j %[mod n]).
Proof.
move=> i j; wlog le_ji: i j / j <= i.
  move=> IH; case: (leqP j i); last move/ltnW; move/IH=> //.
  by rewrite eq_sym (eq_sym (j %% n)%N).
rewrite -{1}(subnKC le_ji) exprn_addr -prim_expr_mod eqn_mod_dvd //.
rewrite prim_order_dvd; apply/eqP/eqP=> [|->]; last by rewrite mulr1.
move/(congr1 ( *%R (z ^+ (n - j %% n)))); rewrite mulrA -exprn_addr.
by rewrite subnK ?prim_expr_order ?mul1r // ltnW ?ltn_mod.
Qed.

End EvalPolynomial.

Notation "p .[ x ]" := (hornerp p x) : ring_scope.
Notation "n .-unity_root" := (root_of_unity n) : ring_scope.
Notation "n .-primitive_root" := (primitive_root_of_unity n) : ring_scope.

Implicit Arguments rootP [R p x].
Implicit Arguments rootPf [R p x].
Implicit Arguments rootPt [R p x].
Implicit Arguments unity_rootP [R n z].

(* Container morphism. *)
Section MapPoly.

Variables (aR rR : ringType).

Section Definitions.

Variable f : aR -> rR.

Definition map_poly (p : {poly aR}) := \poly_(i < size p) f p`_i.

(* Alternative definition; the one above is more convenient because it lets *)
(* us use the lemmas on \poly, e.g., size (map_poly p) <= size p is an      *)
(* instance of size_poly.                                                   *)
Lemma map_polyE : forall p, map_poly p = Poly (map f p).
Proof.
move=> p; congr Poly.
apply: (@eq_from_nth _ 0); rewrite size_mkseq ?size_map // => i lt_i_p.
by rewrite (nth_map 0) ?nth_mkseq.
Qed.

Definition commr_rmorph u := forall x, GRing.comm u (f x).

Definition horner_morph u of commr_rmorph u := fun p => (map_poly p).[u].

End Definitions.

Section Additive.

Variable f : {additive aR -> rR}.

Local Notation "p ^f" := (map_poly f p) : ring_scope.

Lemma coef_map : forall p i, p^f`_i = f p`_i.
Proof.
move=> p i; rewrite coef_poly; case: ltnP => // le_p_i.
by rewrite nth_default ?raddf0.
Qed.

Lemma map_poly_is_additive : additive (map_poly f).
Proof.
by move=> p q; apply/polyP=> i; rewrite !(coef_map, coef_sub) raddf_sub.
Qed.

Canonical Structure map_poly_additive := Additive map_poly_is_additive.


Lemma map_polyC : forall a, (a%:P)^f = (f a)%:P.
Proof.
by move=> a; apply/polyP=> i; rewrite !(coef_map, coefC) -!mulrb raddfMn.
Qed.

Lemma lead_coef_map_eq : forall p,
  f (lead_coef p) != 0 -> lead_coef p^f = f (lead_coef p).
Proof.
move=> p fp_nz; rewrite lead_coef_poly // lt0n size_poly_eq0.
by apply: contra fp_nz; move/eqP->; rewrite lead_coef0 raddf0.
Qed.

End Additive.

Variable f : {rmorphism aR -> rR}.
Implicit Types p : {poly aR}.

Local Notation "p ^f" := (map_poly f p) : ring_scope.

Lemma map_poly_is_rmorphism : GRing.rmorphism (map_poly f).
Proof.
split; first exact: map_poly_is_additive.
split=> [p q|]; apply/polyP=> i; last by rewrite !(coef_map, coef1) /= rmorph_nat.
rewrite coef_map /= !coef_mul /= !rmorph_sum; apply: eq_bigr => j _.
by rewrite !coef_map rmorphM.
Qed.
Canonical Structure map_poly_rmorphism := RMorphism map_poly_is_rmorphism.

Lemma map_polyX : ('X)^f = 'X.
Proof. by apply/polyP=> i; rewrite coef_map !coefX /= rmorph_nat. Qed.

Lemma map_polyXn : forall n, ('X^n)^f = 'X^n.
Proof. by move=> n; rewrite rmorphX /= map_polyX. Qed.

Lemma map_poly_scaler : forall k (p: {poly aR}), (k *: p)^f = f k *: (p^f).
Proof.
by move=> k p; apply/polyP=> i; rewrite !(coef_map, coef_scaler) /= rmorphM.
Qed.

Lemma horner_map : forall p x, p^f.[f x] = f p.[x].
Proof.
move=> p x; rewrite map_polyE horner_Poly /hornerp; move/polyseq: p.
by elim=> /= [|a p ->]; rewrite !(rmorph0, rmorphD, rmorphM).
Qed.

Lemma map_com_poly : forall p x, com_poly p x -> com_poly p^f (f x).
Proof. by move=> p x; rewrite /com_poly horner_map -!rmorphM // => ->. Qed.

Lemma map_com_coef : forall p x, com_coef p x -> com_coef p^f (f x).
Proof. by move=> p x cpx i; rewrite coef_map -!rmorphM ?cpx. Qed.

Lemma root_map_poly : forall p x, root p x -> root p^f (f x).
Proof. by move=> p x px0; rewrite rootE horner_map (eqP px0) rmorph0. Qed.

Lemma rmorph_unity_root : forall n z, n.-unity_root z -> n.-unity_root (f z).
Proof.
move=> n z; move/root_map_poly; rewrite rootE rmorph_sub horner_add horner_opp.
by rewrite /= map_polyXn rmorph1 hornerC hornerXn subr_eq0 unity_rootE.
Qed.

Variable u : rR.
Hypothesis cfu : commr_rmorph f u.

Lemma horner_morphC : forall a, horner_morph cfu a%:P = f a.
Proof. by move=> a; rewrite /horner_morph map_polyC hornerC. Qed.

Lemma horner_morphX : horner_morph cfu 'X = u.
Proof. by rewrite /horner_morph map_polyX hornerX. Qed.

Lemma horner_is_rmorphism : GRing.rmorphism (horner_morph cfu).
Proof.
split=> [p q|]; first by rewrite /horner_morph rmorph_sub horner_add horner_opp.
split=> [p q|]; last by rewrite /horner_morph rmorph1 hornerC.
rewrite /horner_morph rmorphM /= horner_mul_com //.
by apply: com_coef_poly => i; rewrite coef_map cfu.
Qed.
Canonical Structure horner_additive := Additive horner_is_rmorphism.
Canonical Structure horner_rmorphism := RMorphism horner_is_rmorphism.

End MapPoly.

(* Morphisms from the polynomial ring, and the initiality of polynomials  *)
(* with respect to these.                                                 *)
Section MorphPoly.

Variable (aR rR : ringType) (pf : {rmorphism {poly aR} -> rR}).

Lemma polyC_is_rmorphism : GRing.rmorphism (@polyC aR).
Proof.
by do 2?[split]=> // a b; rewrite ?(polyC_opp, polyC_add, polyC_mul).
Qed.
Canonical Structure polyC_additive := Additive polyC_is_rmorphism.
Canonical Structure polyC_rmorphism := RMorphism polyC_is_rmorphism.

Lemma poly_morphX_comm : commr_rmorph (pf \o @polyC aR) (pf 'X).
Proof. by move=> a; red; rewrite /= -!rmorphM // commr_polyX. Qed.

Lemma poly_initial : pf =1 horner_morph poly_morphX_comm.
Proof.
apply: poly_ind => [|p a IHp]; first by rewrite !rmorph0.
by rewrite !rmorphD !rmorphM /= -{}IHp horner_morphC ?horner_morphX.
Qed.

End MorphPoly.

Module PolynomialComRing.
Section PolynomialComRing.

Variable R : comRingType.
Implicit Types p q : {poly R}.

Lemma axiom : forall p q, p * q = q * p.
Proof.
move=> p q; apply/polyP=> i; rewrite coef_mul coef_mul_rev.
by apply: eq_bigr => j _; rewrite mulrC.
Qed.

End PolynomialComRing.
End PolynomialComRing.

Canonical Structure poly_comRingType (R: comRingType) :=
  Eval hnf in ComRingType {poly R} (@PolynomialComRing.axiom R).
Canonical Structure polynomial_comRingType (R: comRingType) :=
  Eval hnf in [comRingType of polynomial R for (poly_comRingType R)].
Canonical Structure poly_algType (R: comRingType) :=
  Eval hnf in CommAlgType R {poly R}.
Canonical Structure polynomial_algType (R: comRingType) :=
  Eval hnf in [algType R of polynomial R for (poly_algType R)].

Section PolynomialComRingTheory.

Variable R : comRingType.
Implicit Types p q : {poly R}.

Lemma horner_mul : forall p q x, (p * q).[x] = p.[x] * q.[x].
Proof. move=> p q x; rewrite horner_mul_com //; exact: mulrC. Qed.

Lemma horner_exp : forall p x n, (p ^+ n).[x] = p.[x] ^+ n.
Proof. move=> p x n; rewrite horner_exp_com //; exact: mulrC. Qed.

Lemma horner_prod : forall I r (P : pred I) (F : I -> {poly R}) x,
  (\prod_(i <- r | P i) F i).[x] = \prod_(i <- r | P i) (F i).[x].
Proof.
move=> I r P F x; pose appx p := p.[x].
apply: (big_morph appx) => [p q|]; [exact: horner_mul | exact: hornerC].
Qed.

Definition horner_lin :=
  (horner_add, horner_opp, hornerX, hornerC, horner_pcons,
   simp, horner_Cmul, horner_scaler, horner_mul).

End PolynomialComRingTheory.

Module PolynomialIdomain.
Section PolynomialIdomain.

(* idomain structure on poly *)

Variable R : idomainType.

Implicit Types p q r m n d : {poly R}.

Lemma size_mul_id : forall p q,
  p != 0 -> q != 0 -> size (p * q) = (size p + size q).-1.
Proof.
move=> p q nzp nzq; apply: size_proper_mul.
by rewrite mulf_eq0 !lead_coef_eq0 negb_or nzp nzq.
Qed.

Lemma mixin : forall p q, p * q = 0 -> (p == 0) || (q == 0).
Proof.
move=> p q pq0; apply/norP=> [[p_nz q_nz]]; move/eqP: (size_mul_id p_nz q_nz).
rewrite eq_sym pq0 size_poly0 -leqn0 -subn1 leq_sub_add leqNgt -addnS.
by rewrite leq_add // lt0n size_poly_eq0.
Qed.

Definition poly_unit : pred {poly R} :=
  fun p => (size p == 1%N) && GRing.unit p`_0.

Definition poly_inv p := if poly_unit p then (p`_0)^-1%:P else p.

Lemma poly_mulVp : {in poly_unit, left_inverse 1 poly_inv *%R}.
Proof.
move=> p Up; rewrite /poly_inv [poly_unit p]Up.
case/andP: Up => szp1 Up.
by rewrite {2}[p]size1_polyC ?(eqP szp1) // -polyC_mul mulVr.
Qed.

Lemma poly_intro_unit : forall p q, q * p = 1 -> poly_unit p.
Proof.
move=> p q pq1; have: size (q * p) == 1%N by rewrite pq1 size_poly1.
case: (eqVneq p 0) => [-> | p_nz]; first by rewrite mulr0 size_poly0.
case: (eqVneq q 0) => [-> | q_nz]; first by rewrite mul0r size_poly0.
rewrite size_mul_id //.
rewrite -1?[size p]prednK -1?[size q]prednK ?lt0n ?size_poly_eq0 //.
rewrite addnS eqSS addn_eq0 -!subn1 !subn_eq0.
case/andP=> szq1 szp1; rewrite /poly_unit eqn_leq szp1 polySpred //.
apply/unitrP; exists q`_0; rewrite 2!mulrC.
move/(congr1 (fun r : {poly R} => r`_0)): pq1.
by rewrite {1}(size1_polyC szp1) {1}(size1_polyC szq1) -polyC_mul !coefC.
Qed.

Lemma poly_inv_out : {in predC poly_unit, poly_inv =1 id}.
Proof. by move=> p nUp; rewrite /poly_inv -if_neg [~~ _]nUp. Qed.

Definition comUnitMixin :=
  ComUnitRingMixin poly_mulVp poly_intro_unit poly_inv_out.

End PolynomialIdomain.
End PolynomialIdomain.

Canonical Structure poly_unitRingType (R : idomainType) :=
  Eval hnf in UnitRingType {poly R} (PolynomialIdomain.comUnitMixin R).
Canonical Structure polynomial_unitRingType (R : idomainType) :=
  Eval hnf in [unitRingType of polynomial R for (poly_unitRingType R)].

Canonical Structure poly_unitAlgType (R : idomainType) :=
  Eval hnf in [unitAlgType R of {poly R}].
Canonical Structure polynomial_unitAlgType (R : idomainType) :=
  Eval hnf in [unitAlgType R of polynomial R].

Canonical Structure poly_comUnitRingType (R : idomainType) :=
  Eval hnf in [comUnitRingType of {poly R}].
Canonical Structure polynomial_comUnitRingType (R : idomainType) :=
  Eval hnf in [comUnitRingType of polynomial R].

Canonical Structure poly_idomainType (R : idomainType) :=
  Eval hnf in IdomainType {poly R} (@PolynomialIdomain.mixin R).
Canonical Structure polynomial_idomainType (R : idomainType) :=
  Eval hnf in [idomainType of polynomial R for (poly_idomainType R)].

Section PolynomialIdomainTheory.

Variable R : idomainType.

Implicit Types x y : R.
Implicit Types p q r : {poly R}.

Lemma poly_unitE : forall p, GRing.unit p = (size p == 1%N) && GRing.unit p`_0.
Proof. by []. Qed.

Lemma poly_invE : forall p, p ^-1 = if GRing.unit p then (p`_0)^-1%:P else p.
Proof. by []. Qed.

Lemma polyCV : forall (c : R), c%:P^-1 = (c^-1)%:P.
Proof.
move=> c; rewrite poly_invE poly_unitE size_polyC coefC eqxx.
case c0: (c == 0)=> /=; first by rewrite (eqP c0) invr0.
by case uc: (_ c)=> //; rewrite [c^-1]invr_out ?uc.
Qed.

Lemma root_mul : forall p q x, root (p * q) x = (root p x) || (root q x).
Proof. by move=> p q x; rewrite !rootE horner_mul mulf_eq0. Qed.

Lemma root_scaler : forall a c p, c != 0 -> root (c *: p) a = (root p a).
Proof. by move=> a c p hc; rewrite -mul_polyC root_mul rootC (negPf hc). Qed.

Lemma size_mul_id : forall p q,
  p != 0 -> q != 0 -> size (p * q) = (size p + size q).-1.
Proof. exact: PolynomialIdomain.size_mul_id. Qed.

Lemma size_polyC_mul : forall c p, c != 0 -> size (c%:P * p) = size p.
Proof.
move=> c p Ec; case: (eqVneq p 0) => [-> | nzp]; first by rewrite simp.
by rewrite size_mul_id ?polyC_eq0 // size_polyC Ec.
Qed.

Lemma size_scaler: forall c p, c != 0 -> size (c *: p) = size p.
Proof.  by intros; rewrite  -mul_polyC size_polyC_mul. Qed.

Lemma lead_coef_Imul : forall p q,
  lead_coef (p * q) = lead_coef p * lead_coef q.
Proof.
move=> p q.
case: (eqVneq p 0) => [->|nzp]; first by rewrite !(simp, lead_coef0).
case: (eqVneq q 0) => [->|nzq]; first by rewrite !(simp, lead_coef0).
by rewrite lead_coef_proper_mul // mulf_eq0 !lead_coef_eq0 negb_or nzp nzq.
Qed.

Lemma scale_poly_eq0: forall a p, (a *: p == 0) =  (a == 0) || (p == 0).
Proof. by move=> a p; rewrite -mul_polyC mulf_eq0 polyC_eq0. Qed.

 Lemma size_prod_id :  forall (I : finType) (P : pred I) (F : I -> {poly R}),
   (forall i, P i -> (F i != 0)) ->
   size (\prod_(i | P i) F i) = ((\sum_(i | P i) size (F i)).+1 - #|P|)%N.
 Proof.
 move=> I P F.
 move/prodf_neq0.
 rewrite cardE -filter_index_enum -!(big_filter _ P).
 elim: (filter P _) => {P} [|i r IHr]; first by rewrite !big_nil size_poly1.
 rewrite !big_cons /= mulf_eq0 negb_or.
 move/andP => [Fine0 allne0].
 rewrite size_mul_id -?(prodf_neq0 r) // subSS IHr //.
 move/polySpred: Fine0 => ->.
 rewrite addSn /= addSnnS addn_subA //.
 clear -allne0.
 elim: r allne0 => [|i r IHr] /=; first by rewrite big_nil.
 rewrite !big_cons /= mulf_eq0 negb_or.
 move/andP => [Fine0 allne0].
 rewrite -add1n -addnS leq_add //; last by apply: IHr.
 by rewrite lt0n size_poly_eq0.
Qed.

Lemma size_exp_id : forall p (n : nat),
  (size (p ^+ n)).-1 = ((size p).-1 * n)%N.
Proof.
move=> p; elim=> [|n IHn]; first by rewrite expr0 size_poly1 muln0.
have [-> | p_nz] := (eqVneq p 0); first by rewrite exprS mul0r size_poly0.
rewrite exprS size_mul_id ?expf_neq0 // mulnS -{}IHn.
by rewrite polySpred // [size (p ^+ n)]polySpred ?expf_neq0 ?addnS.
Qed.

Lemma lead_coef_exp_id : forall p (n : nat),
  lead_coef (p ^+ n) = lead_coef p ^+ n.
Proof.
move=> p; elim=> [|n IHn]; first by rewrite !expr0 lead_coef1.
by rewrite !exprS lead_coef_Imul IHn.
Qed.

Lemma root_prod_factors : forall rs x,
  root (\prod_(z <- rs) ('X - z%:P)) x = (x \in rs).
Proof.
move=> rs x.
elim: rs => [|z rs IHrs]; first by rewrite rootE big_nil hornerC oner_eq0.
by rewrite big_cons root_mul IHrs root_factor.
Qed.

Lemma root_exp_factors : forall n z x, root (('X - z%:P) ^+ n.+1) x = (x == z).
Proof.
by move=> n z x; rewrite rootE horner_exp expf_eq0 [_ == 0]root_factor.
Qed.

Lemma size_factor_exp : forall n x, size (('X - x%:P) ^+ n) = n.+1.
Proof.
move=> n x; rewrite -[size _]prednK ?size_exp_id ?size_factor ?mul1n //.
by rewrite lt0n size_poly_eq0 expf_eq0 factor_eq0 andbF.
Qed.

End PolynomialIdomainTheory.

Section MapFieldPoly.

Variables (F : fieldType) (R : ringType) (f : {rmorphism F -> R}).

Local Notation "p ^f" := (map_poly f p) : ring_scope.

Lemma size_map_poly : forall p, size p^f = size p.
Proof.
move=> p; case: (eqVneq p 0) => [-> | p_nz].
  by rewrite rmorph0 !size_poly0.
by rewrite size_poly_eq // fmorph_eq0 // lead_coef_eq0.
Qed.

Lemma lead_coef_map : forall p, lead_coef p^f = f (lead_coef p).
Proof.
move=> p; case: (eqVneq p 0) => [-> | p_nz].
  by rewrite rmorph0 !lead_coef0 rmorph0.
by rewrite lead_coef_map_eq // fmorph_eq0 // lead_coef_eq0.
Qed.

Lemma map_poly_eq0 : forall p, (p^f == 0) = (p == 0).
Proof. by move=> p; rewrite -!size_poly_eq0 size_map_poly. Qed.

Lemma map_poly_inj : injective (map_poly f).
Proof.
move=> p q eqfpq; apply/eqP; rewrite -subr_eq0 -map_poly_eq0.
by rewrite rmorph_sub /= eqfpq subrr.
Qed.

Lemma map_field_poly_monic : forall p, monic p^f = monic p.
Proof.
by move=> p; rewrite /monic lead_coef_map -(inj_eq (@fmorph_inj _ _ f)) rmorph1.
Qed.

Lemma map_poly_com : forall p x, com_poly p^f (f x).
Proof. move=> p x; exact: map_com_poly (mulrC x _). Qed.

Lemma root_field_map_poly : forall p x, root p^f (f x) = root p x.
Proof. by move=> p x; rewrite rootE horner_map // fmorph_eq0. Qed.


Lemma fmorph_unity_root : forall n z, n.-unity_root (f z) = n.-unity_root z.
Proof.
move=> n z.
by rewrite !unity_rootE -(inj_eq (@fmorph_inj _ _ f)) rmorphX ?rmorph1.
Qed.

Lemma fmorph_primitive_root : forall n z,
  n.-primitive_root (f z) = n.-primitive_root z.
Proof.
move=> n z; congr (_ && _); apply: eq_forallb => i.
by rewrite fmorph_unity_root.
Qed.

End MapFieldPoly.

Section MaxRoots.

Variable R : unitRingType.
Implicit Type p : {poly R}.

Definition diff_roots (x y : R) := (x * y == y * x) && GRing.unit (y - x).

Fixpoint uniq_roots (rs : seq R) {struct rs} :=
  if rs is x :: rs' then all (diff_roots x) rs' && uniq_roots rs' else true.

Lemma uniq_roots_factors : forall p rs,
  all (root p) rs -> uniq_roots rs ->
  exists q, p = q * \prod_(z <- rs) ('X - z%:P).
Proof.
move=> p; elim=> [|z rs IHrs] /=.
  by rewrite big_nil; exists p; rewrite mulr1.
case/andP=> rpz rprs; case/andP=> drs urs; case:IHrs=> // q hq.
case: (factor_theorem q z _) => [|q' hq']; last first.
  by rewrite hq hq'; exists q'; rewrite big_cons mulrA.
move: drs rpz {rprs}; rewrite {p}hq.
elim: rs q urs=> [|t rs IHrs] q /=; first by rewrite big_nil mulr1.
case/andP=> diff_t_rs uniq_rs.
rewrite big_cons -andbA mulrA; case/and3P; move/eqP=> czt inv_zt diff_z_rs.
move/(IHrs _ uniq_rs diff_z_rs)=> {rs IHrs diff_z_rs uniq_rs diff_t_rs}.
rewrite !rootE horner_mul_com; last first.
  by rewrite /com_poly horner_factor mulr_subr mulr_subl czt.
rewrite horner_factor; move/eqP=> hq.
by rewrite -(inj_eq (mulIr inv_zt)) -oppr_sub mulrN hq oppr0 mul0r.
Qed.

Theorem max_ring_poly_roots : forall (p : {poly R}) rs,
  p != 0 -> all (root p) rs -> uniq_roots rs -> size rs < size p.
Proof.
move=> p rs nz_p p_rs_0 uniq_rs; rewrite -size_prod_factors.
case: (@uniq_roots_factors p rs)=> // q hq; rewrite hq in nz_p *.
have nq0: q != 0 by apply: contraNneq nz_p=> ->; rewrite mul0r.
rewrite size_mul_monic ?monic_prod_factors //.
by rewrite -[size q]prednK ?addSn /= ?leq_addl // lt0n size_poly_eq0.
Qed.

Lemma all_roots_factors : forall p rs,
  size p = (size rs).+1 -> all (root p) rs -> uniq_roots rs ->
  p = (lead_coef p) *: \prod_(z <- rs) ('X - z%:P).
Proof.
move=> p rs hprs rrs; case/(uniq_roots_factors rrs)=> q hp.
have np0: p != 0 by rewrite -size_poly_eq0 hprs.
have nq0: q != 0 by apply: contraNneq np0; rewrite hp=> ->; rewrite mul0r.
move: hprs; rewrite hp size_mul_monic ?monic_prod_factors //.
rewrite size_prod_factors addnS /= -add1n; move/addIn=> hsq.
rewrite lead_coef_mul_monic ?monic_prod_factors //.
by rewrite [q]size1_polyC ?hsq // lead_coefC mul_polyC.
Qed.

End MaxRoots.

Section FieldRoots.

Variable F : fieldType.
Implicit Type p : {poly F}.
Implicit Type rs : seq F.

Lemma uniq_rootsE : forall rs, uniq_roots rs = uniq rs.
Proof.
elim=> //= r rs ->; congr (_ && _); rewrite -has_pred1 -all_predC.
by apply: eq_all => t; rewrite /diff_roots mulrC eqxx unitfE subr_eq0.
Qed.

Theorem max_poly_roots : forall p rs,
  p != 0 -> all (root p) rs -> uniq rs -> size rs < size p.
Proof. by move=> p rs; rewrite -uniq_rootsE; exact: max_ring_poly_roots. Qed.

Variable n : nat.

Lemma max_unity_roots : forall rs,
  n > 0 -> all n.-unity_root rs -> uniq rs -> size rs <= n.
Proof.
move=> rs n_gt0 rs_n_1 Urs; have szPn := size_Xn_sub_1 F n_gt0.
by rewrite -ltnS -szPn max_poly_roots -?size_poly_eq0 ?szPn.
Qed.

Lemma mem_unity_roots : forall rs,
    n > 0 -> all n.-unity_root rs -> uniq rs -> size rs = n ->
  n.-unity_root =i rs.
Proof.
move=> rs n_gt0 rs_n_1 Urs sz_rs_n x; rewrite -topredE /=.
apply/idP/idP=> xn1; last exact: (allP rs_n_1).
apply: contraFT (ltnn n) => not_rs_x.
by rewrite -{1}sz_rs_n (@max_unity_roots (x :: rs)) //= ?xn1 ?not_rs_x.
Qed.

(* Showing the existence of a primitive root requires the theory in cyclic. *)

Variable z : F.
Hypothesis prim_z : n.-primitive_root z.

(* add monicP *)
(* rephrase size_mul_id *)
(* state more lemmas about X^n - x (for lead_coef & horner for ex & _eq0) *)


Lemma prod_factors_of_unity : \prod_(0 <= i < n) ('X - (z ^+ i)%:P) = 'X^n - 1.
Proof.
rewrite -(big_map _ xpredT (fun a => 'X - a%:P)); set us := (map _ _).
have n_gt0: n > 0 by  case: n prim_z.
rewrite (@all_roots_factors _ ('X^n - 1) us).
* by rewrite (monicP (monic_Xn_sub_1 _ _)) // scale1r.
* by rewrite size_Xn_sub_1 // size_map size_iota subn0.
* rewrite all_map; apply/allP=> i _ /=.
  rewrite rootE !horner_lin hornerXn -exprn_mulr.
  by rewrite -(prim_expr_mod prim_z) modn_mull subrr.
* rewrite uniq_rootsE map_inj_in_uniq ?iota_uniq // => i j.
  rewrite !mem_index_iota => ltin ltjn; move/eqP.
  by rewrite (eq_prim_root_expr prim_z) !modn_small //; move/eqP.
Qed.

Lemma prim_rootP : forall x, x ^+ n = 1 -> {i : 'I_n | x = z ^+ i}.
Proof.
move=> x xn1; pose zn := map (GRing.exp z) (index_iota 0 n).
case: (pickP (fun i : 'I_n => x == z ^+ i)) => [i | no_i].
  by move/eqP; exists i.
case: notF; suffices{no_i}: x \in zn.
  case/mapP=> i; rewrite mem_index_iota => lt_i_n def_x.
  by rewrite -(no_i (Ordinal lt_i_n)) -def_x.
rewrite -root_prod_factors big_map prod_factors_of_unity.
by rewrite rootE [_==_]unity_rootE xn1.
Qed.

End FieldRoots.

Section MapPolyRoots.

Variables (F : fieldType) (R : unitRingType) (f : {rmorphism F -> R}).

Lemma map_diff_roots : forall x y, diff_roots (f x) (f y) = (x != y).
Proof.
move=> x y; rewrite /diff_roots -rmorph_sub // fmorph_unit // subr_eq0 //.
by rewrite rmorph_comm // eqxx eq_sym.
Qed.

Lemma map_uniq_roots : forall s, uniq_roots (map f s) = uniq s.
Proof.
elim=> //= x s ->; congr (_ && _); elim: s => //= y s ->.
by rewrite map_diff_roots -negb_or.
Qed.

End MapPolyRoots.

Section PolyCompose.

Variable R: ringType.

Implicit Types p q : {poly R}.

(* Todo : might be renamed to comp_poly, allowing to use _poly as a suffix *)
Definition poly_comp q p := (map_poly polyC p).[q].

Local Notation "p \Po q" := (poly_comp q p) (at level 50).

Lemma poly_compE: forall p q, p \Po q = \sum_(i < size p) p`_i *: q^+i.
Proof.
move=> p q; rewrite /poly_comp /map_poly horner_poly.
by apply: eq_bigr=> i _; rewrite mul_polyC.
Qed.

Lemma poly_comp0 : forall p, p \Po 0 = (p`_0)%:P.
Proof.
move=> p; rewrite poly_compE.
case: size (size_poly_eq0 p)=> [|n _].
  by move/eqP; case: eqP=> // -> _; rewrite big_ord0 coef0.
rewrite big_ord_recl big1; first by rewrite addr0 expr0 scale_poly1.
by move=> i; rewrite exprS mul0r scaler0.
Qed.

Lemma poly_comCp : forall c p, c%:P \Po p = c%:P.
Proof.
move=> x p; rewrite poly_compE size_polyC.
case: eqP=> [->|_]; first by rewrite big_ord0.
by rewrite big_ord_recl coefC expr0 scale_poly1 big_ord0 addr0.
Qed.

Lemma poly_compC : forall p c, p \Po c%:P = p.[c]%:P.
Proof.
move=> p c; rewrite poly_compE horner_coef rmorph_sum; apply: congr_big=> //.
by move=> i _; rewrite rmorphM rmorphX mul_polyC.
Qed.

Lemma poly_comp_is_additive : forall p, additive (poly_comp p).
Proof.
by move=> p q r; rewrite /poly_comp rmorph_sub horner_add horner_opp.
Qed.

Canonical Structure poly_comp_additive p := Additive (poly_comp_is_additive p).

Lemma poly_comp_is_linear : forall p, linear (poly_comp p).
move=> p k u v.
by rewrite raddfD /= /poly_comp map_poly_scaler horner_scaler mul_polyC.
Qed.

Canonical Structure poly_comp_linear p := Linear (poly_comp_is_linear p).

Lemma poly_com0p : forall p, 0 \Po p = 0.
Proof. move=> p; exact: raddf0. Qed.

Lemma poly_comp_addl : forall p q r, (p + q) \Po r = (p \Po r) + (q \Po r).
Proof. move=> *; exact: raddfD. Qed.

Lemma poly_comp_subl : forall p q r, (p - q) \Po r = (p \Po r) - (q \Po r).
Proof. move=> *; exact: raddf_sub. Qed.

Lemma poly_comp_scall : forall c p q, (c *: p) \Po q = c *: (p \Po q).
Proof. move=> *; exact: linearZ. Qed.

Lemma poly_compX: forall p, p \Po 'X = p.
Proof. by move=> p; rewrite poly_compE - poly_def coefK. Qed.

Lemma poly_comXp: forall p, 'X \Po p = p.
Proof.
move=> p; rewrite poly_compE size_polyX 2!big_ord_recl big_ord0 !coefX /=.
by rewrite scale0r expr1 scale1r add0r addr0.
Qed.

Lemma poly_comp_translateK : forall z, ('X + z%:P) \Po ('X - z%:P) = 'X.
Proof.
by move => z; rewrite poly_comp_addl poly_comXp poly_comCp subrK.
Qed.

Lemma poly_comp_amulX: forall c p q, (p * 'X + c%:P) \Po q = (p \Po q) * q + c%:P.
Proof.
move=> c p q; case: (p =P 0)=> Hp.
  by rewrite Hp poly_com0p !(mul0r,add0r) poly_comCp.
rewrite poly_comp_addl poly_comCp; congr (_ + _).
rewrite /poly_comp /map_poly !horner_poly.
have->: size (p * 'X) = (size p).+1.
  by rewrite -[_ * _]addr0 size_amulX size_poly_eq0; case: eqP.
rewrite big_ord_recl coef_mulX mul0r add0r -mulr_suml.
by apply: eq_bigr=> i _; rewrite coef_mulX exprSr mulrA.
Qed.

Lemma size_poly_comp: forall p q,
  size (p \Po q) <= ((size p).-1 * (size q).-1).+1.
Proof.
move => p q.
rewrite poly_compE (leq_trans (size_sum _ _ _)) //.
apply/bigmax_leqP => i _.
rewrite -mul_polyC (leq_trans (size_mul _ _)) //.
apply: (@leq_trans (size (q ^+ i))).
  rewrite size_polyC.
  by case (_ != _); rewrite ?add1n // leq_pred.
rewrite (leq_trans (size_exp _ _)) // ltnS mulnC leq_mul //.
case: (size p) i => [[]|n]; first by case.
by apply: leq_ord.
Qed.

Lemma map_poly_comp : forall (aR bR cR : ringType)
(f : bR -> cR) (g : aR -> bR) (p : {poly aR}),
f 0 = 0 -> map_poly (f \o g) p = map_poly f (map_poly g p).
Proof.
move=> aR bR cR f g p f0; apply/polyP => i.
rewrite /map_poly !coef_poly.
set gp := \poly_(i0 < _) _.
case: (ltnP i (size gp))=> hi /=; first by rewrite (leq_trans hi) ?size_poly.
case: ifP=> // hpi; suff ->: g p`_i = 0 by [].
suff: (gp`_i = 0) by rewrite coef_poly hpi.
by move: hi; rewrite leqNgt; apply: contraNeq; apply: leq_coef_size.
Qed.

End PolyCompose.

Notation "p \Po q" := (poly_comp q p) (at level 50).

Section ComPolyCompose.

Variable R: comRingType.

Implicit Types p q r : {poly R}.

Lemma poly_comp_rmorphr : forall p, rmorphism (poly_comp p).
Proof.
move=> p; split=> [q r|]; first by exact: raddf_sub.
split=> [q r|]; last by rewrite poly_comCp.
by rewrite /poly_comp rmorphM horner_mul.
Qed.

Canonical Structure poly_comp_rmorphism p := RMorphism (poly_comp_rmorphr p).

Lemma poly_comp_mull : forall p q r, (p * q) \Po r = (p \Po r) * (q \Po r).
Proof.  move=> *; exact: rmorphM. Qed.

Lemma horner_poly_comp : forall p q x, (p \Po q).[x] = p.[q.[x]].
Proof.
move => p q x.
rewrite /poly_comp (horner_coef_wide _ (size_poly _ _))
        horner_sum [p.[_]]horner_coef.
by apply: eq_bigr => i _; rewrite coef_map ?(horner_lin) ?horner_exp.
Qed.

Lemma root_comp : forall p q (x : R), root (p \Po q) x = root p (q.[x]).
Proof. by move=> p q x; rewrite !rootE horner_poly_comp. Qed.

Lemma poly_compA : forall p q r, (p \Po q) \Po r = p \Po (q \Po r).
Proof.
move => p q r; move: p.
apply: poly_ind => [|p0 c IH]; first by rewrite !poly_comCp.
by rewrite !poly_comp_addl !poly_comp_mull !poly_comXp IH !poly_comCp.
Qed.

End ComPolyCompose.

Section IdomainPolyCompose.

Variable R : idomainType.
Implicit Types x y : R.
Implicit Types p q r : {poly R}.

Lemma size_poly_comp_id: forall p q,
  (size (p \Po q)).-1 = ((size p).-1 * (size q).-1)%N.
Proof.
move => p q.
case (eqVneq p 0) => [->|Hp0].
  by rewrite poly_com0p size_poly0.
case (eqVneq q 0) => [->|Hq0].
  apply/eqP.
  by rewrite poly_comp0 size_polyC size_poly0 muln0 -subn1 subn_eq0 leq_b1.
rewrite poly_compE.
have: (0 < size p) by rewrite lt0n size_poly_eq0.
move/prednK <-.
have Hszq : 0 < size (q ^+ (size p).-1) by rewrite lt0n size_poly_eq0 expf_neq0.
case (leqP (size q).-1 0) => [|Hszq0].
  rewrite leqn0.
  move/eqP => Hszq1.
  rewrite Hszq1 muln0.
  apply/eqP.
  rewrite -subn1 subn_eq0 (leq_trans (size_sum _ _ _)) //.
  apply/bigmax_leqP => i _.
  move/eqP: Hszq1.
  rewrite -subn1 subn_eq0.
  move/size1_polyC ->.
  by rewrite -polyC_exp -mul_polyC -polyC_mul size_polyC leq_b1.
(* Todo : understand and fix this slowdown *)
rewrite big_ord_recr /= addrC size_addl;
  (rewrite size_scaler; last by rewrite -lead_coefE lead_coef_eq0 Hp0).
  by move/prednK: Hszq <-; rewrite size_exp_id mulnC.
apply: (leq_ltn_trans (size_sum _ _ _)).
move/prednK: Hszq <-.
rewrite size_exp_id ltnS.
apply/bigmax_leqP => i _.
case (eqVneq p`_i 0) => [->|]; first by rewrite scale0r size_poly0.
move/size_scaler ->.
have/prednK: 0 < size (q ^+ i) by rewrite lt0n size_poly_eq0 expf_neq0.
move <-.
by rewrite size_exp_id ltn_mul2l Hszq0 ltn_ord.
Qed.

End IdomainPolyCompose.

Section Deriv.

Variable R : ringType.

Implicit Types p q : {poly R}.

Definition deriv p := \poly_(i < (size p).-1) (p`_i.+1 *+ i.+1).

Notation "a ^` ()" := (deriv a).

Lemma coef_deriv : forall p i, p^`()`_i = p`_i.+1 *+ i.+1.
Proof.
move=> [p Hp] i; rewrite coef_poly /=; case: leqP => //.
by case: {Hp}p => [|c p] /=; try move/(nth_default 0)->; rewrite mul0rn.
Qed.

Lemma derivC : forall c, c%:P^`() = 0.
Proof.
by move=> c; apply/polyP=> [[|i]]; rewrite coef_deriv !coefC /= mul0rn.
Qed.

Lemma derivX : ('X)^`() = 1.
Proof.
by apply/polyP=> [[|i]]; rewrite coef_deriv coef1 coefX ?mul0rn.
Qed.

Lemma derivXn : forall n, 'X^n^`() = 'X^n.-1 *+ n.
Proof.
move=> n; apply/polyP=> i; rewrite coef_deriv coef_natmul !coef_Xn.
case: n=> [|n] /=; first by  case: i => [|i]; rewrite mul0rn mulr0n.
by rewrite eqSS; case: eqP; [move=>->| rewrite !mul0rn].
Qed.

Lemma deriv_opp : {morph deriv : p / - p}.
Proof.
by move=> p; apply/polyP=> i; rewrite coef_deriv !coef_opp coef_deriv mulNrn.
Qed.

Lemma deriv_linear_proof : linear deriv.
Proof.
move=> k p q; apply/polyP=> i.
rewrite !(coef_deriv,coef_add,coef_scaler).
by rewrite mulrn_addl mulrnAr.
Qed.

Canonical Structure deriv_linear :=  Linear deriv_linear_proof.

Lemma deriv0 : 0^`() = 0.
Proof. exact: linear0. Qed.

Lemma derivD : {morph deriv : p q / p + q}.
Proof. exact: linearD. Qed.

Lemma deriv_sub : {morph deriv : p q / p - q}.
Proof. exact: linear_sub. Qed.

Lemma derivM : forall p q, (p * q)^`() = p^`() * q + p * q^`().
Proof.
move=> p q; apply/polyP=> i; rewrite !(coef_deriv, coef_add, coef_mul).
pose pq j a b :=  p`_j *+ a * (q`_(i.+1 - j) *+ b).
transitivity (\sum_(j < i.+2) (pq j j 1%N + pq j 1%N (i.+1 - j)%N)).
  rewrite -sumr_muln; apply: eq_bigr => j _.
  by rewrite /pq !mulr1n mulrnAl mulrnAr -mulrn_addr subnKC // leq_ord.
rewrite big_split /= {}/pq; congr (_ + _).
  rewrite big_ord_recl mulr0n mul0r add0r.
  by apply: eq_bigr => j _; rewrite coef_deriv.
rewrite big_ord_recr subnn mulr0n mulr0 /= addr0.
by apply: eq_bigr => j _; rewrite coef_deriv // leq_subS // leq_ord.
Qed.

Lemma derivMn : forall n p, (p *+ n)^`() = p^`() *+ n.
Proof. exact: linearMn. Qed.

Lemma derivMNn : forall n p, (p *- n)^`() = p^`() *- n.
Proof. exact: linearMNn. Qed.

Lemma deriv_mulC : forall c p, (c%:P * p)^`() = c%:P * p^`().
Proof. by move=> c p; rewrite derivM derivC mul0r add0r. Qed.

Lemma deriv_scale : forall c p, (c *: p)^`() = c *: p^`().
Proof. by move=> c p; rewrite -!mul_polyC deriv_mulC. Qed.

Lemma derivN : {morph deriv : p / - p}.
Proof. exact: linearN. Qed.

Lemma derivZ : scalable deriv.
Proof. exact: linearZ. Qed.

Lemma deriv_amulX : forall p c, (p * 'X + c%:P)^`() = p + p^`() * 'X.
Proof.
by move=> p c; rewrite derivD derivC addr0 derivM derivX mulr1 addrC.
Qed.

Lemma deriv_factor : forall (a : R),  ('X - a%:P)^`() = 1.
Proof. by move=> a; rewrite derivD deriv_opp derivX derivC subr0. Qed.

(* Note : reorder derivE, *)
(*    put factor factor before deriv_sub and derivM in the end *)
Definition derivE := (deriv_scale, deriv_mulC, derivC, derivX,
deriv_amulX, derivM, deriv_sub, derivD, derivMn, derivN, derivXn,
deriv_factor).

Definition derivn n p := iter n deriv p.

Notation "a ^` ( n )" := (derivn n a).

Lemma derivn0 : forall p, p^`(0) = p.
Proof. done. Qed.

Lemma derivn1 : forall p, p^`(1) = p^`().
Proof. done. Qed.

Lemma derivnS : forall p n, p^`(n.+1) = p^`(n)^`().
Proof. done. Qed.

Lemma derivSn : forall p n, p^`(n.+1) = p^`()^`(n).
Proof. by move=> p n; rewrite /derivn iterSr. Qed.

Lemma coef_derivn : forall n p i, p^`(n)`_i = p`_(n + i) *+ (n + i) ^_ n.
Proof.
elim=> [|n Hrec] p i; first by rewrite ffactn0 mulr1n.
by rewrite derivnS coef_deriv Hrec -mulrnA ffactnSr addSnnS addKn.
Qed.

Lemma derivnC : forall c n, c%:P^`(n) = if n == 0%N then c%:P else 0.
Proof.
by move=> c; elim=> [|[|n] Hrec] //; rewrite derivnS Hrec -?polyC0 derivC.
Qed.

Lemma derivn_linear_proof : forall n, linear (derivn n).
Proof.
move=> n k p q; apply/polyP=> i.
rewrite !(coef_derivn,coef_add,coef_scaler).
by rewrite mulrn_addl mulrnAr.
Qed.

Canonical Structure derivn_linear n :=  Linear (derivn_linear_proof n).

Lemma derivnD : forall n, {morph (derivn n) : p q / p + q}.
Proof. move=> n; exact: linearD. Qed.

Lemma derivn_sub : forall n, {morph (derivn n) : p q / p - q}.
Proof. move=> n; exact: linear_sub. Qed.

Lemma derivnMn : forall n m p, (p *+ m)^`(n) = p^`(n) *+ m.
Proof. move=> n; exact: linearMn. Qed.

Lemma derivnMNn : forall n m p, (p *- m)^`(n) = p^`(n) *- m.
Proof. move=> n; exact: linearMNn. Qed.

Lemma derivnN : forall n, {morph (derivn n) : p / - p}.
Proof. move=> n; exact: linearN. Qed.

Lemma derivnZ : forall n, scalable (derivn n).
Proof. move=> n; exact: linearZ. Qed.

Lemma derivnXn : forall m n, 'X^m^`(n) = 'X^(m - n) *+ m ^_ n.
Proof.
move=> m n; apply/polyP=>i; rewrite coef_derivn coef_natmul !coef_Xn.
case: (ltnP m n) => [lt_m_n | le_m_n].
  by rewrite eqn_leq leqNgt ltn_addr // mul0rn ffact_small.
by rewrite -{1 3}(subnKC le_m_n) eqn_addl; case: eqP => [->|]; rewrite ?mul0rn.
Qed.

Lemma derivn_amulX : forall n p c,
 (p * 'X + c%:P)^`(n.+1) = p^`(n) *+ n.+1  + p^`(n.+1) * 'X.
Proof.
elim=> [|n Hrec] p c; first by rewrite derivn0 !derivn1 deriv_amulX mulr1n.
rewrite derivnS Hrec derivD derivM derivX mulr1 derivMn -!derivnS.
by rewrite addrA addrAC (mulrS _ n.+1) (addrC p^`(n.+1)).
Qed.

Lemma derivn_poly0 : forall p n, size p <= n -> p^`(n) = 0.
Proof.
move=> p n Hpn; apply/polyP=>i; rewrite coef_derivn.
rewrite nth_default; first by rewrite mul0rn coef0.
by apply: leq_trans Hpn _; apply leq_addr.
Qed.

Lemma lt_size_deriv : forall (p : {poly R}), p != 0 ->
  (size p ^`() < (size p))%N.
Proof.
move=> p np0; apply: leq_ltn_trans (size_poly _ _) _.
case sp: (size p) => [|?] //; move/eqP: sp; rewrite size_poly_eq0 => sp.
by rewrite sp in np0.
Qed.

(* A normalising version of derivation to get the division by n! in Taylor *)

Definition nderivn n p := \poly_(i < size p - n) (p`_(n + i) *+  'C(n + i, n)).

Notation "a ^`N ( n )" := (nderivn n a).


Lemma coef_nderivn : forall n p i, p^`N(n)`_i = p`_(n + i) *+  'C(n + i, n).
Proof.
move=> n p i; rewrite coef_poly; case: leqP=> // Hp.
by rewrite nth_default ?mul0rn // -leq_sub_add.
Qed.

(* Here is the division by n! *)
Lemma nderivn_def : forall n p, p^`(n) = p^`N(n) *+ n`!.
Proof.
move=> m n; apply/polyP=> p; rewrite coef_natmul coef_nderivn coef_derivn.
by rewrite -mulrnA bin_ffact.
Qed.

Lemma nderivn0 : forall p, p^`N(0) = p.
Proof. by move=> p; apply/polyP=>i; rewrite coef_nderivn bin0 mulr1n. Qed.

Lemma nderivn1 : forall p, p^`N(1) = p^`().
Proof. by move=> p; rewrite -derivn1 nderivn_def mulr1n. Qed.

Lemma nderivnC : forall c n, c%:P^`N(n) = if n == 0%N then c%:P else 0.
Proof.
move=> c n; apply/polyP=>i.
rewrite coef_nderivn; case: n=> [|n]; first by rewrite bin0 mulr1n.
by rewrite coefC mul0rn coef0.
Qed.

Lemma nderivnXn : forall m n, 'X^m^`N(n) = 'X^(m - n) *+ 'C(m, n).
Proof.
move=> m n; apply/polyP=>i; rewrite coef_nderivn coef_natmul !coef_Xn.
case: (ltnP m n) => [lt_m_n | le_n_m].
  by rewrite eqn_leq leqNgt ltn_addr // mul0rn bin_small.
by rewrite -{1 3}(subnKC le_n_m) eqn_addl; case: eqP => [->|]; rewrite ?mul0rn.
Qed.

Lemma nderivn_linear_proof : forall n, linear (nderivn n).
Proof.
move=> n k p q; apply/polyP=> i.
rewrite !(coef_nderivn,coef_add,coef_scaler).
by rewrite mulrn_addl mulrnAr.
Qed.

Canonical Structure nderivn_linear n :=  Linear (nderivn_linear_proof n).

Lemma nderivnD : forall n, {morph (nderivn n) : p q / p + q}.
Proof. move=> n; exact: linearD. Qed.

Lemma nderivn_sub : forall n, {morph (nderivn n) : p q / p - q}.
Proof. move=> n; exact: linear_sub. Qed.

Lemma nderivnMn : forall n m p, (p *+ m)^`N(n) = p^`N(n) *+ m.
Proof. move=> n; exact: linearMn. Qed.

Lemma nderivnMNn : forall n m p, (p *- m)^`N(n) = p^`N(n) *- m.
Proof. move=> n; exact: linearMNn. Qed.

Lemma nderivnN : forall n, {morph (nderivn n) : p / - p}.
Proof. move=> n; exact: linearN. Qed.

Lemma nderivnZ : forall n, scalable (nderivn n).
Proof. move=> n; exact: linearZ. Qed.

Lemma nderivn_amulX : forall n p c,
  (p * 'X + c%:P)^`N(n.+1) = p^`N(n) + p^`N(n.+1) * 'X.
Proof.
move=> n p c; apply/polyP=> i; rewrite coef_nderivn !coef_add !coef_mulX coefC.
rewrite !addSn /= !coef_nderivn addr0 binS mulrn_addr addrC; congr (_ + _).
by rewrite addSnnS; case: i; rewrite // addn0 bin_small.
Qed.

Lemma nderivn_poly0 : forall p n, size p <= n -> p^`N(n) = 0.
Proof.
move=> p n Hpn; apply/polyP=> i; rewrite coef_nderivn.
rewrite nth_default; first by rewrite mul0rn coef0.
by apply: leq_trans Hpn _; apply leq_addr.
Qed.

Lemma nderiv_taylor : forall p x h,
  GRing.comm x h -> p.[x + h] = \sum_(i < size p) p^`N(i).[x] * h ^+ i.
Proof.
move=> p x h Cxh; move:p; apply:poly_ind=> [|p c Hrec].
  by rewrite size_poly0 big_ord0 horner0.
rewrite horner_amulX size_amulX; case: eqP => Hs.
  move/eqP: Hs; rewrite size_poly_eq0; move/eqP->; rewrite hornerC !simp.
  case: eqP => [-> | _]; rewrite ?size_poly0 ?big_ord_recl big_ord0 //.
  by rewrite nderivn0 hornerC !simp.
case: (size p)(@nderivn_poly0 p) Hs Hrec => [|n] // Hd _ Hrec.
rewrite big_ord_recl nderivn0 !simp horner_amulX.
set S := \sum_i _; rewrite -addrA [c + S]addrC addrA; congr (_ + _).
rewrite Hrec mulr_addr !big_distrl /= big_ord_recl nderivn0 !simp -!addrA.
congr (_ + _); have ->: S
  = \sum_(i < n.+1) (p^`N(i).[x] * h ^+ i.+1 + p^`N(i.+1).[x] * x * h ^+ i.+1).
- apply eq_big => // i _.
  by rewrite nderivn_amulX horner_add horner_mulX mulr_addl.
rewrite big_split /= addrC.
congr (_ + _); first by apply eq_big => // i _; rewrite exprSr mulrA.
rewrite big_ord_recr /= Hd // horner0 !simp.
by apply eq_big => // i _; rewrite -!mulrA commr_exp.
Qed.

Lemma nderiv_taylor_wide : forall n p x h,
    GRing.comm x h -> size p <= n ->
  p.[x + h] = \sum_(i < n) p^`N(i).[x] * h ^+ i.
Proof.
move=> n p x h Cxh; elim: n => [|n Hrec] Hs.
  suff ->: p = 0 by rewrite horner0 big_ord0.
  by apply/eqP; rewrite -size_poly_eq0; case: size Hs.
move: Hs; rewrite leq_eqVlt; case/orP=> Hc.
  by move/eqP: Hc =><-; apply nderiv_taylor.
by rewrite big_ord_recr -Hrec // nderivn_poly0 // horner0 !simp.
Qed.

End Deriv.

Notation "a ^` ()" := (deriv a) : ring_scope.
Notation "a ^` ( n )" := (derivn n a) : ring_scope.
Notation "a ^`N ( n )" := (nderivn n a) : ring_scope.

Section DerivComRing.

Variable R : comRingType.

Implicit Types p q : {poly R}.

Lemma deriv_poly_comp: forall p q, (p \Po q) ^`() = (p ^`() \Po q) * q^`().
Proof.
move=> p q; move: p.
apply: poly_ind=> [|p c IH]; first by rewrite !(deriv0,poly_com0p) mul0r.
by rewrite  poly_comp_amulX derivD derivC addr0 derivM IH deriv_amulX
            poly_comp_addl  -[_ * 'X]addr0 poly_comp_amulX addr0 mulr_addl
           addrC mulrAC.
Qed.

Lemma deriv_exp : forall p n, (p ^+ n)^`() = p^`() * (p ^+ (n.-1)) *+ n.
Proof.
move=> p []; first by rewrite expr0 mulr0n derivC.
elim=> [|n ihn /=]; first by rewrite expr1 expr0 mulr1 mulr1n.
by rewrite exprS derivM ihn !mulrnAr mulrCA -exprS -mulrS.
Qed.

Definition derivCE := (derivE, deriv_exp).

End DerivComRing.

Lemma deriv_map : forall (R S : ringType) (f : {rmorphism R -> S}) p,
  (map_poly f p)^`() = map_poly f (p^`()).
Proof.
move=> R S f p; apply/polyP => i.
by rewrite !(coef_map, coef_deriv) //= rmorphMn.
Qed.

Lemma derivn_map : forall (R S : ringType) (f : {rmorphism R -> S}) (n : nat) p,
  (map_poly f p)^`(n) = map_poly f (p^`(n)).
Proof.
move=> R S f n p; apply/polyP => i.
by rewrite !(coef_map, coef_derivn) //= rmorphMn.
Qed.

Lemma nderivn_map : forall (R S : ringType) (f : {rmorphism R -> S}) (n : nat) p,
  (map_poly f p)^`N(n) = map_poly f (p^`N(n)).
Proof.
move=> R S f n p; apply/polyP => i.
by rewrite !(coef_map, coef_nderivn) //= rmorphMn.
Qed.

Module UnityRootTheory.

Notation "n .-unity_root" := (root_of_unity n) : unity_root_scope.
Notation "n .-primitive_root" := (primitive_root_of_unity n) : unity_root_scope.
Open Scope unity_root_scope.

Definition unity_rootE := unity_rootE.
Definition unity_rootP := @unity_rootP.
Implicit Arguments unity_rootP [R n z].

Definition prim_order_exists := prim_order_exists.
Notation prim_order_gt0 :=  prim_order_gt0.
Notation prim_expr_order := prim_expr_order.
Definition prim_expr_mod := prim_expr_mod.
Definition prim_order_dvd := prim_order_dvd.
Definition eq_prim_root_expr := eq_prim_root_expr.

Definition rmorph_unity_root := rmorph_unity_root.
Definition fmorph_unity_root := fmorph_unity_root.
Definition fmorph_primitive_root := fmorph_primitive_root.
Definition max_unity_roots := max_unity_roots.
Definition mem_unity_roots := mem_unity_roots.
Definition prim_rootP := prim_rootP.

End UnityRootTheory.

