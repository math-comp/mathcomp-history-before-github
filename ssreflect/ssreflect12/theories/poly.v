(* (c) Copyright Microsoft Corporation and Inria. You may distribute   *)
(* under the terms of either the CeCILL-B License or the CeCILL        *)
(* version 2 License, as specified in the README file.                 *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import bigops ssralg.

(***************************************************************************)
(* This file provides a library for univariate polynomials over ring       *)
(* structures and proposes a theory for these objects when coefficients    *)
(* range over commutative rings and integral domains.                      *)
(*                                                                         *)
(*    polynomial R       == the type of polynomials over the ring R,       *)
(*                          represented as lists with a non zero last      *)
(*                          element (big endian representation)            *)
(*      + objects in this type should be casted by the {poly R} annotation *)
(*    c %:P              == the constant polynomial c, 'X and 'X^n the     *)
(*                          monomials.                                     *)
(*    \poly_ ( i < n ) E == the polynomial of degree strictly less than n, *)
(*                          whose coefficients are given by the general    *)
(*                          term E                                         *)
(*    p.[x]              == The evaluation of a polynomial p at a point x  *)
(*                          following the Horner schema                    *)
(*      + The multi-rule horner_lin (resp. horner_lin_com) unwinds horner  *)
(*        evaluation of a polynomial expression (resp. in a non            *)
(*        commutative case, under the appropriate assumptions)             *)
(*                                                                         *)
(* Degree is not defined as such, we rather use the size operation on      *)
(* sequences. Hence the zero polynomial is the only polynomial of size 0.  *)
(*                                                                         *)
(*    We define pseudo division on polynomials over an integral domain :   *)
(*        m %/ d == the pseudo-quotient                                    *)
(*        m %% d == the pseudo remainder                                   *)
(*        p %| q <=> q is a pseudo-divisor of p                            *)
(*                                                                         *)
(*    p %= q             == the equality modulo constant factors           *)
(*                       := (p %| q) && (q %| p)                           *)
(*       + In the case R is a field p and q are associate                  *)
(*                                                                         *)
(*       gcdp p q  == pseudo-gcd, for poly with coefficients in a ring,    *)
(*          idomain is only require of indempotence and commutativity      *)
(*                                                                         *)
(*       roots p   == roots of poly with coefficients in an idomain.       *)
(* We prove the factor_theorem, and the max_poly_roots inequality relating *)
(* the number of distinct roots of a polynomial and its size               *)
(***************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Open Local Scope ring_scope.

Reserved Notation "{ 'poly' T }" (at level 0, format "{ 'poly'  T }").
Reserved Notation "c %:P" (at level 2, format "c %:P").
Reserved Notation "'X" (at level 0).
Reserved Notation "''X^' n" (at level 3, n at level 2, format "''X^' n").
Reserved Notation "\poly_ ( i < n ) E"
  (at level 36, E at level 36, i, n at level 50,
   format "\poly_ ( i  <  n )  E").

Notation Local simp := Monoid.simpm.

Section Polynomial.

Variable R : ringType.

(* Defines a polynomial as a sequence with <> 0 last element *)
Record polynomial : Type :=
  Polynomial {polyseq :> seq R; _ : last 1 polyseq != 0}.

Definition poly_of of phant R := polynomial.
Identity Coercion type_poly_of : poly_of >-> polynomial.
Notation "{ 'poly' T }" := (poly_of (Phant T)).

Implicit Types p q : {poly R}.

Bind Scope ring_scope with poly_of.

Canonical Structure polynomial_subType :=
  Eval hnf in [subType for polyseq by polynomial_rect].
Definition polynomial_eqMixin := Eval hnf in [eqMixin of polynomial by <:].
Canonical Structure polynomial_eqType := Eval hnf in EqType polynomial_eqMixin.
Definition polynomial_choiceMixin := [choiceMixin of polynomial by <:].
Canonical Structure polynomial_choiceType :=
  Eval hnf in ChoiceType polynomial_choiceMixin.
Canonical Structure poly_subType := Eval hnf in [subType of {poly R}].
Canonical Structure poly_eqType := Eval hnf in [eqType of {poly R}].
Canonical Structure poly_choiceType := Eval hnf in [choiceType of {poly R}].

Lemma poly_inj : injective polyseq. Proof. exact: val_inj. Qed.

Definition lead_coef p := p`_(size p).-1.
Lemma lead_coefE : forall p, lead_coef p = p`_(size p).-1. Proof. by []. Qed.

Definition polyC c : {poly R} :=
  insubd (@Polynomial [::] (nonzero1r _)) [:: c].

Notation "c %:P" := (polyC c).

(* Remember the boolean (c !=0) is coerced to 1 if true and 0 if false *)
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
  if p is Polynomial ((_ :: _) as s) ns then @Polynomial (c :: s) ns else c%:P.

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
Notation "\poly_ ( i < n ) E" := (Poly (mkseq (fun i : nat => E) n)).

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

Definition poly_zmodMixin :=
  ZmodMixin add_polyA add_polyC add_poly0 add_poly_opp.
Canonical Structure poly_zmodType := Eval hnf in ZmodType poly_zmodMixin.
Canonical Structure polynomial_zmodType :=
  Eval hnf in [zmodType of polynomial for poly_zmodType].

(* Properties of the zero polynomial *)

Lemma polyC0 : 0%:P = 0 :> {poly R}. Proof. by []. Qed.

Lemma seq_poly0 : (0 : {poly R}) = [::] :> seq R.
Proof. by rewrite polyseqC eqxx. Qed.

Lemma size_poly0 : size (0 : {poly R}) = 0%N.
Proof. by rewrite seq_poly0. Qed.

Lemma coef0 : forall i, (0 : {poly R})`_i = 0.
Proof. by move=> i; rewrite coefC if_same. Qed.

Lemma lead_coef0 : lead_coef 0 = 0. Proof. exact: lead_coefC. Qed.

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

Lemma polyC_eq0 : forall c, (c%:P == 0) = (c == 0).
Proof. by move=> c; rewrite -size_poly_eq0 size_polyC; case: (c == 0). Qed.

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
Proof. exact: coef_add_poly. Qed.

Lemma coef_opp : forall p i, (- p)`_i = - p`_i.
Proof. exact: coef_opp_poly. Qed.

Lemma coef_sub : forall p1 p2 i, (p1 - p2)`_i = p1`_i - p2`_i.
Proof. by move=> p1 p2 i; rewrite coef_add coef_opp. Qed.

Lemma coef_natmul : forall p n i, (p *+ n)`_i = p`_i *+ n.
Proof.
by move=> p n i; elim: n => [|n IHn]; rewrite ?coef0 // !mulrS coef_add IHn.
Qed.

Lemma coef_negmul : forall p n i, (p *- n)`_i = p`_i *- n.
Proof. by move=> p n i; rewrite coef_natmul coef_opp. Qed.

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
apply: (big_rel K) => //= [|p1 n1 p2 n2 IH1 IH2]; first by rewrite size_poly0.
apply: leq_trans (size_add p1 p2) _.
by rewrite -eqn_maxl maxnAC !maxnA -maxnA (maxnl IH1) (maxnr IH2).
Qed.

Lemma lead_coef_addl : forall p q,
  size p > size q -> lead_coef (p + q) = lead_coef p.
Proof.
move=> p q ltqp; rewrite /lead_coef coef_add size_addl //.
by rewrite addrC nth_default ?simp // -ltnS (ltn_predK ltqp).
Qed.

(* And now the Ring structure. *)

Definition mul_poly p1 p2 :=
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
move=> p1 p2 i; rewrite coef_mul_poly (reindex ord_opp) /=.
  by apply: eq_bigr => j _; rewrite (sub_ordK j).
exists (@ord_opp _ : 'I_(i.+1) -> _) => j _; exact: ord_oppK.
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

Lemma nonzero_poly1 : 1%:P != 0. Proof. by rewrite polyC_eq0 nonzero1r. Qed.

Definition poly_ringMixin :=
  RingMixin mul_polyA mul_1poly mul_poly1 mul_poly_addl mul_poly_addr
            nonzero_poly1.
Canonical Structure poly_ringType := Eval hnf in RingType poly_ringMixin.
Canonical Structure polynomial_ringType :=
   Eval hnf in [ringType of polynomial for poly_ringType].

Lemma polyC1 : 1%:P = 1. Proof. by []. Qed.

Lemma polyseq1 : (1 : {poly R}) = [:: 1] :> seq R.
Proof. by rewrite polyseqC nonzero1r. Qed.

Lemma size_poly1 : size (1 : {poly R}) = 1%N.
Proof. by rewrite polyseq1. Qed.

Lemma coef1 : forall i, (1 : {poly R})`_i = (i == 0%N)%:R.
Proof. by case=> [|i]; rewrite polyseq1 /= ?nth_nil. Qed. 

Lemma lead_coef1 : lead_coef 1 = 1. Proof. exact: lead_coefC. Qed.

Lemma coef_mul : forall p1 p2 i,
  (p1 * p2)`_i = \sum_(j < i.+1) p1`_j * p2`_(i - j)%N.
Proof. exact: coef_mul_poly. Qed.

Lemma coef_mul_rev : forall p1 p2 i,
  (p1 * p2)`_i = \sum_(j < i.+1) p1`_(i - j)%N * p2`_j.
Proof. exact: coef_mul_poly_rev. Qed.

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

Lemma size_exp : forall p n, size (p ^+ n) <= ((size p).-1 * n).+1.
Proof.
move=> p n; case: (poly0Vpos p) => [-> | nzp].
  by case: n => [|n]; rewrite ?exprS ?mul0r size_poly0 ?size_poly1.
elim: n => [|n IHn]; first by rewrite size_poly1.
rewrite exprS (leq_trans (size_mul _ _)) //.
by rewrite -{1}(prednK nzp) mulnS -addnS leq_add2l.
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

(* Indeterminate, at last! *)

Definition polyX := Poly [:: 0; 1].

Notation "'X" := polyX.

Lemma polyseqX : 'X = [:: 0; 1] :> seq R.
Proof. by rewrite !polyseq_cons size_poly0 polyseq1. Qed.

Lemma size_polyX : size 'X = 2. Proof. by rewrite polyseqX. Qed.

Lemma coefX : forall i, 'X`_i = (i == 1%N)%:R.
Proof. by move=> [|[|i]]; rewrite polyseqX //= nth_nil. Qed.

Lemma lead_coefX : lead_coef 'X = 1.
Proof. by rewrite /lead_coef polyseqX. Qed.

Lemma comm_polyX : forall p, GRing.comm p 'X.
Proof.
move=> p; apply/polyP=> i; rewrite coef_mul_rev coef_mul.
by apply: eq_bigr => j _; rewrite coefX commr_nat.
Qed.

Lemma coef_mulX : forall p i, (p * 'X)`_i = (if i is i'.+1 then p`_i' else 0).
Proof.
move=> p i; rewrite coef_mul_rev big_ord_recl coefX ?simp.
case: i => [|i]; rewrite ?big_ord0 //= big_ord_recl polyseqX subn1 /=.
by rewrite big1 ?simp // => j _; rewrite nth_nil !simp.
Qed.

Lemma coef_Xmul : forall p i, ('X * p)`_i = (if i is i'.+1 then p`_i' else 0).
Proof. by move=> p i; rewrite -comm_polyX coef_mulX. Qed.

Lemma poly_cons_def : forall p a, poly_cons a p = p * 'X + a%:P.
Proof.
move=> p a; apply/polyP=> i; rewrite coef_cons coef_add coef_mulX coefC.
by case: i => [|i]; rewrite !simp.
Qed.

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

Notation "''X^' n" := ('X ^+ n).

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

Lemma comm_polyXn : forall p n, GRing.comm p 'X^n.
Proof. by move=> p n; apply: commr_exp; exact: comm_polyX. Qed.

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
Proof. by move=> n p i; rewrite comm_polyXn coef_Xn_mul. Qed.

(* Expansion of a polynomial as an indexed sum *)
Lemma poly_def : forall n E, \poly_(i < n) E i = \sum_(i < n) (E i)%:P * 'X^i.
Proof.
elim=> [|n IHn] E; first by rewrite big_ord0.
rewrite big_ord_recl /= poly_cons_def addrC simp; congr (_ + _).
rewrite (iota_addl 1 0) -map_comp IHn big_distrl /bump /=.
by apply: eq_bigr => i _; rewrite -mulrA exprSr.  
Qed.

(* Monic predicate *)

Definition monic p := lead_coef p == 1.

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

(* Pseudo division, defined on an arbitrary ring *)
Definition edivp_rec (q : {poly R})  :=
  let sq := size q in
  let cq := lead_coef q in
  fix loop (n : nat) (c : R) (qq r : {poly R}) {struct n} :=
    if size r < sq then (c, qq, r) else
    let m := (lead_coef r)%:P * 'X^(size r - sq) in
    let c1 := cq * c in
    let qq1 := qq * cq%:P + m in
    let r1 := r * cq%:P - m * q in
    if n is n1.+1 then loop n1 c1 qq1 r1 else (c1, qq1, r1).

Lemma edivp_mon_spec : forall p q n c qq r,
   monic q -> let d := edivp_rec q n c qq r in
 p = qq * q + r -> p = (d.1).2 * q + d.2.
Proof.
move=> p q n c qq r; move/eqP=> lq1.
elim: n => [|n IHn] /= in c qq r *; case: ltnP => Hp //= def_p.
  by rewrite lq1 !simp /= mulr_addl addrAC addrK.
by apply: IHn; rewrite lq1 !simp /= mulr_addl addrAC addrK.
Qed.

Lemma edivp_mod_spec : forall q n c (qq r : {poly R}),
  q != 0 -> size r <= n -> size (edivp_rec q n c qq r).2 < size q.
Proof.
move=> q; elim=> [|n IHn] c qq r Hq Hqq /=; case: (ltnP (size r)) => [// | Hl].
  by rewrite leqn0 in Hqq; rewrite (eqP Hqq) polySpred in Hl.
apply: IHn => //; apply: leq_size_coef => j Hj.
rewrite coef_add coef_opp -!mulrA coef_mulC coef_Cmul coef_Xn_mul.
move: Hj; rewrite leq_eqVlt; case/predU1P => [<-{j} | Hj]; last first.
  rewrite nth_default ?(leq_trans Hqq) // ?simp.
  rewrite nth_default; first by rewrite if_same !simp oppr0.
  by rewrite -{1}(subKn Hl) leq_sub2r // (leq_trans Hqq).
move: Hqq; rewrite leq_eqVlt ltnS; case/predU1P=> Hqq; last first.
  rewrite !nth_default ?if_same ?simp ?oppr0 //.
  by rewrite -{1}(subKn Hl) leq_sub2r // (leq_trans Hqq).
rewrite {2}/lead_coef Hqq polySpred // subSS ltnNge leq_subr /=.
by rewrite subKn ?addrN // -subn1 leq_sub_add add1n -Hqq.
Qed.

Lemma edivp_scal_spec: forall q n c (qq r : {poly R}),
  exists m, (edivp_rec q n c qq r).1.1 = lead_coef q ^+ m * c.
Proof.
move=> q; elim=> [|n IHn] c qq r /=.
  case: ifP; first by exists 0%N; rewrite mul1r.
  by exists 1%N; rewrite expr1.
case: ifP => _; first by exists 0%N; rewrite mul1r.
set c1 := _ * c; set qq1 := _ + _; set r1 := _ - _.
by have [m ->]:= IHn c1 qq1 r1; exists m.+1; rewrite exprSr -mulrA.
Qed.

Definition edivp (p q : {poly R}) : R * {poly R} * {poly R} :=
  if q == 0 then (1, 0, p) else edivp_rec q (size p) 1 0 p.

Definition divp p q := ((edivp p q).1).2.
Definition modp p q := (edivp p q).2.
Definition scalp p q := ((edivp p q).1).1.
Definition dvdp p q := modp q p == 0.

Notation "m %/ d" := (divp m d) (at level 40, no associativity).
Notation "m %% d" := (modp m d) (at level 40, no associativity).
Notation "p %| q" := (dvdp p q) (at level 70, no associativity).

Lemma divp_size : forall p q, size p < size q -> p %/ q = 0.
Proof.
move=> p q; rewrite /divp /edivp; case: eqP => Eq.
  by rewrite Eq size_poly0.
by case E1: (size p) => [| s] Hs /=; rewrite E1 Hs.
Qed.

Lemma modp_size : forall p q, size p < size q -> p %% q = p.
Proof.
move=> p q; rewrite /modp /edivp; case: eqP => Eq.
  by rewrite Eq size_poly0.
by case E1: (size p) => [| s] Hs /=; rewrite E1 Hs /=.
Qed.

Lemma divp_mon_spec : forall p q, monic q -> p = p %/ q * q + p %% q.
Proof.
move=> p q Mq.
rewrite /divp /modp /scalp /edivp.
case: eqP => [->| Hq]; first by rewrite !simp.
by apply: edivp_mon_spec; rewrite // !simp.
Qed.

Lemma modp_spec : forall p q, q != 0 -> size (p %% q) < size q.
Proof.
move=> p q Hq.
rewrite /divp /modp /scalp /edivp.
case: eqP => He; first by case/negP: Hq; apply/eqP.
by apply: edivp_mod_spec.
Qed.

Lemma scalp_spec : forall p q, exists m, scalp p q = lead_coef q ^+ m.
Proof.
move=> p q; rewrite /divp /modp /scalp /edivp.
case: eqP => He; first by exists 0%N.
by have [m ->]:= (edivp_scal_spec q (size p) 1 0 p); rewrite mulr1; exists m.
Qed.

Lemma div0p : forall p, 0 %/ p = 0.
Proof.
move=> p; rewrite /divp /edivp; case: ifP => // Hp.
by rewrite /edivp_rec !size_poly0 polySpred ?Hp.
Qed.

Lemma modp0 : forall p, p %% 0 = p.
Proof. by rewrite /modp /edivp eqxx. Qed.

Lemma mod0p : forall p, 0 %% p = 0.
Proof.
move=> p; rewrite /modp /edivp; case: ifP => // Hp.
by rewrite /edivp_rec !size_poly0 polySpred ?Hp.
Qed.

Lemma dvdpPm : forall p q, monic q -> reflect (exists qq, p = qq * q) (q %| p).
Proof.
move=> p q Mq; apply: (iffP idP).
  rewrite /dvdp; move/eqP=> Dqp.
  by exists (p %/ q); rewrite {1}(divp_mon_spec p Mq) Dqp !simp.
case=> qq Dqq; rewrite /dvdp.
pose d := qq - p %/ q.
have Epq: p %% q = d * q.
    rewrite mulr_addl mulNr -Dqq {2}(divp_mon_spec p Mq).
    by rewrite -addrA addrC -addrA addNr !simp.
have:= modp_spec p (monic_neq0 Mq); rewrite Epq.
case: (eqVneq d 0) => [->|nz_p]; first by rewrite simp.
by rewrite size_mul_monic // polySpred // ltnNge leq_addl.
Qed.

Lemma dvdp0: forall p, p %| 0.
Proof. move=> p; apply/eqP; exact: mod0p. Qed.

Lemma modpC: forall p c, c != 0 -> p %% c%:P = 0.
Proof.
move=> p c Hc; apply/eqP; rewrite -size_poly_eq0 -leqn0 -ltnS.
by apply: leq_trans (modp_spec _ _) _; rewrite ?polyC_eq0 // size_polyC Hc.
Qed.

Lemma modp1: forall p, p %% 1 = 0.
Proof. move=> p; apply: modpC; exact: nonzero1r. Qed.

Lemma divp1: forall p, p %/ 1 = p.
Proof. by move=> p; rewrite {2}(divp_mon_spec p monic1) modp1 !simp. Qed. 

Lemma dvd1p: forall p, 1 %| p.
Proof. move=> p; apply/eqP; exact: modp1. Qed.

Lemma modp_mon_mull : forall p q, monic q -> p * q %% q = 0.
Proof.
move=> p q Mq; have:= modp_spec (p * q) (monic_neq0 Mq).
pose qq := p - (p * q) %/ q.
have ->: (p * q) %% q = qq * q.
  by rewrite mulr_addl {2}(divp_mon_spec (p * q) Mq) mulNr addrC addKr.
case: (eqVneq qq 0) => [->|nz_qq]; first by rewrite simp.
by rewrite size_mul_monic // polySpred // ltnNge leq_addl.
Qed.

Lemma divp_mon_mull : forall p q, monic q -> p * q %/ q = p.
Proof.
move=> p q Mq.
pose qq := p - (p * q) %/ q.
case: (eqVneq qq 0) => [|nz_qq]; first by move/(canRL (subrK _)); rewrite simp.
have:= modp_spec (p * q) (monic_neq0 Mq).
have ->: (p * q) %% q = qq * q.
  by rewrite mulr_addl {2}(divp_mon_spec (p * q) Mq) mulNr addrC addKr.
by rewrite size_mul_monic // polySpred // ltnNge leq_addl.
Qed.

Lemma dvdp_mon_mull : forall p q, monic q -> q %| p * q.
Proof. move=> p q Mq; apply/eqP; exact: modp_mon_mull. Qed.

(* Pseudo gcd *)
Definition gcdp p q :=
  let: (p1, q1) := if size p < size q then (q, p) else (p, q) in
  if p1 == 0 then q1 else
  let fix loop (n : nat) (pp qq : {poly R}) {struct n} :=
      let rr := pp %% qq in
      if rr == 0 then qq else 
      if n is n1.+1 then loop n1 qq rr else rr in
  loop (size p1) p1 q1.

Lemma gcd0p : left_id 0 gcdp.
Proof.
move=> p; rewrite /gcdp size_poly0 lt0n size_poly_eq0 if_neg.
case: ifP => /= [_ | nzp]; first by rewrite eqxx.
by rewrite polySpred !(modp0, nzp) //; case: _.-1 => [|m]; rewrite mod0p eqxx.
Qed.

Lemma gcdp0 : right_id 0 gcdp.
Proof.
move=> p; have:= gcd0p p; rewrite /gcdp size_poly0 lt0n size_poly_eq0 if_neg.
by case: ifP => /= p0; rewrite ?(eqxx, p0) // (eqP p0).
Qed.

Lemma gcdpE : forall p q, 
  gcdp p q = if size p < size q then gcdp (q %% p) p else gcdp (p %% q) q.
Proof.
pose gcdp_rec := fix gcdp_rec (n : nat) (pp qq : {poly R}) {struct n} := 
   let rr := pp %% qq in
   if rr == 0 then qq else 
   if n is n1.+1 then gcdp_rec n1 qq rr else rr.
have Irec: forall m n p q, size q <= m -> size q <= n 
      -> size q < size p -> gcdp_rec m p q = gcdp_rec n p q.
+ elim=> [|m Hrec] [|n] //= p q.
  - rewrite leqn0 size_poly_eq0; move/eqP=> -> _.
    rewrite size_poly0 lt0n size_poly_eq0 modp0 => nzp.
    by rewrite (negPf nzp); case: n => [|n] /=; rewrite mod0p eqxx.
  - rewrite leqn0 size_poly_eq0 => _; move/eqP=> ->.
    rewrite size_poly0 lt0n size_poly_eq0 modp0 => nzp.
    by rewrite (negPf nzp); case: m {Hrec} => [|m] /=; rewrite mod0p eqxx.
  case: ifP => Epq Sm Sn Sq; rewrite Epq //.
  case: (eqVneq q 0) => [->|nzq].
    by case: n m {Sm Sn Hrec} => [|m] [|n] //=; rewrite mod0p eqxx.
  apply: Hrec; last exact: modp_spec.
    by rewrite -ltnS (leq_trans _ Sm) // modp_spec.
  by rewrite -ltnS (leq_trans _ Sn) // modp_spec.
move=> p q; case: (eqVneq p 0) => [-> | nzp].
  by rewrite mod0p modp0 gcd0p gcdp0 if_same.
case: (eqVneq q 0) => [-> | nzq].
  by rewrite mod0p modp0 gcd0p gcdp0 if_same.
rewrite /gcdp -/gcdp_rec.
case: ltnP; rewrite (negPf nzp, negPf nzq) //=.
  move=> ltpq; rewrite modp_spec (negPf nzp) //=.
  rewrite -(ltn_predK ltpq) /=; case: eqP => [->|].
    by case: (size p) => [|[|s]]; rewrite /= modp0 (negPf nzp) // mod0p eqxx.
  move/eqP=> nzqp; apply: Irec => //; last exact: modp_spec.
    by rewrite -ltnS (ltn_predK ltpq) (leq_trans _ ltpq) ?leqW // modp_spec.
  by rewrite ltnW // modp_spec.
move=> leqp; rewrite modp_spec (negPf nzq) //=.
have p_gt0: size p > 0 by rewrite lt0n size_poly_eq0.
rewrite -(prednK p_gt0) /=; case: eqP => [->|].
  by case: (size q) => [|[|s]]; rewrite /= modp0 (negPf nzq) // mod0p eqxx.
move/eqP=> nzpq; apply: Irec => //; last exact: modp_spec.
  by rewrite -ltnS (prednK p_gt0) (leq_trans _ leqp) // modp_spec.
by rewrite ltnW // modp_spec.
Qed.

End Polynomial.

Bind Scope ring_scope with polynomial.
Notation "{ 'poly' T }" := (poly_of (Phant T)) : type_scope.
Notation "\poly_ ( i < n ) E" := (Poly (mkseq (fun i => E) n)) : ring_scope.
Notation "c %:P" := (polyC c) : ring_scope.
Notation "'X" := (polyX _) : ring_scope.
Notation "''X^' n" := ('X ^+ n) : ring_scope.
Notation "m %/ d" := (divp m d) (at level 40, no associativity) : ring_scope.
Notation "m %% d" := (modp m d) (at level 40, no associativity) : ring_scope.
Notation "p %| q" := (dvdp p q) (at level 70, no associativity) : ring_scope.

(* Horner evaluation of polynomials *)

Section EvalPolynomial.

Variable R : ringType.
Implicit Types p q : {poly R}.
Implicit Types x a c : R.

Fixpoint horner s x {struct s} :=
  if s is a :: s' then horner s' x * x + a else 0.

Notation "p .[ x ]" := (horner (polyseq p) x) : ring_scope.

Lemma horner0 : forall x, (0 : {poly R}).[x] = 0.
Proof. by rewrite seq_poly0. Qed.

Lemma hornerC : forall c x, (c%:P).[x] = c.
Proof. by move=> c x; rewrite polyseqC; case: eqP; rewrite //= !simp. Qed.

Lemma hornerX : forall x, 'X.[x] = x.
Proof. by move=> x; rewrite polyseqX /= !simp. Qed.

Lemma horner_cons : forall p c x, (poly_cons c p).[x] = p.[x] * x + c.
Proof.
move=> p c x; rewrite polyseq_cons.
case/polyseq: p; rewrite //= !simp; exact: hornerC.
Qed.

Lemma horner_Poly : forall s x, (Poly s).[x] = horner s x.
Proof.
by move=> s x; elim: s => [|a s /= <-] /=; rewrite (horner0, horner_cons).
Qed.

Lemma horner_coef : forall p x,
  p.[x] = \sum_(i < size p) p`_i * x ^+ i.
Proof.
move=> p x; elim: {p}(p : seq R) => /= [|a s ->]; first by rewrite big_ord0.
rewrite big_ord_recl simp addrC big_distrl /=; congr (_ + _).
by apply: eq_bigr => i _; rewrite -mulrA exprSr.
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

Lemma horner_sum : forall I r (P : pred I) F x,
  (\sum_(i <- r | P i) F i).[x] = \sum_(i <- r | P i) (F i).[x].
Proof.
move=> I r P F x; pose appx p := p.[x].
apply: (big_morph appx) => [p q|]; [exact: horner_add | exact: horner0].
Qed.

Lemma horner_Cmul : forall c p x, (c%:P * p).[x] = c * p.[x].
Proof.
move=> c p x.
elim/(@poly_ind R): p => [|p d IHp]; first by rewrite !(simp, horner0).
rewrite mulr_addr -polyC_mul mulrA -!poly_cons_def !horner_cons IHp.
by rewrite -mulrA -mulr_addr.
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
move=> p q x com_qx.
elim/(@poly_ind R): p => [|p c IHp]; first by rewrite !(simp, horner0).
rewrite mulr_addl -poly_cons_def horner_cons mulr_addl -!mulrA.
rewrite com_qx -comm_polyX !mulrA -{}IHp -[_ * 'X]addr0 -poly_cons_def.
by rewrite horner_add horner_cons simp horner_Cmul.
Qed.

Lemma horner_exp_com : forall p x n, com_poly p x -> (p ^+ n).[x] = p.[x] ^+ n.
Proof.
move=> p x n com_px; elim: n => [|n IHn]; first by rewrite hornerC.
by rewrite -addn1 !exprn_addr !expr1 -IHn horner_mul_com.
Qed.

Lemma hornerXn : forall x n, ('X^n).[x] = x ^+ n.
Proof. by move=> x n; rewrite horner_exp_com /com_poly hornerX. Qed.

Definition horner_lin_com :=
  (horner_add, horner_opp, hornerX, hornerC, horner_cons,
   simp, horner_Cmul, (fun p x => horner_mul_com p (com_polyX x))).

Lemma factor0 : forall c, ('X - c%:P).[c] = 0.
Proof. by move=> c; rewrite !horner_lin_com addrN. Qed.

Lemma seq_factor : forall c, 'X - c%:P = [:: - c; 1] :> seq R.
Proof.
move=> c; rewrite -['X]mul1r -polyC_opp -poly_cons_def.
by rewrite polyseq_cons size_poly1 polyseq1.
Qed.

Lemma monic_factor : forall c, monic ('X - c%:P).
Proof. by move=> c; rewrite /monic /lead_coef seq_factor. Qed.

Theorem factor_theorem : forall p c,
  reflect (exists q, p = q * ('X - c%:P)) (p.[c] == 0).
Proof.
move=> p c; apply: (iffP eqP) => [root_p_c | [q -> {p}]]; last first.
  by rewrite horner_mul_com /com_poly factor0 ?simp.
set f := 'X - _; exists (p %/ f). 
have mf: monic f by exact: monic_factor.
move: (divp_mon_spec p mf) root_p_c => def_p; rewrite {1 2}def_p.
have:= modp_spec p (monic_neq0 mf); move: (_ %% _) => c1.
rewrite seq_factor ltnS; move/size1_polyC->.
have cfc: com_poly f c by rewrite /com_poly factor0 !simp.
by rewrite !(factor0, horner_mul_com _ cfc, horner_lin_com) => ->; rewrite simp.
Qed.


Lemma root_factor_theorem : forall (p : {poly R}) x,
  p.[x] == 0 = ('X - x%:P %| p).
Proof.
move=> p x; apply/factor_theorem/dvdpPm; first exact: monic_factor.
  by case=> p1 ->; exists p1.
by case=> p1 ->; exists p1.
Qed.


End EvalPolynomial.

Notation "p .[ x ]" := (horner p x) : ring_scope.

Section PolynomialComRing.

Variable R : comRingType.

Lemma horner_mul : forall (p q : {poly R}) x, 
  (p * q).[x] = p.[x] * q.[x].
Proof. move=> p q x; rewrite horner_mul_com //; exact: mulrC. Qed.

Lemma horner_exp : forall (p : {poly R}) x n, (p ^+ n).[x] = p.[x] ^+ n.
Proof. move=> p x n; rewrite horner_exp_com //; exact: mulrC. Qed.

Definition horner_lin :=
  (horner_add, horner_opp, hornerX, hornerC, horner_cons,
   simp, horner_Cmul, horner_mul).

Lemma poly_mulC : forall p1 p2 : {poly R}, p1 * p2 = p2 * p1.
Proof.
move=> p1 p2; apply/polyP=> i; rewrite coef_mul coef_mul_rev.
by apply: eq_bigr => j _; rewrite mulrC.
Qed.

Canonical Structure poly_comRingType := Eval hnf in ComRingType poly_mulC.
Canonical Structure polynomial_comRingType :=
  Eval hnf in [comRingType of polynomial R for poly_comRingType].

(* Pseudo-division in a commutative setting *)

Lemma edivp_spec: forall (p q: {poly R}) n c qq r,
  let d := edivp_rec q n c qq r in
  c%:P * p = qq * q + r -> (d.1).1%:P * p = (d.1).2 * q + d.2.
Proof.
move=> p q; elim=> [| n Hrec] c qq r /=; case: ltnP => Hp //=.
  rewrite polyC_mul -mulrA => ->.
  rewrite mulr_addl mulr_addr !mulrA -!addrA !(mulrC _%:P).
  by congr (_ + _) => //; rewrite addrC -addrA addrC -addrA addKr.
move=> HH; apply: Hrec.
rewrite polyC_mul -mulrA HH.
rewrite mulr_addl mulr_addr !mulrA -!addrA !(mulrC _%:P).
by congr (_ + _) => //; rewrite addrC -addrA addrC -addrA addKr.
Qed.

Lemma divp_spec: forall p q : {poly R}, (scalp p q)%:P * p = p %/ q * q + p %% q.
Proof.
move=> p q.
rewrite /divp /modp /scalp /edivp.
case: eqP => [->| Hq]; first by rewrite !simp.
by apply: edivp_spec; rewrite !simp.
Qed.

End PolynomialComRing.

Section PolynomialIdomain.

Variable R : idomainType.
Implicit Types x y : R.
Implicit Types p q : {poly R}.

Lemma size_mul_id : forall p q,
  p != 0 -> q != 0 -> size (p * q) = (size p + size q).-1.
Proof.
move=> p q nzp nzq; apply: size_proper_mul.
by rewrite mulf_eq0 !lead_coef_eq0 negb_or nzp nzq.
Qed.

Lemma size_polyC_mul: forall c p, c != 0 -> size (c%:P * p) = size p.
Proof.
move=> c p Ec; case: (eqVneq p 0) => [-> | nzp]; first by rewrite simp.
by rewrite size_mul_id ?polyC_eq0 // size_polyC Ec.
Qed.

Lemma lead_coef_mul_id: forall p q, 
  lead_coef (p * q) = lead_coef p * lead_coef q.
Proof.
move=> p q.
case: (eqVneq p 0) => [->|nzp]; first by rewrite !(simp, lead_coef0).
case: (eqVneq q 0) => [->|nzq]; first by rewrite !(simp, lead_coef0).
by rewrite lead_coef_proper_mul // mulf_eq0 !lead_coef_eq0 negb_or nzp nzq.
Qed.

Lemma scalp_id: forall p q, scalp p q != 0.
Proof.
move=> p q; case: (eqVneq q 0) => [->|nzq]. 
  by rewrite /scalp /edivp eqxx nonzero1r.
by case (scalp_spec p q) => m ->; rewrite expf_neq0 ?lead_coef_eq0.
Qed.

(* idomain structure on poly *)

Lemma poly_idomainMixin : forall p q, p * q = 0 -> (p == 0) || (q == 0).
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

Definition poly_unitRingMixin :=
  ComUnitRingMixin poly_mulVp poly_intro_unit poly_inv_out.

Canonical Structure poly_unitRingType :=
   Eval hnf in UnitRingType poly_unitRingMixin.

Canonical Structure poly_comUnitRingType :=
   Eval hnf in ComUnitRingType poly_unitRingMixin.

Canonical Structure poly_idomainType :=
   Eval hnf in IdomainType poly_idomainMixin.

Canonical Structure polynomial_unitRingType :=
   Eval hnf in [unitRingType of polynomial R for poly_unitRingType].

Canonical Structure polynomial_comUnitRingType :=
   Eval hnf in [comUnitRingType of polynomial R for poly_comUnitRingType].

Canonical Structure polynomial_idomainType :=
   Eval hnf in [idomainType of polynomial R for poly_idomainType].

Lemma modp_mull : forall p q, p * q %% q = 0.
Proof.
move=> p q; pose qq := (scalp (p* q) q)%:P * p - (p * q) %/ q.
have Eq: (p * q) %% q = qq * q.
   by rewrite mulr_addl -mulrA divp_spec mulNr addrC addKr.
case: (eqVneq q 0) => [-> | nz_q]; first by rewrite modp0 simp.
case: (eqVneq qq 0) => [qq0 | nz_qq]; first by rewrite Eq qq0 simp.
have:= modp_spec (p * q) nz_q.
by rewrite Eq size_mul_id // polySpred // ltnNge leq_addl.
Qed.

Lemma modpp : forall p, p %% p = 0.
Proof. by move=> p; rewrite -{1}(mul1r p) modp_mull. Qed.

Lemma dvdpp : forall p, p %| p.
Proof. move=> p; apply/eqP; exact: modpp. Qed.

Lemma divp_mull : forall p q, q != 0 -> p * q %/ q = (scalp (p * q) q)%:P * p.
Proof.
move=> p q nz_q.
pose qq := (scalp (p* q) q)%:P * p - (p * q) %/ q.
have Eq: (p * q) %% q = qq * q.
  by rewrite mulr_addl -mulrA divp_spec mulNr addrC addKr.
case: (eqVneq qq 0) => [| nz_qq].
  by move/(canRL (subrK _)); rewrite simp.
have:= modp_spec (p * q) nz_q.
by rewrite Eq size_mul_id // polySpred // ltnNge leq_addl.
Qed.

Lemma dvdpPc : forall p q, 
  reflect (exists c, exists qq, c != 0 /\ c%:P * p = qq * q) (q %| p).
Proof.
move=> /= p q; apply: (iffP idP) => [|[c [qq [nz_c def_qq]]]].
  move/(p %% q =P 0) => dv_qp; exists (scalp p q); exists (p %/ q).
  by rewrite scalp_id divp_spec dv_qp !simp.
have Ecc: c%:P != 0 by rewrite polyC_eq0.
case: (eqVneq p 0) => [->|nz_p]; first by rewrite dvdp0.
pose p1 : {poly R} := (scalp p q)%:P  * qq - c%:P * (p %/ q).
have E1: c%:P * (p %% q) = p1 * q.
  rewrite mulr_addl {1}mulNr -mulrA -def_qq mulrCA.
  by rewrite divp_spec mulr_addr addrAC -mulrA addrN simp.
rewrite /dvdp; apply/idPn=> m_nz.
have: p1 * q != 0 by rewrite -E1 mulf_neq0.
rewrite mulf_eq0; case/norP=> p1_nz q_nz; have:= modp_spec p q_nz.
rewrite -(size_polyC_mul _ nz_c) E1 size_mul_id //.
by rewrite polySpred // ltnNge leq_addl.
Qed.

Lemma size_dvdp : forall p1 p2, p2 != 0 -> p1 %| p2 -> size p1 <= size p2.
Proof.
move=> p1 p2 Ep2; case/dvdpPc => c1 [q1 [Ec1 Ec1p2]].
have: q1 * p1 != 0 by rewrite -Ec1p2 -!size_poly_eq0 size_polyC_mul in Ep2 *. 
rewrite mulf_eq0; case/norP=> Eq1 Ep1.
rewrite -(size_polyC_mul p2 Ec1) Ec1p2 size_mul_id //.
by rewrite (polySpred Eq1) leq_addl.
Qed.

Lemma dvdp_mull : forall d m n : {poly R}, d %| n -> d %| m * n.
Proof.
move=> d m n; case/dvdpPc => c [q [Hc Hq]].
apply/dvdpPc; exists c; exists (m * q); split => //.
by rewrite -mulrA -Hq !mulrA [m * _]mulrC.
Qed.

Lemma dvdp_mulr: forall d m n: {poly R}, d %| m -> d %|  m * n.
Proof. by move=> d m n d_m; rewrite mulrC dvdp_mull. Qed.

Lemma dvdp_mul: forall d1 d2 m1 m2 : {poly R}, 
  d1 %| m1 -> d2 %| m2 -> d1 * d2 %| m1 * m2.
Proof.
move=> d1 d2 m1 m2; case/dvdpPc=> c1 [q1 [Hc1 Hq1]];
  case/dvdpPc=> c2 [q2 [Hc2 Hq2]].
apply/dvdpPc; exists (c1 * c2); exists (q1 * q2); split.
  by rewrite mulf_neq0.
by rewrite polyC_mul mulrCA -!mulrA mulrCA mulrA Hq1 Hq2 mulrCA -!mulrA mulrCA.
Qed.

Lemma dvdp_trans: forall n d m : {poly R}, d %| n -> n %| m -> d %| m.
Proof. 
move=> n d m; case/dvdpPc=> c1 [q1 [Hc1 Hq1]];
  case/dvdpPc=> c2 [q2 [Hc2 Hq2]].
apply/dvdpPc; exists (c2 * c1); exists (q2 * q1); split.
  by apply: mulf_neq0.
rewrite -mulrA -Hq1 [_ * n]mulrC mulrA -Hq2 polyC_mul -!mulrA; congr (_ * _).
by rewrite mulrC.
Qed.

Lemma dvdp_addr : forall m d n : {poly R},
  d %| m -> (d %| m + n) = (d %| n).
Proof.
move=> n d m; case/dvdpPc=> c1 [q1 [Hc1 Hq1]].
apply/dvdpPc/dvdpPc; case=> c2 [q2 [Hc2 Hq2]].
  exists (c1 * c2); exists (c1%:P * q2 - c2%:P * q1).
  rewrite mulf_neq0 // mulr_addl mulNr -2!mulrA -Hq1 -Hq2 (mulrCA c2%:P).
  by rewrite !mulrA -polyC_mul addrC mulr_addr addKr.
exists (c1 * c2); exists (c1%:P * q2 + c2%:P * q1).
rewrite mulf_neq0 // mulr_addl -2!mulrA -Hq1 -Hq2 (mulrCA c2%:P).
by rewrite !mulrA -polyC_mul addrC -mulr_addr.
Qed.

Lemma dvdp_addl : forall n d m : {poly R},
  d %| n -> (d %| m + n) = (d %| m).
Proof. by move=> n d m; rewrite addrC; exact: dvdp_addr. Qed.

Lemma dvdp_add : forall d m n: {poly R}, d %| m -> d %| n -> d %| m + n.
Proof. by move=> n d m; move/dvdp_addr->. Qed.

Lemma dvdp_add_eq : forall d m n: {poly R},
  d %| m + n -> (d %| m) = (d %| n).
Proof. by move=> *; apply/idP/idP; [move/dvdp_addr <-| move/dvdp_addl <-]. Qed.

Lemma dvdp_subr : forall d m n: {poly R},
  d %| m -> (d %| m - n) = (d %| n).
Proof. by move=> *; apply dvdp_add_eq; rewrite -addrA addNr simp. Qed.

Lemma dvdp_subl : forall d m n: {poly R},
  d %| n -> (d %| m - n) = (d %| m).
Proof. by move=> d m n Hn; rewrite -(dvdp_addl _ Hn) subrK. Qed.

Lemma dvdp_sub : forall d m n: {poly R}, d %| m -> d %| n -> d %| m - n.
Proof.  by move=> d n m Dm Dn; rewrite dvdp_subl. Qed.

Lemma dvdp_mod : forall d m n : {poly R},
  d %| m -> (d %| n) = (d %| n %% m).
Proof.
move=> d n m; case/dvdpPc => c1 [q1 [Ec1 Eq1]].
apply/dvdpPc/dvdpPc=> [] [] c2 [q2 [Ec2 Eq2]]; last first.
  exists (c1 * c2 * scalp m n).
  exists (c2%:P * (m  %/ n) * q1 + c1%:P * q2); split.
    by rewrite !mulf_neq0 ?scalp_id.
  rewrite polyC_mul -mulrA divp_spec polyC_mul mulr_addr -!mulrA.
  by rewrite Eq2 2!(mulrCA c1%:P) Eq1 !mulrA -mulr_addl.
exists (c1 * c2); exists (c1%:P * (scalp m n)%:P * q2 - c2%:P * (m %/ n) * q1).
rewrite mulf_neq0 // mulr_addl mulNr -!mulrA -Eq1 -Eq2.
rewrite -{1}(mulrCA c2%:P) divp_spec -addrC -2!{1}(mulrCA c1%:P).
by rewrite 2!{1}(mulrA c1%:P) -polyC_mul mulr_addr addKr.
Qed.

Lemma gcdpp : idempotent (@gcdp R).
Proof. by move=> p; rewrite gcdpE ltnn modpp gcd0p. Qed.

Lemma dvdp_gcd2 : forall m n : {poly R}, (gcdp m n %| m) && (gcdp m n %| n).
Proof.
move=> m n.
elim: {m n}minn {-2}m {-2}n (leqnn (minn (size n) (size m))) => [|r Hrec] m n.
  rewrite leq_minl !leqn0 !size_poly_eq0.
  by case/pred2P=> ->; rewrite (gcdp0, gcd0p) dvdpp dvdp0.
case: (eqVneq m 0) => [-> _|nz_m]; first by rewrite gcd0p dvdpp dvdp0.
case: (eqVneq n 0) => [->|nz_n]; first by rewrite gcdp0 dvdpp dvdp0.
rewrite gcdpE minnC /minn; case: ltnP => [lt_mn | le_nm] le_nr.
  suff: minn (size m) (size (n %% m)) <= r.
    by move/Hrec; case/andP => E1 E2; rewrite E2 (dvdp_mod _ E2).
  rewrite leq_minl orbC -ltnS (leq_trans _ le_nr) //.
  by rewrite (leq_trans (modp_spec _ nz_m)) // leq_minr ltnW // leqnn.
suff: minn (size n) (size (m %% n)) <= r.
  by move/Hrec; case/andP => E1 E2; rewrite E2 andbT (dvdp_mod _ E2).
rewrite leq_minl orbC -ltnS (leq_trans _ le_nr) //.
by rewrite (leq_trans (modp_spec _ nz_n)) // leq_minr leqnn.
Qed.

Lemma dvdp_gcdl : forall m n : {poly R}, gcdp m n %| m.
Proof. by move=> m n; case/andP: (dvdp_gcd2 m n). Qed.

Lemma dvdp_gcdr : forall m n : {poly R}, gcdp m n %| n.
Proof. by move=> m n; case/andP: (dvdp_gcd2 m n). Qed.

Lemma dvdp_gcd : forall p m n: {poly R}, p %| gcdp m n = (p %| m) && (p %| n).
Proof.
move=> p m n; apply/idP/andP=> [dv_pmn | [dv_pm dv_pn]].
  by rewrite ?(dvdp_trans dv_pmn) ?dvdp_gcdl ?dvdp_gcdr.
move: (leqnn (minn (size n) (size m))) dv_pm dv_pn.
elim: {m n}minn {-2}m {-2}n => [|r Hrec] m n.
  rewrite leq_minl !leqn0 !size_poly_eq0.
  by case/pred2P=> ->; rewrite (gcdp0, gcd0p).
case: (eqVneq m 0) => [-> _|nz_m]; first by rewrite gcd0p dvdp0.
case: (eqVneq n 0) => [->|nz_n]; first by rewrite gcdp0 dvdp0.
rewrite gcdpE minnC /minn; case: ltnP => Cnm le_r dv_m dv_n.
  apply: Hrec => //; last by rewrite -(dvdp_mod _ dv_m).
  rewrite leq_minl orbC -ltnS (leq_trans _ le_r) //.
  by rewrite (leq_trans (modp_spec _ nz_m)) // leq_minr ltnW // leqnn.
apply: Hrec => //; last by rewrite -(dvdp_mod _ dv_n).
rewrite leq_minl orbC -ltnS (leq_trans _ le_r) //.
by rewrite (leq_trans (modp_spec _ nz_n)) // leq_minr leqnn.
Qed.

(* Equality modulo constant factors *)

Definition eqp (R : ringType)(p1 p2: {poly R}) :=  (p1 %| p2) && (p2 %| p1).

Notation "p1 '%=' p2" := (eqp p1 p2)
  (at level 70, no associativity).

Lemma eqpP: forall m n: {poly R},
  reflect (exists c1, exists c2, [/\ c1 != 0, c2 != 0 & c1%:P * m = c2%:P * n])
          (m %= n).
Proof.
move=> m n; apply: (iffP idP) => [|[c1 [c2 [nz_c1 nz_c2 eq_cmn]]]]; last first.
  by apply/andP; split; apply/dvdpPc;
      [exists c2; exists c1%:P | exists c1; exists c2%:P].
case/andP; case/dvdpPc=> /= c1 [q1 [Hc1 Hq1]].
case/dvdpPc=> /= c2 [q2 [Hc2 Hq2]].
case: (eqVneq m 0) => [m0 | m_nz].
  by do 2!exists c1; rewrite Hq1 m0 !simp.
have def_q12: q1 * q2 = (c1 * c2)%:P.
  by apply: (mulIf m_nz); rewrite polyC_mul -!mulrA mulrCA -Hq1 mulrCA -Hq2.
have: q1 * q2 != 0 by rewrite def_q12 -size_poly_eq0 size_polyC mulf_neq0.
rewrite mulf_eq0; case/norP=> nz_q1 nz_q2.
exists c2; exists q2`_0; rewrite Hc2 -polyC_eq0 -size1_polyC //.
have:= size_mul_id nz_q1 nz_q2; rewrite def_q12 size_polyC mulf_neq0 //=.
by rewrite polySpred // => ->; rewrite leq_addl.
Qed.

Lemma eqpxx: forall p, p %= p.
Proof. by move=> p; rewrite /eqp dvdpp. Qed. 

Lemma eqp_sym: forall p1 p2, (p1 %= p2) = (p2 %= p1).
Proof. by move=> p1 p2; rewrite /eqp andbC. Qed.

Lemma eqp_trans : forall p1 p2 p3, p1 %= p2 -> p2 %= p3 -> p1 %= p3.
Proof.
move=> p1 p2 p3; case/andP => Dp1 pD1; case/andP => Dp2 pD2.
by rewrite /eqp (dvdp_trans Dp1) // (dvdp_trans pD2).
Qed.

Lemma eqp0E : forall p, (p %= 0) = (p == 0).
Proof.
move=> p; case: eqP; move/eqP=> Ep; first by rewrite (eqP Ep) eqpxx.
by apply/negP; case/andP=> _; rewrite /dvdp modp0 (negPf Ep).
Qed.

Lemma size_eqp: forall p1 p2, p1 %= p2 -> size p1 = size p2.
Proof.
move=> p1 p2.
case: (@eqP _ p2 0); move/eqP => Ep2.
  by rewrite (eqP Ep2) eqp0E; move/eqP->.
rewrite eqp_sym; case: (@eqP _ p1 0); move/eqP => Ep1.
  by rewrite (eqP Ep1) eqp0E; move/eqP->.
by case/andP => Dp1 Dp2; apply: anti_leq; rewrite !size_dvdp.
Qed.

(* Now we can state that gcd is commutative modulo a factor *)
Lemma gcdpC: forall p1 p2, gcdp p1 p2 %= gcdp p2 p1.
Proof.
by move=>p1 p2; rewrite /eqp !dvdp_gcd !dvdp_gcdl !dvdp_gcdr.
Qed.

End PolynomialIdomain.


Section MaxRoots.

Variable R : unitRingType.

Definition roots (p : {poly R}) : pred R := fun x => p.[x] == 0.

Definition diff_root (x y : R) := (x * y == y * x) && GRing.unit (y - x).

Fixpoint uniq_roots (rs : seq R) {struct rs} :=
  if rs is x :: rs' then all (diff_root x) rs' && uniq_roots rs' else true.

Theorem max_ring_poly_roots : forall (p : {poly R}) rs,
  p != 0 -> all (roots p) rs -> uniq_roots rs -> size rs < size p.
Proof.
move=> p rs; elim: rs p => [|x rs IHrs] p nzp /=; first by rewrite polySpred.
case/andP=> p_x p_rs; case/andP=> x_rs Urs.
case/factor_theorem: p_x => q def_p.
have nzq: q != 0 by apply: contra nzp => q0; rewrite def_p (eqP q0) mul0r.
have ->: size p = (size q).+1.
  by rewrite def_p size_mul_monic ?monic_factor ?seq_factor //= addnC.
apply: IHrs Urs => //; apply/allP=> y rs_y.
case/andP: (allP x_rs _ rs_y) => cxy Uxy.
have:= allP p_rs _ rs_y; rewrite /roots def_p horner_mul_com; last first.
  by rewrite /com_poly !horner_lin_com mulr_addl mulr_addr mulrN mulNr (eqP cxy).
by rewrite !horner_lin_com (can2_eq (mulrK Uxy) (divrK Uxy)) mul0r.
Qed.

End MaxRoots.

Theorem max_poly_roots : forall (F : fieldType) (p : polynomial F) rs,
  p != 0 -> all (roots p) rs -> uniq rs -> size rs < size p.
Proof.
move=> F p rs nzp p_rs Urs; apply: max_ring_poly_roots nzp p_rs _ => {p}//.
elim: rs Urs => //= x rs IHrs; case/andP=> rs_x; move/IHrs->; rewrite andbT.
apply/allP=> y rs_y; rewrite /diff_root mulrC eqxx unitfE.
by rewrite (can2_eq (subrK _) (addrK _)) add0r; apply: contra rs_x; move/eqP<-.
Qed.

