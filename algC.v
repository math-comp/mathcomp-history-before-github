(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq bigop div fintype.
Require Import prime finset fingroup ssralg pgroup mxrepresentation.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.

(**************************************************************************)
(* This file deals is an axiomatic presentation of an algebraic closed    *)
(* field over R                                                           *)
(*    C : the closed field                                                *)
(*    x^* = conjugate                                                     *)
(*   0 <= x : x is a positive real                                        *)
(*   x <= y : (y - x) is a positive real                                  *)
(*    x < y : (y - x) is a real positive real                             *)
(*   sqrC x : square root such that sqrt x^2 = x for 0 <= x               *)
(*  normC x : norm of x i.e. sqrC(x * x^* )                               *)
(*  isRatC  : test for rationality                                        *)
(*  getRatC : the rational components,                                    *)
(*            if isRatC x and (n,d) = getRatC x then                      *)
(*               x = (-1)^b * n%:R * (d.+1)%:R^-1                         *)
(*  isNatC  : test for naturality                                         *)
(*  getNatC : the natural component                                       *)
(*            if isNatC x and x = getNatC x)%:R                           *)
(**************************************************************************)

Parameter C : closedFieldType.
Axiom Cchar : [char C] =i pred0.

Parameter conjC : {rmorphism C -> C}.
Notation "x ^* " := (conjC x) (at level 2, format "x ^*") : C_scope.
Open Scope C_scope.
Delimit Scope C_scope with C.

Axiom conjCK : involutive conjC.

Parameter repC : C -> bool. (* C -> R^+ *)
Axiom repCD : forall x y, repC x -> repC y -> repC (x + y).
Axiom repCMl : forall x y, x != 0 -> repC x -> repC (x * y) = repC y.
Axiom repC_anti : forall x, repC x -> repC (-x) -> x = 0.
Axiom repC_unit_exp : forall x n, repC x -> ((x^+n.+1 == 1) = (x == 1)).
Axiom repC_pconj : forall x, repC (x * x ^*).
Axiom repC_conjI : forall x, repC x -> x^* = x.
Axiom repC1 : repC 1.

Lemma repC_inv : forall x, repC (x^-1) = repC x.
Proof.
move=> x; case: (x =P 0)=> [->|]; first by rewrite invr0.
move/eqP; move=> Hx; apply/idP/idP=> Hp.
  by rewrite -(repCMl _ (invr_neq0 Hx)) // mulVf // repC1.
by rewrite -(repCMl _ Hx) // mulfV // repC1.
Qed.

Lemma repC_conj : forall x, repC (x ^*) = repC (x).
Proof.
by move=>x; apply/idP/idP=>Hp; first rewrite -[x]conjCK; 
   rewrite (repC_conjI Hp).
Qed.

Lemma repC0 : repC 0.
Proof. by rewrite -[0](mul0r (0 ^*)) repC_pconj. Qed.

Lemma repC_nat : forall n, repC (n%:R).
Proof.
by elim=> [|n IH]; [exact: repC0 | rewrite -addn1 natr_add repCD // repC1].
Qed.

Lemma conjC_nat : forall n, (n%:R)^* = n%:R.
Proof. exact: rmorph_nat. Qed.

Lemma conjC0 : 0 ^* = 0.
Proof. exact: (conjC_nat 0). Qed.

Lemma conjC1 : 1 ^* = 1.
Proof. exact: (conjC_nat 1). Qed.

Lemma conjC_eq0 : forall x, (x ^* == 0) = (x == 0).
Proof.
move=> x; apply/eqP/eqP=> H; last by rewrite H (conjC_nat 0).
by rewrite -[x]conjCK H (conjC_nat 0).
Qed.

Definition leC x y := repC (y - x).

Notation "x <= y" := (leC x y) : C_scope.

Definition ltC x y := ((y != x) && (x <= y)).

Notation " x < y " := (ltC x y) : C_scope.

Lemma ltCE : forall x y, (x < y) = ((y != x) && (x <= y)).
Proof. by []. Qed.

Lemma posC_pconj : forall x, 0 <= x * x ^*.
Proof. by move=> x; rewrite /leC subr0 repC_pconj. Qed.

Lemma posC_nat : forall n, 0 <= n%:R.
Proof. by move=> n; rewrite /leC subr0 repC_nat. Qed.

Lemma leC_refl : reflexive leC.
Proof. move=> x; rewrite /leC subrr; exact repC0. Qed.

Lemma ltCW : forall x y, x < y -> x <= y.
Proof. by move=> x y; case/andP. Qed.

Lemma leC_add2l : forall z x y, (z + x <= z + y) = (x <= y).
Proof.
by move=> z x y; rewrite /leC oppr_add addrA [z + _]addrC addrK.
Qed.

Lemma leC_add2r : forall z x y, (x + z <= y + z) = (x <= y).
Proof. by move=> z x y; rewrite ![_ +z]addrC leC_add2l. Qed.

Lemma posC_add : forall x y, 0 <= x -> 0 <= y -> 0 <= x + y.
Proof. by move=> x y; rewrite /leC !subr0; exact: repCD. Qed.

Lemma leC_trans : transitive leC.
Proof.
move=> x y z Hx Hy.
by move: (repCD Hy Hx); rewrite addrA subrK.
Qed.

Lemma leC_add : forall x y z t : C, x <= z -> y <= t -> x + y <= z + t.
Proof.
move=> x y z t Hx Hy.
by apply: (@leC_trans (z + y)); [rewrite leC_add2r | rewrite leC_add2l].
Qed.

Lemma posC_mulr : forall x y, 0 < x -> 0 <= x * y = (0 <= y).
Proof. 
move=> x y; case/andP; rewrite /leC !subr0; move=>*.
by apply: repCMl; rewrite // eq_sym. 
Qed.

Lemma posC_mull : forall x y, 0 < x -> 0 <= y * x = (0 <= y).
Proof. move=> x y; rewrite mulrC; exact: posC_mulr. Qed.

Lemma posC_mul : forall x y : C, 0 <= x -> 0 <= y -> 0 <= x * y.
Proof.
move=> x y Hx Hy.
case: (boolP (x == 0)); first by move/eqP->; rewrite mul0r leC_refl.
by move=> Hdx; rewrite posC_mulr //; apply/andP.
Qed.

Lemma leC_anti : forall x y, x <= y -> y <= x -> x = y.
Proof.
move=> x y Hx Hy; apply/eqP; rewrite -subr_eq0; apply/eqP.
by apply: repC_anti; rewrite // oppr_sub.
Qed.

Lemma leC_mul2l : forall m n1 n2, 
  0 <= m -> n1 <= n2 -> m * n1 <= m * n2.
Proof.
move=> m n1 n2 Hm Hn; rewrite {1}/leC -mulr_subr -[_ * _]subr0.
by apply: posC_mul=> //; rewrite -(leC_add2r n1) add0r subrK.
Qed.

Lemma leC_mul2r : forall m n1 n2, 
  0 <= m -> n1 <= n2 -> n1 * m <= n2 * m.
Proof.
by move=> m n1 n2 Hm Hn; rewrite ![_ * m]mulrC leC_mul2l.
Qed.

Lemma leq_leC : forall a b, (a <= b)%N = (a%:R <= b%:R).
Proof.
elim=> [b |a IH [|b]]; first 2 last.
- rewrite -{2}add1n natr_add -{2}[b.+1]add1n natr_add leC_add2l.
  by exact: IH.
- by apply: sym_equal; rewrite leq0n; apply: posC_nat.
apply: sym_equal; rewrite ltn0; apply/idP=> HH.
have: a.+1%:R = 0%:R :> C by apply: leC_anti=> //; apply: posC_nat.
by move/eqP; move/GRing.charf0P: Cchar=> ->.
Qed.

Lemma eqN_eqC : forall a b : nat, (a == b) = (a%:R == b%:R :> C).
Proof.
move=> a b; apply/eqP/eqP=> [->| Hr] //.
wlog le: a b Hr / (a <= b)%N.
  by move=> H; case/orP: (leq_total a b)=> HH; last apply: sym_equal;
     apply: H.
have: b%:R - a%:R = 0 :> C by rewrite Hr subrr.
rewrite -natr_sub //; move/eqP; move/GRing.charf0P: Cchar=> -> HH.
by apply anti_leq; rewrite le.
Qed.

Lemma neq0N_neqC : forall a : nat, (a != 0%N) = (a%:R != 0 :> C).
Proof.
by move=> a; apply/idP/idP; move/negP=> HH; apply/negP=> HH1; case: HH;
   move: HH1; rewrite (eqN_eqC _ 0).
Qed.

Lemma ltC_add2l :  forall p m n, (p + m < p + n) = (m < n).
Proof.
move=> p m n; rewrite ltCE leC_add2l; congr (_ && _).
apply/negP/negP=> HH HH1; case: HH; first by rewrite (eqP HH1).
by apply/eqP; apply: (addrI (eqP HH1)).
Qed.

Lemma ltC_add2r :  forall p m n, (m + p < n + p) = (m < n).
Proof.
by move=> p m n; rewrite ![_ + p]addrC ltC_add2l.
Qed.

Lemma leC_ltC_trans : forall n m p, m <= n -> n < p -> m < p.
Proof.
move=> n m p Hm; rewrite !ltCE; case/andP=> H1m H2m.
rewrite (leC_trans Hm) // andbT.
apply/eqP=> HH; case/eqP: H1m; apply: leC_anti=> //.
by rewrite HH.
Qed.

Lemma ltC_leC_trans : forall n m p, m < n -> n <= p -> m < p.
Proof.
move=> n m p; rewrite !ltCE; case/andP=> H1m H2m Hn.
rewrite (leC_trans H2m) // andbT.
apply/eqP=> HH; case/eqP: H1m; apply: leC_anti=> //.
by rewrite -HH.
Qed.

Lemma ltC_trans : forall n m p, m < n -> n < p -> m < p.
Proof.
move=> n m p; rewrite !ltCE; case/andP=> H1m H2m Hp.
by apply: leC_ltC_trans Hp.
Qed.

Lemma leC_sub : forall x y, (0 <= y - x) = (x <= y).
Proof. by move=> x y; rewrite /leC subr0. Qed.

Lemma ltC_sub : forall x y, (x < y) = (0 < y - x).
Proof. by move=> x y; rewrite -(ltC_add2r (-x)) subrr. Qed.

Lemma ltn_ltC: forall m n, (m < n)%N = (m%:R < n%:R).
Proof.
by move=> m n; rewrite !ltCE -leq_leC -eqN_eqC ltn_neqAle eq_sym.
Qed.

Lemma posC_unit_exp : forall x n, 0 <= x ->  (x ^+ n.+1 == 1) = (x == 1).
Proof. by move=> x n Hx; apply: repC_unit_exp; rewrite -[x]subr0. Qed.

Lemma posC_conjK : forall x, 0 <= x -> x^* = x.
Proof. by move=> x Hx; apply: repC_conjI; rewrite -[x]subr0. Qed.

Lemma posC1 : 0 <= 1.
Proof. by rewrite /leC subr0 repC1. Qed.

Lemma posC_inv : forall x, (0 <= x^-1) = (0 <= x).
Proof. move=> x; rewrite /leC !subr0; exact: repC_inv. Qed.

Lemma sposC_inv: forall x : C, (0 < x^-1) = (0 < x).
Proof.
move=> x; rewrite !ltCE posC_inv; congr (_&&_).
apply/idP/idP=>[HH|]; last by exact: invr_neq0.
by apply/eqP=> HH1;case/eqP: HH; rewrite HH1 invr0.
Qed.

Lemma posC_conj : forall x, (0 <= x ^*) = (0 <= x).
Proof. move=> x; rewrite /leC !subr0; exact: repC_conj. Qed.

Lemma posC_sum : 
   forall (I : eqType) (r : seq I) (P : pred I) (F : I -> C),
   (forall i, (i \in r) && P i -> 0 <= F i) -> 0 <= \sum_(j <- r | P j) F j.
Proof.
move=> i r P F1; elim: r=> [|y r Hrec] H.
  by rewrite big_nil=> *; exact: leC_refl.
rewrite big_cons; case E1: (P _); last first.
  by apply: Hrec=> j; case/andP=> H1j H2j; apply: H; rewrite in_cons H1j orbT.
apply: posC_add.
  by apply: H; rewrite in_cons eqxx.
by apply: Hrec=> j; case/andP=> H1j H2j; apply: H; rewrite in_cons H1j orbT.
Qed.

Lemma posC_add_eq0 : forall x y,
  0 <= x -> 0 <= y -> (x + y == 0) = ((x == 0) && (y == 0)).
Proof.
move=> x y Hx Hy; apply/eqP/andP=>[Hxy|]; last first.
  by case; do 2 move/eqP->; exact: addr0.
split; apply/eqP; apply: leC_anti=> //.
  by rewrite -(leC_add2r y) Hxy add0r.
by rewrite -(leC_add2l x) Hxy addr0.
Qed.

Lemma posC_sum_eq0 : 
   forall (I : eqType) (r : seq I) (P : pred I) (F : I -> C),
   (forall i, (i \in r) && P i -> 0 <= F i) ->
   \sum_(j <- r | P j) F j = 0 ->
   (forall i, (i \in r) && P i -> F i = 0).
Proof.
move=> I r P F; elim: r=> [|y r Hrec] // HN.
rewrite big_cons; case HP: (P _)=> Hs; last first.
  move=> i; rewrite in_cons.
  case/andP; case/orP=> [|Hi Hn]; first by move/eqP->; rewrite HP.
  apply: Hrec=> //; last by rewrite Hi.
  by move=> j; case/andP=> H1j H2j; apply: HN; rewrite in_cons H1j orbT.
have F1: 0 <= \sum_(j <- r | P j) F j.
  by apply: posC_sum=> i; case/andP=> H1i H2i; rewrite HN // in_cons H1i orbT.
move/eqP: Hs; rewrite posC_add_eq0 ?HN //; last by rewrite in_cons eqxx.
case/andP; move/eqP=> HH1; move/eqP=> HH2.
move=> i; rewrite in_cons; case/andP; case/orP; first by move/eqP->.
move=> H1i H2i; apply: Hrec=> //; last by rewrite H1i.
by move=> j; case/andP=> H1j H2j; apply: HN; rewrite in_cons H1j orbT.
Qed.


Lemma sposC_addl : forall m n, 0 <= m -> 0 < n -> 0 < m + n.
Proof.
move=> m n Hm Hn; apply: (leC_ltC_trans Hm).
by rewrite -{1}[m]addr0 ltC_add2l.
Qed.

Lemma sposC_addr : forall m n, 0 < m -> 0 <= n -> 0 < m + n.
Proof.
by move=> m n Hm Hn; rewrite addrC; apply: sposC_addl.
Qed.

Lemma sposC_mul : forall m n, 0 < m -> 0 < n -> 0 < m * n.
Proof.
move=> m n; case/andP=> H1m H2m; case/andP=> H1n H2n; apply/andP; split.
  by rewrite mulf_eq0 (negPf H1m).
by apply: posC_mul.
Qed.

Definition leCif m n c := ((m <= n) * ((m == n) = c))%type.

Notation "m <= n ?= 'iff' c" := (leCif m n c)
    (at level 70, n at next level,
  format "m '[hv'  <=  n '/'  ?=  'iff'  c ']'") : C_scope.

Coercion leC_of_leqif m n c (H : m <= n ?= iff c) := H.1 : m <= n.

Lemma leCifP : forall m n c,
   reflect (m <= n ?= iff c) (if c then m == n else m < n).
Proof.
move=> m n c; apply: (iffP idP); last first.
  case: c=> [] [H1 H2]; last by rewrite ltCE eq_sym H2.
  by apply/eqP; apply: leC_anti=> //; rewrite (eqP H2) leC_refl.
case c; [move/eqP-> |]; split; rewrite ?eqxx //; first exact: leC_refl.
  by apply: ltCW.
by move: H; rewrite ltCE eq_sym; case: eqP.
Qed.

Variable sqrC : C -> C.
Axiom sqrCK : forall c, (sqrC c) ^+ 2 = c.
Axiom repC_sqr : forall c, repC (sqrC c) = repC c.
Axiom sqrC_mul : {morph sqrC: x y / x * y}.

Lemma sqrC_sqr : forall c, (sqrC (c^+2) == c) || (sqrC (c^+2) == -c).
Proof.
move=> c; set sc := sqrC _.
suff: (sc - c) * (sc + c) == 0.
  rewrite mulf_eq0; case/orP; first by rewrite subr_eq0=>->.
  by rewrite orbC -{1}[c]opprK subr_eq0=>->.
rewrite mulr_addr !mulr_subl addrA [c * _]mulrC subrK subr_eq0.
by rewrite -{2}[sc]expr1 -exprS sqrCK.
Qed.

Lemma sqrC0 : sqrC 0 = 0.
Proof. 
have:= sqrCK 0; rewrite exprS expr1.
by move/eqP; rewrite mulf_eq0; case/orP; move/eqP.
Qed.

Lemma sqrC_eq0 : forall c, (sqrC c == 0) = (c == 0).
Proof.
move=> c; apply/eqP/eqP; last by move->; exact: sqrC0.
by rewrite -{2}[c]sqrCK=>->; rewrite exprS mul0r.
Qed.

Lemma sqrC_pos : forall c, (0 <= sqrC c) = (0 <= c).
Proof. by move=> c; rewrite /leC !subr0 repC_sqr. Qed.

Lemma sqrC_sqr_pos : forall c, 0 <= c -> sqrC (c^+2) = c.
Proof.
move=> c Hc; case/orP: (sqrC_sqr c)=>[|HH]; first by move/eqP.
suff->: c = 0 by rewrite exprS mul0r sqrC0.
apply: leC_anti=> //; rewrite /leC sub0r.
rewrite -(eqP HH) repC_sqr -[_^+_]subr0; by apply: posC_mul.
Qed.

Lemma sqrC1 : sqrC 1 = 1.
Proof. by rewrite -{2}(sqrC_sqr_pos posC1) exprS mul1r. Qed. 
 
Definition normC x := sqrC (x * x^*).

Axiom normC_add : forall x y,  normC (x + y) <= normC x + normC y.
Axiom normC_add_eq : forall x y : C, 
  normC (x + y) = normC(x) + normC(y) -> 
  exists2 k, normC k = 1 & ((x == normC x * k) && (y == normC y * k)).

Lemma posC_norm : forall x, 0 <= normC x.
Proof. 
move=> x; rewrite /leC !subr0 repC_sqr; exact: repC_pconj.
Qed.

Lemma normC_pos : forall c, 0 <= c -> normC c = c.
Proof. by move=> c Hc; rewrite /normC posC_conjK // (sqrC_sqr_pos Hc). Qed.

Lemma normC_nat : forall n, normC n%:R = n%:R.
Proof. by move=> n; apply: normC_pos; exact: posC_nat. Qed.

Lemma normC0 : normC 0 = 0.
Proof. by rewrite normC_pos // leC_refl. Qed.

Lemma normC_eq0 : forall c, (normC c == 0) = (c == 0).
Proof.
move=> c; apply/idP/eqP; last by move->; rewrite normC0.
rewrite sqrC_eq0 mulf_eq0; case/orP; first by move/eqP.
by rewrite conjC_eq0; move/eqP.
Qed.

Lemma normC1 : normC 1 = 1.
Proof. by rewrite normC_pos // posC1. Qed.

Lemma normC_mul :  {morph normC: x y / x * y}.
Proof.
move=> x y; rewrite /normC rmorphM -sqrC_mul -!mulrA; 
by congr sqrC; congr (_ * _); rewrite mulrC -!mulrA [y * _]mulrC.
Qed.

Lemma normC_exp : forall x n, normC (x^+n) = normC x ^+ n.
Proof.
move=> x; elim=> [|n IH]; first by rewrite !expr0 normC1.
by rewrite exprS normC_mul IH exprS.
Qed.

Lemma normC_conj : forall x, normC (x^*) = normC x.
Proof. by move=> x; rewrite /normC conjCK mulrC. Qed.

Lemma normC_inv : forall x : C, normC (x^-1) = normC x ^- 1.
Proof.
move=> x.
case: (normC x =P 0); move/eqP.
  by rewrite normC_eq0; move/eqP->; rewrite !(normC0,invr0).
move=> HH; apply: (mulIf HH).
by rewrite mulVf // -normC_mul mulVf ?normC1 // -normC_eq0.
Qed.

Lemma invC_norm : forall x, x^-1 = (normC x)^-2 * x^*.
Proof.
move=> x; case: (x =P 0)=> [->|]; first by rewrite conjC0 mulr0 invr0.
move/eqP=> Hx.
have F1: normC x ^+ 2 != 0.
  by rewrite exprS expr1; apply: mulf_neq0; rewrite normC_eq0.
apply: (mulfI F1); rewrite mulrA divff // mul1r sqrCK [x * _]mulrC.
by rewrite -mulrA divff // mulr1.
Qed.

Lemma conjC_inv : forall x, (x^-1)^* = (x^*)^-1.
Proof.
move=> x; rewrite invC_norm rmorphM conjCK.
rewrite (invC_norm x^*) conjCK; congr (_ * _).
rewrite normC_conj; apply: posC_conjK.
by rewrite posC_inv exprS expr1 posC_mul // posC_norm.
Qed.

Lemma normC_sum : 
   forall (I : eqType) (r : seq I) (P : pred I) (F : I -> C),
   normC (\sum_(i <- r | P i) F i) <= \sum_(i <- r | P i) normC(F i).
Proof.
move=> I r P F; elim: r=> [|i r Hrec].
  by rewrite !big_nil normC0 leC_refl.
rewrite !big_cons; case HP: (P _)=> //.
by apply: (leC_trans (normC_add _ _)); rewrite leC_add2l.
Qed.

Lemma normC_sum_eq : 
   forall (I : eqType) (r : seq I) (P : pred I) (F : I -> C),
   normC (\sum_(j <- r | P j) F j) = (\sum_(j <- r | P j) normC(F j)) ->
   exists2 k, normC k = 1 &
              forall i, (i \in r) && P i -> F i = normC (F i) * k.
Proof.
move=> i r P F; elim: r=> [|j r IH].
  by rewrite !big_nil; exists 1=> //; exact: normC1.
rewrite !big_cons; case HP: (P _)=> HH; last first.
  case: IH=> // k Hk Hr; exists k=> // j1.
  rewrite in_cons; case/andP; case/orP; first by move/eqP->; rewrite HP.
  by move=> *; apply Hr; apply/andP; split.
have F1: normC(\sum_(j <- r | P j) F j) = \sum_(j <- r | P j) normC (F j).
  apply: leC_anti; first by apply: normC_sum.
  by rewrite -(leC_add2l (normC (F j))) -HH normC_add.
move: HH; rewrite -F1; case/normC_add_eq=> k1 H1k1; case/andP=> H2k1 H3k1.
exists k1=> // j1; rewrite in_cons; case/andP; case/orP.
  by move/eqP->; rewrite -(eqP H2k1).
move=> Hj1 Pj1; case: IH=> // k2 H1k2 H2k2.
move: H3k1.
have HH: \sum_(j <- r | P j) F j = (\sum_(j <- r | P j) normC (F j)) * k2.
  elim: {F1 Hj1}r H2k2=> [|j2 r IH1 Hr]; first by rewrite !big_nil mul0r.
  rewrite !big_cons IH1 //; last first.
    by move=> j3; case/andP=> H1j3 H2j3; rewrite -Hr // in_cons H1j3 orbT.
  by case E1: (P _)=> //; rewrite {1}Hr ?(in_cons,eqxx) // mulr_addl.
rewrite {1}HH F1; move/eqP=> HH1.
case: ((\sum_(j0 <- r | P j0) normC (F j0)) =P 0)=> HH2.
  suff: normC (F j1) = 0.
    by move/eqP; rewrite normC_eq0; move/eqP->; rewrite normC0 mul0r.
  apply: (posC_sum_eq0 _ HH2); last by rewrite Hj1.
  move=> j2; case/andP=> H1j2 H2j2 //.
  by apply: posC_norm; rewrite Hj1.
suff->: k1 = k2 by apply: H2k2; rewrite Hj1.
by move/eqP: HH2; move/mulfI; apply.
Qed.

Lemma normC_sum_eq1: 
   forall (I : eqType) (r : seq I) (P : pred I) (F : I -> C),
   normC (\sum_(j <- r | P j) F j) = (\sum_(j <- r | P j) normC(F j)) ->
   (forall i, (i \in r) && P i -> normC (F i) = 1) ->
   exists2 k, normC k = 1 &
              forall i, (i \in r) && P i -> F i = k.
Proof.
move=> I r P F NN N1.
case: (normC_sum_eq NN)=> k Nk Hk.
exists k=> // i Hi.
by move: (Hk _ Hi); rewrite N1 // mul1r.
Qed.

Lemma normC_sum_upper : 
   forall (I : eqType) (r : seq I) (P : pred I) (F : I -> C) (G : I -> C),
   (forall i, (i \in r) && P i -> normC (F i) <= G i) ->
   \sum_(j <- r | P j) F j = \sum_(j <- r | P j) (G j) ->
   forall i, (i \in r) && P i -> F i = G i.
Proof.
move=> I r P F G Hn Hs.
have F0: forall i, (i \in r) && P i -> 0 <= G i.
  by move=> i Pi; apply: leC_trans (Hn _ Pi); exact: posC_norm.
have F1: normC (\sum_(j <- r | P j) F j) = 
          \sum_(j <- r | P j) normC (F j).
  apply: leC_anti=> //; first by apply: normC_sum.
  rewrite Hs normC_pos; last by apply: posC_sum.
  rewrite /leC -sumr_sub -[\sum_(i <- _| _)_]subr0.
  apply: posC_sum=> i Hi.
  by rewrite -(leC_add2r (normC (F i))) add0r subrK // Hn.
case: (normC_sum_eq F1)=> k H1k H2.
have F2: \sum_(j <- r | P j) F j = (\sum_(j <- r | P j) normC (F j)) * k.
  elim: {F0 Hn Hs F1}r H2=> [|j2 r IH1 Hr]; first by rewrite !big_nil mul0r.
  rewrite !big_cons IH1 //; last first.
    by move=> j3; case/andP=> H1j3 H2j3; rewrite -Hr // in_cons H1j3 orbT.
  by case E1: (P _)=> //; rewrite {1}Hr ?(in_cons,eqxx) // mulr_addl.
case: ((\sum_(j <- r | P j) normC (F j)) =P 0)=> H1.
  have F3 := (posC_sum_eq0 (fun i Hi => (posC_norm (F i))) H1).
  move: Hs; rewrite F2 H1 mul0r. move/(@sym_equal _ _ _)=> F4.
  move=> i; case/andP=> H1i H2i.
  rewrite (posC_sum_eq0 _ F4) ?H1i //.
  by apply/eqP; rewrite -normC_eq0 F3 // H1i.
have F3: k = 1.
  rewrite -[k]normC_pos ?H1k //.
  have F4: 0 <= (\sum_(j <- r | P j) normC (F j))^-1.
    by rewrite posC_inv; apply: posC_sum=> i Hi; exact: posC_norm.
  have F5: 0 <= (\sum_(j <- r | P j) normC (F j)) * k.
    by rewrite -F2 Hs posC_sum.
  by move: (posC_mul F4 F5); rewrite mulKr // GRing.unitfE; apply/eqP.
move=> i; case/andP=> Hi Pi; apply/eqP; rewrite eq_sym -subr_eq0; apply/eqP.
have F4: \sum_(j <- r | P j) (G j - F j) = 0.
  by rewrite sumr_sub Hs subrr.
apply: (posC_sum_eq0 _ F4)=> [j Hj|]; last by rewrite Hi.
rewrite -(leC_add2r (F j)) add0r subrK H2 //.
by rewrite F3 mulr1 Hn.
Qed.

Variable getRatC : C -> (bool * nat * nat).
Definition isRatC c := 
   match getRatC c with (b,n,d) => c == (-1)^+b * n%:R * d.+1%:R^-1 end.

Axiom isRatCP :
  forall c,
   reflect
     (exists b: bool, exists p, c = (-1)^+b * p.1%:R * p.2.+1%:R^-1)
     (isRatC c).

Lemma isRatC_opp : forall c , isRatC (-c) = isRatC c.
Proof.
by move=>c;apply/isRatCP/isRatCP=> [] [b [[n d]] H];
   exists (~~b); exists (n,d); first rewrite -[c]opprK;
   rewrite H -!mulNr; case b; rewrite !(expr0,expr1,opprK).
Qed.

Lemma isRatC_add : forall c1 c2, isRatC c1 -> isRatC c2 -> isRatC (c1 + c2).
Proof.
move=> c1 c2; case/isRatCP=> b1 [[n1 d1] ->]; case/isRatCP=> b2 [[n2 d2] ->].
case: (b1 =P b2)=> [<-|Hb].
  apply/isRatCP; exists b1; exists (n1 * d2.+1 + n2 * d1.+1,(d1.+1 * d2.+1).-1)%N.
  rewrite -!mulrA -mulr_addr; congr (_ * _)%R.
  have F1: (d1.+1 * d2.+1)%:R != 0 :> C by rewrite -neq0N_neqC.
  apply: (mulIf F1); apply: sym_equal.
  rewrite -mulrA prednK // mulVf // mulr1 natr_add !natr_mul.
  rewrite mulr_addl mulrA mulfVK -?neq0N_neqC //.
  by rewrite [d1.+1%:R * _]mulrC mulrA mulfVK // -neq0N_neqC.
have->: (-1) ^+ b2 = -(-1) ^+ b1 :> C.
  by case: b1 Hb; case: b2=> // _; rewrite expr1 opprK.
rewrite !mulNr.
wlog HH : n1 d1 n2 d2 / (n2 * d1.+1 <= n1 * d2.+1)%N=> [HH|].
  case: (leqP  (n2 * d1.+1)%N (n1 * d2.+1)%N)=> H; first by apply: HH.
  by rewrite -isRatC_opp oppr_sub HH // ltnW.
apply/isRatCP; exists b1; 
  exists (n1 * d2.+1 - n2 * d1.+1,(d1.+1 * d2.+1).-1)%N.
rewrite -!mulrA -mulr_subr; congr (_ * _).
have F1: (d1.+1 * d2.+1)%:R != 0 :> C by rewrite -neq0N_neqC.
apply: (mulIf F1); apply: sym_equal.
rewrite -mulrA prednK // mulVf // mulr1 natr_sub // !natr_mul.
rewrite mulr_subl mulrA mulfVK -?neq0N_neqC //.
by rewrite [d1.+1%:R * _]mulrC mulrA mulfVK // -neq0N_neqC.
Qed.

Lemma isRatC_addr : forall c1 c2, isRatC c1 -> isRatC (c1 + c2) = isRatC c2.
Proof.
move=> c1 c2 Hc; apply/idP/idP=> HH; last by apply: isRatC_add.
have->: c2 = (-c1) + (c1 + c2) by rewrite addrA addNr add0r.
by apply: isRatC_add; rewrite // isRatC_opp.
Qed.

Lemma isRatC_addl : forall c1 c2, isRatC c2 -> isRatC (c1 + c2) = isRatC c1.
Proof. by move=> c1 c2; rewrite addrC; exact: isRatC_addr. Qed.

Lemma isRatC_inv : forall c, isRatC c^-1 = isRatC c.
Proof.
have F1: forall b, (-1)^+b != 0 :> C.
 move=> b; apply: expf_neq0.
 by apply: (@GRing.Field.intro_unit _ _ (-1)); rewrite mulrNN mul1r.
have F2: forall (b : bool), ((-1)^+b)^-1 = (-1)^+b :> C.
  by case; rewrite !(invrN,invr1).
have F3: forall n, (n.+1)%:R != 0 :> C by move=> n; rewrite -neq0N_neqC.
move=> c; apply/isRatCP/isRatCP=> [] [b [[[|n] d] H]].
- exists true; exists (0,1)%N.
  by move: H; rewrite !(mulr0,mul0r); move/eqP; rewrite invr_eq0; move/eqP.
- exists b; exists (d.+1,n).
  by rewrite -[c]invrK H !invf_mul F2 invrK -!mulrA [_^-1 * _]mulrC.
- exists true; exists (0,1)%N.
  by move: H; rewrite !(mulr0,mul0r); move/eqP; rewrite -invr_eq0; move/eqP.
exists b; exists (d.+1,n); rewrite H.
by rewrite !invf_mul F2 invrK -!mulrA [_^-1 * _]mulrC.
Qed.

Lemma isRatC_mul : forall c1 c2, isRatC c1 -> isRatC c2 -> isRatC (c1 * c2).
Proof.
move=> c1 c2; case/isRatCP=> b1 [[n1 d1] ->]; case/isRatCP=> b2 [[n2 d2] ->].
apply/isRatCP; exists (b1!=b2); exists (n1 * n2,(d1.+1 * d2.+1).-1)%N.
have->: (-1) ^+ (b1 != b2) = (-1) ^+ b1 * (-1) ^+ b2 :> C.
  by case: b1; case: b2; rewrite ?(mulNr,mul1r,opprK).
rewrite !natr_mul prednK // -!mulrA; congr (_ * _).
rewrite [_^+b2 * (n1%:R *_)]mulrC -!mulrA; congr (_ * _).
rewrite natr_mul invf_mul.
by rewrite [_%:R * ( _ * _)]mulrC -!mulrA [d2.+1%:R^-1 * _]mulrC -mulrA.
Qed.

Lemma isRatC_mulr : forall c1 c2, c1 !=0 -> isRatC c1 -> isRatC (c1 * c2) = isRatC c2.
Proof.
move=> c1 c2 Hd Hc; apply/idP/idP=> HH; last by apply: isRatC_mul.
have->: c2 = (c1^-1) * (c1 * c2) by rewrite mulrA mulVf // mul1r.
by apply: isRatC_mul; rewrite // isRatC_inv.
Qed.

Lemma isRatC_mull : forall c1 c2, c2 !=0 -> isRatC c2 -> isRatC (c1 * c2) = isRatC c1.
Proof. by move=> c1 c2; rewrite mulrC; exact: isRatC_mulr. Qed.

Lemma isRatC_conj : forall c, isRatC c -> c^* = c.
Proof.
move=> c; case/isRatCP=> b [[n d]] ->.
by rewrite !rmorphM conjC_inv !conjC_nat rmorph_sign.
Qed.

Lemma isRatC_nat : forall n, isRatC n%:R.
Proof.
move=> n; apply/isRatCP; exists false; exists (n,0)%N.
by rewrite expr0 mul1r invr1 mulr1.
Qed.

Definition isNatC (c : C) : bool :=
 match getRatC c with (b,n,d) => c == (n %/ d.+1)%:R end.

Lemma isNatCP : forall c, reflect (exists n, c = n%:R) (isNatC c).
Proof.
move=> c; apply: (iffP idP)=>[|[n->]].
  by rewrite /isNatC; case getRatC=> [[b n] d]; move/eqP->; 
     exists (n %/ d.+1)%N.
move: (isRatC_nat n); rewrite /isRatC /isNatC; case getRatC=> [[b1 n1] d1].
have Hnd: d1.+1%:R != 0 :> C by rewrite -neq0N_neqC.
case: b1.
  rewrite expr1; move/eqP=> HC.
  have: (n1 + n * d1.+1)%:R == 0 :> C.
    rewrite natr_add natr_mul HC -!mulrA mulVf //.
    by rewrite mulr1 mulN1r subrr.
  rewrite -(eqN_eqC _ 0) addn_eq0.
  by case/andP; move/eqP=> ->; case: {HC}n.
rewrite mul1r;move/eqP=> Hn.
pose m := (n * d1.+1)%N.
have F1: n1%:R = m%:R :> C.
  by rewrite /m natr_mul Hn -mulrA mulVf // mulr1.
suff ->: n1 = m by rewrite mulnK.
case: (leqP n1 m)=> HN.
  suff F2: (m - n1 == 0)%N by rewrite -(subnKC HN) (eqP F2) addn0.
  by rewrite eqN_eqC natr_sub // F1 subrr.
have Hnn := ltnW HN.
have F2: (n1 - m == 0)%N.
  by rewrite eqN_eqC natr_sub // F1 subrr.
by rewrite -(subnKC Hnn) (eqP F2) addn0.
Qed.

Lemma isNatC_isRatC : forall c, isNatC c -> isRatC c.
Proof. move=> c; case/isNatCP=> n ->; exact: isRatC_nat. Qed.

Lemma isNatC_nat : forall n, isNatC (n%:R).
Proof. by move=> n; apply/isNatCP; exists n. Qed.

Lemma isNatC_add: forall c1 c2, isNatC c1 -> isNatC c2 -> isNatC (c1 + c2).
Proof.
move=> c1 c2; case/isNatCP=> n1 ->; case/isNatCP=> n2 ->.
by rewrite -natr_add isNatC_nat.
Qed.

Lemma isNatC_mul : forall c1 c2, isNatC c1 -> isNatC c2 -> isNatC (c1 * c2).
Proof.
move=> c1 c2; case/isNatCP=> n1 ->; case/isNatCP=> n2 ->.
by rewrite -natr_mul isNatC_nat.
Qed.

Lemma isNatC_sum : 
   forall (I : Type) (r : seq I) (P : pred I) (F : I -> C),
   (forall i, P i -> isNatC  (F i)) -> isNatC (\sum_(j <- r | P j) F j).
Proof.
move=> i r P F1 H; elim: r=> [|y r Hrec].
  by rewrite big_nil=> *; exact: (isNatC_nat 0).
rewrite big_cons; case E1: (P _)=> //.
by apply: isNatC_add=> //; exact: H.
Qed.

Lemma isNatCMn : forall x n, isNatC x -> isNatC (x*+n).
Proof.
move=> x; elim=> [|n IH Hx]; first by rewrite mulr0n (isNatC_nat 0).
by rewrite mulrSr isNatC_add // IH.
Qed.

Lemma posC_isNatC : forall c, isNatC c -> 0 <= c.
Proof. by move=> c; case/isNatCP=> n ->; exact: posC_nat. Qed.

Lemma isNatC_conj : forall c, isNatC c -> c^* = c.
Proof. by move=> c; case/isNatCP=> n ->; exact: conjC_nat. Qed.

Lemma isNatC_sum_eq1 : 
   forall (I : eqType) (r : seq I) (P : pred I) (F : I -> C),
   (forall i, P i -> isNatC (F i)) -> uniq r ->
   \sum_(j <- r | P j) F j = 1%:R ->
   (exists i, [/\ i \in r, P i, F i = 1 &
               forall j, j!=i -> j \in r -> P j -> F j = 0]).
Proof.
move=> I r P F HN; elim: r=> [_|y r Hrec].
  by rewrite big_nil; move/eqP; rewrite eq_sym (negPf (nonzero1r _)).
rewrite cons_uniq; case/andP=> [Hyr Hu].
rewrite big_cons; case HP: (P _)=> Hs; last first.
  case: Hrec=> // => i [Hin HPi HFi HF]; exists i; split=> //.
    by rewrite in_cons Hin orbT.
  move=> j Hji; rewrite in_cons; case/orP=> //; last by exact: HF.
  by move/eqP->; rewrite HP.
case/isNatCP: (HN _ (idP HP))=> n Hn.
have: isNatC (\sum_(j <- r | P j) F j) by apply: isNatC_sum.
case/isNatCP=> m Hm.
move: Hs; rewrite Hn Hm -natr_add.
case: n Hn=> [|n Hn]; case: m Hm=>[|m Hm].
- by move=> _ _; move/eqP; rewrite eq_sym (negPf (nonzero1r _)).
- case: m Hm.
    move=> Hs HF _; case: Hrec=> // => j [HInj HPj HFj HF0].
    exists j; split=> //; first by rewrite in_cons HInj orbT.
    move=> k Hk; rewrite in_cons; case/orP; first by move/eqP->.
    by exact: HF0.
  move=> n _ _.
  rewrite -[1%:R]add0r add0n -addn1 natr_add => HH.
  by move/eqP: (addIr HH); rewrite -(eqN_eqC _ 0).
- case: n Hn=> [Hn Hs _|n Hn Hs].
    exists y; split=> //; first by rewrite in_cons eqxx.
    move=> j Hjy; rewrite in_cons; case/orP; first by rewrite (negPf Hjy).
    move=> Hj HPj; apply: (posC_sum_eq0 _ Hs)=> //.
    move=> i; case/andP=> HNI HPI; apply: posC_isNatC; first by exact: HN.
    by rewrite Hj.
  rewrite -[1%:R]add0r addn0 -addn1 natr_add => HH.
  by move/eqP: (addIr HH); rewrite -(eqN_eqC _ 0).
rewrite -[1%:R]add0r addnS -addn1 natr_add => HH.
by move/eqP: (addIr HH); rewrite -(eqN_eqC _ 0).
Qed.

Definition getNatC (c : C) : nat :=
 match getRatC c with (b,n,d) => (n %/ d.+1)%N end.

Lemma getNatCP: forall c, isNatC c = (c == (getNatC c)%:R).
Proof.
move=> c;apply/idP/eqP=>[|->]; last by apply: isNatC_nat.
by rewrite /isNatC /getNatC; case: getRatC=> [[b n]] d; move/eqP.
Qed.

Section Group.

Variable (gT : finGroupType).

Axiom groupC : group_closure_field C gT.

Lemma neq0GC : forall  (G : {group gT}), (#|G|)%:R != 0 :> C.
Proof. by move=> G; rewrite -neq0N_neqC (cardD1 1%g) group1. Qed.

Implicit Type G : {group gT}.
Import GroupScope GRing.Theory.

Lemma pGroupG : forall G, [char C]^'.-group G.
Proof.
by move=> G; apply: sub_pgroup (pgroup_pi G)=> i _; rewrite inE /= Cchar.
Qed.

End Group.