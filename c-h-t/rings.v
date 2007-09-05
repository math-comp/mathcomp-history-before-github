Add LoadPath "../".
Require Import ssreflect eqtype fintype funs ssrnat ssrbool tuple.
Require Import groups group_perm signperm indexed_products.
Require Import algebraic_struct.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section RingAxioms.
(* Ring *)

Structure is_ring (R : Type) (z o : R) (opp : R->R)
  (plus mult : R->R->R) : Prop := {
  ring_is_groups_plusP_ :> (is_abelian_groups z opp plus);
  ring_is_monoid_multP_ :> (is_monoid o mult);
  plus_mult_l_ : forall x1 x2 x3, 
    mult x1 (plus x2 x3) = plus (mult x1 x2) (mult x1 x3);
  plus_mult_r_ : forall x1 x2 x3, 
    mult (plus x1 x2) x3 = plus (mult x1 x3) (mult x2 x3);
  one_diff_zero_ : o <> z  (* Non trivial ring *)
}.

Lemma is_monoid_ring_mult : 
  forall (R : Type) (z o : R) (opp : R->R) (plus mult : R->R->R),
    is_ring z o opp plus mult -> is_monoid o mult.
Proof. move=> R z o opp plus mult; by case. Qed.

Structure is_commutative_ring (R : Type) (z o : R) (opp : R->R)
  (plus mult : R->R->R) : Prop := {
  com_is_ringP_ :> (is_ring z o opp plus mult);
  multC_ : opC mult
}.
(* --- *)

End RingAxioms.

Module Ring.

Structure ring : Type := Ring {
  element :> Type;
  zero : element;
  one : element;
  opp : element -> element;
  plus : element -> element -> element;
  mult : element -> element -> element;
  ringP :> is_ring zero one opp plus mult
}.
End Ring.
Notation ring := Ring.ring.
Notation Ring := Ring.Ring.
Coercion Ring : is_ring >-> ring.

Module CommutativeRing.

Structure commutative_ring : Type := CommutativeRing {
  element :> ring;
  multC_ : opC (@Ring.mult element)
}.
End CommutativeRing.
Notation com_ring := CommutativeRing.commutative_ring.
Notation ComRing := CommutativeRing.CommutativeRing.

(*
Definition Ring_element (R : Ring.ring) : Type := (Ring.element R).

Definition r2r_ (R : ring) : (Ring.element R) -> (Ring_element R).
move=> R x; exact x.
Defined.

Coercion r2r_ : Ring.element >-> Ring_element.
*)

Definition r2m (R : ring) : monoid :=
  Monoid (ring_is_monoid_multP_ (@Ring.ringP R)).

Coercion r2m : ring >-> monoid.

(*
Definition r2g_p (R : ring ) : 
  (Ring.element R) -> (Groups.element R).
move=> G x; exact x.
Defined.
Definition r2m_m (R : ring ) : 
  (Ring.element R) -> (Monoid.element (r2m R)).
move=> G x; exact x.
Defined.
*)

Definition r2ag (R : ring ) : ab_groups :=
  @AbGroups (Groups (ring_is_groups_plusP_ (@Ring.ringP R))) 
    (plusC_ (@Ring.ringP R)).

Coercion r2ag : ring >-> ab_groups.

Definition cr2am (R : com_ring ) : ab_monoid :=
  @AbMonoid (r2m R) (@CommutativeRing.multC_ R).

Coercion cr2am : com_ring >-> ab_monoid.

Delimit Scope ring_scope with R.
Bind Scope ring_scope with Ring.element.

Notation "0" := (Ring.zero _) (at level 0): ring_scope.
Notation "1" := (Ring.one _) (at level 0): ring_scope.
Notation "- x" := (Ring.opp x): ring_scope.
Infix "+" := Ring.plus: ring_scope.
Infix "*" := Ring.mult: ring_scope.

Section RingsProp.
Open Scope ring_scope.

Variable (R : ring).

Lemma plus_rA : forall x1 x2 x3 : R, x1 + (x2 + x3) = x1 + x2 + x3.
Proof. by apply: (@plus_gA R). Qed.

Lemma plus_rC : forall x1 x2 : R, x1 + x2 = x2 + x1.
Proof. by apply: (@plus_gC (r2ag R)). Qed.

Lemma plus_r0l: forall x : R, 0 + x = x.
Proof. by apply: (@plus_g0l R). Qed.

Lemma plus_r0r: forall x : R, x + 0 = x.
Proof. by apply: (@plus_g0r R). Qed.

Lemma plus_opp_rl : forall x : R, - x + x = 0.
Proof. by apply: (@plus_opp_gl R). Qed.

Lemma plus_opp_rr : forall x : R, x + - x = 0.
Proof. by apply: (@plus_opp_gr R). Qed.

Notation plus_r := Ring.plus.
Lemma plus_rK : forall x : R, cancel (plus_r x) (plus_r (- x)).
Proof. by apply: (@plus_gKl R). Qed.

Lemma plus_r_inj : forall x : R, injective (plus_r x).
Proof. move=> x; exact: can_inj (plus_rK x). Qed.

Implicit Arguments plus_r_inj [].

Lemma opp_r0 : -0 = 0 :> R.
Proof. by apply: (@opp_g0 R). Qed.

Notation opp_r := Ring.opp.
Lemma opp_rK : cancel (@opp_r R) (@opp_r R).
Proof. by apply: (@opp_gK R). Qed.

Lemma opp_r_inj : injective (@opp_r R).
Proof. exact: can_inj opp_rK. Qed.

Lemma opp_plus_r : forall x1 x2 : R, - (x1 + x2) = - x1 + - x2. 
Proof.
by move=> x1 x2; rewrite plus_rC; apply: (@opp_plus_g R).
Qed.

Lemma opp_plus_r_eq : forall (x1 x2 : R), x1 + x2 = 0 -> x1 = -x2.
Proof. 
by move=> x1 x2 H; apply: (plus_r_inj x2); rewrite plus_opp_rr plus_rC.
Qed.

(* Multiplication *)
Lemma mult_rA: 
  forall x1 x2 x3 : R, x1 * (x2 * x3) = x1 * x2 * x3.
Proof. by apply (@m_op_A (r2m R)). Qed.

Lemma mult_r1l: forall x : R, 1 * x = x.
Proof. by apply: (@m_op_unitl (r2m R)). Qed.

Lemma mult_r1r : forall x : R, x * 1 = x.
Proof. by apply: (@m_op_unitr (r2m R)). Qed.

Lemma plus_mult_l:
  forall x1 x2 x3 : R, x1 * (x2 + x3) = (x1 * x2) + (x1 * x3).
Proof. by case: R=> elt z o opp p m; case. Qed.

Lemma plus_mult_r:
  forall x1 x2 x3 : R, (x1 + x2) * x3 = (x1 * x3) + (x2 * x3).
Proof. by case: R=> elt z o opp p m; case. Qed.

Lemma one_diff_0 : 1 <> 0 :> R.
Proof. by case: R=>elt z o opp p m; case. Qed.

Lemma mult_r0r: forall x : R, x * 0 = 0.
Proof.
move => x; move: (@plus_r_inj x (x*0) 0) => ->//.
by rewrite -{1}[x]mult_r1r  -plus_mult_l 
  plus_rC plus_r0l mult_r1r plus_rC plus_r0l.
Qed.

Lemma mult_r0l: forall x : R, 0 * x = 0.
Proof.
move => x; move: (@plus_r_inj x (0*x) 0) => ->//.
by rewrite -{1}[x]mult_r1l 
 -plus_mult_r plus_rC plus_r0l mult_r1l plus_rC plus_r0l.
Qed.

Lemma mult_opp_rl: forall x y : R, (- (x * y)) = (- x) * y.
Proof.
move => x y.
by rewrite -[-x*y]plus_r0l -(plus_opp_rl (x*y))
  -plus_rA -plus_mult_r [x+_]plus_rC 
   plus_opp_rl mult_r0l plus_rC plus_r0l.
Qed.

Lemma mult_opp_rr: forall x y : R, (-(x * y)) = x * (- y).
Proof.
move => x y.
by rewrite -[x*-y]plus_r0l -(plus_opp_rl (x*y))
  -plus_rA -plus_mult_l [y+_]plus_rC
   plus_opp_rl mult_r0r plus_rC plus_r0l.
Qed.

Lemma plus_rCA : forall x1 x2 x3 : R, x1 + (x2 + x3) = x2 + (x1 + x3).
Proof. move=> *; rewrite !plus_rA; congr (_ + _); exact: plus_rC. Qed.

Variable cR : com_ring.

Lemma mult_rC : forall x1 x2 : cR, x1 * x2 = x2 * x1.
Proof. by case: cR. Qed.

Lemma mult_rCA : forall x1 x2 x3 : cR, x1 * (x2 * x3) = x2 * (x1 * x3).
Proof.
by move=> *; rewrite !(@m_op_A (r2m cR))//=; congr (_ * _);
  exact: mult_rC.
Qed.

End RingsProp.

Section InjectingNat.
Open Scope ring_scope.

Variable (R : ring).

(* Injecting natural integers. *)

Definition RofSn n := iter n (fun x : R => x + 1) 1.

Definition R_of_nat n := if n is S n' then RofSn n' else 0.

Coercion Local R_of_nat : nat >-> Ring.element.

Notation "'n2r'" := (R_of_nat) (at level 0) : ring_scope.

Lemma RofSnE : forall n, RofSn n = n + 1 :> R.
Proof. by elim=> /= [|_ -> //]; rewrite plus_r0l. Qed.

Lemma Raddn : forall m n, (m + n)%N = m + n :> R.
Proof.
move=> m n; elim: m => /= [|m IHm]; first by rewrite plus_r0l.
by rewrite !RofSnE IHm plus_rC plus_rCA plus_rA.
Qed.

Lemma Rsubn : forall m n, m >= n -> (m - n)%N = m + - n :> R.
Proof.
move=> m n; move/leq_add_sub=> Dm.
by rewrite -{2}Dm Raddn -plus_rA plus_rCA plus_opp_rr plus_rC plus_r0l.
Qed.

Lemma Rmuln : forall m n, (m * n)%N = m * n :> R.
Proof.
move=> m n; elim: m => /= [|m IHm]; first by rewrite mult_r0l.
by rewrite Raddn RofSnE IHm plus_mult_r mult_r1l plus_rC.
Qed.

End InjectingNat.

Section IntPow.
Open Scope ring_scope.

Variable (R : ring).

(* Integer powers. *)

Definition RexpSn x n := iter n (fun y : R => y * x) x.

Definition Rexp_nat x n := if n is S n' then RexpSn x n' else 1.

End IntPow.
Notation "x ^ n" := (Rexp_nat x n).

Section IntPowProp.
Open Scope ring_scope.

Lemma RexpSnE : forall (R : ring) x n, RexpSn x n = x ^ n * x :> R.
Proof. by move=> R x; elim=> /= [|_ -> //]; rewrite mult_r1l. Qed.

Lemma exp1n : forall (R : ring) n, 1 ^ n = 1 :> R.
Proof. by move=> R; elim=> //= n IHn; rewrite RexpSnE IHn mult_r1l. Qed.

Lemma exp0n : forall (R : ring) n, 0 < n -> 0 ^ n = 0 :> R.
Proof. by move=> R [|[|n]] //= _; rewrite mult_r0r. Qed.

Lemma Rexpn : forall (R : ring) m n, (m ^ n)%N = m ^ n :> R.
Proof. by move=> R m; elim=> //= n IHn; rewrite Rmuln RexpSnE IHn. Qed.

Lemma sign_addb : forall (R : ring) b1 b2,
  (-1) ^ (b1 (+) b2) = (-1) ^ b1 * (-1) ^ b2 :> R.
Proof.
move=> R.
do 2!case; rewrite //= ?(@mult_opp_rl (-1) _) ?mult_r1l ?mult_r1r//.
by rewrite -mult_opp_rl -mult_opp_rr opp_rK mult_r1l.
Qed.

Lemma sign_permM : forall (R : ring) d (s t : permType d),
  (-1) ^ odd_perm (s * t)%G = (-1) ^ s * (-1) ^ t :> R.
Proof. by move=> *; rewrite odd_permM sign_addb. Qed.

Variable cR : com_ring.

Lemma mult_exp : forall x1 x2 n, (x1 * x2) ^ n = x1 ^ n * x2 ^ n :> cR.
Proof.
move=> x1 x2; elim=> //= [|n IHn]; first by rewrite mult_r1l.
by rewrite !RexpSnE IHn -!mult_rA (mult_rCA x1).
Qed.

Lemma exp_addn : forall x n1 n2, x ^ (n1 + n2) = x ^ n1 * x ^ n2 :> cR.
Proof.
move=> x n1 n2; elim: n1 => /= [|n1 IHn]; first by rewrite mult_r1l.
by rewrite !RexpSnE IHn mult_rC mult_rCA mult_rA.
Qed.

Lemma exp_muln : forall x n1 n2, x ^ (n1 * n2) = (x ^ n1) ^ n2 :> cR.
Proof.
move=> x n1 n2; rewrite mulnC; elim: n2 => //= n2 IHn.
by rewrite !RexpSnE exp_addn IHn mult_rC.
Qed.

Lemma sign_odd : forall n, (-1) ^ odd n = (-1) ^ n :> cR.
Proof.
move=> n; rewrite -{2}[n]odd_double_half addnC double_mul2 exp_addn exp_muln.
rewrite //= ?(@mult_opp_rl (-1) _) ?mult_r1l ?mult_r1r//.
by rewrite -mult_opp_rl -mult_opp_rr opp_rK mult_r1l exp1n mult_r1l.
Qed.

End IntPowProp.

Section ComRingIndexedProd.
Open Scope ring_scope.

(* Instantiating the "indexed product" lemmas for ring. *)

Section RingIndexedProd.
Variable R: ring.

Notation "'\sum_' ( 'in' r ) F" := (@iprod R _ r F)
   (at level 40, F at level 40,
   format "'\sum_' ( 'in'  r )  F") : local_scope.
Notation "'\prod_' ( 'in' r ) F" := (@iprod (r2m R) _ r F)
   (at level 35, F at level 35,
   format "'\prod_' ( 'in'  r )  F") : local_scope.

Notation "'\sum_' () F" := (@iprod R _ (setA _) F)
   (at level 40, F at level 40, format "'\sum_' ()  F") : local_scope.
Notation "'\prod_' () F" := (@iprod (r2m R) _ (setA _) F)
   (at level 35, F at level 35, format "'\prod_' () F") : local_scope.

Notation "'\sum_' ( i 'in' r ) E" := (@iprod R _ r (fun i => E))
   (at level 40, E at level 40, i at level 50,
    format "'\sum_' ( i  'in'  r )  E") : local_scope.
Notation "'\prod_' ( i 'in' r ) E" := (@iprod (r2m R) _ r (fun i => E))
   (at level 35, E at level 35, i at level 50,
    format "'\prod_' ( i  'in'  r )  E") : local_scope.

Notation "'\sum_' ( i : t 'in' r ) E" := (@iprod R _ r (fun i : t => E))
   (at level 40, E at level 40, i at level 50, only parsing) : local_scope.
Notation "'\prod_' ( i : t 'in' r ) E" := (@iprod (r2m R) _ r (fun i : t => E))
   (at level 35, E at level 35, i at level 50, only parsing) : local_scope.

Notation "'\sum_' ( i | P ) E" := (@iprod R _ (fun i => P) (fun i => E))
   (at level 40, E at level 40, i at level 50, 
   format "'\sum_' ( i  |  P )  E") : local_scope.
Notation "'\prod_' ( i | P ) E" := (@iprod (r2m R) _ (fun i => P) (fun i => E))
   (at level 35, E at level 35, i at level 50,
   format "'\prod_' ( i  |  P )  E") : local_scope.

Notation "'\sum_' ( i : t | P ) E" :=
   (@iprod R _ (fun i : t => P) (fun i : t => E))
   (at level 40, E at level 40, i at level 50, only parsing) : local_scope.
Notation "'\prod_' ( i : t | P ) E" :=
   (@iprod (r2m R) _ (fun i : t => P) (fun i : t => E))
   (at level 35, E at level 35, i at level 50, only parsing) : local_scope.

Notation "'\sum_' ( i ) E" := (@iprod R _ (setA _) (fun i => E))
   (at level 40, E at level 40, i at level 50,
   format "'\sum_' ( i )  E") : local_scope.
Notation "'\prod_' ( i ) E" := (@iprod (r2m R) _ (setA _) (fun i => E))
   (at level 35, E at level 35, i at level 50 ,
   format "'\prod_' ( i )  E") : local_scope.

Notation "'\sum_' ( i : t ) E" := (@iprod R _ (setA _) (fun i : t => E))
   (at level 40, E at level 40, i at level 50, only parsing) : local_scope.
Notation "'\prod_' ( i : t ) E" := (@iprod (r2m R) _ (setA _) (fun i : t => E))
   (at level 35, E at level 35, i at level 50, only parsing) : local_scope.

Notation "'\sum_' ( i < n ) E" := (@iprod R _ (setA _) (fun i : I_(n) => E))
   (at level 40, E at level 40, i, n at level 50, only parsing) : local_scope.
Notation "'\prod_' ( i < n ) E" := (@iprod (r2m R) _ (setA _) (fun i : I_(n) => E))
   (at level 35, E at level 35, i, n at level 50, only parsing) : local_scope.
Open Scope local_scope.

Lemma eq_isum : forall (d : finType) (r r' : set d) F F',
  r =1 r' -> dfequal r F F' -> \sum_(in r) F = \sum_(in r') F'.
Proof. exact: eq_iprod_. Qed.

Lemma eq_iprod : forall (d : finType) (r r' : set d) F F',
  r =1 r' -> dfequal r F F' -> \prod_(in r) F = \prod_(in r') F'.
Proof. exact: eq_iprod_. Qed.

Lemma eq_isumL : forall (d : finType) (r r' : set d) F,
  r =1 r' -> \sum_(in r) F = \sum_(in r') F.
Proof. exact: eq_iprod_set_. Qed.

Lemma eq_isumR : forall (d : finType) (r : set d) F F',
   dfequal r F F' -> \sum_(in r) F = \sum_(in r) F'.
Proof. exact: eq_iprod_f_. Qed.

Lemma eq_iprodL : forall (d : finType) (r r' : set d) F,
  r =1 r' -> \prod_(in r) F = \prod_(in r') F.
Proof. exact: eq_iprod_set_. Qed.

Lemma eq_iprodR : forall (d : finType) (r : set d) F F',
   dfequal r F F' -> \prod_(in r) F = \prod_(in r) F'.
Proof. exact: eq_iprod_f_. Qed.

(* Renormalizing notations that the pretty-printer doesn't recognize. *)

Lemma isum_eta : forall (d : finType) r F,
  \sum_(in r) F = \sum_(i : d | r i) F i.
Proof. exact: iprod_eta_. Qed.

Lemma isum_etaA : forall (d : finType) F, \sum_() F = \sum_(i : d) F i.
Proof. exact: iprod_etaA_. Qed.
 
Lemma iprod_eta : forall (d : finType) r F,
  \prod_(in r) F = \prod_(i : d | r i) F i.
Proof. exact: iprod_eta_. Qed.

Lemma iprod_etaA : forall (d : finType) F, \prod_() F = \prod_(i : d) F i.
Proof. exact: iprod_etaA_. Qed.

Lemma isum_set0_eq : forall (d : finType) (F : d -> R), \sum_(in set0) F = 0.
Proof. move=> *; exact: iprod_set0_eq_. Qed.

Lemma isum_set0 : forall (d : finType) (r : set d) F,
  r =1 set0 -> \sum_(in r) F = 0.
Proof. by move=> *; apply: iprod_set0_. Qed.

Lemma iprod_set0_eq : forall (d : finType) (F : d -> R), \prod_(in set0) F = 1.
Proof. move=> *; exact: iprod_set0_eq_. Qed.

Lemma iprod_set0 : forall (d : finType) (r : set d) F,
  r =1 set0 -> \prod_(in r) F = 1.
Proof. by move=> *; apply: iprod_set0_. Qed.

Lemma isum_set1_eq : forall (d : finType) (i0 : d) F,
  \sum_(in set1 i0) F = F i0.
Proof. move=> *; exact: iprod_set1_eq_. Qed.

Lemma isum_set1 : forall (d : finType) i0 (r : set d) F,
  r =1 set1 i0 -> \sum_(in r) F = F i0.
Proof. move=> *; exact: iprod_set1_. Qed.

Lemma iprod_set1_eq : forall (d : finType) (i0 : d) F,
  \prod_(in set1 i0) F = F i0.
Proof. move=> *; exact: iprod_set1_eq_. Qed.

Lemma iprod_set1 : forall (d : finType) i (r : set d) F,
  r =1 set1 i -> \prod_(in r) F = F i.
Proof. move=> *; exact: iprod_set1_. Qed.

Lemma isumD1 : forall (d : finType) i0 (r : set d) F,
  r i0 -> \sum_(in r) F = F i0 + \sum_(i | (i0 != i) && r i) F i.
Proof. move=> *; exact: (@iprodD1_ R). Qed.

Lemma isumID : forall (d : finType) c r F,
  \sum_(in r) F = \sum_(i : d | r i && c i) F i + \sum_(i | r i && ~~ c i) F i.
Proof. move=> *; exact: (@iprodID_ R). Qed.

Lemma isum0_eq : forall (d : finType) (r : set d),
  \sum_(in r) (fun _ => 0) = 0.
Proof. move=> *; exact: iprod_f1_eq_. Qed.

Lemma isum0 : forall (d : finType) (r : set d) F,
  dfequal r F (fun _ => 0) -> \sum_(in r) F = 0.
Proof. move=> *; exact: iprod_f1_. Qed.

Lemma iprod1_eq : forall (d : finType) (r : set d),
  \prod_(in r) (fun _ => 1) = 1.
Proof. move=> *; exact: iprod_f1_eq_. Qed.

Lemma iprod1 : forall (d : finType) (r : set d) F,
  dfequal r F (fun _ => 1) -> \prod_(in r) F = 1.
Proof. move=> *; exact: iprod_f1_. Qed.

Lemma isum_plus : forall (d : finType) (r : set d) F1 F2,
  \sum_(i in r) (F1 i + F2 i) = \sum_(i in r) F1 i + \sum_(i in r) F2 i.
Proof. by move=> *; apply: (@iprod_mult_ R). Qed.

Lemma isum_distrR : forall (d : finType) x (r : set d) F,
  (\sum_(in r) F) * x = \sum_(i in r) F i * x.
Proof.
move=> *; rewrite -(@i_prod_distr_ R) //=;
  [exact: plus_mult_r|exact: mult_r0l].
Qed.

Lemma isum_distrL : forall (d : finType) x (r : set d) F,
  x * (\sum_(in r) F) = \sum_(i in r) x * F i.
Proof.
move=> *; rewrite -(@i_prod_distl_ R) //=;
  [exact: plus_mult_l | exact: mult_r0r].
Qed.

Lemma isum_opp : forall (d : finType) (r : set d) F,
  \sum_(i in r) - F i = - (\sum_(i in r) F i).
Proof.
move=> *; apply: (@iprod_distf_ R) => //=;
  [exact: opp_r0 | exact: opp_plus_r].
Qed.

Lemma isum_id : forall (d : finType) (r : set d) x,
  \sum_(i in r) x = (R_of_nat R (card r)) * x.
Proof.
move=> d r x; elim: {r}_.+1 {-2}r (ltnSn (card r)) => // n IHn r.
case: (pickP r) => [i ri | r0 _]; last by rewrite isum_set0 ?eq_card0 // mult_r0l.
rewrite (cardD1 i) (@isumD1 _ i) ri //=; move/IHn=> -> {n IHn}; rewrite RofSnE.
by rewrite plus_mult_r mult_r1l plus_rC.
Qed.

Lemma reindex_isum_onto : forall (d d' : finType) (h : d' -> d) h' r F,
    dcancel r h' h -> 
  \sum_(in r) F = \sum_(i | (h' (h i) == i) && r (h i)) F (h i).
Proof. exact: (@reindex_iprod_onto_ R). Qed.

Lemma reindex_isum : forall (d d' : finType) (h : d' -> d) r F,
  ibijective r h -> \sum_(in r) F = \sum_(i | r (h i)) F (h i).
Proof. exact: (@reindex_iprod_ R). Qed.

Lemma partition_isum : forall (d d': finType) (pr : set d) p (r : set d') F,
  (forall j, r j -> pr (p j)) ->
  \sum_(in r) F = \sum_(i in pr) \sum_(j | r j && (p j == i)) F j.
Proof. exact: (@partition_iprod_ R). Qed.

Lemma pair_isum_dep : forall (d d': finType) r r' (F : d -> d' -> R),
  \sum_(i in r) \sum_(in r' i) F i
    = \sum_(u | r (fst u) && r' (fst u) (snd u)) F (fst u) (snd u).
Proof. exact: (@pair_iprod_dep_ R). Qed.

Lemma pair_isum : forall (d d': finType) r r' (F : d -> d' -> R),
  \sum_(i in r) \sum_(in r') F i =
    \sum_(u | r (fst u) && r' (snd u)) F (fst u) (snd u).
Proof. exact: (@pair_iprod_ R). Qed.

Lemma pair_isumA : forall (d d': finType) (F : d -> d' -> R),
  \sum_(i) \sum_() F i = \sum_(u) F (fst u) (snd u).
Proof. exact: (@pair_iprodA_ R). Qed.

Lemma exchange_isum_dep :
  forall (d d' : finType) (r : set d) (r' : d -> set d') (xr : set d') F,
    (forall i j, r i -> r' i j -> xr j) ->
  \sum_(i in r) \sum_(in r' i) F i =
    \sum_(j in xr) \sum_(i | r i && r' i j) F i j.
Proof. exact: (@exchange_iprod_dep_ R). Qed.

Lemma exchange_isum : forall (d d': finType) r r' (F : d -> d' -> R),
  \sum_(i in r) \sum_(in r') F i = \sum_(j in r') \sum_(i in r) F i j.
Proof. exact: (@exchange_iprod_ R). Qed.

End RingIndexedProd.

(* Prop for commutative ring *)
Variable cR :com_ring.

Notation "'\sum_' ( 'in' r ) F" := (@iprod cR _ r F)
   (at level 40, F at level 40,
   format "'\sum_' ( 'in'  r )  F") : local_scope.
Notation "'\prod_' ( 'in' r ) F" := (@iprod (r2m cR) _ r F)
   (at level 35, F at level 35,
   format "'\prod_' ( 'in'  r )  F") : local_scope.

Notation "'\sum_' () F" := (@iprod cR _ (setA _) F)
   (at level 40, F at level 40, format "'\sum_' ()  F") : local_scope.
Notation "'\prod_' () F" := (@iprod (r2m cR) _ (setA _) F)
   (at level 35, F at level 35, format "'\prod_' () F") : local_scope.

Notation "'\sum_' ( i 'in' r ) E" := (@iprod cR _ r (fun i => E))
   (at level 40, E at level 40, i at level 50,
    format "'\sum_' ( i  'in'  r )  E") : local_scope.
Notation "'\prod_' ( i 'in' r ) E" := (@iprod (r2m cR) _ r (fun i => E))
   (at level 35, E at level 35, i at level 50,
    format "'\prod_' ( i  'in'  r )  E") : local_scope.

Notation "'\sum_' ( i : t 'in' r ) E" := (@iprod cR _ r (fun i : t => E))
   (at level 40, E at level 40, i at level 50, only parsing) : local_scope.
Notation "'\prod_' ( i : t 'in' r ) E" := (@iprod (r2m cR) _ r (fun i : t => E))
   (at level 35, E at level 35, i at level 50, only parsing) : local_scope.

Notation "'\sum_' ( i | P ) E" := (@iprod cR _ (fun i => P) (fun i => E))
   (at level 40, E at level 40, i at level 50, 
   format "'\sum_' ( i  |  P )  E") : local_scope.
Notation "'\prod_' ( i | P ) E" := (@iprod (r2m cR) _ (fun i => P) (fun i => E))
   (at level 35, E at level 35, i at level 50,
   format "'\prod_' ( i  |  P )  E") : local_scope.

Notation "'\sum_' ( i : t | P ) E" :=
   (@iprod cR _ (fun i : t => P) (fun i : t => E))
   (at level 40, E at level 40, i at level 50, only parsing) : local_scope.
Notation "'\prod_' ( i : t | P ) E" :=
   (@iprod (r2m cR) _ (fun i : t => P) (fun i : t => E))
   (at level 35, E at level 35, i at level 50, only parsing) : local_scope.

Notation "'\sum_' ( i ) E" := (@iprod cR _ (setA _) (fun i => E))
   (at level 40, E at level 40, i at level 50,
   format "'\sum_' ( i )  E") : local_scope.
Notation "'\prod_' ( i ) E" := (@iprod (r2m cR) _ (setA _) (fun i => E))
   (at level 35, E at level 35, i at level 50 ,
   format "'\prod_' ( i )  E") : local_scope.

Notation "'\sum_' ( i : t ) E" := (@iprod cR _ (setA _) (fun i : t => E))
   (at level 40, E at level 40, i at level 50, only parsing) : local_scope.
Notation "'\prod_' ( i : t ) E" := (@iprod (r2m cR) _ (setA _) (fun i : t => E))
   (at level 35, E at level 35, i at level 50, only parsing) : local_scope.

Notation "'\sum_' ( i < n ) E" := (@iprod cR _ (setA _) (fun i : I_(n) => E))
   (at level 40, E at level 40, i, n at level 50, only parsing) : local_scope.
Notation "'\prod_' ( i < n ) E" := (@iprod (r2m cR) _ (setA _) (fun i : I_(n) => E))
   (at level 35, E at level 35, i, n at level 50, only parsing) : local_scope.
Open Scope local_scope.

Lemma iprodD1 : forall (d : finType) i0 (r : set d) F,
  r i0 -> \prod_(in r) F = F i0 * \prod_(i | (i0 != i) && r i) F i.
Proof. move=> *; exact: (@iprodD1_ (cr2am cR)). Qed.

Lemma iprodID : forall (d : finType) c r F,
  \prod_(in r) F =
    \prod_(i : d | r i && c i) F i * \prod_(i | r i && ~~ c i) F i.
Proof. move=> *; exact: (@iprodID_ (cr2am cR)). Qed.

Lemma iprod_mult : forall (d : finType) (r : set d) F1 F2,
  \prod_(i in r) (F1 i * F2 i) = \prod_(i in r) F1 i * \prod_(i in r) F2 i.
Proof. exact: (@iprod_mult_ (cr2am cR)). Qed.

Lemma iprod_id :  forall (d : finType) (r : set d) (x : cR),
  \prod_(i in r) x = x ^ card r.
Proof.
move=> d r x; elim: {r}_.+1 {-2}r (ltnSn (card r)) => // n IHn r.
case: (pickP r) => [i ri | r0 _]; last by (rewrite iprod_set0 ?eq_card0).
rewrite (cardD1 i) (@iprodD1 _ i _ (fun _: d => x)) ri //=.
by move/IHn=> -> {n IHn}; rewrite RexpSnE mult_rC.
Qed.

Lemma iprod_opp : forall (d : finType) (r : set d) F,
  \prod_(i in r) - F i = (-1) ^ card r * \prod_(i in r) F i.
Proof.
move=> d r F; rewrite -iprod_id -(@iprod_mult_ (cr2am cR)).
by apply: eq_iprod_f_=> i _//; rewrite -mult_opp_rl mult_r1l.
Qed.

Lemma reindex_iprod_onto : forall (d d' : finType) (h : d' -> d) h' r F,
    dcancel r h' h -> 
  \prod_(in r) F = \prod_(i | (h' (h i) == i) && r (h i)) F (h i).
Proof. exact: (@reindex_iprod_onto_ (cr2am cR)). Qed.

Lemma reindex_iprod : forall (d d' : finType) (h : d' -> d) r F,
  ibijective r h -> \prod_(in r) F = \prod_(i | r (h i)) F (h i).
Proof. exact: (@reindex_iprod_ (cr2am cR)). Qed.

Lemma distr_iprod_isum_dep :
  forall (d d': finType) j0 (r : set d) (r' : d -> set d') F,
  \prod_(i in r) (\sum_(in r' i) F i) =
     \sum_(f in pfamily j0 r r') \prod_(i in r) F i (fun_of_fgraph f i).
Proof.
move=> d d' j0 r r' F; pose df := fgraphType d d'.
elim: {r}_.+1 {-2}r (ltnSn (card r)) => // m IHm r.
case: (pickP r) => [i1 ri1 | r0 _]; last first.
  rewrite (@isum_set1 _ _ (fgraph_of_fun (fun _ => j0))) ?iprod_set0 // => f.
  apply/familyP/eqP=> [Df|<-{f} i]; last by rewrite r0 g2f set11.
  by apply/fgraphP=> i; move/(_ i): Df; rewrite r0 g2f; move/eqP.
rewrite ltnS (cardD1 i1) ri1 (@iprodD1 _ i1) /setD1 //; move/IHm=> {m IHm} IH.
rewrite isum_distrR 
  (@partition_isum _ _ _ (r' i1) (fun f : df => f i1)); last first.
  by move=> f; move/familyP; move/(_ i1); rewrite ri1.
apply: eq_isum => // j1 r'j1; rewrite {}IH isum_distrL.
pose seti1 j (f : df) := fgraph_of_fun (fun i => if i1 == i then j else f i).
symmetry.
rewrite (@reindex_isum_onto _ _ _ (seti1 j1) (seti1 j0))=> [|f]; last first.
  case/andP=> _; move/eqP=> fi1; apply/fgraphP=> i.
  by rewrite !g2f; case: eqP => // <-.
apply: eq_isum => [f | f _].
  rewrite g2f !set11 andbT; apply/andP/familyP=> [|r'f]; [case | split].
  - move/eqP=> fi1; move/familyP=> r'f j; move/(_ j): r'f; rewrite g2f.
    by case: eqP => //= <- _; rewrite -fi1 !g2f !set11.
  - apply/eqP; apply/fgraphP=> j; move/(_ j): r'f; rewrite !g2f.
    by case: eqP=> //= <-; move/eqP.
  apply/familyP=> j; move/(_ j): r'f; rewrite !g2f.
  by case: eqP=> //= <- _; rewrite ri1.
rewrite (@iprodD1 _ i1) // g2f set11; congr (_ * _); apply: eq_iprodR => i.
by rewrite g2f; case: eqP.
Qed.

Lemma distr_iprod_isum : forall (d d' : finType) j0 r r' (F : d -> d' -> cR),
  \prod_(i in r) (\sum_(in r') F i) =
     \sum_(f in pfunspace j0 r r') \prod_(i in r) F i (fun_of_fgraph f i).
Proof. move=> *; exact: distr_iprod_isum_dep. Qed.

Lemma distr_iprodA_isum_dep : forall (d d': finType) (r' : d -> set d') F,
  \prod_(i) (\sum_(in r' i) F i) =
  \sum_(f in family r') \prod_(i) F i (fun_of_fgraph f i).
Proof.
move=> d d' r' F; case: (pickP (setA d')) => [j0 _ | d'0].
  exact: (distr_iprod_isum_dep j0).
have d's0: (_ : set d') =1 set0 by move=> ? j; have:= d'0 j.
case: (pickP (setA d)) => [i0 _ | d0].
  rewrite (@iprodD1 _ i0) // isum_set0 // mult_r0l isum_set0 // => f.
  by apply/familyP; move/(_ i0); rewrite d's0.
have f0: d -> d' by move=> i; have:= d0 i.
rewrite iprod_set0 // (@isum_set1 _ _ (fgraph_of_fun f0)) ?iprod_set0 // => f.
apply/familyP/eqP=> _; last by move=> i; have:= d0 i.
by apply/fgraphP=> j; have:= d0 j.
Qed.

Lemma distr_iprodA_isum : forall (d d': finType) (r' : set d') F,
  \prod_(i : d) (\sum_(in r') F i) =
    \sum_(f in tfunspace r') \prod_(i) F i (fun_of_fgraph f i).
Proof. move=> *; exact: distr_iprodA_isum_dep. Qed.

Lemma distr_iprodA_isumA : forall (d d': finType) F,
  \prod_(i) (\sum_() F i) = \sum_(f : fgraphType d d') \prod_(i) F i (f i).
Proof.
move=> *; rewrite distr_iprodA_isum; apply: eq_isumL => f; exact/tfunspaceP.
Qed.

End ComRingIndexedProd.


Unset Implicit Arguments.

