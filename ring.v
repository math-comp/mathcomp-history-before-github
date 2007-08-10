Require Import ssreflect eqtype fintype funs ssrnat ssrbool.
Require Import groups group_perm signperm indexed_products.
Require Import algebraic_struct.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
(*
Module RingClass.

Structure ring_class : Type := RingClass {
  element :> eqType;
  zero : element;
  one : element;
  opp : element -> element;
  plus : element -> element -> element;
  mult : element -> element -> element
}.
End RingClass.
Notation ring_class := RingClass.ring_class.
Notation RingClass := RingClass.RingClass.

Coercion ring2groups_plus_cls (r : ring_class) :=
  (GroupsClass (@RingClass.zero r) (@RingClass.opp r)
  (@RingClass.plus r)).

Coercion ring2monoid_mult_cls (r : ring_class) :=
  (MonoidClass (@RingClass.one r) (@RingClass.mult r)).

*)
Section RingAxioms.
(* Ring *)

Structure is_ring (R : eqType) (z o : R) (opp : R->R)
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
  forall (R : eqType) (z o : R) (opp : R->R) (plus mult : R->R->R),
    is_ring z o opp plus mult -> is_monoid o mult.
Proof. move=> R z o opp plus mult; by case. Qed.

Structure is_commutative_ring (R : eqType) (z o : R) (opp : R->R)
  (plus mult : R->R->R) : Prop := {
  com_is_ringP_ :> (is_ring z o opp plus mult);
  multC_ : opC mult
}.
(* --- *)

End RingAxioms.

Module Ring.

Structure ring : Type := Ring {
  element :> eqType;
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
  forall x1 x2 x3 : R, x3 * (x1 + x2) = (x3 * x1) + (x3 * x2).
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

Coercion R_of_nat n := if n is S n' then RofSn n' else 0.

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

Section RingIndexedProd.
Open Scope ring_scope.

Variable R: ring.

Lemma isum_id : forall (d : finType) (r : set d) (x :R),
  @iprod R _ r (fun _=>x) = (@R_of_nat R (card r)) * x.
Proof.
move=> d r x; elim: {r}_.+1 {-2}r (ltnSn (card r)) => // n IHn r.
case: (pickP r) => [i ri | r0 _]; 
  last (rewrite iprod_set0_ //= ?eq_card0 ?mult_r0l//).
rewrite (cardD1 i) (@iprodD1_ R _ i _ (fun _: d => x)) ri //=; 
move/IHn=> -> {n IHn}; rewrite RofSnE.
by rewrite plus_mult_r mult_r1l plus_rC.
Qed.

Variable cR :com_ring.

Lemma iprod_id :  forall (d : finType) (r : set d) (x : cR),
  @iprod (r2m cR) d r (fun _ : d=> x) = x ^ card r.
Proof.
move=> d r x; elim: {r}_.+1 {-2}r (ltnSn (card r)) => // n IHn r.
case: (pickP r) => [i ri | r0 _]; last by (rewrite iprod_set0_ ?eq_card0).
rewrite (cardD1 i) (@iprodD1_ (cr2am cR) _ i _ (fun _: d => x)) ri //=.
by move/IHn=> -> {n IHn}; rewrite RexpSnE mult_rC.
Qed.

Lemma iprod_opp : forall (d : finType) (r : set d) F,
  @iprod (r2m cR) _ r (fun i => - (F i)) =
  (-1) ^ card r * @iprod (r2m cR) _ r (fun i=> F i).
Proof.
move=> d r F; rewrite -iprod_id -(@iprod_mult_ (cr2am cR)).
by apply: eq_iprod_f_=> i _//; rewrite -mult_opp_rl mult_r1l.
Qed.


End RingIndexedProd.

Unset Implicit Arguments.

