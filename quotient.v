Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice fintype finfun tuple.
Require Import bigops ssralg.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Reserved Notation "\pi_ T" (at level 0, format "\pi_ T").
Reserved Notation "x == y 'mod' T" 
  (at level 70, y at next level, no associativity, format "x  ==  y  'mod'  T").
Reserved Notation "\equiv_ T x y" (at level 2, format "\equiv_ T  x  y").
Reserved Notation "\compat1_ T" (at level 0, format "\compat1_ T").
Reserved Notation "\compat2_ T" (at level 0, format "\compat2_ T").
Reserved Notation "\compatOp1_ T" (at level 0, format "\compatOp1_ T").
Reserved Notation "\compatOp2_ T" (at level 0, format "\compatOp2_ T").


Section Quotient.

Variable T : eqType.

Record quotType := QuotType {
  quot_sort :> Type;
  repr : quot_sort -> T;
  pi : T -> quot_sort;
  _ : forall x : quot_sort, pi (repr x) = x
}.

Variable qT : quotType.
Definition pi_of of phant qT := pi qT.
Notation "\pi_ T" := (@pi_of (Phant T)).

Lemma pi_repr : forall x : qT, pi qT (repr x) = x. 
Proof. by case:qT. Qed.

Definition quot_Sub x (px : repr (pi qT x) == x) := pi qT x.

Lemma reprK : forall x Px, repr (@quot_Sub x Px) = x.
Proof. by move=> x Px; rewrite /quot_Sub (eqP Px). Qed. 

Lemma quot_sortPx : forall x:qT, repr (pi qT (repr x)) == repr x.
Proof. by move=> x; rewrite pi_repr eqxx. Qed.

Lemma quot_sortquot_Sub : forall x:qT, x = quot_Sub (quot_sortPx x).
Proof. by move=> x; apply: (can_inj pi_repr); rewrite reprK. Qed.

Lemma reprP : forall K (_ : forall x Px, K (@quot_Sub x Px)) u, K u.
Proof. by move=> K PK u; rewrite (quot_sortquot_Sub u); apply:PK. Qed.

Canonical Structure quot_subType := SubType _ _ _ reprP reprK.
Definition quot_eqMixin := Eval hnf in [eqMixin of qT by <:].
Canonical Structure quot_eqType := Eval hnf in EqType quot_eqMixin.

Notation "\pi_ T" := (@pi_of (Phant T)).
Notation "x == y 'mod' T" := (\pi_T x == \pi_T y).
Lemma equivP : forall x y, x == y mod qT = (pi qT x == pi qT y).
Proof. by []. Qed.

Canonical Structure equivPred :=  @mkPredType T qT (fun x y => pi _ y == x).

Lemma in_qTE : forall (x:qT) (y:T), y \in x = (pi _ y == x).
Proof. by move=> x y; rewrite -topredE. Qed. 
Lemma in_equiv : forall (x:qT) (y:T), y \in x = ((repr x) == y mod qT).
Proof. by move=> x y; rewrite in_qTE equivP pi_repr eq_sym. Qed.

End Quotient.

Notation "\pi_ T" := (@pi_of _ _ (Phant T)).
Notation "x == y 'mod' T" := (\pi_T x == \pi_T y).




Section Congruence.

Variable T : eqType.
Variable qT : quotType T.

CoInductive compat1 S (op : T -> S) : Type := 
  Compat1 : (forall x:qT, {in x, forall x', op (repr x) = op x'}) -> compat1 op.
Definition compat1_of of phant qT := compat1.
Definition qT_op1 S op (cop : @compat1 S op) x :=  op (@repr T qT x).

Lemma compat1E : forall S (op:T -> S),
  (forall x y,  x == y mod qT -> op x = op y) -> compat1 op.
Proof. 
by move=> ?? Px; constructor; move=> x x'; rewrite in_equiv; move/Px. 
Qed.


CoInductive compat2 S (op : T -> T -> S) : Type :=
  Compat2 : (forall x y:qT, {in x & y, forall x' y',
    op (repr x) (repr y) = op x' y'}) -> compat2 op.
Definition compat2_of of phant qT := compat2.
Definition qT_op2 S op (cop : @compat2 S op) x y :=  
  op (@repr T qT x) (@repr T qT y) .

Lemma compat2E : forall S (op : T -> T -> S),
  (forall x x' y y',  x == x' mod qT -> y == y' mod qT 
    -> op x y = op x' y') -> compat2 op.
Proof. 
move=> S op Pxy; constructor; move=> x x' y y'.
rewrite !in_equiv => ??; exact: Pxy. 
Qed.

Lemma qT_op1E : forall S op cop x, 
  @qT_op1 S op cop (\pi_qT x) = op x.
Proof.
move=> S f [cf] x /=. 
by rewrite -(cf (\pi_qT x)) // in_qTE.
Qed.

Lemma qT_op2E : forall S op cop x y, 
  @qT_op2 S op cop (\pi_qT x) (\pi_qT y) = op x y.
Proof.
move=> S f [cf] x y /=. 
by rewrite -(cf (\pi_qT x) (\pi_qT y)) // in_qTE.
Qed.

Definition qTE := (qT_op1E, qT_op2E).

Lemma quotP : forall P, (forall y:T, P (\pi_qT y)) -> forall x:qT, P x.
Proof.
move=> P Py x. set y := repr x. have -> : x = pi qT y; last exact: Py.
by rewrite /y /=; rewrite pi_repr.
Qed.

Lemma quotPAx : forall P, (forall y:T, (repr (\pi_qT y) = y) 
  -> P (\pi_qT y)) -> forall x:qT, P x.
Proof.
move=> P Py x. set y := repr x. have -> : x = pi qT y.
   by rewrite /y /= pi_repr.
by apply: Py; rewrite /y /= /pi_of pi_repr.
Qed.
 

End Congruence.
Notation "\compat1_ T" := (compat1_of (Phant T)).
Notation "\compat2_ T" := (compat2_of (Phant T)).
(* Notation "\compatOp1_ T" := (compatOp1_of (Phant T)). *)
(* Notation "\compatOp2_ T" := (compatOp2_of (Phant T)). *)


Section cartesianSquare.
Variable R : choiceType.

Definition cartesianSquare := (R * R)%type.

Definition csquare_to_tuple (x : cartesianSquare) := [tuple x.1; x.2].
Definition tuple_to_csquare (t: 2.-tuple R) :=  ([tnth t 0], [tnth t 1]).

Lemma csquare_tupleK : cancel csquare_to_tuple tuple_to_csquare.
Proof. by elim. Qed.

Definition csquareEqMixin := CanEqMixin csquare_tupleK.
(* Canonical Structure csquareEqType := Eval hnf in EqType csquareEqMixin. *)
Canonical Structure csquareEqType := Eval hnf in [eqType of cartesianSquare].
Definition csquareChoiceMixin := CanChoiceMixin csquare_tupleK.
Canonical Structure csquareChoiceType := Eval hnf in ChoiceType csquareChoiceMixin.

Identity Coercion csquareToProd : cartesianSquare >-> prod.

Definition csquare_of of phant R := cartesianSquare.
Identity Coercion type_csquare_of : csquare_of >-> cartesianSquare.

Notation "{ 'csquare' T }" := (csquare_of (Phant T)) (at level 0, format "{ 'csquare'  T }").
Canonical Structure csquareEqType' := Eval hnf in [eqType of {csquare R}].
Canonical Structure csquareChoiceType' := Eval hnf in [choiceType of {csquare R}].

End cartesianSquare.
Notation "{ 'csquare' T }" := (csquare_of (Phant T)) (at level 0, format "{ 'csquare'  T }").

Section Relatives. (* to be moved *)

Definition axiom (z : {csquare nat}) := (z.1 == 0) || (z.2 == 0).
Definition relative := { z | axiom z}.
Definition Relative z (pz : axiom z) : relative := @exist _ axiom _ pz.

Lemma one_diff_eq0 : forall x y, ((x-y) == 0) || ((y-x) == 0).
Proof.
move=> x y. case : (leqP x y); first by rewrite /leq=> ->.
by move/ltnW; rewrite /leq=> ->; rewrite orbT.
Qed.

Definition canon (x : {csquare nat}) :=  
  @Relative ((x.1-x.2),(x.2-x.1)) (one_diff_eq0 _ _).

Lemma canon_valK : forall x, canon (val x)  = x.
Proof.
move=> [[n m] /= p]. apply: val_inj=> /=. move: p.
by rewrite /axiom /=; case/orP; move/eqP->; rewrite subn0.
Qed.


Canonical Structure relative_quotType := Eval hnf in
  @QuotType _ relative [eta val] [eta canon] canon_valK.

Definition relP := @quotP _ relative_quotType.
Definition relPAx := @quotPAx _ relative_quotType.
Definition inRelP := insubP [subType of relative].

Lemma relPN : forall P:(relative -> Prop), (forall x, P (\pi_relative (x,0)))
  -> (forall x, P (\pi_relative (0,x))) -> forall x, P x.
Proof.
move=> P Ppos Pneg. elim/relPAx=> x <- /=.
case/orP:(one_diff_eq0 x.1 x.2); move/eqP->; [exact:Pneg|exact:Ppos].
Qed.

Notation SubRel := (@Sub _ _ [subType of relative]).

Print Canonical Projections.

Definition equivz (x y : {csquare nat}) := x.1 + y.2 == y.1 + x.2.
Lemma equivzP : forall x y, x == y mod relative = equivz x y.
Proof.
move=> x y. rewrite /equivz /= /canon -(inj_eq val_inj) /=.
apply/eqP/eqP=> [[]|Pxy]; last first.
   congr (_,_); rewrite -(subn_add2r y.2) Pxy addnC.
      by rewrite (subn_add2l x.2).
   by rewrite (subn_add2r x.2).
case:(ltnP x.1 x.2); first move/ltnW; move=>Px; move:(Px); 
     rewrite /leq; move/eqP->.
  move/eqP. rewrite eq_sym subn_eq0 =>Py. 
  move/eqP. rewrite -(inj_eq (@addnI y.1)) subnKC //. move/eqP<-.
  by rewrite addnA addnAC subnKC // addnC.
move=> P1. move/eqP. rewrite eq_sym subn_eq0 =>Py. move:P1.
move/eqP. rewrite -(inj_eq (@addnI x.2)) subnKC //. move/eqP->.
by rewrite addnAC -addnA subnKC // addnC.
Qed.

Definition zeroz := \pi_relative (0,0).
Definition onez := \pi_relative (1,0).
Definition natz n := \pi_relative (n,0).

Definition preaddz (x y : {csquare nat}) : {csquare nat} := 
  (x.1 + y.1 , x.2 + y.2).

Lemma addz_compat : \compat2_relative _ (fun x y => \pi_relative (preaddz x y)).
Proof.
apply:compat2E=> x y x' y'. 
rewrite !equivzP /equivz. move/eqP=>Px. move/eqP=>Py.
apply/eqP. rewrite equivzP /=. apply/eqP.
rewrite addnAC addnA Px -!addnA /=. congr (_+_).
symmetry. rewrite addnA addnAC -Py addnC. congr(_+_).
by rewrite addnC.
Qed.

Notation addz := (qT_op2 addz_compat).

Definition preoppz (x : {csquare nat}) : {csquare nat} := (x.2 , x.1).
Lemma oppz_compat : \compat1_relative _ (\pi_relative \o preoppz).
Proof.
apply:compat1E=> x x'. rewrite !equivzP /equivz. move/eqP=>Px.
apply/eqP. rewrite equivzP /equivz /=. 
by rewrite addnC -Px addnC eqxx.
Qed.
Notation oppz := (qT_op1 oppz_compat).


Definition mulz_sub : forall x y : relative, 
  axiom ((val x).1 * (val y).1 + (val x).2 * (val y).2, 
    (val x).1 * (val y).2 + (val x).2 * (val y).1).
Proof. Admitted.

Definition mulz x y := (SubRel _ (mulz_sub x y)).

Lemma addzA : associative addz.
Proof.
elim/relP=>x. elim/relP=>y. elim/relP=>z.
rewrite !qTE. congr pi. rewrite /preaddz /=.
by congr (_,_); rewrite addnA.
Qed.


Lemma addzC : commutative addz.
Proof. 
elim/relP=>x. elim/relP=>y.
by rewrite !qTE /preaddz; congr pi; congr (_,_); rewrite addnC.
Qed.


Lemma add0z: left_id zeroz addz.
Proof. by elim/relP=> x; rewrite !qTE. Qed.


Lemma addzN : left_inverse zeroz oppz addz.
Proof.
elim/relP=>x. rewrite !qTE. apply/eqP. rewrite equivzP /equivz /=.
by rewrite add0n addn0 /= addnC.
Qed.


Definition z_zmodMixin :=  ZmodMixin addzA addzC add0z addzN.
Canonical Structure z_zmodType := Eval hnf in ZmodType z_zmodMixin.


Lemma mulzA : associative mulz.
Proof.
(*elim/relPN=>x; elim/relPN=>y; elim/relPN=>z; rewrite /=.*)
move=> [[x1 x2] Px] [[y1 y2] Py] [[z1 z2] Pz].
apply:val_inj=> /=.
case/orP:Px=>/=; move/eqP->;
case/orP:Py=>/=; move/eqP->;
case/orP:Pz=>/=; move/eqP->;
rewrite !(mul0n, muln0, add0n, addn0, mulnA);
congr(_,_).
Qed.

Lemma mulzC : commutative mulz.
Proof. 
move=> [[x1 x2] Px] [[y1 y2] Py].
apply:val_inj=> /=.
case/orP:Px=>/=; move/eqP->;
case/orP:Py=>/=; move/eqP->;
rewrite !(mul0n, muln0, add0n, addn0) mulnC;
congr(_,_).
Qed.


Lemma mul1z : left_id onez mulz.
Proof.
move=> [[x1 x2] Px].
apply:val_inj=> /=. 
case/orP:Px=>/=; move/eqP->; 
rewrite !(mul0n, muln0, add0n, addn0, subn0, mul1n); congr (_,_).
Qed.

Lemma mulz_addl : left_distributive mulz addz.
Proof.
elim/relP=>x. elim/relP=>y. elim/relP=>z.
Admitted.

Lemma nonzero1z : onez != 0%R.
Proof. Admitted.

Definition z_comRingMixin := ComRingMixin mulzA mulzC mul1z mulz_addl nonzero1z.
Canonical Structure  z_Ring := Eval hnf in RingType z_comRingMixin.
Canonical Structure z_comRing := Eval hnf in ComRingType mulzC.





