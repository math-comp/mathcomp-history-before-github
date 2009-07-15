Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import choice fintype finfun tuple.
Require Import bigops ssralg.

Require Import quotient.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Module Relatives. (* to be moved *)

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

Definition relW := @quotW _ relative_quotType.
Definition relP := @quotP _ relative_quotType.
Definition inRelP := insubP [subType of relative].

Lemma relPN : forall P:(relative -> Prop), (forall x, P (\pi_relative (x,0)))
  -> (forall x, P (\pi_relative (0,x))) -> forall x, P x.
Proof.
move=> P Ppos Pneg. elim/relP=> x <- /=.
case/orP:(one_diff_eq0 x.1 x.2); move/eqP->; [exact:Pneg|exact:Ppos].
Qed.

Notation SubRel := (@Sub _ _ [subType of relative]).

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

Notation zeroz := (\pi_relative (0,0)).
Notation onez := (\pi_relative (1,0)).
Notation natz n := (\pi_relative (n,0)).

Lemma addz_compat : \compat2_relative _ 
  (fun x y => \pi_relative (x.1 + y.1 , x.2 + y.2)).
Proof.
apply:compat2E=> x y x' y'. 
rewrite !equivzP /equivz. move/eqP=>Px. move/eqP=>Py.
apply/eqP. rewrite equivzP /=. apply/eqP.
rewrite addnAC addnA Px -!addnA /=. congr (_+_).
symmetry. rewrite addnA addnAC -Py addnC. congr(_+_).
by rewrite addnC.
Qed.
Notation addz := (qT_op2 addz_compat).

Lemma oppz_compat : \compat1_relative _ 
  (fun x => \pi_relative (x.2 , x.1)).
Proof.
apply:compat1E=> x x'. rewrite !equivzP /equivz. move/eqP=>Px.
apply/eqP. rewrite equivzP /equivz /=. 
by rewrite addnC -Px addnC eqxx.
Qed.
Notation oppz := (qT_op1 oppz_compat).

Lemma mulz_compat : \compat2_relative _ (fun x y => \pi_relative 
    (x.1 * y.1 + x.2 * y.2 , x.1 * y.2 + x.2 * y.1)).
Proof.
apply:Compat2. elim/relPN=> x; elim/relPN=> y; move=> x' y';
rewrite !in_qTE /pi_of !equivzP /equivz; move/eqP=>Px; move/eqP=>Py;
apply/eqP; rewrite equivzP /=; apply/eqP;
rewrite !(sub0n, subn0, mul0n, muln0, add0n, addn0) /= in Px Py *.
  * rewrite Px Py. ring.
  * rewrite Px -Py. ring.
  * rewrite -Px Py. ring.
  * rewrite -Px -Py. ring.
Qed.  
Notation mulz := (qT_op2 mulz_compat).

Lemma addzA : associative addz.
Proof.
elim/relW=>x. elim/relW=>y. elim/relW=>z.
rewrite !qTE. congr pi. rewrite /=.
by congr (_,_); rewrite addnA.
Qed.


Lemma addzC : commutative addz.
Proof. 
elim/relW=>x. elim/relW=>y.
by rewrite !qTE; congr pi; congr (_,_); rewrite addnC.
Qed.


Lemma add0z: left_id zeroz addz.
Proof. by elim/relW=> x; rewrite !qTE. Qed.


Lemma addzN : left_inverse zeroz oppz addz.
Proof.
elim/relW=>x. rewrite !qTE. apply/eqP. rewrite equivzP /equivz /=.
by rewrite add0n addn0 /= addnC.
Qed.


Definition z_zmodMixin :=  ZmodMixin addzA addzC add0z addzN.
Canonical Structure z_zmodType := Eval hnf in ZmodType z_zmodMixin.


Lemma mulzA : associative mulz.
Proof.
elim/relPN=>x; elim/relPN=>y; elim/relPN=>z; rewrite !qTE;
apply/eqP; rewrite equivzP /equivz /=;
by rewrite !sub0n !subn0 !mul0n ! muln0 !add0n !addn0 ?mulnA eqxx.
Qed.

Lemma mulzC : commutative mulz.
Proof. 
elim/relW=>x; elim/relW=>y. rewrite !qTE.
apply/eqP; rewrite equivzP /equivz /=. apply/eqP.
by congr (_+_+_); rewrite mulnC // addnC mulnC; congr (_+_).
Qed.


Lemma mul1z : left_id onez mulz.
Proof.
elim/relPN=>x; rewrite !qTE; apply/eqP; rewrite equivzP /equivz /=; 
by rewrite !(mul0n, muln0, add0n, addn0, mul1n) eqxx.
Qed.


Lemma mulz_addl : left_distributive mulz addz.
Proof.
elim/relPN=>x; elim/relPN=>y; elim/relPN=>z;
rewrite !qTE; apply/eqP; rewrite equivzP /equivz /=;
rewrite !sub0n !subn0 !mul0n ! muln0 !add0n ?addn0 ?muln_addl ?muln_addr;
by rewrite eqxx.
Qed.

Lemma nonzero1z : onez != zeroz.
Proof. by rewrite -(inj_eq val_inj) /=. Qed.


Definition z_comRingMixin := ComRingMixin mulzA mulzC mul1z mulz_addl nonzero1z.
Canonical Structure  z_Ring := Eval hnf in RingType z_comRingMixin.
Canonical Structure z_comRing := Eval hnf in ComRingType mulzC.


Definition unitz := [pred x : relative | ((repr x).1)+((repr x).2) == 1 ].
Definition invz (x : relative) : relative := x.
Notation natmz n := (\pi_relative (0,n)).


Lemma mulVz : {in unitz, left_inverse 1%R invz *%R}.
Proof.
elim/relPN=>x; rewrite /invz; rewrite in_simpl /= sub0n subn0 (add0n,addn0);
by move/eqP=> -> /=; apply:val_inj=>/=; congr(_,_).
Qed.


Lemma unitzPl : forall x y, mulz y x = onez -> unitz x.
Proof.
elim/relPN=>x; elim/relPN=>y; move/eqP; rewrite !qTE -(inj_eq val_inj) /=; 
rewrite !muln0 !mul0n !add0n ?addn0 !sub0n !subn0 //; 
by case/eqP; move/eqP; rewrite eqn_mul1; case/andP.
Qed.

Lemma  invz_out : {in predC unitz, invz =1 id}.
Proof. exact. Qed.

Definition z_comUnitRingMixin :=  ComUnitRingMixin mulVz unitzPl invz_out.
Canonical Structure z_comUnitRing := Eval hnf in ComUnitRingType z_comUnitRingMixin.

Lemma idomain_axiomz : forall x y, 
  (mulz x y = zeroz -> (x == zeroz) || (y == zeroz)).
Proof.
elim/relPN=>x; elim/relPN=>y; move/eqP; rewrite !qTE -!(inj_eq val_inj) /=;
rewrite !muln0 !mul0n !add0n ?addn0 !sub0n !subn0 //;
case/eqP; move/eqP; rewrite muln_eq0; case/orP; move/eqP->; 
by rewrite eqxx (orbT,orTb).
Qed.

Canonical Structure z_iDomain := Eval hnf in IdomainType idomain_axiomz. 

End Relatives.


