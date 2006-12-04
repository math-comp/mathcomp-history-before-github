(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import funs.
Require Export Bool.

Set Implicit Arguments.
Unset Strict Implicit.

(*   Lemmas for boolean connectives, (crucially) including reflection. *)
(*   In the following NEGATION is taken as the standard form of a      *)
(* false condition : hypotheses should be of the form (negb b) rather  *)
(* than b = false or ~b, as much as possible.                          *)
(*   A few lemmas to facilitate the manipulation of large conditionals *)
(* conclude this file.                                                 *)

(* Negation lemmas. *)

Delimit Scope bool_scope with B.
Notation "'~~' b" := (negb b) (at level 35, format "~~  b") : bool_scope.

Lemma negbI : forall b, b = false -> ~~ b. Proof. by case. Qed.
Lemma negbE : forall b, ~~ b -> b = false. Proof. by case. Qed.
Lemma negbIf : forall b : bool, b -> ~~ b = false. Proof. by case. Qed.
Lemma negbEf : forall b, ~~ b = false -> b. Proof. by case. Qed.
Lemma negbK : involutive negb.  Proof. by case. Qed.
Lemma negbE2 : forall b, ~~ (~~ b) -> b.  Proof. by case. Qed.

(* Prenex notations for wider connectives; WARNING: they associate to the   *)
(* right, because this is the natural orientation in most of the proof.     *)
(* This avoids bending backwards to adhere to the left-associative v8 infix *)
(* binary notation.                                                         *)

Inductive and3 (P Q R : Prop) : Prop :=
  And3 (_ : P) (_ : Q) (_ : R).

Notation "'and3b' b1 b2 b3" := (b1 && (b2 && b3))
  (at level 10, b1, b2, b3 at level 8).

Inductive and4 (P Q R S : Prop) : Prop :=
  And4 (_ : P) (_ : Q) (_ : R) (_ : S).

Notation "'and4b' b1 b2 b3 b4" := (b1 && (b2 && (b3 && b4)))
  (at level 10, b1, b2, b3, b4 at level 8).

Inductive and5 (P Q R S T : Prop) : Prop :=
  And5 (_ : P) (_ : Q) (_ : R) (_ : S) (_ : T).

Notation "'and5b' b1 b2 b3 b4 b5" := (b1 && (b2 && (b3 && (b4 && b5))))
  (at level 10, b1, b2, b3, b4, b5 at level 8).

Inductive or3 (P Q R : Prop) : Prop :=
  Or3_1 (_ : P) |  Or3_2 (_ : Q) |  Or3_3 (_ : R).

Notation "'or3b' b1 b2 b3" := (b1 || (b2 || b3))
  (at level 10, b1, b2, b3 at level 8).

Inductive or4 (P Q R S : Prop) : Prop :=
  Or4_1 (_ : P) |  Or4_2 (_ : Q) |  Or4_3 (_ : R) | Or4_4 (_ : S).

Notation "'or4b' b1 b2 b3 b4" := (b1 || (b2 || (b3 || b4)))
  (at level 10, b1, b2, b3, b4 at level 8).

Section ReflectConnectives.

Variable b1 b2 b3 b4 b5 : bool.

Lemma idP : reflect b1 b1.
Proof. by case b1; constructor. Defined.

Lemma idPn : reflect (~~ b1) (~~ b1).
Proof. by case b1; constructor. Qed.

Lemma negP : reflect (~ b1) (~~ b1).
Proof. by case b1; constructor; auto. Qed.

Lemma negPn : reflect b1 (~~ (~~ b1)).
Proof. by case b1; constructor. Qed.

Lemma negPf : reflect (b1 = false) (~~ b1).
Proof. by case b1; constructor. Qed.

Lemma andP : reflect (b1 /\ b2) (b1 && b2).
Proof. by case b1; case b2; constructor=> //; case. Qed.

Lemma and3P : reflect (and3 b1 b2 b3) (and3b b1 b2 b3).
Proof. by case b1; case b2; case b3; constructor; try by case. Qed.

Lemma and4P : reflect (and4 b1 b2 b3 b4) (and4b b1 b2 b3 b4).
Proof.
by case b1; case b2; case b3; case b4; constructor; try by case. Qed.

Lemma and5P : reflect (and5 b1 b2 b3 b4 b5) (and5b b1 b2 b3 b4 b5).
Proof.
by case b1; case b2; case b3; case b4; case b5; constructor; try by case.
Qed.

Lemma orP : reflect (b1 \/ b2) (b1 || b2).
Proof. by case b1; case b2; constructor; auto; case. Qed.

Lemma or3P : reflect (or3 b1 b2 b3) (or3b b1 b2 b3).
Proof.
case b1; first by constructor; constructor 1.
case b2; first by constructor; constructor 2.
case b3; first by constructor; constructor 3.
by constructor; case.
Qed.

Lemma or4P : reflect (or4 b1 b2 b3 b4) (or4b b1 b2 b3 b4).
Proof.
case b1; first by constructor; constructor 1.
case b2; first by constructor; constructor 2.
case b3; first by constructor; constructor 3.
case b4; first by constructor; constructor 4.
by constructor; case.
Qed.

Lemma nandP : reflect (~~ b1 \/ ~~ b2) (~~ (b1 && b2)).
Proof. case b1; case b2; constructor; auto; case; auto. Qed.

Lemma norP : reflect (~~ b1 /\ ~~ b2) (~~ (b1 || b2)).
Proof. case b1; case b2; constructor; auto; case; auto. Qed.

End ReflectConnectives.

Implicit Arguments idP [b1].
Implicit Arguments idPn [b1].
Implicit Arguments negP [b1].
Implicit Arguments negPn [b1].
Implicit Arguments negPf [b1].
Implicit Arguments andP [b1 b2].
Implicit Arguments and3P [b1 b2 b3].
Implicit Arguments and4P [b1 b2 b3 b4].
Implicit Arguments and5P [b1 b2 b3 b4 b5].
Implicit Arguments orP [b1 b2].
Implicit Arguments or3P [b1 b2 b3].
Implicit Arguments or4P [b1 b2 b3 b4].
Implicit Arguments nandP [b1 b2].
Implicit Arguments norP [b1 b2].
Prenex Implicits idP idPn negP negPn negPf.
Prenex Implicits andP and3P and4P and5P orP or3P or4P nandP norP.

(* Shorter, more systematic names for the boolean connectives laws.       *)

Lemma andTb : forall b, true && b = b.      Proof. done. Qed.
Lemma andFb : forall b, false && b = false. Proof. done. Qed.
Lemma andbT : forall b, b && true = b.      Proof. by case. Qed.
Lemma andbF : forall b, b && false = false. Proof. by case. Qed.
Lemma andbb : forall b, b && b = b.         Proof. by case. Qed.

Lemma andbC : forall b1 b2, b1 && b2 = b2 && b1. Proof. by do 2 case. Qed.

Lemma andbA : forall b1 b2 b3, and3b b1 b2 b3 = b1 && b2 && b3.
Proof. by do 3 case. Qed.

Lemma andbCA : forall b1 b2 b3, and3b b1 b2 b3 = and3b b2 b1 b3.
Proof. by do 3 case. Qed.

Lemma orTb : forall b, true || b = true. Proof. done. Qed.
Lemma orFb : forall b, false || b = b.   Proof. done. Qed.
Lemma orbT : forall b, b || true = true. Proof. by case. Qed.
Lemma orbF : forall b, b || false = b.   Proof. by case. Qed.
Lemma orbb : forall b, b || b = b.       Proof. by case. Qed.

Lemma orbC : forall b1 b2, b1 || b2 = b2 || b1.
Proof. by do 2 case. Qed.

Lemma orbA : forall b1 b2 b3, or3b b1 b2 b3 = b1 || b2 || b3.
Proof. by do 3 case. Qed.

Lemma orbCA : forall b1 b2 b3, or3b b1 b2 b3 = or3b b2 b1 b3.
Proof. by do 3 case. Qed.

(* Finally, an alternative to xorb that behaves somewhat better wrt Simpl. *)

Definition addb (b : bool) : bool -> bool := if b then negb else fun b' => b'.
Notation "b1 '(+)' b2" := (addb b1 b2)
  (at level 50, format "b1  '(+)'  b2") : bool_scope.

Lemma addTb : forall b, true (+) b = ~~ b. Proof. done. Qed.
Lemma addFb : forall b, false (+) b = b. Proof. done. Qed.
Lemma addNb : forall b1 b2, ~~ b1 (+) b2 = ~~ (b1 (+) b2). Proof. by do 2 case. Qed.
Lemma addbT : forall b, b (+) true = ~~ b. Proof. by case. Qed.
Lemma addbF : forall b, b (+) false = b. Proof. by case. Qed.
Lemma addbN : forall b1 b2, b1 (+) ~~ b2 = ~~ (b1 (+) b2). Proof. by do 2 case. Qed.
Lemma addbb : forall b, b (+) b = false. Proof. by case. Qed.

Lemma addbC : forall b1 b2, b1 (+) b2 = b2 (+) b1.
Proof. by do 2 case. Qed.

Lemma addbA : forall b1 b2 b3, b1 (+) (b2 (+) b3) = b1 (+) b2 (+) b3.
Proof. by do 3 case. Qed.

Lemma addbCA : forall b1 b2 b3, b1 (+) (b2 (+) b3) = b2 (+) (b1 (+) b3).
Proof. by do 3 case. Qed.

Lemma addbK : forall b1, involutive (addb b1).
Proof. by do 2 case. Qed.

Lemma addKb : forall b2, involutive (fun b1 => b1 (+) b2).
Proof. by do 2 case. Qed.

Lemma addbP : forall b1 b2, b1 (+) b2 -> ~~ b1 = b2.
Proof. by do 2 case. Qed.

(* Resolution tactic for blindly weeding out common terms from boolean       *)
(* equalities. When faced with a goal of the form (andb/orb/addb b1 b2) = b2 *)
(* they will try to locate b1 in b2 and remove it. This can fail!            *)

Ltac bool_congr :=
  match goal with
  | |- (?X1 && ?X2 = ?X3) => first
  [ symmetry; rewrite -1?(andbC X1) -?(andbCA X1); congr 1 (andb X1); symmetry
  | case X1; [ rewrite ?andTb ?andbT | by rewrite /= ?andbF ] ]
  | |- (?X1 || ?X2 = ?X3) => first
  [ symmetry; rewrite -1?(orbC X1) -?(orbCA X1); congr 1 (orb X1); symmetry
  | case X1; [ by rewrite /= ?orbT | rewrite ?orFb ?orbF ] ]
  | |- (?X1 (+) ?X2 = ?X3) =>
    symmetry; rewrite -1?(addbC X1) -?(addbCA X1); congr 1 (addb X1); symmetry
  | |- (~~ ?X1 = ?X2) => congr 1 negb
  end.

(* The following lemmas are mainly useful for ifs with large conditions : *)
(* they allow reasoning about the condition without repeating it inside   *)
(* the proof (the latter IS preferable when the condition is short).      *)
(* Usage :                                                                *)
(*   if the goal contains (if cond then ...) = ...                        *)
(*     case: ifP => Hcond.                                                *)
(*   generates two subgoal, with the assumption Hcond : cond = true/false *)
(*     Rewrite if_same  eliminates redundant ifs                          *)
(*     Rewrite (fun_if f) moves a function f inside an if                 *)
(*     Rewrite if_arg moves an argument inside a function-valued if       *)

CoInductive if_spec (A : Type) (b : bool) (vT vF : A) : A -> bool -> Set :=
  | IfSpecTrue : b -> if_spec b vT vF vT true
  | IfSpecFalse : b = false -> if_spec b vT vF vF false.

Lemma ifP : forall A (b : bool) (vT vF : A),
  if_spec b vT vF (if b then vT else vF) b.
Proof. by move=> A [|]; constructor. Qed.

Lemma if_same : forall A (b : bool) (v : A), (if b then v else v) = v.
Proof. by move=> A [|]. Qed.

Lemma fun_if : forall A B (f : A -> B) (b : bool) v1 v2,
  f (if b then v1 else v2) = (if b then f v1 else f v2).
Proof. by move=> A B f [|]. Qed.

Lemma if_arg : forall A x B (b : bool) (f1 f2 : A -> B),
  (if b then f1 else f2) x = (if b then f1 x else f2 x).
Proof. by move=> A x B [|]. Qed.

Unset Implicit Arguments.