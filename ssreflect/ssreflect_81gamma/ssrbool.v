(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import funs.
Require Export Bool.

Set Implicit Arguments.
Unset Strict Implicit.

(*   Lemmas for boolean connectives, (crucially) including reflection. *)
(*   In the following NEGATION is taken as the standard form of a      *)
(* false condition : hypotheses should be of the form ~~ b rather      *)
(* than b = false or ~ b, as much as possible.                         *)
(*   A few lemmas to facilitate the manipulation of large conditionals *)
(* conclude this file.                                                 *)

(* Coercion bool >-> Prop.                    *)

Coercion is_true b := b = true.

Ltac fold_prop := match goal with |- (?b = true) => change (is_true b) end.

Lemma prop_congr : forall b b' : bool, b = b' -> b = b' :> Prop.
Proof. by move=> b b' ->. Qed.

Ltac prop_congr := apply: prop_congr.

(* Lemmas for auto. *)
Lemma is_true_true : true. Proof. done. Qed.
Lemma not_false_is_true : ~ false. Proof. done. Qed.
Lemma is_true_locked_true : locked true. Proof. by unlock. Qed.
Hint Resolve is_true_true not_false_is_true is_true_locked_true.

(* Negation lemmas. *)

Delimit Scope bool_scope with B.
Notation "'~~' b" := (negb b) (at level 35, format "~~  b") : bool_scope.

Lemma negbT : forall b, b = false -> ~~ b. Proof. by case. Qed.
Lemma negbET : forall b, ~~ b -> b = false. Proof. by case. Qed.
Lemma negbF : forall b : bool, b -> ~~ b = false. Proof. by case. Qed.
Lemma negbEF : forall b, ~~ b = false -> b. Proof. by case. Qed.
Lemma negbK : involutive negb.  Proof. by case. Qed.
Lemma negbE2 : forall b, ~~ (~~ b) -> b.  Proof. by case. Qed.

(* Lemmas for ifs with large conditions, which allow reasoning about the  *)
(* condition without repeating it inside the proof (the latter IS         *)
(* preferable when the condition is short).                               *)
(* Usage :                                                                *)
(*   if the goal contains (if cond then ...) = ...                        *)
(*     case: ifP => Hcond.                                                *)
(*   generates two subgoal, with the assumption Hcond : cond = true/false *)
(*     Rewrite if_same  eliminates redundant ifs                          *)
(*     Rewrite (fun_if f) moves a function f inside an if                 *)
(*     Rewrite if_arg moves an argument inside a function-valued if       *)

Section BoolIf.

Variables (A B : Type) (x : A) (f : A -> B) (b : bool) (vT vF : A).

CoInductive if_spec : A -> bool -> Set :=
  | IfSpecTrue : b -> if_spec vT true
  | IfSpecFalse : b = false -> if_spec vF false.

Lemma ifP : if_spec (if b then vT else vF) b.
Proof. by case Db: b; constructor. Qed.

Lemma if_same : (if b then vT else vT) = vT.
Proof. by case b. Qed.

Lemma if_neg : (if ~~ b then vT else vF) = if b then vF else vT.
Proof. by case b. Qed.

Lemma fun_if : f (if b then vT else vF) = if b then f vT else f vF.
Proof. by case b. Qed.

Lemma if_arg : forall fT fF : A -> B,
  (if b then fT else fF) x = if b then fT x else fF x.
Proof. by case b. Qed.

End BoolIf.

(* The reflection predicate.                                          *)

Inductive reflect (P : Prop) : bool -> Set :=
  | Reflect_true : P -> reflect P true
  | Reflect_false : ~ P -> reflect P false.

(* Core (internal) reflection lemmas, used for the three kinds of views. *)

Section ReflectCore.

Variables (P Q : Prop) (b c : bool).

Hypothesis Hb : reflect P b.

Lemma introNTF : (if c then ~ P else P) -> negb b = c.
Proof. by case c; case Hb. Qed.

Lemma introTF : (if c then P else ~ P) -> b = c.
Proof. by case c; case Hb. Qed.

Lemma elimNTF : negb b = c -> if c then ~ P else P.
Proof. by move <-; case Hb. Qed.

Lemma elimTF : b = c -> if c then P else ~ P.
Proof. by move <-; case Hb. Qed.

Lemma equivPif : (Q -> P) -> (P -> Q) -> if b then Q else ~ Q.
Proof. by case Hb; auto. Qed.

Lemma xorPif : Q \/ P -> ~ (Q /\ P) -> if b then ~ Q else Q.
Proof. by case Hb => [? _ H ? | ? H _]; case: H. Qed.

End ReflectCore.

(* Internal negated reflection lemmas *)
Section ReflectNegCore.

Variables (P Q : Prop) (b c : bool).
Hypothesis Hb : reflect P (negb b).

Lemma introTFn : (if c then ~ P else P) -> b = c.
Proof. by move/(introNTF Hb) <-; case b. Qed.

Lemma elimTFn : b = c -> if c then ~ P else P.
Proof. by move <-; apply: (elimNTF Hb); case b. Qed.

Lemma equivPifn : (Q -> P) -> (P -> Q) -> if b then ~ Q else Q.
Proof. rewrite -if_neg; exact: equivPif. Qed.

Lemma xorPifn : Q \/ P -> ~ (Q /\ P) -> if b then Q else ~ Q.
Proof. rewrite -if_neg; exact: xorPif. Qed.

End ReflectNegCore.

(* User-oriented reflection lemmas *)
(* We still can't use the view feature here, because the ML implementation *)
(* of views refers to this file.                                           *)
Section Reflect.

Variables (P Q : Prop) (b b' c : bool).
Hypotheses (Hb : reflect P b) (Hb' : reflect P (negb b')).

Lemma introT  : P -> b.              Proof. exact: introTF true _. Qed.
Lemma introF  : ~P -> b = false.     Proof. exact: introTF false _. Qed.
Lemma introN  : ~P -> negb b.        Proof. exact: introNTF true _. Qed.
Lemma introNf : P -> negb b = false. Proof. exact: introNTF false _. Qed.
Lemma introTn  : ~P -> b'.           Proof. exact: introTFn true _. Qed.
Lemma introFn  : P -> b' = false.    Proof. exact: introTFn false _. Qed.

Lemma elimT  : b -> P.               Proof. exact: elimTF true _. Qed.
Lemma elimF  : b = false -> ~P.      Proof. exact: elimTF false _. Qed.
Lemma elimN  : negb b -> ~P.         Proof. exact: elimNTF true _. Qed.
Lemma elimNf : negb b = false -> P.  Proof. exact: elimNTF false _. Qed.
Lemma elimTn  : b' -> ~P.            Proof. exact: elimTFn true _. Qed.
Lemma elimFn  : b' = false -> P.     Proof. exact: elimTFn false _. Qed.

Lemma introP : (b -> Q) -> (negb b -> ~ Q) -> reflect Q b.
Proof. by case b; constructor; auto. Qed.

Lemma iffP : (P -> Q) -> (Q -> P) -> reflect Q b.
Proof. by case: Hb; constructor; auto. Qed.

Lemma appP : reflect Q b -> P -> Q.
Proof. by move=> HbQ; move/introT; case: HbQ. Qed.

Lemma sameP : reflect P c -> b = c.
Proof. case; [exact: introT | exact: introF]. Qed.

Lemma decPcases : if b then P else ~ P. Proof. by case Hb. Qed.

Definition decP : {P} + {~ P}. by case: b decPcases; [left | right]. Defined.

End Reflect.

Hint View for move/ elimTF|3 elimNTF|3 elimTFn|3 introT|2 introTn|2 introN|2.

Hint View for apply/ introTF|3 introNTF|3 introTFn|3 elimT|2 elimTn|2 elimN|2.

Hint View for apply// equivPif|3 xorPif|3 equivPifn|3 xorPifn|3.

(* Allow the direct application of a reflection lemma to a boolean assertion.  *)
Coercion elimT : reflect >-> Funclass.

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
Proof. by case b1; constructor. Qed.

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
Proof. by case b1; case b2; constructor; auto; case; auto. Qed.

Lemma norP : reflect (~~ b1 /\ ~~ b2) (~~ (b1 || b2)).
Proof. by case b1; case b2; constructor; auto; case; auto. Qed.

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

Unset Implicit Arguments.