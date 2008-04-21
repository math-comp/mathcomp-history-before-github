(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrfun.
Require Export Bool.

Set Implicit Arguments.
Unset Strict Implicit.

(*   Lemmas for boolean connectives, (crucially) including reflection. *)

(* Parsing and format declarations. *)

Reserved Notation "~~ b" (at level 35, right associativity).
Reserved Notation "b ==> c" (at level 60, right associativity).
Reserved Notation "b1  (+)  b2" (at level 50, left associativity).
Reserved Notation "x \in A" (at level 70, no associativity).
Reserved Notation "x \notin A" (at level 70, no associativity).
Reserved Notation "p1 =i p2" (at level 70, no associativity).

(* We introduce a number of n-ary "list-style" notations, which share a *)
(* common format, namely                                                *)
(*    [op arg1, arg2, ... last_separator last_arg]                      *)
(* This usually denotes a right-associative applications of op, e.g.,   *)
(*  [&& a, b, c & d] denotes a && (b && (c && d))                       *)
(* The last_separator must be a non-operator token; here we use &, | or *)
(* => (our default is &, but we try to match the intended meaning of    *)
(* op). The separator is a workaround for limitations of the parsing    *)
(* engine; for similar reasons the separator cannot be omitted even     *)
(* when last_arg can. The Notation declarations are complicated by the  *)
(* separate treatments for fixed arities (binary for bool operators,    *)
(* and all arities for Prop operators).                                 *)
(*   We also use the square brackets in comprehension-style notations   *)
(* of the form                                                          *)
(*    [type var seperator expr]                                         *)
(* where "type" is the type of the comprehension (e.g., pred) and       *)
(* separator is | or =>. It is important that in other notations a      *)
(* leading square bracket [ is always by an operator symbol or at least *)
(* a fixed identifier.                                                  *)

Reserved Notation "[ /\ P1 & P2 ]" (at level 0, only parsing).
Reserved Notation "[ /\ P1 , P2 & P3 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 ']' '/ '  &  P3 ] ']'").
Reserved Notation "[ /\ P1 , P2 , P3 & P4 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 ']' '/ '  &  P4 ] ']'").
Reserved Notation "[ /\ P1 , P2 , P3 , P4 & P5 ]" (at level 0, format
  "'[hv' [ /\ '['  P1 , '/'  P2 , '/'  P3 , '/'  P4 ']' '/ '  &  P5 ] ']'").

Reserved Notation "[ \/ P1 | P2 ]" (at level 0, only parsing).
Reserved Notation "[ \/ P1 , P2 | P3 ]" (at level 0, format
  "'[hv' [ \/ '['  P1 , '/'  P2 ']' '/ '  |  P3 ] ']'").
Reserved Notation "[ \/ P1 , P2 , P3 | P4 ]" (at level 0, format
  "'[hv' [ \/ '['  P1 , '/'  P2 , '/'  P3 ']' '/ '  |  P4 ] ']'").

Reserved Notation "[ && b1 & c ]" (at level 0, only parsing).
Reserved Notation "[ && b1 , b2 , .. , bn & c ]" (at level 0, format
  "'[hv' [ && '['  b1 , '/'  b2 , '/'  .. , '/'  bn ']' '/ '  &  c ] ']'").

Reserved Notation "[ || b1 | c ]" (at level 0, only parsing).
Reserved Notation "[ || b1 , b2 , .. , bn | c ]" (at level 0, format
  "'[hv' [ || '['  b1 , '/'  b2 , '/'  .. , '/'  bn ']' '/ '  |  c ] ']'").

Reserved Notation "[ ==> b1 => c ]" (at level 0, only parsing).
Reserved Notation "[ ==> b1 , b2 , .. , bn => c ]" (at level 0, format
  "'[hv' [ ==> '['  b1 , '/'  b2 , '/'  .. , '/'  bn ']' '/'  =>  c ] ']'").

Reserved Notation "[ 'pred' : T => E ]" (at level 0, format
  "'[hv' [ 'pred' :  T  => '/ '  E ] ']'").
Reserved Notation "[ 'pred' x => E ]" (at level 0, x at level 8, format
  "'[hv' [ 'pred'  x  => '/ '  E ] ']'").
Reserved Notation "[ 'pred' x : T => E ]" (at level 0, x at level 8, format
  "'[hv' [ 'pred'  x  :  T  => '/ '  E ] ']'").

Reserved Notation "[ 'rel' x y => E ]" (at level 0, x, y at level 8, format
  "'[hv' [ 'rel'  x   y  => '/ '  E ] ']'").
Reserved Notation "[ 'rel' x y : T => E ]" (at level 0, x, y at level 8, format
  "'[hv' [ 'rel'  x  y :  T  => '/ '  E ] ']'").

(* Shorter delimiter *)

Delimit Scope bool_scope with B.

(* The Coq library forgets to set argument scopes on bool ops. *)

Arguments Scope negb [bool_scope].
Arguments Scope orb [bool_scope bool_scope].
Arguments Scope xorb [bool_scope bool_scope].
Arguments Scope andb [bool_scope bool_scope].
Arguments Scope implb [bool_scope bool_scope].
Arguments Scope eqb [bool_scope bool_scope].
Arguments Scope leb [bool_scope bool_scope].
Arguments Scope ifb [bool_scope bool_scope bool_scope].

(* An alternative to xorb that behaves somewhat better wrt simplification. *)

Definition addb b := if b then negb else fun b' => b'.

(* Bool operator notation; we need to redeclare && and || so they get the *)
(* correct argument scopes.                                               *)

Notation "~~ b" := (negb b) : bool_scope.
(* Redundant for now; may be added if dependency on Bool is removed
Notation "b1 && b2" := (andb b1 b2) : bool_scope.
Notation "b1 || b2" := (orb b1 b2) : bool_scope.
*)
Notation "b ==> c" := (implb b c) : bool_scope.
Notation "b1 (+) b2" := (addb b1 b2) : bool_scope.

(* Coercion bool >-> Prop.                    *)

Coercion is_true b := b = true.

Ltac fold_prop := match goal with |- (?b = true) => change (is_true b) end.

Lemma prop_congr : forall b b' : bool, b = b' -> b = b' :> Prop.
Proof. by move=> b b' ->. Qed.

Ltac prop_congr := apply: prop_congr.

(* Lemmas for auto. *)
Lemma is_true_true : true.               Proof. by []. Qed.
Lemma not_false_is_true : ~ false.       Proof. by []. Qed.
Lemma is_true_locked_true : locked true. Proof. by unlock. Qed.
Hint Resolve is_true_true not_false_is_true is_true_locked_true.

(* Negation lemmas. *)

(* Note: in the general we take NEGATION as the standard form of a *)
(* false condition : hypotheses should be of the form ~~ b rather  *)
(* than b = false or ~ b, as much as possible.                     *)

Lemma negbT : forall b, b = false -> ~~ b.        Proof. by case. Qed.
Lemma negbET : forall b, ~~ b -> b = false.       Proof. by case. Qed.
Lemma negbF : forall b : bool, b -> ~~ b = false. Proof. by case. Qed.
Lemma negbEF : forall b, ~~ b = false -> b.       Proof. by case. Qed.
Lemma negbK : involutive negb.                    Proof. by case. Qed.
Lemma negbE2 : forall b, ~~ ~~ b -> b.            Proof. by case. Qed.

Lemma negb_inj : injective negb. Proof. exact: can_inj negbK. Qed.

Lemma negbLR : forall b c, b = ~~ c -> ~~ b = c.
Proof. by move=> ? [] ->. Qed.

Lemma negbRL : forall b c, ~~ b = c -> b = ~~ c.
Proof. by move=> [] ? <-. Qed.

Lemma contra : forall c b : bool, (c -> b) -> ~~ b -> ~~ c.
Proof. by case=> // ? ->. Qed.

(* Coercion of sum-style datatypes into bool, which makes it possible *)
(* to use ssr's boolean if rather than Coq's "generic" if.            *)

Coercion isSome T (u : option T) := if u is Some _ then true else false.

Coercion is_inl A B (u : A + B) := if u is inl _ then true else false.

Coercion is_left A B (u : {A} + {B}) := if u is left _ then true else false.

Coercion is_inleft A B (u : A + {B}) := if u is inleft _ then true else false.

Prenex Implicits  isSome is_inl is_left is_inleft.

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
  | IfSpecTrue  of b         : if_spec vT true
  | IfSpecFalse of b = false : if_spec vF false.

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

(* Patch for a bug in ssreflect 8.1 that corrupts patterns where a *)
(* wildcard appears under a match. Usage:                          *)
(*   rewrite -ifE; set x := if_expr _ _ _.                         *)

Definition if_expr := if b then vT else vF.
Lemma ifE : (if b then vT else vF) = if_expr. Proof. by []. Qed.

End BoolIf.

(* The reflection predicate.                                          *)

Inductive reflect (P : Prop) : bool -> Set :=
  | Reflect_true  of   P : reflect P true
  | Reflect_false of ~ P : reflect P false.

(* Core (internal) reflection lemmas, used for the three kinds of views. *)

Section ReflectCore.

Variables (P Q : Prop) (b c : bool).

Hypothesis Hb : reflect P b.

Lemma introNTF : (if c then ~ P else P) -> ~~ b = c.
Proof. by case c; case Hb. Qed.

Lemma introTF : (if c then P else ~ P) -> b = c.
Proof. by case c; case Hb. Qed.

Lemma elimNTF : ~~ b = c -> if c then ~ P else P.
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
Hypothesis Hb : reflect P (~~ b).

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
Section Reflect.

Variables (P Q : Prop) (b b' c : bool).
Hypotheses (Pb : reflect P b) (Pb' : reflect P (~~ b')).

Lemma introT  : P -> b.            Proof. exact: introTF true _. Qed.
Lemma introF  : ~ P -> b = false.  Proof. exact: introTF false _. Qed.
Lemma introN  : ~ P -> ~~ b.       Proof. exact: introNTF true _. Qed.
Lemma introNf : P -> ~~ b = false. Proof. exact: introNTF false _. Qed.
Lemma introTn : ~ P -> b'.         Proof. exact: introTFn true _. Qed.
Lemma introFn : P -> b' = false.   Proof. exact: introTFn false _. Qed.

Lemma elimT  : b -> P.             Proof. exact: elimTF true _. Qed.
Lemma elimF  : b = false -> ~ P.   Proof. exact: elimTF false _. Qed.
Lemma elimN  : ~~ b -> ~P.         Proof. exact: elimNTF true _. Qed.
Lemma elimNf : ~~ b = false -> P.  Proof. exact: elimNTF false _. Qed.
Lemma elimTn : b' -> ~ P.          Proof. exact: elimTFn true _. Qed.
Lemma elimFn : b' = false -> P.    Proof. exact: elimTFn false _. Qed.

Lemma introP : (b -> Q) -> (~~ b -> ~ Q) -> reflect Q b.
Proof. by case b; constructor; auto. Qed.

Lemma iffP : (P -> Q) -> (Q -> P) -> reflect Q b.
Proof. by case: Pb; constructor; auto. Qed.

Lemma appP : reflect Q b -> P -> Q.
Proof. by move=> Qb; move/introT; case: Qb. Qed.

Lemma sameP : reflect P c -> b = c.
Proof. case; [exact: introT | exact: introF]. Qed.

Lemma decPcases : if b then P else ~ P. Proof. by case Pb. Qed.

Definition decP : {P} + {~ P}. by case: b decPcases; [left | right]. Defined.

End Reflect.

Hint View for move/ elimTF|3 elimNTF|3 elimTFn|3 introT|2 introTn|2 introN|2.

Hint View for apply/ introTF|3 introNTF|3 introTFn|3 elimT|2 elimTn|2 elimN|2.

Hint View for apply// equivPif|3 xorPif|3 equivPifn|3 xorPifn|3.

(* Allow the direct application of a reflection lemma to a boolean assertion.  *)
Coercion elimT : reflect >-> Funclass.

(* List notations for wider connectives; the Prop connectives have a fixed  *)
(* width so as to avoid iterated destruction (we go up to width 5 for /\,   *)
(* and width 4 for or. The bool connectives have arbitrary widths, but      *)
(* denote expressions that associate to the RIGHT. This is consistent with  *)
(* the right associativity of list expressions, and thus more convenient in *)
(* many proofs.                                                             *)

Inductive and3 (P1 P2 P3 : Prop) : Prop := And3 of P1 & P2 & P3.

Inductive and4 (P1 P2 P3 P4 : Prop) : Prop := And4 of P1 & P2 & P3 & P4.

Inductive and5 (P1 P2 P3 P4 P5 : Prop) : Prop :=
  And5 of P1 & P2 & P3 & P4 & P5.

Inductive or3 (P1 P2 P3 : Prop) : Prop := Or31 of P1 | Or32 of P2 | Or33 of P3.

Inductive or4 (P1 P2 P3 P4 : Prop) : Prop :=
  Or41 of P1 | Or42 of P2 | Or43 of P3 | Or44 of P4.

Notation "[ /\ P1 & P2 ]" := (and P1 P2) (only parsing) : type_scope.
Notation "[ /\ P1 , P2 & P3 ]" := (and3 P1 P2 P3) : type_scope.
Notation "[ /\ P1 , P2 , P3 & P4 ]" := (and4 P1 P2 P3 P4) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 & P5 ]" := (and5 P1 P2 P3 P4 P5) : type_scope.

Notation "[ \/ P1 | P2 ]" := (or P1 P2) (only parsing) : type_scope.
Notation "[ \/ P1 , P2 | P3 ]" := (or3 P1 P2 P3) : type_scope.
Notation "[ \/ P1 , P2 , P3 | P4 ]" := (or4 P1 P2 P3 P4) : type_scope.

Notation "[ && b1 & c ]" := (b1 && c) (only parsing) : bool_scope.
Notation "[ && b1 , b2 , .. , bn & c ]" := (b1 && (b2 && .. (bn && c) .. ))
  : bool_scope.

Notation "[ || b1 | c ]" := (b1 || c) (only parsing) : bool_scope.
Notation "[ || b1 , b2 , .. , bn | c ]" := (b1 || (b2 || .. (bn || c) .. ))
  : bool_scope.

Notation "[ ==> b1 , b2 , .. , bn => c ]" :=
   (b1 ==> (b2 ==> .. (bn ==> c) .. )) : bool_scope.
Notation "[ ==> b1 => c ]" := (b1 ==> c) (only parsing) : bool_scope.

Section ReflectConnectives.

Variable b1 b2 b3 b4 b5 : bool.

Lemma idP : reflect b1 b1.
Proof. by case b1; constructor. Qed.

Lemma idPn : reflect (~~ b1) (~~ b1).
Proof. by case b1; constructor. Qed.

Lemma negP : reflect (~ b1) (~~ b1).
Proof. by case b1; constructor; auto. Qed.

Lemma negPn : reflect b1 (~~ ~~ b1).
Proof. by case b1; constructor. Qed.

Lemma negPf : reflect (b1 = false) (~~ b1).
Proof. by case b1; constructor. Qed.

Lemma andP : reflect (b1 /\ b2) (b1 && b2).
Proof. by case b1; case b2; constructor=> //; case. Qed.

Lemma and3P : reflect [/\ b1, b2 & b3] [&& b1, b2 & b3].
Proof. by case b1; case b2; case b3; constructor; try by case. Qed.

Lemma and4P : reflect [/\ b1, b2, b3 & b4] [&& b1, b2, b3 & b4].
Proof.
by case b1; case b2; case b3; case b4; constructor; try by case. Qed.

Lemma and5P : reflect [/\ b1, b2, b3, b4 & b5] [&& b1, b2, b3, b4 & b5].
Proof.
by case b1; case b2; case b3; case b4; case b5; constructor; try by case.
Qed.

Lemma orP : reflect (b1 \/ b2) (b1 || b2).
Proof. by case b1; case b2; constructor; auto; case. Qed.

Lemma or3P : reflect [\/ b1, b2 | b3] [|| b1, b2 | b3].
Proof.
case b1; first by constructor; constructor 1.
case b2; first by constructor; constructor 2.
case b3; first by constructor; constructor 3.
by constructor; case.
Qed.

Lemma or4P : reflect [\/ b1, b2, b3 | b4] [|| b1, b2, b3 | b4].
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

Lemma implyP: reflect (b1 -> b2) (b1 ==> b2).
Proof. by case b1; case b2; constructor; auto. Qed.

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
Implicit Arguments implyP [b1 b2].
Prenex Implicits idP idPn negP negPn negPf.
Prenex Implicits andP and3P and4P and5P orP or3P or4P nandP norP implyP.

(* Shorter, more systematic names for the boolean connectives laws.       *)

Lemma andTb : left_unit true andb.     Proof. by []. Qed.
Lemma andFb : left_zero false andb.    Proof. by []. Qed.
Lemma andbT : right_unit true andb.    Proof. by case. Qed.
Lemma andbF : right_zero false andb.   Proof. by case. Qed.
Lemma andbb : idempotent andb.         Proof. by case. Qed.
Lemma andbC : commutative andb.        Proof. by do 2!case. Qed.
Lemma andbA : associative andb.        Proof. by do 3!case. Qed.
Lemma andbCA : left_commutative andb.  Proof. by do 3!case. Qed.
Lemma andbAC : right_commutative andb. Proof. by do 3!case. Qed.

Lemma orTb : forall b, true || b.      Proof. by []. Qed.
Lemma orFb : left_unit false orb.      Proof. by []. Qed.
Lemma orbT : forall b, b || true.      Proof. by case. Qed.
Lemma orbF : right_unit false orb.     Proof. by case. Qed.
Lemma orbb : idempotent orb.           Proof. by case. Qed.
Lemma orbC : commutative orb.          Proof. by do 2!case. Qed.
Lemma orbA : associative orb.          Proof. by do 3!case. Qed.
Lemma orbCA : left_commutative orb.    Proof. by do 3!case. Qed.
Lemma orbAC : right_commutative orb.   Proof. by do 3!case. Qed.

Lemma andbN : forall b, b && ~~ b = false. Proof. by case. Qed.
Lemma andNb : forall b, ~~ b && b = false. Proof. by case. Qed.
Lemma orbN : forall b, b || ~~ b = true.   Proof. by case. Qed.
Lemma orNb : forall b, ~~ b || b = true.   Proof. by case. Qed.

Lemma andb_orl : left_distributive andb orb.  Proof. by do 3!case. Qed.
Lemma andb_orr : right_distributive andb orb. Proof. by do 3!case. Qed.
Lemma orb_andl : left_distributive orb andb.  Proof. by do 3!case. Qed.
Lemma orb_andr : right_distributive orb andb. Proof. by do 3!case. Qed.

Lemma negb_and : forall b1 b2, ~~ (b1 && b2) = ~~ b1 || ~~ b2.
Proof. by do 2!case. Qed.

Lemma negb_or : forall b1 b2, ~~ (b1 || b2) = ~~ b1 && ~~ b2.
Proof. by do 2!case. Qed.

(* Pseudo-cancellation -- i.e, absorbtion *)

Lemma andbK : forall b1 b2, b1 && b2 || b1 = b1.  Proof. by do 2!case. Qed.
Lemma andKb : forall b1 b2, b1 || b2 && b1 = b1.  Proof. by do 2!case. Qed.
Lemma orbK : forall b1 b2, (b1 || b2) && b1 = b1. Proof. by do 2!case. Qed.
Lemma orKb : forall b1 b2, b1 && (b2 || b1) = b1. Proof. by do 2!case. Qed.

(* Imply *)

Lemma implybT : forall b, b ==> true.           Proof. by case. Qed.
Lemma implybF : forall b, (b ==> false) = ~~ b. Proof. by case. Qed.
Lemma implyFb : forall b, false ==> b.          Proof. by []. Qed.
Lemma implyTb : forall b, (true ==> b) = b.     Proof. by []. Qed.

Lemma negb_imply : forall b1 b2, ~~ (b1 ==> b2) = b1 && ~~ b2.
Proof. by do 2!case. Qed.

Lemma implybE : forall b1 b2, (b1 ==> b2) = ~~ b1 || b2.
Proof. by do 2!case. Qed.

Lemma implybN : forall b1 b2, (~~ b1 ==> ~~ b2) = b2 ==> b1.
Proof. by do 2!case. Qed.

(* addition (xor) *)

Lemma addFb : left_unit false addb.             Proof. by []. Qed.
Lemma addbF : right_unit false addb.            Proof. by case. Qed.
Lemma addbb : self_inverse false addb.          Proof. by case. Qed.
Lemma addbC : commutative addb.                 Proof. by do 2!case. Qed.
Lemma addbA : associative addb.                 Proof. by do 3!case. Qed.
Lemma addbCA : left_commutative addb.           Proof. by do 3!case. Qed.
Lemma addbAC : right_commutative addb.          Proof. by do 3!case. Qed.
Lemma andb_addl : left_distributive andb addb.  Proof. by do 3!case. Qed.
Lemma andb_addr : right_distributive andb addb. Proof. by do 3!case. Qed.
Lemma addbK : forall b, involutive (addb b).    Proof. by do 2!case. Qed.
Lemma addKb : forall b, involutive (addb^~ b).  Proof. by do 2!case. Qed.


Lemma addTb : forall b, true (+) b = ~~ b. Proof. by []. Qed.
Lemma addbT : forall b, b (+) true = ~~ b. Proof. by case. Qed.

Lemma addbN : forall b1 b2, b1 (+) ~~ b2 = ~~ (b1 (+) b2).
Proof. by do 2!case. Qed.
Lemma addNb : forall b1 b2, ~~ b1 (+) b2 = ~~ (b1 (+) b2).
Proof. by do 2!case. Qed.

Lemma addbP : forall b1 b2, b1 (+) b2 -> ~~ b1 = b2.
Proof. by do 2!case. Qed.

(* Resolution tactic for blindly weeding out common terms from boolean       *)
(* equalities. When faced with a goal of the form (andb/orb/addb b1 b2) = b3 *)
(* they will try to locate b1 in b3 and remove it. This can fail!            *)

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

(* Predicates, i.e., packaged functions to bool.                  *)
(*   Indeed, pred T, the basic type for predicates over a type T, *)
(* is simply an alias for T -> bool.                              *)
(*   We actually distinguish two kinds of predicates, which we    *)
(* applicative and collective, based on the syntax used to        *)
(* specialize them to some value x in T:                          *)
(*  - For an applicative predicate P, one uses prefix syntax:     *)
(*        P x                                                     *)
(*    Also, most operations on applicative predicates us prefix   *)
(*    syntax as well (e.g., predI P Q).                           *)
(*  - For a collective predicate A, one uses infix syntax:        *)
(*        x \in A                                                 *)
(*    and all operations on collective predicates use infix       *)
(*    syntax as well (e.g., [predI A & B]).                       *)
(* There are only two kinds of applicative predicates:            *)
(*  - pred T, the alias for T -> bool mentioned above             *)
(*  - simpl_pred T, an alias for simpl_fun T bool with a coercion *)
(*    to pred T that auto-simplifies on application (see ssrfun). *)
(* On the other hand, the set of collective predicate types is    *)
(* open-ended, via                                                *)
(*  - predType T, a Structure that can be used to put Canonical   *)
(*    collective predicate interpretation on other types, such    *)
(*    as lists, tuples, finite sets, etc.                         *)
(* Indeed, we define such interpretations for both applicative    *)
(* predicate types, which can therefore also be used with the     *)
(* infix syntax, e.g. x \in predI P Q. Moreover these infix forms *)
(* are convertible to their prefix counterpart (e.g., predI P Q x *)
(* which in turn simplifies to P x && Q x).                       *)
(*   The converse is not true, however; collective predicate      *)
(* types cannot, in general, be used applicatively, because of    *)
(* the "uniform inheritance" restriction on implicit coercion.    *)
(*   However, we do define an explicit generic coercion           *)
(*  - mem : forall (pT : predType), pT -> mem_pred T              *)
(*    where mem_pred T is a variant of simpl_pred T that          *)
(*    preserves the infix syntax, i.e.,                           *)
(*       mem A x auto-simplifies to x \in A                       *)
(* Indeed, the infix "collective" operators are notation for a    *)
(* prefix operator with arguments of type mem_pred T or pred T,   *)
(* applied to coerced collective predicates, e.g.,                *)
(*      Notation "x \in A" := (in_mem x (mem A)).                 *)
(* This prevents the variability in the predicate type from       *)
(* interfering with the application of generic lemmas. Moreover   *)
(* this also makes it much easier to define generic lemmas,       *)
(* because the simplest type -- pred T -- can be used as the type *)
(* of generic collective predicates, provided one takes care not  *)
(* to use it applicatively; this avoids the burden of having to   *)
(* declare a different predicate type for each predicate          *)
(* parameter of each section or lemma.                            *)
(*   This trick is made possible by the fact that the constructor *)
(* of the mem_pred T type aligns the unification process, forcing *)
(* a generic "collective" predicate A : pred T to unify with the  *)
(* actual collective B, which mem has coerced to pred T via an    *)
(* internal, hidden implicit coercion, supplied by the predType   *)
(* structure for B. Users should take care not to inadverdently   *)
(* "strip" (mem B) down to the coerced B, since this will expose  *)
(* the internal coercion: Coq will display a term B x that can't  *)
(* be typed as such. The topredE lemma can be used to restore the *)
(* x \in B syntax in this case. While -topredE can conversely be  *)
(* used to change x \in P into P x, it is safer to use the inE    *)
(* and memE lemmas instead, as they do not run the risk of        *)
(* exposing internal coercions. As a consequence, it is better to *)
(* explicitly cast a generic applicative pred T to simpl_pred,    *)
(* using the SimplPred constructor, when it is used as a          *)
(* collective predicate (see, e.g., Lemma eq_big in bigops.v).    *)
(*   We also sometimes "instantiate" the predType structure by    *)
(* defining a coercion to the sort of the predPredType structure. *)
(* This works better for types such as set T that have subtypes   *)
(* that coerce to them, since the same coercion will be inserted  *)
(* by tha application of mem. It also allows use to turn some     *)
(* specific Types (namely, any aT : predArgType) into predicates, *)
(* specifically, the total predicate over that type, i.e.,        *)
(* fun _ : aT => true. This allow us to write, e.g.,  #|I_(n)|    *)
(* for the cardinal of the (finite) type of integers less than n. *)
(*   Collective predicates have a specific extensional equality,  *)
(*     - A =i B,                                                  *)
(* while applicative predicates just use the extensional equality *)
(* of functions,                                                  *)
(*     - P =1 Q                                                   *)
(* The two forms are convertible, however.                        *)
(*   We lift boolean operations to predicates, defining:          *)
(*  - predU (union), predI (intersection), predC (complement),    *)
(*    predD (difference), and preim (preimage, i.e., composition) *)
(* For each operation we define three forms, typically:           *)
(*   - predU : pred T -> pred T -> simpl_pred T                   *)
(*   - [predU A & B], a Notation for predU (mem A) (mem B)        *)
(*   - xpredU, a Notation for the lambda-expression inside predU, *)
(*     which is mostly useful as an argument of =1, since it      *)
(*     exposes the head constant of the expression to the         *)
(*     ssreflect matching algoritm.                               *)
(* The syntax for the preimage of a collective predicate A is     *)
(*   - [preim f of A]                                             *)
(* Finally, the generic syntax for defining a simpl_pred T is     *)
(*   - [pred x : T | P(x)], [pred x | P(x)], [pred x \in A | P(x) *)
(* We also support boolean relations, but only the applicative    *)
(* form, with types                                               *)
(*   - rel T, an alias for T -> pred T                            *)
(*   - simpl_rel T, an auto-simplifying version, and syntax       *)
(*     [rel x y | P(x,y)], [rel x y \in A & B | P(x,y)], etc.     *)
(* The notation [rel of fA] can be used to coerce a function      *)
(* returning a collective predicate to one returning pred T.      *)

Definition pred T := T -> bool.

Identity Coercion fun_of_pred : pred >-> Funclass.

Definition rel T := T -> pred T.

Identity Coercion fun_of_rel : rel >-> Funclass.

Notation xpred0 := (fun _ => false).
Notation xpredA := (fun _ => true).
Notation xpredI := (fun (p1 p2 : pred _) x => p1 x && p2 x).
Notation xpredU := (fun (p1 p2 : pred _) x => p1 x || p2 x).
Notation xpredC := (fun (p : pred _) x => ~~ p x).
Notation xpredD := (fun (p1 p2 : pred _) x => ~~ p2 x && p1 x).
Notation xpreim := (fun f (p : pred _) x => p (f x)).
Notation xrelU := (fun (r1 r2 : rel _) x y => r1 x y || r2 x y).

Section Predicates.

Variables T : Type.

Definition subpred (p1 p2 : pred T) := forall x, p1 x -> p2 x.

Definition subrel (r1 r2 : rel T) := forall x y, r1 x y -> r2 x y.

Definition simpl_pred := simpl_fun T bool.

Definition SimplPred (p : pred T) : simpl_pred := SimplFun p.

Coercion pred_of_simpl (p : simpl_pred) : pred T := p : T -> bool.

Definition pred0 := SimplPred xpred0.
Definition predA := SimplPred xpredA.
Definition predI p1 p2 := SimplPred (xpredI p1 p2).
Definition predU p1 p2 := SimplPred (xpredU p1 p2).
Definition predC p := SimplPred (xpredC p).
Definition predD p1 p2 := SimplPred (xpredD p1 p2).
Definition preim rT f (d : pred rT) := SimplPred (xpreim f d).

Definition simpl_rel := simpl_fun T (pred T).

Definition SimplRel (r : rel T) : simpl_rel := [fun x => r x].

Coercion rel_of_simpl_rel (r : simpl_rel) : rel T := fun x y => r x y.

Definition relU r1 r2 := SimplRel (xrelU r1 r2).

Lemma subrelUl : forall r1 r2, subrel r1 (relU r1 r2).
Proof. by move=> * ? *; apply/orP; left. Qed.

Lemma subrelUr : forall r1 r2, subrel r2 (relU r1 r2).
Proof. by move=> * ? *; apply/orP; right. Qed.

CoInductive mem_pred : Type := Mem of pred T.

Definition isMem pT topred mem := mem = (fun p : pT => Mem [eta topred p]).

Structure predType : Type := PredType {
  pred_sort :> Type;
  topred : pred_sort -> pred T;
  _ : {mem | isMem topred mem}
}.

Definition mkPredType pT toP := PredType (exist (@isMem pT toP) _ (erefl _)).

Canonical Structure predPredType := Eval hnf in @mkPredType (pred T) id.
Canonical Structure simplPredType := Eval hnf in mkPredType pred_of_simpl.

Coercion pred_of_mem mp : pred_sort predPredType :=
  let: Mem p := mp in [eta p].

Canonical Structure memPredType := Eval hnf in mkPredType pred_of_mem.

End Predicates.

Implicit Arguments pred0 [T].
Implicit Arguments predA [T].
Prenex Implicits pred0 predA predI predU predC predD preim relU.

Notation "[ 'pred' : T | E ]" := (SimplPred (fun _ : T => E))
  (at level 0, format "[ 'pred' :  T  |  E ]") : fun_scope.
Notation "[ 'pred' x | E ]" := (SimplPred (fun x => E))
  (at level 0, x ident, format "[ 'pred'  x  |  E ]") : fun_scope.
Notation "[ 'pred' x : T | E ]" := (SimplPred (fun x : T => E))
  (at level 0, x ident, only parsing) : fun_scope.
Notation "[ 'rel' x y | E ]" := (SimplRel (fun x y => E))
  (at level 0, x ident, y ident, format "[ 'rel'  x  y  |  E ]") : fun_scope.
Notation "[ 'rel' x y : T | E ]" := (SimplRel (fun x y : T => E))
  (at level 0, x ident, y ident, only parsing) : fun_scope.

Notation "[ 'predType' 'of' pT ]" :=
  (match {pT : as predType _} as s return [type of @PredType _ for s] -> _ with
  | PredType _ a mP => fun k => k a mP end
  (@PredType _ pT)) (at level 0, only parsing) : form_scope.

(* This redundant coercion lets us "inherit" the simpl_predType canonical *)
(* structure by declaring a coercion to simpl_pred. This hack is the only *)
(* way to put a predType structure on a predArgType. We use simpl_pred    *)
(* rather than pred to ensure that /= removes the identity coercion. Note *)
(* that the coercion will never be used directly for simpl_pred, since    *)
(* the canonical structure should always resolve.                         *)

Notation pred_class := (pred_sort (predPredType _)).
Coercion sort_of_simpl_pred T (p : simpl_pred T) : pred_class := p : pred T.

(* This lets us use some types as a synonym for their universal predicate. *)
(* Unfortunately, this won't work for existing types like bool, unless     *)
(* we redefine bool, true, false and all bool ops.                         *)
Definition predArgType := Type.
Identity Coercion sort_of_predArgType : predArgType >-> Sortclass.
Coercion typeA (T : predArgType) : simpl_pred T := predA.
Definition boolA : predArgType := bool.

(* These must be defined outside a Section because "cooking" kills the *)
(* nosimpl tag.                                                        *)

Definition mem T (pT : predType T) : pT -> mem_pred T :=
  nosimpl (let: PredType _ _ (exist mem _) := pT return pT -> _ in mem).
Definition in_mem T x mp := nosimpl pred_of_mem T mp x.

Prenex Implicits mem.

Coercion pred_of_mem_pred T mp := [pred x : T | in_mem x mp].

Definition eq_mem T p1 p2 := forall x : T, in_mem x p1 = in_mem x p2.
Definition sub_mem T p1 p2 := forall x : T, in_mem x p1 -> in_mem x p2.

Notation "x \in A" := (in_mem x (mem A)) : bool_scope.
Notation "x \in A" := (in_mem x (mem A)) : bool_scope.
Notation "x \notin A" := (~~ (x \in A)) : bool_scope.
Notation "A =i B" := (eq_mem (mem A) (mem B)) : type_scope.
Notation "{ 'subset' A <= B }" := (sub_mem (mem A) (mem B))
  (at level 0, A, B at level 69,
   format "{ '[hv' 'subset'  A '/   '  <=  B ']' }") : type_scope.
Notation "[ 'mem' A ]" := (pred_of_simpl (pred_of_mem_pred (mem A)))
  (at level 0, only parsing) : fun_scope.
Notation "[ 'rel' 'of' fA ]" := (fun x => [mem (fA x)])
  (at level 0, format "[ 'rel'  'of'  fA ]") : fun_scope.
Notation "[ 'predI' A & B ]" := (predI [mem A] [mem B])
  (at level 0, format "[ 'predI'  A  &  B ]") : fun_scope.
Notation "[ 'predU' A & B ]" := (predU [mem A] [mem B])
  (at level 0, format "[ 'predU'  A  &  B ]") : fun_scope.
Notation "[ 'predD' A & B ]" := (predD [mem A] [mem B])
  (at level 0, format "[ 'predD'  A  &  B ]") : fun_scope.
Notation "[ 'predC' A ]" := (predC [mem A])
  (at level 0, format "[ 'predC'  A ]") : fun_scope.
Notation "[ 'preim' f 'of' A ]" := (preim f [mem A])
  (at level 0, format "[ 'preim'  f  'of'  A ]") : fun_scope.

Notation "[ 'pred' x \in A | E ]" := [pred x | (x \in A) && E]
  (at level 0, x ident, format "[ 'pred'  x  \in  A  |  E ]") : fun_scope.
Notation "[ 'rel' x y \in A & B | E ]" :=
  [rel x y | (x \in A) && (y \in B) && E]
  (at level 0, x ident, y ident,
   format "[ 'rel'  x  y  \in  A  &  B  |  E ]") : fun_scope.
Notation "[ 'rel' x y \in A & B ]" := [rel x y | (x \in A) && (y \in B)]
  (at level 0, x ident, y ident,
   format "[ 'rel'  x  y  \in  A  &  B ]") : fun_scope.
Notation "[ 'rel' x y \in A | E ]" := [rel x y \in A & A | E]
  (at level 0, x ident, y ident,
   format "[ 'rel'  x  y  \in  A  |  E ]") : fun_scope.
Notation "[ 'rel' x y \in A ]" := [rel x y \in A & A]
  (at level 0, x ident, y ident,
   format "[ 'rel'  x  y  \in  A ]") : fun_scope.

Section simpl_mem.

Variables (T : Type) (pT : predType T).

Lemma mem_topred : forall (p : pT), mem (topred p) = mem p.
Proof. by rewrite /mem; case: pT => T1 app1 [mem1  /= ->]. Qed.

Lemma topredE : forall x (p : pT), topred p x = (x \in p).
Proof. by move=> *; rewrite -mem_topred. Qed.

Lemma in_simpl : forall x (p : simpl_pred T), (x \in p) = p x.
Proof. by []. Qed.

Definition inE := in_simpl. (* to be extended *)

Lemma mem_simpl : forall (p : simpl_pred T), mem p = p :> pred T.
Proof. by []. Qed.

Definition memE := mem_simpl. (* could be extended *)

Lemma mem_mem : forall p : pT, (mem (mem p) = mem p) * (mem [mem p] = mem p).
Proof. by move=> p; rewrite -mem_topred. Qed.

End simpl_mem.

Section RelationProperties.

(* Caveat: reflexive should not be used to state lemmas, since Auto *)
(* and Trivial will not expand the constant.                        *)

Variable T : Type.

Variable R : rel T.

Definition total := forall x y, R x y || R y x.
Definition transitive := forall y x z, R x y -> R y z -> R x z.

Definition symmetric := forall x y, R x y = R y x.
Definition antisymmetric := forall x y, R x y && R y x -> x = y.
Definition reflexive := forall x, R x x.
Definition irreflexive := forall x, R x x = false.

End RelationProperties.

(* Property localization *)

Section LocalProperties.

Variables T1 T2 T3 PfT : Type.

Variables (d1 : mem_pred T1) (d2 : mem_pred T2) (d3 : mem_pred T3).
Notation Local ph := (phantom _).

Definition prop_in1 P & ph (forall x, P x : Prop) :=
  forall x, in_mem x d1 -> P x.

Definition prop_in11 P & ph (forall x y, P x y : Prop) :=
  forall x y, in_mem x d1 -> in_mem y d2 -> P x y.

Definition prop_in2 P & ph (forall x y, P x y : Prop) :=
  forall x y, in_mem x d1 -> in_mem y d1 -> P x y.

Definition prop_in111 P & ph (forall x y z, P x y z : Prop) :=
  forall x y z, in_mem x d1 -> in_mem y d2 -> in_mem z d3 -> P x y z.

Definition prop_in12 P & ph (forall x y z, P x y z : Prop) :=
  forall x y z, in_mem x d1 -> in_mem y d2 -> in_mem z d2 -> P x y z.

Definition prop_in21 P & ph (forall x y z, P x y z : Prop) :=
  forall x y z, in_mem x d1 -> in_mem y d1 -> in_mem z d2 -> P x y z.

Definition prop_in3 P & ph (forall x y z, P x y z : Prop) :=
  forall x y z, in_mem x d1 -> in_mem y d1 -> in_mem z d1 -> P x y z.

Variable f : T1 -> T2.

Definition prop_on1 Pf P & ph (Pf f : PfT) & ph (forall x, P x : Prop) :=
  forall x, in_mem (f x) d2 -> P x.

Definition prop_on11 Pf P & ph (Pf f : PfT) & ph (forall x y, P x y : Prop) :=
  forall x y, in_mem (f x) d2 -> in_mem (f y) d2 -> P x y.

End LocalProperties.

Definition inPhantom (P : Prop) := Phantom P.
Definition onPhantom T (P : T -> Prop) x := Phantom (P x).

Definition bijective_in aT rT (d : mem_pred aT) (f : aT -> rT) :=
  exists2 g, prop_in1 d (inPhantom (cancel f g))
           & prop_on1 d (Phantom (cancel g)) (onPhantom (cancel g) f).

Definition bijective_on aT rT (cd : mem_pred rT) (f : aT -> rT) :=
  exists2 g, prop_on1 cd (Phantom (cancel f)) (onPhantom (cancel f) g)
           & prop_in1 cd (inPhantom (cancel g f)).

Notation "{ 'in' d , P }" :=
  (prop_in1 (mem d) (inPhantom P))
  (at level 0, format "{ 'in'  d ,  P }") : type_scope.

Notation "{ 'in' d1 & d2 , P }" :=
  (prop_in11 (mem d1) (mem d2) (inPhantom P))
  (at level 0, format "{ 'in'  d1  &  d2 ,  P }") : type_scope.

Notation "{ 'in' d & , P }" :=
  (prop_in2 (mem d) (inPhantom P))
  (at level 0, format "{ 'in'  d  & ,  P }") : type_scope.

Notation "{ 'in' d1 & d2 & d3 , P }" :=
  (prop_in111 (mem d1) (mem d2) (mem d3) (inPhantom P))
  (at level 0, format "{ 'in'  d1  &  d2  &  d3 ,  P }") : type_scope.

Notation "{ 'in' d1 & & d3 , P }" :=
  (prop_in21 (mem d1) (mem d3) (inPhantom P))
  (at level 0, format "{ 'in'  d1  &  &  d3 ,  P }") : type_scope.

Notation "{ 'in' d1 & d2 & , P }" :=
  (prop_in12 (mem d1) (mem d2) (inPhantom P))
  (at level 0, format "{ 'in'  d1  &  d2  & ,  P }") : type_scope.

Notation "{ 'in' d & & , P }" :=
  (prop_in3 (mem d) (inPhantom P))
  (at level 0, format "{ 'in'  d  &  & ,  P }") : type_scope.

Notation "{ 'on' cd , P }" :=
  (prop_on1 (mem cd) (inPhantom P) (inPhantom P))
  (at level 0, format "{ 'on'  cd ,  P }") : type_scope.

Notation "{ 'on' cd & , P }" :=
  (prop_on11 (mem cd) (inPhantom P) (inPhantom P))
  (at level 0, format "{ 'on'  cd  & ,  P }") : type_scope.

Notation "{ 'on' cd , P & g }" :=
  (prop_on1 (mem cd) (Phantom P) (onPhantom P g))
  (at level 0, format "{ 'on'  cd ,  P  &  g }") : type_scope.

Notation "{ 'in' d , 'bijective' f }" := (bijective_in (mem d) f)
  (at level 0, f at level 8,
   format "{ 'in'  d ,  'bijective'  f }") : type_scope.

Notation "{ 'on' cd , 'bijective' f }" := (bijective_on (mem cd) f)
  (at level 0, f at level 8,
   format "{ 'on'  cd ,  'bijective'  f }") : type_scope.

(* Weakening and monotonicity lemmas for localized predicates. *)
(* Note that using these lemmas in backward reasoning will     *)
(* cause the expansion of the predicate definition, as Coq     *)
(* needs to expose the quantifier to apply these lemmas. We    *)
(* define some specialized variants to avoid this for some of  *)
(* the ssrfun definitions.                                     *)

Section LocalGlobal.

Variables T1 T2 T3 : predArgType.
Variables (d1 d1' : pred T1) (d2 d2' : pred T2) (d3 d3' : pred T3).
Variables (f f' : T1 -> T2) (g : T2 -> T1) (h : T3).
Variables (P1 : T1 -> Prop) (P2 : T1 -> T2 -> Prop).
Variable P3 : T1 -> T2 -> T3 -> Prop.
Variable Q1 : (T1 -> T2) -> T1 -> Prop.
Variable Q1l : (T1 -> T2) -> T3 -> T1 -> Prop.
Variable Q2 : (T1 -> T2) -> T1 -> T1 -> Prop.
Let allP1 := forall x1, P1 x1.
Let allP2 := forall x1 x2, P2 x1 x2.
Let allP3 := forall x1 x2 x3, P3 x1 x2 x3.
Let allQ1 f'' := forall x, Q1 f'' x.
Let allQ1l f'' h' := forall x, Q1l f'' h' x.
Let allQ2 f'' := forall x y, Q2 f'' x y.

Hypothesis sub1 : {subset d1 <= d1'}.
Hypothesis sub2 : {subset d2 <= d2'}.
Hypothesis sub3 : {subset d3 <= d3'}.

Lemma in1W : allP1 -> {in d1, allP1}. Proof. by move=> ? ?. Qed.

Lemma in2W : allP2 -> {in d1 & d2, allP2}. Proof. by move=> ? ?. Qed.

Lemma in3W : allP3 -> {in d1 & d2 & d3, allP3}. Proof. by move=> ? ?. Qed.

Lemma in1A : {in T1, allP1} -> allP1. Proof. by move=> ? ?; auto. Qed.

Lemma in2A : {in T1 & T2, allP2} -> allP2. Proof. by move=> ? ?; auto. Qed.

Lemma in3A : {in T1 & T2 & T3, allP3} -> allP3.
Proof. by move=> ? ?; auto. Qed.

Lemma subin1 : {in d1', allP1} -> {in d1, allP1}.
Proof. move=> allP x; move/sub1; exact: allP. Qed.

Lemma subin11 : {in d1' & d2', allP2} -> {in d1 & d2, allP2}.
Proof. move=> allP x1 x2; move/sub1=> d1x1; move/sub2; exact: allP. Qed.

Lemma subin111 : {in d1' & d2' & d3', allP3} -> {in d1 & d2 & d3, allP3}.
Proof.
move=> allP x1 x2 x3.
move/sub1=> d1x1; move/sub2=> d2x2; move/sub3; exact: allP.
Qed.

Lemma on1W : allQ1 f -> {on d2, allQ1 f}. Proof. by move=> ? ?. Qed.

Lemma on1lW : allQ1l f h -> {on d2, allQ1l f & h}. Proof. by move=> ? ?. Qed.

Lemma on2W : allQ2 f -> {on d2 &, allQ2 f}. Proof. by move=> ? ?. Qed.

Lemma on1A : {on T2, allQ1 f} -> allQ1 f. Proof. by move=> ? ?; auto. Qed.

Lemma on1lA : {on T2, allQ1l f & h} -> allQ1l f h.
Proof. by move=> ? ?; auto. Qed.

Lemma on2A : {on T2 &, allQ2 f} -> allQ2 f.
Proof. by move=> ? ?; auto. Qed.

Lemma subon1 : {on d2', allQ1 f} -> {on d2, allQ1 f}.
Proof. move=> allQ x; move/sub2; exact: allQ. Qed.

Lemma subon1l : {on d2', allQ1l f & h} -> {on d2, allQ1l f & h}.
Proof. move=> allQ x; move/sub2; exact: allQ. Qed.

Lemma subon2 : {on d2' &, allQ2 f} -> {on d2 &, allQ2 f}.
Proof. move=> allQ x y; move/sub2=> d2fx; move/sub2; exact: allQ. Qed.

Lemma subin_eq : {in d1', f =1 f'} -> {in d1, f =1 f'}.
Proof. move=> eqff' x; move/sub1; exact: eqff'. Qed.

Lemma subin_can : {in d1', cancel f g} -> {in d1, cancel f g}.
Proof. move=> fK x; move/sub1; exact: fK. Qed.

Lemma subin_inj : {in d1' &, injective f} -> {in d1 &, injective f}.
Proof. move=> injf x y; move/sub1=> d1x; move/sub1; exact: injf. Qed.

Lemma subin_bij : {in d1', bijective f} -> {in d1, bijective f}.
Proof.
case=> g' fK g'K; exists g' => x; move/sub1; [exact: fK | exact: g'K].
Qed.

Lemma subon_can : {on d2', cancel f & g} -> {on d2, cancel f & g}.
Proof. move=> fK x; move/sub2; exact: fK. Qed.

Lemma subon_inj : {on d2' &, injective f} -> {on d2 &, injective f}.
Proof. move=> injf x y; move/sub2=> d2fx; move/sub2; exact: injf. Qed.

Lemma subon_bij : {on d2', bijective f} -> {on d2, bijective f}.
Proof.
case=> g' fK g'K; exists g' => x; move/sub2; [exact: fK | exact: g'K].
Qed.

Lemma in_can_inj : {in d1, cancel f g} -> {in d1 &, injective f}.
Proof.
by move=> fK x y; do 2![move/fK=> def; rewrite -{2}def {def}] => ->.
Qed.

Lemma on_can_inj : {on d2, cancel f & g} -> {on d2 &, injective f}.
Proof.
by move=> fK x y; do 2![move/fK=> def; rewrite -{2}def {def}] => ->.
Qed.

Lemma inW_bij : bijective f -> {in d1, bijective f}.
Proof. by case=> g' fK g'K; exists g' => * ? *; auto. Qed.

Lemma onW_bij : bijective f -> {on d2, bijective f}.
Proof. by case=> g' fK g'K; exists g' => * ? *; auto. Qed.

Lemma inA_bij : {in T1, bijective f} -> bijective f.
Proof. by case=> g' fK g'K; exists g' => * ? *; auto. Qed.

Lemma onA_bij : {on T2, bijective f} -> bijective f. 
Proof. by case=> g' fK g'K; exists g' => * ? *; auto. Qed.

End LocalGlobal.

Lemma subin2 : forall T (d d' : pred T) (P : T -> T -> Prop),
  let allP := forall x y, P x y in
  {subset d <= d'} -> {in d' &, allP} -> {in d &, allP}.
Proof. by move=> T d d' P /= sub; exact: subin11. Qed.

Lemma subin3 : forall T (d d' : pred T) (P : T -> T -> T -> Prop),
  let allP := forall x y z, P x y z in
  {subset d <= d'} -> {in d' & &, allP} -> {in d & &, allP}.
Proof. by move=> T d d' P /= sub; exact: subin111. Qed.

