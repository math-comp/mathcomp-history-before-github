(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import funs.
Require Export Bool.

Set Implicit Arguments.
Unset Strict Implicit.

(*   Lemmas for boolean connectives, (crucially) including reflection. *)

(* Parsing and format declarations. *)

Reserved Notation "~~ b" (at level 35, right associativity).
Reserved Notation "b ==> c" (at level 90, right associativity).
Reserved Notation "b1  (+)  b2" (at level 50, left associativity).
Reserved Notation "x \in A" (at level 70, no associativity).
Reserved Notation "x \notin A" (at level 70, no associativity).

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

Reserved Notation "[ 'pred' x => E ]" (at level 0, format
  "'[hv' [ 'pred'  x  => '/ '  E ] ']'").
Reserved Notation "[ 'pred' x : T => E ]" (at level 0, format
  "'[hv' [ 'pred'  x  :  T  => '/ '  E ] ']'").

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
Notation "~~ b" := (negb b) : bool_scope.

(* Note: in the general we take NEGATION as the standard form of a *)
(* false condition : hypotheses should be of the form ~~ b rather  *)
(* than b = false or ~ b, as much as possible.                     *)

Lemma negbT : forall b, b = false -> ~~ b. Proof. by case. Qed.
Lemma negbET : forall b, ~~ b -> b = false. Proof. by case. Qed.
Lemma negbF : forall b : bool, b -> ~~ b = false. Proof. by case. Qed.
Lemma negbEF : forall b, ~~ b = false -> b. Proof. by case. Qed.
Lemma negbK : involutive negb.  Proof. by case. Qed.
Lemma negbE2 : forall b, ~~ ~~ b -> b.  Proof. by case. Qed.

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
  
Definition implyb b c := (~~ b || c).

Notation "b ==> c" := (implyb b c) : bool_scope.
Notation "[ ==> b1 , .. , bn => c ]" := (b1 ==> .. (bn ==> c) .. ) : bool_scope.

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

Lemma andTb : forall b, true && b = b.      Proof. done. Qed.
Lemma andFb : forall b, false && b = false. Proof. done. Qed.
Lemma andbT : forall b, b && true = b.      Proof. by case. Qed.
Lemma andbF : forall b, b && false = false. Proof. by case. Qed.
Lemma andbb : forall b, b && b = b.         Proof. by case. Qed.
Lemma andbN : forall b, b && ~~ b = false.  Proof. by case. Qed.
Lemma andNb : forall b, ~~ b && b = false.  Proof. by case. Qed.

Lemma andbC : forall b1 b2, b1 && b2 = b2 && b1. Proof. by do 2 case. Qed.

Lemma andbA : forall b1 b2 b3, [&& b1, b2 & b3] = b1 && b2 && b3.
Proof. by do 3!case. Qed.

Lemma andbCA : forall b1 b2 b3, [&& b1, b2 & b3] = [&& b2, b1 & b3].
Proof. by do 3!case. Qed.

Lemma andbAC : forall b1 b2 b3, b1 && b2 && b3 = b1 && b3 && b2.
Proof. by do 3!case. Qed.

Lemma orTb : forall b, true || b = true. Proof. done. Qed.
Lemma orFb : forall b, false || b = b.   Proof. done. Qed.
Lemma orbT : forall b, b || true = true. Proof. by case. Qed.
Lemma orbF : forall b, b || false = b.   Proof. by case. Qed.
Lemma orbb : forall b, b || b = b.       Proof. by case. Qed.
Lemma orbN : forall b, b || ~~ b = true. Proof. by case. Qed.
Lemma orNb : forall b, ~~ b || b = true. Proof. by case. Qed.

Lemma orbC : forall b1 b2, b1 || b2 = b2 || b1.
Proof. by do 2!case. Qed.

Lemma orbA : forall b1 b2 b3, [|| b1, b2 | b3] = b1 || b2 || b3.
Proof. by do 3!case. Qed.

Lemma orbCA : forall b1 b2 b3, [|| b1, b2 | b3] = [|| b2, b1 | b3].
Proof. by do 3!case. Qed.

Lemma orbAC : forall b1 b2 b3, b1 || b2 || b3 = b1 || b3 || b2.
Proof. by do 3!case. Qed.

Lemma andb_orl : forall b1 b2 b3, (b1 || b2) && b3 = b1 && b3 || b2 && b3.
Proof. by do 3!case. Qed.

Lemma andb_orr : forall b1 b2 b3, b1 && (b2 || b3) = b1 && b2 || b1 && b3.
Proof. by do 3!case. Qed.

Lemma orb_andl : forall b1 b2 b3, b1 && b2 || b3 = (b1 || b3) && (b2 || b3).
Proof. by do 3!case. Qed.

Lemma orb_andr : forall b1 b2 b3, b1 || b2 && b3 = (b1 || b2) && (b1 || b3).
Proof. by do 3!case. Qed.


(* Finally, an alternative to xorb that behaves somewhat better wrt simpl. *)

Definition addb b := if b then negb else fun b' => b'.
Notation "b1 (+) b2" := (addb b1 b2) : bool_scope.

Lemma addTb : forall b, true (+) b = ~~ b. Proof. done. Qed.
Lemma addFb : forall b, false (+) b = b. Proof. done. Qed.
Lemma addNb : forall b1 b2, ~~ b1 (+) b2 = ~~ (b1 (+) b2).
Proof. by do 2!case. Qed.
Lemma addbT : forall b, b (+) true = ~~ b. Proof. by case. Qed.
Lemma addbF : forall b, b (+) false = b. Proof. by case. Qed.
Lemma addbN : forall b1 b2, b1 (+) ~~ b2 = ~~ (b1 (+) b2).
Proof. by do 2!case. Qed.
Lemma addbb : forall b, b (+) b = false. Proof. by case. Qed.

Lemma addbC : forall b1 b2, b1 (+) b2 = b2 (+) b1.
Proof. by do 2!case. Qed.

Lemma addbA : forall b1 b2 b3, b1 (+) (b2 (+) b3) = b1 (+) b2 (+) b3.
Proof. by do 3!case. Qed.

Lemma addbCA : forall b1 b2 b3, b1 (+) (b2 (+) b3) = b2 (+) (b1 (+) b3).
Proof. by do 3!case. Qed.

Lemma addbAC : forall b1 b2 b3, b1 (+) b2 (+) b3 = b1 (+) b3 (+) b2.
Proof. by do 3!case. Qed.

Lemma addbK : forall b1, involutive (addb b1).
Proof. by do 2!case. Qed.

Lemma addKb : forall b2, involutive (addb^~ b2).
Proof. by do 2!case. Qed.

Lemma addbP : forall b1 b2, b1 (+) b2 -> ~~ b1 = b2.
Proof. by do 2!case. Qed.

Lemma andb_addl : forall b1 b2 b3, (b1 (+) b2) && b3 = b1 && b3 (+) b2 && b3.
Proof. by do 3!case. Qed.

Lemma andb_addr : forall b1 b2 b3, b1 && (b2 (+) b3) = b1 && b2 (+) b1 && b3.
Proof. by do 3!case. Qed.

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

(* Predicates, i.e., packaged functions to bool.                *)
(* We define three layers of packaging:                         *)
(*  - pred_fun A, a simple type alias for A -> bool,            *)
(*  - pred A, a concrete type encapsulating the actual lambda,  *)
(*  - predType A, an abstract structure allowing for arbitrary  *)
(*    representations, such as lists or bitvectors.             *)
(* The latter is the most flexible, and should be the preferred *)
(* way of declaring predicate parameters. The second should be  *)
(* used for defining predicates, and we provide special syntax  *)
(* for it, namely [Pred x => expression(x)]. The first should   *)
(* really only be used for recasting fixpoint definitions as    *)
(* (recursive) predicates, or to avoid the overhead of the      *)
(* constructor in effective code.                               *)
(*   We define Canonical Structures so that Coq can recast the  *)
(* first two layers into the third; conversely the last two     *)
(* layers can coerce to the first, so any predicate can be      *)
(* applied directly (and applying an explicit Pred converts to  *)
(* a beta redex). However, it is recommended to use membership  *)
(* notation "x \in p" (or "x \notin p") for abstract predicates *)
(* as this will allow Coq to infer the predType structure for   *)
(* representation types that cannot coerce to pred_fun because  *)
(* of the uniform inheritance condition.                        *)
(*   The "\in" definition and the pred-to-pred_fun coercion     *)
(* both have nosimpl tags to avoid spurrious expansions; these  *)
(* can be lifted by manually expanding the constants (in_pred   *)
(* fun_of_pred, respectively), or by rewriting with the inE or  *)
(* predE lemmas.                                                *)

Section Predicates.

Variable A : Type.

Definition pred_fun := A -> bool.

Identity Coercion apply_pred_fun : pred_fun >-> Funclass.

CoInductive pred : Type := Pred of pred_fun.

Coercion fun_of_pred p := nosimpl (let: Pred f := p in f).

Lemma predE : forall f, Pred f = f :> pred_fun. Proof. done. Qed.

Structure predType : Type := PredType {
  pred_repr :> Type;
  pred_value : pred_repr -> pred_fun
}.

Coercion pred_value : pred_repr >-> pred_fun.

Canonical Structure pred_fun_predType := PredType (fun p : pred_fun => p).

Canonical Structure pred_predType := PredType fun_of_pred.

Variable pT : predType.

Notation Local "[ 'pred' x => E ]" := (Pred (fun x => E)).

Definition pred0 := [pred x => false].
Definition predA := [pred x => true].
Definition predI (p1 p2 : pT) := [pred x => p1 x && p2 x].
Definition predU (p1 p2 : pT) := [pred x => p1 x || p2 x].
Definition predC (p : pT) := [pred x => ~~ p x].
Definition predD (p1 p2 : pT) := [pred x => ~~ p2 x && p1 x].

Definition in_pred x (p : pT) := nosimpl (p x).
Lemma inE : forall x p, in_pred x p = p x. Proof. done. Qed.

End Predicates.

Implicit Arguments pred0 [A].
Implicit Arguments predA [A].
Prenex Implicits pred0 predA predI predU predC predD.

Notation "x \in p" := (in_pred x p) : bool_scope.
Notation "x \notin p" := (~~ (x \in p)) : bool_scope.
Notation "[ 'pred' x => E ]" := (Pred (fun x => E)) : fun_scope.
Notation "[ 'pred' x : T => E ]" := (Pred (fun x : T => E))
  (only parsing) : fun_scope.

(* This section will eventually belong here; it's in eqtype for now because
   of the dependency on the old "set" type.

Section Funs.

(* More funs variants : local equality, cancellation, inj/bijection. *)

Definition dfequal A B (pA : predType A) (a : pA) (f f' : A -> B) :=
  forall x, x \in a -> f x = f' x.

Definition dcancel A B (pA : predType A) (a : pA) (f : A -> B) f' :=
  forall x, x \in a -> f' (f x) = x.

Definition dinjective A B (pA : predType A) (a : pA) (f : A -> B) := 
  forall x y, x \in a -> y \in a -> f x = f y -> x = y.

Lemma inj_dinj: forall A B (pA : predType A) (a : pA) (f : A -> B),
  injective f -> dinjective a f.
Proof. by move=> * ? *; auto. Qed.

Lemma dcan_inj : forall A B pA a f f',
  @dcancel A B pA a f f' -> dinjective a f.
Proof.
by move=> A B pA a f f' fK x y; do 2![move/fK=> Dx; rewrite -{2}Dx {Dx}] => ->.
Qed.

Definition icancel A B (pB : predType B) (b : pB) (f : A -> B) f' :=
  forall x, f x \in b -> f' (f x) = x.

Definition dbijective A B (pA : predType A) (a : pA) (f : A -> B) :=
  exists2 f', dcancel a f f' & icancel a f' f.

Definition ibijective A B (pB : predType B) (b : pB) (f : A -> B) :=
  exists2 f', icancel b f f' & dcancel b f' f.

Lemma bij_dbij : forall A B pA a f,
  bijective f -> @dbijective A B pA a f.
Proof. by move=> A B pA a f [g fK gK]; exists g => * ? *; auto. Qed.

Lemma bij_ibij : forall A B pB b f,
  bijective f -> @ibijective A B pB b f.
Proof. by move=> A B pB b f [g fK gK]; exists g => * ? *; auto. Qed.

End Funs.

*)