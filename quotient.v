Require Import ssreflect ssrfun ssrbool eqtype choice.
Require Import bigops ssralg.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Section EquivProps. (* To be moved to ssrbool.v *)

Lemma left_trans : forall T0 (e:rel T0), 
  symmetric e -> transitive e -> left_transitive e.
Proof.
move=> T0 e sym tr x y exy z; apply/idP/idP; last do [move/tr:exy; exact].
move:exy; rewrite sym; move/tr; exact.
Qed.

End EquivProps.



Section Representant.

(* pick is not a good name, to be changed, *)
(* or encapsulated in a module *)
Record reprEquivChoice (T : eqType) : Type := ReprChoice {
  pick :> T -> option T;
  _ : forall x, obind pick (pick x) = pick x
}.

End Representant.




Section Quotient.

Variable T : eqType.
Variable p : reprEquivChoice T.

Lemma pick_id: forall x, obind p (p x) = p x.
Proof. by case: p. Qed.



(* Let's define the PER which pick represents *)
Definition equiv x y := (p x == p y) && (p x != None).

Lemma equiv_sym : symmetric equiv.
Proof.
move=> x y; rewrite /equiv eq_sym. 
by case epxy: (p y==p x); first by rewrite (eqP epxy).
Qed.

Lemma equiv_trans : transitive equiv.
Proof. by move=> x y z; rewrite /equiv; case/andP; move/eqP=>->->. Qed.

Definition equiv_left_trans := left_trans equiv_sym equiv_trans.


Reserved Notation "x === y" (at level 70, no associativity).
Local Notation "x === y" := (equiv x y).



(* properties of the PER's domain *)
Reserved Notation "\dom x" (at level 2, format "\dom  x").
Local Notation "\dom x" :=  (x === x).

Lemma dom_coincide : forall x, \dom x = ((p x) != None).
Proof. by move=> x; rewrite /equiv eqxx andTb. Qed.

Lemma dom_equivl : forall x y, x === y -> \dom x.
Proof. by move=> x y exy; apply: (@equiv_trans y)=>//; rewrite equiv_sym. Qed.

Lemma dom_equivr : forall x y, x === y -> \dom y.
Proof. by move=> x y; rewrite equiv_sym; apply: dom_equivl. Qed.

Record dom : Type := Dom { 
  dom_elt :> T;
  _ : \dom dom_elt 
}.

Canonical Structure dom_subType := 
  Eval hnf in [subType for dom_elt by dom_rect]. 

Lemma in_dom : forall x:dom, \dom x.
Proof. by case. Qed.



(* canon is the non monadic version of pick, when we are in dom *)
Definition canon x := odflt x (p x).

Lemma pick_dom : forall x:dom, p x = Some (canon x).
Proof.
move=> x. case px: (p x); first by rewrite /canon /odflt /oapp /= px.
by move:(in_dom x); rewrite dom_coincide px.
Qed.

Lemma p_canon : forall x, p (canon x) = p x.
Proof.
move=> x; rewrite /canon; have:= pick_id x.
by case px:(p x)=> [/= s|]=> [->|]; last by rewrite px.
Qed.

Lemma canon_id : forall x, canon (canon x) = canon x.
Proof. by move=> x; rewrite /canon p_canon; case:(p x). Qed. 


Lemma canon_dom_lemma : forall x : dom, \dom (canon x).
Proof. by move=> x; rewrite /equiv p_canon -dom_coincide eqxx in_dom. Qed.
Canonical Structure canon_dom x := Dom (canon_dom_lemma x).


Lemma equiv_elim: forall x y:dom, (x === y) = (canon x == canon y).
Proof. 
move=> x y; rewrite /equiv -dom_coincide in_dom !andbT.
by rewrite !pick_dom; apply/eqP/eqP=>[[]|->//].
Qed.

Lemma canon_eliml: forall x y:dom, (canon x === y) = (x === y).
Proof. by move=> x y; rewrite !equiv_elim canon_id. Qed.

Lemma canon_elimr: forall x y:dom, (x === canon y) = (x === y).
Proof. by move=> x y; rewrite !equiv_elim canon_id. Qed.



(* quotient theory *)
Record quotient := Quotient {
  repr :> T;
  _ : (canon repr == repr) && (\dom repr)
}.

Canonical Structure quotient_subType :=  
  Eval hnf in [subType for repr by quotient_rect]. 
Definition quotient_eqMixin := Eval hnf in [eqMixin of quotient by <:]. 
Canonical Structure quotient_eqType := Eval hnf in EqType quotient_eqMixin. 


Lemma quot_dom : forall x: quotient, \dom x.
Proof. by case=> r i; move/andP:(i)=>[]. Qed.
Canonical Structure quotient_dom (x:quotient) := Dom (quot_dom x).

Lemma quot_canon : forall x:quotient, canon x = x.
Proof. by case=> r i; apply/eqP; move/andP:(i)=>[]. Qed.

Lemma quotientP: forall (x y:quotient), (x === y) = (x == y).
Proof. by move=> x y; rewrite equiv_elim !quot_canon. Qed.

Lemma equivP: forall (x y:quotient), reflect (x = y) (x === y).
Proof. by move=> x y; rewrite quotientP; apply:(iffP eqP). Qed.

Lemma canon_axiomq : forall x:dom, 
  (canon (canon x) == canon x) && (\dom (canon x)).
Proof. by move=> x; rewrite canon_id eqxx in_dom. Qed.
Canonical Structure canon_quotient x := Quotient (canon_axiomq x).

Lemma quotient_axiomq : forall (x:quotient),
  (canon x == x) && (\dom x).
Proof. by case. Qed.
Canonical Structure quotient_quotient x := Quotient (quotient_axiomq x).
  

(* Canonicals Structures to eliminate canon *)
(* I think this could really be improved (sped up) *)
(* by using some technics extracted from quote.v  *)

Record rew : Type := Rew {
  rew_elt :> dom;
  modulo_elt : dom;
  _ : rew_elt === modulo_elt
}.

Lemma compat_mod: forall x:rew, x === (modulo_elt x).
Proof. by case. Qed.

Lemma rew_mod: forall x:rew,  canon x = canon (modulo_elt x):>T.
Proof. by move=> x; apply/eqP; rewrite -equiv_elim compat_mod. Qed.

(* key point to simplify canon *)
Lemma canon_compat : forall x:rew,  canon x === modulo_elt x.
Proof. by move=> x; rewrite canon_eliml compat_mod.  Qed.
Canonical Structure canon_rew x := Rew (canon_compat x).

(* base case *)
Canonical Structure dom_compat x := Rew (in_dom x).



(* Now, two lemmas used to do the simplification : *)

(* In this state of the work, we need to explicitly simplify *)
(* the expression berfore and after rewriting / applying them  *)
(* This could be solved by using some techniques shown in quote.v *)

(* Note that they work on dom elements, not on quotiented ones *)
(* so, for now, one needs to apply val_inj before using them *)

Lemma rew_equiv : forall  (x:rew) (y:rew),
  (x === y) = ((modulo_elt x) === (modulo_elt y)).
Proof.
move=> [x tx rx] [y ty] /=. rewrite !equiv_elim. move/eqP=><-.
by congr(_==_); apply/eqP; rewrite -equiv_elim.
Qed.

Lemma quot_inj : forall (x:rew) (y:rew) ,
  (modulo_elt x) = (modulo_elt y):>T -> x === y.
Proof. by move=> x y Mxy; rewrite rew_equiv Mxy in_dom.  Qed.



(* This should be generalized in the case of n-ary operatores, *)
(* maybe in the same way as done in quote *)

Definition compat1 (op : T -> T) := forall (x : dom) (xq : quotient),
  x === xq -> op x === op xq.
Definition compat2 (op : T -> T -> T) := forall (x y : dom) (xq yq : quotient),
  x === xq -> y === yq -> op x y === op xq yq.

Lemma compat_mod_op1 : forall op : T -> T, compat1 op -> 
  forall x : rew, op x === op (modulo_elt x).
Proof.
move=> op op_compat x. pose xq := @Quotient (canon x) (canon_axiomq _).
rewrite (@equiv_trans (op xq)) //; last rewrite equiv_sym; apply: op_compat; 
  by rewrite canon_elimr ?in_dom // equiv_sym; apply : compat_mod.
Qed.

Lemma compat_mod_op2 : forall op : T -> T -> T, compat2 op -> 
  forall x y : rew, op x y === op (modulo_elt x) (modulo_elt y).
Proof.
move=> op op_compat x y. 
pose xq := @Quotient (canon x) (canon_axiomq _).
pose yq := @Quotient (canon y) (canon_axiomq _).
rewrite (@equiv_trans (op xq yq)) //; last rewrite equiv_sym; apply: op_compat;
  by rewrite canon_elimr ?in_dom // equiv_sym; apply : compat_mod.
Qed.


Section PickEquivCorresp.

Variable e : rel T.


Definition equiv_canon := forall x:dom, e (canon x) x.
Definition equiv_canonN := forall x y:dom, (e (canon x) (canon y)) -> (x === y).

Hypothesis Se : symmetric e.
Hypothesis Te : transitive e.
Hypothesis eC : equiv_canon.
Hypothesis eCN : equiv_canonN.

Lemma equiv_coincide :  forall x y : dom, (x === y) =  e x y.
Proof. 
move=> x y. apply/idP/idP=> [|Hxy]; last first.
   by apply: eCN; apply:(Te (eC x)); rewrite Se; apply:(Te (eC y)); rewrite Se.
by rewrite equiv_elim; move/eqP=>HC; apply: (Te _ (eC y)); rewrite Se -HC eC.
Qed.

End PickEquivCorresp.

End Quotient.



Section QuotientChoiceType.

Definition quotient_choiceMixin (T:choiceType) p := 
  Eval hnf in [choiceMixin of @quotient T p by <:]. 
Canonical Structure quotient_choiceType (T:choiceType) p := 
  Eval hnf in ChoiceType (@quotient_choiceMixin T p).

End QuotientChoiceType.

