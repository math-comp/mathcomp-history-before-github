Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import tuple finfun bigops ssralg poly.

Import GRing.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.

Module ClosedField.

(* Axiom == all non-constant monic polynomials have a root *)
Definition axiom (R : Ring.type) :=
  forall n (P : nat -> R), n > 0 ->
   exists x : R, x ^+ n = \sum_(i < n) P i * (x ^+ i).

Record class_of (F : Type) : Type :=
  Class {base :> Field.class_of F; _ : axiom (Ring.Pack base F)}.

Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.

Definition pack T b0 (m0 : axiom (@Ring.Pack T b0 T)) :=
  fun bT b & phant_id (Field.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

(* There should eventually be a constructor from polynomial resolution *)
(* that builds the DecidableField mixin using QE.                      *)

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion zmodType cT := Zmodule.Pack (class cT) cT.
Coercion ringType cT := Ring.Pack (class cT) cT.
Coercion comRingType cT := ComRing.Pack (class cT) cT.
Coercion unitRingType cT := UnitRing.Pack (class cT) cT.
Coercion comUnitRingType cT := ComUnitRing.Pack (class cT) cT.
Coercion idomainType cT := IntegralDomain.Pack (class cT) cT.
Coercion fieldType cT := Field.Pack (class cT) cT.
(* Coercion decFieldType cT := DecidableField.Pack (class cT) cT. *)

End ClosedField.

Canonical Structure ClosedField.eqType.
Canonical Structure ClosedField.choiceType.
Canonical Structure ClosedField.zmodType.
Canonical Structure ClosedField.ringType.
Canonical Structure ClosedField.unitRingType.
Canonical Structure ClosedField.comRingType.
Canonical Structure ClosedField.comUnitRingType.
Canonical Structure ClosedField.idomainType.
Canonical Structure ClosedField.fieldType.
(* Canonical Structure ClosedField.decFieldType. *)

Bind Scope ring_scope with ClosedField.sort.

Section ClosedFieldTheory.

Variable F : ClosedField.type.

Lemma solve_monicpoly : ClosedField.axiom F.
Proof. by case: F => ? []. Qed.
  
Notation fF := (formula F).

Definition ifF (th el f: fF) : fF :=
  ((f /\ th) \/ ((~ f) /\ el))%T.

Lemma ifFP : forall th el f e, qf_eval e (ifF th el f) = 
  (fun e f => if f then qf_eval e th else qf_eval e el) e (qf_eval e f).
Proof.
move=> th el f e; rewrite /ifF /=. 
case: (qf_eval e f); rewrite //=.
by case: (qf_eval _ _).
Qed.

Definition polyF := seq (term F).
Lemma eval_poly : seq F -> polyF -> {poly F}.
Admitted.

Lemma deg (k : nat -> fF) :  polyF -> fF.
Admitted.
Lemma degP : forall k P,
  (forall n e, qf_eval e (k n) = P e n)
  -> forall p e, qf_eval e (deg k p) = P e (size (eval_poly e p)).  
Admitted.


Lemma leq_deg (k : fF -> fF) : polyF -> polyF -> fF.
Admitted.
Lemma leq_degP : forall k P,
  (forall b e, qf_eval e (k b) = P e (qf_eval e b))
    -> forall p q e, qf_eval e (leq_deg k p q) = P e (size (eval_poly e p) < size (eval_poly e q)).
Admitted.
(* Lemma same_deg (p: seq (term F)) (k : fF -> fF) :  seq (term F) -> fF. *)
(* Admitted. *)
(* Lemma same_degP : forall p (k:contF (@qf_eval _)) q e,  *)
(*   qf_eval e (same_deg p k q) =  *)
(*   (fun e q => (Pcont k) e (size (eval_poly e p) == size q)) e (eval_poly e q). *)
(* Admitted. *)
(* Canonical Structure contF_same p (k:contF _) := ContF (same_degP p k). *)

Lemma isnull (k : fF -> fF) :  polyF -> fF.
Admitted.
Lemma isnullP : forall k P,
  (forall b e, qf_eval e (k b) = P e (qf_eval e b))
    -> forall p e, qf_eval e (isnull k p) = P e (eval_poly e p == 0).
Admitted.


Lemma remp (p : polyF) (k:polyF -> fF) :  polyF -> fF.
Admitted.
Lemma rempP : forall k P,
  (forall p e, qf_eval e (k p) = P e (eval_poly e p))
    -> forall p q e, qf_eval e (remp p k q) = P e ((eval_poly e p) %% (eval_poly e q)).
Admitted.

Fixpoint loop n (pp qq : {poly F}) {struct n} :=
  if pp %% qq == 0 then qq 
    else if n is n1.+1 then loop n1 qq (pp %% qq)
        else pp %% qq.
Fixpoint loopT pp k n qq {struct n} :=
  remp pp (isnull (ifF (k qq) (if n is n1.+1 then remp pp (loopT qq k n1) qq 
        else remp pp k qq))) qq.

Lemma loopP: forall k P,
  (forall p e, qf_eval e (k p) = P e (eval_poly e p))
    -> forall n p q e, qf_eval e (loopT p k n q) = 
      (fun e q => P e (loop n (eval_poly e p) q)) e (eval_poly e q).
Proof.
move=> k P Pk.
move=> n p q e.
elim: n p q e => /=.
  move=> p q e.
  rewrite  (rempP (isnullP (ifFP (k q) (remp p k q)) : 
    forall _ _, _ = (fun _ f =>  if f == 0 then _ else _) _ _)).
  by case: (eval_poly e p %% eval_poly e q == 0); rewrite ?Pk ?(rempP Pk).
move=> n1 Pn1 p q e.
rewrite (rempP (isnullP (ifFP (k q) (remp p (loopT q k n1)  q)) : 
  forall _ _, _ = (fun _ f =>  if f == 0 then _ else _) _ _)).
case: (eval_poly e p %% eval_poly e q == 0); first by rewrite Pk.
by rewrite (rempP (Pn1 q : forall r _, _ = (fun _ r => _ ( _ r)) _ _)).
Qed.

Definition gcdpT p k q : fF :=
  let aux p1 k q1 := isnull (ifF (k q1) (deg (fun n => (loopT p1 k n q1)) p1)) p1
    in (leq_deg (ifF (aux q k p) (aux p k q)) p q). 

Lemma gcdpP : forall k P,
  (forall p e, qf_eval e (k p) = P e (eval_poly e p))
    -> forall p q e, qf_eval e (gcdpT p k q) = P e (gcdp (eval_poly e p) (eval_poly e q)).
Proof.
move=> k P Pk.
move=> p q e.
rewrite /gcdpT.
set isn1 := isnull _ _.
set isn2 := isnull _ _.
rewrite (leq_degP (ifFP (isn1) (isn2))).
case lqp: (_ < _).
  rewrite /isn1.
  rewrite (isnullP (ifFP (k p) (deg ((loopT q k)^~ p) q)) q).
  case q0: (eval_poly e q == 0); first by rewrite Pk (eqP q0) gcdp0.
  rewrite (degP (fun n e => (loopP Pk) n q p e)).
  by rewrite /loop /gcdp lqp q0 /=.
rewrite /isn2.
rewrite (isnullP (ifFP (k q) (deg ((loopT p k)^~ q) p)) p).
case p0: (eval_poly e p == 0); first by rewrite Pk (eqP p0) gcd0p.
rewrite (degP (fun n e => (loopP Pk) n p q e)).
by rewrite /loop /gcdp lqp p0 /=.
Qed.
   

Fixpoint gcdpTs k ps : fF :=
  if ps is p::pr then gcdpTs (gcdpT p k) pr else k [::Const 1].


End ClosedFieldTheory.
