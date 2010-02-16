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
  
Notation fF := (formula  F).

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
Fixpoint eval_poly (e:seq F) pf := 
  if pf is c::qf then (eval_poly e qf)*'X + (eval e c)%:P else 0.


Fixpoint deg (k : nat -> fF) (p:polyF) :=
  if p is c::q then 
    deg (fun n => if n is m.+1 then k m.+2 else ifF (k 0%N) (k 1%N) (Equal c (Const 0))) q 
    else k O%N.
Lemma degP : forall k P,
  (forall n e, qf_eval e (k n) = P e n)
  -> forall p e, qf_eval e (deg k p) = P e (size (eval_poly e p)).
Proof.
move=> k P Pk.
move=> pf e. 
elim: pf e P k Pk; first by move=> e P k Pk; rewrite Pk size_poly0.
move=> c qf Pqf e P k Pk.
rewrite [deg _ _ ]/=. 
set kn := (fun n => _).
have Pkn : forall P, (forall (n : nat) (e : seq F), qf_eval e (k n) = P e n) ->
        forall n e, qf_eval e (kn n) = 
          (if n is m.+1 then P e n.+1 else if eval e c == 0 then P e 0%N else P e 1%N).
  move=> P' Pk' n e'.
  elim: n=> /=; first by case: (eval e' c == 0)=> /=; rewrite ?orbF Pk'.
  by move=> n'; rewrite Pk'.
rewrite (Pqf e _ kn (Pkn _ Pk)).
move: (erefl (size (eval_poly e qf))).
case: {-1}(size (eval_poly e qf)).
  move=> qf0; rewrite [eval_poly e _]/= size_amulX qf0.
  by case c0: (eval e c == 0).
move=> n sqf.
by rewrite [eval_poly e _]/= size_amulX sqf.
Qed.


Fixpoint isnull (k : fF -> fF) (p: polyF) : fF :=
  if p is a::q 
    then isnull (ifF (k (Equal a (Const 0))) (k (Bool false))) q
    else k (Bool true).
Lemma isnullP : forall k P,
  (forall b e, qf_eval e (k b) = P e (qf_eval e b))
    -> forall p e, qf_eval e (isnull k p) = P e (eval_poly e p == 0).
Proof.
move=> k P Pk p e.
elim: p e k P Pk => /=; first by move=> e k P Pk; rewrite Pk eqxx.
move=> a q Pq e k P Pk.
rewrite (Pq e _ _ (ifFP (k (Equal a (Const 0))) (k (Bool false)))) /=.
rewrite -[_*'X+_ == _]size_poly_eq0 size_amulX.
case q0: (eval_poly e q == 0); rewrite Pk /=.
  by case a0 : (eval e a == 0); rewrite (eqP q0) size_poly0.
by rewrite size_poly_eq0 q0 /=.
Qed.

Fixpoint leq_deg (k : fF -> fF) (p q : polyF) : fF :=
  if p is a::p' then  
    if q is b::q' then isnull (ifF (k (Bool false)) (leq_deg k p' q')) q
      else k (Bool false)
    else k (Bool true).
Lemma leq_degP : forall k P,
  (forall b e, qf_eval e (k b) = P e (qf_eval e b))
    -> forall p q e, qf_eval e (leq_deg k p q) = P e (size (eval_poly e p) < size (eval_poly e q)).
Admitted.

Lemma same_deg (k : fF -> fF) (p q : polyF) : fF.
Admitted.
Lemma same_degP : forall k P,
  (forall b e, qf_eval e (k b) = P e (qf_eval e b))
  -> forall p q e, qf_eval e (same_deg k p q) = P e (size (eval_poly e p) == size (eval_poly e q)).
Admitted.

Lemma remp (p : polyF) (k:polyF -> fF) (q : polyF) : fF.
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

Definition gcdpT (p:polyF) k (q:polyF) : fF :=
  let aux p1 k q1 := isnull (ifF (k q1) (deg (fun n => (loopT p1 k n q1)) p1)) p1
    in (leq_deg (ifF (aux q k p) (aux p k q)) p q). 

Lemma gcdpP : forall k P,
  (forall (p:polyF) e, qf_eval e (k p) = P e (eval_poly e p))
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
   

Fixpoint gcdpTs k (ps : seq polyF) : fF :=
  if ps is p::pr then gcdpTs (gcdpT p k) pr else k [::Const 0].
Lemma gcdpTsP : forall k P,
  (forall p e, qf_eval e (k p) = P e (eval_poly e p))
    -> forall ps e, qf_eval e (gcdpTs k ps) = P e (\big[@gcdp _/0%:P]_(i <- ps)(eval_poly e i)).
Proof.
move=> k P Pk ps.
elim: ps k P Pk; first by move=> k P Pk e; rewrite Pk /= mul0r add0r big_nil.
move=> p ps Pps k P Pk e /=.
rewrite (Pps _ _ (gcdpP Pk p : forall q _, _ = (fun _ q => _ (_  q)) _ (_ q))) /=.
by rewrite big_cons.
Qed.


Definition ex_elim_seq (p : seq polyF) (q : polyF) :=
  Not (gcdpTs (fun d => gcdpT d (same_deg (@id _) d) q) p).
Lemma ex_elim_seqP :
  forall ps q e,
    let ge := (\big[@gcdp _/0%:P]_(i <- ps)(eval_poly e i)) in
      qf_eval e (ex_elim_seq ps q) = (size ge != size (gcdp ge (eval_poly e q))).
Proof.
move=> ps q e /=.
set dgcd := (fun d =>  _).
have dP : forall d e, qf_eval e (dgcd d) 
  = (size (eval_poly e d) == size (gcdp (eval_poly e d) (eval_poly e q))).
  move=> d e'; rewrite /dgcd.
  have sP := @same_degP (@id _) (fun _ => @id _) (fun b e => erefl (qf_eval e b)) d.
  by rewrite (@gcdpP (same_deg id d) (fun e q => (size (eval_poly e d) == size q)) sP).
by rewrite (gcdpTsP (dP : forall d _,
  _ = (fun _ (d:{poly F}) => (size d == size (gcdp d _))) _ (_ d))).
Qed.



End ClosedFieldTheory.
