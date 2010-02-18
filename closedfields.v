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

(*
Definition deg (k : nat -> fF) (p : polyF) :=
  Pick 
  (fun i : 'I_(size p) => 
    nth 0 p i != 0 /\ \big[And/True]_(j < size p | j > i) (nth 0 p j == 0))%T
  (fun i => k i.+1) (k 0%N).
*)

Fixpoint deg (k : nat -> fF) (p:polyF) :=
  if p is c::q then 
    deg (fun n => 
      if n is m.+1 then k m.+2 
        else ifF (k 0%N) (k 1%N) (Equal c (Const 0))) q 
    else k O%N.

Lemma degP : forall k, 
  forall p e, qf_eval e (deg k p) = qf_eval e (k (size (eval_poly e p))).
Proof.
move=> k pf e. 
elim: pf e k; first by move=> *; rewrite size_poly0.
move=> c qf Pqf e k.
rewrite Pqf.
move: (erefl (size (eval_poly e qf))).
case: {-1}(size (eval_poly e qf))=> /= [|n].
  rewrite size_amulX => ->.
  by case c0: (eval e c == 0); rewrite // orbF.
by rewrite [eval_poly e _]/= size_amulX => ->.
Qed.

Definition isnull (k : bool -> fF) (p: polyF) := deg (fun n => k (n == 0%N)) p.
Lemma isnullP : forall k,
  forall p e, qf_eval e (isnull k p) = qf_eval e (k (eval_poly e p == 0)).
Proof. by move=> k p e; rewrite degP size_poly_eq0. Qed.


Definition lt_deg (k : bool -> fF) (p q : polyF) : fF :=
  deg (fun n => deg (fun m => k (n<m)) q) p.
Lemma lt_degP : forall k ,
  forall p q e, qf_eval e (lt_deg k p q) = 
    qf_eval e (k (size (eval_poly e p) < size (eval_poly e q))).
Proof. by move=> k p q e; rewrite !degP. Qed.

Definition same_deg (k : bool -> fF) (p q : polyF) : fF :=
  deg (fun n => deg (fun m => k (n==m)) q) p.
Lemma same_degP : forall k ,
  forall p q e, qf_eval e (same_deg k p q) = 
    qf_eval e (k (size (eval_poly e p) == size (eval_poly e q))).
Proof. by move=> k p q e; rewrite !degP. Qed.

Definition lift (p : {poly F}) := let: q := p in map Const q.
Lemma eval_lift : forall e p, eval_poly e (lift p) = p.
Proof.
move=> e; elim/poly_ind; first by rewrite /lift seq_poly0 /=.
move=> p c.
rewrite -poly_cons_def /lift polyseq_cons.
case pn0: (_==_)=> /=. 
  move=> _; rewrite polyseqC.
  case c0: (_==_)=> /=.
    move: pn0; rewrite (eqP c0) size_poly_eq0; move/eqP->. 
    by apply:val_inj=> /=; rewrite polyseq_cons // size_poly0 eqxx.
  rewrite mul0r add0r.
  by apply:val_inj=> /=; rewrite polyseq_cons // pn0.
by move->; rewrite -poly_cons_def.
Qed.

Fixpoint lead_coefF (k : term F -> fF) p :=  
  if p is c::q then 
    lead_coefF (fun l =>
      ifF (k c) (k l) (Equal l (Const 0))
    ) q 
    else k (Const 0).

Lemma edivpT (p : polyF) (k : term F * polyF * polyF -> fF) (q : polyF) : fF. 
Admitted.
Lemma edivpTP : forall k,
  (forall c qq r e,  qf_eval e (k (c,qq,r)) 
    = qf_eval e (k (Const (eval e c), lift (eval_poly e qq), lift (eval_poly e r))))
  -> forall p q e (d := (edivp (eval_poly e p) (eval_poly e q))),
    qf_eval e (edivpT p k q) = qf_eval e (k (Const d.1.1, lift d.1.2, lift d.2)).
Admitted.

Definition modpT (p : polyF) (k:polyF -> fF) (q : polyF) : fF :=
  edivpT p (fun d => k d.2) q.
Definition divpT (p : polyF) (k:polyF -> fF) (q : polyF) : fF :=
  edivpT p (fun d => k d.1.2) q.
Definition scalpT (p : polyF) (k:term F -> fF) (q : polyF) : fF :=
  edivpT p (fun d => k d.1.1) q.
Definition dvdpT (p : polyF) (k:bool -> fF) (q : polyF) : fF :=
  modpT p (isnull k) q.


Fixpoint loop n (pp qq : {poly F}) {struct n} :=
  if pp %% qq == 0 then qq 
    else if n is n1.+1 then loop n1 qq (pp %% qq)
        else pp %% qq.
Fixpoint loopT pp k n qq {struct n} :=
  modpT pp (isnull 
    (fun b => if b 
      then (k qq) 
      else (if n is n1.+1 
        then modpT pp (loopT qq k n1) qq 
        else modpT pp k qq)
    )
  ) qq.

Lemma loopP: forall k,
  (forall p e, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p))))
  -> forall n p q e, qf_eval e (loopT p k n q) = 
    qf_eval e (k (lift (loop n (eval_poly e p) (eval_poly e q)))).
Proof.
move=> k Pk n p q e.
elim: n p q e => /=.
  move=> p q e.
  rewrite edivpTP; last by move=>*; rewrite !isnullP eval_lift.
  rewrite isnullP eval_lift.
  case: (_ == 0); first by rewrite Pk.
  by rewrite edivpTP; last by move=>*; rewrite Pk.
move=> m Pm p q e.
rewrite edivpTP; last by move=>*; rewrite !isnullP eval_lift.
rewrite isnullP eval_lift.
case: (_ == 0); first by rewrite Pk.
by rewrite edivpTP; move=>*; rewrite ?Pm !eval_lift.
Qed.

Definition gcdpT (p:polyF) k (q:polyF) : fF :=
  let aux p1 k q1 := isnull 
    (fun b => if b 
      then (k q1) 
      else (deg (fun n => (loopT p1 k n q1)) p1)) p1
    in (lt_deg (fun b => if b then (aux q k p) else (aux p k q)) p q). 

Lemma gcdpTP : forall k,
  (forall p e, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p))))
    -> forall p q e, qf_eval e (gcdpT p k q) = qf_eval e (k (lift (gcdp (eval_poly e p) (eval_poly e q)))).
Proof.
move=> k Pk p q e.
rewrite /gcdpT lt_degP.
case lqp: (_ < _).  
  rewrite isnullP.
  case q0: (_ == _); first by rewrite Pk (eqP q0) gcdp0.
  rewrite degP loopP; first by rewrite /gcdp lqp q0.
  by move=> e' p'; rewrite Pk.
rewrite isnullP.
case p0: (_ == _); first by rewrite Pk (eqP p0) gcd0p.
rewrite degP loopP; first by rewrite /gcdp lqp p0.
by move=> e' q'; rewrite Pk.
Qed.

Fixpoint gcdpTs k (ps : seq polyF) : fF :=
  if ps is p::pr then gcdpTs (gcdpT p k) pr else k [::Const 0].
Lemma gcdpTsP : forall k,
  (forall p e, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p))))
  -> forall ps e, qf_eval e (gcdpTs k ps) = qf_eval e (k (lift (\big[@gcdp _/0%:P]_(i <- ps)(eval_poly e i)))).
Proof.
move=> k Pk ps e.
elim: ps k Pk; first by move=> p Pk; rewrite /= big_nil Pk /= mul0r add0r.
move=> p ps Pps /= k Pk /=.
rewrite big_cons Pps.
  by rewrite gcdpTP; first by rewrite eval_lift.
by move=>  p' e'; rewrite !gcdpTP; first by rewrite Pk !eval_lift .
Qed.


(* begin to be put in poly *)

Definition coprimep (p q :  {poly F}) := size (gcdp p q) == 1%N.
Lemma coprime1p: forall p, coprimep 1 p.
Admitted.

(* "gdcop Q P" is the Greatest Divisor of P which is coprime to Q *)
(* if P null, we pose that gdcop returns 1 *)

Fixpoint gdcop_rec (q p : {poly F}) n :=
  if n is m.+1 then
    if coprimep p q then p
      else gdcop_rec q (p %/ (gcdp p q)) m
    else 1.
Definition gdcop q p := gdcop_rec q p (size p).

CoInductive gdcop_spec q p : {poly F} -> Type :=
  GdcopSpec r of (r %| p) & (coprimep r q) 
  & (forall d,  p != 0 -> d %| p -> coprimep d q -> d %| r) : gdcop_spec q p r.

Lemma divp_dvd : forall (p d : {poly F}), d %| p ->  p %/ d %| p.
Proof.
move=> p d dp.
apply/dvdpPc.
have := divp_spec p d.
move: (dp); rewrite {1}/dvdp; move/eqP->.
rewrite addr0.
set c := (scalp _ _)=> f.
exists c.
exists d.
by rewrite scalp_id /= f  mulrC.
Qed.
 

Lemma gdcop_recP : forall (q p : {poly F}) n, 
  size p <= n -> gdcop_spec q p (gdcop_rec q p n).
Proof.
move=> q p n.
elim: n p => [p | n Pn p].
  rewrite leqn0 size_poly_eq0; move/eqP=> p0.
  constructor; rewrite ?p0 ?dvdp0 ?coprime1p //=.
  by move=> d; rewrite eqxx.
move=> sp /=.
case cpq: (coprimep _ _).
  by constructor; rewrite ?dvdpp // cpq.
set p' := _ %/ _.
have sp' : size p' <= n; first admit.
case (Pn _ sp').
move=> r' dr'p' cr'q maxr'.
constructor=> //=.
  apply: (dvdp_trans dr'p').
  by rewrite divp_dvd // dvdp_gcdl.
move=> d p0 dp cdq.
apply: maxr'; last by rewrite cdq.
  admit.
admit.
Qed.

Lemma gdcopP : forall q p, gdcop_spec q p (gdcop q p).
Proof. by move=> q p; rewrite /gdcop; apply: gdcop_recP. Qed.

Lemma coprimep_dvd : forall p q,
  reflect (exists d, (d %| gcdp p q) && (size d > 1))  (~~ coprimep p q).
Admitted.

Lemma dvdp_gdco : forall (p q d : {poly F}), 
  p != 0 -> size d == 2%N ->
  (d %| p) && ~~(d %| q) = (d %| (gdcop q p)).
Proof.
move=> p q d p0 sd.
apply/idP/idP.
  case/andP=> dp dq.
  case: gdcopP=> r rp crq maxr.
  apply: maxr=> //.
  admit.
case: gdcopP=> r rp crq maxr dr.
rewrite (dvdp_trans dr) //=.
move: crq.
apply: contraL=> dq.
apply/coprimep_dvd.
exists d.
by rewrite dvdp_gcd dr dq //= (eqP sd).
Qed.

(* end to be put in poly *)

Variable gdcopT : polyF -> (polyF -> fF) -> (polyF) -> fF.
Lemma gdcopTP : forall k,
  (forall p e, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p))))
    -> forall p q e, qf_eval e (gdcopT p k q) = qf_eval e (k (lift (gdcop (eval_poly e p) (eval_poly e q)))).
Admitted.


Definition ex_elim_seq (ps : seq polyF) (q : polyF) :=
  (gcdpTs (gdcopT q (deg (fun n => Bool (n > 1%N)))) ps).
Lemma ex_elim_seqP :
  forall ps q e,
    let gp := (\big[@gcdp _/0%:P]_(i <- ps)(eval_poly e i)) in
      qf_eval e (ex_elim_seq ps q) = (size (gdcop (eval_poly e q) gp) > 1).
Proof.
by do ![rewrite (gcdpTsP,gdcopTP,degP,eval_lift) //= | move=> * //=].
Qed.

End ClosedFieldTheory.
