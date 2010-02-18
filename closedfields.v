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
Definition sizeT (k : nat -> fF) (p : polyF) :=
  Pick 
  (fun i : 'I_(size p) => 
    nth 0 p i != 0 /\ \big[And/True]_(j < size p | j > i) (nth 0 p j == 0))%T
  (fun i => k i.+1) (k 0%N).
*)

Fixpoint sizeT (k : nat -> fF) (p:polyF) :=
  if p is c::q then 
    sizeT (fun n => 
      if n is m.+1 then k m.+2 
        else ifF (k 0%N) (k 1%N) (Equal c (Const 0))) q 
    else k O%N.

Lemma sizeTP : forall k, 
  forall p e, qf_eval e (sizeT k p) = qf_eval e (k (size (eval_poly e p))).
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

Definition isnull (k : bool -> fF) (p: polyF) := sizeT (fun n => k (n == 0%N)) p.
Lemma isnullP : forall k,
  forall p e, qf_eval e (isnull k p) = qf_eval e (k (eval_poly e p == 0)).
Proof. by move=> k p e; rewrite sizeTP size_poly_eq0. Qed.


Definition lt_sizeT (k : bool -> fF) (p q : polyF) : fF :=
  sizeT (fun n => sizeT (fun m => k (n<m)) q) p.

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

Fixpoint lead_coefT (k : term F -> fF) p :=  
  if p is c::q then 
    lead_coefT (fun l =>
      ifF (k c) (k l) (Equal l (Const 0))
    ) q 
    else k (Const 0).

Lemma lead_coefTP : forall k,
  (forall x e, qf_eval e (k x) = qf_eval e (k (Const (eval e x))))
  -> forall p e, qf_eval e (lead_coefT k p)
    = qf_eval e (k (Const (lead_coef (eval_poly e p)))).
Proof.
move=> k Pk p e.
elim: p k Pk => /=; first by move=> *; rewrite lead_coef0.
move=> a p' Pp' k Pk. 
rewrite Pp'; last by move=> *; rewrite //= -Pk.
rewrite ifFP /= lead_coef_eq0.
case p'0: (_ == _).
  by rewrite (eqP p'0) mul0r add0r lead_coefC -Pk.
rewrite lead_coef_addl ?lead_coef_mulX //.
rewrite polyseqC size_mul_id ?p'0 //.
  rewrite size_polyX addnC /=.
  case: (_ == _)=> //=.
  by rewrite ltnS lt0n size_poly_eq0 p'0.
by rewrite -size_poly_eq0 size_polyX.
Qed.


Fixpoint amulXnT (a:term F) (n:nat) : polyF:=
  if n is n'.+1 then (Const 0)::(amulXnT a n') else [::a].

Lemma eval_amulXnT : forall a n e, 
  eval_poly e (amulXnT a n) = (eval e a)%:P * 'X^n.
Proof.
move=> a n e.
elim: n=> [|n] /=; first by rewrite expr0 mulr1 mul0r add0r.
by move->; rewrite addr0 -mulrA -exprSr.
Qed.

Fixpoint sumpT (p q : polyF) :=
  if p is a::p' then
    if q is b::q' then (Add a b)::(sumpT p' q')
      else p
    else q.

Lemma eval_sumpT : forall p q e,
  eval_poly e (sumpT p q) = (eval_poly e p) + (eval_poly e q).
Proof.
move=> p q e.
elim: p q=> [|a p Hp] q /=; first by rewrite add0r.
case: q=> [|b q] /=; first by rewrite addr0.
rewrite Hp mulr_addl -!addrA; congr (_+_).
rewrite polyC_add addrC -addrA; congr (_+_).
by rewrite addrC.
Qed.  

Fixpoint mulpT (p q : polyF) :=
  if p is a::p' then sumpT (map (Mul a) q) (Const 0::(mulpT p' q)) else [::].

Lemma eval_mulpT : forall p q e,
  eval_poly e (mulpT p q) = (eval_poly e p) * (eval_poly e q).
Proof.
move=> p q e.
elim: p q=> [|a p Hp] q /=; first by rewrite mul0r.
rewrite eval_sumpT /= Hp addr0 mulr_addl addrC mulrAC; congr (_+_).
elim: q=> [|b q Hq] /=; first by rewrite mulr0.
by rewrite Hq polyC_mul mulr_addr mulrA.
Qed.

Fixpoint edivp_rec_loopT (q : polyF) sq cq (k : term F * polyF * polyF -> fF)
  (c : term F) (qq r : polyF) (n : nat) {struct n}:=
  sizeT (fun sr => 
    if sr < sq then k (c, qq, r) else 
      lead_coefT (fun lr =>
        let m := amulXnT lr (sr - sq) in
        let c1 := Mul cq c in
        let qq1 := sumpT (mulpT qq [::cq]) m in
        let r1 := sumpT (mulpT r ([::cq])) (mulpT ([::Const (-1)]) (mulpT m q)) in
        if n is n1.+1 then edivp_rec_loopT q sq cq k c1 qq1 r1 n1
          else k (c1, qq1, r1)
      ) r
  ) r.
  
Fixpoint edivp_rec_loop (q : {poly F}) sq cq 
  (n : nat) (c : F) (qq r : {poly F}) {struct n} :=
    if size r < sq then (c, qq, r) else
    let m := (lead_coef r)%:P * 'X^(size r - sq) in
    let c1 := cq * c in
    let qq1 := qq * cq%:P + m in
    let r1 := r * cq%:P - m * q in
    if n is n1.+1 then edivp_rec_loop q sq cq n1 c1 qq1 r1 else (c1, qq1, r1).

Lemma edivp_rec_loopTP : forall k,
  (forall c qq r e,  qf_eval e (k (c,qq,r)) 
    = qf_eval e (k (Const (eval e c), lift (eval_poly e qq), lift (eval_poly e r))))
  -> forall q sq cq c qq r n e 
    (d := edivp_rec_loop (eval_poly e q) sq (eval e cq) n
      (eval e c) (eval_poly e qq) (eval_poly e r)),
    qf_eval e (edivp_rec_loopT q sq cq k c qq r n) 
    = qf_eval e (k (Const d.1.1, lift d.1.2, lift d.2)).
Proof.
move=> k Pk q sq cq c qq r n e /=.
elim: n c qq r k Pk e.
  move=> c qq r k Pk e; rewrite sizeTP.
  case ltrq : (_<_); first by rewrite /= ltrq /= -Pk.
  rewrite lead_coefTP.
    rewrite Pk ?(eval_mulpT,eval_amulXnT,eval_sumpT) //=. 
    by rewrite ltrq //= ?(mul0r,add0r) polyC_opp mulNr mul1r.
  move=> a p; rewrite Pk; symmetry; rewrite Pk. 
  by rewrite ?(eval_mulpT,eval_amulXnT,eval_sumpT).
move=> n Pn c qq r k Pk e.
rewrite sizeTP.
case ltrq : (_<_); first by rewrite /= ltrq Pk.
rewrite lead_coefTP.
  rewrite Pn ?(eval_mulpT,eval_amulXnT,eval_sumpT) //=. 
  by rewrite ltrq //= ?(mul0r,add0r) polyC_opp mulNr mul1r.
rewrite -/edivp_rec_loopT.
move=> x e'.
rewrite Pn; last by move=>*; rewrite Pk. 
symmetry; rewrite Pn; last by move=>*; rewrite Pk.
rewrite Pk ?(eval_lift,eval_mulpT,eval_amulXnT,eval_sumpT).
by rewrite ?(mul0r,add0r,polyC_opp,mulNr,mul1r).
Qed.

Definition edivpT (p : polyF) (k : term F * polyF * polyF -> fF) (q : polyF) : fF :=
  isnull (fun b =>
    if b then k (Const 1, [::Const 0], p) else
      sizeT (fun sq =>
        sizeT (fun sp =>
          lead_coefT (fun lq =>
            edivp_rec_loopT q sq lq k 1 [::Const 0] p sp
          ) q
        ) p
      ) q
  ) q.

Lemma edivp_rec_loopP : forall q c qq r n, edivp_rec q n c qq r 
    = edivp_rec_loop q (size q) (lead_coef q) n c qq r.
Proof. 
move=> q c qq r n.
elim: n c qq r; first done.
by move=> n Pn c qq r; rewrite /= Pn.
Qed. 

Lemma edivpTP : forall k,
  (forall c qq r e,  qf_eval e (k (c,qq,r)) 
    = qf_eval e (k (Const (eval e c), lift (eval_poly e qq), lift (eval_poly e r))))
  -> forall p q e (d := (edivp (eval_poly e p) (eval_poly e q))),
    qf_eval e (edivpT p k q) = qf_eval e (k (Const d.1.1, lift d.1.2, lift d.2)).
Proof.
move=> k Pk.
move=> p q e /=.
rewrite isnullP /edivp.
case q0 : (_==_); first by rewrite Pk /= mul0r add0r polyC0.
rewrite !sizeTP lead_coefTP /=; last by move=> *; rewrite !edivp_rec_loopTP.
rewrite edivp_rec_loopTP /=; last by move=> *; rewrite Pk.
rewrite mul0r add0r polyC0.
by rewrite edivp_rec_loopP.
Qed.

Definition modpT (p : polyF) (k:polyF -> fF) (q : polyF) : fF :=
  edivpT p (fun d => k d.2) q.
Definition divpT (p : polyF) (k:polyF -> fF) (q : polyF) : fF :=
  edivpT p (fun d => k d.1.2) q.
Definition scalpT (p : polyF) (k:term F -> fF) (q : polyF) : fF :=
  edivpT p (fun d => k d.1.1) q.
Definition dvdpT (p : polyF) (k:bool -> fF) (q : polyF) : fF :=
  modpT p (isnull k) q.


Fixpoint gcdp_loop n (pp qq : {poly F}) {struct n} :=
  if pp %% qq == 0 then qq 
    else if n is n1.+1 then gcdp_loop n1 qq (pp %% qq)
        else pp %% qq.
Fixpoint gcdp_loopT pp k n qq {struct n} :=
  modpT pp (isnull 
    (fun b => if b 
      then (k qq) 
      else (if n is n1.+1 
        then modpT pp (gcdp_loopT qq k n1) qq 
        else modpT pp k qq)
    )
  ) qq.

Lemma gcdp_loopP: forall k,
  (forall p e, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p))))
  -> forall n p q e, qf_eval e (gcdp_loopT p k n q) = 
    qf_eval e (k (lift (gcdp_loop n (eval_poly e p) (eval_poly e q)))).
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
      else (sizeT (fun n => (gcdp_loopT p1 k n q1)) p1)) p1
    in (lt_sizeT (fun b => if b then (aux q k p) else (aux p k q)) p q). 

Lemma gcdpTP : forall k,
  (forall p e, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p))))
    -> forall p q e, qf_eval e (gcdpT p k q) = qf_eval e (k (lift (gcdp (eval_poly e p) (eval_poly e q)))).
Proof.
move=> k Pk p q e.
rewrite /gcdpT !sizeTP.
case lqp: (_ < _).  
  rewrite isnullP.
  case q0: (_ == _); first by rewrite Pk (eqP q0) gcdp0.
  rewrite sizeTP gcdp_loopP; first by rewrite /gcdp lqp q0.
  by move=> e' p'; rewrite Pk.
rewrite isnullP.
case p0: (_ == _); first by rewrite Pk (eqP p0) gcd0p.
rewrite sizeTP gcdp_loopP; first by rewrite /gcdp lqp p0.
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
  & (forall d,  p != 0 -> d %| p -> coprimep d q -> d %| r)
  : gdcop_spec q p r.

Lemma divp_dvd : forall (p d : {poly F}), d %| p ->  p %/ d %| p.
Proof.
move=> p d dp.
apply/dvdpPc.
have := divp_spec p d.
move: (dp); rewrite {1}/dvdp; move/eqP->.
rewrite addr0.
set c := (scalp _ _)=> f.
exists c; exists d.
by rewrite scalp_id /= f  mulrC.
Qed.
 

(* Lemma dvd_coprimepr : forall p q d, d %| q -> coprimep p q -> coprimep p d. *)

Lemma coprimepP : forall p q,
  reflect (exists d, (d %| gcdp p q) && (size d > 1))  (~~ coprimep p q).
Admitted.

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
apply/coprimepP.
exists d.
by rewrite dvdp_gcd dr dq //= (eqP sd).
Qed.

(* end to be put in poly *)

Fixpoint gdcop_recT (q: polyF) k  (p : polyF) n :=
  if n is m.+1 then
    gcdpT p (sizeT (fun sd =>
      if sd == 1%N then k p
        else gcdpT p (divpT p (fun r => gdcop_recT q k r m)) q
    )) q
    else k [::Const 1].
Lemma gdcop_recTP : forall k,
  (forall p e, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p))))
  -> forall p q n e, qf_eval e (gdcop_recT p k q n) 
    = qf_eval e (k (lift (gdcop_rec (eval_poly e p) (eval_poly e q) n))).
Proof.
move=> k Pk p q n e.
elim: n k Pk p q e => [|n Pn] k Pk p q e /=.
  by rewrite Pk /= mul0r add0r polyC1.
rewrite gcdpTP ?sizeTP ?eval_lift.
  rewrite /coprimep; case se : (_==_); first by rewrite Pk.
  by do ?[rewrite (gcdpTP,Pn,eval_lift,edivpTP) | move=> * //=].
by do ?[rewrite (sizeTP,eval_lift) | move=> * //=].
Qed.

Definition gdcopT q k p := sizeT (gdcop_recT q k p) p.
Lemma gdcopTP : forall k,
  (forall p e, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p))))
    -> forall p q e, qf_eval e (gdcopT p k q) = qf_eval e (k (lift (gdcop (eval_poly e p) (eval_poly e q)))).
Proof. by move=> *; rewrite sizeTP gdcop_recTP 1?Pk. Qed.

Definition ex_elim_seq (ps : seq polyF) (q : polyF) :=
  (gcdpTs (gdcopT q (sizeT (fun n => Bool (n > 1%N)))) ps).
Lemma ex_elim_seqP :
  forall ps q e,
    let gp := (\big[@gcdp _/0%:P]_(i <- ps)(eval_poly e i)) in
      qf_eval e (ex_elim_seq ps q) = (size (gdcop (eval_poly e q) gp) > 1).
Proof.
by do ![rewrite (gcdpTsP,gdcopTP,sizeTP,eval_lift) //= | move=> * //=].
Qed.

End ClosedFieldTheory.
