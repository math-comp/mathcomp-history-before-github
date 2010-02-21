Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import tuple finfun bigops ssralg poly polydiv.

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

(* Definition axiomp (R : Ring.type) := *)
(*   forall p : {poly R}, monic p -> size p > 1 -> exists x, p.[x] == 0. *)

(* Lemma axiomP : forall R, axiom R <-> axiomp R. *)
(* Proof. *)
(* move=> R. *)
(* rewrite /axiom /axiomp. *)
(* constructor. *)
(*   move=> HnP p mp sp. *)
(*   have := HnP ((size p).-1) (fun k => - nth 0 p k). *)
(*   rewrite -subn1 subn_gt0=> {HnP} Hsp. *)
(*   have := (Hsp sp) => {Hsp} [[x Px]]; exists x. *)
(*   move:Px. *)
(*   move/eqP=> /=. *)
(* Admitted. *)

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

Variable term_eq : term F -> term F -> bool.
Hypothesis term_eq_axiom : Equality.axiom term_eq.
Canonical Structure term_eqType := EqType (term F) (EqMixin term_eq_axiom).

Lemma solve_monicpoly : ClosedField.axiom F.
Proof. by case: F => ? []. Qed.
  
Notation fF := (formula  F).
Notation QFR f := (qf_form f && rformula f).

Definition ifF (th el f: fF) : fF :=
  ((f /\ th) \/ ((~ f) /\ el))%T.

Lemma ifFP : forall th el f e, qf_eval e (ifF th el f) = 
  (fun e f => if f then qf_eval e th else qf_eval e el) e (qf_eval e f).
Proof.
move=> th el f e; rewrite /ifF /=. 
case: (qf_eval e f); rewrite //=.
by case: (qf_eval _ _).
Qed.
Lemma ifF_QF : forall th el f (thP : QFR th) (elP : QFR el) (fP : QFR f), 
  QFR (ifF th el f).
Proof. by move=> th el f /=; do ?[case/andP=> -> ->]. Qed.

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

Definition rpoly p := (all (@rterm F) p).

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
move=> c qf Pqf e k; rewrite Pqf.
move: (erefl (size (eval_poly e qf))).
case: {-1}(size (eval_poly e qf))=> /= [|n].
  rewrite size_amulX => ->.
  by case c0: (eval e c == 0); rewrite // orbF.
by rewrite [eval_poly e _]/= size_amulX => ->.
Qed.
Lemma sizeT_QF : forall k p, (forall n, QFR (k n))
  -> rpoly p -> QFR (sizeT k p).
Proof.
move=> k p; elim: p k => /= [|c q ihp] k kP rp; first exact: kP.
case/andP: rp=> rc rq.
apply: ihp; rewrite ?rq //; case=> [|n]; last exact: kP.
by apply: ifF_QF=> //=; do ?apply kP; rewrite rc.
Qed.

Definition isnull (k : bool -> fF) (p: polyF) := sizeT (fun n => k (n == 0%N)) p.
Lemma isnullP : forall k,
  forall p e, qf_eval e (isnull k p) = qf_eval e (k (eval_poly e p == 0)).
Proof. by move=> k p e; rewrite sizeTP size_poly_eq0. Qed.

Lemma isnull_QF : forall k p, (forall b, QFR (k b))
  -> rpoly p -> QFR (isnull k p).
Proof. by move=> *; apply: sizeT_QF. Qed.

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

Lemma lead_coefT_QF : forall k p, (forall c, rterm c -> QFR (k c))
  -> rpoly p -> QFR (lead_coefT k p).
Proof.
move=> k p; elim: p k => /= [|c q ihp] k kP rp; first exact: kP.
move: rp; case/andP=> rc rq.
apply: ihp; rewrite ?rq // => l rl .
by apply: ifF_QF; do ?apply: kP; rewrite /= ?rl ?rc.
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

Lemma ramulXnT: forall a n, rterm a -> rpoly (amulXnT a n).
Proof. by move=> a n; elim: n a=> [a /= -> //|n ihn a ra]; apply: ihn. Qed.

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

Lemma rsumpT: forall p q, rpoly p -> rpoly q -> rpoly (sumpT p q).
Proof.
move=> p q; elim: p q=> [|a p ihp] q rp rq //=.
move: rp; case/andP=> ra rp.
case: q rq=> [|b q]; rewrite /= ?ra ?rp //=.
by case/andP=> -> rq //=; apply: ihp.
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

Lemma all_map : forall (A R : Type) p (f: A -> R) s,
  all p (map f s) = all (p \o f) s.
Proof. by move=> A R p f; elim=> [|a s]=> //= ->. Qed.

Lemma all_op: forall (T :Type) (p' p : pred T), p =1 p'-> all p =1 all p'.
Proof. by move=> T p' p pp'; elim=> [|a s]=> //= ->; rewrite pp'. Qed.

Lemma rpoly_map_mul : forall t p, rterm t -> rpoly (map (Mul t) p) = rpoly p.
Proof. 
move=> t p rt; rewrite /rpoly all_map /=.
by rewrite (@all_op _ (@rterm _)) // => x; rewrite /= rt.
Qed.

Lemma rmulpT: forall p q, rpoly p -> rpoly q -> rpoly (mulpT p q).
Proof.
move=> p q; elim: p q=> [|a p ihp] q rp rq //=.
move: rp; case/andP=> ra rp /=.
apply: rsumpT; last exact: ihp.
by rewrite rpoly_map_mul.
Qed.

Definition opppT := map (Mul (@Const F (-1))).
Lemma eval_opppT : forall p e, eval_poly e (opppT p) = - eval_poly e p.
Proof.
move=> p e; elim: p; rewrite //= ?oppr0 // => t ts ->.
by rewrite !mulNr !oppr_add polyC_opp mul1r.
Qed.

Definition natmulpT n := map (Mul (@NatConst F n)).
Lemma eval_natmulpT : forall p n e, 
  eval_poly e (natmulpT n p) = (eval_poly e p) *+ n.
Proof.
move=> p n e; elim: p; rewrite //= ?mul0rn // => c p ->.
rewrite mulrn_addl mulr_natl polyC_natmul; congr (_+_). 
by rewrite -mulr_natl mulrAC -mulrA mulr_natl mulrC.
Qed.


Fixpoint edivp_rec_loopT (q : polyF) sq cq (k : term F * polyF * polyF -> fF)
  (c : term F) (qq r : polyF) (n : nat) {struct n}:=
  sizeT (fun sr => 
    if sr < sq then k (c, qq, r) else 
      lead_coefT (fun lr =>
        let m := amulXnT lr (sr - sq) in
        let c1 := Mul cq c in
        let qq1 := sumpT (mulpT qq [::cq]) m in
        let r1 := sumpT (mulpT r ([::cq])) (opppT (mulpT m q)) in
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
    rewrite Pk ?(eval_mulpT,eval_amulXnT,eval_sumpT,eval_opppT) //=. 
    by rewrite ltrq //= ?(mul0r,add0r).
  move=> a p; rewrite Pk; symmetry; rewrite Pk. 
  by rewrite ?(eval_mulpT,eval_amulXnT,eval_sumpT, eval_opppT).
move=> n Pn c qq r k Pk e.
rewrite sizeTP.
case ltrq : (_<_); first by rewrite /= ltrq Pk.
rewrite lead_coefTP.
  rewrite Pn ?(eval_mulpT,eval_amulXnT,eval_sumpT,eval_opppT) //=. 
  by rewrite ltrq //= ?(mul0r,add0r).
rewrite -/edivp_rec_loopT.
move=> x e'.
rewrite Pn; last by move=>*; rewrite Pk. 
symmetry; rewrite Pn; last by move=>*; rewrite Pk.
rewrite Pk ?(eval_lift,eval_mulpT,eval_amulXnT,eval_sumpT,eval_opppT).
by rewrite ?(mul0r,add0r).
Qed.

Lemma edivp_rec_loopT_QF :  forall q sq cq k c qq r n,
  (forall r, [&& rterm r.1.1, rpoly r.1.2 & rpoly r.2] -> QFR (k r))
  -> rpoly q -> rterm cq -> rterm c -> rpoly qq -> rpoly r
    -> QFR (edivp_rec_loopT q sq cq k c qq r n).
Proof.
move=> q sq cq k c qq r n; move: q sq cq k c qq r.
elim: n => [|n ihn] q sq cq k c qq r kP rq rcq rc rqq rr.
  apply: sizeT_QF=> // n; case: (_ < _).
    by apply: kP => //=; rewrite rc rqq rr.
  apply: lead_coefT_QF=> // l rl.
  apply: kP; rewrite /= rcq rc /=.
  by rewrite ?(rsumpT,rmulpT,ramulXnT,rpoly_map_mul) //= rcq.
apply: sizeT_QF=> // m; case: (_ < _).
  by apply: kP => //=; rewrite rc rqq rr.
apply: lead_coefT_QF=> // l rl.
apply: ihn; rewrite //= ?(rcq,rc) //.
  by rewrite ?(rsumpT,rmulpT,ramulXnT,rpoly_map_mul) //= rcq.
by rewrite ?(rsumpT,rmulpT,ramulXnT,rpoly_map_mul) //= rcq.
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

Lemma edivpT_QF : forall p k q,
  (forall r, [&& rterm r.1.1, rpoly r.1.2 & rpoly r.2] -> QFR (k r))
  -> rpoly p -> rpoly q -> QFR (edivpT p k q).
Proof.
move=> p k q kP rp rq; rewrite /edivpT.
apply: isnull_QF=> // b.
case b; first by apply: kP=> /=.
apply: sizeT_QF=> // sq.
apply: sizeT_QF=> // sp.
apply: lead_coefT_QF=> // lq rlq.
exact: edivp_rec_loopT_QF.
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

Lemma gcdp_loopT_QF : forall p k q n,
  (forall r, rpoly r -> QFR (k r))
  -> rpoly p -> rpoly q -> QFR (gcdp_loopT p k n q).
move=> p k q n; move: p k q.
elim: n=> [|n ihn] p k q kP rp rq.
  apply: edivpT_QF=> // r; case/and3P=> _ _ rr.
  apply: isnull_QF=> // [[]]; first exact: kP.
  by apply: edivpT_QF=> // r'; case/and3P=> _ _ rr'; apply: kP.
apply: edivpT_QF=> // r; case/and3P=> _ _ rr.
apply: isnull_QF=> // [[]]; first exact: kP.
by apply: edivpT_QF=> // r'; case/and3P=> _ _ rr'; apply: ihn.
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

Lemma gcdpT_QF :  forall p k q,  (forall r, rpoly r -> QFR (k r))
  -> rpoly p -> rpoly q -> QFR (gcdpT p k q).
Proof.
move=> p k q kP rp rq.
apply: sizeT_QF=> // n; apply: sizeT_QF=> // m.
by case:(_ < _); apply: isnull_QF=> //; 
  case; do ?apply: kP=> //;
  apply: sizeT_QF=> // n';
  apply: gcdp_loopT_QF.
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

Definition rseq_poly ps := all rpoly ps.

Lemma gcdpTs_QF : forall k ps,  (forall r, rpoly r -> QFR (k r))
  -> rseq_poly ps -> QFR (gcdpTs k ps).
Proof.
move=> k p; elim: p k=> [|c p ihp] k kP rps=> /=; first exact: kP.
move: rps; case/andP=> rc rp.
by apply: ihp=> // r rr; apply: gcdpT_QF.
Qed.

(* end to be put in poly *)
Fixpoint gdcop_recT (q: polyF) k  (p : polyF) n :=
  if n is m.+1 then
    gcdpT p (sizeT (fun sd =>
      if sd == 1%N then k p
        else gcdpT p (divpT p (fun r => gdcop_recT q k r m)) q
    )) q
    else k [::Const 0].
Lemma gdcop_recTP : forall k,
  (forall p e, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p))))
  -> forall p q n e, qf_eval e (gdcop_recT p k q n) 
    = qf_eval e (k (lift (gdcop_rec (eval_poly e p) (eval_poly e q) n))).
Proof.
move=> k Pk p q n e.
elim: n k Pk p q e => [|n Pn] k Pk p q e /=.
  by rewrite Pk /= mul0r add0r polyC0.
rewrite gcdpTP ?sizeTP ?eval_lift.
  rewrite /coprimep; case se : (_==_); first by rewrite Pk.
  by do ?[rewrite (gcdpTP,Pn,eval_lift,edivpTP) | move=> * //=].
by do ?[rewrite (sizeTP,eval_lift) | move=> * //=].
Qed.

Lemma gdcop_recT_QF :  forall p k q n,  (forall r, rpoly r -> QFR (k r))
  -> rpoly p -> rpoly q -> QFR (gdcop_recT p k q n).
Proof.
move=> p k q n; elim: n p k q=> [|n ihn] p k q kP rp rq /=.
apply: kP=> //.
apply: gcdpT_QF=> // g rg.
apply: sizeT_QF=> // n'.
case:(_ == _); first exact: kP.
apply: gcdpT_QF=> // g' rg'.
apply: edivpT_QF=> // r; case/and3P=> _ rr _.
exact: ihn.
Qed.

Definition gdcopT q k p := sizeT (gdcop_recT q k p) p.
Lemma gdcopTP : forall k,
  (forall p e, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p))))
    -> forall p q e, qf_eval e (gdcopT p k q)
      = qf_eval e (k (lift (gdcop (eval_poly e p) (eval_poly e q)))).
Proof. by move=> *; rewrite sizeTP gdcop_recTP 1?Pk. Qed.
Lemma gdcopT_QF : forall p k q, (forall r, rpoly r -> QFR (k r))
  -> rpoly p -> rpoly q -> QFR (gdcopT p k q).
Proof. 
by move=> p k q kP rp rq; apply: sizeT_QF => // n; apply: gdcop_recT_QF.
Qed.


Definition ex_elim_seq (ps : seq polyF) (q : polyF) :=
  (gcdpTs (gdcopT q (sizeT (fun n => Bool (n != 1%N)))) ps).
Lemma ex_elim_seqP :
  forall ps q e,
    let gp := (\big[@gcdp _/0%:P]_(p <- ps)(eval_poly e p)) in
      qf_eval e (ex_elim_seq ps q) = (size (gdcop (eval_poly e q) gp) != 1%N).
Proof.
by do ![rewrite (gcdpTsP,gdcopTP,sizeTP,eval_lift) //= | move=> * //=].
Qed.

Lemma ex_elim_seq_QF : forall ps q, rseq_poly ps -> rpoly q
  -> QFR (ex_elim_seq ps q).
Proof.
move=> ps q rps rq.
apply: gcdpTs_QF=> // g rg.
apply: gdcopT_QF=> // d rd.
exact : sizeT_QF.
Qed.



Fixpoint abstrX (i : nat) (t : term F) :=
  match t with
    | (Var n) => if n == i then [::Const 0; Const 1] else [::t]
    | (Opp x) => opppT (abstrX i x)
    | (Add x y) => sumpT (abstrX i x) (abstrX i y)
    | (Mul x y) => mulpT (abstrX i x) (abstrX i y)
    | (NatMul x n) => natmulpT n (abstrX i x)
    | (Exp x n) => let ax := (abstrX i x) in
      iter n (mulpT ax) [::Const 1]
    | _ => [::t]
  end.

Lemma abstrXP : forall i t e, (eval_poly e (abstrX i t)).[e`_i] = eval e t.
Proof.
move=> i t e; elim: t.
- by move=> n /=; case ni: (_ == _);
  rewrite //= ?(mul0r,add0r,addr0,polyC1,mul1r,hornerX,hornerC) // (eqP ni).
- by move=> r; rewrite /= mul0r add0r hornerC.
- by move=> r; rewrite /= mul0r add0r hornerC.
- by move=> t tP s sP; rewrite /= eval_sumpT horner_add tP sP. 
- by move=> t tP; rewrite /= eval_opppT horner_opp tP.
- by move=> t tP n; rewrite /= eval_natmulpT horner_mulrn tP.
- by move=> t tP s sP; rewrite /= eval_mulpT horner_mul tP sP.
- move=> t tP; admit. (*Il faut corriger abstrX pour inv*)
- move=> t tP => /=; elim; first by rewrite /= expr0 mul0r add0r hornerC.
  by move=> n ihn; rewrite /= eval_mulpT exprSr horner_mul ihn tP mulrC.
Qed.

Lemma rabstrX : forall i t, rterm t -> rpoly (abstrX i t).
Proof.
move=> i; elim; do ?[ by move=> * //=; do ?case: (_ == _)].
- move=> t irt s irs /=; case/andP=> rt rs.
  by apply: rsumpT; rewrite ?irt ?irs //.
- by move=> t irt /= rt; rewrite rpoly_map_mul ?irt //.
- by move=> t irt /= n rt; rewrite rpoly_map_mul ?irt //.
- move=> t irt s irs /=; case/andP=> rt rs.
  by apply: rmulpT; rewrite ?irt ?irs //.
- move=> t irt /= n rt; move: (irt rt)=> {rt} rt; elim: n => [|n ihn] //=.
  exact: rmulpT.
Qed.

Lemma rseq_poly_map : forall x ts,
  all (@rterm _) ts ->  rseq_poly (map (abstrX x) ts).
Proof.
move=> x; elim=> //= t ts iht. 
by case/andP=> rt rts; rewrite rabstrX // iht.
Qed.


Definition ex_elim (x : nat) (pqs : seq (term F) * seq (term F)) :=
  ex_elim_seq (map (abstrX x) pqs.1) 
  (abstrX x (\big[Mul/Const 1]_(q <- pqs.2) q)).
Lemma ex_elim_QF : forall x pqs, 
  dnf_rterm pqs -> QFR (ex_elim x pqs).
move=> x [ps qs]; case/andP=> /= rps rqs.
apply: ex_elim_seq_QF; first exact: rseq_poly_map.
apply: rabstrX=> /=.
elim: qs rqs=> [|t ts iht] //=; first by rewrite big_nil.
by case/andP=> rt rts; rewrite big_cons /= rt /= iht.
Qed.


Lemma has_rootP : forall i bc e
  (ex_i_bc := ('exists 'X_i, dnf_to_form [:: bc])%T)
  (gp := (\big[@gcdp _/0%:P]_(p <- bc.1)(eval_poly e (abstrX i p))))
  (mq := (eval_poly e (abstrX i (\big[Mul/(1%R%:T)%T]_(q <- bc.2) q)))),
  reflect (holds e ex_i_bc) (size (gdcop mq gp) != 1%N).
Admitted.

Lemma holds_ex_elim : QE.holds_proj_axiom ex_elim.
Proof.
move=> i bc ex_i_bc e dnfbc.
pose gp := (\big[@gcdp _/0%:P]_(p <- bc.1)(eval_poly e (abstrX i p))).
pose mq := (eval_poly e (abstrX i (\big[Mul/(1%R%:T)%T]_(q <- bc.2) q))).
suff ->: (qf_eval e (ex_elim i bc)) = (size (gdcop mq gp) != 1%N).
  exact: has_rootP.
by rewrite ex_elim_seqP big_map.
Qed.

Lemma wf_ex_elim : QE.wf_proj_axiom ex_elim.
Proof. by move=> i bc /= rbc; apply: ex_elim_QF. Qed.

Definition closed_fields_QEMixin := 
  QE.Mixin wf_ex_elim holds_ex_elim.
Canonical Structure closed_fields_qe := 
  QE.Pack (QE.Class closed_fields_QEMixin) F.

End ClosedFieldTheory.
