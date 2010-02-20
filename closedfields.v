Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import tuple finfun bigops ssralg poly.

Import GRing.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.



(* begin to be put in poly *)
Section ExtraArith.

Lemma leqn1 : (forall n, n <= 1 = ((n==0) || (n==1)))%N.
Proof. by elim; first done; elim. Qed.

Lemma leqn2 : (forall n, n <= 2 = [|| n == 0,  n == 1 | n == 2])%N.
Proof. by elim; first done; elim; first done; elim. Qed.

Lemma addn_pred1 : (forall n m, n != 0 -> (n == (m + n).-1) = (m == 1))%N.
Proof.
case; first do [elim; done].
move=> n m _; by rewrite addnS /= -add1n eqn_addr eq_sym.
Qed.



End ExtraArith.

Section ExtraPolynomialIdomain.


Variable R : idomainType.
Implicit Types x y c : R.
Implicit Types p q r d : {poly R}.

Lemma size1_is_polyC : forall p, 
  reflect (exists c, c != 0 /\ p = c%:P) (size p == 1%N).
Proof.
move=> p; apply: (iffP eqP) => [s1 | [c [nc0 ep]]].
  exists p`_0; move: (leqnn (size p)); rewrite {2}s1; move/size1_polyC=> e.
  by split=> //; rewrite -polyC_eq0 -e -size_poly_eq0 s1.
by rewrite ep size_polyC nc0.
Qed.

Lemma size1_dvdp1 : forall p, (size p == 1%N) = (p %= 1).
Proof.
move=> p; apply/size1_is_polyC/idP=> [[c [cn0 ep]] |].
  by apply/eqpP; exists 1; exists c; rewrite oner_eq0 mulr1 polyC1 mul1r.
by move/size_eqp; rewrite size_poly1; move/eqP; move/size1_is_polyC.
Qed.

Lemma neqp01 : 0 %= (1 : {poly R}) = false.
Proof.
case abs : (0 %= 1) => //; case/eqpP: abs=> c1 [c2 [c1n0 c2n0]].
by rewrite mulr0 mulr1; move/eqP; rewrite eq_sym polyC_eq0 (negbTE c2n0).
Qed.

Lemma dvd0p : forall p, 0 %| p = (p == 0).
Proof. by move=> p; rewrite /dvdp modp0. Qed.

Lemma dvdp_eqp1 : forall p q, p %| q -> q %= 1 -> p %= 1.
Proof.
move=> p q dpq hq.
have sizeq : size q == 1%N by rewrite size1_dvdp1.
have n0q : q != 0. 
  by case abs: (q == 0) => //; move: hq; rewrite (eqP abs) neqp01.
rewrite -size1_dvdp1 eqn_leq -{1}(eqP sizeq) size_dvdp //=.
case p0 : (size p == 0%N); last by rewrite neq0_lt0n.
move: dpq;  rewrite size_poly_eq0 in p0.
by rewrite (eqP p0) dvd0p (negbTE n0q).
Qed.

Lemma dvdpn0 : forall p q, p %| q -> q != 0 -> p != 0.
Proof.
move=> p q pq; apply: contra=> p0.
by move:pq; rewrite (eqP p0) dvd0p.
Qed.

Lemma dvdp_mulIl : forall p q, p %| p * q.
Proof. by move=> p q; apply: dvdp_mulr; exact: dvdpp. Qed.

Lemma dvdp_mulIr : forall p q, q %| p * q.
Proof. by move=> p q; apply: dvdp_mull; exact: dvdpp. Qed.

Lemma eqp_polyC: forall c, (c != 0) = (c%:P %= 1).
Proof.
move=> c; apply/idP/eqpP=> [nc0 | [x] [y]].
  by exists 1; exists c; rewrite nc0 /= nonzero1r mulrC.
case c0 : (c == 0); rewrite // mulr1 (eqP c0) mulr0; case=> _ /=; move/negbTE<-.
by move/eqP; rewrite eq_sym polyC_eq0.
Qed.

Lemma gcd1p : forall p, gcdp 1 p %= 1.
Proof.
move=> p; rewrite -size1_dvdp1 gcdpE size_poly1; case: ltnP.
  by rewrite modp1 gcd0p size_poly1 eqxx.
move/size1_polyC=> e; rewrite e.
case p00: (p`_0 == 0); first by rewrite (eqP p00) modp0 gcdp0 size_poly1.
by rewrite modpC ?p00 // gcd0p size_polyC p00.
Qed.


  

Lemma modp_dvd : forall p q, (q %| p) -> p %% q = 0.
Proof. by move=> p q; rewrite /dvdp; move/eqP. Qed.


Lemma eqp_dvdr : forall q p d, p %= q -> d %| p = (d %| q).
Proof.
move=> q p d epq; move: q p epq.
suff: forall q p, p %= q -> (d %| p) -> (d %| q)=> [Hpq|] q p.
  by move=> pq; apply/idP/idP; apply: Hpq; rewrite // eqp_sym.
by rewrite /eqp; case/andP=> pq qp dp; apply: (dvdp_trans dp).
Qed.

Lemma eqp_dvdl : forall d' d p, d %= d' -> d %| p = (d' %| p).
move=> d' d p edd'; move: d' d edd'.
suff: forall d' d, d %= d' -> (d %| p) -> (d' %| p)=> [Hdd'|] d' d.
  by move=> dd'; apply/idP/idP; apply: Hdd'; rewrite // eqp_sym.
by rewrite /eqp; case/andP=> dd' d'd dp; apply: (dvdp_trans d'd).
Qed.

Lemma eqp1_dvd : forall d p, d %= 1 -> d %| p. 
Proof. by move=> d p d1; rewrite (@eqp_dvdl 1)// dvd1p. Qed.

Lemma eqp1_dvd1 : forall d, (d %= 1) = (d %| 1).
Proof.
move=> d; apply/idP/idP; first exact: eqp1_dvd.
move=> d1; move/size_dvdp:(d1); rewrite GRing.nonzero1r size_poly1.
rewrite leqn1 size_poly_eq0; case d0 : (_ == _)=> /=.
  by move: d1; rewrite (eqP d0) dvd0p oner_eq0.
by rewrite size1_dvdp1=> d'1; apply: d'1.
Qed.
  
Lemma eqp_mulC : forall p q c, c != 0 -> c%:P * p %= p. 
Proof.
move=> p q c c0; apply/eqpP; exists 1; exists c; rewrite c0 oner_eq0.
by split=> //; rewrite polyC1 mul1r.
Qed. 

Lemma dvdp_size_eqp : forall p q, p %| q -> size p == size q = (p %= q).
Proof.
move=> p q pq; apply/idP/idP; last by move/size_eqp->.
case q0: (q == 0).
  by rewrite (eqP q0) size_poly0 size_poly_eq0; move/eqP->; rewrite eqpxx.
case p0: (p == 0).
  by rewrite (eqP p0) size_poly0 eq_sym size_poly_eq0; move/eqP->; rewrite eqpxx.
case/dvdpPc:pq=> x [qq [x0]]=> eqpq.
move:(eqpq); move/(congr1 (size \o (@polyseq R)))=> /=.
rewrite (@size_eqp _ _ q); last exact: eqp_mulC.
rewrite size_mul_id ?p0 //.
  move ->; rewrite addn_pred1 ?size_poly_eq0 ?p0 // => sqq.
  apply/eqpP; exists qq`_0; exists x.
  split; rewrite // -1?polyC_eq0 -?size1_polyC ?(eqP sqq) //.
  by rewrite -size_poly_eq0 (eqP sqq).
move/eqP:eqpq; apply: contraL; move/eqP->; rewrite mul0r.
by rewrite mulf_neq0 ?q0 ?polyC_eq0.
Qed.



Lemma size_divp : forall p q, q != 0 -> p %/ q != 0 
  -> size (p %/ q) = ((size p) - (size q).-1)%N.
Proof.
move=> p q nq0 nqq0.
move: (nq0); rewrite -size_poly_eq0 -lt0n=> lt0sq.
move: (nqq0); rewrite -size_poly_eq0 -lt0n=> lt0sqq.
case p0: (p == 0).
  by rewrite (eqP p0) div0p size_poly0 sub0n.
case:(divp_spec p q).
move/(congr1 (size \o (@polyseq R)))=> /=.
rewrite (@size_eqp _ _ p) ?eqp_mulC ?scalp_id //.
rewrite size_addl.
  rewrite size_mul_id // => ->.
  apply/eqP; rewrite -(eqn_addr ((size q).-1)).
  rewrite subnK; first by rewrite -subn1 addn_subA // subn1.
  rewrite /leq -(subn_add2l 1%N) !add1n prednK // (@ltn_predK (size q)) //.
    by rewrite addnC -subn_sub subnn sub0n.
  by rewrite -[size q]add0n ltn_add2r.
rewrite size_mul_id // (leq_trans (modp_spec _ nq0)) //.
rewrite /leq -(subn_add2l 1%N) !add1n (@ltn_predK (size q)).
  by rewrite addnC -subn_sub subSnn subn_eq0 //.
by rewrite -[size q]add0n ltn_add2r.
Qed.

Lemma eqp_transl : left_transitive (@eqp R).
Proof. 
apply: left_trans; first exact: eqp_sym.
by move=> p q r pr qr; apply: eqp_trans qr.
Qed.

Lemma gcdp_eq0 : forall p q, gcdp p q == 0 = (p == 0) && (q == 0).
Proof.
move=> p q; apply/idP/idP; last first.
  by case/andP; move/eqP->; move/eqP->; rewrite gcdp0.
move: p q; suff: forall p q,  gcdp p q == 0 -> (p == 0)=> [Hpq|] p q.
  move=> gpq0; apply/andP; split; [apply: (Hpq p q) | apply: (Hpq q p)]=> //.
  by rewrite -eqp0E (eqp_transl (gcdpC _ _)) eqp0E.
move=> gpq0; rewrite -dvd0p.
apply: dvdp_trans (dvdp_gcdl p q).
by rewrite dvd0p.
Qed.

Definition coprimep p q := size (gcdp p q) == 1%N.

Lemma size_gcdp1 : forall p q, size (gcdp p q) == 1%N = (coprimep p q).
Proof. done. Qed.

Lemma gcdp_eqp1 : forall p q, gcdp p q %= 1 = (coprimep p q).
Proof. by move=> p q; rewrite -size1_dvdp1 size_gcdp1. Qed.

Lemma coprimep1p: forall p, coprimep 1 p.
Proof.
move=> p; rewrite /coprimep -[1%N](size_poly1 R); apply/eqP; apply: size_eqp.
exact: gcd1p.
Qed.

Lemma coprimep0p : forall p, coprimep p 0 = (size p == 1%N).
Proof. by move=> p; rewrite /coprimep gcdp0. Qed.

Lemma coprimepP : forall p q,
  reflect (forall d, d %| p -> d %| q -> d %= 1) (coprimep p q).
Proof.
move=> p q; apply: (iffP idP)=> [|h].
  rewrite /coprimep; move/eqP=> hs d dvddp dvddq.
  have dvddg: d %| gcdp p q by rewrite dvdp_gcd dvddp dvddq.
  by apply: (dvdp_eqp1 dvddg); rewrite -size1_dvdp1; apply/eqP.
by case/andP: (dvdp_gcd2 p q)=> h1 h2; rewrite /coprimep size1_dvdp1; apply: h.
Qed.

Lemma coprimepC : forall p q, coprimep p q = coprimep q p.
Proof. 
by move=> p q; rewrite -!gcdp_eqp1; apply: eqp_transl; rewrite gcdpC.
Qed.

Lemma coprimepPn : forall p q, p != 0 ->
  reflect (exists d, (d %| gcdp p q) && ~~(d %= 1))  (~~ coprimep p q).
Proof.
move=> p q p0; apply: (iffP idP).
  by rewrite -gcdp_eqp1=> ng1; exists (gcdp p q); rewrite dvdpp /=.
case=> d; case/andP=> dg; apply: contra; rewrite -gcdp_eqp1=> g1.
by move: dg; rewrite (eqp_dvdr _ g1) eqp1_dvd1.
Qed.

Lemma coprimep_dvdl : forall p q r, 
  r %| q -> coprimep p q -> coprimep p r.
Proof.
move=> p q r rq cpq. 
apply/coprimepP=> d dp dr; move/coprimepP:cpq=> cpq'.
by apply: cpq'; rewrite // (dvdp_trans dr).
Qed.

Lemma gauss : forall p q d, coprimep d q -> d %| p = (d %| p * q).
Admitted.



(* "gdcop Q P" is the Greatest Divisor of P which is coprime to Q *)
(* if P null, we pose that gdcop returns 1 *)
Fixpoint gdcop_rec q p n :=
  if n is m.+1 then
      if coprimep p q then p
        else gdcop_rec q (p %/ (gcdp p q)) m
    else 1.
Definition gdcop q p := gdcop_rec q p (size p).

CoInductive gdcop_spec q p : {poly R} -> Type :=
  GdcopSpec r of (r %| p) & (coprimep r q) 
  & (forall d,  p != 0 -> d %| p -> coprimep d q -> d %| r)
  : gdcop_spec q p r.


Lemma gcopp0 : forall q, gdcop q 0 = 1.
Proof. by move=> q; rewrite /gdcop size_poly0. Qed.

Lemma eqPn0 : (forall n, (n.-1 == 0) = ((n==0) || (n==1)))%N. 
Proof. by elim. Qed.

Lemma divpp : forall p, p != 0 -> p %/ p = (scalp p p)%:P.
Proof.
move=> p np0; case: (divp_spec p p).
rewrite modpp addr0. move/eqP.
by rewrite (inj_eq (mulIf np0)); move/eqP.
Qed. 


Lemma gdcop_recP : forall q p n, 
  size p <= n -> gdcop_spec q p (gdcop_rec q p n).
Proof.
move=> q p n; elim: n p => [p | n ihn p] /=.
  rewrite leqn0 size_poly_eq0; move/eqP->.
  by split; rewrite ?coprimep1p ?dvdp0 ?eqxx.
move=> hs; case cop : (coprimep _ _); first by split; rewrite ?dvdpp ?cpq.
case p0 : (p == 0).
  by rewrite (eqP p0) div0p; apply: ihn; rewrite size_poly0 leq0n.
(* should we have a spec for dvdn ? => I also wondered *)
case: (divp_spec p (gcdp p q)); rewrite modp_dvd ?dvdp_gcdl // addr0 => e.
have p'n0 : p %/ gcdp p q != 0.
  move: (dvdp_mulIl (p %/ gcdp p q) (gcdp p q)); move/dvdpn0; apply; rewrite -e.
  by rewrite -size_poly_eq0 size_polyC_mul ?scalp_id //size_poly_eq0 p0.
have gn0 : gcdp p q != 0.
  move: (dvdp_mulIr (p %/ gcdp p q) (gcdp p q)); move/dvdpn0; apply; rewrite -e.
  by rewrite -size_poly_eq0 size_polyC_mul ?scalp_id //size_poly_eq0 p0.
have sp' : size (p %/ (gcdp p q)) <= n.
  rewrite size_divp// leq_sub_add (leq_trans hs)//.
  rewrite -add1n leq_add2r lt0n eqPn0 negb_orb size_poly_eq0 gn0 /=.
  by rewrite size_gcdp1 cop.
case (ihn _ sp')=> r' dr'p' cr'q maxr'.
constructor=> //=.
  apply: (dvdp_trans dr'p').
  apply/dvdpPc; exists (scalp p (gcdp p q)); exists (gcdp p q).
  by rewrite e mulrC scalp_id.
move=> d _ dp cdq.
apply: maxr'; last by rewrite cdq.
  case p'0: (_ == _)=> //.
  move: e; rewrite (eqP p'0) mul0r.
  move/eqP; apply:contraL=> _; rewrite mulf_neq0 ?p0 //.
  by rewrite polyC_eq0 scalp_id.
case dpq: (d %| gcdp p q).
  move: (dpq); rewrite dvdp_gcd dp /= => dq.
  apply: eqp1_dvd; move: cdq; apply: contraLR=> nd1.
  apply/coprimepPn. 
    move/negP: p0; move/negP; apply: contra=> d0.
    by move:dp; rewrite (eqP d0) dvd0p.
  by exists d; rewrite dvdp_gcd dvdpp dq nd1.
move: (dp); apply: contraLR=> ndp'.
rewrite (@eqp_dvdr ((scalp p (gcdp p q))%:P*p)).
  by rewrite e; rewrite -gauss //; apply: (coprimep_dvdl (dvdp_gcdr _ _)).
by rewrite eqp_sym eqp_mulC // scalp_id.
Qed.

Lemma gdcopP : forall q p, gdcop_spec q p (gdcop q p).
Proof. by move=> q p; rewrite /gdcop; apply: gdcop_recP. Qed.

Lemma dvdp_gdco : forall p q d, 
  p != 0 -> size d == 2%N ->
  (d %| p) && ~~(d %| q) = (d %| (gdcop q p)).
Proof.
move=> p q d p0 sd.
apply/idP/idP.
  case/andP=> dp dq.
  case: gdcopP=> r rp crq maxr.
  apply: maxr=> //.
  apply/negPn; apply/negP; case/coprimepPn.
    by move:p0; apply:contra=> d0; move: dp; rewrite (eqP d0) dvd0p. 
  move=> x; case/andP.
  rewrite dvdp_gcd; case/andP=> xd xq nx1.
  case nd0: (d == 0).
    by move: dp p0; rewrite (eqP nd0) dvd0p=> ->.
  move:(xd); move/negP: nd0; move/negPn=> nd0; move/(size_dvdp nd0).
  rewrite (eqP sd) leqn2; case/or3P.
  * rewrite size_poly_eq0=> x0; rewrite (eqP x0) dvd0p in xd.
    by rewrite (eqP xd) size_poly0 in sd.
  * by rewrite size1_dvdp1=> x1; rewrite x1 in nx1.
  * rewrite -(eqP sd) dvdp_size_eqp // => exd. 
    by rewrite (eqp_dvdl _ exd) in xq; rewrite xq in dq.
case: gdcopP=> r rp crq maxr dr.
rewrite (dvdp_trans dr) //=.
move: crq; apply: contraL=> dq; apply/coprimepPn.
  by move:p0; apply: contra=> r0; move: rp; rewrite (eqP r0) dvd0p.
by exists d; rewrite dvdp_gcd dr dq -size1_dvdp1 (eqP sd).
Qed.

End ExtraPolynomialIdomain.

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
move=> c qf Pqf e k; rewrite Pqf.
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
    -> forall p q e, qf_eval e (gdcopT p k q)
      = qf_eval e (k (lift (gdcop (eval_poly e p) (eval_poly e q)))).
Proof. by move=> *; rewrite sizeTP gdcop_recTP 1?Pk. Qed.

Definition ex_elim_seq (ps : seq polyF) (q : polyF) :=
  (gcdpTs (gdcopT q (sizeT (fun n => Bool (n == 1%N)))) ps).
Lemma ex_elim_seqP :
  forall ps q e,
    let gp := (\big[@gcdp _/0%:P]_(i <- ps)(eval_poly e i)) in
      qf_eval e (ex_elim_seq ps q) = (size (gdcop (eval_poly e q) gp) == 1%N).
Proof.
by do ![rewrite (gcdpTsP,gdcopTP,sizeTP,eval_lift) //= | move=> * //=].
Qed.

End ClosedFieldTheory.
