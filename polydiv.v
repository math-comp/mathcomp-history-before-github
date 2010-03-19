Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigops ssralg poly.

Import GRing.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.



Section ExtraArith.

Lemma leqn1 : (forall n, n <= 1 = ((n==0) || (n==1)))%N.
Proof. by elim; first done; elim. Qed.

Lemma leqn2 : (forall n, n <= 2 = [|| n == 0,  n == 1 | n == 2])%N.
Proof. by elim; first done; elim; first done; elim. Qed.

Lemma addn_pred1 : (forall n m, n != 0 -> (n == (m + n).-1) = (m == 1))%N.
Proof.
case; first by elim.
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

Lemma modp_dvd_eq0 : forall p q, (q %| p) = (p %% q == 0).
Proof. by move=> p q; rewrite /dvdp. Qed.

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


Lemma size_divp : forall p q, q != 0 -> size q <= size p
  -> size (p %/ q) = ((size p) - (size q).-1)%N.
Proof.
move=> p q nq0 sqp.
move: (nq0); rewrite -size_poly_eq0 -lt0n=> lt0sq.
move: (sqp); move/(leq_trans lt0sq) => lt0sp.
move: (lt0sp); rewrite lt0n size_poly_eq0=> p0.
case:(divp_spec p q).
move/(congr1 (size \o (@polyseq R)))=> /=.
rewrite (@size_eqp _ _ p) ?eqp_mulC ?scalp_id //.
case qq0: (p %/ q == 0).
  rewrite (eqP qq0) mul0r add0r=> es.
  by have:= modp_spec p nq0; rewrite -es ltnNge sqp.
move/negP:(qq0); move/negP; rewrite -size_poly_eq0 -lt0n=> lt0qq.
rewrite size_addl. 
  rewrite size_mul_id ?qq0 // => ->.
  apply/eqP; rewrite -(eqn_addr ((size q).-1)).
  rewrite subnK; first by rewrite -subn1 addn_subA // subn1.
  rewrite /leq -(subn_add2l 1%N) !add1n prednK // (@ltn_predK (size q)) //.
    by rewrite addnC -subn_sub subnn sub0n.
  by rewrite -[size q]add0n ltn_add2r.
rewrite size_mul_id ?qq0 // (leq_trans (modp_spec _ nq0)) //.
rewrite /leq -(subn_add2l 1%N) !add1n (@ltn_predK (size q)).
  by rewrite addnC -subn_sub subSnn subn_eq0.
by rewrite -[size q]add0n ltn_add2r.
Qed.

Lemma eqp_transl : left_transitive (@eqp R).
Proof. 
move=> p q r pq.
by apply/idP/idP=> e; apply: eqp_trans e; rewrite // eqp_sym.
Qed.

Lemma eqp_transr : right_transitive (@eqp R).
Proof. by move=> x y xy z; rewrite eqp_sym (eqp_transl xy) eqp_sym. Qed.

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

Lemma coprimep_sym : forall p q, coprimep p q = coprimep q p.
Proof. 
by move=> p q; rewrite -!gcdp_eqp1; apply: eqp_transl; rewrite gcdpC.
Qed.

Lemma coprime1p: forall p, coprimep 1 p.
Proof.
move=> p; rewrite /coprimep -[1%N](size_poly1 R); apply/eqP; apply: size_eqp.
exact: gcd1p.
Qed.

Lemma coprimep1 : forall p, coprimep p 1.
Proof. by move=> p; rewrite coprimep_sym; apply: coprime1p. Qed.

Lemma coprimep0 : forall p, coprimep p 0 = (p %= 1).
Proof. by move=> p; rewrite /coprimep gcdp0 size1_dvdp1. Qed.

Lemma coprime0p : forall p, coprimep 0 p = (p %= 1).
Proof. by move=> p; rewrite coprimep_sym coprimep0. Qed.



Lemma coprimepP : forall p q,
  reflect (forall d, d %| p -> d %| q -> d %= 1) (coprimep p q).
Proof.
move=> p q; apply: (iffP idP)=> [|h].
  rewrite /coprimep; move/eqP=> hs d dvddp dvddq.
  have dvddg: d %| gcdp p q by rewrite dvdp_gcd dvddp dvddq.
  by apply: (dvdp_eqp1 dvddg); rewrite -size1_dvdp1; apply/eqP.
by case/andP: (dvdp_gcd2 p q)=> h1 h2; rewrite /coprimep size1_dvdp1; apply: h.
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

Lemma modp_mod : forall p q, (p %% q) %% q = p %% q.
Proof.
move=> p q; case q0: (q == 0); first by rewrite (eqP q0) modp0.
by rewrite modp_size // modp_spec // q0.
Qed.

Fixpoint egcdp_rec p q n {struct n} :=
  if n is n'.+1 then
    if q == 0 then (1, 0) else
    let: (u, v) := egcdp_rec q (p%%q) n' in
      ((v * (scalp p q)%:P), (u - v * (p %/ q)))
  else (1, 0).
Definition egcdp p q := egcdp_rec p q (size q).

Lemma egcdp_recP : forall n p q, size q <= n -> size q <= size p 
  -> let e := (egcdp_rec p q n) in gcdp p q %= e.1*p + e.2*q.
Proof.
elim=> [|n ihn] p q /=.
  rewrite leqn0 size_poly_eq0; move/eqP=> -> _.
  by rewrite gcdp0 mul1r mulr0 addr0 eqpxx.
move=> sqSn qsp.
case q0: (q == 0)=> /=.
  by rewrite (eqP q0) gcdp0 mul1r mulr0 addr0 eqpxx.
have := (ihn q (p %% q)_ _).
case: (egcdp_rec _ _)=> u v=> ihn'.
rewrite gcdpE ltnNge qsp //= (eqp_transl (gcdpC _ _)).
apply: (eqp_trans (ihn' _ _)).
- by rewrite -(leq_add2l 1) !add1n (leq_trans (modp_spec _ _)) ?q0.
- by rewrite -(leq_add2l 1) !add1n (leq_trans (modp_spec _ _)) ?q0 ?leqnSn.
case: (divp_spec p q). rewrite -mulrA=> ->.
rewrite eqp_sym mulr_addr mulr_subl mulrA /=.
by rewrite addrC addrA -[_-_+_]addrA addNr addr0 eqpxx. 
Qed.

Lemma egcdpPS : forall p q, size q <= size p
  -> let e := egcdp p q in gcdp p q %= e.1*p + e.2*q.
Proof.
move=> p q sqp; rewrite /egcdp //=.
apply: egcdp_recP; rewrite ?leqnn // sqp.
Qed.

Lemma egcdpPW : forall p q, exists u, exists v, (u*p + v*q) %= (gcdp p q).
Proof.
move=> p q; case: (leqP (size p) (size q))=> sqp /=.
  - exists (egcdp q p).2; exists (egcdp q p).1.
    rewrite (eqp_transr (gcdpC _ _)).
    by rewrite addrC eqp_sym; apply: egcdpPS.
  - exists (egcdp p q).1; exists (egcdp p q).2.
    by rewrite eqp_sym; apply: egcdpPS (ltnW _).
Qed.

Lemma coprimepPW : forall p q, 
  reflect (exists u, exists v, (u*p + v*q) %= 1) (coprimep p q).
Proof.
move=> p q; rewrite -gcdp_eqp1; apply:(iffP idP)=> [g1|].
  case: (egcdpPW p q) => [u [v Puv]]; exists u; exists v.
  exact: eqp_trans g1.
move=>[u [v]]; rewrite eqp_sym=> Puv.
rewrite eqp1_dvd1; rewrite (eqp_dvdr _ Puv).
by rewrite dvdp_addr dvdp_mull ?dvdp_gcdl ?dvdp_gcdr.
Qed.

Lemma eqp_mull : forall p q r, (q %= r) -> (p * q %= p * r).
Proof.
move=> p q r.
  case/eqpP=>[c[d [c0 d0 e]]].
  apply/eqpP; exists c; exists d.
  by split=> //; rewrite !mulrA mulrAC e mulrAC.
Qed.

Lemma gauss : forall p q d, coprimep d q -> d %| p = (d %| p * q).
Proof.
move=> p q d.
move/coprimepPW=>[u [v Puv]].
apply/idP/idP; first exact: dvdp_mulr.
move:Puv; move/(eqp_mull p).
rewrite mulr1 mulr_addr eqp_sym=> peq dpq.
rewrite (eqp_dvdr _  peq) dvdp_addr.
  by rewrite mulrA mulrAC dvdp_mulr.
by rewrite mulrA dvdp_mull ?dvdpp.
Qed.

(* "gdcop Q P" is the Greatest Divisor of P which is coprime to Q *)
(* if P null, we pose that gdcop returns 1 if Q null, 0 otherwise*)
Fixpoint gdcop_rec q p n :=
  if n is m.+1 then
      if coprimep p q then p
        else gdcop_rec q (p %/ (gcdp p q)) m
    else (q == 0)%:R.
Definition gdcop q p := gdcop_rec q p (size p).

CoInductive gdcop_spec q p : {poly R} -> Type :=
  GdcopSpec r of (r %| p) & ((coprimep r q) || (p == 0)) 
  & (forall d,  d %| p -> coprimep d q -> d %| r)
  : gdcop_spec q p r.


Lemma gdcop0 : forall q, gdcop q 0 = (q == 0)%:R.
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
  case q0: (_ == _); split; rewrite ?coprime1p ?dvdp0 ?eqxx ?orbT //.
  by move=> d _; rewrite (eqP q0) coprimep0 -eqp1_dvd1.
move=> hs; case cop : (coprimep _ _); first by split; rewrite ?dvdpp ?cop.
case p0 : (p == 0).
  by rewrite (eqP p0) div0p; apply: ihn; rewrite size_poly0 leq0n.
case q0: (q == 0).
  rewrite (eqP q0) gcdp0 divpp ?p0 //= => {hs ihn}; case: n=> /=.
    rewrite eqxx; split; rewrite ?dvd1p ?coprimep0 ?eqpxx //=.
    by move=> d _; rewrite coprimep0 eqp1_dvd1.
  move=> n; rewrite coprimep0 -eqp_polyC scalp_id.
  split; first by rewrite (@eqp_dvdl 1) ?dvd1p -?eqp_polyC ?scalp_id //.
    by rewrite coprimep0 -eqp_polyC scalp_id.
  by move=> d _; rewrite coprimep0; move/eqp_dvdl->; rewrite dvd1p.
(* should we have a spec for dvdn ? => I also wondered *)
case: (divp_spec p (gcdp p q)); rewrite modp_dvd ?dvdp_gcdl // addr0 => e.
have sgp : size (gcdp p q) <= size p.
  by apply: size_dvdp; rewrite ?gcdp_eq0 ?p0 ?q0 // dvdp_gcdl.
have : p %/ gcdp p q != 0; last move/negPf=>p'n0.
  move: (dvdp_mulIl (p %/ gcdp p q) (gcdp p q)); move/dvdpn0; apply; rewrite -e.
  by rewrite -size_poly_eq0 size_polyC_mul ?scalp_id //size_poly_eq0 p0.
have gn0 : gcdp p q != 0.
  move: (dvdp_mulIr (p %/ gcdp p q) (gcdp p q)); move/dvdpn0; apply; rewrite -e.
  by rewrite -size_poly_eq0 size_polyC_mul ?scalp_id //size_poly_eq0 p0.
have sp' : size (p %/ (gcdp p q)) <= n.
  rewrite size_divp ?sgp // leq_sub_add (leq_trans hs)//.
  rewrite -add1n leq_add2r lt0n eqPn0 negb_orb size_poly_eq0 gn0 /=.
  by rewrite size_gcdp1 cop.
case (ihn _ sp')=> r' dr'p'; first rewrite p'n0 orbF=> cr'q maxr'.
constructor=> //=; rewrite ?p0 ?orbF //.
  apply: (dvdp_trans dr'p').
  apply/dvdpPc; exists (scalp p (gcdp p q)); exists (gcdp p q).
  by rewrite e mulrC scalp_id.
move=> d dp cdq.
apply: maxr'; last by rewrite cdq.
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
move/negPf: (p0)=> p0f.
rewrite (dvdp_trans dr) //=.
move: crq; apply: contraL=> dq; rewrite p0f orbF; apply/coprimepPn.
  by move:p0; apply: contra=> r0; move: rp; rewrite (eqP r0) dvd0p.
by exists d; rewrite dvdp_gcd dr dq -size1_dvdp1 (eqP sd).
Qed.

Lemma root_gdco : forall p q, p != 0 ->
  forall x, root p x && ~~(root q x) = root (gdcop q p) x.
Proof.
move=> p q p0 x.
rewrite !root_factor_theorem.
apply: dvdp_gdco; rewrite ?p0 //.
rewrite size_addl size_polyX // size_opp size_polyC.
by case: (x != 0).
Qed.

Lemma root_mul : forall p q x, root (p * q) x = root p x || root q x.
Proof. by move=> p q x; rewrite /root horner_mul mulf_eq0. Qed.

Lemma eqp_root : forall p q, p %= q -> forall x, root p x = root q x.
Proof.
move=> p q; move/eqpP=> [c [d [c0 d0 e]]] x.
rewrite /root; move/negPf:c0=>c0; move/negPf:d0=>d0.
rewrite -[_==_]orFb -c0 -mulf_eq0 -horner_Cmul e.
by rewrite horner_Cmul mulf_eq0 d0.
Qed.

Lemma root_gcd : forall p q x, root (gcdp p q) x = root p x && root q x.
Proof.
move=> p q x; rewrite !root_factor_theorem.
apply/idP/andP=> [dg| [dp dq]].
  by split; apply: (dvdp_trans dg); rewrite ?(dvdp_gcdl, dvdp_gcdr).
have:= (egcdpPW p q)=> [[u [v]]]; rewrite eqp_sym=> e.
by rewrite (eqp_dvdr _ e) dvdp_addl dvdp_mull.
Qed.

Lemma root0 : forall x, root 0 x.
Proof. by move=> x; rewrite /root ?hornerC. Qed.

Lemma root1n : forall x, ~~root 1 x.
Proof. by move=> x; rewrite /root ?hornerC oner_eq0. Qed.

Lemma root_biggcd : forall x (ps : seq {poly R}),
  root (\big[@gcdp _/0]_(p<-ps)p) x = all (fun p => root p x) ps.
Proof.
move=> x; elim; first by rewrite big_nil root0.
by move=> p ps ihp; rewrite big_cons /= root_gcd ihp.
Qed.

Lemma root_bigmul : forall x (ps : seq {poly R}),
  ~~root (\big[@mul _/1]_(p<-ps)p) x = all (fun p => ~~ root p x) ps.
Proof.
move=> x; elim; first by rewrite big_nil root1n.
by move=> p ps ihp; rewrite big_cons /= root_mul negb_or ihp.
Qed.

End ExtraPolynomialIdomain.

Section ExtraPolynomialFields.

Variable F : Field.type.

Variable axiom : ClosedField.axiom F.



Lemma root_size_neq1 : forall p : {poly F}, 
  reflect (exists x, root p x) (size p != 1%N).
Proof.
move=> p; case p0: (p == 0).
  rewrite (eqP p0) /= /root size_poly0 /=.
  by constructor; exists 0; rewrite horner0.
apply: (iffP idP); last first.
  case=> x; rewrite root_factor_theorem.
  apply: contraL; rewrite size1_dvdp1; move/eqp_dvdr->. 
  rewrite -eqp1_dvd1 -size1_dvdp1 size_addl size_polyX //.
  by rewrite size_opp size_polyC; case: (x != 0).
move/negPf => sp.
case: (ltnP (size p).-1 1)=> [|s2].
  by rewrite prednK ?lt0n ?leqn1 ?size_poly_eq0 p0 // sp.
have := axiom (fun n => -p`_n*(lead_coef p)^-1) s2.
case=> x; exists x.
have : 0 < size p by apply: leq_trans s2 _; apply: leq_pred.
rewrite /root horner_coef; move/prednK<-; rewrite big_ord_recr /= H.
apply/eqP; rewrite big_distrr -big_split big1 //= => i _.
rewrite mulrA [ _ * (_ / _)]mulrCA mulfV; last by rewrite lead_coef_eq0 p0.
by rewrite mulr1 mulNr addrN.
Qed.


Lemma ex_px_neq0 : forall p : {poly F}, p != 0 -> exists x, p.[x] != 0.
Proof.
move=> p p0.
case sp1: (size p == 1%N).
  by move/size1_is_polyC: sp1=> [x [x0 ->]]; exists x; rewrite hornerC.
have: (size (1 + p) != 1%N).
  rewrite addrC size_addl ?sp1 //. 
  move/negPf: p0 => p0f.
  by rewrite size_poly1 ltnNge leqn1 size_poly_eq0 p0f sp1.
move/root_size_neq1 => [x rx]; exists x.
move: rx; rewrite /root horner_add hornerC.
rewrite addrC -(inj_eq (@addIr _ (-1))) addrK sub0r.
move/eqP->; rewrite eq_sym -(inj_eq (@addrI _ 1)).
by rewrite addr0 subrr oner_eq0.
Qed.

End ExtraPolynomialFields.


