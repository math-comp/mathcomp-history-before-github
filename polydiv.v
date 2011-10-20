(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
Require Import bigop ssralg poly choice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Reserved Notation "p %= q" (at level 70, no associativity).

Local Notation simp := Monoid.simpm.

Section ToPoly.

Section Ring.

Variable  R : ringType.
Implicit Types p q : {poly R}.

Lemma size_poly_eq0P p : reflect (p = 0) (size p == 0%N).
Proof. by apply: (iffP idP); rewrite size_poly_eq0; move/eqP. Qed.

Lemma size_poly_leq0 p : (size p <= 0) = (p == 0).
Proof. by rewrite leqn0 size_poly_eq0. Qed.

Lemma size_poly_leq0P p : reflect (p = 0) (size p <= 0%N).
Proof. by apply: (iffP idP); rewrite size_poly_leq0; move/eqP. Qed.

Lemma size_poly_gt0 p : (0 < size p) = (p != 0).
Proof. by rewrite lt0n size_poly_eq0. Qed.


End Ring.
End ToPoly.

Module RPdiv.

Section RingPseudoDivision.

Variable R : ringType.
Implicit Types d p q r : {poly R}.

(* Pseudo division, defined on an arbitrary ring *)
Definition redivp_rec (q : {poly R})  :=
  let sq := size q in
  let cq := lead_coef q in
(*  fix loop (n : nat)(k : nat) (qq r : {poly R}) {struct n} :=*)
   fix loop (k : nat) (qq r : {poly R})(n : nat) {struct n} :=
    if size r < sq then (k, qq, r) else
    let m := (lead_coef r) *: 'X^(size r - sq) in
    let qq1 := qq * cq%:P + m in
    let r1 := r * cq%:P - m * q in
    (* if n is n1.+1 then loop n1 k.+1 qq1 r1 else (k.+1, qq1, r1). *)
       if n is n1.+1 then loop k.+1 qq1 r1 n1 else (k.+1, qq1, r1). 

Definition redivp (p q : {poly R}) : nat * {poly R} * {poly R} :=
  (* if q == 0 then (0%N, 0, p) else redivp_rec q (size p) 0 0 p. *)
     if q == 0 then (0%N, 0, p) else redivp_rec q 0 0 p (size p).

Definition rdivp p q := ((redivp p q).1).2.
Definition rmodp p q := (redivp p q).2.
Definition rscalp p q := ((redivp p q).1).1.
Definition rdvdp p q := rmodp q p == 0.
Definition rmultp := [rel m d | rdvdp d m].
Lemma redivp_def p q : redivp p q = (rscalp p q, rdivp p q, rmodp p q).
Proof. by rewrite /rscalp /rdivp /rmodp; case: (redivp p q) => [[]] /=. Qed.

Lemma rdiv0p p : rdivp 0 p = 0.
Proof.
rewrite /rdivp /redivp; case: ifP => // Hp; rewrite /redivp_rec !size_poly0. 
by rewrite polySpred ?Hp.
Qed.

Lemma rdivp0 p : rdivp p 0 = 0.
Proof. by rewrite /rdivp /redivp eqxx. Qed.

Lemma rdivp_small p q : size p < size q -> rdivp p q = 0.
Proof.
rewrite /rdivp /redivp; case: eqP => Eq; first by rewrite Eq size_poly0.
by case sp: (size p) => [| s] hs /=; rewrite sp hs.
Qed.

Lemma leq_rdivp p q : (size (rdivp p q) <= size p).
Proof.
case: (ltnP (size p) (size q)); first by move/rdivp_small->; rewrite size_poly0.
rewrite /rdivp /rmodp /rscalp /redivp; case q0 : (q == 0) => /=.
  by rewrite size_poly0.
have : (size (0 : {poly R})) <= size p by rewrite size_poly0.
move: (leqnn (size p)); move: {2 3 4 6}(size p)=> A.
elim: (size p) 0%N (0 : {poly R}) {1 3 4}p (leqnn (size p)) => [| n ihn] k q1 r.
  by move/size_poly_leq0P->; rewrite /= size_poly0 lt0n size_poly_eq0 q0.
move=> /= hrn hr hq1 hq; case: ltnP=> //= hqr.
have sr: 0 < size r by apply: leq_trans hqr; rewrite size_poly_gt0 q0.
have sq: 0 < size q by rewrite size_poly_neq0 q0.
apply: ihn => //.
- apply/leq_sizeP => j hnj.
  rewrite coef_sub -scaler_mull coefZ coefXnM -ltn_add_sub ltnNge.
  have hj : (size r).-1 <= j.
    by apply: leq_trans hnj; move: hrn; rewrite -{1}(prednK sr) ltnS.
  rewrite polySpred -?size_poly_gt0 // (leq_ltn_trans hj) /=; last first.
    by rewrite -{1}(add0n j) ltn_add2r.
  move: (hj); rewrite leq_eqVlt; case/orP.
    move/eqP<-; rewrite (@polySpred _ q) ?q0 // subSS coefMC.
    rewrite subKn; first by rewrite lead_coefE subrr.
    by rewrite -ltnS -!polySpred // ?q0 -?size_poly_neq0.
  move=> {hj} hj; move: (hj); rewrite prednK // coefMC; move/leq_sizeP=> -> //.
  suff: size q <= j - (size r - size q).
    by rewrite mul0r sub0r; move/leq_sizeP=> -> //; rewrite mulr0 oppr0.
  rewrite subn_subA // addnC -(prednK sq) -(prednK sr) addSn subSS.
  by rewrite -addn_subA ?(ltnW hj) // -{1}[_.-1]addn0 ltn_add2l subn_gt0.
- apply: leq_trans (size_add _ _) _; rewrite leq_maxl; apply/andP; split.
  + apply: leq_trans (size_mul _ _) _; rewrite size_polyC lead_coef_eq0 q0 /=.
    by rewrite addn1.
  + rewrite size_opp; apply: leq_trans (size_mul _ _) _.
  have: size ((lead_coef r)%:P * 'X^(size r - size q)) <= (size r - size q).+1.
      apply: leq_trans (size_mul _ _) _; rewrite size_polyC size_polyXn addnS /=.
      by rewrite  lead_coef_eq0 -size_poly_neq0 sr add1n.
    rewrite -(leq_add2r (size q));  set x := size _; rewrite addSn subnK //.
    have : x + size q > 0 by rewrite addn_gt0 orbC size_poly_neq0 q0.
      by move/prednK=> {1}<-; rewrite ltnS -mul_polyC => h; apply: leq_trans h _.
- apply: leq_trans (size_add _ _) _; rewrite leq_maxl; apply/andP; split.
  + apply: leq_trans (size_mul _ _) _; rewrite size_polyC lead_coef_eq0 q0 /=.
    by rewrite addnS addn0.
  + rewrite -mul_polyC; apply: leq_trans (size_mul _ _) _; rewrite size_polyC.
    rewrite lead_coef_eq0 -size_poly_neq0 sr addSn add0n /= size_polyXn.
    by apply: leq_trans hr; rewrite -{2}(subn0 (size r)) ltn_sub2l.
Qed.

Lemma rmod0p p : rmodp 0 p = 0.
Proof.
rewrite /rmodp /redivp; case: ifP => // Hp; rewrite /redivp_rec !size_poly0.
by rewrite polySpred ?Hp.
Qed.

Lemma rmodp0 p : rmodp p 0 = p.
Proof. by rewrite /rmodp /redivp eqxx. Qed.

Lemma rscalp_small p q : size p < size q -> rscalp p q = 0%N.
Proof.
rewrite /rscalp /redivp; case: eqP => Eq // spq.
by case sp: (size p) => [| s] /=; rewrite spq.
Qed.
  
Lemma ltn_rmodp p q : (size (rmodp p q) < size q) = (q != 0).
Proof.
rewrite /rdivp /rmodp /rscalp /redivp; case q0 : (q == 0).
  by rewrite (eqP q0) /= size_poly0 ltn0.
elim: (size p) 0%N 0 {1 3}p (leqnn (size p)) => [|n ihn] k q1 r.
  rewrite leqn0 size_poly_eq0; move/eqP->; rewrite /= size_poly0 /= lt0n.
  by rewrite size_poly_eq0 q0 /= size_poly0 lt0n size_poly_eq0 q0.
move=> hr /=; case: (@ltnP (size r) _) => //= hsrq; rewrite ihn //.
apply/leq_sizeP => j hnj; rewrite coef_sub.
have sr: 0 < size r.
  by apply: leq_trans hsrq; apply: neq0_lt0n; rewrite size_poly_eq0.
have sq: 0 < size q by rewrite size_poly_neq0 q0.
have hj : (size r).-1 <= j.
  by apply: leq_trans hnj; move: hr; rewrite -{1}(prednK sr) ltnS.
rewrite -scaler_mull !coefZ coefXnM -ltn_add_sub ltnNge; move: (sr).
move/prednK => {1}<-.
have -> /= : (size r).-1 < size q + j.
  apply: (@leq_trans ((size q) + (size r).-1)); last by rewrite leq_add2l.
  by rewrite -{1}[_.-1]add0n ltn_add2r.
move: (hj); rewrite leq_eqVlt; case/orP.
  move/eqP<-; rewrite -{1}(prednK sq) -{3}(prednK sr) subSS.
  rewrite  subKn; first by rewrite coefMC !lead_coefE subrr.
  by move: hsrq; rewrite -{1}(prednK sq) -{1}(prednK sr) ltnS.
move=> {hj} hj; move: (hj); rewrite prednK // coefMC; move/leq_sizeP=> -> //.
suff: size q <= j - (size r - size q).
   by rewrite mul0r sub0r; move/leq_sizeP=> -> //; rewrite mulr0 oppr0.
rewrite subn_subA // addnC -(prednK sq) -(prednK sr) addSn subSS.
by rewrite -addn_subA ?(ltnW hj) // -{1}[_.-1]addn0 ltn_add2l subn_gt0.
Qed.

Lemma ltn_rmodpN0 p q : q != 0 ->  (size (rmodp p q) < size q).
Proof. by rewrite ltn_rmodp. Qed.

Lemma rmodp1 p : rmodp p 1 = 0.
Proof.
case p0: (p == 0); first by rewrite (eqP p0) rmod0p.
apply/eqP; rewrite -size_poly_eq0.
by have := (ltn_rmodp p 1); rewrite size_polyC !nonzero1r ltnS leqn0.
Qed.

Lemma rmodp_small p q : size p < size q -> rmodp p q = p.
Proof.
rewrite /rmodp /redivp; case: eqP => Eq; first by rewrite Eq size_poly0.
by case sp: (size p) => [| s] Hs /=; rewrite sp Hs /=.
Qed.

Lemma leq_rmodp m d : size (rmodp m d)  <= size m.
Proof.
case: (ltnP (size m) (size d)) => [|h]; first by move/rmodp_small->.
case d0: (d == 0); first by rewrite (eqP d0) rmodp0.
by apply: leq_trans h; apply: ltnW; rewrite ltn_rmodp d0.
Qed.

Lemma rmodpC p c : c != 0 -> rmodp p c%:P = 0.
Proof.
move=> Hc; apply/eqP; rewrite -size_poly_eq0 -leqn0 -ltnS.
have -> : 1%N = nat_of_bool (c != 0) by rewrite Hc.
by rewrite -size_polyC ltn_rmodp polyC_eq0.
Qed.

Lemma rdvdp0 d : rdvdp d 0.
Proof. by rewrite /rdvdp rmod0p. Qed.

Lemma rdvd0p n : (rdvdp 0 n) = (n == 0).
Proof. by rewrite /rdvdp rmodp0. Qed.

Lemma rdvd0pP n : reflect (n = 0) (rdvdp 0 n).
Proof. by  apply: (iffP idP); rewrite rdvd0p; move/eqP. Qed.

Lemma rdvdpN0 p q : rdvdp p q -> q != 0 -> p != 0.
Proof. by move=> pq hq; apply: contraL pq=> /eqP ->; rewrite rdvd0p. Qed.

Lemma rdvdp1 d : (rdvdp d 1) = ((size d) == 1%N).
Proof.
rewrite /rdvdp; case d0: (d == 0). 
  by rewrite (eqP d0) rmodp0 size_poly0 (negPf (@nonzero1r _)).
have:= (size_poly_eq0 d); rewrite d0; move/negbT; rewrite -lt0n.
rewrite leq_eqVlt; case/orP => hd; last first.
  rewrite rmodp_small ?size_polyC (negPf (@nonzero1r _)) //.
  by apply: sym_eq; apply: negPf; move: hd; rewrite ltn_neqAle eq_sym; case/andP.
rewrite [_ == 1%N]eq_sym hd; move: hd; rewrite eq_sym; case/size1P=> c cn0 ->.
rewrite /rmodp /redivp polyC_eq0 (negPf cn0) size_polyC (negPf (@nonzero1r _)).
rewrite /= !size_polyC cn0 (negPf (@nonzero1r _)) ltnn /= !lead_coefC !scale1r.
by rewrite subnn mul1r subrr size_poly0 /= eqxx.
Qed.

Lemma rdvd1p m : rdvdp 1 m.
Proof. by rewrite /rdvdp rmodp1. Qed.

Lemma Nrdvdp_small (n d : {poly R}) : n != 0 -> size n < size d -> (rdvdp d n) = false.
Proof. 
by move=> nn0 hs; rewrite /rdvdp; rewrite (rmodp_small hs); apply: negPf.
Qed.

Lemma rmodp_eq0P p q : reflect (rmodp p q = 0) (rdvdp q p).
Proof. exact: (iffP eqP). Qed.

Lemma rmodp_eq0 p q : rdvdp q p -> rmodp p q = 0.
Proof. by move/rmodp_eq0P. Qed.

Lemma rdvdp_leq p q : rdvdp p q -> q != 0 -> size p <= size q.
case/rmodp_eq0P => rpq nq0; case: (ltnP (size p) (size q)); first by move/ltnW->.
rewrite leq_eqVlt; case/orP; first by move/eqP->. 
by move/rmodp_small; rewrite rpq => h; move: nq0; rewrite h eqxx.
Qed.

Definition rgcdp p q :=
  let: (p1, q1) := if size p < size q then (q, p) else (p, q) in
  if p1 == 0 then q1 else
  let fix loop (n : nat) (pp qq : {poly R}) {struct n} :=
      let rr := rmodp pp qq in
      if rr == 0 then qq else
      if n is n1.+1 then loop n1 qq rr else rr in
  loop (size p1) p1 q1.

Lemma rgcd0p : left_id 0 rgcdp.
Proof.
move=> p; rewrite /rgcdp size_poly0 size_poly_neq0 if_neg.
case: ifP => /= [_ | nzp]; first by rewrite eqxx.
by rewrite polySpred !(rmodp0, nzp) //; case: _.-1 => [|m]; rewrite rmod0p eqxx.
Qed.

Lemma rgcdp0 : right_id 0 rgcdp.
Proof.
move=> p; have:= rgcd0p p; rewrite /rgcdp size_poly0 size_poly_neq0 if_neg.
by case: ifP => /= p0; rewrite ?(eqxx, p0) // (eqP p0).
Qed.

Lemma rgcdpE p q :
  rgcdp p q = if size p < size q 
    then rgcdp (rmodp q p) p else rgcdp (rmodp p q) q.
Proof.
pose rgcdp_rec := fix rgcdp_rec (n : nat) (pp qq : {poly R}) {struct n} :=
   let rr := rmodp pp qq in
   if rr == 0 then qq else
   if n is n1.+1 then rgcdp_rec n1 qq rr else rr.
have Irec: forall m n p q, size q <= m -> size q <= n
      -> size q < size p -> rgcdp_rec m p q = rgcdp_rec n p q.
+ elim=> [|m Hrec] [|n] //= p1 q1.
  - rewrite leqn0 size_poly_eq0; move/eqP=> -> _.
    rewrite size_poly0 size_poly_neq0 rmodp0 => nzp.
    by rewrite (negPf nzp); case: n => [|n] /=; rewrite rmod0p eqxx.
  - rewrite leqn0 size_poly_eq0 => _; move/eqP=> ->.
    rewrite size_poly0 size_poly_neq0 rmodp0 => nzp.
    by rewrite (negPf nzp); case: m {Hrec} => [|m] /=; rewrite rmod0p eqxx.
  case: ifP => Epq Sm Sn Sq //; rewrite ?Epq //.
  case: (eqVneq q1 0) => [->|nzq].
    by case: n m {Sm Sn Hrec} => [|m] [|n] //=; rewrite rmod0p eqxx.
  apply: Hrec; last by rewrite ltn_rmodp.
    by rewrite -ltnS (leq_trans _ Sm) // ltn_rmodp.
  by rewrite -ltnS (leq_trans _ Sn) // ltn_rmodp.
case: (eqVneq p 0) => [-> | nzp].
  by rewrite rmod0p rmodp0 rgcd0p rgcdp0 if_same.
case: (eqVneq q 0) => [-> | nzq].
  by rewrite rmod0p rmodp0 rgcd0p rgcdp0 if_same.
rewrite /rgcdp -/rgcdp_rec.
case: ltnP; rewrite (negPf nzp, negPf nzq) //=.
  move=> ltpq; rewrite ltn_rmodp (negPf nzp) //=.
  rewrite -(ltn_predK ltpq) /=; case: eqP => [->|].
    by case: (size p) => [|[|s]]; rewrite /= rmodp0 (negPf nzp) // rmod0p eqxx.
  move/eqP=> nzqp; rewrite (negPf nzp).
  apply: Irec => //; last by rewrite ltn_rmodp.
    by rewrite -ltnS (ltn_predK ltpq) (leq_trans _ ltpq) ?leqW // ltn_rmodp.
  by rewrite ltnW // ltn_rmodp.
move=> leqp; rewrite ltn_rmodp (negPf nzq) //=.
have p_gt0: size p > 0 by rewrite size_poly_neq0.
rewrite -(prednK p_gt0) /=; case: eqP => [->|].
  by case: (size q) => [|[|s]]; rewrite /= rmodp0 (negPf nzq) // rmod0p eqxx.
move/eqP=> nzpq; rewrite (negPf nzq); apply: Irec => //; last by rewrite ltn_rmodp.
  by rewrite -ltnS (prednK p_gt0) (leq_trans _ leqp) // ltn_rmodp.
by rewrite ltnW // ltn_rmodp.
Qed.

CoInductive comm_redivp_spec (m d : {poly R}) : nat * {poly R} * {poly R} -> Type :=
  ComEdivnSpec k (q r: {poly R}) of
   (GRing.comm d (lead_coef d)%:P -> m * (lead_coef d ^+ k)%:P = q * d + r) &
   (d != 0 -> size r < size d) : comm_redivp_spec m d (k, q, r).

Lemma comm_redivpP m d : comm_redivp_spec m d (redivp m d).
Proof.
rewrite /redivp; case: (altP (d =P 0))=> [->| Hd].
  by constructor; rewrite !(simp, eqxx).
have: GRing.comm d (lead_coef d)%:P -> m * (lead_coef d ^+ 0)%:P = 0 * d + m.
  by rewrite !simp.
elim: (size m) 0%N 0 {1 4 6}m (leqnn (size m))=>
   [|n IHn] k q r Hr /=.
  have {Hr} -> : r = 0 by apply/eqP; rewrite -size_poly_eq0; move: Hr; case: size.
  suff hsd: size (0: {poly R}) < size d by rewrite hsd => /= ?; constructor.
  by rewrite size_polyC eqxx (polySpred Hd).
case: ltP=> Hlt Heq; first by constructor=> // _; apply/ltP.
apply: IHn=> [|Cda]; last first.
  rewrite mulr_addl addrAC -addrA subrK exprSr polyC_mul mulrA Heq //.
  by rewrite mulr_addl -mulrA Cda mulrA.
apply/leq_sizeP => j Hj.
rewrite coefD coefN coefMC -scaler_mull coefZ coefXnM.
move/ltP: Hlt; rewrite -leqNgt=> Hlt.
move: Hj; rewrite leq_eqVlt; case/predU1P => [<-{j} | Hj]; last first.
  rewrite nth_default ?(leq_trans Hqq) // ?simp; last by apply: (leq_trans Hr).
  rewrite nth_default; first by rewrite if_same !simp oppr0.
  by rewrite -{1}(subKn Hlt) leq_sub2r // (leq_trans Hr).
move: Hr; rewrite leq_eqVlt ltnS; case/predU1P=> Hqq; last first.
  rewrite !nth_default ?if_same ?simp ?oppr0 //.
  by rewrite -{1}(subKn Hlt) leq_sub2r // (leq_trans Hqq).
rewrite {2}/lead_coef Hqq polySpred // subSS ltnNge leq_subr /=.
by rewrite subKn ?addrN // -subn1 leq_sub_add add1n -Hqq.
Qed.

Definition rcoprimep (p q : {poly R}) := size (rgcdp p q) == 1%N.

Fixpoint rgdcop_rec q p n :=
  if n is m.+1 then
      if rcoprimep p q then p
        else rgdcop_rec q (rdivp p (rgcdp p q)) m
    else (q == 0)%:R.

Definition rgdcop q p := rgdcop_rec q p (size p).

Lemma rgdcop0 q : rgdcop q 0 = (q == 0)%:R.
Proof. by rewrite /rgdcop size_poly0. Qed.

End RingPseudoDivision.


Section ComRegDivisor.

Variable R : ringType.
Variable d : {poly R}.
Hypothesis Cdl : GRing.comm d (lead_coef d)%:P.
Hypothesis Rreg : GRing.rreg (lead_coef d).

Implicit Types p q r : {poly R}.

Lemma redivp_eq q r :  size r < size d ->
  let k := (redivp (q * d + r) d).1.1 in
  let c := (lead_coef d ^+ k)%:P in
  redivp (q * d + r) d = (k, q * c, r * c).
Proof.
move=> lt_rd; case: comm_redivpP=> k q1 r1; move/(_ Cdl)=> Heq.
have: d != 0 by case: (size d) lt_rd (size_poly_eq0 d) => // n _ <-.
move=> dn0; move/(_ dn0)=> Hs.
have eC : q * d * (lead_coef d ^+ k)%:P = q * (lead_coef d ^+ k)%:P * d.
  by rewrite -mulrA polyC_exp (GRing.commr_exp k Cdl) mulrA.
suff e1 : q1 = q * (lead_coef d ^+ k)%:P.
  congr (_, _, _) => //=; move/eqP: Heq; rewrite [_ + r1]addrC.
  rewrite -subr_eq; move/eqP<-; rewrite e1 mulr_addl addrAC -{2}(add0r (r * _)).
  by rewrite eC subrr add0r.
have : (q1 - q * (lead_coef d ^+ k)%:P) * d = r * (lead_coef d ^+ k)%:P - r1.
  apply: (@addIr _ r1); rewrite subrK.
  apply: (@addrI _  ((q * (lead_coef d ^+ k)%:P) * d)).
  by rewrite mulr_addl mulNr !addrA [_ + (q1 * d)]addrC addrK -eC -mulr_addl.
move/eqP; rewrite -[_ == _ - _]subr_eq0 rreg_div0 //.
  by case/andP; rewrite subr_eq0; move/eqP.
rewrite size_opp; apply: (leq_ltn_trans (size_add _ _)); rewrite size_opp ltnNge.
rewrite leq_maxr negb_or -!ltnNge Hs (leq_ltn_trans (size_mul _ _)) //.
rewrite size_polyC; case: (_ == _); last by rewrite addnS addn0.
by rewrite addn0; apply: leq_ltn_trans lt_rd; case: size.
Qed.

(* this is a bad name *)
Lemma rdivp_eq p : 
  p * (lead_coef d ^+ (rscalp p d))%:P = (rdivp p d) * d + (rmodp p d).
Proof. 
rewrite /rdivp /rmodp /rscalp; case: comm_redivpP=> k q1 r1 Hc _; exact: Hc.
Qed.

(* section variables impose an inconvenient order on parameters *)
Lemma eq_rdvdp k q1 p: 
  p * ((lead_coef d)^+ k)%:P = q1 * d -> rdvdp d p.
Proof.
move=> he.
have Hnq0 := rreg_lead0 Rreg; set lq := lead_coef d.
pose v := rscalp p d; pose m := maxn v k.
rewrite /rdvdp -(rreg_scale0 _ (@rregX _ _ (m - v) Rreg)).
suff:
 ((rdivp p d) * (lq ^+ (m - v))%:P  - q1 * (lq ^+ (m - k))%:P) * d +
  (rmodp p d) * (lq ^+ (m - v))%:P  == 0.
  rewrite rreg_div0 //; first by case/andP.
  by rewrite rreg_size ?ltn_rmodp //; apply rregX.
rewrite mulr_addl addrAC mulNr -!mulrA  polyC_exp -(GRing.commr_exp (m-v) Cdl).
rewrite -polyC_exp mulrA -mulr_addl -rdivp_eq // [(_ ^+ (m - k))%:P]polyC_exp.
rewrite -(GRing.commr_exp (m-k) Cdl) -polyC_exp mulrA -he -!mulrA -!polyC_mul.
rewrite -/v -!exprn_addr addnC subnK; last by rewrite leq_maxr leqnn.
by rewrite addnC subnK ?subrr // leq_maxr leqnn orbT.
Qed.

CoInductive rdvdp_spec p q : {poly R} -> bool -> Type :=
  |Rdvdp : forall k q1, 
    p * ((lead_coef q)^+ k)%:P = q1 * q -> rdvdp_spec p q 0 true
  |RdvdpN : rmodp p q != 0 -> rdvdp_spec p q (rmodp p q) false.

(* Is that version useable ? *)

Lemma rdvdp_eqP p : rdvdp_spec p d (rmodp p d) (rdvdp d p).
Proof.
case hdvd: (rdvdp d p); last by apply: RdvdpN; move/rmodp_eq0P/eqP: hdvd.
move/rmodp_eq0P: (hdvd)->; apply: (@Rdvdp _ _ (rscalp p d) (rdivp p d)).
by rewrite rdivp_eq //; move/rmodp_eq0P: (hdvd)->; rewrite addr0.
Qed.

Lemma rdvdp_mull p : rdvdp d (p * d).
Proof. by apply: (@eq_rdvdp 0%N p); rewrite expr0 mulr1. Qed.

Lemma rmodp_mull p : rmodp (p * d) d = 0.
Proof.
case: (d =P 0)=> Hd; first by rewrite Hd simp rmod0p.
by apply/eqP; apply: rdvdp_mull.
Qed.

Lemma rmodpp : rmodp d d = 0.
Proof. by rewrite -{1}(mul1r d) rmodp_mull. Qed.

Lemma rdivpp : rdivp d d = (lead_coef d ^+ rscalp d d)%:P.
have dn0 : d != 0 by rewrite -lead_coef_eq0 rreg_neq0.
move: (rdivp_eq d); rewrite rmodpp addr0.
suff ->: GRing.comm d (lead_coef d ^+ rscalp d d)%:P by move/(rreg_lead Rreg)->.
by rewrite polyC_exp; apply: commr_exp.
Qed.

Lemma rdvdpp : rdvdp d d.
Proof. apply/eqP; exact: rmodpp. Qed.

(* we could provide the value of (rscalep d d) and may be more things... *)
End ComRegDivisor.

Module mon.

Section MonicDivisor.

Variable R : ringType.
Implicit Types p q r : {poly R}.

Variable d : {poly R}.
Hypothesis mond : monic d.

Lemma redivp_eq q r :  size r < size d ->
  let k := (redivp (q * d + r) d).1.1 in
  redivp (q * d + r) d = (k, q, r).
Proof. 
case: (monic_comreg mond)=> Hc Hr; move/(redivp_eq Hc Hr q).
by rewrite  (eqP mond); move=> -> /=; rewrite exp1rn !mulr1.
Qed.

Lemma rdivp_eq p : 
  p = (rdivp p d) * d + (rmodp p d).
Proof.
rewrite -rdivp_eq; rewrite (eqP mond); last exact: commr1.
by rewrite exp1rn mulr1.
Qed.

Lemma rdivpp : rdivp d d = 1.
Proof.
by case: (monic_comreg mond) => hc hr; rewrite rdivpp // (eqP mond) exp1rn.
Qed.

Lemma rdivp_addl_mul_small q r : 
  size r < size d -> rdivp (q * d + r) d = q.
Proof.
by move=> Hd; case: (monic_comreg mond)=> Hc Hr; rewrite /rdivp redivp_eq.
Qed.

Lemma rdivp_addl_mul q r : rdivp (q * d + r) d = q + rdivp r d.
Proof.
case: (monic_comreg mond)=> Hc Hr; rewrite {1}(rdivp_eq r) addrA.
by rewrite -mulr_addl rdivp_addl_mul_small // ltn_rmodp monic_neq0.
Qed.

Lemma rdivp_addl q r : 
  rdvdp d q -> rdivp (q + r) d = rdivp q d + rdivp r d.
Proof.
case: (monic_comreg mond)=> Hc Hr; rewrite {1}(rdivp_eq r) addrA.
rewrite {2}(rdivp_eq q); move/rmodp_eq0P->; rewrite addr0.
by rewrite -mulr_addl rdivp_addl_mul_small // ltn_rmodp monic_neq0.
Qed.

Lemma rdivp_addr q r : 
  rdvdp d r -> rdivp (q + r) d = rdivp q d + rdivp r d.
Proof. by rewrite addrC; move/rdivp_addl->; rewrite addrC. Qed.

Lemma rdivp_mull p  : rdivp (p * d) d = p.
Proof. by rewrite -[p * d]addr0 rdivp_addl_mul rdiv0p addr0. Qed.

Lemma rmodp_mull p : rmodp (p * d) d = 0.
Proof.
apply: rmodp_mull; rewrite (eqP mond); [exact: commr1 | exact: rreg1]. 
Qed.

Lemma rmodpp : rmodp d d = 0.
Proof.
apply: rmodpp; rewrite (eqP mond); [exact: commr1 | exact: rreg1]. 
Qed.

Lemma rmodp_addl_mul_small q r :
  size r < size d -> rmodp (q * d + r) d = r.
Proof.
by move=> Hd; case: (monic_comreg mond)=> Hc Hr; rewrite /rmodp redivp_eq.
Qed.

Lemma rmodp_add p q : rmodp (p + q) d = rmodp p d + rmodp q d.
Proof.
rewrite {1}(rdivp_eq p) {1}(rdivp_eq q).
rewrite addrCA 2!addrA -mulr_addl (addrC (rdivp q d)) -addrA.
rewrite rmodp_addl_mul_small //; apply: (leq_ltn_trans (size_add _ _)).
wlog hyp : / size (rmodp p d) <= size (rmodp q d).
  case/orP: (orbN (size (rmodp p d) <= size (rmodp q d))) => [?|]; first by apply.
  rewrite -ltnNge => sz hyp; rewrite maxnl; last by exact: ltnW.
  by rewrite ltn_rmodp // monic_neq0.
by rewrite maxnr // ltn_rmodp monic_neq0.
Qed.

Lemma rmodp_mulmr p q : rmodp (p * (rmodp q d)) d = rmodp (p * q) d.
Proof.
have -> : rmodp q d = q - (rdivp q d) * d.
  by rewrite {2}(rdivp_eq q) addrAC subrr add0r.
rewrite mulr_addr rmodp_add -mulNr mulrA.
rewrite -{2}[rmodp _ _]addr0; congr (_ + _); exact: rmodp_mull.
Qed.

Lemma rdvdpp : rdvdp d d.
Proof. 
apply: rdvdpp; rewrite (eqP mond); [exact: commr1 | exact: rreg1]. 
Qed.

(* section variables impose an inconvenient order on parameters *)
Lemma eq_rdvdp q1 p : p = q1 * d -> rdvdp d p.
Proof.
(*  this probably means I need to specify impl args for comm_rref_rdvdp *)
move=> h; apply: (@eq_rdvdp _ _ _ _ 1%N q1); rewrite (eqP mond).
- exact: commr1.
- exact: rreg1.
by rewrite exp1rn mulr1.
Qed.

Lemma rdvdp_mull p : rdvdp d (p * d).
Proof. 
apply: rdvdp_mull; rewrite (eqP mond) //; [exact: commr1 | exact: rreg1]. 
Qed.

Lemma rdvdpP p : reflect (exists qq, p = qq * d) (rdvdp d p).
Proof.
case: (monic_comreg mond)=> Hc Hr; apply: (iffP idP).
  case: rdvdp_eqP=> // k qq; rewrite (eqP mond) exp1rn mulr1; move=> -> _.
  by exists qq.
by case=> [qq]; move/eq_rdvdp.
Qed.

End MonicDivisor.


End mon.

Section ExtraMonicRingPseudoDivision.

Variable R : ringType.

Implicit Types d p q r : {poly R}.

Lemma rdivp1 p : rdivp p 1 = p.
Proof. by rewrite -{1}(mulr1 p) mon.rdivp_mull // monic1. Qed.

Lemma rdvdp_factorl p x : rdvdp ('X - x%:P) p = root p x.
Proof.
have [HcX Hr] := (monic_comreg (monic_factor x)).
apply/rmodp_eq0P/factor_theorem; last first.
  case=> p1 ->; apply: mon.rmodp_mull; exact: monic_factor.
move=> e0; exists (rdivp p ('X - x%:P)). 
by rewrite {1}(mon.rdivp_eq (monic_factor x) p) e0 addr0.
Qed.

Lemma factorP p x : reflect (p.[x] = 0) (rdvdp ('X - x%:P) p).
Proof. by apply: (iffP idP); rewrite rdvdp_factorl; move/rootP. Qed.


Lemma root_factor_theorem p x : root p x = (rdvdp ('X - x%:P) p).
Proof. by rewrite rdvdp_factorl. Qed.

End ExtraMonicRingPseudoDivision.

Module ComRing.

Section CommutativeRingPseudoDivision.

Variable R : comRingType.

Implicit Types d p q m n r : {poly R}.

CoInductive redivp_spec (m d : {poly R}) : nat * {poly R} * {poly R} -> Type :=
  EdivnSpec k (q r: {poly R}) of
    (lead_coef d ^+ k) *: m = q * d + r &
   (d != 0 -> size r < size d) : redivp_spec m d (k, q, r).


Lemma redivpP m d : redivp_spec m d (redivp m d).
Proof.
rewrite redivp_def; constructor; last by move=> dn0; rewrite ltn_rmodp.
by rewrite -mul_polyC mulrC rdivp_eq //= /GRing.comm mulrC.
Qed.

Lemma rdivp_eq d p : 
  (lead_coef d ^+ (rscalp p d)) *: p = (rdivp p d) * d + (rmodp p d).
Proof. 
rewrite /rdivp /rmodp /rscalp; case: redivpP=> k q1 r1 Hc _; exact: Hc.
Qed.

Lemma rdvdp_eqP d p : rdvdp_spec p d (rmodp p d) (rdvdp d p).
Proof.
case hdvd: (rdvdp d p); last by apply: RdvdpN; move/rmodp_eq0P/eqP: hdvd.
move/rmodp_eq0P: (hdvd)->; apply: (@Rdvdp _ _ _ (rscalp p d) (rdivp p d)).
by rewrite mulrC mul_polyC rdivp_eq; move/rmodp_eq0P: (hdvd)->; rewrite addr0.
Qed.

Lemma rdvdp_eq q p : 
  (rdvdp q p) = ((lead_coef q) ^+ (rscalp p q) *: p == (rdivp p q) * q).
apply/rmodp_eq0P/eqP; rewrite rdivp_eq; first by move->; rewrite addr0.
by move/eqP; rewrite eq_sym addrC -subr_eq subrr; move/eqP->.
Qed.

End CommutativeRingPseudoDivision.

End ComRing.

Module UnitRing.

Section UnitRingPseudoDivision.

Variable R : unitRingType.
Implicit Type p : {poly R}.

Lemma uniq_roots_rdvdp p rs :
  all (root p) rs -> uniq_roots rs ->
  rdvdp (\prod_(z <- rs) ('X - z%:P)) p.
Proof.
move=> rrs; case/(uniq_roots_factors rrs)=> q ->; apply: mon.rdvdp_mull.
exact: monic_prod_factors.
Qed.

End UnitRingPseudoDivision.

End UnitRing.

End RPdiv.

Section IDomainPseudoDivisionDefs.

Import RPdiv.
Import ComRing.
Import UnitRing.

Variable R : idomainType.
Implicit Type p q r d : {poly R}.

Definition edivp p q :=
let: (k, d, r) := redivp p q in
  if GRing.unit (lead_coef q) 
    then (0%N, (lead_coef q)^-k *: d, (lead_coef q)^-k *: r) else (k, d, r). 

Definition divp p q := ((edivp p q).1).2.
Definition modp p q := (edivp p q).2.
Definition scalp p q := ((edivp p q).1).1.
Definition dvdp p q := modp q p == 0.

End IDomainPseudoDivisionDefs.

Notation "m %/ d" := (divp m d) : ring_scope.
Notation "m %% d" := (modp m d) : ring_scope.
Notation "p %| q" := (dvdp p q) : ring_scope.

Module ID.

Section WeakTheoryForIDomainPseudoDivision.

Import RPdiv.
Import ComRing.
Import UnitRing.

Variable R : idomainType.
Implicit Type p q r d : {poly R}.


Lemma edivp_def p q : edivp p q = (scalp p q, divp p q, modp p q).
Proof. by rewrite /scalp /divp /modp; case: (edivp p q) => [[]] /=. Qed.

Lemma edivp_redivp p q : GRing.unit (lead_coef q) = false ->
  edivp p q = redivp p q.
Proof. by move=> hu; rewrite /edivp hu; case: (redivp p q) => [[? ?] ?]. Qed.

Lemma divpE p q :
  p %/ q = if GRing.unit (lead_coef q) 
    then (lead_coef q)^-(rscalp p q) *: (rdivp p q)
    else rdivp p q.
Proof.
by case ulcq: (GRing.unit (lead_coef q)); rewrite /divp /edivp redivp_def ulcq.
Qed.

Lemma modpE p q :
  p %% q = if GRing.unit (lead_coef q) 
    then (lead_coef q)^-(rscalp p q) *: (rmodp p q)
    else rmodp p q.
Proof.
by case ulcq: (GRing.unit (lead_coef q)); rewrite /modp /edivp redivp_def ulcq.
Qed.

Lemma scalpE p q :
  scalp p q = if GRing.unit (lead_coef q) then 0%N else rscalp p q.
Proof.
by case ulcq: (GRing.unit (lead_coef q)); rewrite /scalp /edivp redivp_def ulcq.
Qed.

Lemma dvdpE p q : p %| q = rdvdp p q.
Proof.
rewrite /dvdp modpE /rdvdp; case ulcq: (GRing.unit (lead_coef p))=> //.
rewrite -[_ *: _ == 0]size_poly_eq0 size_scaler ?size_poly_eq0 //.
by rewrite invr_eq0 expf_neq0 //; apply: contraTneq ulcq => ->; rewrite unitr0.
Qed.

Lemma lc_expn_scalp_neq0 p q : lead_coef q ^+ scalp p q != 0.
Proof.
case: (eqVneq q 0) => [->|nzq]; last by rewrite expf_neq0 ?lead_coef_eq0.
by rewrite /scalp /edivp /redivp /= eqxx lead_coef0 unitr0 /= nonzero1r.
Qed.

Hint Resolve lc_expn_scalp_neq0.
  
CoInductive edivp_spec (m d : {poly R}) : nat * {poly R} * {poly R} -> bool -> Type :=
  |Redivp_spec k (q r: {poly R}) of
    (lead_coef d ^+ k) *: m = q * d + r & ~~(GRing.unit (lead_coef d)) &
   (d != 0 -> size r < size d) : edivp_spec m d (k, q, r) false
  |Fedivp_spec (q r: {poly R}) of m = q * d + r & (GRing.unit (lead_coef d)) &
   (d != 0 -> size r < size d) : edivp_spec m d (0%N, q, r) true.


(* Is this the most appropriate statement?*)
Lemma edivpP m d : edivp_spec m d (edivp m d) (GRing.unit (lead_coef d)).
Proof.
have hC : GRing.comm d (lead_coef d)%:P by rewrite /GRing.comm mulrC.
case ud: (GRing.unit (lead_coef d)); last first.
  rewrite edivp_redivp // redivp_def; constructor; rewrite ?ltn_rmodp // ?ud //.
  by rewrite rdivp_eq.
have cdn0 : lead_coef d != 0.
  by move: ud; case d0: (lead_coef d == 0) => //; rewrite (eqP d0) unitr0.
rewrite /edivp ud redivp_def; constructor => //.
  rewrite -scaler_mull -scaler_addr -mul_polyC.
  have hn0 : (lead_coef d ^+ rscalp m d)%:P != 0.
    by rewrite polyC_eq0; apply: expf_neq0.
  apply: (mulfI hn0); rewrite !mulrA -expr_inv !polyC_exp -exprn_mull -polyC_mul.
  by rewrite  divrr // exp1rn mul1r -polyC_exp mul_polyC rdivp_eq.
move=> dn0; rewrite size_scaler ?ltn_rmodp // -expr_inv expf_eq0 negb_and.
by rewrite invr_eq0 cdn0 orbT.
Qed.

Lemma edivp_eq d q r : size r < size d -> GRing.unit (lead_coef d) ->
  edivp (q * d + r) d = (0%N, q, r).
Proof.
have hC : GRing.comm d (lead_coef d)%:P by rewrite /GRing.comm mulrC.
move=> hsrd hu; rewrite /edivp hu; case et: (redivp _ _) => [[s qq] rr].
have cdn0 : lead_coef d != 0.
  by move: hu; case d0: (lead_coef d == 0) => //; rewrite (eqP d0) unitr0.
move: (et); rewrite redivp_eq //; last by apply/rregP.
rewrite et /=; case => e1 e2; rewrite -!mul_polyC -!expr_inv !polyC_exp.
suff h x y: x * (lead_coef d ^+ s)%:P = y -> ((lead_coef d)^-1)%:P ^+ s * y = x.
  by congr (_, _, _); apply: h.
have hn0 : (lead_coef d)%:P ^+ s != 0 by apply: expf_neq0; rewrite polyC_eq0.
move=> hh; apply: (mulfI hn0); rewrite mulrA -exprn_mull -polyC_mul divrr //.
by rewrite exp1rn mul1r -polyC_exp mulrC; apply: sym_eq.
Qed.

Lemma divp_eq  p q : 
    (lead_coef q ^+ (scalp p q)) *: p = (p %/ q) * q + (p %% q).
Proof.
rewrite divpE modpE scalpE.
case uq: (GRing.unit (lead_coef q)); last by rewrite rdivp_eq.
rewrite expr0 scale1r; case: (altP (q =P 0)) => [-> | qn0].
  rewrite mulr0 add0r lead_coef0 rmodp0 /rscalp /redivp eqxx expr0 invr1.
  by rewrite scale1r.
have hn0 : (lead_coef q ^+ rscalp p q)%:P != 0.
  by rewrite polyC_eq0 expf_neq0 // lead_coef_eq0.
apply: (mulfI hn0).
rewrite -scaler_mull -scaler_addr !mul_polyC scalerA mulrV ?unitr_exp //.
by rewrite scale1r rdivp_eq.
Qed.

(* We inline here a proof made later to be able to overload this lemma later
in the case of fields *)
Lemma divpp p : p != 0 -> p %/ p = (lead_coef p ^+ scalp p p)%:P.
Proof.
move=> np0; have := (divp_eq p p).
suff -> : p %% p = 0.
  by rewrite addr0; move/eqP; rewrite -mul_polyC (inj_eq (mulIf np0)); move/eqP.
rewrite modpE -{5 7}(mul1r p) rmodp_mull ?scaler0 ?if_same //. 
  by red; rewrite mulrC.
by apply/rregP; rewrite lead_coef_eq0.
Qed.

Lemma dvdp_eq q p : 
  (q %| p) = ((lead_coef q) ^+ (scalp p q) *: p == (p %/ q) * q).
Proof.
rewrite dvdpE rdvdp_eq scalpE divpE; case: ifP => ulcq //.
rewrite expr0 scale1r; apply/eqP/eqP.
  by rewrite -scaler_mull; move<-; rewrite scalerA mulVr ?scale1r // unitr_exp.
by move=> {2}->; rewrite scaler_mull scalerA mulrV ?scale1r // unitr_exp.
Qed.

Lemma dvdpP q p : 
  reflect (exists c, exists qq, c != 0 /\ c *: p = qq * q) (q %| p).
Proof.
rewrite dvdp_eq; apply: (iffP eqP) => [e | [c [qq [cn0 e]]]].
  by exists (lead_coef q ^+ scalp p q); exists (p %/ q); rewrite e.
apply/eqP; rewrite -dvdp_eq dvdpE.
have Ecc: c%:P != 0 by rewrite polyC_eq0.
case: (eqVneq p 0) => [->|nz_p]; first by rewrite rdvdp0.
pose p1 : {poly R} := lead_coef q ^+ rscalp p q  *: qq - c *: (rdivp p q).
have E1: c *: (rmodp p q) = p1 * q.
  rewrite mulr_addl {1}mulNr -scaler_mull -e scalerA mulrC -scalerA -scaler_mull.
  by rewrite -scaler_subr rdivp_eq addrC addKr.
rewrite /dvdp; apply/idPn=> m_nz.
have: p1 * q != 0 by rewrite -E1 -mul_polyC mulf_neq0 // -/(dvdp q p) dvdpE.
rewrite mulf_eq0; case/norP=> p1_nz q_nz; have:= ltn_rmodp p q.
rewrite q_nz -(size_scaler _ cn0) E1 size_mul_id //.
by rewrite polySpred // ltnNge leq_addl.
Qed.

Lemma mulpK p q : q != 0 ->
  p * q %/ q = lead_coef q ^+ scalp (p * q) q *: p.
Proof.
move=> qn0; move/rregP: (qn0); apply; rewrite -scaler_mull divp_eq.
suff -> : (p * q) %% q = 0 by rewrite addr0. 
rewrite modpE rmodp_mull ?scaler0 ?if_same //; first by red; rewrite mulrC.
by apply/rregP; rewrite lead_coef_eq0.
Qed.

Lemma mulKp p q :  q != 0 ->
  q * p %/ q = lead_coef q ^+ scalp (p * q) q *: p.
Proof. move=> ?; rewrite mulrC; exact: mulpK. Qed.

End  WeakTheoryForIDomainPseudoDivision.

Hint Resolve lc_expn_scalp_neq0.

Module mon.

Section MonicDivisor.

Import RPdiv.
Import ComRing.
Import UnitRing.

Variable R : idomainType.
Variable q : {poly R}.
Hypothesis monq : monic q.

Implicit Type p d r : {poly R}.

Lemma divpE p : p %/ q = rdivp p q.
Proof. by rewrite divpE (eqP monq) unitr1 exp1rn invr1 scale1r. Qed.

Lemma modpE p : p %% q = rmodp p q.
Proof. by rewrite modpE (eqP monq) unitr1 exp1rn invr1 scale1r. Qed.

Lemma scalpE p : scalp p q = 0%N.
Proof. by rewrite scalpE (eqP monq) unitr1. Qed.

Lemma divp_eq  p : p = (p %/ q) * q + (p %% q).
Proof. by rewrite -divp_eq (eqP monq) exp1rn scale1r. Qed.

Lemma divpp p : q %/ q = 1.
Proof. by rewrite divpp ?monic_neq0 // (eqP monq) exp1rn. Qed.

Lemma dvdp_eq p : (q %| p) = (p == (p %/ q) * q).
Proof. by rewrite dvdp_eq (eqP monq) exp1rn scale1r. Qed.

Lemma dvdpP p : reflect (exists qq, p = qq * q) (q %| p).
Proof.
apply: (iffP idP); first by rewrite dvdp_eq; move/eqP=> e; exists (p %/ q).
by case=> qq ->; rewrite dvdpE rdvdp_mull //; case: (monic_comreg monq).
Qed.

Lemma mulpK p : p * q %/ q = p.
Proof. by rewrite mulpK ?monic_neq0 // (eqP monq) exp1rn scale1r. Qed.

Lemma mulKp p : q * p %/ q = p.
Proof. by rewrite mulrC; exact: mulpK. Qed.

End MonicDivisor.

End mon.

End ID.



Notation "m %/ d" := (@divp _ m d) : ring_scope.
Notation "m %% d" := (@modp _ m d) : ring_scope.
Notation "p %| q" := (@dvdp _ p q) : ring_scope.

Section IDomainPseudoDivision.

Import RPdiv.
Import ComRing.
Import UnitRing.
Import ID.

Variable R : idomainType.
Implicit Type p q r d m n : {poly R}.

Lemma scalp0 p : scalp p 0 = 0%N.
Proof. by rewrite /scalp /edivp lead_coef0 unitr0 /redivp eqxx. Qed.

(* assia : was divp_size *)
Lemma divp_small p q : size p < size q -> p %/ q = 0.
Proof.
move=> spq; rewrite /divp /edivp redivp_def /=. 
by case: ifP; rewrite rdivp_small // scaler0.
Qed.

Lemma leq_divp p q : (size (p %/ q) <= size p).
Proof.
rewrite /divp /edivp redivp_def /=; case: ifP=> /=; rewrite ?leq_rdivp //.
move=> ulcq; rewrite size_scaler ?leq_rdivp //.
rewrite -expr_inv expf_neq0 // invr_eq0.
by move: ulcq; case lcq0: (lead_coef q == 0) => //; rewrite (eqP lcq0) unitr0.
Qed.

Lemma div0p p : 0 %/ p = 0.
Proof.
by rewrite /divp /edivp redivp_def /=; case: ifP; rewrite rdiv0p // scaler0.
Qed.

Lemma divp0 p : p %/ 0 = 0.
Proof.
by rewrite /divp /edivp redivp_def /=; case: ifP; rewrite rdivp0 // scaler0.
Qed.

Lemma divp1 m : m %/ 1 = m.
Proof. by rewrite divpE lead_coefC unitr1 rdivp1 exp1rn invr1 scale1r. Qed.

Lemma mod0p p : 0 %% p = 0.
Proof.
by rewrite /modp /edivp redivp_def /=; case: ifP; rewrite rmod0p // scaler0.
Qed.

Lemma modp0 p : p %% 0 = p.
Proof.
rewrite /modp /edivp redivp_def; case: ifP; rewrite rmodp0 //= lead_coef0. 
by rewrite unitr0.
Qed.

Lemma modp1 p : p %% 1 = 0.
Proof.
by rewrite /modp /edivp redivp_def /=; case: ifP; rewrite rmodp1 // scaler0.
Qed.

Hint Resolve divp0 divp1 mod0p modp0 modp1.

Lemma modp_small p q : size p < size q -> p %% q = p.
Proof.
move=> spq; rewrite /modp /edivp redivp_def; case: ifP; rewrite rmodp_small //.
by rewrite /= rscalp_small // expr0 /= invr1 scale1r.
Qed.

Lemma modpC p c : c != 0 -> p %% c%:P = 0.
Proof.
move=> cn0; rewrite /modp /edivp redivp_def /=; case: ifP; rewrite ?rmodpC //.
by rewrite scaler0.
Qed.

Lemma modp_mull p q : (p * q) %% q = 0.
Proof. 
case: (altP (q =P 0)) => [-> | nq0]; first by rewrite modp0 mulr0.
have rlcq :  (GRing.rreg (lead_coef q)) by apply/rregP; rewrite lead_coef_eq0.
have hC :  GRing.comm q (lead_coef q)%:P by red; rewrite mulrC.
by rewrite modpE; case: ifP => ulcq; rewrite rmodp_mull // scaler0.
Qed.

Lemma modp_mulr d p : (d * p) %% d = 0.
Proof. by rewrite mulrC modp_mull. Qed.

Lemma modpp d : d %% d = 0.
Proof. by rewrite -{1}(mul1r d) modp_mull. Qed.


(* assia : was modp_spec *)
Lemma ltn_modp p q : (size (p %% q) < size q) = (q != 0).
Proof.
rewrite /modp /edivp redivp_def /=; case: ifP=> /=; rewrite ?ltn_rmodp //.
move=> ulcq; rewrite size_scaler ?ltn_rmodp //.
rewrite -expr_inv expf_neq0 // invr_eq0.
by move: ulcq; case lcq0: (lead_coef q == 0) => //; rewrite (eqP lcq0) unitr0.
Qed.

Lemma ltn_divpl d q p : d != 0 -> 
   (size (q %/ d) < size p) = (size q < size (p * d)).
Proof.
move=> dn0; have sd : size d > 0 by rewrite size_poly_neq0 dn0.
have: (lead_coef d) ^+ (scalp q d) != 0 by []. 
move/size_scaler; move/(_ q)<-; rewrite divp_eq; case quo0 : (q %/ d == 0).
  rewrite (eqP quo0) mul0r add0r size_poly0.
  case p0 : (p == 0); first by rewrite (eqP p0) mul0r size_poly0 ltnn ltn0.
  have sp : size p > 0 by rewrite size_poly_neq0 p0.
  rewrite /= size_mul_id ?p0 // sp; apply: sym_eq; move/prednK:(sp)<-.
  by rewrite addSn /= ltn_addl // ltn_modp.
rewrite size_addl; last first.
  rewrite size_mul_id ?quo0 //; move/negbT: quo0; rewrite -size_poly_neq0.
  by move/prednK<-; rewrite addSn /= ltn_addl // ltn_modp.
case: (altP (p =P 0)) => [-> | pn0]; first by rewrite mul0r size_poly0 !ltn0.
by rewrite !size_mul_id ?quo0 //; move/prednK: sd<-; rewrite !addnS ltn_add2r.
Qed.

Lemma leq_divpr d p q : d != 0 -> 
   (size p <= size (q %/ d)) = (size (p * d) <= size q).
Proof. by move=> dn0; rewrite leqNgt ltn_divpl // -leqNgt. Qed.

Lemma divpN0 d p : d != 0 -> (p %/ d != 0) = (size d <= size p).
Proof.
move=> dn0; rewrite -{2}(mul1r d) -leq_divpr // size_polyC oner_eq0 /=.
by rewrite size_poly_neq0.
Qed.

Lemma size_divp p q : q != 0 -> size (p %/ q) = ((size p) - (size q).-1)%N.
Proof.
move=> nq0; case: (leqP (size q) (size p)) => sqp; last first.
  move: (sqp); rewrite -{1}(ltn_predK sqp) ltnS -subn_eq0 divp_small //.
  by move/eqP->; rewrite size_poly0.
move: (nq0); rewrite -size_poly_neq0 => lt0sq.
move: (sqp); move/(leq_trans lt0sq) => lt0sp.
move: (lt0sp); rewrite size_poly_neq0=> p0.
move: (divp_eq p q); move/(congr1 (size \o (@polyseq R)))=> /=.
rewrite size_scaler; last by rewrite expf_eq0 lead_coef_eq0 (negPf nq0) andbF.
case: (eqVneq (p %/ q) 0) => [-> | qq0].
  by rewrite mul0r add0r=> es; move: nq0; rewrite -(ltn_modp p) -es ltnNge sqp.
move/negP:(qq0); move/negP; rewrite -size_poly_neq0 => lt0qq.
rewrite size_addl.
  rewrite size_mul_id ?qq0 // => ->.
  apply/eqP; rewrite -(eqn_addr ((size q).-1)).
  rewrite subnK; first by rewrite -subn1 addn_subA // subn1.
  rewrite /leq -(subn_add2l 1%N) !add1n prednK // (@ltn_predK (size q)) //.
    by rewrite addnC -subn_sub subnn sub0n.
  by rewrite -[size q]add0n ltn_add2r.
rewrite size_mul_id ?qq0 //.
move: nq0; rewrite -(ltn_modp p); move/leq_trans; apply; move/prednK: lt0qq<-.
by rewrite addSn /= leq_addl.
Qed.

Lemma ltn_modpN0 p q : q != 0 -> size (p %% q) < size q.
Proof. by rewrite ltn_modp. Qed.

Lemma modp_mod p q : (p %% q) %% q = p %% q.
Proof.
by case: (eqVneq q 0) => [-> | qn0]; rewrite ?modp0 // modp_small ?ltn_modp.
Qed.

Lemma leq_modp m d : size (m %% d)  <= size m.
Proof.
rewrite /modp /edivp redivp_def /=; case: ifP; rewrite ?leq_rmodp //.
move=> ud; rewrite size_scaler ?leq_rmodp // invr_eq0 expf_neq0 //.
by apply: contraTneq ud => ->; rewrite unitr0.
Qed.

Lemma dvdp0 d : d %| 0.
Proof. by rewrite /dvdp mod0p. Qed.

Hint Resolve dvdp0.

Lemma dvd0p p : (0 %| p) = (p == 0).
Proof. by rewrite /dvdp modp0. Qed.

Lemma dvd0pP p : reflect (p = 0) (0 %| p).
Proof. by apply: (iffP idP); rewrite dvd0p; move/eqP. Qed.

Lemma dvdpN0 p q : p %| q -> q != 0 -> p != 0.
Proof. by move=> pq hq; apply: contraL pq=> /eqP ->; rewrite dvd0p. Qed.

Lemma dvdp1 d : (d %| 1) = ((size d) == 1%N).
Proof.
rewrite /dvdp modpE; case ud: (GRing.unit (lead_coef d)); last exact: rdvdp1.
rewrite -size_poly_eq0 size_scaler; first by rewrite size_poly_eq0; exact: rdvdp1.
by rewrite invr_eq0 expf_neq0 //; apply: contraTneq ud => ->; rewrite unitr0.
Qed.

Lemma dvd1p m : 1 %| m.
Proof. by rewrite /dvdp modp1. Qed.

Lemma gtNdvdp p q : p != 0 -> size p < size q -> (q %| p) = false.
Proof. 
by move=> nn0 hs; rewrite /dvdp; rewrite (modp_small hs); apply: negPf.
Qed.

Lemma modp_eq0P p q : reflect (p %% q = 0) (q %| p).
Proof. exact: (iffP eqP). Qed.

Lemma modp_eq0 p q : (q %| p) -> p %% q = 0.
Proof. by move/modp_eq0P. Qed.

Lemma leq_divpl d p q : 
  d %| p -> (size (p %/ d) <= size q) = (size p <= size (q * d)).
Proof.
case: (eqVneq d 0) => [-> | nd0].
  by move/dvd0pP->; rewrite divp0 size_poly0 !leq0n.
move=> hd; rewrite leq_eqVlt ltn_divpl // (leq_eqVlt (size p)).
case lhs: (size p < size (q * d)); rewrite ?orbT ?orbF //.
have: (lead_coef d) ^+ (scalp p d) != 0 by rewrite expf_neq0 // lead_coef_eq0.
move/size_scaler; move/(_ p)<-; rewrite divp_eq.
move/modp_eq0P: hd->; rewrite addr0; case: (altP (p %/ d =P 0))=> [-> | quon0].
  rewrite mul0r size_poly0 eq_sym (eq_sym 0%N) size_poly_eq0.
  case: (altP (q =P 0)) => [-> | nq0]; first by rewrite mul0r size_poly0 eqxx.
  by rewrite size_poly_eq0 mulf_eq0 (negPf nq0) (negPf nd0).
case: (altP (q =P 0)) => [-> | nq0].
  by rewrite mul0r size_poly0 !size_poly_eq0 mulf_eq0 (negPf nd0) orbF.
rewrite !size_mul_id //; move: nd0; rewrite -size_poly_neq0; move/prednK<-.
by rewrite !addnS /= eqn_addr.
Qed.


Lemma dvdp_leq p q : q != 0 -> p %| q -> size p <= size q.
move=> nq0; case/modp_eq0P => rpq; case: (ltnP (size p) (size q)); first by move/ltnW->.
rewrite leq_eqVlt; case/orP; first by move/eqP->. 
by move/modp_small; rewrite rpq => h; move: nq0; rewrite h eqxx.
Qed.

Lemma eq_dvdp c quo q p : c != 0 -> c *: p = quo * q -> q %| p.
Proof.
move=> cn0; case: (eqVneq p 0) => [->|nz_quo def_quo] //. 
pose p1 : {poly R} := lead_coef q ^+ scalp p q  *: quo - c *: (p %/ q).
have E1: c *: (p %% q) = p1 * q.
  rewrite mulr_addl {1}mulNr-scaler_mull -def_quo scalerA mulrC -scalerA.
  by rewrite -scaler_mull -scaler_subr divp_eq addrAC subrr add0r.
rewrite /dvdp; apply/idPn=> m_nz.
have: p1 * q != 0 by rewrite -E1 -mul_polyC mulf_neq0 // polyC_eq0.
rewrite mulf_eq0; case/norP=> p1_nz q_nz.
have := (ltn_modp p q); rewrite q_nz -(size_scaler (p %% q) cn0) E1.
by rewrite  size_mul_id // polySpred // ltnNge leq_addl.
Qed.

Lemma dvdpp d : d %| d.
Proof. by rewrite /dvdp modpp. Qed.

Hint Resolve dvdpp.

Lemma divp_dvd p q : (p %| q) -> ((q %/ p) %| q).
Proof.
case: (eqVneq p 0) => [-> | np0]; first by rewrite divp0.
rewrite dvdp_eq => /eqP h.
apply: (@eq_dvdp ((lead_coef p)^+ (scalp q p)) p); last by rewrite mulrC.
by rewrite expf_neq0 // lead_coef_eq0.
Qed.

Lemma dvdp_mull m d n : d %| n -> d %| m * n.
Proof. 
case: (eqVneq d 0) => [-> |dn0]; first by move/dvd0pP->; rewrite mulr0 dvdpp.
rewrite dvdp_eq => /eqP e. 
apply: (@eq_dvdp (lead_coef d ^+ scalp n d) (m * (n %/ d))).
  by rewrite expf_neq0 // lead_coef_eq0.
by rewrite scaler_mulr e mulrA.
Qed.

Lemma dvdp_mulr n d m : d %| m -> d %| m * n.
Proof. by move=> hdm; rewrite mulrC dvdp_mull. Qed.

Hint Resolve dvdp_mull dvdp_mulr.

Lemma dvdp_mul d1 d2 m1 m2 : d1 %| m1 -> d2 %| m2 -> d1 * d2 %| m1 * m2.
Proof.
case: (eqVneq d1 0) => [-> |d1n0]; first by move/dvd0pP->; rewrite !mul0r dvdpp.
case: (eqVneq d2 0) => [-> |d2n0]; first by move => _ /dvd0pP ->; rewrite !mulr0.
rewrite dvdp_eq; set c1 := _ ^+ _; set q1 := _ %/ _; move/eqP=> Hq1.
rewrite dvdp_eq; set c2 := _ ^+ _; set q2 := _ %/ _; move/eqP=> Hq2.
apply: (@eq_dvdp (c1 * c2) (q1 * q2)).
  by rewrite mulf_neq0 // expf_neq0 // lead_coef_eq0.
rewrite -scalerA scaler_mulr scaler_mull Hq1 Hq2 -!mulrA. 
by rewrite [d1 * (q2 * _)]mulrCA.
Qed.

Lemma dvdp_addr m d n : d %| m -> (d %| m + n) = (d %| n).
Proof.
case: (altP (d =P 0)) => [-> | dn0]; first by move/dvd0pP->; rewrite add0r.
rewrite dvdp_eq; set c1 := _ ^+ _; set q1 := _ %/ _; move/eqP=> Eq1.
apply/idP/idP; rewrite dvdp_eq; set c2 := _ ^+ _; set q2 := _ %/ _; move/eqP=> Eq2.
  have sn0 : c1 * c2 != 0.     
    by rewrite !mulf_neq0 // expf_eq0 lead_coef_eq0 (negPf dn0) andbF.
  apply: (@eq_dvdp _ (c1 *: q2 - c2 *: q1) _ _ sn0).
  rewrite mulr_addl -scaleNr -!scaler_mull -Eq1 -Eq2 !scalerA.
  by rewrite mulNr mulrC scaleNr -scaler_subr addrC addKr.
  have sn0 : c1 * c2 != 0.     
    by rewrite !mulf_neq0 // expf_eq0 lead_coef_eq0 (negPf dn0) andbF.
  apply: (@eq_dvdp _ (c1 *: q2 + c2 *: q1) _ _ sn0).
by  rewrite mulr_addl -!scaler_mull -Eq1 -Eq2 !scalerA mulrC addrC scaler_addr.
Qed.

Lemma dvdp_addl : forall n d m : {poly R}, d %| n -> (d %| m + n) = (d %| m).
Proof. by move=> n d m; rewrite addrC; exact: dvdp_addr. Qed.

Lemma dvdp_add : forall d m n : {poly R}, d %| m -> d %| n -> d %| m + n.
Proof. by move=> n d m; move/dvdp_addr->. Qed.

Lemma dvdp_add_eq : forall d m n : {poly R}, d %| m + n -> (d %| m) = (d %| n).
Proof. by move=> *; apply/idP/idP; [move/dvdp_addr <-| move/dvdp_addl <-]. Qed.

Lemma dvdp_subr : forall d m n : {poly R}, d %| m -> (d %| m - n) = (d %| n).
Proof. by move=> *; apply dvdp_add_eq; rewrite -addrA addNr simp. Qed.

Lemma dvdp_subl : forall d m n : {poly R}, d %| n -> (d %| m - n) = (d %| m).
Proof. by move=> d m n Hn; rewrite -(dvdp_addl _ Hn) subrK. Qed.

Lemma dvdp_sub : forall d m n : {poly R}, d %| m -> d %| n -> d %| m - n.
Proof.  by move=> d n m Dm Dn; rewrite dvdp_subl. Qed.

Lemma dvdp_mod d n m : d %| n -> (d %| m) = (d %| m %% n).
Proof.
case: (altP (n =P 0)) => [-> | nn0]; first by rewrite modp0.
case: (altP (d =P 0)) => [-> | dn0]; first by move/dvd0pP->; rewrite modp0.
rewrite dvdp_eq; set c1 := _ ^+ _; set q1 := _ %/ _; move/eqP=> Eq1.
apply/idP/idP; rewrite dvdp_eq; set c2 := _ ^+ _; set q2 := _ %/ _; move/eqP=> Eq2.
  have sn0 : c1 * c2 != 0.     
   by rewrite !mulf_neq0 // expf_eq0 lead_coef_eq0 (negPf dn0) andbF.
  pose quo :=  (c1 * lead_coef n ^+ scalp m n) *: q2 - c2 *: (m %/ n) * q1.
  apply: (@eq_dvdp _ quo _ _ sn0); rewrite mulr_addl mulNr -!scaler_mull -!mulrA.
  rewrite  -Eq1 -Eq2 -scaler_mulr !scalerA mulrC [_ * c2]mulrC mulrA.
  by rewrite -[((_ * _) * _) *: _]scalerA -scaler_subr divp_eq addrC addKr.
have sn0 : c1 * c2 * lead_coef n ^+ scalp m n != 0.
  by rewrite !mulf_neq0 // expf_eq0 lead_coef_eq0 ?(negPf dn0) ?(negPf nn0) andbF.
apply: (@eq_dvdp _ (c2 *: (m  %/ n) * q1 + c1 *: q2) _ _ sn0).
  rewrite -scalerA divp_eq scaler_addr -!scalerA Eq2 scaler_mull scaler_mulr Eq1.
  by rewrite scaler_mull mulr_addl mulrA.
Qed.

Lemma dvdp_trans : transitive (@dvdp R).
Proof.
move=> n d m. 
case: (altP (d =P 0)) => [-> | dn0]; first by move/dvd0pP->.
case: (altP (n =P 0)) => [-> | nn0]; first by move=> _ /dvd0pP ->.
rewrite dvdp_eq; set c1 := _ ^+ _; set q1 := _ %/ _; move/eqP=> Hq1.
rewrite dvdp_eq; set c2 := _ ^+ _; set q2 := _ %/ _; move/eqP=> Hq2.
have sn0 : c1 * c2 != 0 by rewrite mulf_neq0 // expf_neq0 // lead_coef_eq0.
by apply: (@eq_dvdp _ (q2 * q1) _ _ sn0); rewrite -scalerA Hq2 scaler_mulr Hq1 mulrA.
Qed.

Lemma dvdp_mulIl p q : p %| p * q. Proof. by apply: dvdp_mulr; exact: dvdpp. Qed.

Lemma dvdp_mulIr p q : q %| p * q. Proof. by apply: dvdp_mull; exact: dvdpp. Qed.

Lemma dvdp_mul2r r p q : r != 0 -> (p * r %| q * r) = (p %| q).
Proof.
move => nzr.
case: (eqVneq p 0) => [-> | pn0].
  by rewrite mul0r !dvd0p mulf_eq0 (negPf nzr) orbF.
case: (eqVneq q 0) => [-> | qn0]; first by rewrite mul0r !dvdp0.
apply/idP/idP; last by move => ?; rewrite dvdp_mul ?dvdpp.
rewrite dvdp_eq; set c := _ ^+ _; set x := _ %/ _; move/eqP=> Hx.
apply: (@eq_dvdp c x).
  by rewrite expf_neq0 // lead_coef_eq0 mulf_neq0.
by apply: (GRing.mulIf nzr); rewrite -GRing.mulrA -GRing.scaler_mull.
Qed.

Lemma dvdp_mul2l r p q: r != 0 -> (r * p %| r * q) = (p %| q).
Proof. by rewrite ![r * _]GRing.mulrC; apply: dvdp_mul2r. Qed.

Lemma ltn_divpr d p q : 
  d %| q -> (size p < size (q %/ d)) = (size (p * d) < size q).
Proof. by move=> dv_d_q; rewrite !ltnNge leq_divpl. Qed.

Lemma dvdp_exp d k p : 0 < k -> d %| p -> d %| (p ^+ k).
Proof. by case: k => // k _ d_dv_m; rewrite exprS dvdp_mulr. Qed.

Lemma dvdp_exp2l d k l : k <= l -> d ^+ k %| d ^+ l.
Proof.
by move/subnK <-; rewrite exprn_addr dvdp_mull // ?lead_coef_exp_id ?unitr_exp.
Qed.

Lemma dvdp_Pexp2l  d k l : 1 < size d -> (d ^+ k %| d ^+ l) = (k <= l).
Proof.
move=> sd; case: leqP => [|gt_n_m]; first exact: dvdp_exp2l.
have dn0 : d != 0 by rewrite -size_poly_neq0; apply: ltn_trans sd.
rewrite gtNdvdp ?expf_neq0 // polySpred ?expf_neq0 // size_exp_id /=.
rewrite [size (d ^+ k)]polySpred ?expf_neq0 // size_exp_id ltnS ltn_mul2l.
by move: sd; rewrite -subn_gt0 subn1; move->.
Qed.

Lemma dvdp_exp2r p q k : p %| q -> p ^+ k %| q ^+ k.
Proof.
case: (eqVneq p 0) => [-> | pn0]; first by move/dvd0pP->.
rewrite dvdp_eq; set c := _ ^+ _; set t := _ %/ _; move/eqP=> e.
apply: (@eq_dvdp (c ^+ k) (t ^+ k)); first by rewrite !expf_neq0 ?lead_coef_eq0.
by rewrite -exprn_mull -scaler_exp; congr (_ ^+ k).
Qed.

Lemma dvdp_exp_sub p q k l: p != 0 ->
  (p ^+ k %| q * p ^+ l) = (p ^+ (k - l) %| q).
Proof.
move=> pn0; case: (leqP k l)=> hkl.
  move:(hkl); rewrite -subn_eq0; move/eqP->; rewrite expr0 dvd1p.
  apply: dvdp_mull; case: (ltnP 1%N (size p)) => sp; first by rewrite dvdp_Pexp2l.
  move: sp; case esp: (size p) => [|sp].
    by move/eqP: esp; rewrite size_poly_eq0 (negPf pn0).
  rewrite ltnS leqn0; move/eqP=> sp0; move/eqP: esp; rewrite sp0.
  by case/size1P => c cn0 ->; move/subnK: hkl<-; rewrite exprn_addr dvdp_mulIr.
rewrite -{1}[k](@subnK l) 1?ltnW// exprn_addr dvdp_mul2r//.
elim: l {hkl}=> [|l ihl]; first by rewrite expr0 oner_eq0.
by rewrite exprS mulf_neq0.
Qed.

Lemma dvdp_factorl p x : ('X - x%:P) %| p = root p x.
Proof. rewrite dvdpE; exact: rdvdp_factorl. Qed.

Lemma factorP p x : reflect (p.[x] = 0) (('X - x%:P) %| p).
Proof. rewrite dvdpE; exact: factorP. Qed.

Lemma eqp_div_factor p c : 
  (p == (p %/ ('X - c%:P)) * ('X - c%:P)) = ('X - c%:P %| p).
Proof. by rewrite dvdp_eq lead_coef_factor exp1rn scale1r. Qed.

Lemma root_factor_theorem p x : root p x = (('X - x%:P) %| p).
Proof. by rewrite dvdp_factorl. Qed.

Lemma uniq_roots_dvdp p rs : all (root p) rs -> uniq_roots rs ->
  (\prod_(z <- rs) ('X - z%:P)) %| p.
Proof.
move=> rrs; case/(uniq_roots_factors rrs)=> q ->.
by apply: dvdp_mull; rewrite // (eqP (monic_prod_factors _)) unitr1.
Qed.


Lemma root_bigmul : forall x (ps : seq {poly R}),
  ~~root (\big[*%R/1]_(p <- ps) p) x = all (fun p => ~~ root p x) ps.
Proof.
move=> x; elim; first by rewrite big_nil root1.
by move=> p ps ihp; rewrite big_cons /= root_mul negb_or ihp.
Qed.

Definition eqp p q :=  (p %| q) && (q %| p).
Notation "p %= q" := (eqp p q) : ring_scope.

Lemma eqpP m n :
  reflect (exists c1, exists c2, [/\ c1 != 0, c2 != 0 & c1 *: m = c2 *: n])
          (m %= n).
Proof.
apply: (iffP idP) => [|[c1 [c2 [nz_c1 nz_c2 eq_cmn]]]]; rewrite /eqp; last first.
  rewrite (@eq_dvdp c2 c1%:P) // -?eq_cmn ?mul_polyC // (@eq_dvdp c1 c2%:P) //.
  by rewrite eq_cmn mul_polyC.
case: (eqVneq m 0) => [-> | m_nz].
  by case/andP => /dvd0pP -> _; do 2! exists 1; rewrite scaler0 oner_eq0.
case: (eqVneq n 0) => [-> | n_nz].
  by case/andP => _ /dvd0pP ->; do 2! exists 1; rewrite scaler0 oner_eq0.
case/andP; rewrite !dvdp_eq; set c1 := _ ^+ _; set c2 := _ ^+ _.
set q1 := _ %/ _; set q2 := _ %/ _; move/eqP => Hq1 /eqP Hq2; 
have Hc1 : c1 != 0 by rewrite expf_eq0 lead_coef_eq0 negb_and m_nz orbT.
have Hc2 : c2 != 0 by rewrite expf_eq0 lead_coef_eq0 negb_and n_nz orbT.
have def_q12: q1 * q2 = (c1 * c2)%:P.
  apply: (mulIf m_nz); rewrite mulrAC mulrC -Hq1 -scaler_mulr -Hq2 scalerA.
  by rewrite -mul_polyC.
have: q1 * q2 != 0 by rewrite def_q12 -size_poly_eq0 size_polyC mulf_neq0.
rewrite mulf_eq0; case/norP=> nz_q1 nz_q2.
exists c2; exists q2`_0.
rewrite -[_ *: n]mul_polyC Hc2 -polyC_eq0 -size1_polyC //.
have:= size_mul_id nz_q1 nz_q2; rewrite def_q12 size_polyC mulf_neq0 //=.
by rewrite polySpred // => ->; rewrite leq_addl.
Qed.

Lemma eqpxx : reflexive eqp.
Proof. by move=> p; rewrite /eqp dvdpp. Qed.

Hint Resolve eqpxx.

Lemma eqp_sym : symmetric eqp.
Proof. by move=> p q; rewrite /eqp andbC. Qed.

Lemma eqp_trans : transitive eqp.
Proof.
move=> p q r; case/andP=> Dp pD; case/andP=> Dq qD.
by rewrite /eqp (dvdp_trans Dp) // (dvdp_trans qD).
Qed.

Lemma eqp_ltrans : left_transitive eqp.
Proof.
move=> p q r pq.
by apply/idP/idP=> e; apply: eqp_trans e; rewrite // eqp_sym.
Qed.

Lemma eqp_rtrans : right_transitive eqp.
Proof. by move=> x y xy z; rewrite eqp_sym (eqp_ltrans xy) eqp_sym. Qed.

Lemma eqp0 : forall p, (p %= 0) = (p == 0).
Proof.
move=> p; case: eqP; move/eqP=> Ep; first by rewrite (eqP Ep) eqpxx.
by apply/negP; case/andP=> _; rewrite /dvdp modp0 (negPf Ep).
Qed.

Lemma eqp01 : 0 %= (1 : {poly R}) = false.
Proof.
case abs : (0 %= 1) => //; case/eqpP: abs=> c1 [c2 [c1n0 c2n0]].
by rewrite scaler0 scale_poly1; move/eqP; rewrite eq_sym polyC_eq0 (negbTE c2n0).
Qed.

Lemma scale_eqp p c : c != 0 -> c *: p %= p.
Proof.
move=> c0; apply/eqpP; exists 1; exists c; rewrite c0 oner_eq0.
by split=> //; rewrite scale1r.
Qed.

Lemma size_eqp : forall p q, p %= q -> size p = size q.
Proof.
move=> p q.
case: (q =P 0); move/eqP => Eq; first by rewrite (eqP Eq) eqp0; move/eqP->.
rewrite eqp_sym; case: (p =P 0); move/eqP => Ep.
  by rewrite (eqP Ep) eqp0; move/eqP->.
by case/andP => Dp Dq; apply: anti_leq; rewrite !dvdp_leq.
Qed.

Lemma size_poly_eq1 : forall p, (size p == 1%N) = (p %= 1).
Proof.
move=> p; apply/size1P/idP=> [[c [cn0 ep]] |].
  by apply/eqpP; exists 1; exists c; rewrite oner_eq0 scale_poly1 scale1r.
by move/size_eqp; rewrite size_poly1; move/eqP; move/size1P.
Qed.

Lemma dvdp_eqp1 : forall p q, p %| q -> q %= 1 -> p %= 1.
Proof.
move=> p q dpq hq.
have sizeq : size q == 1%N by rewrite size_poly_eq1.
have n0q : q != 0.
  by case abs: (q == 0) => //; move: hq; rewrite (eqP abs) eqp01.
rewrite -size_poly_eq1 eqn_leq -{1}(eqP sizeq) dvdp_leq //=.
case p0 : (size p == 0%N); last by rewrite neq0_lt0n.
by move: dpq;  rewrite size_poly_eq0 in p0; rewrite (eqP p0) dvd0p (negbTE n0q).
Qed.

Lemma eqp_dvdr q p d: p %= q -> d %| p = (d %| q).
Proof.
suff Hmn m n: m %= n -> (d %| m) -> (d %| n).
  by move=> mn; apply/idP/idP; apply: Hmn=> //; rewrite eqp_sym.
by rewrite /eqp; case/andP=> pq qp dp; apply: (dvdp_trans dp).
Qed.

Lemma eqp_dvdl d2 d1 p : d1 %= d2 -> d1 %| p = (d2 %| p).
suff Hmn m n: m %= n -> (m %| p) -> (n %| p).
  by move=> ?; apply/idP/idP; apply: Hmn; rewrite // eqp_sym.
by rewrite /eqp; case/andP=> dd' d'd dp; apply: (dvdp_trans d'd).
Qed.

Lemma dvdp_scaler c m n : c != 0 -> m %| c *: n = (m %| n).
Proof. move=> cn0; apply: eqp_dvdr; exact: scale_eqp. Qed.

Lemma dvdp_scalel c m n : c != 0 -> (c *: m %| n) = (m %| n).
Proof. move=> cn0; apply: eqp_dvdl; exact: scale_eqp. Qed.

Lemma dvdp_opp d p : d %| (- p) = (d %| p).
Proof. 
by apply: eqp_dvdr; rewrite -scaleN1r scale_eqp // oppr_eq0 oner_eq0.
Qed.

Lemma eqp_mul2r r p q : r != 0 -> (p * r %= q * r) = (p %= q).
Proof. by move => nz_r; rewrite /eqp !dvdp_mul2r. Qed.

Lemma eqp_mul2l r p q: r != 0 -> (r * p %= r * q) = (p %= q).
Proof. by move => nz_r; rewrite /eqp !dvdp_mul2l. Qed.

Lemma eqp_mull r p q: (q %= r) -> (p * q %= p * r).
Proof.
case/eqpP=> [c [d [c0 d0 e]]]; apply/eqpP; exists c; exists d.
by split=> //; rewrite scaler_mulr e -scaler_mulr.
Qed.

Lemma eqp_mulr q p r : (p %= q) -> (p * r %= q * r).
Proof. by move=>  epq; rewrite ![_ * r]mulrC eqp_mull. Qed.

Lemma eqp_exp  p q k : p %= q -> p ^+ k %= q ^+ k.
Proof.
move=> pq; elim: k=> [|k ihk]; first by rewrite !expr0 eqpxx.
by rewrite !exprS (@eqp_trans (q * p ^+ k)) // (eqp_mulr, eqp_mull).
Qed.

Lemma polyC_eqp1 c : (c%:P %= 1) = (c != 0).
Proof.
apply/eqpP/idP => [[x] [y]|nc0].
  case c0: (c == 0); rewrite // scale_poly1 (eqP c0) scaler0.
  by case=> _ /=; move/negbTE<-; move/eqP; rewrite eq_sym polyC_eq0.
by exists 1; exists c; rewrite nc0 /= nonzero1r scale_poly1 scale1r.
Qed.

Lemma dvdUp d p: d %= 1 -> d %| p.
Proof. by move/eqp_dvdl->; rewrite dvd1p. Qed. 

Lemma dvdp_size_eqp p q : p %| q -> size p == size q = (p %= q).
Proof.
move=> pq; apply/idP/idP; last by move/size_eqp->.
case (q =P 0)=> [->|]; [|move/eqP => Hq].
  by rewrite size_poly0 size_poly_eq0; move/eqP->; rewrite eqpxx.
case (p =P 0)=> [->|]; [|move/eqP => Hp].
  by rewrite size_poly0 eq_sym size_poly_eq0; move/eqP->; rewrite eqpxx.
move: pq; rewrite dvdp_eq; set c := _ ^+ _; set x := _ %/ _; move/eqP=> eqpq.
move:(eqpq); move/(congr1 (size \o (@polyseq R)))=> /=.
have cn0 : c != 0 by  rewrite expf_neq0 // lead_coef_eq0.
rewrite (@size_eqp _ q); last  by exact: scale_eqp.
rewrite size_mul_id ?p0 // => [-> HH|]; last first.
  apply/eqP=> HH; move: eqpq; rewrite HH mul0r.
  by move/eqP; rewrite scale_poly_eq0 (negPf Hq) (negPf cn0).
suff: size x == 1%N.
  case/size1P=> y [H1y H2y].
  apply/eqpP; exists y; exists c; first by rewrite eqpq H2y mul_polyC.
case: (size p) HH (size_poly_eq0 p)=> [|n]; first by case: eqP Hp.
by rewrite addnS -add1n eqn_addr;move/eqP->.
Qed.

Lemma eqp_root p q : p %= q -> root p =1 root q.
Proof.
move/eqpP=> [c [d [c0 d0 e]]] x; move/negPf:c0=>c0; move/negPf:d0=>d0.
rewrite rootE -[_==_]orFb -c0 -mulf_eq0 -horner_scaler e horner_scaler.
by rewrite mulf_eq0 d0.
Qed.

Lemma eqp_rmodp_modp p q : rmodp p q %= modp p q.
Proof.
rewrite modpE eqp_sym; case: ifP=> ulcq //; apply: scale_eqp; rewrite invr_eq0 //.
by apply: expf_neq0; apply: contraTneq ulcq => ->; rewrite unitr0.
Qed.

Lemma eqp_rdivp_divp p q : rdivp p q %= divp p q.
Proof.
rewrite divpE eqp_sym; case: ifP=> ulcq //; apply: scale_eqp; rewrite invr_eq0 //.
by apply: expf_neq0; apply: contraTneq ulcq => ->; rewrite unitr0.
Qed.

Definition gcdp_rec p q :=
  let: (p1, q1) := if size p < size q then (q, p) else (p, q) in
  if p1 == 0 then q1 else
  let fix loop (n : nat) (pp qq : {poly R}) {struct n} :=
      let rr := modp pp qq in
      if rr == 0 then qq else
      if n is n1.+1 then loop n1 qq rr else rr in
  loop (size p1) p1 q1.

Definition gcdp := nosimpl gcdp_rec.

Lemma gcd0p : left_id 0 gcdp.
Proof.
move=> p; rewrite /gcdp /gcdp_rec size_poly0 size_poly_neq0 if_neg.
case: ifP => /= [_ | nzp]; first by rewrite eqxx.
by rewrite polySpred !(modp0, nzp) //; case: _.-1 => [|m]; rewrite mod0p eqxx.
Qed.

Lemma gcdp0 : right_id 0 gcdp.
Proof.
move=> p; have:= gcd0p p; rewrite /gcdp /gcdp_rec size_poly0 size_poly_neq0.
by rewrite if_neg; case: ifP => /= p0; rewrite ?(eqxx, p0) // (eqP p0).
Qed.

Lemma gcdpE p q :
  gcdp p q = if size p < size q 
    then gcdp (modp q p) p else gcdp (modp p q) q.
Proof.
pose gcdpE_rec := fix gcdpE_rec (n : nat) (pp qq : {poly R}) {struct n} :=
   let rr := modp pp qq in
   if rr == 0 then qq else
   if n is n1.+1 then gcdpE_rec n1 qq rr else rr.
have Irec: forall k l p q, size q <= k -> size q <= l
      -> size q < size p -> gcdpE_rec k p q = gcdpE_rec l p q.
+ elim=> [|m Hrec] [|n] //= p1 q1.
  - rewrite leqn0 size_poly_eq0; move/eqP=> -> _.
    rewrite size_poly0 size_poly_neq0 modp0 => nzp.
    by rewrite (negPf nzp); case: n => [|n] /=; rewrite mod0p eqxx.
  - rewrite leqn0 size_poly_eq0 => _; move/eqP=> ->.
    rewrite size_poly0 size_poly_neq0 modp0 => nzp.
    by rewrite (negPf nzp); case: m {Hrec} => [|m] /=; rewrite mod0p eqxx.
  case: ifP => Epq Sm Sn Sq //; rewrite ?Epq //.
  case: (eqVneq q1 0) => [->|nzq].
    by case: n m {Sm Sn Hrec} => [|m] [|n] //=; rewrite mod0p eqxx.
  apply: Hrec; last by rewrite ltn_modp.
    by rewrite -ltnS (leq_trans _ Sm) // ltn_modp.
  by rewrite -ltnS (leq_trans _ Sn) // ltn_modp.
case: (eqVneq p 0) => [-> | nzp].
  by rewrite mod0p modp0 gcd0p gcdp0 if_same.
case: (eqVneq q 0) => [-> | nzq].
  by rewrite mod0p modp0 gcd0p gcdp0 if_same.
rewrite /gcdp /gcdp_rec.
case: ltnP; rewrite (negPf nzp, negPf nzq) //=.
  move=> ltpq; rewrite ltn_modp (negPf nzp) //=.
  rewrite -(ltn_predK ltpq) /=; case: eqP => [->|].
    by case: (size p) => [|[|s]]; rewrite /= modp0 (negPf nzp) // mod0p eqxx.
  move/eqP=> nzqp; rewrite (negPf nzp).
  apply: Irec => //; last by rewrite ltn_modp.
    by rewrite -ltnS (ltn_predK ltpq) (leq_trans _ ltpq) ?leqW // ltn_modp.
  by rewrite ltnW // ltn_modp.
move=> leqp; rewrite ltn_modp (negPf nzq) //=.
have p_gt0: size p > 0 by rewrite size_poly_neq0.
rewrite -(prednK p_gt0) /=; case: eqP => [->|].
  by case: (size q) => [|[|s]]; rewrite /= modp0 (negPf nzq) // mod0p eqxx.
move/eqP=> nzpq; rewrite (negPf nzq); apply: Irec => //; rewrite ?ltn_modp //.
  by rewrite -ltnS (prednK p_gt0) (leq_trans _ leqp) // ltn_modp.
by rewrite ltnW // ltn_modp.
Qed.

Lemma size_gcd1p p : size (gcdp 1 p) = 1%N.
Proof.
rewrite gcdpE size_polyC oner_eq0 /= modp1; case: ltnP.
  by rewrite gcd0p size_polyC oner_eq0.
move/size1_polyC=> e; rewrite e.
case p00: (p`_0 == 0); first by rewrite (eqP p00) modp0 gcdp0 size_poly1.
by rewrite modpC ?p00 // gcd0p size_polyC p00.
Qed.

Lemma size_gcdp1 p : size (gcdp p 1) = 1%N.
rewrite gcdpE size_polyC oner_eq0 /= modp1; case: ltnP; last first.
  by rewrite gcd0p size_polyC oner_eq0.
rewrite ltnS leqn0 size_poly_eq0; move/eqP->; rewrite gcdp0 modp0 size_polyC.
by rewrite oner_eq0.
Qed.

Lemma gcdpp : idempotent gcdp.
Proof. by move=> p; rewrite gcdpE ltnn modpp gcd0p. Qed.

Lemma dvdp_gcdlr p q : (gcdp p q %| p) && (gcdp p q %| q).
Proof.
elim: {p q}minn {-2}p {-2}q (leqnn (minn (size q) (size p))) => [|r Hrec] p q.
  rewrite leq_minl !leqn0 !size_poly_eq0.
  by case/pred2P=> ->; rewrite (gcdp0, gcd0p) dvdpp ?andbT /=.
case: (eqVneq p 0) => [-> _|nz_p]; first by rewrite gcd0p dvdpp andbT.
case: (eqVneq q 0) => [->|nz_q]; first by rewrite gcdp0 dvdpp /=.
rewrite gcdpE minnC /minn; case: ltnP => [lt_pq | le_pq] le_qr.
  suffices: minn (size p) (size (q %% p)) <= r.
    by move/Hrec; case/andP => E1 E2; rewrite E2 (dvdp_mod _ E2).
  by rewrite leq_minl orbC -ltnS (leq_trans _ le_qr) ?ltn_modp.
suffices: minn (size q) (size (p %% q)) <= r.
  by move/Hrec; case/andP => E1 E2; rewrite E2 andbT (dvdp_mod _ E2).
by rewrite leq_minl orbC -ltnS (leq_trans _ le_qr) ?ltn_modp.
Qed.

Lemma dvdp_gcdl p q : gcdp p q %| p.
Proof. by case/andP: (dvdp_gcdlr p q). Qed.

Lemma dvdp_gcdr p q :gcdp p q %| q.
Proof. by case/andP: (dvdp_gcdlr p q). Qed.

Lemma leq_gcdpl p q : p != 0 -> size (gcdp p q) <= size p.
Proof. by move=> pn0; move: (dvdp_gcdl p q); apply: dvdp_leq. Qed.

Lemma leq_gcdpr p q : q != 0 -> size (gcdp p q) <= size q.
Proof. by move=> qn0; move: (dvdp_gcdr p q); apply: dvdp_leq. Qed.

Lemma dvdp_gcd p m n : p %| gcdp m n = (p %| m) && (p %| n).
Proof.
apply/idP/andP=> [dv_pmn | [dv_pm dv_pn]].
  by rewrite ?(dvdp_trans dv_pmn) ?dvdp_gcdl ?dvdp_gcdr.
move: (leqnn (minn (size n) (size m))) dv_pm dv_pn.
elim: {m n}minn {-2}m {-2}n => [|r Hrec] m n.
  rewrite leq_minl !leqn0 !size_poly_eq0.
  by case/pred2P=> ->; rewrite (gcdp0, gcd0p).
case: (eqVneq m 0) => [-> _|nz_m]; first by rewrite gcd0p /=.
case: (eqVneq n 0) => [->|nz_n]; first by rewrite gcdp0 /=.
rewrite gcdpE minnC /minn; case: ltnP => Cnm le_r dv_m dv_n.
  apply: Hrec => //; last by rewrite -(dvdp_mod _ dv_m).
  by rewrite leq_minl orbC -ltnS (leq_trans _ le_r) ?ltn_modp.
apply: Hrec => //; last by rewrite -(dvdp_mod _ dv_n).
by rewrite leq_minl orbC -ltnS (leq_trans _ le_r) ?ltn_modp.
Qed.


Lemma gcdpC : forall p q, gcdp p q %= gcdp q p.
Proof. by move=> p q; rewrite /eqp !dvdp_gcd !dvdp_gcdl !dvdp_gcdr. Qed.

Lemma gcd1p p : gcdp 1 p %= 1.
Proof.
rewrite -size_poly_eq1 gcdpE size_poly1; case: ltnP.
  by rewrite modp1 gcd0p size_poly1 eqxx.
move/size1_polyC=> e; rewrite e.
case p00: (p`_0 == 0); first by rewrite (eqP p00) modp0 gcdp0 size_poly1.
by rewrite modpC ?p00 // gcd0p size_polyC p00.
Qed.

Lemma gcdp1 p : gcdp p 1 %= 1.
Proof. by rewrite (eqp_ltrans (gcdpC _ _)) gcd1p. Qed.

Lemma gcdp_addl_mul p q r: gcdp r (p * r + q) %= gcdp r q.
Proof.
suff h m n d : gcdp d n %| gcdp d (m * d + n).
  apply/andP; split => //; rewrite {2}(_: q = (-p) * r + (p * r + q)) ?H //.
  by rewrite GRing.mulNr GRing.addKr.
by rewrite dvdp_gcd dvdp_gcdl /= dvdp_addr ?dvdp_gcdr ?dvdp_mull ?dvdp_gcdl.
Qed.

Lemma gcdp_addl m n : gcdp m (m + n) %= gcdp m n.
Proof. by rewrite -{2}(mul1r m) gcdp_addl_mul. Qed.

Lemma gcdp_addr m n : gcdp m (n + m) %= gcdp m n.
Proof. by rewrite addrC gcdp_addl. Qed.

Lemma gcdp_mull m n : gcdp n (m * n) %= n.
Proof.
case: (eqVneq n 0) => [-> | nn0]; first by rewrite gcd0p mulr0 eqpxx.
case: (eqVneq m 0) => [-> | mn0]; first by rewrite mul0r gcdp0 eqpxx.
rewrite gcdpE modp_mull gcd0p size_mul_id //; case: ifP; first by rewrite eqpxx.
rewrite  (polySpred mn0) addSn /= -{1}[size n]add0n ltn_add2r; move/negbT.
rewrite -ltnNge prednK ?size_poly_neq0 // leq_eqVlt ltnS leqn0 size_poly_eq0.
rewrite (negPf mn0) orbF; case/size1P=> c cn0 -> {mn0 m}; rewrite mul_polyC.
suff -> : n %% (c *: n) = 0 by rewrite gcd0p; exact: scale_eqp.
by apply/modp_eq0P; rewrite dvdp_scalel.
Qed.

Lemma gcdp_mulr m n : gcdp n (n * m) %= n.
Proof. by rewrite mulrC gcdp_mull. Qed.

Lemma gcdp_scalel c m n : c != 0 -> gcdp (c *: m) n %= gcdp m n.
Proof.
move=> cn0; rewrite /eqp dvdp_gcd [gcdp m n %| _]dvdp_gcd !dvdp_gcdr !andbT. 
apply/andP; split; last first. 
  by apply: dvdp_trans (dvdp_gcdl _ _) _; rewrite dvdp_scaler.
by apply: dvdp_trans (dvdp_gcdl _ _) _; rewrite dvdp_scalel.
Qed.

Lemma gcdp_scaler c m n : c != 0 -> gcdp m (c *: n) %= gcdp m n.
Proof.
move=> cn0; apply: eqp_trans (gcdpC _ _) _.
apply: eqp_trans (gcdp_scalel _ _ _) _ => //; exact: gcdpC.
Qed.

Lemma dvdp_gcd_idl m n : m %| n -> gcdp m n %= m.
Proof. 
case: (eqVneq m 0) => [-> | mn0].
  by rewrite dvd0p => /eqP ->; rewrite gcdp0 eqpxx.
rewrite dvdp_eq; move/eqP; move/(f_equal (gcdp m)) => h.
apply: eqp_trans (gcdp_mull (n %/ m) _); rewrite -h eqp_sym gcdp_scaler //.
by rewrite expf_neq0 // lead_coef_eq0.
Qed.

Lemma dvdp_gcd_idr m n : n %| m -> gcdp m n %= n.
Proof. move/dvdp_gcd_idl => h; apply: eqp_trans h; exact: gcdpC. Qed.

Lemma gcdp_exp p k l : gcdp (p ^+ k) (p ^+ l) %= p ^+ minn k l.
Proof.
wlog leqmn: k l / k <= l.
  move=> hwlog; case: (leqP k l); first exact: hwlog.
  move/ltnW; rewrite minnC; move/hwlog=> h; apply: eqp_trans h; exact: gcdpC.
rewrite (minnl leqmn); move/subnK: leqmn<-; rewrite exprn_addr. 
apply: eqp_trans (gcdp_mull _ _) _; exact: eqpxx.
Qed.

Lemma gcdp_eq0 p q : gcdp p q == 0 = (p == 0) && (q == 0).
Proof.
apply/idP/idP; last by case/andP => /eqP -> /eqP ->; rewrite gcdp0.
have h m n: gcdp m n == 0 -> (m == 0).
  by rewrite -(dvd0p m); move/eqP<-; rewrite dvdp_gcdl.
by move=> ?; rewrite (h _ q) // (h _ p) // -eqp0 (eqp_ltrans (gcdpC _ _)) eqp0.
Qed.

Lemma eqp_gcdr p q r : q %= r -> gcdp p q %= gcdp p r.
Proof.
move=> eqr; rewrite /eqp !(dvdp_gcd, dvdp_gcdl, andbT) /=.
by rewrite -(eqp_dvdr _ eqr) dvdp_gcdr (eqp_dvdr _ eqr) dvdp_gcdr.
Qed.

Lemma eqp_gcdl r p q :  p %= q -> gcdp p r %= gcdp q r.
move=> eqr; rewrite /eqp !(dvdp_gcd, dvdp_gcdr, andbT) /=.
by rewrite -(eqp_dvdr _ eqr) dvdp_gcdl (eqp_dvdr _ eqr) dvdp_gcdl.
Qed.

Lemma eqp_gcd p1 p2 q1 q2 : p1 %= p2 -> q1 %= q2 -> gcdp p1 q1 %= gcdp p2 q2.
Proof.
move=> e1 e2. 
by apply: eqp_trans (eqp_gcdr _ e2); apply: eqp_trans (eqp_gcdl _ e1).
Qed.

Lemma eqp_rgcdp_gcdp p q : rgcdp p q %= gcdp p q.
Proof.
move: (leqnn (minn (size p) (size q))); move: {2}(minn (size p) (size q)) => n.
elim: n p q => [p q|n ihn p q hs].
  rewrite leqn0 /minn; case: ltnP => _; rewrite size_poly_eq0; move/eqP->.
    by rewrite gcd0p rgcd0p eqpxx.
  by rewrite gcdp0 rgcdp0 eqpxx.
case: (eqVneq p 0) => [-> | pn0]; first by rewrite gcd0p rgcd0p eqpxx.
case: (eqVneq q 0) => [-> | qn0]; first by rewrite gcdp0 rgcdp0 eqpxx.
rewrite gcdpE rgcdpE; case: ltnP => sp.
  have e := (eqp_rmodp_modp q p); move: (e); move/(eqp_gcdl p) => h.
  apply: eqp_trans h; apply: ihn; rewrite (size_eqp e) minnl; last first. 
    by rewrite ltnW ?ltn_modp.
  rewrite -ltnS; apply: leq_trans hs; rewrite minnl ?ltn_modp //; exact: ltnW.
  have e := (eqp_rmodp_modp p q); move: (e); move/(eqp_gcdl q) => h.
  apply: eqp_trans h; apply: ihn; rewrite (size_eqp e); rewrite -ltnS.
  apply: leq_trans hs; rewrite minnl; last by rewrite ltnW ?ltn_modp.
  by rewrite minnr // ltn_modp.
Qed.

Lemma gcdp_modr m n : gcdp m (n %% m) %= gcdp m n.
Proof.
case: (eqVneq m 0) => [-> | mn0]; first by rewrite modp0 eqpxx.
have : (lead_coef m) ^+ (scalp n m) != 0 by rewrite expf_neq0 // lead_coef_eq0.
move/gcdp_scaler; move/(_ m n) => h; apply: eqp_trans h; rewrite divp_eq.
by rewrite eqp_sym gcdp_addl_mul.
Qed.

Lemma gcdp_modl m n : gcdp (m %% n) n %= gcdp m n.
Proof.
apply: eqp_trans (gcdpC _ _) _; apply: eqp_trans (gcdp_modr _ _) _; exact: gcdpC.
Qed.

Lemma gcdp_def d m n :
    d %| m -> d %| n -> (forall d', d' %| m -> d' %| n -> d' %| d) ->
  gcdp m n %= d.
Proof.
move=> dm dn h; rewrite /eqp dvdp_gcd dm dn !andbT. 
apply: h; [exact: dvdp_gcdl | exact: dvdp_gcdr].
Qed.

Definition coprimep p q := size (gcdp p q) == 1%N.

Lemma coprimep_def p q : (coprimep p q) = (size (gcdp p q) == 1%N).
Proof. done. Qed.

Lemma gcdp_eqp1 p q : gcdp p q %= 1 = (coprimep p q).
Proof. by rewrite coprimep_def size_poly_eq1. Qed.

Lemma coprimep_sym p q : coprimep p q = coprimep q p.
Proof.
by rewrite -!gcdp_eqp1; apply: eqp_ltrans; rewrite gcdpC.
Qed.

Lemma coprime1p p : coprimep 1 p.
Proof.
rewrite /coprimep -[1%N](size_poly1 R); apply/eqP; apply: size_eqp; exact: gcd1p.
Qed.

Lemma coprimep1 p : coprimep p 1.
Proof. by rewrite coprimep_sym; apply: coprime1p. Qed.


Lemma coprimep0 p : coprimep p 0 = (p %= 1).
Proof. by rewrite /coprimep gcdp0 size_poly_eq1. Qed.

Lemma coprime0p p : coprimep 0 p = (p %= 1).
Proof. by rewrite coprimep_sym coprimep0. Qed.

(* This is different from coprimeP in div. shall we keep this? *)
Lemma coprimepP p q :
 reflect (forall d, d %| p -> d %| q -> d %= 1) (coprimep p q).
Proof.
apply: (iffP idP)=> [|h].
  rewrite /coprimep; move/eqP=> hs d dvddp dvddq.
  have dvddg: d %| gcdp p q by rewrite dvdp_gcd dvddp dvddq.
  by apply: (dvdp_eqp1 dvddg); rewrite -size_poly_eq1; apply/eqP.
by case/andP: (dvdp_gcdlr p q)=> h1 h2; rewrite /coprimep size_poly_eq1; apply: h.
Qed.

Lemma coprimepPn p q : p != 0 ->
  reflect (exists d, (d %| gcdp p q) && ~~(d %= 1))  (~~ coprimep p q).
Proof.
move=> p0; apply: (iffP idP).
  by rewrite -gcdp_eqp1=> ng1; exists (gcdp p q); rewrite dvdpp /=.
case=> d; case/andP=> dg; apply: contra; rewrite -gcdp_eqp1=> g1.
by move: dg; rewrite (eqp_dvdr _ g1) dvdp1 size_poly_eq1.
Qed.

Lemma coprimep_dvdl q p r : r %| q -> coprimep p q -> coprimep p r.
Proof.
move=> rq cpq; apply/coprimepP=> d dp dr; move/coprimepP:cpq=> cpq'.
by apply: cpq'; rewrite // (dvdp_trans dr).
Qed.

Lemma coprimep_dvdr  p q r :
  r %| p -> coprimep p q -> coprimep r q.
Proof.
move=> rp; rewrite ![coprimep _ q]coprimep_sym.
by move/coprimep_dvdl; apply.
Qed.


Lemma coprimep_modl p q : coprimep (p %% q) q = coprimep p q.
Proof.
symmetry; rewrite !coprimep_def.
case: (ltnP (size p) (size q))=> hpq; first by rewrite modp_small.
by rewrite gcdpE ltnNge hpq.
Qed.

Lemma coprimep_modr q p :
  coprimep q (p %% q) = coprimep q p.
Proof. by rewrite ![coprimep q _]coprimep_sym coprimep_modl. Qed.

Lemma rcoprimep_coprimep  q p : rcoprimep q p = coprimep q p.
Proof.
by rewrite /coprimep /rcoprimep; rewrite (size_eqp (eqp_rgcdp_gcdp _ _)).
Qed.

Lemma eqp_coprimepr p q r : q %= r -> coprimep p q = coprimep p r.
Proof. 
by rewrite -!gcdp_eqp1; move/(eqp_gcdr p) => h1; apply: (eqp_ltrans h1).
Qed.

Lemma eqp_coprimepl p q r : q %= r -> coprimep q p = coprimep r p.
Proof. rewrite !(coprimep_sym _ p); exact: eqp_coprimepr. Qed.

(* This should be implemented with an extended remainder sequence *)
Fixpoint egcdp_rec p q k {struct k} : {poly R} * {poly R} :=
  if k is k'.+1 then
    if q == 0 then (1, 0) else
    let: (u, v) := egcdp_rec q (p %% q) k' in
      (lead_coef q ^+ scalp p q *: v, (u - v * (p %/ q)))
  else (1, 0).
 
Definition egcdp p q :=
  if size q <= size p then egcdp_rec p q (size q)
    else let e :=  egcdp_rec q p (size p) in (e.2, e.1).


(* No provable egcd0p *)
Lemma egcdp0 p : egcdp p 0 = (1, 0).
Proof. by rewrite /egcdp size_poly0. Qed.


Lemma egcdp_recP : forall k p q, q != 0 -> size q <= k -> size q <= size p -> 
  let e := (egcdp_rec p q k) in 
    [/\ size e.1 <= size q, size e.2 <= size p & gcdp p q %= e.1 * p + e.2 * q].
Proof.
elim=> [|k ihk] p q /= qn0; first by rewrite leqn0 size_poly_eq0 (negPf qn0).
move=> sqSn qsp; case: (eqVneq q 0)=> q0; first by rewrite q0 eqxx in qn0.
rewrite (negPf qn0).
have sp : size p > 0 by apply: leq_trans qsp; rewrite  size_poly_neq0.
case: (eqVneq (p %% q) 0) => [r0 | rn0] /=.
  rewrite r0 /egcdp_rec; case: k ihk sqSn => [|n] ihn sqSn /=.
    rewrite !scaler0 !mul0r subr0 add0r mul1r size_poly0 size_poly1.
    by rewrite dvdp_gcd_idr /dvdp ?r0.
  rewrite !eqxx mul0r scaler0 /= mul0r add0r subr0 mul1r size_poly0 size_poly1.
  by rewrite dvdp_gcd_idr /dvdp ?r0 //.
have h1 : size (p %% q) <= k.
  by rewrite -ltnS; apply: leq_trans sqSn; rewrite ltn_modp.
have h2 : size (p %% q) <= size q by rewrite ltnW // ltn_modp.
have := (ihk q (p %% q) rn0 h1 h2). 
case: (egcdp_rec _ _)=> u v /= => [[ihn'1 ihn'2 ihn'3]].
rewrite gcdpE ltnNge qsp //= (eqp_ltrans (gcdpC _ _)); split; last first.
- apply: (eqp_trans ihn'3).
  rewrite mulr_subl addrCA -scaler_mull scaler_mulr -mulrA -mulr_subr.
  by rewrite divp_eq addrAC subrr add0r eqpxx.
- apply: (leq_trans (size_add _ _)).
  case: (eqVneq v 0)=> [-> | vn0].
    rewrite mul0r size_opp size_poly0 maxn0; apply: leq_trans ihn'1 _.
    exact: leq_modp.
  case: (eqVneq (p %/ q) 0)=> [-> | qqn0].
    rewrite mulr0 size_opp size_poly0 maxn0;  apply: leq_trans ihn'1 _.
    exact: leq_modp.
  rewrite leq_maxl (leq_trans ihn'1) ?leq_modp //= size_opp size_mul_id //.
  move: (ihn'2); rewrite -(leq_add2r (size (p %/ q))).
  have : size v + size (p %/ q) > 0 by rewrite addn_gt0 size_poly_neq0 vn0.
  have : size q + size (p %/ q) > 0 by rewrite addn_gt0 size_poly_neq0 qn0.
  do 2! move/prednK=> {1}<-; rewrite ltnS => h; apply: leq_trans h _.
  rewrite size_divp // addn_subA; last by apply: leq_trans qsp; exact: leq_pred. 
  rewrite addnC -addn_subA ?leq_pred //; move: qn0; rewrite -size_poly_eq0 -lt0n.
  by move/prednK=> {1}<-; rewrite subSnn addn1.
- by rewrite size_scaler // lc_expn_scalp_neq0.
Qed.


Lemma egcdpP p q : p != 0 ->  q != 0 -> forall (e := egcdp p q),
  [/\ size e.1 <= size q, size e.2 <= size p & gcdp p q %= e.1 * p + e.2 * q].
Proof.
move=> pn0 qn0; rewrite /egcdp; case: (leqP (size q) (size p)) => /= hp.
  by apply: egcdp_recP.
move/ltnW: hp => hp; case: (egcdp_recP pn0 (leqnn (size p)) hp) => h1 h2 h3.
by split => //; rewrite (eqp_ltrans (gcdpC _ _)) addrC.
Qed.

Lemma egcdpE p q: forall (e := egcdp p q), (gcdp p q %= e.1 * p + e.2 * q : Prop).
Proof.
case: (eqVneq q 0)=> [-> | qn0] /=.
   by rewrite gcdp0 egcdp0 mul1r mulr0 addr0.
case: (eqVneq p 0)=> [p0 | pn0] /=; last by case: (egcdpP pn0 qn0).
rewrite p0 gcd0p mulr0 add0r /egcdp size_poly0 leqn0 size_poly_eq0 (negPf qn0).
by rewrite /= mul1r.
Qed.

Lemma bezoutp p q : exists u, u.1 * p + u.2 * q %= (gcdp p q).
Proof.
case: (eqVneq p 0) => [-> | pn0].
  by rewrite gcd0p; exists (0, 1); rewrite mul0r mul1r add0r.
case: (eqVneq q 0) => [-> | qn0].
  by rewrite gcdp0; exists (1, 0); rewrite mul0r mul1r addr0.
pose e := egcdp p q; exists e; rewrite eqp_sym.
by case: (egcdpP pn0 qn0).
Qed.

Lemma bezout_coprimepP : forall p q,
  reflect (exists u, u.1 * p + u.2 * q %= 1) (coprimep p q).
Proof.
move=> p q; rewrite -gcdp_eqp1; apply:(iffP idP)=> [g1|].
  case: (bezoutp p q) => [[u v] Puv]; exists (u, v); exact: eqp_trans g1.
case=>[[u v]]; rewrite eqp_sym=> Puv; rewrite /eqp  (eqp_dvdr _ Puv).
by rewrite  dvdp_addr dvdp_mull ?dvdp_gcdl ?dvdp_gcdr //= dvd1p.
Qed.

Lemma coprimep_root p q x : coprimep p q -> root p x -> q.[x] != 0.
Proof.
case/bezout_coprimepP=> [[u v] euv] px0. 
move/eqpP: euv => [c1 [c2 [c1n0 c2n0 e]]].
suff: c1 * (v.[x] * q.[x]) != 0 by rewrite !mulf_eq0 !negb_or c1n0 /=; case/andP.
move/(f_equal (fun t => horner t x)): e; rewrite /= !horner_scaler horner_add.
by rewrite !horner_mul (eqP px0) mulr0 add0r hornerC mulr1; move->.
Qed.

Lemma gausspl p q d: coprimep d q -> (d %| p * q) = (d %| p).
Proof.
move/bezout_coprimepP=>[[u v] Puv]; apply/idP/idP; last exact: dvdp_mulr.
move:Puv; move/(eqp_mull p); rewrite mulr1 mulr_addr eqp_sym=> peq dpq.
rewrite (eqp_dvdr _  peq) dvdp_addr; first by rewrite mulrA mulrAC dvdp_mulr.
by rewrite mulrA dvdp_mull ?dvdpp.
Qed.

Lemma gausspr p q d: coprimep d q -> (d %| q * p) = (d %| p).
Proof. rewrite mulrC; exact: gausspl. Qed.

(* This could be simplified with the introduction of lcmp *)
Lemma gaussp_inv m n p : coprimep m n -> (m * n %| p) = (m %| p) && (n %| p).
Proof.
case: (eqVneq m 0) => [-> | mn0].
  by rewrite coprime0p;  move/eqp_dvdl->; rewrite !mul0r dvd0p dvd1p andbT.
case: (eqVneq n 0) => [-> | nn0].
  by rewrite coprimep0; move/eqp_dvdl->; rewrite !mulr0 dvd1p.
move=> hc; apply/idP/idP.
  move/gausspl: hc<-;  move=> h; move/(dvdp_mull m): (h); rewrite dvdp_mul2l //.
  move->; move/(dvdp_mulr n): (h); rewrite dvdp_mul2r // andbT; exact: dvdp_mulr.
case/andP => dmp dnp; move: (dnp); rewrite dvdp_eq. 
set c2 := _ ^+ _; set q2 := _ %/ _; move/eqP=> e2.
have := (sym_eq (gausspl q2 hc)); rewrite -e2.
have -> : m %| c2 *: p by rewrite -mul_polyC dvdp_mull.
rewrite dvdp_eq;  set c3 := _ ^+ _; set q3 := _ %/ _; move/eqP=> e3.
apply: (@eq_dvdp (c3 * c2) q3).
  by rewrite mulf_neq0 // expf_neq0 // lead_coef_eq0.
by rewrite mulrA -e3 -scaler_mull -e2 scalerA.
Qed.

Lemma gaussp_gcdr p m n : coprimep p m -> gcdp p (m * n) %= gcdp p n.
Proof.
move=> co_pm; apply/eqP; rewrite /eqp !dvdp_gcd !dvdp_gcdl /= andbC.
rewrite dvdp_mull ?dvdp_gcdr // -(@gausspl _ m); first by rewrite mulrC dvdp_gcdr.
apply/coprimepP=> d; rewrite dvdp_gcd; case/andP=> hdp _ hdm. 
by move/coprimepP: co_pm; apply.
Qed.

Lemma gaussp_gcdl p m n : coprimep p n -> gcdp p (m * n) %= gcdp p m.
Proof. by move=> co_pn; rewrite mulrC gaussp_gcdr. Qed.

Lemma coprimep_mulr p q r : coprimep p (q * r) = (coprimep p q && coprimep p r).
Proof.
apply/coprimepP/andP=> [hp|[/coprimepP hq hr]].
  split; apply/coprimepP=> d dp dq; rewrite hp //;
 [exact: dvdp_mulr|exact: dvdp_mull].
move=> d dp dqr; move/(_ _ dp) in hq.
rewrite gausspl in dqr; first exact: hq.
by move/coprimep_dvdr:hr; apply.
Qed.

Lemma coprimep_mull q r p:
  coprimep (q * r) p = (coprimep q p && coprimep r p).
Proof. by rewrite ![coprimep _ p]coprimep_sym coprimep_mulr. Qed.


Lemma modp_coprime k u n : k != 0 -> (k * u) %% n %= 1 -> coprimep k n.
Proof.
move=> kn0 hmod; apply/bezout_coprimepP.
exists (((lead_coef n)^+(scalp (k * u) n) *: u), (- (k * u %/ n))).
rewrite -scaler_mull mulrC (divp_eq (u * k) n) mulNr -addrAC subrr add0r.
by rewrite mulrC.
Qed.

Lemma coprimep_pexpl k m n : 0 < k -> coprimep (m ^+ k) n = coprimep m n.
Proof.
case: k => // k _; elim: k => [|k IHk]; first by rewrite expr1.
by rewrite exprS coprimep_mull -IHk andbb.
Qed.

Lemma coprimep_pexpr k m n : 0 < k -> coprimep m (n ^+ k) = coprimep m n.
Proof. by move=> k_gt0; rewrite !(coprimep_sym m) coprimep_pexpl. Qed.

Lemma coprimep_expl k m n : coprimep m n -> coprimep (m ^+ k) n.
Proof. by case: k => [|k] co_pm; rewrite ?coprime1p // coprimep_pexpl. Qed.

Lemma coprimep_expr k m n : coprimep m n -> coprimep m (n ^+ k).
Proof. by rewrite !(coprimep_sym m); exact: coprimep_expl. Qed.

Lemma gcdp_mul2l p q r : gcdp (p * q) (p * r) %= (p * gcdp q r).
Proof.
case: (eqVneq p 0)=> [->|hp]; first by rewrite !mul0r gcdp0 eqpxx.
rewrite /eqp !dvdp_gcd !dvdp_mul2l // dvdp_gcdr dvdp_gcdl !andbT.
move: (bezoutp q r) => [[u v]] huv.
rewrite eqp_sym in huv; rewrite (eqp_dvdr _ (eqp_mull _ huv)).
rewrite mulr_addr ![p * (_ * _)]mulrCA.
by apply: dvdp_add; rewrite dvdp_mull// (dvdp_gcdr, dvdp_gcdl).
Qed.

Lemma gcdp_mul2r q r p : gcdp (q * p) (r * p) %= (gcdp q r * p).
Proof. by rewrite ![_ * p]GRing.mulrC gcdp_mul2l. Qed.

Lemma mulp_gcdr p q r : r * (gcdp p q) %= gcdp (r * p) (r * q).
Proof. by rewrite eqp_sym gcdp_mul2l. Qed.

Lemma mulp_gcdl p q r : (gcdp p q) * r %= gcdp (p * r) (q * r).
Proof. by  rewrite eqp_sym gcdp_mul2r. Qed.

Lemma coprimep_div_gcd p q : (p != 0) || (q != 0) ->
  coprimep (p %/ (gcdp p q)) (q %/ gcdp p q).
Proof.
move=> hpq.
have gpq0: gcdp p q != 0 by rewrite gcdp_eq0 negb_and.
rewrite -gcdp_eqp1 -(@eqp_mul2r (gcdp p q)) // mul1r.
have: gcdp p q %| p by rewrite dvdp_gcdl.
have: gcdp p q %| q by rewrite dvdp_gcdr.
rewrite !dvdp_eq eq_sym; move/eqP=> hq; rewrite eq_sym; move/eqP=> hp.
rewrite (eqp_ltrans (mulp_gcdl _ _ _)) hq hp.
have lcn0 k : (lead_coef (gcdp p q)) ^+ k != 0. 
  by rewrite expf_neq0 ?lead_coef_eq0.
by apply: eqp_gcd; rewrite ?scale_eqp.
Qed.

Lemma divp_eq0 p q : (p %/ q == 0) = [|| p == 0, q ==0 | size p < size q].
Proof.
apply/eqP/idP=> [d0|]; last first.
  case/or3P; [by move/eqP->; rewrite div0p| by move/eqP->; rewrite divp0|].
  by move/divp_small.
case: (eqVneq p 0) => [->|pn0]; first by rewrite eqxx.
case: (eqVneq q 0) => [-> | qn0]; first by rewrite eqxx orbT.
move: (divp_eq p q); rewrite d0 mul0r add0r.
move/(f_equal (fun x : {poly R} => size x)).
by rewrite size_scaler ?lc_expn_scalp_neq0 //; move->; rewrite ltn_modp qn0 !orbT.
Qed.

Lemma bezout_coprimepPn p q : p != 0 -> q != 0 ->
  reflect (exists uv : {poly R} * {poly R},
    [&& (0 < size uv.1 < size q),
    (0 < size uv.2 < size p) &
    uv.1 * p == uv.2 * q])
  (~~ (coprimep p q)).
move=> pn0 qn0; apply: (iffP idP); last first.
  case=> [[u v] /= /and3P [/andP [ps1 s1] /andP [ps2 s2]] e].
  have: ~~(size (q * p) <= size (u * p)).
    rewrite -ltnNge !size_mul_id // -?size_poly_neq0 // (polySpred pn0) !addnS.
    by rewrite ltn_add2r.
  apply: contra => ?; apply: dvdp_leq; rewrite ?mulf_neq0 // -?size_poly_neq0 //.
  by rewrite mulrC gaussp_inv // dvdp_mull // (eqP e) dvdp_mull.
rewrite coprimep_def neq_ltn.
case/orP; first by rewrite ltnS leqn0 size_poly_eq0 gcdp_eq0 -[p == 0]negbK pn0.
case sg: (size (gcdp p q)) => [|n] //; case: n sg=> [|n] // sg _.
move: (dvdp_gcdl p q); rewrite dvdp_eq; set c1 := _ ^+ _; move/eqP=> hu1. 
move: (dvdp_gcdr p q); rewrite dvdp_eq; set c2 := _ ^+ _; move/eqP=> hv1. 
exists (c1 *: (q %/ gcdp p q), c2 *: (p %/ gcdp p q)). 
rewrite !{1}size_scaler ?lc_expn_scalp_neq0 //= -!{1}scaler_mull !scaler_mulr.
rewrite hu1 hv1 mulrCA !size_poly_neq0 !divp_eq0 gcdp_eq0 !(negPf pn0).
rewrite !(negPf qn0) /= -!leqNgt leq_gcdpl // leq_gcdpr //=.
rewrite !ltn_divpl -?size_poly_eq0 ?sg // !size_mul_id // -?size_poly_eq0 ?sg //.
rewrite ![(_ + n.+2)%N]addnS /= -{1}(addn0 (size p)) -{1}(addn0 (size q)).
by rewrite !ltn_add2l !eqxx.
Qed.

Lemma dvdp_pexp2r m n k : k > 0 -> (m ^+ k %| n ^+ k) = (m %| n).
Proof.
move=> k_gt0; apply/idP/idP; last exact: dvdp_exp2r.
case: (eqVneq n 0) => [-> | nn0] //; case: (eqVneq m 0) => [-> | mn0].
  move/prednK: k_gt0=> {1}<-; rewrite exprS mul0r //= !dvd0p expf_eq0.
  by case/andP=> _ ->.
set d := gcdp m n; have := (dvdp_gcdr m n); rewrite -/d dvdp_eq.
set c1 := _ ^+ _; set n' := _ %/ _; move/eqP=> def_n.
have := (dvdp_gcdl m n); rewrite -/d dvdp_eq.
set c2 := _ ^+ _; set m' := _ %/ _; move/eqP=> def_m.
have dn0 : d != 0 by rewrite gcdp_eq0 negb_and nn0 orbT.
have c1n0 : c1 != 0 by rewrite !expf_neq0 // lead_coef_eq0.
have c2n0 : c2 != 0 by rewrite !expf_neq0 // lead_coef_eq0.
rewrite -(@dvdp_scaler (c1 ^+ k)) ?expf_neq0 ?lead_coef_eq0 //.
have c2k_n0 : c2 ^+ k != 0 by rewrite !expf_neq0 // lead_coef_eq0.
rewrite -(@dvdp_scalel (c2 ^+k)) // -!scaler_exp def_m def_n !exprn_mull.
rewrite dvdp_mul2r ?expf_neq0 //.
have: coprimep (m' ^+ k) (n' ^+ k).
  rewrite coprimep_pexpl // coprimep_pexpr //; apply: coprimep_div_gcd.
  by rewrite nn0 orbT.
move/coprimepP=> hc hd.
have /size1P [c cn0 em'] : size m' == 1%N.
  case: (eqVneq m' 0)=> [m'0 |m'_n0].
    move: def_m; rewrite m'0 mul0r; move/eqP; rewrite scale_poly_eq0 (negPf mn0).
    by rewrite (negPf c2n0).
  have := (hc _ (dvdpp _) hd); rewrite -size_poly_eq1.
  rewrite polySpred; last by rewrite expf_eq0 negb_and m'_n0 orbT.
  rewrite size_exp_id eqSS muln_eq0;  move: k_gt0; rewrite lt0n; move/negPf->.
  by rewrite orbF -{2}(@prednK (size m')) ?lt0n // size_poly_eq0.
rewrite -(@dvdp_scalel c2) // def_m em' mul_polyC dvdp_scalel //.
by rewrite -(@dvdp_scaler c1) // def_n dvdp_mull.
Qed.

Lemma root_gcd p q x : root (gcdp p q) x = root p x && root q x.
Proof.
rewrite /= !root_factor_theorem; apply/idP/andP=> [dg| [dp dq]].
  by split; apply: dvdp_trans dg _; rewrite ?(dvdp_gcdl, dvdp_gcdr).
have:= (bezoutp p q)=> [[[u v]]]; rewrite eqp_sym=> e.
by rewrite (eqp_dvdr _ e) dvdp_addl dvdp_mull.
Qed.

Lemma root_biggcd : forall x (ps : seq {poly R}),
  root (\big[gcdp/0]_(p <- ps) p) x = all (fun p => root p x) ps.
Proof.
move=> x; elim; first by rewrite big_nil root0.
by move=> p ps ihp; rewrite big_cons /= root_gcd ihp.
Qed.

(* "gdcop Q P" is the Greatest Divisor of P which is coprime to Q *)
(* if P null, we pose that gdcop returns 1 if Q null, 0 otherwise*)
Fixpoint gdcop_rec q p k :=
  if k is m.+1 then
      if coprimep p q then p
        else gdcop_rec q (divp p (gcdp p q)) m
    else (q == 0)%:R.

Definition gdcop q p := gdcop_rec q p (size p).

CoInductive gdcop_spec q p : {poly R} -> Type :=
  GdcopSpec r of (dvdp r p) & ((coprimep r q) || (p == 0))
  & (forall d,  dvdp d p -> coprimep d q -> dvdp d r)
  : gdcop_spec q p r.

Lemma gdcop0 q : gdcop q 0 = (q == 0)%:R.
Proof. by  rewrite /gdcop size_poly0. Qed.

Lemma gdcop_recP : forall q p k,
  size p <= k -> gdcop_spec q p (gdcop_rec q p k).
Proof.
move=> q p k; elim: k p => [p | k ihk p] /=.
  rewrite leqn0 size_poly_eq0; move/eqP->.
  case q0: (_ == _); split; rewrite ?coprime1p // ?eqxx ?orbT //.
  by move=> d _; rewrite (eqP q0) coprimep0 dvdp1 size_poly_eq1.
move=> hs; case cop : (coprimep _ _); first by split; rewrite ?dvdpp ?cop.
case (eqVneq p 0) => [-> | p0].
  by rewrite div0p; apply: ihk; rewrite size_poly0 leq0n.
case: (eqVneq q 0) => [-> | q0].
  rewrite gcdp0 divpp ?p0 //= => {hs ihk}; case: k=> /=.
    rewrite eqxx; split; rewrite ?dvd1p ?coprimep0 ?eqpxx //=.
    by move=> d _; rewrite coprimep0 dvdp1 size_poly_eq1.
  move=> n; rewrite coprimep0 polyC_eqp1 //; rewrite lc_expn_scalp_neq0.
  split; first by rewrite (@eqp_dvdl 1) ?dvd1p ?polyC_eqp1.
    by rewrite coprimep0 polyC_eqp1 // ?lc_expn_scalp_neq0.
  by move=> d _; rewrite coprimep0; move/eqp_dvdl->; rewrite dvd1p.
move: (dvdp_gcdl p q); rewrite dvdp_eq; move/eqP=> e.
have sgp : size (gcdp p q) <= size p.
  by apply: dvdp_leq; rewrite ?gcdp_eq0 ?p0 ?q0 // dvdp_gcdl.
have : p %/ gcdp p q != 0; last move/negPf=>p'n0. 
  move: (dvdp_mulIl (p %/ gcdp p q) (gcdp p q)); move/dvdpN0; apply; rewrite -e.
  by rewrite scale_poly_eq0 negb_or lc_expn_scalp_neq0.
have gn0 : gcdp p q != 0.
  move: (dvdp_mulIr (p %/ gcdp p q) (gcdp p q)); move/dvdpN0; apply; rewrite -e.
  by rewrite scale_poly_eq0 negb_or lc_expn_scalp_neq0.
have sp' : size (p %/ (gcdp p q)) <= k.
  rewrite size_divp ?sgp // leq_sub_add (leq_trans hs)//.
  rewrite -subn_gt0 addnK -subn1 -ltn_add_sub addn0 ltnNge leq_eqVlt.
  by rewrite [_ == _]cop ltnS leqn0 size_poly_eq0 (negPf gn0).
case (ihk _ sp')=> r' dr'p'; first rewrite p'n0 orbF=> cr'q maxr'.
constructor=> //=; rewrite ?(negPf p0) ?orbF //.
  apply: (dvdp_trans dr'p'); apply: divp_dvd; exact: dvdp_gcdl.
move=> d dp cdq; apply: maxr'; last by rewrite cdq.
case dpq: (d %| gcdp p q).
  move: (dpq); rewrite dvdp_gcd dp /= => dq; apply: dvdUp; move: cdq. 
  apply: contraLR=> nd1; apply/coprimepPn; last first.
    by exists d; rewrite dvdp_gcd dvdpp dq nd1.
  move/negP: p0; move/negP; apply: contra=> d0; move:dp; rewrite (eqP d0).
  by rewrite dvd0p.
move: (dp); apply: contraLR=> ndp'.
rewrite (@eqp_dvdr ((lead_coef (gcdp p q) ^+ scalp p (gcdp p q))*:p)).
  by rewrite e; rewrite gausspl //; apply: (coprimep_dvdl (dvdp_gcdr _ _)).
by rewrite eqp_sym scale_eqp // lc_expn_scalp_neq0.
Qed.

Lemma gdcopP q p : gdcop_spec q p (gdcop q p).
Proof. by rewrite /gdcop; apply: gdcop_recP. Qed.

Lemma coprimep_gdco p q : (q != 0)%B -> coprimep (gdcop p q) p.
Proof. by move=> q_neq0; case: gdcopP=> d; rewrite (negPf q_neq0) orbF. Qed.

Lemma size2_dvdp_gdco p q d : p != 0 -> size d = 2%N ->
  (d %| (gdcop q p)) = (d %| p) && ~~(d %| q).
Proof.
case: (eqVneq d 0) => [-> | dn0]; first by rewrite size_poly0.
move=> p0 sd; apply/idP/idP.
  case: gdcopP=> r rp crq maxr dr; move/negPf: (p0)=> p0f.
  rewrite (dvdp_trans dr) //=.
  move: crq; apply: contraL=> dq; rewrite p0f orbF; apply/coprimepPn.
    by move:p0; apply: contra=> r0; move: rp; rewrite (eqP r0) dvd0p.
  by exists d; rewrite dvdp_gcd dr dq -size_poly_eq1 sd.
case/andP=> dp dq; case: gdcopP=> r rp crq maxr; apply: maxr=> //.
apply/coprimepP=> x xd xq.
move: (dvdp_leq dn0 xd); rewrite leq_eqVlt sd; case/orP; last first.
  rewrite ltnS leq_eqVlt; case/orP; first by rewrite -size_poly_eq1.
  rewrite ltnS leqn0 size_poly_eq0; move/eqP=> x0; move: xd; rewrite x0 dvd0p.
  by rewrite (negPf dn0).
by rewrite -sd dvdp_size_eqp //; move/(eqp_dvdl q); rewrite xq (negPf dq).
Qed.

Lemma dvdp_gdco p q : (gdcop p q) %| q.
Proof. by case: gdcopP. Qed.

Lemma root_gdco p q x : p != 0 -> root (gdcop q p) x = root p x && ~~(root q x).
Proof.
move=> p0 /=; rewrite !root_factor_theorem; apply: size2_dvdp_gdco; rewrite ?p0 //.
by rewrite size_addl size_polyX // size_opp size_polyC ltnS; case: (x != 0).
Qed.

Lemma dvdp_comp_poly r p q : (p %| q) -> (p \Po r) %| (q \Po r).
Proof.
case: (eqVneq p 0) => [-> | pn0].
  by rewrite poly_com0p !dvd0p; move/eqP->; rewrite poly_com0p.
rewrite dvdp_eq; set c := _ ^+ _; set s := _ %/ _; move/eqP=> Hq.
apply: (@eq_dvdp c (s \Po r)); first by rewrite expf_neq0 // lead_coef_eq0. 
by rewrite -comp_poly_scall Hq comp_poly_mull.
Qed.

Lemma gcdp_comp_poly r p q : gcdp p q \Po r %=  gcdp (p \Po r) (q \Po r).
Proof.
apply/andP; split.
  by rewrite dvdp_gcd !dvdp_comp_poly ?dvdp_gcdl ?dvdp_gcdr.
case: (bezoutp p q) => [[u v]] /andP [].
move/(dvdp_comp_poly r) => Huv _.
rewrite (dvdp_trans _ Huv) // comp_poly_addl !comp_poly_mull.
by rewrite dvdp_add // dvdp_mull // (dvdp_gcdl,dvdp_gcdr).
Qed.

Lemma coprimep_comp_poly r p q : coprimep p q -> coprimep (p \Po r) (q \Po r).
Proof.
rewrite -!gcdp_eqp1 -!size_poly_eq1 -!dvdp1; move/(dvdp_comp_poly r).
rewrite poly_comCp => Hgcd.
by apply: dvdp_trans Hgcd; case/andP: (gcdp_comp_poly r p q).
Qed.

End IDomainPseudoDivision.

Hint Resolve eqpxx divp0 divp1 mod0p modp0 modp1 dvdp_mull dvdp_mulr dvdpp.
Hint Resolve dvdp0.

Notation "p %= q" := (eqp p q) : ring_scope.

Module unit.

Import RPdiv.
Import ComRing.
Import UnitRing.
Import ID.

Section UnitDivisor.

Variable R : idomainType.
Variable d : {poly R}.

Hypothesis ulcd : GRing.unit (lead_coef d).

Implicit Type p q r : {poly R}.

Lemma divp_eq p : p = (p %/ d) * d + (p %% d).
Proof. by have := (divp_eq p d); rewrite scalpE ulcd expr0 scale1r. Qed.

Lemma edivpP p q r : p = q * d + r -> size r < size d -> 
  q = (p %/ d) /\ r = p %% d.
Proof.
move=> ep srd; have := (divp_eq p); rewrite {1}ep.
move/eqP; rewrite -subr_eq -addrA addrC eq_sym -subr_eq -mulr_subl; move/eqP.
have lcdn0 : lead_coef d != 0 by apply: contraTneq ulcd => ->; rewrite unitr0.
case abs: (p %/ d - q == 0).
  move: abs; rewrite subr_eq0; move/eqP->; rewrite subrr mul0r; move/eqP.
  by rewrite eq_sym subr_eq0; move/eqP->.
have hleq : size d <= size ((p %/ d - q) * d). 
  rewrite size_proper_mul; last first.
    by rewrite mulf_eq0 (negPf lcdn0) orbF lead_coef_eq0 abs.
  move: abs; rewrite -size_poly_eq0; move/negbT; rewrite -lt0n; move/prednK<-.
  by rewrite addSn /= leq_addl.
have hlt : size (r - p %% d) < size d.
  apply: leq_ltn_trans (size_add _ _) _; rewrite size_opp.
  by rewrite ltnNge leq_maxr negb_or -!ltnNge srd ltn_modp /= -lead_coef_eq0.
by move=> e; have:= (leq_trans hlt hleq); rewrite e ltnn.
Qed.

Lemma divpP p q r : p = q * d + r -> size r < size d -> 
  q = (p %/ d).
Proof. by move/edivpP=> h; case/h. Qed.

Lemma modpP p q r :  p = q * d + r -> size r < size d -> r = (p %% d).
Proof. by move/edivpP=> h; case/h. Qed.


(* Lemma dvdp_mull p : d %| (p * d). *)
(* Proof. *)
(* rewrite dvdpE ComReg.rdvdp_mull //; red; rewrite 1?mulrC //; exact: mulIr. *)
(* Qed. *)

(* Lemma dvdp_mulr p : d %| (d * p). *)
(* Proof. by rewrite mulrC dvdp_mull. Qed. *)


Lemma dvdp_eq p : (d %| p) = (p == p %/ d * d).
Proof.
apply/eqP/eqP=> [modp0 | ->]; last exact: modp_mull.
by rewrite {1}(divp_eq p) modp0 addr0.
Qed.

Lemma modp_scalel c p : (c *: p) %% d = c *: (p %% d).
Proof.
case: (altP (c =P 0)) => [-> | cn0]; first by rewrite !scale0r mod0p.
have e : (c *: p) = (c *: (p %/ d)) * d + c *: (p %% d).
  by rewrite -scaler_mull -scaler_addr -divp_eq.
have s: size (c *: (p %% d)) < size d.
  rewrite -mul_polyC; apply: leq_ltn_trans (size_mul _ _) _.
  rewrite size_polyC cn0 addSn add0n /= ltn_modp.
  by rewrite -lead_coef_eq0; apply: contraTneq ulcd => ->; rewrite unitr0.
by case: (edivpP e s) => _ ->.
Qed.

Lemma divp_scalel c p : (c *: p) %/ d = c *: (p %/ d).
Proof.
case: (altP (c =P 0)) => [-> | cn0]; first by rewrite !scale0r div0p.
have e : (c *: p) = (c *: (p %/ d)) * d + c *: (p %% d).
  by rewrite -scaler_mull -scaler_addr -divp_eq.
have s: size (c *: (p %% d)) < size d.
  rewrite -mul_polyC; apply: leq_ltn_trans (size_mul _ _) _.
  rewrite size_polyC cn0 addSn add0n /= ltn_modp.
  by rewrite -lead_coef_eq0; apply: contraTneq ulcd => ->; rewrite unitr0.
by case: (edivpP e s) => ->.
Qed.

Lemma eqp_modpl p q : p %= q -> (p %% d) %= (q %% d).
Proof.
case/eqpP=> [c1 [c2 [c1n0 c2n0 e]]]. 
by apply/eqpP; exists c1; exists c2; split=> //; rewrite -!modp_scalel e.
Qed.

Lemma eqp_divpl p q : p %= q -> (p %/ d) %= (q %/ d).
Proof.
case/eqpP=> [c1 [c2 [c1n0 c2n0 e]]]. 
by apply/eqpP; exists c1; exists c2; split=> //; rewrite -!divp_scalel e.
Qed.


Lemma modp_opp p : (- p) %% d = - (p %% d).
Proof.
by rewrite -mulN1r -[- (_ %% _)]mulN1r -polyC_opp !mul_polyC modp_scalel.
Qed.

Lemma divp_opp p : (- p) %/ d = - (p %/ d).
Proof.
by rewrite -mulN1r -[- (_ %/ _)]mulN1r -polyC_opp !mul_polyC divp_scalel.
Qed.

Lemma modp_add p q : (p + q) %% d = p %% d + q %% d.
Proof.
have hs : size (p %% d + q %% d) < size d.
  apply: leq_ltn_trans (size_add _ _) _; rewrite ltnNge leq_maxr negb_or.
  rewrite -!ltnNge !ltn_modp andbb -lead_coef_eq0.
  by apply: contraTneq ulcd => ->; rewrite unitr0.
have he : (p + q) = (p %/ d + q %/ d) * d + (p %% d + q %% d).
  rewrite {1}(divp_eq p) {1}(divp_eq q) addrAC addrA -mulr_addl.
  by rewrite [_ %% _ + _]addrC addrA.
by case: (edivpP he hs).
Qed.

Lemma divp_add p q : (p + q) %/ d = p %/ d + q %/ d.
Proof.
have hs : size (p %% d + q %% d) < size d.
  apply: leq_ltn_trans (size_add _ _) _; rewrite ltnNge leq_maxr negb_or.
  rewrite -!ltnNge !ltn_modp andbb -lead_coef_eq0.
  by apply: contraTneq ulcd => ->; rewrite unitr0.
have he : (p + q) = (p %/ d + q %/ d) * d + (p %% d + q %% d).
  rewrite {1}(divp_eq p) {1}(divp_eq q) addrAC addrA -mulr_addl.
  by rewrite [_ %% _ + _]addrC addrA.
by case: (edivpP he hs).
Qed.

Lemma mulpK q : (q * d) %/ d = q.
Proof.
have:= (sym_eq (addr0 (q * d))); case/edivpP; rewrite // size_poly0 size_poly_neq0.
by rewrite  -lead_coef_eq0; apply: contraTneq ulcd => ->; rewrite unitr0.
Qed.

Lemma mulKp q : (d * q) %/ d = q.
Proof. rewrite mulrC; exact: mulpK. Qed.

Lemma divp_addl_mul_small q r : 
  size r < size d -> (q * d + r) %/ d = q.
Proof. by move=> srd; rewrite divp_add (divp_small srd) addr0 mulpK. Qed.

Lemma modp_addl_mul_small q r :
  size r < size d -> (q * d + r) %% d = r.
Proof. by move=> srd; rewrite modp_add modp_mull add0r modp_small. Qed.

Lemma divp_addl_mul q r : (q * d + r) %/ d = q + r %/ d.
Proof. by rewrite divp_add mulpK. Qed.

Lemma divpp : d %/ d = 1.
rewrite divpE ulcd rdivpp; [| by red; rewrite 1?mulrC | exact: mulIr].
rewrite -mul_polyC -polyC_mul mulVr //; exact: unitr_exp.
Qed.

Lemma leq_floorp m : size (m %/ d * d) <= size m.
Proof.
have dn0 : d != 0.
  by rewrite -lead_coef_eq0; apply: contraTneq ulcd => ->; rewrite unitr0.
case q0 : (m %/ d == 0); first by rewrite (eqP q0) mul0r size_poly0 leq0n.
rewrite {2}(divp_eq m) size_addl // size_mul_id ?q0 //; move/negbT: q0.
rewrite -size_poly_neq0; move/prednK<-; rewrite addSn /=.
by move: dn0; rewrite -(ltn_modp m); move/ltn_addl->.
Qed.

Lemma dvdpP p : reflect (exists q, p = q * d) (d %| p).
Proof.
apply: (iffP idP) => [| [k ->]]; last by apply/eqP; rewrite modp_mull.
by rewrite dvdp_eq; move/eqP->; exists (p %/ d).
Qed.

Lemma divpK p : d %| p -> p %/ d * d = p.
Proof. by rewrite dvdp_eq; move/eqP. Qed.

Lemma divpKC p : d %| p -> d * (p %/ d) = p.
Proof. by move=> ?; rewrite mulrC divpK. Qed.

Lemma eqp_divp p q :  d %| p -> (q == p %/ d) = (q * d == p).
Proof. 
move/divpK=> {2}<-; apply/eqP/eqP; first by move->.
suff dn0 : d != 0 by move/(mulIf dn0).
by rewrite -lead_coef_eq0; apply: contraTneq ulcd => ->; rewrite unitr0.
Qed.

Lemma eqp_mulp p q : d %| p -> (p == q * d) = (p %/ d == q).
Proof. by move=>dv_d_p; rewrite eq_sym -eqp_divp // eq_sym. Qed.

Lemma divp_mulA p q : d %| q -> p * (q %/ d) = p * q %/ d.
Proof. 
move=> hdm; apply/eqP; rewrite eq_sym -eqp_mulp; first by rewrite -mulrA divpK.
by move/divpK: hdm<-; rewrite mulrA dvdp_mull.
Qed.

Lemma divp_mulAC m n : d %| m -> m %/ d * n = m * n %/ d.
Proof. by move=> hdm; rewrite mulrC (mulrC m); exact: divp_mulA. Qed.

Lemma divp_mulCA p q : d %| p -> d %| q -> p * (q %/ d) = q * (p %/ d).
Proof. by move=> hdp hdq; rewrite mulrC divp_mulAC // divp_mulA. Qed.

Lemma modp_mul p q : (p * (q %% d)) %% d = (p * q) %% d.
Proof.
have -> : q %% d = q - q %/ d * d by rewrite {2}(divp_eq q) -addrA addrC subrK.
rewrite mulr_addr modp_add // -mulNr mulrA -{2}[_ %% _]addr0; congr (_ + _).
by apply/eqP; apply: dvdp_mull.
Qed.

End UnitDivisor.

Section MoreUnitDivisor.

Variable R : idomainType.
Variable d : {poly R}.
Hypothesis ulcd : GRing.unit (lead_coef d).

Implicit Types p q : {poly R}.

Lemma expp_sub m n : n <= m -> (d ^+ (m - n))%N = d ^+ m %/ d ^+ n.
Proof. 
by move/subnK=> {2}<-; rewrite exprn_addr mulpK // lead_coef_exp_id unitr_exp. 
Qed.

Lemma divp_pmul2l p q : GRing.unit (lead_coef q) -> d * p %/ (d * q) = p %/ q.
Proof.
move=> uq.
have udq: GRing.unit (lead_coef (d * q)).
  by rewrite lead_coef_Imul commr_unit_mul ?ulcd //; red; rewrite mulrC.
rewrite {1}(divp_eq uq p) mulr_addr mulrCA divp_addl_mul //.
have dn0 : d != 0.
  by rewrite -lead_coef_eq0; apply: contraTneq ulcd => ->; rewrite unitr0.
have qn0 : q != 0.
  by rewrite -lead_coef_eq0; apply: contraTneq uq => ->; rewrite unitr0.
have dqn0 : d * q != 0 by rewrite mulf_eq0 negb_or dn0.
suff : size (d * (p %% q)) < size (d * q).
  by rewrite ltnNge -divpN0 // negbK => /eqP ->; rewrite addr0. 
case: (altP ( (p %% q) =P 0)) => [-> | rn0].
  by rewrite mulr0 size_poly0 size_poly_neq0.
rewrite !size_mul_id //; move: dn0; rewrite -size_poly_neq0.
by move/prednK<-; rewrite !addSn /= ltn_add2l ltn_modp.
Qed.

Lemma divp_pmul2r p q : GRing.unit (lead_coef p) ->  q * d %/ (p * d) = q %/ p.
Proof. by move=> uq; rewrite -!(mulrC d) divp_pmul2l. Qed.

Lemma divp_divl r p q : GRing.unit (lead_coef r) -> GRing.unit (lead_coef p) -> 
  q %/ p %/ r = q %/ (p * r).
Proof.
move=> ulcr ulcp. 
have e : q = (q %/ p %/ r) * (p * r) + ((q %/ p) %% r * p +  q %% p).
  rewrite addrA (mulrC p) mulrA -mulr_addl; rewrite -divp_eq //; exact: divp_eq.
have pn0 : p != 0.
  by rewrite -lead_coef_eq0; apply: contraTneq ulcp => ->; rewrite unitr0.
have rn0 : r != 0.
  by rewrite -lead_coef_eq0; apply: contraTneq ulcr => ->; rewrite unitr0.
have s : size ((q %/ p) %% r * p +  q %% p) < size (p * r).
  case: (altP ((q %/ p) %% r =P 0)) => [-> | qn0].
    rewrite mul0r add0r size_mul_id // (polySpred rn0) addnS /=.
    by apply: leq_trans (leq_addr _ _); rewrite ltn_modp.
  rewrite size_addl mulrC.
    by rewrite !size_mul_id // (polySpred pn0) !addSn /= ltn_add2l ltn_modp.
  rewrite size_mul_id // (polySpred qn0) addnS /=.
  by apply: leq_trans (leq_addr _ _); rewrite ltn_modp.
case: (edivpP _ e s) => //; rewrite lead_coef_Imul commr_unit_mul ?ulcp //.
by red; rewrite mulrC.
Qed.

Lemma divpAC p q : GRing.unit (lead_coef p) -> q %/ d %/ p =  q %/ p %/ d.
Proof. by move=> ulcp; rewrite !divp_divl // mulrC. Qed.

Lemma modp_scaler c p : GRing.unit c -> p %% (c *: d) = (p %% d).
Proof.
move=> cn0; case: (eqVneq d 0) => [-> | dn0]; first by rewrite scaler0 !modp0. 
have e : p = (c^-1 *: (p %/ d)) * (c *: d) + (p %% d).
  by rewrite scaler_swap scalerA mulVr // scale1r -(divp_eq ulcd).
suff s : size (p %% d) < size (c *: d). 
  by rewrite (modpP _ e s) // -mul_polyC lead_coef_Imul lead_coefC unitr_mul cn0.
by rewrite size_scaler ?ltn_modp //; apply: contraTneq cn0 => ->; rewrite unitr0.
Qed.

Lemma divp_scaler c p :  GRing.unit c -> p %/ (c *: d) = c^-1 *: (p %/ d).
Proof.
move=> cn0; case: (eqVneq d 0) => [-> | dn0].
   by rewrite scaler0 !divp0 scaler0.
have e : p = (c^-1 *: (p %/ d)) * (c *: d) + (p %% d).
  by rewrite scaler_swap scalerA mulVr // scale1r -(divp_eq ulcd).
suff s : size (p %% d) < size (c *: d).
  by rewrite (divpP _ e s) // -mul_polyC lead_coef_Imul lead_coefC unitr_mul cn0.
by rewrite size_scaler ?ltn_modp //; apply: contraTneq cn0 => ->; rewrite unitr0.
Qed.


End MoreUnitDivisor.

End unit.


Section FieldDivision.

Import RPdiv.
Import ComRing.
Import UnitRing.
Import ID.
Import unit.

Variable F : fieldType.

Implicit Type p q r d : {poly F}.

Lemma divp_eq p q : p = (p %/ q) * q + (p %% q).
Proof.
case: (eqVneq q 0) => [-> | qn0]; first by rewrite modp0 mulr0 add0r.
by apply: divp_eq; rewrite GRing.unitfE lead_coef_eq0. 
Qed.

Lemma divp_modpP p q d r : p = q * d + r -> size r < size d -> 
  q = (p %/ d) /\ r = p %% d.
Proof.
move=> he hs; apply: edivpP => //; rewrite GRing.unitfE lead_coef_eq0.
by rewrite -size_poly_neq0; apply: leq_trans hs. 
Qed.

Lemma divpP p q d r : p = q * d + r -> size r < size d -> 
  q = (p %/ d).
Proof. by move/divp_modpP=> h; case/h. Qed.

Lemma modpP p q d r :  p = q * d + r -> size r < size d -> r = (p %% d).
Proof. by move/divp_modpP=> h; case/h. Qed.

Lemma dvdp_eq q p : (q %| p) = (p == p %/ q * q).
Proof.
case: (eqVneq q 0) => [-> | qn0]; first by rewrite dvd0p mulr0 eq_sym.
by apply: dvdp_eq; rewrite GRing.unitfE lead_coef_eq0. 
Qed.

Lemma modp_scalel c p q : (c *: p) %% q = c *: (p %% q).
Proof.
case: (eqVneq q 0) => [-> | qn0]; first by rewrite !modp0.
by apply: modp_scalel; rewrite GRing.unitfE lead_coef_eq0. 
Qed.

Lemma mulpK p q : q != 0 -> p * q %/ q = p.
Proof. by move=> qn0; rewrite mulpK // unitfE lead_coef_eq0. Qed.

Lemma mulKp p q : q != 0 -> q * p %/ q = p.
Proof. by rewrite mulrC; exact: mulpK. Qed.

Lemma divp_scalel c p q : (c *: p) %/ q = c *: (p %/ q).
Proof.
case: (eqVneq q 0) => [-> | qn0]; first by rewrite !divp0 scaler0.
by apply: divp_scalel; rewrite GRing.unitfE lead_coef_eq0. 
Qed.

Lemma modp_scaler c p d : c != 0 -> p %% (c *: d) = (p %% d).
Proof.
move=> cn0; case: (eqVneq d 0) => [-> | dn0]; first by rewrite scaler0 !modp0. 
have e : p = (c^-1 *: (p %/ d)) * (c *: d) + (p %% d).
  by rewrite scaler_swap scalerA mulVf // scale1r -divp_eq.
suff s : size (p %% d) < size (c *: d) by rewrite (modpP e s).
by rewrite size_scaler ?ltn_modp.
Qed.

Lemma divp_scaler c p d : c != 0 -> p %/ (c *: d) = c^-1 *: (p %/ d).
Proof.
move=> cn0; case: (eqVneq d 0) => [-> | dn0].
  by rewrite scaler0 !divp0 scaler0.
have e : p = (c^-1 *: (p %/ d)) * (c *: d) + (p %% d).
  by rewrite scaler_swap scalerA mulVf // scale1r -divp_eq.
suff s : size (p %% d) < size (c *: d) by rewrite (divpP e s).
by rewrite size_scaler ?ltn_modp.
Qed.

Lemma eqp_modpl d p q : p %= q -> (p %% d) %= (q %% d).
Proof.
case/eqpP=> [c1 [c2 [c1n0 c2n0 e]]]. 
by apply/eqpP; exists c1; exists c2; split=> //; rewrite -!modp_scalel e.
Qed.

Lemma eqp_divpl d p q : p %= q -> (p %/ d) %= (q %/ d).
Proof.
case/eqpP=> [c1 [c2 [c1n0 c2n0 e]]]. 
by apply/eqpP; exists c1; exists c2; split=> //; rewrite -!divp_scalel e.
Qed.

Lemma eqp_modpr d p q : p %= q -> (d %% p) %= (d %% q).
Proof.
case/eqpP=> [c1 [c2 [c1n0 c2n0 e]]].
have -> : p = (c1^-1 * c2) *: q by rewrite -scalerA -e scalerA mulVf // scale1r.
by rewrite modp_scaler ?eqpxx // mulf_eq0 negb_or invr_eq0 c1n0.
Qed.

Lemma eqp_mod p1 p2 q1 q2 : p1 %= p2 -> q1 %= q2 -> p1 %% q1 %= p2 %% q2.
Proof.
move=> e1 e2; apply: eqp_trans (eqp_modpr _ e2). 
apply: eqp_trans (eqp_modpl _ e1); exact: eqpxx.
Qed.

Lemma eqp_divpr (d m n : {poly F}) : m %= n -> (d %/ m) %= (d %/ n).
Proof.
case/eqpP=> [c1 [c2 [c1n0 c2n0 e]]].
have -> : m = (c1^-1 * c2) *: n by rewrite -scalerA -e scalerA mulVf // scale1r.
by rewrite divp_scaler ?scale_eqp // ?invr_eq0 mulf_eq0 negb_or invr_eq0 c1n0.
Qed.

Lemma eqp_div p1 p2 q1 q2 : p1 %= p2 -> q1 %= q2 -> p1 %/ q1 %= p2 %/ q2.
Proof.
move=> e1 e2; apply: eqp_trans (eqp_divpr _ e2). 
apply: eqp_trans (eqp_divpl _ e1); exact: eqpxx.
Qed.

Lemma eqp_gdcor p q r : q %= r -> gdcop p q %= gdcop p r.
Proof.
move=> eqr; rewrite /gdcop (size_eqp eqr).
move: (size r)=> n; elim: n p q r eqr => [|n ihn] p q r; first by rewrite eqpxx.
move=> eqr /=; rewrite (eqp_coprimepl p eqr); case: ifP => _ //; apply: ihn. 
apply: eqp_div => //; exact: eqp_gcdl.
Qed.

Lemma eqp_gdcol p q r : q %= r -> gdcop q p %= gdcop r p.
Proof.
move=> eqr; rewrite /gdcop; move: (size p)=> n.
elim: n p q r eqr {1 3}p (eqpxx p) => [|n ihn] p q r eqr s esp /=.
  move: eqr; case: (eqVneq q 0)=> [-> | nq0 eqr] /=.
    by rewrite eqp_sym eqp0; move->; rewrite eqxx eqpxx.
  suff rn0 : r != 0 by rewrite (negPf nq0) (negPf rn0) eqpxx.
  by apply: contraTneq eqr => ->; rewrite eqp0.
rewrite (eqp_coprimepr _ eqr) (eqp_coprimepl _ esp); case: ifP=> _ //.
apply: ihn => //; apply: eqp_div => //; exact: eqp_gcd.
Qed.

Lemma eqp_rgdcop_gdcop q p : rgdcop q p %= gdcop q p.
Proof.
rewrite /rgdcop /gdcop; move: (size p)=> n.
elim: n p q {1 3}p {1 3}q (eqpxx p) (eqpxx q) => [|n ihn] p q s t /= sp tq.
  move: tq; case: (eqVneq t 0)=> [-> | nt0 etq].
    by rewrite eqp_sym eqp0; move->; rewrite eqxx eqpxx.
  suff qn0 : q != 0 by rewrite (negPf nt0) (negPf qn0) eqpxx.
  by apply: contraTneq etq => ->; rewrite eqp0.
rewrite rcoprimep_coprimep (eqp_coprimepl t sp) (eqp_coprimepr p tq). 
case: ifP=> // _; apply: ihn => //; apply: eqp_trans (eqp_rdivp_divp _ _) _.
by apply: eqp_div => //; apply: eqp_trans (eqp_rgcdp_gcdp _ _) _; apply: eqp_gcd.
Qed.

Lemma modp_opp p q : (- p) %% q = - (p %% q).
Proof.
case: (eqVneq q 0) => [-> | qn0]; first by rewrite !modp0.
by apply: modp_opp; rewrite GRing.unitfE lead_coef_eq0. 
Qed.

Lemma divp_opp p q : (- p) %/ q = - (p %/ q).
Proof.
case: (eqVneq q 0) => [-> | qn0]; first by rewrite !divp0 oppr0.
by apply: divp_opp; rewrite GRing.unitfE lead_coef_eq0. 
Qed.

Lemma modp_add d p q : (p + q) %% d = p %% d + q %% d.
Proof.
case: (eqVneq d 0) => [-> | dn0]; first by rewrite !modp0.
by apply: modp_add; rewrite GRing.unitfE lead_coef_eq0. 
Qed.

Lemma divp_add d p q : (p + q) %/ d = p %/ d + q %/ d.
Proof.
case: (eqVneq d 0) => [-> | dn0]; first by rewrite !divp0 addr0.
by apply: divp_add; rewrite GRing.unitfE lead_coef_eq0. 
Qed.

Lemma divp_addl_mul_small d q r : 
  size r < size d -> (q * d + r) %/ d = q.
Proof. 
move=> srd; rewrite divp_add (divp_small srd) addr0 mulpK //. 
by rewrite -size_poly_neq0; apply: leq_trans srd. 
Qed.

Lemma modp_addl_mul_small d q r :
  size r < size d -> (q * d + r) %% d = r.
Proof. by move=> srd; rewrite modp_add modp_mull add0r modp_small. Qed.

Lemma divp_addl_mul d q r : d != 0 -> (q * d + r) %/ d = q + r %/ d.
Proof. by move=> dn0; rewrite divp_add mulpK. Qed.

Lemma divpp d : d != 0 -> d %/ d = 1.
Proof. by move=> dn0; apply: divpp; rewrite GRing.unitfE lead_coef_eq0. Qed.

Lemma leq_floorp d m : size (m %/ d * d) <= size m.
Proof.
case: (eqVneq d 0) => [-> | dn0]; first by rewrite mulr0 size_poly0.
by apply: leq_floorp; rewrite GRing.unitfE lead_coef_eq0. 
Qed.

Lemma divpK d p : d %| p -> p %/ d * d = p.
Proof.
case: (eqVneq d 0) => [-> | dn0]; first by move/dvd0pP->; rewrite mulr0.
by apply: divpK; rewrite GRing.unitfE lead_coef_eq0. 
Qed.

Lemma divpKC d p : d %| p -> d * (p %/ d) = p.
Proof. by move=> ?; rewrite mulrC divpK. Qed.

Lemma eqp_divp d p q :  d != 0 -> d %| p -> (q == p %/ d) = (q * d == p).
Proof.
by move=> dn0; apply: eqp_divp; rewrite GRing.unitfE lead_coef_eq0.
Qed. 

Lemma eqp_mulp d p q : d != 0 -> d %| p -> (p == q * d) = (p %/ d == q).
Proof. by move=> dn0 dv_d_p; rewrite eq_sym -eqp_divp // eq_sym. Qed.

Lemma divp_mulA d p q : d %| q -> p * (q %/ d) = p * q %/ d.
Proof.
case: (eqVneq d 0) => [-> | dn0]; first by move/dvd0pP->; rewrite !divp0 mulr0.
by apply: divp_mulA; rewrite GRing.unitfE lead_coef_eq0.
Qed.

Lemma divp_mulAC d m n : d %| m -> m %/ d * n = m * n %/ d.
Proof. by move=> hdm; rewrite mulrC (mulrC m); exact: divp_mulA. Qed.

Lemma divp_mulCA d p q : d %| p -> d %| q -> p * (q %/ d) = q * (p %/ d).
Proof. by move=> hdp hdq; rewrite mulrC divp_mulAC // divp_mulA. Qed.

Lemma expp_sub d m n : d != 0 -> m >= n -> (d ^+ (m - n))%N = d ^+ m %/ d ^+ n.
Proof. by move=> dn0 /subnK=> {2}<-; rewrite exprn_addr mulpK // expf_neq0. Qed.

Lemma divp_pmul2l d q p : d != 0 -> q != 0 -> d * p %/ (d * q) = p %/ q.
Proof.
by move=> dn0 qn0; apply: divp_pmul2l; rewrite GRing.unitfE lead_coef_eq0. 
Qed.

Lemma divp_pmul2r d p q : d != 0 -> p != 0 ->  q * d %/ (p * d) = q %/ p.
Proof. by move=> dn0 qn0; rewrite -!(mulrC d) divp_pmul2l. Qed.

Lemma divp_divl r p q :  q %/ p %/ r = q %/ (p * r).
Proof.
case: (eqVneq r 0) => [-> | rn0]; first by rewrite mulr0 !divp0.
case: (eqVneq p 0) => [-> | pn0]; first by rewrite mul0r !divp0 div0p.
by apply: divp_divl; rewrite GRing.unitfE lead_coef_eq0.
Qed.

Lemma divpAC d p q : q %/ d %/ p =  q %/ p %/ d.
Proof. by rewrite !divp_divl // mulrC. Qed.

Lemma edivp_def p q : edivp p q = (0%N, p %/ q, p %% q).
Proof. 
rewrite edivp_def; congr (_, _, _); rewrite /scalp /edivp /redivp /=.
case (eqVneq q 0) => [-> | qn0]; first by rewrite eqxx lead_coef0 unitr0.
rewrite (negPf qn0) /= GRing.unitfE lead_coef_eq0 qn0 /=.
by case: (redivp_rec _ _ _ _) => [[]].
Qed.

Lemma divpE p q : p %/ q = (lead_coef q)^-(rscalp p q) *: (rdivp p q).
Proof.
case: (eqVneq q 0) => [-> | qn0]; first by rewrite rdivp0 divp0 scaler0.
by rewrite divpE GRing.unitfE lead_coef_eq0 qn0.
Qed.

Lemma modpE p q : p %% q = (lead_coef q)^-(rscalp p q) *: (rmodp p q).
Proof.
case: (eqVneq q 0) => [-> | qn0].
  by rewrite rmodp0 modp0 /rscalp /redivp eqxx lead_coef0 expr0 invr1 scale1r.
by rewrite modpE GRing.unitfE lead_coef_eq0 qn0.
Qed.

Lemma scalpE p q : scalp p q = 0%N.
Proof.
case: (eqVneq q 0) => [-> | qn0]; first by rewrite scalp0.
by rewrite scalpE GRing.unitfE lead_coef_eq0 qn0.
Qed.

(* Just to have it without importing the weak theory *)
Lemma dvdpE p q : p %| q = rdvdp p q. Proof. exact: dvdpE. Qed.
  
CoInductive edivp_spec m d : nat * {poly F} * {poly F} -> Type :=
  EdivpSpec n q r of 
  m = q * d + r & (d != 0) ==> (size r < size d) : edivp_spec m d (n, q, r).

Lemma edivpP m d : edivp_spec m d (edivp m d).
Proof.
rewrite edivp_def; constructor; first exact: divp_eq.
by apply/implyP=> dn0; rewrite ltn_modp.
Qed.

Lemma edivp_eq d q r : size r < size d -> edivp (q * d + r) d = (0%N, q, r).
Proof.
move=> srd; apply: edivp_eq ; rewrite // GRing.unitfE lead_coef_eq0.
rewrite -size_poly_neq0; exact: leq_trans srd.
Qed.

Lemma modp_mul p q m: (p * (q %% m)) %% m = (p * q) %% m.
Proof.
have -> : q %% m = q - q %/ m * m by rewrite {2}(divp_eq q m) -addrA addrC subrK.
rewrite mulr_addr modp_add // -mulNr mulrA -{2}[_ %% _]addr0; congr (_ + _).
by apply/eqP; apply: dvdp_mull.
Qed.

Lemma dvdpP p q : reflect (exists qq, p = qq * q) (q %| p).
Proof.
case: (eqVneq q 0)=> [-> | qn0]; last first.
  by apply: dvdpP; rewrite GRing.unitfE lead_coef_eq0.
rewrite dvd0p. 
by apply: (iffP idP) => [/eqP->| [? ->]]; [exists 1|]; rewrite mulr0.
Qed.

Lemma bezout_eq1_coprimepP : forall p q,
  reflect (exists u, u.1 * p + u.2 * q = 1) (coprimep p q).
Proof.
move=> p q; apply:(iffP idP)=> [hpq|]; last first.
  by case=>[[u v]] /= e; apply/bezout_coprimepP; exists (u, v); rewrite e eqpxx.
case/bezout_coprimepP: hpq => [[u v]] /=; case/eqpP=> c1 [c2 [c1n0 c2n0]] e.
exists (c2^-1  *: (c1 *: u), c2^-1 *: (c1 *: v)); rewrite /=  -!scaler_mull.
by rewrite -!scaler_addr e scalerA mulVf // scale1r.
Qed.

Lemma dvdp_gdcor p q : q != 0 -> p %| (gdcop q p) * (q ^+ size p).
Proof.
move=> q_neq0; rewrite /gdcop.
elim: (size p) {-2 5}p (leqnn (size p))=> {p} [|n ihn] p.
  rewrite size_poly_leq0; move/eqP->.
  by rewrite size_poly0 /= dvd0p expr0 mulr1 (negPf q_neq0).
move=> hsp /=; have [->|p_neq0] := altP (p =P 0).
  rewrite size_poly0 /= dvd0p expr0 mulr1 div0p /=.
  case: ifP=> // _; have := (ihn 0).
  by rewrite size_poly0 expr0 mulr1 dvd0p=> /(_ isT).
have [|ncop_pq] := boolP (coprimep _ _); first by rewrite dvdp_mulr ?dvdpp.
have g_gt1: (1 < size (gcdp p q))%N.
  have [|//|/eqP] := ltngtP; last by rewrite -coprimep_def (negPf ncop_pq).
  by rewrite ltnS leqn0 size_poly_eq0 gcdp_eq0 (negPf p_neq0).
have sd : (size (p %/ gcdp p q) < size p)%N.
  rewrite size_divp -?size_poly_eq0 -(subnKC g_gt1) // add2n /=.
  by rewrite -[size _]prednK ?size_poly_neq0 // ltnS subSS leq_subr.
rewrite -{1}[p](divpK (dvdp_gcdl _ q)) -(subnKC sd) addSnnS exprn_addr mulrA.
rewrite dvdp_mul ?ihn //; first by rewrite -ltnS (leq_trans sd).
by rewrite exprS dvdp_mulr // dvdp_gcdr.
Qed.

Section FieldRingMap.

Variable rR : ringType.

Variable f : {rmorphism F -> rR}.
Local Notation "p ^f" := (map_poly f p) : ring_scope.

Implicit Type a b : {poly F}.

Lemma redivp_map a b :
  redivp a^f b^f = (rscalp a b, (rdivp a b)^f, (rmodp a b)^f).
Proof. 
rewrite /rdivp /rscalp /rmodp /redivp map_poly_eq0 size_map_poly.
case: eqP; rewrite /= -(rmorph0 (map_poly_rmorphism f)) //; move/eqP=> q_nz.
move: (size a) => m; elim: m 0%N 0 a => [|m IHm] qq r a /=.
  rewrite  -!mul_polyC  !size_map_poly !lead_coef_map // -(map_polyXn f).
  by rewrite -!(map_polyC f) -!rmorphM -rmorph_sub -rmorphD; case: (_ < _).
rewrite  -!mul_polyC !size_map_poly !lead_coef_map // -(map_polyXn f).
by rewrite -!(map_polyC f) -!rmorphM -rmorph_sub -rmorphD /= IHm; case: (_ < _).
Qed.

End FieldRingMap.

Section FieldMap.

Variable rR : idomainType.

Variable f : {rmorphism F -> rR}.
Local Notation "p ^f" := (map_poly f p) : ring_scope.

Implicit Type a b : {poly F}.

Lemma edivp_map a b :
  edivp a^f b^f = (0%N, (a %/ b)^f, (a %% b)^f).
Proof.
case: (eqVneq b 0) => [-> | bn0].
  rewrite (rmorph0 (map_poly_rmorphism f)) ID.edivp_def !modp0 !divp0.
  by rewrite (rmorph0 (map_poly_rmorphism f)) scalp0.
rewrite /edivp redivp_map lead_coef_map GRing.rmorph_unit; last first.
  by rewrite GRing.unitfE lead_coef_eq0.
rewrite modpE divpE !map_poly_scaler !rmorphV ?rmorphX // GRing.unitfE.
by rewrite expf_neq0 // lead_coef_eq0.
Qed.

Lemma size_map_poly p : size p^f = size p.
Proof.
have [-> | nz_p] := eqVneq p 0; first by rewrite rmorph0 !size_poly0.
by rewrite size_poly_eq // fmorph_eq0 // lead_coef_eq0.
Qed.

Lemma scalp_map p q : scalp p^f q^f = scalp p q.
Proof. by rewrite /scalp edivp_map edivp_def. Qed.

Lemma map_divp p q : (p %/ q)^f = p^f %/ q^f.
Proof. by rewrite /divp edivp_map edivp_def. Qed.

Lemma map_modp p q : (p %% q)^f = p^f %% q^f.
Proof. by rewrite /modp edivp_map edivp_def. Qed.

Lemma dvdp_map p q : (p^f %| q^f) = (p %| q).
Proof. by rewrite /dvdp -map_modp map_poly_eq0. Qed.

Lemma eqp_map p q : (p^f %= q^f) = (p %= q).
Proof. by rewrite /eqp !dvdp_map. Qed.

Lemma gcdp_map p q : (gcdp p q)^f = gcdp p^f q^f.
Proof.
wlog lt_p_q: p q / size p < size q.
  move=> IH; case: (ltnP (size p) (size q)) => [|le_q_p]; first exact: IH.
  rewrite gcdpE (gcdpE p^f) !size_map_poly ltnNge le_q_p /= -map_modp.
  case: (eqVneq q 0) => [-> | q_nz]; first by rewrite rmorph0 !gcdp0.
  by rewrite IH ?ltn_modp.
elim: {q}_.+1 p {-2}q (ltnSn (size q)) lt_p_q => // m IHm p q le_q_m lt_p_q.
rewrite gcdpE (gcdpE p^f) !size_map_poly lt_p_q -map_modp.
case: (eqVneq p 0) => [-> | q_nz]; first by rewrite rmorph0 !gcdp0.
by rewrite IHm ?(leq_trans lt_p_q) ?ltn_modp.
Qed.

Lemma gdcop_rec_map p q n : (gdcop_rec p q n)^f = (gdcop_rec p^f q^f n).
Proof.
elim: n p q => [|n IH] => /= p q.
  by rewrite map_poly_eq0; case: eqP; rewrite ?rmorph1 ?rmorph0.
rewrite /coprimep -gcdp_map size_map_poly.
by case: eqP => Hq0 //; rewrite -map_divp -IH.
Qed.

Lemma gdcop_map p q : (gdcop p q)^f = (gdcop p^f q^f).
Proof. by rewrite /gdcop gdcop_rec_map !size_map_poly. Qed.

End FieldMap.

End FieldDivision.

