(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop ssralg poly polydiv orderedalg zmodp polydiv.
Require Import polyorder path interval zint.

Import GRing.Theory ORing.Theory AbsrNotation.
Import ID.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope nat_scope.
Open Scope ring_scope.

Local Notation noroot p := (forall x, ~~root p x).

Section ToBeMoved.
Section SeqR.

Lemma last1_neq0 : forall (R : ringType) (s: seq R) (c:R), c != 0 ->
  (last c s != 0) = (last 1 s != 0).
Proof. by move=> R'; elim=> [|t s ihs] c cn0 //; rewrite oner_eq0 cn0. Qed.

End SeqR.
End ToBeMoved.

Section PolyRCF.

Variable R : rcfType.

Section Prelim.

Implicit Types a b c : R.
Implicit Types x y z t : R.
Implicit Types p q r : {poly R}.

(* we restate poly_ivt in a nicer way. Perhaps the def of PolyRCF should *)
(* be moved in this file, juste above this section                       *)

Lemma poly_ivt : forall (p : {poly R}) (a b : R),
  a <= b -> 0 \in `[p.[a], p.[b]] -> { x : R | x \in `[a, b] & root p x }.
Proof. exact: poly_ivt. Qed.

Lemma polyrN0_int (i : interval R) (p : {poly R}) : {in i, noroot p}
  -> forall y x : R, y \in i -> x \in i -> sgr p.[x] = sgr p.[y].
Proof.
move=> hi y x hy hx; wlog xy: x y hx hy / x <= y=> [hwlog|].
  by case/orP: (ler_total x y)=> xy; [|symmetry]; apply: hwlog.
have hxyi: {subset `[x, y] <= i}.
  move=> z; apply: subintP=> /=.
  by case: i hx hy {hi}=> [[[] ?|] [[] ?|]] /=; do ?[move/intP->|move=> ?].
do 2![case: sgrP; first by move/rootP; rewrite (negPf (hi _ _))]=> //.
  move=> /ltrW py0 /ltrW p0x; case: (@poly_ivt (- p) x y)=> //.
    by rewrite inE !horner_opp !oppr_cp0 p0x.
  by move=> z hz; rewrite root_opp (negPf (hi z _)) // hxyi.
move=> /ltrW p0y /ltrW px0; case: (@poly_ivt p x y); rewrite ?inE ?px0 //.
by move=> z hz; rewrite (negPf (hi z _)) // hxyi.
Qed.

(* Todo : move to polydiv and change name
Lemma divfp_spec : forall p q, let k := lead_coef q ^- scalp p q in
  p = (k *: (p %/ q)) * q + k *: (p %% q).
Proof.
move=> p q k; apply/eqP.
rewrite -(inj_eq (@mulfI _ (k^-1)%:P  _)); last first.
  by rewrite polyC_eq0 invrK scalp_Ineq0.
rewrite !mul_polyC scaler_addr scaler_mull !scalerA mulVf.
  by rewrite invrK !scale1r divCp_spec.
by rewrite invr_neq0 // scalp_Ineq0.
Qed.

(* Todo : move to polydiv and change name *)
Lemma div_factor_spec :forall p x,
  p = (p %/ ('X - x%:P)) * ('X - x%:P) + (p %% ('X - x%:P)).
Proof.
move=> p x; rewrite {1}(@divfp_spec p ('X - x%:P)).
by rewrite lead_coef_factor exp1rn invr1 !scale1r.
Qed.

(* Todo : move to polydiv and change name *)
Lemma divfp_eq0 : forall p q, q != 0 -> (p %/ q == 0) = (size p < size q)%N.
Proof.
move=> p q q0; apply/idP/idP=> hpq; last by rewrite divp_size.
case p0: (p == 0); first by rewrite (eqP p0) size_poly0 lt0n size_poly_eq0.
case: (divCp_spec p q); rewrite (eqP hpq) mul0r add0r=> hpmpq.
apply: leq_ltn_trans (modp_spec p _)=> //.
rewrite // -hpmpq -mul_polyC size_mul_id ?p0 //.
   by rewrite size_polyC scalp_Ineq0.
by rewrite polyC_eq0 scalp_Ineq0.
Qed.

*)
Lemma poly_div_factor : forall (a:R) (P : {poly R} -> Prop),
  (forall k, P k%:P) ->
  (forall p n k, p.[a] != 0 -> P p ->
    P (p * ('X - a%:P)^+(n.+1) + k%:P)%R)
  -> forall p, P p.
Proof.
move=> a P Pk Pq p.
move: {-2}p (leqnn (size p)); elim: (size p)=> {p} [|n ihn] p spn.
  move: spn; rewrite leqn0 size_poly_eq0; move/eqP->; rewrite -polyC0.
  exact: Pk.
case: (leqP (size p) 1)=> sp1; first by rewrite [p]size1_polyC ?sp1//.
rewrite (mon.divp_eq (monic_factor a) p) [_ %% _]size1_polyC; last first.
  rewrite -ltnS.
  by rewrite (@leq_trans (size ('X - a%:P))) // ?ltn_modp ?factor_eq0 ?size_factor.
case: (@maxdivp _ (p %/ ('X - a%:P)) a)=> [|q hqa [n' hp]].
  by rewrite divpN0 ?size_factor ?factor_eq0 // -leqNgt.
rewrite hp -mulrA -exprSr; apply: Pq=> //; apply: ihn.
rewrite (@leq_trans (size (q * ('X - a%:P) ^+ n'))) //.
  rewrite size_mul_id ?expf_eq0 ?factor_eq0 ?andbF //; last first.
    by apply: contra hqa; move/eqP->; rewrite root0.
  by rewrite size_factor_exp addnS leq_addr.
by rewrite -hp size_divp ?factor_eq0 ?size_factor // leq_sub_add.
Qed.

Lemma nth_root x n : x > 0 -> { y | y > 0 & y ^+ (n.+1) = x }.
Proof.
move=> l0x.
case: (ltrgtP x 1)=> hx; last by exists 1; rewrite ?hx ?lter01// exp1rn.
  case: (@poly_ivt ('X ^+ n.+1 - x%:P) 0 1); first by rewrite ler01.
    rewrite ?(horner_lin,horner_exp) ?inE.
    by rewrite exprS mul0r sub0r exp1rn oppr_cp0 subr_gte0/= !ltrW.
  move=> y; case/andP=> [l0y ly1]; rewrite rootE ?(horner_lin,horner_exp).
  rewrite subr_eq0; move/eqP=> hyx; exists y=> //; rewrite ltr_neqAle l0y.
  rewrite andbT; apply/eqP=> y0; move: hyx; rewrite y0.
  by rewrite exprS mul0r=> x0; move: l0x; rewrite -x0 ltrr.
case: (@poly_ivt ('X ^+ n.+1 - x%:P) 0 x); first by rewrite ltrW.
  rewrite ?(horner_lin,horner_exp) exprS mul0r sub0r ?inE.
  by rewrite oppr_cp0 (ltrW l0x) subr_ge0 ler_eexprS// ltrW.
move=> y; case/andP=> l0y lyx; rewrite rootE ?(horner_lin,horner_exp).
rewrite subr_eq0; move/eqP=> hyx; exists y=> //; rewrite ltr_neqAle l0y.
rewrite andbT; apply/eqP=> y0; move: hyx; rewrite y0.
by rewrite exprS mul0r=> x0; move: l0x; rewrite -x0 ltrr.
Qed.

Lemma poly_cont x p e : e > 0 -> exists2 d,
  d > 0 & forall y, `|y - x| < d -> `|p.[y] - p.[x]| < e.
Proof.
elim/(@poly_div_factor x): p e.
  move=> e ep; exists 1; rewrite ?ltr01// => y hy.
  by rewrite !hornerC subrr absr0.
move=> p n k pxn0 Pp e ep.
case: (Pp (`|p.[x]|/2%:R)).
  by rewrite pmulr_lgt0 ?invr_gte0//= ?ltr0Sn// absrE.
move=> d' d'p He'.
case: (@nth_root (e / ((3%:R / 2%:R) * `|p.[x]|)) n).
  by rewrite ltr_pdivl_mulr ?mul0r ?pmulr_rgt0 ?invr_gt0 ?absrE ?ltr0Sn.
move=> d dp rootd.
exists (minr d d'); first by rewrite ltr_minr dp.
move=> y; rewrite ltr_minr; case/andP=> hxye hxye'.
rewrite !(horner_lin, horner_exp) subrr [0 ^+ _]exprS mul0r mulr0 add0r addrK.
rewrite absrM (@ler_lt_trans _  (`|p.[y]| * d ^+ n.+1)) //.
  by rewrite ler_wpmul2l ?absrE // absrX ler_expn2r -?topredE /= ?absrE 1?ltrW.
rewrite rootd mulrCA gtr_pmulr //.
rewrite ltr_pdivr_mulr ?mul1r ?pmulr_rgt0 ?invr_gt0 ?ltr0Sn ?absrE //.
rewrite mulr_addl mulr_addl divff; last by rewrite -mulr2n pnatr_eq0.
rewrite !mul1r mulrC -ltr_subl_addr.
by rewrite (ler_lt_trans _ (He' y _)) // ler_sub_dist.
Qed.

(* Todo : orderedpoly !! *)
(* Lemma deriv_expz_nat : forall (n : nat) p, (p ^ n)^`() = (p^`() * p ^ (n.-1)) *~ n. *)
(* Proof. *)
(* elim=> [|n ihn] p /=; first by rewrite expr0z derivC mul0zr. *)
(* rewrite exprSz_nat derivM ihn mulzrAr mulrCA -exprSz_nat. *)
(* by case: n {ihn}=> [|n] //; rewrite mul0zr addr0 mul1zr. *)
(* Qed. *)

(* Definition derivCE := (derivE, deriv_expz_nat). *)

(* Lemma size_poly_ind : forall K : {poly R} -> Prop, *)
(*   K 0 ->  *)
(*   (forall p sp, size p = sp.+1 ->   *)
(*     forall q, (size q <= sp)%N -> K q -> K p) *)
(*   -> forall p, K p. *)
(* Proof. *)
(* move=> K K0 ihK p. *)
(* move: {-2}p (leqnn (size p)); elim: (size p)=> {p} [|n ihn] p spn. *)
(*   by move: spn; rewrite leqn0 size_poly_eq0; move/eqP->. *)
(* case spSn: (size p == n.+1). *)
(*   move/eqP:spSn; move/ihK=> ihKp; apply: (ihKp 0)=>//. *)
(*   by rewrite size_poly0. *)
(* by move:spn; rewrite leq_eqVlt spSn /= ltnS; by move/ihn.  *)
(* Qed. *)

(* Lemma size_poly_indW : forall K : {poly R} -> Prop, *)
(*   K 0 ->  *)
(*   (forall p sp, size p = sp.+1 ->   *)
(*     forall q, size q = sp -> K q -> K p) *)
(*   -> forall p, K p. *)
(* Proof. *)
(* move=> K K0 ihK p. *)
(* move: {-2}p (leqnn (size p)); elim: (size p)=> {p} [|n ihn] p spn. *)
(*   by move: spn; rewrite leqn0 size_poly_eq0; move/eqP->. *)
(* case spSn: (size p == n.+1). *)
(*   move/eqP:spSn; move/ihK=> ihKp; case: n ihn spn ihKp=> [|n] ihn spn ihKp. *)
(*     by apply: (ihKp 0)=>//; rewrite size_poly0. *)
(*   apply: (ihKp 'X^n)=>//; first by rewrite size_polyXn. *)
(*   by apply: ihn; rewrite size_polyXn. *)
(* by move:spn; rewrite leq_eqVlt spSn /= ltnS; by move/ihn.  *)
(* Qed. *)

Lemma poly_ltsp_roots : forall p (rs : seq R),
  (size rs >= size p)%N -> uniq rs -> all (root p) rs -> p = 0.
Proof.
move=> p rs hrs urs rrs; apply/eqP; apply: contraLR hrs=> np0.
by rewrite -ltnNge; apply: max_poly_roots.
Qed.


Lemma ivt_sign : forall (p : {poly R}) (a b : R),
  a <= b -> sgr p.[a] * sgr p.[b] = -1 -> { x : R | x \in `]a, b[ & root p x}.
Proof.
move=> p a b hab /eqP; rewrite mulrC mulr_sg_eqN1=> /andP [spb0 /eqP spb].
 case: (@poly_ivt (sgr p.[b] *: p) a b)=> //.
  by rewrite !horner_scaler {1}spb mulNr -!absr_dec inE /= oppr_cp0 !absrE.
move=> c hc; rewrite root_scaler ?sgr_eq0 // => rpc; exists c=> //.
rewrite inE /= !ltr_neqAle andbCA -!andbA [_ && (_ <= _)]hc andbT eq_sym -negb_or.
apply/negP=> /orP [] /eqP ec; move: rpc; rewrite ec /root ?(negPf spb0) //.
by rewrite -sgr_cp0 -[sgr _]opprK -spb eqr_oppC oppr0 sgr_cp0 (negPf spb0).
Qed.

Let rolle_weak : forall a b p, a < b ->
  p.[a] = 0 -> p.[b] = 0 ->
   {c | (c \in `]a, b[) & (p^`().[c] == 0) || (p.[c] == 0)}.
Proof.
move=> a b p lab  pa0 pb0.
case p0: (p == 0).
  rewrite (eqP p0); exists (mid a b); first by rewrite mid_in_int.
  by rewrite derivC horner0 eqxx.
case: (@maxdivp _ p a)=> [|p' p'a0 [n hp]]; first by rewrite p0.
case: n hp pa0 p0 pb0 p'a0=> [|n].
  by rewrite {1}expr0 mulr1 rootE=> ->; move/eqP->.
move=> -> _ p0 pb0 p'a0; case: (@maxdivp _ p' b)=> [|q qb0 [m hp']].
  by apply: contra p'a0; move/eqP->; rewrite root0.
case: m hp' pb0 p0 p'a0 qb0=> [|m].
  rewrite {1}expr0 mulr1=> ->; move/eqP.
  rewrite !(horner_lin, horner_exp, mulf_eq0).
  by rewrite !expf_eq0 !subr_eq0 !(gtr_eqF lab) !andbF !orbF !rootE=> ->.
move=> -> _ p0 p'a0 qb0; case: (sgrP (q.[a] * q.[b])); first 2 last.
- move=> sqasb; case: (@ivt_sign q a b)=> //; first exact: ltrW.
    by apply/eqP; rewrite -sgrM sgr_cp0.
  move=> c lacb rqc; exists c=> //.
  by rewrite !horner_mul (eqP rqc) !mul0r eqxx orbT.
- move/eqP; rewrite mulf_eq0 (rootPf qb0) orbF; move/eqP=> qa0.
  by move: p'a0; rewrite ?root_mul rootE qa0 eqxx.
- move=> hspq.
  rewrite !derivCE subr0 !mul1r /= mulr_addl !natmulP.
  set xan := (('X - a%:P) ^+ n); set xbm := (('X - b%:P) ^+ m).
  have ->: ('X - a%:P) ^+ n.+1 = ('X - a%:P) * xan by rewrite exprS.
  have ->: ('X - b%:P) ^+ m.+1 = ('X - b%:P) * xbm by rewrite exprS.
  rewrite -mulrzl -[_ *~ n.+1]mulrzl.
  have fac : forall x y z : {poly R}, x * (y * xbm) * (z * xan)
    = (y * z * x) * (xbm * xan).
    by move=> x y z; rewrite mulrCA !mulrA [_ * y]mulrC mulrA.
  rewrite !fac -!mulr_addl; set r := _ + _ + _.
  case: (@ivt_sign (sgr q.[b] *: r) a b); first exact: ltrW.
    rewrite !horner_scaler !sgrM sgr_id mulrCA !mulrA mulr_sg (rootPf qb0) mul1r.
    rewrite /r !(subrr, mul0r, mulr0, addr0, add0r, hornerC, horner_factor,
      horner_add, horner_opp, horner_mul, horner_mulrn).
    rewrite [_ * _%:R]mulrC -!mulrA !natmulP !mulrzl !sgrMz -sgrM.
    rewrite mulrAC mulrA -mulrA sgrM -oppr_sub mulNr sgrN sgrM mulr_sg.
    rewrite subr_eq0 gtr_eqF // mulN1r.
    by apply/eqP; rewrite eqr_opp sgr_cp0 mulrC.
move=> c lacb; rewrite rootE horner_scaler mulf_eq0.
rewrite sgr_cp0 (rootPf qb0) orFb=> rc0.
by exists c=> //; rewrite !horner_mul !mulf_eq0 rc0.
Qed.

Theorem rolle : forall a b p, a < b ->
  p.[a] = p.[b] -> {c | c \in `]a, b[ & p^`().[c] = 0}.
Proof.
move=> a b p lab pab.
wlog pb0 : p pab / p.[b] = 0=> [hwlog|].
  case: (hwlog (p - p.[b]%:P)); rewrite ?horner_lin ?pab ?subrr //.
  by move=> c acb; rewrite derivE derivC subr0=> hc; exists c.
move: pab; rewrite pb0=> pa0.
have: (forall rs : seq R, {subset rs <= `]a, b[} ->
    (size p <= size rs)%N -> uniq rs -> all (root p) rs -> p = 0).
  by move=> rs hrs; apply: poly_ltsp_roots.
elim: (size p) a b lab pa0 pb0=> [|n ihn] a b lab pa0 pb0 max_roots.
  rewrite (@max_roots [::]) //=.
  by exists (mid a b); rewrite ?mid_in_int // derivE horner0.
case: (@rolle_weak a b p); rewrite // ?pa0 ?pb0 //=.
move=> c hc;  case: (altP (_ =P 0))=> //= p'c0 pc0; first by exists c.
suff: { d : R | d \in `]a, c[ & (p^`()).[d] = 0 }.
  case=> [d hd] p'd0; exists d=> //.
  by apply: subintPr hd; rewrite //= (intP hc).
apply: ihn=> //; first by rewrite (intP hc).
  exact/eqP.
move=> rs hrs srs urs rrs; apply: (max_roots (c :: rs))=> //=; last exact/andP.
  move=> x; rewrite in_cons; case/predU1P=> hx; first by rewrite hx.
  have: x \in `]a, c[ by apply: hrs.
  by apply: subintPr; rewrite /= (intP hc).
by rewrite urs andbT; apply/negP; move/hrs; rewrite bound_in_int.
Qed.

Theorem mvt : forall a b p, a < b ->
  {c | c \in `]a, b[ & p.[b] - p.[a] = p^`().[c] * (b - a)}.
Proof.
move=> a b p lab.
pose q := (p.[b] - p.[a])%:P * ('X - a%:P) - (b - a)%:P * (p - p.[a]%:P).
case: (@rolle a b q)=> //.
  by rewrite /q !horner_lin !(subrr,mulr0) mulrC subrr.
move=> c lacb q'x0; exists c=> //.
move: q'x0; rewrite /q !derivE !(mul0r,add0r,subr0,mulr1).
by move/eqP; rewrite !horner_lin mulrC subr_eq0; move/eqP.
Qed.

Lemma deriv_sign : forall a b p,
  (forall x, x \in `]a, b[ -> p^`().[x] >= 0)
  -> (forall x y, (x \in `]a, b[) && (y \in `]a, b[)
    ->  x < y -> p.[x] <= p.[y] ).
Proof.
move=> a b p Pab x y; case/andP=> hx hy xy.
rewrite -subr_gte0; case: (@mvt x y p)=> //.
move=> c hc ->; rewrite pmulr_lge0 ?subr_gt0 ?Pab //.
by apply: subintP hc; rewrite //= ?(intP hx) ?(intP hy).
Qed.

End Prelim.

Section CauchyBound.

Definition cauchy_bound (p : {poly R}) :=
  `|lead_coef p|^-1 * \sum_(i < size p) `|p`_i|.

(* Could be a sharp bound, and proof should shrink... *)
Lemma cauchy_boundP : forall (p : {poly R}) x,
  p != 0 -> p.[x] = 0 -> `| x | <= cauchy_bound p.
Proof.
move=> p x np0 rpx.
case e: (size p) => [|n]; first by move: np0; rewrite -size_poly_eq0 e eqxx.
have lcp : `|lead_coef p| > 0 by move: np0; rewrite -lead_coef_eq0 -absr_gt0.
have lcn0 : `|lead_coef p| != 0 by rewrite absr_eq0 -absr_gt0.
case: (lerP `|x| 1) => cx1.
  rewrite (ler_trans cx1) // /cauchy_bound ler_pdivl_mull // mulr1.
  rewrite e big_ord_recr /= /lead_coef e ler_addr sumr_ge0 //.
  move=> i _; exact: absr_ge0.
case es:  n e => [|m] e.
  suff p0 : p = 0 by rewrite p0 eqxx in np0.
    by move: rpx; rewrite (@size1_polyC _ p) ?e ?lerr // hornerC; move->.
move: rpx; rewrite horner_coef e -es big_ord_recr /=; move/eqP; rewrite eq_sym.
rewrite -subr_eq sub0r; move/eqP => h1.
have {h1} h1 : `|p`_n| * `|x| ^+ n <= \sum_(i < n) `|p`_i * x ^+ i|.
  rewrite -absrX -absrM -absrN h1.
  by rewrite (ler_trans (ler_abs_sum _ _ _)) // lerr.
have xp : `| x | > 0 by rewrite (ltr_trans _ cx1) ?ltr01.
move: h1; rewrite {-1}es exprS mulrA -ler_pdivl_mulr ?exprn_gt0 // big_distrl /=.
rewrite big_ord_recr /= absrM absrX -mulrA es mulfV; last first.
  by rewrite expf_eq0 negb_and eq_sym (ltr_eqF xp) orbT.
have pnp : 0 < `|p`_n|  by move: lcp; rewrite /lead_coef e es.
rewrite mulr1 -es mulrC -ler_pdivl_mulr //.
rewrite [_ / _]mulrC /cauchy_bound /lead_coef e -es /=.
move=> h1; apply: (ler_trans h1) => //.
rewrite ler_pmul2l ?invr_gt0 ?(ltrW pnp) // big_ord_recr /=.
rewrite es [_ + `|p`_m.+1|]addrC ler_paddl // ?absr_ge0 //.
rewrite big_ord_recr /= ler_add2r; apply: ler_sum => i.
rewrite absrM absrX.
rewrite -mulrA ler_pimulr ?absrE // ler_pdivr_mulr ?exprn_gt0 // mul1r.
by rewrite ler_eexpn2l // 1?ltrW //; case: i=> i hi /=; rewrite ltnW.
(* this could be improved a little bit with relative exponents *)
Qed.

End CauchyBound.

Section MonotonictyAndRoots.

Section NoRoot.

Variable (p : {poly R}).

Variables (a b : R).

Hypothesis der_pos : forall x, x \in `]a, b[ ->  (p^`()).[x] > 0.

Lemma derp0r : 0 <= p.[a] -> forall x, x \in `]a, b] -> p.[x] > 0.
Proof.
move=> pa0 x; case/int_dec=> ax xb; case: (mvt p ax) => c acx.
move/(canRL (@subrK _ _))->; rewrite ltr_paddr //.
by rewrite pmulr_rgt0 ?subr_gt0 // der_pos //; apply: subintPr acx.
Qed.

Lemma derppr : 0 < p.[a] -> forall x, x \in `[a, b] -> p.[x] > 0.
Proof.
move=> pa0 x hx; case exa: (x == a); first by rewrite (eqP exa).
case: (@mvt a x p); first by rewrite ltr_neqAle exa (intP hx).
move=> c hc; move/eqP; rewrite subr_eq; move/eqP->; rewrite ltr_spsaddr //.
rewrite pmulr_rgt0 ?subr_gt0 //; first by rewrite ltr_neqAle exa (intP hx).
by rewrite der_pos // (subintPr _ hc) //=  ?(intP hx).
Qed.

Lemma derp0l : p.[b] <= 0 -> forall x, x \in `[a, b[ -> p.[x] < 0.
Proof.
move=> pb0 x hx; rewrite -oppr_gte0 /=.
case: (@mvt x b p)=> //; first by rewrite (intP hx).
move=> c hc; move/(canRL (@addKr _ _))->; rewrite ltr_spaddr ?oppr_ge0 //.
rewrite pmulr_rgt0 // ?subr_gt0 ?(intP hx) //.
by rewrite der_pos // (subintPl _ hc) //= (intP hx).
Qed.

Lemma derpnl : p.[b] < 0 -> forall x, x \in `[a, b] -> p.[x] < 0.
Proof.
move=> pbn x hx; case xb: (b == x) pbn; first by rewrite -(eqP xb).
case: (@mvt x b p); first by rewrite ltr_neqAle xb ?(intP hx).
move=> y hy; move/eqP; rewrite subr_eq; move/eqP->.
rewrite !ltrNge; apply: contra=> hpx; rewrite ler_paddr // ltrW //.
rewrite pmulr_rgt0 ?subr_gt0 ?(intP hy) //.
by rewrite der_pos // (subintPl _ hy) //= (intP hx).
Qed.

End NoRoot.

Section NoRoot_sg.

Variable (p : {poly R}).

Variables (a b c : R).

Hypothesis derp_neq0 : {in `]a, b[, noroot p^`()}.
Hypothesis acb : c \in `]a, b[.

Local Notation sp'c := (sgr p^`().[c]).
Local Notation q := (sp'c *: p).

Fact derq_pos x : x \in `]a, b[ -> (q^`()).[x] > 0.
Proof.
move=> hx; rewrite derivZ horner_scaler -sgr_cp0.
rewrite sgrM sgr_id mulr_sg_eq1 derp_neq0 //=.
by apply/eqP; apply: (@polyrN0_int `]a, b[).
Qed.

Fact sgp x : sgr p.[x] = sp'c * sgr q.[x].
Proof.
by rewrite horner_scaler sgrM sgr_id mulrA mulr_sg derp_neq0 ?mul1r.
Qed.

Fact hsgp x : 0 < q.[x] -> sgr p.[x] = sp'c.
Proof. by rewrite -sgr_cp0 sgp => /eqP->; rewrite mulr1. Qed.

Fact hsgpN x : q.[x] < 0 -> sgr p.[x] = - sp'c.
Proof. by rewrite -sgr_cp0 sgp => /eqP->; rewrite mulrN1. Qed.

Lemma ders0r : p.[a] = 0 -> forall x, x \in `]a, b] -> sgr p.[x] = sp'c.
Proof.
move=> pa0 x hx; rewrite hsgp // (@derp0r _ a b) //; first exact: derq_pos.
by rewrite horner_scaler pa0 mulr0.
Qed.

Lemma derspr : sgr p.[a] = sp'c -> forall x, x \in `[a, b] -> sgr p.[x] = sp'c.
Proof.
move=> spa x hx; rewrite hsgp // (@derppr _ a b) //; first exact: derq_pos.
by rewrite -sgr_cp0 horner_scaler sgrM sgr_id spa mulr_sg derp_neq0.
Qed.

Lemma ders0l : p.[b] = 0 -> forall x, x \in `[a, b[ -> sgr p.[x] = -sp'c.
Proof.
move=> pa0 x hx; rewrite hsgpN // (@derp0l _ a b) //; first exact: derq_pos.
by rewrite horner_scaler pa0 mulr0.
Qed.

Lemma derspl : sgr p.[b] = -sp'c -> forall x, x \in `[a, b] -> sgr p.[x] = -sp'c.
Proof.
move=> spb x hx; rewrite hsgpN // (@derpnl _ a b) //; first exact: derq_pos.
by rewrite -sgr_cp0 horner_scaler sgrM sgr_id spb mulrN mulr_sg derp_neq0.
Qed.

End NoRoot_sg.

Variable (p : {poly R}).

Variables (a b : R).

Section der_root.

Hypothesis der_pos : forall x, x \in `]a, b[ ->  (p^`()).[x] > 0.

Lemma derp_root : a <= b -> 0 \in `]p.[a], p.[b][ ->
  { r : R |
    [/\ forall x, x \in `[a, r[ -> p.[x] < 0,
      p.[r] = 0,
      r \in `]a, b[ &
      forall x, x \in `]r, b] -> p.[x] > 0] }.
Proof.
move=> leab hpab.
have /eqP hs : sgr p.[a] * sgr p.[b] == -1.
  by rewrite -sgrM sgr_cp0 pmulr_llt0 ?(intP hpab).
case: (ivt_sign leab hs) => r arb pr0; exists r; split => //; last 2 first.
- by move/eqP: pr0.
- move=> x rxb; have hd : forall t, t \in `]r, b[ ->  0 < (p^`()).[t].
    by move=> t ht; rewrite der_pos // ?(subintPl _ ht) //= ?(intP arb).
  by rewrite (derp0r hd) ?(eqP pr0).
- move=> x rxb; have hd : forall t, t \in `]a, r[ ->  0 < (p^`()).[t].
    by move=> t ht; rewrite der_pos // ?(subintPr _ ht) //= ?(intP arb).
  by rewrite (derp0l hd) ?(eqP pr0).
Qed.

End der_root.

(* Section der_root_sg. *)

(* Hypothesis der_pos : forall x, x \in `]a, b[ ->  (p^`()).[x] != 0. *)

(* Lemma derp_root : a <= b -> sgr p.[a] != sgr p.[b] -> *)
(*   { r : R | *)
(*     [/\ forall x, x \in `[a, r[ -> p.[x] < 0, *)
(*       p.[r] = 0, *)
(*       r \in `]a, b[ & *)
(*       forall x, x \in `]r, b] -> p.[x] > 0] }. *)
(* Proof. *)
(* move=> leab hpab. *)
(* have hs : sgr p.[a] * sgr p.[b] == -1. *)
(*   by rewrite -sgrM sgr_cp0 mulr_lt0_gt0 ?(intP hpab). *)
(* case: (ivt_sign ivt leab hs) => r arb pr0; exists r; split => //; last 2 first. *)
(* - by move/eqP: pr0. *)
(* - move=> x rxb; have hd : forall t, t \in `]r, b[ ->  0 < (p^`()).[t]. *)
(*     by move=> t ht; rewrite der_pos // ?(subintPl _ ht) //= ?(intP arb). *)
(*   by rewrite (derp0r hd) ?(eqP pr0). *)
(* - move=> x rxb; have hd : forall t, t \in `]a, r[ ->  0 < (p^`()).[t]. *)
(*     by move=> t ht; rewrite der_pos // ?(subintPr _ ht) //= ?(intP arb). *)
(*   by rewrite (derp0l hd) ?(eqP pr0). *)
(* Qed. *)

(* End der_root. *)

End MonotonictyAndRoots.

Section RootsOn.

Variable T : predType R.

Definition roots_on (p : {poly R}) (i : T) (s : seq R) :=
  forall x, (x \in i) && (root p x) = (x \in s).

Lemma roots_onP : forall p i s, roots_on p i s -> {in i, root p =1 mem s}.
Proof. by move=> p i s hp x hx; move: (hp x); rewrite hx. Qed.

Lemma roots_on_in :  forall p i s,
 roots_on p i s -> forall x, x \in s -> x \in i.
Proof. by move=> p i s hp x; rewrite -hp; case/andP. Qed.

Lemma roots_on_root : forall p i s,
  roots_on p i s -> forall x, x \in s -> root p x.
Proof. by move=> p i s hp x; rewrite -hp; case/andP. Qed.

Lemma root_roots_on : forall p i s,
  roots_on p i s -> forall x, x \in i -> root p x -> x \in s.
Proof. by move=> p i s hp x; rewrite -hp=> ->. Qed.

Lemma roots_on_opp : forall p i s,
   roots_on (- p) i s -> roots_on p i s.
Proof. by move=> p i s hp x; rewrite -hp root_opp. Qed.

Lemma roots_on_nil : forall p i, roots_on p i [::] -> {in i, noroot p}.
Proof.
by move=> p i hp x hx; move: (hp x); rewrite in_nil hx /=; move->.
Qed.

Lemma roots_on_same : forall s' p i s,
  s =i s' -> (roots_on p i s <-> roots_on p i s').
Proof. by move=> s' p i s hss'; split=> hs x; rewrite (hss', (I, hss')). Qed.

End RootsOn.


(* (* Symmetry of center a *) *)
(* Definition symr (a x : R) := a - x. *)

(* Lemma symr_inv : forall a, involutive (symr a). *)
(* Proof. by move=> a y; rewrite /symr oppr_add addrA subrr opprK add0r. Qed. *)

(* Lemma symr_inj : forall a, injective (symr a). *)
(* Proof. by move=> a; apply: inv_inj; apply: symr_inv. Qed. *)

(* Lemma ltr_sym : forall a x y, (symr a x < symr a y) = (y < x). *)
(* Proof. by move=> a x y; rewrite lter_add2r lter_oppr opprK. Qed. *)

(* Lemma symr_add_int : forall a b x,  *)
(*   (a < symr (a + b) x < b) = (a < x < b). *)
(* Proof.  *)
(* move=> a b x; rewrite andbC.    *)
(* by rewrite lter_subrA lter_add2r -lter_addlA lter_add2l. *)
(* Qed. *)

Lemma roots_on_comp : forall p a b s,
  roots_on (p \Po (-'X)) `](-b), (-a)[
  (map (-%R) s) <-> roots_on p `]a, b[ s.
Proof.
move=> p a b /= s; split=> hs x; rewrite ?root_comp ?horner_lin.
  move: (hs (-x)); rewrite mem_map; last exact: (inv_inj (@opprK _)).
  by rewrite root_comp ?horner_lin oppr_int !opprK.
rewrite -[x]opprK oppr_int /= mem_map; last exact: (inv_inj (@opprK _)).
by move: (hs (-x)); rewrite !opprK.
Qed.

Lemma min_roots_on : forall p a b x s,
  all (>%R x) s -> roots_on p `]a, b[ (x :: s)
  -> [/\ x \in `]a, b[, (roots_on p `]a, x[ [::]),
    (root p x) & (roots_on p `]x, b[ s)].
Proof.
move=> p a b x s lxs hxs.
have hx: x \in `]a, b[ by rewrite (roots_on_in hxs) ?mem_head.
rewrite hx (roots_on_root hxs) ?mem_head //.
split=> // y; move: (hxs y); rewrite ?in_nil ?in_cons /=.
  case hy: (y \in `]a, x[)=> //=.
  rewrite (subintPr _ hy) //= ?(intP hx) //= => ->.
  rewrite ltr_eqF ?(intP hy) //=; apply/negP.
  by move/allP: lxs=> lxs /lxs; rewrite ltrNge ?(intP hy).
move/allP:lxs=>lxs; case eyx: (y == _)=> /=.
  case/andP=> hy _; rewrite (eqP eyx).
  rewrite boundl_in_int /=; symmetry.
  by apply/negP; move/lxs; rewrite ltrr.
case py0: root; rewrite !(andbT, andbF) //.
case ys: (y \in s); first by move/lxs:ys; rewrite ?inE => ->; case/andP.
move/negP; move/negP=> nhy; apply: negbTE; apply: contra nhy.
by apply: subintPl; rewrite //= ?(intP hx).
Qed.

Lemma max_roots_on : forall p a b x s,
  all (<%R x) s -> roots_on p `]a, b[ (x :: s)
  -> [/\ x \in `]a, b[, (roots_on p `]x, b[ [::]),
    (root p x) & (roots_on p `]a, x[ s)].
Proof.
move=> p a b x s; move/allP=> lsx; move/roots_on_comp=> /=.
move/min_roots_on; case.
  apply/allP=> y; rewrite -[y]opprK mem_map.
    by move/lsx; rewrite ltr_oppr opprK.
  exact: (inv_inj (@opprK _)).
rewrite oppr_int root_comp !horner_lin !opprK=> -> rxb -> rax.
by split=> //; apply/roots_on_comp.
Qed.

Lemma roots_on_cons : forall p a b r s,
  sorted >%R (r :: s) -> roots_on p `]a, b[ (r :: s) -> roots_on p `]r, b[ s.
Proof.
move=> p a b r s /= hrs hr.
have:= (order_path_min (@ltr_trans _) hrs)=> allrs.
by case: (min_roots_on allrs hr).
Qed.
(* move=> p a b r s hp hr x; apply/andP/idP. *)
(*   have:= (order_path_min (@ltr_trans _) hp) => /=; case/andP=> ar1 _. *)
(*   case; move/oointP=> rxb rpx; move: (hr x); rewrite in_cons rpx andbT. *)
(*   by rewrite rxb andbT (ltr_trans ar1) 1?eq_sym ?ltr_eqF  ?rxb. *)
(* move=> spx. *)
(* have xrsp: x \in r :: s by rewrite in_cons spx orbT. *)
(* rewrite (roots_on_root hr) //. *)
(* rewrite (roots_on_in hr xrsp); move: hp => /=; case/andP=> _. *)
(* by move/(order_path_min (@ltr_trans _)); move/allP; move/(_ _ spx)->. *)
(* Qed. *)

Lemma roots_on_rcons : forall p a b r s,
  sorted >%R (rcons s r) -> roots_on p `]a, b[ (rcons s r)
  -> roots_on p `]a, r[ s.
Proof.
move=> p a b r s; rewrite -{1}[s]revK -!rev_cons rev_sorted /=.
move=> hrs hr.
have := (order_path_min (rev_trans (@ltr_trans _)) hrs)=> allrrs.
have allrs: (all (<%R r) s).
  by apply/allP=> x hx; move/allP:allrrs; apply; rewrite mem_rev.
move/(@roots_on_same _ _ _ _ (r::s)):hr=>hr.
case: (max_roots_on allrs (hr _))=> //.
by move=> x; rewrite mem_rcons.
Qed.


(* move=> p a b r s; rewrite -{1}[s]revK -!rev_cons rev_sorted. *)
(* rewrite  [r :: _]lock /=; unlock; move=> hp hr x; apply/andP/idP. *)
(*   have:= (order_path_min (rev_trans (@ltr_trans _)) hp) => /=. *)
(*   case/andP=> ar1 _; case; move/oointP=> axr rpx. *)
(*   move: (hr x); rewrite mem_rcons in_cons rpx andbT axr andTb. *)
(*   by rewrite ((rev_trans (@ltr_trans _) ar1)) ?ltr_eqF ?axr. *)
(* move=> spx. *)
(* have xrsp: x \in rcons s r by rewrite mem_rcons in_cons spx orbT. *)
(* rewrite (roots_on_root hr) //. *)
(* rewrite (roots_on_in hr xrsp); move: hp => /=; case/andP=> _. *)
(* move/(order_path_min (rev_trans (@ltr_trans _))); move/allP.  *)
(* by move/(_ x)=> -> //; rewrite mem_rev. *)
(* Qed. *)

Lemma no_roots_on : forall (p : {poly R}) a b,
  {in `]a, b[, noroot p} -> roots_on p `]a, b[ [::].
Proof.
move=> p a b hr x; rewrite in_nil; case hx: (x \in _) => //=.
by apply: negPf; apply: hr hx.
Qed.

Lemma monotonic_rootN :  forall (p : {poly R}) (a b : R),
  {in `]a, b[,  noroot p^`()} ->
   ((roots_on p `]a, b[ [::]) + ({r : R | roots_on p `]a, b[ [:: r]}))%type.
Proof.
move=> p a b hp'; case: (ltrP a b); last first => leab.
  by left => x; rewrite in_nil int_gte.
wlog {hp'} hp'sg: p / forall x, x \in `]a, b[ -> sgr (p^`()).[x] = 1.
  move=> hwlog. have :=  (polyrN0_int hp').
  move: (mid_in_intoo leab)=> hm /(_ _ _ hm).
  case: (sgrP _.[mid a b])=> hpm.
  - by move=> abs; move: (hp' _ hm); rewrite rootE hpm eqxx.
  - by move/(hwlog p).
  - move=> hp'N; case: (hwlog (-p))=> [x|h|[r hr]].
    * by rewrite derivE horner_opp sgrN=> /hp'N->; rewrite opprK.
    * by left; apply: roots_on_opp.
    * by right; exists r; apply: roots_on_opp.
have hp'pos: forall x, x \in `]a, b[ -> (p^`()).[x] > 0.
  by move=> x; move/hp'sg; move/eqP; rewrite sgr_cp0.
case: (lerP 0 p.[a]) => ha.
- left; apply: no_roots_on => x axb.
  by rewrite rootE gtr_eqF // (@derp0r _ a b) // (subintPr _ axb) /=.
- case: (lerP p.[b] 0) => hb.
  + left => x; rewrite in_nil; apply: negbTE; case axb: (x \in `]a, b[) => //=.
    by rewrite rootE ltr_eqF // (@derp0l _ a b) // (subintPl _ axb) /=.
  + case: (derp_root hp'pos (ltrW leab) _).
      by rewrite ?inE; apply/andP.
  move=> r [h1 h2 h3] h4; right.
  exists r => x; rewrite in_cons in_nil (int_splitU2 h3).
  case exr: (x == r); rewrite ?(andbT, orbT, andbF, orbF) /=.
    by rewrite rootE (eqP exr) h2 eqxx.
  case px0: root; rewrite (andbT, andbF) //.
  move/eqP: px0=> px0; apply/negP; case/orP=> hx.
    by move: (h1 x); rewrite (subintPl _ hx) //= px0 ltrr; move/implyP.
  by move: (h4 x); rewrite (subintPr _ hx) //= px0 ltrr; move/implyP.
Qed.

(* Inductive polN0 : Type := PolN0 : forall p : {poly R}, p != 0 -> polN0. *)

(* Coercion pol_of_polN0 i := let: PolN0 p _ := i in p. *)

(* Canonical Structure polN0_subType := *)
(*   [subType for pol_of_polN0 by polN0_rect]. *)
(* Definition polN0_eqMixin := Eval hnf in [eqMixin of polN0 by <:]. *)
(* Canonical Structure polN0_eqType := *)
(*   Eval hnf in EqType polN0 polN0_eqMixin. *)
(* Definition polN0_choiceMixin := [choiceMixin of polN0 by <:]. *)
(* Canonical Structure polN0_choiceType := *)
(*   Eval hnf in ChoiceType polN0 polN0_choiceMixin. *)

(* Todo : Lemmas about operations of intervall :
   intersection, restriction and splitting *)
Lemma cat_roots_on : forall (p : {poly R}) a b x,
  x \in `]a, b[ -> ~~ (root p x)
  -> forall s s',
    sorted >%R s -> sorted >%R s'
    -> roots_on p `]a, x[ s -> roots_on p `]x, b[ s'
    -> roots_on p `]a, b[ (s ++ s').
Proof.
move=> p a b x hx /= npx0 s.
elim: s a hx => [|y s ihs] a hx s' //= ss ss'.
  move/roots_on_nil=> hax hs' y.
  rewrite -hs'; case py0: root; rewrite ?(andbT, andbF) //.
  rewrite (int_splitU2 hx); case: (y \in `]x, b[); rewrite ?orbF ?orbT //=.
  apply/negP; case/orP; first by  move/hax; rewrite py0.
  by move/eqP=> exy; rewrite -exy py0 in npx0.
move/min_roots_on; rewrite order_path_min //; last exact: ltr_trans.
case=> // hy hay py0 hs hs' z.
rewrite in_cons; case ezy: (z == y)=> /=.
  by rewrite (eqP ezy) py0 andbT (subintPr _ hy) //= ?(intP hx).
rewrite -(ihs y) //; last exact: path_sorted ss; last first.
  by rewrite inE /= (intP hx) (intP hy).
case pz0: root;  rewrite ?(andbT, andbF) //.
rewrite (@int_splitU2 _ y); last by rewrite (subintPr _ hy) //= (intP hx).
rewrite ezy /=; case: (z \in `]y, b[); rewrite ?orbF ?orbT //.
by apply/negP=> hz; move: (hay z); rewrite hz pz0 in_nil.
Qed.

CoInductive roots_spec (p : {poly R}) (i : pred R) (s : seq R) :
  {poly R} -> bool -> seq R -> Type :=
| Roots0 of p = 0 :> {poly R} & s = [::] : roots_spec p i s 0 true [::]
| Roots of p != 0 & roots_on p i s
  & sorted >%R s : roots_spec p i s p false s.

(* still much too long *)
Lemma int_roots : forall (p :{poly R}) (a b : R),
  {s : seq R & roots_spec p (topred `]a, b[) s p (p == 0) s}.
Proof.
move=> p a b; case p0: (_ == 0).
  by rewrite (eqP p0); exists [::]; constructor.
elim: (size p) {-2}p (leqnn (size p)) p0 a b => {p} [| n ihn] p sp p0 a b.
   by exists [::]; move: p0; rewrite -size_poly_eq0 -leqn0 sp.
move/negbT: (p0)=> np0.
case p'0 : (p^`() == 0).
  move: p'0; rewrite -derivn1 -derivn_poly0; move/size1_polyC => pC.
  exists [::]; constructor=> // x; rewrite in_nil pC rootC; apply: negPf.
  by rewrite negb_and -polyC_eq0 -pC p0 orbT.
move/negbT: (p'0) => np'0.
have sizep' : (size p^`() <= n)%N.
  rewrite -ltnS; apply: leq_trans sp; rewrite size_deriv prednK // lt0n.
  by rewrite size_poly_eq0 p0.
case: (ihn _ sizep' p'0 a b) => sp' ih {ihn}.
case ltab : (a < b); last first.
  exists [::]; constructor=> // x; rewrite in_nil.
  case axb : (x \in _) => //=.
  by case/andP: axb => ax xb; move: ltab; rewrite (ltr_trans ax xb).
elim: sp' a b ltab ih => [|r1 sp' hsp'] a b ltab hp'.
  case: hp' np'0; rewrite ?eqxx // =>  np'0 hroots' _ _.
  move/roots_on_nil : hroots' => hroots'.
  case: (monotonic_rootN hroots') => [h| [r rh]].
    by exists [::]; constructor.
  by exists [:: r]; constructor=> //=; rewrite andbT.
case: hp' np'0; rewrite ?eqxx // => np'0 hroots' /= hpath' _.
case: (min_roots_on _ hroots').
  by rewrite order_path_min //; apply: ltr_trans.
move=> hr1 har1 p'r10 hr1b.
case: (hsp' r1 b); first by rewrite (intP hr1).
  by constructor=> //; rewrite (path_sorted hpath').
move=> s spec_s.
case: spec_s np0; rewrite ?eqxx //.
move=> np0 hroot hsort _.
move: (roots_on_nil har1).
case pr1 : (root p r1); case/monotonic_rootN => hrootsl; last 2 first.
- exists s; constructor=> //.
  by rewrite -[s]cat0s; apply: (cat_roots_on hr1)=> //; rewrite pr1.
- case:hrootsl=> r hr; exists (r::s); constructor=> //=.
    by rewrite -cat1s; apply: (cat_roots_on hr1)=> //; rewrite pr1.
  rewrite path_min_sorted // => y; rewrite -hroot; case/andP=> hy _.
  rewrite (@ltr_trans _ r1) ?(intP hy) //.
  by rewrite (intP (roots_on_in hr (mem_head _ _))).
- exists (r1::s); constructor=> //=; last first.
    rewrite path_min_sorted=> // y; rewrite -hroot.
    by case/andP; move/intP->.
  move=> x; rewrite in_cons; case exr1: (x == r1)=> /=.
    by rewrite (eqP exr1) pr1 andbT.
  rewrite -hroot; case px: root; rewrite ?(andbT, andbF) //.
  rewrite (int_splitU2 hr1) exr1 /=.
  case: (_ \in `]r1, _[); rewrite ?(orbT, orbF) //.
  by apply/negP=> hx; move: (hrootsl x); rewrite hx px in_nil.
- case: hrootsl => r0 hrootsl.
  move/min_roots_on:hrootsl; case=> // hr0 har0 pr0 hr0r1.
  exists [:: r0, r1 & s]; constructor=> //=; last first.
    rewrite (intP hr0) /= path_min_sorted // => y.
    by rewrite -hroot; case/andP; move/intP->.
  move=> y; rewrite !in_cons (int_splitU2 hr1) (int_splitU2 hr0).
  case eyr0: (y == r0); rewrite ?(orbT, orbF, orTb, orFb).
    by rewrite (eqP eyr0) pr0.
  case eyr1: (y == r1); rewrite ?(orbT, orbF, orTb, orFb).
    by rewrite (eqP eyr1) pr1.
  rewrite -hroot; case py0: root; rewrite ?(andbF, andbT) //.
  case: (_ \in `]r1, _[); rewrite ?(orbT, orbF) //.
  apply/negP; case/orP=> hy; first by move: (har0 y); rewrite hy py0 in_nil.
  by move: (hr0r1 y); rewrite hy py0 in_nil.
Qed.

Definition roots (p : {poly R}) a b :=  projT1 (int_roots p a b).

Lemma rootsP : forall p a b,
  roots_spec p (topred `]a, b[) (roots p a b) p (p == 0) (roots p a b).
Proof. by move=> p a b; rewrite /roots; case hp: int_roots. Qed.

Lemma roots0 : forall a b, roots 0 a b = [::].
Proof. by move=> a b; case: rootsP=> //=; rewrite eqxx. Qed.

Lemma roots_on_roots : forall p a b, p != 0 ->
  roots_on p `]a, b[ (roots p a b).
Proof. by move=> a b p; case:rootsP. Qed.
Hint Resolve roots_on_roots.

Lemma sorted_roots : forall a b p, sorted >%R (roots p a b).
Proof. by move=> p a b; case: rootsP. Qed.
Hint Resolve sorted_roots.

Lemma path_roots : forall p a b, path >%R a (roots p a b).
Proof.
move=> p a b; case: rootsP=> //= p0 hp sp; rewrite path_min_sorted //.
by move=> y; rewrite -hp; case/andP; move/intP->.
Qed.
Hint Resolve path_roots.

Lemma root_is_roots :
   forall (p : {poly R}) (a b : R),  p != 0 ->
     forall x, x \in `]a, b[ -> root p x = (x \in roots p a b).
Proof.
by move=> p a b; case: rootsP=> // p0 hs ps _ y hy /=; rewrite -hs hy.
Qed.

Lemma root_in_roots : forall (p : {poly R}) a b, p != 0 ->
  forall x, x \in `]a, b[ -> root p x -> x \in (roots p a b).
Proof. by move=> p a b p0 x axb rpx; rewrite -root_is_roots. Qed.

Lemma root_roots : forall p a b x, x \in roots p a b -> root p x.
Proof. by move=> p a b x; case: rootsP=> // p0 <- _; case/andP. Qed.

Lemma roots_nil : forall p a b, p != 0 ->
  roots p a b = [::] -> {in `]a, b[, noroot p}.
Proof.
move=> p a b; case: rootsP=> // p0 hs ps _ s0 x axb.
by move: (hs x); rewrite s0 in_nil !axb /= => ->.
Qed.

Lemma roots_in : forall p a b x, x \in roots p a b -> x \in `]a, b[.
Proof. by move=> p a b x; case: rootsP=> // *; apply: roots_on_in. Qed.

Lemma rootsEba : forall p a b, b <= a -> roots p a b = [::].
Proof.
move=> p a b; case: rootsP=> // p0; case: (roots _ _ _)=> [|x s] hs ps ba //;
by move: (hs x); rewrite int_gte //= mem_head.
Qed.

Lemma roots_on_uniq : forall p a b s1 s2,
  sorted >%R s1 -> sorted >%R s2 ->
  roots_on p `]a, b[ s1 -> roots_on p `]a, b[ s2 -> s1 = s2.
Proof.
move=> p a b s1.
elim: s1 p a b => [| r1 s1 ih] p a b [| r2 s2] ps1 ps2 rs1 rs2 //.
- have rpr2 : root p r2 by apply: (roots_on_root rs2); rewrite mem_head.
  have abr2 : r2 \in `]a, b[ by apply: (roots_on_in rs2); rewrite mem_head.
  by have:= (rs1 r2); rewrite rpr2 !abr2 in_nil.
- have rpr1 : root p r1 by apply: (roots_on_root rs1); rewrite mem_head.
  have abr1 : r1 \in `]a, b[ by apply: (roots_on_in rs1); rewrite mem_head.
  by have:= (rs2 r1); rewrite rpr1 !abr1 in_nil.
- have er1r2 : r1 = r2.
    move: (rs1 r2); rewrite (roots_on_root rs2) ?mem_head //.
    rewrite !(roots_on_in rs2) ?mem_head //= in_cons.
    move/(@sym_eq _ true); case/orP => hr2; first by rewrite (eqP hr2).
    move: ps1=> /=; move/(order_path_min (@ltr_trans R)); move/allP.
    move/(_ r2 hr2) => h1.
    move: (rs2 r1);  rewrite (roots_on_root rs1) ?mem_head //.
    rewrite !(roots_on_in rs1) ?mem_head //= in_cons.
    move/(@sym_eq _ true); case/orP => hr1; first by rewrite (eqP hr1).
    move: ps2=> /=; move/(order_path_min (@ltr_trans R)); move/allP.
    by move/(_ r1 hr1); rewrite ltrNge ltrW.
congr (_ :: _) => //; rewrite er1r2 in ps1 rs1.
have h3 := (roots_on_cons ps1 rs1).
have h4 := (roots_on_cons ps2 rs2).
move: ps1 ps2=> /=; move/path_sorted=> hs1; move/path_sorted=> hs2.
exact: (ih p _ b _  hs1 hs2 h3 h4).
Qed.

Lemma roots_eq : forall (p q : {poly R}) (a b : R),
  p != 0 -> q != 0 ->
  ({in `]a, b[, root p =1 root q}
    <-> roots p a b = roots q a b).
Proof.
move=> p q a b p0 q0.
case hab : (a < b); last first.
  split; first by rewrite !rootsEba // lerNgt hab.
  move=> _ x. rewrite !inE; case/andP=> ax xb.
  by move: hab; rewrite (@ltr_trans _ x) /=.
split=> hpq.
  apply: (@roots_on_uniq p a b); rewrite ?path_roots ?p0 ?q0 //.
    by apply: roots_on_roots.
  rewrite /roots_on => x; case hx: (_ \in _).
    by rewrite -hx hpq //; apply: roots_on_roots.
  by rewrite /= -(andFb (q.[x] == 0)) -hx; apply: roots_on_roots.
move=> x axb /=.
by rewrite (@root_is_roots q a b) // (@root_is_roots p a b) // hpq.
Qed.

Lemma roots_opp : forall p, roots (- p) =2 roots p.
Proof.
move=> p a b; case p0 : (p == 0); first by rewrite (eqP p0) oppr0.
by apply/roots_eq=> [||x]; rewrite ?oppr_eq0 ?p0 ?root_opp.
Qed.

Lemma no_root_roots : forall (p : {poly R}) a b,
  {in `]a, b[ , noroot p} -> roots p a b = [::].
Proof.
move=> p a b hr; case: rootsP=> // p0 hs ps.
apply: (@roots_on_uniq p a b)=> // x; rewrite in_nil.
by apply/negP; case/andP; move/hr; move/negPf->.
Qed.

Lemma head_roots_on_ge : forall p a b s, a < b ->
  roots_on p `]a, b[ s -> a < head b s.
Proof.
move=> p a b [|x s] ab //; move/(_ x).
by rewrite in_cons eqxx; case/andP; case/andP.
Qed.

Lemma head_roots_ge : forall p a b, a < b -> a < head b (roots p a b).
Proof.
by move=> p a b; case: rootsP=> // *; apply: head_roots_on_ge.
Qed.

Lemma last_roots_on_le : forall p a b s, a < b ->
  roots_on p `]a, b[ s -> last a s < b.
Proof.
move=> p a b [|x s] ab rs //.
by rewrite (intP (roots_on_in rs _)) //= mem_last.
Qed.

Lemma last_roots_le : forall p a b, a < b -> last a (roots p a b) < b.
Proof.
by move=> p a b; case: rootsP=> // *; apply: last_roots_on_le.
Qed.

Lemma roots_uniq : forall p a b s, p != 0 ->
  roots_on p `]a, b[ s -> sorted >%R s -> s = roots p a b.
Proof.
move=> p a b s; case: rootsP=> // p0 hs' ps' _ hs ss.
exact: (@roots_on_uniq p a b)=> //.
Qed.

Lemma roots_cons : forall p a b x s,
  (roots p a b == x :: s)
  = [&& p != 0, x \in `]a, b[,
    (roots p a x == [::]),
    (root p x) & (roots p x b == s)].
Proof.
move=> p a b x s; case: rootsP=> // p0 hs' ps' /=.
apply/idP/idP.
  move/eqP=> es'; move: ps' hs'; rewrite es' /= => sxs.
  case/min_roots_on; first by apply: order_path_min=> //; apply: ltr_trans.
  move=> -> rax px0 rxb.
  rewrite px0 (@roots_uniq p a x [::]) // (@roots_uniq p x b s) ?eqxx //=.
  by move/path_sorted:sxs.
case: rootsP p0=> // p0 rax sax _.
case/and3P=> hx hax; rewrite (eqP hax) in rax sax.
case: rootsP p0=> // p0 rxb sxb _.
case/andP=> px0 hxb; rewrite (eqP hxb) in rxb sxb.
rewrite [_ :: _](@roots_uniq p a b) //; last first.
  rewrite /= path_min_sorted // => y.
  by rewrite -(eqP hxb); move/roots_in; move/intP->.
move=> y; rewrite (int_splitU2 hx) !andb_orl in_cons.
case hy: (y == x); first by rewrite (eqP hy) px0 orbT.
by rewrite andFb orFb rax rxb in_nil.
Qed.

(* Lemma size_poly_comp : forall p q : {poly R},  *)
(*   (size (p \Po q)).-1 = ((size p).-1 * (size q).-1)%N. *)
(* Proof. *)
(* elim/poly_ind=> [|p c ihp] q. *)
(*   by rewrite poly_com0p size_poly0 mul0n. *)
(* rewrite poly_comp_amulX size_addl. *)
(*   rewrite size_mul_id. *)
(* Admitted. *)

(* Lemma lead_coef_comp : forall p q : {poly R}, (1 < size q)%N ->  *)
(*   lead_coef (p \Po q) = lead_coef p * (lead_coef q) ^+ (size p). *)
(* Proof. *)
(* elim/poly_ind=> [|p c ihp] q hq. *)
(*   by rewrite poly_com0p lead_coef0 mul0r. *)
(* rewrite poly_comp_amulX !lead_coef_addl. *)
(* * rewrite !lead_coef_Imul ihp // lead_coefX mulr1 size_addl /=. *)
(* Admitted. *)

(* Lemma roots_comp : forall p a b, p != 0 -> *)
(*   roots p a b = rev (map -%R (roots (p \Po (-'X)) (-b) (-a))). *)
(* Proof. *)
(* move=> p a b np0; set rcp := roots (_ \Po _) _ _. *)
(* have ncp0 : (p \Po (-'X)) != 0. *)
(*   rewrite -lead_coef_eq0. *)
(*   rewrite poly_compE. *)
(*   rewrite big_ord_recr. *)
(*   move: np0; apply: contra. move/poly_eq0=> hcp. *)
(*   apply/poly_eq0=> x; move: (hcp (-x)). *)
(*   by rewrite horner_poly_comp !horner_lin opprK. *)
(* apply/eqP; apply/roots_uniq=> //. *)
(* move: (eqxx rcp); rewrite {1}/rcp; case/roots_uniq=> //. *)
(* move=> hrcp prcp. *)
(* split. *)
(*   apply/roots_on_comp; rewrite map_rev -map_comp. *)
(*   apply/(@roots_on_same rcp)=> // x. *)
(*   by rewrite mem_rev map_id_in // => y /=; rewrite opprK. *)


Lemma roots_rcons : forall p a b x s,
  (roots p a b == rcons s x)
  = [&& p != 0, x \in `]a , b[,
    (roots p x b == [::]),
    (root p x) & (roots p a x == s)].
Proof.
move=> p a b x s; case: rootsP; first by case: s.
move=> // p0 hs' ps' /=.
apply/idP/idP.
  move/eqP=> es'; move: ps' hs'; rewrite es' /= => sxs.
  have hsx: rcons s x =i x :: rev s.
    by move=> y; rewrite mem_rcons !in_cons mem_rev.
  move/(roots_on_same _ _ hsx).
  case/max_roots_on.
    move: sxs; rewrite -[rcons _ _]revK rev_sorted rev_rcons.
    by apply: order_path_min=> u v w /=; move/(ltr_trans _); apply.
  move=> -> rax px0 rxb.
  move/(@roots_on_same _ s): rxb; move/(_ (mem_rev _))=> rxb.
  rewrite px0 (@roots_uniq p x b [::]) // (@roots_uniq p a x s) ?eqxx //=.
  move: sxs; rewrite -[rcons _ _]revK rev_sorted rev_rcons.
  by move/path_sorted; rewrite -rev_sorted revK.
case: rootsP p0=> // p0 rax sax _.
case/and3P=> hx hax; rewrite (eqP hax) in rax sax.
case: rootsP p0=> // p0 rxb sxb _.
case/andP=> px0 hxb; rewrite (eqP hxb) in rxb sxb.
rewrite [rcons _ _](@roots_uniq p a b) //; last first.
  rewrite -[rcons _ _]revK rev_sorted rev_rcons /= path_min_sorted.
    by rewrite -rev_sorted revK.
  move=> y; rewrite mem_rev; rewrite -(eqP hxb).
  by move/roots_in; move/intP->.
move=> y; rewrite (int_splitU2 hx) mem_rcons in_cons !andb_orl.
case hy: (y == x); first by rewrite (eqP hy) px0 orbT.
by rewrite rxb rax in_nil !orbF.
Qed.

Section NeighborHood.

Implicit Types a b : R.

Implicit Types p : {poly R}.

Definition next_root (p : {poly R}) x b := if p == 0 then x else head (maxr b x) (roots p x b).

Lemma next_root0 : forall a b, next_root 0 a b = a.
Proof. by move=> *; rewrite /next_root eqxx. Qed.

CoInductive next_root_spec (p : {poly R}) x b : bool -> R -> Type :=
| NextRootSpec0 of p = 0 : next_root_spec p x b true x
| NextRootSpecRoot y of p != 0 & p.[y] = 0 & y \in `]x, b[
  & {in `]x, y[, forall z, ~~(root p z)} : next_root_spec p x b true y
| NextRootSpecNoRoot c of p != 0 & c = maxr b x
  & {in `]x, b[, forall z, ~~(root p z)} : next_root_spec p x b (p.[c] == 0) c.

Lemma next_rootP : forall (p : {poly R}) a b, next_root_spec p a b (p.[next_root p a b] == 0) (next_root p a b).
Proof.
move=> p a b; rewrite /next_root /=.
case hs: roots=> [|x s] /=.
  case: (altP (p =P 0))=> p0.
    by rewrite {2}p0 hornerC eqxx; constructor; rewrite p0.
  by constructor=> // y hy; apply: (roots_nil p0 hs).
move/eqP: hs; rewrite roots_cons; case/and5P=> p0 hx; move/eqP=> rap rpx rx.
rewrite (negPf p0) (rootPt rpx); constructor=> //; first by move/eqP: rpx.
by move=> y hy /=; move/(roots_nil p0): (rap); apply.
Qed.

Lemma next_root_in : forall p a b, next_root p a b \in `[a, maxr b a].
Proof.
move=> p a b; case: next_rootP=> [p0|y np0 py0 hy _|c np0 hc _].
* by rewrite bound_in_int /= ler_maxr lerr orbT.
* by apply: subintP hy=> /=; rewrite ler_maxr !lerr.
* by rewrite hc bound_in_int /= ler_maxr lerr orbT.
Qed.

Lemma next_root_gt : forall p a b, a < b -> p != 0 -> next_root p a b > a.
Proof.
move=> p a b ab np0; case: next_rootP=> [p0|y _ py0 hy _|c _ -> _].
* by rewrite p0 eqxx in np0.
* by rewrite (intP hy).
* by rewrite maxr_l // ltrW.
Qed.

Lemma next_noroot : forall p a b, {in `]a, (next_root p a b)[, noroot p}.
Proof.
move=> p a b z; case: next_rootP; first by rewrite int_xx.
  by move=> y np0 py0 hy hp hz; rewrite (negPf (hp _ _)).
move=> c p0 -> hp hz; rewrite (negPf (hp _ _)) //.
by case: maxrP hz; last by rewrite int_xx.
Qed.

Lemma is_next_root : forall p a b x, next_root_spec p a b (root p x) x -> x = next_root p a b.
Proof.
move=> p a b x []; first by move->; rewrite /next_root eqxx.
  move=> y; case: next_rootP; first by move->; rewrite eqxx.
  move=> y' np0 py'0 hy' hp' _ py0 hy hp.
    wlog: y y' hy' hy hp' hp py0 py'0 / y <= y'.
      by case/orP: (ler_total y y')=> lyy' hw; [|symmetry]; apply: hw.
    case: ltrgtP=> // hyy' _; move: (hp' y).
    by rewrite rootE py0 eqxx inE /= (intP hy) hyy'; move/(_ isT).
  move=> c p0 ->; case: maxrP=> hab; last by rewrite int_gte // ltrW.
  by move=> hpz _ py0 hy; move/hpz:hy; rewrite rootE py0 eqxx.
case: next_rootP=> //; first by move->; rewrite eqxx.
  by move=> y np0 py0 hy _ c _ _;  move/(_ _ hy); rewrite rootE py0 eqxx.
by move=> c _ -> _ c' _ ->.
Qed.

Definition prev_root (p : {poly R}) a x := if p == 0 then x else last (minr a x) (roots p a x).

Lemma prev_root0 : forall a b, prev_root 0 a b = b.
Proof. by move=> *; rewrite /prev_root eqxx. Qed.

CoInductive prev_root_spec (p : {poly R}) a x : bool -> R -> Type :=
| PrevRootSpec0 of p = 0 : prev_root_spec p a x true x
| PrevRootSpecRoot y of p != 0 & p.[y] = 0 & y \in`]a, x[
  & {in `]y, x[, forall z, ~~(root p z)} : prev_root_spec p a x true y
| PrevRootSpecNoRoot c of p != 0 & c = minr a x
 & {in `]a, x[, forall z, ~~(root p z)} : prev_root_spec p a x (p.[c] == 0) c.

Lemma prev_rootP : forall (p : {poly R}) a b, prev_root_spec p a b (p.[prev_root p a b] == 0) (prev_root p a b).
Proof.
move=> p a b; rewrite /prev_root /=.
move hs: (roots _ _ _)=> s.
case: (lastP s) hs=> {s} [|s x] hs /=.
  case: (altP (p =P 0))=> p0.
    by rewrite {2}p0 hornerC eqxx; constructor; rewrite p0.
  by constructor=> // y hy; apply: (roots_nil p0 hs).
rewrite last_rcons; move/eqP: hs.
rewrite roots_rcons; case/and5P=> p0 hx; move/eqP=> rap rpx rx.
rewrite (negPf p0) (rootPt rpx); constructor=> //; first by move/eqP: rpx.
by move=> y hy /=; move/(roots_nil p0): (rap); apply.
Qed.

Lemma prev_root_in : forall p a b, prev_root p a b \in `[minr a b, b].
Proof.
move=> p a b; case: prev_rootP=> [p0|y np0 py0 hy _|c np0 hc _].
* by rewrite bound_in_int /= ler_minl lerr orbT.
* by apply: subintP hy=> /=; rewrite ler_minl !lerr.
* by rewrite hc bound_in_int /= ler_minl lerr orbT.
Qed.

Lemma prev_noroot : forall p a b, {in `](prev_root p a b), b[, noroot p}.
Proof.
move=> p a b z; case: prev_rootP; first by rewrite int_xx.
  by move=> y np0 py0 hy hp hz; rewrite (negPf (hp _ _)).
move=> c np0 ->; case: minrP=> hab; last by rewrite int_xx.
by move=> hp hz; rewrite (negPf (hp _ _)).
Qed.

Lemma prev_root_lt : forall p a b, a < b -> p != 0 -> prev_root p a b < b.
Proof.
move=> p a b ab np0; case: prev_rootP=> [p0|y _ py0 hy _|c _ -> _].
* by rewrite p0 eqxx in np0.
* by rewrite (intP hy).
* by rewrite minr_l // ltrW.
Qed.

Lemma is_prev_root : forall p a b x, prev_root_spec p a b (root p x) x -> x = prev_root p a b.
Proof.
move=> p a b x []; first by move->; rewrite /prev_root eqxx.
  move=> y; case: prev_rootP; first by move->; rewrite eqxx.
  move=> y' np0 py'0 hy' hp' _ py0 hy hp.
    wlog: y y' hy' hy hp' hp py0 py'0 / y <= y'.
      by case/orP: (ler_total y y')=> lyy' hw; [|symmetry]; apply: hw.
    case: ltrgtP=> // hyy' _; move/implyP: (hp y').
    by rewrite rootE py'0 eqxx inE /= (intP hy') hyy'.
  by move=> c _ _ hpz _ py0 hy; move/hpz:hy; rewrite rootE py0 eqxx.
case: prev_rootP=> //; first by move->; rewrite eqxx.
  move=> y ? py0 hy _ c _ ->; case: minrP hy=> hab; last first.
    by rewrite int_gte // ltrW.
  by move=> hy; move/(_ _ hy); rewrite rootE py0 eqxx.
by move=> c  _ -> _ c' _ ->.
Qed.

Definition neighpr p a b := `]a, (next_root p a b)[.

Definition neighpl p a b := `](prev_root p a b), b[.

Lemma neighpl_root : forall p a x,  {in neighpl p a x, noroot p}.
Proof. exact: prev_noroot. Qed.

Lemma sgr_neighplN : forall p a x, ~~root p x ->
  {in neighpl p a x, forall y, (sgr p.[y] = sgr p.[x])}.
Proof.
rewrite /neighpl=> p a x nrpx /= y hy.
apply: (@polyrN0_int `[y, x]); do ?by rewrite bound_in_int /= (intP hy).
move=> z; rewrite (@int_splitU _ x false) ?int_xx /=; last first. (* Todo : Lemma int_splitP *)
  by rewrite bound_in_int /= (intP hy).
rewrite orbC => /predU1P[-> // | hz].
rewrite (@prev_noroot _ a x) //.
by apply: subintPl hz; rewrite /= (intP hy).
Qed.

Lemma sgr_neighpl_same : forall p a x,
  {in neighpl p a x &, forall y z, (sgr p.[y] = sgr p.[z])}.
Proof.
by rewrite /neighpl=> p x b y z *; apply: (polyrN0_int (@prev_noroot p x b)).
Qed.

Lemma neighpr_root : forall p x b, {in neighpr p x b, noroot p}.
Proof. exact: next_noroot. Qed.

Lemma sgr_neighprN : forall p x b, p.[x] != 0 ->
  {in neighpr p x b, forall y, (sgr p.[y] = sgr p.[x])}.
Proof.
rewrite /neighpr=> p x b nrpx /= y hy; symmetry.
apply: (@polyrN0_int `[x, y]); do ?by rewrite bound_in_int /= (intP hy).
move=> z; rewrite (@int_splitU _ x true) ?int_xx /=; last first. (* Todo : Lemma int_splitP *)
  by rewrite bound_in_int /= (intP hy).
case/orP=> [|hz]; first by rewrite inE /=; move/eqP->.
rewrite (@next_noroot _ x b) //.
by apply: subintPr hz; rewrite /= (intP hy).
Qed.

Lemma sgr_neighpr_same : forall p x b,
  {in neighpr p x b &, forall y z, (sgr p.[y] = sgr p.[z])}.
Proof.
by rewrite /neighpl=> p x b y z *; apply: (polyrN0_int (@next_noroot p x b)).
Qed.

Lemma uniq_roots : forall a b p, uniq (roots p a b).
Proof.
move=> a b p; case p0: (p == 0); first by rewrite (eqP p0) roots0.
by apply: (@sorted_uniq _ >%R); [exact: ltr_trans | exact: ltrr|].
Qed.

Hint Resolve uniq_roots.

Lemma in_roots : forall p a b, forall x : R,
  (x \in roots p a b) = [&& root p x, x \in `]a, b[ & p != 0].
Proof.
move=> p a b x; case: rootsP=> //=; first by rewrite in_nil !andbF.
by move=> p0 hr sr; rewrite andbT -hr andbC.
Qed.

(* Todo : move to polyorder => need char 0 *)
Lemma gdcop_eq0 : forall p q, (gdcop p q == 0) = (q == 0) && (p != 0).
Proof.
move=> p q; case: (eqVneq q 0) => [-> | q0].
  rewrite gdcop0 /= eqxx /=.
  by case: (eqVneq p 0) => [-> | pn0]; rewrite ?(negPf pn0) eqxx  ?oner_eq0.
rewrite /gdcop; move: {-1}(size q) (leqnn (size q))=> k hk.
case: (eqVneq p 0) => [-> | p0].
  rewrite eqxx andbF; apply: negPf.
  elim: k q q0 {hk} => [|k ihk] q q0 /=; first by rewrite eqxx oner_eq0.
  case: ifP=> _ //.
  apply: ihk; rewrite gcdp0 divpp  ?q0 // polyC_eq0; exact: lc_expn_scalp_neq0.
rewrite p0 (negPf q0) /=; apply: negPf. 
elim: k q q0 hk => [|k ihk] /= q q0 hk.
  by move: hk q0; rewrite leqn0 size_poly_eq0; move->.
case: ifP=> cpq; first by rewrite (negPf q0).
apply: ihk.
  rewrite divpN0; last by rewrite gcdp_eq0 negb_and q0.
  by rewrite dvdp_leq // dvdp_gcdl.
rewrite -ltnS; apply: leq_trans hk; move: (dvdp_gcdl q p); rewrite dvdp_eq. 
move/eqP=> eqq; move/(f_equal (fun x : {poly R} => size x)): (eqq).
rewrite size_scaler; last exact: lc_expn_scalp_neq0.
have gcdn0 : gcdp q p != 0 by rewrite gcdp_eq0 negb_and q0.
have qqn0 : q %/ gcdp q p != 0.
   apply: contraTneq q0; rewrite negbK => e. 
   move: (scaler_eq0 (lead_coef (gcdp q p) ^+ scalp q (gcdp q p)) q). 
   by rewrite (negPf (lc_expn_scalp_neq0 _ _)) /=; move<-; rewrite eqq e mul0r.
move->; rewrite size_mul_id //; case sgcd: (size (gcdp q p)) => [|n].
  by move/eqP: sgcd gcdn0; rewrite size_poly_eq0; move->.
case: n sgcd => [|n]; first by move/eqP; rewrite size_poly_eq1 gcdp_eqp1 cpq.
by rewrite addnS /= -{1}[size (_ %/ _)]addn0 ltn_add2l.
Qed.

Lemma roots_mul : forall a b, a < b -> forall p q,
  p != 0 -> q != 0 -> perm_eq (roots (p*q) a b)
  (roots p a b ++ roots ((gdcop p q)) a b).
Proof.
move=> a b hab p q np0 nq0.
apply: uniq_perm_eq; first exact: uniq_roots.
  rewrite cat_uniq ?uniq_roots andbT /=; apply/hasPn=> x /=.
  move/root_roots; rewrite root_gdco //; case/andP=> _.
  by rewrite in_roots !negb_and=> ->.
move=> x; rewrite mem_cat !in_roots root_gdco //.
rewrite root_mul mulf_eq0 gdcop_eq0 negb_and.
case: (x \in `]_, _[); last by rewrite !andbF.
by rewrite negb_or !np0 !nq0 !andbT /=; do 2?case: root=> //=.
Qed.

Lemma roots_mul_coprime : forall a b, a < b -> forall p q,
  p != 0 -> q != 0 -> coprimep p q ->
  perm_eq (roots (p * q) a b)
  (roots p a b ++ roots q a b).
Proof.
move=> a b hab p q np0 nq0 cpq.
rewrite (perm_eq_trans (roots_mul hab np0 nq0)) //.
suff ->: roots (gdcop p q) a b = roots q a b by apply: perm_eq_refl.
case: gdcopP=> r rq hrp; move/(_ q (dvdpp _)).
rewrite coprimep_sym; move/(_ cpq)=> qr.
have erq : r %= q by rewrite /eqp rq qr.
(* Todo : relate eqp with roots *)
apply/roots_eq=> // [|x hx]; last exact: eqp_root.
by rewrite -size_poly_eq0 (eqp_size erq) size_poly_eq0.
Qed.


Lemma next_root_mul : forall a b (p q : {poly R}),
  next_root (p * q) a b = minr (next_root p a b) (next_root q a b).
Proof.
move=> a b p q; symmetry; apply: is_next_root.
wlog: p q / next_root p a b <= next_root q a b.
  case: minrP=> hpq; first by move/(_ _ _ hpq); case: minrP hpq.
  by move/(_ _ _ (ltrW hpq)); rewrite mulrC minrC; case: minrP hpq.
case: minrP=> //; case: next_rootP=> [|y np0 py0 hy|c np0 ->] hp hpq _.
* by rewrite hp mul0r root0; constructor.
* rewrite root_mul; move/rootP:(py0)->; constructor=> //.
  - by rewrite mulf_neq0 //; case: next_rootP hpq; rewrite // (intP hy).
  - by rewrite horner_mul py0 mul0r.
  - move=> z hz /=; rewrite root_mul negb_or ?hp //.
    by rewrite (@next_noroot _ a b) //; apply: subintPr hz.
* case: (altP (q =P 0))=> q0.
    move: hpq; rewrite q0 mulr0 root0 next_root0 ler_maxl lerr andbT.
    by move=> hba; rewrite maxr_r //; constructor.
  constructor=> //; first by rewrite mulf_neq0.
  move=> z hz /=; rewrite root_mul negb_or ?hp //.
  rewrite (@next_noroot _ a b) //; apply: subintPr hz=> /=.
  by move: hpq; rewrite ler_maxl; case/andP.
Qed.

Lemma neighpr_mul : forall a b p q,
  (neighpr (p * q) a b) =i [predI (neighpr p a b) & (neighpr q a b)].
Proof.
move=> a b p q x; rewrite inE /= !inE /= next_root_mul.
by case: (a < x); rewrite // ltr_minr.
Qed.

Lemma prev_root_mul : forall a b (p q : {poly R}),
  prev_root (p * q) a b = maxr (prev_root p a b) (prev_root q a b).
Proof.
move=> a b p q; symmetry; apply: is_prev_root.
wlog: p q / prev_root p a b >= prev_root q a b.
  case: maxrP=> hpq; first by move/(_ _ _ hpq); case: maxrP hpq.
  by move/(_ _ _ (ltrW hpq)); rewrite mulrC maxrC; case: maxrP hpq.
case: maxrP=> //; case: (@prev_rootP p)=> [|y np0 py0 hy|c np0 ->] hp hpq _.
* by rewrite hp mul0r root0; constructor.
* rewrite root_mul; move/rootP:(py0)->; constructor=> //.
  - by rewrite mulf_neq0 //; case: prev_rootP hpq; rewrite // (intP hy).
  - by rewrite horner_mul py0 mul0r.
  - move=> z hz /=; rewrite root_mul negb_or ?hp //.
    by rewrite (@prev_noroot _ a b) //; apply: subintPl hz.
* case: (altP (q =P 0))=> q0.
    move: hpq; rewrite q0 mulr0 root0 prev_root0 ler_minr lerr andbT.
    by move=> hba; rewrite minr_r //; constructor.
  constructor=> //; first by rewrite mulf_neq0.
  move=> z hz /=; rewrite root_mul negb_or ?hp //.
  rewrite (@prev_noroot _ a b) //; apply: subintPl hz=> /=.
  by move: hpq; rewrite ler_minr; case/andP.
Qed.

Lemma neighpl_mul : forall a b p q,
  (neighpl (p * q) a b) =i [predI (neighpl p a b) & (neighpl q a b)].
Proof.
move=> a b p q x; rewrite !inE /= prev_root_mul.
by case: (x < b); rewrite // ltr_maxl !(andbT, andbF).
Qed.

Lemma neighpr_wit : forall p x b, x < b -> p != 0 -> {y | y \in neighpr p x b}.
Proof.
move=> p x b xb; exists (mid x (next_root p x b)).
by rewrite mid_in_int //= next_root_gt.
Qed.

Lemma neighpl_wit : forall p a x, a < x -> p != 0 -> {y | y \in neighpl p a x}.
Proof.
move=> p a x xb; exists (mid (prev_root p a x) x).
by rewrite mid_in_int //= prev_root_lt.
Qed.

End NeighborHood.

Section SignRight.

Definition sgp_right (p : {poly R}) x :=
  let fix aux (p : {poly R}) n :=
  if n is n'.+1
    then if ~~ root p x
      then sgr p.[x]
      else aux p^`() n'
    else 0
      in aux p (size p).

Lemma sgp_right0 : forall x, sgp_right 0 x = 0.
Proof. by move=> x; rewrite /sgp_right size_poly0. Qed.

Lemma sgr_neighpr : forall b p x,
  {in neighpr p x b, forall y, (sgr p.[y] = sgp_right p x)}.
Proof.
move=> b p x.
elim: (size p) {-2}p (leqnn (size p))=> [|n ihn] {p} p.
  rewrite leqn0 size_poly_eq0 /neighpr; move/eqP=> -> /=.
  by move=>y; rewrite next_root0 int_xx.
rewrite leq_eqVlt ltnS; case/orP; last exact: ihn.
move/eqP=> sp; rewrite /sgp_right sp /=.
case px0: root=> /=; last first.
  move=> y; rewrite/neighpr => hy /=; symmetry.
  apply: (@polyrN0_int `[x, y]); do ?by rewrite bound_in_int /= (intP hy).
  move=> z; rewrite (@int_splitU _ x true) ?bound_in_int /= ?(intP hy) //.
  rewrite int_xx /=; case/predU1P=> hz; first by rewrite hz px0.
  rewrite (@next_noroot p x b) //.
  by apply: subintPr hz=> /=; rewrite (intP hy).
have <-: size p^`() = n by rewrite size_deriv sp.
rewrite -/(sgp_right p^`() x).
move=> y; rewrite /neighpr=> hy /=.
case: (@neighpr_wit (p * p^`()) x b)=> [||m hm].
* case: next_rootP hy; first by rewrite int_xx.
    by move=> ? ? ?; move/intP->.
  by move=> c p0 -> _; case: maxrP=> _; rewrite ?int_xx //; move/intP->.
* rewrite mulf_neq0 //.
    by move/eqP:sp; apply: contraTneq=> ->; rewrite size_poly0.
  (* Todo : a lemma for this *)
  move: (size_deriv p); rewrite sp /=; move/eqP; apply: contraTneq=> ->.
  rewrite size_poly0; apply: contraTneq px0=> hn; rewrite -hn in sp.
  by move/eqP: sp; case/size1P=> c nc0 ->; rewrite rootC.
* move: hm; rewrite neighpr_mul /neighpr inE /=; case/andP=> hmp hmp'.
  rewrite (polyrN0_int _ hmp) //; last exact: next_noroot.
  rewrite (@ders0r p x m (mid x m)) ?(eqP px0) ?mid_in_int ?bound_in_int //;
    rewrite /= ?(intP hmp) //; last first.
    move=> u hu /=; rewrite (@next_noroot _ x b) //.
    by apply: subintPr hu; rewrite /= (intP hmp').
  rewrite ihn ?size_deriv ?sp /neighpr //.
  by rewrite (subintP _ (@mid_in_int _ false false _ _ _)) //= ?lerr (intP hmp').
Qed.

Lemma sgr_neighpl : forall a p x,
  {in neighpl p a x, forall y,
    (sgr p.[y] = (-1) ^+ (odd (\mu_x p)) * sgp_right p x)
  }.
Proof.
move=> a p x.
elim: (size p) {-2}p (leqnn (size p))=> [|n ihn] {p} p.
  rewrite leqn0 size_poly_eq0 /neighpl; move/eqP=> -> /=.
  by move=>y; rewrite prev_root0 int_xx.
rewrite leq_eqVlt ltnS; case/orP; last exact: ihn.
move/eqP=> sp; rewrite /sgp_right sp /=.
case px0: root=> /=; last first.
  move=> y; rewrite/neighpl => hy /=; symmetry.
  move: (negbT px0); rewrite -mu_gt0; last first.
    by apply: contraFN px0; move/eqP->; rewrite rootC.
  rewrite -leqNgt leqn0; move/eqP=> -> /=; rewrite expr0 mul1r.
  symmetry; apply: (@polyrN0_int `[y, x]);
    do ?by rewrite bound_in_int /= (intP hy).
  move=> z; rewrite (@int_splitU _ x false) ?bound_in_int /= ?(intP hy) //.
  rewrite int_xx /= orbC; case/predU1P=> hz; first by rewrite hz px0.
  rewrite (@prev_noroot p a x) //.
  by apply: subintPl hz=> /=; rewrite (intP hy).
have <-: size p^`() = n by rewrite size_deriv sp.
rewrite -/(sgp_right p^`() x).
move=> y; rewrite /neighpl=> hy /=.
case: (@neighpl_wit (p * p^`()) a x)=> [||m hm].
* case: prev_rootP hy; first by rewrite int_xx.
    by move=> ? ? ?; move/intP->.
  by move=> c p0 -> _; case: minrP=> _; rewrite ?int_xx //; move/intP->.
* rewrite mulf_neq0 //.
    by move/eqP:sp; apply: contraTneq=> ->; rewrite size_poly0.
  (* Todo : a lemma for this *)
  move: (size_deriv p); rewrite sp /=; move/eqP; apply: contraTneq=> ->.
  rewrite size_poly0; apply: contraTneq px0=> hn; rewrite -hn in sp.
  by move/eqP: sp; case/size1P=> c nc0 ->; rewrite rootC.
* move: hm; rewrite neighpl_mul /neighpl inE /=; case/andP=> hmp hmp'.
  rewrite (polyrN0_int _ hmp) //; last exact: prev_noroot.
  rewrite (@ders0l p m x (mid m x)) ?(eqP px0) ?mid_in_int ?bound_in_int //;
    rewrite /= ?(intP hmp) //; last first.
    move=> u hu /=; rewrite (@prev_noroot _ a x) //.
    by apply: subintPl hu; rewrite /= (intP hmp').
  rewrite ihn ?size_deriv ?sp /neighpl //; last first.
    by rewrite (subintP _ (@mid_in_int _ false false _ _ _)) //= ?lerr (intP hmp').
  rewrite mu_deriv // odd_sub ?mu_gt0 //=; last by rewrite -size_poly_eq0 sp.
  by rewrite signr_addb /= mulrN1 mulNr opprK.
Qed.

Lemma sgp_right_deriv : forall (p : {poly R}) x, root p x ->
  sgp_right p x = sgp_right (p^`()) x.
Proof.
move=> p; elim: (size p) {-2}p (erefl (size p)) => {p} [p|sp hp p hsp x].
  by move/eqP; rewrite size_poly_eq0; move/eqP=> -> x _; rewrite derivC.
by rewrite /sgp_right size_deriv hsp /= => ->.
Qed.

Lemma sgp_rightNroot : forall (p : {poly R}) x,
  ~~ root p x -> sgp_right p x = sgr p.[x].
Proof.
move=> p x nrpx; rewrite /sgp_right; case hsp: (size _)=> [|sp].
  by move/eqP:hsp; rewrite size_poly_eq0; move/eqP->; rewrite hornerC sgr0.
by rewrite nrpx.
Qed.

Lemma sgp_right_mul : forall p q x,
  sgp_right (p * q) x = sgp_right p x * sgp_right q x.
Proof.
move=> p q x.
case: (altP (q =P 0))=> q0; first by rewrite q0 /sgp_right !(size_poly0,mulr0).
case: (altP (p =P 0))=> p0; first by rewrite p0 /sgp_right !(size_poly0,mul0r).
case: (@neighpr_wit (p * q) x (1 + x))=> [||m hpq]; do ?by rewrite mulf_neq0.
  by rewrite ltr_spaddl ?ltr01.
rewrite -(@sgr_neighpr (1 + x) _ _ m) //.
move: hpq; rewrite neighpr_mul inE /=; case/andP=> hp hq.
by rewrite horner_mul sgrM !(@sgr_neighpr (1 + x) _ x) /neighpr.
Qed.

Lemma sgp_right_scale c p x : sgp_right (c *: p) x = sgr c * sgp_right p x.
Proof.
case c0: (c == 0); first by rewrite (eqP c0) scale0r sgr0 mul0r sgp_right0.
by rewrite -mul_polyC sgp_right_mul sgp_rightNroot ?hornerC ?rootC ?c0.
Qed.

Lemma sgp_right_square : forall p x, p != 0 -> sgp_right p x * sgp_right p x = 1.
Proof.
move=> p x np0; case: (@neighpr_wit p x (1 + x))=> [||m hpq] //.
  by rewrite ltr_spaddl ?ltr01.
rewrite -(@sgr_neighpr (1 + x) _ _ m) //.
by rewrite mulr_sg (@next_noroot _ x (1 + x)).
Qed.

Lemma sgp_right_rec p x : sgp_right p x =
  if p == 0 then 0 else
    if ~~ root p x then sgr p.[x]
      else sgp_right p^`() x.
Proof.
rewrite /sgp_right; case hs: size=> [|s]; rewrite -size_poly_eq0 hs //=.
by rewrite size_deriv hs.
Qed.

Lemma sgp_right_addp0 : forall (p q : {poly R}) x, q != 0 ->
  (\mu_x p > \mu_x q)%N -> sgp_right (p + q) x = sgp_right q x.
Proof.
move=> p q x nq0; move hm: (\mu_x q)=> m.
elim: m p q nq0 hm => [|mq ihmq] p q nq0 hmq; case hmp: (\mu_x p)=> // [mp];
  do[
    rewrite ltnS=> hm;
      rewrite sgp_right_rec {1}addrC;
        rewrite GRing.Theory.addr_eq0]. (* Todo : fix this ! *)
  case: (altP (_ =P _))=> hqp.
    move: (nq0); rewrite {1}hqp oppr_eq0=> np0.
    rewrite sgp_right_rec (negPf nq0) -mu_gt0 // hmq /=.
    apply/eqP; rewrite eq_sym hqp horner_opp sgrN.
    by rewrite oppr_eq0 sgr_eq0 -[_ == _]mu_gt0 ?hmp.
  rewrite rootE horner_add.
  have ->: p.[x] = 0.
    apply/eqP; rewrite -[_ == _]mu_gt0 ?hmp //.
    by move/eqP: hmp; apply: contraTneq=> ->; rewrite mu0.
  symmetry; rewrite sgp_right_rec (negPf nq0) add0r.
  by rewrite -/(root _ _) -mu_gt0 // hmq.
case: (altP (_ =P _))=> hqp.
  by move: hm; rewrite -ltnS -hmq -hmp hqp mu_opp ltnn.
have px0: p.[x] = 0.
  apply/rootP; rewrite -mu_gt0 ?hmp //.
  by move/eqP: hmp; apply: contraTneq=> ->; rewrite mu0.
have qx0: q.[x] = 0 by apply/rootP; rewrite -mu_gt0 ?hmq //.
rewrite rootE horner_add px0 qx0 add0r eqxx /=; symmetry.
rewrite sgp_right_rec rootE (negPf nq0) qx0 eqxx /=.
rewrite derivD ihmq // ?mu_deriv ?rootE ?px0 ?qx0 ?hmp ?hmq ?subn1 //.
apply: contra nq0; rewrite -size_poly_eq0 size_deriv.
case hsq: size=> [|sq] /=.
  by move/eqP: hsq; rewrite size_poly_eq0.
move/eqP=> sq0; move/eqP: hsq qx0; rewrite sq0; case/size1P=> c c0 ->.
by rewrite hornerC; move/eqP; rewrite (negPf c0).
Qed.

End SignRight.

End PolyRCF.
