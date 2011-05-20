(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
Require Import ssralg poly orderedalg zmodp polydiv zint orderedzint interval.

(* Reserved Notation "a ^`"(at level 3, format "a ^`"). *)
(* Reserved Notation "a ^`( n )" (at level 3, format "a ^`( n )"). *)
(* Reserved Notation "a ^`N( n )" (at level 3, format "a ^`N( n )"). *)

Import GRing.Theory.
Import OrderedRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

Section PolyReal.

Variable R : oFieldType.

Implicit Types a b c : R.
Implicit Types x y z t : R.
Implicit Types p q r : {poly R}.

(* assia : strange : why this instead of a real closed field ? *)

Hypothesis ivt : forall (p : {poly R}) (a b : R),
  a <= b -> 0 \in `[p.[a], p.[b]] -> { x : R | x \in `[a, b] & root p x }.

(* assia : root should be a notation or at least used only when a *)
(*boolean is needed *)

Lemma polyrN0_intcc : forall p a b,
  (forall x, x \in `[a, b] ->  p.[x] != 0) ->
  forall x, x \in `[a, b] -> sgr p.[x] = sgr p.[a].
Proof.
move=> p a b np0 x laxb; move:(np0 _ laxb).
case: (ltrgtP p.[x] 0)=> [spx npx0|spx npx0|]; last by move->.
  case: (ltrP p.[a] 0)=> spa; first by rewrite !ltr0_sg.
  case/andP:(laxb)=>lax lxb; case:(@ivt (-p) a x)=> //.
    by rewrite !horner_opp inE /= !oppr_cp0/= spa ltrE.
  move=> y ayx; rewrite root_opp rootE (negPf (np0 _ _)) //.
  by apply: subintPr ayx; rewrite /= (intP laxb).
rewrite gtr0_sg //; case: sgrP=> // [|ha].
  by move/eqP; rewrite (negPf (np0 a _)) // bound_in_int //= (intP laxb).
case: (@ivt p a x); rewrite ?(intP laxb) ?inE ?ltrW //.
move=> y hy; rewrite rootE (negPf (np0 y _)) //.
by apply: subintPr hy=> /=; rewrite (intP laxb).
Qed.

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

Lemma div_factor_spec :forall p x,
  p = (p %/ ('X - x%:P)) * ('X - x%:P) + (p %% ('X - x%:P)).
Proof.
move=> p x; rewrite {1}(@divfp_spec p ('X - x%:P)).
by rewrite lead_coef_factor exp1rn invr1 !scale1r.
Qed.

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
case: (@div_factor_spec p a)=> ->.
rewrite [_ %% _]size1_polyC; last first.
  by rewrite -ltnS (leq_trans (modp_spec _ _)) ?factor_eq0 ?size_factor.
case: (@maxdivp _ (p %/ ('X - a%:P)) a)=> [|q hqa [n' hp]].
  by rewrite divfp_eq0 ?size_factor ?factor_eq0 // -leqNgt.
rewrite hp -mulrA -exprSr; apply: Pq=> //; apply: ihn.
rewrite (@leq_trans (size (q * ('X - a%:P) ^+ n'))) //.
  rewrite size_mul_id ?expf_eq0 ?factor_eq0 ?andbF //; last first.
    by apply: contra hqa; move/eqP->; rewrite root0.
  by rewrite size_factor_exp addnS leq_addr.
by rewrite -hp size_divp ?factor_eq0 ?size_factor // leq_sub_add.
Qed.

Lemma nth_root : forall x n, x > 0 -> { y | y > 0 & y ^+ (n.+1) = x }.
Proof.
move=> x n l0x.
case: (ltrgtP x 1)=> hx; last by exists 1; rewrite ?hx ?lter01// exp1rn.
  case: (@ivt ('X ^+ n.+1 - x%:P) 0 1); first by rewrite ler01.
    rewrite ?(horner_lin,horner_exp) ?inE.
    by rewrite exprS mul0r sub0r exp1rn oppr_cp0 subr_gte0/= ltrE// ltrE.
  move=> y; case/andP=> [l0y ly1]; rewrite rootE ?(horner_lin,horner_exp).
  rewrite subr_eq0; move/eqP=> hyx; exists y=> //; rewrite ltr_neqAle l0y.
  rewrite eq_sym andbT; apply/eqP=> y0; move: hyx; rewrite y0.
  by rewrite exprS mul0r=> x0; move: l0x; rewrite -x0 ltrr.
case: (@ivt ('X ^+ n.+1 - x%:P) 0 x); first by rewrite ltrE.
  rewrite ?(horner_lin,horner_exp) exprS mul0r sub0r ?inE.
  by rewrite oppr_cp0 (ltrW l0x) subr_ge0 ler_eexprS// ltrE.
move=> y; case/andP=> l0y lyx; rewrite rootE ?(horner_lin,horner_exp).
rewrite subr_eq0; move/eqP=> hyx; exists y=> //; rewrite ltr_neqAle l0y.
rewrite eq_sym andbT; apply/eqP=> y0; move: hyx; rewrite y0.
by rewrite exprS mul0r=> x0; move: l0x; rewrite -x0 ltrr.
Qed.

Lemma poly_cont : forall x p e, e > 0 -> exists2 d,
  d > 0 & forall y, `|y - x| < d -> `|p.[y] - p.[x]| < e.
Proof.
move=> x; elim/(@poly_div_factor x).
  move=> e ep; exists 1; rewrite ?ltr01// => y hy.
  by rewrite !hornerC subrr absr0.
move=> p n k pxn0 Pp e ep.
case: (Pp (`|p.[x]|/2%:~R)).
  by rewrite mulr_gte0_cp0// ?invr_gte0//= ?ltr0Sn// absrE.
move=> d' d'p He'.
case: (@nth_root (e / ((3%:~R/2%:~R) * `|p.[x]|)) n).
  by rewrite ltr_pdivl_mulr ?mul0r ?mulr_gt0 ?invr_gt0 ?absrE ?ltr0Sn.
move=> d dp rootd.
exists (minr d d'); first by rewrite ltr_minr dp.
move=> y; rewrite ltr_minr; case/andP=> hxye hxye'.
rewrite !(horner_lin, horner_exp) subrr [0 ^+ _]exprS mul0r mulr0 add0r addrK.
rewrite absr_mul (@ler_lt_trans _  (`|p.[y]| * d ^+ n.+1)) //.
  by rewrite ler_pmul2rW ?absrE // absr_exp ler_pexp2 ?absrE 1?ltrE.
rewrite rootd mulrCA ltr_ipmulr //.
rewrite ltr_pdivr_mulr ?mul1r ?mulr_gt0 ?invr_gt0 ?ltr0Sn ?absrE //.
rewrite mulr_addl mulr_addl divff; last by rewrite -mulr2n natmulP mulSn1r_eq0.
rewrite !mul1r mulrC -ltr_subl_addl.
by rewrite (ler_lt_trans _ (He' y _)) // subr_abs_le_sub.
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

Definition has_lt_roots_in p n a b :=
  forall (rs : seq R), size rs = n -> uniq rs ->
    {subset [predI root p & `]a, b[] <= rs} -> p = 0.

Lemma poly_ltsp_roots : forall p (rs : seq R),
  (size rs >= size p)%N -> uniq rs -> all (root p) rs -> p = 0.
Proof.
move=> p rs hrs urs rrs; apply/eqP; apply: contraLR hrs=> np0.
by rewrite -ltnNge; apply: max_poly_roots.
Qed.

(* assia : why == *)
Lemma ivt_sign : forall (p : {poly R}) (a b : R),
  a <= b -> sgr p.[a] * sgr p.[b] == -1 -> { x : R | x \in `]a, b[ & root p x}.
Proof.
move=> p a b hab; have ->: -1 = sgr(-1 : R) by rewrite sgr_opp sgr1.
rewrite muls_eqA sgr_opp sgr1// mulrN1; case/andP; move/eqP=> hpapb pb0.
case: (@ivt (((sgr p.[b])%:~R) *: p) a b)=> //.
   rewrite -{1}hpapb !horner_lin mulrNz mulNr !mulrzl.
   by rewrite ?inE -!absr_dec oppr_cp0/= !absrE.
move=> c; case/andP=> lac lcb.
rewrite rootE !horner_lin mulf_eq0 mul1rz_eq0 (negPf pb0) /= => pc0.
exists c=> //; rewrite inE /= !ltr_neqAle lac lcb !andbT.
apply/andP; split.
  move: pb0; rewrite -hpapb eqr_oppC oppr0; apply: contra.
  by move/eqP->; rewrite (eqP pc0) sgr0.
by move: pb0; apply: contra; move/eqP<-; rewrite (eqP pc0) sgr0.
Qed.

Lemma rolle_weak : forall a b p, a < b ->
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
  by rewrite !expf_eq0 !subr_eq0 !(ltrNW lab) !andbF !orbF !rootE=> ->.
move=> -> _ p0 p'a0 qb0; case: (sgrP (q.[a] * q.[b])); first 2 last.
- move=> sqasb; case: (@ivt_sign q a b)=> //; first exact: ltrW.
    by rewrite -sgr_mul sgr_cp0 sqasb.
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
  case: (@ivt_sign (((sgr q.[b])%:~R) *: r) a b); first exact: ltrW.
    rewrite !horner_scaler !mulrzl !sgr_smul mulrCA -!mulrA mulss qb0 mulr1.
    rewrite /r !(subrr, mul0r, mulr0, addr0, add0r, hornerC, horner_factor,
      horner_add, horner_opp, horner_mul, horner_mulrn).
    rewrite [_ * _%:R]mulrC -!mulrA !natmulP !mulrzl !sgr_mulrz -sgr_mul.
    rewrite mulrAC mulrA -mulrA sgr_mul -oppr_sub mulNr sgr_opp sgr_mul mulss.
    by rewrite subr_eq0 [a == b]ltrWN // mulN1r eqr_opp sgr_cp0.
move=> c lacb; rewrite rootE horner_scaler mulf_eq0.
rewrite mul1rz_eq0 sgr_cp0 (rootPf qb0) orFb=> rc0.
by exists c=> //; rewrite !horner_mul !mulf_eq0 rc0.
Qed.

Lemma rolle : forall a b p, a < b ->
  p.[a] = 0 -> p.[b] = 0 ->
  { c | c \in `]a, b[ & ((p^`()).[c] = 0)}.
Proof.
move=> a b p lab pa0 pb0.
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

Lemma mvt : forall a b p, a < b ->
  { c | c \in `]a, b[ & p.[b] - p.[a] = (p^`()).[c] * (b - a)}.
Proof.
move=> a b p lab.
pose q := (p.[b] - p.[a])%:P * ('X - a%:P) - (b - a)%:P * (p - p.[a]%:P).
case: (@rolle a b q)=> //.
* by rewrite /q !horner_lin !(subrr, mulr0).
* by rewrite /q !horner_lin ?(subrr, mulr0) mulrC subrr.
* move=> c lacb q'x0; exists c=> //.
  move: q'x0; rewrite /q !derivE !(mul0r,add0r,subr0,mulr1).
  by move/eqP; rewrite !horner_lin mulrC subr_eq0; move/eqP.
Qed.

Lemma deriv_sign : forall a b p,
  (forall x, x \in `]a, b[ -> (p^`()).[x] >= 0)
  -> (forall x y, (x \in `]a, b[) && (y \in `]a, b[)
    ->  x < y -> p.[x] <= p.[y] ).
Proof.
move=> a b p Pab x y; case/andP=> hx hy xy.
rewrite -subr_gte0; case: (@mvt x y p)=> //.
move=> c hc ->; rewrite mulr_gte0_cp0//= ?Pab //.
  by apply: subintP hc; rewrite //= ?(intP hx) ?(intP hy).
by rewrite subr_gte0 /= ltrE.
Qed.

End PolyReal.



