Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq tuple.
Require Import fintype finfun bigop ssralg poly polydiv.
Require Import zmodp vector algebra fieldext finalg finfield.
Require Import fingroup perm finset matrix mxalgebra mxpoly.
Require Import div cyclic prime binomial choice generic_quotient.

(******************************************************************************)
(* This file is supposed to provide theory of separable and inseparable field *)
(* extensions, however it is currently half about general field extentions    *)
(* and this half should perhaps be move elsewhere.                            *)
(*                                                                            *)
(*  separablePolynomial p == p has no repeated roots in any field extension   *)
(*   separableElement K x == the minimal polynomial for x is separable        *)
(*          separable K E == every member of E is separable over K            *)
(* separableGenerator K E == some x \in E that generates the largest possible *)
(*                           subfield K[x] that is separable over K           *)
(* purelyInseparableElement K x == there is n \in [char L].-nat such that     *)
(*                                 x ^+ n \in K                               *)
(*  purelyInseparable K E == every member of E is purely inseparable over K   *)
(*                                                                            *)
(*  Derivations are only meant as a tool to prove allSeparableElement         *)
(*         Derivation K D == D is a linear operator on K that satifies        *)
(*                           Leibniz's product rule                           *)
(* DerivationExtend x D K == Given a derivation D on K and a separable        *)
(*                           element x over K, this function returns the      *)
(*                           unique extension of D to K(x).                   *)
(******************************************************************************)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope ring_scope.

Import GRing.Theory.

Lemma exprp_addl (R : comRingType) (x y : R) (n : nat) :
  [char R].-nat n -> (x + y) ^+ n = x ^+ n + y ^+ n.
Proof.
case: n=> [|[|]] // n Hn; move: (Hn)=> /pnatPpi /(_ (pi_pdiv _))=> charR.
move: Hn; rewrite (eq_pnat _ (charf_eq charR))=> /p_natP [] e ->.
elim: e => // e ihe; rewrite !expnSr !exprn_mulr ihe.
by rewrite [_ ^+ _]Frobenius_aut_add_comm //; apply: mulrC.
Qed.

Section SeparablePoly.

Variable (R: idomainType).
Variable (p q : {poly R}).

Definition separablePolynomial (p:{poly R}) := coprimep p (deriv p).

Lemma separable_mul : separablePolynomial (p * q) = 
 [&& separablePolynomial p, separablePolynomial q & coprimep p q].
Proof.
have dvdpR : forall (p q : {poly R}), p %| p * q.
 by move => p0 q0; rewrite dvdp_mulr // dvdpp.
have dvdpL : forall (p q : {poly R}), q %| p * q.
 by move => p0 q0; rewrite dvdp_mull // dvdpp.
rewrite /separablePolynomial.
rewrite derivM.
rewrite -!gcdp_eqp1 -!size_poly_eqp1 -!dvdp1.
have dvdp_or : forall (d n m : {poly R}), (d %| n) || (d %| m) -> d %| m * n.
 move => d n m.
 by move/orP => [H|H]; [apply:dvdp_mull|apply: dvdp_mulr].
apply/idP/and3P => [H|[Hp Hq Hpq]].
 by split; apply: dvdp_trans H; rewrite dvdp_gcd; apply/andP; split;
   rewrite ?(dvdp_add, dvdp_or, dvdp_gcdl, dvdp_gcdr) // orbT.
set (c:=(deriv p * q + p * deriv q)).
suff: (gcdp p c) * (gcdp q c) %| 1.
 apply: dvdp_trans.
 rewrite (eqp_dvdr _ (mulp_gcdl _ _ _)).
 rewrite dvdp_gcd.
 rewrite (eqp_dvdr _ (mulp_gcdr _ _ _)).
 rewrite dvdp_gcd dvdp_gcdl /=.
 by apply/andP; split; apply: (dvdp_trans (dvdp_gcdr _ _));
     [apply: dvdp_mull | apply: dvdp_mulr]; apply: dvdpp.
rewrite /c {c} -(GRing.mulr1 1).
by apply: dvdp_mul; first rewrite GRing.addrC GRing.mulrC;
 rewrite (eqp_dvdl _ (gcdp_addl_mul _ _ _));
 [rewrite GRing.mulrC; move: Hp|move: Hq];
 apply:dvdp_trans;
 rewrite dvdp_gcd dvdp_gcdl /=;
 rewrite -{2}[deriv _](GRing.mul1r);
 apply: dvdp_trans (dvdp_mul Hpq (dvdpp _));
 rewrite (eqp_dvdr _ (mulp_gcdl _ _ _)) dvdp_gcd dvdp_gcdr dvdp_mulr //;
 rewrite dvdp_gcdl.
Qed.

Lemma separable_neq0 : separablePolynomial p -> p != 0.
Proof.
apply: contraL.
move/eqP ->.
by rewrite /separablePolynomial deriv0 coprime0p eqp01.
Qed.

End SeparablePoly.

(* :TODO: Move this to poly.v *)
Lemma factor_irr : forall (R : idomainType) x (d : {poly R}),
 d %| 'X - x%:P -> (d %= 'X - x%:P) || (d %= 1).
Proof.
move => R x d.
move/ID.dvdpP => [c [q [Hc Hq]]].
have: q * d != 0.
 by rewrite -Hq -mul_polyC mulf_eq0 negb_or polyC_eq0 Hc factor_eq0.
rewrite mulf_eq0 negb_or.
case/andP => Hq0 Hd0.
move/(f_equal (fun z : {poly R} => size z)): (Hq).
rewrite size_scaler // size_factor.
rewrite size_mul_id //.
rewrite -size_poly_eqp1.
move: (size_poly_eq0 d).
case: (size d) => [|[|[|n]]].
- by rewrite -[d == 0]negbK Hd0.
- by rewrite eqxx orbT.
- rewrite !addn2 => _.
  case.
  move/eqP.
  rewrite eq_sym size_poly_eqp1 -(eqp_mul2r _ _ Hd0) -Hq mul1r.
  by rewrite (eqp_ltrans (eqp_mulC _ Hc)) eqp_sym => ->.
- rewrite !addnS => _.
  case.
  move/eqP.
  by rewrite eq_sym addn_eq0 size_poly_eq0 -[q == 0]negbK Hq0.
Qed.

Lemma separable_root : forall (R : idomainType) (p : {poly R}) x,
 separablePolynomial (p * ('X - x%:P)) = separablePolynomial p && ~~ root p x.
Proof.
move => R p x.
rewrite separable_mul.
congr (_ && _).
rewrite /separablePolynomial !derivE ?subr0 coprimep1 /= -gcdp_eqp1.
case/factor_irr/orP: (dvdp_gcdr p ('X - x%:P)) => Hp.
 move/eqp_root: (Hp).
 move/(_ x).
 rewrite root_gcd root_factor eqxx andbT => ->.
 rewrite (eqp_ltrans Hp).
 apply/negbTE/negP.
 move/size_eqp.
 by rewrite size_poly1 size_factor.
rewrite Hp.
symmetry.
apply/negbT/negbTE.
move: Hp.
rewrite gcdp_eqp1.
case (eqVneq p 0) => [->|Hp0].
 rewrite coprime0p.
 move/size_eqp.
 by rewrite size_poly1 size_factor.
apply: contraL => Hp.
apply/coprimepPn => //.
exists ('X - x%:P).
rewrite -root_factor_theorem root_gcd root_factor eqxx Hp /=.
apply/negP.
move/size_eqp.
by rewrite size_poly1 size_factor.
Qed.

Lemma separable_factors : forall (R : idomainType) (r : seq R),
  separablePolynomial (\prod_(x <- r) ('X - x%:P)) = uniq r.
Proof.
move => R.
elim => [|x r IH].
 by rewrite big_nil /separablePolynomial coprime1p.
by rewrite big_cons mulrC separable_root IH root_prod_factors andbC.
Qed.

Lemma separable_dvd : forall (R : idomainType) (p q : {poly R}),
  separablePolynomial p -> q %| p ->
  separablePolynomial q.
Proof.
move => R p q Hp.
move/ID.dvdpP => [c [r [Hc0 Hpq]]].
have Hp0: p != 0 by apply separable_neq0.
move: Hp.
rewrite /separablePolynomial /coprimep.
rewrite -[size _]/((size (gcdp p p^`())).+1.-1) -[size _]add0n -addSn.
rewrite -{1}[1%N]/(true:nat) -Hc0 -(size_polyC) -size_mul_id ?polyC_eq0 //.
 rewrite (size_eqp (mulp_gcdr _ _ _)) !mul_polyC -derivZ.
 rewrite -[_ == 1%N]/(separablePolynomial (c *: p)) Hpq separable_mul.
 by case/and3P.
by rewrite gcdp_eq0 negb_and Hp0.
Qed.

(*This isn't a very nice proof :( *)
Lemma make_separable : forall (R : idomainType) (p : {poly R}),
  p != 0 -> separablePolynomial (p %/ (gcdp p p^`())).
Proof.
move => R p.
move: {2}(size p) (leqnn (size p)) => n.
elim: n p => [p | n IH p Hp Hp0].
 rewrite leqn0 size_poly_eq0.
 move/eqP ->.
 by rewrite eqxx.
move: (dvdp_gcdl p p^`()).
rewrite ID.dvdp_eq.
set q := p %/ gcdp p p^`().
set c := _ ^+ _.
have Hc0 : c != 0.
 by rewrite expf_eq0 negb_and lead_coef_eq0 gcdp_eq0 negb_and Hp0 orbT.
case (eqVneq q 0) => [|Hq0].
 move ->.
 by rewrite mul0r -mul_polyC mulf_eq0 -[_ || _]negbK negb_or Hp0 polyC_eq0 Hc0.
case (eqVneq (gcdp p p^`()) 0) => [|Hd0].
 move ->.
 by rewrite mulr0 -mul_polyC mulf_eq0 -[_ || _]negbK negb_or Hp0 polyC_eq0 Hc0.
move/eqP => Hpq.
move/eqP: (f_equal (fun f:{poly R} => size f) Hpq).
rewrite size_scaler // size_mul_id // (polySpred Hd0) addnS.
move/eqP => Hsz.
have: size q <= size p by rewrite Hsz leq_addr.
rewrite leq_eqVlt.
case/orP.
 move/eqP => Hszq.
 move/eqP: Hsz.
 rewrite -[size p]addn0 Hszq eqn_addl -(inj_eq succn_inj) -(polySpred Hd0).
 rewrite eq_sym -[_ == 1%N]/(separablePolynomial p).
 move/separable_dvd; apply.
 by rewrite -(eqp_dvdr _ (eqp_mulC _ Hc0)) Hpq dvdp_mulIl.
move/leq_trans/(_ Hp)/IH/(_ Hq0).
move: (dvdp_gcdl q q^`()).
rewrite ID.dvdp_eq.
set k := gcdp q q^`().
set r := q %/ k.
set b := _ ^+ _.
have Hb0 : b != 0.
 by rewrite expf_eq0 negb_and lead_coef_eq0 gcdp_eq0 negb_and Hq0 orbT.
case (eqVneq r 0) => [|Hr0].
 move ->.
 by rewrite mul0r -mul_polyC mulf_eq0 -[_ || _]negbK negb_or Hq0 polyC_eq0 Hb0.
case (eqVneq k 0) => [|Hk0].
 move ->.
 by rewrite mulr0 -mul_polyC mulf_eq0 -[_ || _]negbK negb_or Hq0 polyC_eq0 Hb0.
move/eqP => Hqr Hsepr.
pose w := gcdp k r.
have := separable_dvd Hsepr (dvdp_gcdr k r).
rewrite -/w => Hsepw.
case (leqP (size w) 1); last first.
 move => Hw.
 have Hwp : exists n, ~~ (w ^+ n %| p).
  exists (size p).
  move: Hw.
  apply: contraL.
  move/(leq_dvdp Hp0).
  rewrite polySpred ?expf_eq0 ?negb_and ?separable_neq0 ?orbT // size_exp_id.
  apply: contraL. 
  move/subnK <-.
  by rewrite addn2 mulSn -leqNgt leq_addr.
 move: (ex_minnP Hwp) => [[|[|m]]].
   by rewrite expr0 dvd1p.
  rewrite expr1.
  suff -> : (w %| p) by done.
  rewrite (dvdp_trans (dvdp_gcdl _ _)) // (@dvdp_trans _ q) //.
   by rewrite -(eqp_dvdr _ (eqp_mulC _ Hb0)) Hqr dvdp_mulIr.
  by rewrite -(eqp_dvdr _ (eqp_mulC _ Hc0)) Hpq dvdp_mulIl.
 move => Hwm2.
 move/(_ m.+1)/contraR.
 rewrite -leqNgt leqnn.
 move/(_ isT) => Hwm1.
 have Hwm : w ^+ m %| gcdp p p^`().
  rewrite dvdp_gcd (dvdp_trans _ Hwm1) ?exprS ?dvdp_mulIr //.
  move/ID.dvdpP: Hwm1 => [a [x [Ha0 Hx]]].
  rewrite -(eqp_dvdr _ (eqp_mulC _ Ha0)) -derivZ Hx derivM. 
  by rewrite deriv_exp -mulr_natl exprS !mulrA -mulr_addl dvdp_mulIr.
 have Hw2 : w * w %| q.
  rewrite -(eqp_dvdr _ (eqp_mulC _ Hb0)) Hqr dvdp_mul ?dvdp_gcdl //.
  by rewrite dvdp_gcdr.
 move: (dvdp_mul Hw2 Hwm).
 rewrite -Hpq (eqp_dvdr _ (eqp_mulC _ Hc0)).
 by rewrite -mulrA -!exprS -[_ %| _]negbK Hwm2.
rewrite 2!leq_eqVlt ltnS ltn0 orbF (inj_eq succn_inj).
case/orP; last by rewrite size_poly_eq0 gcdp_eq0 -[r == 0]negbK Hr0 andbF.
rewrite -[_ == 1%N]/(coprimep k r) => Hkr.
move:(dvdp_gcdr q q^`()).
rewrite -(eqp_dvdr _ (eqp_mulC _ Hb0)) -derivZ Hqr derivM -/k.
rewrite dvdp_addr ?dvdp_mulIr // mulrC gausspl //.
case (eqVneq k^`() 0) => Hk'0; last first.
 by move/(leq_dvdp Hk'0); rewrite leqNgt lt_size_deriv.
move => _.
case (leqP (size k) 1).
 rewrite 2!leq_eqVlt ltnS ltn0 orbF (inj_eq succn_inj).
 by rewrite size_poly_eq0 -[_ == 0]negbK Hk0 orbF.
move => Hk.
have Hkp : exists n, ~~ (k ^+ n %| p).
 exists (size p).
 move: Hk.
 apply: contraL.
 move/(leq_dvdp Hp0).
 rewrite polySpred ?expf_eq0 ?negb_and ?Hk0 ?orbT // size_exp_id.
 apply: contraL.
 move/subnK <-.
 by rewrite addn2 mulSn -leqNgt leq_addr.
move: (ex_minnP Hkp) => [[|m]].
 by rewrite expr0 dvd1p.
move => Hkm1.
move/(_ m)/contraR.
rewrite -leqNgt leqnn.
move/(_ isT) => Hkm.
have : k ^+ m %| gcdp p p^`().
 rewrite dvdp_gcd Hkm.
 move/ID.dvdpP: Hkm => [a [x [Ha0 Hx]]].
 rewrite -(eqp_dvdr _ (eqp_mulC _ Ha0)) -derivZ Hx derivM.
 by rewrite deriv_exp Hk'0 !mul0r mul0rn mulr0 addr0 dvdp_mulIr.
have Hkq : k %| q by rewrite -(eqp_dvdr _ (eqp_mulC _ Hb0)) Hqr dvdp_mulIr.  
move/(dvdp_mul Hkq).
by rewrite -Hpq -exprS (eqp_dvdr _ (eqp_mulC _ Hc0)) -[_ %| _]negbK Hkm1.
Qed.

(*
(* :TODO: Move this to poly.v *)
Lemma egcdp_rec_map:
  forall (F : fieldType) (R : idomainType) (f : {rmorphism F -> R})
         (p q : {poly F}) n,
    (map_poly f (egcdp_rec p q n).1, map_poly f (egcdp_rec p q n).2) =
    (egcdp_rec (map_poly f p) (map_poly f q) n).
Proof.
move => F R f p q n.
elim: n p q => [|n IH] => /= p q; first by rewrite rmorph1 rmorph0.
rewrite map_poly_eq0.
case: eqP => Hq0; first by rewrite rmorph1 rmorph0.
rewrite -map_modp -(IH q (p %% q)).
case: (egcdp_rec _ _ n) => a b /=.
rewrite map_poly_scaler lead_coef_map -rmorphX scalp_map rmorph_sub rmorphM.
by rewrite -map_divp.
Qed.

(* :TODO: Move this to poly.v *)
Lemma egcdp_map:
  forall (F : fieldType) (R : idomainType) (f : {rmorphism F -> R})
         (p q : {poly F}),
    (map_poly f (egcdp p q).1, map_poly f (egcdp p q).2) =
    (egcdp (map_poly f p) (map_poly f q)).
Proof.
move => F R f p q; rewrite /egcdp !size_map_poly.
case: ifP=> /= hspq; first by apply: egcdp_rec_map.
move: (egcdp_rec_map f q p (size p)).
by case: (egcdp_rec (map_poly _ _) _ _)=> [a b [-> ->]].
Qed.
*)
Section InfinitePrimitiveElementTheorem.

Local Notation "p ^ f" := (map_poly f p) : ring_scope.
Local Notation "'Y" := 'X%:P : ring_scope.

Lemma coprime_pT_q_subproof : forall (F : fieldType) (p q : {poly F}),
  p != 0 -> q.[0] != 0 ->
  coprimep ((p ^ polyC) \Po ('Y * 'X)) (q ^ polyC).
Proof.
move => F p q Hp0 Hq0.
set p' := _ \Po _.
set q' := _ ^ _.
have Hp'0 : p' != 0.
 rewrite -lead_coef_eq0 lead_coefE size_comp_poly_id mul_polyC.
 rewrite size_scaler -?['X == 0]size_poly_eq0 size_polyX // muln1 size_map_poly.
 rewrite [p']comp_polyE size_map_poly.
 rewrite (_ : \sum_(i < size p) (p ^ polyC)`_i *: ('Y * 'X) ^+ i
            = \poly_(i < size p) ((p ^ polyC)`_i * 'X ^+ i)); last first.
  rewrite poly_def.
  apply: eq_bigr => i _.
  by rewrite exprn_mull -polyC_exp mul_polyC scalerA.
 rewrite coef_poly.
 move/polySpred: (Hp0) => Hp0'.
 rewrite {2}Hp0' ltnSn mulf_eq0 coef_map polyC_eq0 -lead_coefE lead_coef_eq0.
 by rewrite negb_or Hp0 -size_poly_eq0 size_polyXn.
have Hq'0 : q' != 0.
 rewrite map_poly_eq0.
 move: Hq0.
 apply: contra.
 move/eqP ->.
 by rewrite horner0.
move: Hq0.
apply: contraR.
case (eqVneq q 0) => [->|Hq0]; first by rewrite horner0.
rewrite neq_ltn.
case/orP => [|Hp'q'].
 by rewrite ltnS leqn0 size_poly_eq0 gcdp_eq0 -[p' == 0]negbK Hp'0.
have [[u v]] :
  exists uv, [/\ uv.1 * p' = uv.2 * q'
               , 0 < size uv.1 < size q' & 0 < size uv.2 < size p'].
 have Hgcd : (gcdp p' q') != 0.
  rewrite -size_poly_eq0.
  move: Hp'q'.
  apply: contraL.
  by move/eqP ->.
 move/ID.dvdpP: (dvdp_gcdl p' q') => [c1 [u1 [Hc1 Hu1]]].
 move/ID.dvdpP: (dvdp_gcdr p' q') => [c2 [v1 [Hc2 Hv1]]].
 exists (c1 *: v1, c2 *: u1).
 rewrite !{1}size_scaler // -!{1}scaler_mull !scaler_mulr Hu1 Hv1 !mulrA.
 rewrite [v1 * _]mulrC.
 have Hu10 : u1 != 0.
  rewrite -polyC_eq0 in Hc1.
  move: (mulf_neq0 Hc1 Hp'0).
  rewrite mul_polyC Hu1 mulf_eq0 negb_or.
  by case/andP.
 have Hv10 : v1 != 0.
  rewrite -polyC_eq0 in Hc2.
  move: (mulf_neq0 Hc2 Hq'0).
  rewrite mul_polyC Hv1 mulf_eq0 negb_or.
  by case/andP.
 rewrite -(size_scaler q' Hc2) -(size_scaler p' Hc1) Hv1 Hu1.
 rewrite !{1}size_mul_id // -(subnK Hp'q') !{1}addnA !{1}addn2 !{1}ltnS !{1}leq_addr.
 by rewrite !lt0n !size_poly_eq0 !andbT.
move: {2}(size v + size (lead_coef v))%N
      (refl_equal (size v + size (lead_coef v))%N) => n.
elim: n p u v {Hp0} @p' Hp'0 {Hp'q'} 
     => [|n IH] p u v p' Hp'0 Hszv /= [Huv Hu Hv].
 case/andP: Hv.
 move/eqP: Hszv.
 rewrite addn_eq0.
 case/andP.
 by move/eqP ->.
have Hcomm : commr_rmorph idfun (0:F) by apply: mulrC.
pose Y0 := horner_morph Hcomm.
move: (f_equal (map_poly Y0) Huv).
rewrite !rmorphM /= -/Y0.
rewrite -horner_map rmorphM [_ 'Y]map_polyC [_ 'X]horner_morphX polyC0 mul0r.
rewrite -!map_comp_poly ?rmorph0 ?[Y0 0]rmorph0 //=.
set Z := (_ \o _).
rewrite {1}(_ : 0 = Z 0); last by rewrite [Z 0]rmorph0.
rewrite horner_map /= map_polyC /= horner_morphC /= /idfun mulrC mul_polyC.
rewrite [q ^ _]map_polyE (eq_map (horner_morphC Hcomm) q) map_id polyseqK.
move/(f_equal (fun p : {poly F} => size p))/eqP.
case (eqVneq p.[0] 0) => Hp00; last first.
 rewrite size_scaler //.
 case (eqVneq (v ^ Y0) 0) => HvY0; last first.
  rewrite size_mul_id // eqn_leq.
  case/andP => _ Hsz.
  case/andP: Hu => _.
  apply: contraLR => _.
  rewrite -leqNgt size_map_poly (@leq_trans (size (u ^ Y0))) ?size_poly //.
  rewrite (leq_trans _ Hsz) //.
  move/polySpred: HvY0 ->.
  by rewrite addSn leq_addl.
 rewrite HvY0 mul0r size_poly0 size_poly_eq0.
 move/eqP => HuY0.
 have HYfactor : forall f, f ^ Y0 = 0 -> exists g, f = g * 'Y.
  move => f Hf.
  exists (Poly (map (fun p => p %/ 'X) f)).
  apply/polyP => i.
  rewrite mulrC mul_polyC coefZ coef_Poly.
  case (leqP (size f) i) => Hsz.
   by rewrite !nth_default ?size_map // mulr0.
  rewrite (nth_map 0 0 _ Hsz) mulrC divpK //.
  move/eqP : (f_equal (fun p : {poly F} => p`_i) Hf).
  rewrite coef0 coef_map.
  case/factor_theorem.
  rewrite map_polyE map_id polyseqK subr0 => ? ->.
  by rewrite dvdp_mulIr.
 case: (HYfactor _ HvY0) => v' Hv'.
 case: (HYfactor _ HuY0) => u' Hu'.
 apply: (IH p u' v') => //.
  move: Hszv.
  rewrite Hv' mulrC mul_polyC /lead_coef !size_scaler; last first.
   by rewrite -size_poly_eq0 size_polyX.
  rewrite coefZ size_monic_mul ?monicX //; last first.
   case/andP: Hv.
   rewrite -/(lead_coef v') lead_coef_eq0 lt0n size_poly_eq0 Hv' mulf_eq0.
   rewrite negb_or.
   by case/andP.
  rewrite size_polyX add2n addnS.
  by move/succn_inj.
 move: Huv Hu Hv.
 rewrite -/p' Hv' Hu' ![_ * 'Y]mulrC -2!mulrA /=.
 move/mulfI ->.
  by rewrite !{1}mul_polyC !{1}size_scaler -?{1}size_poly_eq0 ?size_polyX //.
 by rewrite polyC_eq0 monic_neq0 // monicX.
rewrite Hp00 scale0r size_poly0 eq_sym size_poly_eq0.
rewrite mulf_eq0 -[q == 0]negbK Hq0 orbF.
move/eqP => HvY0.
move/eqP: (f_equal (fun p : {poly {poly F}} => p.[0]) Huv).
rewrite !(horner_lin, horner_comp_poly) -{2 4}polyC0 !horner_map Hp00 /=.
rewrite polyC0 mulr0 eq_sym mulf_eq0 polyC_eq0.
case/orP => //.
case/factor_theorem => vx Hvvx.
move/eqP: Hp00.
case/factor_theorem => px Hppx.
rewrite !subr0 in Hvvx Hppx.
have Hpx : p' = (px ^ polyC \Po 'Y * 'X) * ('Y * 'X).
 by rewrite /p' Hppx rmorphM /= map_polyX comp_poly_mull poly_comXp.
apply: (IH px (u * 'Y) vx).
  move: Hp'0.
  rewrite Hpx mulf_eq0 negb_or.
  by case/andP.
 case/andP: Hv Hszv.
 rewrite Hvvx lt0n size_poly_eq0 mulf_eq0 negb_or.
 case/andP => Hvx _ _.
 rewrite size_mul_monic ?lead_coef_mul_monic ?monicX // size_polyX addn2 addSn.
 by move/succn_inj.
split => /=.
  move: Huv.
  rewrite Hvvx Hpx -[_ * q']mulrA [_ * q']mulrC [vx * _]mulrA.
  rewrite [_ * ('Y * _)]mulrA [_ * 'Y]mulrC 2!mulrA.
  move/mulIf.
  apply.
  by rewrite -size_poly_eq0 size_polyX.
 by rewrite mulrC mul_polyC size_scaler // -size_poly_eq0 size_polyX.
case/andP: Hv.
rewrite Hvvx !lt0n !size_poly_eq0 mulf_eq0 negb_or.
case/andP => Hvx0 HX.
move : Hp'0.
rewrite Hvx0 size_mul_monic ?monicX // size_polyX addn2 Hpx mulf_eq0 negb_or.
case/andP => Hpx0 HXX0.
rewrite size_mul_id // mul_polyC size_scaler // -?size_poly_eq0 size_polyX //.
by rewrite addn2 ltnS.
Qed.


Variables (F L: fieldType) (iota : {rmorphism F -> L}).
Variables (x y : L) (p : {poly F}).
Hypothesis (pne0 : p != 0).
Hypothesis (Hpx : root (p ^ iota) x).

Hypothesis resultant_hypothesis : forall (a b: L) (pa pb : {poly F}),
  pa != 0 -> pb != 0 -> root (pa ^ iota) a -> root (pb ^ iota) b -> 
  exists2 p, p != 0 & root (p ^ iota) (a - b).

Lemma PET_Infinite_Case : forall q : {poly F},
  root (q ^ iota) y -> separablePolynomial q ->
  exists r : {poly L}, r != 0 /\
   forall t, ~~root r (iota t) ->
    (exists p0, (p0 ^ iota).[iota t * y - x] = x) /\
    (exists q0, (q0 ^ iota).[iota t * y - x] = y).
Proof.
move => q Hqy Hsep.
have qne0 := separable_neq0 Hsep.
set p' := (p ^ iota) \Po ('X + x%:P).
have [qq Hqq] := (factor_theorem _ _ Hqy).
set q' := qq \Po ('X + y%:P).
move: Hsep.
rewrite /separablePolynomial -gcdp_eqp1 -(eqp_map iota) rmorph1 gcdp_map.
rewrite -deriv_map Hqq gcdp_eqp1 [coprimep _ _]separable_root.
case/andP => _.
rewrite /root {1}(_ : y = ('X + y%:P).[0]); last by rewrite !horner_lin.
rewrite -horner_comp_poly -/q'.
have p'ne0 : p' != 0.
 move: pne0.
 apply: contra.
 move/eqP/(f_equal (fun q => q \Po ('X - x%:P)))/eqP.
 rewrite poly_com0p /p' comp_polyA comp_poly_translateK comp_polyX.
 by rewrite map_poly_eq0.
move/(coprime_pT_q_subproof p'ne0).
rewrite -gcdp_eqp1.
move: (bezoutp (p' ^ polyC \Po 'Y * 'X) (q' ^ polyC)) => [u [v Huv]].
move/(eqp_trans Huv) => {Huv}.
rewrite -size_poly_eqp1.
case/size1P => r [Hr0 Hr].
exists r.
split => // t Ht.
suff Hq0 : (exists q0 : {poly F}, (q0 ^ iota).[iota t * y - x] = y).
 split => //.
 case: Hq0 => q0 Hq0.
 exists (t *: q0 - 'X).
 rewrite rmorph_sub [_ 'X]map_polyX [_ (_ *: _)]map_poly_scaler !horner_lin.
 by rewrite Hq0 oppr_sub addrC addrNK.
have Hcomm: (commr_rmorph idfun (iota t)) by apply: mulrC.
move/(f_equal (map_poly (horner_morph Hcomm))) : Hr.
rewrite rmorphD !{1}rmorphM map_polyC /= /comp_poly -horner_map rmorphM.
rewrite [_ 'Y]map_polyC [_ 'X]horner_morphX [_ 'X]map_polyX.
rewrite -map_comp_poly ?rmorph0 // -[(q' ^ _) ^ _]map_comp_poly ?rmorph0 //.
rewrite ![GRing.Additive.apply _]/=.
rewrite [_ ^ (map_poly _ \o _)]map_polyE.
rewrite (_ : (map (map_poly (horner_morph Hcomm) \o polyC) (p' ^ polyC))
           = (map (polyC \o (horner_morph Hcomm)) (p' ^ polyC))); last first.
 by rewrite (eq_map (map_polyC _)).
rewrite -map_polyE -map_comp_poly ?rmorph0 //.
rewrite -[((polyC \o horner_morph Hcomm) \o polyC)]
        /(polyC \o (horner_morph Hcomm \o polyC)).
rewrite [p' ^ _]map_comp_poly ?rmorph0 // ![GRing.Additive.apply _]/=.
rewrite !map_polyE !(eq_map (horner_morphC _)) !map_id -!map_polyE.
rewrite !polyseqK -/(comp_poly ((iota t)%:P  * 'X) p').
set u1 := (u ^ _).
set v1 := (v ^ _).
set p1 := (_ \Po _).
rewrite /horner_morph map_polyE map_id polyseqK.
move => Hlincomb.
have : (coprimep p1 q').
 apply/bezout_coprimepP.
 exists (u1, v1).
 by rewrite Hlincomb polyC_eqp1.
clear -Hpx Hqy pne0 qne0 Hqq resultant_hypothesis.
move/(coprimep_comp_poly ('X - y%:P)).
rewrite /q' [(qq \Po _) \Po _]comp_polyA comp_poly_translateK comp_polyX.
rewrite -gcdp_eqp1.
set p2 := (_ \Po _) => Hp2.
have: (gcdp p2 (q ^ iota) %= ('X - y%:P)).
 apply/andP; split; last first.
  rewrite -root_factor_theorem root_gcd Hqy andbT /root /p2 /p1 /p'.
  by rewrite !(horner_comp_poly, horner_lin) subrr mulr0 add0r.
 rewrite -[_ - _]mul1r.
 apply: (@dvdp_trans _ (gcdp (p2 * ('X - y%:P)) (q ^ iota))).
  rewrite dvdp_gcd dvdp_gcdr (dvdp_trans (dvdp_gcdl _ _)) // dvdp_mulr //.
 case/andP: Hp2.
 rewrite Hqq -(eqp_dvdl _ (mulp_gcdl _ _ _)) dvdp_mul2r //.
 by rewrite -size_poly_eq0 size_factor.
set z := iota t * y - x.
have [qt qtne0 Hqt] : exists2 qt, qt != 0 & root (qt ^ iota) (iota t * y).
 case (eqVneq t 0) => [-> | Ht].
  exists 'X; first by rewrite -size_poly_eq0 size_polyX.
  by rewrite rmorph0 mul0r /root map_polyX hornerX.
 exists (q \Po (t^-1 *: 'X)).
  move: qne0.
  apply: contra.
  move/eqP/polyP => Hqt.
  apply/eqP/polyP => i.
  rewrite coef0 -[X in _ = X](mulr0 (t ^+ i)) -[X in _ * X](coef0 _ i) -(Hqt i).
  rewrite -coefZ comp_polyE scaler_sumr -{1}[q]coefK poly_def !coef_sum.
  apply: eq_bigr => j _.
  rewrite scaler_exp !coefZ mulrA [t ^+ i * _]mulrC -mulrA coefXn.
  case: (eqVneq i j) => [-> | Hij].
   by rewrite expr_inv mulVKf // expf_eq0 negb_and Ht orbT.
  by rewrite -[_ == _]negbK Hij !mulr0.
 apply/eqP.
 move/eqP: Hqy <-.
 rewrite comp_polyE rmorph_sum /root horner_sum horner_coef size_map_poly.
 apply eq_bigr => i _ /=.
 rewrite map_poly_scaler rmorphX /= map_poly_scaler map_polyX coef_map.
 rewrite horner_scaler horner_exp horner_scaler hornerX.
 by rewrite fmorphV mulKf // fmorph_eq0.
case: (resultant_hypothesis qtne0 pne0 Hqt Hpx) => [f Hf0 Hfz].
set Fz := subFExtend iota z f.
set kappa := (@subfx_inj _ _ _ _ _) : Fz -> L.
pose (Q := (q ^ (inj_subfx iota z f))).
have HQ : q ^ iota = Q ^ kappa.
 rewrite /Q -map_comp_poly ?[kappa 0]rmorph0 // !map_polyE.
 congr (Poly _).
 apply: eq_map => a.
 by rewrite /= /kappa subfx_inj_eval // map_polyC hornerC.
pose (P := (p ^ (inj_subfx iota z f) \Po 
  ((inj_subfx iota z f t) *: 'X - (subfx_eval iota z f 'X)%:P))).
have HP : p2 = P ^ kappa.
 rewrite -!horner_map rmorph_sub /= map_poly_scaler map_polyC map_polyX /=.
 rewrite !subfx_inj_eval // map_polyX map_polyC hornerX hornerC.
 rewrite -map_comp_poly ?rmorph0 //.
 rewrite (eq_map_poly (map_polyC _)).
 rewrite map_comp_poly ?rmorph0 //=.
 rewrite -[(p ^ _) ^ _]map_comp_poly ?rmorph0 //.
 rewrite (eq_map_poly (fun q => subfx_inj_eval (polyC q) Hf0 Hfz)).
 rewrite (eq_map_poly (horner_morphC _)); last by move => ?; apply: mulrC.
 rewrite /p2 /p1 /p' !comp_polyA {2 3}/comp_poly.
 rewrite rmorphM rmorphD ![GRing.RMorphism.apply _]/= !map_polyX !map_polyC.
 rewrite !horner_lin mulr_addr -addrA -polyC_opp -polyC_mul polyC_add oppr_add.
 by rewrite -!polyC_opp opprK mulrN mul_polyC.
rewrite HQ HP -gcdp_map /=.
move/eqpP => [c1 [c2 [Hc1 Hc2]]].
move/(canLR (scalerK Hc2)).
rewrite scalerA.
move/polyP => Hgcd.
move:(Hgcd 1%N).
rewrite coefD coefN coefC coefX subr0 coefZ coef_map mulr1n.
move => Hgcd1.
move:(nonzero1r L).
rewrite -Hgcd1 mulf_eq0 negb_or.
move/andP => [Hc120 Hgcd10].
move/eqP:(Hgcd 0%N).
rewrite coefD coefN coefC coefX coefZ coef_map sub0r -eqr_oppC.
move:Hgcd1.
move/(canRL (mulfK Hgcd10)) ->.
rewrite mul1r -fmorphV -rmorphM -rmorphN.
set y' := -_.
case: (subfxE y') => [h ->].
rewrite /= subfx_inj_eval //.
move/eqP => Hh.
by exists h.
Qed.

Lemma PET_char0 : forall q : {poly F},
  q != 0 -> root (q ^ iota) y -> [char F] =i pred0 -> exists n,
  (exists p0, (p0 ^ iota).[y *+ n - x] = x) /\
  (exists q0, (q0 ^ iota).[y *+ n - x] = y).
Proof.
move => q qne0 Hqy; move/charf0P => Hchar.
move: (dvdp_gcdl q q^`()).
rewrite dvdp_eq.
set qq := _ %/ _ => /eqP Hq.
have Hqqy : root (qq ^ iota) y.
  move: (qne0); rewrite -(map_poly_eq0 iota).
  case/(maxdivp y) => r Hry [[|n] Hqr].
    by  move: Hqr Hqy Hry ->; rewrite expr0 mulr1 => ->.
 move: (f_equal (@deriv _) Hqr).
 rewrite deriv_map derivM deriv_exp deriv_factor mul1r exprS -mulr_natl !mulrA.
 rewrite -mulr_addl => Hq'.
 have: ('X - y%:P) ^+ n.+1 %| q ^iota by rewrite Hqr; apply: dvdp_mulIr.
 move: (f_equal (map_poly iota) Hq).
 rewrite rmorphM /=.
 rewrite gcdp_map {1}Hqr.
 rewrite Hq' exprS mulrA => <-.
 set s1 := r * _.
 set s2 := r^`() * _ + _.
 set s3 := _ ^+ n.
 move: (mulp_gcdl s1 s2 s3).
 move:qne0.
 rewrite -Hq mulf_eq0 negb_or -(map_poly_eq0 iota).
 case/andP.
 move/eqp_mul2l => <- _.
 move/eqp_dvdr <-.
 rewrite mulrA dvdp_mul2r /s3 ?expf_eq0 ?factor_eq0 ?andbF //.
 rewrite -root_factor_theorem root_mul root_gcd.
 case/orP => //.
 case/andP => _.
 rewrite root_factor_theorem dvdp_addr; last by rewrite dvdp_mull // dvdpp.
 rewrite -root_factor_theorem mulr_natr -scaler_nat root_scaler; last first.
  rewrite -(rmorph0 iota) -(rmorph1 iota) -rmorphMn (inj_eq (fmorph_inj _)).
  by rewrite Hchar.
 by rewrite -[_ r y]negbK Hry.
have Hsep: separablePolynomial qq.
 move: (make_separable qne0).
 rewrite -{1}Hq divp_mull; last by rewrite gcdp_eq0 negb_and qne0.
 by move/separable_dvd; apply.
case: (PET_Infinite_Case Hqqy Hsep) => f [Hf0 Hf].
pose s := mkseq (fun x => iota (x%:R : F)) (size f).
have Hs : uniq_roots s.
 rewrite uniq_rootsE.
 apply: mkseq_uniq.
 suff Hwlog: forall a b, iota (a%:R : F) = iota (b%:R : F) -> a <= b;
  move => a b Hab.
  apply/eqP.
  rewrite eqn_leq.
  rewrite !Hwlog //.
 move/eqP: Hab.
 apply: contraLR.
 rewrite -ltnNge => Hab.
 rewrite (inj_eq (fmorph_inj iota)) -subr_eq0 -mulrn_subr; last by rewrite ltnW.
 move: Hab.
 rewrite Hchar -subn_gt0.
 by move/prednK <-.
move/contra: (fun X => max_ring_poly_roots (rs:=s) Hf0 X Hs).
rewrite -leqNgt size_mkseq.
move/(_ (leqnn _)).
case/allPn => ?.
case/mapP => t _ -> Ht.
exists t.
rewrite -mulr_natl -[1](rmorph1 iota) -rmorphMn.
by apply: Hf.
Qed.

End InfinitePrimitiveElementTheorem.

Section Separable.

Variable F0 : fieldType.
Variable L : fieldExtType F0.

Lemma charLF : [char L] =i [char F0].
Proof. apply: fmorph_char. apply: GRing.in_alg_rmorphism. Qed.

Let F : {algebra L } := aspace1 _.

Definition separableElement (K : {vspace L}) x :=
  separablePolynomial (minPoly K x).

Lemma memXED_Fadjoin_subproof : forall x, 
  x ^+ elementDegree F x \in Fadjoin F x.
Proof.
move => x.
case (eqVneq x 0) => [->|xn0]; first by rewrite exprS mul0r mem0v.
rewrite /Fadjoin /elementDegree.
case: ex_minnP.
case => //.
 by rewrite muln1 big_ord1 expr0 prodv1 !ltnn.
move => m.
rewrite dim_injv nonzero1r mul1n big_ord_recr /=.
case/orP => H.
 move/(_ (vdim L)).
 move: (H).
 rewrite ltnn /= ltnNge.
 move/negbTE ->; move/implyP.
 rewrite  implybF -[BigOp.bigop _ _ _ _ _]capfv mul1n ltnS -dimvf.
 by rewrite dimvS // subvf.
move/(_ m).
move/contra.
rewrite -ltnNge mul1n.
move/(_ (leqnn _)).
rewrite negb_or.
case/andP => _.
rewrite -ltnNge.
move/(leq_trans H).
rewrite ltnS prod1v.
set V := (\sum_(i < m.+1) _)%VS.
move => Hdim.
have: \dim (V + (x ^+ m.+1)%:VS) = \dim V.
 by apply: anti_leq; rewrite Hdim dimvS // addvSl.
move/eqP.
rewrite eq_sym dimv_leqif_sup ?addvSl //.
move => HV.
apply: (subv_trans _ HV).
by rewrite addvSr.
Qed.

Section Derivation.

Variables (K : {vspace L}) (D:'End(L)).

(* A deriviation only needs to be additive and satify lebniz's law, but all the
   deriviation I will use are going to be linear, so we just define a
   derivation to be linear. *) 
Definition Derivation : bool :=
 let s := vbasis K in
 (all (fun v1 => all (fun v2 => D (v1 * v2) == D v1 * v2 + v1 * D v2) 
                     s) s).

Hypothesis (HD : Derivation).

Lemma DerivationMul :
  forall u v, u \in K -> v \in K -> D (u * v) = D u * v + u * D v.
Proof.
move/all_nthP: HD; rewrite size_tuple=> Dmult u v Hu Hv.
have Hspan : (is_span K (vbasis K)).
  by rewrite is_span_is_basis ?is_basis_vbasis.
rewrite (is_span_span Hspan Hu) (is_span_span Hspan Hv).
rewrite !linear_sum -big_split /=.
apply: eq_bigr => j _.
rewrite -!mulr_suml linear_sum /=  -big_split /=.
apply: eq_bigr => i _.
rewrite -scaler_mull linearZ /= -scaler_mulr linearZ /=.
move/all_nthP : (Dmult 0 _ (ltn_ord i)); rewrite size_tuple.
move/(_ 0_ (ltn_ord j)); move/eqP->.
by rewrite ![D (_ *: _)]linearZ /= -!scaler_mull -!scaler_mulr !scaler_addr.
Qed.

Lemma Derivation_addp : forall p q, polyOver K p -> polyOver K q ->
 map_poly D (p + q) = map_poly D p + map_poly D q.
Proof.
move => p q. move/polyOverP => ?; move/polyOverP => ?.
by apply/polyP => i; rewrite !{1}(coefD,coef_map [linear of D]) /= linearD.
Qed.

Lemma Derivation_mulp : forall p q, polyOver K p -> polyOver K q ->
 map_poly D (p * q) = map_poly D p * q + p * map_poly D q.
Proof.
move => p q; move/polyOverP => ?; move/polyOverP => ?.
apply/polyP => i.
rewrite coefD (coef_map [linear of D]) /=  ?linear0 //.
rewrite !coefM linear_sum /= -big_split; apply: eq_bigr => j _ /=.
by rewrite !{1}(coef_map [linear of D]) DerivationMul.
Qed.

End Derivation.

Lemma subvDerivation : forall E K D, (K <= E)%VS -> Derivation E D ->
  Derivation K D.
Proof.
move => E K D.
move/subvP => HKE HD.
apply/allP => x Hx.
apply/allP => y Hy.
apply/eqP.
by rewrite (DerivationMul HD) // HKE // memv_basis.
Qed.

Section DerivationAlgebra.

Variables (E : {algebra L}) (D:'End(L)).
Hypothesis (HD : Derivation E D).

Lemma Derivation1 : D 1 = 0.
Proof.
rewrite (@GRing.addIr _ (D 1) (D 1) 0) // GRing.add0r.
by rewrite -{3}[1]mul1r (DerivationMul HD) ?mem1v // mulr1 mul1r.
Qed.

Lemma DerivationF : forall x, x \in F -> D x = 0.
Proof.
move => ?.
move/injvP => [x ->].
by rewrite linearZ /= Derivation1 scaler0.
Qed.

Lemma Derivation_exp : forall x m, x \in E -> D (x ^+ m) = x ^+ m.-1 *+ m * D x.
Proof.
move => x m Hx.
case: m; first by rewrite expr0 mulr0n mul0r Derivation1.
elim; first by rewrite expr1 expr0 mul1r.
move => m Hm.
rewrite GRing.exprS (DerivationMul HD) //; last by apply: memv_exp.
rewrite Hm /= [_ *+ m.+2]GRing.mulrS mulr_addl.
rewrite {3}GRing.exprS mulrA -GRing.mulrnAr.
congr (_ + _).
elim: (m.+1); first by rewrite GRing.expr0 mulr1 mul1r.
move => a Ha.
by rewrite mulrC.
Qed.

Lemma DerivationPoly : forall p x, polyOver E p -> x \in E ->
 D p.[x] = (map_poly D p).[x] + (deriv p).[x] * D x.
Proof.
move => p x Hp Hx.
(* Why do I have to move first? *)
move: p Hp.
apply: poly_ind => [|p c IHp].
  by rewrite !raddf0 horner0 mul0r add0r linear0.
move/polyOverP => Hp.
have Hp0: (polyOver E p).
 apply/polyOverP => i; move: (Hp i.+1).
 by rewrite coefD coefMX coefC /= addr0.
have->: map_poly D (p * 'X + c%:P) = map_poly D p * 'X + (D c)%:P.
 apply/polyP => i.
 by rewrite !(coefD, coefMX, coefC, (coef_map [linear of D])) ?linear0
            //= linearD /= ![D (if _ then _ else _)]fun_if linear0.
rewrite horner_amulX linearD /= (DerivationMul HD) ?(memv_horner Hp0) 
        ?subv_refl //.
rewrite (IHp Hp0) deriv_amulX !horner_add !horner_mul !hornerX !hornerC.
rewrite !mulr_addl -!addrA; congr (_ + _).
by rewrite addrC [_ + D c]addrC -mulrA [_ * x]mulrC mulrA addrA.
Qed.

End DerivationAlgebra.

Section MoreSubalgebra.

Variable K : {algebra L}.

Lemma memv_inv : forall x, (x \in K) = (x^-1 \in K).
Proof.
move => x.
wlog: x / x \in K.
 by move => H; apply/idP/idP => ?; [|rewrite -[x]invrK]; rewrite -H.
move => xK.
rewrite xK.
symmetry;apply/idP.
have xED : x ^+ elementDegree F x \in Fadjoin F x.
 by apply: memXED_Fadjoin_subproof.
have: (Fadjoin F x <= K)%VS.
 by rewrite -subsetFadjoinE_subproof // xK sub1v. 
move/subvP; apply.
case (eqVneq x 0) => [->|nzx]; first by rewrite invr0 mem0v.
move: (size_minPoly F x) (nzx) (root_minPoly_subproof xED).
rewrite -(minPoly_coef0_subproof xED) /root horner_coef.
move => -> c0.
rewrite big_ord_recl -(can_eq (mulVKf c0)) mulr0 mulr_addr (mulKf c0) expr0
        -(can_eq (mulfVK nzx)) mul0r mulr_addl mul1r eq_sym -subr_eq add0r.
move/eqP <-.
rewrite memvN // -mulrA.
move: c0.
have: (minPoly F x)`_0 \in F by move/polyOverP: (minPolyOver F x); apply.
case/injvP => k ->.
case: (eqVneq k 0); first by move ->; rewrite scale0r eq_refl.
move => k0 _.
rewrite scaler_inv ?unitr1 ?unitfE // invr1 -scaler_mull mul1r memvZl //
        -mulr_suml memv_sumr // => i _.
rewrite exprSr mulrA (mulfK nzx) memv_prod ?memv_inj //.
by move/polyOverP: (minPolyOver F x).
Qed.

Lemma memv_invl : forall x, x \in K -> x^-1 \in K.
Proof. by move => x; rewrite memv_inv. Qed.

Definition suba_inv (x : suba_of K) : suba_of K := 
 Suba (memv_invl (subaP x)).

Lemma suba_fieldAxiom : GRing.Field.axiom suba_inv.
Proof.
move => x nzx.
apply: suba_inj.
by rewrite /= mulVf // aunit_eq1.
Qed.

Lemma suba_inv0 : suba_inv 0 = 0.
Proof. by apply: suba_inj; rewrite /= invr0. Qed.

Canonical Structure suba_UnitRingType :=
  Eval hnf in UnitRingType (suba_of K)
              (FieldUnitMixin suba_fieldAxiom suba_inv0).

Canonical Structure suba_comUnitRingType :=
  Eval hnf in [comUnitRingType of (suba_of K)].

Canonical Structure suba_idomainType :=
  Eval hnf in IdomainType (suba_of K) 
              (FieldIdomainMixin
               (@FieldMixin _ _ suba_fieldAxiom suba_inv0)).

Canonical Structure suba_fieldType :=
  Eval hnf in FieldType (suba_of K) 
               (@FieldMixin _ _ suba_fieldAxiom suba_inv0).

(*:TODO: FieldExtType *)

Lemma divp_polyOver : forall p q : {poly L},
  polyOver K p -> polyOver K q -> polyOver K (p %/ q).
Proof.
move => ? ?.
move/polyOver_suba => [p ->].
move/polyOver_suba => [q ->].
apply/polyOver_suba.
exists (p %/ q).
by rewrite map_divp.
Qed.

Lemma modp_polyOver : forall p q : {poly L},
  polyOver K p -> polyOver K q -> polyOver K (p %% q).
Proof.
move => ? ?.
move/polyOver_suba => [p ->].
move/polyOver_suba => [q ->].
apply/polyOver_suba.
exists (p %% q).
by rewrite map_modp.
Qed.

Lemma scalp_polyOver : forall p q : {poly L},
  polyOver K p -> polyOver K q -> (lead_coef p ^+ scalp p q) \in K.
Proof.
move => ? ?; move/polyOver_suba => [p ->]; move/polyOver_suba => [q ->].
by rewrite scalp_map // memv_exp // lead_coef_map // subaP.
Qed.

Lemma gcdp_polyOver : forall p q : {poly L},
  polyOver K p -> polyOver K q -> polyOver K (gcdp p q).
Proof.
move => ? ?; move/polyOver_suba => [p ->]; move/polyOver_suba => [q ->].
by apply/polyOver_suba; exists (gcdp p q); rewrite gcdp_map.
Qed.

Lemma mulmx_matrixOver n m o (A : 'M_(n,m)) (B : 'M_(m,o)) :
  matrixOver K A -> matrixOver K B -> matrixOver K (A *m B).
Proof.
move/matrixOverP => HA.
move/matrixOverP => HB.
apply/matrixOverP => i j.
rewrite mxE memv_suml // => k _.
by rewrite memv_mul.
Qed.

Lemma invmx_matrixOver n (A : 'M_n) :
  matrixOver K A = matrixOver K (invmx A).
Proof.
wlog suff: A / (matrixOver K A -> matrixOver K (invmx A)).
 move => Hsuff.
 move: (Hsuff A) (Hsuff (invmx A)).
 rewrite invmxK.
 case: (matrixOver K A); first by move/(_ isT) ->.
 case: (matrixOver K (invmx A)); last done.
 by move => _ /(_ isT) ->.
case/matrixOver_suba => B ->.
rewrite -map_invmx.
apply/matrixOver_suba.
by exists (invmx B).
Qed.

End MoreSubalgebra.

Section MoreFadjoin.

Variable (K : {algebra L}).
Variable (x : L).

Lemma XED_subproof : x ^+ (elementDegree K x) \in (Fadjoin K x).
case: (eqVneq x 0).
 move ->.
 by rewrite exprS mul0r mem0v.
rewrite (capv_KxED_subproof K).
rewrite -vpick0.
set W := (_ :&: _)%VS.
move: (memv_pick W).
rewrite memv_cap.
case/andP.
move/memv_prodv_inj_coef ->.
set k := (_ / _) => Hk.
have: (k \in K).
 move: (memv_pick W).
 rewrite memv_cap.
 case/andP.
 by move/prodv_inj_coefK.
rewrite memv_inv mulf_eq0 negb_or => Hkinv.
case/andP => nzk _.
rewrite -[x ^+ _](mulKf nzk).
apply/memv_sumP.
case/memv_sumP: Hk => v_ [Hv_1 Hv_2].
exists (fun i => k^-1 * v_ i); split; last by rewrite Hv_2 mulr_sumr.
move => i _.
move/(_ i isT): Hv_1 => Hv_1.
move/memv_prodv_inj_coef: (Hv_1) ->.
by rewrite mulrA memv_prod ?memv_inj // memv_mul // prodv_inj_coefK.
Qed.

Lemma root_minPoly : root (minPoly K x) x. 
Proof. by rewrite root_minPoly_subproof // XED_subproof. Qed.

Lemma minPolyxx : (minPoly K x).[x] = 0.
Proof. by move: root_minPoly; rewrite /root; move/eqP ->. Qed.

Lemma poly_Fadjoin : forall v,
 reflect (exists p, polyOver K p /\ v = p.[x])
         (v \in (Fadjoin K x)).
Proof.
move => v.
apply: (iffP (poly_Fadjoin_small _ _ _)).
 by case => p [? [? ?]]; exists p.
case => p [Kp ->].
move: {2}(size p).+1 (ltnSn (size p)) Kp => n.
elim: n p => //.
move => n IH p szp.
case: (leqP (size p) (elementDegree K x)) => szpx.
 by exists p.
move/ltn_predK: (szpx) (szpx) <-.
rewrite ltnS => szpx0.
move/polyOverP => Kp.
case/poly_Fadjoin_small: XED_subproof => r; case.
move/polyOverP => Kr [szr rxED].
set q := (\poly_(i < (size p).-1) (p`_i)) + 
         (p`_(size p).-1)%:P * r * 'X ^+ ((size p).-1 - elementDegree K x).
have -> : (p.[x] = q.[x]).
 rewrite !(horner_lin,horner_mul).
 by rewrite -rxED hornerXn -mulrA -exprn_addr subnKC // horner_poly horner_coef
            -(ltn_predK szpx) /= big_ord_recr.
apply IH; last first.
 apply/polyOverP => i.
 by rewrite coefD coef_poly -mulrA coefCM coefMXn !(fun_if, if_arg)
            !(mulr0, add0r, addr0) !(mem0v, memvD, memv_mul) ?Kp ?Kr ?if_same.
case: n szp szpx {IH}.
 rewrite ltnS leqn0.
 by move/eqP ->.
move => n szp szpx.
rewrite ltnS.
apply: (leq_trans (size_add _ _)).
rewrite leq_maxl.
apply/andP; split.
 apply: (leq_trans (size_poly _ _)).
 by rewrite -2!ltnS -ltnS (ltn_predK szpx).
rewrite -mulrA.
case: (eqVneq (p`_(size p).-1) 0).
 by move ->; rewrite mul0r size_poly0.
move/size_polyC_mul ->.
apply (leq_trans (size_mul _ _)).
rewrite size_polyXn addnS.
move: szp.
rewrite -{1}(ltn_predK szpx) !ltnS /=.
move/(leq_trans _); apply.
by rewrite -{2}(@subnKC (elementDegree K x) (size p).-1) ?leq_add2r.
Qed.

Lemma Fadjoin_is_aspace : let Kx := Fadjoin K x in
 (has_aunit Kx  && (Kx * Kx <= Kx)%VS).
Proof.
apply/andP; split.
 apply: has_aunit1.
 apply/poly_Fadjoin.
 exists 1;split; last by rewrite horner_lin.
 apply/polyOverP => i.
 rewrite coefC.
 by case: ifP; rewrite ?mem0v ?mem1v.
apply/prodvP => ? ?.
case/poly_Fadjoin => p1 [Hp1 ->].
case/poly_Fadjoin => p2 [Hp2 ->].
apply/poly_Fadjoin.
exists (p1 * p2); rewrite horner_mul; split => //.
by apply: mulp_polyOver.
Qed.

Canonical Structure Fadjoin_aspace : {algebra L} := ASpace Fadjoin_is_aspace.

Lemma subsetFadjoinE: forall E : {algebra L},
   (K <= E)%VS && (x \in E) = (Fadjoin K x <= E)%VS.
Proof. by move => E; rewrite subsetFadjoinE_subproof // XED_subproof. Qed.

Lemma memx_Fadjoin : x \in Fadjoin K x.
Proof.
by move: (subv_refl (Fadjoin K x)); rewrite -subsetFadjoinE; case/andP.
Qed.

Lemma subsetKFadjoin : (K <= Fadjoin K x)%VS.
Proof.
by move: (subv_refl (Fadjoin K x)); rewrite -subsetFadjoinE; case/andP.
Qed.

Lemma memK_Fadjoin : forall y, y \in K -> y \in Fadjoin K x.
Proof.
by move/subvP: subsetKFadjoin.
Qed.

Lemma mempx_Fadjoin : forall p, polyOver K p -> p.[x] \in Fadjoin K x.
Proof. move => p pK; apply/poly_Fadjoin; by exists p. Qed.

Lemma poly_for_K : forall v, v \in K -> poly_for_Fadjoin K x v = v%:P.
Proof.
move => v vK.
apply (@poly_Fadjoin_small_uniq _ _ K x).
    by apply: poly_for_polyOver.
   by apply: polyOverC.
  by apply: size_poly_for.
 by rewrite size_polyC (leq_trans (leq_b1 _)).
rewrite hornerC poly_for_eq //.
by apply: memK_Fadjoin.
Qed.

Lemma poly_for_modp : forall p, polyOver K p ->
 poly_for_Fadjoin K x p.[x] = p %% minPoly K x.
Proof.
move => p Pk.
apply (@poly_Fadjoin_small_uniq _ _ K x).
    by apply: poly_for_polyOver.
   by rewrite modp_polyOver // minPolyOver.
  by apply: size_poly_for.
 by rewrite -ltnS -size_minPoly ltn_modp // -size_poly_eq0 size_minPoly.
 rewrite poly_for_eq ?mempx_Fadjoin //.
by rewrite {1}(divp_eq p (minPoly K x)) horner_add horner_mul
           minPolyxx mulr0 add0r.
Qed.

Lemma elemDeg1 : (x \in K) = (elementDegree K x == 1%N).
Proof.
apply/idP/eqP.
 apply: elemDeg1_subproof.
move => ed1.
suff <-: (Fadjoin K x = K) by apply: memx_Fadjoin.
symmetry; apply/eqP.
by rewrite -(dimv_leqif_eq subsetKFadjoin) dim_Fadjoin ed1 muln1.
Qed.

Lemma FadjoinxK : (x \in K) = (Fadjoin K x == K).
Proof.
rewrite elemDeg1.
apply/eqP/eqP.
 move => ed1.
 apply: subv_anti.
 by rewrite -dimv_leqif_sup subsetKFadjoin // dim_Fadjoin ed1 muln1 andbT.
move => Fadjoin_eq_K.
move/eqP: (dim_Fadjoin K x).
rewrite Fadjoin_eq_K -{1}[\dim K]muln1 eqn_mul2l dimv_eq0.
case/orP; last by move/eqP ->.
move/eqP => K0.
case: (negP (@nonzero1r L)).
by rewrite -memv0 -K0 mem1v.
Qed.

Lemma size_elementDegree : forall p, polyOver K p -> 
 size p <= elementDegree K x -> root p x = (p == 0).
Proof.
move => p Kp szp.
rewrite /root.
apply/eqP/eqP => Hp; last by rewrite Hp horner0.
by apply: (@poly_Fadjoin_small_uniq _ _ K x); 
    rewrite ?polyOver0 ?size_poly0 ?horner0.
Qed. 

Lemma minPoly_irr : forall p, polyOver K p ->
 dvdp p (minPoly K x) -> (p %= minPoly K x) || (p %= 1).
Proof.
rewrite /dvdp.
move => p Kp.
move/eqP => pMin.
set (q := ((minPoly K x) %/ p)).
have Kq : (polyOver K q) by rewrite divp_polyOver // minPolyOver.
move: root_minPoly (size_minPoly K x).
have -> : (minPoly K x = q * p).
  by apply/eqP; rewrite eq_sym -dvdp_eq; apply/modp_eq0P.
move: q Kq => q Kq.
rewrite {pMin} /root horner_mul mulf_eq0 => pq0 szpq.
have nzp : (p != 0).
 move/eqP: szpq.
 apply: contraL.
 move/eqP ->.
 by rewrite mulr0 size_poly0.
have nzq : (q != 0).
 move/eqP: szpq.
 apply: contraL.
 move/eqP ->.
 by rewrite mul0r size_poly0.
wlog: q p Kp Kq nzp nzq szpq pq0 / (q.[x] == 0).
 case/orP: pq0 => [q0|p0].
  apply => //.
  by apply/orP; left.
 move: szpq.
 rewrite mulrC => szpq H.
 have: (q %= p * q) || (q %= 1).
  apply: H => //.
  by apply/orP; left.
 case/orP.
  rewrite -{1}[q]mul1r eqp_mul2r // eqp_sym => ->.
  by rewrite orbT.
 move/(eqp_mull p).
 by rewrite mulr1 [p * _]mulrC eqp_sym => ->.
move => qx0.
apply/orP; right.
have nzq' : size q != 0%N by rewrite size_poly_eq0.
rewrite -size_poly_eqp1 eqn_leq.
apply/andP; split; last by rewrite (polySpred nzp).
rewrite -(leq_add2r (size q)).
move: (size_mul_id nzp nzq); case: (_ + _)%N=> //= _ <-.
rewrite mulrC szpq ltnNge.
apply: contra nzq.
by move/(size_elementDegree Kq) <-.
Qed.

Lemma minPoly_dvdp : forall p, polyOver K p -> root p x -> (minPoly K x) %| p.
Proof.
move => p Kp rootp.
have gcdK : polyOver K (gcdp (minPoly K x) p).
 by rewrite gcdp_polyOver ?minPolyOver //.
have [gcd_eqK|gcd_eq1] := orP (minPoly_irr gcdK (dvdp_gcdl (minPoly K x) p)).
 by rewrite -(eqp_dvdl _ gcd_eqK) dvdp_gcdr.
case/negP: (root1 x).
by rewrite -(eqp_root gcd_eq1) root_gcd rootp root_minPoly.
Qed.

Lemma separableElementP :  
  reflect 
  (exists f, polyOver K f /\ root f x /\ separablePolynomial f) 
   (separableElement K x).
Proof.
apply: (iffP idP).
 move => ?; exists (minPoly K x); do ! (split => //).
  by apply: minPolyOver.
 by apply root_minPoly.
move => [f [fK []]].
move/(minPoly_dvdp fK) => /dvdpP=> [[g ->]].
rewrite  separable_mul.
by case/and3P.
Qed.

Lemma separableinK : x \in K -> (separableElement K x).
Proof.
move => Hx.
apply/separableElementP.
exists ('X - x%:P); repeat split.
  by rewrite addp_polyOver ?polyOverX // opp_polyOver // polyOverC.
 by rewrite root_factor_theorem dvdpp.
by rewrite /separablePolynomial !derivCE subr0 coprimep1.
Qed.

Lemma separable_nzdmp : (separableElement K x) = (deriv (minPoly K x) != 0).
Proof.
rewrite /separableElement /separablePolynomial.
apply/idP/idP.
 apply: contraL.
 move/eqP ->.
 by rewrite coprimep0 -size_poly_eqp1 size_minPoly eqSS -lt0n.
move => Hderiv.
have gcdl := (dvdp_gcdl (minPoly K x) (deriv (minPoly K x))).
have gcdK : polyOver K (gcdp (minPoly K x) (minPoly K x)^`()).
 by rewrite gcdp_polyOver ?deriv_polyOver // minPolyOver.
rewrite -gcdp_eqp1 -size_poly_eqp1 -dvdp1.
case/orP: (minPoly_irr gcdK gcdl); last first.
 rewrite /eqp.
 by case/andP.
rewrite /eqp dvdp_gcd dvdpp /=.
case/andP => _.
move/(leq_dvdp Hderiv) => Hsz.
move: (leq_trans Hsz (size_poly _ _)).
by rewrite size_minPoly ltnn.
Qed.

Lemma separableNXp : 
  reflect (exists2 p, p \in [char L] & 
            exists2 g, (polyOver K g) & (minPoly K x) = g \Po 'X^p)
          (~~ (separableElement K x)).
Proof.
rewrite separable_nzdmp negbK.
apply: (iffP eqP); last first.
 move => [p Hp [g _ ->]].
 by rewrite deriv_comp_poly derivXn -scaler_nat (charf0 Hp) scale0r mulr0.
move/eqP: (monic_minPoly K x).
set (f := minPoly K x) => Hlead Hdf.
have/eqP Hnz : (elementDegree K x)%:R = (0:L).
 rewrite -(coef0 _ ((size f).-2)) -Hdf coef_deriv size_minPoly.
 rewrite -[_.+1.-2.+1]/((elementDegree K x).+1.-1) -size_minPoly.
 rewrite -[elementDegree _ _]/((elementDegree K x).+1.-1) -size_minPoly.
 by rewrite [f`_ _]Hlead.
case: (natf0_char _ Hnz) => [//|p Hp].
exists p; first done.
rewrite -(dvdn_charf Hp) in Hnz.
move: (divnK Hnz).
set r := (_ %/ p)%N => Hrp.
exists (\poly_(i < r.+1) f`_(i * p)).
 rewrite poly_polyOver // => i.
 move: (i * p)%N.
 apply/polyOverP.
 by apply: minPolyOver.
rewrite comp_polyE size_poly_eq; last first.
 rewrite Hrp  -[elementDegree _ _]/((elementDegree K x).+1.-1) -size_minPoly.
 by rewrite [f`_(_)]Hlead nonzero1r.
apply/polyP => i.
rewrite coef_sum.
case Hpi: (p %| i)%N ;last first.
 transitivity (0:L).
  case: i Hpi => [|i Hpi]; first by rewrite dvdn0.
  rewrite -{2}(mul0r ((i.+1)%:R ^-1)) -{2}(coef0 _ i) -Hdf coef_deriv.
  by rewrite -mulr_natr mulfK // -(dvdn_charf Hp) Hpi.
 symmetry.
 apply: big1 => j _.
 rewrite coefZ -exprn_mulr coefXn.
 case: eqP Hpi => [->|]; last by rewrite mulr0.
 by rewrite (dvdn_mulr _ (dvdnn p)).
move: (divnK Hpi) <-.
set s := (i %/ p)%N.
have Hp0 : 0 < p by apply/prime_gt0/(@charf_prime L).
case: (leqP r.+1 s) => Hrs.
 transitivity (0:L).
  apply: nth_default.
  rewrite -(@prednK (size f)); last by rewrite size_minPoly.
  by rewrite size_minPoly -Hrp ltn_mul2r Hrs andbT.
 symmetry.
 apply: big1 => j _.
 rewrite coefZ -exprn_mulr coefXn.
 case: (eqVneq s j) => [Hsj|]; first by move: Hrs; rewrite Hsj ltnNge leq_ord.
 by rewrite mulnC eqn_mul2l => /negbTE->; rewrite eqn0Ngt Hp0 mulr0.
pose (s' := Ordinal Hrs).
rewrite (bigD1 s') // coefZ -exprn_mulr coefXn {2}mulnC eq_refl mulr1.
rewrite coef_poly Hrs mulnC big1 ?[_ _ 0]addr0 // => j /negPf.
rewrite eq_sym => Hj.
rewrite coefZ -exprn_mulr coefXn eqn_mul2l [s == j]Hj eqn0Ngt Hp0.
by rewrite mulr0.
Qed.

Lemma separableNrootdmp : 
  (separableElement K x) != (root (deriv (minPoly K x)) x).
Proof.
rewrite separable_nzdmp size_elementDegree.
  by case: (_ == 0).
 by rewrite deriv_polyOver // minPolyOver.
by rewrite (leq_trans (size_poly _ _)) // size_minPoly leqnn.
Qed.

Lemma DerivationSeparable : forall D, Derivation (Fadjoin K x) D -> 
 (separableElement K x) ->
 D x = - (map_poly D (minPoly K x)).[x] / ((minPoly K x)^`()).[x].
Proof.
move => D Dderiv.
move: separableNrootdmp.
rewrite negb_eqb addbC /root.
move/addbP => <- Hroot.
apply: (canRL (mulfK Hroot)).
rewrite -sub0r.
apply: (canRL (addrK _)).
rewrite mulrC addrC -(DerivationPoly Dderiv) ?memx_Fadjoin //; last first.
 by apply: (polyOver_subset subsetKFadjoin (minPolyOver _ _)).
by rewrite minPolyxx linear0.
Qed.

Section DerivationExtend.

Variable D:'End(L).

Let Dx E := - (map_poly D (minPoly E x)).[x] / ((minPoly E x)^`()).[x].

Let DerivationExtend_body E (D:'End(L)) (y:L) : L :=
 let p := (poly_for_Fadjoin E x y) in
 (map_poly D p).[x] + (p^`()).[x] * (Dx E).

Definition DerivationExtend E : 'End(L) :=
 lapp_of_fun (DerivationExtend_body E D).

Let DerivationExtend_body_linear : forall E,
  linear (DerivationExtend_body E D).
Proof.
move => E a u v.
rewrite /DerivationExtend_body.
move: Dx => C.
rewrite poly_is_linear -mul_polyC derivD derivM derivC mul0r add0r.
rewrite !horner_lin_comm -scaler_mull mul1r.
move : (poly_for_Fadjoin _ _ _) => pu.
move : (poly_for_Fadjoin _ _ _) => pv.
rewrite (_ : map_poly D ((a *: 1)%:P * pu + pv)
           = (a *: 1)%:P * map_poly D pu + map_poly D pv); last first.
  apply/polyP => i; rewrite !(coef_map [linear of D]) ?linear0 // !coefD.
  by rewrite  !{1}coefCM  !{1}(coef_map [linear of D]) ?{1}linear0 //= -!{1}scaler_mull
              !mul1r linearP.
by rewrite !{1}horner_lin_comm -scaler_mull mul1r mulr_addl scaler_addr 
           -scaler_mull -addrA [(_.[x] + _)]addrA [_ + (a *: (_ * _))]addrC /=
           !{1}addrA.
Qed.

Hypothesis HD: Derivation K D.

Lemma DerivationExtended : forall y, y \in K ->  DerivationExtend K y = D y.
Proof.
move => y yK.
rewrite lapp_of_funK; last by apply: DerivationExtend_body_linear.
rewrite /DerivationExtend_body poly_for_K // derivC horner0 mul0r addr0.
rewrite -[D y](hornerC _ x) /horner_morph.
congr (_.[x]).
apply/polyP => i.
by rewrite (coef_map [linear of D]) ?linear0 //= !coefC [D _]fun_if linear0.
Qed.

Lemma DerivationExtend_Poly : forall (p:{poly L}),
 polyOver K p -> (separableElement K x) ->
 DerivationExtend K (p.[x]) = (map_poly D p).[x] + p^`().[x] * Dx K.
Proof.
move => p Kp sep.
move: separableNrootdmp.
rewrite negb_eqb addbC /root sep addbT {sep} => sep.
rewrite lapp_of_funK; last by apply: DerivationExtend_body_linear.
rewrite {-1}(divp_eq p (minPoly K x)) /DerivationExtend_body.
rewrite poly_for_modp // /horner_morph (@Derivation_addp K)
        ?{1}(Derivation_mulp HD)
        ?{1}(mulp_polyOver, divp_polyOver, modp_polyOver, minPolyOver) //.
rewrite derivD derivM !{1}horner_add !{1}horner_mul minPolyxx !{1}mulr0 !{1}add0r.
rewrite mulr_addl addrA [_ + (_ * _ * _)]addrC {2}/Dx /horner_morph -mulrA -/Dx.
by rewrite [((minPoly K x)^`()).[x] * _]mulrC (mulfVK sep) mulrN addKr.
Qed.

Lemma DerivationExtendDerivation :
 (separableElement K x) -> Derivation (Fadjoin K x) (DerivationExtend K).
Proof.
move => sep.
apply/allP => u; move/memv_basis => Hu.
apply/allP => v; move/memv_basis => Hv.
apply/eqP.
rewrite -(poly_for_eq Hu) -(poly_for_eq Hv) -horner_mul !{1}DerivationExtend_Poly
        ?{1}mulp_polyOver ?{1}poly_for_polyOver // /horner_morph (Derivation_mulp HD)
        ?{1}poly_for_polyOver // derivM !{1}horner_add !{1}horner_mul !{1}mulr_addl 
        !{1}mulr_addr -!addrA; congr (_ + _).
move:Dx => Dx0.
rewrite -!{1}mulrA [(Dx0 _) * _]mulrC !{1}addrA; congr (_ + _).
by rewrite addrC.
Qed.

End DerivationExtend.

(* Reference: 
http://www.math.uconn.edu/~kconrad/blurbs/galoistheory/separable2.pdf *)
Lemma separableDerivationP :
  reflect (forall D, Derivation (Fadjoin K x) D ->
                     (K <= lker D)%VS -> (Fadjoin K x <= lker D)%VS)
          (separableElement K x).
Proof.
apply introP.
 move => sep D DD.
 move/subvP => K0.
 apply/subvP => ?.
 move/poly_Fadjoin => [p [Hp ->]].
 have HD0 : forall q, polyOver K q -> map_poly D q = 0.
  move => q.
  move/polyOverP => qK.
  apply/polyP => i.
  apply/eqP.
  by rewrite (coef_map [linear of D]) ?linear0 //= coef0 -memv_ker K0.
 by rewrite memv_ker (DerivationPoly DD) ?memx_Fadjoin 
         ?(polyOver_subset subsetKFadjoin Hp) // (DerivationSeparable DD sep)
         /horner_morph !HD0 ?minPolyOver // horner0 oppr0 mul0r mulr0 addr0.
move => nsep.
move: separableNrootdmp (nsep).
rewrite negb_eqb.
move/addbP ->.
rewrite /root; move/eqP => Hroot.
pose D_body y := ((poly_for_Fadjoin K x y)^`()).[x].
have Dlin : linear D_body.
 move => a u v.
 by rewrite /D_body poly_is_linear -mul_polyC derivD derivM derivC mul0r
            add0r horner_add horner_mul hornerC -scaler_mull mul1r.
pose D := lapp_of_fun D_body.
have DF : (K <= lker D)%VS.
 apply/subvP => v vK.
 by rewrite memv_ker lapp_of_funK // /D //= /D_body poly_for_K // derivC 
            horner0.
have DDeriv : Derivation (Fadjoin K x) D.
 apply/allP => u; move/memv_basis => Hu.
 apply/allP => v; move/memv_basis => Hv.
 by rewrite !lapp_of_funK // /D //= /D_body -{-2}(poly_for_eq Hu)
            -{-3}(poly_for_eq Hv) -!horner_mul -horner_add -derivM 
            poly_for_modp ?mulp_polyOver ?poly_for_polyOver // 
            {2}(divp_eq (_ * _) (minPoly K x)) derivD derivM
            !horner_add !horner_mul Hroot minPolyxx !mulr0 !add0r.
have Dx : D x = 1.
 rewrite !lapp_of_funK // /D //= /D_body.
 rewrite (_ : (poly_for_Fadjoin K x x) = 'X) ?derivX ?hornerC //.
 apply: (@poly_Fadjoin_small_uniq _ _ K x).
     apply: poly_for_polyOver.
    apply: polyOverX.
   apply: size_poly_for.
  rewrite size_polyX ltn_neqAle andbT eq_sym.
  apply: contra nsep.
  move/eqP => eD.
  rewrite separable_nzdmp (_ : (minPoly K x)^`() = 1%:P)  ?nonzero1r //.
  apply/polyP => i.
  rewrite coef_deriv coefC.
  case: i => [|i].
   move: (monic_minPoly K x); rewrite /monic lead_coefE size_minPoly eD.
   by move/eqP ->.
  rewrite (_ : (minPoly K x)`_i.+2 = 0) ?mul0rn //.
   move: (leqnn (size (minPoly K x))); rewrite {2}size_minPoly eD.
   by move/leq_sizeP->.
 by rewrite hornerX (poly_for_eq memx_Fadjoin).
move/(_ _ DDeriv DF).
apply/negP.
move/eqP: Dx.
apply: contraL.
move/subvP.
move/(_ _ memx_Fadjoin).
rewrite memv_ker.
move/eqP ->.
rewrite eq_sym.
by apply: nonzero1r.
Qed.

End MoreFadjoin.

Implicit Types K E : {algebra L}.

Lemma subsetSeparable : forall K E x, (K <= E)%VS -> 
 separableElement K x -> separableElement E x.
Proof.
move => K E x KE.
move/separableElementP => [f [fK [rootf sepf]]].
apply/separableElementP.
exists f; split => //.
by apply: (polyOver_subset KE).
Qed.

Lemma allSeparableElement : forall K x,
  reflect (forall y, y \in Fadjoin K x -> separableElement K y)
          (separableElement K x).
Proof.
move => K x.
apply: (iffP idP); last by apply; apply: memx_Fadjoin.
move => sep ?.
move/poly_Fadjoin => [q [Hq ->]].
apply/separableDerivationP => D DD.
move/subvP => KD0.
apply/subvP => ?.
move/poly_Fadjoin => [p [Hp ->]].
rewrite memv_ker -(DerivationExtended x D (mempx_Fadjoin _ Hp)).
have sepFyx : (separableElement (Fadjoin K (q.[x])) x).
 by apply: (subsetSeparable (subsetKFadjoin _ _)).
have KyxEqKx : (Fadjoin (Fadjoin K (q.[x])) x = Fadjoin K x).
 (* apply/eqP. *)
 (* change (Fadjoin (Fadjoin K q.[x]) x == Fadjoin K x :> {vspace L}). *)
 (* apply/eqP. *)
 apply: subv_anti.
 rewrite -!{1}subsetFadjoinE mempx_Fadjoin //=.
 rewrite {1}subsetKFadjoin (subv_trans _ (subsetKFadjoin _ _)).
    by rewrite !{1}memx_Fadjoin.
 by rewrite subsetKFadjoin.
rewrite -horner_comp_poly.
move: (DerivationExtendDerivation DD sepFyx).
rewrite KyxEqKx => DED.
rewrite (DerivationPoly DED); last first.
  apply: memx_Fadjoin.
 apply: (polyOver_subset (subsetKFadjoin _ _)).
 by apply: compose_polyOver.
suff hmD : forall t, polyOver K t ->
           (map_poly (DerivationExtend x D (Fadjoin K q.[x])) t).[x] = 0.
 rewrite (DerivationSeparable DED); last done.
 rewrite !{1}hmD; first by rewrite oppr0 mul0r mulr0 addr0.
  by apply: minPolyOver.
 by apply: compose_polyOver.
move => t.
move/polyOverP => Ht.
rewrite /horner_morph (_ : map_poly _ _ = 0); first by rewrite horner0.
apply/polyP => i.
rewrite coef0 {1}(coef_map [linear of (DerivationExtend _ _ _)]).
rewrite /= {1}DerivationExtended.
 apply/eqP.
 by rewrite -memv_ker KD0.
apply: (subv_trans _ (subsetKFadjoin _ _)).
by apply: Ht.
Qed.

Lemma FadjoinC : forall x y K,
  Fadjoin (Fadjoin K x) y = Fadjoin (Fadjoin K y) x.
Proof.
suff : forall (x y : L) (K : {algebra L}),
 (Fadjoin (Fadjoin K x) y <= Fadjoin (Fadjoin K y) x)%VS.
 move => H x y K.
 by apply:subv_anti; apply/andP; split.
move => x y K.
rewrite -!subsetFadjoinE memx_Fadjoin memK_Fadjoin ?memx_Fadjoin //.
rewrite (@subv_trans _ _ (Fadjoin K y)); first done;
  by rewrite subsetKFadjoin.
Qed.

Lemma subsetFadjoin : forall x (K E : {algebra L}), 
  (K <= E)%VS -> (Fadjoin K x <= Fadjoin E x)%VS.
Proof.
move => x K E HKE.
apply/subvP => y.
case/poly_Fadjoin => p [Hp ->].
apply: mempx_Fadjoin.
by apply: (polyOver_subset HKE).
Qed.

Section SeparableInCharP.

Variable (K : {algebra L}).

Lemma separablePower : forall x, 
 exists n, [char L].-nat n && separableElement K (x ^+ n).
Proof.
move => x.
move: {2}(elementDegree K x) (leqnn (elementDegree K x)) => n.
elim: n x => [//|n IHn] x.
move => Hdeg.
case Hsep : (separableElement K x); first by exists 1%N.
case/negbT/separableNXp : Hsep => p Hp [g HKg Hg].
suff: elementDegree K (x ^+ p) <= n.
 case/IHn => m; case/andP => Hm.
 rewrite -exprn_mulr => Hsepxpm.
 exists (p * m)%N => //.
 by rewrite pnat_mul pnatE ?(charf_prime Hp) // Hp Hm.
rewrite -ltnS (leq_trans _ Hdeg) // -size_minPoly -ltnS -size_minPoly.
apply: (@leq_ltn_trans (size g)).
 apply: leq_dvdp; last first.
  apply: minPoly_dvdp => //.
  by rewrite /root -hornerXn -horner_comp_poly -Hg minPolyxx.
 move/eqP: Hg.
 apply: contraL.
 move/eqP ->.
 by rewrite poly_com0p -size_poly_eq0 size_minPoly.
rewrite -[size (minPoly K x)](prednK); last by rewrite size_minPoly.
rewrite Hg size_comp_poly_id ltnS.
rewrite size_polyXn.
case: (leqP (size g) 1) Hg.
 move/size1_polyC ->.
 rewrite poly_comCp => Hg.
 have : size (minPoly K x) <= 1 by rewrite Hg size_polyC leq_b1.
 by rewrite size_minPoly ltnS leqNgt.
move => Hszg _.
rewrite -{1}(prednK (ltnW Hszg)) -subn_gt0.
rewrite -(prednK (prime_gt0 (charf_prime Hp))) mulnS addKn muln_gt0 -!subn1.
by rewrite !subn_gt0 Hszg (prime_gt1 (charf_prime Hp)).
Qed.

Lemma separableChar0 : [char L] =i pred0 -> forall x, separableElement K x.
Proof.
move => Hchar x.
case: (separablePower x) => n.
rewrite (eq_pnat _ Hchar) {Hchar}.
case/andP => Hchar.
rewrite (pnat_1 Hchar); first by rewrite expr1.
apply/pnatP => //.
by case/andP: Hchar.
Qed.

Lemma separableCharp : forall x e p, p \in [char L] ->
 separableElement K x = (x \in Fadjoin K (x ^+ (p ^ e.+1))).
Proof.
move => x e p Hp.
apply/idP/idP; last first.
 move/poly_for_eq.
 set (f := (poly_for_Fadjoin K (x ^+ (p ^ e.+1)) x)).
 move => Hx.
 apply/separableElementP.
 exists ('X - (f \Po 'X^(p ^ e.+1))); split.
  by rewrite addp_polyOver ?opp_polyOver ?compose_polyOver ?exp_polyOver
             ?polyOverX ?poly_for_polyOver.
 split.
  by rewrite /root !horner_lin horner_comp_poly hornerXn Hx subrr.
 rewrite /separablePolynomial !(derivE, deriv_comp_poly).
 have : (p %| p ^ e.+1)%N by rewrite dvdn_exp.
 rewrite -mulr_natr (dvdn_charf Hp) -polyC_natmul.
 move/eqP ->.
 by rewrite polyC0 !mulr0 subr0 coprimep1.
wlog: e x / e = 0%N.
 move => H.
 elim: e.+1; first by rewrite expr1 memx_Fadjoin.
 move => {e} e IH Hsep.
 rewrite expnS mulnC exprn_mulr -{2}[p]expn1.
 have : (Fadjoin K (x ^+ (p ^ e)) <= Fadjoin K (x ^+ (p ^ e) ^+ (p ^ 1)))%VS.
  move/allSeparableElement: Hsep => Hsep.
  by rewrite -subsetFadjoinE subsetKFadjoin H ?Hsep ?memv_exp ?memx_Fadjoin.
 move/subvP; apply.
 by apply IH.
move => -> {e}.
set (K' := Fadjoin_aspace K (x ^+ p)).
set (g := 'X^p - (x ^+ p)%:P).
have HK'g : polyOver K' g.
 by rewrite addp_polyOver ?exp_polyOver ?polyOverX // opp_polyOver // polyOverC
            // memx_Fadjoin.
have rootg : root g x by rewrite /root !horner_lin hornerXn subrr.
move/(subsetSeparable (subsetKFadjoin _ (x ^+ p))).
move : (root_minPoly K' x) (minPoly_dvdp HK'g rootg) (minPolyOver K' x).
rewrite root_factor_theorem /separableElement -/K'.
case/(dvdpP) => c -> Hcg HK'c.
rewrite separable_mul.
have Hp' : p \in [char {poly L}] by apply: (rmorph_char (polyC_rmorphism _)).
case/and3P => _ _ Hc.
 have : (coprimep c g).
 rewrite /g polyC_exp -!(Frobenius_autE Hp') -rmorph_sub.
 rewrite [_ (_ - _)]Frobenius_autE -(prednK (prime_gt0 (charf_prime Hp))).
 elim: p.-1 => [|n]; first by rewrite expr1.
 by rewrite [_ ^+ _.+2]exprS coprimep_mulr Hc.
move/coprimepP/(_ _ (dvdpp c))/(_ (dvdp_trans (dvdp_mulr _ (dvdpp c)) Hcg)).
rewrite -size_poly_eqp1.
move/eqP => Hszc.
move: HK'c (Hszc).
rewrite (size1_polyC (eq_leq Hszc)) size_polyC mulr_addr -polyC_opp -polyC_mul.
move/polyOverP => Hx.
move: (Hx 1%N) (Hx 0%N).
rewrite !coefD !coefMX !coefC add0r addr0 => Hx1 Hx0.
case Hc0 : (c`_0 != 0) => // _.
by rewrite memvNl // -[(- x)](mulKf Hc0) memv_mul // -memv_inv.
Qed.

Lemma separableCharn : forall x n, n \in [char L].-nat ->
 1 < n -> separableElement K x = (x \in Fadjoin K (x ^+ n)).
Proof.
move => x n Hn H1n.
set (p := pdiv n).
have Hcharp : p \in [char L].
 move/pnatP : Hn; apply; first by apply ltnW.
  by rewrite pdiv_prime.
 by rewrite pdiv_dvd.
move/charf_eq/(eq_pnat n): (Hcharp) => Hp.
have: p.-nat n by rewrite -Hp.
case/p_natP => e He.
move: (H1n).
rewrite He -[1%N](expn0 p) ltn_exp2l // ?prime_gt1 // ?pdiv_prime //.
move/prednK <-.
by apply: separableCharp.
Qed.

End SeparableInCharP.

Definition purelyInseparableElement (K0 : {vspace L}) x :=
  if insub K0 is Some K then x ^+ (ex_minn (separablePower K x)) \in K
  else false.

Section PurelyInseparableElement.

Variable K : {algebra L}.

Lemma purelyInseparableElementP : forall x, reflect 
 (exists2 n, [char L].-nat n & x ^+ n \in K)
 (purelyInseparableElement K x).
Proof.
move => x.
rewrite /purelyInseparableElement valK.
case: ex_minnP => n.
case/andP => Hn Hsepn Hmin.
apply: (iffP idP); first by move => Hx; exists n.
case => m Hm Hxm.
move/separableinK/(conj Hm)/andP/Hmin: (Hxm).
rewrite {Hmin} leq_eqVlt.
case/orP => [|Hnm]; first by move/eqP ->.
set (p := pdiv m).
have Hp : p \in [char L].
 move/pnatP: Hm; apply; rewrite ?pdiv_prime ?pdiv_dvd //.
  by apply: (leq_trans _ Hnm).
 apply: (leq_trans _ Hnm).
 rewrite ltnS.
 by case/andP: Hn.
move: Hn Hm Hsepn Hnm Hxm.
rewrite !(eq_pnat _ (charf_eq Hp)).
case/p_natP => en ->.
case/p_natP => em ->.
rewrite (separableCharp _ _ (em - en.+1)%N Hp) => Hsepn.
rewrite ltn_exp2l; last by apply/prime_gt1/(charf_prime Hp).
move/subnKC <-.
rewrite addSnnS expn_add exprn_mulr FadjoinxK.
by move/eqP <-.
Qed.

(*
Lemma purelyInseparableElementP : forall x, reflect 
 (forall n, [char L].-nat n -> separableElement K (x ^+ n) -> x ^+ n \in K)
 (purelyInseparableElement x).
Proof.
move => x.
rewrite /purelyInseparableElement.
case: ex_minnP => n.
case/andP => Hn Hsepn Hmin.
apply: (iffP idP); last by apply.
move => Hk m Hm Hsepm.
move/andP/Hmin: (conj Hm Hsepm) => Hnm.
rewrite -(@divnK n m); first by rewrite mulnC exprn_mulr memv_exp.
apply/dvdn_partP; first by case/andP: Hn.
move => p.
move/(pnatPpi Hn) => Hp.
rewrite p_part pfactor_dvdn; [|by apply: (charf_prime Hp)|by case/andP: Hm].
rewrite -(@leq_exp2l p); last by apply/prime_gt1/(charf_prime Hp).
by rewrite -!p_part !part_pnat_id // -(eq_pnat _ (charf_eq Hp)).
Qed.
*)

Lemma separableInseparableElement: forall x, 
 (x \in K) = separableElement K x && purelyInseparableElement K x.
Proof.
move => x.
rewrite /purelyInseparableElement valK.
case: ex_minnP => [[//|[|m]]]; first by rewrite expr1; case/andP => _ ->.
case/andP => Hm Hsep.
move/(_ 1%N).
rewrite expr1.
move/contraNN.
rewrite -ltnNge -[_ && _]/(separableElement K x).
move/(_ isT) => Hx.
move/negbTE: (Hx) ->.
apply/negbTE.
move:Hx.
apply: contra.
by apply: separableinK.
Qed.

Lemma inseparableinK : forall x, x \in K -> purelyInseparableElement K x.
Proof. move => x. rewrite separableInseparableElement. by case/andP. Qed.

End PurelyInseparableElement.

Lemma subsetInseparable:
  forall (K E : {algebra L}) (x : L),
  (K <= E)%VS -> purelyInseparableElement K x -> purelyInseparableElement E x.
Proof.
move => K E x.
move/subvP => HKE.
case/purelyInseparableElementP => n Hn Hxn.
apply/purelyInseparableElementP.
exists n => //.
by apply HKE.
Qed.

Section PrimitiveElementTheorem.

Variable K : {algebra L}.
Variable x y : L.

Let n := (elementDegree K x).
Let m := (elementDegree K y).-1.

Let f := minPoly K x.
Let g := minPoly K y.

Section FiniteCase.

Variable N : nat.

Let KisBig := exists l, [&& (all (mem K) l), uniq l & (N < size l)].

Lemma cyclicOrBig : forall z:L, z != 0 -> KisBig \/ exists a, z ^+ (a.+1) = 1.
Proof.
move => z Hz.
pose d := elementDegree K z.
pose h0 := fun (i:'I_(N ^ d).+1) (j:'I_d) => (poly_for_Fadjoin K z (z^+i))`_j.
pose l := allpairs h0 (ord_enum _) (ord_enum _).
pose Cs := seq_sub_finType l.
case: (leqP (#|Cs|) N) => [leN|ltN];last first;[left|right].
 exists (map val (enum Cs)).
 rewrite size_map -cardT ltN.
 rewrite map_inj_in_uniq ?enum_uniq; last by move => ? ? _ _; apply: val_inj.
 rewrite !andbT.
 apply/allP => ?; case/mapP => w _ ->.
 move: {w} (val w) (valP w) => w.
 rewrite /l /h0.
 case/allpairsP => [[i j] [_ _ ->]] /=.
 by move/polyOverP: (poly_for_polyOver K z (z ^+ i)).
have Hh0 : forall i j, h0 i j \in mem l.
 rewrite mem_mem.
 move => i j.
 rewrite /l.
 apply/allpairsP.
 by exists (i,j); split; rewrite ?mem_ord_enum.
pose h := fun i => [ffun j => (SeqSub (Hh0 i j):Cs)].
have: #|h @: 'I_(N ^ d).+1| != #|'I_(N ^ d).+1|.
 rewrite neq_ltn.
 apply/orP; left.
 rewrite card_ord ltnS (leq_trans (max_card _)) // card_ffun card_ord.
 by rewrite leq_exp2r // elementDegreegt0.
move/imset_injP => Hh.
have: ~injective h by move => H; apply: Hh => i j _ _; apply: H.
move/injectiveP; move/injectivePn => [a1 [a2 Ha Hha]].
exists `|a1 - a2|.-1.
rewrite prednK ?lt0n ?distn_eq0 // {Ha}.
move: Hha.
wlog Ha : a1 a2 / a1 <= a2.
 move => HW.
 case/orP: (leq_total a1 a2); first by apply: HW.
 move => Ha Hha. (*why can't I do move/sym_eq*)
 move: (sym_eq Hha).
 rewrite distnC.
 by apply: HW.
move/ffunP.
rewrite (distnEr Ha) => Hha.
have Hza: (z ^+ a1 != 0) by exact: expf_neq0.
apply/eqP.
rewrite -(can_eq (mulfK Hza)) -exprn_addr mul1r subnK //.
apply/eqP; symmetry.
have Hzi : forall i,  z ^+ i \in Fadjoin K z.
 by move => i; apply: memv_exp; exact: memx_Fadjoin.
move/poly_for_eq:(Hzi a1) <-.
move/poly_for_eq:(Hzi a2) <-.
have Z:=(horner_coef_wide z (size_poly_for K z (z ^+ _))).
(* Why is this so slow? rewrite (Z a1) (Z a2). *)
rewrite !{1}Z.
apply: eq_bigr => i _.
apply: f_equal2; last done.
move: (Hha i).
rewrite /h !ffunE.
by move/(f_equal val) => /=.
Qed.

Lemma PET_finiteCase_subproof : 
  KisBig \/ exists z, Fadjoin (Fadjoin K y) x = Fadjoin K z.
Proof.
case (eqVneq x 0) => [->|Hx0].
 right; exists y.
 apply/eqP.
 rewrite -FadjoinxK.
 by apply: mem0v.
move/cyclicOrBig: (Hx0) => [|[[|a] Hxa]]; first by left.
 rewrite expr1 in Hxa.
 right; exists y.
 apply/eqP.
 rewrite -FadjoinxK Hxa.
 by apply: mem1v.
case (eqVneq y 0) => [->|Hy0].
 right; exists x.
 move: (mem0v K).
 rewrite FadjoinxK.
 by move/eqP ->.
move/cyclicOrBig: (Hy0) => [|[[|b] Hyb]]; first by left.
 rewrite expr1 in Hyb.
 right; exists x.
 move: (mem1v K).
 rewrite FadjoinxK Hyb.
 by move/eqP ->.
right.
pose h0 := fun (i:'I_a.+2) (j:'I_b.+2) => x ^+ i * y ^+ j.
pose l := allpairs h0 (ord_enum _) (ord_enum _).
pose fT := seq_sub_finType l.
have Hl : forall i j, x ^+ i * y ^+ j \in l.
 move => i j.
 rewrite (divn_eq i (a.+2)) (divn_eq j (b.+2)).
 rewrite !exprn_addr ![(_ * _.+2)%N]mulnC !exprn_mulr.
 rewrite Hxa Hyb !exp1rn !mul1r.
 apply/allpairsP.
 exists (Ordinal (@ltn_pmod i (a.+2) (ltn0Sn _))
        ,Ordinal (@ltn_pmod j (b.+2) (ltn0Sn _)));
  split; by rewrite ?mem_ord_enum.
have HmulgT : forall (i j:fT), (val i) * (val j) \in l.
 case => ? /=; move/allpairsP => [[ix iy] [_ _ ->]].
 case => ? /=; move/allpairsP => [[jx jy] [_ _ ->]].
 rewrite /h0 /=.
 rewrite -mulrA [y ^+ iy * _]mulrA [y ^+ iy * _]mulrC -mulrA mulrA.
 by rewrite -!exprn_addr.
pose mulgT := fun (i j:fT) => SeqSub (HmulgT i j):fT.
have HonegT : 1 \in l.
 by rewrite -[1]mulr1 -{1}(expr0 x) -(expr0 y).
pose onegT := SeqSub (HonegT):fT.
have HinvT : forall i:fT, (val i)^-1 \in l.
 case => ? /=; move/allpairsP => [[ix iy] [_ _ ->]].
 rewrite /h0 /=.
 rewrite invf_mul.
 rewrite -[x ^- ix]mul1r -Hxa -{1}[a.+2](subnK (ltnW (ltn_ord ix))) 
         exprn_addr mulfK ?expf_neq0 //.
 by rewrite -[y ^- iy]mul1r -Hyb -{1}[b.+2](subnK (ltnW (ltn_ord iy)))
            exprn_addr mulfK ?expf_neq0.
pose invgT := fun i:fT => SeqSub (HinvT i):fT.
have mulgTA : associative mulgT.
 move => [i ?] [j ?] [k ?].
 apply/val_inj => /=.
 apply: mulrA.
have mul1gT : left_id onegT mulgT.
 move => [i ?].
 apply/val_inj => /=.
 apply: mul1r.
have Hl0 : forall i, i \in l -> i != 0.
 move => ?.
 move/allpairsP => [[ix iy] [_ _ ->]].
 by rewrite /h0 /= mulf_neq0 // expf_neq0.
have mulVgT : left_inverse onegT invgT mulgT.
 move => [i ?].
 apply/val_inj => /=.
 apply: mulVf.
 by apply: Hl0.
pose gT := @FinGroupType (BaseFinGroupType fT 
              (FinGroup.Mixin mulgTA mul1gT mulVgT)) mulVgT.
pose h := fun i:gT => (val i).
have Mh1: {in [set: gT] &, {morph h : u v/ (u * v)%g >-> u * v}} by done.
have Mh2: {in [set: gT], forall x, h x = 1 <-> x = 1%g}.
 move => i _.
 rewrite /h /= -[1]/(ssval onegT); split; last by move ->.
 by move/val_inj ->.
have: cyclic [set: gT] by apply: (field_mul_group_cyclic (f:=h)).
move/cyclicP => [z Hz].
exists (h z).
apply:subv_anti.
apply/andP;split;rewrite -subsetFadjoinE; last first.
 rewrite (subv_trans (subsetKFadjoin K y) (subsetKFadjoin _ x)) /h /=.
 case: z {Hz} => ? /=.
 move/allpairsP => [[ix iy] [_ _ ->]].
 rewrite /h0 /= memv_mul // memv_exp //; first by rewrite memx_Fadjoin.
 by rewrite memK_Fadjoin // memx_Fadjoin.
rewrite -subsetFadjoinE subsetKFadjoin /=.
have Hxl : x \in l.
 apply/allpairsP.
 exists (1,0).
 by rewrite /h0 /= expr0 mulr1 modn_small // expr1 !mem_ord_enum.
have Hyl : y \in l.
 apply/allpairsP.
 exists (0,1).
 by rewrite /h0 /= expr0 mul1r modn_small // expr1 !mem_ord_enum.
have: (SeqSub Hxl \in <[z]>)%g by rewrite -Hz in_setT.
have Hhz : forall i, (h (z ^+ i)%g = h z ^+ i).
 elim => [|i IH] //.
 rewrite expgS exprS -IH.
 by apply: Mh1.
case/cycleP => i.
move/(f_equal val) => /= ->.
have: (SeqSub Hyl \in <[z]>)%g by rewrite -Hz in_setT.
case/cycleP => j.
move/(f_equal val) => /= ->.
by rewrite ![ssval _]Hhz !memv_exp // memx_Fadjoin.
Qed.

End FiniteCase.

Hypothesis sep : separableElement K y.

Let f0 := f \Po ('X + x%:P).
Let g0 := (g \Po ('X + y%:P)) %/ ('X).

Lemma gxg0_subproof : g0 * 'X = g \Po ('X + y%:P).
Proof.
rewrite /g.
have: (root (g \Po ('X + y%:P)) 0).
 by rewrite /root horner_comp_poly ![_.[0]]horner_lin add0r minPolyxx.
rewrite root_factor_theorem /dvdp subr0.
by move/eqP => mod0; rewrite -[_ * _]addr0 -mod0 -divp_eq // monicX.
Qed.

(* Here we mostly follow David Speyer's proof with some simiplifications *)
(* http://mathoverflow.net/questions/29687/primitive-element-theorem-without-building-field-extensions *)
Let Mf := \matrix_(i < m, j < n + m) if i <= j then
                                       (f0`_(j - i) *: 'X ^+ (j - i)) else 0.
Let Mg := \matrix_(i < n, j < n + m) if i <= j then (g0`_(j - i))%:P else 0.
Let M := col_mx Mg Mf.

Lemma szp_subproof : forall p (z:L), p != 0 ->
 size (p \Po ('X + z%:P)) = size p.
Proof.
move => p z nzp.
have Sa: size ('X + z%:P) = 2.
  by rewrite size_addl // !(size_polyX, size_polyC) //; case: eqP.
rewrite /comp_poly horner_coef size_map_poly.
rewrite (polySpred nzp) big_ord_recr /= coef_map mul_polyC.
have H : size (p`_(size p).-1 *: ('X + z%:P) ^+ (size p).-1) = (size p).-1.+1.
  rewrite size_scaler -?lead_coefE ?lead_coef_eq0 //.
  rewrite polySpred; first by rewrite size_exp_id Sa mul1n.
  by rewrite expf_neq0 // -size_poly_eq0 Sa.
rewrite addrC size_addl // H ltnS (leq_trans (size_sum _ _ _)) //.
apply/bigmax_leqP => i _.
rewrite coef_map mulrC.
have [->|nzpi] := (eqVneq p`_i 0); first by rewrite mulr0 size_poly0.
by rewrite mulrC mul_polyC size_scaler // (leq_trans (size_exp _ _)) // Sa
   mul1n.
Qed.

Lemma szf0_subproof : size f0 = n.+1.
Proof.
by rewrite /f0 szp_subproof -?size_poly_eq0 ?size_polyX // size_minPoly // /n.
Qed.

Lemma szg0_subproof : size g0 = m.+1.
Proof.
by rewrite /g0 size_divp ?szp_subproof -?size_poly_eq0 ?size_polyX //
           size_minPoly // /m -(prednK (elementDegreegt0 _ _)).
Qed.

Lemma g0nz_subproof : g0`_0 != 0.
Proof.
move: (separableNrootdmp K y).
rewrite negb_eqb sep /root -/g.
apply: contra.
have <- : g0.[0] = g0`_0.
 rewrite -[g0`_0]addr0.
 rewrite horner_coef szg0_subproof /m big_ord_recl expr0 mulr1.
 congr (_ + _).
 apply: big1 => i _.
 by rewrite exprSr !mulr0.
have: (root (g \Po ('X + y%:P)) 0).
 by rewrite /root horner_comp_poly ![_.[0]]horner_lin add0r minPolyxx.
rewrite -/(root g0 0) !root_factor_theorem.
rewrite -!polyC_opp !oppr0 !addr0 /g0 /dvdp => root1 root2.
suff: ('X - y%:P) ^+ 2 %| g.
 case/dvdpP => [r ->].
 by rewrite exprS expr1 !derivM mulr_addr !horner_add !horner_mul factor0
            !(mul0r, mulr0) !addr0.
have: 'X ^+ 2 %| (g \Po ('X + y%:P)).
 by rewrite -gxg0_subproof dvdp_mul ?dvdpp.
move/dvdpP => [r Hr].
apply/dvdpP.
exists (r \Po ('X - y%:P)).
rewrite -[g]comp_polyX -{1}(comp_poly_translateK y) -comp_polyA Hr.
by rewrite !comp_poly_mull !poly_comXp.
Qed.

Lemma leq_size_prodM_subproof : forall s:'S_(n + m),
 (size (\prod_i M i (s i))) <= (n * m).+1.
Proof.
move => s.
rewrite (leq_trans (size_prod _ _)) // eq_cardT // size_enum_ord big_split_ord
        /= leq_sub_add addnS ltnS -addnA leq_add //.
  apply: (@leq_trans #|'I_n|); last by rewrite card_ord.
  rewrite -sum1_card leq_sum // => i _.
  rewrite col_mxEu mxE !(fun_if, if_arg) size_polyC size_poly0.
  by rewrite leq_b1 if_same.
rewrite -mulSn mulnC -[m in muln m]card_ord -sum_nat_const leq_sum // => i _. 
rewrite col_mxEd mxE; case: ifP => _; last by rewrite size_poly0.
set j := (_ - _)%N.
have [-> | f0neq0] := eqVneq f0`_j 0; first by rewrite scale0r size_poly0.
rewrite size_scaler // size_polyXn -szf0_subproof ltnNge.
by apply: contra f0neq0 => /(nth_default 0)->.
Qed.

Lemma eq_size_prodM_subproof : forall s:'S_(n + m),
 (s == 1%g) = (size (\prod_i M i (s i)) == (n * m).+1).
Proof.
move => s.
apply/eqP/eqP => [->|].
 rewrite big_split_ord /=.
 set b := (\prod_(i < m) _).
 have -> : b = lead_coef(f0) ^+ m *: 'X ^+ (n * m).
  rewrite -mul_polyC rmorphX exprn_mulr -commr_exp_mull;
   last by rewrite /GRing.comm mulrC.
  rewrite -[m]card_ord -prodr_const.
  apply: eq_bigr => i _.
  by rewrite col_mxEd mxE perm1 leq_addl addnK lead_coefE szf0_subproof
     -mul_polyC.
 set a := (\prod_(i < n) _).
 have -> : a = (g0`_0 ^+ n)%:P.
  rewrite rmorphX -[n]card_ord -prodr_const.
  apply: eq_bigr => i _.
  by rewrite perm1 col_mxEu mxE leqnn subnn.
 by rewrite mul_polyC !size_scaler ?expf_neq0 ?g0nz_subproof // ?lead_coef_eq0
            -?size_poly_eq0 ?szf0_subproof // size_polyXn.
rewrite big_split_ord /=.
set a := \prod_(i < n) M (lshift m i) (s (lshift m i)).
case: (eqVneq a 0) => [->|aneq0]; first by rewrite mul0r size_poly0.
set b := \prod_(i < m) M (rshift n i) (s (rshift n i)).
case: (eqVneq b 0) => [->|bneq0]; first by rewrite mulr0 size_poly0.
have usize1: forall i, predT i -> size (M (lshift m i) (s (lshift m i))) = 1%N.
 move => i _.
 apply/eqP.
 rewrite eqn_leq.
 apply/andP; split.
 rewrite col_mxEu mxE.
  by case: ifP; rewrite ?size_poly0 // size_polyC leq_b1.
 move: aneq0.
 rewrite lt0n size_poly_eq0.
 move/prodf_neq0.
 by apply.
rewrite size_mul_id // size_prod_id; last first.
 by move => i _ /=; rewrite -size_poly_eq0 usize1.
rewrite (eq_bigr _ usize1) /= sum_nat_const eq_cardT // size_enum_ord
        muln1 subSnn addSn /= add0n => sizeb.
suff: forall k : 'I_(n+m), k <= s k.
  move => Hs; apply/permP => i.
  apply/eqP; rewrite perm1 eq_sym.
  move: i.
  have Hs0 := (fun k => leqif_eq (Hs k)).
  have Hs1 := (leqif_sum (fun i _ => (Hs0 i))).
  move: (Hs1 predT) => /=.
  rewrite (reindex_inj (@perm_inj _ s)) /=.
  by move/leqif_refl; move/forallP.
move => i.
rewrite -[i]splitK.
case: (split i) => {i} /= i.
 move: (usize1 i isT).
 rewrite col_mxEu mxE.
 case: ifP => //.
 by rewrite size_poly0.
move: sizeb.
rewrite size_prod_id; last by apply/prodf_neq0.
rewrite eq_cardT // size_enum_ord.
move/eqP.
apply: contraLR.
rewrite -ltnNge neq_ltn => Hs.
apply/orP; left.
rewrite ltnS leq_sub_add -mulSn (bigD1 i) //= -addSn.
have Hm := ltn_predK (ltn_ord i).
rewrite leqNgt -{1}Hm -leqNgt mulnS leq_add //.
(* rewrite -[m in (n.+1 * m)%N]Hm mulnS leq_add //. *)
 move: Hs.
 rewrite col_mxEd mxE.
 case: ifP; last by rewrite size_poly0.
  case: (eqVneq f0`_(s (rshift n i) - i) 0) => [->|].
  by rewrite scale0r size_poly0.
 move/size_scaler => -> _.
 rewrite size_polyXn -[X in (X + i)%N]/(n.-1.+1) addSn.
 by rewrite !ltnS leq_sub_add [(n.-1 + _)%N]addnC.
rewrite -[m in m.-1]card_ord -(cardC1 i) mulnC -sum_nat_const leq_sum // => j _.
rewrite col_mxEd mxE; case: ifP => _; last by rewrite size_poly0.
case: (eqVneq f0`_(s (rshift n j) - j) 0) => [->|Hf0].
 by rewrite scale0r size_poly0.
rewrite size_scaler // size_polyXn -szf0_subproof ltnNge.
by apply: contra Hf0 => /(nth_default 0)->.
Qed.

Let size_detM : size (\det M) = (n * m).+1.
Proof.
rewrite /determinant (bigD1 1%g) //=.
set a := (_ * _).
have Ha : size a = (n * m).+1.
 apply/eqP.
 by rewrite /a -polyC_opp -polyC_exp mul_polyC size_scaler ?signr_eq0
            -?eq_size_prodM_subproof.
rewrite size_addl // Ha ltnS (leq_trans (size_sum _ _ _)) //.
apply/bigmax_leqP => s.
rewrite -polyC_opp -polyC_exp mul_polyC size_scaler ?signr_eq0 // 
        eq_size_prodM_subproof.
move/negbTE => szneq.
move: (leq_size_prodM_subproof s).
by rewrite leq_eqVlt szneq ltnS.
Qed.

Let f1 t := f0 \Po (t *: 'X).

Lemma root_det_coprime_subproof :
 forall t, ~~ coprimep (f1 t) g0 -> root (\det M) t.
Proof.
move => t.
rewrite /root.
have HMt : rmorphism (fun x => (map_poly id x).[t]).
  have F2: rmorphism (@id L) by done.
  have F1: commr_rmorph (RMorphism F2) t := (mulrC _).
  exact: (horner_is_rmorphism F1).
have -> : forall p : {poly L}, p.[t] = (map_poly id p).[t].
 by move => p; rewrite map_polyE map_id polyseqK.
move: (det_map_mx (RMorphism HMt) M) => /= <-.
set f1t := f1 t.
have f1tdef : f1t = \sum_(i < size f0) (f0`_i * t ^+ i) *: 'X ^+ i.
  rewrite /f1t /f1 /comp_poly horner_coef size_map_poly;  apply: eq_bigr => j _.
  rewrite -!mul_polyC commr_exp_mull; last by apply: mulrC.
  by rewrite coef_map mulrA polyC_mul polyC_exp.
have szf1t : size f1t <= n.+1.
  by rewrite f1tdef -(poly_def (size f0) (fun i => f0`_i * t ^+ i))
             szf0_subproof size_poly.
have f1ti : forall i, f1t`_i = f0`_i * t ^+ i.
  move => i.
  rewrite f1tdef.
  rewrite -(poly_def (size f0) (fun i => f0`_i * t ^+ i)) coef_poly.
  case: ifP => //.
  move/negbT.
  rewrite -leqNgt => ?.
  by rewrite nth_default // mul0r.
move/dvdpP: (dvdp_gcdl f1t g0) => [r1 Hr1].
move/dvdpP: (dvdp_gcdr f1t g0) => [r2 Hr2].
rewrite /coprimep neq_ltn ltnS leqn0.
case/orP => [|szgcd].
  rewrite size_poly_eq0 gcdp_eq0 -{1}size_poly_eq0.
  case/andP => _; move/eqP => g00.
  move: g0nz_subproof.
  by rewrite g00 coef0 eq_refl.
have szgcd0 : 0 < size (gcdp f1t g0) by apply (@leq_trans 2%N).
have nzr2 : (0 < size r2).
  rewrite lt0n.
  move/eqP: Hr2.
  apply: contraL.
  rewrite size_poly_eq0.
  by move/eqP ->; rewrite mul0r -size_poly_eq0 szg0_subproof.
have r1small : size r1 <= n.
  case (eqVneq (size r1) 0%N) => [->|] //.
  rewrite -lt0n => nzr1.
  rewrite -(prednK szgcd0) ltnS in szgcd.
  rewrite -ltnS (leq_trans _ szf1t) //.
  rewrite Hr1 size_mul_id -?size_poly_eq0 -?lt0n //.
  move/prednK: (leq_trans (szgcd) (leq_pred _))<-; rewrite addnS /= //.
  by rewrite -{1}(addn0 (size r1)) ltn_add2l.
have r2small : size r2 <= m.
  rewrite -(prednK szgcd0) ltnS in szgcd.
  by rewrite -ltnS -szg0_subproof Hr2 size_mul_id
             -?size_poly_eq0 -?lt0n // -(prednK szgcd0) addnS -(prednK szgcd) 
             addnS ltnS leq_addr.
apply/det0P.
exists (row_mx (\row_i (r1`_i)) (-(\row_i (r2`_i)))).
  apply/negP; move/eqP.
  rewrite -row_mx0.
  case/eq_row_mx => _.
  move/rowP.
  have ordszr2 : (size r2).-1 < m.
    by rewrite (prednK nzr2).
  move/(_ (Ordinal ordszr2)).
  rewrite !mxE /=.
  move/eqP.
  rewrite oppr_eq0 -lead_coefE lead_coef_eq0 -size_poly_eq0 -[_ == _](negbK).
  by rewrite -lt0n nzr2.
apply/rowP => i.
rewrite /M map_col_mx mul_row_col mulNmx.
rewrite !mxE.
apply/eqP.
have matrixPolyMul: forall (h r : {poly L}) k z, size r <= k ->
  (z = (map_mx (fun x0 : {poly L} => (map_poly id x0).[t])
        (\matrix_(i, j) (if i <= j then (h`_(j - i))%:P else 0)))) ->
  \sum_j
   (\row_i0 r`_i0) 0 (j:'I_k) * z j i = (r * h)`_i.
  move => h r k z rsmall -> {z}.
  set a := (\sum_j _).
  rewrite coefM.
  case/orP: (leq_total i.+1 k) => [ismall|ilarge].
    rewrite (big_ord_widen _ (fun j => r`_j * h`_(i - j)) ismall).
    rewrite big_mkcond.
    apply: eq_bigr => j _.
    rewrite !mxE /horner_morph map_polyE map_id polyseqK ltnS.
    by case: (j <= i); rewrite hornerC // mulr0.
  rewrite -(big_mkord (fun j => true) (fun j =>  r`_j * h`_(i - j)))
          (big_cat_nat _ (fun j => true) (fun j =>  r`_j * h`_(i - j))
                         (leq0n _) ilarge)
          /=.
  have -> : \sum_(k <= i0 < i.+1) r`_i0 * h`_(i - i0) = 0.
    apply: big1_seq => j /=.
    rewrite mem_index_iota.
    move/andP => [Hnj Hji].
    by rewrite nth_default ?mulr0 ?mul0r // (leq_trans rsmall).
  rewrite addr0 big_mkord.
  apply: eq_bigr => j _.
  rewrite !mxE /horner_morph map_polyE map_id polyseqK.
  case: ifP; rewrite hornerC //.
  move/negbT.
  rewrite -ltnNge => Hij.
  by rewrite nth_default ?mulr0 ?mul0r // (leq_trans _ Hij) // 
             (leq_trans _ ilarge).
rewrite (matrixPolyMul g0) //.
rewrite (matrixPolyMul f1t) //.
  by rewrite Hr1 {1}Hr2 mulrA [r1 * r2]mulrC -mulrA subrr.
apply/matrixP => j k.
rewrite !mxE.
case: leqP => // _.
by rewrite !map_polyE !map_id !polyseqK horner_scaler hornerXn hornerC f1ti.
Qed.


Section InfiniteCase.

Variable t : L.
Hypothesis tK : t \in K.
Hypothesis troot : ~~(root (\det M) t).

Let z := x - t*y.
Let h := f \Po (t *: 'X + z%:P).

Lemma gcdhg_subproof : gcdp h g %= 'X - y%:P.
Proof.
apply/andP; split; last first.
 rewrite dvdp_gcd.
 apply/andP; split; rewrite -root_factor_theorem; last by rewrite root_minPoly.
 by rewrite /root /h horner_comp_poly ![_.[y]]horner_lin /z addrC subrK 
            minPolyxx.
rewrite /h /z polyC_add [x%:P + _]addrC polyC_opp polyC_mul -mul_polyC addrA 
        -mulr_subr mul_polyC.
(*
have PCRM := polyC_RM.
have RM1 : GRing.morphism (horner_morph polyC (t *: ('X - y%:P))).
 by apply: horner_morphRM => //;move => ?;apply: mulrC.
*)
have -> : t *: ('X - y%:P) + x%:P =
          ('X + x%:P) \Po (t *: ('X - y%:P)).
  by rewrite comp_poly_addl poly_comXp poly_comCp.
rewrite -comp_polyA -/f0.
(*
have RM2 : GRing.morphism (horner_morph polyC ('X - y%:P)).
 by apply: horner_morphRM => //;move => ?;apply: mulrC.
*)
have -> : t *: ('X - y%:P) = (t *: 'X) \Po ('X - y%:P).
  by rewrite comp_poly_scall poly_comXp.
rewrite -[g](comp_polyX) -{3}(comp_poly_translateK y).
rewrite -!comp_polyA -(eqp_dvdl _ (gcdp_comp_poly _ _ _)) -gxg0_subproof.
rewrite -/(f1 t) -{2}['X-y%:P]poly_comXp dvdp_comp_poly //.
apply (@dvdp_trans _ (gcdp ((f1 t) * 'X) (g0 * 'X))).
 by rewrite dvdp_gcd dvdp_gcdr dvdp_mulr // dvdp_gcdl.
rewrite -(eqp_dvdl _ (mulp_gcdl _ _ _)) -{2}['X]mul1r dvdp_mul2r
        -?size_poly_eq0 ?size_polyX //.
rewrite dvdp1 size_poly_eqp1 gcdp_eqp1.
apply: contraR troot.
apply: root_det_coprime_subproof.
Qed.

Lemma PET_infiniteCase_subproof : Fadjoin (Fadjoin K y) x = Fadjoin K z.
Proof.
apply: subv_anti.
apply/andP;split; rewrite -subsetFadjoinE; last first.
 rewrite (subv_trans (subsetKFadjoin K y) (subsetKFadjoin _ x)) /=.
 have -> : z = ('X - t *: y%:P).[x] by rewrite !horner_lin.
 rewrite mempx_Fadjoin // addp_polyOver ?opp_polyOver ?scalep_polyOver
         ?polyOverC ?polyOverX //; last by rewrite memx_Fadjoin.
 by rewrite memK_Fadjoin.
rewrite -subsetFadjoinE.
rewrite subsetKFadjoin /=.
have Hy : (y \in Fadjoin K z).
 suff: polyOver (Fadjoin K z) ('X - y%:P).
  move/polyOverP.
  move/(_ 0%N).
  rewrite coefD coefX add0r coefN coefC /=.
  by apply: memvNl.
 rewrite addp_polyOver ?polyOverX // opp_polyOver //.
 have: (polyOver (Fadjoin K z) (gcdp h g)).
  rewrite gcdp_polyOver ?compose_polyOver //; 
   try solve [by rewrite (polyOver_subset (subsetKFadjoin _ _)) // minPolyOver].
  by rewrite addp_polyOver ?polyOverC ?memx_Fadjoin //
             (polyOver_subset (subsetKFadjoin _ _)) // scalep_polyOver 
             ?polyOverX.
 move/polyOverP => HKz.
 rewrite (_ : y = (- (gcdp h g)`_0)/(gcdp h g)`_1).
   by rewrite polyOverC  // memv_mul -?memv_inv // memvN.
 have szgcd : size (gcdp h g) = 2.
  by rewrite (size_eqp gcdhg_subproof) size_factor.
 apply: (canRL (mulrK _)).
  by rewrite unitfE -[1%N]/(2.-1) -szgcd -lead_coefE lead_coef_eq0
             -size_poly_eq0 szgcd.
 move/eqpP: gcdhg_subproof => [c1 [c2 [c1nz c2nz Hc]]].
 rewrite -unitfE in c1nz.
 apply (can_inj (mulKr c1nz)).
 by rewrite [y * _]mulrC mulrA mulrN -!coefZ Hc !coefZ !coefD
            !coefX add0r !coefN !coefC subr0 mulr1 mulrN opprK.
rewrite Hy /= -[x](subrK (t * y)) -/z memvD ?memv_mul //.
 by rewrite memx_Fadjoin.
by rewrite memK_Fadjoin.
Qed.

End InfiniteCase.

Lemma PrimitiveElementTheorem : exists z, Fadjoin (Fadjoin K y) x = Fadjoin K z.
Proof.
case: (PET_finiteCase_subproof (n * m)) => [[l]|//].
case/and3P; move/allP => HKl Hl Hnml.
have: ~~(all (root (\det M)) l).
 move: Hnml.
 rewrite -size_detM leqNgt.
 apply: contra => HMl.
 apply: max_poly_roots => //.
 by rewrite -size_poly_eq0 size_detM.
case/allPn => z Hzl HMz.
exists (x - z * y).
apply: PET_infiniteCase_subproof => //.
by apply: HKl.
Qed.

Lemma separableFadjoinExtend : separableElement (Fadjoin K y) x -> 
  separableElement K x.
Proof.
move/separableDerivationP => sepx.
move/separableDerivationP: sep => sepy.
case: PrimitiveElementTheorem => z Hz.
suff/allSeparableElement : separableElement K z.
 by apply; rewrite -Hz memx_Fadjoin.
apply/separableDerivationP => D.
rewrite -Hz => HDz.
have HDy : Derivation (Fadjoin K y) D.
 apply: (subvDerivation _ HDz).
 by rewrite subsetKFadjoin.
move/(sepy _ HDy).
by apply: sepx=> /=.
Qed.

End PrimitiveElementTheorem.

Lemma StrongPrimitiveElementTheorem
     : forall (K : {algebra L}) (x y : L),
       separableElement (Fadjoin K x) y ->
       exists2 z : L, Fadjoin (Fadjoin K y) x = Fadjoin K z &
                      separableElement K x -> separableElement K y.
Proof.
move => K x y Hsep.
case: (separablePower K y) => n.
case/andP => Hn.
case/(PrimitiveElementTheorem x) => z Hz.
exists z; last by move/separableFadjoinExtend; apply.
case (eqVneq n 1%N) => Hn1; first by move: Hz; rewrite Hn1 expr1.
have : (1 < n) by case: n Hz Hn Hn1 => [|[|n]].
move => {Hn1} Hn1.
rewrite -Hz {1}FadjoinC [X in _ = X]FadjoinC.
apply: subv_anti.
apply/andP; split; rewrite -{1}subsetFadjoinE {1}subsetKFadjoin.
 by rewrite -separableCharn // Hsep.
by rewrite memv_exp ?memx_Fadjoin.
Qed.

Section SeparableAndInseparableExtensions.

Definition separable (K E : {vspace L}) : bool :=
 all (separableElement K) (vbasis E).

Definition purelyInseparable (K E : {vspace L}) : bool :=
 all (purelyInseparableElement K) (vbasis E).

Variable (K : {algebra L}).

Lemma separable_add : forall x y,
  separableElement K x -> separableElement K y -> separableElement K (x + y).
Proof.
move => x y Hx Hy.
case: (PrimitiveElementTheorem x Hy) => z Hz.
have: (x + y) \in Fadjoin (Fadjoin K y) x.
 by apply: memvD; last apply: memK_Fadjoin; apply: memx_Fadjoin.
rewrite Hz.
move: (x + y); apply/allSeparableElement.
apply: (separableFadjoinExtend Hy).
apply: (@separableFadjoinExtend _ _ x); last first.
 by rewrite Hz separableinK ?memx_Fadjoin.
by apply: (subsetSeparable (subsetKFadjoin K y)).
Qed.

Lemma separable_sum : forall I r (P : pred I) (v_ : I -> L),
  (forall i, P i -> separableElement K (v_ i)) ->
  separableElement K (\sum_(i <- r | P i) v_ i).
Proof.
apply: (@big_ind L (separableElement K)).
 apply/separableinK/mem0v.
apply: separable_add.
Qed.

Lemma inseparable_add : forall x y,
  purelyInseparableElement K x -> purelyInseparableElement K y ->
  purelyInseparableElement K (x + y).
Proof.
move => x y.
case/purelyInseparableElementP => n Hn Hx.
case/purelyInseparableElementP => m Hm Hy.
apply/purelyInseparableElementP.
have Hnm : [char L].-nat (n * m)%N by rewrite pnat_mul Hn Hm.
exists (n * m)%N => //.
by rewrite exprp_addl // {2}mulnC !exprn_mulr memvD // memv_exp.
Qed.

Lemma inseparable_sum : forall I r (P : pred I) (v_ : I -> L),
  (forall i, P i -> purelyInseparableElement K (v_ i)) ->
  purelyInseparableElement K (\sum_(i <- r | P i) v_ i).
Proof.
apply: (@big_ind L (purelyInseparableElement K)).
 apply/inseparableinK/mem0v.
apply: inseparable_add.
Qed.

Variable (E : {algebra L}).

Lemma separableP :
  reflect (forall y, y \in E -> separableElement K y)
          (separable K E).
Proof.
apply (iffP idP); last first.
 move => HEK.
 apply/allP => x; move/memv_basis => Hx.
 by apply: HEK.
move/allP => HEK y.
move/coord_basis ->.
apply/separable_sum => i _.
have/allSeparableElement : (separableElement K (vbasis E)`_i).
 case: (leqP (size (vbasis E)) i); last by move/(mem_nth 0)/HEK.
 by move/(nth_default 0) ->; rewrite separableinK // mem0v.
apply.
by rewrite memvZl // memx_Fadjoin.
Qed.

Lemma purelyInseparableP :
  reflect (forall y, y \in E -> purelyInseparableElement K y)
          (purelyInseparable K E).
Proof.
apply (iffP idP); last first.
 move => HEK.
 apply/allP => x; move/memv_basis => Hx.
 by apply: HEK.
move/allP => HEK y.
move/coord_basis ->.
apply/inseparable_sum => i _.
have : (vbasis E)`_i \in vbasis E.
 rewrite mem_nth //.
 case: (vbasis E) => /= ?.
 by move/eqP ->.
case/HEK/purelyInseparableElementP => n Hn HK.
apply/purelyInseparableElementP.
exists n => //.
by rewrite scaler_exp memvZl.
Qed.

End SeparableAndInseparableExtensions.

Section SeparableInseparableDecomposition.

Lemma separableSeparableExtension : forall K x,
 separableElement K x -> separable K (Fadjoin K x).
Proof.
move => K x.
move/allSeparableElement => Hsep.
by apply/separableP.
Qed.

Lemma separableInseparableDecomposition : forall E K ,
 exists x, [&& x \in E, separableElement K x & 
             purelyInseparable (Fadjoin K x) E].
Proof.
move => E K.
wlog: K / (K <= E)%VS => [|HKE].
 case/(_ _ (capvSr K E)) => x.
 case/and3P => HxE Hsep.
 move/purelyInseparableP => Hinsep.
 exists x.
 apply/and3P; split; first done.
  by apply/(subsetSeparable _ Hsep)/capvSl.
 apply/purelyInseparableP => y Hy.
 apply: subsetInseparable; last by apply Hinsep.
 by apply/subsetFadjoin/capvSl.
set (f := fun i => 
      (vbasis E)`_i ^+ ex_minn (separablePower K (vbasis E)`_i)).
set (s := mkseq f (\dim E)).
have Hsep : all (separableElement K) s.
 apply/allP => x.
 case/mapP => i _ ->.
 rewrite /f.
 by case ex_minnP => m; case/andP.
set (K' := foldr (fun x y => Fadjoin_aspace y x) K s).
have: exists x, [&& x \in E, separableElement K x
                  & K' == Fadjoin K x :> {vspace _}].
 rewrite /K' {K'}.
 have: all (fun x => x \in E) s.
  apply/allP => ?.
  case/mapP => i.
  rewrite mem_iota => Hi ->.
  rewrite /f memv_exp // memv_basis // mem_nth //.
  case: (vbasis E) => ? /=.
  by move/eqP ->.
 elim: s Hsep => [|t s IH].
  exists 0.
  apply/and3P; split => //; first by rewrite mem0v.
   by rewrite separableinK // mem0v.
  rewrite eq_sym -FadjoinxK.
  by apply: mem0v.
 case/andP => Ht Hs.
 case/andP => HtE HsE.
 case: (IH Hs HsE) => y.
 case/and3P => HyE Hsep Hy.
 case: (PrimitiveElementTheorem t Hsep) => x Hx.
 exists x.
 apply/and3P; split.
   suff: (Fadjoin K x <= E)%VS by move/subvP; apply; rewrite memx_Fadjoin.
   by rewrite -Hx -!subsetFadjoinE HKE HyE.
  apply/allSeparableElement => z.
  rewrite -Hx => Hz.
  apply: (separableFadjoinExtend Hsep).
  move/allSeparableElement: (subsetSeparable (subsetKFadjoin K y) Ht).
  by apply.
 move/eqP: Hy => /= ->.
 by apply/eqP.
case => x.
case/and3P => HxE Hsepx.
move/eqP => HK'.
exists x.
rewrite -HK' HxE Hsepx.
apply/allP => y.
case/(nthP 0) => i Hy <-.
apply/purelyInseparableElementP.
exists (ex_minn (separablePower K (vbasis E)`_i)).
 by case: ex_minnP => ?; case/andP.
rewrite /K' foldr_map -[_ ^+ _]/(f i).
move: Hy.
case: (vbasis E) => ? /=.
move/eqP ->.
rewrite -[_ < _]/(0 <= i < 0 + (\dim E)).
rewrite -mem_iota.
elim: (iota 0 (\dim E)) => [//|a b IH].
case/orP; last by move => ?; apply/memK_Fadjoin/IH.
move/eqP ->.
by apply: memx_Fadjoin.
Qed.

(* Are these defintions not needed? *)

Definition separableGenerator K E : L:= 
  choice.xchoose (separableInseparableDecomposition E K).

Lemma separableGeneratorInE : forall E K, separableGenerator K E \in E.
Proof.
move => E K.
by case/and3P: (choice.xchooseP 
  (separableInseparableDecomposition E K)).
Qed.

Lemma separableGeneratorSep : forall E K, 
 separableElement K (separableGenerator K E).
Proof.
move => E K.
by case/and3P: (choice.xchooseP 
  (separableInseparableDecomposition E K)).
Qed.

Lemma separableGeneratorMaximal : forall E K, 
 purelyInseparable (Fadjoin K (separableGenerator K E)) E.
Proof.
move => E K.
by case/and3P: (choice.xchooseP 
  (separableInseparableDecomposition E K)).
Qed.

Lemma separableSeparableGeneratorEx : forall E K,
 separable K E -> (E <= Fadjoin K (separableGenerator K E))%VS.
Proof.
move => E K.
move/separableP => Hsep.
apply/subvP => v Hv.
rewrite separableInseparableElement.
move/purelyInseparableP/(_ _ Hv): (separableGeneratorMaximal E K) ->.
by rewrite (subsetSeparable _ (Hsep _ Hv)) // subsetKFadjoin.
Qed.

Lemma separableSeparableGenerator : forall E K,
 separable K E -> (K <= E)%VS -> E = Fadjoin K (separableGenerator K E) :> {vspace _}.
Proof.
move => E K Hsep HKE.
apply: subv_anti.
rewrite separableSeparableGeneratorEx //=.
by rewrite -subsetFadjoinE HKE separableGeneratorInE.
Qed.

End SeparableInseparableDecomposition.

End Separable.

Section FiniteSeparable.

Variable F : finFieldType.
Variable L : fieldExtType F.

Let pCharL : char F \in [char L].
Proof. by rewrite charLF finField_char. Qed.

Lemma FermatLittleTheorem  (x : L) : x ^+ (#|F| ^ vdim L) = x.
Proof.
pose m1 := (CanCountMixin (@v2rvK _ L)).
pose m2 := (CanFinMixin (eT := CountType L m1) (@v2rvK _ L)).
pose FL := @FinRing.Field.pack L _ _ id (FinType L m2) _ id.
suff -> : #|F| ^ vdim L = #|FL| by apply: (@expf_card FL).
pose f (x : FL) := coord (vbasis (fullv L)) x.
rewrite -[vdim L]card_ord -card_ffun -dimvf.
have/card_in_image <- : {in FL &, injective f}.
 move => a b Ha Hb /= /ffunP Hab.
 rewrite (coord_basis (memvf a)) (coord_basis (memvf b)).
 apply: eq_bigr => i _.
 by rewrite Hab.
apply: eq_card => g.
rewrite !inE.
symmetry; apply/idP.
apply/mapP.
exists (\sum_i g i *: (vbasis (fullv L))`_i); first by rewrite mem_enum.
apply/ffunP => i.
by rewrite free_coords // (free_is_basis (is_basis_vbasis (fullv L))).
Qed.

Lemma separableFiniteField (K E : {algebra L}) : separable K E.
Proof.
apply/separableP => y _.
rewrite (separableCharp _ _ 0 pCharL) expn1.
rewrite -{1}[y]FermatLittleTheorem.
 case: (p_natP (finField_card F)) => [[|n ->]].
 move/eqP.
 by rewrite expn0 -{1}(subnK (finField_card_gt1 F)) addnC.
rewrite -expn_mulr.
suff -> : (n.+1 * (vdim L))%N = (n.+1 * (vdim L)).-1.+1.
 by rewrite expnS exprn_mulr memv_exp // memx_Fadjoin.
rewrite prednK // muln_gt0.
apply: (@leq_trans (elementDegree (fullv L) 1)) => //.
apply: elementDegreeBound.
Qed.

End FiniteSeparable.