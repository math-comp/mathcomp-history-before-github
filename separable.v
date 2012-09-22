Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
Require Import tuple finfun bigop prime binomial ssralg poly polydiv.
Require ssrint.
Require Import finset fingroup perm finalg zmodp cyclic.
Require Import matrix mxalgebra mxpoly polyXY vector falgebra fieldext.

(******************************************************************************)
(* This file provides a theory of separable and inseparable field extensions  *)
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

Import GRing.Theory ssrint.IntDist.


Section SeparablePoly.

Variable (R: idomainType).
Implicit Types (p q d u v : {poly R}).

Definition separablePolynomial p := coprimep p p^`().

Local Notation sep := separablePolynomial.
Local Notation lcn_neq0 := (Pdiv.Idomain.lc_expn_scalp_neq0 _).

Lemma separable_neq0 p : separablePolynomial p -> p != 0.
Proof. by apply: contraL=> /eqP ->; rewrite /sep deriv0 coprime0p eqp01. Qed.

Lemma nosquareP p :
  (forall u v, u * v %| p -> coprimep u v)
  <-> (forall u, size u != 1%N -> ~~ (u ^+ 2 %| p)).
Proof.
split=> [hp u pu_neq1|hp u v dvd_uv_p].
  by apply/negP=> /hp; rewrite coprimepp; apply/negP.
rewrite coprimep_def; have [//|/hp/negPf<-] := altP eqP.
by rewrite (dvdp_trans _ dvd_uv_p) // dvdp_mul ?dvdp_gcdl ?dvdp_gcdr.
Qed.

Lemma separablePolynomialP p :
  reflect ((forall u v, u * v %| p -> coprimep u v)
        /\ (forall u, u %| p -> 1 < size u -> u^`() != 0))
          (sep p).
Proof.
apply: (iffP idP)=> [sep_p|].
  split; last first.
    move=> u dvd_up u_gt1; apply/negP=> /eqP u_eq0.
    suff: u %| gcdp p p^`().
      by rewrite gtNdvdp -?size_poly_eq0 // coprimep_size_gcd.
    pose c := lead_coef u ^+ scalp p u.
    have c_neq0 : c != 0 by rewrite lcn_neq0. 
    rewrite dvdp_gcd dvd_up -(@dvdp_scaler _ c) // -derivZ -Pdiv.Idomain.divpK //=.
    by rewrite derivM u_eq0 mulr0 addr0 dvdp_mull // dvdpp.
  move=> u v; rewrite Pdiv.Idomain.dvdp_eq; set c := _ ^+ _.
  have c_neq0 : c != 0 by rewrite lcn_neq0.
  rewrite mulrA; set r := _ * u => /eqP p_eq; move: sep_p; rewrite /sep.
  rewrite -(coprimep_scalel _ _ c_neq0) -(coprimep_scaler _ _ c_neq0).
  rewrite -derivZ p_eq derivM coprimep_mull.
  rewrite {1}addrC mulrC !coprimep_addl_mul !(coprimep_mull, coprimep_mulr).
  by do ![case/andP|move=> ?].
move=> [hp2 hp1]; rewrite /sep coprimep_def; set g := gcdp _ _.
pose c := lead_coef g ^+ scalp p g.
have c_neq0 : c != 0 by rewrite lcn_neq0.
have [|p_gt1|//] := ltngtP.
  rewrite ltnS leqn0 size_poly_eq0 /g gcdp_eq0=> /andP[/eqP p_eq0 _].
  by have := hp2 0 0; rewrite mulr0 p_eq0 dvdp0 coprimep0 eqp01; apply.
have: g %| (c *: p^`()) by rewrite dvdp_scaler ?dvdp_gcdr.
rewrite -derivZ -Pdiv.Idomain.divpK ?dvdp_gcdl // derivM.
rewrite dvdp_addr; last by rewrite dvdp_mull ?dvdpp.
rewrite Gauss_dvdpr ?hp2 1?mulrC ?Pdiv.Idomain.divpK ?dvdp_gcdl -/c ?dvdp_scalel ?dvdpp //.
move=> /dvdp_leq; rewrite leqNgt lt_size_deriv; last first.
  by rewrite -size_poly_gt0 (leq_trans _ p_gt1).
by apply; rewrite hp1 ?Pdiv.Idomain.dvdp_gcdl.
Qed.

Lemma separable_coprime p : sep p -> forall u v, u * v %| p -> coprimep u v.

Proof. by move=> /separablePolynomialP[]. Qed.

Lemma separable_nosquare p : sep p ->
  forall u k, 1%N < k -> u %| p -> size u != 1%N -> u ^+ k %| p = false.
Proof.
move=> /separablePolynomialP[/nosquareP hp _] u [|[|]] // k _ hu su.
have [|//] := boolP (_ %| _) => /(dvdp_trans _) => /(_ (u ^+ 2)).
by rewrite (negPf (hp _ _)) // => -> //; rewrite expr2 !exprS mulrA dvdp_mulr ?dvdpp.
Qed.

Lemma separable_deriv_eq0 p : sep p ->
  forall u, u %| p -> 1 < size u -> (u^`() == 0) = false.
Proof.
by move=> /separablePolynomialP[_ h] u hu su; apply: negbTE; rewrite h.
Qed.

Lemma dvdp_separable p q : q %| p -> sep p -> sep q.
Proof.
move=> dvd_qp sep_p; apply/separablePolynomialP; split=> [u v huv|u hu su].
  by rewrite (separable_coprime sep_p) // (dvdp_trans huv).
by rewrite (separable_deriv_eq0 sep_p) // (dvdp_trans hu).
Qed.

Lemma separable_mul p q : separablePolynomial (p * q) =
 [&& separablePolynomial p, separablePolynomial q & coprimep p q].
Proof.
apply/idP/and3P => [H|].
  by rewrite !(dvdp_separable _ H) (dvdp_mulIr,dvdp_mulIl,separable_coprime H).
rewrite /sep=> [] [Hp Hq Hpq]; rewrite derivM coprimep_mull {1}addrC mulrC.
rewrite !coprimep_addl_mul !coprimep_def !(eqp_size (Gauss_gcdpr _ _)) //.
by rewrite -?coprimep_def Hpq coprimep_sym.
Qed.

Lemma eqp_separable p q : p %= q -> sep p = sep q.
Proof. by move=> /andP[hpq hqp]; apply/idP/idP=> /dvdp_separable; apply. Qed.

Lemma separable_root p x : sep (p * ('X - x%:P)) = sep p && ~~ root p x.
Proof.
rewrite separable_mul; have [sep_p /=|//] := boolP (sep p).
by rewrite /sep derivXsubC coprimep1 coprimep_XsubC.
Qed.

Lemma separable_prod_XsubC (r : seq R) :
  separablePolynomial (\prod_(x <- r) ('X - x%:P)) = uniq r.
Proof.
elim: r => [|x r IH]; first by rewrite big_nil /separablePolynomial coprime1p.
by rewrite big_cons mulrC separable_root IH root_prod_XsubC andbC.
Qed.

Lemma make_separable p : p != 0 -> sep (p %/ (gcdp p p^`())).
Proof.
move=> p_neq0; set g := gcdp _ _; apply/separablePolynomialP.
have max_dvd_u : forall u : {poly R}, 1 < size u -> exists k, ~~ (u ^+ k %| p).
  move=> u size_u; exists (size p); rewrite gtNdvdp // [X in _ < X]polySpred.
    by rewrite size_exp ltnS leq_pmull //; case: size size_u.
  by rewrite expf_neq0 // -size_poly_gt0 (leq_trans _ size_u).
split; last first.
  move=> u hu size_u; apply: contraL isT=> /eqP u'_eq0 /=.
  have [//|[|k]] := ex_minnP (max_dvd_u u _); first by rewrite dvd1p.
  move=> hk /(_ k); rewrite ltnn; apply; apply: contra hk=> hk.
  suff: u ^+ k.+1 %| (p %/ g) * g.
    by rewrite Pdiv.Idomain.divpK ?dvdp_gcdl // dvdp_scaler ?lcn_neq0.
  rewrite exprS dvdp_mul // dvdp_gcd hk //=.
  suff: u ^+ k %| ((p %/ u ^+ k) * u ^+ k)^`().
    by rewrite Pdiv.Idomain.divpK ?dvdp_gcdl // derivZ dvdp_scaler ?lcn_neq0.
  by rewrite ?dvdp_gcdl // !derivCE u'_eq0 mul0r mul0rn mulr0 addr0 dvdp_mull.
apply/nosquareP=> u; have [|size_u _|//] := ltngtP.
  rewrite // ltnS leqn0 size_poly_eq0=> /eqP -> _; rewrite exprS mul0r.
  apply/negP=> /dvdp_trans/=/(_ _ (divp_dvd _)).
  by rewrite dvd0p (negPf p_neq0) dvdp_gcdl=> /implyP.
have [hu|//] := boolP (_ %| _); have [//|] := ex_minnP (max_dvd_u u _).
move=> [|[|n hn]]; first by rewrite dvd1p.
  rewrite expr1 (@dvdp_trans _ (p %/ g)) ?divp_dvd ?dvdp_gcdl //.
  by rewrite (dvdp_trans _ hu) // exprS dvdp_mulr.
move=> /(_ n.+1); rewrite ltnn; apply; apply: contra hn=> hn.
suff: u ^+ n.+2 %| (p %/ g) * g.
  by rewrite Pdiv.Idomain.divpK ?dvdp_gcdl // dvdp_scaler ?lcn_neq0.
rewrite !exprS mulrA dvdp_mul //.
rewrite dvdp_gcd (dvdp_trans _ hn) ?exprS ?dvdp_mull //=.
suff: u ^+ n %| ((p %/ u ^+ n.+1) * u ^+ n.+1)^`().
  by rewrite Pdiv.Idomain.divpK ?dvdp_gcdl // derivZ dvdp_scaler ?lcn_neq0.
by rewrite !derivCE dvdp_add // -1?mulr_natl ?exprS !dvdp_mull.
Qed.

End SeparablePoly.

Lemma separable_map (F : fieldType) (R:idomainType) (f : {rmorphism F -> R})
 (p : {poly F}) : separablePolynomial (map_poly f p) = separablePolynomial p.
Proof.
by rewrite /separablePolynomial deriv_map /coprimep -gcdp_map size_map_poly.
Qed.

Section InfinitePrimitiveElementTheorem.

Local Notation "p ^ f" := (map_poly f p) : ring_scope.
Local Notation "'Y" := 'X%:P : ring_scope.

Variables (F L: fieldType) (iota : {rmorphism F -> L}).
Variables (x y : L) (p : {poly F}).
Hypothesis (pne0 : p != 0).
Hypothesis (Hpx : root (p ^ iota) x).

Lemma PET_Infinite_Case q :
  root (q ^ iota) y -> separablePolynomial q ->
  exists r, r != 0 /\
   forall t, ~~root r (iota t) ->
    (exists p0, (p0 ^ iota).[iota t * y - x] = x) /\
    (exists q0, (q0 ^ iota).[iota t * y - x] = y).
Proof.
move => Hqy Hsep.
have qne0 := separable_neq0 Hsep.
set p' := (p ^ iota) \Po ('X + x%:P).
have [qq Hqq] := (factor_theorem _ _ Hqy).
set q' := qq \Po ('X + y%:P).
have q'0_neq0: q'.[0] != 0.
  move: Hsep.
  rewrite horner_comp !hornerE -rootE -(separable_map iota) Hqq separable_root.
  by case/andP.
have p'ne0 : p' != 0.
  move: pne0.
  apply: contra.
  move/eqP/(f_equal (fun q => q \Po ('X - x%:P)))/eqP.
  by rewrite comp_poly0 comp_polyXaddC_K map_poly_eq0.
have q'ne0 : q' != 0.
  by apply: contra q'0_neq0 => /eqP->; rewrite horner0.
have : coprimep ((p' ^ polyC) \Po ('Y * 'X)) (q' ^ polyC).
  rewrite coprimep_def -[_ == _]negbK neq_ltn ltnS size_poly_leq0.
  rewrite gcdp_eq0 mulrC poly_XmY_eq0 map_polyC_eq0.
  rewrite (negPf p'ne0) (negPf q'ne0) /= -resultant_eq0.
  by rewrite annul_div_neq0.
rewrite -gcdp_eqp1.
move: (Bezoutp (p' ^ polyC \Po 'Y * 'X) (q' ^ polyC)) => [[u v] /= Huv].
rewrite -(eqp_ltrans Huv) -size_poly_eq1.
case/size_poly1P => {Huv} r Hr0 Hr.
exists r.
split => [//|t Ht].
suff Hq0 : (exists q0 : {poly F}, (q0 ^ iota).[iota t * y - x] = y).
  split => //.
  case: Hq0 => q0 Hq0.
  exists (t *: q0 - 'X).
  rewrite rmorphB [_ 'X]map_polyX [_ (_ *: _)]map_polyZ !hornerE.
  by rewrite Hq0 opprB addrC addrNK.
have Hcomm: (commr_rmorph idfun (iota t)) by apply: mulrC.
move/(f_equal (map_poly (horner_morph Hcomm))): Hr.
rewrite rmorphD !{1}rmorphM map_polyC /= /comp_poly -horner_map rmorphM.
rewrite [_ 'Y]map_polyC [_ 'X]horner_morphX  [_ 'X]map_polyX.
rewrite -map_poly_comp ?rmorph0 // -[(q' ^ _) ^ _]map_poly_comp ?rmorph0 //.
rewrite ![GRing.Additive.apply _]/=.
rewrite [_ ^ (map_poly _ \o _)]map_polyE.
rewrite (_ : (map (map_poly (horner_morph Hcomm) \o polyC) (p' ^ polyC))
           = (map (polyC \o (horner_morph Hcomm)) (p' ^ polyC))); last first.
 by rewrite (eq_map (map_polyC _)).
rewrite -map_polyE -map_poly_comp ?rmorph0 //.
rewrite -[((polyC \o horner_morph Hcomm) \o polyC)]
        /(polyC \o (horner_morph Hcomm \o polyC)).
rewrite [p' ^ _]map_poly_comp ?rmorph0 // ![GRing.Additive.apply _]/=.
rewrite !map_polyE !(eq_map (horner_morphC _)) !map_id -!map_polyE.
rewrite !polyseqK -/(comp_poly ((iota t)%:P  * 'X) p').
set u1 := (u ^ _).
set v1 := (v ^ _).
set p1 := (_ \Po _).
rewrite /horner_morph map_polyE map_id polyseqK.
move => Hlincomb.
have : (coprimep p1 q').
  apply/Bezout_coprimepP.
  exists (u1, v1).
  by rewrite Hlincomb polyC_eqp1.
clear -Hpx Hqy pne0 qne0 Hqq.
move/(coprimep_comp_poly ('X - y%:P)).
rewrite comp_polyXaddC_K -gcdp_eqp1.
set p2 := (_ \Po _) => Hp2.
have: (gcdp p2 (q ^ iota) %= ('X - y%:P)).
  apply/andP; split; last first.
    rewrite -root_factor_theorem root_gcd Hqy andbT /root /p2 /p1 /p'.
    by rewrite !(horner_comp, hornerE) subrr mulr0 add0r.
  rewrite -[_ - _]mul1r.
  apply: (@dvdp_trans _ (gcdp (p2 * ('X - y%:P)) (q ^ iota))).
    rewrite dvdp_gcd dvdp_gcdr (dvdp_trans (dvdp_gcdl _ _)) // dvdp_mulr //.
  case/andP: Hp2.
  rewrite Hqq -(eqp_dvdl _ (mulp_gcdl _ _ _)) dvdp_mul2r //.
  by rewrite -size_poly_eq0 size_XsubC.
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
    rewrite coef0 -[X in _ = X](mulr0 (t ^+ i)) -[X in _ * X](coef0 _ i).
    rewrite -(Hqt i) -coefZ comp_polyE scaler_sumr -{1}[q]coefK poly_def.
    rewrite !coef_sum.
    apply: eq_bigr => j _.
    rewrite exprZn !coefZ mulrA [t ^+ i * _]mulrC -mulrA coefXn.
    case: (eqVneq i j) => [-> | Hij].
      by rewrite exprVn mulVKf // expf_eq0 negb_and Ht orbT.
    by rewrite -[_ == _]negbK Hij !mulr0.
  apply/eqP.
  move/eqP: Hqy <-.
  rewrite comp_polyE rmorph_sum /root horner_sum horner_coef size_map_poly.
  apply eq_bigr => i _ /=.
  rewrite map_polyZ rmorphX /= map_polyZ map_polyX coef_map.
  rewrite hornerZ horner_exp hornerZ hornerX.
  by rewrite fmorphV mulKf // fmorph_eq0.
pose f := annul_sub qt p.
have Hf0 : f != 0 by rewrite annul_sub_neq0.
have Hfz : root (f ^ iota) z by rewrite rootE annul_sub_iotaP //; apply/rootP.
set Fz := subFExtend iota z f.
set kappa := (@subfx_inj _ _ _ _ _) : Fz -> L.
pose (Q := (q ^ (inj_subfx iota z f))).
have HQ : q ^ iota = Q ^ kappa.
  rewrite /Q -map_poly_comp ?[kappa 0]rmorph0 // !map_polyE.
  congr (Poly _); apply: eq_map => a.
  by rewrite /= /kappa subfx_inj_eval // map_polyC hornerC.
pose (P := (p ^ (inj_subfx iota z f) \Po
  ((inj_subfx iota z f t) *: 'X - (subfx_eval iota z f 'X)%:P))).
have HP : p2 = P ^ kappa.
  rewrite -!horner_map rmorphB /= map_polyZ map_polyC map_polyX /=.
  rewrite !subfx_inj_eval // map_polyX map_polyC hornerX hornerC.
  rewrite -map_poly_comp ?rmorph0 //.
  rewrite (eq_map_poly (map_polyC _)).
  rewrite map_poly_comp ?rmorph0 //=.
  rewrite -[(p ^ _) ^ _]map_poly_comp ?rmorph0 //.
  rewrite (eq_map_poly (fun q => subfx_inj_eval (polyC q) Hf0 Hfz)).
  rewrite (eq_map_poly (horner_morphC _)); last by move => ?; apply: mulrC.
  rewrite /p2 /p1 /p' -!comp_polyA {2 3}/comp_poly.
  rewrite rmorphM rmorphD ![GRing.RMorphism.apply _]/= !map_polyX !map_polyC.
  rewrite !hornerE mulrDr -addrA -polyC_opp -polyC_mul polyC_add opprD.
  by rewrite -!polyC_opp opprK mulrN mul_polyC.
rewrite HQ HP -gcdp_map /=.
move/eqpP => [[c1 c2]] /andP [Hc1 Hc2].
move/(canLR (scalerK Hc2)).
rewrite scalerA.
move/polyP => Hgcd.
move:(Hgcd 1%N).
rewrite coefD coefN coefC coefX subr0 coefZ coef_map mulr1n.
move => Hgcd1.
move:(oner_neq0 L).
rewrite -Hgcd1 mulf_eq0 negb_or.
move/andP => [Hc120 Hgcd10].
move/eqP:(Hgcd 0%N).
rewrite coefD coefN coefC coefX coefZ coef_map sub0r -eqr_oppLR.
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
case/Pdiv.Field.dvdpP: (dvdp_gcdl q q^`()) => [qq Hq].
have Hqqy : root (qq ^ iota) y.
  have [[|n] [r Hry Hqr]] := multiplicity_XsubC (q ^ iota) y.
    by move: Hqy Hry; rewrite map_poly_eq0 qne0 Hqr mulr1 => ->.
  have := congr1 (@deriv _) Hqr.
  rewrite deriv_map derivM deriv_exp derivXsubC mul1r exprS -mulr_natl !mulrA.
  rewrite -mulrDl => Hq'.
  have: ('X - y%:P) ^+ n.+1 %| q ^iota by rewrite Hqr; apply: dvdp_mulIr.
  move: (f_equal (map_poly iota) Hq).
  rewrite rmorphM /=.
  rewrite gcdp_map {2}Hqr.
  rewrite Hq' exprS mulrA => ->.
  set s1 := r * _.
  set s2 := r^`() * _ + _.
  set s3 := _ ^+ n.
  move: (mulp_gcdl s1 s2 s3).
  have:= qne0.
  rewrite Hq mulf_eq0 negb_or -(map_poly_eq0 iota).
  case/andP.
  move/eqp_mul2l => <- _.
  move/eqp_dvdr <-.
  rewrite mulrA dvdp_mul2r /s3 ?expf_eq0 ?polyXsubC_eq0 ?andbF //.
  rewrite -root_factor_theorem rootM root_gcd.
  case/orP => //.
  case/andP => _.
  rewrite root_factor_theorem dvdp_addr; last by rewrite dvdp_mull // dvdpp.
  rewrite -root_factor_theorem mulr_natr -scaler_nat rootZ; last first.
  rewrite -(rmorph0 iota) -(rmorph1 iota) -rmorphMn (inj_eq (fmorph_inj _)).
    by rewrite Hchar.
  by move=> ry0; rewrite map_poly_eq0 qne0 ry0 in Hry.
have Hsep: separablePolynomial qq.
 move: (make_separable qne0).
 rewrite {1}Hq mulpK; last by rewrite gcdp_eq0 negb_and qne0.
 by move/dvdp_separable; apply. 
case: (PET_Infinite_Case Hqqy Hsep) => f [Hf0 Hf].
pose s := mkseq (fun x => iota (x%:R : F)) (size f).
have Hs : uniq_roots s.
  rewrite uniq_rootsE.
  apply: mkseq_uniq.
  suff Hwlog: forall a b, iota (a%:R : F) = iota (b%:R : F) -> a <= b;
    move => a b Hab.
    apply/eqP.
    by rewrite eqn_leq !Hwlog.
  move/eqP: Hab.
  apply: contraLR.
  rewrite -ltnNge => Hab.
   rewrite (inj_eq (fmorph_inj iota)) -subr_eq0 -mulrnBr; last by rewrite ltnW.
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

Let F : {subfield L } := aspace1 _.

Definition separableElement (K : {vspace L}) x :=
  separablePolynomial (minPoly K x).

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

Lemma DerivationMul u v : u \in K -> v \in K -> D (u * v) = D u * v + u * D v.
Proof.
move/all_nthP: HD; rewrite size_tuple=> Dmult Hu Hv.
rewrite (coord_vbasis Hu) (coord_vbasis Hv) !(mulr_sumr, linear_sum).
rewrite -big_split /=; apply: eq_bigr => j _.
rewrite !mulr_suml linear_sum /= -big_split /=; apply: eq_bigr => i _.
rewrite -scalerAl linearZ /= -scalerAr linearZ /=.
move/all_nthP : (Dmult 0 _ (ltn_ord i)); rewrite size_tuple.
move/(_ 0 _ (ltn_ord j)); move/eqP->.
by rewrite ![D (_ *: _)]linearZ /= -!scalerAl -!scalerAr !scalerDr.
Qed.

Lemma Derivation_addp p q : map_poly D (p + q) = map_poly D p + map_poly D q.
Proof. by apply/polyP=> i; rewrite !{1}(coefD, coef_map) /= linearD. Qed.

Lemma Derivation_mulp p q : p \is a polyOver K -> q \is a polyOver K ->
 map_poly D (p * q) = map_poly D p * q + p * map_poly D q.
Proof.
move => Kp Kq; apply/polyP=> i.
rewrite coefD coef_map /=  ?linear0 //.
rewrite !coefM linear_sum /= -big_split; apply: eq_bigr => j _ /=.
by rewrite !{1}coef_map DerivationMul ?(polyOverP _).
Qed.

End Derivation.

Lemma subvDerivation E K D : (K <= E)%VS -> Derivation E D -> Derivation K D.
Proof.
move/subvP => HKE HD.
apply/allP => x Hx.
apply/allP => y Hy.
apply/eqP.
by rewrite (DerivationMul HD) // HKE // vbasis_mem.
Qed.

Section DerivationAlgebra.

Variables (E : {subfield L}) (D:'End(L)).
Hypothesis (HD : Derivation E D).

Lemma Derivation1 : D 1 = 0.
Proof.
rewrite (@addIr _ (D 1) (D 1) 0) // add0r.
by rewrite -{3}[1]mul1r (DerivationMul HD) ?mem1v // mulr1 mul1r.
Qed.

Lemma DerivationF x : x \in F -> D x = 0.
Proof. move => /vlineP[y ->]; by rewrite linearZ /= Derivation1 scaler0. Qed.

Lemma Derivation_exp x m : x \in E -> D (x ^+ m) = x ^+ m.-1 *+ m * D x.
Proof.
move => Hx.
case: m; first by rewrite expr0 mulr0n mul0r Derivation1.
elim; first by rewrite expr1 expr0 mul1r.
move => m Hm.
rewrite GRing.exprS (DerivationMul HD) //; last by apply: rpredX.
rewrite Hm /= [_ *+ m.+2]GRing.mulrS mulrDl.
rewrite {3}GRing.exprS mulrA -GRing.mulrnAr.
congr (_ + _).
elim: (m.+1); first by rewrite GRing.expr0 mulr1 mul1r.
move => a Ha.
by rewrite mulrC.
Qed.

Lemma DerivationPoly p x : p \is a polyOver E -> x \in E ->
 D p.[x] = (map_poly D p).[x] + (deriv p).[x] * D x.
Proof.
move => Hp Hx.
elim/poly_ind: p Hp => [|p c IHp].
  by rewrite !raddf0 horner0 mul0r add0r linear0.
move/polyOverP => Hp.
have Hp0: p \is a polyOver E.
  apply/polyOverP=> i.
  have:= Hp i.+1.
  by rewrite coefD coefMX coefC /= addr0; apply.
have->: map_poly D (p * 'X + c%:P) = map_poly D p * 'X + (D c)%:P.
  apply/polyP => i.
  rewrite !(coefD, coefMX, coefC, coef_map) ?linear0 //= linearD /=.
  by rewrite !(fun_if D) linear0.
rewrite hornerMXaddC linearD /= (DerivationMul HD) ?rpred_horner //.
rewrite (IHp Hp0) derivMXaddC !hornerD !hornerM !hornerX !hornerC.
rewrite !mulrDl -!addrA; congr (_ + _).
by rewrite addrC [_ + D c]addrC -mulrA [_ * x]mulrC mulrA addrA.
Qed.

End DerivationAlgebra.

Section SeparableElement.

Variable (K : {subfield L}).
Variable (x : L).

Lemma separableElementP :  
  reflect 
  (exists f, f \is a polyOver K /\ root f x /\ separablePolynomial f) 
   (separableElement K x).
Proof.
apply: (iffP idP).
  move => ?; exists (minPoly K x); do ! (split => //).
    by apply: minPolyOver.
   by apply: root_minPoly.
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
- by rewrite polyOverXsubC.
- by rewrite root_factor_theorem dvdpp.
by rewrite /separablePolynomial !derivCE coprimep1.
Qed.

Lemma separable_nzdmp : (separableElement K x) = (deriv (minPoly K x) != 0).
Proof.
rewrite /separableElement /separablePolynomial.
apply/idP/idP.
  apply: contraL.
  move/eqP ->.
  by rewrite coprimep0 -size_poly_eq1 size_minPoly eqSS -lt0n.
move => Hderiv.
have gcdl := (dvdp_gcdl (minPoly K x) (deriv (minPoly K x))).
have gcdK : gcdp (minPoly K x) (minPoly K x)^`() \in polyOver K.
  by rewrite gcdp_polyOver ?polyOver_deriv // minPolyOver.
rewrite -gcdp_eqp1 -size_poly_eq1 -dvdp1.
case/orP: (minPoly_irr gcdK gcdl); last first.
  rewrite /eqp.
  by case/andP.
rewrite /eqp dvdp_gcd dvdpp /=.
case/andP => _.
move/(dvdp_leq Hderiv) => Hsz.
move: (leq_trans Hsz (size_poly _ _)).
by rewrite size_minPoly ltnn.
Qed.

Lemma separableNXp : 
  reflect (exists2 p, p \in [char L] & 
            exists2 g, g \is a polyOver K & (minPoly K x) = g \Po 'X^p)
          (~~ separableElement K x).
Proof.
rewrite separable_nzdmp negbK.
apply: (iffP eqP); last first.
  move => [p Hp [g _ ->]].
  by rewrite deriv_comp derivXn -scaler_nat (charf0 Hp) scale0r mulr0.
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
  by apply: polyOver_poly => i _; rewrite (polyOverP _) ?minPolyOver.
rewrite comp_polyE size_poly_eq; last first.
  rewrite Hrp  -[elementDegree _ _]/((elementDegree K x).+1.-1) -size_minPoly.
  by rewrite [f`_(_)]Hlead oner_neq0.
apply/polyP => i.
rewrite coef_sum.
case Hpi: (p %| i)%N ;last first.
  transitivity (0:L).
    case: i Hpi => [|i Hpi]; first by rewrite dvdn0.
    rewrite -{2}(mul0r ((i.+1)%:R ^-1)) -{2}(coef0 _ i) -Hdf coef_deriv.
    by rewrite -mulr_natr mulfK // -(dvdn_charf Hp) Hpi.
  symmetry.
  apply: big1 => j _.
  rewrite coefZ -exprM coefXn.
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
  rewrite coefZ -exprM coefXn.
  case: (eqVneq s j) => [Hsj|]; first by move: Hrs; rewrite Hsj ltnNge leq_ord.
  by rewrite mulnC eqn_mul2l => /negbTE->; rewrite eqn0Ngt Hp0 mulr0.
pose (s' := Ordinal Hrs).
rewrite (bigD1 s') // coefZ -exprM coefXn {2}mulnC eq_refl mulr1.
rewrite coef_poly Hrs mulnC big1 ?[_ _ 0]addr0 // => j /negPf.
rewrite eq_sym => Hj.
by rewrite coefZ -exprM coefXn eqn_mul2l [s == j]Hj eqn0Ngt Hp0 mulr0.
Qed.

Lemma separableNrootdmp : 
  (separableElement K x) != (root (deriv (minPoly K x)) x).
Proof.
rewrite separable_nzdmp (size_elementDegree (_ : _ \is a polyOver K)).
- by case: (_ == 0).
- by rewrite polyOver_deriv // minPolyOver.
by rewrite (leq_trans (size_poly _ _)) // size_minPoly leqnn.
Qed.

Lemma DerivationSeparable D : Derivation <<K; x>>%AS D -> 
 (separableElement K x) ->
 D x = - (map_poly D (minPoly K x)).[x] / ((minPoly K x)^`()).[x].
Proof.
move => Dderiv.
move: separableNrootdmp.
rewrite negb_eqb addbC /root.
move/addbP => <- Hroot.
apply: (canRL (mulfK Hroot)).
rewrite -sub0r.
apply: (canRL (addrK _)).
rewrite mulrC addrC -(DerivationPoly Dderiv) ?memv_adjoin //; last first.
   by apply: polyOverSv (minPolyOver _ _); apply: subv_adjoin.
by rewrite minPolyxx linear0.
Qed.

Section DerivationExtend.

Variable D:'End(L).

Let Dx E := - (map_poly D (minPoly E x)).[x] / ((minPoly E x)^`()).[x].

Fact DerivationExtend_subproof E :
  let body y (p := poly_for_Fadjoin E x y) :=
    (map_poly D p).[x] + (p^`()).[x] * (Dx E) in
  linear body.
Proof.
move: Dx => C /= a u v.
rewrite linearP /= -mul_polyC derivD derivM derivC mul0r add0r.
rewrite !hornerE_comm -scalerAl mul1r.
move : (poly_for_Fadjoin _ _ _) => pu.
move : (poly_for_Fadjoin _ _ _) => pv.
have ->: map_poly D (a%:A%:P * pu + pv)
           = a%:A%:P * map_poly D pu + map_poly D pv.
- apply/polyP => i; rewrite !coef_map ?linear0 // !coefD.
  rewrite !{1}coefCM !{1}coef_map ?{1}linear0 //= -!{1}scalerAl !mul1r.
  by rewrite linearP.
rewrite !{1}hornerE_comm -scalerAl mul1r mulrDl scalerDr -scalerAl -addrA.
by rewrite [(_.[x] + _)]addrA [_ + (a *: (_ * _))]addrC /= !{1}addrA.
Qed.

Definition DerivationExtend E : 'End(L) :=
  linfun (Linear (DerivationExtend_subproof E)).

Hypothesis HD: Derivation K D.

Lemma DerivationExtended y : y \in K -> DerivationExtend K y = D y.
Proof.
move=> yK; rewrite lfunE /= poly_for_K //.
rewrite  derivC horner0 mul0r addr0 -[D y](hornerC _ x) /horner_morph.
congr (_.[x]).
apply/polyP => i.
by rewrite (coef_map [linear of D]) ?linear0 //= !coefC [D _]fun_if linear0.
Qed.

Lemma DerivationExtend_Poly p : p \is a polyOver K -> separableElement K x ->
 DerivationExtend K (p.[x]) = (map_poly D p).[x] + p^`().[x] * Dx K.
Proof.
move => Kp sep.
move: separableNrootdmp.
rewrite negb_eqb addbC /root sep addbT {sep} /= => sep.
rewrite {-1}(divp_eq p (minPoly K x)) lfunE /=.
rewrite poly_for_modp // /horner_morph Derivation_addp
        ?{1}(Derivation_mulp HD)
        ?{1}(rpredM, divp_polyOver, modp_polyOver, minPolyOver) //.
rewrite derivD derivM !{1}hornerD !{1}hornerM minPolyxx !{1}mulr0 !{1}add0r.
rewrite mulrDl addrA [_ + (_ * _ * _)]addrC {2}/Dx /horner_morph -mulrA -/Dx.
by rewrite [((minPoly K x)^`()).[x] * _]mulrC (mulfVK sep) mulrN addKr.
Qed.

Lemma DerivationExtendDerivation :
 (separableElement K x) -> Derivation <<K; x>>%AS (DerivationExtend K).
Proof.
move => sep.
apply/allP => u; move/vbasis_mem => Hu.
apply/allP => v; move/vbasis_mem => Hv.
apply/eqP.
rewrite -(poly_for_eq Hu) -(poly_for_eq Hv) -hornerM !{1}DerivationExtend_Poly
        ?{1}rpredM ?{1}poly_for_polyOver // /horner_morph (Derivation_mulp HD)
        ?{1}poly_for_polyOver // derivM !{1}hornerD !{1}hornerM !{1}mulrDl 
        !{1}mulrDr -!addrA; congr (_ + _).
move:Dx => Dx0.
rewrite -!{1}mulrA [(Dx0 _) * _]mulrC !{1}addrA; congr (_ + _).
by rewrite addrC.
Qed.

End DerivationExtend.

(* Reference: 
http://www.math.uconn.edu/~kconrad/blurbs/galoistheory/separable2.pdf *)
Lemma separableDerivationP :
  reflect (forall D, Derivation <<K; x>>%AS D ->
                     (K <= lker D)%VS -> (<<K; x>>%AS <= lker D)%VS)
          (separableElement K x).
Proof.
apply introP.
  move => sep D DD.
  move/subvP => K0.
  apply/subvP => ?.
  move/poly_Fadjoin => [p Hp ->].
  have HD0 : forall q, q \is a polyOver K -> map_poly D q = 0.
    move=> q /polyOverP qK; apply/polyP => i; apply/eqP.
    by rewrite coef_map ?linear0 //= coef0 -memv_ker K0 ?qK.
  rewrite memv_ker (DerivationPoly DD) ?memv_adjoin
          ?(polyOverSv (subv_adjoin _ _) Hp) //.
  rewrite (DerivationSeparable DD sep) /horner_morph !HD0 ?minPolyOver //.
  by rewrite horner0 oppr0 mul0r mulr0 addr0.
move => nsep.
move: separableNrootdmp (nsep).
rewrite negb_eqb.
move/addbP ->.
rewrite /root; move/eqP => Hroot.
have Dlin : linear (fun y => (poly_for_Fadjoin K x y)^`().[x]).
  move => a u v; rewrite linearP /= -mul_polyC derivD derivM derivC mul0r add0r.
  by rewrite hornerD hornerM hornerC -scalerAl mul1r.
pose D := linfun (Linear Dlin).
have DF : (K <= lker D)%VS.
  apply/subvP => v vK.
  by rewrite memv_ker lfunE /= poly_for_K // derivC horner0.
have DDeriv : Derivation <<K; x>>%AS D.
  apply/allP => u; move/vbasis_mem => Hu.
  apply/allP => v; move/vbasis_mem => Hv.
  by rewrite !lfunE /= -{-2}(poly_for_eq Hu)
             -{-3}(poly_for_eq Hv) -!hornerM -hornerD -derivM 
             poly_for_modp ?rpredM ?poly_for_polyOver // 
             {2}(divp_eq (_ * _) (minPoly K x)) derivD derivM
             !hornerD !hornerM Hroot minPolyxx !mulr0 !add0r.
have Dx : D x = 1.
  rewrite !lfunE /= (_ : (poly_for_Fadjoin K x x) = 'X) ?derivX ?hornerC //.
  apply: (@poly_Fadjoin_small_uniq _ _ K x).
  - exact: poly_for_polyOver.
  - exact: polyOverX.
  - exact: size_poly_for.
  - rewrite size_polyX ltn_neqAle andbT eq_sym.
    apply: contra nsep.
    move/eqP => eD.
    rewrite separable_nzdmp (_ : (minPoly K x)^`() = 1%:P)  ?oner_neq0 //.
    apply/polyP => i.
    rewrite coef_deriv coefC.
    case: i => [|i].
      move: (monic_minPoly K x); rewrite monicE lead_coefE size_minPoly eD.
      by move/eqP ->.
    rewrite (_ : (minPoly K x)`_i.+2 = 0) ?mul0rn //.
    move: (leqnn (size (minPoly K x))); rewrite {2}size_minPoly eD.
    by move/leq_sizeP->.
  by rewrite hornerX (poly_for_eq (memv_adjoin _ _)).
move/(_ _ DDeriv DF).
apply/negP.
move/eqP: Dx.
apply: contraL.
move/subvP.
move/(_ _ (memv_adjoin _ _)).
rewrite memv_ker.
move/eqP ->.
rewrite eq_sym.
by apply: oner_neq0.
Qed.

End SeparableElement.

Implicit Types K E : {subfield L}.

Lemma separableElementS : forall K E x, (K <= E)%VS -> 
 separableElement K x -> separableElement E x.
Proof.
move => K E x KE.
move/separableElementP => [f [fK [rootf sepf]]].
apply/separableElementP.
exists f; split => //.
by apply: (polyOverSv KE).
Qed.

Lemma allSeparableElement K x :
  reflect (forall y, y \in <<K; x>>%AS -> separableElement K y)
          (separableElement K x).
Proof.
apply: (iffP idP); last by apply; apply: memv_adjoin.
move => sep ?.
move/poly_Fadjoin => [q Hq ->].
apply/separableDerivationP => D DD.
move/subvP => KD0.
apply/subvP => ?.
move/poly_Fadjoin => [p Hp ->].
rewrite memv_ker -(DerivationExtended x D (mempx_Fadjoin _ Hp)).
have sepFyx : (separableElement <<K; q.[x]>>%AS x).
  by apply: (separableElementS (subv_adjoin _ _)).
have KyxEqKx : << <<K; q.[x]>>%AS; x>>%AS = <<K; x>>%AS.
  apply: subv_anti; apply/andP; split; last by rewrite adjoinSl // subv_adjoin.
  apply/FadjoinP/andP; rewrite memv_adjoin andbT.
  by apply/FadjoinP/andP; rewrite subv_adjoin mempx_Fadjoin.
rewrite -horner_comp.
move: (DerivationExtendDerivation DD sepFyx).
rewrite KyxEqKx => DED.
rewrite (DerivationPoly DED); last first.
    apply: memv_adjoin.
  apply: (polyOverSv (subv_adjoin _ _)).
  exact: polyOver_comp.
suff hmD : forall t, t \is a polyOver K ->
           (map_poly (DerivationExtend x D <<K; q.[x]>>%AS) t).[x] = 0.
  rewrite (DerivationSeparable DED); last done.
  rewrite !{1}hmD; first by rewrite oppr0 mul0r mulr0 addr0.
    exact: minPolyOver.
  exact: polyOver_comp.
move => t.
move/polyOverP => Ht.
rewrite /horner_morph (_ : map_poly _ _ = 0); first by rewrite horner0.
apply/polyP => i.
rewrite coef0 {1}coef_map /= {1}DerivationExtended.
  apply/eqP.
  by rewrite -memv_ker KD0 ?Ht.
apply: (subv_trans _ (subv_adjoin _ _)).
by apply: Ht.
Qed.

Section SeparableInCharP.

Variable (K : {subfield L}).

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
 rewrite -exprM => Hsepxpm.
 exists (p * m)%N => //.
 by rewrite pnat_mul pnatE ?(charf_prime Hp) // Hp Hm.
rewrite -ltnS (leq_trans _ Hdeg) // -size_minPoly -ltnS -size_minPoly.
apply: (@leq_ltn_trans (size g)).
 apply: dvdp_leq; last first.
  apply: minPoly_dvdp => //.
  by rewrite /root -hornerXn -horner_comp -Hg minPolyxx.
 move/eqP: Hg.
 apply: contraL.
 move/eqP ->.
 by rewrite comp_poly0 -size_poly_eq0 size_minPoly.
rewrite -[size (minPoly K x)](prednK); last by rewrite size_minPoly.
rewrite Hg size_comp_poly ltnS size_polyXn.
case: (leqP (size g) 1) Hg.
 move/size1_polyC ->.
 rewrite comp_polyC => Hg.
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
 separableElement K x = (x \in <<K; x ^+ (p ^ e.+1)>>%AS).
Proof.
move => x e p Hp.
apply/idP/idP; last first.
 move/poly_for_eq.
 set (f := (poly_for_Fadjoin K (x ^+ (p ^ e.+1)) x)).
 move => Hx.
 apply/separableElementP.
 exists ('X - (f \Po 'X^(p ^ e.+1))); split.
  by rewrite rpredB ?polyOver_comp ?rpredX ?polyOverX ?poly_for_polyOver.
 split.
  by rewrite /root !hornerE horner_comp hornerXn Hx subrr.
 rewrite /separablePolynomial !(derivE, deriv_comp).
 have : (p %| p ^ e.+1)%N by rewrite dvdn_exp.
 rewrite -mulr_natr (dvdn_charf Hp) -polyC_muln.
 move/eqP ->.
 by rewrite polyC0 !mulr0 subr0 coprimep1.
wlog: e x / e = 0%N.
 move => H.
 elim: e.+1; first by rewrite expr1 memv_adjoin.
 move => {e} e IH Hsep.
 rewrite expnS mulnC exprM -{2}[p]expn1.
 have : (<<K; x ^+ (p ^ e)>>%AS <= <<K; x ^+ (p ^ e) ^+ (p ^ 1)>>%AS)%VS.
  move/allSeparableElement: Hsep => Hsep.
  apply/FadjoinP/andP.
  by rewrite subv_adjoin H ?Hsep ?rpredX ?memv_adjoin.
 move/subvP; apply.
 by apply IH.
move => -> {e}.
pose K' : {subfield L} := [aspace of <<K; x ^+ p>>%AS].
pose g := 'X^p - (x ^+ p)%:P.
have HK'g : g \in polyOver K'.
  by rewrite rpredB ?rpredX ?polyOverX // polyOverC memv_adjoin.
have rootg : root g x by rewrite /root !hornerE hornerXn subrr.
move/(separableElementS (subv_adjoin _ (x ^+ p))).
move : (root_minPoly K' x) (minPoly_dvdp HK'g rootg) (minPolyOver K' x).
rewrite root_factor_theorem /separableElement -/K'.
case/(dvdpP) => c -> Hcg HK'c.
rewrite separable_mul.
have Hp' : p \in [char {poly L}] by apply: (rmorph_char (polyC_rmorphism _)).
case/and3P => _ _ Hc.
 have : (coprimep c g).
 rewrite /g polyC_exp -!(Frobenius_autE Hp') -rmorphB.
 rewrite [_ (_ - _)]Frobenius_autE -(prednK (prime_gt0 (charf_prime Hp))).
 elim: p.-1 => [|n]; first by rewrite expr1.
 by rewrite [_ ^+ _.+2]exprS coprimep_mulr Hc.
move/coprimepP/(_ _ (dvdpp c))/(_ (dvdp_trans (dvdp_mulr _ (dvdpp c)) Hcg)).
rewrite -size_poly_eq1.
move/eqP => Hszc.
move: HK'c (Hszc).
rewrite (size1_polyC (eq_leq Hszc)) size_polyC mulrDr -polyC_opp -polyC_mul.
move/polyOverP => Hx; move: (Hx 1%N) (Hx 0%N).
rewrite !coefD !coefMX !coefC add0r addr0 => Hx1 Hx0.
case Hc0 : (c`_0 != 0) => // _.
by rewrite -memvN -[(- x)](mulKf Hc0) memv_mul // rpredV.
Qed.

Lemma separableCharn : forall x n, n \in [char L].-nat ->
 1 < n -> separableElement K x = (x \in <<K; x ^+ n>>%AS).
Proof.
move => x n Hn H1n.
set p := pdiv n.
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

Variable K : {subfield L}.

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
rewrite addSnnS expnD exprM memv_adjoin_eq.
by move/eqP <-.
Qed.

(* begin hide *)

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
rewrite -(@divnK n m); first by rewrite mulnC exprM memv_exp.
apply/dvdn_partP; first by case/andP: Hn.
move => p.
move/(pnatPpi Hn) => Hp.
rewrite p_part pfactor_dvdn; [|by apply: (charf_prime Hp)|by case/andP: Hm].
rewrite -(@leq_exp2l p); last by apply/prime_gt1/(charf_prime Hp).
by rewrite -!p_part !part_pnat_id // -(eq_pnat _ (charf_eq Hp)).
Qed.
*)

(* end hide *)

Lemma separableInseparableElement: forall x, 
 (x \in K) = separableElement K x && purelyInseparableElement K x.
Proof.
move => x; rewrite /purelyInseparableElement valK.
case: ex_minnP=> [[//|[/=|m]]] => [-> // | _ /(_ 1%N)/implyP/= not_sep_x].
by rewrite (contraNF (@separableinK K x) not_sep_x) (negPf not_sep_x).
Qed.

Lemma inseparableinK : forall x, x \in K -> purelyInseparableElement K x.
Proof. move => x. rewrite separableInseparableElement. by case/andP. Qed.

End PurelyInseparableElement.

Lemma subsetInseparable:
  forall (K E : {subfield L}) (x : L),
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

Variable K : {subfield L}.
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
 by rewrite (polyOverP _) ?poly_for_polyOver.
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
 move=> Ha /esym.
 rewrite distnC.
 by apply: HW.
move/ffunP.
rewrite (distnEr Ha) => Hha.
have Hza: (z ^+ a1 != 0) by exact: expf_neq0.
apply/eqP.
rewrite -(can_eq (mulfK Hza)) -exprD mul1r subnK //.
apply/eqP; symmetry.
have Hzi : forall i,  z ^+ i \in <<K; z>>%AS.
 by move => i; apply: rpredX; exact: memv_adjoin.
move/poly_for_eq:(Hzi a1) <-.
move/poly_for_eq:(Hzi a2) <-.
have Z:=(horner_coef_wide z (size_poly_for K z (z ^+ _))).
rewrite !{1}Z.
apply: eq_bigr => i _.
apply: f_equal2; last done.
move: (Hha i).
rewrite /h !ffunE.
by move/(f_equal val) => /=.
Qed.

Lemma PET_finiteCase_subproof : 
  KisBig \/ exists z, << <<K; y>>%AS; x>>%AS = <<K; z>>%AS.
Proof.
case (eqVneq x 0) => [->|Hx0].
 right; exists y.
 apply/eqP.
 rewrite -memv_adjoin_eq.
 by apply: mem0v.
move/cyclicOrBig: (Hx0) => [|[[|a] Hxa]]; first by left.
 rewrite expr1 in Hxa.
 right; exists y.
 apply/eqP.
 rewrite -memv_adjoin_eq Hxa.
 by apply: mem1v.
case (eqVneq y 0) => [->|Hy0].
 right; exists x.
 move: (mem0v K).
 rewrite memv_adjoin_eq.
 by move/eqP ->.
move/cyclicOrBig: (Hy0) => [|[[|b] Hyb]]; first by left.
 rewrite expr1 in Hyb.
 right; exists x.
 move: (mem1v K).
 rewrite memv_adjoin_eq Hyb.
 by move/eqP ->.
right.
pose h0 := fun (i:'I_a.+2) (j:'I_b.+2) => x ^+ i * y ^+ j.
pose l := allpairs h0 (ord_enum _) (ord_enum _).
pose fT := seq_sub_finType l.
have Hl : forall i j, x ^+ i * y ^+ j \in l.
 move => i j.
 rewrite (divn_eq i (a.+2)) (divn_eq j (b.+2)).
 rewrite !exprD ![(_ * _.+2)%N]mulnC !exprM.
 rewrite Hxa Hyb !expr1n !mul1r.
 apply/allpairsP.
 exists (Ordinal (@ltn_pmod i (a.+2) (ltn0Sn _))
        ,Ordinal (@ltn_pmod j (b.+2) (ltn0Sn _)));
  split; by rewrite ?mem_ord_enum.
have HmulgT : forall (i j:fT), (val i) * (val j) \in l.
 case => ? /=; move/allpairsP => [[ix iy] [_ _ ->]].
 case => ? /=; move/allpairsP => [[jx jy] [_ _ ->]].
 rewrite /h0 /=.
 rewrite -mulrA [y ^+ iy * _]mulrA [y ^+ iy * _]mulrC -mulrA mulrA.
 by rewrite -!exprD.
pose mulgT := fun (i j:fT) => SeqSub (HmulgT i j):fT.
have HonegT : 1 \in l.
 by rewrite -[1]mulr1 -{1}(expr0 x) -(expr0 y).
pose onegT := SeqSub (HonegT):fT.
have HinvT : forall i:fT, (val i)^-1 \in l.
 case => ? /=; move/allpairsP => [[ix iy] [_ _ ->]].
 rewrite /h0 /=.
 rewrite invfM.
 rewrite -[x ^- ix]mul1r -Hxa -{1}[a.+2](subnK (ltnW (ltn_ord ix))) 
         exprD mulfK ?expf_neq0 //.
 by rewrite -[y ^- iy]mul1r -Hyb -{1}[b.+2](subnK (ltnW (ltn_ord iy)))
            exprD mulfK ?expf_neq0.
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
apply/andP;split;last first.
 apply/FadjoinP/andP.
 rewrite (subv_trans (subv_adjoin K y) (subv_adjoin _ x)) /h /=.
 case: z {Hz} => ? /=.
 move/allpairsP => [[ix iy] [_ _ ->]].
 rewrite /h0 /= memv_mul // rpredX //; first by rewrite memv_adjoin.
 by rewrite memv_mem_adjoin // memv_adjoin.
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
rewrite ![ssval _]Hhz.
do 2 (apply/FadjoinP/andP; rewrite rpredX ?memv_adjoin // andbT).
by rewrite subv_adjoin.
Qed.

End FiniteCase.

Hypothesis sep : separableElement K y.

Lemma PrimitiveElementTheorem : exists z, << <<K; y>>%AS; x>>%AS = <<K; z>>%AS.
Proof.
move/monic_neq0: (monic_minPoly K x).
case/polyOver_subvs: (minPolyOver K x) (root_minPoly K x) => p -> Hrootp.
rewrite map_poly_eq0 => Hp0.
case/separableElementP: sep => q0 [HKq0 [Hrootq0 Hsepq0]].
move: (minPoly_dvdp HKq0 Hrootq0).
case/polyOver_subvs: (minPolyOver K y) (root_minPoly K y) => q-> Hrootq Hqq0.
move: (dvdp_separable Hqq0 Hsepq0).
rewrite separable_map => Hsepq.
case: (PET_Infinite_Case Hp0 Hrootp Hrootq Hsepq) => r [Hr HPET].
case: (PET_finiteCase_subproof (size r)) => [[l /and3P [/allP HKl Hl Hnml]]|//].
move/contra: (fun x => max_poly_roots Hr x Hl).
rewrite -leqNgt.
case/(_ (ltnW Hnml))/allPn => c /HKl Hc Hrootc.
case: (HPET (Subvs Hc) Hrootc).
set z := (_ * y - x) => [[a Ha] [b Hb]].
exists z.
apply: subv_anti.
apply/andP;split; apply/FadjoinP/andP; last first.
 rewrite (subv_trans (subv_adjoin K y) (subv_adjoin _ x)) /=.
 rewrite memvB //; last by rewrite memv_adjoin.
 rewrite memv_mem_adjoin // rpredM //; last by rewrite memv_adjoin.
 by rewrite memv_mem_adjoin.
apply/andP; split; last first.
 apply/poly_Fadjoin.
 exists (map_poly vsval a); last by rewrite Ha.
 apply/polyOver_subvs.
 by exists a.
apply/FadjoinP/andP.
 rewrite subv_adjoin /=.
 apply/poly_Fadjoin.
 exists (map_poly vsval b); last by rewrite Hb.
 apply/polyOver_subvs.
 by exists b.
Qed.

Lemma separableFadjoinExtend : separableElement <<K; y>>%AS x -> 
  separableElement K x.
Proof.
move/separableDerivationP => sepx.
move/separableDerivationP: sep => sepy.
case: PrimitiveElementTheorem => z Hz.
suff/allSeparableElement : separableElement K z.
 by apply; rewrite -Hz memv_adjoin.
apply/separableDerivationP => D.
rewrite -Hz => HDz.
have HDy : Derivation <<K; y>>%AS D.
 apply: (subvDerivation _ HDz).
 by rewrite subv_adjoin.
move/(sepy _ HDy).
by apply: sepx=> /=.
Qed.

End PrimitiveElementTheorem.

Lemma StrongPrimitiveElementTheorem
     : forall (K : {subfield L}) (x y : L),
       separableElement <<K; x>>%AS y ->
       exists2 z : L, << <<K; y>>%AS; x>>%AS = <<K; z>>%AS &
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
rewrite -Hz.
rewrite closurea_add_closure -addvA [(<[_]> + <[_]>)%VS]addvC.
rewrite addvA -closurea_add_closure.
symmetry.
rewrite closurea_add_closure -addvA [(<[_]> + <[_]>)%VS]addvC.
rewrite addvA -closurea_add_closure.
apply: subv_anti.
apply/andP; split; apply/FadjoinP/andP; rewrite subv_adjoin /=.
  by rewrite rpredX ?memv_adjoin.
by rewrite -separableCharn // Hsep.
Qed.

Section SeparableAndInseparableExtensions.

Definition separable (K E : {vspace L}) : bool :=
 all (separableElement K) (vbasis E).

Definition purelyInseparable (K E : {vspace L}) : bool :=
 all (purelyInseparableElement K) (vbasis E).

Variable (K : {subfield L}).

Lemma separable_add : forall x y,
  separableElement K x -> separableElement K y -> separableElement K (x + y).
Proof.
move => x y Hx Hy.
case: (PrimitiveElementTheorem x Hy) => z Hz.
have: (x + y) \in << <<K; y>>%AS; x>>%AS.
  by apply: memvD; last apply: memv_mem_adjoin; apply: memv_adjoin.
rewrite Hz.
move: (x + y); apply/allSeparableElement.
apply: (separableFadjoinExtend Hy).
apply: (@separableFadjoinExtend _ _ x); last first.
  by rewrite Hz separableinK ?memv_adjoin.
by apply: (separableElementS (subv_adjoin K y)).
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
by rewrite exprDn_char // {2}mulnC !exprM memvD // rpredX.
Qed.

Lemma inseparable_sum : forall I r (P : pred I) (v_ : I -> L),
  (forall i, P i -> purelyInseparableElement K (v_ i)) ->
  purelyInseparableElement K (\sum_(i <- r | P i) v_ i).
Proof.
apply: (@big_ind L (purelyInseparableElement K)).
 apply/inseparableinK/mem0v.
apply: inseparable_add.
Qed.

Variable (E : {subfield L}).

Lemma separableP :
  reflect (forall y, y \in E -> separableElement K y)
          (separable K E).
Proof.
apply (iffP idP); last first.
 move => HEK.
 apply/allP => x; move/vbasis_mem => Hx.
 by apply: HEK.
move/allP => HEK y.
move/coord_vbasis ->.
apply/separable_sum => i _.
have/allSeparableElement : (separableElement K (vbasis E)`_i).
 case: (leqP (size (vbasis E)) i); last by move/(mem_nth 0)/HEK.
 by move/(nth_default 0) ->; rewrite separableinK // mem0v.
apply.
by rewrite memvZ // memv_adjoin.
Qed.

Lemma purelyInseparableP :
  reflect (forall y, y \in E -> purelyInseparableElement K y)
          (purelyInseparable K E).
Proof.
apply (iffP idP); last first.
 move => HEK.
 apply/allP => x; move/vbasis_mem => Hx.
 by apply: HEK.
move/allP => HEK y.
move/coord_vbasis ->.
apply/inseparable_sum => i _.
have : (vbasis E)`_i \in vbasis E.
 rewrite mem_nth //.
 case: (vbasis E) => /= ?.
 by move/eqP ->.
case/HEK/purelyInseparableElementP => n Hn HK.
apply/purelyInseparableElementP.
exists n => //.
by rewrite exprZn memvZ.
Qed.

End SeparableAndInseparableExtensions.

Section SeparableInseparableDecomposition.

Lemma separableSeparableExtension : forall K x,
 separableElement K x = separable K <<K; x>>%AS.
Proof.
move => K x.
by apply/(sameP (allSeparableElement _ _))/(iffP (separableP _ _)).
Qed.

Lemma separableInseparableDecomposition : forall E K ,
 exists x, [&& x \in E, separableElement K x & 
             purelyInseparable <<K; x>>%AS E].
Proof.
move => E K.
wlog: K / (K <= E)%VS => [|HKE].
 case/(_ _ (capvSr K E)) => x.
 case/and3P => HxE Hsep.
 move/purelyInseparableP => Hinsep.
 exists x.
 apply/and3P; split; first done.
  by apply/(separableElementS _ Hsep)/capvSl.
 apply/purelyInseparableP => y Hy.
 apply: subsetInseparable; last by apply Hinsep.
 by apply/adjoinSl/capvSl.
set (f := fun i => 
      (vbasis E)`_i ^+ ex_minn (separablePower K (vbasis E)`_i)).
set (s := mkseq f (\dim E)).
have Hsep : all (separableElement K) s.
 apply/allP => x.
 case/mapP => i _ ->.
 rewrite /f.
 by case ex_minnP => m; case/andP.
pose K' : {subfield L} :=
  foldr (fun x (y : {subfield L}) => [aspace of <<y; x>>%AS]) K s.
have: exists x, [&& x \in E, separableElement K x
                  & K' == <<K; x>>%AS :> {vspace _}].
 rewrite /K' {K'}.
 have: all (fun x => x \in E) s.
  apply/allP => ?.
  case/mapP => i.
  rewrite mem_iota => Hi ->.
  rewrite /f rpredX // vbasis_mem // mem_nth //.
  case: (vbasis E) => ? /=.
  by move/eqP ->.
 elim: s Hsep => [|t s IH].
  exists 0.
  apply/and3P; split => //; first by rewrite mem0v.
   by rewrite separableinK // mem0v.
  by rewrite eq_sym addv0 subfield_closed.
 case/andP => Ht Hs.
 case/andP => HtE HsE.
 case: (IH Hs HsE) => y.
 case/and3P => HyE Hsep Hy.
 case: (PrimitiveElementTheorem t Hsep) => x Hx.
 exists x.
 apply/and3P; split.
   suff: (<<K; x>>%AS <= E)%VS by move/subvP; apply; rewrite memv_adjoin.
   rewrite -Hx.
   apply/FadjoinP; split => //.
   by apply/FadjoinP/andP; rewrite HKE HyE.
  apply/allSeparableElement => z.
  rewrite -Hx => Hz.
  apply: (separableFadjoinExtend Hsep).
  move/allSeparableElement: (separableElementS (subv_adjoin K y) Ht).
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
case/orP; last by move => ?; apply/memv_mem_adjoin/IH.
move/eqP ->.
by apply: memv_adjoin.
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
 purelyInseparable <<K; separableGenerator K E>>%AS E.
Proof.
move => E K.
by case/and3P: (choice.xchooseP 
  (separableInseparableDecomposition E K)).
Qed.

Lemma separableSeparableGeneratorEx : forall E K,
 separable K E -> (E <= <<K; separableGenerator K E>>%AS)%VS.
Proof.
move => E K.
move/separableP => Hsep.
apply/subvP => v Hv.
rewrite separableInseparableElement.
move/purelyInseparableP/(_ _ Hv): (separableGeneratorMaximal E K) ->.
by rewrite (separableElementS _ (Hsep _ Hv)) // subv_adjoin.
Qed.

Lemma separableSeparableGenerator : forall E K,
 separable K E -> (K <= E)%VS ->
 E = <<K; separableGenerator K E>>%AS :> {vspace _}.
Proof.
move => E K Hsep HKE.
apply: subv_anti.
rewrite separableSeparableGeneratorEx //=.
by apply/FadjoinP/andP; rewrite HKE separableGeneratorInE.
Qed.

End SeparableInseparableDecomposition.

Lemma separable_refl (K : {subfield L}) : separable K K.
Proof. by apply/separableP; apply: separableinK. Qed.

Lemma separable_trans (M K E : {subfield L}) :
  separable K M -> separable M E -> separable K E.
Proof.
move/separableSeparableGeneratorEx.
set x := (separableGenerator K M) => HKM /separableP HME.
apply/separableP => w /HME/(separableElementS HKM).
case/StrongPrimitiveElementTheorem => _ _; apply.
apply: separableGeneratorSep.
Qed.

Lemma separableSl (K M E : {subfield L}) : (K <= M)%VS -> separable K E ->
  separable M E.
Proof.
move => HKM /separableP HKE.
apply/separableP => y Hy.
apply: (separableElementS HKM).
by apply: HKE.
Qed.

Lemma separableSr (K M E : {subfield L}) : (M <= E)%VS -> separable K E ->
  separable K M.
Proof.
move => /subvP HME /separableP HKE.
apply/separableP => y Hy.
by apply: HKE; apply: HME.
Qed.

Lemma separableS (K1 K2 E2 E1 : {subfield L}) : 
  (K1 <= K2)%VS -> (E2 <= E1)%VS -> separable K1 E1 ->
  separable K2 E2.
Proof.
move => HK HE Hsep.
by apply: (separableSr HE); apply (separableSl HK).
Qed.

Lemma separable_Fadjoin_seq (K : {subfield L}) rs :
  all (separableElement K) rs -> separable K <<K & rs>>%AS.
Proof.
elim: rs K => [|/= x rs IH] K.
  by rewrite span_nil addv0 subfield_closed separable_refl.
case/andP => Hx /allP Hrs.
apply: (@separable_trans [aspace of <<K; x>>%AS]) => /=.
  by rewrite -separableSeparableExtension.
rewrite span_cons addvA -[<<_ & rs>>%AS]closurea_add_closure.
apply IH.
apply/allP => y Hy.
by apply: (separableElementS (subv_adjoin K x)) (Hrs _ _).
Qed.

Lemma purelyInseperable_refl (K : {subfield L}) : purelyInseparable K K.
Proof. by apply/purelyInseparableP; apply: inseparableinK. Qed.

(*
Lemma purelyInseparable_trans (M K E : {subfield L}) :
  purelyInseparable K M -> purelyInseparable M E -> purelyInseparable K E.
*)

End Separable.