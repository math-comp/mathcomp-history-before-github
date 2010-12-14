(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Require Import fintype finfun bigop ssralg poly polydiv.
Require Import zmodp vector algebra fieldext.
Require Import fingroup perm finset matrix mxalgebra.


(******************************************************************************)
(* This file is supposed to provide galois theory, however it is currently    *)
(* almost entirely about field extentions and the contents should perahps be  *)
(* moved there.                                                               *)
(*                                                                            *)
(*           polyOver K p == the coefficents of p lie in the subspace K       *)
(*          FadjoinVS K x == K(x) as a vector space                           *)
(*            Fadjoin K x == same as FadjoinVS K but of subalgebra type       *)
(*            minPoly K x == the monic minimal polynomial of x over the       *)
(*                           subfield K                                       *)
(*      elementDegree K x == the degree of the minimial polynomial or the     *)
(*                           dimension of K(x)/K                              *)
(* poly_for_Fadjoin K x y == a polynomial p over K such that y = p.[x]        *)
(*                                                                            *)
(*  seperablePolynomial p == p has no repeated roots in any field extension   *)
(*   seperableElement K x == the minimal polynomial for x is seperable        *)
(*                                                                            *)
(*  Derivations are only meant as a tool to prove allSeperableElement         *)
(*         Derivation K D == D is a linear operator on K that satifies        *)
(*                           Leibniz's product rule                           *)
(* DerivationExtend K x D == Given a derivation D on K and a seperable        *)
(*                           element x over K, this function returns the      *)
(*                           unique extension of D to K(x).                   *)
(******************************************************************************)


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Local Scope ring_scope.

Import GRing.Theory.

Section SeperablePoly.

Variable (R: idomainType).
Variable (p q : {poly R}).

Definition seperablePolynomial (p:{poly R}) := coprimep p (deriv p).

Lemma seperable_mul : seperablePolynomial (p * q) = 
 [&& seperablePolynomial p, seperablePolynomial q & coprimep p q].
Proof.
have dvdpR : forall (p q : {poly R}), p %| p * q.
 by move => p0 q0; rewrite dvdp_mulr // dvdpp.
have dvdpL : forall (p q : {poly R}), q %| p * q.
 by move => p0 q0; rewrite dvdp_mull // dvdpp.
rewrite /seperablePolynomial.
rewrite derivM.
rewrite -!gcdp_eqp1 !eqp1_dvd1.
have dvdp_or : forall (d n m : {poly R}), (d %| n) || (d %| m) -> d %| m * n.
 move => d n m.
 by move/orP => [H|H]; [apply:dvdp_mull|apply: dvdp_mulr].
apply/idP/and3P => [H|[Hp Hq Hpq]].
 by split; apply: dvdp_trans H; rewrite dvdp_gcd; apply/andP; split;
   rewrite ?(dvdp_add, dvdp_or, dvdp_gcdl, dvdp_gcdr) // orb_true_r.
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

End SeperablePoly.

Section Galois.

Variable F0 : fieldType.
Variable L : fieldExtType F0.

Let F : {algebra L } := aspace1 _.

Lemma dim_prodvf : forall (K:{vspace L}) x, x != 0 -> \dim (K * x%:VS) = \dim K.
Proof.
have: forall (K:{vspace L}) x, x != 0 -> \dim (K * x%:VS) <= \dim K.
 move => K x Hx.
 by rewrite (leq_trans (dim_prodv _ _)) // dim_injv Hx muln1.
move => suff K x Hx.
apply: anti_leq.
(* why do I need the {vspace L} annotation? *)
by rewrite suff //= -{1}[K:{vspace L}]prodv1 -(mulfV Hx) prodv_inj prodvA
           suff // invr_neq0.
Qed.

Section SubAlgebra.

Variable K : {algebra L}.

Lemma memv1 : 1 \in K.
Proof.
by rewrite -aunit1 -(can_eq (mulfK (anonzero1r K))) mul1r
           (aunitl (memv_unit K)).
Qed.

Lemma aunit_eq1 : aunit K = 1.
Proof. by apply/eqP; rewrite aunit1 memv1. Qed.

Lemma subset1v : (1%:VS <= K)%VS.
Proof. by apply: memv1. Qed.

Lemma subsetv1 : ((K <= 1%:VS) = (K == F))%VS.
Proof.
apply/idP/idP; last by move/eqP->; exact: subsetv_refl.
move=> H; rewrite /eq_op; apply/eqP.
by apply: subsetv_anti; rewrite H  subset1v.
Qed.

Lemma memv_exp : forall x i, x \in K -> x ^+ i \in K.
Proof.
move => x.
elim => [|i Hi] Hx.
 by rewrite expr0 memv1.
by rewrite exprS memv_mul // Hi.
Qed.

Lemma sa_val_rmorph : rmorphism (@sa_val _ _ K).
Proof.
split => //=; split => //=; exact: aunit_eq1.
Qed.

Canonical Structure sa_val_additive := Additive sa_val_rmorph.
Canonical Structure sa_val_rmorphism := RMorphism sa_val_rmorph.

Lemma suba_mul_com : commutative (@suba_mul _ _ K).
Proof. move=> u v; apply: val_inj; exact: mulrC. Qed.

Canonical Structure suba_comRingType :=
  Eval hnf in ComRingType (suba_of K) suba_mul_com.

Definition polyOver := [pred p : {poly L} | all (mem K) p].

Lemma polyOverP : forall p : {poly L},
  reflect (forall i, p`_i \in K) (polyOver p).
Proof.
move => p.
apply: (iffP allP).
 move => Hp i.
 case E : (leq (size p) i); first by rewrite nth_default // mem0v.
 apply: Hp.
 by rewrite mem_nth // ltnNge E.
move => hP x /=.
move/(nth_index _).
by move/(_ 0) <-.
Qed.

Lemma polyOver_suba : forall p : {poly L},
  reflect (exists q : {poly (suba_of K)}, p = map_poly (@sa_val _ _ K) q)
          (polyOver p).
Proof.
move => p.
apply: (iffP (polyOverP _)); last first.
 by move => [q ->] i; rewrite coef_map // subaP.
move => Hp.
exists (\poly_(i < size p) (Suba (Hp i))).
apply/polyP => i.
rewrite coef_map // coef_poly fun_if /=.
apply/eqP.
move: (@leq_coef_size _ p i).
case: (i < size (polyseq p)) => //.
move/(contraR).
by apply.
Qed.

Lemma addp_polyOver : forall p q : {poly L},
  polyOver p -> polyOver q -> polyOver (p + q).
Proof.
move => ? ?; move/polyOver_suba => [p ->]; move/polyOver_suba => [q ->].
by apply/polyOver_suba; exists (p + q); rewrite rmorphD.
Qed.

Lemma opp_polyOver : forall p : {poly L}, polyOver p -> polyOver (- p).
Proof.
move => ?; move/polyOver_suba => [p ->].
by apply/polyOver_suba; exists (- p); rewrite rmorphN.
Qed.

Lemma mulp_polyOver : forall p q : {poly L},
  polyOver p -> polyOver q -> polyOver (p * q).
Proof.
move => ? ?; move/polyOver_suba => [p ->]; move/polyOver_suba => [q ->].
by apply/polyOver_suba; exists (p * q); rewrite rmorphM.
Qed.

Lemma exp_polyOver : forall (p : {poly L}) n, polyOver p -> polyOver (p ^+ n).
Proof.
move => ? n; move/polyOver_suba => [p ->].
by apply/polyOver_suba; exists (p ^+ n); rewrite rmorphX.
Qed.

Lemma scalep_polyOver : forall (c : L) (q : {poly L}),
  c \in K -> polyOver q -> polyOver (c *: q).
Proof.
move => ? ? cK; move/polyOver_suba => [q ->].
apply/polyOver_suba; exists ((Suba cK) *: q).
by rewrite -!mul_polyC rmorphM /= map_polyC.
Qed.

Lemma polyOver0 : polyOver 0.
Proof. by apply/polyOver_suba; exists 0; rewrite map_polyC. Qed.

Lemma polyOverX : polyOver 'X.
Proof.
apply/polyOverP => i.
by rewrite coefX; case: (_ == _); [apply: memv1 | apply: mem0v].
Qed.

Lemma polyOverC : forall c, c \in K -> polyOver (c%:P).
Proof.
move => c cK; apply/polyOverP => i.
by rewrite coefC; case: (_ == _) => //; apply: mem0v.
Qed.

Lemma sump_polyOver : forall (I : finType) (P : pred I) (p_ : I -> {poly L}),
  (forall i, P i -> polyOver (p_ i)) -> polyOver (\sum_(i | P i) p_ i).
Proof.
move=> I P p_ Hp; apply big_prop => //; first by apply polyOver0.
by exact: addp_polyOver.
Qed.

Lemma compose_polyOver : forall p q : {poly L},
  polyOver p -> polyOver q -> polyOver (p \Po q).
Proof.
move => p q; move/polyOverP => Hp; move/polyOverP => Hq.
apply/polyOverP => i.
rewrite /poly_comp horner_coef coef_sum memv_sum // => j _.
rewrite coef_mul memv_sum // => k _.
apply: memv_mul.
   by rewrite coef_map coefC; case: eqP=> // _; exact: mem0v.
elim: (j:nat) (i - k)%N => [|l IH] m.
 by rewrite coefC fun_if if_arg mem0v memv1 if_same.
rewrite exprS coef_mul memv_sum // => n _.
by rewrite memv_mul ?IH.
Qed.

Lemma deriv_polyOver :  forall (p : {poly L}), polyOver p -> polyOver p^`().
Proof.
move => ?; move/polyOver_suba => [p ->].
by apply/polyOver_suba; exists (p^`()); apply: deriv_map.
Qed.

End SubAlgebra.

Lemma polyOver_subset : forall (K E : {algebra L}) p, (K <= E)%VS ->
 polyOver K p -> polyOver E p.
Proof.
move => K E p; move/subsetvP => KE; move/polyOverP => Kp.
by apply/polyOverP => i; rewrite KE.
Qed.

Lemma memv_horner: forall (K E : {algebra L}) p, polyOver K p -> (K <= E)%VS ->
 forall x, x \in E -> p.[x] \in E.
Proof.
move => K E p; move/polyOverP => x HE pK Hx.
rewrite horner_coef memv_sum // => i _.
rewrite memv_mul //; last by rewrite memv_exp.
by move/subsetvP : HE; apply.
Qed.

(* A deriviation only needs to be additive and satify lebniz's law, but all the
   deriviation I will use are going to be linear, so we just define a
   derivation to be linear. *) 
Definition Derivation (K:{algebra L}) (D : 'End(L)) : bool :=
 (D @v: K <= K)%VS &&
 (all (fun v1 => all (fun v2 => D (v1 * v2) == D v1 * v2 + v1 * D v2) (vbasis K))
      (vbasis K)).

Lemma DerivationMul : forall E D, Derivation E D -> 
forall u v, u \in E -> v \in E -> D (u * v) = D u * v + u * D v.
Proof.
move => E D.
case/andP => _.
move/all_nthP => Dmult u v Hu Hv.
have Hspan : (is_span E (vbasis E)) by rewrite is_basis_span ?is_basis_vbasis.
rewrite (is_span_span Hspan Hu) (is_span_span Hspan Hv).
rewrite !linear_sum -big_split /=.
apply: eq_bigr => j _.
rewrite -!mulr_suml linear_sum /=  -big_split /=.
apply: eq_bigr => i _.
rewrite -scaler_mull linearZ /= -scaler_mulr linearZ /=.
move/all_nthP : (Dmult 0 _ (ltn_ord i)); move/(_ 0_ (ltn_ord j)); move/eqP->.
by rewrite ![D (_ *: _)]linearZ /= -!scaler_mull -!scaler_mulr !scaler_addr.
Qed.

Lemma Derivation1 : forall E D, Derivation E D -> D 1 = 0.
Proof.
move => E D HD.
rewrite (@GRing.addIr _ (D 1) (D 1) 0) // GRing.add0r.
by rewrite -{3}[1]mul1r (DerivationMul HD) ?memv1 // mulr1 mul1r.
Qed.

Lemma DerivationF : forall E D x, Derivation E D ->
 x \in F -> D x = 0.
Proof.
move => E D ? HD.
move/injvP => [x ->].
by rewrite linearZ /= (Derivation1 HD) scaler0.
Qed.

Lemma Derivation_exp : forall E D, Derivation E D -> 
 forall x, x \in E -> forall m, D (x ^+ m) = x ^+ m.-1 *+ m * D x.
Proof.
move => E D HD x Hx.
case.
 by rewrite expr0 mulr0n mul0r (Derivation1 HD).
simpl.
elim.
 by rewrite expr1 expr0 mul1r.
move => m Hm.
rewrite GRing.exprS (DerivationMul HD) //.
 rewrite Hm /=.
 rewrite [_ *+ m.+2]GRing.mulrS mulr_addl.
 rewrite {3}GRing.exprS mulrA -GRing.mulrnAr.
 congr (_ + _).
 elim: (m.+1).
  by rewrite GRing.expr0 mulr1 mul1r.
 move => a Ha.
 by rewrite mulrC.
by apply memv_exp.
Qed.

Lemma Derivation_addp : forall E D p q, Derivation E D ->
 polyOver E p -> polyOver E q ->
 map_poly D (p + q) = map_poly D p + map_poly D q.
Proof.
move => E D p q ED; move/polyOverP => Ep; move/polyOverP => Eq.
by apply/polyP => i; rewrite !(coef_add,coef_map [linear of D]) /= linearD.
Qed.

Lemma Derivation_mulp : forall E D p q, Derivation E D ->
 polyOver E p -> polyOver E q ->
 map_poly D (p * q) = map_poly D p * q + p * map_poly D q.
Proof.
move => E D p q ED; move/polyOverP => Ep; move/polyOverP => Eq.
apply/polyP => i.
rewrite coef_add (coef_map [linear of D]) /=  ?linear0 //.
rewrite !coef_mul linear_sum /= -big_split; apply: eq_bigr => j _ /=.
by rewrite !(coef_map [linear of D]) ?linear0 // (DerivationMul ED).
Qed.

Lemma DerivationPoly : forall E D p x, Derivation E D ->
 polyOver E p -> x \in E ->
 D p.[x] = (map_poly D p).[x] + (deriv p).[x] * D x.
Proof.
move => E D p x HD Hp Hx.
(* Why do I have to move first? *)
move: p Hp.
apply: poly_ind => [|p c IHp].
  by rewrite /map_poly size_polyC eqxx derivC !horner0 mul0r add0r linear0.
move/polyOverP => Hp.
have Hp0: (polyOver E p).
 apply/polyOverP => i; move: (Hp i.+1).
 by rewrite coef_add_poly coef_mulX coefC /= addr0.
have->: map_poly D (p * 'X + c%:P) = map_poly D p * 'X + (D c)%:P.
 apply/polyP => i.
 by rewrite !(coef_add, coef_mulX, coefC, (coef_map [linear of D])) ?linear0
            //= linearD /= ![D (if _ then _ else _)]fun_if linear0.
rewrite horner_amulX linearD /= (DerivationMul HD) ?(memv_horner Hp0) 
        ?subsetv_refl //.
rewrite (IHp Hp0) deriv_amulX !horner_add !horner_mul !hornerX !hornerC.
rewrite !mulr_addl -!addrA; congr (_ + _).
by rewrite addrC [_ + D c]addrC -mulrA [_ * x]mulrC mulrA addrA.
Qed.

Section Fadjoin.

Variable (K : {algebra L}).
Variable (x : L).

Let P n := \dim (\sum_(i < n.+1) (K * (x ^+ i)%:VS))%VS < \dim K * n.+1.

Let Pholds : exists n, P n.
exists (vdim L).
set d:=(vdim _).
rewrite /P.
apply: (@leq_trans (d.+1)).
 by rewrite ltnS {6}/d -dimvf dimvS // subsetvf.
rewrite leq_pmull // lt0n dimv_eq0 -subsetv0.
apply: contra (nonzero1r L) => HK.
move: (subsetv_trans (subset1v K) HK).
move/subsetvP.
move/(_ 1).
move/(_ (memv_inj _)).
by rewrite memv0.
Qed.

Definition elementDegree := ex_minn Pholds.

Lemma elementDegreegt0 : (0%N < elementDegree).
Proof.
rewrite /elementDegree.
case: ex_minnP.
case.
 by rewrite /P muln1 big_ord1 expr0 prodv1 ltnn.
by move => m _ _; apply: ltn0Sn.
Qed.

Definition FadjoinVS := (\sum_(i < elementDegree) (K * (x ^+ i)%:VS))%VS.

Lemma dim_Fadjoin_subproof : forall n,
 \sum_(i < n) \dim (K * (x ^+ i)%:VS)%VS <= (\dim K * n)%N.
Proof.
elim; first by rewrite big_ord0.
move => n IH.
rewrite big_ord_recr /= mulnSr leq_add ?IH // (leq_trans (dim_prodv _ _)) //
        dim_injv.
by case: (x ^+ n != 0); rewrite ?muln0 ?muln1.
Qed.

Lemma dim_Fadjoin : \dim FadjoinVS = (\dim K * elementDegree)%N.
Proof.
move: elementDegreegt0.
rewrite /FadjoinVS /elementDegree.
case: ex_minnP.
move => m _ Hm m0.
apply: anti_leq.
rewrite (leq_trans (dimv_leq_sum _ _)) ?dim_Fadjoin_subproof //=.
case: m Hm m0 => // m Hm _.
rewrite leqNgt.
move/negP: (ltnSn m); move/negP.
rewrite ltnNge.
apply: contra.
apply: Hm.
Qed.

Lemma direct_Fadjoin : directv FadjoinVS.
Proof.
apply/directvP => /=.
by apply: anti_leq; rewrite dimv_leq_sum dim_Fadjoin dim_Fadjoin_subproof.
Qed.

Lemma capv_KxED_subproof :
 (x == 0) = ((K * (x ^+ elementDegree)%:VS :&: FadjoinVS)%VS == 0%:VS).
Proof.
apply/eqP/eqP.
 move ->.
 move/prednK: elementDegreegt0 <-.
 by rewrite exprS mul0r prodv0 cap0v.
move/eqP => H; apply/eqP; move: H.
apply: contraLR => nzx.
rewrite -subsetv0 -dimv_sum_leqif neq_ltn.
apply/orP; left.
rewrite dim_Fadjoin.
rewrite dim_prodvf ?expf_neq0 // -{1}[\dim K]muln1 -muln_addr add1n.
rewrite /FadjoinVS /elementDegree.
case: ex_minnP => m Hm _.
apply: (leq_trans _ Hm).
by rewrite big_ord_recr /= addvC.
Qed.

Lemma elemDeg1_subproof : (x \in K) -> elementDegree = 1%N.
Proof.
move: elementDegreegt0.
rewrite /elementDegree.
case: ex_minnP.
case => // m _ Hm _ xK.
apply/eqP.
rewrite eqSS -leqn0 -ltnS Hm // /P !big_ord_recl big_ord0 expr1 expr0 addv0 
        prodv1.
apply (@leq_trans (\dim K).+1).
 by rewrite ltnS dimvS // addv_sub subsetv_refl (subsetv_trans _ (asubsetv K))
            // prodv_monor.
by rewrite -addn1 mulnC -[(2 * _)%N]/(\dim K + (\dim K + 0))%N
           leq_add2l addn0 -(dimv1 L) dimvS // subset1v.
Qed.

(* Give k*x^i return the k.  Used as a tool.  It would nicer to hide this definition
   and it's assocated lemmas. *)
Definition MinPoly_coef i v := 
  \sum_j coord (map (fun y => (y * x ^+ i)) (vbasis K)) v j *: (vbasis K)`_j.

Lemma MinPoly_coefK : forall i v, MinPoly_coef i v \in K.
Proof.
move => i v.
rewrite /MinPoly_coef /= memv_sum => // j _.
rewrite memvZl // memv_basis // mem_nth //.
move: j.
by rewrite size_map.
Qed.

Lemma memv_MinPoly_coef : forall i v, v \in (K * (x ^+ i)%:VS)%VS ->
 v = (MinPoly_coef i v) * x ^+ i.
Proof.
move => i v.
rewrite (_ : (K * (x ^+ i)%:VS)%VS = span (map (fun y => (y * x ^+ i)) (vbasis K))).
 move/(coord_span) => Hv.
 rewrite {1}Hv {Hv} /MinPoly_coef.
 rewrite -GRing.mulr_suml.
 apply: eq_bigr => j _.
 rewrite (nth_map 0) ?scaler_mull //.
 move: j.
 by rewrite size_map.
apply: subsetv_anti.
rewrite -!span_subsetl.
apply/andP; split; apply/allP; last first.
 move => ?.
 case/mapP => k.
 move/memv_basis => Hk ->.
 by rewrite memv_prod ?memv_inj.
move => ?.
case/allpairsP=> [[x1 x2]]; case=> I1 I2 ->.
move/memv_basis: I2.
case/injvP => c -> /=.
rewrite -scaler_mulr memvZl //.
apply memv_span.
apply/mapP.
by exists x1.
Qed.

Lemma MinPoly_coef_linear : forall i a u v, 
 MinPoly_coef i (a *: u + v) = 
 a *: MinPoly_coef i u + MinPoly_coef i v.
Proof.
move => i a u v.
rewrite /MinPoly_coef.
rewrite scaler_sumr -big_split.
apply: eq_bigr => j _ /=.
rewrite !linearP /=.
move: (coord _) => f.
by rewrite !ffunE scaler_addl scalerA.
Qed.

Definition minPoly : {poly L} := 
  'X^elementDegree - \sum_(i < elementDegree)
   (MinPoly_coef i (sumv_pi (fun i : ordinal elementDegree => 
                            K * (x ^+ i)%:VS)%VS predT i (x ^+ elementDegree)))
    *: 'X^i.

Lemma size_minPoly : size minPoly = elementDegree.+1.
Proof.
rewrite /minPoly size_addl ?size_polyXn // size_opp ltnS.
apply: (leq_trans (size_sum _ _ _)).
apply/bigmax_leqP => i _.
set c := (MinPoly_coef _ _).
case E : (c == 0).
 by move/eqP: E ->; rewrite GRing.scale0r size_poly0.
by rewrite size_scaler ?E // size_polyXn.
Qed.

Lemma monic_minPoly : monic minPoly.
Proof.
rewrite /monic /lead_coef size_minPoly /= /minPoly coef_sub coef_Xn eq_refl
        -GRing.subr_eq0 GRing.addrC GRing.addrA GRing.addNr GRing.subr_eq
        GRing.add0r coef_sum.
apply/eqP.
symmetry.
apply: big1 => i _.
rewrite coef_scaler coef_Xn (_ : (_ == _) = false) ?GRing.mulr0 //.
apply: negbTE.
rewrite neq_ltn.
by apply/orP; right.
Qed.

Lemma minPolyOver : polyOver K minPoly.
Proof.
apply/polyOverP => i.
case: (eqVneq i elementDegree).
 move ->.
 move: monic_minPoly.
 rewrite /monic /lead_coef size_minPoly.
 move/eqP ->.
 apply: memv1.
rewrite /minPoly coef_sub coef_Xn coef_sum.
move/negbTE ->.
rewrite add0r memvN // memv_sum // => j _.
rewrite coef_scaler coef_Xn.
case: eqP => _; last first.
 by rewrite mulr0 mem0v.
by rewrite mulr1 MinPoly_coefK.
Qed.

Lemma memXED_Fadjoin_subproof : K = F -> 
 x ^+ elementDegree \in FadjoinVS.
Proof.
move => KF.
case (eqVneq x 0) => [->|xn0].
 move/prednK: elementDegreegt0 <-.
 by rewrite exprS mul0r mem0v.
move: elementDegreegt0.
rewrite /FadjoinVS /elementDegree.
case: ex_minnP.
case => //.
rewrite /P.
move: KF ->.
move => m.
rewrite dim_injv nonzero1r mul1n big_ord_recr /= => H.
move/(_ m).
move/contra.
rewrite -!ltnNge mul1n.
move/(_ (leqnn _)).
move/(leq_trans H).
rewrite ltnS prod1v.
set V := (\sum_(i < m.+1) _)%VS.
move => Hdim.
have: \dim (V + (x ^+ m.+1)%:VS) = \dim V.
 by apply: anti_leq; rewrite Hdim dimvS // addvSl.
move/eqP.
rewrite eq_sym dimv_leqif_sup ?addvSl //.
move => HV _.
apply: (subsetv_trans _ HV).
by rewrite addvSr.
Qed.

Definition poly_for_Fadjoin (v : L) := 
  \sum_(i < elementDegree)
   (MinPoly_coef i (sumv_pi (fun (i : 'I_elementDegree) => (K * (x ^+ i)%:VS)%VS)
                            predT i v))%:P * 'X^i.

Lemma poly_for_polyOver : forall v, polyOver K (poly_for_Fadjoin v).
Proof.
move => v.
apply/polyOverP => i.
rewrite /poly_for_Fadjoin coef_sum memv_sum // => j _.
by rewrite coef_mulXn coefC !(fun_if,if_arg) mem0v MinPoly_coefK !if_same.
Qed.

Lemma size_poly_for : forall v, size (poly_for_Fadjoin v) <= elementDegree.
Proof.
move => v.
rewrite (leq_trans (size_sum _ _ _)) //.
apply/bigmax_leqP => i _.
set c := (MinPoly_coef _ _).
case (eqVneq c 0).
 move ->.
 by rewrite mul0r size_poly0.
move => nzc.
by rewrite (size_polyC_mul _ nzc) size_polyXn.
Qed.

Lemma poly_for_eq : forall v, v \in FadjoinVS -> v = (poly_for_Fadjoin v).[x].
Proof.
move => v Hv.
rewrite /poly_for_Fadjoin horner_sum {1}(sumv_sum_pi Hv) sum_lappE.
apply: eq_bigr => i _.
by rewrite !horner_lin hornerXn -memv_MinPoly_coef // memv_sum_pi.
Qed.

Lemma poly_Fadjoin_small : forall v,
 reflect (exists p, polyOver K p /\ size p <= elementDegree /\ v = p.[x])
         (v \in FadjoinVS).
Proof.
move => v.
apply: (iffP idP) => [Hp|]; last first.
  case => p; case; move/polyOverP => pK [sizep vp].
  apply/memv_sumP.
  exists (fun i : 'I_elementDegree => p`_i * x ^+ i); split=>[i _|].
    by rewrite memv_prod ?memv_inj.
  by rewrite vp (horner_coef_wide _ sizep).
by exists (poly_for_Fadjoin v); (split; [apply: poly_for_polyOver | split]);
    [apply: size_poly_for | apply: poly_for_eq].
Qed.

Lemma poly_for_linear : forall a u v, 
 poly_for_Fadjoin (a *: u + v) = 
 (a *: 1) *: poly_for_Fadjoin u + poly_for_Fadjoin v.
Proof.
move => a u v.
rewrite /poly_for_Fadjoin scaler_sumr -big_split.
apply eq_bigr => i _ /=.
by rewrite linearP MinPoly_coef_linear rmorphD mulr_addl
           scaler_mull -mul_polyC -polyC_mul -scaler_mull mul1r.
Qed.

Lemma poly_Fadjoin_small_uniq : forall p q, polyOver K p -> polyOver K q ->
 size p <= elementDegree -> size q <= elementDegree -> p.[x] = q.[x] -> p = q.
Proof.
case (eqVneq x 0).
 move/eqP; rewrite -memv0 => x0.
 move: (subsetv_trans x0 (subset0v K)).
 move/elemDeg1_subproof => -> p q pK qK.
 by do 2 move/size1_polyC ->; rewrite !horner_lin => ->.
move => nzx p q; move/polyOverP => pK; move/polyOverP => qK szp szq.
rewrite (horner_coef_wide _ szp) (horner_coef_wide _ szq).
move/eqP; move: (direct_Fadjoin); move/directv_sum_unique => sumUniq.
rewrite sumUniq {sumUniq}; do ? move => i _; rewrite ?memv_prod ?memv_inj //.
move/forall_inP => Hpq.
apply/polyP => i.
apply: (mulIf (expf_neq0 i nzx)).
case: (leqP elementDegree i) => Hi; last first.
 by apply/eqP; apply (Hpq (Ordinal Hi)).
by rewrite (_ : p`_i = 0) ?mul0r; first rewrite (_ : q`_i = 0) ?mul0r //;
 apply/eqP; move: Hi; [move/(leq_trans szq)|move/(leq_trans szp)];
 apply: contraLR; rewrite -ltnNge; apply: leq_coef_size.
Qed.

Hypothesis HxED : x ^+ elementDegree \in FadjoinVS.

Lemma root_minPoly_subproof : root minPoly x.
Proof.
rewrite /root /minPoly !horner_lin_com horner_sum hornerXn {1}(sumv_sum_pi HxED)
        sum_lappE subr_eq0.
apply/eqP.
apply: eq_bigr => i _.
by rewrite !horner_lin_com hornerXn -memv_MinPoly_coef ?memv_sum_pi.
Qed.

Lemma minPoly_coef0_subproof : (minPoly`_0 == 0) = (x == 0).
Proof.
case (@eqP _ x 0) => Hx.
 move: Hx root_minPoly_subproof ->.
 rewrite /root horner_coef size_minPoly big_ord_recl big1
         ?expr0 ?mulr1 ?addr0 // => i _.
 by rewrite exprSr !mulr0.
move: minPoly minPolyOver root_minPoly_subproof size_minPoly => p.
move/polyOverP => pK rootp sizep.
do 2 apply/negP.
have: (lead_coef p != 0).
 by rewrite lead_coef_eq0 -size_poly_eq0 sizep.
apply: contra.
move/eqP => p0.
move/directv_sumP: direct_Fadjoin.
move/eqP: Hx rootp => Hx.
rewrite /root horner_coef sizep big_ord_recl p0 mul0r add0r
        -(can_eq (mulfVK Hx)) -GRing.mulr_suml mul0r.
move/prednK: elementDegreegt0 sizep => <- sizep sump.
have Hxi : x ^+ (elementDegree.-1) != 0.
 by rewrite expf_eq0 negb_and Hx orbT.
rewrite -(can_eq (mulfK Hxi)) mul0r -memv0.
move/(_ ord_max isT) <-.
rewrite memv_cap lead_coefE sizep.
apply/andP; split; first by rewrite memv_prod ?memv_inj //.
move: sump.
(* why is this line so slow? *)
rewrite (bigID (fun j => j == ord_max)).
rewrite big_pred1_eq eq_sym -subr_eq add0r eq_sym exprSr mulrA  (mulfK Hx).
rewrite /ord_max.
move/eqP ->.
apply: memvNr.
apply: sumv_mem => i _.
by rewrite exprSr mulrA (mulfK Hx) memv_prod ?memv_inj.
Qed.

Lemma subsetFadjoinE_subproof: forall E : {algebra L},
   (K <= E)%VS && (x \in E) = (FadjoinVS <= E)%VS.
Proof.
move => E.
apply/idP/idP.
 case/andP => KE xE.
 apply/subsetv_sumP => i _.
 apply: (subsetv_trans _ (asubsetv _)).
 apply: (subsetv_trans (prodv_monol _ _) (prodv_monor _ _)) => //.
 by apply: memv_exp.
move => HFxE.
apply/andP; split; apply: (subsetv_trans _ HFxE).
 rewrite /FadjoinVS.
 move/prednK: elementDegreegt0 <-.
 by rewrite big_ord_recl expr0 prodv1 addvSl.
move: HxED.
rewrite /FadjoinVS.
move/prednK: elementDegreegt0 <-.
case: elementDegree.-1 => [|d].
 by rewrite expr1.
move => _.
rewrite !big_ord_recl.
apply: (subsetv_trans _ (addvSr _ _)).
apply: (subsetv_trans _ (addvSl _ _)).
by rewrite -{1}[x%:VS]prod1v prodv_monol // subset1v.
Qed.

End Fadjoin.

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
have xED : x ^+ elementDegree F x \in FadjoinVS F x.
 by apply: memXED_Fadjoin_subproof.
have: (FadjoinVS F x <= K)%VS.
 by rewrite -subsetFadjoinE_subproof // xK subset1v. 
move/subsetvP; apply.
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
        -mulr_suml sumv_mem // => i _.
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

End MoreSubalgebra.

Section MoreFadjoin.

Variable (K : {algebra L}).
Variable (x : L).

Lemma XED_subproof : x ^+ (elementDegree K x) \in (FadjoinVS K x).
case: (eqVneq x 0).
 move ->.
 move/prednK: (elementDegreegt0 K 0) <-.
 by rewrite exprS mul0r mem0v.
rewrite (capv_KxED_subproof K).
rewrite -vpick0.
set W := (_ :&: _)%VS.
move: (memv_pick W).
rewrite memv_cap.
case/andP.
move/memv_MinPoly_coef ->.
set k := (MinPoly_coef _ _ _ _) => Hk.
have: (k \in K) by apply: MinPoly_coefK.
rewrite memv_inv mulf_eq0 negb_or => Hkinv.
case/andP => nzk _.
rewrite -[x ^+ _](mulKf nzk).
apply/memv_sumP.
case/memv_sumP: Hk => v_ [Hv_1 Hv_2].
exists (fun i => k^-1 * v_ i); split; last by rewrite Hv_2 mulr_sumr.
move => i _.
move/(_ i isT): Hv_1.
move/memv_MinPoly_coef ->.
by rewrite mulrA memv_prod ?memv_inj // memv_mul // MinPoly_coefK.
Qed.

Lemma root_minPoly : root (minPoly K x) x. 
Proof. by rewrite root_minPoly_subproof // XED_subproof. Qed.

Lemma minPolyxx : (minPoly K x).[x] = 0.
Proof. by move: root_minPoly; rewrite /root; move/eqP ->. Qed.

Lemma subsetFadjoinE: forall E : {algebra L},
   (K <= E)%VS && (x \in E) = (FadjoinVS K x <= E)%VS.
Proof. by move => E; rewrite subsetFadjoinE_subproof // XED_subproof. Qed.

Lemma poly_Fadjoin : forall v,
 reflect (exists p, polyOver K p /\ v = p.[x])
         (v \in (FadjoinVS K x)).
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
 by rewrite coef_add coef_poly -mulrA coef_Cmul coef_mulXn !(fun_if, if_arg)
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

Lemma Fadjoin_is_aspace : let Kx := FadjoinVS K x in
 (has_aunit Kx  && (Kx * Kx <= Kx)%VS).
Proof.
apply/andP; split.
 apply: has_aunit1.
 apply/poly_Fadjoin.
 exists 1;split; last by rewrite horner_lin.
 apply/polyOverP => i.
 rewrite coefC.
 by case: ifP; rewrite ?mem0v ?memv1.
apply/prodvP => ? ?.
case/poly_Fadjoin => p1 [Hp1 ->].
case/poly_Fadjoin => p2 [Hp2 ->].
apply/poly_Fadjoin.
exists (p1 * p2); rewrite horner_mul; split => //.
by apply: mulp_polyOver.
Qed.

Canonical Structure Fadjoin : {algebra L} := ASpace Fadjoin_is_aspace.

Lemma memx_Fadjoin : x \in Fadjoin.
Proof.
by move: (subsetv_refl Fadjoin); rewrite -subsetFadjoinE; case/andP.
Qed.

Lemma subsetKFadjoin : (K <= Fadjoin)%VS.
Proof.
by move: (subsetv_refl Fadjoin); rewrite -subsetFadjoinE; case/andP.
Qed.

Lemma mempx_Fadjoin : forall p, polyOver K p -> p.[x] \in Fadjoin.
Proof. move => p pK; apply/poly_Fadjoin; by exists p. Qed.

Lemma poly_for_K : forall v, v \in K -> poly_for_Fadjoin K x v = v%:P.
Proof.
move => v vK.
apply (@poly_Fadjoin_small_uniq K x).
    by apply: poly_for_polyOver.
   by apply: polyOverC.
  by apply: size_poly_for.
 by rewrite size_polyC (leq_trans (leq_b1 _)) // elementDegreegt0.
rewrite hornerC -poly_for_eq //.
move/subsetvP: subsetKFadjoin.
by apply.
Qed.

Lemma poly_for_modp : forall p, polyOver K p ->
 poly_for_Fadjoin K x p.[x] = p %% minPoly K x.
Proof.
move => p Pk.
apply (@poly_Fadjoin_small_uniq K x).
    by apply: poly_for_polyOver.
   by rewrite modp_polyOver // minPolyOver.
  by apply: size_poly_for.
 by rewrite -ltnS -size_minPoly modp_spec // -size_poly_eq0 size_minPoly.
by rewrite -poly_for_eq ?mempx_Fadjoin // 
           {1}(divp_mon_spec p (monic_minPoly K x)) horner_add horner_mul
           minPolyxx mulr0 add0r.
Qed.

Lemma elemDeg1 : (x \in K) = (elementDegree K x == 1%N).
Proof.
apply/idP/eqP.
 apply: elemDeg1_subproof.
move => ed1.
have: (K == Fadjoin).
(* can I somehow avoid the a2vs? *)
 change (a2vs K == a2vs Fadjoin).
 by rewrite -(dimv_leqif_eq subsetKFadjoin) dim_Fadjoin ed1 muln1.
move/eqP ->.
by apply: memx_Fadjoin.
Qed.

Lemma FadjoinxK : (x \in K) = (Fadjoin == K).
Proof.
rewrite elemDeg1.
rewrite -[Fadjoin == K]/(Fadjoin == K :> {vspace L}).
apply/eqP/eqP.
 move => ed1.
 apply: subsetv_anti.
 by rewrite -dimv_leqif_sup subsetKFadjoin // dim_Fadjoin ed1 muln1 andbT.
move => Fadjoin_eq_K.
move/eqP: (dim_Fadjoin K x).
rewrite Fadjoin_eq_K -{1}[\dim K]muln1 eqn_mul2l dimv_eq0.
case/orP; last by move/eqP ->.
move/eqP => K0.
case: (negP (@nonzero1r L)).
by rewrite -memv0 -K0 memv1.
Qed.

Lemma size_elementDegree : forall p, polyOver K p -> 
 size p <= elementDegree K x -> root p x = (p == 0).
Proof.
move => p Kp szp.
rewrite /root.
apply/eqP/eqP => Hp; last by rewrite Hp horner0.
by apply: (@poly_Fadjoin_small_uniq K x); 
    rewrite ?polyOver0 ?size_poly0 ?horner0.
Qed. 

Lemma minPoly_irr : forall p, polyOver K p ->
 dvdp p (minPoly K x) -> (p %= minPoly K x) || (p %= 1).
Proof.
rewrite /dvdp.
move => p Kp.
move/eqP => pMin.
set (q := lead_coef p ^- scalp (minPoly K x) p *: ((minPoly K x) %/ p)).
have Kq : (polyOver K q).
  rewrite scalep_polyOver -?memv_inv ? scalp_polyOver ?divp_polyOver //.
    by rewrite memv_exp // lead_coefE; move/polyOverP: Kp; apply.
  by rewrite minPolyOver.
move: root_minPoly (size_minPoly K x).
have -> : (minPoly K x = q * p).
 have nzc := (scalp_Ineq0 (minPoly K x) p).
 rewrite -scaler_mull.
 apply: (canRL (scalerK nzc)).
 by rewrite (divCp_spec (minPoly K x) p) pMin addr0.
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
rewrite -size1_dvdp1 eqn_leq.
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
case/negP: (root1n x).
by rewrite -(eqp_root gcd_eq1) root_gcd rootp root_minPoly.
Qed.

Definition seperableElement := seperablePolynomial (minPoly K x).

Lemma seperableElementP :  
  reflect 
  (exists f, polyOver K f /\ root f x /\ seperablePolynomial f) 
   seperableElement.
Proof.
apply: (iffP idP).
 move => ?; exists (minPoly K x); do ! (split => //).
  by apply: minPolyOver.
 by apply root_minPoly.
move => [f [fK [rf sf]]].
move/dvdpPc: (minPoly_dvdp fK rf) => [c [g [Hc Hg]]].
move: (canRL (GRing.scalerK Hc) Hg) sf ->.
rewrite (GRing.scaler_mull) seperable_mul.
by case/and3P.
Qed.

Lemma seperable_nzdmp : seperableElement = (deriv (minPoly K x) != 0).
Proof.
rewrite /seperableElement /seperablePolynomial.
apply/idP/idP.
 apply: contraL.
 move/eqP ->.
 by rewrite coprimep0 -size1_dvdp1 size_minPoly eqSS -lt0n elementDegreegt0.
move => Hderiv.
have gcdl := (dvdp_gcdl (minPoly K x) (deriv (minPoly K x))).
have gcdK : polyOver K (gcdp (minPoly K x) (minPoly K x)^`()).
 by rewrite gcdp_polyOver ?deriv_polyOver // minPolyOver.
rewrite -gcdp_eqp1 eqp1_dvd1.
case/orP: (minPoly_irr gcdK gcdl); last first.
 rewrite /eqp.
 by case/andP.
rewrite /eqp dvdp_gcd dvdpp /=.
case/andP => _.
move/(size_dvdp Hderiv) => Hsz.
move: (leq_trans Hsz (size_poly _ _)).
by rewrite size_minPoly ltnn.
Qed.

Lemma seperableNrootdmp : 
  seperableElement != (root (deriv (minPoly K x)) x).
Proof.
rewrite seperable_nzdmp size_elementDegree.
  by case: (_ == 0).
 by rewrite deriv_polyOver // minPolyOver.
by rewrite (leq_trans (size_Poly _)) // size_mkseq size_minPoly leqnn.
Qed.

Lemma DerivationSeperable : forall D, Derivation Fadjoin D -> 
 seperableElement ->
 D x = - (map_poly D (minPoly K x)).[x] / ((minPoly K x)^`()).[x].
Proof.
move => D Dderiv.
move: seperableNrootdmp.
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
Hypothesis HD: Derivation K D.

Let Dx := - (map_poly D (minPoly K x)).[x] / ((minPoly K x)^`()).[x].

Let DerivationExtend_body (D:'End(L)) (y:L) : L :=
 let p := (poly_for_Fadjoin K x y) in
 (map_poly D p).[x] + (p^`()).[x] * Dx.

Let DerivationExtend_body_linear : linear (DerivationExtend_body D).
Proof.
move => a u v.
rewrite /DerivationExtend_body.
move: Dx => C.
rewrite poly_for_linear -mul_polyC.
rewrite derivD.
rewrite derivM derivC mul0r add0r.
rewrite !horner_lin_com.
rewrite -scaler_mull mul1r.
move : (poly_for_Fadjoin _ _ _) => pu.
move : (poly_for_Fadjoin _ _ _) => pv.
rewrite (_ : map_poly D ((a *: 1)%:P * pu + pv)
           = (a *: 1)%:P * map_poly D pu + map_poly D pv); last first.
  apply/polyP => i; rewrite !(coef_map [linear of D]) ?linear0 // !coef_add.
  by rewrite  !coef_Cmul  !(coef_map [linear of D]) ?linear0 //= -!scaler_mull
              !mul1r linearP.
by rewrite !horner_lin_com -scaler_mull mul1r mulr_addl scaler_addr 
           -scaler_mull -addrA [(_.[x] + _)]addrA [_ + (a *: (_ * _))]addrC /=
           !addrA.
Qed.

Definition DerivationExtend : 'End(L) :=
 lapp_of_fun (DerivationExtend_body D).

Lemma DerivationExtended : forall y, y \in K ->  DerivationExtend y = D y.
Proof.
move => y yK.
rewrite lapp_of_funK; last by apply: DerivationExtend_body_linear.
rewrite /DerivationExtend_body.
rewrite poly_for_K // derivC horner0 mul0r addr0.
rewrite -[D y](hornerC _ x) /horner_morph.
congr (_.[x]).
apply: f_equal.
apply/polyP => i.
by rewrite (coef_map [linear of D]) ?linear0 //= !coefC [D _]fun_if linear0.
Qed.

Lemma DerivationExtend_Poly : forall (p:{poly L}),
 polyOver K p -> seperableElement ->
 DerivationExtend (p.[x]) = (map_poly D p).[x] + p^`().[x] * Dx.
Proof.
move => p Kp sep.
move: seperableNrootdmp.
rewrite negb_eqb addbC /root sep addbT {sep} => sep.
rewrite lapp_of_funK; last by apply: DerivationExtend_body_linear.
by rewrite {-1}(divp_mon_spec p (monic_minPoly K x)) /DerivationExtend_body
           poly_for_modp // /horner_morph (Derivation_addp HD) 
           ?(Derivation_mulp HD)
           ?(mulp_polyOver, divp_polyOver, modp_polyOver, minPolyOver) // 
           derivD derivM !horner_add !horner_mul minPolyxx !mulr0 !add0r
           mulr_addl addrA [_ + (_ * _ * _)]addrC {2}/Dx /horner_morph -mulrA
           [_ * (- _ * _)]mulrC (mulfVK sep) mulrN addKr.
Qed.


Lemma DerivationExtendDerivation :
 seperableElement -> Derivation Fadjoin DerivationExtend.
Proof.
move => sep.
have polyOverMapD : forall p, polyOver K p -> polyOver K (map_poly D p).
 move => p pK.
 apply/polyOverP => i.
 case/andP: HD; move/subsetvP => HD1 _.
 rewrite (coef_map [linear of D]) ?linear0 // HD1 // memv_img //.
 by move: i; apply/polyOverP.
apply/andP;split.
 apply/subsetvP => ?.
 move/memv_imgP => [v [Hv ->]].
 rewrite lapp_of_funK; last by apply: DerivationExtend_body_linear.
 rewrite /DerivationExtend_body /horner_morph.
 rewrite memvD //.
  apply/poly_Fadjoin.
  exists (map_poly D (poly_for_Fadjoin K x v)); split => //.
  by rewrite polyOverMapD // poly_for_polyOver.
 rewrite memv_mul //.
  apply/poly_Fadjoin.
  exists ((poly_for_Fadjoin K x v)^`()); split => //.
  by rewrite deriv_polyOver // poly_for_polyOver.
 rewrite memv_mul //.
  rewrite memvN.
  apply/poly_Fadjoin.
  exists (map_poly D (minPoly K x)); split => //.
  by rewrite polyOverMapD // minPolyOver.
 rewrite -memv_inv.
 apply/poly_Fadjoin.
 exists ((minPoly K x)^`()); split => //.
 by rewrite deriv_polyOver // minPolyOver.
apply/allP => u; move/memv_basis => Hu.
apply/allP => v; move/memv_basis => Hv.
apply/eqP.
rewrite (poly_for_eq Hu) (poly_for_eq Hv) -horner_mul !{1}DerivationExtend_Poly
        ?mulp_polyOver ?poly_for_polyOver // /horner_morph (Derivation_mulp HD)
        ?poly_for_polyOver // derivM !horner_add !horner_mul !mulr_addl 
        !mulr_addr -!addrA; congr (_ + _).
move:Dx => Dx0.
rewrite -!mulrA [Dx0 * _]mulrC !addrA; congr (_ + _).
by rewrite addrC.
Qed.

End DerivationExtend.

(* Reference: 
http://www.math.uconn.edu/~kconrad/blurbs/galoistheory/separable2.pdf *)
Lemma seperableDerivationP :
  reflect (forall D, Derivation Fadjoin D ->
                     (K <= lker D)%VS -> (Fadjoin <= lker D)%VS)
          seperableElement.
Proof.
apply introP.
 move => sep D DD.
 move/subsetvP => K0.
 apply/subsetvP => ?.
 move/poly_Fadjoin => [p [Hp ->]].
 have HD0 : forall q, polyOver K q -> map_poly D q = 0.
  move => q.
  move/polyOverP => qK.
  apply/polyP => i.
  apply/eqP.
  by rewrite (coef_map [linear of D]) ?linear0 //= coef0 -memv_ker K0.
 by rewrite memv_ker (DerivationPoly DD) ?memx_Fadjoin 
         ?(polyOver_subset subsetKFadjoin Hp) // (DerivationSeperable DD sep)
         /horner_morph !HD0 ?minPolyOver // horner0 oppr0 mul0r mulr0 addr0.
move => nsep.
move: seperableNrootdmp (nsep).
rewrite negb_eqb.
move/addbP ->.
rewrite /root; move/eqP => Hroot.
pose D_body y := ((poly_for_Fadjoin K x y)^`()).[x].
have Dlin : linear D_body.
 move => a u v.
 by rewrite /D_body poly_for_linear -mul_polyC derivD derivM derivC mul0r
            add0r horner_add horner_mul hornerC -scaler_mull mul1r.
pose D := lapp_of_fun D_body.
have DF : (K <= lker D)%VS.
 apply/subsetvP => v vK.
 by rewrite memv_ker lapp_of_funK // /D //= /D_body poly_for_K // derivC 
            horner0.
have DDeriv : Derivation Fadjoin D.
 apply/andP; split.
  apply/subsetvP => ?.
  move/memv_imgP => [v [Hv1 ->]].
  by rewrite lapp_of_funK // /D //= /D_body mempx_Fadjoin // deriv_polyOver //
             poly_for_polyOver.
 apply/allP => u; move/memv_basis => Hu.
 apply/allP => v; move/memv_basis => Hv.
 by rewrite !lapp_of_funK // /D //= /D_body {-2}(poly_for_eq Hu)
            {-3}(poly_for_eq Hv) -!horner_mul -horner_add -derivM 
            poly_for_modp ?mulp_polyOver ?poly_for_polyOver // 
            {2}(divp_mon_spec (_ * _) (monic_minPoly K x)) derivD derivM
            !horner_add !horner_mul Hroot minPolyxx !mulr0 !add0r.
have Dx : D x = 1.
 rewrite !lapp_of_funK // /D //= /D_body.
 rewrite (_ : (poly_for_Fadjoin K x x) = 'X) ?derivX ?hornerC //.
 apply: (@poly_Fadjoin_small_uniq K x).
     apply: poly_for_polyOver.
    apply: polyOverX.
   apply: size_poly_for.
  rewrite size_polyX ltn_neqAle (elementDegreegt0 K x) andbT eq_sym.
  apply: contra nsep.
  move/eqP => eD.
  rewrite seperable_nzdmp (_ : (minPoly K x)^`() = 1%:P)  ?nonzero1r //.
  apply/polyP => i.
  rewrite coef_deriv coefC.
  case: i => [|i].
   move: (monic_minPoly K x).
   rewrite /monic lead_coefE size_minPoly eD.
   move/eqP ->.
   by rewrite eq_refl.
  rewrite (_ : (minPoly K x)`_i.+2 = 0) ?mul0rn //.
  apply/eqP.
  apply (contraR (@leq_coef_size _ _ _)).
  by rewrite -ltnNge size_minPoly eD.
 by rewrite hornerX -(poly_for_eq memx_Fadjoin).
move/(_ _ DDeriv DF).
apply/negP.
move/eqP: Dx.
apply: contraL.
move/subsetvP.
move/(_ _ memx_Fadjoin).
rewrite memv_ker.
move/eqP ->.
rewrite eq_sym.
by apply: nonzero1r.
Qed.

End MoreFadjoin.

Lemma subsetSeperable : forall (K E : {algebra L}) x, (K <= E)%VS -> 
 seperableElement K x -> seperableElement E x.
Proof.
move => K E x KE.
move/seperableElementP => [f [fK [rootf sepf]]].
apply/seperableElementP.
exists f; split => //.
by apply: (polyOver_subset KE).
Qed.

Lemma allSeperableElement : forall K x,
  reflect (forall y, y \in Fadjoin K x -> seperableElement K y)
          (seperableElement K x).
Proof.
move => K x.
apply (iffP idP); last by apply; apply memx_Fadjoin.
move => sep ?.
move/poly_Fadjoin => [q [Hq ->]].
apply/seperableDerivationP => D DD.
move/subsetvP => KD0.
apply/subsetvP => ?.
move/poly_Fadjoin => [p [Hp ->]].
rewrite memv_ker -(DerivationExtended x D (mempx_Fadjoin _ Hp)).
have sepFyx : (seperableElement (Fadjoin K (q.[x])) x).
 by apply: (subsetSeperable (subsetKFadjoin _ _)).
have KyxEqKx : (Fadjoin (Fadjoin K (q.[x])) x = Fadjoin K x).
 apply/eqP.
 change (Fadjoin (Fadjoin K q.[x]) x == Fadjoin K x :> {vspace L}).
 apply/eqP.
 apply: subsetv_anti.
 by rewrite -!{1}subsetFadjoinE mempx_Fadjoin //
         (subsetv_trans _ (subsetKFadjoin (Fadjoin K _) _)) subsetKFadjoin 
         // !{1}memx_Fadjoin.
rewrite -horner_poly_comp.
move: (DerivationExtendDerivation DD sepFyx).
rewrite KyxEqKx => DED.
rewrite (DerivationPoly DED); last first.
  apply: memx_Fadjoin.
 apply: (polyOver_subset (subsetKFadjoin _ _)).
 by apply: compose_polyOver.
have hmD : forall t, polyOver K t ->
           (map_poly (DerivationExtend (Fadjoin K q.[x]) x D) t).[x] = 0.
 move => t.
 move/polyOverP => Ht.
 rewrite /horner_morph (_ : map_poly _ _ = 0); first by rewrite horner0.
 apply/polyP => i.
 rewrite coef0 (coef_map [linear of (DerivationExtend _ _ _)]) 
         ?linear0 //= DerivationExtended.
  apply/eqP.
  by rewrite -memv_ker KD0.
 apply: (subsetv_trans _ (subsetKFadjoin _ _)).
 by apply: Ht.
by rewrite (DerivationSeperable DED) // !hmD ?compose_polyOver ?minPolyOver //
           oppr0 mul0r mulr0 addr0.
Qed.

Section PrimitiveElementTheorem.

Variable K : {algebra L}.
Variable x y : L.
Hypothesis sep : seperableElement K y.

Let n := (elementDegree K x).
Let m := (elementDegree K y).-1.

Let f := minPoly K x.
Let g := minPoly K y.

Let f0 := f \Po ('X + x%:P).
Let g0 := (g \Po ('X + y%:P)) %/ ('X).

Lemma gxg0_subproof : g0 * 'X = g \Po ('X + y%:P).
Proof.
rewrite /g.
have: (root (g \Po ('X + y%:P)) 0).
 by rewrite /root horner_poly_comp ![_.[0]]horner_lin add0r minPolyxx.
rewrite root_factor_theorem /dvdp subr0.
by move/eqP => mod0; rewrite -[_ * _]addr0 -mod0 -divp_mon_spec // monicX.
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
rewrite /poly_comp horner_coef.
have -> : size (map_poly polyC p) = size p.
 by rewrite map_polyE (PolyK (c:=0%:P)) ?size_map // last_map polyC_eq0
            -nth_last -lead_coefE lead_coef_eq0.
rewrite (polySpred nzp) big_ord_recr /= coef_map mul_polyC.
have H : size (p`_(size p).-1 *: ('X + z%:P) ^+ (size p).-1) = (size p).-1.+1.
  rewrite size_scaler -?lead_coefE ?lead_coef_eq0 //.
  rewrite polySpred; first by rewrite size_exp_id Sa mul1n.
  by rewrite expf_neq0 // -size_poly_eq0 Sa.
rewrite addrC size_addl // H ltnS (leq_trans (size_sum _ _ _)) //.
apply/bigmax_leqP => i _.
rewrite coef_map poly_mulC.
have [->|nzpi] := (eqVneq p`_i 0); first by rewrite mulr0 size_poly0.
by rewrite mulrC mul_polyC size_scaler // (leq_trans (size_exp _ _)) // Sa mul1n.
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
move: (seperableNrootdmp K y).
rewrite negb_eqb sep /root -/g.
apply: contra.
have <- : g0.[0] = g0`_0.
 rewrite -[g0`_0]addr0.
 rewrite horner_coef szg0_subproof /m -(prednK (elementDegreegt0 _ _)) 
         big_ord_recl expr0 mulr1.
 congr (_ + _).
 apply: big1 => i _.
 by rewrite exprSr !mulr0.
have: (root (g \Po ('X + y%:P)) 0).
 by rewrite /root horner_poly_comp ![_.[0]]horner_lin add0r minPolyxx.
rewrite -/(root g0 0) !root_factor_theorem.
rewrite -!polyC_opp !oppr0 !addr0 /g0 /dvdp => root1 root2.
suff: ('X - y%:P) ^+ 2 %| g.
 case/dvdMpP => [|r ->]; first by rewrite monic_exp // monic_factor.
 by rewrite exprS expr1 !derivM mulr_addr !horner_add !horner_mul factor0
            !(mul0r, mulr0) !addr0.
have: 'X ^+ 2 %| (g \Po ('X + y%:P)).
 by rewrite -gxg0_subproof dvdp_mul ?dvdpp.
move/dvdMpP => [|r Hr]; first by apply: monicXn.
apply/dvdMpP; first by rewrite monic_exp // monic_factor.
exists (r \Po ('X - y%:P)).
rewrite -[g]poly_compX -{1}(poly_comp_translateK y) -poly_compA Hr.
by rewrite !poly_comp_mull !poly_comXp.
Qed.

Lemma leq_size_prodM_subproof : forall s:'S_(n + m),
 (size (\prod_i M i (s i))) <= (n * m).+1.
Proof.
move => s.
rewrite big_split_ord /=.
have move_predn : forall a b, (a + b).-1 <= a.-1 + b.
 case => [|a] b //.
 apply: leq_pred.
rewrite (leq_trans (size_mul _ _)) // (@leq_trans (1 + (n * m).+1).-1) //=
        (leq_trans (move_predn _ _)) // -[_.+1]add0n leq_add //.
  rewrite -subn1; apply: (@leq_sub2r 1 _ 1).
  pose p := fun i => M (lshift m i) (s (lshift m i)).
  rewrite -[\prod_(i < n) _]/(\prod_(i < n) p i).
  have : forall i, size (p i) <= 1.
    move => i.
    by rewrite /p col_mxEu /Mg mxE !(fun_if, if_arg) size_polyC size_poly0
              leq_b1 if_same.
  elim: n p => [|n0 IH] p.
    rewrite big_ord0 size_polyC.
    by case: (1 != 0).
  rewrite big_ord_recl => sz.
  rewrite (leq_trans (size_mul _ _)) // (leq_trans (move_predn _ _)) //
             -[1%N]/(0 + 1)%N leq_add ?IH //.
  by rewrite -subn1; apply: (@leq_sub2r 1 _ 1).
pose p := fun i => M (rshift n i) (s (rshift n i)).
rewrite -[\prod_(i < m) _]/(\prod_(i < m) p i).
have : forall i, (size (p i)).-1 <= n.
 move => i.
 rewrite /p col_mxEd /Mf mxE.
 case: ifP => [_|_]; last by rewrite size_poly0.
 set j := (_ - _)%N.
 have [big|small] := (leqP (size f0) j).
  by rewrite (nth_default _ big) scale0r size_poly0.
 have [->|f0neq0] := (eqVneq f0`_j 0).
  by rewrite scale0r size_poly0.
 by rewrite size_scaler // size_polyXn -ltnS -szf0_subproof.
elim: m p => [|m0 IH] p.
 rewrite big_ord0 size_polyC.
 by case: (1 != 0).
rewrite big_ord_recl => sz.
by rewrite (leq_trans (size_mul _ _)) // (leq_trans (move_predn _ _)) //
             mulnS -addnS leq_add ?IH //.
Qed.

(* Now that we know 0 < n, this proof should be simplified *)
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
  by rewrite col_mxEd mxE perm1 leq_addl addnK lead_coefE szf0_subproof -mul_polyC.
 set a := (\prod_(i < n) _).
 have -> : a = (g0`_0 ^+ n)%:P.
  rewrite rmorphX -[n]card_ord -prodr_const.
  apply: eq_bigr => i _.
  by rewrite perm1 col_mxEu mxE leqnn subnn.
 by rewrite mul_polyC !size_scaler ?expf_neq0 ?g0nz_subproof // ?lead_coef_eq0
            -?size_poly_eq0 ?szf0_subproof // size_polyXn.
move => sz.
have Misi : forall i, M i (s i) != 0.
 move => i.
 apply/negP.
 move/eqP => eq0.
 suff: ((n * m).+1 == 0)%N => //.
 by rewrite -sz size_poly_eq0 (bigD1 i) //= eq0 mul0r.
have szg : forall i : 'I_(n + m), i < n -> size (M i (s i)) = 1%N.
 move => i Hi.
 suff: (size (M i (s i)) <= 1).
  rewrite leq_eqVlt ltnS leqn0; case/orP => [|]; first by move/eqP.
  rewrite size_poly_eq0.
  by move/negbTE: (Misi i) ->.
 rewrite mxE.
 case: (splitP i) Hi => // j Hij _.
 rewrite mxE.
 case: ifP => _; by rewrite ?size_poly0 // size_polyC leq_b1.
have sz0 : (\sum_i (size (M i (s i))).-1)%N = (n * m)%N.
 apply: succn_inj.
 rewrite -sz.
 pose M0 := (fun i => M i (s i)).
 rewrite -[(\sum_i _)%N]/(\sum_i (size (M0 i)).-1)%N
         -[\prod_i _]/(\prod_i (M0 i)).
 elim: (n + m)%N M0 (Misi:(forall i, M0 i != 0)) => [|z IH] p_ Hp_.
  by rewrite !big_ord0 size_poly1.
 by rewrite !big_ord_recr /= size_mul_id // -?size_poly_eq0 -IH //= 
            -{2}[size (p_ ord_max)]prednK // lt0n size_poly_eq0.
have Hin : forall i : 'I_(n + m), ~~(i < n) -> i = s i :> nat.
 move => i Hi.
 apply/eqP.
 move/eqP: sz0.
 apply: contraLR => Hisi.
 rewrite (bigD1 i) //=.
 rewrite big_split_ord /=.
 rewrite big1; last first.
  move => j _.
  by rewrite szg /=.
 rewrite add0n.
 case: (eqVneq m 0%N) => [m0|].
  move: (ltn_ord i).
  rewrite {2}m0 addn0.
  by move/negbTE: Hi ->.
 rewrite -lt0n.
 move/prednK => Hm.
 rewrite -{15}Hm mulnS neq_ltn -addSn.
 apply/orP;left.
 apply: leq_add.
  move: Hi Hisi (Misi i).
  rewrite mxE.
  case: splitP => // k -> _ Hk.
  rewrite mxE.
  case: ifP => //; last by rewrite eq_refl.
  case: (eqVneq (f0`_(s i - k)) 0) => [->|nz].
   by rewrite scale0r eq_refl.
  move => ksi _.
  rewrite size_scaler // size_polyXn /=.
  move: Hk.
  rewrite -{1}(subnK ksi) eqn_addr neq_ltn.
  case/orP => //.
  move: (leq_coef_size nz).
  by rewrite szf0_subproof ltnS ltnNge => ->.
 rewrite -big_filter.
 set sq := (filter _ _).
 suff: size sq = m.-1.
  move <-.
  elim: sq => [|c sq IH].
   by rewrite muln0 big_nil.
  rewrite big_cons /= mulnS leq_add // -ltnS.
  move: (Misi (rshift n c)).
  rewrite -size_poly_eq0 -lt0n.
  move/prednK ->.
  rewrite /M col_mxEd mxE.
  case: ifP; last by rewrite size_poly0.
  move => _.
  case (eqVneq (f0`_(s (rshift n c) - c)) 0) => [->|nz].
   by rewrite scale0r size_poly0.
  by rewrite size_scaler // size_polyXn -szf0_subproof (leq_coef_size nz).
 rewrite -count_filter.
 apply: succn_inj.
 rewrite Hm -addn1 -{6}(size_enum_ord m).
 rewrite -[index_enum _]enumT.
 rewrite (_ : 1%N 
          = count (predC (fun i0 : 'I_m => rshift n i0 != i)) (enum 'I_m))
         ?count_predC //.
 rewrite -leqNgt in Hi.
 have ordj : (i - n < m)%N.
  rewrite -(ltn_add2r n) (subnK Hi) [(m + n)%N]addnC.
  by apply: ltn_ord.
 rewrite (_ : 1%N = count (pred1 (Ordinal ordj)) (enum 'I_m)).
  apply: eq_count => j.
  rewrite /= /eq_op /= negb_involutive.
  by rewrite -(eqn_addr n) addnC (subnK Hi).
 by rewrite count_uniq_mem ?mem_enum // enum_uniq.
suff: forall k : 'I_(n+m), k <= s k.
  move => Hs; apply/permP => i.
  apply/eqP; rewrite perm1 eq_sym.
  move: i.
  have Hs0 := (fun k => leqif_eq (Hs k)).
  have Hs1 := (leqif_sum (fun i _ => (Hs0 i))).
  move: (Hs1 predT) => /=.
  rewrite (reindex_inj (@perm_inj _ s)) /=.
  by move/leqif_refl; move/forallP.
move => k.
move: (Hin k) (szg k).
rewrite mxE.
case: (splitP k); move => j ->.
  move => _.
  move/(_ isT).
  rewrite mxE.
  case: ifP => //.
  by rewrite size_poly0.
by move/(_ isT) ->.
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

Lemma root_det_coprime_subproof : forall t, ~~ coprimep (f1 t) g0 -> root (\det M) t.
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
have [->|tnz] := (eqVneq t 0).
 (* I believe this case can be simplified now since (f1 0) now must be 0 *)
  rewrite /f1 scale0r poly_comp0.
  have [f00|] := (eqVneq f0`_0 0).
    move => ncoprime.
    have ordm : 0 <  m.
      move: ncoprime.
      by rewrite /coprimep f00 gcd0p szg0_subproof eqSS lt0n.
    rewrite (expand_det_row _ (rshift n (Ordinal ordm))).
    apply/eqP; apply: big1 => i _; apply/eqP.
    rewrite mulf_eq0; apply/orP; left.
    rewrite mxE map_polyE map_id polyseqK col_mxEd mxE.
    case: (Ordinal ordm <= i); last by rewrite horner0.
    rewrite horner_scaler hornerXn.
    have [->|] := (eqVneq (i - Ordinal ordm) 0)%N.
      by rewrite f00 mul0r.
    rewrite -lt0n; move/prednK <-.
    by rewrite exprS mul0r mulr0.
  rewrite eqp_polyC eqp1_dvd1 => f00.
  case/negP.
  apply/coprimepP => d Hd _.
  by rewrite eqp1_dvd1 (dvdp_trans Hd f00).
set f1t := f1 t.
have f1tdef : f1t = \sum_(i < size f0) (f0`_i * t ^+ i) *: 'X ^+ i.
  rewrite /f1t /f1 /poly_comp horner_coef size_map_poly;  apply: eq_bigr => j _.
  rewrite -!mul_polyC commr_exp_mull; last by apply: mulrC.
  by rewrite coef_map mulrA polyC_mul polyC_exp. 
have szf1t : size f1t = n.+1.
  rewrite f1tdef.
  by rewrite -(poly_def (size f0) (fun i => f0`_i * t ^+ i)) size_poly_eq
             -?lead_coefE ?szf0_subproof // mulf_neq0 // ?expf_neq0 // 
             lead_coef_eq0 -size_poly_eq0 szf0_subproof.
have f1ti : forall i, f1t`_i = f0`_i * t ^+ i.
  move => i.
  rewrite f1tdef.
  rewrite -(poly_def (size f0) (fun i => f0`_i * t ^+ i)) coef_poly.
  case: ifP => //.
  move/negbT.
  rewrite -leqNgt => ?.
  by rewrite nth_default // mul0r.
move/dvdpPc: (dvdp_gcdl f1t g0) => [c1 [r1 [c1nz Hr1]]].
move/dvdpPc: (dvdp_gcdr f1t g0) => [c2 [r2 [c2nz Hr2]]].
rewrite /coprimep neq_ltn ltnS leqn0.
case/orP => [|szgcd].
  by rewrite size_poly_eq0 gcdp_eq0 -{1}size_poly_eq0 szf1t.
have szgcd0 : 0 < size (gcdp f1t g0) by apply (@leq_trans 2%N).
have nzr1 : (0 < size r1).
  rewrite lt0n.
  move/eqP: Hr1.
  apply: contraL.
  rewrite size_poly_eq0.
  move/eqP ->.
  by rewrite mul0r scaler_eq0 negb_orb -size_poly_eq0 szf1t c1nz.
have nzr2 : (0 < size r2).
  rewrite lt0n.
  move/eqP: Hr2.
  apply: contraL.
  rewrite size_poly_eq0.
  move/eqP ->.
  by rewrite mul0r scaler_eq0 negb_orb -size_poly_eq0 szg0_subproof c2nz.
have r1small : size r1 <= n.
  rewrite -(prednK szgcd0) ltnS in szgcd.
  by rewrite -ltnS -szf1t -[size f1t](size_scaler _ c1nz) Hr1 size_mul_id
             -?size_poly_eq0 -?lt0n // -(prednK szgcd0) addnS -(prednK szgcd) 
             addnS ltnS leq_addr.
have r2small : size r2 <= m.
  rewrite -(prednK szgcd0) ltnS in szgcd.
  by rewrite -ltnS -szg0_subproof -[size g0](size_scaler _ c2nz) Hr2 size_mul_id
             -?size_poly_eq0 -?lt0n // -(prednK szgcd0) addnS -(prednK szgcd) 
             addnS ltnS leq_addr.
apply/det0P.
exists (row_mx (\row_i ((c2 *: r1)`_i)) (-(\row_i ((c1 *: r2)`_i)))).
  apply/negP; move/eqP.
  rewrite -row_mx0.
  case/eq_row_mx.
  move/rowP.
  have ordszr1 : (size r1).-1 < n.
    by rewrite (prednK nzr1).
  move/(_ (Ordinal ordszr1)).
  rewrite !mxE /=.
  move/eqP.
  rewrite coef_scaler mulf_eq0.
  move/negbTE: c2nz ->.
  rewrite -lead_coefE lead_coef_eq0 -size_poly_eq0 /=.
  move/eqP => impossible.
  move: nzr1.
  by rewrite impossible.
apply/rowP => i.
rewrite /M map_col_mx mul_row_col mulNmx.
rewrite !mxE.
apply/eqP.
set a := (\sum_j _).
have -> : a = ((c2 *: r1) * g0)`_i.
  rewrite coef_mul.
  case/orP: (leq_total i.+1 n) => [ismall|ilarge].
    rewrite (big_ord_widen _ (fun j => (c2 *: r1)`_j * g0`_(i - j)) ismall).
    rewrite big_mkcond.
    apply: eq_bigr => j _.
    rewrite !mxE /horner_morph map_polyE map_id polyseqK ltnS.
    by case: (j <= i); rewrite hornerC // mulr0.
  rewrite -(big_mkord (fun j => true) (fun j =>  (c2 *: r1)`_j * g0`_(i - j)))
          (big_cat_nat _ (fun j => true) (fun j =>  (c2 *: r1)`_j * g0`_(i - j)) (leq0n _) ilarge)
          /=.
  have -> : \sum_(n <= i0 < i.+1) (c2 *: r1)`_i0 * g0`_(i - i0) = 0.
    apply: big1_seq => j /=.
    rewrite mem_index_iota.
    move/andP => [Hnj Hji].
    by rewrite coef_scaler nth_default ?mulr0 ?mul0r // (leq_trans r1small).
  rewrite addr0 big_mkord.
  apply: eq_bigr => j _.    
  rewrite !mxE /horner_morph map_polyE map_id polyseqK.
  case: ifP; rewrite hornerC //.
  move/negbT.
  rewrite -ltnNge => Hij.
  by rewrite coef_scaler nth_default ?mulr0 ?mul0r // (leq_trans _ Hij) // 
             (leq_trans _ ilarge).
set b := (\sum_j _).
have -> : b = ((c1 *: r2) * f1t)`_i.
  rewrite coef_mul.
  case/orP: (leq_total i.+1 m) => [ismall|ilarge].
    rewrite (big_ord_widen _ (fun j => (c1 *: r2)`_j * f1t`_(i - j)) ismall).
    rewrite big_mkcond.
    apply: eq_bigr => j _.
    rewrite !mxE /horner_morph map_polyE map_id polyseqK ltnS.
    case: (j <= i).
      by rewrite horner_scaler hornerXn f1ti.
    by rewrite horner0 mulr0.
  rewrite -(big_mkord (fun j => true) (fun j =>  (c1 *: r2)`_j * f1t`_(i - j))).
  rewrite (big_cat_nat _ (fun j => true) 
          (fun j =>  (c1 *: r2)`_j * f1t`_(i - j)) (leq0n _) ilarge).
  have -> : \sum_(m <= i0 < i.+1) (c1 *: r2)`_i0 * f1t`_(i - i0) = 0.
    apply: big1_seq => j.
    rewrite mem_index_iota.
    case/andP => Hnj; case/andP => Hij _.
    by rewrite coef_scaler nth_default ?mulr0 ?mul0r // (leq_trans r2small).
  rewrite [GRing.add_monoid _ _ _]addr0 big_mkord.
  apply: eq_bigr => j _.
  rewrite !mxE /horner_morph map_polyE map_id polyseqK.
  case: ifP.
    by rewrite f1ti horner_scaler hornerXn.
  rewrite hornerC //.
  move/negbT.
  rewrite -ltnNge => Hij.
  by rewrite coef_scaler nth_default ?mulr0 ?mul0r // (leq_trans _ Hij) // (leq_trans _ ilarge).
by rewrite !scaler_swap Hr1 Hr2 mulrA [r1 * r2]mulrC -mulrA subrr.
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
 by rewrite /root /h horner_poly_comp ![_.[y]]horner_lin /z addrC subrK minPolyxx.
rewrite /h /z polyC_add [x%:P + _]addrC polyC_opp polyC_mul -mul_polyC addrA 
        -mulr_subr mul_polyC.
(*
have PCRM := polyC_RM.
have RM1 : GRing.morphism (horner_morph polyC (t *: ('X - y%:P))).
 by apply: horner_morphRM => //;move => ?;apply: mulrC.
*)
have -> : t *: ('X - y%:P) + x%:P =
          ('X + x%:P) \Po (t *: ('X - y%:P)).
  by rewrite poly_comp_addl poly_comXp poly_compC.
rewrite -poly_compA -/f0.
(*
have RM2 : GRing.morphism (horner_morph polyC ('X - y%:P)).
 by apply: horner_morphRM => //;move => ?;apply: mulrC.
*)
have -> : t *: ('X - y%:P) = (t *: 'X) \Po ('X - y%:P).
  by rewrite poly_comp_scall poly_comXp.
rewrite -[g](poly_compX) -{3}(poly_comp_translateK y).
rewrite -!poly_compA -(eqp_dvdl _ (gcdp_poly_comp _ _ _)) -gxg0_subproof.
rewrite -/(f1 t) -{2}['X-y%:P]poly_comXp dvdp_poly_comp //.
apply (@dvdp_trans _ (gcdp ((f1 t) * 'X) (g0 * 'X))).
 by rewrite dvdp_gcd dvdp_gcdr dvdp_mulr // dvdp_gcdl.
rewrite -(eqp_dvdl _ (mulp_gcdl _ _ _)) -{2}['X]mul1r dvdp_mul2r
        -?size_poly_eq0 ?size_polyX // -eqp1_dvd1 gcdp_eqp1.
apply: contraR troot.
apply: root_det_coprime_subproof.
Qed.

Lemma PET_infiniteCase_subproof : Fadjoin (Fadjoin K x) y = Fadjoin K z.
Proof.
apply/eqP.
rewrite /eq_op /=.
apply/eqP.
apply: subsetv_anti.
apply/andP;split; rewrite -subsetFadjoinE; last first.
 rewrite (subsetv_trans (subsetKFadjoin K x) (subsetKFadjoin _ y)) /=.
 have -> : z = (x%:P - t *: 'X).[y] by rewrite !horner_lin.
 rewrite mempx_Fadjoin // addp_polyOver ?opp_polyOver ?polyOverC ?memx_Fadjoin
         // scalep_polyOver ?polyOverX //.
 have -> : t = (t%:P).[x] by rewrite horner_lin.
 by rewrite mempx_Fadjoin // polyOverC.
rewrite -subsetFadjoinE.
rewrite subsetKFadjoin /=.
have Hy : (y \in Fadjoin K z).
 suff: polyOver (Fadjoin K z) ('X - y%:P).
  move/polyOverP.
  move/(_ 0%N).
  rewrite coef_add coefX add0r coef_opp coefC /=.
  by apply: memvNl.
 rewrite addp_polyOver ?polyOverX // opp_polyOver //.
 have: (polyOver (Fadjoin K z) (gcdp h g)).
  rewrite gcdp_polyOver ?compose_polyOver //; 
   try solve [by rewrite (polyOver_subset (subsetKFadjoin _ _)) // minPolyOver].
  by rewrite addp_polyOver ?polyOverC ?memx_Fadjoin //
             (polyOver_subset (subsetKFadjoin _ _)) // scalep_polyOver ?polyOverX.
 move/polyOverP => HKz.
 rewrite (_ : y = (- (gcdp h g)`_0)/(gcdp h g)`_1).
   by rewrite polyOverC  // memv_mul -?memv_inv // memvN.
 have szgcd : size (gcdp h g) = 2.
  by rewrite (size_eqp gcdhg_subproof) size_XMa.
 apply: (canRL (mulrK _)).
  by rewrite unitfE -[1%N]/(2.-1) -szgcd -lead_coefE lead_coef_eq0
             -size_poly_eq0 szgcd.
 move/eqpP: gcdhg_subproof => [c1 [c2 [c1nz c2nz Hc]]].
 rewrite -unitfE in c1nz.
 apply (can_inj (mulKr c1nz)).
 by rewrite [y * _]mulrC mulrA mulrN -!coef_scaler Hc !coef_scaler !coef_add
            !coefX add0r !coef_opp !coefC subr0 mulr1 mulrN opprK.
by rewrite Hy andbT -[x](subrK (t * y)) -/z memvD ?memv_mul 
           ?[t \in _](subsetv_trans _ (subsetKFadjoin _ _)) // memx_Fadjoin.
Qed.

End InfiniteCase.

(* :TODO: remove this unnecessary lemma. Just use PET_infiniteCase_subproof directly *)
Lemma abstract_PET_infiniteCase_subproof
     : { p : {poly L} | (* (polyOver K p) && *) (p != 0) & 
        forall t : L, t \in K ->  ~~ root p t -> Fadjoin (Fadjoin K x) y = Fadjoin K (x - t * y)}.
Proof.
exists (\det M).
 by rewrite -size_poly_eq0 size_detM.
apply: PET_infiniteCase_subproof.
Defined.

End PrimitiveElementTheorem.

(*
Section Eigenspace.

Variable (K: fieldType) (V:vspaceType K) (f:'End(V)) (lambda:K).

Definition Eigenspace := lker (f - lambda *: \1)%VS.

Lemma EigenspaceIn : forall x, 
(x \in Eigenspace) = (f x == lambda *: x) .
Proof.
move => x.
by rewrite memv_ker add_lappE opp_lappE scale_lappE GRing.subr_eq0 unit_lappE.
Qed.

Lemma EigensubspaceImage : 
 forall vs, (vs <= Eigenspace)%VS -> (f @v: vs <= vs)%VS.
Proof.
move => vs.
move/subsetvP => Hvs.
apply/subsetvP => x.
case/memv_imgP => y [Hy ->].
move/Hvs:(Hy).
rewrite EigenspaceIn.
move/eqP ->.
by apply: memvZ.
Qed.

Lemma EigensubspaceImageEq :
 forall vs, (lambda != 0) -> (vs <= Eigenspace)%VS -> f @v: vs = vs.
Proof.
move => vs Hl Hvs.
apply: subsetv_anti.
apply/andP.
split; first by apply: EigensubspaceImage.
move/subsetvP: Hvs => Hvs.
apply/subsetvP => x Hx.
apply/memv_imgP.
exists (lambda^-1 *: x).
have Hlx : (lambda^-1 *: x \in vs) by apply: memvZ.
split=>//.
move/Hvs: Hlx.
rewrite EigenspaceIn.
move/eqP ->.
by rewrite GRing.scalerA GRing.divff // GRing.scale1r.
Qed.

End Eigenspace.

(* In applications we will require that (subfield E). *)
(* why do I need a2vs here? *)
Definition FieldAutomorphism (E:{algebra L}) (f : 'End(L) ) : bool :=
 [&& (f @v: E == a2vs E), (E^C <= Eigenspace f 1)%VS &
 (all (fun v1 => all (fun v2 => f (v1 * v2) == f v1 * f v2) (vbasis E))
      (vbasis E))].

Lemma AutomorphMul : forall E f, FieldAutomorphism E f -> 
forall u v, u \in E -> v \in E -> f (u * v) = f u * f v.
Proof.
move => E f.
case/and3P => _ _.
move/all_nthP => fmult u v Hu Hv.
have Hspan : (is_span E (vbasis E)) by rewrite is_basis_span ?is_basis_vbasis.
rewrite (is_span_span Hspan Hu) (is_span_span Hspan Hv).
rewrite !linear_sum /=; apply eq_bigr => j _.
rewrite -!mulr_suml linear_sum /=.
apply: eq_bigr => i _.
rewrite -scaler_mull linearZ /= -scaler_mulr linearZ /=.
rewrite linearZ /= -scaler_mull linearZ -scaler_mulr.
repeat apply f_equal.
apply/eqP.
move/all_nthP : (fmult 0 _ (ltn_ord i)).
by apply.
Qed.

Lemma AutomorphismIsUnit : forall E f, 
 FieldAutomorphism E f -> lker f = 0%:VS.
Proof.
move => E f.
case/and3P => Hf1 Hf2 _.
apply/eqP.
rewrite -(capfv (lker f)) -dimv_eq0 -(eqn_addr (\dim (f @v: (fullv _)))).
rewrite add0n limg_ker_dim -(addv_complf E) limg_add.
move/eqP: Hf1 ->.
rewrite (EigensubspaceImageEq _ Hf2) //.
apply: GRing.nonzero1r.
Qed.

Lemma Automorph1 : forall E f, FieldAutomorphism E f -> f 1 = 1.
Proof.
move => E f Hf.
case/and3P: (Hf).
move/eqP => Hf1 _ _.
have Hf10 : GRing.unit (f 1).
 by rewrite unitfE -memv_ker (AutomorphismIsUnit Hf) memv0 nonzero1r.
apply: (can_inj (mulKr Hf10)).
by rewrite mulr1 -(AutomorphMul Hf) ?memv1 // mulr1.
Qed.

Lemma idAutomorphism : forall E, FieldAutomorphism E \1%VS.
Proof.
move => E.
apply/and3P; split; do ? (apply/allP => i _ ;apply/allP => j _);
 rewrite ?unit_lappE ?lim1g //.
apply/subsetvP => v _.
by rewrite EigenspaceIn unit_lappE GRing.scale1r.
Qed.

Lemma compAutomorphism : forall E f g, 
 FieldAutomorphism E f ->  FieldAutomorphism E g ->
 FieldAutomorphism E (f \o g)%VS.
Proof.
move => E f g Ff Fg.
case/and3P: (Ff); move/eqP => Hf1; move/subsetvP => Hf2; move/eqP => _.
case/and3P: (Fg); move/eqP => Hg1; move/subsetvP => Hg2; move/eqP => _.
apply/and3P; split; do 2? apply/allP => ? ?;
  rewrite ?limg_comp ?comp_lappE /= ?Hg1 ?Hf1 //.
  apply/subsetvP => v Hv.
  rewrite EigenspaceIn comp_lappE /=.
  move/(_ _ Hv): Hg2; rewrite EigenspaceIn; move/eqP->.
  move/(_ _ Hv): Hf2; rewrite EigenspaceIn.
  by rewrite  GRing.scale1r.
by rewrite (AutomorphMul Fg);
 first (rewrite (AutomorphMul Ff) // -[g _ \in E]/(g _ \in a2vs E) -Hg1);
 do ? apply memv_img; apply: memv_basis.
Qed.

Lemma invAutomorphism : forall E f,
 FieldAutomorphism E f -> FieldAutomorphism E (f \^-1)%VS.
Proof.
move => E f Ff.
have kerf := AutomorphismIsUnit Ff.
case/and3P: (Ff); move/eqP => Hf1; move/subsetvP => Hf2; move/eqP => _.
have H1 : (inv_lapp f @v: E = E).
 apply/eqP.
 by rewrite -{1}Hf1 -limg_comp inv_lker0 ?kerf // lim1g.
apply/and3P; split.
- by rewrite H1.
- apply/subsetvP => v.
  move/Hf2=> Hv; rewrite EigenspaceIn GRing.scale1r in Hv.
  rewrite EigenspaceIn GRing.scale1r.
  rewrite -{1}(eqP Hv) /=.
  by rewrite -[(f \^-1)%VS (f _)](comp_lappE) inv_lker0 ?kerf // unit_lappE.
- rewrite <- Hf1.
  do 2 (apply/allP => ?; move/memv_basis;
        case/memv_imgP => ? [? ->]).
  rewrite -(AutomorphMul Ff) // -!{1}[(f \^-1)%VS (f _)](comp_lappE).
  by rewrite inv_lker0 ?kerf // !unit_lappE.
Qed.

Definition FixedField E f := (E :&: @Eigenspace F0 L f 1)%VS.

Lemma FixedField_is_subfield : forall E f,
  FieldAutomorphism E f ->
  let K0 := FixedField E f in
  ((1 \in K0) && (K0 * K0 <= K0))%VS.
Proof.
move => E f Hf /=.
apply/andP; split.
 rewrite memv_cap.
 apply/andP; split.
  by apply: memv1.
 by rewrite EigenspaceIn (Automorph1 Hf) scale1r.
apply/prodvP => u v.
rewrite !memv_cap !EigenspaceIn !scale1r.
case/andP => uE; move/eqP => fu.
case/andP => vE; move/eqP => fv.
apply/andP; split.
 by rewrite memv_mul.
by rewrite (AutomorphMul Hf) // fu fv.
Qed.

Canonical Structure FixedField_subfield E f Hf : {algebra L} :=
 Eval hnf in ASpace (@FixedField_is_subfield E f Hf).

Lemma AutomorphsimEE_id : 
 forall E f, FieldAutomorphism E f -> FixedField E f = E -> f = \1%VS.
Proof.
move => E f.
case/and3P => _.
move/subsetvP => Hf _ HE.
apply/eqP.
apply/eq_lapp => v.
move: (memvf v).
rewrite unit_lappE -(addv_complf (FixedField E f)).
move/addv_memP => [va [vb [Hva Hvb ->]]].
move: Hva Hvb.
rewrite memv_cap HE.
rewrite linearD EigenspaceIn /=.
case/andP => _.
move/eqP ->.
move/Hf.
rewrite EigenspaceIn.
move/eqP ->.
by rewrite !GRing.scale1r.
Qed.
*)

End Galois.
