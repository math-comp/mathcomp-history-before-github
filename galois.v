Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq tuple.
Require Import fintype finfun bigop ssralg poly polydiv.
Require Import zmodp vector algebra fieldext.
Require Import fingroup perm finset matrix mxalgebra.
Require Import div cyclic prime binomial.

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
(* DerivationExtend K x D == Given a derivation D on K and a separable        *)
(*                           element x over K, this function returns the      *)
(*                           unique extension of D to K(x).                   *)
(******************************************************************************)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope ring_scope.

Import GRing.Theory.

Lemma exprp_addl: forall (R : comRingType) (x y : R) (n : nat),
  [char R].-nat n -> (x + y) ^+ n = x ^+ n + y ^+ n.
Proof.
move => R x y [|[|n]] // Hn.
set (n' := n.+2) in *.
set (p := pdiv n').
have Hp : p \in [char R].
 move/pnatP: (Hn).
 by apply => //; rewrite ?pdiv_prime // pdiv_dvd.
move: Hn.
rewrite (eq_pnat _ (charf_eq Hp)).
case/p_natP => e ->.
set (f := Frobenius_aut Hp).
have Hiter : forall z, z ^+ (p ^ e) = iter e f z.
 elim: e => // e IH z.
 by rewrite expnS mulnC exprn_mulr IH.
rewrite !Hiter {Hiter}.
elim: e => // e IH /=.
by rewrite -rmorphD -IH.
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

End SeparablePoly.

Section Separable.

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

Lemma sub1v : (1%:VS <= K)%VS.
Proof. by apply: memv1. Qed.

Lemma subv1 : ((K <= 1%:VS) = (K == F))%VS.
Proof.
apply/idP/idP; last by move/eqP->; exact: subv_refl.
move=> H; rewrite /eq_op; apply/eqP.
by apply: subv_anti; rewrite H  sub1v.
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

Lemma poly_polyOver : forall n (E : nat -> L),
  (forall i, E i \in K) -> polyOver (\poly_(i < n) E i).
Proof.
move => n E HE.
rewrite poly_def.
apply: sump_polyOver => i _.
by rewrite scalep_polyOver // exp_polyOver // polyOverX.
Qed.

Lemma compose_polyOver : forall p q : {poly L},
  polyOver p -> polyOver q -> polyOver (p \Po q).
Proof.
move => p q; move/polyOverP => Hp; move/polyOverP => Hq.
apply/polyOverP => i.
rewrite /poly_comp horner_coef coef_sum memv_suml // => j _.
rewrite coef_mul memv_suml // => k _.
apply: memv_mul.
   by rewrite coef_map coefC; case: eqP=> // _; exact: mem0v.
elim: (j:nat) (i - k)%N => [|l IH] m.
 by rewrite coefC fun_if if_arg mem0v memv1 if_same.
rewrite exprS coef_mul memv_suml // => n _.
by rewrite memv_mul ?IH.
Qed.

Lemma deriv_polyOver :  forall (p : {poly L}), polyOver p -> polyOver p^`().
Proof.
move => ?; move/polyOver_suba => [p ->].
by apply/polyOver_suba; exists (p^`()); apply: deriv_map.
Qed.

End SubAlgebra.

Section aspace_cap.

Variable A B : {algebra L}.

Canonical Structure fspace_cap : {algebra L} :=
 Eval hnf in (aspace_cap (trans_eq (aunit_eq1 A) (sym_eq (aunit_eq1 B)))).

End aspace_cap.

Lemma polyOver_subset : forall (K E : {algebra L}) p, (K <= E)%VS ->
 polyOver K p -> polyOver E p.
Proof.
move => K E p; move/subvP => KE; move/polyOverP => Kp.
by apply/polyOverP => i; rewrite KE.
Qed.

Lemma memv_horner: forall (K E : {algebra L}) p, polyOver K p -> (K <= E)%VS ->
 forall x, x \in E -> p.[x] \in E.
Proof.
move => K E p; move/polyOverP => x HE pK Hx.
rewrite horner_coef memv_suml // => i _.
rewrite memv_mul //; last by rewrite memv_exp.
by move/subvP : HE; apply.
Qed.

(* A deriviation only needs to be additive and satify lebniz's law, but all the
   deriviation I will use are going to be linear, so we just define a
   derivation to be linear. *) 
Definition Derivation (K:{algebra L}) (D : 'End(L)) : bool :=
 let s := vbasis K in
 (all (fun v1 => all (fun v2 => D (v1 * v2) == D v1 * v2 + v1 * D v2) 
                     s) s).

Lemma DerivationMul : forall E D, Derivation E D -> 
  forall u v, u \in E -> v \in E -> D (u * v) = D u * v + u * D v.
Proof.
move => E D.
move/all_nthP; rewrite size_tuple=> Dmult u v Hu Hv.
have Hspan : (is_span E (vbasis E)) by rewrite is_basis_span ?is_basis_vbasis.
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
        ?subv_refl //.
rewrite (IHp Hp0) deriv_amulX !horner_add !horner_mul !hornerX !hornerC.
rewrite !mulr_addl -!addrA; congr (_ + _).
by rewrite addrC [_ + D c]addrC -mulrA [_ * x]mulrC mulrA addrA.
Qed.

Lemma subvDerivation : forall (E K : {algebra L}) D, (K <= E)%VS ->
  Derivation E D -> Derivation K D.
Proof.
move => E K D.
move/subvP => HKE HED.
apply/allP => x Hx.
apply/allP => y Hy.
apply/eqP.
by rewrite (DerivationMul HED) // HKE // memv_basis.
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
 by rewrite ltnS {6}/d -dimvf dimvS // subvf.
rewrite leq_pmull // lt0n dimv_eq0 -subv0.
apply: contra (nonzero1r L) => HK.
move: (subv_trans (sub1v K) HK).
move/subvP.
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
rewrite -subv0 -dimv_sum_leqif neq_ltn.
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
 by rewrite ltnS dimvS // subv_add subv_refl (subv_trans _ (asubv K))
            // prodv_monor.
by rewrite -addn1 mulnC -[(2 * _)%N]/(\dim K + (\dim K + 0))%N
           leq_add2l addn0 -(dimv1 L) dimvS // sub1v.
Qed.

(* Give k*x^i return the k.  Used as a tool.
   It would nicer to hide this definition and it's assocated lemmas. *)
Definition MinPoly_coef i v := 
  \sum_j coord [tuple of map (fun y => (y * x ^+ i))
                (vbasis K)] v j *: (vbasis K)`_j.

Lemma MinPoly_coefK : forall i v, MinPoly_coef i v \in K.
Proof.
move => i v.
rewrite /MinPoly_coef /= memv_suml => // j _.
by rewrite memvZl // memv_basis // mem_nth // size_tuple.
Qed.

Lemma memv_MinPoly_coef : forall i v, v \in (K * (x ^+ i)%:VS)%VS ->
 v = (MinPoly_coef i v) * x ^+ i.
Proof.
move => i v.
rewrite (_ : (K * (x ^+ i)%:VS)%VS = 
             span (map (fun y => (y * x ^+ i)) (vbasis K))).
 move/(coord_span) => Hv.
 rewrite {1}Hv {Hv} /MinPoly_coef.
 rewrite -GRing.mulr_suml.
 apply: eq_bigr => j _.
 by rewrite (nth_map 0) ?scaler_mull // size_tuple.
apply: subv_anti.
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
rewrite add0r memvN // memv_suml // => j _.
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
apply: (subv_trans _ HV).
by rewrite addvSr.
Qed.

Definition poly_for_Fadjoin (v : L) := 
  \sum_(i < elementDegree) (MinPoly_coef i (sumv_pi 
     (fun (i : 'I_elementDegree) => (K * (x ^+ i)%:VS)%VS) predT i v))%:P *
   'X^i.

Lemma poly_for_polyOver : forall v, polyOver K (poly_for_Fadjoin v).
Proof.
move => v.
apply/polyOverP => i.
rewrite /poly_for_Fadjoin coef_sum memv_suml // => j _.
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
 move: (subv_trans x0 (sub0v K)).
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
apply: memv_sumr=> i _.
by rewrite exprSr mulrA (mulfK Hx) memv_prod ?memv_inj.
Qed.

Lemma subsetFadjoinE_subproof: forall E : {algebra L},
   (K <= E)%VS && (x \in E) = (FadjoinVS <= E)%VS.
Proof.
move => E.
apply/idP/idP.
 case/andP => KE xE.
 apply/subv_sumP => i _.
 apply: (subv_trans _ (asubv _)).
 apply: (subv_trans (prodv_monol _ _) (prodv_monor _ _)) => //.
 by apply: memv_exp.
move => HFxE.
apply/andP; split; apply: (subv_trans _ HFxE).
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
apply: (subv_trans _ (addvSr _ _)).
apply: (subv_trans _ (addvSl _ _)).
by rewrite -{1}[x%:VS]prod1v prodv_monol // sub1v.
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
by move: (subv_refl Fadjoin); rewrite -subsetFadjoinE; case/andP.
Qed.

Lemma subsetKFadjoin : (K <= Fadjoin)%VS.
Proof.
by move: (subv_refl Fadjoin); rewrite -subsetFadjoinE; case/andP.
Qed.

Lemma memK_Fadjoin : forall y, y \in K -> y \in Fadjoin.
Proof.
by move/subvP: subsetKFadjoin.
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
by apply: memK_Fadjoin.
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
 apply: subv_anti.
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

Definition separableElement := separablePolynomial (minPoly K x).

Lemma separableElementP :  
  reflect 
  (exists f, polyOver K f /\ root f x /\ separablePolynomial f) 
   separableElement.
Proof.
apply: (iffP idP).
 move => ?; exists (minPoly K x); do ! (split => //).
  by apply: minPolyOver.
 by apply root_minPoly.
move => [f [fK [rf sf]]].
move/dvdpPc: (minPoly_dvdp fK rf) => [c [g [Hc Hg]]].
move: (canRL (GRing.scalerK Hc) Hg) sf ->.
rewrite (GRing.scaler_mull) separable_mul.
by case/and3P.
Qed.

Lemma separableinK : x \in K -> separableElement.
Proof.
move => Hx.
apply/separableElementP.
exists ('X - x%:P); repeat split.
  by rewrite addp_polyOver ?polyOverX // opp_polyOver // polyOverC.
 by rewrite root_factor_theorem dvdpp.
by rewrite /separablePolynomial !derivCE subr0 coprimep1.
Qed.

Lemma separable_nzdmp : separableElement = (deriv (minPoly K x) != 0).
Proof.
rewrite /separableElement /separablePolynomial.
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

Lemma separableNXp : 
  reflect (exists2 p, p \in [char L] & 
            exists2 g, (polyOver K g) & (minPoly K x) = g \Po 'X^p)
          (~~ separableElement).
Proof.
rewrite separable_nzdmp negb_involutive.
apply: (iffP eqP); last first.
 move => [p Hp [g _ ->]].
 by rewrite deriv_poly_comp derivXn -scaler_nat (charf0 Hp) scale0r mulr0.
move/eqP: (monic_minPoly K x).
set (f := minPoly K x) => Hlead Hdf.
have/eqP Hnz : ((size f).-1)%:R = (0:L).
 rewrite -(coef0 _ ((size f).-2)) -Hdf coef_deriv size_minPoly.
 rewrite (prednK (elementDegreegt0 _ _)).
 rewrite -[(elementDegree K x)]/((elementDegree K x).+1.-1) -size_minPoly.
 by rewrite [f`_(_).-1]Hlead.
move : (elementDegreegt0 K x).
rewrite -[(elementDegree K x)]/((elementDegree K x).+1.-1) -size_minPoly.
case/natf0_char/(_ Hnz) => p Hp.
exists p; first done.
rewrite -(dvdn_charf Hp) in Hnz.
move: (divnK Hnz).
set r := ((size f).-1 %/ p)%N => Hrp.
exists (\poly_(i < r.+1) f`_(i * p)).
 rewrite poly_polyOver // => i.
 move: (i * p)%N.
 apply/polyOverP.
 by apply: minPolyOver.
rewrite poly_compE size_poly_eq; last by rewrite Hrp [f`_(_)]Hlead nonzero1r.
apply/polyP => i.
rewrite coef_sum.
case Hpi: (p %| i)%N ;last first.
 transitivity (0:L).
  case: i Hpi => [|i Hpi]; first by rewrite dvdn0.
  rewrite -{2}(mul0r ((i.+1)%:R ^-1)) -{2}(coef0 _ i) -Hdf coef_deriv.
  by rewrite -mulr_natr mulfK // -(dvdn_charf Hp) Hpi.
 symmetry.
 apply: big1 => j _.
 rewrite coef_scaler -exprn_mulr coef_Xn.
 case: eqP Hpi => [->|]; last by rewrite mulr0.
 by rewrite (dvdn_mulr _ (dvdnn p)).
move: (divnK Hpi) <-.
set s := (i %/ p)%N.
have Hp0 : 0 < p by apply/prime_gt0/(@charf_prime L).
case: (leqP r.+1 s) => Hrs.
 transitivity (0:L).
  apply: nth_default.
  rewrite -(@prednK (size f)); last by rewrite size_minPoly.
  by rewrite -Hrp ltn_mul2r Hrs andbT.
 symmetry.
 apply: big1 => j _.
 rewrite coef_scaler -exprn_mulr coef_Xn.
 case: (eqVneq s j) => [Hsj|]; first by move: Hrs; rewrite Hsj ltnNge leq_ord.
 rewrite mulnC eqn_mul2l.
 move/negb_true_iff ->.
 by rewrite eqn0Ngt Hp0 mulr0.
pose (s' := Ordinal Hrs).
rewrite (bigD1 s') // coef_scaler -exprn_mulr coef_Xn {2}mulnC eq_refl mulr1.
rewrite coef_Poly nth_mkseq // mulnC big1 ?[_ _ 0]addr0 // => j.
move/negb_true_iff.
rewrite eq_sym => Hj.
rewrite coef_scaler -exprn_mulr coef_Xn eqn_mul2l [(s == j)]Hj eqn0Ngt Hp0.
by rewrite mulr0.
Qed.

Lemma separableNrootdmp : 
  separableElement != (root (deriv (minPoly K x)) x).
Proof.
rewrite separable_nzdmp size_elementDegree.
  by case: (_ == 0).
 by rewrite deriv_polyOver // minPolyOver.
by rewrite (leq_trans (size_Poly _)) // size_mkseq size_minPoly leqnn.
Qed.

Lemma DerivationSeparable : forall D, Derivation Fadjoin D -> 
 separableElement ->
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
 polyOver K p -> separableElement ->
 DerivationExtend (p.[x]) = (map_poly D p).[x] + p^`().[x] * Dx.
Proof.
move => p Kp sep.
move: separableNrootdmp.
rewrite negb_eqb addbC /root sep addbT {sep} => sep.
rewrite lapp_of_funK; last by apply: DerivationExtend_body_linear.
rewrite {-1}(divp_mon_spec p (monic_minPoly K x)) /DerivationExtend_body.
rewrite poly_for_modp // /horner_morph (Derivation_addp HD);
  rewrite ?(Derivation_mulp HD);
  rewrite ?(mulp_polyOver, divp_polyOver, modp_polyOver, minPolyOver) //. 
rewrite derivD derivM !horner_add !horner_mul minPolyxx !mulr0 !add0r.
rewrite mulr_addl addrA [_ + (_ * _ * _)]addrC {2}/Dx /horner_morph -mulrA -/Dx.
by rewrite [((minPoly K x)^`()).[x] * Dx]mulrC (mulfVK sep) mulrN addKr.
Qed.


Lemma DerivationExtendDerivation :
 separableElement -> Derivation Fadjoin DerivationExtend.
Proof.
move => sep.
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
Lemma separableDerivationP :
  reflect (forall D, Derivation Fadjoin D ->
                     (K <= lker D)%VS -> (Fadjoin <= lker D)%VS)
          separableElement.
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
 by rewrite /D_body poly_for_linear -mul_polyC derivD derivM derivC mul0r
            add0r horner_add horner_mul hornerC -scaler_mull mul1r.
pose D := lapp_of_fun D_body.
have DF : (K <= lker D)%VS.
 apply/subvP => v vK.
 by rewrite memv_ker lapp_of_funK // /D //= /D_body poly_for_K // derivC 
            horner0.
have DDeriv : Derivation Fadjoin D.
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
  rewrite separable_nzdmp (_ : (minPoly K x)^`() = 1%:P)  ?nonzero1r //.
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
move/subvP.
move/(_ _ memx_Fadjoin).
rewrite memv_ker.
move/eqP ->.
rewrite eq_sym.
by apply: nonzero1r.
Qed.

End MoreFadjoin.

Lemma subsetSeparable : forall (K E : {algebra L}) x, (K <= E)%VS -> 
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
apply (iffP idP); last by apply; apply memx_Fadjoin.
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
 apply/eqP.
 change (Fadjoin (Fadjoin K q.[x]) x == Fadjoin K x :> {vspace L}).
 apply/eqP.
 apply: subv_anti.
 by rewrite -!{1}subsetFadjoinE mempx_Fadjoin //
         (subv_trans _ (subsetKFadjoin (Fadjoin K _) _)) subsetKFadjoin 
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
 apply: (subv_trans _ (subsetKFadjoin _ _)).
 by apply: Ht.
by rewrite (DerivationSeparable DED) // !hmD ?compose_polyOver ?minPolyOver //
           oppr0 mul0r mulr0 addr0.
Qed.

Lemma FadjoinC : forall x y K,
  Fadjoin (Fadjoin K x) y = Fadjoin (Fadjoin K y) x.
Proof.
suff : forall (x y : L) (K : {algebra L}),
 (Fadjoin (Fadjoin K x) y <= Fadjoin (Fadjoin K y) x)%VS.
 move => H x y K.
 apply/eqP; rewrite /eq_op; apply/eqP.
 apply:subv_anti.
 by apply/andP; split.
move => x y K.
rewrite -!subsetFadjoinE memx_Fadjoin memK_Fadjoin ?memx_Fadjoin //.
by rewrite (@subv_trans _ _ (Fadjoin K y)) // subsetKFadjoin.
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

Section PurelyInseparableElement.

Variable (K : {algebra L}).

Lemma separablePower : forall x, 
 exists n, [char L].-nat n && separableElement K (x ^+ n).
Proof.
move => x.
move: {2}(elementDegree K x) (leqnn (elementDegree K x)) => n.
elim: n x => [|n IHn] x.
 by rewrite -(prednK (elementDegreegt0 K x)).
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
 apply: size_dvdp; last first.
  apply: minPoly_dvdp => //.
  by rewrite /root -hornerXn -horner_poly_comp -Hg minPolyxx.
 move/eqP: Hg.
 apply: contraL.
 move/eqP ->.
 by rewrite poly_com0p -size_poly_eq0 size_minPoly.
rewrite -[size (minPoly K x)](prednK); last by rewrite size_minPoly.
rewrite Hg size_poly_comp_id ltnS.
rewrite size_polyXn.
case: (leqP (size g) 1) Hg.
 move/size1_polyC ->.
 rewrite poly_compC => Hg.
 have : size (minPoly K x) <= 1 by rewrite Hg size_polyC leq_b1.
 by rewrite size_minPoly ltnS leqNgt elementDegreegt0.
move => Hszg _.
rewrite -{1}(prednK (ltnW Hszg)) -subn_gt0.
rewrite -(prednK (prime_gt0 (charf_prime Hp))) mulnS addKn muln_gt0 -!subn1.
by rewrite !subn_gt0 Hszg (prime_gt1 (charf_prime Hp)).
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
  by rewrite /root !horner_lin horner_poly_comp hornerXn -Hx subrr.
 rewrite /separablePolynomial !(derivE, deriv_poly_comp).
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
set (K' := Fadjoin K (x ^+ p)).
set (g := 'X^p - (x ^+ p)%:P).
have HK'g : polyOver K' g.
 by rewrite addp_polyOver ?exp_polyOver ?polyOverX // opp_polyOver // polyOverC
            // memx_Fadjoin.
have rootg : root g x by rewrite /root !horner_lin hornerXn subrr.
move/(subsetSeparable (subsetKFadjoin _ (x ^+ p))).
move : (root_minPoly K' x) (minPoly_dvdp HK'g rootg) (minPolyOver K' x).
rewrite root_factor_theorem /separableElement -/K'.
move/(dvdMpP).
case/(_ (monic_factor _)) => c -> Hcg HK'c.
rewrite separable_mul.
have Hp' : p \in [char {poly L}] by apply: (rmorph_char (polyC_rmorphism _)).
case/and3P => _ _ Hc.
 have : (coprimep c g).
 rewrite /g polyC_exp -!(Frobenius_autE Hp') -rmorph_sub.
 rewrite [_ (_ - _)]Frobenius_autE -(prednK (prime_gt0 (charf_prime Hp))).
 elim: p.-1 => [|n]; first by rewrite expr1.
 (* TODO: abstract out coprime p q -> coprime p r -> coprime p (q*r) *)
 rewrite -gcdp_eqp1 => IH.
 move: (egcdpPW c (('X - x%:P) ^+ n.+1)) => [s [t]].
 rewrite (eqp_transr IH) -(@eqp_mul2r _ ('X - x%:P)); last first.
  by rewrite monic_neq0 // monic_factor.
 rewrite mul1r mulr_addl -[t * _ * _]mulrA -exprSr => Hcn.
 apply/coprimepP => d Hdc Hdn.
 move/coprimepP: Hc; apply; first done.
 by rewrite -(eqp_dvdr _ Hcn) -mulrA dvdp_add // dvdp_mull // dvdp_mulr.
move/coprimepP/(_ _ (dvdpp c))/(_ (dvdp_trans (dvdp_mulr _ (dvdpp c)) Hcg)).
rewrite -size1_dvdp1.
move/eqP => Hszc.
move: HK'c (Hszc).
rewrite (size1_polyC (eq_leq Hszc)) size_polyC mulr_addr -polyC_opp -polyC_mul.
move/polyOverP => Hx.
move: (Hx 1%N) (Hx 0%N).
rewrite !coef_add !coef_mulX !coefC add0r addr0 => Hx1 Hx0.
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

Definition purelyInseparableElement x :=
  x ^+ (ex_minn (separablePower x)) \in K.

Lemma purelyInseparableElementP : forall x, reflect 
 (exists2 n, [char L].-nat n & x ^+ n \in K)
 (purelyInseparableElement x).
Proof.
move => x.
rewrite /purelyInseparableElement.
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
rewrite (separableCharp _ (em - en.+1)%N Hp) => Hsepn.
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
 (x \in K) = separableElement K x && purelyInseparableElement x.
Proof.
move => x.
rewrite /purelyInseparableElement.
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

Lemma inseparableinK : forall x, x \in K -> purelyInseparableElement x.
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
pose h := fun i => finfun (fun j => (SeqSub (Hh0 i j):Cs)).
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
move/poly_for_eq:(Hzi a1) ->.
move/poly_for_eq:(Hzi a2) ->.
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
 by apply: memv1.
case (eqVneq y 0) => [->|Hy0].
 right; exists x.
 move: (mem0v K).
 rewrite FadjoinxK.
 by move/eqP ->.
move/cyclicOrBig: (Hy0) => [|[[|b] Hyb]]; first by left.
 rewrite expr1 in Hyb.
 right; exists x.
 move: (memv1 K).
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
apply/eqP.
rewrite /eq_op /=.
apply/eqP.
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
rewrite (leq_trans (size_prod _ _)) // eq_cardT // size_enum_ord big_split_ord
        /= leq_sub_add addnS ltnS -addnA leq_add //.
 pose p := fun i => M (lshift m i) (s (lshift m i)).
 have : forall i, predT i -> size (p i) <= 1.
  move => i _.
  by rewrite /p col_mxEu /Mg mxE !(fun_if, if_arg) size_polyC size_poly0 
             leq_b1 if_same.
 move/leq_sum.
 move/leq_trans => -> //.
 by rewrite sum_nat_const eq_cardT // size_enum_ord muln1.
pose p := fun i => M (rshift n i) (s (rshift n i)).
have : forall i, predT i -> (size (p i)) <= n.+1.
 move => i _.
 rewrite /p col_mxEd /Mf mxE.
 case: ifP => [_|_]; last by rewrite size_poly0.
 set j := (_ - _)%N.
 have [big|small] := (leqP (size f0) j).
  by rewrite (nth_default _ big) scale0r size_poly0.
 have [->|f0neq0] := (eqVneq f0`_j 0).
  by rewrite scale0r size_poly0.
 by rewrite size_scaler // size_polyXn -ltnS -szf0_subproof.
move/leq_sum.
move/leq_trans => -> //.
by rewrite sum_nat_const eq_cardT // size_enum_ord mulnS mulnC.
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
 rewrite size_polyXn.
 by rewrite -{4 8}[n](prednK (elementDegreegt0 _ _)) -/n addSn !ltnS leq_sub_add
            [(n.-1 + _)%N]addnC.
suff: forall i0, (i0 != i) -> size (M (rshift n i0) (s (rshift n i0))) <= n.+1.
 move/leq_sum; move/leq_trans; apply.
 move: (cardC (pred1 i)).
 rewrite sum_nat_const card_ord card1 => Hcard.
 by rewrite leqNgt -{1}Hcard mulnC ltnn.
 (* by rewrite -[m in m.-1]Hcard add1n /= mulnC. *)
move => j _.
rewrite col_mxEd mxE.
case: ifP; last by rewrite size_poly0.
case: (eqVneq f0`_(s (rshift n j) - j) 0) => [->|Hf0].
 by rewrite scale0r size_poly0.
rewrite size_scaler // size_polyXn-szf0_subproof.
apply: contraLR.
rewrite -leqNgt.
move/(nth_default 0) => H.
move:H Hf0 ->.
by rewrite eq_refl.
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
  rewrite /f1t /f1 /poly_comp horner_coef size_map_poly;  apply: eq_bigr => j _.
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
move/dvdpPc: (dvdp_gcdl f1t g0) => [c1 [r1 [c1nz Hr1]]].
move/dvdpPc: (dvdp_gcdr f1t g0) => [c2 [r2 [c2nz Hr2]]].
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
  move/eqP ->.
  by rewrite mul0r scaler_eq0 negb_orb -size_poly_eq0 szg0_subproof c2nz.
have r1small : size r1 <= n.
  case (eqVneq (size r1) 0%N) => [->|] //.
  rewrite -lt0n => nzr1.
  rewrite -(prednK szgcd0) ltnS in szgcd.
  rewrite -ltnS (leq_trans _ szf1t) //.
  by rewrite -[size f1t](size_scaler _ c1nz) Hr1 size_mul_id
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
  case/eq_row_mx => _.
  move/rowP.
  have ordszr2 : (size r2).-1 < m.
    by rewrite (prednK nzr2).
  move/(_ (Ordinal ordszr2)).
  rewrite !mxE /=.
  move/eqP.
  rewrite oppr_eq0 coef_scaler mulf_eq0.
  move/negbTE: c1nz ->.
  rewrite -lead_coefE lead_coef_eq0 -size_poly_eq0 /=.
  move/eqP => impossible.
  move: nzr2.
  by rewrite impossible.
apply/rowP => i.
rewrite /M map_col_mx mul_row_col mulNmx.
rewrite !mxE.
apply/eqP.
have matrixPolyMul: forall (h r : {poly L}) k z c, size r <= k ->
  (z = (map_mx (fun x0 : {poly L} => (map_poly id x0).[t])
        (\matrix_(i, j) (if i <= j then (h`_(j - i))%:P else 0)))) ->
  \sum_j
   (\row_i0 (c *: r)`_i0) 0 (j:'I_k) * z j i = ((c *: r) * h)`_i.
  move => h r k z c rsmall -> {z}.
  set a := (\sum_j _).
  rewrite coef_mul.
  case/orP: (leq_total i.+1 k) => [ismall|ilarge].
    rewrite (big_ord_widen _ (fun j => (c *: r)`_j * h`_(i - j)) ismall).
    rewrite big_mkcond.
    apply: eq_bigr => j _.
    rewrite !mxE /horner_morph map_polyE map_id polyseqK ltnS.
    by case: (j <= i); rewrite hornerC // mulr0.
  rewrite -(big_mkord (fun j => true) (fun j =>  (c *: r)`_j * h`_(i - j)))
          (big_cat_nat _ (fun j => true) (fun j =>  (c *: r)`_j * h`_(i - j))
                         (leq0n _) ilarge)
          /=.
  have -> : \sum_(k <= i0 < i.+1) (c *: r)`_i0 * h`_(i - i0) = 0.
    apply: big1_seq => j /=.
    rewrite mem_index_iota.
    move/andP => [Hnj Hji].
    by rewrite coef_scaler nth_default ?mulr0 ?mul0r // (leq_trans rsmall).
  rewrite addr0 big_mkord.
  apply: eq_bigr => j _.
  rewrite !mxE /horner_morph map_polyE map_id polyseqK.
  case: ifP; rewrite hornerC //.
  move/negbT.
  rewrite -ltnNge => Hij.
  by rewrite coef_scaler nth_default ?mulr0 ?mul0r // (leq_trans _ Hij) // 
             (leq_trans _ ilarge).
rewrite (matrixPolyMul g0) //.
rewrite (matrixPolyMul f1t) //.
  by rewrite !scaler_swap Hr1 Hr2 mulrA [r1 * r2]mulrC -mulrA subrr.
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
 by rewrite /root /h horner_poly_comp ![_.[y]]horner_lin /z addrC subrK 
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

Lemma PET_infiniteCase_subproof : Fadjoin (Fadjoin K y) x = Fadjoin K z.
Proof.
apply/eqP.
rewrite /eq_op /=.
apply/eqP.
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
  rewrite coef_add coefX add0r coef_opp coefC /=.
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
  by rewrite (size_eqp gcdhg_subproof) size_XMa.
 apply: (canRL (mulrK _)).
  by rewrite unitfE -[1%N]/(2.-1) -szgcd -lead_coefE lead_coef_eq0
             -size_poly_eq0 szgcd.
 move/eqpP: gcdhg_subproof => [c1 [c2 [c1nz c2nz Hc]]].
 rewrite -unitfE in c1nz.
 apply (can_inj (mulKr c1nz)).
 by rewrite [y * _]mulrC mulrA mulrN -!coef_scaler Hc !coef_scaler !coef_add
            !coefX add0r !coef_opp !coefC subr0 mulr1 mulrN opprK.
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
by apply: sepx.
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
rewrite -Hz ![Fadjoin (Fadjoin _ _) x]FadjoinC.
apply/eqP; rewrite /eq_op; apply/eqP.
apply: subv_anti.
apply/andP; split; rewrite -subsetFadjoinE subsetKFadjoin.
 by rewrite -separableCharn // Hsep.
by rewrite memv_exp ?memx_Fadjoin.
Qed.

Section SeparableAndInseparableExtensions.

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
apply: (@big_prop L (separableElement K)).
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
apply: (@big_prop L (purelyInseparableElement K)).
 apply/inseparableinK/mem0v.
apply: inseparable_add.
Qed.

Variable (E : {algebra L}).

Definition separable : bool :=
 all (separableElement K) (vbasis E).

Lemma separableP :
  reflect (forall y, y \in E -> separableElement K y)
          separable.
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

Definition purelyInseparable : bool :=
 all (purelyInseparableElement K) (vbasis E).

Lemma purelyInseparableP :
  reflect (forall y, y \in E -> purelyInseparableElement K y)
          purelyInseparable.
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

Lemma separableSeparableExtension : forall K x,
 separableElement K x -> separable K (Fadjoin K x).
Proof.
move => K x.
move/allSeparableElement => Hsep.
by apply/separableP.
Qed.

Lemma separableInseparableDecomposition_subproof :
 forall E K, exists x, [&& x \in E, separableElement K x & 
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
set (K' := foldr (fun x y => Fadjoin y x) K s).
have: exists x, [&& x \in E, separableElement K x & K' == Fadjoin K x].
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
  apply: mem0v.
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

Definition separableGenerator (K E:{algebra L}) : L:= 
  choice.xchoose (separableInseparableDecomposition_subproof E K).

Lemma separableGeneratorInE : forall E K, separableGenerator K E \in E.
Proof.
move => E K.
by case/and3P: (choice.xchooseP 
  (separableInseparableDecomposition_subproof E K)).
Qed.

Lemma separableGeneratorSep : forall E K, 
 separableElement K (separableGenerator K E).
Proof.
move => E K.
by case/and3P: (choice.xchooseP 
  (separableInseparableDecomposition_subproof E K)).
Qed.

Lemma separableGeneratorMaximal : forall E K, 
 purelyInseparable (Fadjoin K (separableGenerator K E)) E.
Proof.
move => E K.
by case/and3P: (choice.xchooseP 
  (separableInseparableDecomposition_subproof E K)).
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
 separable K E -> (K <= E)%VS -> E = Fadjoin K (separableGenerator K E).
Proof.
move => E K Hsep HKE.
apply/eqP; rewrite /eq_op; apply/eqP; apply: subv_anti.
rewrite separableSeparableGeneratorEx //=.
by rewrite -subsetFadjoinE HKE separableGeneratorInE.
Qed.

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
move/subvP => Hvs.
apply/subvP => x.
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
apply: subv_anti.
apply/andP.
split; first by apply: EigensubspaceImage.
move/subvP: Hvs => Hvs.
apply/subvP => x Hx.
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
apply/subvP => v _.
by rewrite EigenspaceIn unit_lappE GRing.scale1r.
Qed.

Lemma compAutomorphism : forall E f g, 
 FieldAutomorphism E f ->  FieldAutomorphism E g ->
 FieldAutomorphism E (f \o g)%VS.
Proof.
move => E f g Ff Fg.
case/and3P: (Ff); move/eqP => Hf1; move/subvP => Hf2; move/eqP => _.
case/and3P: (Fg); move/eqP => Hg1; move/subvP => Hg2; move/eqP => _.
apply/and3P; split; do 2? apply/allP => ? ?;
  rewrite ?limg_comp ?comp_lappE /= ?Hg1 ?Hf1 //.
  apply/subvP => v Hv.
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
case/and3P: (Ff); move/eqP => Hf1; move/subvP => Hf2; move/eqP => _.
have H1 : (inv_lapp f @v: E = E).
 apply/eqP.
 by rewrite -{1}Hf1 -limg_comp inv_lker0 ?kerf // lim1g.
apply/and3P; split.
- by rewrite H1.
- apply/subvP => v.
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
move/subvP => Hf _ HE.
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

End Separable.

