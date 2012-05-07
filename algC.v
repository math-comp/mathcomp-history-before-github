(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq choice div fintype.
Require Import bigop finset prime ssralg poly polydiv mxpoly generic_quotient.
Require Import countalg ssrnum ssrint rat intdiv.

(******************************************************************************)
(* This file provides an axiomatic construction of the algebraic numbers.     *)
(* The construction only assumes the existence of an algebraically closed     *)
(* filed with an automorphism of order 2; this amounts to the purely          *)
(* algebraic contents of the Fundamenta Theorem of Algebra.                   *)
(*       algC == the closed, countable field of algebraic numbers.            *)
(*        z^* == the complex conjugate of z (:= conjC z).                     *)
(*    sqrtC z == a nonnegative square root of z, i.e., 0 <= sqrt x if 0 <= x. *)
(* The ssrnum interfaces are implemented for algC as follows:                 *)
(*     x <= y <=> (y - x) is a nonnegative real                               *)
(*      x < y <=> (y - x) is a (strictly) positive real                       *)
(*       `|z| == the complex norm of z, i.e., sqrtC (z * z^* ).               *)
(*      Creal == the subset of real numbers (:= Num.real for algC).           *)
(* In addition, we provide:                                                   *)
(*         'i == the imaginary number (:= sqrtC (-1)).                        *)
(*      'Re z == the real component of z.                                     *)
(*      'Im z == the imaginary component of z.                                *)
(*       Crat == the subset of rational numbers.                              *)
(*       Cint == the subset of integers.                                      *)
(*       Cnat == the subset of natural integers.                              *)
(*  getCrat z == some a : rat such that ratr a = z, provided z \in Crat.      *)
(*   floorC z == for z \in Creal, an m : int s.t. m%:~R <= z < (m + 1)%:~R.   *)
(*  truncC z == for z >= 0, an n : nat s.t. n%:R <= z < n.+1%:R, else 0%N.   *)
(* minCpoly z == the minimal (monic) polynomial over Crat with root z.        *)
(* algC_invaut nu == an inverse of nu : {rmorphism algC -> algC}.             *)
(*         (x %| y)%C <=> y is an integer (Cint) multiple of x; if x or y are *)
(*        (x %| y)%Cx     of type nat or int they are coerced to algC here.   *)
(*                        The (x %| y)%Cx display form is a workaround for    *)
(*                        design limitations of the Coq Notation facilities.  *)
(* (x == y %[mod z])%C <=> x and y differ by an integer (Cint) multiple of z; *)
(*                as above, arguments of type nat or int are cast to algC.    *)
(* (x != y %[mod z])%C <=> x and y do not differ by an integer multiple of z. *)
(* Note that in file algnum we give an alternative definition of divisibility *)
(* based on algebraic integers, overloading the notation in the %A scope.     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(* The Num mixin for an algebraically closed field with an automorphism of    *)
(* order 2, making it into a field of complex numbers.                        *)
Lemma ComplexNumMixin (L : closedFieldType) (conj : {rmorphism L -> L}) :
    involutive conj -> ~ conj =1 id ->
  {numL | forall x : NumDomainType L numL, `|x| ^+ 2 = x * conj x}.
Proof.
move=> conjK conj_nt.
have nz2: 2%:R != 0 :> L.
  apply/eqP=> char2; apply: conj_nt => e; apply/eqP/idPn=> eJ.
  have opp_id x: - x = x :> L.
    by apply/esym/eqP; rewrite -addr_eq0 -mulr2n -mulr_natl char2 mul0r.
  have{char2} char2: 2 \in [char L] by exact/eqP.
  without loss{eJ} eJ: e / conj e = e + 1.
    move/(_ (e / (e + conj e))); apply.
    rewrite fmorph_div rmorphD conjK -{1}[conj e](addNKr e) mulrDl.
    by rewrite opp_id (addrC e) divff // addr_eq0 opp_id.
  pose a := e * conj e; have aJ: conj a = a by rewrite rmorphM conjK mulrC.
  have [w Dw] := @solve_monicpoly _ 2 (nth 0 [:: e * a; - 1]) isT.
  have{Dw} Dw: w ^+ 2 + w = e * a.
    by rewrite Dw !big_ord_recl big_ord0 /= mulr1 mulN1r addr0 subrK.
  pose b := w + conj w; have bJ: conj b = b by rewrite rmorphD conjK addrC.
  have Db2: b ^+ 2 + b = a.
    rewrite -Frobenius_autE // rmorphD addrACA Dw /= Frobenius_autE -rmorphX.
    by rewrite -rmorphD Dw rmorphM aJ eJ -mulrDl -{1}[e]opp_id addKr mul1r.
  have /eqP[] := oner_eq0 L; apply: (addrI b); rewrite addr0 -{2}bJ.
  have: (b + e) * (b + conj e) == 0.
    rewrite mulrDl 2!mulrDr -/a addrA addr_eq0 opp_id (mulrC e) -addrA.
    by rewrite -mulrDr eJ addrAC -{2}[e]opp_id subrr add0r mulr1 Db2.
  rewrite mulf_eq0 !addr_eq0 !opp_id => /pred2P[] -> //.
  by rewrite {2}eJ rmorphD rmorph1.
have mul2I: injective (fun z : L => z *+ 2).
  by move=> x y; rewrite /= -mulr_natl -(mulr_natl y) => /mulfI->.
pose sqrt x : L := sval (sig_eqW (@solve_monicpoly _ 2 (nth 0 [:: x]) isT)).
have sqrtK x: sqrt x ^+ 2 = x.
  rewrite /sqrt; case: sig_eqW => /= y ->.
  by rewrite !big_ord_recl big_ord0 /= mulr1 mul0r !addr0.
have sqrtE x y: y ^+ 2 = x -> {b : bool | y = (-1) ^+ b * sqrt x}.
  move=> Dx; exists (y != sqrt x); apply/eqP; rewrite mulr_sign if_neg.
  by case: ifPn => //; apply/implyP; rewrite implyNb -eqf_sqr Dx sqrtK.
pose i := sqrt (- 1).
have sqrMi x: (i * x) ^+ 2 = - x ^+ 2 by rewrite exprMn sqrtK mulN1r.
have iJ : conj i = - i.
  have /sqrtE[b]: conj i ^+ 2 = - 1 by rewrite -rmorphX sqrtK rmorphN1.
  rewrite mulr_sign -/i; case: b => // Ri.
  case: conj_nt => z; wlog zJ: z / conj z = - z.
    move/(_ (z - conj z)); rewrite !rmorphB conjK opprB => zJ.
    by apply/mul2I/(canRL (subrK _)); rewrite -addrA zJ // addrC subrK.
  have [-> | nz_z] := eqVneq z 0; first exact: rmorph0.
  have [u Ru [v Rv Dz]]:
    exists2 u, conj u = u & exists2 v, conj v = v & (u + z * v) ^+ 2 = z.
  - pose y := sqrt z; exists ((y + conj y) / 2%:R).
      by rewrite fmorph_div rmorphD conjK addrC rmorph_nat.
    exists ((y - conj y) / (z *+ 2)).
      rewrite fmorph_div rmorphMn zJ mulNrn invrN mulrN -mulNr rmorphB opprB.
      by rewrite conjK.
    rewrite -(mulr_natl z) invfM (mulrC z) !mulrA divfK // -mulrDl addrACA.
    by rewrite subrr addr0 -mulr2n -mulr_natr mulfK ?Neq0 ?sqrtK.
  suffices u0: u = 0 by rewrite -Dz u0 add0r rmorphX rmorphM Rv zJ mulNr sqrrN.
  suffices [b Du]: exists b : bool, u = (-1) ^+ b * i * z * v.
    apply: mul2I; rewrite mul0rn mulr2n -{2}Ru.
    by rewrite Du !rmorphM rmorph_sign Rv Ri zJ !mulrN mulNr subrr.
  have/eqP:= zJ; rewrite -addr_eq0 -{1 2}Dz rmorphX rmorphD rmorphM Ru Rv zJ.
  rewrite mulNr sqrrB sqrrD addrACA (addrACA (u ^+ 2)) addNr addr0 -!mulr2n.
  rewrite -mulrnDl -(mul0rn _ 2) (inj_eq mul2I) /= -[rhs in _ + rhs]opprK.
  rewrite -sqrMi subr_eq0 eqf_sqr -mulNr !mulrA.
  by case/pred2P=> ->; [exists false | exists true]; rewrite mulr_sign.
pose norm x := sqrt x * conj (sqrt x).
have normK x : norm x ^+ 2 = x * conj x by rewrite exprMn -rmorphX sqrtK.
have normE x y : y ^+ 2 = x -> norm x = y * conj y.
  rewrite /norm => /sqrtE[b /(canLR (signrMK b)) <-].
  by rewrite !rmorphM rmorph_sign mulrACA -mulrA signrMK.
have norm_eq0 x : norm x = 0 -> x = 0.
  by move/eqP; rewrite mulf_eq0 fmorph_eq0 -mulf_eq0 -expr2 sqrtK => /eqP.
have normM x y : norm (x * y) = norm x * norm y.
  by rewrite mulrACA -rmorphM; apply: normE; rewrite exprMn !sqrtK.
have normN x : norm (- x) = norm x.
  by rewrite -mulN1r normM {1}/norm iJ mulrN -expr2 sqrtK opprK mul1r.
pose le x y := norm (y - x) == y - x; pose lt x y := (y != x) && le x y.
have posE x: le 0 x = (norm x == x) by rewrite /le subr0.
have leB x y: le x y = le 0 (y - x) by rewrite posE.
have posP x : reflect (exists y, x = y * conj y) (le 0 x).
  rewrite posE; apply: (iffP eqP) => [Dx | [y {x}->]]; first by exists (sqrt x).
  by rewrite (normE _ _ (normK y)) rmorphM conjK (mulrC (conj _)) -expr2 normK.
have posJ x : le 0 x -> conj x = x.
  by case/posP=> {x}u ->; rewrite rmorphM conjK mulrC.
have pos_linear x y : le 0 x -> le 0 y -> le x y || le y x.
  move=> pos_x pos_y; rewrite leB -opprB orbC leB !posE normN -eqf_sqr.
  by rewrite normK rmorphB !posJ ?subrr.
have sposDl x y : lt 0 x -> le 0 y -> lt 0 (x + y).
  have sqrtJ z : le 0 z -> conj (sqrt z) = sqrt z.
    rewrite posE -{2}[z]sqrtK -subr_eq0 -mulrBr mulf_eq0 subr_eq0.
    by case/pred2P=> ->; rewrite ?rmorph0.
  case/andP=> nz_x /sqrtJ uJ /sqrtJ vJ. 
  set u := sqrt x in uJ; set v := sqrt y in vJ; pose w := u + i * v.
  have ->: x + y = w * conj w.
    rewrite rmorphD rmorphM iJ uJ vJ mulNr mulrC -subr_sqr sqrMi opprK.
    by rewrite !sqrtK.
  apply/andP; split; last by apply/posP; exists w.
  rewrite -normK expf_eq0 //=; apply: contraNneq nz_x => /norm_eq0 w0.
  rewrite -[x]sqrtK expf_eq0 /= -/u -(inj_eq mul2I) !mulr2n -{2}(rmorph0 conj).
  by rewrite -w0 rmorphD rmorphM iJ uJ vJ mulNr addrACA subrr addr0.
have sposD x y : lt 0 x -> lt 0 y -> lt 0 (x + y).
  by move=> x_gt0 /andP[_]; apply: sposDl.
have normD x y : le (norm (x + y)) (norm x + norm y).
  have sposM u v: lt 0 u -> le 0 (u * v) -> le 0 v.
    by rewrite /lt !posE normM andbC => /andP[/eqP-> /mulfI/inj_eq->].
  have posD u v: le 0 u -> le 0 v -> le 0 (u + v).
    have [-> | nz_u u_ge0 v_ge0] := eqVneq u 0; first by rewrite add0r.
    by have /andP[]: lt 0 (u + v) by rewrite sposDl // /lt nz_u.
  have le_sqr u v: conj u = u -> le 0 v -> le (u ^+ 2) (v ^+ 2) -> le u v.
    move=> Ru v_ge0; have [-> // | nz_u] := eqVneq u 0.
    have [u_gt0 | u_le0 _] := boolP (lt 0 u).    
      by rewrite leB (leB u) subr_sqr mulrC addrC; apply: sposM; apply: sposDl.
    rewrite leB posD // posE normN -addr_eq0; apply/eqP.
    rewrite /lt nz_u posE -subr_eq0 in u_le0; apply: (mulfI u_le0).
    by rewrite mulr0 -subr_sqr normK Ru subrr.
  have pos_norm z: le 0 (norm z) by apply/posP; exists (sqrt z).
  rewrite le_sqr ?posJ ?posD // sqrrD !normK -normM rmorphD mulrDl !mulrDr.
  rewrite addrA addrC !addrA -(addrC (y * conj y)) !addrA.
  move: (y * _ + _) => u; rewrite -!addrA leB opprD addrACA {u}subrr add0r -leB.
  rewrite {}le_sqr ?posD //.
    by rewrite rmorphD !rmorphM !conjK addrC mulrC (mulrC y).
  rewrite -mulr2n -mulr_natr exprMn normK -natrX mulr_natr sqrrD mulrACA.
  rewrite -rmorphM (mulrC y x) addrAC leB mulrnA mulr2n opprD addrACA.
  rewrite  subrr addr0 {2}(mulrC x) rmorphM mulrACA -opprB addrAC -sqrrB -sqrMi.
  apply/posP; exists (i * (x * conj y - y * conj x)); congr (_ * _).
  rewrite !(rmorphM, rmorphB) iJ !conjK mulNr -mulrN opprB.
  by rewrite (mulrC x) (mulrC y).
by exists (Num.Mixin normD sposD norm_eq0 pos_linear normM (rrefl _) (rrefl _)).
Qed.

(* A "purely algebraic" statement of th Fundamental Theorem of Algebra. *)
Axiom complex_closed_field_exists :
  {L : closedFieldType &
     {conj : {rmorphism L -> L} | involutive conj & ~ conj =1 id}}.

Module Algebraics.

Module Type Specification.

Parameter type : Type.

Parameter eqMixin : Equality.class_of type.
Canonical eqType := EqType type eqMixin.

Parameter choiceMixin : Choice.mixin_of type.
Canonical choiceType := ChoiceType type choiceMixin.

Parameter countMixin : Countable.mixin_of type.
Canonical countType := CountType type countMixin.

Parameter zmodMixin : GRing.Zmodule.mixin_of type.
Canonical zmodType := ZmodType type zmodMixin.
Canonical countZmodType := [countZmodType of type].

Parameter ringMixin : GRing.Ring.mixin_of zmodType.
Canonical ringType := RingType type ringMixin.
Canonical countRingType := [countRingType of type].

Parameter unitRingMixin : GRing.UnitRing.mixin_of ringType.
Canonical unitRingType := UnitRingType type unitRingMixin.

Axiom mulC : @commutative ringType ringType *%R.
Canonical comRingType := ComRingType type mulC.
Canonical comUnitRingType := [comUnitRingType of type].

Axiom idomainAxiom : GRing.IntegralDomain.axiom ringType.
Canonical idomainType := IdomainType type idomainAxiom.

Axiom fieldMixin : GRing.Field.mixin_of unitRingType.
Canonical fieldType := FieldType type fieldMixin.

Parameter decFieldMixin : GRing.DecidableField.mixin_of unitRingType.
Canonical decFieldType := DecFieldType type decFieldMixin.

Axiom closedFieldAxiom : GRing.ClosedField.axiom ringType.
Canonical closedFieldType := ClosedFieldType type closedFieldAxiom.

Parameter numMixin : Num.mixin_of ringType.
Canonical numDomainType := NumDomainType type numMixin.
Canonical numFieldType := [numFieldType of type].

Parameter conj : {rmorphism type -> type}.
Axiom conjK : involutive conj.
Axiom normK : forall x, `|x| ^+ 2 = x * conj x.

Axiom algebraic : integralRange (@ratr unitRingType).

End Specification.

Module Implementation : Specification.

Definition L := tag complex_closed_field_exists.

Definition conjL : {rmorphism L -> L} :=
  s2val (tagged complex_closed_field_exists).

Fact conjL_K : involutive conjL.
Proof. exact: s2valP (tagged complex_closed_field_exists). Qed.

Fact conjL_nt : ~ conjL =1 id.
Proof. exact: s2valP' (tagged complex_closed_field_exists). Qed.

Definition LnumMixin := ComplexNumMixin conjL_K conjL_nt.
Definition Lnum := NumDomainType L (sval LnumMixin).

Definition QtoL := [rmorphism of @ratr [numFieldType of Lnum]].
Notation pQtoL := (map_poly QtoL).

Definition rootQtoL p_j :=
  if p_j.1 == 0 then 0 else
  (sval (closed_field_poly_normal (pQtoL p_j.1)))`_p_j.2.

(* ?!!?! generic_quotient does not support quotient-by-projection ??!?! *)
Definition eq_root p_j q_k := rootQtoL p_j == rootQtoL q_k.
Fact eq_root_is_equiv : equiv_class_of eq_root.
Proof. by rewrite /eq_root; split=> // [? | ? ? ? /eqP->]. Qed.
Canonical eq_root_equiv := EquivRelPack eq_root_is_equiv.
Definition type : Type := {eq_quot eq_root}%qT.

Definition eqMixin : Equality.class_of type := EquivQuot.eqMixin _.
Canonical eqType := EqType type eqMixin.

Definition choiceMixin : Choice.mixin_of type := EquivQuot.choiceMixin _.
Canonical choiceType := ChoiceType type choiceMixin.

Definition countMixin : Countable.mixin_of type := CanCountMixin (@reprK _ _).
Canonical countType := CountType type countMixin.

Definition CtoL (u : type) := rootQtoL (repr u).

Fact CtoL_inj : injective CtoL.
Proof. by move=> u v /eqP eq_uv; rewrite -[u]reprK -[v]reprK; apply/eqmodP. Qed.

Fact CtoL_P u : integralOver QtoL (CtoL u).
Proof.
rewrite /CtoL /rootQtoL; case: (repr u) => p j /=.
case: (closed_field_poly_normal _) => r Dp /=.
case: ifPn => [_ | nz_p]; first exact: integral0.
have [/(nth_default 0)-> | lt_j_r] := leqP (size r) j; first exact: integral0.
apply/integral_algebraic; exists p; rewrite // Dp -mul_polyC rootM orbC.
by rewrite root_prod_XsubC mem_nth.
Qed.

Fact LtoC_subproof z : integralOver QtoL z -> {u | CtoL u = z}.
Proof.
case/sig2_eqW=> p mon_p pz0; rewrite /CtoL.
pose j := index z (sval (closed_field_poly_normal (pQtoL p))).
pose u := \pi_type%qT (p, j); exists u; have /eqmodP/eqP-> := reprK u.
rewrite /rootQtoL -if_neg monic_neq0 //; apply: nth_index => /=.
case: (closed_field_poly_normal _) => r /= Dp.
by rewrite Dp (monicP _) ?(monic_map QtoL) // scale1r root_prod_XsubC in pz0.
Qed.

Definition LtoC z Az := sval (@LtoC_subproof z Az).
Fact LtoC_K z Az : CtoL (@LtoC z Az) = z.
Proof. exact: (svalP (LtoC_subproof Az)). Qed.

Fact CtoL_K u : LtoC (CtoL_P u) = u.
Proof. by apply: CtoL_inj; rewrite LtoC_K. Qed.

Definition zero := LtoC (integral0 _).
Definition add u v := LtoC (integral_add (CtoL_P u) (CtoL_P v)).
Definition opp u := LtoC (integral_opp (CtoL_P u)).

Fact addA : associative add.
Proof. by move=> u v w; apply: CtoL_inj; rewrite !LtoC_K addrA. Qed.

Fact addC : commutative add.
Proof. by move=> u v; apply: CtoL_inj; rewrite !LtoC_K addrC. Qed.

Fact add0 : left_id zero add.
Proof. by move=> u; apply: CtoL_inj; rewrite !LtoC_K add0r. Qed.

Fact addN : left_inverse zero opp add.
Proof. by move=> u; apply: CtoL_inj; rewrite !LtoC_K addNr. Qed.

Definition zmodMixin := ZmodMixin addA addC add0 addN.
Canonical zmodType := ZmodType type zmodMixin.
Canonical countZmodType := [countZmodType of type].

Fact CtoL_is_additive : additive CtoL.
Proof. by move=> u v; rewrite !LtoC_K. Qed.
Canonical CtoL_additive := Additive CtoL_is_additive.

Definition one := LtoC (integral1 _).
Definition mul u v := LtoC (integral_mul (CtoL_P u) (CtoL_P v)).
Definition inv u := LtoC (integral_inv (CtoL_P u)).

Fact mulA : associative mul.
Proof. by move=> u v w; apply: CtoL_inj; rewrite !LtoC_K mulrA. Qed.

Fact mulC : commutative mul.
Proof. by move=> u v; apply: CtoL_inj; rewrite !LtoC_K mulrC. Qed.

Fact mul1 : left_id one mul.
Proof. by move=> u; apply: CtoL_inj; rewrite !LtoC_K mul1r. Qed.

Fact mulD : left_distributive mul +%R.
Proof. by move=> u v w; apply: CtoL_inj; rewrite !LtoC_K mulrDl. Qed.

Fact one_nz : one != 0 :> type.
Proof. by rewrite -(inj_eq CtoL_inj) !LtoC_K oner_eq0. Qed.

Definition ringMixin := ComRingMixin mulA mulC mul1 mulD one_nz.
Canonical ringType := RingType type ringMixin.
Canonical comRingType := ComRingType type mulC.
Canonical countRingType := [countRingType of type].

Fact CtoL_is_multiplicative : multiplicative CtoL.
Proof. by split=> [u v|]; rewrite !LtoC_K. Qed.
Canonical CtoL_rmorphism := AddRMorphism CtoL_is_multiplicative.

Fact mulVf : GRing.Field.axiom inv.
Proof.
move=> u; rewrite -(inj_eq CtoL_inj) rmorph0 => nz_u.
by apply: CtoL_inj; rewrite !LtoC_K mulVf.
Qed.
Fact inv0 : inv 0 = 0. Proof. by apply: CtoL_inj; rewrite !LtoC_K invr0. Qed.

Definition unitRingMixin := FieldUnitMixin mulVf inv0.
Canonical unitRingType := UnitRingType type unitRingMixin.
Canonical comUnitRingType := [comUnitRingType of type].

Definition fieldMixin := @FieldMixin _ _ mulVf inv0.
Definition idomainAxiom := FieldIdomainMixin fieldMixin.
Canonical idomainType := IdomainType type idomainAxiom.
Canonical fieldType := FieldType type fieldMixin.

Fact closedFieldAxiom : GRing.ClosedField.axiom ringType.
Proof.
move=> n a n_gt0; pose p := 'X^n - \poly_(i < n) CtoL (a i).
have Ap: {in p : seq L, integralRange QtoL}.
  move=> _ /(nthP 0)[j _ <-]; rewrite coefB coefXn coef_poly.
  apply: integral_sub; first exact: integral_nat.
  by case: ifP => _; [apply: CtoL_P | apply: integral0].
have sz_p: size p = n.+1.
  by rewrite size_addl size_polyXn // size_opp ltnS size_poly.
have [z pz0]: exists z, root p z by apply/closed_rootP; rewrite sz_p eqSS -lt0n.
have Az: integralOver ratr z.
  by apply: integral_root Ap; rewrite // -size_poly_gt0 sz_p.
exists (LtoC Az); apply/CtoL_inj; rewrite -[CtoL _]subr0 -(rootP pz0).
rewrite rmorphX /= LtoC_K hornerD hornerXn hornerN opprD addNKr opprK.
rewrite horner_poly rmorph_sum; apply: eq_bigr => k _.
by rewrite rmorphM rmorphX /= LtoC_K.
Qed.

Definition decFieldMixin := closed_field.closed_fields_QEMixin closedFieldAxiom.
Canonical decFieldType := DecFieldType type decFieldMixin.
Canonical closedFieldType := ClosedFieldType type closedFieldAxiom.

Fact conj_subproof u : integralOver QtoL (conjL (CtoL u)).
Proof.
have [p mon_p pu0] := CtoL_P u; exists p => //.
rewrite -(fmorph_root conjL) conjL_K map_poly_id // => _ /(nthP 0)[j _ <-].
by rewrite coef_map fmorph_rat.
Qed.
Fact conj_is_rmorphism : rmorphism (fun u => LtoC (conj_subproof u)).
Proof.
do 2?split=> [u v|]; apply: CtoL_inj; last by rewrite !LtoC_K rmorph1.
- by rewrite LtoC_K 3!{1}rmorphB /= !LtoC_K.
by rewrite LtoC_K 3!{1}rmorphM /= !LtoC_K.
Qed.
Definition conj : {rmorphism type -> type} := RMorphism conj_is_rmorphism.
Lemma conjK : involutive conj.
Proof. by move=> u; apply: CtoL_inj; rewrite !LtoC_K conjL_K. Qed.

Fact conj_nt : ~ conj =1 id.
Proof. 
have [i i2]: exists i : type, i ^+ 2 = -1.
  have [i] := @solve_monicpoly _ 2 (nth 0 [:: -1 : type]) isT.
  by rewrite !big_ord_recl big_ord0 /= mul0r mulr1 !addr0; exists i.
move/(_ i)/(congr1 CtoL); rewrite LtoC_K => iL_J.
have/ltr_geF/idP[] := @ltr01 Lnum; rewrite -oppr_ge0 -(rmorphN1 CtoL_rmorphism).
rewrite -i2 rmorphX /= expr2 -{2}iL_J -(svalP LnumMixin).
by rewrite exprn_ge0 ?normr_ge0.
Qed.

Definition numMixin := sval (ComplexNumMixin conjK conj_nt).
Canonical numDomainType := NumDomainType type numMixin.
Canonical numFieldType := [numFieldType of type].

Lemma normK u : `|u| ^+ 2 = u * conj u.
Proof. exact: svalP (ComplexNumMixin conjK conj_nt) u. Qed.

Lemma algebraic : integralRange (@ratr unitRingType).
Proof.
move=> u; have [p mon_p pu0] := CtoL_P u; exists p => {mon_p}//.
rewrite -(fmorph_root CtoL_rmorphism) -map_poly_comp; congr (root _ _): pu0.
by apply/esym/eq_map_poly; apply: fmorph_eq_rat.
Qed.

End Implementation.

Definition divisor := Implementation.type.

Module Internals.

Import Implementation.

Local Notation algC := type.
Local Notation QtoC := (ratr : rat -> algC).
Local Notation QtoCm := [rmorphism of QtoC].
Local Notation pQtoC := (map_poly QtoC).
Local Notation ZtoQ := (intr : int -> rat).
Local Notation ZtoC := (intr : int -> algC).
Local Notation Creal := (Num.real : qualifier 0 algC).

CoInductive sqrtC_spec (x : algC)  : Type :=
  SqrtCspec (y : algC) of y ^+ 2 = x & 0 <= x -> 0 <= y.

Fact sqrtC_subproof x : sqrtC_spec x.
Proof.
have /sig_eqW[y y2x] := solve_monicpoly (nth 0 [:: x]) (isT : 0 < 2)%N.
rewrite !big_ord_recl big_ord0 mulr1 mul0r !addr0 /= in y2x.
exists (if 0 <= x then `|y| else y) => [|->]; last exact: normr_ge0.
by case: ifP => // x_ge0; rewrite -normrX y2x ger0_norm.
Qed.

CoInductive getCrat_spec : Type := GetCrat_spec CtoQ of cancel QtoC CtoQ.

(* Reconstructed rational subring. *)
(* Note that this proof is tweaked so that it depends only on the fact that *)
(* QtoC is a field embedding, and not on the order structure assumed for C. *)
(* Thus, it could be used in (and moved to) the construction of C.          *)
Fact getCrat_subproof : getCrat_spec.
Proof.
have QtoCinj: injective QtoC by exact: fmorph_inj.
have ZtoQinj: injective ZtoQ by exact: intr_inj.
have defZtoC: ZtoC =1 QtoC \o ZtoQ by move=> m; rewrite /= rmorph_int.
suffices CtoQ x: {xa : seq rat | forall a, x = QtoC a -> a \in xa}.
  exists (fun x => let: exist xa _ := CtoQ x in xa`_(index x (map QtoC xa))).
  move=> a /=; case: (CtoQ _) => xa /= /(_ a (erefl _)) xa_a; apply: QtoCinj.
  by rewrite -(nth_map _ 0) ?nth_index -?(size_map QtoC) ?index_mem ?map_f.
have [-> | nz_x] := eqVneq x 0.
  by exists [:: 0] => a; rewrite inE -(inj_eq QtoCinj) rmorph0 => <-.
have /sig2_eqW[q mon_q qx0] := algebraic x.
have [p [a nz_a Dq]] := rat_poly_scale q.
have{mon_q} Da: lead_coef p = a.
  apply: ZtoQinj; rewrite -{2}(monicP mon_q) Dq lead_coefZ.
  rewrite -(mulrzr _ a) (mulrC _^-1) divfK ?intr_eq0 //.
  by rewrite !lead_coefE size_rat_int_poly coef_map.
have{q Dq qx0} px0: root (map_poly ZtoC p) x.
  rewrite Dq map_polyZ -map_poly_comp -(eq_map_poly defZtoC) rootZ // in qx0.
  by rewrite fmorph_eq0 invr_eq0 intr_eq0.  
without loss{nz_x} nz_p0: p Da px0 / p`_0 != 0.
  move=> IH; elim/poly_ind: p => [| p c IHp] in Da px0.
    by rewrite -Da lead_coef_eq0 eqxx in nz_a.
  have [c0 | nz_c] := eqVneq c 0; last first.
    by apply: IH Da px0 _; rewrite coefD coefC coefMX add0r.
  rewrite c0 addr0 lead_coefM lead_coefX mulr1 mulrC rmorphM /= in Da px0.
  by apply: IHp Da _; rewrite rootM map_polyX rootX (negPf nz_x) in px0.
pose q e m := ZtoQ ((-1) ^+ e * m%:Z) / ZtoQ a.
exists [seq q e m | e <- iota 0 2, m <- divisors `|a * p`_0|] => y Dx.
rewrite {x}Dx (eq_map_poly defZtoC) map_poly_comp fmorph_root /root in px0.
have [n Dn]: {n | size p = n.+2}.
  exists (size p - 2)%N; rewrite -addn2 subnK //.
  rewrite -size_rat_int_poly (root_size_gt1 _ px0) // -size_poly_eq0.
  by rewrite size_rat_int_poly size_poly_eq0 -lead_coef_eq0 Da.
pose m := numq y; pose d := denq y.
have co_md: coprimez m d by exact: coprime_num_den.
have{px0} [c /eqP Dc]: {c | a * m ^+ n.+1 + p`_0 * d ^+ n.+1 == c * m * d}.
  exists (- \sum_(i < n) p`_i.+1 * m ^+ i * d ^+ (n - i.+1)).
  rewrite -mulrA mulNr mulr_suml -addr_eq0 -addrA addrC; apply/eqP/ZtoQinj.
  rewrite raddf0 -(mul0r (ZtoQ d ^+ n.+1)) -(rootP px0).
  rewrite horner_coef mulr_suml size_rat_int_poly Dn big_ord_recr big_ord_recl.
  rewrite lead_coefE Dn in Da; rewrite !coef_map {}Da !raddfD raddf_sum mulr1.
  rewrite -rmorphX -rmorphM; congr (_ + _ + _); last first.
    by rewrite rmorphX -mulrA -exprMn -numqE -rmorphX -rmorphM.
  apply: eq_bigr => k _; rewrite coef_map; move: (nth 0 p) => p_ /=.
  rewrite !rmorphM !rmorphX /= numqE exprMn -/d -!mulrA; congr (_ * _).
  rewrite -!(mulrCA y) mulrA -exprS -expr2 -!exprD; congr (_ * _ ^+ _).
  by rewrite addnCA addn2 addnS subnK.
have dv_d_a: (d %| a)%Z.
  rewrite -(@Gauss_dvdzl _ _ (m ^+ n.+1)) 1?coprimez_sym ?coprimez_expl //.
  by rewrite (canRL (addrK _) Dc) exprSr !mulrA -mulrBl dvdz_mull.
have dv_m_p0: (m %| p`_0)%Z.
  rewrite -(@Gauss_dvdzl _ _ (d ^+ n.+1)) ?coprimez_expr //.
  by rewrite (canRL (addKr _) Dc) addrC mulrAC exprSr mulrA -mulrBl dvdz_mull.
pose ma := (a %/ d)%Z * m; apply/allpairsP; exists (ma < 0 : nat, `|ma|%N).
rewrite mem_iota ltnS leq_b1 -dvdn_divisors ?absz_gt0 ?mulf_neq0 //.
rewrite /q -intEsign -dvdzE rmorphM dvdz_mul //= ?numqE -/d.
  by rewrite mulrCA -rmorphM divzK ?mulfK ?intr_eq0.
by apply/dvdzP; exists d; rewrite mulrC divzK.
Qed.

Fact floorC_subproof x : {m | x \is Creal -> ZtoC m <= x < ZtoC (m + 1)}.
Proof.
have [Rx | _] := boolP (x \is Creal); last by exists 0.
without loss x_ge0: x Rx / x >= 0.
  have [x_ge0 | /ltrW x_le0] := real_ger0P Rx; first exact.
  case/(_ (- x)) => [||m /(_ isT)]; rewrite ?rpredN ?oppr_ge0 //.
  rewrite ler_oppr ltr_oppl -!rmorphN opprD /= ltr_neqAle ler_eqVlt.
  case: eqP => [-> _ | _ /and3P[lt_x_m _ le_m_x]].
    by exists (- m) => _; rewrite lerr rmorphD ltr_addl ltr01.
  by exists (- m - 1); rewrite le_m_x subrK.
suffices /ex_minnP[n lt_x_n1 min_n]: exists n, x < n.+1%:R.
  exists n%:Z => _; rewrite addrC -intS lt_x_n1 andbT.
  case Dn: n => // [n1]; rewrite -Dn.
  have [||//|] := @real_lerP _ n%:R x; rewrite ?rpred_nat //.
  by rewrite Dn => /min_n; rewrite Dn ltnn.
suffices [n x_le_n]: exists n, x <= n%:R.
  by exists n; rewrite (ler_lt_trans x_le_n) ?ltr_nat.
have [||| x_gt1] := @real_lerP _ x 1; rewrite ?rpred1 //; first by exists 1%N.
have [p mon_p px0] := algebraic x; have nz_p: p != 0 := monic_neq0 mon_p.
pose n := (size p).-2; have Dn: n.+2 = size p.
  rewrite /n -subn2 -addn2 subnK // -(size_map_poly QtoCm).
  by rewrite (root_size_gt1 _ px0) // map_poly_eq0.
have xk_gt0 k: 0 < x ^+ k by rewrite exprn_gt0 // (ltr_trans ltr01).
exists (\sum_(i < n.+1) `|numq p`_i|)%N.
have ->: x = QtoC (lead_coef p) * x by rewrite (monicP mon_p) rmorph1 mul1r.
rewrite -[_ * x]subr0 -(ler_pmul2r (xk_gt0 n)) mulrBl mul0r -mulrA -exprS.
rewrite -(eqP px0) horner_coef size_map_poly lead_coefE -Dn.
rewrite big_ord_recr opprD addrC coef_map subrK -sumrN /= natr_sum mulr_suml.
apply: ler_sum => k _; rewrite coef_map -mulNr -rmorphN /=.
apply: (@ler_trans _ (`|numq p`_k|%:~R * x ^+ k)); last first.
  by rewrite -abszE ler_wpmul2l ?ler0n // ler_eexpn2l ?leq_ord.
rewrite ler_pmul2r // -(rmorph_int QtoCm) -normr_int ler_rat numqE normrM.
apply: ler_trans (real_ler_norm (num_real _)) _.
by rewrite normrN ler_pemulr ?normr_ge0 // normr_int ler1n absz_gt0.
Qed.

Fact minCpoly_subproof (x : algC) :
  {p | p \is monic & forall q, root (pQtoC q) x = (p %| q)}.
Proof.
have /sig2_eqW[p0 mon_p0 p0x] := algebraic x.
have [r Dp0] := closed_field_poly_normal (map_poly QtoC p0).
rewrite (monicP _) ?monic_map {mon_p0}// scale1r in Dp0.
have r_x: x \in r by rewrite Dp0 root_prod_XsubC in p0x.
pose p_ (I : {set 'I_(size r)}) := \prod_(i <- enum I) ('X - (r`_i)%:P).
have [CtoQ QtoC_K] := getCrat_subproof.
pose Crat : pred type := fun z => QtoC (CtoQ z) == z.
pose Qpx I := root (p_ I) x && (p_ I \is a polyOver Crat).
have{p0 p0x Dp0} /minset_exists[I /minsetP[]]: Qpx setT.
  rewrite /Qpx; have ->: p_ setT = pQtoC p0.
     rewrite Dp0 (big_nth 0) big_mkord /p_ big_filter /=.
     by apply: eq_bigl => i; rewrite inE.
   rewrite p0x; apply/(all_nthP 0) => i _ /=.
   by rewrite coef_map unfold_in QtoC_K.
case/andP=> pIx QpI minI _; pose p := map_poly CtoQ (p_ I).
have DpI: p_ I = pQtoC p.
  rewrite -[p_ I]coefK; apply/polyP=> i; rewrite -map_poly_comp !coef_poly.
  by case: ifP => //= lti_pI; apply/esym/eqP/(allP QpI)/mem_nth.
exists p => [|q]; first by rewrite -(map_monic QtoCm) -DpI monic_prod_XsubC.
apply/idP/idP=> [qx0 | /dvdpP[{q} q ->]]; last first.
  by rewrite rmorphM rootM /= -DpI pIx orbT.
pose q1 := gcdp p q; have /dvdp_prod_XsubC[m Dq1]: pQtoC q1 %| p_ I.
  by rewrite gcdp_map DpI dvdp_gcdl.
pose B := [set i \in mask m (enum I)].
have{Dq1} Dq1: pQtoC q1 %= p_ B.
  congr (_ %= _): Dq1; apply: eq_big_perm.
  by rewrite uniq_perm_eq ?mask_uniq ?enum_uniq // => i; rewrite mem_enum inE.
rewrite -(dvdp_map QtoCm) -DpI -(minI B); last 1 first.
- by apply/subsetP=> i; rewrite inE => /mem_mask; rewrite mem_enum.
- by rewrite -(eqp_dvdl _ Dq1) gcdp_map dvdp_gcdr.
rewrite /Qpx -(eqp_root Dq1) gcdp_map root_gcd qx0 -DpI pIx.
have{Dq1} /eqpP[[d1 d2] /= /andP[nz_d1 nz_d2] Dq1] := Dq1.
rewrite -[p_ B](scalerK nz_d2) -Dq1 scalerA mulrC.
have ->: d1 / d2 = (QtoC (lead_coef q1))^-1.
  have /esym := congr1 lead_coef Dq1; rewrite !lead_coefZ lead_coef_map.
  by rewrite (monicP _) ?monic_prod_XsubC // mulr1 => ->; rewrite invfM mulVKf.
apply/(all_nthP 0)=> i _; rewrite coefZ coef_map mulrC /=.
by rewrite -fmorph_div unfold_in QtoC_K.
Qed.

Definition algC_divisor (x : algC) := x : divisor.
Definition int_divisor m := m%:~R : divisor.
Definition nat_divisor n := n%:R : divisor.

End Internals.

Module Import Exports.

Import Implementation Internals.

Notation algC := type.
Notation conjC := conj.
Delimit Scope C_scope with C.
Delimit Scope C_core_scope with Cc.
Delimit Scope C_expanded_scope with Cx.
Open Scope C_core_scope.
Notation "x ^*" := (conjC x) (at level 2, format "x ^*") : C_core_scope.
Notation "x ^*" := x^* (only parsing) : C_scope.

Canonical eqType.
Canonical choiceType.
Canonical countType.
Canonical zmodType.
Canonical countZmodType.
Canonical ringType.
Canonical countRingType.
Canonical unitRingType.
Canonical comRingType.
Canonical comUnitRingType.
Canonical idomainType.
Canonical numDomainType.
Canonical fieldType.
Canonical numFieldType.
Canonical decFieldType.
Canonical closedFieldType.

Definition sqrtC x := let: SqrtCspec y _ _ := sqrtC_subproof x in y.

Definition algCi := sqrtC (-1).
Notation "'i" := algCi (at level 0) : C_core_scope.
Notation "'i" := 'i (only parsing) : C_scope.

Definition algRe x := (x + x^*) / 2%:R.
Definition algIm x := (x - x^*) / ('i *+ 2).
Notation "'Re z" := (algRe z) (at level 10, z at level 8) : C_core_scope.
Notation "'Im z" := (algIm z) (at level 10, z at level 8) : C_core_scope.
Notation "'Re z" := ('Re z) (only parsing) : C_scope.
Notation "'Im z" := ('Im z) (only parsing) : C_scope.

Notation Creal := (@Num.Def.Rreal numDomainType).

Definition getCrat := let: GetCrat_spec CtoQ _ := getCrat_subproof in CtoQ.
Definition Crat : pred_class := fun x : algC => ratr (getCrat x) == x.

Definition floorC x := sval (floorC_subproof x).
Definition Cint : pred_class := fun x : algC => (floorC x)%:~R == x.

Definition truncC x := if x >= 0 then `|floorC x|%N else 0%N.
Definition Cnat : pred_class := fun x : algC => (truncC x)%:R == x.

Definition minCpoly x : {poly algC} :=
  let: exist2 p _ _ := minCpoly_subproof x in map_poly ratr p.

Coercion algC_divisor : algC >-> divisor.
Coercion int_divisor : int >-> divisor.
Coercion nat_divisor : nat >-> divisor.

Lemma nCdivE (p : nat) : p = p%:R :> divisor. Proof. by []. Qed.
Lemma zCdivE (p : int) : p = p%:~R :> divisor. Proof. by []. Qed.
Definition CdivE := (nCdivE, zCdivE).

Definition dvdC (x : divisor) : pred_class :=
   fun y : algC => if x == 0 then y == 0 else y / x \in Cint.
Notation "x %| y" := (y \in dvdC x) : C_expanded_scope.
Notation "x %| y" := (@in_mem divisor y (mem (dvdC x))) : C_scope.

Definition eqCmod (e x y : divisor) := (e %| x - y)%C.

Notation "x == y %[mod e ]" := (eqCmod e x y) : C_scope.
Notation "x != y %[mod e ]" := (~~ (x == y %[mod e])%C) : C_scope.

End Exports.

End Algebraics.

Export Algebraics.Exports.

Section AlgebraicsTheory.

Implicit Types (x y z : algC) (n : nat) (m : int) (b : bool).
Import Algebraics.Internals.

Local Notation ZtoQ := (intr : int -> rat).
Local Notation ZtoC := (intr : int -> algC).
Local Notation QtoC := (ratr : rat -> algC).
Local Notation QtoCm := [rmorphism of QtoC].
Local Notation CtoQ := getCrat.
Local Notation CtoN := truncC.
Local Notation intrp := (map_poly intr).
Local Notation pZtoQ := (map_poly ZtoQ).
Local Notation pZtoC := (map_poly ZtoC).
Local Notation pQtoC := (map_poly ratr).
Local Hint Resolve (@intr_inj _ : injective ZtoC).

(* Sepcialization of a few basic ssrnum order lemmas. *)

Definition eqC_nat n p : (n%:R == p%:R :> algC) = (n == p) := eqr_nat _ n p.
Definition leC_nat n p : (n%:R <= p%:R :> algC) = (n <= p)%N := ler_nat _ n p.
Definition ltC_nat n p : (n%:R < p%:R :> algC) = (n < p)%N := ltr_nat _ n p.
Definition Cchar : [char algC] =i pred0 := @char_num _.

Let nz2 : 2%:R != 0 :> algC. Proof. by rewrite pnatr_eq0. Qed.

(* Conjugation and norm. *)

Definition conjCK : involutive conjC := Algebraics.Implementation.conjK.
Definition normCK x : `|x| ^+ 2 = x * x^* := Algebraics.Implementation.normK x.
Definition algC_algebraic x := Algebraics.Implementation.algebraic x.

Lemma mul_conjC_ge0 x : 0 <= x * x^*.
Proof. by rewrite -normCK exprn_ge0 ?normr_ge0. Qed.

Lemma mul_conjC_gt0 x : (0 < x * x^*) = (x != 0).
Proof. 
have [->|x_neq0] := altP eqP; first by rewrite rmorph0 mulr0.
by rewrite -normCK exprn_gt0 ?normr_gt0.
Qed.

Lemma mul_conjC_eq0 x : (x * x^* == 0) = (x == 0).
Proof. by rewrite -normCK expf_eq0 normr_eq0. Qed.

Lemma conjC_ge0 x : (0 <= x^*) = (0 <= x).
Proof.
wlog suffices: x / 0 <= x -> 0 <= x^*.
  by move=> IH; apply/idP/idP=> /IH; rewrite ?conjCK.
rewrite le0r => /predU1P[-> | x_gt0]; first by rewrite rmorph0.
by rewrite -(pmulr_rge0 _ x_gt0) mul_conjC_ge0.
Qed.

Lemma conjC_nat n : (n%:R)^* = n%:R. Proof. exact: rmorph_nat. Qed.
Lemma conjC0 : 0^* = 0. Proof. exact: rmorph0. Qed.
Lemma conjC1 : 1^* = 1. Proof. exact: rmorph1. Qed.
Lemma conjC_eq0 x : (x^* == 0) = (x == 0). Proof. exact: fmorph_eq0. Qed.

Lemma invC_norm x : x^-1 = `|x| ^- 2 * x^*.
Proof.
have [-> | nx_x] := eqVneq x 0; first by rewrite conjC0 mulr0 invr0.
by rewrite normCK invfM divfK ?conjC_eq0.
Qed.

(* Square root. *)

Lemma sqrtCK x : sqrtC x ^+ 2 = x.
Proof. by rewrite /sqrtC; case: (sqrtC_subproof x). Qed.

Lemma sqrtC_ge0 x : (0 <= sqrtC x) = (0 <= x).
Proof.
apply/idP/idP=> x_ge0; first by rewrite -[x]sqrtCK exprn_ge0.
by rewrite /sqrtC; case: (sqrtC_subproof x) => y _ ->.
Qed.

Lemma sqrtC_lt0 x : (sqrtC x < 0) = false.
Proof.
apply/idP=> x2_lt0; have /idP[] := ltr_geF x2_lt0; rewrite sqrtC_ge0.
by rewrite -[x]sqrtCK -sqrrN exprn_ge0 // oppr_ge0 ltrW.
Qed.

Lemma sqrCK x : 0 <= x -> sqrtC (x ^+ 2) = x.
Proof.
move=> x_ge0; have /eqP := sqrtCK (x ^+ 2); rewrite eqf_sqr => /pred2P[] // Dx.
by rewrite Dx (@ler_anti _ x 0) ?oppr0 // -oppr_ge0 -Dx sqrtC_ge0 exprn_ge0.
Qed.

Lemma sqrtC0 : sqrtC 0 = 0. Proof. by rewrite -{1}(mulr0 0) sqrCK. Qed.
Lemma sqrtC1 : sqrtC 1 = 1. Proof. by rewrite -{1}[1]mul1r sqrCK ?ler01. Qed.

Lemma sqrtC_eq0 x : (sqrtC x == 0) = (x == 0).
Proof.
apply/eqP/eqP=> [|->]; last exact: sqrtC0.
by rewrite -{2}[x]sqrtCK => ->; rewrite exprS mul0r.
Qed.

Lemma sqrtC_le0 x : (sqrtC x <= 0) = (x == 0).
Proof. by rewrite ler_eqVlt sqrtC_lt0 sqrtC_eq0 orbF. Qed.

Lemma normC_def x : `|x| = sqrtC (x * x^*).
Proof. by rewrite -normCK sqrCK ?normr_ge0. Qed.

Lemma norm_conjC x : `|x^*| = `|x|.
Proof. by rewrite !normC_def conjCK mulrC. Qed.

(* Real number subset. *)

Lemma CrealE x : (x \is Creal) = (x^* == x).
Proof.
rewrite realEsqr ger0_def normrX normCK.
by have [-> | /mulfI/inj_eq-> //] := eqVneq x 0; rewrite rmorph0 !eqxx.
Qed.

Lemma CrealP {x} : reflect (x^* = x) (x \is Creal).
Proof. by rewrite CrealE; apply: eqP. Qed.

Lemma conj_Creal x : x \is Creal -> x^* = x.
Proof. by move/CrealP. Qed.

Lemma conj_normC z : `|z|^* = `|z|.
Proof. by rewrite conj_Creal ?normr_real. Qed.

Lemma geC0_conj x : 0 <= x -> x^* = x.
Proof. by move=> /ger0_real/CrealP. Qed.

Lemma geC0_unit_exp x n : 0 <= x -> (x ^+ n.+1 == 1) = (x == 1).
Proof. by move=> x_ge0; rewrite pexpr_eq1. Qed.

(* Norm sum (in)equalities. *)

Lemma normC_add_eq x y :
    `|x + y| = `|x| + `|y| ->
  {k : algC | `|k| == 1 & (x, y) = (`|x| * k, `|y| * k)}.
Proof.
move=> lin_xy; apply: sig2_eqW; pose u z := if z == 0 then 1 else z / `|z|.
have uE z: (`|u z| = 1) * (`|z| * u z = z).
  rewrite /u; have [->|nz_z] := altP eqP; first by rewrite normr0 normr1 mul0r.
  by rewrite normf_div normr_id mulrCA divff ?mulr1 ?normr_eq0.
have [->|nz_x] := eqVneq x 0; first by exists (u y); rewrite uE ?normr0 ?mul0r.
exists (u x); rewrite uE // /u (negPf nz_x); congr (_ , _).
have{lin_xy} def2xy: `|x| * `|y| *+ 2 = x * y ^* + y * x ^*.
  apply/(addrI (x * x^*))/(addIr (y * y^*)); rewrite -2!{1}normCK -sqrrD.
  by rewrite addrA -addrA -!mulrDr -mulrDl -rmorphD -normCK lin_xy.
have def_xy: x * y ^* = y * x^*.
  apply/eqP; rewrite -subr_eq0 -[_ == 0](@expf_eq0 _ _ 2).
  rewrite (canRL (subrK _) (subr_sqrDB _ _)) opprK -def2xy exprMn_n exprMn.
  by rewrite mulrN mulrAC mulrA -mulrA mulrACA -!normCK mulNrn addNr.
have{def_xy def2xy} def_yx: `|y * x| = y * x^*.
  by apply: (mulIf nz2); rewrite !mulr_natr mulrC normrM def2xy def_xy.
rewrite -{1}(divfK nz_x y) invC_norm mulrCA -{}def_yx !normrM invfM.
by rewrite mulrCA divfK ?normr_eq0 // mulrAC mulrA.
Qed.

Lemma normC_sum_eq (I : finType) (P : pred I) (F : I -> algC) :
     `|\sum_(i | P i) F i| = \sum_(i | P i) `|F i| ->
   {k : algC | `|k| == 1 & forall i, P i -> F i = `|F i| * k}.
Proof.
have [i /andP[Pi nzFi] | F0] := pickP [pred i | P i && (F i != 0)]; last first.
  exists 1 => [|i Pi]; first by rewrite normr1.
  by case/nandP: (F0 i) => [/negP[]// | /negbNE/eqP->]; rewrite normr0 mul0r.
rewrite !(bigD1 i Pi) /=; set Q := fun _ => _ : bool => norm_sumF.
rewrite -normr_eq0 in nzFi; set c := F i / `|F i|; exists c => [|j Pj].
  by rewrite normrM normfV normr_id divff.
have [Qj | /nandP[/negP[]// | /negbNE/eqP->]] := boolP (Q j); last first.
  by rewrite mulrC divfK.
have: `|F i + F j| = `|F i| + `|F j|.
  do [rewrite !(bigD1 j Qj) /=; set z := \sum_(k | _) `|_|] in norm_sumF.
  apply/eqP; rewrite eqr_le ler_norm_add -(ler_add2r z) -addrA -norm_sumF addrA.
  by rewrite (ler_trans (ler_norm_add _ _)) // ler_add2l ler_norm_sum.
by case/normC_add_eq=> k _ [/(canLR (mulKf nzFi)) <-]; rewrite -(mulrC (F i)).
Qed.

Lemma normC_sum_eq1 (I : finType) (P : pred I) (F : I -> algC) :
    `|\sum_(i | P i) F i| = (\sum_(i | P i) `|F i|) ->
     (forall i, P i -> `|F i| = 1) ->
   {k : algC | `|k| == 1 & forall i, P i -> F i = k}.
Proof.
case/normC_sum_eq=> k k1 defF normF.
by exists k => // i Pi; rewrite defF // normF // mul1r.
Qed.

Lemma normC_sum_upper (I : finType) (P : pred I) (F G : I -> algC) :
     (forall i, P i -> `|F i| <= G i) ->
     \sum_(i | P i) F i = \sum_(i | P i) G i ->
   forall i, P i -> F i = G i.
Proof.
set sumF := \sum_(i | _) _; set sumG := \sum_(i | _) _ => leFG eq_sumFG.
have posG i: P i -> 0 <= G i by move/leFG; apply: ler_trans; exact: normr_ge0.
have norm_sumG: `|sumG| = sumG by rewrite ger0_norm ?sumr_ge0.
have norm_sumF: `|sumF| = \sum_(i | P i) `|F i|.
  apply/eqP; rewrite eqr_le ler_norm_sum eq_sumFG norm_sumG -subr_ge0 -sumrB.
  by rewrite sumr_ge0 // => i Pi; rewrite subr_ge0 ?leFG.
have [k _ defF] := normC_sum_eq norm_sumF.
have [/(psumr_eq0P posG) G0 i Pi | nz_sumG] := eqVneq sumG 0.
  by apply/eqP; rewrite G0 // -normr_eq0 eqr_le normr_ge0 -(G0 i Pi) leFG.
have k1: k = 1.
  apply: (mulfI nz_sumG); rewrite mulr1 -{1}norm_sumG -eq_sumFG norm_sumF.
  by rewrite mulr_suml -(eq_bigr _ defF).
have /psumr_eq0P eqFG i : P i -> 0 <= G i - F i.
  by move=> Pi; rewrite subr_ge0 defF // k1 mulr1 leFG.
move=> i /eqFG/(canRL (subrK _))->; rewrite ?add0r //.
by rewrite sumrB -/sumF eq_sumFG subrr.
Qed.

(* Rectangular coordinates. *)

Lemma sqr_algCi : 'i ^+ 2 = -1. Proof. exact: sqrtCK. Qed.

Lemma algCi_nonReal : 'i \isn't Creal.
Proof. by rewrite realEsqr sqr_algCi oppr_ge0 ltr_geF ?ltr01. Qed.

Lemma algCi_neq0 : 'i != 0.
Proof. by apply: contraNneq algCi_nonReal => ->; apply: real0. Qed.

Lemma normCi : `|'i| = 1.
Proof.
apply/eqP; rewrite -(@pexpr_eq1 _ _ 2) ?normr_ge0 //.
by rewrite -normrX sqr_algCi normrN1.
Qed.

Lemma invCi : 'i^-1 = - 'i.
Proof. by rewrite -div1r -[1]opprK -sqr_algCi mulNr mulfK ?algCi_neq0. Qed.

Lemma conjCi : 'i^* = - 'i.
Proof. by rewrite -invCi invC_norm normCi expr1n invr1 mul1r. Qed.

Lemma algCrect x : x = 'Re x + 'i * 'Im x.
Proof. 
rewrite mulrCA -mulr_natr invfM mulVKf ?algCi_neq0 // -mulrDl addrACA subrr.
by rewrite addr0 -mulr2n -mulr_natr mulfK.
Qed.

Lemma Creal_Re x : 'Re x \is Creal.
Proof. by rewrite CrealE fmorph_div rmorph_nat rmorphD conjCK addrC. Qed.

Lemma Creal_Im x : 'Im x \is Creal.
Proof.
rewrite CrealE fmorph_div rmorphMn conjCi mulNrn invrN mulrN -mulNr.
by rewrite rmorphB conjCK opprB.
Qed.

Lemma algRe_rect : {in Creal &, forall x y, 'Re (x + 'i * y) = x}.
Proof.
move=> x y Rx Ry; rewrite /algRe rmorphD addrCA !addrA rmorphM conjCi mulNr.
by rewrite !conj_Creal // addrK -mulr2n -(mulr_natr x) mulfK.
Qed.

Lemma algIm_rect x y : x \is Creal -> y \is Creal -> 'Im (x + 'i * y) = y.
Proof.
move=> Rx Ry; rewrite /algIm rmorphD opprD addrACA rmorphM conjCi mulNr opprK.
rewrite !conj_Creal // subrr add0r -mulr2n -mulrnAl mulrC mulKf //.
by rewrite -mulr_natr mulf_neq0 ?algCi_neq0.
Qed.

Lemma normC_rect x y :
  x \is Creal -> y \is Creal -> `|x + 'i * y| = sqrtC (x ^+ 2 + y ^+ 2).
Proof.
move=> Rx Ry; rewrite normC_def rmorphD rmorphM conjCi !conj_Creal //.
by rewrite mulrC mulNr -subr_sqr exprMn sqr_algCi mulN1r opprK.
Qed.

(* Natural integer subset. *)

Lemma truncC_def x (n := CtoN x) :
  if 0 <= x then (n%:R <= x < n.+1%:R) else n == 0%N.
Proof.
rewrite /n /truncC; case: {-}_ / ifPn => [le0x | //].
rewrite /floorC; case: (Algebraics.Internals.floorC_subproof x) => m /=.
move/(_ (ger0_real le0x)); case: m => m; first by rewrite addrC -intS.
by rewrite andbC ler_gtF // (ler_trans _ le0x) // lerz0 addrC NegzE subr_le0.
Qed.

Lemma natCK n : CtoN n%:R = n.
Proof.
by have:= truncC_def n%:R; rewrite /= ler0n ler_nat ltr_nat => /anti_leq.
Qed.

Lemma truncCK : {in Cnat, cancel CtoN (GRing.natmul 1)}.
Proof. by move=> x /eqP. Qed.

Lemma CnatP x : reflect (exists n, x = n%:R) (x \in Cnat).
Proof.
by apply: (iffP eqP) => [<- | [n ->]]; [exists (truncC x) | rewrite natCK].
Qed.

Lemma rpred_Cnat S (ringS : semiringPred S) (kS : keyed_pred ringS) x :
  x \in Cnat -> x \in kS.
Proof. by case/CnatP=> n ->; apply: rpred_nat. Qed.

Lemma Cnat_nat n : n%:R \in Cnat. Proof. by apply/CnatP; exists n. Qed.
Lemma Cnat0 : 0 \in Cnat. Proof. exact: (Cnat_nat 0). Qed.
Lemma Cnat1 : 1 \in Cnat. Proof. exact: (Cnat_nat 1). Qed.
Hint Resolve Cnat_nat Cnat0 Cnat1.

Fact Cnat_key : pred_key Cnat. Proof. by []. Qed.
Fact Cnat_semiring : semiring_closed Cnat.
Proof.
by do 2![split] => //= _ _ /CnatP[n ->] /CnatP[m ->]; rewrite -(natrD, natrM).
Qed.
Canonical Cnat_keyed := KeyedPred Cnat_key.
Canonical Cnat_addrPred := AddrPred Cnat_semiring.
Canonical Cnat_mulrPred := MulrPred Cnat_semiring.
Canonical Cnat_semiringPred := SemiringPred Cnat_semiring.

Lemma Cnat_ge0 x : x \in Cnat -> 0 <= x.
Proof. by case/CnatP=> n ->; apply: ler0n. Qed.

Lemma conj_Cnat x : x \in Cnat -> x^* = x.
Proof. by case/CnatP=> n ->; apply: rmorph_nat. Qed.

Lemma Creal_Cnat : {subset Cnat <= Creal}.
Proof. by move=> z /conj_Cnat/CrealP. Qed.

Lemma Cnat_sum_eq1 (I : finType) (P : pred I) (F : I -> algC) :
     (forall i, P i -> F i \in Cnat) -> \sum_(i | P i) F i = 1 ->
   {i : I | [/\ P i, F i = 1 & forall j, j != i -> P j -> F j = 0]}.
Proof.
move=> natF sumF1; pose nF i := truncC (F i).
have{natF} defF i: P i -> F i = (nF i)%:R by move/natF/eqP.
have{sumF1} /eqP sumF1: (\sum_(i | P i) nF i == 1)%N.
  by rewrite -eqC_nat natr_sum -(eq_bigr _ defF) sumF1.
have [i Pi nZfi]: {i : I | P i & nF i != 0%N}.
  by apply/sig2W/exists_inP; rewrite -negb_forall_in -sum_nat_eq0 sumF1.
have F'ge0 := (leq0n _, etrans (eq_sym _ _) (sum_nat_eq0 (predD1 P i) nF)).
rewrite -lt0n in nZfi; have [_] := (leqif_add (leqif_eq nZfi) (F'ge0 _)).
rewrite /= big_andbC -bigD1 // sumF1 => /esym/andP/=[/eqP Fi1 /forall_inP Fi'0].
exists i; split=> // [|j neq_ji Pj]; first by rewrite defF // -Fi1.
by rewrite defF // (eqP (Fi'0 j _)) // neq_ji.
Qed.

(* Integer subset. *)

Lemma floorC_def x : x \is Creal -> (floorC x)%:~R <= x < (floorC x + 1)%:~R.
Proof. by rewrite /floorC => Rx; case: (floorC_subproof x) => //= m; apply. Qed.

Lemma intCK : cancel intr floorC.
Proof.
move=> m; have:= floorC_def (rpred_int _ m).
by rewrite ler_int ltr_int ltz_addr1 => /ler_anti.
Qed.

Lemma floorCK : {in Cint, cancel floorC intr}. Proof. by move=> z /eqP. Qed.

Lemma floorC0 : floorC 0 = 0. Proof. exact: (intCK 0). Qed.
Hint Resolve floorC0.

Lemma floorCpK (p : {poly algC}) :
  p \is a polyOver Cint -> map_poly intr (map_poly floorC p) = p.
Proof.
move/(all_nthP 0)=> Zp; apply/polyP=> i.
rewrite coef_map coef_map_id0 //= -[p]coefK coef_poly.
by case: ifP => [/Zp/floorCK // | _]; rewrite floorC0.
Qed.

Lemma floorCpP (p : {poly algC}) :
  p \is a polyOver Cint -> {q | p = map_poly intr q}.
Proof. by exists (map_poly floorC p); rewrite floorCpK. Qed.

Lemma Cint_int (m : int) : m%:~R \in Cint.
Proof. by rewrite unfold_in intCK. Qed.

Lemma CintP x : reflect (exists m, x = m%:~R) (x \in Cint).
Proof.
by apply: (iffP idP) => [/eqP<-|[m ->]]; [exists (floorC x) | apply: Cint_int].
Qed.

Lemma rpred_Cint S (ringS : subringPred S) (kS : keyed_pred ringS) x :
  x \in Cint -> x \in kS.
Proof. by case/CintP=> m ->; apply: rpred_int. Qed.

Lemma Cint_Cnat : {subset Cnat <= Cint}.
Proof. by move=> _ /CnatP[n ->]; rewrite pmulrn Cint_int. Qed.

Lemma Cint0 : 0 \in Cint. Proof. exact: Cint_Cnat. Qed.
Lemma Cint1 : 1 \in Cint. Proof. exact: Cint_Cnat. Qed.
Hint Resolve Cint0 Cint1.

Fact Cint_key : pred_key Cint. Proof. by []. Qed.
Fact Cint_subring : subring_closed Cint.
Proof.
by split=> // _ _ /CintP[m ->] /CintP[p ->];
    rewrite -(rmorphB, rmorphM) Cint_int.
Qed.
Canonical Cint_keyed := KeyedPred Cint_key.
Canonical Cint_opprPred := OpprPred Cint_subring.
Canonical Cint_addrPred := AddrPred Cint_subring.
Canonical Cint_mulrPred := MulrPred Cint_subring.
Canonical Cint_zmodPred := ZmodPred Cint_subring.
Canonical Cint_semiringPred := SemiringPred Cint_subring.
Canonical Cint_smulrPred := SmulrPred Cint_subring.
Canonical Cint_subringPred := SubringPred Cint_subring.

Lemma CintE x : (x \in Cint) = (x \in Cnat) || (- x \in Cnat).
Proof.
apply/idP/idP=> [/CintP[[n | n] ->] | ]; first by rewrite Cnat_nat.
  by rewrite NegzE opprK Cnat_nat orbT.
by case/pred2P=> [<- | /(canLR (@opprK _)) <-]; rewrite ?rpredN rpred_nat.
Qed.

Lemma Creal_Cint : {subset Cint <= Creal}.
Proof. by move=> _ /CintP[m ->]; apply: realz. Qed.

Lemma conj_Cint x : x \in Cint -> x^* = x.
Proof. by move/Creal_Cint/conj_Creal. Qed.

Lemma Cint_normK x : x \in Cint -> `|x| ^+ 2 = x ^+ 2.
Proof. by move/Creal_Cint/real_normK. Qed.

Lemma CintEsign x : x \in Cint -> x = (-1) ^+ (x < 0)%C * `|x|.
Proof. by move/Creal_Cint/realEsign. Qed.

Lemma Cnat_norm_Cint x : x \in Cint -> `|x| \in Cnat.
Proof.
case/CintP=> [m ->]; rewrite [m]intEsign rmorphM rmorph_sign.
by rewrite normrM normr_sign mul1r normr_nat rpred_nat.
Qed.

Lemma CnatEint x : (x \in Cnat) = (x \in Cint) && (0 <= x).
Proof.
apply/idP/andP=> [Nx | [Zx x_ge0]]; first by rewrite Cint_Cnat ?Cnat_ge0.
by rewrite -(ger0_norm x_ge0) Cnat_norm_Cint.
Qed.

Lemma CintEge0 x : 0 <= x -> (x \in Cint) = (x \in Cnat).
Proof. by rewrite CnatEint andbC => ->. Qed.

Lemma Cnat_exp_even x n : ~~ odd n -> x \in Cint -> x ^+ n \in Cnat.
Proof.
rewrite -dvdn2 => /dvdnP[m ->] Zx; rewrite mulnC exprM -Cint_normK ?rpredX //.
exact: Cnat_norm_Cint.
Qed.

Lemma norm_Cint_ge1 x : x \in Cint -> x != 0 -> 1 <= `|x|.
Proof.
rewrite -normr_eq0 => /Cnat_norm_Cint/CnatP[n ->].
by rewrite pnatr_eq0 ler1n lt0n.
Qed.

Lemma sqr_Cint_ge1 x : x \in Cint -> x != 0 -> 1 <= x ^+ 2.
Proof.
by move=> Zx nz_x; rewrite -Cint_normK // expr_ge1 ?normr_ge0 ?norm_Cint_ge1.
Qed.

(* Integer divisibility. *)

Lemma dvdCP x y : reflect (exists2 z, z \in Cint & y = z * x) (x %| y)%C.
Proof.
rewrite unfold_in; have [-> | nz_x] := altP eqP.
  by apply: (iffP eqP) => [-> | [z _ ->]]; first exists 0; rewrite ?mulr0.
apply: (iffP idP) => [Zyx | [z Zz ->]]; last by rewrite mulfK.
by exists (y / x); rewrite ?divfK.
Qed.

Lemma dvdCP_nat x y : 0 <= x -> 0 <= y -> (x %| y)%C -> {n | y = n%:R * x}.
Proof.
move=> x_ge0 y_ge0 x_dv_y; apply: sig_eqW.
case/dvdCP: x_dv_y => z Zz -> in y_ge0 *; move: x_ge0 y_ge0 Zz.
rewrite ler_eqVlt => /predU1P[<- | ]; first by exists 22; rewrite !mulr0.
by move=> /pmulr_lge0-> /CintEge0-> /CnatP[n ->]; exists n.
Qed.

Lemma dvdC0 x : (x %| 0)%C.
Proof. by apply/dvdCP; exists 0; rewrite ?mul0r. Qed.

Lemma dvd0C x : (0 %| x)%C = (x == 0).
Proof. by rewrite unfold_in eqxx. Qed.

Lemma dvdC_mull x y z : y \in Cint -> (x %| z)%C -> (x %| y * z)%C.
Proof.
move=> Zy /dvdCP[m Zm ->]; apply/dvdCP.
by exists (y * m); rewrite ?mulrA ?rpredM.
Qed.

Lemma dvdC_mulr x y z : y \in Cint -> (x %| z)%C -> (x %| z * y)%C.
Proof. by rewrite mulrC; apply: dvdC_mull. Qed.

Lemma dvdC_trans x y z : (x %| y)%C -> (y %| z)%C -> (x %| z)%C.
Proof. by move=> x_dv_y /dvdCP[m Zm ->]; apply: dvdC_mull. Qed.

Lemma dvdC_refl x : (x %| x)%C.
Proof. by apply/dvdCP; exists 1; rewrite ?mul1r. Qed.
Hint Resolve dvdC_refl.

Fact dvdC_key x : pred_key (dvdC x). Proof. by []. Qed.
Lemma dvdC_zmod x : zmod_closed (dvdC x).
Proof.
split=> [| _ _ /dvdCP[y Zy ->] /dvdCP[z Zz ->]]; first exact: dvdC0.
by rewrite -mulrBl dvdC_mull ?rpredB.
Qed.
Canonical dvdC_keyed x := KeyedPred (dvdC_key x).
Canonical dvdC_opprPred x := OpprPred (dvdC_zmod x).
Canonical dvdC_addrPred x := AddrPred (dvdC_zmod x).
Canonical dvdC_zmodPred x := ZmodPred (dvdC_zmod x).

Lemma dvdC_nat (p n : nat) : (p %| n)%C = (p %| n)%N.
Proof.
rewrite unfold_in CintEge0 ?divr_ge0 ?invr_ge0 ?ler0n // !pnatr_eq0.
have [-> | nz_p] := altP eqP; first by rewrite dvd0n.
apply/CnatP/dvdnP=> [[q def_q] | [q ->]]; exists q.
  by apply/eqP; rewrite -eqC_nat natrM -def_q divfK ?pnatr_eq0. 
by rewrite [num in num / _]natrM mulfK ?pnatr_eq0.
Qed.

Lemma dvdC_int (p : nat) x : x \in Cint -> (p %| x)%C = (p %| `|floorC x|)%N.
Proof.
move=> Zx; rewrite -{1}(floorCK Zx) {1}[floorC x]intEsign.
by rewrite rmorphMsign rpredMsign dvdC_nat.
Qed.

(* Elementary modular arithmetic. *)

Lemma eqCmod_refl e x : (x == x %[mod e])%C.
Proof. by rewrite /eqCmod subrr rpred0. Qed.

Lemma eqCmodm0 e : (e == 0 %[mod e])%C. Proof. by rewrite /eqCmod subr0. Qed.
Hint Resolve eqCmod_refl eqCmodm0.

Lemma eqCmod_sym e x y : ((x == y %[mod e]) = (y == x %[mod e]))%C.
Proof. by rewrite /eqCmod -opprB rpredN. Qed.

Lemma eqCmod_trans e x y z :
  (x == y %[mod e] -> y == z %[mod e] -> x == z %[mod e])%C.
Proof. by move=> Exy Eyz; rewrite /eqCmod -[x](subrK y) -addrA rpredD. Qed.

Lemma eqCmodN e x y : (- x == y %[mod e])%C = (x == - y %[mod e])%C.
Proof. by rewrite eqCmod_sym /eqCmod !opprK addrC. Qed.

Lemma eqCmodDr e x y z : (y + x == z + x %[mod e])%C = (y == z %[mod e])%C.
Proof. by rewrite /eqCmod addrAC opprD !addrA subrK. Qed.

Lemma eqCmodDl e x y z : (x + y == x + z %[mod e])%C = (y == z %[mod e])%C.
Proof. by rewrite !(addrC x) eqCmodDr. Qed.

Lemma eqCmodD e x1 x2 y1 y2 :
  (x1 == x2 %[mod e] -> y1 == y2 %[mod e] -> x1 + y1 == x2 + y2 %[mod e])%C.
Proof. rewrite -(eqCmodDl e x2 y1) -(eqCmodDr e y1); exact: eqCmod_trans. Qed.

Lemma eqCmodMr e :
  {in Cint, forall z x y, x == y %[mod e] -> x * z == y * z %[mod e]}%C.
Proof. by move=> z Zz x y; rewrite /eqCmod -mulrBl => /dvdC_mulr->. Qed.

Lemma eqCmodMl e :
  {in Cint, forall z x y, x == y %[mod e] -> z * x == z * y %[mod e]}%C.
Proof. by move=> z Zz x y Exy; rewrite !(mulrC z) eqCmodMr. Qed.

Lemma eqCmodMl0 e : {in Cint, forall x, x * e == 0 %[mod e]}%C.
Proof. by move=> x Zx; rewrite -(mulr0 x) eqCmodMl. Qed.

Lemma eqCmodMr0 e : {in Cint, forall x, e * x == 0 %[mod e]}%C.
Proof. by move=> x Zx; rewrite /= mulrC eqCmodMl0. Qed.

Lemma eqCmod_addl_mul e : {in Cint, forall x y, x * e + y == y %[mod e]}%C.
Proof. by move=> x Zx y; rewrite -{2}[y]add0r eqCmodDr eqCmodMl0. Qed.

Lemma eqCmodM e : {in Cint & Cint, forall x1 y2 x2 y1,
  x1 == x2 %[mod e] -> y1 == y2 %[mod e] -> x1 * y1 == x2 * y2 %[mod e]}%C.
Proof.
move=> x1 y2 Zx1 Zy2 x2 y1 eq_x /(eqCmodMl Zx1)/eqCmod_trans-> //.
exact: eqCmodMr.
Qed.

(* Rational number subset. *)

Lemma ratCK : cancel QtoC CtoQ.
Proof. by rewrite /getCrat; case: getCrat_subproof. Qed.

Lemma getCratK : {in Crat, cancel CtoQ QtoC}.
Proof. by move=> x /eqP. Qed.

Lemma Crat_rat (a : rat) : QtoC a \in Crat.
Proof. by rewrite unfold_in ratCK. Qed.

Lemma CratP x : reflect (exists a, x = QtoC a) (x \in Crat).
Proof.
by apply: (iffP eqP) => [<- | [a ->]]; [exists (CtoQ x) | rewrite ratCK].
Qed.

Lemma Crat0 : 0 \in Crat. Proof. by apply/CratP; exists 0; rewrite rmorph0. Qed.
Lemma Crat1 : 1 \in Crat. Proof. by apply/CratP; exists 1; rewrite rmorph1. Qed.
Hint Resolve Crat0 Crat1.

Fact Crat_key : pred_key Crat. Proof. by []. Qed.
Fact Crat_divring_closed : divring_closed Crat.
Proof.
split=> // _ _ /CratP[x ->] /CratP[y ->].
  by rewrite -rmorphB Crat_rat.
by rewrite -fmorph_div Crat_rat.
Qed.
Canonical Crat_keyed := KeyedPred Crat_key.
Canonical Crat_opprPred := OpprPred Crat_divring_closed.
Canonical Crat_addrPred := AddrPred Crat_divring_closed.
Canonical Crat_mulrPred := MulrPred Crat_divring_closed.
Canonical Crat_zmodPred := ZmodPred Crat_divring_closed.
Canonical Crat_semiringPred := SemiringPred Crat_divring_closed.
Canonical Crat_smulrPred := SmulrPred Crat_divring_closed.
Canonical Crat_divrPred := DivrPred Crat_divring_closed.
Canonical Crat_subringPred := SubringPred Crat_divring_closed.
Canonical Crat_sdivrPred := SdivrPred Crat_divring_closed.
Canonical Crat_divringPred := DivringPred Crat_divring_closed.

Lemma rpred_Crat S (ringS : divringPred S) (kS : keyed_pred ringS) :
  {subset Crat <= kS}.
Proof. by move=> _ /CratP[a ->]; apply: rpred_rat. Qed.

Lemma conj_Crat z : z \in Crat -> z^* = z.
Proof. by move/getCratK <-; rewrite fmorph_div !rmorph_int. Qed.

Lemma Creal_Crat : {subset Crat <= Creal}.
Proof. by move=> x /conj_Crat/CrealP. Qed.

Lemma Cint_rat a : (QtoC a \in Cint) = (a \in Qint).
Proof.
apply/idP/idP=> [Za | /numqK <-]; last by rewrite rmorph_int Cint_int.
apply/QintP; exists (floorC (QtoC a)); apply: (can_inj ratCK).
by rewrite rmorph_int floorCK.
Qed.

Lemma minCpolyP x :
   {p | minCpoly x = pQtoC p /\ p \is monic
      & forall q, root (pQtoC q) x = (p %| q)%R}.
Proof. by unlock minCpoly; case: (minCpoly_subproof x) => p /=; exists p. Qed.

Lemma minCpoly_monic x : minCpoly x \is monic.
Proof. by have [p [-> mon_p] _] := minCpolyP x; rewrite map_monic. Qed.

Lemma minCpoly_eq0 x : (minCpoly x == 0) = false.
Proof. exact/negbTE/monic_neq0/minCpoly_monic. Qed.

Lemma root_minCpoly x : root (minCpoly x) x.
Proof. by have [p [-> _] ->] := minCpolyP x. Qed.

Lemma size_minCpoly x : (1 < size (minCpoly x))%N.
Proof. by apply: root_size_gt1 (root_minCpoly x); rewrite ?minCpoly_eq0. Qed.

(* Basic properties of automorphisms. *)
Section AutC.

Implicit Type nu : {rmorphism algC -> algC}.

Lemma aut_Cnat nu : {in Cnat, nu =1 id}.
Proof. by move=> _ /CnatP[n ->]; apply: rmorph_nat. Qed.

Lemma aut_Cint nu : {in Cint, nu =1 id}.
Proof. by move=> _ /CintP[m ->]; apply: rmorph_int. Qed.

Lemma aut_Crat nu : {in Crat, nu =1 id}.
Proof. by move=> _ /CratP[a ->]; apply: fmorph_rat. Qed.

Lemma Cnat_aut nu x : (nu x \in Cnat) = (x \in Cnat).
Proof.
by do [apply/idP/idP=> Nx; have:= aut_Cnat nu Nx] => [/fmorph_inj <- | ->].
Qed.

Lemma Cint_aut nu x : (nu x \in Cint) = (x \in Cint).
Proof. by rewrite !CintE -rmorphN !Cnat_aut. Qed.

Lemma Crat_aut nu x : (nu x \in Crat) = (x \in Crat).
Proof.
apply/idP/idP=> /CratP[a] => [|->]; last by rewrite fmorph_rat Crat_rat.
by rewrite -(fmorph_rat nu) => /fmorph_inj->; apply: Crat_rat.
Qed.

Lemma algC_invaut_subproof nu x : {y | nu y = x}.
Proof.
have [r Dp] := closed_field_poly_normal (minCpoly x).
suffices /mapP/sig2_eqW[y _ ->]: x \in map nu r by exists y.
rewrite -root_prod_XsubC; congr (root _ x): (root_minCpoly x).
have [q [Dq _] _] := minCpolyP x; rewrite Dq -(eq_map_poly (fmorph_rat nu)).
rewrite (map_poly_comp nu) -{q}Dq Dp (monicP (minCpoly_monic x)) scale1r.
rewrite rmorph_prod big_map; apply: eq_bigr => z _.
by rewrite rmorphB /= map_polyX map_polyC.
Qed.
Definition algC_invaut nu x := sval (algC_invaut_subproof nu x).

Lemma algC_invautK nu : cancel (algC_invaut nu) nu.
Proof. by move=> x; rewrite /algC_invaut; case: algC_invaut_subproof. Qed.

Lemma algC_autK nu : cancel nu (algC_invaut nu).
Proof. exact: inj_can_sym (algC_invautK nu) (fmorph_inj nu). Qed.

Fact algC_invaut_is_rmorphism nu : rmorphism (algC_invaut nu).
Proof. exact: can2_rmorphism (algC_autK nu) (algC_invautK nu). Qed.
Canonical algC_invaut_additive nu := Additive (algC_invaut_is_rmorphism nu).
Canonical algC_invaut_rmorphism nu := RMorphism (algC_invaut_is_rmorphism nu).

Lemma minCpoly_aut nu x : minCpoly (nu x) = minCpoly x.
Proof.
wlog suffices dvd_nu: nu x / (minCpoly x %| minCpoly (nu x))%R.
  apply/eqP; rewrite -eqp_monic ?minCpoly_monic //; apply/andP; split=> //.
  by rewrite -{2}(algC_autK nu x) dvd_nu.
have [[q [Dq _] min_q] [q1 [Dq1 _] _]] := (minCpolyP x, minCpolyP (nu x)).
rewrite Dq Dq1 dvdp_map -min_q -(fmorph_root nu) -map_poly_comp.
by rewrite (eq_map_poly (fmorph_rat nu)) -Dq1 root_minCpoly.
Qed.

End AutC.

Section AutLmodC.

Variables (U V : lmodType algC) (f : {additive U -> V}).

Lemma raddfZ_Cnat a u : a \in Cnat -> f (a *: u) = a *: f u. 
Proof. by case/CnatP=> n ->; exact: raddfZnat. Qed.

Lemma raddfZ_Cint a u : a \in Cint -> f (a *: u) = a *: f u. 
Proof. by case/CintP=> m ->; rewrite !scaler_int raddfMz. Qed.

End AutLmodC.

End AlgebraicsTheory.
Hint Resolve Cnat_nat Cnat0 Cnat1 Cint0 Cint1 floorC0 Crat0 Crat1.
Hint Resolve dvdC0 dvdC_refl eqCmod_refl eqCmodm0.