Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype bigop.
Require Import finfun ssralg matrix zmodp poly polydiv mxpoly vector algebra.
Require Import tuple generic_quotient.

(******************************************************************************)
(*  * Finite dimensional Field Extentions                                     *)
(*     fieldExt F      == type for finite dimensional field extension.        *)
(*     FieldExt F E    == packs a field E to build a field extension over     *)
(*                         F. The field E should have a canonical structure   *)
(*                         as a algFType over F.                              *)
(*                                                                            *)
(*    subFExtend iota z p == Given a field morphism iota : F -> L, this is a  *)
(*                           type for the field F^iota(z). It requires        *)
(*                           p : {poly F} be non-zero and z be a root of      *)
(*                           p^iota otherwise the field F^iota is returned.   *)
(*                           p need not be irredicible.                       *)
(*            subfx_inj x == The injection of F^iota(z) into L.               *)
(*   inj_subfx iota z p x == The injection of F into F^iota(z).               *)
(*  subfx_eval iota z p q == Given q : {poly F} returns q.[z] as a valule of  *)
(*                           type F^iota(z).                                  *)
(*                                                                            *)
(*           polyOver K p == the coefficents of p lie in the subspace K       *)
(*            Fadjoin K x == K(x) as a vector space                           *)
(*            minPoly K x == the monic minimal polynomial of x over the       *)
(*                           subfield K                                       *)
(*      elementDegree K x == the degree of the minimial polynomial or the     *)
(*                           dimension of K(x)/K                              *)
(* poly_for_Fadjoin K x y == a polynomial p over K such that y = p.[x]        *)
(******************************************************************************)

(* Some remarks about subfields:  In a finite dimensional field extension,    *)
(* the subfields are exactly the subalgebras.  So you can use {algebra E}     *)
(* where you'd want to use {field E}.                                         *)
(*                                                                            *)
(* Also note that not all constructive subfields have type {algebra E} in     *)
(* the same way that not all constructive subspaces have type {vector E}.     *)
(* These types only include the so called "detachable" subspaces (and         *)
(* subalgebras).                                                              *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Local Scope ring_scope.

Import GRing.Theory.

(* Finite Dimensional Field Extension *)

Module FieldExt.

Import GRing.

Section FieldExt.

Variable R : Ring.type.
Implicit Type phR : phant R.

Record class_of (T : Type) : Type := Class {
  base1 : Field.class_of T;
  lmod_ext : Lmodule.mixin_of R (Zmodule.Pack base1 T);
  lalg_ext : @Lalgebra.axiom R (Lmodule.Pack _ (Lmodule.Class lmod_ext) T) 
                                (Ring.mul base1);
  (* Do I really need this since it can be derived? *)
  alg_ext : Algebra.axiom (Lalgebra.Pack (Phant R)
                                          (Lalgebra.Class lalg_ext) T);
  vec_ext : VectorType.mixin_of (Lmodule.Pack _ (Lmodule.Class lmod_ext) T)
}.

Local Coercion base1 : class_of >-> Field.class_of.
Local Coercion alg_ext : class_of >-> Algebra.axiom.
Definition base2 T (c : class_of T) :=
  @AlgFType.Class _ _ (Algebra.Class c) (vec_ext c).
Local Coercion base2 : class_of >-> AlgFType.class_of.
Definition base3 T (c : class_of T) := @UnitAlgebra.Class _ _ c c.
Local Coercion base3 : class_of >-> UnitAlgebra.class_of.

Structure type phR := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Definition class phR (cT : type phR) :=
  let: Pack _ c _ :=  cT return class_of cT in c.
Definition clone phR T cT c of phant_id (@class phR cT) c := @Pack phR T c T.

Definition pack phR T :=
  fun bT b & phant_id (Field.class bT) (b : Field.class_of T) =>
  fun mT lm lam am vm & phant_id (@AlgFType.class _ phR mT) 
    (@AlgFType.Class R T 
       (@Algebra.Class R T (@Lalgebra.Class R T b lm lam) am) vm) =>
    Pack (Phant R) (@Class T b lm lam am vm) T.

Lemma AlgebraAxiom T (base : Field.class_of T)
  (lmod_ext : Lmodule.mixin_of R (Zmodule.Pack base T))
  (lalg_ext : @Lalgebra.axiom R (Lmodule.Pack _ (Lmodule.Class lmod_ext) T) 
                                (Ring.mul base)) :
  Algebra.axiom (Lalgebra.Pack (Phant R) (Lalgebra.Class lalg_ext) T).
Proof.
move=> c /= x y.
have Hcom: (commutative (Ring.mul base)) by case: (ComUnitRing.base base).
by rewrite /mul /= !(Hcom x) scalerAl.
Qed.

Definition eqType phR cT := Equality.Pack (@class phR cT) cT.
Definition choiceType phR cT := Choice.Pack (@class phR cT) cT.
Definition zmodType phR cT := Zmodule.Pack (@class phR cT) cT.
Definition ringType phR cT := Ring.Pack (@class phR cT) cT.
Definition unitRingType phR cT := UnitRing.Pack (@class phR cT) cT.
Definition comRingType phR cT := ComRing.Pack (@class phR cT) cT.
Definition comUnitRingType phR cT := ComUnitRing.Pack (@class phR cT) cT.
Definition idomainType phR cT := IntegralDomain.Pack (@class phR cT) cT.
Definition fieldType phR cT := Field.Pack (@class phR cT) cT.
Definition lmodType phR cT := Lmodule.Pack phR (@class phR cT) cT.
Definition lalgType phR cT := Lalgebra.Pack phR (@class phR cT) cT.
Definition algType phR cT := Algebra.Pack phR (@class phR cT) cT.
Definition unitAlgType phR cT := UnitAlgebra.Pack phR (@class phR cT) cT.
Definition vectorType phR cT := VectorType.Pack phR (@class phR cT) cT.
Definition algfType phR cT := AlgFType.Pack phR (@class phR cT) cT.

Definition unitRing_algfType phR  cT :=
  @UnitRing.Pack (AlgFType.sort (@algfType phR cT)) 
    (class cT) (AlgFType.sort (algfType cT)).
Definition comRing_algfType phR  cT :=
  @ComRing.Pack (AlgFType.sort (@algfType phR cT)) 
    (class cT) (AlgFType.sort (algfType cT)).
Definition comUnitRing_algfType phR  cT :=
  @ComUnitRing.Pack (AlgFType.sort (@algfType phR cT)) 
    (class cT) (AlgFType.sort (algfType cT)).
Definition idomain_algfType phR  cT :=
  @IntegralDomain.Pack (AlgFType.sort (@algfType phR cT)) 
    (class cT) (AlgFType.sort (algfType cT)).
Definition field_algfType phR  cT :=
  @Field.Pack (AlgFType.sort (@algfType phR cT)) 
    (class cT) (AlgFType.sort (algfType cT)).
Definition unitAlg_algfType phR  cT :=
  @UnitAlgebra.Pack R phR (AlgFType.sort (@algfType phR cT)) 
    (class cT) (AlgFType.sort (algfType cT)).
Definition lmodule_algfType phR  cT :=
  @Lmodule.Pack R phR (AlgFType.sort (@algfType phR cT)) 
    (class cT) (AlgFType.sort (algfType cT)).
Definition vector_algfType phR  cT :=
  @VectorType.Pack R phR (AlgFType.sort (@algfType phR cT)) 
    (class cT) (AlgFType.sort (algfType cT)).

Definition unitRing_unitAlgType phR  cT :=
  @UnitRing.Pack (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).
Definition comRing_unitAlgType phR  cT :=
  @ComRing.Pack (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).
Definition comUnitRing_unitAlgType phR  cT :=
  @ComUnitRing.Pack (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).
Definition idomain_unitAlgType phR  cT :=
  @IntegralDomain.Pack (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).
Definition field_unitAlgType phR  cT :=
  @Field.Pack (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).
Definition lmodule_unitAlgType phR  cT :=
  @Lmodule.Pack R phR (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).
Definition lalgebra_unitAlgType phR  cT :=
  @Lalgebra.Pack R phR (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).
Definition algebra_unitAlgType phR  cT :=
  @Algebra.Pack R phR (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).
Definition vector_unitAlgType phR  cT :=
  @VectorType.Pack R phR (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).
Definition algfType_unitAlgType phR  cT :=
  @AlgFType.Pack R phR (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).

End FieldExt.

Module Exports.

Coercion sort : type >-> Sortclass.
Coercion base1 : class_of >-> Field.class_of.
Coercion lmod_ext : class_of >-> Lmodule.mixin_of.
Coercion lalg_ext : class_of >-> Lalgebra.axiom.
Coercion alg_ext : class_of >-> Algebra.axiom.
Coercion vec_ext : class_of >-> VectorType.mixin_of.
Coercion base2 : class_of >-> AlgFType.class_of.
Coercion base3 : class_of >-> UnitAlgebra.class_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Coercion comUnitRingType : type >-> ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> IntegralDomain.type.
Canonical idomainType.
Coercion fieldType : type >-> Field.type.
Canonical fieldType.
Coercion lmodType : type >-> Lmodule.type.
Canonical lmodType.
Coercion lalgType : type >-> Lalgebra.type.
Canonical lalgType.
Coercion algType : type >-> Algebra.type.
Canonical algType.
Coercion unitAlgType : type >-> UnitAlgebra.type.
Canonical unitAlgType.
Coercion vectorType : type >-> VectorType.type.
Canonical vectorType.
Coercion algfType : type >-> AlgFType.type.
Canonical algfType.

Canonical unitRing_algfType.
Canonical comRing_algfType.
Canonical comUnitRing_algfType.
Canonical idomain_algfType.
Canonical field_algfType.
Canonical unitAlg_algfType.
Canonical lmodule_algfType.
Canonical vector_algfType.

Canonical unitRing_unitAlgType.
Canonical comRing_unitAlgType.
Canonical comUnitRing_unitAlgType.
Canonical idomain_unitAlgType.
Canonical field_unitAlgType.
Canonical lmodule_unitAlgType.
Canonical lalgebra_unitAlgType.
Canonical algebra_unitAlgType.
Canonical vector_unitAlgType.
Canonical algfType_unitAlgType.

Bind Scope ring_scope with FieldExt.sort.

Notation fieldExtType R := (@FieldExt.type _ (Phant R)).
Notation FieldExtType R T :=
    (@FieldExt.pack _ (Phant R) T _ _ id _ _ _ _ _ id).

End Exports.
End FieldExt.
Import FieldExt.Exports.

Section SubFieldExtension.

Local Open Scope quotient_scope.

Local Notation "p ^ f" := (map_poly f p) : ring_scope.

Variables (F L: fieldType) (iota : {rmorphism F -> L}).
Variables (z : L) (p : {poly F}).

Let p' := if ((p != 0) && (root (p ^ iota) z))
          then  (lead_coef p)^-1 *: p
          else 'X.

Let p'_mon : p' \is monic.
Proof.
rewrite (fun_if (fun p => p \in _)) monicX.
case: ifP => // /andP [Hp0 _].
rewrite monicE /p' /lead_coef coefZ.
by rewrite size_scale ?mulVf ?invr_neq0 // -/(lead_coef p) lead_coef_eq0.
Qed.

Let p'ne0 : p' != 0.
Proof. by rewrite monic_neq0 // p'_mon. Qed.

Let z' := if ((p != 0) && (root (p ^ iota) z))
          then z
          else 0.

Let Hp'z : root (p' ^ iota) z'.
Proof.
rewrite /p' /z'.
case: ifP => [/andP [_ Hpz]|]; last by rewrite map_polyX rootX.
rewrite map_polyZ /root hornerZ mulf_eq0 -/(root (p ^ iota) z) Hpz.
by rewrite orbT.
Qed.

Let H1p' : 0 < (size p').-1.
Proof.
rewrite -ltnS -polySpred // -/(size [:: z']) -(size_map_poly iota).
by rewrite (max_poly_roots) ?map_poly_eq0 // /= Hp'z.
Qed.

Let iotaz : commr_rmorph iota z'.
Proof. move => x; apply: mulrC. Qed.

Let n (x : 'rV[F]_(size p').-1) := (horner_morph iotaz (rVpoly x)).

Let e : equiv_rel [choiceType of ('rV[F]_(size p').-1)].
apply: (@EquivRel _ (fun x y => n x == n y)) => [x | x y | x y w] //.
apply: eq_op_trans.
Defined.

Definition subFExtend : Type := [mod e].
Canonical Structure subFExtend_eqType := [eqType of subFExtend].
Canonical Structure subFExtend_choiceType := [choiceType of subFExtend].

Lemma subfext_injm : mfun1_spec
  (fun (x: 'rV[F]_(size p').-1) => horner_morph iotaz (rVpoly x)) subFExtend.
Proof.
move => y /=.
apply/eqP.
rewrite -[_ == _]/(e _ _).
apply/equivP.
by rewrite reprK.
Qed.

Definition subfx_inj : subFExtend -> L := (mfun1 subfext_injm).

Lemma subfext_addm : mop2_spec (fun x y => x + y) subFExtend.
Proof.
move=> x y /=; apply/equivP/eqP; rewrite /n !linearD /=.
by congr (_ + _); apply subfext_injm.
Qed.

Lemma subfext_oppm : mop1_spec (fun x => - x) subFExtend.
Proof.
move=> y /=; apply/equivP/eqP; rewrite /n !linearN /=.
congr (- _); apply subfext_injm.
Qed.

Local Notation subfext_add := (mop2 subfext_addm).
Local Notation subfext_opp := (mop1 subfext_oppm).
Local Notation subfext0 := (\pi_subFExtend 0).

Lemma addfxA : associative subfext_add.
Proof. exact: MonoidQuotient.mulqA subfext_addm. Qed.

Lemma addfxC : commutative subfext_add.
Proof. exact: MonoidQuotient.mulqC subfext_addm. Qed.

Lemma add0fx : left_id subfext0 subfext_add.
Proof. exact: MonoidQuotient.mul1q subfext_addm. Qed.

Lemma addfxN : left_inverse subfext0 subfext_opp subfext_add.
Proof. by elim/quotW=> x; rewrite !mopP; apply/equivP; rewrite addNr. Qed.

Definition subfext_zmodMixin :=  ZmodMixin addfxA addfxC add0fx addfxN.
Canonical Structure subfext_zmodType :=
  Eval hnf in ZmodType subFExtend subfext_zmodMixin.

Lemma poly_rV_K_modp_subproof q :
  rVpoly (poly_rV (q %% p') : 'rV[F]_(size p').-1) = q %% p'.
Proof.
apply: poly_rV_K.
have Hl : (lead_coef p')^-1 != 0 by rewrite invr_neq0 // lead_coef_eq0.
by rewrite -(size_scale _ Hl) -ltnS -polySpred // size_scale // ltn_modp //.
Qed.

Definition subfx_mul_rep (x y : 'rV[F]_(size p').-1) : 'rV[F]_(size p').-1
 := poly_rV ((rVpoly x) * (rVpoly y) %% p').

Lemma horner_iotaz_modp_subproof q :
  horner_morph iotaz (q %% p') = horner_morph iotaz q.
Proof.
rewrite {2}(divp_eq q p') rmorphD rmorphM /= {3}/horner_morph.
by move/eqP: Hp'z ->; rewrite mulr0 add0r.
Qed.

Lemma subfext_mulm : mop2_spec subfx_mul_rep subFExtend.
Proof.
move => x y /=.
apply/equivP/eqP.
rewrite /n !poly_rV_K_modp_subproof !horner_iotaz_modp_subproof 2!rmorphM.
by congr (_ * _); apply subfext_injm.
Qed.

Local Notation subfext_mul := (mop2 subfext_mulm).
Local Notation subfext1 := (\pi_subFExtend (poly_rV 1)).

Lemma mulfxA : associative (subfext_mul).
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> w.
rewrite !mopP; apply/equivP.
rewrite  /= /n !poly_rV_K_modp_subproof [_ %% p' * _ w]mulrC.
by rewrite !modp_mul // mulrA [_ * _ w]mulrC [_ w * (_ x * _ y)]mulrC.
Qed.

Lemma mulfxC : commutative subfext_mul.
Proof.
elim/quotW=> x; elim/quotW=> y.
rewrite !mopP; apply/equivP.
by rewrite /= /n !poly_rV_K_modp_subproof mulrC.
Qed.

Lemma mul1fx : left_id subfext1 subfext_mul.
Proof.
elim/quotW=> x; rewrite !mopP; apply/equivP => /=; rewrite /n.
rewrite poly_rV_K_modp_subproof poly_rV_K ?mul1r ?size_poly1 ?H1p' //.
rewrite modp_small //.
by apply: leq_ltn_trans (size_poly _ _) _; rewrite -polySpred.
Qed.

Lemma mulfx_addl : left_distributive subfext_mul subfext_add.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> w.
rewrite !mopP; apply/equivP.
rewrite /= /n linearD /= !poly_rV_K_modp_subproof -modp_add //.
by rewrite -mulrDl linearD.
Qed.

Lemma nonzero1fx : subfext1 != subfext0.
Proof.
move: (oner_neq0 L).
apply: contra.
move/eqP/equivP.
by rewrite /= /n linear0 poly_rV_K ?rmorph1 ?rmorph0 // size_poly1 H1p'.
Qed.

Definition subfext_comRingMixin := ComRingMixin (R:=[zmodType of subFExtend])
  mulfxA mulfxC mul1fx mulfx_addl nonzero1fx.
Canonical Structure  subfext_Ring :=
  Eval hnf in RingType subFExtend subfext_comRingMixin.
Canonical Structure subfext_comRing :=
  Eval hnf in ComRingType subFExtend mulfxC.

Definition poly_invert (q : {poly F}) : {poly F} :=
  if (horner_morph iotaz q) == 0 then 0
  else let g := gdcop q p' in
       let e := egcdp q g in
       let k := e.1 * q + e.2 * g in
       (k`_0)^-1 *: e.1.

Lemma poly_invertE q :
  horner_morph iotaz (poly_invert q) = (horner_morph iotaz q)^-1.
Proof.
rewrite /poly_invert.
case: eqP => [->|]; first by rewrite rmorph0 invr0.
move/eqP => Hqz.
have : root ((gdcop q p') ^ iota) z' 
     = root (p' ^ iota) z' && ~~ root (q ^ iota) z'.
  by rewrite -root_gdco ? map_poly_eq0 // gdcop_map.
case: gdcopP => r _.
rewrite -[p' == 0]negbK p'ne0 orbF coprimep_sym -gcdp_eqp1 eqp_sym => Hcoprime.
move/(eqp_trans Hcoprime): (egcdpE q r).
rewrite eqp_sym -size_poly_eq1.
case/size_poly1P => k Hk0 Hk Hr Hroot.
rewrite Hk -mul_polyC rmorphM coefC eqxx [_ _%:P]horner_morphC fmorphV.
apply: (canLR (mulKf _)); first by rewrite fmorph_eq0.
apply: (canRL (mulfK _)); first done.
rewrite -(horner_morphC iotaz) -Hk rmorphD !rmorphM.
suff /= -> : horner_morph iotaz r = 0 by rewrite mulr0 addr0.
apply /eqP.
by rewrite [_ == 0]Hroot Hp'z Hqz.
Qed.

Definition subfx_inv_rep (x : 'rV[F]_(size p').-1) : 'rV[F]_(size p').-1 :=
  poly_rV (poly_invert (rVpoly x) %% p').

Lemma subfext_invm : mop1_spec subfx_inv_rep subFExtend.
Proof.
move => x /=.
apply/equivP/eqP.
rewrite /n 2!{1}poly_rV_K_modp_subproof 2!{1}horner_iotaz_modp_subproof.
rewrite !poly_invertE.
congr (_^-1).
apply: subfext_injm.
Qed.

Local Notation subfext_inv := (mop1 subfext_invm).

Lemma subfx_fieldAxiom : GRing.Field.axiom 
  (subfext_inv : subFExtend -> subFExtend).
Proof.
elim/quotW => x Hx.
rewrite mopP [_ * _]mop2P.
apply/equivP.
rewrite /= /n !poly_rV_K_modp_subproof horner_iotaz_modp_subproof rmorphM /=.
rewrite horner_iotaz_modp_subproof poly_invertE mulVf.
  by rewrite poly_rV_K ?mul1r ?modp_size ?size_poly1 ?H1p' // rmorph1.
move: Hx.
apply: contra.
rewrite -(rmorph0 (horner_rmorphism iotaz)).
rewrite -(linear0 (rVpoly_linear _ (size p').-1)) -[_ == _]/(e _ _).
by move/equivP ->.
Qed.

Lemma subfx_inv0 : subfext_inv (0:subFExtend) = (0:subFExtend).
Proof.
rewrite mopP; apply/equivP; rewrite /= /n /subfx_inv_rep linear0.
by rewrite /poly_invert rmorph0 eqxx mod0p !linear0.
Qed.

Canonical Structure subfext_unitRing := Eval hnf in
  UnitRingType subFExtend (FieldUnitMixin subfx_fieldAxiom subfx_inv0).

Canonical Structure subfext_comUnitRing := Eval hnf in 
  [comUnitRingType of subFExtend].

Canonical Structure subfext_idomainType := Eval hnf in
  IdomainType subFExtend 
    (FieldIdomainMixin (@FieldMixin _ _ subfx_fieldAxiom subfx_inv0)).

Canonical Structure subfext_fieldType := Eval hnf in 
  FieldType subFExtend (@FieldMixin _ _ subfx_fieldAxiom subfx_inv0).

Lemma subfx_inj_is_rmorphism : rmorphism subfx_inj.
Proof.
split.
  elim/quotW=> x; elim/quotW=> y.
  by rewrite /subfx_inj [- _]mop1P [_ + _]mop2P !mfun1P linearB rmorphB.
split; last by rewrite /subfx_inj mfun1P poly_rV_K ?rmorph1 // size_poly1 H1p'.
elim/quotW=> x; elim/quotW=> y.
rewrite /subfx_inj [_ * _]mop2P !mfun1P /subfx_mul_rep.
by rewrite  poly_rV_K_modp_subproof horner_iotaz_modp_subproof rmorphM.
Qed.

Canonical Structure subfx_inj_additive := Additive subfx_inj_is_rmorphism.
Canonical Structure subfx_inj_rmorphism := RMorphism subfx_inj_is_rmorphism.

Definition subfx_eval (q : {poly F}) : subFExtend :=
  \pi_subFExtend (poly_rV (q %% p')).

Lemma subfx_eval_is_rmorphism : rmorphism subfx_eval.
Proof.
split=> [x y|].
  symmetry.
  rewrite /subfx_eval [- _]mop1P [_ + _]mop2P -linearB /= modp_add //.
  congr (\pi_subFExtend (poly_rV (_ + _))).
  symmetry.
  apply/eqP.
  by rewrite -addr_eq0 -modp_add // addNr mod0p.
split=> [x y|]; last first.
  by rewrite /subfx_eval modp_small // size_poly1 -subn_gt0 subn1 H1p'.
symmetry.
rewrite /subfx_eval [_ * _]mop2P /subfx_mul_rep !poly_rV_K_modp_subproof.
by rewrite modp_mul // mulrC modp_mul // mulrC.
Qed.

Canonical Structure subfx_eval_additive := Additive subfx_eval_is_rmorphism.
Canonical Structure subfx_eval_rmorphism := RMorphism subfx_eval_is_rmorphism.

Lemma subfx_inj_eval q :
  (p != 0) -> root (p ^ iota) z -> subfx_inj (subfx_eval q) = (q ^ iota).[z].
Proof.
move => Hp0 Hpz.
rewrite /subfx_inj mfun1P poly_rV_K_modp_subproof horner_iotaz_modp_subproof.
by rewrite /horner_morph /z' Hp0 Hpz.
Qed.

Definition inj_subfx := (subfx_eval \o polyC).

Lemma subfxE x : exists p, x = subfx_eval p.
Proof.
elim/quotW: x => x.
exists (rVpoly x).
apply/equivP.
by rewrite /= /n poly_rV_K_modp_subproof horner_iotaz_modp_subproof.
Qed.

End SubFieldExtension.

Section FieldExtTheory.

Variable F0 : fieldType.
Variable L : fieldExtType F0.

Lemma dim_prodvf : forall (K:{vspace L}) x, x != 0 -> \dim (K * x%:VS) = \dim K.
Proof.
have (K:{vspace L}) x : x != 0 -> \dim (K * x%:VS) <= \dim K.
  by move => Hx; rewrite (leq_trans (dim_prodv _ _)) // dim_injv Hx muln1.
move => suff K x Hx.
apply: anti_leq.
rewrite suff //= -{1}[K]prodv1 -(mulfV Hx) prodv_inj prodvA suff //.
by rewrite invr_neq0.
Qed.

Definition matrixOver (K : {vspace L}) n m (A : 'M_(n,m)) :=
  forallb i, forallb j, A i j \in K.

Lemma matrixOverP (K : {vspace L}) n m (A : 'M_(n,m)) :
  reflect (forall i j, A i j \in K) (matrixOver K A).
Proof.
apply: (iffP forallP).
  move => H i.
  by move/forallP: (H i).
move => H i.
by apply/forallP.
Qed.

Section SubAlgebra.

Variable K : {algebra L}.

Lemma mem1v : 1 \in K.
Proof.
by rewrite -aunit1 -(can_eq (mulfK (aoner_neq0 K))) mul1r aunitl // memv_unit.
Qed.

Lemma aunit_eq1 : aunit K = 1.
Proof. by apply/eqP; rewrite aunit1 mem1v. Qed.

Lemma sub1v : (1%:VS <= K)%VS.
Proof. by apply: mem1v. Qed.

Lemma memv_exp : forall x i, x \in K -> x ^+ i \in K.
Proof.
move => x.
elim => [|i Hi] Hx; first by rewrite expr0 mem1v.
by rewrite exprS memv_mul // Hi.
Qed.

Lemma memv_prodl I r (P : pred I) (vs_ : I -> L) :
  (forall i, P i -> vs_ i \in K) -> \prod_(i <- r | P i) vs_ i \in K.
Proof.
by move=> Hp; elim/big_ind: _ => //; [exact: mem1v | exact: memv_mul].
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

Fact aspace_mulr_closed : mulr_closed K.
Proof. by split; [exact: mem1v | exact: memv_mul]. Qed.
Canonical aspace_mulrPred := MulrPred aspace_mulr_closed.
Canonical aspace_smulrPred := SmulrPred aspace_mulr_closed.
Canonical aspace_semiringPred := SemiringPred aspace_mulr_closed.
Canonical aspace_subringPred := SubringPred aspace_mulr_closed.

Lemma polyOver_suba (p : {poly L}) :
  reflect (exists q : {poly (suba_of K)}, p = map_poly (@sa_val _ _ K) q)
          (p \is a polyOver K).
Proof.
apply: (iffP polyOverP) => [Hp | [q ->] i]; last by rewrite coef_map // subaP.
exists (\poly_(i < size p) (Suba (Hp i))).
rewrite -{1}[p]coefK.
apply/polyP => i.
rewrite coef_map !coef_poly.
by case: ifP.
Qed.

Lemma matrixOver_suba n m (A : 'M_(n,m)) :
  reflect (exists B, A = map_mx (@sa_val _ _ K) B)
          (matrixOver K A).
Proof.
apply: (iffP (matrixOverP _ _)); last first.
  by move => [B ->] i j; rewrite mxE subaP.
move => HA.
exists (\matrix_(i, j) (Suba (HA i j))).
apply/matrixP => i j.
by rewrite !mxE.
Qed.

End SubAlgebra.

Section aspace_cap.

Variable A B : {algebra L}.

Canonical Structure fspace_cap : {algebra L} :=
  Eval hnf in (aspace_cap (trans_eq (aunit_eq1 A) (sym_eq (aunit_eq1 B)))).

End aspace_cap.

Lemma polyOverSv (K E : {vspace L}):
  (K <= E)%VS -> {subset polyOver K <= polyOver E}.
Proof. by move/subvP=> sKE; exact: polyOverS. Qed.

Section FadjoinDefinitions.

Variable (K : {vspace L}).
Variable (x : L).

Let P n := (vdim L < n) ||
           (\dim (\sum_(i < n.+1) (K * (x ^+ i)%:VS))%VS < \dim K * n.+1).

Let Pholds : exists n, P n.
Proof. by exists (vdim L).+1; rewrite /P ltnSn. Qed.

Definition elementDegree := (ex_minn Pholds).-1.+1.

Definition Fadjoin := (\sum_(i < elementDegree) (K * (x ^+ i)%:VS))%VS.

(* Ideally this definition should use \poly; however we really make use of the
   fact that the index i has an ordinal type. *)
Definition poly_for_Fadjoin (v : L) := 
  \sum_(i < elementDegree) 
    ((sumv_pi (fun j => (K * (x ^+ nat_of_ord j)%:VS)%VS) predT i v) / (x ^+ i))
    *: 'X^i.

Definition minPoly : {poly L} := 
  'X^elementDegree - poly_for_Fadjoin (x ^+ elementDegree).

Let Pholds_gt0 : (0%N < ex_minn Pholds).
Proof.
case: ex_minnP => [[|//]].
by rewrite /P muln1 big_ord1 expr0 prodv1 !ltnn.
Qed.

Lemma dim_Fadjoin_subproof n :
  \sum_(i < n) \dim (K * (x ^+ i)%:VS)%VS <= (\dim K * n)%N.
Proof.
elim: n => [|n IH]; first by rewrite big_ord0.
rewrite big_ord_recr /= mulnSr leq_add ?IH // (leq_trans (dim_prodv _ _)) //.
rewrite dim_injv.
by case: (x ^+ n != 0); rewrite ?muln0 ?muln1.
Qed.

Lemma dim_Fadjoin : \dim Fadjoin = (\dim K * elementDegree)%N.
Proof.
move: Pholds_gt0.
rewrite /Fadjoin /elementDegree.
case: ex_minnP.
move => m _ Hm m0.
apply: anti_leq.
rewrite (leq_trans (dimv_leq_sum _ _)) ?dim_Fadjoin_subproof //=.
case: m Hm m0 => [//|m Hm _].
move: (ltnSn m).
rewrite ltnNge.
apply: contraR.
rewrite -ltnNge => Hlt.
apply: Hm.
by apply/orP; right.
Qed.

Lemma direct_Fadjoin : directv Fadjoin.
Proof.
apply/directvP => /=.
by apply: anti_leq; rewrite dimv_leq_sum dim_Fadjoin dim_Fadjoin_subproof.
Qed.

Lemma prodv_inj_coefK y v : v \in (K * y%:VS)%VS -> v / y \in K.
Proof.
move/coord_span ->.
rewrite mulr_suml memv_suml // => i _.
rewrite -scalerAl memvZl //.
have/(mem_nth 0)/allpairsP : (i < size (Tuple (size_prodv K y%:VS))).
  rewrite size_tuple.
  by case i.
move => [[c d] [/memv_basis Hc /memv_basis/injvP [a ->]] ->].
rewrite -mulrA -scalerAl.
case: (eqVneq y 0) => [-> | Hy0].
  by rewrite invr0 mulr0 scaler0 mulr0 mem0v.
by rewrite mulfV // mulrC -scalerAl mul1r memvZl.
Qed.

Lemma memv_prodv_inj_coef y v : v \in (K * y%:VS)%VS ->
 v = v / y * y.
Proof.
case: (eqVneq y 0) => [-> | Hy0]; last by rewrite mulfVK.
rewrite prodv0 memv0 => /eqP ->.
by rewrite mulr0.
Qed.

Lemma poly_for_polyOver v : poly_for_Fadjoin v \is a polyOver K.
Proof.
apply/(all_nthP 0) => i _ /=.
rewrite /poly_for_Fadjoin coef_sum memv_suml // => j _.
rewrite coefZ coefXn.
case: (i == j);last by rewrite mulr0 mem0v.
rewrite mulr1 prodv_inj_coefK //.
by apply: memv_sum_pi.
Qed.

Lemma size_poly_for v : size (poly_for_Fadjoin v) <= elementDegree.
Proof.
rewrite (leq_trans (size_sum _ _ _)) //.
apply/bigmax_leqP => i _.
set c := (_ / _).
case: (eqVneq c 0) => [-> | nzc]; first by rewrite scale0r size_poly0.
by rewrite (size_scale _ nzc) size_polyXn.
Qed.

Lemma poly_for_eq v : v \in Fadjoin -> (poly_for_Fadjoin v).[x] = v.
Proof.
move => Hv.
rewrite /poly_for_Fadjoin horner_sum {2}(sumv_sum_pi Hv) sum_lappE.
apply: eq_bigr => i _.
by rewrite !hornerE hornerXn -memv_prodv_inj_coef // memv_sum_pi.
Qed.

Lemma poly_Fadjoin_small v :
  reflect (exists p,
            [/\ p \is a polyOver K, size p <= elementDegree & v = p.[x]])
          (v \in Fadjoin).
Proof.
apply: (iffP idP) => [Hp|[p [/(all_nthP 0)/= pK sizep vp]]].
  exists (poly_for_Fadjoin v).
  by rewrite poly_for_polyOver size_poly_for poly_for_eq.
apply/memv_sumP.
exists (fun i : 'I_elementDegree => p`_i * x ^+ i).
split => [i _|]; last by rewrite vp (horner_coef_wide _ sizep).
rewrite memv_prod ?memv_inj //.
by have [/pK// | /(nth_default 0)->] := ltnP i (size p); exact: mem0v.
Qed.

Lemma poly_is_linear : linear_for (in_alg L \; *:%R) poly_for_Fadjoin.
Proof.
move=> a p q; rewrite /poly_for_Fadjoin /= scaler_sumr -big_split /=.
apply eq_bigr => i _ /=.
by rewrite linearP mulrDl scalerA -2!scalerAl mul1r scalerDl.
Qed.
Canonical poly_for_Fadjoin_addidive := Additive poly_is_linear.
Canonical poly_for_Fadjoin_linear := AddLinear poly_is_linear.

Lemma size_minPoly : size minPoly = elementDegree.+1.
Proof.
by rewrite /minPoly size_addl ?size_polyXn // size_opp ltnS size_poly_for.
Qed.

Lemma monic_minPoly : minPoly \is monic.
Proof.
rewrite monicE /lead_coef size_minPoly coefB coefXn eq_refl.
by rewrite nth_default ?subr0 // size_poly_for.
Qed.

Lemma root_minPoly_subproof : x ^+ elementDegree \in Fadjoin ->
  root minPoly x.
Proof.
move => HxED.
rewrite /root !hornerE_comm horner_sum hornerXn.
rewrite {1}(sumv_sum_pi HxED) sum_lappE subr_eq0.
apply/eqP.
apply: eq_bigr => i _.
by rewrite !hornerE_comm hornerXn -memv_prodv_inj_coef ?memv_sum_pi.
Qed.

End FadjoinDefinitions.

Section Fadjoin.

Variable (K : {algebra L}).
Variable (x : L).

Lemma elementDegreeBound : elementDegree K x <= vdim L.
Proof.
rewrite /elementDegree prednK; last first.
  case: ex_minnP => [[|//]].
  by rewrite muln1 big_ord1 expr0 prodv1 !ltnn.
case: ex_minnP => m _. apply.
apply/orP; right.
apply: (@leq_trans ((vdim L).+1)); first by rewrite ltnS -dimvf dimvS // subvf.
rewrite leq_pmull // lt0n dimv_eq0 -subv0.
apply: contra (oner_neq0 L).
rewrite -memv0.
move/(subv_trans (sub1v K)).
move/subvP; apply.
by apply: memv_inj.
Qed.

Lemma capv_KxED_subproof :
  (x == 0) = ((K * (x ^+ elementDegree K x)%:VS :&: Fadjoin K x)%VS == 0%:VS).
Proof.
apply/eqP/eqP => [->|/eqP H]; first by rewrite exprS mul0r prodv0 cap0v.
apply/eqP; move: H.
apply: contraLR => nzx.
rewrite -subv0 -dimv_sum_leqif neq_ltn.
apply/orP; left.
rewrite dim_Fadjoin dim_prodvf ?expf_neq0 // -{1}[\dim K]muln1 -muln_addr add1n.
move: elementDegreeBound.
rewrite /Fadjoin /elementDegree.
case: ex_minnP => [[|m]]; first by rewrite muln1 big_ord1 expr0 prodv1 !ltnn.
rewrite leqNgt.
case/orP => [|Hm _ _]; first by rewrite ltnS; move/negbTE ->.
apply: (leq_trans _ Hm).
by rewrite [(\sum_(i < m.+2) _)%VS]big_ord_recr addvC.
Qed.

Lemma elemDeg1_subproof : (x \in K) -> elementDegree K x = 1%N.
Proof.
rewrite /elementDegree.
case: ex_minnP => [[|m _ Hm xK]].
  by rewrite muln1 big_ord1 expr0 prodv1 !ltnn.
apply/eqP.
rewrite eqSS -leqn0 -ltnS Hm //.
rewrite !big_ord_recl big_ord0 expr1 expr0 addv0 prodv1.
apply/orP; right.
apply (@leq_trans (\dim K).+1).
  rewrite ltnS dimvS // subv_add subv_refl (subv_trans _ (asubv K)) //.
  by rewrite prodv_monor.
rewrite -addn1 mulnC -[(2 * _)%N]/(\dim K + (\dim K + 0))%N leq_add2l addn0.
by rewrite -(dimv1 L) dimvS // sub1v.
Qed.

Lemma minPolyOver : minPoly K x \is a polyOver K.
Proof. by rewrite /minPoly rpredB ?rpredX ?polyOverX ?poly_for_polyOver. Qed.

(* This lemma could be generalized if I instead defined elementDegree 0 x = 0 *)
Lemma poly_Fadjoin_small_uniq : {in polyOver K &, forall p q : {poly L}, 
    size p <= elementDegree K x -> size q <= elementDegree K x ->
  p.[x] = q.[x] -> p = q}.
Proof.
case (eqVneq x 0).
  move/eqP; rewrite -memv0 => x0.
  move: (subv_trans x0 (sub0v K)).
  move/elemDeg1_subproof => -> p q pK qK.
  by do 2 move/size1_polyC ->; rewrite !hornerE => ->.
move => nzx p q; move/polyOverP => pK; move/polyOverP => qK szp szq.
rewrite (horner_coef_wide _ szp) (horner_coef_wide _ szq).
move/eqP; move: (direct_Fadjoin K x); move/directv_sum_unique => sumUniq.
rewrite sumUniq {sumUniq}; try by move=> i; rewrite memv_prod ?memv_inj ?pK ?qK.
move/forall_inP => Hpq; apply/polyP => i.
apply: (mulIf (expf_neq0 i nzx)).
case: (leqP (elementDegree K x) i) => Hi; last first.
  by apply/eqP; apply (Hpq (Ordinal Hi)).
by rewrite (_ : p`_i = 0) ?mul0r; first rewrite (_ : q`_i = 0) ?mul0r //;
 move: Hi; [ move/(leq_trans szq) | move/(leq_trans szp) ];
 move/leq_sizeP; apply.
Qed.

Hypothesis HxED : x ^+ (elementDegree K x) \in (Fadjoin K x).

Lemma minPoly_coef0_subproof : ((minPoly K x)`_0 == 0) = (x == 0).
Proof.
case (@eqP _ x 0) => Hx.
  move: Hx (root_minPoly_subproof HxED) ->.
  rewrite /root horner_coef size_minPoly big_ord_recl big1
          ?expr0 ?mulr1 ?addr0 // => i _.
  by rewrite exprSr !mulr0.
move: (minPoly K x) minPolyOver (root_minPoly_subproof HxED)
      (size_minPoly K x) => p.
move/polyOverP => pK rootp sizep.
do 2 apply/negP.
have: (lead_coef p != 0) by rewrite lead_coef_eq0 -size_poly_eq0 sizep.
apply: contra.
move/eqP => p0.
move/directv_sumP: (direct_Fadjoin K x).
move/eqP: Hx rootp => Hx.
rewrite /root horner_coef sizep big_ord_recl p0 mul0r add0r
        -(can_eq (mulfVK Hx)) mulr_suml mul0r => sump.
have Hxi : x ^+ ((elementDegree K x).-1) != 0.
  by rewrite expf_eq0 negb_and Hx orbT.
rewrite -(can_eq (mulfK Hxi)) mul0r -memv0.
move/(_ ord_max isT) <-.
rewrite memv_cap lead_coefE sizep.
apply/andP; split; first by rewrite memv_prod ?memv_inj ?pK.
rewrite [nth 0]lock /= (bigID (fun j => j == ord_max)) -lock in sump.
rewrite big_pred1_eq addr_eq0 exprSr mulrA mulfK // in sump.
rewrite {sump}(eqP sump) memvN memv_sumr // => i _.
by rewrite exprSr mulrA (mulfK Hx) memv_prod ?memv_inj ?pK.
Qed.

Lemma subsetFadjoinE_subproof: forall E : {algebra L},
  (K <= E)%VS && (x \in E) = (Fadjoin K x <= E)%VS.
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
  by rewrite /Fadjoin big_ord_recl expr0 prodv1 addvSl.
move: HxED.
rewrite /Fadjoin /elementDegree.
rewrite exprS.
case: _.-1 => [|d]; first by rewrite expr0 mulr1.
move => _.
rewrite !big_ord_recl.
apply: (subv_trans _ (addvSr _ _)).
apply: (subv_trans _ (addvSl _ _)).
by rewrite -{1}[x%:VS]prod1v prodv_monol // sub1v.
Qed.

End Fadjoin.

End FieldExtTheory.

Export FieldExt.Exports.