Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype bigop.
Require Import finfun ssralg matrix zmodp vector algebra.
Require Import poly polydiv mxpoly generic_quotient.

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
  base1 :> Field.class_of T;
  lmod_ext :> Lmodule.mixin_of R (Zmodule.Pack base1 T);
  lalg_ext :> @Lalgebra.axiom R (Lmodule.Pack _ (Lmodule.Class lmod_ext) T) 
                                (Ring.mul base1);
  (* Do I really need this since it can be derived? *)
  alg_ext :> Algebra.axiom (Lalgebra.Pack (Phant R)
                                          (Lalgebra.Class lalg_ext) T);
  vec_ext :> VectorType.mixin_of (Lmodule.Pack _ (Lmodule.Class lmod_ext) T)
}.

Coercion base2 T (m:class_of T) :=
  @AlgFType.Class R T (Algebra.Class m) (vec_ext m).
Coercion base3 T (m:class_of T) := @UnitAlgebra.Class R T m m.

Structure type phR := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class phR (cT : type phR) :=
  let: Pack _ c _ :=  cT return class_of cT in c.
Definition clone phR T cT c of phant_id (@class phR cT) c := @Pack phR T c T.
Definition pack phR T :=
  fun bT b & phant_id (Field.class bT) (b : Field.class_of T) =>
  fun mT lm lam am vm & phant_id (@AlgFType.class _ phR mT) 
   (@AlgFType.Class R T 
    (@Algebra.Class R T (@Lalgebra.Class R T b lm lam) am)
    vm) =>
  Pack (Phant R) (@Class T b lm lam am vm) T.

Lemma AlgebraAxiom : forall T
  (base : Field.class_of T)
  (lmod_ext : Lmodule.mixin_of R (Zmodule.Pack base T))
  (lalg_ext : @Lalgebra.axiom R (Lmodule.Pack _ (Lmodule.Class lmod_ext) T) 
                                (Ring.mul base)),
  Algebra.axiom (Lalgebra.Pack (Phant R) (Lalgebra.Class lalg_ext) T).
Proof.
move=> T b lm lam c /= x y.
have Hcom: (commutative (Ring.mul b)) by case: (ComUnitRing.base b).
rewrite /mul /= !(Hcom x).
by rewrite scaler_mull.
Qed.

Coercion eqType phR cT := Equality.Pack (@class phR cT) cT.
Coercion choiceType phR cT := Choice.Pack (@class phR cT) cT.
Coercion zmodType phR cT := Zmodule.Pack (@class phR cT) cT.
Coercion ringType phR cT := Ring.Pack (@class phR cT) cT.
Coercion unitRingType phR cT := UnitRing.Pack (@class phR cT) cT.
Coercion comRingType phR cT := ComRing.Pack (@class phR cT) cT.
Coercion comUnitRingType phR cT := ComUnitRing.Pack (@class phR cT) cT.
Coercion idomainType phR cT := IntegralDomain.Pack (@class phR cT) cT.
Coercion fieldType phR cT := Field.Pack (@class phR cT) cT.
Coercion lmodType phR cT := Lmodule.Pack phR (@class phR cT) cT.
Coercion lalgType phR cT := Lalgebra.Pack phR (@class phR cT) cT.
Coercion algType phR cT := Algebra.Pack phR (@class phR cT) cT.
Coercion unitAlgType phR cT := UnitAlgebra.Pack phR (@class phR cT) cT.
Coercion vectorType phR cT := VectorType.Pack phR (@class phR cT) cT.
Coercion algfType phR cT := AlgFType.Pack phR (@class phR cT) cT.

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
Definition lmodRing_unitAlgType phR  cT :=
  @Lmodule.Pack R phR (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).
Definition lalgRing_unitAlgType phR  cT :=
  @Lalgebra.Pack R phR (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).
Definition algRing_unitAlgType phR  cT :=
  @Algebra.Pack R phR (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).
Definition vectorRing_unitAlgType phR  cT :=
  @VectorType.Pack R phR (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).
Definition algfRing_unitAlgType phR  cT :=
  @AlgFType.Pack R phR (UnitAlgebra.sort (@unitAlgType phR cT)) 
    (class cT) (UnitAlgebra.sort (unitAlgType cT)).

End FieldExt.

End FieldExt.

Canonical Structure FieldExt.eqType.
Canonical Structure FieldExt.choiceType.
Canonical Structure FieldExt.zmodType.
Canonical Structure FieldExt.ringType.
Canonical Structure FieldExt.unitRingType.
Canonical Structure FieldExt.comRingType.
Canonical Structure FieldExt.comUnitRingType.
Canonical Structure FieldExt.idomainType.
Canonical Structure FieldExt.fieldType.
Canonical Structure FieldExt.lmodType.
Canonical Structure FieldExt.lalgType.
Canonical Structure FieldExt.algType.
Canonical Structure FieldExt.unitAlgType.
Canonical Structure FieldExt.vectorType.
Canonical Structure FieldExt.algfType.
Canonical Structure FieldExt.unitRing_algfType.
Canonical Structure FieldExt.comRing_algfType.
Canonical Structure FieldExt.comUnitRing_algfType.
Canonical Structure FieldExt.idomain_algfType.
Canonical Structure FieldExt.field_algfType.
Canonical Structure FieldExt.unitAlg_algfType.
Canonical Structure FieldExt.unitRing_unitAlgType.
Canonical Structure FieldExt.comRing_unitAlgType.
Canonical Structure FieldExt.comUnitRing_unitAlgType.
Canonical Structure FieldExt.idomain_unitAlgType.
Canonical Structure FieldExt.field_unitAlgType.
Canonical Structure FieldExt.lmodRing_unitAlgType.
Canonical Structure FieldExt.lalgRing_unitAlgType.
Canonical Structure FieldExt.algRing_unitAlgType.
Canonical Structure FieldExt.vectorRing_unitAlgType.
Canonical Structure FieldExt.algfRing_unitAlgType.

Bind Scope ring_scope with FieldExt.sort.

Notation fieldExtType R := (@FieldExt.type _ (Phant R)).
Notation FieldExtType R T :=
    (@FieldExt.pack _ (Phant R) T _ _ id _ _ _ _ _ id).

Section SubFieldExtension.

Local Open Scope quotient_scope.

Local Notation "p ^ f" := (map_poly f p) : ring_scope.

Variables (F L: fieldType) (iota : {rmorphism F -> L}).
Variables (z : L) (p : {poly F}).

Let p' := if ((p != 0) && (root (p ^ iota) z))
          then  (lead_coef p)^-1 *: p
          else 'X.

Let p'_mon : monic p'.
Proof.
rewrite /p' fun_if monicX.
case: ifP => // /andP [Hp0 _].
rewrite /monic /p' /lead_coef coefZ.
by rewrite size_scaler ?mulVf ?invr_neq0 // -/(lead_coef p) lead_coef_eq0.
Qed.

Let p'ne0 : p' != 0.
Proof. by rewrite monic_neq0 // p'_mon. Qed.

Let z' := if ((p != 0) && (root (p ^ iota) z))
          then z
          else 0.

Let Hp'z : root (p' ^ iota) z'.
Proof.
rewrite /p' /z'.
case: ifP; last by rewrite map_polyX rootX.
case/andP => _ Hpz.
rewrite map_poly_scaler /root horner_scaler mulf_eq0 -/(root (p ^ iota) z) Hpz.
by rewrite orbT.
Qed.

Let H1p' : 0 < (size p').-1.
Proof.
rewrite -ltnS -polySpred // -/(size [:: z']) -(size_map_poly iota).
by rewrite (max_poly_roots) ?map_poly_eq0 // /= Hp'z.
Qed.

Let iotaz : commr_rmorph iota z'.
Proof. move => x; apply: mulrC. Qed.

Let e : equiv_rel [choiceType of ('rV[F]_(size p').-1)].
apply: (@EquivRel _ (fun x y =>
  (horner_morph iotaz (rVpoly x)) == (horner_morph iotaz (rVpoly y))))
  => [x | x y | x y w] //.
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
move => x y /=.
apply/equivP/eqP.
rewrite !linearD !rmorphD /=.
by congr (_ + _); apply subfext_injm.
Qed.

Lemma subfext_oppm : mop1_spec (fun x => - x) subFExtend.
Proof.
move => y /=.
apply/equivP/eqP.
rewrite !linearN !rmorphN /=.
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
Proof.
elim/quotW=> x.
rewrite !mopP; apply/equivP.
by rewrite addNr.
Qed.

Definition subfext_zmodMixin :=  ZmodMixin addfxA addfxC add0fx addfxN.
Canonical Structure subfext_zmodType :=
  Eval hnf in ZmodType subFExtend subfext_zmodMixin.

Lemma poly_rV_K_modp_subproof q :
  rVpoly (poly_rV (q %% p') : 'rV[F]_(size p').-1) = q %% p'.
Proof.
apply: poly_rV_K.
have Hl : (lead_coef p')^-1 != 0 by rewrite invr_neq0 // lead_coef_eq0.
by rewrite -(size_scaler _ Hl) -ltnS -polySpred // size_scaler // modp_spec //.
Qed.

Definition subfx_mul_rep (x y : 'rV[F]_(size p').-1) : 'rV[F]_(size p').-1
 := poly_rV ((rVpoly x) * (rVpoly y) %% p').

Lemma horner_iotaz_modp_subproof q :
  horner_morph iotaz (q %% p') = horner_morph iotaz q.
Proof.
rewrite {2}(divp_mon_spec q p'_mon) rmorphD rmorphM /= {3}/horner_morph.
move/eqP: Hp'z ->.
by rewrite mulr0 add0r.
Qed.

Lemma subfext_mulm : mop2_spec subfx_mul_rep subFExtend.
Proof.
move => x y /=.
apply/equivP/eqP.
rewrite !poly_rV_K_modp_subproof !horner_iotaz_modp_subproof 2!rmorphM.
by congr (_ * _); apply subfext_injm.
Qed.

Local Notation subfext_mul := (mop2 subfext_mulm).
Local Notation subfext1 := (\pi_subFExtend (poly_rV 1)).

Lemma mulfxA : associative (subfext_mul).
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> w.
rewrite !mopP; apply/equivP.
rewrite /= !poly_rV_K_modp_subproof [_ %% p' * _ w]mulrC.
by rewrite !monic_modp_mulmr // mulrA [_ * _ w]mulrC [_ w * (_ x * _ y)]mulrC.
Qed.

Lemma mulfxC : commutative subfext_mul.
Proof.
elim/quotW=> x; elim/quotW=> y.
rewrite !mopP; apply/equivP.
by rewrite /= !poly_rV_K_modp_subproof mulrC.
Qed.

Lemma mul1fx : left_id subfext1 subfext_mul.
Proof.
elim/quotW=> x.
rewrite !mopP; apply/equivP.
rewrite /= poly_rV_K_modp_subproof.
rewrite poly_rV_K ?mul1r ?modp_size ?size_poly1 ?H1p' //.
apply (leq_ltn_trans (size_poly _ _)).
by rewrite -polySpred.
Qed.

Lemma mulfx_addl : left_distributive subfext_mul subfext_add.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> w.
rewrite !mopP; apply/equivP.
rewrite /= linearD /= !poly_rV_K_modp_subproof -monic_modp_add //.
by rewrite -mulr_addl linearD.
Qed.

Lemma nonzero1fx : subfext1 != subfext0.
Proof.
move: (nonzero1r L).
apply: contra.
move/eqP/equivP.
by rewrite /= linear0 poly_rV_K ?rmorph1 ?rmorph0 // size_poly1 H1p'.
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
move/(eqp_trans Hcoprime): (egcdpP q r).
rewrite eqp_sym -size_poly_eq1.
case/size1P => k [Hk0 Hk] Hr Hroot.
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
rewrite 2!{1}poly_rV_K_modp_subproof 2!{1}horner_iotaz_modp_subproof.
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
rewrite /= !poly_rV_K_modp_subproof horner_iotaz_modp_subproof rmorphM /=.
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
rewrite mopP.
apply/equivP.
rewrite /= /subfx_inv_rep linear0 /poly_invert rmorph0 eqxx mod0p !linear0.
by rewrite rmorph0.
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
  by rewrite /subfx_inj [- _]mop1P [_ + _]mop2P !mfun1P linear_sub rmorph_sub.
split.
  elim/quotW=> x; elim/quotW=> y.
  rewrite /subfx_inj [_ * _]mop2P !mfun1P /subfx_mul_rep.
  by rewrite  poly_rV_K_modp_subproof horner_iotaz_modp_subproof rmorphM.
by rewrite /subfx_inj mfun1P poly_rV_K ?rmorph1 // size_poly1 H1p'.
Qed.

Canonical Structure subfx_inj_additive := Additive subfx_inj_is_rmorphism.
Canonical Structure subfx_inj_rmorphism := RMorphism subfx_inj_is_rmorphism.

Definition subfx_eval (q : {poly F}) : subFExtend :=
  \pi_subFExtend (poly_rV (q %% p')).

Lemma subfx_eval_is_rmorphism : rmorphism subfx_eval.
Proof.
split=> [x y|].
  symmetry.
  rewrite /subfx_eval [- _]mop1P [_ + _]mop2P -linear_sub /= monic_modp_add //.
  congr (\pi_subFExtend (poly_rV (_ + _))).
  symmetry.
  apply/eqP.
  by rewrite -addr_eq0 -monic_modp_add // addNr mod0p.
split=> [x y|]; last first.
  by rewrite /subfx_eval modp_size // size_poly1 -subn_gt0 subn1 H1p'.
symmetry.
rewrite /subfx_eval [_ * _]mop2P /subfx_mul_rep !poly_rV_K_modp_subproof.
by rewrite monic_modp_mulmr // mulrC monic_modp_mulmr // mulrC.
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
by rewrite /= poly_rV_K_modp_subproof horner_iotaz_modp_subproof.
Qed.

End SubFieldExtension.
