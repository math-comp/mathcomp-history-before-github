Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div choice fintype.
Require Import tuple finfun bigop ssralg finalg zmodp matrix vector falgebra.
Require Import poly polydiv mxpoly generic_quotient.

(******************************************************************************)
(*  * Finite dimensional field extentions                                     *)
(*      fieldExtType F == the interface type for finite field extensions of F *)
(*                        it simply combines the fieldType and FalgType F     *)
(*                        interfaces.                                         *)
(* [fieldExtType F of L] == a fieldExt F structure for a type L that has both *)
(*                        fieldType and FalgType F canonical structures.      *)
(* [fieldExtType F of L for K] == a fieldExtType F structure for a type L     *)
(*                        that has an FalgType F canonical structure, given   *)
(*                        a K : fieldType whose unitRingType projection       *)
(*                        coincides with the canonical unitRingType for F.    *)
(*        {subfield L} == the type of subfields of L that are also extensions *)
(*                        of F; since we are in a finite dimensional setting  *)
(*                        these are exactly the F-subalgebras of L, and       *)
(*                        indeed {subfield L} is just display notation for    *)
(*                        {aspace L} when L is an extFieldType.               *)
(*  --> All aspace operations apply to {subfield L}, but there are several    *)
(*      additional lemmas and canonical instances specific to {subfield L}    *)
(*      spaces, e.g., subvs_of E is an extFieldType F when E : {subfield L}.  *)
(*  --> Also note that not all constructive subfields have type {subfield E}  *)
(*      in the same way that not all constructive subspaces have type         *)
(*      {vspace E}. These types only include the so called "detachable"       *)
(*      subspaces (and subalgebras).                                          *)
(*                                                                            *)
(*               \dim_F E == (\dim E %/ dim F)%N.                             *)
(* (E :&: F)%AS, (E * F)%AS == the intersection and product (meet and join)   *)
(*                           of E and F as subfields.                         *)
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
(*            Fadjoin K x == K(x) as a vector space.                          *)
(*            minPoly K x == the monic minimal polynomial of x over the       *)
(*                           subfield K.                                      *)
(*      elementDegree K x == the degree of the minimial polynomial or the     *)
(*                           dimension of K(x)/K.                             *)
(* poly_for_Fadjoin K x y == a polynomial p over K such that y = p.[x].       *)
(*          genField K rs == K(rs : seq L) as a vector space.                 *)
(*                                                                            *)
(*            fieldOver F == L, but with an extFieldType (subvs_of F)         *)
(*                           structure, for F : {subfield L}                  *)
(*         vspaceOver F V == the smallest subspace of fieldOver F containing  *)
(*                           V; this coincides with V if V is an F-ideal.     *)
(*        baseFieldType L == L, but with an extFieldType F0 structure, when L *)
(*                           has a canonical extFieldType F structure and F   *)
(*                           in turn has an extFieldType F0 structure.        *)
(*           baseVspace V == the subspace of baseFieldType L that coincides   *)
(*                           with V : {vspace L}.                             *)
(* --> Some caution muse be exercised when using fieldOver and basFieldType,  *)
(*     because these are convertible to L while carrying different Lmodule    *)
(*     structures. This means that the safeguards engineered in the ssralg    *)
(*     library that normally curb the Coq kernel's inclination to diverge are *)
(*     no longer effectcive, so additional precautions should be taken when   *)
(*     matching or rewriting terms of the form a *: u, because Coq may take   *)
(*     forever to realize it's dealing with a *: in the wrong structure. The  *)
(*     baseField_scaleE and fieldOver_scaleE lemmas should be used to expand  *)
(*     or fold such "trans-structure" operations explicitly beforehand.       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

Module FieldExt.

Import GRing.

Section FieldExt.

Variable R : ringType.

Record class_of T := Class {
  base : Falgebra.class_of R T;
  comm_ext : commutative (Ring.mul base);
  idomain_ext : IntegralDomain.axiom (Ring.Pack base T);
  field_ext : Field.mixin_of (UnitRing.Pack base T)
}.

Local Coercion base : class_of >-> Falgebra.class_of.

Section Bases.
Variables (T : Type) (c : class_of T).
Definition base1 := ComRing.Class (@comm_ext T c).
Definition base2 := @ComUnitRing.Class T base1 c.
Definition base3 := @IntegralDomain.Class T base2 (@idomain_ext T c).
Definition base4 := @Field.Class T base3 (@field_ext T c).
End Bases.
Local Coercion base1 : class_of >-> ComRing.class_of.
Local Coercion base2 : class_of >-> ComUnitRing.class_of.
Local Coercion base3 : class_of >-> IntegralDomain.class_of.
Local Coercion base4 : class_of >-> Field.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variables (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c _ :=  cT return class_of cT in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun (bT : Falgebra.type phR) b
    & phant_id (Falgebra.class bT : Falgebra.class_of R bT)
               (b : Falgebra.class_of R T) =>
  fun mT Cm IDm Fm & phant_id (Field.class mT) (@Field.Class T
        (@IntegralDomain.Class T (@ComUnitRing.Class T (@ComRing.Class T b
          Cm) b) IDm) Fm) => Pack (Phant R) (@Class T b Cm IDm Fm) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @Ring.Pack cT xclass xT.
Definition unitRingType := @UnitRing.Pack cT xclass xT.
Definition comRingType := @ComRing.Pack cT xclass xT.
Definition comUnitRingType := @ComUnitRing.Pack cT xclass xT.
Definition idomainType := @IntegralDomain.Pack cT xclass xT.
Definition fieldType := @Field.Pack cT xclass xT.
Definition lmodType := @Lmodule.Pack R phR cT xclass xT.
Definition lalgType := @Lalgebra.Pack R phR cT xclass xT.
Definition algType := @Algebra.Pack R phR cT xclass xT.
Definition unitAlgType := @UnitAlgebra.Pack R phR cT xclass xT.
Definition vectType := @Vector.Pack R phR cT xclass xT.
Definition FalgType := @Falgebra.Pack R phR cT xclass xT.

Definition Falg_comRingType := @ComRing.Pack FalgType xclass xT.
Definition Falg_comUnitRingType := @ComUnitRing.Pack FalgType xclass xT.
Definition Falg_idomainType := @IntegralDomain.Pack FalgType xclass xT.
Definition Falg_fieldType := @Field.Pack FalgType xclass xT.

Definition vect_comRingType := @ComRing.Pack vectType xclass xT.
Definition vect_comUnitRingType := @ComUnitRing.Pack vectType xclass xT.
Definition vect_idomainType := @IntegralDomain.Pack vectType xclass xT.
Definition vect_fieldType := @Field.Pack vectType xclass xT.

Definition unitAlg_comRingType := @ComRing.Pack unitAlgType xclass xT.
Definition unitAlg_comUnitRingType := @ComUnitRing.Pack unitAlgType xclass xT.
Definition unitAlg_idomainType := @IntegralDomain.Pack unitAlgType xclass xT.
Definition unitAlg_fieldType := @Field.Pack unitAlgType xclass xT.

Definition alg_comRingType := @ComRing.Pack algType xclass xT.
Definition alg_comUnitRingType := @ComUnitRing.Pack algType xclass xT.
Definition alg_idomainType := @IntegralDomain.Pack algType xclass xT.
Definition alg_fieldType := @Field.Pack algType xclass xT.

Definition lalg_comRingType := @ComRing.Pack lalgType xclass xT.
Definition lalg_comUnitRingType := @ComUnitRing.Pack lalgType xclass xT.
Definition lalg_idomainType := @IntegralDomain.Pack lalgType xclass xT.
Definition lalg_fieldType := @Field.Pack lalgType xclass xT.

Definition lmod_comRingType := @ComRing.Pack lmodType xclass xT.
Definition lmod_comUnitRingType := @ComUnitRing.Pack lmodType xclass xT.
Definition lmod_idomainType := @IntegralDomain.Pack lmodType xclass xT.
Definition lmod_fieldType := @Field.Pack lmodType xclass xT.

End FieldExt.

Module Exports.

Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion base : class_of >-> Falgebra.class_of.
Coercion base4 : class_of >-> Field.class_of.
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
Coercion vectType : type >-> Vector.type.
Canonical vectType.
Coercion FalgType : type >-> Falgebra.type.
Canonical FalgType.

Canonical Falg_comRingType.
Canonical Falg_comUnitRingType.
Canonical Falg_idomainType.
Canonical Falg_fieldType.
Canonical vect_comRingType.
Canonical vect_comUnitRingType.
Canonical vect_idomainType.
Canonical vect_fieldType.
Canonical unitAlg_comRingType.
Canonical unitAlg_comUnitRingType.
Canonical unitAlg_idomainType.
Canonical unitAlg_fieldType.
Canonical alg_comRingType.
Canonical alg_comUnitRingType.
Canonical alg_idomainType.
Canonical alg_fieldType.
Canonical lalg_comRingType.
Canonical lalg_comUnitRingType.
Canonical lalg_idomainType.
Canonical lalg_fieldType.
Canonical lmod_comRingType.
Canonical lmod_comUnitRingType.
Canonical lmod_idomainType.
Canonical lmod_fieldType.
Notation fieldExtType R := (type (Phant R)).

Notation "[ 'fieldExtType' F 'of' L ]" :=
  (@pack _ (Phant F) L _ _ id _ _ _ _ id)
  (at level 0, format "[ 'fieldExtType'  F  'of'  L ]") : form_scope.
Notation "[ 'fieldExtType' F 'of' L 'for' K ]" :=
  (@FieldExt.pack _ (Phant F) L _ _ id K _ _ _ idfun)
  (at level 0, format "[ 'fieldExtType'  F  'of'  L  'for'  K ]") : form_scope.

Notation "{ 'subfield' L }" := (@aspace_of _ (FalgType _) (Phant L))
  (at level 0, format "{ 'subfield'  L }") : type_scope.

End Exports.
End FieldExt.
Export FieldExt.Exports.

Notation "\dim_ E V" := (divn (\dim V) (\dim E))
  (at level 10, E at level 2, V at level 8, format "\dim_ E  V") : nat_scope.

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

Definition equiv_subfext x y := (n x == n y).

Fact equiv_subfext_is_equiv : equiv_class_of equiv_subfext.
Proof. by rewrite /equiv_subfext; split => [x|x y|t x y] // /eqP ->. Qed.

Canonical equiv_subfext_equiv := EquivRelPack equiv_subfext_is_equiv.
Canonical equiv_subfext_encModRel := defaultEncModRel equiv_subfext.

Definition subFExtend := {eq_quot equiv_subfext}.
Canonical subFExtend_eqType := [eqType of subFExtend].
Canonical subFExtend_choiceType := [choiceType of subFExtend].
Canonical subFExtend_quotType := [quotType of subFExtend].
Canonical subFExtend_eqQuotType := [eqQuotType equiv_subfext of subFExtend].

Definition subfx_inj := lift_fun1 subFExtend n.

Lemma equiv_subfextE x y : (n x == n y) = (x == y %[mod subFExtend]).
Proof. by rewrite piE. Qed.

Lemma pi_subfx_inj : {mono \pi : x / 
  (horner_morph iotaz (rVpoly x)) >-> subfx_inj x}.
Proof.
by move=> x; unlock subfx_inj; apply/eqP; rewrite equiv_subfextE reprK.
Qed.
Canonical pi_subfx_inj_morph := PiMono1 pi_subfx_inj.

Definition subfext0 := lift_cst subFExtend 0.
Canonical subfext0_morph := PiConst subfext0.

Definition subfext_add := lift_op2 subFExtend +%R.
Lemma pi_subfext_add : {morph \pi : x y / x + y >-> subfext_add x y}.
Proof.
move=> x y /=; unlock subfext_add; apply/eqmodP/eqP.
by rewrite /n !linearD /= -!pi_subfx_inj !reprK.
Qed.
Canonical pi_subfx_add_morph := PiMorph2 pi_subfext_add.

Definition subfext_opp := lift_op1 subFExtend -%R.
Lemma pi_subfext_opp : {morph \pi : x / - x >-> subfext_opp x}.
Proof.
move=> y /=; unlock subfext_opp; apply/eqmodP/eqP. 
by rewrite /n !linearN /= -!pi_subfx_inj !reprK.
Qed.
Canonical pi_subfext_opp_morph := PiMorph1 pi_subfext_opp.

Lemma addfxA : associative subfext_add.
Proof. by move=> x y t; rewrite -[x]reprK -[y]reprK -[t]reprK !piE addrA. Qed.

Lemma addfxC : commutative subfext_add.
Proof. by move=> x y; rewrite -[x]reprK -[y]reprK !piE addrC. Qed.

Lemma add0fx : left_id subfext0 subfext_add.
Proof. by move=> x; rewrite -[x]reprK !piE add0r. Qed.

Lemma addfxN : left_inverse subfext0 subfext_opp subfext_add.
Proof. by move=> x; rewrite -[x]reprK !piE addNr. Qed.

Definition subfext_zmodMixin :=  ZmodMixin addfxA addfxC add0fx addfxN.
Canonical subfext_zmodType :=
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

Definition subfext_mul := lift_op2 subFExtend subfx_mul_rep.
Lemma pi_subfext_mul :
  {morph \pi : x y / subfx_mul_rep x y >-> subfext_mul x y}.
Proof.
move => x y /=; unlock subfext_mul; apply/eqmodP/eqP.
rewrite /n !poly_rV_K_modp_subproof !horner_iotaz_modp_subproof 2!rmorphM.
by rewrite /= -!pi_subfx_inj !reprK.
Qed.
Canonical pi_subfext_mul_morph := PiMorph2 pi_subfext_mul.

Definition subfext1 := lift_cst subFExtend (poly_rV 1).
Canonical subfext1_morph := PiConst subfext1.

Lemma mulfxA : associative (subfext_mul).
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> w; rewrite !piE /subfx_mul_rep.
rewrite !poly_rV_K_modp_subproof [_ %% p' * _ w]mulrC.
by rewrite !modp_mul // mulrA [_ * _ w]mulrC [_ w * (_ x * _ y)]mulrC.
Qed.

Lemma mulfxC : commutative subfext_mul.
Proof.
by elim/quotW=> x; elim/quotW=> y; rewrite !piE /subfx_mul_rep /= mulrC.
Qed.

Lemma mul1fx : left_id subfext1 subfext_mul.
Proof.
elim/quotW=> x; rewrite !piE /subfx_mul_rep.
rewrite poly_rV_K ?mul1r ?size_poly1 ?H1p' //.
rewrite modp_small ?rVpolyK //.
by apply: leq_ltn_trans (size_poly _ _) _; rewrite -polySpred.
Qed.

Lemma mulfx_addl : left_distributive subfext_mul subfext_add.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> w; rewrite !piE /subfx_mul_rep.
by rewrite linearD /= mulrDl modp_add linearD.
Qed.

Lemma nonzero1fx : subfext1 != subfext0.
Proof.
rewrite !piE /equiv_subfext /n !linear0.
by rewrite poly_rV_K ?rmorph1 ?oner_eq0 // size_poly1 H1p'.
Qed.

Definition subfext_comRingMixin :=
  ComRingMixin mulfxA mulfxC mul1fx mulfx_addl nonzero1fx.
Canonical  subfext_Ring :=
  Eval hnf in RingType subFExtend subfext_comRingMixin.
Canonical subfext_comRing :=
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

Definition subfx_inv_rep (x : 'rV[F]_(size p').-1) :
  'rV[F]_(size p').-1 := poly_rV (poly_invert (rVpoly x) %% p').

Definition subfext_inv := lift_op1 subFExtend subfx_inv_rep.
Lemma pi_subfext_inv : {morph \pi : x / subfx_inv_rep x >-> subfext_inv x}.
Proof.
move => x /=; unlock subfext_inv; apply/eqmodP/eqP.
rewrite /n 2!{1}poly_rV_K_modp_subproof 2!{1}horner_iotaz_modp_subproof.
by rewrite !poly_invertE -!pi_subfx_inj !reprK.
Qed.
Canonical pi_subfext_inv_morph := PiMorph1 pi_subfext_inv.

Lemma subfx_fieldAxiom :
  GRing.Field.axiom (subfext_inv : subFExtend -> subFExtend).
Proof.
elim/quotW => x Hx; apply/eqP; rewrite !piE /equiv_subfext /n.
rewrite !poly_rV_K_modp_subproof horner_iotaz_modp_subproof rmorphM /=.
rewrite horner_iotaz_modp_subproof poly_invertE mulVf.
  by rewrite poly_rV_K ?mul1r ?modp_size ?size_poly1 ?H1p' // rmorph1.
apply: contra Hx; rewrite !piE -(rmorph0 (horner_rmorphism iotaz)).
by rewrite -(linear0 (rVpoly_linear _ (size p').-1)).
Qed.

Lemma subfx_inv0 : subfext_inv (0 : subFExtend) = (0 : subFExtend).
Proof.
apply/eqP; rewrite !piE /equiv_subfext /n /subfx_inv_rep !linear0.
by rewrite /poly_invert rmorph0 eqxx mod0p !linear0.
Qed.

Definition subfext_unitRingMixin := FieldUnitMixin subfx_fieldAxiom subfx_inv0.
Canonical subfext_unitRingType :=
  Eval hnf in UnitRingType subFExtend subfext_unitRingMixin.
Canonical subfext_comUnitRing := Eval hnf in [comUnitRingType of subFExtend].
Definition subfext_fieldMixin := @FieldMixin _ _ subfx_fieldAxiom subfx_inv0.
Definition subfext_idomainMixin := FieldIdomainMixin subfext_fieldMixin.
Canonical subfext_idomainType :=
  Eval hnf in IdomainType subFExtend subfext_idomainMixin.
Canonical subfext_fieldType :=
  Eval hnf in FieldType subFExtend subfext_fieldMixin.

Lemma subfx_inj_is_rmorphism : rmorphism subfx_inj.
Proof.
do 2?split; last by rewrite piE poly_rV_K ?rmorph1 // size_poly1 H1p'.
  by elim/quotW=> x; elim/quotW=> y; rewrite !piE linearB rmorphB.
elim/quotW=> x; elim/quotW=> y; rewrite !piE /subfx_mul_rep.
by rewrite poly_rV_K_modp_subproof horner_iotaz_modp_subproof rmorphM.
Qed.
Canonical subfx_inj_additive := Additive subfx_inj_is_rmorphism.
Canonical subfx_inj_rmorphism := RMorphism subfx_inj_is_rmorphism.

Definition subfx_eval := lift_embed subFExtend (fun q => poly_rV (q %% p')).
Canonical subfx_eval_morph := PiEmbed subfx_eval.

Lemma subfx_eval_is_rmorphism : rmorphism subfx_eval.
Proof.
do 2?split; do ?move=> x y /=; apply/eqP; first 2 last.
+ by rewrite piE modp_small // size_poly1 -subn_gt0 subn1.
+ by rewrite piE -linearB modp_add modNp.
rewrite piE /subfx_mul_rep !poly_rV_K_modp_subproof.
by rewrite modp_mul [_ %% _ * _]mulrC modp_mul mulrC.
Qed.
Canonical subfx_eval_additive := Additive subfx_eval_is_rmorphism.
Canonical subfx_eval_rmorphism := AddRMorphism subfx_eval_is_rmorphism.

Lemma subfx_inj_eval q :
  (p != 0) -> root (p ^ iota) z -> subfx_inj (subfx_eval q) = (q ^ iota).[z].
Proof.
move => Hp0 Hpz.
rewrite piE poly_rV_K_modp_subproof horner_iotaz_modp_subproof.
by rewrite /horner_morph /z' Hp0 Hpz.
Qed.

Definition inj_subfx := (subfx_eval \o polyC).
Canonical inj_subfx_addidive := [additive of inj_subfx].
Canonical inj_subfx_rmorphism := [rmorphism of inj_subfx].

Lemma subfxE : forall x, exists p, x = subfx_eval p.
Proof.
elim/quotW=> x; exists (rVpoly x); apply/eqP; rewrite piE /equiv_subfext /n.
by rewrite poly_rV_K_modp_subproof horner_iotaz_modp_subproof.
Qed.

Definition subfx_scale a x := inj_subfx a * x.
Fact subfx_scalerA a b x :
  subfx_scale a (subfx_scale b x) = subfx_scale (a * b) x.
Proof. by rewrite /subfx_scale rmorphM mulrA. Qed.
Fact subfx_scaler1r : left_id 1 subfx_scale.
Proof. by move=> x; rewrite /subfx_scale rmorph1 mul1r. Qed.
Fact subfx_scalerDr : right_distributive subfx_scale +%R.
Proof. by move=> a; exact: mulrDr. Qed.
Fact subfx_scalerDl x : {morph subfx_scale^~ x : a b / a + b}.
Proof. by move=> a b; rewrite /subfx_scale rmorphD mulrDl. Qed.
Definition subfx_lmodMixin :=
  LmodMixin subfx_scalerA subfx_scaler1r subfx_scalerDr subfx_scalerDl.
Canonical subfx_lmodType := LmodType F subFExtend subfx_lmodMixin.

Fact subfx_scaleAl : GRing.Lalgebra.axiom ( *%R : subFExtend -> _).
Proof. by move=> a; exact: mulrA. Qed.
Canonical subfx_lalgType := LalgType F subFExtend subfx_scaleAl.

Fact subfx_scaleAr : GRing.Algebra.axiom subfx_lalgType.
Proof. by move=> a; exact: mulrCA. Qed.
Canonical subfx_algType := AlgType F subFExtend subfx_scaleAr.

Fact subfx_evalZ : scalable subfx_eval.
Proof. by move=> a q; rewrite -mul_polyC rmorphM. Qed.
Canonical subfx_eval_linear := AddLinear subfx_evalZ.
Canonical subfx_eval_lrmorphism := [lrmorphism of subfx_eval].

Hypotheses (pz0 : root (map_poly iota p) z) (nz_p : p != 0).

Lemma subfx_injZ b x : subfx_inj (b *: x) = iota b * subfx_inj x.
Proof. by rewrite rmorphM /= subfx_inj_eval // map_polyC hornerC. Qed.

Lemma subfx_inj_base b : subfx_inj b%:A = iota b.
Proof. by rewrite subfx_injZ rmorph1 mulr1. Qed.

(* The Vector axiom requires irreducibility. *)
Lemma min_subfx_vectAxiom :
    (forall q, root (map_poly iota q) z -> q != 0 -> (size p <= size q)%N) ->
  Vector.axiom (size p).-1 subfx_lmodType.
Proof.
move=> min_p; set d := (size p).-1; have Dd: d.+1 = size p by rewrite polySpred.
pose Fz2v x : 'rV_d := poly_rV (sval (sig_eqW (subfxE x)) %% p).
pose vFz : 'rV_d -> subFExtend := subfx_eval \o @rVpoly F d.
have FLinj: injective subfx_inj by exact: fmorph_inj.
have Fz2vK: cancel Fz2v vFz.
  move=> x; rewrite /vFz /Fz2v; case: (sig_eqW _) => /= q ->.
  apply: FLinj; rewrite !subfx_inj_eval // {2}(divp_eq q p) rmorphD rmorphM /=.
  by rewrite !hornerE (eqP pz0) mulr0 add0r poly_rV_K // -ltnS Dd ltn_modpN0.
have vFzK: cancel vFz Fz2v.
  apply: inj_can_sym Fz2vK _ => v1 v2 /(congr1 subfx_inj)/eqP.
  rewrite -subr_eq0 -!raddfB /= subfx_inj_eval // => /min_p/implyP.
  rewrite leqNgt implybNN -Dd ltnS size_poly linearB subr_eq0 /=.
  by move/eqP/(can_inj (@rVpolyK _ _)).
by exists Fz2v; [apply: can2_linear Fz2vK | exists vFz].
Qed.

End SubFieldExtension.

Section FieldExtTheory.

Variable F0 : fieldType.
Variable L : fieldExtType F0.
Implicit Types (U V J : {vspace L}) (E F K : {subfield L}).

Lemma dim_cosetv U x : x != 0 -> \dim (U * <[x]>) = \dim U.
Proof.
move=> nz_x; rewrite -limg_amulr limg_dim_eq //.
apply/eqP; rewrite -subv0; apply/subvP=> y.
by rewrite memv_cap memv0 memv_ker lfunE mulf_eq0 (negPf nz_x) orbF => /andP[].
Qed.

Definition matrixOver U n m (A : 'M_(n,m)) := forallb i, forallb j, A i j \in U.

Lemma matrixOverP U n m (A : 'M_(n,m)) :
  reflect (forall i j, A i j \in U) (matrixOver U A).
Proof. by apply: (iffP forallP) => U_A i; exact/forallP. Qed.

Lemma prodvC : commutative (@prodv F0 L).
Proof.
move=> U V; wlog suffices subC: U V / (U * V <= V * U)%VS.
  by apply/eqP; rewrite eqEsubv !{1}subC.
by apply/prodvP=> x y Ux Vy; rewrite mulrC memv_prod.
Qed.
Canonical prodv_comoid := Monoid.ComLaw prodvC.

Lemma prodvCA : left_commutative (@prodv F0 L).
Proof. exact: Monoid.mulmCA. Qed.

Lemma prodvAC : right_commutative (@prodv F0 L).
Proof. exact: Monoid.mulmAC. Qed.

Section SubAlgebra.

Variable K : {subfield L}.

Lemma algid1 : algid K = 1.
Proof. by apply: (mulIf (algid_neq0 K)); rewrite mul1r algidl ?memv_algid. Qed.

Lemma mem1v : 1 \in K. Proof. by rewrite -algid1 memv_algid. Qed.
Lemma sub1v : (1 <= K)%VS. Proof. exact: mem1v. Qed.

Fact vsval_multiplicative : multiplicative (vsval : subvs_of K -> L).
Proof. by split => //=; exact: algid1. Qed.
Canonical vsval_rmorphism := AddRMorphism vsval_multiplicative.
Canonical vsval_lrmorphism := [lrmorphism of (vsval : subvs_of K -> L)].

Lemma vsval_invf (w : subvs_of K) : val w^-1 = (vsval w)^-1.
Proof.
have [-> | Uv] := eqVneq w 0; first by rewrite !invr0.
by apply: vsval_invr; rewrite unitfE.
Qed.

Fact aspace_divr_closed : divr_closed K.
Proof.
split=> [|u v Ku Kv]; first exact: mem1v.
by rewrite -(vsval_invf (Subvs Kv)) memv_mul ?subvsP. 
Qed.
Canonical aspace_mulrPred := MulrPred aspace_divr_closed.
Canonical aspace_divrPred := DivrPred aspace_divr_closed.
Canonical aspace_smulrPred := SmulrPred aspace_divr_closed.
Canonical aspace_sdivrPred := SdivrPred aspace_divr_closed.
Canonical aspace_semiringPred := SemiringPred aspace_divr_closed.
Canonical aspace_subringPred := SubringPred aspace_divr_closed.
Canonical aspace_subalgPred := SubalgPred (memv_submod_closed K).
Canonical aspace_divringPred := DivringPred aspace_divr_closed.
Canonical aspace_divalgPred := DivalgPred (memv_submod_closed K).

Lemma memv_inv u : (u^-1 \in K) = (u \in K). Proof. exact: rpredV. Qed.
Lemma memv_invl u : u \in K -> u^-1 \in K. Proof. exact: GRing.rpredVr. Qed.

Lemma memv_exp x i : x \in K -> x ^+ i \in K. Proof. exact: rpredX. Qed.

Lemma memv_prodl I r (P : pred I) (vs : I -> L) :
  (forall i, P i -> vs i \in K) -> \prod_(i <- r | P i) vs i \in K.
Proof. exact: rpred_prod. Qed.

Definition subvs_mulC := [comRingMixin of subvs_of K by <:].
Canonical subvs_comRingType := Eval hnf in ComRingType (subvs_of K) subvs_mulC.
Canonical subvs_comUnitRingType := Eval hnf in [comUnitRingType of subvs_of K].
Definition subvs_mul_eq0 := [idomainMixin of subvs_of K by <:].
Canonical subvs_idomainType :=
  Eval hnf in IdomainType (subvs_of K) subvs_mul_eq0.
Lemma subvs_fieldMixin : GRing.Field.mixin_of subvs_idomainType.
Proof.
by move=> w nz_w; rewrite unitrE -val_eqE /= vsval_invf algid1 divff.
Qed.
Canonical subvs_fieldType :=
  Eval hnf in FieldType (subvs_of K) subvs_fieldMixin.
Canonical subvs_fieldExtType := Eval hnf in [fieldExtType F0 of subvs_of K].

Lemma polyOver_subvs (p : {poly L}) :
  reflect (exists q : {poly subvs_of K}, p = map_poly vsval q)
          (p \is a polyOver K).
Proof.
apply: (iffP polyOverP) => [Hp | [q ->] i]; last by rewrite coef_map // subvsP.
exists (\poly_(i < size p) (Subvs (Hp i))); rewrite -{1}[p]coefK.
by apply/polyP => i; rewrite coef_map !coef_poly; case: ifP.
Qed.

Lemma matrixOver_subvs n m (A : 'M_(n, m)) :
  reflect (exists B : 'M[subvs_of K]_(n, m), A = map_mx vsval B)
          (matrixOver K A).
Proof.
apply: (iffP (matrixOverP _ _)) => [K_A | [B ->] i j]; last first.
  by rewrite mxE subvsP.
by exists (\matrix_(i, j) (Subvs (K_A i j))); apply/matrixP=> i j; rewrite !mxE.
Qed.

Lemma divp_polyOver : {in polyOver K &, forall p q, p %/ q \is a polyOver K}.
Proof.
move=> _ _ /polyOver_subvs[p ->] /polyOver_subvs[q ->].
by apply/polyOver_subvs; exists (p %/ q); rewrite map_divp.
Qed.

Lemma modp_polyOver : {in polyOver K &, forall p q, p %% q \is a polyOver K}.
Proof.
move=> _ _ /polyOver_subvs[p ->] /polyOver_subvs[q ->].
by apply/polyOver_subvs; exists (p %% q); rewrite map_modp.
Qed.

Lemma scalp_polyOver :
  {in polyOver K &, forall p q, lead_coef p ^+ scalp p q \in K}.
Proof.
move=> _ _ /polyOver_subvs[p ->] /polyOver_subvs[q ->].
by rewrite scalp_map // memv_exp // lead_coef_map // subvsP.
Qed.

Lemma gcdp_polyOver : {in polyOver K &, forall p q, gcdp p q \is a polyOver K}.
Proof.
move=> _ _ /polyOver_subvs[p ->] /polyOver_subvs[q ->].
by apply/polyOver_subvs; exists (gcdp p q); rewrite gcdp_map.
Qed.

Lemma mulmx_matrixOver n m o (A : 'M_(n, m)) (B : 'M_(m, o)) :
  matrixOver K A -> matrixOver K B -> matrixOver K (A *m B).
Proof.
move => /matrixOverP K_A /matrixOverP K_B; apply/matrixOverP=> i j.
by rewrite mxE memv_suml // => k _; rewrite memv_mul.
Qed.

Lemma invmx_matrixOver n (A : 'M_n) : matrixOver K A = matrixOver K (invmx A).
Proof.
wlog suff Kinvmx: A / (matrixOver K A -> matrixOver K (invmx A)).
  by apply/idP/idP=> /Kinvmx; rewrite ?invmxK.
case/matrixOver_subvs => B ->; rewrite -map_invmx; apply/matrixOver_subvs.
by exists (invmx B).
Qed.

End SubAlgebra.

Fact prodv_is_aspace E F : is_aspace (E * F).
Proof.
rewrite /is_aspace prodvCA -!prodvA prodvA !prodv_id has_algid1 //=.
by rewrite -[1]mulr1 memv_prod ?mem1v.
Qed.
Canonical prodv_aspace E F : {subfield L} := ASpace (prodv_is_aspace E F).

Fact field_same_algid E F : algid E = algid F.
Proof. by rewrite !algid1. Qed.
Canonical capv_aspace E F : {subfield L} := aspace_cap (field_same_algid E F).

Lemma polyOverSv U V : (U <= V)%VS -> {subset polyOver U <= polyOver V}.
Proof. by move/subvP=> sUV; apply: polyOverS. Qed.

Lemma field_subvMl F U : (U <= F * U)%VS.
Proof. by rewrite -{1}[U]prod1v prodvSl ?sub1v. Qed.

Lemma field_subvMr U F : (U <= U * F)%VS.
Proof. by rewrite prodvC field_subvMl. Qed.

Lemma field_ideal_eq F J : (F * J <= J)%VS -> (F * J)%VS = J.
Proof. by move=> idealJ; apply/eqP; rewrite eqEsubv idealJ field_subvMl. Qed.

Lemma sup_field_ideal F E : (F * E <= E)%VS = (F <= E)%VS.
Proof.
apply/idP/idP; first exact: subv_trans (field_subvMr F E).
by move/(prodvSl E)/subv_trans->; rewrite ?asubv.
Qed.

Lemma field_ideal_semisimple F J (m := \dim_F J) (idealJ : (F * J <= J)%VS) :
  {b : m.-tuple L | [/\ {subset b <= J}, 0 \notin b & \dim J = (m * \dim F)%N]
     & let Sb := (\sum_(i < m) F * <[b`_i]>)%VS in Sb = J /\ directv Sb}.
Proof.
pose S n (b : n.-tuple L) := (\sum_(i < n) F * <[b`_i]>)%VS.
pose m1 := (m + ~~ (\dim F %| \dim J))%N.
suffices [b dimSb /andP[/allP sbJ nz_b]]:
  {b | \dim (S m1 b) = (m1 * \dim F)%N & all (mem J) b && (0%R \notin b)}.
- have defSb : S _ b = J.
    apply/eqP; rewrite eqEdim dimSb; apply/andP; split.
      apply/subv_sumP=> i _; apply: subv_trans idealJ.
      by apply/prodvSr/sbJ/mem_nth; rewrite size_tuple.
    rewrite (divn_eq (\dim J) (\dim F)) mulnDl leq_add2l /dvdn.
    by case: eqP => [-> // | _]; rewrite mul1n ltnW // ltn_mod adim_gt0.
  have ->: m = m1 by rewrite /m1 -defSb dimSb addnC dvdn_mull.
  rewrite -{2}defSb; exists b; split=> //; apply/eqnP; rewrite /= dimSb.
  rewrite -{1}[m1]card_ord -sum_nat_const; apply: eq_bigr => i _.
  by rewrite dim_cosetv ?(memPn nz_b) ?memt_nth.
have: (m1 * \dim F < \dim F + \dim J)%N.
  rewrite addnC {1}(divn_eq (\dim J) (\dim F)) -addnA mulnDl ltn_add2l /dvdn.
  by case: (_ %% _)%N => [|r]; rewrite ?adim_gt0 // mul1n ltnS leq_addl.
elim: {m}m1 => [|m IHm] ltFmJ.
  by exists [tuple] => //; rewrite /S big_ord0 dimv0.
rewrite mulSn ltn_add2l in ltFmJ.
have [b dimSb Jb] := IHm (leq_trans ltFmJ (leq_addl _ _)).
have /subvPn/sig2W[x Jx S'x]: ~~ (J <= S _ b)%VS.
  by apply: contraL ltFmJ => /dimvS; rewrite -dimSb -leqNgt.
have nz_x: x != 0 by apply: contraNneq S'x => ->; exact: mem0v.
exists [tuple of x :: b]; last by rewrite /= !inE Jx /= negb_or eq_sym nz_x.
rewrite /S big_ord_recl /= -/(S _ _) mulSn.
rewrite dimv_disjoint_sum ?dimSb ?dim_cosetv //; apply/eqP; rewrite -subv0. 
apply/subvP=> y; rewrite memv_cap memv0 => /andP[/memv_cosetP[a Fa ->{y}] Sax].
apply: contraR S'x; rewrite mulf_eq0 => /norP[/mulKf/( _ x)<- _].
rewrite -[S _ _](@field_ideal_eq F) ?memv_prod ?memv_inv //.
by rewrite /S -big_distrr prodvA prodv_id.
Qed.

Lemma dim_field_ideal F J : (F * J <= J)%VS -> \dim J = (\dim_F J * \dim F)%N.
Proof. by case/field_ideal_semisimple=> ? []. Qed.

Lemma dim_sup_field F E : (F <= E)%VS -> \dim E = (\dim_F E * \dim F)%N.
Proof. by rewrite -sup_field_ideal; exact: dim_field_ideal. Qed.

Lemma ideal_dimS F J : (F * J <= J)%VS -> (\dim F %| \dim J)%N.
Proof. by move/dim_field_ideal->; exact: dvdn_mull. Qed.

Lemma field_dimS F E : (F <= E)%VS -> (\dim F %| \dim E)%N.
Proof. by rewrite -sup_field_ideal; exact: ideal_dimS. Qed.

Section FadjoinDefinitions.

Variable (K : {vspace L}).
Variable (x : L).

Definition elementDegree_property n :=
  (Vector.dim L < n) ||
  (\dim (\sum_(i < n.+1) (K * <[x ^+ i]>)) < \dim K * n.+1).

Fact elementDegree_property_holds : exists n, elementDegree_property n.
Proof. by exists (Vector.dim L).+1; rewrite /elementDegree_property ltnSn. Qed.

Definition elementDegree := (ex_minn elementDegree_property_holds).-1.+1.

Definition Fadjoin := (\sum_(i < elementDegree) (K * <[x ^+ i]>))%VS.

(* Ideally this definition should use \poly; however we really make use of the
   fact that the index i has an ordinal type. *)
Definition poly_for_Fadjoin (v : L) := 
  \sum_i sumv_pi Fadjoin i v / x ^+ i *: 'X^i.

Definition minPoly : {poly L} := 
  'X^elementDegree - poly_for_Fadjoin (x ^+ elementDegree).

Let Pholds_gt0 : (0 < ex_minn elementDegree_property_holds).
Proof.
case: ex_minnP => [[|//]].
by rewrite /elementDegree_property muln1 big_ord1 expr0 prodv1 !ltnn.
Qed.

Lemma dim_Fadjoin_subproof n : \sum_(i < n) \dim (K * <[x ^+ i]>) <= \dim K * n.
Proof.
elim: n => [|n IH]; first by rewrite big_ord0.
rewrite big_ord_recr /= mulnSr leq_add ?IH // (leq_trans (dim_prodv _ _)) //.
rewrite dim_vline.
by case: (x ^+ n != 0); rewrite ?muln0 ?muln1.
Qed.

Lemma dim_Fadjoin : \dim Fadjoin = (\dim K * elementDegree)%N.
Proof.
move: Pholds_gt0.
rewrite /Fadjoin /elementDegree.
case: ex_minnP.
move => m _ Hm m0.
apply: anti_leq.
rewrite (leq_trans (dimv_leq_sum _ _ _)) ?dim_Fadjoin_subproof //=.
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

Lemma prodv_line_coefK y v : v \in (K * <[y]>)%VS -> v / y \in K.
Proof.
case/memv_cosetP=> u Ku ->; have [-> | /mulfK-> //] := eqVneq y 0.
by rewrite mulr0 mul0r mem0v.
Qed.

Lemma memv_prodv_line_coef y v : v \in (K * <[y]>)%VS -> v = v / y * y.
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
rewrite mulr1 prodv_line_coefK //.
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
rewrite /poly_for_Fadjoin horner_sum -{2}(sumv_pi_sum (erefl Fadjoin) Hv).
apply: eq_bigr => i _.
by rewrite !hornerE hornerXn -memv_prodv_line_coef // memv_sum_pi.
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
exists (fun i : 'I_elementDegree => p`_i * x ^+ i) => [i _|]; last first.
  by rewrite vp (horner_coef_wide _ sizep).
rewrite memv_prod ?memv_line //.
by have [/pK// | /(nth_default 0)->] := ltnP i (size p); exact: mem0v.
Qed.

Fact Fadjoin_poly_is_linear : linear_for (in_alg L \; *:%R) poly_for_Fadjoin.
Proof.
move=> a p q; rewrite /poly_for_Fadjoin /= scaler_sumr -big_split /=.
apply eq_bigr => i _ /=.
by rewrite linearP mulrDl scalerA -2!scalerAl mul1r scalerDl.
Qed.
Canonical poly_for_Fadjoin_addidive := Additive Fadjoin_poly_is_linear.
Canonical poly_for_Fadjoin_linear := AddLinear Fadjoin_poly_is_linear.

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
rewrite -{1}(sumv_pi_sum (erefl Fadjoin) HxED) subr_eq0.
apply/eqP/eq_bigr => i _.
by rewrite !hornerE_comm hornerXn -memv_prodv_line_coef ?memv_sum_pi.
Qed.

End FadjoinDefinitions.

Section Fadjoin.

Variable (K : {subfield L}).
Variable (x : L).

Lemma elementDegreeBound : elementDegree K x <= Vector.dim L.
Proof.
rewrite /elementDegree prednK; last first.
  case: ex_minnP => [[|//]].
  by rewrite /elementDegree_property muln1 big_ord1 expr0 prodv1 !ltnn.
case: ex_minnP => m _. apply.
apply/orP; right.
apply: (@leq_trans ((Vector.dim L).+1)).
  by rewrite ltnS -dimvf dimvS // subvf.
rewrite leq_pmull // lt0n dimv_eq0 -subv0.
apply: contra (oner_neq0 L).
rewrite -memv0.
move/(subv_trans (sub1v K)).
move/subvP; apply.
by apply: memv_line.
Qed.

Lemma capv_KxED_subproof :
  (x == 0) = (K * <[x ^+ elementDegree K x]> :&: Fadjoin K x == 0)%VS.
Proof.
apply/eqP/eqP => [->|/eqP H]; first by rewrite exprS mul0r prodv0 cap0v.
apply/eqP; move: H.
apply: contraLR => nzx.
rewrite (sameP eqP directv_addP) directvE ltn_eqF //=.
rewrite dim_Fadjoin dim_cosetv ?expf_neq0 // -mulnS.
have:= elementDegreeBound; rewrite /Fadjoin /elementDegree.
case: ex_minnP => [[|m]].
  by rewrite /elementDegree_property muln1 big_ord1 expr0 prodv1 !ltnn.
rewrite ltnNge; case/orP => [/idPn//|Hm _ _]; apply: leq_trans Hm.
by rewrite [(\sum_(i < m.+2) _)%VS]big_ord_recr addvC.
Qed.

Lemma elemDeg1_subproof : x \in K -> elementDegree K x = 1%N.
Proof.
rewrite /elementDegree.
case: ex_minnP => [[|m _ Hm xK]].
  by rewrite /elementDegree_property muln1 big_ord1 expr0 prodv1 !ltnn.
apply/eqP.
rewrite eqSS -leqn0 -ltnS Hm // /elementDegree_property.
rewrite !big_ord_recl big_ord0 expr1 expr0 addv0 prodv1.
apply/orP; right.
apply (@leq_trans (\dim K).+1).
  rewrite ltnS dimvS // subv_add subv_refl (subv_trans _ (asubv K)) //.
  by rewrite prodvSr.
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
rewrite {}sumUniq; try by move=> i; rewrite memv_prod ?memv_line ?pK ?qK.
move/forall_inP => Hpq; apply/polyP => i.
apply: (mulIf (expf_neq0 i nzx)).
case: (leqP (elementDegree K x) i) => Hi; last first.
  by apply/eqP; apply (Hpq (Ordinal Hi)).
by rewrite (_ : p`_i = 0) ?mul0r; first rewrite (_ : q`_i = 0) ?mul0r //;
 move: Hi; [ move/(leq_trans szq) | move/(leq_trans szp) ];
 move/leq_sizeP; apply.
Qed.

Lemma XED_subproof : x ^+ (elementDegree K x) \in (Fadjoin K x).
case: (eqVneq x 0).
 move ->.
 by rewrite exprS mul0r mem0v.
rewrite capv_KxED_subproof.
rewrite -vpick0.
set W := (_ :&: _)%VS.
move: (memv_pick W).
rewrite memv_cap.
case/andP.
move/memv_prodv_line_coef ->.
set k := (_ / _) => Hk.
have: (k \in K).
 move: (memv_pick W).
 rewrite memv_cap.
 case/andP.
 by move/prodv_line_coefK.
rewrite -memv_inv mulf_eq0 negb_or => Hkinv.
case/andP => nzk _.
rewrite -[x ^+ _](mulKf nzk).
apply/memv_sumP.
case/memv_sumP: Hk => v_ Hv_1 Hv_2.
exists (fun i => k^-1 * v_ i) => [i _|]; last by rewrite Hv_2 -mulr_sumr.
move/(_ i isT): Hv_1 => Hv_1.
move/memv_prodv_line_coef: (Hv_1) ->.
by rewrite mulrA memv_prod ?memv_line // memv_mul // prodv_line_coefK.
Qed.

Lemma root_minPoly : root (minPoly K x) x. 
Proof. by rewrite root_minPoly_subproof // XED_subproof. Qed.

Lemma minPolyxx : (minPoly K x).[x] = 0.
Proof. by move: root_minPoly; rewrite /root; move/eqP ->. Qed.

(* GG - not used !! *)
Lemma minPoly_coef0 : ((minPoly K x)`_0 == 0) = (x == 0).
Proof.
case (@eqP _ x 0) => Hx.
  move: Hx root_minPoly => ->.
  rewrite /root horner_coef size_minPoly big_ord_recl big1
          ?expr0 ?mulr1 ?addr0 // => i _.
  by rewrite exprSr !mulr0.
move: (minPoly K x) minPolyOver root_minPoly (size_minPoly K x) => p.
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
apply/andP; split; first by rewrite memv_prod ?memv_line ?pK.
rewrite [nth 0]lock /= (bigD1 ord_max) // [ord_max]lock /= -!lock in sump.
rewrite -/(elementDegree K x) addr_eq0 exprSr mulrA mulfK // in sump.
rewrite {sump}(eqP sump) memvN memv_sumr // => i _.
by rewrite exprSr mulrA (mulfK Hx) memv_prod ?memv_line ?pK.
Qed.

Lemma poly_Fadjoin v :
  reflect (exists p, p \in polyOver K /\ v = p.[x]) (v \in Fadjoin K x).
Proof.
apply: (iffP (poly_Fadjoin_small _ _ _)).
 by case => p [? ? ?]; exists p.
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
move/polyOverP => Kr szr rxED.
set q := (\poly_(i < (size p).-1) (p`_i)) + 
         (p`_(size p).-1)%:P * r * 'X ^+ ((size p).-1 - elementDegree K x).
have -> : (p.[x] = q.[x]).
 rewrite !(hornerE,hornerM).
 by rewrite -rxED hornerXn -mulrA -exprD subnKC // horner_poly horner_coef
            -(ltn_predK szpx) /= big_ord_recr.
apply IH; last first.
 apply/polyOverP => i.
 by rewrite coefD coef_poly -mulrA coefCM coefMXn !(fun_if, if_arg)
            !(mulr0, add0r, addr0) !(mem0v, memvD, memv_mul) ?Kp ?if_same.
case: n szp szpx {IH}.
 rewrite ltnS leqn0.
 by move/eqP ->.
move => n szp szpx.
rewrite ltnS.
apply: (leq_trans (size_add _ _)).
rewrite geq_max.
apply/andP; split.
 apply: (leq_trans (size_poly _ _)).
 by rewrite -2!ltnS -ltnS (ltn_predK szpx).
rewrite -mulrA.
case: (eqVneq (p`_(size p).-1) 0).
 by move ->; rewrite mul0r size_poly0.
move/size_Cmul ->.
apply (leq_trans (size_mul_leq _ _)).
rewrite size_polyXn addnS.
move: szp.
rewrite -{1}(ltn_predK szpx) !ltnS /=.
move/(leq_trans _); apply.
by rewrite -{2}(@subnKC (elementDegree K x) (size p).-1) ?leq_add2r.
Qed.

Lemma Fadjoin_is_aspace : is_aspace (Fadjoin K x).
Proof.
apply/andP; split.
 apply: has_algid1.
 apply/poly_Fadjoin.
 exists 1;split; last by rewrite hornerE.
 apply/polyOverP => i.
 rewrite coefC.
 by case: ifP; rewrite ?mem0v ?mem1v.
apply/prodvP => ? ?.
case/poly_Fadjoin => p1 [Hp1 ->].
case/poly_Fadjoin => p2 [Hp2 ->].
apply/poly_Fadjoin.
by exists (p1 * p2); rewrite hornerM; split => //; rewrite rpredM.
Qed.
Canonical Fadjoin_aspace : {subfield L} := ASpace Fadjoin_is_aspace.

Lemma subsetFadjoinE E : (K <= E)%VS && (x \in E) = (Fadjoin K x <= E)%VS.
Proof.
apply/idP/idP.
  case/andP => KE xE.
  apply/subv_sumP => i _.
  apply: (subv_trans _ (asubv _)).
  apply: (subv_trans (prodvSl _ _) (prodvSr _ _)) => //.
  by apply: memv_exp.
move => HFxE.
apply/andP; split; apply: (subv_trans _ HFxE).
  by rewrite /Fadjoin big_ord_recl expr0 prodv1 addvSl.
move: XED_subproof; rewrite /Fadjoin /elementDegree exprS.
case: _.-1 => [|d _]; first by rewrite expr0 mulr1.
rewrite !big_ord_recl.
apply: (subv_trans _ (addvSr _ _)).
apply: (subv_trans _ (addvSl _ _)).
by rewrite -{1}[<[x]>%VS]prod1v prodvSl // sub1v.
Qed.

Lemma memx_Fadjoin : x \in Fadjoin K x.
Proof.
by move: (subv_refl (Fadjoin K x)); rewrite -subsetFadjoinE; case/andP.
Qed.

Lemma subsetKFadjoin : (K <= Fadjoin K x)%VS.
Proof.
by move: (subv_refl (Fadjoin K x)); rewrite -subsetFadjoinE; case/andP.
Qed.

Lemma memK_Fadjoin y : y \in K -> y \in Fadjoin K x.
Proof. exact/subvP/subsetKFadjoin. Qed.

Lemma mempx_Fadjoin p : p \is a polyOver K -> p.[x] \in Fadjoin K x.
Proof. by move=> pK; apply/poly_Fadjoin; exists p. Qed.

Lemma poly_for_K v : v \in K -> poly_for_Fadjoin K x v = v%:P.
Proof.
move=> vK.
apply: poly_Fadjoin_small_uniq.
- exact: poly_for_polyOver.
- by rewrite polyOverC.
- exact: size_poly_for.
- by rewrite size_polyC (leq_trans (leq_b1 _)).
by rewrite hornerC poly_for_eq // memK_Fadjoin.
Qed.

Lemma poly_for_modp p :
  p \is a polyOver K -> poly_for_Fadjoin K x p.[x] = p %% minPoly K x.
Proof.
move=> Pk.
apply: poly_Fadjoin_small_uniq.
- exact: poly_for_polyOver.
- by rewrite modp_polyOver // minPolyOver.
- exact: size_poly_for.
- by rewrite -ltnS -size_minPoly ltn_modp // -size_poly_eq0 size_minPoly.
rewrite poly_for_eq ?mempx_Fadjoin // {1}(divp_eq p (minPoly K x)).
by rewrite hornerD hornerM minPolyxx mulr0 add0r.
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
case: (negP (@oner_neq0 L)).
by rewrite -memv0 -K0 mem1v.
Qed.

Lemma size_elementDegree p :
  p \is a polyOver K -> size p <= elementDegree K x -> root p x = (p == 0).
Proof.
rewrite /root => Kp szp.
apply/eqP/eqP => Hp; last by rewrite Hp horner0.
by apply: poly_Fadjoin_small_uniq; rewrite ?polyOver0 ?size_poly0 ?horner0.
Qed. 

Lemma minPoly_irr p :
  p \is a polyOver K -> p %| (minPoly K x) -> (p %= minPoly K x) || (p %= 1).
Proof.
rewrite /dvdp => Kp /eqP pMin.
pose q := minPoly K x %/ p.
have Kq : q \is a polyOver K by rewrite divp_polyOver // minPolyOver.
move: root_minPoly (size_minPoly K x).
have -> : minPoly K x = q * p.
  by apply/eqP; rewrite -dvdp_eq; apply/modp_eq0P.
move: q Kq => q Kq.
rewrite {pMin} /root hornerM mulf_eq0 => pq0 szpq.
have nzp: p != 0.
 move/eqP: szpq.
 apply: contraL.
 move/eqP ->.
 by rewrite mulr0 size_poly0.
have nzq: q != 0.
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
rewrite -size_poly_eq1 eqn_leq.
apply/andP; split; last by rewrite (polySpred nzp).
rewrite -(leq_add2r (size q)).
move: (size_mul nzp nzq); case: (_ + _)%N=> //= _ <-.
rewrite mulrC szpq ltnNge.
apply: contra nzq.
by move/(size_elementDegree Kq) <-.
Qed.

Lemma minPoly_dvdp p : p \is a polyOver K -> root p x -> (minPoly K x) %| p.
Proof.
move=> Kp rootp.
have gcdK : gcdp (minPoly K x) p \is a polyOver K.
 by rewrite gcdp_polyOver ?minPolyOver //.
have [gcd_eqK|gcd_eq1] := orP (minPoly_irr gcdK (dvdp_gcdl (minPoly K x) p)).
 by rewrite -(eqp_dvdl _ gcd_eqK) dvdp_gcdr.
case/negP: (root1 x).
by rewrite -(eqp_root gcd_eq1) root_gcd rootp root_minPoly.
Qed.

End Fadjoin.

Section GenField.

Implicit Types rs : seq L.

Lemma poly_for_X K z : z \notin K -> poly_for_Fadjoin K z z = 'X.
Proof.
move=> K'z; rewrite -{2}[z]hornerX poly_for_modp ?polyOverX ?modp_small //.
by rewrite size_minPoly ltnS size_polyX ltn_neqAle eq_sym andbT -elemDeg1.
Qed.

Definition genField V rs := foldl Fadjoin V rs.

Fact genField_is_aspace K rs : is_aspace (genField K rs).
Proof. by elim: rs K => [|z rs IHrs] K; [exact: (valP K) | exact: IHrs]. Qed.
Canonical genField_aspace K rs := ASpace (genField_is_aspace K rs).

Lemma genField_rcons V rs z :
  genField V (rcons rs z) = Fadjoin (genField V rs) z.
Proof. by rewrite -cats1 /genField foldl_cat. Qed.

Lemma genFieldP {K rs E} :
  reflect (K <= E /\ {subset rs <= E})%VS (genField K rs <= E)%VS.
Proof.
elim: rs K => [|z rs IHrs] K /=; first by apply: (iffP idP) => // [[]].
apply: (equivP (IHrs _)); rewrite -subsetFadjoinE.
split=> [[/andP[-> Ez] /allP Ers] | [-> /allP/=/andP[-> /allP//]]].
by split=> //; exact/allP/andP.
Qed.

Lemma sub_genField K rs : (K <= genField K rs)%VS.
Proof. by have /genFieldP[] := subv_refl (genField K rs). Qed.

Lemma mem_genField K rs : {subset rs <= genField K rs}.
Proof. by have /genFieldP[] := subv_refl (genField K rs). Qed.

Lemma genFieldSl K E rs : (K <= E)%VS -> (genField K rs <= genField E rs)%VS.
Proof.
move=> sKE; apply/genFieldP; split; last exact: mem_genField.
exact: subv_trans sKE (sub_genField E rs).
Qed.

Lemma genFieldSr K rs1 rs2 :
  {subset rs1 <= rs2} -> (genField K rs1 <= genField K rs2)%VS.
Proof.
move=> s_rs12; apply/genFieldP; split=> [|z /s_rs12]; first exact: sub_genField.
exact: mem_genField.
Qed.

Lemma subv_genField K E : (K <= E)%VS -> {s | E = genField K s :> {vspace L}}.
Proof.
elim: _.+1 {-2}K (ltnSn (\dim E - \dim K)) => // n IHn F1 geFn sF1E.
have [sEF1 | ltF1E] := boolP (E <= F1)%VS.
  by exists [::]; apply/eqP; rewrite eqEsubv sEF1.
have /sig2W[v Ev F1'v] := subvPn ltF1E.
have [||s ->] := IHn (Fadjoin_aspace F1 v); last by exists (v :: s).
  rewrite -ltnS (leq_trans _ geFn) // ltnS ltn_sub2l //.
    by rewrite (ltn_leqif (dimv_leqif_sup sF1E)).
  rewrite dim_Fadjoin ltn_Pmulr ?adim_gt0 // ltn_neqAle eq_sym.
  by rewrite -elemDeg1 F1'v.
by rewrite -subsetFadjoinE sF1E.
Qed.

End GenField.

Section Horner.

Variables z : L.

Definition fieldExt_horner := horner_morph (fun x => mulrC z (in_alg L x)).
Canonical fieldExtHorner_additive := [additive of fieldExt_horner].
Canonical fieldExtHorner_rmorphism := [rmorphism of fieldExt_horner].
Lemma fieldExt_hornerC b : fieldExt_horner b%:P = b%:A.
Proof. exact: horner_morphC. Qed.
Lemma fieldExt_hornerX : fieldExt_horner 'X = z.
Proof. exact: horner_morphX. Qed.
Fact fieldExt_hornerZ : scalable fieldExt_horner.
Proof.
move=> a p; rewrite -mul_polyC rmorphM /= fieldExt_hornerC.
by rewrite -scalerAl mul1r.
Qed.
Canonical fieldExt_horner_linear := AddLinear fieldExt_hornerZ.
Canonical fieldExt_horner_lrmorhism := [lrmorphism of fieldExt_horner].

End Horner.

End FieldExtTheory.

Prenex Implicits Fadjoin.
Implicit Arguments genFieldP [F0 L K rs E].

Notation "E :&: F" := (capv_aspace E F) : aspace_scope.
Notation "E * F" := (prodv_aspace E F) : aspace_scope.

(* Changing up the reference field of a fieldExtType. *)
Section FieldOver.

Variables (F0 : fieldType) (L : fieldExtType F0) (F : {subfield L}).

Definition fieldOver of {vspace L} : Type := L.
Local Notation K_F := (subvs_of F).
Local Notation L_F := (fieldOver F).

Canonical fieldOver_eqType := [eqType of L_F].
Canonical fieldOver_choiceType := [choiceType of L_F].
Canonical fieldOver_zmodType := [zmodType of L_F].
Canonical fieldOver_ringType := [ringType of L_F].
Canonical fieldOver_unitRingType := [unitRingType of L_F].
Canonical fieldOver_comRingType := [comRingType of L_F].
Canonical fieldOver_comUnitRingType := [comUnitRingType of L_F].
Canonical fieldOver_idomainType := [idomainType of L_F].
Canonical fieldOver_fieldType := [fieldType of L_F].

Definition fieldOver_scale (a : K_F) (u : L_F) : L_F := vsval a * u.
Local Infix "*F:" := fieldOver_scale (at level 40).

Fact fieldOver_scaleA a b u : a *F: (b *F: u) = (a * b) *F: u.
Proof. exact: mulrA. Qed.

Fact fieldOver_scale1 u : 1 *F: u = u.
Proof. by rewrite /(1 *F: u) /= algid1 mul1r. Qed.

Fact fieldOver_scaleDr a u v : a *F: (u + v) = a *F: u + a *F: v.
Proof. exact: mulrDr. Qed.

Fact fieldOver_scaleDl v a b : (a + b) *F: v = a *F: v + b *F: v.
Proof. exact: mulrDl. Qed.

Definition fieldOver_lmodMixin :=
  LmodMixin fieldOver_scaleA fieldOver_scale1
            fieldOver_scaleDr fieldOver_scaleDl.

Canonical fieldOver_lmodType := LmodType K_F L_F fieldOver_lmodMixin.

Lemma fieldOver_scaleE a (u : L) : a *: (u : L_F) = vsval a * u.
Proof. by []. Qed.

Fact fieldOver_scaleAl a u v : a *F: (u * v) = (a *F: u) * v.
Proof. exact: mulrA. Qed.

Canonical fieldOver_lalgType := LalgType K_F L_F fieldOver_scaleAl.

Fact fieldOver_scaleAr a u v : a *F: (u * v) = u * (a *F: v).
Proof. exact: mulrCA. Qed.

Canonical fieldOver_algType := AlgType K_F L_F fieldOver_scaleAr.
Canonical fieldOver_unitAlgType := [unitAlgType K_F of L_F].

Fact fieldOver_vectMixin : Vector.mixin_of fieldOver_lmodType.
Proof.
have [bL [_ nz_bL _] [defL dxSbL]] := field_ideal_semisimple (subvf (F * _)%VS).
set n := (_ %/ _)%N in bL nz_bL defL dxSbL.
set SbL := (\sum_i _)%VS in defL dxSbL.
have in_bL i (a : K_F) : val a * (bL`_i : L_F) \in (F * <[bL`_i]>)%VS.
  by rewrite memv_prod ?(valP a) ?memv_line.
have nz_bLi (i : 'I_n): bL`_i != 0 by rewrite (memPn nz_bL) ?memt_nth.
pose r2v (v : 'rV[K_F]_n) : L_F := \sum_i v 0 i *: (bL`_i : L_F).
have r2v_lin: linear r2v.
  move=> a u v; rewrite /r2v scaler_sumr -big_split /=; apply: eq_bigr => i _.
  by rewrite scalerA -scalerDl !mxE.
have v2rP x: {r : 'rV[K_F]_n | x = r2v r}.
  apply: sig_eqW; have /memv_sumP[y Fy ->]: x \in SbL by rewrite defL memvf.
  have /fin_all_exists[r Dr] i: exists r, y i = r *: (bL`_i : L_F).
    by have /memv_cosetP[a Fa ->] := Fy i isT; exists (Subvs Fa).
  by exists (\row_i r i); apply: eq_bigr => i _; rewrite mxE.
pose v2r x := sval (v2rP x).
have v2rK: cancel v2r (Linear r2v_lin) by rewrite /v2r => x; case: (v2rP x).
suffices r2vK: cancel r2v v2r.
  by exists n, v2r; [exact: can2_linear v2rK | exists r2v].
move=> r; apply/rowP=> i; apply/val_inj/(mulIf (nz_bLi i))/eqP; move: i isT.
by apply/forall_inP; move/directv_sum_unique: dxSbL => <- //; exact/eqP/v2rK.
Qed.

Canonical fieldOver_vectType := VectType K_F L_F fieldOver_vectMixin.
Canonical fieldOver_FalgType := [FalgType K_F of L_F].
Canonical fieldOver_fieldExtType := [fieldExtType K_F of L_F].

Implicit Types (V : {vspace L}) (E : {subfield L}).

Definition vspaceOver V := <<vbasis V : seq L_F>>%VS.

Lemma mem_vspaceOver V : vspaceOver V =i (F * V)%VS.
Proof.
move=> y; apply/idP/idP; last rewrite prodvE; move/coord_span->.
  rewrite (@memv_suml F0 L) // => i _.
  by rewrite memv_prod ?subvsP // vbasis_mem ?memt_nth.
rewrite memv_suml // => ij _; rewrite -tnth_nth; set x := tnth _ ij.
have/allpairsP[[u z] /= [Fu Vz {x}->]]: x \in _ := mem_tnth ij _.
by rewrite scalerAl (memvZ (Subvs _)) ?memvZ ?memv_span //= vbasis_mem.
Qed.

Lemma mem_aspaceOver E : (F <= E)%VS -> vspaceOver E =i E.
Proof.
by move=> sFE y; rewrite mem_vspaceOver field_ideal_eq ?sup_field_ideal.
Qed.

Fact aspaceOver_suproof E : is_aspace (vspaceOver E).
Proof.
rewrite /is_aspace has_algid1; last by rewrite mem_vspaceOver (@mem1v _ L).
by apply/prodvP=> u v; rewrite !mem_vspaceOver; exact: memv_mul.
Qed.
Canonical aspaceOver E := ASpace (aspaceOver_suproof E).

Lemma dim_vspaceOver J : (F * J <= J)%VS -> \dim (vspaceOver J) = \dim_F J.
Proof.
move=> idealJ; have [] := field_ideal_semisimple idealJ; set n := (_ %/ _)%N.
move=> b [Jb nz_b _] [defJ dx_b].
suff: basis_of (vspaceOver J) b by exact: size_basis.
apply/andP; split.
  rewrite eqEsubv; apply/andP; split; apply/span_subvP=> u.
    by rewrite mem_vspaceOver field_ideal_eq // => /Jb.
  move/(@vbasis_mem _ _ _ J).
  rewrite -defJ => /memv_sumP[{u}u Fu ->]; apply: memv_suml => i _.
  have /memv_cosetP[a Fa ->] := Fu i isT; apply: (memvZ (Subvs Fa)).
  by rewrite memv_span ?memt_nth.
apply/freeP=> a /(directv_sum_independent dx_b) a_0 i.
have{a_0}: a i *: (b`_i : L_F) == 0.
  by rewrite a_0 {i}// => i _; rewrite memv_prod ?memv_line ?subvsP.
by rewrite scaler_eq0=> /predU1P[] // /idPn[]; rewrite (memPn nz_b) ?memt_nth.
Qed.

Lemma dim_aspaceOver E : (F <= E)%VS -> \dim (vspaceOver E) = \dim_F E.
Proof. by rewrite -sup_field_ideal; exact: dim_vspaceOver. Qed.

Lemma vspaceOverP V_F :
  {V | [/\ V_F = vspaceOver V, (F * V <= V)%VS & V_F =i V]}.
Proof.
pose V := (F * <<vbasis V_F : seq L>>)%VS.
have idV: (F * V)%VS = V by rewrite prodvA prodv_id.
suffices defVF: V_F = vspaceOver V.
  by exists V; split=> [||u]; rewrite ?defVF ?mem_vspaceOver ?idV.
apply/vspaceP=> v; rewrite mem_vspaceOver idV.
do [apply/idP/idP; last rewrite /V prodvE] => [/coord_vbasis|/coord_span] ->.
  by apply: memv_suml => i _; rewrite memv_prod ?subvsP ?memv_span ?memt_nth.
apply: memv_suml => i _; rewrite -tnth_nth; set xu := tnth _ i.
have /allpairsP[[x u] /=]: xu \in _ := mem_tnth i _.
case=> /vbasis_mem Fx /vbasis_mem Vu ->.
rewrite scalerAl (coord_span Vu) mulr_sumr memv_suml // => j_.
by rewrite -scalerCA (memvZ (Subvs _)) ?memvZ // vbasis_mem ?memt_nth.
Qed.

Lemma aspaceOverP (E_F : {subfield L_F}) :
  {E | [/\ E_F = aspaceOver E, (F <= E)%VS & E_F =i E]}.
Proof.
have [V [defEF idealV memV]] := vspaceOverP E_F.
have algE: has_algid V && (V * V <= V)%VS.
  rewrite has_algid1; last by rewrite -memV mem1v.
  by apply/prodvP=> u v; rewrite -!memV; exact: memv_mul.
by exists (ASpace algE); rewrite -sup_field_ideal; split; first exact: val_inj.
Qed.

End FieldOver.

(* Changing the reference field to a smaller field. *)
Section BaseField.

Variables (F0 : fieldType) (F : fieldExtType F0) (L : fieldExtType F).

Definition baseField_type of phant L : Type := L.
Notation L0 := (baseField_type (Phant (FieldExt.sort L))).

Canonical baseField_eqType := [eqType of L0].
Canonical baseField_choiceType := [choiceType of L0].
Canonical baseField_zmodType := [zmodType of L0].
Canonical baseField_ringType := [ringType of L0].
Canonical baseField_unitRingType := [unitRingType of L0].
Canonical baseField_comRingType := [comRingType of L0].
Canonical baseField_comUnitRingType := [comUnitRingType of L0].
Canonical baseField_idomainType := [idomainType of L0].
Canonical baseField_fieldType := [fieldType of L0].

Definition baseField_scale (a : F0) (u : L0) : L0 := in_alg F a *: u.
Local Infix "*F0:" := baseField_scale (at level 40).

Fact baseField_scaleA a b u : a *F0: (b *F0: u) = (a * b) *F0: u.
Proof. by rewrite [_ *F0: _]scalerA -rmorphM. Qed.

Fact baseField_scale1 u : 1 *F0: u = u.
Proof. by rewrite /(1 *F0: u) rmorph1 scale1r. Qed.

Fact baseField_scaleDr a u v : a *F0: (u + v) = a *F0: u + a *F0: v.
Proof. exact: scalerDr. Qed.

Fact baseField_scaleDl v a b : (a + b) *F0: v = a *F0: v + b *F0: v.
Proof. by rewrite -scalerDl -rmorphD. Qed.

Definition baseField_lmodMixin :=
  LmodMixin baseField_scaleA baseField_scale1
            baseField_scaleDr baseField_scaleDl.

Canonical baseField_lmodType := LmodType F0 L0 baseField_lmodMixin.

Lemma baseField_scaleE a (u : L) : a *: (u : L0) = a%:A *: u.
Proof. by []. Qed.

Fact baseField_scaleAl a (u v : L0) : a *F0: (u * v) = (a *F0: u) * v.
Proof. exact: scalerAl. Qed.

Canonical baseField_lalgType := LalgType F0 L0 baseField_scaleAl.

Fact baseField_scaleAr a u v : a *F0: (u * v) = u * (a *F0: v).
Proof. exact: scalerAr. Qed.

Canonical baseField_algType := AlgType F0 L0 baseField_scaleAr.
Canonical baseField_unitAlgType := [unitAlgType F0 of L0].

Let n := \dim {:F}.
Let bF : n.-tuple F := vbasis {:F}.
Let coordF (x : F) := (coord_vbasis (memvf x)).

Fact baseField_vectMixin : Vector.mixin_of baseField_lmodType.
Proof.
pose bL := vbasis {:L}; set m := \dim {:L} in bL.
pose v2r (x : L0) := mxvec (\matrix_(i, j) coord bF j (coord bL i x)).
have v2r_lin: linear v2r.
  move=> a x y; rewrite -linearP; congr (mxvec _); apply/matrixP=> i j.
  by rewrite !mxE linearP mulr_algl linearP.
pose r2v r := \sum_(i < m) (\sum_(j < n) vec_mx r i j *: bF`_j) *: bL`_i.
have v2rK: cancel v2r r2v.
  move=> x; transitivity (\sum_(i < m) coord bL i x *: bL`_i); last first.
    by rewrite -coord_vbasis ?memvf.
    (* GG: rewrite {2}(coord_vbasis (memvf x)) -/m would take 8s; *)
    (* The -/m takes 8s, and without it then apply: eq_bigr takes 12s. *)
    (* The time drops to 2s with  a -[GRing.Field.ringType F]/(F : fieldType) *)
  apply: eq_bigr => i _; rewrite mxvecK; congr (_ *: _ : L).
  by rewrite (coordF (coord bL i x)); apply: eq_bigr => j _; rewrite mxE.
exists (m * n)%N, v2r => //; exists r2v => // r.
apply: (canLR vec_mxK); apply/matrixP=> i j; rewrite mxE.
by rewrite !coord_sum_free ?(basis_free (vbasisP _)).
Qed.

Canonical baseField_vectType := VectType F0 L0 baseField_vectMixin.
Canonical baseField_FalgType := [FalgType F0 of L0].
Canonical baseField_extFieldType := [fieldExtType F0 of L0].

Let F0ZEZ a x v : a *: ((x *: v : L) : L0)  = (a *: x) *: v.
Proof. by rewrite [a *: _]scalerA -scalerAl mul1r. Qed.

Let baseVspace_basis V : seq L0 :=
  [image tnth bF ij.2 *: tnth (vbasis V) ij.1 | ij <- predT].
Definition baseVspace V := <<baseVspace_basis V>>%VS.

Lemma mem_baseVspace V : baseVspace V =i V.
Proof.
move=> y; apply/idP/idP=> [/coord_span->|/coord_vbasis->]; last first.
  apply: memv_suml => i _; rewrite (coordF (coord _ i (y : L))) scaler_suml -/n.
  apply: memv_suml => j _; rewrite -/bF -F0ZEZ memvZ ?memv_span // -!tnth_nth.
  by apply/imageP; exists (i, j).
  (* GG: the F0ZEZ lemma avoids serious performance issues here. *)
apply: memv_suml => k _; rewrite nth_image; case: (enum_val k) => i j /=.
by rewrite F0ZEZ memvZ ?vbasis_mem ?mem_tnth.
Qed.

Lemma dim_baseVspace V : \dim (baseVspace V) = (\dim V * n)%N.
Proof.
pose bV0 := baseVspace_basis V; set m := \dim V in bV0 *.
suffices /size_basis->: basis_of (baseVspace V) bV0.
  by rewrite card_prod !card_ord.
rewrite /basis_of eqxx.
apply/freeP=> s sb0 k; rewrite -(enum_valK k); case/enum_val: k => i j.
have free_baseP := freeP (basis_free (vbasisP _)).
move: j; apply: (free_baseP _ _ fullv); move: i; apply: (free_baseP _ _ V).
transitivity (\sum_i \sum_j s (enum_rank (i, j)) *: bV0`_(enum_rank (i, j))).
  apply: eq_bigr => i _; rewrite scaler_suml; apply: eq_bigr => j _.
  by rewrite -F0ZEZ nth_image enum_rankK -!tnth_nth.
rewrite pair_bigA (reindex _ (onW_bij _ (enum_val_bij _))); apply: etrans sb0.
by apply: eq_bigr => k _; rewrite -{5 6}[k](enum_valK k); case/enum_val: k.
Qed.

Fact baseAspace_suproof (E : {subfield L}) : is_aspace (baseVspace E).
Proof.
rewrite /is_aspace has_algid1; last by rewrite mem_baseVspace (mem1v E).
by apply/prodvP=> u v; rewrite !mem_baseVspace; exact: memv_mul.
Qed.
Canonical baseAspace E := ASpace (baseAspace_suproof E).

Definition refBaseField := locked (baseAspace 1).
Notation F1 := refBaseField.

Lemma dim_refBaseField : \dim F1 = n.
Proof. by unlock F1; rewrite dim_baseVspace dimv1 mul1n. Qed.

Lemma baseVspace_ideal V (V0 := baseVspace V) : (F1 * V0 <= V0)%VS.
Proof.
apply/prodvP=> u v; unlock F1; rewrite !mem_baseVspace => /vlineP[x ->] Vv.
by rewrite -(@scalerAl F L) mul1r; exact: memvZ.
Qed.

Lemma sub_baseField (E : {subfield L}) : (F1 <= baseVspace E)%VS.
Proof. by rewrite -sup_field_ideal baseVspace_ideal. Qed.

Lemma vspaceOver_refBase V : vspaceOver F1 (baseVspace V) =i V.
Proof.
move=> v; rewrite mem_vspaceOver field_ideal_eq ?baseVspace_ideal //.
by rewrite mem_baseVspace.
Qed.

Lemma ideal_baseVspace J0 :
  (F1 * J0 <= J0)%VS -> {V | J0 = baseVspace V & J0 =i V}.
Proof.
move=> J0ideal; pose V := <<vbasis (vspaceOver F1 J0) : seq L>>%VS.
suffices memJ0: J0 =i V.
  by exists V => //; apply/vspaceP=> v; rewrite mem_baseVspace memJ0.
move=> v; rewrite -{1}(field_ideal_eq J0ideal) -(mem_vspaceOver J0) {}/V.
move: (vspaceOver F1 J0) => J.
apply/idP/idP=> [/coord_vbasis|/coord_span]->; apply/memv_suml=> i _.
  rewrite /(_ *: _) /= /fieldOver_scale; case: (coord _ i _) => /= x.
  unlock {1}F1; rewrite mem_baseVspace => /vlineP[{x}x ->].
  by rewrite -(@scalerAl F L) mul1r memvZ ?memv_span ?memt_nth.
move: (coord _ i _) => x; rewrite -[_`_i]mul1r scalerAl -tnth_nth.
have F1x: x%:A \in F1.
  by unlock F1; rewrite mem_baseVspace (@memvZ F L) // mem1v.
by congr (_ \in J): (memvZ (Subvs F1x) (vbasis_mem (mem_tnth i _))).
Qed.

Lemma ideal_baseAspace (E0 : {subfield L0}) :
  (F1 <= E0)%VS -> {E | E0 = baseAspace E & E0 =i E}.
Proof.
rewrite -sup_field_ideal => /ideal_baseVspace[E defE0 memE0].
suffices algE: has_algid E && (E * E <= E)%VS.
  by exists (ASpace algE); first exact: val_inj.
rewrite has_algid1 -?memE0 ?mem1v //.
by apply/prodvP=> u v; rewrite -!memE0; exact: memv_mul.
Qed.

End BaseField.

Notation baseFieldType L := (baseField_type (Phant L)).

(* Base of fieldOver, finally. *)
Section MoreFieldOver.

Variables (F0 : fieldType) (L : fieldExtType F0) (F : {subfield L}).

Lemma base_vspaceOver V : baseVspace (vspaceOver F V) =i (F * V)%VS.
Proof. by move=> v; rewrite mem_baseVspace mem_vspaceOver. Qed.

Lemma base_idealOver V : (F * V <= V)%VS -> baseVspace (vspaceOver F V) =i V.
Proof. by move=> /field_ideal_eq defV v; rewrite base_vspaceOver defV. Qed.

Lemma base_aspaceOver (E : {subfield L}) :
  (F <= E)%VS -> baseVspace (vspaceOver F E) =i E.
Proof. by rewrite -sup_field_ideal; exact: base_idealOver. Qed.

End MoreFieldOver.

Lemma irredp_FAdjoin (F : fieldType) (p : {poly F}) :
    irreducible_poly p ->
  {L : fieldExtType F & \dim {:L} = (size p).-1 &
    {z | root (map_poly (in_alg L) p) z & Fadjoin 1 z = fullv}}.
Proof.
case=> p_gt1 irr_p; set n := (size p).-1; pose vL := [vectType F of 'rV_n].
have Dn: n.+1 = size p := ltn_predK p_gt1.
have nz_p: p != 0 by rewrite -size_poly_eq0 -Dn.
suffices [L dimL [toPF [toL toPF_K toL_K]]]:
   {L : fieldExtType F & \dim {:L} = (size p).-1
      & {toPF : {linear L -> {poly F}} & {toL : {lrmorphism {poly F} -> L} |
         cancel toPF toL & forall q, toPF (toL q) = q %% p}}}.
- exists L => //; pose z := toL 'X; set iota := in_alg _.
  suffices q_z q: toPF (map_poly iota q).[z] = q %% p.
    exists z; first by rewrite /root -(can_eq toPF_K) q_z modpp linear0.
    apply/vspaceP=> x; rewrite memvf; apply/poly_Fadjoin.
    exists (map_poly iota (toPF x)); split.
      by apply/polyOverP=> i; rewrite coef_map memvZ ?mem1v.
    by apply: (can_inj toPF_K); rewrite q_z -toL_K toPF_K.
  elim/poly_ind: q => [|a q IHq].
    by rewrite map_poly0 horner0 linear0 mod0p.
  rewrite rmorphD rmorphM /= map_polyX map_polyC hornerMXaddC linearD /=.
  rewrite linearZ /= -(rmorph1 toL) toL_K -modp_scalel scale_poly1 modp_add.
  congr (_ + _); rewrite -toL_K rmorphM /= -/z; congr (toPF (_ * z)).
  by apply: (can_inj toPF_K); rewrite toL_K. 
pose toL q : vL := poly_rV (q %% p); pose toPF (x : vL) := rVpoly x.
have toL_K q : toPF (toL q) = q %% p.
  by rewrite /toPF poly_rV_K // -ltnS Dn ?ltn_modp -?Dn.
have toPF_K: cancel toPF toL.
  by move=> x; rewrite /toL modp_small ?rVpolyK // -Dn ltnS size_poly.
have toPinj := can_inj toPF_K.
pose mul x y := toL (toPF x * toPF y); pose L1 := toL 1.
have L1K: toPF L1 = 1 by rewrite toL_K modp_small ?size_poly1.
have mulC: commutative mul by rewrite /mul => x y; rewrite mulrC.
have mulA: associative mul.
  by move=> x y z; apply: toPinj; rewrite -!(mulC z) !toL_K !modp_mul mulrCA.
have mul1: left_id L1 mul.
  move=> x; apply: toPinj.
  by rewrite mulC !toL_K modp_mul mulr1 -toL_K toPF_K.
have mulD: left_distributive mul +%R.
  move=> x y z; apply: toPinj; rewrite /toPF raddfD /= -!/(toPF _).
  by rewrite !toL_K /toPF raddfD mulrDl modp_add.
have nzL1: L1 != 0 by rewrite -(inj_eq toPinj) L1K /toPF raddf0 oner_eq0. 
pose mulM := ComRingMixin mulA mulC mul1 mulD nzL1.
pose rL := ComRingType (RingType vL mulM) mulC.
have mulZl: GRing.Lalgebra.axiom mul.
  move=> a x y; apply: toPinj; rewrite  toL_K /toPF !linearZ /= -!/(toPF _).
  by rewrite toL_K -scalerAl modp_scalel.
have mulZr: @GRing.Algebra.axiom _ (LalgType F rL mulZl).
  by move=> a x y; rewrite !(mulrC x) scalerAl.
pose aL := AlgType F _ mulZr; pose urL := FalgUnitRingType aL.
pose uaL := [unitAlgType F of AlgType F urL mulZr].
pose faL := [FalgType F of uaL].
have unitE: GRing.Field.mixin_of urL.
  move=> x nz_x; apply/unitrP; set q := toPF x.
  have nz_q: q != 0 by rewrite -(inj_eq toPinj) /toPF raddf0 in nz_x.
  have /Bezout_eq1_coprimepP[u upq1]: coprimep p q.
    apply: contraLR (leq_gcdpr p nz_q) => /irr_p/implyP.
    rewrite dvdp_gcdl -ltnNge /= => /eqp_size->.
    by rewrite (polySpred nz_p) ltnS size_poly.
  suffices: x * toL u.2 = 1 by exists (toL u.2); rewrite mulrC.
  apply: toPinj; rewrite !toL_K -upq1 modp_mul modp_add mulrC.
  by rewrite modp_mull add0r.
pose ucrL := [comUnitRingType of ComRingType urL mulC].
have mul0 := GRing.Field.IdomainMixin unitE.
pose fL := FieldType (IdomainType ucrL mul0) unitE.
exists [fieldExtType F of faL for fL]; first by rewrite dimvf; exact: mul1n.
exists [linear of toPF as @rVpoly _ _].
suffices toLM: lrmorphism (toL : {poly F} -> aL) by exists (LRMorphism toLM).
have toLlin: linear toL.
  by move=> a q1 q2; rewrite -linearP -modp_scalel -modp_add.
do ?split; try exact: toLlin; move=> q r /=.
by apply: toPinj; rewrite !toL_K modp_mul -!(mulrC r) modp_mul.
Qed.

(* Coq 8.3 processes this shorter proof correctly, but then crashes on Qed.
Lemma irredp_FAdjoin (F : fieldType) (p : {poly F}) :
    irreducible_poly p ->
  {L : fieldExtType F & Vector.dim L = (size p).-1 &
    {z | root (map_poly (in_alg L) p) z & Fadjoin 1 z = fullv}}.
Proof.
case=> p_gt1 irr_p; set n := (size p).-1; pose vL := [vectType F of 'rV_n].
have Dn: n.+1 = size p := ltn_predK p_gt1.
have nz_p: p != 0 by rewrite -size_poly_eq0 -Dn.
pose toL q : vL := poly_rV (q %% p).
have toL_K q : rVpoly (toL q) = q %% p.
  by rewrite poly_rV_K // -ltnS Dn ?ltn_modp -?Dn.
pose mul (x y : vL) : vL := toL (rVpoly x * rVpoly y).
pose L1 : vL := poly_rV 1.
have L1K: rVpoly L1 = 1 by rewrite poly_rV_K // size_poly1 -ltnS Dn.
have mulC: commutative mul by rewrite /mul => x y; rewrite mulrC.
have mulA: associative mul.
  by move=> x y z; rewrite -!(mulC z) /mul !toL_K /toL !modp_mul mulrCA.
have mul1: left_id L1 mul.
  move=> x; rewrite /mul L1K mul1r /toL modp_small ?rVpolyK // -Dn ltnS.
  by rewrite size_poly.
have mulD: left_distributive mul +%R.
  move=> x y z; apply: canLR (@rVpolyK _ _) _.
  by rewrite !raddfD mulrDl /= !toL_K /toL modp_add.
have nzL1: L1 != 0 by rewrite -(can_eq (@rVpolyK _ _)) L1K raddf0 oner_eq0.
pose mulM := ComRingMixin mulA mulC mul1 mulD nzL1.
pose rL := ComRingType (RingType vL mulM) mulC.
have mulZl: GRing.Lalgebra.axiom mul.
  move=> a x y; apply: canRL (@rVpolyK _ _) _; rewrite !linearZ /= toL_K.
  by rewrite -scalerAl modp_scalel.
have mulZr: @GRing.Algebra.axiom _ (LalgType F rL mulZl).
  by move=> a x y; rewrite !(mulrC x) scalerAl.
pose aL := AlgType F _ mulZr; pose urL := FalgUnitRingType aL.
pose uaL := [unitAlgType F of AlgType F urL mulZr].
pose faL := [FalgType F of uaL].
have unitE: GRing.Field.mixin_of urL.
  move=> x nz_x; apply/unitrP; set q := rVpoly x.
  have nz_q: q != 0 by rewrite -(can_eq (@rVpolyK _ _)) raddf0 in nz_x.
  have /Bezout_eq1_coprimepP[u upq1]: coprimep p q.
    have /orP[|/eqp_size sz_pq] := irr_p _ (dvdp_gcdl p q).
      by rewrite -size_poly_eq1.
    have: size (gcdp p q) <= size q by exact: leq_gcdpr. 
    by rewrite sz_pq leqNgt (polySpred nz_p) ltnS size_poly.
  suffices: x * toL u.2 = 1 by exists (toL u.2); rewrite mulrC.
  congr (poly_rV _); rewrite toL_K modp_mul mulrC (canRL (addKr _) upq1).
  by rewrite -mulNr modp_addl_mul_small ?size_poly1.
pose ucrL := [comUnitRingType of ComRingType urL mulC].
pose fL := FieldType (IdomainType ucrL (GRing.Field.IdomainMixin unitE)) unitE.
exists [fieldExtType F of faL for fL]; first exact: mul1n.
pose z : vL := toL 'X; set iota := in_alg _.
have q_z q: rVpoly (map_poly iota q).[z] = q %% p.
  elim/poly_ind: q => [|a q IHq].
    by rewrite map_poly0 horner0 linear0 mod0p.
  rewrite rmorphD rmorphM /= map_polyX map_polyC hornerMXaddC linearD /=.
  rewrite linearZ /= L1K scale_poly1 modp_add; congr (_ + _); last first.
    by rewrite modp_small // size_polyC; case: (~~ _) => //; apply: ltnW.
  by rewrite !toL_K IHq mulrC modp_mul mulrC modp_mul.
exists z; first by rewrite /root -(can_eq (@rVpolyK _ _)) q_z modpp linear0.
apply/vspaceP=> x; rewrite memvf; apply/poly_Fadjoin.
exists (map_poly iota (rVpoly x)); split.
  by apply/polyOverP=> i; rewrite coef_map memvZ ?mem1v.
apply: (can_inj (@rVpolyK _ _)).
by rewrite q_z modp_small // -Dn ltnS size_poly.
Qed.
*)