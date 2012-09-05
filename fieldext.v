(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
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
(*            minPoly K x == the monic minimal polynomial of x over the       *)
(*                           subfield K.                                      *)
(*      elementDegree K x == the degree of the minimial polynomial or the     *)
(*                           dimension of K(x)/K.                             *)
(* poly_for_Fadjoin K x y == a polynomial p over K such that y = p.[x].       *)
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
          Cm) b) IDm) Fm) => Pack phR (@Class T b Cm IDm Fm) T.

Definition pack_eta K :=
  let cK := Field.class K in let Cm := ComRing.mixin cK in
  let IDm := IntegralDomain.mixin cK in let Fm := Field.mixin cK in
  fun (bT : Falgebra.type phR) b & phant_id (Falgebra.class bT) b =>
  fun cT_ & phant_id (@Class T b) cT_ => @Pack phR T (cT_ Cm IDm Fm) T.

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
(*Notation "[ 'fieldExtType' F 'of' L 'for' K ]" :=
  (@FieldExt.pack _ (Phant F) L _ _ id K _ _ _ idfun)
  (at level 0, format "[ 'fieldExtType'  F  'of'  L  'for'  K ]") : form_scope.
*)
Notation "[ 'fieldExtType' F 'of' L 'for' K ]" :=
  (@pack_eta _ (Phant F) L K _ _ id _ id)
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

Lemma algid1 K : algid K = 1.
Proof. by apply: (mulIf (algid_neq0 K)); rewrite mul1r algidl ?memv_algid. Qed.

Lemma mem1v K : 1 \in K. Proof. by rewrite -(algid1 K) memv_algid. Qed.
Lemma sub1v K : (1 <= K)%VS. Proof. exact: mem1v. Qed.

Lemma subfield_closed K : <<K>>%AS = K.
Proof.
apply: subv_anti.
rewrite subv_closure andbT.
rewrite closureaEl subv_add sub1v closurea_idealr //.
by rewrite prodv_id subvv.
Qed.

Fact ahom_img_is_aspace (aT : FalgType F0) (f : 'AHom(L, aT)) K :
   let Kf := (f @: K)%VS in
   has_algid Kf && (Kf * Kf <= Kf)%VS.
Proof.
apply/andP; split.
  apply/has_algidP; exists (f 1); split.
  - by rewrite memv_img // mem1v.
  - by rewrite rmorph1 oner_neq0.
  - move => u Hu /=.
    by rewrite rmorph1 mulr1 mul1r.
apply/prodvP => _ _ /memv_imgP [a Ha ->] /memv_imgP [b Hb ->].
by rewrite -rmorphM memv_img // memv_mul.
Qed.
Canonical ahom_img_aspace (aT : FalgType F0) (f : 'AHom(L, aT)) K : {aspace aT}
  := Eval hnf in ASpace (ahom_img_is_aspace f K).

Lemma memv_adjoin_eq K x : (x \in K) = (<<K; x>>%AS == K).
Proof.
apply/idP/eqP; first by move/addv_idPl ->; apply subfield_closed.
by move <-; apply: memv_adjoin.
Qed.

Lemma Fadjoin_nil K : <<K & [::]>>%AS = K.
Proof. by rewrite adjoin_nil subfield_closed. Qed.

Lemma FadjoinP K x E :
  reflect (K <= E /\ x \in E)%VS (<<K; x>>%AS <= E)%VS.
Proof.
apply: (iffP idP).
  move => H.
  rewrite memvE !(subv_trans _ H) ?subv_adjoin //.
  by apply: memv_adjoin.
move/andP.
rewrite -subv_add -[X in (<<_>>%AS <= X)%VS]subfield_closed.
apply: closureaS.
Qed.

Lemma Fadjoin_seqP K (rs : seq L) E :
  reflect (K <= E /\ {subset rs <= E})%VS (<<K & rs>>%AS <= E)%VS.
Proof.
apply: (iffP idP).
  move => H; split; first by apply: (subv_trans (subv_adjoin_seq _ _) H).
  move => x /(seqv_sub_adjoin K); move: x.
  by move/subvP: H; apply.
case => HKE /span_subvP/(conj HKE)/andP.
rewrite -subv_add -[X in (<<_>>%AS <= X)%VS]subfield_closed.
apply: closureaS.
Qed.

Fact vsval_multiplicative K : multiplicative (vsval : subvs_of K -> L).
Proof. by split => //=; exact: algid1. Qed.
Canonical vsval_rmorphism K := AddRMorphism (vsval_multiplicative K).
Canonical vsval_lrmorphism K := [lrmorphism of (vsval : subvs_of K -> L)].

Lemma vsval_invf K (w : subvs_of K) : val w^-1 = (vsval w)^-1.
Proof.
have [-> | Uv] := eqVneq w 0; first by rewrite !invr0.
by apply: vsval_invr; rewrite unitfE.
Qed.

Fact aspace_divr_closed K : divr_closed K.
Proof.
split=> [|u v Ku Kv]; first exact: mem1v.
by rewrite -(vsval_invf (Subvs Kv)) memv_mul ?subvsP. 
Qed.
Canonical aspace_mulrPred K := MulrPred (aspace_divr_closed K).
Canonical aspace_divrPred K := DivrPred (aspace_divr_closed K).
Canonical aspace_smulrPred K := SmulrPred (aspace_divr_closed K).
Canonical aspace_sdivrPred K := SdivrPred (aspace_divr_closed K).
Canonical aspace_semiringPred K := SemiringPred (aspace_divr_closed K).
Canonical aspace_subringPred K := SubringPred (aspace_divr_closed K).
Canonical aspace_subalgPred K := SubalgPred (memv_submod_closed K).
Canonical aspace_divringPred K := DivringPred (aspace_divr_closed K).
Canonical aspace_divalgPred K := DivalgPred (memv_submod_closed K).

Definition subvs_mulC K := [comRingMixin of subvs_of K by <:].
Canonical subvs_comRingType K :=
  Eval hnf in ComRingType (subvs_of K) (@subvs_mulC K).
Canonical subvs_comUnitRingType K :=
  Eval hnf in [comUnitRingType of subvs_of K].
Definition subvs_mul_eq0 K := [idomainMixin of subvs_of K by <:].
Canonical subvs_idomainType K :=
  Eval hnf in IdomainType (subvs_of K) (@subvs_mul_eq0 K).
Lemma subvs_fieldMixin K : GRing.Field.mixin_of (@subvs_idomainType K).
Proof.
by move=> w nz_w; rewrite unitrE -val_eqE /= vsval_invf algid1 divff.
Qed.
Canonical subvs_fieldType K :=
  Eval hnf in FieldType (subvs_of K) (@subvs_fieldMixin K).
Canonical subvs_fieldExtType K := Eval hnf in [fieldExtType F0 of subvs_of K].

Lemma polyOver_subvs K (p : {poly L}) :
  reflect (exists q : {poly subvs_of K}, p = map_poly vsval q)
          (p \is a polyOver K).
Proof.
apply: (iffP polyOverP) => [Hp | [q ->] i]; last by rewrite coef_map // subvsP.
exists (\poly_(i < size p) (Subvs (Hp i))); rewrite -{1}[p]coefK.
by apply/polyP => i; rewrite coef_map !coef_poly; case: ifP.
Qed.

Lemma divp_polyOver K : {in polyOver K &, forall p q, p %/ q \is a polyOver K}.
Proof.
move=> _ _ /polyOver_subvs[p ->] /polyOver_subvs[q ->].
by apply/polyOver_subvs; exists (p %/ q); rewrite map_divp.
Qed.

Lemma modp_polyOver K : {in polyOver K &, forall p q, p %% q \is a polyOver K}.
Proof.
move=> _ _ /polyOver_subvs[p ->] /polyOver_subvs[q ->].
by apply/polyOver_subvs; exists (p %% q); rewrite map_modp.
Qed.

Lemma gcdp_polyOver K :
  {in polyOver K &, forall p q, gcdp p q \is a polyOver K}.
Proof.
move=> _ _ /polyOver_subvs[p ->] /polyOver_subvs[q ->].
by apply/polyOver_subvs; exists (gcdp p q); rewrite gcdp_map.
Qed.

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
rewrite -[S _ _](@field_ideal_eq F) ?memv_prod ?rpredV //.
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

Definition power_space U x n := (\sum_(i < n) U * <[x ^+ i]>)%VS.

Lemma power_space_in_adjoin U x n : (power_space U x n <= <<U; x>>%AS)%VS.
Proof.
apply/subv_sumP => i _.
rewrite -[X in (_ <= X)%VS]prodv_id prodvS ?subv_adjoin //.
rewrite -expv_line (subv_trans (subvX_closure _ _)) // closureaS //.
by rewrite addvSr.
Qed.

Lemma power_space_direct_or_complete K x n :
   directv (power_space K x n) || (power_space K x n == <<K; x>>%AS).
Proof.
rewrite eqEsubv power_space_in_adjoin /=.
elim: n => [|n /orP]; first by rewrite directvE /= !big_ord0 dimv0 eqxx.
case => [/directvP /= IH | IH]; last first.
  by rewrite (subv_trans IH) ?orbT // /power_space big_ord_recr addvSl.
rewrite directvE /=; case: (altP eqP) => //=.
rewrite !big_ord_recr -IH {IH} /= dimv_add_leqif subv0 -vpick0.
set Z := (_ :&: _)%VS.
move: (memv_pick Z).
rewrite memv_cap andbC; case/andP => /memv_cosetP [z HzK ->] Hzsum.
rewrite mulf_eq0 negb_or expf_eq0 negb_and; case/andP => Hz0.
case: {Z} n Hzsum Hz0 => [|n Hzsum Hz0 /= Hx0].
  by rewrite expr0 mulr1 big_ord0 memv0 => ->.
rewrite /power_space big_ord_recr (subv_trans _ (addvSl _ _)) //=.
apply: ideall_closurea_sub.
  by rewrite big_ord_recl expr0 prodv1 (subv_trans (sub1v K)) // addvSl.
rewrite prodvDl subv_add.
rewrite -[X in (K * X)%VS]big_distrr prodvA prodv_id big_distrr subvv.
rewrite prodvC big_distrl /=.
apply/subv_sumP => [[i Hi] _].
rewrite -prodvA -expv_line -expvSr expv_line /=.
rewrite ltnS leq_eqVlt in Hi.
case/orP: Hi => [/eqP -> | Hi]; last first.
  by apply:(sumv_sup (lift ord0 (Ordinal Hi))) => //; rewrite lift0 subvv.
rewrite -big_distrr /= -[in X in (_ <= X)%VS]prodv_id -prodvA big_distrr /=.
rewrite -[in X in (_ <= (X * _))%VS]prodv_id -prodvA prodvSr //.
rewrite -[X in <[X]>%VS](mulKf Hz0); apply: memv_prod => //.
by rewrite rpredV.
Qed.

Section Fadjoin.

Definition elementDegree U x := (\dim_U%AS <<U; x>>%AS).-1.+1.

Lemma elementDegreeE K x : elementDegree K x = \dim_K <<K; x>>%AS.
Proof.
rewrite /elementDegree prednK => //.
by rewrite ltn_divRL ?mul0n ?adim_gt0 // field_dimS // subv_adjoin.
Qed.

Let Fadjoin U x := power_space U x (elementDegree U x).

(* Ideally this definition should use \poly; however we really make use of the
   fact that the index i has an ordinal type. *)
Definition poly_for_Fadjoin U x v : {poly L} := 
  \sum_i sumv_pi (Fadjoin U x) i v / x ^+ i *: 'X^i.

Definition minPoly U x : {poly L} := 
  'X^(elementDegree U x) - poly_for_Fadjoin U x (x ^+ (elementDegree U x)).

Lemma poly_for_polyOver U x v : poly_for_Fadjoin U x v \is a polyOver U.
Proof.
apply/(all_nthP 0) => i _ /=.
rewrite /poly_for_Fadjoin coef_sum memv_suml // => j _.
rewrite coefZ coefXn.
case: (i == j);last by rewrite mulr0 mem0v.
rewrite mulr1.
case/memv_cosetP: (memv_sum_pi (refl_equal (Fadjoin U x)) j v) => c Hc ->.
have [-> | /mulfK-> //] := eqVneq (x ^+ j) 0.
by rewrite mulr0 mul0r mem0v.
Qed.

Lemma size_poly_for U x v : size (poly_for_Fadjoin U x v) <= elementDegree U x.
Proof.
rewrite (leq_trans (size_sum _ _ _)) //.
apply/bigmax_leqP => i _.
set c := (_ / _).
case: (eqVneq c 0) => [-> | nzc]; first by rewrite scale0r size_poly0.
by rewrite (size_scale _ nzc) size_polyXn.
Qed.

Lemma size_minPoly U x : size (minPoly U x) = (elementDegree U x).+1.
Proof.
by rewrite /minPoly size_addl ?size_polyXn // size_opp ltnS size_poly_for.
Qed.

Lemma monic_minPoly U x : minPoly U x \is monic.
Proof.
rewrite monicE /lead_coef size_minPoly coefB coefXn eq_refl.
by rewrite nth_default ?subr0 // size_poly_for.
Qed.

Lemma elemDeg0 K : elementDegree K 0 = 1%N.
Proof. by rewrite /elementDegree addv0 subfield_closed divnn adim_gt0. Qed.

Lemma Fadjoin_is_power_space K x : <<K; x>>%AS = Fadjoin K x.
Proof.
symmetry.
apply/eqP.
case/orP: (power_space_direct_or_complete K x (elementDegree K x)) => //.
rewrite -[_ == _]dimv_leqif_eq; last by apply: power_space_in_adjoin.
move/directvP => -> /=.
rewrite (dim_sup_field (F:=K)) ?subv_adjoin //.
rewrite /elementDegree prednK ?divn_gt0 ?dimvS ?subv_adjoin ?adim_gt0 //.
rewrite -[X in (X * _)%N]subn0 -sum_nat_const_nat big_mkord.
apply/eqP; apply: eq_bigr.
case: (eqVneq x 0) => [->| Hx0 i _]; last first.
  by rewrite dim_cosetv // expf_eq0 negb_and Hx0 orbT.
rewrite addv0 subfield_closed divnn adim_gt0 => [[[] //= _] _].
by rewrite expr0 prodv1.
Qed.

Lemma directv_Fadjoin K x : directv (Fadjoin K x).
Proof.
case: (eqVneq x 0) => [-> | Hx0].
  rewrite /Fadjoin /power_space elemDeg0.
  apply/directvP => /=.
  by rewrite !big_ord_recl !big_ord0 addv0 addn0.
rewrite directvE /= -[(\sum_ _ _)%VS]/(Fadjoin K x).
apply/eqP.
rewrite -Fadjoin_is_power_space.
rewrite (dim_sup_field (F:=K)) ?subv_adjoin /elementDegree //=.
rewrite -[X in (X * _)%N]subn0 prednK; last first.
  rewrite divn_gt0 ?adim_gt0 // dimvS // (subv_trans _ (subv_closure _)) //.
  by rewrite addvSl.
rewrite -sum_nat_const_nat big_mkord /=.
apply: eq_bigr => i _.
by rewrite dim_cosetv // expf_eq0 negb_and Hx0 orbT.
Qed.

End Fadjoin.

Lemma poly_for_eq K x v : v \in <<K; x>>%AS -> (poly_for_Fadjoin K x v).[x] = v.
Proof.
rewrite Fadjoin_is_power_space => Hv.
rewrite /poly_for_Fadjoin horner_sum -{2}(sumv_pi_sum (erefl _) Hv).
apply: eq_bigr => i _.
rewrite !hornerE hornerXn.
have [/eqP | /mulfVK-> //] := eqVneq (x ^+ i) 0.
rewrite expf_eq0.
case/andP => Hi Hx.
move: {Hv} i Hi.
move/eqP: Hx ->.
rewrite /elementDegree.
move/addv_idPl: (sub0v K) ->.
rewrite -[X in \dim_X _]subfield_closed divnn adim_gt0.
by case; case.
Qed.

Fact Fadjoin_poly_is_linear U x :
  linear_for (in_alg L \; *:%R) (poly_for_Fadjoin U x).
Proof.
move=> a p q; rewrite /poly_for_Fadjoin /= scaler_sumr -big_split /=.
apply eq_bigr => i _ /=.
by rewrite linearP mulrDl scalerA -2!scalerAl mul1r scalerDl.
Qed.
Canonical poly_for_Fadjoin_additive U x :=
  Additive (Fadjoin_poly_is_linear U x).
Canonical poly_for_Fadjoin_linear U x := AddLinear (Fadjoin_poly_is_linear U x).

(*
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
*)

Lemma minPolyOver K x : minPoly K x \is a polyOver K.
Proof. by rewrite /minPoly rpredB ?rpredX ?polyOverX ?poly_for_polyOver. Qed.

Lemma poly_Fadjoin_small_uniq K x: {in polyOver K &, forall p q : {poly L}, 
  size p <= elementDegree K x -> size q <= elementDegree K x ->
  p.[x] = q.[x] -> p = q}.
Proof.
case: (eqVneq x 0) => [->|nzx].
  rewrite elemDeg0.
  move => p q _ _ /size1_polyC -> /size1_polyC ->.
  by rewrite !hornerC => ->.
move => p q; move/polyOverP => pK; move/polyOverP => qK szp szq.
rewrite (horner_coef_wide _ szp) (horner_coef_wide _ szq).
move/eqP; move: (directv_Fadjoin K x); move/directv_sum_unique => sumUniq.
rewrite {}sumUniq; try by move=> i; rewrite memv_prod ?memv_line ?pK ?qK.
move/forall_inP => Hpq; apply/polyP => i.
apply: (mulIf (expf_neq0 i nzx)).
case: (leqP (elementDegree K x) i) => Hi; last first.
  by apply/eqP; apply (Hpq (Ordinal Hi)).
by rewrite (_ : p`_i = 0) ?mul0r; first rewrite (_ : q`_i = 0) ?mul0r //;
  move: Hi; [ move/(leq_trans szq) | move/(leq_trans szp) ];
  move/leq_sizeP; apply.
Qed.

Lemma root_minPoly K x : root (minPoly K x) x. 
Proof.
apply/rootP.
rewrite /minPoly hornerD hornerN poly_for_eq ?rpredX ?memv_adjoin //.
by rewrite hornerXn subrr.
Qed.

Lemma minPolyxx K x : (minPoly K x).[x] = 0.
Proof. by apply/rootP; apply root_minPoly. Qed.

Lemma poly_Fadjoin K x v :
  reflect (exists2 p, p \in polyOver K & v = p.[x]) (v \in <<K; x>>%AS).
Proof.
apply: (iffP idP).
  move => Hv.
  exists (poly_for_Fadjoin K x v); first by apply: poly_for_polyOver.
  by symmetry; apply: poly_for_eq.
case => p /polyOverP Hp ->.
rewrite horner_coef.
apply: rpred_sum => i _.
rewrite rpredM ?rpredX ?memv_adjoin //.
apply: (subv_trans (Hp i)); apply: subv_adjoin.
Qed.

Lemma mempx_Fadjoin K x p : p \is a polyOver K -> p.[x] \in <<K; x>>%AS.
Proof. by move=> pK; apply/poly_Fadjoin; exists p. Qed.

Lemma poly_for_K K x v : v \in K -> poly_for_Fadjoin K x v = v%:P.
Proof.
move=> vK.
apply: (@poly_Fadjoin_small_uniq K x).
- exact: poly_for_polyOver.
- by rewrite polyOverC.
- exact: size_poly_for.
- by rewrite size_polyC (leq_trans (leq_b1 _)).
by rewrite hornerC poly_for_eq // memv_mem_adjoin.
Qed.

Lemma poly_for_modp K x p :
  p \is a polyOver K -> poly_for_Fadjoin K x p.[x] = p %% minPoly K x.
Proof.
move=> Pk.
apply: (@poly_Fadjoin_small_uniq K x).
- exact: poly_for_polyOver.
- by rewrite modp_polyOver // minPolyOver.
- exact: size_poly_for.
- by rewrite -ltnS -size_minPoly ltn_modp // -size_poly_eq0 size_minPoly.
rewrite poly_for_eq ?mempx_Fadjoin // {1}(divp_eq p (minPoly K x)).
by rewrite hornerD hornerM minPolyxx mulr0 add0r.
Qed.

Lemma elemDeg1 K x : (x \in K) = (elementDegree K x == 1%N).
Proof.
rewrite memv_adjoin_eq /elementDegree.
apply/eqP/eqP; first by move ->; rewrite divnn adim_gt0.
rewrite prednK; last first.
  rewrite divn_gt0 ?adim_gt0 // dimvS // (subv_trans _ (subv_closure _)) //.
  by rewrite addvSl.
move/eqP; rewrite -eqn_mul ?adim_gt0 ?field_dimS ?subv_adjoin // mul1n.
move => Hx.
by apply/eqP; rewrite eq_sym -dimv_leqif_eq ?subv_adjoin // eq_sym.
Qed.

Lemma minPoly_in_K K x : reflect (minPoly K x = 'X - x%:P) (x \in K).
Proof.
apply: (iffP idP); last first.
  move => HminPoly.
  have := (minPolyOver K x).
  rewrite HminPoly.
  move/polyOverP/(_ 0%N).
  by rewrite coefB coefX coefC eqxx add0r rpredN.
rewrite elemDeg1 => /eqP Hx.
rewrite [minPoly K x](all_roots_prod_XsubC (rs:=[:: x])) //=.
- by rewrite (monicP (monic_minPoly K x)) scale1r big_seq1.
- by rewrite size_minPoly Hx.
- by rewrite root_minPoly.
Qed.

Lemma poly_for_X K x : x \notin K -> poly_for_Fadjoin K x x = 'X.
Proof.
move=> K'z; rewrite -{2}[x]hornerX poly_for_modp ?polyOverX ?modp_small //.
by rewrite size_minPoly ltnS size_polyX ltn_neqAle eq_sym andbT -elemDeg1.
Qed.

Lemma size_elementDegree K x p :
  p \is a polyOver K -> size p <= elementDegree K x -> root p x = (p == 0).
Proof.
rewrite /root => Kp szp.
apply/eqP/eqP => Hp; last by rewrite Hp horner0.
by apply: (@poly_Fadjoin_small_uniq K x);
  rewrite ?polyOver0 ?size_poly0 ?horner0.
Qed. 

Lemma minPoly_irr K x p :
  p \is a polyOver K -> p %| (minPoly K x) -> (p %= minPoly K x) || (p %= 1).
Proof.
rewrite /dvdp => Kp /eqP pMin.
pose q := minPoly K x %/ p.
have Kq : q \is a polyOver K by rewrite divp_polyOver // minPolyOver.
move: (root_minPoly K x) (size_minPoly K x).
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
wlog: q p Kp Kq nzp nzq szpq pq0 / (q.[x] == 0); last first.
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
Qed.

Lemma minPoly_dvdp K x p : p \is a polyOver K -> root p x -> (minPoly K x) %| p.
Proof.
move=> Kp rootp.
have gcdK : gcdp (minPoly K x) p \is a polyOver K.
  by rewrite gcdp_polyOver ?minPolyOver //.
have [gcd_eqK|gcd_eq1] := orP (minPoly_irr gcdK (dvdp_gcdl (minPoly K x) p)).
  by rewrite -(eqp_dvdl _ gcd_eqK) dvdp_gcdr.
case/negP: (root1 x).
by rewrite -(eqp_root gcd_eq1) root_gcd rootp root_minPoly.
Qed.

Lemma minPolyS K E a : (K <= E)%VS -> minPoly E a %| minPoly K a.
Proof.
move => HKE.
apply: minPoly_dvdp; last by apply: root_minPoly.
apply: (polyOverSv HKE).
by rewrite minPolyOver.
Qed.

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
move=> y; apply/idP/idP; last rewrite unlock; move=> /coord_span->.
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
do [apply/idP/idP; last rewrite /V unlock] => [/coord_vbasis|/coord_span] ->.
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
  [seq tnth bF ij.2 *: tnth (vbasis V) ij.1 | ij : 'I_(\dim V) * 'I_n].
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

Fact refBaseField_key : unit. Proof. by []. Qed.
Definition refBaseField := locked_with refBaseField_key (baseAspace 1).
Canonical refBaseField_unlockable := [unlockable of refBaseField].
Notation F1 := refBaseField.

Lemma dim_refBaseField : \dim F1 = n.
Proof. by rewrite [F1]unlock dim_baseVspace dimv1 mul1n. Qed.

Lemma baseVspace_ideal V (V0 := baseVspace V) : (F1 * V0 <= V0)%VS.
Proof.
apply/prodvP=> u v; rewrite [F1]unlock !mem_baseVspace => /vlineP[x ->] Vv.
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
  rewrite {1}[F1]unlock mem_baseVspace => /vlineP[{x}x ->].
  by rewrite -(@scalerAl F L) mul1r memvZ ?memv_span ?memt_nth.
move: (coord _ i _) => x; rewrite -[_`_i]mul1r scalerAl -tnth_nth.
have F1x: x%:A \in F1.
  by rewrite [F1]unlock mem_baseVspace (@memvZ F L) // mem1v.
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
    {z | root (map_poly (in_alg L) p) z & <<1; z>>%AS = fullv}}.
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
    exists (map_poly iota (toPF x)).
      by apply/polyOverP=> i; rewrite coef_map memvZ ?mem1v.
    by apply: (can_inj toPF_K); rewrite q_z -toL_K toPF_K.
  elim/poly_ind: q => [|a q IHq].
    by rewrite map_poly0 horner0 linear0 mod0p.
  rewrite rmorphD rmorphM /= map_polyX map_polyC hornerMXaddC linearD /=.
  rewrite linearZ /= -(rmorph1 toL) toL_K -modp_scalel alg_polyC modp_add.
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
  by move=> x; apply: toPinj; rewrite mulC !toL_K modp_mul mulr1 -toL_K toPF_K.
have mulD: left_distributive mul +%R.
  move=> x y z; apply: toPinj; rewrite /toPF raddfD /= -!/(toPF _).
  by rewrite !toL_K /toPF raddfD mulrDl modp_add.
have nzL1: L1 != 0 by rewrite -(inj_eq toPinj) L1K /toPF raddf0 oner_eq0. 
pose mulM := ComRingMixin mulA mulC mul1 mulD nzL1.
pose rL := ComRingType (RingType vL mulM) mulC.
have mulZl: GRing.Lalgebra.axiom mul.
  move=> a x y; apply: toPinj; rewrite  toL_K /toPF !linearZ /= -!/(toPF _).
  by rewrite toL_K -scalerAl modp_scalel.
have mulZr: GRing.Algebra.axiom (LalgType F rL mulZl).
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

(*Coq 8.3 processes this shorter proof correctly, but then crashes on Qed.
Lemma Xirredp_FAdjoin' (F : fieldType) (p : {poly F}) :
    irreducible_poly p ->
  {L : fieldExtType F & Vector.dim L = (size p).-1 &
    {z | root (map_poly (in_alg L) p) z & <<1; z>>%AS = fullv}}.
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
    have /contraR := irr_p _ _ (dvdp_gcdl p q); apply.
    have: size (gcdp p q) <= size q by exact: leq_gcdpr.
    rewrite leqNgt;apply:contra;move/eqp_size ->.
    by rewrite (polySpred nz_p) ltnS size_poly.
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
  rewrite linearZ /= L1K alg_polyC modp_add; congr (_ + _); last first.
    by rewrite modp_small // size_polyC; case: (~~ _) => //; apply: ltnW.
  by rewrite !toL_K IHq mulrC modp_mul mulrC modp_mul.
exists z; first by rewrite /root -(can_eq (@rVpolyK _ _)) q_z modpp linear0.
apply/vspaceP=> x; rewrite memvf; apply/poly_Fadjoin.
exists (map_poly iota (rVpoly x)).
  by apply/polyOverP=> i; rewrite coef_map memvZ ?mem1v.
apply: (can_inj (@rVpolyK _ _)).
by rewrite q_z modp_small // -Dn ltnS size_poly.
Qed.
*)
