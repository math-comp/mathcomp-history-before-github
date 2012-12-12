(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path choice fintype.
Require Import tuple finfun bigop ssralg finalg zmodp matrix vector poly.

(******************************************************************************)
(* Finite dimensional free algebras, usually known as F-algebras.             *)
(*       FalgType K   == the interface type for F-algebras over K; it simply  *)
(*                       joins the unitAlgType K and vectType K interfaces.   *)
(* [FalgType K of aT] == an FalgType K structure for a type aT that has both  *)
(*                       unitAlgType K and vectType K canonical structures.   *)
(* [FalgType K of aT for vT] == an FalgType K structure for a type aT with a  *)
(*                       unitAlgType K canonical structure, given a structure *)
(*                       vT : vectType K whose lmodType K projection matches  *)
(*                       the canonical lmodType for aT.                       *)
(* FalgUnitRingType T == a default unitRingType structure for a type T with   *)
(*                       both algType and vectType structures.                *)
(*   Any aT with an FalgType structure inherits all the Vector, Ring and      *)
(* Algebra operations, and supports the following additional operations:      *)
(*            amull u == the linear function v |-> u * v, for u, v : aT.      *)
(*            amulr u == the linear function v |-> v * u, for u, v : aT.      *)
(*   1, f * g, f ^+ n == the identity function, the composite g \o f, the nth *)
(*                       iterate of f, for 1, f, g in 'End(aT). This is just  *)
(*                       the usual F-algebra structure on 'End(aT). It is NOT *)
(*                       canonical by default, but can be activated by the    *)
(*                       line Import FalgLfun. Beware also that (f^-1)%VF is  *)
(*                       the linear function inverse, not the ring inverse of *)
(*                       f (though they do coincide when f is injective).     *)
(*               1%VS == the line generated by 1 : aT.                        *)
(*         (U * V)%VS == the smallest subspace of aT that contains all        *)
(*                       products u * v for u in U, v in V.                   *)
(*        (U ^+ n)%VS == (U * U * ... * U), n-times.  U ^+ 0 = 1%VS           *)
(*            agenv U == the smallest subalgebra containing U ^+ n for all n. *)
(*        <<U; v>>%VS == agenv (U + <[v]>) (adjoin v to U).                   *)
(*      <<U & vs>>%VS == agenv (U + <<vs>>) (adjoin vs to U).                 *)
(*        {aspace aT} == a subType of {vspace aT} consisting of sub-algebras  *)
(*                       of aT (see below); for A : {aspace aT}, subvs_of A   *)
(*                       has a canonical FalgType K structure.                *)
(*        is_aspace U <=> the characteristic predicate of {aspace aT} stating *)
(*                       that U is closed under product and contains an       *)
(*                       identity element, := has_algid U && (U * U <= U)%VS. *)
(*            algid A == the identity element of A : {aspace aT}, which need  *)
(*                       not be equal to 1 (indeed, in a Wedderburn           *)
(*                       decomposition it is not even a unit in aT).          *)
(*       is_algid U e <-> e : aT is an identity element for the subspace U:   *)
(*                       e in U, e != 0 & e * u = u * e = u for all u in U.   *)
(*        has_algid U <=> there is an e such that is_algid U e.               *)
(*      [aspace of U] == a clone of an existing {aspace aT} structure on      *)
(*                       U : {vspace aT} (more instances of {aspace aT} will  *)
(*                       be defined in extFieldType).                         *)
(* [aspace of U for A] == a clone of A : {aspace aT} for U : {vspace aT}.     *)
(*               1%AS == the canonical sub-algebra 1%VS.                      *)
(*           {:aT}%AS == the canonical full algebra.                          *)
(*           <<U>>%AS == the canonical algebra for agenv U; note that this is *)
(*                       unrelated to <<vs>>%VS, the subspace spanned by vs.  *)
(*        <<U; v>>%AS == the canonical algebra for <<U; v>>%VS.               *)
(*      <<U & vs>>%AS == the canonical algebra for <<U & vs>>%VS.             *)
(*        ahom_in U f <=> f : 'Hom(aT, rT) is a multiplicative homomorphism   *)
(*                       inside U, and in addition f 1 = 1 (even if U doesn't *)
(*                       contain 1). Note that f @: U need not be a           *)
(*                       subalgebra when U is, as f could annilate U.         *)
(*      'AHom(aT, rT) == the type of algebra homomorphisms from aT to rT,     *)
(*                       where aT and rT ARE FalgType structures. Elements of *)
(*                       'AHom(aT, rT) coerce to 'End(aT, rT) and aT -> rT.   *)
(* --> Caveat: aT and rT must denote actual FalgType structures, not their    *)
(*     projections on Type.                                                   *)
(*          'AEnd(aT) == algebra endomorphisms of aT (:= 'AHom(aT, aT)).      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Local Scope ring_scope.

Reserved Notation "{ 'aspace' T }" (at level 0, format "{ 'aspace'  T }").
Reserved Notation "<< U & vs >>" (at level 0, format "<< U  &  vs >>").
Reserved Notation "<< U ; x >>" (at level 0, format "<< U ;  x >>").
Reserved Notation "''AHom' ( T , rT )"
  (at level 8, format "''AHom' ( T ,  rT )").
Reserved Notation "''AEnd' ( T )" (at level 8, format "''AEnd' ( T )").

Import GRing.Theory.

(* Finite dimensional algebra *)
Module Falgebra.

(* Supply a default unitRing mixin for the default unitAlgType base type. *)
Section DefaultBase.

Variables (K : fieldType) (A : algType K).

Lemma BaseMixin : Vector.mixin_of A -> GRing.UnitRing.mixin_of A.
Proof.
move=> vAm; pose vA := VectType K A vAm.
pose am u := linfun (u \o* idfun : vA -> vA).
have amE u v : am u v = v * u by rewrite lfunE.
pose uam := [pred u | lker (am u) == 0%VS].
pose vam := [fun u => if u \in uam then (am u)^-1%VF 1 else u].
have vamKl: {in uam, left_inverse 1 vam *%R}.
  by move=> u Uu; rewrite /= Uu -amE lker0_lfunVK.  
exists uam vam => // [u Uu | u v [_ uv1] | u /negbTE/= -> //].
  by apply/(lker0P Uu); rewrite !amE -mulrA vamKl // mul1r mulr1.
by apply/lker0P=> w1 w2 /(congr1 (am v)); rewrite !amE -!mulrA uv1 !mulr1.
Qed.

Definition BaseType T :=
  fun c vAm & phant_id c (GRing.UnitRing.Class (BaseMixin vAm)) =>
  fun (vT : vectType K) & phant vT
     & phant_id (Vector.mixin (Vector.class vT)) vAm =>
  @GRing.UnitRing.Pack T c T.

End DefaultBase.

Section ClassDef.
Variable R : ringType.
Implicit Type phR : phant R.

Record class_of A := Class {
  base1 : GRing.UnitAlgebra.class_of R A;
  mixin : Vector.mixin_of (GRing.Lmodule.Pack _ base1 A)
}.
Local Coercion base1 : class_of >-> GRing.UnitAlgebra.class_of.
Definition base2 A c := @Vector.Class _ _ (@base1 A c) (mixin c).
Local Coercion base2 : class_of >-> Vector.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Variables (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c _ := cT return class_of cT in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun bT b & phant_id (@GRing.UnitAlgebra.class R phR bT)
                      (b : GRing.UnitAlgebra.class_of R T) =>
  fun mT m & phant_id (@Vector.class R phR mT) (@Vector.Class R T b m) =>
  Pack (Phant R) (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition lmodType := @GRing.Lmodule.Pack R phR cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass xT.
Definition lalgType := @GRing.Lalgebra.Pack R phR cT xclass xT.
Definition algType := @GRing.Algebra.Pack R phR cT xclass xT.
Definition unitAlgType := @GRing.UnitAlgebra.Pack R phR cT xclass xT.
Definition vectType := @Vector.Pack R phR cT xclass cT.
Definition vect_ringType := @GRing.Ring.Pack vectType xclass xT.
Definition vect_unitRingType := @GRing.UnitRing.Pack vectType xclass xT.
Definition vect_lalgType := @GRing.Lalgebra.Pack R phR vectType xclass xT.
Definition vect_algType := @GRing.Algebra.Pack R phR vectType xclass xT.
Definition vect_unitAlgType := @GRing.UnitAlgebra.Pack R phR vectType xclass xT.

End ClassDef.

Module Exports.

Coercion base1 : class_of >-> GRing.UnitAlgebra.class_of.
Coercion base2 : class_of >-> Vector.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >->  Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion lmodType : type>->  GRing.Lmodule.type.
Canonical lmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion lalgType : type >-> GRing.Lalgebra.type.
Canonical lalgType.
Coercion algType : type >-> GRing.Algebra.type.
Canonical algType.
Coercion unitAlgType : type >-> GRing.UnitAlgebra.type.
Canonical unitAlgType.
Coercion vectType : type >-> Vector.type.
Canonical vectType.
Canonical vect_ringType.
Canonical vect_unitRingType.
Canonical vect_lalgType.
Canonical vect_algType.
Canonical vect_unitAlgType.
Notation FalgType R := (type (Phant R)).
Notation "[ 'FalgType' R 'of' A ]" := (@pack _ (Phant R) A _ _ id _ _ id)
  (at level 0, format "[ 'FalgType'  R  'of'  A ]") : form_scope.
Notation "[ 'FalgType' R 'of' A 'for' vT ]" :=
  (@pack _ (Phant R) A _ _ id vT _ idfun)
  (at level 0, format "[ 'FalgType'  R  'of'  A  'for'  vT ]") : form_scope.
Notation FalgUnitRingType T := (@BaseType _ _ T _ _ id _ (Phant T) id).
End Exports.

End Falgebra.
Export Falgebra.Exports.

Notation "1" := (vline 1) : vspace_scope.

Canonical matrix_FalgType (K : fieldType) n := [FalgType K of 'M[K]_n.+1].

Section Proper.

Variables (R : ringType) (aT : FalgType R).
Import Vector.InternalTheory.

Lemma FalgType_proper : Vector.dim aT > 0.
Proof.
rewrite lt0n; apply: contraNneq (oner_neq0 aT) => aT0.
by apply/eqP/v2r_inj; do 2!move: (v2r _); rewrite aT0 => u v; rewrite !thinmx0.
Qed.

End Proper.

Module FalgLfun.

Section FalgLfun.

Variable (R : comRingType) (aT : FalgType R).
Implicit Types f g : 'End(aT).

Canonical Falg_fun_ringType := lfun_ringType (FalgType_proper aT).
Canonical Falg_fun_lalgType := lfun_lalgType (FalgType_proper aT).
Canonical Falg_fun_algType := lfun_algType (FalgType_proper aT).

Lemma lfun_mulE f g u : (f * g) u = g (f u). Proof. exact: lfunE. Qed.
Lemma lfun_compE f g : (g \o f)%VF = f * g. Proof. by []. Qed.

End FalgLfun.

Section InvLfun.

Variable (K : fieldType) (aT : FalgType K).
Implicit Types f g : 'End(aT).

Definition lfun_invr f := if lker f == 0%VS then f^-1%VF else f.

Lemma lfun_mulVr f : lker f == 0%VS -> f^-1%VF * f = 1.
Proof. exact: lker0_compfV. Qed.

Lemma lfun_mulrV f : lker f == 0%VS -> f * f^-1%VF = 1.
Proof. exact: lker0_compVf. Qed.

Fact lfun_mulRVr f : lker f == 0%VS -> lfun_invr f * f = 1.
Proof. by move=> Uf; rewrite /lfun_invr Uf lfun_mulVr. Qed.

Fact lfun_mulrRV f : lker f == 0%VS -> f * lfun_invr f = 1.
Proof. by move=> Uf; rewrite /lfun_invr Uf lfun_mulrV. Qed.

Fact lfun_unitrP f g : g * f = 1 /\ f * g = 1 -> lker f == 0%VS.
Proof.
case=> _ fK; apply/lker0P; apply: can_inj (g) _ => u.
by rewrite -lfun_mulE fK lfunE.
Qed.

Lemma lfun_invr_out f : lker f != 0%VS -> lfun_invr f = f.
Proof. by rewrite /lfun_invr => /negPf->. Qed.

Definition lfun_unitRingMixin :=
  UnitRingMixin lfun_mulRVr lfun_mulrRV lfun_unitrP lfun_invr_out.
Canonical lfun_unitRingType := UnitRingType 'End(aT) lfun_unitRingMixin.
Canonical lfun_unitAlgType := [unitAlgType K of 'End(aT)].
Canonical Falg_fun_FalgType := [FalgType K of 'End(aT)].

Lemma lfun_invE f : lker f == 0%VS -> f^-1%VF = f^-1.
Proof. by rewrite /f^-1 /= /lfun_invr => ->. Qed.

End InvLfun.

End FalgLfun.

Section FalgebraTheory.

Variables (K : fieldType) (aT : FalgType K).
Implicit Types (u v : aT) (U V W : {vspace aT}).

Import FalgLfun.

Definition amull u : 'End(aT) := linfun (u \*o @idfun aT).
Definition amulr u : 'End(aT) := linfun (u \o* @idfun aT).

Lemma amull_inj : injective amull.
Proof. by move=> x y /lfunP/(_ 1); rewrite !lfunE /= !mulr1. Qed.

Lemma amulr_inj : injective amulr.
Proof. by move=> x y /lfunP/(_ 1); rewrite !lfunE /= !mul1r. Qed.

Fact amull_is_linear : linear amull.
Proof.
move=> a x y; apply/lfunP => z.
by rewrite !lfunE /= scale_lfunE !lfunE /= mulrDl scalerAl.
Qed.
Canonical amull_additive := Eval hnf in Additive amull_is_linear.
Canonical amull_linear := Eval hnf in AddLinear amull_is_linear.

(* amull is a converse ring morphism *)
Lemma amull1 : amull 1 = \1%VF.
Proof. by apply/lfunP => z; rewrite id_lfunE lfunE /= mul1r. Qed.

Lemma amullM x y : (amull (x * y) = amull y * amull x)%VF.
Proof. by apply/lfunP => z; rewrite comp_lfunE !lfunE /= mulrA. Qed.

Lemma amulr_is_lrmorphism : lrmorphism amulr.
Proof.
split=> [|a x]; last by apply/lfunP=> z; rewrite scale_lfunE !lfunE /= scalerAr.
split=> [x y|]; first by apply/lfunP => z; do 3!rewrite !lfunE /= ?mulrBr.
split=> [x y|]; last by apply/lfunP=> z; rewrite id_lfunE !lfunE /= mulr1.
by apply/lfunP=> z; rewrite comp_lfunE !lfunE /= mulrA.
Qed.
Canonical amulr_additive := Eval hnf in Additive amulr_is_lrmorphism.
Canonical amulr_linear := Eval hnf in AddLinear amulr_is_lrmorphism.
Canonical amulr_rmorphism := Eval hnf in AddRMorphism amulr_is_lrmorphism.
Canonical amulr_lrmorphism := Eval hnf in LRMorphism amulr_is_lrmorphism.

Lemma lfun1_poly (p : {poly aT}) : map_poly \1%VF p = p.
Proof. by apply: map_poly_id => u _; apply: id_lfunE. Qed.

Fact prodv_key : unit. Proof. by []. Qed.
Definition prodv :=
  locked_with prodv_key (fun U V => <<allpairs *%R (vbasis U) (vbasis V)>>%VS).
Canonical prodv_unlockable := [unlockable fun prodv].
Local Notation "A * B" := (prodv A B) : vspace_scope.

Lemma memv_prod U V : {in U & V, forall u v, u * v \in (U * V)%VS}.
Proof.
move=> u v /coord_vbasis-> /coord_vbasis->.
rewrite mulr_suml; apply: memv_suml => i _.
rewrite mulr_sumr; apply: memv_suml => j _.
rewrite -scalerAl -scalerAr !memvZ // [prodv]unlock memv_span //.
by apply/allpairsP; exists ((vbasis U)`_i, (vbasis V)`_j); rewrite !memt_nth.
Qed.

Lemma prodvP {U V W} :
  reflect {in U & V, forall u v, u * v \in W} (U * V <= W)%VS.
Proof.
apply: (iffP idP) => [sUVW u v Uu Vv | sUVW].
  by rewrite (subvP sUVW) ?memv_prod.
rewrite [prodv]unlock; apply/span_subvP=> _ /allpairsP[[u v] /= [Uu Vv ->]].
by rewrite sUVW ?vbasis_mem.
Qed.

Lemma prodv_line u v : (<[u]> * <[v]> = <[u * v]>)%VS.
Proof.
apply: subv_anti; rewrite -memvE memv_prod ?memv_line // andbT.
apply/prodvP=> _ _ /vlineP[a ->] /vlineP[b ->].
by rewrite -scalerAr -scalerAl !memvZ ?memv_line.
Qed.

Lemma dimv1: \dim (1%VS : {vspace aT}) = 1%N.
Proof. by rewrite dim_vline oner_neq0. Qed.

Lemma dim_prodv U V : \dim (U * V) <= \dim U * \dim V.
Proof. by rewrite unlock (leq_trans (dim_span _)) ?size_tuple. Qed.

Lemma vspace1_neq0 : (1 != 0 :> {vspace aT})%VS.
Proof. by rewrite -dimv_eq0 dimv1. Qed.

Lemma vbasis1 : exists2 k, k != 0 & vbasis 1 = [:: k%:A] :> seq aT.
Proof.
move: (vbasis 1) (@vbasisP K aT 1); rewrite dim_vline oner_neq0.
case/tupleP=> x X0; rewrite {X0}tuple0 => defX; have Xx := mem_head x nil.
have /vlineP[k def_x] := basis_mem defX Xx; exists k; last by rewrite def_x.
by have:= basis_not0 defX Xx; rewrite def_x scaler_eq0 oner_eq0 orbF.
Qed.

Lemma prod0v : left_zero 0%VS prodv.
Proof.
move=> U; apply/eqP; rewrite -dimv_eq0 -leqn0 (leq_trans (dim_prodv 0 U)) //.
by rewrite dimv0.
Qed.

Lemma prodv0 : right_zero 0%VS prodv.
Proof.
move=> U; apply/eqP; rewrite -dimv_eq0 -leqn0 (leq_trans (dim_prodv U 0)) //.
by rewrite dimv0 muln0.
Qed.

Canonical prodv_muloid := Monoid.MulLaw prod0v prodv0.

Lemma prod1v : left_id 1%VS prodv.
Proof.
move=> U; apply/subv_anti/andP; split.
  by apply/prodvP=> _ u /vlineP[a ->] Uu; rewrite mulr_algl memvZ.
by apply/subvP=> u Uu; rewrite -[u]mul1r memv_prod ?memv_line.
Qed.

Lemma prodv1 : right_id 1%VS prodv.
Proof.
move=> U; apply/subv_anti/andP; split.
  by apply/prodvP=> u _ Uu /vlineP[a ->]; rewrite mulr_algr memvZ.
by apply/subvP=> u Uu; rewrite -[u]mulr1 memv_prod ?memv_line.
Qed.

Lemma prodvS U1 U2 V1 V2 : (U1 <= U2 -> V1 <= V2 -> U1 * V1 <= U2 * V2)%VS.
Proof.
move/subvP=> sU12 /subvP sV12; apply/prodvP=> u v Uu Vv.
by rewrite memv_prod ?sU12 ?sV12.
Qed.

Lemma prodvSl U1 U2 V : (U1 <= U2 -> U1 * V <= U2 * V)%VS.
Proof. by move/prodvS->. Qed.

Lemma prodvSr U V1 V2 : (V1 <= V2 -> U * V1 <= U * V2)%VS.
Proof. exact: prodvS. Qed.

Lemma prodvDl : left_distributive prodv addv.
Proof.
move=> U1 U2 V; apply/esym/subv_anti/andP; split.
  by rewrite subv_add 2?prodvS ?addvSl ?addvSr.
apply/prodvP=> _ v /memv_addP[u1 Uu1 [u2 Uu2 ->]] Vv.
by rewrite mulrDl memv_add ?memv_prod.
Qed.

Lemma prodvDr : right_distributive prodv addv.
Proof.
move=> U V1 V2; apply/esym/subv_anti/andP; split.
  by rewrite subv_add 2?prodvS ?addvSl ?addvSr.
apply/prodvP=> u _ Uu /memv_addP[v1 Vv1 [v2 Vv2 ->]].
by rewrite mulrDr memv_add ?memv_prod.
Qed.

Canonical addv_addoid := Monoid.AddLaw prodvDl prodvDr.

Lemma prodvA : associative prodv.
Proof.
move=> U V W; rewrite -(span_basis (vbasisP U)) span_def !big_distrl /=.
apply: eq_bigr => u _; rewrite -(span_basis (vbasisP W)) span_def !big_distrr.
apply: eq_bigr => w _; rewrite -(span_basis (vbasisP V)) span_def /=.
rewrite !(big_distrl, big_distrr) /=; apply: eq_bigr => v _.
by rewrite !prodv_line mulrA.
Qed.

Canonical prodv_monoid := Monoid.Law prodvA prod1v prodv1.

Definition expv U n := iterop n.+1.-1 prodv U 1%VS.
Local Notation "A ^+ n" := (expv A n) : vspace_scope.

Lemma expv0 U : (U ^+ 0 = 1)%VS. Proof. by []. Qed.
Lemma expv1 U : (U ^+ 1 = U)%VS. Proof. by []. Qed.
Lemma expv2 U : (U ^+ 2 = U * U)%VS. Proof. by []. Qed.

Lemma expvSl U n : (U ^+ n.+1 = U * U ^+ n)%VS.
Proof. by case: n => //; rewrite prodv1. Qed.

Lemma expv0n n : (0 ^+ n = if n is _.+1 then 0 else 1)%VS.
Proof. by case: n => // n; rewrite expvSl prod0v. Qed.

Lemma expv1n n : (1 ^+ n = 1)%VS.
Proof. by elim: n => // n IHn; rewrite expvSl IHn prodv1. Qed.

Lemma expvD U m n : (U ^+ (m + n) = U ^+ m * U ^+ n)%VS.
Proof. by elim: m => [|m IHm]; rewrite ?prod1v // !expvSl IHm prodvA. Qed.

Lemma expvSr U n : (U ^+ n.+1 = U ^+ n * U)%VS.
Proof. by rewrite -addn1 expvD. Qed.

Lemma expvM U m n : (U ^+ (m * n) = U ^+ m ^+ n)%VS.
Proof. by elim: n => [|n IHn]; rewrite ?muln0 // mulnS expvD IHn expvSl. Qed.

Lemma expvS U V n : (U <= V -> U ^+ n <= V ^+ n)%VS.
Proof.
move=> sUV; elim: n => [|n IHn]; first by rewrite !expv0 subvv.
by rewrite !expvSl prodvS.
Qed.

Lemma expv_line u n : (<[u]> ^+ n = <[u ^+ n]>)%VS.
Proof.
elim: n => [|n IH]; first by rewrite expr0 expv0.
by rewrite exprS expvSl IH prodv_line.
Qed.

(* Building the predicate that checks is a vspace has a unit *)
Definition is_algid e U :=
  [/\ e \in U, e != 0 & {in U, forall u, e * u = u /\ u * e = u}].

Fact algid_decidable U : decidable (exists e, is_algid e U).
Proof.
have [-> | nzU] := eqVneq U 0%VS.
  by right=> [[e []]]; rewrite memv0 => ->.
pose X := vbasis U; pose feq f1 f2 := [tuple of map f1 X ++ map f2 X].
have feqL f i: tnth (feq _ f _) (lshift _ i) = f X`_i.
  set v := f _; rewrite (tnth_nth v) /= nth_cat size_map size_tuple.
  by rewrite ltn_ord (nth_map 0) ?size_tuple.
have feqR f i: tnth (feq _ _ f) (rshift _ i) = f X`_i.
  set v := f _; rewrite (tnth_nth v) /= nth_cat size_map size_tuple.
  by rewrite ltnNge leq_addr addKn /= (nth_map 0) ?size_tuple.
apply: decP (vsolve_eq (feq _ amulr amull) (feq _ id id) U) _.
apply: (iffP (vsolve_eqP _ _ _)) => [[e Ue id_e] | [e [Ue _ id_e]]].
  suffices idUe: {in U, forall u, e * u = u /\ u * e = u}.
    exists e; split=> //; apply: contraNneq nzU => e0; rewrite -subv0.
    by apply/subvP=> u /idUe[<- _]; rewrite e0 mul0r mem0v.
  move=> u /coord_vbasis->; rewrite mulr_sumr mulr_suml.
  split; apply/eq_bigr=> i _; rewrite -(scalerAr, scalerAl); congr (_ *: _).
    by have:= id_e (lshift _ i); rewrite !feqL lfunE.
  by have:= id_e (rshift _ i); rewrite !feqR lfunE.
have{id_e} /all_and2[ideX idXe]:= id_e _ (vbasis_mem (mem_tnth _ X)).
exists e => // k; rewrite -[k]splitK.
by case: (split k) => i; rewrite !(feqL, feqR) lfunE /= -tnth_nth.
Qed.

Definition has_algid : pred {vspace aT} := algid_decidable.

Lemma has_algidP {U} : reflect (exists e, is_algid e U) (has_algid U).
Proof. exact: sumboolP. Qed.

Lemma has_algid1 U : 1 \in U -> has_algid U.
Proof.
move=> U1; apply/has_algidP; exists 1; split; rewrite ?oner_eq0 // => u _.
by rewrite mulr1 mul1r.
Qed.

Definition is_aspace U := has_algid U && (U * U <= U)%VS.
Structure aspace := ASpace {asval :> {vspace aT}; _ : is_aspace asval}.
Definition aspace_of of phant aT := aspace.
Local Notation "{ 'aspace' T }" := (aspace_of (Phant T)) : type_scope.

Canonical aspace_subType := Eval hnf in [subType for asval].
Definition aspace_eqMixin := [eqMixin of aspace by <:].
Canonical aspace_eqType := Eval hnf in EqType aspace aspace_eqMixin.
Definition aspace_choiceMixin := [choiceMixin of aspace by <:].
Canonical aspace_choiceType := Eval hnf in ChoiceType aspace aspace_choiceMixin.

Canonical aspace_of_subType := Eval hnf in [subType of {aspace aT}].
Canonical aspace_of_eqType := Eval hnf in [eqType of {aspace aT}].
Canonical aspace_of_choiceType := Eval hnf in [choiceType of {aspace aT}].

Definition clone_aspace U (A : {aspace aT}) :=
  fun algU & phant_id algU (valP A) =>  @ASpace U algU : {aspace aT}.

Fact aspace1_subproof : is_aspace 1.
Proof. by rewrite /is_aspace prod1v -memvE has_algid1 memv_line. Qed.
Canonical aspace1 : {aspace aT} := ASpace aspace1_subproof.

Lemma aspacef_subproof : is_aspace fullv.
Proof. by rewrite /is_aspace subvf has_algid1 ?memvf. Qed.
Canonical aspacef : {aspace aT} := ASpace aspacef_subproof.

End FalgebraTheory.

Delimit Scope aspace_scope with AS.
Bind Scope aspace_scope with aspace.
Bind Scope aspace_scope with aspace_of.
Arguments Scope asval [_ _ aspace_scope].
Arguments Scope clone_aspace [_ _ vspace_scope aspace_scope _ _].

Notation "{ 'aspace' T }" := (aspace_of (Phant T)) : type_scope.
Notation "A * B" := (prodv A B) : vspace_scope.
Notation "A ^+ n" := (expv A n) : vspace_scope.
Notation "1" := (aspace1 _) : aspace_scope.
Notation "{ : aT }" := (aspacef aT) : aspace_scope.
Notation "[ 'aspace' 'of' U ]" := (@clone_aspace _ _ U _ _ id)
  (at level 0, format "[ 'aspace'  'of'  U ]") : form_scope.
Notation "[ 'aspace' 'of' U 'for' A ]" := (@clone_aspace _ _ U A _ idfun)
  (at level 0, format "[ 'aspace'  'of'  U  'for'  A ]") : form_scope.

Implicit Arguments prodvP [K aT U V W].
Implicit Arguments has_algidP [K aT U].

Section AspaceTheory.

Variables (K : fieldType) (aT : FalgType K).
Implicit Types (u v e : aT) (U V : {vspace aT}) (A B : {aspace aT}).
Import FalgLfun.

Lemma algid_subproof U :
  {e | e \in U
     & has_algid U ==> (U <= lker (amull e - 1) :&: lker (amulr e - 1))%VS}.
Proof.
apply: sig2W; case: has_algidP => [[e]|]; last by exists 0; rewrite ?mem0v.
case=> Ae _ idAe; exists e => //; apply/subvP=> u /idAe[eu_u ue_u].
by rewrite memv_cap !memv_ker !lfun_simp /= eu_u ue_u subrr eqxx.
Qed.

Definition algid U := s2val (algid_subproof U).

Lemma memv_algid U : algid U \in U.
Proof. by rewrite /algid; case: algid_subproof. Qed.

Lemma algidl A : {in A, left_id (algid A) *%R}.
Proof.
rewrite /algid; case: algid_subproof => e _ /=; have /andP[-> _] := valP A.
move/subvP=> idAe u /idAe/memv_capP[].
by rewrite memv_ker !lfun_simp /= subr_eq0 => /eqP.
Qed.

Lemma algidr A : {in A, right_id (algid A) *%R}.
Proof.
rewrite /algid; case: algid_subproof => e _ /=; have /andP[-> _] := valP A.
move/subvP=> idAe u /idAe/memv_capP[_].
by rewrite memv_ker !lfun_simp /= subr_eq0 => /eqP.
Qed.

Lemma algid_eq1 A : (algid A == 1) = (1 \in A).
Proof. by apply/eqP/idP=> [<- | /algidr <-]; rewrite ?memv_algid ?mul1r. Qed.

Lemma algid_neq0 A : algid A != 0.
Proof.
have /andP[/has_algidP[u [Au nz_u _]] _] := valP A.
by apply: contraNneq nz_u => e0; rewrite -(algidr Au) e0 mulr0.
Qed.

Lemma dim_algid A : \dim <[algid A]> = 1%N.
Proof. by rewrite dim_vline algid_neq0. Qed.

Lemma adim_gt0 A : (0 < \dim A)%N.
Proof. by rewrite -(dim_algid A) dimvS // -memvE ?memv_algid. Qed.

Lemma not_asubv0 A : ~~ (A <= 0)%VS.
Proof. by rewrite subv0 -dimv_eq0 -lt0n adim_gt0. Qed.

Lemma adim1P {A} : reflect (A = <[algid A]>%VS :> {vspace aT}) (\dim A == 1%N).
Proof.
rewrite eqn_leq adim_gt0 -(memv_algid A) andbC -(dim_algid A) -eqEdim eq_sym.
exact: eqP.
Qed.

Lemma asubv A : (A * A <= A)%VS.
Proof. by have /andP[] := valP A. Qed.

Lemma memv_mul A : {in A &, forall u v, u * v \in A}.
Proof. exact/prodvP/asubv. Qed.

Lemma prodv_id A : (A * A)%VS = A.
Proof.
apply/eqP; rewrite eqEsubv asubv; apply/subvP=> u Au.
by rewrite -(algidl Au) memv_prod // memv_algid.
Qed.

Lemma prodv_sub U V A : (U <= A -> V <= A -> U * V <= A)%VS.
Proof. by move=> sUA sVA; rewrite -prodv_id prodvS. Qed.

Lemma expv_id A n : (A ^+ n.+1)%VS = A.
Proof. by elim: n => // n IHn; rewrite !expvSl prodvA prodv_id -expvSl. Qed.

Lemma limg_amulr U v : (amulr v @: U = U * <[v]>)%VS.
Proof.
rewrite -(span_basis (vbasisP U)) limg_span !span_def big_distrl /= big_map.
by apply: eq_bigr => u; rewrite prodv_line lfunE.
Qed.
 
Lemma memv_cosetP {U v w} :
  reflect (exists2 u, u\in U & w = u * v) (w \in U * <[v]>)%VS.
Proof.
rewrite -limg_amulr.
by apply: (iffP memv_imgP) => [] [u] Uu ->; exists u; rewrite ?lfunE.
Qed.

Lemma aspace_cap_subproof A B : algid A = algid B -> is_aspace (A :&: B).
Proof.
move=> eq_eAB; apply/andP; split.
  apply/has_algidP; exists (algid A); split; rewrite ?algid_neq0 //.
    by rewrite memv_cap {2}eq_eAB !memv_algid.
  by move=> u /memv_capP[Au _]; rewrite algidl ?algidr.
by rewrite -{3}(prodv_id A) -{3}(prodv_id B) subv_cap !prodvS ?capvSl ?capvSr.
Qed.

Definition aspace_cap A B eq_eAB := ASpace (@aspace_cap_subproof A B eq_eAB).

End AspaceTheory.

Implicit Arguments adim1P [K aT A].
Implicit Arguments memv_cosetP [K aT U v w].

Section Closure.

Variables (K : fieldType) (aT : FalgType K).
Implicit Types (u v : aT) (U V W : {vspace aT}).

(* Subspaces of an F-algebra form a Kleene algebra *)
Definition agenv U := (\sum_(i < \dim {:aT}) U ^+ i)%VS.
Local Notation "<< U & vs >>" := (agenv (U + <<vs>>)) : vspace_scope.
Local Notation "<< U ; x >>" := (agenv (U + <[x]>)) : vspace_scope.

Lemma agenvEl U : agenv U = (1 + U * agenv U)%VS.
Proof.
pose f V := (1 + U * V)%VS; rewrite -/(f _); pose n := \dim {:aT}.
have ->: agenv U = iter n f 0%VS.
  rewrite /agenv -/n; elim: n => [|n IHn]; first by rewrite big_ord0.
  rewrite big_ord_recl /= -{}IHn; congr (1 + _)%VS; rewrite big_distrr /=.
  by apply: eq_bigr => i; rewrite expvSl.
have fS i j: i <= j -> (iter i f 0 <= iter j f 0)%VS.
  by elim: i j => [|i IHi] [|j] leij; rewrite ?sub0v //= addvS ?prodvSr ?IHi.
suffices /(@trajectP _ f _ n.+1)[i le_i_n Dfi]: looping f 0%VS n.+1.
  by apply/eqP; rewrite eqEsubv -iterS fS // Dfi fS.
apply: contraLR (dimvS (subvf (iter n.+1 f 0%VS))); rewrite -/n -ltnNge.
rewrite -looping_uniq; elim: n.+1 => // i IHi; rewrite trajectSr rcons_uniq.
rewrite {1}trajectSr mem_rcons inE negb_or eq_sym eqEdim fS ?leqW // -ltnNge.
by rewrite -andbA => /and3P[lt_fi _ /IHi/leq_ltn_trans->].
Qed.

Lemma agenvEr U : agenv U = (1 + agenv U * U)%VS.
Proof.
rewrite [lhs in lhs = _]agenvEl big_distrr big_distrl /=; congr (_ + _)%VS.
by apply: eq_bigr => i _ /=; rewrite -expvSr -expvSl.
Qed.

Lemma agenv_ideall U V : (U * V <= V -> agenv U * V <= V)%VS.
Proof.
rewrite big_distrl /= => idlU_V; apply/subv_sumP=> [[i _] /= _].
elim: i => [|i]; first by rewrite expv0 prod1v.
by apply: subv_trans; rewrite expvSr -prodvA prodvSr.
Qed.

Lemma agenv_idealr U V : (V * U <= V -> V * agenv U <= V)%VS.
Proof.
rewrite big_distrr /= => idrU_V; apply/subv_sumP=> [[i _] /= _].
elim: i => [|i]; first by rewrite expv0 prodv1.
by apply: subv_trans; rewrite expvSl prodvA prodvSl.
Qed.

Fact agenv_is_aspace U : is_aspace (agenv U).
Proof.
rewrite /is_aspace has_algid1; last by rewrite memvE agenvEl addvSl.
by rewrite agenv_ideall // [V in (_ <= V)%VS]agenvEl addvSr.
Qed.
Canonical agenv_aspace U : {aspace aT} := ASpace (agenv_is_aspace U).

Lemma agenvE U : agenv U = agenv_aspace U. Proof. by []. Qed.

(* Kleene algebra properties *)

Lemma agenvM U : (agenv U * agenv U)%VS = agenv U. Proof. exact: prodv_id. Qed.
Lemma agenvX n U : (agenv U ^+ n.+1)%VS = agenv U. Proof. exact: expv_id. Qed.

Lemma sub1_agenv U : (1 <= agenv U)%VS. Proof. by rewrite agenvEl addvSl. Qed.

Lemma sub_agenv U : (U <= agenv U)%VS.
Proof. by rewrite 2!agenvEl addvC prodvDr prodv1 -addvA addvSl. Qed.

Lemma subX_agenv U n : (U ^+ n <= agenv U)%VS.
Proof.
by case: n => [|n]; rewrite ?sub1_agenv // -(agenvX n) expvS // sub_agenv.
Qed.

Lemma agenv_sub_ideall U V : (1 <= V -> U * V <= V -> agenv U <= V)%VS.
Proof.
move=> s1V /agenv_ideall; apply: subv_trans.
by rewrite -[Us in (Us <= _)%VS]prodv1 prodvSr.
Qed.

Lemma agenv_sub_idealr U V : (1 <= V -> V * U <= V -> agenv U <= V)%VS.
Proof.
move=> s1V /agenv_idealr; apply: subv_trans.
by rewrite -[Us in (Us <= _)%VS]prod1v prodvSl.
Qed.

Lemma agenv_id U : agenv (agenv U) = agenv U.
Proof.
apply/eqP; rewrite eqEsubv sub_agenv andbT.
by rewrite agenv_sub_ideall ?sub1_agenv ?agenvM.
Qed.

Lemma agenvS U V : (U <= V -> agenv U <= agenv V)%VS.
Proof.
move=> sUV; rewrite agenv_sub_ideall ?sub1_agenv //.
by rewrite -[Vs in (_ <= Vs)%VS]agenvM prodvSl ?(subv_trans sUV) ?sub_agenv.
Qed.

Lemma agenv_add_id U V : agenv (agenv U + V) = agenv (U + V).
Proof.
apply/eqP; rewrite eqEsubv andbC agenvS ?addvS ?sub_agenv //=.
rewrite agenv_sub_ideall ?sub1_agenv //.
rewrite -[rhs in (_ <= rhs)%VS]agenvM prodvSl // subv_add agenvS ?addvSl //=.
exact: subv_trans (addvSr U V) (sub_agenv _).
Qed.

Lemma subv_adjoin U x : (U <= <<U; x>>)%VS.
Proof. by rewrite (subv_trans (sub_agenv _)) ?agenvS ?addvSl. Qed.

Lemma subv_adjoin_seq U xs : (U <= <<U & xs>>)%VS.
Proof. by rewrite (subv_trans (sub_agenv _)) // ?agenvS ?addvSl. Qed.

Lemma memv_adjoin U x : x \in <<U; x>>%VS.
Proof. by rewrite memvE (subv_trans (sub_agenv _)) ?agenvS ?addvSr. Qed.

Lemma seqv_sub_adjoin U xs : {subset xs <= <<U & xs>>%VS}.
Proof.
by apply/span_subvP; rewrite (subv_trans (sub_agenv _)) ?agenvS ?addvSr.
Qed.

Lemma subvP_adjoin U x y : y \in U -> y \in <<U; x>>%VS.
Proof. exact/subvP/subv_adjoin. Qed.

Lemma adjoin_nil V : <<V & [::]>>%VS = agenv V.
Proof. by rewrite span_nil addv0. Qed.

Lemma adjoin_cons V x rs : <<V & x :: rs>>%VS = << <<V; x>> & rs>>%VS.
Proof. by rewrite span_cons addvA agenv_add_id. Qed.

Lemma adjoin_rcons V rs x : <<V & rcons rs x>>%VS = << <<V & rs>>%VS; x>>%VS.
Proof. by rewrite -cats1 span_cat addvA span_seq1 agenv_add_id. Qed.

Lemma adjoin_seq1 V x : <<V & [:: x]>>%VS = <<V; x>>%VS.
Proof. by rewrite adjoin_cons adjoin_nil agenv_id. Qed.

Lemma adjoinC V x y : << <<V; x>>; y>>%VS = << <<V; y>>; x>>%VS.
Proof. by rewrite !agenv_add_id -!addvA (addvC <[x]>%VS). Qed.

Lemma adjoinSl U V x : (U <= V -> <<U; x>> <= <<V; x>>)%VS.
Proof. by move=> sUV; rewrite agenvS ?addvS. Qed.

Lemma adjoin_seqSl U V rs : (U <= V -> <<U & rs>> <= <<V & rs>>)%VS.
Proof. by move=> sUV; rewrite agenvS ?addvS. Qed.

Lemma adjoin_seqSr U rs1 rs2 :
  {subset rs1 <= rs2} -> (<<U & rs1>> <= <<U & rs2>>)%VS.
Proof. by move/sub_span=> s_rs12; rewrite agenvS ?addvS. Qed.

End Closure.

Notation "<< U >>" := (agenv_aspace U) : aspace_scope.
Notation "<< U & vs >>" := (agenv (U + <<vs>>)) : vspace_scope.
Notation "<< U ; x >>" := (agenv (U + <[x]>)) : vspace_scope.
Notation "<< U & vs >>" := << U + <<vs>> >>%AS : aspace_scope.
Notation "<< U ; x >>" := << U + <[x]> >>%AS : aspace_scope. 

Section SubFalgType.

(* The FalgType structure of subvs_of A for A : {aspace aT}.                  *)
(* We can't use the rpred-based mixin, because A need not contain 1.          *)
Variable (K : fieldType) (aT : FalgType K) (A : {aspace aT}).

Definition subvs_one := Subvs (memv_algid A).
Definition subvs_mul (u v : subvs_of A) := 
  Subvs (subv_trans (memv_prod (subvsP u) (subvsP v)) (asubv _)).

Fact subvs_mulA : associative subvs_mul.
Proof. by move=> x y z; apply/val_inj/mulrA. Qed.
Fact subvs_mu1l : left_id subvs_one subvs_mul.
Proof. by move=> x; apply/val_inj/algidl/(valP x). Qed.
Fact subvs_mul1 : right_id subvs_one subvs_mul.
Proof. by move=> x; apply/val_inj/algidr/(valP x). Qed.
Fact subvs_mulDl : left_distributive subvs_mul +%R.
Proof. move=> x y z; apply/val_inj/mulrDl. Qed.
Fact subvs_mulDr : right_distributive subvs_mul +%R.
Proof. move=> x y z; apply/val_inj/mulrDr. Qed.

Definition subvs_ringMixin :=
  RingMixin subvs_mulA subvs_mu1l subvs_mul1 subvs_mulDl subvs_mulDr
            (algid_neq0 _).
Canonical subvs_ringType := Eval hnf in RingType (subvs_of A) subvs_ringMixin.

Lemma subvs_scaleAl k (x y : subvs_of A) : k *: (x * y) = (k *: x) * y.
Proof. exact/val_inj/scalerAl. Qed.
Canonical subvs_lalgType := Eval hnf in LalgType K (subvs_of A) subvs_scaleAl.

Lemma subvs_scaleAr k (x y : subvs_of A) : k *: (x * y) = x * (k *: y).
Proof. exact/val_inj/scalerAr. Qed.
Canonical subvs_algType := Eval hnf in AlgType K (subvs_of A) subvs_scaleAr.

Canonical subvs_unitRingType := Eval hnf in FalgUnitRingType (subvs_of A).
Canonical subvs_unitAlgType := Eval hnf in [unitAlgType K of subvs_of A].
Canonical subvs_FalgType := Eval hnf in [FalgType K of subvs_of A].

Lemma vsval_unitr (w : subvs_of A) :
  vsval w \is a GRing.unit -> w \is a GRing.unit.
Proof. 
move=> Uv; have /memv_imgP[v1 Av1 v1w]: algid A \in (amulr (val w) @: A)%VS.
  apply: subvP (memv_algid A); rewrite -dimv_leqif_sup.
    rewrite limg_dim_eq // -(capv0 A); congr (_ :&: _)%VS.
    by apply/eqP/lker0P=> v1 v2; rewrite !lfunE; apply: (mulIr Uv).
  by rewrite -[V in (_ <= V)%VS]prodv_id limg_amulr prodvSr // -memvE (valP w).
rewrite lfunE /= in v1w; apply/unitrP; exists (Subvs Av1).
split; apply: val_inj => //; apply: (mulIr Uv).
by rewrite /= -mulrA -v1w algidl ?algidr ?(valP w).
Qed.

Lemma vsval_invr (w : subvs_of A) :
  vsval w \is a GRing.unit -> val w^-1 = (vsval w)^-1.
Proof. 
by move=> Uv; apply: (mulIr Uv); rewrite -{4}[w](mulVKr (vsval_unitr Uv)) mulKr.
Qed.
(* Note that this implies algid A = 1. *)

End SubFalgType.

Section AHom.

Variable K : fieldType.

Section Class_Def.

Variables aT rT : FalgType K.

Definition ahom_in (U : {vspace aT}) (f : 'Hom(aT, rT)) :=
  let fM_at x y := f (x * y) == f x * f y in
  all (fun x => all (fM_at x) (vbasis U)) (vbasis U) && (f 1 == 1).

Lemma ahom_inP {f : 'Hom(aT, rT)} {U : {vspace aT}} :
  reflect ({in U &, {morph f : x y / x * y >-> x * y}} * (f 1 = 1))
          (ahom_in U f).
Proof.
apply: (iffP andP) => [[/allP fM /eqP f1] | [fM f1]]; last first.
  rewrite f1; split=> //; apply/allP=> x Ax; apply/allP=> y Ay.
  by rewrite fM // vbasis_mem.
split=> // x y  /coord_vbasis -> /coord_vbasis ->.
rewrite !mulr_suml ![f _]linear_sum mulr_suml; apply: eq_bigr => i _ /=.
rewrite !mulr_sumr linear_sum; apply: eq_bigr => j _ /=.
rewrite !linearZ -!scalerAr -!scalerAl 2!linearZ /=; congr (_ *: (_ *: _)).
by apply/eqP/(allP (fM _ _)); apply: memt_nth.
Qed.

Lemma ahomP {f : 'Hom(aT, rT)} : reflect (lrmorphism f) (ahom_in {:aT} f).
Proof.
apply: (iffP ahom_inP) => [[fM f1] | fRM_P]; last first.
  pose fRM := LRMorphism fRM_P.
  by split; [apply: in2W (rmorphM fRM) | apply: (rmorph1 fRM)].
split; last exact: linearZZ; split; first exact: linearB.
by split=> // x y; rewrite fM ?memvf.
Qed.

Structure ahom := AHom {ahval :> 'Hom(aT, rT); _ : ahom_in {:aT} ahval}.

Canonical ahom_subType := Eval hnf in [subType for ahval].
Definition ahom_eqMixin := [eqMixin of ahom by <:].
Canonical ahom_eqType := Eval hnf in EqType ahom ahom_eqMixin.

Definition ahom_choiceMixin := [choiceMixin of ahom by <:].
Canonical ahom_choiceType := Eval hnf in ChoiceType ahom ahom_choiceMixin.

End Class_Def.

Implicit Arguments ahom_in [aT rT].
Implicit Arguments ahom_inP [aT rT f U].
Implicit Arguments ahomP [aT rT f].

Section LRMorphism.

Variables aT rT sT : FalgType K.

Fact ahom_is_lrmorphism (f : ahom aT rT) : lrmorphism f.
Proof. by apply/ahomP; case: f. Qed.
Canonical ahom_rmorphism f := Eval hnf in AddRMorphism (ahom_is_lrmorphism f).
Canonical ahom_lrmorphism f := Eval hnf in AddLRMorphism (ahom_is_lrmorphism f).

Lemma ahomWin (f : ahom aT rT) U : ahom_in U f.
Proof.
by apply/ahom_inP; split; [apply: in2W (rmorphM _) | apply: rmorph1].
Qed.

Lemma id_is_ahom (V : {vspace aT}) : ahom_in V \1.
Proof. by apply/ahom_inP; split=> [x y|] /=; rewrite !id_lfunE. Qed.

Lemma comp_is_ahom (V : {vspace aT}) (f : 'Hom(rT, sT)) (g : 'Hom(aT, rT)) :
  ahom_in {:rT} f -> ahom_in V g -> ahom_in V (f \o g).
Proof.
move=> /ahom_inP fM /ahom_inP gM; apply/ahom_inP.
by split=> [x y Vx Vy|] /=; rewrite !comp_lfunE gM // fM ?memvf.
Qed.

Canonical id_ahom := AHom (id_is_ahom (aspacef aT)).

Canonical comp_ahom (f : ahom rT sT) (g : ahom aT rT) :=
  AHom (comp_is_ahom (valP f) (valP g)).

Lemma aimgM (f : ahom aT rT) U V : (f @: (U * V) = f @: U * f @: V)%VS.
Proof.
apply/eqP; rewrite eqEsubv; apply/andP; split; last first.
  apply/prodvP=> _ _ /memv_imgP[u Hu ->] /memv_imgP[v Hv ->].
  by rewrite -rmorphM memv_img // memv_prod.
apply/subvP=> _ /memv_imgP[w UVw ->]; rewrite memv_preim (subvP _ w UVw) //.
by apply/prodvP=> u v Uu Vv; rewrite -memv_preim rmorphM memv_prod // memv_img.
Qed.

Lemma aimg1 (f : ahom aT rT) : (f @: 1 = 1)%VS.
Proof. by rewrite limg_line rmorph1. Qed.

Lemma aimgX (f : ahom aT rT) U n : (f @: (U ^+ n) = f @: U ^+ n)%VS.
Proof.
elim: n => [|n IH]; first by rewrite !expv0 aimg1.
by rewrite !expvSl aimgM IH.
Qed.

Lemma aimg_agen (f : ahom aT rT) U : (f @: agenv U)%VS = agenv (f @: U).
Proof.
apply/eqP; rewrite eqEsubv; apply/andP; split.
  by rewrite limg_sum; apply/subv_sumP => i _; rewrite aimgX subX_agenv.
apply: agenv_sub_ideall; first by rewrite -(aimg1 f) limgS // sub1_agenv.
by rewrite -aimgM limgS // [rhs in (_ <= rhs)%VS]agenvEl addvSr.
Qed.

Lemma aimg_adjoin (f : ahom aT rT) U x : (f @: <<U; x>> = <<f @: U; f x>>)%VS.
Proof. by rewrite aimg_agen limg_add limg_line. Qed.

Lemma aimg_adjoin_seq (f : ahom aT rT) U xs :
  (f @: <<U & xs>> = <<f @: U & map f xs>>)%VS.
Proof. by rewrite aimg_agen limg_add limg_span. Qed.

End LRMorphism.

Variable (aT : FalgType K) (f : ahom aT aT).

Fact fixedSpace_is_aspace : is_aspace (fixedSpace f).
Proof.
apply/andP; split; first exact/has_algid1/fixedSpaceP/rmorph1.
apply/prodvP => a b /fixedSpaceP fa_a /fixedSpaceP fb_b.
by apply/fixedSpaceP; rewrite rmorphM /= fa_a fb_b.
Qed.
Canonical fixedSpace_aspace : {aspace aT} := ASpace fixedSpace_is_aspace.

End AHom.

Implicit Arguments ahom_in [K aT rT].

Notation "''AHom' ( aT , rT )" := (ahom aT rT) : type_scope.
Notation "''AEnd' ( aT )" := (ahom aT aT) : type_scope.

Delimit Scope lrfun_scope with AF.
Bind Scope lrfun_scope with ahom. 

Notation "\1" := (@id_ahom _ _) : lrfun_scope.
Notation "f \o g" := (comp_ahom f g) : lrfun_scope.
