(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype bigop.
Require Import finfun tuple ssralg matrix mxalgebra zmodp.
(******************************************************************************)
(*  * Finite dimensional vector spaces                                        *)
(*           vectType R == interface structure for finite dimensional (more   *)
(*                         precisely, detachable) vector spaces over R, which *)
(*                         should be at least a ringType.                     *)
(*     Vector.axiom n M <-> type M is linearly isomorphic to 'rV_n.           *)
(*                         := {v2r : M -> 'rV_n| linear v2r & bijective v2r}. *)
(*       VectMixin isoM == packages a proof isoV of Vector.axiom n M as the   *)
(*                         vectType mixin for an n-dimensional R-space        *)
(*                         structure on a type M that is an lmodType R.       *)
(*      VectType K M mT == packs the vectType mixin mT to into a vectType K   *)
(*                         instance for T; T should have an lmodType K        *)
(*                         canonical instance.                                *)
(* [vectType R of T for vS] == a copy of the vS : vectType R structure where  *)
(*                         the sort is replaced by T; vS : lmodType R should  *)
(*                         be convertible to a canonical lmodType for T.      *)
(*    [vectType R of V] == a clone of an existing vectType R structure on V.  *)
(*          {vspace vT} == the type of (detachable) subspaces of vT; vT       *)
(*                         should have a vectType structure over a fieldType. *)
(*           subvs_of U == the subtype of elements of V in the subspace U.    *)
(*                         This is canonically a vectType.                    *)
(*               vsval u == linear injection of u : subvs_of U into V.        *)
(*            vsproj U v == linear projection of v : V in subvs U.            *)
(*         'Hom(aT, rT) == the type of linear functions (homomorphisms) from  *)
(*                         aT to rT, where aT and rT ARE vectType structures. *)
(*                         Elements of 'Hom(aT, rT) coerce to Coq functions.  *)
(* --> Caveat: aT and rT must denote actual vectType structures, not their    *)
(*     projections on Type.                                                   *)
(*             linfun f == a vector linear function in 'Hom(aT, rT) that      *)
(*                         coincides with f : aT -> rT when f is linear.      *)
(*             'End(vT) == endomorphisms of vT (:= 'Hom(vT, vT)).             *)
(* --> The types subvs_of U, 'Hom(aT, rT), 'End(vT), K^o, 'M[K]_(m, n),       *)
(*     vT * wT, {ffun I -> vT}, vT ^ n all have canonical vectType instances. *)
(*                                                                            *)
(*  Functions:                                                                *)
(*                v%:VS == a vector space of dimension 1 composed of v.       *)
(*                 0%VS == the trivial vector subspace.                       *)
(*                fullv == the complete vector subspace.                      *)
(*           (U + V)%VS == the join (sum) of two subspaces U and V.           *)
(*         (U :&: V)%VS == intersection of vector subspaces U and V.          *)
(*             (U^C)%VS == a complement of the vector subspace U.             *)
(*         (U :\: V)%VS == a local complement to U :& V in the subspace U.    *)
(*               \dim U == dimension of a vector space U.                     *)
(*               span B == the subspace spanned by the vector sequence B.     *)
(*          coord B i v == i'th coordinate of v on B, when v \in span B, and  *)
(*                         where B : n.-tuple vT and i : 'I_n. Note that      *)
(*                         coord b i is a scalar function.                    *)
(*              vpick U == pick an nonzero element of U, or 0 if U is 0%VS.   *)
(*             vbasis U == a (\dim U).-tuple that is a basis of U.            *)
(*                \1%VF == the identity linear function.                      *)
(*          (f \o g)%VF == the composite of two linear functions f and g.     *)
(*            (f^-1)%VF == a linear function that is a right inverse to the   *)
(*                         linear function f on the codomain of f.            *)
(*          (f @: U)%VS == the image of vs by the linear function f.          *)
(*       (f @^-1: U)%VS == the pre-image of vs by the linear function f.      *)
(*               lker f == the kernel of the linear function f.               *)
(*               limg f == the image of the linear function f.                *)
(*         daddv_pi U V == projection onto U along V if U and V are disjoint; *)
(*                         daddv_pi U V + daddv_pi V U is then a projection   *)
(*                         onto the direct sum (U + V)%VS.                    *)
(*              projv U == projection onto U (along U^C, := daddv_pi U U^C).  *)
(*         addv_pi1 U V == projection onto the subspace U :\: V of U along V. *)
(*         addv_pi2 U V == projection onto V along U :\: V; note that         *)
(*                         addv_pi1 U V and addv_pi2 U V are (asymmetrical)   *)
(*                         complementary projections on (U + V)%VS.           *)
(*   sumv_pi_for defV i == for defV : V = (V \sum_(j <- r | P j) Vs j)%VS,    *)
(*                         j ranging over an eqType, this is a projection on  *)
(*                         a subspace of Vs i, along a complement in V, such  *)
(*                         that \sum_(j <- r | P j) sumv_pi_for defV j is a   *)
(*                         projection onto V if filter P r is duplicate-free  *)
(*                         (e.g., when V := \sum_(j | P j) Vs j).             *)
(*          sumv_pi V i == notation the above when defV == erefl V, and V is  *)
(*                         convertible to \sum_(j <- r | P j) Vs j)%VS.       *)
(*                                                                            *)
(*  Predicates:                                                               *)
(*              v \in U == v belongs to U (:= (v%:VS <= U)%VS).               *)
(*          (U <= V)%VS == U is a subspace of V.                              *)
(*               free B == B is a sequence of nonzero linearly independent    *)
(*                         vectors.                                           *)
(*         basis_of U b == b is a basis of the subspace U.                    *)
(*            directv S == S is the expression for a direct sum of subspaces. *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Local Scope ring_scope.

Reserved Notation "{ 'vspace' T }" (at level 0, format "{ 'vspace'  T }").
Reserved Notation "''Hom' ( T , rT )" (at level 8, format "''Hom' ( T ,  rT )").
Reserved Notation "''End' ( T )" (at level 8, format "''End' ( T )").
Reserved Notation "\dim A" (at level 10, A at level 8, format "\dim  A").
Reserved Notation "v %:VS" (at level 2, format "v %:VS").

Delimit Scope vspace_scope with VS.

Import GRing.Theory.

(* Finite dimension vector space *)
Module Vector.

Section ClassDef.
Variable R : ringType.

Definition axiom_def n (V : lmodType R) of phant V :=
  {v2r : V -> 'rV[R]_n | linear v2r & bijective v2r}.

Inductive mixin_of (V : lmodType R) := Mixin dim & axiom_def dim (Phant V).

Structure class_of V := Class {
  base : GRing.Lmodule.class_of R V;
  mixin : mixin_of (GRing.Lmodule.Pack _ base V)
}.
Local Coercion base : class_of >-> GRing.Lmodule.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c _ := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack phR T c T.
Definition dim := let: Mixin n _ := mixin class in n.

Definition pack b0 (m0 : mixin_of (@GRing.Lmodule.Pack R _ T b0 T)) :=
  fun bT b & phant_id (@GRing.Lmodule.class _ phR bT) b =>
  fun    m & phant_id m0 m => Pack phR (@Class T b m) T.

Definition eqType := Equality.Pack class cT.
Definition choiceType := Choice.Pack class cT.
Definition zmodType := GRing.Zmodule.Pack class cT.
Definition lmodType := GRing.Lmodule.Pack phR class cT.

End ClassDef.
Notation axiom n V := (axiom_def n (Phant V)).

Section OtherDefs.
Local Coercion sort : type >-> Sortclass.
Local Coercion dim : type >-> nat.
Inductive space (K : fieldType) (vT : type (Phant K)) (phV : phant vT) :=
  Space (mx : 'M[K]_vT) & <<mx>>%MS == mx.
Inductive hom (R : ringType) (vT wT : type (Phant R)) :=
  Hom of 'M[R]_(vT, wT).
End OtherDefs.

Module Import Exports.

Coercion base : class_of >-> GRing.Lmodule.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType: type >->  Equality.type.
Bind Scope ring_scope with sort.
Canonical eqType.
Coercion choiceType: type >-> Choice.type.
Canonical choiceType.
Coercion zmodType: type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion lmodType: type>->  GRing.Lmodule.type.
Canonical lmodType.
Notation vectType R := (@type _ (Phant R)).
Notation VectType R V mV :=
   (@pack _ (Phant R) V _ mV _ _ id _ id).
Notation VectMixin := Mixin.
Notation "[ 'vectType' R 'of' T 'for' cT ]" := (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'vectType'  R  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'vectType' R 'of' T ]" := (@clone _ (Phant R) T _ _ idfun)
  (at level 0, format "[ 'vectType'  R  'of'  T ]") : form_scope.

Notation "{ 'vspace' vT }" := (space (Phant vT)) : type_scope.
Notation "''Hom' ( aT , rT )" := (hom aT rT) : type_scope.
Notation "''End' ( vT )" := (hom vT vT) : type_scope.

Prenex Implicits Hom.

Delimit Scope vspace_scope with VS.
Bind Scope vspace_scope with space.
Delimit Scope lfun_scope with VF.
Bind Scope lfun_scope with hom.

End Exports.

(* The contents of this module exposes the matrix encodings, and should       *)
(* therefore not be used outside of the vector library implementation.        *)
Module InternalTheory.

Section Iso.
Variables (R : ringType) (vT rT : vectType R).
Local Coercion dim : vectType >-> nat.

Fact v2r_subproof : axiom vT vT. Proof. by case: vT => T [bT []]. Qed.
Definition v2r := s2val v2r_subproof.

Let v2r_bij : bijective v2r := s2valP' v2r_subproof.
Fact r2v_subproof : {r2v | cancel r2v v2r}.
Proof.
have r2vP r: {v | v2r v = r}.
  by apply: sig_eqW; have [v _ vK] := v2r_bij; exists (v r).
by exists (fun r => sval (r2vP r)) => r; case: (r2vP r).
Qed. 
Definition r2v := sval r2v_subproof.

Lemma r2vK : cancel r2v v2r.   Proof. exact: (svalP r2v_subproof). Qed.
Lemma r2v_inj : injective r2v. Proof. exact: can_inj r2vK. Qed.
Lemma v2rK : cancel v2r r2v.   Proof. by have/bij_can_sym:= r2vK; apply. Qed.
Lemma v2r_inj : injective v2r. Proof. exact: can_inj v2rK. Qed.

Canonical v2r_linear := Linear (s2valP v2r_subproof : linear v2r).
Canonical r2v_linear := Linear (can2_linear v2rK r2vK).
End Iso.

Section Vspace.
Variables (K : fieldType) (vT : vectType K).
Local Coercion dim : vectType >-> nat.

Definition b2mx n (X : n.-tuple vT) := \matrix_i v2r (tnth X i).
Lemma b2mxK n (X : n.-tuple vT) i : r2v (row i (b2mx X)) = X`_i.
Proof. by rewrite rowK v2rK -tnth_nth. Qed.

Definition vs2mx {phV} (U : @space K vT phV) := let: Space mx _ := U in mx.
Lemma gen_vs2mx (U : {vspace vT}) : <<vs2mx U>>%MS = vs2mx U.
Proof. by apply/eqP; rewrite /vs2mx; case: U. Qed.

Fact mx2vs_subproof m (A : 'M[K]_(m, vT)) : <<(<<A>>)>>%MS == <<A>>%MS.
Proof. by rewrite genmx_id. Qed.
Definition mx2vs {m} A : {vspace vT} := Space _ (@mx2vs_subproof m A).

Canonical space_subType := [subType for vs2mx by @space_rect K _ (Phant vT)].
Lemma vs2mxK : cancel vs2mx mx2vs.
Proof. by move=> v; apply: val_inj; rewrite /= gen_vs2mx. Qed.
Lemma mx2vsK m (M : 'M_(m, vT)) : (vs2mx (mx2vs M) :=: M)%MS.
Proof. exact: genmxE. Qed.
End Vspace.

Section Hom.
Variables (R : ringType) (aT rT : vectType R).
Definition f2mx (f : 'Hom(aT, rT)) := let: Hom A := f in A.
Canonical hom_subType := [newType for f2mx by @hom_rect _ _ _].
End Hom.

Arguments Scope mx2vs [_ _ nat_scope matrix_set_scope].
Prenex Implicits v2r r2v v2rK r2vK b2mx vs2mx vs2mxK f2mx.

End InternalTheory.

End Vector.
Export Vector.Exports.
Import Vector.InternalTheory.

Section VspaceDefs.

Variables (K : fieldType) (vT : vectType K).
Implicit Types (u : vT) (X : seq vT) (U V : {vspace vT}).

Definition space_eqMixin := Eval hnf in [eqMixin of {vspace vT} by <:].
Canonical space_eqType := EqType {vspace vT} space_eqMixin.
Definition space_choiceMixin := Eval hnf in [choiceMixin of {vspace vT} by <:].
Canonical space_choiceType := ChoiceType {vspace vT} space_choiceMixin.

Definition dimv U := \rank (vs2mx U).
Definition subsetv U V := (vs2mx U <= vs2mx V)%MS.
Definition injv u := mx2vs (v2r u).

(* Vspace membership is defined via the injv injection. *)
Definition pred_of_vspace phV (U : Vector.space phV) : pred_class :=
  fun v => (vs2mx (injv v) <= vs2mx U)%MS.
Canonical vspace_predType :=
  @mkPredType _ (unkeyed {vspace vT}) (@pred_of_vspace _).

Definition fullv : {vspace vT} := mx2vs 1%:M.
Definition addv U V := mx2vs (vs2mx U + vs2mx V).
Definition capv U V := mx2vs (vs2mx U :&: vs2mx V).
Definition complv U := mx2vs (vs2mx U)^C.
Definition diffv U V := mx2vs (vs2mx U :\: vs2mx V).
Definition vpick U := r2v (nz_row (vs2mx U)).
Definition span X := locked (mx2vs (b2mx (in_tuple X))).
Definition vbasis U :=
  locked [tuple r2v (row i (row_base (vs2mx U))) | i < dimv U].
(* coord and directv are defined in the VectorTheory section. *)

Definition free X := dimv (span X) == size X.
Definition basis_of U X := (span X == U) && free X.

End VspaceDefs.

Coercion pred_of_vspace : Vector.space >-> pred_class.
Notation "\dim U" := (dimv U) : nat_scope.
Notation "U <= V" := (subsetv U V) : vspace_scope.
Notation "U <= V <= W" := (subsetv U V && subsetv V W) : vspace_scope.
Notation "v %:VS" := (injv v) : ring_scope.
Notation "0" := (injv 0) : vspace_scope.
Implicit Arguments fullv [[K] [vT]].
Prenex Implicits subsetv addv capv complv diffv span free basis_of.

Notation "U + V" := (addv U V) : vspace_scope.
Notation "U :&: V" := (capv U V) : vspace_scope.
Notation "U ^C" := (complv U) : vspace_scope.
Notation "U :\: V" := (diffv U V) : vspace_scope.

Notation "\sum_ ( <- r | P ) U" :=
  (\big[addv/0%VS]_(<- r | P%B) U%VS) : vspace_scope.
Notation "\sum_ ( i <- r | P ) U" :=
  (\big[addv/0%VS]_(i <- r | P%B) U%VS) : vspace_scope.
Notation "\sum_ ( i <- r ) U" :=
  (\big[addv/0%VS]_(i <- r) U%VS) : vspace_scope.
Notation "\sum_ ( m <= i < n | P ) U" :=
  (\big[addv/0%VS]_(m <= i < n | P%B) U%VS) : vspace_scope.
Notation "\sum_ ( m <= i < n ) U" :=
  (\big[addv/0%VS]_(m <= i < n) U%VS) : vspace_scope.
Notation "\sum_ ( i | P ) U" :=
  (\big[addv/0%VS]_(i | P%B) U%VS) : vspace_scope.
Notation "\sum_ i U" :=
  (\big[addv/0%VS]_i U%VS) : vspace_scope.
Notation "\sum_ ( i : t | P ) U" :=
  (\big[addv/0%VS]_(i : t | P%B) U%VS) (only parsing) : vspace_scope.
Notation "\sum_ ( i : t ) U" :=
  (\big[addv/0%VS]_(i : t) U%VS) (only parsing) : vspace_scope.
Notation "\sum_ ( i < n | P ) U" :=
  (\big[addv/0%VS]_(i < n | P%B) U%VS) : vspace_scope.
Notation "\sum_ ( i < n ) U" :=
  (\big[addv/0%VS]_(i < n) U%VS) : vspace_scope.
Notation "\sum_ ( i \in A | P ) U" :=
  (\big[addv/0%VS]_(i \in A | P%B) U%VS) : vspace_scope.
Notation "\sum_ ( i \in A ) U" :=
  (\big[addv/0%VS]_(i \in A) U%VS) : vspace_scope.

Notation "\bigcap_ ( <- r | P ) U" :=
  (\big[capv/fullv]_(<- r | P%B) U%VS) : vspace_scope.
Notation "\bigcap_ ( i <- r | P ) U" :=
  (\big[capv/fullv]_(i <- r | P%B) U%VS) : vspace_scope.
Notation "\bigcap_ ( i <- r ) U" :=
  (\big[capv/fullv]_(i <- r) U%VS) : vspace_scope.
Notation "\bigcap_ ( m <= i < n | P ) U" :=
  (\big[capv/fullv]_(m <= i < n | P%B) U%VS) : vspace_scope.
Notation "\bigcap_ ( m <= i < n ) U" :=
  (\big[capv/fullv]_(m <= i < n) U%VS) : vspace_scope.
Notation "\bigcap_ ( i | P ) U" :=
  (\big[capv/fullv]_(i | P%B) U%VS) : vspace_scope.
Notation "\bigcap_ i U" :=
  (\big[capv/fullv]_i U%VS) : vspace_scope.
Notation "\bigcap_ ( i : t | P ) U" :=
  (\big[capv/fullv]_(i : t | P%B) U%VS) (only parsing) : vspace_scope.
Notation "\bigcap_ ( i : t ) U" :=
  (\big[capv/(fullv _)]_(i : t) U%VS) (only parsing) : vspace_scope.
Notation "\bigcap_ ( i < n | P ) U" :=
  (\big[capv/fullv]_(i < n | P%B) U%VS) : vspace_scope.
Notation "\bigcap_ ( i < n ) U" :=
  (\big[capv/fullv]_(i < n) U%VS) : vspace_scope.
Notation "\bigcap_ ( i \in A | P ) U" :=
  (\big[capv/fullv]_(i \in A | P%B) U%VS) : vspace_scope.
Notation "\bigcap_ ( i \in A ) U" :=
  (\big[capv/fullv]_(i \in A) U%VS) : vspace_scope.

Section VectorTheory.

Variables (K : fieldType) (vT : vectType K).
Implicit Types (a : K) (u v w : vT) (X Y : seq vT) (U V W : {vspace vT}).

Local Notation subV := (@subsetv K vT) (only parsing).
Local Notation addV := (@addv K vT) (only parsing).
Local Notation capV := (@capv K vT) (only parsing).

(* begin hide *) (* Internal theory facts *)
Let vs2mxP U V : reflect (U = V) (vs2mx U == vs2mx V)%MS.
Proof. by rewrite (sameP genmxP eqP) !gen_vs2mx; apply: eqP. Qed.

Let memvK v U : (v \in U) = (v2r v <= vs2mx U)%MS.
Proof. by rewrite -genmxE. Qed.

Let mem_r2v rv U : (r2v rv \in U) = (rv <= vs2mx U)%MS.
Proof. by rewrite memvK r2vK. Qed.

Let vs2mx0 : @vs2mx K vT _ 0 = 0.
Proof. by rewrite /= linear0 genmx0. Qed.

Let vs2mxD U V : vs2mx (U + V) = (vs2mx U + vs2mx V)%MS.
Proof. by rewrite /= genmx_adds !gen_vs2mx. Qed.

Let vs2mx_sum := big_morph _ vs2mxD vs2mx0.

Let vs2mxI U V : vs2mx (U :&: V) = (vs2mx U :&: vs2mx V)%MS.
Proof. by rewrite /= genmx_cap !gen_vs2mx. Qed.

Let vs2mxF : vs2mx (@fullv K vT) = 1%:M.
Proof. by rewrite /= genmx1. Qed.

Let row_b2mx n (X : n.-tuple vT) i : row i (b2mx X) = v2r X`_i.
Proof. by rewrite -tnth_nth rowK. Qed.

Let span_b2mx n (X : n.-tuple vT) : span X = mx2vs (b2mx X).
Proof. by unlock span; rewrite tvalK; case: _ / (esym _). Qed.

Let mul_b2mx n (X : n.-tuple vT) (rk : 'rV_n) :
  \sum_i rk 0 i *: X`_i = r2v (rk *m b2mx X).
Proof.
rewrite mulmx_sum_row linear_sum; apply: eq_bigr => i _.
by rewrite row_b2mx linearZ /= v2rK.
Qed.

Let lin_b2mx n (X : n.-tuple vT) k :  
  \sum_(i < n) k i *: X`_i = r2v (\row_i k i *m b2mx X).
Proof. by rewrite -mul_b2mx; apply: eq_bigr => i _; rewrite mxE. Qed.

Let free_b2mx n (X : n.-tuple vT) : free X = row_free (b2mx X).
Proof. by rewrite /free /dimv span_b2mx genmxE size_tuple. Qed.
(* end hide *)

Fact vspace_key U : pred_key U. Proof. by []. Qed.
Canonical vspace_keyed U := KeyedPred (vspace_key U).

Lemma memvE v U : (v \in U) = (v%:VS <= U)%VS. Proof. by []. Qed.

Lemma injvP v1 v2 : reflect (exists k, v1 = k *: v2) (v1 \in v2%:VS).
Proof.
apply: (iffP idP) => [|[k ->]]; rewrite memvK genmxE ?linearZ ?scalemx_sub //.
by case/sub_rVP=> k; rewrite -linearZ => /v2r_inj->; exists k.
Qed.

Fact memv_submod_closed U : submod_closed U.
Proof.
split=> [|a u v]; rewrite !memvK ?linear0 ?sub0mx // => Uu Uv.
by rewrite linearP addmx_sub ?scalemx_sub.
Qed.
Canonical memv_opprPred U := OpprPred (memv_submod_closed U).
Canonical memv_addrPred U := AddrPred (memv_submod_closed U).
Canonical memv_zmodPred U := ZmodPred (memv_submod_closed U).
Canonical memv_submodPred U := SubmodPred (memv_submod_closed U).

Lemma mem0v U : 0 \in U. Proof. exact : rpred0. Qed.
Lemma memvN U v : (- v \in U) = (v \in U). Proof. exact: rpredN. Qed.
Lemma memvD U : {in U &, forall u v, u + v \in U}. Proof. exact : rpredD. Qed.
Lemma memvB U : {in U &, forall u v, u - v \in U}. Proof. exact : rpredB. Qed.
Lemma memvZ U k : {in U, forall v, k *: v \in U}. Proof. exact : rpredZ. Qed.

(* Generalize and move to ssralg. *)
Lemma memvZeq U k v : (k *: v \in U) = (k == 0) || (v \in U).
Proof.
have [-> | nz_k] := altP eqP; first by rewrite scale0r rpred0.
by apply/idP/idP; first rewrite -{2}(scalerK nz_k v); apply: rpredZ.
Qed.

Lemma memv_suml I r (P : pred I) vs U :
  (forall i, P i -> vs i \in U) -> \sum_(i <- r | P i) vs i \in U.
Proof. exact: rpred_sum. Qed.

Lemma memv_inj u : u \in u%:VS.
Proof. by apply/injvP; exists 1; rewrite scale1r. Qed.

Lemma subvP U V : reflect {subset U <= V} (U <= V)%VS.
Proof.
apply: (iffP rV_subP) => sU12 u.
  by rewrite !memvE /subsetv !genmxE => /sU12.
by have:= sU12 (r2v u); rewrite !memvE /subsetv !genmxE r2vK.
Qed.

Lemma subv_refl U : (U <= U)%VS. Proof. exact/subvP. Qed.
Hint Resolve subv_refl.

Lemma subv_trans : transitive subV.
Proof. by move=> U V W /subvP sUV /subvP sVW; apply/subvP=> u /sUV/sVW. Qed.

Lemma subv_anti : antisymmetric subV.
Proof. by move=> U V; apply/vs2mxP. Qed.

Lemma eqEsubv U V : (U == V) = (U <= V <= U)%VS.
Proof. by apply/eqP/idP=> [-> | /subv_anti//]; rewrite subv_refl. Qed.

Lemma vspaceP U V : U =i V <-> U = V.
Proof.
split=> [eqUV | -> //]; apply/subv_anti/andP.
by split; apply/subvP=> v; rewrite eqUV.
Qed.

Lemma subvPn {U V} : reflect (exists2 u, u \in U & u \notin V) (~~ (U <= V)%VS).
Proof.
apply: (iffP idP) => [|[u Uu]]; last by apply: contra => /subvP->.
case/row_subPn=> i; set vi := row i _ => V'vi.
by exists (r2v vi); rewrite memvK r2vK ?row_sub.
Qed.

(* Empty space. *)
Lemma sub0v U : (0 <= U)%VS.
Proof. exact: mem0v. Qed.

Lemma subv0 U : (U <= 0)%VS = (U == 0%VS).
Proof. by rewrite eqEsubv sub0v andbT. Qed.

Lemma memv0 v : v \in 0%VS = (v == 0).
Proof. by apply/idP/eqP=> [/injvP[k ->] | ->]; rewrite (scaler0, mem0v). Qed.

(* Full space *)

Lemma subvf U : (U <= fullv)%VS. Proof. by rewrite /subsetv vs2mxF submx1. Qed.
Lemma memvf v : v \in fullv. Proof. exact: subvf. Qed.

(* Picking a non-zero vector in a subspace. *)
Lemma memv_pick U : vpick U \in U. Proof. by rewrite mem_r2v nz_row_sub. Qed.

Lemma vpick0 U : (vpick U == 0) = (U == 0%VS).
Proof. by  rewrite -memv0 mem_r2v -subv0 /subV vs2mx0 !submx0 nz_row_eq0. Qed.

(* Sum of subspaces. *)
Lemma subv_add U V W : (U + V <= W)%VS = (U <= W)%VS && (V <= W)%VS.
Proof. by rewrite /subV vs2mxD addsmx_sub. Qed.

Lemma addvS U1 U2 V1 V2 : (U1 <= U2 -> V1 <= V2 -> U1 + V1 <= U2 + V2)%VS.
Proof. by rewrite /subV !vs2mxD; apply: addsmxS. Qed.

Lemma addvSl U V : (U <= U + V)%VS.
Proof. by rewrite /subV vs2mxD addsmxSl. Qed.

Lemma addvSr U V : (V <= U + V)%VS.
Proof. by rewrite /subV vs2mxD addsmxSr. Qed.

Lemma addvC : commutative addV.
Proof. by move=> U V; apply/vs2mxP; rewrite !vs2mxD addsmxC submx_refl. Qed.

Lemma addvA : associative addV.
Proof. by move=> U V W; apply/vs2mxP; rewrite !vs2mxD addsmxA submx_refl. Qed.

Lemma addv_idPl {U V}: reflect (U + V = U)%VS (V <= U)%VS.
Proof. by rewrite /subV (sameP addsmx_idPl eqmxP) -vs2mxD; apply: vs2mxP. Qed.

Lemma addv_idPr {U V} : reflect (U + V = V)%VS (U <= V)%VS.
Proof. by rewrite addvC; apply: addv_idPl. Qed.

Lemma addvv : idempotent addV.
Proof. by move=> U; apply/addv_idPl. Qed.
 
Lemma add0v : left_id 0%VS addV.
Proof. by move=> U; apply/addv_idPr/sub0v. Qed.

Lemma addv0 : right_id 0%VS addV.
Proof. by move=> U; apply/addv_idPl/sub0v. Qed.

Lemma sumfv : left_zero fullv addV.
Proof. by move=> U; apply/addv_idPl/subvf. Qed.

Lemma addvf : right_zero fullv addV.
Proof. by move=> U; apply/addv_idPr/subvf. Qed.

Canonical addv_monoid := Monoid.Law addvA add0v addv0.
Canonical addv_comoid := Monoid.ComLaw addvC.

Lemma memv_add u v U V : u \in U -> v \in V -> u + v \in (U + V)%VS.
Proof. by rewrite !memvK genmxE linearD; apply: addmx_sub_adds. Qed.

Lemma memv_addP {w U V} :
  reflect (exists2 u, u \in U & exists2 v, v \in V & w = u + v)
          (w \in U + V)%VS.
Proof.
apply: (iffP idP) => [|[u Uu [v Vv ->]]]; last exact: memv_add.
rewrite memvK genmxE => /sub_addsmxP[r /(canRL v2rK)->].
rewrite linearD /=; set u := r2v _; set v := r2v _.
by exists u; last exists v; rewrite // mem_r2v submxMl.
Qed.

Section BigSum.
Variable I : finType.
Implicit Type P : pred I.

Lemma sumv_sup i0 P U Vs :
  P i0 -> (U <= Vs i0)%VS -> (U <= \sum_(i | P i) Vs i)%VS.
Proof. by move=> Pi0 /subv_trans-> //; rewrite (bigD1 i0) ?addvSl. Qed.
Implicit Arguments sumv_sup [P U Vs].

Lemma subv_sumP {P Us V} :
  reflect (forall i, P i -> Us i <= V)%VS  (\sum_(i | P i) Us i <= V)%VS.
Proof.
apply: (iffP idP) => [sUV i Pi | sUV].
  by apply: subv_trans sUV; apply: sumv_sup Pi _.
by elim/big_rec: _ => [|i W Pi sWV]; rewrite ?sub0v // subv_add sUV.
Qed.

Lemma memv_sumr P vs (Us : I -> {vspace vT}) :
    (forall i, P i -> vs i \in Us i) ->
  \sum_(i | P i) vs i \in (\sum_(i | P i) Us i)%VS.
Proof. by move=> Uv; apply/rpred_sum=> i Pi; apply/(sumv_sup i Pi)/Uv. Qed.

Lemma memv_sumP {P} {Us : I -> {vspace vT}} {v} : 
  reflect (exists2 vs, forall i, P i ->  vs i \in Us i
                     & v = \sum_(i | P i) vs i)
          (v \in \sum_(i | P i) Us i)%VS.
Proof.
apply: (iffP idP) => [|[vs Uv ->]]; last exact: memv_sumr.
rewrite memvK vs2mx_sum => /sub_sumsmxP[r /(canRL v2rK)->].
rewrite linear_sum /=; set f := fun i => r2v _; exists f => //= i _.
by rewrite mem_r2v submxMl.
Qed.

End BigSum.

(* Intersection *)

Lemma subv_cap U V W : (U <= V :&: W)%VS = (U <= V)%VS && (U <= W)%VS.
Proof. by rewrite /subV vs2mxI sub_capmx. Qed.

Lemma capvS U1 U2 V1 V2 : (U1 <= U2 -> V1 <= V2 -> U1 :&: V1 <= U2 :&: V2)%VS.
Proof. by rewrite /subV !vs2mxI; apply: capmxS. Qed.

Lemma capvSl U V : (U :&: V <= U)%VS.
Proof. by rewrite /subV vs2mxI capmxSl. Qed.

Lemma capvSr U V : (U :&: V <= V)%VS.
Proof. by rewrite /subV vs2mxI capmxSr. Qed.

Lemma capvC : commutative capV.
Proof. by move=> U V; apply/vs2mxP; rewrite !vs2mxI capmxC submx_refl. Qed.

Lemma capvA : associative capV.
Proof. by move=> U V W; apply/vs2mxP; rewrite !vs2mxI capmxA submx_refl. Qed.

Lemma capv_idPl {U V} : reflect (U :&: V = U)%VS (U <= V)%VS.
Proof. by rewrite /subV(sameP capmx_idPl eqmxP) -vs2mxI; apply: vs2mxP. Qed.

Lemma capv_idPr {U V} : reflect (U :&: V = V)%VS (V <= U)%VS.
Proof. by rewrite capvC; apply: capv_idPl. Qed.

Lemma capvv : idempotent capV.
Proof. by move=> U; apply/capv_idPl. Qed.

Lemma cap0v : left_zero 0%VS capV.
Proof. by move=> U; apply/capv_idPl/sub0v. Qed.

Lemma capv0 : right_zero 0%VS capV.
Proof. by move=> U; apply/capv_idPr/sub0v. Qed.

Lemma capfv : left_id fullv capV.
Proof. by move=> U; apply/capv_idPr/subvf. Qed.

Lemma capvf : right_id fullv capV.
Proof. by move=> U; apply/capv_idPl/subvf. Qed.

Canonical capv_monoid := Monoid.Law capvA capfv capvf.
Canonical capv_comoid := Monoid.ComLaw capvC.

Lemma memv_cap w U V : (w \in U :&: V)%VS = (w \in U) && (w \in V).
Proof. by rewrite !memvE subv_cap. Qed.

Lemma memv_capP {w U V} : reflect (w \in U /\ w \in V) (w \in U :&: V)%VS.
Proof. by rewrite memv_cap; apply: andP. Qed.

Lemma vspace_modl U V W : (U <= W -> U + (V :&: W) = (U + V) :&: W)%VS.
Proof.
by move=> sUV; apply/vs2mxP; rewrite !(vs2mxD, vs2mxI); exact/eqmxP/matrix_modl.
Qed.

Lemma vspace_modr  U V W : (W <= U -> (U :&: V) + W = U :&: (V + W))%VS.
Proof. by rewrite -!(addvC W) !(capvC U); apply: vspace_modl. Qed.

Section BigCap.
Variable I : finType.
Implicit Type P : pred I.

Lemma bigcapv_inf i0 P Us V :
  P i0 -> (Us i0 <= V -> \bigcap_(i | P i) Us i <= V)%VS.
Proof. by move=> Pi0; apply: subv_trans; rewrite (bigD1 i0) ?capvSl. Qed.

Lemma subv_bigcapP {P U Vs} :
  reflect (forall i, P i -> U <= Vs i)%VS (U <= \bigcap_(i | P i) Vs i)%VS.
Proof.
apply: (iffP idP) => [sUV i Pi | sUV].
  by rewrite (subv_trans sUV) ?(bigcapv_inf Pi).
by elim/big_rec: _ => [|i W Pi]; rewrite ?subvf // subv_cap sUV.
Qed.

End BigCap.

(* Complement *)
Lemma addv_complf U : (U + U^C)%VS = fullv.
Proof.
apply/vs2mxP; rewrite vs2mxD -gen_vs2mx -genmx_adds !genmxE submx1 sub1mx.
exact: addsmx_compl_full.
Qed.

Lemma capv_compl U : (U :&: U^C = 0)%VS.
Proof.
apply/val_inj; rewrite [val]/= vs2mx0 vs2mxI -gen_vs2mx -genmx_cap.
by rewrite capmx_compl genmx0.
Qed.

(* Difference *)
Lemma diffvSl U V : (U :\: V <= U)%VS.
Proof. by rewrite /subV genmxE diffmxSl. Qed.

Lemma capv_diff U V : ((U :\: V) :&: V = 0)%VS.
Proof.
apply/val_inj; rewrite [val]/= vs2mx0 vs2mxI -(gen_vs2mx V) -genmx_cap.
by rewrite capmx_diff genmx0.
Qed.

Lemma addv_diff_cap U V : (U :\: V + U :&: V)%VS = U.
Proof.
apply/vs2mxP; rewrite vs2mxD -genmx_adds !genmxE.
exact/eqmxP/addsmx_diff_cap_eq.
Qed.

Lemma addv_diff U V : (U :\: V + V = U + V)%VS.
Proof. by rewrite -{2}(addv_diff_cap U V) -addvA (addv_idPr (capvSr U V)). Qed.

(* Subspace dimension. *)
Lemma dimv0 : \dim (0%VS : {vspace vT}) = 0%N.
Proof. by rewrite /dimv vs2mx0 mxrank0. Qed.

Lemma dimv_eq0 U :  (\dim U == 0%N) = (U == 0%:VS).
Proof. by rewrite /dimv /= mxrank_eq0 {2}/eq_op /= linear0 genmx0. Qed.

Lemma dimvf : \dim (@fullv K vT) = Vector.dim vT.
Proof.  by rewrite /dimv vs2mxF mxrank1. Qed.

Lemma dim_injv v : \dim v%:VS = (v != 0).
Proof. by rewrite /dimv mxrank_gen rank_rV (can2_eq v2rK r2vK) linear0. Qed.

Lemma dimvS U V : (U <= V)%VS -> \dim U <= \dim V.
Proof. exact: mxrankS. Qed.

Lemma dimv_leqif_sup U V : (U <= V)%VS -> \dim U <= \dim V ?= iff (V <= U)%VS.
Proof. exact: mxrank_leqif_sup. Qed. 

Lemma dimv_leqif_eq U V : (U <= V)%VS -> \dim U <= \dim V ?= iff (U == V).
Proof. by rewrite eqEsubv; apply: mxrank_leqif_eq. Qed.

Lemma eqEdim U V : (U == V) = (U <= V)%VS && (\dim V <= \dim U).
Proof. by apply/idP/andP=> [/eqP | [/dimv_leqif_eq/geq_leqif]] ->. Qed.

Lemma dimv_compl U : \dim U^C = (\dim (@fullv K vT) - \dim U)%N.
Proof. by rewrite dimvf /dimv mxrank_gen mxrank_compl. Qed.

Lemma dimv_cap_compl U V : (\dim (U :&: V) + \dim (U :\: V))%N = \dim U.
Proof. by rewrite /dimv !mxrank_gen mxrank_cap_compl. Qed.

Lemma dimv_sum_cap U V : (\dim (U + V) + \dim (U :&: V) = \dim U + \dim V)%N.
Proof. by rewrite /dimv !mxrank_gen mxrank_sum_cap. Qed.

Lemma dimv_disjoint_sum U V :
  (U :&: V = 0)%VS -> \dim (U + V) = (\dim U + \dim V)%N.
Proof. by move=> dxUV; rewrite -dimv_sum_cap dxUV dimv0 addn0. Qed.

Lemma dimv_add_leqif U V :
  \dim (U + V) <= \dim U + \dim V ?= iff (U :&: V <= 0)%VS.
Proof.
by rewrite /dimv /subV !mxrank_gen vs2mx0 genmxE; apply: mxrank_adds_leqif.
Qed.

Lemma diffv_eq0 U V : (U :\: V == 0)%VS = (U <= V)%VS.
Proof.
rewrite -dimv_eq0 -(eqn_add2l (\dim (U :&: V))) addn0 dimv_cap_compl eq_sym.
by rewrite (dimv_leqif_eq (capvSl _ _)) (sameP capv_idPl eqP).
Qed.

Lemma dimv_leq_sum I r (P : pred I) (Us : I -> {vspace vT}) : 
  \dim (\sum_(i <- r | P i) Us i) <= \sum_(i <- r | P i) \dim (Us i).
Proof.
elim/big_rec2: _ => [|i d vs _ le_vs_d]; first by rewrite dim_injv eqxx.
by apply: (leq_trans (dimv_add_leqif _ _)); rewrite leq_add2l.
Qed.

Section SumExpr.

(* The vector direct sum theory clones the interface types of the matrix     *)
(* direct sum theory (see mxalgebra for the technical details), but          *)
(* nevetheless reuses much of the matrix theory.                             *)
Structure addv_expr := Sumv {
  addv_val :> wrapped {vspace vT};
  addv_dim : wrapped nat;
  _ : mxsum_spec (vs2mx (unwrap addv_val)) (unwrap addv_dim)
}.

(* Piggyback on mxalgebra theory. *)
Definition vs2mx_sum_expr_subproof (S : addv_expr) :
  mxsum_spec (vs2mx (unwrap S)) (unwrap (addv_dim S)).
Proof. by case: S. Qed.
Canonical vs2mx_sum_expr S := ProperMxsumExpr (vs2mx_sum_expr_subproof S).

Canonical trivial_addv U := @Sumv (Wrap U) (Wrap (\dim U)) (TrivialMxsum _).

Structure proper_addv_expr := ProperSumvExpr {
  proper_addv_val :> {vspace vT};
  proper_addv_dim :> nat;
  _ : mxsum_spec (vs2mx proper_addv_val) proper_addv_dim
}.

Definition proper_addvP (S : proper_addv_expr) :=
  let: ProperSumvExpr _ _ termS := S return mxsum_spec (vs2mx S) S in termS.

Canonical proper_addv (S : proper_addv_expr) :=
  @Sumv (wrap (S : {vspace vT})) (wrap (S : nat)) (proper_addvP S).

(* begin hide *)
(* GG: suppressed this because its addv_dim projection is disruptive.
Section Vector.
Variable v : vT.
Fact vector_addv_proof : addv_spec (v%:VS) (v != 0).
Proof. by rewrite -dim_injv; left. Qed.
Canonical vector_addv_expr := ProperSumvExpr vector_addv_proof.
End Vector. *)
(* end hide *)

Section Binary.
Variables S1 S2 : addv_expr.
Fact binary_addv_subproof :
  mxsum_spec (vs2mx (unwrap S1 + unwrap S2))
             (unwrap (addv_dim S1) + unwrap (addv_dim S2)).
Proof. by rewrite vs2mxD; apply: proper_mxsumP. Qed.
Canonical binary_addv_expr := ProperSumvExpr binary_addv_subproof.
End Binary.

Section Nary.
Variables (I : Type) (r : seq I) (P : pred I) (S_ : I -> addv_expr).
Fact nary_addv_subproof :
  mxsum_spec (vs2mx (\sum_(i <- r | P i) unwrap (S_ i)))
             (\sum_(i <- r | P i) unwrap (addv_dim (S_ i))).
Proof. by rewrite vs2mx_sum; apply: proper_mxsumP. Qed.
Canonical nary_addv_expr := ProperSumvExpr nary_addv_subproof.
End Nary.

Definition directv_def S of phantom {vspace vT} (unwrap (addv_val S)) :=
  \dim (unwrap S) == unwrap (addv_dim S).

End SumExpr.

Local Notation directv A := (directv_def (Phantom {vspace _} A%VS)).

Lemma directvE (S : addv_expr) :
  directv (unwrap S) = (\dim (unwrap S) == unwrap (addv_dim S)).
Proof. by []. Qed.

Lemma directvP {S : proper_addv_expr} : reflect (\dim S = S :> nat) (directv S).
Proof. exact: eqnP. Qed.

Lemma directv_trivial U : directv (unwrap (@trivial_addv U)).
Proof. exact: eqxx. Qed.

Lemma dimv_sum_leqif (S : addv_expr) :
  \dim (unwrap S) <= unwrap (addv_dim S) ?= iff directv (unwrap S).
Proof.
rewrite directvE; case: S => [[U] [d] /= defUd]; split=> //=.
rewrite /dimv; elim: {1}_ {U}_ d / defUd => // m1 m2 A1 A2 r1 r2 _ leA1 _ leA2.
by apply: leq_trans (leq_add leA1 leA2); rewrite mxrank_adds_leqif.
Qed.

Lemma directvEgeq (S : addv_expr) :
  directv (unwrap S) = (\dim (unwrap S) >= unwrap (addv_dim S)).
Proof. by rewrite leq_eqVlt ltnNge eq_sym !dimv_sum_leqif orbF. Qed.

Section BinaryDirect.

Lemma directv_addE (S1 S2 : addv_expr) :
  directv (unwrap S1 + unwrap S2)
    = [&& directv (unwrap S1), directv (unwrap S2)
        & unwrap S1 :&: unwrap S2 == 0]%VS.
Proof.
by rewrite /directv_def /dimv vs2mxD -mxdirectE mxdirect_addsE -vs2mxI -vs2mx0.
Qed.

Lemma directv_addP {U V} : reflect (U :&: V = 0)%VS (directv (U + V)).
Proof. by rewrite directv_addE !directv_trivial; apply: eqP. Qed.

Lemma directv_add_unique {U V} :
   reflect (forall u1 u2 v1 v2, u1 \in U -> u2 \in U -> v1 \in V -> v2 \in V ->
             (u1 + v1 == u2 + v2) = ((u1, v1) == (u2, v2)))
           (directv (U + V)).
Proof.
apply: (iffP directv_addP) => [dxUV u1 u2 v1 v2 Uu1 Uu2 Vv1 Vv2 | dxUV].
  apply/idP/idP=> [| /eqP[-> ->] //]; rewrite -subr_eq0 opprD addrACA addr_eq0.
  move/eqP=> eq_uv; rewrite xpair_eqE -subr_eq0 eq_uv oppr_eq0 subr_eq0 andbb.
  by rewrite -subr_eq0 -memv0 -dxUV memv_cap -memvN -eq_uv !memvB.
apply/eqP; rewrite -subv0; apply/subvP=> v /memv_capP[U1v U2v].
by rewrite memv0 -[v == 0]andbb {1}eq_sym -xpair_eqE -dxUV ?mem0v // addrC.
Qed.

End BinaryDirect.

Section NaryDirect.

Context {I : finType} {P : pred I}.

Lemma directv_sumP {Us : I -> {vspace vT}} :
  reflect (forall i, P i -> Us i :&: (\sum_(j | P j && (j != i)) Us j) = 0)%VS
          (directv (\sum_(i | P i) Us i)).
Proof.
rewrite directvE /= /dimv vs2mx_sum -mxdirectE; apply: (equivP mxdirect_sumsP).
by do [split=> dxU i /dxU; rewrite -vs2mx_sum -vs2mxI -vs2mx0] => [/val_inj|->].
Qed.

Lemma directv_sumE {Ss : I -> addv_expr} (xunwrap := unwrap) :
  reflect [/\ forall i, P i -> directv (unwrap (Ss i))
            & directv (\sum_(i | P i) xunwrap (Ss i))]
          (directv (\sum_(i | P i) unwrap (Ss i))).
Proof.
by rewrite !directvE /= /dimv 2!{1}vs2mx_sum -!mxdirectE; apply: mxdirect_sumsE.
Qed.

Lemma directv_sum_independent {Us : I -> {vspace vT}} :
   reflect (forall us,
               (forall i, P i -> us i \in Us i) -> \sum_(i | P i) us i = 0 ->
             (forall i, P i -> us i = 0))
           (directv (\sum_(i | P i) Us i)).
Proof.
apply: (iffP directv_sumP) => [dxU us Uu u_0 i Pi | dxU i Pi].
  apply/eqP; rewrite -memv0 -(dxU i Pi) memv_cap Uu //= -memvN -sub0r -{1}u_0.
  by rewrite (bigD1 i) //= addrC addKr memv_sumr // => j /andP[/Uu].
apply/eqP; rewrite -subv0; apply/subvP=> v.
rewrite memv_cap memv0 => /andP[Uiv /memv_sumP[us Uu Dv]].
have: \sum_(j | P j) [eta us with i |-> - v] j = 0.
  rewrite (bigD1 i) //= eqxx {1}Dv addrC -sumrB big1 // => j /andP[_ i'j].
  by rewrite (negPf i'j) subrr.
move/dxU/(_ i Pi); rewrite /= eqxx -oppr_eq0 => -> // j Pj.
by have [-> | i'j] := altP eqP; rewrite ?memvN // Uu ?Pj.
Qed.

Lemma directv_sum_unique {Us : I -> {vspace vT}} :
  reflect (forall us vs,
    (forall i, P i -> us i \in Us i) ->
              (forall i, P i -> vs i \in Us i) ->
            (\sum_(i | P i) us i == \sum_(i | P i) vs i)
              = (forallb i, P i ==> (us i == vs i)))
          (directv (\sum_(i | P i) Us i)).
Proof.
apply: (iffP directv_sum_independent) => [dxU us vs Uu Uv | dxU us Uu u_0 i Pi].
  apply/idP/forall_inP=> [|eq_uv]; last by apply/eqP/eq_bigr => i /eq_uv/eqP.
  rewrite -subr_eq0 -sumrB => /eqP/dxU eq_uv i Pi.
  by rewrite -subr_eq0 eq_uv // => j Pj; apply: memvB; move: j Pj.
apply/eqP; have:= esym (dxU us \0 Uu _); rewrite u_0 big1_eq eqxx.
by move/(_ _)/forall_inP=> -> // j _; apply: mem0v.
Qed.

End NaryDirect.

(* Linear span generated by a list of vectors *)
Lemma memv_span X v : v \in X -> v \in span X.
Proof.
unlock span => /seq_tnthP[i {v}->].
by rewrite memvK genmxE (eq_row_sub i) // rowK.
Qed.

Lemma memv_span1 v : v \in span [:: v].
Proof. by rewrite memv_span ?mem_head. Qed.

Lemma dim_span X : \dim (span X) <= size X.
Proof. by unlock span; rewrite /dimv genmxE rank_leq_row. Qed.

Lemma span_subvP {X U} : reflect {subset X <= U} (span X <= U)%VS.
Proof.
unlock subV span; rewrite genmxE; apply: (iffP row_subP) => /= [sXU | sXU i].
  by move=>  _ /seq_tnthP[i ->]; have:= sXU i; rewrite rowK memvK.
by rewrite rowK -memvK sXU ?mem_tnth.
Qed.

Lemma sub_span X Y : {subset X <= Y} -> (span X <= span Y)%VS.
Proof. by move=> sXY; apply/span_subvP=> v /sXY/memv_span. Qed.

Lemma eq_span X Y : X =i Y -> span X = span Y.
Proof.
by move=> eqXY; apply: subv_anti; rewrite !sub_span // => u; rewrite eqXY.
Qed.

Lemma span_def X : span X = (\sum_(u <- X) u%:VS)%VS.
Proof.
apply/subv_anti/andP; split.
  by apply/span_subvP=> v Xv; rewrite (big_rem v) // memvE addvSl.
by rewrite big_tnth; apply/subv_sumP=> i _; rewrite -memvE memv_span ?mem_tnth.
Qed.

Lemma span_nil : span (Nil vT) = 0%VS :> {vspace vT}.
Proof. by rewrite span_def big_nil. Qed.

Lemma span_seq1 v : span [:: v] = v%:VS.
Proof. by rewrite span_def big_seq1. Qed.

Lemma span_cons v X : span (v :: X) = (v%:VS + span X)%VS.
Proof. by rewrite !span_def big_cons. Qed.

Lemma span_cat X Y : span (X ++ Y) = (span X + span Y)%VS.
Proof. by rewrite !span_def big_cat. Qed.

(* Coordinates function; should perhaps be generalized to nat indices. *)

Definition coord :=
  locked (fun n (X : n.-tuple vT) i v => (v2r v *m pinvmx (b2mx X)) 0 i). 

Fact coord_is_scalar n (X : n.-tuple vT) i : scalar (coord X i).
Proof. by unlock coord => k u v; rewrite linearP mulmxDl -scalemxAl !mxE. Qed.
Canonical coord_addidive n Xn i := Additive (@coord_is_scalar n Xn i).
Canonical coord_linear n Xn i := AddLinear (@coord_is_scalar n Xn i).

Lemma coord_span n (X : n.-tuple vT) v :
  v \in span X -> v = \sum_i coord X i v *: X`_i.
Proof.
rewrite memvK span_b2mx genmxE => Xv.
by unlock coord; rewrite mul_b2mx mulmxKpV ?v2rK.
Qed.

(* Free generator sequences. *)

Lemma nil_free : free (Nil vT).
Proof. by rewrite /free span_nil dimv0. Qed.

Lemma seq1_free v : free [:: v] = (v != 0).
Proof. by rewrite /free span_seq1 dim_injv; case: (~~ _). Qed.
 
Lemma perm_free X Y : perm_eq X Y -> free X = free Y.
Proof. 
by move=> eqX; rewrite /free (perm_eq_size eqX) (eq_span (perm_eq_mem eqX)).
Qed.

Lemma free_directv X : free X = (0 \notin X) && directv (\sum_(v <- X) v%:VS).
Proof.
have leXi i (v := tnth (in_tuple X) i): true -> \dim v%:VS <= 1 ?= iff (v != 0).
  by rewrite -seq1_free -span_seq1 => _; apply/leqif_eq/dim_span.
have [_ /=] := leqif_trans (dimv_sum_leqif _) (leqif_sum leXi).
rewrite sum1_card card_ord !directvE /= /free andbC span_def !(big_tnth _ _ X).
by congr (_ = _ && _); rewrite -has_pred1 -all_predC -big_all big_tnth big_andE.
Qed.

Lemma free_not0 v X : free X -> v \in X -> v != 0.
Proof. by rewrite free_directv andbC => /andP[_ /memPn]; apply. Qed.

Lemma freeP n (X : n.-tuple vT) :  
  reflect (forall k, \sum_(i < n) k i *: X`_i = 0 -> (forall i, k i = 0))
          (free X).
Proof.
rewrite free_b2mx; apply: (iffP idP) => [t_free k kt0 i | t_free].
  suffices /rowP/(_ i): \row_i k i = 0 by rewrite !mxE.
  by apply/(row_free_inj t_free)/r2v_inj; rewrite mul0mx -lin_b2mx kt0 linear0.
rewrite -kermx_eq0; apply/rowV0P=> rk /sub_kermxP kt0.
by apply/rowP=> i; rewrite mxE {}t_free // mul_b2mx kt0 linear0.
Qed.

Lemma coord_free n (X : n.-tuple vT) (i j : 'I_n) :  
  free X -> coord X j (X`_i) = (i == j)%:R.
Proof.
unlock coord; rewrite free_b2mx => /row_freeP[Ct CtK]; rewrite -row_b2mx.
by rewrite -row_mul -[pinvmx _]mulmx1 -CtK 2!mulmxA mulmxKpV // CtK !mxE.
Qed.

Lemma coord_sum_free n (X : n.-tuple vT) k j : 
  free X -> coord X j (\sum_(i < n) k i *: X`_i) = k j.
Proof.
move=> Xfree; rewrite linear_sum (bigD1 j) ?linearZ //= coord_free // eqxx.
rewrite mulr1 big1 ?addr0 // => i /negPf j'i.
by rewrite linearZ /= coord_free // j'i mulr0.
Qed.

Lemma cat_free X Y :
  free (X ++ Y) = [&& free X, free Y & directv (span X + span Y)].
Proof.
rewrite !free_directv mem_cat directvE /= !big_cat -directvE directv_addE /=.
rewrite negb_or -!andbA; do !bool_congr; rewrite -!span_def.
by rewrite (sameP eqP directv_addP).
Qed.

Lemma catl_free Y X : free (X ++ Y) -> free X.
Proof. by rewrite cat_free => /and3P[]. Qed.

Lemma catr_free X Y : free (X ++ Y) -> free Y.
Proof. by rewrite cat_free => /and3P[]. Qed.

Lemma filter_free p X : free X -> free (filter p X).
Proof.
rewrite -(perm_free (etrans (perm_filterC p X _) (perm_eq_refl X))).
exact: catl_free.
Qed.

Lemma free_cons v X : free (v :: X) = (v \notin span X) && free X.
Proof.
rewrite (cat_free [:: v]) seq1_free directvEgeq /= span_seq1 dim_injv.
case: eqP => [-> | _] /=; first by rewrite mem0v.
rewrite andbC ltnNge (geq_leqif (dimv_leqif_sup _)) ?addvSr //.
by rewrite subv_add subv_refl andbT -memvE.
Qed.

Lemma freeE n (X : n.-tuple vT) :
  free X = (forallb i : 'I_n, X`_i \notin span (drop i.+1 X)).
Proof.
case: X => X /= /eqP <-{n}; rewrite -(big_andE xpredT) /=.
elim: X => [|v X IH_X] /=; first by rewrite nil_free big_ord0.
by rewrite free_cons IH_X big_ord_recl drop0.
Qed.

Lemma freeNE n (X : n.-tuple vT) :
  ~~ free X = (existsb i : 'I_n, X`_i \in span (drop i.+1 X)).
Proof. by rewrite freeE -negb_exists negbK. Qed.

Lemma free_uniq X : free X -> uniq X.
Proof.
elim: X => //= v b IH_X; rewrite free_cons => /andP[X'v /IH_X->].
by rewrite (contra _ X'v) // => /memv_span.
Qed.

Lemma free_span X v (sumX := fun k => \sum_(x <- X) k x *: x) :
    free X -> v \in span X ->
  {k | v = sumX k & forall k1, v = sumX k1 -> {in X, k1 =1 k}}.
Proof.
rewrite -{2}[X]in_tupleE => freeX /coord_span def_v.
pose k x := oapp (fun i => coord (in_tuple X) i v) 0 (insub (index x X)).
exists k => [|k1 {def_v}def_v _ /(nthP 0)[i ltiX <-]].
  rewrite /sumX (big_nth 0) big_mkord def_v; apply: eq_bigr => i _.
  by rewrite /k index_uniq ?free_uniq // valK.
rewrite /k /= index_uniq ?free_uniq // insubT //= def_v.
by rewrite /sumX (big_nth 0) big_mkord coord_sum_free.
Qed.

Lemma linear_of_free (rT : lmodType K) X (fX : seq rT) :
  {f : {linear vT -> rT} | free X -> size fX = size X -> map f X = fX}.
Proof.
pose f u := \sum_i coord (in_tuple X) i u *: fX`_i.
have lin_f: linear f.
  move=> k u v; rewrite scaler_sumr -big_split; apply: eq_bigr => i _.
  by rewrite /= scalerA -scalerDl linearP.
exists (Linear lin_f) => freeX eq_szX.
apply/esym/(@eq_from_nth _ 0); rewrite ?size_map eq_szX // => i ltiX.
rewrite (nth_map 0) //= /f (bigD1 (Ordinal ltiX)) //=.
rewrite big1 => [|j /negbTE neqji]; rewrite (coord_free (Ordinal _)) //.
  by rewrite eqxx scale1r addr0.
by rewrite eq_sym neqji scale0r.
Qed.

(* Subspace bases *)

Lemma span_basis U b : basis_of U b -> span b = U.
Proof. by case/andP=> /eqP. Qed.

Lemma basis_free U b : basis_of U b -> free b.
Proof. by case/andP. Qed.

Lemma coord_basis U n (X : n.-tuple vT) v :
  basis_of U X -> v \in U -> v = \sum_i coord X i v *: X`_i.
Proof. by move/span_basis <-; apply: coord_span. Qed.

Lemma nil_basis : basis_of 0 (Nil vT).
Proof. by rewrite /basis_of span_nil eqxx nil_free. Qed.

Lemma seq1_basis v : v != 0 -> basis_of v%:VS [:: v].
Proof. by move=> nz_v; rewrite /basis_of span_seq1 // eqxx seq1_free. Qed.

Lemma basis_not0 x U X : basis_of U X -> x \in X -> x != 0.
Proof. by move/basis_free/free_not0; apply. Qed.

Lemma basis_mem x U X : basis_of U X -> x \in X -> x \in U.
Proof. by move/span_basis=> <- /memv_span. Qed.

Lemma cat_basis U V X Y : 
  directv (U + V) -> basis_of U X -> basis_of V Y -> basis_of (U + V) (X ++ Y).
Proof.
move=> dxUV /andP[/eqP defU freeX] /andP[/eqP defV freeY].
by rewrite /basis_of span_cat cat_free defU defV // eqxx freeX freeY.
Qed.

Lemma size_basis U n (X : n.-tuple vT) : basis_of U X -> \dim U = n.
Proof. by case/andP=> /eqP <- /eqnP->; apply: size_tuple. Qed.

Lemma basisEdim X U : basis_of U X = (U <= span X)%VS && (size X <= \dim U).
Proof.
apply/andP/idP=> [[defU /eqnP <-]| ]; first by rewrite -eqEdim eq_sym.
case/andP=> sUX leXU; have leXX := dim_span X.
rewrite /free eq_sym eqEdim sUX eqn_leq !(leq_trans leXX) //.
by rewrite (leq_trans leXU) ?dimvS.
Qed.

Lemma perm_basis X Y U : perm_eq X Y -> basis_of U X = basis_of U Y.
Proof.
move=> eqXY; congr ((_ == _) && _); last exact: perm_free.
by apply/eq_span; apply: perm_eq_mem.
Qed.

Lemma vbasisP U : basis_of U (vbasis U).
Proof.
rewrite /basis_of free_b2mx span_b2mx (sameP eqP (vs2mxP _ _)) !genmxE.
have ->: b2mx (vbasis U) = row_base (vs2mx U).
  by unlock vbasis; apply/row_matrixP=> i; rewrite rowK tnth_mktuple r2vK.
by rewrite row_base_free !eq_row_base submx_refl.
Qed.

Lemma vbasis_mem v U : v \in (vbasis U) -> v \in U.
Proof. exact: (basis_mem (vbasisP _)). Qed.

Lemma coord_vbasis v U :
  v \in U -> v = \sum_(i < \dim U) coord (vbasis U) i v *: (vbasis U)`_i.
Proof. exact: coord_basis (vbasisP U). Qed.

Section BigSumBasis.

Variables (I : finType) (P : pred I) (Xs : I -> seq vT).

Lemma span_bigcat :
  span (\big[cat/[::]]_(i | P i) Xs i) = (\sum_(i | P i) span (Xs i))%VS.
Proof. by rewrite (big_morph _ span_cat span_nil). Qed.

Lemma bigcat_free :
    (directv (\sum_(i | P i) span (Xs i))) -> 
  (forall i, P i -> free (Xs i)) -> free (\big[cat/[::]]_(i | P i) Xs i).
Proof.
rewrite /free directvE /= span_bigcat => /directvP-> /= freeXs. 
rewrite (big_morph _ (@size_cat _) (erefl _)) /=.
by apply/eqP/eq_bigr=> i /freeXs/eqP.
Qed.

Lemma bigcat_basis Us (U := (\sum_(i | P i) Us i)%VS) :
    directv U -> (forall i, P i -> basis_of (Us i) (Xs i)) -> 
  basis_of U (\big[cat/[::]]_(i | P i) Xs i).
Proof.
move=> dxU XsUs; rewrite /basis_of span_bigcat.
have defUs i: P i -> span (Xs i) = Us i by case/XsUs/andP=> /eqP.
rewrite (eq_bigr _ defUs) eqxx bigcat_free // => [|_ /XsUs/andP[]//].
apply/directvP; rewrite /= (eq_bigr _ defUs) (directvP dxU) /=.
by apply/eq_bigr=> i /defUs->.
Qed.

End BigSumBasis.

End VectorTheory.

Hint Resolve subv_refl.
Implicit Arguments subvP [K vT U V].
Implicit Arguments addv_idPl [K vT U V].
Implicit Arguments addv_idPr [K vT U V].
Implicit Arguments memv_addP [K vT U V w].
Implicit Arguments sumv_sup [K vT I P U Vs].
Implicit Arguments memv_sumP [K vT I P Us v].
Implicit Arguments subv_sumP [K vT I P Us V].
Implicit Arguments capv_idPl [K vT U V].
Implicit Arguments capv_idPr [K vT U V].
Implicit Arguments memv_capP [K vT U V w].
Implicit Arguments bigcapv_inf [K vT I P Us V].
Implicit Arguments subv_bigcapP [K vT I P U Vs].
Implicit Arguments directvP [K vT S].
Implicit Arguments directv_addP [K vT U V].
Implicit Arguments directv_add_unique [K vT U V].
Implicit Arguments directv_sumP [K vT I P Us].
Implicit Arguments directv_sumE [K vT I P Ss].
Implicit Arguments directv_sum_independent [K vT I P Us].
Implicit Arguments directv_sum_unique [K vT I P Us].
Implicit Arguments span_subvP [K vT X U].
Implicit Arguments freeP [K vT n X].

Prenex Implicits coord.
Notation directv S := (directv_def (Phantom _ S%VS)).

(* Linear functions over a vectType *)
Section LfunDefs.

Variable R : ringType.
Implicit Types aT vT rT : vectType R.

Definition fun_of_lfun aT rT :=
   locked (fun f : 'Hom(aT, rT) => r2v \o mulmxr (f2mx f) \o v2r).
Definition linfun aT rT :=
  locked (fun f : aT -> rT => Vector.Hom (lin1_mx (v2r \o f \o r2v))).

Definition id_lfun vT := @linfun vT vT idfun.
Definition comp_lfun aT vT rT (f : 'Hom(vT, rT)) (g : 'Hom(aT, vT)) :=
  linfun (fun_of_lfun f \o fun_of_lfun g).

End LfunDefs.

Coercion fun_of_lfun : Vector.hom >-> Funclass.
Notation "\1" := (@id_lfun _ _) : lfun_scope.
Notation "f \o g" := (comp_lfun f g) : lfun_scope.

Section LfunVspaceDefs.

Variable K : fieldType.
Implicit Types aT rT : vectType K.

Definition inv_lfun aT rT (f : 'Hom(aT, rT)) := Vector.Hom (pinvmx (f2mx f)).
Definition lker aT rT (f : 'Hom(aT, rT)) := mx2vs (kermx (f2mx f)).
Definition lfun_img aT rT :=
  locked (fun f (U : {vspace aT}) => mx2vs (vs2mx U *m f2mx f) : {vspace rT}).
Definition lfun_pre aT rT (f : 'Hom(aT, rT)) W :=
  (lfun_img (inv_lfun f) (W :&: lfun_img f fullv) + lker f)%VS.

End LfunVspaceDefs.

Prenex Implicits linfun lfun_img lker lfun_pre.
Notation "f ^-1" := (inv_lfun f) : lfun_scope.
Notation "f @: U" := (lfun_img f%VF%R U) (at level 24) : vspace_scope.
Notation "f @^-1: W" := (lfun_pre f%VF%R W) (at level 24) : vspace_scope.
Notation limg f := (lfun_img f fullv).

Section LfunZmodType.

Variables (R : ringType) (aT rT : vectType R).
Implicit Types f g h : 'Hom(aT, rT).

Canonical lfun_eqMixin := Eval hnf in [eqMixin of 'Hom(aT, rT) by <:].
Canonical lfun_eqType := EqType 'Hom(aT, rT) lfun_eqMixin.
Definition lfun_choiceMixin := [choiceMixin of 'Hom(aT, rT) by <:].
Canonical lfun_choiceType := ChoiceType 'Hom(aT, rT) lfun_choiceMixin.

Fact lfun_is_linear f : linear f.
Proof. by unlock fun_of_lfun; apply: linearP. Qed.
Canonical lfun_additive f := Additive (lfun_is_linear f).
Canonical lfun_linear f := AddLinear (lfun_is_linear f).

Lemma lfunE (ff : {linear aT -> rT}) : linfun ff =1 ff.
Proof. by unlock linfun fun_of_lfun => v; rewrite /= mul_rV_lin1 /= !v2rK. Qed.

Lemma fun_of_lfunK : cancel (@fun_of_lfun R aT rT) linfun.
Proof.
move=> f; apply/val_inj/row_matrixP=> i.
by unlock fun_of_lfun linfun; rewrite rowK /= !r2vK -rowE.
Qed.

Lemma lfunP f g : f =1 g <-> f = g.
Proof.
split=> [eq_fg | -> //]; rewrite -[f]fun_of_lfunK -[g]fun_of_lfunK.
by unlock linfun; apply/val_inj/row_matrixP=> i; rewrite !rowK /= eq_fg.
Qed.

Definition zero_lfun : 'Hom(aT, rT) := linfun \0.
Definition add_lfun f g := linfun (f \+ g).
Definition opp_lfun f := linfun (-%R \o f).

Fact lfun_addA : associative add_lfun.
Proof. by move=> f g h; apply/lfunP=> v; rewrite !lfunE /= !lfunE addrA. Qed.

Fact lfun_addC : commutative add_lfun.
Proof. by move=> f g; apply/lfunP=> v; rewrite !lfunE /= addrC. Qed.

Fact lfun_add0 : left_id zero_lfun add_lfun.
Proof. by move=> f; apply/lfunP=> v; rewrite lfunE /= lfunE add0r. Qed.

Lemma lfun_addN : left_inverse zero_lfun opp_lfun add_lfun.
Proof. by move=> f; apply/lfunP=> v; rewrite !lfunE /= lfunE addNr. Qed.

Definition lfun_zmodMixin := ZmodMixin lfun_addA lfun_addC lfun_add0 lfun_addN.
Canonical lfun_zmodType := Eval hnf in ZmodType 'Hom(aT, rT) lfun_zmodMixin.

Lemma zero_lfunE x : (0 : 'Hom(aT, rT)) x = 0. Proof. exact: lfunE. Qed.
Lemma add_lfunE f g x : (f + g) x = f x + g x. Proof. exact: lfunE. Qed.
Lemma opp_lfunE f x : (- f) x = - f x. Proof. exact: lfunE. Qed.
Lemma sum_lfunE I (r : seq I) (P : pred I) (fs : I -> 'Hom(aT, rT)) x :
  (\sum_(i <- r | P i) fs i) x = \sum_(i <- r | P i) fs i x.
Proof. by elim/big_rec2: _ => [|i _ f _ <-]; rewrite lfunE. Qed.

End LfunZmodType.

Section LfunVectType.

Variables (R : comRingType) (aT rT : vectType R).
Implicit Types f : 'Hom(aT, rT).

Definition scale_lfun k f := linfun (k \*: f).
Local Infix "*:l" := scale_lfun (at level 40).

Fact lfun_scaleA k1 k2 f : k1 *:l (k2 *:l f) = (k1 * k2) *:l f.
Proof. by apply/lfunP=> v; rewrite !lfunE /= lfunE scalerA. Qed.

Fact lfun_scale1 f : 1 *:l f = f.
Proof. by apply/lfunP=> v; rewrite lfunE /= scale1r. Qed.

Fact lfun_scaleDr k f1 f2 : k *:l (f1 + f2) = k *:l f1 + k *:l f2.
Proof. by apply/lfunP=> v; rewrite !lfunE /= !lfunE scalerDr. Qed.

Fact lfun_scaleDl f k1 k2 : (k1 + k2) *:l f = k1 *:l f + k2 *:l f.
Proof. by apply/lfunP=> v; rewrite !lfunE /= !lfunE scalerDl. Qed.

Definition lfun_lmodMixin := 
  LmodMixin lfun_scaleA lfun_scale1 lfun_scaleDr lfun_scaleDl.
Canonical lfun_lmodType := Eval hnf in LmodType R 'Hom(aT, rT) lfun_lmodMixin.

Lemma scale_lfunE k f x : (k *: f) x = k *: f x. Proof. exact: lfunE. Qed.

(* GG: exists (Vector.Hom \o vec_mx) fails in the proof below in 8.3,     *)
(* probably because of incomplete type unification. Will it work in 8.4?  *)
Fact lfun_vect_iso : Vector.axiom (Vector.dim aT * Vector.dim rT) 'Hom(aT, rT).
Proof.
exists (mxvec \o f2mx) => [a f g|].
  rewrite /= -linearP /= -[A in _ = mxvec A]/(f2mx (Vector.Hom _)).
  congr (mxvec (f2mx _)); apply/lfunP=> v; do 2!rewrite lfunE /=.
  by unlock fun_of_lfun; rewrite /= -linearP mulmxDr scalemxAr.
apply: Bijective (Vector.Hom \o vec_mx) _ _ => [[A]|A] /=; last exact: vec_mxK.
by rewrite mxvecK.
Qed.

Definition lfun_vectMixin := VectMixin lfun_vect_iso.
Canonical lfun_vectType := VectType R 'Hom(aT, rT) lfun_vectMixin.

End LfunVectType.

Section CompLfun.

Variables (R : ringType) (wT aT vT rT : vectType R).
Implicit Types (f : 'Hom(vT, rT)) (g : 'Hom(aT, vT)) (h : 'Hom(wT, aT)).

Lemma id_lfunE u: \1%VF u = u :> aT. Proof. exact: lfunE. Qed.
Lemma comp_lfunE f g u : (f \o g)%VF u = f (g u). Proof. exact: lfunE. Qed.

Lemma comp_lfunA f g h : (f \o (g \o h) = (f \o g) \o h)%VF.
Proof. by apply/lfunP=> u; do !rewrite lfunE /=. Qed.

Lemma comp_lfun1l f : (\1 \o f)%VF = f.
Proof. by apply/lfunP=> u; do !rewrite lfunE /=. Qed.

Lemma comp_lfun1r f : (f \o \1)%VF = f.
Proof. by apply/lfunP=> u; do !rewrite lfunE /=. Qed.

Lemma comp_lfun0l g : (0 \o g)%VF = 0 :> 'Hom(aT, rT).
Proof. by apply/lfunP=> u; do !rewrite lfunE /=. Qed.

Lemma comp_lfun0r f : (f \o 0)%VF = 0 :> 'Hom(aT, rT).
Proof. by apply/lfunP=> u; do !rewrite lfunE /=; rewrite linear0. Qed.

Lemma comp_lfunDl f1 f2 g : ((f1 + f2) \o g = (f1 \o g) + (f2 \o g))%VF.
Proof. by apply/lfunP=> u; do !rewrite lfunE /=. Qed.

Lemma comp_lfunDr f g1 g2 : (f \o (g1 + g2) = (f \o g1) + (f \o g2))%VF.
Proof. by apply/lfunP=> u; do !rewrite lfunE /=; rewrite linearD. Qed.

Lemma comp_lfunNl f g : ((- f) \o g = - (f \o g))%VF.
Proof. by apply/lfunP=> u; do !rewrite lfunE /=. Qed.

Lemma comp_lfunNr f g : (f \o (- g) = - (f \o g))%VF.
Proof. by apply/lfunP=> u; do !rewrite lfunE /=; rewrite linearN. Qed.

End CompLfun.

Definition lfun_simp :=
  (comp_lfunE, scale_lfunE, opp_lfunE, add_lfunE, sum_lfunE, lfunE).

Section ScaleCompLfun.

Variables (R : comRingType) (aT vT rT : vectType R).
Implicit Types (f : 'Hom(vT, rT)) (g : 'Hom(aT, vT)).

Lemma comp_lfunZl k f g : (k *: (f \o g) = (k *: f) \o g)%VF.
Proof. by apply/lfunP=> u; do !rewrite lfunE /=. Qed.

Lemma comp_lfunZr k f g : (k *: (f \o g) = f \o (k *: g))%VF.
Proof. by apply/lfunP=> u; do !rewrite lfunE /=; rewrite linearZ. Qed.

End ScaleCompLfun.

Section LinearImage.

Variables (K : fieldType) (aT rT : vectType K).
Implicit Types (f g : 'Hom(aT, rT)) (U V : {vspace aT}) (W : {vspace rT}).

Lemma limgS f U V : (U <= V)%VS -> (f @: U <= f @: V)%VS.
Proof. by unlock lfun_img subsetv; rewrite !genmxE; apply: submxMr. Qed.

Lemma limg_inj f v : (f @: v%:VS)%VS = (f v)%:VS.
Proof.
unlock lfun_img fun_of_lfun; apply/eqP; rewrite eqEsubv /subsetv /=.
by rewrite r2vK !genmxE !(eqmxMr _ (genmxE _)) submx_refl.
Qed.

Lemma limg0 f : (f @: 0 = 0)%VS. Proof. by rewrite limg_inj linear0. Qed.

Lemma memv_img f v U : v \in U -> f v \in (f @: U)%VS.
Proof. by move=> Uv; rewrite memvE -limg_inj limgS. Qed.

Lemma memv_imgP f w U :
  reflect (exists2 u, u \in U & w = f u) (w \in f @: U)%VS.
Proof.
apply: (iffP idP) => [|[u Uu ->]]; last exact: memv_img.
unlock lfun_img fun_of_lfun; rewrite memvE /subsetv !genmxE => /submxP[ku Drw].
exists (r2v (ku *m vs2mx U)); last by rewrite /= r2vK -mulmxA -Drw v2rK.
by rewrite memvE /subsetv !genmxE r2vK submxMl.
Qed.

Lemma lim0g U : (0 @: U = 0 :> {vspace rT})%VS.
Proof.
apply/eqP; rewrite -subv0; apply/subvP=> _ /memv_imgP[u _ ->].
by rewrite lfunE rpred0.
Qed.

Lemma limg_add f : {morph lfun_img f : U V / U + V}%VS.
Proof.
unlock lfun_img => U V; apply/eqP; rewrite eqEsubv /subsetv /= -genmx_adds.
by rewrite !genmxE !(eqmxMr _ (genmxE _)) !addsmxMr submx_refl.
Qed.

Lemma limg_sum f I r (P : pred I) Us :
  (f @: (\sum_(i <- r | P i) Us i) = \sum_(i <- r | P i) f @: Us i)%VS.
Proof. exact: (big_morph _ (limg_add f) (limg0 f)). Qed.

Lemma limg_cap f U V : (f @: (U :&: V) <= f @: U :&: f @: V)%VS.
Proof. by rewrite subv_cap !limgS ?capvSl ?capvSr. Qed.

Lemma limg_bigcap f I r (P : pred I) Us :
  (f @: (\bigcap_(i <- r | P i) Us i) <= \bigcap_(i <- r | P i) f @: Us i)%VS.
Proof.
elim/big_rec2: _ => [|i V U _ sUV]; first exact: subvf.
by rewrite (subv_trans (limg_cap f _ U)) ?capvS.
Qed.

Lemma limg_span f X : (f @: span X)%VS = span (map f X).
Proof.
by rewrite !span_def big_map limg_sum; apply: eq_bigr => x _; rewrite limg_inj.
Qed.

Lemma lfunPn f g : reflect (exists u, f u != g u) (f != g).
Proof.
apply: (iffP idP) => [f'g|[x]]; last by apply: contraNneq => /lfunP->.
suffices /subvPn[_ /memv_imgP[u _ ->]]: ~~ (limg (f - g) <= 0)%VS.
  by rewrite lfunE /= lfunE /= memv0 subr_eq0; exists u.
apply: contra f'g => /subvP fg0; apply/eqP/lfunP=> u; apply/eqP.
by rewrite -subr_eq0 -opp_lfunE -add_lfunE -memv0 fg0 ?memv_img ?memvf.
Qed.

Lemma inv_lfun_def f : (f \o f^-1 \o f)%VF = f.
Proof.
apply/lfunP=> u; do !rewrite lfunE /=; unlock fun_of_lfun.
by rewrite /= !r2vK mulmxKpV ?submxMl.
Qed.

Lemma limg_lfunVK f : {in limg f, cancel f^-1%VF f}.
Proof. by move=> _ /memv_imgP[u _ ->]; rewrite -!comp_lfunE inv_lfun_def. Qed.

Lemma lkerE f U : (U <= lker f)%VS = (f @: U == 0)%VS. 
Proof.
unlock lfun_img; rewrite -dimv_eq0 /dimv /subsetv !genmxE mxrank_eq0.
by rewrite (sameP sub_kermxP eqP).
Qed.

Lemma memv_ker f v : (v \in lker f) = (f v == 0).
Proof. by rewrite -memv0 !memvE subv0 lkerE limg_inj. Qed.

Lemma limg_ker_compl f U : (f @: (U :\: lker f) = f @: U)%VS.
Proof. 
rewrite -{2}(addv_diff_cap U (lker f)) limg_add; apply/esym/addv_idPl.
by rewrite (subv_trans _ (sub0v _)) // subv0 -lkerE capvSr.
Qed.

Lemma limg_ker_dim f U : (\dim (U :&: lker f) + \dim (f @: U) = \dim U)%N.
Proof.
unlock lfun_img; rewrite /dimv /= genmx_cap genmx_id -genmx_cap !genmxE.
by rewrite addnC mxrank_mul_ker.
Qed.

Lemma limg_dim_eq f U : (U :&: lker f = 0)%VS -> \dim (f @: U) = \dim U.
Proof. by rewrite -(limg_ker_dim f U) => ->; rewrite dimv0. Qed.

Lemma limg_basis_of f U X :
  (U :&: lker f = 0)%VS -> basis_of U X -> basis_of (f @: U) (map f X).
Proof.
move=> injUf /andP[/eqP defU /eqnP freeX].
by rewrite /basis_of /free size_map -limg_span -freeX defU limg_dim_eq ?eqxx.
Qed.

Lemma lker0P f : reflect (injective f) (lker f == 0%VS).
Proof.
rewrite -subv0; apply: (iffP subvP) => [injf u v eq_fuv | injf u].
  apply/eqP; rewrite -subr_eq0 -memv0 injf //.
  by rewrite memv_ker linearB /= eq_fuv subrr.
by rewrite memv_ker memv0 -(inj_eq injf) linear0.
Qed.

Lemma limg_ker0 f U V : lker f == 0%VS -> (f @: U <= f @: V)%VS = (U <= V)%VS.
Proof.
move/lker0P=> injf; apply/idP/idP=> [/subvP sfUV | ]; last exact: limgS.
by apply/subvP=> u Uu; have /memv_imgP[v Vv /injf->] := sfUV _ (memv_img f Uu).
Qed.

Lemma eq_limg_ker0 f U V : lker f == 0%VS -> (f @: U == f @: V)%VS = (U == V).
Proof. by move=> injf; rewrite !eqEsubv !limg_ker0. Qed.

Lemma lker0_lfunK f : lker f == 0%VS -> cancel f f^-1%VF.
Proof.
by move/lker0P=> injf u; apply: injf; rewrite limg_lfunVK ?memv_img ?memvf.
Qed.

Lemma lker0_compVf f : lker f == 0%VS -> (f^-1 \o f = \1)%VF.
Proof. by move/lker0_lfunK=> fK; apply/lfunP=> u; rewrite !lfunE /= fK. Qed.

End LinearImage.

Implicit Arguments memv_imgP [K aT rT f U w].
Implicit Arguments lfunPn [K aT rT f g].
Implicit Arguments lker0P [K aT rT f].

Section LinAut.

Variables (K : fieldType) (vT : vectType K) (f : 'End(vT)).
Hypothesis kerf0 : lker f == 0%:VS.

Lemma lker0_limgf : limg f = fullv.
Proof.
by apply/eqP; rewrite eqEdim subvf limg_dim_eq //= (eqP kerf0) capv0.
Qed.

Lemma lker0_lfunVK : cancel f^-1%VF f.
Proof. by move=> u; rewrite limg_lfunVK // lker0_limgf memvf. Qed.

Lemma lker0_compfV : (f \o f^-1 = \1)%VF.
Proof. by apply/lfunP=> u; rewrite !lfunE /= lker0_lfunVK. Qed.

Lemma lker0_compVKf aT g : (f \o (f^-1 \o g))%VF = g :> 'Hom(aT, vT).
Proof. by rewrite comp_lfunA lker0_compfV comp_lfun1l. Qed.

Lemma lker0_compKf aT g : (f^-1 \o (f \o g))%VF = g :> 'Hom(aT, vT).
Proof. by rewrite comp_lfunA lker0_compVf ?comp_lfun1l. Qed.

Lemma lker0_compfK rT h : ((h \o f) \o f^-1)%VF = h :> 'Hom(vT, rT).
Proof. by rewrite -comp_lfunA lker0_compfV comp_lfun1r. Qed.

Lemma lker0_compfVK rT h : ((h \o f^-1) \o f)%VF = h :> 'Hom(vT, rT).
Proof. by rewrite -comp_lfunA lker0_compVf ?comp_lfun1r. Qed.

End LinAut.

Section LinearImageComp.

Variables (K : fieldType) (aT vT rT : vectType K).
Implicit Types (f : 'Hom(aT, vT)) (g : 'Hom(vT, rT)) (U : {vspace aT}).

Lemma lim1g U : (\1 @: U)%VS = U.
Proof.
have /andP[/eqP <- _] := vbasisP U; rewrite limg_span map_id_in // => u _.
by rewrite lfunE.
Qed.

Lemma limg_comp f g U : ((g \o f) @: U = g @: (f @: U))%VS.
Proof.
have /andP[/eqP <- _] := vbasisP U; rewrite !limg_span; congr (span _).
by rewrite -map_comp; apply/eq_map => u; rewrite lfunE.
Qed.

End LinearImageComp.

Section LinearPreimage.

Variables (K : fieldType) (aT rT : vectType K).
Implicit Types (f : 'Hom(aT, rT)) (U : {vspace aT}) (V W : {vspace rT}).

Lemma lpre_img_full f W : (f @^-1: (W :&: limg f))%VS = (f @^-1: W)%VS.
Proof. by rewrite /lfun_pre -capvA capvv. Qed.

Lemma lpre_img0 f : (f @^-1: 0)%VS = lker f.
Proof. by rewrite /lfun_pre cap0v limg0 add0v. Qed.

Lemma lpre_imgS f V W : (V <= W)%VS-> (f @^-1: V <= f @^-1: W)%VS.
Proof. by move=> sVW; rewrite addvS // limgS // capvS. Qed.

Lemma lpre_imgK f W : (W <= limg f)%VS -> (f @: (f @^-1: W))%VS = W.
Proof.
move=> sWf; rewrite limg_add (capv_idPl sWf) // -limg_comp.
have /eqP->: (f @: lker f == 0)%VS by rewrite -lkerE.
have /andP[/eqP defW _] := vbasisP W; rewrite addv0 -defW limg_span.
rewrite map_id_in // => x Xx; rewrite lfunE /= limg_lfunVK //.
by apply: span_subvP Xx; rewrite defW.
Qed.

Lemma memv_pre_img f u W : (f u \in W) = (u \in f @^-1: W)%VS.
Proof.
apply/idP/idP=> [Wfu | /(memv_img f)]; last first.
  by rewrite -lpre_img_full lpre_imgK ?capvSr // => /memv_capP[].
rewrite -[u](addNKr (f^-1%VF (f u))) memv_add ?memv_img //.
  by rewrite memv_cap Wfu memv_img ?memvf.
by rewrite memv_ker addrC linearB /= subr_eq0 limg_lfunVK ?memv_img ?memvf.
Qed.

End LinearPreimage.

Section LfunAlgebra.
(* This section is a bit of a place holder: the instances we build here can't *)
(* be canonical because we are missing an interface for proper vectTypes,     *)
(* would sit between Vector and Falgebra. For now, we just supply structure   *)
(* definitions here and supply actual instances for F-algebras in a submodule *)
(* of the algebra library (there is currently no actual use of the End(vT)    *)
(* algebra structure). Also note that the unit ring structure is missing.     *)

Variables (R : comRingType) (vT : vectType R).
Hypothesis vT_proper : Vector.dim vT > 0.

Fact lfun1_neq0 : \1%VF != 0 :> 'End(vT).
Proof.
apply/eqP=> /lfunP/(_ (r2v (const_mx 1))); rewrite !lfunE /= => /(canRL r2vK).
by move=> /rowP/(_ (Ordinal vT_proper))/eqP; rewrite linear0 !mxE oner_eq0.
Qed.

Prenex Implicits comp_lfunA comp_lfun1l comp_lfun1r comp_lfunDl comp_lfunDr.

Definition lfun_comp_ringMixin :=
  RingMixin comp_lfunA comp_lfun1l comp_lfun1r comp_lfunDl comp_lfunDr
            lfun1_neq0.
Definition lfun_comp_ringType := RingType 'End(vT) lfun_comp_ringMixin.

(* In the standard endomorphism ring product is categorical composition.     *)
Definition lfun_ringMixin : GRing.Ring.mixin_of (lfun_zmodType vT vT) :=
  GRing.converse_ringMixin lfun_comp_ringType.
Definition lfun_ringType := Eval hnf in RingType 'End(vT) lfun_ringMixin.
Definition lfun_lalgType := Eval hnf in [lalgType R of 'End(vT)
  for LalgType R lfun_ringType (fun k x y => comp_lfunZr k y x)].
Definition lfun_algType := Eval hnf in [algType R of 'End(vT)
  for AlgType R _ (fun k (x y : lfun_lalgType) => comp_lfunZl k y x)].

End LfunAlgebra.

Section Projection.

Variables (K : fieldType) (vT : vectType K).
Implicit Types U V : {vspace vT}.

Definition daddv_pi U V := Vector.Hom (proj_mx (vs2mx U) (vs2mx V)).
Definition projv U := daddv_pi U U^C.
Definition addv_pi1 U V := daddv_pi (U :\: V) V.
Definition addv_pi2 U V := daddv_pi V (U :\: V).

Lemma memv_pi U V w : (daddv_pi U V) w \in U.
Proof.
by unlock fun_of_lfun; rewrite memvE /subsetv genmxE /= r2vK proj_mx_sub.
Qed.

Lemma memv_proj U w : projv U w \in U. Proof. exact: memv_pi. Qed.

Lemma memv_pi1 U V w : (addv_pi1 U V) w \in U.
Proof. by rewrite (subvP (diffvSl U V)) ?memv_pi. Qed.

Lemma memv_pi2 U V w : (addv_pi2 U V) w \in V. Proof. exact: memv_pi. Qed.

Lemma daddv_pi_id U V u : (U :&: V = 0)%VS -> u \in U -> daddv_pi U V u = u.
Proof.
move/eqP; rewrite -dimv_eq0 memvE /subsetv /dimv !genmxE mxrank_eq0 => /eqP.
by unlock fun_of_lfun=> dxUV Uu; rewrite /= proj_mx_id ?v2rK.
Qed.

Lemma daddv_pi_proj U V w (pi := daddv_pi U V) :
  (U :&: V = 0)%VS -> pi (pi w) = pi w.
Proof. by move/daddv_pi_id=> -> //; apply: memv_pi. Qed.

Lemma daddv_pi_add U V w :
  (U :&: V = 0)%VS -> (w \in U + V)%VS -> daddv_pi U V w + daddv_pi V U w = w.
Proof.
move/eqP; rewrite -dimv_eq0 memvE /subsetv /dimv !genmxE mxrank_eq0 => /eqP.
by unlock fun_of_lfun => dxUW UVw; rewrite /= -linearD /= add_proj_mx ?v2rK.
Qed.

Lemma projv_id U u : u \in U -> projv U u = u.
Proof. exact: daddv_pi_id (capv_compl _). Qed.

Lemma projv_proj U w : projv U (projv U w) = projv U w.
Proof. exact: daddv_pi_proj (capv_compl _). Qed.

Lemma memv_projC U w : w - projv U w \in (U^C)%VS.
Proof.
rewrite -{1}[w](daddv_pi_add (capv_compl U)) ?addv_complf ?memvf //.
by rewrite addrC addKr memv_pi.
Qed.

Lemma limg_proj U : limg (projv U) = U.
Proof.
apply/vspaceP=> u; apply/memv_imgP/idP=> [[u1 _ ->] | ]; first exact: memv_proj.
by exists (projv U u); rewrite ?projv_id ?memv_img ?memvf.
Qed.

Lemma lker_proj U : lker (projv U) = (U^C)%VS.
Proof.
apply/eqP; rewrite eqEdim andbC; apply/andP; split.
  by rewrite dimv_compl -(limg_ker_dim (projv U) fullv) limg_proj addnK capfv.
by apply/subvP=> v; rewrite memv_ker -{2}[v]subr0 => /eqP <-; apply: memv_projC.
Qed.

Lemma addv_pi1_proj U V w (pi1 := addv_pi1 U V) : pi1 (pi1 w) = pi1 w.
Proof. by rewrite daddv_pi_proj // capv_diff. Qed.

Lemma addv_pi2_id U V v : v \in V -> addv_pi2 U V v = v.
Proof. by apply: daddv_pi_id; rewrite capvC capv_diff. Qed.

Lemma addv_pi2_proj U V w (pi2 := addv_pi2 U V) : pi2 (pi2 w) = pi2 w.
Proof. by rewrite addv_pi2_id ?memv_pi2. Qed.

Lemma addv_pi1_pi2 U V w :
  w \in (U + V)%VS -> addv_pi1 U V w + addv_pi2 U V w = w. 
Proof. by rewrite -addv_diff; apply: daddv_pi_add; apply: capv_diff. Qed.

Section Sumv_Pi.

Variables (I : eqType) (r0 : seq I) (P : pred I) (Vs : I -> {vspace vT}).

Let sumv_pi_rec i :=
  fix loop r := if r is j :: r1 then
    let V1 := (\sum_(k <- r1) Vs k)%VS in
    if j == i then addv_pi1 (Vs j) V1 else (loop r1 \o addv_pi2 (Vs j) V1)%VF
  else 0.

Notation sumV := (\sum_(i <- r0 | P i) Vs i)%VS.
Definition sumv_pi_for V of V = sumV := fun i => sumv_pi_rec i (filter P r0).

Variables (V : {vspace vT}) (defV : V = sumV).

Lemma memv_sum_pi i v : sumv_pi_for defV i v \in Vs i.
Proof.
rewrite /sumv_pi_for.
elim: (filter P r0) v => [|j r IHr] v /=; first by rewrite lfunE mem0v.
by case: eqP => [->|_]; rewrite ?lfunE ?memv_pi1 /=.
Qed.

Lemma sumv_pi_uniq_sum v :
    uniq (filter P r0) -> v \in V ->
  \sum_(i <- r0 | P i) sumv_pi_for defV i v = v.
Proof.
rewrite /sumv_pi_for defV -!(big_filter r0 P).
elim: (filter P r0) v => [|i r IHr] v /= => [_ | /andP[r'i /IHr{IHr}IHr]].
  by rewrite !big_nil memv0 => /eqP.
rewrite !big_cons eqxx => /addv_pi1_pi2; congr (_ + _ = v).
rewrite -[_ v]IHr ?memv_pi2 //; apply: eq_big_seq => j /=.
by case: eqP => [<- /idPn | _]; rewrite ?lfunE.
Qed.

End Sumv_Pi.

End Projection.

Prenex Implicits daddv_pi projv addv_pi1 addv_pi2.
Notation sumv_pi V := (sumv_pi_for (erefl V)).

Section SumvPi.

Variable (K : fieldType) (vT : vectType K).

Lemma sumv_pi_sum (I : finType) (P : pred I) Vs v (V : {vspace vT})
                  (defV : V = (\sum_(i | P i) Vs i)%VS) :
  v \in V -> \sum_(i | P i) sumv_pi_for defV i v = v :> vT.
Proof. by apply: sumv_pi_uniq_sum; apply: enum_uniq. Qed.

Lemma sumv_pi_nat_sum m n (P : pred nat) Vs v (V : {vspace vT})
                      (defV : V = (\sum_(m <= i < n | P i) Vs i)%VS) :
  v \in V -> \sum_(m <= i < n | P i) sumv_pi_for defV i v = v :> vT.
Proof. by apply: sumv_pi_uniq_sum; apply/filter_uniq/iota_uniq. Qed.

End SumvPi.

Section SubVector.

(* Turn a {vspace V} into a vectType                                          *)
Variable (K : fieldType) (vT : vectType K) (U : {vspace vT}).

Inductive subvs_of : predArgType := Subvs u & u \in U.

Definition vsval w := let: Subvs u _ := w in u.
Canonical subvs_subType := Eval hnf in [subType for vsval by subvs_of_rect].
Definition subvs_eqMixin := Eval hnf in [eqMixin of subvs_of by <:].
Canonical subvs_eqType := Eval hnf in EqType subvs_of subvs_eqMixin.
Definition subvs_choiceMixin := [choiceMixin of subvs_of by <:].
Canonical subvs_choiceType := ChoiceType subvs_of subvs_choiceMixin.
Definition subvs_zmodMixin := [zmodMixin of subvs_of by <:].
Canonical subvs_zmodType := ZmodType subvs_of subvs_zmodMixin.
Definition subvs_lmodMixin := [lmodMixin of subvs_of by <:].
Canonical subvs_lmodType := LmodType K subvs_of subvs_lmodMixin.

Lemma subvsP w : vsval w \in U. Proof. exact: valP. Qed.
Lemma subvs_inj : injective vsval. Proof. exact: val_inj. Qed.
Lemma congr_subvs u v : u = v -> vsval u = vsval v. Proof. exact: congr1. Qed.

Lemma vsval_is_linear : linear vsval. Proof. by []. Qed.
Canonical vsval_additive := Additive vsval_is_linear.
Canonical vsval_linear := AddLinear vsval_is_linear.

Definition vsproj u := locked (Subvs (memv_proj U u)).
Lemma vsprojK : {in U, cancel vsproj vsval}.
Proof. by unlock vsproj; apply: projv_id. Qed.
Lemma vsvalK : cancel vsval vsproj.
Proof. by move=> w; exact/val_inj/vsprojK/subvsP. Qed.

Lemma vsproj_is_linear : linear vsproj.
Proof. by unlock vsproj => k w1 w2; apply: val_inj; rewrite /= linearP. Qed.
Canonical vsproj_additive := Additive vsproj_is_linear.
Canonical vsproj_linear := AddLinear vsproj_is_linear.

Fact subvs_vect_iso : Vector.axiom (\dim U) subvs_of.
Proof.
exists (fun w => \row_i coord (vbasis U) i (vsval w)).
  by move=> k w1 w2; apply/rowP=> i; rewrite !mxE linearP.
exists (fun rw : 'rV_(\dim U) => vsproj (\sum_i rw 0 i *: (vbasis U)`_i)).
  move=> w /=; congr (vsproj _ = w): (vsvalK w).
  by rewrite {1}(coord_vbasis (subvsP w)); apply: eq_bigr => i _; rewrite mxE.
move=> rw; apply/rowP=> i; rewrite mxE vsprojK.
  by rewrite coord_sum_free ?(basis_free (vbasisP U)).
by apply: rpred_sum => j _; rewrite rpredZ ?vbasis_mem ?memt_nth.
Qed.

Definition subvs_vectMixin :=  VectMixin subvs_vect_iso.
Canonical subvs_vectType := VectType K subvs_of subvs_vectMixin.

End SubVector.
Prenex Implicits vsval vsproj vsvalK.
Implicit Arguments subvs_inj [[K] [vT] [U] x1 x2].
Implicit Arguments vsprojK [[K] [vT] [U] x].

Section MatrixVectType.

Variables (R : ringType) (m n : nat).

(* The apparently useless => /= in line 1 of the proof performs some evar     *)
(* expansions that the Ltac interpretation of exists is incapable of doing.   *)
Fact matrix_vect_iso : Vector.axiom (m * n) 'M[R]_(m, n).
Proof.
exists mxvec => /=; first exact: linearP.
by exists vec_mx; [apply: mxvecK | apply: vec_mxK].
Qed.
Definition matrix_vectMixin := VectMixin matrix_vect_iso.
Canonical matrix_vectType := VectType R 'M[R]_(m, n) matrix_vectMixin.

End MatrixVectType.

(* A ring is a one-dimension vector space *)
Section RegularVectType.

Variable R : ringType.

Fact regular_vect_iso : Vector.axiom 1 R^o.
Proof.
exists (fun a => a%:M) => [a b c|]; first by rewrite rmorphD scale_scalar_mx.
by exists (fun A : 'M_1 => A 0 0) => [a | A]; rewrite ?mxE // -mx11_scalar.
Qed.
Definition regular_vectMixin := VectMixin regular_vect_iso.
Canonical regular_vectType := VectType R R^o regular_vectMixin.

End RegularVectType.

(* Simple Product of two vectTypes. *)
(* This section is a somewhat of a placeholder -- see PairZmodType in ssralg. *)
Section ProdVector.

Variables (R : ringType) (vT1 vT2 : vectType R).

Let rv (u : vT1 * vT2) := row_mx (v2r u.1) (v2r u.2).
Let pv w := (r2v (lsubmx w) : vT1, r2v (rsubmx w) : vT2).
Let pvK : cancel pv rv. Proof. by move=> w; rewrite /rv !r2vK hsubmxK. Qed.
Let rvK : cancel rv pv.
Proof. by case=> u1 u2; rewrite /pv row_mxKl row_mxKr !v2rK. Qed.

Definition vpair_choiceType := ChoiceType (vT1 * vT2) (CanChoiceMixin rvK).
Canonical vpair_zmodType :=
  [zmodType of vT1 * vT2 for ZmodType vpair_choiceType (pair_zmodMixin _ _)].

Definition scale_pair a (w : vT1 * vT2) : vT1 * vT2 := (a *: w.1, a *: w.2).

Fact pair_scaleA a b u : scale_pair a (scale_pair b u) = scale_pair (a * b) u.
Proof. by congr (_, _); apply: scalerA. Qed.

Fact pair_scale1 u : scale_pair 1 u = u.
Proof. by case: u => u1 u2; congr (_, _); apply: scale1r. Qed.

Fact pair_scaleDr : right_distributive scale_pair +%R.
Proof. by move=> a u v; congr (_, _); apply: scalerDr. Qed.

Fact pair_scaleDl u : {morph scale_pair^~ u: a b / a + b}.
Proof. by move=> a b; congr (_, _); apply: scalerDl. Qed.

Definition vpair_lmodMixin :=
  LmodMixin pair_scaleA pair_scale1 pair_scaleDr pair_scaleDl.
Canonical vpair_lmodType := LmodType R (vT1 * vT2) vpair_lmodMixin.

Fact pair_vect_iso : Vector.axiom (Vector.dim vT1 + Vector.dim vT2) (vT1 * vT2).
Proof.
have pv_lin: linear pv by move=> a u v; congr (_ , _); rewrite /= !linearP.
by exists rv; [apply: (@can2_linear _ _ _ (Linear pv_lin)) | exists pv].
Qed.
Definition pair_vectMixin := VectMixin pair_vect_iso.
Canonical pair_vectType := VectType R (vT1 * vT2) pair_vectMixin.

End ProdVector.

(* Function from a finType into a ring form a vectype. *)
Section FunVectType.

Variable (I : finType) (R : ringType) (vT : vectType R).

(* Type unification with exist is again a problem in this proof. *)
Fact ffun_vect_iso : Vector.axiom (#|I| * Vector.dim vT) {ffun I -> vT}.
Proof.
hnf=> /=; exists (fun f => mxvec (\matrix_i v2r (f (enum_val i)))) => [k f g|].
  rewrite -linearP; congr (mxvec _); apply/matrixP=> i j.
  by rewrite !mxE /= !ffunE linearP !mxE.
exists (fun r => [ffun i => r2v (row (enum_rank i) (vec_mx r)) : vT]) => [g|r].
  by apply/ffunP=> i; rewrite ffunE mxvecK rowK v2rK enum_rankK.
by apply/(canLR vec_mxK)/matrixP=> i j; rewrite mxE ffunE r2vK enum_valK mxE.
Qed.

Definition ffun_vectMixin := VectMixin ffun_vect_iso.
Canonical ffun_vectType := VectType R {ffun I -> vT} ffun_vectMixin.

End FunVectType.

Canonical exp_vectType (K : fieldType) (vT : vectType K) n :=
  [vectType K of vT ^ n].

(* Solving a tuple of linear equations. *)
Section Solver.

Variable (K : fieldType) (vT : vectType K).
Variables (n : nat) (lhs : n.-tuple 'End(vT)) (rhs : n.-tuple vT).

Let lhsf u := finfun ((tnth lhs)^~ u).
Definition vsolve_eq U := finfun (tnth rhs) \in (linfun lhsf @: U)%VS.

Lemma vsolve_eqP (U : {vspace vT}) :
  reflect (exists2 u, u \in U & forall i, tnth lhs i u = tnth rhs i) 
          (vsolve_eq U).
Proof.
have lhsZ: linear lhsf by move=> a u v; apply/ffunP=> i; rewrite !ffunE linearP.
apply: (iffP memv_imgP) => [] [u Uu sol_u]; exists u => //.
  by move=> i; rewrite -[tnth rhs i]ffunE sol_u (lfunE (Linear lhsZ)) ffunE.
by apply/ffunP=> i; rewrite (lfunE (Linear lhsZ)) !ffunE sol_u.
Qed.

End Solver.

