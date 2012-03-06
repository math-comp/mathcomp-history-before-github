(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype bigop.
Require Import finfun ssralg matrix zmodp tuple vector.

(*****************************************************************************)
(*  * Finite dimensional algebras                                            *)
(*     algFType K       == type for finite dimension algebra structure.      *)
(*     algFMixin K      == builds the mixins containing the definition       *)
(*                         of an algebra over K.                             *)
(*     AlgFType T M     == packs the mixin M to build an algebra of type     *)
(*                         algFType K. The field K will be infered from the  *)
(*                         mixin M. The underlying type T should have a      *)
(*                         algType canonical structure.                      *)
(*      ... inherite definition and proofs from algType + vector.            *)
(*      (A * B)%VS      == the smallest vector space that contains           *)
(*                           {a * b | a \in A & b \in B}                     *)
(*      {algebra A}     == an algebra over A                                 *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Local Scope ring_scope.

Reserved Notation "{ 'algebra' T }" (at level 0, format "{ 'algebra'  T }").

Import GRing.Theory.

(* Finite dimensional algebra *)
Module AlgFType.

Section ClassDef.
Variable R : ringType.
Implicit Type phR : phant R.

Structure class_of (A : Type) : Type := Class {
  base1 : GRing.Algebra.class_of R A;
  mixin : Vector.mixin_of (GRing.Lmodule.Pack _ base1 A)
}.
Local Coercion base1 : class_of >-> GRing.Algebra.class_of.
Local Coercion mixin : class_of >-> Vector.mixin_of.
Definition base2 A (c : class_of A) := @Vector.Class _ _ c c.
Local Coercion base2 : class_of >-> Vector.class_of.

Structure type phR: Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.

Definition class phR (cT : type phR):=
  let: Pack _ c _ := cT return class_of cT in c.
Definition clone phR T cT c of phant_id (@class phR cT) c := @Pack phR T c T.

Definition pack phR A A0 (m0 : Vector.mixin_of (@GRing.Lmodule.Pack R _ A A0 A)) :=
  fun bT b & phant_id (@GRing.Algebra.class _ phR bT) b =>
  fun    m & phant_id m0 m => Pack phR (@Class A b m) A.

Definition eqType phR cT := Equality.Pack (@class phR cT) cT.
Definition choiceType phR cT := Choice.Pack (@class phR cT) cT.
Definition zmodType phR cT := GRing.Zmodule.Pack (@class phR cT) cT.
Definition lmodType phR cT := GRing.Lmodule.Pack phR (@class phR cT) cT.
Definition ringType phR cT := GRing.Ring.Pack (@class phR cT) cT.
Definition lalgType phR cT := GRing.Lalgebra.Pack phR (@class phR cT) cT.
Definition algType phR cT := GRing.Algebra.Pack phR (@class phR cT) cT.
Definition vectType phR  cT := Vector.Pack phR (@class phR cT) cT.

Definition vector_ringType phR  cT :=
  @Vector.Pack R phR  (GRing.Ring.sort (@ringType phR cT)) 
    (class cT) (GRing.Ring.sort (ringType cT)).

End ClassDef.

Module Exports.

Coercion base1 : class_of >-> GRing.Algebra.class_of.
Coercion mixin : class_of >-> Vector.mixin_of.
Coercion base2 : class_of >-> Vector.class_of.
Coercion eqType : type >->  Equality.type.
Canonical Structure eqType.
Coercion choiceType : type >-> Choice.type.
Canonical Structure choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical Structure zmodType.
Coercion lmodType : type>->  GRing.Lmodule.type.
Canonical Structure lmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical Structure ringType.
Coercion lalgType : type >-> GRing.Lalgebra.type.
Canonical Structure lalgType.
Coercion algType : type >-> GRing.Algebra.type.
Canonical Structure algType.
Coercion vectType : type >-> Vector.type.
Canonical Structure vectType.
Canonical Structure vector_ringType.
Bind Scope ring_scope with sort.
Notation algFType R := (@type _ (Phant R)).
Notation AlgFType R m :=
   (@pack _ (Phant R) _ _ m _ _ id _ id).

End Exports.

End AlgFType.
Export AlgFType.Exports.

Notation "1" := (injv 1) : vspace_scope.

Section algFTypeTheory.

Variable R: comRingType. 

Definition matrixAlgFType n := AlgFType R (matrix_vectMixin R n.+1 n.+1).

End algFTypeTheory.

Canonical Structure matrixAlgFType.

Section AlgebraDef.
Variable (K : fieldType) (A : algFType K).
Implicit Type u v : A.
Implicit Type vs : {vspace A}.

Definition amull u : 'End(A) := linfun (u \*o @idfun A).
Local Notation "\*l a" := (amull a) (at level 10): vspace_scope.

Definition amulr u : 'End(A) := linfun (u \o* @idfun A).
Local Notation "\*r a" := (amulr a) (at level 10): vspace_scope.

Lemma size_prodv (vs1 vs2 : {vspace A}) :
  size (allpairs ( *%R) (vbasis vs1) (vbasis vs2)) == (\dim vs1 * \dim vs2)%N.
Proof. by rewrite size_allpairs !size_tuple. Qed.

Definition prodv vs1 vs2: {vspace A} := span (Tuple (size_prodv vs1 vs2)).

Local Notation "A * B" := (prodv A B) : vspace_scope.

Lemma memv_prod : forall vs1 vs2 a b, a \in vs1 -> b \in vs2 -> a * b \in (vs1 * vs2)%VS.
Proof.
move=> vs1 vs2 a b Hvs1 Hvs2.
rewrite (coord_vbasis Hvs1) (coord_vbasis Hvs2).
rewrite mulr_suml; apply: memv_suml => i _.  
rewrite mulr_sumr; apply: memv_suml => j _.
rewrite -scalerAl -scalerAr scalerA memvZ //.
apply: memv_span; apply/allpairsP; exists ((vbasis vs1)`_i,(vbasis vs2)`_j).
by rewrite !mem_nth // size_tuple.
Qed.

Lemma prodvP : forall vs1 vs2 vs3,
  reflect (forall a b, a \in vs1 -> b \in vs2 -> a * b \in vs3)
          (vs1 * vs2 <= vs3)%VS.
Proof.
move=> vs1 vs2 vs3; apply: (iffP idP).
  move=> Hs a b Ha Hb; apply: subv_trans Hs; exact: memv_prod.
move=> Ha; apply/subvP=> v.
move/coord_span->; apply: memv_suml => i _.
apply: memvZ=> /=.
set u := allpairs _ _ _.
have: i < size u by rewrite (eqP (size_prodv _ _)).
move/(mem_nth 0); case/allpairsP=> [[x1 x2] [I1 I2 ->]].
by apply Ha; apply: vbasis_mem.
Qed.

Lemma prodv_inj : forall (x y : A), (x * y)%:VS = (x%:VS * y%:VS)%VS.
Proof.
move => x y.
apply: subv_anti.
apply/andP; split.
 by apply: memv_prod; rewrite memv_inj.
apply/prodvP => a b.
case/injvP => ca ->.
case/injvP => cb ->.
by rewrite -scalerAr -scalerAl !memvZ ?memv_inj.
Qed.

Lemma dimv1: \dim (1%VS : {vspace A}) = 1%N.
Proof. by rewrite dim_injv oner_neq0. Qed.

Lemma dim_prodv : forall vs1 vs2, \dim (vs1 * vs2) <= \dim vs1 * \dim vs2.
Proof.
move => vs1 vs2.
by rewrite (leq_trans (dim_span _)) // size_allpairs !size_tuple.
Qed.

Lemma voner_neq0 : (1 != 0 :> {vspace A})%VS.
Proof. by apply/eqP=> HH; move/eqP: dimv1; rewrite HH dimv0=> HH1. Qed.

Lemma vbasis1 : exists k, k != 0 /\ vbasis 1 = [:: k%:A] :> seq A.
Proof.
move: (vbasis 1) (@vbasisP K A 1); rewrite dim_injv oner_neq0.
case/tupleP=> x X0; rewrite {X0}tuple0 => defX; have Xx := mem_head x nil.
have /injvP[k def_x] := basis_mem defX Xx.
exists k; split; last by rewrite def_x.
by have:= basis_not0 defX Xx; rewrite def_x scaler_eq0 oner_eq0 orbF.
Qed.

Lemma prod0v: left_zero 0%VS prodv.
Proof.
move=> vs; apply subv_anti; rewrite sub0v andbT.
apply/prodvP=> a b; case/injvP=> k1 -> Hb.
by rewrite scaler0 mul0r mem0v.
Qed.

Lemma prodv0: right_zero 0%VS prodv.
Proof.
move=> vs; apply subv_anti; rewrite sub0v andbT.
apply/prodvP=> a b Ha; case/injvP=> k1 ->.
by rewrite scaler0 mulr0 mem0v.
Qed.

Lemma prod1v: left_id 1%VS prodv.
Proof.
case: vbasis1=> k [Hk He] /=.
move=> vs; apply subv_anti; apply/andP; split.
  apply/prodvP=> a b; case/injvP=> k1 -> Hb.
  by rewrite -scalerAl mul1r memvZ.
apply/subvP=> v Hv.
rewrite (coord_vbasis Hv); apply: memv_suml => i _ /=.
rewrite memvZ // -[_`_i]mul1r memv_prod ?(orbT, memv_inj) //.
by apply: vbasis_mem; apply: mem_nth; rewrite size_tuple.
Qed.

Lemma prodv1: right_id 1%VS prodv.
Proof.
case: vbasis1=> k [Hk He] /=.
move=> vs; apply subv_anti; apply/andP; split.
  apply/prodvP=> a b Ha; case/injvP=> k1 ->.
  by rewrite -scalerAr mulr1 memvZ.
apply/subvP=> v Hv; rewrite (coord_vbasis Hv).
apply: memv_suml => i _ /=.
rewrite memvZ // -[_`_i]mulr1 memv_prod ?(orbT, memv_inj) //.
by apply: vbasis_mem; apply: mem_nth; rewrite size_tuple.
Qed.

Lemma prodvA: associative prodv.
Proof.
move=> vs1 vs2 vs3; apply subv_anti; apply/andP.
split; apply/prodvP=> a b Ha Hb.
  rewrite (coord_vbasis Ha) mulr_suml.
  apply: memv_suml => i _ /=.
  move/coord_span: Hb->; rewrite mulr_sumr.  
  apply: memv_suml => j _ /=.
  rewrite -scalerAl -scalerAr scalerA memvZ //.
  set u := allpairs _ _ _.
  have: j < size u by rewrite (eqP (size_prodv _ _)).
  move/(mem_nth 0); case/allpairsP=> [[x1 x2] [I1 I2 ->]].
  by rewrite mulrA !memv_prod // ?vbasis_mem // mem_nth // size_tuple.
move/coord_span: Ha->; rewrite (coord_vbasis Hb).
rewrite mulr_suml; apply: memv_suml => i _ /=.  
rewrite mulr_sumr; apply: memv_suml => j _ /=.
rewrite -scalerAl -scalerAr scalerA memvZ //.
set u := allpairs _ _ _; have: i < size u by rewrite (eqP (size_prodv _ _)).
move/(mem_nth 0); case/allpairsP=> [[x1 x2] [I1 I2 ->]].
by rewrite -mulrA !memv_prod // ?vbasis_mem // mem_nth // size_tuple.
Qed.

Lemma prodv_monol : forall vs vs1 vs2, (vs1 <= vs2 -> vs1 * vs <= vs2 * vs)%VS.
Proof.
move=> vs vs1 vs2 Hvs; apply/prodvP=> a b Ha Hb; apply: memv_prod=> //.
by apply: subv_trans Hvs.
Qed.

Lemma prodv_monor : forall vs vs1 vs2, (vs1 <= vs2 -> vs * vs1 <= vs * vs2)%VS.
Proof.
move=> vs vs1 vs2 Hvs; apply/prodvP=> a b Ha Hb; apply: memv_prod=> //.
by apply: subv_trans Hvs.
Qed.

Lemma prodv_addl: left_distributive prodv addv.
Proof.
move=> vs1 vs2 vs3; apply subv_anti; apply/andP; split.
  apply/prodvP=> a b; case/memv_addP=> v1 v2 [Hv1 Hv2 ->] Hb.
  by rewrite mulrDl; apply: memv_add; apply: memv_prod.
apply/subvP=> v;  case/memv_addP=> v1 Hv1 [v2 Hv2 ->].
apply: memvD.
  move: v1 Hv1; apply/subvP; apply: prodv_monol; exact: addvSl.
move: v2 Hv2; apply/subvP; apply: prodv_monol; exact: addvSr.
Qed.

Lemma prodv_addr: right_distributive prodv addv.
Proof.
move=> vs1 vs2 vs3; apply subv_anti; apply/andP; split.
  apply/prodvP=> a b Ha;case/memv_addP=> v1 Hv1 [v2 Hv2 ->].
  by rewrite mulrDr; apply: memv_add; apply: memv_prod.
apply/subvP=> v;  case/memv_addP=> v1 Hv1 [v2 Hv2 ->].
apply: memvD.
  move: v1 Hv1; apply/subvP; apply: prodv_monor; exact: addvSl.
move: v2 Hv2; apply/subvP; apply: prodv_monor; exact: addvSr.
Qed.

(* Building the predicate that checks is a vspace has a unit *)
Let feq T vs f1 f2 : (\dim vs + \dim vs).-tuple T :=
  [tuple of map f1 (vbasis vs) ++ map f2 (vbasis vs)].

Let feq_lshift : forall vs T (f1 f2 : _ -> T) (i : 'I_(\dim vs)),
   let b := vbasis vs in 
  tnth (feq vs f1 f2) (lshift _ i) = f1 b`_i.
Proof.
move=> vs T f1 f2 i b; set v1 := f1 _.
rewrite (tnth_nth v1) /= nth_cat size_map size_tuple ltn_ord.
by rewrite (nth_map 0) ?size_tuple.
Qed.

Let feq_rshift : forall vs T (f1 f2 : _ -> T) i,
   let b := vbasis vs in 
  tnth (feq vs f1 f2) (rshift _ i) = f2 b`_i.
Proof.
move=> vs T f1 f2 i b; set v2 := f2 _.
rewrite (tnth_nth v2) /= nth_cat size_map size_tuple ltnNge leq_addr /=.
by rewrite addKn (nth_map 0) ?size_tuple.
Qed.

Definition has_aunit vs := 
  (\dim vs != 0%N) && vsolve_eq (feq vs amull amulr) (feq vs id id) vs.

Lemma has_aunitP : forall vs,
  reflect
   (exists u, 
     [/\ u \in vs, u != 0 & forall x, x \in vs -> u * x = x /\ x = x * u])
   (has_aunit vs).
Proof.
move=> vs; apply: (iffP andP).
  case=> Hd; case/vsolve_eqP=> /= u H1u H2u; exists u; rewrite H1u.
  suff Hu: forall x : A, x \in vs -> u * x = x /\ x = x * u.
    split=> //; apply/eqP=> Hu0.
    case: (Hu _ (memv_pick vs)); rewrite Hu0 mul0r.
    by move/esym/eqP; rewrite vpick0 -dimv_eq0 => /idPn.
  move=> x /coord_vbasis->.
  rewrite mulr_suml mulr_sumr; split; apply eq_bigr=> i /= _.
    rewrite -scalerAr; congr (_ *: _).
    by have:= H2u (rshift _ i); rewrite !{1}feq_rshift /= lfunE.
  rewrite -scalerAl /=; congr (_ *: _).
  by have:= H2u (lshift _ i); rewrite !{1}feq_lshift /= lfunE.
case=> u [H1u H2u H3u]; split.
  by rewrite dimv_eq0; apply: contraTneq H1u => ->; rewrite memv0.
apply/vsolve_eqP; exists u => // i.
rewrite -[i]splitK /unsplit; case: split => o.
  rewrite !feq_lshift lfunE /= -tnth_nth.
  by have [] := H3u _ (vbasis_mem (mem_tnth o _)).
rewrite !feq_rshift lfunE /= -tnth_nth.
by have [] := H3u _ (vbasis_mem (mem_tnth o _)).
Qed.

Lemma has_aunit1 : forall vs, 1 \in vs -> has_aunit vs.
Proof.
move=> vs Hvs; apply/has_aunitP.
exists 1; split=> //; first exact: oner_neq0.
by move=> *; rewrite !(mulr1, mul1r).
Qed.
  
Structure aspace : Type := ASpace {
    a2vs :> {vspace A};
    _ : ((has_aunit a2vs) && (a2vs * a2vs <= a2vs))%VS 
}.

Definition aspace_of of phant A := aspace.
Local Notation "{ 'algebra' T }" := (aspace_of (Phant T)) : type_scope.

Canonical Structure aspace_subType :=
  Eval hnf in [subType for a2vs by aspace_rect].
Canonical Structure aspace_eqMixin := [eqMixin of aspace by <:].
Canonical Structure aspace_eqType := Eval hnf in EqType aspace aspace_eqMixin.
Definition aspace_choiceMixin := [choiceMixin of aspace by <:].
Canonical Structure aspace_choiceType :=
  Eval hnf in ChoiceType aspace aspace_choiceMixin.

Canonical Structure aspace_of_subType := Eval hnf in [subType of {algebra A}].
Canonical Structure aspace_of_eqType := Eval hnf in [eqType of {algebra A}].
Canonical Structure aspace_for_choiceType :=  Eval hnf in [choiceType of {algebra A}].

Implicit Type gs: {algebra A}.

Lemma aunit_subproof gs (b := vbasis gs) :
  {u | u \in gs & forallb i, let x := tnth b i in (x * u == x) && (u * x == x)}.
Proof.
apply: sig2W; have /has_aunitP[u]: has_aunit gs by have /andP[] := valP gs.
case=> gs_u _ id_gs_u; exists u => //=; apply/forallP=> i.
by have /id_gs_u[-> <-] := vbasis_mem (mem_tnth i _); rewrite eqxx.
Qed.

Definition aunit gs := s2val (aunit_subproof gs).

Lemma memv_unit gs : aunit gs \in gs.
Proof. by rewrite /aunit; case: aunit_subproof. Qed.

Lemma aunitl gs : {in gs, left_id (aunit gs) *%R}.
Proof.
rewrite /aunit; case: aunit_subproof => u _ /= /forallP id_u x /coord_vbasis->.
rewrite mulr_sumr; apply: eq_bigr => i /= _; rewrite -scalerAr; congr (_ *: _).
by rewrite -tnth_nth; have /andP[_ /eqP] := id_u i.
Qed.

Lemma aunitr gs : {in gs, right_id (aunit gs) *%R}.
Proof.
rewrite /aunit; case: aunit_subproof => u _ /= /forallP id_u x /coord_vbasis->.
rewrite mulr_suml; apply: eq_bigr => i /= _; rewrite -scalerAl; congr (_ *: _).
by rewrite -tnth_nth; have /andP[/eqP] := id_u i.
Qed.

Lemma aunit1 : forall gs, (aunit gs == 1) = (1 \in gs).
Proof.
move=> gs; apply/eqP/idP=> H; first by rewrite -H memv_unit.
by move: (aunitr H); rewrite mul1r.
Qed.

Lemma aoner_neq0 : forall gs, aunit gs != 0.
Proof.
move=> gs; apply/eqP=> Eu0.
move: (aunitr (memv_pick gs)); rewrite Eu0 mulr0.
move/(@sym_equal _ _ _); move/eqP; rewrite vpick0 -dimv_eq0.
by apply/negP; case gs=> vs /=; case/andP; case/andP.
Qed.

Fact aspace1_subproof : has_aunit 1 && (1 * 1 <= 1)%VS.
Proof. 
rewrite prod1v subv_refl andbT.
apply/has_aunitP; exists 1; split; first by exact: memv_inj.
  exact: oner_neq0.
by move=> x; rewrite mul1r mulr1.
Qed.
Canonical aspace1 : {algebra A} := ASpace aspace1_subproof.

Lemma aspacef_subproof : has_aunit fullv && (fullv * fullv <= @fullv _ A)%VS.
Proof. by rewrite subvf has_aunit1 ?memvf. Qed.

Canonical aspacef : {algebra A} := ASpace aspacef_subproof.

Lemma asubv : forall gs, (gs * gs <= gs)%VS.
Proof. by case=> vs /= /andP[]. Qed.

Lemma memv_mul : forall gs x y,
  x \in gs -> y \in gs -> x * y \in gs.
Proof. by move => gs x y Hx Hy; move/prodvP: (asubv gs); apply. Qed.

Lemma aspace_cap_subproof : forall gs1 gs2, 
  aunit gs1 = aunit gs2 ->
  let gs := (gs1 :&: gs2)%VS in ((has_aunit gs) && (gs * gs <= gs))%VS.
Proof.
move=> gs1 gs2 Ha; apply/andP; split.
  apply/has_aunitP; exists (aunit gs1); split.
  - by rewrite memv_cap memv_unit Ha memv_unit.
  - by exact: aoner_neq0.
  move=> x; rewrite  memv_cap; case/andP=> Hg _.
  by rewrite !(aunitl,aunitr). 
rewrite subv_cap; apply/andP; split.
  apply: (subv_trans (prodv_monol _ (capvSl _ _))).
  apply: (subv_trans (prodv_monor _ (capvSl _ _))).
  exact: asubv.
apply: (subv_trans (prodv_monol _ (capvSr _ _))).
apply: (subv_trans (prodv_monor _ (capvSr _ _))).
exact: asubv.
Qed.

Definition aspace_cap gs1 gs2 (u : aunit gs1 = aunit gs2) : {algebra A} := 
  ASpace (aspace_cap_subproof u).

End AlgebraDef.

Notation "{ 'algebra' T }" := (aspace_of (Phant T)) : type_scope.
Notation "A * B" := (prodv A B) : vspace_scope.

Section SubAlgFType.

(* The algType structure of subvs_of als for als : {algebra A}.               *)
(* We can't use the rpred-based mixin, because als need not contain 1.        *)
Variable (K : fieldType) (A : algFType K) (als : {algebra A}).

Definition subvs_one := Subvs (memv_unit als).
Definition subvs_mul (u v : subvs_of als) := 
  Subvs (subv_trans (memv_prod (subvsP u) (subvsP v)) (asubv _)).

Fact subvs_mulA : associative subvs_mul.
Proof. by move=> u v w; apply/val_inj/mulrA. Qed.
Fact subvs_mu1l : left_id subvs_one subvs_mul.
Proof. by move=> u; apply/val_inj/aunitl/(valP u). Qed.
Fact subvs_mul1 : right_id subvs_one subvs_mul.
Proof. by move=> u; apply/val_inj/aunitr/(valP u). Qed.
Fact subvs_mulDl : left_distributive subvs_mul +%R.
Proof. move=> u v w; apply/val_inj/mulrDl. Qed.
Fact subvs_mulDr : right_distributive subvs_mul +%R.
Proof. move=> u v w; apply/val_inj/mulrDr. Qed.

Definition subvs_ringMixin :=
  RingMixin subvs_mulA subvs_mu1l subvs_mul1 subvs_mulDl subvs_mulDr
            (aoner_neq0 _).

Canonical subvs_ringType := Eval hnf in RingType (subvs_of als) subvs_ringMixin.

Lemma subvs_scaleAl k (x y : subvs_of als) : k *: (x * y) = (k *: x) * y.
Proof. exact/val_inj/scalerAl. Qed.

Canonical subvs_lalgType := Eval hnf in LalgType K (subvs_of als) subvs_scaleAl.

Lemma subvs_scaleAr k (x y : subvs_of als) : k *: (x * y) = x * (k *: y).
Proof. exact/val_inj/scalerAr. Qed.

Canonical subvs_algType := Eval hnf in  AlgType K (subvs_of als) subvs_scaleAr.
Canonical subvs_algFType := AlgFType K (subvs_vectMixin als).

End SubAlgFType.

Module FalgLfun.
Section FalgLfun.

Variable (R : comRingType) (A : algFType R).
Import Vector.InternalTheory.

Fact FalgType_proper : Vector.dim A > 0.
Proof.
rewrite lt0n; apply: contraNneq (oner_neq0 A) => A0.
by apply/eqP/v2r_inj; move: (v2r 1); rewrite linear0 A0; apply: thinmx0.
Qed.

Canonical Falg_fun_ringType := lfun_ringType FalgType_proper.
Canonical Falg_fun_lalgType := lfun_lalgType FalgType_proper.
Canonical Falg_fun_algType := lfun_algType FalgType_proper.
Canonical Falg_fun_FalgType := Eval hnf in AlgFType R (lfun_vectMixin A A).
 
End FalgLfun.
End FalgLfun.
