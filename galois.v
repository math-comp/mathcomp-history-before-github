Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq tuple.
Require Import fintype finfun bigop ssralg poly polydiv.
Require Import zmodp vector algebra fieldext.
Require Import fingroup perm finset matrix mxalgebra.
Require Import separable.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope ring_scope.
Import GRing.Theory.

(******************************************************************************)

(* This should be moved to vector.v *)

Section Eigenspace.

Variable (K: fieldType) (V:vspaceType K) (f:'End(V)) (lambda:K).

Definition eigenspace := lker (f - lambda *: \1)%VS.

Lemma eigenspaceIn : forall x, (x \in eigenspace) = (f x == lambda *: x) .
Proof.
move => x.
by rewrite memv_ker add_lappE opp_lappE scale_lappE GRing.subr_eq0 unit_lappE.
Qed.

Lemma eigensubspaceImage :  forall vs, 
  (vs <= eigenspace)%VS -> (f @: vs <= vs)%VS.
Proof.
move => vs.
move/subvP => Hvs.
apply/subvP => x.
case/memv_imgP => y [Hy ->].
move/Hvs:(Hy).
rewrite eigenspaceIn.
move/eqP ->.
by apply: memvZl.
Qed.

Lemma eigensubspaceImageEq :
 forall vs, (lambda != 0) -> (vs <= eigenspace)%VS -> (f @: vs = vs)%VS.
Proof.
move => vs Hl Hvs.
apply: subv_anti.
apply/andP.
split; first by apply: eigensubspaceImage.
move/subvP: Hvs => Hvs.
apply/subvP => x Hx.
apply/memv_imgP.
exists (lambda^-1 *: x).
have Hlx : (lambda^-1 *: x \in vs) by rewrite memvZ Hx orbT.
split=>//.
move/Hvs: Hlx.
rewrite eigenspaceIn.
move/eqP ->.
by rewrite GRing.scalerA GRing.divff // GRing.scale1r.
Qed.

End Eigenspace.

Section Galois.

Variable F0 : fieldType.
Variable L : fieldExtType F0.

Let F : {algebra L} := aspace1 _.

(* Should I make this canonical by setting fixing (f @: E)^C ? *)
Definition kHom (K E : {vspace L}) : pred 'End(L) :=
fun f => (K <= eigenspace f 1)%VS &&
  (all (fun v1 => all (fun v2 => f (v1 * v2) == f v1 * f v2) (vbasis E))
       (vbasis E)).

Lemma kHomP : forall (K E: {vspace L}) (f : 'End(L)),
 reflect ((forall x, x \in K -> f x = x) /\
          (forall x y, x \in E -> y \in E -> f (x * y) = f x * f y))
 (kHom K E f).
Proof.
move => K E f.
apply: (iffP andP); case; last first.
 move => HK HE.
 split.
  apply/subvP => v Hv.
  by rewrite eigenspaceIn scale1r HK.
 apply/allP => x; move/memv_basis => Hx.
 apply/allP => y; move/memv_basis => Hy.
 apply/eqP.
 by apply: HE.
move/subvP => HK.
move/all_nthP => HE.
split.
 move => x Hx.
 apply/eqP.
 by rewrite -{2}[x]scale1r -eigenspaceIn HK.
move => x y.
do 2 move/coord_basis ->.
rewrite -mulr_suml ![f _]linear_sum -mulr_suml.
apply: eq_bigr => i _ /=.
rewrite -!mulr_sumr linear_sum.
apply: eq_bigr => j _ /=.
rewrite !linearZ /= -!scaler_mull linearZ.
repeat apply: f_equal.
apply/eqP.
move: (ltn_ord i).
rewrite -{2}(size_tuple (vbasis _)).
move/(HE 0).
move/all_nthP.
apply.
by rewrite (size_tuple (vbasis _)).
Qed.

Let kHomExtendF (E : {vspace L}) (f:'End(L)) (x y z: L) :=
 (map_poly f (poly_for_Fadjoin E x z)).[y].

Let kHomExtendF_linear : forall E f x y,
 linear (kHomExtendF E f x y).
Proof.
move => E f x y k a b.
rewrite /kHomExtendF poly_for_linear raddfD horner_lin.
congr (_ + _).
rewrite -[(map_poly f (poly_for_Fadjoin E x a)).[y]]mul1r.
rewrite scaler_mull -horner_scaler.
congr ((polyseq _).[_]).
apply/polyP => i.
rewrite !(coef_scaler, coef_map [linear of f]).
by rewrite -!scaler_mull !mul1r /= linearZ.
Qed.

Definition kHomExtend E f x y := lapp_of_fun (kHomExtendF E f x y).

Lemma kHomExtendE : forall E f x y z,
 kHomExtend E f x y z = (map_poly f (poly_for_Fadjoin E x z)).[y].
Proof. by move => E f x y z; rewrite lapp_of_funK. Qed.

Section kHomExtend.

Variables (K E : {algebra L}) (f : 'End(L)) (x y : L).
Hypothesis HKE : (K <= E)%VS.
Hypothesis Hf : kHom K E f.
Hypothesis Hy : root (map_poly f (minPoly E x)) y.

Lemma kHomExtend_poly : forall p,
 polyOver E p -> kHomExtend E f x y (p.[x]) = (map_poly f p).[y].
Proof.
move => p Hp.
rewrite kHomExtendE.
move/(poly_for_modp x): (Hp) ->.
case/kHomP: Hf => HK HE.
have Hfmin : monic (map_poly f (minPoly E x)).
 by rewrite /monic lead_coef_map_eq;
  move/eqP: (monic_minPoly E x) ->;
  rewrite /= HK ?memv1 // nonzero1r.
rewrite (divp_mon_spec (map_poly f p) Hfmin) !horner_lin.
move/eqP: Hy ->.
rewrite mulr0 add0r.
case/polyOver_suba: Hp => p' ->.
case/polyOver_suba: (minPolyOver E x) => q' ->.
rewrite -map_modp !map_polyE.
have Hlast : forall q : {poly suba_of E},
  (last (sa_val (1:suba_of E)) (map (sa_val_rmorphism E) q) != 0).
 move => q.
 rewrite last_map.
 rewrite -[0]/(sa_val (0:suba_of E)).
 apply/negP; move/eqP/suba_inj/eqP; apply/negP.
 by case q.
rewrite !(PolyK (Hlast _)) // -map_comp.
have Hmorph : rmorphism (f \o (sa_val_rmorphism E)).
 split; first by move => a b; rewrite /= linear_sub.
 split; first by move => a b; rewrite /= HE // subaP.
 by rewrite /= aunit_eq1 HK // memv1.
rewrite -map_polyE.
rewrite -[f \o sa_val_rmorphism E]/(GRing.RMorphism.apply (RMorphism Hmorph)).
by rewrite map_modp !map_polyE /= 2![map (_ \o _) _]map_comp.
Qed.

(*
Lemma kHomExtendkHom : forall (K E : {algebra L}) f x y,
 (K <= E)%VS -> kHom K E f -> root (map_poly f (minPoly E x)) y ->
 kHom K (Fadjoin E x) (kHomExtend E f x y).
Proof.
move => K E f x y.
move/subvP => HKE.
case/kHomP => HK HE Hy.
apply/kHomP; split.
 move => z Hz.
 rewrite kHomExtendE.
 move/HKE/poly_for_K: (Hz) ->.
 by rewrite (map_polyC [linear of f]) hornerC /= HK.
move => a b Ha Hb.
have Hab : (a * b) \in Fadjoin E x by apply: memv_mul.
rewrite !kHomExtendE -horner_mul.
congr ((polyseq _).[_]).
apply/polyP => i.

rewrite -map_poly_mul.
*)
 
End kHomExtend.



(*
Definition FieldAutomorphism (E:{vspace L}) (f : 'End(L) ) : bool :=
 [&& (f @: E == E)%VS, (E^C <= eigenspace f 1)%VS &
 (all (fun v1 => all (fun v2 => f (v1 * v2) == f v1 * f v2) (vbasis E))
      (vbasis E))].

Definition FixedField E f := (E :&: @eigenspace F0 L f 1)%VS.

Implicit Types (E K:{algebra L}).

Lemma AutomorphMul : forall E f, FieldAutomorphism E f -> 
forall u v, u \in E -> v \in E -> f (u * v) = f u * f v.
Proof.
move => E f.
case/and3P => _ _.
move/all_nthP => fmult u v.
move/coord_basis => -> Hv.
rewrite -mulr_suml !linear_sum -mulr_suml.
apply: eq_bigr => i _.
move/coord_basis: Hv ->.
rewrite -mulr_sumr !linear_sum.
apply: eq_bigr => j _ /=.
rewrite ![f (_ *: _)]linearZ -scaler_mull linearZ -scaler_mulr linearZ.
rewrite -scaler_mull -scaler_mulr.
do 2 apply: f_equal.
apply/eqP.
move: (ltn_ord i).
rewrite -{2}(size_tuple (vbasis _)).
move/(fmult 0 _).
move/all_nthP.
apply.
by rewrite size_tuple.
Qed.

Lemma AutomorphismIsUnit : forall E f, 
 FieldAutomorphism E f -> lker f = 0%:VS.
Proof.
move => E f.
case/and3P => Hf1 Hf2 _.
apply/eqP.
rewrite -(capfv (lker f)) -dimv_eq0 -(eqn_addr (\dim (f @: (fullv _)))).
rewrite add0n limg_ker_dim -(addv_complf E) limg_add.
move/eqP: Hf1 ->.
rewrite (eigensubspaceImageEq _ Hf2) //.
apply: nonzero1r.
Qed.

Lemma idAutomorphism : forall E, FieldAutomorphism E \1%VS.
Proof.
move => E.
apply/and3P; split; do ? (apply/allP => i _ ;apply/allP => j _);
 rewrite ?unit_lappE ?lim1g //.
apply/subvP => v _.
by rewrite eigenspaceIn unit_lappE scale1r.
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
  rewrite eigenspaceIn comp_lappE /=.
  move/(_ _ Hv): Hg2; rewrite eigenspaceIn; move/eqP->.
  move/(_ _ Hv): Hf2; rewrite eigenspaceIn.
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
have H1 : (f \^-1 @: E = E)%VS.
 apply/eqP.
 by rewrite -{1}Hf1 -limg_comp inv_lker0 ?kerf // lim1g.
apply/and3P; split.
- by rewrite H1.
- apply/subvP => v.
  move/Hf2=> Hv; rewrite eigenspaceIn GRing.scale1r in Hv.
  rewrite eigenspaceIn scale1r.
  rewrite -{1}(eqP Hv) /=.
  by rewrite -[(f \^-1)%VS (f _)](comp_lappE) inv_lker0 ?kerf // unit_lappE.
- rewrite <- Hf1.
  do 2 (apply/allP => ?; move/memv_basis;
        case/memv_imgP => ? [? ->]).
  rewrite -(AutomorphMul Ff) // -!{1}[(f \^-1)%VS (f _)](comp_lappE).
  by rewrite inv_lker0 ?kerf // !unit_lappE.
Qed.

Lemma FixedField_is_subfield : forall E f,
  FieldAutomorphism E f ->
  let K0 := FixedField E f in
  (has_aunit K0 && (K0 * K0 <= K0))%VS.
Proof.
move => E f Hf /=.
apply/andP; split.
 rewrite has_aunit1 // memv_cap.
 apply/andP; split.
  by apply: memv1.
 rewrite eigenspaceIn.
 apply/eqP.
 have Hf1 : f 1 != 0.
  by rewrite -memv_ker (AutomorphismIsUnit Hf) memv0 nonzero1r.
 apply: (mulfI Hf1).
 by rewrite -(AutomorphMul Hf) ?memv1 // scale1r !mulr1.
apply/prodvP => u v.
rewrite !memv_cap !eigenspaceIn !scale1r.
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
move/memv_addP => [va [vb [Hva Hvb ->]]].
move: Hva Hvb.
rewrite memv_cap HE.
rewrite linearD eigenspaceIn /=.
case/andP => _.
move/eqP ->.
move/Hf.
rewrite eigenspaceIn.
move/eqP ->.
by rewrite !scale1r.
Qed.
*)
End Galois.
