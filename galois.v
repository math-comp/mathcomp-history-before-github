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

Let F : {algebra L } := aspace1 _.

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
move/all_nthP => fmult u v Hu Hv.
have Hspan : (is_span E (vbasis E)) by rewrite is_basis_span ?is_basis_vbasis.
rewrite (is_span_span Hspan Hu) (is_span_span Hspan Hv).
rewrite !linear_sum /=; apply eq_bigr => j _.
rewrite -!mulr_suml linear_sum /=.
apply: eq_bigr => i _.
rewrite -scaler_mull linearZ /= -scaler_mulr linearZ /=.
symmetry.
rewrite ![f _]linearZ /=.
rewrite -scaler_mull.
rewrite -[f _ * _]scaler_mulr.
repeat apply: f_equal.
symmetry.
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
rewrite mulr1.
by rewrite -(AutomorphMul Hf) ?memv1 // mulr1.
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
 by rewrite eigenspaceIn (Automorph1 Hf) scale1r.
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

End Galois.

