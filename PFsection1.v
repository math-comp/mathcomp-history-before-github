(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient finalg action zmodp.
Require Import commutator cyclic center pgroup matrix mxalgebra mxpoly.
Require Import mxrepresentation vector algC character.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.


(**************************************************************************)
(* This file contains the proof of Section1 of Peterfalvi's book          *)
(**************************************************************************)

Section Main.

Variable (gT : finGroupType).

Hypothesis groupC : group_closure_field C gT.

Local Notation "'{ f '^/' N }" := (qfun_of_cfun N f).
Local Notation "'{ f '^()' }" := (cfun_of_qfun f).

(* This corresponds to 1.2 in PF *)
Lemma not_in_ker_char0: forall (H G: {group gT}) (i : irr_class G) g,
   g \in G -> H <| G -> ~(H \subset cker G i) -> 'C_H[g] = 1%g -> i g = 0.
Proof.
move=> H G i g InG NN NoN HC.
have FC: group_closure_field C (coset_groupType H).
  by apply: coset_splitting_field.
have: (#|'C_G[g]| <= #|'C_(G/H)[coset H g]|)%N.
  suff->: #|'C_G[g]| = #|'C_G[g] / H|%G.
    by apply: (subset_leq_card (quotient_subcent1 H G g)).
  apply: card_isog.
  apply: isog_trans (second_isog _); last first.
    apply: subset_trans (normal_norm NN).
    by apply: subcent1_sub.
  suff->: H :&: 'C_G[g] = 1%g by exact: quotient1_isog.
    rewrite -HC.
    apply/setP=> h; rewrite inE.
    apply/andP/subcent1P; case=> H1 H2; split=> //.
      by move/subcent1P: H2; case.
    apply/subcent1P; split=> //.
    by apply: (subsetP (normal_sub NN)).
have F1: coset H g \in (G/H)%g.
  by rewrite -imset_coset; apply/imsetP; exists g.
rewrite le_leC.
move: (chi_second_orthogonal_relation groupC InG InG).
rewrite class_refl=> <-.
move: (chi_second_orthogonal_relation FC F1 F1).
rewrite class_refl=> <-.
have->:
    \sum_(i : irr_class (G/H)) (i (coset H g)) * (i (coset H g))^* =
    \sum_(i : irr_class G | H \subset cker G i) (i g) * (i g)^*.
  pose h (i : irr_class (G/H)) :=
         odflt (irr_class1 G)  [pick j \in irr_class G | '{i ^()} == j].
  have hE: forall i : irr_class (G/H), '{i^()} = h i.
    move=> i'; rewrite /h; case: pickP=> [j'|/=].
      by rewrite andTb; move/eqP->.
    case (cfunq_irr i' NN)=> j Hj.
    by move/(_ j); rewrite Hj eqxx.
  pose h' (i : irr_class G) :=
     odflt (irr_class1 (G/H))  [pick j \in irr_class (G/H) | '{i^/H} == j].
  have h'E: forall i : irr_class G, H \subset cker G i -> '{i^/H} = h' i.
    move=> i' Cf; rewrite /h'.
    case: pickP=> [j|/=]; first by rewrite andTb; move/eqP->.
    by case (qfunc_irr groupC NN Cf)=> j Hj; move/(_ j); rewrite Hj eqxx.
  rewrite (reindex h).
  apply: eq_big=> i'; first by rewrite -hE cker_cfunq // is_char_irr.
    by move=> _; rewrite -hE cfunqE // (subsetP (normal_norm NN)).
  exists h'=> i'; rewrite !inE // => Hi.
    apply: irr_cfun_inj.
    rewrite -h'E -hE //; last first.
      by apply: cker_cfunq=> //; apply: is_char_irr.
    by apply: (@cfunq_id _ _ G) => //; apply: is_char_irr.
  apply: irr_cfun_inj.
  rewrite -hE -h'E //; apply: (@qfunc_id _ _ G)=> //.
  by apply: is_char_irr.
rewrite (bigID (fun i : irr_class G => H \subset cker G i)) //=.
set S := \sum_(i | ~~ _) _; set S' := \sum_(i | _) _ => HH.
have F2: 0 = S.
  apply: leC_anti; last by rewrite -(leC_add2l S') addr0.
  by apply: posC_sum=> j _; rewrite /leC subr0; exact: repC_pconj.
apply/eqP;  have: i g * (i g)^* == 0.
  apply/eqP; apply: (posC_sum_eq0 _ (sym_equal F2)).
    by move=> j _; rewrite /leC subr0; exact: repC_pconj.
  by move/negP: NoN->; rewrite  /index_enum -enumT mem_enum.
rewrite mulf_eq0; case/orP=> //.
by rewrite conjC_eq0.
Qed. 

End Main.
