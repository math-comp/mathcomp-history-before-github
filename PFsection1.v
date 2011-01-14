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


(* Move to fingroup and should replace card_classes_abelian in action *)
Lemma card_classes_abelianP : forall (gT : finGroupType) (G : {group gT}), 
  abelian G <-> #|classes G| = #|G|.
Proof.
move=> gT G.
have F : abelian G <-> forall i, i \in classes G -> #|i| = 1%N.
  split=> [HH i| HH].
    case/imsetP=> g InG ->; apply/eqP; apply/cards1P; exists g.
    by apply/cent_classP; move/subsetP: HH->.
  apply/subsetP=> g InG; apply/centP=> h InH.
  move/eqP: (HH _ (mem_classes InG)); case/cards1P=> l H.
  have: g \in g ^: G by exact: class_refl.
  have: g ^ h \in g ^: G by exact: memJ_class.
  rewrite H !inE; move/eqP=> H1; move/eqP=> H2.
  by rewrite /commute {2}H2 -H1 mulgA mulgV mul1g.
rewrite -sum_card_class; split=> [|HH].
  by move/F=> HH; rewrite (eq_bigr (fun _ => 1%N)) // sum_nat_const muln1.
have F1: forall g, g \in G -> (0 < #|g ^: G|)%N.
  by move=> g InG; rewrite (cardD1 g) class_refl.
apply/F=> i; case/imsetP=> g InG ->; move/eqP: HH.
rewrite (eq_bigr (fun  C : {set gT}  => #|C|.-1 + 1))%N; last first.
  by move=> C; case/imsetP=> h InH->; rewrite addn1 prednK // F1.
rewrite big_split sum_nat_const //= muln1 -{1}[#|_|]add0n eqn_addr.
rewrite eq_sym sum_nat_eq0.
move/forallP; move/(_ (g ^: G)); move/implyP; move/(_ (mem_classes InG)).
by case: #|_| (F1 _ InG)=> // [] [].
Qed.

(* Move to algC *)
Lemma eqN_eqC : forall (a b : nat), a = b <-> a%:R = b%:R :> C.
Proof.
move=> a b; split=> [->| Hr] //.
wlog le: a b Hr / (a <= b)%N.
  by move=> H; case/orP: (leq_total a b)=> HH; last apply: sym_equal;
     apply: H.
have: b%:R - a%:R = 0 :> C by rewrite Hr subrr.
rewrite -natr_sub //; move/eqP; move/GRing.charf0P: Cchar=> -> HH.
by apply anti_leq; rewrite le.
Qed.

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

(* Move to character *)
Definition clinear (G : {group gT}) f := is_char G f && (f 1%g == 1).

Lemma clinear1: forall (G: {group gT}) (f: cfun_type C gT),
  clinear G f -> f 1%g = 1.
Proof. by move=> G f CLf; apply/eqP; case/andP: CLf. Qed.

Lemma clinearM: forall (G: {group gT}) (f: cfun_type C gT) g h,
 clinear G f -> g \in G -> h \in G -> f (g * h)%g = f g * f h.
Proof.
move=> G f g h CLf InG InH.
case/andP: (CLf); case/is_charP=> // n [rG <-] HH.
move: (char1 rG); rewrite (eqP HH) -(eqN_eqC 1%N) => Hn.
rewrite !cfunE groupM // InG InH // !mul1r repr_mxM //.
move: {HH}rG; rewrite -Hn=> rG.
rewrite (mx11_scalar (rG g)) (mx11_scalar (rG h)) -scalar_mxM.
by rewrite !mxtrace_scalar !mulr1n.
Qed.

Lemma clinearV: forall (G: {group gT}) (f: cfun_type C gT) g,
 clinear G f -> g \in G -> f (g^-1)%g = (f g)^-1.
Proof.
move=> G f g CLf InG.
have F1: f g * f (g^-1%g) = 1.
  by rewrite -(clinearM CLf) ?groupV // mulgV (clinear1 CLf).
have F2: f g != 0.
  by apply/eqP=> HH; move: F1; rewrite HH mul0r=> HH1; case/eqP: (nonzero1r C). 
by apply: (mulfI F2); rewrite F1 divff.
Qed.

Lemma char_abelianP : forall (G : {group gT}),
  (forall (i : irr_class G), clinear G i) <-> (abelian G).
Proof.
move=> G; split=> HH.
  apply/card_classes_abelianP.
  rewrite eqN_eqC -sum_chi2 // (eq_bigr (fun i => 1)) //=.
    by rewrite sumr_const // -card_irr_class.
  by move=> i _; case/andP: (HH i)=> _ HH'; rewrite (eqP HH') exprS mulr1.
by move=> i; rewrite /clinear chi1 irr_degree_abelian // is_char_irr // eqxx.
Qed.

End Main.