Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype paths connect finfun ssralg bigops finset.
Require Import groups commutators automorphism normal center. 
Import GroupScope.

Section LowerCentral.

Variable gT : finGroupType.
Notation sT := {set gT}.

Definition lc_elt (G: sT) := nosimpl 
  fix iter (n: nat)  {struct n} :=
    if n is n1.+1 then [~: iter n1, G] else G.

Lemma lc_elt_S G n: lc_elt G n.+1 = [~: lc_elt G n, G].
Proof. by done. Qed.

Lemma lc_elt_0 G: lc_elt G 0 = G.
Proof. by done. Qed.

Definition nilpotent (G: sT) := exists n, trivg (lc_elt G n).

Definition of_class (G: sT) (n: nat) :=
   trivg (lc_elt G n) /\ forall m, m < n -> ~~ trivg (lc_elt G m).

Lemma lcn_char (G: {group gT}) n: characteristic G (lc_elt G n).
Proof.
by move=> G n; elim: n => [| n Hrec]; try apply: char_comm;
  rewrite // setT_group_char.
Qed.

Lemma lcn_group_set n (G: {group gT}) : group_set (lc_elt G n).
Proof.
move=> n G; elim: n => [| n Hrec]; first by exact: groupP.
by exact: group_set_bigcap.
Qed.

Canonical Structure lcn_group n (G: {group gT}) := Group (lcn_group_set n G).

Lemma lcn_subset n (G: {group gT}) : lc_elt G n.+1 \subset lc_elt G n.
Proof.
move=> n G.
rewrite lc_elt_S sym_sgcomm subcomm_normal.
case: n => [| n]; first by exact: normG.
by rewrite /= lc_elt_S sym_sgcomm normGR.
Qed.

Lemma lcn_subset0 n (G: {group gT}) : lc_elt G n \subset G.
Proof.
move=> n G; elim: n => [| n Hrec]; first by exact: subset_refl.
apply: subset_trans (lcn_subset n G) Hrec.
Qed.

Lemma lcn_normal n (G: {group gT}) : lc_elt G n.+1 <|  lc_elt G n.
Proof.
move=> n G; rewrite /normal_subset lcn_subset.
apply/subsetP => x Hx; apply/normgP.
apply/eqP;  rewrite eqset_sub_card card_conjg leqnn andbT lc_elt_S -genJg gen_subG.
apply/subsetP=> xy; case/imsetP => x1; case/imset2P => x2 x3 Hx2 Hx3 -> ->.
rewrite conjg_Rmul groupM //.
  apply: mem_geng; apply/imset2P; exists x [~ x2, x3]^-1 => //.
  by rewrite groupV !groupM // ?groupV // (subsetP (lcn_subset0 n G)).
by apply: mem_geng; apply/imset2P; exists x2 x3.
Qed.

Lemma lcn_normal0 n (G: {group gT}) : lc_elt G n <|  G.
Proof.
move=> n G; apply: normal_char; exact: lcn_char.
Qed.

Lemma lcn_center n (G: {group gT}) :
  lc_elt G n / lc_elt G n.+1 \subset 'Z(G / lc_elt G n.+1).
Proof.
move=> n G.
apply/subsetP => H1; case/quotientP => x [Hx1 Hx2 ->].
apply/centerP; split.
  apply/quotientP; exists x; split=> //.
  by apply: (subsetP (lcn_subset0 n G)).
move=> H2; case/quotientP => y [Hy1 Hy2 ->]; rewrite /commute.
case Ht: (trivm (coset_of  (lcn_group n.+1 G))).
  by rewrite !(trivm_is_cst Ht).
move/negP: Ht; move/negP => Ht.
rewrite -!coset_of_morphM /= ?dom_coset //.
rewrite commgC coset_of_morphM ?dom_coset //;
 try by rewrite !groupM // ?groupV.
have F1: [~ x, y] \in lc_elt G n.+1.
  rewrite /= lc_elt_S; apply: mem_geng. 
  by apply /imset2P; exists x y.
by rewrite (coset_of_id F1) // mulg1.
Qed.

End LowerCentral.