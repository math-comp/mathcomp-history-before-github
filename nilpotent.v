Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype paths connect finfun ssralg bigops finset.
Require Import groups commutators automorphism normal center. 
Import GroupScope.

Section LowerCentral.

Variable gT : finGroupType.
Notation sT := {set gT}.

Definition lcn_elt (G: sT) := nosimpl 
  fix iter (n: nat)  {struct n} :=
    if n is n1.+1 then [~: iter n1, G] else G.

Lemma lcn_eltS G n: lcn_elt G n.+1 = [~: lcn_elt G n, G].
Proof. by done. Qed.

Lemma lcn_elt_0 G: lcn_elt G 0 = G.
Proof. by done. Qed.

Definition nilpotent (G: sT) := exists n, trivg (lcn_elt G n).

Definition of_class (G: sT) (n: nat) :=
   trivg (lcn_elt G n) /\ forall m, m < n -> ~~ trivg (lcn_elt G m).

Lemma lcn_char (G: {group gT}) n: characteristic G (lcn_elt G n).
Proof.
by move=> G n; elim: n => [| n Hrec]; try apply: char_comm;
  rewrite // setT_group_char.
Qed.

Lemma lcn_group_set n (G: {group gT}) : group_set (lcn_elt G n).
Proof.
move=> n G; elim: n => [| n Hrec]; first by exact: groupP.
by exact: group_set_bigcap.
Qed.

Canonical Structure lcn_group n (G: {group gT}) := Group (lcn_group_set n G).

Lemma lcn_subset n (G: {group gT}) : lcn_elt G n.+1 \subset lcn_elt G n.
Proof.
move=> n G.
rewrite lcn_eltS sym_sgcomm subcomm_normal.
case: n => [| n]; first by exact: normG.
by rewrite /= lcn_eltS sym_sgcomm normGR.
Qed.

Lemma lcn_subset0 n (G: {group gT}) : lcn_elt G n \subset G.
Proof.
move=> n G; elim: n => [| n Hrec]; first by exact: subset_refl.
apply: subset_trans (lcn_subset n G) Hrec.
Qed.

Lemma lcn_normal n (G: {group gT}) : lcn_elt G n.+1 <|  lcn_elt G n.
Proof.
move=> n G; rewrite /normal_subset lcn_subset.
apply/subsetP => x Hx; apply/normgP.
apply/eqP;  rewrite eqset_sub_card card_conjg leqnn andbT lcn_eltS -genJg gen_subG.
apply/subsetP=> xy; case/imsetP => x1; case/imset2P => x2 x3 Hx2 Hx3 -> ->.
rewrite conjg_Rmul groupM //.
  apply: mem_geng; apply/imset2P; exists x [~ x2, x3]^-1 => //.
  by rewrite groupV !groupM // ?groupV // (subsetP (lcn_subset0 n G)).
by apply: mem_geng; apply/imset2P; exists x2 x3.
Qed.

Lemma lcn_normal0 n (G: {group gT}) : lcn_elt G n <|  G.
Proof.
move=> n G; apply: normal_char; exact: lcn_char.
Qed.

Lemma lcn_center n (G: {group gT}) :
  lcn_elt G n / lcn_elt G n.+1 \subset 'Z(G / lcn_elt G n.+1).
Proof.
move=> n G.
apply/subsetP => H1; case/quotientP => x [Hx1 Hx2 ->].
apply/centerP; split.
  apply/quotientP; exists x; split=> //.
  by apply: (subsetP (lcn_subset0 n G)).
move=> H2; case/quotientP => y [Hy1 Hy2 ->]; rewrite /commute.
case Ht: (trivm (coset_of  (lcn_elt G n.+1))).
  by rewrite !(trivm_is_cst Ht).
move/negP: Ht; move/negP => Ht.
rewrite -!coset_of_morphM /= ?dom_coset //.
rewrite commgC coset_of_morphM ?dom_coset //;
 try by rewrite !groupM // ?groupV.
have F1: [~ x, y] \in lcn_elt G n.+1.
  rewrite /= lcn_eltS; apply: mem_geng. 
  by apply /imset2P; exists x y.
by rewrite (coset_of_id F1) // mulg1.
Qed.

End LowerCentral.


Section UpperCentral.

Variable gT : finGroupType.
Notation sT := {set gT}.

Definition ucn_elt (G: sT) := nosimpl 
  fix iter (n: nat)  {struct n}: sT :=
    if n is n1.+1 then 
      [set x \in G |  (fun y => [~ x, y]) @: G \subset iter n1] 
    else 1.

Lemma ucn_elt0 (G: sT): ucn_elt G 0 = 1.
Proof. done. Qed.

Lemma ucn_elt1 (G: {group gT}): ucn_elt G 1 = 'Z(G).
Proof.
move=> G; rewrite /ucn_elt.
apply/eqP; rewrite eqset_sub; apply/andP; split; apply/subsetP => x; last first.
  case/centerP => H1 H2; rewrite inE H1; apply/subsetP => y.
  case/imsetP => z Hz ->; rewrite inE; apply/commgP; exact: H2.
rewrite inE; case/andP => H1x H2x.
apply/centerP; split => // y Hy.
have F1: [~ x, y] \in (fun y : gT => [~ x, y]) @: G by apply/imsetP; exists y.
by apply/commgP; move: (subsetP H2x _ F1); rewrite inE.
Qed.

Lemma ucn_eltS (G: {group gT}) n: 
  ucn_elt G n.+1 = [set x \in G |  (fun y => [~ x, y]) @: G \subset ucn_elt G n].
Proof. done. Qed.

Lemma ucn_group_set n (G: {group gT}) : group_set (ucn_elt G n).
Proof.
move=> n G ; elim: n => [| n Hrec]; first exact: group_set_unit.
pose g0 := Group Hrec.
apply/group_setP; split.
  rewrite ucn_eltS inE group1.
  by apply/subsetP => x; case/imsetP => y Hy ->; rewrite comm1g (group1 g0).
move=> x y; rewrite ucn_eltS !inE.
case/andP=> H1x H2x; case/andP=> H1y H2y.
rewrite groupM //; apply/subsetP=> z; case/imsetP=> t Ht ->.
rewrite commg_gmult_left (@groupM  _ g0) //; last first.
  by apply: (subsetP H2y); apply/imsetP; exists t.
have F1: [~ x, y] \in ucn_elt G n.
  by apply: (subsetP H2x); apply/imsetP; exists y.
have ->: [~ x, t] ^ y = [~ x, y]^-1 * [~ x, t * y].
  by rewrite commg_gmult_right mulgA mulVg mul1g.
rewrite groupM //; try rewrite groupV; apply: (subsetP H2x).
  by apply/imsetP; exists y.
by apply/imsetP; exists (t * y); rewrite // groupM.
Qed.


Canonical Structure ucn_group n (G: {group gT}) := Group (ucn_group_set n G).

Lemma ucn_elt_subset0 n (G: {group gT}) : ucn_elt G n \subset G.
Proof.
move=> [| n G]; first by exact: sub1G.
by rewrite ucn_eltS; apply/subsetP=> x; rewrite inE; case/andP.
Qed.


Lemma ucn_elt_char n (G: {group gT}) : characteristic G (ucn_elt G n).
Proof.
move=> n G; elim: n => [| n Hrec].
  by rewrite ucn_elt0 trivg_char.
(* Down to the definition :-( *)
apply/subset_charP; split; first by exact: ucn_elt_subset0.
move=> f Hf; case/andP: (Hf) => H1f H2f; apply/subsetP=> x; case/imsetP => y /=.
rewrite ucn_eltS inE; case/andP => Hy H1y ->.
rewrite !inE; apply/andP; split; first by rewrite (group_perm.perm_closed _ H1f).
apply/subsetP => z; case/imsetP => z1 Hz1 ->.
pose z2 := (group_perm.perm_inv f z1).
have Hz2: z2 \in G by rewrite -(group_perm.perm_closed _ H1f) group_perm.permKV.
have ->: z1 = f z2 by rewrite group_perm.permKV.
rewrite -(morphic_comm H2f) //.
case/subset_charP: Hrec => _; move/(_ _ Hf).
move/subsetP=> HH; apply: HH.
apply/imsetP; exists [~ y, z2] => //.
by apply: (subsetP H1y); apply/imsetP; exists z2.
Qed.

Lemma ucn_elt_normal0 n (G: {group gT}) : ucn_elt G n <| G.
Proof. move=> n G; apply: normal_char; exact: ucn_elt_char. Qed.

(* Definition of Aschbacher *)
Lemma ucn_eltS1 (G: {group gT}) n: 
  ucn_elt G n.+1 = (coset_of (ucn_elt G n)) @^-1: 'Z(G/(ucn_elt G n)) :&: G.
Proof.
move=> G n; rewrite ucn_eltS.
case Ht: (trivm (coset_of (ucn_elt G n))).
  have F1: ucn_elt G n = G.
    apply/eqP; rewrite eqset_sub; case/andP: (ucn_elt_normal0 n G).
    by case/trivm_coset_of: Ht => -> ->.
  apply/eqP; rewrite eqset_sub; apply/andP; split; apply/subsetP => x; last first.
    rewrite !inE; (do 2 case/andP) =>  H1x H2x H3x; rewrite H3x F1.
    by apply/subsetP => y; case/imsetP => z Hz ->; exact: groupR.
  rewrite !inE; case/andP => HH _.
  by rewrite coset_of_id /= ?F1 // !group1.
move/negP: Ht; move/negP => Ht.
have F0: G \subset 'N(ucn_group n G) by case/andP: (ucn_elt_normal0 n G).
apply/eqP; rewrite eqset_sub; apply/andP; split; apply/subsetP => x; last first.
  rewrite !inE; (do 2 case/andP) =>  H1x H2x H3x; rewrite H3x.
  apply/subsetP => y; case/imsetP => z Hz ->.
  have F1: coset_of (ucn_elt G n) z \in G / ucn_elt G n.
    by apply/quotientP; exists z; repeat split => //; exact: (subsetP F0).
  apply: coset_of_idr; first by apply: (subsetP F0); exact: groupR.
  rewrite -(commg_coset F0) //.
  by apply/eqP; apply/commgP; apply: (centgP H2x).
rewrite !inE; case/andP => H1x H2x.
rewrite H1x andbT; apply/andP; split.
  by apply/quotientP; exists x; repeat split => //; apply: (subsetP F0).
apply/centgP => y; case/quotientP => z [H1z H2z] ->.
apply/commgP; rewrite (commg_coset F0) //.
apply/eqP; apply: coset_of_id.
by apply: (subsetP H2x); apply/imsetP; exists z.
Qed.

Lemma ucn_elt_subset n (G: {group gT}) : ucn_elt G n \subset ucn_elt G n.+1.
Proof.
move=> n G.
rewrite ucn_eltS1.
apply/subsetP => x Hx; rewrite inE.
have H1x: x \in G by exact: (subsetP (ucn_elt_subset0 n G)).
rewrite H1x andbT inE.
by rewrite coset_of_id // group1.
Qed.

Lemma ucn_elt_normal n (G: {group gT}) : ucn_elt G n <| ucn_elt G n.+1.
Proof.
move=> n G; apply/andP; split.
  exact: ucn_elt_subset.
apply/subsetP => x.
rewrite ucn_eltS => Hx.
rewrite inE in Hx; case/andP: Hx => Hx H1x.
rewrite inE; apply/subsetP => y.
case/imsetP => z Hz ->.
rewrite conjg_mulR groupM // groupVl // invg_comm.
apply: (subsetP H1x); apply/imsetP; exists z => //.
by apply: (subsetP (ucn_elt_subset0 n G)).
Qed.

Lemma ucn_elt_center n (G: {group gT}) :
  ucn_elt G n.+1 / ucn_elt G n \subset 'Z(G / ucn_elt G n).
Proof.
move=> n G.
apply/subsetP => x.
case/quotientP => y [H1y H2y ->].
move: H1y; rewrite /= ucn_eltS1.
by rewrite inE; case/andP; rewrite inE.
Qed.


Lemma ucn_lcn_step (m: nat) (G: {group gT}):
  lcn_elt _ G m = 1 -> ucn_elt G m = G.
Proof.
move=> m G Hm.
apply/eqP; rewrite eqset_sub  ucn_elt_subset0 -(lcn_elt_0 gT G) -{1}(subnn m).
elim: {1 4 5} m (leqnn m) => [| n].
  by rewrite subn0 Hm sub1G.
case: m Hm => // [m Hm Hrec Hlt].
have F1: n <= m.+1 by rewrite (leq_trans (leqnSn _) Hlt).
apply/subsetP => y Hy.
rewrite ucn_eltS inE (subsetP (lcn_subset0 _ (m - n) G)) //.
apply/subsetP => x; case/imsetP => x1 Hx1 ->.
apply: (subsetP (Hrec F1)); rewrite leq_subS //.
exact: commg_in_commgs.
Qed.


Lemma ucn_lcn_step1 (m: nat) (G: {group gT}):
  ucn_elt G m = G -> lcn_elt _ G m = 1.
Proof.
move=> n G Hn.
apply/eqP; rewrite eqset_sub sub1G andbT.
rewrite  -(ucn_elt0  G)  -(subnn n).
elim: {1 3 5} n (leqnn n) => [| i].
 rewrite subn0 Hn (lcn_elt_0 gT G) => _;exact: subset_refl.
case: n Hn => // [n Hn Hrec Hlt].
have F1: i <= n.+1 by rewrite (leq_trans (leqnSn _) Hlt).
rewrite lcn_eltS .
have HH: G\subset G by apply: subset_refl.
have H1: [~: lcn_elt gT G i, G] \subset [~: ucn_elt G (n.+1 - i), G] by apply: (genSg (commg_setSS (Hrec F1) HH)).
apply: (subset_trans H1).
rewrite subSS leq_subS // ucn_eltS gen_subG.
apply/subsetP => x.
case/imset2P => x1 x2; rewrite !inE.
case/andP => H1x1 H2x1 Hx2 ->.
apply: (subsetP H2x1).
by apply/imsetP; exists x2.
Qed.

End UpperCentral.