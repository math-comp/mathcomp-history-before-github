(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Frobenius theorem                                                  *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)

Require Import ssreflect ssrbool ssrfun ssrnat.
Require Import eqtype fintype div finset.
Require Import groups normal cyclic center.

(* Require Import seq paths connect zp. *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section Kb.

Variables (gT : finGroupType) (H : {group gT}).
Variable x : gT.
Hypothesis Hx : x \in H.

(* proof to be reworked *)
Lemma orderg_krg : forall p (Hp : prime p) l y,
    y \in 'C_H[x] / cyclic x ->
    #[x] = (p ^ l.+1)%N ->
    coprime #[x] #[y] ->
  exists z, [&& coprime #[x] #[z],
                coset_of (cyclic x) z == y
              & z \in 'C_H[x]].
Proof.
move=> p Hp l y.
case/morphimP => i [Hi1 Hi2 ->] Hox {y} Hy.
set y := coset_of (cyclic x) i.
have F1: coset_of (cyclic x) (i ^+ #[y]) = 1.
  by rewrite morphX ?orderg_expn1 // dom_coset ?Hnt.
have F2: i ^+ #[y] \in 'N(cyclic x).
  by rewrite groupX.
case/cyclicP: (coset_of_idr F2 F1) => j Hj.
have:= Hy; rewrite coprime_sym {1}/coprime => Hy1.
have:= bezoutr #[x] (orderg_pos y).
rewrite gcdnC (eqP Hy1); case => u Hu.
case/dvdnP => v Hv {Hy1}.
have C1: x ^+ v \in 'C_H[x].
  by apply: centraliserXr => //; exact: centraliser_id.
have F0: commute x i by move/centraliserP: Hi2 =>[_].
have F4: x ^+ (v * #[y]) = x.
  by rewrite -Hv expgn_add expg1 mulnC expgn_mul orderg_expn1 exp1gn mulg1.
have F5: x ^+ (j * v * #[y]) = i ^+ #[y].
  by rewrite -!mulnA mulnC expgn_mul F4 Hj.
pose k1 := (j * v * (#[x] - 1))%N.
have F6: ((x ^+ k1) * i) ^+ #[y] = 1.
  rewrite expMgn; last by apply: commute_sym; exact: commuteX.
  rewrite -expgn_mul -F5 -expgn_add. 
  rewrite /k1 -!mulnA !(mulnA j) -muln_addr.
  rewrite -{2}(mul1n #[y]) -muln_addl.
  rewrite addnC subnK; last exact: orderg_pos.
  by rewrite mulnC -!mulnA expgn_mul orderg_expn1 exp1gn.
have F7: x ^+ k1 \in 'C_H[x].
  by apply: centraliserXr; exact: centraliser_id.
exists (x ^+ k1 * i).
rewrite groupM // andbT; apply/andP; split.
  move/eqP: F6; rewrite -orderg_dvd.
  case/dvdnP => k Hk.
  by move: Hy; rewrite Hk coprime_mulr; case/andP.
rewrite coset_of_morphM -/y; last by rewrite ?dom_coset ?Hnt.
  rewrite coset_of_id ?cyclic_in; gsimpl.
by rewrite ?Hnt // groupX //= (subsetP (normG _)) // cyclicnn.
Qed.

Lemma KB_image: forall p (Hp : prime p) l s,
  #[x] = (p ^ l.+1)%N -> coprime #[x] s ->
  image (coset_of (cyclic x)) [pred z \in 'C_H[x] | #[z] %| s]
     =i [pred z \in 'C_H[x] / cyclic x | #[z] %| s].
Proof.
move=> p Hp l s H1 H2 x1; apply/idP/idP; rewrite inE /= => H3.
  case: (diinv_exists H3) => y /=; do 2![case/andP] => HH1 HH2 HH3.
  rewrite orderg_dvd; apply/andP; split.
    apply/morphimP; exists y => //; last by rewrite -(eqP HH3).
    by apply: (subsetP (normal_centraliser Hx)).
  rewrite -(eqP HH3) -morphX.
    rewrite (_ : y ^+ s = 1) ?coset_of_id ?morph1 //=.
    by apply/eqP; rewrite -orderg_dvd.
  by rewrite ?Hnt // ?(subsetP (centraliser_normaliser Hx)) ?Ht.
case/andP: H3 => H3 H4.
have F1: coprime #[x] #[x1].
  case/dvdnP: H4 => k1 Hk1.
  by move: H2; rewrite Hk1 coprime_mulr; case/andP.
case: (orderg_krg Hp H3 H1 F1) => x2.
case/and3P=> Hx1 Hx2 Hx3.
have E1: x1 = coset_of (cyclic x) x2 by symmetry; apply/eqP.
rewrite E1 -topredE /= mem_image //= Hx3 /=.
apply: dvdn_trans H4.
rewrite -(@gauss _ #[x]); last by rewrite coprime_sym.
rewrite mulnC orderg_dvd.
have: x1 ^+ #[x1] = 1 by rewrite orderg_expn1.
rewrite {1}E1 -morphX => [/= E2|]; last first.
  rewrite ?Ht //. 
  by rewrite (subsetP (centraliser_normaliser Hx)) // Ht.
have E3: x2 ^+ #[x1] \in cyclic x.
  apply: coset_of_idr => //. 
  by rewrite groupX ?(subsetP (centraliser_normaliser Hx)).
case/cyclicP: E3 => i; rewrite expgn_mul => <-.
by rewrite -expgn_mul mulnC expgn_mul orderg_expn1 exp1gn.
Qed.

Lemma KB_card_image: forall p (Hp : prime p) l s,
    #[x] = (p ^ l.+1)%N -> coprime #[x] s ->
  #|[pred z \in 'C_H[x] | #[z] %| s]|
     = #|[pred z \in 'C_H[x] / cyclic x | #[z] %| s]|.
Proof.
move=> p Hp l s Hx1 Hx2.
symmetry; rewrite -(eq_card (KB_image Hp Hx1 Hx2)).
apply: card_dimage=> y1 y2; case/andP => H1 H2; case/andP => H3 H4 H5.
have: y1^-1 * y2 \in cyclic x.
  have sCN := subsetP (centraliser_normaliser Hx).
  apply: coset_of_idr; first by rewrite sCN // groupM // groupV.
  rewrite coset_of_morphM; first by [rewrite coset_ofV H5 mulVg];
  by rewrite ?Ht ?groupV ?sCN.  
case/cyclicP => i Hi.
have F0: y1 * (x ^+ i) = y2 by rewrite Hi; gsimpl.
have F1: #[x] %| i * (#[y1] * #[y2]).
  rewrite orderg_dvd expgn_mul; apply/eqP.
  rewrite -(exp1gn _ #[y1]) -(orderg_expn1 y2).
  rewrite -!expgn_mul -F0 expMgn //; last first.
    by apply: commuteX; case/centraliserP: H1.
  by rewrite (mulnC _ #[y1]) !expgn_mul orderg_expn1 exp1gn mul1g.
rewrite -F0 -{1}(mulg1 y1); congr (_ * _); symmetry.
apply/eqP; rewrite -orderg_dvd. 
rewrite mulnC gauss // in F1.
rewrite coprime_mulr; apply/andP; split.
  case/dvdnP: H2 => k1 Hk1.
  by rewrite Hk1 coprime_mulr in Hx2; case/andP: Hx2.
case/dvdnP: H4 => k1 Hk1.
by rewrite Hk1 coprime_mulr in Hx2; case/andP: Hx2.
Qed.

End Kb.

Section PConstituent.

Variable p s : nat.
Hypothesis primep : prime p.
Hypothesis coprimeps : coprime p s.
Variable gT : finGroupType.
Variable G : {group gT}.

(***********************************************************************)
(*                                                                     *)
(*        p - constituent                                              *)
(*                                                                     *)
(***********************************************************************)

Definition pconst (x : gT) :=
  let u := (p ^ logn p #[x])%N in
  let v := #[x] %/ u in
  let: (k1, k2) := abezoutn u v in x ^+ (v * k2).
  
Definition prem (x: gT) :=
  let u := (p ^ logn p #[x])%N in
  let v := #[x] %/ u in
  let: (k1, k2) := abezoutn u v in (x ^+ (u * k1)).

Lemma pconst_group: forall x, x \in G -> pconst x \in G.
Proof.
move => x y; rewrite /pconst.
by case: abezoutn => _ n; apply: groupX.
Qed.

Lemma prem_group: forall x, x \in G -> prem x \in G.
Proof.
move => x y; rewrite /prem.
by case: abezoutn => n _; apply: groupX.
Qed.

Lemma pconst_conjg: forall x y,
  pconst (x ^ y) = (pconst x) ^ y.
Proof.
move => x y; rewrite /pconst.
by rewrite orderg_conjg; case: abezoutn => _ n; rewrite conjXg.
Qed.

Lemma prem_conjg: forall x y,
  prem (x ^ y) = (prem x) ^ y.
Proof.
move => x y; rewrite /prem.
by rewrite orderg_conjg; case: abezoutn => n _; rewrite conjXg.
Qed.

Lemma pconst_rem: forall x, (pconst x) * (prem x) = x.
Proof.
move => x; rewrite /pconst /prem.
set l := logn p #[x].
set t :=  #[x] %/ p ^ l.
have F0: #[x] = (p ^ l * t)%N.
  case/dvdnP: (dvdn_p_part p #[x]); rewrite /p_part -/l => k Hk.
  rewrite /t {2}Hk (mulnC k) divn_mulr ?(mulnC _ k) //.
  by move: (orderg_pos x); rewrite Hk; case: (p ^ l)%N => //; rewrite muln0. 
have F1: coprime (p ^ l)  t.
  case Eq1: l => [| l1]; first by rewrite expn0 coprime1n.
  rewrite coprime_expl // prime_coprime //.
  apply/negP => H1; case/dvdnP: H1 => k1 Hk1. 
  have F1: p ^ l.+1 %| #[x].
    by rewrite F0 Hk1 (mulnC k1) mulnA (mulnC _ p) -expnS dvdn_mulr.
  have:= dvdn_leq_log primep (orderg_pos x) F1.
  by rewrite logn_exp -/l // ltnn.
case Eq1: #[x] => [| n1].
  by move: (orderg_pos x); rewrite Eq1.
case: n1 Eq1 => [| n1] Eq1.
   move: (orderg_expn1 x); rewrite Eq1 expg1 => F2.
   by case: abezoutn => k1 k2; rewrite F2 !exp1gn mulg1.
have F2: 1 < p ^ l * t by rewrite -F0 Eq1.
move: (abezout_coprime F2 F1); case: abezoutn => k1 k2.
rewrite (mulnC t) -!F0 => H1.
rewrite -expgn_add addnC mulnC [_ + _](divn_eq _ #[x]) H1.
rewrite expgn_add expg1 mulnC expgn_mul orderg_expn1 exp1gn.
exact: mul1g.
Qed.

Lemma pconst_remC: forall x, commute (pconst x) (prem x).
Proof.
move => x; rewrite /commute /pconst /prem.
case: abezoutn => k1 k2.
by rewrite -!expgn_add addnC.
Qed.

Lemma pconstC: forall x, commute x (pconst x).
Proof.
by move=> x; rewrite /commute -{1 4}(pconst_rem x) {2}(pconst_remC x) !mulgA.
Qed.

Lemma premC: forall x, commute x (prem x).
Proof.
by move=> x; rewrite /commute -{1 4}(pconst_rem x) {1}pconst_remC !mulgA.
Qed.


Lemma orderg_pconst: forall x, #[pconst x] = (p ^ logn p #[x])%N.
Proof.
move => x; move: (pconst_rem x); rewrite /pconst /prem.
set l := logn p #[x].
set t :=  #[x] %/ p ^ l.
have F0: #[x] = (p ^ l * t)%N.
  case/dvdnP: (dvdn_p_part p #[x]); rewrite /p_part -/l => k Hk.
  rewrite /t {2}Hk (mulnC k) divn_mulr ?(mulnC _ k) //.
  by move: (orderg_pos x); rewrite Hk; case: (p ^ l)%N => //; rewrite muln0. 
have P1: (0 < t) by move: (orderg_pos x); rewrite F0; case t; rewrite ?muln0.
have P2: (0 < p ^ l) by move: (orderg_pos x); rewrite F0; case (p ^ l)%N.
have P3: 0 < t * _.+1 by move=> k; rewrite ltn_0mul P1.
have P4: 0 < p ^ l * _.+1 by move=> k; rewrite ltn_0mul P2.
case E1: (abezoutn _ _) => [[| k1] [| k2]] //.
- rewrite !muln0 !expg0 mulg1 => H1. 
  move/eqP: (sym_equal F0); rewrite -H1 orderg1 eqn_mul1.
  by case/andP; move/eqP. 
- rewrite muln0 expg0 mulg1 => H1. 
  have F1: t %| t * k2.+1 - 1.
    apply: (@dvdn_trans #[x]); first by rewrite F0 dvdn_mull.
    rewrite orderg_dvd; apply/eqP; apply: (mulg_injl x).
    by rewrite -{1}(expg1 x) mulg1 -expgn_add subnK.
  rewrite dvdn_subr ?dvdn_mulr // dvdn1 in F1.
  by rewrite H1 F0 (eqP F1) muln1.
- rewrite muln0 expg0 mul1g => H1. 
  have F1: p ^ l %| p ^ l * k1.+1 - 1.
    apply: (@dvdn_trans #[x]); first by rewrite F0 dvdn_mulr.
    rewrite orderg_dvd; apply/eqP; apply: (mulg_injl x).
    by rewrite -{1}(expg1 x) mulg1 -expgn_add subnK // ltn_0mul P2.
  rewrite dvdn_subr ?dvdn_mulr // dvdn1 in F1.
  by rewrite orderg1 (eqP F1).
have P5: 0 < gcdn t k1.+1 by rewrite ltn_0gcd orbT.
have P6: 0 < gcdn (p ^ l) k2.+1 by rewrite ltn_0gcd orbT.
have F1 := @orderg_gcd _ x _ (P3 k2).
rewrite F0 -(mulnC t) gcdn_mul2l divn_pmul2l // in F1.
have F2 := @orderg_gcd _ x _ (P4 k1).
rewrite F0 gcdn_mul2l divn_pmul2l // in F2.
move=> H1; rewrite F1.
have F3:  x ^+ (#[x ^+ (t * k2.+1)] * #[x ^+ (p ^ l * k1.+1)]) = 1.
  rewrite -{1}H1 -expgn_add -expgn_mul muln_addl expgn_add.
  rewrite !expgn_mul orderg_expn1 exp1gn mul1g.
  by rewrite -expgn_mul mulnC expgn_mul orderg_expn1 exp1gn.
move/eqP: F3; rewrite -orderg_dvd F0 F1 F2.
rewrite -[(_ * (t %/ _))%N]muln1.
have G1 := dvdn_gcdl (p ^ l) k2.+1.
rewrite dvdn_eq in G1; rewrite -{1}(eqP G1) -mulnA (mulnC _ t).
have G2 := dvdn_gcdl t k1.+1.
rewrite dvdn_eq in G2; rewrite -{1}(eqP G2) !mulnA.
set u := (_ %/ _ * _)%N.
rewrite -mulnA dvdn_pmul2l //.
  rewrite dvdn1 eqn_mul1; case/andP => _ H2.
  by rewrite (eqP H2) divn1.
by move: P1 P2; rewrite -(eqP G1) -(eqP G2) !ltn_0mul; do 2!case/andP=> -> _.
Qed.

(* there should be a short cut better than this cut-and-paste *)
Lemma orderg_prem: forall x, #[prem x] = #[x] %/ p ^ logn p #[x].
Proof.
move => x; move: (pconst_rem x); rewrite /pconst /prem.
set l := logn p #[x].
set t := #[x] %/ p ^ l.
have F0: #[x] = (p ^ l * t)%N.
  by apply/eqP; rewrite -mulnC eq_sym -dvdn_eq dvdn_p_part.
have [P1 P2]: 0 < t /\ 0 < p ^ l.
  by apply/andP; rewrite andbC -ltn_0mul -F0 orderg_pos.
have P3: 0 < t * _.+1 by case: {+}t P1.
have P4: 0 < p ^ l * _.+1 by case: (p ^ l)%N P2.
case E1: (abezoutn _ _) => [[| k1] [| k2]].
- rewrite !muln0 !expg0 mulg1 => H1. 
  move/eqP: (sym_equal F0); rewrite -H1 orderg1 eqn_mul1.
  by case/andP => _ H2; rewrite (eqP H2).
- rewrite muln0 expg0 mulg1 => H1. 
  have F1: t %| t * k2.+1 - 1.
    apply: (@dvdn_trans #[x]); first by rewrite F0 dvdn_mull.
    rewrite orderg_dvd; apply/eqP; apply: (mulg_injl x).
    by rewrite -{1}(expg1 x) mulg1 -expgn_add subnK.
  rewrite dvdn_subr ?dvdn_mulr // dvdn1 in F1.
  by rewrite orderg1 (eqP F1).
- rewrite muln0 expg0 mul1g => H1. 
  have F1: p ^ l %| p ^ l * k1.+1 - 1.
    apply: (@dvdn_trans #[x]); first by rewrite F0 dvdn_mulr.
    rewrite orderg_dvd; apply/eqP; apply: (mulg_injl x).
    by rewrite -{1}(expg1 x) mulg1 -expgn_add subnK.
  rewrite dvdn_subr ?dvdn_mulr // dvdn1 in F1.
  by rewrite H1 F0 (eqP F1) mul1n.
have P5: 0 < gcdn t k1.+1 by rewrite ltn_0gcd orbT.
have P6: 0 < gcdn (p ^ l) k2.+1 by rewrite ltn_0gcd orbT.
have F1 := @orderg_gcd _ x _ (P3 k2).
rewrite F0 -(mulnC t) gcdn_mul2l divn_pmul2l // in F1.
have F2 := @orderg_gcd _ x _ (P4 k1).
rewrite F0 gcdn_mul2l divn_pmul2l // in F2.
move => H1; rewrite F2.
have F3:  x ^+ (#[x ^+ (t * k2.+1)] * #[x ^+ (p ^ l * k1.+1)]) = 1.
  rewrite -{1}H1 -expgn_add -expgn_mul muln_addl expgn_add.
  rewrite !expgn_mul orderg_expn1 exp1gn mul1g.
  by rewrite -expgn_mul mulnC expgn_mul orderg_expn1 exp1gn.
move/eqP: F3; rewrite -orderg_dvd F0 F1 F2.
rewrite -[(_ * (t %/ _))%N]muln1.
have G1 := dvdn_gcdl (p ^ l) (k2.+1).
rewrite dvdn_eq in G1; rewrite -{1}(eqP G1) -mulnA (mulnC _ t).
have G2 := dvdn_gcdl t (k1.+1). 
rewrite dvdn_eq in G2; rewrite -{1}(eqP G2) !mulnA.
set u := (_ %/ _ * _)%N. 
rewrite -mulnA dvdn_pmul2l //.
  rewrite dvdn1 eqn_mul1; case/andP => H2 _.
  by rewrite (eqP H2) divn1.
by move: P1 P2; rewrite -(eqP G1) -(eqP G2) !ltn_0mul; do 2!case/andP=> -> _.
Qed.

Lemma pconst_coprime: forall x, coprime #[pconst x] #[prem x].
Proof.
move => x.
rewrite orderg_pconst orderg_prem.
case E1: (logn _ _) => [| n].
  by rewrite expn0 divn1 coprime1n.
rewrite coprime_expl // -E1.
case (@p_part_coprime p #[x]) => //; first exact: orderg_pos.
move => xx Hxx Hr; rewrite {1}Hr divn_mull // ltn_0exp.
by case: p primep.
Qed.

Lemma pconst_prem_orderg: forall x, #[x] = (#[pconst x] * #[prem x])%N.
Proof.
move=> x; rewrite -{1}(pconst_rem x).
apply: orderg_mul; first exact: pconst_remC.
exact: pconst_coprime.
Qed.

Definition spconst x := 
  [set y \in G | (pconst y == x) && (#[y] %| #[x] * s)].
  
Lemma spconst_uniq: forall x1 x2 y,
  y \in spconst x1 -> y \in spconst x2 -> x1 = x2.
Proof.
move=> x1 x2 y; rewrite !inE.
case/and3P => _ H1 _; case/and3P => _ H2 _.
by rewrite -(eqP H1); apply/eqP.
Qed.

Lemma spconst_conjgs: forall a b,
  b \in G -> spconst (a ^ b) = spconst a :^ b.
Proof.
move => a b Hb; apply/setP => x; apply/idP/idP.
  rewrite mem_conjg !inE; case/and3P=> H1 H2 H3; apply/and3P; split.
  - by rewrite groupJr ?groupV.
  - by rewrite pconst_conjg (eqP H2) conjgK.
  by move: H3; rewrite !orderg_conjg.
case/imsetP=> y; rewrite !inE; case/and3P=> H1 H2 H3 ->{x}; apply/and3P; split.
- exact: groupJ.
- by rewrite pconst_conjg (eqP H2).
by move: H3; rewrite !orderg_conjg.
Qed.

Lemma spconst_card: forall a b, b \in G -> #|spconst (a ^ b)| = #|spconst a|.
Proof.
move => a b Hb; rewrite -(card_imset (mem (spconst a)) (conjg_inj b)).
apply eq_card => x.
by rewrite spconst_conjgs // sconjg_imset.
Qed.

Lemma pconst_subset_centralizer : forall y, spconst y \subset 'C_G[y].
Proof.
move=> y; apply/subsetP=> x; rewrite inE; case/and3P=> Hx1 Hx2 Hx3.
apply/centraliserP; split=> //.
apply: commute_sym; rewrite -(eqP Hx2); exact: pconstC.
Qed.

Lemma pconst_mul_in: forall y z l, 
  y \in G -> z \in G -> commute y z -> #[y] = (p ^ l.+1)%N -> #[z] %| s ->
  y * z \in spconst y.
Proof.
move => y z l Hy Hz H H1 H2.
have F0: coprime #[y] #[z].
  rewrite H1 coprime_expl //.
  case/dvdnP: H2 coprimeps => k ->.
  by rewrite coprime_mulr; case/andP.
have F1: #[y * z] = (p ^ l.+1 * #[z])%N.
  by rewrite -H1; apply: orderg_mul.
rewrite inE; apply/and3P; split; first exact: groupM; last first.
  by rewrite orderg_mul // dvdn_pmul2l // orderg_pos.
rewrite /spconst /pconst.
have F2:  1 < #[y * z].
  apply: leq_ltn_trans (orderg_pos z) _.
  rewrite -{1}(mul1n #[z]) F1 ltn_mul2r orderg_pos andTb.
  by rewrite -(expn0 p) ltn_exp2l // prime_gt1.
rewrite {1 3 5}F1 logn_mul // ?orderg_pos ?logn_exp //; last first.
  by rewrite ?ltn_0exp; case: p primep.
have FF: (p %| #[z]) = false.
  apply/negP; apply/negP.
  by rewrite -prime_coprime // -(@coprime_pexpl l.+1) // -H1.
rewrite lognE primep orderg_pos FF [l.+1]lock /= addn0;  unlock.
rewrite -H1 F1 -H1 divn_mulr ?orderg_pos //.
have F3: 1 < #[y] * #[z] by rewrite H1 -F1.
move: (abezout_coprime F3 F0).
case: abezoutn => k1 k2 H3; apply/eqP.
rewrite expMgn // (expgn_mul z) orderg_expn1 exp1gn mulg1 mulnC.
rewrite -(mul1g (y ^+ _)) -(exp1gn gT k1) -(orderg_expn1 y) -expgn_mul.
rewrite mulnC -expgn_add.
rewrite [_ + _](@divn_eq _ (#[y] * #[z])) H3 expgn_add expg1.
by rewrite mulnCA expgn_mul orderg_expn1 exp1gn mul1g.
Qed.

Lemma pconst_image: forall y l, y \in G ->
  #[y] = (p ^ l.+1)%N -> coprime #[y] s -> 
  [image prem of spconst y] =i [pred z \in 'C_G[y] | #[z] %| s]. 
Proof.
move=> y l Hy0 Hy Cy x1; apply/idP/idP; rewrite inE /=  => H1.
  case: (diinv_exists H1) => y1.
  rewrite /= inE /=; case/andP; case/and3P => HH1 HH2 HH3 HH4.
  rewrite  -(eqP HH4) -(eqP HH2) inE prem_group //=; apply/andP; split.
    apply/centg1P; apply: commute_sym; exact: pconst_remC.
  rewrite -(dvdn_pmul2r (orderg_pos (pconst y1))).
  rewrite mulnC -pconst_prem_orderg.
  by rewrite (eqP HH2) mulnC.
case/andP: H1 => H1 H2.
have F0: coprime #[y] #[x1].
  case/dvdnP: H2 => k Hk; rewrite Hk coprime_mulr in Cy.
  by case/andP: Cy.
have [F3 F1]: x1 \in G /\ commute y x1 by case/centraliserP: H1.
have F2: coprime p #[x1] by rewrite -(@coprime_pexpl l.+1) // -Hy. 
move: (pconst_mul_in Hy0 F3 F1 Hy H2); rewrite inE.
case/and3P => H3 H4 H5.
replace x1 with (prem (y * x1)).
  by apply: mem_image; rewrite /= inE H3 H4 H5.
apply: (mulg_injl y).
rewrite -{1}(eqP H4); exact: pconst_rem.
Qed.

Lemma pconst_card : forall y l, y \in G ->
  #[y] = (p ^ l.+1)%N ->
    #|spconst y| = #|[pred z \in 'C_G[y] | #[z] %| s]|. 
Proof.
move => y l Hy H.
have F0: coprime #[y] s by rewrite H coprime_expl.
symmetry; rewrite -(eq_card (pconst_image Hy H F0)).
apply: card_dimage=> y1 y2; rewrite /= !inE;
  case/and3P => H1 H2 H3; case/and3P => H4 H5 H6 H7.
by rewrite -(pconst_rem y1) (eqP H2) -(eqP H5) H7 pconst_rem.
Qed.

Lemma pconst_card_KRG: forall y l, y \in G -> 
  #[y] = (p ^ l.+1)%N ->  
  #|spconst y| = #|[pred z \in 'C_G[y] / cyclic y | #[z] %| s]|.
Proof.
move => y l Hy H.
rewrite (pconst_card Hy H).
apply: (KB_card_image Hy primep H).
by rewrite H coprime_expl.
Qed.

Definition spconstw y := 
  \bigcup_(i \in rcosets 'C_G[y] G) spconst (y ^ repr i).

Lemma spconstwP: forall x y, y \in G ->
  reflect (exists i, (i \in G) && (x \in spconst (y ^ i))) (x \in spconstw y).
Proof.
move => x y Hy; apply: (iffP idP).
 case/bigcupP => i Hi1 Hi2.
 exists (repr i); rewrite Hi2 andbT.
 case/rcosetsP: Hi1 => x1 Hx1 Hx2.
 move: (@repr_rcosetP gT 'C_G[y] x1).
 rewrite -Hx2.
 case => x2; rewrite inE; case/andP => Hx3 _.
 exact: groupM.
case => i; case/andP => Hi1 Hi2.
set r := 'C_G[y] :* i.
apply/bigcupP; exists r; first by apply/rcosetsP; exists i.
case: (repr r) / (repr_rcosetP 'C_G[y] i) => z /=; case/centraliserP=> _.
by move/commgP; move/conjg_fixP; rewrite conjgM => ->.
Qed.

Lemma card_spconstw: forall y l, y \in G -> #[y] = (p ^ l.+1)%N ->  
  #|spconstw y| = 
   (#|G : 'C_G[y]| * #|[pred z \in 'C_G[y] / cyclic y | #[z] %| s]|)%N.
Proof.
move=> y l Hy Oy.
rewrite /spconstw (@card_setnU_id _ _ _ _ #|spconst y|).
- congr muln => //.
  by exact: (pconst_card_KRG _ Oy).
- move => u v x Hu Hv /= Hsu Hsv.
  case/rcosetsP: Hu Hsu => i1 /= Hi1 ->{u}.
  case: (repr _) / (repr_rcosetP 'C_G[y] i1) => j1 Hj1 Hsu.
  case/rcosetsP: Hv Hsv => i2 /= Hi2 ->{v}.
  case: (repr _) / (repr_rcosetP 'C_G[y] i2) => j2 Hj2 Hsv.
  apply: rcoset_trans1 => /=; rewrite mem_rcoset; apply/centraliserP; split.
    by rewrite !in_group.
  apply/commgP; apply/conjg_fixP.
  have:= spconst_uniq Hsu Hsv; rewrite !conjgM.
  move: Hj1 Hj2; do 2![case/centraliserP=> _; move/commgP; move/conjg_fixP->].
  exact: (canLR (conjgK _)).
move=> x; case/rcosetsP=> i2 /= Hi2 ->; apply: spconst_card.
case: (repr _) / (repr_rcosetP 'C_G[y] i2) => y1; case/setIP=> Gy1 _.
exact: groupM.
Qed.

End PConstituent.

Section Frob.

Theorem frobenius: forall (gT : finGroupType) (G : {group gT}) n,
  n %| #|G| -> n %| #|[pred z \in G | #[z] %| n]|.
Proof.
pose f gT (H : group gT) n := [pred z \in H | #[z] %| n].
change (forall gT (G : group gT) n, n %| #|G| -> n %| #|f gT G n|).
move => gT G.
move: {G}#|G| {-2}G (leqnn #|G|) => n.
elim: n gT.
  by move=> gT H; move: (pos_card_group H); case: #|H|.
move=> k Rec gT G; rewrite leq_eqVlt; case/orP => Hk n Hn;
    last apply Rec => //.
have Hn1: n <= #|G| by apply: dvdn_leq. 
move: Hn; rewrite -(@subKn n #|G|) //.
set e := _ - n; elim: e {-2}e (leqnn e).
  case => // _ _; rewrite subn0.
  apply/dvdnP; exists 1%N; rewrite mul1n.
  apply: eq_card => x.
  rewrite inE /= /orderg; case E1: (x \in G) => //=.
  by rewrite group_dvdn // cyclic_h.
move => n1 Hrec e.
rewrite leq_eqVlt; case/orP => H H1; last apply Hrec => //.
move: H1; rewrite (eqP H).
set n2 := _ - n1.+1.
have Hn2: n2 < #|G| by rewrite /n2 (eqP Hk) ltnS subSS leq_subr.
move: (leq0n n2); rewrite leq_eqVlt; case/orP.
  move => HH; rewrite -(eqP HH).
  case/dvdnP; move => x; rewrite muln0 => Hx.
  by move: Hn2; rewrite Hx.
rewrite leq_eqVlt; case/orP;
  first by move => HH; rewrite -(eqP HH) !dvd1n.
move => Hn2b; case/dvdnP => [k1 Hk1].
have Hn2b0: 0 < n2 by case: (n2) Hn2b.
have HHk: 1 < k1.
  case: k1 Hk1 Hk Hn2; first by move => ->.
  case => //.
  by move => ->; rewrite mul1n ltnn.
pose p := pdiv k1.
have Hp := prime_pdiv HHk; rewrite -/p in Hp.
have Hp0: 0 < p by case: p Hp.
have Hp1: n2 * p %| #|G| by rewrite mulnC Hk1 dvdn_pmul2r ?dvdn_pdiv.
have Hp2: n2 * p <= #|G| by apply dvdn_leq => //; rewrite (eqP Hk).
have D1: n2 %| #|f gT G (n2 * p)%N|.
  apply: (@dvdn_trans (n2 * p)) => //.
    by rewrite dvdn_mulr ?dvdnn.
  rewrite -(@subKn (n2 * p) #|G|) //.
  apply Hrec; last by rewrite subKn.
  rewrite leq_sub_add -(@subnK n1.+1 #|G|).
    rewrite -ltnS -/n2 -[(_ + n1).+1]addnS addnC ltn_add2r.
    by rewrite -{1}(mul1n n2) mulnC ltn_pmul2l // prime_gt1.
  apply ltn_trans with (n1.+1); first exact: ltnSn.
  by rewrite -ltn_0sub -/n2; case: (n2) Hn2b.
rewrite -(@dvdn_addr #|predI (f gT G (n2 * p)%N) (predC (f gT G n2))|).
  case/dvdnP: D1 => u Hu; apply/dvdnP; exists u; rewrite -Hu.
  rewrite -(cardID (f gT G n2) (f gT G (n2 * p)%N)) addnC.
  congr (_ + _); last by apply: eq_card => x; rewrite !inE /= andbC.
  apply: eq_card => x; rewrite [f]lock !inE /= !inE /= -lock andbC /=.
  by case: andP => //= [[-> /= HH]]; rewrite (dvdn_trans HH) ?dvdn_mulr.
case (p_part_coprime Hp Hn2b0); rewrite /p_part => s.
rewrite mulnC; set l := logn p n2 => Hsl1 Hsl.
have P1: 0 < p ^ (l.+1) by rewrite ltn_0exp Hp0.
set A := (predI _ _).
have F1: forall z, z \in A ->
  exists u, coprime p u &&  (#[z] == u * p ^ l.+1)%N.
- move => z; case/andP => /=; case/andP => H1 Hb1 /=.
  rewrite H1 /=; move/negP => H2. 
  case/dvdnP: Hb1 => u Hu.
  case E1: (p %| u).
    case/dvdnP: (idP E1) => u1 Hu1.
    case H2; apply/dvdnP; exists u1.
    apply/eqP; rewrite -(@eqn_pmul2r p) //.
    by rewrite Hu Hu1 -mulnA (mulnC p) mulnA eq_refl.
  have E2: p ^ l.+1 %| #[z].
    rewrite -(@gauss _ u); first by
      rewrite -Hu Hsl expnS (mulnC _ p) mulnA dvdn_mulr ?dvdnn.
    by rewrite coprime_expl // prime_coprime // E1.  
  case/dvdnP: E2 => u1 Hu1.
  exists u1; rewrite Hu1 eq_refl andbT.
  have E2: (s == u * u1)%N.
    rewrite  -(@eqn_pmul2r (p ^ (l.+1))) //.
    by rewrite -mulnA -Hu1 -Hu (mulnC _ p) Hsl mulnA -expnS mulnC.
  rewrite (eqP E2) coprime_mulr in Hsl1.
  by case/andP: Hsl1.
rewrite {1}Hsl gauss_inv; last first.
  case: (l) => [| u]; last by rewrite coprime_expl.
  by rewrite expn0 /coprime -dvdn1 dvdn_gcdl.
apply/andP;split.
(* First case *)
  apply: (@dvdn_trans  ((p ^ l) * (p - 1))%N);
    first by rewrite dvdn_mulr.
  pose e1 x : pred gT := generator (cyclic x).
  have F2: (wpartition [set x | A x] (fun x => set_of (e1 x)) [set x | A x]).
    split.
      move=> u v x; rewrite /= !inE => Hu Hv Hu1 Hu2 y; rewrite /= !inE.
      by congr (_ == _); rewrite ((_ =P cyclic x) Hu1) ((_ =P cyclic x) Hu2).
    apply/eqP; apply/setP=> x; rewrite inE; apply/bigcupP/idP=> [[y]| Ax].
      rewrite !inE /= /f -andbA; case/and3P=> Gy y_p_n2; rewrite Gy /= => y_p_n2' e1_y_x.
      have{e1_y_x} e_x_y: cyclic x = cyclic y by symmetry; apply/eqP.
      have ->: x \in G.
        by apply: (subsetP (cyclic_h Gy)); rewrite -e_x_y cyclicnn.
      by rewrite /orderg e_x_y y_p_n2.
    by exists x; rewrite inE // [e1 _ _]eqxx.
  rewrite -cardsE; apply: card_dvdn_partition F2 _ => x; rewrite inE => Ax.
  case: (F1 _ Ax) => z; case/andP => Hz Hz1.
  rewrite cardsE -phi_gen (eqP Hz1) phi_mult.
    rewrite phi_prime_k // dvdn_mull //.
    by rewrite expnS muln_subr muln1 (mulnC p) dvdnn.
  by rewrite coprime_sym coprime_expl.
(* Second case *)
have F2: wpartition [set z \in G | #[z] == p ^ l.+1]%N
                    (spconstw p s G) [set x | A x].
  split.
    move=> u v x /=; rewrite !inE; case/andP => Hu Hu0; case/andP => Hv Hv0.
    case/(spconstwP _ _ _ Hu) => u1; case/andP => Hub1 Hu1.
    case/(spconstwP _ _ _ Hv) => u2; case/andP => Hub2 Hu2.
    have F2:= (spconst_uniq Hu1 Hu2).
    move=> x1; apply/spconstwP/spconstwP=> // [] [i]; case/andP => Hi1 Hi2.
      exists (u2 * (u1^-1 * i)); rewrite !groupM ?groupV //=.
      by rewrite (_ : v ^ _ = u ^ i) // !conjgM -F2 conjgK.
    exists (u1 * (u2^-1 * i)); rewrite !groupM ?groupV //=.
    by rewrite (_ : u ^ _ = v ^ i) // !conjgM F2 conjgK.
  apply/coverP; split.
     move => x; rewrite inE; case/andP => Hpx Hx; apply/subsetP => y.
     case/(spconstwP _ _ _ Hpx) => i; case/andP => Hpi.
     rewrite /spconst inE; case/and3P => Hi0 Hi1 Hi2.
     move: (pconst_prem_orderg Hp y).
     rewrite inE (eqP Hi1) orderg_conjg (eqP Hx) => Hi3.
     rewrite orderg_conjg (eqP Hx) in Hi2.
     rewrite /A /f Hsl /= Hi0 /= mulnC mulnA Hi2 /=.
     rewrite /= Hi3 expnS -mulnA mulnC -!mulnA
             /= dvdn_pmul2l //; last by rewrite ltn_0exp Hp0.
     apply/negP => H1.
     have F2: ~~(p %| s) by rewrite -prime_coprime.
     case/negP: F2; apply: (dvdn_trans _ H1).
     exact: dvdn_mull.
  move=> x; rewrite inE=> Hx.
  case: (F1 x) => // t; case/andP => Ht1 Ht2.
  have F2: #[pconst p x] = (p ^ l.+1)%N.
    rewrite orderg_pconst // (eqP Ht2).
    by rewrite logn_gauss // logn_exp.
  have F3: x \in G by case/andP: Hx; case/andP. 
  exists (pconst p x); first by rewrite inE (pconst_group _ F3) F2 eqxx.
  apply /spconstwP; first by rewrite pconst_group.
  exists (1 : gT); rewrite conjg1 group1 /=.
  rewrite /spconst inE F3 eq_refl /= F2.
  rewrite expnS -mulnA -Hsl mulnC.
  by case/andP: Hx; case/andP.
rewrite -cardsE; apply: (card_dvdn_partition F2) => x.
rewrite inE; case/andP=> Hbx Hx.
rewrite (card_spconstw _ _ _ (eqP Hx)) //.
set KRG := (quotient _ _).
set cKRG := #|KRG|.
have F3: #|KRG| = #|'C_G[x] : cyclic x|.
  apply: card_quotient.
  exact: normal_centraliser.
have F4: #|'C_G[x]| = (#|KRG| * #[x])%N.
  rewrite F3 /orderg.
  apply sym_equal; rewrite mulnC; apply: LaGrange => //=.
  exact: cyclic_subset_centraliser.
have F5: cKRG <= k.
  rewrite (eqP Hx) in F4.
  have F5: #|'C_G[x]| %| #|G|.
    by apply: group_dvdn; exact: subset_centraliser.
  rewrite F4 in F5.
  rewrite -ltnS -(eqP Hk).
  have F6: 0 < #|G| by rewrite (eqP Hk).
  move: (dvdn_leq F6 F5) => H1.
  apply: (leq_trans _ H1). 
  rewrite -(muln1 cKRG) /cKRG ltn_pmul2l.
    apply (@leq_trans ((l.+1).+1)) => //.
    apply ltn_expl; exact: prime_gt1.  
  case E1: #|KRG| => //.
  move: (card0_eq E1) => H2.
  move: (H2 1) => //=.
  by rewrite /KRG group1.
have F6b := (dvdn_gcdr cKRG s).
have F6 := (dvdn_gcdl cKRG s).
have F7: [pred z \in KRG | #[z] %| s]
           =i [pred z \in KRG | #[z] %| gcdn cKRG s].
  move => y /=; apply/idP/idP; case/andP => H1b H1; rewrite inE /= H1b /=.
    by apply dvdn_gcd => //; exact: orderg_dvd_g.
  by apply: (dvdn_trans  H1).
rewrite (eq_card F7).
case/dvdnP: (Rec _ (quotient_group _ _) F5 _ F6) => c.
rewrite /f /cKRG => ->.
set r := #|_ : _|.
have F8: #|G| = (r * #|'C_G[x]|)%N.
  apply sym_equal; rewrite mulnC; apply: LaGrange => //.
  by exact: subset_centraliser.
rewrite F4 (eqP Hx) in F8. 
apply: (@dvdn_trans (r * gcdn #|KRG| s)); last first.
  by apply/dvdnP; exists c; rewrite mulnA (mulnC r) !mulnA.
case/dvdnP: (dvdn_gcdl #|KRG| s) => u1 Hu1.
case/dvdnP: (dvdn_gcdr #|KRG| s) => u2 Hu2.
have F9: (gcdn #|KRG| s == 0) = false.
  move: (ltn_0gcd #|KRG| s).
  move: Hn2b; rewrite Hsl; case s => [|s1 _]; first by rewrite muln0.
  by rewrite /= orbT; case gcdn.
have Hu3: coprime u1 u2.
  move: (refl_equal (gcdn #|KRG| s)).
  rewrite -{2}(@muln1 (gcdn _ _)).
  rewrite {1}Hu1 {2}Hu2 (mulnC u1) (mulnC u2) gcdn_mul2l.
  by move/eqP; rewrite eqn_mul2l F9.
rewrite {1}Hu2 dvdn_pmul2r //; last by case: gcdn F9.
rewrite coprime_sym in Hu3.
rewrite -(gauss _ Hu3) -(@dvdn_pmul2r (gcdn #|KRG| s));
  last by case: gcdn F9.
rewrite -Hu2 -mulnA (mulnC r) mulnA -Hu1.
have F10: coprime s (p ^ (l.+1)).
  by rewrite coprime_sym coprime_expl.
rewrite mulnC -(gauss _ F10) mulnC -mulnA -F8.
by rewrite Hk1 Hsl mulnA dvdn_mull.
Qed.

End Frob.

Unset Implicit Arguments.
