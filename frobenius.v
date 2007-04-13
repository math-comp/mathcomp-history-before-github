
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

Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import fintype.
Require Import paths.
Require Import connect.
Require Import groups.
Require Import div.
Require Import zp.
Require Import cyclic.
Require Import normal.
Require Import center.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Section PConstituent.

Variable p s: nat.
Hypothesis primep: prime p.
Hypothesis coprimeps: coprime p s.
Variable elt: finGroupType.
Variable G: group elt.
Open Scope group_scope.


(***********************************************************************)
(*                                                                     *)
(*        p - constituent                                              *)
(*                                                                     *)
(***********************************************************************)

Definition pconst (x: elt) :=
  let u := (p ^ (logn p (orderg x)))%N in
  let v := divn (orderg x) u in
  let (k1,k2) := abezoutn u v in (x ** (v * k2)).
  
Definition prem (x: elt) :=
  let u := (p ^ (logn p (orderg x)))%N in
  let v := divn (orderg x) u in
  let (k1,k2) := abezoutn u v in (x ** (u * k1)).

Lemma pconst_group: forall x, G x -> G (pconst x).
Proof.
move => x y; rewrite /pconst.
case: abezoutn => _ n.
by apply: groupE.
Qed.

Lemma prem_group: forall x, G x -> G (prem x).
Proof.
move => x y; rewrite /prem.
case: abezoutn => n _.
by apply: groupE.
Qed.

Lemma pconst_conjg: forall x y,
  pconst (x ^ y) = (pconst x) ^ y.
Proof.
move => x y; rewrite /pconst.
rewrite orderg_conjg; case: abezoutn => _ n.
by rewrite gexpn_conjg.
Qed.

Lemma prem_conjg: forall x y,
  prem (x ^ y) = (prem x) ^ y.
Proof.
move => x y; rewrite /prem.
rewrite orderg_conjg; case: abezoutn => n _.
by rewrite gexpn_conjg.
Qed.

Lemma pconst_rem: forall x, (pconst x) * (prem x) = x.
Proof.
move => x; rewrite /pconst /prem.
set (l := logn p (orderg x)).
set (t := divn (orderg x) (p ^ l)%N).
have F0: (orderg x = (p ^ l * t)%N).
  case/dvdnP: (dvdn_p_part p (orderg x)); rewrite /p_part -/l => k Hk.
  rewrite /t {2}Hk (mulnC k) divn_mulr ?(mulnC _ k) //.
  by move: (orderg_pos x); rewrite Hk; case: (p ^ l)%N => //;
       rewrite muln0. 
have F1: (coprime (p ^ l)  t).
  case Eq1: l => [| l1].
    by rewrite expn0 /coprime gcdnC gcdnE /= modn1.
  rewrite -prime_coprime_expn // prime_coprime //.
  apply/negP => H1; case/dvdnP: H1 => k1 Hk1. 
  have F1: (dvdn (p ^ (S l)) (orderg x)).
    rewrite F0 Hk1 (mulnC k1) mulnA (mulnC _ p) -expnS.
    by apply dvdn_mulr.
  move: (dvdn_leq_log primep (orderg_pos x) F1).
  by rewrite logn_exp -/l // ltnn.
case Eq1: (orderg x) => [| n1].
  by move: (orderg_pos x); rewrite Eq1.
case: n1 Eq1 => [| n1] Eq1.
   move: (orderg_expn1 x); rewrite Eq1 gexpn1 => F2.
   by case: abezoutn => k1 k2; rewrite (eqP F2) !gexp1n mulg1.
have F2: (1%N < p ^ l * t) by rewrite -F0 Eq1.
move: (abezout_coprime F2 F1); case: abezoutn => k1 k2.
rewrite (mulnC t) -!F0 => H1.
by rewrite gexpn_add (mulnC _ k1) (mulnC t) addnC
          (divn_eq (k1 * p ^ l + k2 * t) (orderg x))
          mulnC -gexpn_add (eqP H1) gexpn1
          -gexpn_mul (eqP (orderg_expn1 x)) gexp1n mul1g.
Qed.

Lemma pconst_remC: forall x, commute (pconst x) (prem x).
Proof.
move => x; rewrite /commute /pconst /prem.
case: abezoutn => k1 k2.
by rewrite !gexpn_add addnC.
Qed.

Lemma pconstC: forall x, commute x (pconst x).
Proof.
by move => x; rewrite /commute -{1 4}(pconst_rem x)
                     {2}(eqP (pconst_remC x)) !mulgA.
Qed.

Lemma premC: forall x, commute x (prem x).
Proof.
by move => x; rewrite /commute -{1 4}(pconst_rem x)
                      {1}(eqP (pconst_remC _)) !mulgA.
Qed.


Lemma orderg_pconst: forall x, 
  orderg (pconst x) = (p ^ (logn p (orderg x)))%N.
Proof.
move => x; move: (pconst_rem x); rewrite /pconst /prem.
set (l := logn p (orderg x)).
set (t := divn (orderg x) (p ^ l)).
have F0: (orderg x = (p ^ l * t)%N).
  case/dvdnP: (dvdn_p_part p (orderg x)); rewrite /p_part -/l => k Hk.
  rewrite /t {2}Hk (mulnC k) divn_mulr ?(mulnC _ k) //.
  by move: (orderg_pos x); rewrite Hk; case: (p ^ l)%N => //;
       rewrite muln0. 
have P1: (0 < t) by
  move: (orderg_pos x); rewrite F0; case t; rewrite ?muln0.
have P2: (0 < p ^ l) by
  move: (orderg_pos x); rewrite F0; case (p ^ l)%N.
case E1: (abezoutn _ _) => [[| k1] [| k2]].
  rewrite !muln0 !gexpn0 mulg1 => H1. 
  move/eqP: (sym_equal F0); rewrite -H1 orderg1 eqn_mul1.
  by case/andP; move/eqP. 
- rewrite muln0 gexpn0 mulg1 => H1. 
  have F1: dvdn t (t * S k2 - 1).
    apply: (@dvdn_trans (orderg x)); first
      by rewrite F0; exact: dvdn_mull.
    rewrite orderg_dvd.
    apply/eqP; apply: (mulg_injl x).
    rewrite -{1}(gexpn1 x) mulg1 gexpn_add leq_add_sub //.
    by move: P1; case t.
  rewrite dvdn_subr in F1; last by exact: dvdn_mulr.
  rewrite H1 F0 -{2}(muln1 (p ^ l)); congr muln.
  by apply/eqP; rewrite -dvdn1.
  move: P1; case: (t) => [| [| s1]] //=.
- rewrite muln0  gexpn0 mul1g => H1. 
  have F1: dvdn (p ^ l) (p ^ l * S k1 - 1).
    apply: (@dvdn_trans (orderg x)); 
      first by rewrite F0; exact: dvdn_mulr.
    rewrite orderg_dvd.
    apply/eqP; apply: (mulg_injl x).
    rewrite -{1}(gexpn1 x) mulg1 gexpn_add leq_add_sub //.
    by move: P2; case (p ^ l)%N.
  rewrite dvdn_subr in F1; last exact: dvdn_mulr.
  rewrite orderg1; apply sym_equal.
  by apply/eqP; rewrite -dvdn1.
  move: P2; case: (p ^ l)%N => [| [| s1]] //=.
have P3: 0 < t * S k2 by move: P1; case t.
have P4: 0 < p ^ l * S k1 by move: P2; case (p ^ l)%N.
have P5: 0 < gcdn t (S k1).
  by rewrite ltn_0gcd orbT.
have P6: 0 < gcdn (p ^ l) (S k2).
  by rewrite ltn_0gcd orbT.
have F1 := (@orderg_gcd _ x _ P3).
rewrite F0 -(mulnC t) gcdn_mul2l divn_pmul2l // in F1.
have F2 := (@orderg_gcd _ x _ P4).
  rewrite F0 gcdn_mul2l divn_pmul2l // in F2.
move => H1; rewrite F1.
have F3:  x ** (orderg (x ** (t * S k2)) *
                   orderg (x ** (p ^ l * S k1))) = 1.
  rewrite -{1}H1 gexpn_add gexpn_mul muln_addl -gexpn_add.
  rewrite -!gexpn_mul (eqP (orderg_expn1 _)) gexp1n mul1g.
  by rewrite gexpn_mul mulnC -gexpn_mul (eqP (orderg_expn1 _))
              gexp1n.
move/eqP: F3; rewrite -orderg_dvd F0 F1 F2.
rewrite -[(_ * divn t _)%N]muln1.
have G1 := dvdn_gcdl (p ^ l) (S k2). 
rewrite dvdn_eq in G1; rewrite -{1}(eqP G1) -mulnA (mulnC _ t).
have G2 := dvdn_gcdl t (S k1). 
rewrite dvdn_eq in G2; rewrite -{1}(eqP G2) !mulnA.
set u := (divn _ _ * _)%N. 
rewrite -mulnA dvdn_pmul2l //.
  rewrite dvdn1 eqn_mul1; case/andP => _ H2.
  by rewrite (eqP H2) divn1.
case E2: u =>//; move/eqP: E2.
rewrite /u eqn_mul0; case/orP => E2.
  rewrite (eqP E2) mul0n in G1.
  by rewrite -(eqP G1) in P2.
rewrite (eqP E2) mul0n in G2.
by rewrite -(eqP G2) in P1.
Qed.

(* there should be a short cut better than this cut-and-paste *)
Lemma orderg_prem: forall x, 
  (orderg (prem x) = divn (orderg x) (p ^ (logn p (orderg x)))).
Proof.
move => x; move: (pconst_rem x); rewrite /pconst /prem.
set (l := logn p (orderg x)).
set (t := divn (orderg x) (p ^ l)).
have F0: (orderg x = (p ^ l * t)%N).
  case/dvdnP: (dvdn_p_part p (orderg x)); rewrite /p_part -/l => k Hk.
  rewrite /t {2}Hk (mulnC k) divn_mulr ?(mulnC _ k) //.
  by move: (orderg_pos x); rewrite Hk; case: (p ^ l)%N => //;
       rewrite muln0. 
have P1: (0 < t) by
  move: (orderg_pos x); rewrite F0; case t; rewrite ?muln0.
have P2: (0 < p ^ l) by
  move: (orderg_pos x); rewrite F0; case (p ^ l)%N.
case E1: (abezoutn _ _) => [[| k1] [| k2]].
  rewrite !muln0 !gexpn0 mulg1 => H1. 
  move/eqP: (sym_equal F0); rewrite -H1 orderg1 eqn_mul1.
  by case/andP => _ H2; rewrite (eqP H2).
- rewrite muln0 gexpn0 mulg1 => H1. 
  have F1: dvdn t (t * S k2 - 1).
    apply: (@dvdn_trans (orderg x)); first
      by rewrite F0; exact: dvdn_mull.
    rewrite orderg_dvd.
    apply/eqP; apply: (mulg_injl x).
    rewrite -{1}(gexpn1 x) mulg1 gexpn_add leq_add_sub //.
    by move: P1; case t.
  rewrite dvdn_subr in F1; last by exact: dvdn_mulr.
  rewrite orderg1; apply sym_equal.
  move: F1; rewrite dvdn1; try by move/eqP.
  by move: P1; case: (t).
- rewrite muln0  gexpn0 mul1g => H1. 
  have F1: dvdn (p ^ l) (p ^ l * S k1 - 1).
    apply: (@dvdn_trans (orderg x)); 
      first by rewrite F0; exact: dvdn_mulr.
    rewrite orderg_dvd.
    apply/eqP; apply: (mulg_injl x).
    rewrite -{1}(gexpn1 x) mulg1 gexpn_add leq_add_sub //.
    by move: P2; case (p ^ l)%N.
  rewrite dvdn_subr in F1; last exact: dvdn_mulr.
  rewrite H1 F0 -{2}(mul1n t); congr muln.
  move: F1; rewrite dvdn1; try by move/eqP.
  by move: P2; case: (p ^ l)%N.
have P3: 0 < t * S k2 by move: P1; case t.
have P4: 0 < p ^ l * S k1 by move: P2; case (p ^ l)%N.
have P5: 0 < gcdn t (S k1).
  by rewrite ltn_0gcd orbT.
have P6: 0 < gcdn (p ^ l) (S k2).
  by rewrite ltn_0gcd orbT.
have F1 := (@orderg_gcd _ x _ P3).
rewrite F0 -(mulnC t) gcdn_mul2l divn_pmul2l // in F1.
have F2 := (@orderg_gcd _ x _ P4).
  rewrite F0 gcdn_mul2l divn_pmul2l // in F2.
move => H1; rewrite F2.
have F3:  x ** (orderg (x ** (t * S k2)) *
                   orderg (x ** (p ^ l * S k1))) = 1.
  rewrite -{1}H1 gexpn_add gexpn_mul muln_addl -gexpn_add.
  rewrite -!gexpn_mul (eqP (orderg_expn1 _)) gexp1n mul1g.
  by rewrite gexpn_mul mulnC -gexpn_mul (eqP (orderg_expn1 _))
              gexp1n.
move/eqP: F3; rewrite -orderg_dvd F0 F1 F2.
rewrite -[(_ * divn t _)%N]muln1.
have G1 := dvdn_gcdl (p ^ l) (S k2).
rewrite dvdn_eq in G1; rewrite -{1}(eqP G1) -mulnA (mulnC _ t).
have G2 := dvdn_gcdl t (S k1). 
rewrite dvdn_eq in G2; rewrite -{1}(eqP G2) !mulnA.
set u := (divn _ _ * _)%N. 
rewrite -mulnA dvdn_pmul2l //.
  rewrite dvdn1 eqn_mul1; case/andP => H2 _.
  by rewrite (eqP H2) divn1.
case E2: u =>//; move/eqP: E2.
rewrite /u eqn_mul0; case/orP => E2.
  rewrite (eqP E2) mul0n in G1.
  by rewrite -(eqP G1) in P2.
rewrite (eqP E2) mul0n in G2.
by rewrite -(eqP G2) in P1.
Qed.

Lemma pconst_coprime: forall x, 
 coprime (orderg (pconst x)) (orderg (prem x)).
Proof.
move => x.
rewrite orderg_pconst orderg_prem.
case E1: (logn _ _) => [| n].
  rewrite expn0 divn1 /coprime gcdnC //=.
rewrite -prime_coprime_expn // -E1.
case (@p_part_coprime p (orderg x)) => //; first exact: orderg_pos.
move => xx Hxx Hr; rewrite {1}Hr divn_mull // ltn_0exp.
by case: p primep.
Qed.

Lemma pconst_prem_orderg: forall x, 
 orderg x = (orderg (pconst x) * orderg (prem x))%N.
Proof.
move => x; rewrite -{1}(pconst_rem x).
apply: orderg_mul; first exact: pconst_remC.
exact: pconst_coprime.
Qed.

Definition spconst x := 
  {y,  G y && ((pconst y == x) && (dvdn (orderg y) (orderg x * s)))}.
  
Lemma spconst_uniq: forall x1 x2 y,
  spconst x1 y -> spconst x2 y -> x1 = x2.
Proof.
move => x1 x2 y; rewrite /spconst !s2f.
case/and3P => _ H1 _; case/and3P => _ H2 _.
by rewrite -(eqP H1); apply/eqP.
Qed.

Lemma spconst_conjgs: forall a b, G b ->
   spconst (a ^ b) = (spconst a) :^ b.
Proof.
move => a b Hb; apply/isetP => x; apply/idP/idP.
  rewrite /spconst !s2f; case/and3P => H1 H2 H3.
  apply/and3P; split.
  - by repeat apply: groupM; gsimpl => //; exact: groupVr.
  - rewrite pconst_conjg (eqP H2) conjg_conj; gsimpl;
    by rewrite conjg1.
  - by move: H3; rewrite !orderg_conjg.
rewrite /spconst !s2f; case/and3P => H1 H2 H3.
apply/and3P; split.
- rewrite -(conjgKv b x); repeat apply: groupM => //.
  by exact: groupVr.
- by rewrite -(eqP H2) pconst_conjg conjg_conj mulVg conjg1.
by move: H3; rewrite !orderg_conjg.
Qed.

Lemma spconst_card: forall a b, G b ->
  card (spconst (a ^ b)) = card (spconst a).
Proof.
move => a b Hb; rewrite -(card_iimage (conjg_inj b) (spconst a)).
apply eq_card => x.
by rewrite spconst_conjgs // sconjg_iimage.
Qed.

Lemma pconst_subset_centralizer:  forall y,
  subset (spconst y) (centraliser G y).
Proof.
move => y; rewrite /spconst; apply/subsetP => x; rewrite !s2f.
case/and3P => Hx1 Hx2 Hx3.
rewrite /centraliser; repeat (apply/andP; split) => //.
rewrite -(gexpn1 x) -(eqP Hx2) /pconst.
by case: abezoutn => _ n; rewrite /commute !gexpn_add addnC.
Qed.

Lemma pconst_mul_in: forall y z l, 
  G y -> G z -> commute y z ->
  orderg y = (p ^ (S l))%N -> dvdn (orderg z) s ->
  spconst y (y * z).
Proof.
move => y z l Hy Hz H H1 H2.
have F0: coprime (orderg y) (orderg z).
  rewrite H1 -prime_coprime_expn //.
  case/dvdnP: H2 coprimeps => k ->.
  by rewrite coprime_mulr; case/andP.
have F1: (orderg (y * z) = (p ^ (S l) * (orderg z))%N).
  by rewrite -H1; apply: orderg_mul.
rewrite s2f; apply/and3P; split; last
  by rewrite orderg_mul // dvdn_pmul2l // orderg_pos.
  exact: groupM.
rewrite /spconst /pconst F1.
rewrite -F1.
have F2:  1 < orderg (y * z).
  rewrite F1.
  apply: (@leq_trans (S (orderg z))); first exact: orderg_pos. 
  rewrite -{1}(mul1n (orderg z)) ltn_mul2r orderg_pos andTb.
  by rewrite -(expn0 p) ltn_exp2l // prime_gt1.
rewrite {1 3 5}F1 logn_mul // ?orderg_pos ?logn_exp //; last
  by rewrite ?ltn_0exp; case: p primep.
have FF: (dvdn p (orderg z)) = false.
  apply/negP; apply/negP.
  by rewrite -prime_coprime // (prime_coprime_expn l) // -H1.
rewrite lognE primep orderg_pos FF [S l]lock /= addn0;  unlock.
rewrite -H1 F1 -H1 divn_mulr ?orderg_pos //.
have F3: (1 < orderg y * orderg z) by rewrite H1 -F1.
move: (abezout_coprime F3 F0).
case: abezoutn => k1 k2 H3; apply/eqP.
rewrite gexpnC // -(gexpn_mul z) (eqP (orderg_expn1 _))
        gexp1n mulg1 mulnC.
rewrite -(mul1g (gexpn _ _)) -(gexp1n elt k1)
        -(eqP (orderg_expn1 y)) gexpn_mul mulnC
        gexpn_add.
rewrite [_ + _](@divn_eq _ (orderg z * orderg y)) (eqP H3).
by rewrite -gexpn_add  !mulnA (mulnC _ (orderg y))
           -gexpn_mul (eqP (orderg_expn1 _)) gexp1n gexpn1
           mul1g.
Qed.

Lemma pconst_image: forall y l, G y ->
  orderg y = (p ^ (S l))%N -> coprime (orderg y) s -> 
  image prem (spconst y) =1
        (fun z => centraliser G y z && dvdn (orderg z) s). 
Proof.
move => y l Hy0 Hy Cy x1; apply/idP/idP => H1.
  case: (Hdiinv H1) => y1.
  rewrite s2f; case/and4P => HH1 HH2 HH3 HH4.
  rewrite  -(eqP HH3) (eqP HH1); apply/andP; split.
    rewrite /centraliser !s2f prem_group //.
    by exact: pconst_remC.
  rewrite -(dvdn_pmul2r (orderg_pos (pconst y1))).
  rewrite mulnC -pconst_prem_orderg.
  by rewrite (eqP HH3) mulnC.
case/andP: H1 => H1 H2.
have F0: coprime (orderg y) (orderg x1).
  case/dvdnP: H2 => k Hk; rewrite Hk coprime_mulr in Cy.
  by case/andP: Cy.
have F1: commute y x1.
 by  rewrite !s2f in H1; case/andP: H1.
have F2: coprime p (orderg x1).
  by rewrite (prime_coprime_expn l) // -Hy. 
have F3: G x1.
 by  rewrite !s2f in H1; case/andP: H1.
move: (pconst_mul_in Hy0 F3 F1 Hy H2); rewrite s2f.
case/and3P => H3 H4 H5.
replace x1 with (prem (y * x1)).
  apply: image_f_imp.
  by rewrite s2f H3 H4 H5.
apply: (mulg_injl y).
rewrite -{1}(eqP H4); exact: pconst_rem.
Qed.

Lemma pconst_card: forall y l, G y ->
  orderg y = (p ^ (S l))%N ->  
  card (spconst y) =
  card (fun z => centraliser G y z && dvdn (orderg z) s). 
Proof.
move => y l Hy H.
have F0: coprime (orderg y) s.
  by rewrite H -prime_coprime_expn.
apply: etrans (eq_card (pconst_image Hy H F0)).
apply: sym_equal; apply: card_dimage.
move => y1 y2; rewrite !s2f;
  case/and3P => H1 H2 H3; case/and3P => H4 H5 H6 H7.
by rewrite -(pconst_rem y1) (eqP H2) -(eqP H5) H7 pconst_rem.
Qed.

Let KRG (y: elt) := (coset_groupType (group_cyclic y)).

Lemma pconst_card_KRG: forall y l, G y -> 
  orderg y = (p ^ (S l))%N ->  
  card (spconst y) =
  card (fun z: (KRG y) => (centraliser G y/ cyclic y) z
                          && dvdn (orderg z) s).
Proof.
move => y l Hy H.
rewrite (pconst_card Hy H).
apply: (KB_card_image Hy primep H).
by rewrite H -prime_coprime_expn.
Qed.


Definition spconstw y := 
  setnU (rcosets (group_centraliser G y) G)
        (fun x => spconst (y ^ (repr x))).

Lemma spconstwP: forall x y, G y ->
  reflect (exists i, G i && spconst (y ^ i) x)
          (spconstw y x).
Proof.
move => x y Hy; apply: (iffP idP).
 case/setnUP => i; case/andP => Hi1 Hi2.
 exists (repr i); rewrite Hi2 andbT.
 case/iimageP: Hi1 => x1 Hx1 Hx2.
 move: (@repr_rcosetP elt (group_centraliser G y) x1).
 rewrite -Hx2.
 case => x2; rewrite s2f; case/andP => Hx3 _.
 exact: groupM.
case => i; case/andP => Hi1 Hi2.
set r := (centraliser G y) :* i.
have F1: (rcosets (group_centraliser G y) G) r.
  by apply/iimageP; exists i.
apply/setnUP; exists r; rewrite F1 //=.
rewrite /is_true -Hi2; congr s2s; congr spconst.
rewrite /conjg.
replace ((repr r)^-1 * y * (repr r)) with 
   (i^-1 * (((repr r) * i^-1)^-1 * y * ((repr r) *  i^-1)) * i); last gsimpl.
have F2: rcoset (centraliser G y) i (repr r).
 case/iimageP: F1 => x1 Hx1 Hx2.
 move: (@repr_rcosetP elt (group_centraliser G y) x1).
 rewrite -/r -Hx2.
 case => x2 Hx3; rewrite Hx2 s2f; gsimpl.
rewrite /rcoset /centraliser !s2f in F2; case/andP: F2 => _ F2.
rewrite -(mulgA _ y) (eqP F2); gsimpl.
Qed.

Lemma card_spconstw: forall y l, G y -> orderg y = (p ^ (S l))%N ->  
  card (spconstw y) = 
   ((indexg (group_centraliser G y) G) * 
   card (fun z: (KRG y) => 
          (centraliser G y/ cyclic y) z && dvdn (orderg z) s))%N.
Proof.
move => y l Hy Oy.
rewrite /spconstw (@card_setnU_id _ _ _ _ (card (spconst y))) //.
    congr muln => //.
    exact: (pconst_card_KRG _ Oy).
  move => u v x Hu Hv /= Hsu Hsv.
  case/iimageP: Hu => i1 /= Hi1 Ei1.
  move: (@repr_rcosetP elt (group_centraliser G y) i1) Hsu.
  rewrite -Ei1; case => /= j1 Hj1 Hsu; rewrite Ei1.
  case/iimageP: Hv => i2 /= Hi2 Ei2.
  move: (@repr_rcosetP elt (group_centraliser G y) i2) Hsv.
  rewrite -Ei2; case => /= j2 Hj2 Hsv; rewrite Ei2.
  apply: rcoset_trans1 => /=.
  rewrite s2f.
  rewrite /centraliser !s2f; rewrite groupM ?groupV //=.
  apply/conjg_fpP.
  move: (spconst_uniq Hsu Hsv).
  rewrite /conjg_fp -!conjg_conj .
  have F1: conjg_fp j2 y.
    apply/conjg_fpP.
    by move: Hj2; rewrite !s2f; case/andP.
  rewrite (eqP F1) => <-; rewrite conjgK.
  apply/conjg_fpP.
  by move: Hj1; rewrite !s2f; case/andP.
move => x Hx.
apply: spconst_card.
case/iimageP: Hx => i2 /= Hi2 Ei2.
move: (@repr_rcosetP elt (group_centraliser G y) i2).
rewrite -Ei2; case => y1 /=; rewrite !s2f; case/andP => Hy1 _.
by exact: groupM.
Qed.

End PConstituent.

Section Frob.

Theorem frobenius: forall elt (G: group elt) n,
  dvdn n (card G) ->
  dvdn n  (card (fun z => G z && dvdn (orderg z) n)).
pose f elt (H: group elt) n := (fun z => H z && dvdn (orderg z) n).
change 
 (forall elt (G: group elt) n, dvdn n (card G) -> dvdn n  (card (f elt G n))).
move => elt G.
move: {G}(card G) {-2}G (leqnn (card G)) => n.
elim: n elt.
  by move => elt H; move: (pos_card_group H); case: (card H).
move => k Rec elt G; rewrite leq_eqVlt; case/orP => Hk n Hn;
    last apply Rec => //.
have Hn1: n <= card G by
  apply: dvdn_leq. 
move: Hn; rewrite -(@leq_sub_sub n (card G)) //.
set (e := card G - n); elim: e {-2}e (leqnn e).
  case => // _ _; rewrite subn0.
  apply/dvdnP; exists 1%N; rewrite mul1n.
  apply: eq_card => x.
  rewrite /f /orderg; case E1: (G x) => //=.
  rewrite group_dvdn //.
  apply/subsetP => i; case/cyclicP => m Hm.
  by rewrite -(eqP Hm) groupE.
move => n1 Hrec e.
rewrite leq_eqVlt; case/orP => H H1; last apply Hrec => //.
move: H1; rewrite (eqP H).
set (n2 := card G - S n1).
have Hn2: n2 < card G 
 by rewrite /n2 (eqP Hk) ltnS subSS leq_subr.
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
set (p := pdiv k1).
have Hp := prime_pdiv HHk; rewrite -/p in Hp.
have Hp0: 0 < p by case: p Hp.
have Hp1: dvdn (n2 * p) (card G).
  by rewrite mulnC Hk1 dvdn_pmul2r ?dvdn_pdiv.
have Hp2: n2 * p <= card G by apply dvdn_leq => //; 
                              rewrite (eqP Hk).
have D1: dvdn n2 (card (f elt G (n2 * p)%N)).
  apply: (@dvdn_trans (n2 * p)) => //.
    by rewrite dvdn_mulr ?dvdnn.
  rewrite -(@leq_sub_sub (n2 * p) (card G)) //.
  apply Hrec; last by rewrite leq_sub_sub.
  rewrite leq_sub_add.
  rewrite -(@leq_add_sub (S n1) (card G)).
    rewrite -ltnS -/n2 -[S(_ + n1)]addnS addnC ltn_add2r 
            -{1}(mul1n n2) mulnC ltn_pmul2l //.
    exact: prime_gt1.
  apply ltn_trans with (S n1); first exact: ltnSn.
  by rewrite -ltn_0sub -/n2; case: (n2) Hn2b.
rewrite -(@dvdn_addr (card (setI (f elt G (n2 * p)%N) (setC (f elt G n2))))).
  case/dvdnP: D1 => u Hu; apply/dvdnP; exists u; rewrite -Hu.
  rewrite -(cardIC (f elt G n2) (f elt G (n2 * p)%N)) addnC; congr addn.
  apply: eq_card => x; rewrite /setI; case Eq1: (f elt G n2 x);
    last by rewrite andbF. 
  rewrite andbT /f; apply sym_equal; apply/idP.
  case/andP: (idP Eq1) => -> HH /=.
  by apply: (dvdn_trans HH); rewrite dvdn_mulr ?dvdnn.
case (p_part_coprime Hp Hn2b0); rewrite /p_part => s.
rewrite mulnC; set l := logn p n2 => Hsl1 Hsl.
have P1: 0 < p ^ (S l) by rewrite ltn_0exp Hp0.
set A := (setI _ _).
have F1: forall z, A z -> exists u,
     coprime p u &&  (orderg z == u * p ^ (S l))%N.
  move => z; case/andP; rewrite /f /setC; case/andP => H1 Hb1.
  rewrite H1 /=; move/negP => H2. 
  case/dvdnP: Hb1 => u Hu.
  case E1: (dvdn p u).
    case/dvdnP: (idP E1) => u1 Hu1.
    case H2; apply/dvdnP; exists u1.
    apply/eqP; rewrite -(@eqn_pmul2r p) //.
    by rewrite Hu Hu1 -mulnA (mulnC p) mulnA eq_refl.
  have E2: dvdn (p ^ (S l)) (orderg z).
    rewrite -(@gauss _ u); first by
      rewrite -Hu Hsl expnS (mulnC _ p) mulnA dvdn_mulr ?dvdnn.
    by rewrite -prime_coprime_expn // prime_coprime // E1.  
  case/dvdnP: E2 => u1 Hu1.
  exists u1; rewrite Hu1 eq_refl andbT.
  have E2: (s == u * u1)%N.
    rewrite  -(@eqn_pmul2r (p ^ (S l))) //.
    by rewrite -mulnA -Hu1 -Hu (mulnC _ p) Hsl mulnA -expnS mulnC.
  rewrite (eqP E2) coprime_mulr in Hsl1.
  by case/andP: Hsl1.
rewrite {1}Hsl gauss_inv; last by
  case: (l) => [| u];
    last rewrite -prime_coprime_expn //;
  rewrite expn0 /coprime -dvdn1 dvdn_gcdl.
apply/andP;split.
(* First case *)
  apply: (@dvdn_trans  ((p ^ l) * (p - 1))%N);
    first by rewrite dvdn_mulr.
  set (e1 := fun x => (generator (cyclic x)): set elt).
  have F2: (wpartition A e1 A).
    split.
      move => u v x Hu Hv Hu1 Hu2 y.
      case/andP: Hu1 => Hu1 Hub1.
      case/andP: Hu2 => Hu2 Hub2.
      apply/idP/idP; 
      move/andP => [HH1 HH2]; apply/andP; split.
      - by apply: (subset_trans HH1); apply: (subset_trans Hub1).
      - by apply: (subset_trans Hub2); apply: (subset_trans Hu1).
      - by apply: (subset_trans HH1); apply: (subset_trans Hub2).
      by apply: (subset_trans Hub1); apply: (subset_trans Hu2).
    rewrite /cover; apply/andP; split; apply/subsetP => x.
      move/setnUP; case => y;  case/andP.
      case/andP; case/andP => Hy Hy1.
      rewrite /f /setC Hy /= => Hy2 Hy3.
      have F2: G x.
        apply: (subsetP (cyclic_h Hy)).
        case/andP: Hy3 => Hy4 _.
        by apply: (subsetP Hy4 ); rewrite cyclicnn.
      rewrite /A /f /setI /setC F2 !andTb.
      by rewrite -(generator_orderg Hy3) Hy1.
    move => Hx; apply/setnUP; exists x; rewrite Hx /=. 
    by rewrite /e1 generator_cyclic.
    apply: (card_dvdn_partition F2) => x Hx.
    case: (F1 _ Hx) => z; case/andP => Hz Hz1.
    rewrite /e1 -phi_gen (eqP Hz1) phi_mult.
      rewrite phi_prime_k // dvdn_mull //.
      by rewrite expnS muln_subr muln1 (mulnC p) dvdnn.
    by rewrite coprime_sym -prime_coprime_expn.
(* Second case *)
have F2: wpartition (fun z => G z && (orderg z == p ^ (S l))%N)
                    (spconstw p s G) A.
  split.
    move => u v x /=; case/andP => Hu Hu0; case/andP => Hv Hv0.
    case/(spconstwP _ _ _ Hu) => u1; case/andP => Hub1 Hu1.
    case/(spconstwP _ _ _ Hv) => u2; case/andP => Hub2 Hu2.
    have F2:= (spconst_uniq Hu1 Hu2).
    move => x1; apply/spconstwP/spconstwP => //;
      case => i; case/andP => Hi1 Hi2.
      exists (u2 * (u1^-1 * i))%G.
      rewrite !groupM ?groupV //=.
      rewrite /is_true -Hi2; congr s2s; congr spconst.
      by rewrite -conjg_conj -F2 conjg_conj; congr conjg; gsimpl.
    exists (u1 * (u2^-1 * i))%G.
    rewrite !groupM ?groupV //=.
    rewrite /is_true -Hi2; congr s2s; congr spconst.
    by rewrite -conjg_conj F2 conjg_conj; congr conjg; gsimpl.
  apply/coverP; split.
     move => x; case/andP => Hpx Hx; apply/subsetP => y.
     case/(spconstwP _ _ _ Hpx) => i; case/andP => Hpi.
     rewrite /spconst s2f; case/and3P => Hi0 Hi1 Hi2.
     move: (pconst_prem_orderg Hp y).
     rewrite (eqP Hi1) orderg_conjg (eqP Hx) => Hi3.
     rewrite orderg_conjg (eqP Hx) in Hi2.
     rewrite /A /f /setI Hsl Hi0 /= mulnC mulnA Hi2 /=.
     rewrite /setC Hi3 expnS -mulnA mulnC -!mulnA Hi0  
             /= dvdn_pmul2l //; last by rewrite ltn_0exp Hp0.
     apply/negP => H1.
     have F2: ~~(dvdn p s) by rewrite -prime_coprime.
     case/negP: F2; apply: (dvdn_trans _ H1).
     exact: dvdn_mull.
  move => x Hx.
  case: (F1 x) =>  // t; case/andP => Ht1 Ht2.
  have F2: (orderg (pconst p x) = p ^ S l)%N.
    rewrite orderg_pconst // (eqP Ht2).
    by rewrite logn_gauss // logn_exp.
  have F3: G x by case/andP: Hx; case/andP. 
  exists (pconst p x); rewrite (pconst_group _ F3) F2 eq_refl /=.
  apply /spconstwP.
    by rewrite (pconst_group _ F3).
  exists (1: elt); rewrite conjg1 /id. 
  rewrite group1 /=.
  rewrite /spconst s2f F3 eq_refl /= F2.
  rewrite expnS -mulnA -Hsl mulnC.
  by case/andP: Hx; case/andP.
apply: (card_dvdn_partition F2) => x; case/andP => Hbx Hx.
rewrite (card_spconstw _ _ _ (eqP Hx)) //.
set KRG := (quotient _ _).
set cKRG := card KRG.
have F3: card KRG = indexg (group_cyclic x) (centraliser G x).
  apply: quotient_indexg; first exact: cyclic_subset_centraliser.
  exact: normal_centraliser.
have F4: card (centraliser G x) = (card KRG * orderg x)%N.
  rewrite F3 /orderg.
  apply sym_equal; rewrite mulnC; apply: LaGrange => //=.
    rewrite /subgroup; apply: cyclic_subset_centraliser => //.
have F5: cKRG <= k.
  rewrite (eqP Hx) in F4.
  have F5: dvdn (card (centraliser G x)) (card G).
   by apply: group_dvdn; exact: subset_centraliser.
  rewrite F4 in F5.
  rewrite -ltnS -(eqP Hk).
  have F6: 0 < card G by rewrite (eqP Hk).
  move: (dvdn_leq F6 F5) => H1.
  apply: (leq_trans _ H1). 
  rewrite -(muln1 cKRG) /cKRG ltn_pmul2l.
    apply (@leq_trans (S (S l))) => //.
    apply ltn_expl; exact: prime_gt1.  
  case E1: (card KRG) => //.
    move: (card0_eq E1) => H2.
    move: (H2 1) => //=.
    by rewrite /KRG group1.
have F6b:= (dvdn_gcdr cKRG s).
have F6:= (dvdn_gcdl cKRG s).
have F7: (fun z => KRG z  && (dvdn (orderg z) s)) =1
         (fun z => KRG z &&  (dvdn (orderg z) (gcdn cKRG s))).
  move => y /=; apply/idP/idP; case/andP => H1b H1; rewrite H1b /=.
    by apply dvdn_gcd => //; exact: orderg_dvd_g.
  by apply: (dvdn_trans  H1).
rewrite (eq_card F7).
case/dvdnP: (Rec _ (group_quotient _ _) F5 _ F6) => c.
rewrite /f /cKRG => ->.
set r := (indexg _ _).
have F8: card G = (r *  card (centraliser G x))%N.
  apply sym_equal; rewrite mulnC; apply: LaGrange => //.
  by exact: subset_centraliser.
rewrite F4 (eqP Hx) in F8. 
apply: (@dvdn_trans (r * gcdn (card KRG) s)); last
  by apply/dvdnP; exists c; rewrite mulnA (mulnC r) !mulnA.
case/dvdnP: (dvdn_gcdl (card KRG) s) => u1 Hu1.
case/dvdnP: (dvdn_gcdr (card KRG) s) => u2 Hu2.
have F9: (gcdn (card KRG) s == 0) = false.
  move: (ltn_0gcd (card KRG) s).
  move: Hn2b; rewrite Hsl; case s => [|s1 _]; first by rewrite muln0.
  by rewrite /= orbT; case gcdn.
have Hu3: coprime u1 u2.
  move: (refl_equal (gcdn (card KRG) s)).
  rewrite -{2}(@muln1 (gcdn _ _)).
  rewrite {1}Hu1 {2}Hu2 (mulnC u1) (mulnC u2) gcdn_mul2l.
  by move/eqP; rewrite eqn_mul2l F9.
rewrite {1}Hu2 dvdn_pmul2r //; last by case: gcdn F9.
rewrite coprime_sym in Hu3.
rewrite -(gauss _ Hu3) -(@dvdn_pmul2r (gcdn (card KRG) s));
  last by case: gcdn F9.
rewrite -Hu2 -mulnA (mulnC r) mulnA -Hu1.
have F10: coprime s (p ^ (S l)).
  by rewrite coprime_sym -prime_coprime_expn.
rewrite mulnC -(gauss _ F10) mulnC -mulnA -F8.
by rewrite Hk1 Hsl mulnA dvdn_mull.
Qed.

End Frob.

Unset Implicit Arguments.
