
(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Order of an element                                                *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)

Require Import baux.
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
Variable G: finGroup.

Open Scope group_scope.


(***********************************************************************)
(*                                                                     *)
(*        p - constituent                                                     *)
(*                                                                     *)
(***********************************************************************)

Definition pconst (x: G) :=
  let u := (p ^ (dlogn p (orderg x)))%N in
  let v := edivn (orderg x) u in
  let (k1,k2) := abezoutn u v in (x ^ (v * k2)).
  
Definition prem (x: G) :=
  let u := (p ^ (dlogn p (orderg x)))%N in
  let v := edivn (orderg x) u in
  let (k1,k2) := abezoutn u v in (x ^ (u * k1)).

Lemma pconst_conjg: forall x y,
  pconst (x ^g y) = (pconst x) ^g y.
Proof.
move => x y; rewrite /pconst.
rewrite orderg_conjg; case: abezoutn => _ n.
by rewrite gexpn_conjg.
Qed.

Lemma prem_conjg: forall x y,
  prem (x ^g y) = (prem x) ^g y.
Proof.
move => x y; rewrite /prem.
rewrite orderg_conjg; case: abezoutn => n _.
by rewrite gexpn_conjg.
Qed.

Lemma pconst_rem: forall (x:G), (pconst x) * (prem x) = x.
Proof.
move => x; rewrite /pconst /prem.
set (l := dlogn p (orderg x)).
set (t := edivn (orderg x) (p ^ l)).
have F0: (orderg x = (p ^ l * t)%N).
  case/divnP: (dlogn_l p (orderg x)); rewrite -/l => k Hk.
  rewrite /t {2}Hk (mulnC k) edivn_mull ?(mulnC _ k) //.
  by move: (orderg_pos x); rewrite Hk; case: (p ^ l)%N => //;
       rewrite muln0. 
have F1: (coprime (p ^ l)  t).
  case Eq1: l => [| l1].
    by rewrite expn0 /coprime gcdn1.
  rewrite -prime_coprime_k //.
  apply/negP => H1; case/divnP: H1 => k1 Hk1. 
  have F1: (divn (p ^ (S l)) (orderg x)).
    rewrite F0 Hk1 (mulnC k1) mulnA (mulnC _ p) -expnS.
    by apply divnMr.
  rewrite /l dlogn_r in F1; last exact: prime_leq_2.
  by move: (orderg_pos x); rewrite (eqP F1).
case Eq1: (orderg x) => [| n1].
  by move: (orderg_pos x); rewrite Eq1.
case: n1 Eq1 => [| n1] Eq1.
   move: (orderg_expn1 x); rewrite Eq1 gexpn1 => F2.
   by case: abezoutn => k1 k2; rewrite (eqP F2) !gexp1n mulg1.
have F2: (1%N < p ^ l * t) by rewrite -F0 Eq1.
move: (abezout_coprime _ _ F2 F1); case: abezoutn => k1 k2.
rewrite (mulnC t) -!F0 => H1.
by rewrite gexpn_add (mulnC _ k1) (mulnC t) addnC
          (edivn_modn (k1 * p ^ l + k2 * t) (orderg x)) (eqP H1)
          mulnC -gexpn_add gexpn1 -gexpn_mul (eqP (orderg_expn1 x))
          gexp1n mul1g.
Qed.

Lemma pconst_remC: forall (x:G), commg (pconst x) (prem x).
Proof.
move => x; rewrite /commg /pconst /prem.
case: abezoutn => k1 k2.
by rewrite !gexpn_add addnC.
Qed.

Lemma pconstC: forall (x:G), commg x (pconst x).
Proof.
by move => x; rewrite /commg -{1 4}(pconst_rem x) 
                     {2}pconst_remC !mulgA.
Qed.

Lemma premC: forall (x:G), commg x (prem x).
Proof.
by move => x; rewrite /commg -{1 4}(pconst_rem x)
                      {1}pconst_remC !mulgA.
Qed.


Lemma orderg_pconst: forall (x:G), 
  orderg (pconst x) = (p ^ (dlogn p (orderg x)))%N.
Proof.
move => x; move: (pconst_rem x); rewrite /pconst /prem.
set (l := dlogn p (orderg x)).
set (t := edivn (orderg x) (p ^ l)).
have F0: (orderg x = (p ^ l * t)%N).
  case/divnP: (dlogn_l p (orderg x)); rewrite -/l => k Hk.
  rewrite /t {2}Hk (mulnC k) edivn_mull ?(mulnC _ k) //.
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
  have F1: divn t (t * S k2 - 1).
    apply: (divntrans _ (orderg x)); 
      first by rewrite F0; exact: divnMl.
    rewrite orderg_divn.
    apply/eqP; apply: (mulg_injl x).
    rewrite -{1}(gexpn1 x) mulg1 gexpn_add leq_add_sub //.
    by move: P1; case t.
  rewrite divn_minus_r in F1; last exact: divnMr.
  rewrite H1 F0 -{2}(muln1 (p ^ l)); congr muln.
  case/orP: F1 => H2; last by apply/eqP; rewrite -divn1.
  move: P1 H2; case: (t) => [| [| s1]] //=.
  by case k2.
- rewrite muln0  gexpn0 mul1g => H1. 
  have F1: divn (p ^ l) (p ^ l * S k1 - 1).
    apply: (divntrans _ (orderg x)); 
      first by rewrite F0; exact: divnMr.
    rewrite orderg_divn.
    apply/eqP; apply: (mulg_injl x).
    rewrite -{1}(gexpn1 x) mulg1 gexpn_add leq_add_sub //.
    by move: P2; case (p ^ l)%N.
  rewrite divn_minus_r in F1; last exact: divnMr.
  rewrite orderg1; apply sym_equal.
  case/orP: F1 => H2; last by apply/eqP; rewrite -divn1.
  move: P2 H2; case: (p ^ l)%N => [| [| s1]] //=.
  by case k1.
have P3: 0 < t * S k2 by move: P1; case t.
have P4: 0 < p ^ l * S k1 by move: P2; case (p ^ l)%N.
have P5: 0 < gcdn t (S k1).
  by move: (gcdn_0_inv t (S k1)); rewrite andbF;
     case: gcdn.
have P6: 0 < gcdn (p ^ l) (S k2).
  by move: (gcdn_0_inv (p ^ l) (S k2)); rewrite andbF;
     case: gcdn.
have F1 := (@orderg_gcd _ x _ P3).
rewrite F0 -(mulnC t) gcdn_mul2l edivn_mul2r in F1; last
  by rewrite lt_mul0 P1 P6.
have F2 := (@orderg_gcd _ x _ P4).
  rewrite F0 gcdn_mul2l edivn_mul2r in F2; last 
  by rewrite lt_mul0 P2 P5.
move => H1; rewrite F1.
have F3:  x ^ (orderg (x ^ (t * S k2)) *
                   orderg (x ^ (p ^ l * S k1))) = 1.
  rewrite -{1}H1 gexpn_add gexpn_mul muln_addl -gexpn_add.
  rewrite -!gexpn_mul (eqP (orderg_expn1 _)) gexp1n mul1g.
  by rewrite gexpn_mul mulnC -gexpn_mul (eqP (orderg_expn1 _))
              gexp1n.
move/eqP: F3; rewrite -orderg_divn F0 F1 F2.
rewrite -[(_ * edivn t _)%N]muln1.
have G1 := gcdn_divl (p ^ l) (S k2). 
rewrite divn_edivn in G1; rewrite -{1}(eqP G1) -mulnA (mulnC _ t).
have G2 := gcdn_divl t (S k1). 
rewrite divn_edivn in G2; rewrite -{1}(eqP G2) !mulnA.
set u := (edivn _ _ * _)%N. 
rewrite -mulnA divn_mul2r.
case E2: (u == 0).
  rewrite /u eqn_mul0 in E2; case/orP: E2 => H2.
    rewrite (eqP H2) mul0n in G1.
    by rewrite -(eqP G1) in P2.
  rewrite (eqP H2) mul0n in G2.
  by rewrite -(eqP G2) in P1.
rewrite orFb divn1.
rewrite eqn_mul1; case/andP => _ H2.
by rewrite (eqP H2) edivn1.
Qed.

(* there should be a short cut better than this cut-and-paste *)
Lemma orderg_prem: forall (x:G), 
  (orderg (prem x) = edivn (orderg x) (p ^ (dlogn p (orderg x)))).
Proof.
move => x; move: (pconst_rem x); rewrite /pconst /prem.
set (l := dlogn p (orderg x)).
set (t := edivn (orderg x) (p ^ l)).
have F0: (orderg x = (p ^ l * t)%N).
  case/divnP: (dlogn_l p (orderg x)); rewrite -/l => k Hk.
  rewrite /t {2}Hk (mulnC k) edivn_mull ?(mulnC _ k) //.
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
  have F1: divn t (t * S k2 - 1).
    apply: (divntrans _ (orderg x)); 
      first by rewrite F0; exact: divnMl.
    rewrite orderg_divn.
    apply/eqP; apply: (mulg_injl x).
    rewrite -{1}(gexpn1 x) mulg1 gexpn_add leq_add_sub //.
    by move: P1; case t.
  rewrite divn_minus_r in F1; last exact: divnMr.
  rewrite orderg1; apply sym_equal.
  case/orP: F1 => H2; last by apply/eqP; rewrite -divn1.
  move: P1 H2; case: (t) => [| [| t1]] //=.
  by case k2.
- rewrite muln0  gexpn0 mul1g => H1. 
  have F1: divn (p ^ l) (p ^ l * S k1 - 1).
    apply: (divntrans _ (orderg x)); 
      first by rewrite F0; exact: divnMr.
    rewrite orderg_divn.
    apply/eqP; apply: (mulg_injl x).
    rewrite -{1}(gexpn1 x) mulg1 gexpn_add leq_add_sub //.
    by move: P2; case (p ^ l)%N.
  rewrite divn_minus_r in F1; last exact: divnMr.
  rewrite H1 F0 -{2}(mul1n t); congr muln.
  case/orP: F1 => H2; last by apply/eqP; rewrite -divn1.
  move: P2 H2; case: (p ^ l)%N => [| [| s1]] //=.
  by case k1.
have P3: 0 < t * S k2 by move: P1; case t.
have P4: 0 < p ^ l * S k1 by move: P2; case (p ^ l)%N.
have P5: 0 < gcdn t (S k1).
  by move: (gcdn_0_inv t (S k1)); rewrite andbF;
     case: gcdn.
have P6: 0 < gcdn (p ^ l) (S k2).
  by move: (gcdn_0_inv (p ^ l) (S k2)); rewrite andbF;
     case: gcdn.
have F1 := (@orderg_gcd _ x _ P3).
rewrite F0 -(mulnC t) gcdn_mul2l edivn_mul2r in F1; last
  by rewrite lt_mul0 P1 P6.
have F2 := (@orderg_gcd _ x _ P4).
  rewrite F0 gcdn_mul2l edivn_mul2r in F2; last 
  by rewrite lt_mul0 P2 P5.
move => H1; rewrite F2.
have F3:  x ^ (orderg (x ^ (t * S k2)) *
                   orderg (x ^ (p ^ l * S k1))) = 1.
  rewrite -{1}H1 gexpn_add gexpn_mul muln_addl -gexpn_add.
  rewrite -!gexpn_mul (eqP (orderg_expn1 _)) gexp1n mul1g.
  by rewrite gexpn_mul mulnC -gexpn_mul (eqP (orderg_expn1 _))
              gexp1n.
move/eqP: F3; rewrite -orderg_divn F0 F1 F2.
rewrite -[(_ * edivn t _)%N]muln1.
have G1 := gcdn_divl (p ^ l) (S k2). 
rewrite divn_edivn in G1; rewrite -{1}(eqP G1) -mulnA (mulnC _ t).
have G2 := gcdn_divl t (S k1). 
rewrite divn_edivn in G2; rewrite -{1}(eqP G2) !mulnA.
set u := (edivn _ _ * _)%N.
rewrite -mulnA divn_mul2r.
case E2: (u == 0).
  rewrite /u eqn_mul0 in E2; case/orP: E2 => H2.
    rewrite (eqP H2) mul0n in G1.
    by rewrite -(eqP G1) in P2.
  rewrite (eqP H2) mul0n in G2.
  by rewrite -(eqP G2) in P1.
rewrite orFb divn1.
rewrite eqn_mul1; case/andP => H2 _.
by rewrite (eqP H2) edivn1.
Qed.

Lemma pconst_coprime: forall (x:G), 
 coprime (orderg (pconst x)) (orderg (prem x)).
Proof.
move => x.
rewrite orderg_pconst orderg_prem dlogn_coprime //.
exact: orderg_pos.
Qed.

Lemma pconst_prem_orderg: forall (x:G), 
 orderg x = (orderg (pconst x) * orderg (prem x))%N.
Proof.
move => x; rewrite -{1}(pconst_rem x).
apply: orderg_mul; first exact: pconst_remC.
exact: pconst_coprime.
Qed.

Definition spconst x y := 
  (pconst y == x)  && (divn (orderg y) (orderg x * s)).

Lemma spconst_uniq: forall x1 x2 y,
  spconst x1 y -> spconst x2 y -> x1 = x2.
Proof.
move => x1 x2 y; rewrite /spconst.
case/andP => H1 _; case/andP => H2 _.
by rewrite -(eqP H1); apply/eqP.
Qed.

Lemma spconst_conjgs: forall a b,
   spconst (a ^g b) =1 conjsg (spconst a) (b^-1).
Proof.
move => a b x; apply/idP/idP.
  rewrite /spconst; case/andP => H1 H2.
  apply/andP; split; first
     by rewrite pconst_conjg (eqP H1) conjg_conj
                mulgV conjg1.
  by move: H2; rewrite !orderg_conjg.
rewrite /spconst /conjsg; case/andP => H1 H2.
apply/andP; split.
  by rewrite -(eqP H1) pconst_conjg conjg_conj mulVg conjg1.
by move: H2; rewrite !orderg_conjg.
Qed.

Lemma spconst_card: forall a b,
  card (spconst (a ^g b)) = card (spconst a).
Proof.
move => a b; rewrite -(card_image (conjg_inj b) (spconst a)).
apply eq_card => x.
by rewrite spconst_conjgs conjsg_image invg_inv.
Qed.

Lemma pconst_subset_centralizer:  forall (y: G),
  subset (spconst y) (centraliser G y).
Proof.
move => y; rewrite /spconst; apply/subsetP => x.
case/andP => Hx1 Hx2.
rewrite /centraliser; repeat (apply/andP; split) => //.
rewrite -(gexpn1 x) -(eqP Hx1) /pconst.
by case: abezoutn => _ n; rewrite !gexpn_add addnC.
Qed.

Lemma pconst_mul_in: forall y z l, commg y z ->
  orderg y = (p ^ (S l))%N -> divn (orderg z) s ->
  spconst y (y * z).
Proof.
move => y z l H H1 H2.
have F0: coprime (orderg y) (orderg z).
  rewrite H1 -prime_coprime_k // prime_coprime //.
  case/divnP: H2 coprimeps => k ->.
  by rewrite coprime_mulr; case/andP.
have F1: (orderg (y * z) = (p ^ (S l) * (orderg z))%N).
  by rewrite -H1; apply: orderg_mul.
apply/andP; split; last
  by rewrite orderg_mul // divn_mul2r H2 orbT.
rewrite /spconst /pconst F1.
rewrite -F1.
have F2:  1 < orderg (y * z).
  rewrite F1.
  apply: (@leq_trans (S (orderg z))); first exact: orderg_pos. 
  rewrite -{1}(mul1n (orderg z)) lt_mul2r; 
    case: (orderg z) (orderg_pos z) => [| n _] //;
    rewrite andbT.
  apply: (@leq_trans (S (S l))) => //; apply: expn_lt.
  exact: prime_leq_2.
rewrite {1 3 5}F1 dlogn_mul_expn //; last (by exact: prime_leq_2);
  last exact: orderg_pos.
rewrite dlogn_ndiv ?addn0 -?H1; last 
  by apply/negP; rewrite (prime_coprime_k l) // -H1.
rewrite F1 -H1 edivn_mull; last exact: orderg_pos.
have F3: (1 < orderg y * orderg z) by rewrite H1 -F1.
move: (abezout_coprime _ _ F3 F0).
case: abezoutn => k1 k2 H3; apply/eqP.
rewrite gexpnC // -(gexpn_mul z) (eqP (orderg_expn1 _))
        gexp1n mulg1 mulnC.
rewrite -(mul1g (gexpn _ _)) -(gexp1n G k1)
        -(eqP (orderg_expn1 y)) gexpn_mul mulnC
        gexpn_add.
rewrite [_ + _](@edivn_modn _ (orderg z * orderg y)) (eqP H3).
by rewrite -gexpn_add  !mulnA (mulnC _ (orderg y))
           -gexpn_mul (eqP (orderg_expn1 _)) gexp1n gexpn1
           mul1g.
Qed.

Lemma pconst_image: forall y l, 
  orderg y = (p ^ (S l))%N -> coprime (orderg y) s -> 
  image prem (spconst y) =1
        (fun z => centraliser G y z && divn (orderg z) s). 
Proof.
move => y l Hy Cy x1; apply eqb_imp => H1.
  case: (Hdiinv H1) => y1; case/and3P => HH1 HH2 HH3.
  rewrite  -(eqP HH2) (eqP HH1); apply/andP; split.
    by apply/eqP; exact: pconst_remC.
  have F1: (orderg (pconst y1) == 0) = false.
    by case: orderg (orderg_pos (pconst y1)).
  rewrite -orFb -F1 -divn_mulSr mulnC -pconst_prem_orderg.
  by rewrite (eqP HH2) mulnC.
case/andP: H1 => H1 H2.
have F0: coprime (orderg y) (orderg x1).
  case/divnP: H2 => k Hk; rewrite Hk coprime_mulr in Cy.
  by case/andP: Cy.
have F1: commg y x1.
  rewrite /centraliser in H1; case/andP: H1 => _.
  by move/eqP.
have F2: coprime p (orderg x1).
  by rewrite -prime_coprime // (prime_coprime_k l) // -Hy. 
case/andP: (pconst_mul_in F1 Hy H2); move/eqP => H3 H4.
replace x1 with (prem (y * x1)).
  apply: image_f_imp; rewrite /spconst H3 eq_refl /=.
  rewrite orderg_mul //.
  by rewrite divn_mulSl H2 orbT.
apply: (mulg_injl y); rewrite -{1}H3; exact: pconst_rem.
Qed.


Lemma pconst_card: forall y l, 
  orderg y = (p ^ (S l))%N ->  
  card (spconst y) =
  card (fun z => centraliser G y z && divn (orderg z) s). 
Proof.
move => y l H.
have F0: coprime (orderg y) s.
  by rewrite H -prime_coprime_k // prime_coprime.
apply: etrans (eq_card  (pconst_image H F0)).
apply: sym_equal; apply: card_dimage.
move => y1 y2; case/andP => H1 H2; case/andP => H3 H4 H5.
move: (@KB_card_image G G (subgrp_of_group G) y _ _ primep).
by rewrite -(pconst_rem y1) -(pconst_rem y2) (eqP H1) (eqP H3) H5.
Qed.

Let KRG y :=
let i := is_true_true in
RG (subgrp_cyclic (G:=G) y) (subgrp_centraliser G (x:=y) is_true_true)
            (cyclic_subset_centraliser G (x:=y) i)
            (normal_centraliser G (x:=y) i).

Lemma pconst_card_KRG: forall y l, 
  orderg y = (p ^ (S l))%N ->  
  card (spconst y) =
  card (fun z: (KRG y) => divn (orderg z) s).
Proof.
move => y l H.
rewrite (pconst_card H).
apply: (KB_card_image (subgrp_of_group G) (is_true_true: G y) primep H).
by rewrite H -prime_coprime_k // prime_coprime.
Qed.


Definition spconstw (y: G) := 
  setnU (roots (rcoset (centraliser G y))) 
        (fun x => spconst (y ^g x)).

Lemma spconstwP: forall x y,
  reflect (exists i, spconst (y ^g i) x)
          (spconstw y x).
Proof.
move => x y; apply: (iffP idP).
  by case/setnUP => i; case/andP => Hi1 Hi2; exists i. 
case => i Hi; apply/setnUP.
set rco := rcoset _.
pose r := (root rco i).
have F1: roots rco r.
  by apply: roots_root; apply: rcoset_csym; 
     exact: (subgrp_centraliser G is_true_true).
exists r; rewrite F1 //=.
rewrite /is_true -Hi; congr spconst.
rewrite /conjg.
replace (r^-1 * y * r) with 
   (i^-1 * ((r * i^-1)^-1 * y * (r *  i^-1)) * i); last gsimpl.
have F2: rcoset (centraliser G y) i r.
  rewrite -rcoset_trans; first exact: connect_root.
  exact: (subgrp_centraliser (subgrp_of_group _) _).
rewrite /rcoset /centraliser in F2; case/andP: F2 => _ F2.
rewrite -(mulgA _ y) (eqP F2); gsimpl.
Qed.

Lemma card_spconstw: forall y l, orderg y = (p ^ (S l))%N ->  
  card (spconstw y) = ((rindex (centraliser G y) G) * 
                      card (fun z: (KRG y) => divn (orderg z) s))%N.
Proof.
move => y l Oy.
rewrite /spconstw (@card_setnU_id _ _ _ _ (card (spconst y))) //.
  congr muln => //.
    by apply: eq_card => x; rewrite /setI andbC.
  - exact: (pconst_card_KRG Oy).
  move => u v x Hu Hv Hsu Hsv.
  rewrite -(eqP Hu) -(eqP Hv).
  have F0 := (subgrp_of_group G).
  have F1 := (subgrp_centraliser F0 (is_true_true: G y)).
  apply sym_equal; apply/eqP.
  rewrite root_connect; last by exact: rcoset_csym.
  rewrite rcoset_trans /rcoset //. 
  have F2: y ^g u = y ^g v by apply: (spconst_uniq Hsu Hsv).
  rewrite /centraliser /=.
  rewrite /conjg in F2.
  apply/eqP; apply: (mulg_injl u^-1).
  rewrite !mulgA F2; gsimpl.
move => x; move/eqP => Hx.
exact: spconst_card.

Qed.


End PConstituent.

Section Frob.

Theorem frobenius: forall (G: finGroup) n,
  divn n (card G) ->
  divn n  (card (fun z: G => divn (orderg z) n)).
pose f (H: finGroup) n := (fun z: H => divn (orderg z) n).
change 
 (forall (G: finGroup) n, divn n (card G) -> divn n  (card (f G n))).
move => G; move: {2}(card G) (leqnn (card G)) => k.
elim: k G.
move => H; case Eq1: (card H) => [| n1] // _ n _.
rewrite eq_card0; first exact: divn0.
move => z; move: Eq1; rewrite (cardD1 z) //.
move => k Rec G; rewrite leq_eqVlt; case/orP => Hk n Hn;
  last apply Rec => //.
have Hn1: n <= card G by
  apply divn_le => //; rewrite (eqP Hk).
move: Hn; rewrite -(@leq_sub_sub n (card G)) //.
set (e := card G - n); elim: e {-2}e (leqnn e).
  case => // _ _; rewrite subn0.
  apply/divnP; exists 1%N; rewrite mul1n.
  apply: eq_card => x; rewrite /f /orderg subgrp_divn //.
  - apply subgrp_cyclic.
  - apply subgrp_of_group.
  - apply cyclic_h => //; apply subgrp_of_group.
move => n1 Hrec e.
rewrite leq_eqVlt; case/orP => H H1; last apply Hrec => //.
move: H1; rewrite (eqP H).
set (n2 := card G - S n1).
have Hn2: n2 < card G 
 by rewrite /n2 (eqP Hk) ltnS subSS leq_subr.
move: (leq0n n2); rewrite leq_eqVlt; case/orP.
  by move => HH; rewrite -(eqP HH) div0n (eqP Hk).
rewrite leq_eqVlt; case/orP;
  first by move => HH; rewrite -(eqP HH) !div1n.
move => Hn2b; case/divnP => [k1 Hk1].
set (p := first_prime k1).
have Hp := first_prime_prime k1; rewrite -/p in Hp.
have Hp1: divn (n2 * p) (card G).
  have F1: negb(k1 == 1%N) by
    move: Hn2; rewrite {p Hp}Hk1; 
    case: k1 => //; case => //;
    rewrite mul1n ltnn.
  case/divnP: (first_prime_divn _ F1) => k2 Hk2.
  by rewrite Hk1 Hk2 -/p -mulnA (mulnC p) divnMl.
have Hp2: n2 * p <= card G by apply divn_le => //; 
                              rewrite (eqP Hk).
have D1: divn n2 (card (f G (n2 * p))).
  apply: (divntrans _ (n2 * p)); first exact: divnMr.
  rewrite -(@leq_sub_sub (n2 * p) (card G)) //.
  apply Hrec; last by rewrite leq_sub_sub.
  rewrite leq_sub_add.
  rewrite -(@leq_add_sub (S n1) (card G)).
    rewrite -ltnS -/n2 -[S(_ + n1)]addnS addnC ltn_add2r 
            -{1}(mul1n n2) mulnC lt_mul2l.
    move: Hp Hn2b; case: (n2) => // n3; 
    by case: (p) => //; case.
  apply ltn_trans with (S n1); first exact: ltnSn.
  rewrite ltn_lt0sub; apply ltn_trans with 1%N => //.
rewrite -(@divn_plus_r _ (card (setI (f G (n2 * p)) (setC (f G n2))))).
  case/divnP: D1 => u Hu; apply/divnP; exists u; rewrite -Hu.
  rewrite -(cardIC (f G n2) (f G (n2 * p))) addnC; congr addn.
  apply eq_card => x; rewrite /setI; case Eq1: (f G n2 x);
    last by rewrite andbF. 
  rewrite andbT /f; apply sym_equal; apply/idP.
  by apply: (divntrans _ _ _ (idP Eq1)); apply divnMr.
pose l := dlogn p n2.
pose s := (edivn n2 (p ^ l)).
have P1: 0 < p ^ (S l).
  apply (@ltn_trans (S l)) => //.
by apply expn_lt; apply prime_leq_2.  
have Hsl: n2 = (p ^ l) * s.
  rewrite /s; apply/eqP.
  rewrite eq_sym mulnC -divn_edivn.
  exact: dlogn_l.
have Hsl1: coprime p s.
  rewrite -(expn1 p) -prime_coprime_k //.
  apply/negP => H1.
  have F1: S 0 < p by exact: prime_leq_2.
  move: (dlogn_r _ n2 F1) Hn2b; 
  rewrite -/l expnS {1}Hsl mulnC divn_mulSl H1 orbT.
  by case: (n2).
set A := (setI (f G (n2 * p)) (setC (f G n2))).
have F1: forall z, A z -> exists u,
     coprime p u &&  (orderg z == u * p ^ (S l)).
  move => z; case/andP; rewrite /f /setC => H1; move/negP => H2. 
  case/divnP: H1 => u Hu.
  case E1: (divn p u).
    case/divnP: (idP E1) => u1 Hu1.
    case H2; apply/divnP; exists u1.
    apply/eqP; rewrite -(@eqn_mulr p); last by case: (p) Hp.
    by rewrite Hu Hu1 -mulnA (mulnC p) mulnA eq_refl.
  have E2: divn (p ^ (S l)) (orderg z).
    rewrite -(gauss _ u); first by
      rewrite -Hu Hsl expnS (mulnC _ p) mulnA divnMr.
    by rewrite -prime_coprime_k // E1.
  case/divnP: E2 => u1 Hu1.
  exists u1; rewrite Hu1 eq_refl andbT.
  have E2: (s == u * u1).
    rewrite  -(@eqn_mulr (p ^ (S l))).
      by rewrite -mulnA -Hu1 -Hu (mulnC _ p) Hsl mulnA -expnS mulnC.
    by case: (p ^ (S l)) P1.
  rewrite (eqP E2) coprime_mulr in Hsl1.
  by case/andP: Hsl1.
rewrite {1}Hsl gauss_inv; 
  last (by (case: (l) => [| u]; 
          first (by rewrite expn0 /coprime gcdn1 eq_refl);
        rewrite -prime_coprime_k // prime_coprime));
  apply/andP;split.
(* First case *)
  apply divntrans with ((p ^ l) * (p - 1)); first by exact: divnMr.
  set (e1 := fun x:G => (generator (cyclic x)): set G).
  have Her: forall x, e1 x x.
    by move => x; rewrite /e1 generator_cyclic.  
  have Hes: forall x y, e1 x y = e1 y x.
    move => x y; rewrite /e1; apply/idP/idP; 
     move/andP => [HH1 HH2]; apply/andP; split; auto.
  have Het: forall x y, connect e1 x y = e1 x y.
    move=> x y; apply/idP/idP; last exact: connect1.
    move/connectP=> [p1 HHp1 <- {y}]; rewrite Hes.
    elim: p1 x HHp1 => [|y p1 IHp1] x /=; first by rewrite Her.
    move/andP=> [Hxy HHp1]; rewrite /e1.
    case/andP: Hxy.
      move/subsetP => Hxy1.
      move/subsetP => Hxy2.
    case/andP: (IHp1 _ HHp1).
      move/subsetP => HHp2.
      move/subsetP => HHp3.
    have HHp4 : (cyclic (last y p1) =1 (cyclic y)).
      move => z; apply/idP/idP => HHp4; first
        by apply: HHp3.
      by apply: HHp2.
    rewrite /generator; apply/andP; split;
        apply/subsetP => z; rewrite HHp4 => HHp0.
      exact: Hxy2.
    exact: Hxy1.
  have Hec: connect_sym e1.
    by move=> x1 y1; rewrite !Het Hes.
  have He1: closed e1 A.
    move => x y; move/andP => [Hx  Hxy].
      have Hxy1: (orderg x = orderg y).
       apply eqn_antisym; apply: subset_leq_card; auto. 
      rewrite /A /f /setI Hxy1; congr andb.
      by rewrite /setC Hxy1.
  move: {2}(n_comp e1 A) (refl_equal (n_comp e1 A)) He1 F1.
  move => nn; elim: nn A => [| nn Hrecn] A.
    move/eqP => H1 H2 H3.
    replace (card A) with 0; first by exact: divn0.
    symmetry; apply: (appP set0P eqP) => x; apply/idP=> Hx.
    case/idP: (set0P H1 (root e1 x)).
    rewrite /setI (roots_root Hec) /=.
    by rewrite -(closed_connect H2 (connect_root _ _)).
  case: (pickP (setI (roots e1) A)) => [x Hx | HHk]; last
    by rewrite /n_comp (eq_card HHk) card0.
  rewrite -(cardIC (e1 x) A) /n_comp (cardD1 x) Hx => [] [Dn].
  move => H1 H2.
  rewrite divn_plus_l.
    replace (card (setI A (e1 x))) with (card (e1 x)).
      rewrite /e1 -phi_gen. 
      have J1: A x by case/andP: Hx. 
      case: (H2 _ J1) => [kk1 Hkk1].
      case/andP: Hkk1 => Hkk1 Hkk2.
      rewrite (eqP Hkk2) phi_mult ?phi_prime_k //.
        apply/divnP; exists (phi kk1); congr muln.
        by rewrite expnS muln_subr muln1 (mulnC p).
      by rewrite coprimeC -prime_coprime_k ?prime_coprime.
    apply eq_card => x1; apply/idP/idP => Hx1;
        last by case/andP: Hx1.
    rewrite /setI Hx1 andbT -(H1 x x1) //.
    by case/andP: Hx.
    replace (card (setI A (setC (e1 x)))) with
            (card (setD A (e1 x)));
      last by apply: eq_card => y; exact: andbC.
    apply: Hrecn => //.
      apply: {nn}etrans Dn; apply: eq_card => y; rewrite /setD1 /setI andbCA /setD.
      rewrite -Het (sameP (rootP Hec) eqP) -/e1.
      by case Dy: (roots e1 y) (andP Hx) => //=
            [] [Dx _]; rewrite (eqP Dy) (eqP Dx).
    move=> y z Hyz; rewrite /setD (H1 _ _ Hyz) -!Het -/e1.
    by rewrite (same_connect_r Hec (connect1 Hyz)).
  by move => z Hz; apply H2; case/andP: Hz.
(* Second case *)
have F2: wpartition (fun z => orderg z == p ^ (S l))
                    (@spconstw p s G) A.
  split.
    move => u v x /= Hu Hv.
    case/spconstwP => u1 Hu1.
    case/spconstwP => u2 Hu2.
    have F2:= (spconst_uniq Hu1 Hu2).
    move => x1; apply/spconstwP/spconstwP => [] [i Hi].
      exists (u2 * (u1^-1 * i))%G.
      rewrite /is_true -Hi; congr spconst.
      by rewrite -conjg_conj -F2 conjg_conj; congr conjg; gsimpl.
    exists (u1 * (u2^-1 * i))%G.
    rewrite /is_true -Hi; congr spconst.
    by rewrite -conjg_conj F2 conjg_conj; congr conjg; gsimpl.
  apply/coverP; split.
     move => x Hx; apply/subsetP => y; case/spconstwP => i Hi.
     case/andP: Hi => Hi1 Hi2.
     move: (pconst_prem_orderg Hp y).
     rewrite (eqP Hi1) orderg_conjg (eqP Hx) => Hi3.
     rewrite orderg_conjg (eqP Hx) in Hi2.
     rewrite /A /f /setI Hsl.
     apply/andP; split.
       by rewrite mulnC mulnA.
     rewrite /setC Hi3 expnS -mulnA mulnC -!mulnA divn_mul2r.
     move: P1; rewrite expnS; case (p ^ l); first by rewrite muln0.
     move => _ _ /=.
     apply/negP => H1.
     have F2: ~~(divn p s); first rewrite prime_coprime //.
     case/negP: F2; apply: (divntrans _ _ _ _ H1); exact: divnMl.
  move => x Hx.
  case: (F1 x) =>  // t; case/andP => Ht1 Ht2.
  have F2: orderg (pconst p x) = p ^S l.
    rewrite orderg_pconst // (eqP Ht2).
    rewrite mulnC dlogn_mul_expn //.
      rewrite dlogn_ndiv; first by rewrite addn0.
      by apply/negP; rewrite prime_coprime.
    - move: (orderg_pos x); rewrite (eqP Ht2); by case t. 
    exact: prime_leq_2.     
  exists (pconst p x); rewrite F2 eq_refl /=.
  apply /spconstwP; exists (Group.unit G); rewrite conjg1 /id.
  rewrite /spconst eq_refl /= F2.
  rewrite expnS -mulnA -Hsl mulnC.
  by case/andP: Hx.
apply: (card_divn_partition F2) => x Hx.
rewrite (card_spconstw _ _ (eqP Hx)) //.
set KRG := (RG _ _ _ _).
set cKRG := card KRG.
have F3: card KRG = lindex (cyclic x) (centraliser G x).
  apply: card_root_group.
have F4: card (centraliser G x) = card KRG * orderg x.
  rewrite F3 /orderg.
  apply sym_equal; rewrite mulnC; apply: lLaGrange => //.
    exact: subgrp_cyclic.
  apply: subgrp_centraliser => //; exact: subgrp_of_group.
  apply: cyclic_subset_centraliser  => //; exact: subgrp_of_group.
have F5: cKRG <= k.
  rewrite (eqP Hx) in F4.
  have F5: divn (card (centraliser G x)) (card G).
    apply: subgrp_divn.
      apply: subgrp_centraliser => //; exact: subgrp_of_group.
    - exact: subgrp_of_group.
    exact: subset_centraliser.
  rewrite F4 in F5.
  rewrite -ltnS -(eqP Hk).
  have F6: 0 < card G by rewrite (eqP Hk).
  move: (divn_le _ _ F6 F5) => H1.
  apply: (leq_trans _ H1). 
  rewrite -(muln1 cKRG) /cKRG lt_mul2l.
  case E1: (card KRG == 0).
    move: (card0_eq (eqP E1)) => H2.
    move: (H2 (Group.unit KRG)) => //.
  rewrite andTb.
  apply (@leq_trans (S (S l))) => //.
  by apply expn_lt; apply prime_leq_2.  
have F6:= (gcdn_divl cKRG s).
have F7: (fun z : KRG => divn (orderg (G:=KRG) z) s) =1
         (fun z : KRG => divn (orderg (G:=KRG) z) (gcdn cKRG s)).
  move => y /=; apply/idP/idP => H1.
    apply gcdn_div_div => //; exact: orderg_div_g.
  apply: (divntrans _ _ _ H1); exact: gcdn_divr.
rewrite (eq_card F7).
case/divnP: (Rec _ F5 (gcdn (card KRG) s) F6) => c.
rewrite /f /cKRG => ->.
set r := (rindex _ _).
have F8: card G = r *  card (centraliser G x).
  apply sym_equal; rewrite mulnC; apply: rLaGrange => //.
  apply: subgrp_centraliser => //; exact: subgrp_of_group.
  exact: subgrp_of_group.
  exact: subset_centraliser. 
rewrite F4 (eqP Hx) in F8. 
apply: (@divntrans _ (r * gcdn (card KRG) s)); last
  by apply/divnP; exists c; rewrite mulnA (mulnC r) !mulnA.
case (coprime_gcdn (card KRG) s) => u1 [u2 [Hu1 [Hu2 Hu3]]].
rewrite {1}Hu2 (mulnC r) divn_mul2r.
have F9: (gcdn (card KRG) s == 0) = false.
  case E1: (gcdn (card KRG) s) => [| u] //.
  move/eqP: E1; rewrite gcdn_0_inv.
  move: Hn2b; rewrite Hsl; case s => [|s1 _]; first by rewrite muln0.
  by rewrite /= andbF.
rewrite F9 orFb.
rewrite coprimeC in Hu3.
rewrite -(gauss _ _ _ Hu3) -orFb -F9 -divn_mul2r -Hu2
        mulnA -Hu1.
have F10: coprime s (p ^ (S l)).
  by rewrite coprimeC -prime_coprime_k // prime_coprime.
rewrite mulnC -(gauss _ _ _ F10) mulnC -mulnA -F8.
by rewrite Hk1 Hsl mulnA divnMl.
Qed.

End Frob.

Unset Implicit Arguments.
