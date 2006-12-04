(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*          Definition of sylow group                                  *)
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
Require Import action.
Require Import perm.
Require Import cyclic.
Require Import zp.
Require Import normal.
Require Import baux.
Require Import leftTranslation.
Require Import powerSet.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Cauchy.

Open Scope group_scope.

Variable (G : finGroup) (H : set G).
Hypothesis subgrp_H: subgrp H.

Variable p: nat.
Hypothesis prime_p: prime p.
Hypothesis p_divides_H: divn p (card H).


(**********************************************************************)
(*               Cauchy theorem                                       *)
(**********************************************************************)

Theorem cauchy: exists a, H a && (card (cyclic a) == p).
Proof.
set mzp := (@zp_group (S (S (p - 2))) is_true_true).
set mp := (@permute_zp _ _ subgrp_H (p - 2)).
set e := (S0 mzp mp).
have F1: (divn p (card e)).
   have F2: card mzp = (p ^ 1)%N.
     rewrite /mzp card_zp.
     rewrite -!leq_subS ?subSS; last by apply prime_leq_2.
       by rewrite subn0 expn1.
     by case: p prime_p.
  rewrite /e /divn -(mpl _ _ _ _ F2) //.
   rewrite card_permSet.
   by exact: divn_expn.
   by exact: subgrp_of_group.
   by move => x Hx; exact: permute_zp_bij.
   by move => x y H0 Hx Hy; exact: permute_zp_morph.
have F2: e (permSet1 subgrp_H (p - 2)).
  by move: (stab1 subgrp_H (p - 2)) F1; rewrite /stab.
have F3: card e >= 2.
  move: F1.
  rewrite (cardD1 (permSet1 subgrp_H (p - 2))) F2 //= add1n.
  match goal with |- context[S ?x] => case x => //= end.
  by rewrite divn1; move/eqP => H1; move: prime_p; rewrite H1.
move: F3.
rewrite (cardD1 (permSet1 subgrp_H (p - 2))) F2 //= add1n ltnS => F3.
match type of F3 with is_true (_ < ?x)  => 
  move: F3; set (u := x) => F3 end.
have F4: u != 0.
   by move: F3; case u.
move/set0Pn: F4 => [[a Ha] Ha1].
move/andP: Ha1 => [Ha1 Ha2].
move: (stab_in Ha2) => [[e1 He1] He2].
rewrite /val /valP in He2.
exists e1; rewrite He1 /=.
move/prime_div: prime_p => [Hp0 Hp].
have F4: e1 ^ p == 1.
  replace p with (S (S (p -2))).
    apply/eqP.
    rewrite -(prod_prodn_id (H:= H) _ He1) // -He2.
    by rewrite -(f_iinv Ha) prod_add_inv.
  case: p prime_p => //; case => //= n1 _.
    by rewrite !subSS subn0.
apply/eqP; case: (Hp (orderg e1)) => //.
  by rewrite orderg_divn.
move => H1.
have F5: (set1 1) =1 (cyclic e1).
  apply/subset_cardP.
    by rewrite card1.
  by apply/subsetP => x Hx; rewrite -(eqP Hx) cyclic1.
move: (F5 e1).
rewrite -{3}(gexpn1 e1) cyclic_in.
move/eqP => H2.
case (negP Ha1).
do 2 apply/val_eqP => /=; rewrite He2.
apply/eqP; congr EqPair.
  by apply/val_eqP; apply/eqP.
by apply: prodn_id_irr.
Qed.

End Cauchy.

Section Sylow.

Open Scope group_scope.

Variable (G : finGroup) (K : set G).
Hypothesis subgrp_K: subgrp K.

Variable p: nat.
Hypothesis prime_p: prime p.

Let n:= dlogn p (card K).

Hypothesis n_pos: 0 < n.

(**********************************************************************)
(*  Definition of a sylow group:                                      *)
(*  its a subgroup of cardinal p ^n where n is the largest n such     *)
(*  that p^n divides card k                                           *)
(**********************************************************************)

Definition sylow L := 
  (subgrpb L) && ((subset L K) && (card L == p ^ n)%N).

Lemma eq_sylow: forall L1 L2, L1 =1 L2 -> sylow L1 = sylow L2.
Proof.
by (move => L1 L2 H0; apply/and3P/and3P => [] [H1 [H2 H3]]; repeat split);
 [rewrite -(eq_subgroup H0)|
  rewrite -(eq_subset H0) |
  rewrite -(eq_card H0) |
  rewrite (eq_subgroup H0) |
  rewrite (eq_subset H0) |
 rewrite (eq_card H0)].
Qed.


Lemma sylow_conjsg: forall L x, K x -> 
  sylow L -> sylow (conjsg L x).
Proof.
move => L x Hkx H.
move/and3P: H => [H1 H2] H3.
apply/and3P; repeat split; first by apply conjsg_subgrp.
  apply/subsetP => y Hy.
  replace y with (x * (x^-1 * y * x) * x^-1); last by gsimpl.
  apply subgrpM => //; last by exact: subgrpV.
  apply subgrpM => //.
  by apply (subsetP H2).
by rewrite conjsg_card.
Qed.

Lemma sylow1_rec: forall i Hi, 0 < i -> i < n -> 
  subgrp Hi -> subset Hi K -> (card Hi = p ^ i)%N ->
  exists H: set G, subgrp H /\ subset Hi H /\ subset H K 
                   /\ normal Hi H /\ (card H = p ^ (S i))%N.
Proof.
move => i Hi L0i Lin Hh1 Hh2 Hh3.
have F1: divn p (lindex Hi K).
  move/divnP: (dlogn_l p (card K)); rewrite -/n => [] [k1 Hk1].
  apply/divnP; exists (muln k1 (p ^ (n - (S i))))%nat.
  rewrite -{2}(expn1 p) -mulnA -expn_add addn1 -leq_subS //  subSS.
  have F2: card Hi != 0.
    rewrite (cardD1 1) subgrp1 //=.
  apply: (muln_injl F2).
  rewrite (lLaGrange Hh1 subgrp_K) // Hk1 Hh3.
  rewrite (mulnC (p ^ i)) -mulnA -expn_add addnC leq_add_sub //.
  by apply: (leq_trans _ Lin); rewrite leqnSn.
set (lS0 := (lS0 subgrp_K Hh1 Hh2)).
have F2:
  (modn (lindex Hi K) p =  modn (card lS0) p).
  rewrite -card_rootSet.
  apply: mpl Hh3 => //.
    by move => x Hx; apply: ltrans_bij => //; apply (subsetP Hh2).
  by move => x y z Hx Hy; apply: ltrans_morph => //; apply (subsetP Hh2).
set (ng_q := (RGN subgrp_K Hh1 Hh2)).
have F3:card lS0 = card ng_q.
  apply sym_equal; apply: bij_eq_card.
  by exists (@to_RG_inv _ _ _ subgrp_K Hh1 Hh2);
     apply: to_RG_inv_bij.
have F4: divn p (card ng_q).
  rewrite -F3 /divn -F2 -/divn; exact F1.
case: (cauchy (subgrp_of_group _) prime_p F4) => sng.
case/andP => Hsng1 Hsng2.
set L :=
 (setI 
   (preimage 
    (quotient Hh1 (normaliser_grp Hi (subgrp_K)) 
         (subset_normaliser Hh1 Hh2) (normaliser_normal Hh2))
    (cyclic sng)) (normaliser Hi K)).
have T0: (subgrp (cyclic sng)).
  by apply: subgrp_cyclic.
have T1: subgrp L.
  exact: quotient_preimage_subgrp.
have T2: subset Hi L.
  exact: quotient_preimage_subset_h.
exists L; repeat split => //.
    apply: (subset_trans _ (normaliser_subset Hi K)).
    by exact: quotient_preimage_subset_k.
  apply (normal_subset  (normaliser_normal Hh2)) => //.
  by exact: quotient_preimage_subset_k.
rewrite -(lLaGrange Hh1) // Hh3.
rewrite (quotient_index Hh1 (normaliser_grp Hi (subgrp_K)) 
         (subset_normaliser Hh1 Hh2) (normaliser_normal Hh2)) //.
  rewrite /L (eq_card (@quotient_image_preimage _ _ _
                      Hh1 (normaliser_grp Hi (subgrp_K))
                    (subset_normaliser Hh1 Hh2) (normaliser_normal Hh2)
                    (cyclic sng))).
  rewrite expnS [muln p _]mulnC; congr muln.
  by exact: (eqP Hsng2).
by exact: quotient_preimage_subset_k.
Qed.

Lemma sylow1: forall i, 0 < i -> i <= n -> 
  exists H: set G, subgrp H /\ subset H K /\ (card H = p ^ i)%N.
Proof.
elim => [| i] //.
case: i => [| i].
  move => _ _ _; rewrite expn1.
  case: (cauchy subgrp_K prime_p).
     apply: divntrans _ (dlogn_l p (card K)).
     rewrite -/n; move: n_pos; case: n => // n1 _.
     by apply divn_expn; rewrite divnn.
  move => a; case/andP => Ha1 Ha2.
  exists (cyclic a: set G); repeat split => //; last exact: eqP.
    by apply subgrp_cyclic.
  apply: cyclic_h => //.
move => Rec _ H; case: Rec => //.
  by rewrite (leq_trans _ H) // leqnSn.
move => H0 [Hh1 [Hh2 Hh3]].
have F1: 0 < S i by done.
case (sylow1_rec F1 H Hh1 Hh2 Hh3).
by move => ngc [H1 [H2 [H3 [H4 H5]]]]; exists ngc; repeat split.
Qed.

(**********************************************************************)
(*               First Sylow theorem                                  *)
(**********************************************************************)

Theorem sylow1_cor: exists H: set G, sylow H.
Proof.
case (@sylow1 n) => //.
move => H [H1 [H2 H3]]; exists H.
apply/and3P; repeat split => //.
by apply/eqP.
Qed.

Lemma sylow2: forall H L i,0 <i -> i <= n ->
 subgrp H -> subset H K ->  (card H = p ^ i)%N -> sylow L ->
   exists x, (K x) && subset H (conjsg L x).
Proof.
move => H L i H1 H2 Hsh Hshk Hch Hsl.
move/and3P: Hsl => [[Hsl Hsl1] Hsl2].
set ltrans1 := ltrans subgrp_K Hsl Hshk Hsl1.
set (lS0 := S0 H ltrans1).
have F1: ~~(divn p (lindex L K)).
  apply/negP => Fd.
  move/divnP: Fd => [u Hu].
  have F2: (divn (p ^ (S n)) (card K)).
    apply/divnP; exists u.
    rewrite -(lLaGrange Hsl subgrp_K Hsl1) Hu (eqP Hsl2) expnS (mulnA u).
    exact: mulnC.
  move: F2; rewrite /n dlogn_r;
    last by (move: prime_p; case p => //=; case).
  rewrite (cardD1 1) subgrp1 //=.
have F2:  modn (lindex L K) p =  modn (card lS0) p.
  rewrite -card_rootSet /lS0.
  apply: mpl Hch => //.
    move => x Hx; apply: ltrans_bij => //.
  by move => x y z Hx Hy; apply: ltrans_morph.
rewrite /divn {}F2 in F1.
have F3: exists x, lS0 x.
  apply/set0Pn.
  by move: F1; rewrite /set0b; case (card lS0) => //=; rewrite mod0n.
case: F3 => [[x Hx] Hx3].
move: (andP Hx) => [Hx1 Hx2].
exists x; apply/andP; split => //.
apply/subsetP => y Hy; rewrite -(invg_inv y); apply conjsg_inv => //.
rewrite /conjsg conjgE.
replace (x^-1 * y^-1 * x) with ((y * x)^-1 * x); last by gsimpl.
change (is_true (lcoset L (y * x) x)).
move: (root_connect (lcoset_csym Hsl) (y * x) x).
rewrite lcoset_trans //.
move => H0; rewrite -H0.
rewrite (eqP Hx1).
move/andP: {Hx3}(subsetP Hx3 y Hy) => [Hx3 _].
move: Hx3; rewrite /ltrans1 /ltrans.
case: (wb (H y)); case => e.
move/val_eqP; move/val_eqP => //=.
by move: Hy; rewrite e.
Qed.


(**********************************************************************)
(*               Second Sylow theorem                                 *)
(**********************************************************************)

Lemma sylow2_cor: forall L1 L2,
   sylow L1 -> sylow L2 -> exists x, (K x) /\ (L2 =1 conjsg L1 x).
move => L1 L2 Hl1; move/and3P => [[Hl2 Ml2] Nl2].
case: (sylow2 (i := n) (H := L2) (L := L1)) => //.
  by apply/eqP.
move => x; move/andP => [Hx1 Hx2].
exists x; split => //.
apply/subset_cardP => //.
rewrite conjsg_card (eqP Nl2).
by apply sym_equal; apply/eqP; case/and3P: Hl1.
Qed.


(**********************************************************************)
(*   Definition of the set of sylow set                               *)
(**********************************************************************)

Let ps := powerSet G.
Definition syset (p: ps) := sylow (val p).


(**********************************************************************)
(*   Definition of the group action x |-> [ H |-> xHx^-1              *)
(**********************************************************************)

Definition aconj: 
 forall L (Hl1: subgrp L) (Hl2: subset L K),
 G -> sub_finType syset -> sub_finType syset.
move => L Hl1 Hl2 x.
case (wb (L x)); case => Hkx; last done.
move => [[y Hy] Hy1].
have F1: sylow (conjsg y x).
  by apply: sylow_conjsg => //; apply (subsetP Hl2).
exists ((EqSig _ _ (powerSeq_mem (enum G) (conjsg (G:= G) y x))): ps).
by rewrite /syset //= (eq_sylow (filter_enum _)).
Defined.

Lemma aconj_cancel:
  forall L (Hl1: subgrp L) (Hl2: subset L K),
  forall x, L x -> cancel (aconj Hl1 Hl2 x) (aconj Hl1 Hl2 x^-1).
Proof.
move => L Hl1 Hl2 x Hkx [[y Hy] Hy1].
have F1: L x ^-1 by exact: subgrpV.
rewrite /aconj.
case (wb (L x^-1)); case; last (by rewrite F1); move => H1.
case (wb (L x)); case; last (by rewrite Hkx); move => H2.
do 3 apply/val_eqP => //=.
set (e := (conjsg y x)).
replace y with (filter y (enum G)).
  apply/eqP; apply: eq_filter => z.
  rewrite (eq_conjsg _ (filter_enum e)).
  by rewrite /e /conjsg conjg_conj mulVg conjg1.
apply sym_equal; apply: powerSeq_uniq_eq => //=.
exact: uniq_enum.
Qed.

Lemma aconj_bij:
  forall L (Hl1: subgrp L) (Hl2: subset L K),
  forall x : G, L x -> bijective (aconj Hl1 Hl2 x).
Proof.
move => L Hl1 Hl2 x Hkx.
have F1: L x ^-1 by exact: subgrpV.
exists (aconj Hl1 Hl2 x^-1); first by apply aconj_cancel.
rewrite -{2}(invg_inv x).
by apply aconj_cancel.
Qed.

Lemma aconj_morph: 
  forall L (Hl1: subgrp L) (Hl2: subset L K),
  forall x y z, L x -> L y -> 
  aconj Hl1 Hl2 (x * y) z = aconj Hl1 Hl2 x (aconj Hl1 Hl2 y z).
Proof.
move => L Hl1 Hl2 x y [[z Hz] Hz1] H1 H2.
have F1: L (x * y) by exact: subgrpM.
rewrite /aconj.
case (wb (L (x * y))); case; last (by rewrite F1); move => HH1.
case (wb (L x)); case; last (by rewrite H1); move => HH2.
case (wb (L y)); case; last (by rewrite H2); move => HH3.
do 3 apply/val_eqP => //=.
apply/eqP; apply: eq_filter => z1.
by rewrite /conjsg mem_filter /setI mem_enum andbT  conjg_conj.
Qed.

(**********************************************************************)
(*   First part of the third Sylow theorem                            *)
(**********************************************************************)

Theorem sylow3_div: divn (card syset) (card K).
Proof.
case sylow1_cor => H Hh.
have F1:  (syset (EqSig _ _ (powerSeq_mem (enum G) H)))
by rewrite /syset //= (eq_sylow (filter_enum _)).
set (aconj1 := aconj subgrp_K (subset_refl _)).
replace (card syset) with (card (orbit K aconj1 (EqSig _ _ F1))).
apply: card_orbit_div => //.
  by exact: aconj_bij.
  by exact: aconj_morph.
have F2: (card (sub_finType syset) = card syset).
  exact: card_setA_sub.
rewrite -{}F2.
apply eq_card => x; apply eqb_imp => //= H0.
rewrite /orbit.
have F2 : (sylow (val (val x))).
  case x => //=.
case: (sylow2_cor Hh F2) => y [Hy Hy1].
replace x with (aconj1 y (EqSig _ _ F1)).
  by exact: image_f_imp.
rewrite /aconj1 /aconj.
case (wb (K y)); case; last (by rewrite Hy); move => HH.
do 3 apply/val_eqP => //=.
match goal with |- is_true (_ == ?x) => 
  replace x with (filter x (enum G))
end.
  apply/eqP; apply: eq_filter => z.
  rewrite Hy1.
  exact: (eq_conjsg _ (filter_enum H)).
apply sym_equal; apply: powerSeq_uniq_eq => //=.
exact: uniq_enum.
case x => //= [[x1 Hx1] Hx2] //=.
Qed.

End Sylow.

Section SylowAux.

Open Scope group_scope.

Variable (G : finGroup) (H K L: set G).
Hypothesis subgrp_K: subgrp K.
Hypothesis subgrp_L: subgrp L.
Hypothesis subgrp_H: subgrp H.
Hypothesis subset_HL: subset H L.
Hypothesis subset_LK: subset L K.

Variable p: nat.
Hypothesis prime_p: prime p.
Let n := dlogn p (card K).
Hypothesis n_pos: 0 < n.

Lemma sylow_subset: sylow K p H -> sylow L p H.
Proof.
move/and3P => [H1 H2 H3].
apply/and3P; repeat split => //.
rewrite (eqP H3); apply/eqP.
congr expn.
have F1:= prime_leq_2 _ prime_p.
apply: eqn_antisym.
  rewrite -dlogn_leq -?(eqP H3) //.
    by exact: subgrp_divn.
  by rewrite (cardD1 1) subgrp1.
apply divn_dlogn => //.
  by rewrite (cardD1 1) subgrp1.
by exact: subgrp_divn.
Qed.

End SylowAux.

Section Sylow3.

Open Scope group_scope.

Variable (G : finGroup) (K : set G).
Hypothesis subgrp_K: subgrp K.

Variable p: nat.
Hypothesis prime_p: prime p.

Let n := dlogn p (card K).

Hypothesis n_pos: 0 < n.

(**********************************************************************)
(*   Second part of the third Sylow theorem                           *)
(**********************************************************************)
Lemma sylow3_mod: modn (card (syset K p)) p = 1%N.
Proof.
case (sylow1_cor subgrp_K prime_p n_pos)  => H Hh.
have F1: subgrp H by case/and3P: Hh.
have F2: subset H K by case/and3P: Hh.
have F3: (card H = p ^ n)%N by (apply/eqP; case/and3P: Hh).
set S1 := sub_finType (syset K p).
set aconj1 := aconj subgrp_K F1 F2 (p := p).
set S01 := S0 H aconj1.
have F4: (card S1 = card (syset K p)).
  exact: card_setA_sub.
rewrite -{}F4.
have F4: modn (card S1) p = modn (card S01) p.
  apply: mpl F3 => //.
  exact: aconj_bij.
  exact: aconj_morph.
rewrite {}F4.
rewrite -(@modn_small 1%N p); last by case: p prime_p => //=; case.
congr modn.
have F4:  (syset K p (EqSig _ _ (powerSeq_mem (enum G) H))).
  by rewrite /syset //= (eq_sylow _ _ (filter_enum _)).
set h1:= @EqSig _ (syset K p) _ F4.
have F5: S01 h1.
  apply/subsetP => x Hx.
  apply/andP; split => //.
  rewrite /aconj1 /aconj.
  case (wb (H x)); case; last (by rewrite Hx); move => HH.
  do 4 apply/val_eqP => //=.
  apply/eqP; apply: eq_filter => z.
  rewrite (eq_conjsg _ (filter_enum H)).
  rewrite /conjsg conjgE.
  apply/idP/idP => HH1.
    replace z with (x * (x^-1 * z * x) * x^-1); last gsimpl.
    apply subgrpM => //; last by exact: subgrpV.
    by apply subgrpM => //.
  apply subgrpM => //.
  by apply subgrpM => //; first by exact: subgrpV.
have F6: forall x, S01 x -> x = h1.
  move => [[x Hx] Hx1] H1.
  case (and3P Hx1) => //= G1 G2 G3.
  have F7: subset H (normaliser x K). 
    apply/subsetP => y Hy.
    apply/andP; split; last by apply (subsetP F2).
    apply/subsetP => z Hxy.
    rewrite /conjsg conjgE.
    have F8: stabiliser H aconj1 (EqSig _ _ Hx1) y.
      by apply: (subsetP H1).
    move/andP: F8 => [H2 H3].
    move: H2; rewrite /aconj1 /aconj.
    case (wb (H y)); case; last by rewrite Hy.
    move => He; move/eqP; move/val_eqP.
    move/eqP; move/val_eqP => //= H4.
    rewrite -{2}(eqP H4) filter_enum.
    by rewrite /conjsg conjgE eq_refl.
  have N1 := (subset_normaliser G1 G2).
  have N2 := (normaliser_normal G2).
  have N3 := normaliser_grp x subgrp_K.
  have N4 := (normaliser_subset x K).
  have F8 : sylow (normaliser x K) p H.
    apply: (sylow_subset (K := K)) => //.
  have F9 : sylow (normaliser x K) p x.
    apply: (sylow_subset (K := K)) => //.
  case: (sylow2_cor N3 prime_p _ F9 F8).
    apply: (@leq_trans (dlogn p (card x))).
      rewrite (eqP G3).
      rewrite dlogn_expn //.
      exact: prime_leq_2.
    apply: divn_dlogn => //; first by exact: prime_leq_2.
      by rewrite (cardD1 1) subgrp1.
    by exact: subgrp_divn.
  move => u [Hu Hu1].
  have F10:= (conjsg_normal N3 N2 Hu).
  have F11 : x =1 H.
    by move => z; rewrite -F10 -Hu1.
  rewrite /h1; apply/val_eqP => //=.
  apply/eqP; apply/val_eqP => //=.
  rewrite -(eq_filter (F11)).
  apply/eqP; apply: powerSeq_uniq_eq => //.
  by rewrite uniq_enum.
rewrite -(card1 (d := sub_finType (syset K p)) h1).
apply eq_card => x; apply/idP/idP => HH1.
  by rewrite (F6 x).
by rewrite -(eqP HH1).
Qed.

End Sylow3.

Unset Implicit Arguments.
