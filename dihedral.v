(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div fintype connect.
Require Import finset groups cyclic ssralg.

Import GroupScope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition involg (gT : finGroupType) (a : gT) := involutive (mulg a).

Lemma involgKP : forall (gT : finGroupType) (a : gT),
  reflect (involg a) (a * a == 1).
Proof.
move=> gT a; apply:(iffP eqP)=> Ha; first by move=> x; rewrite mulgA Ha mul1g.
by rewrite -{2}(mulg1 a).
Qed.

Lemma invol_conjg_expn : forall (gT:finGroupType) (a t:gT),
  (involg t) -> forall n, a ^+ n ^t = (a ^ t) ^+n.
Proof.
move=> gT a t Hi; move/involgKP: Hi=> Heq.
elim =>[|n IHn]; first by rewrite !expg0 conj1g.
by rewrite !expgS conjMg IHn. 
Qed.

Lemma involgen_order : forall (gT: finGroupType) (t: gT),
  (involg t) -> t !=1 -> #[t] = 2.
move=> gT t Hi; have:= (trivg_card1 <[t]>); rewrite cycle_eq1=>-> /=.
move/involgKP: Hi; have:= (expgS t 1); rewrite expg1=> <-.
move/order_inf;move: (order_gt0 t); rewrite /order /=.
case : #|<[t]>| => [|n0] ; first by rewrite ltn0.
by case :n0=> [|n1] // _; rewrite !ltnS leq_eqVlt ltn0 orbF; move/eqP->.
Qed.

Lemma involgen_group2 : forall (gT:finGroupType) (t:gT),
  (involg t) -> t != 1 -> <[t]> = [set 1;t].
Proof.
move=> gT t Hi Hn1; apply/eqP.
rewrite eqEsubset subUset !sub1set group1 cycle_id !andbT.
have G1t: (group_set [set 1; t]).
apply/group_setP; split; first by apply/setUP; left; apply/set1P.
move=> x y; move/setUP; case; move/set1P->; move/setUP; case; move/set1P->;
  rewrite ?mul1g ?mulg1 inE !in_set1 ?eq_refl ?orbT //.
  by move/involgKP: Hi->.
by rewrite -[[set 1; t]]/(gval (group G1t)) gen_subG /= sub1set inE !in_set1 eq_refl ?orbT.
Qed.

Module Type  Dihedral.
Parameter gT: finGroupType.
Parameter D : {group gT}.
Parameter c : gT.
Axiom dhntriv : (cycle c) != 1.
Axiom dhsub : c \in D.
Axiom dhindex : #|D : (cycle c)| = 2.
Axiom dhinvol : forall t, (t \in (D:\: (cycle c))) -> involg t.
End Dihedral.

Section Involutions.
Variable gT: finGroupType.
Variable D : {group gT}.
Variable c : gT.
Hypothesis dhsub : c \in D.
Hypothesis dhindex : #|D : (cycle c)| = 2.

Notation Local C := (cycle c).

Lemma D_order : (#|C| * 2 = #|D|)%nat.
Proof.
move: dhsub; rewrite -cycle_subG; move/LaGrange.
by rewrite dhindex.
Qed.

Variable t :gT.
Variable Ht : t \in D:\:C.
Hypothesis Hit : involg t.

Lemma DmC_coset : D :\: C = C :* t.
Proof.
apply/eqP; rewrite eq_sym eqEcard card_rcoset.
have:= (cardsID C D); rewrite setIC; move: dhsub.
rewrite -cycle_subG; move/setIidPl ->; move/eqP.
rewrite -D_order mulnSr muln1 eqn_addl; move/eqP ->; rewrite leqnn andbT.
apply/subsetP=> x Hx; rewrite inE andbC; apply/andP; split;
move/rcosetP:Hx=> [a Heq] ->; move: Ht; rewrite inE; move/andP=> [HnC].
  move: dhsub; rewrite -cycle_subG; move/subsetP; move/(_ _ Heq).
  by move/groupMl ->.
by move=> [_]; rewrite (groupMl _ Heq).
Qed.

Lemma DmC_involP : 
 reflect (forall u, (u \in D:\:C) -> involg u)
 (c ^ t == c ^-1).
Proof.
rewrite DmC_coset; apply:(iffP eqP).
  move=> Heq x; move/rcosetP=> [a Ha]->.
  move/cycleP: Ha => [n ->]; apply/involgKP; move/involgKP: Hit.
  rewrite  -{2}(invgK t) -eq_mulgV1 =>Hti.
  rewrite {1}(eqP Hti) -mulgA -/(conjg (c ^+ n) t).
  by rewrite (invol_conjg_expn _ Hit) Heq expVgn mulgV.
move=> Hix; apply/eqP; rewrite eq_sym eq_mulVg1 invgK conjgE; move: Hit.
move/involgKP; rewrite -{2}(invgK t) -eq_mulgV1 mulgA; move/eqP<-.
apply/involgKP; apply: (Hix (c * t)); apply/rcosetP; exists c => //.
by apply:cycle_id.
Qed.

End Involutions.

Module DihedralTheory (Dh:Dihedral).

Notation Local gT := Dh.gT.
Notation Local D := Dh.D.
Notation Local c := Dh.c.
Notation Local dhntriv := Dh.dhntriv.
Notation Local dhsub := Dh.dhsub.
Notation Local dhindex := Dh.dhindex.
Notation Local dhinvol := Dh.dhinvol.

Notation Local C := (cycle c).

Lemma DmCJ : forall a y, a \in C -> y \in D:\:C -> a ^ y = a ^-1.
Proof.
move=> a y Ha Hy; move/cycleP:Ha=> [n] ->; move/involgKP:(dhinvol Hy) => Heq.
apply/eqP; rewrite eq_sym eq_mulVg1 invgK conjgE mulgA.
move: Heq; rewrite -{2}(invgK y) -eq_mulgV1; move/eqP<-.
apply/involgKP; apply:dhinvol; rewrite (DmC_coset dhsub dhindex Hy).
apply/rcosetP; exists (c^+n) => //; apply:mem_cycle.
Qed.

Lemma Dgen : forall t, t\in D:\:C -> <<[set c * t; t]>> = D.
Proof.
move=> t Ht; apply/eqP; rewrite eqEcard.
have c2sub : <<[set c * t; t]>> \subset D.
  rewrite gen_subG subUset !sub1set (groupMl _ dhsub).
  by move:Ht; rewrite inE; move/andP=>[_] ->.
rewrite c2sub /=.
have: C \proper <<[set c* t; t]>>.
  rewrite properE gen_subG sub1set; apply/andP; split.
    apply/generatedP=> G; rewrite subUset !sub1set; move/andP=> [Gct Gt].
    rewrite -(mulg1 c); move/involgKP: (dhinvol Ht); move/eqP <-; rewrite mulgA.
    by rewrite (groupMl _ Gct).
  apply/subsetPn; exists t; first by apply:mem_gen; rewrite !inE eq_refl orbT.
  by move: Ht; rewrite inE; move/andP=> [H].
rewrite properEcard; move/andP=> [HCsub HCcard].
rewrite -(D_order dhsub dhindex); move: (cardSg HCsub).
move/dvdnP=> [k Hk]; rewrite Hk mulnC leq_mul2r.
move/eqP: Hk; rewrite -(LaGrange HCsub) mulnC /= eqn_mul2r.
move:(cardG_gt0 [group of C]); rewrite eqn0Ngt /= => -> /=.
move/eqP<-.
case e: #|<<[set c * t; t]>> : C|=>[|n0];
  first by move/eqP: e; rewrite eqn0Ngt indexg_gt0.
rewrite ltnS; move:e; case n0=>[|n1]; last by rewrite ltn0Sn.
by move/(index1g HCsub)=>Hcsub; move:HCcard; injection Hcsub=>->; rewrite ltnn.
Qed.

End DihedralTheory.

Section InvoGen.

Variable gT:finGroupType.
Variables s t : gT.
Hypothesis His : involg s.
Hypothesis Hit: involg t.
Hypothesis Hdistinct: s != t.
Hypothesis Htn1 : t != 1.
Hypothesis Hsn1 : s != 1.

Notation Local D := <<[set s; t]>>.
Notation Local C := (cycle (s * t)).

Lemma Cntriv : C != 1.
Proof.
apply/eqP; apply/trivgP; rewrite gen_subG sub1set inE; move: (His 1); move/eqP.
by rewrite mulg1 -{2}(invgK s) -eq_mulgV1; move/eqP->; rewrite -eq_mulVg1.
Qed.

Lemma DC_invol : (s * t) ^ t = (s * t) ^-1.
Proof.
apply/eqP; move/involgKP: Hit; rewrite conjgE -mulgA invMg; move/eqP->.
by move/involgKP: His; rewrite mulg1 -{2}(invgK s) -eq_mulgV1; move/eqP<-.
Qed.

Lemma DC_norm : t \in 'N_D(C).
Proof.
rewrite inE; apply/andP; split.
  by apply/generatedP=> G; rewrite subUset !sub1set; move/andP=> [_].
rewrite -sub1set; apply/normsP => x; move/set1P->.
rewrite -genJ conjg_set1 DC_invol; exact: cycleV.
Qed.

Lemma DCt : C * (cycle t) = D.
Proof.
suff : (s \in C * (cycle t)) && (t \in C * (cycle t)).
  move=> Hst; apply/eqP; rewrite eqEsubset.
  apply/andP; split; last first.
  have GCt : (group_set (C * <[t]>)).
    apply/comm_group_setP; apply:commute_sym; apply:normC; move: DC_norm.
    by move/setIP=>[_]; rewrite -sub1set -gen_subG.
  by rewrite -[C * <[t]>]/(gval (group GCt)) gen_subG subUset !sub1set /=.
by apply: mul_subG; rewrite gen_subG ?subUset sub1set ?groupM ?mem_gen // 
  in_setU !in_set1 eq_refl ?orbT.
rewrite -{1}(mulg1 s) -(mulgV t) -{5}(mul1g t).
move/involgKP: Hit; rewrite -{2}(invgK t) -eq_mulgV1 mulgA; move/eqP<-.
by rewrite !mem_mulg ?group1 ?mem_gen ?inE ?eq_refl.
Qed.

Lemma Cnotst : ~~ ((s \in C) || (t \in C)).
Proof.
apply/negP =>H; have {H}Hboth: (s \in C) && (t\in C).
  by case/orP: H=> H; move: (cycle_id (s * t)); 
    rewrite ?(groupMl _ H) ?(groupMr _ H) => Hcyc; rewrite H Hcyc.
case e: (2 %| #[s * t]); move/andP:Hboth=> [Hsin]; move/cycleP=>[n0 H];
move: (cycleX (s * t) n0); rewrite -H; last first.
  by move/cardSg; rewrite [#|_|]involgen_order // e.
move/cycleP:Hsin =>[n1 H1]; move: (cycleX (s * t) n1); rewrite -H1=> sCsub tCsub.
set SG := [set H : {group gT} | (H \subset C) && (#|H| == 2)].
rewrite /= in SG; have :[group of <[s]>] \in SG.
by rewrite inE /= sCsub; move: (involgen_order His Hsn1); rewrite /order => ->.
have :[group of <[t]>] \in SG.
by rewrite inE /= tCsub; move: (involgen_order Hit Htn1); rewrite /order => ->.
rewrite /SG (cycle_sub_group e) !in_set1.
move/eqP<-; move/eqP; rewrite /= /group =>Hst.
have {Hst}: <[s]> = <[t]> by rewrite -![<[_]>]/(gval _) /cycle_group Hst /=.
rewrite (involgen_group2 Hit Htn1) (involgen_group2 His Hsn1); move/eqP.
rewrite eqEsubset !subUset !sub1set !inE eq_refl (negbTE Hsn1) (negbTE Htn1) /=.
by rewrite (negbTE Hdistinct).
Qed.

Lemma Ctcap : C :&: <[t]> = 1.
Proof.
move: Cnotst; rewrite negb_or; move/andP=>[_] HtnC.
rewrite (involgen_group2 Hit Htn1) setIUr.
move: (group1 [group of C]); rewrite -sub1set /=.
move/setIidPr->; move: (subsetIr C [set t]).
rewrite subset1; case/orP; last by move/eqP=>->; rewrite setU0.
by move/eqP; move/setIidPr; rewrite sub1set=>H; move: HtnC; rewrite H.
Qed.


Lemma DCindex : #|D : C| = 2.
Proof.
move: (divgI [group of D] [group of C]).
rewrite /= -DCt -group_modl ?subset_refl // -(setIC C <[t]>) Ctcap mulg1.

rewrite (TI_cardMg Ctcap) mulKn ?order_gt0 // =><- /=.
by rewrite [#|<[_]>|](involgen_order Hit Htn1).
Qed.

End InvoGen.

Module Involuted : Dihedral.
Variable gT:finGroupType.
Variables s t : gT.
Hypothesis His : involg s.
Hypothesis Hit: involg t.
Hypothesis Hdistinct: s != t.
Hypothesis Htn1 : t != 1.
Hypothesis Hsn1 : s != 1.

Definition D := [group of <<[set s; t]>>].
Definition c := (s * t).
Definition dhntriv : (cycle c) != 1 := (Cntriv His Hdistinct).
Lemma dhsub : c \in D.
Proof.
apply/generatedP=> G; rewrite subUset !sub1set; move/andP=>[Gs Gt].
by apply:groupM.
Qed.
Definition dhindex : #|D : (cycle c)| = 2 := 
  DCindex His Hit Hdistinct Htn1 Hsn1.
Lemma dhinvol : forall t, (t \in (D:\: (cycle c))) -> involg t.
Proof.
apply/(DmC_involP dhsub dhindex _ Hit ); last first.
  apply/eqP; apply:DC_invol; [exact:His|exact:Hit].
have:= (Cnotst His Hit Hdistinct Htn1 Hsn1); rewrite negb_or inE.
move/andP=> [_] -> /=; rewrite -(DCt His Hit) -{1}(mul1g t).
by apply:mem_mulg; rewrite ?group1 ?cycle_id.
Qed.
End Involuted.
