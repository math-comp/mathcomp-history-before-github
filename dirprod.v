(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Milne's lemmas for direct product                                  *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
Require Import ssreflect.
Require Import ssrbool.
Require Import ssrfun.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import fintype.
Require Import paths.
Require Import connect.
Require Import finset.
Require Import groups.
Require Import normal.
Require Import div.
Require Import automorphism.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section ExternalDirProd.

Variables gT1 gT2 : finGroupType.

Definition extprod_mulg (x y : gT1 * gT2) := (x.1 * y.1, x.2 * y.2).
Definition extprod_invg (x : gT1 * gT2) := (x.1^-1, x.2^-1).

Lemma extprod_mul1g : left_unit (1, 1) extprod_mulg.
Proof. case=> x1 x2; congr (_, _); exact: mul1g. Qed.

Lemma extprod_mulVg : left_inverse (1, 1) extprod_invg extprod_mulg.
Proof. by move=> x; congr (_, _); exact: mulVg. Qed.

Lemma extprod_mulgA : associative extprod_mulg.
Proof. by move=> x y z; congr (_, _); exact: mulgA. Qed.

Canonical Structure extprod_baseFinGroupType := Eval hnf in
  [baseFinGroupType of gT1 * gT2
     by extprod_mulgA, extprod_mul1g & extprod_mulVg].

Canonical Structure prod_group := FinGroupType extprod_mulVg.

Lemma group_setX : forall (H1 : {group gT1}) (H2 : {group gT2}),
  group_set (setX H1 H2).
Proof.
move=> H1 H2; apply/group_setP; split; first by rewrite inE !group1.
case=> [x1 x2] [y1 y2]; rewrite !inE; case/andP=> Hx1 Hx2; case/andP=> Hy1 Hy2.
by rewrite /= !groupM.
Qed.

Canonical Structure setX_group H1 H2 := Group (group_setX H1 H2).


Lemma setX_gen (H1 : {set gT1}) (H2 : {set gT2}):
 1 \in H1 -> 1 \in H2 -> <<setX H1 H2>> = setX <<H1>> <<H2>>.
Proof.
(* Too long but I could not find a shorter proof *)
move=> H1 H2 H11 H12; apply/eqP; rewrite eqset_sub; apply/andP; split.
  rewrite gen_subG; apply/subsetP => [[x1 x2]]; rewrite !inE /=.
  by case/andP => Hx1 Hx2;apply/andP; split; apply: mem_geng.
apply/subsetP => [[x1 x2]]; rewrite !inE /=; case/andP => Hx1 Hx2.
have ->: forall (x: gT1) (y: gT2), (x,y) = (x,1) * (1,y).
  by move=> x y; rewrite /mulg /= /extprod_mulg /= mulg1 mul1g.
rewrite groupM //.
  have F1: forall (x y: gT1), (x * y,(1: gT2)) = (x,1) * (y,1).
    by move=> x y; rewrite {2}/mulg /= /extprod_mulg /= mulg1.
  have F2: <<setX H1 1>> \subset <<setX H1 H2>>.
    apply: genSg; apply/subsetP => [[y1 y2]]; rewrite !inE /=.
    by case/andP => ->; move/eqP->.
  apply: (subsetP F2).
  pose f1 (x: gT1) := (x,unitg gT2).
  have P1f1: group_set (dom f1).
    apply/andP; split.
       by rewrite !inE eq_refl orbF; apply/forallP => x; rewrite mul1g.
    apply/subsetP => y _; rewrite !inE /= /f1.
    case E1: (_ == _); move/idP: E1=> E1; last by rewrite orbT.
    rewrite orbF; apply/forallP => y1 /=.
    by rewrite /f1 F1 (eqP E1) mul1g.
  have P2f1: {in dom f1 &, {morph f1 : x y / x * y}}.
    by move=> x y /=; rewrite /f1 {2}/mulg /= /extprod_mulg /= mul1g.
  pose mf1 := (Morphism P1f1 P2f1).
  have P3f1: forall H: {set gT1}, f1 @: H = setX H 1.
    move=> H.
    apply/eqP; rewrite eqset_sub; apply/andP; split; apply/subsetP => x.
      case/imsetP => y; rewrite !inE /f1 /= => Hy ->.
      by rewrite Hy eq_refl.
    case: x => xx1 xx2; rewrite !inE /=.
    by case/andP => Hxx1; move/eqP->; apply/imsetP; exists xx1.
  have P4f1: H1 \subset dom f1.
    apply/subsetP => y _.
    rewrite /f1 !inE /=; case E1: (_ == _); move/idP: E1 => E1; last by rewrite orbT.
    by rewrite orbF; apply/forallP => z /=; rewrite F1 (eqP E1) mul1g.
  by rewrite -P3f1 -(@gen_f_com _ _ mf1 _ P4f1) P3f1 !inE /= Hx1 eq_refl.
have F1: forall (x y: gT2), ((1: gT1), x * y) = (1, x) * (1, y).
  by move=> x y; rewrite {2}/mulg /= /extprod_mulg /= mulg1.
have F2: <<setX 1 H2>> \subset <<setX H1 H2>>.
  apply: genSg; apply/subsetP => [[y1 y2]]; rewrite !inE /=.
  by case/andP; move/eqP->; rewrite H11.
apply: (subsetP F2).
pose f1 (x: gT2) := (unitg gT1, x).
have P1f1: group_set (dom f1).
  apply/andP; split.
     by rewrite !inE eq_refl orbF; apply/forallP => x; rewrite mul1g.
  apply/subsetP => y _; rewrite !inE /= /f1.
  case E1: (_ == _); move/idP: E1=> E1; last by rewrite orbT.
  rewrite orbF; apply/forallP => y1 /=.
  by rewrite /f1 F1 (eqP E1) mul1g.
have P2f1: {in dom f1 &, {morph f1 : x y / x * y}}.
  by move=> x y /=; rewrite /f1 {2}/mulg /= /extprod_mulg /= mul1g.
pose mf1 := (Morphism P1f1 P2f1).
have P3f1: forall H: {set gT2}, f1 @: H = setX 1 H.
  move=> H.
  apply/eqP; rewrite eqset_sub; apply/andP; split; apply/subsetP => x.
    case/imsetP => y; rewrite !inE /f1 /= => Hy ->.
    by rewrite Hy eq_refl.
  case: x => xx1 xx2; rewrite !inE /=.
  by case/andP; move/eqP => -> Hxx1; apply/imsetP; exists xx2.
have P4f1: H2 \subset dom f1.
  apply/subsetP => y _.
  rewrite /f1 !inE /=; case E1: (_ == _); move/idP: E1 => E1; last by rewrite orbT.
  by rewrite orbF; apply/forallP => z /=; rewrite F1 (eqP E1) mul1g.
by rewrite -P3f1 -(@gen_f_com _ _ mf1 _ P4f1) P3f1 !inE /= Hx2 eq_refl.
Qed.

End ExternalDirProd.

Section InternalDirProd.

Variables gT : finGroupType.
Implicit Types G H : {group gT}.

Definition mulg_pair := prod_curry (@mulg gT).

Lemma mulg_setX : forall H1 H2, mulg_pair @: (setX H1 H2) = H1 * H2.
Proof. by move=> H1 H2; rewrite -curry_imset2X. Qed.

Lemma dirprod_isom : forall H1 H2 G,
  reflect [/\ {in H1, central H2}, G = (H1 <*> H2)%G & trivg (H1 :&: H2)]
          (morphic (setX H1 H2) mulg_pair && isom mulg_pair (setX H1 H2) G).
Proof.
move=> H1 H2 G; set H := {2}(setX H1 H2); rewrite /isom mulg_setX.
apply: (iffP and3P) => [[pM] | [cH ->{G} trH]].
  move/eqP=> defG; move/(injmorphicP pM); rewrite /= -/H => injp.
  have cH: {in H1, central H2}.
    move=> x1 Hx1 /= x2 Hx2; have:= morphP pM (1, x2) (x1, 1).
    rewrite /= !inE !group1 andbT !mul1g !mulg1; exact.
  split=> //; first by apply: val_inj; rewrite /= central_mulgenE.
  apply/subsetP=> x; case/setIP=> H1x H2x; apply/set1P.
  have:= injp (x, 1) (1, x); rewrite !inE ?group1 andbT /= !gsimp. 
  by case/(_ H1x H2x (erefl x)).
have pM: morphic H mulg_pair.
  apply/morphP=> [[x1 x2] [y1 y2]]; rewrite !inE.
  case/andP=> _ Hx2; case/andP=> Hy1 _.
  by rewrite /= mulgA -(mulgA x1) (cH _ Hy1) ?mulgA.
split=> //=; first by rewrite central_mulgenE.
apply/subsetP=> u; case/setD1P=> nu1 Hu.
have npu1: mulg_pair u <> 1.
  apply/eqP; apply: contra nu1; case: u Hu => x1 x2 Hu /=.
  rewrite -eq_invg_mul; move/eqP=> def_x2.
  rewrite -{x2}def_x2 inE groupV -in_setI /= in Hu *.
  by move/(subsetP trH): Hu; move/set1P->; rewrite invg1 eqxx.
have Du: u \in dom mulg_pair by apply/setUP; right; rewrite inE; exact/eqP.
rewrite inE Du andbT; rewrite /H in pM; apply/(kermorphicP pM) => //.
by rewrite inE Hu Du.
Qed.

Lemma smulg_1set : forall H1 H2, 
  (H1 * H2 == 1) = (H1 == 1 :> set _) && (H2 == 1 :> set _).
Proof.
move=> H1 H2; rewrite !eqset_sub (subset_trans _ (mulG_subr _ _)) ?sub1G //=.
by rewrite !andbT -gen_subG genM_mulgen gen_subG subUset.
Qed.

Lemma dirprod_normal_isom : forall H1 H2 G,
  reflect [/\ H1 <| G, H2 <| G, G = H1 * H2 :> set _ & trivg (H1 :&: H2)]
          (morphic (setX H1 H2) mulg_pair && isom mulg_pair (setX H1 H2) G).
Proof.
move=> H1 H2 G.
apply: (iffP (dirprod_isom H1 H2 G)) => [[cH -> trH] | [nH1 nH2 defG trH]].
  rewrite /normal_subset /= {-2 4}central_mulgenE // mulG_subl // mulG_subr //.
  rewrite //= !gen_subG !subUset normG /= andbC normG /=.
  split=> //; apply/normalP; apply: in_central_normal => //.
  exact: central_sym.
suff: {in H1, central H2}.
  by split=> //; apply: val_inj; rewrite /= central_mulgenE.
(* This ia a classic use of commutators *)
move=> x1 Hx1 /= x2 Hx2; apply/commgP; rewrite -in_set1.
apply: (subsetP trH); rewrite inE {1}commgEl commgEr.
rewrite groupMl (groupMr _ Hx2, groupV) //.
case/normalsubP: nH1 => sH1 nH1; case/normalsubP: nH2 => sH2 nH2.
rewrite -(nH1 _ (subsetP sH2 _ Hx2)) -(nH2 _ (subsetP sH1 _ Hx1)).
by rewrite !memJ_conjg Hx1 groupV.
Qed.

Definition dprod (A B: set gT): set gT :=
  if [&& group_set A , group_set B, A \subset 'C(B) & trivg (A :&: B)]
  then A * B else set0.

Infix "'*" := dprod (at level 40, left associativity).

Lemma dprodC A B: A '* B = B '* A.
Proof.
move=> A B; rewrite /dprod; do 2 (case: (group_set _) => //).
rewrite setIC; case: (trivg _); rewrite ?andbF //.
rewrite centralC; case CAB: (_ \subset _); move/centralP: CAB => CAB //=.
by apply/eqP; rewrite eqset_sub; apply/andP; split; apply/subsetP => x;
   case/imset2P => x1 x2 Hx1 Hx2 ->; [rewrite -CAB | rewrite CAB] => //;
   apply/imset2P; exists x2 x1.
Qed.

Lemma dprod1g (A: {group gT}): 1 '* A = A.
Proof.
move=> A; rewrite /dprod group_set_unit groupP sub1G.
suff ->: trivg (1 :&: A) by rewrite mul1g.
by apply/subsetP => x; rewrite inE; case/andP.
Qed.

Lemma dprodg1 (A: {group gT}): A '* 1 = A.
Proof.
by move=> A; rewrite dprodC dprod1g.
Qed.

Lemma dprodA A B C: (A '* B) '* C = A '* (B '* C).
Proof.
move=> A B C; rewrite /dprod.
have F1: forall (D: {set gT}), set0 * D = set0.
  by move=> D; apply/eqP; rewrite eqset_sub; apply/andP; split;
  apply/subsetP=> x; rewrite !inE //; case/imset2P=>x1 x2; rewrite inE.
have F2: forall (D: {set gT}), D * set0 = set0.
  by move=> D; apply/eqP; rewrite eqset_sub; apply/andP; split;
  apply/subsetP=> x; rewrite !inE //; case/imset2P=>x1 x2; rewrite inE.
case CA: (group_set A); move/idP: CA => CA; last by rewrite F1; case: (_ && _).
case CB: (group_set B); move/idP: CB => CB; last by rewrite !F1 !F2; do 2 case: (_ && _).
case CC: (group_set C); move/idP: CC => CC; last by rewrite !andbF !F2; case: (_ && _).
case SA: (A \subset 'C(B)); move/idP: SA => SA; last first.
  case SB: (B \subset 'C(C)); move/idP: SB => SB; last first.
    by rewrite !F1 !F2; do 2 case: (_ && _).
  case TB: (trivg (B :&: C)); move/idP: TB => TB /=; last by rewrite /group_set inE .
  case SA1: (A \subset 'C(B * C)); move/idP: SA1 => SA1; last first.
    by rewrite andbF; case: (_ && _); rewrite //= F1.
  case: SA; move: SA1; rewrite !(centralC  A) => SA1.
  apply: (subset_trans _ SA1).
  apply/subsetP=> x Hx; apply/imset2P; exists x (1: gT); rewrite ?mulg1 //.
  by apply: (group1 (Group CC)).
case SB: (B \subset 'C(C)); move/idP: SB => SB; last first.
  case TA: (trivg (A :&: B)); move/idP: TA => TA /=; last by rewrite /group_set !inE.
  case SC: (_ \subset _); move/idP: SC => SC; last by rewrite andbF /group_set inE.
  case SB; apply: (subset_trans  _ SC).
  apply/subsetP=> x Hx; apply/imset2P; exists (1: gT) x; rewrite // ?mul1g //.
  by apply: (group1 (Group CA)).
case TA: (trivg (A :&: B)); move/idP: TA => TA /=; last first.
  case TB: (trivg (B :&: C)); move/idP: TB => TB /=; last by rewrite /group_set inE.
  case TA1: (trivg (A :&: _)); move/idP: TA1 => TA1; last by rewrite !andbF /group_set inE.
  case TA; apply: (subset_trans _ TA1).
  apply/subsetP=> x; rewrite !inE; case/andP => -> H1.
  apply/imset2P; exists x (1: gT); rewrite // ?mulg1 //.
  by apply: (group1 (Group CC)).
case TB: (trivg (B :&: C)); move/idP: TB => TB /=; last first.
  case TA1: (trivg (A * _ :&: _)); move/idP: TA1 => TA1; last by rewrite !andbF /group_set inE.
  case TB; apply: (subset_trans _ TA1).
  apply/subsetP=> x; rewrite !inE; case/andP => H1 ->; rewrite andbT.
  apply/imset2P; exists (1: gT) x; rewrite // ?mul1g //.
  by apply: (group1 (Group CA)).
have ->: group_set ((Group CA) * (Group CB)).
  apply/comm_group_setP; apply: normalC.
  by apply: in_central_normal; apply/centralP.
have ->: group_set ((Group CB) * (Group CC)).
  apply/comm_group_setP; apply: normalC.
  by apply: in_central_normal; apply/centralP.
case TA1: (trivg _); move/idP: TA1 => TA1; last first.
  suff ->: trivg (A :&: B * C) = false by rewrite !andbF.
  apply/idP => HH; case TA1.
  apply/subsetP => x; rewrite !inE; case/andP; case/imset2P => x1 x2 Hx1 Hx2 -> Hx1x2.
  have Fx1: x1 \in 1%G.
     apply: (subsetP HH); rewrite inE Hx1.
     apply/imset2P; exists (x2^-1) (x1 * x2); rewrite // ?(groupV (Group CB)) //.
     rewrite mulgA -(centgP (subsetP SA _ Hx1) x2^-1) // ?(groupV (Group CB)) //.
     by rewrite -mulgA mulVg mulg1.
  have Fx2: x2 \in 1%G.
     apply: (subsetP TB); rewrite inE Hx2.
     by move: Fx1 Hx1x2; rewrite !inE; move/eqP->; rewrite mul1g.
  by move: Fx1 Fx2; rewrite !inE; move/eqP->; rewrite mul1g.
have ->: trivg (A :&: B * C).
  apply/subsetP => x; rewrite !inE; case/andP => Hx; 
    case/imset2P => x1 x2 Hx1 Hx2 Hx3; subst.
  have Fx2: x2 \in 1%G.
     apply: (subsetP TA1); rewrite inE Hx2 andbT.
     apply/imset2P; exists (x1 * x2) (x1^-1); rewrite // ?(groupV (Group CB)) //.
     rewrite (centgP (subsetP SA _ Hx)) // ?(groupV (Group CB)) //.
     by rewrite mulgA mulVg mul1g.
  have Fx1: x1 \in 1%G.
     apply: (subsetP TA); rewrite inE Hx1.
     by move: Fx2 Hx; rewrite !inE; move/eqP->; rewrite mulg1 andbT.
  by move: Fx1 Fx2; rewrite !inE; move/eqP->; rewrite mul1g.
case SA1: (_ \subset _); move/idP: SA1 => SA1.
  suff ->: A \subset 'C(B * C) by rewrite mulgA.
  apply/centralP => x Hx y; case/imset2P => y1 y2 Hy1 Hy2 ->.
  rewrite /commute.
  have: x * y1 \in A * B by apply/imset2P; exists x y1.
  move/(centralP SA1); move/(_ _ Hy2).
  rewrite /commute !mulgA => ->.
  move/(centralP SB): (Hy1); move/(_ _ Hy2)->.
  rewrite -!mulgA.
  by move/(centralP SA): Hx; move/(_ _ Hy1)->.
suff ->: A \subset 'C(B * C) = false by done.
apply/idP => HH; case SA1.
apply/centralP => x; case/imset2P => x1 x2 Hx1 Hx2 -> y Hy.
have Fx2y: x2 * y \in B * C by apply/imset2P; exists x2 y.
move/(centralP HH): (Hx1); move/(_ _ Fx2y).
rewrite /commute -!mulgA => ->; rewrite mulgA.
move/(centralP SB): (Hx2); move/(_ _ Hy)->.
by move/(centralP SA): Hx1; move/(_ _ Hx2)->; rewrite mulgA.
Qed.       
 
End InternalDirProd.
