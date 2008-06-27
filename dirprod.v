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
(* Require Import ssrnat. *)
Require Import seq.
(* Require Import paths. *)
(* Require Import connect. *)
(* Require Import div. *)
(* Require Import automorphism. *)
Require Import ssralg.
Require Import bigops.
Require Import fintype.
Require Import finset.
Require Import groups.
Require Import normal.

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

Notation Local inr := pair.
Notation Local inl := (fun x y  => (pair y x)).

Lemma morph_inl : {morph inl (1:gT2) : x y / x * y}.
Proof.
by move=> x y /=; rewrite {2}/mulg /= /extprod_mulg /= mul1g.
Qed.

Lemma morph_inr : {morph inr (1:gT1) : x y / x * y}.
Proof.
by move=> x y /=; rewrite {2}/mulg /= /extprod_mulg /= mul1g.
Qed.

Lemma setX_gen (H1 : {set gT1}) (H2 : {set gT2}):
 1 \in H1 -> 1 \in H2 -> <<setX H1 H2>> = setX <<H1>> <<H2>>.
Proof.
move=> H1 H2 *.
apply/eqP; rewrite eqset_sub gen_subG; apply/andP; split.
  apply/subsetP; case => x1 x2; move/setXP=>[Hx1 Hx2].
  by apply/setXP; split; apply:mem_gen.
have Hm : <<setX H1 1>> * <<setX 1 H2>> \subset <<setX H1 H2>>.
  by rewrite -[<<setX H1 H2 >>]mulGid mulgSS ?genS //;
  apply/subsetP; case=> h1 h2; move/setXP=> [Hh1 Hh2]; apply/setXP; split=>//;
  [move/set1P : Hh2->|move/set1P:Hh1->].
apply: (subset_trans _ Hm).
apply/subsetP; case=> [x1 x2]; move/setXP=> [Hx1 Hx2].
have Heq : (x1,x2) = (x1,1) * (1,x2).
by rewrite /mulg /= /extprod_mulg /= mul1g mulg1.
apply/mulsgP; exists (x1, 1:gT2) (1:gT1 ,x2); last by apply: Heq.
  pose minl := (Morphism (in2W morph_inl) : morphism _ setT).
  have ->: setX H1 1 = (minl @: H1).
    apply/setP; case=> [x01 x02]; apply/setXP/imsetP=>[[H01]|[x0 Hx0]].
      by move/set1P=> H02; exists (x01)=> //; rewrite H02.
   case=> -> ->; split => //; last by rewrite inE.
  rewrite -(setTI H1) -morphim_gen ?subsetT //.
  by apply/imsetP; rewrite /= setTI; exists x1.
pose minr := (Morphism (in2W morph_inr) : morphism _ setT).
have ->: setX 1 H2 = (minr @: H2).
  apply/setP; case=> [x01 x02]; apply/setXP/imsetP=>[[H01 H02]|[x0 Hx0]].
    by move/set1P: H01=> H01; exists (x02)=> //; rewrite H01.
 case=> -> ->; split => //; last by rewrite inE.
rewrite -(setTI H2) -morphim_gen ?subsetT //.
by apply/imsetP; rewrite /= setTI; exists x2.
Qed.

End ExternalDirProd.

Section InternalDirProd.

Variables gT : finGroupType.
Implicit Types G H : {group gT}.
Implicit Types A B C : {set gT}.

Definition mulg_pair := prod_curry (@mulg gT).

Lemma mulg_setX : forall H1 H2, mulg_pair @: (setX H1 H2) = H1 * H2.
Proof. by move=> H1 H2; rewrite -curry_imset2X. Qed.

Lemma dirprod_isom : forall H1 H2 G,
  reflect [/\ {in H1, centralised H2}, G = (H1 <*> H2)%G & trivg (H1 :&: H2)]
          (misom (setX H1 H2) G mulg_pair).
Proof.
move=> H1 H2 G; set H := setX _ _.
apply: (iffP misomP) => [ [pM] | [cH ->{G} trH]].
  pose f := morphm_morphism pM; case/isomP=> injf fHG.
  have cH: {in H1, centralised H2}.
    move=> x1 Hx1 /= x2 Hx2; have:= @morphM _ _ _ f (1, x2) (x1, 1) => /=.
    rewrite !inE !group1 andbT morphmE /= !mulg1 !mul1g; exact.
  have defG: G = (H1 <*> H2)%G.
    apply: val_inj; rewrite /= centralised_mulgenE // -fHG morphimEdom.
    by rewrite -curry_imset2X.
  split=> //; apply/subsetP=> x; case/setIP=> H1x H2x; apply/set1P.
  have:= injmP _ injf (x, 1) (1, x); rewrite !inE ?group1 andbT /=.
  by rewrite morphmE /= !gsimp; case/(_ H1x H2x (erefl x)).
have pM: morphic H mulg_pair.
  apply/morphicP=> [[x1 x2] [y1 y2]]; rewrite !inE /=.
  case/andP=> _ Hx2; case/andP=> Hy1 _.
  by rewrite /= mulgA -(mulgA x1) (cH _ Hy1) ?mulgA.
exists pM; apply/isomP; split; last first.
  by rewrite /= centralised_mulgenE // morphimEdom -curry_imset2X.
apply/subsetP=> u; case/setIP; rewrite !inE /=.
case: u => u1 u2 /= Hu; rewrite -eq_invg_mul; move/eqP=> def_u2.
rewrite -def_u2 ?groupV -in_setI /= in Hu *.
by move/(subsetP trH): Hu; move/set1P->; rewrite invg1 eqxx.
Qed.

Lemma dirprod_normal_isom : forall H1 H2 G,
  reflect [/\ H1 <| G, H2 <| G, G = H1 * H2 :> set _ & trivg (H1 :&: H2)]
          (misom (setX H1 H2) G mulg_pair).
Proof.
move=> H1 H2 G.
apply: (iffP (dirprod_isom H1 H2 G)) => [[cH -> trH] | [nH1 nH2 defG trH]].
  rewrite /normal /= {-2 4}centralised_mulgenE // mulG_subl // mulG_subr //.
  rewrite //= !gen_subG !subUset normG /= andbC normG /=.
  move/centsP: cH => cH; split=> //; apply: subset_trans (cent_subset _) => //.
  by rewrite centsC.
suff: {in H1, centralised H2}.
  by split=> //; apply: val_inj; rewrite /= centralised_mulgenE.
(* This ia a classic use of commutators *)
move=> x1 Hx1 /= x2 Hx2; apply/commgP; rewrite -in_set1.
apply: (subsetP trH); rewrite inE {1}commgEl commgEr.
rewrite groupMl (groupMr _ Hx2, groupV) //.
case/normalP: nH1 => sH1 nH1; case/normalP: nH2 => sH2 nH2.
rewrite -(nH1 _ (subsetP sH2 _ Hx2)) -(nH2 _ (subsetP sH1 _ Hx1)).
by rewrite !memJ_conjg Hx1 groupV.
Qed.

Definition central_product A B :=
  if A == 1 then B else if B == 1 then A else
  if [&& group_set A, group_set B & A \subset 'C(B)] then A * B else set0.

Infix "\*" := central_product (at level 40, left associativity).

Lemma smulg_1set : forall H1 H2,
  (H1 * H2 == 1) = (H1 == 1 :> set _) && (H2 == 1 :> set _).
Proof.
move=> H1 H2; rewrite !eqset_sub -{2}[1]mulGid mulgSS ?sub1G // !andbT.
by rewrite -gen_subG genM_mulgen gen_subG subUset.
Qed.

Lemma cprodC : commutative central_product.
Proof.
move=> A B; do 2!rewrite /(_ \* _); case: eqP => [->|_]; first by case: eqP.
rewrite andbCA centsC; case cAB: (B \subset _); last by rewrite !andbF.
by rewrite -normC // (subset_trans _ (cent_subset _)).
Qed.

Lemma cprod1g : left_unit 1 central_product.
Proof. by move=> A; rewrite /(_ \* _) eqxx. Qed.

Lemma cprodg1 : right_unit 1 central_product.
Proof. by move=> A; rewrite cprodC cprod1g. Qed.

Lemma cprodA : associative central_product.
Proof.
have ng0: @group_set gT set0 = false by apply/andP; case; rewrite inE.
have n01: (@set0 gT == 1) = false by rewrite eqset_sub sub1set inE andbF.
have mgenE := @cent_mulgenE gT (Group _) (Group _); simpl in mgenE.
have mul1E := @smulg_1set (Group _) (Group _); simpl in mul1E.
move=> A B C; case nA1: (A == 1); first by rewrite (eqP nA1) !cprod1g.
case nB1: (B == 1); first by rewrite (eqP nB1) cprod1g cprodg1.
case nC1: (C == 1); first by rewrite (eqP nC1) !cprodg1.
rewrite /central_product nA1 nB1 nC1.
case: and3P => [[gB gC cBC] | ngBC]; last first.
  rewrite n01 ng0 andbF.
  case: and3P => [[gA gB cAB] | _]; last by rewrite n01 ng0.
  rewrite mul1E // nA1 nB1 /=; case: and3P => // [[_ gC cABC]]; case: ngBC.
  split=> //; apply: subset_trans cABC; exact: (mulG_subr (Group gA)).
rewrite mul1E // nB1 nC1 gB gC /= -mgenE // groupP /=.
rewrite centsC gen_subG subUset -!(centsC A) /= andbA; symmetry.
case: andP => [[gA cAB] | _]; last by rewrite n01 ng0.
rewrite mul1E // nA1 nB1 /= -mgenE // groupP gen_subG subUset cBC andbT /=.
by rewrite !mgenE ?mulgA.
Qed.

Canonical Structure central_product_law := Monoid.Law cprodA cprod1g cprodg1.
Canonical Structure central_product_abelaw := Monoid.AbelianLaw cprodC.

Lemma cprodGE : forall G H, G \subset 'C(H) -> G \* H = G * H.
Proof.
move=> G H cGH; rewrite /(G \* H) !groupP cGH andbT.
by do 2![case: eqP => [-> | _]; first by rewrite gsimp].
Qed.

CoInductive cprod_spec A B C : Prop :=
  CprodSpec H1 H2 of A = H1 & B = H2 & A * B = C & A \subset 'C(B).

Lemma cprodP : forall A B,
  A != 1 -> B != 1 -> A \* B = set0 \/ cprod_spec A B (A \* B).
Proof.
move=> A B nA1 nB1; rewrite /(A \* B) (negbET nA1) (negbET nB1).
case: and3P => [[gA gB cAB] | _]; [right | by left].
by exists (Group gA) (Group gB).
Qed.

Lemma cprodGP : forall A B G, A \* B = G -> cprod_spec A B G.
Proof.
move=> A B G AB_G; have:= @cprodP A B; rewrite AB_G; move: AB_G.
rewrite /(A \* B); case: eqP => [-> -> _ | _].
  by exists (1%G : {group gT}) G; rewrite // ?mul1g ?sub1G.
case: eqP => [-> -> _ | _ _].
  by exists G (1%G : {group gT}); rewrite ?mulg1 // centsC sub1G.
by case=> //; move/setP; move/(_ 1); rewrite group1 inE.
Qed.

Lemma bigcprodE : forall I (r : seq I) P F G,
  \big[central_product/1]_(i <- r | P i) F i = G
  -> \prod_(i <- r | P i) F i = G.
Proof.
move=> I r P F; rewrite -!(big_filter r).
elim: {r}filter => [|i r IHr] G; rewrite !(big_seq0, big_adds) //=.
by case/cprodGP=> _ G' _ defG' <- _; rewrite defG' (IHr _ defG').
Qed.

Lemma cprod0g : left_zero set0 central_product.
Proof.
move=> A; rewrite /(_ \* A) eqset_sub sub1set {1}/group_set !inE andbF.
exact: if_same.
Qed.

Lemma cprodg0 : right_zero set0 central_product.
Proof. by move=> A; rewrite cprodC cprod0g. Qed.

Definition direct_product A B := if trivg (A :&: B) then A \* B else set0.

Infix "\x" := direct_product (at level 40, left associativity).

Lemma dprodC : commutative direct_product.
Proof. by move=> A B; rewrite /(A \x B) setIC cprodC. Qed.

Lemma dprod1g : left_unit 1 direct_product.
Proof. by move=> A; rewrite /(1 \x A) /trivg subsetIl cprod1g. Qed.

Lemma dprodg1 : right_unit 1 direct_product.
Proof. by move=> A; rewrite dprodC dprod1g. Qed.

Lemma dprodA : associative direct_product.
Proof.
move=> A B C; case: (A =P 1) => [-> |]; [by rewrite !dprod1g | move/eqP=> nA1].
case: (B =P 1) => [-> |]; [by rewrite dprod1g dprodg1 | move/eqP=> nB1].
case: (C =P 1) => [-> |]; [by rewrite !dprodg1 | move/eqP=> nC1].
rewrite /direct_product (fun_if (central_product A)).
rewrite (fun_if (central_product^~ C)) cprodA cprodg0 cprod0g.
case: (cprodP nA1 nB1) => [-> | [G _ -> _ mGB _]].
  by rewrite cprod0g !if_same.
rewrite -cprodA -{}mGB; case: (cprodP nB1 nC1) => [-> | [H K -> -> <- _]].
  by rewrite cprodg0 !if_same.
case trGH: (trivg (G :&: H)); case trHK: (trivg (H :&: K));
  rewrite ?if_same //; last first.
- case: ifP => // trGHK; case/idP: trGH; apply: subset_trans trGHK.
  by rewrite setIS ?mulG_subl.
- case: ifP => // trGHK; case/idP: trHK; apply: subset_trans trGHK.
  by rewrite setSI ?mulG_subr.
rewrite !ifE; congr if_expr; apply/idP/idP=> trGHK.
  apply: subset_trans trHK; apply/subsetP=> z; case/setIP.
  case/imset2P=> x y Gx Hy z_xy Kz.
  suff x1: x \in 1%G by rewrite inE Kz z_xy (set1P _ _ x1) mul1g Hy.
  rewrite -groupV (subsetP trGHK) // inE groupV Gx -(mulgK z x^-1).
  by rewrite {1}z_xy mulKg mem_mulg ?groupV.
apply: subset_trans trGH; apply/subsetP=> x; case/setIP=> Gx.
case/imset2P=> y z Hy Kz x_yz.
suff z1: z \in 1%G by rewrite inE Gx x_yz (set1P _ _ z1) mulg1.
rewrite -groupV (subsetP trGHK) // inE groupV Kz -(mulKg x z^-1).
by rewrite {2}x_yz mulgK mem_mulg ?groupV.
Qed.

Canonical Structure direct_product_law := Monoid.Law dprodA dprod1g dprodg1.
Canonical Structure direct_product_abelaw := Monoid.AbelianLaw dprodC.

Lemma dprodGP : forall A B G,
  A \x B = G -> cprod_spec A B G /\ trivg (A :&: B).
Proof.
move=> A B G; rewrite /(A \x B); case: trivg; first by move/cprodGP.
by move/setP; move/(_ 1); rewrite group1 inE.
Qed.

Lemma bigdprodE : forall I (r : seq I) P F G,
  \big[direct_product/1]_(i <- r | P i) F i = G
  -> \prod_(i <- r | P i) F i = G.
Proof.
move=> I r P F; rewrite -!(big_filter r).
elim: {r}filter => [|i r IHr] G; rewrite !(big_seq0, big_adds) //=.
by case/dprodGP=> [[_ G' _ defG' <- _] _]; rewrite defG' (IHr _ defG').
Qed.

End InternalDirProd.
