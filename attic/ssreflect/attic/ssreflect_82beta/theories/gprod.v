(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Partial, semidirect, central and direct products.                  *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq ssralg.
Require Import bigops fintype finset groups morphisms normal.
Require Import group_perm automorphism.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section Defs.

Variables gT : finGroupType.
Implicit Types A B C : {set gT}.

Definition partial_product A B :=
  if A == 1 then B else if B == 1 then A else
  if [&& group_set A, group_set B & B \subset 'N(A)] then A * B else set0.

Definition semidirect_product A B :=
  if A :&: B \subset 1%G then partial_product A B else set0.

Definition central_product A B :=
  if A \subset 'C(B) then partial_product A B else set0.

Definition direct_product A B :=
  if A :&: B \subset 1%G then central_product A B else set0.

Definition complements_to_in A B :=
  [set K : {group gT} | (A :&: K == 1) && (A * K == B)].

Definition splits_over B A := complements_to_in A B != set0.

(* Product remainder functions *)

(* Deferring the left variant, as we don't need it for the moment
Definition remgl A B x := repr (A :&: x *: B).
Definition divgl A B x := (remgl A B x)^-1 * x.
*)
Definition remgr A B x := repr (A :* x :&: B).
Definition divgr A B x := x * (remgr A B x)^-1.

End Defs.

Implicit Arguments partial_product [].
Implicit Arguments semidirect_product [].
Implicit Arguments central_product [].
Implicit Arguments direct_product [].
Notation pprod := (partial_product _).
Notation sdprod := (semidirect_product _).
Notation cprod := (central_product _).
Notation dprod := (direct_product _).

Notation "G ><| H" := (sdprod G H) (at level 40, left associativity).
Notation "G \* H" := (cprod G H) (at level 40, left associativity).
Notation "G \x H" := (dprod G H) (at level 40, left associativity).

Notation "[ 'complements' 'to' A 'in' B ]" := (complements_to_in A B)
  (at level 0, format "[ 'complements'  'to'  A  'in'  B ]") : group_scope.

Notation "[ 'splits' B , 'over' A ]" := (splits_over B A)
  (at level 0, format "[ 'splits'  B ,  'over'  A ]") : group_scope.

(* Prenex Implicits remgl divgl. *)
Prenex Implicits remgr divgr.

Section InternalDirProd.

Variables gT : finGroupType.
Implicit Types A B C : {set gT}.
Implicit Types G H K : {group gT}.

Notation Local pprod := (partial_product gT).
Notation Local sdprod := (semidirect_product gT) (only parsing).
Notation Local cprod := (central_product gT) (only parsing).
Notation Local dprod := (direct_product gT) (only parsing).

Lemma pprod1g : left_unit 1 pprod.
Proof. by move=> A; rewrite /pprod eqxx. Qed.

Lemma pprodg1 : right_unit 1 pprod.
Proof. by move=> A; rewrite /pprod eqxx; case: eqP. Qed.

CoInductive are_groups A B : Prop := AreGroups G H of A = G & B = H.

Lemma group_not0 : forall G, set0 <> G.
Proof. by move=> G G0; have:= group1 G; rewrite -G0 inE. Qed.

Lemma pprodP : forall A B G,
  pprod A B = G -> [/\ are_groups A B, A * B = G & B \subset 'N(A)].
Proof.
rewrite /pprod => A B G; have Gnot0 := @group_not0 G; pose g1 := [1 gT]%G.
do 2?case: eqP => [-> ->| _].
- by rewrite mul1g norms1; split; first exists g1 G.
- by rewrite mulg1 sub1G; split; first exists G g1.
by case: and3P => // [[gA gB nBA]]; split; first exists (Group gA) (Group gB).
Qed.

Lemma pprodE : forall G H, H \subset 'N(G) -> pprod G H = G * H.
Proof.
move=> G H nGH; rewrite /pprod nGH !groupP /=.
by do 2?case: eqP => [-> | _]; rewrite ?mulg1 ?mul1g.
Qed.

Lemma pprodEgen : forall G H, H \subset 'N(G) -> pprod G H = G <*> H.
Proof. by move=> G H nGH; rewrite pprodE ?norm_mulgenEr. Qed.

Lemma mulg0 : right_zero (@set0 gT) mulg.
Proof.
by move=> A; apply/setP=> x; rewrite inE; apply/imset2P=> [[y z]]; rewrite inE.
Qed.

Lemma mul0g : left_zero (@set0 gT) mulg.
Proof.
by move=> A; apply/setP=> x; rewrite inE; apply/imset2P=> [[y z]]; rewrite inE.
Qed.

(* Properties of the remainders *)
(* Outcommented left variant as not currently used -- GG
Lemma remgl_id : forall A G x y, y \in G -> remgl A G (x * y) = remgl A G x.
Proof. by move=> A G x y Gy; rewrite {1}/remgl lcosetM lcoset_id. Qed.

Lemma remglP : forall A G x, (remgl A G x \in A :&: x *: G) = (x \in A * G).
Proof.
move=> A G x; set y := remgl A G x; apply/idP/mulsgP=> [|[a g Aa Gg x_ag]].
  rewrite inE lcoset_sym mem_lcoset; case/andP=> Ay Gy'x.
  by exists y (y^-1 * x); rewrite ?mulKVg.
by apply: (mem_repr a); rewrite inE Aa lcoset_sym mem_lcoset x_ag mulKg.
Qed.

Lemma divgl_eq : forall A B x, x = remgl A B x * divgl A B x.
Proof. by move=> A B x; rewrite mulKVg. Qed.

Lemma divgl_id : forall A G x y,
  y \in G -> divgl A G (x * y) = divgl A G x * y.
Proof. by move=> A G x y Gy; rewrite /divgl remgl_id ?mulgA. Qed.

Lemma mem_remgl : forall A G x, x \in A * G -> remgl A G x \in A.
Proof. by move=> A G x; rewrite -remglP; case/setIP. Qed.

Lemma mem_divgl : forall A G x, x \in A * G -> divgl A G x \in G.
Proof.
by move=> A G x; rewrite -remglP inE lcoset_sym mem_lcoset; case/andP.
Qed.
*)

Lemma remgrMl : forall H B x y, y \in H -> remgr H B (y * x) = remgr H B x.
Proof. by move=> H B x y Hy; rewrite {1}/remgr rcosetM rcoset_id. Qed.

Lemma remgrP : forall H B x, (remgr H B x \in H :* x :&: B) = (x \in H * B).
Proof.
move=> H B x; set y := _ x; apply/idP/mulsgP=> [|[g b Hg Bb x_gb]].
  rewrite inE rcoset_sym mem_rcoset; case/andP=> Hxy' By.
  by exists (x * y^-1) y; rewrite ?mulgKV.
by apply: (mem_repr b); rewrite inE rcoset_sym mem_rcoset x_gb mulgK Hg.
Qed.

Lemma remgr1 : forall H K x, x \in H -> remgr H K x = 1.
Proof. by move=> H K x Hx; rewrite /remgr rcoset_id ?repr_group. Qed.

Lemma divgr_eq : forall A B x, x = divgr A B x * remgr A B x.
Proof. by move=> *; rewrite mulgKV. Qed.

Lemma divgrMl : forall H B x y,
  x \in H -> divgr H B (x * y) = x * divgr H B y.
Proof. by move=> H B x y Hx; rewrite /divgr remgrMl ?mulgA. Qed.

Lemma divgr_id : forall H K x, x \in H -> divgr H K x = x.
Proof. by move=> H K x Hx; rewrite /divgr remgr1 // invg1 mulg1. Qed.

Lemma mem_remgr : forall H B x, x \in H * B -> remgr H B x \in B.
Proof. by move=> H B x; rewrite -remgrP; case/setIP. Qed.

Lemma mem_divgr : forall H B x, x \in H * B -> divgr H B x \in H.
Proof.
by move=> H B x; rewrite -remgrP inE rcoset_sym mem_rcoset; case/andP.
Qed.

Section DisjointRem.

Variables H K : {group gT}.

Hypothesis trHK : H :&: K = 1.

Lemma remgr_id : forall x, x \in K -> remgr H K x = x.
Proof.
move=> x Kx; apply/eqP; rewrite eq_mulgV1 -in_set1 -[[set 1]]trHK inE.
rewrite -mem_rcoset groupMr ?groupV // -in_setI remgrP.
by apply: subsetP Kx; exact: mulG_subr.
Qed.

Lemma remgrMid : forall x y, x \in H -> y \in K -> remgr H K (x * y) = y.
Proof. by move=> x y Hx Ky; rewrite remgrMl ?remgr_id. Qed.

Lemma divgrMid : forall x y, x \in H -> y \in K -> divgr H K (x * y) = x.
Proof. by move=> x y Hx Ky; rewrite /divgr remgrMid ?mulgK. Qed.

End DisjointRem.

(* Complements, and splitting. *)

Lemma complP : forall K A B,
  reflect (A :&: K = 1 /\ A * K = B) (K \in [complements to A in B]).
Proof. by move=> K A B; apply: (iffP setIdP); case; split; apply/eqP. Qed.

Lemma splitsP : forall B A,
  reflect (exists K, K \in [complements to A in B]) [splits B, over A].
Proof. by move=> B A; exact: set0Pn. Qed.

Lemma complgC : forall H K G,
  (H \in [complements to K in G]) = (K \in [complements to H in G]).
Proof.
move=> H K G; rewrite !inE setIC; congr (_ && _).
by apply/eqP/eqP=> defG; rewrite -(comm_group_setP _) // defG groupP.
Qed.

Section NormalComplement.

Variables H K G : {group gT}.

Hypothesis kH_K : K \in [complements to H in G].
Hypothesis nHG : H <| G.

Lemma remgrM : {in G &, {morph remgr H K : x y / x * y}}.
Proof.
case/normalP: nHG => _; case/complP: kH_K => trHK <- nHHK x y HKx HKy.
rewrite {1}(divgr_eq H K y) mulgA (conjgCV x) {2}(divgr_eq H K x) -2!mulgA.
rewrite mulgA remgrMl; last by rewrite groupMl -?mem_conjg ?nHHK ?mem_divgr.
by rewrite remgr_id // groupMl ?mem_remgr.
Qed.

End NormalComplement.

(* Semi-direct product *)

Lemma sdprod1g : left_unit 1 sdprod.
Proof. by move=> A; rewrite /sdprod subsetIl pprod1g. Qed.

Lemma sdprodg1 : right_unit 1 sdprod.
Proof. by move=> A; rewrite /sdprod subsetIr pprodg1. Qed.

Lemma sdprodP : forall A B G,
  A ><| B = G -> [/\ are_groups A B, A * B = G, B \subset 'N(A) & A :&: B = 1].
Proof.
rewrite /sdprod => A B G; case: ifP => [trAB|_]; last by case/group_not0.
case/pprodP=> gAB defG nBA; split=> {defG nBA}//.
by case: gAB trAB => H K -> ->; move/trivgP.
Qed.

Lemma sdprodE : forall G H, H \subset 'N(G) -> G :&: H = 1 -> G ><| H = G * H.
Proof. by move=> G H nGH trGH; rewrite /sdprod trGH subxx pprodE. Qed.

Lemma sdprodEgen : forall G H,
  H \subset 'N(G) -> G :&: H = 1 -> G ><| H = G <*> H.
Proof. by move=> G H nGH trGH; rewrite sdprodE ?norm_mulgenEr. Qed.

Lemma sdprod_normal_compl : forall G H K,
  H ><| K = G <-> H <| G /\ H \in [complements to K in G].
Proof.
move=> G H K; rewrite complgC; split=> [|[]].
  case/sdprodP=> _ <- nHK trHK.
  by rewrite /normal mulG_subl mul_subG ?normG // inE trHK !eqxx.
case/andP=> _ nHG; case/complP=> trHK eHK.
by rewrite sdprodE // (subset_trans _ nHG) // -eHK mulG_subr.
Qed.

Lemma sdprod_card : forall G A B, A ><| B = G -> (#|A| * #|B|)%N = #|G|.
Proof. by move=> G A B; case/sdprodP=> [[H K -> ->] <- _]; move/TI_cardMg. Qed.

(* Central product *)

Lemma cprod1g : left_unit 1 cprod.
Proof. by move=> A; rewrite /cprod sub1G pprod1g. Qed.

Lemma cprodg1 : right_unit 1 cprod.
Proof. by move=> A; rewrite /cprod cents1 pprodg1. Qed.

Lemma cprodP : forall A B G,
  A \* B = G -> [/\ are_groups A B, A * B = G & A \subset 'C(B)].
Proof.
rewrite /cprod => A B G; case: ifP => [cAB|_]; last by case/group_not0.
by case/pprodP.
Qed.

Lemma cprodE : forall G H, G \subset 'C(H) -> G \* H = G * H.
Proof. by move=> G H cGH; rewrite /cprod cGH pprodE ?cents_norm // centsC. Qed.

Lemma cprodEgen : forall G H, G \subset 'C(H) -> G \* H = G <*> H.
Proof. by move=> G H cGH; rewrite cprodE ?cent_mulgenEl. Qed.

Lemma bigcprodE : forall I (r : seq I) P F G,
  \big[cprod/1]_(i <- r | P i) F i = G
  -> \prod_(i <- r | P i) F i = G.
Proof.
move=> I r P F; pose R A B := forall G, A = G -> B = G.
apply: (big_rel R) => [|A1 B1 A2 B2 RA RB G | _ _ _] //.
by case/cprodP=> [[G1 G2 dG1 dG2] <- _]; rewrite dG1 dG2 (RA G1) ?(RB G2).
Qed.

Lemma bigcprodEgen : forall I (r : seq I) P F G,
  \big[cprod/1]_(i <- r | P i) F i = G
  -> << \bigcup_(i <- r | P i) F i >> = G.
Proof.
move=> I r P F; pose R A B := forall G, A = G -> <<B>> = G.
apply: (big_rel R) => [_ <-|A1 B1 A2 B2| i _ G ->]; rewrite ?gen0 ?genGid //.
move=> RA RB G; case/cprodP=> [[G1 G2 dG1 dG2] <-]; rewrite dG1 dG2.
by move/cent_mulgenEl <-; rewrite -(RA G1) // -(RB G2) ?mulgen_idl ?mulgen_idr.
Qed.

Lemma cprodC : commutative cprod.
Proof.
rewrite /cprod => A B; case: ifP => cAB; rewrite centsC cAB // /pprod.
by rewrite andbCA normC !cents_norm // 1?centsC //; do 2!case: eqP => // ->.
Qed.

Lemma triv_cprod : forall A B, (A \* B == 1) = (A == 1) && (B == 1).
Proof.
move=> A B; case A1: (A == 1); first by rewrite (eqP A1) cprod1g.
apply/eqP; case/cprodP=> [[G H defA ->]]; move/eqP.
by  rewrite defA trivMg -defA A1.
Qed.

Lemma cprod_ntriv : forall A B, A != 1 -> B != 1 ->
  A \* B =
    if [&& group_set A, group_set B & A \subset 'C(B)] then A * B else set0.
Proof.
move=> A B A1 B1; rewrite /cprod; case: ifP => cAB; rewrite cAB ?andbF //=.
by rewrite /pprod -if_neg A1 -if_neg B1 cents_norm // centsC.
Qed.

Lemma trivg0 : (@set0 gT == 1) = false.
Proof. by rewrite eqEcard cards0 cards1 andbF. Qed.

Lemma group0 : group_set (@set0 gT) = false.
Proof. by rewrite /group_set inE. Qed.

Lemma cprod0g : forall A, set0 \* A = set0.
Proof. by move=> A; rewrite /cprod sub0set /pprod group0 trivg0 !if_same. Qed.

Lemma cprodA : associative cprod.
Proof.
move=> A B C; case A1: (A == 1); first by rewrite (eqP A1) !cprod1g.
case B1: (B == 1); first by rewrite (eqP B1) cprod1g cprodg1.
case C1: (C == 1); first by rewrite (eqP C1) !cprodg1.
rewrite !(triv_cprod, cprod_ntriv) ?{}A1 ?{}B1 ?{}C1 //.
case: isgroupP => [[G ->{A}] | _]; last by rewrite group0.
case: (isgroupP B) => [[H ->{B}] | _]; last by rewrite group0.
case: (isgroupP C) => [[K ->{C}] | _]; last by rewrite group0 !andbF.
case cGH: (G \subset 'C(H)); case cHK: (H \subset 'C(K)); last first.
- by rewrite group0.
- by rewrite group0 /= centM subsetI cGH andbF.
- by rewrite group0 /= -gen_subG genM_mulgen mulgen_subG cHK !andbF.
rewrite /= mulgA centM subsetI cGH -(cent_mulgenEl cHK).
by rewrite -{2 3}(cent_mulgenEl cGH) mulgen_subG cHK !groupP !andbT.
Qed.

Canonical Structure cprod_law := Monoid.Law cprodA cprod1g cprodg1.
Canonical Structure cprod_abelaw := Monoid.AbelianLaw cprodC.

Lemma dprod1g : left_unit 1 dprod.
Proof. by move=> A; rewrite /dprod subsetIl cprod1g. Qed.

Lemma dprodg1 : right_unit 1 dprod.
Proof. by move=> A; rewrite /dprod subsetIr cprodg1. Qed.

Lemma dprodP : forall A B G,
  A \x B = G -> [/\ are_groups A B, A * B = G, A \subset 'C(B) & A :&: B = 1].
Proof.
rewrite /dprod=> A B G; case: ifP => trAB; last by case/group_not0.
by case/cprodP=> gAB; split=> //; case: gAB trAB => ? ? -> ->; move/trivgP.
Qed.

Lemma dprodE : forall G H,
  G \subset 'C(H) -> G :&: H = 1 -> G \x H = G * H.
Proof. by move=> G H cGH trGH; rewrite /dprod trGH sub1G cprodE. Qed.

Lemma dprodEcprod : forall A B, A :&: B = 1 -> A \x B = A \* B.
Proof. by move=> A B trAB; rewrite /dprod trAB subxx. Qed.

Lemma dprodEsdprod : forall A B, A \subset 'C(B) -> A \x B = A ><| B.
Proof. by rewrite /dprod /cprod => A B ->. Qed.

Lemma dprodEgen : forall G H,
  G \subset 'C(H) -> G :&: H = 1 -> G \x H = G <*> H.
Proof. by move=> G H cGH trGH; rewrite /dprod trGH subxx cprodEgen. Qed.

Lemma bigdprodEcprod : forall I (r : seq I) P F G,
  \big[dprod/1]_(i <- r | P i) F i = G
   -> \big[cprod/1]_(i <- r | P i) F i = G.
Proof.
move=> I r P F; rewrite -!(big_filter r).
elim: {r}filter => [|i r IHr] G; rewrite !(big_seq0, big_adds) //=.
case/dprodP=> [[F' G' -> defG'] <-]; rewrite defG' (IHr _ defG') => cFG' _.
by rewrite cprodE.
Qed.

Lemma bigdprodE : forall I (r : seq I) P F G,
  \big[dprod/1]_(i <- r | P i) F i = G
  -> \prod_(i <- r | P i) F i = G.
Proof. move=> I r P F G; move/bigdprodEcprod; exact: bigcprodE. Qed.

Lemma bigdprodEgen : forall I (r : seq I) P F G,
  \big[dprod/1]_(i <- r | P i) F i = G
  -> << \bigcup_(i <- r | P i) F i >> = G.
Proof. move=> I r P F G; move/bigdprodEcprod; exact: bigcprodEgen. Qed.

Lemma dprodC : commutative dprod.
Proof. by move=> A B; rewrite /dprod setIC cprodC. Qed.

Lemma dprodA : associative dprod.
Proof.
move=> A B C; case A1: (A == 1); first by rewrite (eqP A1) !dprod1g.
case B1: (B == 1); first by rewrite (eqP B1) dprod1g dprodg1.
case C1: (C == 1); first by rewrite (eqP C1) !dprodg1.
rewrite /dprod (fun_if (cprod A)) (fun_if (cprod^~ C)) -cprodA.
rewrite -(cprodC set0) !cprod0g cprod_ntriv ?B1 ?{}C1 //.
case: and3P B1 => [[] | _ _]; last by rewrite cprodC cprod0g !if_same.
case/isgroupP=> H ->; case/isgroupP=> K -> {B C}; move/cent_mulgenEl=> eHK H1.
rewrite cprod_ntriv ?trivMg ?{}A1 ?{}H1 // centM subsetI.
case: and4P => [[] | _]; last by rewrite !if_same.
case/isgroupP=> G ->{A} _ cGH _; rewrite cprodEgen // -eHK.
case trGH: (G :&: H \subset _); case trHK: (H :&: K \subset _); last first.
- by rewrite !if_same.
- rewrite if_same; case: ifP => // trG_HK; case/negP: trGH.
  by apply: subset_trans trG_HK; rewrite setIS ?mulgen_subl.
- rewrite if_same; case: ifP => // trGH_K; case/negP: trHK.
  by apply: subset_trans trGH_K; rewrite setSI ?mulgen_subr.
do 2![case: ifP] => // trGH_K trG_HK; [case/negP: trGH_K | case/negP: trG_HK].
  apply: subset_trans trHK; rewrite subsetI subsetIr -{2}(mulg1 H) -mulGS.
  rewrite setIC group_modl ?mulgen_subr //= cent_mulgenEl // -eHK.
  by rewrite -group_modr ?mulgen_subl //= setIC -(normC (sub1G _)) mulSg.
apply: subset_trans trGH; rewrite subsetI subsetIl -{2}(mul1g H) -mulSG.
rewrite setIC group_modr ?mulgen_subl //= eHK -(cent_mulgenEl cGH).
by rewrite -group_modl ?mulgen_subr //= setIC (normC (sub1G _)) mulgS.
Qed.

Canonical Structure dprod_law := Monoid.Law dprodA dprod1g dprodg1.
Canonical Structure dprod_abelaw := Monoid.AbelianLaw dprodC.

End InternalDirProd.

Implicit Arguments complP [gT K A B].
Implicit Arguments splitsP [gT A B].

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

Definition pairg1 x : gT1 * gT2 := (x, 1).
Definition pair1g x : gT1 * gT2 := (1, x).

Lemma pairg1_morphM : {morph pairg1 : x y / x * y}.
Proof. by move=> x y /=; rewrite {2}/mulg /= /extprod_mulg /= mul1g. Qed.

Canonical Structure pairg1_morphism :=
  @Morphism _ _ setT _ (in2W pairg1_morphM).

Lemma pair1g_morphM : {morph pair1g : x y / x * y}.
Proof. by move=> x y /=; rewrite {2}/mulg /= /extprod_mulg /= mul1g. Qed.

Canonical Structure pair1g_morphism :=
  @Morphism _ _ setT _ (in2W pair1g_morphM).

Lemma injm_pair1g : 'injm pair1g.
Proof.
apply/subsetP=> x; case/morphpreP=> _; case/set1P=> ->; exact: set11.
Qed.

Lemma injm_pairg1 : 'injm pairg1.
Proof.
apply/subsetP=> x; case/morphpreP=> _; case/set1P=> ->; exact: set11.
Qed.

Lemma morphim_pairg1 : forall (H1 : {set gT1}), pairg1 @* H1 = setX H1 1.
Proof.
by move=> H1; rewrite -imset2_pair imset2_set1r morphimEsub ?subsetT.
Qed.

Lemma morphim_pair1g : forall (H2 : {set gT2}), pair1g @* H2 = setX 1 H2.
Proof.
by move=> H1; rewrite -imset2_pair imset2_set1l morphimEsub ?subsetT.
Qed.

Lemma setX_prod : forall (H1 : {set gT1}) (H2 : {set gT2}),
  setX H1 1 * setX 1 H2 = setX H1 H2.
Proof.
move=> H1 H2; apply/setP=> [[x y]]; rewrite !inE /=.
apply/imset2P/andP=> [[[x1 u1] [v1 y1]] | [Hx Hy]].
  rewrite !inE /=; case/andP=> Hx1; move/eqP->; case/andP; move/eqP=> -> Hx2.
  by case=> -> ->; rewrite mulg1 mul1g.
exists (x, 1 : gT2) (1 : gT1, y); rewrite ?inE ?Hx ?eqxx //.
by rewrite /mulg /= /extprod_mulg /= mulg1 mul1g.
Qed.

Lemma setX_dprod : forall (H1 : {group gT1}) (H2 : {group gT2}),
  setX H1 1 \x setX 1 H2 = setX H1 H2.
Proof.
move=> H1 H2; rewrite dprodE ?setX_prod //.
  apply/centsP=> [[x u]]; rewrite !inE /=; case/andP=> _; move/eqP=> -> [v y].
  rewrite !inE /=; case/andP; move/eqP=> -> _.
  by rewrite /commute /mulg /= /extprod_mulg /= !mulg1 !mul1g.
apply/trivgP; apply/subsetP=> [[x y]]; rewrite !inE /= -!andbA; case/and4P=> _.
by do 2!move/eqP->; rewrite eqxx.
Qed.

Lemma isog_setX1 : forall (H1 : {group gT1}), isog H1 (setX H1 1).
Proof.
move=> H1; apply/isogP; exists [morphism of restrm (subsetT H1) pairg1].
  by rewrite injm_restrm ?injm_pairg1.
by rewrite morphim_restrm morphim_pairg1 setIid.
Qed.

Lemma isog_set1X : forall (H2 : {group gT2}), isog H2 (setX 1 H2).
Proof.
move=> H2; apply/isogP; exists [morphism of restrm (subsetT H2) pair1g].
  by rewrite injm_restrm ?injm_pair1g.
by rewrite morphim_restrm morphim_pair1g setIid.
Qed.

Lemma setX_gen (H1 : {set gT1}) (H2 : {set gT2}):
  1 \in H1 -> 1 \in H2 -> <<setX H1 H2>> = setX <<H1>> <<H2>>.
Proof.
move=> H1 H2 H1_1 H2_1; apply/eqP.
rewrite eqEsubset gen_subG setXS ?subset_gen //.
rewrite -setX_prod -morphim_pair1g -morphim_pairg1 !morphim_gen ?subsetT //.
by rewrite morphim_pair1g morphim_pairg1 mul_subG // genS // setXS ?sub1set.
Qed.

End ExternalDirProd.

Section ExternalSDirProd.

Variables (hT kT : finGroupType) (H : {group hT}) (K : {group kT}).
Variable to : {morphism K >-> {perm hT}}.

(* Beware: the pair (x, a) denotes the product sdpair2 a * sdpair1 x *)

Inductive sdprod_of (toAut : to @* K \subset Aut H) : predArgType :=
  SdPair (xa : hT * kT) & xa \in setX H K.

Coercion pair_of_sd toAut (u : sdprod_of toAut) := let: SdPair xa _ := u in xa.

Hypothesis toAut : to @* K \subset Aut H.

Notation sdT := (sdprod_of toAut).
Notation sdval := (@pair_of_sd toAut).

Canonical Structure sdprod_subType :=
  SubType sdval (@sdprod_of_rect toAut) vrefl.
Canonical Structure sdprod_eqType := Eval hnf in [subEqType for sdval].
Canonical Structure sdprod_finType := Eval hnf in [finType of sdT by :>].
Canonical Structure sdprod_subFinType := Eval hnf in [subFinType of sdT].

Definition sdprod_unit := SdPair toAut (group1 _).

Lemma sdprod_aut_proof : forall a, a \in K -> to a \in Aut H.
Proof. by move=> a Ka; rewrite (subsetP toAut) ?mem_morphim. Qed.

Notation Local toA := sdprod_aut_proof.

Lemma sdprod_closed : forall a x, a \in K -> (to a x \in H) = (x \in H).
Proof. by move=> a x Ka; apply: perm_closed; case/setIdP: (toA Ka). Qed.

Lemma sdprod_inv_proof : forall u : sdT,
  (to u.2^-1 u.1^-1, u.2^-1) \in setX H K.
Proof.
case=> [[x a]] /=; case/setXP=> Hx Ka.
by rewrite inE sdprod_closed !groupV ?Hx ?Ka.
Qed.

Definition sdprod_inv u := SdPair toAut (sdprod_inv_proof u).

Lemma sdprod_mul_proof : forall u v : sdT,
  (to v.2 u.1 * v.1, u.2 * v.2) \in setX H K.
Proof.
case=> [[x a]] /=; case/setXP=> Hx Ka [[y b]] /=; case/setXP=> Hy Kb.
by rewrite inE !groupMr //= sdprod_closed ?Hx.
Qed.

Definition sdprod_mul u v := SdPair toAut (sdprod_mul_proof u v).

Lemma sdprod_mul1g : left_unit sdprod_unit sdprod_mul.
Proof.
move=> u; apply: val_inj; case: u => [[x a] /=]; case/setXP=> _ Ka.
by rewrite -(autmE (toA Ka)) morph1 !mul1g.
Qed.

Lemma sdprod_mulVg : left_inverse sdprod_unit sdprod_inv sdprod_mul.
Proof.
move=> u; apply: val_inj; case: u => [[x a] /=]; case/setXP=> _ Ka.
by rewrite morphV // permKV !mulVg.
Qed.

Lemma sdprod_mulgA : associative sdprod_mul.
Proof.
move=> u v w; apply: val_inj; case: u => [[x a]] /=; case/setXP=> Hx Ka.
case: v w => [[y b]] /=; case/setXP=> Hy Kb [[z c]] /=; case/setXP=> Hz Kc.
by rewrite !mulgA -(autmE (toA Kc)) !morphM ?permM ?sdprod_closed.
Qed.

Canonical Structure sdprod_baseFinGroupType := Eval hnf in
  [baseFinGroupType of sdT by sdprod_mulgA, sdprod_mul1g & sdprod_mulVg].

Canonical Structure sdprod_groupType := FinGroupType sdprod_mulVg.

Definition sdpair1 x := insubd sdprod_unit (x, 1) : sdT.
Definition sdpair2 a := insubd sdprod_unit (1, a) : sdT.

Lemma sdpair1_morphM : {in H &, {morph sdpair1 : x y / x * y}}.
Proof.
move=> x y Hx Hy; apply: val_inj.
by rewrite /= !val_insubd !inE !group1 !groupM ?Hx ?Hy //= mulg1 morph1 perm1.
Qed.

Lemma sdpair2_morphM : {in K &, {morph sdpair2 : a b / a * b}}.
Proof.
move=> a b Ka Kb; apply: val_inj.
rewrite /= !val_insubd !inE !group1 !groupM ?Ka ?Kb //= mulg1.
by rewrite -(autmE (toA Kb)) morph1.
Qed.

Canonical Structure sdpair1_morphism := Morphism sdpair1_morphM.

Canonical Structure sdpair2_morphism := Morphism sdpair2_morphM.

Lemma injm_sdpair1 : 'injm sdpair1.
Proof.
apply/subsetP=> x; case/setIP=> Hx.
by rewrite !inE -val_eqE val_insubd inE Hx group1 /=; case/andP.
Qed.

Lemma injm_sdpair2 : 'injm sdpair2.
Proof.
apply/subsetP=> a; case/setIP=> Ka.
by rewrite !inE -val_eqE val_insubd inE Ka group1 /=; case/andP.
Qed.

Lemma sdpairJ : forall x a,
  x \in H -> a \in K -> sdpair1 x ^ sdpair2 a = sdpair1 (to a x).
Proof.
move=> x a Hx Ka; apply: val_inj.
rewrite /= !val_insubd !inE !group1 sdprod_closed ?Ka ?Hx //=.
by rewrite !mul1g mulVg invg1 mulg1 morphV // permKV mul1g.
Qed.

Lemma sdpairEdom: sdpair1 @* H ><| sdpair2 @* K = setT.
Proof.
apply/eqP; rewrite -subTset sdprodE /= !morphimEdom /=.
- apply/subsetP=> /= u _; have [/= Hu Ku] := setIdP (valP u).
  apply/imset2P; exists (sdpair1 (to u.2^-1 u.1)) (sdpair2 u.2).
  + by rewrite mem_imset ?sdprod_closed ?groupV.
  + by rewrite mem_imset.
  rewrite -sdpairJ ?groupV // morphV // -conjgCV; apply: val_inj.
  rewrite /= !val_insubd !inE {}Ku {}Hu !group1 /= morph1 perm1 mulg1 mul1g.
  by case: u => [[]].
- apply/subsetP=> u; case/imsetP=> a Ka ->{u}; rewrite inE.
  apply/subsetP=> va; case/imsetP=> v; case/imsetP=> x Hx -> -> {v va}.
  by rewrite sdpairJ // mem_imset // sdprod_closed.
apply/trivgP; apply/subsetP=> u; case/setIP; case/imsetP=> a Ka ->{u}.
case/imsetP=> x Hx; move/eqP; rewrite inE -!val_eqE.
by rewrite !val_insubd !inE Ka Hx !group1 /eqd /= eqxx; case/andP=> ->.
Qed.

End ExternalSDirProd.

Section ProdMorph.

Variables gT rT : finGroupType.
Implicit Types A B : {set gT}.
Implicit Types G H K : {group gT}.
Implicit Types C D : {set rT}.
Implicit Type L : {group rT}.

Section defs.

Variables (A B : {set gT}) (fA fB : gT -> FinGroup.sort rT).

Definition morph_actJ := forall x a, fA (x ^ a) = fA x ^ fB a.

Definition pprodm of B \subset 'N(A) & {in A & B, morph_actJ}
                  & {in A :&: B, fA =1 fB} :=
  fun x => fA (divgr A B x) * fB (remgr A B x).

End defs.

Section Props.

Variables H K : {group gT}.
Variables (fH : {morphism H >-> rT}) (fK : {morphism K >-> rT}).
Hypothesis nHK : K \subset 'N(H).
Hypothesis actf : {in H & K, morph_actJ fH fK}.
Hypothesis eqfHK : {in H :&: K, fH =1 fK}.

Notation Local f := (pprodm nHK actf eqfHK).

Lemma pprodmE : forall x a, x \in H -> a \in K -> f (x * a) = fH x * fK a.
Proof.
move=> x a Hx Ka; have: x * a \in H * K by rewrite mem_imset2.
rewrite -remgrP inE /f rcoset_sym mem_rcoset /divgr -mulgA groupMl //.
case/andP; move: (remgr H K _) => b Hab Kb; rewrite morphM // -mulgA.
have Kab: a * b^-1 \in K by rewrite groupM ?groupV.
by congr (_ * _); rewrite eqfHK 1?inE ?Hab // -morphM // mulgKV.
Qed.

Lemma pprodmEl : {in H, f =1 fH}.
Proof. by move=> x Hx; rewrite -(mulg1 x) pprodmE // morph1 !mulg1. Qed.

Lemma pprodmEr : {in K, f =1 fK}.
Proof. by move=> a Ka; rewrite -(mul1g a) pprodmE // morph1 !mul1g. Qed.

Lemma pprodmM : {in H <*> K &, {morph f: x y / x * y}}.
Proof.
move=> xa yb; rewrite norm_mulgenEr //.
case/imset2P=> x a Ha Ka ->{xa}; case/imset2P=> y b Hy Kb ->{yb}.
have Hya: y ^ a^-1 \in H by rewrite -mem_conjg (normsP nHK).
rewrite mulgA -(mulgA x) (conjgCV a y) (mulgA x) -mulgA !pprodmE 1?groupMl //.
by rewrite 2?morphM // actf ?groupV ?morphV // !mulgA mulgKV invgK.
Qed.

Canonical Structure pprodm_morphism := Morphism pprodmM.

Lemma morphim_pprodm : forall A B,
  A \subset H -> B \subset K -> f @* (A * B) = fH @* A * fK @* B.
Proof.
move=> A B sAH sBK; rewrite [f @* _]morphimEsub /=; last first.
  by rewrite norm_mulgenEr // mulgSS.
apply/setP=> y; apply/imsetP/idP=> [[xa] |].
  case/imset2P=> x a Ax Ba -> -> {y xa}.
  have Hx := subsetP sAH x Ax; have Ka := subsetP sBK a Ba.
  by rewrite pprodmE // mem_imset2 ?mem_morphim.
case/imset2P=> fx fa.
case/morphimP=> x Hx Ax ->; case/morphimP=> a Ka Ba -> ->{y fx fa}.
by exists (x * a); rewrite ?mem_imset2 ?pprodmE.
Qed.

Lemma morphim_pprodml : forall A, A \subset H -> f @* A = fH @* A.
Proof.
by move=> A sAH; rewrite -{1}(mulg1 A) morphim_pprodm ?sub1G // morphim1 mulg1.
Qed.

Lemma morphim_pprodmr : forall B, B \subset K -> f @* B = fK @* B.
Proof.
by move=> B sBK; rewrite -{1}(mul1g B) morphim_pprodm ?sub1G // morphim1 mul1g.
Qed.

Lemma ker_pprodm : 'ker f = [set x * a^-1 | x <- H, a <- K, fH x == fK a].
Proof.
apply/setP=> y; rewrite 3!inE {1}norm_mulgenEr //=.
apply/andP/imset2P=> [[]|[x a Hx]].
  case/imset2P=> x a Hx Ka ->{y}; rewrite pprodmE // => fxa1.
  by exists x a^-1; rewrite ?invgK // inE groupVr ?morphV // eq_mulgV1 invgK.
case/setIdP=> Kx; move/eqP=> fx -> {y}.
by rewrite mem_imset2 ?pprodmE ?groupV ?morphV // fx mulgV.
Qed.

Lemma injm_pprodm :
  'injm f = [&& 'injm fH, 'injm fK & fH @* H :&: fK @* K == fH @* K].
Proof.
apply/idP/and3P=> [injf | [injfH injfK]].
  rewrite eq_sym -{1}morphimIdom -(morphim_pprodml (subsetIl _ _)) injmI //.
  rewrite morphim_pprodml // morphim_pprodmr //=; split=> //.
    apply/injmP=> x y Hx Hy /=; rewrite -!pprodmEl //.
    by apply: (injmP _ injf); rewrite ?mem_gen ?inE ?Hx ?Hy.
  apply/injmP=> a b Ka Kb /=; rewrite -!pprodmEr //.
  by apply: (injmP _ injf); rewrite ?mem_gen //; apply/setUP; right.
move/eqP=> fHK; rewrite ker_pprodm; apply/subsetP=> y.
case/imset2P=> x a Hx; case/setIdP=> Ka; move/eqP=> fxa ->.
have: fH x \in fH @* K by rewrite -fHK inE {2}fxa !mem_morphim.
case/morphimP=> z Hz Kz; move/(injmP _ injfH) => def_x.
rewrite def_x // eqfHK ?inE ?Hz // in fxa.
by rewrite def_x // (injmP _ injfK _ _ Kz Ka fxa) mulgV set11.
Qed.

End Props.

Section Sdprodm.

Variables H K G : {group gT}.
Variables (fH : {morphism H >-> rT}) (fK : {morphism K >-> rT}).
Hypothesis eqHK_G : H ><| K = G.
Hypothesis actf : {in H & K, morph_actJ fH fK}.

Lemma sdprodm_norm : K \subset 'N(H).
Proof. by case/sdprodP: eqHK_G. Qed.

Lemma sdprodm_sub : G \subset H <*> K.
Proof. by case/sdprodP: eqHK_G => _ <- nHK _; rewrite norm_mulgenEr. Qed.

Lemma sdprodm_eqf : {in H :&: K, fH =1 fK}.
Proof.
by case/sdprodP: eqHK_G => _ _ _ -> x; move/set1P->; rewrite !morph1.
Qed.

Definition sdprodm :=
  restrm sdprodm_sub (pprodm sdprodm_norm actf sdprodm_eqf).

Canonical Structure sdprodm_morphism := Eval hnf in [morphism of sdprodm].

Lemma sdprodmE : forall a b,
  a \in H -> b \in K -> sdprodm (a * b) = fH a * fK b.
Proof. exact: pprodmE. Qed.

Lemma sdprodmEl : forall a, a \in H -> sdprodm a = fH a.
Proof. exact: pprodmEl. Qed.

Lemma sdprodmEr : forall b, b \in K -> sdprodm b = fK b.
Proof. exact: pprodmEr. Qed.

Lemma morphim_sdprodm : forall A B,
  A \subset H -> B \subset K -> sdprodm @* (A * B) = fH @* A * fK @* B.
Proof.
move=> A B sAH sBK; rewrite morphim_restrm /= (setIidPr _) ?morphim_pprodm //.
case/sdprodP: eqHK_G => _ <- _ _; exact: mulgSS.
Qed.

Lemma morphim_sdprodml : forall A, A \subset H -> sdprodm @* A = fH @* A.
Proof.
move=> A sHA.
by rewrite -{1}(mulg1 A) morphim_sdprodm ?sub1G // morphim1 mulg1.
Qed.

Lemma morphim_sdprodmr : forall B, B \subset K -> sdprodm @* B = fK @* B.
Proof.
move=> B sBK.
by rewrite -{1}(mul1g B) morphim_sdprodm ?sub1G // morphim1 mul1g.
Qed.

Lemma ker_sdprodm :
  'ker sdprodm = [set a * b^-1 | a <- H, b <- K, fH a == fK b].
Proof.
rewrite ker_restrm (setIidPr _) ?subIset ?ker_pprodm //; apply/orP; left.
by case/sdprodP: eqHK_G => _ <- nHK _; rewrite norm_mulgenEr.
Qed.

Lemma injm_sdprodm :
  'injm sdprodm = [&& 'injm fH, 'injm fK & fH @* H :&: fK @* K == fH @* K].
Proof.
by rewrite ker_sdprodm -(ker_pprodm sdprodm_norm actf sdprodm_eqf) injm_pprodm.
Qed.

End Sdprodm.

Section Cprodm.

Variables H K G : {group gT}.
Variables (fH : {morphism H >-> rT}) (fK : {morphism K >-> rT}).
Hypothesis eqHK_G : H \* K = G.
Hypothesis cfHK : fH @* H \subset 'C(fK @* K).
Hypothesis eqfHK : {in H :&: K, fH =1 fK}.

Lemma cprodm_norm : K \subset 'N(H).
Proof. by rewrite cents_norm // centsC; case/cprodP: eqHK_G. Qed.

Lemma cprodm_sub : G \subset H <*> K.
Proof. by case/cprodP: eqHK_G => _ <- cHK; rewrite cent_mulgenEl. Qed.

Lemma cprodm_actf : {in H & K, morph_actJ fH fK}.
Proof.
case/cprodP: eqHK_G => _ _ cHK a b Ha Kb /=.
rewrite /conjg (centsP cHK a) // mulKg.
by rewrite (centsP cfHK (fH a)) ?mem_morphim // mulKg.
Qed.

Definition cprodm := restrm cprodm_sub (pprodm cprodm_norm cprodm_actf eqfHK).

Canonical Structure cprodm_morphism := Eval hnf in [morphism of cprodm].

Lemma cprodmE : forall a b, a \in H -> b \in K -> cprodm (a * b) = fH a * fK b.
Proof. exact: pprodmE. Qed.

Lemma cprodmEl : forall a, a \in H -> cprodm a = fH a.
Proof. exact: pprodmEl. Qed.

Lemma cprodmEr : forall b, b \in K -> cprodm b = fK b.
Proof. exact: pprodmEr. Qed.

Lemma morphim_cprodm : forall A B,
  A \subset H -> B \subset K -> cprodm @* (A * B) = fH @* A * fK @* B.
Proof.
move=> A B sAH sBK; rewrite morphim_restrm /= (setIidPr _) ?morphim_pprodm //.
case/cprodP: eqHK_G => _ <- _; exact: mulgSS.
Qed.

Lemma morphim_cprodml : forall A, A \subset H -> cprodm @* A = fH @* A.
Proof.
by move=> A sHA; rewrite -{1}(mulg1 A) morphim_cprodm ?sub1G // morphim1 mulg1.
Qed.

Lemma morphim_cprodmr : forall B, B \subset K -> cprodm @* B = fK @* B.
Proof.
by move=> B sBK; rewrite -{1}(mul1g B) morphim_cprodm ?sub1G // morphim1 mul1g.
Qed.

Lemma ker_cprodm : 'ker cprodm = [set a * b^-1 | a <- H, b <- K, fH a == fK b].
Proof.
rewrite ker_restrm (setIidPr _) ?subIset ?ker_pprodm //; apply/orP; left.
by case/cprodP: eqHK_G => _ <- cHK; rewrite cent_mulgenEl.
Qed.

Lemma injm_cprodm :
  'injm cprodm = [&& 'injm fH, 'injm fK & fH @* H :&: fK @* K == fH @* K].
Proof.
by rewrite ker_cprodm -(ker_pprodm cprodm_norm cprodm_actf eqfHK) injm_pprodm.
Qed.

End Cprodm.

Section Dprodm.

Variables G H K : {group gT}.
Variables (fH : {morphism H >-> rT}) (fK : {morphism K >-> rT}).
Hypothesis eqHK_G : H \x K = G.
Hypothesis cfHK : fH @* H \subset 'C(fK @* K).

Lemma dprodm_cprod : H \* K = G.
Proof.
by rewrite -eqHK_G /dprod; case/dprodP: eqHK_G => _ _ _ ->; rewrite subxx.
Qed.

Lemma dprodm_eqf : {in H :&: K, fH =1 fK}.
Proof.
by case/dprodP: eqHK_G => _ _ _ -> x; move/set1P->; rewrite !morph1.
Qed.

Definition dprodm := cprodm dprodm_cprod cfHK dprodm_eqf.

Canonical Structure dprodm_morphism := Eval hnf in [morphism of dprodm].

Lemma dprodmE : forall a b, a \in H -> b \in K -> dprodm (a * b) = fH a * fK b.
Proof. exact: pprodmE. Qed.

Lemma dprodmEl : forall a, a \in H -> dprodm a = fH a.
Proof. exact: pprodmEl. Qed.

Lemma dprodmEr : forall b, b \in K -> dprodm b = fK b.
Proof. exact: pprodmEr. Qed.

Lemma morphim_dprodm : forall A B,
  A \subset H -> B \subset K -> dprodm @* (A * B) = fH @* A * fK @* B.
Proof. exact: morphim_cprodm. Qed.

Lemma morphim_dprodml : forall A, A \subset H -> dprodm @* A = fH @* A.
Proof. exact: morphim_cprodml. Qed.

Lemma morphim_dprodmr : forall B, B \subset K -> dprodm @* B = fK @* B.
Proof. exact: morphim_cprodmr. Qed.

Lemma ker_dprodm : 'ker dprodm = [set a * b^-1 | a <- H, b <- K, fH a == fK b].
Proof. exact: ker_cprodm. Qed.

Lemma injm_dprodm :
  'injm dprodm = [&& 'injm fH, 'injm fK & fH @* H :&: fK @* K == 1].
Proof.
rewrite injm_cprodm -(morphimIdom fH K).
by case/dprodP: eqHK_G => _ _ _ ->; rewrite morphim1.
Qed.

End Dprodm.

Lemma isog_dprod : forall A B G C D L,
  A \x B = G -> C \x D = L -> isog A C -> isog B D -> isog G L.
Proof.
move=> A0 B0 G C0 D0 L defG.
case/dprodP=> [[C D -> ->] defL cCD trCD] {C0 D0}.
case/dprodP: defG (defG) => [[A B -> ->] defG _ _] dG {A0 B0} defC defD.
case/isogP: defC defL cCD trCD => fA injfA <-{C}.
case/isogP: defD => fB injfB <-{D} defL cCD trCD.
apply/isogP; exists (dprodm_morphism dG cCD).
  by rewrite injm_dprodm injfA injfB trCD eqxx.
by rewrite /= -{2}defG morphim_dprodm.
Qed.

End ProdMorph.

Section DirprodIsom.

Variable gT : finGroupType.
Implicit Types G H : {group gT}.

Definition mulgm : gT * gT -> _ := prod_curry mulg.

Lemma imset_mulgm : forall A B : {set gT}, mulgm @: setX A B = A * B.
Proof. by move=> A B; rewrite -curry_imset2X. Qed.

Lemma mulgmP : forall H1 H2 G,
  reflect (H1 \x H2 = G) (misom (setX H1 H2) G mulgm).
Proof.
move=> H1 H2 G; apply: (iffP misomP) => [[pM] | ].
  case/isomP=> injf /= <-; case/dprodP: (setX_dprod H1 H2) => _ /= defX cH12.
  rewrite -{4}defX {}defX; move/(congr1 (fun A => morphm pM @* A)).
  move/(morphimS (morphm_morphism pM)): cH12 => /=.
  have sH1H: setX H1 1 \subset setX H1 H2 by rewrite setXS ?sub1G.
  have sH2H: setX 1 H2 \subset setX H1 H2 by rewrite setXS ?sub1G.
  rewrite morphim1 injm_cent ?injmI //= subsetI; case/andP=> _.
  by rewrite !morphimEsub //= !imset_mulgm mulg1 mul1g; exact: dprodE.
case/dprodP=> _ defG cH12 trH12.
have fM: morphic (setX H1 H2) mulgm.
  apply/morphicP=> [[x1 x2] [y1 y2]]; rewrite !inE /=.
  case/andP=> _ Hx2; case/andP=> Hy1 _.
  by rewrite /= mulgA -(mulgA x1) (centsP cH12 y1) ?mulgA.
exists fM; apply/isomP; split; last by rewrite morphimEsub //= imset_mulgm.
apply/subsetP=> [[x1 x2]]; rewrite !inE /= andbC -eq_invg_mul.
case: eqP => //= <-; rewrite groupV -in_setI trH12; move/set1P->.
by rewrite invg1 eqxx.
Qed.

End DirprodIsom.

Implicit Arguments mulgmP [gT H1 H2 G].
Prenex Implicits mulgm mulgmP.
