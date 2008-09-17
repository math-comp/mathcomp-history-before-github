(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)

Require Import ssreflect. 
Require Import ssrbool.
Require Import ssrfun.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import fintype.
Require Import paths.
Require Import bigops.
Require Import finset.
Require Import finfun.
Require Import groups.
Import GroupScope.
Require Import morphisms.
Require Import normal.

Require Import automorphism.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section MaxNormal.

Open Scope group_scope.

Variables (gT : finGroupType).
Notation gTg := {group gT}.
Notation sT := {set gT}.

Definition maxnormal (A B : sT) := [max B of G | (G <| A) && ~~ (A \subset G)].

(* si on garde une defintion, penser au PI *)

Section MaxNormalElemProps.

Variables G N : gTg.

Lemma maxnormalP :
  reflect [/\ N <| G , (N \proper G) &
    (forall H : gTg, H <| G -> G :!=: H -> N \subset H -> H :=: N)]
  (maxnormal G N).
Proof.
apply: (iffP (maxgroupP _ _)) => [[]|[nNG]].
  case/andP=> nNG nsGN max; rewrite nNG /= properE nsGN.
  rewrite normal_sub //; split=> // H nHG neGH; move/max=> -> //.
  by move: neGH; rewrite eqset_sub nHG (normal_sub nHG) andbT.
rewrite properE; case/andP=> sNG pNG max; rewrite /= nNG pNG; split=> [//|H].
by case/andP=> nHG nsGH; apply: max; rewrite // eqset_sub negb_and nsGH.
Qed.


Lemma maxN_norm : maxnormal G N -> N <| G.
Proof. by move/maxgroupp; case/andP. Qed.

Lemma maxN_proper : maxnormal G N -> N \proper G.
Proof.
by move/maxgroupp; case/andP; rewrite properE; move/normal_sub->.
Qed.

Lemma maxNS : maxnormal G N -> N \subset G.
Proof. by move=> pNN; rewrite proper_sub // maxN_proper. Qed.

Lemma maxN_exists : ~~ trivg G -> {N : gTg | maxnormal G N}.
Proof.
by move=> nt; apply: ex_maxgroup; exists (1%G : gTg); rewrite /= normal1.
Qed.

Lemma maxN_sub :
  N <| G -> N \proper G -> {H : gTg | maxnormal G H & N \subset H}.
Proof.
by move=> nNG; case/andP=> _ pNGl; apply: maxgroup_exists; rewrite nNG.
Qed.

End MaxNormalElemProps.

Lemma maxN_prod : forall G N1 N2 : gTg,
  maxnormal G N1 -> maxnormal G N2 -> N1 :<>: N2 -> N1 * N2 = G.
Proof.
move=> G N1 N2 pmN1 pmN2 neN12.
have cN12 : commute N1 N2.
  by apply: normC; rewrite (subset_trans (maxNS pmN1)) ?normal_norm ?maxN_norm.
wlog nsN21 : G N1 N2 pmN1 pmN2 neN12 cN12/ ~~(N1 \subset N2).
  move/eqP: (neN12); rewrite eqset_sub negb_and; case/orP=> ns; first by apply.
  by rewrite cN12; apply=> //; apply: sym_not_eq.
have nP : N1 * N2 <| G by rewrite normalM ?maxN_norm //.
have sN2P : N2 \subset N1 * N2 by rewrite mulg_subr ?group1.
case/maxnormalP:(pmN2)=> nN2G pN2G mN2.
have contr : (G != (N1 <*> N2)%G -> (N1 <*> N2) == N2).
  by move => ne; apply/eqP=> /=; apply: mN2 => //=; rewrite comm_mulgenE.
apply/eqP; rewrite eq_sym; rewrite -[_ == _]negb_involutive -comm_mulgenE //.
have nsPN2 : ~~ (N1 * N2 \subset N2).
case/subsetPn: nsN21=> x N2x nN1x; apply/subsetPn; exists x=> //.
apply: (subsetP (mulg_subl _ _ )); rewrite // group1.
by apply: (contra contr); rewrite comm_mulgenE // eqset_sub negb_and nsPN2.
Qed.


End MaxNormal.

Prenex Implicits maxnormal.

Section Simple.

Variables (T : finGroupType).
Notation sT := {set T}.
Notation gT := {group T}.

Implicit Types G : gT.
(* Warning! This overloads the definition still present in normal ! *)

Definition simple (A : sT) := maxnormal A 1%G.

Lemma trivGn : forall G, ~~ trivg G = (1%G \proper G).
Proof. by move=> G; rewrite /trivg properE sub1set group1 /=. Qed.


Lemma simpleP : forall G, 
  reflect (~~ trivg G /\ forall H : gT, H <| G -> H :=: 1 \/ H :=: G)
          (simple G).
Proof.
move=> G; rewrite trivGn; apply: (iffP (maxnormalP _ _)) => [[_] | [nt max]].
  move=> p1G max; split=> // N nNG.
  case NGe : (N :==: G); first by right; rewrite (eqP NGe).
  by left; apply: max; rewrite // ?sub1set ?group1 // eq_sym NGe.
split; rewrite ?normal1 // => H nHG GHne _; case: (max H)=> // HGe.
by rewrite HGe eqxx in GHne.
Qed.

(* penser au Prenex Implicit *)


End Simple.

Prenex Implicits simple.

Lemma isog_simpl : forall (gT1 gT2 : finGroupType)(G : {group gT1})(H : {group gT2}),
   G \isog H -> simple G -> simple H.
Proof.
move=> gT1 gT2 G H; move/isog_sym_imply; case/isogP=> f injf <-.
case/simpleP=> ntH simH; apply/simpleP; split=> [|L nLH].
  by apply: contra ntH; move/trivGP=> H1; rewrite {3}H1 /= morphim1.
case: (andP nLH); move/(morphim_invm injf); move/group_inj=> <- _.
have: f @* L <| f @* H by rewrite morphim_normal.
by case/simH=> /= ->; [left | right]; rewrite (morphim1, morphim_invm).
Qed.



Section SimpleMaxNormal.


Variables (gT : finGroupType).
Notation gt := {group gT}.
Notation st := {set gT}.

Variables G N : {group gT}.


Lemma maxN_simple_quo : maxnormal G N -> simple (G / N).
Proof.
case/maxnormalP=> nNG pNG Nmax; apply/simpleP; split; last move=> K' nK'Q. 
  by rewrite trivg_quotient ?normal_norm ?proper_subn.
have : (K' \proper (G / N)) || (G / N == K').
  by rewrite properE eqset_sub andbC (normal_sub nK'Q) !andbT orbC orb_negb_r.
case/orP=> [ pHQ | eQH]; last by right; apply sym_eq; apply/eqP.
left; pose K := ((coset_of N) @*^-1 K')%G.
have eK'I : K' \subset (coset_of N) @* 'N(N).
  by rewrite (subset_trans (normal_sub nK'Q)) ?morphimS ?normal_norm.
have eKK' : K' :=: K / N by rewrite /(K / N) morphpreK //=.
suff eKN : K :=: N by rewrite -trivial_quotient eKK' eKN.
have nKG : K <| G by rewrite -(cosetimGK nNG) cosetpre_normal.
apply: Nmax=> //; last by rewrite -(ker_coset N) kerE morphpreSK sub1G.
suff : ~~ (G \subset K) by rewrite eqset_sub negb_and (normal_sub nKG) orbF.
by rewrite -(cosetimGK nNG) morphpreSK /= ?proper_subn // ?morphimS ?normal_norm.
Qed.


Lemma normal_simple_quo_maxN_ : N <| G -> simple (G / N) -> maxnormal G N.
Proof.
move=> nNG; move/simpleP=> [nt sQ]; apply/maxnormalP; rewrite nNG properE.
rewrite normal_sub // -trivg_quotient ?normal_norm //; split=> // K nKG neGK sNK.
pose K':= ((coset_of N) @* K)%G.
have K'dQ : K' <| (G / N)%G by apply: morphim_normal.
have nKN : N <| K by rewrite (normalS _ _ nNG) // normal_sub.
case: (sQ K' K'dQ)=> /=; last first.
  by move/quotient_inj; rewrite !inE /=; move/(_ nKN nNG)=> c; rewrite c eqxx in neGK.
rewrite -trivial_quotient; move=> tK'; apply:(congr1 (@set_of_group _)); move: tK'.
apply: (@quotient_inj _ N); rewrite ?inE /= ?normal_refl /normal ?sNK //.
by rewrite ?(subset_trans sKG) ?normal_norm.
Qed.

Lemma maxN__is_simple_quo : N <| G -> maxnormal G N = simple (G / N).
Proof.
by move=> nNG; apply/idP/idP; [apply:maxN_simple_quo|apply:normal_simple_quo_maxN_].
Qed.


End SimpleMaxNormal.


Section SectionSeries.

Variables (gT : finGroupType).

Inductive section : Type := Sec of {group gT} * {group gT}.

Delimit Scope section_scope with sec.
Bind Scope section_scope with section.

Definition mkSec G H := Sec (G, H).

Infix "/" := mkSec : section_scope.

Coercion pair_of_section s := let: Sec u := s in u.
Coercion quotient_of_section (u : section) := u.1 / u.2.

Canonical Structure section_subType := 
  NewType pair_of_section section_rect vrefl.

Canonical Structure section_eqType := 
  Eval hnf in [subEqType for pair_of_section].
Canonical Structure section_finType :=
  Eval hnf in [finType of section by :>].
Canonical Structure section_subFinType :=
  Eval hnf in [subFinType of section].

Canonical Structure section_group(u : section) : {group _} := 
  Eval hnf in [group of u : set _].

Coercion section_group : section >-> group_for.

(* Isomophic sections *)
Definition sisog := [rel x y : section | x \isog y].

(* A representant of the isomorphism class of a section *)
Definition srepr (H : section) := 
  if (pick (sisog ^~ H)) is Some s then s else (mkSec 1 1)%sec.

Definition mksrepr G1 G2 := srepr (mkSec G1 G2).

Lemma sreprP : forall H : section, (srepr H) \isog H.
Proof.
move=> H; rewrite /srepr; case: pickP; first by move=> x; rewrite /sisog.
by move/(_ H); rewrite /= isog_refl.
Qed.

Lemma srepr_isog : forall H1 H2 : section, H1 \isog H2 -> srepr H1 = srepr H2.
Proof.
move=> H1 H2 iH12; rewrite /srepr.
suff siso12 : (sisog ^~ H1) =1 (sisog ^~ H2) by rewrite (eq_pick siso12).
by move=> x /=; apply:isog_transr.
Qed.

Definition mapsrepr (s : seq section) := maps srepr s.

Notation gTg := {group gT}.


(*From a seq of groups to the associated seq of representatives of factors *)
Definition mkfactors (G : gTg) (s : seq gTg) := 
  mapsrepr (pairmap mkSec G s).

End SectionSeries.

Infix "/" := mkSec : section_scope.

Prenex Implicits perm_eq.

Section CompositionSeries.

Variables (gT : finGroupType).

Notation gTsec := (section gT).
Notation gTg := {group gT}.

Implicit Type G : gTg.
Implicit Type s : seq gTg.

(* Composition series for G :
- successive proper maxnormal subgroups
- starts with a proper max for G
- ends with 1
*)

Definition comps G s :=
  ((last G s) == 1%G) && path [rel x y : gTg | maxnormal x y] G s.

Lemma compsP : forall G s, reflect
  (last G s = 1%G /\  path [rel x y : gTg | maxnormal x y] G s) (comps G s).
Proof. by move=> G s; apply: (iffP andP); case; move/eqP. Qed.

Lemma trivg_comps : forall G s, comps G s -> trivg G = (s == [::]).
Proof.
move=> G s; case/andP=> ls cs; apply/trivgP/eqP; last first.
  by move=> se; rewrite se /= in ls; apply/eqP.
move=> G1; case: s ls cs => // H s _ /=; case/andP; case/maxnormalP=> _.
by rewrite G1 /proper sub1set group1 andbF.
Qed.

Lemma comps_adds : forall G H s, comps G (H :: s) -> comps H s.
Proof. 
by move=> G H s; case/andP => /= ls; case/andP=> _ p; rewrite /comps ls. 
Qed.

Lemma simple_compsP : forall G s, comps G s ->
  reflect (s = [:: (1%G : gTg) ]) (simple G).
Proof.
move=> G s cs; apply: (iffP idP); last first.
  by move=> se; move: cs; rewrite se /=; case/andP=> /=; rewrite andbT.
case: s cs; first by rewrite /comps /= andbT; move/eqP->; case/simpleP; rewrite trivg1.
move=> H s cs sG; apply/eqP; rewrite eqseq_adds -(trivg_comps (comps_adds cs)).
suff H1: H :=: 1 by rewrite H1 trivg1 andbT; apply/eqP; apply: val_inj=> /=.
case/compsP: cs=> /= ls; case/andP=> mH ps; case/maxnormalP: sG=> _ _.
by apply; rewrite ?sub1set ?group1 ?maxN_norm // eq_sym proper_neq ?maxN_proper.
Qed.



(* Existence of a composition serie for a finite group, 
by recursion of the cardinal.
*)
Lemma exists_comps : forall G : gTg, exists s, comps G s.
Proof.
move=> G; elim: {G} #|G| {1 3}G (leqnn #|G|) => [G | n Hi G cG].
  by rewrite leqNgt ltn_0group.
case/orP: (orbN (simple G)) => [sG | nsG].
  by exists [:: (1%G : gTg) ]; rewrite /comps eqxx /= -/(simple G) sG.
case/orP: (orbN (trivg G))=> [tG | ntG].
  exists (Seq0 gTg); rewrite /comps /= andbT; apply/eqP; apply: val_inj.
  by apply/trivgP.
case: (maxN_exists ntG)=> N pmN.
have cN: #|N| <= n.
  by rewrite -ltnS (leq_trans _ cG) // proper_card // maxN_proper.
case: (Hi _ cN)=> s; case/andP=> lasts ps; exists [:: N & s]; rewrite /comps.
by rewrite last_adds lasts /= pmN.
Qed.



(* The factors associated to two
composition series of the same group are the same up to
isomophism and permutation *)

Lemma JordanHolderUniqueness : forall (G : gTg) (s1 s2 : seq gTg),
  comps G s1 -> comps G s2 -> perm_eq (mkfactors G s1) (mkfactors G s2).
Proof.
move=> G; elim: {G} #|G| {-2}G (leqnn #|G|) => [G | n Hi G cG].
  by rewrite leqNgt ltn_0group.
move=> s1 s2 cs1 cs2; case/orP: (orbN (trivg G))=> [tG | ntG].
  have -> : s1 = [::] by apply/eqP; rewrite -(trivg_comps cs1).
  have -> : s2 = [::] by apply/eqP; rewrite -(trivg_comps cs2).
  by rewrite /= perm_eq_refl.
case/orP: (orbN (simple G))=> [sG | nsG].
  have -> : s1 = [:: 1%G ] by apply/(simple_compsP cs1).
  have -> : s2 = [:: 1%G ] by apply/(simple_compsP cs2).
  by rewrite /= perm_eq_refl.
case es1: s1 cs1 => [|N1 st1] cs1.
  by move: (trivg_comps cs1); rewrite eqxx; move/negP:ntG.
case es2: s2 cs2 => [|N2 st2] cs2 {s1 es1}.
  by move: (trivg_comps cs2); rewrite eqxx; move/negP:ntG.
case/andP: cs1 => /= lst1; case/andP=> maxN_1 pst1.
case/andP: cs2 => /= lst2; case/andP=> maxN_2 pst2.
have cN1 : #|N1| <= n.
  by rewrite -ltnS (leq_trans _ cG) ?proper_card ?maxN_proper.
have cN2 : #|N2| <= n.
  by rewrite -ltnS (leq_trans _ cG) ?proper_card ?maxN_proper.
case: (N1 =P N2) {s2 es2} => [eN12 |].
  by rewrite eN12 /= perm_adds Hi // /comps ?lst2 //= -eN12 lst1.
move/eqP; rewrite -val_eqE /=; move/eqP=> neN12.
have nN1G : N1 <| G by apply maxN_norm.
have nN2G : N2 <| G by apply maxN_norm.
pose N := (N1 :&: N2)%G.
have nNG : N <| G.
  rewrite /normal subIset ?(normal_sub nN1G) //=.
  apply: subset_trans (normI _ _).
  by rewrite subsetI !normal_norm.
have iso1 : (G / N1)%G \isog (N2 / N)%G.
  rewrite isog_sym /= -(maxN_prod maxN_1 maxN_2) //.
  rewrite (@normC _ N1 N2) ?(subset_trans (normal_sub nN1G)) ?normal_norm //.
  by apply: weak_second_isom; rewrite ?(subset_trans (normal_sub nN2G)) ?normal_norm.
have iso2 : (G / N2)%G \isog (N1 / N)%G.
  rewrite isog_sym /= -(maxN_prod maxN_1 maxN_2) // setIC.
  by apply: weak_second_isom; rewrite ?(subset_trans (normal_sub nN1G)) ?normal_norm.
case: (exists_comps N)=> sN; case/andP=> lsN csN.
have i1 : perm_eq (mksrepr G N1 :: mkfactors N1 st1)
                  [:: mksrepr G N1, mksrepr N1 N & mkfactors N sN].
  rewrite perm_adds -[mksrepr _ _ :: _]/(mkfactors N1 [:: N & sN]).
  apply: Hi=> //; rewrite /comps ?lst1 //= lsN csN andbT /=.
  apply: normal_simple_quo_maxN_.
  rewrite (normalS (subsetIl N1 N2) (normal_sub nN1G)) //.
  by apply: (isog_simpl iso2); apply: maxN_simple_quo.
have i2 : perm_eq (mksrepr G N2 :: mkfactors N2 st2) 
                  [:: mksrepr G N2, mksrepr N2 N & mkfactors N sN].
  rewrite perm_adds -[mksrepr _ _ :: _]/(mkfactors N2 [:: N & sN]).
  apply: Hi=> //; rewrite /comps ?lst2 //= lsN csN andbT /=.
  apply: normal_simple_quo_maxN_.
  rewrite (normalS (subsetIr N1 N2) (normal_sub nN2G)) //.
  by apply: (isog_simpl iso1); apply: maxN_simple_quo.
pose fG1 := [:: mksrepr G N1, mksrepr N1 N & mkfactors N sN].
pose fG2 := [:: mksrepr G N2, mksrepr N2 N & mkfactors N sN].
have i3 : perm_eq fG1 fG2.
  rewrite (@perm_catCA _ [::_] [::_]) /mksrepr.
  rewrite (@srepr_isog _ (mkSec _ _) (mkSec _ _) iso1).
  rewrite -(@srepr_isog _ (mkSec _ _) (mkSec _ _) iso2).
  exact: perm_eq_refl.
apply: (perm_eq_trans i1); apply: (perm_eq_trans i3); rewrite perm_eq_sym.
apply: perm_eq_trans i2; exact: perm_eq_refl.
Qed.

End CompositionSeries.