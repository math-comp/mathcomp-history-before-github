(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import paths finfun bigops finset groups morphisms automorphism normal.
Require Import maximal.
Import GroupScope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Aditional properties on maxnormal groups. To be  moved in maximal
once generalised *)
Section MaxNormalProps.

Variables (gT : finGroupType).

Implicit Types A B C : {set gT}.
Implicit Types G H K : {group gT}.

Lemma maxnormal_sub_normal : forall A B C,
  C \subset B -> maxnormal A C B -> A <| B.
Proof.
move=> A B C sCB; case/maxsetP; case/and3P; move/gen_set_id=> /= -> pAC sBN _.
by rewrite /normal (subset_trans (proper_sub pAC)).
Qed.

Lemma maxnormal_normal : forall A B, maxnormal A B B -> A <| B.
Proof. by move=> A B mABB; apply: (maxnormal_sub_normal (subxx B)). Qed.

Lemma maxnormal_proper : forall A B C, maxnormal A B C -> A \proper B.
Proof.
move=> A B C; case/maxsetP; case/andP=> gA; case/andP=> pAB _ _.
exact: (sub_proper_trans (subset_gen A)).
Qed.

Lemma maxnormal_sub : forall A B C, maxnormal A B C -> A \subset B.
Proof.
move=> A B C hmax; rewrite proper_sub //; exact: (maxnormal_proper hmax).
Qed.

Lemma ex_maxnormal_ntrivg : forall G,
  G :!=: 1-> {N : {group gT} | maxnormal N G G}.
Proof.
move=> G ntG; apply: ex_maxgroup; exists [1 gT]%G; rewrite norm1 proper1G.
by rewrite subsetT ntG.
Qed.

Lemma ex_maxnormal_normal : forall G H K,
  K <| G -> K \proper G -> {H : {group gT} | maxnormal H G K}.
Proof.
move=> G H K nKG; case/andP=> _ pKG; apply: ex_maxgroup; exists K.
by rewrite normG /proper andbT normal_sub.
Qed.

Lemma maxnormalM : forall G H K,
  maxnormal H G G -> maxnormal K G G -> H :<>: K -> H * K = G.
Proof.
move=> G N1 N2 pmN1 pmN2 neN12.
have cN12 : commute N1 N2.
  apply: normC; apply: (subset_trans (maxnormal_sub pmN1)).
  by rewrite normal_norm ?maxnormal_normal.
wlog nsN21 : G N1 N2 pmN1 pmN2 neN12 cN12/ ~~(N1 \subset N2).
  move/eqP: (neN12); rewrite eqEsubset negb_and; case/orP=> ns; first by apply.
  by rewrite cN12; apply=> //; apply: sym_not_eq.
have nP : N1 * N2 <| G by rewrite normalM ?maxnormal_normal.
have sN2P : N2 \subset N1 * N2 by rewrite mulg_subr ?group1.
case/maxgroupP: (pmN2); case/andP=> nN2G pN2G mN2.
have contr : (N1 <*> N2) \proper G -> (N1 <*> N2) == N2.
  move => ne; apply/eqP=> /=; apply: mN2 => //=; rewrite ?ne comm_mulgenE //.
  by rewrite normal_norm.
suff h: ~~ (N1 * N2 \proper G).
  apply/eqP; rewrite eqEproper h.
  by rewrite mul_subG // ?(maxnormal_sub pmN1) ?(maxnormal_sub pmN2).
rewrite -comm_mulgenE //; apply: (contra contr).
rewrite comm_mulgenE // eqEsubset negb_and sN2P orbF; apply/negP=> h.
apply: (negP nsN21); apply: subset_trans h; apply: mulG_subl.
Qed.

End MaxNormalProps.


(* Group chains like composition series, normal series, chief sries, are
described in term of the associates series of quotients of adjacent
elements. To describe these quotients avoiding the heavy use of highly
polymorphic lists, we represent the quotients by pairs of adjacent elements
 in a chain. We call such a pair a section.
*)
Section Sections.

Variables (gT : finGroupType).

Inductive section : Type := Sec of {group gT} * {group gT}.

Delimit Scope section_scope with sec.
Bind Scope section_scope with section.

Definition mkSec G H := Sec (G, H).

Infix "/" := mkSec : section_scope.

Coercion pair_of_section s := let: Sec u := s in u.
Coercion quotient_of_section (u : section) : GroupSet.sort _ := u.1 / u.2.

Canonical Structure section_subType :=
  Eval hnf in [newType for pair_of_section by section_rect].
Definition section_eqMixin := Eval hnf in [eqMixin of section by <:].
Canonical Structure section_eqType :=
  Eval hnf in EqType section section_eqMixin.
Definition section_choiceMixin := [choiceMixin of section by <:].
Canonical Structure section_choiceType :=
  Eval hnf in ChoiceType section section_choiceMixin.
Definition section_countMixin := [countMixin of section by <:].
Canonical Structure section_countType :=
   Eval hnf in CountType section section_countMixin.
Canonical Structure section_subCountType :=
  Eval hnf in [subCountType of section].
Definition section_finMixin := [finMixin of section by <:].
Canonical Structure section_finType :=
  Eval hnf in FinType section section_finMixin.
Canonical Structure section_subFinType := Eval hnf in [subFinType of section].
Canonical Structure section_group (u : section) : {group coset_of u.2} :=
  Eval hnf in [group of u].

Coercion section_group : section >-> group_of.

(* Isomophic sections *)
Definition section_isog := [rel x y : section | x \isog y].

(* A representant of the isomorphism class of a section *)
Definition section_repr (H : section) :=
  if (pick (section_isog ^~ H)) is Some s then s else (mkSec 1 1)%sec.

Definition mksrepr G1 G2 := section_repr (mkSec G1 G2).

Lemma section_reprP : forall H : section, (section_repr H) \isog H.
Proof.
move=> H; rewrite /section_repr; case: pickP => //; move/(_ H).
by rewrite /= isog_refl.
Qed.

Lemma section_repr_isog : forall H1 H2 : section,
  H1 \isog H2 -> section_repr H1 = section_repr H2.
Proof.
move=> H1 H2 iH12; rewrite /section_repr.
suff siso12 : (section_isog ^~ H1) =1 (section_isog ^~ H2) .
  by rewrite (eq_pick siso12).
by move=> x /=; apply:isog_transr.
Qed.

Definition maprepr (s : seq section) := map section_repr s.

Notation gTg := {group gT}.

(*From a seq of groups to the associated seq of representatives of factors *)
Definition mkfactors (G : gTg) (s : seq gTg) :=
  maprepr (pairmap mkSec G s).

End Sections.

Infix "/" := mkSec : section_scope.

(*Prenex Implicits perm_eq.*)

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
  ((last G s) == 1%G) && path [rel x y : gTg | maxnormal y x x] G s.

Lemma compsP : forall G s, reflect
  (last G s = 1%G /\  path [rel x y : gTg | maxnormal y x x] G s) (comps G s).
Proof. by move=> G s; apply: (iffP andP); case; move/eqP. Qed.

Lemma trivg_comps : forall G s, comps G s -> (G :==: 1) = (s == [::]).
Proof.
move=> G s; case/andP=> ls cs; apply/eqP/eqP; last first.
  by move=> se; rewrite se /= in ls; apply/eqP.
move=> G1; case: s ls cs => // H s _ /=; case/andP; case/maxgroupP.
by rewrite G1 /proper sub1set group1 andbF.
Qed.

Lemma comps_cons : forall G H s, comps G (H :: s) -> comps H s.
Proof.
by move=> G H s; case/andP => /= ls; case/andP=> _ p; rewrite /comps ls.
Qed.

Lemma simple_compsP : forall G s, comps G s ->
  reflect (s = [:: (1%G : gTg) ]) (simple G).
Proof.
move=> G s cs; apply: (iffP idP); last first.
  move=> se; move: cs; rewrite se /=; case/andP=> /=.
  by rewrite andbT simple_maxnormal.
case: s cs.
  by rewrite /comps /= andbT; move/eqP->; case/simpleP; rewrite eqxx.
move=> H s cs sG; apply/eqP; rewrite eqseq_cons -(trivg_comps (comps_cons cs)).
suff H1: H :=: 1 by rewrite H1 eqxx andbT; apply/eqP; apply: val_inj=> /=.
case/compsP: cs=> /= ls; case/andP=> mH ps; move: sG; rewrite simple_maxnormal.
case/maxgroupP=> _; apply; rewrite ?sub1set // (maxnormal_proper mH) normal_norm //.
by rewrite maxnormal_normal.
Qed.


(* Existence of a composition serie for a finite group,
by recursion of the cardinal.
*)
Lemma exists_comps : forall G : gTg, exists s, comps G s.
Proof.
move=> G; elim: {G} #|G| {1 3}G (leqnn #|G|) => [G | n Hi G cG].
  by rewrite leqNgt cardG_gt0.
case/orP: (orbN (simple G)) => [sG | nsG].
  by exists [:: (1%G : gTg) ]; rewrite /comps eqxx /= -simple_maxnormal andbT.
case/orP: (orbN (G :==: 1))=> [tG | ntG].
  by exists (Nil gTg); rewrite /comps /= andbT.
case: (ex_maxnormal_ntrivg ntG)=> N pmN.
have cN: #|N| <= n.
  by rewrite -ltnS (leq_trans _ cG) // proper_card // (maxnormal_proper pmN).
case: (Hi _ cN)=> s; case/andP=> lasts ps; exists [:: N & s]; rewrite /comps.
by rewrite last_cons lasts /= pmN.
Qed.


(* The factors associated to two
composition series of the same group are the same up to
isomophism and permutation *)

Lemma JordanHolderUniqueness : forall (G : gTg) (s1 s2 : seq gTg),
  comps G s1 -> comps G s2 -> perm_eq (mkfactors G s1) (mkfactors G s2).
Proof.
move=> G; elim: {G} #|G| {-2}G (leqnn #|G|) => [G | n Hi G cG].
  by rewrite leqNgt cardG_gt0.
move=> s1 s2 cs1 cs2; case/orP: (orbN (G :==: 1)) => [tG | ntG].
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
  by rewrite -ltnS (leq_trans _ cG) ?proper_card ?(maxnormal_proper maxN_1).
have cN2 : #|N2| <= n.
  by rewrite -ltnS (leq_trans _ cG) ?proper_card ?(maxnormal_proper maxN_2).
case: (N1 =P N2) {s2 es2} => [eN12 |].
  by rewrite eN12 /= perm_cons Hi // /comps ?lst2 //= -eN12 lst1.
move/eqP; rewrite -val_eqE /=; move/eqP=> neN12.
have nN1G : N1 <| G by apply: maxnormal_normal.
have nN2G : N2 <| G by apply: maxnormal_normal.
pose N := (N1 :&: N2)%G.
have nNG : N <| G.
  by rewrite /normal subIset ?(normal_sub nN1G) //= normsI ?normal_norm.
have iso1 : (G / N1)%G \isog (N2 / N)%G.
  rewrite isog_sym /= -(maxnormalM maxN_1 maxN_2) //.
  rewrite (@normC _ N1 N2) ?(subset_trans (normal_sub nN1G)) ?normal_norm //.
  by rewrite weak_second_isog ?(subset_trans (normal_sub nN2G)) ?normal_norm.
have iso2 : (G / N2)%G \isog (N1 / N)%G.
  rewrite isog_sym /= -(maxnormalM maxN_1 maxN_2) // setIC.
  by rewrite weak_second_isog ?(subset_trans (normal_sub nN1G)) ?normal_norm.
case: (exists_comps N)=> sN; case/andP=> lsN csN.
have i1 : perm_eq (mksrepr G N1 :: mkfactors N1 st1)
                  [:: mksrepr G N1, mksrepr N1 N & mkfactors N sN].
  rewrite perm_cons -[mksrepr _ _ :: _]/(mkfactors N1 [:: N & sN]).
  apply: Hi=> //; rewrite /comps ?lst1 //= lsN csN andbT /=.
  rewrite -quotient_simple.
    by rewrite -(isog_simple iso2) quotient_simple.
  by rewrite (normalS (subsetIl N1 N2) (normal_sub nN1G)).
have i2 : perm_eq (mksrepr G N2 :: mkfactors N2 st2)
                  [:: mksrepr G N2, mksrepr N2 N & mkfactors N sN].
  rewrite perm_cons -[mksrepr _ _ :: _]/(mkfactors N2 [:: N & sN]).
  apply: Hi=> //; rewrite /comps ?lst2 //= lsN csN andbT /=.
  rewrite -quotient_simple.
    by rewrite -(isog_simple iso1) quotient_simple.
  by rewrite (normalS (subsetIr N1 N2) (normal_sub nN2G)).
pose fG1 := [:: mksrepr G N1, mksrepr N1 N & mkfactors N sN].
pose fG2 := [:: mksrepr G N2, mksrepr N2 N & mkfactors N sN].
have i3 : perm_eq fG1 fG2.
  rewrite (@perm_catCA _ [::_] [::_]) /mksrepr.
  rewrite (@section_repr_isog _ (mkSec _ _) (mkSec _ _) iso1).
  rewrite -(@section_repr_isog _ (mkSec _ _) (mkSec _ _) iso2).
  exact: perm_eq_refl.
apply: (perm_eq_trans i1); apply: (perm_eq_trans i3); rewrite perm_eq_sym.
apply: perm_eq_trans i2; exact: perm_eq_refl.
Qed.

End CompositionSeries.


(*
Section GeneralJordanHolder.


Variables (gT : finGroupType).

Definition ainvar(A G : {set gT}) := A \subset 'N(G).

Lemma ainvar1 : forall A, ainvar A 1%G.
Proof. rewrite /ainvar norm1; exact: subsetT. Qed.

Lemma ainvar1G : forall A : {group gT}, ainvar 1%G A.
Proof. by move=> A; rewrite /ainvar sub1set group1. Qed.


Lemma ainvar_refl : forall A : {group gT}, ainvar A A.
Proof. rewrite /ainvar; exact: normG. Qed.


Definition maxainv (A B C : {set gT}) :=
  [max C of G | [&& (G <| B), ~~ (B \subset G) & ainvar A G]].

(* garder le != pour aller avec maxnormalP ou bien changer les deux en  ~\subset*)
Lemma maxainvP : forall A G H : {group gT},
  reflect [/\ H <| G, H \proper G, ainvar A H &
    (forall K : {group gT}, K <| G -> K \proper G -> ainvar A K -> H \subset K -> K :=: H)]
  (maxainv A G H).
Proof.
move=> A G H; apply: (iffP idP).
  case/maxgroupP; case/and3P=> nHG pH aiH iH; split=> //; rewrite /proper ?(normal_sub nHG) //.
  by move=>  K nKH neKH iK; apply: iH; rewrite nKH; case/andP: neKH => _ ->.
case=> nHG pHG aH Hm; apply/maxgroupP.
rewrite nHG proper_subn //=; split=> // K; case/and3P=> nKG nsGK aKs HK; apply: Hm=> //.
by rewrite /proper (normal_sub nKG).
Qed.

Section MaxAinvProps.

Variables A G N : {group gT}.

Lemma maxainv_norm : maxainv A G N -> N <| G.
Proof. by move/maxgroupp; case/andP. Qed.

Lemma maxainv_proper : maxainv A G N -> N \proper G.
Proof.
by move/maxgroupp; case/andP; rewrite properE; move/normal_sub->; case/andP.
Qed.

Lemma maxainv_ainvar : maxainv A G N -> ainvar A N.
Proof. by move/maxgroupp; case/and3P. Qed.

Lemma maxainvS : maxainv A G N -> N \subset G.
Proof. by move=> pNN; rewrite proper_sub // maxainv_proper. Qed.

Lemma maxainv_exists : G :!=: 1 -> {N : {group gT} | maxainv A G N}.
Proof.
move=> nt; apply: ex_maxgroup; exists [1 gT]%G.
by rewrite /= normal1 ainvar1 subG1 nt.
Qed.

Lemma maxainv_sub :
  N <| G -> N \proper G -> ainvar A N -> {H : {group gT} | maxainv A G H & N \subset H}.
Proof.
by move=> nNG; case/andP=> _ pNGl aN; apply: maxgroup_exists; rewrite nNG pNGl.
Qed.

End MaxAinvProps.

Definition asimple (A G : {set gT}) := maxainv A G 1.

Lemma asimpleP : forall A G : {group gT},
  reflect (G :!=: 1 /\ (forall H : {group gT}, H <| G -> ainvar A H -> H :=: 1 \/ H :=: G)) (asimple A G).
Proof.
move=> A G; apply: (iffP idP).
  case; case/maxainvP=> _ ntG ainvG mG; split; first by rewrite  -proper1G.
  move=> H nHG ainvH; case eHG : (H == G); first by rewrite (eqP eHG) /=; right.
  left; apply: mG=> //; rewrite ?sub1set ?group1 // properEneq normal_sub // andbT.
  by move/negbT:eHG.
rewrite -proper1G; case=> ntG; move=> h; apply/maxainvP.
rewrite normal1 ntG ainvar1; split=> // K nKG pKG ainvK _.
by case: (h _ nKG ainvK)=> //; move/eqP; move/negbTE: (proper_neq pKG)->.
Qed.

Lemma asimple1 : forall G : {group gT}, (G :!=: 1) && asimple 1 G = simple G.
Proof.
move=> G; apply/andP/simpleP.
  by case=> ntG; case/asimpleP=> ntH asH; split=> // H nHG; apply: asH; rewrite // ainvar1G.
by  case=> ntG sG; split=> //; apply/asimpleP; split => // H sHG _; apply: (sG).
Qed.


Section RelativeCompositionSeries.


Notation gTsec := (section gT).
Notation gTg := {group gT}.

Implicit Type G : gTg.
Implicit Type s : seq gTg.


Variable A : gTg.

Definition acomps G s :=
  ((last G s) == 1%G) && path [rel x y : gTg | maxainv A x y] G s.

Lemma acompsP : forall G s, reflect
  (last G s = 1%G /\  path [rel x y : gTg | maxainv A x y] G s) (acomps G s).
Proof. by move=> G s; apply: (iffP andP); case; move/eqP. Qed.

Lemma trivg_acomps : forall G s, acomps G s -> (G :==: 1) = (s == [::]).
Proof.
move=> G s; case/andP=> ls cs; apply/eqP/eqP; last first.
  by move=> se; rewrite se /= in ls; apply/eqP.
move=> G1; case: s ls cs => // H s _ /=; case/andP; case/maxainvP=> _.
by rewrite G1 /proper sub1set group1 andbF.
Qed.


Lemma acomps_cons : forall G H s, acomps G (H :: s) -> acomps H s.
Proof.
by move=> G H s; case/andP => /= ls; case/andP=> _ p; rewrite /acomps ls.
Qed.

Lemma asimple_acompsP : forall G s,
  acomps G s -> reflect (s = [:: 1%G]) (asimple A G).
Proof.
move=> G s cs; apply: (iffP idP); last first.
  by move=> se; move: cs; rewrite se /=; case/andP=> /=; rewrite andbT.
case: s cs; first by rewrite /acomps /= andbT; move/eqP->; case/asimpleP; rewrite eqxx.
move=> H s cs sG; apply/eqP.
rewrite eqseq_cons -(trivg_acomps (acomps_cons cs)) andbC andbb.
case/acompsP: cs => /= ls; case/andP=> mH ps.
case/maxainvP: sG => _ ntG _ -> //; rewrite ?sub1G  ?(maxainv_norm mH) ?(maxainv_proper mH) //.
exact: (maxainv_ainvar mH).
Qed.

(* Existence of a composition serie for a finite group,
by recursion on the cardinal.
*)
Lemma exists_acomps : forall G : gTg, exists s, acomps G s.
Proof.
move=> G; elim: {G} #|G| {1 3}G (leqnn #|G|) => [G | n Hi G cG].
  by rewrite leqNgt cardG_gt0.
case/orP: (orbN (asimple A G)) => [sG | nsG].
  by exists [:: (1%G : gTg) ]; rewrite /acomps eqxx /= andbT; rewrite /asimple in sG.
case/orP: (orbN (G :==: 1))=> [tG | ntG].
  by exists (Nil gTg); rewrite /acomps /= andbT.
case: (maxainv_exists A ntG)=> N pmN.
have cN: #|N| <= n.
  by rewrite -ltnS (leq_trans _ cG) // proper_card // (maxainv_proper pmN).
case: (Hi _ cN)=> s; case/andP=> lasts ps; exists [:: N & s]; rewrite /acomps.
by rewrite last_cons lasts /= pmN.
Qed.

End RelativeCompositionSeries.

End GeneralJordanHolder.

Prenex Implicits ainvar.

Section RelativeSimpleMaxInv.

Variable (gT : finGroupType).
Notation gt := {group gT}.
Notation st := {set gT}.

Variables A G N : {group gT}.


Lemma maxainv_asimple_quo : maxainv A G N -> asimple (A / N) (G / N).
Proof.
case/maxainvP=> nNG pNG Ninv Nmax; apply/asimpleP; split; last move=> K' nK'Q.
  by rewrite -subG1 quotient_sub1 ?normal_norm ?proper_subn.
have : (K' \proper (G / N)) || (G / N == K').
  by rewrite properE eqEsubset andbC (normal_sub nK'Q) !andbT orbC orb_negb_r.
case/orP=> [ pHQ | eQH]; last by right; apply sym_eq; apply/eqP.
left; pose K := ((coset N) @*^-1 K')%G.
have eK'I : K' \subset (coset N) @* 'N(N).
  by rewrite (subset_trans (normal_sub nK'Q)) ?morphimS ?normal_norm.
have eKK' : K' :=: K / N by rewrite /(K / N) morphpreK //=.
suff eKN : K :=: N by rewrite -trivg_quotient eKK' eKN.
have nKG : K <| G by rewrite -(quotientGK nNG) cosetpre_normal.
have sNK : N \subset K by rewrite -ker_coset kerE morphpreS // sub1set group1.
have {sNK} nNK : N <| K by rewrite (@normalS _ G) // normal_sub.
have iK : ainvar A K.
  move: {Nmax pNG} H; rewrite eKK' /ainvar -quotient_normG //.
  by rewrite quotientSGK // (subset_trans (normal_sub nNG)) // normal_norm.
apply: Nmax=> //; last by rewrite -(ker_coset N) kerE morphpreSK sub1G.
suff : ~~ (G \subset K) by rewrite properE (normal_sub nKG).
by rewrite -(quotientGK nNG) morphpreSK /= ?proper_subn // ?morphimS ?normal_norm.
Qed.

Lemma asimple_quo_maxainv :
  ainvar A N -> N <| G -> asimple (A / N) (G / N) -> maxainv A G N.
Proof.
move=> aiN nNG; move/asimpleP=> [nt sQ]; apply/maxainvP; rewrite nNG properE.
rewrite normal_sub // -quotient_sub1 ?normal_norm // subG1 nt aiN.
split=> // K nKG neGK aiK sNK.
pose K':= (K / N)%G.
have K'dQ : K' <| (G / N)%G by apply: morphim_normal.
have nKN : N <| K by rewrite (normalS _ _ nNG) // normal_sub.
have aiK' : ainvar (A / N) K' by rewrite /ainvar /K' -quotient_normG // quotientS.
case: (sQ K' K'dQ aiK')=> /=; last first.
  move/quotient_injG; rewrite !inE /=; move/(_ nKN nNG)=> c; move: neGK.
  by rewrite c properE subxx.
rewrite -trivg_quotient; move=> tK'; apply:(congr1 (@gval _)); move: tK'.
apply: (@quotient_injG _ N); rewrite ?inE /= ?normal_refl /normal ?sNK //.
by rewrite ?(subset_trans sKG) ?normal_norm.
Qed.


End RelativeSimpleMaxInv.

*)