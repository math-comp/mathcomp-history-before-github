(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)

(* Warning, this library is still under developpment names, definitions
and statements will probably change very soon ... *)

Require Import ssreflect. 
Require Import ssrbool.
Require Import ssrfun.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import fintype.
Require Import paths.
Require Import connect.
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


Section Proper.

Variable T : finType.
Implicit Types A B C : {set T}.

Definition proper A B := (A \subset B) && ~~ (B \subset A).

Notation "x \proper y" := (proper x y)
  (at level 70, no associativity, format "x  \proper  y") : bool_scope.

Lemma proper_sub : forall A B, A \proper B -> A \subset B.
Proof. by move=> A B; case/andP=>->. Qed.

Lemma proper_subn : forall A B, A \proper B -> ~~ (B \subset A).
Proof. by move=> A B; case/andP=>_ ->. Qed.

Lemma proper_inD : forall A B,
  A \proper B -> exists2 x, x \in B & x \notin A.
Proof. by move=> A B; case/andP=> _; case/subsetPn=> x Bx nAx; exists x. Qed.

Lemma proper_trans : forall A B C,
  A \proper B -> B \proper C -> A \proper C.
Proof.
move=> A B C; case/andP=> sAB pAB; case/andP=> sBC; case/subsetPn=> x Cx nAx.
rewrite /proper (subset_trans sAB) //=; apply/subsetPn; exists x=> //.
by apply/negP; move/(subsetP sAB); apply/negP.
Qed.

Lemma proper_sub_trans : forall A B C,
  A \proper B -> B \subset C -> A \proper C.
Proof.
move=> A B C; case/andP=> sAB pAB sBC; rewrite /proper (subset_trans sAB) //=.
by case/subsetPn: pAB=> x Bx nAx; apply/subsetPn; exists x; rewrite ?(subsetP sBC).
Qed.

Lemma sub_proper_trans : forall A B C,
  A \subset B -> B \proper C -> A \proper C.
move=> A B C sAB; case/andP=> sBC pBC; rewrite /proper (subset_trans _ sBC) //=.
case/subsetPn: pBC=> x Cx nBx; apply/subsetPn; exists x; rewrite //; apply/negP.
by move/(subsetP sAB); apply/negP.
Qed.

Lemma proper_card : forall A B,
  A \proper B -> #|A| < #|B|.
Proof.
move=> A B; case/andP=> sAB eAB; rewrite ltn_neqAle.
by case: (subset_leqif_card sAB)=> -> ->; rewrite andbT.
Qed.

Lemma proper_empty : forall A, A != set0 ->  set0 \proper A.
Proof. by move=> A neA; rewrite /proper sub0set subset0 neA. Qed.

(* This misses in finset ? *)
Lemma subsetD1 : forall A x, A :\ x \subset A.
Proof. by move=> A x; apply/subsetP=> y; case/setD1P. Qed.

Lemma properD1 : forall A x, x \in A -> A :\ x \proper A.
Proof.
move=> A x Ax; rewrite /proper subsetD1; apply/subsetPn; exists x=> //.
by rewrite in_setD1 Ax eqxx.
Qed.
 
Lemma properIr :  forall A B, ~~ (B \subset A) -> A :&: B \proper B.
Proof. by move=> A B nsAB; rewrite /proper subsetIr subsetI negb_andb nsAB. Qed.

Lemma properIl : forall A B, ~~ (A \subset B) -> A :&: B \proper A.
Proof. 
by move=> A B nsBA; rewrite /proper subsetIl subsetI negb_andb nsBA orbT. 
Qed.

Lemma properE : forall A B, A \proper B = (A \subset B) && (A != B).
Proof. by move=> A B; rewrite /proper eqset_sub; case sAB : (A \subset B). Qed.

Lemma proper_neq :  forall A B, A \proper B -> A != B.
Proof. by move=> A B; rewrite properE; case/andP. Qed.

Lemma properUr : forall A B, A :\: B != set0 ->  B \proper A :|: B.
Proof.
move=> A B; rewrite /proper subsetUr subUset subset_refl andbT -subset0 subDset.
by rewrite setU0.
Qed.

Lemma properUl : forall A B, B :\: A != set0 ->  A \proper A :|: B.
Proof. by move=> A B ned; rewrite setUC properUr. Qed.



End Proper.


Notation "x \proper y" := (proper x y)
  (at level 70, no associativity, format "x  \proper  y") : bool_scope.


Reserved Notation "x \isog y" (at level 70, no associativity).


Section MaxSet.

Variable T : finType.
Notation sT := {set T}.

Implicit Type b c: sT.

Variable p : pred sT.

Definition maxset b := 
  p b && (forallb c, (p c && (b \subset c)) ==> (c == b)).

Lemma maxsetP : forall b, 
  reflect ((p b) /\ (forall c, p c -> b \subset c -> c = b)) (maxset b).
Proof.
move=> b; apply: (iffP andP); move=> [pb bmax].
  split=>//; move=> c pc; move/forallP: bmax; move/(_ c); rewrite pc /=.
   move/implyP=> h sbc; apply/eqP; exact: h.
split=> //; apply/forallP=> x; apply/implyP; case/andP=> px sxb; apply/eqP.
by apply: (bmax x).
Qed.

Lemma maxsetp : forall b, maxset b -> p b.
Proof. by move=> b; case/maxsetP. Qed.

(* This misses in ssrnat ? *)
Lemma ltn_leq_trans :  forall n m p : nat, m < n -> n <= p -> m < p.
Proof.
move=> x y z ltxy; rewrite leq_eqVlt; case/orP=> h; first by rewrite -(eqP h).
exact: (ltn_trans ltxy).
Qed.

Lemma maxset_exists : forall c, p c -> exists b, (maxset b) && (c \subset b).
move=> c; pose t := setT : sT.
move: {2}(#|t| - #|c|) (leqnn (#|t| - #|c|))=> n; elim: n c=> [|n Hi] c hle pc.
  exists t; rewrite subsetT andbT; apply/maxsetP; split; last first. 
    by move=> x px xT; apply/eqP; rewrite -subTset.
  rewrite -(_ : c = t) //; apply/eqP; rewrite eqset_sub_card subsetT.
  by rewrite -eqn_sub0 -leqn0.
case cmax: (maxset c); first by exists c; rewrite subset_refl andbT.
move/negbT: cmax; rewrite negb_and pc /=; case/existsP=> b; rewrite negb_imply.
case/andP=> /=; case/andP=> pb scb nebc; case: (Hi b)=> //; last first.
  by move=> d; case/andP=> maxd sbd; exists d; rewrite maxd /= (subset_trans scb).
suff h2 :  #|t| - #|b| <  #|t| - #|c| by rewrite -ltnS; apply: (ltn_leq_trans h2).
have ltbc : #|c| < #|b| by rewrite proper_card // properE scb eq_sym.
by rewrite ltn_sub2l // (ltn_leq_trans ltbc) // subset_leq_card  ?subsetT.
Qed. 


End MaxSet.

Prenex Implicits maxset.


Section MaxGroup.

Variable gT : finGroupType.
Notation gt := {group gT}.
Notation sT := {set gT}.
Implicit Type b: sT.
Implicit Type c d: gt.

Variable p : pred sT.

Definition maxgroup b := 
  p b && (forallb c, (p (c :gt) && (b \subset c)) ==> (c == b :> {set gT})).

Lemma maxgroupP : forall b, 
  reflect ((p b) /\ (forall c, p c -> b \subset c -> c = b :> {set gT})) (maxgroup b).
Proof.
move=> b; apply: (iffP andP); move=> [pb bmax].
  split=>//; move=> c pc; move/forallP: bmax; move/(_ c); rewrite pc /=.
   move/implyP=> h sbc; apply/eqP; exact: h.
split=> //; apply/forallP=> x; apply/implyP; case/andP=> px sxb; apply/eqP.
exact:bmax.
Qed.

Lemma maxgroupp : forall b, maxgroup b -> p b.
Proof. by move=> b; case/maxgroupP. Qed.

(* Can we avoid duplicating the proof ? *)
Lemma maxgroup_exists : forall c, p c -> exists d : gt, maxgroup d && (c \subset d).
move=> c; pose t := setT : {set gT}.
move: {2}(#|t| - #|c|) (leqnn (#|t| - #|c|))=> n; elim: n c=> [|n Hi] c hle pc.
  exists [group of t] => /=; rewrite subsetT andbT; apply/maxgroupP; split; last first. 
  by  move=> x px xT; apply/eqP; rewrite -subTset.
  rewrite (_ : t = c ) //=; apply/eqP; rewrite eq_sym.
  by rewrite eqset_sub_card subsetT -eqn_sub0 -leqn0.
case cmax: (maxgroup c); first by exists c; rewrite subset_refl andbT.
move/negbT: cmax; rewrite negb_and pc /=; case/existsP=> b; rewrite negb_imply.
case/andP=> /=; case/andP=> pb scb nebc; case: (Hi b)=> //; last first.
  by move=> d; case/andP=> maxd sbd; exists d; rewrite maxd /= (subset_trans scb).
suff h2 :  #|t| - #|b| <  #|t| - #|c| by rewrite -ltnS; apply: (ltn_leq_trans h2).
have ltbc : #|c| < #|b| by rewrite proper_card // properE scb eq_sym.
by rewrite ltn_sub2l // (ltn_leq_trans ltbc) // subset_leq_card  ?subsetT.
Qed. 

End MaxGroup.


Prenex Implicits maxgroup.

Section MaxNormal.

Open Scope group_scope.

Variables (gT : finGroupType).
Notation gTg := {group gT}.
Notation st := {set gT}.

Variable G : gTg.

Definition maxnormal (N : st) := maxgroup [pred x | x <| G] N.

Definition pmaxnormal (N : st) := 
  maxgroup [pred x | (x <| G) && ~~(G \subset x)] N.

Lemma maxnormalP  : forall N : st, 
  reflect (N <| G /\ (forall H : gTg, H <| G -> N \subset H -> H = N :> st)) 
  (maxnormal N).
move=> N; rewrite /maxnormal;  apply: (iffP idP); first by move/maxgroupP.
by move=> *; apply/maxgroupP.
Qed.

Lemma pmaxnormalP : forall N : st, 
  reflect [/\ N <| G , (N \proper G) &
    (forall H : gTg, H <| G -> G != H :> st -> N \subset H -> H = N :> st)]
  (pmaxnormal N).
move=> N; rewrite /pmaxnormal;  apply: (iffP idP).
  case/maxgroupP=> /=; case/andP=> nNG nsGN max; rewrite nNG /= /proper nsGN.
  rewrite normal_sub //; split=> // H nHG neGH sNH; apply: max=> //; rewrite nHG /=.
  by move: neGH; rewrite eqset_sub (normal_sub nHG) andbT.
case=> nNG; case/andP=> sNG pNG max; apply/maxgroupP; rewrite /= nNG pNG; split=> //.
by move=> H; case/andP=> nHG nsGH sNH; apply: max=> //; rewrite eqset_sub negb_and nsGH.
Qed.

Lemma maxnormal_norm : forall N : st, maxnormal N -> N <| G.
Proof. by move=> N; move/maxgroupp. Qed.

Lemma pmaxnormal_norm : forall N : st, pmaxnormal N -> N <| G.
Proof. by move=> N; move/maxgroupp; case/andP. Qed.

Lemma pmaxnormal_proper : forall N : st, pmaxnormal N -> N \proper G.
Proof. by move=> N; move/maxgroupp; case/andP; rewrite /proper; move/normal_sub->. Qed.

Lemma pmaxnormalS : forall N : st, pmaxnormal N -> N \subset G.
Proof. by move=> N pNN; rewrite proper_sub // pmaxnormal_proper. Qed.

(* This misses in normal ? *)
Lemma normal1 : 1 <| G.
Proof. by rewrite /normal sub1set group1 normaliser1 subsetT. Qed.

Lemma maxnormal_exists : exists N : gTg, maxnormal N.
 case: (@maxgroup_exists _ [pred x | x <| G] _ (normal1)) => N; case/andP=> mN _.
by exists N.
Qed.

Lemma maxnormal_sub : forall H : gTg, 
  H <| G -> H \subset G -> exists N : gTg, maxnormal N && (H \subset N).
Proof.
move=> H nHG sHG. case: (@maxgroup_exists _ [pred x | x <| G] _ nHG)=> N.
by case/andP=> maxN sHN; exists N; rewrite /maxnormal maxN.
Qed.

Lemma pmaxnormal_exists : ~~ trivg G -> exists N : gTg, pmaxnormal N.
Proof.
move=> nt; case: (@maxgroup_exists _ [pred x | (x <| G) && ~~(G \subset x)] 1%G).
  by rewrite /= normal1.
by move=> N; case/andP=> mN _; exists N.
Qed.

Lemma pmaxnormal_sub :  forall H : gTg, 
  H <| G -> H \proper G -> exists N : gTg, pmaxnormal N && (H \subset N).
Proof.
move=> H nHG pHGl.
have pnHG : (H <| G) && ~~ (G \subset H) by rewrite nHG proper_subn.

case: (@maxgroup_exists _ [pred x | (x <| G) && ~~(G \subset x)] _ pnHG)=> N.
by case/andP=> mN sHN; exists N; rewrite /pmaxnormal mN.
Qed.

(* This proof needs serious cleanup ... *)
Lemma pmaxnormalprod : forall N1 N2 : gTg,
  pmaxnormal N1 -> pmaxnormal N2 -> N1 <> N2 :> set _ -> N1 * N2 = G.
Proof.

move=> N1 N2 pmN1 pmN2 neN12; case/pmaxnormalP: (pmN1)=> nN1G pN1G mN1.
case/pmaxnormalP: (pmN2)=> nN2G pN2 mN2.
have cN12 : commute N1 N2.
  apply: normC; move/normal_sub: nN1G => sN1G; apply: (subset_trans sN1G).
  by apply: normal_norm.
wlog nsN12: N1 N2 pmN1 pmN2 neN12 nN2G cN12 nN1G pN1G mN1 pN2 mN2/ ~~(N1 \subset N2).
  move/eqP: (neN12); rewrite (eqset_sub N1 N2) negb_and; case/orP=> ns; first by apply.
  by rewrite cN12; apply=> //; move => e; move: (sym_eq e).
move: (comm_mulgenE cN12)=> eP.
have sPG : N1 * N2 \subset G by rewrite mul_subG ?pmaxnormalS.
case sGP : (G \subset N1 * N2); first by apply/eqP; rewrite eqset_sub sPG.
have dPG : N1 * N2 <| G.
  rewrite /normal sPG; apply: subset_trans (normM N1 N2); rewrite subsetI.
  by rewrite !normal_norm // pmaxnormal_norm.
case: (@pmaxnormal_sub (N1 <*> N2))=> /=; rewrite ?eP /proper ?sPG ?sGP //.
move=> N; case/andP; case/pmaxnormalP=> nNG pNG _ sPN.
have neGN : G != N by rewrite eq_sym proper_neq.
have sN1N : N1 \subset N by apply: subset_trans sPN; rewrite mulg_subl ?group1.
have sN2N : N2 \subset N by apply: subset_trans sPN; rewrite mulg_subr ?group1.
move : (mN2 N nNG neGN sN2N)=> eNN2 {mN1 mN2 eP nNG nN2G nN1G dPG}.
case/subsetPn: nsN12=> x N1x nN2x; move/subsetP: sN1N; move/(_ x N1x).
by rewrite eNN2; move/negP: nN2x.
Qed.

End MaxNormal.



Section Simple.

Variables (T : finGroupType).
Notation sT := {set T}.
Notation gT := {group T}.
Variables G : gT.

(* Warning! This overloads the definition still present in normal ! *)
Definition simple := pmaxnormal G 1%G.

Lemma simple_nt : simple -> ~~ (trivg G).
Proof.
by rewrite /simple; case/pmaxnormalP=> _ p1G _; rewrite /trivg; move/proper_subn:p1G.
Qed.

Lemma nt_proper1 : ~~ trivg G -> 1%G \proper G.
Proof. by rewrite /trivg /proper sub1set group1=> ->. Qed.

Lemma proper_preim : forall (T1 T2: finType)(f : T1 -> T2) (x y : {set T2}),
y \subset (f @: T1) -> x \proper y -> (f @^-1: x) \proper (f @^-1: y).
Proof.
move=> T1 T2 f x y syi ; case/andP=> sfxy pfxy; rewrite /proper preimsetS //=.
 case/subsetPn: pfxy=> u yu nxu; apply/subsetPn.
have iu : u \in f @: T1 by apply: (subsetP syi).
by case/imsetP: iu=> v _ uv; exists v; rewrite inE -uv.
Qed.

(* to be cleaned !!! *)
Lemma proper_inj_im :  forall (gT2 : finGroupType)(f : {morphism G >-> gT2})
(x y : gT), 'injm f -> y \subset G -> x \proper y -> f @* x \proper f @* y.
Proof.
move=> gT2 f x y ijf syG pxy; rewrite properE morphimS ?proper_sub //=; apply/eqP.
move=> e; move: e (proper_neq pxy). 
move/morphim_inj=> /= ->; rewrite ?eqxx // !inE /=; move: (trivgP _ ijf)=> /= ->;
rewrite sub1set group1 //.
by apply: subset_trans _ syG; rewrite proper_sub.
Qed.

Lemma simpleP :
  reflect (~~ trivg G /\ forall N : gT, N <| G -> N \proper G -> N = 1%G) 
  simple.
Proof.
apply: (iffP idP).
  move=> s; rewrite simple_nt //; split=> //.
  case/pmaxnormalP: s => _ _ max N nNG pNG; apply: val_inj=> /=.
  by apply: (max N); rewrite // ?sub1set ?group1 // eq_sym proper_neq.
case=> nt max; apply/pmaxnormalP; split; rewrite ?normal1 ?nt_proper1 //.
by move=> H nHG neGH _ /=; rewrite (max H) // properE normal_sub // eq_sym.
Qed.

Lemma simple_pmaxN1 : 
  reflect (~~ trivg G /\ forall N : gT, pmaxnormal G N -> N = 1%G)
  simple.
Proof.
apply: (iffP simpleP); case=> -> sG; split=> // N.
  by move=> pmaxN; apply: sG; rewrite ?pmaxnormal_norm ?pmaxnormal_proper.
move=> nNG pNG; case: (pmaxnormal_sub nNG pNG)=> M; case/andP=> pmaxM sNM.
have M1 : M = 1%G by apply: sG.
apply: val_inj=> /=; apply/eqP; rewrite eqset_sub sub1set group1 andbT /=.
by rewrite M1 in sNM.
Qed.
 
End Simple.


Section SimpleMaxNormal.

(* To be moved in previous section ? *)
Lemma isog_simple : forall (gT hT : finGroupType) 
  (G : {group gT}) (H : {group hT}),
  isog G H -> simple G -> simple  H.
Proof.
move=> gT hT G H; move/isog_sym_imply; case/isogP=> f injf e. 
rewrite (_ : G = (f @*H)%G); last by apply: val_inj=> /=.
case/simpleP=> ntH simH; apply/simpleP; split=> [|L nLH pLN].
  by apply: contra ntH; move/trivGP=> H1; rewrite {3}H1 /= morphim1.
have di : f @* L <| f @* H by rewrite morphim_normal.
have pi:  f @* L \proper f @* H by apply: proper_inj_im.
move: (simH _ di pi)=> /=.
move/congr_group=> /=; rewrite -{1}(morphim_ker f).
move/morphim_inj; rewrite !inE /= ker_injm // !sub1set !group1 proper_sub //=.
by move=> -> //; apply: val_inj; rewrite /= ker_injm.
Qed.


Variables (gT : finGroupType).
Notation gt := {group gT}.


Notation st := {set gT}.


Variables G N : {group gT}.

(* The two next proofs should shrink with the specialization of morph lemmas to quotients *)
Lemma pmaxN_simple_quo : pmaxnormal G N -> simple (G / N).
Proof.
case/pmaxnormalP=> nNG; case/andP=> sNG pNG Nmax; apply/simpleP; split.
  by rewrite trivg_quotient ?normal_norm.
move=> K' nK'Q pK'Q; pose K := ((coset_of N) @*^-1 K')%G.
have scK'G : K' \subset coset_of N @* G  by apply: (normal_sub nK'Q).
have sK'd : K' \subset coset_of N @* 'N(N).
  by rewrite (subset_trans scK'G) // morphimS ?normal_norm.
have skG: 'ker (coset_of N) \subset G by rewrite ker_coset.
have neKG : K \proper G.
  rewrite /proper; move/morphimGK: skG => /= <-; rewrite ?normal_norm //.
  by rewrite morphpreS //= morphpreSK -?quotientE ?proper_subn ?morphimS ?normal_norm.
apply: val_inj => /=; suff eKN : K = N :> set _.
  have -> : K' = coset_of N @* K :> set _.
    by rewrite /K morphpreK //= (subset_trans scKG) // morphimS ?normal_norm.
  by rewrite eKN -{7}ker_coset morphim_ker.
have sNK : N \subset K by rewrite -(ker_coset N) kerE morphpreSK sub1set group1.
have nKG : K <| G.
  rewrite -(morphimGK skG) ?normal_norm // ?morphimS.
  by rewrite morphpre_normal ?morphimS ?normal_norm //=.
by apply: Nmax=> //; rewrite eq_sym proper_neq.
Qed.


Lemma normal_simple_quo_pmaxN : N <| G -> simple (G / N) -> pmaxnormal G N.
Proof.
move=> nNG; case/normalP:(nNG) => NsG; move/normsP=> sGNN.
move/simpleP=> [nt sQ]; apply/pmaxnormalP.
split; rewrite /proper ?NsG //= -?(trivg_quotient sGNN) // => K nKG neGK sNK.
pose K':= ((coset_of N) @* K); pose gK':= ((coset_of N) @* K)%G.
have K'dQ : K' <| (G / N) by apply: morphim_normal.
have sKG : K \subset G by rewrite  normal_sub.
have pK'Q : gK' \proper (G / N).
  rewrite /proper (normal_sub K'dQ) /=; rewrite sub_morphim_pre //=.
  rewrite morphimGK ?ker_coset // ?(subset_trans sKG) ?normal_norm //. 
  by move: neGK; rewrite eqset_sub sKG andbT.
apply/eqP; rewrite eqset_sub sNK andbT -(ker_coset N) ker_trivg_morphim.
rewrite normal_norm /= ?(normalS _ _ nNG) // ?normal_sub //=; apply/trivgP.
by rewrite -/gK' (sQ gK').
Qed.

Lemma pmaxN_is_simple_quo : N <| G -> pmaxnormal G N = simple (G / N).
Proof.
by move=> nNG; apply/idP/idP; [apply:pmaxN_simple_quo|apply:normal_simple_quo_pmaxN].
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

(* To be moved in normal *)
Notation "x \isog y":= (isog x y).

Canonical Structure section_group(u : section) : {group _} := 
  Eval hnf in [group of u : set _].

Coercion section_group : section >-> group_for.

(* Isomophic sections *)
Definition sisog := [rel x y : section | isog x y].

(* A representant of the isomorphism class of a section *)
Definition srepr (H : section) := 
  if (pick (sisog ^~ H)) is Some s then s else (1/ 1)%sec.

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

Notation "x \isog y":= (isog x y).

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

Lemma n1proper : forall G, ~~ (G \proper 1%G).
Proof. by move=> G; rewrite /proper negb_and sub1set group1 orbT. Qed.

Definition comps G s :=
  ((last G s) == 1%G) && path [rel x y : gTg | pmaxnormal x y] G s.


Lemma trivg_comps : forall G s, comps G s -> trivg G = (s == [::]).
Proof.
move=> G s; case/andP=> ls cs; apply/trivgP/eqP; last first.
  by move=> se; rewrite se /= in ls; apply/eqP.
move=> G1; case: s ls cs => // H s _ /=; case/andP; case/pmaxnormalP=> _.
by rewrite G1; move/(negP (n1proper _)).
Qed.

Lemma simple_comps : forall G s, 
  comps G s -> simple G = (s == [:: (1%G : gTg) ]).
Proof.
move=> G s; case/andP=> ls cs; apply/idP/eqP; last first.
  by move=> se; move: cs; rewrite se /= andbT. 
case: s ls cs=> /= [| H].
  by move/eqP=> -> _; move/simple_nt; rewrite /trivg subset_refl.
move=> s ls; case/andP=> maxH cs sG; case/simple_pmaxN1:(sG)=> ntG.
move/(_ H maxH)=> H1; apply/eqP; rewrite eqseq_adds H1 eqxx.
by rewrite -(@trivg_comps H s) /comps ?ls //=; apply/trivgP; move/(congr1 val): H1.
Qed.



(* Existence of a composition serie for a finite group, 
by recursion of the cardinal.
Is it usefull to have explicitely the values for trivg and simple ? 
*)
Lemma exists_comps : forall G : gTg, exists s, comps G s.
Proof.
move=> G; elim: {G} #|G| {1 3}G (leqnn #|G|) => [G | n Hi G cG].
  by rewrite leqNgt pos_card_group.
case/orP: (orbN (simple G)) => [sG | nsG].
  by exists [:: (1%G : gTg) ]; rewrite /comps eqxx /= -/(simple G) sG.
case/orP: (orbN (trivg G))=> [tG | ntG].
  exists (Seq0 gTg); rewrite /comps /= andbT; apply/eqP; apply: val_inj.
  by apply/trivgP.
case: (pmaxnormal_exists ntG)=> N pmN.
have cN: #|N| <= n.
  by rewrite -ltnS (ltn_leq_trans _ cG) // proper_card // pmaxnormal_proper.
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
  by rewrite leqNgt pos_card_group.
move=> s1 s2 cs1 cs2; case/orP: (orbN (trivg G))=> [tG | ntG].
  have -> : s1 = [::] by apply/eqP; rewrite -(trivg_comps cs1).
  have -> : s2 = [::] by apply/eqP; rewrite -(trivg_comps cs2).
  by rewrite /= perm_eq_refl.
case/orP: (orbN (simple G))=> [sG | nsG].
  have -> : s1 = [:: (1%G : gTg) ] by apply/eqP; rewrite -(simple_comps cs1).
  have -> : s2 = [:: (1%G : gTg) ] by apply/eqP; rewrite -(simple_comps cs2).
  by rewrite /= perm_eq_refl.
case es1: s1 cs1 => [|N1 st1] cs1.
  by move: (trivg_comps cs1); rewrite eqxx; move/negP:ntG.
case es2: s2 cs2 => [|N2 st2] cs2 {s1 es1}.
  by move: (trivg_comps cs2); rewrite eqxx; move/negP:ntG.
case/andP: cs1 => /= lst1; case/andP=> pmaxN1 pst1.
case/andP: cs2 => /= lst2; case/andP=> pmaxN2 pst2.
have cN1 : #|N1| <= n.
  by rewrite -ltnS (ltn_leq_trans _ cG) ?proper_card ?pmaxnormal_proper.
have cN2 : #|N2| <= n.
  by rewrite -ltnS (ltn_leq_trans _ cG) ?proper_card ?pmaxnormal_proper.
case eN12 : (N1 == N2)=> {s2 es2}.
  rewrite (eqP eN12) /= perm_adds; apply: Hi=> //; rewrite /comps ?lst2 //=.
  by rewrite -(eqP eN12) lst1.
have {eN12} neN12 : N1 <> N2 :> set _ by move/val_inj; move/eqP; rewrite /= eN12.
have nN1G : N1 <| G by apply pmaxnormal_norm.
have nN2G : N2 <| G by apply pmaxnormal_norm.
pose N := (N1 :&: N2)%G.
have nNG : N <| G.
  rewrite /normal subIset ?(normal_sub nN1G) //=; apply: subset_trans (normI _ _).
  by rewrite subsetI !normal_norm.
have iso1 : isog (G / N1) (N2 / N).
  rewrite isog_sym /= -(pmaxnormalprod pmaxN1 pmaxN2) //.
  rewrite (@normC _ N1 N2) ?(subset_trans (normal_sub nN1G)) ?normal_norm //.
  by apply: weak_second_isom; rewrite ?(subset_trans (normal_sub nN2G)) ?normal_norm.
have iso2 : isog (G / N2) (N1 / N).
  rewrite isog_sym /= -(pmaxnormalprod pmaxN1 pmaxN2) // setIC.
  by apply: weak_second_isom; rewrite ?(subset_trans (normal_sub nN1G)) ?normal_norm.
case: (exists_comps N)=> sN; case/andP=> lsN csN.
have i1 : perm_eq (mksrepr G N1 :: mkfactors N1 st1)
                  [:: mksrepr G N1, mksrepr N1 N & mkfactors N sN].
  rewrite perm_adds -[mksrepr _ _ :: _]/(mkfactors N1 [:: N & sN]).
  apply: Hi=> //; rewrite /comps ?lst1 //= lsN csN andbT /=.
  apply: normal_simple_quo_pmaxN.
  rewrite (normalS (subsetIl N1 N2) (normal_sub nN1G)) //.
  by apply: (isog_simple iso2); apply: pmaxN_simple_quo.
have i2 : perm_eq (mksrepr G N2 :: mkfactors N2 st2) 
                  [:: mksrepr G N2, mksrepr N2 N & mkfactors N sN].
  rewrite perm_adds -[mksrepr _ _ :: _]/(mkfactors N2 [:: N & sN]).
  apply: Hi=> //; rewrite /comps ?lst2 //= lsN csN andbT /=.
  apply: normal_simple_quo_pmaxN.
  rewrite (normalS (subsetIr N1 N2) (normal_sub nN2G)) //.
  by apply: (isog_simple iso1); apply: pmaxN_simple_quo.
(* Trying to use lemmas as cat1s makes Coq go into deep thoughts,
hence these pedestrian forward reasoning steps *)
pose fG1 := [:: mksrepr G N1, mksrepr N1 N & mkfactors N sN].
pose fG2 := [:: mksrepr G N2, mksrepr N2 N & mkfactors N sN].
have i3 : perm_eq fG1 fG2.
  rewrite /fG1 -cat1s -[_ :: mkfactors _ _]cat1s catA.
  rewrite -[fG2]/(([:: mksrepr G N2] ++ [:: mksrepr N2 N])++mkfactors N sN).
  rewrite perm_cat2r /=.
  have -> : mksrepr G N1 = mksrepr N2 N by rewrite /mksrepr; apply: srepr_isog.
  have -> : mksrepr G N2 = mksrepr N1 N by rewrite /mksrepr; apply: srepr_isog.
  set a := mksrepr _ _; set b := mksrepr _ _ .
  suff: perm_eq ([:: a] ++ [:: b]) ([:: b] ++ [:: a]) by done. 
  by rewrite perm_catC perm_eq_refl.
apply: (perm_eq_trans i1); apply: (perm_eq_trans i3); rewrite perm_eq_sym.
apply: perm_eq_trans i2; exact: perm_eq_refl.
Qed.

End CompositionSeries.