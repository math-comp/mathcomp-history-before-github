(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat.
Require Import div seq fintype.
(* Require Import connect. *)
Require Import tuple finfun ssralg bigops finset.
Require Import groups group_perm morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section ActionDef.

Variable aT : finGroupType.

Definition is_action T (to : T -> aT -> T) :=
  prod (forall x, to x 1 = x) (forall a x y, to a (x * y) = to (to a x) y).

Record action (T : Type) : Type :=
  Action { afun :> T -> aT -> T; _ : is_action afun }.

Definition action_for of phant aT := action.

End ActionDef.

Notation "{ 'action' aT &-> T }" := (action_for (Phant aT) T)
  (at level 0, format "{ 'action'  aT  &->  T }") : type_scope.

Notation "[ 'action' 'of' a ]" :=
  (match [is a : _ -> _ <: action _ _] as s
   return {type of @Action _ _ for s} -> _ with
   | Action _ actP => fun k => k actP
   end (@Action _ _ a)) (at level 0) : form_scope.

Delimit Scope action_scope with act.
Bind Scope action_scope with action.
Bind Scope action_scope with action_for.

Section ActionOpsDef.

Variables (aT : finGroupType) (sT : finType).
Implicit Type A : {set aT}.
Implicit Type to : {action aT &-> sT}.
Implicit Type S : {set sT}.

Definition afix A to := [set x | A \subset [set a | to x a == x]].

Definition astab to S := [set a | S \subset [set x | to x a == x]].

Definition orbit to A x := to x @: A.

Definition astabs to S := [set a | S \subset to^~ a @^-1: S ].

Definition acts_on to S := forall a x, (to x a \in S) = (x \in S).

Definition atrans A to S := S \in orbit to A @: S.

Definition faithful A to S := trivg (A :&: astab to S).

End ActionOpsDef.

Notation "''C' ( A | to )" := (afix A to)
 (at level 8, format "''C' ( A  |  to )") : group_scope.

Notation "''C_' S ( A | to )" := (S :&: 'C(A | to))
 (at level 8, S at level 2, format "''C_' S ( A  |  to )") : group_scope.

(* Camlp4 factoring. *)
Notation "''C_' ( G ) ( A )" := 'C_G(A)
  (at level 8, only parsing) : group_scope.
Notation "''C_' ( G ) ( A )" := 'C_G(A)%G (only parsing) : subgroup_scope.
Notation "''C_' ( G ) ( A | to )" := 'C_G(A | to)
  (at level 8, only parsing) : group_scope.

Notation "''N_' ( G ) ( A )" := 'N_G(A)
  (at level 8, only parsing) : group_scope.
Notation "''N_' ( G ) ( A )" := 'N_G(A)%G (only parsing) : subgroup_scope.

Notation "''C_' ( | to ) ( S )" := (astab to S)
 (at level 8, format "''C_' ( | to ) ( S )") : group_scope.

Notation "''C_' ( A | to ) ( S )" := (A :&: 'C_(|to)(S))
 (at level 8, format "''C_' ( A  |  to ) ( S )") : group_scope.

Notation "''N_' ( | to ) ( S )" := (astabs to S)
  (at level 8, format "''N_' ( | to ) ( S )") : group_scope.

Notation "''N_' ( A | to ) ( S )" := (A :&: 'N_(|to)(S))
  (at level 8, format "''N_' ( A  |  to ) ( S )") : group_scope.

Notation "''C_' ( | to ) [ x ]" := 'C_(|to)([set x])
  (at level 8, format "''C_' ( | to ) [ x ]") : group_scope.

Notation "''C_' ( A | to ) [ x ]" := 'C_(A | to)([set x])
  (at level 8, format "''C_' ( A  |  to ) [ x ]") : group_scope.

Notation "''C' [ a | to ]" := 'C([set a] | to)
  (at level 8, format "''C' [ a  |  to ]") : group_scope.

Notation "''C_' S [ a | to ] " := 'C_S([set a] | to)
  (at level 8, S at level 2, format "''C_' S [ a  |  to ]") : group_scope.

Notation "[ 'acts' ( A | to ) 'on' S ]" := (A \subset pred_of_set 'N_(|to)(S))
  (at level 0, format "[ 'acts'  ( A  |  to )  'on'  S ]") : form_scope.

Notation "{ 'acts' ( A | to ) 'on' S }" := {in A, acts_on to S}
  (at level 0, format "{ 'acts'  ( A  |  to )  'on'  S }") : form_scope.

Notation "[ 'transitive' ( A | to ) 'on' S ]" := (atrans A to S)
  (at level 0, format "[ 'transitive'  ( A  |  to )  'on'  S ]") : form_scope.

Notation "[ 'faithful' ( A | to ) 'on' S ]" := (faithful A to S)
  (at level 0, format "[ 'faithful'  ( A  |  to )  'on'  S ]") : form_scope.

Prenex Implicits orbit.

Section Action.

Variable (aT : finGroupType) (sT : finType).

Implicit Types a b c : aT.
Implicit Types x y z : sT.
Implicit Types A B : {group aT}.
Implicit Types S : {set sT}.

Variable to : {action aT &-> sT}.

Lemma act1 : forall x, to x 1 = x.
Proof. by case: to => ? []. Qed.

Lemma actM : forall x a b, to x (a * b) = to (to x a) b.
Proof. by case: to => ? []. Qed.

Lemma actK : forall a, cancel (to^~ a) (to^~ a^-1).
Proof. by move=> a x; rewrite -actM ?groupV // mulgV act1. Qed.

Lemma actKV : forall a, cancel (to^~ a^-1) (to^~ a).
Proof. by move=> a x; rewrite -{2}(invgK a) actK. Qed.

Lemma actCJ : forall a b x, to (to x a) b = to (to x b) (a ^ b).
Proof. by move=> a b x; rewrite !actM actK. Qed.

Lemma actCJV : forall a b x, to (to x a) b = to (to x (b ^ a^-1)) a.
Proof. by move=> a b x; rewrite (actCJ _ a) conjgKV. Qed.

Lemma act_inj : forall a, injective (to^~ a).
Proof. move=> a; exact: (can_inj (actK a)). Qed.

Lemma orbitE : forall A x, orbit to A x = to x @: A. Proof. by []. Qed.

Lemma orbitP : forall A x y,
  reflect (exists2 a, a \in A & to x a = y) (y \in orbit to A x).
Proof. by move=> A x y; apply: (iffP imsetP) => [] [a]; exists a. Qed.

Lemma orbit_to : forall A x a, a \in A -> to x a \in orbit to A x.
Proof. move=> A x; exact: mem_imset. Qed.

Lemma orbit_refl : forall A x, x \in orbit to A x.
Proof. by move=> A x; rewrite -{1}[x]act1 orbit_to. Qed.

Lemma orbit_sym : forall A x y, (y \in orbit to A x) = (x \in orbit to A y).
Proof.
move=> A x y; apply/idP/idP; case/orbitP=> a Aa; move/(canRL (actK a))->;
  by rewrite mem_imset ?groupV.
Qed.

Lemma orbit_trans : forall A x y z,
  y \in orbit to A x -> z \in orbit to A y -> z \in orbit to A x.
Proof.
move=> A x y z; case/orbitP=> a Aa <-; case/orbitP=> b Ab <-{y z}.
by rewrite -actM mem_imset ?groupM.
Qed.

Lemma orbit_transl : forall A x y,
  y \in orbit to A x -> orbit to A y = orbit to A x.
Proof.
move=> A x y Axy; apply/setP=> z; apply/idP/idP; apply: orbit_trans => //.
by rewrite orbit_sym.
Qed.

Lemma orbit_transr : forall A x y z,
  y \in orbit to A x -> (y \in orbit to A z) = (x \in orbit to A z).
Proof.
by move=> A x y z Axy; rewrite !(orbit_sym A z) (orbit_transl Axy).
Qed.

Lemma afixP : forall (A : {set aT}) x,
  reflect (forall a, a \in A -> to x a = x) (x \in 'C(A | to)).
Proof.
move=> A x; rewrite inE; apply: (iffP subsetP) => [xfix a | xfix a Aa].
  by move/xfix; rewrite inE; move/eqP.
by rewrite inE xfix.
Qed.

Lemma orbit1P : forall A x,
  reflect ([set x] = orbit to A x) (x \in 'C(A | to)).
Proof.
move=> A x; apply: (iffP (afixP _ _)) => [xfix | xfix a Aa].
  apply/eqP; rewrite eqset_sub sub1set orbit_refl.
  by apply/subsetP=> y; case/imsetP=> a Aa ->; rewrite inE xfix.
by apply/set1P; rewrite xfix mem_imset.
Qed.

Lemma afix1P : forall a x, reflect (to x a = x) (x \in 'C[a | to]).
Proof. move=> a x; rewrite inE sub1set inE; exact: eqP. Qed.

Lemma astabP : forall S a,
  reflect (forall x, x \in S -> to x a = x) (a \in 'C_(|to)(S)).
Proof.
move=> S a; rewrite inE; apply: (iffP subsetP) => fix_a y => [|Sy].
  by move/fix_a; rewrite inE; move/eqP.
by rewrite inE fix_a.
Qed.

Lemma astab1P : forall x a, reflect (to x a = x) (a \in 'C_(|to)[x]).
Proof. move=> x a; rewrite inE sub1set inE; exact: eqP. Qed.

Lemma astabsP : forall S a,
  reflect (forall x, (to x a \in S) = (x \in S)) (a \in 'N_(|to)(S)).
Proof.
move=> S a; rewrite inE; apply: (iffP idP) => [sSaS x | eSaS]; last first.
  by apply/subsetP=> x Sx; rewrite inE eSaS.
rewrite {2}((S =P to^~ a @^-1: S) _) ?inE // eqset_sub_card {}sSaS /=.
rewrite card_preimset //; exact: act_inj.
Qed.

Lemma group_set_astab : forall S, group_set 'C_(|to)(S).
Proof.
move=> S; apply/group_setP; split=> [|a b].
  by apply/astabP=> x _; rewrite act1.
move/astabP=> Ca; move/astabP=> Cb; apply/astabP=> x Sx.
by rewrite actM Ca ?Cb.
Qed.

Canonical Structure astab_group S := Group (group_set_astab S).

Lemma group_set_astabs : forall S, group_set 'N_(|to)(S).
Proof.
move=> S; apply/group_setP; split=> [|a b].
  by apply/astabsP=> y; rewrite act1.
move/astabsP=> Na; move/astabsP=> Nb; apply/astabsP=> x.
by rewrite actM Nb Na.
Qed.

Canonical Structure astabs_group S := Group (group_set_astabs S).

Lemma subset_astab : forall A S, 'C_(A | to)(S) \subset A.
Proof. move=> A S; exact: subsetIl. Qed.

Lemma card_orbit_stab : forall A x,
  (#|orbit to A x| * #|'C_(A | to)[x]|)%N = #|A|.
Proof.
move=> A x; rewrite [#|A|]card_sum_1 (partition_big_imset (to x)) /=.
rewrite -sum_nat_const; apply: eq_bigr => y; case/imsetP=> a Aa ->{y}.
rewrite (reindex (mulg^~ a)) /= ?card_sum_1; last first.
  by exists (mulg^~ a^-1) => b _; rewrite (mulgK, mulgKV).
apply: eq_bigl => b; rewrite inE groupMr // actM inE sub1set inE.
by rewrite (inj_eq (@act_inj a)). 
Qed.

Lemma card_orbit : forall A x, #|orbit to A x| = #|A : 'C_(A | to)[x]|.
Proof.
move=> A x; rewrite -divgS ?subsetIl //.
by rewrite -(card_orbit_stab A x) divn_mull ?ltn_0group.
Qed.

Lemma dvdn_orbit : forall A x, #|orbit to A x| %| #|A|.
Proof. by move=> A x; rewrite -(card_orbit_stab A x) dvdn_mulr. Qed. 

Lemma card_orbit1 : forall A x,
  #|orbit to A x| = 1%N -> orbit to A x = [set x].
Proof.
move=> A x orb1; apply/eqP; rewrite eq_sym eqset_sub_card {}orb1 cards1.
by rewrite sub1set orbit_refl.
Qed.

Lemma actsP : forall A S,
  reflect {acts (A | to) on S} [acts (A | to) on S].
Proof.
move=> A S; apply: (iffP subsetP) => nAS a Aa; apply/astabsP; exact: nAS.
Qed.
Implicit Arguments actsP [A S].

Lemma acts_orbit : forall A S x,
  [acts (A | to) on S] -> (orbit to A x \subset S) = (x \in S).
Proof.
move=> A S x; move/actsP=> AactS; apply/subsetP/idP=> [| Sx y].
  apply; exact: orbit_refl.
by case/imsetP=> a Aa ->{y}; rewrite AactS.
Qed.

Lemma orbit_in_act : forall A S x y,
  [acts (A | to) on S] -> y \in orbit to A x -> x \in S -> y \in S.
Proof. move=> A S x y; move/acts_orbit=> <- xAy; move/subsetP; exact. Qed.

Lemma acts_sum_card_orbit : forall A S, [acts (A | to) on S] ->
  \sum_(T \in orbit to A @: S) #|T| = #|S|.
Proof.
move=> A S AactS; rewrite card_sum_1 (partition_big_imset (orbit to A)) /=.
apply: eq_bigr => xS; case/imsetP=> x Sx ->{xS}; rewrite card_sum_1.
apply: eq_bigl=> y; apply/idP/andP=> [xAy|[_]].
  by rewrite (orbit_transl xAy) (orbit_in_act _ xAy).
by move/eqP <-; exact: orbit_refl.
Qed.

Lemma astab_to : forall S a, 'C_(| to)(to^~a @: S) = 'C_(| to)(S) :^ a.
Proof.
move=> S a; apply/setP=> b; rewrite mem_conjg.
apply/astabP/astabP=> stab x => [Sx|].
  by rewrite conjgE invgK !actM stab ?actK //; apply/imsetP; exists x.
by case/imsetP=> y Sy ->{x}; rewrite -actM conjgCV actM stab.
Qed.

Lemma astab1_to : forall G x a,
  a \in 'N(G) -> 'C_(G | to)[to x a] = 'C_(G | to)[x] :^ a.
Proof.
by move=> G x a nGa; rewrite conjIg (normP nGa) -astab_to imset_set1.
Qed.

Theorem Frobenius_Cauchy : forall A S, [acts (A | to) on S] ->
  \sum_(a \in A) #|'C_S[a | to]| = (#|orbit to A @: S| * #|A|)%N.
Proof.
move=> A S AactS; transitivity (\sum_(a \in A) \sum_(x \in 'C_S[a | to]) 1%N).
  by apply: eq_bigr => a _; rewrite card_sum_1.
rewrite (exchange_big_dep (mem S)) /= => [|a x _]; last by case/setIP.
set orbA := orbit to A; rewrite (partition_big_imset orbA) -sum_nat_const /=.
apply: eq_bigr => X; case/imsetP=> x Sx ->{X}.
rewrite (eq_bigl (mem (orbA x))) => [|y] /=; last first.
  apply/andP/idP=> [[_]|xAy]; first by move/eqP <-; exact: orbit_refl.
  by rewrite /orbA (orbit_transl xAy) (orbit_in_act AactS xAy).
rewrite -(card_orbit_stab A x) -sum_nat_const.
apply: eq_bigr => y; rewrite orbit_sym; case/imsetP=> a Aa defx.
rewrite defx astab1_to (subsetP (normG _), card_conjg) // card_sum_1.
by apply: eq_bigl => b; rewrite !(sub1set, inE) -(actsP AactS a Aa) -defx Sx.
Qed.

Lemma atransP : forall A S, [transitive (A | to) on S] ->
  forall x, x \in S -> orbit to A x = S.
Proof. move=> A S; case/imsetP=> x _ -> y; exact: orbit_transl. Qed.

Lemma atransP2 : forall A S, [transitive (A | to) on S] ->
  {in S &, forall x y, exists2 a, a \in A & y = to x a}.
Proof. by move=> A S AtrS x y; move/(atransP AtrS) <-; move/imsetP. Qed.

Lemma trans_acts : forall A S,
  [transitive (A | to) on S] -> [acts (A | to) on S].
Proof.
move=> A S AtrS; apply/subsetP=> a Aa; rewrite inE.
by apply/subsetP=> x; move/(atransP AtrS) <-; rewrite inE mem_imset.
Qed.

Lemma atrans_acts_card : forall A S,
  [transitive (A | to) on S] =
     [acts (A | to) on S] && (#|orbit to A @: S| == 1%N).
Proof.
move=> A S; apply/idP/andP=> [AtrS | [nSA]].
  split; first exact: trans_acts.
  rewrite ((_ @: S =P [set S]) _) ?cards1 // eqset_sub sub1set.
  apply/andP; split=> //; apply/subsetP=> X; case/imsetP=> x Sx ->.
  by rewrite inE (atransP AtrS).
rewrite eqn_leq andbC lt0n; case/andP.
case/existsP=> X; case/imsetP=> x Sx X_Ax.
rewrite (cardD1 X) {X}X_Ax mem_imset // ltnS leqn0; move/eqP=> AtrS.
apply/imsetP; exists x => //; apply/eqP.
rewrite eqset_sub acts_orbit // Sx andbT.
apply/subsetP=> y Sy; have:= card0_eq AtrS (orbit to A y).
rewrite !inE /= mem_imset // andbT; move/eqP <-; exact: orbit_refl.
Qed.

Lemma trans_div : forall A S x,
  x \in S -> [transitive (A | to) on S] -> #|S| %| #|A|.
Proof.
by move=> A S x Sx; move/atransP=> AtrS; rewrite -(AtrS x Sx) dvdn_orbit.
Qed.

(* Aschbacher 5.2 *)
Lemma norm_act_fix : forall A B, 
  A \subset 'N(B) -> [acts (A | to) on 'C(B | to)].
Proof.
move=> A B; move/subsetP=> nBA; apply/actsP=> a Aa x.
apply/afixP/afixP=> fix_x b Bb.
  by rewrite -(actK a (to x b)) (actCJ b) fix_x (actK, memJ_norm) // nBA.
by rewrite actCJV fix_x // memJ_norm // groupV nBA.
Qed.

Lemma norm_stab : forall A B S, 
  A \subset 'N(B) -> 'C_(A | to)(S) \subset 'N('C_(B | to)(S)).
Proof.
move=> A B S nAB; apply/normsP=> a; case/setIP=> Aa; move/astabP=> toSa.
apply/setP=> b; rewrite mem_conjg !in_setI memJ_norm ?(groupV, subsetP nAB) //.
congr (_ && _); apply/astabP/astabP=> toSb x Sx.
  by rewrite -(toSa _ Sx) actCJV toSb.
by rewrite !actM invgK toSa ?toSb // -{1}(toSa x Sx) actK.
Qed.

Lemma faithfulP : forall A S,
  reflect (forall a, a \in A -> {in S, to^~ a =1 id} -> a = 1)
          [faithful (A | to) on S].
Proof.
move=> A S; apply: (iffP subsetP) => [Cto1 a Aa Ca | Cto1 a].
  apply/set1P; rewrite Cto1 // inE Aa; exact/astabP.
case/setIP=> Aa; move/astabP=> Ca; apply/set1P; exact: Cto1.
Qed.

Lemma subset_faithful : forall A B S,
  B \subset A -> [faithful (A | to) on S] -> [faithful (B | to) on S].
Proof. move=> A B S sAB; apply: subset_trans; exact: setSI. Qed.

End Action.

Implicit Arguments act_inj [aT sT].
Implicit Arguments orbitP [aT sT to A x y].
Implicit Arguments afixP [aT sT to A x].
Implicit Arguments afix1P [aT sT to a x].
Implicit Arguments orbit1P [aT sT to A x].
Implicit Arguments astabP [aT sT to S a].
Implicit Arguments astab1P [aT sT to x a].
Implicit Arguments astabsP [aT sT to S a].
Implicit Arguments atransP [aT sT to A S].
Implicit Arguments actsP [aT sT to A S].
Implicit Arguments faithfulP [aT sT to A S].

Prenex Implicits orbitP afixP afix1P orbit1P astabP astab1P astabsP.
Prenex Implicits atransP actsP faithfulP.

Notation "''C_' ( | to ) ( S )" := (astab_group to S) : subgroup_scope.
Notation "''C_' ( A | to ) ( S )" := (A :&: 'C_(|to)(S))%G : subgroup_scope.
Notation "''C_' ( | to ) [ x ]" := ('C_(|to)([set x]))%G : subgroup_scope.
Notation "''C_' ( A | to ) [ x ]" := (A :&: 'C_(|to)[x])%G : subgroup_scope.
Notation "''N_' ( | to ) ( S )" := (astabs_group to S) : subgroup_scope.
Notation "''N_' ( A | to ) ( S )" := (A :&: 'N_(|to)(S))%G : subgroup_scope.

(*  Definition of the right translation as an action on cosets.        *)

Section GroupActions.

Variable gT : finGroupType.
Implicit Type A : {set gT}.
Implicit Type G : {group gT}.

Canonical Structure mulgr_action := Action (@mulg1 gT, @mulgA gT).

Canonical Structure conjg_action := Action (@conjg1 gT, @conjgM gT).

Lemma rcoset_is_action : is_action (@rcoset_of gT).
Proof. by split=> [A|A x y]; rewrite !rcosetE (mulg1, rcosetM). Qed.

Canonical Structure rcoset_action := Action rcoset_is_action.

Canonical Structure conjsg_action := Action (@conjsg1 gT, @conjsgM gT).

Lemma conjG_is_action : is_action (@conjG_group gT).
Proof. by split=> *; apply: group_inj; rewrite /= ?conjsg1 ?conjsgM. Qed.

Definition conjG_action := Action conjG_is_action.

End GroupActions.

Notation "'Mr" := (@mulgr_action _) (at level 0) : action_scope.
Notation "'Msr" := (@rcoset_action _) (at level 0) : action_scope.
Notation "'J" := (@conjg_action _) (at level 0) : action_scope.
Notation "'Js" := (@conjsg_action _) (at level 0) : action_scope.
Notation "'JG" := (@conjG_action _) (at level 0) : action_scope.

Section Bij.

Variable (gT : finGroupType) (H G : {group gT}).

Hypothesis sHG : H \subset G.

Section LBij.

Variable L : {group gT}.

(***********************************************************************)
(*                                                                     *)
(*  Definition of the set of element of orbit 1 by the right           *)
(*    translation  of rcoset of H in G                                 *)
(*                                                                     *)
(***********************************************************************)

Lemma act_fix_sub : forall x, (H :* x \in 'C(L | 'Msr)) = (L \subset H :^ x).
Proof.
move=> x; rewrite inE /=; apply: eq_subset_r => a.
rewrite inE rcosetE -(can2_eq (rcosetKV x) (rcosetK x)) -!rcosetM.
rewrite (conjgCV x) mulgK eqset_sub_card card_rcoset leqnn andbT.
by rewrite -{2 3}(mulGid H) mulGS sub1set -mem_conjg.
Qed.

End LBij.

Lemma act_fix_norm : forall x, (H :* x \in 'C(H | 'Msr)) = (x \in 'N(H)).
Proof. by move=> x; rewrite act_fix_sub -groupV inE sub_conjgV. Qed.

Lemma rtrans_fix_norm : 'C_(rcosets H G)(H | 'Msr) = rcosets H 'N_G(H).
Proof.
apply/setP=> Hx; apply/setIP/rcosetsP=> [[]|[x]].
  case/rcosetsP=> x Gx ->{Hx}; rewrite act_fix_norm => Nx.
  by exists x; rewrite // inE Gx.
by case/setIP=> Nx Gx ->; rewrite -{1}rcosetE mem_imset // act_fix_norm.
Qed.

Lemma rtrans_stabG : 'C_(| 'Msr)[G : {set _}] = G.
Proof.
apply/setP=> x.
by apply/astab1P/idP=> /= [<- | Gx]; rewrite rcosetE (rcoset_refl, rcoset_id).
Qed.

Lemma conjg_fix : forall A : {set gT}, 'C(A | 'J) = 'C(A).
Proof.
move=> A; apply/setP=> x; apply/afixP/centP=> cAx y Ay /=.
  by rewrite /commute conjgC cAx.
by rewrite conjgE cAx ?mulKg.
Qed.

Lemma conjg_astab : forall A : {set gT}, 'C_(| 'J)(A) = 'C(A).
Proof.
move=> A; apply/setP=> x; apply/astabP/centP=> cAx y Ay /=.
  by apply: esym; rewrite conjgC cAx.
by rewrite conjgE -cAx ?mulKg.
Qed.

Lemma conjg_astab1 : forall x : gT, 'C_(| 'J)[x] = 'C[x].
Proof. by move=> x; rewrite conjg_astab cent_set1. Qed.

Lemma conjsg_astab1 : forall A : {set gT}, 'C_(| 'Js)[A] = 'N(A).
Proof. by move=> A; apply/setP=> x; apply/astab1P/normP. Qed.

Lemma conjG_astab1 : 'C_(| 'JG)[G] = 'N(G).
Proof.
by apply/setP=> x; apply/astab1P/normP; [move/(congr1 val) | move/group_inj].
Qed.

(* Other group action identities, most of which hold by conversion
   Outcommented for now, until we require them.
Lemma conjg_orbit : forall x, orbit 'J%act G x = x ^: G.
Proof. by []. Qed.

Lemma rtrans_orbit : forall A : {set gT}, orbit 'Msr%act G A = rcosets A G.
Proof. by []. Qed.

Lemma rmul_orbit : forall x, orbit 'Mr%act G x = x *: G.
Proof. by move=> x; rewrite -lcosetE. Qed.

Lemma conjsg_orbit : forall A : {set gT}, orbit 'Js%act G A = A :^: G.
Proof. by []. Qed.
*)
End Bij.

Section CardClass.

Variables (gT : finGroupType) (G : {group gT}).

Lemma index_cent1 : forall x, #|G : 'C_G[x]| = #|x ^: G|.
Proof. by move=> x; rewrite -conjg_astab1 -card_orbit. Qed.

Lemma sum_card_class : \sum_(C \in classes G) #|C| = #|G|.
Proof. apply: acts_sum_card_orbit; apply/actsP=> x Gx y; exact: groupJr. Qed.

Lemma class_formula : \sum_(C \in classes G) #|G : 'C_G[repr C]| = #|G|.
Proof.
rewrite -sum_card_class; apply: eq_bigr => C; case/imsetP=> x Gx ->.
have: x \in x ^: G by rewrite -{1}(conjg1 x) mem_imset.
by move/mem_repr; case/imsetP=> y Gy ->; rewrite index_cent1 classGidl.
Qed.

End CardClass.

(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Definition of permutation as an action                             *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)

Section PermAction.

Variable sT : finType.
Notation gT := {perm sT}.
Implicit Types a b c : gT.

Definition aperm x (a : gT) := a x.

Definition apermE : forall x a, aperm x a = a x. Proof. by []. Qed.

Lemma aperm_is_action : is_action aperm.
Proof. by split=> [x|x a b]; rewrite apermE (perm1, permM). Qed.

Canonical Structure perm_action := Action aperm_is_action.

Lemma perm_act1P : forall a, reflect (forall x, aperm x a = x) (a == 1).
Proof.
move=> a; apply: (iffP eqP) => [-> x | a1]; first exact: act1.
by apply/permP=> x; rewrite -apermE a1 perm1.
Qed.

End PermAction.

Implicit Arguments perm_act1P [sT a].
Prenex Implicits perm_act1P.

Notation "'P" := (perm_action _) (at level 0) : action_scope.

Section PermFact.

Variable gT : finGroupType.
Variable sT : finType.
Variable to : {action gT &-> sT}.
Implicit Type A : {set gT}.

Definition actm A a := perm_of (act_inj to a).

Lemma actmE : forall A a x, actm A a x = to x a.
Proof. by move=> A a x; rewrite permE. Qed.

Lemma aperm_actm : forall A x a, aperm x (actm A a) = to x a.
Proof. move=> A x a; exact: actmE. Qed.

Lemma perm_of_actM : forall A, {morph actm A : a b / a * b}.
Proof. by move=> A a b; apply/permP => x; rewrite permM !permE actM. Qed.

Canonical Structure actm_morphism A :=
  @Morphism _ _ A _ (in2W (@perm_of_actM A)).

(* For equality we would need to restrict the permutation to S. *)
Lemma faithful_isom : forall (A : {group gT}) (S : {set sT}),
  [faithful (A | to) on S] -> isom A (actm A @: A) (actm A).
Proof.
move=> A S ffulA; apply/isomP; split; last exact: morphimEdom.
apply/subsetP=> a; case/morphpreP=> Aa; move/set1P=> /= a1; apply/set1P.
by apply: (faithfulP ffulA) => // x _; rewrite -(actmE A) a1 perm1.
Qed.

End PermFact.

(* We can't do the converse -- define an action from a morphism --  *)
(* without also restricting the action group type to the morphism   *)
(* domain. This only really makes sense for automorphism actions,   *)
(* but then it seems these are almost always best treated as        *)
(* internal actions.                                                *)

Section PrimitiveDef.

Variables (aT : finGroupType) (sT : finType).
Variables (A : {set aT}) (to : {action aT &-> sT}) (S : {set sT}).

Definition primitive :=
  (#|S| > 0) &&
  forallb R : {ffun sT -> {ffun sT -> bool}},
   [==> forallb x, (x \in S) ==> R x x,
        forallb x, forallb y, forallb a,
         [==> x \in S, y \in S, a \in A, R x y => R (to x a) == R (to y a)]
    => (forallb x, forallb y, [==> x \in S, y \in S, R x y => x == y])
    || (forallb x, forallb y, [==> x \in S, y \in S => R x y])].

Lemma primitiveP:
  reflect
  ((exists x, x \in S) /\ forall R : rel sT,
      (forall x, x \in S -> R x x)
   -> (forall x y a, x \in S -> y \in S -> a \in A ->
       R x y -> R (to x a) =1 R (to y a))
   -> (forall x y, x \in S -> y \in S -> R x y -> x = y)
   \/ (forall x y, x \in S -> y \in S -> R x y))
   primitive.
Proof.
apply: (iffP andP) => /= [] [nS0 prim].
  split=> [|R Rrefl Rinv]; first by rewrite lt0n in nS0; move/existsP: nS0.
  pose gR := [ffun x => [ffun y => R x y]]; simpl in gR.
  have{nS0 prim} := forallP prim gR; case: forallP => [_ | [x]]; last first.
    by apply/implyP=> Sx; rewrite !ffunE Rrefl.
  case: forallP => [_ /= | [x]]; last first.
    apply/forallP=> y; apply/forallP=> a; apply/implyP=> Sx; apply/implyP=> Sy.
    apply/implyP=> Aa; rewrite !ffunE; apply/implyP=> Rxy; apply/eqP.
    by apply/ffunP=> c; rewrite !ffunE (Rinv _ y).
  case/orP; move/forallP=> prim; [left | right] => x y Sx Sy => [Rxy|];
    move/(_ x): prim; move/forallP; move/(_ y); rewrite Sx Sy !ffunE ?Rxy //=.
  exact: eqP.
split; first by case: nS0 => x Sx; rewrite (cardD1 x) Sx.
apply/forallP=> R; apply/implyP; move/forallP=> Rrefl.
apply/implyP; move/forallP=> Rinv.
apply/orP; move/(_ (fun x y => R x y)): prim.
case=> [x | x y a Sx Sy Aa Rxy | R1 | RS]; first exact/implyP.
- move/forallP: (Rinv x); move/(_ y); move/forallP; move/(_ a).
  by rewrite Sx Sy Aa Rxy; case: eqP => // ->.
- left; apply/forallP=> x; apply/forallP=> y.
  by apply/implyP=> Sx; apply/implyP=> Sy; apply/implyP; move/R1->.
right; apply/forallP => x; apply/forallP => y; apply/implyP=> Sx.
apply/implyP; exact: RS.
Qed.

End PrimitiveDef.

Notation "[ 'primitive' ( A | to ) 'on' S ]" := (primitive A to S)
  (at level 0, format "[ 'primitive'  (  A  |  to  )  'on'  S ]") : form_scope.

Implicit Arguments primitiveP [aT sT A to S].
Prenex Implicits primitiveP.

Section Primitive.

Variables (aT : finGroupType) (sT : finType).
Variables (G : {group aT}) (to : {action aT &-> sT}) (S : {set sT}).

Hypothesis Gtrans : [transitive (G | to) on S].
Let Gact := actsP (trans_acts Gtrans).

Lemma primitivePt:
  reflect
    (forall Y : {set sT},
       Y \subset S -> wdisjointn (mem G) (fun a x => to x a \in Y)
     -> #|Y| <= 1 \/ Y = S)
   [primitive (G | to) on S].
Proof.
apply: (iffP primitiveP) => [[_ prim] Y sYS impY| prim].
  case: leqP => cardY; [by left | right]; apply/eqP; rewrite eqset_sub sYS /=.
  case: (pickP (mem Y)) => [x /= Yx | Y0]; last by rewrite eq_card0 in cardY.
  move/subsetP: sYS => sYS; have Sx := sYS x Yx.
  pose R b c := existsb x, [&& x \in G, to b x \in Y & to c x \in Y].
  case/(_ R): prim => [y Sy | {x Sx Yx} x y a Sx Sy Ga | R1 | RS].
  - move: Sx; rewrite -(atransP Gtrans _ Sy); case/imsetP=> a Ga toya.
    by apply/existsP; exists a; rewrite -toya Ga Yx.
  - case/existsP=> [b]; case/and3P=> Gb Yxb Yyb z.
    wlog Ryaz: x y Sx Sy Yxb Yyb / R (to y a) z.
      by move=> impl; apply/idP/idP => R_az; move/impl: (R_az) ->.
    rewrite Ryaz; case/existsP: Ryaz => c; case/and3P=> Gc Yyac Yzc.
    apply/existsP; exists c; rewrite Gc {z}Yzc /= andbT -actM.
    by rewrite (impY _ b y) //= (actM, groupM).
  - move: cardY; rewrite (cardD1 x) Yx ltnS lt0n; case/existsP=> y /=.
    case/andP=> nyx Yy; case/eqP: nyx; apply: R1; rewrite ?sYS //.
    by apply/existsP; exists (1 : aT); rewrite group1 !act1 Yx Yy.
  apply/subsetP=> y Sy; case/existsP: (RS x y Sx Sy) => a; case/and3P=> Ga Yxa.
  move: Sy; rewrite -(atransP Gtrans x Sx); case/imsetP=> b Gb ->{y} Yxba.
  by rewrite (impY _ (b * a) (to x b^-1)) //= ?(actM, groupM, actKV).
case/imsetP: Gtrans => x Sx S_xA; split=> [|R Rrefl Rinv]; first by exists x.
pose Y := S :&: [set y | R x y].
case/(_ Y (subsetIl _ _)): prim => [a b y /= Ga Gb Yya Yyb z | Y1 | YS].
- wlog Yzb: a b Ga Gb Yya Yyb / to z b \in Y.
    by move=> impl; apply/idP/idP => Yz_; move/impl: (Yz_) ->.
  rewrite Yzb; move: Yya Yyb Yzb; rewrite !inE.
  case/andP=> Sya Rxya; case/andP=> Syb Rxyb; case/andP=> Szb Rxzb.
  have Sza: to z a \in S by rewrite !Gact in Szb *.
  have Gb1a: b^-1 * a \in G by rewrite groupM ?groupV.
  rewrite Sza -(act1 to x) (Rinv _ (to y a)) //= act1 -(actK to b y) -actM.
  by rewrite -(Rinv x) // (Rinv _ (to z b)) // actM actK Rrefl.
- left=> y z Sy; rewrite S_xA; case/imsetP=> a Ga ->{z} Ryxa.
  move: Y1; rewrite (cardD1 x) (cardD1 (to y a^-1)) !inE /= !inE Sx Rrefl //=.
  case: eqP => [<- _|_]; first by rewrite actKV.
  rewrite Gact ?groupV // Sy -{1}(actK to a x).
  by rewrite -(Rinv y) ?(Gact, groupV, Rrefl).
right=> y z; rewrite -YS !inE; case/andP=> Sy Rxy; case/andP=> Sz Rxz.
by rewrite -(act1 to y) -(Rinv x) ?act1.
Qed.

Lemma prim_trans_norm : forall H : {group aT},
  [primitive (G | to) on S] -> H <| G ->
     H \subset 'C_(G | to)(S) \/ [transitive (H | to) on S].
Proof.
move=> H prim; case/normalP=> sHG nHG; pose R x y := y \in orbit to H x.
case: (primitiveP prim) => [] [x Sx].
case/(_ R)=> [{x Sx} x Sx | {x Sx} x y a Sx _ Ga | {x Sx} R1 | RS].
- exact: orbit_refl.
- case/imsetP=> b Hb ->{y} y; congr (y \in (_ : set _)); apply: orbit_transl.
  by rewrite actCJ orbit_sym mem_imset // -(nHG _ Ga) memJ_conjg.
- left; apply/subsetP => a Ha; have Ga: a \in G by apply: (subsetP sHG).
  rewrite inE Ga; apply/astabP=> x Sx; symmetry; apply: R1; rewrite ?Gact //.
  by rewrite [R _ _]mem_imset.
right; apply/imsetP; exists x => //.
apply/setP=> y; apply/idP/idP; first exact: RS.
by case/imsetP=> a Ha ->; rewrite Gact ?(subsetP sHG).
Qed.

End Primitive.

Section NactionDef.

Variables (gT : finGroupType) (sT : finType).

Variable to : {action gT &-> sT}.
Variable n :  nat.
Notation tT := (tuple n sT).

Definition n_act (t : tT) a : tT := [tuple of maps (to^~ a) t].

Lemma n_act_is_action : is_action n_act.
Proof.
by split=> [t|t a b]; apply: eq_from_tsub=> i; rewrite !tsub_maps ?act1 ?actM.
Qed.

Canonical Structure n_act_action := Action n_act_is_action.

End NactionDef.

Notation "to * n" := (n_act_action to n) : action_scope.

Section NTransitive.

Variables (gT : finGroupType) (sT : finType).
Variable n :  nat.
Variable A : {set gT}.
Variable to : {action gT &-> sT}.
Variable S : {set sT}.

Definition dtuple_on := [set t : tuple n sT | uniq t && (t \subset S)].
Definition ntransitive := [transitive (A | to * n) on dtuple_on].

Lemma dtuple_onP : forall t,
  reflect (injective (tsub t) /\ forall i, tsub t i \in S) (t \in dtuple_on).
Proof.
move=> t; rewrite inE subset_all -maps_tsub_enum.
case: (uniq _) / (injectiveP (tsub t)) => f_inj; last by right; case.
rewrite -[all _ _]negbK -has_predC has_maps has_predC negbK /=.
by apply: (iffP allP) => [Sf|[]//]; split=> // i; rewrite Sf ?mem_enum.
Qed.

Lemma n_act_dtuple : forall t a,
  a \in 'N_(|to)(S) -> t \in dtuple_on -> n_act to t a \in dtuple_on.
Proof.
move=> t a; move/astabsP=> toSa; case/dtuple_onP=> t_inj St; apply/dtuple_onP.
split=> [i j | i]; rewrite !tsub_maps ?[_ \in S]toSa //.
by move/act_inj; exact: t_inj.
Qed.

End NTransitive.

Implicit Arguments n_act [gT sT n].

Notation "[ 'transitive' * n ( A | to ) 'on' S ]" := (ntransitive n A to S)
  (at level 0, n at level 8,
   format "[ 'transitive'  *  n  ( A  |  to )  'on'  S ]") : form_scope.

Section NTransitveProp.

Variable (gT : finGroupType) (sT : finType).
Variable to : {action gT &-> sT}.
Variable G : {group gT}.
Variable S : {set sT}.

Lemma card_uniq_tuple m (t : tuple m sT) : uniq t -> #|t| = m.
Proof. move=> m t; move/card_uniqP->; exact: size_tuple. Qed.

Lemma n_act0 (t : tuple 0 sT) a : n_act to t a = [tuple].
Proof. move=> *; exact: tuple0. Qed.

Lemma dtuple_on_add : forall n x (t : tuple n sT),
  ([tuple of x :: t] \in dtuple_on n.+1 S) =
     [&& x \in S, x \notin t & t \in dtuple_on n S].
Proof. move=> *; rewrite !inE memtE !subset_all -!andbA; do !bool_congr. Qed.

Lemma dtuple_on_add_D1 : forall n x (t : tuple n sT),
  ([tuple of x :: t] \in dtuple_on n.+1 S)
     = (x \in S) && (t \in dtuple_on n (S :\ x)).
Proof.
move=> n x t; rewrite dtuple_on_add !inE (andbCA (~~ _)); do 2!congr (_ && _).
rewrite -!(eq_subset (in_set (mem t))) setD1E setIC subsetI; congr (_ && _).
by rewrite setC1E -setCS setCK sub1set !inE.
Qed.

Lemma dtuple_on_subset : forall n (S1 S2 : {set sT}) (t : tuple n sT),
  S1 \subset S2 -> t \in dtuple_on n S1 -> t \in dtuple_on n S2.
Proof.
move=> n S1 S2 t sS12; rewrite !inE; case/andP=> ->; move/subset_trans; exact.
Qed.

Lemma n_act_add m x (t : tuple m sT) a :
  n_act to [tuple of x :: t] a = [tuple of to x a :: n_act to t a].
Proof. by move=> *; exact: val_inj. Qed.

Lemma ntransitive0 : [transitive * 0 (G | to) on S].
Proof.
have dt0: [tuple] \in dtuple_on 0 S by rewrite inE memtE subset_all.
apply/imsetP; exists [tuple of Seq0 sT] => //.
by apply/setP=> x; rewrite [x]tuple0 orbit_refl.
Qed.

Lemma ntransitive_weak : forall k m,
  k <= m -> [transitive * m (G | to) on S] -> [transitive * k (G | to) on S].
Proof.
move=> k m; move/subnK <-; rewrite addnC; elim: {m}(m - k) => // m IHm.
rewrite addSn => tr_m1; apply: IHm; move: {m k}(m + k) tr_m1 => m tr_m1.
have ext_t: forall t, t \in dtuple_on m S ->
  exists x, [tuple of x :: t] \in dtuple_on m.+1 S.
- move=> /= t dt; case sSt: (S \subset t); last first.
    case/subsetPn: sSt => x Sx ntx.
    by exists x; rewrite dtuple_on_add andbA /= Sx ntx.
  case/imsetP: tr_m1 dt => t1.
  rewrite !inE; case/andP=> Ut1 St1 _; case/andP=> Ut _.
  have:= subset_trans St1 sSt; move/subset_leq_card.
  by rewrite !card_uniq_tuple // ltnn.
case/imsetP: (tr_m1); case/tupleP=> x t; rewrite dtuple_on_add.
case/and3P=> Sx ntx dt; set xt := [tuple of _] => tr_xt.
apply/imsetP; exists t => //.
apply/setP=> u; apply/idP/imsetP=> [du | [a Ga ->{u}]].
  case: (ext_t u du) => y; rewrite tr_xt.
  by case/imsetP=> a Ga [_ def_u]; exists a => //; exact: val_inj.
have: n_act to xt a \in dtuple_on _ S by rewrite tr_xt mem_imset.
by rewrite n_act_add dtuple_on_add; case/and3P.
Qed.

Lemma ntransitive1 : forall m,
  0 < m -> [transitive * m (G | to) on S] -> [transitive (G | to) on S].
Proof.
have trdom1: forall x, ([tuple x] \in dtuple_on 1 S) = (x \in S).
  by move=> x; rewrite dtuple_on_add !inE memtE subset_all andbT.
move=> m m_pos; move/(ntransitive_weak m_pos)=> {m m_pos}.
case/imsetP; case/tupleP=> x t0; rewrite {t0}(tuple0 t0) trdom1 => Sx trx.
apply/imsetP; exists x => //; apply/setP=> y; rewrite -trdom1 trx.
apply/imsetP/imsetP; case=> a Ga [->]; exists a => //; exact: val_inj.
Qed.

Lemma ntransitive_primitive : forall m,
  1 < m -> [transitive * m (G | to) on S] -> [primitive (G | to) on S].
Proof.
move=> m lt1m; move/(ntransitive_weak lt1m) => {m lt1m} Ht2.
apply/primitiveP; split=> [|f Hf1 Hf2].
  case/imsetP: Ht2; case/tupleP=> x t.
  by rewrite dtuple_on_add; case/andP; exists x.
case triv1: (forallb x, (x \in S) ==> (#|predI (mem S) (f x)| == 1%N)).
  left => x y Sx Sy Hf; apply/eqP; apply/idPn=> nxy.
  have:= forallP triv1 x; rewrite (cardD1 x) inE /= Sx Hf1 //=.
  by rewrite (cardD1 y) inE /= (eq_sym y) nxy inE /= Sy Hf.
case/existsP: triv1 => x; rewrite negb_imply; case/andP=> Sx.
rewrite (cardD1 x) inE /= Hf1 // Sx; case/pred0Pn => y /=.
case/and3P=> nxy Sy fxy; right=> x1 y1 Sx1 Sy1.
case: (x1 =P y1) => [-> //|]; [exact: Hf1 | move/eqP; rewrite eq_sym => nxy1].
pose t := [tuple y; x]; pose t1 := [tuple y1; x1].
have{Sx1 Sy1 nxy1} [dt dt1]: t \in dtuple_on 2 S /\ t1 \in dtuple_on 2 S.
  rewrite !inE !memtE !subset_all /= !mem_seq1 !andbT; split; exact/and3P.
case: (atransP2 Ht2 dt dt1) => a Ga [->] ->.
have trGS: [transitive (G | to) on S] by exact: ntransitive1 Ht2.
by move/Hf2: fxy => -> //; rewrite Hf1 // -(atransP trGS _ Sy) mem_imset.
Qed.

Lemma trans_prim_astab : forall x,
  x \in S -> [transitive (G | to) on S] ->
    [primitive (G | to) on S] = maximal_eq 'C_(G | to)[x] G.
Proof.
move=> x Sx Ht; apply/(primitivePt Ht)/maximal_eqP=> [Hp | [Hs Hst Y Hsub Hd]].
  split=> [|H Hk1 Hk2]; first exact: subsetIl.
  pose Y := orbit to H x; have Yx: x \in Y by exact: orbit_refl.
  case/(_ Y): Hp.
  - rewrite -(acts_orbit _ (trans_acts Ht)) in Sx.
    apply: subset_trans Sx; exact: imsetS.
  - move=> g1 g2 y /= Gg1 Gg2 Yyg1 Yyg2 z; apply: orbit_transr.
    rewrite -{1}(actK to g2 z) -actM mem_imset {z}//.
    case/imsetP: Yyg1 => h1 Hh1 yg1_xh1; case/imsetP: Yyg2 => h2 Hh2 yg2_xh2.
    rewrite -(groupMl _ Hh2) -[_ * _](mulgKV h1) groupMr //.
    apply: (subsetP Hk1); apply/setIP; split.
      by rewrite !(groupM, groupV) // (subsetP Hk2).
    by apply/astab1P; rewrite !actM -yg2_xh2 actK yg1_xh1 actK.
  - move=> Y1; left; apply/eqP; rewrite eqset_sub Hk1 subsetI Hk2 /= andbT.
    apply/subsetP=> a Ha; apply/astab1P.
    apply/set1P; rewrite (([set x] =P Y) _) ?mem_imset //.
    by rewrite eqset_sub_card sub1set Yx cards1.
  move=> YS; right; apply/eqP; rewrite eqset_sub Hk2; apply/subsetP => a Ga.
  have: to x a \in Y by rewrite YS -(atransP Ht _ Sx) mem_imset.
  case/imsetP=> b Hb xab; rewrite -(mulgKV b a) groupMr // (subsetP Hk1) //.
  rewrite inE groupMl // groupV (subsetP Hk2) //; apply/astab1P.
  by rewrite actM xab actK.
case: leqP => lt1Y; [by left | right]; apply/eqP; rewrite eqset_sub Hsub /=.
case: (pickP (mem Y)) lt1Y => [y /= Yy | Y0]; last by rewrite eq_card0.
have{Hd} defN: 'N_(G | to)(Y) = G :&: [set a | to y a \in Y].
  apply/setP=> a; rewrite !in_setI inE; case Ga: (a \in G) => //=.
  apply/astabsP/idP=> [-> // | Yya z].
  by rewrite (Hd a 1 y) ?act1 /=.
rewrite (cardD1 y) Yy ltnS lt0n; case/existsP=> z; case/andP=> nny /= Yz.
have:= subsetP Hsub _ Yy; rewrite -(atransP Ht x Sx); case/imsetP=> a Ga y_xa.
case: (Hst ('N_(G | to)(Y) :^ a^-1)%G) => /=.
- apply/subsetP=> b; case/setIP=> Gb; move/astab1P=> xb_x.
  by rewrite mem_conjgV defN !inE groupJ // y_xa -actCJ xb_x -y_xa.
- by rewrite conjIg conjGid (groupV, subsetIl).
- have:= subsetP Hsub z Yz; rewrite -(atransP Ht _  (subsetP Hsub y Yy)).
  case/imsetP=> b Gb z_yb Cx_NY; case/eqP: nny; rewrite z_yb y_xa actCJV.
  have: b \in 'N_(G | to)(Y) by rewrite defN !inE Gb -z_yb /=.
  by rewrite -(memJ_conjg _ a^-1) Cx_NY inE groupJ ?groupV //; move/astab1P->.
move=> NY_G; apply/subsetP=> t; case/imsetP=> b.
rewrite -{1}(mulgKV a b) groupMr // -NY_G defN mem_conjgV conjgE mulgKV.
by rewrite !inE actM y_xa actK; case/andP=> _ ? ->.
Qed.

End NTransitveProp.

Section NTransitveProp1.

Variable (gT : finGroupType) (sT : finType).

Variable to : {action gT &-> sT}.
Variable G : {group gT}.
Variable S : {set sT}.

(* Corresponds to => of 15.12.1 Aschbacher *)
Theorem stab_ntransitive : forall m x,
     0 < m -> x \in S ->  [transitive * m.+1 (G | to) on S]
  -> [transitive * m ('C_(G | to)[x] | to) on S :\ x].
Proof.
move=> m x m_pos Sx Gtr.
have sSxS: S :\ x \subset S by rewrite setD1E subsetIl.
case: (imsetP Gtr); case/tupleP=> x1 t1; rewrite dtuple_on_add.
case/and3P=> Sx1 nt1x1 dt1 trt1; have Gtr1 := ntransitive1 (ltn0Sn _) Gtr.
case: (atransP2 Gtr1 Sx1 Sx) => // a Ga x1ax.
pose t := n_act to t1 a.
have dxt: [tuple of x :: t] \in dtuple_on _ S.
  rewrite trt1 x1ax; apply/imsetP; exists a => //; exact: val_inj.
apply/imsetP; exists t.
  by rewrite dtuple_on_add_D1 Sx in dxt. 
apply/setP=> t2; apply/idP/imsetP => [dt2|[b]].
  have: [tuple of x :: t2] \in dtuple_on _ S by rewrite dtuple_on_add_D1 Sx.
  case/(atransP2 Gtr dxt)=> b Gb [xbx tbt2].
  exists b; [rewrite inE Gb; exact/astab1P | exact: val_inj].
case/setIP=> Gb; move/astab1P=> xbx ->{t2}.
rewrite n_act_dtuple //; last by rewrite dtuple_on_add_D1 Sx in dxt.
apply/astabsP=> y; rewrite !inE -{1}xbx (inj_eq (act_inj _ _)).
by rewrite (actsP (trans_acts Gtr1)).
Qed.

(* Correspond to <= of 15.12.1 Aschbacher *)
Theorem stab_ntransitiveI : forall m x,
     x \in S ->  [transitive (G | to) on S]
  -> [transitive * m ('C_(G | to)[x] | to) on S :\ x]
  -> [transitive * m.+1 (G | to) on S].
Proof.
move=> m x Sx Gtr Gntr.
have t_to_x: forall t, t \in dtuple_on m.+1 S ->
  exists2 a, a \in G & exists2 t', t' \in dtuple_on _ (S :\ x)
                                 & t = n_act to [tuple of x :: t'] a.
- case/tupleP=> y t St.
  have Sy: y \in S by rewrite dtuple_on_add_D1 in St; case/andP: St.
  rewrite -(atransP Gtr _ Sy) in Sx; case/imsetP: Sx => a Ga toya.
  exists a^-1; first exact: groupVr.
  exists (n_act to t a); last by rewrite n_act_add toya !actK.
  move/(n_act_dtuple (subsetP (trans_acts Gtr) a Ga)): St.
  by rewrite n_act_add -toya dtuple_on_add_D1; case/andP.
case: (imsetP Gntr) => t dt S_tG; pose xt := [tuple of x :: t].
have dxt: xt \in dtuple_on _ S by rewrite dtuple_on_add_D1 Sx.
apply/imsetP; exists xt => //; apply/setP=> t2.
symmetry; apply/imsetP/idP=> [[a Ga ->] | ].
  by apply: n_act_dtuple; rewrite // (subsetP (trans_acts Gtr)).
case/t_to_x=> a2 Ga2 [t2']; rewrite S_tG.
case/imsetP=> a; case/setIP=> Ga; move/astab1P=> toxa -> -> {t2 t2'}.
by exists (a * a2); rewrite (groupM, actM) //= !n_act_add toxa.
Qed.

(* => of 5.20 Aschbacher *)
Theorem subgroup_transitive : forall (H : {group gT}) x,
     x \in S -> H \subset G ->
       [transitive (G | to) on S] -> [transitive (H | to) on S]
  -> 'C_(G | to)[x] * H = G.
Proof.
move=> H x Hx H1 H2 H3.
apply/setP => z; apply/mulsgP/idP => [[hx1 k1 Hx1 Hk1 ->] | Hz].
  apply: groupM; last by apply: (subsetP H1).
  by case/setIP: Hx1.
pose y := to x z.
have: y \in S by rewrite -(atransP H2 x Hx) mem_imset.
rewrite -(atransP H3 x Hx); case/imsetP=> k Hk Hk1.
exists (z * k ^-1)  k => //; last by rewrite mulgKV.
rewrite inE groupMl // groupV (subsetP H1) //; apply/astab1P.
by rewrite actM -/y Hk1 actK.
Qed.

(* <= of 5.20 Aschbacher *)
Theorem subgroup_transitiveI : forall (H : {group gT}) x,
     x \in S -> H \subset G -> [transitive (G | to) on S]
  -> 'C_(G | to)[x] * H = G
  -> [transitive (H | to) on S].
Proof.
move=> H x Hx Hkh; move/atransP=> Ht Heq.
apply/imsetP; exists x => //; apply/setP=> y; symmetry.
apply/imsetP/idP => [[g1 Hg1 ->] | Hy].
  have F: g1 \in G by apply: (subsetP Hkh).
  by rewrite -(Ht _ Hx); apply/imsetP; exists g1.
have:= Hy; rewrite -(Ht _ Hx); case/imsetP=> ab.
rewrite -Heq; case/imset2P=> a b; case/setIP=> _; move/astab1P=> xax Hb -> ->.
by exists b; rewrite // actM xax.
Qed.

End NTransitveProp1.
