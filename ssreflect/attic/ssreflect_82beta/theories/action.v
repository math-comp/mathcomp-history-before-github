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
  (StructureOf (@Action _ _ a)
   match [is a : _ -> _ <: action _ _] as s
   return {type of @Action _ _ for s} -> _ with
   | Action _ actP => fun k => k actP
   end) (at level 0, only parsing) : form_scope.

Notation "[ 'action' 'o' 'f' a ]" := (StructureOf (@Action _ _ a) _)
  (at level 0, format "[ 'action'  'o' 'f'  a ]") : form_scope.

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

Definition faithful A to S := A :&: astab to S \subset [1].

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
  apply/eqP; rewrite eqEsubset sub1set orbit_refl.
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
rewrite {2}((S =P to^~ a @^-1: S) _) ?inE // eqEcard {}sSaS /=.
rewrite card_preimset //; exact: act_inj.
Qed.

Lemma group_set_astab : forall S, group_set 'C_(|to)(S).
Proof.
move=> S; apply/group_setP; split=> [|a b].
  by apply/astabP=> x _; rewrite act1.
move/astabP=> Ca; move/astabP=> Cb; apply/astabP=> x Sx.
by rewrite actM Ca ?Cb.
Qed.

Canonical Structure astab_group S := group (group_set_astab S).

Lemma group_set_astabs : forall S, group_set 'N_(|to)(S).
Proof.
move=> S; apply/group_setP; split=> [|a b].
  by apply/astabsP=> y; rewrite act1.
move/astabsP=> Na; move/astabsP=> Nb; apply/astabsP=> x.
by rewrite actM Nb Na.
Qed.

Canonical Structure astabs_group S := group (group_set_astabs S).

Lemma subset_astab : forall A S, 'C_(A | to)(S) \subset A.
Proof. move=> A S; exact: subsetIl. Qed.

Lemma card_orbit_stab : forall A x,
  (#|orbit to A x| * #|'C_(A | to)[x]|)%N = #|A|.
Proof.
move=> A x; rewrite -[#|A|]sum1_card (partition_big_imset (to x)) /=.
rewrite -sum_nat_const; apply: eq_bigr => y; case/imsetP=> a Aa ->{y}.
rewrite (reindex (mulg^~ a)) /= -?sum1_card; last first.
  by exists (mulg^~ a^-1) => b _; rewrite (mulgK, mulgKV).
apply: eq_bigl => b; rewrite inE groupMr // actM inE sub1set inE.
by rewrite (inj_eq (@act_inj a)).
Qed.

Lemma card_orbit : forall A x, #|orbit to A x| = #|A : 'C_(A | to)[x]|.
Proof.
move=> A x; rewrite -divgS ?subsetIl //.
by rewrite -(card_orbit_stab A x) mulnK ?ltn_0group.
Qed.

Lemma dvdn_orbit : forall A x, #|orbit to A x| %| #|A|.
Proof. by move=> A x; rewrite -(card_orbit_stab A x) dvdn_mulr. Qed.

Lemma card_orbit1 : forall A x,
  #|orbit to A x| = 1%N -> orbit to A x = [set x].
Proof.
move=> A x orb1; apply/eqP; rewrite eq_sym eqEcard {}orb1 cards1.
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
move=> A S AactS; rewrite -sum1_card (partition_big_imset (orbit to A)) /=.
apply: eq_bigr => xS; case/imsetP=> x Sx ->{xS}; rewrite -sum1_card.
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
  by apply: eq_bigr => a _; rewrite -sum1_card.
rewrite (exchange_big_dep (mem S)) /= => [|a x _]; last by case/setIP.
set orbA := orbit to A; rewrite (partition_big_imset orbA) -sum_nat_const /=.
apply: eq_bigr => X; case/imsetP=> x Sx ->{X}.
rewrite (eq_bigl (mem (orbA x))) => [|y] /=; last first.
  apply/andP/idP=> [[_]|xAy]; first by move/eqP <-; exact: orbit_refl.
  by rewrite /orbA (orbit_transl xAy) (orbit_in_act AactS xAy).
rewrite -(card_orbit_stab A x) -sum_nat_const.
apply: eq_bigr => y; rewrite orbit_sym; case/imsetP=> a Aa defx.
rewrite defx astab1_to (subsetP (normG _), cardJg) // -sum1_card.
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
  rewrite ((_ @: S =P [set S]) _) ?cards1 // eqEsubset sub1set.
  apply/andP; split=> //; apply/subsetP=> X; case/imsetP=> x Sx ->.
  by rewrite inE (atransP AtrS).
rewrite eqn_leq andbC lt0n; case/andP.
case/existsP=> X; case/imsetP=> x Sx X_Ax.
rewrite (cardD1 X) {X}X_Ax mem_imset // ltnS leqn0; move/eqP=> AtrS.
apply/imsetP; exists x => //; apply/eqP.
rewrite eqEsubset acts_orbit // Sx andbT.
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

(* Aschbacher 5.20 *)
Theorem subgroup_transitiveP : forall (G H : {group aT}) S x,
     x \in S -> H \subset G -> [transitive (G | to) on S] ->
  reflect ('C_(G | to)[x] * H = G) [transitive (H | to) on S].
Proof.
move=> G H S x Sx sHG trG; apply: (iffP idP) => [trH | defG].
  rewrite group_modr //; apply/setIidPl; apply/subsetP=> a Ga.
  have Sxa: to x a \in S by rewrite (actsP (trans_acts trG)).
  have [b Hb xab]:= atransP2 trH Sxa Sx.
  by rewrite -(mulgK b a) mem_mulg ?groupV //; apply/astab1P; rewrite actM.
apply/imsetP; exists x => //; apply/setP=> y; rewrite -(atransP trG Sx).
apply/imsetP/imsetP=> [] [a]; last by exists a; first exact: (subsetP sHG).
rewrite -defG; case/imset2P=> c b; case/setIP=> _; move/astab1P=> xc Hb -> ->.
by exists b; rewrite // actM xc.
Qed.

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

Section SetAction.

Variables (aT : finGroupType) (sT : finType) (to : {action aT &-> sT}).

Definition set_act (S : {set sT}) a := to^~ a @: S.

Lemma is_set_action : is_action set_act.
Proof.
split=> [S | S a b].
  apply/eqP; rewrite eqEcard card_imset ?leqnn ?andbT; last exact: act_inj.
  by apply/subsetP=> x1; case/imsetP=> x Sx ->; rewrite act1.
rewrite /set_act -imset_comp; apply: eq_imset => x; exact: actM.
Qed.

Canonical Structure set_action := Action is_set_action.

Lemma astab1_set : forall S, 'C_(|set_action)[S] = 'N_(|to)(S).
Proof.
move=> S; apply/setP=> a; rewrite -groupV !inE sub1set inE /=.
rewrite /set_act (can_imset_pre _ (actKV to _)) eq_sym eqEcard andbC.
by rewrite card_preimset ?leqnn //; exact: act_inj.
Qed.

End SetAction.

Notation "to ^*" := (set_action to)
  (at level 2, format "to ^*") : action_scope.

(*  Definition of the right translation as an action on cosets.        *)

Section GroupActions.

Variable gT : finGroupType.
Implicit Type A : {set gT}.
Implicit Type G : {group gT}.

Canonical Structure mulgr_action := Action (@mulg1 gT, @mulgA gT).

Canonical Structure conjg_action := Action (@conjg1 gT, @conjgM gT).

Lemma rcoset_is_action : is_action (@rcoset gT).
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

Variable (gT : finGroupType).
Implicit Types A B : {set gT}.
Implicit Types H G : {group gT}.

(*  Various identities for actions on groups; may need some trimming.  *)

Lemma act_fix_sub : forall G x A,
 (G :* x \in 'C(A | 'Msr)) = (A \subset G :^ x).
Proof.
move=> G x A; rewrite inE /=; apply: eq_subset_r => a.
rewrite inE rcosetE -(can2_eq (rcosetKV x) (rcosetK x)) -!rcosetM.
rewrite (conjgCV x) mulgK eqEcard card_rcoset leqnn andbT.
by rewrite -{2 3}(mulGid G) mulGS sub1set -mem_conjg.
Qed.

Lemma act_fix_norm : forall G x, (G :* x \in 'C(G | 'Msr)) = (x \in 'N(G)).
Proof. by move=> G x; rewrite act_fix_sub -groupV inE sub_conjgV. Qed.

Lemma rtrans_fix_norm : forall A G,
  'C_(rcosets G A)(G | 'Msr) = rcosets G 'N_A(G).
Proof.
move=> A G; apply/setP=> Gx; apply/setIP/rcosetsP=> [[]|[x]].
  case/rcosetsP=> x Ax ->{Gx}; rewrite act_fix_norm => Nx.
  by exists x; rewrite // inE Ax.
by case/setIP=> Ax Nx ->; rewrite -{1}rcosetE mem_imset // act_fix_norm.
Qed.

Lemma rtrans_stabG : forall G, 'C_(| 'Msr)[G : {set gT}] = G.
Proof.
move=> G; apply/setP=> x.
by apply/astab1P/idP=> /= [<- | Gx]; rewrite rcosetE (rcoset_refl, rcoset_id).
Qed.

Lemma conjg_fix : forall A, 'C(A | 'J) = 'C(A).
Proof.
move=> A; apply/setP=> x; apply/afixP/centP=> cAx y Ay /=.
  by rewrite /commute conjgC cAx.
by rewrite conjgE cAx ?mulKg.
Qed.

Lemma conjg_astab : forall A, 'C_(| 'J)(A) = 'C(A).
Proof.
move=> A; apply/setP=> x; apply/astabP/centP=> cAx y Ay /=.
  by apply: esym; rewrite conjgC cAx.
by rewrite conjgE -cAx ?mulKg.
Qed.

Lemma conjg_astab1 : forall x : gT, 'C_(| 'J)[x] = 'C[x].
Proof. by move=> x; rewrite conjg_astab cent_set1. Qed.

Lemma conjg_astabs : forall G, 'N_(|'J)(G) = 'N(G).
Proof.
by move=> G; apply/setP=> x; rewrite -2!groupV !inE -conjg_preim -sub_conjg.
Qed.

Lemma conjsg_astab1 : forall A, 'C_(| 'Js)[A] = 'N(A).
Proof. by move=> A; apply/setP=> x; apply/astab1P/normP. Qed.

Lemma conjG_fix: forall G A, (G \in 'C(A | 'JG)) = (A \subset 'N(G)).
Proof.
by move=> G A; apply/afixP/normsP=> nG x Ax; apply/eqP; move/eqP: (nG x Ax).
Qed.

Lemma conjG_astab1 : forall G, 'C_(| 'JG)[G] = 'N(G).
Proof.
move=> G; apply/setP=> x.
by apply/astab1P/normP; [move/(congr1 val) | move/group_inj].
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

Definition actm A a := perm (act_inj to a).

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
