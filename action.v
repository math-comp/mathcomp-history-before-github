(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq fintype.
Require Import tuple finfun bigops finset groups perm morphisms normal.

(*****************************************************************************)
(* Group action: orbits, stabilizers, transitivity.                          *)
(*        is_action to A == the function to : T -> aT -> T defines an action *)
(*                          of A : {set aT} on T                             *)
(*            action A T == structure for a function defining an action of A *)
(*    {action: aT &-> T} == structure for a total action                     *)
(*                       == action [set: aT] T                               *)
(*   TotalAction to1 toM == the constructor for total actions; to1 and toM   *)
(*                          are the proofs of the morphism identities for 1  *)
(*                          and a * b, respectively.                         *)
(*      orbit to A x == the orbit of x under the action of A via to          *)
(*      'C_A[x | to] == the stabilizer of x : sT in A :&: D                  *)
(*      'C_A(S | to) == the pointwise stabilizer of S : {set sT} in A :&: D  *)
(*      'N_A(S | to) == the global stabilizer of S : {set sT} in A :&: D     *)
(*  'Fix_(S | to)[a] == the set of fixpoints of a in S                       *)
(*  'Fix_(S | to)(A) == the set of fixpoints of A in S                       *)
(* In the first three _A can be omitted and defaults to the domain D of to;  *)
(* In the last two S can be omitted and defaults to [set: T], so 'Fix_to[a]  *)
(* is the set of all fixpoints of a.                                         *)
(*   The domain restriction ensures that stabilizers have a canonical group  *)
(* structure, but note that 'Fix sets are generally not groups.              *)
(*          [acts A, on S | to] == A \subset D acts on the set S via to      *)
(*          {acts A, on S | to} == A acts on the set S (Prop statement)      *)
(*    [transitive A, on S | to] == A acts transitively on S                  *)
(*      [faithful A, on S | to] == A acts faithfully on S                    *)
(* Important caveat: the definitions of orbit, 'Fix_(S | to)(A), transitive, *)
(* and faithful assume that A is a subset of the domain D. As most of the    *)
(* actions we consider are total, this is usually harmless (note that the    *)
(* theory of partial actions is only very partially developed).              *)
(*   In all of the above, to is expected to be the actual action structure,  *)
(* not merely the function. There is a special scope %act for actions, and   *)
(* constructions and notations for many classical actions:                   *)
(*      'P == natural action of a permutation group (via the aperm function) *)
(*      'J == internal group action (via conjuation)                         *)
(*      'R == regular group action (via right translation)                   *)
(*    to^* == the action of to lifted (pointwise) to subsets                 *)
(*     'Js == the conjugation action on subsets, equivalent to 'J^*.         *)
(*    ' Rs == the right translation action on subsets, equivalent to 'R^*.   *)
(*     'JG == the conjugation action on group structures.                    *)
(*  to / H == the action of to lifted to coset_of H (w. restricted domain).  *)
(*      'Q == the conjugation action lifted to cosets (w. domain 'N_D(H)).   *)
(* to %% A == the action of to taken mod A, with support 'C(D :&: A | to).   *)
(*   restr_action to sAD == the action to restricted to sAD : A \subset D.   *)
(*       sub_act(ion) to == the action to corestricted to a subType          *)
(*   sub_action_dom P to == the domain of sub_act for ssT : subType P.       *)
(*               actm to == the morphism D >-> {perm sT} induced by to.      *)
(*    morph_act(ion) phi == the action induced by phi : D >-> {perm sT}.     *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section ActionDef.

Variable aT : finGroupType.

Section Axioms.

Variables (T : Type) (to : T -> aT -> T).

CoInductive is_action (A : {set aT}) :=
  IsActionIn of forall a, injective (to^~ a)
              & {in A &, forall a b, to^~ (a * b) =1 to^~ b \o to^~ a}.

Lemma is_total_action :
    to^~ 1 =1 id -> (forall x a b, to x (a * b) = to (to x a) b) ->
  is_action setT.
Proof.
move=> to1 toM; split=> [a|a b _ _ x] /=; last by rewrite toM.
by apply: can_inj (to^~ a^-1) _ => x; rewrite -toM ?mulgV.
Qed.

End Axioms.

Record action A T := Action { afun :> T -> aT -> T; _ : is_action afun A}.

Definition TotalAction T to to1 toM := Action (@is_total_action T to to1 toM).

Definition repack_action A T f :=
  let: Action _ fP := f return {type of @Action A T for f} -> action A T
  in fun k => k fP.

End ActionDef.

Notation "{ 'action' aT &-> T }" := (action [set: aT] T)
  (at level 0, format "{ 'action'  aT  &->  T }") : type_scope.

Notation "[ 'action' 'of' to ]" :=
    (repack_action (fun aP => @Action _ _ _ to aP))
  (at level 0, format "[ 'action'  'of'  to ]") : form_scope.

Delimit Scope action_scope with act.
Bind Scope action_scope with action.

Section ActionOpsDef.

Variables (aT : finGroupType) (D : {set aT}) (sT : finType).
Implicit Type to : action D sT.
Implicit Type A : {set aT}.
Implicit Type S : {set sT}.

Definition afix to A := [set x | A \subset [set a | to x a == x]].

Definition astab S to := [set a \in D | S \subset [set x | to x a == x]].

Definition orbit to A x := to x @: A.

Definition astabs S to := [set a \in D | S \subset to^~ a @^-1: S ].

Definition acts_on S to := forall a x, (to x a \in S) = (x \in S).

Definition atrans A S to := S \in orbit to A @: S.

Definition faithful A S to := A :&: astab S to \subset [1].

End ActionOpsDef.

Notation "''Fix_' to ( A )" := (afix to A)
 (at level 8, to at level 2, format "''Fix_' to ( A )") : group_scope.

Notation "''Fix_' ( S | to ) ( A )" := (S :&: 'Fix_to(A))
 (at level 8, format "''Fix_' ( S  |  to ) ( A )") : group_scope.

Notation "''Fix_' to [ a ]" := ('Fix_to([set a]))
 (at level 8, to at level 2, format "''Fix_' to [ a ]") : group_scope.

Notation "''Fix_' ( S | to ) [ a ]" := (S :&: 'Fix_to[a])
 (at level 8, format "''Fix_' ( S  |  to ) [ a ]") : group_scope.

Notation "''C' ( S | to )" := (astab S to)
 (at level 8, format "''C' ( S  |  to )") : group_scope.

Notation "''C_' A ( S | to )" := (A :&: 'C(S | to))
 (at level 8, A at level 2, format "''C_' A ( S  |  to )") : group_scope.

Notation "''C' [ x | to ]" := ('C([set x] | to))
 (at level 8, format "''C' [ x  |  to ]") : group_scope.

Notation "''C_' A [ x | to ]" := (A :&: 'C[x | to])
 (at level 8, A at level 2, format "''C_' A [ x  |  to ]") : group_scope.

Notation "''N' ( S | to )" := (astabs S to)
  (at level 8, format "''N' ( S  |  to )") : group_scope.

Notation "''N_' A ( S | to )" := (A :&: 'N(S | to))
  (at level 8, A at level 2, format "''N_' A ( S  |  to )") : group_scope.

Notation "[ 'acts' A , 'on' S | to ]" := (A \subset pred_of_set 'N(S | to))
  (at level 0, format "[ 'acts'  A ,  'on'  S  |  to ]") : form_scope.

Notation "{ 'acts' A , 'on' S | to }" := {in A, acts_on S to}
  (at level 0, format "{ 'acts'  A ,  'on'  S  |  to }") : form_scope.

Notation "[ 'transitive' A , 'on' S | to ]" := (atrans A S to)
  (at level 0, format "[ 'transitive'  A ,  'on'  S  | to ]") : form_scope.

Notation "[ 'faithful' A , 'on' S | to ]" := (faithful A S to)
  (at level 0, format "[ 'faithful'  A ,  'on'  S  |  to ]") : form_scope.

Prenex Implicits orbit.

Section PartialAction.

Variable (aT : finGroupType) (D : {group aT}) (sT : finType).

Variable to : action D sT.

Implicit Types a b c : aT.
Implicit Types x y z : sT.
Implicit Types A B : {group aT}.
Implicit Types S : {set sT}.

Lemma act_inj : forall a, injective (to^~ a).
Proof. by case: to => ? []. Qed.

Lemma actM_in : {in D &, forall a b x, to x (a * b) = to (to x a) b}.
Proof. by case: to => ? []. Qed.

Lemma act1 : forall x, to x 1 = x.
Proof. by move=> x; apply: (@act_inj 1); rewrite -actM_in ?mulg1. Qed.

Lemma actK_in : forall a, a \in D -> cancel (to^~ a) (to^~ a^-1).
Proof. by move=> a Da x; rewrite -actM_in ?groupV // mulgV act1. Qed.

Lemma actKV_in : forall a, a \in D -> cancel (to^~ a^-1) (to^~ a).
Proof. by move=> a Da x; rewrite -{2}(invgK a) actK_in ?groupV. Qed.

Lemma orbitE : forall A x, orbit to A x = to x @: A. Proof. by []. Qed.

Lemma orbitP : forall A x y,
  reflect (exists2 a, a \in A & to x a = y) (y \in orbit to A x).
Proof. by move=> A x y; apply: (iffP imsetP) => [] [a]; exists a. Qed.

Lemma orbit_to : forall A x a, a \in A -> to x a \in orbit to A x.
Proof. move=> A x a; exact: mem_imset. Qed.

Lemma orbit_refl : forall A x, x \in orbit to A x.
Proof. by move=> A x; rewrite -{1}[x]act1 orbit_to. Qed.

Local Notation orbit_rel A := (fun x y => y \in orbit to A x).

Lemma orbit_sym_in : forall A, A \subset D -> symmetric (orbit_rel A).
Proof.
move=> A sAD; apply: symmetric_from_pre => x y; case/imsetP=> a Aa.
by move/(canLR (actK_in (subsetP sAD a Aa))) <-; rewrite orbit_to ?groupV.
Qed.

Lemma orbit_trans_in : forall A, A \subset D -> transitive (orbit_rel A).
Proof.
move=> A sAD y x z; case/imsetP=> a Aa ->; case/imsetP=> b Ab ->{y z}.
by rewrite -actM_in ?orbit_to ?groupM // (subsetP sAD).
Qed.

Lemma afixP : forall (A : {set aT}) x,
  reflect (forall a, a \in A -> to x a = x) (x \in 'Fix_to(A)).
Proof.
move=> A x; rewrite inE; apply: (iffP subsetP) => [xfix a | xfix a Aa].
  by move/xfix; rewrite inE; move/eqP.
by rewrite inE xfix.
Qed.

Lemma orbit1P : forall A x,
  reflect ([set x] = orbit to A x) (x \in 'Fix_to(A)).
Proof.
move=> A x; apply: (iffP (afixP _ _)) => [xfix | xfix a Aa].
  apply/eqP; rewrite eqEsubset sub1set -{1}[x]act1 mem_imset //=.
  by apply/subsetP=> y; case/imsetP=> a Aa ->; rewrite inE xfix.
by apply/set1P; rewrite xfix mem_imset.
Qed.

Lemma afix1P : forall a x, reflect (to x a = x) (x \in 'Fix_to[a]).
Proof. move=> a x; rewrite inE sub1set inE; exact: eqP. Qed.

Lemma astab_dom : forall S, {subset 'C(S | to) <= D}.
Proof. by move=> S a; case/setIdP. Qed.

Lemma astabP_in : forall S a x, a \in 'C(S | to) -> x \in S -> to x a = x.
Proof.
move=> S a x; case/setIdP=> _; move/subsetP=> cSa; move/cSa; rewrite inE.
by move/eqP.
Qed.

Lemma astabs_dom : forall S, {subset 'N(S | to) <= D}.
Proof. by move=> S a; case/setIdP. Qed.

Lemma astabsP_in : forall S a x,
  a \in 'N(S | to) -> (to x a \in S) = (x \in S).
Proof.
move=> S a x; case/setIdP=> _; rewrite subEproper properEcard.
rewrite (card_preimset _ (@act_inj _)) ltnn andbF orbF; move/eqP=> defS.
by rewrite {2}defS inE.
Qed.

Lemma group_set_astab : forall S, group_set 'C(S | to).
Proof.
move=> S; apply/group_setP; split=> [|a b cSa cSb].
  by rewrite inE group1; apply/subsetP=> x _; rewrite inE act1.
rewrite inE groupM ?(@astab_dom S) //; apply/subsetP=> x Sx.
by rewrite inE actM_in ?(@astab_dom S) ?(astabP_in _ Sx).
Qed.

Canonical Structure astab_group S := group (group_set_astab S).

Lemma group_set_astabs : forall S, group_set 'N(S | to).
Proof.
move=> S; apply/group_setP; split=> [|a b cSa cSb].
  by rewrite inE group1; apply/subsetP=> x Sx; rewrite inE act1.
rewrite inE groupM ?(@astabs_dom S) //; apply/subsetP=> x Sx.
by rewrite inE actM_in ?(@astabs_dom S) ?astabsP_in.
Qed.

Canonical Structure astabs_group S := group (group_set_astabs S).

Lemma subset_astab : forall A S, 'C_A(S | to) \subset A.
Proof. move=> A S; exact: subsetIl. Qed.

Lemma card_orbit1 : forall A x,
  #|orbit to A x| = 1%N -> orbit to A x = [set x].
Proof.
move=> A x orb1; apply/eqP; rewrite eq_sym eqEcard {}orb1 cards1.
by rewrite sub1set orbit_refl.
Qed.

Lemma actsP_dom : forall A S, [acts A, on S | to] -> A \subset D.
Proof.
by move=> A S nSA; apply/subsetP=> a; move/(subsetP nSA); case/setIdP.
Qed.

Lemma actsP_sub : forall A S, [acts A, on S | to] -> {acts A, on S | to}.
Proof. by move=> A S nAS a Aa x; rewrite astabsP_in ?(subsetP nAS). Qed.

Lemma acts_orbit : forall A S x,
  [acts A, on S | to] -> (orbit to A x \subset S) = (x \in S).
Proof.
move=> A S x; move/actsP_sub=> AactS.
apply/subsetP/idP=> [| Sx y]; first by apply; exact: orbit_refl.
by case/orbitP=> a Aa <-{y}; rewrite AactS.
Qed.

Lemma orbit_in_act : forall A S x y,
  [acts A, on S | to] -> y \in orbit to A x -> x \in S -> y \in S.
Proof. move=> A S x y; move/acts_orbit=> <- xAy; move/subsetP; exact. Qed.

Lemma subset_faithful : forall A B S,
  B \subset A -> [faithful A, on S | to] -> [faithful B, on S | to].
Proof. move=> A B S sAB; apply: subset_trans; exact: setSI. Qed.

End PartialAction.

Implicit Arguments act_inj [aT D sT].
Implicit Arguments orbitP [aT D sT to A x y].
Implicit Arguments afixP [aT D sT to A x].
Implicit Arguments afix1P [aT D sT to a x].
Implicit Arguments orbit1P [aT D sT to A x].
Prenex Implicits act_inj orbitP afixP afix1P orbit1P.

Notation "''C' ( S | to )" := (astab_group to S) : subgroup_scope.
Notation "''C_' A ( S | to )" := (A :&: 'C(S | to))%G : subgroup_scope.
Notation "''C' [ x | to ]" := ('C([set x] | to))%G : subgroup_scope.
Notation "''C_' A [ x | to ]" := (A :&: 'C[x | to])%G : subgroup_scope.
Notation "''N' ( S | to )" := (astabs_group to S) : subgroup_scope.
Notation "''N_' A ( S | to )" := (A :&: 'N(S | to))%G : subgroup_scope.

Section TotalAction.

Variable (aT : finGroupType) (sT : finType).

Variable to : {action aT &-> sT}.

Implicit Types a b c : aT.
Implicit Types x y z : sT.
Implicit Types A B : {group aT}.
Implicit Types S : {set sT}.

Lemma actM : forall x a b, to x (a * b) = to (to x a) b.
Proof. by move=> x a b; rewrite actM_in ?inE. Qed.

Lemma actK : forall a, cancel (to^~ a) (to^~ a^-1).
Proof. by move=> a; apply: actK_in; rewrite inE. Qed.

Lemma actKV : forall a, cancel (to^~ a^-1) (to^~ a).
Proof. by move=> a; apply: actKV_in; rewrite inE. Qed.

Lemma actX : forall x a n, to x (a ^+ n) = iter n (to^~ a) x.
Proof. by move=> x a; elim=> [|n /= <-]; rewrite ?act1 // -actM expgSr. Qed.

Lemma actCJ : forall a b x, to (to x a) b = to (to x b) (a ^ b).
Proof. by move=> a b x; rewrite !actM actK. Qed.

Lemma actCJV : forall a b x, to (to x a) b = to (to x (b ^ a^-1)) a.
Proof. by move=> a b x; rewrite (actCJ _ a) conjgKV. Qed.

Lemma orbit_sym : forall A x y, (y \in orbit to A x) = (x \in orbit to A y).
Proof. move=> A; apply: orbit_sym_in; exact: subsetT. Qed.

Lemma orbit_trans : forall A x y z,
  y \in orbit to A x -> z \in orbit to A y -> z \in orbit to A x.
Proof. move=> A x y z; apply: orbit_trans_in; exact: subsetT. Qed.

Lemma orbit_transl : forall A x y,
  y \in orbit to A x -> orbit to A y = orbit to A x.
Proof.
move=> A x y Axy; apply/setP=> z; apply/idP/idP; apply: orbit_trans => //.
by rewrite orbit_sym.
Qed.

Lemma orbit_transr : forall A x y z,
  y \in orbit to A x -> (y \in orbit to A z) = (x \in orbit to A z).
Proof.
by move=> A x y z Axy; rewrite orbit_sym (orbit_transl Axy) orbit_sym.
Qed.

Lemma orbit_eq_mem : forall A x y,
  (orbit to A x == orbit to A y) = (x \in orbit to A y).
Proof.
move=> A x y; apply/eqP/idP=> [<-|]; [exact: orbit_refl | exact: orbit_transl].
Qed.

Lemma astabP : forall S a,
  reflect (forall x, x \in S -> to x a = x) (a \in 'C(S | to)).
Proof.
move=> S a; apply: (iffP idP) => [cSa x|cSa]; first exact: astabP_in.
by rewrite !inE; apply/subsetP=> x Sx; rewrite inE cSa.
Qed.

Lemma astab1P : forall x a, reflect (to x a = x) (a \in 'C[x | to]).
Proof. move=> x a; rewrite !inE sub1set inE; exact: eqP. Qed.

Lemma astabsP : forall S a,
  reflect (forall x, (to x a \in S) = (x \in S)) (a \in 'N(S | to)).
Proof.
move=> S a; apply: (iffP idP) => [nSa x|nSa]; first exact: astabsP_in.
by rewrite !inE; apply/subsetP=> x; rewrite inE nSa.
Qed.

Lemma card_orbit_stab : forall A x,
  (#|orbit to A x| * #|'C_A[x | to]|)%N = #|A|.
Proof.
move=> A x; rewrite -[#|A|]sum1_card (partition_big_imset (to x)) /=.
rewrite -sum_nat_const; apply: eq_bigr => y; case/imsetP=> a Aa ->{y}.
rewrite (reindex (mulg^~ a)) /= -?sum1_card; last first.
  by exists (mulg^~ a^-1) => b _; rewrite (mulgK, mulgKV).
apply: eq_bigl => b; rewrite inE groupMr // actM inE sub1set !inE.
by rewrite (inj_eq (act_inj to a)). 
Qed.

Lemma card_orbit : forall A x, #|orbit to A x| = #|A : 'C_A[x | to]|.
Proof.
move=> A x; rewrite -divgS ?subsetIl //.
by rewrite -(card_orbit_stab A x) mulnK ?cardG_gt0.
Qed.

Lemma dvdn_orbit : forall A x, #|orbit to A x| %| #|A|.
Proof. by move=> A x; rewrite -(card_orbit_stab A x) dvdn_mulr. Qed. 

Lemma actsP : forall A S, reflect {acts A, on S | to} [acts A, on S | to].
Proof.
move=> A S; apply: (iffP idP) => [nSA x|nSA]; first exact: actsP_sub.
by apply/subsetP=> a Aa; rewrite !inE; apply/subsetP=> x; rewrite inE nSA.
Qed.
Implicit Arguments actsP [A S].

Lemma acts_sum_card_orbit : forall A S,
  [acts A, on S | to] -> \sum_(T \in orbit to A @: S) #|T| = #|S|.
Proof.
move=> A S AactS; rewrite -sum1_card (partition_big_imset (orbit to A)) /=.
apply: eq_bigr => xS; case/imsetP=> x Sx ->{xS}; rewrite -sum1_card.
apply: eq_bigl=> y; apply/idP/andP=> [xAy|[_]].
  by rewrite (orbit_transl xAy) (orbit_in_act _ xAy).
by move/eqP <-; exact: orbit_refl.
Qed.

Lemma astab_to : forall S a, 'C(to^~a @: S | to) = 'C(S | to) :^ a.
Proof.
move=> S a; apply/setP=> b; rewrite mem_conjg.
apply/astabP/astabP=> stab x => [Sx|].
  by rewrite conjgE invgK !actM stab ?actK //; apply/imsetP; exists x.
by case/imsetP=> y Sy ->{x}; rewrite -actM conjgCV actM stab.
Qed.

Lemma astab1_to : forall G x a,
  a \in 'N(G) -> 'C_G[to x a | to] = 'C_G[x | to] :^ a.
Proof.
by move=> G x a nGa; rewrite conjIg (normP nGa) -astab_to imset_set1.
Qed.

Theorem Frobenius_Cauchy : forall A S, [acts A, on S | to] ->
  \sum_(a \in A) #|'Fix_(S | to)[a]| = (#|orbit to A @: S| * #|A|)%N.
Proof.
move=> A S AactS.
transitivity (\sum_(a \in A) \sum_(x \in 'Fix_(S | to)[a]) 1%N).
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

Lemma atransP : forall A S, [transitive A, on S | to] ->
  forall x, x \in S -> orbit to A x = S.
Proof. move=> A S; case/imsetP=> x _ -> y; exact: orbit_transl. Qed.

Lemma atransP2 : forall A S, [transitive A, on S | to] ->
  {in S &, forall x y, exists2 a, a \in A & y = to x a}.
Proof. by move=> A S AtrS x y; move/(atransP AtrS) <-; move/imsetP. Qed.

Lemma trans_acts : forall A S,
  [transitive A, on S | to] -> [acts A, on S | to].
Proof.
move=> A S AtrS; apply/subsetP=> a Aa; rewrite !inE.
by apply/subsetP=> x; move/(atransP AtrS) <-; rewrite inE mem_imset.
Qed.

Lemma atrans_acts_card : forall A S,
  [transitive A, on S | to] =
     [acts A, on S | to] && (#|orbit to A @: S| == 1%N).
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

Lemma atrans_dvd : forall A S x,
  x \in S -> [transitive A, on S | to] -> #|S| %| #|A|.
Proof.
by move=> A S x Sx; move/atransP=> AtrS; rewrite -(AtrS x Sx) dvdn_orbit.
Qed.

(* Aschbacher 5.2 *)
Lemma norm_act_fix : forall A B, 
  A \subset 'N(B) -> [acts A, on 'Fix_to(B) | to].
Proof.
move=> A B; move/subsetP=> nBA; apply/actsP=> a Aa x.
apply/afixP/afixP=> fix_x b Bb.
  by rewrite -(actK a (to x b)) (actCJ b) fix_x (actK, memJ_norm) // nBA.
by rewrite actCJV fix_x // memJ_norm // groupV nBA.
Qed.

Lemma norm_stab : forall A B S, 
  A \subset 'N(B) -> 'C_A(S | to) \subset 'N('C_B(S | to)).
Proof.
move=> A B S nAB; apply/normsP=> a; case/setIP=> Aa; move/astabP=> toSa.
apply/setP=> b; rewrite mem_conjg !in_setI memJ_norm ?(groupV, subsetP nAB) //.
congr (_ && _); apply/astabP/astabP=> toSb x Sx.
  by rewrite -(toSa _ Sx) actCJV toSb.
by rewrite !actM invgK toSa ?toSb // -{1}(toSa x Sx) actK.
Qed.

Lemma faithfulP : forall A S,
  reflect (forall a, a \in A -> {in S, to^~ a =1 id} -> a = 1)
          [faithful A, on S | to].
Proof.
move=> A S; apply: (iffP subsetP) => [Cto1 a Aa Ca | Cto1 a].
  apply/set1P; rewrite Cto1 // inE Aa; exact/astabP.
case/setIP=> Aa; move/astabP=> Ca; apply/set1P; exact: Cto1.
Qed.

(* Aschbacher 5.20 *)
Theorem subgroup_transitiveP : forall (G H : {group aT}) S x,
     x \in S -> H \subset G -> [transitive G, on S | to] ->
  reflect ('C_G[x | to] * H = G) [transitive H, on S | to].
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

End TotalAction.

Implicit Arguments astabP [aT sT to S a].
Implicit Arguments astab1P [aT sT to x a].
Implicit Arguments astabsP [aT sT to S a].
Implicit Arguments atransP [aT sT to A S].
Implicit Arguments actsP [aT sT to A S].
Implicit Arguments faithfulP [aT sT to A S].
Prenex Implicits astabP astab1P astabsP atransP actsP faithfulP.

Section SetAction.

Variables (aT : finGroupType) (D : {group aT}) (sT : finType).
Variable to : action D sT.

Definition set_act (S : {set sT}) a := to^~ a @: S.

Lemma is_set_action : is_action set_act D.
Proof.
split=> [a S1 S2 eqS12 | a b Da Db S]; last first.
  rewrite /set_act /= -imset_comp; apply: eq_imset => x; exact: actM_in.
apply/setP=> x; wlog S1x: S1 S2 eqS12 / x \in S1.
  by move=> IH; apply/idP/idP=> Sx; move/IH: (Sx) => <-.
have: to x a \in set_act S1 a by apply/imsetP; exists x.
by rewrite eqS12 S1x; case/imsetP=> y S2y; move/act_inj->.
Qed.

Canonical Structure set_action := Action is_set_action.

Lemma astab1_set : forall S, 'C[S | set_action] = 'N(S |to).
Proof.
move=> S; apply/setP=> a; rewrite -groupV !inE sub1set inE /= groupV.
case Da: (a \in D) => //.
rewrite /set_act (can_imset_pre _ (actKV_in to Da)) eq_sym eqEcard.
by rewrite card_preimset ?leqnn ?andbT //; exact: act_inj.
Qed.

End SetAction.

Notation "to ^*" := (set_action to)
  (at level 2, format "to ^*") : action_scope.

Section RestrictAction.

Variables (aT : finGroupType) (A D : {set aT}) (sT : finType).
Variable to : action D sT.

Definition restr_act of A \subset D := to.

Lemma is_restr_action : forall sAD, is_action (restr_act sAD) A.
Proof.
rewrite /restr_act => sAD; case: to => f [f_inj fM]; split=> //=.
apply: sub_in2 fM; exact/subsetP.
Qed.

Canonical Structure restr_action sAD := Action (is_restr_action sAD).

End RestrictAction.

Section SubAction.

Variables (aT : finGroupType) (D : {group aT}).
Variables (sT : finType) (sP : pred sT) (ssT : subType sP) (to : action D sT). 

Definition sub_act_dom := 'N(finset sP | to).
Canonical Structure sub_act_dom_group := [group of sub_act_dom].

Lemma sub_act_proof : forall (u : ssT) (Na : subg_of sub_act_dom_group),
  sP (to (val u) (val Na)).
Proof.
move=> u [a] /=; case/setIdP=> _; move/subsetP; move/(_ (val u)).
by rewrite !inE valP => ->.
Qed.

Definition sub_act u a :=
  if insub a is Some Na then Sub _ (sub_act_proof u Na) else u.

Lemma val_sub_act : forall u a,
  val (sub_act u a) = if a \in sub_act_dom then to (val u) a else val u.
Proof.
move=> u a; rewrite /sub_act -if_neg.
by case: insubP => [Na|] -> //=; rewrite SubK => ->.
Qed.

Lemma is_sub_action : is_action sub_act sub_act_dom.
Proof.
split=> [a u v eq_uv | a b Na Nb u]; apply: val_inj.
  move/(congr1 val): eq_uv; rewrite !val_sub_act.
  by case: (a \in _); first move/act_inj.
have Da := astabs_dom Na; have Db := astabs_dom Nb. 
by rewrite !val_sub_act Na Nb groupM ?actM_in.
Qed.

Canonical Structure sub_action := Action is_sub_action.

End SubAction.

Section QuotientAction.

Variables (aT : finGroupType) (D : {group aT}) (sT : finGroupType).
Variables (to : action D sT) (H : {set sT}).

Definition quo_act := sub_act to^* : coset_of H -> _.

Canonical Structure quo_action := [action of quo_act].

End QuotientAction.

Notation "to / H" := (quo_action to H) : action_scope.

Section ModAction.

Variables (aT : finGroupType) (D H : {group aT}) (sT : finType).
Variable to : action D sT.

Definition mod_act_support := 'Fix_to(D :&: H).

Definition mod_act x (Ha : coset_of H) :=
  if x \in mod_act_support then to x (repr (D :&: Ha)) else x.

Lemma mod_act_coset : forall x a,
  x \in mod_act_support -> a \in 'N_D(H) -> mod_act x (coset H a) = to x a.
Proof.
move=> x a Cx; case/setIP=> Da Na; rewrite /mod_act Cx.
rewrite val_coset // -group_modr ?sub1set //.
case: (repr _) / (repr_rcosetP (D :&: H) a) => a' Ha'.
by rewrite actM_in ?(afixP Cx _ Ha') //; case/setIP: Ha'.
Qed.

Lemma mod_act_supp : forall x a,
  x \in mod_act_support -> a \in 'N_D(H) -> to x a \in mod_act_support.
Proof.
move=> x a Cx Na; have [Da _] := setIP Na.
apply/afixP=> b Hb; have [Db _] := setIP Hb.
rewrite -actM_in // conjgCV  actM_in ?groupJ ?groupV //; congr (to _ _).
apply: (afixP Cx); rewrite memJ_norm // groupV /=.
by apply: subsetP Na; rewrite normsI ?subsetIr ?subIset ?normG.
Qed.

Lemma is_mod_action : is_action mod_act (D / H).
Proof.
split=> [Ha x y | Ha Hb].
  case: (set_0Vmem (D :&: Ha)) => [Da0 | [a]].
    by rewrite /mod_act Da0 repr_set0 !act1 !if_same.
  case/setIP=> Da NHa; have Na := subsetP (coset_norm _) _ NHa.
  have NDa: a \in 'N_D(H) by rewrite inE Da.
  wlog Cx: x y / x \in mod_act_support.
    move=> IH; case Cx: (x \in mod_act_support); first exact: IH Cx.
    case Cy: (y \in mod_act_support); first by move/esym; move/IH->.
    by rewrite /mod_act Cx Cy.
  rewrite -(coset_mem NHa) mod_act_coset //.
  case Cy: (y \in mod_act_support).
    by rewrite mod_act_coset //; move/act_inj.
  by rewrite /mod_act Cy => def_y; rewrite -def_y mod_act_supp in Cy.
case/morphimP=> a Na Da ->{Ha}; case/morphimP=> b Nb Db ->{Hb} x /=.
rewrite -morphM //=; case Cx: (x \in mod_act_support).
  by rewrite !mod_act_coset ?mod_act_supp // ?groupM 1?inE ?actM_in ?Da ?Db.
by rewrite /mod_act !Cx.
Qed.

Canonical Structure mod_action := Action is_mod_action.

End ModAction.

Notation "to %% H" := (mod_action H to) : action_scope.

(* Conjugation and right translation actions. *)

Section GroupActions.

Variable gT : finGroupType.
Implicit Type A : {set gT}.
Implicit Type G : {group gT}.

Canonical Structure mulgr_action := TotalAction (@mulg1 gT) (@mulgA gT).

Canonical Structure conjg_action := TotalAction (@conjg1 gT) (@conjgM gT).

Lemma rcoset_is_action : is_action (@rcoset gT) setT.
Proof.
by apply: is_total_action => [A|A x y]; rewrite !rcosetE (mulg1, rcosetM).
Qed.

Canonical Structure rcoset_action := Action rcoset_is_action.

Canonical Structure conjsg_action := TotalAction (@conjsg1 gT) (@conjsgM gT).

Lemma conjG_is_action : is_action (@conjG_group gT) setT.
Proof.
by apply: is_total_action => G *; apply: group_inj; rewrite /= ?act1 ?actM.
Qed.

Definition conjG_action := Action conjG_is_action.

End GroupActions.

Notation "'R" := (@mulgr_action _) (at level 0) : action_scope.
Notation "'Rs" := (@rcoset_action _) (at level 0) : action_scope.
Notation "'J" := (@conjg_action _) (at level 0) : action_scope.
Notation "'Js" := (@conjsg_action _) (at level 0) : action_scope.
Notation "'JG" := (@conjG_action _) (at level 0) : action_scope.
Notation "'Q" := ('J / _)%act (at level 0) : action_scope.

Section Bij.

Variable gT : finGroupType.
Implicit Types A B : {set gT}.
Implicit Types H G : {group gT}.

(*  Various identities for actions on groups. *)

Lemma act_Cayley: forall G H, [acts G, on rcosets H G | 'Rs].
Proof.
move=> G H; apply/subsetP=> x Gx; rewrite 2!inE; apply/subsetP=> Hy.
case/rcosetsP=> y Gy ->{Hy}; rewrite inE /= rcosetE -rcosetM -rcosetE.
by rewrite mem_imset ?groupM.
Qed.

Lemma act_fix_sub : forall G x A,
 (G :* x \in 'Fix_'Rs(A)) = (A \subset G :^ x).
Proof.
move=> G x A; rewrite inE /=; apply: eq_subset_r => a.
rewrite inE rcosetE -(can2_eq (rcosetKV x) (rcosetK x)) -!rcosetM.
rewrite (conjgCV x) mulgK eqEcard card_rcoset leqnn andbT.
by rewrite -{2 3}(mulGid G) mulGS sub1set -mem_conjg.
Qed.

Lemma act_fix_norm : forall G x, (G :* x \in 'Fix_'Rs(G)) = (x \in 'N(G)).
Proof. by move=> G x; rewrite act_fix_sub -groupV inE sub_conjgV. Qed.

Lemma rtrans_fix_norm : forall A G,
  'Fix_(rcosets G A | 'Rs)(G) = rcosets G 'N_A(G).
Proof.
move=> A G; apply/setP=> Gx; apply/setIP/rcosetsP=> [[]|[x]].
  case/rcosetsP=> x Ax ->{Gx}; rewrite act_fix_norm => Nx.
  by exists x; rewrite // inE Ax.
by case/setIP=> Ax Nx ->; rewrite -{1}rcosetE mem_imset // act_fix_norm.
Qed.

Lemma rtrans_stabG : forall G, 'C[G : {set gT} | 'Rs] = G.
Proof.
move=> G; apply/setP=> x.
by apply/astab1P/idP=> /= [<- | Gx]; rewrite rcosetE ?rcoset_refl ?rcoset_id.
Qed.

Lemma conjg_fix : forall A, 'Fix_'J(A) = 'C(A).
Proof.
move=> A; apply/setP=> x; apply/afixP/centP=> cAx y Ay /=.
  by rewrite /commute conjgC cAx.
by rewrite conjgE cAx ?mulKg.
Qed.

Lemma conjg_astab : forall A, 'C(A |'J) = 'C(A).
Proof.
move=> A; apply/setP=> x; apply/astabP/centP=> cAx y Ay /=.
  by apply: esym; rewrite conjgC cAx.
by rewrite conjgE -cAx ?mulKg.
Qed.

Lemma conjg_astab1 : forall x : gT, 'C[x |'J] = 'C[x].
Proof. by move=> x; rewrite conjg_astab cent_set1. Qed.

Lemma conjg_astabs : forall G, 'N(G | 'J) = 'N(G).
Proof.
by move=> G; apply/setP=> x; rewrite -2!groupV !inE -conjg_preim -sub_conjg.
Qed.

Lemma conjsg_astab1 : forall A, 'C[A | 'Js] = 'N(A).
Proof. by move=> A; apply/setP=> x; apply/astab1P/normP. Qed.

Lemma conjG_fix: forall G A, (G \in 'Fix_'JG(A)) = (A \subset 'N(G)).
Proof.
by move=> G A; apply/afixP/normsP=> nG x Ax; apply/eqP; move/eqP: (nG x Ax).
Qed.

Lemma conjG_astab1 : forall G, 'C[G | 'JG] = 'N(G).
Proof.
move=> G; apply/setP=> x.
by apply/astab1P/normP; [move/(congr1 val) | move/group_inj].
Qed.

Lemma conjg_orbit : forall G x, orbit 'J G x = x ^: G. Proof. by []. Qed.

Lemma rtrans_orbit : forall G A, orbit 'Rs G A = rcosets A G.
Proof. by []. Qed.

Lemma rmul_orbit : forall G x, orbit 'R G x = x *: G.
Proof. by move=> G x; rewrite -lcosetE. Qed.

Lemma conjsg_orbit : forall G A, orbit 'Js G A = A :^: G. Proof. by []. Qed.

Lemma set_actJ : forall A x, set_act 'J A x = A :^ x. Proof. by []. Qed.

Lemma dom_quo_act : forall G, sub_act_dom (coset_range G) 'J^* = 'N(G).
Proof.
move=> G; apply/setP=> x; rewrite 2!inE; apply/subsetP/normP=> Nx.
  move/implyP: {Nx}(Nx G); rewrite !inE genGid -{1}(rcoset1 G) -rcosetE.
  rewrite mem_imset ?group1 //= set_actJ.
  case/rcosetsP=> y Hy def_Gx; rewrite def_Gx rcoset_id //.
  by rewrite -(mulg1 G) rcoset_sym -def_Gx group1.
move=> Gy; rewrite !inE genGid; case/rcosetsP=> y Ny ->{Gy}.
by rewrite [_ x]conjsMg conjg_set1 Nx -rcosetE mem_imset ?groupJ // inE Nx.
Qed.

Lemma quo_actJ : forall G (Gy : coset_of G) x,
  quo_act 'J Gy x = if x \in 'N(G) then Gy ^ coset G x else Gy.
Proof.
move=> G Gy x; apply: val_inj; rewrite val_sub_act dom_quo_act.
case Nx: (x \in 'N(G)) => //; case: (cosetP Gy) => y Ny ->{Gy}.
rewrite -morphJ //= set_actJ !val_coset ?groupJ //.
by rewrite conjsMg conjg_set1 (normP Nx).
Qed.

Lemma quoJ_astab : forall G (Abar : {set coset_of G}),
  'C(Abar |'Q) = [set x \in 'N(G) | coset G x \in 'C(Abar)].
Proof.
move=> G Abar; apply/setP=> x; rewrite 2!inE /= dom_quo_act.
case Nx: (x \in 'N(G)) => //; rewrite -sub1set centsC cent_set1.
congr (Abar \subset (_ : {set _})) => {Abar}.
apply/setP=> Gy; rewrite inE quo_actJ Nx (sameP eqP conjg_fixP).
by rewrite (sameP cent1P eqP) (sameP commgP eqP).
Qed.

Lemma quoJ_astabs : forall A G Bbar,
  (A \subset 'C(Bbar | 'Q)) = (A \subset 'N(G)) && (A / G \subset 'C(Bbar)).
Proof.
move=> A G Bbar; rewrite quoJ_astab; apply/subsetP/andP=> [cA | [nGA cA] x Ax].
  split; first by apply/subsetP=> x; move/cA; case/setIdP.
  by apply/subsetP=> Gx; case/morphimP=> x Nx Ax ->; case/setIdP: (cA x Ax).
by have Nx := subsetP nGA x Ax; rewrite inE Nx (subsetP cA) // mem_morphim.
Qed.

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

(*  Natural action of permutation groups.                        *)

Section PermAction.

Variable sT : finType.
Notation gT := {perm sT}.
Implicit Types a b c : gT.

Lemma aperm_is_action : is_action (@aperm sT) setT.
Proof.
by apply: is_total_action => [x|x a b]; rewrite apermE (perm1, permM).
Qed.

Canonical Structure perm_action := Action aperm_is_action.

Lemma pcycleE : forall a, pcycle a = orbit perm_action <[a]>.
Proof. by []. Qed.

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

Variables (aT : finGroupType) (D : {group aT}) (sT : finType).
Variable to : action D sT.

Definition actm a := perm (act_inj to a).

Lemma actmE : forall a x, actm a x = to x a.
Proof. by move=> a x; rewrite permE. Qed.

Lemma aperm_actm : forall x a, aperm x (actm a) = to x a.
Proof. move=> x a; exact: actmE. Qed.

Lemma perm_of_actM : {in D &, {morph actm : a b / a * b}}.
Proof. by move=> a b Da Db; apply/permP=> x; rewrite permM !permE actM_in. Qed.

Canonical Structure actm_morphism := Morphism perm_of_actM.

Lemma faithful_isom : forall S,
  [faithful D, on S | to] -> isom D (actm @: D) actm.
Proof.
move=> S fful; apply/isomP; split; last exact: morphimEdom.
apply/subsetP=> a; case/morphpreP=> Da; move/set1P=> /= a1; apply/set1P.
apply/set1P; apply: (subsetP fful); rewrite !inE Da; apply/subsetP=> x _.
by rewrite inE -actmE a1 perm1.
Qed.

End PermFact.

Section MorphAct.

Variables (aT : finGroupType) (D : {group aT}) (sT : finType).
Variable phi : {morphism D >-> {perm sT}}.

Definition morph_act x a := phi a x.

Lemma morph_is_action : is_action morph_act D.
Proof.
split=> [a x y | a b Da Db x]; first exact: perm_inj.
by rewrite /morph_act morphM //= permM.
Qed.

Canonical Structure morph_action := Action morph_is_action.

Lemma morph_actE : forall x a, morph_act x a = phi a x. Proof. by []. Qed.

Lemma injm_faithful : 'injm phi -> [faithful D, on setT | morph_action].
Proof.
move/injmP=> phi_inj; apply/subsetP=> a; case/setIP=> Da.
move/astabP_in=> a1; apply/set1P; apply: phi_inj => //.
by apply/permP=> x; rewrite morph1 perm1 -morph_actE a1 ?inE.
Qed.

End MorphAct.
