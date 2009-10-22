(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq fintype.
Require Import bigops finset groups perm morphisms normal automorphism.

(*****************************************************************************)
(* Group action: orbits, stabilisers, transitivity.                          *)
(*        is_action D to == the function to : T -> aT -> T defines an action *)
(*                          of D : {set aT} on T                             *)
(*            action D T == structure for a function defining an action of D *)
(*            act_dom to == the domain D of to : action D rT                 *)
(*    {action: aT &-> T} == structure for a total action                     *)
(*                       == action [set: aT] T                               *)
(*   TotalAction to1 toM == the constructor for total actions; to1 and toM   *)
(*                          are the proofs of the action identities for 1    *)
(*                          and a * b, respectively.                         *)
(*   is_groupAction R to == to is a group action on range R: for all a in D, *)
(*                          the permutation induced by to a is in Aut R.     *)
(*                          Thus the action of D must be trivial outside R.  *)
(*       groupAction D R == the structure for group actions of D on R.       *)
(*                          This is a telescope on action D rT.              *)
(*         gact_range to == the range R of to : groupAction D R              *)
(*     GroupAction toAut == construct a groupAction for action to from       *)
(*                          toAut : actm to @* D \subset Aut R (actm to is   *)
(*                          the morphism to {perm rT} associated to 'to').   *)
(*      orbit to A x == the orbit of x under the action of A via to          *)
(*    amove to A x y == the set of a in A whose action send x to y           *)
(*      'C_A[x | to] == the stabiliser of x : rT in A :&: D                  *)
(*      'C_A(S | to) == the point-wise stabiliser of S : {set rT} in D :&: A *)
(*      'N_A(S | to) == the global stabiliser of S : {set rT} in D :&: A     *)
(*  'Fix_(S | to)[a] == the set of fixpoints of a in S                       *)
(*  'Fix_(S | to)(A) == the set of fixpoints of A in S                       *)
(* In the first three _A can be omitted and defaults to the domain D of to;  *)
(* In the last two S can be omitted and defaults to [set: T], so 'Fix_to[a]  *)
(* is the set of all fixpoints of a.                                         *)
(*   The domain restriction ensures that stabilisers have a canonical group  *)
(* structure, but note that 'Fix sets are generally not groups. Indeed, we   *)
(* provide alternative definitions when to is a group action on R:           *)
(*      'C_(G | to)(A) == the centraliser in R :&: G of the group action of  *)
(*                        D :&: A via to                                     *)
(*      'C_(G | to)[a] == the centraliser in R :&: G of a \in D, via to.     *)
(*   These sets are groups when G is. G can be omitted: 'C(|to)(A) is the    *)
(* centraliser in R of the action of D :&: A via to.                         *)
(*          [acts A, on S | to] == A \subset D acts on the set S via to      *)
(*          {acts A, on S | to} == A acts on the set S (Prop statement)      *)
(*    {acts A, on group G | to} == [acts A, on S | to] /\ G \subset R, i.e., *)
(*                                 A \subset D acts on G \subset R, via      *)
(*                                 to : groupAction D R                      *)
(*    [transitive A, on S | to] == A acts transitively on S                  *)
(*      [faithful A, on S | to] == A acts faithfully on S                    *)
(* Important caveat: the definitions of orbit, amove, 'Fix_(S | to)(A),      *)
(* transitive, and faithful assume that A is a subset of the domain D.       *)
(* As most of the actions we consider are total, this is usually harmless.   *)
(* (Note that the theory of partial actions is only partially developed.)    *)
(*   In all of the above, to is expected to be the actual action structure,  *)
(* not merely the function. There is a special scope %act for actions, and   *)
(* constructions and notations for many classical actions:                   *)
(*       'P == natural action of a permutation group via aperm               *)
(*       'J == internal group action (conjugation) via _ ^ _                 *)
(*       'R == regular group action (right translation) via _ * _            *)
(*             (but, to limit ambiguity, _ * _ is NOT a canonical action)    *)
(*     to^* == the action induced by to on {set rT} via to^* (== setact to)  *)
(*      'Js == the internal action on subsets via _ :^ _, equivalent to 'J^* *)
(*      'Rs == the regular action on subsets via rcoset, equivalent to 'R^*  *)
(*      'JG == the conjugation action on {group rT} via _ :^ _               *)
(*   to / H == the action induced by to on coset_of H via qact to H, and     *)
(*             restricted to qact_dom to H == 'N(rcosets H 'N(H) | to^* )    *)
(*       'Q == the action induced to cosets by conjugation; the domain is    *)
(*             qact_dom 'J H, which is provably equal to 'N(H).              *)
(*  to %% A == the action of coset_of A via modact to A, with domain D / A   *)
(*             and support restricted to 'C(D :&: A | to)                    *)
(* to \ sAD == the action of A via ract to sAD == to, if sAD : A \subset D.  *)
(*     'A_G == the permutation action restricted to Aut G, via autact G      *)
(*  <[nRA]> == the action of A on R via actby nRA == to in A and on R, and   *)
(*             the trivial action elsewhere; here nRA : [acts A, on R | to]  *)
(*             or nRA : {acts A, on group R | to}.                           *)
(*     to^? == the action induced by to on sT : @subType rT P, via subact to *)
(*             with domain subact_dom P to == 'N([set x | P x] | to)         *)
(*  <<phi>> == the action of phi : D >-> {perm rT}, via mact phi             *)
(* The explicit application of an action to is usually written (to%act x a), *)
(* where the %act omitted if to is an abstract action or a set action to0^*. *)
(* Note that this form will simplify and expose the acting function.         *)
(*   There is a %gact scope for group actions; the notations above are       *)
(* recognised in %gact when they denote canonical group actions.             *)
(*   Actions can be used to define morphisms:                                *)
(* actperm to == the morphism D >-> {perm rT} induced by to.                 *)
(*  actm to a == if a \in D the function on D induced by the action to, else *)
(*               else the identity function. If to is a group action with    *)
(*               range R then actm to a is canonically a morphism on R.      *)
(*  Finally, gprod.v will provide a semi-direct group construction that maps *)
(* an external group action to an internal one.                              *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section ActionDef.

Variables (aT : finGroupType) (D : {set aT}) (rT : Type).
Implicit Types a b : aT.
Implicit Type x : rT.

Definition act_morph to x := forall a b, to x (a * b) = to (to x a) b.

Definition is_action to :=
  left_injective to /\ forall x, {in D &, act_morph to x}.

Record action := Action {act :> rT -> aT -> rT; _ : is_action act}.

Definition repack_action to :=
  let: Action _ toP := to return {type of Action for to} -> action in
  fun k => k toP.

End ActionDef.

(* Need to close the Section here to avoid re-declaring all Argument Scopes *)
Delimit Scope action_scope with act.
Bind Scope action_scope with action.
Arguments Scope
  act [_ group_scope type_scope action_scope group_scope group_scope].
Arguments Scope repack_action [_ group_scope type_scope action_scope _].

Notation "{ 'action' aT &-> T }" := (action [set: aT] T)
  (at level 0, format "{ 'action'  aT  &->  T }") : type_scope.

Notation "[ 'action' 'of' to ]" :=
    (repack_action (fun aP => @Action _ _ _ to aP))
  (at level 0, format "[ 'action'  'of'  to ]") : form_scope.

Definition act_dom aT D rT of @action aT D rT := D.

Section TotalAction.

Variables (aT : finGroupType) (rT : Type) (to : rT -> aT -> rT).
Hypotheses (to1 : to^~ 1 =1 id) (toM : forall x, act_morph to x).

Lemma is_total_action : is_action setT to.
Proof.
split=> [a | x a b _ _] /=; last by rewrite toM.
by apply: can_inj (to^~ a^-1) _ => x; rewrite -toM ?mulgV.
Qed.

Definition TotalAction := Action is_total_action.

End TotalAction.

Section ActionDefs.
(* Most definitions on actions require a finType structure on rT *)

Variables (aT : finGroupType) (D : {set aT}) (rT : finType).
Implicit Type to : action D rT.
Implicit Type A : {set aT}.
Implicit Type S : {set rT}.

Definition actm to a := if a \in D then to^~ a else id.

Definition setact to S a := [set to x a | x <- S].

Definition orbit to A x := to x @: A.

Definition amove to A x y := [set a \in A | to x a == y].

Definition afix to A := [set x | A \subset [set a | to x a == x]].

Definition astab S to := D :&: [set a | S \subset [set x | to x a == x]].

Definition astabs S to := D :&: [set a | S \subset to^~ a @^-1: S].

Definition acts_on A S to := {in A, forall a x, (to x a \in S) = (x \in S)}.

Definition atrans A S to := S \in orbit to A @: S.

Definition faithful A S to := A :&: astab S to \subset [1].

End ActionDefs.

Notation "to ^*" := (setact to) (at level 2, format "to ^*") : fun_scope.

Prenex Implicits orbit amove.

Notation "''Fix_' to ( A )" := (afix to A)
 (at level 8, to at level 2, format "''Fix_' to ( A )") : group_scope.

(* camlp4 grammar factoring *)
Notation "''Fix_' ( to ) ( A )" := 'Fix_to(A)
  (at level 8, only parsing) : group_scope.

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

Notation "{ 'acts' A , 'on' S | to }" := (acts_on A S to)
  (at level 0, format "{ 'acts'  A ,  'on'  S  |  to }") : form_scope.

Notation "[ 'transitive' A , 'on' S | to ]" := (atrans A S to)
  (at level 0, format "[ 'transitive'  A ,  'on'  S  |  to ]") : form_scope.

Notation "[ 'faithful' A , 'on' S | to ]" := (faithful A S to)
  (at level 0, format "[ 'faithful'  A ,  'on'  S  |  to ]") : form_scope.

Section RawAction.
(* Lemmas that do not require the group structure on the action domain. *)
(* Some lemmas like actMin would be actually be valid for arbitrary rT, *)
(* e.g., for actions on a function type, but would be difficult to use  *)
(* as a view due to the confusion between parameters and assumptions.   *)

Variables (aT : finGroupType) (D : {set aT}) (rT : finType) (to : action D rT).

Implicit Types a : aT.
Implicit Types x y : rT.
Implicit Type A B : {set aT}.
Implicit Types S : {set rT}.

Lemma act_inj : left_injective to. Proof. by case: to => ? []. Qed.
Implicit Arguments act_inj [].

Lemma actMin : forall x, {in D &, act_morph to x}.
Proof. by case: to => ? []. Qed.

Lemma actmEfun : forall a, a \in D -> actm to a = to^~ a.
Proof. by rewrite /actm => a ->. Qed.

Lemma actmE : forall a, a \in D -> actm to a =1 to^~ a.
Proof. by move=> a Da; rewrite actmEfun. Qed.

Lemma setactE : forall S a, to^* S a = [set to x a | x <- S].
Proof. by []. Qed.

Lemma mem_setact : forall S a x, x \in S -> to x a \in to^* S a.
Proof. move=> S a; exact: mem_imset. Qed.

Lemma card_setact : forall S a, #|to^* S a| = #|S|.
Proof. by move=> S a; apply: card_imset; exact: act_inj. Qed.

Lemma setact_is_action : is_action D to^*.
Proof.
split=> [a R S eqRS | a b Da Db S]; last first.
  rewrite /setact /= -imset_comp; apply: eq_imset => x; exact: actMin.
apply/setP=> x; apply/idP/idP; move/(mem_setact a).
  by rewrite eqRS; case/imsetP=> y Sy; move/act_inj->.
by rewrite -eqRS; case/imsetP=> y Ry; move/act_inj->.
Qed.

Canonical Structure set_action := Action setact_is_action.

Lemma orbitE : forall A x, orbit to A x = to x @: A. Proof. by []. Qed.

Lemma orbitP : forall A x y,
  reflect (exists2 a, a \in A & to x a = y) (y \in orbit to A x).
Proof. by move=> A x y; apply: (iffP imsetP) => [] [a]; exists a. Qed.

Lemma mem_orbit : forall A x a, a \in A -> to x a \in orbit to A x.
Proof. move=> A x a; exact: mem_imset. Qed.

Lemma afixP : forall (A : {set aT}) x,
  reflect (forall a, a \in A -> to x a = x) (x \in 'Fix_to(A)).
Proof.
move=> A x; rewrite inE; apply: (iffP subsetP) => [xfix a | xfix a Aa].
  by move/xfix; rewrite inE; move/eqP.
by rewrite inE xfix.
Qed.

Lemma afix1P : forall a x, reflect (to x a = x) (x \in 'Fix_to[a]).
Proof. move=> a x; rewrite inE sub1set inE; exact: eqP. Qed.

Lemma astabIdom : forall S, 'C_D(S | to) = 'C(S | to).
Proof. by move=> S; rewrite setIA setIid. Qed.

Lemma astab_dom : forall S, {subset 'C(S | to) <= D}.
Proof. by move=> S a; case/setIP. Qed.

Lemma astab_act : forall S a x, a \in 'C(S | to) -> x \in S -> to x a = x.
Proof.
move=> S a x; rewrite 2!inE; case/andP=> _ cSa Sx; apply/eqP.
by have:= subsetP cSa x Sx; rewrite inE.
Qed.

Lemma astabsIdom : forall S, 'N_D(S | to) = 'N(S | to).
Proof. by move=> S; rewrite setIA setIid. Qed.

Lemma astabs_dom : forall S, {subset 'N(S | to) <= D}.
Proof. by move=> S a; case/setIdP. Qed.

Lemma astabs_act : forall S a x,
  a \in 'N(S | to) -> (to x a \in S) = (x \in S).
Proof.
move=> S a x; rewrite 2!inE subEproper properEcard; case/andP=> _.
rewrite (card_preimset _ (act_inj _)) ltnn andbF orbF; move/eqP=> defS.
by rewrite {2}defS inE.
Qed.

Lemma astab_sub : forall S, 'C(S | to) \subset 'N(S | to).
Proof.
move=> S; apply/subsetP=> a cSa; rewrite !inE (astab_dom cSa).
by apply/subsetP=> x Sx; rewrite inE (astab_act cSa).
Qed.

Lemma astabs_setact : forall S a, a \in 'N(S | to) -> to^* S a = S.
Proof.
move=> S a nSa; apply/eqP; rewrite eqEcard card_setact leqnn andbT.
by apply/subsetP=> xa; case/imsetP=> x Sx ->; rewrite astabs_act.
Qed.

Lemma astab1_set : forall S, 'C[S | set_action] = 'N(S | to).
Proof.
move=> S; apply/setP=> a; apply/idP/idP=> nSa.
  case/setIdP: nSa => Da; rewrite !inE Da sub1set inE; move/eqP=> defS.
  by apply/subsetP=> x Sx; rewrite inE -defS mem_setact.
by rewrite !inE (astabs_dom nSa) sub1set inE /= astabs_setact.
Qed.

Lemma acts_dom : forall A S, [acts A, on S | to] -> A \subset D.
Proof. by move=> A S nSA; rewrite (subset_trans nSA) ?subsetIl. Qed.

Lemma acts_act : forall A S, [acts A, on S | to] -> {acts A, on S | to}.
Proof. by move=> A S nAS a Aa x; rewrite astabs_act ?(subsetP nAS). Qed.

Lemma acts_in_orbit : forall A S x y,
  [acts A, on S | to] -> y \in orbit to A x -> x \in S -> y \in S.
Proof.
move=> A S x y nSA; case/imsetP=> a Aa ->{y} Sx.
by rewrite (astabs_act _ (subsetP nSA a Aa)).
Qed.

Lemma subset_faithful : forall A B S,
  B \subset A -> [faithful A, on S | to] -> [faithful B, on S | to].
Proof. move=> A B S sAB; apply: subset_trans; exact: setSI. Qed.

Section Reindex.

Variables (vT : Type) (idx : vT) (op : Monoid.com_law idx) (S : {set rT}).

Lemma reindex_astabs : forall a F, a \in 'N(S | to) ->
  \big[op/idx]_(i \in S) F i = \big[op/idx]_(i \in S) F (to i a).
Proof.
move=> a F nSa; rewrite (reindex_inj (act_inj a)); apply: eq_bigl => x.
exact: astabs_act.
Qed.

Lemma reindex_acts : forall A a F, [acts A, on S | to] -> a \in A ->
  \big[op/idx]_(i \in S) F i = \big[op/idx]_(i \in S) F (to i a).
Proof. move=> A a F nSA; move/(subsetP nSA); exact: reindex_astabs. Qed.

End Reindex.

End RawAction.

(* Warning: this directive depends on names of bound variables in the *)
(* definition of injective, in ssrfun.v.                              *)
Implicit Arguments act_inj [[aT] [D] [rT] x1 x2].

Notation "to ^*" := (set_action to) : action_scope.

Implicit Arguments orbitP [aT D rT to A x y].
Implicit Arguments afixP [aT D rT to A x].
Implicit Arguments afix1P [aT D rT to a x].
Prenex Implicits orbitP afixP afix1P.

Implicit Arguments reindex_astabs [aT D rT vT idx op S F].
Implicit Arguments reindex_acts [aT D rT vT idx op S A a F].

Section PartialAction.
(* Lemmas that require a (partial) group domain. *)

Variables (aT : finGroupType) (D : {group aT}) (rT : finType).
Variable to : action D rT.

Implicit Types a : aT.
Implicit Types x y : rT.
Implicit Types A B : {group aT}.
Implicit Types S : {set rT}.

Lemma act1 : forall x, to x 1 = x.
Proof. by move=> x; apply: (act_inj _ 1); rewrite -actMin ?mulg1. Qed.

Lemma actKin : {in D, right_loop invg to}.
Proof. by move=> a Da /= x; rewrite -actMin ?groupV // mulgV act1. Qed.

Lemma actKVin : {in D, rev_right_loop invg to}.
Proof. by move=> a Da /= x; rewrite -{2}(invgK a) actKin ?groupV. Qed.

Lemma setactVin : forall S a, a \in D -> to^* S a^-1 = to^~ a @^-1: S.
Proof.
move=> S a Da; apply: can2_imset_pre; [exact: actKVin | exact: actKin].
Qed.

Lemma orbit_refl : forall A x, x \in orbit to A x.
Proof. by move=> A x; rewrite -{1}[x]act1 mem_orbit. Qed.

Local Notation orbit_rel A := (fun x y => y \in orbit to A x).

Lemma sub_orbit_sym : forall A, A \subset D -> symmetric (orbit_rel A).
Proof.
move=> A sAD; apply: symmetric_from_pre => x y; case/imsetP=> a Aa.
by move/(canLR (actKin (subsetP sAD a Aa))) <-; rewrite mem_orbit ?groupV.
Qed.

Lemma sub_orbit_trans : forall A, A \subset D -> transitive (orbit_rel A).
Proof.
move=> A sAD y x z; case/imsetP=> a Aa ->; case/imsetP=> b Ab ->{y z}.
by rewrite -actMin ?mem_orbit ?groupM // (subsetP sAD).
Qed.

Lemma orbit1P : forall A x,
  reflect (orbit to A x = [set x]) (x \in 'Fix_to(A)).
Proof.
move=> A x; apply: (iffP afixP) => [xfix | xfix a Aa].
  apply/eqP; rewrite eq_sym eqEsubset sub1set -{1}[x]act1 mem_imset //=.
  by apply/subsetP=> y; case/imsetP=> a Aa ->; rewrite inE xfix.
by apply/set1P; rewrite -xfix mem_imset.
Qed.

Lemma card_orbit1 : forall A x,
  #|orbit to A x| = 1%N -> orbit to A x = [set x].
Proof.
move=> A x orb1; apply/eqP; rewrite eq_sym eqEcard {}orb1 cards1.
by rewrite sub1set orbit_refl.
Qed.

Lemma group_set_astab : forall S, group_set 'C(S | to).
Proof.
move=> S; apply/group_setP; split=> [|a b cSa cSb].
  by rewrite !inE group1; apply/subsetP=> x _; rewrite inE act1.
rewrite !inE groupM ?(@astab_dom _ _ _ to S) //; apply/subsetP=> x Sx.
by rewrite inE actMin ?(@astab_dom _ _ _ to S) ?(astab_act _ Sx).
Qed.

Canonical Structure astab_group S := group (group_set_astab S).

Lemma group_set_astabs : forall S, group_set 'N(S | to).
Proof.
move=> S; apply/group_setP; split=> [|a b cSa cSb].
  by rewrite !inE group1; apply/subsetP=> x Sx; rewrite inE act1.
rewrite !inE groupM ?(@astabs_dom _ _ _ to S) //; apply/subsetP=> x Sx.
by rewrite inE actMin ?(@astabs_dom _ _ _ to S) ?astabs_act.
Qed.

Canonical Structure astabs_group S := group (group_set_astabs S).

Lemma astab_norm : forall S, 'N(S | to) \subset 'N('C(S | to)).
Proof.
move=> S; apply/subsetP=> a nSa; rewrite inE sub_conjg; apply/subsetP=> b cSb.
have [Da Db] := (astabs_dom nSa, astab_dom cSb).
rewrite mem_conjgV !inE groupJ //; apply/subsetP=> x Sx.
rewrite inE !actMin ?groupM ?groupV //.
by rewrite (astab_act cSb) ?actKVin ?astabs_act ?groupV.
Qed.

Lemma astab_normal : forall S, 'C(S | to) <| 'N(S | to).
Proof. by move=> S; rewrite /normal astab_sub astab_norm. Qed.

Lemma acts_sub_orbit : forall A S x,
  [acts A, on S | to] -> (orbit to A x \subset S) = (x \in S).
Proof.
move=> A S x; move/acts_act=> AactS.
apply/subsetP/idP=> [| Sx y]; first by apply; exact: orbit_refl.
by case/orbitP=> a Aa <-{y}; rewrite AactS.
Qed.

Lemma acts_orbit : forall A x, A \subset D -> [acts A, on orbit to A x | to].
Proof.
move=> A x; move/subsetP=> sAD; apply/subsetP=> a Aa; rewrite !inE sAD //.
apply/subsetP=> xb; case/imsetP=> b Ab ->{xb}.
by rewrite inE -actMin ?sAD // mem_imset ?groupM.
Qed.

Lemma acts_subnorm_fix : forall A, [acts 'N_D(A), on 'Fix_to(D :&: A) | to].
Proof.
move=> A; apply/subsetP=> a nAa; have [Da _] := setIP nAa; rewrite !inE Da.
apply/subsetP=> x Cx; rewrite inE; apply/afixP=> b DAb.
have [Db _]:= setIP DAb; rewrite -actMin // conjgCV  actMin ?groupJ ?groupV //.
by rewrite /= (afixP Cx) // memJ_norm // groupV (subsetP (normsGI _ _) _ nAa).
Qed.

Lemma atrans_orbit : forall A x, [transitive A, on orbit to A x | to].
Proof. move=> A x; apply: mem_imset; exact: orbit_refl. Qed.

Section OrbitStabilizer.

Variables (A : {group aT}) (x : rT).
Hypothesis sAD : A \subset D.
Let ssAD := subsetP sAD.

Lemma amove_act : forall a,
  a \in A -> amove to A x (to x a) = 'C_A[x | to] :* a.
Proof.
move=> a Aa; apply/setP => b; have Da := ssAD Aa.
rewrite mem_rcoset !(inE, sub1set) !groupMr ?groupV //.
by case Ab: (b \in A); rewrite //= actMin ?groupV ?ssAD ?(canF_eq (actKVin Da)).
Qed.

Lemma amove_orbit : amove to A x @: orbit to A x = rcosets 'C_A[x | to] A.
Proof.
apply/setP => Ha; apply/imsetP/rcosetsP=> [[y] | [a Aa ->]].
  by case/imsetP=> b Ab -> ->{Ha y}; exists b => //; rewrite amove_act.
by rewrite -amove_act //; exists (to x a); first exact: mem_orbit.
Qed.

Lemma amoveK :
  {in orbit to A x, cancel (amove to A x) (fun Ca => to x (repr Ca))}.
Proof. 
move=> y; case/orbitP=> a Aa <-{y}; rewrite amove_act //= -[A :&: _]/(gval _).
case: repr_rcosetP => b; rewrite !(inE, sub1set); case/and3P=> Ab _ xbx.
by rewrite actMin ?ssAD ?(eqP xbx). 
Qed.

Lemma orbit_stabilizer :
  orbit to A x = [set to x (repr Ca) | Ca <- rcosets 'C_A[x | to] A].
Proof.
rewrite -amove_orbit -imset_comp /=; apply/setP=> z.
by apply/idP/imsetP=> [xAz | [y xAy ->]]; first exists z; rewrite /= ?amoveK.
Qed.

Lemma act_reprK :
  {in rcosets 'C_A[x | to] A, cancel (to x \o repr) (amove to A x)}.
Proof.
move=> Ca; case/rcosetsP=> a Aa ->{Ca} /=; rewrite amove_act ?rcoset_repr //.
rewrite -[A :&: _]/(gval _); case: repr_rcosetP => b; case/setIP=> Ab _.
exact: groupM.
Qed.

End OrbitStabilizer.

End PartialAction.

Implicit Arguments orbit1P [aT D rT to A x].
Prenex Implicits orbit1P.

Notation "''C' ( S | to )" := (astab_group to S) : subgroup_scope.
Notation "''C_' A ( S | to )" := (A :&: 'C(S | to))%G : subgroup_scope.
Notation "''C' [ x | to ]" := ('C([set x] | to))%G : subgroup_scope.
Notation "''C_' A [ x | to ]" := (A :&: 'C[x | to])%G : subgroup_scope.
Notation "''N' ( S | to )" := (astabs_group to S) : subgroup_scope.
Notation "''N_' A ( S | to )" := (A :&: 'N(S | to))%G : subgroup_scope.

Section TotalActions.
(* These lemmas are only established for total actions (domain = [set: rT]) *)

Variable (aT : finGroupType) (rT : finType).

Variable to : {action aT &-> rT}.

Implicit Types a b : aT.
Implicit Types x y z : rT.
Implicit Types A B : {group aT}.
Implicit Types S : {set rT}.

Lemma actM : forall x a b, to x (a * b) = to (to x a) b.
Proof. by move=> x a b; rewrite actMin ?inE. Qed.

Lemma actK : right_loop invg to.
Proof. by move=> a; apply: actKin; rewrite inE. Qed.

Lemma actKV : rev_right_loop invg to.
Proof. by move=> a; apply: actKVin; rewrite inE. Qed.

Lemma actX : forall x a n, to x (a ^+ n) = iter n (to^~ a) x.
Proof. by move=> x a; elim=> [|n /= <-]; rewrite ?act1 // -actM expgSr. Qed.

Lemma actCJ : forall a b x, to (to x a) b = to (to x b) (a ^ b).
Proof. by move=> a b x; rewrite !actM actK. Qed.

Lemma actCJV : forall a b x, to (to x a) b = to (to x (b ^ a^-1)) a.
Proof. by move=> a b x; rewrite (actCJ _ a) conjgKV. Qed.

Lemma orbit_sym : forall A x y, (y \in orbit to A x) = (x \in orbit to A y).
Proof. move=> A; apply: sub_orbit_sym; exact: subsetT. Qed.

Lemma orbit_trans : forall A x y z,
  y \in orbit to A x -> z \in orbit to A y -> z \in orbit to A x.
Proof. move=> A x y z; apply: sub_orbit_trans; exact: subsetT. Qed.

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
move=> S a; apply: (iffP idP) => [cSa x|cSa]; first exact: astab_act.
by rewrite !inE; apply/subsetP=> x Sx; rewrite inE cSa.
Qed.

Lemma astab1P : forall x a, reflect (to x a = x) (a \in 'C[x | to]).
Proof. move=> x a; rewrite !inE sub1set inE; exact: eqP. Qed.

Lemma sub_astab1 : forall A x, (A \subset 'C[x | to]) = (x \in 'Fix_to(A)).
Proof.
move=> A x; apply/subsetP/afixP=> cAx a; move/cAx;
  by rewrite ?(sub1set, inE) /=; move/eqP.
Qed.

Lemma astabsP : forall S a,
  reflect (forall x, (to x a \in S) = (x \in S)) (a \in 'N(S | to)).
Proof.
move=> S a; apply: (iffP idP) => [nSa x|nSa]; first exact: astabs_act.
by rewrite !inE; apply/subsetP=> x; rewrite inE nSa.
Qed.

Lemma card_orbit : forall A x, #|orbit to A x| = #|A : 'C_A[x | to]|.
Proof.
move=> A x; have sAT := subsetT A.
by rewrite orbit_stabilizer // (card_in_imset (can_in_inj (act_reprK sAT))).
Qed.

Lemma dvdn_orbit : forall A x, #|orbit to A x| %| #|A|.
Proof. by move=> A x; rewrite card_orbit dvdn_indexg. Qed. 

Lemma card_orbit_stab : forall A x,
  (#|orbit to A x| * #|'C_A[x | to]|)%N = #|A|.
Proof. by move=> A x; rewrite mulnC card_orbit LaGrange ?subsetIl. Qed.

Lemma actsP : forall A S, reflect {acts A, on S | to} [acts A, on S | to].
Proof.
move=> A S; apply: (iffP idP) => [nSA x|nSA]; first exact: acts_act.
by apply/subsetP=> a Aa; rewrite !inE; apply/subsetP=> x; rewrite inE nSA.
Qed.
Implicit Arguments actsP [A S].

Lemma acts_sum_card_orbit : forall A S,
  [acts A, on S | to] -> \sum_(T \in orbit to A @: S) #|T| = #|S|.
Proof.
move=> A S AactS; rewrite -sum1_card (partition_big_imset (orbit to A)) /=.
apply: eq_bigr => xS; case/imsetP=> x Sx ->{xS}; rewrite -sum1_card.
apply: eq_bigl=> y; apply/idP/andP=> [xAy|[_]].
  by rewrite (orbit_transl xAy) (acts_in_orbit _ xAy).
by move/eqP <-; exact: orbit_refl.
Qed.

Lemma setact_orbit : forall A x b,
  to^* (orbit to A x) b = orbit to (A :^ b) (to x b).
Proof.
move=> A x b; apply/setP=> y; apply/idP/idP.
  case/imsetP=> xa; case/imsetP=> a Aa -> ->{xa y}.
  by rewrite actCJ mem_orbit ?memJ_conjg.
case/imsetP=> ab; case/imsetP=> a Aa -> ->{ab y}.
by rewrite -actCJ mem_setact ?mem_orbit.
Qed.

Lemma astab_setact : forall S a, 'C(to^* S a | to) = 'C(S | to) :^ a.
Proof.
move=> S a; apply/setP=> b; rewrite mem_conjg.
apply/astabP/astabP=> stab x => [Sx|].
  by rewrite conjgE invgK !actM stab ?actK //; apply/imsetP; exists x.
by case/imsetP=> y Sy ->{x}; rewrite -actM conjgCV actM stab.
Qed.

Lemma astab1_act : forall x a, 'C[to x a | to] = 'C[x | to] :^ a.
Proof. by move=> x a; rewrite -astab_setact /setact imset_set1. Qed.

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
  by rewrite /orbA (orbit_transl xAy) (acts_in_orbit AactS xAy).
rewrite -(card_orbit_stab A x) -sum_nat_const.
apply: eq_bigr => y; rewrite orbit_sym; case/imsetP=> a Aa defx.
rewrite defx astab1_act -{2}(conjGid Aa) -conjIg cardJg -sum1_card.
by apply: eq_bigl => b; rewrite !(sub1set, inE) -(actsP AactS a Aa) -defx Sx.
Qed.

Lemma atransP : forall A S, [transitive A, on S | to] ->
  forall x, x \in S -> orbit to A x = S.
Proof. move=> A S; case/imsetP=> x _ -> y; exact: orbit_transl. Qed.

Lemma atransP2 : forall A S, [transitive A, on S | to] ->
  {in S &, forall x y, exists2 a, a \in A & y = to x a}.
Proof. by move=> A S AtrS x y; move/(atransP AtrS) <-; move/imsetP. Qed.

Lemma atrans_acts : forall A S,
  [transitive A, on S | to] -> [acts A, on S | to].
Proof.
move=> A S AtrS; apply/subsetP=> a Aa; rewrite !inE.
by apply/subsetP=> x; move/(atransP AtrS) <-; rewrite inE mem_imset.
Qed.

Lemma atrans_supgroup : forall A B S,
   A \subset B -> [transitive A, on S | to] ->
    [transitive B, on S | to] = [acts B, on S | to].
Proof.
move=> A B S sAB trA; apply/idP/idP=> [|actB]; first exact: atrans_acts.
case/imsetP: trA => x Sx defS; apply/imsetP; exists x => //.
by apply/eqP; rewrite eqEsubset acts_sub_orbit ?Sx // defS imsetS.
Qed.

Lemma atrans_acts_card : forall A S,
  [transitive A, on S | to] =
     [acts A, on S | to] && (#|orbit to A @: S| == 1%N).
Proof.
move=> A S; apply/idP/andP=> [AtrS | [nSA]].
  split; first exact: atrans_acts.
  rewrite ((_ @: S =P [set S]) _) ?cards1 // eqEsubset sub1set.
  apply/andP; split=> //; apply/subsetP=> X; case/imsetP=> x Sx ->.
  by rewrite inE (atransP AtrS).
rewrite eqn_leq andbC lt0n; case/andP.
case/existsP=> X; case/imsetP=> x Sx X_Ax.
rewrite (cardD1 X) {X}X_Ax mem_imset // ltnS leqn0; move/eqP=> AtrS.
apply/imsetP; exists x => //; apply/eqP.
rewrite eqEsubset acts_sub_orbit // Sx andbT.
apply/subsetP=> y Sy; have:= card0_eq AtrS (orbit to A y).
rewrite !inE /= mem_imset // andbT; move/eqP <-; exact: orbit_refl.
Qed.

Lemma atrans_dvd : forall A S x,
  x \in S -> [transitive A, on S | to] -> #|S| %| #|A|.
Proof.
by move=> A S x Sx; move/atransP=> AtrS; rewrite -(AtrS x Sx) dvdn_orbit.
Qed.

(* Aschbacher 5.2 *)
Lemma acts_fix_norm : forall A B, 
  A \subset 'N(B) -> [acts A, on 'Fix_to(B) | to].
Proof.
move=> A B nAB; have:= acts_subnorm_fix to B; rewrite !setTI.
exact: subset_trans.
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
Theorem subgroup_transitiveP : forall A B S x,
     x \in S -> B \subset A -> [transitive A, on S | to] ->
  reflect ('C_A[x | to] * B = A) [transitive B, on S | to].
Proof.
move=> A B S x Sx sBA trA; apply: (iffP idP) => [trB | defA].
  rewrite group_modr //; apply/setIidPl; apply/subsetP=> a Aa.
  have Sxa: to x a \in S by rewrite (actsP (atrans_acts trA)).
  have [b Bb xab]:= atransP2 trB Sxa Sx.
  by rewrite -(mulgK b a) mem_mulg ?groupV //; apply/astab1P; rewrite actM.
apply/imsetP; exists x => //; apply/setP=> y; rewrite -(atransP trA Sx).
apply/imsetP/imsetP=> [] [a]; last by exists a; first exact: (subsetP sBA).
rewrite -defA; case/imset2P=> c b; case/setIP=> _; move/astab1P=> xc Bb -> ->.
by exists b; rewrite // actM xc.
Qed.

(* Aschbacher 5.21 *)
Lemma trans_subnorm_fixP : forall x A B S,
  let C := 'C_A[x | to] in let T := 'Fix_(S | to)(B) in
    [transitive A, on S | to] -> x \in S -> B \subset C ->
  reflect ((B :^: A) ::&: C = B :^: C) [transitive 'N_A(B), on T | to].
Proof.
move=> x A B S C T trAS Sx sBC; have actAS := acts_act (atrans_acts trAS).
have:= sBC; rewrite subsetI sub_astab1; case/andP=> sBA cBx.
have Tx: x \in T by rewrite inE Sx.
apply: (iffP idP) => [trN | trC].
  apply/setP=> Ba; apply/setIdP/imsetP=> [[]|[a Ca ->{Ba}]]; last first.
    by rewrite conj_subG //; case/setIP: Ca => Aa _; rewrite mem_imset.
  case/imsetP=> a Aa ->{Ba}; rewrite subsetI !sub_conjg; case/andP=> _ sBCa.
  have Txa: to x a^-1 \in T.
    by rewrite inE -sub_astab1 astab1_act actAS ?Sx ?groupV.
  have [b] := atransP2 trN Tx Txa; case/setIP=> Ab nBb cxba.
  exists (b * a); last by rewrite conjsgM (normP nBb).
  by rewrite inE groupM //; apply/astab1P; rewrite actM -cxba actKV.
apply/imsetP; exists x => //; apply/setP=> y; apply/idP/idP=> [Ty|].
  have [Sy cBy]:= setIP Ty; have [a Aa defy] := atransP2 trAS Sx Sy.
  have: B :^ a^-1 \in B :^: C.
    rewrite -trC inE subsetI mem_imset 1?conj_subG ?groupV // sub_conjgV.
    by rewrite -astab1_act -defy sub_astab1.
  case/imsetP=> b; case/setIP=> Ab; move/astab1P=> cxb defBb.
  rewrite defy -{1}cxb -actM mem_orbit // inE groupM //.
  by apply/normP; rewrite conjsgM -defBb conjsgKV.
case/imsetP=> a; case/setIP=> Aa nBa ->{y}.
by rewrite inE actAS // Sx (acts_act (acts_fix_norm _) nBa).
Qed.

End TotalActions.

Implicit Arguments astabP [aT rT to S a].
Implicit Arguments astab1P [aT rT to x a].
Implicit Arguments astabsP [aT rT to S a].
Implicit Arguments atransP [aT rT to A S].
Implicit Arguments actsP [aT rT to A S].
Implicit Arguments faithfulP [aT rT to A S].
Prenex Implicits astabP astab1P astabsP atransP actsP faithfulP.

Section Restrict.

Variables (aT : finGroupType) (D : {set aT}) (rT : Type).
Variables (to : action D rT) (A : {set aT}).

Definition ract of A \subset D := act to.

Variable sAD : A \subset D.

Lemma ract_is_action : is_action A (ract sAD).
Proof.
rewrite /ract; case: to => f [injf fM].
split=> // x; exact: (sub_in2 (subsetP sAD)).
Qed.

Canonical Structure raction := Action ract_is_action.

Lemma ractE : raction =1 to. Proof. by []. Qed.

(* Other properties of raction need rT : finType; we defer them *)
(* until after the definition of actperm.                       *)

End Restrict.

Notation "to \ sAD" := (raction to sAD) (at level 50) : action_scope.

Section ActBy.

Variables (aT : finGroupType) (D : {set aT}) (rT : finType).

Definition actby_cond (A : {set aT}) R (to : action D rT) : Prop :=
  [acts A, on R | to].

Definition actby A R to of actby_cond A R to :=
  fun x a => if (x \in R) && (a \in A) then to x a else x.

Variables (A : {group aT}) (R : {set rT}) (to : action D rT).
Hypothesis nRA : actby_cond A R to.

Lemma actby_is_action : is_action A (actby nRA).
Proof.
rewrite /actby; split=> [a x y | x a b Aa Ab /=]; last first.
  rewrite Aa Ab groupM // !andbT actMin ?(subsetP (acts_dom nRA)) //.
  by case Rx: (x \in R); rewrite ?(acts_act nRA) ?Rx.
case Aa: (a \in A); rewrite ?andbF ?andbT //.
case Rx: (x \in R); case Ry: (y \in R) => // eqxy; first exact: act_inj eqxy.
  by rewrite -eqxy (acts_act nRA Aa) Rx in Ry.
by rewrite eqxy (acts_act nRA Aa) Ry in Rx.
Qed.

Canonical Structure action_by := Action actby_is_action.
Local Notation "<[nRA]>" := action_by : action_scope.

Lemma actbyE : forall x a, x \in R -> a \in A -> <[nRA]>%act x a = to x a.
Proof. by rewrite /= /actby => x a -> ->. Qed.

Lemma afix_actby : forall B, 'Fix_<[nRA]>(B) = ~: R :|: 'Fix_to(A :&: B).
Proof.
move=> B; apply/setP=> x; rewrite !inE /= /actby.
case: (x \in R); last by apply/subsetP=> a _; rewrite !inE.
apply/subsetP/subsetP=> [cBx a | cABx a Ba]; rewrite !inE.
  by case/andP=> Aa; move/cBx; rewrite inE Aa.
by case: ifP => //= Aa; have:= cABx a; rewrite !inE Aa => ->.
Qed.
 
Lemma astab_actby : forall S, 'C(S | <[nRA]>) = 'C_A(R :&: S | to).
Proof.
move=> S; apply/setP=> a; rewrite setIA (setIidPl (acts_dom nRA)) !inE.
case Aa: (a \in A) => //=; apply/subsetP/subsetP=> cRSa x => [|Sx].
  by case/setIP=> Rx; move/cRSa; rewrite !inE actbyE.
by have:= cRSa x; rewrite !inE /= /actby Aa Sx; case: (x \in R) => //; apply.
Qed.

Lemma astabs_actby : forall S, 'N(S | <[nRA]>) = 'N_A(R :&: S | to).
Proof.
move=> S; apply/setP=> a; rewrite setIA (setIidPl (acts_dom nRA)) !inE.
case Aa: (a \in A) => //=; apply/subsetP/subsetP=> nRSa x => [|Sx].
  by case/setIP=> Rx; move/nRSa; rewrite !inE actbyE ?(acts_act nRA) ?Rx.
have:= nRSa x; rewrite !inE /= /actby Aa Sx ?(acts_act nRA) //.
by case: (x \in R) => //; apply.
Qed.

Lemma acts_actby : forall (B : {set aT}) S,
  [acts B, on S | <[nRA]>] = (B \subset A) && [acts B, on R :&: S | to].
Proof. by move=> B S; rewrite astabs_actby subsetI. Qed.

End ActBy.

Notation "<[ nRA ] >" := (action_by nRA) : action_scope.

Section SubAction.

Variables (aT : finGroupType) (D : {group aT}).
Variables (rT : finType) (sP : pred rT) (sT : subType sP) (to : action D rT).
Implicit Type u : sT.

Definition subact_dom := 'N([set x | sP x] | to).
Canonical Structure subact_dom_group := [group of subact_dom].

Implicit Type Na : {a | a \in subact_dom}.
Lemma sub_act_proof : forall u Na, sP (to (val u) (val Na)).
Proof. by move=> u [a] /=; move/(astabs_act (val u)); rewrite !inE valP. Qed.

Definition subact u a :=
  if insub a is Some Na then Sub _ (sub_act_proof u Na) else u.

Lemma val_subact : forall u a,
  val (subact u a) = if a \in subact_dom then to (val u) a else val u.
Proof.
move=> u a; rewrite /subact -if_neg.
by case: insubP => [Na|] -> //=; rewrite SubK => ->.
Qed.

Lemma subact_is_action : is_action subact_dom subact.
Proof.
split=> [a u v eq_uv | u a b Na Nb]; apply: val_inj.
  move/(congr1 val): eq_uv; rewrite !val_subact.
  by case: (a \in _); first move/act_inj.
have Da := astabs_dom Na; have Db := astabs_dom Nb. 
by rewrite !val_subact Na Nb groupM ?actMin.
Qed.

Canonical Structure subaction := Action subact_is_action.

End SubAction.

Notation "to ^?" := (subaction _ to)
  (at level 2, format "to ^?") : action_scope.

Section QuotientAction.

Variables (aT : finGroupType) (D : {group aT}) (rT : finGroupType).
Variables (to : action D rT) (H : {group rT}).

Definition qact_dom := 'N(rcosets H 'N(H) | to^*).
Canonical Structure qact_dom_group := [group of qact_dom].

Local Notation subdom := (subact_dom (coset_range H)  to^*).
Fact qact_subdomE : subdom = qact_dom.
Proof. by congr 'N(_|_); apply/setP=> Hx; rewrite !inE genGid. Qed.
Lemma qact_proof : qact_dom \subset subdom.
Proof. by rewrite qact_subdomE. Qed.

Definition qact : coset_of H -> aT -> coset_of H := act (to^*^? \ qact_proof).

Canonical Structure quotient_action := [action of qact].

Lemma acts_qact_dom : [acts qact_dom, on 'N(H) | to].
Proof.
apply/subsetP=> a nNa; rewrite !inE (astabs_dom nNa); apply/subsetP=> x Nx.
have: H :* x \in rcosets H 'N(H) by rewrite -rcosetE mem_imset.
rewrite inE -(astabs_act _ nNa); case/rcosetsP=> y Ny defHy.
have: to x a \in H :* y by rewrite -defHy (mem_imset (to^~a)) ?rcoset_refl.
by apply: subsetP; rewrite mul_subG ?sub1set ?normG.
Qed.

Lemma qactEcond : forall x a,
    x \in 'N(H) ->
  quotient_action (coset H x) a =
     (if a \in qact_dom then coset H (to x a) else coset H x).
Proof.
move=> x a Nx; apply: val_inj; rewrite val_subact //= qact_subdomE.
have: H :* x \in rcosets H 'N(H) by rewrite -rcosetE mem_imset.
case nNa: (a \in _); rewrite // -(astabs_act _ nNa).
rewrite !val_coset ?(acts_act acts_qact_dom nNa) //=.
case/rcosetsP=> y Ny defHy; rewrite defHy; apply: rcoset_transl.
by rewrite rcoset_sym -defHy (mem_imset (_^~_)) ?rcoset_refl.
Qed.

Lemma qactE : forall x a,
    x \in 'N(H) -> a \in qact_dom ->
  quotient_action (coset H x) a = coset H (to x a).
Proof. by move=> x a Nx nNa; rewrite qactEcond ?nNa. Qed.

End QuotientAction.

Notation "to / H" := (quotient_action to H) : action_scope.

Section ModAction.

Variables (aT : finGroupType) (D A : {group aT}) (rT : finType).
Variable to : action D rT.

Local Notation dom := 'N_D(A).
Local Notation range := 'Fix_to(D :&: A).
Let acts_dom : {acts dom, on range | to} := acts_act (acts_subnorm_fix to A).

Definition modact x (Aa : coset_of A) :=
  if x \in range then to x (repr (D :&: Aa)) else x.

Lemma modactEcond : forall x a,
  a \in dom -> modact x (coset A a) = (if x \in range then to x a else x).
Proof.
move=> x a; case/setIP=> Da Na; case: ifP => Cx; rewrite /modact Cx //.
rewrite val_coset // -group_modr ?sub1set //.
case: (repr _) / (repr_rcosetP (D :&: A) a) => a' Aa'.
by rewrite actMin ?(afixP Cx _ Aa') //; case/setIP: Aa'.
Qed.

Lemma modactE : forall x a,
  a \in D -> a \in 'N(A) -> x \in range ->  modact x (coset A a) = to x a.
Proof. by move=> x a Da Na Rx; rewrite modactEcond ?Rx // inE Da. Qed.

Lemma modact_is_action : is_action (D / A) modact.
Proof.
split=> [Aa x y | x Aa Ab]; last first.
  case/morphimP=> a Na Da ->{Aa}; case/morphimP=> b Nb Db ->{Ab}.
  rewrite -morphM //= !modactEcond // ?groupM ?(introT setIP _) //.
  by case: ifP => Cx; rewrite ?(acts_dom, Cx, actMin, introT setIP _). 
case: (set_0Vmem (D :&: Aa)) => [Da0 | [a]].
  by rewrite /modact Da0 repr_set0 !act1 !if_same.
case/setIP=> Da NAa; have Na := subsetP (coset_norm _) _ NAa.
have NDa: a \in 'N_D(A) by rewrite inE Da.
rewrite -(coset_mem NAa) !modactEcond //.
do 2![case: ifP]=> Cy Cx // eqxy; first exact: act_inj eqxy.
  by rewrite -eqxy acts_dom ?Cx in Cy.
by rewrite eqxy acts_dom ?Cy in Cx.
Qed.

Canonical Structure mod_action := Action modact_is_action.

End ModAction.

Notation "to %% H" := (mod_action H to) : action_scope.

Section ActPerm.
(* Morphism to permutations induced by an action. *)

Variables (aT : finGroupType) (D : {set aT}) (rT : finType).
Variable to : action D rT.

Definition actperm a := perm (act_inj to a).

Lemma actpermM : {in D &, {morph actperm : a b / a * b}}.
Proof. by move=> a b Da Db; apply/permP=> x; rewrite permM !permE actMin. Qed.

Canonical Structure actperm_morphism := Morphism actpermM.

Lemma actpermE : forall a x, actperm a x = to x a.
Proof. by move=> a x; rewrite permE. Qed.

Lemma actpermK : forall x a, aperm x (actperm a) = to x a.
Proof. move=> x a; exact: actpermE. Qed.

Lemma ker_actperm : 'ker actperm = 'C(setT | to).
Proof.
congr (_ :&: _); apply/setP=> a; rewrite !inE /=.
apply/eqP/subsetP=> [a1 x _ | a1]; first by rewrite inE -actpermE a1 perm1.
by apply/permP=> x; apply/eqP; have:= a1 x; rewrite !inE actpermE perm1 => ->.
Qed.

End ActPerm.

Section RestrictActionTheory.

Variables (aT : finGroupType) (D : {set aT}) (rT : finType).
Variables (to : action D rT).

Lemma faithful_isom : forall (A : {group aT}) S (nSA : actby_cond A S to),
   [faithful A, on S | to] -> isom A (actperm <[nSA]> @* A) (actperm <[nSA]>).
Proof.
by move=> A S nSA ffulAS; apply/isomP; rewrite ker_actperm astab_actby setIT.
Qed.

Variables (A : {set aT}) (sAD : A \subset D).

Lemma ractpermE : actperm (to \ sAD) =1 actperm to.
Proof. by move=> a; apply/permP=> x; rewrite !permE. Qed.

Lemma afix_ract : forall B, 'Fix_(to \ sAD)(B) = 'Fix_to(B). Proof. by []. Qed.

Lemma astab_ract : forall S, 'C(S | to \ sAD) = 'C_A(S | to).
Proof. by move=> S; rewrite setIA (setIidPl sAD). Qed.

Lemma astabs_ract : forall S, 'N(S | to \ sAD) = 'N_A(S | to).
Proof. by move=> S; rewrite setIA (setIidPl sAD). Qed.

Lemma acts_ract : forall (B : {set aT}) S,
  [acts B, on S | to \ sAD] = (B \subset A) && [acts B, on S | to].
Proof. by move=> B S; rewrite astabs_ract subsetI. Qed.

End RestrictActionTheory.

Section MorphAct.
(* Action induced by a morphism to permutations. *)

Variables (aT : finGroupType) (D : {group aT}) (rT : finType).
Variable phi : {morphism D >-> {perm rT}}.

Definition mact x a := phi a x.

Lemma mact_is_action : is_action D mact.
Proof.
split=> [a x y | x a b Da Db]; first exact: perm_inj.
by rewrite /mact morphM //= permM.
Qed.

Canonical Structure morph_action := Action mact_is_action.

Lemma mactE : forall x a, morph_action x a = phi a x. Proof. by []. Qed.

Lemma injm_faithful : 'injm phi -> [faithful D, on setT | morph_action].
Proof.
move/injmP=> phi_inj; apply/subsetP=> a; case/setIP=> Da.
move/astab_act=> a1; apply/set1P; apply: phi_inj => //.
by apply/permP=> x; rewrite morph1 perm1 -mactE a1 ?inE.
Qed.

Lemma perm_mact : forall a, actperm morph_action a = phi a.
Proof. by move=> a; apply/permP=> x; rewrite permE. Qed.

End MorphAct.

Notation "<< phi >>" := (morph_action phi) : action_scope.

Section PermAction.
  (*  Natural action of permutation groups.                        *)

Variable rT : finType.
Local Notation gT := {perm rT}.
Implicit Types a b c : gT.

Lemma aperm_is_action : is_action setT (@aperm rT).
Proof.
by apply: is_total_action => [x|x a b]; rewrite apermE (perm1, permM).
Qed.

Canonical Structure perm_action := Action aperm_is_action.

Lemma pcycleE : forall a, pcycle a = orbit perm_action <[a]>%g.
Proof. by []. Qed.

Lemma perm_act1P : forall a, reflect (forall x, aperm x a = x) (a == 1).
Proof.
move=> a; apply: (iffP eqP) => [-> x | a1]; first exact: act1.
by apply/permP=> x; rewrite -apermE a1 perm1.
Qed.

Lemma perm_faithful : forall A, [faithful A, on setT | perm_action].
Proof.
move=> A; apply/subsetP=> a; case/setIP => Da crTa.
by apply/set1P; apply/permP=> x; rewrite -apermE perm1 (astabP crTa) ?inE.
Qed.

Lemma actperm_id : forall p, actperm perm_action p = p.
Proof. by move=> p; apply/permP=> x; rewrite permE. Qed.

End PermAction.

Implicit Arguments perm_act1P [rT a].
Prenex Implicits perm_act1P.

Notation "'P" := (perm_action _) (at level 0) : action_scope.

Section GroupAction.

Variables (aT rT : finGroupType) (D : {set aT}) (R : {set rT}).
Local Notation actT := (action D rT).

Definition is_groupAction (to : actT) :=
  {in D, forall a, actperm to a \in Aut R}.

Structure groupAction := GroupAction {gact :> actT; _ : is_groupAction gact}.

Definition repack_groupAction to :=
  let: GroupAction _ toA := to return {type of GroupAction for to} -> _ in
  fun k => k toA : groupAction.

End GroupAction.

Delimit Scope groupAction_scope with gact.
Bind Scope groupAction_scope with groupAction.
Arguments Scope gact [_ _ group_scope group_scope groupAction_scope].

Notation "[ 'groupAction' 'of' to ]" :=
    (repack_groupAction (fun toA => @GroupAction _ _ _ to))
  (at level 0, format "[ 'groupAction'  'of'  to ]") : form_scope.

Section GroupActionDefs.

Variables (aT rT : finGroupType) (D : {set aT}) (R : {set rT}).
Implicit Type A : {set aT}.
Implicit Type S : {set rT}.
Implicit Type to : groupAction D R.

Definition gact_range of groupAction D R := R.

Definition gacent to A := 'Fix_(R | to)(D :&: A).

Definition acts_on_group A S to := [acts A, on S | to] /\ S \subset R.

Coercion actby_cond_group A S to : acts_on_group A S to -> actby_cond A S to :=
  @proj1 _ _.

End GroupActionDefs.

(* Camlp4 factoring for group action centraliser. *)
Notation "''C_' ( G ) ( A )" := 'C_G(A)
  (at level 8, only parsing) : group_scope.
Notation "''C_' ( G ) ( A )" := 'C_G(A)%G
  (only parsing) : subgroup_scope.
Notation "''C_' ( G ) ( A | to )" := 'C_G(A | to)
  (at level 8, only parsing) : group_scope.
Notation "''C_' ( G ) ( A | to )" := 'C_G(A | to)%G
  (only parsing) : subgroup_scope.
Notation "''C_' ( G ) [ a ]" := 'C_G[a]
  (at level 8, only parsing) : group_scope.
Notation "''C_' ( G ) [ a ]" := 'C_G[a]%G (only parsing) : subgroup_scope.
Notation "''C_' ( G ) [ a | to ]" := 'C_G[a | to]
  (at level 8, only parsing) : group_scope.
Notation "''C_' ( G ) [ a | to ]" := 'C_G[a | to]%G
  (only parsing) : subgroup_scope.

Notation "''C_' ( | to ) ( A )" := (gacent to A)
  (at level 8, format "''C_' ( | to ) ( A )") : group_scope.
Notation "''C_' ( G | to ) ( A )" := (G :&: 'C_(|to)(A))
  (at level 8, format "''C_' ( G  |  to ) ( A )") : group_scope.
Notation "''C_' ( | to ) [ a ]" := 'C_(|to)([set a])
  (at level 8, format "''C_' ( | to ) [ a ]") : group_scope.
Notation "''C_' ( G | to ) [ a ]" := 'C_(G | to)([set a])
  (at level 8, format "''C_' ( G  |  to ) [ a ]") : group_scope.

Notation "{ 'acts' A , 'on' 'group' G | to }" := (acts_on_group A G to)
  (at level 0, format "{ 'acts'  A ,  'on'  'group'  G  |  to }") : form_scope.

Section RawGroupAction.

Variables (aT rT : finGroupType) (D : {set aT}) (R : {set rT}).
Variable to : groupAction D R.

Lemma actperm_Aut : is_groupAction R to. Proof. by case: to. Qed.

Lemma im_actperm_Aut : actperm to @* D \subset Aut R.
Proof. apply/subsetP=> pa; case/morphimP=> a _ Da ->; exact: actperm_Aut. Qed.

Lemma gact_out : forall x a, a \in D -> x \notin R -> to x a = x.
Proof. by move=> x a Da Rx; rewrite -actpermE (out_Aut _ Rx) ?actperm_Aut. Qed.

Lemma gactM : {in D, forall a, {in R &, {morph to^~ a : x y / x * y}}}.
Proof.
move=> a Da /= x y; rewrite -!(actpermE to); apply: morphicP x y.
by rewrite Aut_morphic ?actperm_Aut.
Qed.

Lemma actmM : forall a, {in R &, {morph actm to a : x y / x * y}}.
Proof. rewrite /actm => a; case: ifP => //; exact: gactM. Qed.

Canonical Structure act_morphism a := Morphism (actmM a).

Lemma morphim_actm :
  {in D, forall a (S : {set rT}), S \subset R -> actm to a @* S = to^* S a}.
Proof. by move=> a Da /= S ?; rewrite /morphim /= actmEfun ?(setIidPr _). Qed.

Variables (a : aT) (A : {set aT}) (G : {set rT}).

Lemma gacentIdom : 'C_(|to)(D :&: A) = 'C_(|to)(A).
Proof. by rewrite /gacent setIA setIid. Qed.

Lemma gacentIim : 'C_(R | to)(A) = 'C_(|to)(A).
Proof. by rewrite setIA setIid. Qed.

Hypotheses (Da : a \in D) (sAD : A \subset D) (sGR : G \subset R).

Lemma gacentE : 'C_(|to)(A) = 'Fix_(R | to)(A).
Proof. by rewrite -{2}(setIidPr sAD). Qed.

Lemma gacent1E : 'C_(|to)[a] = 'Fix_(R | to)[a].
Proof. by rewrite /gacent [D :&: _](setIidPr _) ?sub1set. Qed.

Lemma subgacentE : 'C_(G | to)(A) = 'Fix_(G | to)(A).
Proof. by rewrite gacentE setIA (setIidPl sGR). Qed.

Lemma subgacent1E : 'C_(G | to)[a] = 'Fix_(G | to)[a].
Proof. by rewrite gacent1E setIA (setIidPl sGR). Qed.

End RawGroupAction.

Section GroupActionTheory.

Variables aT rT : finGroupType.
Variables (D : {group aT}) (R : {group rT}) (to : groupAction D R).

Lemma gact1 : {in D, forall a, to 1 a = 1}.
Proof. by move=> a Da; rewrite /= -actmE ?morph1. Qed.

Lemma gactV : {in D, forall a, {in R, {morph to^~ a : x / x^-1}}}.
Proof. by move=> a Da /= x Rx; move; rewrite -!actmE ?morphV. Qed.

Lemma gactX : {in D, forall a n, {in R, {morph to^~ a : x / x ^+ n}}}.
Proof. by move=> a Da /= n x Rx; rewrite -!actmE // morphX. Qed.

Lemma gactJ : {in D, forall a, {in R &, {morph to^~ a : x y / x ^ y}}}.
Proof. by move=> a Da /= x Rx y Ry; rewrite -!actmE // morphJ. Qed.

Lemma gactR : {in D, forall a, {in R &, {morph to^~ a : x y / [~ x, y]}}}.
Proof. by move=> a Da /= x Rx y Ry; rewrite -!actmE // morphR. Qed.

Lemma gact_stable : {acts D, on R | to}.
Proof.
apply: acts_act; apply/subsetP=> a Da; rewrite !inE Da.
apply/subsetP=> x; rewrite inE; apply: contraLR => R'xa.
by rewrite -(actKin to Da x) gact_out ?groupV.
Qed.

Lemma group_set_gacent : forall A, group_set 'C_(|to)(A).
Proof.
move=> A; apply/group_setP; split=> [|x y].
  rewrite !inE group1; apply/subsetP=> a; case/setIP=> Da _.
  by rewrite inE gact1.
case/setIP=> Rx; move/afixP=> cAx; case/setIP=> Ry; move/afixP=> cAy.
rewrite inE groupM //; apply/afixP=> a Aa.
by rewrite gactM ?cAx ?cAy //; case/setIP: Aa.
Qed.

Canonical Structure gacent_group A := Group (group_set_gacent A).

Lemma injm_actm : forall a, 'injm (actm to a).
Proof.
move=> a; apply/injmP=> x y Rx Ry; rewrite /= /actm; case: ifP => Da //.
exact: act_inj.
Qed. 

Lemma im_actm : forall a, actm to a @* R = R.
Proof.
move=> a; apply/eqP; rewrite eqEcard (card_injm (injm_actm a)) // leqnn andbT.
apply/subsetP=> xa; case/morphimP=> x Rx _ ->{xa} /=.
by rewrite /actm; case: ifP => // Da; rewrite gact_stable.
Qed.

Section Restrict.

Variables (A : {group aT}) (sAD : A \subset D).

Lemma ract_is_groupAction : is_groupAction R (to \ sAD).
Proof. by move=> a Aa /=; rewrite ractpermE actperm_Aut ?(subsetP sAD). Qed.

Canonical Structure ract_groupAction := GroupAction ract_is_groupAction.

Lemma gacent_ract : forall B, 'C_(|ract_groupAction)(B) = 'C_(|to)(A :&: B).
Proof. by move=> B; rewrite /gacent afix_ract setIA (setIidPr sAD). Qed.

End Restrict.

Section ActBy.

Variables (A : {group aT}) (G : {group rT}) (nGAg : {acts A, on group G | to}).

Lemma actby_is_groupAction : is_groupAction G <[nGAg]>.
Proof.
move=> a Aa; rewrite /= inE; apply/andP; split.
  apply/subsetP=> x; apply: contraR => Gx.
  by rewrite actpermE /= /actby (negbTE Gx).
apply/morphicP=> x y Gx Gy; rewrite !actpermE /= /actby Aa groupM ?Gx ?Gy //=.
by case nGAg; move/acts_dom; do 2!move/subsetP=> ?; rewrite gactM; auto.
Qed.
  
Canonical Structure actby_groupAction := GroupAction actby_is_groupAction.

Lemma gacent_actby : forall B,
  'C_(|actby_groupAction)(B) = 'C_(G | to)(A :&: B).
Proof.
move=> B; rewrite /gacent afix_actby !setIA setIid setIUr setICr set0U.
by have [nAG sGR] := nGAg; rewrite (setIidPr (acts_dom nAG)) (setIidPl sGR).
Qed.

End ActBy.

Section Quotient.

Variable H : {group rT}.

Lemma acts_qact_dom_norm : {acts qact_dom to H, on 'N(H) | to}.
Proof.
move=> a HDa /= x; rewrite {2}(('N(H) =P to^~ a @^-1: 'N(H)) _) ?inE {x}//.
rewrite eqEcard (card_preimset _ (act_inj _ _)) leqnn andbT.
apply/subsetP=> x Nx; rewrite inE; move/(astabs_act (H :* x)): HDa.
rewrite mem_rcosets mulSGid ?normG // Nx; case/rcosetsP=> y Ny defHy.
have: H :* y \subset 'N(H) by rewrite mul_subG ?sub1set ?normG.
move/subsetP; apply; rewrite -defHy; apply: mem_imset; exact: rcoset_refl.
Qed.

Lemma qact_is_groupAction : is_groupAction (R / H) (to / H).
Proof.
move=> a HDa /=; have Da := astabs_dom HDa.
rewrite inE; apply/andP; split.
  apply/subsetP=> Hx /=; case: (cosetP Hx) => x Nx ->{Hx}.
  apply: contraR => R'Hx; rewrite actpermE qactE // gact_out //.
  by apply: contra R'Hx; apply: mem_morphim.
apply/morphicP=> Hx Hy; rewrite !actpermE.
case/morphimP=> x Nx Gx ->{Hx}; case/morphimP=> y Ny Gy ->{Hy}.
by rewrite -morphM ?qactE ?groupM ?gactM // morphM ?acts_qact_dom_norm.
Qed.

Canonical Structure quotient_groupAction := GroupAction qact_is_groupAction.

Lemma qact_domE : H \subset R -> qact_dom to H = 'N(H | to).
Proof.
move=> sHR; apply/setP=> a; apply/idP/idP=> nHa; have Da := astabs_dom nHa.
  rewrite !inE Da; apply/subsetP=> x Hx; rewrite inE.
  have: to^~ a @: H \in rcosets H 'N(H).
    by rewrite (astabs_act _ nHa) -{1}(mulg1 H) -rcosetE mem_imset ?group1.
  case/rcosetsP=> y Ny defHy; rewrite -(rcoset1 H).
  by rewrite (@rcoset_transl _ H 1 y) -defHy -1?(gact1 Da) mem_setact.
rewrite !inE Da; apply/subsetP=> Hx; rewrite inE; case/rcosetsP=> x Nx ->{Hx}.
apply/imsetP; exists (to x a).
  case Rx: (x \in R); last by rewrite gact_out ?Rx.
  rewrite inE; apply/subsetP=> ya; case/imsetP=> y Hy ->{ya}.
  rewrite -(actKVin to Da y) -gactJ // ?(subsetP sHR, astabs_act, groupV) //.
  by rewrite memJ_norm // astabs_act ?groupV.
apply/eqP; rewrite rcosetE eqEcard.
rewrite (card_imset _ (act_inj _ _)) !card_rcoset leqnn andbT.
apply/subsetP=> ya; case/imsetP=> y; rewrite !mem_rcoset=> Hxy ->{ya}.
have Rxy := subsetP sHR _ Hxy; rewrite -(mulgKV x y).
case Rx: (x \in R); last by rewrite !gact_out ?mulgK // 1?groupMl ?Rx.
by rewrite -gactV // -gactM 1?groupMr ?groupV // mulgK astabs_act.
Qed.

End Quotient.

Section Mod.

Variable A : {group aT}.

Lemma modact_is_groupAction : is_groupAction 'C_(|to)(A) (to %% A).
Proof.
move=> Aa; case/morphimP=> a Na Da ->.
have NDa: a \in 'N_D(A) by exact/setIP.
rewrite inE; apply/andP; split.
  apply/subsetP=> x; apply: contraR.
  rewrite inE andbC actpermE /= modactEcond //.
  by case: ifP => // -> Rx; rewrite gact_out.
apply/morphicP=> x y; case/setIP=> Rx cAx; case/setIP=> Ry cAy.
rewrite /= !actpermE /= !modactE ?gactM //.
suff: x * y \in 'C_(|to)(A) by case/setIP.
rewrite groupM //; exact/setIP.
Qed.

Canonical Structure mod_groupAction := GroupAction modact_is_groupAction.

Hypothesis cRA : A \subset 'C(R | to).

Lemma modgactE : forall x a,
  a \in 'N_D(A) -> (to %% A)%act x (coset A a) = to x a.
Proof.
move=> x a NDa; have [Da Na] := setIP NDa.
case Rx: (x \in R).
  rewrite /= modactE //.
  by apply/afixP=> b; case/setIP=> _; move/(subsetP cRA); move/astab_act->.
rewrite gact_out ?inE ?Rx //= /modact; case: ifP => // _.
rewrite gact_out ?Rx //.
have sAaD: coset A a \subset D.
  rewrite val_coset // mul_subG ?sub1set //.
  by apply: subset_trans cRA _; apply/subsetP=> b; case/setIdP.
by rewrite (setIidPr _) // (subsetP sAaD) // mem_repr_coset.
Qed.

End Mod.

Lemma modact_coset_astab : forall x a,
  a \in D -> (to %% 'C(R | to))%act x (coset _ a) = to x a.
Proof.
move=> x a Da; apply: modgactE => {x}//.
rewrite !inE Da; apply/subsetP=> ca; case/imsetP=> c Cc ->{ca}.
have Dc := astab_dom Cc; rewrite !inE groupJ //.
apply/subsetP=> x Rx; rewrite inE conjgE !actMin ?groupM ?groupV //.
by rewrite (astab_act Cc) ?actKVin // gact_stable ?groupV.
Qed.

End GroupActionTheory.

Notation "''C_' ( | to ) ( A )" := (gacent_group to A) : subgroup_scope.
Notation "''C_' ( G | to ) ( A )" := (G :&: 'C_(|to)(A))%G : subgroup_scope.
Notation "''C_' ( | to ) [ a ]" := 'C_(|to)([set a%g])%G : subgroup_scope.
Notation "''C_' ( G | to ) [ a ]" := 'C_(G | to)([set a%g])%G : subgroup_scope.

Notation "to \ sAD" := (ract_groupAction to sAD) : groupAction_scope.
Notation "<[ nGA ] >" := (actby_groupAction nGA) : groupAction_scope.
Notation "to / H" := (quotient_groupAction to H) : groupAction_scope.
Notation "to %% H" := (mod_groupAction to H) : groupAction_scope.

(* Conjugation and right translation actions. *)

Section InternalActionDefs.

Variable gT : finGroupType.
Implicit Type A : {set gT}.
Implicit Type G : {group gT}.

(* This is not a Canonical Structure because it is seldom used, and it would *)
(* cause too many spurious matches (any group product would be viewed as an  *)
(* action!).                                                                 *)
Definition mulgr_action := TotalAction (@mulg1 gT) (@mulgA gT).

Canonical Structure conjg_action := TotalAction (@conjg1 gT) (@conjgM gT).

Lemma conjg_is_groupAction : is_groupAction setT conjg_action.
Proof.
move=> a _; rewrite /= inE; apply/andP; split.
  by apply/subsetP=> x _; rewrite inE.
by apply/morphicP=> x y _ _; rewrite !actpermE /= conjMg.
Qed.

Canonical Structure conjg_groupAction := GroupAction conjg_is_groupAction.

Lemma rcoset_is_action : is_action setT (@rcoset gT).
Proof.
by apply: is_total_action => [A|A x y]; rewrite !rcosetE (mulg1, rcosetM).
Qed.

Canonical Structure rcoset_action := Action rcoset_is_action.

Canonical Structure conjsg_action := TotalAction (@conjsg1 gT) (@conjsgM gT).

Lemma conjG_is_action : is_action setT (@conjG_group gT).
Proof.
apply: is_total_action => [G | G x y]; apply: val_inj; rewrite /= ?act1 //.
exact: actM.
Qed.

Definition conjG_action := Action conjG_is_action.

End InternalActionDefs.

Notation "'R" := (@mulgr_action _) (at level 0) : action_scope.
Notation "'Rs" := (@rcoset_action _) (at level 0) : action_scope.
Notation "'J" := (@conjg_action _) (at level 0) : action_scope.
Notation "'J" := (@conjg_groupAction _) (at level 0) : groupAction_scope.
Notation "'Js" := (@conjsg_action _) (at level 0) : action_scope.
Notation "'JG" := (@conjG_action _) (at level 0) : action_scope.
Notation "'Q" := ('J / _)%act (at level 0) : action_scope.
Notation "'Q" := ('J / _)%gact (at level 0) : groupAction_scope.

Section InternalGroupAction.

Variable gT : finGroupType.
Implicit Types A B : {set gT}.
Implicit Types H G : {group gT}.

(*  Various identities for actions on groups. *)

Lemma orbitR : forall G x, orbit 'R G x = x *: G.
Proof. by move=> G x; rewrite -lcosetE. Qed.

Lemma astab1R : forall x : gT, 'C[x | 'R] = 1.
Proof.
move=> x; apply/trivgP; apply/subsetP=> y cxy.
by rewrite -(mulKg x y) [x * y](astab1P cxy) mulVg set11.
Qed.

Lemma astabR : forall G, 'C(G | 'R) = 1.
Proof.
move=> G; apply/trivgP; apply/subsetP=> x cGx.
by rewrite -(mul1g x) [1 * x](astabP cGx) group1.
Qed.

Lemma astabsR : forall G, 'N(G | 'R) = G.
Proof.
move=> G; apply/setP=> x; rewrite !inE -setactVin ?inE //=.
by rewrite -groupV -{1 3}(mulg1 G) rcoset_sym -sub1set -mulGS -!rcosetE.
Qed.

Lemma atransR : forall G, [transitive G, on G | 'R].
Proof. by move=> G; rewrite /atrans -{1}(mul1g G) -orbitR mem_imset. Qed.

Lemma faithfulR : forall G, [faithful G, on G | 'R].
Proof. by move=> G; rewrite /faithful astabR subsetIr. Qed.

Definition Cayley_repr G := actperm <[atrans_acts (atransR G)]>.

Theorem Cayley_isom : forall G, isom G (Cayley_repr G @* G) (Cayley_repr G).
Proof. move=> G; exact: faithful_isom (faithfulR G). Qed.

Theorem Cayley_isog : forall G, G \isog Cayley_repr G @* G.
Proof. move=> G; exact: isom_isog (Cayley_isom G). Qed.

Lemma orbitJ : forall G x, orbit 'J G x = x ^: G. Proof. by []. Qed.

Lemma afixJ : forall A, 'Fix_'J(A) = 'C(A).
Proof.
move=> A; apply/setP=> x; apply/afixP/centP=> cAx y Ay /=.
  by rewrite /commute conjgC cAx.
by rewrite conjgE cAx ?mulKg.
Qed.

Lemma astabJ : forall A, 'C(A |'J) = 'C(A).
Proof.
move=> A; apply/setP=> x; apply/astabP/centP=> cAx y Ay /=.
  by apply: esym; rewrite conjgC cAx.
by rewrite conjgE -cAx ?mulKg.
Qed.

Lemma astab1J : forall x : gT, 'C[x |'J] = 'C[x].

Proof. by move=> x; rewrite astabJ cent_set1. Qed.

Lemma astabsJ : forall G, 'N(G | 'J) = 'N(G).
Proof.
by move=> G; apply/setP=> x; rewrite -2!groupV !inE -conjg_preim -sub_conjg.
Qed.

Lemma setactJ : forall A x, 'J^*%act A x = A :^ x. Proof. by []. Qed.

Lemma gacentJ : forall A, 'C_(|'J)(A) = 'C(A).
Proof. by move=> A; rewrite gacentE ?setTI ?subsetT ?afixJ. Qed.

Lemma orbitRs : forall G A, orbit 'Rs G A = rcosets A G. Proof. by []. Qed.

Lemma sub_afixRs_norms : forall G x A,
 (G :* x \in 'Fix_'Rs(A)) = (A \subset G :^ x).
Proof.
move=> G x A; rewrite inE /=; apply: eq_subset_r => a.
rewrite inE rcosetE -(can2_eq (rcosetKV x) (rcosetK x)) -!rcosetM.
rewrite eqEcard card_rcoset leqnn andbT mulgA (conjgCV x) mulgK. 
by rewrite -{2 3}(mulGid G) mulGS sub1set -mem_conjg.
Qed.

Lemma sub_afixRs_norm : forall G x, (G :* x \in 'Fix_'Rs(G)) = (x \in 'N(G)).
Proof. by move=> G x; rewrite sub_afixRs_norms -groupV inE sub_conjgV. Qed.

Lemma afixRs_rcosets : forall A G,
  'Fix_(rcosets G A | 'Rs)(G) = rcosets G 'N_A(G).
Proof.
move=> A G; apply/setP=> Gx; apply/setIP/rcosetsP=> [[]|[x]].
  case/rcosetsP=> x Ax ->{Gx}; rewrite sub_afixRs_norm => Nx.
  by exists x; rewrite // inE Ax.
by case/setIP=> Ax Nx ->; rewrite -{1}rcosetE mem_imset // sub_afixRs_norm.
Qed.

Lemma astab1Rs : forall G, 'C[G : {set gT} | 'Rs] = G.
Proof.
move=> G; apply/setP=> x.
by apply/astab1P/idP=> /= [<- | Gx]; rewrite rcosetE ?rcoset_refl ?rcoset_id.
Qed.

Lemma actsRs_rcosets : forall H G, [acts G, on rcosets H G | 'Rs].
Proof. by move=> H G; rewrite -orbitRs acts_orbit ?subsetT. Qed.

Lemma transRs_rcosets : forall H G, [transitive G, on rcosets H G | 'Rs].
Proof. by move=> H G; rewrite -orbitRs atrans_orbit. Qed.

Lemma orbitJs : forall G A, orbit 'Js G A = A :^: G. Proof. by []. Qed.

Lemma astab1Js : forall A, 'C[A | 'Js] = 'N(A).
Proof. by move=> A; apply/setP=> x; apply/astab1P/normP. Qed.

Lemma afixJG : forall G A, (G \in 'Fix_'JG(A)) = (A \subset 'N(G)).
Proof.
by move=> G A; apply/afixP/normsP=> nG x Ax; apply/eqP; move/eqP: (nG x Ax).
Qed.

Lemma astab1JG : forall G, 'C[G | 'JG] = 'N(G).
Proof.
move=> G; apply/setP=> x.
by apply/astab1P/normP; [move/(congr1 val) | move/group_inj].
Qed.

Lemma dom_qactJ : forall G, qact_dom 'J G = 'N(G).
Proof. by move=> G; rewrite qact_domE ?subsetT ?astabsJ. Qed.

Lemma qactJ : forall G (Gy : coset_of G) x,
  'Q%act Gy x = if x \in 'N(G) then Gy ^ coset G x else Gy.
Proof.
move=> G Gy; case: (cosetP Gy) => y Ny ->{Gy} x.
by rewrite qactEcond // dom_qactJ; case Nx: (x \in 'N(G)); rewrite ?morphJ. 
Qed.

Lemma astabQ : forall G Abar, 'C(Abar |'Q) = coset G @*^-1 'C(Abar).
Proof.
move=> G Abar; apply/setP=> x; rewrite inE /= dom_qactJ morphpreE in_setI /=.
case Nx: (x \in 'N(G)) => //=; rewrite !inE -sub1set centsC cent_set1.
congr (Abar \subset (_ : {set _})) => {Abar}.
apply/setP=> Gy; rewrite inE qactJ Nx (sameP eqP conjg_fixP).
by rewrite (sameP cent1P eqP) (sameP commgP eqP).
Qed.

Lemma astabsQ : forall A G Bbar,
  (A \subset 'C(Bbar | 'Q)) = (A \subset 'N(G)) && (A / G \subset 'C(Bbar)).
Proof.
move=> A G Bbar; rewrite astabQ -morphpreIdom subsetI.
by case nGA: (A \subset 'N(G)) => //=; rewrite -sub_quotient_pre.
Qed.

Lemma astabsQR : forall A B G,
     A \subset 'N(G) -> B \subset 'N(G) ->
  (A \subset 'C(B / G | 'Q)) = ([~: A, B] \subset G).
Proof.
move=> A B G nGA nGB; rewrite astabsQ nGA /= (sameP commG1P eqP).
by rewrite eqEsubset sub1G andbT -quotientR // quotient_sub1 // comm_subG.
Qed.

Lemma quotient_astabQ : forall G Abar, 'C(Abar | 'Q) / G = 'C(Abar).
Proof. by move=> G Abar; rewrite astabQ cosetpreK. Qed.

Section CardClass.

Variable G : {group gT}.

Lemma index_cent1 : forall x, #|G : 'C_G[x]| = #|x ^: G|.
Proof. by move=> x; rewrite -astab1J -card_orbit. Qed.

Lemma sum_card_class : \sum_(C \in classes G) #|C| = #|G|.
Proof. apply: acts_sum_card_orbit; apply/actsP=> x Gx y; exact: groupJr. Qed.

Lemma class_formula : \sum_(C \in classes G) #|G : 'C_G[repr C]| = #|G|.
Proof.
rewrite -sum_card_class; apply: eq_bigr => C; case/imsetP=> x Gx ->.
have: x \in x ^: G by rewrite -{1}(conjg1 x) mem_imset.
by move/mem_repr; case/imsetP=> y Gy ->; rewrite index_cent1 classGidl.
Qed.

End CardClass.

End InternalGroupAction.

Section AutAct.

Variable (gT : finGroupType) (G : {set gT}).

Definition autact := act ('P \ subsetT (Aut G)).
Canonical Structure aut_action := [action of autact].

Lemma autactK : forall a, actperm aut_action a = a.
Proof. by move=> a; apply/permP=> x; rewrite permE. Qed.

Lemma autact_is_groupAction : is_groupAction G aut_action.
Proof. by move=> a Aa /=; rewrite autactK. Qed.
Canonical Structure aut_groupAction := GroupAction autact_is_groupAction.

End AutAct.

Notation "''A_' G" := (aut_action G)
  (at level 8, format "''A_' G") : action_scope.
Notation "''A_' G" := (aut_groupAction G) : groupAction_scope.

