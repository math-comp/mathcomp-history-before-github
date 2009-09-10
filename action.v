(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq fintype.
Require Import bigops finset groups perm morphisms normal automorphism.

(*****************************************************************************)
(* Group action: orbits, stabilisers, transitivity.                          *)
(*        is_action to D == the function to : T -> aT -> T defines an action *)
(*                          of D : {set aT} on T                             *)
(*            action D T == structure for a function defining an action of D *)
(*    {action: aT &-> T} == structure for a total action                     *)
(*                       == action [set: aT] T                               *)
(*   TotalAction to1 toM == the constructor for total actions; to1 and toM   *)
(*                          are the proofs of the morphism identities for 1  *)
(*                          and a * b, respectively.                         *)
(*       groupAction D R == the structure for group actions of D on R, i.e., *)
(*                          representations of D in automorphisms of R.      *)
(*                          This is a telescope on action D rT, and requires *)
(*                          a finGroupType structure on rT.                  *)
(*     GroupAction toAut == construct a groupAction for action to from       *)
(*                          toAut : actm to @* D \subset Aut R (actm to is   *)
(*                          the morphism to {perm rT} associated to 'to').   *)
(*      orbit to A x == the orbit of x under the action of A via to          *)
(*      'C_A[x | to] == the stabiliser of x : rT in A :&: D                  *)
(*      'C_A(S | to) == the pointwise stabiliser of S : {set rT} in D :&: A  *)
(*      'N_A(S | to) == the global stabiliser of S : {set rT} in D :&: A     *)
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
(* cetraliser in R of the action of D :&: A via to.                          *)
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
(*  ract(ion)_in to sAD == the action of A by to, with sAD : A \subset D.    *)
(*  ract(ion)_by to nRA == the action of A by to, corestricted to R          *)
(*                         with nRA : [acts A, on R | to].                   *)
(*       subact(ion) to == the action to corestricted to a subType           *)
(*      subact_dom P to == the domain of subact for sT : subType P.          *)
(*                      == 'N([set x | P x] | to)                            *)
(*        qact_dom to H == the domain of to / H                              *)
(*                      == 'N(rcosets H 'N(H) | to^* )                       *)
(*    morph_act(ion) phi== the action induced by phi : D >-> {perm rT}.      *)
(*              actm to == the morphism D >-> {perm rT} induced by to.       *)
(*           gactm to a == if a \in D, the (auto)morphism on R induced by    *)
(*                         the group action of a via to (this is canonically *)
(*                         a morphism, as if a \notin D then gactm to a      *)
(*                         defaults to the identity function).               *)
(*  The internal action 'J, its restrictions, quotients, mod, etc. are all   *)
(* recognized as group actions. Convrsely, gprod.v will provide a semidirect *)
(* group construction that maps an external group action to an internal one. *)
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

Record action A T := Action { actby :> T -> aT -> T; _ : is_action actby A}.

Definition TotalAction T to to1 toM := Action (@is_total_action T to to1 toM).

Definition repack_action A T f :=
  let: Action _ fP := f return {type of @Action A T for f} -> action A T
  in fun k => k fP.

Definition actdom A T of action A T := A.

End ActionDef.

Notation "{ 'action' aT &-> T }" := (action [set: aT] T)
  (at level 0, format "{ 'action'  aT  &->  T }") : type_scope.

Notation "[ 'action' 'of' to ]" :=
    (repack_action (fun aP => @Action _ _ _ to aP))
  (at level 0, format "[ 'action'  'of'  to ]") : form_scope.

Delimit Scope action_scope with act.
Bind Scope action_scope with action.
Arguments Scope actby
  [_ group_scope type_scope action_scope group_scope group_scope].
Arguments Scope actdom [_ group_scope type_scope action_scope].

Section ActionOpsDef.

Variables (aT : finGroupType) (D : {set aT}) (rT : finType).
Implicit Type to : action D rT.
Implicit Type A : {set aT}.
Implicit Type S : {set rT}.

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

Section RawAction.

(* Lemmas that do not require the group structure on the action domain. *)

Variables (aT : finGroupType) (D : {set aT}) (rT : finType) (to : action D rT).

Implicit Types a : aT.
Implicit Types x y : rT.
Implicit Type A B : {set aT}.
Implicit Types S : {set rT}.

Lemma act_inj : forall a, injective (to^~ a).
Proof. by case: to => ? []. Qed.

Lemma actMin : {in D &, forall a b x, to x (a * b) = to (to x a) b}.
Proof. by case: to => ? []. Qed.

Lemma orbitE : forall A x, orbit to A x = to x @: A. Proof. by []. Qed.

Lemma orbitP : forall A x y,
  reflect (exists2 a, a \in A & to x a = y) (y \in orbit to A x).
Proof. by move=> A x y; apply: (iffP imsetP) => [] [a]; exists a. Qed.

Lemma orbit_act : forall A x a, a \in A -> to x a \in orbit to A x.
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

Lemma astab_dom : forall S, {subset 'C(S | to) <= D}.
Proof. by move=> S a; case/setIdP. Qed.

Lemma astab_act : forall S a x, a \in 'C(S | to) -> x \in S -> to x a = x.
Proof.
move=> S a x; case/setIdP=> _ cSa Sx; apply/eqP.
by have:= subsetP cSa x Sx; rewrite inE.
Qed.

Lemma astabs_dom : forall S, {subset 'N(S | to) <= D}.
Proof. by move=> S a; case/setIdP. Qed.

Lemma raw_astabs_act : forall S a,
  S \subset to^~ a @^-1: S -> S = to^~ a @^-1: S.
Proof.
move=> S a sSa'S; apply/eqP.
by rewrite eqEcard {}sSa'S card_preimset //=; exact: act_inj.
Qed.

Lemma astabs_act : forall S a x,
  a \in 'N(S | to) -> (to x a \in S) = (x \in S).
Proof.
by move=> S a x; case/setIdP=> _ nSa; rewrite {2}(raw_astabs_act nSa) inE.
Qed.

Lemma astab_sub : forall S, 'C(S | to) \subset 'N(S | to).
Proof.
move=> S; apply/subsetP=> a cSa; rewrite inE (astab_dom cSa).
by apply/subsetP=> x Sx; rewrite inE (astab_act cSa).
Qed.

Lemma acts_dom : forall A S, [acts A, on S | to] -> A \subset D.
Proof.
by move=> A S nSA; apply/subsetP=> a; move/(subsetP nSA); case/setIdP.
Qed.

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

End RawAction.

Implicit Arguments act_inj [aT D rT].
Implicit Arguments orbitP [aT D rT to A x y].
Implicit Arguments afixP [aT D rT to A x].
Implicit Arguments afix1P [aT D rT to a x].
Prenex Implicits act_inj orbitP afixP afix1P.

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

Lemma actKin : forall a, a \in D -> cancel (to^~ a) (to^~ a^-1).
Proof. by move=> a Da x; rewrite -actMin ?groupV // mulgV act1. Qed.

Lemma actKVin : forall a, a \in D -> cancel (to^~ a^-1) (to^~ a).
Proof. by move=> a Da x; rewrite -{2}(invgK a) actKin ?groupV. Qed.

Lemma orbit_refl : forall A x, x \in orbit to A x.
Proof. by move=> A x; rewrite -{1}[x]act1 orbit_act. Qed.

Local Notation orbit_rel A := (fun x y => y \in orbit to A x).

Lemma sub_orbit_sym : forall A, A \subset D -> symmetric (orbit_rel A).
Proof.
move=> A sAD; apply: symmetric_from_pre => x y; case/imsetP=> a Aa.
by move/(canLR (actKin (subsetP sAD a Aa))) <-; rewrite orbit_act ?groupV.
Qed.

Lemma sub_orbit_trans : forall A, A \subset D -> transitive (orbit_rel A).
Proof.
move=> A sAD y x z; case/imsetP=> a Aa ->; case/imsetP=> b Ab ->{y z}.
by rewrite -actMin ?orbit_act ?groupM // (subsetP sAD).
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
  by rewrite inE group1; apply/subsetP=> x _; rewrite inE act1.
rewrite inE groupM ?(@astab_dom _ _ _ to S) //; apply/subsetP=> x Sx.
by rewrite inE actMin ?(@astab_dom _ _ _ to S) ?(astab_act _ Sx).
Qed.

Canonical Structure astab_group S := group (group_set_astab S).

Lemma group_set_astabs : forall S, group_set 'N(S | to).
Proof.
move=> S; apply/group_setP; split=> [|a b cSa cSb].
  by rewrite inE group1; apply/subsetP=> x Sx; rewrite inE act1.
rewrite inE groupM ?(@astabs_dom _ _ _ to S) //; apply/subsetP=> x Sx.
by rewrite inE actMin ?(@astabs_dom _ _ _ to S) ?astabs_act.
Qed.

Canonical Structure astabs_group S := group (group_set_astabs S).

Lemma astab_norm : forall S, 'N(S | to) \subset 'N('C(S | to)).
Proof.
move=> S; apply/subsetP=> a nSa; rewrite inE sub_conjg; apply/subsetP=> b cSb.
have [Da Db] := (astabs_dom nSa, astab_dom cSb).
rewrite mem_conjgV inE groupJ //; apply/subsetP=> x Sx.
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

Lemma acts_subnorm_fix : forall A, [acts 'N_D(A), on 'Fix_to(D :&: A) | to].
Proof.
move=> A; apply/subsetP=> a nAa; have [Da _] := setIP nAa; rewrite inE Da.
apply/subsetP=> x Cx; rewrite inE; apply/afixP=> b Hb.
have [Db _]:= setIP Hb; rewrite -actMin // conjgCV  actMin ?groupJ ?groupV //.
by rewrite (afixP Cx) // memJ_norm // groupV (subsetP (normsGI _ _) _ nAa).
Qed.

End PartialAction.

Implicit Arguments orbit1P [aT D rT to A x].
Prenex Implicits orbit1P.

Notation "''C' ( S | to )" := (astab_group to S) : subgroup_scope.
Notation "''C_' A ( S | to )" := (A :&: 'C(S | to))%G : subgroup_scope.
Notation "''C' [ x | to ]" := ('C([set x] | to))%G : subgroup_scope.
Notation "''C_' A [ x | to ]" := (A :&: 'C[x | to])%G : subgroup_scope.
Notation "''N' ( S | to )" := (astabs_group to S) : subgroup_scope.
Notation "''N_' A ( S | to )" := (A :&: 'N(S | to))%G : subgroup_scope.

Section TotalAction.
(* These lemmas are only established for total actions (domain = [set: rT]) *)

Variable (aT : finGroupType) (rT : finType).

Variable to : {action aT &-> rT}.

Implicit Types a b : aT.
Implicit Types x y z : rT.
Implicit Types A B : {group aT}.
Implicit Types S : {set rT}.

Lemma actM : forall x a b, to x (a * b) = to (to x a) b.
Proof. by move=> x a b; rewrite actMin ?inE. Qed.

Lemma actK : forall a, cancel (to^~ a) (to^~ a^-1).
Proof. by move=> a; apply: actKin; rewrite inE. Qed.

Lemma actKV : forall a, cancel (to^~ a^-1) (to^~ a).
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

Lemma astabsP : forall S a,
  reflect (forall x, (to x a \in S) = (x \in S)) (a \in 'N(S | to)).
Proof.
move=> S a; apply: (iffP idP) => [nSa x|nSa]; first exact: astabs_act.
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

Lemma astab_imset : forall S a, 'C(to^~a @: S | to) = 'C(S | to) :^ a.
Proof.
move=> S a; apply/setP=> b; rewrite mem_conjg.
apply/astabP/astabP=> stab x => [Sx|].
  by rewrite conjgE invgK !actM stab ?actK //; apply/imsetP; exists x.
by case/imsetP=> y Sy ->{x}; rewrite -actM conjgCV actM stab.
Qed.

Lemma astab1_act : forall x a, 'C[to x a | to] = 'C[x | to] :^ a.
Proof. by move=> x a; rewrite -astab_imset imset_set1. Qed.

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

End TotalAction.

Implicit Arguments astabP [aT rT to S a].
Implicit Arguments astab1P [aT rT to x a].
Implicit Arguments astabsP [aT rT to S a].
Implicit Arguments atransP [aT rT to A S].
Implicit Arguments actsP [aT rT to A S].
Implicit Arguments faithfulP [aT rT to A S].
Prenex Implicits astabP astab1P astabsP atransP actsP faithfulP.

Section SetAction.

Variables (aT : finGroupType) (D : {set aT}) (rT : finType).
Variable to : action D rT.

Definition setact (S : {set rT}) a := [set to x a | x <- S].

Lemma setactE : forall S a, setact S a = [set to x a | x <- S].
Proof. by []. Qed.

Lemma setact_is_action : is_action setact D.
Proof.
split=> [a S1 S2 eqS12 | a b Da Db S]; last first.
  rewrite /setact /= -imset_comp; apply: eq_imset => x; exact: actMin.
apply/setP=> x; wlog S1x: S1 S2 eqS12 / x \in S1.
  by move=> IH; apply/idP/idP=> Sx; move/IH: (Sx) => <-.
have: to x a \in setact S1 a by apply/imsetP; exists x.
by rewrite eqS12 S1x; case/imsetP=> y S2y; move/act_inj->.
Qed.

Canonical Structure set_action := Action setact_is_action.

Lemma astab1_set : forall S, 'C[S | set_action] = 'N(S | to).
Proof.
move=> S; apply/setP=> a; rewrite inE sub1set inE /=.
rewrite eqEcard (card_imset _ (act_inj _ _)) leqnn andbT.
apply/andP/idP=> [[Da nSa] | nSa].
  rewrite inE Da; apply/subsetP=> x Sx; rewrite inE.
  exact: (subsetP nSa) (mem_imset _ Sx).
split; first exact: (astabs_dom nSa).
by apply/subsetP=> xa; case/imsetP=> x Sa ->{xa}; rewrite astabs_act.
Qed.

End SetAction.

Notation "to ^*" := (set_action to)
  (at level 2, format "to ^*") : action_scope.

Section RestrictAction.

Variables (aT : finGroupType) (D : {set aT}) (rT : finType).
Variable to : action D rT.
Variables (A : {set aT}) (B : {group aT}) (S : {set rT}).

Definition ract_in of A \subset D := actby to.
Definition ract_by of [acts B, on S | to] :=
  fun x a => if (x \in S) && (a \in B) then to x a else x.

Lemma ract_in_is_action : forall sAD, is_action (ract_in sAD) A.
Proof.
move=> sAD; split; first exact: act_inj.
by apply: sub_in2 (actMin to); exact/subsetP.
Qed.

Lemma ract_by_is_action : forall nSB, is_action (ract_by nSB) B.
Proof.
rewrite /ract_by => nSa; split=> [a x y | a b Aa Ab x /=]; last first.
  rewrite Aa Ab groupM // !andbT actMin ?(subsetP (acts_dom nSa)) //.
  by case Sx: (x \in S); rewrite ?(acts_act nSa) ?Sx.
case Aa: (a \in B); rewrite ?andbF ?andbT //.
case Sx: (x \in S); case Sy: (y \in S) => // eqxy; first exact: act_inj eqxy.
  by rewrite -eqxy (acts_act nSa Aa) Sx in Sy.
by rewrite eqxy (acts_act nSa Aa) Sy in Sx.
Qed.

Canonical Structure raction_in sAD := Action (ract_in_is_action sAD).
Canonical Structure raction_by nSB := Action (ract_by_is_action nSB).

End RestrictAction.

Section SubAction.

Variables (aT : finGroupType) (D : {group aT}).
Variables (rT : finType) (sP : pred rT) (sT : subType sP) (to : action D rT).

Definition subact_dom := 'N([set x | sP x] | to).
Canonical Structure subact_dom_group := [group of subact_dom].

Lemma sub_act_proof : forall (u : sT) (Na : subg_of subact_dom_group),
  sP (to (val u) (val Na)).
Proof.
move=> u [a] /=; case/setIdP=> _; move/subsetP; move/(_ (val u)).
by rewrite !inE valP => ->.
Qed.

Definition subact u a :=
  if insub a is Some Na then Sub _ (sub_act_proof u Na) else u.

Lemma val_subact : forall u a,
  val (subact u a) = if a \in subact_dom then to (val u) a else val u.
Proof.
move=> u a; rewrite /subact -if_neg.
by case: insubP => [Na|] -> //=; rewrite SubK => ->.
Qed.

Lemma subact_is_action : is_action subact subact_dom.
Proof.
split=> [a u v eq_uv | a b Na Nb u]; apply: val_inj.
  move/(congr1 val): eq_uv; rewrite !val_subact.
  by case: (a \in _); first move/act_inj.
have Da := astabs_dom Na; have Db := astabs_dom Nb. 
by rewrite !val_subact Na Nb groupM ?actMin.
Qed.

Canonical Structure subaction := Action subact_is_action.

End SubAction.

Section QuotientAction.

Variables (aT : finGroupType) (D : {group aT}) (rT : finGroupType).
Variables (to : action D rT) (H : {group rT}).

Definition qact_dom := 'N(rcosets H 'N(H) | to^*).
Canonical Structure qact_dom_group := [group of qact_dom].

Local Notation subdom := (subact_dom (coset_range H) to^*).
Fact qact_subdomE : subdom = qact_dom.
Proof. by congr 'N(_|_); apply/setP=> Hx; rewrite !inE genGid. Qed.
Lemma qact_subproof : qact_dom \subset subdom.
Proof. by rewrite qact_subdomE. Qed.

Definition qact : coset_of H -> aT -> coset_of H :=
  ract_in (subaction _ to^*) qact_subproof.

Canonical Structure quotient_action := [action of qact].

Lemma acts_qact_dom : [acts qact_dom, on 'N(H) | to].
Proof.
apply/subsetP=> a nNa; rewrite inE (astabs_dom nNa); apply/subsetP=> x Nx.
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

Lemma modact_is_action : is_action modact (D / A).
Proof.
split=> [Aa x y | Aa Ab]; last first.
  case/morphimP=> a Na Da ->{Aa}; case/morphimP=> b Nb Db ->{Ab} x /=.
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

Lemma act_Cayley : forall G H, [acts G, on rcosets H G | 'Rs].
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

Lemma setactJ : forall A x, actby 'J^* A x = A :^ x. Proof. by []. Qed.

Lemma dom_qactJ : forall G, qact_dom 'J G = 'N(G).
Proof.
move=> G; apply/setP=> x; rewrite 2!inE; apply/subsetP/normP=> Nx.
  move/implyP: {Nx}(Nx G); rewrite !inE -{1}(rcoset1 G) -rcosetE.
  rewrite mem_imset ?group1 //= setactJ.
  case/rcosetsP=> y Hy def_Gx; rewrite def_Gx rcoset_id //.
  by rewrite -(mulg1 G) rcoset_sym -def_Gx group1.
move=> Gy; rewrite !inE; case/rcosetsP=> y Ny ->{Gy}.
by rewrite [_ x]conjsMg conjg_set1 Nx -rcosetE mem_imset ?groupJ // inE Nx.
Qed.

Lemma qactJ : forall G (Gy : coset_of G) x,
  'Q%act Gy x = if x \in 'N(G) then Gy ^ coset G x else Gy.
Proof.
move=> G Gy; case: (cosetP Gy) => y Ny ->{Gy} x.
by rewrite qactEcond // dom_qactJ; case Nx: (x \in 'N(G)); rewrite ?morphJ. 
Qed.

Lemma astab_quo : forall G (Abar : {set coset_of G}),
  'C(Abar |'Q) = coset G @*^-1 'C(Abar).
Proof.
move=> G Abar; apply/setP=> x; rewrite inE /= dom_qactJ morphpreE in_setI /=.
case Nx: (x \in 'N(G)) => //=; rewrite inE -sub1set centsC cent_set1.
congr (Abar \subset (_ : {set _})) => {Abar}.
apply/setP=> Gy; rewrite inE qactJ Nx (sameP eqP conjg_fixP).
by rewrite (sameP cent1P eqP) (sameP commgP eqP).
Qed.

Lemma astabs_quo : forall A G Bbar,
  (A \subset 'C(Bbar | 'Q)) = (A \subset 'N(G)) && (A / G \subset 'C(Bbar)).
Proof.
move=> A G Bbar; rewrite astab_quo -morphpreIdom subsetI.
by case nGA: (A \subset 'N(G)) => //=; rewrite -sub_quotient_pre.
Qed.

Lemma quotient_astab_quo : forall G Abar, 'C(Abar | 'Q) / G = 'C(Abar).
Proof. by move=> G Abar; rewrite astab_quo cosetpreK. Qed.

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

Variable rT : finType.
Notation gT := {perm rT}.
Implicit Types a b c : gT.

Lemma aperm_is_action : is_action (@aperm rT) setT.
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

Implicit Arguments perm_act1P [rT a].
Prenex Implicits perm_act1P.

Notation "'P" := (perm_action _) (at level 0) : action_scope.

Section MorphAct.

Variables (aT : finGroupType) (D : {group aT}) (rT : finType).
Variable phi : {morphism D >-> {perm rT}}.

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
move/astab_act=> a1; apply/set1P; apply: phi_inj => //.
by apply/permP=> x; rewrite morph1 perm1 -morph_actE a1 ?inE.
Qed.

End MorphAct.

Section ActMorph.

Variable aT : finGroupType.

Section Raw.

Variables (D : {set aT}) (rT : finType) (to : action D rT).

Definition actm a := perm (act_inj to a).

Lemma actmE : forall a x, actm a x = to x a.
Proof. by move=> a x; rewrite permE. Qed.

Lemma aperm_actm : forall x a, aperm x (actm a) = to x a.
Proof. move=> x a; exact: actmE. Qed.

Lemma perm_of_actM : {in D &, {morph actm : a b / a * b}}.
Proof. by move=> a b Da Db; apply/permP=> x; rewrite permM !permE actMin. Qed.

Canonical Structure actm_morphism := Morphism perm_of_actM.

End Raw.

Variables (D : {group aT}) (rT : finType) (to : action D rT) (S : {set rT}).

Lemma faithful_isom :
  [faithful D, on S | to] -> isom D (actm to @: D) (actm to).
Proof.
move=> fful; apply/isomP; split; last exact: morphimEdom.
apply/subsetP=> a; case/morphpreP=> Da; move/set1P=> /= a1; apply/set1P.
apply/set1P; apply: (subsetP fful); rewrite !inE Da; apply/subsetP=> x _.
by rewrite inE -actmE a1 perm1.
Qed.

End ActMorph.

Require Import automorphism.

Section GroupAction.

Variables aT rT : finGroupType.

Section Raw.

Variables (D : {set aT}) (R : {set rT}).

Structure groupAction :=
  GroupAction {gaval :> action D rT; _ : actm gaval @* D \subset Aut R}.

Variable to : groupAction.

Lemma gactAut : actm to @* D \subset Aut R. Proof. by case to. Qed.

Lemma Aut_actm : forall a, a \in D -> actm to a \in Aut R.
Proof. by move=> a Da; by rewrite (subsetP gactAut) // mem_imset ?setIid. Qed.

Lemma gact_out : forall x a, a \in D -> x \notin R -> to x a = x.
Proof. move=> x a Da; rewrite -actmE; apply: out_Aut; exact: Aut_actm. Qed.

Lemma gactM : {in D, forall a, {in R &, {morph to^~ a : x y / x * y}}}.
Proof.
move=> a Da /= x y; rewrite -!(actmE to); apply: morphicP x y.
by rewrite Aut_morphic ?Aut_actm.
Qed.

Definition gactm a := if a \in D then to^~ a else id.

Lemma gactmEfun : forall a, a \in D -> gactm a = to^~ a.
Proof. by rewrite /gactm => a ->. Qed.

Lemma gactmE : forall a, a \in D -> gactm a =1 to^~ a.
Proof. by move=> a Da; rewrite gactmEfun. Qed.

Lemma gactmM : forall a, {in R &, {morph gactm a : x y / x * y}}.
Proof. rewrite /gactm => a; case: ifP => //; exact: gactM. Qed.

Canonical Structure gact_morphism a := Morphism (gactmM a).

Lemma morphim_gactm :
  {in D, forall a (S : {set rT}), S \subset R -> gactm a @* S = to^~ a @: S}.
Proof. by move=> a Da /= S ?; rewrite /morphim /= gactmEfun ?(setIidPr _). Qed.

End Raw.

Variables (D : {group aT}) (R : {group rT}) (to : groupAction D R).

Lemma gact1 : {in D, forall a, to 1 a = 1}.
Proof. by move=> a Da; rewrite /= -gactmE ?morph1. Qed.

Lemma gactV : {in D, forall a, {in R, {morph to^~ a : x / x^-1}}}.
Proof. by move=> a Da /= x Rx; move; rewrite -!gactmE ?morphV. Qed.

Lemma gactX : {in D, forall a n, {in R, {morph to^~ a : x / x ^+ n}}}.
Proof. by move=> a Da /= n x Rx; rewrite -!gactmE // morphX. Qed.

Lemma gactJ : {in D, forall a, {in R &, {morph to^~ a : x y / x ^ y}}}.
Proof. by move=> a Da /= x Rx y Ry; rewrite -!gactmE // morphJ. Qed.

Lemma gactR : {in D, forall a, {in R &, {morph to^~ a : x y / [~ x, y]}}}.
Proof. by move=> a Da /= x Rx y Ry; rewrite -!gactmE // morphR. Qed.

Lemma gact_stable : {acts D, on R | to}.
Proof.
apply: acts_act; apply/subsetP=> a Da; rewrite inE Da.
apply/subsetP=> x; rewrite inE; apply: contraLR => R'xa.
by rewrite -(actKin to Da x) gact_out ?groupV.
Qed.

Definition gact_centraliser (_ : phantom (action _ _) to) A :=
  'Fix_(R | to)(D :&: A).

Lemma group_set_gacent : forall ph A, group_set (gact_centraliser ph A).
Proof.
move=> ph A; apply/group_setP; split=> [|x y].
  rewrite !inE group1; apply/subsetP=> a; case/setIP=> Da _.
  by rewrite inE gact1.
case/setIP=> Rx; move/afixP=> cAx; case/setIP=> Ry; move/afixP=> cAy.
rewrite inE groupM //; apply/afixP=> a Aa.
by rewrite gactM ?cAx ?cAy //; case/setIP: Aa.
Qed.

Canonical Structure gacent_group ph A := Group (group_set_gacent ph A).

End GroupAction.

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

Local Notation aPhantom to := (@Phantom (action _ _) to%act).
Notation "''C_' ( | to ) ( A )" := (gact_centraliser (aPhantom to) A)
  (at level 8, format "''C_' ( | to ) ( A )") : group_scope.
Notation "''C_' ( G | to ) ( A )" := (G :&: 'C_(|to)(A))
  (at level 8, format "''C_' ( G  |  to ) ( A )") : group_scope.
Notation "''C_' ( | to ) [ a ]" := 'C_(|to)([set a])

  (at level 8, format "''C_' ( | to ) [ a ]") : group_scope.
Notation "''C_' ( G | to ) [ a ]" := 'C_(G | to)([set a])
  (at level 8, format "''C_' ( G  |  to ) [ a ]") : group_scope.
Notation "''C_' ( | to ) ( A )" := (gacent_group (aPhantom to) A)
  : subgroup_scope.
Notation "''C_' ( G | to ) ( A )" := (G :&: 'C_(|to)(A))%G : subgroup_scope.
Notation "''C_' ( | to ) [ a ]" := 'C_(|to)([set a%g])%G : subgroup_scope.
Notation "''C_' ( G | to ) [ a ]" := 'C_(G | to)([set a%g])%G : subgroup_scope.

Section InternalGroupAction.

Variable gT : finGroupType.

Lemma internal_Aut : actm 'J @* [set: gT] \subset Aut [set: gT].
Proof.
apply/subsetP=> p; case/imsetP=> a _ ->{p}; rewrite inE.
apply/andP; split; first by apply/subsetP=> x _; rewrite inE.
by apply/morphicP=> x y _ _; rewrite !actmE /= conjMg.
Qed.

Canonical Structure internal_groupAction := GroupAction internal_Aut.

Lemma gacentJ : forall A, 'C_(|'J)(A) = 'C(A).
Proof. by move=> A; rewrite /'C_(|_)(_) !setTI conjg_fix. Qed.

End InternalGroupAction.

Section GroupActionTheory.

Variables (aT rT : finGroupType) (D : {group aT}) (R : {group rT}).
Variables to : groupAction D R.

Lemma injm_gactm : forall a, 'injm (gactm to a).
Proof.
move=> a; apply/injmP=> x y Rx Ry; rewrite /= /gactm; case: ifP => Da //.
exact: act_inj.
Qed. 

Lemma im_gactm : forall a, gactm to a @* R = R.
Proof.
move=> a; apply/eqP; rewrite eqEcard (card_injm (injm_gactm a)) // leqnn andbT.
apply/subsetP=> xa; case/morphimP=> x Rx _ ->{xa} /=.
by rewrite /gactm; case: ifP => // Da; rewrite gact_stable.
Qed.

Section CentElim.

Variables (a : aT) (A : {set aT}) (G : {set rT}).
Hypotheses (Da : a \in D) (sAD : A \subset D) (sGR : G \subset R).

Lemma gacentE : 'C_(|to)(A) = 'Fix_(R | to)(A).
Proof. by rewrite -{2}(setIidPr sAD). Qed.

Lemma gacent1E : 'C_(|to)[a] = 'Fix_(R | to)[a].
Proof. by rewrite /gact_centraliser [D :&: _](setIidPr _) ?sub1set. Qed.

Lemma gacent_inE : 'C_(G | to)(A) = 'Fix_(G | to)(A).
Proof. by rewrite gacentE setIA (setIidPl sGR). Qed.

Lemma gacent1_inE : 'C_(G | to)[a] = 'Fix_(G | to)[a].
Proof. by rewrite gacent1E setIA (setIidPl sGR). Qed.

End CentElim.

Section Restrict.

Variables (A : {group aT}) (G : {group rT}).
Hypotheses (sAD : A \subset D) (nGA : [acts A, on R :&: G | to]).

Lemma ract_in_Aut : actm (raction_in to sAD) @* A \subset Aut R.
Proof.
apply/subsetP=> p; case/morphimP=> a Aa _ ->{p}; apply: (subsetP (gactAut to)).
apply/morphimP; exists a; rewrite ?(subsetP sAD) //=; apply/permP=> x.
by rewrite !actmE.
Qed.

Canonical Structure raction_in_groupAction := GroupAction ract_in_Aut.

Lemma ract_by_Aut : actm (raction_by nGA) @* A \subset Aut (R :&: G).
Proof.
apply/subsetP=> p; case/morphimP=> a Aa _ ->{p}.
rewrite inE; apply/andP; split.
  apply/subsetP=> x; apply: contraR => Gx.
  by rewrite actmE /= /ract_by (negbTE Gx).
apply/morphicP=> x y Gx Gy; rewrite !actmE /= /ract_by Aa groupM ?Gx ?Gy //=.
by rewrite gactM ?(subsetP (subsetIl R G), subsetP sAD).
Qed.
  
Canonical Structure raction_by_groupAction := GroupAction ract_by_Aut.

End Restrict.

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

Lemma qact_Aut : actm (to / H) @* qact_dom to H \subset Aut (R / H).
Proof.
apply/subsetP=> p; case/morphimP=> a HDa _ ->; have Da := astabs_dom HDa.
rewrite inE; apply/andP; split.
  apply/subsetP=> Hx /=; case: (cosetP Hx) => x Nx ->{Hx}.
  apply: contraR => R'Hx; rewrite actmE qactE // gact_out //.
  by apply: contra R'Hx; apply: mem_morphim.
apply/morphicP=> Hx Hy; rewrite !actmE.
case/morphimP=> x Nx Gx ->{Hx}; case/morphimP=> y Ny Gy ->{Hy}.
by rewrite -morphM ?qactE ?groupM ?gactM // morphM ?acts_qact_dom_norm.
Qed.

Canonical Structure quotient_groupAction := GroupAction qact_Aut.

Lemma qact_domE : H \subset R -> qact_dom to H = 'N(H | to).
Proof.
move=> sHR; apply/setP=> a; apply/idP/idP=> nHa; have Da := astabs_dom nHa.
  rewrite inE Da; apply/subsetP=> x Hx; rewrite inE.
  have: to^~ a @: H \in rcosets H 'N(H).
    by rewrite (astabs_act _ nHa) -{1}(mulg1 H) -rcosetE mem_imset ?group1.
  case/rcosetsP=> y Ny defHy; rewrite -(rcoset1 H).
  rewrite (@rcoset_transl _ H 1 y) -defHy -1?(gact1 to Da); exact: mem_imset.
rewrite inE Da; apply/subsetP=> Hx; rewrite inE; case/rcosetsP=> x Nx ->{Hx}.
apply/imsetP; exists (to x a).
  case Rx: (x \in R); last by rewrite gact_out ?Rx.
  rewrite inE; apply/subsetP=> ya; case/imsetP=> y Hy ->{ya}.
  rewrite -(actKVin to Da y) -gactJ // ?(subsetP sHR, astabs_act, groupV) //.
  by rewrite conjg_astabs.
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

Lemma modact_Aut : actm (to %% A) @* (D / A) \subset Aut 'C_(|to)(A).
Proof.
apply/subsetP=> p; case/morphimP=> Aa _; case/morphimP=> a Na Da -> ->{Aa p}.
have NDa: a \in 'N_D(A) by exact/setIP.
rewrite inE; apply/andP; split.
  apply/subsetP=> x; apply: contraR.
  rewrite inE andbC actmE /= modactEcond //.
  by case: ifP => // -> Rx; rewrite gact_out.
apply/morphicP=> x y; case/setIP=> Rx cAx; case/setIP=> Ry cAy.
rewrite /= !actmE /= !modactE ?gactM //.
suff: x * y \in 'C_(|to)(A) by case/setIP.
rewrite groupM //; exact/setIP.
Qed.

Canonical Structure mod_groupAction := GroupAction modact_Aut.

Hypothesis cRA : A \subset 'C(R | to).

Lemma modgactE : forall x a,
  a \in 'N_D(A) -> actby (to %% A) x (coset A a) = to x a.
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
  a \in D -> modact to x (coset 'C(R | to) a) = to x a.
Proof.
move=> x a Da; apply: modgactE => {x}//.
rewrite !inE Da; apply/subsetP=> ca; case/imsetP=> c Cc ->{ca}.
have Dc := astab_dom Cc; rewrite inE groupJ //.
apply/subsetP=> x Rx; rewrite inE conjgE !actMin ?groupM ?groupV //.
by rewrite (astab_act Cc) ?actKVin // gact_stable ?groupV.
Qed.

End GroupActionTheory.

