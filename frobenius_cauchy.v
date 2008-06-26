(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
Require Import ssreflect.
Require Import ssrbool.
Require Import ssrfun.
Require Import eqtype.
Require Import ssrnat.
(* Require Import seq. *)
Require Import fintype.
Require Import connect.
Require Import ssralg.
Require Import bigops.
Require Import finset.
Require Import groups.
Require Import action.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Frob_Cauchy.

Open Scope group_scope.

Variable G : finGroupType.
Variable S : finType.
Variable to : action G S.
Variable H : {group G}.

(* Fg : x of S, left fixed by g *)
Definition act_fix1 g := [set x | to x g == x].

Definition act_nbcomp := #|roots [rel of orbit to H]|.

Hint Resolve orbit_csym.

Lemma stabilizer_to : forall x g,
  g \in normaliser H -> stabilizer to H (to x g) = stabilizer to H x :^ g.
Proof.
move=> x g nHg; apply/setP=> h; rewrite mem_conjg !inE -mem_conjg.
by rewrite (normgP _) // !actM invgK (canF_eq (actKV to g)).
Qed.

Lemma orbit_eq : forall x y,
  y \in (orbit to H x) -> orbit to H x = orbit to H y.
Proof.
move=> x y Hxy; apply/setP=> z; rewrite -!orbit_trans in Hxy *.
exact: same_connect Hxy z.
Qed.

Lemma card_stab_eq : forall x y,
  y \in orbit to H x -> #|stabilizer to H x| = #|stabilizer to H y|.
Proof.
move=> x y; case/orbitP=> g Hg <- {y}; rewrite stabilizer_to ?card_conjg //.
exact: (subsetP (normG H)).
Qed.

(* should become a posnat structure
Lemma indexg_gt0: forall (g : finGroupType) (h k : group g), 0 < indexg h k.
Proof.
move=> g h k; rewrite lt0n; apply/pred0Pn; exists (h :* 1).
by apply/imsetP; exists (1 : g).
Qed.
*)

Theorem Frobenius_Cauchy :
  \sum_(g \in H) #|act_fix1 g| = (act_nbcomp * #|H|)%N.
Proof.
transitivity (\sum_(g \in H) \sum_(x \in act_fix1 g) 1%N).
  by apply: eq_bigr => g _; rewrite sum_nat_const muln1.
rewrite (exchange_big_dep predT) //=; pose orbH := [rel of orbit to H].
rewrite (partition_big (root orbH) (roots orbH)) //= => [|y _]; last first.
  apply: roots_root; exact: orbit_csym.
rewrite -sum_nat_const; apply: eq_bigr => x; move/eqP=> rx.
rewrite (eq_bigl (mem (orbit to H x))) => [|y]; last first.
  by rewrite /= -orbit_trans (sameP (rootP _) eqP) ?rx.
rewrite -(LaGrange (subset_stab to H x)) mulnC -card_orbit -sum_nat_const.
apply: eq_bigr => y Hxy; rewrite sum_nat_const muln1 (card_stab_eq Hxy).
by apply: eq_card => h; rewrite -topredE /= !inE.
Qed.

End  Frob_Cauchy.

