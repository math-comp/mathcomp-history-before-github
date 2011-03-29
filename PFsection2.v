(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import cyclic pgroup matrix mxalgebra mxrepresentation vector algC.
Require Import character inertia.
Require Import PFsection1.

(******************************************************************************)
(* This file covers Peterfalvi, Section 2: the Dade isometry                  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

Lemma partition_cent_rcoset : forall (gT : finGroupType) (G H : {group gT}) g,
  H \subset G -> g \in 'N_G(H) -> coprime #|H| #[g] ->
  let P := ('C_H[g] :* g) :^: H in partition P (H :* g) /\ #|P| = #|H : 'C[g]|.
Proof.
move=> gT G H g sHG; case/setIP=> Gg nHg coHg P; pose K := cover P.
rewrite -indexgI; do [set C := 'C_H[g]; set Cg := C :* g] in P K *.
have sKHg: K \subset H :* g.
  apply/bigcupsP=> Cgx; case/imsetP=> x Hx ->{Cgx}.
  rewrite conjsgE -rcosetM conjgCV rcosetM mulgA mulSg //.
  by rewrite !mul_subG ?subsetIl // sub1set ?memJ_norm ?groupV.
pose pi := \pi(#[g]); have id_pi: forall u x, u \in Cg -> (u ^ x).`_ pi = g ^ x.
  move=> ug x; case/rcosetP=> u; case/setIP=> Hu cgu ->{ug}.
  rewrite consttJ consttM; last exact/cent1P.
  rewrite (constt_p_elt (pgroup_pi _)) (constt1P _) ?mul1g //.
  by rewrite (mem_p_elt _ Hu) // /pgroup -coprime_pi' // coprime_sym.
have{id_pi} C'tiP: {in H &,
  forall x y, y \notin C :* x -> [disjoint Cg :^ x & Cg :^ y]}.
- move=> x y Hx Hy; apply: contraR; case/pred0Pn=> ugx; case/andP=> /=.
  case/imsetP=> u Cgu ->{ugx}; case/imsetP=> v Cgv eq_ux_vy.
  rewrite mem_rcoset inE groupM ?groupV //= cent1C (sameP cent1P commgP). 
  by apply/conjg_fixP; rewrite conjgM -(id_pi v) // -eq_ux_vy id_pi ?conjgK.
have nzCg: #|Cg| != 0%N by rewrite card_rcoset -lt0n cardG_gt0.
have defC: 'C_H[Cg | 'Js] = C.
  apply/setP=> z; apply/idP/idP=> Cz; have [Hz cz] := setIP Cz; last first.
    by rewrite !inE Hz sub1set inE /= conjsMg (normP cz) conjGid.
  apply: contraR nzCg; rewrite -{1}(mulg1 C); move/(C'tiP _ _ (group1 H) Hz).
  by rewrite (astab1P cz) act1 -setI_eq0 setIid -cards_eq0.
have oP: #|P| = #|H : C| by rewrite card_orbit defC.
have tiP: trivIset P.
  apply/trivIsetP=> Cgx Cgy.
  case/imsetP=> x Hx ->{Cgx}; case/imsetP=> y Hy ->{Cgy}.
  have [Cx_y | not_Cx_y] := boolP (y \in C :* x); last by right; exact: C'tiP.
  rewrite mem_rcoset -defC in Cx_y; have [_ cCg_xy] := setIP Cx_y.
  by left; rewrite -{1}(astab1P cCg_xy) actM actKV.
split=> //; apply/and3P; split=> //; rewrite -/K; last first.
  apply: contra nzCg; case/imsetP=> x _ Cx0.
  by rewrite -(cardJg _ x) -Cx0 cards0.
rewrite eqEcard sKHg -(eqnP tiP) card_rcoset /=.
rewrite (eq_bigr (fun _ => #|C|)) => [|Cgx]; last first.
  by case/imsetP=> x _ ->; rewrite cardJg card_rcoset.
by rewrite sum_nat_const oP mulnC LaGrange ?subsetIl.
Qed.

