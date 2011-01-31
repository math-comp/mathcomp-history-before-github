(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient finalg action zmodp.
Require Import commutator cyclic center pgroup matrix mxalgebra mxpoly.
Require Import mxrepresentation vector algC character.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.


(**************************************************************************)
(* This file contains the proof of Section1 of Peterfalvi's book          *)
(**************************************************************************)

Section Main.

Variable (gT : finGroupType).

Local Notation "'{ f '^/' N }" := (qfun_of_cfun N f).
Local Notation "'{ f '^()' }" := (cfun_of_qfun f).
Local Notation "'[ u , v  ]@ G":=  (inner_prod (val G) u v) (at level 10).
Local Notation "'{ f | G }" := (crestrict G f).
Local Notation "'{ f ^[ G , H ]}" := (induced G H f).

(* This corresponds to 1.2 in PF *)
Lemma not_in_ker_char0: forall (H G: {group gT}) (i : irr_class G) g,
   g \in G -> H <| G -> ~(H \subset cker G i) -> 'C_H[g] = 1%g -> i g = 0.
Proof.
move=> H G i g InG NN NoN HC.
have: (#|'C_G[g]| <= #|'C_(G/H)[coset H g]|)%N.
  suff->: #|'C_G[g]| = #|'C_G[g] / H|%G.
    by apply: (subset_leq_card (quotient_subcent1 H G g)).
  apply: card_isog.
  apply: isog_trans (second_isog _); last first.
    apply: subset_trans (normal_norm NN).
    by apply: subcent1_sub.
  suff->: H :&: 'C_G[g] = 1%g by exact: quotient1_isog.
    rewrite -HC.
    apply/setP=> h; rewrite inE.
    apply/andP/subcent1P; case=> H1 H2; split=> //.
      by move/subcent1P: H2; case.
    apply/subcent1P; split=> //.
    by apply: (subsetP (normal_sub NN)).
have F1: coset H g \in (G/H)%g.
  by rewrite -imset_coset; apply/imsetP; exists g.
rewrite leq_leC.
move: (irr_second_orthogonal_relation InG InG).
rewrite class_refl=> <-.
move: (irr_second_orthogonal_relation F1 F1).
rewrite class_refl=> <-; rewrite sum_norm_quo //.
rewrite (bigID (fun i : irr_class G => H \subset cker G i)) //=.
set S := \sum_(i | ~~ _) _; set S' := \sum_(i | _) _ => HH.
have F2: 0 = S.
  apply: leC_anti; last by rewrite -(leC_add2l S') addr0.
  by apply: posC_sum=> j _; rewrite /leC subr0; exact: repC_pconj.
apply/eqP;  have: i g * (i g)^* == 0.
  apply/eqP; apply: (posC_sum_eq0 _ (sym_equal F2)).
    by move=> j _; rewrite /leC subr0; exact: repC_pconj.
  by move/negP: NoN->; rewrite  /index_enum -enumT mem_enum.
rewrite mulf_eq0; case/orP=> //.
by rewrite conjC_eq0.
Qed.

(* This is PF 1.8 *)
Lemma irr1_bound_quo : forall (G H1 H2 H3 : {group gT}) (i : irr_class G),
  H1 <| H2 -> H1 \subset cker G i -> H1 \subset H3 -> H3 \subset H2 -> H2 \subset G ->
  (H3/H1 \subset 'Z(H2/H1) -> (i 1)^+2 <= #|G|%:R^+2 * #|H2|%:R^-1 * #|H3|%:R^-1)%g.
Proof.
move=> G H1 H2 H3 i H1nH2 H1sK H1sH3 H3sH2 H2sG QsZ.
pose Cr := irr_rest H2sG i.
case: (boolP (Cr == character0 H2))=> [HH|].
  have: Cr 1%g = 0 by rewrite (eqP HH) cfunE.
  by rewrite crestrictE // => HH1; case/eqP: (irr1_neq0 i).
case/is_comp_neq0=> i1 Hi1.
pose Ir := irr_induced i1 H2sG.
have CIr: is_comp i Ir.
  rewrite /is_comp ncoord_inner_prod ?(induced_in_cfun, char_in_cfun) //.
  rewrite -freciprocity ?char_in_cfun // (inner_prod_charC _ Cr).
  by rewrite  -ncoord_inner_prod // character_in_cfun.
have H1sKi : H1 \subset cker H2 i1.
  suff H1sKri: H1 \subset cker H2 '{i|H2}.
    by apply: (subset_trans H1sKri); exact: (is_comp_cker Hi1).
  apply/subsetP=> g GiG.
  have F: g \in H2 by rewrite (subsetP (subset_trans H1sH3 _)).
  rewrite (char_ckerE Cr) inE F !crestrictE //.
  by move: (subsetP H1sK _ GiG); rewrite irr_ckerE inE (subsetP H2sG) ?F.
pose i2 := qirrc H1 i1.
have ZsC: 'Z(H2/H1)%g \subset  ccenter (H2/H1) i2.
    by rewrite (center_bigcap (H2/H1)); apply: bigcap_inf.
have H21sH: H2 :&: H1 \subset H3.
    apply/subsetP=> g; rewrite inE; case/andP=> _ HH.
    by apply: (subsetP (H1sH3)).
have I1B: i1 1%g ^+ 2 <= #|H2:H3|%:R.
  case: (irr1_bound i2)=> HH _; move: HH.
  have->: i2 1%g = i1 1%g.
    by rewrite -qirrcE // -(coset_id (group1 H1)) (qfuncE _ H1nH2) ?is_char_irr.
  move/leC_trans; apply.
  rewrite -leq_leC // -(index_quotient_eq H21sH) ?normal_norm //.
  rewrite -(@leq_pmul2l #|ccenter (H2 / H1) i2|) ?cardG_gt0 ?ccenter_sub //.
  rewrite  LaGrange ?quotientS ?ccenter_sub //.
  rewrite -(@leq_pmul2l #|(H3/H1)%g|) ?cardG_gt0 //.
  rewrite mulnA mulnAC LaGrange ?quotientS //.
  rewrite mulnC leq_pmul2l ?cardG_gt0 // subset_leq_card //.
  by apply: (subset_trans QsZ).
move: (is_comp_irr1_char1 CIr); rewrite induced1 //= => HH1.
apply: (leC_trans (leC_square (posC_char1 (character_of_irr i)) HH1)).
rewrite commr_exp_mull; last by apply: mulrC.
have F8: 0 < #|H2|%:R^+2 by apply: sposC_mul; apply sposGC.
rewrite -(leC_pmul2l _ _ F8) mulrA -commr_exp_mull; last by apply: mulrC.
rewrite -natr_mul LaGrange // [#|H2|%:R ^+ 2 *_]mulrC -!mulrA.
rewrite !(leC_pmul2l,sposGC) //  [#|H3|%:R ^-1 * _]mulrC !mulrA.
rewrite mulVf ?neq0GC // mul1r -(LaGrange H3sH2) mulrC.
by rewrite natr_mul mulrA mulVf ?(mul1r,neq0GC).
Qed.

(* This is PF 1.5(a) *)
Lemma induced_sum_rcosets : 
  forall (G H : {group gT}) (HnG : H <| G) (i : irr_class H),
  {in H,
    '{'{ i ^[ G , H ]}|H} =1 #|inertia HnG i : H|%:R *:
       \sum_(j \in rcosets (inertia HnG i) G) cfun_conj i (repr j)}.
Proof.
move=> G H HnG i h HiH.
rewrite crestrictE // !(sum_cfunE,cfunE).
apply: (mulfI (neq0GC H)); rewrite !mulrA divff ?(neq0GC H) // mul1r.
rewrite -natr_mul LaGrange ?subset_inertia //.
rewrite -mulr_sumr.
rewrite (reindex invg) /=; last by exists invg=> g; rewrite invgK.
rewrite (eq_bigr (fun j => (cfun_conj i j h))); last first.
  by move=> g Hg; rewrite cfun_conjE.
have F1: forall g : gT, g^-1%g \in G -> 
  (inertia HnG i) :* g \in rcosets (inertia HnG i) G.
  move=> g; rewrite groupV // => GiG; apply/imsetP; exists g=> //.
  by rewrite rcosetE.
rewrite {1}(partition_big _  _ F1) /=.
apply: eq_bigr=> N; case/imsetP=> x XiG ->.
set a := repr _.
rewrite (eq_bigr (fun _ => cfun_conj i a h)); last first.
  move=> i1; case/andP; rewrite groupV /a // => Hi1; move/eqP=> <-.
  suff: cfun_conj i i1 == cfun_conj i (repr ((inertia HnG i) :* i1)).
    by move/eqP<-.
  rewrite (cfun_conj_eqE HnG) ?mem_repr_rcoset //.
  have: inertia HnG i :* i1 \subset G.
    apply/subsetP=> g; case/imset2P=> h1 h2; rewrite !inE.
    by case/andP=> H1iG _ Eh2 ->; rewrite groupM // (eqP Eh2).
  by move/subsetP; apply; apply: (mem_repr_rcoset (inertia_group HnG i) i1).
rewrite -(card_rcoset _ x) -sum1_card natr_sum -!mulr_suml.
apply: eq_big=> [i1|i1]; last by rewrite mul1r.
rewrite rcosetE; apply/andP/idP=>[|HH]; last first.
  split; last by apply/eqP; apply: rcoset_transl.
  case/rcosetP: HH=> h1 H1iI ->; rewrite groupV groupM //.
  by apply: (subsetP (inertia_sub HnG i)).
case=> I1iG; move/eqP<-; apply/rcosetP.
by exists 1%g; rewrite ?mul1g // ?(group1 (inertia_group HnG i)).
Qed.

Lemma induced_sum_rcosets1 : 
  forall (G H : {group gT}) (HnG : H <| G) (i : irr_class H),
  {in H,
    '{'{ i ^[ G , H ]}|H} =1 #|inertia HnG i : H|%:R *:
       \sum_(j \in rcosets (inertia HnG i) G) (i : cfun_type _ _)}.
Proof.
move=> G H HnG i h HiG.
rewrite induced_sum_rcosets //.
rewrite 6!(cfunE,sum_cfunE).
congr (_ * _).
apply: eq_big=> //.
move=> j Hj.
rewrite cfun_conjE.
rewrite (cfunJ (character_in_cfun _)) //. 



(*  This 1.5b *)
Lemma induced_prod_index : 
  forall (G H : {group gT}) (HnG : H <| G) (i : irr_class H),
    '['{i ^[ G , H ]},'{i ^[ G , H ]}]@G = #|inertia HnG i : H|%:R.
Proof.
move=> G H HnG i; have CFi := irr_in_cfun i; have HsG := normal_sub HnG.
rewrite -freciprocity ?induced_in_cfun //.
rewrite inner_prodE.
have: forall (f : character G) g h,  cfun_conj f g h = f h.
move=> f g h.
rewrite cfun_conjE.
rewrite (cfunJ (character_in_cfun _)). 


End Main.