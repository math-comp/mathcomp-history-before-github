(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient finalg action.
Require Import zmodp commutator cyclic center pgroup sylow matrix mxalgebra.
Require Import mxpoly mxrepresentation vector algC classfun character.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(******************************************************************************)
(* This file provides basic notions of virtual character theory:              *)
(* 'Z[S, A]      : integer combinations of elements of S : seq {cfun gT that  *)
(*                 have support in A.                                         *)
(* 'Z[T]         : integer combinations of elements S                         *)
(******************************************************************************)

Reserved Notation "''Z[' S , A ]" (at level 0, format "''Z[' S ,  A ]"). 
Reserved Notation "''Z[' S ]" (at level 0, format "''Z[' S ]").

Lemma subseq_filter (T : eqType) (s1 s2 : seq T) (p : pred T) :
  subseq s1 (filter p s2) = all p s1 && subseq s1 s2.
Proof.
elim: s2 s1 => [|x s2 IHs] [|y s1] //=; rewrite ?andbF ?sub0seq //.
case: ifP => [px | pxF] /=; first by case: eqP => [-> | _]; rewrite IHs ?px.
by rewrite IHs /=; case: eqP => // ->; rewrite pxF.
Qed.

Lemma subseq_uniqP (T : eqType) (s1 s2 : seq T) :
  uniq s2 -> reflect (s1 = filter (mem s1) s2) (subseq s1 s2).
Proof.
move=> uniq_s2; apply: (iffP idP) => [ss12 | ->]; last exact: filter_subseq.
apply/eqP; rewrite -size_subseq_leqif ?subseq_filter ?(introT allP) //.
apply/eqP/esym/perm_eq_size.
rewrite uniq_perm_eq ?filter_uniq ?(subseq_uniq ss12) // => x.
by rewrite mem_filter; apply: andb_idr; exact: (mem_subseq ss12).
Qed.

Definition tcast m n T (eq_mn : m = n) t :=
  let: erefl in _ = n := eq_mn return n.-tuple T in t.

Lemma tcastE m n T (eq_mn : m = n) t i :
  tnth (tcast eq_mn t) i = tnth t (cast_ord (esym eq_mn) i) :> T.
Proof. by case: n / eq_mn in i *; rewrite cast_ord_id. Qed.

Lemma tcast_id T n eq_nn t : tcast eq_nn t = t :> n.-tuple T.
Proof. by rewrite (eq_axiomK eq_nn). Qed.

Lemma tcastK T m n eq_mn : cancel (@tcast m n T eq_mn) (tcast (esym eq_mn)).
Proof. by case: n / eq_mn. Qed.

Lemma tcastKV T m n eq_mn : cancel (tcast (esym eq_mn)) (@tcast m n T eq_mn).
Proof. by case: n / eq_mn. Qed.

Lemma tcast_trans T m n p eq_mn (eq_np : n = p) (t : m.-tuple T) :
  tcast (etrans eq_mn eq_np) t = tcast eq_np (tcast eq_mn t).
Proof. by case: n / eq_mn eq_np; case: p /. Qed.

Lemma tvalK n T (t : n.-tuple T) : in_tuple t = tcast (esym (size_tuple t)) t.
Proof. by apply: val_inj => /=; case: _ / (esym _). Qed.

Lemma subsetT_hint (T : finType) mA : subset mA (mem [set: T]).
Proof. by rewrite unlock; apply/pred0P=> x; rewrite !inE. Qed.
Hint Resolve subsetT_hint.

Section IsVChar.

Variable (gT : finGroupType) (G : {group gT}).
Implicit Types (A : {set gT}) (f : {cfun gT}) (S : seq {cfun gT}).

Definition virtual_char_pred S A :=
  [pred f \in span S | [&& forallb i, isZC (coord (in_tuple S) f i)
                         & support f \subset A]].

Local Notation "''Z[' S , A ]" := (virtual_char_pred S A) : group_scope.
Local Notation "''Z[' S ]" := 'Z[S, setT] : group_scope.

Lemma vcharP f :
  reflect (exists2 f1, is_char G f1 & exists2 f2, is_char G f2 & f = f1 - f2)
          (f \in 'Z[irr G]).
Proof.
rewrite 2!inE tvalK /tcast; case: _ / (esym _).
have /andP[/(span _ =P _)-> _] := is_basis_irr G.
apply: (iffP and3P) => [[CFf VCf Af] | [f1 Hf1 [f2 Hf2 ->]]]; last first.
  split=> //; first by rewrite memv_sub ?memc_is_char.
  apply/forallP=> i; rewrite linearD linearN !ffunE.
  have dot_i := coord_inner_prodE i (memc_is_char _).
  by rewrite isZC_add ?isZC_opp // isZCE dot_i ?isNatC_coord_char.
pose Nf (i : Iirr G) := isNatC('[f, 'xi_i]_G).
rewrite -(sum_inner_prodE CFf) (bigID Nf) /=.
set f1 := \sum_(i | _) _; set f2 := \sum_(i | _) _; exists f1.
  apply: is_char_sum => i /andP[/isNatCP[n ->] _].
  by rewrite scaler_nat is_char_scal ?is_char_irr.
exists (- f2); last by rewrite opprK.
rewrite -sumr_opp is_char_sum // => i /andP[notNfi _]; rewrite -scaleNr.
have: isZC ('[f, 'xi_i]_G).
  by have:= forallP VCf i; rewrite (coord_inner_prodE _ CFf).
rewrite isZCE [isNatC _](negbTE notNfi) => /isNatCP[n ->].
by rewrite scaler_nat is_char_scal ?is_char_irr.
Qed.

Lemma vchar_char f : is_char G f -> f \in 'Z[irr G].
Proof.
by move=> Hf; apply/vcharP; exists f => //; exists 0; rewrite ?is_char0 ?subr0.
Qed.

Lemma vchar_irr i : 'xi[G]_i \in 'Z[irr G].
Proof. by apply: vchar_char; apply: is_char_irr. Qed.

Lemma support_vchar S A f : f \in 'Z[S, A] -> support f \subset A.
Proof. by case/and3P. Qed.

Lemma span_vchar S A : {subset 'Z[S, A] <= span S}.
Proof. by move=> f /and3P[]. Qed.

Lemma vcharW S A : {subset 'Z[S, A] <= 'Z[S]}.
Proof. by move=> f /and3P[Sf VCf _]; exact/and3P. Qed.

Lemma memc_Zirr : {subset 'Z[irr G] <= 'CF(G)}.
Proof.
by move=> _ /vcharP[f1 ch1 [f2 ch2 ->]]; rewrite memv_sub ?memc_is_char.
Qed.

Lemma vchar_split S A f :
  f \in 'Z[S, A] = (f \in 'Z[S]) && (support f \subset A).
Proof. by rewrite !inE subsetT_hint -!andbA. Qed.

Lemma memc_vchar A : {subset 'Z[irr G, A] <= 'CF(G, A)}.
Proof. by move=> f; rewrite vchar_split memcE => /andP[/memc_Zirr-> ->]. Qed.

Lemma memv_vchar S A f : 
  free S -> support f \subset A -> f \in S -> f \in 'Z[S, A].
Proof.
move=> freeS Af Sf; apply/and3P; split=> //; first exact: memv_span.
have lt_f_S: (index f S < size S)%N by rewrite index_mem.
apply/forallP=> i; rewrite -(nth_index 0 Sf) (free_coordt (Ordinal _)) //.
exact: isZC_nat.
Qed.

Lemma isZC_inner_prod_vchar A (i : Iirr G) f :
  f \in 'Z[irr G, A] -> isZC ('[f, 'xi_i]_G).
Proof.
move=> VCf; have /and3P[_ /forallP] := VCf.
rewrite tvalK /tcast; case: _ / (esym _) => Zf _.
by rewrite -(coord_inner_prodE _ (memc_Zirr (vcharW VCf))) Zf.
Qed.

Lemma isZC_coord_vchar m (S : m.-tuple _) A f i : 
  f \in 'Z[S, A] -> isZC (coord S f i).
Proof. by case/and3P; rewrite tvalK; case: _ / (esym _) => _ /forallP->. Qed.

Lemma inner_prod_vchar A f1 f2 :
    f1 \in 'Z[irr G, A] -> f2 \in 'Z[irr G, A] ->
  '[f1, f2]_G = \sum_(i < Nirr G) '[f1, 'xi_i]_G * '[f2, 'xi_i]_G.
Proof.
move=> /vcharW CFf1 /vcharW CFf2.
rewrite (inner_prod_cf (memc_Zirr CFf1)) ?memc_Zirr //.
by apply: eq_bigr=> t _; rewrite isZC_conj ?(isZC_inner_prod_vchar _ CFf2).
Qed.

Lemma isZC_inner_Zirr : {in 'Z[irr G] &, forall phi psi, isZC ('[phi, psi]_G)}.
Proof.
move=> phi psi Zphi Zpsi; rewrite /= (inner_prod_vchar Zphi Zpsi).
by apply: isZC_sum => k _; rewrite isZC_mul ?(@isZC_inner_prod_vchar setT).
Qed.

Lemma vchar0 S A : 0 \in 'Z[S, A].
Proof.
rewrite !inE; apply/and3P; split; first by apply: mem0v.
  by apply/forallP=> i;rewrite linear0  ffunE (isZC_nat 0). 
by apply/subsetP=> x; rewrite !inE ffunE eqxx.
Qed.

Lemma vchar_opp S A f : (- f \in 'Z[S, A]) = (f \in 'Z[S, A]).
Proof.
wlog suff: f / f \in 'Z[S, A] -> - f \in 'Z[S, A].
  by move=> IH; apply/idP/idP=> /IH //; rewrite opprK.
case/and3P=> Sf /forallP VCf Af; rewrite !inE memvN {}Sf linearN /=.
apply/andP; split; first by apply/forallP=> i; rewrite ffunE isZC_opp.
by apply: etrans Af; apply: eq_subset => a; rewrite !inE ffunE oppr_eq0.
Qed.

Lemma vchar_add S A f1 f2 :
  f1 \in 'Z[S, A]-> f2 \in 'Z[S, A]-> (f1 + f2) \in 'Z[S, A].
Proof.
case/and3P=> Sf1 /forallP VCf1 /off_support Af1.
case/and3P=> Sf2 /forallP VCf2 /off_support Af2.
rewrite !inE memvD //=; apply/andP; split.
  by apply/forallP=> a; rewrite linearD ffunE isZC_add.
by apply/subsetP=> a; apply: contraR => notAa; rewrite ffunE Af1 // add0r Af2.
Qed.

Lemma vchar_sub S A f1 f2 : 
   f1 \in 'Z[S, A] -> f2 \in 'Z[S, A] -> (f1 - f2) \in 'Z[S, A]. 
Proof. by move=> Hf1 Hf2; rewrite vchar_add ?vchar_opp. Qed.

Lemma vchar_scal S A f n : f \in 'Z[S, A] -> (f *+ n) \in 'Z[S, A].
Proof.
by move=> Hf; elim: n => [|n Hn]; rewrite ?vchar0 // mulrS vchar_add.
Qed.

Lemma vchar_scaln S A f n : f \in 'Z[S, A] -> (f *- n) \in 'Z[S, A].
Proof. by move=> Hf; rewrite vchar_opp vchar_scal. Qed.

Lemma vchar_scalZ S A f a : isZC a -> f \in 'Z[S, A] -> a *: f \in 'Z[S, A].
Proof.
move/eqP=> -> /vchar_scal Sf.
by case: getZC => [[] n]; rewrite ?mulNr mul1r ?scaleNr ?vchar_opp scaler_nat.
Qed.

Lemma vchar_sum S A I r (P : pred I) F :
  (forall i, P i -> F i \in 'Z[S, A]) -> \sum_(i <- r | P i) F i \in 'Z[S, A].
Proof.
by move=> S_F; elim/big_rec: _ => [|i f Pi Sf]; rewrite ?vchar0 ?vchar_add ?S_F.
Qed.

Lemma vchar_mul f g A : 
  f \in 'Z[irr G, A]-> g \in 'Z[irr G, A]-> (f * g) \in 'Z[irr G, A].
Proof.
rewrite !(vchar_split _ A) => /andP[/vcharP[f1 Cf1 [f2 Cf2 def_f]] Af].
case/andP=> [/vcharP[g1 Cg1 [g2 Cg2 ->]] _].
apply/andP; split; last first.
  apply/subsetP=> a; rewrite !inE; apply: contraR => notAa.
  by rewrite ffunE (off_support Af) ?mul0r.
have isch := (is_char_add, is_char_mul); apply/vcharP.
exists (f1 * g1 + f2 * g2); first by rewrite !isch.
exists (f1 * g2 + f2 * g1); first by rewrite !isch.
by rewrite mulr_subr def_f !mulr_subl addrAC oppr_sub -!addrA -oppr_add.
Qed.

Lemma vchar_trans S1 S2 A B :
    free S1 -> free S2 -> {subset S1 <= 'Z[S2, B]} ->
  {subset 'Z[S1, A] <= 'Z[S2, A]}.
Proof.
move=> freeS1 freeS2 sS12 f /and3P[S1f VCf Af]; rewrite !inE {}Af andbT.
rewrite (@coord_span _ _ _ (in_tuple S1) f) ?memv_suml // => [|i _]; last first.
  by rewrite memvZ (span_vchar (sS12 _ _)) ?mem_nth ?orbT.
apply/forallP=> i; rewrite coord_sumE isZC_sum // => j _.
rewrite linearZ !ffunE /= isZC_mul ?(forallP VCf) //.
by have/and3P[_ /forallP-> _]: S1`_j \in 'Z[S2, B] by rewrite sS12 ?mem_nth.
Qed.

Lemma vchar_sub_irr S A :
  free S -> {subset S <= 'Z[irr G]} -> {subset 'Z[S, A] <= 'Z[irr G, A]}.
Proof. by move/vchar_trans; apply; exact: free_irr. Qed.

Lemma vchar_subset S1 S2 A :
  free S1 -> free S2 -> {subset S1 <= S2} -> {subset 'Z[S1, A] <= 'Z[S2, A]}.
Proof.
move=> freeS1 freeS2 sS12; apply: vchar_trans setT _ _ _ => // f /sS12 S2f.
exact: memv_vchar.
Qed.

Lemma vchar_subseq S1 S2 A :
  free S2 -> subseq S1 S2 -> {subset 'Z[S1, A] <= 'Z[S2, A]}.
Proof.
move=> freeS2 sS12; apply: vchar_subset (mem_subseq sS12) => //.
by rewrite (subseq_uniqP _ (uniq_free freeS2) sS12) free_filter.
Qed.

Lemma vchar_filter S A (p : pred {cfun gT}) :
  free S -> {subset 'Z[filter p S, A] <= 'Z[S, A]}.
Proof.
move=> freeS; apply: vchar_subset; rewrite ?free_filter // => f.
by rewrite mem_filter => /andP[].
Qed.

End IsVChar.

Notation "''Z[' S , A ]" := (virtual_char_pred S A) : group_scope.
Notation "''Z[' S ]" := 'Z[S, setT] : group_scope.

Section MoreIsVChar.

Variable gT : finGroupType.
Variable G H : {group gT}.

Lemma vchar_restrict f : 
  H \subset G -> f \in 'Z[irr G] -> 'Res[H] f \in 'Z[irr H].
Proof.
move=> HsG /vcharP[f1 Cf1 [f2 Cf2 ->]].
by rewrite linear_sub vchar_sub // vchar_char // (is_char_restrict HsG).
Qed.

Lemma vchar_induced f :
  H \subset G -> f \in 'Z[irr H] -> 'Ind[G, H] f \in 'Z[irr G].
Proof.
move=> HsG /vcharP[f1 Cf1 [f2 Cf2 ->]].
by rewrite linear_sub vchar_sub // vchar_char // is_char_induced.
Qed.

End MoreIsVChar.
