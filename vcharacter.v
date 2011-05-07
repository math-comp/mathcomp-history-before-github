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

(**************************************************************************)
(*                                                                        *)
(* This file contains the basic notions of virtual character theory       *)
(*                                                                        *)
(* 'Z[T,A]       : integer combinations of elements of the tuple T        *)
(*                 that have support in A                                 *)
(* 'Z[T]         : integer combinations of elements of the tuple T        *)
(*                                                                        *)
(*                                                                        *)
(**************************************************************************)

Section IsVChar.

Variable (gT : finGroupType) (G : {group gT}).

Definition virtual_char_pred m (S : m.-tuple {cfun gT}) (A : {set gT}) :
  pred {cfun gT} :=
  [pred x \in span S | (forallb i, isZC (coord S x i)) && has_support x A].

Local Notation " 'Z[ S , A ]" := 
  (virtual_char_pred S A) (format " ''Z[' S ,  A ]"). 

Local Notation " 'Z[ S ]" :=  (virtual_char_pred S setT) (format " ''Z[' S ]"). 

Lemma vcharP : forall  (f : {cfun _}),
  reflect (exists f1, exists f2, [/\ is_char G f1, is_char G f2 & f = f1 - f2])
          (f \in 'Z['Irr(G)]).
Proof.
move=> f; apply: (iffP andP); last first.
  case=> f1; case=> f2 [Hf1 Hf2 ->]; split.
    move: (base_irr_basis G); rewrite /is_basis /is_span.
    case/andP; move/eqP=> -> _.
    by apply: memv_sub; apply: memc_is_char.
  apply/andP; split; last by apply/forallP=> x; rewrite inE.
  apply/forallP=> x; rewrite linearD linearN /= ffunE isZC_add //.
    rewrite isZCE; apply/orP;left.
    by  move: (isNatC_ncoord_char (enum_val x) Hf1);rewrite /ncoord enum_valK.
  by rewrite ffunE isZC_opp //; rewrite isZCE; apply/orP;left;
     move: (isNatC_ncoord_char (enum_val x) Hf2);rewrite /ncoord  enum_valK.
case=> Hs; case/andP; move/forallP => Hc Hss.
pose f1 := \sum_(i : irr G) 
               (if isNatC(ncoord i f) then ncoord i f else 0) *: i%:CF.
pose f2 := \sum_(i : irr G) 
              (if isNatC(-ncoord i f) then -ncoord i f else 0) *: i%:CF.
exists f1; exists f2; split.
- apply: is_char_sum=> i _.
  case: (boolP (isNatC _)); last by rewrite scale0r is_char0.
  by case/isNatCP=> n ->; rewrite scaler_nat is_char_scal // is_char_irr.
- apply: is_char_sum=> i _.
  case: (boolP (isNatC _)); last by rewrite scale0r is_char0.
  by case/isNatCP=> n ->; rewrite scaler_nat is_char_scal // is_char_irr.
rewrite -sumr_sub.
have Hf : f \in 'CF(G).
   by case/andP: (base_irr_basis G) Hs; rewrite /is_span;move/eqP => ->.
rewrite {1}(ncoord_sum Hf); apply: eq_bigr=> chi _.
have: isZC (ncoord chi f) by apply: Hc; rewrite mem_enum.
rewrite isZCE; case/orP=> HH; rewrite HH; case: (boolP (isNatC _))=> HH1.
- suff->: (ncoord chi f) = 0 by rewrite oppr0 !scale0r subrr.
  apply: leC_anti; last by apply posC_isNatC.
  by rewrite -leC_sub sub0r posC_isNatC.
- by rewrite scale0r subr0.
- suff->: (ncoord chi f) = 0 by rewrite oppr0 !scale0r subrr.
  apply: leC_anti; last by apply posC_isNatC.
  by rewrite -leC_sub sub0r posC_isNatC.
by rewrite scale0r sub0r scaleNr opprK.
Qed.

Lemma vchar_char : forall f, is_char G f -> f \in 'Z['Irr(G)].
Proof.
move=> f Hf; apply/vcharP; exists f; exists 0.
by split; [ done | exact: is_char0 | rewrite subr0].
Qed.

Lemma vchar_irr : forall theta : irr G, (theta: {cfun _}) \in 'Z['Irr(G)].
Proof. by move=> theta; apply: vchar_char; apply: is_char_irr. Qed.

Lemma isZC_ncoord_vchar : forall (A : {set gT})(theta : irr G) (f : {cfun _}),
  f \in 'Z['Irr(G), A] -> isZC (ncoord theta f).
Proof. move=> A theta f; case/and3P=> _;move/forallP => HH _; apply: HH. Qed.

Lemma isZC_coord_vchar : forall m (S : m.-tuple _) A f i, 
  f \in 'Z[S, A] -> isZC (coord S f i).
Proof. by move=> m S B i f; case/and3P => _; move/forallP. Qed.

Lemma support_vchar : forall m (S : m.-tuple _) A f,
  f \in 'Z[S, A] -> has_support f A.
Proof. by move=> m S B f; case/and3P. Qed.

Lemma span_vchar : forall m (S : m.-tuple _) A f,
  f \in 'Z[S, A] -> f \in span S.
Proof. by move=> m S B f; case/and3P. Qed.

Lemma memc_vchar : forall f A, f \in 'Z['Irr(G), A]-> f \in 'CF(G, A).
Proof. 
move=> f A;case/and3P=> Hspan; move/forallP => Hc Hsup.
case/andP: (base_irr_basis G) Hspan; rewrite /is_span;move/eqP => -> _ HH.
by rewrite memcE Hsup.
Qed.

Lemma vcharW : forall f A, f \in 'Z['Irr(G), A]-> f \in 'Z['Irr(G)].
Proof. 
move=> f A;case/and3P=> Hspan Hc Hsup;apply/and3P;split => //.
by apply/forallP=>x; rewrite inE.
Qed.

Lemma vchar0 :  forall m (S : m.-tuple _) A,  0 \in 'Z[S, A].
Proof. 
move => m S A;rewrite !inE; apply/and3P;split; first by apply: mem0v.
  by apply/forallP=> i;rewrite linear0  ffunE (isZC_nat 0). 
by apply/forall_inP=> x; rewrite ffunE eqxx.
Qed.

Lemma vchar_support :  forall f A,
          f \in 'Z['Irr(G), A] =  (f \in 'Z['Irr(G)]) && has_support f A.
Proof.
move=> f A; apply/idP/idP=>H.
  move/memc_vchar: (H); rewrite memcE; case/andP=> -> HCF.
  rewrite andbT.
  case/and3P: H=> irrGaa ZGaa Aaa; apply/and3P; split=> //.
  by apply/forallP=> x; rewrite inE.
by case/andP:H; case/and3P=>irrGaa ZGaa Aaa Hs;apply/and3P.
Qed.

Lemma vchar_opp : forall m (S : m.-tuple _) A f ,
  f \in 'Z[S, A]-> (-f) \in 'Z[S, A].
Proof.
move=> m S A f;case/and3P=> Hspan; move/forallP=> HZC; move/forall_inP=> Hs.
apply/and3P;split;first by rewrite memvN.
  by apply/forallP=>i; rewrite linearN ffunE isZC_opp.
by apply/forall_inP=> x H; rewrite ffunE (eqP (Hs _ H)) oppr0.
Qed.

Lemma vchar_add : forall m (S : m.-tuple _) A f1 f2, 
                      f1 \in 'Z[S, A]-> f2  \in 'Z[S, A]-> (f1 + f2) \in 'Z[S, A].
Proof.
move=> m S A f1 f2.
case/and3P=> Hspan1; move/forallP=> HZC1; move/forall_inP=> Hs1.
case/and3P=> Hspan2; move/forallP=> HZC2; move/forall_inP=> Hs2.
apply/and3P;split;first by rewrite  memvD.
  by apply/forallP=>i; rewrite linearD ffunE isZC_add.
apply/forall_inP=> x Hx.
by rewrite ffunE (eqP (Hs1 _ Hx)) (eqP (Hs2 _ Hx)) add0r.
Qed.

Lemma vchar_sub : forall m (S : m.-tuple _) A f1 f2, 
   f1  \in 'Z[S, A]  -> f2 \in 'Z[S, A] -> (f1 - f2) \in 'Z[S, A]. 
Proof.
by move=> m S A f1 f2 Hf1 Hf2; apply: vchar_add=> //; exact: vchar_opp.
Qed.

Lemma vchar_scal : forall m (S : m.-tuple _) A f n,
  f \in 'Z[S, A] -> (f *+ n) \in 'Z[S, A].
Proof.
move=> m S A f n Hf; elim: n=> [|n Hn]; first by rewrite mulr0n  vchar0.
by rewrite mulrS vchar_add.
Qed.

Lemma vchar_scaln : forall m (S : m.-tuple _) A f n,
  f \in 'Z[S, A] -> (f *- n) \in 'Z[S, A].
Proof.
move=> m S A f n Hf; elim: n=> [|n Hn]; first by rewrite oppr0 vchar0.
by rewrite -mulNrn mulrS mulNrn vchar_add // vchar_opp.
Qed.

Lemma vchar_sum : forall m (S : m.-tuple _) A (I : eqType) r (P : I -> bool) 
                              (F : I -> {cfun _}),
  (forall i, ((P i) && (i \in r)) -> (F i) \in 'Z[S, A]) -> 
    (\sum_(i <- r | P i)  F i) \in 'Z[S, A].
Proof.
move=> m S A I r P F; elim: r=> [| a r IH HH].
  by rewrite big_nil vchar0.
have HF : (\sum_(i <- r | P i) F i) \in 'Z[S, A].
  by apply: IH=> i; case/andP=> HH1 HH2; apply: HH; rewrite HH1 inE HH2 orbT.
rewrite big_cons; case: (boolP (P a))=> HP //; rewrite vchar_add //.
by rewrite HH // inE eqxx andbT.
Qed.

Lemma vchar_mul : forall f g A, 
                      f \in 'Z['Irr(G), A]-> g  \in 'Z['Irr(G), A]-> 
                        (f * g) \in 'Z['Irr(G), A].
Proof.
move=>  f g A; rewrite vchar_support; case/andP=> H1f H2f.
rewrite vchar_support; case/andP=> H1g H2g.
rewrite vchar_support; apply/andP; split; last first.
  apply/forall_inP=> x XniA; rewrite ffunE.
  by move/forall_inP: H2f; move/(_ _ XniA); move/eqP->; rewrite mul0r.
case/vcharP:H1f=>f1; case=> f2 [Hf1 Hf2 ->].
case/vcharP:H1g=>g1; case=> g2 [Hg1 Hg2 ->].
apply/vcharP;exists ((f1 * g1) + (f2 * g2));exists ((f1 * g2 ) + (f2 * g1)).
split;rewrite ?(is_char_add, is_char_mul)//.
rewrite !mulr_addl !mulr_subr -!addrA; congr  (_ + _).
rewrite addrC -!addrA !mulNr opprK addrC -!addrA;congr (_ + _). 
by rewrite oppr_add.
Qed.

Lemma vchar_subset :
  forall m n (S1 : m.-tuple {cfun gT}) (S2 : n.-tuple _) A,
  free S1 -> free S2 -> {subset S1 <= S2} -> {subset 'Z[S1,A] <= 'Z[S2,A]}.
Proof.
move=> m n S1 S2 A FS1 FS2 Hs f; case/and3P=> Hf Cf Sf; apply/and3P; split=> //.
  by move/subvP: (span_subset Hs); apply.
apply/forallP=> /= i.
case: m S1 FS1 Hs Hf {Sf}Cf=> [|m S1 FS1 Hs Hf Cf].
  (do 2 case)=> //= _ _ _ HH _; move: HH; rewrite span_nil.
  case/injvP=> k; rewrite scaler0=> ->.
  by rewrite linear0 ffunE (isZC_nat 0).
case: n i S2 FS2 Hs=> [|n] i S2 FS2 Hs.
  by move: (uniq_leq_size (free_uniq FS1) Hs); rewrite !size_tuple.
pose g (i : 'I_n.+1) : 'I_m.+1 := locked (inZp (index S2`_i S1)).
pose h (i : 'I_m.+1) : 'I_n.+1 := locked (inZp (index S1`_i S2)).
pose c (i : 'I_n.+1) := if S2`_ i \in S1 then (coord S1 f) (g i) else 0.
suff->: f = \sum_(i < n.+1) c i *: (S2`_i).
  rewrite free_coords // /c /=; case: (boolP (_ \in _))=> Hi; last first.
    by rewrite (isZC_nat 0).
  by move/forallP: Cf; apply.
rewrite (bigID (fun i : 'I_n.+1 =>  S2`_i \in S1)) /= [X in _ + X]big1 ?addr0.
  have F0: forall j : 'I_m.+1, S1`_j \in S2.
    by move=> j;  rewrite Hs // mem_nth // size_tuple.
  have F1: forall j : 'I_m.+1,S2`_(h j) = S1`_j.
    move=> j; rewrite /h; unlock; rewrite /= modn_small ?nth_index //.
    by move: (F0 j); rewrite -index_mem size_tuple.
  have F2: forall j : 'I_n.+1, S2`_j \in S1 -> S1`_(g j) = S2`_j.
    move=> j FF; rewrite /g; unlock; rewrite /= modn_small ?nth_index //.
    by move: FF; rewrite -index_mem size_tuple.
  have F3: forall j, g (h j) = j. 
    move=> j; rewrite /g; unlock; rewrite F1.
    apply/val_eqP=> /= ; rewrite /= modn_small.
      by rewrite index_uniq ?size_tuple // free_uniq.
    by rewrite -{4}(size_tuple S1) index_mem // mem_nth // size_tuple.
  rewrite (eq_bigr (fun i => (coord S1 f) (g i) *: S1`_(g i))); last first.
     by move=> j SiS; rewrite /c SiS F2.
  rewrite (reindex h) /=.
    rewrite (coord_span Hf).
    apply: eq_big=> /= [j|j _].
      by rewrite F1 mem_nth // size_tuple.
    by rewrite F3 free_coords.
  exists g=> u; rewrite inE ? F3 //=.
  move=> FF; rewrite /h; unlock; rewrite F2 //.
  apply/val_eqP=> /= ; rewrite /= modn_small.
   by rewrite index_uniq ?size_tuple // free_uniq.
  by rewrite -{4}(size_tuple S2) index_mem // mem_nth // size_tuple.
by move=> j; rewrite /c; move/negPf->; exact: scale0r.
Qed.

Lemma vchar_split :  forall m (S : m.-tuple _) A (f : {cfun gT}), 
          f \in 'Z[S, A] =  (f \in 'Z[S]) && has_support f A.
Proof.
(move=> m S A f; apply/and3P/andP; case)=> [H1 H2 H3|H1 H2]; split=> //.
- apply/and3P; split=> //.
  by apply/forall_inP=> i; rewrite inE.
- by case/and3P: H1.
by case/and3P: H1.
Qed.

Lemma memv_vchar :  forall m (S : m.-tuple _) A (f : {cfun gT}), 
          free S -> has_support f A -> f \in S -> f \in 'Z[S,A].
Proof.
move=> [|m] S A f HF HS FiS.
  by case: {HF}S FiS; case.
apply/and3P; split=> //; first by apply: memv_span.
apply/forallP=> i.
have->: f = S`_(inZp (index f S): 'I_m.+1).
  by rewrite /= modn_small ?nth_index // -{2}(size_tuple S) index_mem.
by rewrite (free_coordt _ _ HF) isZC_nat.
Qed.

Lemma inner_prod_vchar :
   forall A (chi1 chi2 : {cfun gT}),
   chi1 \in 'Z['Irr(G),A] -> chi2 \in 'Z['Irr(G),A] ->
   '[chi1, chi2]_G = \sum_(theta: irr G) ncoord theta chi1 * ncoord theta chi2.
Proof.
move=> A chi1 chi2 H1 H2.
move/memc_vchar: (H1)=>/memcW H1CF; move/memc_vchar:(H2)=>/memcW H2CF.
move: H1;rewrite vchar_split; case/andP;case/and3P=> Hsp1 HZC1 _ _.
move: H2;rewrite vchar_split; case/andP;case/and3P=> Hsp2 HZC2 _ _.
rewrite (inner_prod_cf H1CF) //.
by apply: eq_bigr=> t _; rewrite isZC_conj //; move/forallP: HZC2=> ->.
Qed.

End IsVChar.

Notation " 'Z[ S , A ]" := 
  (virtual_char_pred S A) (format " ''Z[' S ,  A ]").

Notation " 'Z[ S ]" :=  (virtual_char_pred S [set : _]) (format " ''Z[' S ]"). 

Section MoreIsVChar.

Variable gT : finGroupType.
Variable G H : {group gT}.

Lemma vchar_restrict : forall f, 
  H \subset G -> f \in 'Z['Irr(G)] -> 'Res[H] f \in 'Z['Irr(H)].
Proof.
move=> f HsG; case/vcharP=> f1; case=> f2 [Hf1 Hf2 ->].
by rewrite linearD linearN vchar_sub // vchar_char // (is_char_restrict HsG).
Qed.

Lemma vchar_induced : forall chi,
   H \subset G -> chi \in 'Z['Irr(H)] -> 'Ind[G,H] chi \in 'Z['Irr(G)].
Proof.
move=> chi HsG; case/vcharP=> f1; case=> f2 [Hf1 Hf2 ->].
by rewrite linearD linearN vchar_add ?vchar_opp //
           vchar_char // is_char_induced.
Qed.

End MoreIsVChar.
