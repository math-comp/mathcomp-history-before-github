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
(*  is_vchar G f : predicates that tells if the function f is a virtual   *)
(*                 character                                              *)
(*                                                                        *)
(**************************************************************************)

Section IsVChar.

Variable (gT : finGroupType) (G : {group gT}) (A : {set gT}).

Definition virtual_char_pred (S : seq (cfun gT algC)) (A : {set gT}) :
  pred (cfun gT algC) :=
  [pred x \in span S | (forallb i, isZC (coord S x i)) && has_support x A].

Local Notation " 'Z[ S , A ]" := 
  (virtual_char_pred S A) (format " ''Z[' S ,  A ]"). 

Local Notation " 'Z[ 'Irr G , A ]" := 
  (virtual_char_pred (base_irr G) A) (format "''Z[' ''Irr'  G ,  A ]"). 

Local Notation " 'Z[ 'Irr G ]" := 
  (virtual_char_pred (base_irr G) G) (format "''Z[' ''Irr'  G ]"). 


Lemma is_vcharP : forall  (f : cfun _ _),
  reflect (exists f1, exists f2, [/\ is_char G f1, is_char G f2 & f = f1 - f2])
          (f \in 'Z['Irr G]).
Proof.
move=> f; apply: (iffP andP); last first.
  case=> f1; case=> f2 [Hf1 Hf2 ->]; split.
    move: (base_irr_basis G); rewrite /is_basis /is_span.
    case/andP; move/eqP=> -> _.
    by apply: memv_sub; apply: is_char_in_cfun.
  apply/andP; split.
    apply/forallP=> x; rewrite linearD linearN /= ffunE isZC_add //.
      rewrite isZCE; apply/orP;left.
      by move: (isNatC_ncoord_char ( bi2sg x) Hf1);rewrite /ncoord  bi2sgK //=.
    rewrite ffunE isZC_opp //; rewrite isZCE; apply/orP;left;
    by move: (isNatC_ncoord_char ( bi2sg x) Hf2);rewrite /ncoord  bi2sgK //=.
  apply/forallP=> x.
  rewrite !cfunE; case:(boolP (x \in G)); first by move=> _; apply: implybT.
  move=> HxG; move/is_char_in_cfun: (Hf1);move/cfun_memP.
  move=>[H _]; rewrite (H _ HxG).
  move/is_char_in_cfun: (Hf2);move/cfun_memP; move=>[H2 _].
  by rewrite (H2 _ HxG) subr0 implybF eqxx.
case=> Hs; case/andP; move/forallP => Hc Hss.
pose f1 := \sum_(i : irr G) (if isNatC(ncoord i f) then ncoord i f else 0) 
                            *: (i : cfun _ _).
pose f2 := \sum_(i : irr G) (if isNatC(-ncoord i f) then -ncoord i f else 0) 
                            *: (i : cfun _ _).
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

Lemma is_vchar_char : forall f, is_char G f -> f \in 'Z['Irr G].
Proof.
move=> f Hf; apply/is_vcharP; exists f; exists 0; split=> //.
  by exact: is_char0.
by rewrite subr0.
Qed.

Lemma is_vchar_irr : forall theta : irr G, (theta: cfun _ _) \in 'Z['Irr G].
Proof.
by move=> theta; apply: is_vchar_char; apply: is_char_irr.
Qed.

Lemma isZC_ncoord_gvchar : forall (A : {set gT})(theta : irr G) (f : cfun _ _),
 f \in 'Z['Irr G, A] -> isZC (ncoord theta f).
Proof.
by move=> B theta f; case/andP => Hf; case/andP; move/forallP=> HH _; apply: HH.
Qed.

Lemma isZC_ncoord_vchar : forall (theta : irr G) (f : cfun _ _),
 f \in 'Z['Irr G] -> isZC (ncoord theta f).
Proof. by apply: isZC_ncoord_gvchar. Qed.

Lemma is_vchar0 : forall A,  0 \in 'Z['Irr G, A].
Proof. 
move => B;rewrite !inE /=; apply/andP; split; first by apply: mem0v.
apply/andP;split.
  by rewrite linear0; apply/forallP=> i;rewrite ffunE (isZC_nat 0).
by apply/forall_inP=> x; rewrite cfunE eqxx.
Qed.

Lemma is_vchar_in_cfun : forall f, f \in 'Z['Irr G]-> f \in 'CF(G).
Proof. 
move=> f; case/is_vcharP=> f1; case=> f2 [Hf1 Hf2 ->].
by apply: memv_sub; apply: is_char_in_cfun.
Qed.

(* to move to classfun *)
Lemma cfun_support: forall (A B: {set gT}) f, has_support f A -> 
f \in 'CF(G,B ) -> f \in 'CF(G, A).
Proof.
move=> A' B f Hss;move/cfun_memfP=> [H1 H2];apply/cfun_memfP; split=>// {H2}.
move=> x;rewrite inE negb_andb;case/orP.
  move/forallP:Hss; move/(_ x);rewrite implyNb;case/orP; first by move/eqP.
  by move ->.
by move => Hx;apply:H1;rewrite inE negb_andb;apply/orP;right.
Qed.

Lemma is_gvchar_in_cfun : forall f, f \in 'Z['Irr G, A]-> f \in 'CF(G, A).
Proof. 
move=> f;case/andP=> Hs; case/andP; move/forallP => Hc Hss.
case/andP: (base_irr_basis G) Hs. rewrite /is_span;move/eqP => -> _.
exact: cfun_support. 
Qed.

Lemma is_vchar_opp : forall f, f \in 'Z['Irr G]-> (-f) \in 'Z['Irr G].
Proof.
move=> f; case/is_vcharP=> f1; case=> f2 [Hf1 Hf2 ->].
by rewrite oppr_sub; apply/is_vcharP; exists f2; exists f1; split.
Qed.

Lemma is_vchar_add : forall f1 f2, 
  f1 \in 'Z['Irr G]-> f2  \in 'Z['Irr G]-> (f1 + f2) \in 'Z['Irr G].
Proof.
move=> f1 f2; case/is_vcharP=> f11; case=> f12 [Hf11 Hf12 ->].
case/is_vcharP=> f21; case=> f22 [Hf21 Hf22 ->].
apply/is_vcharP; exists (f11 + f21); exists (f12 + f22); split.
- by apply: is_char_add.
- by apply: is_char_add.
rewrite -!addrA; congr (_ + _).
by rewrite addrC -!addrA oppr_add [-_ + _]addrC.
Qed.

Lemma is_vchar_sub : forall f1 f2, 
   f1  \in 'Z['Irr G]  -> f2 \in 'Z['Irr G] -> (f1 - f2) \in 'Z['Irr G]. 
Proof.
by move=> f1 f2 Hf1 Hf2; apply: is_vchar_add=> //; exact: is_vchar_opp.
Qed.

Lemma is_vchar_scal : forall f n, f \in 'Z['Irr G] -> (f *+ n) \in 'Z['Irr G].
Proof.
move=> f n Hf; elim: n=> [|n Hn].
rewrite mulr0n  is_vchar0 //.
by rewrite mulrS is_vchar_add.
Qed.

Lemma is_vchar_scaln : forall f n, f \in 'Z['Irr G] -> (f *- n) \in 'Z['Irr G].
Proof.
move=> f n Hf; elim: n=> [|n Hn]; first by rewrite oppr0 is_vchar0.
by rewrite -mulNrn mulrS mulNrn is_vchar_add // is_vchar_opp.
Qed.

Lemma is_vchar_sum : forall (I : eqType) r (P : I -> bool) (F : I -> cfun _ _),
  (forall i, ((P i) && (i \in r)) -> (F i) \in 'Z['Irr G]) -> 
    (\sum_(i <- r | P i)  F i) \in 'Z['Irr G].
Proof.
move=> I r P F; elim: r=> [| a r IH HH].
  by rewrite big_nil is_vchar0.
have HF : (\sum_(i <- r | P i) F i) \in 'Z['Irr G].
  by apply: IH=> i; case/andP=> HH1 HH2; apply: HH; rewrite HH1 inE HH2 orbT.
rewrite big_cons; case: (boolP (P a))=> HP //; rewrite is_vchar_add //.
by rewrite HH // inE eqxx andbT.
Qed.

End IsVChar.


Section MoreIsVChar.

Variable gT : finGroupType.
Variable G H : {group gT}.

Local Notation " 'Z[ S , A ]" := 
  (virtual_char_pred S A) (format " ''Z[' S ,  A ]"). 

Local Notation " 'Z[ 'Irr G , A ]" := 
  (virtual_char_pred (base_irr G) A) (format "''Z[' ''Irr'  G ,  A ]"). 

Local Notation " 'Z[ 'Irr G ]" := 
  (virtual_char_pred (base_irr G) G) (format "''Z[' ''Irr'  G ]"). 

Lemma is_vchar_restrict : forall f, 
  H \subset G -> f \in 'Z['Irr G] -> ('Res[H] f)\in 'Z['Irr H].
Proof.
move=> f HsG; case/is_vcharP=> f1; case=> f2 [Hf1 Hf2 ->].
by rewrite linearD linearN is_vchar_sub // is_vchar_char //
           (is_char_restrict HsG).
Qed.

Lemma is_vchar_induced : forall chi,
   H \subset G -> chi \in 'Z['Irr H] -> ('Ind[G,H] chi) \in 'Z['Irr G].
Proof.
move=> chi HsG; case/is_vcharP=> f1; case=> f2 [Hf1 Hf2 ->].
by rewrite linearD linearN is_vchar_add ?is_vchar_opp //
           is_vchar_char // is_char_induced.
Qed.

End MoreIsVChar.
