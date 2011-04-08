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


Lemma is_vcharP : forall f : cfun _ _,
  reflect (exists f1, exists f2, [/\ is_char G f1, is_char G f2 & f = f1 - f2])
          (f \in 'Z['Irr G]).
Proof.
move=> f; apply: (iffP andP); last first.
  case=> f1; case=> f2 [Hf1 Hf2 ->]; split.
    move: (base_irr_basis G); rewrite /is_basis /is_span.
    case/andP; move/eqP=> -> _.
    by apply: memv_sub; apply: is_char_in_cfun.
  apply/andP; split.
    apply/forallP=> x.
    rewrite linearD linearN /= ffunE isZC_add //.
      rewrite isZCE; apply/orP;left.
      by move: (isNatC_ncoord_char ( bi2sg x) Hf1);rewrite /ncoord  bi2sgK //=.
    rewrite ffunE isZC_opp //; rewrite isZCE; apply/orP;left.
    by move: (isNatC_ncoord_char ( bi2sg x) Hf2);rewrite /ncoord  bi2sgK //=.
  admit.
case=> Hs; case/andP; move/forallP => Hc Hss.
pose f1 := 
  \sum_(i : irr G) (if isNatC(ncoord i f) then ncoord i f else 0) *: (i : cfun _ _).
 pose f2 := 
  \sum_(i : irr G) (if isNatC(-ncoord i f) then -ncoord i f else 0) *: (i : cfun _ _).
exists f1; exists f2; split.
- apply: is_char_sum=> i _.
  case: (boolP (isNatC _)); last by rewrite scale0r is_char0.
  by case/isNatCP=> n ->; rewrite scaler_nat is_char_scal // is_char_irr.
- apply: is_char_sum=> i _.
  case: (boolP (isNatC _)); last by rewrite scale0r is_char0.
  by case/isNatCP=> n ->; rewrite scaler_nat is_char_scal // is_char_irr.
rewrite -sumr_sub.
have Hf : f \in 'CF(G).
  admit.
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
(*
    apply: isZC_sub.
 last first.
    by apply:  memv_sub; exact: is_char_in_cfun.
  apply/forallP=> chi.
  by rewrite linearD linearN isZC_sub // isZCE isNatC_ncoord_char.
case; move/forallP; rewrite genGid => HZ Hf.
pose f1 := 
  \sum_(i : irr G) (if isNatC(ncoord i f) then ncoord i f else 0) *: (i : cfun _ _).
pose f2 := 
  \sum_(i : irr G) (if isNatC(-ncoord i f) then -ncoord i f else 0) *: (i : cfun _ _).
exists f1; exists f2; split.
- apply: is_char_sum=> i _.
  case: (boolP (isNatC _)); last by rewrite scale0r is_char0.
  by case/isNatCP=> n ->; rewrite scaler_nat is_char_scal // is_char_irr.
- apply: is_char_sum=> i _.
  case: (boolP (isNatC _)); last by rewrite scale0r is_char0.
  by case/isNatCP=> n ->; rewrite scaler_nat is_char_scal // is_char_irr.
rewrite -sumr_sub {1}(ncoord_sum Hf); apply: eq_bigr=> chi _.
have: isZC (ncoord chi f) by apply: HZ; rewrite mem_enum.
rewrite isZCE; case/orP=> HH; rewrite HH; case: (boolP (isNatC _))=> HH1.
- suff->: (ncoord chi f) = 0 by rewrite oppr0 !scale0r subrr.
  apply: leC_anti; last by apply posC_isNatC.
  by rewrite -leC_sub sub0r posC_isNatC.memv_sub
- by rewrite scale0r subr0.
- suff->: (ncoord chi f) = 0 by rewrite oppr0 !scale0r subrr.
  apply: leC_anti; last by apply posC_isNatC.
  by rewrite -leC_sub sub0r posC_isNatC.
by rewrite scale0r sub0r scaleNr opprK.*)
Qed.

Definition  is_vchar G f  :=(f \in 'Z['Irr G]).
Lemma is_vchar_char : forall f, is_char G f -> is_vchar G f.
Proof.
move=> f Hf; apply/is_vcharP; exists f; exists 0; split=> //.
  by exact: is_char0.
by rewrite subr0.
Qed.

Lemma is_vchar_irr : forall theta : irr G, is_vchar G theta.
Proof.
by move=> theta; apply: is_vchar_char; apply: is_char_irr.
Qed.

Lemma isZC_ncoord_vchar : forall (theta : irr G) (f : cfun _ _),
 is_vchar G f -> isZC (ncoord theta f).
Proof.
by move=> theta f; case/andP => Hf; case/andP; move/forallP=> HH _; apply: HH.
Qed.

Lemma is_vchar0 : is_vchar G 0.
Proof. by rewrite is_vchar_char // is_char0. Qed.

Lemma is_vchar_in_cfun : forall f,  is_vchar G f -> f \in 'CF(G).
Proof. 
move=> f; case/is_vcharP=> f1; case=> f2 [Hf1 Hf2 ->].
by apply: memv_sub; apply: is_char_in_cfun.
Qed.

Lemma is_vchar_opp : forall f, is_vchar G f -> is_vchar G (-f).
Proof.
move=> f; case/is_vcharP=> f1; case=> f2 [Hf1 Hf2 ->].
by rewrite oppr_sub; apply/is_vcharP; exists f2; exists f1; split.
Qed.

Lemma is_vchar_add : forall f1 f2, 
  is_vchar G f1 -> is_vchar G f2 -> is_vchar G (f1 + f2).
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
  is_vchar G f1 -> is_vchar G f2 -> is_vchar G (f1 - f2).
Proof.
by move=> f1 f2 Hf1 Hf2; apply: is_vchar_add=> //; exact: is_vchar_opp.
Qed.

Lemma is_vchar_scal : forall f n, is_vchar G f -> is_vchar G (f *+ n).
Proof.
move=> f n Hf; elim: n=> [|n Hn]; first by rewrite mulr0n is_vchar0.
by rewrite mulrS is_vchar_add.
Qed.

Lemma is_vchar_scaln : forall f n, is_vchar G f -> is_vchar G (f *- n).
Proof.
move=> f n Hf; elim: n=> [|n Hn]; first by rewrite oppr0 is_vchar0.
by rewrite -mulNrn mulrS mulNrn is_vchar_add // is_vchar_opp.
Qed.

Lemma is_vchar_sum : forall (I : eqType) r (P : I -> bool) (F : I -> cfun _ _),
  (forall i, ((P i) && (i \in r)) -> is_vchar G (F i)) -> 
    is_vchar G (\sum_(i <- r | P i)  F i).
Proof.
move=> I r P F; elim: r=> [| a r IH HH].
  by rewrite big_nil is_vchar0.
have HF : is_vchar G (\sum_(i <- r | P i) F i).
  by apply: IH=> i; case/andP=> HH1 HH2; apply: HH; rewrite HH1 inE HH2 orbT.
rewrite big_cons; case: (boolP (P a))=> HP //; rewrite is_vchar_add //.
by rewrite HH // inE eqxx andbT.
Qed.

End IsVChar.


Section MoreIsVChar.

Variable gT : finGroupType.
Variable G H : {group gT}.

Lemma is_vchar_restrict : forall f, 
  H \subset G -> is_vchar G f -> is_vchar H ('Res[H] f).
Proof.
move=> f HsG; case/is_vcharP=> f1; case=> f2 [Hf1 Hf2 ->].
by rewrite linearD linearN is_vchar_sub // is_vchar_char //
           (is_char_restrict HsG).
Qed.

Lemma is_vchar_induced : forall chi,
   H \subset G -> is_vchar H chi -> is_vchar G ('Ind[G,H] chi).
Proof.
move=> chi HsG; case/is_vcharP=> f1; case=> f2 [Hf1 Hf2 ->].
by rewrite linearD linearN is_vchar_add ?is_vchar_opp //
           is_vchar_char // is_char_induced.
Qed.

End MoreIsVChar.
