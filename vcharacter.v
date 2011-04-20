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

Variable (gT : finGroupType) (G : {group gT}).

Definition virtual_char_pred m (S : m.-tuple {cfun gT}) (A : {set gT}) :
  pred {cfun gT} :=
  [pred x \in span S | (forallb i, isZC (coord S x i)) && has_support x A].

Local Notation " 'Z[ S , A ]" := 
  (virtual_char_pred S A) (format " ''Z[' S ,  A ]"). 

Local Notation " 'Z[ 'Irr G , A ]" := 
  (virtual_char_pred (base_irr G) A) (format "''Z[' ''Irr'  G ,  A ]"). 

Local Notation " 'Z[ 'Irr G ]" := 
  (virtual_char_pred (base_irr G) G) (format "''Z[' ''Irr'  G ]"). 

Lemma is_vcharP : forall  (f : {cfun _}),
  reflect (exists f1, exists f2, [/\ is_char G f1, is_char G f2 & f = f1 - f2])
          (f \in 'Z['Irr G]).
Proof.
move=> f; apply: (iffP andP); last first.
  case=> f1; case=> f2 [Hf1 Hf2 ->]; split.
    move: (base_irr_basis G); rewrite /is_basis /is_span.
    case/andP; move/eqP=> -> _.
    by apply: memv_sub; apply: memc_is_char.
  apply/andP; split.
    apply/forallP=> x; rewrite linearD linearN /= ffunE isZC_add //.
      rewrite isZCE; apply/orP;left.
     by  move: (isNatC_ncoord_char (enum_val x) Hf1);rewrite /ncoord enum_valK.
    rewrite ffunE isZC_opp //; rewrite isZCE; apply/orP;left;
    by move: (isNatC_ncoord_char (enum_val x) Hf2);rewrite /ncoord  enum_valK.
  apply/forall_inP=> x XniG; rewrite !ffunE.
  move/memc_is_char:Hf1; move/support_memc; move/forall_inP.
  move/(_ _ XniG); move/eqP->.
  move/memc_is_char:Hf2; move/support_memc; move/forall_inP.
  by move/(_ _ XniG); move/eqP->; rewrite subr0.
case=> Hs; case/andP; move/forallP => Hc Hss.
pose f1 := \sum_(i : irr G) (if isNatC(ncoord i f) then ncoord i f else 0) 
                            *: (i : {cfun _}).
pose f2 := \sum_(i : irr G) (if isNatC(-ncoord i f) then -ncoord i f else 0) 
                            *: (i : {cfun _}).
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

Lemma is_vchar_irr : forall theta : irr G, (theta: {cfun _}) \in 'Z['Irr G].
Proof.
by move=> theta; apply: is_vchar_char; apply: is_char_irr.
Qed.

Lemma isZC_ncoord_vchar : forall (A : {set gT})(theta : irr G) (f : {cfun _}),
  f \in 'Z['Irr G, A] -> isZC (ncoord theta f).
Proof.
move=> B theta f; case/and3P=> _;move/forallP => HH _; apply: HH.
Qed.

Lemma isZC_coord_vchar : forall m (S : m.-tuple _) A f i, 
  f \in 'Z[S, A] -> isZC (coord S f i).
Proof. by move=> m S B i f; case/and3P => _; move/forallP. Qed.

Lemma support_vchar : forall m (S : m.-tuple _) A f,
  f \in 'Z[S, A] -> has_support f A.
Proof. by move=> m S B f; case/and3P. Qed.

Lemma span_vchar : forall m (S : m.-tuple _) A f,
  f \in 'Z[S, A] -> f \in span S.
Proof. by move=> m S B f; case/and3P. Qed.

Lemma memc_is_gvchar : forall f B, f \in 'Z['Irr G, B]-> f \in 'CF(G, B).
Proof. 
move=> f B;case/and3P=> Hspan; move/forallP => Hc Hsup.
case/andP: (base_irr_basis G) Hspan; rewrite /is_span;move/eqP => -> _ HH.
by rewrite memcE Hsup.
Qed.

Lemma memc_is_vchar : forall f, f \in 'Z['Irr G]-> f \in 'CF(G).
Proof. 
move=> f; case/is_vcharP=> f1; case=> f2 [Hf1 Hf2 ->].
by apply: memv_sub; apply: memc_is_char.
Qed.

Lemma is_vchar0 :  forall m (S : m.-tuple _) A,  0 \in 'Z[S, A].
Proof. 
move => m S B;rewrite !inE; apply/and3P;split; first by apply: mem0v.
  by apply/forallP=> i;rewrite linear0  ffunE (isZC_nat 0). 
by apply/forall_inP=> x; rewrite ffunE eqxx.
Qed.

Lemma vchar_support:  forall f A,
          f \in 'Z['Irr G, A] =  (f \in 'Z['Irr G]) && has_support f A.
Proof.
move=> f A; apply/idP/idP=>H.
  move/memc_is_gvchar: (H); rewrite memcE; case/andP=> -> HCF.
  rewrite andbT.
  case/and3P: H=> irrGaa ZGaa Aaa; apply/and3P; split=> //.
  by apply: support_memc HCF.
by case/andP:H; case/and3P=>irrGaa ZGaa Aaa Hs;apply/and3P.
Qed.

Lemma is_vchar_opp : forall m (S : m.-tuple _) A f ,
  f \in 'Z[S, A]-> (-f) \in 'Z[S, A].
Proof.
move=> m S A f;case/and3P=> Hspan; move/forallP=> HZC; move/forall_inP=> Hs.
apply/and3P;split;first by rewrite memvN.
  by apply/forallP=>i; rewrite linearN ffunE isZC_opp.
by apply/forall_inP=> x H; rewrite ffunE (eqP (Hs _ H)) oppr0.
Qed.

Lemma is_vchar_add : forall m (S : m.-tuple _) A f1 f2, 
                      f1 \in 'Z[S, A]-> f2  \in 'Z[S, A]-> (f1 + f2) \in 'Z[S, A].
Proof.
move=> m S A f1 f2.
case/and3P=> Hspan1; move/forallP=> HZC1; move/forall_inP=> Hs1.
case/and3P=> Hspan2; move/forallP=> HZC2; move/forall_inP=> Hs2.
apply/and3P;split;first by rewrite  memvD.
  by apply/forallP=>i; rewrite linearD ffunE isZC_add.
by apply/forall_inP=> x Hx;rewrite ffunE (eqP (Hs1 _ Hx)) (eqP (Hs2 _ Hx)) add0r.
Qed.

Lemma is_vchar_sub : forall m (S : m.-tuple _) A f1 f2, 
   f1  \in 'Z[S, A]  -> f2 \in 'Z[S, A] -> (f1 - f2) \in 'Z[S, A]. 
Proof.
by move=> m S A f1 f2 Hf1 Hf2; apply: is_vchar_add=> //; exact: is_vchar_opp.
Qed.

Lemma is_vchar_scal : forall m (S : m.-tuple _) A f n,
  f \in 'Z[S, A] -> (f *+ n) \in 'Z[S, A].
Proof.
move=> m S A f n Hf; elim: n=> [|n Hn].
  by rewrite mulr0n  is_vchar0.
by rewrite mulrS is_vchar_add.
Qed.

Lemma is_vchar_scaln : forall m (S : m.-tuple _) A f n,
  f \in 'Z[S, A] -> (f *- n) \in 'Z[S, A].
Proof.
move=> m S A f n Hf; elim: n=> [|n Hn]; first by rewrite oppr0 is_vchar0.
by rewrite -mulNrn mulrS mulNrn is_vchar_add // is_vchar_opp.
Qed.

Lemma is_vchar_sum : forall m (S : m.-tuple _) A (I : eqType) r (P : I -> bool) 
                              (F : I -> {cfun _}),
  (forall i, ((P i) && (i \in r)) -> (F i) \in 'Z[S, A]) -> 
    (\sum_(i <- r | P i)  F i) \in 'Z[S, A].
Proof.
move=> m S A I r P F; elim: r=> [| a r IH HH].
  by rewrite big_nil is_vchar0.
have HF : (\sum_(i <- r | P i) F i) \in 'Z[S, A].
  by apply: IH=> i; case/andP=> HH1 HH2; apply: HH; rewrite HH1 inE HH2 orbT.
rewrite big_cons; case: (boolP (P a))=> HP //; rewrite is_vchar_add //.
by rewrite HH // inE eqxx andbT.
Qed.

Lemma is_vchar_mul : forall f g A, 
                      f \in 'Z['Irr G, A]-> g  \in 'Z['Irr G, A]-> 
                        (f * g) \in 'Z['Irr G, A].
Proof.
move=>  f g A; rewrite vchar_support; case/andP=> H1f H2f.
rewrite vchar_support; case/andP=> H1g H2g.
rewrite vchar_support; apply/andP; split; last first.
  apply/forall_inP=> x XniA; rewrite ffunE.
  by move/forall_inP: H2f; move/(_ _ XniA); move/eqP->; rewrite mul0r.
case/is_vcharP:H1f=>f1; case=> f2 [Hf1 Hf2 ->].
case/is_vcharP:H1g=>g1; case=> g2 [Hg1 Hg2 ->].
apply/is_vcharP;exists ((f1 * g1) + (f2 * g2));exists ((f1 * g2 ) + (f2 * g1)).
split;rewrite ?(is_char_add, is_char_mul)//.
rewrite !mulr_addl !mulr_subr -!addrA; congr  (_ + _).
rewrite addrC -!addrA !mulNr opprK addrC -!addrA;congr (_ + _). 
by rewrite oppr_add.
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
