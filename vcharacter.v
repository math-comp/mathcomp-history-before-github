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
  rewrite !cfunE; case: (boolP (_ \in G)); first by move=> _; apply: implybT.
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

Lemma isZC_ncoord_vchar : forall (A : {set gT})(theta : irr G) (f : cfun _ _),
 f \in 'Z['Irr G, A] -> isZC (ncoord theta f).
Proof.
move=> B theta f; case/and3P=> _;move/forallP => HH _; apply: HH.
Qed.

Lemma isZC_coord_vchar : forall S A f i, f \in 'Z[S, A] -> isZC (coord S f i).
Proof. by move=> S B i f; case/and3P => _; move/forallP. Qed.

Lemma support_vchar : forall S A f, f \in 'Z[S, A] -> has_support f A.
Proof. by move=> S B f; case/and3P. Qed.

Lemma inspan_vchar : forall S A f, f \in 'Z[S, A] -> f \in span S.
Proof. by move=> S B f; case/and3P. Qed.

Lemma is_gvchar_in_cfun : forall f B, f \in 'Z['Irr G, B]-> f \in 'CF(G, B).
Proof. 
move=> f B;case/and3P=> Hspan; move/forallP => Hc Hsup.
case/andP: (base_irr_basis G) Hspan; rewrite /is_span;move/eqP => -> _.
by apply: cfun_supportsAB.
Qed.

(* Lemma isZC_ncoord_gvchar : forall (A : {set gT}) (f : cfun _ _),
 f \in 'Z['Irr G, A] = (forallb theta : irr G, isZC (ncoord theta f)) && (f \in 'CF(G, A)).
Proof.
move=> B f; apply/idP/andP.
  move=>H;split; last by apply: is_gvchar_in_cfun.
  by apply/forallP=> theta; rewrite (isZC_ncoord_vchar _ H).
move=> [Hf H]; apply/and3P;split; last by apply:(cfun_support H).
  case/andP: (base_irr_basis G); rewrite /is_basis /is_span; move/eqP => -> _.
  by apply: (cfun_support_cfun H).
by apply/forallP=> i;move/forallP:Hf;move/(_ (bi2sg i)); rewrite /ncoord  bi2sgK.
Qed.*)


Lemma is_vchar_in_cfun : forall f, f \in 'Z['Irr G]-> f \in 'CF(G).
Proof. 
move=> f; case/is_vcharP=> f1; case=> f2 [Hf1 Hf2 ->].
by apply: memv_sub; apply: is_char_in_cfun.
Qed.

Lemma is_vchar0:  forall S A,  0 \in 'Z[S, A].
Proof. 
move => S B;rewrite !inE; apply/and3P;split; first by apply: mem0v.
  by apply/forallP=> i;rewrite linear0  ffunE (isZC_nat 0). 
by apply/forall_inP=> x; rewrite cfunE eqxx.
Qed.

(* ! supprimer cfun_memfP *)
Lemma vchar_support:  forall f,
          f \in 'Z['Irr G, A] =  (f \in 'Z['Irr G]) && has_support f A.
Proof.
move=> f; apply/idP/idP=> H.
  move/is_gvchar_in_cfun: (H) => HCF.
  rewrite (cfun_support HCF) andbT.
  case/and3P: H=> irrGaa ZGaa Aaa.
  move/cfun_memfP: HCF=> [H _].
  apply/and3P; split=> //; apply/forall_inP=> x Hx.
  move: (H x);rewrite inE; rewrite negb_andb.
  case: (boolP (_ \in G)) =>//.
  rewrite /= orbT=> _ Hf0.
  by move: Hx ; rewrite Hf0 //  eqxx //.
case/andP:H => H Hs;move/is_vchar_in_cfun: (H) => H3.
case/and3P: H=> irrGaa ZGaa Aaa.
apply/and3P; split=> //; apply/forall_inP=> x.
Qed.

Lemma is_vchar_opp : forall S A f , f \in 'Z[S, A]-> (-f) \in 'Z[S, A].
Proof.
move=> S A' f;case/and3P=> Hspan; move/forallP=> HZC; move/forall_inP=> Hs.
apply/and3P;split;first by rewrite memvN.
  by apply/forallP=>i; rewrite linearN ffunE isZC_opp.
apply/forall_inP=> x H;  apply:Hs;apply/negP=> H1;apply:(negP H). 
by rewrite cfunE (eqP H1) oppr0.
Qed.

Lemma is_vchar_add : forall S A f1 f2, 
                      f1 \in 'Z[S, A]-> f2  \in 'Z[S, A]-> (f1 + f2) \in 'Z[S, A].
Proof.
move=> S A' f1 f2.
case/and3P=> Hspan1; move/forallP=> HZC1; move/contra_support=> Hs1.
case/and3P=> Hspan2; move/forallP=> HZC2; move/contra_support=> Hs2.
apply/and3P;split;first by rewrite  memvD.
  by apply/forallP=>i; rewrite linearD ffunE isZC_add.
by apply/contra_support=> x => Hx;rewrite cfunE (Hs1 _ Hx) (Hs2 _ Hx) add0r.
Qed.

Lemma is_vchar_sub : forall S A f1 f2, 
   f1  \in 'Z[S, A]  -> f2 \in 'Z[S, A] -> (f1 - f2) \in 'Z[S, A]. 
Proof.
by move=> S A' f1 f2 Hf1 Hf2; apply: is_vchar_add=> //; exact: is_vchar_opp.
Qed.

Lemma is_vchar_scal : forall S A f n, f \in 'Z[S, A] -> (f *+ n) \in 'Z[S, A].
Proof.
move=> S A' f n Hf; elim: n=> [|n Hn].
  by rewrite mulr0n  is_vchar0.
by rewrite mulrS is_vchar_add.
Qed.

Lemma is_vchar_scaln : forall S A f n, f \in 'Z[S, A] -> (f *- n) \in 'Z[S, A].
Proof.
move=> S A' f n Hf; elim: n=> [|n Hn]; first by rewrite oppr0 is_vchar0.
by rewrite -mulNrn mulrS mulNrn is_vchar_add // is_vchar_opp.
Qed.

Lemma is_vchar_sum : forall S A (I : eqType) r (P : I -> bool) (F : I -> cfun _ _),
  (forall i, ((P i) && (i \in r)) -> (F i) \in 'Z[S, A]) -> 
    (\sum_(i <- r | P i)  F i) \in 'Z[S, A].
Proof.
move=> S A' I r P F; elim: r=> [| a r IH HH].
  by rewrite big_nil is_vchar0.
have HF : (\sum_(i <- r | P i) F i) \in 'Z[S, A'].
  by apply: IH=> i; case/andP=> HH1 HH2; apply: HH; rewrite HH1 inE HH2 orbT.
rewrite big_cons; case: (boolP (P a))=> HP //; rewrite is_vchar_add //.
by rewrite HH // inE eqxx andbT.
Qed.

(*
Lemma is_vchar_mul : forall S A f1 f2, 
                      f1 \in 'Z[S, A]-> f2  \in 'Z[S, A]-> (f1 * f2) \in 'Z[S, A].
Proof.
admit.
Qed.*)

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
