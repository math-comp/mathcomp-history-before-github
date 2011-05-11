(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient finalg action.
Require Import zmodp commutator cyclic center pgroup sylow.
Require Import vector algC matrix.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(**************************************************************************)
(*                                                                        *)
(* This file contains the basic notions of class functions                *)
(*                                                                        *)
(*  {cfun gT} : the type of functions from gT to algC                     *)
(*                                                                        *)
(*  (f ^* )%CH  : the conjugate function                                  *)
(*                                                                        *)
(*  'CF(G,A)    : the vector space of class functions of G with support   *)
(*                                                                        *)
(*  'CF(G)      : the vector space of class functions of G over algC      *)
(*                                                                        *)
(*  '[f,g]_G : the inner product of f g such that irr G is                *)
(*                     an orthonormal basis of 'CF(G)                     *)
(*                                                                        *)
(*   (f/N)%CH  :  if f \in 'CF(G) and N <| G, the corresponding class     *)
(*                function on the cosets of N                             *)
(*                                                                        *)
(*  (f^())%CH  : if f \in 'CF(G/N), the corresponding class function      *)
(*               on G                                                     *)
(*                                                                        *)
(* 'Res[H] f: restrict the function to H, i.e f x = 0 for x \notin H      *)
(*                                                                        *)
(* 'Ind[G,H] f: the induced function from H to G                          *)
(*                                                                        *)
(*                                                                        *)
(**************************************************************************)

Section AlgC.

Variable (gT : finGroupType).

Lemma neq0GC : forall  (G : {group gT}), (#|G|)%:R != 0 :> algC.
Proof. by move=> G; rewrite -neq0N_neqC (cardD1 1%g) group1. Qed.

Lemma sposGC : forall (G : {group gT}), 0 < #|G|%:R.
Proof. by move=> G; rewrite /ltC neq0GC // posC_nat. Qed.

Implicit Type G : {group gT}.
Import GroupScope GRing.Theory.

Lemma pGroupG : forall G, [char algC]^'.-group G.
Proof.
by move=> G; apply: sub_pgroup (pgroup_pi G)=> i _; rewrite inE /= Cchar.
Qed.

End AlgC.

Delimit Scope character_scope with CH.

Definition cfun (gT : finGroupType) of (phant gT) := {ffun gT -> algC}.

Notation "{ 'cfun' T }" := (cfun (Phant T)) (format "{ 'cfun'  T }").

Section ClassFun. 

Variable (gT : finGroupType) (G : {group gT}).

Canonical Structure cfun_eqType := [eqType of {cfun gT}].
Canonical Structure cfun_choiceType := [eqType of {cfun gT}].
Canonical Structure cfun_zmodType := [zmodType of {cfun gT}].
Canonical Structure cfun_ringType := 
  Eval hnf in RingType {cfun gT} (@ffun_ringMixin gT algC 1%g).
Canonical Structure cfun_lmodType := 
  Eval hnf in LmodType algC {cfun gT} (
                 @ffun_lmodMixin algC gT (GRing.regular_lmodType algC)).

(* GG: this should either go in finfun, or be replaced with *)
(* pffun_on 0 A predT (val f) *)
Definition has_support (f : {cfun gT}) (A : {set gT}) :=
  forallb x: gT, (x \notin A) ==> (f x == 0).

Definition base_cfun (G A : {set gT}) : _.-tuple {cfun gT} :=
  tseq (filter
    (has_support^~ A)
    (map (fun i : 'I_#|classes G|  => 
        [ffun x => (x \in (enum_val i))%:R])
      (enum 'I_#|classes G|))).

Lemma base_cfun_subset : forall (A : {set gT}),
 G \subset A -> 
 base_cfun G A = (map (fun i : 'I_#|classes G|  => 
                   [ffun x => (x \in (enum_val i))%:R])
                   (enum 'I_#|classes G|)) :> seq _.
Proof.
move=> A GsA; apply/all_filterP.
apply/allP=> /= f; case/mapP=> i Hi ->.
apply/forall_inP=> x XiA; rewrite ffunE.
case: (boolP (_ \in _))=> // XinE; case/negP: XiA.
move/subsetP: GsA; apply.
suff: (enum_val i) \subset G by move/subsetP; apply.
case/imsetP: (enum_valP i)=> g GiG ->.
by apply: class_subG.
Qed.
 
Canonical Structure cfunVectType := 
 (@VectorType.pack algC _ {cfun gT} _  _ _ _ idfun
  (@ffunVectMixin algC (regVectType algC) gT)
  idfun).

Definition class_fun G  A := span (base_cfun G A).
Local Notation "'CF( G , A )" := (class_fun G A)
  (format "''CF(' G ,  A )").
Local Notation "'CF( G )" := (class_fun G G)
  (format "''CF(' G )").

(* Definition 
   forall x, x \notin A -> f x = 0 (ajouter A \subset G) 
   forall x y, y \in G -> f (x ^ y) = f x)
 *)
Lemma cfun_memfP : forall (A : {set gT}) (f : {cfun gT}),
  reflect 
    [/\ forall x, x \notin (A :&: G) -> f x = 0
      & forall x y, y \in G -> f (x ^ y) = f x]
    (f \in 'CF(G, A)).
Proof.
move=> A f; pose bGA := base_cfun G A.
apply: (iffP idP)=> [|[Hg Hc]].
  move/coord_span->; split=> [x XniAG|x y YiG].
    rewrite sum_ffunE ffunE; apply: big1=> i _; rewrite ffunE.
    have: bGA`_i \in bGA by apply: mem_nth.
    rewrite mem_filter; case/andP=> Hs.
    move: XniAG; rewrite inE negb_andb; case/orP=> [XniA|XniG].
      move/forall_inP: Hs; move/(_ x XniA).
      by move/eqP->; rewrite scaler0.
    case/mapP=> j Hj ->; rewrite !ffunE.
    have [y Gy ->] := imsetP (enum_valP j).
    move/subsetP: (class_subG Gy (subxx _)); move/(_ x); move/contra.
    by move/(_ XniG); case: (_ \in _)=> //; rewrite scaler0.
  apply/eqP; rewrite -subr_eq0; apply/eqP.
  rewrite !sum_ffunE !ffunE -sumr_sub; apply: big1=> i _.
  set u := coord _ _ _; rewrite !ffunE.
  have: bGA`_i \in bGA by apply: mem_nth.
  rewrite mem_filter; case/andP=> Hs.
  case/mapP=> j Hj ->; rewrite !ffunE.
  have [z Gz ->] := imsetP (enum_valP j).
  by rewrite (class_transl _ (memJ_class _ _)) // subrr.
suff<-: \sum_(C \in (classes G)) 
           (f (repr C)) *: ([ffun x : gT => (x \in C)%:R] : {cfun gT}) = f.
  apply: memv_suml=> i Hi.
  case: (boolP (f (repr i) == 0))=> [|Hr].
    by move/eqP->; rewrite scale0r mem0v.
  apply: memvZl; apply: memv_span.
  rewrite mem_filter; apply/andP; split.
    apply/forall_inP=> x XniA; rewrite ffunE.
    case: (boolP (x \in i))=> //= XiI; case/eqP: Hr.
    case/imsetP: Hi XiI => g GiG ->; case/imsetP=> h HiG Hx.
    case: (repr_class G g)=> h1 H1iG ->.
    by rewrite Hc // -(Hc _ _ HiG) // -Hx Hg // inE (negPf XniA).
  by apply/mapP; exists (enum_rank_in (classes1 G) i);  
      [rewrite mem_enum | rewrite enum_rankK_in].
apply/ffunP=> g; rewrite sum_ffunE ffunE.
case GiG: (g \in G); last first.
  rewrite Hg ?(inE,GiG,andbF) //; apply: big1=> i Hi; rewrite !ffunE.
  have [x Gx ->] := imsetP Hi.
  case Hgx: (_ \in _); last by rewrite scaler0.
  move/subsetP: (class_subG Gx (subxx G)) GiG.
  by move/(_ g (idP Hgx))=> ->.
rewrite (bigD1 (g ^: G : set_of_finType _)) /=; last by apply/imsetP; exists g.
rewrite !ffunE big1.
  rewrite class_refl.
  by case: (repr_class G g)=> x Hx ->; rewrite Hc // addr0; exact: mulr1.
move=> i; case/andP; case/imsetP=> y Hy -> Hz.
rewrite !ffunE; case E1: (_ \in _); last by rewrite scaler0.
by case/negP: Hz; rewrite eq_sym; apply/eqP; apply: class_transr.
Qed.

Lemma cfun_memP : forall (f : {cfun gT}),
  reflect 
    ((forall x, x \notin G -> f x = 0) /\
        (forall x y, y \in G -> f (x ^ y) = f x))
    (f \in 'CF(G)).
Proof. by move=> f; apply: (iffP (cfun_memfP G f)); rewrite setIid. Qed.

Lemma cfunS0 : forall A (f : {cfun gT}) x, f \in 'CF(G,A) -> x \notin A -> f x = 0.
Proof. 
move=> A f x; case/cfun_memfP=> HH _ XniA; apply: HH.
by rewrite inE (negPf XniA).
Qed.

Lemma cfun0 : forall (f : {cfun gT}) x, f \in 'CF(G) -> x \notin G -> f x = 0.
Proof. exact: cfunS0. Qed.

Lemma cfunJ : forall A (f : {cfun gT}) x y, 
   f \in 'CF(G,A) -> y \in G -> f (x ^ y) = f x.
Proof. by move=> A f x y; case/cfun_memfP=> _ HH; exact: HH. Qed.

Lemma cfun_sum : forall (F : gT -> algC),
  (forall g h, g \in G -> h \in G -> F (g^h) = F g) ->
  \sum_(g \in G) F g = \sum_(C \in classes G) #|C|%:R * (F (repr C)).
Proof.
move=> F HF.
rewrite {1}(partition_big _  _ ((@mem_classes gT)^~ G)) /=.
apply: eq_bigr=> cl Hcl.
rewrite (eq_bigr (fun _ => F (repr cl))); last first.
  move=> i1; case/andP=> Hi1; move/eqP=> <-.
  by case: (repr_class G i1)=> z Hz ->; rewrite HF.
rewrite -sum1_card natr_sum -!mulr_suml.
apply: eq_big=> [i1|i1]; last by rewrite mul1r.
case/imsetP: Hcl=> z Hz ->; apply/idP/idP=>[|Hi].
  by case/andP=> Hi; move/eqP<-; exact: class_refl.
move/subsetP: (class_subG Hz (subxx _)); move/(_ _ Hi)->.
by apply/eqP; apply: class_transr.
Qed.

Lemma cfun_free : forall A, free (base_cfun G A).
Proof.
move=> A; apply: free_filter.
apply/freeP=> s S0 i.
have Hi: (i < #|classes G|)%N. 
  by case: i=> /= m; rewrite card_ord.
move/ffunP: S0; move/(_ (repr (enum_val (Ordinal Hi)))).
rewrite sum_ffunE !ffunE (bigD1 i) //= big1.
 rewrite !ffunE (nth_map (Ordinal Hi)) // ?ffunE; last first.
   by rewrite -cardE.
 rewrite (nth_ord_enum  _ (Ordinal Hi)).
 have [y Gy ->] := imsetP (enum_valP (Ordinal Hi)).
 case: (repr_class G y)=> x Hx ->.
 by rewrite memJ_class // addr0 => <-; apply: sym_equal; exact: mulr1.
move=> j Dij.
rewrite (nth_map (Ordinal Hi)) ?ffunE; last by rewrite -cardE.
have Hj: (j < #|classes G|)%N by rewrite -{6}[#|classes G|]card_ord.
rewrite (nth_ord_enum  _ (Ordinal Hj))=> /=.
move: (@enum_val_inj _  _ (Ordinal Hj) (Ordinal Hi)).
have [y Gy ->] := imsetP (enum_valP (Ordinal Hi)).
have [z Gz ->] := imsetP (enum_valP (Ordinal Hj)).
case: (repr_class G y)=> t Ht -> Heq.
case Et: (_ \in _); last by  exact: mulr0.
suff: z ^: G = y ^: G by move/Heq; move/val_eqP=> HH; case/negP: Dij.
apply: class_transr.
by rewrite class_sym (class_trans _ Et) // -{1}[y]conjg1 
           classGidl // conjg1 class_refl .
Qed.

Lemma dim_cfun : \dim ('CF(G)) = #|classes G|.
Proof.
move: (cfun_free G); rewrite /free; move/eqP->.
by rewrite base_cfun_subset ?subxx // size_map -cardE card_ord.
Qed.

(* cfun and support *)

Lemma support_subset : forall (A B: {set gT}) f, 
       has_support f A -> A \subset B -> has_support f B.
Proof.
move=> A B f; move/forall_inP=> Hss AsB.
apply/forall_inP=> x Hx; apply: Hss.
move: Hx; apply: contra; exact: (subsetP AsB).
Qed.

Lemma support_memc : forall f B , f \in 'CF( G ,B) -> has_support f B.
Proof.
move=> f B;move/cfun_memfP=> [H1 _].
by apply/forall_inP=> x XniA; rewrite H1 // inE (negPf XniA).
Qed.

Lemma memc_subset : forall (A B: {set gT}) f,
 B \subset A -> f \in 'CF(G, B) -> f \in 'CF(G, A).
Proof.
move=> A B f Hss; case/cfun_memfP=> H1 H2; apply/cfun_memfP.
split=> {H2}// x XniAG; apply: H1.
move: XniAG; apply: contra; rewrite !inE; case/andP.
by move/(subsetP Hss)=> ->.
Qed.

Lemma memcW : forall f A , f \in 'CF(G, A) -> f \in 'CF(G).
Proof.
move=> f B;move/cfun_memfP=> [H1 H2];apply/cfun_memP;split=> //.
by move=> x XniG; apply: H1; rewrite inE (negPf XniG) andbF.
Qed.

Lemma memcE : forall A f, 
  f \in 'CF(G, A) = (has_support f A) && (f \in 'CF(G)).
Proof.
move=> A f; apply/cfun_memfP/andP=> [[Hs Hj]|[Hs Hc]]; split.
- by apply/forall_inP=> x XniA; rewrite Hs // inE (negPf XniA).
- by apply/cfun_memP; split=> // x XniA; rewrite Hs // inE (negPf XniA) andbF.
- move=> x; rewrite inE negb_andb; case/orP=> HH; last by apply: cfun0.
  by apply/eqP; move/forall_inP: Hs; apply.
by case/cfun_memP: Hc.
Qed.

End ClassFun.

Notation "'CF( G , A )" := (class_fun G A)
  (format "''CF(' G ,  A )").
Notation "'CF( G )" := (class_fun G G)
  (format "''CF(' G )").

Definition cfun_conjC (gT: finGroupType) (f : {cfun gT}) : {cfun gT} :=
  [ffun h => (f h)^*].

Notation "f ^*" := (cfun_conjC f) : character_scope.

Lemma cfun_conjCE : forall (gT : finGroupType) (f : {cfun gT}) g, 
  (f^*)%CH g = (f g)^*.
Proof. by move=> gT f g; rewrite ffunE. Qed.

Lemma cfun_conjCK : forall (gT : finGroupType), involutive (@cfun_conjC gT).
Proof. by move=> gT f; apply/ffunP=> g; rewrite !ffunE conjCK. Qed.

Section Restrict.

Variable (gT : finGroupType).

Definition crestrict (G : {set gT}) (f : {cfun gT}) : {cfun gT} :=
    [ffun g : gT => (g \in G)%:R * (f g)].

Local Notation "''Res[' G ]  f " := (crestrict G f) (at level 24).

Lemma crestrictE : forall (G : {set gT}) f, {in G, 'Res[G] f =1 f}.
Proof. by move=> G f g H; rewrite ffunE H mul1r. Qed.
 
Lemma memc_restrict : forall (f : {cfun gT}) (G H : {group gT}), 
  H \subset G -> f \in 'CF(G) -> 'Res[H] f \in 'CF(H).
Proof.
move=> f G H Hsub fC; apply/cfun_memP; split.
  by move=> g; rewrite ffunE; case: (_ \in _)=> //; rewrite mul0r.
move=> g h hIn; rewrite !ffunE.
by rewrite (cfunJ _ fC) ?(subsetP Hsub) // (groupJr _ hIn).
Qed.

Lemma crestrict_is_linear : forall (G : {group gT}), linear (crestrict G).
Proof.
move=> G c f1 f2; apply/ffunP=> g.
by rewrite !ffunE mulr_addr mulrCA.
Qed.

Canonical Structure crestrit_linear G :=
  Linear (crestrict_is_linear G).

Lemma crestrict_subset : 
  forall (G  H : {set gT}) (f : {cfun gT}),
  H \subset G -> 'Res[H] ('Res[G] f) = 'Res[H] f.
Proof.
move=> G H f HsG; apply/ffunP=> g.
by rewrite !ffunE; case: (boolP (_ \in _))=> [HH|]; 
   rewrite ?mul0r // (subsetP HsG) // !mul1r.
Qed.

End Restrict.

Notation "''Res[' G ]  f " := (crestrict G f) (at level 24).

Section InnerProduct.

Variable (gT : finGroupType) (G : {group gT}).

Let card_neq0 : #|G|%:R^-1 != 0 :> algC.
Proof. by rewrite invr_eq0 neq0GC. Qed.

Definition inner_prod (G : {set gT}) (f g : {cfun gT}) :=
  #|G|%:R^-1 * \sum_(i \in G) f i * (g i)^*.

Local Notation "'[ u , v ]_ G":=  (inner_prod G u v) (at level 10,
  format "'[hv' ''[' u ,  '/' v ]_ G ']'").

Lemma inner_prodE: forall (f g : {cfun gT}),
  '[f,g]_G = #|G|%:R^-1 * \sum_(i \in G) f i * (g i)^*.
Proof. by []. Qed.

Let card_conj : (#|G|%:R^-1)^* = #|G|%:R^-1.
Proof. by rewrite posC_conjK // posC_inv posC_nat. Qed.

Lemma inner_conj : forall f g, '[f, g]_G = ('[g, f]_G)^*.
Proof.
move=> f g; rewrite /inner_prod rmorphM card_conj.
congr (_ * _); rewrite rmorph_sum; apply: eq_bigr=> i _.
by rewrite rmorphM conjCK mulrC.
Qed.
 
Lemma posC_inner_prod : forall f, 0 <= '[f, f]_G.
Proof. 
move=> f; apply: posC_mul; first by rewrite posC_inv posC_nat.
by rewrite posC_sum // => i _; rewrite /leC subr0 repC_pconj.
Qed.

Lemma inner_prod0l : forall f, '[0, f]_G = 0.
Proof.
move=> f.
rewrite inner_prodE big1 ?mulr0 // => i.
by rewrite ffunE mul0r.
Qed.

Lemma inner_prod0r : forall f, '[f, 0]_G = 0.
Proof.
move=> f.
rewrite inner_prodE big1 ?mulr0 // => i.
by rewrite ffunE conjC0 mulr0.
Qed.

Lemma inner_prod0 : forall f : {cfun gT}, 
  f \in 'CF(G) -> ('[f, f]_G == 0) = (f == 0).
Proof.
rewrite /=.
move=> f Hf; apply/eqP/eqP=> Hp; last first.
  by rewrite Hp /inner_prod big1 ?mulr0 // => i _; rewrite !ffunE mul0r.
apply/ffunP=> g; rewrite ffunE.
case: (boolP (g \in G))=> Hin; last by rewrite (cfun0 Hf).
suff: f g * (f g)^* == 0.
  by rewrite mulf_eq0; case/orP; [move/eqP|rewrite conjC_eq0;move/eqP].
move: Hp; move/eqP; rewrite /inner_prod mulf_eq0; case/orP=> [|Hp].
  by rewrite (negPf card_neq0).
apply/eqP; apply: (posC_sum_eq0 _ (eqP Hp))=> //.
 by move=>*; rewrite -sqrtC_pos; exact: posC_norm.
by rewrite /index_enum -enumT mem_enum.
Qed.

Definition inner_prodb f := (@inner_prod G)^~ f.

Lemma inner_prodbE : forall f g, inner_prodb f g = inner_prod G g f.
Proof. by []. Qed.

Lemma inner_prodb_is_linear : forall f, linear (inner_prodb f : _ -> algC^o).
Proof.
move=> f k g1 g2.
rewrite /inner_prodb /inner_prod.
rewrite {1}scaler_mulr -{1}scaler_addr; congr (_ * _).
rewrite {1}scaler_sumr /= -{1}big_split /=; apply: eq_bigr=> i _.
by rewrite scaler_mull -mulr_addl !ffunE.
Qed.

Canonical Structure inner_prodb_linear f :=
  Linear (inner_prodb_is_linear f).

Lemma inner_prod_is_additive : forall f, additive (inner_prod G f).
Proof.
move=> f g1 g2.
rewrite /inner_prod /inner_prod.
rewrite -mulr_subr; congr (_ * _).
rewrite -sumr_sub; apply: eq_bigr=> i _.
by rewrite !ffunE rmorph_sub // mulr_subr.
Qed.

Canonical Structure inner_prod_additive f := 
  Additive (inner_prod_is_additive f).

Lemma inner_prodZ : forall k (f g : {cfun gT}), '[f, k *: g]_G = k^* * '[f, g]_G.
Proof.
move=> k f g; rewrite /inner_prod.
rewrite mulrCA; congr (_ * _).
rewrite -mulr_sumr; apply: eq_bigr=> i _.
by rewrite !ffunE rmorphM mulrCA.
Qed.

Lemma cfun_conjC_inner : forall f1 f2 : {cfun gT},
 ('[f1^*, f2^*]_G)%CH = ('[f1, f2]_G)^*.
Proof.
move=> f1 f2; rewrite !inner_prodE rmorphM conjC_inv conjC_nat.
congr (_ * _); rewrite (big_morph _ (rmorphD conjC) conjC0); apply: eq_bigr.
by move=> g GiG; rewrite !ffunE rmorphM.
Qed.

End InnerProduct.

Notation "'[ u , v ]_ G":=  (inner_prod G u v) (at level 10,
  format "'[hv' ''[' u ,  '/' v ]_ G ']'").

Section Coset.

Variable (gT : finGroupType).

Implicit Type G : {group gT}.

Definition qfun_of_cfun (N: {set gT}) (f : {cfun gT}) :=
  [ffun x : coset_of N => f (repr x)].

Local Notation "f '/' N" := (qfun_of_cfun N f) : character_scope.

Definition cfun_of_qfun (N: {set gT}) (f : {cfun (coset_of N)}) : {cfun gT} :=
  [ffun x : gT => (x \in 'N(N))%:R * f (coset N x)].

Local Notation " f '^()'" := (cfun_of_qfun f) (at level 2) : character_scope.

Lemma cfunqE : forall (N : {group gT}) f x,
 x \in 'N(N) -> (f ^())%CH x = f (coset N x).
Proof. by move=> N f x InG; rewrite !ffunE InG // mul1r. Qed.

End Coset.

Notation "f '/' N" := (qfun_of_cfun N f) : character_scope.
Notation " f '^()'" := (cfun_of_qfun f) (at level 2) : character_scope.


Section Induced.

Variable (gT : finGroupType).

Definition cinduced  (G H : {set gT}) (f : {cfun gT}) : {cfun gT} :=
 [ffun g =>  #|H|%:R^-1 * \sum_(c | c \in G) f (g ^ c)].

Local Notation "'Ind[ G , H ] f" := (cinduced G H f) (at level 24).

Variable (G H : {group gT}).

Lemma memc_induced : forall (f : {cfun gT}),
  H \subset G -> f \in 'CF(H) -> 'Ind[G,H] f \in 'CF(G).
Proof.
move=> f HsG Hf; apply/cfun_memP; split=> [g Hg|g h HiG].
  rewrite !ffunE big1 ?mulr0 // => h HiG.
  rewrite (cfun0 Hf) //.
  apply/negP; move/(subsetP HsG)=> GHiH; case/negP: Hg.
  by rewrite -[g]conjg1 -[1%g](mulgV h) conjgM groupJ // groupV.
rewrite !ffunE; congr (_ * _).
rewrite (reindex (fun x => h^-1 * x)%g) //=; last first.
  by exists (mulg h)=> l; rewrite mulgA (mulgV,mulVg) mul1g.
apply: eq_big=> [l|l _]; first by rewrite groupMl // groupV.
by rewrite -conjgM mulgA mulgV mul1g.
Qed.

Lemma has_support_induced : forall f : {cfun gT},
  f \in 'CF(H) -> H <| G -> has_support ('Ind[G,H] f) H.
Proof.
move=> f Cf HnG; apply/forall_inP=> h HniH.
rewrite ffunE big1 ?mulr0 // => g GiG.
by rewrite (cfun0 Cf) // memJ_norm // (subsetP (normal_norm HnG)).
Qed.
 
Lemma cinduced1 : forall f, 
  H \subset G -> ('Ind[G, H] f) 1%g = #|G : H|%:R * f 1%g.
Proof.
move=> f HsG; rewrite ffunE (eq_bigr (fun _ => f 1%g)).
  rewrite sumr_const -[(f _) *+ _]mulr_natl mulrA -(LaGrange HsG).
  by rewrite natr_mul mulrA mulVf ?mul1r // neq0GC.
by move=> i; rewrite conj1g.
Qed.

Lemma cinduced_is_linear : linear (cinduced G H).
Proof.
move=> c f1 f2; apply/ffunP=> g.
rewrite !ffunE [_ *: (_ * _)]mulrCA -mulr_addr.
rewrite -[c * _]mulr_sumr -big_split; congr (_ * _).
by apply: eq_bigr=> h HiG; rewrite !ffunE.
Qed.

Canonical Structure cinduced_linear :=
  Linear cinduced_is_linear.

(* Isaacs' 5.2 *)
Lemma frobenius_reciprocity : 
  forall f1 f2, H \subset G -> f1 \in 'CF(H) -> f2 \in 'CF(G)->
   '[f1, 'Res[H] f2]_H = '['Ind[G, H] f1, f2]_G.
Proof.
move=> f1 f2 HsG F1iC F2iC.
apply: sym_equal; rewrite !inner_prodE.
pose f3 i :=  #|H|%:R^-1 * \sum_(g \in G) f1 (i ^g) * (f2 i)^*.
rewrite (eq_bigr f3) =>[/=|g GiG]; rewrite {}/f3; last first.
  by rewrite ffunE -mulrA -mulr_suml.
rewrite mulr_sumr exchange_big /=.
pose f3 i :=  \sum_(g \in G) f1 (g ^ i) * (f2 (g ^ i))^*.
rewrite (eq_bigr f3) =>[/=|g GiG]; rewrite {}/f3; last first.
  by apply: eq_bigr=> h HiG; rewrite (cfunJ _ F2iC).
rewrite  pair_big /= .
rewrite (reindex (fun p => (p.1,p.2^(p.1^-1))%g)) /=; last first.
  by exists (fun p => (p.1,p.2^(p.1))%g)=> [] [g h];
     rewrite -conjgM ?(mulgV, mulVg,conjg1) //=.
rewrite (eq_bigl (fun j => (j.1 \in G) && (j.2 \in G))); last first.
  move=> [g h]; case E1: (g \in G)=> //; move/idP: E1 => E1.
  by rewrite groupMl !(groupMr,groupV).
rewrite (eq_bigr (fun i =>  f1 i.2 * (f2 i.2)^*)); last first.
  by move=> [g h]; rewrite -conjgM ?(mulgV, mulVg,conjg1).
rewrite -(pair_big (fun g => g \in G) (fun g => g \in G)
                 (fun i j =>  f1 j * (f2 j)^*)) /=.
rewrite sumr_const (bigID (fun g => g \notin H)) big1 //= ?add0r; last first.
  by move=> g; case/andP=> GiG GniH; rewrite (cfun0 F1iC) ?mul0r.
set u := _%:R; set v := _%:R; rewrite -mulr_natl -/u.
rewrite !mulrA [_/_]mulrC mulfVK ?neq0GC //; congr (_ * _).
apply: eq_big=> [g|g]; rewrite negbK.
  by case E1: (g \in H); rewrite ?andbF // (subsetP HsG _ (idP E1)).
by case/andP=> _ GiH; rewrite crestrictE.
Qed.

Lemma cinduced_conjC : forall f, ('Ind[G, H] f)^*%CH = 'Ind[G, H] (f^*)%CH.
Proof.
move=> f; apply/ffunP=> g.
rewrite !ffunE rmorphM conjC_inv conjC_nat; congr (_ * _).
rewrite rmorph_sum; apply: eq_bigr=> h HiG.
by rewrite ffunE.
Qed.

End Induced.

Notation "''Ind[' G , H ]  f " := (cinduced G H f) (at level 24).

Section Product.

Variable (gT : finGroupType) (G : {group gT}).

Lemma memc_prodI : forall (A B : {set gT}) (f1 f2 : {cfun gT}) , 
  f1 \in 'CF(G,A) -> f2 \in 'CF(G,B) -> f1 * f2 \in 'CF(G, A :&: B).
Proof.
move=> A B f1 f2; case/cfun_memfP=> H1f1 H2f1; case/cfun_memfP=> H1f2 H2f2.
apply/cfun_memfP; split=> [x|x y YiG]; rewrite !ffunE; last first.
  by rewrite H2f1 // H2f2.
rewrite !inE -andbA negb_andb; case/orP=> HA.
  by rewrite H1f1 ?mul0r // inE (negPf HA).
by rewrite H1f2 ?mulr0 // inE.
Qed.

Lemma memc_prod : forall (A : {set gT}) (f1 f2 : {cfun gT}) , 
  f1 \in 'CF(G,A) -> f2 \in 'CF(G,A) -> f1 * f2 \in 'CF(G, A).
Proof. by move=> A f1 f2 Hf1 Hf2; rewrite -[A]setIid memc_prodI. Qed.

End Product.
