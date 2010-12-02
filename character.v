(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient finalg action zmodp.
Require Import commutator cyclic center pgroup matrix mxalgebra mxpoly.
Require Import mxrepresentation vector.

(****************************************************************************)
(*  trying to do something about characters                                 *)
(****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(* function of a fintype into a ring form a vectype *)
Section Vectype.

Variable (R : fieldType) (aT : finType).

Implicit Types f g : {ffun aT -> R^o}.

(* Why this does not work?
Definition ffun2rv f :=  \row_(i < #|aT|) f (enum_val i).
Lemma class_fun2rv_morph_p : linear ffun2rv.
*)
Definition ffun2rv f : 'rV[R]_#|aT| :=  \row_(i < #|aT|) f (enum_val i).

Lemma ffun2rv_morph_p : linear ffun2rv.
Proof.
by move=> k /= x y; apply/matrixP=> [] [[|i] Hi] j; rewrite !mxE !ffunE.
Qed.

Canonical Structure ffun2rv_morph := Linear ffun2rv_morph_p.

Lemma ffun2rv_bij : bijective ffun2rv.
Proof.
exists (fun r: 'rV[R]_#|aT| => [ffun x: aT => r 0 (enum_rank x)]).
  by move=> g; apply/ffunP=> x; rewrite ffunE mxE enum_rankK.
by move=> r; apply/rowP=> i; rewrite mxE ffunE enum_valK.
Qed.

Definition ffunVectMixin := VectMixin ffun2rv_morph_p ffun2rv_bij.
Canonical Structure ffunVectType := VectType R ffunVectMixin.

End Vectype.

Local Notation "{ 'vffun' x '->' y }" := (ffunVectType y x)
  (at level 0, format "{ 'vffun'  '[hv' x  '->'  y ']' }") : type_scope.

Section ClassFun.

Variable (R : fieldType) (gT: finGroupType) (G: {group gT}).

Definition base_class_fun : seq {ffun gT -> R^o} :=
  (map (fun i : 'I_#|classes G| => [ffun x => (x \in  (enum_val i))%:R])
    (enum 'I_#|classes G|)).

(* for the moment we build it like this, the proper base should
   the set of irreducible character instead
*)
Definition class_fun := span base_class_fun.

Lemma class_fun_memP: forall (f: {ffun gT -> R}),
  reflect 
    ((forall x, x \notin G -> f x = 0) /\
     (forall x y, x \in G -> y \in G -> f (x ^ y) = f x))
    (f \in class_fun).
Proof.
move=> f; apply: (iffP idP)=> [|[Hg Hc]].
  move/coord_span->; split=> [x Inx|].
    rewrite sum_ffunE ffunE; apply: big1=> i _.
    have: base_class_fun`_i \in base_class_fun by apply: mem_nth.
    case/mapP=> j Hj ->; rewrite !ffunE.
    have [y Gy ->] := imsetP (enum_valP j).
    move/subsetP: (class_subG Gy (subxx _)); move/(_ x); move/contra.
    by move/(_ Inx); case: (_ \in _)=> //; rewrite scaler0.
  move=> x y Hx Hy.
  apply/eqP; rewrite -subr_eq0; apply/eqP.
  rewrite !sum_ffunE !ffunE -sumr_sub; apply: big1=> i _.
  set u := coord _ _ _; rewrite !ffunE.
  have: base_class_fun`_i \in base_class_fun by apply: mem_nth.
  case/mapP=> j Hj ->; rewrite !ffunE.
  have [z Gz ->] := imsetP (enum_valP j).
  by rewrite (class_transl _ (memJ_class _ _)) // subrr.
suff<-: \sum_(C \in (classes G)) 
           (f (repr C)) *: [ffun x => (x \in C)%:R] = f :> {ffun gT -> R^o}.
  apply: memv_sum=> i Hi.
  apply: memvZl; apply: memv_span;  apply/mapP.
  by exists (enum_rank_in (classes1 G) i); [rewrite mem_enum | rewrite enum_rankK_in].
apply/ffunP=> g; rewrite sum_ffunE !ffunE.
case HgG: (g \in G); last first.
  rewrite Hg ?HgG //; apply: big1=> i Hi; rewrite !ffunE.
  have [x Gx ->{k}] := imsetP Hi.
  case Hgx: (_ \in _); last by rewrite scaler0.
  move/subsetP: (class_subG Gx (subxx G)).
  by move/(_ g (idP Hgx)); rewrite HgG.
rewrite (bigD1 (g ^: G : set_of_finType _)) /=; last by apply/imsetP; exists g.
rewrite !ffunE big1.
  rewrite class_refl.
  case: (repr_class G g)=> x Hx ->; rewrite Hc // addr0; exact: mulr1.
move=> i; case/andP; case/imsetP=> y Hy -> Hz.
rewrite !ffunE; case E1: (_ \in _); last by rewrite scaler0.
by case/negP: Hz; rewrite eq_sym; apply/eqP; apply: class_transr.
Qed.

Lemma class_fun_free: free base_class_fun.
Proof.
apply/freeP=> s S0 i.
have Hi: i < #|classes G| by case: i=> /= m; rewrite size_map -cardE card_ord.
move/ffunP: S0; move/(_ (repr (enum_val (Ordinal Hi)))).
rewrite sum_ffunE !ffunE (bigD1 i) //= big1.
 rewrite !ffunE (nth_map (Ordinal Hi)) // ?ffunE; last first.
   by rewrite -cardE card_ord.
 rewrite (nth_ord_enum  _ (Ordinal Hi)).
 have [y Gy ->] := imsetP (enum_valP (Ordinal Hi)).
 case: (repr_class G y)=> x Hx ->.
 by rewrite memJ_class // addr0 => <-; apply: sym_equal; exact: mulr1.
move=> j Dij.
rewrite (nth_map (Ordinal Hi)) ?ffunE; last first.
  by case: {Dij}j=> /= m; rewrite size_map.
have Hj: j < #|classes G|.
  by case: {Dij}j=> /= m; rewrite size_map -cardE card_ord.
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

End ClassFun.

Local Notation "''CL[' R ] ( G ) " := (class_fun R G).
 
Section Character.

(* Some axioms to start with *)
Variable C : closedFieldType.

Hypothesis Cchar : [char C] =i pred0.
Variable conjC : {rmorphism C -> C}.
Notation "x ^* " := (conjC x).

Hypothesis conjCK : involutive conjC.
Hypothesis conjCC : forall n, conjC (n%:R) = n%:R.

Lemma conjC0 : 0 ^* = 0.
Proof. exact: (conjCC 0). Qed.

Lemma conjC1 : 1 ^* = 1.
Proof. exact: (conjCC 1). Qed.

Lemma conjC_eq0 : forall x, (x ^* == 0) = (x == 0).
Proof.
move=> x; apply/eqP/eqP=> H; last by rewrite H (conjCC 0).
by rewrite -[x]conjCK H (conjCC 0).
Qed.

Variable repC : C -> bool. (* C -> R^+ *)
Hypothesis repC_inv : forall x, x != 0 -> repC x = repC (1/x).
Hypothesis repCD : forall x y, repC x -> repC y -> repC (x + y).
Hypothesis repC_pconj : forall x, repC (x * x ^*).
Hypothesis repC_conj : forall x, repC (x ^*) = repC (x).
Hypothesis repCMl : forall x y, x != 0 -> repC x -> repC (x * y) = repC y.
Hypothesis repC_anti : forall x, repC x -> repC (-x) -> x = 0.

Lemma repC0 : repC 0.
Proof. by rewrite -[0](mul0r (0 ^*)) repC_pconj. Qed.

Lemma repC1 : repC 1.
Proof. by rewrite -[1](mul1r 1) -{2}conjC1 repC_pconj. Qed.

Lemma repCC : forall n, repC (n%:R).
Proof.
by elim=> [|n IH]; [exact: repC0 | rewrite -addn1 natr_add repCD // repC1].
Qed.

Definition leC x y := repC (y - x).

Notation "x <= y" := (leC x y).

Definition ltC x y := ((x != y) && (x <= y)).

Notation " x < y " := (ltC x y).

Lemma leCC : forall n, 0 <= n%:R.
Proof. by move=> n; rewrite /leC subr0 repCC. Qed.

Lemma ltCW : forall x y, x < y -> x <= y.
Proof. by move=> x y; case/andP. Qed.

Lemma leCD2l: forall z x y, (z + x <= z + y) = (x <= y).
Proof.
by move=> z x y; rewrite /leC oppr_add addrA [z + _]addrC addrK.
Qed.


Section Character1.

(* Our group *)
Variable (gT : finGroupType).
Variable G: {group gT}.

Hypothesis groupC: group_closure_field C gT.

Definition character_of n (f: gT -> 'M[C]_n) := 
  [ffun g: gT => ((g \in G)%:R * \tr (f g))].

Lemma character_of_sim: 
  forall n1 n2 (repr1: mx_representation C G n1) (repr2: mx_representation C G n2),
  mx_rsim repr1 repr2 -> character_of repr1 = character_of repr2.
Proof.
move=> n1 n2 repr1 repr2; case/mx_rsim_def=> M1 [M2] HM1M2 Hx.
apply/ffunP=> x; rewrite !ffunE; case H: (_ \in _); last by rewrite !mul0r.
by rewrite Hx // mxtrace_mulC mulmxA HM1M2 mul1mx.
Qed.

Lemma character_of_in_class_fun: forall n (repr:  mx_representation C G n), 
  (character_of repr) \in 'CL[C](G).
Proof.
move=> n repr; apply/class_fun_memP.
split=> [x|x y Hx Hy]; rewrite !ffunE.
  by case: (x \in G)=> //; rewrite mul0r.
by rewrite groupJ // Hx !mul1r !(repr_mxM,repr_mxV,groupM,groupV) //
           mxtrace_mulC mulmxK // repr_mx_unit.
Qed.  

Variable sG : irrType C G.

Definition irr_class_fun (i : sG) :=  character_of (irr_repr i).

Local Notation "\chi_ i" :=  (irr_class_fun i) (at level 3).

Lemma chi1: forall i, \chi_ i 1%g = (irr_degree i)%:R.
Proof.
by move=> i; rewrite ffunE group1 mul1r repr_mx1 mxtrace1.
Qed.

Lemma sum_chi2: \sum_i (\chi_ i 1%g) ^+ 2 = #|G|%:R.
Proof.
rewrite -{5}(sum_irr_degree sG) //.
  rewrite (big_morph _ (@natr_add _) (erefl _)).
  by apply: eq_bigr=> i _; rewrite chi1 natr_exp.
by apply: sub_pgroup (pgroup_pi G)=> i _; rewrite inE /= Cchar.
Qed.

Definition  xchar (u: 'rV[C]_#|G|) chi := \sum_(i < #|G|) u 0 i * chi (enum_val i).

(*
Lemma xchar_trace: forall i u,
  xchar u \chi_i = \tr (gring_op (irr_repr i) (gring_mx (regular_repr C G) u)).
Proof.
*)

End Character1.

End Character.
