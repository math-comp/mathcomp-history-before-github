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

Lemma dim_class_fun: \dim class_fun = #|classes G|.
Proof.
by move: class_fun_free; rewrite /free size_map -cardE card_ord; move/eqP.
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

Section Main.

(* Our group *)
Variable (gT : finGroupType).
Variable G: {group gT}.

Hypothesis groupC: group_closure_field C gT.

Let pGroupG: [char C]^'.-group G.
Proof.
by apply: sub_pgroup (pgroup_pi G)=> i _; rewrite inE /= Cchar.
Qed.

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
Qed.

Definition  xchar (chi: {ffun gT -> C^o}) (u: 'rV[C]_#|G|) : C^o := 
  \sum_(i < #|G|) u 0 i * chi (enum_val i).

Local Notation "\chi^_ i" := (xchar (irr_class_fun i)) (at level 3).

Lemma xchar_i_is_linear: forall i, linear (\chi^_ i).
Proof.
move=> i k m n.
rewrite scaler_sumr -big_split /=; apply: eq_bigr=> l _.
by rewrite scaler_mull -mulr_addl !mxE.
Qed.

Canonical Structure xchar_i_linear i := Linear (xchar_i_is_linear i).

Lemma xchar_is_linear: forall x, linear (xchar^~ x).
Proof.
move=> i k m n.
rewrite /xchar scaler_sumr -big_split /=; apply: eq_bigr=> l _.
by rewrite !ffunE mulr_addr scaler_mulr.
Qed.

Canonical Structure xchar_linear i := Linear (xchar_is_linear i).

(* To triger the previous structure *)
Lemma xchar_lin: forall x u, xchar u x = xchar^~ x u.
Proof. by []. Qed.

Lemma xchar_trace: forall i u,
  \chi^_i u  = \tr (gring_op (irr_repr i) (gring_mx (regular_repr C G) u)).
Proof.
move=> i u.
rewrite /xchar /gring_op /= gring_mxK /irr_class_fun.
apply: (@etrans _ _
   (\sum_(i0 < #|G|) \tr(u 0 i0 *: irr_repr i (enum_val i0)))).
  by apply: eq_bigr=> j _; rewrite ffunE enum_valP mul1r mxtraceZ.
rewrite -raddf_sum; congr (\tr _).
apply/matrixP=> i1 j1; rewrite !mxE summxE; apply eq_bigr=> k1 _.
by rewrite !(mxvecE,mxE).
Qed.

Local Notation e_ := (@Wedderburn_id _ _ _ _).
Local Notation R_ := (@Wedderburn_subring _ _ _ _).

Lemma xchar_subring : forall i j A, i != j -> (A \in R_ j)%MS -> \chi^_i (gring_row A) = 0.
Proof.
move=> i j A.
rewrite eq_sym -{1}(irr_reprK _ i) // -{1}(irr_reprK _ j) // => Hi HA.
rewrite xchar_trace -(mxtrace0 _ (irr_degree i)); congr (\tr _).
apply: (irr_comp'_op0 _ _ Hi)=> //; first by apply: socle_irr.
rewrite irr_reprK // gring_rowK  ?Wedderburn_id_mem //.
rewrite -(Wedderburn_sum sG pGroupG).
apply/memmx_sumsP; exists (fun i => (i==j)%:R *: A).
  rewrite (bigD1 j) //= eqxx scale1r big1 ?addr0 // => k.
  by case: (k == j); rewrite // scale0r.
by move=> k; case E1: (k == j); 
  [move/eqP: E1->; rewrite scale1r | rewrite scale0r mem0mx].
Qed.

Lemma xchar_id : forall i j,
  \chi^_i (gring_row (e_ j)) = if i == j then \chi_i 1%g else 0.
Proof.
move=> i j; case: eqP=> [->|Hi]; last first.
  by apply: xchar_subring (Wedderburn_id_mem _); apply/eqP.
rewrite ffunE group1 mul1r -gring_opG //.
have R1 := (envelop_mx_id (regular_repr C G) (group1 G)).
rewrite -[regular_repr C G 1%g]gring_rowK // -xchar_trace.
rewrite -[regular_repr _ _ _]mul1mx -(Wedderburn_sum_id sG pGroupG).
have->: regular_repr C G 1%g = 1%:M.
  by apply/matrixP=> i1 j1; rewrite !mxE !eqxx mulg1 gring_valK eq_sym.
rewrite mulmx1 !linear_sum /= (bigD1 j) //= big1; first by rewrite addr0.
move=> k; rewrite eq_sym => Hij.
by apply: (xchar_subring Hij); exact: (Wedderburn_id_mem).
Qed.

Definition base_irr: seq {ffun _ -> C^o} := map (fun i => \chi_ i) (enum sG).

Lemma free_base_irr : free (base_irr).
Proof.
apply/freeP=> s; set ss := \sum_(i<_) _ => Hs j.
have Hj: (j <  #|sG|)%nat.
  by case: j; rewrite size_map -cardE card_irr.
pose j' := enum_val (Ordinal Hj).
suff: xchar ss (gring_row (e_ j')) = s j * \chi_ j' 1%g.
  rewrite /xchar big1 //.
    move/eqP; rewrite eq_sym mulf_eq0; case/orP; first by move/eqP.
    rewrite chi1; move/GRing.charf0P: Cchar=> -> He.
    by move: (irr_degree_gt0 j'); rewrite (eqP He).
  by move=> i _; rewrite Hs ffunE mulr0.
(* ugly *)
set u := gring_row _; move: (@linear_sum _ _ _ (xchar_linear u))=> /= ->.
rewrite (bigD1 j) //= big1.
  rewrite  addr0 (nth_map (principal_comp sG)) //; last by rewrite -cardE.
  move: (@linearZ _ _ _ (xchar_linear u))=> /= ->.
  suff->: (nth [1 sG]%irr (enum sG) j) = j' by rewrite  xchar_id eqxx.
  by move: (nth_enum_rank [1 sG]%irr j'); rewrite enum_valK.
move=> i Hij.
have Hi: (i <  #|sG|)%nat.
  by case: {Hij}i; rewrite size_map -cardE card_irr.
pose i' := enum_val (Ordinal Hi).
rewrite  (nth_map (principal_comp sG)) //; last by rewrite -cardE.
move: (@linearZ _ _ _ (xchar_linear u))=> /= ->.
have->: (nth [1 sG]%irr (enum sG) i) = i'.
  by move: (nth_enum_rank [1 sG]%irr i'); rewrite enum_valK.
rewrite  xchar_id; case: eqP; last by rewrite scaler0.
move/eqP=> HH; case/negP: Hij.
by move: HH; rewrite (bij_eq ((enum_val_bij (socle_finType sG)))).
Qed.

Lemma base_irr_basis: is_basis 'CL[C](G) base_irr.
Proof.
rewrite /is_basis free_base_irr andbT /is_span -dimv_leqif_eq.
   rewrite dim_class_fun.
   move: free_base_irr; rewrite /free; move/eqP->.
   by rewrite size_map -cardE card_irr.
rewrite -span_subsetl; apply/allP=> i; case/mapP=> j _ ->.
apply: character_of_in_class_fun.
Qed.

End Character.

End Main.