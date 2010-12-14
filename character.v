(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient finalg action zmodp.
Require Import commutator cyclic center pgroup matrix mxalgebra mxpoly.
Require Import mxrepresentation vector.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(**
 This should be moved to matrix.v
**)


Lemma cofactor_mxZ : forall (R : comRingType) (n : nat) (A : 'M[R]_n) a i j, 
 cofactor (a *: A) i j = a^+n.-1 * cofactor A i j.
Proof.
move=> R n A a i j; rewrite !expand_cofactor.
rewrite -mulr_sumr; apply: eq_bigr=> k Hk.
rewrite [a^+_ * _]mulrC -mulrA; congr (_ * _).
suff->: a ^+ n.-1 = \prod_(k0 | i != k0) a.
  by rewrite -big_split; apply: eq_bigr=> i1 _; rewrite !mxE mulrC.
rewrite prodr_const; congr (_ ^+ _).
rewrite -{1}[n]card_ord -(cardsC1 i); apply: eq_card=> m.
by rewrite !inE /in_mem /= eq_sym; case: (i == m).
Qed.

Lemma adj1 : forall (R : comRingType) (n : nat), \adj (1%:M) = 1%:M :> 'M[R]_n.
Proof.
by move=> R n; rewrite -{2}(det1 R n) -mul_adj_mx mulmx1.
Qed.

Lemma adj_mxZ : forall (R : comRingType) (n : nat) (A : 'M[R]_n) a, 
 \adj (a *: A) = a^+n.-1 *: \adj A.
Proof.
by move=> R n A a; apply/matrixP=> i j; rewrite !mxE cofactor_mxZ.
Qed.

Lemma unitmxZ: forall (R : comUnitRingType) n (A : 'M[R]_n) a,
  GRing.unit a -> (a *: A) \in unitmx = (A \in unitmx).
Proof.
move=> R n A a Ha.
rewrite !unitmxE det_scalemx GRing.commr_unit_mul ?GRing.unitr_exp //.
exact: mulrC.
Qed.

Lemma invmxZ : forall (R : fieldType) (n : nat) (A : 'M[R]_n) a, 
 A \in unitmx -> invmx (a *: A) = a^-1 *: invmx A.
Proof.
move=> R [|n] A a HA; first by rewrite !(flatmx0 (_ *: _)); exact: flatmx0.
case: (a =P 0)=> [->|].
  by rewrite invr0 !scale0r /invmx det0 invr0 scale0r if_same.
move/eqP=> Ha.
have Ua: GRing.unit a by by rewrite GRing.unitfE.
have Uan: GRing.unit (a^+n) by rewrite GRing.unitr_exp.
have Uan1: GRing.unit (a^+n.+1) by rewrite GRing.unitr_exp.
rewrite /invmx det_scalemx adj_mxZ unitmxZ // HA !scalerA invr_mul //.
congr (_ *: _); rewrite -mulrA mulrC; congr (_ / _).
by rewrite mulrC exprS invr_mul // mulrA GRing.divrr // mul1r.
Qed.

Lemma invmx1:  forall (R : fieldType) (n : nat), invmx 1%:M = 1%:M :> 'M[R]_n.
Proof.
by move=> R n; rewrite /invmx det1 invr1 scale1r adj1 if_same.
Qed.

Lemma invmx_scalar :
 forall (R : fieldType) (n : nat) (a: R), invmx (a%:M) = a^-1%:M :> 'M[R]_n.
Proof.
by move=> R n a; rewrite -scalemx1 invmxZ ?unitmx1 // invmx1 scalemx1.
Qed.

Lemma scalar_exp:
 forall (R : ringType) (m n : nat) (a: R), 
 (a^+m)%:M = a%:M^+ m :> 'M_n.+1.
Proof.
move=> R m n a; elim: m=> [|m IH]; first by rewrite !expr0.
by rewrite !exprS scalar_mxM IH.
Qed.


(****************************************************************************)
(*  trying to do something about characters                                 *)
(****************************************************************************)

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

Lemma class_fun_memP : forall (f: {ffun gT -> R}),
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

Lemma class_fun0 : forall (f: {ffun gT -> R}) x, 
  f \in class_fun -> x \notinG -> f x = 0.
Proof.
by move=> f x; case/class_fun_memP=> Hx _; exact: (Hx x).
Qed.

Lemma class_funJ : forall (f: {ffun gT -> R}) x y, 
  f \in class_fun -> x \in G -> y \in G  -> f (x ^ y) = f x.
Proof.
by move=> f x y; case/class_fun_memP=> _ Hx; exact: (Hx x).
Qed.

Lemma class_fun_free : free base_class_fun.
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

Lemma dim_class_fun : \dim class_fun = #|classes G|.
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
Hypothesis repC_unit_exp: forall x n, repC x -> ((x^+n == 1) = (x == 1)).

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

Lemma leCD2l : forall z x y, (z + x <= z + y) = (x <= y).
Proof.
by move=> z x y; rewrite /leC oppr_add addrA [z + _]addrC addrK.
Qed.

Definition normC x := x * x^*.

Lemma repC_normC : forall x, repC (normC x).
Proof. exact: repC_pconj. Qed.

Lemma normC0 : normC 0 = 0.
Proof.  exact: mul0r. Qed.

Lemma normC1 : normC 1 = 1.
Proof.  by rewrite /normC mul1r conjC1. Qed.

Lemma normC_mul :  {morph normC: x y / x * y}.
Proof.
move=> x y; rewrite /normC rmorphM -!mulrA; congr (_ * _).
by rewrite mulrC -!mulrA [y * _]mulrC.
Qed.

Lemma normC_exp : forall x n, normC (x^+n) = normC x ^+ n.
Proof.
move=> x; elim=> [|n IH]; first by rewrite !expr0 normC1.
by rewrite exprS normC_mul IH exprS.
Qed.

Lemma repC_norm_inv : forall x, x^-1 = (normC x)^-1 * x^*.
Proof.
move=> x; case: (x =P 0)=> [->|].
  by rewrite conjC0 mulr0 invr0.
move/eqP=> Hx.
rewrite /normC invr_mul ?(GRing.unitfE,conjC_eq0) //.
by rewrite mulrC mulrA GRing.mulrV ?(GRing.unitfE,conjC_eq0) // div1r.
Qed.

Section Main. 

(* Our group *)
Variable (gT : finGroupType).
Variable G : {group gT}.

Hypothesis groupC : group_closure_field C gT.

Let pGroupG : [char C]^'.-group G.
Proof.
by apply: sub_pgroup (pgroup_pi G)=> i _; rewrite inE /= Cchar.
Qed.

Definition character_of n (f: gT -> 'M[C]_n) : {ffun gT -> C^o} := 
  [ffun g: gT => ((g \in G)%:R * \tr (f g))].

Lemma character_of_sim : 
  forall n1 n2 (repr1: mx_representation C G n1) (repr2: mx_representation C G n2),
  mx_rsim repr1 repr2 -> character_of repr1 = character_of repr2.
Proof.
move=> n1 n2 repr1 repr2; case/mx_rsim_def=> M1 [M2] HM1M2 Hx.
apply/ffunP=> x; rewrite !ffunE; case H: (_ \in _); last by rewrite !mul0r.
by rewrite Hx // mxtrace_mulC mulmxA HM1M2 mul1mx.
Qed.

Lemma character_of_in_class_fun : forall n (repr:  mx_representation C G n), 
  (character_of repr) \in 'CL[C](G).
Proof.
move=> n repr; apply/class_fun_memP.
split=> [x|x y Hx Hy]; rewrite !ffunE.
  by case: (x \in G)=> //; rewrite mul0r.
by rewrite groupJ // Hx !mul1r !(repr_mxM,repr_mxV,groupM,groupV) //
           mxtrace_mulC mulmxK // repr_mx_unit.
Qed.  

Let sG : irrType C G := DecSocleType (regular_repr C G).

Definition irr_class_fun (i : sG) :=  character_of (irr_repr i).

Local Notation "\chi_ i" :=  (irr_class_fun i) (at level 3).

Lemma chi1 : forall i, \chi_ i 1%g = (irr_degree i)%:R.
Proof.
by move=> i; rewrite ffunE group1 mul1r repr_mx1 mxtrace1.
Qed.

Lemma chi1_neq0: forall i, \chi_ i 1%g != 0.
Proof.
move=> i; rewrite chi1; move/GRing.charf0P: Cchar=> ->.
by case: irr_degree (irr_degree_gt0 i).
Qed.

Lemma sum_chi2 : \sum_i (\chi_ i 1%g) ^+ 2 = #|G|%:R.
Proof.
rewrite -{5}(sum_irr_degree sG) //.
rewrite (big_morph _ (@natr_add _) (erefl _)).
by apply: eq_bigr=> i _; rewrite chi1 natr_exp.
Qed.

Definition  xchar (chi: {ffun gT -> C^o}) (u: 'rV[C]_#|G|) : C^o := 
  \sum_(i < #|G|) u 0 i * chi (enum_val i).

Local Notation "\chi^_ i" := (xchar (irr_class_fun i)) (at level 3).

Lemma xchar_is_linear : forall chi, linear (xchar chi).
Proof.
move=> chi k m n.
rewrite scaler_sumr -big_split /=; apply: eq_bigr=> l _.
by rewrite scaler_mull -mulr_addl !mxE.
Qed.

Canonical Structure xchar_linear chi := Linear (xchar_is_linear chi).

(* In order to add a second canonical structure on xchar *)
Definition xcharb x := xchar^~ x.

Lemma xcharbE : forall u x, xchar u x = xcharb x u.
Proof. by []. Qed.

Lemma xcharb_is_linear : forall x, linear (xcharb x).
Proof.
move=> i k m n.
rewrite /xchar scaler_sumr -big_split /=; apply: eq_bigr=> l _.
by rewrite !ffunE mulr_addr scaler_mulr.
Qed.

Canonical Structure xcharb_linear x := Linear (xcharb_is_linear x).

Lemma xchar_trace : forall u n (chi: mx_representation C G n),
  xchar (character_of chi) u = \tr (gring_op chi (gring_mx (regular_repr C G) u)).
Proof.
move=> u n chi.
rewrite /xchar /gring_op /= gring_mxK /irr_class_fun.
apply: (@etrans _ _
   (\sum_(i0 < #|G|) \tr(u 0 i0 *: chi (enum_val i0)))).
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

Definition base_irr : seq {ffun _ -> C^o} := map (fun i => \chi_ i) (enum sG).
  
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
rewrite xcharbE linear_sum; rewrite (bigD1 j) //= big1.
  rewrite  addr0 (nth_map (principal_comp sG)) //; last by rewrite -cardE.
  rewrite linearZ /= -xcharbE.
  suff->: (nth [1 sG]%irr (enum sG) j) = j' by rewrite  xchar_id eqxx.
  by move: (nth_enum_rank [1 sG]%irr j'); rewrite enum_valK.
move=> i Hij.
have Hi: (i <  #|sG|)%nat.
  by case: {Hij}i; rewrite size_map -cardE card_irr.
pose i' := enum_val (Ordinal Hi).
rewrite  (nth_map (principal_comp sG)) //; last by rewrite -cardE.
rewrite linearZ /= -xcharbE.
have->: (nth [1 sG]%irr (enum sG) i) = i'.
  by move: (nth_enum_rank [1 sG]%irr i'); rewrite enum_valK.
rewrite  xchar_id; case: eqP; last by rewrite scaler0.
move/eqP=> HH; case/negP: Hij.
by move: HH; rewrite (bij_eq ((enum_val_bij (socle_finType sG)))).
Qed.

Lemma base_irr_basis : is_basis 'CL[C](G) base_irr.
Proof.
rewrite /is_basis free_base_irr andbT /is_span -dimv_leqif_eq.
   rewrite dim_class_fun.
   move: free_base_irr; rewrite /free; move/eqP->.
   by rewrite size_map -cardE card_irr.
rewrite -span_subsetl; apply/allP=> i; case/mapP=> j _ ->.
apply: character_of_in_class_fun.
Qed.

Lemma add_mx_repr :
 forall m n 
  (repr1 : mx_representation C G m) (repr2 : mx_representation C G n),
  mx_repr G (fun g => block_mx (repr1 g) 0 0 (repr2 g)).
Proof.
move=> m n repr1 repr2; split=> [|x y Hx Hy].
  by rewrite !repr_mx1 -scalar_mx_block.
by rewrite mulmx_block !(mulmx0,mul0mx,addr0,add0r,repr_mxM).
Qed.

Definition add_repr m n
  (repr1 : mx_representation C G m) (repr2 : mx_representation C G n)
  := MxRepresentation (add_mx_repr repr1 repr2).

Lemma character_of_morph : forall m n
  (repr1 : mx_representation C G m) (repr2 :  mx_representation C G n),
  character_of (add_repr repr1 repr2) = character_of repr1 + character_of repr2.
Proof.
move=> m n repr1 repr2.
by apply/ffunP=> g; rewrite !ffunE -mulr_addr mxtrace_block.
Qed.

Notation "\rho" :=  (character_of (regular_repr C G)).

Lemma rho_val : forall g : gT, g \in G ->
  \rho g = if g == 1%g then #|G|%:R else 0%:R.
Proof.
move=> g Hg; rewrite ffunE Hg mul1r; rewrite /mxtrace.
case: eqP=> [->| Hd]; last first.
  apply: big1=> i _; rewrite !mxE andTb.
  case: eqP=> // He; case: Hd; apply: sym_equal.
  apply: (mulgI (enum_val i)); rewrite mulg1.
  by apply: (can_in_inj (@gring_indexK _ G));
   [exact: enum_valP | exact: (groupM (enum_valP _) Hg) | rewrite gring_valK].
rewrite (eq_bigr (fun x => 1%:R)); last first.
  by move=> i; rewrite !mxE mulg1 gring_valK !eqxx.
by rewrite sumr_const cardT -cardE card_ord.
Qed.

Lemma rho_sum : \rho = \sum_i \chi_i(1%g) *: \chi_i.
Proof.
apply/ffunP=> g; rewrite !ffunE.
case Ig: (_ \in _); last first.
  rewrite mul0r sum_ffunE ffunE big1 // => i _.
  by rewrite ffunE [_ g](class_fun0 (character_of_in_class_fun _)) (scaler0,Ig).
rewrite mul1r mxtrace_regular // sum_ffunE ffunE.
by apply eq_bigr=> i _; rewrite chi1 !ffunE Ig mul1r // GRing.scaler_nat.
Qed.

Lemma row_is_linear: 
  forall (R: ringType) m n (i: 'I_m), linear (@row R m n i).
Proof.
by move=> R m n i k A B; apply/matrixP=> x y; rewrite !mxE.
Qed.

Canonical Structure row_linear R m n i := Linear (@row_is_linear R m n i).

Lemma gring_row_is_linear: 
  forall (R: comUnitRingType) gT G, linear (@gring_row R gT G).
Proof.
move=> *; exact: row_is_linear.
Qed.

Canonical Structure gring_row_linear R gT G := 
  Linear (@gring_row_is_linear R gT G).

Lemma chi_e_mul : forall i A, (A \in group_ring C G)%MS ->
 \chi^_i (gring_row (e_ i *m A)) = \chi^_i (gring_row A).
Proof.
move=> i A HA.
rewrite -{2}[A]mul1mx -(Wedderburn_sum_id sG) //.
rewrite mulmx_suml !linear_sum (bigD1 i) //=.
rewrite big1 ?addr0 // => j; rewrite eq_sym => Hij.
apply: (xchar_subring Hij).
case/andP: (Wedderburn_ideal j)=> _ Hj.
apply: submx_trans Hj=> //.
apply: mem_mulsmx=> //.
exact: Wedderburn_id_mem.
Qed.

Lemma xchar_singleton : forall n g (repr: mx_representation C G n),
  let chi := (character_of repr) in
  g \in G -> xchar chi (gring_row (regular_repr C G g)) = chi g.
Proof.
move=> n g repr chi Hg.
  rewrite /xchar (bigD1 (enum_rank_in (group1 G) g)) // big1 ?addr0.
  by rewrite enum_rankK_in // !mxE gring_indexK // mul1g !eqxx mul1r //= addr0.
move=> i; rewrite !mxE enum_rankK_in // mul1g /gring_index.
by case: (i == _)=> //; rewrite mul0r.
Qed.


(* This corresponds to Issac Th. 2.12 *)
Lemma gring_row_e : forall (i: sG), 
  gring_row (e_ i) = 
  \row_j (#|G|%:R^-1 * \chi_i 1%g * \chi_i ((enum_val j)^-1)%g).
Proof.
move=> i; apply/rowP=> j.
set j1 := ((enum_val j)^-1)%g.
have Inj1: ((enum_val j)^-1 \in G)%g by rewrite groupV enum_valP.
pose rj := regular_repr C G j1.
have: xchar \rho (gring_row (e_ i *m rj)) = #|G|%:R * gring_row (e_ i) 0 j.
  rewrite /xchar (bigD1 (gring_index G 1%g)) //= big1; last first.
    move=> k Hk; rewrite rho_val; last by apply: enum_valP.
    case: eqP; last by rewrite mulr0.
    by move=> Hk'; case/negP: Hk; rewrite -Hk' gring_valK.
  rewrite addr0 enum_rankK_in // gring_row_mul.
  rewrite rho_val // eqxx mulrC; congr (_ * _).
  rewrite {1}mxE {1}(bigD1 j) //= {1}big1.
    by rewrite !mxE mulgV !eqxx mulr1 addr0.
  move=> k Hk.
  rewrite !mxE eqxx; case: eqP; last by rewrite mulr0.
  move=> Hi; case/negP: Hk.
  apply/eqP; apply: enum_val_inj; apply/eqP; rewrite eq_mulgV1.
  rewrite eq_sym; apply/eqP.
  apply: (can_in_inj (@gring_indexK _ G))=> //.
  by rewrite !(groupM,enum_valP).
rewrite rho_sum xcharbE linear_sum /=.
rewrite (bigD1 i) //= big1 ?addr0; last first.
  move=> k Hki.
  rewrite linearZ /= -xcharbE.
  rewrite (xchar_subring Hki) //; first by rewrite scaler0.
  case/andP: (Wedderburn_ideal i)=> _ Hi.
  apply: submx_trans Hi; apply: mem_mulsmx; first by exact: Wedderburn_id_mem.
  by apply: envelop_mx_id; rewrite groupV enum_valP.
rewrite linearZ /= -xcharbE.
rewrite chi_e_mul; last first.
  by apply: envelop_mx_id; rewrite groupV enum_valP.
rewrite !mxE xchar_singleton // /GRing.scale /= -mulrA => ->.
rewrite !mulrA mulVr ?mul1r // GRing.unitfE.
by move/charf0P: Cchar->; case: #|_| (cardG_gt0 G).
Qed.

(* Painfully following Issac's proof 2.14 *)
Lemma chi_orthogonal_relation: forall (i j: sG),
 ((#|G|%:R^-1 * 
 \sum_(k < #|G|)
   \chi_i ((enum_val k))%g * \chi_j (enum_val k)^-1%g) = 
  (i == j)%:R)%R.
Proof.
move=> i j.
have F0 : e_ i *m e_ j = (i == j)%:R *: e_ i.
  case: eqP=> [<-|Hij]; [rewrite scale1r | rewrite scale0r].
    by case: (Wedderburn_is_id pGroupG i)=> _ Hi Hj _; exact: Hj.
  move/eqP: Hij=> HH; apply: (Wedderburn_mulmx0 HH); exact: Wedderburn_id_mem.
have F1: #|G|%:R^-1 * \chi_i 1%g * \chi_j 1%g != 0.
  apply: mulf_neq0; last by exact: chi1_neq0.
  apply: mulf_neq0; last by exact: chi1_neq0.
  apply: invr_neq0.
  by move/charf0P: Cchar->; case: #|_| (cardG_gt0 G).
apply: (mulIf F1).
pose r1 (u: 'M[C]_#|G|) := gring_row u 0 (gring_index G 1%g).
apply: (@etrans _ _ (r1 (e_ i *m e_ j))).
  have F3: injective (fun x : 'I_#|G| => gring_index G (enum_val x)^-1).
    move=> x y H; apply: enum_val_inj; apply: invg_inj.
    by apply: (can_in_inj (@gring_indexK _ G)); rewrite // groupV enum_valP.
  rewrite (reindex_inj F3) /=.
  have->:
    r1 (e_ i *m e_ j) =
   \sum_j0
     (gring_row (e_ i) 0 j0) * ((gring_row (e_ j) 0 (gring_index G (enum_val j0)^-1))).
    rewrite /r1 gring_row_mul.
    have F2: (e_ j \in group_ring C G)%MS.
      apply (submx_trans (Wedderburn_id_mem _)).
      by rewrite /Wedderburn_subring genmxE submxMl.
    rewrite -{1}(gring_rowK F2) mxE.
    apply:eq_bigr=> i1 _; congr (_ * _).
    rewrite 2!mxE.
    rewrite {1}(bigD1 (gring_index G (enum_val i1)^-1)) //=.
    set u := gring_row _ _ _ .
    rewrite {1}big1 ?addr0.
      rewrite !(mxE,mxvecE) gring_indexK; last by rewrite groupV enum_valP.
      by rewrite mulgV !eqxx mulr1.
    move=> i2 Hi2.
    rewrite !(mxE,mxvecE).
    case: (gring_index G 1 =P _); last by rewrite andbF mulr0.
    move=> HH; case/negP: Hi2.
    have F4: (enum_val i1 * enum_val i2)%g \in G.
      by apply: groupM; exact: enum_valP.
    rewrite -[_^-1%g]mulg1.
    rewrite (can_in_inj (@gring_indexK _ G) (group1 G) F4 HH).
    by rewrite mulgA mulVg mul1g gring_valK.
  rewrite -mulr_sumr -mulr_suml; apply: eq_bigr=> i1 _.
  rewrite  {1}gring_row_e {1}gring_row_e !mxE.
  rewrite gring_indexK; last by rewrite groupV enum_valP.
  (* mimicing ring *)
  rewrite invgK.
  rewrite -!mulrA; congr (_ * _).
  apply: sym_equal; rewrite mulrC -!mulrA; congr (_ * _).
  apply: sym_equal; rewrite [\chi_ j _ * _]mulrC -!mulrA; congr (_ * _).
  by rewrite mulrC -!mulrA; congr (_ * _).
rewrite F0; case: eqP=> [->|_].
  by rewrite scale1r mul1r /r1 gring_row_e !mxE gring_indexK // invg1.
rewrite scale0r mul0r /r1.
suff->: @gring_row C _ G 0 = 0 by rewrite mxE.
by apply/rowP=> k; rewrite !mxE.
Qed.

Lemma chi_inv_abelian : forall (i: sG) g, abelian G -> g \in G ->
 \chi_i g^-1%g = (\chi_i g)^*.
Proof.
move=> i g AG Hg.
pose u := let m := Ordinal (irr_degree_gt0 i) in irr_repr i g m m.
have irr_scal: irr_repr i g = u %:M.
  apply/matrixP=> [] [[|i1] Hi1]; last first.
    by move: (Hi1); rewrite irr_degree_abelian in Hi1.
  case=> [] [|j1] Hj1; last first.
    by move: (Hj1); rewrite irr_degree_abelian in Hj1.
  rewrite /u !mxE; apply: eq_bigr=> i2 _l; rewrite !mxE.
  congr (_ * _); apply: eq_bigr=> i3 _; rewrite !mxE //.
  by congr (_ * _); apply: eq_bigr=> i4 _; rewrite !mxE.
have->: \chi_i g^-1%g = (\chi_i g)^-1.
  rewrite !ffunE groupV Hg {1}mul1r {1}mul1r repr_mxV //.
  by rewrite irr_scal -scalemx1 (invmxZ _ (unitmx1 _ _)) invmx1 
             !mxtraceZ mxtrace1 irr_degree_abelian // !mulr1.
rewrite repC_norm_inv.
suff->: normC (\chi_ i g) = 1 by rewrite invr1 mul1r.
apply/eqP; rewrite -(repC_unit_exp #[g])?repC_normC //.
rewrite -normC_exp -normC1; apply/eqP; congr (normC).
have<-: \chi_i 1%g = 1 by rewrite chi1 irr_degree_abelian.
rewrite -(expg_order g) !ffunE irr_scal Hg mul1r -scalemx1 mxtraceZ.
suff->: irr_repr i (g ^+ #[g]) = u^+#[g] *: 1%:M.
  by rewrite mxtraceZ mxtrace1 irr_degree_abelian // groupX // !mulr1 mul1r.
elim: #[_]=> [|n IH]; first by rewrite expg0 expr0 scale1r repr_mx1.
by rewrite expgS repr_mxM ?groupX // IH irr_scal !scalemx1 -scalar_mxM -exprS.
Qed.

End Main.

End Character.