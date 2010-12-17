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
This should be moved to ssralg.v
**)

Lemma ffunMn: forall (aT : finType) (rT : zmodType)  (f : {ffun aT -> rT}) n x,
  (f *+ n) x = f x *+ n.
Proof.
move=> aT rT f n x; elim: n => [|n IH].
  by rewrite !mulr0n ffunE.
by rewrite !mulrS ffunE IH.
Qed.


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

Variable repC : C -> bool. (* C -> R^+ *)
Hypothesis repCD : forall x y, repC x -> repC y -> repC (x + y).
Hypothesis repCMl : forall x y, x != 0 -> repC x -> repC (x * y) = repC y.
Hypothesis repC_anti : forall x, repC x -> repC (-x) -> x = 0.
Hypothesis repC_unit_exp: forall x n, repC x -> ((x^+n == 1) = (x == 1)).
Hypothesis repC_pconj : forall x, repC (x * x ^*).
Hypothesis repC_conjI : forall x, repC x -> x^* = x.
Hypothesis repC1 : repC 1.

Lemma repC_inv : forall x, repC (x^-1) = repC x.
Proof.
move=> x; case: (x =P 0)=> [->|]; first by rewrite invr0.
move/eqP; move=> Hx; apply/idP/idP=> Hp.
  by rewrite -(repCMl _ (invr_neq0 Hx)) // mulVf.
by rewrite -(repCMl _ Hx) // mulfV.
Qed.

Lemma repC_conj : forall x, repC (x ^*) = repC (x).
Proof.
by move=>x; apply/idP/idP=>Hp; first rewrite -[x]conjCK; 
   rewrite (repC_conjI Hp).
Qed.

Lemma repC0 : repC 0.
Proof. by rewrite -[0](mul0r (0 ^*)) repC_pconj. Qed.

Lemma repC_nat : forall n, repC (n%:R).
Proof.
by elim=> [|n IH]; [exact: repC0 | rewrite -addn1 natr_add repCD // repC1].
Qed.

Lemma conjC_nat : forall n, (n%:R)^* = n%:R.
Proof. exact: rmorph_nat. Qed.

Lemma conjC0 : 0 ^* = 0.
Proof. exact: (conjC_nat 0). Qed.

Lemma conjC1 : 1 ^* = 1.
Proof. exact: (conjC_nat 1). Qed.

Lemma conjC_eq0 : forall x, (x ^* == 0) = (x == 0).
Proof.
move=> x; apply/eqP/eqP=> H; last by rewrite H (conjC_nat 0).
by rewrite -[x]conjCK H (conjC_nat 0).
Qed.

Definition leC x y := repC (y - x).

Notation "x <= y" := (leC x y).

Definition ltC x y := ((x != y) && (x <= y)).

Notation " x < y " := (ltC x y).

Lemma leC_nat : forall n, 0 <= n%:R.
Proof. by move=> n; rewrite /leC subr0 repC_nat. Qed.

Lemma leC_refl: forall x, x <= x.
Proof. move=> x; rewrite /leC subrr; exact repC0. Qed.

Lemma ltCW : forall x y, x < y -> x <= y.
Proof. by move=> x y; case/andP. Qed.

Lemma leC_add2l : forall z x y, (z + x <= z + y) = (x <= y).
Proof.
by move=> z x y; rewrite /leC oppr_add addrA [z + _]addrC addrK.
Qed.

Lemma leC_add2r : forall z x y, (x + z <= y + z) = (x <= y).
Proof. by move=> z x y; rewrite ![_ +z]addrC leC_add2l. Qed.

Lemma posC_add: forall x y, 0 <= x -> 0 <= y -> 0 <= x + y.
Proof. by move=> x y; rewrite /leC !subr0; exact: repCD. Qed.

Lemma posC_mulr: forall x y, 0 < x -> 0 <= x * y = (0 <= y).
Proof. 
move=> x y; case/andP; rewrite /leC !subr0; move=>*.
by apply: repCMl; rewrite // eq_sym. 
Qed.

Lemma posC_mull: forall x y, 0 < x -> 0 <= y * x = (0 <= y).
Proof. move=> x y; rewrite mulrC; exact: posC_mulr. Qed.

Lemma posC_mul : forall x y : C, 0 <= x -> 0 <= y -> 0 <= x * y.
Proof.
move=> x y Hx Hy.
case: (boolP (x == 0)); first by move/eqP->; rewrite mul0r leC_refl.
by move=> Hdx; rewrite posC_mulr //; apply/andP; rewrite eq_sym.
Qed.

Lemma leC_anti: forall x y, x <= y -> y <= x -> x = y.
Proof.
move=> x y Hx Hy; apply/eqP; rewrite -subr_eq0; apply/eqP.
by apply: repC_anti; rewrite // oppr_sub.
Qed.

Lemma posC_unit_exp: forall x n, 0 <= x ->  (x ^+ n == 1) = (x == 1).
Proof. by move=> x n Hx; apply: repC_unit_exp; rewrite -[x]subr0. Qed.

Lemma posC_conjK: forall x, 0 <= x -> x^* = x.
Proof. by move=> x Hx; apply: repC_conjI; rewrite -[x]subr0. Qed.

Lemma posC1: 0 <= 1.
Proof. by rewrite /leC subr0. Qed.

Lemma posC_inv : forall x, (0 <= x^-1) = (0 <= x).
Proof. move=> x; rewrite /leC !subr0; exact: repC_inv. Qed.

Lemma posC_conj : forall x, (0 <= x ^*) = (0 <= x).
Proof. move=> x; rewrite /leC !subr0; exact: repC_conj. Qed.

Lemma posC_sum: 
   forall (I : Type) (r : seq I) (P : pred I) (F : I -> C),
   (forall i, P i -> 0 <= F i) -> 0 <= \sum_(j <- r | P j) F j.
Proof.
move=> i r P F1 H; elim: r=> [|y r Hrec].
  by rewrite big_nil=> *; exact: leC_refl.
rewrite big_cons; case E1: (P _)=> //.
by apply: posC_add=> //; exact: H.
Qed.

Lemma posC_add_eq0: forall x y,
  0 <= x -> 0 <= y -> (x + y == 0) = ((x == 0) && (y == 0)).
Proof.
move=> x y Hx Hy; apply/eqP/andP=>[Hxy|]; last first.
  by case; do 2 move/eqP->; exact: addr0.
split; apply/eqP; apply: leC_anti=> //.
  by rewrite -(leC_add2r y) Hxy add0r.
by rewrite -(leC_add2l x) Hxy addr0.
Qed.

Lemma posC_sum_eq0: 
   forall (I : eqType) (r : seq I) (P : pred I) (F : I -> C),
   (forall i, P i -> 0 <= F i) ->
   \sum_(j <- r | P j) F j = 0 ->
   (forall i, i \in r -> P i -> F i = 0).
Proof.
move=> I r P F HN; elim: r=> [|y r Hrec] //.
rewrite big_cons; case HP: (P _)=> Hs; last first.
  move=> i Hi Hp; apply: Hrec=> //.
  move: Hi; rewrite in_cons; case/orP=> //.
  by move/eqP=>Hi; case/negP: HP; rewrite -Hi.
move=> i Hi HP1.
move/eqP: Hs; rewrite posC_add_eq0 ?HN //.
  case/andP; move: Hi; rewrite in_cons; case/orP; first by do 2 move/eqP->.
  by move=> Hin _; move/eqP=> Hs; exact: Hrec.
by apply: posC_sum.
Qed.

Definition normC x := x * x^*.

(*
Hypothesis normC_add: forall x y,
  normC (x + y) <= normC x + normC y +  2%:R * (normC x * normC y).
*)

Lemma posC_norm : forall x, 0 <= normC x.
Proof. move=> x; rewrite /leC !subr0; exact: repC_pconj. Qed.

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

Lemma normC_conj: forall x, normC (x^*) = normC x.
Proof. by move=> x; rewrite /normC conjCK mulrC. Qed.

Lemma normC_inv : forall x, x^-1 = (normC x)^-1 * x^*.
Proof.
move=> x; case: (x =P 0)=> [->|].
  by rewrite conjC0 mulr0 invr0.
move/eqP=> Hx.
rewrite /normC invr_mul ?(GRing.unitfE,conjC_eq0) //.
by rewrite mulrC mulrA GRing.mulrV ?(GRing.unitfE,conjC_eq0) // div1r.
Qed.

Lemma normC_eq0: forall x, (normC x == 0) = (x == 0).
Proof.
move=> x; apply/eqP/eqP=> Hp; last first.
  by rewrite Hp normC0.
by apply/eqP; rewrite -invr_eq0 normC_inv Hp invr0 mul0r.
Qed.

Lemma conjC_inv: forall x, (x^-1)^* = (x^*)^-1.
Proof.
move=> x; rewrite normC_inv rmorphM conjCK.
rewrite (normC_inv x^*) conjCK; congr (_ * _).
rewrite normC_conj; apply: posC_conjK.
by rewrite posC_inv; exact: posC_norm.
Qed.

Variable getRatC : C -> (bool * nat * nat).
Definition isRatC c := 
   match getRatC c with (b,n,d) => c == (-1)^+b * n%:R * d.+1%:R^-1 end.

Hypothesis isRatCP :
  forall c,
   reflect
     (exists b: bool, exists p, c = (-1)^+b * p.1%:R * p.2.+1%:R^-1)
     (isRatC c).

Lemma isRatC_opp : forall c , isRatC (-c) = isRatC c.
Proof.
by move=>c;apply/isRatCP/isRatCP=> [] [b [[n d]] H];
   exists (~~b); exists (n,d); first rewrite -[c]opprK;
   rewrite H -!mulNr; case b; rewrite !(expr0,expr1,opprK).
Qed.

Lemma isRatC_add : forall c1 c2, isRatC c1 -> isRatC c2 -> isRatC (c1 + c2).
Proof.
move=> c1 c2; case/isRatCP=> b1 [[n1 d1] ->]; case/isRatCP=> b2 [[n2 d2] ->].
case: (b1 =P b2)=> [<-|Hb].
  apply/isRatCP; exists b1; exists (n1 * d2.+1 + n2 * d1.+1,(d1.+1 * d2.+1).-1)%N.
  rewrite -!mulrA -mulr_addr; congr (_ * _)%R.
  have F1: (d1.+1 * d2.+1)%:R != 0 :> C by move/GRing.charf0P: Cchar => ->.
  apply: (mulIf F1); apply: sym_equal.
  rewrite -mulrA prednK // mulVr ?GRing.unitfE // mulr1 natr_add !natr_mul.
  rewrite mulr_addl mulrA mulrVK; last first.
    by rewrite ?GRing.unitfE; move/GRing.charf0P: Cchar => ->.
  rewrite [d1.+1%:R * _]mulrC mulrA mulrVK // ?GRing.unitfE.
  by move/GRing.charf0P: Cchar => ->.
have->: (-1) ^+ b2 = -(-1) ^+ b1 :> C.
  by case: b1 Hb; case: b2=> // _; rewrite expr1 opprK.
rewrite !mulNr.
wlog HH : n1 d1 n2 d2 / (n2 * d1.+1 <= n1 * d2.+1)%N=> [HH|].
  case: (leqP  (n2 * d1.+1)%N (n1 * d2.+1)%N)=> H; first by apply: HH.
  by rewrite -isRatC_opp oppr_sub HH // ltnW.
apply/isRatCP; exists b1; 
  exists (n1 * d2.+1 - n2 * d1.+1,(d1.+1 * d2.+1).-1)%N.
rewrite -!mulrA -mulr_subr; congr (_ * _).
have F1: (d1.+1 * d2.+1)%:R != 0 :> C by move/GRing.charf0P: Cchar => ->.
apply: (mulIf F1); apply: sym_equal.
rewrite -mulrA prednK // mulVr ?GRing.unitfE // mulr1 natr_sub // !natr_mul.
rewrite mulr_subl mulrA mulrVK; last first.
  by rewrite ?GRing.unitfE; move/GRing.charf0P: Cchar => ->.
rewrite [d1.+1%:R * _]mulrC mulrA mulrVK // ?GRing.unitfE.
by move/GRing.charf0P: Cchar => ->.
Qed.

Lemma isRatC_addr : forall c1 c2, isRatC c1 -> isRatC (c1 + c2) = isRatC c2.
Proof.
move=> c1 c2 Hc; apply/idP/idP=> HH; last by apply: isRatC_add.
have->: c2 = (-c1) + (c1 + c2) by rewrite addrA addNr add0r.
by apply: isRatC_add; rewrite // isRatC_opp.
Qed.

Lemma isRatC_addl : forall c1 c2, isRatC c2 -> isRatC (c1 + c2) = isRatC c1.
Proof. by move=> c1 c2; rewrite addrC; exact: isRatC_addr. Qed.

Lemma isRatC_inv : forall c, isRatC c^-1 = isRatC c.
Proof.
have F1: forall b, GRing.unit ((-1)^+b : C).
  by move=> b; apply: GRing.unitr_exp; rewrite unitr_opp unitr1.
have F2: forall (b : bool), ((-1)^+b)^-1 = (-1)^+b :> C.
  by case; rewrite !(invrN,invr1).
have F3: forall n, GRing.unit ((n.+1)%:R : C).
  by move=> n; rewrite ?GRing.unitfE; move/GRing.charf0P: Cchar => ->.
move=> c; apply/isRatCP/isRatCP=> [] [b [[[|n] d] H]].
- exists true; exists (0,1)%N.
  by move: H; rewrite !(mulr0,mul0r); move/eqP; rewrite GRing.invr_eq0; move/eqP.
- exists b; exists (d.+1,n).
  rewrite -[c]invrK H !invr_mul ?(GRing.unitr_mulr,GRing.unitr_inv) //=.
  by rewrite invrK F2 -!mulrA [(-1) ^+ b * _]mulrC !mulrA.
- exists true; exists (0,1)%N.
  by move: H; rewrite !(mulr0,mul0r); move/eqP; rewrite -GRing.invr_eq0; move/eqP.
exists b; exists (d.+1,n); rewrite H.
rewrite !invr_mul ?(GRing.unitr_mulr,GRing.unitr_inv)  //=.
by rewrite invrK [_^+ _ * _]mulrC -!mulrA; congr (_ * _); rewrite F2 mulrC.
Qed.

Lemma isRatC_mul : forall c1 c2, isRatC c1 -> isRatC c2 -> isRatC (c1 * c2).
Proof.
move=> c1 c2; case/isRatCP=> b1 [[n1 d1] ->]; case/isRatCP=> b2 [[n2 d2] ->].
apply/isRatCP; exists (b1!=b2); exists (n1 * n2,(d1.+1 * d2.+1).-1)%N.
have->: (-1) ^+ (b1 != b2) = (-1) ^+ b1 * (-1) ^+ b2 :> C.
  by case: b1; case: b2; rewrite ?(mulNr,mul1r,opprK).
rewrite !natr_mul prednK // -!mulrA; congr (_ * _).
rewrite [_^+b2 * (n1%:R *_)]mulrC -!mulrA; congr (_ * _).
rewrite natr_mul invr_mul; last 2 first.
- by rewrite ?GRing.unitfE; move/GRing.charf0P: Cchar => ->.
- by rewrite ?GRing.unitfE; move/GRing.charf0P: Cchar => ->.
by rewrite mulrC -!mulrA mulrC -!mulrA.
Qed.

Lemma isRatC_mulr : forall c1 c2, c1 !=0 -> isRatC c1 -> isRatC (c1 * c2) = isRatC c2.
Proof.
move=> c1 c2 Hd Hc; apply/idP/idP=> HH; last by apply: isRatC_mul.
have->: c2 = (c1^-1) * (c1 * c2) by rewrite mulrA mulVf // mul1r.
by apply: isRatC_mul; rewrite // isRatC_inv.
Qed.

Lemma isRatC_mull : forall c1 c2, c2 !=0 -> isRatC c2 -> isRatC (c1 * c2) = isRatC c1.
Proof. by move=> c1 c2; rewrite mulrC; exact: isRatC_mulr. Qed.

Lemma isRatC_conj : forall c, isRatC c -> c^* = c.
Proof.
move=> c; case/isRatCP=> b [[n d]] ->.
by rewrite !rmorphM conjC_inv !conjC_nat rmorph_sign.
Qed.

Lemma isRatC_nat: forall n, isRatC n%:R.
Proof.
move=> n; apply/isRatCP; exists false; exists (n,0)%N.
by rewrite expr0 mul1r invr1 mulr1.
Qed.

Definition isNatC (c: C) : bool :=
 match getRatC c with (b,n,d) => c == (n %/ d.+1)%:R end.

Lemma isNatCP: forall c, reflect (exists n, c = n%:R) (isNatC c).
Proof.
move=> c; apply: (iffP idP)=>[|[n->]].
  by rewrite /isNatC; case getRatC=> [[b n] d]; move/eqP->; 
     exists (n %/ d.+1)%N.
move: (isRatC_nat n); rewrite /isRatC /isNatC; case getRatC=> [[b1 n1] d1].
have Hnd: GRing.unit (d1.+1%:R : C).
  by rewrite GRing.unitfE; move/GRing.charf0P: Cchar=> ->.
case: b1.
  rewrite expr1; move/eqP=> HC.
  have: (n1 + n * d1.+1)%:R = 0 :> C.
    rewrite natr_add natr_mul HC -!mulrA mulVr //.
    by rewrite mulr1 mulN1r subrr.
  move/eqP; move/GRing.charf0P: Cchar=> ->; rewrite addn_eq0.
  by case/andP; move/eqP=> ->; case: {HC}n.
rewrite mul1r;move/eqP=> Hn.
pose m := (n * d1.+1)%N.
have F1: n1%:R = m%:R :> C.
  by rewrite /m natr_mul Hn -mulrA mulVr // mulr1.
suff ->: n1 = m by rewrite mulnK.
case: (leqP n1 m)=> HN.
  suff F2: (m - n1 == 0)%N by rewrite -(subnKC HN) (eqP F2) addn0.
  by move/GRing.charf0P: Cchar=> <-; rewrite natr_sub // F1 subrr.
have Hnn := ltnW HN.
have F2: (n1 - m == 0)%N.
  by move/GRing.charf0P: Cchar=> <-; rewrite natr_sub // F1 subrr.
by rewrite -(subnKC Hnn) (eqP F2) addn0.
Qed.

Lemma isNatC_isRatC: forall c, isNatC c -> isRatC c.
Proof.
move=> c; case/isNatCP=> n ->; exact: isRatC_nat.
Qed.

Lemma isNatC_nat: forall n, isNatC (n%:R).
Proof. by move=> n; apply/isNatCP; exists n. Qed.

Lemma isNatC_add: forall c1 c2, isNatC c1 -> isNatC c2 -> isNatC (c1 + c2).
Proof.
move=> c1 c2; case/isNatCP=> n1 ->; case/isNatCP=> n2 ->.
by rewrite -natr_add isNatC_nat.
Qed.

Lemma isNatC_mul: forall c1 c2, isNatC c1 -> isNatC c2 -> isNatC (c1 * c2).
Proof.
move=> c1 c2; case/isNatCP=> n1 ->; case/isNatCP=> n2 ->.
by rewrite -natr_mul isNatC_nat.
Qed.

Lemma isNatC_sum: 
   forall (I : Type) (r : seq I) (P : pred I) (F : I -> C),
   (forall i, P i -> isNatC  (F i)) -> isNatC (\sum_(j <- r | P j) F j).
Proof.
move=> i r P F1 H; elim: r=> [|y r Hrec].
  by rewrite big_nil=> *; exact: (isNatC_nat 0).
rewrite big_cons; case E1: (P _)=> //.
by apply: isNatC_add=> //; exact: H.
Qed.

Lemma isNatCMn: forall x n, isNatC x -> isNatC (x*+n).
Proof.
move=> x; elim=> [|n IH Hx]; first by rewrite mulr0n (isNatC_nat 0).
by rewrite mulrSr isNatC_add // IH.
Qed.

Lemma posC_isNatC : forall c, isNatC c -> 0 <= c.
Proof.
by move=> c; case/isNatCP=> n ->; exact: leC_nat.
Qed.

Lemma isNatC_conj : forall c, isNatC c -> c^* = c.
Proof.
by move=> c; case/isNatCP=> n ->; exact: conjC_nat.
Qed.


Lemma isNatC_sum_eq1 : 
   forall (I : eqType) (r : seq I) (P : pred I) (F : I -> C),
   (forall i, P i -> isNatC (F i)) -> uniq r ->
   \sum_(j <- r | P j) F j = 1%:R ->
   (exists i, [/\ i \in r, P i, F i = 1 &
               forall j, j!=i -> j \in r -> P j -> F j = 0]).
Proof.
move=> I r P F HN; elim: r=> [_|y r Hrec].
  by rewrite big_nil; move/eqP; rewrite eq_sym (negPf (nonzero1r _)).
rewrite cons_uniq; case/andP=> [Hyr Hu].
rewrite big_cons; case HP: (P _)=> Hs; last first.
  case: Hrec=> // => i [Hin HPi HFi HF]; exists i; split=> //.
    by rewrite in_cons Hin orbT.
  move=> j Hji; rewrite in_cons; case/orP=> //; last by exact: HF.
  by move/eqP->; rewrite HP.
case/isNatCP: (HN _ (idP HP))=> n Hn.
have: isNatC (\sum_(j <- r | P j) F j) by apply: isNatC_sum.
case/isNatCP=> m Hm.
move: Hs; rewrite Hn Hm -natr_add.
case: n Hn=> [|n Hn]; case: m Hm=>[|m Hm].
- by move=> _ _; move/eqP; rewrite eq_sym (negPf (nonzero1r _)).
- case: m Hm.
    move=> Hs HF _; case: Hrec=> // => j [HInj HPj HFj HF0].
    exists j; split=> //; first by rewrite in_cons HInj orbT.
    move=> k Hk; rewrite in_cons; case/orP; first by move/eqP->.
    by exact: HF0.
  move=> n _ _.
  rewrite -[1%:R]add0r add0n -addn1 natr_add => HH.
  by move: (addIr HH); move/eqP; move/charf0P: Cchar->.
- case: n Hn=> [Hn Hs _|n Hn Hs].
    exists y; split=> //; first by rewrite in_cons eqxx.
    move=> j Hjy; rewrite in_cons; case/orP; first by rewrite (negPf Hjy).
    move=> Hj HPj; apply: (posC_sum_eq0 _ Hs)=> //.
    move=> i HPI; apply: posC_isNatC; exact: HN.
  rewrite -[1%:R]add0r addn0 -addn1 natr_add => HH.
  by move: (addIr HH); move/eqP; move/charf0P: Cchar->.
rewrite -[1%:R]add0r addnS -addn1 natr_add => HH.
by move: (addIr HH); move/eqP; move/charf0P: Cchar->.
Qed.
	
Section Main.

Variable (gT : finGroupType).

Hypothesis groupC : group_closure_field C gT.

Let pGroupG (G: {group gT}) : [char C]^'.-group G.
Proof.
by move=> G; apply: sub_pgroup (pgroup_pi G)=> i _; rewrite inE /= Cchar.
Qed.

Section FixGroup.

(* Our group *)
Variable G : {group gT}.

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
rewrite -(Wedderburn_sum sG (pGroupG _)).
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
rewrite -[regular_repr _ _ _]mul1mx -(Wedderburn_sum_id sG (pGroupG _)).
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

Lemma sg2bi_ord : forall (i : sG), (enum_rank i < size base_irr)%N.
Proof. by move=> i; rewrite size_map -cardE. Qed.

Definition sg2bi i := Ordinal (sg2bi_ord i).

Lemma bi2sg_ord : forall (i : 'I_(size base_irr)), (i < #|sG|)%N.
Proof. by case=> i; rewrite size_map -cardE. Qed.

Definition bi2sg i := enum_val (Ordinal (bi2sg_ord i)).

Lemma bi2sgK: cancel bi2sg sg2bi.
Proof. by case=> i Hi; apply/val_eqP; rewrite /= enum_valK. Qed.

Lemma sg2biK: cancel sg2bi bi2sg.
Proof. 
by move=> i; rewrite -{2}(enum_rankK i); congr enum_val; apply/val_eqP.
Qed.

Definition ncoord (i: sG) c : C^o :=
 coord base_irr c (sg2bi i).

Lemma ncoord_sum: forall x, x \in 'CL[C](G) -> x = \sum_i ncoord i x *: \chi_ i.
Proof.
move=> x Hx.
have F1:  {on [pred i | xpredT i], bijective bi2sg}.
  by apply: onW_bij; exists sg2bi; [exact: bi2sgK | exact: sg2biK ].
rewrite (reindex _ F1) /=.
have F2: x \in span base_irr.
  move: (is_basis_span base_irr_basis).
  by rewrite /is_span; move/eqP->.
rewrite {1}(coord_span F2); apply: eq_bigr=> i _; congr (_ *: _).
  by rewrite /ncoord bi2sgK.
rewrite  (nth_map [1 sG]%irr).
  by congr (\chi_ _); rewrite /bi2sg (enum_val_nth [1 sG]%irr).
rewrite -cardE; apply: bi2sg_ord.
Qed.

Lemma ncoord_is_linear : forall (i : sG), linear (ncoord i).
Proof.
by move=> i k c1 c2; rewrite /ncoord linearD linearZ !ffunE.
Qed.

Canonical Structure ncoord_linear i := Linear (ncoord_is_linear i).

Lemma ncoordE : forall  (f : sG -> C)  x, x \in 'CL[C](G) -> 
   x = \sum_i (f i) *: \chi_ i -> forall i, f i = ncoord i x.
Proof.
move=> f x Hin Hx i.
suff: (fun j => ncoord (bi2sg j) x -  f (bi2sg j)) =1 (fun _ => 0).
  by move/(_ (sg2bi i)); rewrite sg2biK; move/eqP; rewrite subr_eq0; move/eqP.
move/freeP: free_base_irr; apply.
have F1:  {on [pred i | xpredT i], bijective sg2bi}.
  by apply: onW_bij; exists bi2sg; [exact: sg2biK | exact: bi2sgK ].
rewrite (reindex _ F1) /=.
rewrite (eq_bigr (fun j => ncoord j x *: \chi_j -  f j *: \chi_j)).
  by rewrite sumr_sub -Hx -ncoord_sum // subrr.
by move=> j _; rewrite sg2biK scaler_subl // (nth_map [1 sG]%irr) -?cardE
                       // nth_enum_rank.
Qed.

Lemma ncoord_chi: forall i j, ncoord j (\chi_i) = (i == j)%:R.
Proof.
move=> i j; apply: sym_equal; apply: (@ncoordE (fun j => (i == j)%:R)).
  exact: character_of_in_class_fun.
rewrite (bigD1 i) // big1 /= ?(addr0,eqxx,scale1r) // => i1.
by rewrite eq_sym; case: (_ == _)=> //; rewrite scale0r.
Qed.

Lemma ncoord_character_of : forall n (rG : mx_representation C G n) (i: sG),
  isNatC (ncoord i (character_of rG)).
Proof.
move=> n rG i.
pose sG':= DecSocleType rG.
suff->: character_of rG = \sum_i (character_of (irr_repr (irr_comp sG (socle_repr (i: sG'))))) *+ socle_mult i.
  rewrite linear_sum; apply: isNatC_sum=> j _ /=.
  by rewrite linearMn; apply: isNatCMn; rewrite /= ncoord_chi; apply isNatC_nat.
apply/ffunP=> g; rewrite !(sum_ffunE,ffunE).
case: (boolP (_ \in _))=> Hin; last first.
  rewrite mul0r big1 ?ffunE // => j _.
  by rewrite (class_fun0 _ Hin) ?mul0rn // memvMn // character_of_in_class_fun.
have F1: (Socle (DecSocleType rG) :=: 1%:M)%MS.
  rewrite reducible_Socle1 //; exact: mx_Maschke.
rewrite mul1r -(mxtrace_submod1 (Socle_module (DecSocleType rG)) F1) // mxtrace_Socle=> //.
apply: eq_bigr=> i1 _ /=.
rewrite  ffunMn !ffunE Hin mul1r; congr (_ *+ _).
by apply: mxtrace_rsim=> //; apply: rsim_irr_comp=> //; apply/submod_mx_irr; apply: socle_simple.
Qed.

Lemma add_mx_repr :
 forall m n 
  (rG1 : mx_representation C G m) (rG2 : mx_representation C G n),
  mx_repr G (fun g => block_mx (rG1 g) 0 0 (rG2 g)).
Proof.
move=> m n repr1 repr2; split=> [|x y Hx Hy].
  by rewrite !repr_mx1 -scalar_mx_block.
by rewrite mulmx_block !(mulmx0,mul0mx,addr0,add0r,repr_mxM).
Qed.

Definition add_repr m n
  (rG1 : mx_representation C G m) (rG2 : mx_representation C G n)
  := MxRepresentation (add_mx_repr rG1 rG2).

Lemma character_of_morph : forall m n
  (rG1 : mx_representation C G m) (rG2 :  mx_representation C G n),
  character_of (add_repr rG1 rG2) = character_of rG1 + character_of rG2.
Proof.
move=> m n rG1 rG2.
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

Lemma xchar_singleton : forall n g (rG : mx_representation C G n),
  let chi := (character_of rG) in
  g \in G -> xchar chi (gring_row (regular_repr C G g)) = chi g.
Proof.
move=> n g rG chi Hg.
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
    by case: (Wedderburn_is_id (pGroupG _) i)=> _ Hi Hj _; exact: Hj.
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
  (* mimicking ring *)
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

Lemma chi_inv : forall (i: sG) g, g \in G -> abelian G -> \chi_i g^-1%g = (\chi_i g)^*.
Proof.
move=> i g Hin AG.
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
  rewrite !ffunE groupV Hin {1}mul1r {1}mul1r repr_mxV //.
  by rewrite irr_scal -scalemx1 (invmxZ _ (unitmx1 _ _)) invmx1 
             !mxtraceZ mxtrace1 irr_degree_abelian // !mulr1.
rewrite normC_inv.
suff->: normC (\chi_ i g) = 1 by rewrite invr1 mul1r.
apply/eqP; rewrite -(posC_unit_exp #[g]) ?posC_norm //.
rewrite -normC_exp -normC1; apply/eqP; congr (normC).
have<-: \chi_i 1%g = 1 by rewrite chi1 irr_degree_abelian.
rewrite -(expg_order g) !ffunE irr_scal Hin mul1r -scalemx1 mxtraceZ.
suff->: irr_repr i (g ^+ #[g]) = u^+#[g] *: 1%:M.
  by rewrite mxtraceZ mxtrace1 irr_degree_abelian // groupX // !mulr1 mul1r.
elim: #[_]=> [|n IH]; first by rewrite expg0 expr0 scale1r repr_mx1.
by rewrite expgS repr_mxM ?groupX // IH irr_scal !scalemx1 -scalar_mxM -exprS.
Qed.

End FixGroup.

Section More.

Variable G : {group gT}.

Let sG : irrType C G := DecSocleType (regular_repr C G).

Local Notation "\chi_ i" :=  (irr_class_fun i) (at level 3).

Lemma character_of_inv : forall n (rG: mx_representation C G n) g,
  character_of G rG g^-1%g = (character_of G rG g)^*.
Proof.
move=> n rG g.
case: (boolP (g \in G))=> Hin; last first.
  by rewrite (class_fun0 (character_of_in_class_fun _) Hin); rewrite -groupV // in Hin;
     rewrite (class_fun0 (character_of_in_class_fun _) Hin) conjC0.
have F1: (<[g]> \subset G) by rewrite cycle_subG.
pose rG' := subg_repr rG F1.
have F2: forall g1, g1 \in <[g]> -> character_of G rG g1 = character_of <[g]> rG' g1.
  by move=> g1 Hg1; rewrite !ffunE Hg1; move/subsetP: (F1)->.
rewrite !F2 ?(groupVr,cycle_id) //. 
rewrite (ncoord_sum (character_of_in_class_fun _)).
rewrite sum_ffunE 2!ffunE rmorph_sum; apply: eq_bigr=> i _.
rewrite ffunE chi_inv //.
have F3: isNatC (ncoord i (character_of <[g]> rG')).
  apply: ncoord_character_of.
rewrite -{1}(isNatC_conj F3) {1}/GRing.scale /= -rmorphM ?ffunE //.
  apply: cycle_id.
apply: cycle_abelian.
Qed.

Implicit Types f g : {ffun gT -> C^o}.

Definition inner_prod f g := 
  #|G|%:R^-1 * \sum_(i < #|G|) f (enum_val i) * (g (enum_val i))^*.

Local Notation "'[ f , g ]" := (inner_prod f g).

Let card_neq0 : #|G|%:R^-1 != 0 :> C.
Proof.
rewrite invr_eq0; move/GRing.charf0P: Cchar->.
by move: (cardG_gt0 G); case: #|_|.
Qed.

Let card_conj : (#|G|%:R^-1)^* = #|G|%:R^-1.
Proof.
by rewrite posC_conjK // posC_inv leC_nat.
Qed.

Lemma inner_conj : forall f g, '[f,g] = '[g,f]^*.
Proof.
move=> f g; rewrite /inner_prod rmorphM card_conj.
congr (_ * _); rewrite rmorph_sum; apply: eq_bigr=> i _.
by rewrite rmorphM conjCK mulrC.
Qed.
 
Lemma posC_inner_prod : forall f, 0 <= '[f, f].
Proof. 
move=> f; apply: posC_mul; first by rewrite posC_inv leC_nat.
rewrite posC_sum // => i _; exact: posC_norm.
Qed.

Lemma inner_prod0: forall f, f \in 'CL[C](G) -> ('[f, f] == 0) = (f == 0).
Proof.
move=> f Hf; apply/eqP/eqP=> Hp; last first.
  by rewrite Hp /inner_prod big1 ?mulr0 // => i _; rewrite !ffunE mul0r.
apply/ffunP=> g; rewrite ffunE.
case: (boolP (g \in G))=> Hin; last by rewrite (class_fun0 _ Hin).
apply/eqP; rewrite -normC_eq0; apply/eqP.
rewrite -[g](@gring_indexK _ G) //.
move: Hp; move/eqP; rewrite /inner_prod mulf_eq0; case/orP=> [|Hp].
  by rewrite (negPf card_neq0).
apply: (posC_sum_eq0 _ (eqP Hp))=> //; first by move=>*; exact: posC_norm.
rewrite /index_enum -enumT.
apply/(nthP (gring_index G g)); exists (gring_index G g).
  by rewrite -cardT card_ord.
by apply/val_eqP=> //=; rewrite nth_enum_ord.
Qed.

Definition inner_prodb f := inner_prod^~ f.

Lemma inner_prodbE: forall f g, inner_prodb f g = inner_prod g f.
Proof. by []. Qed.

Lemma inner_prodb_is_linear : forall f, linear (inner_prodb f).
Proof.
move=> f k g1 g2.
rewrite /inner_prodb /inner_prod.
rewrite {1}scaler_mulr -{1}scaler_addr; congr (_ * _).
rewrite {1}scaler_sumr /= -{1}big_split /=; apply: eq_bigr=> i _.
by rewrite scaler_mull -mulr_addl !ffunE.
Qed.

Canonical Structure inner_prodb_linear f := Linear (inner_prodb_is_linear f).

Lemma inner_prod_is_additive : forall f, additive (inner_prod f).
Proof.
move=> f g1 g2.
rewrite /inner_prod /inner_prod.
rewrite -mulr_subr; congr (_ * _).
rewrite -sumr_sub; apply: eq_bigr=> i _.
by rewrite !ffunE rmorph_sub // mulr_subr.
Qed.

Canonical Structure inner_prod_additive f := 
  Additive (inner_prod_is_additive f).

Lemma inner_prodZ : forall k f g, '[f, k *: g] = k^* *: '[f,g].
Proof.
move=> k f g; rewrite /inner_prod scaler_mulr; congr (_ * _).
rewrite scaler_sumr; apply: eq_bigr=> i _.
by rewrite scaler_mulr {2}/GRing.scale /= !ffunE rmorphM.
Qed.

Lemma chi_orthonormal : forall i j: sG, '[\chi_i,\chi_j] = (i == j)%:R.
Proof.
move=> i j.
rewrite -chi_orthogonal_relation; congr (_ * _).
by apply: eq_bigr=> k _; rewrite character_of_inv.
Qed.

Lemma inner_prod_character :
  forall m n (rG1 : mx_representation C G m) (rG2 : mx_representation C G n),
    '[character_of G rG1,character_of G rG2] =
    \sum_(i:sG) (ncoord i (character_of G rG1)) * (ncoord i (character_of G rG2)).
Proof.
move=> m n rG1 rG2.
rewrite (ncoord_sum (character_of_in_class_fun _))
        [character_of _ rG2](ncoord_sum (character_of_in_class_fun _)).
rewrite -inner_prodbE linear_sum /=.
apply: eq_bigr=> i _; rewrite inner_prodbE.
rewrite raddf_sum /= {1}(bigD1 i) // big1 //= => [|j Hj];
    rewrite inner_prodZ -{1}inner_prodbE {1}[inner_prodb _ _]linearZ /= 
            inner_prodbE chi_orthonormal; last first.
  by rewrite eq_sym (negPf Hj) !scaler0.
rewrite eqxx.
rewrite linear_sum {1}(bigD1 i) // big1 /=; last first.
  by move=> j Hj; rewrite linearZ /= ncoord_chi (negPf Hj) scaler0.
rewrite linear_sum {1}(bigD1 i) // big1 /=; last first.
  by move=> j Hj; rewrite linearZ /= ncoord_chi (negPf Hj) scaler0.
apply: sym_equal; rewrite {1}addr0 {1}addr0 {1}linearZ {1}linearZ /=.
rewrite ncoord_chi eqxx -scaler_mulr -scaler_mull mulr1 addr0 isNatC_conj //.
exact: ncoord_character_of.
Qed.

Lemma inner_prod_character_nat :
  forall m n (rG1 : mx_representation C G m) (rG2 : mx_representation C G n),
    isNatC '[character_of G rG1,character_of G rG2].
Proof.
move=> m n rG1 rG2.
rewrite inner_prod_character; apply: isNatC_sum=> i _.
apply: isNatC_mul; exact: ncoord_character_of.
Qed.
 
Lemma inner_prod_characterC :
  forall m n (rG1 : mx_representation C G m) (rG2 : mx_representation C G n),
    '[character_of G rG1,character_of G rG2] = 
    '[character_of G rG2,character_of G rG1].
Proof.
move=> m n rG1 rG2.
by rewrite !inner_prod_character; apply: eq_bigr=> i _; rewrite mulrC.
Qed.

Lemma character_of_irreducibleP : 
  forall n (rG : mx_representation C G n),
  reflect
    (exists i : sG, character_of G rG = \chi_i)
    ('[character_of G rG, character_of G rG] == 1).
Proof.
move=> n rG; apply: (iffP idP); last first.
  by case=> i->; rewrite chi_orthonormal eqxx.
rewrite inner_prod_character.
move/eqP=> HH; case: (isNatC_sum_eq1 _ _ HH).
- by move=> i _; apply: isNatC_mul; exact: ncoord_character_of.
- by rewrite /index_enum -enumT; exact: enum_uniq.
move=> i [Hin _ HF HG]; exists i.
rewrite (ncoord_sum (character_of_in_class_fun _)); apply: sym_equal.
rewrite [\chi_i](ncoord_sum (character_of_in_class_fun _)).
apply: eq_bigr=> k _; congr (_ *: _).
rewrite ncoord_chi; case: eqP=> [<-|]; last first.
  move/eqP; rewrite eq_sym=> Hik.
  have F1: k \in index_enum (socle_finType sG).
    rewrite /index_enum -enumT.
    apply/(nthP [1 sG]%irr); exists (enum_rank k)=> //.
      case: enum_rank=> /= m; first by rewrite cardT /=.
    by apply/val_eqP; rewrite nth_enum_rank.
  move: (HG _ Hik F1 is_true_true).
  case/isNatCP: (ncoord_character_of rG k)=> m ->.
  by rewrite -natr_mul; move/eqP; move/charf0P: Cchar->; case: m.
case/isNatCP: (ncoord_character_of rG i) HF=> m ->.
rewrite -natr_mul; case: m=> [|[|m]] //.
rewrite mulnS addSn -{2}[1]add0r -addn1 natr_add => HH1.
by move: (addIr HH1); move/eqP; move/charf0P: Cchar->.
Qed.

End More.

End Main.

End Character.