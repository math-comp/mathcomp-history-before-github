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
Lemma cfun2rv_morph_p : linear ffun2rv.
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

Inductive cfun_type : predArgType := ClassFun of {ffun gT -> R}.
Definition finfun_of_cfun A := let: ClassFun f := A in f.
Definition fun_of_cfun (f : cfun_type) x := finfun_of_cfun f x.
Coercion fun_of_cfun : cfun_type >-> Funclass.

Lemma finfun_of_cfunE: forall f x, finfun_of_cfun f x  = f x.
by [].
Qed.

Definition cfun_of_fun f := locked ClassFun [ffun i => f i].

Lemma cfunE : forall f, cfun_of_fun f =1 f.
Proof. by unlock cfun_of_fun fun_of_cfun => f i; rewrite /= ffunE. Qed.

Lemma cfunP : forall (f1 f2 : cfun_type), f1 =1 f2 <-> f1 = f2.
Proof.
move=> [f1] [f2]; split=> [/= eqf1f2 | -> //].
congr ClassFun; apply/ffunP=> i; exact: eqf1f2.
Qed.

Canonical Structure cfun_subType :=
  Eval hnf in [newType for finfun_of_cfun by cfun_type_rect].
Definition cfun_eqMixin := Eval hnf in [eqMixin of cfun_type by <:].
Canonical Structure cfun_eqType := 
  Eval hnf in EqType cfun_type cfun_eqMixin.
Definition cfun_choiceMixin := [choiceMixin of cfun_type by <:].
Canonical Structure cfun_choiceType :=
  Eval hnf in ChoiceType cfun_type cfun_choiceMixin.

Definition cfun_zero := cfun_of_fun (fun _ => 0).
Definition cfun_one := cfun_of_fun (fun _ => 1).
Definition cfun_opp (f : cfun_type) := cfun_of_fun (fun x => - f x).
Definition cfun_add (f g : cfun_type) := cfun_of_fun (fun x => f x + g x). 
Definition cfun_mul (f g : cfun_type) := cfun_of_fun (fun x => f x * g x). 

Fact cfun_addA : associative cfun_add.
Proof. by move=> f1 f2 f3; apply/cfunP=> i; rewrite !cfunE addrA. Qed.
Fact cfun_addC : commutative cfun_add.
Proof. by move=> f1 f2; apply/cfunP=> i; rewrite !cfunE addrC. Qed.
Fact cfun_add0 : left_id cfun_zero cfun_add.
Proof. by move=> f; apply/cfunP=> i; rewrite !cfunE add0r. Qed.
Fact cfun_addN : left_inverse cfun_zero cfun_opp cfun_add.
Proof. by move=> f; apply/cfunP=> i; rewrite !cfunE addNr. Qed.

Definition cfun_zmodMixin :=
  GRing.Zmodule.Mixin cfun_addA cfun_addC cfun_add0 cfun_addN.
Canonical Structure cfun_zmodType :=
  Eval hnf in ZmodType _ cfun_zmodMixin.

Fact cfun_mulA : associative cfun_mul.
Proof. by move=> f1 f2 f3; apply/cfunP=> i; rewrite !cfunE mulrA. Qed.
Fact cfun_mulC : commutative cfun_mul.
Proof. by move=> f1 f2; apply/cfunP=> i; rewrite !cfunE mulrC. Qed.
Fact cfun_1l : left_id cfun_one cfun_mul.
Proof. by move=> f; apply/cfunP=> i; rewrite !cfunE mul1r. Qed.
Fact cfun_mul_addl :  left_distributive cfun_mul cfun_add.
Proof. by move=> f1 f2 f3; apply/cfunP=> i; rewrite !cfunE mulr_addl. Qed.
Fact cfun1_nonzero :  cfun_one != 0.
Proof. 
apply/eqP; move/cfunP; move/(_ 1%g); rewrite !cfunE.
by move/eqP; rewrite oner_eq0.
Qed.

Definition cfun_ringMixin := 
  ComRingMixin cfun_mulA cfun_mulC cfun_1l cfun_mul_addl cfun1_nonzero.
Canonical Structure cfun_ringType := Eval hnf in RingType cfun_type cfun_ringMixin.
Canonical Structure cfun_comRingType := Eval hnf in ComRingType cfun_type cfun_mulC.

Definition cfun_scale k (f : cfun_type) :=  cfun_of_fun (fun x => k * f x).

Fact cfun_scaleA : forall k1 k2 f, 
  cfun_scale k1 (cfun_scale k2 f) = cfun_scale (k1 * k2) f.
Proof. by move=> k1 k2 f; apply/cfunP=> i; rewrite !cfunE mulrA. Qed.
Fact cfun_scale1 : left_id 1 cfun_scale.
Proof. by move=> f; apply/cfunP=> i; rewrite !cfunE mul1r. Qed.
Fact cfun_scale_addr : forall k, {morph (cfun_scale k) : x y / x + y}.
Proof. by move=> k f g; apply/cfunP=> i; rewrite !cfunE mulr_addr. Qed.
Fact cfun_scale_addl : forall u, {morph (cfun_scale)^~ u : k1 k2 / k1 + k2}.
Proof. by move=> k f g; apply/cfunP=> i; rewrite !cfunE mulr_addl. Qed.

Definition cfun_lmodMixin := 
  LmodMixin cfun_scaleA cfun_scale1 cfun_scale_addr cfun_scale_addl.
Canonical Structure cfun_lmodType :=
  Eval hnf in LmodType R cfun_type cfun_lmodMixin.

Lemma sum_cfunE:  
  forall I (r : seq I) (P : pred I) (F : I -> cfun_type),
  \big[+%R/0]_(i <- r | P i) F i = 
     cfun_of_fun (fun x => \big[+%R/0]_(i <- r | P i) (F i x)).
Proof.
move=> i r P F1; elim: r=> [|y r Hrec].
  by rewrite !big_nil; apply/cfunP=> j; rewrite !cfunE big_nil.
by rewrite big_cons Hrec; case F2: (P _); apply/cfunP=> x;
   rewrite !cfunE big_cons F2.
Qed.

Lemma cfunMn : forall (f : cfun_type) n x, (f *+ n) x = f x *+ n.
Proof.
by move=> f n x; elim: n => [|n IHn]; rewrite ?mulrS !cfunE -?IHn //. 
Qed.

Definition base_cfun : seq cfun_type :=
  (map (fun i : 'I_#|classes G| => cfun_of_fun (fun x => (x \in  (enum_val i))%:R))
    (enum 'I_#|classes G|)).

Definition cfun2rv f := ffun2rv (finfun_of_cfun f).

Lemma cfun2rv_morph_p : linear cfun2rv.
Proof. 
move=> k x y; rewrite -ffun2rv_morph_p; congr ffun2rv.
by apply/ffunP=> i; rewrite !ffunE !finfun_of_cfunE !cfunE.
Qed.

Canonical Structure cfun2rv_morph := Linear cfun2rv_morph_p.

Lemma cfun2rv_bij : bijective cfun2rv.
Proof.
case: (ffun2rv_bij R gT) => f H1f H2f.
exists (fun x  => ClassFun (f x))=> [[g]|x]; last by exact: (H2f x).
congr ClassFun; exact: (H1f g).
Qed.

Definition cfunVectMixin := VectMixin cfun2rv_morph_p cfun2rv_bij.
Canonical Structure cfunVectType := VectType R cfunVectMixin.

Definition class_fun := span base_cfun.

Lemma cfun_memP : forall (f : cfun_type),
  reflect 
    ((forall x, x \notin G -> f x = 0) /\
     (forall x y, x \in G -> y \in G -> f (x ^ y) = f x))
    (f \in class_fun).
Proof.
move=> f; apply: (iffP idP)=> [|[Hg Hc]].
  move/coord_span->; split=> [x Inx|].
    rewrite sum_cfunE cfunE; apply: big1=> i _.
    have: base_cfun`_i \in base_cfun by apply: mem_nth.
    case/mapP=> j Hj ->; rewrite !cfunE.
    have [y Gy ->] := imsetP (enum_valP j).
    move/subsetP: (class_subG Gy (subxx _)); move/(_ x); move/contra.
    by move/(_ Inx); case: (_ \in _)=> //; rewrite mulr0.
  move=> x y Hx Hy.
  apply/eqP; rewrite -subr_eq0; apply/eqP.
  rewrite !sum_cfunE !cfunE -sumr_sub; apply: big1=> i _.
  set u := coord _ _ _; rewrite !cfunE.
  have: base_cfun`_i \in base_cfun by apply: mem_nth.
  case/mapP=> j Hj ->; rewrite !cfunE.
  have [z Gz ->] := imsetP (enum_valP j).
  by rewrite (class_transl _ (memJ_class _ _)) // subrr.
suff<-: \sum_(C \in (classes G)) 
           (f (repr C)) *: cfun_of_fun (fun x => (x \in C)%:R) = f.
  apply: memv_sum=> i Hi.
  apply: memvZl; apply: memv_span;  apply/mapP.
  by exists (enum_rank_in (classes1 G) i); [rewrite mem_enum | rewrite enum_rankK_in].
apply/cfunP=> g; rewrite sum_cfunE cfunE.
case HgG: (g \in G); last first.
  rewrite Hg ?HgG //; apply: big1=> i Hi; rewrite !cfunE.
  have [x Gx ->{k}] := imsetP Hi.
  case Hgx: (_ \in _); last by rewrite mulr0.
  move/subsetP: (class_subG Gx (subxx G)).
  by move/(_ g (idP Hgx)); rewrite HgG.
rewrite (bigD1 (g ^: G : set_of_finType _)) /=; last by apply/imsetP; exists g.
rewrite !cfunE big1.
  rewrite class_refl.
  case: (repr_class G g)=> x Hx ->; rewrite Hc // addr0; exact: mulr1.
move=> i; case/andP; case/imsetP=> y Hy -> Hz.
rewrite !cfunE; case E1: (_ \in _); last by rewrite mulr0.
by case/negP: Hz; rewrite eq_sym; apply/eqP; apply: class_transr.
Qed.

Lemma cfun0 : forall (f : cfun_type) x, 
  x \notin G -> f \in class_fun -> f x = 0.
Proof. by move=> f x Hx; case/cfun_memP=> HH _; exact: HH. Qed.

Lemma cfunJ : forall (f : cfun_type) x y, 
   x \in G -> y \in G -> f \in class_fun -> f (x ^ y) = f x.
Proof. by move=> f x y Hx Hy; case/cfun_memP=> _ HH; exact: HH. Qed.

Lemma cfun_sum : forall (F: gT -> R),
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

Lemma cfun_free : free base_cfun.
Proof.
apply/freeP=> s S0 i.
have Hi: i < #|classes G| by case: i=> /= m; rewrite size_map -cardE card_ord.
move/cfunP: S0; move/(_ (repr (enum_val (Ordinal Hi)))).
rewrite sum_cfunE !cfunE (bigD1 i) //= big1.
 rewrite !cfunE (nth_map (Ordinal Hi)) // ?cfunE; last first.
   by rewrite -cardE card_ord.
 rewrite (nth_ord_enum  _ (Ordinal Hi)).
 have [y Gy ->] := imsetP (enum_valP (Ordinal Hi)).
 case: (repr_class G y)=> x Hx ->.
 by rewrite memJ_class // addr0 => <-; apply: sym_equal; exact: mulr1.
move=> j Dij.
rewrite (nth_map (Ordinal Hi)) ?cfunE ?ffunE; last first.
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

Lemma dim_cfun : \dim class_fun = #|classes G|.
Proof.
by move: cfun_free; rewrite /free size_map -cardE card_ord; move/eqP.
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
Hypothesis repC_unit_exp: forall x n, repC x -> ((x^+n.+1 == 1) = (x == 1)).
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

Lemma leC_refl: reflexive leC.
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

Lemma leC_trans: transitive leC.
Proof.
move=> x y z Hx Hy.
by move: (repCD Hy Hx); rewrite addrA subrK.
Qed.

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

Lemma posC_unit_exp: forall x n, 0 <= x ->  (x ^+ n.+1 == 1) = (x == 1).
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

Variable sqrC: C -> C.
Hypothesis sqrCK : forall c, (sqrC c) ^+ 2 = c.
Hypothesis repC_sqr : forall c, repC (sqrC c) = repC c.
Hypothesis sqrC_mul : {morph sqrC: x y / x * y}.

Lemma sqrC_sqr : forall c, (sqrC (c^+2) == c) || (sqrC (c^+2) == -c).
Proof.
move=> c; set sc := sqrC _.
suff: (sc - c) * (sc + c) == 0.
  rewrite mulf_eq0; case/orP; first by rewrite subr_eq0=>->.
  by rewrite orbC -{1}[c]opprK subr_eq0=>->.
rewrite mulr_addr !mulr_subl addrA [c * _]mulrC subrK subr_eq0.
by rewrite -{2}[sc]expr1 -exprS sqrCK.
Qed.

Lemma sqrC0 : sqrC 0 = 0.
Proof. 
have:= sqrCK 0; rewrite exprS expr1.
by move/eqP; rewrite mulf_eq0; case/orP; move/eqP.
Qed.

Lemma sqrC_eq0 : forall c, (sqrC c == 0) = (c == 0).
Proof.
move=> c; apply/eqP/eqP; last by move->; exact: sqrC0.
by rewrite -{2}[c]sqrCK=>->; rewrite exprS mul0r.
Qed.

Lemma sqrC_pos : forall c, (0 <= sqrC c) = (0 <= c).
Proof. by move=> c; rewrite /leC !subr0 repC_sqr. Qed.

Lemma sqrC_sqr_pos : forall c, 0 <= c -> sqrC (c^+2) = c.
Proof.
move=> c Hc; case/orP: (sqrC_sqr c)=>[|HH]; first by move/eqP.
suff->: c = 0 by rewrite exprS mul0r sqrC0.
apply: leC_anti=> //; rewrite /leC sub0r.
rewrite -(eqP HH) repC_sqr -[_^+_]subr0; by apply: posC_mul.
Qed.

Lemma sqrC1: sqrC 1 = 1.
Proof. by rewrite -{2}(sqrC_sqr_pos posC1) exprS mul1r. Qed. 
 
Definition normC x := sqrC (x * x^*).

Hypothesis normC_add: forall x y,  normC (x + y) <= normC x + normC y.
Hypothesis normC_add_eq: forall x y : C, normC (x + y) = normC(x) + normC(y) -> 
   (exists2 r, 0 <= r & ((x == r * y) || (y == r * x))).

Lemma posC_norm : forall x, 0 <= normC x.
Proof. 
move=> x; rewrite /leC !subr0 repC_sqr; exact: repC_pconj.
Qed.

Lemma normC_pos : forall c, 0 <= c -> normC c = c.
Proof.
by move=> c Hc; rewrite /normC posC_conjK // (sqrC_sqr_pos Hc).
Qed.

Lemma normC0 : normC 0 = 0.
Proof. by rewrite normC_pos // leC_refl. Qed.

Lemma normC_eq0 : forall c, (normC c == 0) = (c == 0).
Proof.
move=> c; apply/idP/eqP; last by move->; rewrite normC0.
rewrite sqrC_eq0 mulf_eq0; case/orP; first by move/eqP.
by rewrite conjC_eq0; move/eqP.
Qed.

Lemma normC1 : normC 1 = 1.
Proof. by rewrite normC_pos // posC1. Qed.

Lemma normC_mul :  {morph normC: x y / x * y}.
Proof.
move=> x y; rewrite /normC rmorphM -sqrC_mul -!mulrA; 
by congr sqrC; congr (_ * _); rewrite mulrC -!mulrA [y * _]mulrC.
Qed.

Lemma normC_exp : forall x n, normC (x^+n) = normC x ^+ n.
Proof.
move=> x; elim=> [|n IH]; first by rewrite !expr0 normC1.
by rewrite exprS normC_mul IH exprS.
Qed.

Lemma normC_conj: forall x, normC (x^*) = normC x.
Proof. by move=> x; rewrite /normC conjCK mulrC. Qed.

Lemma normC_inv : forall x, x^-1 = (normC x)^-2 * x^*.
Proof.
move=> x; case: (x =P 0)=> [->|]; first by rewrite conjC0 mulr0 invr0.
move/eqP=> Hx.
have F1: normC x ^+ 2 != 0.
  by rewrite exprS expr1; apply: mulf_neq0; rewrite normC_eq0.
apply: (mulfI F1); rewrite mulrA divff // mul1r sqrCK [x * _]mulrC.
by rewrite -mulrA divff // mulr1.
Qed.

Lemma conjC_inv: forall x, (x^-1)^* = (x^*)^-1.
Proof.
move=> x; rewrite normC_inv rmorphM conjCK.
rewrite (normC_inv x^*) conjCK; congr (_ * _).
rewrite normC_conj; apply: posC_conjK.
by rewrite posC_inv exprS expr1 posC_mul // posC_norm.
Qed.

Lemma normC_sum: 
   forall (I : eqType) (r : seq I) (P : pred I) (F : I -> C),
   normC (\sum_(i <- r | P i) F i) <= \sum_(i <- r | P i) normC(F i).
Proof.
move=> I r P F; elim: r=> [|i r Hrec].
  by rewrite !big_nil normC0 leC_refl.
rewrite !big_cons; case HP: (P _)=> //.
by apply: (leC_trans (normC_add _ _)); rewrite leC_add2l.
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

Let pGroupG : forall (G: {group gT}), [char C]^'.-group G.
Proof.
by move=> G; apply: sub_pgroup (pgroup_pi G)=> i _; rewrite inE /= Cchar.
Qed.

Section FixGroup.

(* Our group *)
Variable G : {group gT}.

Definition char n (f: gT -> 'M[C]_n) := 
 cfun_of_fun (fun g : gT => ((g \in G)%:R * \tr (f g))).

Lemma char1 : 
  forall n (rG : mx_representation C G n), char rG 1%g = n%:R.
Proof.
by move=> n rG; rewrite !cfunE group1 repr_mx1 mxtrace1 mul1r.
Qed.

Lemma char_sim : 
  forall n1 n2 (rG1: mx_representation C G n1) (rG2: mx_representation C G n2),
  mx_rsim rG1 rG2 -> char rG1 = char rG2.
Proof.
move=> n1 n2 rG1 rG2; case/mx_rsim_def=> M1 [M2] HM1M2 Hx.
apply/cfunP=> x; rewrite !cfunE; case H: (_ \in _); last by rewrite !mul0r.
by rewrite Hx // mxtrace_mulC mulmxA HM1M2 mul1mx.
Qed.

Lemma char_in_cfun : forall n (rG :  mx_representation C G n), 
  char rG \in 'CL[C](G).
Proof.
move=> n rG; apply/cfun_memP.
split=> [x|x y Hx Hy]; rewrite !cfunE.
  by case: (x \in G)=> //; rewrite mul0r.
by rewrite groupJ // Hx !mul1r !(repr_mxM,repr_mxV,groupM,groupV) //
           mxtrace_mulC mulmxK // repr_mx_unit.
Qed.  

Let sG := DecSocleType (regular_repr C G).

Inductive irr_class : predArgType :=
  IrrClass of sG.
Definition socle_of_irr_class  A := let: IrrClass i := A in i.

Canonical Structure irr_class_subType :=
  Eval hnf in [newType for socle_of_irr_class by irr_class_rect].
Definition irr_class_eqMixin := Eval hnf in [eqMixin of irr_class by <:].
Canonical Structure irr_class_eqType := 
  Eval hnf in EqType irr_class irr_class_eqMixin.
Definition irr_class_choiceMixin := [choiceMixin of irr_class by <:].
Canonical Structure irr_class_choiceType :=
  Eval hnf in ChoiceType irr_class irr_class_choiceMixin.
Definition irr_class_countMixin := [countMixin of irr_class by <:].
Canonical Structure irr_class_countType :=
  Eval hnf in CountType irr_class irr_class_countMixin.
Canonical Structure irr_class_subCountType :=
  Eval hnf in [subCountType of irr_class].
Definition irr_class_finMixin := [finMixin of irr_class by <:].
Canonical Structure irr_class_finType :=
  Eval hnf in FinType irr_class irr_class_finMixin.
Canonical Structure irr_class_subFinType :=
  Eval hnf in [subFinType of irr_class].

Coercion irr_cfun chi := 
  char (irr_repr (socle_of_irr_class chi)).

Definition irr_class1 := IrrClass (principal_comp sG).

Lemma irr_class1E : forall g, irr_class1 g = (g \in G)%:R.
Proof.
move=> g; case: (boolP (_ \in _))=> Hg; last first.
 by rewrite (cfun0 Hg) //; exact: char_in_cfun.
by rewrite cfunE Hg mul1r irr1_repr // mxtrace1 degree_irr1.
Qed.

Lemma card_irr_class : #|irr_class| = #|classes G|.
Proof.
rewrite -(card_irr sG) // card_sub.
by apply: eq_card=> i; rewrite !inE.
Qed.

Implicit Types chi : irr_class. 

Lemma chi1 : forall chi, chi 1%g = (irr_degree (socle_of_irr_class chi))%:R.
Proof.
by move=> i; rewrite cfunE group1 mul1r repr_mx1 mxtrace1.
Qed.

Lemma chi1_neq0: forall chi, chi 1%g != 0.
Proof.
move=> i; rewrite chi1; move/GRing.charf0P: Cchar=> ->.
by case: irr_degree (irr_degree_gt0 (socle_of_irr_class i)).
Qed.

Lemma sum_chi2 : \sum_(chi : irr_class) (chi 1%g) ^+ 2 = #|G|%:R.
Proof.
rewrite -(sum_irr_degree sG) //.
rewrite (big_morph _ (@natr_add _) (erefl _)).
rewrite (reindex socle_of_irr_class).
  by apply: eq_bigr=> i _; rewrite chi1 natr_exp.
by exists IrrClass=> [] [i].
Qed.

Definition  xchar (chi: cfun_type C gT) (u: 'rV[C]_#|G|) : C^o := 
  \sum_(i < #|G|) u 0 i * chi (enum_val i).

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
by rewrite !cfunE mulr_addr scaler_mulr.
Qed.

Canonical Structure xcharb_linear x := Linear (xcharb_is_linear x).

Lemma xchar_trace : forall u n (chi: mx_representation C G n),
  xchar (char chi) u = \tr (gring_op chi (gring_mx (regular_repr C G) u)).
Proof.
move=> u n chi.
rewrite /xchar /gring_op /= gring_mxK /irr_cfun.
apply: (@etrans _ _
   (\sum_(i0 < #|G|) \tr(u 0 i0 *: chi (enum_val i0)))).
  by apply: eq_bigr=> j _; rewrite cfunE enum_valP mul1r mxtraceZ.
rewrite -raddf_sum; congr (\tr _).
apply/matrixP=> i1 j1; rewrite !mxE summxE; apply eq_bigr=> k1 _.
by rewrite !(mxvecE,mxE).
Qed.

Local Notation e_ := 
  (comp (@Wedderburn_id _ _ _ _) socle_of_irr_class).
Local Notation R_ := 
  (comp (@Wedderburn_subring _ _ _ _) socle_of_irr_class).

Lemma xchar_subring : forall (i j : irr_class) A, 
  i != j -> (A \in R_ j)%MS -> xchar i (gring_row A) = 0.
Proof.
move=> i j A Hi HA.
pose s i := socle_of_irr_class i.
rewrite xchar_trace -(mxtrace0 _ (irr_degree (s i))); congr (\tr _).
have F1: s j != irr_comp sG (irr_repr (s i)).
  rewrite irr_reprK //.
  by apply/eqP=> HH; case/eqP: Hi; apply/val_eqP; rewrite /= -/s HH.
apply: irr_comp'_op0 F1 _ => //; first by apply: socle_irr.
rewrite gring_rowK // -(Wedderburn_sum sG (pGroupG _)).
apply/memmx_sumsP; exists (fun i => (i==s j)%:R *: A).
  rewrite (bigD1 (s j)) //= eqxx scale1r big1 ?addr0 // => k.
  by case: (k == s j); rewrite // scale0r.
by move=> k; case E1: (k == s j); 
  [move/eqP: E1->; rewrite scale1r | rewrite scale0r mem0mx].
Qed.

Lemma xchar_id : forall i j : irr_class,
  xchar i (gring_row (e_ j)) = if i == j then i 1%g else 0.
Proof.
move=> i j; case: eqP=> [->|Hi]; last first.
  by apply: xchar_subring (Wedderburn_id_mem _); apply/eqP.
rewrite cfunE group1 mul1r -gring_opG //.
have R1 := (envelop_mx_id (regular_repr C G) (group1 G)).
rewrite -[regular_repr C G 1%g]gring_rowK // -xchar_trace.
rewrite -[regular_repr _ _ _]mul1mx -(Wedderburn_sum_id sG (pGroupG _)).
have->: regular_repr C G 1%g = 1%:M.
  by apply/matrixP=> i1 j1; rewrite !mxE !eqxx mulg1 gring_valK eq_sym.
pose s i := socle_of_irr_class i.
rewrite mulmx1 !linear_sum /= (bigD1 (s j)) //= big1; first by rewrite addr0.
move=> k; rewrite eq_sym => Hij.
have F1: j != IrrClass k.
  by apply/eqP; move/val_eqP=> HH; case/negP: Hij.
exact: (xchar_subring F1 (Wedderburn_id_mem k)).
Qed.

Definition base_irr := map (irr_cfun) (enum irr_class).
  
Lemma free_base_irr : free (base_irr).
Proof.
apply/freeP=> s; set ss := \sum_(i<_) _ => Hs j.
have Hj: (j <  #|irr_class|)%nat by case: j; rewrite size_map -cardE.
pose j' := enum_val (Ordinal Hj).
suff: xchar ss (gring_row (e_ j')) = s j * j' 1%g.
  rewrite /xchar big1 //.
    move/eqP; rewrite eq_sym mulf_eq0; case/orP; first by move/eqP.
    rewrite chi1; move/GRing.charf0P: Cchar=> -> He.
    by move: (irr_degree_gt0 (socle_of_irr_class j')); rewrite (eqP He).
  by move=> i _; rewrite Hs cfunE mulr0.
rewrite xcharbE linear_sum; rewrite (bigD1 j) //= big1.
  rewrite  addr0 (nth_map irr_class1) //; last by rewrite -cardE.
  rewrite linearZ /= -xcharbE.
  suff->: (nth irr_class1 (enum irr_class) j) = j' by rewrite  xchar_id eqxx.
  by move: (nth_enum_rank irr_class1 j'); rewrite enum_valK.
move=> i Hij.
have Hi: (i <  #|irr_class|)%nat.
  by case: {Hij}i; rewrite size_map -cardE.
pose i' := enum_val (Ordinal Hi).
rewrite  (nth_map irr_class1) //; last by rewrite -cardE.
rewrite linearZ /= -xcharbE.
have->: (nth irr_class1 (enum irr_class) i) = i'.
  by move: (nth_enum_rank irr_class1 i'); rewrite enum_valK.
rewrite  xchar_id; case: eqP; last by rewrite scaler0.
move/eqP=> HH; case/negP: Hij.
by move: HH; rewrite (bij_eq (enum_val_bij irr_class_finType)).
Qed.

Lemma base_irr_basis : is_basis 'CL[C](G) base_irr.
Proof.
rewrite /is_basis free_base_irr andbT /is_span -dimv_leqif_eq.
   rewrite dim_cfun.
   move: free_base_irr; rewrite /free; move/eqP->.
   by rewrite size_map -cardE card_irr_class.
rewrite -span_subsetl; apply/allP=> i; case/mapP=> j _ ->.
apply: char_in_cfun.
Qed.

Lemma sg2bi_ord : forall (i : irr_class), (enum_rank i < size base_irr)%N.
Proof. by move=> i; rewrite size_map -cardE. Qed.

Definition sg2bi i := Ordinal (sg2bi_ord i).

Lemma bi2sg_ord : forall (i : 'I_(size base_irr)), (i < #|irr_class|)%N.
Proof. by case=> i; rewrite size_map -cardE. Qed.

Definition bi2sg i := enum_val (Ordinal (bi2sg_ord i)).

Lemma bi2sgK: cancel bi2sg sg2bi.
Proof. by case=> i Hi; apply/val_eqP; rewrite /= enum_valK. Qed.

Lemma sg2biK: cancel sg2bi bi2sg.
Proof. 
by move=> i; rewrite -{2}(enum_rankK i); congr enum_val; apply/val_eqP.
Qed.

Definition ncoord (i: irr_class) c : C^o :=
 coord base_irr c (sg2bi i).

Lemma ncoord_sum: forall x : cfun_type C gT, x \in 'CL[C](G) -> 
  x = \sum_i  ncoord i x *: irr_cfun i.
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
rewrite  (nth_map irr_class1).
  by rewrite /bi2sg (enum_val_nth irr_class1).
rewrite -cardE; apply: bi2sg_ord.
Qed.

Lemma ncoord_is_linear : forall i, linear (ncoord i).
Proof.
by move=> i k c1 c2; rewrite /ncoord linearD linearZ !ffunE.
Qed.

Canonical Structure ncoord_linear i := Linear (ncoord_is_linear i).

Lemma ncoordE : forall  (f : irr_class -> C)  x, x \in 'CL[C](G) -> 
   x = \sum_i (f i) *: (irr_cfun i) -> forall i, f i = ncoord i x.
Proof.
move=> f x Hin Hx i.
suff: (fun j => ncoord (bi2sg j) x -  f (bi2sg j)) =1 (fun _ => 0).
  by move/(_ (sg2bi i)); rewrite sg2biK; move/eqP; rewrite subr_eq0; move/eqP.
move/freeP: free_base_irr; apply.
have F1:  {on [pred i | xpredT i], bijective sg2bi}.
  by apply: onW_bij; exists bi2sg; [exact: sg2biK | exact: bi2sgK ].
rewrite (reindex _ F1) /=.
rewrite (eq_bigr (fun j => ncoord j x *: irr_cfun j -  f j *: irr_cfun j)).
  by rewrite sumr_sub -Hx -ncoord_sum // subrr.
by move=> j _; rewrite sg2biK scaler_subl // (nth_map irr_class1) -?cardE
                       // nth_enum_rank.
Qed.

Lemma ncoord_chi: forall i j, ncoord j (irr_cfun i) = (i == j)%:R.
Proof.
move=> i j; apply: sym_equal; apply: (@ncoordE (fun j => (i == j)%:R)).
  exact: char_in_cfun.
rewrite (bigD1 i) // big1 /= ?(addr0,eqxx,scale1r) // => i1.
by rewrite eq_sym; case: (_ == _)=> //; rewrite scale0r.
Qed.

Definition to_socle  n (rG : mx_representation C G n) (j: DecSocleType rG) :=  
  irr_comp sG (socle_repr j).

Lemma to_socle_inj: forall n (rG : mx_representation C G n),
  injective (@to_socle n rG).
Proof.
move=> n rG x y Hxy.
apply/eqP; apply/socle_rsimP.
apply: (mx_rsim_trans (rsim_irr_comp sG _ (socle_irr _)))=> //.
apply: mx_rsim_sym; move: Hxy; rewrite /to_socle=>->.
by apply: (rsim_irr_comp sG _ (socle_irr _)).
Qed.

Let to_socle_coef n (rG : mx_representation C G n) (i: sG) :=
oapp (fun i => socle_mult i) 0%N [pick j | i == to_socle (j: DecSocleType rG)].

Lemma ncoord_char : forall n (rG : mx_representation C G n) (i: irr_class),
  ncoord i (char rG) = (to_socle_coef rG (socle_of_irr_class i))%:R.
Proof.
move=> n rG i; apply: sym_equal.
pose sG':= DecSocleType rG.
apply (@ncoordE (fun i => (to_socle_coef rG (socle_of_irr_class i))%:R)).
   by exact: char_in_cfun.
pose ts (i: sG') := (to_socle i).
have->: char rG = 
  \sum_i (irr_cfun (IrrClass (ts i))) *+ socle_mult i.
  apply/cfunP=> g; rewrite !(sum_cfunE,cfunE).
  case: (boolP (_ \in _))=> Hin; last first.
    rewrite mul0r big1 ?ffunE // => j _.
    by rewrite (cfun0 Hin) ?mul0rn // memvMn // char_in_cfun.
  have F1: (Socle sG' :=: 1%:M)%MS.
    rewrite reducible_Socle1 //; exact: mx_Maschke.
  rewrite mul1r -(mxtrace_submod1 (Socle_module sG') F1) // mxtrace_Socle=> //.
  apply: eq_bigr=> i1 _ /=.
  rewrite  cfunMn !cfunE Hin mul1r; congr (_ *+ _).
  by apply: mxtrace_rsim=> //; apply: rsim_irr_comp=> //; 
     apply/submod_mx_irr; apply: socle_simple.
case  E1: (enum sG') => [| x s].
  have F1: forall (i: sG'), false.
    by move=> x; have: x \in enum sG'; [rewrite mem_enum | rewrite E1].
  rewrite !big1 //; last by move=> x; have:= F1 x.
  move=> j; rewrite /to_socle_coef; case: pickP; last by rewrite scale0r.
  by move=> x; have:= F1 x.
rewrite (reindex IrrClass) /=; last first.
  by exists socle_of_irr_class=> // [] [].
have->: 
  \sum_(i0 : sG)
    (to_socle_coef rG i0)%:R *: (IrrClass i0 : cfun_type _ _) = 
   \sum_(i0: sG |  codom ts i0) 
    (to_socle_coef rG i0)%:R *: (IrrClass i0 : cfun_type _ _).
  apply: sym_equal; rewrite big_mkcond; apply: eq_bigr=> k _.
  rewrite /to_socle_coef; case: pickP; last by rewrite scale0r if_same.  
  by move=> i1; move/eqP->; rewrite codom_f.
have F1:  {on [pred i | codom ts i],  bijective ts}.
  pose f i := odflt x [pick j | i == ts j].
  exists f=> [i1 _|i1].
    rewrite /f; case: pickP=> [i2|]; last by move/(_ i1); rewrite eqxx.
    by move/eqP; move/to_socle_inj->.
  case/imageP=> i2 Hi2.
  rewrite /f; case: pickP; first by move=>i3; move/eqP.
  by move/(_ i2); move/eqP.
rewrite (reindex _ F1) /=.
apply: eq_big=>[i1 /=|i1 _]; first by rewrite /= codom_f.
rewrite scaler_nat /to_socle_coef; congr (_ *+ _).
case: pickP; last by move/(_ i1); rewrite eqxx.
by move=> i2; move/eqP; move/to_socle_inj<-.
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

Lemma char_morph : forall m n
  (rG1 : mx_representation C G m) (rG2 :  mx_representation C G n),
  char (add_repr rG1 rG2) = char rG1 + char rG2.
Proof.
move=> m n rG1 rG2.
by apply/cfunP=> g; rewrite !cfunE -mulr_addr mxtrace_block.
Qed.

Lemma mx_repr1: mx_repr G (fun _ : gT => 1%:M : 'M[C]_0).
Proof. by split=> // g h Hg Hx; rewrite mulmx1. Qed.
 
Definition natrepr (m : nat) (rG : mx_representation C G m) := 
  fix iter (n : nat) : mx_representation C G (n * m) :=
    if n is n1.+1 then add_repr rG (iter n1) else MxRepresentation mx_repr1.

Lemma char_natrepr : forall m n (rG : mx_representation C G m), 
  char (natrepr rG n) = char rG *+n.
Proof.
move=> m n rG; elim: n=> [|n IH].
  by apply/cfunP=> g; rewrite !cfunE mxtrace1 mulr0.
by rewrite /= char_morph IH mulrS.
Qed.

(* !!!!!!!!!!! FOR THE MOMENT AN AXIOM !!!!!!!!!!!!!!!!!!! *)
Lemma char_rsimP: forall m n (rG1 : mx_representation C G m)
                          (rG2 : mx_representation C G n),
   reflect (mx_rsim rG1 rG2) (char rG1 == char rG2).
Proof.
move=> m n rG1 rG2; apply: (iffP eqP)=> HH; last first.
  apply/cfunP=> g; rewrite !cfunE.
  case E1: (g \in G); last by rewrite !mul0r.
  by rewrite !mul1r; apply: mxtrace_rsim.
admit.
Qed.
  
Notation "\rho" :=  (char (regular_repr C G)).

Lemma rho_val : forall g : gT, g \in G ->
  \rho g = if g == 1%g then #|G|%:R else 0%:R.
Proof.
move=> g Hg; rewrite cfunE Hg mul1r; rewrite /mxtrace.
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

Lemma rho_sum : \rho = \sum_(i : irr_class) i (1%g) *: irr_cfun i.
Proof.
apply/cfunP=> g; rewrite !cfunE.
case Ig: (_ \in _); last first.
  rewrite mul0r sum_cfunE cfunE big1 // => i _.
  by rewrite cfunE [_ g](cfun0 _ (char_in_cfun _)) (mulr0,Ig).
rewrite mul1r mxtrace_regular // sum_cfunE cfunE.
rewrite {1}(reindex socle_of_irr_class) /=; last by exists IrrClass=> [] [].
by apply eq_bigr=> i _; rewrite chi1 !cfunE Ig mul1r // GRing.mulr_natl.
Qed.

Lemma chi_e_mul : forall (i : irr_class) A, (A \in group_ring C G)%MS ->
 xchar i (gring_row (e_ i *m A)) = xchar i (gring_row A).
Proof.
move=> i A HA.
rewrite -{2}[A]mul1mx -(Wedderburn_sum_id sG) //.
rewrite mulmx_suml !linear_sum (bigD1 (socle_of_irr_class i)) //=.
rewrite big1 ?addr0 // => j; rewrite eq_sym => Hij.
have F1: i != IrrClass j by apply/eqP; move/val_eqP=> HH; case/negP: Hij.
apply: (xchar_subring F1).
case/andP: (Wedderburn_ideal j)=> _ Hj.
apply: submx_trans Hj=> //.
apply: mem_mulsmx=> //.
exact: Wedderburn_id_mem.
Qed.

Lemma xchar_singleton : forall n g (rG : mx_representation C G n),
  let chi := (char rG) in
  g \in G -> xchar chi (gring_row (regular_repr C G g)) = chi g.
Proof.
move=> n g rG chi Hg.
  rewrite /xchar (bigD1 (enum_rank_in (group1 G) g)) // big1 ?addr0.
  by rewrite enum_rankK_in // !mxE gring_indexK // mul1g !eqxx mul1r //= addr0.
move=> i; rewrite !mxE enum_rankK_in // mul1g /gring_index.
by case: (i == _)=> //; rewrite mul0r.
Qed.

(* This corresponds to Issac Th. 2.12 *)
Lemma gring_row_e : forall (i: irr_class), 
  gring_row (e_ i) = 
  \row_j (#|G|%:R^-1 * i 1%g * i ((enum_val j)^-1)%g).
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
  case/andP: (Wedderburn_ideal (socle_of_irr_class i))=> _ Hi.
  apply: submx_trans Hi; apply: mem_mulsmx; first by exact: Wedderburn_id_mem.
  by apply: envelop_mx_id; rewrite groupV enum_valP.
rewrite linearZ /= -xcharbE.
rewrite chi_e_mul; last first.
  by apply: envelop_mx_id; rewrite groupV enum_valP.
rewrite !mxE xchar_singleton // /GRing.scale /= -mulrA => ->.
rewrite !mulrA mulVr ?mul1r // GRing.unitfE.
by move/charf0P: Cchar->; case: #|_| (cardG_gt0 G).
Qed.

Lemma chi_exp_abelian : forall (chi: irr_class) g n, g \in G -> abelian G ->
  (chi g)^+n = chi (g^+n)%g.
Proof.
move=> chi g n Hin AG.
pose i := socle_of_irr_class chi.
pose u := let m := Ordinal (irr_degree_gt0 i) in irr_repr i g m m.
have irr_scal: irr_repr i g = u %:M.
  apply/matrixP=> [] [[|i1] Hi1]; last first.
    by move: (Hi1); rewrite irr_degree_abelian in Hi1.
  case=> [] [|j1] Hj1; last first.
    by move: (Hj1); rewrite irr_degree_abelian in Hj1.
  rewrite /u !mxE; apply: eq_bigr=> i2 _l; rewrite !mxE.
  congr (_ * _); apply: eq_bigr=> i3 _; rewrite !mxE //.
  by congr (_ * _); apply: eq_bigr=> i4 _; rewrite !mxE.
elim: n=> [|n IH].
  by rewrite expr0 expg0 chi1 irr_degree_abelian.
rewrite exprS IH !cfunE {2}expgS repr_mxM // !groupX // Hin.
rewrite irr_scal mul_scalar_mx mxtraceZ mxtrace_scalar.
by rewrite {1}irr_degree_abelian // mulr1n !mul1r.
Qed.

Lemma chi_unit_abelian : forall (chi: irr_class) g, abelian G -> 
  chi g ^+ #[g] = (g \in G)%:R.
Proof.
move=> i g AG; case: (boolP (g \in G))=> Hin; last first.
  rewrite (cfun0 Hin (char_in_cfun _)) //.
  by case: #[g] (order_gt0 g)=> [|n] //; rewrite exprS mul0r.
by rewrite chi_exp_abelian // expg_order chi1 irr_degree_abelian.
Qed.

Lemma chi_norm_abelian : forall (chi : irr_class) g, abelian G -> 
  normC (chi g) = (g \in G)%:R.
Proof.
move=> i g AG; have := chi_unit_abelian i g AG.
case: (boolP (g \in G)) => Hin Hs; last first.
  by rewrite (cfun0 Hin (char_in_cfun _)) // normC0. 
apply/eqP; rewrite -(@posC_unit_exp _ (#[g].-1)) //; last by exact: posC_norm.
by rewrite prednK // -normC_exp Hs normC1.
Qed.

Lemma chi_inv_abelian : forall (chi : irr_class) g, g \in G -> abelian G -> 
  chi (g^-1%g) = (chi g)^*.
Proof.
move=> chi g Hin AG; rewrite invg_expg -chi_exp_abelian //.
have F1 : chi g != 0.
  by rewrite -normC_eq0 chi_norm_abelian // Hin nonzero1r.
apply: (mulfI F1).
rewrite -exprS prednK // chi_unit_abelian // Hin -[_ * _]sqrCK.
move: (chi_norm_abelian chi g); rewrite /normC => -> //.
by rewrite Hin exprS mulr1.
Qed.

End FixGroup.

Section More.

Variable G : {group gT}.

Lemma char_inv : forall n (rG: mx_representation C G n) g,
  char G rG g^-1%g = (char G rG g)^*.
Proof.
move=> n rG g.
case: (boolP (g \in G))=> Hin; last first.
  by rewrite (cfun0 Hin (char_in_cfun _)); rewrite -groupV // in Hin;
     rewrite (cfun0 Hin (char_in_cfun _)) conjC0.
have F1: (<[g]> \subset G) by rewrite cycle_subG.
pose rG' := subg_repr rG F1.
have F2: forall g1, g1 \in <[g]> -> char G rG g1 = char <[g]> rG' g1.
  by move=> g1 Hg1; rewrite !cfunE Hg1; move/subsetP: (F1)->.
rewrite !F2 ?(groupVr,cycle_id) //. 
rewrite (ncoord_sum (char_in_cfun _)).
rewrite sum_cfunE 2!cfunE rmorph_sum; apply: eq_bigr=> i _.
rewrite cfunE chi_inv_abelian //.
have F3: isNatC (ncoord i (char <[g]> rG')).
  rewrite ncoord_char; apply: isNatC_nat.
rewrite -{1}(isNatC_conj F3) {1}/GRing.scale /= -rmorphM ?cfunE //.
  apply: cycle_id.
apply: cycle_abelian.
Qed.

Let card_neq0 : #|G|%:R^-1 != 0 :> C.
Proof.
rewrite invr_eq0; move/GRing.charf0P: Cchar->.
by move: (cardG_gt0 G); case: #|_|.
Qed.

Lemma char_upper : forall n (rG: mx_representation C G n) g,
  normC (char G rG g) <= n%:R.
Proof.
move=> n rG g.
case: (boolP (g \in G))=> Hin; last first.
  by rewrite (cfun0 Hin (char_in_cfun _)) // normC0 leC_nat.
have F1: (<[g]> \subset G) by rewrite cycle_subG.
pose rG' := subg_repr rG F1.
have ->: forall g1, g1 \in <[g]> -> 
  char G rG g1 = char <[g]> rG' g1; last by exact: cycle_id.
  by move=> g1 Hg1; rewrite !cfunE Hg1; move/subsetP: (F1)->.
rewrite -(char1 rG') (ncoord_sum (char_in_cfun _)).
rewrite !sum_cfunE 2!cfunE.
pose nc (i: irr_class <[g]>) := ncoord i (char <[g]> rG').
suff->: \sum_i (nc i *: (i: cfun_type _ _)) 1%g = 
        \sum_i normC ((nc i *: (i: cfun_type _ _)) g%g).
  by apply: normC_sum.
have F2 := cycle_abelian g.
apply: eq_bigr=> i _.
rewrite cfunE chi1 irr_degree_abelian //.
rewrite cfunE normC_mul chi_norm_abelian //.
by rewrite cycle_id normC_pos // /nc ncoord_char leC_nat.
Qed.

Local Notation e_ := ((@Wedderburn_id _ _ _ _) \o (@socle_of_irr_class G)).

(* Painfully following Issac's proof 2.14 *)
Lemma chi_first_orthogonal_relation : forall (i j: irr_class G),
 (#|G|%:R^-1 * \sum_(g \in G) i g * (j g)^*)%R = (i == j)%:R.
Proof.
move=> i j.
rewrite (reindex invg) /=; last by apply: onW_bij; apply: inv_bij; exact invgK.
have F1 : e_ i *m e_ j = (i == j)%:R *: e_ i.
  case: eqP=> [<-|Hij]; [rewrite scale1r | rewrite scale0r].
    by case: (Wedderburn_is_id (pGroupG _) (socle_of_irr_class i))=> _ Hi Hj _; exact: Hj.
  move/eqP: Hij=> HH; apply: (Wedderburn_mulmx0 HH); exact: Wedderburn_id_mem.
have F2: #|G|%:R^-1 * i 1%g * j 1%g != 0.
  by do 2 (apply: mulf_neq0; last by exact: chi1_neq0).
apply: (mulIf F2).
pose r1 (u: 'M[C]_#|G|) := gring_row u 0 (gring_index G 1%g).
apply: (@etrans _ _ (r1 (e_ i *m e_ j))); last first.
  rewrite F1 /=; case: eqP=> [->|_].
    by rewrite scale1r mul1r /r1 gring_row_e !mxE gring_indexK // invg1.
  rewrite scale0r mul0r /r1.
  suff->: @gring_row C _ G 0 = 0 by rewrite mxE.
  by apply/rowP=> k; rewrite !mxE.
pose gr i g := gring_row (e_ (i: irr_class G)) 0 (gring_index G g). 
suff->:
    r1 (e_ i *m e_ j) = \sum_(g \in G) gr i g * gr j (g^-1)%g.
  rewrite -mulr_sumr -mulr_suml.
  apply: eq_big=> [g|i1]; first by rewrite /= groupV.
  rewrite -char_inv groupV=> Hi1.
  rewrite  /gr {1}gring_row_e {1}gring_row_e !mxE !gring_indexK ?groupV //.
  (* mimicking ring *)
  rewrite invgK; rewrite -!mulrA; congr (_ * _).
  apply: sym_equal; rewrite mulrC -!mulrA; congr (_ * _).
  apply: sym_equal; rewrite [j _ * _]mulrC -!mulrA; congr (_ * _).
  by rewrite mulrC -!mulrA; congr (_ * _).
rewrite /r1 gring_row_mul.
have F3: (e_ j \in group_ring C G)%MS.
  apply (submx_trans (Wedderburn_id_mem _)).
  by rewrite /Wedderburn_subring genmxE submxMl.
rewrite -{1}(gring_rowK F3) mxE.
rewrite {1}(reindex (@enum_val _ (fun x=> x \in G))) /=; last first.
  by exists (gring_index G)=> g Hg; [exact: gring_valK | apply: gring_indexK].
apply: eq_big=> [g|i1 _]; first by rewrite enum_valP.
rewrite  /gr !gring_valK; congr (_ * _).
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
have F5: (enum_val i1 * enum_val i2)%g \in G.
  by apply: groupM; exact: enum_valP.
rewrite -[_^-1%g]mulg1.
rewrite (can_in_inj (@gring_indexK _ G) (group1 G) F5 HH).
by rewrite mulgA mulVg mul1g gring_valK.
Qed.

Lemma chi_second_orthogonal_relation : forall (y z: gT),
  y \in G -> z \in G ->
 \sum_(chi : irr_class G) chi y * (chi z)^* =  
    if y \in (z ^: G) then #|'C_G[z]|%:R else 0.
Proof.
move=> y z Hy Hz.
have F0: forall j, (j < #|irr_class G| -> j < #|classes G|)%N 
  by move=> j; rewrite card_irr_class.
pose f i := Ordinal (F0 _ (ltn_ord i)).
have G0: forall j, (j < #|classes G| -> j < #|irr_class G|)%N 
  by move=> j1; rewrite card_irr_class.
pose g i := Ordinal (G0 _ (ltn_ord i)).
have FG: forall i, f (g i) = i by move=> i; apply/val_eqP.
have GF: forall i, g (f i) = i by move=> i; apply/val_eqP.
pose X := \matrix_(i < #|irr_class G|, j < #|irr_class G|) 
  ((enum_val i) (repr (enum_val (f j)))).
pose Y := \matrix_(i < #|irr_class G|, j < #|irr_class G|) 
  (let C := enum_val (f i) in #|C|%:R * (#|G|%:R^-1 * (enum_val j) (repr C))^*).
have F2: X *m Y = 1%:M.
  apply/matrixP=> i j; rewrite !mxE.
  have->: (i == j) = (enum_val i == enum_val j).
    by apply/eqP/eqP; [move-> | exact: enum_val_inj].
  rewrite -chi_first_orthogonal_relation -mulr_sumr cfun_sum; last first.
    by move=> g1 g2 Hg1 Hg2; rewrite -!char_inv  -conjVg 
               !(cfunJ _  _ (char_in_cfun _)) ?groupV.
  rewrite (reindex g) /=; last by apply: onW_bij; exists f=> i1; apply/val_eqP.
  rewrite (reindex (@enum_val _ (fun x => x \in classes G))) /=; last first.
    by apply: (enum_val_bij_in (mem_classes (group1 G))).
  apply: eq_big=> [i1|i1 _]; first by rewrite enum_valP.
  rewrite !mxE /= FG.
  (* mimicking ring *)
  rewrite mulrC -!mulrA; congr (_ * _).
  rewrite rmorphM rmorphV ?conjC_nat //; last first.
    by rewrite unitfE; move/charf0P: Cchar->; case: #|_| (cardG_gt0 G).
  by rewrite -mulrA [enum_val i _ * _]mulrC.
have Hi1: #|z ^: G|%:R != 0 :> C.
  by move/charf0P: Cchar->; rewrite (cardsD1 z) class_refl.
apply: (mulfI (mulf_neq0 Hi1 card_neq0)); rewrite -mulr_sumr.
apply: (@etrans _ _ (y \in z ^: G)%:R); last first.
  case: (boolP (_ \in _))=> [Hin|]; last by rewrite mulr0.
  rewrite -(LaGrange (subcent1_sub z G)) index_cent1.
  rewrite mulrC mulrA natr_mul divff //.
  apply: mulf_neq0=> //.
  by move/charf0P: Cchar->; rewrite (cardsD1 z) (subcent1_id Hz).
move/mulmx1C: F2.
pose toC x := enum_rank_in (classes1 G) (x ^: G).
move/matrixP; move/(_ (g (toC z)) (g (toC y))).
rewrite !mxE.
have<-:  (g (toC z) == g (toC y)) = (y \in z ^: G)=> [|<-].
  apply/eqP/idP=> [|Hin]; last by rewrite /toC (class_transr Hin).
  move/(can_inj FG).
  move/(can_in_inj (enum_rankK_in (classes1 G)) 
         (mem_classes Hz) (mem_classes Hy))->.
  exact: class_refl.
rewrite (reindex (fun i: irr_class G => enum_rank i)); last first.
  by apply: onW_bij; apply: enum_rank_bij.
apply: eq_bigr=> i _.
rewrite !mxE /= !FG  /toC !enum_rankK !enum_rankK_in ?mem_classes //.
case: (repr_class G y)=> y1 Hy1->.
case: (repr_class G z)=> z1 Hz1->.
rewrite !(cfunJ _ _ (char_in_cfun _)) //.
rewrite -!mulrA; congr (_ * _).
rewrite rmorphM rmorphV ?conjC_nat //; last first.
  by rewrite unitfE; move/charf0P: Cchar->; case: #|_| (cardG_gt0 G).
by rewrite -mulrA [i _ * _]mulrC.
Qed.

Lemma chi_conjugate : forall (y z: gT),
  y \in G -> z \in G ->
  reflect (forall chi : irr_class G, chi y = chi z)
          (y \in (z ^: G)).
Proof.
move=> y z Hy Hz; apply: (iffP idP)=> [HH chi|HH].
  case/imsetP: HH=> x Hx ->.
  by rewrite (cfunJ Hz) // char_in_cfun.
move: (chi_second_orthogonal_relation Hy Hz); case: (_ \in _)=> // HH1.
have F1:  forall chi : irr_class G, xpredT chi -> 0 <= chi y * (chi z)^*.
  by move=> chi _; rewrite HH /leC subr0 repC_pconj.
case/eqP: (nonzero1r C).
move: (posC_sum_eq0 F1 HH1); move/(_ (irr_class1 G)).
rewrite !irr_class1E Hy Hz conjC1 mul1r; apply=> //.
by rewrite  /index_enum -enumT mem_enum.
Qed.

Implicit Types f g : cfun_type C gT.

Definition inner_prod f g :=  #|G|%:R^-1 * \sum_(i \in G) f i * (g i)^*.

Local Notation "'[ f , g ]" := (inner_prod f g).

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
by rewrite posC_sum // => i _; rewrite /leC subr0.
Qed.

Lemma inner_prod0: forall f, f \in 'CL[C](G) -> ('[f, f] == 0) = (f == 0).
Proof.
move=> f Hf; apply/eqP/eqP=> Hp; last first.
  by rewrite Hp /inner_prod big1 ?mulr0 // => i _; rewrite !cfunE mul0r.
apply/cfunP=> g; rewrite cfunE.
case: (boolP (g \in G))=> Hin; last by rewrite (cfun0 Hin).
suff: f g * (f g)^* == 0.
  by rewrite mulf_eq0; case/orP; [move/eqP|rewrite conjC_eq0;move/eqP].
move: Hp; move/eqP; rewrite /inner_prod mulf_eq0; case/orP=> [|Hp].
  by rewrite (negPf card_neq0).
apply/eqP; apply: (posC_sum_eq0 _ (eqP Hp))=> //.
 by move=>*; rewrite -sqrC_pos; exact: posC_norm.
by rewrite /index_enum -enumT mem_enum.
Qed.

Definition inner_prodb f := inner_prod^~ f.

Lemma inner_prodbE: forall f g, inner_prodb f g = inner_prod g f.
Proof. by []. Qed.

Lemma inner_prodb_is_linear : forall f, linear (inner_prodb f : _ -> C^o).
Proof.
move=> f k g1 g2.
rewrite /inner_prodb /inner_prod.
rewrite {1}scaler_mulr -{1}scaler_addr; congr (_ * _).
rewrite {1}scaler_sumr /= -{1}big_split /=; apply: eq_bigr=> i _.
by rewrite scaler_mull -mulr_addl !cfunE.
Qed.

Canonical Structure inner_prodb_linear f := Linear (inner_prodb_is_linear f).

Lemma inner_prod_is_additive : forall f, additive (inner_prod f).
Proof.
move=> f g1 g2.
rewrite /inner_prod /inner_prod.
rewrite -mulr_subr; congr (_ * _).
rewrite -sumr_sub; apply: eq_bigr=> i _.
by rewrite !cfunE rmorph_sub // mulr_subr.
Qed.

Canonical Structure inner_prod_additive f := 
  Additive (inner_prod_is_additive f).

Lemma inner_prodZ : forall k f g, '[f, k *: g] = k^* * '[f,g].
Proof.
move=> k f g; rewrite /inner_prod.
rewrite mulrCA; congr (_ * _).
rewrite -mulr_sumr; apply: eq_bigr=> i _.
by rewrite !cfunE rmorphM mulrCA.
Qed.

Lemma chi_orthonormal : forall i j: irr_class G, '[i,j] = (i == j)%:R.
Proof.
by move=> i j; rewrite -chi_first_orthogonal_relation; congr (_ * _).
Qed.

Definition is_char (f : cfun_type C gT) :=
  all (fun i : irr_class G => isNatC (ncoord i f)) (enum (irr_class G)) &&
  (f \in 'CL[C](G)).

Definition getNatC (c: C) : nat :=
 match getRatC c with (b,n,d) => (n %/ d.+1)%N end.

Lemma getNatCP: forall c, isNatC c = (c == (getNatC c)%:R).
Proof.
move=> c;apply/idP/eqP=>[|->]; last by apply: isNatC_nat.
by rewrite /isNatC /getNatC; case: getRatC=> [[b n]] d; move/eqP.
Qed.

Lemma is_charP : forall f,
  reflect (exists n, exists rG : mx_representation C G n, char G rG = f)
          (is_char f).
Proof.
move=> f; apply: (iffP andP); last first.
  case=> n [rG <-]; split; last exact: char_in_cfun.
  by apply/allP=> chi _; rewrite ncoord_char isNatC_nat.
case; move/allP=> Ha Hf.
pose n' (j : irr_class G) := getNatC (ncoord j f).
have->: f = \sum_(j : irr_class G) (n' j)%:R *: (j : cfun_type _ _).
  rewrite {1}(ncoord_sum Hf); apply: eq_bigr=> i _.
  congr (_ *: _); apply/eqP; rewrite -getNatCP; apply: Ha.
  by exact: mem_enum.
elim: {n'}(\sum_j (n' j))%N {-2}n' (leqnn (\sum_j (n' j)))=> [| N IH] n' HS.
  exists 0%N; exists (MxRepresentation (mx_repr1 G)).
  apply/cfunP=> i; rewrite sum_cfunE !cfunE mxtrace1 mulr0 big1 // => j Hj.
  by move: HS; rewrite (bigD1 j) //=; case: (n' j)=> //; rewrite scale0r cfunE.
case: (boolP (all (fun i => n' i == 0%N) (enum (irr_class G)))).
  move/allP=> HH.
  exists 0%N; exists (MxRepresentation (mx_repr1 G)).
  apply/cfunP=> i; rewrite sum_cfunE !cfunE mxtrace1 mulr0 big1 // => j Hj.
  by rewrite (eqP (HH _ (mem_enum _ j))) scale0r cfunE.
case/allPn=> k kIn Hk.
pose n'' j := if (j == k) then (n' j).-1 else n' j.
have F1: (\sum_j (n' j) = 1 + \sum_j n'' j)%N.
  rewrite (bigD1 k) //[(\sum_j n'' j)%N](bigD1 k) //.
  rewrite addnA /n'' eqxx add1n prednK; last by case: (n' k) Hk.
  by congr (_ + _)%N; apply: eq_bigr=> i; case: (i == k).
have F2: \sum_j (n' j)%:R *: (j : cfun_type _ _)  = 
             (k : cfun_type _ _) + \sum_j (n'' j)%:R *: (j : cfun_type _ _).
  rewrite (bigD1 k) //[(\sum_j (n'' j)%:R *: _)](bigD1 k) // addrA; congr (_ + _).
    rewrite /n'' eqxx -{2}[(k: cfun_type _ _)]scale1r -scaler_addl -(natr_add _ 1%N).
    by rewrite add1n prednK //; case: (n' k) Hk.
  by apply: eq_bigr=> i; rewrite /n''; case: (i == k).
case: (IH n''); first by  rewrite -ltnS -add1n -F1.
intros n [rG HrG].
pose i := socle_of_irr_class k.
exists ((irr_degree i) + n)%N; exists (add_repr (irr_repr i) rG).
by rewrite char_morph HrG F2.
Qed.

Lemma is_char_irr : forall i : irr_class G, is_char i.
Proof. 
move=> i; apply/is_charP; pose i' := socle_of_irr_class i.
by exists (irr_degree i'); exists (irr_repr i').
Qed.

Lemma is_char0 : is_char 0.
Proof.
apply/is_charP.
exists 0%N; exists (MxRepresentation (mx_repr1 G)).
by apply/cfunP=> i; rewrite !cfunE mxtrace1 mulr0.
Qed.

Lemma is_char_add : forall f1 f2, 
  is_char f1 -> is_char f2 -> is_char (f1 + f2).
Proof.
move=> f1 f2; case/is_charP=> m [rG1 HrG1]; case/is_charP=> n [rG2 HrG2].
apply/is_charP; exists (m + n)%N; exists (add_repr rG1 rG2).
by rewrite char_morph HrG1 HrG2.
Qed.

Lemma is_char_scal : forall f k, isNatC k -> is_char f -> is_char (k *: f).
Proof.
move=> f k; case/isNatCP=> n -> Hf; elim: n=> [|n Hn].
  by rewrite scale0r is_char0.
by rewrite -add1n natr_add scaler_addl scale1r is_char_add.
Qed.

Lemma inner_prod_char :
  forall ch1 ch2, is_char ch1 -> is_char ch2 ->
   '[ch1,ch2] = \sum_(i:irr_class G) (ncoord i ch1) * (ncoord i ch2).
Proof.
move=> ch1 ch2; case/is_charP=> m [rG1 <-]; case/is_charP=> n [rG2 <-].
rewrite (ncoord_sum (char_in_cfun _))
        [char _ rG2](ncoord_sum (char_in_cfun _)).
rewrite -inner_prodbE linear_sum /=.
apply: eq_bigr=> i _; rewrite inner_prodbE.
rewrite raddf_sum /= {1}(bigD1 i) // big1 //= => [|j Hj];
    rewrite inner_prodZ -{1}inner_prodbE {1}[inner_prodb _ _]linearZ /= 
            inner_prodbE chi_orthonormal; last first.
  by rewrite eq_sym (negPf Hj) scaler0 mulr0.
rewrite eqxx.
rewrite linear_sum {1}(bigD1 i) // big1 /=; last first.
  by move=> j Hj; rewrite linearZ /= ncoord_chi (negPf Hj) scaler0.
rewrite linear_sum {1}(bigD1 i) // big1 /=; last first.
  by move=> j Hj; rewrite linearZ /= ncoord_chi (negPf Hj) scaler0.
apply: sym_equal; rewrite {1}addr0 {1}addr0 {1}linearZ {1}linearZ /=.
rewrite ncoord_chi eqxx -scaler_mulr -scaler_mull mulr1 addr0 isNatC_conj //.
rewrite ncoord_char; exact: isNatC_nat.
Qed.

Lemma inner_prod_char_nat :
  forall ch1 ch2, is_char ch1 -> is_char ch2 -> isNatC '[ch1,ch2].
Proof.
move=> ch1 ch2 Hch1 Hch2; rewrite inner_prod_char //.
apply: isNatC_sum=> i _.
by apply: isNatC_mul; [case/is_charP: Hch1|case/is_charP: Hch2];
  move=> n [rG <-]; rewrite ncoord_char; exact: isNatC_nat.
Qed.
 
Lemma inner_prod_charC :
  forall ch1 ch2, is_char ch1 -> is_char ch2 -> '[ch1,ch2] = '[ch2,ch1].
Proof.
move=> ch1 ch2 Hc1 Hc2.
by rewrite !inner_prod_char //; apply: eq_bigr=> i _; rewrite mulrC.
Qed.

Lemma char_irreducibleP : forall ch, is_char ch ->
  reflect (exists chi : irr_class G, ch = chi) ('[ch, ch] == 1).
Proof.
move=> ch Hch; apply: (iffP idP); last first.
  by case=> i->; rewrite chi_orthonormal eqxx.
rewrite inner_prod_char //.
case/is_charP: Hch => n [rG <-].
move/eqP=> HH; case: (isNatC_sum_eq1 _ _ HH).
- by move=> i _; apply: isNatC_mul; 
     rewrite ncoord_char isNatC_nat.
- by rewrite /index_enum -enumT; exact: enum_uniq.
move=> i [Hin _ HF HG]; exists i.
rewrite (ncoord_sum (char_in_cfun _)); apply: sym_equal.
rewrite [irr_cfun i](ncoord_sum (char_in_cfun _)).
apply: eq_bigr=> k _; congr (_ *: _).
rewrite ncoord_chi; case: eqP=> [<-|]; last first.
  move/eqP; rewrite eq_sym=> Hik.
  have F1: k \in index_enum (irr_class_finType G).
    rewrite /index_enum -enumT.
    apply/(nthP (irr_class1 G)); exists (enum_rank k)=> //.
      case: enum_rank=> /= m; first by rewrite cardT /=.
    by apply/val_eqP; rewrite nth_enum_rank.
  move: (HG _ Hik F1 is_true_true).
  by move/eqP; rewrite mulf_eq0; case/orP; move/eqP->.
move: HF; rewrite ncoord_char -natr_mul; case: (oapp _ _ _)=>//. 
case=> // m.
rewrite mulnS addSn -{2}[1]add0r -addn1 natr_add => HH1.
by move: (addIr HH1); move/eqP; move/charf0P: Cchar->.
Qed.

End More.

End Main.

End Character.