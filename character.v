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


(* Our group *)
Variable (gT : finGroupType).
Implicit Type G H: {group gT}.

Hypothesis groupC: group_closure_field C gT.

Section ClassFunction.

Variable G: {group gT}.

Definition class_fun_pred (f: {ffun  gT -> C}) :=
 (forallb x, (x \notin G) ==> (f x == 0)) && 
 (forallb x, forallb y, ((x \in G) && (y \in G)) ==> (f (x ^ y) == f x)).

Structure class_fun : Type := ClassFun {
  fofc :> {ffun  gT -> C};
     _ : class_fun_pred fofc
}.

Canonical Structure class_fun_subType :=
  Eval hnf in [subType for fofc by class_fun_rect].
Canonical Structure class_fun_eqMixin := [eqMixin of class_fun by <:].
Canonical Structure class_eqType := 
  Eval hnf in EqType class_fun class_fun_eqMixin.
Definition class_fun_choiceMixin := [choiceMixin of class_fun by <:].
Canonical Structure class_fun_choiceType :=
  Eval hnf in ChoiceType class_fun class_fun_choiceMixin.

Lemma class_fun_notin: forall (f: class_fun) x, x \notin G -> f x = 0.
Proof.
case=> f /=; case/andP; move/forallP=> Hf _ x Hx; apply/eqP.
by move: Hx; apply/implyP.
Qed.

Lemma class_funJ: forall (f: class_fun) x y, 
  x \in G -> y \in G -> f (x ^ y) = f x.
Proof.
case=> f /=; case/andP=> _ Hf x y Hx Hy.
apply/eqP; move/forallP: Hf; move/(_ x); move/forallP; move/(_ y).
by rewrite Hx Hy.
Qed.

Lemma class_fun_pred0: class_fun_pred [ffun g => 0].
Proof.
by apply/andP; split; apply/forallP=> x; last apply/forallP=> y;
   rewrite !ffunE eqxx implybT.
Qed.

Definition class_fun0 := ClassFun class_fun_pred0.

Lemma class_fun_pred1: class_fun_pred [ffun g => (g \in G)%:R].
Proof.
apply/andP; split; apply/forallP=> x; last apply/forallP=> y; rewrite !ffunE.
  by case: (_ \in _)=> //; rewrite eqxx implybT.
by apply/implyP; case/andP=> Hx Hy; rewrite groupJr.
Qed.

Definition class_fun1 := ClassFun class_fun_pred1.

Lemma class_fun_add_pred : forall f g: class_fun, 
  class_fun_pred [ffun x => f x + g x].
Proof.
move=> f g; apply/andP; split; apply/forallP=> x; last apply/forallP=> y; 
    rewrite !ffunE.
  by apply/implyP=> Hx; rewrite !class_fun_notin // add0r.
by apply/implyP; case/andP=> Hx Hy; rewrite !class_funJ.
Qed.

Definition class_fun_add f g := ClassFun (class_fun_add_pred f g).

Lemma class_fun_opp_pred : forall (f : class_fun), 
  class_fun_pred [ffun x => - (f x)].
Proof.
move=> f; apply/andP; split; apply/forallP=> x; last apply/forallP=> y; 
    rewrite !ffunE.
  by apply/implyP=> Hx; rewrite !class_fun_notin // oppr0.
by apply/implyP; case/andP=> Hx Hy; rewrite !class_funJ.
Qed.

Definition class_fun_opp f := ClassFun (class_fun_opp_pred f).

Lemma class_fun_scal_pred : forall (k: C) (f : class_fun), 
  class_fun_pred [ffun x => k * f x].
Proof.
move=> k f; apply/andP; split; apply/forallP=> x; last apply/forallP=> y; 
    rewrite !ffunE.
  by apply/implyP=> Hx; rewrite !class_fun_notin // mulr0.
by apply/implyP; case/andP=> Hx Hy; rewrite !class_funJ.
Qed.

Definition class_fun_scal k f := ClassFun (class_fun_scal_pred k f).

Lemma class_fun_addA : associative class_fun_add.
Proof. 
by move=> *; apply: val_inj; apply/ffunP=> ?; rewrite !ffunE addrA.
Qed.

Lemma class_fun_addC : commutative class_fun_add.
Proof. 
by move=> *; apply: val_inj; apply/ffunP=> ?; rewrite !ffunE addrC.
Qed.

Lemma class_fun_add0 : left_id class_fun0 class_fun_add.
Proof.
by move=> *; apply: val_inj; apply/ffunP=> ?; rewrite !ffunE add0r.
Qed.

Lemma class_fun_addN : left_inverse class_fun0 class_fun_opp class_fun_add.
Proof.
by move=> *; apply: val_inj; apply/ffunP=> ?; rewrite !ffunE addNr.
Qed.

(* abelian group structure *)
Definition class_funZmodMixin := 
  ZmodMixin class_fun_addA class_fun_addC class_fun_add0 class_fun_addN.
Canonical Structure class_funZmodType :=
 Eval hnf in ZmodType class_fun class_funZmodMixin.

Lemma class_fun_scalA : forall a b f, 
  class_fun_scal a (class_fun_scal b f) = class_fun_scal (a * b) f.
Proof.
by move=> *; apply: val_inj; apply/ffunP=> g; rewrite !ffunE mulrA.
Qed.

Lemma class_fun_scal1 : forall f, class_fun_scal 1 f = f.
Proof. by move=> f; apply: val_inj; apply/ffunP=> g; rewrite ffunE mul1r. Qed.

Lemma class_fun_scal_addr :  forall a f g, 
  class_fun_scal a (f + g) = (class_fun_scal a f) + (class_fun_scal a g).
Proof.
by move=> *; apply: val_inj; apply/ffunP=> g; rewrite !ffunE mulr_addr.
Qed.

Lemma class_fun_scal_addl : forall f a b, 
  class_fun_scal (a + b) f = (class_fun_scal a f) + (class_fun_scal b f).
Proof.
by move=> *; apply: val_inj; apply/ffunP=> g; rewrite !ffunE mulr_addl.
Qed.

Definition class_funLmodMixin :=
  LmodMixin class_fun_scalA class_fun_scal1 
     class_fun_scal_addr class_fun_scal_addl.
Canonical Structure class_funLmodType :=
  Eval hnf in LmodType C class_fun class_funLmodMixin.

Definition class_fun2rv (f: class_fun) := 
 \row_(i < #|classes G|) f (repr (enum_val i)).

Lemma class_fun2rv_morph_p : linear class_fun2rv.
Proof.
by move=> k /= x y; apply/matrixP=> [] [[|i] Hi] j; rewrite !mxE !ffunE.
Qed.

Canonical Structure class_fun2rv_morph := Linear class_fun2rv_morph_p.

Lemma class_fun2rv_bij : bijective class_fun2rv.
Proof.
pose f (r: 'rV[C]_#|classes G|) :=
  [ffun x: gT =>
    if (x \in G) then r 0 (enum_rank_in (classes1 G) (x ^: G))
    else 0 
  ].
have Hf: forall r, class_fun_pred (f r).
  move=> r; apply/andP; split.
    by apply/forallP=> x; rewrite ffunE; case: (_ \in _); rewrite // eqxx.
  apply/forallP=> x; apply/forallP=> y; apply/implyP; case/andP=> Hx Hy.
  by rewrite !ffunE; rewrite groupJr // Hx classGidl.
exists (fun r => ClassFun (Hf r)).
  move=> g; apply/val_eqP=> /=; apply/eqP; apply/ffunP=> x.
  rewrite /f ffunE; case Hi: (_ \in _); last by rewrite class_fun_notin // Hi.
  rewrite /class_fun2rv /= mxE enum_rankK_in //; last by apply: mem_classes.
  by case: (repr_class G x) => y Hy ->; rewrite class_funJ.
move=> r; apply/rowP=> i.
have reG: repr (enum_val i) \in G.
  case/imsetP: (enum_valP i)=> x Hx ->.
  apply: (subsetP (class_subG Hx (subxx _))).
  by apply: mem_repr (class_refl _ _).
rewrite !mxE !ffunE reG -{2}(enum_valK_in (classes1 G) i).
suff H1: repr (enum_val i) ^: G = enum_val i by rewrite H1.
case/imsetP: (enum_valP i)=> x Hx ->.
case: (repr_class G x)=> y Hy ->.
by apply: classGidl.
Qed.

Definition class_funVectMixin := 
  VectMixin class_fun2rv_morph_p class_fun2rv_bij.
Canonical Structure class_funVectType := 
  VectType C class_funVectMixin.

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

Lemma class_fun_pred_character_of: forall n (repr:  mx_representation C G n), 
  class_fun_pred (character_of repr).
Proof.
move=> n repr; apply/andP; split; apply/forallP=> x; rewrite ffunE.
  by case: (x \in G)=> //; rewrite mul0r eqxx.
apply/forallP=> y; apply/implyP; rewrite ffunE; case/andP=> Hx Hy.
by rewrite groupJ // Hx !mul1r !(repr_mxM,repr_mxV,groupM,groupV) // 
           mxtrace_mulC mulmxK // repr_mx_unit.
Qed.  

Variable sG : irrType C G.

Definition irr_class_fun (i : sG) := 
  ClassFun (class_fun_pred_character_of (irr_repr i)).

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

End ClassFunction.

End Character.
