(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient finalg action zmodp.
Require Import commutator cyclic center pgroup matrix mxalgebra mxpoly.
Require Import mxrepresentation vector algC.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(**************************************************************************)
(*                                                                        *)
(* This file contains the fundamental of character theory                 *)
(*                                                                        *)
(*  cfun_type C gT : the type of functions from gT to C                   *)
(*                                                                        *)
(*  class_fun G : the vector space of class functions of G                *)
(*                                                                        *)
(*  irr_class G : irreducible character of G                              *)
(*                                                                        *)
(*  char G rG : turn the representation rG into a character               *)
(*                                                                        *)
(*  is_char G f : predicates that tells if the function f is a character  *)
(*                                                                        *)
(*  inner_prod G f g : the inner product of f g such that irr_class is    *)
(*                     an orthonormal basis of class_fun G                *)
(*                                                                        *)
(*  cker G f : the kernel of G i.e g \in G such that f g = f 1            *)
(*                                                                        *)
(* (qfun_of_cfun N f) : if f is a character G, it returns the isomorphic  *)
(*                      character in G/N                                  *)
(* (cfun_of_qfun N f) : if f is a character G/N, returns the isomorphic   *)
(*                      character in G                                    *)
(*                                                                        *)
(**************************************************************************)

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

Lemma unitmxZ : forall (R : comUnitRingType) n (A : 'M[R]_n) a,
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

Lemma invmx1 : forall (R : fieldType) (n : nat), invmx 1%:M = 1%:M :> 'M[R]_n.
Proof.
by move=> R n; rewrite /invmx det1 invr1 scale1r adj1 if_same.
Qed.

Lemma invmx_scalar :
 forall (R : fieldType) (n : nat) (a: R), invmx (a%:M) = a^-1%:M :> 'M[R]_n.
Proof.
by move=> R n a; rewrite -scalemx1 invmxZ ?unitmx1 // invmx1 scalemx1.
Qed.

Lemma scalar_exp :
 forall (R : ringType) (m n : nat) (a: R), 
 (a^+m)%:M = a%:M^+ m :> 'M_n.+1.
Proof.
move=> R m n a; elim: m=> [|m IH]; first by rewrite !expr0.
by rewrite !exprS scalar_mxM IH.
Qed.

Lemma row_is_linear : 
  forall (R: ringType) m n (i: 'I_m), linear (@row R m n i).
Proof.
by move=> R m n i k A B; apply/matrixP=> x y; rewrite !mxE.
Qed.

Canonical Structure row_linear R m n i := Linear (@row_is_linear R m n i).

Lemma gring_row_is_linear : 
  forall (R: comUnitRingType) gT G, linear (@gring_row R gT G).
Proof. move=> *; exact: row_is_linear. Qed.

Canonical Structure gring_row_linear R gT G := 
  Linear (@gring_row_is_linear R gT G).


Lemma block_mx1 : forall (R: ringType) m n,
       block_mx (1%:M : 'M[R]_m) 0 0 (1%:M : 'M[R]_n) = 1%:M.
Proof.
move=> R m n.
apply/matrixP=> [] [i Hi] [j Hj]; rewrite !mxE.
case: splitP=> [] [i1 Hi1]; rewrite !mxE /eq_op /= => ->;
    case: splitP=> [] [j1 Hj1]; rewrite !mxE /= => -> //.
- by case: eqP=> HH=> //; move: Hi1; rewrite HH ltnNge leq_addr.
- by case: eqP=> HH=> //; move: Hj1; rewrite -HH ltnNge leq_addr.
by rewrite eqn_addl.
Qed.

(* This should be put in mxrepresentation *)


Section MxR.

Variable (gT : finGroupType).

Variables (G  N: {group gT}) (n : nat).
Variable R : fieldType.
Variable rG : mx_representation R (G/N)%g n.
Hypothesis NN: N <| G.

Definition coset_mx of N <| G := rG \o (coset N).

Lemma coset_mx_repr : mx_repr G  (coset_mx NN).
Proof.
split=> [|x y Hx Hy].
  rewrite /coset_mx /= -(repr_mx1 rG); congr (rG _).
  by apply/val_eqP; rewrite /= (coset1 N) genGid.
by rewrite /coset_mx /= !coset_morphM ?(repr_mxM,mem_quotient)//;
   apply: (subsetP (normal_norm NN)).
Qed.

Canonical Structure coset_repr := MxRepresentation coset_mx_repr.

Local Notation rGH := coset_repr.

Lemma coset_repr_coset : forall x, x \in G -> rG (coset N x) = rGH x.
Proof.  by []. Qed.

Lemma coset_repr_rker : N \subset (rker rGH).
Proof.
apply/subsetP=> g InG.
rewrite inE (subsetP (normal_sub NN)) // mul1mx /=.
by rewrite /coset_mx /= coset_id // repr_mx1.
Qed.

Lemma quo_coset_repr : 
  mx_rsim (quo_repr (coset_repr_rker) (normal_norm NN)) rG.
Proof.
exists 1%:M=> //.
  by apply/row_freeP; exists 1%:M; rewrite mul1mx.
move=> M InM.
rewrite mul1mx mulmx1 /= /coset_mx /=.
admit.
Qed.

End MxR.

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

Definition base_cfun (G : {set gT}) : seq cfun_type :=
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

Definition class_fun G := span (base_cfun G).

Lemma cfun_memP : forall (f : cfun_type),
  reflect 
    ((forall x, x \notin G -> f x = 0) /\
     (forall x y, x \in G -> y \in G -> f (x ^ y) = f x))
    (f \in class_fun G).
Proof.
move=> f; apply: (iffP idP)=> [|[Hg Hc]].
  move/coord_span->; split=> [x Inx|].
    rewrite sum_cfunE cfunE; apply: big1=> i _.
    have: (base_cfun G)`_i \in (base_cfun G) by apply: mem_nth.
    case/mapP=> j Hj ->; rewrite !cfunE.
    have [y Gy ->] := imsetP (enum_valP j).
    move/subsetP: (class_subG Gy (subxx _)); move/(_ x); move/contra.
    by move/(_ Inx); case: (_ \in _)=> //; rewrite mulr0.
  move=> x y Hx Hy.
  apply/eqP; rewrite -subr_eq0; apply/eqP.
  rewrite !sum_cfunE !cfunE -sumr_sub; apply: big1=> i _.
  set u := coord _ _ _; rewrite !cfunE.
  have: (base_cfun G)`_i \in base_cfun G by apply: mem_nth.
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
  x \notin G -> f \in class_fun G -> f x = 0.
Proof. by move=> f x Hx; case/cfun_memP=> HH _; exact: HH. Qed.

Lemma cfunJ : forall (f : cfun_type) x y, 
   x \in G -> y \in G -> f \in class_fun G -> f (x ^ y) = f x.
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

Lemma cfun_free : free (base_cfun G).
Proof.
apply/freeP=> s S0 i.
have Hi: (i < #|classes G|)%N 
  by case: i=> /= m; rewrite size_map -cardE card_ord.
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
have Hj: (j < #|classes G|)%N.
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

Lemma dim_cfun : \dim (class_fun G) = #|classes G|.
Proof.
by move: cfun_free; rewrite /free size_map -cardE card_ord; move/eqP.
Qed.

End ClassFun.

Local Notation "''CL[' R ] ( G ) " := (class_fun R G).
 
Section Character.
	
Section Main.

Variable (gT : finGroupType).

Hypothesis groupC : group_closure_field C gT.

Implicit Type G : {group gT}.

Let pGroupG : forall G, [char C]^'.-group G.
Proof.
by move=> G; apply: sub_pgroup (pgroup_pi G)=> i _; rewrite inE /= Cchar.
Qed.

Definition char n (G : {set gT}) (f: gT -> 'M[C]_n) := 
 cfun_of_fun (fun g : gT => ((g \in G)%:R * \tr (f g))).

Lemma char1 : 
  forall n G (rG : mx_representation C G n), char G rG 1%g = n%:R.
Proof.
by move=> n G rG; rewrite !cfunE group1 repr_mx1 mxtrace1 mul1r.
Qed.

Lemma char_sim : 
  forall n1 n2 G (rG1: mx_representation C G n1) (rG2: mx_representation C G n2),
  mx_rsim rG1 rG2 -> char G rG1 = char G rG2.
Proof.
move=> n1 n2 G rG1 rG2; case/mx_rsim_def=> M1 [M2] HM1M2 Hx.
apply/cfunP=> x; rewrite !cfunE; case H: (_ \in _); last by rewrite !mul0r.
by rewrite Hx // mxtrace_mulC mulmxA HM1M2 mul1mx.
Qed.

Lemma char_in_cfun : forall n G (rG :  mx_representation C G n), 
  char G rG \in 'CL[C](G).
Proof.
move=> n G rG; apply/cfun_memP.
split=> [x|x y Hx Hy]; rewrite !cfunE.
  by case: (x \in G)=> //; rewrite mul0r.
by rewrite groupJ // Hx !mul1r !(repr_mxM,repr_mxV,groupM,groupV) //
           mxtrace_mulC mulmxK // repr_mx_unit.
Qed.  

Let sG G := DecSocleType (regular_repr C G).

Inductive irr_class G : predArgType :=
  IrrClass of (sG G).
Definition socle_of_irr_class G (A : irr_class G) := let: IrrClass i := A in i.

Canonical Structure irr_class_subType G :=
  Eval hnf in [newType for (@socle_of_irr_class G) by (@irr_class_rect G)].
Definition irr_class_eqMixin G := Eval hnf in [eqMixin of (irr_class G) by <:].
Canonical Structure irr_class_eqType G := 
  Eval hnf in EqType (irr_class G) (irr_class_eqMixin G).
Definition irr_class_choiceMixin G := [choiceMixin of (irr_class G) by <:].
Canonical Structure irr_class_choiceType G :=
  Eval hnf in ChoiceType (irr_class G) (irr_class_choiceMixin G).
Definition irr_class_countMixin G := [countMixin of (irr_class G) by <:].
Canonical Structure irr_class_countType G :=
  Eval hnf in CountType (irr_class G) (irr_class_countMixin G).
Canonical Structure irr_class_subCountType G :=
  Eval hnf in [subCountType of (irr_class G)].
Definition irr_class_finMixin G := [finMixin of (irr_class G) by <:].
Canonical Structure irr_class_finType G :=
  Eval hnf in FinType (irr_class G) (irr_class_finMixin G).
Canonical Structure irr_class_subFinType G :=
  Eval hnf in [subFinType of (irr_class G)].

Coercion irr_cfun G chi := 
  char G (irr_repr (@socle_of_irr_class G chi)).

Definition irr_class1 G := IrrClass (principal_comp (sG G)).

Lemma irr_class1E : forall G g, irr_class1 G g = (g \in G)%:R.
Proof.
move=> G g; case: (boolP (_ \in _))=> Hg; last first.
 by rewrite (cfun0 Hg) //; exact: char_in_cfun.
by rewrite cfunE Hg mul1r irr1_repr // mxtrace1 degree_irr1.
Qed.

Lemma card_irr_class : forall G, #|irr_class G| = #|classes G|.
Proof.
move=> G; rewrite -(card_irr (sG G)) // card_sub.
by apply: eq_card=> i; rewrite !inE.
Qed.

Lemma chi1 : forall G (chi : irr_class G), 
  chi 1%g = (irr_degree (socle_of_irr_class chi))%:R.
Proof.
by move=> G i; rewrite cfunE group1 mul1r repr_mx1 mxtrace1.
Qed.

Lemma chi1_neq0 : forall G (chi : irr_class G), chi 1%g != 0.
Proof.
move=> G i; rewrite chi1; move/GRing.charf0P: Cchar=> ->.
by case: irr_degree (irr_degree_gt0 (socle_of_irr_class i)).
Qed.

Lemma sum_chi2 : forall G, \sum_(chi : irr_class G) (chi 1%g) ^+ 2 = #|G|%:R.
Proof.
move=> G; rewrite -(sum_irr_degree (sG G)) //.
rewrite (big_morph _ (@natr_add _) (erefl _)).
rewrite (reindex (@socle_of_irr_class G)).
  by apply: eq_bigr=> i _; rewrite chi1 natr_exp.
by exists (@IrrClass G)=> [] [i].
Qed.

Definition xchar G (chi: cfun_type C gT) (u: 'rV[C]_#|G|) : C^o := 
  \sum_(i < #|G|) u 0 i * chi (enum_val i).

Lemma xchar_is_linear : forall G (chi : irr_class G), linear (@xchar G chi).
Proof.
move=> G chi k m n.
rewrite scaler_sumr -big_split /=; apply: eq_bigr=> l _.
by rewrite scaler_mull -mulr_addl !mxE.
Qed.

Canonical Structure xchar_linear G (chi : irr_class G) := 
  Linear (xchar_is_linear chi).

(* In order to add a second canonical structure on xchar *)
Definition xcharb G x := (@xchar G)^~ x.

Lemma xcharbE : forall G u (x : 'rV_#|G|), xchar u x = xcharb x u.
Proof. by []. Qed.

Lemma xcharb_is_linear : forall G x, linear (@xcharb G x).
Proof.
move=> G i k m n.
rewrite /xchar scaler_sumr -big_split /=; apply: eq_bigr=> l _.
by rewrite !cfunE mulr_addr scaler_mulr.
Qed.

Canonical Structure xcharb_linear G x := Linear (@xcharb_is_linear G x).

Lemma xchar_trace : forall G u n (chi: mx_representation C G n),
  xchar (char G chi) u = \tr (gring_op chi (gring_mx (regular_repr C G) u)).
Proof.
move=> G u n chi.
rewrite /xchar /gring_op /= gring_mxK /irr_cfun.
apply: (@etrans _ _
   (\sum_(i0 < #|G|) \tr(u 0 i0 *: chi (enum_val i0)))).
  by apply: eq_bigr=> j _; rewrite cfunE enum_valP mul1r mxtraceZ.
rewrite -raddf_sum; congr (\tr _).
apply/matrixP=> i1 j1; rewrite !mxE summxE; apply eq_bigr=> k1 _.
by rewrite !(mxvecE,mxE).
Qed.

Local Notation "'e( G )_" := 
  ((@Wedderburn_id _ _ _ _) \o (@socle_of_irr_class G)) (at level 0).
Local Notation "'R( G )_":= 
  ((@Wedderburn_subring _ _ _ _) \o (@socle_of_irr_class G)) (at level 0).

Lemma xchar_subring : forall G (i j : irr_class G) A, 
  i != j -> (A \in 'R(G)_j)%MS -> xchar i (gring_row A) = 0.
Proof.
move=> G i j A Hi HA.
pose s i := @socle_of_irr_class G i.
rewrite xchar_trace -(mxtrace0 _ (irr_degree (s i))); congr (\tr _).
have F1: s j != irr_comp (sG G) (irr_repr (s i)).
  rewrite irr_reprK //.
  apply/eqP=> HH; case/eqP: Hi; apply/val_eqP.
  by rewrite eq_sym; apply/eqP.
apply: irr_comp'_op0 F1 _ => //; first by apply: socle_irr.
rewrite gring_rowK // -(Wedderburn_sum (sG G) (pGroupG _)).
apply/memmx_sumsP; exists (fun i => (i==s j)%:R *: A).
  rewrite (bigD1 (s j)) //= eqxx scale1r big1 ?addr0 // => k.
  by case: (k == s j); rewrite // scale0r.
by move=> k; case E1: (k == s j); 
  [move/eqP: E1->; rewrite scale1r | rewrite scale0r mem0mx].
Qed.

Lemma xchar_id : forall G (i j : irr_class G),
  xchar i (gring_row ('e(G)_ j)) = if i == j then i 1%g else 0.
Proof.
move=> G i j; case: eqP=> [->|Hi]; last first.
  by apply: xchar_subring (Wedderburn_id_mem _); apply/eqP.
rewrite cfunE group1 mul1r -gring_opG //.
have R1 := (envelop_mx_id (regular_repr C G) (group1 G)).
rewrite -[regular_repr C G 1%g]gring_rowK // -xchar_trace.
rewrite -[regular_repr _ _ _]mul1mx -(Wedderburn_sum_id (sG G) (pGroupG _)).
have->: regular_repr C G 1%g = 1%:M.
  by apply/matrixP=> i1 j1; rewrite !mxE !eqxx mulg1 gring_valK eq_sym.
pose s i := @socle_of_irr_class G i.
rewrite mulmx1 !linear_sum /= (bigD1 (s j)) //= big1; first by rewrite addr0.
move=> k; rewrite eq_sym => Hij.
have F1: j != IrrClass k.
  by apply/eqP; move/val_eqP=> HH; case/negP: Hij.
exact: (xchar_subring F1 (Wedderburn_id_mem k)).
Qed.

Definition base_irr G := map (@irr_cfun G) (enum (irr_class G)).
  
Lemma free_base_irr : forall G, free (base_irr G).
Proof.
move=> G; apply/freeP=> s; set ss := \sum_(i<_) _ => Hs j.
have Hj: (j <  #|irr_class G|)%nat by case: j; rewrite size_map -cardE.
pose j' := enum_val (Ordinal Hj).
suff: xchar ss (gring_row ('e(G)_ j')) = s j * j' 1%g.
  rewrite /xchar big1 //.
    move/eqP; rewrite eq_sym mulf_eq0; case/orP; first by move/eqP.
    rewrite chi1; move/GRing.charf0P: Cchar=> -> He.
    by move: (irr_degree_gt0 (socle_of_irr_class j')); rewrite (eqP He).
  by move=> i _; rewrite Hs cfunE mulr0.
rewrite xcharbE linear_sum; rewrite (bigD1 j) //= big1.
  rewrite  addr0 (nth_map (irr_class1 G)) //; last by rewrite -cardE.
  rewrite linearZ /= -xcharbE.
  suff->: (nth (irr_class1 G) (enum (irr_class G)) j) = j'
    by rewrite  xchar_id eqxx.
  by move: (nth_enum_rank (irr_class1 G) j'); rewrite enum_valK.
move=> i Hij.
have Hi: (i <  #|irr_class G|)%nat.
  by case: {Hij}i; rewrite size_map -cardE.
pose i' := enum_val (Ordinal Hi).
rewrite  (nth_map (irr_class1 G)) //; last by rewrite -cardE.
rewrite linearZ /= -xcharbE.
have->: (nth (irr_class1 G) (enum (irr_class G)) i) = i'.
  by move: (nth_enum_rank (irr_class1 G) i'); rewrite enum_valK.
rewrite  xchar_id; case: eqP; last by rewrite scaler0.
move/eqP=> HH; case/negP: Hij.
by move: HH; rewrite (bij_eq (enum_val_bij (irr_class_finType G))).
Qed.

Lemma base_irr_basis : forall G, is_basis 'CL[C](G) (base_irr G).
Proof.
move=> G; rewrite /is_basis free_base_irr andbT /is_span -dimv_leqif_eq.
   rewrite dim_cfun.
   move: (free_base_irr G); rewrite /free; move/eqP->.
   by rewrite size_map -cardE card_irr_class.
rewrite -span_subsetl; apply/allP=> i; case/mapP=> j _ ->.
apply: char_in_cfun.
Qed.

Lemma sg2bi_ord : forall G (i : irr_class G), 
  (enum_rank i < size (base_irr G))%N.
Proof. by move=> G i; rewrite size_map -cardE. Qed.

Definition sg2bi G (i : irr_class G) := Ordinal (sg2bi_ord i).

Lemma bi2sg_ord : 
  forall G (i : 'I_(size (base_irr G))), (i < #|irr_class G|)%N.
Proof. by move=> G; case=> i; rewrite size_map -cardE. Qed.

Definition bi2sg G (i : 'I_(size (base_irr G))) := 
  enum_val (Ordinal (bi2sg_ord i)).

Lemma bi2sgK : forall G, cancel (@bi2sg G) (@sg2bi G).
Proof. 
by move=> G; case=> i Hi; apply/val_eqP; rewrite /= enum_valK.
Qed.

Lemma sg2biK : forall G, cancel (@sg2bi G) (@bi2sg G).
Proof. 
by move=> G i; rewrite -{2}(enum_rankK i); congr enum_val; apply/val_eqP.
Qed.

Definition ncoord G (i: irr_class G) c : C^o :=
 coord (base_irr G) c (sg2bi i).

Lemma ncoord_sum : forall G (x : cfun_type C gT), x \in 'CL[C](G) -> 
  x = \sum_(i : irr_class G) ncoord i x *: irr_cfun i.
Proof.
move=> G x Hx.
have F1:  {on [pred i | xpredT i], bijective (@bi2sg G)}.
  by apply: onW_bij; exists (@sg2bi G); [apply: bi2sgK | apply: sg2biK].
rewrite (reindex _ F1) /=.
have F2: x \in span (base_irr G).
  move: (is_basis_span (base_irr_basis G)).
  by rewrite /is_span; move/eqP->.
rewrite {1}(coord_span F2); apply: eq_bigr=> i _; congr (_ *: _).
  by rewrite /ncoord bi2sgK.
rewrite  (nth_map (irr_class1 G)).
  by rewrite /bi2sg (enum_val_nth (irr_class1 G)).
rewrite -cardE; apply: bi2sg_ord.
Qed.

Lemma ncoord_is_linear : forall G (i : irr_class G), linear (ncoord i).
Proof.
by move=> G i k c1 c2; rewrite /ncoord linearD linearZ !ffunE.
Qed.

Canonical Structure ncoord_linear G (i : irr_class G) := 
  Linear (ncoord_is_linear i).

Lemma ncoordE : forall G (f : irr_class G -> C)  (x : cfun_type _ _), 
  x \in 'CL[C](G) -> 
   x = \sum_i (f i) *: (irr_cfun i) -> forall i, f i = ncoord i x.
Proof.
move=> G f x Hin Hx i.
suff: (fun j => ncoord (bi2sg j) x -  f (bi2sg j)) =1 (fun _ => 0).
  by move/(_ (sg2bi i)); rewrite sg2biK; move/eqP; rewrite subr_eq0; move/eqP.
move/freeP: (free_base_irr G); apply.
have F1:  {on [pred i | xpredT i], bijective (@sg2bi G)}.
  by apply: onW_bij; exists (@bi2sg G); [apply: sg2biK | apply: bi2sgK ].
rewrite (reindex _ F1) /=.
rewrite (eq_bigr (fun j => ncoord j x *: irr_cfun j -  f j *: irr_cfun j)).
  by rewrite sumr_sub -Hx -ncoord_sum // subrr.
by move=> j _; rewrite sg2biK scaler_subl // (nth_map (irr_class1 G)) -?cardE
                       // nth_enum_rank.
Qed.

Lemma ncoord0 : forall G (i : irr_class G), ncoord i 0 = 0.
Proof.
move=> G i; apply: sym_equal.
apply: (@ncoordE G (fun i => 0:C) 0); first exact: mem0v.
by rewrite big1 // => j _; exact: scale0r.
Qed.

Lemma ncoord_chi : forall G (i j : irr_class G), 
  ncoord j (irr_cfun i) = (i == j)%:R.
Proof.
move=> G i j; apply: sym_equal; apply: (@ncoordE G (fun j => (i == j)%:R)).
  exact: char_in_cfun.
rewrite (bigD1 i) // big1 /= ?(addr0,eqxx,scale1r) // => i1.
by rewrite eq_sym; case: (_ == _)=> //; rewrite scale0r.
Qed.

Definition to_socle G n (rG : mx_representation C G n) (j: DecSocleType rG) :=  
  irr_comp (sG G) (socle_repr j).

Lemma to_socle_inj : forall G n (rG : mx_representation C G n),
  injective (@to_socle G n rG).
Proof.
move=> G n rG x y Hxy.
apply/eqP; apply/socle_rsimP.
apply: (mx_rsim_trans (rsim_irr_comp (sG G) _ (socle_irr _)))=> //.
apply: mx_rsim_sym; move: Hxy; rewrite /to_socle=>->.
by apply: (rsim_irr_comp (sG G) _ (socle_irr _)).
Qed.

Let to_socle_coef G n (rG : mx_representation C G n) (i: (sG G)) :=
oapp (fun i => socle_mult i) 0%N [pick j | i == to_socle (j: DecSocleType rG)].

Lemma ncoord_char : forall G n (rG : mx_representation C G n) (i: irr_class G),
  ncoord i (char G rG) = (to_socle_coef rG (socle_of_irr_class i))%:R.
Proof.
move=> G n rG i; apply: sym_equal.
pose sG':= DecSocleType rG.
apply (@ncoordE G (fun i => (to_socle_coef rG (socle_of_irr_class i))%:R)).
   by exact: char_in_cfun.
pose ts (i: sG') := (to_socle i).
have->: char G rG = 
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
rewrite (reindex (@IrrClass G)) /=; last first.
  by exists (@socle_of_irr_class G)=> // [] [].
have->: 
  \sum_(i0 : sG G)
    (to_socle_coef rG i0)%:R *: (IrrClass i0 : cfun_type _ _) = 
   \sum_(i0: sG G |  codom ts i0) 
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
 forall G m n 
  (rG1 : mx_representation C G m) (rG2 : mx_representation C G n),
  mx_repr G (fun g => block_mx (rG1 g) 0 0 (rG2 g)).
Proof.
move=> G m n repr1 repr2; split=> [|x y Hx Hy].
  by rewrite !repr_mx1 -scalar_mx_block.
by rewrite mulmx_block !(mulmx0,mul0mx,addr0,add0r,repr_mxM).
Qed.

Definition add_repr G m n
  (rG1 : mx_representation C G m) (rG2 : mx_representation C G n)
  := MxRepresentation (add_mx_repr rG1 rG2).

Lemma char_morph : forall G m n
  (rG1 : mx_representation C G m) (rG2 :  mx_representation C G n),
  char G (add_repr rG1 rG2) = char G rG1 + char G rG2.
Proof.
move=> G m n rG1 rG2.
by apply/cfunP=> g; rewrite !cfunE -mulr_addr mxtrace_block.
Qed.

Lemma mx_repr0 : forall G, mx_repr G (fun _ : gT => 1%:M : 'M[C]_0).
Proof. by split=> // g h Hg Hx; rewrite mulmx1. Qed.

Definition repr0 G :=  MxRepresentation (mx_repr0 G).

Lemma char_repr0 : forall G, char G (repr0 G) = 0.
Proof.
by move=> G; apply/cfunP=> g; rewrite !cfunE mxtrace1 mulr0.
Qed.
 
Definition natrepr G (m : nat) (rG : mx_representation C G m) := 
  fix iter (n : nat) : mx_representation C G (n * m) :=
    if n is n1.+1 then add_repr rG (iter n1) else (repr0 G).

Lemma char_natrepr : forall G m n (rG : mx_representation C G m), 
  char G (natrepr rG n) = char G rG *+n.
Proof.
move=> G m n rG; elim: n=> [|n IH].
  by apply/cfunP=> g; rewrite !cfunE mxtrace1 mulr0.
by rewrite /= char_morph IH mulrS.
Qed.

(* !!!!!!!!!!! FOR THE MOMENT AN AXIOM !!!!!!!!!!!!!!!!!!! *)
Lemma char_rsimP : forall G m n (rG1 : mx_representation C G m)
                          (rG2 : mx_representation C G n),
   reflect (mx_rsim rG1 rG2) (char G rG1 == char G rG2).
Proof.
move=> G m n rG1 rG2; apply: (iffP eqP)=> HH; last first.
  apply/cfunP=> g; rewrite !cfunE.
  case E1: (g \in G); last by rewrite !mul0r.
  by rewrite !mul1r; apply: mxtrace_rsim.
admit.
Qed.

Lemma irr_cfun_inj : 
  forall G (i j : irr_class G), i = j :> cfun_type _ _  -> i = j.
Proof.
move=> G i j; move/eqP; move/char_rsimP.
move/(irr_comp_rsim (sG G) (pGroupG G)).
rewrite !irr_reprK //.
by case: i; case: j=>  u v /= ->.
Qed. 
  
Definition cfun_reg G := char G (regular_repr C G).

Lemma cfun_reg_val : forall (G : {group gT}) (g : gT),
  cfun_reg G g = if (g == 1%g) then #|G|%:R else 0.
Proof.
move=> G g; rewrite cfunE.
case: (boolP (g \in G))=> [Hg|]; last first.
  by rewrite !mul0r; case: eqP=> // ->; case/negP; exact: group1.
rewrite mul1r /mxtrace.
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

Lemma cfun_reg_sum : forall G,
 cfun_reg G = \sum_(i : irr_class G) i (1%g) *: irr_cfun i.
Proof.
move=> G; apply/cfunP=> g; rewrite !cfunE.
case Ig: (_ \in _); last first.
  rewrite mul0r sum_cfunE cfunE big1 // => i _.
  by rewrite cfunE [_ g](cfun0 _ (char_in_cfun _)) (mulr0,Ig).
rewrite mul1r mxtrace_regular // sum_cfunE cfunE.
rewrite {1}(reindex (@socle_of_irr_class G)) /=; last first.
  by exists (@IrrClass G)=> [] [].
by apply eq_bigr=> i _; rewrite chi1 !cfunE Ig mul1r // GRing.mulr_natl.
Qed.

Lemma chi_e_mul : forall G (i : irr_class G) A, (A \in group_ring C G)%MS ->
 xchar i (gring_row ('e(G)_ i *m A)) = xchar i (gring_row A).
Proof.
move=> G i A HA.
rewrite -{2}[A]mul1mx -(Wedderburn_sum_id (sG G)) //.
rewrite mulmx_suml !linear_sum (bigD1 (socle_of_irr_class i)) //=.
rewrite big1 ?addr0 // => j; rewrite eq_sym => Hij.
have F1: i != IrrClass j by apply/eqP; move/val_eqP=> HH; case/negP: Hij.
apply: (xchar_subring F1).
case/andP: (Wedderburn_ideal j)=> _ Hj.
apply: submx_trans Hj=> //.
apply: mem_mulsmx=> //.
exact: Wedderburn_id_mem.
Qed.

Lemma xchar_singleton : forall G n g (rG : mx_representation C G n),
  let chi := (char G rG) in
  g \in G -> xchar chi (gring_row (regular_repr C G g)) = chi g.
Proof.
move=> G n g rG chi Hg.
  rewrite /xchar (bigD1 (enum_rank_in (group1 G) g)) // big1 ?addr0.
  by rewrite enum_rankK_in // !mxE gring_indexK // mul1g !eqxx mul1r //= addr0.
move=> i; rewrite !mxE enum_rankK_in // mul1g /gring_index.
by case: (i == _)=> //; rewrite mul0r.
Qed.

(* This corresponds to Issac Th. 2.12 *)
Lemma gring_row_e : forall G (i: irr_class G), 
  gring_row ('e(G)_ i) = \row_j (#|G|%:R^-1 * i 1%g * i ((enum_val j)^-1)%g).
Proof.
move=> G i; apply/rowP=> j.
set j1 := ((enum_val j)^-1)%g.
have Inj1: ((enum_val j)^-1 \in G)%g by rewrite groupV enum_valP.
pose rj := regular_repr C G j1.
have: xchar (cfun_reg G) (gring_row ('e(G)_ i *m rj)) = 
        #|G|%:R * gring_row ('e(G)_ i) 0 j.
  rewrite /xchar (bigD1 (gring_index G 1%g)) //= big1; last first.
    move=> k Hk; rewrite cfun_reg_val.
    case: eqP; last by rewrite mulr0.
    by move=> Hk'; case/negP: Hk; rewrite -Hk' gring_valK.
  rewrite addr0 enum_rankK_in // gring_row_mul.
  rewrite cfun_reg_val // eqxx mulrC; congr (_ * _).
  (* This takes ages 
  rewrite {1}mxE {1}(bigD1 j) //= {1}big1.
  *)
  rewrite {1}mxE {1}(@bigD1 _ _ (GRing.add_comoid C) _ j) //= big1.
    by rewrite !mxE mulgV !eqxx mulr1 addr0.
  move=> k Hk.
  rewrite !mxE eqxx; case: eqP; last by rewrite mulr0.
  move=> Hi; case/negP: Hk.
  apply/eqP; apply: enum_val_inj; apply/eqP; rewrite eq_mulgV1.
  rewrite eq_sym; apply/eqP.
  apply: (can_in_inj (@gring_indexK _ G))=> //.
  by rewrite !(groupM,enum_valP).
rewrite cfun_reg_sum xcharbE linear_sum /=.
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

Lemma irr_repr_abelian : forall G (i : irr_class G) g,
   g \in G -> abelian G -> irr_repr (socle_of_irr_class i) g = (i g)%:M.
Proof.
move=> G i g InG AbG.
rewrite cfunE InG mul1r.
move: (irr_repr (socle_of_irr_class i)); rewrite irr_degree_abelian //.
move=> irr_repr; rewrite trace_mx11.
apply/matrixP=> [] [[|] Hi1] // [[|] Hj1] //.
by rewrite !mxE /= mulr1n; congr fun_of_matrix; apply/eqP.
Qed. 

Lemma chi_exp_abelian : forall G (chi: irr_class G) g n, 
  g \in G -> abelian G -> (chi g)^+n = chi (g^+n)%g.
Proof.
move=> G chi g n Hin AG.
rewrite !cfunE Hin groupX // 2!{1}mul1r.
elim: n=> [|n IH].
  by rewrite expr0 expg0 repr_mx1 mxtrace1 irr_degree_abelian.
rewrite exprS IH expgS repr_mxM ?groupX // {2}irr_repr_abelian //.
by rewrite mul_scalar_mx mxtraceZ cfunE Hin {1}mul1r.
Qed.

Lemma chi_unit_abelian : forall G (chi: irr_class G) g, 
  abelian G -> chi g ^+ #[g] = (g \in G)%:R.
Proof.
move=> G i g AG; case: (boolP (g \in G))=> Hin; last first.
  rewrite (cfun0 Hin (char_in_cfun _)) //.
  by case: #[g] (order_gt0 g)=> [|n] //; rewrite exprS mul0r.
by rewrite chi_exp_abelian // expg_order chi1 irr_degree_abelian.
Qed.

Lemma chi_norm_abelian : forall G (chi : irr_class G) g,
  abelian G -> normC (chi g) = (g \in G)%:R.
Proof.
move=> G i g AG; have := chi_unit_abelian i g AG.
case: (boolP (g \in G)) => Hin Hs; last first.
  by rewrite (cfun0 Hin (char_in_cfun _)) // normC0. 
apply/eqP; rewrite -(@posC_unit_exp _ (#[g].-1)) //; last by exact: posC_norm.
by rewrite prednK // -normC_exp Hs normC1.
Qed.

Lemma chi_inv_abelian : forall G (chi : irr_class G) g,
  g \in G -> abelian G -> chi (g^-1%g) = (chi g)^*.
Proof.
move=> G chi g Hin AG; rewrite invg_expg -chi_exp_abelian //.
have F1 : chi g != 0.
  by rewrite -normC_eq0 chi_norm_abelian // Hin nonzero1r.
apply: (mulfI F1).
rewrite -exprS prednK // chi_unit_abelian // Hin -[_ * _]sqrCK.
move: (chi_norm_abelian chi g); rewrite /normC => -> //.
by rewrite Hin exprS mulr1.
Qed.

Lemma char_inv : forall G n (rG: mx_representation C G n) g,
  char G rG g^-1%g = (char G rG g)^*.
Proof.
move=> G n rG g.
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

Let card_neq0 : forall (G : {group gT}), #|G|%:R^-1 != 0 :> C.
Proof.
move=> G; rewrite invr_eq0; move/GRing.charf0P: Cchar->.
by move: (cardG_gt0 G); case: #|_|.
Qed.

(* Painfully following Issac's proof 2.14 *)
Lemma chi_first_orthogonal_relation : forall G (i j: irr_class G),
 (#|G|%:R^-1 * \sum_(g \in G) i g * (j g)^*)%R = (i == j)%:R.
Proof.
move=> G i j.
rewrite (reindex invg) /=; last by apply: onW_bij; apply: inv_bij; exact invgK.
have F1 : 'e(G)_ i *m 'e(G)_ j = (i == j)%:R *: 'e(G)_ i.
  case: eqP=> [<-|Hij]; [rewrite scale1r | rewrite scale0r].
    case: (Wedderburn_is_id (pGroupG _) (socle_of_irr_class i))=> _ Hi Hj _.
    by exact: Hj.
  move/eqP: Hij=> HH; apply: (Wedderburn_mulmx0 HH); exact: Wedderburn_id_mem.
have F2: #|G|%:R^-1 * i 1%g * j 1%g != 0.
  by do 2 (apply: mulf_neq0; last by exact: chi1_neq0).
apply: (mulIf F2).
pose r1 (u: 'M[C]_#|G|) := gring_row u 0 (gring_index G 1%g).
apply: (@etrans _ _ (r1 ('e(G)_ i *m 'e(G)_ j))); last first.
  rewrite F1 /=; case: eqP=> [->|_].
    by rewrite scale1r mul1r /r1 gring_row_e !mxE gring_indexK // invg1.
  rewrite scale0r mul0r /r1.
  suff->: @gring_row C _ G 0 = 0 by rewrite mxE.
  by apply/rowP=> k; rewrite !mxE.
pose gr i g := gring_row ('e(G)_ (i: irr_class G)) 0 (gring_index G g). 
suff->:
    r1 ('e(G)_ i *m 'e(G)_ j) = \sum_(g \in G) gr i g * gr j (g^-1)%g.
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
have F3: ('e(G)_ j \in group_ring C G)%MS.
  apply (submx_trans (Wedderburn_id_mem _)).
  by rewrite /Wedderburn_subring genmxE submxMl.
rewrite -{1}(gring_rowK F3) mxE.
  (* This takes ages
rewrite {1}(reindex (@enum_val _ (fun x=> x \in G))) /=; last first.
  *)
rewrite {1}(@reindex _ _ (GRing.add_comoid C) _ _
     (@enum_val _ (fun x=> x \in G))) /=; last first.
  by exists (gring_index G)=> g Hg; [exact: gring_valK | apply: gring_indexK].
apply: eq_big=> [g|i1 _]; first by rewrite enum_valP.
rewrite  /gr !gring_valK; congr (_ * _).
rewrite 2!mxE.
  (* This takes ages
rewrite {1}(@bigD1 (gring_index G (enum_val i1)^-1)) //=.
  *)
rewrite {1}(@bigD1 _ _  (GRing.add_comoid C) _ 
                        (gring_index G (enum_val i1)^-1)) //=.
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

Lemma chi_second_orthogonal_relation : forall G (y z: gT), 
 y \in G -> z \in G ->
 \sum_(chi : irr_class G) chi y * (chi z)^* =
   if y \in (z ^: G) then #|'C_G[z]|%:R else 0.
Proof.
move=> G y z Hy Hz.
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
apply: (mulfI (mulf_neq0 Hi1 (card_neq0 G))); rewrite -mulr_sumr.
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

Lemma chi_conjugate : forall G (y z: gT), y \in G -> z \in G ->
  reflect (forall chi : irr_class G, chi y = chi z) (y \in (z ^: G)).
Proof.
move=> G y z Hy Hz; apply: (iffP idP)=> [HH chi|HH].
  case/imsetP: HH=> x Hx ->.
  by rewrite (cfunJ Hz) // char_in_cfun.
move: (chi_second_orthogonal_relation Hy Hz); case: (_ \in _)=> // HH1.
move: (fun I=> posC_sum_eq0 I HH1).
have F1:  forall chi : irr_class G, 
  (chi \in index_enum (irr_class_finType G)) && xpredT chi -> 
     0 <= chi y * (chi z)^*.
  by move=> chi _; rewrite HH /leC subr0 repC_pconj.
case/eqP: (nonzero1r C).
move: (posC_sum_eq0 F1 HH1); move/(_ (irr_class1 G)).
rewrite !irr_class1E Hy Hz conjC1 mul1r; apply=> //.
by rewrite  /index_enum -enumT mem_enum.
Qed.

Definition inner_prod (G : {set gT}) (f g : cfun_type _ _) :=
  #|G|%:R^-1 * \sum_(i \in G) f i * (g i)^*.

Local Notation "'[ f , g ]@ G" := (inner_prod G f g) (at level 0).

Let card_conj : forall G, (#|G|%:R^-1)^* = #|G|%:R^-1.
Proof.
by move=> G; rewrite posC_conjK // posC_inv leC_nat.
Qed.

Lemma inner_conj : forall G f g, '[f,g]@G = '[g,f]@G^*.
Proof.
move=> G f g; rewrite /inner_prod rmorphM card_conj.
congr (_ * _); rewrite rmorph_sum; apply: eq_bigr=> i _.
by rewrite rmorphM conjCK mulrC.
Qed.
 
Lemma posC_inner_prod : forall G f, 0 <= '[f, f]@G.
Proof. 
move=> G f; apply: posC_mul; first by rewrite posC_inv leC_nat.
by rewrite posC_sum // => i _; rewrite /leC subr0 repC_pconj.
Qed.

Lemma inner_prod0 : forall G f, f \in 'CL[C](G) -> ('[f, f]@G == 0) = (f == 0).
Proof.
move=> G f Hf; apply/eqP/eqP=> Hp; last first.
  by rewrite Hp /inner_prod big1 ?mulr0 // => i _; rewrite !cfunE mul0r.
apply/cfunP=> g; rewrite cfunE.
case: (boolP (g \in G))=> Hin; last by rewrite (cfun0 Hin).
suff: f g * (f g)^* == 0.
  by rewrite mulf_eq0; case/orP; [move/eqP|rewrite conjC_eq0;move/eqP].
move: Hp; move/eqP; rewrite /inner_prod mulf_eq0; case/orP=> [|Hp].
  by rewrite (negPf (card_neq0 G)).
apply/eqP; apply: (posC_sum_eq0 _ (eqP Hp))=> //.
 by move=>*; rewrite -sqrC_pos; exact: posC_norm.
by rewrite /index_enum -enumT mem_enum.
Qed.

Definition inner_prodb G f := (@inner_prod G)^~ f.

Lemma inner_prodbE : forall G f g, inner_prodb G f g = inner_prod G g f.
Proof. by []. Qed.

Lemma inner_prodb_is_linear : forall G f, linear (inner_prodb G f : _ -> C^o).
Proof.
move=> G f k g1 g2.
rewrite /inner_prodb /inner_prod.
rewrite {1}scaler_mulr -{1}scaler_addr; congr (_ * _).
rewrite {1}scaler_sumr /= -{1}big_split /=; apply: eq_bigr=> i _.
by rewrite scaler_mull -mulr_addl !cfunE.
Qed.

Canonical Structure inner_prodb_linear G f :=
  Linear (inner_prodb_is_linear G f).

Lemma inner_prod_is_additive : forall G f, additive (inner_prod G f).
Proof.
move=> G f g1 g2.
rewrite /inner_prod /inner_prod.
rewrite -mulr_subr; congr (_ * _).
rewrite -sumr_sub; apply: eq_bigr=> i _.
by rewrite !cfunE rmorph_sub // mulr_subr.
Qed.

Canonical Structure inner_prod_additive G f := 
  Additive (inner_prod_is_additive G f).

Lemma inner_prodZ : forall G k f g, '[f, k *: g]@G = k^* * '[f,g]@G.
Proof.
move=> G k f g; rewrite /inner_prod.
rewrite mulrCA; congr (_ * _).
rewrite -mulr_sumr; apply: eq_bigr=> i _.
by rewrite !cfunE rmorphM mulrCA.
Qed.

Lemma chi_orthonormal : forall G (i j: irr_class G), '[i,j]@G = (i == j)%:R.
Proof.
by move=> G i j; rewrite -chi_first_orthogonal_relation; congr (_ * _).
Qed.

Definition is_char G (f : cfun_type C gT) :=
  all (fun i : irr_class G => isNatC (ncoord i f)) (enum (irr_class G)) &&
  (f \in 'CL[C](G)).

Lemma is_charP : forall (G : {group gT}) f,
  reflect (exists n, exists rG : mx_representation C G n, char G rG = f)
          (is_char G f).
Proof.
move=> G f; apply: (iffP andP); last first.
  case=> n [rG <-]; split; last exact: char_in_cfun.
  by apply/allP=> chi _; rewrite ncoord_char isNatC_nat.
case; move/allP=> Ha Hf.
pose n' (j : irr_class G) := getNatC (ncoord j f).
have->: f = \sum_(j : irr_class G) (n' j)%:R *: (j : cfun_type _ _).
  rewrite {1}(ncoord_sum Hf); apply: eq_bigr=> i _.
  congr (_ *: _); apply/eqP; rewrite -getNatCP; apply: Ha.
  by exact: mem_enum.
elim: {n'}(\sum_j (n' j))%N {-2}n' (leqnn (\sum_j (n' j)))=> [| N IH] n' HS.
  exists 0%N; exists (repr0 G).
  apply/cfunP=> i; rewrite sum_cfunE !cfunE mxtrace1 mulr0 big1 // => j Hj.
  by move: HS; rewrite (bigD1 j) //=; case: (n' j)=> //; rewrite scale0r cfunE.
case: (boolP (all (fun i => n' i == 0%N) (enum (irr_class G)))).
  move/allP=> HH.
  exists 0%N; exists (repr0 G).
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

Lemma is_char_char : forall G n (rG : mx_representation C G n),
  is_char G (char G rG).
Proof.
by move=> G n rG; apply/is_charP; exists n; exists rG.
Qed.

Definition crestrict (G : {set gT}) (f : cfun_type C gT) :=
    cfun_of_fun (fun g : gT => (g \in G)%:R * (f g)).

Local Notation "'{ f | G }" := (crestrict G f).

Lemma crestrictE : forall G f, {in G, '{f|G} =1 f}.
Proof.
by move=> G f g H; rewrite cfunE H mul1r.
Qed.
 
Lemma cfun_subset : forall f (G H : {group gT}), 
  H \subset G -> f \in 'CL[C](G) -> '{f|H} \in 'CL[C](H).
Proof.
move=> f G H Hsub fC; apply/cfun_memP; split.
  by move=> g; rewrite cfunE; case: (_ \in _)=> //; rewrite mul0r.
move=> g h gIn hIn; rewrite !cfunE groupJ //.
by rewrite gIn (cfunJ _ _ fC) // (subsetP Hsub).
Qed.

Lemma is_char_subset : forall f (G H : {group gT}), 
  H \subset G -> is_char G f -> is_char H '{f|H}.
Proof.
move=> f G H Hsub; case/is_charP=> n [rG <-].
apply/is_charP; exists n; exists (subg_repr rG Hsub).
apply/cfunP=> g; rewrite !cfunE; case E1: (_ \in _); last by rewrite !mul0r.
by rewrite (subsetP Hsub) // !mul1r.
Qed.

Lemma is_char_irr : forall G (i : irr_class G), is_char G i.
Proof. 
move=> G1 i; apply/is_charP; pose i' := socle_of_irr_class i.
by exists (irr_degree i'); exists (irr_repr i').
Qed.

Lemma is_char_ncoord : forall G (i : irr_class G) f,
  is_char G f -> isNatC (ncoord i f).
Proof.
move=> G i f; case/is_charP=> n [rG <-].
by rewrite ncoord_char isNatC_nat.
Qed.

Lemma is_char0 : forall G, is_char G 0.
Proof.
by move=> G; rewrite -(char_repr0 G) is_char_char.
Qed.

Lemma is_char_add : forall G f1 f2, 
  is_char G f1 -> is_char G f2 -> is_char G (f1 + f2).
Proof.
move=> G1 f1 f2; case/is_charP=> m [rG1 HrG1]; case/is_charP=> n [rG2 HrG2].
apply/is_charP; exists (m + n)%N; exists (add_repr rG1 rG2).
by rewrite char_morph HrG1 HrG2.
Qed.

Lemma is_char_scal : forall G f k, 
  isNatC k -> is_char G f -> is_char G (k *: f).
Proof.
move=> G f k; case/isNatCP=> n -> Hf; elim: n=> [|n Hn].
  by rewrite scale0r is_char0.
by rewrite -add1n natr_add scaler_addl scale1r is_char_add.
Qed.

Lemma is_char_in_cfun : forall G f, is_char G f -> f \in 'CL[C](G).
Proof.
by move=> G f; case/is_charP=> n [rG <-]; apply: char_in_cfun.
Qed.

Lemma is_char_cb : forall G (P: _ -> bool) n,
 is_char G (\sum_(i : irr_class G | P i) (n i)%:R *: irr_cfun i).
Proof.
move=> G P n.
elim: {n}(\sum_(i | P i) (n i))%N {-2}n (leqnn (\sum_(i | P i) (n i)))=>
       [|N IH] n.
  move=> Hn; rewrite big1 ?is_char0 //.
  move=> i Pi; move: Hn; rewrite (bigD1 i) //.
  by case: (n i)=> //; rewrite scale0r.
case: (boolP (all (fun i => n i == 0%N) (filter P (enum (irr_class G))))).
  move/allP=> Hi Hn.
  rewrite big1  ?is_char0 //.
  move=> i Pi; move: (Hi i); rewrite mem_filter Pi mem_enum.
  by move/(_ is_true_true); move/eqP->; rewrite scale0r.
case/allPn=> i; rewrite mem_filter mem_enum; case/andP=> H1i H2i H3i HH.
pose n' (j : irr_class G) := if (j == i) then (n j).-1 else n j.
have F1: (\sum_(i | P i) (n i) = (\sum_(i | P i) (n' i)).+1)%N.
  rewrite (bigD1 i) // [(\sum_(i | P i) n' i)%N](bigD1 i) //= -add1n addnA.
  congr (_ + _)%N; first by rewrite /n' eqxx; case: (n i) H3i.
  by apply: eq_bigr=> j; case/andP=> H1j H2j; rewrite /n' (negPf H2j).
have F2: \sum_(i | P i) (n i)%:R *: irr_cfun i  = 
           irr_cfun i + \sum_(i | P i) (n' i)%:R *: irr_cfun i.
  rewrite (bigD1 i) //= [\sum_(i | P i) (n' i)%:R *: irr_cfun i](bigD1 i) //=.
  rewrite addrA; congr (_ + _).
    rewrite /n' eqxx; case: (n i) H3i=> // m' _.
    by rewrite -{1}add1n natr_add scaler_addl scale1r.
  by apply: eq_bigr=> j; case/andP=> H1j H2j; rewrite /n' (negPf H2j).
rewrite F2; apply is_char_add; first exact: is_char_irr.
by apply: IH; rewrite -ltnS -F1.
Qed.

Lemma is_char_cbP : forall G f,
  reflect 
    (exists n, f = \sum_(i : irr_class G) (n i)%:R *: irr_cfun i)
    (is_char G f).
Proof.
move=> G f; apply: (iffP idP)=> [HH|[n ->]]; last exact: is_char_cb.
exists (fun i => getNatC (ncoord i f)).
rewrite {1}(ncoord_sum (is_char_in_cfun HH)).
apply: eq_bigr=> i _.
by move/(@is_char_ncoord G i): HH; rewrite getNatCP; move/eqP<-.
Qed.

Lemma inner_prod_char :
  forall G ch1 ch2, is_char G ch1 -> is_char G ch2 ->
   '[ch1,ch2]@G = \sum_(i : irr_class G) (ncoord i ch1) * (ncoord i ch2).
Proof.
move=> G ch1 ch2; case/is_charP=> m [rG1 <-]; case/is_charP=> n [rG2 <-].
rewrite (ncoord_sum (char_in_cfun _))
        [char _ rG2](ncoord_sum (char_in_cfun _)).
rewrite -inner_prodbE linear_sum /=.
apply: eq_bigr=> i _; rewrite inner_prodbE.
rewrite raddf_sum /= {1}(bigD1 i) // big1 //= => [|j Hj];
    rewrite inner_prodZ -{1}inner_prodbE {1}[inner_prodb _ _ _]linearZ /= 
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
  forall G ch1 ch2, is_char G ch1 -> is_char G ch2 -> isNatC '[ch1,ch2]@G.
Proof.
move=> G ch1 ch2 Hch1 Hch2; rewrite inner_prod_char //.
apply: isNatC_sum=> i _.
by apply: isNatC_mul; [case/is_charP: Hch1|case/is_charP: Hch2];
  move=> n [rG <-]; rewrite ncoord_char; exact: isNatC_nat.
Qed.
 
Lemma inner_prod_charC : forall G ch1 ch2,
  is_char G ch1 -> is_char G ch2 -> '[ch1,ch2]@G = '[ch2,ch1]@G.
Proof.
move=> G ch1 ch2 Hc1 Hc2.
by rewrite !inner_prod_char //; apply: eq_bigr=> i _; rewrite mulrC.
Qed.

Lemma char_irreducibleP : forall G ch, is_char G ch ->
  reflect (exists chi : irr_class G, ch = chi) ('[ch, ch]@G == 1).
Proof.
move=> G ch Hch; apply: (iffP idP); last first.
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
move: HF; rewrite ncoord_char -natr_mul /to_socle_coef.
case: (oapp _ _)=>//; case=> // m.
rewrite mulnS addSn -{2}[1]add0r -addn1 natr_add => HH1.
by move: (addIr HH1); move/eqP; move/charf0P: Cchar->.
Qed.

Lemma is_char_norm : forall G f (g : gT), is_char G f ->
  normC (f g) <= f 1%g.
Proof.
move=> G f g; case/is_charP=> n [rG <-].
case: (boolP (g \in G))=> Hin; last first.
  by rewrite (cfun0 Hin (char_in_cfun _)) // normC0 char1 leC_nat.
have F1: (<[g]> \subset G) by rewrite cycle_subG.
pose rG' := subg_repr rG F1.
have Hf: forall g1, g1 \in <[g]> -> char G rG g1 = char <[g]> rG' g1.
  by move=> g1 Hg1; rewrite !cfunE Hg1; move/subsetP: (F1)->.
rewrite !Hf ?(cycle_id,group1) // (ncoord_sum (char_in_cfun _)).
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

Definition cker G (f : cfun_type C gT) := 
  if is_char G f then [set g \in G | f g == f 1%g] else 1%G.

Lemma is_char_cker : forall G f,
   is_char G f -> cker G f = [set g \in G | f g == f 1%g].
Proof. by move=> G f Hf; rewrite /cker Hf. Qed.

Lemma is_Nchar_cker : forall G f, ~is_char G f -> cker G f = 1%G.
Proof. by move=> G f Hf; rewrite /cker; move/eqP: Hf; case: is_char. Qed.

Definition cfaithful G f := cker G f \subset 1%G.

Lemma ckerE : forall G f, is_char G f -> 
  cker G f = if f == 0 then (G : {set _}) else
             \bigcap_(i : irr_class G | ncoord i f != 0) cker G i.
Proof.
move=> G f Hf; rewrite is_char_cker //.
case: eqP=> [->|Hdf].
  by apply/setP=> g; rewrite !inE !cfunE eqxx andbT.
apply/setP=> g; apply/idP/bigcapP=> [|Hi]; last first.
  have InG: g \in G.
   case: (boolP (all (fun i => ncoord i f == 0%:R) (enum (irr_class G)))).
     move/allP=> HH; case Hdf.
     rewrite (ncoord_sum (is_char_in_cfun Hf)); apply: big1=> i1 Hi1.
     suff->: ncoord i1 f = 0 by exact: scale0r.
     by apply/eqP; apply: HH=> //; rewrite mem_enum.
    case/allPn=> k kIn Hk; move: (Hi _ Hk).
    by rewrite is_char_cker ?is_char_irr // inE; case/andP.
  case/andP: (Hf)=> _ H1f.
  rewrite inE /= (ncoord_sum H1f) !sum_cfunE !cfunE InG; apply/eqP.
  apply: eq_bigr=> chi _; rewrite cfunE [_ 1%g]cfunE.
  case: (ncoord chi f =P 0) (Hi chi)=> [->|_]; first by rewrite !mul0r.
  rewrite is_char_cker ?is_char_irr // !inE.
  by move/(_ is_true_true); rewrite InG; move/eqP->.
rewrite inE; case/andP=> InG.
case/andP: (Hf)=> _ H1f; rewrite (ncoord_sum H1f) !sum_cfunE !cfunE.
move/eqP=> Hs i; rewrite is_char_cker ?is_char_irr // !inE InG.
have<-: f =
   cfun_of_fun (fun x : gT => 
                  \sum_(i:irr_class G) (ncoord i f *: irr_cfun i) x).
  by apply/cfunP=> x; rewrite cfunE {1}(@ncoord_sum G f) // sum_cfunE cfunE.
move=> Hd.
have F: (ncoord i f *: irr_cfun i) g = (ncoord i f *: irr_cfun i) 1%g.
  have F1: 0 <= ncoord i f by apply: posC_isNatC; rewrite is_char_ncoord.
  apply: (normC_sum_upper _ Hs)=> [j Hj|]; last first.
    by rewrite /index_enum -enumT mem_enum.
  have F2: 0 <= ncoord j f by apply: posC_isNatC; rewrite is_char_ncoord.
  rewrite cfunE [(ncoord j f *: irr_cfun j) 1%g]cfunE !normC_mul //.
  by rewrite normC_pos // leC_mul2l // (is_char_norm _ (is_char_irr j)).
apply/eqP; apply: (mulfI Hd).
by move: F; rewrite cfunE => ->; rewrite !cfunE.
Qed. 

Lemma cker_all1 : forall G, \bigcap_(i : irr_class G) cker G i = 1%G.
Proof.
move=> G.
apply/setP=> g; apply/idP/idP; rewrite inE; last first.
  move/eqP->; apply/bigcapP=> i _.
  by rewrite is_char_cker ?is_char_irr // inE group1 eqxx.
have F1: (\bigcap_(i : irr_class G) cker G i) \subset cker G (cfun_reg G).
  rewrite (ckerE (is_char_char _)).
  case: eqP=> Heq.
    have: char G (regular_repr C G) 1%g = 0 by rewrite Heq cfunE.
    rewrite cfunE group1 repr_mx1 mxtrace1 mul1r.
    by move/eqP; move/charf0P: Cchar->; rewrite (cardD1 1%g) group1.
  apply/subsetP=> h; move/bigcapP=> Hi; apply/bigcapP=> j _.
  by exact: Hi.
move/(subsetP F1); rewrite is_char_cker ?is_char_char // inE !cfun_reg_val //.
case/andP=> InG; rewrite eqxx; case: (g == 1%g)=> //.
rewrite eq_sym; move/charf0P: Cchar->.
by rewrite (cardD1 1%g) group1.
Qed.

Let char_rker_aux : forall G (P: _ -> bool) g,
  g \in G ->
  (forall i : irr_class G, P i -> irr_repr (socle_of_irr_class i) g == 1%:M) ->
  forall n m (rG: mx_representation C G m),
  \sum_(i : irr_class G | P i) (n i)%:R *: irr_cfun i = char G rG -> 
  g \in rker rG.
Proof.
move=> G P g Ing Hg n.
elim: {n}(\sum_(i | P i) (n i))%N {-2}n (leqnn (\sum_(i | P i) (n i)))=>
       [|N IH] n.
  move=> Hn m rG; rewrite big1; last first.
    by move=> i Pi; move: Hn; rewrite (bigD1 i) //=; case: (n i)=> //; rewrite scale0r.
  rewrite -(char_repr0 G)=> HH; apply/rkerP; split=> //; apply/matrixP=> [] [i Hi].
  by case/negP: Hi; move/eqP: HH; move/char_rsimP; move/mxrank_rsim<-.
case: (boolP (all (fun i => n i == 0%N) (filter P (enum (irr_class G))))).
  move/allP=> Hi _ m rG.
  rewrite big1; last first.
    move=> i Pi; move: (Hi i); rewrite mem_filter Pi mem_enum.
    by move/(_ is_true_true); move/eqP->; rewrite scale0r.
  rewrite -(char_repr0 G)=> HH; apply/rkerP; split=> //; apply/matrixP=> [] [j Hj].
  by case/negP: Hj; move/eqP: HH; move/char_rsimP; move/mxrank_rsim<-.
case/allPn=> i; rewrite mem_filter mem_enum; case/andP=> H1i H2i H3i HH m rG Hs.
pose n' (j : irr_class G) := if (j == i) then (n j).-1 else n j.
have F1: (\sum_(i | P i) (n i) = (\sum_(i | P i) (n' i)).+1)%N.
  rewrite (bigD1 i) // [(\sum_(i | P i) n' i)%N](bigD1 i) //= -add1n addnA.
  congr (_ + _)%N; first by rewrite /n' eqxx; case: (n i) H3i.
  by apply: eq_bigr=> j; case/andP=> H1j H2j; rewrite /n' (negPf H2j).
have F2: \sum_(i | P i) (n i)%:R *: irr_cfun i  = 
           irr_cfun i + \sum_(i | P i) (n' i)%:R *: irr_cfun i.
  rewrite (bigD1 i) //= [\sum_(i | P i) (n' i)%:R *: irr_cfun i](bigD1 i) //=.
  rewrite addrA; congr (_ + _).
    rewrite /n' eqxx; case: (n i) H3i=> // m' _.
    by rewrite -{1}add1n natr_add scaler_addl scale1r.
  by apply: eq_bigr=> j; case/andP=> H1j H2j; rewrite /n' (negPf H2j).
case/is_charP: (@is_char_cb G P n')=> n1 [rG1 HrG1].
pose rG' := add_repr (irr_repr (socle_of_irr_class i)) rG1.
have ->: rker rG = rker rG'.
   apply: rker_mx_rsim; apply/char_rsimP; rewrite char_morph.
   by rewrite HrG1 -F2 Hs.
apply/rkerP; split=>//.
have: g \in rker rG1.
  by apply: IH (sym_equal HrG1); rewrite -ltnS -F1.
case/rkerP=> _ Hr1.
by rewrite /rG' /= (eqP (Hg i H1i)) Hr1 block_mx1.
Qed.

Lemma char_rkerP : forall G n (rG : mx_representation C G n), 
  cker G (char G rG) = rker rG.
Proof.
move=> G n rG.
rewrite is_char_cker ?is_char_char //.
apply/setP=> g; apply/idP/rkerP=>[Hg |[H1 H2]]; last first.
  by rewrite inE !cfunE H1 H2 repr_mx1 !group1 mul1r mxtrace1 eqxx.
have InG: g \in G by move: Hg; rewrite inE; case/andP.
split=> //.
have F1: (<[g]> \subset G) by rewrite cycle_subG.
pose rG' := subg_repr rG F1.
have H'g: g \in cker <[g]> (char <[g]> rG').
  move: Hg; rewrite is_char_cker ?is_char_char //.
  by rewrite /rG' !inE !cfunE !group1 !InG cycle_id !mul1r.
suff: g \in rker rG' by rewrite inE mul1mx; case/andP=> _; move/eqP.
have Abg := cycle_abelian g.
have Ing := cycle_id g.
apply: (@char_rker_aux <[g]> (fun i => ncoord i (char <[g]>%G rG') != 0)
             g (cycle_id _) _ (fun i => getNatC (ncoord i (char <[g]>%G rG')))).
  move=> i Hi.
  have: g \in cker <[g]> i.
    move: H'g; rewrite ckerE ?is_char_char //.
    case: eqP=> HH; first by case/negP: Hi; rewrite HH ncoord0.
    by move/bigcapP; apply.
  rewrite is_char_cker ?is_char_irr // inE; case/andP=> _;case/eqP.
  rewrite irr_repr_abelian // => ->. 
  by rewrite char1 irr_degree_abelian.
rewrite big_mkcond /= {3}(ncoord_sum (is_char_in_cfun (is_char_char rG'))).
apply: eq_bigr=> i Hi; case: eqP=>[->|HH]; first by rewrite scale0r.
by move: (is_char_ncoord i (is_char_char rG')); rewrite getNatCP; move/eqP<-.
Qed.

Lemma cker_group_set : forall G f, group_set (cker G f).
Proof.
move=> G f; case: (boolP (is_char G f))=> Hf.
  case/is_charP: Hf=> n [rG <-]; rewrite char_rkerP //.
  by exact: rstab_group_set.
rewrite is_Nchar_cker; last by move/negP: Hf.
by exact: group_set_one.
Qed.

Canonical Structure cker_group G f := Group (cker_group_set G f).

Lemma cker_normal : forall G f, cker G f <| G.
Proof.
move=> G f; case: (boolP (is_char G f))=> Hf.
  by case/is_charP: Hf=> n [rG <-]; rewrite char_rkerP // rker_normal.
rewrite is_Nchar_cker; last by move/negP: Hf.
by exact: normal1.
Qed.

End Main.

Section Coset.

Variable (gT : finGroupType).

Hypothesis groupC : group_closure_field C gT.

Implicit Type G : {group gT}.

Let pGroupG : forall G, [char C]^'.-group G.
Proof.
by move=> G; apply: sub_pgroup (pgroup_pi G)=> i _; rewrite inE /= Cchar.
Qed.

Definition qfun_of_cfun (N: {set gT}) (f : cfun_type C gT) :=
  cfun_of_fun (fun x : coset_of N => f (repr x)).

Local Notation "'{ f '^/' N }" := (qfun_of_cfun N f).

Definition cfun_of_qfun (N: {set gT}) (f : cfun_type C (coset_groupType N)) :=
  cfun_of_fun (fun x : gT => (x \in 'N(N))%:R * f (coset N x)).


Local Notation "'{ f '^()' }" := (cfun_of_qfun f).

Lemma is_char_ckerM : forall (G N : {group gT}) f x y,
 is_char G f -> x \in N -> y \in G -> N \subset cker G f -> 
   f (x * y)%g = f y.
Proof.
move=> G N f x y Cf Inx Iny.
case/is_charP: Cf=> // n [rG <-] Ncker.
have InG: x \in G.
  apply: (subsetP (normal_sub (cker_normal _ G (char G rG)))) => //.
  by apply: (subsetP Ncker).
rewrite !cfunE groupM ?Iny // repr_mxM //.
move: ((subsetP Ncker) _ Inx).
rewrite char_rkerP // inE InG mul1mx andTb; move/eqP->.
by rewrite mul1mx.
Qed.

Let repr_quo_fact1 : forall (G N: {group gT}) (M : coset_of N),
 N <| G -> (repr M \in G) = (M \in (G / N)%g).
Proof.
move=> G N M NN; rewrite -imset_coset; apply/idP/imsetP.
  by move=> InG; exists (repr M)=> //; rewrite coset_reprK.
case=> g Hg ->.
rewrite  val_coset ?(subsetP (normal_norm NN)) //.
suff: N :* g \subset G by move/subsetP=>-> //; apply: mem_repr_rcoset.
apply/subsetP=> x; case/rcosetP=> y Hy ->; apply: groupM=> //.
by apply: (subsetP (normal_sub NN)).
Qed.

Let repr_quo_fact2 : forall (G N: {group gT}) g,
 N <| G -> (g \in 'N(N)) && (coset N g \in (G/N)%g) = (g \in G).
Proof.
move=> G N g NN.
rewrite -imset_coset; apply/andP/idP=>[[HN]|HH]; last first.
  split; first by apply: (subsetP (normal_norm NN)).
  by apply/imsetP; exists g.
case/imsetP=> h InH.
have HH: h \in 'N(N) by apply: (subsetP (normal_norm NN)).
move/(rcoset_kercosetP HN HH); rewrite mem_rcoset=> InNM.
suff->: g = ((g * h^-1)*h)%g.
  by rewrite groupM // (subsetP (normal_sub NN)).
by rewrite -mulgA mulVg mulg1.
Qed.

Lemma is_char_qfunc : forall (G N : {group gT}) f,
  is_char G f -> N <| G -> N \subset cker G f -> is_char (G/N) '{f ^/ N}.
Proof.
move=> G N f; case/is_charP=> // n [rG <-] HN HC.
move: (HC); rewrite char_rkerP=> HC' //.
pose rG' := quo_repr HC' (normal_norm HN).
suff->: '{char G rG ^/ N} = char (G/N)%g rG'.
  by apply: is_char_char; exact: coset_splitting_field.
by apply/cfunP=> M; rewrite !cfunE repr_quo_fact1.
Qed.

Lemma qfuncE : forall (G N : {group gT}) f x,
 is_char G f -> N <| G -> N \subset cker G f -> x \in G -> 
  '{f ^/ N} (coset N x) = f x.
Proof.
move=> G N f x Cf NN  Ncker InG; rewrite !cfunE.
rewrite val_coset //; last by apply: (subsetP (normal_norm NN)).
by case: repr_rcosetP=> y Hy; apply: (is_char_ckerM Cf Hy).
Qed.

Lemma cfunqE : forall (N : {group gT}) f x,
 x \in 'N(N) -> '{f ^()} x = f (coset N x).
Proof. by move=> N f x InG; rewrite !cfunE InG // mul1r. Qed.

Lemma is_char_cfunq : forall (G N : {group gT}) f,
  N <| G -> is_char (G/N) f -> is_char G '{f^()}.
Proof.
move=> G N f NN; case/is_charP; first by exact: coset_splitting_field.
move=> n [rG <-].
pose rG' := coset_repr rG NN.
suff->: '{char (G/N)%g rG ^()} = char G rG' by apply: is_char_char.
apply/cfunP=> M; rewrite !cfunE mulrA -natr_mul mulnb.
rewrite repr_quo_fact2 //.
Qed.

(* We could do better *)
Lemma cker_cfunq : forall (G N : {group gT}) f,
 is_char (G/N) f -> N <| G -> N \subset cker G '{f^()}.
Proof.
move=> G N f Cf HN.
have F1: is_char G '{f^()} by apply: is_char_cfunq.
apply/subsetP=> g Hg.
have InG: g \in G by apply: (subsetP (normal_sub HN)).
rewrite /cker F1 inE InG !cfunqE ?group1 //.
- by rewrite !coset_id // eqxx.
by apply: (subsetP (normal_norm HN)).
Qed.

Lemma cfunq_id : forall (G N : {group gT}) f,
 is_char (G/N) f -> N <| G -> '{'{f^()} ^/ N} = f.
Proof.
move=> G N f Cf HN.
have FC: group_closure_field C (coset_groupType N).
  by apply: coset_splitting_field.
have F1: is_char G '{f^()} by apply: is_char_cfunq.
have F2:= cker_cfunq Cf HN.
have F3: is_char (G/N) '{'{f^()} ^/ N} by apply: is_char_qfunc.
apply/cfunP=> x.
case: (boolP (x \in (G/N)%g))=> [|InG]; last first.
  rewrite (cfun0 _ (is_char_in_cfun _ Cf)) //.
  by apply: (cfun0 _ (is_char_in_cfun _ F3)).
rewrite -imset_coset; case/imsetP=> y InG ->.
rewrite (@qfuncE G) //  cfunqE //.
by apply: (subsetP (normal_norm HN)).
Qed.

Lemma qfunc_id : forall (G N : {group gT}) f,
 is_char G f -> N <| G -> N \subset cker G f -> '{'{f^/N} ^()} = f.
Proof.
move=> G N f Cf HN Hc.
have F1: is_char (G/N) '{f^/N} by apply: is_char_qfunc.
have F2: is_char G '{'{f^/N} ^()} by apply: is_char_cfunq.
apply/cfunP=> x.
case: (boolP (x \in G))=> InG; last first.
  rewrite (cfun0 _ (is_char_in_cfun _ Cf)) //.
  apply: (cfun0 _ (is_char_in_cfun _ F2))=> //.
rewrite cfunqE ?(@qfuncE G) //.
by apply: (subsetP (normal_norm HN)).
Qed.

Lemma qfunc_irr : forall (G N : {group gT}) (i : irr_class G),
 N <| G -> N \subset cker G i -> 
  exists j : irr_class (G/N), '{i^/N} = j :> cfun_type _ _.
Proof.
move=> G N i NN Cf.
pose sG := DecSocleType (regular_repr C (G/N)%G).
move: (Cf); rewrite char_rkerP=> Cf' //.
pose rG := quo_repr Cf' (normal_norm NN).
exists (IrrClass (irr_comp sG rG)).
apply/cfunP=> x.
have->: IrrClass (irr_comp sG rG) x =
       char (G/N)%g (irr_repr (irr_comp sG rG)) x.
  by [].
have F1: mx_irreducible rG.
  by apply/quo_mx_irr=> //; apply: socle_irr.
have F2: ([char C]^').-group (G / N)%G.
  by apply: sub_pgroup (pgroup_pi _)=> i' _; rewrite inE /= Cchar.
move/(rsim_irr_comp sG F2): F1.
move/char_rsimP; move/eqP<-.
by rewrite /rG !cfunE repr_quo_fact1.
Qed.

Lemma cfunq_irr : forall (G N : {group gT}) (i : irr_class (G/N)),
 N <| G ->  exists j : irr_class G, '{i^()} = j :> cfun_type _ _.
Proof.
move=> G N i NN.
pose sG := DecSocleType (regular_repr C G).
pose j := socle_of_irr_class i.
pose rG := coset_repr (irr_repr j) NN.
exists (IrrClass (irr_comp sG rG)).
apply/cfunP=> x.
have->: IrrClass (irr_comp sG rG) x = char G (irr_repr (irr_comp sG rG)) x.
  by [].
have F1: mx_irreducible rG.
  apply/(quo_mx_irr (coset_repr_rker (irr_repr j) NN) (normal_norm NN)).
  apply: (mx_rsim_irr (mx_rsim_sym (quo_coset_repr (irr_repr j) NN))).
  by apply: socle_irr.
move/(rsim_irr_comp sG (pGroupG G)): F1.
move/char_rsimP; move/eqP<-.
rewrite /rG !cfunE.
by rewrite  mulrA -natr_mul mulnb repr_quo_fact2.
Qed.

End Coset.

End Character.
