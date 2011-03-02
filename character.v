(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient finalg action.
Require Import zmodp commutator cyclic center pgroup sylow matrix mxalgebra.
Require Import mxpoly mxrepresentation vector algC.

Set Implicit Arguments.
Unset Strict Implicit.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(**************************************************************************)
(*                                                                        *)
(* This file contains the basic notions of character theory               *)
(*                                                                        *)
(*  cfun gT R : the type of functions from gT to R                        *)
(*                                                                        *)
(*  (f ^* )%CH  : the conjugate function                                  *)
(*                                                                        *)
(*  (f ^ g)%CH : the group conjugate function                             *)
(*                                                                        *)
(* is_conjugate G f g: f and g are G group conjugate                      *)
(*                                                                        *)
(*  'CL[R](G,A) : the vector space of class functions of G with support   *)
(*                in A                                                    *)
(*  'CL(G,A)    : the vector space of class functions of G with support   *)
(*                in A over algC                                          *)
(*  'CL(R)      : the vector space of class functions of G over R         *)
(*  'CL(G)      : the vector space of class functions of G over algC      *)
(*                                                                        *)
(*  irr G : irreducible character of G                                    *)
(*                                                                        *)
(*  is_irr G f :  predicates that tells if the function f is a character  *)
(*                                                                        *)
(*  get_irr G f : if is_irr G f is true returns the corresponding         *)
(*                 irreducible character                                  *)
(*                                                                        *)
(*  char_of_repr G rG : turn the representation rG into a character       *)
(*                                                                        *)
(*  is_char G f : predicates that tells if the function f is a character  *)
(*                                                                        *)
(*  get_char G f : if is_irr G f is true returns the corresponding        *)
(*                 character                                              *)
(*                                                                        *)
(*  '[f,g]_G : the inner product of f g such that irr G is                *)
(*                     an orthonormal basis of 'CL(G)                     *)
(*                                                                        *)
(*  cker G f : the kernel of G i.e g \in G such that f g = f 1            *)
(*                                                                        *)
(*   (f/N)%CH  :        if f is a character G, it returns the isomorphic  *)
(*                      character in G/N                                  *)
(*  (f^())%CH  : if f is a character G/N, returns the isomorphic          *)
(*                      character in G                                    *)
(*                                                                        *)
(* is_comp i f : the irreducible character i is a constituent of f        *)
(*                                                                        *)
(* 'Res[H] f: restrict the function to H, i.e f x = 0 for x \notin H      *)
(*                                                                        *)
(* 'Ind[G,H] f: the induced function from H to G                          *)
(*                                                                        *)
(* ccenter G f: the center i.e g \in G such that |f g| = f 1              *)
(*                                                                        *)
(* cfaithful G f: the class function f is faithfull, i.e its center       *)
(*                 is trivial                                             *)
(*                                                                        *)
(* inertia HnG i : when HnG is the proof of the H is normal in G, it      *)
(*                 the inertia group of elements of G for the irreducible *)
(*                 character H                                            *)
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

(* This should be put in mxrepresentation *)

Section MxR.

Variables (R : fieldType) (gT : finGroupType) (G : {group gT}).

Lemma mx_rsim_scalar : 
  forall m n 
   (rG1 : mx_representation R G m) (rG2 : mx_representation R G n) g c,
   g \in G -> mx_rsim rG1 rG2 -> rG1 g = c%:M -> rG2 g = c%:M.
Proof.
move=> m n rG1 rG2 g c InG HR.
move/mx_rsim_sym: (HR); case/mx_rsim_def=> B1 [B2 HH].
move/(_ _ InG)=> -> ->; rewrite scalar_mxC -mulmxA.
suff->: B1 *m B2 = 1%:M by rewrite mulmx1.
by move: B1 B2 HH; rewrite (mxrank_rsim HR); move=> *; exact: mulmx1C.
Qed.

Lemma add_mx_repr :
 forall m n 
  (rG1 : mx_representation R G m) (rG2 : mx_representation R G n),
  mx_repr G (fun g => block_mx (rG1 g) 0 0 (rG2 g)).
Proof.
move=> m n repr1 repr2; split=> [|x y Hx Hy].
  by rewrite !repr_mx1 -scalar_mx_block.
by rewrite mulmx_block !(mulmx0,mul0mx,addr0,add0r,repr_mxM).
Qed.

Definition add_repr m n
  (rG1 : mx_representation R G m) (rG2 : mx_representation R G n)
  := MxRepresentation (add_mx_repr rG1 rG2).

Lemma mx_repr0 : mx_repr G (fun _ : gT => 1%:M : 'M[R]_0).
Proof. by split=> // g h Hg Hx; rewrite mulmx1. Qed.

Definition repr0 :=  MxRepresentation mx_repr0.
 
Definition natrepr (m : nat) (rG : mx_representation R G m) := 
  fix iter (n : nat) : mx_representation R G (n * m) :=
    if n is n1.+1 then add_repr rG (iter n1) else repr0.

Variable (N : {group gT}) (n : nat) (rG : mx_representation R (G/N)%g n).
Hypothesis NN: N <| G.

Definition coset_mx of N <| G := rG \o (coset N).

Lemma coset_mx_repr : mx_repr G (coset_mx NN).
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
move=> M; case: (@cosetP _ _ M)=> g Hg ->.
by rewrite mul1mx mulmx1 /= /coset_mx /= coset_reprK//.
Qed.

End MxR.

(* Move to fingroup and should replace card_classes_abelian in action *)
Lemma card_classes_abelian : forall (gT : finGroupType) (G : {group gT}), 
  abelian G = (#|classes G| == #|G|).
Proof.
move=> gT G.
have F : reflect (forall i, i \in classes G -> #|i| = 1%N) (abelian G).
  apply(iffP idP)=> [HH i| HH].
    case/imsetP=> g InG ->; apply/eqP; apply/cards1P; exists g.
    by apply/cent_classP; move/subsetP: HH->.
  apply/subsetP=> g InG; apply/centP=> h InH.
  move/eqP: (HH _ (mem_classes InG)); case/cards1P=> l H.
  have: g \in g ^: G by exact: class_refl.
  have: g ^ h \in g ^: G by exact: memJ_class.
  rewrite H !inE; move/eqP=> H1; move/eqP=> H2.
  by rewrite /commute {2}H2 -H1 mulgA mulgV mul1g.
rewrite -sum_card_class; apply/idP/idP=>[|HH].
  by move/F=> HH; rewrite (eq_bigr (fun _ => 1%N)) // sum_nat_const muln1.
have F1: forall g, g \in G -> (0 < #|g ^: G|)%N.
  by move=> g InG; rewrite (cardD1 g) class_refl.
apply/F=> i; case/imsetP=> g InG ->; move: HH.
rewrite (eq_bigr (fun  C : {set gT}  => #|C|.-1 + 1))%N; last first.
  by move=> C; case/imsetP=> h InH->; rewrite addn1 prednK // F1.
rewrite big_split sum_nat_const //= muln1 -{1}[#|_|]add0n eqn_addr.
rewrite eq_sym sum_nat_eq0.
move/forallP; move/(_ (g ^: G)); move/implyP; move/(_ (mem_classes InG)).
by case: #|_| (F1 _ InG)=> // [] [].
Qed.

Lemma class_inv: forall (gT : finGroupType) (G : {group gT}) g,
  (g ^: G)^-1%g = g^-1 ^: G.
Proof.
move=> gT G g; apply/setP=> h; rewrite inE.
apply/imsetP/imsetP; case=> l LiG H.
  by exists l=> //; rewrite conjVg -H invgK.
by exists l=> //; rewrite H conjVg invgK.
Qed.

Section AlgC.

Variable (gT : finGroupType).

Axiom groupC : group_closure_field algC gT.

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

(****************************************************************************)
(*  trying to do something about characters                                 *)
(****************************************************************************)

Delimit Scope character_scope with CH.

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

Variable (gT: finGroupType) (R : fieldType) (G: {group gT}).

Inductive cfun : predArgType := ClassFun of {ffun gT -> R}.

Definition finfun_of_cfun A := let: ClassFun f := A in f.
Definition fun_of_cfun f x := finfun_of_cfun f x.
Coercion fun_of_cfun : cfun >-> Funclass.

Lemma finfun_of_cfunE: forall f x, finfun_of_cfun f x  = f x.
by [].
Qed.

Definition cfun_of_fun f := locked ClassFun [ffun i => f i].

Lemma cfunE : forall f, cfun_of_fun f =1 f.
Proof. by unlock cfun_of_fun fun_of_cfun => f i; rewrite /= ffunE. Qed.

Lemma cfunP : forall (f1 f2 : cfun), f1 =1 f2 <-> f1 = f2.
Proof.
move=> [f1] [f2]; split=> [/= eqf1f2 | -> //].
congr ClassFun; apply/ffunP=> i; exact: eqf1f2.
Qed.

Canonical Structure cfun_subType :=
  Eval hnf in [newType for finfun_of_cfun by cfun_rect].
Definition cfun_eqMixin := Eval hnf in [eqMixin of cfun by <:].
Canonical Structure cfun_eqType := 
  Eval hnf in EqType cfun cfun_eqMixin.
Definition cfun_choiceMixin := [choiceMixin of cfun by <:].
Canonical Structure cfun_choiceType :=
  Eval hnf in ChoiceType cfun cfun_choiceMixin.

Definition cfun_zero := cfun_of_fun (fun _ => 0).
Definition cfun_one := cfun_of_fun (fun _ => 1).
Definition cfun_opp (f : cfun) := cfun_of_fun (fun x => - f x).
Definition cfun_add (f g : cfun) := cfun_of_fun (fun x => f x + g x). 
Definition cfun_mul (f g : cfun) := cfun_of_fun (fun x => f x * g x). 

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
Canonical Structure cfun_ringType := Eval hnf in RingType cfun cfun_ringMixin.
Canonical Structure cfun_comRingType := Eval hnf in ComRingType cfun cfun_mulC.

Definition cfun_scale k (f : cfun) :=  cfun_of_fun (fun x => k * f x).

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
  Eval hnf in LmodType R cfun cfun_lmodMixin.

Lemma sum_cfunE:  
  forall I (r : seq I) (P : pred I) (F : I -> cfun),
  \big[+%R/0]_(i <- r | P i) F i = 
     cfun_of_fun (fun x => \big[+%R/0]_(i <- r | P i) (F i x)).
Proof.
move=> i r P F1; elim: r=> [|y r Hrec].
  by rewrite !big_nil; apply/cfunP=> j; rewrite !cfunE big_nil.
by rewrite big_cons Hrec; case F2: (P _); apply/cfunP=> x;
   rewrite !cfunE big_cons F2.
Qed.

Lemma cfunMn : forall (f : cfun) n x, (f *+ n) x = f x *+ n.
Proof.
by move=> f n x; elim: n => [|n IHn]; rewrite ?mulrS !cfunE -?IHn //. 
Qed.

Definition has_support (f : cfun) (A : {set gT}) :=
  forallb x: gT, (f x != 0) ==> (x \in A).

Definition base_cfun (G A : {set gT}) : seq cfun :=
  filter
    (has_support^~A)
    (map (fun i : 'I_#|classes G|  => 
        cfun_of_fun (fun x => (x \in (enum_val i))%:R))
      (enum 'I_#|classes G|)).

Lemma base_cfun_subset : forall (A : {set gT}),
 G \subset A -> 
 base_cfun G A = (map (fun i : 'I_#|classes G|  => 
                   cfun_of_fun (fun x => (x \in (enum_val i))%:R))
                   (enum 'I_#|classes G|)).
Proof.
move=> A GsA; apply/all_filterP.
apply/allP=> /= f; case/mapP=> i Hi ->.
apply/forall_inP=> x; rewrite cfunE.
case: (boolP (_ \in _))=> Hxi HH; last by case/eqP: HH.
apply: (subsetP GsA).
suff: (enum_val i) \subset G by move/subsetP; apply.
case/imsetP: (enum_valP i)=> g GiG ->.
by apply: class_subG.
Qed.
 
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

Definition class_fun G  A := span (base_cfun G A).

Local Notation "'CL( G , A )" := (class_fun G A).
Local Notation "'CL( G )" := (class_fun G G).

Lemma cfun_memfP : forall (A : {set gT}) (f : cfun),
  reflect 
    (   (forall x, x \notin (A :&: G) -> f x = 0) 
     /\ 
        (forall x y, x \in G -> y \in G -> f (x ^ y) = f x)
    )
    (f \in 'CL(G, A)).
Proof.
move=> A f; pose bGA := base_cfun G A.
apply: (iffP idP)=> [|[Hg Hc]].
  move/coord_span->; split=> [x XniAG|x y XiG YiG].
    rewrite sum_cfunE cfunE; apply: big1=> i _; rewrite !cfunE.
    have: bGA`_i \in bGA by apply: mem_nth.
    rewrite mem_filter; case/andP=> Hs.
    move: XniAG; rewrite inE negb_andb; case/orP=> [XniA|XniG].
      move/forallP: Hs; move/(_ x).
      by rewrite (negPf XniA) implybF negbK; move/eqP->; rewrite mulr0.
    case/mapP=> j Hj ->; rewrite !cfunE.
    have [y Gy ->] := imsetP (enum_valP j).
    move/subsetP: (class_subG Gy (subxx _)); move/(_ x); move/contra.
    by move/(_ XniG); case: (_ \in _)=> //; rewrite mulr0.
  apply/eqP; rewrite -subr_eq0; apply/eqP.
  rewrite !sum_cfunE !cfunE -sumr_sub; apply: big1=> i _.
  set u := coord _ _ _; rewrite !cfunE.
  have: bGA`_i \in bGA by apply: mem_nth.
  rewrite mem_filter; case/andP=> Hs.
  case/mapP=> j Hj ->; rewrite !cfunE.
  have [z Gz ->] := imsetP (enum_valP j).
  by rewrite (class_transl _ (memJ_class _ _)) // subrr.
suff<-: \sum_(C \in (classes G)) 
           (f (repr C)) *: cfun_of_fun (fun x => (x \in C)%:R) = f.
  apply: memv_sum=> i Hi.
  case: (boolP (f (repr i) == 0))=> [|Hr].
    by move/eqP->; rewrite scale0r mem0v.
  apply: memvZl; apply: memv_span.
  rewrite mem_filter; apply/andP; split.
    apply/forall_inP=> x; rewrite cfunE.
    case: (boolP (x \in i))=> //= XiI HH //; last by case/eqP: HH.
    case: (boolP (x \in A))=> // XniA; case/eqP: Hr.
    case/imsetP: Hi XiI => g GiG ->; case/imsetP=> h HiG Hx.
    case: (repr_class G g)=> h1 H1iG ->.
    by rewrite Hc // -(Hc _ _ _ HiG) // -Hx Hg // inE (negPf XniA).
  by apply/mapP; exists (enum_rank_in (classes1 G) i);  
      [rewrite mem_enum | rewrite enum_rankK_in].
apply/cfunP=> g; rewrite sum_cfunE cfunE.
case GiG: (g \in G); last first.
  rewrite Hg ?(inE,GiG,andbF) //; apply: big1=> i Hi; rewrite !cfunE.
  have [x Gx ->] := imsetP Hi.
  case Hgx: (_ \in _); last by rewrite mulr0.
  move/subsetP: (class_subG Gx (subxx G)) GiG.
  by move/(_ g (idP Hgx))=> ->.
rewrite (bigD1 (g ^: G : set_of_finType _)) /=; last by apply/imsetP; exists g.
rewrite !cfunE big1.
  rewrite class_refl.
  case: (repr_class G g)=> x Hx ->; rewrite Hc // addr0; exact: mulr1.
move=> i; case/andP; case/imsetP=> y Hy -> Hz.
rewrite !cfunE; case E1: (_ \in _); last by rewrite mulr0.
by case/negP: Hz; rewrite eq_sym; apply/eqP; apply: class_transr.
Qed.

Lemma cfun_memP : forall (f : cfun),
  reflect 
    ((forall x, x \notin G -> f x = 0) /\
        (forall x y, x \in G -> y \in G -> f (x ^ y) = f x))
    (f \in 'CL(G)).
Proof. by move=> f; apply: (iffP (cfun_memfP G f)); rewrite setIid. Qed.

Lemma cfunS0 : forall A (f : cfun) x, f \in 'CL(G,A) -> x \notin A -> f x = 0.
Proof. 
move=> A f x; case/cfun_memfP=> HH _ XniA; apply: HH.
by rewrite inE (negPf XniA).
Qed.

Lemma cfun0 : forall (f : cfun) x, f \in 'CL(G) -> x \notin G -> f x = 0.
Proof. exact: cfunS0. Qed.

Lemma cfunJ : forall A (f : cfun) x y, 
   f \in 'CL(G,A) -> x \in G -> y \in G -> f (x ^ y) = f x.
Proof. by move=> A f x y; case/cfun_memfP=> _ HH; exact: HH. Qed.

Lemma cfun_sum : forall (F : gT -> R),
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

Lemma dim_cfun : \dim ('CL(G)) = #|classes G|.
Proof.
move: (cfun_free G); rewrite /free; move/eqP->.
by rewrite base_cfun_subset ?subxx // size_map -cardE card_ord.
Qed.

Definition cfun_conj (f : cfun) (g : gT) :=
  cfun_of_fun (fun h => f (h^(g^-1))).

Notation "f ^ g" := (cfun_conj f g) : character_scope.

Lemma cfun_conjE : forall f g h, (f ^ g)%CH h = f (h^(g^-1)).
Proof. by move=> f g h; rewrite cfunE. Qed.

(* Isaacs' 6.1.a *)
Lemma cfun_conj_in_cfun : forall f g,
  g \in G -> f \in 'CL(G) -> (f^g)%CH \in 'CL(G).
Proof.
move=> f g GiG CLf.
apply/cfun_memP; split=> [h HniG|h1 h2 H1iG H2iG].
  rewrite cfunE (cfun0 CLf) //; apply/negP=> HGiG; case/negP: HniG.
  by rewrite -(groupJr h (groupVr GiG)).
by rewrite !cfunE !(cfunJ CLf, groupV) // groupJ.
Qed.

(* Isaacs' 6.1.b *)
Lemma cfun_conjM : forall (f : cfun) (g h : gT),
  (f ^ (g * h) = (f ^ g) ^ h)%CH.
Proof. by move=> f g h; apply/cfunP=> k; rewrite !cfun_conjE invMg conjgM. Qed.

Definition is_conjugate (G : {set gT}) (f1 f2: cfun) :=
  existsb g : gT, (g \in G) && (f2 == (f1^g)%CH).

Lemma is_conjugateP : forall f1 f2,
  reflect (exists2 g : gT, g \in G & f2 = (f1^g)%CH) (is_conjugate G f1 f2).
Proof.
move=> f1 f2; apply: (iffP existsP); case=> g.
  by case/andP=> GiG; move/eqP=> He; exists g.
by move=> GiG ->; exists g; rewrite GiG eqxx.
Qed.

Lemma cfun_conj1 : forall f : cfun, (f^1)%CH = f.
Proof. by move=> f; apply/cfunP=> g; rewrite cfunE invg1 conjg1. Qed.

Lemma cfun_conj_val1 : forall (f : cfun) g, (f^g)%CH 1%g = f 1%g.
Proof. by move=> f g; rewrite cfunE conj1g. Qed.

Lemma is_conjugate_refl : reflexive (is_conjugate G).
Proof. 
move=> f; apply/is_conjugateP.
by exists 1%g; [exact: group1 | rewrite cfun_conj1].
Qed.

Lemma is_conjugate_sym : symmetric (is_conjugate G).
Proof.
by move=> f1 f2; apply/is_conjugateP/is_conjugateP; case=> g GiG ->; 
   exists (g^-1%g); rewrite ?groupV // -cfun_conjM mulgV cfun_conj1.
Qed.

Lemma is_conjugate_trans : transitive (is_conjugate G).
Proof.
move=> f1 f2 f3; case/is_conjugateP=> g GiG ->; case/is_conjugateP=> h HiG ->.
by apply/is_conjugateP; exists (g * h)%g; [exact: groupM | rewrite cfun_conjM].
Qed.

End ClassFun.

Notation "''CL[' R ] ( G , A ) " := (class_fun R G A).
Notation "''CL[' R ] ( G ) " := (class_fun R G G).
Notation "''CL(' G , A ) " := 
  (class_fun (GRing.ClosedField.fieldType algC) G A).
Notation "''CL(' G ) " := 
  (class_fun (GRing.ClosedField.fieldType algC) G G).
Notation "f ^ g" := (cfun_conj f g) : character_scope.

Definition cfun_conjC (gT: finGroupType) (f : cfun gT algC) :=
  cfun_of_fun (fun h => (f h)^*).

Notation "f ^*" := (cfun_conjC f) : character_scope.

Lemma cfun_conjCE : forall gT (f : cfun gT algC) g, (f^*)%CH g = (f g)^*.
Proof. by move=> gT f g; rewrite cfunE. Qed.

Lemma cfun_conjCK: forall gT (f : cfun gT algC), (f^*^*)%CH = f.
Proof. by move=> gT f; apply/cfunP=> g; rewrite !cfunE conjCK. Qed.

Lemma cfun_conj_conjC : forall gT (f : cfun gT algC) (g : gT),
  (f^g)^*%CH = (f^* ^ g)%CH.
Proof. by move=> gT f g; apply/cfunP=> h; rewrite !cfunE. Qed.

Section Char.

Variables (gT : finGroupType) (G : {group gT}).

Definition char_of_repr n (G : {set gT}) (f: gT -> 'M[algC]_n) := 
 cfun_of_fun (fun g : gT => ((g \in G)%:R * \tr (f g))).

Lemma char_of_repr1 : 
  forall n (rG : mx_representation algC G n), char_of_repr G rG 1%g = n%:R.
Proof. by move=> n rG; rewrite !cfunE group1 repr_mx1 mxtrace1 mul1r. Qed.

Lemma char_of_repr_sim : 
  forall n1 n2 (rG1: mx_representation algC G n1) 
               (rG2: mx_representation algC G n2),
  mx_rsim rG1 rG2 -> char_of_repr G rG1 = char_of_repr G rG2.
Proof.
move=> n1 n2 rG1 rG2; case/mx_rsim_def=> M1 [M2] HM1M2 Hx.
apply/cfunP=> x; rewrite !cfunE; case H: (_ \in _); last by rewrite !mul0r.
by rewrite Hx // mxtrace_mulC mulmxA HM1M2 mul1mx.
Qed.

Lemma char_of_repr_in_cfun : forall n (rG :  mx_representation algC G n), 
  char_of_repr G rG \in 'CL(G).
Proof.
move=> n rG; apply/cfun_memP.
split=> [x|x y Hx Hy]; rewrite !cfunE.
  by case: (x \in G)=> //; rewrite mul0r.
by rewrite groupJ // Hx !mul1r !(repr_mxM,repr_mxV,groupM,groupV) //
           mxtrace_mulC mulmxK // repr_mx_unit.
Qed.

Lemma char_of_repr_morph : forall m n
  (rG1 : mx_representation algC G m) (rG2 :  mx_representation algC G n),
  char_of_repr G (add_repr rG1 rG2) = 
    char_of_repr G rG1 + char_of_repr G rG2.
Proof.
move=> m n rG1 rG2.
by apply/cfunP=> g; rewrite !cfunE -mulr_addr mxtrace_block.
Qed.

Lemma char_of_repr0 : char_of_repr G (repr0 algC G) = 0.
Proof.
by apply/cfunP=> g; rewrite !cfunE mxtrace1 mulr0.
Qed.

Lemma char_of_repr_nat : forall m n (rG : mx_representation algC G m), 
  char_of_repr G (natrepr rG n) = char_of_repr G rG *+n.
Proof.
move=> m n rG; elim: n=> [|n IH].
  by apply/cfunP=> g; rewrite !cfunE mxtrace1 mulr0.
by rewrite /= char_of_repr_morph IH mulrS.
Qed.

(* !!!!!!!!!!! FOR THE MOMENT AN AXIOM !!!!!!!!!!!!!!!!!!! *)
Lemma char_of_repr_rsimP : forall m n (rG1 : mx_representation algC G m)
                                      (rG2 : mx_representation algC G n),
   reflect (mx_rsim rG1 rG2) (char_of_repr G rG1 == char_of_repr G rG2).
Proof.
move=> m n rG1 rG2; apply: (iffP eqP)=> HH; last first.
  apply/cfunP=> g; rewrite !cfunE.
  case E1: (g \in G); last by rewrite !mul0r.
  by rewrite !mul1r; apply: mxtrace_rsim.
admit.
Qed.
  
Definition reg_cfun := char_of_repr G (regular_repr algC G).

Lemma reg_cfunE : forall (g : gT),
  reg_cfun g = if (g == 1%g) then #|G|%:R else 0.
Proof.
move=> g; rewrite cfunE.
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

Definition xchar (chi: cfun gT algC) (u: 'rV[algC]_#|G|) : algC^o := 
  \sum_(i < #|G|) u 0 i * chi (enum_val i).

(* In order to add a second canonical structure on xchar *)
Definition xcharb x := (@xchar)^~ x.

Lemma xcharbE : forall u (x : 'rV_#|G|), xchar u x = xcharb x u.
Proof. by []. Qed.

Lemma xcharb_is_linear : forall x, linear (xcharb x).
Proof.
move=> i k m n.
rewrite /xchar scaler_sumr -big_split /=; apply: eq_bigr=> l _.
by rewrite !cfunE mulr_addr scaler_mulr.
Qed.

Canonical Structure xcharb_linear x := Linear (xcharb_is_linear x).

Lemma xchar_trace : forall u n (rG: mx_representation algC G n),
  xchar (char_of_repr G rG) u = 
  \tr (gring_op rG (gring_mx (regular_repr algC G) u)).
Proof.
move=> u n rG.
rewrite /xchar /gring_op /= gring_mxK.
apply: (@etrans _ _
   (\sum_(i0 < #|G|) \tr(u 0 i0 *: rG (enum_val i0)))).
  by apply: eq_bigr=> j _; rewrite cfunE enum_valP mul1r mxtraceZ.
rewrite -raddf_sum; congr (\tr _).
apply/matrixP=> i1 j1; rewrite !mxE summxE; apply eq_bigr=> k1 _.
by rewrite !(mxvecE,mxE).
Qed.

End Char.

Section IrrClass.

Variable (gT : finGroupType) (G : {group gT}).

Let sG := DecSocleType (regular_repr algC G).

Inductive irr : predArgType := IrrClass of sG.
Definition socle_of_irr (A : irr) := let: IrrClass i := A in i.

Canonical Structure irr_subType :=
  Eval hnf in [newType for socle_of_irr by irr_rect].
Definition irr_eqMixin := Eval hnf in [eqMixin of irr by <:].
Canonical Structure irr_eqType := 
  Eval hnf in EqType irr irr_eqMixin.
Definition irr_choiceMixin := [choiceMixin of irr by <:].
Canonical Structure irr_choiceType :=
  Eval hnf in ChoiceType irr irr_choiceMixin.
Definition irr_countMixin := [countMixin of irr by <:].
Canonical Structure irr_countType :=
  Eval hnf in CountType irr irr_countMixin.
Canonical Structure irr_subCountType :=
  Eval hnf in [subCountType of irr].
Definition irr_finMixin := [finMixin of irr by <:].
Canonical Structure irr_finType :=
  Eval hnf in FinType irr irr_finMixin.
Canonical Structure irr_subFinType :=
  Eval hnf in [subFinType of irr].

Coercion cfun_of_irr chi := 
  char_of_repr G (irr_repr (@socle_of_irr chi)).

Lemma cfun_of_irr_inj : injective cfun_of_irr.
Proof.
move=> i j; move/eqP; move/char_of_repr_rsimP.
move/(irr_comp_rsim sG (pGroupG G)).
rewrite !irr_reprK //; try exact: pGroupG.
by case: i; case: j=>  u v /= ->.
Qed.

Definition irr1 := IrrClass (principal_comp sG).

Lemma irr1E : forall g, irr1 g = (g \in G)%:R.
Proof.
move=> g; case: (boolP (_ \in _))=> Hg; last first.
  by rewrite (cfun0 (char_of_repr_in_cfun _)).
by rewrite cfunE Hg mul1r irr1_repr // mxtrace1 degree_irr1.
Qed.

Lemma card_irr : #|irr| = #|classes G|.
Proof.
rewrite -(card_irr sG) ?pGroupG //; last exact: groupC.
by rewrite card_sub; apply: eq_card=> i; rewrite !inE.
Qed.

Lemma irr_val1 : forall i : irr, 
  i 1%g = (irr_degree (socle_of_irr i))%:R.
Proof.
by move=> i; rewrite cfunE group1 mul1r repr_mx1 mxtrace1.
Qed.

Lemma irr1_neq0 : forall i : irr, i 1%g != 0.
Proof.
move=> i; rewrite irr_val1 -neq0N_neqC.
by case: irr_degree (irr_degree_gt0 (socle_of_irr i)).
Qed.

Lemma irr_sum_square : \sum_(i : irr) (i 1%g) ^+ 2 = #|G|%:R.
Proof.
rewrite -(sum_irr_degree sG) ?pGroupG //; last exact: groupC.
rewrite (big_morph _ (@natr_add _) (erefl _)).
rewrite (reindex socle_of_irr); last by exists IrrClass=> [] [i].
by apply: eq_bigr=> i _; rewrite irr_val1 natr_exp.
Qed.

Lemma irr_in_cfun : forall i : irr, (i : cfun _ _) \in 'CL(G).
Proof. 
by move=> i; exact: (char_of_repr_in_cfun ((irr_repr (@socle_of_irr i)))).
Qed.

Definition is_irr f := existsb i : irr, f == i :> cfun _ _.

Lemma is_irr_irr: forall i : irr, is_irr i.
Proof. by move=> i; apply/existsP; exists i. Qed.

Lemma is_irrP : forall f, 
  reflect (exists i : irr, f = i :> cfun _ _) (is_irr f).
Proof.
move=> f; apply: (iffP (@existsP _ _))=>[[i Hi]|[i ->]]; exists i=> //.
by apply/eqP.
Qed.

Definition get_irr f :=
  odflt irr1 [pick i | (i : irr) == f :> cfun _ _].

Lemma get_irrE : forall f, is_irr f -> get_irr f = f :> cfun _ _ .
Proof.
move=> f; case/is_irrP=> i Hi; rewrite /get_irr; case: pickP=> /=.
  by move=> j; move/eqP.
by move/(_ i); rewrite Hi eqxx.
Qed.
 
Lemma reg_cfun_sum : 
  reg_cfun G = \sum_(i : irr) i (1%g) *: (i : cfun _ _).
Proof.
apply/cfunP=> g; rewrite !cfunE.
case Ig: (_ \in _); last first.
  rewrite mul0r sum_cfunE cfunE big1 // => i _.
  by rewrite cfunE [_ g](cfun0 (char_of_repr_in_cfun _)) (mulr0,Ig).
rewrite mul1r (mxtrace_regular sG (pGroupG _)) //; last by exact: groupC.
rewrite sum_cfunE cfunE.
rewrite {1}(reindex socle_of_irr) /=; last by exists IrrClass=> [] [].
by apply eq_bigr=> i _; rewrite irr_val1 !cfunE Ig mul1r // GRing.mulr_natl.
Qed.

Lemma xchar_is_linear : forall i : irr, linear (@xchar _ G i).
Proof.
move=> i k m n.
rewrite scaler_sumr -big_split /=; apply: eq_bigr=> l _.
by rewrite scaler_mull -mulr_addl !mxE.
Qed.

Canonical Structure xchar_linear (i : irr) := 
  Linear (xchar_is_linear i).

Local Notation "'E_" := 
  ((@Wedderburn_id _ _ _ _) \o socle_of_irr) (at level 0).
Local Notation "'R_":= 
  ((@Wedderburn_subring _ _ _ _) \o socle_of_irr) (at level 0).

Lemma xchar_subring : forall (i j : irr) A, 
  i != j -> (A \in 'R_j)%MS -> xchar i (gring_row A) = 0.
Proof.
move=> i j A Hi HA.
pose s i := socle_of_irr i.
rewrite xchar_trace -(mxtrace0 _ (irr_degree (s i))); congr (\tr _).
have F1: s j != irr_comp sG (irr_repr (s i)).
  rewrite irr_reprK ?pGroupG //.
  apply/eqP=> HH; case/eqP: Hi; apply/val_eqP.
  by rewrite eq_sym; apply/eqP.
apply: irr_comp'_op0 F1 _; first by exact: pGroupG.
  by apply: socle_irr.
rewrite gring_rowK // -(Wedderburn_sum sG (pGroupG _)).
apply/memmx_sumsP; exists (fun i => (i==s j)%:R *: A).
  rewrite (bigD1 (s j)) //= eqxx scale1r big1 ?addr0 // => k.
  by case: (k == s j); rewrite // scale0r.
by move=> k; case E1: (k == s j); 
  [move/eqP: E1->; rewrite scale1r | rewrite scale0r mem0mx].
Qed.

Lemma xchar_id : forall i j : irr,
  xchar i (gring_row ('E_ j)) = if i == j then i 1%g else 0.
Proof.
move=> i j; case: eqP=> [->|Hi]; last first.
  by apply: xchar_subring (Wedderburn_id_mem _); apply/eqP.
rewrite cfunE group1 mul1r -gring_opG //.
have R1 := (envelop_mx_id (regular_repr algC G) (group1 G)).
rewrite -[regular_repr algC G 1%g]gring_rowK // -xchar_trace.
rewrite -[regular_repr _ _ _]mul1mx -(Wedderburn_sum_id sG (pGroupG _)).
have->: regular_repr algC G 1%g = 1%:M.
  by apply/matrixP=> i1 j1; rewrite !mxE !eqxx mulg1 gring_valK eq_sym.
pose s i := socle_of_irr i.
rewrite mulmx1 !linear_sum /= (bigD1 (s j)) //= big1; first by rewrite addr0.
move=> k; rewrite eq_sym => Hij.
have F1: j != IrrClass k by apply/eqP; move/val_eqP=> HH; case/negP: Hij.
exact: (xchar_subring F1 (Wedderburn_id_mem k)).
Qed.

Lemma irr_e_mul : forall (i : irr) A, (A \in group_ring algC G)%MS ->
 xchar i (gring_row ('E_ i *m A)) = xchar i (gring_row A).
Proof.
move=> i A HA.
rewrite -{2}[A]mul1mx -(Wedderburn_sum_id sG); last exact: pGroupG.
rewrite mulmx_suml !linear_sum (bigD1 (socle_of_irr i)) //=.
rewrite big1 ?addr0 // => j; rewrite eq_sym => Hij.
have F1: i != IrrClass j by apply/eqP; move/val_eqP=> HH; case/negP: Hij.
apply: (xchar_subring F1).
case/andP: (Wedderburn_ideal j)=> _ Hj.
apply: submx_trans Hj=> //.
apply: mem_mulsmx=> //.
exact: Wedderburn_id_mem.
Qed.

Lemma xchar_singleton : forall n g (rG : mx_representation algC G n),  
  g \in G -> 
    xchar (char_of_repr G rG) (gring_row (regular_repr algC G g)) = 
    char_of_repr G rG g.
Proof.
move=> n g rG Hg.
  rewrite /xchar (bigD1 (enum_rank_in (group1 G) g)) // big1 ?addr0.
  by rewrite enum_rankK_in // !mxE gring_indexK // mul1g !eqxx mul1r //= addr0.
move=> i; rewrite !mxE enum_rankK_in // mul1g /gring_index.
by case: (i == _)=> //; rewrite mul0r.
Qed.

(* This corresponds to Isaacs' Th. 2.12 *)
Lemma gring_row_e : forall i: irr, 
  gring_row ('E_ i) = \row_j (#|G|%:R^-1 * i 1%g * i ((enum_val j)^-1)%g).
Proof.
move=> i; apply/rowP=> j.
set j1 := ((enum_val j)^-1)%g.
have Inj1: ((enum_val j)^-1 \in G)%g by rewrite groupV enum_valP.
pose rj := regular_repr algC G j1.
have: xchar (reg_cfun G) (gring_row ('E_ i *m rj)) = 
        #|G|%:R * gring_row ('E_ i) 0 j.
  rewrite /xchar (bigD1 (gring_index G 1%g)) //= big1; last first.
    move=> k Hk; rewrite reg_cfunE.
    case: eqP; last by rewrite mulr0.
    by move=> Hk'; case/negP: Hk; rewrite -Hk' gring_valK.
  rewrite addr0 enum_rankK_in // gring_row_mul.
  rewrite reg_cfunE // eqxx mulrC; congr (_ * _).
  (* This takes ages 
  rewrite {1}mxE {1}(bigD1 j) //= {1}big1.
  *)
  rewrite {1}mxE {1}(@bigD1 _ _ (GRing.add_comoid algC) _ j) //= big1.
    by rewrite !mxE mulgV !eqxx mulr1 addr0.
  move=> k Hk.
  rewrite !mxE eqxx; case: eqP; last by rewrite mulr0.
  move=> Hi; case/negP: Hk.
  apply/eqP; apply: enum_val_inj; apply/eqP; rewrite eq_mulgV1.
  rewrite eq_sym; apply/eqP.
  apply: (can_in_inj (@gring_indexK _ G))=> //.
  by rewrite !(groupM,enum_valP).
rewrite reg_cfun_sum xcharbE linear_sum /=.
rewrite (bigD1 i) //= big1 ?addr0; last first.
  move=> k Hki.
  rewrite linearZ /= -xcharbE.
  rewrite (xchar_subring Hki) //; first by rewrite scaler0.
  case/andP: (Wedderburn_ideal (socle_of_irr i))=> _ Hi.
  apply: submx_trans Hi; apply: mem_mulsmx; first by exact: Wedderburn_id_mem.
  by apply: envelop_mx_id; rewrite groupV enum_valP.
rewrite linearZ /= -xcharbE.
rewrite irr_e_mul; last first.
  by apply: envelop_mx_id; rewrite groupV enum_valP.
rewrite !mxE xchar_singleton // /GRing.scale /= -mulrA => ->.
by rewrite !mulrA mulVf ?mul1r // neq0GC.
Qed.

Definition to_socle n (rG : mx_representation algC G n) (j: DecSocleType rG) := 
  irr_comp sG (socle_repr j).

Lemma to_socle_inj : forall n (rG : mx_representation algC G n),
  injective (@to_socle n rG).
Proof.
move=> n rG x y Hxy; apply/eqP; apply/socle_rsimP.
apply: (mx_rsim_trans (rsim_irr_comp sG _ (socle_irr _))).
  by exact: pGroupG.
apply: mx_rsim_sym; move: Hxy; rewrite /to_socle=>->.
by apply: (rsim_irr_comp sG _ (socle_irr _)); exact: pGroupG.
Qed.

Definition irr_coef n (rG : mx_representation algC G n) i :=
let i :=  socle_of_irr i in
oapp (fun i => socle_mult i) 0%N [pick j | i == to_socle (j: DecSocleType rG)].

End IrrClass.

 
Section VectorSpace.

Variable (gT : finGroupType) (G : {group gT}).

Definition base_irr := map (@cfun_of_irr gT G) (enum (irr G)).

Local Notation "'E_" := 
  ((@Wedderburn_id _ _ _ _) \o (@socle_of_irr _ G)) (at level 0).
Local Notation "'R_":= 
  ((@Wedderburn_subring _ _ _ _) \o (@socle_of_irr _ G)) (at level 0).
  
Lemma free_base_irr : free base_irr.
Proof.
apply/freeP=> s; set ss := \sum_(i<_) _ => Hs j.
have Hj: (j <  #|irr G|)%nat by case: j; rewrite size_map -cardE.
pose j' := enum_val (Ordinal Hj).
suff: xchar ss (gring_row ('E_ j')) = s j * j' 1%g.
  rewrite /xchar big1 //.
    move/eqP; rewrite eq_sym mulf_eq0; case/orP; first by move/eqP.
    rewrite irr_val1 -(eqN_eqC _ 0)=> He.
    by move: (irr_degree_gt0 (socle_of_irr j')); rewrite (eqP He).
  by move=> i _; rewrite Hs cfunE mulr0.
rewrite xcharbE linear_sum; rewrite (bigD1 j) //= big1.
  rewrite  addr0 (nth_map (irr1 G)) //; last by rewrite -cardE.
  rewrite linearZ /= -xcharbE.
  suff->: (nth (irr1 G) (enum (irr G)) j) = j'
    by rewrite  xchar_id eqxx.
  by move: (nth_enum_rank (irr1 G) j'); rewrite enum_valK.
move=> i Hij.
have Hi: (i <  #|irr G|)%nat.
  by case: {Hij}i; rewrite size_map -cardE.
pose i' := enum_val (Ordinal Hi).
rewrite  (nth_map (irr1 G)) //; last by rewrite -cardE.
rewrite linearZ /= -xcharbE.
have->: (nth (irr1 G) (enum (irr G)) i) = i'.
  by move: (nth_enum_rank (irr1 G) i'); rewrite enum_valK.
rewrite  xchar_id; case: eqP; last by rewrite scaler0.
move/eqP=> HH; case/negP: Hij.
by move: HH; rewrite (bij_eq (enum_val_bij (irr_finType G))).
Qed.

Lemma base_irr_basis : is_basis 'CL(G) base_irr.
Proof.
rewrite /is_basis free_base_irr andbT /is_span -dimv_leqif_eq.
  rewrite dim_cfun.
  move: free_base_irr; rewrite /free; move/eqP->.
  by rewrite size_map -cardE card_irr.
rewrite -span_subsetl; apply/allP=> i; case/mapP=> j _ ->.
apply: char_of_repr_in_cfun.
Qed.

Lemma sg2bi_ord : forall (i : irr G), 
  (enum_rank i < size base_irr)%N.
Proof. by move=> i; rewrite size_map -cardE. Qed.

Definition sg2bi (i : irr G) := Ordinal (sg2bi_ord i).

Lemma bi2sg_ord : 
  forall (i : 'I_(size base_irr)), (i < #|irr G|)%N.
Proof. by case=> i; rewrite size_map -cardE. Qed.

Definition bi2sg (i : 'I_(size base_irr)) :=
  enum_val (Ordinal (bi2sg_ord i)).

Lemma bi2sgK : cancel bi2sg sg2bi.
Proof. by case=> i Hi; apply/val_eqP; rewrite /= enum_valK. Qed.

Lemma sg2biK : cancel sg2bi bi2sg.
Proof. 
by move=> i; rewrite -{2}(enum_rankK i); congr enum_val; apply/val_eqP.
Qed.

Definition ncoord (i: irr G) c : algC^o := coord base_irr c (sg2bi i).

Lemma ncoord_sum : forall x : cfun gT algC, x \in 'CL(G) -> 
  x = \sum_(i : irr G) ncoord i x *: (i : cfun _ _).
Proof.
move=> x Hx.
have F1:  {on [pred i | xpredT i], bijective bi2sg}.
  by apply: onW_bij; exists sg2bi; [apply: bi2sgK | apply: sg2biK].
rewrite (reindex _ F1) /=.
have F2: x \in span base_irr.
  move: (is_basis_span base_irr_basis).
  by rewrite /is_span; move/eqP->.
rewrite {1}(coord_span F2); apply: eq_bigr=> i _; congr (_ *: _).
  by rewrite /ncoord bi2sgK.
rewrite  (nth_map (irr1 G)).
  by rewrite /bi2sg (enum_val_nth (irr1 G)).
rewrite -cardE; apply: bi2sg_ord.
Qed.

Lemma ncoord_is_linear : forall i : irr G, linear (ncoord i).
Proof. by move=> i k c1 c2; rewrite /ncoord linearD linearZ !ffunE. Qed.

Canonical Structure ncoord_linear (i : irr G) :=
  Linear (ncoord_is_linear i).

Lemma ncoordE : forall (f : irr G -> algC)  (x : cfun _ _), 
  x \in 'CL(G) -> 
   x = \sum_i (f i) *: (i: cfun _ _) -> forall i, f i = ncoord i x.
Proof.
move=> f x Hin Hx i.
suff: (fun j => ncoord (bi2sg j) x -  f (bi2sg j)) =1 (fun _ => 0).
  by move/(_ (sg2bi i)); rewrite sg2biK; move/eqP; rewrite subr_eq0; move/eqP.
move/freeP: free_base_irr; apply.
have F1:  {on [pred i | xpredT i], bijective sg2bi}.
  by apply: onW_bij; exists bi2sg; [apply: sg2biK | apply: bi2sgK ].
rewrite (reindex _ F1) /=.
rewrite (eq_bigr (fun j => ncoord j x *: (j : cfun _ _) - 
                             f j *: (j : cfun _ _))).
  by rewrite sumr_sub -Hx -ncoord_sum // subrr.
by move=> j _; rewrite sg2biK scaler_subl // (nth_map (irr1 G)) -?cardE
                       // nth_enum_rank.
Qed.

Lemma ncoord0 : forall i : irr G, ncoord i 0 = 0.
Proof.
move=> i; apply: sym_equal.
apply: (@ncoordE (fun i => 0:algC) 0); first exact: mem0v.
by rewrite big1 // => j _; exact: scale0r.
Qed.

Lemma ncoord_irr : forall i j : irr G, ncoord j i = (i == j)%:R.
Proof.
move=> i j; apply: sym_equal; apply: (@ncoordE (fun j => (i == j)%:R)).
  by exact: char_of_repr_in_cfun.
rewrite (bigD1 i) // big1 /= ?(addr0,eqxx,scale1r) // => i1.
by rewrite eq_sym; case: (_ == _)=> //; rewrite scale0r.
Qed.

Lemma ncoord_repr : forall n (rG : mx_representation algC G n) (i: irr G),
  ncoord i (char_of_repr G rG) = (irr_coef rG i)%:R.
Proof.
move=> n rG i; apply: sym_equal.
pose sG':= DecSocleType rG.
apply (@ncoordE (fun i => (irr_coef rG i)%:R)).
  by exact: char_of_repr_in_cfun.
pose ts (i: sG') := (to_socle i).
have->: char_of_repr G rG = 
  \sum_i (IrrClass (ts i) : cfun _ _) *+ socle_mult i.
  apply/cfunP=> g; rewrite !(sum_cfunE,cfunE).
  case: (boolP (_ \in _))=> Hin; last first.
    rewrite mul0r big1 ?ffunE // => j _.
    by rewrite (cfun0 _ Hin) // memvMn // char_of_repr_in_cfun.
  have F1: (Socle sG' :=: 1%:M)%MS.
    by rewrite reducible_Socle1 //; apply: mx_Maschke; exact: pGroupG.
  rewrite mul1r -(mxtrace_submod1 (Socle_module sG') F1) // mxtrace_Socle=> //.
  apply: eq_bigr=> i1 _ /=.
  rewrite  cfunMn !cfunE Hin mul1r; congr (_ *+ _).
  apply: mxtrace_rsim=> //; apply: rsim_irr_comp=> //; first by exact: pGroupG. 
  by apply/submod_mx_irr; apply: socle_simple.
case  E1: (enum sG') => [| x s].
  have F1: forall (i: sG'), false.
    by move=> x; have: x \in enum sG'; [rewrite mem_enum | rewrite E1].
  rewrite !big1 //; last by move=> x; have:= F1 x.
  move=> j; rewrite /irr_coef; case: pickP; last by rewrite scale0r.
  by move=> x; have:= F1 x.
rewrite (reindex (@IrrClass _ G)) /=; last first.
  by exists (@socle_of_irr _ G)=> // [] [].
have->: 
  \sum_i
    (irr_coef rG (IrrClass i))%:R *: (IrrClass i : cfun _ _) = 
   \sum_ (i |  codom ts i) 
    (irr_coef rG (IrrClass i))%:R *: (IrrClass i : cfun _ _).
  apply: sym_equal; rewrite big_mkcond; apply: eq_bigr=> k _.
  rewrite /irr_coef; case: pickP; last by rewrite scale0r if_same.
  by move=> i1 /=; move/eqP->; rewrite codom_f.
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
rewrite scaler_nat /irr_coef; congr (_ *+ _).
case: pickP; last by move/(_ i1); rewrite eqxx.
by move=> i2; move/eqP; move/to_socle_inj<-.
Qed.

End VectorSpace.

Section Restrict.

Variable (gT : finGroupType).

Definition crestrict (G : {set gT}) (f : cfun gT algC) :=
    cfun_of_fun (fun g : gT => (g \in G)%:R * (f g)).

Local Notation "''Res[' G ]  f " := (crestrict G f) (at level 24).

Lemma crestrictE : forall (G : {set gT}) f, {in G, 'Res[G] f =1 f}.
Proof. by move=> G f g H; rewrite cfunE H mul1r. Qed.
 
Lemma cfun_subset : forall f (G H : {group gT}), 
  H \subset G -> f \in 'CL(G) -> 'Res[H] f \in 'CL(H).
Proof.
move=> f G H Hsub fC; apply/cfun_memP; split.
  by move=> g; rewrite cfunE; case: (_ \in _)=> //; rewrite mul0r.
move=> g h gIn hIn; rewrite !cfunE groupJ //.
by rewrite gIn (cfunJ fC) // (subsetP Hsub).
Qed.

End Restrict.

Notation "''Res[' G ]  f " := (crestrict G f) (at level 24).

Section IsChar.

Variable (gT : finGroupType) (G : {group gT}).

Definition is_char (f : cfun gT algC) :=
  all (fun i : irr G => isNatC (ncoord i f)) (enum (irr G)) &&
  (f \in 'CL[algC](G)).

Lemma is_charRP : forall f,
  reflect (exists n, exists rG : mx_representation algC G n, 
            char_of_repr G rG = f)
          (is_char f).
Proof.
move=> f; apply: (iffP andP); last first.
  case=> n [rG <-]; split; last exact: char_of_repr_in_cfun.
  by apply/allP=> chi _; rewrite ncoord_repr isNatC_nat.
case; move/allP=> Ha Hf.
pose n' (j : irr G) := getNatC (ncoord j f).
have->: f = \sum_(j : irr G) (n' j)%:R *: (j : cfun _ _).
  rewrite {1}(ncoord_sum Hf); apply: eq_bigr=> i _.
  congr (_ *: _); apply/eqP; rewrite -getNatCP; apply: Ha.
  by exact: mem_enum.
elim: {n'}(\sum_j (n' j))%N {-2}n' (leqnn (\sum_j (n' j)))=> [| N IH] n' HS.
  exists 0%N; exists (repr0 algC G).
  apply/cfunP=> i; rewrite sum_cfunE !cfunE mxtrace1 mulr0 big1 // => j Hj.
  by move: HS; rewrite (bigD1 j) //=; case: (n' j)=> //; rewrite scale0r cfunE.
case: (boolP (all (fun i => n' i == 0%N) (enum (irr G)))).
  move/allP=> HH.
  exists 0%N; exists (repr0 algC G).
  apply/cfunP=> i; rewrite sum_cfunE !cfunE mxtrace1 mulr0 big1 // => j Hj.
  by rewrite (eqP (HH _ (mem_enum _ j))) scale0r cfunE.
case/allPn=> k kIn Hk.
pose n'' j := if (j == k) then (n' j).-1 else n' j.
have F1: (\sum_j (n' j) = 1 + \sum_j n'' j)%N.
  rewrite (bigD1 k) //[(\sum_j n'' j)%N](bigD1 k) //.
  rewrite addnA /n'' eqxx add1n prednK; last by case: (n' k) Hk.
  by congr (_ + _)%N; apply: eq_bigr=> i; case: (i == k).
have F2: \sum_j (n' j)%:R *: (j : cfun _ _)  = 
             (k : cfun _ _) + \sum_j (n'' j)%:R *: (j : cfun _ _).
  rewrite (bigD1 k) //[(\sum_j (n'' j)%:R *: _)](bigD1 k) // addrA; congr (_ + _).
    rewrite /n'' eqxx -{2}[(k: cfun _ _)]scale1r -scaler_addl -(natr_add _ 1%N).
    by rewrite add1n prednK //; case: (n' k) Hk.
  by apply: eq_bigr=> i; rewrite /n''; case: (i == k).
case: (IH n''); first by  rewrite -ltnS -add1n -F1.
intros n [rG HrG].
pose i := socle_of_irr k.
exists ((irr_degree i) + n)%N; exists (add_repr (irr_repr i) rG).
by rewrite char_of_repr_morph HrG F2.
Qed.

Lemma is_char_char_of_repr : forall n (rG : mx_representation algC G n),
  is_char (char_of_repr G rG).
Proof. by move=> n rG; apply/is_charRP; exists n; exists rG. Qed.

Lemma is_char_irr : forall i : irr G, is_char i.
Proof. 
move=> i; apply/is_charRP; pose i' := socle_of_irr i.
by exists (irr_degree i'); exists (irr_repr i').
Qed.

Lemma is_char_isNatC_ncoord : forall (i : irr G) (f : cfun _ _),
 is_char f -> isNatC (ncoord i f).
Proof.
move=> i f; case/is_charRP=> n [rG <-].
by rewrite ncoord_repr isNatC_nat.
Qed.

Lemma is_char0 : is_char 0.
Proof. by rewrite -(char_of_repr0 G) is_char_char_of_repr. Qed.

Lemma is_char_in_cfun : forall f,  is_char f -> f \in 'CL(G).
Proof. 
by move=> f; case/is_charRP=> n [rG <-]; apply: char_of_repr_in_cfun.
Qed.

Lemma is_char_add : forall f1 f2, 
  is_char f1 -> is_char f2 -> is_char (f1 + f2).
Proof.
move=> f1 f2; case/is_charRP=> m [rG1 HrG1]; case/is_charRP=> n [rG2 HrG2].
apply/is_charRP; exists (m + n)%N; exists (add_repr rG1 rG2).
by rewrite char_of_repr_morph HrG1 HrG2.
Qed.

Lemma is_char_scal : forall f n, is_char f -> is_char (f *+ n).
Proof.
move=> f n Hf; elim: n=> [|n Hn]; first by rewrite mulr0n is_char0.
by rewrite mulrS is_char_add.
Qed.

Lemma is_char_cb : forall (P: _ -> bool) n,
 is_char (\sum_(i : irr G | P i) (n i)%:R *: (i : cfun _ _)).
Proof.
move=> P n.
elim: {n}(\sum_(i | P i) (n i))%N {-2}n (leqnn (\sum_(i | P i) (n i)))=>
       [|N IH] n.
  move=> Hn; rewrite big1 ?is_char0 //.
  move=> i Pi; move: Hn; rewrite (bigD1 i) //.
  by case: (n i)=> //; rewrite scale0r.
case: (boolP (all (fun i => n i == 0%N) (filter P (enum (irr G))))).
  move/allP=> Hi Hn.
  rewrite big1  ?is_char0 //.
  move=> i Pi; move: (Hi i); rewrite mem_filter Pi mem_enum.
  by move/(_ is_true_true); move/eqP->; rewrite scale0r.
case/allPn=> i; rewrite mem_filter mem_enum; case/andP=> H1i H2i H3i HH.
pose n' (j : irr G) := if (j == i) then (n j).-1 else n j.
have F1: (\sum_(i | P i) (n i) = (\sum_(i | P i) (n' i)).+1)%N.
  rewrite (bigD1 i) // [(\sum_(i | P i) n' i)%N](bigD1 i) //= -add1n addnA.
  congr (_ + _)%N; first by rewrite /n' eqxx; case: (n i) H3i.
  by apply: eq_bigr=> j; case/andP=> H1j H2j; rewrite /n' (negPf H2j).
have F2: \sum_(i | P i) (n i)%:R *: (i : cfun _ _)  = 
           (i : cfun _ _) + \sum_(i | P i) (n' i)%:R *: (i : cfun _ _).
  rewrite (bigD1 i) //= [\sum_(i | P i) (n' i)%:R *: _](bigD1 i) //=.
  rewrite addrA; congr (_ + _).
    rewrite /n' eqxx; case: (n i) H3i=> // m' _.
    by rewrite -{1}add1n natr_add scaler_addl scale1r.
  by apply: eq_bigr=> j; case/andP=> H1j H2j; rewrite /n' (negPf H2j).
rewrite F2; apply is_char_add; first exact: is_char_irr.
by apply: IH; rewrite -ltnS -F1.
Qed.

Lemma is_char_cbP : forall f,
  reflect 
    (exists n, f = \sum_(i : irr G) (n i)%:R *: (i : cfun _ _))
    (is_char f).
Proof.
move=> f; apply: (iffP idP)=> [HH|[n ->]]; last exact: is_char_cb.
exists (fun i => getNatC (ncoord i f)).
rewrite {1}(ncoord_sum (is_char_in_cfun HH)).
apply: eq_bigr=> i _.
by move/(@is_char_isNatC_ncoord i): HH; rewrite getNatCP; move/eqP<-.
Qed.

End IsChar.

Section MoreIsChar.

Lemma is_char_restrict : forall (gT : finGroupType) f (G H : {group gT}), 
  H \subset G -> is_char G f -> is_char H ('Res[H] f).
Proof.
move=> gT f G H Hsub; case/is_charRP=> n [rG <-].
apply/is_charRP; exists n; exists (subg_repr rG Hsub).
apply/cfunP=> g; rewrite !cfunE; case E1: (_ \in _); last by rewrite !mul0r.
by rewrite (subsetP Hsub) // !mul1r.
Qed.

End MoreIsChar.

Section Linear.

Variables (gT : finGroupType) (G : {group gT}) (f: cfun gT algC).

Definition clinear f := is_char G f && (f 1%g == 1).

Hypothesis CLf : clinear f.

Lemma clinear1: f 1%g = 1.
Proof. by apply/eqP; case/andP: CLf. Qed.

Lemma clinearM: forall g h,
  g \in G -> h \in G -> f (g * h)%g = f g * f h.
Proof.
move=> g h InG InH.
case/andP: (CLf); case/is_charRP=> // n [rG <-] HH.
move/eqP: (char_of_repr1 rG); rewrite (eqP HH) -(eqN_eqC 1%N) => Hn.
rewrite !cfunE groupM // InG InH // !mul1r repr_mxM //.
move: {HH}rG; rewrite -(eqP Hn)=> rG.
rewrite (mx11_scalar (rG g)) (mx11_scalar (rG h)) -scalar_mxM.
by rewrite !mxtrace_scalar !mulr1n.
Qed.

Lemma clinear_neq0: forall g, g \in G -> f g != 0.
Proof.
move=> g InG; apply/eqP=> fg.
case/eqP: (nonzero1r algC); case/andP: (CLf)=> _; move/eqP<-.
by rewrite -(mulgV g) clinearM ?groupV // fg mul0r.
Qed.

Lemma clinearV: forall g, g \in G -> f (g^-1)%g = (f g)^-1.
Proof.
move=> g InG.
have F1: f g * f (g^-1%g) = 1 by rewrite -clinearM ?groupV // mulgV clinear1.
have F2 := clinear_neq0 InG.
by apply: (mulfI F2); rewrite F1 divff.
Qed.

Lemma clinearX : forall g n, g \in G -> (f g)^+n = f (g^+n)%g.
Proof.
move=> g n Hin; elim: n=> [|n IH]; first by rewrite expr0 expg0 clinear1.
by rewrite exprS expgS clinearM ?groupX // IH.
Qed.

Lemma clinear_unit : forall g, g \in G -> f g ^+ #[g] = 1.
Proof. by move=> g InG; rewrite clinearX // expg_order clinear1. Qed.

Lemma clinear_norm : forall g, g \in G -> normC (f g) = 1%:R.
Proof.
move=> g InG; have Hs := clinear_unit InG.
apply/eqP; rewrite -(@posC_unit_exp _ (#[g].-1)) //; last by exact: posC_norm.
by rewrite prednK // -normC_exp Hs normC1.
Qed.

Lemma clinearV_norm : forall g, g \in G ->  f (g^-1%g) = (f g)^*.
Proof.
move=> g InG; rewrite invg_expg -clinearX //.
apply: (mulfI (clinear_neq0 InG)).
rewrite -exprS prednK // clinear_unit // -[_ * _]sqrCK.
move: (clinear_norm InG); rewrite /normC => -> //.
by rewrite exprS mulr1.
Qed.

Lemma char_abelianP : 
  reflect (forall (i : irr G), clinear i) (abelian G).
Proof.
apply: (iffP idP)=> [HH i|HH].
  rewrite /clinear irr_val1 irr_degree_abelian //; last exact: groupC.
  by rewrite is_char_irr // eqxx.
rewrite card_classes_abelian.
rewrite eqN_eqC -irr_sum_square // (eq_bigr (fun i => 1)) //=.
  by rewrite sumr_const // -card_irr.
by move=> i _; case/andP: (HH i)=> _ HH'; rewrite (eqP HH') exprS mulr1.
Qed.

Lemma irr_repr_linear : forall (i : irr G) g,
   g \in G -> clinear i -> irr_repr (socle_of_irr i) g = (i g)%:M.
Proof.
move=> i g InG AbG.
rewrite cfunE InG mul1r.
move: (irr_repr (socle_of_irr i)).
case/andP: AbG=> _; rewrite irr_val1.
rewrite -(eqN_eqC _ 1);move/eqP->.
move=> irr_repr; rewrite trace_mx11.
apply/matrixP=> [] [[|] Hi1] // [[|] Hj1] //.
by rewrite !mxE /= mulr1n; congr fun_of_matrix; apply/eqP.
Qed.

Lemma clinear_is_irr : is_irr G f.
Proof.
case/andP: (CLf)=> Hc Hf.
case/is_charRP: Hc => n [rG HrG].
move: Hf; rewrite -HrG char_of_repr1 -(eqN_eqC _ 1%N).
move/eqP=> Hn; move: rG HrG; rewrite Hn.
move=> rG HrG; apply/is_irrP.
pose sG := DecSocleType (regular_repr algC G).
exists (IrrClass (irr_comp sG rG)).
apply/eqP; apply/char_of_repr_rsimP=> /=.
apply: rsim_irr_comp; first by exact: pGroupG.
apply/mx_irrP; split=> // U HU HU1.
move: HU1 (rank_leq_row U); rewrite -mxrank_eq0 /row_full.
by case: (\rank _)=> // [] [|].
Qed.

End Linear.

Section Character.

Variable (gT : finGroupType) (G : {group gT}).

Structure character : Type := Character {
    cfun_of_character :> cfun gT algC;
                    _ : is_char G cfun_of_character
}.

Canonical Structure character_subType :=
  Eval hnf in [subType for cfun_of_character by character_rect].
Canonical Structure character_eqMixin := [eqMixin of character by <:].
Canonical Structure character_eqType := 
  Eval hnf in EqType character character_eqMixin.
Definition character_choiceMixin := [choiceMixin of character by <:].
Canonical Structure character_choiceType :=
  Eval hnf in ChoiceType character character_choiceMixin.

Lemma is_char_character : forall (chi : character), is_char G chi.
Proof. by case. Qed.

Definition character_of_char (n : nat) (rG : mx_representation algC G n) :=
  Character (is_char_char_of_repr rG).

Canonical Structure character_of_irr (i : irr G) := 
  Character (is_char_irr i).

Lemma charRE : forall f : character,
  exists n, exists rG : mx_representation algC G n, char_of_repr G rG = f.
Proof. by move=> f; move/is_charRP: (is_char_character f). Qed.

Lemma is_charP : forall f,
  reflect (exists fc : character, fc = f :> cfun _ _)
          (is_char G f).
Proof.
move=> f; apply: (iffP (is_charRP G f))=> [[n [rG HrG]]|].
  by exists (character_of_char rG).
case=> fc <-; case/is_charRP: (is_char_character fc)=> n [rG <-].
by exists n; exists rG.
Qed.
 
Lemma char_isNatC_ncoord : forall (i : irr G) (f : character),
  isNatC (ncoord i f).
Proof.
move=> i f; case/is_charRP: (is_char_character f)=> n [rG <-].
by rewrite ncoord_repr isNatC_nat.
Qed.

Lemma character_in_cfun : forall f : character, (f : cfun _ _) \in 'CL[algC](G).
Proof.
move=> f; case/is_charRP: (is_char_character f) => n [rG <-].
by apply: char_of_repr_in_cfun.
Qed.

Lemma ncoord_character : forall f : character, 
  f = \sum_(i : irr G) ncoord i f *: (i : cfun _ _) :> cfun _ _.
Proof. by move=> f; apply: ncoord_sum; exact: character_in_cfun. Qed.

Definition character0 := Character (is_char0 G).

Local Notation "0" := (character0 _) : character_scope.

Definition character1 := character_of_irr (irr1 G).

Lemma character1E : forall g, character1 g = (g \in G)%:R.
Proof. by move=> g; move: (irr1E G g). Qed.

Local Notation "1" := (character1 _) : character_scope.

Canonical Structure character_add (ch1 ch2 : character) := 
   Character (is_char_add (is_char_character ch1) (is_char_character ch2)).

Local Notation "f + g" := (character_add  _ f g) : character_scope.

Canonical Structure character_scal n (f : character) := 
   Character (is_char_scal n (is_char_character f)).

Local Notation "f *+ g" := (character_scal  _ f g) : character_scope.

Canonical Structure character_cb P n :=  Character (@is_char_cb _ G P n).

Lemma charE : forall f : character,
  exists n, f = \sum_(i : irr G) (n i)%:R *: (i : cfun _ _) :> cfun _ _.
Proof.
by move=> f; case/is_char_cbP: (is_char_character f)=> n ->; exists n.
Qed.

Definition get_char (f : cfun _ _) := 
  character_cb xpredT (fun i : irr G => getNatC (ncoord i f)).

Lemma get_charE : forall f, is_char G f -> get_char f = f :> cfun _ _ .
Proof.
move=> f; case/is_charP=> cf <-.
rewrite {2}(ncoord_character cf).
apply: eq_bigr=> i _; congr (_ *: _).
by apply/eqP; rewrite eq_sym -getNatCP char_isNatC_ncoord.
Qed.

Canonical Structure char_reg := 
  @Character (reg_cfun G) (is_char_char_of_repr _).

Lemma char_norm : forall (f : character) (g : gT), normC (f g) <= f 1%g.
Proof.
move=> f g; case: (charRE f)=> n [rG <-].
case: (boolP (g \in G))=> Hin; last first.
  by rewrite (cfun0 (char_of_repr_in_cfun _)) // normC0 char_of_repr1 posC_nat.
have F1: (<[g]> \subset G) by rewrite cycle_subG.
pose rG' := subg_repr rG F1.
have Hf: forall g1, g1 \in <[g]> -> 
    char_of_repr G rG g1 = char_of_repr <[g]> rG' g1.
  by move=> g1 Hg1; rewrite !cfunE Hg1; move/subsetP: (F1)->.
rewrite !Hf ?(cycle_id,group1) // (ncoord_sum (char_of_repr_in_cfun _)).
rewrite !sum_cfunE 2!cfunE.
pose nc (i: irr <[g]>) := ncoord i (char_of_repr <[g]> rG').
suff->: \sum_i (nc i *: (i: cfun _ _)) 1%g = 
        \sum_i normC ((nc i *: (i: cfun _ _)) g%g).
  by apply: normC_sum.
have F2 := cycle_abelian g.
apply: eq_bigr=> i _.
rewrite cfunE irr_val1 irr_degree_abelian //; last by exact: groupC.
have CLf: clinear <[g]> i by move/char_abelianP: F2; apply.
rewrite cfunE normC_mul (clinear_norm  CLf) ?cycle_id //.
by rewrite normC_pos // /nc ncoord_repr posC_nat.
Qed.

Lemma character_indi : forall (P: cfun gT algC -> Prop),
  P 0 -> (forall (i : irr G) (f : character), P f -> P ((i : cfun _ _) + f)) ->
  forall (f : character), P f.
Proof.
move=> P P0 IH f.
case: (charE f)=> n ->.
elim: {n}(\sum_i (n i))%N {-2}n (leqnn (\sum_i (n i)))=>[n HH|N IH1 n].
  rewrite big1 // => i _.
  by move: HH; rewrite (bigD1 i) //=; case: (n i)=> //; rewrite scale0r.
case: (boolP (all (fun i => n i == 0%N) (enum (irr G)))).
  move/allP=> Hi _; rewrite big1 // => i _.
  move: (Hi i); rewrite mem_enum.
  by move/(_ is_true_true); move/eqP->; rewrite scale0r.
case/allPn=> i; rewrite mem_enum=> Hi Ni0 HH.
pose n' (j : irr G) := if (j == i) then (n j).-1 else n j.
have F1: (\sum_i (n i) = (\sum_i (n' i)).+1)%N.
  rewrite (bigD1 i) // [(\sum_i n' i)%N](bigD1 i) //= -add1n addnA.
  congr (_ + _)%N; first by rewrite /n' eqxx; case: (n i) Ni0.
  by apply: eq_bigr=> j Hj; rewrite /n' (negPf Hj).
have F2: \sum_i (n i)%:R *: (i : cfun _ _)  = 
           (i : cfun _ _) + \sum_i (n' i)%:R *: (i : cfun _ _).
  rewrite (bigD1 i) //= [\sum_i (n' i)%:R *: _](bigD1 i) //=.
  rewrite addrA; congr (_ + _).
    rewrite /n' eqxx; case: (n i) Ni0=> // m' _.
    by rewrite -{1}add1n natr_add scaler_addl scale1r.
  by apply: eq_bigr=> j Hj; rewrite /n' (negPf Hj).
rewrite F2; apply: IH; apply: IH1.
by rewrite -ltnS -F1.
Qed.

Lemma isNatC_character1 : forall f : character, isNatC (f 1%g).
Proof.
move=> f; apply character_indi=> {f}[|i f IH].
  by rewrite cfunE (isNatC_nat 0).
by rewrite cfunE isNatC_add // irr_val1 isNatC_nat.
Qed.

Lemma posC_char1 : forall f : character, 0 <= f 1%g.
Proof. by move=> f; apply: posC_isNatC; apply: (isNatC_character1 _). Qed.

Lemma clinear_norm_scalar : 
  forall (f : character) n (rG : mx_representation algC G n) g,
   g \in G -> 
   (forall (i : irr G), clinear G i) ->
   normC (f g) = f 1%g ->
   char_of_repr G rG = f -> exists2 c, normC c = (n != 0%N)%:R & rG g = c%:M.
Proof.
move=> f n rG g InG Hi.
move: n rG; apply character_indi=> {f}[|i f IH] n rG NN CC.
   have: mx_rsim rG (repr0 algC G)
     by apply/char_of_repr_rsimP; rewrite CC char_of_repr0.
   move/mxrank_rsim=> HH; move: {CC}rG; rewrite HH=> rG.
   exists 0; first by rewrite eqxx normC0.
   by rewrite (flatmx0 (rG g)) (flatmx0 _%:M) .
move: NN; rewrite cfunE [_ 1%g]cfunE=> NN.
have F1: normC (i g + f g) = normC (i g) + normC (f g).
  apply: (leC_anti (normC_add _ _)); rewrite NN.
  apply: leC_add; [apply: char_norm | apply: char_norm].
have F2 : normC (f g) = f 1%g.
  apply: (leC_anti (char_norm _ _)).
  by rewrite -(leC_add2l (i 1%g)) -NN F1 leC_add2r char_norm.
have F3: normC(i g) = i 1%g.
  by apply: (@addIr _ (normC (f g))); rewrite -F1 NN F2.
have F4 := (irr_repr_linear InG (Hi i)).
have F5: i 1%g = 1 by case: (Hi i); case/andP=> _;move/eqP.
case: (charRE f)=> m [rG1 Hf].
case: (IH _ _ F2 Hf)=> c H1c H2c.
move: H1c; case: eqP=> Hm H1c.
  have F6: mx_rsim rG (irr_repr (socle_of_irr i)).
    apply/char_of_repr_rsimP; rewrite CC.
    suff->: f = 0 :> cfun _ _ by rewrite addr0.
    rewrite -Hf; move: {Hf H2c}rG1; rewrite Hm=> rG1.
    by apply/cfunP=> h; rewrite !cfunE (flatmx0 (rG1 _)) mxtrace0 mulr0.
  exists (i g); last by apply: (mx_rsim_scalar InG (mx_rsim_sym F6)).
  rewrite F3; case/andP: (Hi i)=> _; move/eqP->.
  case: eqP=> //; move/eqP; rewrite eqN_eqC.
  move/mxrank_rsim: F6->; rewrite -(irr_val1 i) F5.
  by rewrite -(eqN_eqC 1 0).
have F6 : (i g) = c.
  case/normC_add_eq: F1=> k Hk.
  case/andP; move/eqP=> H1k; move/eqP=> H2k.
  rewrite H1k F3 F5 mul1r.
  move/eqP: Hm; rewrite neq0N_neqC;move/mulfI; apply.
  move: H2k; rewrite -Hf cfunE InG mul1r H2c.
  rewrite mxtrace_scalar -mulr_natr normC_mul H1c mul1r.
  by rewrite normC_pos ?posC_nat // mulrC.
pose rG' := add_repr (irr_repr (socle_of_irr i)) rG1.
have F7: mx_rsim rG rG' 
  by apply/char_of_repr_rsimP; rewrite CC char_of_repr_morph Hf.
have F8 : rG' g = c%:M.
  have->: rG' g= block_mx (irr_repr (socle_of_irr i) g) 0 0 (rG1 g).
   by [].
  by rewrite H2c F4 F6 -scalar_mx_block.
exists c; last by by apply: (mx_rsim_scalar InG (mx_rsim_sym F7)).
rewrite H1c; case/mxrank_rsim: F7; move/eqP.
rewrite eqN_eqC natr_add -(irr_val1 i) F5 -(natr_add _ 1%N m) -eqN_eqC.
by case: {rG CC}n.
Qed.

Lemma clinear_cker_mx1 : 
  forall (f : character) n (rG : mx_representation algC G n) g,
   g \in G -> 
   (forall (i : irr G), clinear G i) ->
   f g = f 1%g -> char_of_repr G rG = f -> rG g = 1%:M.
Proof.
move=> f n rG g InG Hi Heq HC.
case/isNatCP: (isNatC_character1 f)=> k Hk.
case: (clinear_norm_scalar InG Hi _ HC)=> [|c Hc Hx].
  by rewrite Heq Hk normC_pos // posC_nat.
move: Hk; rewrite -Heq -HC cfunE InG Hx mxtrace_scalar.
move: Hc; case: eqP=> [HH _ _|Hn HN]; first by rewrite HH !(flatmx0 _%:M).
rewrite mul1r=> HH.
suff->: c = 1 by [].
have F1: n%:R != 0 :> algC by rewrite -neq0N_neqC; move/eqP: Hn.
have F2: c = k%:R * n%:R^-1.
  by apply: (mulIf F1); rewrite mulr_natr HH mulfVK.
move: HN; rewrite F2.
by rewrite normC_mul normC_inv normC_pos ?posC_nat // normC_nat.
Qed.

Lemma crestrict_subg : 
  forall (H: {group gT}) n (rG : mx_representation algC G n)
                              (HsG: H \subset G),
  'Res[H] (char_of_repr G rG) = char_of_repr H (subg_repr rG HsG).
Proof.
move=> H n rG HsG; apply/cfunP=> g; rewrite !cfunE /=.
by case InH: (g \in H); rewrite ?mul0r // (subsetP HsG _ (idP InH)) !mul1r.
Qed.

Lemma is_irr_crestrict : forall (H : {group gT}) (f : character),
 H \subset G -> is_irr H ('Res[H] f) -> is_irr G f.
Proof.
move=> H f; case: (charRE f)=> n [rG <-] HsG.
rewrite (crestrict_subg _ HsG).
case/is_irrP=> i Hi.
pose sG := DecSocleType (regular_repr algC G).
apply/is_irrP.
exists (IrrClass (irr_comp sG rG)).
apply/eqP;apply/char_of_repr_rsimP=> /=.
apply: rsim_irr_comp; first by exact: pGroupG.
apply: (@subg_mx_irr _ _ _ _ _ _ HsG).
move/eqP: Hi; move/char_of_repr_rsimP=> /=.
move/mx_rsim_sym; move/mx_rsim_irr; apply.
by apply: socle_irr.
Qed.

Definition is_comp (i : irr G) (f : cfun gT algC) := ncoord i f != 0.

Lemma is_compE : forall i f, is_comp i f = (ncoord i f != 0).
Proof. by []. Qed.

Lemma is_comp_neq0 : forall f : character,
 f != character0 -> exists i, is_comp i f.
Proof.
move=> f Nf0; case: (pickP (is_comp^~ f)) => [i Hi | HH].
  by exists i.
case/eqP: Nf0; apply/val_eqP=> /=.
move: (ncoord_character f); rewrite big1=> [|i Hi]; first by move=> ->.
by move/eqP: (HH i)->; rewrite scale0r.
Qed.

Lemma is_comp_irr1_char1 : forall (i : irr G) (f : character), 
   is_comp i f -> i 1%g <= f 1%g.
Proof.
move=> i f; rewrite is_compE => Hn.
rewrite (ncoord_sum (character_in_cfun f)) (bigD1 i) //=.
set i1 := i 1%g; rewrite 2!cfunE {}/i1 -leC_sub addrC addrA.
apply: posC_add.
  rewrite -mulN1r -mulr_addl posC_mul //; last first.
    by rewrite posC_isNatC // isNatC_character1.
  case/isNatCP: (char_isNatC_ncoord i f) Hn=> [] [|n] -> //.
    by rewrite /is_comp; case/negP.
  by move=> _; rewrite -add1n natr_add addrA addNr add0r posC_nat.
rewrite sum_cfunE cfunE posC_sum // => j Hj.
rewrite cfunE posC_mul //; last first.
  by rewrite posC_isNatC // isNatC_character1.
by rewrite posC_isNatC // (char_isNatC_ncoord j f).
Qed.

Lemma is_char_conjC : forall f : character, is_char G (f^*)%CH.
Proof.
move=> f; case: (charRE f)=> n [rG <-].
apply/is_charRP; exists n; exists (map_repr conjC rG).
by apply/cfunP=> h; rewrite !cfunE map_reprE trace_map_mx rmorphM conjC_nat.
Qed.

Canonical Structure character_conjC (f : character) :=
  Character (is_char_conjC f).

Definition character_conjCE : forall (f : character),
  character_conjC f = (f^*)%CH :> cfun _ _.
Proof. by move=> f; apply/cfunP=> h; rewrite cfunE. Qed.

End Character.

Notation "0" := (character0 _) : character_scope.
Notation "1" := (character1 _) : character_scope.
Notation "f + g" := (character_add  _ f g) : character_scope.
Notation "f *+ g" := (character_scal  _ f g) : character_scope.

Section MoreCharacter.

Variable (gT : finGroupType) (G H : {group gT}) 
         (HsG : H \subset G).

Definition character_rest (f : character G) :=
  Character (is_char_restrict HsG (is_char_character f)).

Definition irr_rest (i : irr G) :=  character_rest (character_of_irr i).

Lemma character_restE : forall f : character G,
  character_rest f = 'Res[H] f :> cfun _ _.
Proof. by []. Qed.
  
End MoreCharacter.

Section OrthogonalRelations.

Variable (aT gT : finGroupType) (A : {group aT}) (G : {group gT}).

Lemma char_inv : forall n (rG: mx_representation algC G n) g,
  char_of_repr G rG g^-1%g = (char_of_repr G rG g)^*.
Proof.
move=> n rG g.
case: (boolP (g \in G))=> Hin; last first.
  by rewrite (cfun0 (char_of_repr_in_cfun _) Hin); rewrite -groupV // in Hin;
     rewrite (cfun0 (char_of_repr_in_cfun _)) // conjC0.
have F1: (<[g]> \subset G) by rewrite cycle_subG.
pose rG' := subg_repr rG F1.
have F2: forall g1, g1 \in <[g]> -> 
    char_of_repr G rG g1 = char_of_repr <[g]> rG' g1.
  by move=> g1 Hg1; rewrite !cfunE Hg1; move/subsetP: (F1)->.
rewrite !F2 ?(groupVr,cycle_id) //. 
rewrite (ncoord_sum (char_of_repr_in_cfun _)).
rewrite sum_cfunE 2!cfunE rmorph_sum; apply: eq_bigr=> i _.
have Cf: clinear <[g]> i by move/char_abelianP: (cycle_abelian g); move/(_ i).
rewrite cfunE (clinearV_norm Cf) ?cycle_id //.
have F3: isNatC (ncoord i (char_of_repr <[g]> rG'))
  by rewrite ncoord_repr; apply: isNatC_nat.
by rewrite -{1}(isNatC_conj F3) {1}/GRing.scale /= -rmorphM ?cfunE.
Qed.

Lemma character_inv : forall (f : character G) g, f g^-1%g = (f g)^*.
Proof.
move=> f g; case: (charRE f)=> n [rG <-]; exact: char_inv.
Qed.

Let card_neq0 : #|G|%:R^-1 != 0 :> algC.
Proof. by rewrite invr_eq0 neq0GC. Qed.

(* Painfully following Isaacs' proof 2.14 *)
Lemma irr_first_orthogonal_relation : forall i j: irr G,
 (#|G|%:R^-1 * \sum_(g \in G) i g * (j g)^*)%R = (i == j)%:R.
Proof.
move=> i j.
rewrite (reindex invg) /=; last by apply: onW_bij; apply: inv_bij; exact invgK.
pose e (i : irr G) :=  Wedderburn_id (socle_of_irr i).
have F1 : e i *m e j = (i == j)%:R *: e i.
  case: eqP=> [<-|Hij]; [rewrite scale1r | rewrite scale0r].
    case: (Wedderburn_is_id (pGroupG _) (socle_of_irr i))=> _ Hi Hj _.
    by exact: Hj.
  move/eqP: Hij=> HH; apply: (Wedderburn_mulmx0 HH); exact: Wedderburn_id_mem.
have F2: #|G|%:R^-1 * i 1%g * j 1%g != 0.
  by do 2 (apply: mulf_neq0; last by exact: irr1_neq0).
apply: (mulIf F2).
pose r1 (u: 'M[algC]_#|G|) := gring_row u 0 (gring_index G 1%g).
apply: (@etrans _ _ (r1 (e i *m e j))); last first.
  rewrite F1 /=; case: eqP=> [->|_].
    by rewrite scale1r mul1r /r1 gring_row_e !mxE gring_indexK // invg1.
  rewrite scale0r mul0r /r1.
  suff->: @gring_row algC _ G 0 = 0 by rewrite mxE.
  by apply/rowP=> k; rewrite !mxE.
pose gr i g := gring_row (e i) 0 (gring_index G g). 
suff->:
    r1 (e i *m e j) = \sum_(g \in G) gr i g * gr j (g^-1)%g.
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
have F3: (e j \in group_ring algC G)%MS.
  apply (submx_trans (Wedderburn_id_mem _)).
  by rewrite /Wedderburn_subring genmxE submxMl.
rewrite -{1}(gring_rowK F3) mxE.
  (* This takes ages
rewrite {1}(reindex (@enum_val _ (fun x=> x \in G))) /=; last first.
  *)
rewrite {1}(@reindex _ _ (GRing.add_comoid algC) _ _
     (@enum_val _ (fun x=> x \in G))) /=; last first.
  by exists (gring_index G)=> g Hg; [exact: gring_valK | apply: gring_indexK].
apply: eq_big=> [g|i1 _]; first by rewrite enum_valP.
rewrite  /gr !gring_valK; congr (_ * _).
rewrite 2!mxE.
  (* This takes ages
rewrite {1}(@bigD1 (gring_index G (enum_val i1)^-1)) //=.
  *)
rewrite {1}(@bigD1 _ _  (GRing.add_comoid algC) _ 
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

Lemma irr_second_orthogonal_relation : forall (y z: gT), 
 y \in G -> z \in G ->
 \sum_(i : irr G) i y * (i z)^* =
   if y \in (z ^: G) then #|'C_G[z]|%:R else 0.
Proof.
move=> y z Hy Hz.
have F0: forall j, (j < #|irr G| -> j < #|classes G|)%N 
  by move=> j; rewrite card_irr.
pose f i := Ordinal (F0 _ (ltn_ord i)).
have G0: forall j, (j < #|classes G| -> j < #|irr G|)%N 
  by move=> j1; rewrite card_irr.
pose g i := Ordinal (G0 _ (ltn_ord i)).
have FG: forall i, f (g i) = i by move=> i; apply/val_eqP.
have GF: forall i, g (f i) = i by move=> i; apply/val_eqP.
pose X := \matrix_(i < #|irr G|, j < #|irr G|) 
  ((enum_val i) (repr (enum_val (f j)))).
pose Y := \matrix_(i < #|irr G|, j < #|irr G|) 
  (let C := enum_val (f i) in #|C|%:R * (#|G|%:R^-1 * (enum_val j) (repr C))^*).
have F2: X *m Y = 1%:M.
  apply/matrixP=> i j; rewrite !mxE.
  have->: (i == j) = (enum_val i == enum_val j).
    by apply/eqP/eqP; [move-> | exact: enum_val_inj].
  rewrite -irr_first_orthogonal_relation -mulr_sumr cfun_sum; last first.
    by move=> g1 g2 Hg1 Hg2; 
       rewrite -!char_inv  -conjVg  !(cfunJ (char_of_repr_in_cfun _)) ?groupV.
  rewrite (reindex g) /=; last by apply: onW_bij; exists f=> i1; apply/val_eqP.
  rewrite (reindex (@enum_val _ (fun x => x \in classes G))) /=; last first.
    by apply: (enum_val_bij_in (mem_classes (group1 G))).
  apply: eq_big=> [i1|i1 _]; first by rewrite enum_valP.
  rewrite !mxE /= FG.
  (* mimicking ring *)
  rewrite mulrC -!mulrA; congr (_ * _).
  rewrite rmorphM fmorphV ?conjC_nat //.
  by rewrite -mulrA [enum_val i _ * _]mulrC.
have Hi1: #|z ^: G|%:R != 0 :> algC.
  by rewrite -neq0N_neqC (cardsD1 z) class_refl.
apply: (mulfI (mulf_neq0 Hi1 card_neq0)); rewrite -mulr_sumr.
apply: (@etrans _ _ (y \in z ^: G)%:R); last first.
  case: (boolP (_ \in _))=> [Hin|]; last by rewrite mulr0.
  rewrite -(LaGrange (subcent1_sub z G)) index_cent1.
  rewrite mulrC mulrA natr_mul divff //.
  apply: mulf_neq0=> //.
  by rewrite -neq0N_neqC (cardsD1 z) (subcent1_id Hz).
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
rewrite (reindex (fun i: irr G => enum_rank i)); last first.
  by apply: onW_bij; apply: enum_rank_bij.
apply: eq_bigr=> i _.
rewrite !mxE /= !FG  /toC !enum_rankK !enum_rankK_in ?mem_classes //.
case: (repr_class G y)=> y1 Hy1->.
case: (repr_class G z)=> z1 Hz1->.
rewrite !(cfunJ (char_of_repr_in_cfun _)) //.
rewrite -!mulrA; congr (_ * _).
by rewrite rmorphM fmorphV ?conjC_nat // -mulrA [i _ * _]mulrC.
Qed.

Lemma irr_conjugate : forall (y z: gT), y \in G -> z \in G ->
  reflect (forall i : irr G, i y = i z) (y \in (z ^: G)).
Proof.
move=> y z Hy Hz; apply: (iffP idP)=> [HH chi|HH].
  case/imsetP: HH=> x Hx ->.
  by rewrite (cfunJ (char_of_repr_in_cfun _)).
move: (irr_second_orthogonal_relation Hy Hz); case: (_ \in _)=> // HH1.
move: (fun I=> posC_sum_eq0 I HH1).
have F1:  forall chi : irr G, 
  (chi \in index_enum (irr_finType G)) && xpredT chi -> 
     0 <= chi y * (chi z)^*.
  by move=> chi _; rewrite HH /leC subr0 repC_pconj.
case/eqP: (nonzero1r algC).
move: (posC_sum_eq0 F1 HH1); move/(_ (irr1 G)).
rewrite !irr1E Hy Hz conjC1 mul1r; apply=> //.
by rewrite  /index_enum -enumT mem_enum.
Qed.


(* This corresponds to Isaacs' 6.32 *)
Lemma action_irr_class_card : 
  forall (ito : action A (irr G))  (cto : action A {set gT}) a,
   a \in A -> [acts A, on (classes G) | cto] -> 
   (forall c (i : irr G),  c \in classes G -> i (repr c) = ito i a (repr (cto c a))) ->
     #|'Fix_ito[a]| = #|'Fix_(classes G| cto)[a]|.
Proof.
move=> ito cto a AiA Acto H.
 (* borrowed to the second orthogonality proof *)
have F0: forall j, (j < #|irr G| -> j < #|classes G|)%N 
  by move=> j; rewrite card_irr.
pose f i := Ordinal (F0 _ (ltn_ord i)).
have G0: forall j, (j < #|classes G| -> j < #|irr G|)%N 
  by move=> j1; rewrite card_irr.
pose g i := Ordinal (G0 _ (ltn_ord i)).
have FG: forall i, f (g i) = i by move=> i; apply/val_eqP.
have GF: forall i, g (f i) = i by move=> i; apply/val_eqP.
pose X := \matrix_(i < #|irr G|, j < #|irr G|) 
  ((enum_val i) (repr (enum_val (f j)))).
pose Y := \matrix_(i < #|irr G|, j < #|irr G|) 
  (let C := enum_val (f i) in #|C|%:R * (#|G|%:R^-1 * (enum_val j) (repr C))^*).
have F2: X *m Y = 1%:M.
  apply/matrixP=> i j; rewrite !mxE.
  have->: (i == j) = (enum_val i == enum_val j).
    by apply/eqP/eqP; [move-> | exact: enum_val_inj].
  rewrite -irr_first_orthogonal_relation -mulr_sumr cfun_sum; last first.
    move=> g1 g2 Hg1 Hg2.
    by rewrite -!char_inv  -conjVg !(cfunJ (char_of_repr_in_cfun _)) ?groupV.
  rewrite (reindex g) /=; last by apply: onW_bij; exists f=> i1; apply/val_eqP.
  rewrite (reindex (@enum_val _ (fun x => x \in classes G))) /=; last first.
    by apply: (enum_val_bij_in (mem_classes (group1 G))).
  apply: eq_big=> [i1|i1 _]; first by rewrite enum_valP.
  rewrite !mxE /= FG mulrC -!mulrA; congr (_ * _).
  by rewrite rmorphM fmorphV ?conjC_nat // -mulrA [enum_val i _ * _]mulrC.
 (****************************************)
pose Pa : 'M[algC]_ _ := 
  \matrix_(i < #|irr G|, j < #|irr G|) (ito (enum_val i) a == (enum_val j))%:R.
apply/eqP; rewrite eqN_eqC.
have <-: \tr Pa = #|'Fix_ito[a]|%:R.
  rewrite /mxtrace (bigID (fun u => (enum_val u) \in 'Fix_ito[a])) /=.
  rewrite (eq_bigr (fun u => 1%:R)); last first.
    move=> i; rewrite inE mxE; move/subsetP=> Hi.
    case: eqP=> // Hv; case: Hv; apply/eqP.
    by move: (Hi a); rewrite !inE; apply.
  rewrite sumr_const big1 ?addr0; last first.
    move=> i; rewrite inE mxE; move/subsetP=> Hi.
    by case: eqP=> // Hv; case: Hi=> b; rewrite !inE; move/eqP->; rewrite Hv.
  rewrite -mulr_natl mulr1 /= -(card_imset  (pred_of_set 'Fix_ito[a]) (@enum_rank_inj _)).
  apply/eqP; rewrite -eqN_eqC; apply/eqP; apply: eq_card=> i.
  apply/idP/imsetP; first by move=> j; exists (enum_val i)=> //; rewrite enum_valK.
  by case=> j Hj ->; rewrite /in_mem /= enum_rankK.
pose Qa : 'M[algC]_ _ := 
  \matrix_(i < #|irr G|, j < #|irr G|) (cto (enum_val (f i)) a == (enum_val (f j)))%:R.
have <-: \tr Qa = #|'Fix_(classes G | cto)[a]|%:R.
  rewrite /mxtrace (bigID (fun u => (enum_val (f u)) \in 'Fix_(classes G | cto)[a])) /=.
  rewrite (eq_bigr (fun u => 1%:R)); last first.
    move=> i; rewrite !inE !mxE; case/andP=> H1i; move/subsetP=> H2i.
    case: eqP=> // Hv; case: Hv; apply/eqP.
    by move: (H2i a); rewrite !inE; apply.
  rewrite sumr_const big1 ?addr0; last first.
    move=> i; rewrite !inE !mxE => Hi.
    case: eqP=> //; move/eqP=> Hv; case/negP: Hi; rewrite enum_valP.
    by apply/subsetP=> b; rewrite !inE; move/eqP->.
  rewrite -mulr_natl mulr1 /=.
  have F1: injective (enum_val \o f).
    by move=> i j; move/enum_val_inj; move/val_eqP=> HH; apply/eqP.
  rewrite -(card_imset _ F1).
  apply/eqP; rewrite -eqN_eqC; apply/eqP; apply: eq_card=> i.
  apply/imsetP/idP; first by case=> j Hj ->.
  move=> Hi; move: (Hi); rewrite inE; case/andP=> H1i _.
  by exists (g (enum_rank_in (classes1 _) i));  rewrite /in_mem /= FG enum_rankK_in.
have F3: X \in unitmx by case/mulmx1_unit: F2.
suff->: Qa = invmx X *m Pa *m X.
  rewrite mxtrace_mulC mulmxA mulmxV ?mul1mx //.
rewrite -[Qa]mul1mx -(mulVmx F3) -!mulmxA; congr (_ *m _).
apply/matrixP=> u v; rewrite !mxE.
have [oti H1o H2o]: bijective (ito ^~a).
  apply: injF_bij; apply: act_inj.
have [otc H1co H2co]: bijective (cto ^~a).
  apply: injF_bij; apply: act_inj.
have Hv : otc (enum_val (f v)) \in classes G.
  by rewrite -(acts_act Acto AiA) H2co enum_valP.
pose i1 := enum_rank (ito (enum_val u) a). 
have Hi1: ito (enum_val u) a = enum_val i1 by rewrite enum_rankK.
pose j1 := g (enum_rank_in (classes1 G) (otc (enum_val (f v)))).
have Hj1: cto (enum_val (f j1)) a = enum_val (f v).
  by rewrite FG enum_rankK_in ?H2co.
rewrite (bigD1 j1) // big1 /= ?addr0 => [|i Dii1]; last first.
  rewrite !mxE; case: eqP; rewrite ?mulr0 // -Hj1.
  by move/(can_inj H1co); move/enum_val_inj; move/val_eqP=> /==> HH; case/negP: Dii1.
 (* too slow ! 
rewrite (bigD1 i1) // big1 /= ?addr0=> [|i Dii1]; last first.
 *)
 have->: \sum_(j < #|irr G|) Pa u j * X j v = Pa u i1 * X i1 v.
  rewrite {1}(bigD1 i1) // big1 /= ?addr0=> [|i Dii1] //.
  rewrite !mxE; case: eqP; rewrite ?mul0r // Hi1.
  by move/enum_val_inj=> HH; case/eqP: Dii1.
rewrite !mxE Hi1 Hj1 !(eqxx, mulr1, mul1r).
by rewrite H FG enum_rankK_in // H2co  enum_rankK.
Qed.

End OrthogonalRelations.

Section InnerProduct.

Variable (gT : finGroupType) (G : {group gT}).

Let card_neq0 : #|G|%:R^-1 != 0 :> algC.
Proof. by rewrite invr_eq0 neq0GC. Qed.

Definition inner_prod (G : {set gT}) (f g : cfun _ _) :=
  #|G|%:R^-1 * \sum_(i \in G) f i * (g i)^*.

Local Notation "'[ f , g ]" := (inner_prod (val G) f g) (at level 0).

Lemma inner_prodE: forall (f g : cfun _ _),
  '[f,g] = #|G|%:R^-1 * \sum_(i \in G) f i * (g i)^*.
Proof. by []. Qed.

Let card_conj : (#|G|%:R^-1)^* = #|G|%:R^-1.
Proof. by rewrite posC_conjK // posC_inv posC_nat. Qed.

Lemma inner_conj : forall f g, '[f,g] = '[g,f]^*.
Proof.
move=> f g; rewrite /inner_prod rmorphM card_conj.
congr (_ * _); rewrite rmorph_sum; apply: eq_bigr=> i _.
by rewrite rmorphM conjCK mulrC.
Qed.
 
Lemma posC_inner_prod : forall f, 0 <= '[f, f].
Proof. 
move=> f; apply: posC_mul; first by rewrite posC_inv posC_nat.
by rewrite posC_sum // => i _; rewrite /leC subr0 repC_pconj.
Qed.

Lemma inner_prod0 : forall f, f \in 'CL[algC](G) -> ('[f, f] == 0) = (f == 0).
Proof.
move=> f Hf; apply/eqP/eqP=> Hp; last first.
  by rewrite Hp /inner_prod big1 ?mulr0 // => i _; rewrite !cfunE mul0r.
apply/cfunP=> g; rewrite cfunE.
case: (boolP (g \in G))=> Hin; last by rewrite (cfun0 Hf).
suff: f g * (f g)^* == 0.
  by rewrite mulf_eq0; case/orP; [move/eqP|rewrite conjC_eq0;move/eqP].
move: Hp; move/eqP; rewrite /inner_prod mulf_eq0; case/orP=> [|Hp].
  by rewrite (negPf card_neq0).
apply/eqP; apply: (posC_sum_eq0 _ (eqP Hp))=> //.
 by move=>*; rewrite -sqrC_pos; exact: posC_norm.
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
by rewrite scaler_mull -mulr_addl !cfunE.
Qed.

Canonical Structure inner_prodb_linear f :=
  Linear (inner_prodb_is_linear f).

Lemma inner_prod_is_additive : forall f, additive (inner_prod G f).
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

Lemma irr_orthonormal : forall (i j: irr G), '[i,j] = (i == j)%:R.
Proof.
by move=> i j; rewrite -irr_first_orthogonal_relation; congr (_ * _).
Qed.

Lemma ncoord_inner_prod : forall (f : cfun _ _) (i : irr G),
   f \in 'CL[algC](G) -> ncoord i f = '[f,i].
Proof.
move=> f i FiC.
rewrite {2}(ncoord_sum FiC) -inner_prodbE linear_sum.
by rewrite (bigD1 i) // big1=> [|j Hj]; 
   rewrite /= ?addr0 linearZ /= inner_prodbE irr_orthonormal;
    [rewrite eqxx /GRing.scale /= mulr1|rewrite (negPf Hj) scaler0].
Qed.

Lemma inner_prod_char : forall (ch1 ch2 : character G), 
   '[ch1,ch2] = \sum_(i : irr G) (ncoord i ch1) * (ncoord i ch2).
Proof.
move=> ch1 ch2; case: (charE ch1)=> n ->; case: (charE ch2)=> m ->.
rewrite -inner_prodbE {1}linear_sum /=.
apply: eq_bigr=> i _; rewrite linearZ /= inner_prodbE.
rewrite raddf_sum  {1}(bigD1 i) // big1 //= ?addr0 => [|j Hj]; last first.
  rewrite inner_prodZ irr_orthonormal.
  by move: Hj; rewrite eq_sym; case: (_ == _)=> //; rewrite mulr0.
rewrite inner_prodZ conjC_nat irr_orthonormal eqxx mulr1.
rewrite !linear_sum (bigD1 i) // big1 /= ?addr0 => [|j Hj]; last first.
  by rewrite linearZ /= ncoord_irr; case: (_ == _) Hj; rewrite // scaler0.
rewrite (bigD1 i) // big1 /= ?addr0 => [|j Hj]; last first.
  by rewrite linearZ /= ncoord_irr; case: (_ == _) Hj; rewrite // scaler0.
by rewrite !linearZ //= !ncoord_irr eqxx /GRing.scale /= !mulr1.
Qed.

Lemma inner_prod_char_nat : forall (ch1 ch2 : character G), isNatC '[ch1,ch2].
Proof.
move=> ch1 ch2; rewrite inner_prod_char //.
apply: isNatC_sum=> i _; apply: isNatC_mul; apply: char_isNatC_ncoord.
Qed.
 
Lemma inner_prod_charC : forall (chi1 chi2 : character G),
  '[chi1,chi2] = '[chi2,chi1].
Proof.
move=> chi1 chi2.
by rewrite !inner_prod_char //; apply: eq_bigr=> i _; rewrite mulrC.
Qed.

Lemma char_irreducibleE : forall (chi : character G),
  is_irr G chi = ('[chi, chi] == 1).
Proof.
move=> chi; apply/is_irrP/eqP=> [[i ->]|].
  by rewrite irr_orthonormal eqxx.
rewrite inner_prod_char //.
case: (charE chi)=> n Hchi HH.
case: (isNatC_sum_eq1 _ _ HH).
- move=> i _; apply: isNatC_mul;
     rewrite Hchi linear_sum isNatC_sum //= => j _; rewrite linearZ /= ?ncoord_irr;
       apply: isNatC_mul; apply: isNatC_nat.
- by rewrite /index_enum -enumT; exact: enum_uniq.
move=> i [Hin _ HF HG]; exists i.
apply/val_eqP=> /=; apply/eqP.
rewrite ncoord_character [cfun_of_irr i](ncoord_sum (char_of_repr_in_cfun _)).
congr finfun_of_cfun.
apply: eq_bigr=> k _; congr (_ *: _).
rewrite ncoord_irr; case: eqP=> [<-|]; last first.
  move/eqP; rewrite eq_sym=> Hik.
  have F1: k \in index_enum (irr_finType G).
    rewrite /index_enum -enumT.
    apply/(nthP (irr1 G)); exists (enum_rank k)=> //.
      case: enum_rank=> /= m; first by rewrite cardT /=.
    by apply/val_eqP; rewrite nth_enum_rank.
  move: (HG _ Hik F1 is_true_true).
  by move/eqP; rewrite mulf_eq0; case/orP; rewrite Hchi; move/eqP.
case/isNatCP: (char_isNatC_ncoord i chi) HF=> m ->; move/eqP=> HH1; apply/eqP.
by move: HH1; rewrite -natr_mul -eqN_eqC -(eqN_eqC _ 1); case: m=> //; case.
Qed.

Lemma cfun_conjC_inner : forall f1 f2 : cfun gT algC,
 ('[f1^*,f2^*])%CH = '[f1,f2]^*.
Proof.
move=> f1 f2; rewrite !inner_prodE rmorphM conjC_inv conjC_nat.
congr (_ * _); rewrite (big_morph _ (rmorphD conjC) conjC0); apply: eq_bigr.
by move=> g GiG; rewrite !cfunE rmorphM.
Qed.

Lemma is_irr_conjC : forall (i : irr G), 
  is_irr G (character_conjC (character_of_irr i))%CH.
Proof.
move=> i; rewrite char_irreducibleE character_conjCE cfun_conjC_inner //.
apply/eqP; rewrite -conjC1; congr (_^*); apply/eqP.
by rewrite -char_irreducibleE is_irr_irr.
Qed.
 
Definition irr_conjC (G : {group gT}) (i : irr G) :=
  get_irr G (character_conjC (character_of_irr i))%CH.

Lemma irr_conjCE : forall i : irr G,
  irr_conjC i = (i^*)%CH :> cfun _ _.
Proof. by move=> i; rewrite get_irrE // is_irr_conjC. Qed.

Lemma irr_conjCK : involutive (@irr_conjC G).
Proof.
by move=> i; apply: cfun_of_irr_inj; rewrite !irr_conjCE cfun_conjCK.
Qed.

End InnerProduct.

Notation "'[ u , v  ]_ G":=  (inner_prod (val G) u v) (at level 10).

Section Kernel.

Variable (gT : finGroupType) (G : {group gT}).

Definition cker (f : cfun gT algC) := 
  if is_char G f then [set g \in G | f g == f 1%g] else 1%G.

Lemma char_ckerE : forall (f : character G),
   cker f = [set g \in G | f g == f 1%g].
Proof. by move=> f; rewrite /cker is_char_character. Qed.

Lemma irr_ckerE : forall (f : irr G),
  cker f = [set g \in G | f g == f 1%g].
Proof.  by move=> f; rewrite /cker is_char_irr. Qed.

Lemma is_Nchar_cker : forall f, ~is_char G f -> cker f = 1%G.
Proof. by move=> f Hf; rewrite /cker; move/eqP: Hf; case: is_char. Qed.

Definition cfaithful f := cker f \subset 1%G.

Lemma cfaithful_reg : cfaithful (char_reg G).
Proof.
apply/subsetP=> g.
rewrite char_ckerE !inE !reg_cfunE eqxx.
case E1: (g == 1%g); first by move/eqP: E1->; rewrite group1 eqxx.
by rewrite eq_sym (negPf (neq0GC G)) andbF.
Qed.

Lemma ckerE : forall (f : character G), 
  cker f = if f == character0 G then (G : {set _}) else
             \bigcap_(i : irr G | is_comp i f) cker i.
Proof.
move=> f; rewrite char_ckerE //.
case: eqP=> [->|Hdf].
  by apply/setP=> g; rewrite !inE !cfunE eqxx andbT.
apply/setP=> g; apply/idP/bigcapP=> [|Hi]; last first.
  have InG: g \in G.
    move/eqP: Hdf; case/is_comp_neq0=> j; move/(Hi _).
    by rewrite irr_ckerE // inE; case/andP.
  rewrite inE /= ncoord_character !sum_cfunE !cfunE InG.
  apply/eqP; apply: eq_bigr=> i _; rewrite cfunE [_ 1%g]cfunE.
  case: (boolP (is_comp i f))=> [Hf|].
    by move: (Hi _ Hf); rewrite irr_ckerE // inE InG /=; move/eqP->.
  by rewrite negbK; move/eqP->; rewrite !mul0r.
rewrite inE; case/andP=> InG.
rewrite ncoord_character !sum_cfunE !cfunE.
move/eqP=> Hs i; rewrite irr_ckerE // !inE InG.
have->:
   cfun_of_fun (fun x : gT => 
                  \sum_(i:irr G) (ncoord i f *: (i : cfun _ _)) x) = f.
  by apply/cfunP=> x; rewrite cfunE {2}ncoord_character sum_cfunE cfunE.
move=> Hd.
have F: (ncoord i f *: (i : cfun _ _)) g = (ncoord i f *: (i : cfun _ _)) 1%g.
  have F1: 0 <= ncoord i f by apply: posC_isNatC; rewrite char_isNatC_ncoord.
  apply: (normC_sum_upper _ Hs)=> [j Hj|]; last first.
    by rewrite /index_enum -enumT mem_enum.
  have F2: 0 <= ncoord j f by apply: posC_isNatC; rewrite char_isNatC_ncoord.
  rewrite cfunE [(ncoord j f *: (j : cfun _ _)) 1%g]cfunE !normC_mul //.
  by rewrite normC_pos // leC_mul2l // char_norm.
apply/eqP; apply: (mulfI Hd).
by move: F; rewrite cfunE => ->; rewrite !cfunE.
Qed. 

Lemma cker_all1 : \bigcap_(i : irr G) cker i = 1%G.
Proof.
apply/setP=> g; apply/idP/idP; rewrite inE; last first.
  move/eqP->; apply/bigcapP=> i _.
  by rewrite irr_ckerE // inE group1 eqxx.
have F1: (\bigcap_(i : irr G) cker i) \subset cker (reg_cfun G).
  rewrite ckerE //.
  case: eqP=> Heq.
    have: char_reg G 1%g = 0 by rewrite Heq cfunE.
    rewrite cfunE group1 repr_mx1 mxtrace1 mul1r.
    by move/eqP; rewrite (negPf (neq0GC G)).
  by apply/subsetP=> h; move/bigcapP=> Hi; apply/bigcapP=> j _; exact: Hi.
move/(subsetP F1); rewrite char_ckerE // inE !reg_cfunE //.
case/andP=> InG; rewrite eqxx; case: (g == 1%g)=> //.
by rewrite eq_sym (negPf (neq0GC G)).
Qed.

Lemma is_comp_cker : forall (i : irr G) (f : character G),
  is_comp i f -> cker f \subset cker i.
Proof.
move=> i f HC.
rewrite ckerE; case: eqP=> HH; last by apply: (bigcap_min i).
by case/eqP: HC; rewrite HH ncoord0.
Qed.

End Kernel.

Section MoreKernel.

Variable (gT : finGroupType) (G : {group gT}).

Lemma char_rkerP : forall n (rG : mx_representation algC G n), 
  cker G (char_of_repr G rG) = rker rG.
Proof.
move=> n rG; rewrite /cker ?is_char_char_of_repr //.
apply/setP=> g; apply/idP/rkerP=>[Hg |[H1 H2]]; last first.
  by rewrite inE !cfunE H1 H2 repr_mx1 !group1 mul1r mxtrace1 eqxx.
have InG: g \in G by move: Hg; rewrite inE; case/andP.
split=> //.
have F1: (<[g]> \subset G) by rewrite cycle_subG.
pose rG' := subg_repr rG F1.
have H'g: g \in cker <[g]> (char_of_repr <[g]> rG').
  move: Hg; rewrite /cker ?is_char_char_of_repr //.
  by rewrite /rG' !inE !cfunE !group1 !InG cycle_id !mul1r.
suff: g \in rker rG' by rewrite inE mul1mx; case/andP=> _; move/eqP.
have Ing := cycle_id g.
apply/rkerP; split => //.
apply: (@clinear_cker_mx1 _ <[g]> (character_of_char rG'))=> //.
  by apply/char_abelianP; exact: cycle_abelian.
by move: H'g; rewrite /cker is_char_char_of_repr !inE Ing; move/eqP.
Qed.

Lemma cker_group_set : forall f, group_set (cker G f).
Proof.
move=> f; case: (boolP (is_char G f))=> Hf.
  case/is_charRP: Hf=> n [rG <-]; rewrite char_rkerP //.
  by exact: rstab_group_set.
rewrite is_Nchar_cker; last by move/negP: Hf.
by exact: group_set_one.
Qed.

Canonical Structure cker_group f := Group (cker_group_set f).

Lemma cker_normal : forall f, cker G f <| G.
Proof.
move=> f; case: (boolP (is_char G f))=> Hf.
  by case/is_charRP: Hf=> n [rG <-]; rewrite char_rkerP // rker_normal.
rewrite is_Nchar_cker; last by move/negP: Hf.
by exact: normal1.
Qed.

Lemma cker_sub : forall f, cker G f \subset G.
Proof. by move=> f; apply: (normal_sub (cker_normal _)). Qed.

Lemma char_ckerMr : forall (f : character G) x y,
  x \in cker G f -> y \in G -> f (x * y)%g = f y.
Proof.
move=> f x y.
case: (charRE f)=> // n [rG <-] XiC YiG.
have XiG: x \in G.
  by apply: (subsetP (cker_sub (char_of_repr G rG))).
rewrite !cfunE groupM ?YiG // repr_mxM //.
move: XiC; rewrite char_rkerP // inE XiG mul1mx andTb; move/eqP->.
by rewrite mul1mx.
Qed.

Lemma char_ckerMl : forall (f : character G) x y,
  x \in cker G f -> y \in G -> f (y * x)%g = f y.
Proof.
move=> f x y.
case: (charRE f)=> // n [rG <-] XiC YiG.
have XiG: x \in G by apply: (subsetP (cker_sub (char_of_repr G rG))).
rewrite !cfunE groupM ?YiG // repr_mxM //.
move: XiC; rewrite char_rkerP // inE XiG mul1mx andTb; move/eqP->.
by rewrite mulmx1.
Qed.

Lemma clinear_commutator : forall f,
  clinear G f -> (G^`(1) \subset cker G f)%g.
Proof.
move=> f Cf; case/andP: (Cf)=> F1 F2.
have->: cker G f = (cker_group f) by [].
rewrite gen_subG; apply/subsetP=> gh; case/imset2P=> g h InG InH ->.
rewrite /= /cker F1 inE groupR ?(InG,InH) // commgEl.
rewrite !(clinearM Cf) ?(groupM, groupV) // !(clinearV Cf) //.
rewrite mulrCA mulrC mulrA mulVf ?(clinear_neq0 Cf) //.
by rewrite mul1r divff ?(clinear_neq0 Cf) // (eqP F2) eqxx.
Qed.

End MoreKernel.

Section Coset.

Variable (gT : finGroupType).

Implicit Type G : {group gT}.

Definition qfun_of_cfun (N: {set gT}) (f : cfun gT algC) :=
  cfun_of_fun (fun x : coset_of N => f (repr x)).

Local Notation "f '/' N" := (qfun_of_cfun N f) : character_scope.

Definition cfun_of_qfun (N: {set gT}) (f : cfun (coset_groupType N) algC) :=
  cfun_of_fun (fun x : gT => (x \in 'N(N))%:R * f (coset N x)).

Local Notation " f '^()'" := (cfun_of_qfun f) (at level 2) : character_scope.

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
  is_char G f -> N <| G -> N \subset cker G f -> is_char (G/N) (f / N)%CH.
Proof.
move=> G N f; case/is_charRP=> // n [rG <-] HN HC.
move: (HC); rewrite char_rkerP=> HC' //.
pose rG' := quo_repr HC' (normal_norm HN).
suff->: (char_of_repr G rG / N)%CH = char_of_repr (G/N)%g rG'.
  by apply: is_char_char_of_repr; exact: coset_splitting_field.
by apply/cfunP=> M; rewrite !cfunE repr_quo_fact1.
Qed.

Lemma qfuncE : forall (G N : {group gT}) f x,
 is_char G f -> N <| G -> N \subset cker G f -> x \in G -> 
  (f / N)%CH (coset N x) = f x.
Proof.
move=> G N f x Cf NN  Ncker InG; rewrite !cfunE.
rewrite val_coset //; last by apply: (subsetP (normal_norm NN)).
case: repr_rcosetP=> y Hy.
by apply: (@char_ckerMr _ _ (Character Cf))=> //; apply: (subsetP Ncker).
Qed.

Lemma cfunqE : forall (N : {group gT}) f x,
 x \in 'N(N) -> (f ^())%CH x = f (coset N x).
Proof. by move=> N f x InG; rewrite !cfunE InG // mul1r. Qed.

Lemma is_char_cfunq : forall (G N : {group gT}) f,
  N <| G -> is_char (G/N) f -> is_char G (f^())%CH.
Proof.
move=> G N f NN; case/is_charRP=> n [rG <-].
pose rG' := coset_repr rG NN.
suff->: ((char_of_repr (G/N)%g rG)^())%CH = char_of_repr G rG' 
  by apply: is_char_char_of_repr.
apply/cfunP=> M; rewrite !cfunE mulrA -natr_mul mulnb.
rewrite repr_quo_fact2 //.
Qed.

(* We could do better *)
Lemma cker_cfunq : forall (G N : {group gT}) f,
 is_char (G/N) f -> N <| G -> N \subset cker G (f^())%CH.
Proof.
move=> G N f Cf HN.
have F1: is_char G (f^())%CH by apply: is_char_cfunq.
apply/subsetP=> g Hg.
have InG: g \in G by apply: (subsetP (normal_sub HN)).
rewrite /cker F1 inE InG !cfunqE ?group1 //.
- by rewrite !coset_id // eqxx.
by apply: (subsetP (normal_norm HN)).
Qed.

Lemma cfunq_id : forall (G N : {group gT}) f,
 is_char (G/N) f -> N <| G -> (f^()/ N)%CH = f.
Proof.
move=> G N f Cf HN.
have F1: is_char G (f^())%CH by apply: is_char_cfunq.
have F2:= cker_cfunq Cf HN.
have F3: is_char (G/N) (f^() / N)%CH by apply: is_char_qfunc.
apply/cfunP=> x.
case: (boolP (x \in (G/N)%g))=> [|InG]; last first.
  rewrite (cfun0 (is_char_in_cfun Cf)) //.
  by apply: (cfun0 (is_char_in_cfun F3)).
rewrite -imset_coset; case/imsetP=> y InG ->.
rewrite (@qfuncE G) //  cfunqE //.
by apply: (subsetP (normal_norm HN)).
Qed.

Lemma qfunc_id : forall (G N : {group gT}) f,
 is_char G f -> N <| G -> N \subset cker G f -> ((f/N)^())%CH = f.
Proof.
move=> G N f Cf HN Hc.
have F1: is_char (G/N) (f/N)%CH by apply: is_char_qfunc.
have F2: is_char G ((f/N)^())%CH by apply: is_char_cfunq.
apply/cfunP=> x.
case: (boolP (x \in G))=> InG; last first.
  rewrite (cfun0 (is_char_in_cfun Cf)) //.
  apply: (cfun0 (is_char_in_cfun F2))=> //.
rewrite cfunqE ?(@qfuncE G) //.
by apply: (subsetP (normal_norm HN)).
Qed.

Lemma qfunc_irr : forall (G N : {group gT}) (i : irr G),
 N <| G -> N \subset cker G i -> is_irr (G/N)%G (i/N)%CH.
Proof.
move=> G N i NN Cf.
pose sG := DecSocleType (regular_repr algC (G/N)%G).
move: (Cf); rewrite char_rkerP=> Cf' //.
pose rG := quo_repr Cf' (normal_norm NN).
apply/is_irrP; exists (IrrClass (irr_comp sG rG)).
apply/cfunP=> x.
have->: IrrClass (irr_comp sG rG) x =
       char_of_repr (G/N)%g (irr_repr (irr_comp sG rG)) x.
  by [].
have F1: mx_irreducible rG.
  by apply/quo_mx_irr=> //; apply: socle_irr.
have F2: ([char algC]^').-group (G / N)%G.
  by apply: sub_pgroup (pgroup_pi _)=> i' _; rewrite inE /= Cchar.
move/(rsim_irr_comp sG F2): F1.
move/char_of_repr_rsimP; move/eqP<-.
by rewrite /rG !cfunE repr_quo_fact1.
Qed.

Lemma cfunq_irr : forall (G N : {group gT}) (i : irr (G/N)),
 N <| G ->  is_irr G (i^())%CH.
Proof.
move=> G N i NN.
pose sG := DecSocleType (regular_repr algC G).
pose j := socle_of_irr i.
pose rG := coset_repr (irr_repr j) NN.
apply/is_irrP; exists (IrrClass (irr_comp sG rG)).
apply/cfunP=> x.
have->: IrrClass (irr_comp sG rG) x = 
          char_of_repr G (irr_repr (irr_comp sG rG)) x by [].
have F1: mx_irreducible rG.
  apply/(quo_mx_irr (coset_repr_rker (irr_repr j) NN) (normal_norm NN)).
  apply: (mx_rsim_irr (mx_rsim_sym (quo_coset_repr (irr_repr j) NN))).
  by apply: socle_irr.
move/(rsim_irr_comp sG (pGroupG G)): F1.
move/char_of_repr_rsimP; move/eqP<-.
rewrite /rG !cfunE.
by rewrite  mulrA -natr_mul mulnb repr_quo_fact2.
Qed.

Definition cirrq (G H : {group gT}) (i : irr (G/H)) := get_irr G (i^())%CH.

Lemma cirrqE : forall (G H : {group gT}) (i : irr (G/H)%G), 
  H <| G -> cirrq i = (i^())%CH :> cfun _ _.
Proof. by move=> *; rewrite /cirrq get_irrE // cfunq_irr. Qed.

Definition qirrc (G H : {group gT}) (i : irr G) := get_irr (G/H) (i/H)%CH.

Lemma qirrcE : forall (G H : {group gT}) (i : irr G), 
 H <| G  -> H \subset cker G i -> qirrc H i = (i/H)%CH :> cfun _ _.
Proof. by move=> *; rewrite /qirrc get_irrE // qfunc_irr. Qed.

Lemma cirrqK : forall (G H : {group gT}),
  H <| G -> cancel (@cirrq G H) (@qirrc G H).
Proof.
move=> G H HnG i; apply cfun_of_irr_inj.
have F1 := is_char_irr i.
by rewrite qirrcE // cirrqE ?cker_cfunq // (cfunq_id F1).
Qed.

Lemma qirrcK : forall (G H : {group gT}) (i : irr G),
  H <| G ->  H \subset cker G i -> cirrq (qirrc H i) = i.
Proof.
move=> G H i HnG Hi; apply cfun_of_irr_inj.
have F1 := is_char_irr i.
by rewrite cirrqE // qirrcE // (qfunc_id F1).
Qed.

Lemma norm_cap_cker : forall (G N : {group gT}), N <| G ->  
   N = \bigcap_(i : irr G | N \subset cker G i) (cker G i) :> {set _}.
Proof.
move=> G N NN; apply/eqP; rewrite eqEsubset; apply/andP; split.
  by  apply/bigcapsP.
apply/subsetP=> g; move/bigcapP=> Hg.
have InG : g \in G.
  case/is_irrP: (cfunq_irr (irr1 _) NN)=> j Hj.
  apply: (subsetP (cker_sub G j)). 
  by apply: Hg; rewrite -Hj; apply: cker_cfunq=>//; exact: is_char_irr.
have InN: g \in 'N(N) by apply: (subsetP (normal_norm NN)).
suff: coset N g \in \bigcap_(i : irr (G/N)) cker (G/N) i.
  by rewrite cker_all1; move/set1P; move/coset_idr; apply.
apply/bigcapP=> i _.
case/is_irrP: (cfunq_irr i NN)=> j Hj.
have: g \in cker G j by apply: Hg; rewrite -Hj cker_cfunq // is_char_irr.
rewrite /cker !(is_char_irr) !inE -(repr_quo_fact2 _ NN) InN.
rewrite -Hj !cfunqE ?group1 //.
suff->: coset N 1%g  = 1%g by [].
by apply: coset_id; exact: group1.
Qed.

Lemma sum_norm_quo : forall (H G : {group gT}) g,
   g \in G -> H <| G ->
    \sum_(i : irr (G/H)) (i (coset H g)) * (i (coset H g))^* =
    \sum_(i : irr G | H \subset cker G i) (i g) * (i g)^*.
Proof.
move=> H G g InG NN.
rewrite (reindex (@cirrq G H)) //=.
apply: eq_big=> i'; first by rewrite cirrqE // cker_cfunq // is_char_irr.
  by move=> _; rewrite cirrqE // cfunqE // (subsetP (normal_norm NN)).
exists (qirrc H)=> i' HH; first by apply: cirrqK.
by apply: qirrcK.
Qed.

Lemma norm_cker : forall (G N : {group gT}), N <| G ->  
   N = cker G ((char_reg (G/N)%G) ^())%CH :> {set _}.
Proof.
move=> G N NN; apply/setP=> g.
rewrite /cker is_char_cfunq ?is_char_char_of_repr // !inE.
case: (boolP (g \in G))=> InG /=; last first.
  by apply/idP=> HH; case/negP: InG; apply: (subsetP (normal_sub NN)).
rewrite !cfunqE ?(group1, (subsetP (normal_norm NN)) ) //.
rewrite !reg_cfunE (coset_id (group1 _)) eqxx.
case E1: (g \in N); first by rewrite coset_id // !eqxx.
case: (_ =P 1%g)=> [HH|__].
  by case/idP: E1; apply: coset_idr=> //; apply: (subsetP (normal_norm NN)).
by rewrite eq_sym (negPf (neq0GC _)).
Qed.

End Coset.

Notation "f '/' N" := (qfun_of_cfun N f) : character_scope.
Notation " f '^()'" := (cfun_of_qfun f) (at level 2) : character_scope.

Section Derive.

Variable gT : finGroupType.

Lemma clinear_commutator_irr : forall (G : {group gT}) (i : irr G),
  clinear G i = (G^`(1) \subset cker G i)%g.
Proof.
move=> G i; apply/idP/idP=> [|NN]; first by apply: clinear_commutator.
case/is_irrP: (qfunc_irr (der_normal 1 G) NN)=> j Hj.
have F1 : abelian (G/G^`(1)) := der_abelian 0 G.
move/char_abelianP: F1; move/(_ j)=> HH.
rewrite /clinear is_char_irr.
rewrite -(qfunc_id (is_char_irr _) (der_normal 1 G) NN).
rewrite cfunqE ?group1 //  Hj.
suff->: coset (G^`(1))%G 1%g = 1%g by case/andP: HH.
by apply: coset_id; exact: group1.
Qed.

(* This corresponds to Isaacs' 2.23(a) *) 
Lemma derive_at_cap : forall (G : {group gT}),
   (G^`(1) = \bigcap_(i : irr G | clinear G i) cker G i)%g.
Proof.
move=> G; rewrite (norm_cap_cker (der_normal 1 G)).
by apply: eq_bigl=> i; rewrite clinear_commutator_irr.
Qed.

(* Isaacs' 2.23(b) *)
Lemma card_linear : forall (G : {group gT}),
  #|[pred i: irr G | clinear G i]| = #|G : G^`(1)%g|.
Proof.
move=> G.
have F1 := der_normal 1 G.
rewrite -card_quotient ?normal_norm //.
move: (der_abelian 0 G); rewrite card_classes_abelian; move/eqP<-. 
rewrite -card_irr.
have->: (G^`(0) = G)%G by apply/val_eqP=> //.
rewrite -(card_imset _ (can_inj (cirrqK F1))) //.
apply: eq_card=> i.
rewrite !inE clinear_commutator_irr.
apply/idP/imsetP=> [HH|[j H1 ->]]; last first.
  by rewrite cirrqE // cker_cfunq // is_char_irr.
by exists (qirrc _ i)=> //; rewrite qirrcK.
Qed.

(* This is 2.24 *)
Lemma quotient_subcent_card : forall (G N : {group gT}) g,
 g \in G -> N <| G -> (#|'C_(G / N)[coset N g]| <= #|'C_G[g]|)%N.
Proof.
move=> G N g InG NN; rewrite leq_leC.
move: (irr_second_orthogonal_relation InG InG); rewrite class_refl => <-.
have InN : coset N g \in (G/N)%g by apply: mem_quotient.
move: (irr_second_orthogonal_relation InN InN); rewrite class_refl => <-.
rewrite sum_norm_quo //.
rewrite [\sum_i(_)](bigID (fun i : irr G => N \subset cker G i)) //=.
rewrite -{1}[\sum_(i|_)(_)]addr0 leC_add2l.
apply: posC_sum=> i _.
by rewrite /leC subr0; exact: repC_pconj.
Qed.

End Derive.

Section Center.

Variable (gT : finGroupType) (G : {group gT}).

Definition ccenter (f : cfun gT algC) := 
  if is_char G f then [set g \in G | normC(f g) == f 1%g] else 1%G.

Definition rcenter (n : nat) (rG : mx_representation algC G n) :=
  [set g \in G | is_scalar_mx (rG g)].

Lemma rcenter_norm: forall (n : nat) (rG : mx_representation algC G n) g c,
  n != 0%N -> g \in G -> rG g = c%:M -> normC(c) = 1.
Proof.
move=> [|n] // rG g c _ InG HrG.
have F1: forall m, rG (g ^+ m)%g = (c ^+ m)%:M.
  by move=> m; rewrite repr_mxX // HrG scalar_exp.
have F2: c ^+ #[g] = 1.
  move: (F1 #[g]); rewrite expg_order repr_mx1.
  by move/matrixP; move/(_ 0 0); rewrite !mxE eqxx mulr1n.
apply/eqP; rewrite -(@posC_unit_exp _ #[g].-1) ?posC_norm //.
by rewrite -normC_exp prednK ?order_gt0 // F2 normC1.
Qed.

Lemma rcenter_group_set : forall  (n : nat) (rG : mx_representation algC G n),
 group_set (rcenter rG).
Proof.
move=> n rG.
rewrite /group_set !inE group1 repr_mx1 scalar_mx_is_scalar.
apply/subsetP=> i; rewrite !inE; case/imset2P=> g1 g2; rewrite !inE.
case/andP=> InG1; case/is_scalar_mxP=> k1 Hk1.
case/andP=> InG2; case/is_scalar_mxP=> k2 Hk2 HH.
by rewrite HH groupM // repr_mxM // Hk1 Hk2 -scalar_mxM scalar_mx_is_scalar.
Qed.

(* Isaacs' 2.27a *)
Lemma char_rcenterP : forall n (rG : mx_representation algC G n), 
  ccenter (char_of_repr G rG) = rcenter rG.
Proof.
move=> n rG; rewrite /ccenter /rcenter ?is_char_char_of_repr //.
apply/setP=> g; apply/idP/idP; rewrite !inE; case/andP=> InG; last first.
  rewrite InG; case/is_scalar_mxP=> c.
  case: (boolP (n == 0%N))=> Hn.
    move: rG; rewrite (eqP Hn)=> rG.
    by rewrite !cfunE !(flatmx0 (rG _)) !mxtrace0 !mulr0 normC0 eqxx.
  move=> Hc; rewrite cfunE InG mul1r Hc mxtrace_scalar char_of_repr1.
  by rewrite -mulr_natr normC_mul (rcenter_norm Hn InG Hc) 
              mul1r normC_nat eqxx.
rewrite InG; move/eqP=> HH.
have F1: (<[g]> \subset G) by rewrite cycle_subG.
pose rG' := subg_repr rG F1.
have HH': normC (char_of_repr <[g]> rG' g) = char_of_repr <[g]> rG' 1%g.
  by move: HH; rewrite /rG' !cfunE !group1 !InG cycle_id.
suff: exists2 c, normC c = (n != 0%N)%:R & rG' g = c%:M.
  by case=> c _ HH1; apply/is_scalar_mxP; exists c; rewrite -HH1.
apply: (@clinear_norm_scalar  _ <[g]> (character_of_char rG'))=> //.
  exact: cycle_id.
by apply/char_abelianP; exact: cycle_abelian.
Qed.

Lemma ccenter_group_set : forall f, group_set (ccenter f).
Proof.
move=> f; case: (boolP (is_char G f))=> Hf; last first.
  by rewrite /ccenter (negPf Hf) group_set_one.
case/is_charRP: Hf=> n [rG <-]; rewrite char_rcenterP //.
by exact: rcenter_group_set.
Qed.

Lemma irr_ccenterE : forall (i : irr G) g,
  g \in G -> g \in ccenter i = (normC (i g) == i 1%g).
Proof. by move=> i g GiG; rewrite /ccenter (is_char_irr i) inE GiG. Qed.

Lemma char_ccenterE : forall (f : character G) g,
  g \in G -> g \in ccenter f = (normC (f g) == f 1%g).
Proof. by move=> i g GiG; rewrite /ccenter (is_char_character i) inE GiG. Qed.

Lemma ccenter_mulC : forall (f : character G) g h,
  g \in ccenter f -> h \in G -> f (g * h)%g = f (h * g)%g.
Proof.
move=> f; case: (boolP (is_char G f))=> Hf g h; last first.
  by rewrite /ccenter (negPf Hf); move/set1gP->; rewrite mul1g mulg1.
case/is_charRP: Hf=> n [rG <-]; rewrite char_rcenterP //.
rewrite inE !cfunE; case/andP=> GiG; case/is_scalar_mxP=> k rGK HiG.
by rewrite !(groupM,GiG,HiG,mul1r) // !repr_mxM // rGK scalar_mxC.
Qed.

(* Isaacs' 2.27b *)
Canonical Structure ccenter_group f := Group (ccenter_group_set f).

(* Isaacs' 2.27b *)
Lemma ccenter_sub : forall f, ccenter f \subset G.
Proof.
move=> f; case: (boolP (is_char G f))=> Hf; last first.
  rewrite /ccenter (negPf Hf).
  by apply/subsetP=> g; rewrite inE; move/eqP->; exact: group1.
by rewrite /ccenter Hf; apply/subsetP=> g; rewrite inE; case/andP.
Qed.

Lemma cker_center_normal : forall f, cker G f <| ccenter f.
Proof.
move=> f; apply: normalS (cker_normal _ _); last by exact: ccenter_sub.
apply/subsetP=> g; rewrite /= /cker /ccenter.
case E1: (is_char _ _)=> //; rewrite !inE.
case/andP=> HH; move/eqP->; rewrite HH normC_pos ?eqxx //.
apply: posC_isNatC; exact: (isNatC_character1 (Character (idP E1))).
Qed.

Lemma ccenter_normal : forall f, ccenter f <| G.
Proof.
move=> f; apply/normalP; split; first exact: ccenter_sub.
move=> g InG; apply/setP=> h.
rewrite /ccenter; case E1: (is_char G f); last by rewrite conjs1g.
have F1 := character_in_cfun (Character (idP E1)).
rewrite !inE; apply/imsetP/idP.
  case=> l; rewrite inE; case/andP=> LiG Hn ->.
  by rewrite groupJ // (cfunJ F1) ?Hn.
case/andP=> HiG NcH; exists (h ^(g^-1))%g; last first.
  by rewrite -conjgM mulVg conjg1.
by rewrite inE groupJ ?groupV // (cfunJ F1) ?groupV.
Qed.

(* Isaacs' 2.27c *)
Lemma ccenter_restrict : forall (f : character G),
  exists2 lambda : character [group of ccenter f],
     clinear  [group of ccenter f] lambda & 
     'Res[ccenter f] f =  (f 1%g) *: (lambda : cfun _ _).
Proof.
move=> f.
case: (charRE f)=> [] [|n] [rG Hf].
  exists (character1 [group of ccenter f]).
    by rewrite /clinear is_char_character character1E group1 eqxx.
  by apply/cfunP=> g; rewrite -Hf !cfunE !(flatmx0 (rG _)) mxtrace0 !mulr0 mul0r.
pose repr g := ((rG g 0 0)%:M : 'M_(1,1)).
have Mx: mx_repr  [group of ccenter f] repr.
  split=> [| g h]; first by rewrite /repr repr_mx1 mxE eqxx.
  rewrite /= -Hf  char_rcenterP /rcenter !inE.
  case/andP=> InG; case/is_scalar_mxP=> k1 Hk1.
  case/andP=> InH; case/is_scalar_mxP=> k2 Hk2.
  by rewrite /repr repr_mxM // Hk1 Hk2 -!scalar_mxM !mxE !mulr1n.
exists (Character (is_char_char_of_repr (MxRepresentation Mx))).
  by rewrite /clinear is_char_character cfunE group1 mul1r repr_mx1 mxtrace1 eqxx.
apply/cfunP=> g; rewrite !cfunE /=.
case: (boolP (g \in _))=> InG; last by rewrite !mul0r mulr0.
rewrite !mul1r.
move: InG; rewrite -Hf char_rcenterP /rcenter !inE.
case/andP=> InG; case/is_scalar_mxP=> k1 Hk1.
rewrite /repr !cfunE InG group1 Hk1 repr_mx1 !mul1r !mxE.
by rewrite  !mxtrace_scalar !mulr1n mulr_natl.
Qed.

Lemma character0_eq0 : forall f : character G,  (f == 0%CH) = (f 1%g == 0).
Proof.
move=> f; apply/eqP/eqP=> [->|HH]; first by rewrite cfunE.
apply/val_eqP=> /=; move: HH; case: (charRE f)=> n [rG <-].
rewrite !cfunE group1 repr_mx1 mxtrace1 mul1r; move/eqP; rewrite -(eqN_eqC _ 0).
move=>HH; move: rG; rewrite (eqP HH)=> rG; apply/eqP.
by apply/cfunP=> g; rewrite !cfunE [rG _]flatmx0 mxtrace0 mulr0.
Qed.

Lemma cker_char1: forall (G : {group gT}) (f : character G) g, g \in cker G f -> f g = f 1%g.
Proof.
by move=> G1 f g; rewrite /cker is_char_character inE; case/andP=> _; move/eqP.
Qed.

(* Isaacs' 2.27d *)
Lemma ccenter_cyclic: forall (f : character G), f != 0%CH -> cyclic (ccenter f/cker G f)%g.
Proof.
move=> f Hf; pose G' := [group of ccenter f].
have F1 : f 1%g != 0 by rewrite -character0_eq0.
case: (ccenter_restrict f)=> l H1l H2l.
have F2: cker G f = cker G' ('Res[ccenter f] f)%CH .
   rewrite /cker (is_char_restrict (ccenter_sub _)) is_char_character //.
   apply/setP=> g; rewrite !inE.
   rewrite /G' /= /ccenter is_char_character !cfunE !inE.
   rewrite group1 /=; case E1: (g \in G)=> //=.
   rewrite [normC (f 1%g)]normC_pos ?(posC_isNatC,isNatC_character1) // eqxx.
   case: (normC _ =P _); first by rewrite !mul1r.
   case: (_ =P _)=> // HH HH1; case: HH1; rewrite HH.
   by rewrite normC_pos ?(posC_isNatC,isNatC_character1).
have F3 : cker G' ('Res[ccenter f] f)%CH = cker G' l.
   rewrite /cker !(is_char_character, (is_char_restrict (ccenter_sub _))) //.
   apply/setP=> g; rewrite !inE H2l !cfunE.
   by congr (_ && _); apply/eqP/eqP=>[|-> //]; move/(mulfI F1).
rewrite F2 F3; pose m (u : coset_of (cker G' l)) := l (repr u).
have Fm : forall C,  C  \in (ccenter f / cker G' l)%g ->
         exists c, [/\ c \in 'N(cker G' l), c \in  ccenter f, (C =  coset (cker G' l) c)%g & m C = l c].
  move=> C; case/imsetP=> /= c; rewrite inE; case/andP=> H1c H2c ->.
  exists c; rewrite H1c H2c; split=> //.
  rewrite /m /= !val_coset //.
  case: repr_rcosetP=> g InG.
  rewrite !(clinearM H1l) ?(cker_char1 InG, clinear1 H1l, mul1r) //.
  by rewrite (subsetP (normal_sub (cker_center_normal _))) // F2 F3.
apply: (@field_mul_group_cyclic _ _ _ m).
  move=> /= C1 C2; case/Fm=> c1 [H1c1 H2c1 -> ->]; case/Fm=> c2 [H1c2 H2c2 -> ->].
  rewrite /m /= !val_coset // rcoset_mul //.
  case: repr_rcosetP=> k InK.
  rewrite !(clinearM H1l) ?groupM // ?(cker_char1 InK, clinear1 H1l, mul1r) //.
  by rewrite (subsetP (normal_sub (cker_center_normal _))) // F2 F3.
move=> C; case/Fm=> c [H1c H2c -> ->].
split.
  by move=> HH; rewrite coset_id // char_ckerE inE HH (clinear1 H1l) eqxx andbT.
move/(coset_idr H1c).
rewrite /= char_ckerE inE (clinear1 H1l)  //.
by case/andP=> _ HH1; apply/eqP.
Qed.

(* Isaacs' 2.27e *)
Lemma ccenter_subset_center : forall f : character G, 
  (ccenter f/cker G f)%g \subset 'Z(G/cker G f)%g.
Proof.
move=> f; apply/subsetP.
move=> C1; case/imsetP=> g; rewrite inE; case/andP=> H1g H2g -> /=.
apply/centerP; split.
  by apply: mem_quotient; apply: (subsetP (ccenter_sub f)).
move=> C2; case/imsetP=> h; rewrite inE; case/andP=> H1h H2h -> /=.
apply/val_eqP; apply/eqP=> /=.
rewrite !val_coset //= !rcoset_mul //.
apply: rcoset_transl; apply/rcosetP; exists [~ g^-1, h^-1]; last first.
  exact: commgCV.
have InG: g \in G by apply: (subsetP (ccenter_sub f)).
case: (charRE f)=> n [rG HrG].
rewrite -HrG /= char_rkerP inE ?(groupR,groupV) //.
rewrite mul1mx !repr_mxM ?(invgK,groupR,groupJ,groupM,groupV)//.
move: H2g; rewrite -HrG char_rcenterP inE; case/andP=> _.
case/is_scalar_mxP=> k Hk.
rewrite !mulmxA Hk -scalar_mxC -Hk repr_mxK // -repr_mxM ?groupV//.
by rewrite mulgV repr_mx1 eqxx.
Qed.

(* Isaacs' 2.27f*)
Lemma ccenter_eq_center : forall i : irr G, 
  (ccenter i/cker G i)%g ='Z(G/cker G i)%g.
Proof.
move=> i; apply/eqP; rewrite eqEsubset.
rewrite ccenter_subset_center.
apply/subsetP=> C1; case: (@cosetP _ _ C1)=> g Hg -> HH.
have InG: g \in G.
  move: HH; rewrite inE; case/andP.
  case/imsetP=> h; rewrite inE; case/andP=> H1h H2h /=.
  move/(rcoset_kercosetP Hg H1h)=> //.
  case/rcosetP=> l H1l -> _; rewrite groupM //.
  by rewrite (subsetP (cker_sub _ i)) //.
apply: mem_quotient.
rewrite /= char_rcenterP /rcenter inE InG.
have F1:  mx_absolutely_irreducible (irr_repr (socle_of_irr i)).
  by apply: groupC; apply: socle_irr.
apply: (mx_abs_irr_cent_scalar F1).
apply/subsetP=> h InH.
have Hh: h \in 'N(cker G i).
  by apply: (subsetP (normal_norm (cker_normal G i))).
set rGi := irr_repr _.
rewrite inE InH -{1}repr_mxM //.
have F2 : (g * h)%g  \in (coset (cker G i) g * coset (cker G i) h)%g.
  apply/imset2P=> /=.
  by exists (g : gT) (h : gT)=> //;
     rewrite val_coset //; apply/rcosetP; exists 1%g; rewrite // mul1g.
move: F2; case/centerP: HH=> _; move/(_ (coset (cker G i) h))->; last first.
  by apply: mem_quotient.
case/imset2P=> g1 h1.
rewrite val_coset //; case/rcosetP=> g2 Hg2 ->.
rewrite val_coset //; case/rcosetP=> h2 Hh2 -> ->.
rewrite !repr_mxM ?groupM // ?(subsetP (cker_sub G i)) //.
have: g2 \in rker rGi by rewrite -char_rkerP.
rewrite inE; case/andP=> _; rewrite {1}mul1mx; move/eqP->; rewrite {1}mul1mx.
have: h2 \in rker rGi by rewrite -char_rkerP.
rewrite inE; case/andP=> _; rewrite {1}mul1mx; move/eqP->; rewrite {1}mul1mx.
by rewrite eqxx.
Qed.

Lemma center_sub_quo : forall (M N : {group gT}),
  N <| M -> ('Z(M)/N \subset 'Z(M/N))%g.
Proof.
move=> M N NM; apply/subsetP=> C.
case/imsetP=> g; rewrite inE; case/andP=> H1g H2g -> /=.
apply/centerP; split.
  by apply: mem_quotient; apply: (subsetP (center_sub M)).
move=> C1; case/imsetP=> h; rewrite inE; case/andP=> H1h H2h -> /=.
apply/val_eqP=> /=; apply/eqP.
rewrite !val_coset // !rcoset_mul //.
by case/centerP: H2g=> InG; move/(_ _ H2h); rewrite /commute => ->.
Qed.
  
(* This is 2.28 *)
Lemma center_bigcap : 'Z(G) = \bigcap_(i : irr G) ccenter i.
Proof.
apply/setP=> g; apply/idP/idP=> [InG|].
  have InG': g \in G by apply: (subsetP (center_sub G)).
  apply/bigcapP=> i _.
  have: coset (cker G i) g \in (ccenter i/(cker G i))%g.
    rewrite ccenter_eq_center.
    apply: (subsetP ( center_sub_quo (cker_normal _ _))).
    by apply: mem_quotient.
  case/imsetP=> h; rewrite inE; case/andP=> H1h H2h /=.
  move/val_eqP; rewrite /= !val_coset //; last first.
    by apply: (subsetP (normal_norm (cker_normal G i))).
  move=> HH; move: InG'.
  have: g \in  cker_group G i :* g.
    by apply/rcosetP; exists (1%g); rewrite ?(group1,mul1g).
  rewrite (eqP HH); case/rcosetP=> l /= InL -> InG'.
  have InL': l \in G by apply: (subsetP (cker_sub G i)).
  have InH: h \in G by apply: (subsetP (ccenter_sub i)).
  rewrite char_rcenterP inE InG'.
  move: InL; rewrite char_rkerP inE mul1mx {1}repr_mxM //.
  case/andP=> InL; move/eqP->; rewrite mul1mx.
  by move: H2h; rewrite char_rcenterP inE; case/andP.
move/bigcapP=> HH.
have InG: g \in G.
  by apply: (subsetP (ccenter_sub (irr1 G))); apply: HH.
apply/centerP; split=> //.
move=> h InH; apply/commgP.
suff: [~ g, h] \in 1%G by rewrite inE.
rewrite -(cker_all1 G); apply/bigcapP=> i _.
rewrite char_rkerP inE groupR // mul1mx.
set rGi := irr_repr _.
rewrite !repr_mxM ?(groupV,groupJ,groupM) //.
have: is_scalar_mx (rGi g).
  by move: (HH i is_true_true); rewrite char_rcenterP inE InG.
case/is_scalar_mxP=> k Hk; rewrite Hk -scalar_mxC {1}mulmxA {1}mulmxA.
rewrite -Hk andTb; apply/eqP.
  (* Too slow
rewrite  {1}(repr_mxKV rGi InH).
*)
have->: rGi (g^-1)%g *m rGi (h^-1)%g *m rGi h *m rGi g = rGi (g^-1)%g *m rGi g.
   by congr (_ *m _); apply: (repr_mxKV rGi InH).
by rewrite -repr_mxM ?groupV // mulVg repr_mx1.
Qed.
 
Lemma inner_subl: forall (H : {group gT}) (f1 f2 : cfun _ _), 
  H \subset G ->  (forall g, g \in G :\: H -> f1 g = 0) -> 
  '[f1,f2]_H = #|G : H|%:R * '[f1,f2]_G.
Proof.
move=> H f1 f2 HsG Hi; apply: sym_equal.
rewrite !inner_prodE {1}(bigID (fun x => x \in H)) /= addrC.
rewrite {1}big1=> [|j Hj]; last by rewrite Hi ?mul0r // inE andbC.
have CG := neq0GC G; have CH := neq0GC H.
apply: (mulfI CH).
rewrite add0r !mulrA -natr_mul LaGrange // !divff // !mul1r.
apply: eq_bigl=> g; rewrite andbC; case E1: (g \in H)=> //.
by rewrite (subsetP HsG).
Qed.

(* This is 2.29 *)
Lemma crestrict_sub_inner_bound : forall (H : {group gT}) f,
  H \subset G ->  '['Res[H] f,'Res[H] f]_H <= #|G : H|%:R * '[f,f]_G ?= iff
      (forallb g : gT, (g \in G:\:H) ==> (f g == 0)).
Proof.
move=> H f HsG; rewrite inner_subl // => [|i]; last first.
  by rewrite cfunE inE; case/andP; move/negPf->; rewrite mul0r.
apply/leCifP; case: (boolP (forallb b:_, _)).
  move/forall_inP=> Hi; apply/eqP.
  congr(_ * _); rewrite !inner_prodE; congr (_ * _); apply: eq_bigr=> g InG.
  rewrite cfunE; case E1: (g \in H); rewrite (mul0r,mul1r) //.
  have: g \in G:\:H by rewrite inE E1.
  by move/Hi; move/eqP->; rewrite !mul0r.
rewrite negb_forall_in; case/existsP=> g; case/andP=> H1g H2g.
rewrite ltC_sub -mulr_subr sposC_mul //.
  by rewrite -(ltn_ltC 0) indexg_gt0.
have InG: g \in G by apply: (subsetP (subsetDl G H)).
rewrite ['['Res[_] _,_]_G]inner_prodE (bigD1 g) //=.
rewrite inner_prodE (bigD1 g) //=.
rewrite -mulr_subr sposC_mul //.
  by rewrite sposC_inv -(ltn_ltC 0) cardG_gt0.
rewrite -addrA sposC_addr //.
  by rewrite ltCE posC_pconj andbT mulf_neq0 // conjC_eq0.
have: g \notin H by move: H1g; rewrite inE; case/andP.
rewrite cfunE; move/negPf->; rewrite !mul0r add0r.
rewrite -sumr_sub posC_sum // => i; case/andP=> _;case/andP=> HH _.
by rewrite !cfunE; case: (_ \in _); 
   rewrite !(mul0r,mul1r,subrr,subr0, (posC_nat 0),posC_pconj).
Qed.

(* This is 2.30 *)
Lemma irr1_bound : forall (i : irr G),
  (i 1%g)^+2 <= #|G:ccenter i|%:R ?= iff
      (forallb g : gT, (g \in G:\:ccenter i) ==> (i g == 0)).
Proof.
move=> i.
pose H := [group of (ccenter i)].
have F1 : H \subset G by apply: (ccenter_sub _).
rewrite -[_%:R]mulr1.
have: is_irr G i by apply: is_irr_irr.
rewrite char_irreducibleE; move/eqP=>HH; rewrite -{2}HH.
suff{HH}->: (i 1%g)^+2 = '['Res[H] i,'Res[H] i]_H.
  by apply: (@crestrict_sub_inner_bound H i F1).
case (@ccenter_restrict (character_of_irr i))=> l Hl ->.
rewrite inner_prodZ -inner_prodbE linearZ /= inner_prodbE.
move: (clinear_is_irr Hl).
rewrite char_irreducibleE; move/eqP->.
rewrite ?expr2 isNatC_conj; last by apply: isNatC_character1.
by rewrite /GRing.scale /= mulr1.
Qed.
  
(* This is 2.31 *)
Lemma irr1_abelian_bound : forall (i : irr G),
  abelian (G/ccenter i) -> (i 1%g)^+2 = #|G:ccenter i|%:R.
Proof.
move=> i AbGc; apply/eqP; rewrite irr1_bound.
apply/forall_inP=> g; rewrite inE; case/andP=> NInC GiG.
have GiN := subsetP (normal_norm (cker_normal G i)) _ GiG.
pose CC := [group of ccenter i].
have: coset (cker G i) g \notin (CC/cker G i)%G.
  apply/negP; case/imsetP=> /= h; rewrite inE; case/andP=> HiN HiC.
  have HiG: h \in G by apply: (subsetP (ccenter_sub i)).
  move/rcoset_kercosetP; move/(_ GiN HiN); case/rcosetP=> u Hu Hg.
  have UiG: u \in G by apply: (subsetP (cker_sub G i)).
  case/negP: NInC; rewrite Hg.
  by rewrite irr_ccenterE ?groupM // char_ckerMr // -irr_ccenterE.
rewrite  /= (ccenter_eq_center i) => H.
case: (boolP (existsb h: gT, (h \in G) && ([ ~ g, h] \notin cker G i))); last first.
  rewrite negb_exists_in; move/forall_inP=> HH.
  case/negP: H; apply/centerP; split=> /=.
    by apply: mem_quotient.
  move=> N; case: (@cosetP _ _ N)=> h H1h -> H2h.
  apply/commgP.
  suff<-: coset (cker G i) [~ g,h] = 1%g.
    by rewrite /commg /conjg !morphM ?(groupM,groupV) // !morphV.
  have HiG: h \in G.
    case/imsetP: H2h=> l; rewrite inE; case/andP=> H1l H2l.
    move/(rcoset_kercosetP H1h H1l).
    case/rcosetP=> k Hk ->; rewrite groupM //.
    by apply: (subsetP (normal_sub (cker_normal _ i))).
  by apply: coset_id; move: (HH _ HiG); rewrite negbK.
case/existsP=> h; case/andP=> HiG CNiK.
have HiN: h \in 'N(ccenter i).
  by apply: (subsetP (normal_norm (ccenter_normal _))).
have GiNc: g \in 'N(ccenter i).
  by apply: (subsetP (normal_norm (ccenter_normal _))).
have CiC :  [~ g, h] \in ccenter i.
  apply: coset_idr; first by rewrite groupR.
  rewrite /commg /conjg !morphM ?(groupM,groupV,morphV) //=.
  suff->: commute (coset (ccenter i) g) (coset (ccenter i) h).
    by rewrite !mulgA mulgKV mulVg.
  move: AbGc; rewrite abelianE; move/subsetP.
  move/(_ _ (mem_quotient CC GiG)); move/centP.     
  by move/(_ _ (mem_quotient CC HiG)).
have: i (g * [~ g, h])%g = i (g).
  by rewrite -conjg_mulR (cfunJ (irr_in_cfun i)).
case: (charRE (character_of_irr i))=> //= n [rG HrG].
move: CiC CNiK; rewrite -!HrG char_rkerP inE mul1mx=> CiC.
have RiG: [~ g, h] \in G by rewrite groupR.
rewrite !cfunE ?RiG groupM ?(GiG,RiG,group1,mul1r) // repr_mxM //.
move: CiC; rewrite char_rcenterP // inE RiG; case/is_scalar_mxP=> k ->.
rewrite scalar_mxC mul_scalar_mx mxtraceZ andTb.
case: (boolP (\tr(rG g) == 0))=> // HH HH1 HH2.
case/eqP: HH1.
apply/matrixP=> i1 j1; rewrite !mxE; case: eqP=> // _.
by apply: (mulIf HH); rewrite mul1r.
Qed.

Lemma cfaithfulE : forall f, cfaithful G f = (cker G f \subset 1%G).
Proof. by []. Qed.

(* 2.32a *)
Lemma irr_faithful_center: forall i : irr G,
  cfaithful G i -> cyclic ('Z(G)).
Proof.
move=> i; move/trivgP=> HH.
rewrite (isog_cyclic (isog_center (quotient1_isog G))) -HH.
rewrite /= -ccenter_eq_center.
apply: ccenter_cyclic.
apply/negP; move/eqP;move/val_eqP=> /=; move/eqP.
move/cfunP; move/(_ 1%g)=> HH1.
by case/negP: (irr1_neq0 i); rewrite HH1 cfunE.
Qed.

(* 2.32b *)
Lemma pgroup_cyclic_faithful: forall p : nat, 
  p.-group G -> cyclic 'Z(G) -> exists i : irr G, cfaithful G i.
Proof.
 (* Lengthly Proof!! *)
move=> p PG CZG.
case: (boolP (G == 1%g :> {set _}))=> [HG1|DG].
  exists (irr1 G); rewrite /cfaithful /=.
  by move/eqP: HG1<-; exact: cker_sub.
case/(pgroup_pdiv PG): (DG) => Pp Dp [m Hm].
case: (boolP (forallb i : irr G, cker G i != 1%g)); last first.
  rewrite negb_forall; case/existsP=> i; rewrite negbK=> Hi.
  by exists i; apply/trivGP; apply/eqP.
move/forallP=> Hi.
case/cyclicP: CZG=> b Zb.
have: 'Z(G) != 1%g.
  by apply/eqP=> HH; case/eqP: DG; apply: (trivg_center_pgroup PG).
case/(pgroup_pdiv (pgroupS (center_sub _) PG))=> _ Zp1 [m1 Hm1].
pose Z := <[(b^+(p^m1)%N)%g]>.
have CZ: #|Z| = p.
  have ->: p = (p ^ (m1.+1 - m1))%N by rewrite subSnn expn1.
  by rewrite -orderE; apply: orderXexp; rewrite -Hm1 /= Zb orderE.
suff: Z \subset 1%G.
  move/subset_leq_card; rewrite CZ cards1.
  by move: Pp; case: (p)=> // [[|]].
rewrite -(cker_all1 G); apply/bigcapsP=> i _.
suff: forall N : {group gT}, N <| G -> N != 1%G -> Z \subset N.
  by apply; [apply: cker_normal | apply: Hi].
move=> {i Hi}N NnG DN.
have NsG:  N :&: 'Z(G) \subset G by apply: subIset; rewrite (normal_sub NnG).
have: N :&: 'Z(G) != 1%g.
  apply/eqP=> DNZ.
  case: (pgroup_pdiv (pgroupS (normal_sub NnG) PG) DN)=> _ Dp' [m' Hm'].
  move: (Pp).
  have Act : [acts G, on N | 'J] by rewrite astabsJ normal_norm.
  have DOr : forall x,  x \in N ->
       #|orbit 'J G x| != 1%N -> (p %| #|(orbit 'J G x)|)%N.  
    move=> g GiN; rewrite orbitJ -index_cent1; move: (dvdn_indexg G 'C_G[g]).
    rewrite Hm; case/dvdn_pfactor=> // [] [|m2] Hm2-> //.
    by rewrite expnS dvdn_mulr.
  move: Dp'; rewrite -(acts_sum_card_orbit Act).
  rewrite (bigID (fun i : {set _} => #|i| != 1%N)) dvdn_addr; last first.
    apply big_prop=> [|x y Hx Hy|]; rewrite ?(dvdn0,dvdn_addr) //=.
    by move=> i; case/andP; case/imsetP=> g GiG -> HH; exact: DOr.
  rewrite (bigD1 1%g) ?(cards1,andbT) //=; last first.
    by apply/imsetP; exists 1%g; rewrite ?group1 // orbitJ (class1g (group1 _)).
  rewrite big1 /=; first by rewrite dvdn1; move/eqP->.
  move=> i; do 2 case/andP; case/imsetP=> g GiN ->.
  rewrite negbK orbitJ -index_cent1 indexg_eq1 classG_eq1=> H1g H2g.
  move/eqP: DNZ; rewrite -[_==_]negbK; case/negP.
  apply/trivgPn; exists g=> //.
  have GiG : g \in G by apply: (subsetP (normal_sub NnG)).
  rewrite inE GiN; apply/centerP; split=> // y YiG.
  by case/subcent1P: (subsetP H1g _ YiG).
case/(pgroup_pdiv (pgroupS NsG PG))=> _ HH [m2 Hm2].
case: (Cauchy Pp HH)=> u Hu Hv.
have: u \in <[b]> by rewrite -Zb; move: Hu; rewrite inE; case/andP.
case/cyclePmin=> m3 Hm3 H1u.
move: (expg_order  u); rewrite Hv H1u -expgn_mul.
move/eqP; rewrite -order_dvdn.
move: Hm1; rewrite /= Zb /= -orderE => ->.
rewrite expnSr dvdn_pmul2r ?prime_gt0 //.
case/dvdnP=> k Hk.
have <-: <[u]> = Z.
  apply/eqP; rewrite eqEcard -orderE Hv CZ leqnn cycle_subG.
  by rewrite H1u Hk mulnC expgn_mul mem_cycle.
by rewrite cycle_subG (subsetP (subsetIl _ 'Z(G))).
Qed.

End Center.

Section Induced.

Variable (gT : finGroupType) (G H : {group gT}).

Definition induced (f : cfun gT algC) := cfun_of_fun
 (fun g =>  #|H|%:R^-1 * \sum_(x | x \in G) f (g ^ x)).

Local Notation "'Ind f" := (induced f) (at level 24).

Lemma induced_in_cfun : forall (f : cfun gT algC),
  H \subset G -> f \in 'CL[algC](H) -> 'Ind f \in 'CL[algC](G).
Proof.
move=> f HsG Hf; apply/cfun_memP; split=> [g Hg|g h GiG HiG].
  rewrite !cfunE big1 ?mulr0 // => h HiG.
  rewrite (cfun0 Hf) //.
  apply/negP; move/(subsetP HsG)=> GHiH; case/negP: Hg.
  by rewrite -[g]conjg1 -[1%g](mulgV h) conjgM groupJ // groupV.
rewrite !cfunE; congr (_ * _).
rewrite (reindex (fun x => h^-1 * x)%g) //=; last first.
  by exists (mulg h)=> l; rewrite mulgA (mulgV,mulVg) mul1g.
apply: eq_big=> [l|l _]; first by rewrite groupMl // groupV.
by rewrite -conjgM mulgA mulgV mul1g.
Qed.

Lemma induced1 : forall f, H \subset G -> ('Ind f) 1%g = #|G:H|%:R * f 1%g.
Proof.
move=> f HsG; rewrite cfunE (eq_bigr (fun _ => f 1%g)).
  rewrite sumr_const -[(f _) *+ _]mulr_natl mulrA -(LaGrange HsG).
  by rewrite natr_mul mulrA mulVf ?mul1r // neq0GC.
by move=> i; rewrite conj1g.
Qed.

(* Isaacs' 5.2 *)
Lemma freciprocity : forall f1 f2,
  H \subset G -> f1 \in 'CL[algC](H) -> f2 \in 'CL[algC](G)->
   '[f1,'Res[H] f2]_H = '['Ind f1,f2]_G.
Proof.
move=> f1 f2 HsG F1iC F2iC.
apply: sym_equal; rewrite !inner_prodE.
pose f3 i :=  #|H|%:R^-1 * \sum_(j \in G) f1 (i ^j) * (f2 i)^*.
rewrite (eq_bigr f3) =>[/=|g GiG]; rewrite {}/f3; last first.
  by rewrite cfunE -mulrA -mulr_suml.
rewrite mulr_sumr exchange_big /=.
pose f3 j :=  \sum_(i \in G) f1 (i ^ j) * (f2 (i ^ j))^*.
rewrite (eq_bigr f3) =>[/=|g GiG]; rewrite {}/f3; last first.
  by apply: eq_bigr=> h HiG; rewrite (cfunJ F2iC).
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

Lemma induced_conjC : forall f, ('Ind f)^*%CH = 'Ind (f^*)%CH.
Proof.
move=> f; apply/cfunP=> g.
rewrite !cfunE rmorphM conjC_inv conjC_nat; congr (_ * _).
rewrite rmorph_sum; apply: eq_bigr=> h HiG.
by rewrite cfunE.
Qed.

Lemma is_char_induced : forall (f : character H),
   H \subset G -> is_char G ('Ind f).
Proof.
move=> f HsG; have IiC := induced_in_cfun HsG (character_in_cfun f).
apply/andP; split=> //; apply/allP=> i _.
rewrite ncoord_inner_prod // -freciprocity ?(character_in_cfun,irr_in_cfun) //.
rewrite (inner_prod_char f (irr_rest HsG i)).
by apply: isNatC_sum => j _; rewrite isNatC_mul // char_isNatC_ncoord.
Qed.

Definition character_induced (f : character H) (HsG : H \subset G) :=
  Character (is_char_induced f HsG).

Definition irr_induced (i : irr H) (HsG : H \subset G) :=
  character_induced (character_of_irr i) HsG.

Lemma is_comp_irr_restrict : forall i : irr H,
  H \subset G -> exists j : irr G, is_comp i ('Res[H] j).
Proof.
move=> i HsG.
case: (boolP (irr_induced i HsG == character0 G))=> [HH|].
  have: irr_induced i HsG 1%g == 0 by rewrite (eqP HH) cfunE.
  rewrite /= (induced1 i HsG)=> /=.
  rewrite mulf_eq0 (negPf (irr1_neq0 _)) orbF -(eqN_eqC _ 0).
  by case: indexg (indexg_gt0 G H).
case/is_comp_neq0=> j Hj; exists j.
pose cr := irr_rest HsG j.
rewrite is_compE  ncoord_inner_prod ?(character_in_cfun cr) //.
rewrite (inner_prod_charC cr) /=.
rewrite freciprocity ?irr_in_cfun //.
by rewrite -ncoord_inner_prod // ?induced_in_cfun // irr_in_cfun.
Qed.

Lemma is_conjugate_induced : forall (f1 f2 : cfun gT algC),
   H <| G ->  f1 \in 'CL[algC](H) -> f2 \in 'CL[algC](H) ->  
   is_conjugate G f1 f2 -> 'Ind f1 = 'Ind f2.
Proof.
move=> f1 f2 HnG Cf1 Cf2; case/is_conjugateP=> g GiG Jeq.
apply/cfunP=> h; case: (boolP (h \in G))=> [HiG| HniG]; last first.
rewrite !(cfun0 (induced_in_cfun _ _)) ?(normal_sub HnG) //.
rewrite Jeq !cfunE; congr (_ * _).
rewrite (reindex (mulg^~ g^-1%g)); last first.
  by exists (mulg^~ g)=> h1 _; rewrite -mulgA (mulgV,mulVg) mulg1.
apply: eq_big=> [|h1 H1iG]; last by rewrite cfun_conjE conjgM.
by move=> h1 /=; rewrite groupMr // groupV.
Qed.

End Induced.

Notation "''Ind[' G , H ]  f " := (induced G H f) (at level 24).

Section Inertia.

Variable gT : finGroupType.
Variable (G H : {group gT}).

Definition inertia (i : irr H) := 
  if H <| G then [set g \in G | cfun_conj i g == i] else 1%g.

Lemma group_set_inertia : forall i, group_set (inertia i).
Proof.
move=> i; rewrite /inertia; case: (boolP (H <| G))=> HnG; last first.
  by exact: group_set_one.
apply/andP; split.
  rewrite inE group1; apply/eqP; apply/cfunP=> g.
  by rewrite cfunE invg1 conjg1.
apply/subsetP=> p; case/imset2P=> g1 g2; rewrite !inE.
case/andP=> G1iG CF1; case/andP=> G2iG CF2 ->; rewrite groupM //.
apply/eqP; apply/cfunP=> h; rewrite cfunE invMg conjgM.
move/cfunP: (eqP CF1); move/(_ (h^(g2^-1))); rewrite cfunE => ->.
by move/cfunP: (eqP CF2); move/(_ h); rewrite cfunE => ->.
Qed.

Canonical Structure inertia_group i := Group (group_set_inertia i).

Lemma inertia_sub : forall i, inertia i \subset G.
Proof. 
move=> i; apply/subsetP=> g.
rewrite /inertia; case: (boolP (H <| G))=> HnG; last first.
  by apply: (subsetP (sub1G G)). 
by rewrite inE; case/andP.
Qed.

Lemma cfun_conj_eqE : forall (i : irr H) (x y : gT),
 H <| G -> x \in G -> y \in G ->
 (i^x == i^y)%CH = (y \in (inertia i :* x)).
Proof.
move=> i x y HnG XiG YiG; rewrite /inertia HnG.
apply/eqP/rcosetP=> [Hx|]; last first.
  case=> g; rewrite inE; case/andP=> GiG; move/eqP=> CCi ->.
  apply/cfunP=> h; rewrite cfunE -{1}CCi cfunE -conjgM.
  by rewrite cfun_conjE invMg.
exists (y * x^-1)%g; last by rewrite -mulgA mulVg mulg1.
rewrite inE !(groupM,groupV) //; apply/eqP; apply/cfunP=> g.
rewrite cfunE invMg invgK conjgM.
move/cfunP: Hx; move/(_ (g^x)); rewrite !cfun_conjE => <-.
by rewrite -conjgM mulgV conjg1.
Qed.

Lemma inertia_center : forall i, H <| G -> 'Z(G) \subset (inertia i).
Proof.
move=> i HnG; rewrite /inertia HnG.
apply/subsetP=> g; case/centerP=> GiG Cg; rewrite inE GiG.
apply/eqP; apply/cfunP=> h; rewrite cfunE.
case: (boolP (h \in H))=> [HiG|HniG].
  rewrite !conjgE invgK mulgA Cg ?(subsetP (normal_sub HnG)) //.
  by rewrite -mulgA mulgV mulg1.
rewrite !(cfun0 (irr_in_cfun _)) //.
by rewrite memJ_norm // (subsetP (normal_norm HnG)) // groupV.
Qed.

Lemma subset_inertia : forall (i : irr H), H <| G -> H \subset inertia i.
Proof.
move=> i HnG; rewrite /inertia HnG.
apply/subsetP=> h1 H1iH.
rewrite inE (subsetP (normal_sub HnG)) //.
apply/eqP; apply/cfunP=> h2; case: (boolP (h2 \in H))=> [H2iH|H2niH].
  by rewrite cfunE (cfunJ (irr_in_cfun i)) // groupV.
rewrite cfunE !(cfun0 (irr_in_cfun i)) //.
apply/negP=> HH; case/negP: H2niH.
by rewrite -(groupJr _ (groupVr H1iH)).
Qed.

(* Isaacs' 6.1.c *)
Lemma cfun_conj_inner : forall (f1 f2 : cfun gT algC) (g : gT),
 H <| G -> g \in G -> ('[f1^g,f2^g]_H = '[f1,f2]_H)%CH.
Proof.
move=> f1 f2 g HnG GiG; rewrite !inner_prodE.
congr (_ * _).
rewrite (reindex (conjg^~ g)); last first.
  by exists (conjg^~ g^-1%g)=> h; rewrite -conjgM (mulVg,mulgV) conjg1.
apply: eq_big=> [|h HiG].
  by move=> h; apply: memJ_norm; apply: (subsetP (normal_norm HnG)).
by rewrite !cfun_conjE -!conjgM mulgV conjg1.
Qed.
 
(* Isaacs' 6.1.d *)
Lemma cfun_conj_inner_rest : forall (f1 f2 : cfun _ _) (g : gT),
 H <| G -> f1 \in 'CL(G) ->  g \in G -> 
   ('['Res[H] f1,f2^g]_H = '['Res[H] f1,f2]_H)%CH.
Proof.
move=> f1 f2 g HnG CLf GiG.
rewrite -['[_,f2]_H](cfun_conj_inner _ _ HnG GiG).
rewrite !inner_prodE; congr (_ * _).
apply: eq_bigr=> h HiH; congr (_ * _); rewrite !cfunE (cfunJ CLf) ?groupV //.
  by rewrite memJ_norm // (subsetP (normal_norm HnG)) // groupV.
by apply: (subsetP (normal_sub HnG)).
Qed.

Lemma is_char_conj : forall (f : character H) g, 
  H <| G -> g \in G -> is_char H (f^g)%CH.
Proof.
move=> f g HnG GiG; case: (charRE f)=> n [rG <-].
have mx_reprj: mx_repr H (fun x => rG (x^(g^-1%g))).
  split=> [|h1 h2 H1iH H2iH]; first by rewrite conj1g repr_mx1.
  by rewrite conjMg repr_mxM ?(memJ_norm, groupV, (subsetP (normal_norm HnG))).
apply/is_charRP; exists n; exists (MxRepresentation mx_reprj).
by apply/cfunP=> h; rewrite !cfunE ?(memJ_norm, groupV, (subsetP (normal_norm HnG))).
Qed.

(* Isaac's 6.1.e *)
Definition character_conj (f : character H) g (HnG : H <| G) (GiG : g \in G) :=
  Character (is_char_conj f HnG GiG).

Definition character_conjE :
  forall (f : character H) g (HnG : H <| G) (GiG : g \in G),
    character_conj f HnG GiG = (f^g)%CH :> cfun _ _.
Proof. by move=> f g HnG GiG; apply/cfunP=> h; rewrite cfunE. Qed.

Lemma is_irr_conj : forall (i : irr H) g (HnG : H <| G) (GiG : g \in G), 
  is_irr H (character_conj (character_of_irr i) HnG GiG)%CH.
Proof.
move=> i g HnG GiG.
rewrite char_irreducibleE character_conjE cfun_conj_inner //.
by rewrite -char_irreducibleE is_irr_irr.
Qed.
 
Definition irr_conj (i : irr H) g (HnG : H <| G) (GiG : g \in G) :=
  get_irr H (character_conj (character_of_irr i) HnG GiG)%CH.

Lemma irr_conjE : forall (i : irr H) g (HnG : H <| G) (GiG : g \in G),
  irr_conj i HnG GiG = (i^g)%CH :> cfun _ _.
Proof. by move=> i g HnG GiG; rewrite get_irrE // is_irr_conj. Qed.

Lemma is_irr_inner : forall (i : irr H) g,
  H <| G -> g \in G -> '[i,(i^g)%CH]_H = (g \in inertia i)%:R.
Proof.
move=> i g HnG GiG; rewrite -(irr_conjE i HnG GiG) irr_orthonormal.
rewrite /inertia HnG.
rewrite inE GiG eq_sym /=; congr (_%:R); congr nat_of_bool.
apply/eqP/eqP=> HH; last by apply: cfun_of_irr_inj; rewrite irr_conjE.
by rewrite -(irr_conjE i HnG GiG) HH.
Qed.

End Inertia.

