(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient finalg action.
Require Import zmodp commutator cyclic center pgroup sylow.
Require Import vector algC matrix mxrepresentation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(**************************************************************************)
(*                                                                        *)
(* This file contains the basic notions of class functions                *)
(*                                                                        *)
(*  cfun gT R : the type of functions from gT to R                        *)
(*                                                                        *)
(*  (f ^* )%CH  : the conjugate function                                  *)
(*                                                                        *)
(*  'CF[R](G,A) : the vector space of class functions of G with support   *)
(*                in A                                                    *)
(*  'CF(G,A)    : the vector space of class functions of G with support   *)
(*                in A over algC                                          *)
(*  'CF(R)      : the vector space of class functions of G over R         *)
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


(* Move to fingroup and should replace card_classes_abelian in action *)
(* GG: can't move to fingroup, because sum_card_class is in action. *)
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

Lemma groupC : group_closure_field algC gT.
Proof. exact: group_closure_closed_field. Qed.

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

(* function of a fintype into a ring form a vectype *)
Section Vectype.

Variable (R : fieldType) (aT : finType).

(* Dans vector.v
   {ffun aT -> rT} avec rT : vectType R 
   mxvec (\matrix_(i < #|aT|) v2rv (f (enum_val i)))
+ vectType pour R^o
*)
Definition ffun2rv (f : {ffun aT -> R^o}) :=  \row_(i < #|aT|) f (enum_val i).

Lemma ffun2rv_is_linear : linear ffun2rv.
Proof. by move=> k /= x y; apply/rowP=> i; rewrite !mxE !ffunE. Qed.

Canonical Structure ffun2rv_linear := Linear ffun2rv_is_linear.

Lemma ffun2rv_bij : bijective ffun2rv.
Proof.
exists (fun r : 'rV_#|aT| => [ffun x => r 0 (enum_rank x)]) => [g | r].
  by apply/ffunP=> x; rewrite ffunE mxE enum_rankK.
by apply/rowP=> i; rewrite mxE ffunE enum_valK.
Qed.

Definition ffunVectMixin := VectMixin ffun2rv_is_linear ffun2rv_bij.
Canonical Structure ffunVectType := VectType R ffunVectMixin.

End Vectype.

Local Notation "{ 'vffun' x '->' y }" := (ffunVectType y x)
  (at level 0, format "{ 'vffun'  '[hv' x  '->'  y ']' }") : type_scope.

Section ClassFun.

Variable (gT : finGroupType) (R : fieldType) (G : {group gT}).

(* Un alias + phantom sur gT pas de R *) 
Inductive cfun : predArgType := ClassFun of {ffun gT -> R}.

Definition finfun_of_cfun A := let: ClassFun f := A in f.
Definition fun_of_cfun f x := finfun_of_cfun f x.
Coercion fun_of_cfun : cfun >-> Funclass.

Lemma finfun_of_cfunE: forall f x, finfun_of_cfun f x  = f x.
Proof. by []. Qed.

Definition cfun_of_fun f := locked ClassFun [ffun x => f x].

Lemma cfunE : forall f, cfun_of_fun f =1 f.
Proof. by unlock cfun_of_fun fun_of_cfun => f x; rewrite /= ffunE. Qed.

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

(* GG: this should either go in finfun, or be replaced with *)
(* pffun_on 0 A predT (val f) *)
Definition has_support (f : cfun) (A : {set gT}) :=
  forallb x: gT, (f x != 0) ==> (x \in A).

Definition base_cfun (G A : {set gT}) : seq cfun :=
  filter
    (has_support^~ A)
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

Lemma cfun2rv_is_linear : linear cfun2rv.
Proof. 
move=> k x y; rewrite -linearP; congr ffun2rv.
by apply/ffunP=> i; rewrite !ffunE !finfun_of_cfunE !cfunE.
Qed.

Canonical Structure cfun2rv_linear := Linear cfun2rv_is_linear.

Lemma cfun2rv_bij : bijective cfun2rv.
Proof.
have [f H1f H2f] := ffun2rv_bij R gT.
exists (fun x  => ClassFun (f x))=> [[g]|x]; last exact: (H2f x).
by congr ClassFun; exact: (H1f g).
Qed.

Definition cfunVectMixin := VectMixin cfun2rv_is_linear cfun2rv_bij.
Canonical Structure cfunVectType := VectType R cfunVectMixin.

Definition class_fun G  A := span (base_cfun G A).

Local Notation "'CF( G , A )" := (class_fun G A).
Local Notation "'CF( G )" := (class_fun G G).

(* Definition 
   forall x, x \notin A -> f x = 0 (ajouter A \subset G) 
   forall x y, y \in G -> f (x ^ y) = f x)
 *)
Lemma cfun_memfP : forall (A : {set gT}) (f : cfun),
  reflect 
    [/\ forall x, x \notin (A :&: G) -> f x = 0
      & forall x y, x \in G -> y \in G -> f (x ^ y) = f x]
    (f \in 'CF(G, A)).
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
  apply: memv_suml=> i Hi.
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
    (f \in 'CF(G)).
Proof. by move=> f; apply: (iffP (cfun_memfP G f)); rewrite setIid. Qed.

Lemma cfunS0 : forall A (f : cfun) x, f \in 'CF(G,A) -> x \notin A -> f x = 0.
Proof. 
move=> A f x; case/cfun_memfP=> HH _ XniA; apply: HH.
by rewrite inE (negPf XniA).
Qed.

Lemma cfun0 : forall (f : cfun) x, f \in 'CF(G) -> x \notin G -> f x = 0.
Proof. exact: cfunS0. Qed.

Lemma cfunJ : forall A (f : cfun) x y, 
   f \in 'CF(G,A) -> x \in G -> y \in G -> f (x ^ y) = f x.
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

Lemma dim_cfun : \dim ('CF(G)) = #|classes G|.
Proof.
move: (cfun_free G); rewrite /free; move/eqP->.
by rewrite base_cfun_subset ?subxx // size_map -cardE card_ord.
Qed.

End ClassFun.

Notation "''CF[' R ] ( G , A ) " := (class_fun R G A).
Notation "''CF[' R ] ( G ) " := (class_fun R G G).
Notation "''CF(' G , A ) " := 
  (class_fun (GRing.ClosedField.fieldType algC) G A).
Notation "''CF(' G ) " := 
  (class_fun (GRing.ClosedField.fieldType algC) G G).

Definition cfun_conjC (gT: finGroupType) (f : cfun gT algC) :=
  cfun_of_fun (fun h => (f h)^*).

Notation "f ^*" := (cfun_conjC f) : character_scope.

Lemma cfun_conjCE : forall gT (f : cfun gT algC) g, (f^*)%CH g = (f g)^*.
Proof. by move=> gT f g; rewrite cfunE. Qed.

Lemma cfun_conjCK: forall gT (f : cfun gT algC), (f^*^*)%CH = f.
Proof. by move=> gT f; apply/cfunP=> g; rewrite !cfunE conjCK. Qed.

Section Restrict.

Variable (gT : finGroupType).

Definition crestrict (G : {set gT}) (f : cfun gT algC) :=
    cfun_of_fun (fun g : gT => (g \in G)%:R * (f g)).

Local Notation "''Res[' G ]  f " := (crestrict G f) (at level 24).

Lemma crestrictE : forall (G : {set gT}) f, {in G, 'Res[G] f =1 f}.
Proof. by move=> G f g H; rewrite cfunE H mul1r. Qed.
 
Lemma crestrict_in_cfun : forall f (G H : {group gT}), 
  H \subset G -> f \in 'CF(G) -> 'Res[H] f \in 'CF(H).
Proof.
move=> f G H Hsub fC; apply/cfun_memP; split.
  by move=> g; rewrite cfunE; case: (_ \in _)=> //; rewrite mul0r.
move=> g h gIn hIn; rewrite !cfunE groupJ //.
by rewrite gIn (cfunJ fC) // (subsetP Hsub).
Qed.

Lemma crestrict_is_linear : forall (G : {group gT}), linear (crestrict G).
Proof.
move=> G c f1 f2; apply/cfunP=> g.
by rewrite !cfunE mulr_addr mulrCA.
Qed.

Canonical Structure crestrit_linear G :=
  Linear (crestrict_is_linear G).

Lemma crestrict_subset : 
  forall (G  H : {set gT}) (f : cfun gT algC),
  H \subset G -> 'Res[H] ('Res[G] f) = 'Res[H] f.
Proof.
move=> G H f HsG; apply/cfunP=> g.
by rewrite !cfunE; case: (boolP (_ \in _))=> [HH|]; 
   rewrite ?mul0r // (subsetP HsG) // !mul1r.
Qed.

End Restrict.

Notation "''Res[' G ]  f " := (crestrict G f) (at level 24).

Section InnerProduct.

Variable (gT : finGroupType) (G : {group gT}).

Let card_neq0 : #|G|%:R^-1 != 0 :> algC.
Proof. by rewrite invr_eq0 neq0GC. Qed.

Definition inner_prod (G : {set gT}) (f g : cfun _ _) :=
  #|G|%:R^-1 * \sum_(i \in G) f i * (g i)^*.

Local Notation "'[ u , v ]_ G":=  (inner_prod G u v) (at level 10).
(* format *)

Lemma inner_prodE: forall (f g : cfun _ _),
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

Lemma inner_prod0l : forall f, '[0,f]_G = 0.
Proof.
move=> f.
rewrite inner_prodE big1 ?mulr0 // => i.
by rewrite cfunE mul0r.
Qed.

Lemma inner_prod0r : forall f, '[f,0]_G = 0.
Proof.
move=> f.
rewrite inner_prodE big1 ?mulr0 // => i.
by rewrite cfunE conjC0 mulr0.
Qed.

Lemma inner_prod0 : forall f : cfun _ _, 
  f \in 'CF(G) -> ('[f, f]_G == 0) = (f == 0).
Proof.
rewrite /=.
move=> f Hf; apply/eqP/eqP=> Hp; last first.
  by rewrite Hp /inner_prod big1 ?mulr0 // => i _; rewrite !cfunE mul0r.
apply/cfunP=> g; rewrite cfunE.
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

Lemma inner_prodZ : forall k f g, '[f, k *: g]_G = k^* * '[f,g]_G.
Proof.
move=> k f g; rewrite /inner_prod.
rewrite mulrCA; congr (_ * _).
rewrite -mulr_sumr; apply: eq_bigr=> i _.
by rewrite !cfunE rmorphM mulrCA.
Qed.

Lemma cfun_conjC_inner : forall f1 f2 : cfun gT algC,
 ('[f1^*,f2^*]_G)%CH = ('[f1,f2]_G)^*.
Proof.
move=> f1 f2; rewrite !inner_prodE rmorphM conjC_inv conjC_nat.
congr (_ * _); rewrite (big_morph _ (rmorphD conjC) conjC0); apply: eq_bigr.
by move=> g GiG; rewrite !cfunE rmorphM.
Qed.

End InnerProduct.

Notation "'[ u , v  ]_ G":=  (inner_prod G u v) (at level 10).

Section Coset.

Variable (gT : finGroupType).

Implicit Type G : {group gT}.

Definition qfun_of_cfun (N: {set gT}) (f : cfun gT algC) :=
  cfun_of_fun (fun x : coset_of N => f (repr x)).

Local Notation "f '/' N" := (qfun_of_cfun N f) : character_scope.

Definition cfun_of_qfun (N: {set gT}) (f : cfun (coset_groupType N) algC) :=
  cfun_of_fun (fun x : gT => (x \in 'N(N))%:R * f (coset N x)).

Local Notation " f '^()'" := (cfun_of_qfun f) (at level 2) : character_scope.

Lemma cfunqE : forall (N : {group gT}) f x,
 x \in 'N(N) -> (f ^())%CH x = f (coset N x).
Proof. by move=> N f x InG; rewrite !cfunE InG // mul1r. Qed.

End Coset.

Notation "f '/' N" := (qfun_of_cfun N f) : character_scope.
Notation " f '^()'" := (cfun_of_qfun f) (at level 2) : character_scope.


Section Induced.

Variable (gT : finGroupType).

Definition cinduced  (G H : {set gT}) (f : cfun gT algC) := cfun_of_fun
 (fun g =>  #|H|%:R^-1 * \sum_(c | c \in G) f (g ^ c)).

Local Notation "'Ind[ G , H ] f" := (cinduced G H f) (at level 24).
Variable (G H : {group gT}).

Lemma cinduced_in_cfun : forall (f : cfun gT algC),
  H \subset G -> f \in 'CF(H) -> 'Ind[G,H] f \in 'CF(G).
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

Lemma cinduced1 : forall f, 
  H \subset G -> ('Ind[G,H] f) 1%g = #|G:H|%:R * f 1%g.
Proof.
move=> f HsG; rewrite cfunE (eq_bigr (fun _ => f 1%g)).
  rewrite sumr_const -[(f _) *+ _]mulr_natl mulrA -(LaGrange HsG).
  by rewrite natr_mul mulrA mulVf ?mul1r // neq0GC.
by move=> i; rewrite conj1g.
Qed.

Lemma cinduced_is_linear : linear (cinduced G H).
Proof.
move=> c f1 f2; apply/cfunP=> g.
rewrite !cfunE mulrCA -mulr_addr.
rewrite -[c * _]mulr_sumr -big_split; congr (_ * _).
by apply: eq_bigr=> h HiG; rewrite !cfunE.
Qed.

Canonical Structure cinduced_linear :=
  Linear cinduced_is_linear.

(* Isaacs' 5.2 *)
Lemma frobenius_reciprocity : 
  forall f1 f2, H \subset G -> f1 \in 'CF(H) -> f2 \in 'CF(G)->
   '[f1,'Res[H] f2]_H = '['Ind[G,H] f1,f2]_G.
Proof.
move=> f1 f2 HsG F1iC F2iC.
apply: sym_equal; rewrite !inner_prodE.
pose f3 i :=  #|H|%:R^-1 * \sum_(g \in G) f1 (i ^g) * (f2 i)^*.
rewrite (eq_bigr f3) =>[/=|g GiG]; rewrite {}/f3; last first.
  by rewrite cfunE -mulrA -mulr_suml.
rewrite mulr_sumr exchange_big /=.
pose f3 i :=  \sum_(g \in G) f1 (g ^ i) * (f2 (g ^ i))^*.
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

Lemma cinduced_conjC : forall f, ('Ind[G,H] f)^*%CH = 'Ind[G,H] (f^*)%CH.
Proof.
move=> f; apply/cfunP=> g.
rewrite !cfunE rmorphM conjC_inv conjC_nat; congr (_ * _).
rewrite rmorph_sum; apply: eq_bigr=> h HiG.
by rewrite cfunE.
Qed.

End Induced.

Notation "''Ind[' G , H ]  f " := (cinduced G H f) (at level 24).

Section Product.

Variable (gT : finGroupType) (G : {group gT}).

Lemma prod_in_cfunI : forall (A B : {set gT}) (f1 f2 : cfun gT algC) , 
  f1 \in 'CF(G,A) -> f2 \in 'CF(G,B) -> f1 * f2 \in 'CF(G, A :&: B).
Proof.
move=> A B f1 f2; case/cfun_memfP=> H1f1 H2f1; case/cfun_memfP=> H1f2 H2f2.
apply/cfun_memfP; split=> [x|x y XiG YiG]; rewrite !cfunE; last first.
  by rewrite H2f1 // H2f2.
rewrite !inE -andbA negb_andb; case/orP=> HA.
  by rewrite H1f1 ?mul0r // inE (negPf HA).
by rewrite H1f2 ?mulr0 // inE.
Qed.

Lemma prod_in_cfun : forall (A : {set gT}) (f1 f2 : cfun gT algC) , 
  f1 \in 'CF(G,A) -> f2 \in 'CF(G,A) -> f1 * f2 \in 'CF(G, A).
Proof. by move=> A f1 f2 Hf1 Hf2; rewrite -[A]setIid prod_in_cfunI. Qed.

End Product.
