(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient finalg action.
Require Import gproduct zmodp commutator cyclic center pgroup sylow.
Require Import vector algC matrix.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(******************************************************************************)
(* This file contains the basic notions of class functions                    *)
(*    {cfun gT} == the type of functions from the finGroupType gT to algC.    *)
(*         '1_G == the indicator function of G as a class function.           *)
(*       f^*%CH == the function conjugate to f.                               *)
(*    'CF(G, A) == the vector space of class functions of G with support A.   *)
(*       'CF(G) == the vector space of class functions of G with support G.   *)
(*    '[f, g]_G == the convolution product of f and g, normalised so that     *)
(*                 irr G is an orthonormal basis of 'CF(G).                   *)
(*   (f / N)%CH == if f \in 'CF(G) and N <| G, the corresponding class        *)
(*                 function on the cosets of N.                               *)
(*  (f %% N)%CH == the class function on G corresponding to f \in 'CF(G / N). *)
(*    'Res[H] f == the restriction of f to H: 'Res[H] f x = f x if x \in H,   *)
(*                 and 'Res[H] f x = 0 if x \notin H.                         *)
(* 'Ind[G, H] f == the class function induced by f from H to G.               *)
(******************************************************************************)

Reserved Notation "''CF' ( G , A )" (at level 8, format "''CF' ( G ,  A )").
Reserved Notation "''CF' ( G )" (at level 8, format "''CF' ( G )").
Reserved Notation "''1_' G" (at level 8, G at level 2, format "''1_' G").
Reserved Notation "''Res[' H ]" (at level 8, format "''Res[' H ]").
Reserved Notation "''Ind[' G , H ]" (at level 8, format "''Ind[' G ,  H ]").
Reserved Notation "'[ u , v ]_ G"
  (at level 8, G at level 2, format "'[hv' ''[' u ,  '/' v ]_ G ']'").
Reserved Notation "'[ u ]_ G"
  (at level 8, G at level 2, format "''[' u ]_ G").

Section AlgC.

Variable (gT : finGroupType).

Lemma neq0GC (G : {group gT}) : (#|G|)%:R != 0 :> algC.
Proof. by rewrite -neq0N_neqC (cardD1 1%g) group1. Qed.

Lemma sposGC (G : {group gT}) : 0 < #|G|%:R.
Proof. by rewrite /ltC neq0GC // posC_nat. Qed.
Implicit Type G : {group gT}.
Import GroupScope GRing.Theory.

Lemma pGroupG G : [char algC]^'.-group G.
Proof.
by apply: sub_pgroup (pgroup_pi G)=> i _; rewrite inE /= Cchar.
Qed.

End AlgC.

Delimit Scope character_scope with CH.

Definition cfun (gT : finGroupType) of phant gT := {ffun gT -> algC}.
Bind Scope character_scope with cfun.

Notation "{ 'cfun' T }" := (cfun (Phant T))
  (at level 0, format "{ 'cfun'  T }") : type_scope.

Section FunOfCfun.

Implicit Type gT : finGroupType.

Definition fun_of_cfun gT phT (f : @cfun gT phT) := f : gT -> algC.
Coercion fun_of_cfun : cfun >-> Funclass.

Lemma cfunE gT (f : gT -> algC) x :
  ((finfun f : {cfun gT}) x = f x) * (finfun f x = f x).
Proof. by split; exact: ffunE. Qed.

Lemma cfunP gT (f1 f2 : {cfun gT}) : f1 =1 f2 <-> f1 = f2.
Proof. exact: ffunP. Qed.

End FunOfCfun.

(* Temporary kludge to compensate the cloning of the ffun Lmodule instance. *)
(* Bizzarre behavior of pattern matching: omitting the (Phant _) pattern    *)
(* triggers an "undeclared evar" anomaly when trying to do rewrite -/fcf in *)
(* a DIFFERENT file (it works fin in classfun !!!).                         *)
Notation fcf := (@fun_of_cfun _ (Phant _) _).

Section ClassFun. 

Variables (gT : finGroupType) (G : {group gT}).

Canonical cfun_eqType := [eqType of {cfun gT}].
Canonical cfun_choiceType := [eqType of {cfun gT}].
Canonical cfun_zmodType := [zmodType of {cfun gT}].
Canonical cfun_ringType := 
  Eval hnf in RingType {cfun gT} (@ffun_ringMixin gT algC 1%g).
Canonical cfun_lmodType := 
  Eval hnf in LmodType algC {cfun gT} (
                 @ffun_lmodMixin algC gT (GRing.regular_lmodType algC)).

Lemma sum_cfunE I r (P : pred I) (F : I -> {cfun gT}) :
  \sum_(i <- r | P i) F i = [ffun x => \sum_(i <- r | P i) F i x].
Proof. exact: sum_ffunE. Qed.

Definition cfuni (G : {set gT}) : {cfun gT} := [ffun g => (g \in G)%N%:R].

Local Notation "''1_' G" := (cfuni G).
 
Lemma cfuniE (A : {set gT}) g : '1_A g = (g \in A)%:R.
Proof. by rewrite cfunE. Qed.

Lemma cfuniM (A B : {set gT}) : '1_A * '1_B = '1_(A :&: B).
Proof.
apply/cfunP=> g; rewrite !cfunE inE.
by do 2 (case: (_ \in _); rewrite ?(mul1r,mul0r)).
Qed.

Lemma support_cfuni (A : {set gT}) : support '1_A =i A.
Proof. by move=> x; rewrite !inE cfunE -(eqN_eqC _ 0) -lt0n lt0b. Qed.

Definition base_cfun (G A : {set gT}) : _.-tuple {cfun gT} :=
  in_tuple (filter [pred f : {cfun gT} | support f \subset A]
                   [seq '1_xG | xG <- enum (classes G)]).

Lemma base_cfun_subset (A : {set gT}) :
  G \subset A -> base_cfun G A = [seq '1_xG | xG <- enum (classes G)] :> seq _.
Proof.
move=> sGA; apply/all_filterP/allP=> /= f /mapP[xG].
rewrite mem_enum => /imsetP[x Gx ->] ->{xG}.
by rewrite (eq_subset (support_cfuni _)) (subset_trans (class_subG Gx _)).
Qed.
 
Canonical cfunVectType := 
 (@VectorType.pack algC _ {cfun gT} _  _ _ _ idfun
   (@ffunVectMixin algC (regVectType algC) gT)
    idfun).

Definition class_fun G  A := span (base_cfun G A).
Local Notation "''CF' ( G , A )" := (class_fun G A) : ring_scope.
Local Notation "''CF' ( G )" := (class_fun G G) : ring_scope.

Lemma class_funE (A : {set gT}) :
  'CF(G,A) = 
     (\sum_(i < #|classes G| | enum_val i \subset A) ('1_(enum_val i))%:VS)%VS.
Proof.
rewrite /class_fun /span /base_cfun /= big_filter /= big_map /=.
have bij_cG := enum_val_bij_in (classes1 G).
rewrite big_filter_cond (reindex _ (subon_bij _ bij_cG)) => [|_ /andP[]] //=.
by apply: eq_bigl => i; rewrite enum_valP (eq_subset (support_cfuni _)).
Qed.

(* Definition 
   forall x, x \notin A -> f x = 0 (ajouter A \subset G) 
   forall x y, y \in G -> f (x ^ y) = f x)
 *)
Lemma cfun_memfP (A : {set gT}) (f : {cfun gT}) :
  reflect 
    [/\ forall x, x \notin A :&: G -> f x = 0
      & forall x y, y \in G -> f (x ^ y) = f x]
    (f \in 'CF(G, A)).
Proof.
pose bGA := base_cfun G A.
apply: (iffP idP)=> [|[Hg Hc]].
  move/coord_span->; split=> [x XniAG|x y YiG].
    rewrite sum_cfunE cfunE; apply: big1 => i _; rewrite cfunE -/fcf -/bGA.
    have: bGA`_i \in bGA by apply: mem_nth.
    rewrite mem_filter => /andP[AbGAi /imageP[_ /imsetP[y Gy ->] def_bGAi]].
    apply: contraNeq XniAG; rewrite mulf_eq0 inE => /norP[_ nz_bGAi_x].
    rewrite (subsetP AbGAi) ?inE ?(subsetP (class_subG Gy (subxx _))) //.
    by rewrite -support_cfuni -def_bGAi inE.
  apply/eqP; rewrite -subr_eq0; apply/eqP.
  rewrite !sum_cfunE !cfunE -sumr_sub; apply: big1=> i _.
  set u := coord _ _ _; rewrite !cfunE.
  have: bGA`_i \in bGA by apply: mem_nth.
  rewrite mem_filter => /andP[Hs /imageP[_ /imsetP[z Gz ->] ->]].
  by rewrite !cfunE (class_transl _ (memJ_class _ _)) // subrr.
suff<-: \sum_(C \in (classes G)) 
           (f (repr C)) *: ([ffun x : gT => (x \in C)%:R] : {cfun gT}) = f.
  apply: memv_suml=> i Hi.
  case: (boolP (f (repr i) == 0))=> [|Hr].
    by move/eqP->; rewrite scale0r mem0v.
  apply: memvZl; apply: memv_span.
  rewrite mem_filter; apply/andP; split; last by apply/imageP; exists i.
  apply/subsetP=> x; rewrite !inE cfunE.
  apply: contraR=> XniA.
  case: (boolP (x \in i))=> //= XiI; case/eqP: Hr.
  case/imsetP: Hi XiI => g GiG ->; case/imsetP=> h HiG Hx.
  case: (repr_class G g)=> h1 H1iG ->.
  by rewrite Hc // -(Hc _ _ HiG) // -Hx Hg // inE (negPf XniA).
apply/cfunP=> g; rewrite sum_cfunE cfunE.
case GiG: (g \in G); last first.
  rewrite Hg ?(inE,GiG,andbF) //; apply: big1=> i Hi; rewrite !cfunE.
  have [x Gx ->] := imsetP Hi.
  case Hgx: (_ \in _); last by rewrite scaler0.
  move/subsetP: (class_subG Gx (subxx G)) GiG.
  by move/(_ g (idP Hgx))=> ->.
rewrite (bigD1 (g ^: G : set_of_finType _)) /=; last by apply/imsetP; exists g.
rewrite !cfunE big1.
  rewrite class_refl.
  by case: (repr_class G g)=> x Hx ->; rewrite Hc // addr0; exact: mulr1.
move=> i; case/andP; case/imsetP=> y Hy -> Hz.
rewrite !cfunE; case E1: (_ \in _); last by rewrite scaler0.
by case/negP: Hz; rewrite eq_sym; apply/eqP; apply: class_transr.
Qed.

Lemma cfun_memP (f : {cfun gT}) :
  reflect 
    ((forall x, x \notin G -> f x = 0) /\
        (forall x y, y \in G -> f (x ^ y) = f x))
    (f \in 'CF(G)).
Proof. by apply: (iffP (cfun_memfP G f)); rewrite setIid. Qed.

Lemma cfunS0 A (f : {cfun gT}) x : f \in 'CF(G,A) -> x \notin A -> f x = 0.
Proof. 
case/cfun_memfP=> HH _ XniA; apply: HH.
by rewrite inE (negPf XniA).
Qed.

Lemma cfun0 (f : {cfun gT}) x : f \in 'CF(G) -> x \notin G -> f x = 0.
Proof. exact: cfunS0. Qed.

Lemma cfunJ A (f : {cfun gT}) x y : 
   f \in 'CF(G,A) -> y \in G -> f (x ^ y) = f x.
Proof. by case/cfun_memfP=> _ HH; exact: HH. Qed.

Lemma cfun_sum (F : gT -> algC) :
  (forall g h, g \in G -> h \in G -> F (g ^ h) = F g) ->
  \sum_(g \in G) F g = \sum_(C \in classes G) #|C|%:R * (F (repr C)).
Proof.
move=> HF.
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

Lemma cfun_free A : free (base_cfun G A).
Proof.
apply: free_filter; apply /freeP => s S0 i.
move/cfunP/(_ (repr (enum_val i))): S0.
rewrite sum_cfunE !cfunE (bigD1 i) //= big1 ?addr0 => [|j].
  pose i0 := @enum_default _ [eta _] i.
  rewrite (nth_map i0) -/(enum_val i) -?cardE // !cfunE [_ *: _]mulr_natr.
  by have /imsetP[x _ ->] := enum_valP i; rewrite (mem_repr x) ?class_refl.
pose j0 := @enum_default _ [eta _] j.
rewrite (nth_map j0) -?cardE // -/(enum_val j) !cfunE.
apply: contraNeq; rewrite mulf_eq0 -(eqN_eqC _ 0) eqb0 => /norP[_ /negbNE].
rewrite -(inj_eq (@enum_val_inj _ _)).
have /imsetP[y _ ->] := enum_valP i; have /imsetP[z _ ->] := enum_valP j.
move/class_transr <-; apply/eqP/class_transr.
by rewrite (mem_repr y _) ?class_refl.
Qed.

Lemma dim_cfun : \dim 'CF(G) = #|classes G|.
Proof.
by rewrite (eqnP (cfun_free G)) base_cfun_subset // size_map -cardE.
Qed.

(* cfun and support *)

Lemma support1 (A : {set gT}) : support '1_A \subset A.
Proof.
apply/subsetP=> g; rewrite !inE !cfunE; apply: contraR.
by move/negPf->; rewrite -(eqN_eqC _ 0).
Qed.

Lemma support_subset (A B: {set gT}) (f: {cfun gT}) : 
       support f \subset A -> A \subset B -> support f \subset B.
Proof. by apply: subset_trans. Qed.

Lemma support_memc f B : f \in 'CF(G ,B) -> support f \subset B.
Proof.
move/cfun_memfP=> [H1 _]; apply/subsetP=> x; rewrite !inE -/fcf.
by apply: contraR => XniB; rewrite H1 // inE (negPf XniB).
Qed.

Lemma memc1: '1_G \in 'CF(G).
Proof.
apply/cfun_memP; split=> [x XniG| x y XiG]; last by rewrite !cfunE groupJr.
by apply/eqP; move/subsetP: (support1 G);move/(_ x); rewrite !inE;
 move/contra; rewrite negbK=> ->.
Qed.

Lemma memc_subset (A B: {set gT}) f :
  B \subset A -> f \in 'CF(G, B) -> f \in 'CF(G, A).
Proof.
move=> Hss; case/cfun_memfP=> H1 H2; apply/cfun_memfP.
split=> {H2}// x XniAG; apply: H1.
move: XniAG; rewrite !inE !negb_and => /orP[] => Hx; last by rewrite Hx orbT.
by apply/orP;left; move: Hx; apply: contra; move/(subsetP Hss)=> ->.
Qed.

Lemma memcW f A : f \in 'CF(G, A) -> f \in 'CF(G).
Proof.
move/cfun_memfP=> [H1 H2];apply/cfun_memP;split=> //.
by move=> x XniG; apply: H1; rewrite inE (negPf XniG) andbF.
Qed.

Lemma memcE A f : 
  f \in 'CF(G, A) = (support f \subset A) && (f \in 'CF(G)).
Proof.
apply/cfun_memfP/andP=> [[Hs Hj]|[Hs Hc]]; split.
- by apply/subsetP=> x; rewrite !inE; apply: contraR => XniA;
    rewrite -/fcf Hs // inE (negPf XniA).   
- by apply/cfun_memP; split=> // x XniA; rewrite Hs // inE (negPf XniA) andbF.
- move=> x; rewrite inE negb_and; case/orP=> HH; last by apply: cfun0.
  by move/supportP: Hs; rewrite -/fcf => ->.
by case/cfun_memP: Hc.
Qed.

End ClassFun.

Arguments Scope class_fun [_ group_scope group_scope].
Notation "''CF' ( G , A )" := (class_fun G A) : ring_scope.
Notation "''CF' ( G )" := (class_fun G G) : ring_scope.

Arguments Scope cfuni [_ group_scope].
Notation "''1_' G" := (cfuni G) : ring_scope.

Definition cfun_conjC (gT : finGroupType) (f : {cfun gT}) : {cfun gT} :=
  [ffun h => (f h)^*].

Arguments Scope cfuni [_ character_scope].
Notation "f ^*" := (cfun_conjC f) : character_scope.

Lemma cfun_conjCE (gT : finGroupType) (f : {cfun gT}) g : 
  (f^*)%CH g = (f g)^*.
Proof. by rewrite cfunE. Qed.

Lemma cfun_conjCK (gT : finGroupType) : involutive (@cfun_conjC gT).
Proof. by move=> f; apply/cfunP=> g; rewrite !cfunE conjCK. Qed.

Lemma cfun_conjC1 (gT : finGroupType) (G : {set gT}) : 
  (('1_G)^*)%CH = '1_G.
Proof. by apply/cfunP=> g; rewrite !cfunE conjC_nat. Qed.

Section Restrict.

Variable (gT : finGroupType).

Definition crestrict (G : {set gT}) (f : {cfun gT}) : {cfun gT} := '1_G * f.

Local Notation "''Res[' H ]" := (crestrict H) : ring_scope.

Lemma crestrictE (G : {set gT}) f : {in G, 'Res[G] f =1 f}.
Proof. by move=> g GiG; rewrite /= !cfunE GiG mul1r. Qed.
 
Lemma crestrict1 (G H : {set gT}) : 'Res[H] '1_G = '1_(H :&: G).
Proof. by exact: cfuniM. Qed.
 
Lemma memc_restrict (f : {cfun gT}) (G H : {group gT}) : 
  H \subset G -> f \in 'CF(G) -> 'Res[H] f \in 'CF(H).
Proof.
move=> Hsub fC; apply/cfun_memP; split.
  by move=> g; rewrite !cfunE; case: (_ \in _)=> //; rewrite mul0r.
move=> g h hIn; rewrite !cfunE -/fcf.
by rewrite (cfunJ _ fC) ?(subsetP Hsub) // (groupJr _ hIn).
Qed.

Lemma crestrict_is_linear (G : {set gT}) : linear (crestrict G).
Proof.
move=> c f1 f2; apply/cfunP=> g.
by rewrite !cfunE mulr_addr mulrCA.
Qed.

Canonical crestrit_linear G := Linear (crestrict_is_linear G).

Lemma crestrict_subset (G H : {set gT}) (f : {cfun gT}) :
  H \subset G -> 'Res[H] ('Res[G] f) = 'Res[H] f.
Proof.
move=> HsG; apply/cfunP=> g.
by rewrite !cfunE; case: (boolP (_ \in _))=> [HH|]; 
   rewrite ?mul0r // (subsetP HsG) // !mul1r.
Qed.

End Restrict.

Arguments Scope crestrict [_ group_scope character_scope].
Notation "''Res[' H ]" := (crestrict H) : ring_scope.

Section InnerProduct.

Variable (gT : finGroupType) (G : {group gT}).

Let card_neq0 : #|G|%:R^-1 != 0 :> algC.
Proof. by rewrite invr_eq0 neq0GC. Qed.

Definition inner_prod (G : {set gT}) (f g : {cfun gT}) :=
  #|G|%:R^-1 * \sum_(i \in G) f i * (g i)^*.

Local Notation "''[' u , v ]_ G":= (inner_prod G u v) : ring_scope.
Local Notation "''[' u ]_ G" := '[u , u]_G : ring_scope.

Lemma inner_prodE (f g : {cfun gT}) :
  '[f, g]_G = #|G|%:R^-1 * \sum_(i \in G) f i * (g i)^*.
Proof. by []. Qed.

Lemma inner_prod1 (H1 H2 : {set gT}) :
 '['1_H1, '1_H2]_G =  #|G :&: H1 :&: H2|%:R / #|G|%:R.
Proof.
rewrite inner_prodE big_mkcond /=.
rewrite (bigID [pred x \in G :&: H1 :&: H2]) /=.
rewrite (eq_bigr (fun i : gT => 1))=> [|i]; last first.
  rewrite -setIA inE; case: (_ \in _)=> //=.
  rewrite -cfun_conjCE // cfun_conjC1.
  move: (cfuniE (H1 :&: H2) i).
  by rewrite -cfuniM cfunE => ->; case: (_ \in _).
rewrite sumr_const big1 ?(addr0) //; first by exact: mulrC.
move=> i; rewrite -setIA inE; case: (_ \in _)=> //=.
rewrite -cfun_conjCE // cfun_conjC1.
move: (cfuniE (H1 :&: H2) i).
by rewrite -cfuniM cfunE => ->; case: (_ \in _).
Qed.
 
Let card_conj : (#|G|%:R^-1)^* = #|G|%:R^-1.
Proof. by rewrite posC_conjK // posC_inv posC_nat. Qed.

Lemma inner_conj f g : '[f, g]_G = ('[g, f]_G)^*.
Proof.
rewrite /inner_prod rmorphM card_conj.
congr (_ * _); rewrite rmorph_sum; apply: eq_bigr=> i _.
by rewrite rmorphM conjCK mulrC.
Qed.
 
Lemma posC_inner_prod f : 0 <= '[f]_G.
Proof. 
apply: posC_mul; first by rewrite posC_inv posC_nat.
by rewrite posC_sum // => i _; rewrite /leC subr0 repC_pconj.
Qed.

Lemma inner_prod0l f : '[0, f]_G = 0.
Proof.
rewrite inner_prodE big1 ?mulr0 // => i.
by rewrite cfunE mul0r.
Qed.

Lemma inner_prod0r f : '[f, 0]_G = 0.
Proof.
rewrite inner_prodE big1 ?mulr0 // => i.
by rewrite cfunE conjC0 mulr0.
Qed.

Lemma inner_prod0 (f : {cfun gT}) : 
  f \in 'CF(G) -> ('[f]_G == 0) = (f == 0).
Proof.
move=> Hf; apply/eqP/eqP=> Hp; last first.
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

Lemma inner_prodbE f g : inner_prodb f g = inner_prod G g f.
Proof. by []. Qed.

Lemma inner_prodb_is_linear f : linear (inner_prodb f : _ -> algC^o).
Proof.
move=> k g1 g2.
rewrite /inner_prodb /inner_prod.
rewrite {1}scaler_mulr -{1}scaler_addr; congr (_ * _).
rewrite {1}scaler_sumr /= -{1}big_split /=; apply: eq_bigr=> i _.
by rewrite scaler_mull -mulr_addl !cfunE.
Qed.

Canonical inner_prodb_linear f := Linear (inner_prodb_is_linear f).

Lemma inner_prod_is_additive f : additive (inner_prod G f).
Proof.
move=> g1 g2.
rewrite /inner_prod /inner_prod.
rewrite -mulr_subr; congr (_ * _).
rewrite -sumr_sub; apply: eq_bigr=> i _.
by rewrite !cfunE rmorph_sub // mulr_subr.
Qed.

Canonical inner_prod_additive f := Additive (inner_prod_is_additive f).

Lemma inner_prodZ k (f g : {cfun gT}) : '[f, k *: g]_G = k^* * '[f, g]_G.
Proof.
rewrite /inner_prod mulrCA; congr (_ * _).
rewrite -mulr_sumr; apply: eq_bigr=> i _.
by rewrite !cfunE rmorphM mulrCA.
Qed.

Lemma cfun_conjC_inner (f1 f2 : {cfun gT}) :
  ('[f1^*, f2^*]_G)%CH = ('[f1, f2]_G)^*.
Proof.
rewrite !inner_prodE rmorphM conjC_inv conjC_nat.
congr (_ * _); rewrite (big_morph _ (rmorphD conjC) conjC0); apply: eq_bigr.
by move=> g GiG; rewrite !cfunE rmorphM.
Qed.

End InnerProduct.

Arguments Scope inner_prod [_ group_scope character_scope character_scope].
Notation "''[' u , v ]_ G":=  (inner_prod G u v) : ring_scope.
Notation "''[' u ]_ G":= '[u, u]_G : ring_scope.

Section Coset.

Variable (gT : finGroupType).

Implicit Type G : {group gT}.

Definition qfun_of_cfun (N : {set gT}) (f : {cfun gT}) :=
  [ffun x : coset_of N => f (repr x)].

Local Notation "f / N" := (qfun_of_cfun N f) : character_scope.

Definition cfun_of_qfun (N : {set gT}) (f : {cfun (coset_of N)}) : {cfun gT} :=
  [ffun x : gT => (x \in 'N(N))%:R * f (coset N x)].

Local Notation "f %% N" := (@cfun_of_qfun N f) : character_scope.

Lemma cfunqE (N : {group gT}) f x :
  x \in 'N(N) -> (f %% N)%CH x = f (coset N x).
Proof. by move=> XiNN; rewrite !cfunE XiNN // mul1r. Qed.

End Coset.

Arguments Scope qfun_of_cfun [_ group_scope character_scope].
Arguments Scope cfun_of_qfun [_ group_scope character_scope].
Notation "f / N" := (qfun_of_cfun N f) : character_scope.
Notation "f %% N" := (@cfun_of_qfun _ N f) : character_scope.

Section Induced.

Variable gT : finGroupType.

Definition cinduced  (G H : {set gT}) (f : {cfun gT}) : {cfun gT} :=
 [ffun g =>  #|H|%:R^-1 * \sum_(c | c \in G) f (g ^ c)].

Local Notation "'Ind[ G , H ]" := (cinduced G H) : ring_scope.

Variables G H : {group gT}.

Lemma memc_induced (f : {cfun gT}) :
  H \subset G -> f \in 'CF(H) -> 'Ind[G,H] f \in 'CF(G).
Proof.
move=> HsG Hf; apply/cfun_memP; split=> [g Hg|g h HiG].
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

Lemma support_induced f :
  f \in 'CF(H) -> H <| G -> support ('Ind[G,H] f) \subset H.
Proof.
move=> Cf HnG; apply/subsetP=> h. rewrite !inE; apply:contraR=> HniH.
rewrite cfunE big1 ?mulr0 // => g GiG.
by rewrite (cfun0 Cf) // memJ_norm // (subsetP (normal_norm HnG)).
Qed.
 
Lemma cinduced1 f : 
  H \subset G -> ('Ind[G, H] f) 1%g = #|G : H|%:R * f 1%g.
Proof.
move=> HsG; rewrite cfunE (eq_bigr (fun _ => f 1%g)).
  rewrite sumr_const -[(f _) *+ _]mulr_natl mulrA -(LaGrange HsG).
  by rewrite natr_mul mulrA mulVf ?mul1r // neq0GC.
by move=> i; rewrite conj1g.
Qed.

Lemma cinduced_is_linear : linear (cinduced G H).
Proof.
move=> c f1 f2; apply/cfunP=> g.
rewrite !cfunE [_ *: (_ * _)]mulrCA -mulr_addr.
rewrite -[c * _]mulr_sumr -big_split; congr (_ * _).
by apply: eq_bigr=> h HiG; rewrite !cfunE.
Qed.
Canonical cinduced_linear := Linear cinduced_is_linear.

(* Isaacs' 5.2 *)
Lemma frobenius_reciprocity f1 f2 :
    H \subset G -> f1 \in 'CF(H) -> f2 \in 'CF(G)->
  '[f1, 'Res[H] f2]_H = '['Ind[G, H] f1, f2]_G.
Proof.
move=> HsG F1iC F2iC.
apply: sym_equal; rewrite !inner_prodE.
pose f3 i :=  #|H|%:R^-1 * \sum_(g \in G) f1 (i ^g) * (f2 i)^*.
rewrite (eq_bigr f3) =>[/=|g GiG]; rewrite {}/f3; last first.
  by rewrite cfunE -mulrA -mulr_suml.
rewrite mulr_sumr exchange_big /=.
pose f3 i :=  \sum_(g \in G) f1 (g ^ i) * (f2 (g ^ i))^*.
rewrite (eq_bigr f3) =>[/=|g GiG]; rewrite {}/f3; last first.
  by apply: eq_bigr=> h HiG; rewrite -!/fcf (cfunJ _ F2iC).
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
  by move=> g; case/andP=> GiG GniH; rewrite -/fcf (cfun0 F1iC) ?mul0r.
set u := _%:R; set v := _%:R; rewrite -mulr_natl -/u.
rewrite !mulrA [_/_]mulrC mulfVK ?neq0GC //; congr (_ * _).
apply: eq_big=> [g|g]; rewrite negbK.
  by case E1: (g \in H); rewrite ?andbF // (subsetP HsG _ (idP E1)).
by case/andP=> _ GiH; rewrite crestrictE.
Qed.

Lemma cinduced_conjC f : ('Ind[G, H] f)^*%CH = 'Ind[G, H] f^*%CH.
Proof.
apply/cfunP=> g.
rewrite !cfunE rmorphM conjC_inv conjC_nat; congr (_ * _).
rewrite rmorph_sum; apply: eq_bigr=> h HiG.
by rewrite cfunE.
Qed.

End Induced.

Arguments Scope cinduced [_ group_scope group_scope character_scope].
Notation "''Ind[' G , H ]" := (cinduced G H) : ring_scope.

Section Product.

Variable (gT : finGroupType) (G : {group gT}).

Lemma memc_prodI (A B : {set gT}) (f1 f2 : {cfun gT}) : 
  f1 \in 'CF(G, A) -> f2 \in 'CF(G, B) -> f1 * f2 \in 'CF(G, A :&: B).
Proof.
case/cfun_memfP=> H1f1 H2f1; case/cfun_memfP=> H1f2 H2f2.
apply/cfun_memfP; split=> [x|x y YiG]; rewrite !cfunE -!/fcf; last first.
  by rewrite H2f1 // H2f2.
rewrite !inE -andbA negb_and; case/orP=> HA.
  by rewrite H1f1 ?mul0r // inE (negPf HA).
by rewrite H1f2 ?mulr0 // inE.
Qed.

Lemma memc_prod (A : {set gT}) (f1 f2 : {cfun gT}) : 
  f1 \in 'CF(G, A) -> f2 \in 'CF(G, A) -> f1 * f2 \in 'CF(G, A).
Proof. by move=> Hf1 Hf2; rewrite -[A]setIid memc_prodI. Qed.

End Product.

Section DProduct. 

Variable (gT : finGroupType) (G H1 H2 : {group gT}).
Hypothesis H1xH2 : H1 \x H2 = G.

Lemma sum_dprodl (R : Type) (idx : R) (op : Monoid.com_law idx) (F : gT -> R) :
   \big[op/idx]_(g \in G) F g =
      \big[op/idx]_(h1 \in H1) \big[op/idx]_(h2 \in H2) F (h1 * h2)%g.
Proof.
rewrite pair_big_dep.
pose f (g : gT) := (divgr H1 H2 g, remgr H1 H2 g).
have Hf: {on [pred i | (i.1 \in H1) && (i.2 \in H2)], bijective f}.
  case/dprodP: H1xH2=> _ _ _ HH.
  exists (fun p => (p.1 * p.2)%g)=> [g|[g h] /andP [] /= Hg Hh].
    by rewrite !inE -?divgr_eq.
  by rewrite /f ?(divgrMid,remgrMid).
rewrite (reindex f) //.
apply: eq_big; last first.
  by move=> g GiG; rewrite /= -divgr_eq.
move=> g /=; apply/idP/idP=> [GiG | /andP [] DiH1 DiH2].
  rewrite [g](divgr_eq H1 H2).
  by rewrite !(mem_divgr,mem_remgr) // -divgr_eq; case/dprodP: H1xH2=> _ ->.
rewrite [g](divgr_eq H1 H2).
case/dprodP: H1xH2=> _ <- _ _.
by apply: mem_mulg.
Qed.

Lemma sum_dprodr (R : Type) (idx : R) (op : Monoid.com_law idx) (F : gT -> R) :
  \big[op/idx]_(g \in G) F g =
    \big[op/idx]_(h2 \in H2) \big[op/idx]_(h1 \in H1) F (h1 * h2)%g.
Proof.
rewrite pair_big_dep.
pose f (g : gT) := (remgr H1 H2 g, divgr H1 H2 g).
have Hf: {on [pred i | (i.1 \in H2) && (i.2 \in H1)], bijective f}.
  case/dprodP: H1xH2=> _ _ _ HH.
  exists (fun p => (p.2 * p.1)%g)=> [g|[g h] /andP [] /= Hg Hh].
    by rewrite !inE -?divgr_eq.
  by rewrite /f ?(divgrMid,remgrMid).
rewrite (reindex f) //.
apply: eq_big; last first.
  by move=> g GiG; rewrite /= -divgr_eq.
move=> g /=; apply/idP/idP=> [GiG | /andP [] DiH1 DiH2].
  rewrite [g](divgr_eq H1 H2).
  by rewrite !(mem_divgr,mem_remgr) // -divgr_eq; case/dprodP: H1xH2=> _ ->.
rewrite [g](divgr_eq H1 H2).
case/dprodP: H1xH2=> _ <- _ _.
by apply: mem_mulg.
Qed.

Definition cfun_div (H1xH2 : H1 \x H2 = G) (f : {cfun gT}) : {cfun gT} :=
  '1_G * [ffun g => f (divgr H1 H2 g)].

Definition cfun_rem (H1xH2 : H1 \x H2 = G) (f : {cfun gT}) : {cfun gT} :=
  '1_G * [ffun g => f (remgr H1 H2 g)].

Definition cfun_dprod (f1 f2 : {cfun gT}) : {cfun gT} :=
  cfun_div H1xH2 f1 * cfun_rem H1xH2 f2.

Lemma mem_dprod g :
   g \in G = ((divgr H1 H2 g \in H1) && (remgr H1 H2 g \in H2)).
Proof.
apply/idP/idP=> [|/andP [] Hrem Hdiv]; last first.
  case/dprodP: H1xH2=> _ <- _ _.
  apply/imset2P; exists (divgr H1 H2 g) (remgr H1 H2 g) => //.
  apply: divgr_eq.
case/dprodP: H1xH2=> _ <- _ DH1H2.
case/imset2P=> y1 y2 Y1iH1 Y2iH2 ->.
by rewrite divgrMid // remgrMid // Y1iH1.
Qed.

Lemma cfun_dprod1r f : cfun_dprod f '1_H2 = cfun_div H1xH2 f.
Proof.
apply/cfunP=> g; rewrite !cfunE mem_dprod.
by set u := remgr _ _ _ \in H2; set v := divgr _ _ _ \in H1;
   case u; case v=> /=; rewrite !(mul0r,mul1r,mulr1).
Qed.

Lemma cfun_dprod1l f : cfun_dprod '1_H1 f = cfun_rem H1xH2 f.
Proof.
apply/cfunP=> g; rewrite !cfunE mem_dprod.
by set u := remgr _ _ _ \in H2; set v := divgr _ _ _ \in H1;
   case u; case v=> /=; rewrite !(mul0r,mul1r,mulr1).
Qed.

Lemma inner_prod_dprod (f1 f2 f'1 f'2 : {cfun gT}) :
     f1 \in 'CF(H1) ->  f2 \in 'CF(H2) ->
    f'1 \in 'CF(H1) -> f'2 \in 'CF(H2) ->
  '[cfun_dprod f1 f2, cfun_dprod f'1 f'2]_G = 
     '[f1, f'1]_H1 * '[f2, f'2]_H2.
Proof.
move=> Cf1 Cf2 Cf'1 Cf'2.
rewrite inner_prodE -(dprod_card H1xH2) natr_mul.
rewrite invf_mul -mulrA -mulr_sumr.
rewrite sum_dprodl /=.
rewrite inner_prodE -mulrA; congr (_ * _).
rewrite -mulr_suml; apply: eq_bigr=> h1 H1iH1.
rewrite inner_prodE -!mulr_sumr.
apply: eq_bigr=> h2 H2iH2.
case/dprodP: (H1xH2)=> _ _ _ HH.
rewrite !cfunE !(divgrMid,remgrMid) //.
have->: (h1 * h2)%g \in G.
  by case/dprodP: H1xH2=> _ <- _ _; apply: mem_mulg.
rewrite !mul1r mulrCA -!mulrA; congr (_ * _).
rewrite mulrCA [X in _ = X]mulrCA; congr (_ * _).
by rewrite mulrCA rmorphM.
Qed.

Lemma inner_prod_rem (f1 f2 : {cfun gT}) :
     f1 \in 'CF(H2) ->  f2 \in 'CF(H2) ->
  '[cfun_rem H1xH2 f1, cfun_rem H1xH2 f2]_G = '[f1, f2]_H2.
Proof.
move=> Cf1 Cf2.
rewrite -!cfun_dprod1l inner_prod_dprod ?memc1 //.
by rewrite inner_prod1 !setIid mulfV ?mul1r // neq0GC.
Qed.

Lemma inner_prod_div (f1 f2 : {cfun gT}) :
     f1 \in 'CF(H1) -> f2 \in 'CF(H1) ->
  '[cfun_div H1xH2 f1, cfun_div H1xH2 f2]_G = '[f1, f2]_H1.
Proof.
move=> Cf1 Cf2.
rewrite -!cfun_dprod1r inner_prod_dprod ?memc1 //.
by rewrite inner_prod1 !setIid mulfV ?mulr1 // neq0GC.
Qed.

End DProduct.
