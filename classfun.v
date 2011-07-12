(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient finalg action.
Require Import gproduct zmodp commutator cyclic center pgroup sylow.
Require Import vector algebra algC matrix.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(******************************************************************************)
(* This file contains the basic notions of class functions                    *)
(*          'CF(G) == the type of class functions on G : {group gT}, i.e.,    *)
(*                    which map gT to the type algC of complex algebraics,    *)
(*                    have support in G, and are constant on each conjugacy   *)
(*                    class of G. 'CF(G) implements the algebraType interface *)
(*                    of finite-dimensional F-algebras.                       *)
(*                    The identity 1 : 'CF(G) is the indicator function of G, *)
(*                    and (later) the principal character).                   *)
(*       'CF(G)%VS == the (total) vector space of 'CF(G).                     *)
(*       'CF(G, A) == the subspace of functions in 'CF(G) with support in A.  *)
(*           phi x == the image of x : gT under phi : 'CF(G).                 *)
(*       cfker phi == the kernel of phi : 'CF(G); note that cfker phi <| G.   *)
(*   cfaithful phi <=>  phi : 'CF(G) is faithful (has a trivial kernel).      *)
(*            '1_A == the indicator function of A as a function of 'CF(G).    *)
(*                    (Provided A \subset G; G is determined by the context.) *)
(*        phi^*%CH == the function conjugate to phi : 'CF(G).                 *)
(*                    (The %CH scope is bound to the 'CF(_) types.)           *)
(*           phi^u == the function conjugate to phi by an algC-automorphism u *)
(*   cfunAut u phi    The notation "_ ^u" is only reserved; it is up to       *)
(*                    clients to set Notation "phi ^u" := (cfunAut u phi).    *)
(*     '[phi, psi] == the convolution of phi, psi : 'CF(G) over G, normalised *)
(*   '[phi, psi]_G    by #|G| so that '[1, 1]_G = 1 (G is usually inferred).  *)
(*  cfdotr psi phi == '[phi, psi] (self-expanding).                           *)
(* '[phi], '[phi]_G == the squared norm '[phi, phi] of phi : 'CF(G).          *)
(* orthogonal R S <=> each phi in R : seq 'CF(G) is orthogonal to each psi in *)
(*                    S, i.e., '[phi, psi] = 0. As 'CF(G) coerces to seq, one *)
(*                    can write orthogonal phi S and orthogonal phi psi.      *)
(* pairwise_orthogonal S <=> the class functions in S are pairwise orhtogonal *)
(*                    AND non-zero.                                           *)
(*   orthonormal S <=> S is pairwise orthogonal and all class functions in S  *)
(*                    have norm 1.                                            *)
(*    isometry tau <-> tau : 'CF(D) -> 'CF(R) is an isometry, mapping         *)
(*                    '[_, _]_D to '[_, _]_R.                                 *)
(* {in CD, isometry tau, to CR} <-> in the domain CD, tau is an isometry      *)
(*                    whose range is contained in CR.                         *)
(* conjC_closed S <-> S : seq 'CF(G) is closed under DISTINCT conjugates: for *)
(*                    eact phi \in S, phi^*%CH != phi is also in S.           *)
(*     'Res[H] phi == the restriction of phi : 'CF(G) to a function of 'CF(H) *)
(*  'Res[H, G] phi    'Res[H] phi x = phi x if x \in H (when H \subset G),    *)
(*        'Res phi    'Res[H] phi x = 0 if x \notin H.                        *)
(*     'Ind[G] phi == the class function of 'CF(G) induced by phi : 'CF(H),   *)
(*  'Ind[G, H] phi    when H \subset G. As with 'Res phi, both G and H can    *)
(*        'Ind phi    be inferred, thou usually G isn't.                      *)
(*   cfunMorph phi == the class function in 'CF(G) that maps x to phi (f x),  *)
(*                    where phi : 'CF(f @* G), provided G \subset 'dom f.     *)
(*   (phi %% H)%CH == special case of cfunMorph phi, when phi : 'CF(G / H).   *)
(*    (phi / H)%CH == the class function in 'CF(G / H) that coincides with    *)
(*                    phi : 'CF(G) on cosets of H on which phi is constant.   *)
(* For a group G that is a direct product (with KxH : K \x H = G), we set     *)
(*  cfun_dprodl KxH phi == for phi : 'CF(K), the class function of 'CF(G)     *)
(*                         that maps k * h to phi k when k \in K and h \in H. *)
(*  cfun_dprodr KxH psi == for psi : 'CF(H), the class function of 'CF(G)     *)
(*                         that maps k * h to psi h when k \in K and h \in H. *)
(*  cfun_dprod KxH phi psi == the class function of 'CF(G) that maps k * h to *)
(*                         to phi k * psi h (this is the product of the above *)
(*                         two).                                              *)
(******************************************************************************)

Reserved Notation "''CF' ( G , A )" (at level 8, format "''CF' ( G ,  A )").
Reserved Notation "''CF' ( G )" (at level 8, format "''CF' ( G )").
Reserved Notation "''1_' G" (at level 8, G at level 2, format "''1_' G").
Reserved Notation "''Res[' H , G ]" (at level 8, only parsing).
Reserved Notation "''Res[' H ]" (at level 8, format "''Res[' H ]").
Reserved Notation "''Res'" (at level 0, only parsing).
Reserved Notation "''Ind[' G , H ]" (at level 8, only parsing).
Reserved Notation "''Ind[' G ]" (at level 8, format "''Ind[' G ]").
Reserved Notation "''Ind'" (at level 0, only parsing).
Reserved Notation "'[ phi , psi ]_ G" (at level 2, only parsing).
Reserved Notation "'[ phi , psi ]"
  (at level 2, format "'[hv' ''[' phi ,  '/' psi ] ']'").
Reserved Notation "'[ phi ]_ G" (at level 2, only parsing).
Reserved Notation "'[ phi ]" (at level 2, format "''[' phi ]").
Reserved Notation "phi ^u" (at level 3, format "phi ^u").

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

Section Defs.

Variable gT : finGroupType.

Definition is_class_fun (B : {set gT}) (f : {ffun gT -> algC}) :=
  (forallb x, forallb y, (y \in B) ==> (f (x ^ y) == f x))
  && (support f \subset B).

Lemma intro_class_fun (G : {group gT}) f :
    {in G &, forall x y, f (x ^ y) = f x} ->
    (forall x, x \notin G -> f x = 0) ->
  is_class_fun G (finfun f).
Proof.
move=> fJ Gf; apply/andP; split; last first.
  by apply/supportP=> x notAf; rewrite ffunE Gf.
apply/forallP=> x; apply/forall_inP=> y Gy; apply/eqP; rewrite !ffunE.
by have [/fJ-> // | notGx] := boolP (x \in G); rewrite !Gf ?groupJr.
Qed.

Variable B : {set gT}.
Local Notation G := <<B>>.

Record classfun : predArgType :=
  Classfun {cfun_val; _ : is_class_fun G cfun_val}.
Implicit Types phi psi xi : classfun.
(* The default expansion lemma cfunE requires key = 0. *)
Definition Cfun := locked (fun key : nat => Classfun).

Canonical cfun_subType := Eval hnf in [subType for cfun_val by classfun_rect].
Definition cfun_eqMixin := Eval hnf in [eqMixin of classfun by <:].
Canonical cfun_eqType := Eval hnf in EqType classfun cfun_eqMixin.
Canonical cfun_choiceMixin := Eval hnf in [choiceMixin of classfun by <:].
Canonical cfun_choiceType := Eval hnf in ChoiceType classfun cfun_choiceMixin.

Definition fun_of_cfun phi := cfun_val phi : gT -> algC.
Coercion fun_of_cfun : classfun >-> Funclass.

Lemma cfunElock k f fP : @Cfun k (finfun f) fP =1 f.
Proof. by unlock Cfun; exact: ffunE. Qed.

Lemma cfunE f fP : @Cfun 0 (finfun f) fP =1 f.
Proof. exact: cfunElock. Qed.

Lemma cfunP phi psi : phi =1 psi <-> phi = psi.
Proof. by split=> [/ffunP/val_inj | ->]. Qed.

Lemma cfun0gen phi x : x \notin G -> phi x = 0.
Proof. by case: phi => f fP; case: (andP fP) => _ /supportP; exact. Qed.

Lemma cfun_in_genP phi psi : {in G, phi =1 psi} -> phi = psi.
Proof.
move=> eq_phi; apply/cfunP=> x.
by have [/eq_phi-> // | notAx] := boolP (x \in G); rewrite !cfun0gen.
Qed.

Lemma cfunJgen phi x y : y \in G -> phi (x ^ y) = phi x.
Proof.
case: phi => f fP Gy; apply/eqP.
by case: (andP fP) => /forallP/(_ x)/forall_inP->.
Qed.

Fact cfun_zero_subproof : is_class_fun G (0 : {ffun _}).
Proof. exact: intro_class_fun. Qed.
Definition cfun_zero := Cfun 0 cfun_zero_subproof.

Fact cfun_comp_subproof f phi :
  f 0 = 0 -> is_class_fun G [ffun x => f (phi x)].
Proof.
by move=> f0; apply: intro_class_fun => [x y _ /cfunJgen | x /cfun0gen] ->.
Qed.
Definition cfun_comp f f0 phi := Cfun 0 (@cfun_comp_subproof f phi f0).
Definition cfun_opp := cfun_comp (oppr0 _).

Fact cfun_add_subproof phi psi : is_class_fun G [ffun x => phi x + psi x].
Proof.
apply: intro_class_fun => [x y Gx Gy | x notGx]; rewrite ?cfunJgen //.
by rewrite !cfun0gen ?add0r.
Qed.
Definition cfun_add phi psi := Cfun 0 (cfun_add_subproof phi psi).

Fact cfun_indicator_subproof (A : {set gT}) :
  is_class_fun G [ffun x => ((x \in G) && (x ^: G \subset A))%:R].
Proof.
apply: intro_class_fun => [x y Gx Gy | x /negbTE/= -> //].
by rewrite groupJr ?classGidl.
Qed.
Definition cfun_indicator A := Cfun 1 (cfun_indicator_subproof A).
Local Notation "''1_' A" := (cfun_indicator A) : ring_scope.

Lemma cfun1Egen x : '1_G x = (x \in G)%:R.
Proof. by rewrite cfunElock andb_idr // => /class_subG->. Qed.

Fact cfun_mul_subproof phi psi : is_class_fun G [ffun x => phi x * psi x].
Proof.
apply: intro_class_fun => [x y Gx Gy | x notGx]; rewrite ?cfunJgen //.
by rewrite cfun0gen ?mul0r.
Qed.
Definition cfun_mul phi psi := Cfun 0 (cfun_mul_subproof phi psi).

Definition cfun_unit :=
  [pred phi : classfun | forallb x, (x \in G) ==> (phi x != 0)].
Definition cfun_inv phi :=
  if phi \in cfun_unit then cfun_comp (invr0 _) phi else phi.

Definition cfun_scale a := cfun_comp (mulr0 a).

Fact cfun_addA : associative cfun_add.
Proof. by move=> phi psi xi; apply/cfunP=> x; rewrite !cfunE addrA. Qed.
Fact cfun_addC : commutative cfun_add.
Proof. by move=> phi psi; apply/cfunP=> x; rewrite !cfunE addrC. Qed.
Fact cfun_add0 : left_id cfun_zero cfun_add.
Proof. by move=> phi; apply/cfunP=> x; rewrite !cfunE add0r. Qed.
Fact cfun_addN : left_inverse cfun_zero cfun_opp cfun_add.
Proof. by move=> phi; apply/cfunP=> x; rewrite !cfunE addNr. Qed.

Definition cfun_zmodMixin := ZmodMixin cfun_addA cfun_addC cfun_add0 cfun_addN.
Canonical cfun_zmodType := ZmodType classfun cfun_zmodMixin.

Lemma muln_cfunE phi n x : (phi *+ n) x = phi x *+ n.
Proof. by elim: n => [|n IHn]; rewrite ?mulrS !cfunE ?IHn. Qed.

Lemma sum_cfunE I r (P : pred I) (phi : I -> classfun) x :
  (\sum_(i <- r | P i) phi i) x = \sum_(i <- r | P i) (phi i) x.
Proof. by elim/big_rec2: _ => [|i _ psi _ <-]; rewrite cfunE. Qed.

Fact cfun_mulA : associative cfun_mul.
Proof. by move=> phi psi xi; apply/cfunP=> x; rewrite !cfunE mulrA. Qed.
Fact cfun_mulC : commutative cfun_mul.
Proof. by move=> phi psi; apply/cfunP=> x; rewrite !cfunE mulrC. Qed.
Fact cfun_mul1 : left_id '1_G cfun_mul.
Proof.
by move=> phi; apply: cfun_in_genP => x Gx; rewrite !cfunE cfun1Egen Gx mul1r.
Qed.
Fact cfun_mulD : left_distributive cfun_mul cfun_add.
Proof. by move=> phi psi xi; apply/cfunP=> x; rewrite !cfunE mulr_addl. Qed.
Fact cfun_nz1 : '1_G != 0.
Proof.
by apply/eqP=> /cfunP/(_ 1%g)/eqP; rewrite cfun1Egen cfunE group1 oner_eq0.
Qed.

Definition cfun_ringMixin :=
  ComRingMixin cfun_mulA cfun_mulC cfun_mul1 cfun_mulD cfun_nz1.
Canonical cfun_ringType := RingType classfun cfun_ringMixin.
Canonical cfun_comRingType := ComRingType classfun cfun_mulC.

Fact cfun_mulV : {in cfun_unit, left_inverse 1 cfun_inv *%R}.
Proof.
move=> phi Uphi; rewrite /cfun_inv Uphi; apply/cfun_in_genP=> x Gx.
by rewrite !cfunE cfun1Egen Gx mulVf ?(forall_inP Uphi).
Qed.
Fact cfun_unitP phi psi : psi * phi = 1 -> phi \in cfun_unit.
Proof.
move/cfunP=> phiK; apply/forall_inP=> x Gx; rewrite -unitfE; apply/unitrP.
by exists (psi x); have:= phiK x; rewrite !cfunE cfun1Egen Gx mulrC.
Qed.
Fact cfun_inv0id : {in [predC cfun_unit], cfun_inv =1 id}.
Proof. by rewrite /cfun_inv => phi /negbTE/= ->. Qed.

Definition cfun_unitMixin := ComUnitRingMixin cfun_mulV cfun_unitP cfun_inv0id.
Canonical cfun_unitRingType := UnitRingType classfun cfun_unitMixin.
Canonical cfun_comUnitRingType := [comUnitRingType of classfun].

Fact cfun_scaleA a b phi :
  cfun_scale a (cfun_scale b phi) = cfun_scale (a * b) phi.
Proof. by apply/cfunP=> x; rewrite !cfunE mulrA. Qed.
Fact cfun_scale1 : left_id 1 cfun_scale.
Proof. by move=> phi; apply/cfunP=> x; rewrite !cfunE mul1r. Qed.
Fact cfun_scaleDr : right_distributive cfun_scale +%R.
Proof. by move=> a phi psi; apply/cfunP=> x; rewrite !cfunE mulr_addr. Qed.
Fact cfun_scaleDl phi : {morph cfun_scale^~ phi : a b / a + b}.
Proof. by move=> a b; apply/cfunP=> x; rewrite !cfunE mulr_addl. Qed.

Definition cfun_lmodMixin :=
  LmodMixin cfun_scaleA cfun_scale1 cfun_scaleDr cfun_scaleDl.
Canonical cfun_lmodType := LmodType algC classfun cfun_lmodMixin.

Fact cfun_scaleAl a phi psi : a *: (phi * psi) = (a *: phi) * psi.
Proof. by apply/cfunP=> x; rewrite !cfunE mulrA. Qed.
Fact cfun_scaleAr a phi psi : a *: (phi * psi) = phi * (a *: psi).
Proof. by rewrite !(mulrC phi) cfun_scaleAl. Qed.

Canonical cfun_lalgType := LalgType algC classfun cfun_scaleAl.
Canonical cfun_algType := AlgType algC classfun cfun_scaleAr.
Canonical cfun_unitAlgType := [unitAlgType algC of classfun].

Section Automorphism.

Variable u : {rmorphism algC -> algC}.

Definition cfunAut := cfun_comp (rmorph0 u).

Lemma cfunAut1i A : cfunAut '1_A = '1_A.
Proof. by apply/cfunP=> x; rewrite !cfunElock rmorph_nat. Qed.

Lemma cfunAutZ a phi : cfunAut (a *: phi) = u a *: cfunAut phi.
Proof. by apply/cfunP=> x; rewrite !cfunE rmorphM. Qed.

Lemma cfunAut_is_rmorphism : rmorphism cfunAut.
Proof.
by do 2?split=> [phi psi|]; last exact: cfunAut1i;
   apply/cfunP=> x; rewrite !cfunE (rmorph_sub, rmorphM).
Qed.
Canonical cfunAut_additive := Additive cfunAut_is_rmorphism.
Canonical cfunAut_rmorhism := RMorphism cfunAut_is_rmorphism.

End Automorphism.

Definition cfun_v2rV phi := \row_(i < #|classes G|) phi (repr (enum_val i)).
Fact cfun_v2rV_linear : linear cfun_v2rV.
Proof. by move=> a phi psi; apply/rowP=> i; rewrite !(mxE, cfunE). Qed.
Fact cfun_v2rV_bij : bijective cfun_v2rV.
Proof.
set n := #|_|; pose eK x : 'I_n := enum_rank_in (classes1 _) (x ^: G).
have rV2vP v : is_class_fun G [ffun x => v (eK x) *+ (x \in G)].
  apply: intro_class_fun => [x y Gx Gy | x /negbTE/=-> //].
  by rewrite groupJr // /eK classGidl.
exists (fun v : 'rV_n => Cfun 0 (rV2vP (v 0))) => [phi | v].
  apply/cfun_in_genP=> x Gx; rewrite cfunE Gx mxE enum_rankK_in ?mem_classes //.
  by have [y Gy ->] := repr_class <<B>> x; rewrite cfunJgen.
apply/rowP=> i; rewrite mxE cfunE; have /imsetP[x Gx def_i] := enum_valP i.
rewrite def_i; have [y Gy ->] := repr_class <<B>> x.
by rewrite groupJ // /eK classGidl // -def_i enum_valK_in.
Qed.

Definition cfun_vectMixin := VectMixin cfun_v2rV_linear cfun_v2rV_bij.
Canonical cfun_vectType := VectType algC cfun_vectMixin.
Canonical cfun_fAlgType := AlgFType algC cfun_vectMixin.

Definition base_cfun A : #|classes B ::&: A|.-tuple classfun :=
  [tuple of [seq ('1_xB)%R | xB <- enum (classes B ::&: A)]].
Definition classfun_on A := span (base_cfun A).

Definition cfdot phi psi := #|B|%:R^-1 * \sum_(x \in B) phi x * (psi x)^*.
Definition cfdotr_head k psi phi := let: tt := k in cfdot phi psi.

End Defs.

Bind Scope character_scope with classfun.

Arguments Scope classfun [_ group_scope].
Arguments Scope classfun_on [_ group_scope group_scope].
Arguments Scope cfun_indicator [_ group_scope].
Arguments Scope cfunAut [_ group_scope _ character_scope].
Arguments Scope cfdot [_ group_scope character_scope character_scope].
Arguments Scope cfdotr_head [_ group_scope _ character_scope character_scope].

Notation "''CF' ( G )" := (classfun G) : type_scope.
Notation "''CF' ( G )" := (fullv (cfun_vectType G)) : vspace_scope.
Notation "''1_' A" := (cfun_indicator _ A) : ring_scope.
Notation "''CF' ( G , A )" := (classfun_on G A) : ring_scope.
Notation "phi ^*" := (cfunAut conjC phi) : character_scope.

Notation "''[' u , v ]_ G":=  (@cfdot _ G u v) (only parsing) : ring_scope.
Notation "''[' u , v ]" := (cfdot u v) : ring_scope.
Notation "''[' u ]_ G" := '[u, u]_G (only parsing) : ring_scope.
Notation "''[' u ]" := '[u, u] : ring_scope.
Notation cfdotr := (cfdotr_head tt).

(* Before section so the nosimple does not get "cooked" out. *)
Definition orthogonal (gT : finGroupType) (D : {set gT}) (S R : seq 'CF(D)) :=
  nosimpl (all [pred phi | all [pred psi | '[phi, psi] == 0] R] S).

Coercion seq_of_cfun (gT : finGroupType) (D : {set gT}) (phi : 'CF(D)) :=
  [:: phi].

Section Predicates.

Variables (gT rT : finGroupType) (D : {set gT}) (R : {set rT}).
Implicit Types (phi psi : 'CF(D)) (S : seq 'CF(D)) (tau : 'CF(D) -> 'CF(R)).

Definition cfker phi := [set x \in D | forallb y, phi (x * y)%g == phi y].

Definition cfaithful phi := cfker phi \subset [1].

(* We exclude 0 from pairwise orthogonal sets. *)
Fixpoint pairwise_orthogonal S := 
  if S is psi :: S' then
    [&& psi != 0, orthogonal psi S' & pairwise_orthogonal S']
  else true.

Definition orthonormal S :=
  all [pred psi | '[psi] == 1] S && pairwise_orthogonal S.

Definition conjC_closed S :=
  {in S, forall phi, (phi^*)%CH \in [predD1 S & phi]}.

Definition isometry tau := forall phi psi, '[tau phi, tau psi] = '[phi, psi].

Definition isometry_from_to mCFD tau mCFR :=
   prop_in2 mCFD (inPhantom (isometry tau))
  /\ prop_in1 mCFD (inPhantom (forall phi, in_mem (tau phi) mCFR)).

End Predicates.

Arguments Scope cfker [_ group_scope character_scope].
Arguments Scope cfaithful [_ group_scope character_scope].
Arguments Scope orthogonal [_ group_scope character_scope character_scope].
Arguments Scope pairwise_orthogonal [_ group_scope character_scope].
Arguments Scope orthonormal [_ group_scope character_scope].
Arguments Scope isometry [_ _ group_scope group_scope character_scope].

Notation "{ 'in' CFD , 'isometry' tau , 'to' CFR }" :=
    (isometry_from_to (mem CFD) tau (mem CFR))
  (at level 0, format "{ 'in'  CFD ,  'isometry'  tau ,  'to'  CFR }")
     : type_scope.

Section ClassFun. 

Variables (gT : finGroupType) (G : {group gT}).
Implicit Types (A B : {set gT}) (H K : {group gT}) (phi psi xi : 'CF(G)).

Local Notation "''1_' A" := (cfun_indicator G A).

Lemma cfun0 phi x : x \notin G -> phi x = 0.
Proof. by rewrite -{1}(genGid G) => /(cfun0gen phi). Qed.

Lemma support_cfun phi : support phi \subset G.
Proof. by apply/subsetP=> g; apply: contraR => /cfun0->. Qed.

Lemma cfunJ phi x y : y \in G -> phi (x ^ y) = phi x.
Proof. by rewrite -{1}(genGid G) => /(cfunJgen phi)->. Qed.

Lemma cfun_repr phi x : phi (repr (x ^: G)) = phi x.
Proof. by have [y Gy ->] := repr_class G x; exact: cfunJ. Qed.

Lemma cfun_inP phi psi : {in G, phi =1 psi} -> phi = psi.
Proof. by rewrite -{1}genGid => /cfun_in_genP. Qed.

Lemma cfuniE A x : A <| G -> '1_A x = (x \in A)%:R.
Proof.
case/andP=> sAG nAG; rewrite cfunElock genGid.
by rewrite class_sub_norm // andb_idl // => /(subsetP sAG).
Qed.

Lemma cfun_classE x y : '1_(x ^: G) y = ((x \in G) && (y \in x ^: G))%:R.
Proof.
rewrite cfunElock genGid class_sub_norm ?class_norm //; congr (_ : bool)%:R.
by apply: andb_id2r => /imsetP[z Gz ->]; rewrite groupJr.
Qed.

Lemma cfuni1 : '1_G = 1.
Proof. by rewrite -[G in '1_G]genGid. Qed.

Lemma cfun1E g : (1 : 'CF(G)) g = (g \in G)%:R.
Proof. by rewrite -cfuni1 cfuniE. Qed.

Lemma support_cfuni A : A <| G -> support '1_A =i A.
Proof. by move=> nsAG x; rewrite !inE cfuniE // -(eqN_eqC _ 0) -lt0n lt0b. Qed.

Lemma cfuniM A B : '1_A * '1_B = '1_(A :&: B) :> 'CF(G).
Proof.
apply/cfunP=> g; rewrite !cfunElock -natr_mul mulnb subsetI.
by rewrite andbCA !andbA andbb.
Qed.

Lemma cfun_onE A :
  'CF(G, A) = (\sum_(xG \in classes G | xG \subset A) ('1_xG)%:VS)%VS.
Proof.
by rewrite ['CF(G, A)]big_map big_filter; apply: eq_bigl => xG; rewrite !inE.
Qed.

Lemma cfun_memfP A phi :
  reflect (forall x, x \notin A -> phi x = 0) (phi \in 'CF(G, A)).
Proof.
apply: (iffP idP) => [/coord_span-> x notAx | Aphi].
  set b := base_cfun G A; rewrite sum_cfunE big1 // => i _; rewrite cfunE.
  have /mapP[xG]: b`_i \in b by rewrite -tnth_nth mem_tnth.
  rewrite mem_enum => /setIdP[/imsetP[y Gy ->] Ay] ->.
  by rewrite cfun_classE Gy (contraNF (subsetP Ay x)) ?mulr0.
suffices <-: \sum_(xG \in classes G) phi (repr xG) *: '1_xG = phi.
  apply: memv_suml => _ /imsetP[x Gx ->]; rewrite memvZ cfun_repr.
  have [s_xG_A | /subsetPn[_ /imsetP[y Gy ->]]] := boolP (x ^: G \subset A).
    by rewrite cfun_onE [_ \in _](sumv_sup (x ^: G)) ?mem_classes ?orbT.
  by move/Aphi; rewrite cfunJ // => ->; rewrite eqxx.
apply/cfun_inP=> x Gx; rewrite sum_cfunE (bigD1 (x ^: G)) ?mem_classes //=.
rewrite cfunE cfun_repr cfun_classE Gx class_refl mulr1.
rewrite big1 ?addr0 // => _ /andP[/imsetP[y Gy ->]]; apply: contraNeq.
rewrite cfunE cfun_repr cfun_classE Gy mulf_eq0 => /norP[_].
by rewrite -(eqN_eqC _ 0) -lt0n lt0b => /class_transr->.
Qed.
Implicit Arguments cfun_memfP [A phi].

Lemma cfunS0 A phi x : phi \in 'CF(G, A) -> x \notin A -> phi x = 0.
Proof. by move/cfun_memfP; exact. Qed.

Lemma cfun_sum (F : gT -> algC) :
    {in G &, forall g h, F (g ^ h) = F g} ->
  \sum_(g \in G) F g = \sum_(xG \in classes G) #|xG|%:R * F (repr xG).
Proof.
move=> FJ; rewrite {1}(partition_big _  _ ((@mem_classes gT)^~ G)) /=.
apply: eq_bigr => _ /imsetP[x Gx ->]; have [y Gy ->] := repr_class G x.
rewrite mulr_natl -sumr_const FJ {y Gy}//; apply/esym/eq_big=> y /=.
  apply/idP/andP=> [xGy | [Gy /eqP<-]]; last exact: class_refl.
  by rewrite (class_transr xGy) (subsetP (class_subG Gx (subxx _))).
by case/imsetP=> z Gz ->; rewrite FJ.
Qed.

Lemma cfun_free A : free (base_cfun G A).
Proof.
have b_i (i : 'I_#|classes G ::&: A|) : (base_cfun G A)`_i = '1_(enum_val i).
  by rewrite /enum_val -!tnth_nth tnth_map.
apply/freeP => s S0 i; move/cfunP/(_ (repr (enum_val i))): S0.
rewrite sum_cfunE (bigD1 i) //= big1 ?addr0 => [|j].
  rewrite b_i !cfunE; have /setIdP[/imsetP[x Gx ->] _] := enum_valP i.
  by rewrite cfun_repr cfun_classE Gx class_refl mulr1.
apply: contraNeq; rewrite b_i !cfunE mulf_eq0 => /norP[_].
rewrite -(inj_eq (@enum_val_inj _ _)).
have /setIdP[/imsetP[x _ ->] _] := enum_valP i; rewrite cfun_repr.
have /setIdP[/imsetP[y Gy ->] _] := enum_valP j; rewrite cfun_classE Gy.
by rewrite -(eqN_eqC _ 0) -lt0n lt0b => /class_transr->.
Qed.

Lemma dim_cfun : \dim 'CF(G) = #|classes G|.
Proof. by rewrite dimvf /vdim //= genGid. Qed.

(* cfun and support *)

Lemma support1 A : support '1_A \subset A.
Proof.
apply/supportP=> x notAx; rewrite cfunElock genGid.
by case: andP => // [[_ s_xG_A]]; rewrite (subsetP s_xG_A) ?class_refl in notAx.
Qed.

Lemma memcE phi A : (phi \in 'CF(G, A)) = (support phi \subset A).
Proof. exact: (sameP cfun_memfP supportP). Qed.

Lemma memc_support phi A : phi \in 'CF(G, A) -> support phi \subset A.
Proof. by rewrite memcE. Qed.

Lemma memc_subset A B phi :
  B \subset A -> phi \in 'CF(G, B) -> phi \in 'CF(G, A).
Proof. by rewrite !memcE => sBA /subset_trans->. Qed.

Lemma cfun_conjCE phi x : (phi^*)%CH x = (phi x)^*.
Proof. by rewrite cfunE. Qed.

Lemma cfun_conjCK : involutive (fun phi => phi^*)%CH.
Proof. by move=> phi; apply/cfunP=> x; rewrite !cfunE conjCK. Qed.

Lemma cfun_conjC1 : (1^*)%CH = 1 :> 'CF(G).
Proof. exact: rmorph1. Qed.

(* Class function kernel and faithful class functions *)

Fact cfker_is_group phi : group_set (cfker phi).
Proof.
apply/group_setP; split=> [|x y]; rewrite !inE ?group1.
  by apply/forallP=> y; rewrite mul1g.
case/andP=> Gx /forallP Kx /andP[Gy /forallP Ky]; rewrite groupM //.
by apply/forallP=> z; rewrite -mulgA (eqP (Kx _)) Ky.
Qed.
Canonical cfker_group phi := Group (cfker_is_group phi).

Lemma cfker_sub phi : cfker phi \subset G.
Proof. by rewrite /cfker setIdE subsetIl. Qed.

Lemma cfker_norm phi : G \subset 'N(cfker phi).
Proof.
apply/subsetP=> z Gz; have phiJz := cfunJ phi _ (groupVr Gz).
rewrite inE; apply/subsetP=> _ /imsetP[x /setIdP[Gx /forallP Kx] ->].
rewrite inE groupJ //; apply/forallP=> y.
by rewrite -(phiJz y) -phiJz conjMg conjgK Kx.
Qed.

Lemma cfker_normal phi : cfker phi <| G.
Proof. by rewrite /normal cfker_sub cfker_norm. Qed.

Lemma cfkerMl phi x y : x \in cfker phi -> phi (x * y)%g = phi y.
Proof. by case/setIdP=> _ /forallP/(_ y)/eqP. Qed.

Lemma cfkerMr phi x y : x \in cfker phi -> phi (y * x)%g = phi y.
Proof.
by move=> Kx; rewrite conjgC cfkerMl ?cfunJ ?(subsetP (cfker_sub phi)).
Qed.

Lemma cfker1 phi x : x \in cfker phi -> phi x = phi 1%g.
Proof. by move=> Kx; rewrite -[x]mulg1 cfkerMl. Qed.

Lemma cfker_constant H phi (Hx : coset_of H) :
  H \subset cfker phi -> Hx \subset [set y | phi y == phi (repr Hx)].
Proof.
move/subsetP=> sHK; rewrite -{1}(coset_reprK Hx) val_coset ?repr_coset_norm //.
by apply/subsetP=> _ /rcosetP[y Hy ->]; rewrite inE cfkerMl ?sHK.
Qed.

Lemma cfker_cfun1 : @cfker _ G 1 = G.
Proof.
apply/setP=> x; rewrite !inE andb_idr // => Gx; apply/forallP=> y.
by rewrite !cfun1E groupMl.
Qed.

Lemma cfaithfulE phi : cfaithful phi = (cfker phi \subset [1]).
Proof. by []. Qed.

End ClassFun.

Arguments Scope classfun_on [_ group_scope group_scope].
Notation "''CF' ( G , A )" := (classfun_on G A) : ring_scope.

Implicit Arguments cfun_memfP [gT G A phi].

Section DotProduct.

Variable (gT : finGroupType) (G : {group gT}).
Implicit Types (phi psi xi : 'CF(G)) (R S : seq 'CF(G)).

Lemma cfdotE phi psi :
  '[phi, psi] = #|G|%:R^-1 * \sum_(x \in G) phi x * (psi x)^*.
Proof. by []. Qed.

Lemma cfdot1i A B :
  A <| G -> B <| G -> '['1_A, '1_B]_G = #|A :&: B|%:R / #|G|%:R.
Proof.
move=> nsAG nsBG; rewrite cfdotE mulrC (big_setID (A :&: B)) /=; congr (_ / _).
rewrite addrC big1 ?add0r => [|x /setDP[_]]; last first.
  by rewrite inE !cfuniE // rmorph_nat -natr_mul mulnb => /negbTE->.
rewrite (setIidPr _) ?subIset ?(normal_sub nsAG) // -sum1_card natr_sum.
by apply: eq_bigr => x /setIP[Ax Bx]; rewrite !cfuniE // Ax Bx rmorph1 mulr1.
Qed.

Lemma cfnorm1 : '[1]_G = 1.
Proof. by rewrite cfdot1i ?genGid // setIid divff ?neq0GC. Qed.

Lemma cfdotrE psi phi : cfdotr psi phi = '[phi, psi]. Proof. by []. Qed.

Lemma cfdotr_is_linear xi : linear (cfdotr xi : 'CF(G) -> algC^o).
Proof.
move=> a phi psi; rewrite scaler_mulr -mulr_addr; congr (_ * _).
rewrite linear_sum -big_split; apply: eq_bigr => x _ /=.
by rewrite !cfunE mulr_addl -mulrA.
Qed.
Canonical cfdotr_additive xi := Additive (cfdotr_is_linear xi).
Canonical cfdotr_linear xi := Linear (cfdotr_is_linear xi).

Lemma cfdot0l xi : '[0, xi] = 0.
Proof. by rewrite -cfdotrE linear0. Qed.
Lemma cfdotNl xi phi : '[- phi, xi] = - '[phi, xi].
Proof. by rewrite -!cfdotrE linearN. Qed.
Lemma cfdotDl xi phi psi : '[phi + psi, xi] = '[phi, xi] + '[psi, xi].
Proof. by rewrite -!cfdotrE linearD. Qed.
Lemma cfdot_subl xi phi psi : '[phi - psi, xi] = '[phi, xi] - '[psi, xi].
Proof. by rewrite -!cfdotrE linear_sub. Qed.
Lemma cfdotMnl xi phi n : '[phi *+ n, xi] = '[phi, xi] *+ n.
Proof. by rewrite -!cfdotrE linearMn. Qed.
Lemma cfdot_suml xi I r (P : pred I) (phi : I -> 'CF(G)) :
  '[\sum_(i <- r | P i) phi i, xi] = \sum_(i <- r | P i) '[phi i, xi].
Proof. by rewrite -!cfdotrE linear_sum. Qed.
Lemma cfdotZl xi a phi : '[a *: phi, xi] = a * '[phi, xi].
Proof. by rewrite -!cfdotrE linearZ. Qed.

Lemma cfdotC phi psi : '[phi, psi] = ('[psi, phi])^*.
Proof.
rewrite /cfdot rmorphM fmorphV rmorph_nat rmorph_sum; congr (_ * _).
by apply: eq_bigr=> x _; rewrite rmorphM conjCK mulrC.
Qed.
 
Lemma cfdot_subr xi phi psi : '[xi, phi - psi] = '[xi, phi] - '[xi, psi].
Proof. by rewrite !(cfdotC xi) -rmorph_sub cfdot_subl. Qed.
Canonical cfun_dot_additive xi := Additive (cfdot_subr xi).

Lemma cfdot0r xi : '[xi, 0] = 0. Proof. exact: raddf0. Qed.
Lemma cfdotNr xi phi : '[xi, - phi] = - '[xi, phi].
Proof. exact: raddfN. Qed.
Lemma cfdotDr xi phi psi : '[xi, phi + psi] = '[xi, phi] + '[xi, psi].
Proof. exact: raddfD. Qed.
Lemma cfdotMnr xi phi n : '[xi, phi *+ n] = '[xi, phi] *+ n.
Proof. exact: raddfMn. Qed.
Lemma cfdot_sumr xi I r (P : pred I) (phi : I -> 'CF(G)) :
  '[xi, \sum_(i <- r | P i) phi i] = \sum_(i <- r | P i) '[xi, phi i].
Proof. exact: raddf_sum. Qed.
Lemma cfdotZr a xi phi : '[xi, a *: phi] = a^* * '[xi, phi].
Proof. by rewrite !(cfdotC xi) cfdotZl rmorphM. Qed.

Lemma cfdot_cfunAut_r u phi psi : 
    {in [image psi of G], algC_Aut u} ->
  '[cfunAut u phi, cfunAut u psi] = u '[phi, psi].
Proof.
move=> uC; rewrite rmorphM fmorphV rmorph_nat rmorph_sum; congr (_ * _).
by apply: eq_bigr => x Gx; rewrite !cfunE rmorphM uC ?map_f ?mem_enum.
Qed.

Lemma cfdot_cfunAut u phi psi : 
  algC_Aut u -> '[cfunAut u phi, cfunAut u psi]_G = u '[phi, psi].
Proof. by move=> uC; rewrite cfdot_cfunAut_r // => a _. Qed.

Lemma conj_cfdot phi psi : '[phi, psi]^* = '[phi^*, psi^*].
Proof. by rewrite cfdot_cfunAut. Qed.

Lemma posC_cfnorm phi : 0 <= '[phi].
Proof.
by rewrite posC_mul ?posC_inv ?posC_nat ?posC_sum // => x _; exact: posC_pconj.
Qed.

Lemma cfnorm_eq0 phi : ('[phi] == 0) = (phi == 0).
Proof.
apply/idP/eqP=> [|->]; last by rewrite cfdot0r.
rewrite mulf_eq0 invr_eq0 (negbTE (neq0GC G)) /= => /eqP/posC_sum_eq0 phi0.
apply/cfun_inP=> x Gx; apply/eqP; rewrite cfunE -normC_eq0 sqrtC_eq0.
by rewrite phi0 // => y _; exact: posC_pconj.
Qed.

Lemma cfnormZ a phi : '[a *: phi]= `|a| ^+ 2 * '[phi]_G.
Proof. by rewrite cfdotZl cfdotZr mulrA normCK. Qed.

Lemma cfnormN phi : '[- phi] = '[phi].
Proof. by rewrite cfdotNl raddfN opprK. Qed.

Lemma cfnormD phi psi :
  let d := '[phi, psi] in '[phi + psi] = '[phi] + '[psi] + (d + d^*).
Proof. by rewrite /= addrAC -cfdotC cfdotDl !cfdotDr !addrA. Qed.

Lemma orthogonal_cons phi R S :
  orthogonal (phi :: R) S = orthogonal phi S && orthogonal R S.
Proof. by rewrite /orthogonal /= andbT. Qed.

Lemma orthogonal1P phi psi : reflect ('[phi, psi] = 0) (orthogonal phi psi).
Proof. rewrite /orthogonal /= !andbT; exact: eqP. Qed.

Lemma orthogonalP S R :
  reflect {in S & R, forall phi psi, '[phi, psi] = 0} (orthogonal S R).
Proof.
apply: (iffP allP) => oSR phi => [psi /oSR/allP opS /opS/eqP // | /oSR opS].
by apply/allP=> psi /= /opS->.
Qed.

Lemma orthogonal_sym : symmetric (@orthogonal _ G).
Proof.
apply: symmetric_from_pre => R S /orthogonalP oRS.
by apply/orthogonalP=> phi psi Rpsi Sphi; rewrite cfdotC oRS ?rmorph0.
Qed.

Lemma eq_orthogonal R1 R2 S1 S2 :
  R1 =i R2 -> S1 =i S2 -> orthogonal R1 S1 = orthogonal R2 S2.
Proof.
move=> eqR eqS; apply/orthogonalP/orthogonalP=> oRS phi psi;
  by rewrite ?eqR ?eqS => *; rewrite oRS ?eqR ?eqS.
Qed.

Lemma orthogonal_catl R1 R2 S :
  orthogonal (R1 ++ R2) S = orthogonal R1 S && orthogonal R2 S.
Proof. exact: all_cat. Qed.

Lemma orthogonal_catr R S1 S2 :
  orthogonal R (S1 ++ S2) = orthogonal R S1 && orthogonal R S2.
Proof. by rewrite !(orthogonal_sym R) orthogonal_catl. Qed.

Lemma pairwise_orthogonalP S :
  reflect (uniq (0 :: S)
             /\ {in S &, forall phi psi, phi != psi -> '[phi, psi] = 0})
          (pairwise_orthogonal S).
Proof.
elim: S => [|phi S IH] /=; first by left.
rewrite inE eq_sym /orthogonal /= andbT.
have [_ | /= nz_phi] := altP eqP; first by right; case.
have [opS | not_opS] := altP allP; last first.
  right=> [[/and3P[_ notSp _] opS]].
  have [psi Spsi /eqP[]] := allPn not_opS.
  by rewrite opS ?mem_head 1?mem_behead //; apply: contraNneq notSp => ->.
have -> /=: (phi \notin S).
  by apply: contra nz_phi => /opS /=; rewrite cfnorm_eq0.
apply: (iffP IH) => [] [uniqS oSS]; last first.
  by split=> // psi xi Spsi Sxi; apply: oSS; exact: mem_behead.
split=> // psi xi /predU1P[-> // | ].
  by case/predU1P=> [-> | /opS] /eqP.
move=> Spsi /predU1P[-> _ | Sxi /oSS-> //]; move/opS/eqP: Spsi => o_phi_psi.
by rewrite cfdotC o_phi_psi rmorph0.
Qed.

Lemma pairwise_orthogonal_cat R S :
  pairwise_orthogonal (R ++ S) =
    [&& pairwise_orthogonal R, pairwise_orthogonal S & orthogonal R S].
Proof.
elim: R => [|phi R /= ->]; rewrite ?andbT //.
(* ssreflect 1.3 pl2 regression here
by rewrite orthogonal_cons orthogonal_catr -!andbA; do !bool_congr. *)
rewrite orthogonal_cons orthogonal_catr -!andbA /=.
by congr [&& _, _ & _]; case: (all _ _); rewrite ?andbF.
Qed.

Lemma cfnorm_orthogonal S :
  pairwise_orthogonal S -> '[\sum_(phi <- S) phi] = \sum_(phi <- S) '[phi].
Proof.
case/pairwise_orthogonalP=> [/=/andP[_ uniqS] oSS].
rewrite raddf_sum /= !(big_tnth _ _ S); apply: eq_bigr => i _.
rewrite cfdot_suml (bigD1 i) // big1 /= ?addr0 // => j neq_ji.
by rewrite !(tnth_nth 0) /= oSS ?mem_nth ?nth_uniq.
Qed.

Lemma orthogonal_free S : pairwise_orthogonal S -> free S.
Proof.
case/pairwise_orthogonalP=> [/=/andP[notS0 uniqS] oSS].
apply/(freeP (in_tuple S)) => a aS0 i; have S_i: S`_i \in S by exact: mem_nth.
have /eqP: '[S`_i, 0]_G = 0 := cfdot0r _.
rewrite -{2}aS0 raddf_sum /= (bigD1 i) //= big1 => [|j neq_ji]; last 1 first.
  by rewrite cfdotZr oSS ?mulr0 ?mem_nth // eq_sym nth_uniq.
rewrite addr0 cfdotZr mulf_eq0 conjC_eq0 cfnorm_eq0.
by case/pred2P=> // Si0; rewrite -Si0 S_i in notS0.
Qed.

Lemma orthonormal_cat R S :
  orthonormal (R ++ S) = [&& orthonormal R, orthonormal S & orthogonal R S].
Proof.
by rewrite /orthonormal pairwise_orthogonal_cat all_cat -!andbA; do !bool_congr.
Qed.

Lemma orthonormal_orthogonal S : orthonormal S -> pairwise_orthogonal S.
Proof. by case/andP. Qed.

Lemma orthonormal_free S : orthonormal S -> free S.
Proof. by move/orthonormal_orthogonal/orthogonal_free. Qed.

Lemma orthonormalP S :
  reflect (uniq S /\ {in S &, forall phi psi, '[phi, psi]_G = (phi == psi)%:R})
          (orthonormal S).
Proof.
rewrite /orthonormal; have [normS | not_normS] := altP allP; last first.
  right=> [[_ o1S]]; have [phi Sphi /eqP[]] := allPn not_normS.
  by rewrite o1S ?eqxx.
apply: (iffP (pairwise_orthogonalP S)) => [] [uniqS oSS].
  split=> // [|phi psi]; first by case/andP: uniqS.
  by have [-> _ /normS/eqP | /oSS] := altP eqP.
split=> // [|phi psi Sphi Spsi /negbTE]; last by rewrite oSS // => ->.
rewrite /= uniqS andbT; apply/negP=> S_0.
by move/eqP: (oSS 0 0 S_0 S_0); rewrite cfdot0r eq_sym eqxx oner_eq0.
Qed.

Lemma cfun_conjC_Z a phi : ((a *: phi)^*)%CH = a^* *: (phi^*)%CH.
Proof. by apply/cfunP=> x; rewrite !cfunE rmorphM. Qed.

Lemma conjC_closed_not0 S : conjC_closed S -> 0 \notin S.
Proof. by move=> clC_S; rewrite (contra (clC_S 0)) // rmorph0 !inE eqxx. Qed.

End DotProduct.

Section Restrict.

Variables (gT : finGroupType) (A B : {set gT}).
Local Notation H := <<A>>.
Local Notation G := <<B>>.

Fact cfunRes_subproof (phi : 'CF(B)) :
  is_class_fun H [ffun x => phi x *+ ((x \in H) && (H \subset G))].
Proof.
apply: intro_class_fun => /= [x y Hx Hy | x /negbTE/=-> //].
by rewrite Hx groupJ //; case: subsetP => // sHG; rewrite cfunJgen ?sHG.
Qed.
Definition cfunRes phi := Cfun 1 (cfunRes_subproof phi).

Lemma cfunResE phi : A \subset B -> {in A, cfunRes phi =1 phi}.
Proof. by move=> sAB x Ax; rewrite cfunElock mem_gen ?genS. Qed.
 
Lemma cfunRes_is_linear : linear cfunRes.
Proof.
by move=> a phi psi; apply/cfunP=> x; rewrite !cfunElock mulrnAr mulrn_addl.
Qed.
Canonical cfunRes_additive := Additive cfunRes_is_linear.
Canonical cfunRes_linear := Linear cfunRes_is_linear.

Lemma cfunRes1 : A \subset B -> cfunRes 1 = 1.
Proof.
move/genS=> sHG; apply: cfun_in_genP => x Hx.
by rewrite cfunElock Hx sHG !cfun1Egen Hx (subsetP sHG).
Qed.

End Restrict.

Arguments Scope cfunRes [_ group_scope group_scope character_scope].
Notation "''Res[' H , G ]" := (@cfunRes _ H G) (only parsing) : ring_scope.
Notation "''Res[' H ]" := 'Res[H, _] : ring_scope.
Notation "''Res'" := 'Res[_] (only parsing) : ring_scope.

Section MoreRestrict.

Variables (gT : finGroupType) (G H : {group gT}) (A : {set gT}).

Lemma cfunRes_subset (phi : 'CF(G)) :
  A \subset H -> H \subset G -> 'Res[A] ('Res[H] phi) = 'Res[A] phi.
Proof.
move=> sAH sHG; apply/cfunP=> x; rewrite !cfunElock !genGid !gen_subG sAH sHG.
rewrite (subset_trans sAH) // !andbT -mulrnA mulnb.
by rewrite (andb_idl (subsetP _ x)) ?gen_subG.
Qed.

Lemma cfunRes_id phi : 'Res[A] phi = phi.
Proof. by apply/cfun_in_genP=> x Gx; rewrite cfunElock Gx subxx. Qed.

End MoreRestrict.

Section Morphim.

Variables (aT rT : finGroupType) (G D : {group aT}) (f : {morphism D >-> rT}).

Fact cfunMorph_subproof (phi : 'CF(f @* G)) :
  is_class_fun <<G>> [ffun x => phi (f x) *+ ((x \in G) && (G \subset D))].
Proof.
rewrite genGid; apply: intro_class_fun => [x y Gx Gy | x /negbTE/= ->//].
rewrite Gx groupJ //; case dG: (G \subset D) => //.
by rewrite morphJ ?cfunJ ?mem_morphim ?(subsetP dG).
Qed.
Definition cfunMorph phi := Cfun 1 (cfunMorph_subproof phi).

Lemma cfunMorphE phi x : G \subset D -> x \in G -> cfunMorph phi x = phi (f x).
Proof. by rewrite cfunElock => -> ->. Qed.

Fact cfunMorph_is_linear : linear cfunMorph.
Proof.
by move=> a phi psi; apply/cfunP=> x; rewrite !cfunElock mulrnAr -mulrn_addl.
Qed.
Canonical cfunMorph_additive := Additive cfunMorph_is_linear.
Canonical cfunMorph_linear := Linear cfunMorph_is_linear.

Lemma cfunMorph1 : G \subset D -> cfunMorph 1 = 1.
Proof.
move=> dG; apply/cfun_inP=> x Gx.
by rewrite cfunMorphE // !cfun1E /= morphimEsub // mem_imset Gx.
Qed.

End Morphim.

Prenex Implicits cfunMorph.

Section Coset.

Variables (gT : finGroupType) (G : {group gT}) (B : {set gT}).
Implicit Type rT : finGroupType.
Local Notation H := <<B>>%g.

Definition ffun_Quo (phi : 'CF(G)) :=
  [ffun Bx : coset_of B => phi (repr Bx) *+ [&& B <| G & B \subset cfker phi]].
Fact cfunQuo_subproof phi : is_class_fun <<G / B>> (ffun_Quo phi).
Proof.
rewrite genGid; apply: intro_class_fun => [|Hx].
  move=> _ _ /morphimP[x Nx _ ->] /morphimP[z Nz Gz ->].
  rewrite -morphJ ?val_coset_prim ?groupJ // -gen_subG andbC.
  have [sHK | //] := altP subsetP; do 2!case: repr_rcosetP => _ /sHK/cfkerMl->.
  by rewrite cfunJ.
have [x Nx -> notGx] := cosetP Hx; rewrite -gen_subG val_coset_prim // andbC.
have [sHK | //] := altP subsetP; case: repr_rcosetP => _ /sHK/cfkerMl->.
by rewrite cfun0 ?mul0rn //; apply: contra notGx; exact: mem_morphim.
Qed.
Definition cfunQuo phi := Cfun 1 (cfunQuo_subproof phi).

Definition cfunMod : 'CF(G / B) -> 'CF(G) := @cfunMorph _ _ _ _ _.

Local Notation "phi /  'B'" := (cfunQuo phi) (at level 40) : character_scope.
Local Notation "phi %%  'B'" := (cfunMod phi) (at level 40) : character_scope.

Lemma cfunQuoE (phi : 'CF(G)) x :
  B <| G -> B \subset cfker phi -> x \in G -> (phi / B)%CH (coset B x) = phi x.
Proof.
rewrite cfunElock -gen_subG => nsBG sHK Gx; rewrite nsBG sHK.
rewrite val_coset_prim ?(subsetP (normal_norm nsBG)) //.
by case: repr_rcosetP => _ /(subsetP sHK)/cfkerMl->.
Qed.

Lemma cfunModE phi x : B <| G -> x \in G -> (phi %% B)%CH x = phi (coset B x).
Proof. by move/normal_norm=> nBG; exact: cfunMorphE. Qed.

Canonical cfunMod_additive := [additive of cfunMod].
Canonical cfunMod_linear := [linear of cfunMod].

Lemma cfunMod1 : B <| G -> (1 %% B)%CH = 1.
Proof. by move/normal_norm=> nBG; exact: cfunMorph1. Qed.

(* cfunQuo is only linear on the class functions that have H in their kernel. *)

Lemma cfker_Morph rT (A D : {group gT}) (f : {morphism D >-> rT})
                  (phi : 'CF(f @* A)) :
  A \subset D -> 'ker_A f \subset cfker (cfunMorph phi).
Proof.
move=> dG; apply/subsetP=> x /setIP[Ax Kx]; rewrite inE Ax /=.
apply/forallP=> y; rewrite !cfunElock dG groupMl //= andbT !mulrb.
by case: ifP => // /(subsetP dG) Dy; rewrite mkerl.
Qed.

Lemma cfker_Mod (phi : 'CF(G / _)) : B <| G -> B \subset cfker (phi %% B).
Proof.
rewrite /normal -!(gen_subG B) => /andP[/setIidPr <- nBG].
by rewrite -(setIidPl nBG) setIAC -setIA -ker_coset_prim cfker_Morph.
Qed.

Lemma cfunModK (phi : 'CF(G / _)) : B <| G -> (phi %% B / B)%CH = phi.
Proof.
move=> nsBG; apply/cfun_inP=> _ /morphimP[x Nx Gx ->] //.
by rewrite cfunQuoE ?cfker_Mod ?cfunModE.
Qed.

Lemma cfunQuoK (phi : 'CF(G)) :
  B <| G -> B \subset cfker phi -> (phi / B %% B)%CH = phi.
Proof.
by move=> nsHG sHK; apply/cfun_inP=> x Gx; rewrite cfunModE ?cfunQuoE.
Qed.

End Coset.

Arguments Scope cfunQuo [_ subgroup_scope group_scope character_scope].
Arguments Scope cfunMod [_ subgroup_scope group_scope character_scope].
Notation "phi / H" := (cfunQuo H phi) : character_scope.
Notation "phi %% H" := (@cfunMod _ _ H phi) : character_scope.

Section Induced.

Variable gT : finGroupType.

Section Def.

Variables B A : {set gT}.
Local Notation G := <<B>>.
Local Notation H := <<A>>.

Definition ffun_cfInd (phi : 'CF(A)) :=
  [ffun x => #|A|%:R^-1 * (\sum_(y \in G) phi (x ^ y)) *+ (<<A>> \subset G)].

Fact cfunInd_subproof phi : is_class_fun G (ffun_cfInd phi).
Proof.
apply: intro_class_fun => [x y Gx Gy | x notGx //].
  congr (_ * _ *+ _); rewrite (reindex_inj (mulgI y^-1)%g) /=.
  apply: eq_big => [z | z Gz]; first by rewrite groupMl ?groupV.
  by rewrite -conjgM mulKVg.
case: subsetP => // sHG; rewrite big1 ?mulr0 // => y Gy.
by rewrite cfun0gen // (contra (sHG _)) // groupJr.
Qed.
Definition cfunInd phi := Cfun 1 (cfunInd_subproof phi).

Lemma cfunInd_is_linear : linear cfunInd.
Proof.
move=> c phi psi; apply/cfunP=> x.
rewrite !cfunElock -!mulrnAl mulrCA -mulr_addr /=; congr (_ * _).
by rewrite big_distrr -big_split /=; apply: eq_bigr => y Gy /=; rewrite !cfunE.
Qed.
Canonical cfunInd_additive := Additive cfunInd_is_linear.
Canonical cfunInd_linear := Linear cfunInd_is_linear.

End Def.

Local Notation "''Ind[' B , A ]" := (@cfunInd B A) : ring_scope.
Local Notation "''Ind[' B ]" := 'Ind[B, _] : ring_scope.

Variables G H : {group gT}.
Implicit Types (phi : 'CF(H)) (psi : 'CF(G)).

Lemma cfunIndE phi x :
  H \subset G -> 'Ind[G] phi x = #|H|%:R^-1 * (\sum_(y \in G) phi (x ^ y)).
Proof. by move=> sHG; rewrite cfunElock !genGid sHG. Qed.

Lemma support_Ind_normal phi : H <| G -> support ('Ind[G] phi) \subset H.
Proof.
case/andP=> sHG nHG; apply/supportP=> x notHx; rewrite cfunIndE //.
by rewrite big1 ?mulr0 // => y Gy; rewrite cfun0 // memJ_norm ?(subsetP nHG).
Qed.
 
Lemma cfunInd1 phi : H \subset G -> 'Ind[G] phi 1%g = #|G : H|%:R * phi 1%g.
Proof.
move=> sHG; rewrite cfunIndE //; apply: canLR (mulKf (neq0GC H)) _.
rewrite mulrA -natr_mul LaGrange // mulr_natl -sumr_const; apply: eq_bigr => x.
by rewrite conj1g.
Qed.

Lemma cfunInd_normal1 : H <| G -> 'Ind[G, H] 1 = #|G : H|%:R *: '1_H.
Proof.
move=> nsHG; have [sHG nHG] := andP nsHG.
apply/cfunP=> x; rewrite cfunIndE // cfunE cfuniE //.
apply: canLR (mulKf (neq0GC H)) _; rewrite mulrA -natr_mul LaGrange //.
rewrite mulr_natl -sumr_const; apply: eq_bigr => y Gy.
by rewrite cfun1E -{1}(normsP nHG y Gy) memJ_conjg.
Qed.

(* This is Isaacs, Lemma (5.2). *)
Lemma Frobenius_reciprocity phi psi : '[phi, 'Res[H] psi] = '['Ind[G] phi, psi].
Proof.
case sHG: (H \subset G); last first.
  rewrite /cfdot !big1 ?mulr0 // => x; rewrite cfunElock !genGid sHG ?mul0r //.
  by rewrite andbF conjC0 mulr0.
transitivity (#|H|%:R^-1 * \sum_(x \in G) phi x * (psi x)^*).
  rewrite (big_setID H) /= (setIidPr sHG) addrC big1 ?add0r; last first.
    by move=> x /setDP[_ /cfun0->]; rewrite mul0r.
  by congr (_ * _); apply: eq_bigr => x Hx; rewrite cfunResE.
set h' := _^-1; apply: canRL (mulKf (neq0GC G)) _.
transitivity (h' * \sum_(y \in G) \sum_(x \in G) phi (x ^ y) * (psi (x ^ y))^*).
  rewrite mulrCA mulr_natl -sumr_const; congr (_ * _); apply: eq_bigr => y Gy.
  by rewrite (reindex_acts 'J _ Gy) ?astabsJ ?normG.
rewrite exchange_big big_distrr; apply: eq_bigr => x _; rewrite cfunIndE //=.
by rewrite -mulrA big_distrl; congr (_ * _); apply: eq_bigr => y /(cfunJ psi)->.
Qed.
Definition cfdot_Res_r := Frobenius_reciprocity.

Lemma cfdot_Res_l psi phi : '['Res[H] psi, phi] = '[psi, 'Ind[G] phi].
Proof. by rewrite cfdotC cfdot_Res_r -cfdotC. Qed.

End Induced.

Arguments Scope cfunInd [_ group_scope group_scope character_scope].
Notation "''Ind[' G , H ]" := (@cfunInd _ G H) : ring_scope.
Notation "''Ind[' G ]" := (@cfunInd _ G _) : ring_scope.
Notation "''Ind'" := (@cfunInd _ _) (at level 0, only parsing) : ring_scope.

Section FieldAutomorphism.

Variables (u : {rmorphism algC -> algC}) (gT : finGroupType) (G H : {group gT}).
Local Notation "phi ^u" := (cfunAut u phi) (at level 3, format "phi ^u").

Lemma cfunAutRes (phi : 'CF(G)) : ('Res[H] phi)^u = 'Res phi^u.
Proof. by apply/cfunP=> x; rewrite !cfunElock rmorphMn. Qed.

Lemma cfker_Aut (phi : 'CF(G)) : cfker phi^u = cfker phi.
Proof.
apply/setP=> x; rewrite !inE; apply: andb_id2l => Gx.
by apply/forallP/forallP=> Kx y;
  have:= Kx y; rewrite !cfunE (inj_eq (fmorph_inj u)).
Qed.

Lemma cfunAutQuo (phi : 'CF(G)) : (phi / H)^u = (phi^u / H)%CH.
Proof. by apply/cfunP=> Hx; rewrite !cfunElock cfker_Aut rmorphMn. Qed.

Lemma cfunAutMod (phi : 'CF(G / H)) : (phi %% H)^u = (phi^u %% H)%CH.
Proof. by apply/cfunP=> x; rewrite !cfunElock rmorphMn. Qed.

Lemma cfunAutInd (phi : 'CF(H)) : ('Ind[G] phi)^u = 'Ind phi^u.
Proof.
apply/cfunP=> x; rewrite !cfunElock rmorphMn rmorphM fmorphV rmorph_nat.
by congr (_ * _ *+ _); rewrite rmorph_sum; apply: eq_bigr => y; rewrite !cfunE.
Qed.

End FieldAutomorphism.

Definition conj_cfunRes := cfunAutRes conjC.
Definition conj_cfunQuo := cfunAutQuo conjC.
Definition conj_cfunMod := cfunAutMod conjC.
Definition conj_cfunInd := cfunAutInd conjC.

Section Product.

Variable (gT : finGroupType) (G : {group gT}).

Lemma memc_prodI A B phi psi : 
  phi \in 'CF(G, A) -> psi \in 'CF(G, B) -> phi * psi \in 'CF(G, A :&: B).
Proof.
rewrite !memcE => Aphi Bpsi; apply/subsetP=> x; rewrite !inE cfunE mulf_eq0.
by case/norP=> /(subsetP Aphi)-> /(subsetP Bpsi).
Qed.

Lemma memc_prod A phi psi : 
  phi \in 'CF(G, A) -> psi \in 'CF(G, A) -> phi * psi \in 'CF(G, A).
Proof. by move=> Aphi Bpsi; rewrite -[A]setIid memc_prodI. Qed.

End Product.

Section DProduct. 

Variables (gT : finGroupType) (G K H : {group gT}).
Hypothesis KxH : K \x H = G.

Lemma sum_dprodl R idx (op : Monoid.com_law idx) (F : gT -> R) :
   \big[op/idx]_(g \in G) F g =
      \big[op/idx]_(k \in K) \big[op/idx]_(h \in H) F (k * h)%g.
Proof.
have /mulgmP/misomP[fM /isomP[injf im_f]] := KxH.
rewrite pair_big_dep (reindex_onto (morphm fM) (invm injf)); last first.
  by move=> u KHu; rewrite invmK ?im_f.
apply: eq_big => [[x y] | []//]; rewrite -in_setX.
apply/andP/idP=> [[Gfu f'fu] | KHu].
  by rewrite -(im_invm injf) -(eqP f'fu) mem_morphim //= im_f.
by rewrite -[in G in _ \in G]im_f mem_morphim ?invmE.
Qed.

Lemma sum_dprodr R idx (op : Monoid.com_law idx) (F : gT -> R) :
  \big[op/idx]_(g \in G) F g =
    \big[op/idx]_(h \in H) \big[op/idx]_(k \in K) F (k * h)%g.
Proof. by rewrite sum_dprodl exchange_big. Qed.

Let fP := misomP (introT mulgmP KxH).
Let f := morphm (tag fP).
Let injf : 'injm f := proj1 (isomP (tagged fP)).
Let im_f : f @* setX K H = G := proj2 (isomP (tagged fP)).
Fact dom_dprod_inv_morph : G \subset f @* setX K H. Proof. by rewrite im_f. Qed.
Definition dprod_inv_morph := restrm dom_dprod_inv_morph (invm injf).
Canonical dprod_inv_morphism := [morphism of dprod_inv_morph].
Local Notation f' := dprod_inv_morph.
Lemma im_dprod_inv_morph : f' @* G = setX K H.
Proof. by rewrite im_restrm -[G in _ @* G = _]im_f im_invm. Qed.
Local Notation im_f' := im_dprod_inv_morph.
Local Notation pK := (@fst gT gT).
Local Notation pH := (@snd gT gT).

Definition cfun_dprodl := cfunMorph \o cfunMorph \o 'Res[pK @* (f' @* G), K].
Definition cfun_dprodr := cfunMorph \o cfunMorph \o 'Res[pH @* (f' @* G), H].
Definition cfun_dprod phi psi := cfun_dprodl phi * cfun_dprodr psi.

Let imK : pK @* (f' @* G) \subset K.
Proof. by rewrite im_dprod_inv_morph morphim_fstX. Qed.

Let imH : pH @* (f' @* G) \subset H.
Proof. by rewrite im_dprod_inv_morph morphim_sndX. Qed.

Lemma cfun_dprod1r phi : cfun_dprod phi 1 = cfun_dprodl phi.
Proof.
by rewrite /cfun_dprod /cfun_dprodr /= cfunRes1 ?cfunMorph1 ?mulr1 ?subsetT.
Qed.

Lemma cfun_dprod1l psi : cfun_dprod 1 psi = cfun_dprodr psi.
Proof.
by rewrite /cfun_dprod /cfun_dprodl /= cfunRes1 ?cfunMorph1 ?mul1r ?subsetT.
Qed.

Lemma cfun_dprodE phi psi :
  {in K & H, forall h k, cfun_dprod phi psi (h * k)%g = phi h * psi k}.
Proof.
move=> k h Kk Hh /=; move def_u: (k, h) => u.
have ->: (k * h)%g = f u by rewrite -def_u.
have{Kk Hh} KHu: u \in setX K H by rewrite -def_u inE Kk Hh.
have Gfu: f u \in G by rewrite -im_f morphimEsub // mem_imset.
rewrite cfunE !cfunMorphE ?cfunResE ?subsetT ?mem_morphim ?in_setT //=.
by rewrite [f' _]invmE // -def_u.
Qed.

Lemma cfun_dprodEl phi :
  {in K & H, forall k h, cfun_dprodl phi (k * h)%g = phi k}.
Proof.
by move=> k h Kk Hh; rewrite -cfun_dprod1r cfun_dprodE // cfun1E Hh mulr1.
Qed.

Lemma cfun_dprodEr psi :
  {in K & H, forall k h, cfun_dprodr psi (k * h)%g = psi h}.
Proof.
by move=> k h Kk Hh; rewrite -cfun_dprod1l cfun_dprodE // cfun1E Kk mul1r.
Qed.

Lemma cfdot_dprod phi1 phi2 psi1 psi2 :
  '[cfun_dprod phi1 psi1, cfun_dprod phi2 psi2] = '[phi1, phi2] * '[psi1, psi2].
Proof.
rewrite !cfdotE mulrCA -mulrA mulrCA mulrA -invf_mul -natr_mul (dprod_card KxH).
congr (_ * _); rewrite big_distrl sum_dprodl /=; apply: eq_bigr => k Kk.
rewrite big_distrr; apply: eq_bigr => h Hh /=.
by rewrite mulrCA -mulrA -rmorphM mulrCA mulrA !cfun_dprodE.
Qed.

Canonical cfun_dprodl_additive := [additive of cfun_dprodl].
Canonical cfun_dprodl_linear := [linear of cfun_dprodl].
Canonical cfun_dprodr_additive := [additive of cfun_dprodr].
Canonical cfun_dprodr_linear := [linear of cfun_dprodr].

Lemma cfdot_dprodl : isometry cfun_dprodl.
Proof.
by move=> phi1 phi2; rewrite -!cfun_dprod1r cfdot_dprod cfnorm1 mulr1.
Qed.

Lemma cfdot_dprodr : isometry cfun_dprodr.
Proof.
by move=> psi1 psi2; rewrite -!cfun_dprod1l cfdot_dprod cfnorm1 mul1r.
Qed.

End DProduct.
