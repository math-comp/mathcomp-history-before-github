(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient finalg action.
Require Import gproduct zmodp commutator cyclic center pgroup sylow.
Require Import matrix vector algebra algC.

(******************************************************************************)
(* This file contains the basic theory of class functions:                    *)
(*          'CF(G) == the type of class functions on G : {group gT}, i.e.,    *)
(*                    which map gT to the type algC of complex algebraics,    *)
(*                    have support in G, and are constant on each conjugacy   *)
(*                    class of G. 'CF(G) implements the algebraType interface *)
(*                    of finite-dimensional F-algebras.                       *)
(*                    The identity 1 : 'CF(G) is the indicator function of G, *)
(*                    and (later) the principal character.                    *)
(*  --> The %CF scope (cfun_scope) is bound to the 'CF(_) types.              *)
(*       'CF(G)%VS == the (total) vector space of 'CF(G).                     *)
(*       'CF(G, A) == the subspace of functions in 'CF(G) with support in A.  *)
(*           phi x == the image of x : gT under phi : 'CF(G).                 *)
(*       cfker phi == the kernel of phi : 'CF(G); note that cfker phi <| G.   *)
(*   cfaithful phi <=>  phi : 'CF(G) is faithful (has a trivial kernel).      *)
(*            '1_A == the indicator function of A as a function of 'CF(G).    *)
(*                    (Provided A <| G; G is determined by the context.)      *)
(*        phi^*%CF == the function conjugate to phi : 'CF(G).                 *)
(*     cfAut u phi == the function conjugate to phi by an algC-automorphism u *)
(*           phi^u    The notation "_ ^u" is only reserved; it is up to       *)
(*                    clients to set Notation "phi ^u" := (cfAut u phi).      *)
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
(*     cfReal phi <=> phi is real, i.e., phi^* == phi.                        *)
(* cfAut_closed u S <-> S : seq 'CF(G) is closed under conjugation by u.      *)
(* conjC_closed S <-> S : seq 'CF(G) is closed under complex conjugation.     *)
(*     'Res[H] phi == the restriction of phi : 'CF(G) to a function of 'CF(H) *)
(*  'Res[H, G] phi    'Res[H] phi x = phi x if x \in H (when H \subset G),    *)
(*        'Res phi    'Res[H] phi x = 0 if x \notin H. The syntax variants    *)
(*                    allow H and G to be inferred; the default is to specify *)
(*                    H explicitly, and infer G from the type of phi.         *)
(*     'Ind[G] phi == the class function of 'CF(G) induced by phi : 'CF(H),   *)
(*  'Ind[G, H] phi    when H \subset G. As with 'Res phi, both G and H can    *)
(*        'Ind phi    be inferred, though usually G isn't.                    *)
(*     cfMorph phi == the class function in 'CF(G) that maps x to phi (f x),  *)
(*                    where phi : 'CF(f @* G), provided G \subset 'dom f.     *)
(*   (phi %% H)%CF == special case of cfMorph phi, when phi : 'CF(G / H).     *)
(*    (phi / H)%CF == the class function in 'CF(G / H) that coincides with    *)
(*                    phi : 'CF(G) on cosets of H \subset cfker phi.          *)
(* For a group G that is a direct product (with KxH : K \x H = G), we set     *)
(*    cfDprodl KxH phi == for phi : 'CF(K), the class function of 'CF(G) that *)
(*                        maps k * h to phi k when k \in K and h \in H.       *)
(*    cfDprodr KxH psi == for psi : 'CF(H), the class function of 'CF(G) that *)
(*                        maps k * h to psi h when k \in K and h \in H.       *)
(* cfDprod KxH phi psi == for phi : 'CF(K), psi : 'CF(H), the class function  *)
(*                        of 'CF(G) that maps k * h to phi k * psi h (this is *)
(*                        the product of the two functions above).            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.
Delimit Scope cfun_scope with CF.

Reserved Notation "''CF' ( G , A )" (at level 8, format "''CF' ( G ,  A )").
Reserved Notation "''CF' ( G )" (at level 8, format "''CF' ( G )").
Reserved Notation "''1_' G" (at level 8, G at level 2, format "''1_' G").
Reserved Notation "''Res[' H , G ]" (at level 8, only parsing).
Reserved Notation "''Res[' H ]" (at level 8, format "''Res[' H ]").
Reserved Notation "''Res'" (at level 8, only parsing).
Reserved Notation "''Ind[' G , H ]" (at level 8, only parsing).
Reserved Notation "''Ind[' G ]" (at level 8, format "''Ind[' G ]").
Reserved Notation "''Ind'" (at level 8, only parsing).
Reserved Notation "'[ phi , psi ]_ G" (at level 2, only parsing).
Reserved Notation "'[ phi , psi ]"
  (at level 2, format "'[hv' ''[' phi , '/ '  psi ] ']'").
Reserved Notation "'[ phi ]_ G" (at level 2, only parsing).
Reserved Notation "'[ phi ]" (at level 2, format "''[' phi ]").
Reserved Notation "phi ^u" (at level 3, format "phi ^u").

Section AlgC.
(* Arithmetic properties of group orders in the characteristic 0 field algC. *)

Variable (gT : finGroupType).
Implicit Types (G H : {group gT}) (B : {set gT}).

Lemma neq0GC G : (#|G|)%:R != 0 :> algC.
Proof. by rewrite -neq0N_neqC -lt0n. Qed.

Lemma neq0GiC G B : (#|G : B|)%:R != 0 :> algC.
Proof. by rewrite -neq0N_neqC -lt0n. Qed.

Lemma divgS_C G H : H \subset G -> #|G : H|%:R = #|G|%:R / #|H|%:R :> algC.
Proof. by move/LaGrange <-; rewrite mulnC natr_mul mulfK ?neq0GC. Qed.

Lemma sposGC G : 0 < #|G|%:R.
Proof. by rewrite -(ltn_ltC 0). Qed.

Lemma sposGiC G B : 0 < #|G : B|%:R.
Proof. by rewrite -(ltn_ltC 0). Qed.

Lemma algC'G G : [char algC]^'.-group G.
Proof. by apply/pgroupP=> p _; rewrite inE /= Cchar. Qed.

End AlgC.

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

Definition cfAut := cfun_comp (rmorph0 u).

Lemma cfAut1i A : cfAut '1_A = '1_A.
Proof. by apply/cfunP=> x; rewrite !cfunElock rmorph_nat. Qed.

Lemma cfAutZ a phi : cfAut (a *: phi) = u a *: cfAut phi.
Proof. by apply/cfunP=> x; rewrite !cfunE rmorphM. Qed.

Lemma cfAut_is_rmorphism : rmorphism cfAut.
Proof.
by do 2?split=> [phi psi|]; last exact: cfAut1i;
   apply/cfunP=> x; rewrite !cfunE (rmorph_sub, rmorphM).
Qed.
Canonical cfAut_additive := Additive cfAut_is_rmorphism.
Canonical cfAut_rmorphism := RMorphism cfAut_is_rmorphism.

Definition cfAut_closed (S : seq classfun) :=
  {in S, forall phi, cfAut phi \in S}.

End Automorphism.

Definition cfReal phi := cfAut conjC phi == phi.

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

Definition cfun_base A : #|classes B ::&: A|.-tuple classfun :=
  [tuple of [image ('1_xB)%R | xB <- classes B ::&: A]].
Definition classfun_on A := span (cfun_base A).

Definition cfdot phi psi := #|B|%:R^-1 * \sum_(x \in B) phi x * (psi x)^*.
Definition cfdotr_head k psi phi := let: tt := k in cfdot phi psi.
Definition cfnorm_head k phi := let: tt := k in cfdot phi phi.

Coercion seq_of_cfun phi := [:: phi].

End Defs.

Bind Scope cfun_scope with classfun.

Arguments Scope classfun [_ group_scope].
Arguments Scope classfun_on [_ group_scope group_scope].
Arguments Scope cfun_indicator [_ group_scope].
Arguments Scope cfAut [_ group_scope _ cfun_scope].
Arguments Scope cfReal [_ group_scope cfun_scope].
Arguments Scope cfdot [_ group_scope cfun_scope cfun_scope].
Arguments Scope cfdotr_head [_ group_scope _ cfun_scope cfun_scope].
Arguments Scope cfdotr_head [_ group_scope _ cfun_scope].

Notation "''CF' ( G )" := (classfun G) : type_scope.
Notation "''CF' ( G )" := (fullv (cfun_vectType G)) : vspace_scope.
Notation "''1_' A" := (cfun_indicator _ A) : ring_scope.
Notation "''CF' ( G , A )" := (classfun_on G A) : ring_scope.

Notation "phi ^*" := (cfAut conjC phi) : cfun_scope.
Notation conjC_closed := (cfAut_closed conjC).
Prenex Implicits cfReal.
(* Workaround for overeager projection reduction. *)
Notation eqcfP := (@eqP (cfun_eqType _) _ _) (only parsing).

Notation "''[' u , v ]_ G":=  (@cfdot _ G u v) (only parsing) : ring_scope.
Notation "''[' u , v ]" := (cfdot u v) : ring_scope.
Notation "''[' u ]_ G" := '[u, u]_G (only parsing) : ring_scope.
Notation "''[' u ]" := '[u, u] : ring_scope.
Notation cfdotr := (cfdotr_head tt).
Notation cfnorm := (cfnorm_head tt).

Section Predicates.

Variables (gT rT : finGroupType) (D : {set gT}) (R : {set rT}).
Implicit Types (phi psi : 'CF(D)) (S : seq 'CF(D)) (tau : 'CF(D) -> 'CF(R)).

Definition cfker phi := [set x \in D | forallb y, phi (x * y)%g == phi y].

Definition cfaithful phi := cfker phi \subset [1].

Definition ortho_rec S1 S2 :=
  all [pred phi | all [pred psi | '[phi, psi] == 0] S2] S1.

Fixpoint pair_ortho_rec S := 
  if S is psi :: S' then ortho_rec psi S' && pair_ortho_rec S' else true.

(* We exclude 0 from pairwise orthogonal sets. *)
Definition pairwise_orthogonal S := (0 \notin S) && pair_ortho_rec S.

Definition orthonormal S := all [pred psi | '[psi] == 1] S && pair_ortho_rec S.

Definition isometry tau := forall phi psi, '[tau phi, tau psi] = '[phi, psi].

Definition isometry_from_to mCFD tau mCFR :=
   prop_in2 mCFD (inPhantom (isometry tau))
  /\ prop_in1 mCFD (inPhantom (forall phi, in_mem (tau phi) mCFR)).

End Predicates.

(* Outside section so the nosimpl does not get "cooked" out. *)
Definition orthogonal gT D S1 S2 := nosimpl (@ortho_rec gT D S1 S2).

Arguments Scope cfker [_ group_scope cfun_scope].
Arguments Scope cfaithful [_ group_scope cfun_scope].
Arguments Scope orthogonal [_ group_scope cfun_scope cfun_scope].
Arguments Scope pairwise_orthogonal [_ group_scope cfun_scope].
Arguments Scope orthonormal [_ group_scope cfun_scope].
Arguments Scope isometry [_ _ group_scope group_scope cfun_scope].

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

Lemma support_cfuni A : A <| G -> support '1_A =i A.
Proof. by move=> nsAG x; rewrite !inE cfuniE // -(eqN_eqC _ 0) -lt0n lt0b. Qed.

Lemma eq_mul_cfuni A phi : A <| G -> {in A, phi * '1_A =1 phi}.
Proof. by move=> nsAG x Ax; rewrite cfunE cfuniE // Ax mulr1. Qed.

Lemma eq_cfuni A : A <| G -> {in A, '1_A =1 (1 : 'CF(G))}.
Proof. by rewrite -['1_A]mul1r; exact: eq_mul_cfuni. Qed.

Lemma cfuniG : '1_G = 1.
Proof. by rewrite -[G in '1_G]genGid. Qed.

Lemma cfun1E g : (1 : 'CF(G)) g = (g \in G)%:R.
Proof. by rewrite -cfuniG cfuniE. Qed.

Lemma mul_cfuni A B : '1_A * '1_B = '1_(A :&: B) :> 'CF(G).
Proof.
apply/cfunP=> g; rewrite !cfunElock -natr_mul mulnb subsetI.
by rewrite andbCA !andbA andbb.
Qed.

Lemma cfun_classE x y : '1_(x ^: G) y = ((x \in G) && (y \in x ^: G))%:R.
Proof.
rewrite cfunElock genGid class_sub_norm ?class_norm //; congr (_ : bool)%:R.
by apply: andb_id2r => /imsetP[z Gz ->]; rewrite groupJr.
Qed.

Lemma cfun_on_sum A :
  'CF(G, A) = (\sum_(xG \in classes G | xG \subset A) ('1_xG)%:VS)%VS.
Proof.
by rewrite ['CF(G, A)]big_map big_filter; apply: eq_bigl => xG; rewrite !inE.
Qed.

Lemma cfun_onP A phi :
  reflect (forall x, x \notin A -> phi x = 0) (phi \in 'CF(G, A)).
Proof.
apply: (iffP idP) => [/coord_span-> x notAx | Aphi].
  set b := cfun_base G A; rewrite sum_cfunE big1 // => i _; rewrite cfunE.
  have /mapP[xG]: b`_i \in b by rewrite -tnth_nth mem_tnth.
  rewrite mem_enum => /setIdP[/imsetP[y Gy ->] Ay] ->.
  by rewrite cfun_classE Gy (contraNF (subsetP Ay x)) ?mulr0.
suffices <-: \sum_(xG \in classes G) phi (repr xG) *: '1_xG = phi.
  apply: memv_suml => _ /imsetP[x Gx ->]; rewrite memvZ cfun_repr.
  have [s_xG_A | /subsetPn[_ /imsetP[y Gy ->]]] := boolP (x ^: G \subset A).
    by rewrite cfun_on_sum [_ \in _](sumv_sup (x ^: G)) ?mem_classes ?orbT.
  by move/Aphi; rewrite cfunJ // => ->; rewrite eqxx.
apply/cfun_inP=> x Gx; rewrite sum_cfunE (bigD1 (x ^: G)) ?mem_classes //=.
rewrite cfunE cfun_repr cfun_classE Gx class_refl mulr1.
rewrite big1 ?addr0 // => _ /andP[/imsetP[y Gy ->]]; apply: contraNeq.
rewrite cfunE cfun_repr cfun_classE Gy mulf_eq0 => /norP[_].
by rewrite -(eqN_eqC _ 0) -lt0n lt0b => /class_transr->.
Qed.
Implicit Arguments cfun_onP [A phi].

Lemma cfun_on0 A phi x : phi \in 'CF(G, A) -> x \notin A -> phi x = 0.
Proof. by move/cfun_onP; exact. Qed.

Lemma sum_by_classes (R : ringType) (F : gT -> R) :
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

Lemma cfun_base_free A : free (cfun_base G A).
Proof.
have b_i (i : 'I_#|classes G ::&: A|) : (cfun_base G A)`_i = '1_(enum_val i).
  by rewrite /enum_val -!tnth_nth tnth_map.
apply/freeP => s S0 i; move/cfunP/(_ (repr (enum_val i))): S0.
rewrite sum_cfunE (bigD1 i) //= big1 ?addr0 => [|j].
  rewrite b_i !cfunE; have /setIdP[/imsetP[x Gx ->] _] := enum_valP i.
  by rewrite cfun_repr cfun_classE Gx class_refl mulr1.
apply: contraNeq; rewrite b_i !cfunE mulf_eq0 => /norP[_].
rewrite -(inj_eq enum_val_inj).
have /setIdP[/imsetP[x _ ->] _] := enum_valP i; rewrite cfun_repr.
have /setIdP[/imsetP[y Gy ->] _] := enum_valP j; rewrite cfun_classE Gy.
by rewrite -(eqN_eqC _ 0) -lt0n lt0b => /class_transr->.
Qed.

Lemma dim_cfun : \dim 'CF(G) = #|classes G|.
Proof. by rewrite dimvf /vdim //= genGid. Qed.

Lemma dim_cfun_on A : \dim 'CF(G, A) = #|classes G ::&: A|.
Proof. by rewrite (eqnP (cfun_base_free A)) size_tuple. Qed.

Lemma dim_cfun_on_abelian A : abelian G -> A \subset G -> \dim 'CF(G, A) = #|A|.
Proof.
move/abelian_classP=> cGG sAG; rewrite -(card_imset _ set1_inj) dim_cfun_on.
apply/eq_card=> xG; rewrite !inE.
apply/andP/imsetP=> [[/imsetP[x Gx ->] Ax] | [x Ax ->]] {xG}.
  by rewrite cGG ?sub1set // in Ax *; exists x.
by rewrite -{1}(cGG x) ?mem_classes ?(subsetP sAG) ?sub1set.
Qed.

Lemma cfuni_on A : '1_A \in 'CF(G, A).
Proof.
apply/cfun_onP=> x notAx; rewrite cfunElock genGid.
by case: andP => // [[_ s_xG_A]]; rewrite (subsetP s_xG_A) ?class_refl in notAx.
Qed.

Lemma mul_cfuni_on A phi : phi * '1_A \in 'CF(G, A).
Proof.
by apply/cfun_onP=> x /(cfun_onP (cfuni_on A)) Ax0; rewrite cfunE Ax0 mulr0.
Qed.

Lemma cfun_onE phi A : (phi \in 'CF(G, A)) = (support phi \subset A).
Proof. exact: (sameP cfun_onP supportP). Qed.

Lemma cfun_onT phi : phi \in 'CF(G, [set: gT]).
Proof. by rewrite cfun_onE. Qed.

Lemma cfun_onD1 phi A :
  (phi \in 'CF(G, A^#)) = (phi \in 'CF(G, A)) && (phi 1%g == 0).
Proof.
by rewrite !cfun_onE -!(eq_subset (in_set (support _))) subsetD1 !inE negbK.
Qed.

Lemma cfun_onG phi : phi \in 'CF(G, G).
Proof. by rewrite cfun_onE support_cfun. Qed.

Lemma cfunD1E phi : (phi \in 'CF(G, G^#)) = (phi 1%g == 0).
Proof. by rewrite cfun_onD1 cfun_onG. Qed.

Lemma cfunGid : 'CF(G, G) = 'CF(G)%VS.
Proof. by apply/eqP/vspaceP=> phi; rewrite cfun_onG memvf. Qed.

Lemma cfun_onS A B phi : B \subset A -> phi \in 'CF(G, B) -> phi \in 'CF(G, A).
Proof. by rewrite !cfun_onE => sBA /subset_trans->. Qed.

Lemma cfConjCE phi x : (phi^*)%CF x = (phi x)^*.
Proof. by rewrite cfunE. Qed.

Lemma cfConjCK : involutive (fun phi => phi^*)%CF.
Proof. by move=> phi; apply/cfunP=> x; rewrite !cfunE conjCK. Qed.

Lemma cfConjC1 : (1^*)%CF = 1 :> 'CF(G).
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

Implicit Arguments cfun_onP [gT G A phi].
Hint Resolve cfun_onT.

Section DotProduct.

Variable (gT : finGroupType) (G : {group gT}).
Implicit Types (M : {group gT}) (phi psi xi : 'CF(G)) (R S : seq 'CF(G)).

Lemma cfdotE phi psi :
  '[phi, psi] = #|G|%:R^-1 * \sum_(x \in G) phi x * (psi x)^*.
Proof. by []. Qed.

Lemma cfdotElr A B phi psi :
     phi \in 'CF(G, A) -> psi \in 'CF(G, B) ->
  '[phi, psi] = #|G|%:R^-1 * \sum_(x \in A :&: B) phi x * (psi x)^*.
Proof.
move=> Aphi Bpsi; rewrite (big_setID G) cfdotE (big_setID (A :&: B)) setIC /=.
congr (_ * (_ + _)); rewrite !big1 // => x /setDP[_].
  by move/cfun0->; rewrite mul0r.
rewrite inE; case/nandP=> notABx; first by rewrite (cfun_on0 Aphi) ?mul0r.
by rewrite (cfun_on0 Bpsi) // rmorph0 mulr0.
Qed.

Lemma cfdotEl A phi psi :
     phi \in 'CF(G, A) ->
  '[phi, psi] = #|G|%:R^-1 * \sum_(x \in A) phi x * (psi x)^*.
Proof. by move=> Aphi; rewrite (cfdotElr Aphi (cfun_onT psi)) setIT. Qed.

Lemma cfdotEr A phi psi :
     psi \in 'CF(G, A) ->
  '[phi, psi] = #|G|%:R^-1 * \sum_(x \in A) phi x * (psi x)^*.
Proof. by move=> Apsi; rewrite (cfdotElr (cfun_onT phi) Apsi) setTI. Qed.

Lemma cfnormE A phi :
  phi \in 'CF(G, A) -> '[phi] = #|G|%:R^-1 * (\sum_(x \in A) `|phi x| ^+ 2).
Proof. by move/cfdotEl->; rewrite (eq_bigr _ (fun _ _ => normCK _)). Qed.

Lemma eq_cfdotl A phi1 phi2 psi :
  psi \in 'CF(G, A) -> {in A, phi1 =1 phi2} -> '[phi1, psi] = '[phi2, psi].
Proof.
move/cfdotEr=> eq_dot eq_phi; rewrite !eq_dot; congr (_ * _).
by apply: eq_bigr => x Ax; rewrite eq_phi.
Qed.

Lemma cfdot_cfuni A B :
  A <| G -> B <| G -> '['1_A, '1_B]_G = #|A :&: B|%:R / #|G|%:R.
Proof.
move=> nsAG nsBG; rewrite (cfdotElr (cfuni_on G A) (cfuni_on G B)) mulrC.
congr (_ / _); rewrite -sumr_const; apply: eq_bigr => x /setIP[Ax Bx].
by rewrite !cfuniE // Ax Bx rmorph1 mulr1.
Qed.

Lemma cfnorm1 : '[1]_G = 1.
Proof. by rewrite cfdot_cfuni ?genGid // setIid divff ?neq0GC. Qed.

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
 
Lemma eq_cfdotr A phi psi1 psi2 :
  phi \in 'CF(G, A) -> {in A, psi1 =1 psi2} -> '[phi, psi1] = '[phi, psi2].
Proof. by move=> Aphi /eq_cfdotl eq_dot; rewrite cfdotC eq_dot // -cfdotC. Qed.

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

Lemma cfdot_cfAut (u : {rmorphism algC -> algC}) phi psi : 
    {in image psi G, {morph u : x / x^*}} ->
  '[cfAut u phi, cfAut u psi] = u '[phi, psi].
Proof.
move=> uC; rewrite rmorphM fmorphV rmorph_nat rmorph_sum; congr (_ * _).
by apply: eq_bigr => x Gx; rewrite !cfunE rmorphM uC ?map_f ?mem_enum.
Qed.

Lemma cfdot_conjC phi psi : '[phi^*, psi^*] = '[phi, psi]^*.
Proof. by rewrite cfdot_cfAut. Qed.

Lemma cfnorm_posC phi : 0 <= '[phi].
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

Lemma cfnorm_sign n phi : '[(-1) ^+ n *: phi] = '[phi].
Proof. by rewrite -signr_odd scaler_sign; case: (odd n); rewrite ?cfnormN. Qed.

Lemma cfnormD phi psi :
  let d := '[phi, psi] in '[phi + psi] = '[phi] + '[psi] + (d + d^*).
Proof. by rewrite /= addrAC -cfdotC cfdotDl !cfdotDr !addrA. Qed.

Lemma cfnorm_sub phi psi :
  let d := '[phi, psi] in '[phi - psi] = '[phi] + '[psi] - (d + d^*).
Proof. by rewrite /= cfnormD cfnormN cfdotNr rmorphN -oppr_add. Qed.

Lemma cfnormDd phi psi : '[phi, psi] = 0 -> '[phi + psi] = '[phi] + '[psi].
Proof. by move=> ophipsi; rewrite cfnormD ophipsi rmorph0 !addr0. Qed.

Lemma cfnorm_subd phi psi : '[phi, psi] = 0 -> '[phi - psi] = '[phi] + '[psi].
Proof.
by move=> ophipsi; rewrite cfnormDd ?cfnormN // cfdotNr ophipsi oppr0.
Qed.

Lemma cfnorm_conjC phi : '[phi^*] = '[phi].
Proof. by rewrite cfdot_conjC posC_conjK // cfnorm_posC. Qed.

Lemma orthogonal_cons phi R S :
  orthogonal (phi :: R) S = orthogonal phi S && orthogonal R S.
Proof. by rewrite /orthogonal /= andbT. Qed.

Lemma orthoP phi psi : reflect ('[phi, psi] = 0) (orthogonal phi psi).
Proof. by rewrite /orthogonal /= !andbT; exact: eqP. Qed.

Lemma orthogonalP S R :
  reflect {in S & R, forall phi psi, '[phi, psi] = 0} (orthogonal S R).
Proof.
apply: (iffP allP) => oSR phi => [psi /oSR/allP opS /opS/eqP // | /oSR opS].
by apply/allP=> psi /= /opS->.
Qed.

Lemma orthoPl phi S :
  reflect {in S, forall psi, '[phi, psi] = 0} (orthogonal phi S).
Proof.
by rewrite [orthogonal _ S]andbT /=; apply: (iffP allP) => ophiS ? /ophiS/eqP.
Qed.
Implicit Arguments orthoPl [phi S].

Lemma orthogonal_sym : symmetric (@orthogonal _ G).
Proof.
apply: symmetric_from_pre => R S /orthogonalP oRS.
by apply/orthogonalP=> phi psi Rpsi Sphi; rewrite cfdotC oRS ?rmorph0.
Qed.

Lemma orthoPr S psi :
  reflect {in S, forall phi, '[phi, psi] = 0} (orthogonal S psi).
Proof.
rewrite orthogonal_sym.
by apply: (iffP orthoPl) => oSpsi phi Sphi; rewrite cfdotC oSpsi ?conjC0.
Qed.

Lemma eq_orthogonal R1 R2 S1 S2 :
  R1 =i R2 -> S1 =i S2 -> orthogonal R1 S1 = orthogonal R2 S2.
Proof.
move=> eqR eqS; rewrite [orthogonal _ _](eq_all_r eqR).
by apply: eq_all => psi /=; exact: eq_all_r.
Qed.

Lemma orthogonal_catl R1 R2 S :
  orthogonal (R1 ++ R2) S = orthogonal R1 S && orthogonal R2 S.
Proof. exact: all_cat. Qed.

Lemma orthogonal_catr R S1 S2 :
  orthogonal R (S1 ++ S2) = orthogonal R S1 && orthogonal R S2.
Proof. by rewrite !(orthogonal_sym R) orthogonal_catl. Qed.

Lemma span_orthogonal S1 S2 phi1 phi2 :
  orthogonal S1 S2 -> phi1 \in span S1 -> phi2 \in span S2 -> '[phi1, phi2] = 0.
Proof.
move/orthogonalP=> oS12; do 2!move/(@coord_span _ _ _ (in_tuple _))->.
rewrite cfdot_suml big1 // => i _; rewrite cfdot_sumr big1 // => j _.
by rewrite cfdotZl cfdotZr oS12 ?mem_nth ?mulr0.
Qed.

Lemma orthogonal_split S beta :
  {X : 'CF(G) & {Y | [/\ beta = X + Y, X \in span S & orthogonal Y S]}}.
Proof.
elim: S beta => [|phi S IHS] beta; first by exists 0, beta; rewrite add0r mem0v.
have [[U [V [-> S_U oVS]]] [X [Y [-> S_X oYS]]]] := (IHS phi, IHS beta).
pose Z := '[Y, V] / '[V] *: V; exists (X + Z), (Y - Z).
split; first by rewrite addrCA !addrA addrK addrC.
  rewrite /Z -{4}(addKr U V) scaler_addr scalerN addrA addrC span_cons.
  by rewrite memv_add ?memv_sub ?memvZl ?memv_inj.
apply/orthoPl=> psi; rewrite !inE => /predU1P[-> | Spsi]; last first.
  by rewrite cfdot_subl cfdotZl (orthoPl oVS _ Spsi) mulr0 subr0 (orthoPl oYS).
rewrite cfdot_subl !cfdotDr (span_orthogonal oYS) // ?memv_span ?mem_head //.
rewrite !cfdotZl (span_orthogonal oVS _ S_U) ?mulr0 ?memv_span ?mem_head //.
have [-> | nzV] := eqVneq V 0; first by rewrite cfdot0r !mul0r subrr.
by rewrite divfK ?cfnorm_eq0 ?subrr.
Qed.

Lemma map_orthogonal M (nu : 'CF(G) -> 'CF(M)) S R (A : pred 'CF(G)) :
  {in A &, isometry nu} -> {subset S <= A} -> {subset R <= A} ->
 orthogonal (map nu S) (map nu R) = orthogonal S R.
Proof.
move=> Inu sSA sRA; rewrite [orthogonal _ _]all_map.
apply: eq_in_all => phi Sphi; rewrite /= all_map.
by apply: eq_in_all => psi Rpsi; rewrite /= Inu ?(sSA phi) ?(sRA psi).
Qed.

Lemma pairwise_orthogonalP S :
  reflect (uniq (0 :: S)
             /\ {in S &, forall phi psi, phi != psi -> '[phi, psi] = 0})
          (pairwise_orthogonal S).
Proof.
rewrite /pairwise_orthogonal /=; case notS0: (~~ _); last by right; case.
elim: S notS0 => [|phi S IH] /=; first by left.
rewrite inE eq_sym andbT => /norP[nz_phi /IH{IH}IH].
have [opS | not_opS] := allP; last first.
  right=> [[/andP[notSp _] opS]]; case: not_opS => psi Spsi /=.
  by rewrite opS ?mem_head 1?mem_behead // eq_sym (memPn notSp).
rewrite (contra (opS _)) /= ?cfnorm_eq0 //.
apply: (iffP IH) => [] [uniqS oSS]; last first.
  by split=> //; apply: sub_in2 oSS => psi Spsi; exact: mem_behead.
split=> // psi xi; rewrite !inE => /predU1P[-> // | Spsi].
  by case/predU1P=> [-> | /opS] /eqP.
case/predU1P=> [-> _ | Sxi /oSS-> //].
by apply/eqP; rewrite cfdotC conjC_eq0 [_ == 0]opS.
Qed.

Lemma pairwise_orthogonal_cat R S :
  pairwise_orthogonal (R ++ S) =
    [&& pairwise_orthogonal R, pairwise_orthogonal S & orthogonal R S].
Proof.
rewrite /pairwise_orthogonal mem_cat negb_or -!andbA; do !bool_congr.
elim: R => [|phi R /= ->]; rewrite ?andbT // orthogonal_cons all_cat -!andbA /=.
by do !bool_congr.
Qed.

Lemma eq_pairwise_orthogonal R S :
  perm_eq R S -> pairwise_orthogonal R = pairwise_orthogonal S.
Proof.
apply: catCA_perm_subst R S => R S S'. 
rewrite !pairwise_orthogonal_cat !orthogonal_catr (orthogonal_sym R S) -!andbA.
by do !bool_congr.
Qed.

Lemma sub_pairwise_orthogonal S1 S2 :
    {subset S1 <= S2} ->  uniq S1 ->
  pairwise_orthogonal S2 -> pairwise_orthogonal S1.
Proof.
move=> sS12 uniqS1 /pairwise_orthogonalP[/andP[notS2_0 _] oS2].
apply/pairwise_orthogonalP; rewrite /= (contra (sS12 0)) //.
by split=> //; exact: sub_in2 oS2.
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

Lemma filter_pairwise_orthogonal S p : 
  pairwise_orthogonal S -> pairwise_orthogonal (filter p S).
Proof.
move=> orthoS; apply: sub_pairwise_orthogonal (orthoS).
  exact: mem_subseq (filter_subseq p S).
exact/filter_uniq/uniq_free/orthogonal_free.
Qed.

Lemma orthonormal_not0 S : orthonormal S -> 0 \notin S.
Proof.
by case/andP=> /allP S1 _; rewrite (contra (S1 _)) //= cfdot0r eq_sym oner_eq0.
Qed.

Lemma orthonormalE S :
  orthonormal S = all [pred phi | '[phi] == 1] S && pairwise_orthogonal S.
Proof. by rewrite -(andb_idl (@orthonormal_not0 S)) andbCA. Qed.

Lemma orthonormal_orthogonal S : orthonormal S -> pairwise_orthogonal S.
Proof. by rewrite orthonormalE => /andP[_]. Qed.

Lemma orthonormal_cat R S :
  orthonormal (R ++ S) = [&& orthonormal R, orthonormal S & orthogonal R S].
Proof.
rewrite !orthonormalE pairwise_orthogonal_cat all_cat -!andbA.
by do !bool_congr.
Qed.

Lemma eq_orthonormal R S : perm_eq R S -> orthonormal R = orthonormal S.
Proof.
move=> eqRS; rewrite !orthonormalE (eq_all_r (perm_eq_mem eqRS)).
by rewrite (eq_pairwise_orthogonal eqRS).
Qed.

Lemma orthonormal_free S : orthonormal S -> free S.
Proof. by move/orthonormal_orthogonal/orthogonal_free. Qed.

Lemma orthonormalP S :
  reflect (uniq S /\ {in S &, forall phi psi, '[phi, psi]_G = (phi == psi)%:R})
          (orthonormal S).
Proof.
rewrite orthonormalE; have [/= normS | not_normS] := allP; last first.
  by right=> [[_ o1S]]; case: not_normS => phi Sphi; rewrite /= o1S ?eqxx.
apply: (iffP (pairwise_orthogonalP S)) => [] [uniqS oSS].
  split=> // [|phi psi]; first by case/andP: uniqS.
  by have [-> _ /normS/eqP | /oSS] := altP eqP.
split=> // [|phi psi Sphi Spsi /negbTE]; last by rewrite oSS // => ->.
by rewrite /= (contra (normS _)) // cfdot0r eq_sym oner_eq0.
Qed.

Lemma sub_orthonormal S1 S2 :
  {subset S1 <= S2} -> uniq S1 -> orthonormal S2 -> orthonormal S1.
Proof.
move=> sS12 uniqS1 /orthonormalP[_ oS1]. 
by apply/orthonormalP; split; last exact: sub_in2 sS12 _ _.
Qed.

Lemma orthonormal2P phi psi :
  reflect [/\ '[phi, psi] = 0, '[phi] = 1 & '[psi] = 1]
          (orthonormal [:: phi; psi]).
Proof.
rewrite /orthonormal /= !andbT andbC.
by apply: (iffP and3P) => [] []; do 3!move/eqP->.
Qed.

Lemma conjC_pair_orthogonal S chi :
    conjC_closed S -> ~~ has cfReal S -> pairwise_orthogonal S -> chi \in S ->
  pairwise_orthogonal (chi :: chi^*%CF).
Proof.
move=> ccS /hasPn nrS oSS Schi; apply: sub_pairwise_orthogonal oSS.
  by apply/allP; rewrite /= Schi ccS.
by rewrite /= inE eq_sym nrS.
Qed.

Lemma cfdot_real_conjC phi psi : cfReal phi -> '[phi, psi^*]_G = '[phi, psi]^*.
Proof. by rewrite -cfdot_conjC => /eqcfP->. Qed.

(* Note: other isometry lemmas, and the dot product lemmas for orthogonal     *)
(* and orthonormal sequences are in vcharacter, because we need the 'Z[S]     *)
(* notation for the isometry domains. Alternatively, this could be moved to   *)
(* cfun.                                                                      *)

End DotProduct.

Implicit Arguments orthoP [gT G phi psi].
Implicit Arguments orthoPl [gT G phi S].
Implicit Arguments orthoPr [gT G S psi].
Implicit Arguments orthogonalP [gT G R S].
Implicit Arguments pairwise_orthogonalP [gT G S].
Implicit Arguments orthonormalP [gT G S].

Section BuildIsometries.

Variable (gT : finGroupType) (L G : {group gT}).
Implicit Types (phi psi xi : 'CF(L)) (R S : seq 'CF(L)).
Implicit Types (U : pred 'CF(L)) (W : pred 'CF(G)).

Lemma sub_iso_to U1 U2 W1 W2 tau :
    {subset U2 <= U1} -> {subset W1 <= W2} ->
  {in U1, isometry tau, to W1} -> {in U2, isometry tau, to W2}.
Proof.
by move=> sU sW [Itau Wtau]; split=> [|u /sU/Wtau/sW //]; exact: sub_in2 Itau.
Qed.

Lemma isometry_of_cfnorm S tauS :
    pairwise_orthogonal S -> pairwise_orthogonal tauS ->
    map cfnorm tauS = map cfnorm S ->
  {tau : {linear 'CF(L) -> 'CF(G)} | map tau S = tauS
                                   & {in span S &, isometry tau}}.
Proof.
move=> oS oT eq_nST; have freeS := orthogonal_free oS.
have eq_sz: size tauS = size S by have:= congr1 size eq_nST; rewrite !size_map.
have [tau /(_ freeS eq_sz) defT] := linear_of_free S tauS.
rewrite -[S]/(tval (in_tuple S)).
exists tau => // u v /coord_span-> /coord_span->; rewrite !raddf_sum /=.
apply: eq_bigr => i _ /=; rewrite linearZ !cfdotZr !cfdot_suml; congr (_ * _).
apply: eq_bigr => j _ /=; rewrite linearZ !cfdotZl; congr (_ * _).
rewrite -!((nth_map _ 0) tau) // defT; have [-> | neq_ji] := eqVneq j i.
  by rewrite -!['[_]]((nth_map _ 0) cfnorm) ?eq_sz // eq_nST.
have{oS} [/=/andP[_ uS] oS] := pairwise_orthogonalP oS.
have{oT} [/=/andP[_ uT] oT] := pairwise_orthogonalP oT.
by rewrite oS ?oT ?mem_nth ? nth_uniq ?eq_sz.
Qed.

Lemma isometry_raddf_inj U (tau : {additive 'CF(L) -> 'CF(G)}) :
    {in U &, isometry tau} -> {in U &, forall u v, u - v \in U} ->
  {in U &, injective tau}.
Proof.
move=> Itau linU phi psi Uphi Upsi /eqP; rewrite -subr_eq0 -raddf_sub.
by rewrite -cfnorm_eq0 Itau ?linU // cfnorm_eq0 subr_eq0 => /eqP.
Qed.

End BuildIsometries.

Section Restrict.

Variables (gT : finGroupType) (A B : {set gT}).
Local Notation H := <<A>>.
Local Notation G := <<B>>.

Fact cfRes_subproof (phi : 'CF(B)) :
  is_class_fun H [ffun x => phi x *+ ((x \in H) && (H \subset G))].
Proof.
apply: intro_class_fun => /= [x y Hx Hy | x /negbTE/=-> //].
by rewrite Hx groupJ //; case: subsetP => // sHG; rewrite cfunJgen ?sHG.
Qed.
Definition cfRes phi := Cfun 1 (cfRes_subproof phi).

Lemma cfResE phi : A \subset B -> {in A, cfRes phi =1 phi}.
Proof. by move=> sAB x Ax; rewrite cfunElock mem_gen ?genS. Qed.
 
Lemma cfRes_is_linear : linear cfRes.
Proof.
by move=> a phi psi; apply/cfunP=> x; rewrite !cfunElock mulrnAr mulrn_addl.
Qed.
Canonical cfRes_additive := Additive cfRes_is_linear.
Canonical cfRes_linear := Linear cfRes_is_linear.

Lemma cfRes_cfun1 : A \subset B -> cfRes 1 = 1.
Proof.
move/genS=> sHG; apply: cfun_in_genP => x Hx.
by rewrite cfunElock Hx sHG !cfun1Egen Hx (subsetP sHG).
Qed.

Lemma cfRes1 phi : A \subset B -> cfRes phi 1%g = phi 1%g.
Proof. by move/genS=> sHG; rewrite cfunElock sHG group1. Qed.

End Restrict.

Arguments Scope cfRes [_ group_scope group_scope cfun_scope].
Notation "''Res[' H , G ]" := (@cfRes _ H G) (only parsing) : ring_scope.
Notation "''Res[' H ]" := 'Res[H, _] : ring_scope.
Notation "''Res'" := 'Res[_] (only parsing) : ring_scope.

Section MoreRestrict.

Variables (gT : finGroupType) (G H : {group gT}) (A : {set gT}).

Lemma cfResRes (phi : 'CF(G)) :
  A \subset H -> H \subset G -> 'Res[A] ('Res[H] phi) = 'Res[A] phi.
Proof.
move=> sAH sHG; apply/cfunP=> x; rewrite !cfunElock !genGid !gen_subG sAH sHG.
rewrite (subset_trans sAH) // !andbT -mulrnA mulnb.
by rewrite (andb_idl (subsetP _ x)) ?gen_subG.
Qed.

Lemma cfRes_id phi : 'Res[A] phi = phi.
Proof. by apply/cfun_in_genP=> x Gx; rewrite cfunElock Gx subxx. Qed.

End MoreRestrict.

Section Morphim.

Variables (aT rT : finGroupType) (G D : {group aT}) (f : {morphism D >-> rT}).

Fact cfMorph_subproof (phi : 'CF(f @* G)) :
  is_class_fun <<G>> [ffun x => phi (f x) *+ ((x \in G) && (G \subset D))].
Proof.
rewrite genGid; apply: intro_class_fun => [x y Gx Gy | x /negbTE/= ->//].
rewrite Gx groupJ //; case dG: (G \subset D) => //.
by rewrite morphJ ?cfunJ ?mem_morphim ?(subsetP dG).
Qed.
Definition cfMorph phi := Cfun 1 (cfMorph_subproof phi).

Lemma cfMorphE phi x : G \subset D -> x \in G -> cfMorph phi x = phi (f x).
Proof. by rewrite cfunElock => -> ->. Qed.

Fact cfMorph_is_linear : linear cfMorph.
Proof.
by move=> a phi psi; apply/cfunP=> x; rewrite !cfunElock mulrnAr -mulrn_addl.
Qed.
Canonical cfMorph_additive := Additive cfMorph_is_linear.
Canonical cfMorph_linear := Linear cfMorph_is_linear.

Lemma cfMorph_cfun1 : G \subset D -> cfMorph 1 = 1.
Proof.
move=> dG; apply/cfun_inP=> x Gx.
by rewrite cfMorphE // !cfun1E /= morphimEsub // mem_imset Gx.
Qed.

Lemma cfMorph1 phi : G \subset D -> cfMorph phi 1%g = phi 1%g.
Proof. by move=> dG; rewrite cfMorphE // morph1. Qed.

End Morphim.

Prenex Implicits cfMorph.

Section Coset.

Variables (gT : finGroupType) (G : {group gT}) (B : {set gT}).
Implicit Type rT : finGroupType.
Local Notation H := <<B>>%g.

Definition ffun_Quo (phi : 'CF(G)) :=
  [ffun Bx : coset_of B => phi (repr Bx) *+ [&& B <| G & B \subset cfker phi]].
Fact cfQuo_subproof phi : is_class_fun <<G / B>> (ffun_Quo phi).
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
Definition cfQuo phi := Cfun 1 (cfQuo_subproof phi).

Definition cfMod : 'CF(G / B) -> 'CF(G) := @cfMorph _ _ _ _ _.

Local Notation "phi /  'B'" := (cfQuo phi) (at level 40) : cfun_scope.
Local Notation "phi %%  'B'" := (cfMod phi) (at level 40) : cfun_scope.

Lemma cfQuoE (phi : 'CF(G)) x :
  B <| G -> B \subset cfker phi -> x \in G -> (phi / B)%CF (coset B x) = phi x.
Proof.
rewrite cfunElock -gen_subG => nsBG sHK Gx; rewrite nsBG sHK.
rewrite val_coset_prim ?(subsetP (normal_norm nsBG)) //.
by case: repr_rcosetP => _ /(subsetP sHK)/cfkerMl->.
Qed.

Lemma cfModE phi x : B <| G -> x \in G -> (phi %% B)%CF x = phi (coset B x).
Proof. by move/normal_norm=> nBG; exact: cfMorphE. Qed.

Canonical cfMod_additive := [additive of cfMod].
Canonical cfMod_linear := [linear of cfMod].

Lemma cfMod_cfun1 : B <| G -> (1 %% B)%CF = 1.
Proof. by move/normal_norm; exact: cfMorph_cfun1. Qed.

Lemma cfMod1 phi : B <| G -> (phi %% B)%CF 1%g = phi 1%g.
Proof. by move/normal_norm; exact: cfMorph1. Qed.

(* cfQuo is only linear on the class functions that have H in their kernel. *)

Lemma cfker_Morph rT (A D : {group gT}) (f : {morphism D >-> rT})
                  (phi : 'CF(f @* A)) :
  A \subset D -> 'ker_A f \subset cfker (cfMorph phi).
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

Lemma cfModK (phi : 'CF(G / _)) : B <| G -> (phi %% B / B)%CF = phi.
Proof.
move=> nsBG; apply/cfun_inP=> _ /morphimP[x Nx Gx ->] //.
by rewrite cfQuoE ?cfker_Mod ?cfModE.
Qed.

Lemma cfQuoK (phi : 'CF(G)) :
  B <| G -> B \subset cfker phi -> (phi / B %% B)%CF = phi.
Proof.
by move=> nsHG sHK; apply/cfun_inP=> x Gx; rewrite cfModE ?cfQuoE.
Qed.

End Coset.

Arguments Scope cfQuo [_ Group_scope group_scope cfun_scope].
Arguments Scope cfMod [_ Group_scope group_scope cfun_scope].
Notation "phi / H" := (cfQuo H phi) : cfun_scope.
Notation "phi %% H" := (@cfMod _ _ H phi) : cfun_scope.

Section MorphIsometry.

Variable gT : finGroupType.
Implicit Types D G H : {group gT}.

Lemma cfMorph_iso (rT : finGroupType) G D (f : {morphism D >-> rT}) :
  G \subset D -> isometry (@cfMorph _ _ G D f).
Proof.
move=> sGD phi psi; rewrite !cfdotE card_morphim (setIidPr sGD).
rewrite -(LaGrangeI G ('ker f)) /= mulnC natr_mul invf_mul -mulrA.
congr (_ * _); apply: (canLR (mulKf (neq0GC _))).
rewrite -mulr_sumr (partition_big_imset f) /= -morphimEsub //.
apply: eq_bigr => _ /morphimP[x Dx Gx ->].
rewrite -(card_rcoset _ x) mulr_natl -sumr_const.
apply/eq_big => [y | y /andP[Gy /eqP <-]]; last by rewrite !cfMorphE.
rewrite mem_rcoset inE groupMr ?groupV // -mem_rcoset.
by apply: andb_id2l => /(subsetP sGD) Dy; exact: sameP eqP (rcoset_kerP f _ _).
Qed.

Lemma cfMod_iso H G : H <| G -> isometry (@cfMod _ G H).
Proof. by case/andP=> _; exact: cfMorph_iso. Qed.

Lemma cfQuo_iso H G:
  H <| G -> {in [pred phi | H \subset cfker phi] &, isometry (@cfQuo _ G H)}.
Proof.
by move=> nsHG phi psi sHkphi sHkpsi; rewrite -(cfMod_iso nsHG) !cfQuoK.
Qed.

Lemma cfnorm_Quo H G phi :
  H <| G -> H \subset cfker phi -> '[phi / H] = '[phi]_G.
Proof. by move=> nsHG sHker; exact: cfQuo_iso. Qed.

Lemma cfQuo_cfun1 H G : H <| G -> (1 / H)%CF = 1 :> 'CF(G / H).
Proof. by move=> nsHG; rewrite -(cfMod_cfun1 nsHG) cfModK. Qed.

End MorphIsometry.

Section Induced.

Variable gT : finGroupType.

Section Def.

Variables B A : {set gT}.
Local Notation G := <<B>>.
Local Notation H := <<A>>.

Definition ffun_cfInd (phi : 'CF(A)) :=
  [ffun x => #|A|%:R^-1 * (\sum_(y \in G) phi (x ^ y)) *+ (<<A>> \subset G)].

Fact cfInd_subproof phi : is_class_fun G (ffun_cfInd phi).
Proof.
apply: intro_class_fun => [x y Gx Gy | x notGx //].
  congr (_ * _ *+ _); rewrite (reindex_inj (mulgI y^-1)%g) /=.
  apply: eq_big => [z | z Gz]; first by rewrite groupMl ?groupV.
  by rewrite -conjgM mulKVg.
case: subsetP => // sHG; rewrite big1 ?mulr0 // => y Gy.
by rewrite cfun0gen // (contra (sHG _)) // groupJr.
Qed.
Definition cfInd phi := Cfun 1 (cfInd_subproof phi).

Lemma cfInd_is_linear : linear cfInd.
Proof.
move=> c phi psi; apply/cfunP=> x.
rewrite !cfunElock -!mulrnAl mulrCA -mulr_addr /=; congr (_ * _).
by rewrite big_distrr -big_split /=; apply: eq_bigr => y Gy /=; rewrite !cfunE.
Qed.
Canonical cfInd_additive := Additive cfInd_is_linear.
Canonical cfInd_linear := Linear cfInd_is_linear.

End Def.

Local Notation "''Ind[' B , A ]" := (@cfInd B A) : ring_scope.
Local Notation "''Ind[' B ]" := 'Ind[B, _] : ring_scope.

Variables G H : {group gT}.
Implicit Types (phi : 'CF(H)) (psi : 'CF(G)).

Lemma cfIndE phi x :
  H \subset G -> 'Ind[G] phi x = #|H|%:R^-1 * (\sum_(y \in G) phi (x ^ y)).
Proof. by move=> sHG; rewrite cfunElock !genGid sHG. Qed.

Lemma cfInd_normal phi : H <| G -> 'Ind[G] phi \in 'CF(G, H).
Proof.
case/andP=> sHG nHG; apply/cfun_onP=> x notHx; rewrite cfIndE //.
by rewrite big1 ?mulr0 // => y Gy; rewrite cfun0 // memJ_norm ?(subsetP nHG).
Qed.
 
Lemma cfInd1 phi : H \subset G -> 'Ind[G] phi 1%g = #|G : H|%:R * phi 1%g.
Proof.
move=> sHG; rewrite cfIndE //; apply: canLR (mulKf (neq0GC H)) _.
rewrite mulrA -natr_mul LaGrange // mulr_natl -sumr_const; apply: eq_bigr => x.
by rewrite conj1g.
Qed.

Lemma cfInd_cfun1 : H <| G -> 'Ind[G, H] 1 = #|G : H|%:R *: '1_H.
Proof.
move=> nsHG; have [sHG nHG] := andP nsHG.
apply/cfunP=> x; rewrite cfIndE // cfunE cfuniE //.
apply: canLR (mulKf (neq0GC H)) _; rewrite mulrA -natr_mul LaGrange //.
rewrite mulr_natl -sumr_const; apply: eq_bigr => y Gy.
by rewrite cfun1E -{1}(normsP nHG y Gy) memJ_conjg.
Qed.

Lemma cfnorm_Ind_cfun1 : H <| G -> '['Ind[G, H] 1] = #|G : H|%:R.
Proof.
move=> nsHG; rewrite cfInd_cfun1 // cfnormZ normC_nat cfdot_cfuni // setIid.
rewrite mulrC -mulrA mulrCA (mulrA _%:R) -natr_mul LaGrange ?normal_sub //.
by rewrite mulKf ?neq0GC.
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
  by congr (_ * _); apply: eq_bigr => x Hx; rewrite cfResE.
set h' := _^-1; apply: canRL (mulKf (neq0GC G)) _.
transitivity (h' * \sum_(y \in G) \sum_(x \in G) phi (x ^ y) * (psi (x ^ y))^*).
  rewrite mulrCA mulr_natl -sumr_const; congr (_ * _); apply: eq_bigr => y Gy.
  by rewrite (reindex_acts 'J _ Gy) ?astabsJ ?normG.
rewrite exchange_big big_distrr; apply: eq_bigr => x _; rewrite cfIndE //=.
by rewrite -mulrA big_distrl; congr (_ * _); apply: eq_bigr => y /(cfunJ psi)->.
Qed.
Definition cfdot_Res_r := Frobenius_reciprocity.

Lemma cfdot_Res_l psi phi : '['Res[H] psi, phi] = '[psi, 'Ind[G] phi].
Proof. by rewrite cfdotC cfdot_Res_r -cfdotC. Qed.

End Induced.

Arguments Scope cfInd [_ group_scope group_scope cfun_scope].
Notation "''Ind[' G , H ]" := (@cfInd _ G H) (only parsing) : ring_scope.
Notation "''Ind[' G ]" := 'Ind[G, _] : ring_scope.
Notation "''Ind'" := 'Ind[_] (only parsing) : ring_scope.

Section FieldAutomorphism.

Variables (u : {rmorphism algC -> algC}) (gT : finGroupType) (G H : {group gT}).
Implicit Types (phi : 'CF(G)) (S : seq 'CF(G)).
Local Notation "phi ^u" := (cfAut u phi) (at level 3, format "phi ^u").

Lemma cfAutZ_nat n phi : (n%:R *: phi)^u = n%:R *: phi^u.
Proof. exact: raddfZnat. Qed.

Lemma cfAutZ_Nat z phi : isNatC z -> (z *: phi)^u = z *: phi^u.
Proof. exact: raddfZ_NatC. Qed.

Lemma cfAutZ_Int z phi : isIntC z -> (z *: phi)^u = z *: phi^u.
Proof. exact: raddfZ_IntC. Qed.

Lemma cfAut_inj : injective (@cfAut gT G u).
Proof.
move=> phi psi /cfunP eqfg; apply/cfunP=> x.
by have := eqfg x; rewrite !cfunE => /fmorph_inj.
Qed.

Lemma support_cfAut phi : support phi^u =i support phi.
Proof. by move=> x; rewrite !inE cfunE fmorph_eq0. Qed.

Lemma map_cfAut_free S : cfAut_closed u S -> free S -> free (map (cfAut u) S).
Proof.
set Su := map _ S => sSuS freeS; have uniqS := uniq_free freeS.
have uniqSu: uniq Su by rewrite (map_inj_uniq cfAut_inj).
have{sSuS} sSuS: {subset Su <= S} by move=> _ /mapP[phi Sphi ->]; exact: sSuS.
have [|eqSuS _] := leq_size_perm uniqSu sSuS; first by rewrite size_map.
by rewrite (free_perm_eq (uniq_perm_eq uniqSu uniqS eqSuS)).
Qed.

Lemma cfAut_on A phi : (phi^u \in 'CF(G, A)) = (phi \in 'CF(G, A)).
Proof. by rewrite !cfun_onE (eq_subset (support_cfAut phi)). Qed.

Lemma cfAutRes phi : ('Res[H] phi)^u = 'Res phi^u.
Proof. by apply/cfunP=> x; rewrite !cfunElock rmorphMn. Qed.

Lemma cfker_Aut phi : cfker phi^u = cfker phi.
Proof.
apply/setP=> x; rewrite !inE; apply: andb_id2l => Gx.
by apply/forallP/forallP=> Kx y;
  have:= Kx y; rewrite !cfunE (inj_eq (fmorph_inj u)).
Qed.

Lemma cfAutQuo phi : (phi / H)^u = (phi^u / H)%CF.
Proof. by apply/cfunP=> Hx; rewrite !cfunElock cfker_Aut rmorphMn. Qed.

Lemma cfAutMod (psi : 'CF(G / H)) : (psi %% H)^u = (psi^u %% H)%CF.
Proof. by apply/cfunP=> x; rewrite !cfunElock rmorphMn. Qed.

Lemma cfAutInd (psi : 'CF(H)) : ('Ind[G] psi)^u = 'Ind psi^u.
Proof.
apply/cfunP=> x; rewrite !cfunElock rmorphMn rmorphM fmorphV rmorph_nat.
by congr (_ * _ *+ _); rewrite rmorph_sum; apply: eq_bigr => y; rewrite !cfunE.
Qed.

End FieldAutomorphism.

Definition conj_cfRes := cfAutRes conjC.
Definition cfker_conjC := cfker_Aut conjC.
Definition conj_cfQuo := cfAutQuo conjC.
Definition conj_cfMod := cfAutMod conjC.
Definition conj_cfInd := cfAutInd conjC.

Section Product.

Variable (gT : finGroupType) (G : {group gT}).

Lemma cfunM_onI A B phi psi : 
  phi \in 'CF(G, A) -> psi \in 'CF(G, B) -> phi * psi \in 'CF(G, A :&: B).
Proof.
rewrite !cfun_onE => Aphi Bpsi; apply/subsetP=> x; rewrite !inE cfunE mulf_eq0.
by case/norP=> /(subsetP Aphi)-> /(subsetP Bpsi).
Qed.

Lemma cfunM_on A phi psi : 
  phi \in 'CF(G, A) -> psi \in 'CF(G, A) -> phi * psi \in 'CF(G, A).
Proof. by move=> Aphi Bpsi; rewrite -[A]setIid cfunM_onI. Qed.

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

Definition cfDprodl := cfMorph \o cfMorph \o 'Res[pK @* (f' @* G), K].
Definition cfDprodr := cfMorph \o cfMorph \o 'Res[pH @* (f' @* G), H].
Definition cfDprod phi psi := cfDprodl phi * cfDprodr psi.

Let imK : pK @* (f' @* G) \subset K.
Proof. by rewrite im_dprod_inv_morph morphim_fstX. Qed.

Let imH : pH @* (f' @* G) \subset H.
Proof. by rewrite im_dprod_inv_morph morphim_sndX. Qed.

Lemma cfDprodr1 : cfDprodr 1 = 1.
Proof. by rewrite /cfDprodr /= cfRes_cfun1 ?cfMorph_cfun1 ?subsetT. Qed.

Lemma cfDprodl1 : cfDprodl 1 = 1.
Proof. by rewrite /cfDprodl /= cfRes_cfun1 ?cfMorph_cfun1 ?subsetT. Qed.

Lemma cfDprod1r phi : cfDprod phi 1 = cfDprodl phi.
Proof. by rewrite /cfDprod cfDprodr1 mulr1. Qed.

Lemma cfDprod1l psi : cfDprod 1 psi = cfDprodr psi.
Proof. by rewrite /cfDprod cfDprodl1 mul1r. Qed.

Lemma cfDprod11 : cfDprod 1 1 = 1.
Proof. by rewrite cfDprod1l cfDprodr1. Qed.

Lemma cfDprodE phi psi :
  {in K & H, forall h k, cfDprod phi psi (h * k)%g = phi h * psi k}.
Proof.
move=> k h Kk Hh /=; move def_u: (k, h) => u.
have ->: (k * h)%g = f u by rewrite -def_u.
have{Kk Hh} KHu: u \in setX K H by rewrite -def_u inE Kk Hh.
have Gfu: f u \in G by rewrite -im_f morphimEsub // mem_imset.
rewrite cfunE !cfMorphE ?cfResE ?subsetT ?mem_morphim ?in_setT //=.
by rewrite [f' _]invmE // -def_u.
Qed.

Lemma cfDprodEl phi : {in K & H, forall k h, cfDprodl phi (k * h)%g = phi k}.
Proof. by move=> k h Kk Hh; rewrite -cfDprod1r cfDprodE // cfun1E Hh mulr1. Qed.

Lemma cfDprodEr psi : {in K & H, forall k h, cfDprodr psi (k * h)%g = psi h}.
Proof. by move=> k h Kk Hh; rewrite -cfDprod1l cfDprodE // cfun1E Kk mul1r. Qed.

Lemma cfdot_dprod phi1 phi2 psi1 psi2 :
  '[cfDprod phi1 psi1, cfDprod phi2 psi2] = '[phi1, phi2] * '[psi1, psi2].
Proof.
rewrite !cfdotE mulrCA -mulrA mulrCA mulrA -invf_mul -natr_mul (dprod_card KxH).
congr (_ * _); rewrite big_distrl sum_dprodl /=; apply: eq_bigr => k Kk.
rewrite big_distrr; apply: eq_bigr => h Hh /=.
by rewrite mulrCA -mulrA -rmorphM mulrCA mulrA !cfDprodE.
Qed.

Canonical cfDprodl_additive := [additive of cfDprodl].
Canonical cfDprodl_linear := [linear of cfDprodl].
Canonical cfDprodr_additive := [additive of cfDprodr].
Canonical cfDprodr_linear := [linear of cfDprodr].

Lemma cfdot_dprodl : isometry cfDprodl.
Proof. by move=> phi1 phi2; rewrite -!cfDprod1r cfdot_dprod cfnorm1 mulr1. Qed.

Lemma cfdot_dprodr : isometry cfDprodr.
Proof. by move=> psi1 psi2; rewrite -!cfDprod1l cfdot_dprod cfnorm1 mul1r. Qed.

End DProduct.
