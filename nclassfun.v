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
(*          'CF(G) == the type of class functions on G : {group gT}, i.e.,    *)
(*                    which map gT to the type algC of complex algebraics,    *)
(*                    have support in G, and are constant on each conjugacy   *)
(*                    class of G. 'CF(G) is both an algType and a vectType.   *)
(*                    The identity 1 : 'CF(G) is the indicator function of G, *)
(*                    and (later) the principal character).                   *)
(*       'CF(G)%VS == the (total) vector space of 'CF(G).                     *)
(*       'CF(G, A) == the subspace of functions in 'CF(G) with support in A.  *)
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
(*    isometry tau == tau : 'CF(D) -> 'CF(R) is an isometry, mapping          *)
(*                    '[_, _]_D to '[_, _]_R.                                 *)
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

Lemma supportP (aT : finType) (rT : eqType) (y : rT) (A : pred aT) f :
  reflect (forall x, x \notin A -> f x = y) (y.-support f \subset A).
Proof.
by apply: (iffP subsetP) => Af x; [apply: contraNeq | apply: contraR] => /Af->.
Qed.
Implicit Arguments supportP [aT rT y A f].

Lemma class_normal (gT : finGroupType) (G : {group gT}) x :
  x \in G -> x ^: G <| G.
Proof. by move=> Gx; rewrite /normal class_norm class_subG. Qed.

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

(*
Require Import algebra.
Canonical cfun_fAlgType := AlgFType algC cfun_vectMixin.
*)

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

Definition isometry (aT rT : finGroupType) (D : {set aT}) (R : {set rT}) tau :=
  forall phi1 phi2, '[tau phi1, tau phi2]_R = '[phi1, phi2]_D.

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

(*
Lemma base_cfun_subset A :
  G \subset A -> base_cfun G A = [seq '1_xG | xG <- enum (classes G)] :> seq _.
Proof.
move=> sGA; rewrite /= -setI_powerset (setIidPl _) //.
apply/subsetP=> _ /imsetP[x Gx ->].
by rewrite inE (subset_trans _ sGA) ?class_subG.
Qed.
*)

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

End ClassFun.

Arguments Scope classfun_on [_ group_scope group_scope].
Notation "''CF' ( G , A )" := (classfun_on G A) : ring_scope.

Implicit Arguments cfun_memfP [gT G A phi].

Section DotProduct.

Variable (gT : finGroupType) (G : {group gT}).
Implicit Types phi psi xi : 'CF(G).

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

Lemma cfdot_sym phi psi : '[phi, psi] = ('[psi, phi])^*.
Proof.
rewrite /cfdot rmorphM fmorphV rmorph_nat rmorph_sum; congr (_ * _).
by apply: eq_bigr=> x _; rewrite rmorphM conjCK mulrC.
Qed.
 
Lemma cfdot_subr xi phi psi : '[xi, phi - psi] = '[xi, phi] - '[xi, psi].
Proof. by rewrite !(cfdot_sym xi) -rmorph_sub cfdot_subl. Qed.
Canonical cfun_dot_additive xi := Additive (cfdot_subr xi).

Lemma cfdot0r xi : '[xi, 0] = 0. Proof. exact: raddf0. Qed.
Lemma cfdotDr xi phi psi : '[xi, phi + psi] = '[xi, phi] + '[xi, psi].
Proof. exact: raddfD. Qed.
Lemma cfdotMnr xi phi n : '[xi, phi *+ n] = '[xi, phi] *+ n.
Proof. exact: raddfMn. Qed.
Lemma cfdot_sumr xi I r (P : pred I) (phi : I -> 'CF(G)) :
  '[xi, \sum_(i <- r | P i) phi i] = \sum_(i <- r | P i) '[xi, phi i].
Proof. exact: raddf_sum. Qed.
Lemma cfdotZr a xi phi : '[xi, a *: phi] = a^* * '[xi, phi].
Proof. by rewrite !(cfdot_sym xi) cfdotZl rmorphM. Qed.

Lemma posC_cfnorm phi : 0 <= '[phi].
Proof.
by rewrite posC_mul ?posC_inv ?posC_nat ?posC_sum // => x _; exact: posC_pconj.
Qed.

Lemma cfnorm_eq0 phi : ('[phi] == 0) = (phi == 0).
Proof.
apply/idP/eqP=> [|->]; last by rewrite cfdot0r.
rewrite mulf_eq0 invr_eq0 (negbTE (neq0GC G)) /= => /eqP/posC_sum_eq0 phi0.
apply/cfun_inP=> x Gx; apply/eqP; rewrite cfunE -normC_eq0 sqrtC_eq0.
rewrite phi0 // => [{x Gx} x _|]; first exact: posC_pconj.
by rewrite /index_enum -enumT mem_enum.
Qed.

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

Lemma cfunRes_subset (gT : finGroupType) (G H K : {group gT}) (phi : 'CF(G)) :
  H \subset K -> K \subset G -> 'Res[H] ('Res[K] phi) = 'Res[H] phi.
Proof.
move=> sHK sKG; apply/cfunP=> x; rewrite !cfunElock !genGid sHK sKG.
rewrite (subset_trans sHK) // !andbT -mulrnA mulnb.
by rewrite (andb_idl (subsetP sHK x)).
Qed.

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

Fact cfunQuo_subproof (phi : 'CF(G)) :
  is_class_fun <<G / B>> [ffun Bx : coset_of B =>
    oapp phi 0 [pick x0 | Bx \subset [set y | phi y == phi x0]]].
Proof.
rewrite genGid; apply: intro_class_fun => [|Bx].
  move=> _ _ /morphimP[x Nx _ ->] /morphimP[z Nz Gz ->]; congr (oapp _ _ _).
  apply: eq_pick => x0; rewrite -morphJ ?val_coset_prim ?groupJ //.
  rewrite -{1}(normP Nz) genJ -conjg_set1 -conjsMg sub_conjg.
  by apply: eq_subset_r => y; rewrite mem_conjgV !inE cfunJ.
case: pickP => //= x0; have{Bx} [x Nx ->] := cosetP Bx => phi_Bx not_GBx.
have{x0 phi_Bx} /eqP <-: phi x == phi x0.
  by have /implyP := subsetP phi_Bx x; rewrite inE val_coset_prim ?rcoset_refl.
by apply/cfun0/(contra _ not_GBx)=> Gx; exact: mem_morphim.
Qed.
Definition cfunQuo phi := Cfun 1 (cfunQuo_subproof phi).

(* Alternative definition, slightly shorter, but harder to reason about
Fact cfunQuo_subproof (phi : 'CF(G)) :
  is_class_fun <<G / B>>
     [ffun Bx : coset_of B => phi (repr (class_support Bx G)) *+ group_set B].
Proof.
rewrite genGid; apply: intro_class_fun => [Bx By | Bx].
  case/morphimP=> x Nx Gx -> /morphimP[y Ny Gy ->]; rewrite -morphJ //.
  rewrite /= !val_coset_prim ?groupJ //.
  by rewrite -{1}(normP Ny) genJ -conjg_set1 -conjsMg class_supportGidl.
have [x Nx -> {Bx}] := cosetP Bx; rewrite inE val_coset_prim //= => notGx.
case gB: (group_set B) => //; set BxG := class_support _ G.
have /mem_repr/imset2P[_ z /rcosetP[y By ->] Gz ->]: (x ^ 1)%g \in BxG.
  by rewrite mem_imset2 // rcoset_refl.
rewrite cfunJ {z Gz}// cfun0 //; apply: contra notGx => Gyx.
have Ny: y \in 'N(B) by rewrite -(gen_set_id gB) (subsetP (normG _)).
apply/imsetP; exists (y * x)%g; first by rewrite inE groupM.
by rewrite mkerl // ker_coset_prim inE By.
Qed.
*)

Definition cfunMod : 'CF(G / B) -> 'CF(G) := @cfunMorph _ _ _ _ _.

Local Notation "phi %% 'B'" := (cfunMod phi) (at level 40) : character_scope.

Lemma cfunModE phi x : B <| G -> x \in G -> (phi %% B)%CH x = phi (coset B x).
Proof. by move/normal_norm=> nBG; exact: cfunMorphE. Qed.

Canonical cfunMod_additive := [additive of cfunMod].
Canonical cfunMod_linear := [linear of cfunMod].

Lemma cfunMod1 : B <| G -> (1 %% B)%CH = 1.
Proof. by move/normal_norm=> nBG; exact: cfunMorph1. Qed.

(* cfunQuo is only linear on the class functions that have H in their kernel. *)

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

Fact cfunInd_subproof (phi : 'CF(A)) :
  is_class_fun G
    [ffun x => #|A|%:R^-1 * (\sum_(y \in G) phi (x ^ y)) *+ (x \in G)].
Proof.
apply: intro_class_fun => [x y Gx Gy | x /negbTE/=-> //].
rewrite Gx groupJ // (reindex_inj (mulgI y^-1)%g) /=; congr (_ * _).
apply: eq_big => [z | z Gz]; first by rewrite groupMl ?groupV.
by rewrite -conjgM mulKVg.
Qed.
Definition cfunInd phi := Cfun 1 (cfunInd_subproof phi).

End Def.

Local Notation "''Ind[' B , A ]" := (@cfunInd B A) : ring_scope.
Local Notation "''Ind[' B ]" := 'Ind[B, _] : ring_scope.

Variables G H : {group gT}.
Implicit Types (phi : 'CF(H)) (psi : 'CF(G)).

Lemma cfunIndE phi x :
  H \subset G -> 'Ind[G] phi x = #|H|%:R^-1 * (\sum_(y \in G) phi (x ^ y)).
Proof.
move=> sHG; rewrite cfunElock genGid.
have [// | notGx] := boolP (x \in G); rewrite big1 ?mulr0 // => y Gy.
by rewrite cfun0 // (contra (subsetP sHG _)) ?groupJr.
Qed.

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

Lemma cfunInd_is_linear : linear 'Ind[G, H].
Proof.
move=> c phi psi; apply/cfun_inP=> x Gx.
rewrite !cfunElock genGid Gx mulrCA -mulr_addr /=; congr (_ * _).
by rewrite big_distrr -big_split /=; apply: eq_bigr => y Gy /=; rewrite !cfunE.
Qed.
Canonical cfunInd_additive := Additive cfunInd_is_linear.
Canonical cfunInd_linear := Linear cfunInd_is_linear.

(* This is Isaacs, Lemma (5.2). *)
Lemma Frobenius_reciprocity phi psi :
  H \subset G -> '[phi, 'Res[H] psi]_H = '['Ind[G] phi, psi]_G.
Proof.
move=> sHG; transitivity (#|H|%:R^-1 * \sum_(x \in G) phi x * (psi x)^*).
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

Lemma cfunAutQuo (phi : 'CF(G)) : (phi / H)^u = (phi^u / H)%CH.
Proof.
apply/cfunP=> Hx; rewrite !cfunElock; set x0 := pick _; set x0u := pick _.
suffices <-: x0 = x0u by case: x0 => [x|]; rewrite /= ?cfunE ?rmorph0.
apply: eq_pick => {x0 x0u}x0; apply: eq_subset_r => y.
by rewrite !inE !cfunE (inj_eq (fmorph_inj u)).
Qed.

Lemma cfunAutMod (phi : 'CF(G / H)) : (phi %% H)^u = (phi^u %% H)%CH.
Proof. by apply/cfunP=> x; rewrite !cfunElock rmorphMn. Qed.

Lemma cfunAutInd (phi : 'CF(H)) : ('Ind[G] phi)^u = 'Ind phi^u.
Proof.
apply/cfun_inP=> x Gx; rewrite !cfunElock genGid Gx ?mulr1n.
rewrite rmorphM fmorphV rmorph_nat rmorph_sum; congr (_ * _).
by apply: eq_bigr => y Gy; rewrite !cfunE.
Qed.

(* GG: This holds for ^u as well, but the proof depends on the fact that *)
(* all automorphisms of algC commute with ^*. *)
Lemma conj_cfdot (phi psi : 'CF(G)) : '[phi, psi]^* = '[phi^*, psi^*].
Proof.
rewrite rmorphM fmorphV rmorph_nat rmorph_sum; congr (_ * _).
by apply: eq_bigr => x _; rewrite rmorphM !cfunE.
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
Let fG : f @* setX K H = G := proj2 (isomP (tagged fP)).
Let fK := @fst _ _ \o invm injf.
Let fH := @snd _ _ \o invm injf.

Definition cfun_dprodl := cfunMorph \o 'Res[fK @* G, K].
Definition cfun_dprodr := cfunMorph \o 'Res[fH @* G, H].
Definition cfun_dprod phi psi := cfun_dprodl phi * cfun_dprodr psi.

Let dK: G \subset 'dom fK.
Proof. by rewrite -sub_morphim_pre ?subsetT //= fG. Qed.

Let dH: G \subset 'dom fH.
Proof. by rewrite -sub_morphim_pre ?subsetT //= fG. Qed.

Let imK: fK @* G \subset K.
Proof. by rewrite -[G in _ @* G]fG morphim_comp im_invm morphim_fstX. Qed.

Let imH: fH @* G \subset H.
Proof. by rewrite -[G in _ @* G]fG morphim_comp im_invm morphim_sndX. Qed. 

Lemma cfun_dprod1r phi : cfun_dprod phi 1 = cfun_dprodl phi.
Proof. by rewrite /cfun_dprod /cfun_dprodr /= cfunRes1 ?cfunMorph1 ?mulr1. Qed.

Lemma cfun_dprod1l psi : cfun_dprod 1 psi = cfun_dprodr psi.
Proof. by rewrite /cfun_dprod /cfun_dprodl /= cfunRes1 ?cfunMorph1 ?mul1r. Qed.

Lemma cfun_dprodE phi psi :
  {in K & H, forall h k, cfun_dprod phi psi (h * k)%g = phi h * psi k}.
Proof.
move=> k h Kk Hh /=; move def_u: (k, h) => u.
have ->: (k * h)%g = f u by rewrite -def_u.
have{Kk Hh} KHu: u \in setX K H by rewrite -def_u inE Kk Hh.
have Gfu: f u \in G by rewrite -fG morphimEsub // mem_imset.
rewrite cfunE !cfunMorphE ?cfunResE //= ?morphimEsub //; try exact: mem_imset.
by rewrite !invmE // -def_u.
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
