(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div choice.
Require Import fintype prime finset fingroup morphism automorphism.

(******************************************************************************)
(* This file contains the definitions of:                                     *)
(*          coset_of H == the (sub)type of bilateral cosets of H (see below)  *)
(*             coset H == the canonical projection into coset_of H            *)
(*               A / H == the quotient of A by H, that is, the morphic image  *)
(*                        of A by coset H. We do not require H <| A, so in a  *)
(*                        textbook A / H would be written 'N_A(H) * H / H.    *)
(*   quotm f (nHG : H <| G) == the quotient morphism induced by f,            *)
(*                             mapping G / H onto f @* G / f @* H             *)
(*   qisom f (eqHG : H = G) == the identity isomorphism between               *)
(*                            [set: coset_of G] and [set: coset_of H].        *)
(* We also prove the three isomorphism theorems, and counting lemmas for      *)
(* morphisms.                                                                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section Cosets.

Variables (gT : finGroupType) (Q A : {set gT}).

(******************************************************************************)
(* Cosets are right cosets of elements in the normaliser                      *)
(* We let cosets coerce to GroupSet.sort, so they inherit the group subset    *)
(* base group structure. Later we will define a proper group structure on     *)
(* cosets, which will then hide the inherited structure once coset_of unifies *)
(* with FinGroup.sort; the coercion to GroupSet.sort will no longer be used.  *)
(*   Note that for Hx Hy : coset_of H, Hx * Hy : {set gT} can mean either     *)
(*    set_of_coset (mulg Hx Hy) OR mulg (set_of_coset Hx) (set_of_coset Hy)   *)
(* However, since the two terms are actually convertible, we can live with    *)
(* this ambiguity.                                                            *)
(*   We take great care that neither the type coset_of H, nor its Canonical   *)
(* finGroupType structure, nor the coset H morphism depend on the actual      *)
(* group structure of H. Otherwise, rewriting would be extremely awkward      *)
(* because all our equalities are stated at the set level.                    *)
(*   The trick we use is to interpret coset_of A, when A is any set, as the   *)
(* type of cosets of the group <A> generated by A, in the group A <*> N(A)    *)
(* generated by A and its normaliser. This coincides with the type of         *)
(* bilateral cosets of A when A is a group. We restrict the domain of coset A *)
(* to 'N(A), so that we get almost all the same conversion equalities as if   *)
(* we had forced A to be a group in the first place; the only exception, that *)
(* 1 : coset_of A : set _ = <<A>> rather than A, is covered by genGid.        *)
(******************************************************************************)

Notation H := <<A>>.
Definition coset_range := [pred B in rcosets H 'N(A)].

Record coset_of : Type :=
  Coset { set_of_coset :> GroupSet.sort gT; _ : coset_range set_of_coset }.

Canonical coset_subType :=
  Eval hnf in [subType for set_of_coset by coset_of_rect].
Definition coset_eqMixin := Eval hnf in [eqMixin of coset_of by <:].
Canonical coset_eqType := Eval hnf in EqType coset_of coset_eqMixin.
Definition coset_choiceMixin := [choiceMixin of coset_of by <:].
Canonical coset_choiceType := Eval hnf in ChoiceType coset_of coset_choiceMixin.
Definition coset_countMixin := [countMixin of coset_of by <:].
Canonical coset_countType := Eval hnf in CountType coset_of coset_countMixin.
Canonical coset_subCountType := Eval hnf in [subCountType of coset_of].
Definition coset_finMixin := [finMixin of coset_of by <:].
Canonical coset_finType := Eval hnf in FinType coset_of coset_finMixin.
Canonical coset_subFinType := Eval hnf in [subFinType of coset_of].

(* We build a new (canonical) structure of groupType for cosets.              *)
(* When A is a group, this is the largest possible quotient 'N(A) / A.        *)

Lemma coset_one_proof : coset_range H.
Proof. by apply/rcosetsP; exists (1 : gT); rewrite (group1, mulg1). Qed.
Definition coset_one := Coset coset_one_proof.

Let nNH := subsetP (norm_gen A).

Lemma coset_range_mul (B C : coset_of) : coset_range (B * C).
Proof.
case: B C => _ /= /rcosetsP[x Nx ->] [_ /= /rcosetsP[y Ny ->]].
by apply/rcosetsP; exists (x * y); rewrite !(groupM, rcoset_mul, nNH).
Qed.

Definition coset_mul B C := Coset (coset_range_mul B C).

Lemma coset_range_inv (B : coset_of) : coset_range B^-1.
Proof.
case: B => _ /= /rcosetsP[x Nx ->]; rewrite norm_rlcoset ?nNH // invg_lcoset.
by apply/rcosetsP; exists x^-1; rewrite ?groupV.
Qed.

Definition coset_inv B := Coset (coset_range_inv B).

Lemma coset_mulP : associative coset_mul.
Proof. by move=> B C D; apply: val_inj; rewrite /= mulgA. Qed.

Lemma coset_oneP : left_id coset_one coset_mul.
Proof.
case=> B coB; apply: val_inj => /=; case/rcosetsP: coB => x Hx ->{B}.
by rewrite mulgA mulGid.
Qed.

Lemma coset_invP : left_inverse coset_one coset_inv coset_mul.
Proof.
case=> B coB; apply: val_inj => /=; case/rcosetsP: coB => x Hx ->{B}.
rewrite invg_rcoset -mulgA (mulgA H) mulGid.
by rewrite norm_rlcoset ?nNH // -lcosetM mulVg mul1g.
Qed.

Definition coset_of_groupMixin :=
  FinGroup.Mixin coset_mulP coset_oneP coset_invP.

Canonical coset_baseGroupType :=
  Eval hnf in BaseFinGroupType coset_of coset_of_groupMixin.
Canonical coset_groupType := FinGroupType coset_invP.

(* Projection of the initial group type over the cosets groupType  *)

Definition coset x : coset_of := insubd (1 : coset_of) (H :* x).

(* This is a primitive lemma -- we'll need to restate it for *)
(* the case where A is a group. *)
Lemma val_coset_prim x : x \in 'N(A) -> coset x :=: H :* x.
Proof.
by move=> Nx; rewrite val_insubd /= mem_rcosets -{1}(mul1g x) mem_mulg.
Qed.

Lemma coset_morphM : {in 'N(A) &, {morph coset : x y / x * y}}.
Proof.
move=> x y Nx Ny; apply: val_inj.
by rewrite /= !val_coset_prim ?groupM //= rcoset_mul ?nNH.
Qed.

Canonical coset_morphism := Morphism coset_morphM.

Lemma ker_coset_prim : 'ker coset = 'N_H(A).
Proof.
apply/setP=> z; rewrite !in_setI andbC 2!inE -val_eqE /=.
case Nz: (z \in 'N(A)); rewrite ?andbF ?val_coset_prim // !andbT.
by apply/eqP/idP=> [<-| Az]; rewrite (rcoset_refl, rcoset_id).
Qed.

Implicit Type xbar : coset_of.

Lemma coset_mem y xbar : y \in xbar -> coset y = xbar.
Proof.
case: xbar => /= Hx NHx Hxy; apply: val_inj=> /=.
case/rcosetsP: NHx (NHx) Hxy => x Nx -> NHx Hxy.
by rewrite val_insubd /= (rcoset_transl Hxy) NHx.
Qed.

(* coset is an inverse to repr *)

Lemma mem_repr_coset xbar : repr xbar \in xbar.
Proof. case: xbar => /= _ /rcosetsP[x _ ->]; exact: mem_repr_rcoset. Qed.

Lemma repr_coset1 : repr (1 : coset_of) = 1.
Proof. exact: repr_group. Qed.

Lemma coset_reprK : cancel (fun xbar => repr xbar) coset.
Proof. by move=> xbar; exact: coset_mem (mem_repr_coset xbar). Qed.

(* cosetP is slightly stronger than using repr because we only *)
(* guarantee  repr xbar \in 'N(A) when A is a group.           *)
Lemma cosetP xbar : {x | x \in 'N(A) & xbar = coset x}.
Proof.
pose x := repr 'N_xbar(A).
have [xbar_x Nx]: x \in xbar /\ x \in 'N(A).
  apply/setIP; rewrite {}/x; case: xbar => /= _ /rcosetsP[y Ny ->].
  by apply: (mem_repr y); rewrite inE rcoset_refl.
by exists x; last rewrite (coset_mem xbar_x).
Qed.

Lemma coset_id x : x \in A -> coset x = 1.
Proof. by move=> Ax; apply: coset_mem; exact: mem_gen. Qed.

Lemma im_coset : coset @* 'N(A) = setT.
Proof.
by apply/setP=> xbar; case: (cosetP xbar) => x Nx ->; rewrite inE mem_morphim.
Qed.

Lemma sub_im_coset (C : {set coset_of}) : C \subset coset @* 'N(A).
Proof. by rewrite im_coset subsetT. Qed.

Lemma cosetpre_proper C D :
  (coset @*^-1 C \proper coset @*^-1 D) = (C \proper D).
Proof. by rewrite morphpre_proper ?sub_im_coset. Qed.

Definition quotient : {set coset_of} := coset @* Q.

Lemma quotientE : quotient = coset @* Q. Proof. by []. Qed.

End Cosets.

Prenex Implicits coset_of coset.
Arguments Scope quotient [_ group_scope group_scope].

Bind Scope group_scope with coset_of.

Notation "A / B" := (quotient A B) : group_scope.

Section CosetOfGroupTheory.

Variables (gT : finGroupType) (H : {group gT}).
Implicit Types (A B : {set gT}) (G K : {group gT}) (xbar yb : coset_of H).
Implicit Types (C D : {set coset_of H}) (L M : {group coset_of H}).

Canonical quotient_group G A : {group coset_of A} :=
  Eval hnf in [group of G / A].

Infix "/" := quotient_group : Group_scope.

Lemma val_coset x : x \in 'N(H) -> coset H x :=: H :* x.
Proof. by move=> Nx; rewrite val_coset_prim // genGid. Qed.

Lemma coset_default x : (x \in 'N(H)) = false -> coset H x = 1.
Proof.
move=> Nx; apply: val_inj.
by rewrite val_insubd /= mem_rcosets /= genGid mulSGid ?normG ?Nx.
Qed.

Lemma coset_norm xbar : xbar \subset 'N(H).
Proof.
case: xbar => /= _ /rcosetsP[x Nx ->].
by rewrite genGid mul_subG ?sub1set ?normG.
Qed.

Lemma ker_coset : 'ker (coset H) = H.
Proof. by rewrite ker_coset_prim genGid (setIidPl _) ?normG. Qed.

Lemma coset_idr x : x \in 'N(H) -> coset H x = 1 -> x \in H.
Proof. by move=> Nx Hx1; rewrite -ker_coset mem_morphpre //= Hx1 set11. Qed.

Lemma repr_coset_norm xbar : repr xbar \in 'N(H).
Proof. exact: subsetP (coset_norm _) _ (mem_repr_coset _). Qed.

Lemma imset_coset G : coset H @: G = G / H.
Proof.
apply/eqP; rewrite eqEsubset andbC imsetS ?subsetIr //=.
apply/subsetP=> _ /imsetP[x Gx ->].
by case Nx: (x \in 'N(H)); rewrite ?(coset_default Nx) ?mem_morphim ?group1.
Qed.

Lemma val_quotient A : val @: (A / H) = rcosets H 'N_A(H).
Proof.
apply/setP=> B; apply/imsetP/rcosetsP=> [[xbar Axbar]|[x /setIP[Ax Nx]]] ->{B}.
  case/morphimP: Axbar => x Nx Ax ->{xbar}.
  by exists x; [rewrite inE Ax | rewrite /= val_coset].
by exists (coset H x); [apply/morphimP; exists x | rewrite /= val_coset].
Qed.

Lemma card_quotient_subnorm A : #|A / H| = #|'N_A(H) : H|.
Proof. by rewrite -(card_imset _ val_inj) val_quotient. Qed.

Lemma leq_quotient A : #|A / H| <= #|A|.
Proof. exact: leq_morphim. Qed.

Lemma ltn_quotient A : H :!=: 1 -> H \subset A -> #|A / H| < #|A|.
Proof.
by move=> ntH sHA; rewrite ltn_morphim // ker_coset (setIidPr sHA) proper1G.
Qed.

Lemma card_quotient A : A \subset 'N(H) -> #|A / H| = #|A : H|.
Proof. by move=> nHA; rewrite card_quotient_subnorm (setIidPl nHA). Qed.

Lemma divg_normal G : H <| G -> #|G| %/ #|H| = #|G / H|.
Proof. by case/andP=> sHG nHG; rewrite divgS ?card_quotient. Qed.

(* Specializing all the morphisms lemmas that have different assumptions    *)
(* (e.g., because 'ker (coset H) = H), or conclusions (e.g., because we use *)
(* A / H rather than coset H @* A). We may want to reevaluate later, and    *)
(* eliminate variants that aren't used                                  .   *)

(* Variant of morph1; no specialization for other morph lemmas. *)
Lemma coset1 : coset H 1 :=: H.
Proof. by rewrite morph1 /= genGid. Qed.

(* Variant of kerE. *)
Lemma cosetpre1 : coset H @*^-1 1 = H.
Proof. by rewrite -kerE ker_coset. Qed.

(* Variant of morphimEdom; mophimE[sub] covered by imset_coset.   *)
(* morph[im|pre]Iim are also covered by im_quotient.              *)
Lemma im_quotient : 'N(H) / H = setT.
Proof. exact: im_coset. Qed.

Lemma quotientT : setT / H = setT.
Proof. by rewrite -im_quotient; exact: morphimT. Qed.

(* Variant of morphimIdom. *)
Lemma quotientInorm A : 'N_A(H) / H = A / H.
Proof. by rewrite /quotient setIC morphimIdom. Qed.

Lemma mem_quotient x G : x \in G -> coset H x \in G / H.
Proof. by move=> Gx; rewrite -imset_coset mem_imset. Qed.

Lemma quotientS A B : A \subset B -> A / H \subset B / H.
Proof. exact: morphimS. Qed.

Lemma quotient0 : set0 / H = set0.
Proof. exact: morphim0. Qed.

Lemma quotient_set1 x : x \in 'N(H) -> [set x] / H = [set coset H x].
Proof. exact: morphim_set1. Qed.

Lemma quotient1 : 1 / H = 1.
Proof. exact: morphim1. Qed.

Lemma quotientV A : A^-1 / H = (A / H)^-1.
Proof. exact: morphimV. Qed.

Lemma quotientMl A B : A \subset 'N(H) -> A * B / H = (A / H) * (B / H).
Proof. exact: morphimMl. Qed.

Lemma quotientMr A B : B \subset 'N(H) -> A * B / H = (A / H) * (B / H).
Proof. exact: morphimMr. Qed.

Lemma cosetpreM C D : coset H @*^-1 (C * D) = coset H @*^-1 C * coset H @*^-1 D.
Proof. by rewrite morphpreMl ?sub_im_coset. Qed.

Lemma quotientJ A x : x \in 'N(H) -> A :^ x / H = (A / H) :^ coset H x.
Proof. exact: morphimJ. Qed.

Lemma quotientU A B : (A :|: B) / H = A / H :|: B / H.
Proof. exact: morphimU. Qed.

Lemma quotientI A B : (A :&: B) / H \subset A / H :&: B / H.
Proof. exact: morphimI. Qed.

Lemma quotientY A B :
  A \subset 'N(H) -> B \subset 'N(H) -> (A <*> B) / H = (A / H) <*> (B / H).
Proof. exact: morphimY. Qed.

Lemma quotient_homg A : A \subset 'N(H) -> homg (A / H) A.
Proof. exact: morphim_homg. Qed.

Lemma coset_kerl x y : x \in H -> coset H (x * y) = coset H y.
Proof.
move=> Hx; case Ny: (y \in 'N(H)); first by rewrite mkerl ?ker_coset.
by rewrite !coset_default ?groupMl // (subsetP (normG H)).
Qed.

Lemma coset_kerr x y : y \in H -> coset H (x * y) = coset H x.
Proof.
move=> Hy; case Nx: (x \in 'N(H)); first by rewrite mkerr ?ker_coset.
by rewrite !coset_default ?groupMr // (subsetP (normG H)).
Qed.

Lemma rcoset_kercosetP x y :
  x \in 'N(H) -> y \in 'N(H) -> reflect (coset H x = coset H y) (x \in H :* y).
Proof. rewrite -{6}ker_coset; exact: rcoset_kerP. Qed.

Lemma kercoset_rcoset x y :
    x \in 'N(H) -> y \in 'N(H) ->
  coset H x = coset H y -> exists2 z, z \in H & x = z * y.
Proof. by move=> Nx Ny eqfxy; rewrite -ker_coset; exact: ker_rcoset. Qed.

Lemma quotientGI G A : H \subset G -> (G :&: A) / H = G / H :&: A / H.
Proof. by rewrite -{1}ker_coset; exact: morphimGI. Qed.

Lemma quotientIG A G : H \subset G -> (A :&: G) / H = A / H :&: G / H.
Proof. by rewrite -{1}ker_coset; exact: morphimIG. Qed.

Lemma quotientD A B : A / H :\: B / H \subset (A :\: B) / H.
Proof. exact: morphimD. Qed.

Lemma quotientD1 A : (A / H)^# \subset A^# / H.
Proof. exact: morphimD1. Qed.

Lemma quotientDG A G : H \subset G -> (A :\: G) / H = A / H :\: G / H.
Proof. by rewrite -{1}ker_coset; exact: morphimDG. Qed.

Lemma quotientK A : A \subset 'N(H) -> coset H @*^-1 (A / H) = H * A.
Proof. by rewrite -{8}ker_coset; exact: morphimK. Qed.

Lemma quotientYK G : G \subset 'N(H) -> coset H @*^-1 (G / H) = H <*> G.
Proof. by move=> nHG; rewrite quotientK ?norm_joinEr. Qed.

Lemma quotientGK G : H <| G -> coset H @*^-1 (G / H) = G.
Proof. by case/andP; rewrite -{1}ker_coset; exact: morphimGK. Qed.

Lemma quotient_class x A :
  x \in 'N(H) -> A \subset 'N(H) -> x ^: A / H  = coset H x ^: (A / H).
Proof. exact: morphim_class. Qed.

Lemma classes_quotient A :
  A \subset 'N(H) -> classes (A / H) = [set xA / H | xA in classes A].
Proof. exact: classes_morphim. Qed.

Lemma cosetpre_set1 x :
  x \in 'N(H) -> coset H @*^-1 [set coset H x] = H :* x.
Proof. by rewrite -{9}ker_coset; exact: morphpre_set1. Qed.

Lemma cosetpre_set1_coset xbar : coset H @*^-1 [set xbar] = xbar.
Proof. by case: (cosetP xbar) => x Nx ->; rewrite cosetpre_set1 ?val_coset. Qed.

Lemma cosetpreK C : coset H @*^-1 C / H = C.
Proof. by rewrite /quotient morphpreK ?sub_im_coset. Qed.

(* Variant of morhphim_ker *)
Lemma trivg_quotient : H / H = 1.
Proof. by rewrite -{3}ker_coset /quotient morphim_ker. Qed.

Lemma quotientS1 G : G \subset H -> G / H = 1.
Proof. by move=> sGH; apply/trivgP; rewrite -trivg_quotient quotientS. Qed.

Lemma sub_cosetpre M : H \subset coset H @*^-1 M.
Proof. by rewrite -{1}ker_coset; exact: ker_sub_pre. Qed.

Lemma quotient_proper G K :
  H <| G -> H <| K -> (G / H \proper K / H) = (G \proper K).
Proof. by move=> nHG nHK; rewrite -cosetpre_proper ?quotientGK. Qed.

Lemma normal_cosetpre M : H <| coset H @*^-1 M.
Proof. rewrite -{1}ker_coset; exact: ker_normal_pre. Qed.

Lemma cosetpreSK C D :
  (coset H @*^-1 C \subset coset H @*^-1 D) = (C \subset D).
Proof. by rewrite morphpreSK ?sub_im_coset. Qed.

Lemma sub_quotient_pre A C :
  A \subset 'N(H) -> (A / H \subset C) = (A \subset coset H @*^-1 C).
Proof. exact: sub_morphim_pre. Qed.

Lemma sub_cosetpre_quo C G :
  H <| G -> (coset H @*^-1 C \subset G) = (C \subset G / H).
Proof. by move=> nHG; rewrite -cosetpreSK quotientGK. Qed.

(* Variant of ker_trivg_morphim. *)
Lemma quotient_sub1 A : A \subset 'N(H) -> (A / H \subset [1]) = (A \subset H).
Proof. by move=> nHA /=; rewrite -{10}ker_coset ker_trivg_morphim nHA. Qed.

Lemma quotientSK A B :
  A \subset 'N(H) -> (A / H \subset B / H) = (A \subset H * B).
Proof. by move=> nHA; rewrite morphimSK ?ker_coset. Qed.

Lemma quotientSGK A G :
  A \subset 'N(H) -> H \subset G -> (A / H \subset G / H) = (A \subset G).
Proof. by rewrite -{2}ker_coset; exact: morphimSGK. Qed.

Lemma quotient_injG :
  {in [pred G : {group gT} | H <| G] &, injective (fun G => G / H)}.
Proof. by rewrite /normal -{1}ker_coset; exact: morphim_injG. Qed.

Lemma quotient_inj G1 G2 :
   H <| G1 -> H <| G2 -> G1 / H = G2 / H -> G1 :=: G2.
Proof. by rewrite /normal -{1 3}ker_coset; exact: morphim_inj. Qed.

Lemma quotient_neq1 A : H <| A -> (A / H != 1) = (H \proper A).
Proof.
case/andP=> sHA  nHA; rewrite /proper sHA -trivg_quotient eqEsubset andbC.
by rewrite quotientS //= quotientSGK.
Qed.

Lemma quotient_gen A : A \subset 'N(H) -> <<A>> / H = <<A / H>>.
Proof. exact: morphim_gen. Qed.

Lemma cosetpre_gen C :
  1 \in C -> coset H @*^-1 <<C>> = <<coset H @*^-1 C>>.
Proof. by move=> C1; rewrite morphpre_gen ?sub_im_coset. Qed.

Lemma quotientR A B :
  A \subset 'N(H) -> B \subset 'N(H) -> [~: A, B] / H = [~: A / H, B / H].
Proof. exact: morphimR. Qed.

Lemma quotient_norm A : 'N(A) / H \subset 'N(A / H).
Proof. exact: morphim_norm. Qed.

Lemma quotient_norms A B : A \subset 'N(B) -> A / H \subset 'N(B / H).
Proof. exact: morphim_norms. Qed.

Lemma quotient_subnorm A B : 'N_A(B) / H \subset 'N_(A / H)(B / H).
Proof. exact: morphim_subnorm. Qed.

Lemma quotient_normal A B : A <| B -> A / H <| B / H.
Proof. exact: morphim_normal. Qed.

Lemma quotient_cent1 x : 'C[x] / H \subset 'C[coset H x].
Proof.
case Nx: (x \in 'N(H)); first exact: morphim_cent1.
by rewrite coset_default // cent11T subsetT.
Qed.

Lemma quotient_cent1s A x : A \subset 'C[x] -> A / H \subset 'C[coset H x].
Proof.
by move=> sAC; exact: subset_trans (quotientS sAC) (quotient_cent1 x).
Qed.

Lemma quotient_subcent1 A x : 'C_A[x] / H \subset 'C_(A / H)[coset H x].
Proof. exact: subset_trans (quotientI _ _) (setIS _ (quotient_cent1 x)). Qed.

Lemma quotient_cent A : 'C(A) / H \subset 'C(A / H).
Proof. exact: morphim_cent. Qed.

Lemma quotient_cents A B : A \subset 'C(B) -> A / H \subset 'C(B / H).
Proof. exact: morphim_cents. Qed.

Lemma quotient_abelian A : abelian A -> abelian (A / H).
Proof. exact: morphim_abelian. Qed.

Lemma quotient_subcent A B : 'C_A(B) / H \subset 'C_(A / H)(B / H).
Proof. exact: morphim_subcent. Qed.

Lemma norm_quotient_pre A C :
  A \subset 'N(H) -> A / H \subset 'N(C) -> A \subset 'N(coset H @*^-1 C).
Proof.
by move/sub_quotient_pre=> -> /subset_trans-> //; exact: morphpre_norm.
Qed.

Lemma cosetpre_normal C D : (coset H @*^-1 C <| coset H @*^-1 D) = (C <| D).
Proof. by rewrite morphpre_normal ?sub_im_coset. Qed.

Lemma quotient_normG G : H <| G -> 'N(G) / H = 'N(G / H).
Proof.
case/andP=> sHG nHG.
by rewrite [_ / _]morphim_normG ?ker_coset // im_coset setTI.
Qed.

Lemma quotient_subnormG A G : H <| G -> 'N_A(G) / H = 'N_(A / H)(G / H).
Proof. by case/andP=> sHG nHG; rewrite -morphim_subnormG ?ker_coset. Qed.

Lemma cosetpre_cent1 x : 'C_('N(H))[x] \subset coset H @*^-1 'C[coset H x].
Proof.
case Nx: (x \in 'N(H)); first by rewrite morphpre_cent1.
by rewrite coset_default // cent11T morphpreT subsetIl.
Qed.

Lemma cosetpre_cent1s C x :
  coset H @*^-1 C \subset 'C[x] -> C \subset 'C[coset H x].
Proof.
move=> sC; rewrite -cosetpreSK; apply: subset_trans (cosetpre_cent1 x).
by rewrite subsetI subsetIl.
Qed.

Lemma cosetpre_subcent1 C x :
  'C_(coset H @*^-1 C)[x] \subset coset H @*^-1 'C_C[coset H x].
Proof.
by rewrite -morphpreIdom -setIA setICA morphpreI setIS // cosetpre_cent1.
Qed.

Lemma cosetpre_cent A : 'C_('N(H))(A) \subset coset H @*^-1 'C(A / H).
Proof. exact: morphpre_cent. Qed.

Lemma cosetpre_cents A C : coset H @*^-1 C \subset 'C(A) -> C \subset 'C(A / H).
Proof. by apply: morphpre_cents; rewrite ?sub_im_coset. Qed.

Lemma cosetpre_subcent C A :
  'C_(coset H @*^-1 C)(A) \subset coset H @*^-1 'C_C(A / H).
Proof. exact: morphpre_subcent. Qed.

Section InverseImage.

Variables (G : {group gT}) (Kbar : {group coset_of H}).

Hypothesis nHG : H <| G.

CoInductive inv_quotient_spec (P : pred {group gT}) : Prop :=
  InvQuotientSpec K of Kbar :=: K / H & H \subset K & P K.

Lemma inv_quotientS :
  Kbar \subset G / H -> inv_quotient_spec (fun K => K \subset G).
Proof.
case/andP: nHG => sHG nHG' sKbarG.
have sKdH: Kbar \subset 'N(H) / H by rewrite (subset_trans sKbarG) ?morphimS.
exists (coset H @*^-1 Kbar)%G; first by rewrite cosetpreK.
  by rewrite -{1}ker_coset morphpreS ?sub1G.
by rewrite sub_cosetpre_quo.
Qed.

Lemma inv_quotientN : Kbar <| G / H -> inv_quotient_spec (fun K => K <| G).
Proof.
move=> nKbar; case/inv_quotientS: (normal_sub nKbar) => K defKbar sHK sKG.
exists K => //; rewrite defKbar -cosetpre_normal !quotientGK // in nKbar.
exact: normalS nHG.
Qed.

End InverseImage.

Lemma quotientMidr A : A * H / H = A / H.
Proof.
by rewrite [_ /_]morphimMr ?normG //= -!quotientE trivg_quotient mulg1.
Qed.

Lemma quotientMidl A : H * A / H = A / H.
Proof.
by rewrite [_ /_]morphimMl ?normG //= -!quotientE trivg_quotient mul1g.
Qed.

Lemma quotientYidr G : G \subset 'N(H) -> G <*> H / H = G / H.
Proof.
move=> nHG; rewrite -genM_join quotient_gen ?mul_subG ?normG //.
by rewrite quotientMidr genGid.
Qed.

Lemma quotientYidl G : G \subset 'N(H) -> H <*> G / H = G / H.
Proof. by move=> nHG; rewrite joingC quotientYidr. Qed.

Section Injective.

Variables (G : {group gT}).
Hypotheses (nHG : G \subset 'N(H)) (tiHG : H :&: G = 1).

Lemma quotient_isom : isom G (G / H) (restrm nHG (coset H)).
Proof. by apply/isomP; rewrite ker_restrm setIC ker_coset tiHG im_restrm. Qed.

Lemma quotient_isog : isog G (G / H).
Proof. exact: isom_isog quotient_isom. Qed.

End Injective.

End CosetOfGroupTheory.

Notation "A / H" := (quotient_group A H) : Group_scope.

Section Quotient1.

Variables (gT : finGroupType) (A : {set gT}).

Lemma coset1_injm : 'injm (@coset gT 1).
Proof. by rewrite ker_coset /=. Qed.

Lemma quotient1_isom : isom A (A / 1) (coset 1).
Proof. by apply: sub_isom coset1_injm; rewrite ?norms1. Qed.

Lemma quotient1_isog : isog A (A / 1).
Proof. apply: isom_isog quotient1_isom; exact: norms1. Qed.

End Quotient1.

Section QuotientMorphism.

Variable (gT rT : finGroupType) (G H : {group gT}) (f : {morphism G >-> rT}).

Implicit Types A : {set gT}.
Implicit Types B : {set (coset_of H)}.
Hypotheses (nsHG : H <| G).
Let sHG : H \subset G := normal_sub nsHG.
Let nHG : G \subset 'N(H) := normal_norm nsHG.
Let nfHfG : f @* G \subset 'N(f @* H) := morphim_norms f nHG.

Notation fH := (coset (f @* H) \o f).

Lemma quotm_dom_proof : G \subset 'dom fH.
Proof. by rewrite -sub_morphim_pre. Qed.

Notation fH_G := (restrm quotm_dom_proof fH).

Lemma quotm_ker_proof : 'ker (coset H) \subset 'ker fH_G.
Proof.
by rewrite ker_restrm ker_comp !ker_coset morphpreIdom morphimK ?mulG_subr.
Qed.

Definition quotm := factm quotm_ker_proof nHG.

Canonical quotm_morphism := [morphism G / H of quotm].

Lemma quotmE x : x \in G -> quotm (coset H x) = coset (f @* H) (f x).
Proof. exact: factmE. Qed.

Lemma morphim_quotm A : quotm @* (A / H) = f @* A / f @* H.
Proof. by rewrite morphim_factm morphim_restrm morphim_comp morphimIdom. Qed.

Lemma morphpre_quotm Abar : quotm @*^-1 (Abar / f @* H) = f @*^-1 Abar / H.
Proof.
rewrite morphpre_factm morphpre_restrm morphpre_comp /=.
rewrite morphpreIdom -[Abar / _]quotientInorm quotientK ?subsetIr //=.
rewrite morphpreMl ?morphimS // morphimK // [_ * H]normC ?subIset ?nHG //.
rewrite -quotientE -mulgA quotientMidl /= setIC -morphpreIim setIA.
by rewrite (setIidPl nfHfG) morphpreIim -morphpreMl ?sub1G ?mul1g.
Qed.

Lemma ker_quotm : 'ker quotm = 'ker f / H.
Proof. by rewrite -morphpre_quotm /quotient morphim1. Qed.

Lemma injm_quotm : 'injm f -> 'injm quotm.
Proof. by move/trivgP=> /= kf1; rewrite ker_quotm kf1 quotientE morphim1. Qed.

End QuotientMorphism.

Section EqIso.

Variables (gT : finGroupType) (G H : {group gT}).

Hypothesis (eqGH : G :=: H).

Lemma im_qisom_proof : 'N(H) \subset 'N(G). Proof. by rewrite eqGH. Qed.
Lemma qisom_ker_proof : 'ker (coset G) \subset 'ker (coset H).
Proof. by rewrite eqGH. Qed.
Lemma qisom_restr_proof : setT \subset 'N(H) / G.
Proof. by rewrite eqGH im_quotient. Qed.

Definition qisom :=
  restrm qisom_restr_proof (factm qisom_ker_proof im_qisom_proof).

Canonical qisom_morphism := Eval hnf in [morphism of qisom].

Lemma qisomE x : qisom (coset G x) = coset H x.
Proof.
case Nx: (x \in 'N(H)); first exact: factmE.
by rewrite !coset_default ?eqGH ?morph1.
Qed.

Lemma val_qisom Gx : val (qisom Gx) = val Gx.
Proof.
by case: (cosetP Gx) => x Nx ->{Gx}; rewrite qisomE /= !val_coset -?eqGH.
Qed.

Lemma morphim_qisom A : qisom @* (A / G) = A / H.
Proof. by rewrite morphim_restrm setTI morphim_factm. Qed.

Lemma morphpre_qisom A : qisom @*^-1 (A / H) = A / G.
Proof.
rewrite morphpre_restrm setTI morphpre_factm eqGH.
by rewrite morphpreK // im_coset subsetT.
Qed.

Lemma injm_qisom : 'injm qisom.
Proof. by rewrite -quotient1 -morphpre_qisom morphpreS ?sub1G. Qed.

Lemma im_qisom : qisom @* setT = setT.
Proof. by rewrite -{2}im_quotient morphim_qisom eqGH im_quotient. Qed.

Lemma qisom_isom : isom setT setT qisom.
Proof. by apply/isomP; rewrite injm_qisom im_qisom. Qed.

Lemma qisom_isog : [set: coset_of G] \isog [set: coset_of H].
Proof. exact: isom_isog qisom_isom. Qed.

Lemma qisom_inj : injective qisom.
Proof. by move=> x y; apply: (injmP _ injm_qisom); rewrite inE. Qed.

Lemma morphim_qisom_inj : injective (fun Gx => qisom @* Gx).
Proof.
by move=> Gx Gy; apply: injm_morphim_inj; rewrite (injm_qisom, subsetT).
Qed.

End EqIso.

Implicit Arguments qisom_inj [gT G H].
Implicit Arguments morphim_qisom_inj [gT G H].

Section FirstIsomorphism.

Variables aT rT : finGroupType.

Lemma first_isom (G : {group aT}) (f : {morphism G >-> rT}) :
  {g : {morphism G / 'ker f >-> rT} | 'injm g &
      forall A : {set aT}, g @* (A / 'ker f) = f @* A}.
Proof.
have nkG := ker_norm f.
have skk: 'ker (coset ('ker f)) \subset 'ker f by rewrite ker_coset.
exists (factm_morphism skk nkG) => /=; last exact: morphim_factm.
by rewrite ker_factm -quotientE trivg_quotient.
Qed.

Variables (G H : {group aT}) (f : {morphism G >-> rT}).
Hypothesis sHG : H \subset G.

Lemma first_isog : (G / 'ker f) \isog (f @* G).
Proof.
by case: (first_isom f) => g injg im_g; apply/isogP; exists g; rewrite ?im_g.
Qed.

Lemma first_isom_loc : {g : {morphism H / 'ker_H f >-> rT} |
 'injm g & forall A : {set aT}, A \subset H -> g @* (A / 'ker_H f) = f @* A}.
Proof.
case: (first_isom (restrm_morphism sHG f)).
rewrite ker_restrm => g injg im_g; exists g => // A sAH.
by rewrite im_g morphim_restrm (setIidPr sAH).
Qed.

Lemma first_isog_loc : (H / 'ker_H f) \isog (f @* H).
Proof.
by case: first_isom_loc => g injg im_g; apply/isogP; exists g; rewrite ?im_g.
Qed.

End FirstIsomorphism.

Section SecondIsomorphism.

Variables (gT : finGroupType) (H K : {group gT}).

Hypothesis nKH : H \subset 'N(K).

Lemma second_isom : {f : {morphism H / (K :&: H) >-> coset_of K} |
  'injm f & forall A : {set gT}, A \subset H -> f @* (A / (K :&: H)) = A / K}.
Proof.
have ->: K :&: H = 'ker_H (coset K) by rewrite ker_coset setIC.
exact: first_isom_loc.
Qed.

Lemma second_isog : H / (K :&: H) \isog H / K.
Proof. by rewrite setIC -{1 3}(ker_coset K); exact: first_isog_loc. Qed.

Lemma weak_second_isog : H / (K :&: H) \isog H * K / K.
Proof. by rewrite quotientMidr; exact: second_isog. Qed.

End SecondIsomorphism.

Section ThirdIsomorphism.

Variables (gT : finGroupType) (G H K : {group gT}).

Lemma homg_quotientS (A : {set gT}) :
  A \subset 'N(H) -> A \subset 'N(K) -> H \subset K -> A / K \homg A / H.
Proof.
rewrite -!(gen_subG A) /=; set L := <<A>> => nHL nKL sKH.
have sub_ker: 'ker (restrm nHL (coset H)) \subset 'ker (restrm nKL (coset K)).
  by rewrite !ker_restrm !ker_coset setIS.
have sAL: A \subset L := subset_gen A; rewrite -(setIidPr sAL).
rewrite -[_ / H](morphim_restrm nHL) -[_ / K](morphim_restrm nKL) /=.
by rewrite -(morphim_factm sub_ker (subxx L)) morphim_homg ?morphimS.
Qed.

Hypothesis sHK : H \subset K.
Hypothesis snHG : H <| G.
Hypothesis snKG : K <| G.

Theorem third_isom : {f : {morphism (G / H) / (K / H) >-> coset_of K} | 'injm f
   & forall A : {set gT}, A \subset G -> f @* (A / H / (K / H)) = A / K}.
Proof.
have [[sKG nKG] [sHG nHG]] := (andP snKG, andP snHG).
have sHker: 'ker (coset H) \subset 'ker (restrm nKG (coset K)).
  by rewrite ker_restrm !ker_coset subsetI sHG.
have:= first_isom_loc (factm_morphism sHker nHG) (subxx _) => /=.
rewrite ker_factm_loc ker_restrm ker_coset !(setIidPr sKG) /= -!quotientE.
case=> f injf im_f; exists f => // A sAG; rewrite im_f ?morphimS //.
by rewrite morphim_factm morphim_restrm (setIidPr sAG).
Qed.

Theorem third_isog : (G / H / (K / H)) \isog (G / K).
Proof.
by case: third_isom => f inj_f im_f; apply/isogP; exists f; rewrite ?im_f.
Qed.

End ThirdIsomorphism.

Lemma char_from_quotient (gT : finGroupType) (G H K : {group gT}) :
  H <| K -> H \char G -> K / H \char G / H -> K \char G.
Proof.
case/andP=> sHK nHK chHG.
have nsHG := char_normal chHG; have [sHG nHG] := andP nsHG.
case/charP; rewrite quotientSGK // => sKG /= chKG.
apply/charP; split=> // f injf Gf; apply/morphim_fixP => //.
rewrite -(quotientSGK _ sHK); last by rewrite -morphimIim Gf subIset ?nHG.
have{chHG} Hf: f @* H = H by case/charP: chHG => _; apply.
set q := quotm_morphism f nsHG; have{injf}: 'injm q by exact: injm_quotm.
have: q @* _ = _ := morphim_quotm _ _ _; move: q; rewrite Hf => q im_q injq.
by rewrite -im_q chKG // im_q Gf.
Qed.

(* Counting lemmas for morphisms. *)

Section CardMorphism.

Variables (aT rT : finGroupType) (D : {group aT}) (f : {morphism D >-> rT}).
Implicit Types G H : {group aT}.
Implicit Types L M : {group rT}.

Lemma card_morphim G : #|f @* G| = #|D :&: G : 'ker f|.
Proof.
rewrite -morphimIdom -indexgI -card_quotient; last first.
  by rewrite normsI ?normG ?subIset ?ker_norm.
by apply: esym (card_isog _); rewrite first_isog_loc ?subsetIl.
Qed.

Lemma dvdn_morphim G : #|f @* G| %| #|G|.
Proof.
rewrite card_morphim (dvdn_trans (dvdn_indexg _ _)) //.
by rewrite cardSg ?subsetIr.
Qed.

Lemma logn_morphim p G : logn p #|f @* G| <= logn p #|G|.
Proof. by rewrite dvdn_leq_log ?dvdn_morphim. Qed.

Lemma coprime_morphl G p : coprime #|G| p -> coprime #|f @* G| p.
Proof. exact: coprime_dvdl (dvdn_morphim G). Qed.

Lemma coprime_morphr G p : coprime p #|G| -> coprime p #|f @* G|.
Proof. exact: coprime_dvdr (dvdn_morphim G). Qed.

Lemma coprime_morph G H : coprime #|G| #|H| -> coprime #|f @* G| #|f @* H|.
Proof. by move=> coGH; rewrite coprime_morphl // coprime_morphr. Qed.

Lemma index_morphim_ker G H :
    H \subset G -> G \subset D ->
  (#|f @* G : f @* H| * #|'ker_G f : H|)%N = #|G : H|.
Proof.
move=> sHG sGD; apply/eqP.
rewrite -(eqn_pmul2l (cardG_gt0 (f @* H))) mulnA Lagrange ?morphimS //.
rewrite !card_morphim (setIidPr sGD) (setIidPr (subset_trans sHG sGD)).
rewrite -(eqn_pmul2l (cardG_gt0 ('ker_H f))) /=.
by rewrite -{1}(setIidPr sHG) setIAC mulnCA mulnC mulnA !LagrangeI Lagrange.
Qed.

Lemma index_morphim G H : G :&: H \subset D -> #|f @* G : f @* H| %| #|G : H|.
Proof.
move=> dGH; rewrite -(indexgI G) -(setIidPr dGH) setIA.
apply: dvdn_trans (indexSg (subsetIl _ H) (subsetIr D G)).
rewrite -index_morphim_ker ?subsetIl ?subsetIr ?dvdn_mulr //= morphimIdom.
by rewrite indexgS ?morphimS ?subsetIr.
Qed.

Lemma index_injm G H : 'injm f -> G \subset D -> #|f @* G : f @* H| = #|G : H|.
Proof.
move=> injf dG; rewrite -{2}(setIidPr dG) -(indexgI _ H) /=.
rewrite -index_morphim_ker ?subsetIl ?subsetIr //= setIAC morphimIdom setIC.
rewrite injmI ?subsetIr // indexgI /= morphimIdom setIC ker_injm //.
by rewrite -(indexgI (1 :&: _)) /= -setIA !(setIidPl (sub1G _)) indexgg muln1.
Qed.

Lemma card_morphpre L : L \subset f @* D -> #|f @*^-1 L| = (#|'ker f| * #|L|)%N.
Proof.
move/morphpreK=> {2} <-; rewrite card_morphim morphpreIdom.
by rewrite Lagrange // morphpreS ?sub1G.
Qed.

Lemma index_morphpre L M :
  L \subset f @* D -> #|f @*^-1 L : f @*^-1 M| = #|L : M|.
Proof.
move=> dL; rewrite -!divgI -morphpreI card_morphpre //.
have: L :&: M \subset f @* D by rewrite subIset ?dL.
by move/card_morphpre->; rewrite divnMl ?cardG_gt0.
Qed.

End CardMorphism.

Lemma card_homg (aT rT : finGroupType) (G : {group aT}) (R : {group rT}) :
  G \homg R -> #|G| %| #|R|.
Proof. by case/homgP=> f <-; rewrite card_morphim setIid dvdn_indexg. Qed.

Section CardCosetpre.

Variables (gT : finGroupType) (G H K : {group gT}) (L M : {group coset_of H}).

Lemma dvdn_quotient : #|G / H| %| #|G|.
Proof. exact: dvdn_morphim. Qed.

Lemma index_quotient_ker :
     K \subset G -> G \subset 'N(H) ->
  (#|G / H : K / H| * #|G :&: H : K|)%N = #|G : K|.
Proof. by rewrite -{5}(ker_coset H); exact: index_morphim_ker. Qed.

Lemma index_quotient : G :&: K \subset 'N(H) -> #|G / H : K / H| %| #|G : K|.
Proof. exact: index_morphim. Qed.

Lemma index_quotient_eq :
    G :&: H \subset K -> K \subset G -> G \subset 'N(H) ->
  #|G / H : K / H| = #|G : K|.
Proof.
move=> sGH_K sKG sGN; rewrite -index_quotient_ker {sKG sGN}//.
by rewrite -(indexgI _ K) (setIidPl sGH_K) indexgg muln1.
Qed.

Lemma card_cosetpre : #|coset H @*^-1 L| = (#|H| * #|L|)%N.
Proof. by rewrite card_morphpre ?ker_coset ?sub_im_coset. Qed.

Lemma index_cosetpre : #|coset H @*^-1 L : coset H @*^-1 M| = #|L : M|.
Proof. by rewrite index_morphpre ?sub_im_coset. Qed.

End CardCosetpre.
