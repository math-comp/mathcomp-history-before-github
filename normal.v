(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Cosets, quotients, and isomorphism theorems                        *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
Require Import ssreflect.
Require Import ssrbool.
Require Import ssrfun.
Require Import eqtype.
Require Import ssrnat.
(* Require Import seq. *)
(* Require Import paths. *)
(* Require Import connect. *)
Require Import fintype.
Require Import finfun.
Require Import finset.
Require Import div.
Require Import groups.
Require Import morphisms.
Require Import automorphism.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.


(********************************************************************)
(*       Cosets are right cosets of elements in the normaliser      *)
(********************************************************************)

Section Cosets.

Variables (gT : finGroupType) (Q A : {set gT}).

(* We let cosets coerce to GroupSet.sort, so they inherit the group  *)
(* subset base group structure. Later we will define a proper group  *)
(* structure on cosets, which will then hide the inherited structure *)
(* once coset_of unifies with FinGroup.sort; the coercion to         *)
(* GroupSet.sort will no longer be used.                             *)
(*   Note that for Hx Hy : coset_of H, Hx * Hy : {set gT} can mean   *)
(*      either set_of_coset (mulg Hx Hy)                             *)
(*          OR mulg (set_of_coset Hx) (set_of_coset Hy)              *)
(* However, since the two terms are actually convertible, we can     *)
(* live with this ambiguity.                                         *)
(*   We take great care that neither the type coset_of H, its        *)
(* finGroupType structure, nor the coset H morphism depend on the    *)
(* actual group structure of H. Otherwise, rewriting would be        *)
(* extremely awkward because all our equalities are stated at the    *)
(* set level.                                                        *)
(*   The trick we use is to interpret coset_of A, when A is any set, *)
(* as the type of cosets of the group <A> generated by A, in the     *)
(* group <A, N(A)> generated by A and its normaliser. This coincides *)
(* with the type of bilateral cosets of A when A is a group. We      *)
(* restrict the domain of coset_of A to 'N(A), so that we get almost *)
(* all the same conversion equalities as if we had forced A to be a  *)
(* group in the first place -- the only exception is that            *)
(*      1 : coset_of A : set _ = <<A>> rather than A,                *)
(* is covered by the genGid lemma.                                   *)

Notation H := <<A>>.
Definition coset_range := [pred B \in rcosets H 'N(A)].

Record coset_of : Type :=
  Coset { set_of_coset :> GroupSet.sort gT; _ : coset_range set_of_coset }.

Canonical Structure coset_subType := SubType set_of_coset coset_of_rect vrefl.
Canonical Structure coset_eqType := Eval hnf in [subEqType for set_of_coset].
Canonical Structure coset_finType := Eval hnf in [finType of coset_of by :>].
Canonical Structure coset_subFinType := Eval hnf in [subFinType of coset_of].

(* We build a new (canonical) structure of groupType for cosets.      *)
(* When A is a group, this is the largest possible quotient 'N(H) / H *)

Lemma coset_range_unit : coset_range H.
Proof. by apply/rcosetsP; exists (1 : gT); rewrite (group1, mulg1). Qed.
Definition coset_unit := Coset coset_range_unit.

Let nNH := subsetP (norm_gen A).

Lemma coset_range_mul : forall B C : coset_of, coset_range (B * C).
Proof.
case=> B /=; case/rcosetsP=> x Nx ->{B} [C] /=; case/rcosetsP=> y Ny ->{C}.
by apply/rcosetsP; exists (x * y); rewrite !(groupM, rcoset_mul, nNH).
Qed.

Definition coset_mul B C := Coset (coset_range_mul B C).

Lemma coset_range_inv : forall B : coset_of, coset_range B^-1.
Proof.
case=> B /=; case/rcosetsP=> x Nx ->{B}.
rewrite norm_rlcoset ?nNH // invg_lcoset.
by apply/rcosetsP; exists x^-1; rewrite ?groupV.
Qed.

Definition coset_inv B := Coset (coset_range_inv B).

Lemma coset_mulP : associative coset_mul.
Proof. by move=> B C D; apply: val_inj; rewrite /= mulgA. Qed.

Lemma coset_unitP : left_unit coset_unit coset_mul.
Proof.
case=> B coB; apply: val_inj => /=; case/rcosetsP: coB => x Hx ->{B}.
by rewrite mulgA mulGid.
Qed.

Lemma coset_invP : left_inverse coset_unit coset_inv coset_mul.
Proof.
case=> B coB; apply: val_inj => /=; case/rcosetsP: coB => x Hx ->{B}.
rewrite invg_rcoset -mulgA (mulgA H) mulGid.
by rewrite norm_rlcoset ?nNH // -lcosetM mulVg mul1g.
Qed.

Canonical Structure coset_preGroupType :=
  [baseFinGroupType of coset_of by coset_mulP, coset_unitP & coset_invP].
Canonical Structure coset_groupType := FinGroupType coset_invP.

(* GG -- we dont use repr anymore 
Lemma norm_repr_coset : forall xbar : coset, repr xbar \in 'N(H).
Proof.
case=> C /=; case/rcosetsP=> x Nx ->{C}.
case: (repr_rcosetP [group of H]) => /=.
by move=> z Hz; rewrite groupMr //= (subsetP (normG _)).
Qed.
*)

(* Projection of the initial group type over the cosets groupType  *)

Definition coset x : coset_of := insubd (1 : coset_of) (H :* x).

(* This is a primitive lemma -- we'll need to restate it for *)
(* the case where A is a group. *)
Lemma val_coset_prim : forall x, x \in 'N(A) -> coset x :=: H :* x.
Proof.
by move=> x Nx; rewrite val_insubd /= mem_rcosets -{1}(mul1g x) mem_mulg.
Qed.

(* GG -- completely redundant with the generic morphism theory
Lemma coset_ofV : {morph coset_of : x / x^-1}.
Proof.
move=> x; apply: val_inj; rewrite /= !val_coset_of groupV /=.
by case: ifP => Nx; rewrite Nx ?invGid // -invg_lcoset norm_rlcoset.
Qed.
*)

Lemma coset_morphM : {in 'N(A) &, {morph coset : x y / x * y}}.
Proof.
move=> x y Nx Ny; apply: val_inj.
by rewrite /= !val_coset_prim ?groupM //= rcoset_mul ?nNH.
Qed.

Canonical Structure coset_morphism := Morphism coset_morphM.

Lemma ker_coset_prim : 'ker coset = 'N_H(A).
Proof.
apply/setP=> z; rewrite !in_setI andbC 2!inE -val_eqE /=.
case Nz: (z \in 'N(A)); rewrite ?andbF ?val_coset_prim // !andbT.
by apply/eqP/idP=> [<-| Az]; rewrite (rcoset_refl, rcoset_id).
Qed.

Implicit Type xb : coset_of.

Lemma coset_mem : forall y xb, y \in xb -> coset y = xb.
Proof.
move=> y [/= Hx NHx] /= Hxy; apply: val_inj=> /=.
case/rcosetsP: NHx (NHx) Hxy => x Nx -> NHx Hxy.
by rewrite val_insubd /= (rcoset_transl Hxy) NHx.
Qed.

Lemma cosetP : forall xb, {x | x \in 'N(A) & xb = coset x}.
Proof.
move=> xb; pose x := repr 'N_xb(A).
have [xb_x Nx]: x \in xb /\ x \in 'N(A).
  apply/setIP; rewrite {}/x; case: xb => Hy /=; case/rcosetsP=> y Ny ->.
  by apply: (@mem_repr _ y); rewrite inE rcoset_refl.
by exists x; last rewrite (coset_mem xb_x).
Qed.

Lemma coset_id : forall x, x \in A -> coset x = 1.
Proof. move=> x Ax; apply: coset_mem; exact: mem_gen. Qed.

Lemma coset_imT : coset @* 'N(A) = setT.
Proof.
by apply/setP=> xb; case: (cosetP xb) => x Nx ->{xb}; rewrite inE mem_morphim.
Qed.

Lemma coset_im : forall C : {set coset_of}, C \subset coset @* 'N(A).
Proof. by move=> C; rewrite coset_imT subsetT. Qed.

Definition quotient : {set coset_of} := coset @* Q.

Lemma quotientE : quotient = coset @* Q. Proof. by []. Qed.

End Cosets.

Prenex Implicits coset_of coset.

Notation "A / B" := (quotient A B) : group_scope.

Section CosetOfGroupTheory.

Variables (gT : finGroupType) (H : {group gT}).
Implicit Types A B : {set gT}.
Implicit Types G K : {group gT}.
Implicit Types xb yb : coset_of H.
Implicit Types C D : {set coset_of H}.
Implicit Types L M : {group coset_of H}.

Canonical Structure quotient_group G A : {group coset_of A} :=
  Eval hnf in [group of G / A].

Infix "/" := quotient_group : subgroup_scope.

Lemma val_coset : forall x, x \in 'N(H) -> coset H x :=: H :* x.
Proof. by move=> x Nx; rewrite val_coset_prim // genGid. Qed.

Lemma coset_default : forall x, (x \in 'N(H)) = false -> coset H x = 1.
Proof.
move=> x Nx; apply: val_inj.
by rewrite val_insubd /= mem_rcosets /= genGid mulSGid ?normG ?Nx.
Qed.

Lemma coset_norm : forall xb, xb \subset 'N(H).
Proof.
case=> Hx /=; case/rcosetsP=> x Nx ->.
by rewrite genGid mul_subG ?sub1set ?normG.
Qed.

Lemma ker_coset : 'ker (coset H) = H.
Proof. by rewrite ker_coset_prim genGid (setIidPl _) ?normG. Qed.

Lemma coset_idr : forall x, x \in 'N(H) -> coset H x = 1 -> x \in H.
Proof. by move=> x Nx Hx1; rewrite -ker_coset mem_morphpre //= Hx1 set11. Qed.

(* deprecated -- GG
Lemma norm_repr_cosetG : forall xbar : coset H, repr xbar \in 'N(H).
Proof. by move=> xbar; rewrite -{2}(genGid H) norm_repr_coset. Qed.

Lemma coset_of_repr : forall xbar : coset H, cH (repr xbar) = xbar.
Proof.
move=> xbar; apply: val_inj; rewrite /= set_of_coset_of norm_repr_cosetG.
case: xbar => A /=; case/rcosetsP=> x; rewrite genGid => Nx ->{A}.
exact: rcoset_repr.
Qed.

Lemma cosetP : forall xbar, {x | x \in 'N(H) & xbar = cH x}.
Proof.
by move=> xbar; exists (repr xbar); rewrite ?coset_of_repr ?norm_repr_cosetG.
Qed.
*)

Lemma imset_coset : forall G, coset H @: G = G / H.
Proof.
move=> G; apply/eqP; rewrite eqset_sub andbC imsetS ?subsetIr //=.
apply/subsetP=> xb; case/imsetP=> x Gx -> {xb}.
by case Nx: (x \in 'N(H)); rewrite ?(coset_default Nx) ?mem_morphim ?group1.
Qed.

Lemma val_quotient : forall A, val @: (A / H) = rcosets H 'N_A(H).
Proof.
move=> A; apply/setP=> B; apply/imsetP/rcosetsP=> [[xb Axb]|[x ANx]] ->{B}.
  case/morphimP: Axb => x Nx Ax ->{xb}.
  by exists x; [rewrite inE Ax | rewrite /= val_coset].
case/setIP: ANx => Ax Nx.
by exists (coset H x); [apply/morphimP; exists x | rewrite /= val_coset].
Qed.

Lemma card_quotient_subnorm : forall A, #|A / H| = #|'N_A(H) : H|.
Proof. by move=> A; rewrite -(card_imset _ val_inj) val_quotient. Qed.

Lemma card_quotient : forall A, A \subset 'N(H) -> #|A / H| = #|A : H|.
Proof. by move=> A nHA; rewrite card_quotient_subnorm (setIidPl nHA). Qed.

(* GG -- identical to coset_id 
Lemma coset_ker : forall x, x \in H -> cH x = 1.
Proof. rewrite -{1}ker_coset; exact: mker. Qed.
*)

(* GG -- replacing "coset image" by "quotient" throughout, merging sections *)
(* I'm completing the lemma set, specializing all the morphisms lemmas that *)
(* have different assumptions (e.g., because 'ker (coset H) = H), or        *)
(* conclusions (e.g., because we use A / H rather than coset H @* A). We    *)
(* may want to reevaluate later, and eliminate variants that aren't used.   *)

(* Variant of morph1; no specialization for other morph lemmas. *)
Lemma coset1 : coset H 1 :=: H.
Proof. by rewrite morph1 /= genGid. Qed.

(* Variant of kerE. *)
Lemma cosetpre1 : coset H @*^-1 1 = H.
Proof. by rewrite -kerE ker_coset. Qed.

(* Variant of morphimEdom; mophimE[sub] covered by imset_coset. *)
(* morph[im|pre]Iim are also covered by quotientT.              *)
Lemma quotientT : 'N(H) / H = setT.
Proof. exact: coset_imT. Qed.

(* Variant of morphimIdom. *)
Lemma quotientInorm : forall A, 'N_A(H) / H = A / H.
Proof. by move=> A; rewrite /quotient setIC morphimIdom. Qed.

Lemma mem_quotient : forall x G, x \in G -> coset H x \in G / H.
Proof. by move=> x G Gx; rewrite -imset_coset mem_imset. Qed.

Lemma quotientS : forall A B, A \subset B -> A / H \subset B / H.
Proof. exact: morphimS. Qed.

Lemma quotient0 : set0 / H = set0.
Proof. exact: morphim0. Qed.

Lemma quotient_set1 : forall x, x \in 'N(H) -> [set x] / H = [set coset H x].
Proof. exact: morphim_set1. Qed.

Lemma quotient1 : 1 / H = 1.
Proof. exact: morphim1. Qed.

Lemma quotientV : forall A, A^-1 / H = (A / H)^-1.
Proof. exact: morphimV. Qed.

Lemma quotientMl : forall A B,
  A \subset 'N(H) -> A * B / H = (A / H) * (B / H).
Proof. exact: morphimMl. Qed.

Lemma quotientMr : forall A B,
  B \subset 'N(H) -> A * B / H = (A / H) * (B / H).
Proof. exact: morphimMr. Qed.

Lemma cosetpreM : forall C D,
  coset H @*^-1 (C * D) = coset H @*^-1 C * coset H @*^-1 D.
Proof. by move=> C D; rewrite morphpreMl ?coset_im. Qed.

Lemma quotientJ : forall A x, x \in 'N(H) -> A :^ x / H = (A / H) :^ coset H x.
Proof. exact: morphimJ. Qed.

Lemma quotientU : forall A B, (A :|: B) / H = A / H :|: B / H.
Proof. exact: morphimU. Qed.

Lemma quotientI : forall A B, (A :&: B) / H \subset A / H :&: B / H.
Proof. exact: morphimI. Qed.

Lemma coset_kerl : forall x y, x \in H -> coset H (x * y) = coset H y.
Proof.
move=> x y Hx; case Ny: (y \in 'N(H)); first by rewrite mkerl ?ker_coset.
by rewrite !coset_default ?groupMl // (subsetP (normG H)).
Qed.

Lemma coset_kerr : forall x y, y \in H -> coset H (x * y) = coset H x.
Proof.
move=> x y Hy; case Nx: (x \in 'N(H)); first by rewrite mkerr ?ker_coset.
by rewrite !coset_default ?groupMr // (subsetP (normG H)).
Qed.

Lemma rcoset_kercosetP : forall x y,
  x \in 'N(H) -> y \in 'N(H) -> reflect (coset H x = coset H y) (x \in H :* y).
Proof. rewrite -{6}ker_coset; exact: rcoset_kerP. Qed.

Lemma kercoset_rcoset : forall x y,
  x \in 'N(H) -> y \in 'N(H) ->
    coset H x = coset H y -> exists2 z, z \in H & x = z * y.
Proof. move=> x y Gx Gy eqfxy; rewrite -ker_coset; exact: ker_rcoset. Qed.

Lemma quotientGI : forall G A, H \subset G -> (G :&: A) / H = G / H :&: A / H.
Proof. rewrite -{1}ker_coset; exact: morphimGI. Qed.

Lemma quotientIG : forall A G, H \subset G -> (A :&: G) / H = A / H :&: G / H.
Proof. rewrite -{1}ker_coset. exact: morphimIG. Qed.

Lemma quotientD : forall A B, A / H :\: B / H \subset (A :\: B) / H.
Proof. exact: morphimD. Qed. 

Lemma quotientDG : forall A G, H \subset G -> (A :\: G) / H = A / H :\: G / H.
Proof. rewrite -{1}ker_coset; exact: morphimDG. Qed.

Lemma quotientK : forall A, A \subset 'N(H) -> coset H @*^-1 (A / H) = H * A.
Proof. rewrite -{8}ker_coset; exact: morphimK. Qed.

Lemma quotientGK : forall G, H <| G -> coset H @*^-1 (G / H) = G.
Proof. move=> G; case/andP; rewrite -{1}ker_coset; exact: morphimGK. Qed.

Lemma cosetpre_set1 : forall x,
  x \in 'N(H) -> coset H @*^-1 [set coset H x] = H :* x.
Proof. by rewrite -{9}ker_coset; exact: morphpre_set1. Qed.

Lemma cosetpre_set1_coset : forall xb, coset H @*^-1 [set xb] = xb.
Proof.
by move=> xb; case: (cosetP xb) => x Nx ->; rewrite cosetpre_set1 ?val_coset.
Qed.

Lemma cosetpreK : forall C, coset H @*^-1 C / H = C.
Proof. by move=> C; rewrite /quotient morphpreK ?coset_im. Qed.

(* Variant of morhphim_ker*)
Lemma trivial_quotient : H / H = 1.
Proof. by rewrite -{3}ker_coset /quotient morphim_ker. Qed.

Lemma sub_cosetpre : forall M, H \subset coset H @*^-1 M.
Proof. rewrite -{3}ker_coset; exact: ker_sub_pre. Qed.

Lemma normal_cosetpre : forall M, H <| coset H @*^-1 M.
Proof. rewrite -{3}ker_coset; exact: ker_normal_pre. Qed.

Lemma cosetpreSK : forall C D,
  (coset H @*^-1 C \subset coset H @*^-1 D) = (C \subset D).
Proof. by move=> C D; rewrite morphpreSK ?coset_im. Qed.

Lemma sub_quotient_pre : forall A C,
  A \subset 'N(H) -> (A / H \subset C) = (A \subset coset H @*^-1 C).
Proof. by move=> A C; exact: sub_morphim_pre. Qed.

Lemma sub_cosetpre_quo : forall C G,
  H <| G -> (coset H @*^-1 C \subset G) = (C \subset G / H).
Proof. by move=> C G nHG; rewrite -cosetpreSK quotientGK. Qed.

(* Variant of ker_trivg_morphim. *)
Lemma trivg_quotient : forall A,
  A \subset 'N(H) -> trivg (A / H) = (A \subset H).
Proof. by move=> A nHA; rewrite -{3}ker_coset ker_trivg_morphim nHA. Qed.

Lemma quotientSK : forall A B,
  A \subset 'N(H) -> (A / H \subset B / H) = (A \subset H * B).
Proof. by move=> A B nHA; rewrite morphimSK ?ker_coset. Qed.

Lemma quotientSGK : forall A G,
  A \subset 'N(H) -> H \subset G -> (A / H \subset G / H) = (A \subset G).
Proof. rewrite -{2}ker_coset; exact: morphimSGK. Qed.

Lemma quotient_injG :
  {in [pred G : {group gT} | H <| G] &, injective (fun G => G / H)}.
Proof. rewrite /normal -{1}ker_coset; exact: morphim_injG. Qed.

Lemma quotient_inj : forall G1 G2,
   H <| G1 -> H <| G2 -> G1 / H = G2 / H -> G1 :=: G2.
Proof. rewrite /normal -{1 3}ker_coset; exact: morphim_inj. Qed.

Lemma quotient_gen : forall A, A \subset 'N(H) -> <<A>> / H = <<A / H>>.
Proof. exact: morphim_gen. Qed.

Lemma cosetpre_gen : forall C,
  1 \in C -> coset H @*^-1 <<C>> = <<coset H @*^-1 C>>.
Proof. by move=> C C1; rewrite morphpre_gen ?coset_im. Qed.

Lemma quotientR : forall A B,
  A \subset 'N(H) -> B \subset 'N(H) -> [~: A, B] / H = [~: A / H, B / H].
Proof. exact: morphimR. Qed.

Lemma quotient_norm : forall A, 'N(A) / H \subset 'N(A / H).
Proof. exact: morphim_norm. Qed.

Lemma quotient_norms : forall A B, A \subset 'N(B) -> A / H \subset 'N(B / H).
Proof. exact: morphim_norms. Qed.

Lemma quotient_subnorm : forall A B, 'N_A(B) / H \subset 'N_(A / H)(B / H).
Proof. exact: morphim_subnorm. Qed.

Lemma quotient_normal : forall A B, A <| B -> A / H <| B / H.
Proof. exact: morphim_normal. Qed.

Lemma quotient_cent1 : forall x, 'C[x] / H \subset 'C[coset H x].
Proof.
move=> x; case Nx: (x \in 'N(H)); first exact: morphim_cent1.
by rewrite coset_default // cent11T subsetT.
Qed.

Lemma quotient_cent1s : forall A x,
  A \subset 'C[x] -> A / H \subset 'C[coset H x].
Proof.
move=> A x sAC; exact: subset_trans (quotientS sAC) (quotient_cent1 x).
Qed.

Lemma quotient_subcent1 : forall A x,
  'C_A[x] / H \subset 'C_(A / H)[coset H x].
Proof.
move=> A x; exact: subset_trans (quotientI _ _) (setIS _ (quotient_cent1 x)).
Qed.

Lemma quotient_cent : forall A, 'C(A) / H \subset 'C(A / H).
Proof. exact: morphim_cent. Qed.

Lemma quotient_cents : forall A B,
  A \subset 'C(B) -> A / H \subset 'C(B / H).
Proof. exact: morphim_cents. Qed.

Lemma quotient_subcent : forall A B, 'C_A(B) / H \subset 'C_(A / H)(B / H).
Proof. exact: morphim_subcent. Qed.

Lemma cosetpre_normal : forall C D,
  (coset H @*^-1 C <| coset H @*^-1 D) = (C <| D).
Proof. by move=> C D; rewrite morphpre_normal ?coset_im. Qed.

Lemma quotient_normG : forall G, H <| G -> 'N(G) / H = 'N(G / H).
Proof.
move=> G; case/andP=> sHG nHG.
by rewrite [_ / _]morphim_normG ?ker_coset // coset_imT setTI.
Qed.

Lemma quotient_subnormG : forall A G,
   H <| G -> 'N_A(G) / H = 'N_(A / H)(G / H).
Proof.
by move=> A G; case/andP=> sHG nHG; rewrite -morphim_subnormG ?ker_coset.
Qed.

Lemma cosetpre_cent1 : forall x,
  'C_('N(H))[x] \subset coset H @*^-1 'C[coset H x].
Proof.
move=> x; case Nx: (x \in 'N(H)); first by rewrite morphpre_cent1.
by rewrite coset_default // cent11T morphpreT subsetIl.
Qed.

Lemma cosetpre_cent1s : forall C x,
  coset H @*^-1 C \subset 'C[x] -> C \subset 'C[coset H x].
Proof.
move=> C x sC; rewrite -cosetpreSK; apply: subset_trans (cosetpre_cent1 x).
by rewrite subsetI subsetIl.
Qed.

Lemma cosetpre_subcent1 : forall C x,
  'C_(coset H @*^-1 C)[x] \subset coset H @*^-1 'C_C[coset H x].
Proof.
move=> C x; rewrite -morphpreIdom -setIA setICA morphpreI setIS //.
exact: cosetpre_cent1.
Qed.

Lemma cosetpre_cent : forall A, 'C_('N(H))(A) \subset coset H @*^-1 'C(A / H).
Proof. exact: morphpre_cent. Qed.

Lemma cosetpre_cents : forall A C,
  coset H @*^-1 C \subset 'C(A) -> C \subset 'C(A / H).
Proof. by move=> A C; apply: morphpre_cents; rewrite ?coset_im. Qed.

Lemma cosetpre_subcent : forall C A,
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

Lemma quotient_mulg : forall A, A * H / H = A / H.
Proof.
move=> A; rewrite [_ /_]morphimMr ?normG //= -!quotientE.
by rewrite trivial_quotient mulg1.
Qed.

Lemma quotient_mulgr : forall A, H * A / H = A / H.
Proof.
move=> A; rewrite [_ /_]morphimMl ?normG //= -!quotientE.
by rewrite trivial_quotient mul1g.
Qed.

Lemma quotient_mulgen : forall G, G \subset 'N(H) -> G <*> H / H = G / H.
Proof.
move=> G nHG; rewrite -genM_mulgen quotientE morphim_gen -?quotientE.
  by rewrite quotient_mulg genGid.
by rewrite -(mulSGid nHG) mulgS ?normG.
Qed.

Section Injective.

Variables (G : {group gT}).
Hypotheses (nHG : G \subset 'N(H)) (trGH : trivg (G :&: H)).

Lemma quotient_isom : isom G (G / H) (restrm nHG (coset H)).
Proof. by apply/isomP; rewrite ker_restrm ker_coset morphim_restrm setIid. Qed.

Lemma quotient_isog : isog G (G / H).
Proof. exact: isom_isog quotient_isom. Qed.

End Injective.

End CosetOfGroupTheory.

Notation "A / H" := (quotient_group A H) : subgroup_scope.

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

Variable (gT : finGroupType) (G H : {group gT}) (f : {morphism G >-> gT}).

Implicit Types A : {set gT}.
Implicit Types B : {set (coset_groupType H)}.
Hypotheses (nHG : H <| G) (nGf : f @* G = G) (nHf : f @* H = H).

Notation fH := (coset H \o f).

Lemma quotm_restr_proof : G \subset 'dom fH.
Proof. by rewrite -sub_morphim_pre // nGf; case/andP: nHG. Qed.

Notation fH_G := (restrm quotm_restr_proof fH).

Lemma quotm_fact_proof1 : G \subset 'N(H).
Proof. by case/andP: nHG. Qed.

Lemma quotm_fact_proof2 : 'ker (coset H) \subset 'ker fH_G.
Proof.
case/andP: nHG => sHG _; rewrite ker_restrm ker_comp ker_coset subsetI.
by rewrite -sub_morphim_pre sHG ?nHf /=.
Qed.

Definition quotm := factm quotm_fact_proof1 quotm_fact_proof2.
Canonical Structure quotm_morphism := Eval hnf in [morphism of quotm].

Lemma morphim_quotm : forall A, quotm @* (A / H) = f @* A / H.
Proof.
case/andP: nHG => sHG nHG' A.
by rewrite morphim_factm morphim_restrm morphim_comp morphimIdom.
Qed.

Lemma cosetpre_quotm : forall A,
  quotm @*^-1 (A / H) = f @*^-1 A / H.
Proof.
case/andP: nHG => sHG nHG' A; rewrite morphpre_factm morphpre_restrm.
rewrite morphpre_comp morphpreIdom quotientE -(morphimIdom _ A) /= -quotientE.
rewrite morphimK ?subsetIl // ker_coset morphpreMl ?nGf // -{3}nHf morphimK //.
rewrite -morphpreIim setIA -(morphpreIim _ A) !nGf (setIidPl nHG').
rewrite [_ * H]normC; last by apply: subset_trans nHG'; rewrite subsetIl.
by rewrite -mulgA quotient_mulgr -morphpreMl (mul1g, sub1G).
Qed.

Lemma ker_quotm : 'ker quotm = 'ker f / H.
Proof. by rewrite -cosetpre_quotm /quotient morphim1. Qed.

Lemma injm_quotm : 'injm f -> 'injm quotm.
Proof. by move/trivgP=> /= kf1; rewrite ker_quotm kf1 quotientE morphim1. Qed.

End QuotientMorphism.

Section FirstIsomorphism.

Variables aT rT : finGroupType.

Lemma first_isom : forall (G : {group aT}) (f : {morphism G >-> rT}),
  {g : {morphism G / 'ker f >-> rT} | 'injm g &
      forall A : {set aT}, g @* (A / 'ker f) = f @* A}.
Proof.
move=> G f; have nkG := ker_norm f.
have skk: 'ker (coset ('ker f)) \subset 'ker f by rewrite ker_coset.
exists (factm_morphism nkG skk) => /=; last exact: morphim_factm.
by rewrite ker_factm -quotientE trivial_quotient.
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
Proof. rewrite setIC -{1 3}(ker_coset K); exact: first_isog_loc. Qed.

Lemma weak_second_isog : H / (K :&: H) \isog H * K / K.
Proof. rewrite quotient_mulg; exact: second_isog. Qed.

End SecondIsomorphism.

Section ThirdIsomorphism.

Variables (gT : finGroupType) (G H K : {group gT}).

Hypothesis sHK : H \subset K.
Hypothesis snHG : H <| G.
Hypothesis snKG : K <| G.

Theorem third_isom : {f : {morphism (G / H) / (K / H) >-> coset_of K} | 'injm f
   & forall A : {set gT}, A \subset G -> f @* (A / H / (K / H)) = A / K}.
Proof.
case/andP: snKG => sKG nKG; case/andP: snHG => sHG nHG.
have sHker: 'ker (coset H) \subset 'ker (restrm nKG (coset K)).
  by rewrite ker_restrm !ker_coset subsetI sHG.
have:= first_isom_loc (factm_morphism nHG sHker) (subset_refl _) => /=.
rewrite ker_factm_loc ker_restrm ker_coset !(setIidPr sKG) /= -!quotientE.
case=> f injf im_f; exists f => // A sAG; rewrite im_f ?morphimS //.
by rewrite morphim_factm morphim_restrm (setIidPr sAG).
Qed.

Theorem third_isog : (G / H / (K / H)) \isog (G / K).
Proof.
by case: third_isom => f inj_f im_f; apply/isogP; exists f; rewrite ?im_f.
Qed.

End ThirdIsomorphism.

Lemma char_from_quotient : forall (gT : finGroupType) (G H K : {group gT}),
  H <| K -> H \char G -> K / H \char G / H -> K \char G.
Proof.
move=> gT G H K; case/andP=> sHK nHK chHG; case/charP=> sKG chKG.
have nHG := char_normal chHG; case: (andP nHG) => sHG nHG'.
rewrite -(ker_coset H) in sHK; rewrite morphimSGK ?ker_coset // in sKG.
apply/charP; split=> // f injf Gf; apply/morphim_fixP => //.
have{chHG} Hf: f @* H = H by case/charP: chHG => _; apply.
rewrite -(morphimSGK _ sHK) -?quotientE; last first.
  by apply: subset_trans nHG'; rewrite -{3}Gf morphimS.
rewrite -(morphim_quotm nHG Gf Hf) {}chKG // ?injm_quotm //.
by rewrite morphim_quotm Gf.
Qed.

(* Counting lemmas for morphisms. *)

Section CardMorphism.

Variables (aT rT : finGroupType) (D : {group aT}) (f : {morphism D >-> rT}).
Implicit Types G H : {group aT}.
Implicit Types L M : {group rT}.

Lemma card_morphim : forall G, #|f @* G| = #|D :&: G : 'ker f|.
Proof.
move=> G; rewrite -morphimIdom -indexgI -card_quotient; last first.
  by rewrite normsI ?normG ?subIset ?ker_norm.
by apply: esym (isog_card _); rewrite first_isog_loc ?subsetIl.
Qed.

Lemma dvdn_morphim :  forall G, #|f @* G| %| #|G|.
Proof.
move=> G; rewrite card_morphim (dvdn_trans (dvdn_indexg _ _)) //.
by rewrite cardSg ?subsetIr.
Qed.

Lemma dvdn_morphim_index : forall G H,
  G :&: H \subset D -> #|f @* G : f @* H| %| #|G : H|.
Proof.
move=> G H dGH; apply: (@dvdn_trans #|f @* G : f @* (G :&: H)|).
  by rewrite -indexgI indexgS ?morphimI.
have: 0 < #|'ker_(D :&: G) f| * #|f @* (G :&: H)|.
  by rewrite ltn_0mul !ltn_0group.
move/dvdn_pmul2l <-; rewrite -mulnA LaGrange ?(morphimS, subsetIl) //.
rewrite 2!card_morphim LaGrangeI (setIidPr dGH).
have: 'ker_(G :&: H) f \subset 'ker_(D :&: G) f.
  by rewrite setSI // subsetI dGH subsetIl.
move/LaGrange <-; rewrite -!mulnA mulnCA dvdn_mull //= mulnA !LaGrangeI.
by rewrite cardSg ?subsetIr.
Qed.

Lemma card_morphpre : forall L,
  L \subset f @* D -> #|f @*^-1 L| = (#|'ker f| * #|L|)%N.
Proof.
move=> L; move/morphpreK=> defL; rewrite -{2}defL card_morphim morphpreIdom.
by rewrite LaGrange // morphpreS ?sub1G.
Qed.

Lemma index_morphpre : forall L M,
  L \subset f @* D -> #|f @*^-1 L : f @*^-1 M| = #|L : M|.
Proof.
move=> L M dL; rewrite -!divgI -morphpreI card_morphpre //.
have: L :&: M \subset f @* D by rewrite subIset ?dL.
by move/card_morphpre->; rewrite divn_pmul2l ?ltn_0group.
Qed.

End CardMorphism.


