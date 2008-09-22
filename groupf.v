(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import ssrfun.
Require Import eqtype.
Require Import ssrnat.
Require Import fintype.
Require Import finset.
Require Import groups.
Require Import group_perm.
Require Import normal.
Require Import morphisms.
Require Import automorphism.
Require Import bigops.

Import GroupScope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section IdentitySubFunctorDefs.

Implicit Types gT hT : finGroupType.

(* An object mapping on sets *)

Definition obmap : Type := forall gT, {set gT} -> {set gT}.

Identity Coercion fun_of_obmap : obmap >-> Funclass.

(* A filter on morphisms *)

Definition filter gT hT : Type := forall (G:{group gT}),
  {morphism G >-> hT} -> Prop.

(* Subcommutation of that object mapping with morphisms respecting the filter *)

Definition resp (F : obmap) gT hT (P : filter gT hT): Prop :=
  forall (G:{group gT}) (phi:{morphism G >-> hT}),
    (P G phi) -> phi @* (F _ G) \subset F _ (phi @* G).

(* Some filter examples *)

Variable gT:finGroupType.

Implicit Types H:{group gT}.

Definition is_int_aut H (phi : {morphism H >-> gT}) :=
  exists y, y \in 'N(H) /\ (conjgm H y) =1 phi.

Definition is_aut H (phi : {morphism H >-> gT}) :=
  'injm phi && (phi @* H == H).

Definition is_surj_end H (phi : {morphism H >-> gT}) :=
  phi @* H \subset H.

Definition is_inj hT H (phi : {morphism H >-> hT}) :=
  'injm phi.

Definition is_morphism hT H (phi: {morphism H >-> hT}) :=
  True.

End IdentitySubFunctorDefs.

Module IdSubFunctor.

Section IdentitySubFunctorStructs.

Variable gT:finGroupType.
Variable hT : finGroupType.

Implicit Types F:obmap.
Implicit Types P:filter gT hT.

(* Conditions for an object mapping on Grp, restricted to arrows verifying
   a given filter, to define a subfunctor of the identity*)

Structure subfuncclass P : Type := SubFuncClass { 
  Fobj :> obmap;
  _ : forall (G : {group gT}), group_set (Fobj gT G);
  _ : forall (G: {group gT}), Fobj gT G \subset G;
  _ : resp Fobj P}.

End IdentitySubFunctorStructs.

End IdSubFunctor.

Notation isFc := IdSubFunctor.subfuncclass.
Notation isFcClass := IdSubFunctor.SubFuncClass.

Notation Local "''e_' s ( G )" := (s _ G)
  (at level 8,s at level 2, format "''e_' s ( G )") : group_scope.

Section IdentitySubfunctorProps.

Variables gT hT:finGroupType.
Variable P : filter gT hT.
Implicit Types sF: isFc P.

Lemma subfuncclass_groupset : forall sF (G:{group gT}), group_set ('e_sF(G)).
Proof. by case. Qed.

Canonical Structure subfuncclass_group sF G := 
  Group (subfuncclass_groupset sF G).

Lemma subfuncclass_clos : forall sF (G:{group gT}),
  'e_sF(G) \subset G.
Proof. by case. Qed.

Lemma subfuncclass_resp : forall sF, resp (sF) P.
Proof. by case. Qed.

Lemma filterW : forall (Q : filter gT hT) sF,
  (forall H f, Q H f ->  P f) ->
  resp (sF) Q.
Proof.
move=> Q sF Hint H phi HQ.
by apply (subfuncclass_resp sF (Hint _ _ HQ)).
Qed.

End IdentitySubfunctorProps.

Section IdentitySubfunctorEndo.

Variables gT hT:finGroupType.
Variable P : filter gT gT.
Implicit Types sF: isFc P.

Implicit Types H:{group gT}.

(* For interior automorphisms, subfunctors of Id yield normal groups*)

Lemma resp_normal : forall sF, 
  (forall H (phi:{morphism H >-> gT}), is_int_aut phi -> P phi) ->
  forall G : {group gT}, ('e_sF(G)) <| G.
Proof.
move=> sF H G; apply/normalP; split; first exact: (subfuncclass_clos sF G).
apply/normsP; apply/subsetP=> x; move/(subsetP (normG _)); move/normP=>Heq.
rewrite inE.
have Hint : (is_int_aut [morphism of conjgm G x]).
  by exists x=>/=; split; rewrite ?inE ?Heq.
move: ((filterW sF H) _ _ Hint)=> /=; rewrite !morphim_conj setIid.
by move/setIidPr : (subfuncclass_clos sF G) ->; rewrite Heq => ->.
Qed.

(* For automorphisms, subfunctors of Id yield characteristic groups *)

Lemma resp_charac : forall sF,
  (forall H (phi:{morphism H >-> gT}), is_aut phi -> P phi) ->
  forall G : {group gT}, ('e_sF(G)) \char G.
Proof.
move=> sF H G; apply/charP; rewrite /= (subfuncclass_clos sF G).
split=> // f Hinj Heq; apply/(morphim_fixP Hinj _ (subfuncclass_clos sF G)).
by move/eqP : (Heq); move/(conj Hinj); move/andP; move/(filterW sF H);rewrite Heq.
Qed.

(* For endomorphisms, they yield strictly characteristic groups.
   -> do we need that notion ?*)

End IdentitySubfunctorEndo.

Section IdentitySubfunctorSub.

(* TO ENHANCE : This is just for fun & pretty inusable because of the
   uniform inheritance restriction on isFc.

   It would be really nice, though, to have a way to render a graph of
   implications between filters structurally, without having to define a
   dozen specialized structures for bijective, injective, etc
   [endo-|hetero-]morphisms.  *)

Variable gT:finGroupType.

Variables Q Q':filter gT gT.

Hypothesis Hpq : forall H f, @Q H f -> @Q' H f.

Variable sF: isFc Q'.

Definition superisfc :=
  @isFcClass gT _ Q _
    (subfuncclass_groupset sF)
    (subfuncclass_clos sF)
    (fun H f Hq => ((subfuncclass_resp sF) _ _ (@Hpq _ f Hq))).

End IdentitySubfunctorSub.

Section IdentitySubfunctorSup.

Variable gT: finGroupType.

Implicit Types H: {group gT}.

Lemma int_aut_is_aut : forall H (f:{morphism H >-> gT}),
  is_int_aut f -> is_aut f.
Proof.
move=> H f [x [Hnorm Heq]]; suff: (isom H H f).
by move/isomP=> [Hinj]; move/eqP; rewrite /is_aut Hinj=> ->.
rewrite /isom -(eq_imset H^# Heq); apply/isomP; rewrite injm_conj; split=> //.
by apply:norm_conj_dom.
Qed.

Lemma aut_is_surj_end : forall H (f:{morphism H >-> gT}),
  is_aut f -> is_surj_end f.
Proof. by move=> H f; move/andP=>[Hinj]; rewrite eqset_sub; case/andP. Qed.

Lemma aut_is_inj : forall H (f:{morphism H >-> gT}),
  is_aut f -> is_inj f.
Proof. by move=> H f; move/andP => [Hinj _]. Qed.

End IdentitySubfunctorSup.

Section IdentitySubfunctorsExamples.

Variable gT:finGroupType.

Lemma id_resp : resp (fun _ S => S) (@is_morphism gT gT).
Proof. by []. Qed.

Canonical Structure id_subfunc :=
  isFcClass (fun G => groupP G%G)
            (fun G => subset_refl _)
            id_resp.

Lemma triv_resp : resp (fun _ S => 1) (@is_morphism gT gT).
Proof. by move=> H f _ ; rewrite morphim1. Qed.

Canonical Structure triv_subfunc :=
  @isFcClass _ _ _ (fun _ S => 1)
            (fun G => groupP 1%G)
            (@sub1G gT)
            triv_resp.

Require Import center.

Lemma center_resp : resp (fun _ S => 'Z(S)) (@is_surj_end gT).
Proof.
move=> H phi /= Heq; apply:(subset_trans (morphimI _ _ _ )).
rewrite subsetI subsetIl /=; apply:(subset_trans (subsetIr (phi @* H) _) ).
exact:morphim_cent.
Qed.

Canonical Structure center_id_subfunc :=
  isFcClass (fun G => groupP 'Z(G)%G)
            (fun G => @center_sub gT G)
            (center_resp).

Require Import maximal.

Lemma Frattini_resp : resp (Frattini) (@is_inj gT gT).
Proof.
move=> H phi Hinj; apply/bigcap_inP=> i Hi.
rewrite sub_morphim_pre; last by apply:Phi_sub.
apply:bigcap_inf; move/subsetP: (@dom_ker _ _ H phi); move/morphimGK.
move/(_ (subset_refl _)) => Heq; rewrite -{2}Heq /= -2!(morphim_invmE Hinj).
by apply:maximal_morphim; first by apply subset_refl.
Qed.

Canonical Structure Frattini_subfunc :=
  isFcClass (fun G => groupP 'Phi(G)%G)
            (@Phi_sub gT)
            (Frattini_resp).

Require Import nilpotent.

Lemma der_clos : forall n (G:{group gT}), G^`(n) \subset G.
Proof.
elim; first by move=> G; rewrite derg0.
by move=> n0 IH G; rewrite dergSn (comm_subG (IH _) (IH _)).
Qed.

Lemma der_resp : forall n, 
  resp (fun gT G => derived_at G n) (@is_morphism gT gT).
Proof.
elim => [|n IH] H phi _; first by rewrite derg0.
rewrite !dergSn (morphimR _ (der_clos _ _) (der_clos _ _)).
by rewrite commgSS ?IH.
Qed.

Canonical Structure der_id_subfunctor (n:nat) :=
  isFcClass (fun (G:{group gT}) => der_group_set G n)
            (der_clos n)
            (der_resp n).

Require Import pgroups.

Implicit Types G:{group gT}.

Lemma Ohm_sub : forall i G, 'Ohm_i(G) \subset G.
Proof. move=> i; exact: Ohm_sub. Qed.

Lemma Ohm_resp : forall i,
  resp (fun gT S => 'Ohm_i(S)) (@is_aut gT).
Proof. move=> i G f _; exact: morphim_Ohm. Qed.

Canonical Structure Ohm_id_subfunctor (i:nat) :=
  @isFcClass _ _ _ (fun _ S => 'Ohm_i(S))
            (fun G => groupP 'Ohm_i(G)%G)
            (Ohm_sub i)
            (Ohm_resp i).

Lemma Mho_sub : forall i G, 'Mho^i(G) \subset G.
Proof. move=> i; exact: Mho_sub. Qed.

Lemma Mho_resp : forall i,
  resp (fun gT S => 'Mho^i(S)) (@is_aut gT).
Proof. move=> i G f _; exact: morphim_Mho. Qed.

Canonical Structure Mho_id_subfunctor (i:nat) :=
  @isFcClass _ _ _ (fun _ S => 'Mho^i(S))
            (fun G => groupP 'Mho^i(G)%G)
            (Mho_sub i)
            (Mho_resp i).

End IdentitySubfunctorsExamples.

Unset Implicit Arguments.
