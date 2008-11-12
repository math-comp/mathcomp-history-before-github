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

(* General functoriality *)

Definition resp (F : obmap): Prop :=
  forall gT hT (G:{group gT}) (phi:{morphism G >-> hT}),
    phi @* (F _ G) \subset F _ (phi @* G).

(* Functoriality on grp whose arrows are restricted to automorphisms *)

Definition aresp (F : obmap) : Prop :=
  forall gT (G:{group gT}) phi (HA:phi \in Aut G), 
        (autm_morphism HA) @* (F _ G) \subset F _ ((autm_morphism HA) @* G).

Lemma aresp_of_resp : forall (F:obmap), resp F -> aresp F.
Proof. by move=> F H gT G phi Ha; apply:H. Qed.

(* "Anti-monotonicity" *)

Definition decr (F : obmap) : Prop :=
  forall gT (H G : {group gT}), (H \subset G) -> (F _ G) :&: H \subset (F _ H).

End IdentitySubFunctorDefs.

Module BaseIdSubFunctor.

(* Those mappings only functorial w.r.t. automorphisms*)

Implicit Types gT: finGroupType.

Structure mixin (Fobj : obmap) : Type := Mixin { 
(*)  _ : forall gT (G : {group gT}), group_set (Fobj gT G);*)
  _ : forall gT (G: {group gT}), Fobj gT G \subset G;
  _ : aresp Fobj}.

Structure class : Type := Class { Fobj :> obmap ; 
   _ : mixin Fobj}.

Definition subset_of (Fobj : obmap) (MF : mixin Fobj) := 
  let: Mixin s _ := MF return
  forall gT (G: {group gT}), Fobj gT G \subset G in s.

Coercion mixin_of F := let: Class _ m := F return mixin F in m.

End BaseIdSubFunctor.

Notation bisFc := BaseIdSubFunctor.class.
Notation BisFc := BaseIdSubFunctor.Class.
Notation BisFMixin := BaseIdSubFunctor.Mixin.

Definition mkBaseisFc F Fsub Fresp := 
  BisFc (@BisFMixin F Fsub Fresp).

Notation "[ 'bisFc' 'of' F ]" :=
  (match [is F : _ -> _ <: bisFc] as s return {type of BisFc for s} -> _ with
    | BisFc _ m => fun k => k m end
  (@BisFc F)) (at level 0, only parsing) : form_scope.

Notation Local "''e_' s ( G )" := (s _ G)
  (at level 8,s at level 2, format "''e_' s ( G )") : group_scope.

Section BaseIdentitySubfunctorProps.

Variables gT hT:finGroupType.
Variable sF: bisFc.
Implicit Types G H : {group gT}.

(*
Canonical Structure bisfc_group G := 
  Group (bisfc_groupset G).
*)

Lemma bisfc_clos : forall (fT:finGroupType) (H:{group fT}),
  'e_sF(H) \subset H.
Proof. by case sF=> F; case. Qed.

Lemma bisfc_aresp : aresp sF.
Proof. by case sF=> Fobj; case. Qed.

Lemma bisfc_norm : forall G, G \subset 'N('e_sF(G)).
Proof.
move=> G; apply/subsetP=> x Gx; rewrite inE -{2}(conjGid Gx) -{2}(setIid G).
rewrite -(setIidPr (bisfc_clos G)) -!morphim_conj.
pose conjgx := (autm (Aut_aut (@injm_conj _ G _) 
               (norm_conj_dom (valP (insigd (group1 _) x))))).
rewrite -!(@eq_morphim _ _ _ [morphism of conjgx] (conjgm_morphism _ x)) =>/=;
rewrite ?bisfc_clos ?bisfc_aresp // => y; apply: (conj_autE Gx).
Qed.

Lemma bisfc_normal : forall G, 'e_sF(G) <| G.
Proof. by move=> G; apply/andP; rewrite bisfc_clos bisfc_norm. Qed.

Lemma bisfc_char : forall G, 'e_sF(G) \char G.
Proof.
move=> G; apply/andP; split => //; first by apply: bisfc_clos.
apply/forallP=> f; apply/implyP=> Af; rewrite -{2}(autm_dom Af).
rewrite  -(morphimEsub (autm_morphism Af)) ?bisfc_clos //.
by apply: bisfc_aresp.
Qed.

End BaseIdentitySubfunctorProps.

Module IdSubFunctor.

(* Mappings functorial w.r.t. (surjective) morphisms *)

(* Beware, since our commutativity property is defined on f @* G,
   i.e. implicitly restricts Grp to surjective morphisms, these do not
   necessarily yield completely characteristic groups (counterexample :
   center).*)

Implicit Types gT: finGroupType.

Structure class : Type := Class { 
  Fobj :> obmap ;
   _ : BaseIdSubFunctor.mixin Fobj;
   _ : resp Fobj}.

Coercion mixin_of F := let: Class _ m _ := F return 
  BaseIdSubFunctor.mixin F in m.

Lemma isfc_resp (sF: class): resp sF.
Proof. by case => F FM. Qed.

End IdSubFunctor.

Notation isFc := IdSubFunctor.class.
Notation IsFc := IdSubFunctor.Class.

Definition mkIsFc F Fsub (Fresp:resp F) := 
  IsFc (BisFMixin Fsub (aresp_of_resp Fresp)) Fresp.

Notation "[ 'isFc' 'of' F ]" :=
  (match [is F : _ -> _ <: bisFc] as s return {type of BisFc for s} -> _ with
    | IsFc _ m r => fun k => k m r end
  (@IsFc F)) (at level 0, only parsing) : form_scope.

Coercion isFc_bisFc (sF : isFc) := 
  BisFc (BisFMixin (BaseIdSubFunctor.subset_of sF)
  (aresp_of_resp (IdSubFunctor.isfc_resp sF))).

Canonical Structure isFc_bisFc.

Section IdentitySubFunctorProps.

Implicit Types gT hT:finGroupType.
Variable sF: isFc.

Lemma isfc_resp : resp sF.
Proof. exact:IdSubFunctor.isfc_resp. Qed.

Lemma morphim_sfunctor : forall gT hT (G D : {group gT})
  (f : {morphism D >-> hT}),
  G \subset D -> f @* ('e_sF(G)) \subset 'e_sF(f @* G).
Proof.
move=> gT hT G D f sGD; rewrite -(setIidPr (bisfc_clos sF G)).
by rewrite  -{3}(setIid G) -!(morphim_restrm sGD) isfc_resp.
Qed.

Lemma injm_sfunctor : forall gT hT (G D : {group gT}) (f : {morphism D >-> hT}),
  'injm f -> G \subset D -> f @* ('e_sF(G)) = 'e_sF(f @* G).
Proof.
move=> gT hT G D f injf sGD; apply/eqP; rewrite eqEsubset morphim_sfunctor //=.
rewrite -{2}(morphim_invm injf sGD) -[f @* sF _ _](morphpre_invm injf).
have sFtr := subset_trans (bisfc_clos _ _).
by rewrite -sub_morphim_pre (morphim_sfunctor, sFtr) ?morphimS.
Qed.

Lemma isom_sfunctor : forall gT hT (D G : {group gT}) (R : {group hT}) 
                                   (f : {morphism D >-> hT}),
  G \subset D -> isom G R f -> isom ('e_sF(G)) ('e_sF(R)) f.
Proof.
move=> gT rT D G R f; case/(restrmP f)=> g [_ _ ->]; case/isomP=> injf <-.
rewrite /isom -(injm_sfunctor injf) // -morphimEsub ?morphimDG ?morphim1 //. 
by rewrite subDset subsetU // bisfc_clos orbT.
Qed.

Lemma isog_sfunctor : forall gT hT (D : {group gT}) (R : {group hT}),
  D \isog R -> 'e_sF(D) \isog 'e_sF(R).
Proof.
move=> gT rT D R; case/isogP=> f *.
apply: (isom_isog f) => //; first by apply: bisfc_clos.
apply: isom_sfunctor => //; exact/isomP.
Qed.

End IdentitySubFunctorProps.

Module DecrIdSubFunctor.

(* Mappings functorial w.r.t. (surjective) morphisms,
   well-behaved w.r.t. modulo application *)

Implicit Types gT: finGroupType.

Structure class : Type := Class { 
  Fobj :> obmap;
   _ : BaseIdSubFunctor.mixin Fobj;
   _ : resp Fobj;
   _ : decr Fobj}.

Coercion mixin_of F := let: Class _ m _ _ := F return 
  BaseIdSubFunctor.mixin F in m.

Lemma disfc_resp (sF: class): resp sF.
Proof. by case => F. Qed.

Lemma disfc_decr (sF : class): decr sF.
Proof. by case => F. Qed.

End DecrIdSubFunctor.

Notation disFc := DecrIdSubFunctor.class.
Notation DisFc := DecrIdSubFunctor.Class.

Definition mkdIsFc F Fsub (Fresp:resp F) (Fdecr : decr F) := 
  DisFc (BisFMixin Fsub (aresp_of_resp Fresp)) Fresp Fdecr.

Notation "[ 'disFc' 'of' F ]" :=
  (match [is F : _ -> _ <: bisFc] as s return {type of BisFc for s} -> _ with
    | DisFc _ m r d => fun k => k m r d end
  (@DisFc F)) (at level 0, only parsing) : form_scope.

Coercion disFc_isFc (sF : disFc) := 
  IsFc sF (DecrIdSubFunctor.disfc_resp sF).

Canonical Structure disFc_isFc.

Section DecreasingIdentitySubFunctorProps.

End DecreasingIdentitySubFunctorProps.

Section IdentitySubfunctorsExamples.

Implicit Types gT:finGroupType.

Lemma id_resp : resp (fun _ S => S).
Proof. by []. Qed.

Canonical Structure id_subfunc :=
  mkIsFc (fun gT G => subxx _)
         id_resp.

Lemma triv_resp : resp (fun _ S => 1).
Proof. by move=> gT hT H f; rewrite morphim1. Qed.

Canonical Structure triv_subfunc :=
  @mkIsFc (fun _ S => 1) sub1G
        triv_resp.

Require Import center.

Lemma center_resp : resp (fun _ S => 'Z(S)).
Proof.
move=> gT hT H phi /=; apply:(subset_trans (morphimI _ _ _ )).
rewrite subsetI subsetIl /=; apply:(subset_trans (subsetIr (phi @* H) _) ).
exact:morphim_cent.
Qed.

Canonical Structure center_id_subfunc :=
  mkIsFc (fun gT G => @center_sub gT G)
         center_resp.

Require Import maximal.

Lemma Frattini_resp : resp (Frattini).
Proof. exact: gfunc_Phi. Qed.

Canonical Structure Frattini_subfunc :=
  mkIsFc (fun gT => @Phi_sub gT)
         Frattini_resp.

Require Import nilpotent.

Lemma der_clos : forall n gT (G:{group gT}), G^`(n) \subset G.
Proof.
elim; first by move=> gT G; rewrite derg0.
by move=> n0 IH gT G; rewrite dergSn (comm_subG (IH _ _) (IH _ _)).
Qed.

Lemma der_resp : forall n, 
  resp (fun gT G => derived_at G n).
Proof.
elim => [|n IH] gT hT H phi; first by rewrite derg0.
rewrite !dergSn (morphimR _ (der_clos _ _) (der_clos _ _)).
by rewrite commgSS ?IH.
Qed.

Canonical Structure der_id_subfunctor (n:nat) :=
  mkIsFc (der_clos n)
         (der_resp n).

Lemma lcn_resp : forall n,
  resp (fun gT G => 'L_n(G)).
Proof.
elim=> [|n IH] gT hT H phi; first by rewrite !lcn0.
by rewrite !lcnSn morphimR ?lcn_sub0 // commSg ?IH.
Qed.

Canonical Structure lcn_id_subfunctor (n:nat) :=
  mkIsFc (fun gT G => (lcn_sub0 G n))
         (lcn_resp n).

Require Import pgroups.

Lemma Ohm_sub : forall i gT (G:{group gT}), 'Ohm_i(G) \subset G.
Proof. move=> gT i; exact: Ohm_sub. Qed.

Lemma Ohm_resp : forall i,
  resp (fun gT S => 'Ohm_i(S)).
Proof. move=> i G f; exact: gfunc_Ohm. Qed.

Canonical Structure Ohm_id_subfunctor (i:nat) :=
  mkIsFc (Ohm_sub i)
         (Ohm_resp i).

Lemma Mho_sub : forall i gT (G:{group gT}), 'Mho^i(G) \subset G.
Proof. move=> i; exact: Mho_sub. Qed.

Lemma Mho_resp : forall i,
  resp (fun gT S => 'Mho^i(S)).
Proof. move=> i G f; exact: gfunc_Mho. Qed.

Canonical Structure Mho_id_subfunctor (i:nat) :=
  mkIsFc (Mho_sub i)
         (Mho_resp i).

End IdentitySubfunctorsExamples.

Unset Implicit Arguments.
