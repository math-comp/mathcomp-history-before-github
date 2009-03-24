(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import ssrfun.
Require Import eqtype.
Require Import ssrnat.
Require Import fintype.
Require Import finset.
Require Import groups.
Require Import perm.
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

(* Functoriality on grp whose arrows are restricted to isomorphisms *)

Definition aresp (F : obmap) : Prop :=
  forall gT hT (G:{group gT}) (phi:{morphism G >-> hT}) (HA:'injm phi), 
    phi @* (F _ G) \subset F _ (phi @* G).

Lemma aresp_of_resp : forall (F:obmap), resp F -> aresp F.
Proof. by move=> F H gT hT G phi Ha; apply:H. Qed.

(* Hereditary w.r.t. inclusion *)

Definition hereditary (F : obmap) : Prop :=
  forall gT (H G : {group gT}), (H \subset G) -> (F _ G) :&: H \subset (F _ H).

(* Modulo Application *)

Definition appmod (F1 F2 : obmap) :=
  fun gT (G:{set gT}) => coset (F2 gT G) @*^-1 (F1 _ (G / (F2 gT G))).

Definition app (F1 F2 : obmap) :=
  fun gT (G:{set gT}) => F1 _ (F2 _ G).

(* Strong functoriality (wrt domains)*)

Definition dresp (F : obmap): Prop :=
  forall gT hT (G D:{group gT}) (phi:{morphism D >-> hT}),
    phi @* (F _ G) \subset F _ (phi @* G).

Lemma resp_of_dresp : forall (F:obmap), dresp F -> resp F.
Proof. by move=> F H gT hT G phi; apply:H. Qed.

Lemma hereditary_of_dresp (sF:obmap) : dresp sF -> hereditary sF.
Proof.
move=> sF Hresp gT H G sHG; move: (Hresp _ _ G _ (idm_morphism H)) =>/=.
rewrite -morphimIdom -[idm H @* G]morphimIdom !morphim_idm ?subsetIl //.
by rewrite (setIidPl sHG) setIC.
Qed.

(* Compatible w.r.t. inclusion *)

Definition compatible (F : obmap) : Prop :=
  forall gT (H G : {group gT}), H \subset G -> (F _ H) \subset (F _ G). 

End IdentitySubFunctorDefs.

Module BaseGFunctor.

(* Those mappings only functorial w.r.t. isomorphisms*)

Implicit Types gT: finGroupType.

Structure mixin_of (Fobj : obmap) : Type := Mixin { 
  (* group preservation *)
  _ : forall gT (G:{group gT}), group_set (Fobj _ G);
  (* submapping *)
  _ : forall gT (G: {group gT}), Fobj _ G \subset G;
  (* functoriality condition *)
  _ : aresp Fobj}.

Notation class_of := mixin_of (only parsing).

(* pack the functor plus its properties *)
Structure func : Type := Pack {F :> obmap; _ : class_of F; _ : obmap}.
(* destructor returning the parametric class of properties from the
   packaged functor *)
Definition class cF := let: Pack _ c _ := cF return class_of cF in c.
(* cps 'recombiner' taking a Type and its binary constructor k from
   functors and their classes, returning its application to components
   extracted from a packed functor cF *) 
Definition unpack K (k : forall F (c : class_of F), K F c) cF :=
  let: Pack F c _ := cF return K _ (class cF) in k _ c.
(* given a packaged functor, and the a packing function (intended to give
you the right obmap repetition at the tail of your record), produces the
glued constructor that reproduces the same functor class with that packing
function*)
Definition repack cF : _ -> obmap -> func :=
  let k (F:obmap) (c:class_of F) (p:class_of F -> obmap -> func) := p c in 
    unpack k cF.

Definition pack F c := @Pack F c F.

Definition subset_of (Fobj : obmap) (MF : class_of Fobj) := 
  let: Mixin _ s _ := MF return
  forall gT (G: {group gT}), Fobj gT G \subset G in s.

Definition group_of (Fobj : obmap) (MF : class_of Fobj) := 
  let: Mixin g _ _ := MF return
  forall gT (G: {group gT}), group_set (Fobj gT G) in g.

End BaseGFunctor.

Notation bgFunc := BaseGFunctor.func.
Notation BgFunc := BaseGFunctor.pack.
Notation BgMixin := BaseGFunctor.Mixin.
Notation "[ 'bgFunc' 'of' F 'for' cF ]" :=
    (@BaseGFunctor.repack cF (@BaseGFunctor.Pack F) F)
    (at level 0, only parsing) : form_scope.
Notation "[ 'bgFunc' 'of' F ]" :=
    (BaseGFunctor.repack (fun c => @BaseGFunctor.Pack F c) F)
  (at level 0, only parsing) : form_scope.

Notation Local "''e_' s ( G )" := (s _ G)
  (at level 8,s at level 2, format "''e_' s ( G )") : group_scope.

Lemma bgFunc_groupset : forall (sF:bgFunc) (gT:finGroupType) (G:{group gT}),
  group_set (sF gT G).
Proof. by move=> sF gT G; case sF=> F; case. Qed.

Canonical Structure bgFunc_group (sF:bgFunc) (gT:finGroupType) (G:{group gT}) :=
  (group (bgFunc_groupset sF G)).

Definition mkBasegFunc (F:obmap) Fgrp Fsub Fresp := 
  BgFunc (@BgMixin F Fgrp Fsub Fresp).

Section BaseIdentitySubFunctorProps.

Implicit Types gT hT:finGroupType.
Variable sF: bgFunc.

Lemma bgFunc_clos : forall (fT:finGroupType) (H:{group fT}),
  'e_sF(H) \subset H.
Proof. by case sF=> F; case. Qed.

Lemma bgFunc_aresp : aresp sF.
Proof. by case sF=> Fobj; case. Qed.

Lemma bgFunc_char : forall gT (G:{group gT}), 'e_sF(G) \char G.
Proof.
move=> gT G; apply/andP; split => //; first by apply: bgFunc_clos.
apply/forallP=> f; apply/implyP=> Af; rewrite -{2}(autm_dom Af).
by rewrite -(morphimEsub (autm_morphism Af)) ?bgFunc_clos ?bgFunc_aresp ?injm_autm.
Qed.

Lemma bgFunc_norm : forall gT (G:{group gT}), G \subset 'N('e_sF(G)).
Proof. by move=> *; rewrite char_norm ?bgFunc_char. Qed.

(* independent from the group preservation requirement*)
Lemma bgFunc_gen_norm : forall gT (G:{group gT}),
  <<'e_sF(G)>> \subset 'N('e_sF(G)).
Proof.
move=> gT G; apply/normsP=> x Hx; move/normsP: (bgFunc_norm G); apply.
by move: ((subsetP (genS (bgFunc_clos G))) _ Hx); rewrite genGid.
Qed.

Lemma bgFunc_normal : forall gT (G : {group gT}), 'e_sF(G) <| G.
Proof.  by move=> *; rewrite char_normal ?bgFunc_char. Qed.

Lemma bgFunc_asresp_sub :
  forall gT hT (H G:{group gT})  (f : {morphism G >-> hT}),
  'injm f -> H \subset G -> f @* ('e_sF(H)) \subset 'e_sF(f @* H).
Proof.
move=> gT hT H G f injf sHG; apply/eqP; rewrite -(setIidPr (bgFunc_clos H)).
by rewrite-{3}(setIid H) -!(morphim_restrm sHG) bgFunc_aresp ?injm_restrm //=.
Qed.

Lemma bgFunc_asresp : forall gT hT (H G : {group gT}) (f : {morphism G >-> hT}),
  'injm f -> H \subset G -> f @* ('e_sF(H)) = 'e_sF(f @* H).
Proof.
move=> gT hT H G f injf sHG; apply/eqP; rewrite eqEsubset bgFunc_asresp_sub //=.
rewrite -{2}(morphim_invm injf sHG) -[f @* sF _ _](morphpre_invm injf).
have sFtr := subset_trans (bgFunc_clos _).
by rewrite -sub_morphim_pre (bgFunc_asresp_sub, sFtr) ?morphimS ?injm_invm.
Qed.

Lemma bgFunc_nker_resp : forall gT hT (H G : {group gT})
  (f : {morphism G >-> hT}),
  'ker f = 1 -> H \subset G -> f @* ('e_sF(H)) = 'e_sF(f @* H).
Proof. by move=> gT hT H G f; move/trivgP =>/=; apply:bgFunc_asresp. Qed.

Lemma bgFunc_isom : forall gT hT (H G : {group gT}) (R : {group hT}) 
                                   (f : {morphism G >-> hT}),
  H \subset G -> isom H R f -> isom ('e_sF(H)) ('e_sF(R)) f.
Proof.
move=> gT rT H G R f; case/(restrmP f)=> g [_ _ ->]; case/isomP=> injf <-.
rewrite /isom -(bgFunc_asresp injf) // -morphimEsub ?morphimDG ?morphim1 //. 
by rewrite subDset subsetU // bgFunc_clos orbT.
Qed.

Lemma bgFunc_isog : forall gT hT (G : {group gT}) (R : {group hT}),
  G \isog R -> 'e_sF(G) \isog 'e_sF(R).
Proof.
move=> gT rT D R; case/isogP=> f *.
apply: (isom_isog f) => //; first by apply: bgFunc_clos.
apply: bgFunc_isom => //; exact/isomP.
Qed.

End BaseIdentitySubFunctorProps.

Module GFunctor.

(* Mappings functorial w.r.t. (surjective) morphisms *)

(* Beware, since our commutativity property is defined on f @* G,
   i.e. implicitly restricts Grp to surjective morphisms, these do not
   necessarily yield completely characteristic groups (counterexample :
   center).*)

Implicit Types gT: finGroupType.

Structure gFuncClass : Type := Pack { 
  FbgFunc :> bgFunc ;
   _ : resp FbgFunc}.

Definition repack FbgFunc :=
  let: Pack c r := FbgFunc return {type of Pack for FbgFunc} -> _ in
    fun k => k r.

Lemma gFunc_resp (sF: gFuncClass): resp sF.
Proof. by case => F FM. Qed.

End GFunctor.

Notation gFunc := GFunctor.gFuncClass.
Notation GFunc := GFunctor.Pack.

Notation "[ 'gFunc' 'of' F ]" :=
  (GFunctor.repack (fun m => @GFunc [bgFunc of F] m))
  (at level 0, only parsing) : form_scope.

Definition mkGFunc F Fgrp Fsub (Fresp:resp F) := 
  @GFunc (mkBasegFunc Fgrp Fsub (aresp_of_resp Fresp)) Fresp.

Section IdentitySubFunctorProps.

Implicit Types gT hT:finGroupType.
Variable sF: gFunc.

Lemma gFunc_resp : resp sF.
Proof. exact:GFunctor.gFunc_resp. Qed.

Lemma morphim_sFunctor : forall gT hT (G D : {group gT})
  (f : {morphism D >-> hT}),
  G \subset D -> f @* ('e_sF(G)) \subset 'e_sF(f @* G).
Proof.
move=> gT hT G D f sGD; rewrite -(setIidPr (bgFunc_clos sF G)).
by rewrite  -{3}(setIid G) -!(morphim_restrm sGD) gFunc_resp.
Qed.

Lemma injm_sFunctor : forall gT hT (G D : {group gT}) (f : {morphism D >-> hT}),
  'injm f -> G \subset D -> f @* ('e_sF(G)) = 'e_sF(f @* G).
Proof. exact: bgFunc_asresp. Qed.

Lemma isom_sFunctor : forall gT hT (D G : {group gT}) (R : {group hT}) 
                                   (f : {morphism D >-> hT}),
  G \subset D -> isom G R f -> isom ('e_sF(G)) ('e_sF(R)) f.
Proof. move=> gT hT D G; exact:bgFunc_isom. Qed.

Lemma isog_sFunctor : forall gT hT (D : {group gT}) (R : {group hT}),
  D \isog R -> 'e_sF(D) \isog 'e_sF(R).
Proof. exact: bgFunc_isog. Qed.

End IdentitySubFunctorProps.

Module HereditaryGFunctor.

(* Mappings Functorial w.r.t. (surjective) morphisms,
   well-behaved w.r.t. modulo application *)

Implicit Types gT: finGroupType.

Structure class : Type := Pack { 
  FgFunc :> gFunc;
   _ : hereditary FgFunc}.

Definition repack FgFunc :=
  let: Pack c r := FgFunc return {type of Pack for FgFunc} -> _ in
    fun k => k r.

Lemma hgFunc_resp (sF: class): resp sF.
Proof. by move=> sF; apply:gFunc_resp. Qed.

Lemma hgFunc_hereditary (sF : class): hereditary sF.
Proof. by case => F. Qed.

End HereditaryGFunctor.

Notation hgFunc := HereditaryGFunctor.class.
Notation HgFunc := HereditaryGFunctor.Pack.

Notation "[ 'hgFunc' 'of' F ]" :=
  (HereditaryGFunctor.repack (fun m => @HgFunc [gFunc of F] m))
  (at level 0, only parsing) : form_scope.

Definition mkhgFunc F Fgrp Fsub (Fresp:resp F) (Fdecr : hereditary F) := 
  @HgFunc (mkGFunc Fgrp Fsub Fresp) Fdecr.

Section HereditaryIdentitySubFunctorProps.

Implicit Types gT hT:finGroupType.

Section HereditaryIdBaseProps.

Variable sF: hgFunc.

Lemma hgFunc_resp : resp sF.
Proof. exact:GFunctor.gFunc_resp. Qed.

Lemma hgFunc_hereditary : hereditary sF.
Proof. exact:HereditaryGFunctor.hgFunc_hereditary. Qed.

Lemma hgFunc_imsetI : forall gT (G H:{group gT}),
  'e_sF(G) :&: H = 'e_sF (G) :&: 'e_sF (G :&: H).
Proof.
move=>gT G H; rewrite -{1}(setIidPr (bgFunc_clos sF G)) [G :&: _]setIC -setIA.
move/setIidPr: (hgFunc_hereditary (subsetIl G H)) <-.
by rewrite setIC -setIA (setIidPr (bgFunc_clos sF (G:&: H))).
Qed.

Lemma hgFunc_morphim : dresp sF.
Proof.
move=> gT hT G D f.
rewrite -morphimIdom -(setIidPl (bgFunc_clos sF G)) setIC -setIA [G :&: _]setIC.
apply: (subset_trans (morphimS f (hgFunc_hereditary (subsetIr D G)))).
apply:(subset_trans (morphim_sFunctor sF _ _ )); last by rewrite morphimIdom.
exact:subsetIl.
Qed.

Lemma hereditary_idem : forall (gT:finGroupType) (G:{group gT}),
  (app sF sF) _ G  = sF _ G.
Proof.
move=> gT G /=; apply/eqP; rewrite eqEsubset bgFunc_clos.
by move/hgFunc_hereditary : (bgFunc_clos sF G); rewrite setIid /=.
Qed.

End HereditaryIdBaseProps.

Section HereditaryIdentitySFComp.

Variable sF: hgFunc.
Variable sF2 : gFunc.

(* independent from the group preservation requirement *)
Lemma hgFunc_comp_clos : forall gT (G:{group gT}),
  (appmod sF sF2) gT G \subset G.
Proof.
move=> gT G; rewrite /appmod; have nFD := (bgFunc_norm sF2 G).
rewrite sub_morphpre_im ?(bgFunc_clos sF) //=.
  by rewrite ker_coset_prim subIset // gen_subG (bgFunc_clos sF2 G).
by apply: subset_trans (bgFunc_clos sF _) _; apply: morphimS.
Qed.

Lemma hgFunc_comp_quo : forall gT (G : {group gT}) (B : {set gT}),
  (coset B @*^-1  sF _ (G / B)) / B  = sF _ (G / B).
Proof.
move=> gT A B; apply: morphpreK; apply: subset_trans (bgFunc_clos sF _) _.
by rewrite /= /quotient -morphimIdom  morphimS ?subsetIl.
Qed.

Lemma hgFunc_comp_resp : resp (appmod sF sF2).
move=> gT rT G f; have nF := bgFunc_norm sF2.
have kF := ker_coset (Group (bgFunc_groupset sF2 _)); simpl in kF.
have sDF: G \subset 'dom (coset (sF2 _ G)) by rewrite ?nF.
have sDFf: G \subset 'dom (coset (sF2 _ (f @* G)) \o f).
  by rewrite -sub_morphim_pre ?subsetIl // nF.
pose K := 'ker (restrm sDFf (coset (sF2 _ (f @* G)) \o f)).
have sFK: 'ker (restrm sDF (coset (sF2 _ G))) \subset K.
  rewrite /K  !ker_restrm ker_comp /= subsetI subsetIl /=.
  by rewrite -sub_morphim_pre ?subsetIl // morphimIdom !kF ?morphim_sFunctor.
have sOF := bgFunc_clos sF (G / sF2 _ G); have sGG: G \subset G by [].
rewrite -sub_morphim_pre -?quotientE; last first.
  by apply: subset_trans (nF _ _); rewrite morphimS ?hgFunc_comp_clos.
suffices im_fact: forall H : {group gT}, sF2 _ G \subset H -> H \subset G ->
  factm sGG sFK @* (H / sF2 _ G) = f @* H / sF2 _ (f @* G).
- rewrite -2?im_fact ?hgFunc_comp_clos ?bgFunc_clos //.
  by rewrite hgFunc_comp_quo morphim_sFunctor /= ?morphim_restrm ?setIid //.
  by rewrite -{1}kF morphpreS ?sub1G.
move=> H sFH sHG; rewrite -(morphimIdom _ (H / _)) /= {2}morphim_restrm setIid.
rewrite -morphimIG ?kF // -(morphim_restrm sDF) morphim_factm morphim_restrm.
by rewrite morphim_comp -quotientE morphimIdom.
Qed.

End HereditaryIdentitySFComp.

Canonical Structure hgFunc_comp_bgFunc (sF:hgFunc) (sF2:gFunc) :=
  @mkBasegFunc (appmod sF sF2)
  (fun gT G => groupP [group of ((appmod sF sF2) _ G)])
  (hgFunc_comp_clos sF sF2)
  (aresp_of_resp (hgFunc_comp_resp sF sF2)).

Canonical Structure hgFunc_comp_gFunc (sF:hgFunc) (sF2:gFunc) :=
  @GFunc (hgFunc_comp_bgFunc sF sF2)
  (hgFunc_comp_resp sF sF2).

Variables sF sF3:hgFunc.

Lemma hgFunc_comp_hereditary : hereditary (appmod sF sF3).
Proof.
move=> gT H G sHG; rewrite -sub_morphim_pre; 
  last exact: (subset_trans (subsetIr _ _) (bgFunc_norm _ _)).
rewrite -[coset_morphism _ @* _]/(quotient _ _).
have:= (morphim_restrm (bgFunc_norm sF3 H) (coset_morphism (sF3 _ H)) H).
rewrite setIid=> rnorm_simpl.
have sqKfK: ('ker (restrm_morphism (subset_trans sHG (bgFunc_norm sF3 _))
                                   (coset_morphism (sF3 gT G)))
     :<=: 'ker (restrm_morphism (bgFunc_norm sF3 _) (coset_morphism (sF3 _ H)))).
  rewrite !ker_restrm !ker_coset (setIidPr (bgFunc_clos sF3 _)) setIC /=.
  exact: (hgFunc_hereditary sF3).
have sHrefl: (H \subset H) by [].
rewrite {2}/quotient -rnorm_simpl /= -(morphim_factm sHrefl sqKfK) /=.
apply: (subset_trans _ (gFunc_resp sF (factm_morphism _ _)))=>/=.
rewrite {2}morphim_restrm setIid.
apply: (subset_trans _ (morphimS (factm_morphism _ _)
  (hgFunc_hereditary sF (quotientS [group of sF3 _ G] sHG))))=>/=.
have:= (morphim_restrm (bgFunc_norm sF3 H) (coset_morphism (sF3 _ H)) 
  (appmod sF sF3 G :&: H)).
rewrite setIC setIA setIid {1}/quotient => <-.
rewrite -(morphim_factm sHrefl sqKfK) /=; apply:morphimS.
rewrite morphim_restrm setIA setIid -[coset _ @* _]/(quotient _ _).
apply:(subset_trans (morphimI _ _ _)).
rewrite morphpreK 1?setIC //=; apply:(subset_trans (bgFunc_clos sF _)).
exact: (quotientS [group of sF3 _ G] (bgFunc_norm sF3 G)).
Qed.

End HereditaryIdentitySubFunctorProps.

Canonical Structure hgFunc_comp_hgFunc (sF sF3:hgFunc)  :=
  @HgFunc (hgFunc_comp_gFunc sF sF3)
  (hgFunc_comp_hereditary sF sF3).

Module CompatibleGFunctor.

(* Mappings Functorial w.r.t. (surjective) morphisms,
   well-behaved w.r.t. application *)

Implicit Types gT: finGroupType.

Structure class : Type := Pack { 
  FgFunc :> gFunc;
   _ : compatible FgFunc}.

Definition repack FgFunc :=
  let: Pack c r := FgFunc return {type of Pack for FgFunc} -> _ in
    fun k => k r.

Lemma cgFunc_resp (sF: class): resp sF.
Proof. by move=> sF; apply:gFunc_resp. Qed.

Lemma cgFunc_compatible (sF : class): compatible sF.
Proof. by case => F. Qed.

End CompatibleGFunctor.

Notation cgFunc := CompatibleGFunctor.class.
Notation CgFunc := CompatibleGFunctor.Pack.

Notation "[ 'cgFunc' 'of' F ]" :=
  (CompatibleGFunctor.repack (fun m => @CgFunc [gFunc of F] m))
  (at level 0, only parsing) : form_scope.

Definition mkcgFunc F Fgrp Fsub (Fresp:resp F) (Fincr : compatible F) := 
  @CgFunc (mkGFunc Fgrp Fsub Fresp) Fincr.

Section CompatibleIdentitySubFunctorProps.

Implicit Types gT hT:finGroupType.

Section CompatibleIdBaseProps.

Variable sF: cgFunc.

Lemma cgFunc_resp : resp sF.
Proof. exact:GFunctor.gFunc_resp. Qed.

Lemma cgFunc_compatible : compatible sF.
Proof. exact:CompatibleGFunctor.cgFunc_compatible. Qed.

End CompatibleIdBaseProps.

Section CompatibleIdentitySFComp.

Variable sF: cgFunc.
Variable sF2 : gFunc.

(* independent from the group preservation requirement *)
Lemma cgFunc_comp_clos : forall gT (G:{group gT}),
  (app sF sF2) gT G \subset G.
Proof. by move=> gT G; rewrite (subset_trans (bgFunc_clos _ _)) ?bgFunc_clos. Qed.

Lemma cgFunc_comp_resp : resp (app sF sF2).
Proof.
move=> gT hT G phi.
rewrite (subset_trans (morphim_sFunctor _ _ (bgFunc_clos _ _))) //.
by rewrite (subset_trans (cgFunc_compatible sF (gFunc_resp sF2 phi))).
Qed.

End CompatibleIdentitySFComp.

Canonical Structure cgFunc_comp_bgFunc (sF:cgFunc) (sF2:gFunc) :=
  @mkBasegFunc (app sF sF2)
  (fun gT G => groupP [group of ((app sF sF2) _ G)])
  (cgFunc_comp_clos sF sF2)
  (aresp_of_resp (cgFunc_comp_resp sF sF2)).

Canonical Structure cgFunc_comp_gFunc (sF:cgFunc) (sF2:gFunc) :=
  @GFunc (cgFunc_comp_bgFunc sF sF2)
  (cgFunc_comp_resp sF sF2).

Variables sF sF3:cgFunc.

Lemma cgFunc_comp_compatible : compatible (cgFunc_comp_gFunc sF sF3).
Proof. by move=> gT H G sHG; rewrite !cgFunc_compatible. Qed.

End CompatibleIdentitySubFunctorProps.

Definition cgFunc_comp_hgFunc (sF sF3:cgFunc)  :=
  @CgFunc (cgFunc_comp_gFunc sF sF3) (cgFunc_comp_compatible sF sF3).

Section IdentitySubFunctorsExamples.

Implicit Types gT:finGroupType.

Lemma id_resp : resp (fun _ S => S).
Proof. by []. Qed.

Lemma id_compatible : compatible (fun _ S => S).
Proof. by []. Qed.

Canonical Structure bgFunc_id :=
  mkBasegFunc (fun gT G => groupP G%G)
  (fun gT G => subxx _)
  (aresp_of_resp id_resp).

Canonical Structure gFunc_id :=
  @GFunc bgFunc_id id_resp.

Lemma triv_resp : resp (fun _ S => 1).
Proof. by move=> gT hT H f; rewrite morphim1. Qed.

Canonical Structure bgFunc_triv :=
  @mkBasegFunc (fun _ S => 1)
  (fun _ G => groupP 1%G)
  sub1G
  (aresp_of_resp triv_resp).

Canonical Structure gFunc_triv :=
  @GFunc bgFunc_triv triv_resp.

End IdentitySubFunctorsExamples.

Unset Implicit Arguments.
