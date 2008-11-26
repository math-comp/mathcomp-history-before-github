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

(* "Anti-monotonicity" *)

Definition decr (F : obmap) : Prop :=
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

Lemma decr_of_dresp (sF:obmap) : dresp sF -> decr sF.
Proof.
move=> sF Hresp gT H G sHG; move: (Hresp _ _ G _ (idm_morphism H)) =>/=.
rewrite -morphimIdom -[idm H @* G]morphimIdom !morphim_idm ?subsetIl //.
by rewrite (setIidPl sHG) setIC.
Qed.

(* Increasing w.r.t. inclusion *)

Definition incr (F : obmap) : Prop :=
  forall gT (H G : {group gT}), H \subset G -> (F _ H) \subset (F _ G). 

End IdentitySubFunctorDefs.

Module BaseIdSubFunctor.

(* Those mappings only functorial w.r.t. isomorphisms*)

Implicit Types gT: finGroupType.

Structure mixin (Fobj : obmap) : Type := Mixin { 
  (* group preservation *)
  _ : forall gT (G:{group gT}), group_set (Fobj gT G);
  (* submapping *)
  _ : forall gT (G: {group gT}), Fobj gT G \subset G;
  (* functoriality condition *)
  _ : aresp Fobj}.

Structure class : Type := Class { Fobj :> obmap ; 
   _ : mixin Fobj}.

Definition subset_of (Fobj : obmap) (MF : mixin Fobj) := 
  let: Mixin _ s _ := MF return
  forall gT (G: {group gT}), Fobj gT G \subset G in s.

Definition group_of (Fobj : obmap) (MF : mixin Fobj) := 
  let: Mixin g _ _ := MF return
  forall gT (G: {group gT}), group_set (Fobj gT G) in g.

Coercion mixin_of F := let: Class _ m := F return mixin F in m.

End BaseIdSubFunctor.

Notation bisFc := BaseIdSubFunctor.class.
Notation BisFc := BaseIdSubFunctor.Class.
Notation BisFMixin := BaseIdSubFunctor.Mixin.

Definition mkBaseisFc F Fgrp Fsub Fresp := 
  BisFc (@BisFMixin F Fgrp Fsub Fresp).

Notation "[ 'bisFc' 'of' F ]" :=
  (match [is F : _ -> _ <: bisFc] as s return {type of BisFc for s} -> _ with
    | BisFc _ m => fun k => k m end
  (@BisFc F)) (at level 0, only parsing) : form_scope.

Notation Local "''e_' s ( G )" := (s _ G)
  (at level 8,s at level 2, format "''e_' s ( G )") : group_scope.

Lemma bisfc_groupset : forall (sF:bisFc) (gT:finGroupType) (G:{group gT}),
  group_set (sF gT G).
Proof. by move=> sF gT G; case sF=> F; case. Qed.

Canonical Structure bisfc_group (sF:bisFc) (gT:finGroupType) (G:{group gT}) :=
  (group (bisfc_groupset sF G)).

Section BaseIdentitySubfunctorProps.

Implicit Types gT hT:finGroupType.
Variable sF: bisFc.

Lemma bisfc_clos : forall (fT:finGroupType) (H:{group fT}),
  'e_sF(H) \subset H.
Proof. by case sF=> F; case. Qed.

Lemma bisfc_aresp : aresp sF.
Proof. by case sF=> Fobj; case. Qed.

Lemma bisfc_norm : forall gT (G:{group gT}), G \subset 'N('e_sF(G)).
Proof.
move=> gT G; apply/subsetP=> x Gx; rewrite inE -{2}(conjGid Gx) -{2}(setIid G).
by rewrite -(setIidPr (bisfc_clos G)) -!morphim_conj bisfc_aresp ?injm_conj.
Qed.

(* independent from the group preservation requirement*)
Lemma bisfc_gen_norm : forall gT (G:{group gT}),
  <<'e_sF(G)>> \subset 'N('e_sF(G)).
Proof.
move=> gT G; apply/normsP=> x Hx; move/normsP: (bisfc_norm G); apply.
by move: ((subsetP (genS (bisfc_clos G))) _ Hx); rewrite genGid.
Qed.

Lemma bisfc_normal : forall gT (G : {group gT}), 'e_sF(G) <| G.
Proof. by move=> gT G; apply/andP; rewrite bisfc_clos bisfc_norm. Qed.

Lemma bisfc_char : forall gT (G:{group gT}), 'e_sF(G) \char G.
Proof.
move=> gT G; apply/andP; split => //; first by apply: bisfc_clos.
apply/forallP=> f; apply/implyP=> Af; rewrite -{2}(autm_dom Af).
by rewrite -(morphimEsub (autm_morphism Af)) ?bisfc_clos ?bisfc_aresp ?injm_autm.
Qed.

Lemma bisfc_asresp_sub :
  forall gT hT (H G:{group gT})  (f : {morphism G >-> hT}),
  'injm f -> H \subset G -> f @* ('e_sF(H)) \subset 'e_sF(f @* H).
Proof.
move=> gT hT H G f injf sHG; apply/eqP; rewrite -(setIidPr (bisfc_clos H)).
by rewrite-{3}(setIid H) -!(morphim_restrm sHG) bisfc_aresp ?injm_restrm //=.
Qed.

Lemma bisfc_asresp : forall gT hT (H G : {group gT}) (f : {morphism G >-> hT}),
  'injm f -> H \subset G -> f @* ('e_sF(H)) = 'e_sF(f @* H).
Proof.
move=> gT hT H G f injf sHG; apply/eqP; rewrite eqEsubset bisfc_asresp_sub //=.
rewrite -{2}(morphim_invm injf sHG) -[f @* sF _ _](morphpre_invm injf).
have sFtr := subset_trans (bisfc_clos _).
by rewrite -sub_morphim_pre (bisfc_asresp_sub, sFtr) ?morphimS ?injm_invm.
Qed.

Lemma bisfc_nker_resp : forall gT hT (H G : {group gT})
  (f : {morphism G >-> hT}),
  'ker f = 1 -> H \subset G -> f @* ('e_sF(H)) = 'e_sF(f @* H).
Proof. by move=> gT hT H G f; move/trivgP =>/=; apply:bisfc_asresp. Qed.

Lemma bisfc_isom : forall gT hT (H G : {group gT}) (R : {group hT}) 
                                   (f : {morphism G >-> hT}),
  H \subset G -> isom H R f -> isom ('e_sF(H)) ('e_sF(R)) f.
Proof.
move=> gT rT H G R f; case/(restrmP f)=> g [_ _ ->]; case/isomP=> injf <-.
rewrite /isom -(bisfc_asresp injf) // -morphimEsub ?morphimDG ?morphim1 //. 
by rewrite subDset subsetU // bisfc_clos orbT.
Qed.

Lemma bisfc_isog : forall gT hT (G : {group gT}) (R : {group hT}),
  G \isog R -> 'e_sF(G) \isog 'e_sF(R).
Proof.
move=> gT rT D R; case/isogP=> f *.
apply: (isom_isog f) => //; first by apply: bisfc_clos.
apply: bisfc_isom => //; exact/isomP.
Qed.

End BaseIdentitySubfunctorProps.

Module IdSubFunctor.

(* Mappings functorial w.r.t. (surjective) morphisms *)

(* Beware, since our commutativity property is defined on f @* G,
   i.e. implicitly restricts Grp to surjective morphisms, these do not
   necessarily yield completely characteristic groups (counterexample :
   center).*)

Implicit Types gT: finGroupType.

Structure isFcClass : Type := Class { 
  FbisFc :> bisFc ;
   _ : resp FbisFc}.

Lemma isfc_resp (sF: isFcClass): resp sF.
Proof. by case => F FM. Qed.

End IdSubFunctor.

Notation isFc := IdSubFunctor.isFcClass.
Notation IsFc := IdSubFunctor.Class.

Definition mkIsFc F Fgrp Fsub (Fresp:resp F) := 
  @IsFc (mkBaseisFc Fgrp Fsub (aresp_of_resp Fresp)) Fresp.

Notation "[ 'isFc' 'of' F ]" :=
  (match [is F : _ -> _ <: isFc] as s return {type of IsFc for s} -> _ with
    | IsFc _ m => fun k => k m end
  (@IsFc F)) (at level 0, only parsing) : form_scope.

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
Proof. exact: bisfc_asresp. Qed.

Lemma isom_sfunctor : forall gT hT (D G : {group gT}) (R : {group hT}) 
                                   (f : {morphism D >-> hT}),
  G \subset D -> isom G R f -> isom ('e_sF(G)) ('e_sF(R)) f.
Proof. move=> gT hT D G; exact:bisfc_isom. Qed.

Lemma isog_sfunctor : forall gT hT (D : {group gT}) (R : {group hT}),
  D \isog R -> 'e_sF(D) \isog 'e_sF(R).
Proof. exact: bisfc_isog. Qed.

End IdentitySubFunctorProps.

Module DecrIdSubFunctor.

(* Mappings functorial w.r.t. (surjective) morphisms,
   well-behaved w.r.t. modulo application *)

Implicit Types gT: finGroupType.

Structure class : Type := Class { 
  FisFc :> isFc;
   _ : decr FisFc}.

Lemma disfc_resp (sF: class): resp sF.
Proof. by move=> sF; apply:isfc_resp. Qed.

Lemma disfc_decr (sF : class): decr sF.
Proof. by case => F. Qed.

End DecrIdSubFunctor.

Notation disFc := DecrIdSubFunctor.class.
Notation DisFc := DecrIdSubFunctor.Class.

Definition mkdIsFc F Fgrp Fsub (Fresp:resp F) (Fdecr : decr F) := 
  @DisFc (mkIsFc Fgrp Fsub Fresp) Fdecr.

Notation "[ 'disFc' 'of' F ]" :=
  (match [is F : _ -> _ <: disFc] as s return {type of DisFc for s} -> _ with
    | DisFc _ d => fun k => k  d end
  (@DisFc F)) (at level 0, only parsing) : form_scope.

Section DecreasingIdentitySubFunctorProps.

Implicit Types gT hT:finGroupType.

Section DecreasingIdBaseProps.

Variable sF: disFc.

Lemma disfc_resp : resp sF.
Proof. exact:IdSubFunctor.isfc_resp. Qed.

Lemma disfc_decr : decr sF.
Proof. exact:DecrIdSubFunctor.disfc_decr. Qed.

Lemma disfc_imsetI : forall gT (G H:{group gT}),
  'e_sF(G) :&: H = 'e_sF (G) :&: 'e_sF (G :&: H).
Proof.
move=>gT G H; rewrite -{1}(setIidPr (bisfc_clos sF G)) [G :&: _]setIC -setIA.
move/setIidPr: (disfc_decr (subsetIl G H)) <-.
by rewrite setIC -setIA (setIidPr (bisfc_clos sF (G:&: H))).
Qed.

Lemma disfc_morphim : dresp sF.
Proof.
move=> gT hT G D f.
rewrite -morphimIdom -(setIidPl (bisfc_clos sF G)) setIC -setIA [G :&: _]setIC.
apply: (subset_trans (morphimS f (disfc_decr (subsetIr D G)))).
apply:(subset_trans (morphim_sfunctor sF _ _ )); last by rewrite morphimIdom.
exact:subsetIl.
Qed.

End DecreasingIdBaseProps.

Section DecreasingIdentitySFComp.

Variable sF: disFc.
Variable sF2 : isFc.

(* independent from the group preservation requirement *)
Lemma disfc_comp_clos : forall gT (G:{group gT}),
  (appmod sF sF2) gT G \subset G.
Proof.
move=> gT G; rewrite /appmod; have nFD := (bisfc_norm sF2 G).
rewrite sub_morphpre_im ?(bisfc_clos sF) //=.
  by rewrite ker_coset_prim subIset // gen_subG (bisfc_clos sF2 G).
by apply: subset_trans (bisfc_clos sF _) _; apply: morphimS.
Qed.

Lemma disfc_comp_idsubfunc : forall gT (G : {group gT}) (B : {set gT}),
  (coset B @*^-1  sF _ (G / B)) / B  = sF _ (G / B).
Proof.
move=> gT A B; apply: morphpreK; apply: subset_trans (bisfc_clos sF _) _.
by rewrite /= /quotient -morphimIdom  morphimS ?subsetIl.
Qed.

Lemma disfc_comp_resp : resp (appmod sF sF2).
move=> gT rT G f; have nF := bisfc_norm sF2.
have kF := ker_coset (Group (bisfc_groupset sF2 _)); simpl in kF.
have sDF: G \subset 'dom (coset (sF2 _ G)) by rewrite ?nF.
have sDFf: G \subset 'dom (coset (sF2 _ (f @* G)) \o f).
  by rewrite -sub_morphim_pre ?subsetIl // nF.
pose K := 'ker (restrm sDFf (coset (sF2 _ (f @* G)) \o f)).
have sFK: 'ker (restrm sDF (coset (sF2 _ G))) \subset K.
  rewrite /K  !ker_restrm ker_comp /= subsetI subsetIl /=.
  by rewrite -sub_morphim_pre ?subsetIl // morphimIdom !kF ?morphim_sfunctor.
have sOF := bisfc_clos sF (G / sF2 _ G); have sGG: G \subset G by [].
rewrite -sub_morphim_pre -?quotientE; last first.
  by apply: subset_trans (nF _ _); rewrite morphimS ?disfc_comp_clos.
suffices im_fact: forall H : {group gT}, sF2 _ G \subset H -> H \subset G ->
  factm sGG sFK @* (H / sF2 _ G) = f @* H / sF2 _ (f @* G).
- rewrite -2?im_fact ?disfc_comp_clos ?bisfc_clos //.
  by rewrite disfc_comp_idsubfunc morphim_sfunctor /= ?morphim_restrm ?setIid //.
  by rewrite -{1}kF morphpreS ?sub1G.
move=> H sFH sHG; rewrite -(morphimIdom _ (H / _)) /= {2}morphim_restrm setIid.
rewrite -morphimIG ?kF // -(morphim_restrm sDF) morphim_factm morphim_restrm.
by rewrite morphim_comp -quotientE morphimIdom.
Qed.

End DecreasingIdentitySFComp.

(*The structure for this one is un-inferrable, see morphim for phantom creation*)
Definition disfc_comp_isfc (sF:disFc) (sF2:isFc) :=
  @mkIsFc (appmod sF sF2)
  (fun gT G => groupP [group of ((appmod sF sF2) _ G)])
  (disfc_comp_clos sF sF2)
  (disfc_comp_resp sF sF2).

(* TOFIX *)

Variables sF sF3:disFc.

Lemma disfc_comp_dresp : dresp (disfc_comp_isfc sF sF3).
Proof.
move=> gT rT G D f /=; have nF := bisfc_norm sF3.
have kF := ker_coset (Group (bisfc_groupset sF3 _)); simpl in kF.
have sDF: D :&: G \subset 'dom (coset (sF3 _ G)) by rewrite setIC subIset ?nF.
have sDFf: D :&: G \subset 'dom (coset (sF3 _ (f @* G)) \o f).
  by rewrite -sub_morphim_pre ?subsetIl // morphimIdom nF.
pose K := 'ker (restrm sDFf (coset (sF3 _ (f @* G)) \o f)).
have sFK: 'ker (restrm sDF (coset (sF3 _ G))) \subset K.
  rewrite /K  !ker_restrm ker_comp /= subsetI subsetIl /= -setIA.
  by rewrite -sub_morphim_pre ?subsetIl // morphimIdom !kF (setIidPr _) ?disfc_morphim ?bisfc_clos.
have sOF := bisfc_clos sF (G / sF3 _ G); have sGG: D :&: G \subset D :&: G by [].
rewrite -sub_morphim_pre -?quotientE; last first.
  by apply: subset_trans (nF _ _); rewrite morphimS ?disfc_comp_clos.
suffices im_fact: forall H : {group gT}, sF3 _ G \subset H -> H \subset G ->
  factm sGG sFK @* (H / sF3 _ G) = f @* H / sF3 _ (f @* G).
- rewrite -2?im_fact ?disfc_comp_clos ?bisfc_clos //.
  by rewrite disfc_comp_idsubfunc disfc_morphim /=.
  by rewrite -{1}kF morphpreS ?sub1G.
move=> H sFH sHG; rewrite -(morphimIdom _ (H / _)) /= {2}morphim_restrm setIid.
rewrite -morphimIG ?kF // -(morphim_restrm sDF) morphim_factm morphim_restrm.
by rewrite morphim_comp -quotientE -setIA morphimIdom (setIidPr _).
Qed.

End DecreasingIdentitySubFunctorProps.

Definition disfc_comp_disfc (sF sF3:disFc)  :=
  DisFc (decr_of_dresp (disfc_comp_dresp sF sF3)).

Module IncrIdSubFunctor.

(* Mappings functorial w.r.t. (surjective) morphisms,
   well-behaved w.r.t. application *)

Implicit Types gT: finGroupType.

Structure class : Type := Class { 
  FisFc :> isFc;
   _ : incr FisFc}.

Lemma iisfc_resp (sF: class): resp sF.
Proof. by move=> sF; apply:isfc_resp. Qed.

Lemma iisfc_incr (sF : class): incr sF.
Proof. by case => F. Qed.

End IncrIdSubFunctor.

Notation iisFc := IncrIdSubFunctor.class.
Notation IisFc := IncrIdSubFunctor.Class.

Definition mkiIsFc F Fgrp Fsub (Fresp:resp F) (Fincr : incr F) := 
  @IisFc (mkIsFc Fgrp Fsub Fresp) Fincr.

Notation "[ 'iisFc' 'of' F ]" :=
  (match [is F : _ -> _ <: iisFc] as s return {type of IisFc for s} -> _ with
    | IisFc _ d => fun k => k  d end
  (@IisFc F)) (at level 0, only parsing) : form_scope.

Section IncreasingIdentitySubFunctorProps.

Implicit Types gT hT:finGroupType.

Section IncreasingIdBaseProps.

Variable sF: iisFc.

Lemma iisfc_resp : resp sF.
Proof. exact:IdSubFunctor.isfc_resp. Qed.

Lemma iisfc_incr : incr sF.
Proof. exact:IncrIdSubFunctor.iisfc_incr. Qed.

End IncreasingIdBaseProps.

Section IncreasingIdentitySFComp.

Variable sF: iisFc.
Variable sF2 : isFc.

(* independent from the group preservation requirement *)
Lemma iisfc_comp_clos : forall gT (G:{group gT}),
  (app sF sF2) gT G \subset G.
Proof. by move=> gT G; rewrite (subset_trans (bisfc_clos _ _)) ?bisfc_clos. Qed.

Lemma iisfc_comp_resp : resp (app sF sF2).
Proof.
move=> gT hT G phi.
rewrite (subset_trans (morphim_sfunctor _ _ (bisfc_clos _ _))) //.
by rewrite (subset_trans (iisfc_incr sF (isfc_resp sF2 phi))).
Qed.

End IncreasingIdentitySFComp.

(*The structure for this one is un-inferrable, 
   see morphim for phantom creation*)
Definition iisfc_comp_isfc (sF:iisFc) (sF2:isFc) :=
  @mkIsFc (app sF sF2)
  (fun gT G => groupP [group of ((app sF sF2) _ G)])
  (iisfc_comp_clos sF sF2)
  (iisfc_comp_resp sF sF2).

(* TOFIX *)

Variables sF sF3:iisFc.

Lemma iisfc_comp_incr : incr (iisfc_comp_isfc sF sF3).
Proof. by move=> gT H G sHG; rewrite !iisfc_incr. Qed.

End IncreasingIdentitySubFunctorProps.

Definition iisfc_comp_disfc (sF sF3:iisFc)  :=
  IisFc (iisfc_comp_incr sF sF3).

Section IdentitySubfunctorsExamples.

Implicit Types gT:finGroupType.

Lemma id_resp : resp (fun _ S => S).
Proof. by []. Qed.

Lemma id_incr : incr (fun _ S => S).
Proof. by []. Qed.

Canonical Structure incr_id_subfunc :=
  mkiIsFc (fun gT G => groupP G%G)
  (fun gT G => subxx _)
  id_resp.

Lemma triv_resp : resp (fun _ S => 1).
Proof. by move=> gT hT H f; rewrite morphim1. Qed.

Canonical Structure triv_subfunc :=
  @mkIsFc (fun _ S => 1)
  (fun _ G => groupP 1%G)
  sub1G
  triv_resp.

Require Import center.

Lemma center_resp : resp (fun _ S => 'Z(S)).
Proof.
move=> gT hT H phi /=; apply:(subset_trans (morphimI _ _ _ )).
rewrite subsetI subsetIl /=; apply:(subset_trans (subsetIr (phi @* H) _) ).
exact:morphim_cent.
Qed.

Lemma center_decr : decr (fun _ S => 'Z(S)).
Proof.
move=> gT H G sHG; rewrite setIC /center setIA (setIidPl sHG) setIS //.
by rewrite (centsS sHG).
Qed.

Canonical Structure center_decr_id_subfunc :=
  mkdIsFc (fun gT G => groupP 'Z(G)%G) (fun gT G => @center_sub gT G)
         center_resp center_decr.

Require Import maximal.

Lemma Frattini_resp : resp (Frattini).
Proof. exact: gfunc_Phi. Qed.

Canonical Structure Frattini_subfunc :=
  mkIsFc (fun gT G => groupP 'Phi(G)%G) (fun gT => @Phi_sub gT)
         Frattini_resp.

Lemma Fitting_decr : decr (fun _ G => 'F(G)).
Proof. by move=> gT H G; move/FittingS; rewrite setIC. Qed.

Canonical Structure Fitting_decr_id_subfunc :=
  mkdIsFc (fun gT G => groupP 'F(G)%G)
           Fitting_sub
           gfunc_Fitting
           Fitting_decr.

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

Lemma der_incr : forall n, 
  incr (fun gT G => derived_at G n).
Proof.
elim => [|n IH] gT H G sHG; first by rewrite !derg0.
by rewrite !dergSn commgSS ?IH.
Qed.

Canonical Structure der_incr_id_subfunctor (n:nat) :=
  mkiIsFc (fun gT (G:{group gT}) => der_group_set G n)
         (der_clos n)
         (der_resp n)
         (der_incr n).

Lemma lcn_resp : forall n,
  resp (fun gT G => 'L_n(G)).
Proof.
elim=> [|n IH] gT hT H phi; first by rewrite !lcn0.
by rewrite !lcnSn morphimR ?lcn_sub0 // commSg ?IH.
Qed.

Lemma lcn_incr : forall n,
  incr (fun gT G => 'L_n(G)).
Proof.
elim=> [|n IH] gT H G sHG; first by rewrite !lcn0.
by rewrite !lcnSn commgSS ?IH.
Qed.

Canonical Structure lcn_incr_id_subfunctor (n:nat) :=
  mkiIsFc (fun gT (G :{group gT}) => lcn_group_set G n)
  (fun gT G => (lcn_sub0 G n))
  (lcn_resp n)
  (lcn_incr n).

Lemma ucn_isfc :  forall n,
  [/\ resp (fun _ G => 'Z_n(G)),
      decr (fun _ G => 'Z_n(G)) & 
      forall gT (G:{group gT}), 'Z_n(G) \subset G ].
Proof.
elim => [|n [Hresp Hdecr Hsub]].
 by split=> [gT hT G phi|gT H G sHG| gT G];
 rewrite ?ucn0 ?morphim1 ?sub1G ?subsetIl //.
pose Zn := (mkdIsFc (fun _ G => ucn_group_set G n) Hsub Hresp Hdecr).
(* TOFIX *)
pose ZSn := (disfc_comp_disfc center_decr_id_subfunc Zn).
split=> [gT hT G phi|gT H G sHG| gT G]; rewrite ucnSn.
- apply: (isfc_resp ZSn).
- apply: (disfc_decr ZSn sHG).
- apply: (bisfc_clos ZSn).
Qed.

Lemma ucn_resp : forall n, resp (fun _ G => 'Z_n(G)).
Proof. by move=> n; case:(ucn_isfc n). Qed.

Lemma ucn_decr : forall n, decr (fun _ G => 'Z_n(G)).
Proof. by move=> n; case:(ucn_isfc n). Qed.

Lemma ucn_clos : forall n gT (G:{group gT}), 'Z_n(G) \subset G.
Proof. by move=> n; case:(ucn_isfc n). Qed.

Canonical Structure ucn_decr_id_subfunctor (n:nat) :=
  mkdIsFc (fun gT (G:{group gT}) => ucn_group_set G n)
  (ucn_clos n)
  (ucn_resp n)
  (ucn_decr n).

Require Import prime.
Require Import pgroups.

Lemma pcore_decr : forall (pi:nat_pred), decr (fun _ G => 'O_pi(G)).
Proof. by move=> pi gT H G; move/pcoreS; rewrite setIC. Qed.

Canonical Structure pcore_decr_id_subfunctor (pi:nat_pred) :=
  mkdIsFc (fun gT (G:{group gT}) => groupP [group of 'O_pi(G)])
  (pcore_sub pi)
  (gfunc_pcore pi)
  (pcore_decr pi).


Lemma Ohm_sub : forall i gT (G:{group gT}), 'Ohm_i(G) \subset G.
Proof. move=> gT i; exact: Ohm_sub. Qed.

Lemma Ohm_resp : forall i,
  resp (fun gT S => 'Ohm_i(S)).
Proof. move=> i G f; exact: gfunc_Ohm. Qed.

Canonical Structure Ohm_id_subfunctor (i:nat) :=
  mkIsFc (fun gT (G:{group gT}) => groupP 'Ohm_i(G)%G)
  (Ohm_sub i)
  (Ohm_resp i).

Lemma Mho_sub : forall i gT (G:{group gT}), 'Mho^i(G) \subset G.
Proof. move=> i; exact: Mho_sub. Qed.

Lemma Mho_resp : forall i,
  resp (fun gT S => 'Mho^i(S)).
Proof. move=> i G f; exact: gfunc_Mho. Qed.

Lemma Mho_incr : forall i,
  incr (fun gT S => 'Mho^i(S)).
Proof. move=> i gT H G sHG; exact:MhoS. Qed.

Canonical Structure Mho_id_subfunctor (i:nat) :=
  mkiIsFc (fun gT (G:{group gT}) => groupP 'Mho^i(G)%G)
  (Mho_sub i)
  (Mho_resp i)
  (Mho_incr i).

End IdentitySubfunctorsExamples.

Unset Implicit Arguments.
