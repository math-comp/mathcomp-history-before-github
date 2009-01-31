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

Structure mixin (Fobj : obmap) : Type := Mixin { 
  (* group preservation *)
  _ : forall gT (G:{group gT}), group_set (Fobj _ G);
  (* submapping *)
  _ : forall gT (G: {group gT}), Fobj _ G \subset G;
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

End BaseGFunctor.

Notation bgFunc := BaseGFunctor.class.
Notation BgFunc := BaseGFunctor.Class.
Notation BgFuncMixin := BaseGFunctor.Mixin.

Definition mkBasegFunc F Fgrp Fsub Fresp := 
  BgFunc (@BgFuncMixin F Fgrp Fsub Fresp).

Notation "[ 'bgFunc' 'of' F ]" :=
  (match [the bgFunc of F : _ -> _] as s return {type of BgFunc for s} -> _ with
    | BgFunc _ m => fun k => k m end
  (@BgFunc F)) (at level 0, only parsing) : form_scope.

Notation Local "''e_' s ( G )" := (s _ G)
  (at level 8,s at level 2, format "''e_' s ( G )") : group_scope.

Lemma bgfunc_groupset : forall (sF:bgFunc) (gT:finGroupType) (G:{group gT}),
  group_set (sF gT G).
Proof. by move=> sF gT G; case sF=> F; case. Qed.

Canonical Structure bgfunc_group (sF:bgFunc) (gT:finGroupType) (G:{group gT}) :=
  (group (bgfunc_groupset sF G)).

Section BaseIdentitySubfunctorProps.

Implicit Types gT hT:finGroupType.
Variable sF: bgFunc.

Lemma bgfunc_clos : forall (fT:finGroupType) (H:{group fT}),
  'e_sF(H) \subset H.
Proof. by case sF=> F; case. Qed.

Lemma bgfunc_aresp : aresp sF.
Proof. by case sF=> Fobj; case. Qed.

Lemma bgfunc_char : forall gT (G:{group gT}), 'e_sF(G) \char G.
Proof.
move=> gT G; apply/andP; split => //; first by apply: bgfunc_clos.
apply/forallP=> f; apply/implyP=> Af; rewrite -{2}(autm_dom Af).
by rewrite -(morphimEsub (autm_morphism Af)) ?bgfunc_clos ?bgfunc_aresp ?injm_autm.
Qed.

Lemma bgfunc_norm : forall gT (G:{group gT}), G \subset 'N('e_sF(G)).
Proof. by move=> *; rewrite char_norm ?bgfunc_char. Qed.

(* independent from the group preservation requirement*)
Lemma bgfunc_gen_norm : forall gT (G:{group gT}),
  <<'e_sF(G)>> \subset 'N('e_sF(G)).
Proof.
move=> gT G; apply/normsP=> x Hx; move/normsP: (bgfunc_norm G); apply.
by move: ((subsetP (genS (bgfunc_clos G))) _ Hx); rewrite genGid.
Qed.

Lemma bgfunc_normal : forall gT (G : {group gT}), 'e_sF(G) <| G.
Proof.  by move=> *; rewrite char_normal ?bgfunc_char. Qed.

Lemma bgfunc_asresp_sub :
  forall gT hT (H G:{group gT})  (f : {morphism G >-> hT}),
  'injm f -> H \subset G -> f @* ('e_sF(H)) \subset 'e_sF(f @* H).
Proof.
move=> gT hT H G f injf sHG; apply/eqP; rewrite -(setIidPr (bgfunc_clos H)).
by rewrite-{3}(setIid H) -!(morphim_restrm sHG) bgfunc_aresp ?injm_restrm //=.
Qed.

Lemma bgfunc_asresp : forall gT hT (H G : {group gT}) (f : {morphism G >-> hT}),
  'injm f -> H \subset G -> f @* ('e_sF(H)) = 'e_sF(f @* H).
Proof.
move=> gT hT H G f injf sHG; apply/eqP; rewrite eqEsubset bgfunc_asresp_sub //=.
rewrite -{2}(morphim_invm injf sHG) -[f @* sF _ _](morphpre_invm injf).
have sFtr := subset_trans (bgfunc_clos _).
by rewrite -sub_morphim_pre (bgfunc_asresp_sub, sFtr) ?morphimS ?injm_invm.
Qed.

Lemma bgfunc_nker_resp : forall gT hT (H G : {group gT})
  (f : {morphism G >-> hT}),
  'ker f = 1 -> H \subset G -> f @* ('e_sF(H)) = 'e_sF(f @* H).
Proof. by move=> gT hT H G f; move/trivgP =>/=; apply:bgfunc_asresp. Qed.

Lemma bgfunc_isom : forall gT hT (H G : {group gT}) (R : {group hT}) 
                                   (f : {morphism G >-> hT}),
  H \subset G -> isom H R f -> isom ('e_sF(H)) ('e_sF(R)) f.
Proof.
move=> gT rT H G R f; case/(restrmP f)=> g [_ _ ->]; case/isomP=> injf <-.
rewrite /isom -(bgfunc_asresp injf) // -morphimEsub ?morphimDG ?morphim1 //. 
by rewrite subDset subsetU // bgfunc_clos orbT.
Qed.

Lemma bgfunc_isog : forall gT hT (G : {group gT}) (R : {group hT}),
  G \isog R -> 'e_sF(G) \isog 'e_sF(R).
Proof.
move=> gT rT D R; case/isogP=> f *.
apply: (isom_isog f) => //; first by apply: bgfunc_clos.
apply: bgfunc_isom => //; exact/isomP.
Qed.

End BaseIdentitySubfunctorProps.

Module GFunctor.

(* Mappings functorial w.r.t. (surjective) morphisms *)

(* Beware, since our commutativity property is defined on f @* G,
   i.e. implicitly restricts Grp to surjective morphisms, these do not
   necessarily yield completely characteristic groups (counterexample :
   center).*)

Implicit Types gT: finGroupType.

Structure gFuncClass : Type := Class { 
  FbgFunc :> bgFunc ;
   _ : resp FbgFunc}.

Lemma gfunc_resp (sF: gFuncClass): resp sF.
Proof. by case => F FM. Qed.

End GFunctor.

Notation gFunc := GFunctor.gFuncClass.
Notation Gfunc := GFunctor.Class.

Definition mkGfunc F Fgrp Fsub (Fresp:resp F) := 
  @Gfunc (@BgFunc F (@BgFuncMixin F Fgrp Fsub (aresp_of_resp Fresp))) Fresp.

Notation "[ 'gFunc' 'of' F ]" :=
  (match [the gFunc of F : _ -> _] as s return {type of Gfunc for s} -> _ with
    | Gfunc _ m => fun k => k m end
  (@Gfunc [bgFunc of F])) (at level 0, only parsing) : form_scope.

Section IdentitySubFunctorProps.

Implicit Types gT hT:finGroupType.
Variable sF: gFunc.

Lemma gfunc_resp : resp sF.
Proof. exact:GFunctor.gfunc_resp. Qed.

Lemma morphim_sfunctor : forall gT hT (G D : {group gT})
  (f : {morphism D >-> hT}),
  G \subset D -> f @* ('e_sF(G)) \subset 'e_sF(f @* G).
Proof.
move=> gT hT G D f sGD; rewrite -(setIidPr (bgfunc_clos sF G)).
by rewrite  -{3}(setIid G) -!(morphim_restrm sGD) gfunc_resp.
Qed.

Lemma injm_sfunctor : forall gT hT (G D : {group gT}) (f : {morphism D >-> hT}),
  'injm f -> G \subset D -> f @* ('e_sF(G)) = 'e_sF(f @* G).
Proof. exact: bgfunc_asresp. Qed.

Lemma isom_sfunctor : forall gT hT (D G : {group gT}) (R : {group hT}) 
                                   (f : {morphism D >-> hT}),
  G \subset D -> isom G R f -> isom ('e_sF(G)) ('e_sF(R)) f.
Proof. move=> gT hT D G; exact:bgfunc_isom. Qed.

Lemma isog_sfunctor : forall gT hT (D : {group gT}) (R : {group hT}),
  D \isog R -> 'e_sF(D) \isog 'e_sF(R).
Proof. exact: bgfunc_isog. Qed.

End IdentitySubFunctorProps.

Module HereditaryGFunctor.

(* Mappings functorial w.r.t. (surjective) morphisms,
   well-behaved w.r.t. modulo application *)

Implicit Types gT: finGroupType.

Structure class : Type := Class { 
  FgFunc :> gFunc;
   _ : hereditary FgFunc}.

Lemma hgfunc_resp (sF: class): resp sF.
Proof. by move=> sF; apply:gfunc_resp. Qed.

Lemma hgfunc_hereditary (sF : class): hereditary sF.
Proof. by case => F. Qed.

End HereditaryGFunctor.

Notation hgfunc := HereditaryGFunctor.class.
Notation Hgfunc := HereditaryGFunctor.Class.

Definition mkhgfunc F Fgrp Fsub (Fresp:resp F) (Fdecr : hereditary F) := 
  @Hgfunc
    (@Gfunc
      (@BgFunc F (@BgFuncMixin F Fgrp Fsub (aresp_of_resp Fresp)))
     Fresp)
  Fdecr.

Notation "[ 'hgfunc' 'of' F ]" :=
  (match [the hgfunc of F : _ -> _ ] as s return {type of Hgfunc for s} -> _ with
    | Hgfunc _ d => fun k => k  d end
  (@Hgfunc [gFunc of F])) (at level 0, only parsing) : form_scope.

Section HereditaryIdentitySubFunctorProps.

Implicit Types gT hT:finGroupType.

Section HereditaryIdBaseProps.

Variable sF: hgfunc.

Lemma hgfunc_resp : resp sF.
Proof. exact:GFunctor.gfunc_resp. Qed.

Lemma hgfunc_hereditary : hereditary sF.
Proof. exact:HereditaryGFunctor.hgfunc_hereditary. Qed.

Lemma hgfunc_imsetI : forall gT (G H:{group gT}),
  'e_sF(G) :&: H = 'e_sF (G) :&: 'e_sF (G :&: H).
Proof.
move=>gT G H; rewrite -{1}(setIidPr (bgfunc_clos sF G)) [G :&: _]setIC -setIA.
move/setIidPr: (hgfunc_hereditary (subsetIl G H)) <-.
by rewrite setIC -setIA (setIidPr (bgfunc_clos sF (G:&: H))).
Qed.

Lemma hgfunc_morphim : dresp sF.
Proof.
move=> gT hT G D f.
rewrite -morphimIdom -(setIidPl (bgfunc_clos sF G)) setIC -setIA [G :&: _]setIC.
apply: (subset_trans (morphimS f (hgfunc_hereditary (subsetIr D G)))).
apply:(subset_trans (morphim_sfunctor sF _ _ )); last by rewrite morphimIdom.
exact:subsetIl.
Qed.

Lemma hereditary_idem : forall (gT:finGroupType) (G:{group gT}),
  (app sF sF) _ G  = sF _ G.
Proof.
move=> gT G /=; apply/eqP; rewrite eqEsubset bgfunc_clos.
by move/hgfunc_hereditary : (bgfunc_clos sF G); rewrite setIid /=.
Qed.

End HereditaryIdBaseProps.

Section HereditaryIdentitySFComp.

Variable sF: hgfunc.
Variable sF2 : gFunc.

(* independent from the group preservation requirement *)
Lemma hgfunc_comp_clos : forall gT (G:{group gT}),
  (appmod sF sF2) gT G \subset G.
Proof.
move=> gT G; rewrite /appmod; have nFD := (bgfunc_norm sF2 G).
rewrite sub_morphpre_im ?(bgfunc_clos sF) //=.
  by rewrite ker_coset_prim subIset // gen_subG (bgfunc_clos sF2 G).
by apply: subset_trans (bgfunc_clos sF _) _; apply: morphimS.
Qed.

Lemma hgfunc_comp_quo : forall gT (G : {group gT}) (B : {set gT}),
  (coset B @*^-1  sF _ (G / B)) / B  = sF _ (G / B).
Proof.
move=> gT A B; apply: morphpreK; apply: subset_trans (bgfunc_clos sF _) _.
by rewrite /= /quotient -morphimIdom  morphimS ?subsetIl.
Qed.

Lemma hgfunc_comp_resp : resp (appmod sF sF2).
move=> gT rT G f; have nF := bgfunc_norm sF2.
have kF := ker_coset (Group (bgfunc_groupset sF2 _)); simpl in kF.
have sDF: G \subset 'dom (coset (sF2 _ G)) by rewrite ?nF.
have sDFf: G \subset 'dom (coset (sF2 _ (f @* G)) \o f).
  by rewrite -sub_morphim_pre ?subsetIl // nF.
pose K := 'ker (restrm sDFf (coset (sF2 _ (f @* G)) \o f)).
have sFK: 'ker (restrm sDF (coset (sF2 _ G))) \subset K.
  rewrite /K  !ker_restrm ker_comp /= subsetI subsetIl /=.
  by rewrite -sub_morphim_pre ?subsetIl // morphimIdom !kF ?morphim_sfunctor.
have sOF := bgfunc_clos sF (G / sF2 _ G); have sGG: G \subset G by [].
rewrite -sub_morphim_pre -?quotientE; last first.
  by apply: subset_trans (nF _ _); rewrite morphimS ?hgfunc_comp_clos.
suffices im_fact: forall H : {group gT}, sF2 _ G \subset H -> H \subset G ->
  factm sGG sFK @* (H / sF2 _ G) = f @* H / sF2 _ (f @* G).
- rewrite -2?im_fact ?hgfunc_comp_clos ?bgfunc_clos //.
  by rewrite hgfunc_comp_quo morphim_sfunctor /= ?morphim_restrm ?setIid //.
  by rewrite -{1}kF morphpreS ?sub1G.
move=> H sFH sHG; rewrite -(morphimIdom _ (H / _)) /= {2}morphim_restrm setIid.
rewrite -morphimIG ?kF // -(morphim_restrm sDF) morphim_factm morphim_restrm.
by rewrite morphim_comp -quotientE morphimIdom.
Qed.

End HereditaryIdentitySFComp.

Canonical Structure hgfunc_comp_bgfunc (sF:hgfunc) (sF2:gFunc) :=
  @mkBasegFunc (appmod sF sF2)
  (fun gT G => groupP [group of ((appmod sF sF2) _ G)])
  (hgfunc_comp_clos sF sF2)
  (aresp_of_resp (hgfunc_comp_resp sF sF2)).

Canonical Structure hgfunc_comp_gfunc (sF:hgfunc) (sF2:gFunc) :=
  @Gfunc (hgfunc_comp_bgfunc sF sF2)
  (hgfunc_comp_resp sF sF2).

Variables sF sF3:hgfunc.

Lemma hgfunc_comp_dresp : dresp ([gFunc of (appmod sF sF3)]).
Proof.
move=> gT rT G D f /=; have nF := bgfunc_norm sF3.
have kF := ker_coset (Group (bgfunc_groupset sF3 _)); simpl in kF.
have sDF: D :&: G \subset 'dom (coset (sF3 _ G)) by rewrite setIC subIset ?nF.
have sDFf: D :&: G \subset 'dom (coset (sF3 _ (f @* G)) \o f).
  by rewrite -sub_morphim_pre ?subsetIl // morphimIdom nF.
pose K := 'ker (restrm sDFf (coset (sF3 _ (f @* G)) \o f)).
have sFK: 'ker (restrm sDF (coset (sF3 _ G))) \subset K.
  rewrite /K  !ker_restrm ker_comp /= subsetI subsetIl /= -setIA.
  by rewrite -sub_morphim_pre ?subsetIl // morphimIdom !kF (setIidPr _) ?hgfunc_morphim ?bgfunc_clos.
have sOF := bgfunc_clos sF (G / sF3 _ G); have sGG: D :&: G \subset D :&: G by [].
rewrite -sub_morphim_pre -?quotientE; last first.
  by apply: subset_trans (nF _ _); rewrite morphimS ?hgfunc_comp_clos.
suffices im_fact: forall H : {group gT}, sF3 _ G \subset H -> H \subset G ->
  factm sGG sFK @* (H / sF3 _ G) = f @* H / sF3 _ (f @* G).
- rewrite -2?im_fact ?hgfunc_comp_clos ?bgfunc_clos //.
  by rewrite hgfunc_comp_quo hgfunc_morphim /=.
  by rewrite -{1}kF morphpreS ?sub1G.
move=> H sFH sHG; rewrite -(morphimIdom _ (H / _)) /= {2}morphim_restrm setIid.
rewrite -morphimIG ?kF // -(morphim_restrm sDF) morphim_factm morphim_restrm.
by rewrite morphim_comp -quotientE -setIA morphimIdom (setIidPr _).
Qed.

End HereditaryIdentitySubFunctorProps.

Canonical Structure hgfunc_comp_hgfunc (sF sF3:hgfunc)  :=
  @Hgfunc (hgfunc_comp_gfunc sF sF3)
  (hereditary_of_dresp (hgfunc_comp_dresp sF sF3)).

Module CompatibleGfunctor.

(* Mappings functorial w.r.t. (surjective) morphisms,
   well-behaved w.r.t. application *)

Implicit Types gT: finGroupType.

Structure class : Type := Class { 
  FgFunc :> gFunc;
   _ : compatible FgFunc}.

Lemma cgfunc_resp (sF: class): resp sF.
Proof. by move=> sF; apply:gfunc_resp. Qed.

Lemma cgfunc_compatible (sF : class): compatible sF.
Proof. by case => F. Qed.

End CompatibleGfunctor.

Notation cgfunc := CompatibleGfunctor.class.
Notation Cgfunc := CompatibleGfunctor.Class.

Definition mkcgfunc F Fgrp Fsub (Fresp:resp F) (Fincr : compatible F) := 
  @Cgfunc (mkGfunc Fgrp Fsub Fresp) Fincr.

Notation "[ 'cgfunc' 'of' F ]" :=
  (match [the cgfunc of F : _ -> _ ] as s return {type of Cgfunc for s} -> _ with
    | Cgfunc _ d => fun k => k  d end
  (@Cgfunc [gFunc of F])) (at level 0, only parsing) : form_scope.

Section CompatibleIdentitySubFunctorProps.

Implicit Types gT hT:finGroupType.

Section CompatibleIdBaseProps.

Variable sF: cgfunc.

Lemma cgfunc_resp : resp sF.
Proof. exact:GFunctor.gfunc_resp. Qed.

Lemma cgfunc_compatible : compatible sF.
Proof. exact:CompatibleGfunctor.cgfunc_compatible. Qed.

End CompatibleIdBaseProps.

Section CompatibleIdentitySFComp.

Variable sF: cgfunc.
Variable sF2 : gFunc.

(* independent from the group preservation requirement *)
Lemma cgfunc_comp_clos : forall gT (G:{group gT}),
  (app sF sF2) gT G \subset G.
Proof. by move=> gT G; rewrite (subset_trans (bgfunc_clos _ _)) ?bgfunc_clos. Qed.

Lemma cgfunc_comp_resp : resp (app sF sF2).
Proof.
move=> gT hT G phi.
rewrite (subset_trans (morphim_sfunctor _ _ (bgfunc_clos _ _))) //.
by rewrite (subset_trans (cgfunc_compatible sF (gfunc_resp sF2 phi))).
Qed.

End CompatibleIdentitySFComp.

Canonical Structure cgfunc_comp_bgfunc (sF:cgfunc) (sF2:gFunc) :=
  @mkBasegFunc (app sF sF2)
  (fun gT G => groupP [group of ((app sF sF2) _ G)])
  (cgfunc_comp_clos sF sF2)
  (aresp_of_resp (cgfunc_comp_resp sF sF2)).

Canonical Structure cgfunc_comp_gfunc (sF:cgfunc) (sF2:gFunc) :=
  @Gfunc (cgfunc_comp_bgfunc sF sF2)
  (cgfunc_comp_resp sF sF2).

Variables sF sF3:cgfunc.

Lemma cgfunc_comp_compatible : compatible (cgfunc_comp_gfunc sF sF3).
Proof. by move=> gT H G sHG; rewrite !cgfunc_compatible. Qed.

End CompatibleIdentitySubFunctorProps.

Definition cgfunc_comp_hgfunc (sF sF3:cgfunc)  :=
  @Cgfunc (cgfunc_comp_gfunc sF sF3) (cgfunc_comp_compatible sF sF3).

Section IdentitySubfunctorsExamples.

Implicit Types gT:finGroupType.

Lemma id_resp : resp (fun _ S => S).
Proof. by []. Qed.

Lemma id_compatible : compatible (fun _ S => S).
Proof. by []. Qed.

Canonical Structure bgfunc_id :=
  mkBasegFunc (fun gT G => groupP G%G)
  (fun gT G => subxx _)
  (aresp_of_resp id_resp).

Canonical Structure gfunc_id :=
  @Gfunc bgfunc_id id_resp.

Lemma triv_resp : resp (fun _ S => 1).
Proof. by move=> gT hT H f; rewrite morphim1. Qed.

Canonical Structure bgfunc_triv :=
  @mkBasegFunc (fun _ S => 1)
  (fun _ G => groupP 1%G)
  sub1G
  (aresp_of_resp triv_resp).

Canonical Structure gfunc_triv :=
  @Gfunc bgfunc_triv triv_resp.

Require Import center.

Lemma center_resp : resp (fun _ S => 'Z(S)).
Proof.
move=> gT hT H phi /=; apply:(subset_trans (morphimI _ _ _ )).
rewrite subsetI subsetIl /=; apply:(subset_trans (subsetIr (phi @* H) _) ).
exact:morphim_cent.
Qed.

Lemma center_hereditary : hereditary (fun _ S => 'Z(S)).
Proof.
move=> gT H G sHG; rewrite setIC /center setIA (setIidPl sHG) setIS //.
by rewrite (centsS sHG).
Qed.

Canonical Structure bgfunc_center :=
  @mkBasegFunc center 
  (fun gT G => groupP 'Z(G)%G) (fun gT G => @center_sub gT G)
  (aresp_of_resp center_resp).

Canonical Structure gfunc_center :=
  @Gfunc bgfunc_center center_resp.

Canonical Structure hgfunc_center :=
  @Hgfunc gfunc_center center_hereditary.

Require Import maximal.

Lemma Frattini_resp : resp (Frattini).
Proof. exact: gfunc_Phi. Qed.

Canonical Structure bgfunc_Frattini :=
  mkBasegFunc (fun gT G => groupP 'Phi(G)%G) (fun gT => @Phi_sub gT)
  (aresp_of_resp Frattini_resp).

Canonical Structure gfunc_Frattini :=
  @Gfunc bgfunc_Frattini Frattini_resp.

Lemma Fitting_hereditary : hereditary (fun _ G => 'F(G)).
Proof. by move=> gT H G; move/FittingS; rewrite setIC. Qed.

Canonical Structure bgfunc_Fitting :=
  mkBasegFunc (fun gT G => groupP 'F(G)%G)
           Fitting_sub
           (aresp_of_resp gfunc_Fitting).

Canonical Structure gfunc_Fitting :=
  @Gfunc bgfunc_Fitting gfunc_Fitting.

Canonical Structure hgfunc_Fitting :=
  @Hgfunc gfunc_Fitting Fitting_hereditary.

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

Lemma der_compatible : forall n, 
  compatible (fun gT G => derived_at G n).
Proof.
elim => [|n IH] gT H G sHG; first by rewrite !derg0.
by rewrite !dergSn commgSS ?IH.
Qed.

Canonical Structure bgfunc_der (n:nat) :=
  mkBasegFunc (fun gT (G:{group gT}) => der_group_set G n)
         (der_clos n)
         (aresp_of_resp (der_resp n)).

Canonical Structure gfunc_der (n:nat) :=
  @Gfunc (bgfunc_der n) (der_resp n).

Canonical Structure cgfunc_der (n:nat) :=
  @Cgfunc (gfunc_der n) (der_compatible n).

Lemma lcn_resp : forall n,
  resp (fun gT G => 'L_n(G)).
Proof.
elim=> [|n IH] gT hT H phi; first by rewrite !lcn0.
by rewrite !lcnSn morphimR ?lcn_sub0 // commSg ?IH.
Qed.

Lemma lcn_compatible : forall n,
  compatible (fun gT G => 'L_n(G)).
Proof.
elim=> [|n IH] gT H G sHG; first by rewrite !lcn0.
by rewrite !lcnSn commgSS ?IH.
Qed.

Canonical Structure bgfunc_lcn (n:nat) :=
  mkBasegFunc (fun gT (G:{group gT}) => lcn_group_set G n)
             (fun gT G => (lcn_sub0 G n))
             (aresp_of_resp (lcn_resp n)).

Canonical Structure gfunc_lcn (n:nat) :=
  @Gfunc (bgfunc_lcn n) (lcn_resp n).

Canonical Structure cgfunc_lcn (n:nat) :=
  @Cgfunc (gfunc_lcn n) (lcn_compatible n).

Lemma ucn_gfunc :  forall n,
  [/\ resp (fun _ G => 'Z_n(G)),
      hereditary (fun _ G => 'Z_n(G)) & 
      forall gT (G:{group gT}), 'Z_n(G) \subset G ].
Proof.
elim => [|n [Hresp Hhereditary Hsub]].
 by split=> [gT hT G phi|gT H G sHG| gT G];
 rewrite ?ucn0 ?morphim1 ?sub1G ?subsetIl //.
pose Zn := (mkhgfunc (fun _ G => ucn_group_set G n) Hsub Hresp Hhereditary).
pose ZSn:= [hgfunc of (appmod center Zn)].
split=> [gT hT G phi|gT H G sHG| gT G]; rewrite ucnSn.
- apply: (gfunc_resp ZSn).
- apply: (hgfunc_hereditary ZSn sHG).
- apply: (bgfunc_clos ZSn).
Qed.

Lemma ucn_resp : forall n, resp (fun _ G => 'Z_n(G)).
Proof. by move=> n; case:(ucn_gfunc n). Qed.

Lemma ucn_hereditary : forall n, hereditary (fun _ G => 'Z_n(G)).
Proof. by move=> n; case:(ucn_gfunc n). Qed.

Lemma ucn_clos : forall n gT (G:{group gT}), 'Z_n(G) \subset G.
Proof. by move=> n; case:(ucn_gfunc n). Qed.

Canonical Structure bgfunc_ucn (n:nat) :=
  mkBasegFunc (fun gT (G:{group gT}) => ucn_group_set G n)
  (ucn_clos n)
  (aresp_of_resp (ucn_resp n)).

Canonical Structure gfunc_ucn (n:nat) :=
  @Gfunc (bgfunc_ucn n) (ucn_resp n).

Canonical Structure hgfunc_ucn (n:nat) :=
  @Hgfunc (gfunc_ucn n) (ucn_hereditary n).

Require Import prime.
Require Import pgroups.

Lemma pcore_hereditary : forall (pi:nat_pred), hereditary (fun _ G => 'O_pi(G)).
Proof. by move=> pi gT H G; move/pcoreS; rewrite setIC. Qed.

Canonical Structure bgfunc_pcore (pi : nat_pred) :=
  mkBasegFunc (fun gT (G:{group gT}) => groupP [group of 'O_pi(G)])
  (pcore_sub pi)
  (aresp_of_resp (gfunc_pcore pi)).

Canonical Structure gfunc_pcore (pi:nat_pred) :=
  @Gfunc (bgfunc_pcore pi) (gfunc_pcore pi).

Canonical Structure dsfc_pcore (pi:nat_pred) :=
  @Hgfunc (gfunc_pcore pi) (pcore_hereditary pi).

Lemma Ohm_sub : forall i gT (G:{group gT}), 'Ohm_i(G) \subset G.
Proof. move=> gT i; exact: Ohm_sub. Qed.

Lemma Ohm_resp : forall i,
  resp (fun gT S => 'Ohm_i(S)).
Proof. move=> i G f; exact: gfunc_Ohm. Qed.

Lemma Ohm_compatible : forall i, compatible (fun gT S => 'Ohm_i(S)).
Proof.
move=> i gT H G Hsub; apply:genS; apply/subsetP=> x.
by rewrite !inE; move/andP => [Hx ->]; rewrite (subsetP Hsub _ Hx).
Qed.

Canonical Structure bgfunc_Ohm (i:nat) :=
  mkBasegFunc (fun gT (G:{group gT}) => groupP 'Ohm_i(G)%G)
  (Ohm_sub i)
  (aresp_of_resp (Ohm_resp i)).

Canonical Structure gfunc_Ohm (i:nat) :=
  @Gfunc (bgfunc_Ohm i) (Ohm_resp i).

Canonical Structure cgfunc_Ohm (i:nat) :=
  @Cgfunc (gfunc_Ohm i) (Ohm_compatible i).

Lemma Mho_sub : forall i gT (G:{group gT}), 'Mho^i(G) \subset G.
Proof. move=> i; exact: Mho_sub. Qed.

Lemma Mho_resp : forall i,
  resp (fun gT S => 'Mho^i(S)).
Proof. move=> i G f; exact: gfunc_Mho. Qed.

Lemma Mho_compatible : forall i,
  compatible (fun gT S => 'Mho^i(S)).
Proof. move=> i gT H G sHG; exact:MhoS. Qed.

Canonical Structure bgfunc_Mho (i:nat) :=
  mkBasegFunc (fun gT (G:{group gT}) => groupP 'Mho^i(G)%G)
  (Mho_sub i)
  (aresp_of_resp (Mho_resp i)).

Canonical Structure gfunc_Mho (i:nat) :=
  @Gfunc (bgfunc_Mho i) (Mho_resp i).

Canonical Structure cgfunc_Mho (i:nat) :=
  @Cgfunc (gfunc_Mho i) (Mho_compatible i).

End IdentitySubfunctorsExamples.

Unset Implicit Arguments.
