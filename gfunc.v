(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import ssrfun.
Require Import eqtype.
Require Import ssrnat.
Require Import fintype.
Require Import finset.
Require Import groups.
Require Import normal.
Require Import morphisms.
Require Import automorphism.

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

Definition cont (F : obmap) : Prop :=
  forall gT hT (G : {group gT}) (phi : {morphism G >-> hT}),
    phi @* (F _ G) \subset F _ (phi @* G).

(* Functoriality on grp whose arrows are restricted to isomorphisms *)

Definition acont (F : obmap) : Prop :=
  forall gT hT (G : {group gT}) (phi : {morphism G >-> hT}),
   'injm phi -> phi @* (F _ G) \subset F _ (phi @* G).

Lemma acont_of_cont : forall F, cont F -> acont F.
Proof. by move=> F H gT hT G phi Ha; apply:H. Qed.

(* Hereditary w.r.t. inclusion *)

Definition hereditary (F : obmap) : Prop :=
  forall gT (H G : {group gT}), H \subset G -> (F _ G) :&: H \subset (F _ H).

(* Modulo Application *)

Definition appmod (F1 F2 : obmap) :=
  fun gT G => coset (F2 gT G) @*^-1 (F1 _ (G / (F2 gT G))).

Definition app (F1 F2 : obmap) :=
  fun gT G => F1 _ (F2 gT G).

(* Strong functoriality (wrt domains) *)

Definition dcont (F : obmap) : Prop :=
  forall gT hT (G D : {group gT}) (phi : {morphism D >-> hT}),
    phi @* (F _ G) \subset F _ (phi @* G).

Lemma cont_of_dcont : forall F, dcont F -> cont F.
Proof. by move=> F contF gT hT G; exact: contF. Qed.

Lemma hereditary_of_dcont sF : dcont sF -> hereditary sF.
Proof.
move=> sF Hcont gT H G sHG; move: (Hcont _ _ G _ (idm_morphism H)) => /=.
rewrite -morphimIdom -[idm H @* G]morphimIdom !morphim_idm ?subsetIl //.
by rewrite (setIidPl sHG) setIC.
Qed.

(* Order-preserving w.r.t. inclusion *)

Definition monotonous (F : obmap) : Prop :=
  forall gT (H G : {group gT}), H \subset G -> (F _ H) \subset (F _ G).

End IdentitySubFunctorDefs.

Module FunctorDefs.

Implicit Type gT : finGroupType.

Structure bgFunc : Type := BGFunc {
  Fobj :> obmap;
  (* group preservation *)
  _ : forall gT (G : {group gT}), group_set (@Fobj gT G);
  (* submapping *)
  _ : forall gT (G : {group gT}), @Fobj gT G \subset G;
  (* functoriality condition *)
  _ : acont Fobj}.

Structure gFunc : Type := GFunc {
  F_bgFunc :> bgFunc ;
   _ : cont F_bgFunc}.

Structure hgFunc : Type := HGFunc {
  F_hgFunc :> gFunc;
   _ : hereditary F_hgFunc}.

Structure mgFunc : Type := MGFunc {
  F_mgFunc :> gFunc;
   _ : monotonous F_mgFunc}.

Definition mkBGFunc F rF gF sF := @BGFunc F gF sF rF.

Definition mkGFunc F rF gF sF :=
  @GFunc (@BGFunc F gF sF (acont_of_cont rF)) rF.

Definition repack_bgFunc bgF :=
let: BGFunc _ gp smap arp := bgF
  return {type of BGFunc for bgF} -> bgFunc in
  fun k => k gp smap arp.

Definition obmap_phant := phantom obmap.
Definition obmap_uni op1 op2 := obmap_phant op1 -> obmap_phant op2.

Definition repack_gFunc F (bgF : bgFunc) (gF : gFunc) :=
  fun (_ : obmap_uni bgF F) ( _ : obmap_uni gF F) obmapEq =>
    (let: GFunc _ rp := gF
      return {type of GFunc for gF} -> gFunc in
      fun k => k rp)
    (let: erefl in _ = gF := obmapEq
      return {type of GFunc for gF}
      in @GFunc bgF).

Definition repack_hgFunc F (gF : gFunc) (hgF : hgFunc) :=
  fun (_ : obmap_uni gF F) ( _ : obmap_uni hgF F) obmapEq =>
    (let: HGFunc _ hp := hgF
      return {type of HGFunc for hgF} -> hgFunc in
      fun k => k hp)
    (let: erefl in _ = hgF := obmapEq
      return {type of HGFunc for hgF}
      in @HGFunc gF).

Definition repack_mgFunc F (gF : gFunc) (mgF : mgFunc) :=
  fun (_ : obmap_uni gF F) ( _ : obmap_uni mgF F) obmapEq =>
    (let: MGFunc _ cp := mgF
      return {type of MGFunc for mgF} -> mgFunc in
      fun k => k cp)
    (let: erefl in _ = mgF := obmapEq
      return {type of MGFunc for mgF}
      in @MGFunc gF).

End FunctorDefs.

Notation "[ 'bgFunc' 'of' F ]" :=
  (FunctorDefs.repack_bgFunc (fun bgP => @FunctorDefs.BGFunc F bgP))
  (at level 0, format"[ 'bgFunc'  'of'  F ]") : form_scope.

Notation "[ 'bgFunc' 'by' sF & ! rF ]" :=
  (FunctorDefs.mkBGFunc rF (fun gT G => groupP _) sF)
  (at level 0, format "[ 'bgFunc'  'by'  sF  &  ! rF ]") : form_scope.

Notation "[ 'bgFunc' 'by' sF & rF ]" :=
  [bgFunc by sF & !acont_of_cont rF]
  (at level 0, format "[ 'bgFunc'  'by'  sF  &  rF ]") : form_scope.

Notation "[ 'gFunc' 'by' sF & rF ]" :=
  (FunctorDefs.mkGFunc rF (fun gT G => groupP _) sF)
  (at level 0, format "[ 'gFunc'  'by'  sF  &  rF ]") : form_scope.

Notation "[ 'gFunc' 'of' F ]" :=
  (@FunctorDefs.repack_gFunc F _ _ id id (erefl _))
  (at level 0, format "[ 'gFunc'  'of'  F ]") : form_scope.

Notation "[ 'hgFunc' 'of' F ]" :=
  (@FunctorDefs.repack_hgFunc F _ _ id id (erefl _))
  (at level 0, format "[ 'hgFunc' 'of'  F ]") : form_scope.

Notation "[ 'mgFunc' 'of' F ]" :=
  (@FunctorDefs.repack_mgFunc F _ _ id id (erefl _))
  (at level 0, format "[ 'mgFunc' 'of'  F ]") : form_scope.


Notation bgFunc := FunctorDefs.bgFunc.
Notation gFunc := FunctorDefs.gFunc.
Notation hgFunc := FunctorDefs.hgFunc.
Notation mgFunc := FunctorDefs.mgFunc.

Notation BGFunc := FunctorDefs.BGFunc.
Notation GFunc := FunctorDefs.GFunc.
Notation HGFunc := FunctorDefs.HGFunc.
Notation MGFunc := FunctorDefs.MGFunc.

Section BgGroup.
(* Preliminary : group structure *)
Variables (sF : bgFunc) (gT : finGroupType) (H : {group gT}).
Lemma bgFunc_groupset : group_set (sF _ H). Proof. by case: sF. Qed.
Canonical Structure bgFunc_group := Group bgFunc_groupset.
End BgGroup.

Section BaseIdentitySubFunctorProps.

Implicit Types gT hT : finGroupType.
Variable sF : bgFunc.

Lemma bgFunc_clos : forall gT (H : {group gT}), sF _ H \subset H.
Proof. by case sF. Qed.

Lemma bgFunc_acont : acont sF.
Proof. by case sF. Qed.

Lemma bgFunc_char : forall gT (G : {group gT}), sF _ G \char G.
Proof.
move=> gT G; apply/andP; split => //; first by apply: bgFunc_clos.
apply/forallP=> f; apply/implyP=> Af; rewrite -{2}(im_autm Af) -(autmE Af).
by rewrite -morphimEsub ?bgFunc_clos ?bgFunc_acont ?injm_autm.
Qed.

Lemma bgFunc_norm : forall gT (G : {group gT}), G \subset 'N(sF _ G).
Proof. by move=> *; rewrite char_norm ?bgFunc_char. Qed.

(* independent from the group preservation requirement*)
Lemma bgFunc_gen_norm : forall gT (G : {group gT}),
  << sF _ G >> \subset 'N(sF _ G).
Proof.
move=> gT G; apply/normsP=> x Hx; move/normsP: (bgFunc_norm G); apply.
by move: ((subsetP (genS (bgFunc_clos G))) _ Hx); rewrite genGid.
Qed.

Lemma bgFunc_normal : forall gT (G : {group gT}), sF _ G <| G.
Proof.  by move=> *; rewrite char_normal ?bgFunc_char. Qed.

Lemma bgFunc_ascont_sub :
   forall gT hT (H G : {group gT}) (f : {morphism G >-> hT}),
  'injm f -> H \subset G -> f @* (sF _ H) \subset sF _ (f @* H).
Proof.
move=> gT hT H G f injf sHG; apply/eqP; rewrite -(setIidPr (bgFunc_clos H)).
by rewrite-{3}(setIid H) -!(morphim_restrm sHG) bgFunc_acont // injm_restrm.
Qed.

Lemma bgFunc_ascont :
 forall gT hT (H G : {group gT}) (f : {morphism G >-> hT}),
 'injm f -> H \subset G -> f @* (sF _ H) = sF _ (f @* H).
Proof.
move=> gT hT H G f injf sHG.
apply/eqP; rewrite eqEsubset bgFunc_ascont_sub //=.
rewrite -{2}(morphim_invm injf sHG) -[f @* sF _ _](morphpre_invm injf).
have sFtr := subset_trans (bgFunc_clos _).
by rewrite -sub_morphim_pre (bgFunc_ascont_sub, sFtr) ?morphimS ?injm_invm.
Qed.

Lemma bgFunc_nker_cont :
  forall gT hT (H G : {group gT}) (f : {morphism G >-> hT}),
  'ker f = 1 -> H \subset G -> f @* (sF _ H) = sF _ (f @* H).
Proof. by move=> gT hT H G f; move/trivgP => /=; apply: bgFunc_ascont. Qed.

Lemma bgFunc_isom :
  forall gT hT (H G : {group gT}) (R : {group hT}) (f : {morphism G >-> hT}),
  H \subset G -> isom H R f -> isom (sF _ H) (sF _ R) f.
Proof.
move=> gT rT H G R f; case/(restrmP f)=> g [gf _ _ _]; rewrite -{f}gf.
by case/isomP=> injg <-; rewrite sub_isom ?bgFunc_clos ?bgFunc_ascont.
Qed.

Lemma bgFunc_isog : forall gT hT (G : {group gT}) (R : {group hT}),
  G \isog R -> sF _ G \isog sF _ R.
Proof.
move=> gT rT D R; case/isogP=> f *.
apply: (isom_isog f) => //; first by apply: bgFunc_clos.
apply: bgFunc_isom => //; exact/isomP.
Qed.

End BaseIdentitySubFunctorProps.

Section IdentitySubFunctorProps.

Implicit Types gT hT : finGroupType.
Variable sF : gFunc.

Lemma gFunc_cont : cont sF.
Proof. by case sF. Qed.

Lemma morphim_sFunctor : forall gT hT (G D : {group gT})
  (f : {morphism D >-> hT}),
  G \subset D -> f @* (sF _ G) \subset sF _ (f @* G).
Proof.
move=> gT hT G D f sGD; rewrite -(setIidPr (bgFunc_clos sF G)).
by rewrite  -{3}(setIid G) -!(morphim_restrm sGD) gFunc_cont.
Qed.

Lemma injm_sFunctor :
  forall gT hT (G D : {group gT}) (f : {morphism D >-> hT}),
  'injm f -> G \subset D -> f @* (sF _ G) = sF _ (f @* G).
Proof. exact: bgFunc_ascont. Qed.

Lemma isom_sFunctor :
  forall gT hT (D G : {group gT}) (R : {group hT}) (f : {morphism D >-> hT}),
  G \subset D -> isom G R f -> isom (sF _ G) (sF _ R) f.
Proof. move=> gT hT D G; exact: bgFunc_isom. Qed.

Lemma isog_sFunctor : forall gT hT (D : {group gT}) (R : {group hT}),
  D \isog R -> sF _ D \isog sF _ R.
Proof. exact: bgFunc_isog. Qed.

End IdentitySubFunctorProps.

Section HereditaryIdentitySubFunctorProps.

Implicit Types gT hT : finGroupType.

Section HereditaryIdBaseProps.

Variable sF : hgFunc.

Lemma hgFunc_cont : cont sF.
Proof. by apply: gFunc_cont. Qed.

Lemma hgFunc_hereditary : hereditary sF.
Proof. by case sF. Qed.

Lemma hgFunc_imsetI : forall gT (G H : {group gT}),
  sF _ G :&: H = sF _ G :&: sF _ (G :&: H).
Proof.
move=> gT G H; rewrite -{1}(setIidPr (bgFunc_clos sF G)) [G :&: _]setIC -setIA.
move/setIidPr: (hgFunc_hereditary (subsetIl G H)) <-.
by rewrite setIC -setIA (setIidPr (bgFunc_clos sF (G:&: H))).
Qed.

Lemma hgFunc_morphim : dcont sF.
Proof.
move=> gT hT G D f.
rewrite -morphimIdom -(setIidPl (bgFunc_clos sF G)) setICA.
apply: (subset_trans (morphimS f (hgFunc_hereditary (subsetIr D G)))).
apply: (subset_trans (morphim_sFunctor sF _ _ )); last by rewrite morphimIdom.
exact: subsetIl.
Qed.

Lemma hereditary_idem : forall (gT:finGroupType) (G:{group gT}),
  (app sF sF) _ G  = sF _ G.
Proof.
move=> gT G /=; apply/eqP; rewrite eqEsubset bgFunc_clos.
by move/hgFunc_hereditary: (bgFunc_clos sF G); rewrite setIid /=.
Qed.

End HereditaryIdBaseProps.

Section HereditaryIdentitySFComp.

Variables (sF : hgFunc) (sF2 : gFunc).

(* independent from the group preservation requirement *)
Lemma hgFunc_comp_clos : forall gT (G : {group gT}),
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

Lemma hgFunc_comp_cont : cont (appmod sF sF2).
Proof.
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
  factm sFK sGG @* (H / sF2 _ G) = f @* H / sF2 _ (f @* G).
- rewrite -2?im_fact ?hgFunc_comp_clos ?bgFunc_clos //.
  by rewrite hgFunc_comp_quo morphim_sFunctor /= ?morphim_restrm ?setIid //.
  by rewrite -{1}kF morphpreS ?sub1G.
move=> H sFH sHG; rewrite -(morphimIdom _ (H / _)) /= {2}morphim_restrm setIid.
rewrite -morphimIG ?kF // -(morphim_restrm sDF) morphim_factm morphim_restrm.
by rewrite morphim_comp -quotientE morphimIdom.
Qed.

Canonical Structure hgFunc_comp_bgFunc :=
  [bgFunc by hgFunc_comp_clos & hgFunc_comp_cont].

Canonical Structure hgFunc_comp_gFunc := GFunc hgFunc_comp_cont.

End HereditaryIdentitySFComp.

Variables sF sF3 : hgFunc.

Lemma hgFunc_comp_hereditary : hereditary (appmod sF sF3).
Proof.
move=> gT H G sHG; set FGH := _ :&: H; have nF3H := bgFunc_norm sF3 H.
rewrite -sub_quotient_pre; last exact: subset_trans (subsetIr _ _) _.
pose rH := restrm nF3H (coset (sF3 _ H)); pose rHM := [morphism of rH].
have rnorm_simpl: rHM @* H = H / sF3 _ H by rewrite morphim_restrm setIid.
have nF3G := subset_trans sHG (bgFunc_norm sF3 _).
pose rG := restrm nF3G (coset (sF3 _ G)); pose rGM := [morphism of rG].
have sqKfK: 'ker rGM \subset 'ker rHM.
  rewrite !ker_restrm !ker_coset (setIidPr (bgFunc_clos sF3 _)) setIC /=.
  exact: (hgFunc_hereditary sF3).
have sHH := subxx H; rewrite -rnorm_simpl /= -(morphim_factm sqKfK sHH) /=.
apply: subset_trans (gFunc_cont sF _); rewrite /= {2}morphim_restrm setIid /=.
apply: subset_trans (morphimS _ (hgFunc_hereditary _ (quotientS _ sHG))) => /=.
have ->: FGH / _ = restrm nF3H (coset _) @* FGH.
  by rewrite morphim_restrm setICA setIid.
rewrite -(morphim_factm sqKfK sHH) morphimS //= morphim_restrm -quotientE.
by rewrite setICA setIid (subset_trans (quotientI _ _ _)) // cosetpreK.
Qed.

Canonical Structure hgFunc_comp_hgFunc := HGFunc hgFunc_comp_hereditary.

End HereditaryIdentitySubFunctorProps.

Section MonotonousIdentitySubFunctorProps.

Implicit Types gT hT : finGroupType.

Section MonotonousIdBaseProps.

Variable sF : mgFunc.

Lemma mgFunc_cont : cont sF.
Proof. exact: gFunc_cont. Qed.

Lemma mgFunc_monotonous : monotonous sF.
Proof. by case sF. Qed.

End MonotonousIdBaseProps.

Section MonotonousIdentitySFComp.

Variables (sF : mgFunc) (sF2 : gFunc).

(* independent from the group preservation requirement *)
Lemma mgFunc_comp_clos : forall gT (G : {group gT}),
  (app sF sF2) gT G \subset G.
Proof.
by move=> gT G; rewrite (subset_trans (bgFunc_clos _ _)) ?bgFunc_clos.
Qed.

Lemma mgFunc_comp_cont : cont (app sF sF2).
Proof.
move=> gT hT G phi.
rewrite (subset_trans (morphim_sFunctor _ _ (bgFunc_clos _ _))) //.
by rewrite (subset_trans (mgFunc_monotonous sF (gFunc_cont sF2 phi))).
Qed.

Canonical Structure mgFunc_comp_bgFunc :=
  [bgFunc by mgFunc_comp_clos & mgFunc_comp_cont].

Canonical Structure mgFunc_comp_gFunc := GFunc mgFunc_comp_cont.

End MonotonousIdentitySFComp.

Variables sF sF3 : mgFunc.

Lemma mgFunc_comp_monotonous : monotonous (mgFunc_comp_gFunc sF sF3).
Proof. by move=> gT H G sHG; rewrite !mgFunc_monotonous. Qed.

Definition mgFunc_comp_hgFunc := MGFunc mgFunc_comp_monotonous.

End MonotonousIdentitySubFunctorProps.

Section IdentitySubFunctorsExamples.

Implicit Types gT : finGroupType.

Definition id_sF gT := @id {set gT}.

Lemma id_cont : cont id_sF.
Proof. by []. Qed.

Lemma id_monotonous : monotonous id_sF.
Proof. by []. Qed.

Canonical Structure bgFunc_id := [bgFunc by fun _ _ => subxx _ & id_cont].
Canonical Structure gFunc_id := GFunc id_cont.
Canonical Structure mgFunc_id := MGFunc id_monotonous.

Definition triv_sF gT of {set gT} := [1 gT].

Lemma triv_cont : cont triv_sF.
Proof. by move=> gT hT H f; rewrite morphim1. Qed.

Canonical Structure bgFunc_triv := [bgFunc by sub1G & triv_cont].
Canonical Structure gFunc_triv := GFunc triv_cont.
Canonical Structure hgFunc_triv :=
  @HGFunc gFunc_triv (fun gT G _ _ => subsetIl 1 G).

End IdentitySubFunctorsExamples.

Unset Implicit Arguments.
