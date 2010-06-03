(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype fintype finset groups normal.
Require Import normal morphisms automorphism bigops gprod.

Import GroupScope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section IdentitySubFunctorDefs.

Implicit Types gT hT : finGroupType.

(* An object mapping on sets *)

Definition obmap : Type := forall gT, {set gT} -> {set gT}.

Identity Coercion fun_of_obmap : obmap >-> Funclass.

(* General functoriality, a.k.a continuity of the object mapping *)

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

(* TOFIX: this should ultimately use the Idempotent Property defined below *)
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

Section Torsion.

Implicit Types gT hT: finGroupType.

(* Orthogonality property*)
Definition trivlsed gT (B : {group gT}) hT (C : {group hT}) :=
  forall f : {morphism B >-> hT},
  f @* B \subset C -> f @* B :=: 1%G.

Definition GClass := forall gT (B: {group gT}), Prop.

Identity Coercion fun_of_obsel : GClass >-> Funclass.

Implicit Types P Pa Pb : GClass.

(* Closure properties*)

Definition cisom P := forall gT (G : {group gT}) hT (H : {group hT}),
  isog G H -> P _ G -> P _ H.

Definition csub P := forall gT (G H : {group gT}),
  H \subset G -> P _ G -> P _ H.

Definition cquo P := forall gT (G H : {group gT}),
  H <| G -> P _ G -> P _ (G / H)%G.

Lemma cquoisom1 P : cquo P -> cisom P ->
  (forall gT (G:{group gT}), P _ G -> forall hT, P _ (one_group hT)).
Proof. 
move=> P qP iP gT G PG hT; have : P (coset_groupType G) 1%G.
  move:(trivg_quotient G); move/group_inj=><-.
  by apply:(qP _ _ _ (normal_refl _) PG).
apply:iP; rewrite isog_symr //; have:= (quotient1 G); move/group_inj=><-.
apply: (@isog_trans _ _ _ _ (one_group gT)); first by apply: trivial_isog.
apply: (isom_isog _ _ (quotient_isom (sub1G 'N(G)) (setIidPl (sub1G G)))).
by apply:subxx.
Qed.

Definition cex P := forall gT (G H : {group gT}),
  H <| G -> P _ H -> P _ (G / H)%G -> P _ G.

Definition cjoin P := forall gT (H G : {group gT}),
  P _ H -> P _ G -> P _ (H <*> G)%G.

(* TOFIX : this is a puny excuse for being 'closed by direct product' *)
Definition csetX P := forall gT (G : {group gT}) hT (H : {group hT}),
  P _ G -> P _ H -> P _ [group of setX G H].

(* Order relations on group classes *)

(* NB : lP has to relate polymorphically quantified classes,
   otherwise a finGroupType and a quotient type of it can't be in the same class
   This is necessary as soon as ClB below. *)

Definition lP Pa Pb := forall gT B, Pa gT B -> Pb _ B.

Definition eP Pa Pb := forall gT B, Pa gT B <-> Pb _ B.

(* a torsion theory is a couple of classes related by the two operators below.

   A formal definition would correspond to the hypotheses of sections
   EquivalenceTheorem2 & EquivalenceTheorem3.*)

Definition Rfun P hT (C : {group hT}) :=
  lP P (fun gT B => trivlsed B C) (* : forall gT, Prop ~= bool*).

Definition Lfun P gT (B : {group gT}) :=
  lP P (trivlsed B).

Lemma RightLeft : forall (Bs Cs : GClass),
   lP Cs (Rfun Bs) <-> lP Bs (Lfun Cs).
Proof.
by move=> Bs Cs; split; move=> H gT B HB hT C HC; apply H.
Qed.

(* TOFIX : those should be moved to section IdentitySubFunctorDefs *)
Definition Idemp (F : obmap) := forall gT (G : {group gT}), F _ (F _ G) = F _ G.
Definition radical (F : obmap) := forall gT (G : {group gT}),
  F _ (G / (F _ G)) = 1.

Section EquivalenceTheorem1.
(* An indempotent radical generated by a torsion theory*)

Variable T : mgFunc.
Hypothesis Hid : Idemp T.
Hypothesis Hrad : radical T.

Local Notation Bs := 
  (fun (fT:finGroupType) (B : {group fT}) => T _ B = B).
Local Notation Cs := 
  (fun (fT:finGroupType) (C : {group fT}) => T _ C = 1).

(* NB : we need monotonicity (alone) here *)
Lemma BCl : lP Bs (Lfun Cs).
Proof.
move=> gT B /= HB hT C /= HC; move=> f; rewrite /= -{6}HB.
move/(mgFunc_monotonous T)=>HTB; apply/trivgP; rewrite -HC.
by apply:subset_trans HTB; apply: mgFunc_cont.
Qed.

Lemma CBr : lP Cs (Rfun Bs).
Proof. by apply/RightLeft; apply:BCl. Qed.

(* NB : radicality alone needed*)
Lemma ClB : lP (Lfun Cs) Bs.
Proof.
move=> gT B2; rewrite /Lfun /lP; move/(_ _ (B2 / T _ B2)%G); move/(_ (Hrad B2)).
pose f:= [morphism of restrm (bgFunc_norm T B2) (coset (T _ B2))].
move/(_ f); rewrite /= /restrm quotientE=> H.
have e : B2 \subset 'ker (coset (T _ B2)).
  rewrite ker_trivg_morphim bgFunc_norm; apply/trivgP.
  by apply: val_inj; rewrite /= -H !morphim_restrm !morphimE setIid.
by apply/eqP; rewrite eqEsubset bgFunc_clos; rewrite ker_coset in e.
Qed.

(* NB : idempotence alone needed *)
Lemma BrC : lP (Rfun Bs) Cs.
Proof.
move=> hT C2; rewrite /Rfun /lP; move/(_ _ [group of T _ C2])=>/=.
move/(_ (Hid C2)); pose f := [morphism of restrm (bgFunc_clos T C2) (idm C2)].
move/(_ f); rewrite /= /restrm morphim_restrm morphim_idm setIid bgFunc_clos //.
by apply.
Qed.

Lemma eBC : eP Bs (Lfun Cs) /\ eP Cs (Rfun Bs).
Proof.
by split; move=> gT B; split; [apply BCl|apply ClB|apply CBr|apply BrC].
Qed.

End EquivalenceTheorem1.

Section EquivalenceTheorem2.

(* Here we get closure properties from Lfun properties.
   Those will ultimately allow us to build a corresponding 
   (not necessarily idempotent) radical
*)

Variables Bs Cs : forall gT (_:{group gT}), Prop.
Hypothesis eBC : eP Bs (Lfun Cs).

Lemma hBCl : lP Bs (Lfun Cs).
Proof. by move=> gT B; rewrite (eBC B). Qed.

Lemma hClB : lP (Lfun Cs) Bs.
Proof. by move=> gT B; rewrite (eBC B). Qed.

Lemma cisomB : cisom Bs.
Proof.
move=> gT B hT C; move/isogP => [f Hfinj Hfim]; move/hBCl=>HB.
apply:hClB=> fT Y HY g Hgim; move : (injmK Hfinj (subxx _)).
rewrite Hfim=> Hfpre; have:= (comp_morphM g (f:=f)); rewrite Hfpre => H.
pose gof := Morphism H; move: (HB _ _ HY gof).
by rewrite morphimE imset_comp -morphimE Hfim -{2 4}(setIid C) -morphimE;
move/(_ Hgim).
Qed.

Lemma cquoB : cquo Bs.
Proof.
move=> gT X H Hs; move/hBCl=>HX; apply:hClB=> hT C2 HC2 g2 Hg2.
pose f:= [morphism of restrm (normal_sub Hs) (coset H)].
have:= (comp_morphM g2 (f:=f)); rewrite /restrm (quotientGK Hs)=>Hm.
pose g:= Morphism Hm; move:(HX _ _ HC2 g); rewrite morphimE imset_comp.
rewrite setIid -(setIidPr (normal_norm Hs)) -morphimE /= /restrm -quotientE.
by rewrite -{2 4}(setIid (X / H)) -morphimE; move/(_ Hg2).
Qed.

Lemma cexB : cex Bs.
Proof.
move=> gT M B Hs; move/hBCl=>HB; move/hBCl=> Hqu; apply:hClB=> hT C3 HC3 f3 Hf3.
move: (comp_morphM f3 (f:= [morphism of idm B])).
rewrite morphpre_idm (setIidPl (normal_sub Hs))=>Hf3i; pose f:= Morphism Hf3i.
move: (HB _ _ HC3 f); rewrite morphimE imset_comp -morphimE.
rewrite morphim_idm ?subxx // -{1 2}(setIidPr (normal_sub Hs)) -morphimE.
move/(_ (subset_trans (morphimS f3 (normal_sub Hs)) Hf3))=>Hf3B.
move/trivgP:(Hf3B); move/(conj (normal_sub Hs)); move/andP.
rewrite -ker_trivg_morphim=> HBker.
have Hinj : 'injm (coset (f3 @* B)) by rewrite Hf3B; apply:coset1_injm.
move: (morphM [morphism of (invm Hinj) \o (quotm f3 Hs)])=>/=.
rewrite -quotientE morphpre_quotm {1}Hf3B norm1 morphpreT=>Hq.
pose qfq := Morphism Hq; move:(Hqu _ _ HC3 qfq).
rewrite morphimE imset_comp -morphimE morphim_quotm quotientE.
have:= (subsetT (f3 @* M)); rewrite -norm1 -[1]/(gval _) -{1}Hf3B =>Hm.
rewrite -(setIidPr (morphimS _  Hm)) -morphimE morphim_invm ?Hm //.
by move/(_ Hf3).
Qed.

Lemma cjoinB : cjoin Bs.
Proof.
move=> Pb G H BH BG; apply: hClB=> hT C5 HC5 f5.
rewrite morphim_gen ?subset_gen // gen_subG {1}morphimU subUset.
rewrite 2!morphimE (setIidPr (mulgen_subl _ _)) (setIidPr (mulgen_subr _ _)).
move/andP=> [Hf5G Hf5H]; apply/trivgP; rewrite gen_subG.
rewrite sub_morphim_pre ?subset_gen -?sub_morphim_pre ?sub_gen //.
move: (morphM [morphism of f5 \o (idm G)]).
move: (morphM [morphism of f5 \o (idm H)]). 
rewrite {1}[idm_morphism G @*^-1 _]morphpre_idm.
rewrite {1}[idm_morphism H @*^-1 _]morphpre_idm.
rewrite (setIidPl (mulgen_subl _ _)) (setIidPl (mulgen_subr _ _)) =>Hf Hg.
pose f:= Morphism Hf; pose g:= Morphism Hg.
move: (hBCl BH HC5) (hBCl BG HC5)=> HtG HtH; move: (HtG g) (HtH f).
rewrite 2!morphimE 2!imset_comp -!morphimE !morphim_idm ?subxx // morphimU.
rewrite subUset !morphimE (setIidPr (mulgen_subl _ _)). 
rewrite (setIidPr (mulgen_subr _ _)); move/(_ Hf5G)=>->; move/(_ Hf5H)=>->.
by rewrite subxx.
Qed.

(*
TOFIX : add closure wrt direct sum
*)

End EquivalenceTheorem2.

Section EquivalenceTheorem3.

(* Closure properties from Rfun properties.
   Those will ultimately allow us to build a corresponding 
   (not necessarily radical) idempotent pre-radical
*)

Variables Bs Cs : forall gT (_:{group gT}), Prop.
Hypothesis eCB : eP Cs (Rfun Bs).

(* This is done to syntactically isolate what I use, of course views apply
   bidirectionnaly
*)

Lemma hCBr : lP Cs (Rfun Bs).
Proof. by move=> gT C; rewrite (eCB C). Qed.

Lemma hBrC : lP (Rfun Bs) Cs.
Proof. by move=> gT C; rewrite (eCB C). Qed.

Lemma cisomC : cisom Cs.
Proof.
move=> gT G hT H; case/isogP=> f Hfinj Hfim; move/hCBr=>HC.
apply:hBrC=> fT Y HY g Hgim; pose h := (invm Hfinj)\o g.
have mH: morphic Y h.
  move:Hgim; rewrite (sub_morphim_pre _ _ (subxx _)); move/subsetP=>Hgim.
  have:= (comp_morphM [morphism of invm Hfinj] (f:=g)); rewrite /= Hfim=> Hm.
  by apply/morphicP; move=> x y; move/Hgim=> Hx; move/Hgim=>Hy; apply:Hm.
rewrite -Hfim in Hgim.
apply: (injm_morphim_inj (injm_invm Hfinj) Hgim (sub1G _)).
pose invfog := Morphism (morphicP mH); move: (HC _ _ HY invfog).
rewrite morphimE imset_comp -morphimE -{1 2}(setIidPr Hgim) -morphimE.
move/(morphimS [morphism of invm Hfinj]) : Hgim =>/=.
by rewrite morphim1 (morphim_invm _ (subxx _))=>Hi; move/(_ Hi).
Qed.

Lemma csubC : csub Cs.
Proof.
move=> hT X H Hs; move/hCBr=> HtBrG; apply:hBrC=> gT B2 HB2 f2 Hf2.
pose h:= (idm H) \o f2; have mH : morphic B2 h.
  rewrite (sub_morphim_pre _ _ (subxx _)) in Hf2; move/subsetP:Hf2=>Hf2.
  apply/morphicP; have := (morphM [morphism of h])=> Hm x y; move/Hf2=>Hx.
  by move/Hf2=>Hy; apply:Hm.
pose iof := Morphism (morphicP mH); move: (HtBrG _ _ HB2 iof); rewrite morphimE.
rewrite imset_comp -morphimE -{1 2}(setIidPr Hf2) -morphimE morphim_idm ?Hf2 //.
by move/(_ (subset_trans Hf2 Hs)).
Qed.

Lemma cexC : cex Cs.
Proof.
move=> hT M C Hs; move/hCBr=>HB; move/hCBr=> Hqu; apply:hBrC=> gT B3 HB3 f3 Hf3.
pose h:= (restrm (normal_norm Hs) (coset C)) \o f3.
have mH: morphic B3 h.
  apply/morphicP; move: (morphM [morphism of h])=> Hm x y.
  rewrite (sub_morphim_pre _ _ (subxx _)) in Hf3; move/subsetP:Hf3=>Hf3.
  by move/Hf3=> Hx; move/Hf3=> Hy; apply:Hm.
(* TOFIX : don't know why the simpl is mandatory here*)
move/morphicP: mH=> /= mH; pose hm := Morphism mH.
move: (Hqu _ _ HB3 hm); rewrite morphimE imset_comp -morphimE /restrm.
rewrite -{1 2}(setIidPr (subset_trans Hf3 (normal_norm Hs))) -morphimE.
rewrite -quotientE; move/(_ (quotientS _ Hf3)).
move/trivgP; move/(conj (subset_trans Hf3 (normal_norm Hs))); move/andP.
by rewrite -ker_trivg_morphim ker_coset; move/(HB _ _ HB3 f3).
Qed.

(* TOFIX : according to what is inferred in this lemma, the structures on 
   [eta fst], [eta snd] declared in gprod.v don't work so well*)
Lemma csetXP : csetX Cs.
Proof.
move=> gT G hT H; move/hCBr=> HG; move/hCBr=> HH; apply hBrC=> fT B4 HB4 g4 Hg4.
pose p1g4 := restrm (subsetT (setX G H)) [morphism of fun x => x.1] \o g4.
pose p2g4 := restrm (subsetT (setX G H)) [morphism of fun x => x.2] \o g4.
have Hp1g4 : morphic B4 p1g4.
  apply/morphicP=> x y;  move: Hg4; rewrite (sub_morphim_pre _ _ (subxx _)).
  move/subsetP=> Hs; move/Hs=> Hx; move/Hs=>Hy.
  by apply:(morphM [morphism of p1g4]).
have Hp2g4: morphic B4 p2g4.
  apply/morphicP=> x y;  move: Hg4; rewrite (sub_morphim_pre _ _ (subxx _)).
  move/subsetP=> Hs; move/Hs=> Hx; move/Hs=>Hy.
  by apply: (morphM [morphism of p2g4]).
pose mp1g4:= Morphism (morphicP Hp1g4); pose mp2g4 := Morphism (morphicP Hp2g4).
move: (HG _ _ HB4 mp1g4) (HH _ _ HB4 mp2g4).
rewrite morphimE imset_comp -morphimE /restrm -{1}(setTI (g4 @* B4)) -morphimE.
move: (morphimS [morphism of restrm (subsetT (setX G H)) (fun x => x.1)] Hg4).
move: (morphimS [morphism of restrm (subsetT (setX G H)) (fun x => x.2)] Hg4).
rewrite morphim_fstX morphim_sndX /restrm=> Hm2 Hm1.
move/(_ Hm1)=>H1; rewrite morphimE imset_comp -morphimE /restrm.
rewrite  -{1}(setTI (g4 @* B4)) -morphimE; move/(_ Hm2)=> H2.
apply/trivgP; apply/subsetP; case=>[x1 x2 Hx12].
move: (mem_imset [morphism of fun x =>x.1] Hx12); rewrite H1 /=; move/set1P=>->.
move: (mem_imset [morphism of fun x =>x.2] Hx12); rewrite H2 /=; move/set1P=>->.
by apply/set1P.
Qed.

End EquivalenceTheorem3.


Section EquivalenceTheorem4.

(* Here, as well as in the next section we define a (pre-)radical from
 closure properties.

 Since our assumptions in the last section are minimal, the ones in this
 section might surprise. Notice that in fact, we simply require closure
 properties on the class we study (here, Bs), and computational definition
 on the other (C = B^r).

*)

Variables (Bs Cs : GClass). 
Hypothesis  eCB : eP Cs (Rfun Bs).

(* This is done to syntactically isolate what I use, of course views apply
   bidirectionnaly
*)

Lemma hCBr' : lP Cs (Rfun Bs).
Proof. by move=> gT C; rewrite (eCB C). Qed.

Lemma hBrC' : lP (Rfun Bs) Cs.
Proof. by move=> gT C; rewrite (eCB C). Qed.

Hypothesis cquoB : cquo Bs.
Hypothesis cisomB : cisom Bs.
Hypothesis cexB : cex Bs.
Hypothesis cjoinB : cjoin Bs.

Variables Bbool Cbool : forall gT, pred {group gT}.
Hypothesis reflectB : forall gT (G:{group gT}), reflect (Bs G) (Bbool G).

(***************************************************************************)
(* This implies our interpretation of class Bs in terms of a functor will  *)
(* only be valid when Bs is not empty. We will have to carry around a      *)
(* non-emptyness hypothesis, but this is actually better than the          *)
(* alternative, which is to have a T that does not always carry a group    *)
(* structure (being sometimes empty) - hence one that wouldn't even fit our*)
(* bgFunc structure.                                                       *)
(***************************************************************************)

Definition T gT (G:{set gT}) := 
  \big[mulGen/1%G]_(H: {group gT} | (@Bbool _ H) && (H \subset G)) H.

(* The following is trivial, but important to notice *)
Lemma sub1TG : forall gT (G:{group gT}), 1%G \subset T G.
Proof. by move=> gT G; apply: sub1G. Qed.

Lemma noBstrivT : (forall gT (H:{group gT}), Bs H -> False) ->
  (forall hT (H:{group hT}), T H :=: 1).
Proof.
move=> noBs hT H; apply/trivgP; rewrite bigprodGE gen_subG.
by apply/bigcupsP=> G; case/andP; move/reflectB; move/noBs.
Qed.

Lemma T_B : forall hT (H:{group hT}), Bs H -> 
  forall gT (G:{group gT}), Bs (T G).
Proof.
move=> hT H BsH gT G.
apply: big_prop; last by move=>H0; case/andP => BbH0 _; apply/reflectB.
  apply: (cquoisom1 cquoB cisomB BsH).
apply: cjoinB.
Qed.

Lemma T_sub : forall gT (G:{group gT}), T G \subset G.
Proof.
by move=>gT G; rewrite bigprodGE gen_subG; apply/bigcupsP=> H; case/andP.
Qed.

Lemma T_cont : cont T.
Proof.
move=> gT hT G f; have sUG:(\bigcup_(H | Bbool H && (H \subset G)) H \subset G).
 by apply/bigcupsP=> H; case/andP.
rewrite bigprodGE morphim_gen ?sUG ?gen_subG ?sub_morphim_pre ?sUG //.
apply/bigcupsP=> H; case/andP=> BbH sHG; rewrite -sub_morphim_pre ?sub_gen //.
rewrite -[f @* H]/(gval _); rewrite bigprodGE sub_gen //; apply:bigcup_sup.
rewrite morphimS ?andbT //; apply/reflectB; suff : (Bs (H / 'ker_H f)%G).
  by apply : cisomB; apply: (first_isog_loc f sHG).
apply:cquoB; last by apply/reflectB.
by rewrite /= -(ker_restrm sHG f) ker_normal.
Qed.

Canonical Structure bgFunc_T := [bgFunc by T_sub & T_cont].
Canonical Structure gFunc_T := GFunc (T_cont: cont bgFunc_T).

Lemma T_rad : radical T.
Proof.
move=> gT G; apply/trivgP; rewrite (@bigprodGE (coset_groupType _) _) gen_subG.
apply/bigcupsP=> H; case/andP=> BbH.
case/(inv_quotientS (bgFunc_normal bgFunc_T G)) => K KH sTGK sKG.
have KsNTG : K \subset 'N(T G) by exact: (subset_trans sKG (bgFunc_norm bgFunc_T G)).
rewrite KH quotient_sub1; last by exact: KsNTG.
rewrite bigprodGE sub_gen //; apply:bigcup_sup; rewrite sKG andbT.
move: (BbH); move/group_inj: KH =>->; move/reflectB => Bbquo.
apply/reflectB; apply: (cexB _ _ Bbquo); first by rewrite /normal sTGK KsNTG.
exact: (T_B (reflectB _ BbH)).
Qed.

Lemma T_Bs_devel : forall hT (H:{group hT}), Bs H ->
  forall gT (G : {group gT}), Bs G <-> T G :=: G.
Proof.
move=> hT H BsH gT G; split; last first.
  by move/group_inj=>eq; move:(T_B BsH G); rewrite eq.
move=> BsG; apply/eqP; rewrite eqEsubset; apply/andP; split; rewrite bigprodGE.
  by rewrite gen_subG; apply/bigcupsP=> H0; case/andP=> _.
by rewrite sub_gen //; apply: bigcup_sup; rewrite subxx andbT; apply/reflectB.
Qed.

Lemma T_idem : Idemp T.
Proof.
move=> gT G /=.
case e: (existsb H:{group gT}, Bbool H).
  move/idP: e; move/existsP; case=> /= H; move/reflectB=> BsH.
  by move: (T_B BsH G); move/(T_Bs_devel BsH).
suff noBs : (forall gT (H:{group gT}), Bs H -> False).
  by rewrite !(noBstrivT noBs).
move=> hT H BsH; case: (elimF existsP e); exists 1%G.
by apply/reflectB; apply: (cquoisom1 _ _ BsH).
Qed.

Lemma T_Cs_devel : forall hT (H:{group hT}), Bs H ->
  forall gT (G : {group gT}), Cs G <-> T G :=: 1%G.
Proof.
move=> hT H BsH gT G; split.
  move:(T_B BsH G)=>BsTG; move/hCBr'; move/(_ _ _ BsTG).
  move/(_ (idm_morphism (T G))); rewrite morphim_idm ?subxx //.
  (* TOFIX : Ugh ! Tsub !*)
  by move: (bgFunc_clos bgFunc_T G)=>/= TsubG; move/(_ TsubG).
move=> trivTG; apply: hBrC'=> hT0 H0 BsH0 f sfH0G.
apply/trivgP; rewrite -trivTG bigprodGE sub_gen //.
apply:bigcup_sup; rewrite sfH0G andbT; apply/reflectB.
move: (gFunc_cont gFunc_T f); move:(BsH0); move/(T_Bs_devel BsH0 H0)=>-> /=.
move/(conj (bgFunc_clos bgFunc_T (f @* H0))); move/andP; rewrite -eqEsubset /=.
by move/eqP; move/(T_Bs_devel BsH0).
Qed.

End EquivalenceTheorem4.

End Torsion.


Unset Implicit Arguments.
