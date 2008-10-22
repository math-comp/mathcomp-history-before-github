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

End IdentitySubFunctorDefs.

Module BaseIdSubFunctor.

(* Those mappings only functorial w.r.t. automorphisms*)

Implicit Types gT: finGroupType.

Structure mixin (Fobj : obmap) : Type := Mixin { _ : aresp Fobj}.

Structure class : Type := Class { Fobj :> obmap ; 
   _ : forall gT (G : {group gT}), group_set (Fobj gT G);
   _ : forall gT (G: {group gT}), Fobj gT G \subset G;
   _ : mixin Fobj}.

Definition group_of F := let: Class _ g _ _ := F return 
  forall gT (G : {group gT}), group_set (F gT G) in g.
Definition subset_of F := let: Class _ _ s _ := F return
  forall gT (G: {group gT}), F gT G \subset G in s.

Coercion mixin_of F := let: Class _ _ _ m := F return mixin F in m.

End BaseIdSubFunctor.

Notation bisFc := BaseIdSubFunctor.class.
Notation BisFc := BaseIdSubFunctor.Class.
Notation BisFMixin := BaseIdSubFunctor.Mixin.

Definition mkBaseisFc F FM Fsub Fresp := 
  BisFc FM Fsub (@BisFMixin F Fresp).

Notation "[ 'bisFc' 'of' F ]" :=
  (match [is F : _ -> _ <: bisFc] as s return {type of BisFc for s} -> _ with
    | BisFc _ g s m => fun k => k g s m end
  (@BisFc F)) (at level 0, only parsing) : form_scope.

Notation Local "''e_' s ( G )" := (s _ G)
  (at level 8,s at level 2, format "''e_' s ( G )") : group_scope.

Section BaseIdentitySubfunctorProps.

Variables gT hT:finGroupType.
Variable sF: bisFc.
Implicit Types G H : {group gT}.

Lemma bisfc_groupset : forall G, group_set ('e_sF(G)).
Proof. by case sF. Qed.

Canonical Structure bisfc_group G := 
  Group (bisfc_groupset G).

Lemma bisfc_clos : forall (fT:finGroupType) (H:{group fT}),
  'e_sF(H) \subset H.
Proof. by case sF. Qed.

Lemma bisfc_aresp : aresp sF.
Proof. by case sF=> Fobj Fg Fs; case. Qed.

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

Structure mixin (Fobj : obmap) : Type := Mixin { _ : resp Fobj}.

Structure class : Type := Class { 
  Fobj :> obmap ;
   _ : forall gT (G : {group gT}), group_set (Fobj gT G);
   _ : forall gT (G: {group gT}), Fobj gT G \subset G;
   _ : mixin Fobj}.

Definition group_of F := let: Class _ g _ _ := F return 
  forall gT (G : {group gT}), group_set (F gT G) in g.
Definition subset_of F := let: Class _ _ s _ := F return
  forall gT (G: {group gT}), F gT G \subset G in s.

Coercion mixin_of F := let: Class _ _ _ m := F return mixin F in m.

Lemma isfc_resp (sF: class): resp sF.
Proof. by case => F FM Fs; case. Qed.

Coercion bmixin_of_mixin Fobj (m : mixin Fobj) := 
  let: Mixin mresp := m return BaseIdSubFunctor.mixin Fobj in
  BisFMixin (aresp_of_resp mresp).

End IdSubFunctor.

Notation isFc := IdSubFunctor.class.
Notation IsFc := IdSubFunctor.Class.
Notation IsFMixin := IdSubFunctor.Mixin.

Definition mkIsFc F FM Fsub Fresp := 
  IsFc FM Fsub (@IsFMixin F Fresp).

Notation "[ 'isFc' 'of' F ]" :=
  (match [is F : _ -> _ <: bisFc] as s return {type of BisFc for s} -> _ with
    | IsFc _ g s m => fun k => k g s m end
  (@IsFc F)) (at level 0, only parsing) : form_scope.

Coercion isFc_bisFc (sF : isFc) := 
  BisFc (IdSubFunctor.group_of sF) (IdSubFunctor.subset_of sF) sF.

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
move=> gT hT G D f injf sGD; apply/eqP; rewrite eqset_sub morphim_sfunctor //=.
rewrite -{2}(morphim_invm injf sGD) -[f @* sF _ _](morphpre_invm injf).
have sFtr := subset_trans (bisfc_clos _ _).
by rewrite -sub_morphim_pre (morphim_sfunctor, sFtr) ?morphimS.
Qed.

Lemma isom_sfunctor : forall gT hT (D G : {group gT}) (R : {group hT}) 
                                   (f : {morphism D >-> hT}),
  G \subset D -> isom G R f -> isom ('e_sF(G)) ('e_sF(R)) f.
Proof.
move=> gT rT D G R f; case/(restrmP f)=> g [_ _ ->]; case/isomP=> injf <-.
rewrite /isom -!setDset1 -(injm_sfunctor injf) //.
rewrite -morphimEsub ?morphimDG ?morphim1 //. 
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

Section IdentitySubfunctorsExamples.

Implicit Types gT:finGroupType.

Lemma id_resp : resp (fun _ S => S).
Proof. by []. Qed.

Canonical Structure id_subfunc :=
  IsFc (fun gT G => groupP G%G)
       (fun gT G => subset_refl _)
       (IsFMixin id_resp).

Lemma triv_resp : resp (fun _ S => 1).
Proof. by move=> gT hT H f; rewrite morphim1. Qed.

Canonical Structure triv_subfunc :=
  @IsFc (fun _ S => 1)
        (fun _ G => groupP 1%G)
        sub1G
        (IsFMixin triv_resp).

Require Import center.

Lemma center_resp : resp (fun _ S => 'Z(S)).
Proof.
move=> gT hT H phi /=; apply:(subset_trans (morphimI _ _ _ )).
rewrite subsetI subsetIl /=; apply:(subset_trans (subsetIr (phi @* H) _) ).
exact:morphim_cent.
Qed.

Canonical Structure center_id_subfunc :=
  IsFc (fun gT G => groupP 'Z(G)%G)
       (fun gT G => @center_sub gT G)
       (IsFMixin center_resp).

Require Import maximal.

Lemma Frattini_resp : resp (Frattini).
Proof. exact: gfunc_Phi. Qed.

Canonical Structure Frattini_subfunc :=
  IsFc (fun gT G => groupP 'Phi(G)%G)
       (fun gT => @Phi_sub gT)
       (IsFMixin Frattini_resp).

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
  IsFc (fun gT (G:{group gT}) => der_group_set G n)
       (der_clos n)
       (IsFMixin (der_resp n)).

Lemma lcn_resp : forall n,
  resp (fun gT G => 'L_n(G)).
Proof.
elim=> [|n IH] gT hT H phi; first by rewrite !lcn0.
by rewrite !lcnSn morphimR ?lcn_sub0 // commSg ?IH.
Qed.

Canonical Structure lcn_id_subfunctor (n:nat) :=
  IsFc (fun gT (G :{group gT}) => lcn_group_set G n)
       (fun gT G => (lcn_sub0 G n))
       (IsFMixin (lcn_resp n)).

Require Import pgroups.

Lemma Ohm_sub : forall i gT (G:{group gT}), 'Ohm_i(G) \subset G.
Proof. move=> gT i; exact: Ohm_sub. Qed.

Lemma Ohm_resp : forall i,
  resp (fun gT S => 'Ohm_i(S)).
Proof. move=> i G f; exact: gfunc_Ohm. Qed.

Canonical Structure Ohm_id_subfunctor (i:nat) :=
  IsFc  (fun gT (G:{group gT}) => groupP 'Ohm_i(G)%G)
        (Ohm_sub i)
        (IsFMixin (Ohm_resp i)).

Lemma Mho_sub : forall i gT (G:{group gT}), 'Mho^i(G) \subset G.
Proof. move=> i; exact: Mho_sub. Qed.

Lemma Mho_resp : forall i,
  resp (fun gT S => 'Mho^i(S)).
Proof. move=> i G f; exact: gfunc_Mho. Qed.

Canonical Structure Mho_id_subfunctor (i:nat) :=
  IsFc (fun gT (G:{group gT}) => groupP 'Mho^i(G)%G)
       (Mho_sub i)
       (IsFMixin (Mho_resp i)).

End IdentitySubfunctorsExamples.

Section MaxnormalSeries.

Variable gT:finGroupType.
Implicit Types G M N B:{group gT}.

Lemma norm_morphim_conj : forall G M (nMG : M <| G) x,
  x \in 'N(M) ->
  (conjgm G x) @* M = M.
by move=> G M *; rewrite morphim_conj (setIidPr (normal_sub _)) //; apply:normP. 
Qed.

Definition max_ucn (G M : {group gT}) (nMG:M <| G) B :=
  [max B of N | (M \subset N) && (N <| G) && 
    forallb x, (x \in G) ==> forallb y, (y \in N / M) ==>
    ((coset M \o conjgm N x) (repr y) == y)].

Definition prop_ucn (G M : {group gT}) (nMG:M <| G) N :=
 forall (H1:M\subset N) (H2: N <| G) x (Hx:x \in G),
   let nMN := (normalS H1 (normal_sub H2) nMG) in
    {in N/M, quotm nMN
    (norm_conj_dom ((subsetP (normal_norm H2)) x Hx))
    (norm_morphim_conj nMN ((subsetP (normal_norm nMG)) x Hx))
      =1 idm (N / M)}.

Lemma max_ucnP : forall G M (nMG: M <| G) B,
  reflect [/\ (M \subset B), (B <| G), (prop_ucn nMG B)
    & (forall H : {group gT},
      [/\ (M \subset H), (H <| G), (prop_ucn nMG H) & B \subset H] -> H = B)]
  (max_ucn nMG B).
Proof.
move=> G M nMG N; apply: (iffP (maxgroupP _ _)) => [[]|[sMN nNG Hid max]].
  case/andP; case/andP=> sMN nNG Hid max; rewrite sMN nNG ; split=>//.
    move=> HsMN HnNG x Hx; rewrite /quotm /factm /= /restrm.
    move/(_ x): (forallP Hid); move/implyP; move/(_ Hx)=> H y Hy.
    move/(_ y): (forallP H); move/implyP; move/(_ Hy); move/eqP.
    by rewrite cosetpre_set1_coset.
  move=> H [sMH nHG HHid sNH]; apply:val_inj; apply:(max H) =>//.
  rewrite sMH nHG !andTb; apply/forallP=> x; apply/implyP=> Hx.
  apply/forallP=> y; apply/implyP=> Hy;apply/eqP. 
  by rewrite -cosetpre_set1_coset; apply:HHid.
rewrite sMN nNG; split=>/= [|H]; last first.
  case/andP; case/andP => sMH nHG HHid sNH; rewrite (max H); split =>//.
  move=> HsMH HnHG x Hx; rewrite /quotm /factm /= /restrm.
  move/(_ x): (forallP HHid); move/implyP; move/(_ Hx)=> HH y Hy.
  move/(_ y): (forallP HH); move/implyP; move/(_ Hy); move/eqP.
  by rewrite cosetpre_set1_coset.
apply/forallP=> x; apply/implyP=> Hx; apply/forallP=> y; apply/implyP=> Hy.
by apply/eqP; rewrite -cosetpre_set1_coset; apply: Hid.
Qed.

Lemma commute_conjgP : forall (x y:gT), reflect (commute x y) (x ^ y == x).
Proof.
move=> x y.
apply: (iffP eqP); rewrite conjgE; last by move=>->; rewrite mulgA mulVg mul1g.
by rewrite -{2}(mul1g x) -(mulVg y) -mulgA; move/mulg_injl.
Qed.

Lemma center_ucn1 : forall (G:{group gT}), max_ucn (normal1 G) 'Z(G).
Proof.
move=> G; apply/max_ucnP; rewrite center_normal sub1G; split => //.
  move=> s1Z nZG x Hx /= y; move/imsetP=> [x0]; rewrite {1}norm1 setTI => nHx ->.
  rewrite /quotm factmE //= /restrm; move/subcentP: nHx=>[Hx0].
  by move/(_ x Hx); rewrite /= conjgmE; move/commute_conjgP; move/eqP->.
move=> H [_ nHG Hid] sZH.
apply:val_inj; apply/eqP; rewrite eq_sym eqset_sub sZH; apply/subsetP=> x /= Hx.
apply/subcentP; split; first by rewrite (subsetP (normal_sub nHG)).
move=> y Hy; apply/commute_conjgP; apply/eqP; move/injmP:(@coset1_injm gT).
rewrite /= norm1; apply; rewrite ?in_setT //.
have Hqx: ((coset 1 x) \in H / 1)
  by rewrite /quotient /morphim mem_imset ?norm1 ?setTI.
by move: (Hid (sub1G H) nHG y Hy (coset 1 x) Hqx); rewrite /quotm factmE.
Qed.

End MaxnormalSeries.


Unset Implicit Arguments.
