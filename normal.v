(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Definitions of conjugate set, normal set and quotient group        *)
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

Variables (gT : finGroupType) (A : {set gT}).

(* We let cosets coerce to GroupSet.sort, so they inherit the   *)
(* group subset base group structure. Later we will define a    *)
(* proper group structure on cosets, which will then hide the   *)
(* inherited structure (once coset unifies with FinGroup.sort   *)
(* the coercion to GroupSet.sort will no longer be used). Note  *)
(* that for Hx Hy : coset H, Hx * Hy : {set gT} can be either   *)
(*           set_of_coset (mulg Hx Hy)                          *)
(*   or mulg (set_of_coset Hx) (set_of_coset Hy)                *)
(* However, since the two terms are actually convertible, we    *)
(* can live with this ambiguity.                                *)
(*   We take great care that neither the type coset H, nor its  *)
(* finGroupType structure, nor the coset_of H morphism depend   *)
(* the actual group structure of H; this is because the proof   *)
(* component of that structure can become quite involved (there *)
(* could be, for instance, several morphic images that depend   *)
(* in turn on side conditions), which would swamp the display.  *)
(* Further, all our equalities are stated at the set level, so  *)
(* rewriting would be extremely awkward.                        *)
(*   The trick we use is to interpret coset A, when A is any    *)
(* set, as the type of bilateral cosets of <<A>>, using the     *)
(* fact that this coincides with the cosets of A when A is a    *)
(* group. We restrict the domain of coset_of A to 'N(A), so     *)
(* that we get almost all the same conversion equalities as if  *)
(* we had forced A to be a group in the first place -- the only *)
(* exception is that 1 : coset H : set _ = <<H>> rather than H, *)
(* which hardly interferes as it's covered by the genGid lemma. *)

Notation H := <<A>>.
Definition coset_range := [pred B \in rcosets H 'N(H)].

Record coset : Type :=
  Coset { set_of_coset :> GroupSet.sort gT; _ : coset_range set_of_coset }.

Canonical Structure coset_subType := SubType set_of_coset coset_rect vrefl.
Canonical Structure coset_eqType := Eval hnf in [subEqType for set_of_coset].
Canonical Structure coset_finType := Eval hnf in [finType of coset by :>].
Canonical Structure coset_subFinType := Eval hnf in [subFinType of coset].

(* We build a new (canonical) structure of groupType for cosets.      *)
(* When A is a group, this is the largest possible quotient 'N(H) / H *)

Lemma coset_range_unit : coset_range H.
Proof. by apply/rcosetsP; exists (1 : gT); rewrite (group1, mulg1). Qed.
Definition coset_unit := Coset coset_range_unit.

Lemma coset_range_mul : forall B C : coset, coset_range (B * C).
Proof.
case=> B /=; case/rcosetsP=> x Nx ->{B} [C] /=; case/rcosetsP=> y Ny ->{C}.
by apply/rcosetsP; exists (x * y); rewrite (groupM, rcoset_mul).
Qed.

Definition coset_mul B C := Coset (coset_range_mul B C).

Lemma coset_range_inv : forall B : coset, coset_range B^-1.
Proof.
case=> B /=; case/rcosetsP=> x Nx ->{B}; rewrite norm_rlcoset // invg_lcoset.
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
by rewrite norm_rlcoset // -lcosetM mulVg mul1g.
Qed.

Canonical Structure coset_preGroupType :=
  [baseFinGroupType of coset by coset_mulP, coset_unitP & coset_invP].
Canonical Structure coset_groupType := FinGroupType coset_invP.

Lemma norm_repr_coset : forall xbar : coset, repr xbar \in 'N(H).
Proof.
case=> C /=; case/rcosetsP=> x Nx ->{C}; case: (repr_rcosetP [group of H]) => /=.
by move=> z Hz; rewrite groupMr //= (subsetP (normG _)).
Qed.

(* Projection of the initial group type over the cosets groupType  *)

Definition coset_of x : coset := insubd (1 : coset) (H :* x).

Lemma val_coset_of : forall x,
  val (coset_of x) = (if x \in 'N(H) then H :* x else H).
Proof. by move=> x; rewrite val_insubd /= mem_rcosets mulSGid ?normG. Qed.

Lemma coset_ofV : {morph coset_of : x / x^-1}.
Proof.
move=> x; apply: val_inj; rewrite /= !val_coset_of groupV /=.
by case: ifP => Nx; rewrite Nx ?invGid // -invg_lcoset norm_rlcoset.
Qed.

Lemma coset_of_morphM : {in 'N(A) &, {morph coset_of : x y / x * y}}.
Proof.
apply: (subin2 (subsetP (norm_gen A))) => x y Nx Ny; apply: val_inj.
by rewrite /= !val_coset_of Nx Ny groupM //= rcoset_mul.
Qed.

Canonical Structure coset_of_morphism := Morphism coset_of_morphM.

End Cosets.

Prenex Implicits coset coset_of.


Section CosetOfGroupTheory.

Variables (gT : finGroupType) (H : {group gT}).
Implicit Types A : {set gT}.
Notation cH := (coset_of H).
Notation cT := (coset_groupType H).

Lemma set_of_coset_of : forall x,
  cH x = (if x \in 'N(H) then H :* x else H) :> {set _}.
Proof. by move=> x; rewrite val_coset_of /= genGid. Qed.

Lemma coset_ofN : forall x, x \in 'N(H) -> cH x = H :* x :> set _.
Proof. by move=> x; rewrite set_of_coset_of => ->. Qed.

Lemma coset_of_id : forall x, x \in H -> cH x = 1.
Proof.
move=> x Hx; apply: val_inj => /=.
by rewrite coset_ofN ?(rcoset_id, genGid) // inE conjGid.
Qed.

Lemma coset_of_idr : forall x, x \in 'N(H) -> cH x = 1 -> x \in H.
Proof.
move=> x Nx;  move/(congr1 val); rewrite /= genGid => <-.
by rewrite coset_ofN ?rcoset_refl.
Qed.

Lemma ker_coset : 'ker (cH) = H.
Proof.
apply/setP=> x; rewrite inE; apply/andP/idP=> [[Nx] | Hx] /=.
  rewrite inE; move/set1P; exact: coset_of_idr.
by rewrite (subsetP (normG H)) // inE /= coset_of_id ?set11.
Qed.

Lemma norm_repr_cosetG : forall xbar : coset  H, repr xbar \in 'N(H).
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

Lemma cosetpre_coset_set1 : forall xbar, cH @*^-1 [set xbar] = xbar.
Proof.
move=> xbar; case: (cosetP xbar) => x Nx ->{xbar}; apply/setP=> y.
symmetry; rewrite inE !coset_ofN //; case Ny: (y \in 'N(H)).
  by rewrite !inE (sameP eqP (rcoset_kerP _ Ny Nx)) ker_coset.
apply/rcosetP=> [[z Hz def_y]]; case/idP: Ny.
by rewrite def_y groupMl // (subsetP (normG _)).
Qed.

(* We now build the morphism theory of coset_of by specialising the
lemmas of the normal library, in part. with the value of 'ker cH *)

Lemma coset_of1 : cH 1%g = H :> set _.
Proof. by rewrite morph1 /= genGid. Qed.

Lemma ker_cosetE : H = cH @*^-1 1 :> set _. 
Proof. symmetry; rewrite -{7}ker_coset; apply: kerE. Qed.

Lemma cosetimEdom : cH @* 'N(H) = setT.
Proof.
rewrite morphimEdom /=; apply/eqP; rewrite eqset_sub subsetT.
by  apply/subsetP=> /= x _; case: (cosetP x)=> u Nu ->; apply/imsetP; exists u.
Qed.

Lemma coset_ker : forall x, x \in H -> cH x = 1.
Proof. rewrite -{1}ker_coset; exact: mker. Qed.

Lemma coset_kerl : forall x y, x \in H -> y \in 'N(H) -> cH (x * y) = cH y.
Proof. rewrite -{1}ker_coset; exact: mkerl. Qed.

Lemma coset_kerr : forall x y, x \in 'N(H) -> y \in H -> cH (x * y) = cH x.
Proof. rewrite -{2}ker_coset; exact: mkerr. Qed.

Lemma rcoset_kercosetP : forall x y,
  x \in 'N(H) -> y \in 'N(H) -> reflect (cH x = cH y) (x \in H :* y).
Proof. rewrite -{6}ker_coset; exact: rcoset_kerP. Qed.

Lemma kercoset_rcoset : forall x y,
  x \in 'N(H) -> y \in 'N(H) -> cH x = cH y -> exists2 z, z \in H & x = z * y.
Proof. move=> x y Gx Gy eqfxy; rewrite -ker_coset; exact: ker_rcoset. Qed.

Lemma cosetimGI : forall (G : {group gT})(A : {set gT}),
  H \subset G -> cH @* (G :&: A) = cH @* G :&: cH @* A.
Proof. by rewrite -{1}ker_coset; exact: morphimGI. Qed.


Lemma cosetimIG : forall (A : {set gT}) (G : {group gT}),
  H \subset G -> cH @* (A :&: G) = cH @* A :&: cH @* G.
Proof. rewrite -{1}ker_coset. exact: morphimIG. Qed.

Lemma cosetimDG : forall A (G : {group gT}),
  H \subset G -> cH @* (A :\: G) = cH @* A :\: cH @* G.
Proof. rewrite -{1}ker_coset; exact: morphimDG. Qed.

Lemma cosetimK : forall A, A \subset 'N(H) -> cH @*^-1 (cH @* A) = H * A.
Proof. rewrite -{12}ker_coset; exact: morphimK. Qed.

Lemma cosetimGK : forall (G : {group gT}),
 H \subset G -> G \subset 'N(H) -> cH @*^-1 (cH @* G) = G.
Proof. by rewrite -{1}ker_coset; exact: morphimGK. Qed.

Lemma cosetpre_set1 : forall x, x \in 'N(H) -> cH @*^-1 [set cH x] = H :* x.
Proof. by rewrite -{9}ker_coset; exact: morphpre_set1. Qed.

Lemma cosetim_ker : cH @* H = 1.
Proof. by rewrite -{8}ker_coset morphim_ker. Qed.

Lemma normal_ker_cosetpre : forall (G : {group cT}),
  H <| cH @*^-1 G.
Proof. rewrite -{3}ker_coset; exact: normal_ker_pre. Qed.

Lemma sub_cosetpre_im : forall (C : {set cT})(G : {group gT}),
    H \subset G -> G \subset 'N(H) -> C \subset cH @* 'N(H) ->
  (cH @*^-1 C \subset G) = (C \subset cH @* G).
Proof. rewrite -{3}ker_coset; exact: sub_morphpre_im. Qed.

Lemma ker_trivg_cosetim : forall A,
  (A \subset H) = (A \subset 'N(H)) && trivg (cH @* A).
Proof. rewrite -{1}ker_coset; exact: ker_trivg_morphim. Qed. 

Lemma cosetimSK : forall A B,
  A \subset 'N(H) -> (cH @* A \subset cH @* B) = (A \subset H * B).
Proof. rewrite -{19}ker_coset; exact: morphimSK. Qed.

Lemma cosetimSGK : forall A (G : {group gT}),
  A \subset 'N(H) -> H \subset G -> (cH @* A \subset cH @* G) = (A \subset G).
Proof. rewrite -{2}ker_coset; exact: morphimSGK. Qed.

Lemma cosetim_inj :
  {in [pred G : {group _} | (H \subset G) && (G \subset 'N(H))] &,
   injective (fun G : group _ => cH @* G)}.
Proof. rewrite -{1}ker_coset; exact: morphim_inj. Qed.


End CosetOfGroupTheory.

Section Quotient.

Variable gT : finGroupType.

Implicit Types A B : {set gT}.
Implicit Types G H K : {group gT}.

Definition quotient A B : {set coset B} := coset_of B @* A.

Infix "/" := quotient : group_scope.

Lemma quotientE : forall A B, A / B = coset_of B @* A. Proof. by []. Qed.

Canonical Structure quotient_group G A := Eval hnf in [group of G / A].

Infix "/" := quotient_group : subgroup_scope.

(* From this point on, we work only with cosets of real groups. *)

Variable H : {group gT}.

Lemma coset_of_norm : forall G, coset_of H @: G = G / H.
Proof.
move=> G; apply/eqP; rewrite eqset_sub andbC imsetS ?subsetIr //=.
apply/subsetP=> xbar; case/imsetP=> x Gx -> {xbar}.
case Nx: (x \in 'N(H)); first by rewrite mem_imset 1?inE ?Nx.
by rewrite ((_ x =P 1) _) ?group1 // -val_eqE /= set_of_coset_of Nx genGid.
Qed.

Lemma trivial_quotient : H / H = 1.
Proof. by rewrite -{3}ker_coset quotientE morphim_ker. Qed.
  
Lemma trivg_quotient : forall A,
  A \subset 'N(H) -> trivg (A / H) = (A \subset H).
Proof. by move=> A nHA; rewrite -{3}ker_coset ker_trivg_morphim nHA. Qed.

Lemma val_quotient : forall A, val @: (A / H) = rcosets H 'N_A(H).
Proof.
move=> A; apply/setP=> B; apply/imsetP/rcosetsP=> [[xb Axb]|[x ANx]] ->{B}.
  case/morphimP: Axb => x Nx Ax ->{xb}.
  by exists x; [rewrite inE Ax | rewrite /= coset_ofN].
case/setIP: ANx => Ax Nx.
by exists (coset_of H x); [apply/morphimP; exists x | rewrite /= coset_ofN].
Qed.

Lemma card_quotient : forall A, A \subset 'N(H) -> #|A / H| = #|A : H|.
Proof.
by move=> A nHA; rewrite -(card_imset _ val_inj) val_quotient (setIidPl nHA).
Qed.

Lemma quotient_inj :
  {in [pred K : {group gT} | H <| K] &, injective (fun K => K / H)}.
Proof. by move=> G K nHG nHK; apply: morphim_inj; rewrite ker_coset. Qed.

Section InverseImage.

Variables (G : {group gT}) (Kbar : {group coset H}).

Hypothesis nHG : H <| G.

CoInductive inv_quotient_spec (P : pred {group gT}) : Prop :=
  InvQuotientSpec K of (Kbar = K / H)%G & H \subset K & P K.

Lemma inv_quotientS :
  Kbar \subset G / H -> inv_quotient_spec (fun K => K \subset G).
Proof.
case/andP: nHG => sHG nHG' sKbarG.
have sKdH: Kbar \subset 'N(H) / H by rewrite (subset_trans sKbarG) ?morphimS.
exists [group of coset_of H @*^-1 Kbar].
- by apply: val_inj; rewrite /= quotientE morphpreK.
- by rewrite -{1}ker_coset morphpreS ?sub1G.
by rewrite sub_morphpre_im ?ker_coset.
Qed.

Lemma inv_quotientN : Kbar <| G / H -> inv_quotient_spec (fun K => K <| G).
Proof.
case/andP: nHG => sHG nHG' nKbar; case: (andP nKbar) => sKbarG _.
case: (inv_quotientS sKbarG) => K defKbar sHK sKG.
have nHGbar: G / H \subset 'N(H) / H by rewrite morphimS; case/andP: nHG.
rewrite -(morphpre_normal (subset_trans sKbarG nHGbar) nHGbar) /= in nKbar.
exists K => //; rewrite defKbar !morphimGK ?ker_coset // in nKbar.
exact: subset_trans nHG'.
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

Lemma quotient_mulG : forall G, G \subset 'N(H) -> G <*> H / H = G / H.
Proof.
move=> G nHG; rewrite -genM_mulgen quotientE morphim_gen -?quotientE.
  by rewrite quotient_mulg genGid.
by rewrite -(mulSGid nHG) mulgS ?normG.
Qed.

End Quotient.

Notation "A / B" := (quotient A B) : group_scope.
Notation "A / H" := (quotient_group A H) : subgroup_scope.

Section QuotientMorphism.

Variable (gT : finGroupType) (G H : {group gT}) (f : {morphism G >-> gT}).

Hypotheses (nHG : H <| G) (nGf : f @* G = G) (nHf : f @* H = H).

Notation fH := (coset_of H \o f).

Lemma quotm_restr_proof : G \subset 'dom fH.
Proof. by rewrite -sub_morphim_pre // nGf; case/andP: nHG. Qed.

Notation fH_G := (restrm quotm_restr_proof fH).

Lemma quotm_fact_proof1 : G \subset 'N(H).
Proof. by case/andP: nHG. Qed.

Lemma quotm_fact_proof2 : 'ker (coset_of H) \subset 'ker fH_G.
Proof.
case/andP: nHG => sHG _; rewrite ker_restrm ker_comp ker_coset subsetI.
by rewrite -sub_morphim_pre sHG ?nHf /=.
Qed.

Definition quotm := factm quotm_fact_proof1 quotm_fact_proof2.
Canonical Structure quotm_morphism := Eval hnf in [morphism of quotm].

Lemma cosetim_quotm : forall A : {set gT}, quotm @* (A / H) = f @* A / H.
Proof.
case/andP: nHG => sHG nHG' A.
by rewrite morphim_factm morphim_restrm morphim_comp morphimIdom.
Qed.

Lemma cosetpre_quotm : forall A : {set gT},
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
Implicit Types G H : {group aT}.

Lemma first_isom : forall G (f : {morphism G >-> rT}),
  isog (G / 'ker f) (f @* G).
Proof.
move=> G f; apply/isogP; have nkG := norm_ker f.
have skk: 'ker (coset_of ('ker f)) \subset 'ker f by rewrite ker_coset.
exists [morphism of factm nkG skk] => /=; last by rewrite morphim_factm.
by rewrite ker_factm -quotientE trivial_quotient.
Qed.

Lemma first_isom_loc : forall G H (f : {morphism G >-> rT}),
  H \subset G -> isog (H / 'ker_H f) (f @* H).
Proof.
move=> G H f sHG.
rewrite -{4}(setIid H) -(morphim_restrm sHG) -(ker_restrm sHG f).
exact: first_isom.
Qed.

End FirstIsomorphism.

Section SecondIsomorphism.

Variables (gT : finGroupType) (H K : {group gT}).

Hypothesis nKH : H \subset 'N(K).

Lemma second_isom : isog (H / (K :&: H)) (H / K).
Proof. rewrite setIC -{1 3}(ker_coset K); exact: first_isom_loc. Qed.

Lemma weak_second_isom : isog (H / (K :&: H)) (H * K / K).
Proof. rewrite quotient_mulg; exact: second_isom. Qed.

End SecondIsomorphism.

Section ThirdIsomorphism.

Variables (gT : finGroupType) (G H K : {group gT}).

Hypothesis sHK : H \subset K.
Hypothesis snHG : H <| G.
Hypothesis snKG : K <| G.

Theorem third_isom : isog (G / H / (K / H)) (G / K).
Proof.
case/andP: snKG => sKG nKG; case/andP: snHG => sHG nHG.
have sHker: 'ker (coset_of H) \subset 'ker (restrm nKG (coset_of K)).
  by rewrite ker_restrm !ker_coset subsetI sHG.
have:= first_isom_loc [morphism of factm nHG sHker] (subset_refl _) => /=.
rewrite ker_factm_loc morphim_factm morphim_restrm ker_restrm -!quotientE.
by rewrite ker_coset !(setIidPr sKG) setIid.
Qed.

End ThirdIsomorphism.



Lemma char_from_quotient : forall (gT : finGroupType) (G H K : {group gT}),
  H <| K -> H \char G -> K / H \char G / H -> K \char G.
Proof.
move=> gT G H K; case/andP=> sHK nHK chHG; case/charP=> sKG chKG.
have nHG := normal_char chHG; case: (andP nHG) => sHG nHG'.
rewrite -(ker_coset H) in sHK; rewrite morphimSGK ?ker_coset // in sKG.
apply/charP; split=> // f injf Gf; apply/morphim_fixP => //.
have{chHG} Hf: f @* H = H by case/charP: chHG => _; apply.
rewrite -(morphimSGK _ sHK) -?quotientE; last first.
  by apply: subset_trans nHG'; rewrite -{3}Gf morphimS.
rewrite -(cosetim_quotm nHG Gf Hf) {}chKG // ?injm_quotm //.
by rewrite cosetim_quotm Gf.
Qed.
