(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import ssrfun.
Require Import eqtype.
Require Import ssrnat.
(* Require Import seq. *)
(* Require Import bigops. *)
(* Require Import ssralg. *)
(* Require Import paths. *)
(* Require Import connect. *)
(* Require Import div. *)
Require Import fintype.
Require Import finset.
Require Import groups.
Require Import group_perm.
Require Import normal.

Import GroupScope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Automorphism.

(* a group automorphism is a permutation on a subset of a finGroupType,*)
(* that respects the morphism law                                      *)

Variable gT : finGroupType.
Implicit Type A : {set gT}.

Definition Aut A := [set f | perm_on A f && morphic A f].

Lemma aut_morphic : forall A f, f \in Aut A -> morphic A f.
Proof. by move=> A f; rewrite inE; case/andP. Qed.

Definition autm A f Af := morphm (@aut_morphic A f Af).
Lemma autmE : forall A f Af, @autm A f Af = f.
Proof. by []. Qed.

Canonical Structure autm_morphism A f fM :=
  Eval hnf in [morphism of @autm A f fM].

Variables (G : {group gT}).

Lemma Aut_group_set : group_set (Aut G).
Proof.
apply/group_setP; split=> [|f g].
  by rewrite inE perm_on1; apply/morphicP=> ? *; rewrite !permE.
rewrite !inE; case/andP=> Gf fM; case/andP=> Gg gM; rewrite perm_onM //=.
apply/morphicP=> x y Gx Gy; rewrite !permM (morphicP fM) //.
by rewrite (morphicP gM) ?perm_closed.
Qed.

Canonical Structure Aut_group := Group Aut_group_set.

(* Should be redundant
Lemma automorphic_inv : forall f, f \in Aut G -> perm_inv f \in Aut G.
Proof. exact: groupVr. Qed.
*)

Variable (f : {perm gT}) (Af : f \in Aut G).
Notation fm := (autm Af).
Notation fmE := (autmE Af).

Lemma injm_autm : 'injm fm.
Proof. apply/injmP; apply: in2W; exact: perm_inj. Qed.

Lemma ker_autm : 'ker fm = 1.
Proof. by case/trivgP: injm_autm. Qed.

Lemma autm_dom : fm @* G = G.
Proof.
apply/setP=> x; rewrite morphimEdom (can_imset_pre _ (permK f)) inE.
by have:= Af; rewrite inE; case/andP; move/perm_closed=> <-; rewrite permKV.
Qed.

End Automorphism.

Notation "[ 'Aut' G ]" := (Aut_group G)
  (at level 0, format "[ 'Aut'  G ]") : subgroup_scope.

Prenex Implicits Aut autm.

Section PermOnOf.

Variables (T : finType) (B : {set T}) (f : T -> T).

Hypotheses (injf : {in B &, injective f}) (sBf : f @: B \subset B).

Lemma perm_on_of_inj : injective (fun x => if x \in B then f x else x).
Proof.
move=> x y /=; wlog By: x y / y \in B.
  by move=> IH eqfxy; case: ifP (eqfxy); [symmetry | case ifP => //]; auto.
rewrite By; case: ifP => [Bx | nBx def_x]; first exact: injf.
by case/negP: nBx; rewrite def_x (subsetP sBf) ?mem_imset.
Qed.

Definition perm_on_of := perm_of perm_on_of_inj.

Lemma perm_on_of_on : perm_on B perm_on_of.
Proof.
by apply/subsetP=> x; rewrite inE /= permE; case ifP => // _; case/eqP.
Qed.

Lemma perm_onE : {in B, perm_on_of =1 f}.
Proof. by move=> x Bx; rewrite /= permE Bx. Qed.

End PermOnOf.

Prenex Implicits perm_of.

Section AutOf.

Variables (gT : finGroupType) (G : {group gT}) (f : {morphism G >-> gT}).
Implicit Type A : {set gT}.

Hypothesis injf : 'injm f.

Lemma morphim_fixP : forall A,
  A \subset G -> reflect (f @* A = A) (f @* A \subset A).
Proof.
rewrite /morphim => A sAG; have:= eqset_sub_card (f @: A) A.
rewrite (setIidPr sAG) card_dimset ?leqnn ?andbT  => [<-|]; first exact: eqP.
move/injmP: injf; apply: subin2; exact/subsetP.
Qed.

Hypothesis Gf : f @* G = G.

Lemma aut_of_closed : f @: G \subset G.
Proof. rewrite -morphimEdom; exact/morphim_fixP. Qed.

Definition aut_of := perm_on_of (injmP _ injf) aut_of_closed.

Lemma autE : {in G, aut_of =1 f}.
Proof. exact: perm_onE. Qed.

Lemma morphic_aut_of : morphic G aut_of.
Proof. by apply/morphicP=> x y Gx Gy /=; rewrite !autE ?groupM // morphM. Qed.

Lemma Aut_aut_of : aut_of \in Aut G.
Proof. by rewrite inE morphic_aut_of perm_on_of_on. Qed.

Lemma imset_autE : forall A,  A \subset G -> aut_of @: A = f @* A.
Proof.
move=> A sAG; rewrite /morphim (setIidPr sAG).
apply: dfequal_imset; apply: subin1 autE; exact/subsetP.
Qed.

Lemma preim_autE : forall A, A \subset G -> aut_of @^-1: A = f @*^-1 A.
Proof.
move=> A sAG; apply/setP=> x; rewrite !inE permE /=.
by case Gx: (x \in G) => //; apply/negP=> Ax; rewrite (subsetP sAG) in Gx.
Qed.

End AutOf.

Implicit Arguments morphim_fixP [gT G f].
Prenex Implicits aut_of morphim_fixP.

Section ConjugationMorphism.

Variable gT : finGroupType.

Definition conjgm of {set gT} := fun x y : gT => y ^ x.

Lemma conjgmE : forall A x y, conjgm A x y = y ^ x. Proof. by []. Qed.

Canonical Structure conjgm_morphism A x :=
  @Morphism _ _ A (conjgm A x) (in2W (fun y z => conjMg y z x)).

Lemma morphim_conj : forall A x B, conjgm A x @* B = (A :&: B) :^ x.
Proof. by []. Qed.

Variable G : {group gT}.

Lemma injm_conj : forall x, 'injm (conjgm G x).
Proof. move=> x; apply/injmP; apply: in2W; exact: conjg_inj. Qed.

Lemma norm_conj_dom : forall x, x \in 'N(G) -> conjgm G x @* G = G.
Proof. move=> x; rewrite morphimEdom; exact: normgP. Qed.

Definition conj_aut x :=
  aut_of (injm_conj _) (norm_conj_dom (valP (insigd (group1 _) x))).

Lemma norm_conj_autE : {in 'N(G) & G, forall x y, conj_aut x y = y ^ x}.
Proof. by move=> x y nGx Gy; rewrite /= autE //= val_insubd nGx. Qed.

Lemma conj_autE : {in G &, forall x y, conj_aut x y = y ^ x}.
Proof. apply: subin11 norm_conj_autE => //; exact: subsetP (normG G). Qed.

Lemma conj_aut_morphM : {in 'N(G) &, {morph conj_aut : x y / x * y}}.
Proof.
move=> x y nGx nGy; apply/permP=> z /=; rewrite permM.
case Gz: (z \in G); last by rewrite !permE /= !Gz.
by rewrite !norm_conj_autE // (conjgM, memJ_normg, groupM).
Qed.

Canonical Structure conj_aut_morphism := Morphism conj_aut_morphM.

Lemma ker_conj_aut : 'ker conj_aut = 'C(G).
Proof.
apply/setP=> x; rewrite inE; case nGx: (x \in 'N(G)); last first.
  by symmetry; apply/idP=> cGx; rewrite (subsetP (sub_centg G)) in nGx.
rewrite 2!inE /=; apply/eqP/centgP=> [cx1 y Gy | cGx].
  by rewrite /commute (conjgC y) -norm_conj_autE // cx1 perm1.
apply/permP=> y; case Gy: (y \in G); last by rewrite !permE Gy.
by rewrite perm1 norm_conj_autE // conjgE -cGx ?mulKg.
Qed.

End ConjugationMorphism.

Prenex Implicits conjgm conj_aut.

Reserved Notation "G \char H" (at level 70).

Section Characteristicity.

Variable gT : finGroupType.
Implicit Types G H K L : {group gT}.

Definition characteristic (A B : {set gT}) :=
  (A \subset B) && (forallb f, (f \in Aut B) ==> (f @: A \subset A)).

Infix "\char" := characteristic.

Lemma charP : forall H G,
  reflect [/\ H \subset G & forall f : {morphism G >-> gT},
                            'injm f -> f @* G = G -> f @* H = H]
          (H \char G).
Proof.
move=> H G; apply: (iffP andP); case=> sHG chHG; split=> //.
  move=> f injf Gf; apply/morphim_fixP=> //.
  by have:= forallP chHG (aut_of injf Gf); rewrite Aut_aut_of imset_autE.
apply/forallP=> f; apply/implyP=> Af; have injf := injm_autm Af.
move/(morphim_fixP injf _ sHG): (chHG _ injf (autm_dom Af)).
by rewrite /morphim (setIidPr _).
Qed.

Lemma trivg_char : forall G, 1 \char G.
Proof.
by move=> G; apply/charP; split=> [|f _ _]; rewrite (sub1G, morphim1).
Qed.

Lemma char_refl : forall G, G \char G.
Proof. move=> G; exact/charP. Qed.

Lemma lone_subgroup_char : forall G H,
  H \subset G -> (forall K, K \subset G -> isog K H -> K \subset H) ->
  H \char G.
Proof.
move=> G H sHG Huniq; apply/charP; split=> // f injf Gf; apply/eqP.
have{injf} injf: {in H &, injective f}.
  by move/injmP: injf; apply: subin2; exact/subsetP.
have fH: f @* H = f @: H by rewrite /morphim (setIidPr sHG).
rewrite eqset_sub_card {2}fH card_dimset ?{}Huniq //=.
  by rewrite -{3}Gf morphimS.
rewrite isog_sym; apply/isogP.
exists [morphism of restrm sHG f] => //=; first exact/injmP.
by rewrite morphimEdom fH.
Qed.

Lemma char_trans : forall H G K, K \char H -> H \char G -> K \char G.
Proof.
move=> H G K; case/charP=> sKH chKH; case/charP=> sHG chHG.
apply/charP; split=> [|f injf Gf]; first exact: subset_trans sHG.
rewrite -{1}(setIidPr sKH) -(morphim_restrm sHG) chKH //.
  rewrite ker_restrm; case/trivgP: injf => ->; exact: subsetIr.
by rewrite morphim_restrm setIid chHG.
Qed.

Lemma char_norm_trans : forall H G K, K \char H -> H <| G -> K <| G.
Proof.
move=> H G K; case/charP=> sKH chKH; case/normalsubP=> sHG nHG.
apply/normalsubP; split=> [|x Gx]; first exact: subset_trans sHG.
have:= (chKH [morphism of conjgm H x]) => /=.
rewrite /morphim /= setIid (setIidPr sKH).
apply; [exact: injm_conj | exact: nHG].
Qed.

Lemma normal_char : forall H G, H \char G -> H <| G.
Proof.
by move=> H G; move/char_norm_trans; apply; apply/andP; rewrite normG.
Qed.

Lemma norm_char : forall H G, H \char G -> G \subset 'N(H).
Proof. by move=> H G; move/normal_char; case/andP. Qed.

Lemma charI : forall G H K, H \char G -> K \char G -> H :&: K \char G.
Proof.
move=> G H K; case/charP=> sHG chHG; case/charP=> _ chKG.
apply/charP; split=> [|f injf Gf]; first by rewrite subIset // sHG.
rewrite morphimGI ?(chHG, chKG) //; exact: subset_trans (sub1G H).
Qed.

Lemma charMgen : forall G H K, H \char G -> K \char G -> H <*> K \char G.
Proof.
move=> G H K; case/charP=> sHG chHG; case/charP=> sKG chKG.
apply/charP; split=> [|f injf Gf]; first by rewrite gen_subG subUset sHG.
by rewrite morphim_gen ?(morphimU, subUset, sHG, chHG, chKG).
Qed.

Lemma charM : forall G H K, H \char G -> K \char G -> H * K \char G.
Proof.
move=> G H K chHG chKG; rewrite -norm_mulgenE ?charMgen //.
by case/andP: (normal_char chKG) => _; apply: subset_trans; case/andP: chHG.
Qed.

End Characteristicity.

Notation "H \char G" := (characteristic H G) : group_scope.

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
rewrite -(morphim_quotm nHG Gf Hf) {}chKG // ?injm_quotm //.
by rewrite morphim_quotm Gf.
Qed.

Unset Implicit Arguments.
