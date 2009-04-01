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
Require Import perm.
Require Import morphisms.


Import GroupScope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Automorphism.

(* a group automorphism is a permutation on a subset of a finGroupType,*)
(* that respects the morphism law                                      *)

Variable gT : finGroupType.
Implicit Type A : {set gT}.
Implicit Types f g : {perm gT}.

Definition Aut A := [set f | perm_on A f && morphic A f].

Lemma Aut_morphic : forall A f, f \in Aut A -> morphic A f.
Proof. by move=> A f; rewrite inE; case/andP. Qed.

Lemma out_Aut : forall A f x, f \in Aut A -> x \notin A -> f x = x.
Proof. by move=> A f x; case/setIdP=> Af _; exact: out_perm. Qed.

Lemma eq_Aut : forall A, {in Aut A &, forall f g, {in A, f =1 g} -> f = g}.
Proof.
move=> A f g Af Ag eqfg; apply/permP=> x.
by case/orP: (orbN (x \in A)); [apply eqfg | move/out_Aut=> out; rewrite !out].
Qed.

Definition autm A f Af := morphm (@Aut_morphic A f Af).
Lemma autmE : forall A f Af, @autm A f Af = f.
Proof. by []. Qed.

Canonical Structure autm_morphism A f fM :=
  Eval hnf in [morphism of @autm A f fM].

Section AutGroup.

Variable G : {group gT}.

Lemma Aut_group_set : group_set (Aut G).
Proof.
apply/group_setP; split=> [|f g].
  by rewrite inE perm_on1; apply/morphicP=> ? *; rewrite !permE.
rewrite !inE; case/andP=> Gf fM; case/andP=> Gg gM; rewrite perm_onM //=.
apply/morphicP=> x y Gx Gy; rewrite !permM (morphicP fM) //.
by rewrite (morphicP gM) ?perm_closed.
Qed.

Canonical Structure Aut_group := group Aut_group_set.

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
End AutGroup.

Lemma Aut1 : Aut 1 = 1.
Proof.
apply/trivgP; apply/subsetP=> s /= As; apply/set1P.
apply: eq_Aut (As) (group1 _) _ => x; move/set1P=> ->{x}.
by rewrite -(autmE As) morph1 perm1.
Qed.

End Automorphism.

Notation "[ 'Aut' G ]" := (Aut_group G)
  (at level 0, format "[ 'Aut'  G ]") : subgroup_scope.

Prenex Implicits Aut autm.

Section PermIn.

Variables (T : finType) (B : {set T}) (f : T -> T).

Hypotheses (injf : {in B &, injective f}) (sBf : f @: B \subset B).

Lemma perm_in_inj : injective (fun x => if x \in B then f x else x).
Proof.
move=> x y /=; wlog By: x y / y \in B.
  by move=> IH eqfxy; case: ifP (eqfxy); [symmetry | case ifP => //]; auto.
rewrite By; case: ifP => [Bx | nBx def_x]; first exact: injf.
by case/negP: nBx; rewrite def_x (subsetP sBf) ?mem_imset.
Qed.

Definition perm_in := perm perm_in_inj.

Lemma perm_in_on : perm_on B perm_in.
Proof.
by apply/subsetP=> x; rewrite inE /= permE; case ifP => // _; case/eqP.
Qed.

Lemma perm_inE : {in B, perm_in =1 f}.
Proof. by move=> x Bx; rewrite /= permE Bx. Qed.

End PermIn.

Section MakeAut.

Variables (gT : finGroupType) (G : {group gT}) (f : {morphism G >-> gT}).
Implicit Type A : {set gT}.

Hypothesis injf : 'injm f.

Lemma morphim_fixP : forall A,
  A \subset G -> reflect (f @* A = A) (f @* A \subset A).
Proof.
rewrite /morphim => A sAG; have:= eqEcard (f @: A) A.
rewrite (setIidPr sAG) card_in_imset ?leqnn ?andbT  => [<-|]; first exact: eqP.
move/injmP: injf; apply: sub_in2; exact/subsetP.
Qed.

Hypothesis Gf : f @* G = G.

Lemma aut_closed : f @: G \subset G.
Proof. rewrite -morphimEdom; exact/morphim_fixP. Qed.

Definition aut := perm_in (injmP _ injf) aut_closed.

Lemma autE : {in G, aut =1 f}.
Proof. exact: perm_inE. Qed.

Lemma morphic_aut : morphic G aut.
Proof. by apply/morphicP=> x y Gx Gy /=; rewrite !autE ?groupM // morphM. Qed.

Lemma Aut_aut : aut \in Aut G.
Proof. by rewrite inE morphic_aut perm_in_on. Qed.

Lemma imset_autE : forall A, A \subset G -> aut @: A = f @* A.
Proof.
move=> A sAG; rewrite /morphim (setIidPr sAG).
apply: eq_in_imset; apply: sub_in1 autE; exact/subsetP.
Qed.

Lemma preim_autE : forall A, A \subset G -> aut @^-1: A = f @*^-1 A.
Proof.
move=> A sAG; apply/setP=> x; rewrite !inE permE /=.
by case Gx: (x \in G) => //; apply/negP=> Ax; rewrite (subsetP sAG) in Gx.
Qed.

End MakeAut.

Implicit Arguments morphim_fixP [gT G f].
Prenex Implicits aut morphim_fixP.

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
Proof. move=> x; rewrite morphimEdom; exact: normP. Qed.

Definition conj_aut x :=
  aut (injm_conj _) (norm_conj_dom (valP (insigd (group1 _) x))).

Lemma norm_conj_autE : {in 'N(G) & G, forall x y, conj_aut x y = y ^ x}.
Proof. by move=> x y nGx Gy; rewrite /= autE //= val_insubd nGx. Qed.

Lemma conj_autE : {in G &, forall x y, conj_aut x y = y ^ x}.
Proof. apply: sub_in11 norm_conj_autE => //; exact: subsetP (normG G). Qed.

Lemma conj_aut_morphM : {in 'N(G) &, {morph conj_aut : x y / x * y}}.
Proof.
move=> x y nGx nGy; apply/permP=> z /=; rewrite permM.
case Gz: (z \in G); last by rewrite !permE /= !Gz.
by rewrite !norm_conj_autE // (conjgM, memJ_norm, groupM).
Qed.

Canonical Structure conj_aut_morphism := Morphism conj_aut_morphM.

Lemma ker_conj_aut : 'ker conj_aut = 'C(G).
Proof.
apply/setP=> x; rewrite inE; case nGx: (x \in 'N(G)); last first.
  by symmetry; apply/idP=> cGx; rewrite (subsetP (cent_sub G)) in nGx.
rewrite 2!inE /=; apply/eqP/centP=> [cx1 y Gy | cGx].
  by rewrite /commute (conjgC y) -norm_conj_autE // cx1 perm1.
apply/permP=> y; case Gy: (y \in G); last by rewrite !permE Gy.
by rewrite perm1 norm_conj_autE // conjgE -cGx ?mulKg.
Qed.

End ConjugationMorphism.

Prenex Implicits conjgm conj_aut.

Reserved Notation "G \char H" (at level 70).

Section Characteristicity.

Variable gT : finGroupType.
Implicit Types A B : {set gT}.
Implicit Types G H K L : {group gT}.

Definition characteristic A B :=
  (A \subset B) && (forallb f, (f \in Aut B) ==> (f @: A \subset A)).

Infix "\char" := characteristic.

Lemma charP : forall H G,
  reflect [/\ H \subset G & forall f : {morphism G >-> gT},
                            'injm f -> f @* G = G -> f @* H = H]
          (H \char G).
Proof.
move=> H G; apply: (iffP andP); case=> sHG chHG; split=> //.
  move=> f injf Gf; apply/morphim_fixP=> //.
  by have:= forallP chHG (aut injf Gf); rewrite Aut_aut imset_autE.
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

Lemma char_trans : forall H G K, K \char H -> H \char G -> K \char G.
Proof.
move=> H G K; case/charP=> sKH chKH; case/charP=> sHG chHG.
apply/charP; split=> [|f injf Gf]; first exact: subset_trans sHG.
rewrite -{1}(setIidPr sKH) -(morphim_restrm sHG) chKH //.
  rewrite ker_restrm; case/trivgP: injf => ->; exact: subsetIr.
by rewrite morphim_restrm setIid chHG.
Qed.

Lemma char_norms : forall H G, H \char G -> 'N(G) \subset 'N(H).
Proof.
move=> H G; case/charP=> sHG chHG; apply/normsP=> x; move/normP=> Nx.
have:= chHG [morphism of conjgm G x] => /=.
by rewrite !morphimEsub //=; apply; rewrite // injm_conj.
Qed.

Lemma char_sub : forall A B, A \char B -> A \subset B.
Proof. by move=> A B; case/andP. Qed.

Lemma char_norm_trans : forall H G A,
  H \char G -> A \subset 'N(G) -> A \subset 'N(H).
Proof. move=> H G A; move/char_norms=> nHnG nGA; exact: subset_trans nHnG. Qed.

Lemma char_normal_trans : forall H G K, K \char H -> H <| G -> K <| G.
Proof.
move=> H G K chKH; case/andP=> sHG nHG.
by rewrite /normal (subset_trans (char_sub chKH)) // (char_norm_trans chKH).
Qed.

Lemma char_normal : forall H G, H \char G -> H <| G.
Proof.
by move=> H G; move/char_normal_trans; apply; apply/andP; rewrite normG.
Qed.

Lemma char_norm : forall H G, H \char G -> G \subset 'N(H).
Proof. by move=> H G; move/char_normal; case/andP. Qed.

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
move=> G H K chHG chKG; rewrite -norm_mulgenEl ?charMgen //.
by case/andP: (char_normal chKG) => _; apply: subset_trans; case/andP: chHG.
Qed.

Lemma lone_subgroup_char : forall G H,
  H \subset G -> (forall K, K \subset G -> K \isog H -> K \subset H) ->
  H \char G.
Proof.
move=> G H sHG Huniq; apply/charP; split=> // f injf Gf; apply/eqP.
have{injf} injf: {in H &, injective f}.
  by move/injmP: injf; apply: sub_in2; exact/subsetP.
have fH: f @* H = f @: H by rewrite /morphim (setIidPr sHG).
rewrite eqEcard {2}fH card_in_imset ?{}Huniq //=.
  by rewrite -{3}Gf morphimS.
rewrite isog_sym; apply/isogP.
exists [morphism of restrm sHG f] => //=; first exact/injmP.
by rewrite morphimEdom fH.
Qed.

End Characteristicity.

Notation "H \char G" := (characteristic H G) : group_scope.

Unset Implicit Arguments.
