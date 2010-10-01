(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat fintype finset.
Require Import fingroup perm morphism.

(******************************************************************************)
(* Group automorphisms and characteristic subgroups.                          *)
(* Unlike morphisms on a group G, which are functions of type gT -> rT, with  *)
(* a canonical structure of dependent type {morphim G >-> rT}, automorphisms  *)
(* are permutations of type {perm gT} contained in Aut G : {set {perm gT}}.   *)
(* This lets us use the finGroupType of {perm gT}. Note also that while       *)
(* morphisms on G are undefined outside G, automorphisms have their support   *)
(* in G, i.e., they are the identity ouside G.                                *)
(* Definitions:                                                               *)
(*    Aut G (or [Aut G]) == the automorphism group of G.                      *)
(*             [Aut G]%G == the group structure for Aut G.                    *)
(*            autm AutGa == the morphism on G induced by a, given             *)
(*                          AutGa : a \in Aut G.                              *)
(*       perm_in injf fA == the permutation with support B in induced by f,   *)
(*                          given injf : {in A &, injective f} and            *)
(*                          fA : f @: A \subset A.                            *)
(*           aut injf fG == the automorphism of G induced by the morphism f,  *)
(*                          given injf : 'injm f and fG : f @* G \subset G.   *)
(*    Aut_isom injf sDom == the injective homomorphism that maps Aut G to     *)
(*                          Aut (f @* G), with f : {morphism D >-> rT} and    *)
(*                          given injf: 'injm f and sDom : G \subset D.       *)
(*              conjgm G == the conjugation automorphism on G.                *)
(*             H \char G == H is a characteristic subgroup of G.              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

(***********************************************************************)
(* A group automorphism, defined as a permutation on a subset of a     *)
(* finGroupType that respects the morphism law.                        *)
(* Here perm_on is used as a closure rule for the set A.               *)
(***********************************************************************)

Section Automorphism.

Variable gT : finGroupType.
Implicit Type A : {set gT}.
Implicit Types a b : {perm gT}.

Definition Aut A := [set a | perm_on A a && morphic A a].

Lemma Aut_morphic : forall A a, a \in Aut A -> morphic A a.
Proof. by move=> A a; rewrite inE; case/andP. Qed.

Lemma out_Aut : forall A a x, a \in Aut A -> x \notin A -> a x = x.
Proof. by move=> A a x; case/setIdP=> Aa _; exact: out_perm. Qed.

Lemma eq_Aut : forall A, {in Aut A &, forall a b, {in A, a =1 b} -> a = b}.
Proof.
move=> A a g Aa Ag eqag; apply/permP=> x.
by case/orP: (orbN (x \in A)); [apply eqag | move/out_Aut=> out; rewrite !out].
Qed.

(* The morphism that is represented by a given element of Aut A. *)

Definition autm A a (AutAa : a \in Aut A) := morphm (Aut_morphic AutAa).
Lemma autmE : forall A a (AutAa : a \in Aut A), autm AutAa = a.
Proof. by []. Qed.

Canonical Structure autm_morphism A a aM :=
  Eval hnf in [morphism of @autm A a aM].

Section AutGroup.

Variable G : {group gT}.

Lemma Aut_group_set : group_set (Aut G).
Proof.
apply/group_setP; split=> [|a b].
  by rewrite inE perm_on1; apply/morphicP=> ? *; rewrite !permE.
rewrite !inE; case/andP=> Ga aM; case/andP=> Gb bM; rewrite perm_onM //=.
apply/morphicP=> x y Gx Gy; rewrite !permM (morphicP aM) //.
by rewrite (morphicP bM) ?perm_closed.
Qed.

Canonical Structure Aut_group := group Aut_group_set.

Variable (a : {perm gT}) (AutGa : a \in Aut G).
Notation f := (autm AutGa).
Notation fE := (autmE AutGa).

Lemma injm_autm : 'injm f.
Proof. apply/injmP; apply: in2W; exact: perm_inj. Qed.

Lemma ker_autm : 'ker f = 1. Proof. by case/trivgP: injm_autm. Qed.

Lemma im_autm : f @* G = G.
Proof.
apply/setP=> x; rewrite morphimEdom (can_imset_pre _ (permK a)) inE.
by have:= AutGa; rewrite inE; case/andP; move/perm_closed=> <-; rewrite permKV.
Qed.

Lemma Aut_closed : forall `(x \in G), a x \in G.
Proof. by move=> x Gx; rewrite -im_autm; exact: mem_morphim. Qed.

End AutGroup.

Lemma Aut1 : Aut 1 = 1.
Proof.
apply/trivgP; apply/subsetP=> a /= AutGa; apply/set1P.
apply: eq_Aut (AutGa) (group1 _) _ => x; move/set1P=> ->{x}.
by rewrite -(autmE AutGa) morph1 perm1.
Qed.

End Automorphism.

Notation "[ 'Aut' G ]" := (Aut_group G)
  (at level 0, format "[ 'Aut'  G ]") : subgroup_scope.
Notation "[ 'Aut' G ]" := (Aut G)
  (at level 0, only parsing) : group_scope.

Prenex Implicits Aut autm.

(* The permutation function (total on the underlying groupType) that is the *)
(* representant of a given morphism f with domain A in (Aut A).             *)

Section PermIn.

Variables (T : finType) (A : {set T}) (f : T -> T).

Hypotheses (injf : {in A &, injective f}) (sBf : f @: A \subset A).

Lemma perm_in_inj : injective (fun x => if x \in A then f x else x).
Proof.
move=> x y /=; wlog Ay: x y / y \in A.
  by move=> IH eqfxy; case: ifP (eqfxy); [symmetry | case ifP => //]; auto.
rewrite Ay; case: ifP => [Ax | nAx def_x]; first exact: injf.
by case/negP: nAx; rewrite def_x (subsetP sBf) ?mem_imset.
Qed.

Definition perm_in := perm perm_in_inj.

Lemma perm_in_on : perm_on A perm_in.
Proof.
by apply/subsetP=> x; rewrite inE /= permE; case ifP => // _; case/eqP.
Qed.

Lemma perm_inE : {in A, perm_in =1 f}.
Proof. by move=> x Ax; rewrite /= permE Ax. Qed.

End PermIn.

(* properties of injective endomorphisms *)

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

Section AutIsom.

Variables (gT rT : finGroupType) (G D : {group gT}) (f : {morphism D >-> rT}).

Hypotheses (injf : 'injm f) (sGD : G \subset D).
Let domG := subsetP sGD.

Lemma Aut_isom_subproof : forall a,
  {a' | a' \in Aut (f @* G) & a \in Aut G -> {in G, a' \o f =1 f \o a}}.
Proof.
move=> a; set Aut_a := autm (subgP (subg [Aut G] a)).
have aDom: 'dom (f \o Aut_a \o invm injf) = f @* G.
  rewrite /dom /= morphpre_invm -morphpreIim; congr (f @* _).
  by rewrite [_ :&: D](setIidPl _) ?injmK ?injm_autm ?im_autm.
have [af [def_af ker_af _ im_af]] := domP _ aDom.
have inj_a': 'injm af by rewrite ker_af !injm_comp ?injm_autm ?injm_invm.
have im_a': af @* (f @* G) = f @* G.
  by rewrite im_af !morphim_comp morphim_invm // im_autm.
pose a' := aut inj_a' im_a'; exists a' => [|AutGa x Gx]; first exact: Aut_aut.
have Dx := domG Gx; rewrite /= [a' _]autE ?mem_morphim //.
by rewrite def_af /= invmE // autmE subgK.
Qed.

Definition Aut_isom a := s2val (Aut_isom_subproof a).

Lemma Aut_Aut_isom : forall a, Aut_isom a \in Aut (f @* G).
Proof. by rewrite /Aut_isom => a; case: (Aut_isom_subproof a). Qed.

Lemma Aut_isomE : forall `(a \in Aut G) `(x \in G), Aut_isom a (f x) = f (a x).
Proof. by rewrite /Aut_isom => a; case: (Aut_isom_subproof a). Qed.

Lemma Aut_isomM : {in Aut G &, {morph Aut_isom: x y / x * y}}.
Proof.
move=> a b AutGa AutGb; apply: eq_Aut; rewrite ?groupM ?Aut_Aut_isom //.
move=> fx; case/morphimP=> x Dx Gx ->{fx}.
by rewrite permM !Aut_isomE ?groupM /= ?permM ?Aut_closed.
Qed.
Canonical Structure Aut_isom_morphism := Morphism Aut_isomM.

Lemma injm_Aut_isom : 'injm Aut_isom.
Proof.
apply/injmP=> a b AutGa AutGb eq_ab'; apply: (eq_Aut AutGa AutGb) => x Gx.
by apply: (injmP _ injf); rewrite ?domG ?Aut_closed // -!Aut_isomE //= eq_ab'.
Qed.

End AutIsom.

Section InjmAut.

Variables (gT rT : finGroupType) (G D : {group gT}) (f : {morphism D >-> rT}).

Hypotheses (injf : 'injm f) (sGD : G \subset D).
Let domG := subsetP sGD.

Lemma im_Aut_isom : Aut_isom injf sGD @* Aut G = Aut (f @* G).
apply/eqP; rewrite eqEcard; apply/andP; split.
  by apply/subsetP=> a'; case/morphimP=> a _ AutGa ->; exact: Aut_Aut_isom.
have inj_isom' := injm_Aut_isom (injm_invm injf) (morphimS _ sGD).
rewrite card_injm ?injm_Aut_isom // -(card_injm inj_isom') ?subset_leq_card //.
apply/subsetP=> a; case/morphimP=> a' _ AutfGa' def_a.
by rewrite -(morphim_invm injf sGD) def_a Aut_Aut_isom.
Qed.

Lemma Aut_isomP : isom (Aut G) (Aut (f @* G)) (Aut_isom injf sGD).
Proof. by apply/isomP; split; [exact: injm_Aut_isom | exact: im_Aut_isom]. Qed.

Lemma injm_Aut : Aut (f @* G) \isog Aut G.
Proof. by rewrite isog_sym (isom_isog _ _ Aut_isomP). Qed.

End InjmAut.

(* conjugation automorphism *)

Section ConjugationMorphism.

Variable gT : finGroupType.
Implicit Type A : {set gT}.

Definition conjgm of {set gT} := fun x y : gT => y ^ x.

Lemma conjgmE : forall A x y, conjgm A x y = y ^ x. Proof. by []. Qed.

Canonical Structure conjgm_morphism A x :=
  @Morphism _ _ A (conjgm A x) (in2W (fun y z => conjMg y z x)).

Lemma morphim_conj : forall A x B, conjgm A x @* B = (A :&: B) :^ x.
Proof. by []. Qed.

Variable G : {group gT}.

Lemma injm_conj : forall x, 'injm (conjgm G x).
Proof. move=> x; apply/injmP; apply: in2W; exact: conjg_inj. Qed.

Lemma im_conjgm_norm : forall x, x \in 'N(G) -> conjgm G x @* G = G.
Proof. move=> x; rewrite morphimEdom; exact: normP. Qed.

Definition conj_aut x :=
  aut (injm_conj _) (im_conjgm_norm (valP (insigd (group1 _) x))).

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

Lemma Aut_conj_aut : forall A, conj_aut @* A \subset Aut G.
Proof. move=> A; apply/subsetP=> p; case/imsetP=> x _ ->; exact: Aut_aut. Qed.

End ConjugationMorphism.

Prenex Implicits conjgm conj_aut.

Reserved Notation "G \char H" (at level 70).

(* Characteristic subgroup *)

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
move/(morphim_fixP injf _ sHG): (chHG _ injf (im_autm Af)).
by rewrite /morphim (setIidPr _).
Qed.

(* Characteristic subgroup properties : composition, relational properties *)

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

Section InjmChar.

Variables (aT rT : finGroupType) (D : {group aT}) (f : {morphism D >-> rT}).

Hypothesis injf : 'injm f.

Lemma injm_char : forall G H : {group aT},
  G \subset D -> H \char G -> f @* H \char f @* G.
Proof.
move=> G H sGD; case/charP=> sHG charH.
apply/charP; split=> [|g injg gfG]; first exact: morphimS.
have: 'dom (invm injf \o g \o f) = G.
  by rewrite /dom /= -(morphpreIim g) (setIidPl _) ?injmK // gfG morphimS.
case/domP=> h [_ ker_h _ im_h].
have hH: h @* H = H.
  apply: charH; first by rewrite ker_h !injm_comp ?injm_invm.
  by rewrite im_h !morphim_comp gfG morphim_invm.
rewrite /= -{2}hH im_h !morphim_comp morphim_invmE morphpreK //.
by rewrite (subset_trans _ (morphimS f sGD)) //= -{3}gfG !morphimS.
Qed.

End InjmChar.

Section CharInjm.

Variables (aT rT : finGroupType) (D : {group aT}) (f : {morphism D >-> rT}).
Hypothesis injf : 'injm f.

Lemma char_injm : forall G H : {group aT},
  G \subset D -> H \subset D -> (f @* H \char f @* G) = (H \char G).
Proof.
move=> G H sGD sHD; apply/idP/idP; last exact: injm_char.
by move/(injm_char (injm_invm injf)); rewrite !morphim_invm ?morphimS // => ->.
Qed.

End CharInjm.

Unset Implicit Arguments.
