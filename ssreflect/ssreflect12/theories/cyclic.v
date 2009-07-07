(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Properties of cyclic groups                                        *)
(*                                                                     *)
(***********************************************************************)
(* Definitions:                                                        *)
(* From groups.v:                                                      *)
(*   <[x]>         == the cycle (cyclic group) generated by x          *)
(*   #[x]          == the order of x, i.e., the cardinal of <[x]>.     *)
(* In this file:                                                       *)
(*   cyclic G      <=> G is a cyclic group.                            *)
(*   generator G x <=> x is a generator of the (cyclic) group G.       *)
(*   Zpm x         == the isomorphism between the additive group of    *)
(*                    integers mod #[x], and the group <[x]>           *)
(*   cyclem x n    == the endomorphism y |-> y ^+ n of <[x]>           *)
(*   Zp_unitm x    == the isomorphism from the multiplicative group of *)
(*                    the units of the ring of integers mod #[x], with *)
(*                    the group Aut <[x]> of automorphisms of <[x]>.   *)
(*                    (Zp_unitm x map u to cyclem x u)                *)
(* Basic results for these notions, plus the classical result that     *)
(* any finite group isomorphic to a subggroup of a field is cycle,     *)
(* and the corollary that Aut G is cyclic when G is of prime order.    *)
(***********************************************************************)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat.
Require Import seq fintype div bigops prime ssralg poly.
Require Import finset groups morphisms automorphism normal perm zmodp.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

(***********************************************************************)
(*                                                                     *)
(*  Cyclic groups.                                                     *)
(*                                                                     *)
(***********************************************************************)

Section Cyclic.

Variable gT : finGroupType.
Implicit Types a x y : gT.
Implicit Types A B : {set gT}.
Implicit Types G H : {group gT}.

Definition cyclic A := existsb x, A == <[x]>.

Lemma cyclicP : forall A, reflect (exists x, A = <[x]>) (cyclic A).
Proof. move=> A; apply: (iffP existsP) => [] [x]; exists x; exact/eqP. Qed.

Lemma cycle_cyclic : forall x, cyclic <[x]>.
Proof. by move=> x; apply/cyclicP; exists x. Qed.

Lemma cyclic1 : cyclic [1 gT].
Proof. by rewrite -cycle1 cycle_cyclic. Qed.

Section Zpm.

Variable a : gT.

Definition Zpm (i : 'I_#[a]) := a ^+ i.

Lemma ZpmM : {in Zp #[a] &, {morph Zpm : x y / x * y}}.
Proof. by move=> i j _ _; rewrite /Zpm /= expg_mod_order expgn_add. Qed.

Canonical Structure Zpm_morphism := Morphism ZpmM.

Lemma morphim_Zpm : Zpm @* Zp #[a] = <[a]>.
Proof.
apply/eqP; rewrite morphimEdom eq_sym eqEcard andbC.
rewrite -[#|<[a]>|]card_Zp leq_imset_card.
apply/subsetP=> x; case/cyclePmin=> i lt_i_a ->.
by apply/imsetP; exists (Ordinal lt_i_a); rewrite ?inE.
Qed.

Lemma Zpm_inj : injective Zpm.
Proof.
apply/injectiveP; apply/card_uniqP; rewrite size_map -cardE card_ord /=.
rewrite {5}/order -morphim_Zpm morphimEdom /=; apply: eq_card => x.
by apply/imageP/imsetP=> [] [i _ ->] /=; exists i; rewrite ?inE.
Qed.

Lemma injm_Zpm : 'injm Zpm.
Proof. apply/injmP; exact: (in2W Zpm_inj). Qed.

Lemma eq_expg_mod_order : forall m n,
  (a ^+ m == a ^+ n) = (m == n %[mod #[a]]).
Proof.
move=> m n; symmetry; pose Za := inZp (order_gt0 a).
by rewrite -[_ == _](inj_eq Zpm_inj (Za m) (Za n)) /Zpm !expg_mod_order.
Qed.

Lemma Zp_isom : isom (Zp #[a]) <[a]> Zpm.
Proof. by apply/isomP; rewrite injm_Zpm morphim_Zpm. Qed.

Lemma Zp_isog : isog (Zp #[a]) <[a]>.
Proof. exact: isom_isog Zp_isom. Qed.

Lemma cycle_decomp : forall b,
  b \in <[a]> -> {m : nat | m < #[a] & a ^+ m = b}.
Proof.
move=> b; rewrite -morphim_Zpm; move/(invmK injm_Zpm).
by case: {+}(invm _ b) => m; exists m.
Qed.

End Zpm.

(***********************************************************************)
(*                                                                     *)
(*        Central and direct product of cycles                         *)
(*                                                                     *)
(***********************************************************************)

Lemma cents_cycle : forall a b, commute a b -> <[a]> \subset 'C(<[b]>).
Proof.
move=> a b cab; rewrite gen_subG centsC cent_set1 cycle_subG; exact/cent1P.
Qed.

Lemma cycle_abelian : forall a, abelian <[a]>.
Proof. move=> a; exact: cents_cycle. Qed.

Lemma cyclic_abelian : forall A, cyclic A -> abelian A.
Proof. move=> A; case/cyclicP=> a ->; exact: cycle_abelian. Qed.

Lemma cycleMsub : forall a b,
  commute a b -> coprime #[a] #[b] -> <[a]> \subset <[a * b]>.
Proof.
move=> a b cab co_ab; apply/subsetP=> x; case/cycleP=> k ->{x}.
apply/cycleP; exists (chinese #[a] #[b] k 0); symmetry.
rewrite expMgn // -expg_mod_order chinese_modl // expg_mod_order.
by rewrite /chinese addn0 -mulnA mulnCA expgn_mul expg_order exp1gn mulg1.
Qed.

Lemma cycleM : forall a b,
  commute a b -> coprime #[a] #[b] -> <[a * b]> = <[a]> * <[b]>.
Proof.
move=> a b cab co_ab; apply/eqP.
rewrite eqEsubset -(cent_mulgenEl (cents_cycle cab)).
rewrite mulgen_subG {3}cab !cycleMsub // 1?coprime_sym //.
by rewrite -genM_mulgen cycle_subG mem_gen // mem_imset2 ?cycle_id.
Qed.

(***********************************************************************)
(*                                                                     *)
(*        Order properties                                             *)
(*                                                                     *)
(***********************************************************************)

Lemma order_dvdn : forall a n, (#[a] %| n) = (a ^+ n == 1).
Proof. by move=> a n; rewrite (eq_expg_mod_order a n 0) mod0n. Qed.

Lemma order_inf : forall a n, a ^+ n.+1 == 1 -> #[a] <= n.+1.
Proof. move=> a n; rewrite -order_dvdn; exact: dvdn_leq. Qed.

Lemma order_eq1 : forall a, (#[a] == 1%N) = (a == 1).
Proof. by move=> a; rewrite -dvdn1 order_dvdn expg1. Qed.

Lemma cycle_eq1 : forall a, (<[a]> == 1) = (a == 1).
Proof. by move=> a; rewrite -order_eq1 trivg_card1. Qed.

Lemma order_dvdG : forall (G : {group gT}) a, a \in G -> #[a] %| #|G|.
Proof. by move=> G a Ga; apply: cardSg; rewrite cycle_subG. Qed.

Lemma orderXdvd : forall a n, #[a ^+ n] %| #[a].
Proof. move=> a n; apply: order_dvdG; exact: mem_cycle. Qed.

Lemma orderXgcd : forall a n, #[a ^+ n] = #[a] %/ gcdn #[a] n.
Proof.
move=> a n; apply/eqP; rewrite eqn_dvd; apply/andP; split.
  rewrite order_dvdn -expgn_mul -gcdn_divnC //.
  by rewrite expgn_mul expg_order exp1gn.
case: (posnP n) => [-> | n_gt0]; first by rewrite gcdn0 divnn order_gt0 dvd1n.
rewrite -(dvdn_pmul2r n_gt0) divn_mulAC ?dvdn_gcdl // dvdn_lcm.
by rewrite order_dvdn mulnC expgn_mul expg_order eqxx dvdn_mulr.
Qed.

Lemma orderXdiv : forall a n, n %| #[a] -> #[a ^+ n] = #[a] %/ n.
Proof.
by move=> a n; case/dvdnP=> q defq; rewrite orderXgcd {2}defq gcdnC gcdn_mull.
Qed.

Lemma orderM : forall a b : gT,
  commute a b -> coprime #[a] #[b] -> #[a * b] = (#[a] * #[b])%N.
Proof. by move=> a b Hcom Hcop; rewrite -coprime_cardMg -?cycleM. Qed.

(***********************************************************************)
(*                                                                     *)
(*        Generator                                                    *)
(*                                                                     *)
(***********************************************************************)

Definition generator (A : {set gT}) a := A == <[a]>.

Lemma generator_cycle : forall a, generator <[a]> a.
Proof. by move=> a; exact: eqxx. Qed.

Lemma cycle_generator : forall a x, generator <[a]> x -> x \in <[a]>.
Proof. move=> a x; move/(<[a]> =P _)->; exact: cycle_id. Qed.

Lemma generator_order : forall a b,
  generator <[a]> b -> #[a] = #[b].
Proof. by rewrite /order => a b; move/(<[a]> =P _)->. Qed.

End Cyclic.

(* Just for fun Euler's theorem *)

Theorem Euler: forall a n, coprime a n -> a ^ phi n  = 1 %[mod n].
Proof.
move=> a n; case: (posnP n) => [-> //|n_gt0] co_a_n; pose n0 := PosNat n_gt0.
have Ua: coprime n0 (inZp n_gt0 a) by rewrite coprime_sym coprime_modl.
have: ZpUnit Ua ^+ phi n0 == 1.
  by rewrite -card_Zp_units -order_dvdn order_dvdG ?inE.
by rewrite -2!val_eqE /= (@Zp_units_expgn n0) /= modn_exp; move/eqP.
Qed.

Section CyclicSubGroup.

Variable gT : finGroupType.

(*  G. 1.3.1 (i) *)

Lemma cycle_sub_group : forall (a : gT) m, m %| #[a] ->
  [set H : {group gT} | (H \subset <[a]>) && (#|H| == m)]
     = [set <[a ^+ (#[a] %/ m)]>%G].
Proof.
move=> a m Hdiv.
have Hpos: 0 < m by apply (dvdn_gt0 (order_gt0 a) Hdiv).
have Hcardm: #|<[a ^+ (#[a] %/ m)]>| == m.
  rewrite [#|_|]orderXgcd -(divn_pmul2r Hpos) muln_gcdl divnK // gcdnC.
  by rewrite gcdn_mulr mulKn.
apply/eqP; rewrite eqEsubset sub1set inE /= cycleX Hcardm !andbT.
apply/subsetP=> X; rewrite in_set1 inE -val_eqE /= eqEcard (eqP Hcardm).
case/andP=> sXa; move/eqP=> oX; rewrite oX leqnn andbT.
apply/subsetP=> x Xx; case/cycleP: (subsetP sXa _ Xx) => k def_x.
have: (x ^+ m == 1)%g by rewrite -oX -order_dvdn cardSg // gen_subG sub1set.
rewrite def_x -expgn_mul -order_dvdn -[#[a]](LaGrange sXa) -oX mulnC.
rewrite dvdn_pmul2r // mulnK //; case/dvdnP=> i ->{def_x k}.
by rewrite mulnC expgn_mul groupX // cycle_id.
Qed.

Lemma cycle_subgroup_char : forall a (H : {group gT}),
  H \subset <[a]> -> H \char <[a]>.
Proof.
move=> a H sHa; apply: lone_subgroup_char => // J sJa isoJH.
have dvHa: #|H| %| #[a] by exact: cardSg.
have{dvHa} Huniq := esym (cycle_sub_group dvHa).
move/setP: Huniq => Huniq; move: (Huniq H) (Huniq J); rewrite !inE /=.
by rewrite sHa sJa (isog_card isoJH) eqxx; do 2!move/eqP <-.
Qed.

End CyclicSubGroup.

Section MorphicImage.

Variables aT rT : finGroupType.
Variables (D : {group aT}) (f : {morphism D >-> rT}) (x : aT).
Hypothesis Dx : x \in D.

Lemma morphim_cycle : f @* <[x]> = <[f x]>.
Proof. by rewrite morphim_gen (sub1set, morphim_set1). Qed.

Lemma morph_order : #[f x] %| #[x].
Proof. by rewrite order_dvdn -morphX // expg_order morph1. Qed.

Lemma morph_generator : forall A, generator A x -> generator (f @* A) (f x).
Proof. by move=> A; move/(A =P _)->; rewrite /generator morphim_cycle. Qed.

End MorphicImage.

Section CyclicProps.

Variables gT : finGroupType. 
Implicit Types G H K : {group gT}.
Implicit Types aT rT : finGroupType.

Lemma cyclicS : forall G H, H \subset G -> cyclic G -> cyclic H. 
Proof.
move=> G H HsubG; case/cyclicP=> x gex; apply/cyclicP.
exists (x ^+ (#[x] %/ #|H|)); apply: congr_group; apply/set1P.
by rewrite -cycle_sub_group /order -gex ?cardSg // inE HsubG eqxx.
Qed.

Lemma cyclicJ:  forall G x, cyclic (G :^ x) = cyclic G.
Proof.
move=> G x; apply/cyclicP/cyclicP=> [[y] | [y ->]].
  by move/(canRL (conjsgK x)); rewrite -cycleJ; exists (y ^ x^-1).
by exists (y ^ x); rewrite cycleJ.
Qed.

Lemma morphim_cyclic :  forall rT G H (f : {morphism G >-> rT}),
  cyclic H -> cyclic (f @* H).
Proof.
move=> rT G H f cH; wlog sHG: H cH / H \subset G.
  by rewrite -morphimIdom; apply; rewrite (cyclicS _ cH, subsetIl) ?subsetIr.
case/cyclicP: cH sHG => x ->; rewrite gen_subG sub1set => Gx.
by apply/cyclicP; exists (f x); rewrite morphim_cycle.
Qed.

Lemma quotient_cycle : forall x H, x \in 'N(H) -> <[x]> / H = <[coset H x]>.
Proof. move=> x H; exact: morphim_cycle. Qed.

Lemma quotient_cyclic : forall G H, cyclic G -> cyclic (G / H).
Proof. move=> G H; exact: morphim_cyclic. Qed.

Lemma quotient_generator : forall x G H,
  x \in 'N(H) -> generator G x -> generator (G / H) (coset H x).
Proof. by move=> x G H Nx; apply: morph_generator. Qed.

Lemma prime_cyclic : forall G, prime #|G| -> cyclic G.
Proof.
move=> G pG; case: (pickP (mem G^#)) => [x Hx| Hx]; last first.
  by move: pG; rewrite (cardsD1 1 G) group1 (eq_card0 Hx).
move: (Hx); rewrite /= in_setD1; case/andP => xD1; rewrite -cycle_subG=> xIG.
case/primeP: pG => _; move/(_ _ (cardSg xIG)); case/orP;  move/eqP.
  by rewrite (cardsD1 1) (cardsD1 x) group1 in_setD1 xD1 cycle_id.
move=> CxG; apply/cyclicP; exists x.
by apply/eqP; rewrite eq_sym eqEcard // CxG leqnn andbT.
Qed.

Lemma cyclic_small : forall G, #|G| <= 3 -> cyclic G.
Proof.
move=> G; rewrite 4!(ltnS, leq_eqVlt) -trivg_card_le1 orbA orbC.
case/predU1P=> [->|oG]; first exact: cyclic1.
by apply: prime_cyclic; case/pred2P: oG => ->.
Qed.

End CyclicProps.

Section IsoCyclic.

Variables gT rT : finGroupType.
Implicit Types G H : {group gT}.
Implicit Types M : {group rT}.

Lemma injm_cyclic :  forall G H (f : {morphism G >-> rT}),
  'injm f -> H \subset G -> cyclic (f @* H) = cyclic H.
Proof.
move=> G H f injf sHG; apply/idP/idP; last exact: morphim_cyclic.
rewrite -{2}(morphim_invm injf sHG); exact: morphim_cyclic.
Qed.

Lemma isog_cyclic :forall G M, G \isog M -> cyclic G = cyclic M.
Proof. by move=> G M; case/isogP=> f injf <-; rewrite injm_cyclic. Qed.

Lemma isog_cyclic_card : forall G M,
  cyclic G -> isog G M = cyclic M && (#|M| == #|G|).
Proof.
move=> G H cycG; apply/idP/idP=> [isoGM | ].
  by rewrite (isog_card isoGM) -(isog_cyclic isoGM) cycG /=.
case/cyclicP: cycG => x ->{G}; case/andP; case/cyclicP=> y ->{M} oy.
apply: isog_trans (isog_symr _) (Zp_isog y).
by rewrite ((order_pos_nat y =P order_pos_nat x) _) // Zp_isog.
Qed.

Lemma injm_generator : forall G H (f : {morphism G >-> rT}) x,
    'injm f -> x \in G -> H \subset G ->
  generator (f @* H) (f x) = generator H x.
Proof.
move=> G H f x injf Gx sHG; apply/idP/idP; last exact: morph_generator.
rewrite -{2}(morphim_invm injf sHG) -{2}(invmE injf Gx).
apply: morph_generator; exact: mem_morphim.
Qed.

End IsoCyclic.

(***********************************************************************)
(*                                                                     *)
(*       Automorphisms of cyclic groups                                *)
(*                                                                     *)
(***********************************************************************)

Section CyclicAutomorphism.

Variable gT : finGroupType.

Section CycleAutomorphism.

Variable a : gT.

Section CycleMorphism.

Variable n : nat.

Definition cyclem of gT := fun x : gT => x ^+ n.

Lemma cyclemM : {in <[a]> & , {morph cyclem a : x y / x * y}}.
Proof.
move=> x y ax ay; apply: expMgn; exact: (centsP (cycle_abelian a)).
Qed.

Canonical Structure cyclem_morphism := Morphism cyclemM.

End CycleMorphism.

Section ZpUnitMorphism.

Variable u : Zp_unit #[a].

Lemma injm_cyclem : 'injm (cyclem u a).
Proof.
apply/subsetP=> x; case/setIdP=> ax; rewrite !inE -order_dvdn.
rewrite -order_eq1 -dvdn1; move/eqnP: (valP u) => /= <-.
by rewrite dvdn_gcd order_dvdG.
Qed.

Lemma cyclem_dom : cyclem u a @* <[a]> = <[a]>.
Proof.
apply/morphim_fixP=> //; first exact: injm_cyclem.
by rewrite morphim_cycle ?cycle_id ?cycleX.
Qed.

Definition Zp_unitm := aut injm_cyclem cyclem_dom.

End ZpUnitMorphism.

Lemma Zp_unitmM : {in Zp_units #[a] &, {morph Zp_unitm : u v / u * v}}.
Proof.
move=> u v _ _; apply: (eq_Aut (Aut_aut _ _)) => [|x a_x].
  by rewrite groupM ?Aut_aut.
rewrite permM !autE ?groupX //= /cyclem -expgn_mul.
by rewrite -expg_mod_order modn_dvdm ?expg_mod_order // order_dvdG.
Qed.

Canonical Structure Zp_unit_morphism := Morphism Zp_unitmM.

Lemma injm_Zp_unitm : 'injm Zp_unitm.
Proof.
apply/subsetP=> u; case/morphpreP=> _; move/set1P=> /= um1.
have{um1}: Zp_unitm u a == Zp_unitm 1 a by rewrite um1 morph1.
by rewrite !autE ?cycle_id // eq_expg_mod_order !modZp inE.
Qed.

Lemma generator_coprime : forall m, generator <[a]> (a ^+ m) = coprime #[a] m.
Proof.
move=> m; rewrite /generator eq_sym eqEcard cycleX -/#[a] [#|_|]orderXgcd /=.
apply/idP/idP=> [le_a_am|co_am]; last by rewrite (eqnP co_am) divn1.
have am_gt0: 0 < gcdn #[a] m by rewrite gcdn_gt0 order_gt0.
by rewrite /coprime eqn_leq am_gt0 andbT -(@leq_pmul2l #[a]) ?muln1 -?leq_divr.
Qed.

Lemma morphim_Zp_unitm : Zp_unitm @* Zp_units #[a] = Aut <[a]>.
Proof.
rewrite morphimEdom; apply/setP=> f; apply/imsetP/idP=> [[u _ ->] | Af].
  exact: Aut_aut.
pose n := invm (injm_Zpm a) (f a).
have a_fa: <[a]> = <[f a]>.
  by rewrite -(autmE Af) -morphim_cycle ?autm_dom ?cycle_id.
have def_n: a ^+ n = f a.
  by rewrite -/(Zpm n) invmK // morphim_Zpm a_fa cycle_id.
have co_a_n : coprime #[a] n by rewrite -generator_coprime def_n; exact/eqP.
exists (ZpUnit co_a_n); rewrite ?inE //.
apply: eq_Aut (Af) (Aut_aut _ _) _ => x ax.
rewrite autE //= /cyclem; case/cycleP: ax => k ->{x}.
by rewrite -(autmE Af) morphX ?cycle_id //= autmE -def_n -!expgn_mul mulnC.
Qed.

Lemma Zp_unit_isom : isom (Zp_units #[a]) (Aut <[a]>) Zp_unitm.
Proof. by apply/isomP; rewrite ?injm_Zp_unitm ?morphim_Zp_unitm. Qed.

Lemma Zp_unit_isog : isog (Zp_units #[a]) (Aut <[a]>).
Proof. exact: isom_isog Zp_unit_isom. Qed.

Lemma card_Aut_cycle : #|Aut <[a]>| = phi #[a].
Proof. by rewrite -(isog_card Zp_unit_isog) card_Zp_units. Qed.

Lemma phi_gen : phi #[a] = #|[set x | generator <[a]> x]|.
Proof.
rewrite -(card_injm (injm_invm (injm_Zpm a))) /= ?morphim_Zpm.
  rewrite -card_Zp_units cardsE card_sub morphim_invmE.
  by apply: eq_card => d; rewrite !inE /= -generator_coprime.
apply/subsetP=> x; rewrite inE; exact: cycle_generator.
Qed.

Lemma Aut_cycle_abelian : abelian (Aut <[a]>).
Proof. by rewrite -morphim_Zp_unitm morphim_abelian ?Zp_units_abelian. Qed.

End CycleAutomorphism.

Variable G : {group gT}.

Lemma Aut_cyclic_abelian : cyclic G -> abelian (Aut G).
Proof. case/cyclicP=> x ->; exact: Aut_cycle_abelian. Qed.

Lemma card_Aut_cyclic : cyclic G -> #|Aut G| = phi #|G|.
Proof. case/cyclicP=> x ->; exact: card_Aut_cycle. Qed.

Lemma sum_ncycle_phi :
  \sum_(d < #|G|.+1) #|[set <[x]> | x <- G, #[x] == d]| * phi d = #|G|.
Proof.
pose h (x : gT) : 'I_#|G|.+1 := inord #[x].
symmetry; rewrite -{1}sum1_card (partition_big h xpredT) //=.
apply: eq_bigr => d _; set Gd := finset _.
rewrite -sum_nat_const sum1dep_card -sum1_card (_ : finset _ = Gd); last first.
  apply/setP=> x; rewrite !inE; case Gx: (x \in G) => //.
  by rewrite /eq_op /= inordK // ltnS subset_leq_card ?cycle_subG.
rewrite (partition_big_imset cycle) {}/Gd; apply: eq_bigr => C /=.
case/imsetP=> x; case/setIdP=> Gx; move/eqP=> <- -> {C d}.
rewrite sum1dep_card phi_gen; apply: eq_card => y; rewrite !inE /generator.
move: Gx; rewrite andbC eq_sym -!cycle_subG /order.
by case: (<[x]> == <[y]>) / (<[x]> =P <[y]>) => // -> ->; exact: eqxx.
Qed.

End CyclicAutomorphism.

Lemma sum_phi_dvd : forall n, \sum_(d < n.+1 | d %| n) phi d = n.
Proof.
move=> n; rewrite big_mkcond /=.
case: (posnP n) => [-> | n_gt0]; first by rewrite big_ord_recl big_ord0.
pose n0 := PosNat n_gt0; pose x1 : 'I_n0 := Zp_gen.
have ox1 : #[x1] = n by rewrite /order -Zp_cycle card_Zp.
rewrite -{8}ox1 -[#[_]]sum_ncycle_phi [#|_|]ox1; apply: eq_bigr => d _.
rewrite -{2}ox1; case: ifP => [|ndv_dG]; last first.
  rewrite eq_card0 // => C; apply/imsetP=> [[x]]; case/setIdP=> Gx oxd _{C}.
  by rewrite -(eqP oxd) order_dvdG in ndv_dG.
move/cycle_sub_group; set Gd := [set _] => def_Gd.
rewrite (_ : _ @: _ = @gval _ @: Gd); first by rewrite imset_set1 cards1 mul1n.
apply/setP=> C; apply/idP/imsetP=> [| [gC GdC ->{C}]].
  case/imsetP=> x; case/setIdP=> _ oxd ->; exists <[x]>%G => //.
  by rewrite -def_Gd inE -Zp_cycle subsetT.
have:= GdC; rewrite -def_Gd; case/setIdP=> _; move/eqP=> <-.
by rewrite (set1P GdC) /= mem_imset // inE eqxx (mem_cycle x1).
Qed.

Section FieldMulCyclic.

(* A classic application to finite multiplicative subgroups of fields. *)
Import GRing.Theory.

Variables (gT : finGroupType) (G : {group gT}).

Lemma order_inj_cyclic :
  {in G &, forall x y, #[x] = #[y] -> <[x]> = <[y]>} -> cyclic G.
Proof.
move=> ucG; apply: negbNE (contra _ (negbT (ltnn #|G|))) => ncG.
rewrite -{2}[#|G|]sum_phi_dvd big_mkcond (bigD1 ord_max) ?dvdnn //=.
rewrite -{1}[#|G|]sum_ncycle_phi (bigD1 ord_max) //= -addSn leq_add //.
  rewrite eq_card0 ?phi_gt0 ?cardG_gt0 // => C.
  apply/imsetP=> [[x]]; case/setIdP=> Gx; move/eqP=> oxG; case/cyclicP: ncG.
  by exists x; apply/eqP; rewrite eq_sym eqEcard cycle_subG Gx -oxG /=.
apply: (big_rel (fun a b => a <= b)) => // [*|d _]; first exact: leq_add.
set Gd := _ @: _; case: (set_0Vmem Gd) => [-> | [C]]; first by rewrite cards0.
rewrite {}/Gd; case/imsetP=> x; case/setIdP=> Gx; move/eqP=> <- _ {C d}.
rewrite order_dvdG // (@eq_card1 _ <[x]>) ?mul1n // => C.
apply/idP/eqP=> [|-> {C}]; last by rewrite mem_imset // inE Gx eqxx.
by case/imsetP=> y; case/setIdP=> Gy; move/eqP; move/ucG->.
Qed.

Lemma div_ring_mul_group_cyclic : forall (R : unitRingType) (f : gT -> R),
    f 1 = 1%R -> {in G &, {morph f : u v / u * v >-> (u * v)%R}} ->
    {in G^#, forall x, GRing.unit (f x - 1)%R} ->
  abelian G -> cyclic G.
Proof.
move=> R f f1 fM f1P abelG.
have fX: forall n, {in G, {morph f : u / u ^+ n >-> (u ^+ n)%R}}.
  by case=> // n x Gx; elim: n => //= n IHn; rewrite expgS fM ?groupX ?IHn.
have fU: forall x, x \in G -> GRing.unit (f x).
  move=> x Gx; apply/unitrP.
  by exists (f x^-1); rewrite -!fM ?groupV ?gsimp.
apply: order_inj_cyclic => x y Gx Gy; set n := #[x] => yn.
apply/eqP; rewrite eq_sym eqEcard -[#|_|]/n yn leqnn andbT cycle_subG /=.
suff{y Gy yn} ->: <[x]> = G :&: [set z | #[z] %| n] by rewrite !inE Gy yn /=.
apply/eqP; rewrite eqEcard subsetI cycle_subG {}Gx /= cardE; set rs := enum _.
apply/andP; split; first by apply/subsetP=> y xy; rewrite inE order_dvdG.
pose P : {poly R} := ('X^n - 1)%R; have n_gt0: n > 0 by exact: order_gt0.
have szP: size P = n.+1 by rewrite size_addl size_polyXn ?size_opp ?size_poly1.
rewrite -ltnS -szP -(size_map f) max_ring_poly_roots -?size_poly_eq0 ?{}szP //.
  apply/allP=> fy; case/mapP=> y; rewrite mem_enum !inE order_dvdn.
  case/andP=> Gy; move/eqP=> yn1 ->{fy}; apply/eqP.
  by rewrite !(horner_lin, hornerXn) -fX // yn1 f1 subrr.
have: uniq rs by exact: enum_uniq.
have: all (mem G) rs by apply/allP=> y; rewrite mem_enum; case/setIP.
elim: rs => //= y rs IHrs; case/andP=> Gy Grs; case/andP=> y_rs; rewrite andbC.
move/IHrs=> -> {IHrs}//; apply/allP=> fz; case/mapP=> z rs_z ->{fz}.
have{Grs} Gz := allP Grs z rs_z; rewrite /diff_root -!fM // (centsP abelG) //.
rewrite eqxx -[f y]mul1r -(mulgKV y z) fM ?groupM ?groupV //=.
rewrite -mulNr -mulr_addl unitr_mull ?fU ?f1P // !inE.
by rewrite groupM ?groupV // andbT -eq_mulgV1; apply: contra y_rs; move/eqP <-.
Qed.

Lemma field_mul_group_cyclic : forall (F : fieldType) (f : gT -> F),
    {in G &, {morph f : u v / u * v >-> (u * v)%R}} ->
    {in G, forall x, f x = 1%R <-> x = 1} ->
  cyclic G.
Proof.
move=> F f fM f1P; have f1 : f 1 = 1%R by exact/f1P.
apply: (div_ring_mul_group_cyclic f1 fM) => [x|].
  case/setD1P=> x1 Gx; rewrite unitfE; apply: contra x1.
  by rewrite subr_eq0; move/eqP; move/f1P->.
apply/centsP=> x Gx y Gy; apply/commgP; apply/eqP.
apply/f1P; rewrite ?fM ?groupM ?groupV //.
by rewrite mulrCA -!fM ?groupM ?groupV // mulKg mulVg.
Qed.

End FieldMulCyclic.

Section AutPrime.

Variable gT : finGroupType.

Lemma Aut_prime_cycle_cyclic : forall a : gT, prime #[a] -> cyclic (Aut <[a]>).
Proof.
move=> a pr_a; pose ff f := invm (injm_Zp_unitm a) f : Fp_field pr_a.
apply: (@field_mul_group_cyclic _ _ _ ff) => [f g Af Ag | f Af].
  by apply: val_inj; rewrite /ff morphM ?morphim_Zp_unitm.
split=> [/= ff1 |->]; last by apply: val_inj; rewrite /ff morph1.
apply: (injm1 (injm_invm (injm_Zp_unitm a))).
  by rewrite /= morphim_Zp_unitm.
by do 2!apply: val_inj; move/(congr1 val): ff1.
Qed.

Lemma Aut_prime_cyclic : forall G : {group gT}, prime #|G| -> cyclic (Aut G).
Proof.
move=> G pr_G; case/cyclicP: (prime_cyclic pr_G) (pr_G) => x ->.
exact: Aut_prime_cycle_cyclic.
Qed.

End AutPrime.
