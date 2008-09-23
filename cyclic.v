(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Definition of cyclic group                                         *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat.
Require Import seq fintype div prime.
Require Import finset groups morphisms automorphism normal group_perm zp fp.

(* Require Import paths connect bigops. *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Phi.

(***********************************************************************)
(*                                                                     *)
(*  Euler phi function                                                 *)
(*                                                                     *)
(***********************************************************************)

Definition phi n := #|([eta coprime n] : pred 'I_n)|.

Lemma cardphi : forall p, #|fp_mul_finGroupType p| = (phi p).
Proof.  by move=> p; rewrite card_sub. Qed.

Lemma phi0 : phi 0 = 0.
Proof.
by rewrite /phi eq_card0 //; case; case=> [|n]; case/negP; rewrite ltn0.
Qed.

Lemma phi_mult: forall m n,
  coprime m n -> phi (m * n) = phi m * phi n.
Proof.
move=> m n Hcop.
case: (posnP m) => [-> | mpos]; first by rewrite mul0n phi0 mul0n.
case: (posnP n) => [-> | npos]; first by rewrite muln0 phi0 muln0.
have:= @rho_isom (PosNat mpos) (PosNat npos) Hcop.
by move/isom_card; rewrite !cardsT card_prod !cardphi.
Qed.

Lemma phi_prime_k: forall p k (H:prime p),
  phi (p ^ k.+1) = (p ^ (k.+1)) - (p ^ k).
Proof.
move => p k Hp; have Hp0: (0 < p) by exact: (ltn_0prime Hp).
apply: (canRL (addnK _)); rewrite /phi /= {7}expnS.
have Hf: forall x : fzp (p ^ k), p * x < p * (p ^ k).
  by move => [n1 /= Hn1]; rewrite /= ltn_pmul2l.
pose f (x : fzp (p ^ k)) := Ordinal (Hf x).
have injF: injective f.
  move=> [x Hx] [y Hy] [Hxy]; apply: val_inj => /=.
  by apply/eqP; rewrite -(@eqn_pmul2l p) // Hxy.
rewrite -{1}(card_ord (p ^ k)) -(card_image injF ).
rewrite -{5}(card_ord (p * p ^ k)) addnC.
set a := image _ _; apply: etrans (cardC a); congr addn.
apply: eq_card => [[x Hx]] /=.
rewrite [_ \in _]coprime_pexpl // prime_coprime //=.
suff: p %| x = ~~ predC a (Ordinal Hx) by move=> ->; apply/negPn/idP.
apply/idP/idP.
  move/dvdnP=> [y Dx]; have Hy := Hx.
  rewrite Dx mulnC ltn_pmul2l /= in Hy => //.
  apply/negPn; apply/imageP.
  exists (Ordinal Hy) => //.
  by rewrite /f /=; apply: val_inj; rewrite /= mulnC.
move/negPn; move/imageP=> [y Hy]; rewrite/f; move/eqP=> /= HH.
by apply/dvdnP; exists (nat_of_ord y); rewrite mulnC; apply/eqP.
Qed.

End Phi.

(***********************************************************************)
(*                                                                     *)
(*  Cyclic group                                                       *)
(*                                                                     *)
(***********************************************************************)

Import GroupScope.

Section Cyclic.

Variable gT : finGroupType.
Implicit Types a x y : gT.
Implicit Types A B : {set gT}.
Implicit Types G H : {group gT}.

Definition cyclic A := existsb x, A == <[x]>.

Lemma cyclicP : forall A, reflect (exists x, A = <[x]>) (cyclic A).
Proof. move=> A; apply: (iffP existsP) => [] [x]; exists x; exact/eqP. Qed.

Lemma cycle_unit : <[1]> = 1 :> {set gT}.
Proof. by apply/eqP; rewrite eqset_sub gen_subG !sub1G. Qed.

Lemma cycle_h : forall a H, a \in H -> <[a]> \subset H.
Proof. by move=> a H Ha; rewrite gen_subG sub1set. Qed.

Lemma cyclenn : forall a, a \in <[a]>.
Proof. by move=> a; rewrite mem_gen // set11. Qed.

Lemma cycle_expgn : forall a b n, b \in <[a]> -> b ^+ n \in <[a]>.
Proof. move=> a; exact: groupX. Qed.

Lemma cycle_in : forall a m, a ^+ m \in <[a]>.
Proof. by move=> a m; rewrite cycle_expgn // cyclenn. Qed.

Definition zp_to_cycle n a (i : 'I_n) := a ^+ i.

Lemma zp_to_cycleM : forall (n : pos_nat) a, a ^+ n = 1 ->
  {in setT &, {morph @zp_to_cycle n a : x y / x * y}}.
Proof.
rewrite /zp_to_cycle => n a an_1 [i _] [j _] _ _ /=; rewrite -expgn_add.
by rewrite {2}(divn_eq (i + j) n) expgn_add mulnC expgn_mul an_1 exp1gn mul1g.
Qed.

Lemma order1 : #[1 : gT] = 1%N.
Proof. by rewrite /order cycle_unit cards1. Qed.

Lemma order_inf : forall a n, a ^+ n.+1 == 1 -> #[a] <= n.+1.
Proof.
move=> a [|n]; move/eqP; first by rewrite expg1 => ->; rewrite order1.
move/zp_to_cycleM=> zpM; rewrite -[n.+2]card_ord -cardsT.
apply: leq_trans (subset_leq_card _) (leq_imset_card (Morphism zpM) _).
rewrite -morphimEdom gen_subG sub1set /= morphimEdom /=.
apply/imsetP; exists (inord 1 : 'I_n.+2); first exact: in_setT.
by rewrite /zp_to_cycle inordK // expg1.
Qed.

Lemma zp_to_cycle_inj : forall a, injective (@zp_to_cycle #[a] a).
Proof.
move=> a i j; wlog ltij : i j / i < j.
  by case (ltngtP i j); [|symmetry|move/val_inj]; auto.
move/eqP; rewrite eq_mulVg1 /zp_to_cycle -(subnK ltij) addSnnS expgn_add mulKg.
move/order_inf; rewrite -leq_subS // subSS leqNgt; case/negP.
exact: leq_ltn_trans (leq_subr i j) _.
Qed.

Lemma zp_to_cycle_imset :  forall a, @zp_to_cycle #[a] a @: setT = <[a]>.
Proof.
move=> a; apply/eqP; rewrite eqset_sub_card andbC.
rewrite (card_imset _ (@zp_to_cycle_inj a)) cardsT card_ord leqnn.
by apply/subsetP=> x; case/imsetP=> i _ ->; rewrite cycle_in.
Qed.

Lemma cyclePmin : forall a b,
  reflect (exists2 m, m < #[a] & a ^+ m = b) (b \in <[a]>).
Proof.
move=> a b; rewrite -zp_to_cycle_imset.
apply: (iffP imsetP) => [[m] | [m ltma <-]]; first by exists (m : nat).
by exists (Ordinal ltma); rewrite ?inE.
Qed.

Lemma cycleP : forall a b, reflect (exists n, a ^+ n = b) (b \in <[a]>).
Proof.
move=> a b; apply: (iffP idP) => [|[n <-]]; last exact: cycle_in.
by case/cyclePmin=> n; exists n.
Qed.

Lemma order_expn1 : forall a, a ^+ #[a] = 1.
Proof.
move=> a; have: a^-1 \in <[a]> by rewrite groupV cyclenn.
case/cyclePmin=> i; rewrite leq_eqVlt=> ltia a_i.
have{a_i} a_i1: a ^+ i.+1 = 1 by rewrite expgS a_i mulgV.
case/predU1P: ltia => [<- //| lti1a].
by have:= @zp_to_cycle_inj a (Ordinal lti1a) ord0 a_i1.
Qed.

Canonical Structure zp_to_cycle_morphism a :=
  Morphism (zp_to_cycleM (order_expn1 a)).

Lemma zp_to_cycle_injm : forall a, 'injm (@zp_to_cycle #[a] a).
Proof.
by move=>a; apply/injmP; move=> x y _ _; apply:zp_to_cycle_inj.
Qed.

Lemma cycle_isom : forall a, isom setT  <[a]> (@zp_to_cycle #[a] a).
Proof.
move=> a; apply/isomP; split; last by rewrite morphimEdom zp_to_cycle_imset.
apply/injmP; apply: in2W; exact: zp_to_cycle_inj.
Qed.

Lemma cycle_decomp : forall a b,
  b \in <[a]> -> {m : nat | m < #[a] & a ^+ m = b}.
Proof.
move=> a b Cab; have ex_i: exists i, a ^+ i == b.
  by case/cycleP: Cab => i <-; exists i.
exists (ex_minn ex_i); case: ex_minnP => i a_i min_i; last exact/eqP.
case/cyclePmin: Cab => j ltja a_j; apply: leq_ltn_trans ltja.
by rewrite min_i // a_j.
Qed.

(***********************************************************************)
(*                                                                     *)
(*        Order Properties (1/2)                                       *)
(*                                                                     *)
(***********************************************************************)

Lemma cycle_conjgs : forall a b, <[a ^ b]> = <[a]> :^ b.
Proof.
move=> a b; apply/setP=> x; rewrite mem_conjg; apply/cycleP/idP=> [[n <-]|].
  by rewrite conjXg conjgK cycle_in.
by case/cycleP=> [n a_n_x]; exists n; rewrite -conjXg a_n_x conjgKV.
Qed.

Lemma orderJ : forall a b, #[a ^ b] = #[a].
Proof. by move=> a b; rewrite /order cycle_conjgs card_conjg. Qed.

Lemma expgn_modnorder : forall a k, a ^+ k = a ^+ (k %% #[a]).
Proof.
move=> a k; rewrite {1}(divn_eq k #[a]) expgn_add mulnC expgn_mul.
by rewrite order_expn1 exp1gn mul1g.
Qed.

(***********************************************************************)
(*                                                                     *)
(*        Commutativity Properties                                     *)
(*                                                                     *)
(***********************************************************************)


Lemma commute_cycle_com : forall a b : gT,
  commute a b -> {in <[a]>, centralised <[b]>}.
Proof.
move=> a b Hcom x; case/cycleP=> kx <-{x} y; case/cycleP=> ky <- {y}.
exact: commuteX2.
Qed.

Lemma commute_cycle_normal : forall a b : gT,
  commute a b -> <[a * b]> \subset 'N(<[a]>).
Proof.
move=> a b Hcom; apply: cents_norm.
apply/centsP; apply: commute_cycle_com.
apply: commute_sym; exact: commuteM.
Qed.

Lemma commute_cycle_sub : forall a b : gT,
  commute a b -> coprime #[a] #[b] -> <[a]> \subset <[a * b]>.
Proof.
move=> a b c_ab; move/eqnP=> co_ab; apply/subsetP=> x; case/cycleP=> k <-{x}.
case: (egcdnP #[a] (ltn_0order b))=> kb ka Heq Hineq.
apply/cycleP; exists (kb * #[b] * k)%N.
rewrite (expMgn _ c_ab) {2}(mulnC kb) -(mulnA #[b]).
rewrite (expgn_mul b #[b]) order_expn1 exp1gn mulg1.
rewrite Heq gcdnC co_ab muln_addl mul1n expgn_add -(mulnC #[a]).
by rewrite -(mulnA #[a]) expgn_mul order_expn1 exp1gn mul1g.
Qed.

Lemma cycle_mul : forall (a b : gT),
  commute a b -> coprime #[a] #[b] -> <[a * b]> = <[a]> * <[b]>.
Proof.
move=> a b c_ab co_ab; apply/eqP; rewrite eqset_sub_card coprime_card_mulG //.
have ->: <[a * b]> \subset <[a]> * <[b]>.
  have CaCb := centralised_mulgenE (commute_cycle_com c_ab).
  by rewrite -CaCb gen_subG sub1set /= CaCb mem_mulg ?cyclenn.
rewrite dvdn_leq ?ltn_0order // gauss_inv //=.
by rewrite {2}c_ab !cardSg // commute_cycle_sub // coprime_sym.
Qed.

(***********************************************************************)
(*                                                                     *)
(*        Bijection with Zp                                            *)
(*                                                                     *)
(***********************************************************************)

Lemma decomp_irr : forall a b (x y : {m | (m < #[a]) && (a ^+ m == b)}),
  x = y.
Proof.
move=> a b x y; apply: val_inj; wlog: x y / val x < val y.
  by move=> IH; case: (ltngtP (val x) (val y)) => // *; last symmetry; auto.
case: x => m /=; case/andP=> _; case: y => n /=; case/andP=> lt_n_oa.
move/eqP <-; rewrite eq_mulVg1 => eq1 ltmn; move: eq1.
rewrite -{1}(subnK ltmn) addSnnS expgn_add mulKg; move/order_inf.
by rewrite leqNgt (leq_trans _ lt_n_oa) // -leq_subS // ltnS subSS leq_subr.
Qed.

Lemma decomp_order_unicity :  forall a m (lt_m_oa : m < #[a]) n,
  (n < #[a]) && (a ^+ n == a ^+ m) -> m = n.
Proof.
move=> a m; rewrite -[m < _]andbT -(eqxx (a ^+ m)) => def_m n def_n.
by case: (decomp_irr (Sub m def_m) (Sub n def_n)).
Qed.

Lemma imset_zp_to_cycle : forall a, <[a]> \subset (zp_to_cycle a @* setT).
Proof. by move=> a; rewrite -zp_to_cycle_imset morphimEdom. Qed.

Definition cycle_to_zp (a: gT) :=
  restrm (imset_zp_to_cycle a) (invm (zp_to_cycle_injm a)).

Lemma cycle_to_zp_id : forall a n,
   n %% #[a] = cycle_to_zp a (a ^+ n).
Proof.
move=> a n; move :(ltn_0order a); rewrite expgn_modnorder -(ltn_mod n #[a]) => H.
rewrite -/(nat_of_ord (Ordinal H)).
by rewrite -{1}(invmE (zp_to_cycle_injm a) (in_setT (Ordinal H))).
Qed.

Lemma cycle_to_zp_corr : forall a b,
  b \in <[a]> -> a ^+ (cycle_to_zp a b) == b.
Proof.
move=> a b; rewrite -zp_to_cycle_imset; move/imsetP => [n Hn ->].
by rewrite -{2}(invmE (zp_to_cycle_injm a) Hn).
Qed.

Lemma zp_inj : forall a, 'injm ([morphism of cycle_to_zp a]).
Proof. by move=> a /=; apply: (injm_restrm _ (injm_invm _)). Qed.

Lemma zp_isom : forall a, isom <[a]> setT ([morphism of cycle_to_zp a]).
Proof.
move=> a; apply/isomP; split; first exact: zp_inj.
by rewrite /= morphim_restrm setIid -zp_to_cycle_imset -morphimEdom invm_dom.
Qed.

(***********************************************************************)
(*                                                                     *)
(*        Order properties  (2/2)                                      *)
(*                                                                     *)
(***********************************************************************)

Lemma order_dvd : forall a n, (#[a] %| n) = (a ^+ n == 1).
Proof.
move=> a n; rewrite expgn_modnorder /dvdn; apply/idP/idP.
  by move/eqP->; rewrite expg0.
rewrite -(expg0 a); move : (ltn_0order a); rewrite -(ltn_mod n)=> H.
by move/(conj H); move/andP; move/(decomp_order_unicity (ltn_0order a))=> <-.
Qed.

Lemma order_dvd_g : forall (H : group gT) a, a \in H -> #[a] %| #|H|.
Proof. move=> H a Ha; apply: cardSg; exact: cycle_h. Qed.

Lemma order_gexp_dvd : forall a n, #[a ^+ n] %| #[a].
Proof. move=> a n; apply: order_dvd_g; exact: cycle_in. Qed.

Lemma order_gcd : forall a n, 0 < n -> #[a ^+ n] = #[a] %/ gcdn #[a] n.
Proof.
move => a n H.
apply/eqP; rewrite eqn_dvd; apply/andP; split.
  rewrite order_dvd -expgn_mul -gcdn_divnC //.
  by rewrite expgn_mul order_expn1 exp1gn.
suff: #[a] %| #[a ^+ n] * gcdn #[a] n.
  move: (dvdn_gcdl #[a] n) (divn_eq #[a] (gcdn #[a] n)).
  rewrite {1}/dvdn; move/eqP=> H1; rewrite {1}H1 addn0=> {H1} H1.
  by rewrite {1}H1 dvdn_pmul2r // ltn_0gcd H orbT.
rewrite order_dvd mulnC expgn_mul -[a ^+ _]mulg1.
case: (egcdnP #[a] H)=> z2 z1 H1 H2.
rewrite -{1}(@exp1gn _ z1) -{1}(order_expn1 a) -expgn_mul.
rewrite mulnC -expgn_add addnC gcdnC -H1 -expgn_mul -mulnA mulnC.
by rewrite 2!expgn_mul order_expn1 exp1gn.
Qed.

Lemma order_mul : forall a b : gT,
  commute a b -> coprime #[a] #[b] -> #[a * b] = (#[a] * #[b])%N.
Proof.
by move=> a b Hcom Hcop; rewrite -coprime_card_mulG -?cycle_mul.
Qed.

(***********************************************************************)
(*                                                                     *)
(*        Generator                                                    *)
(*                                                                     *)
(***********************************************************************)

Definition generator (A : {set gT}) a := A == <[a]>.

Lemma generator_cycle : forall a, generator <[a]> a.
Proof. by move=> a; exact: eqxx. Qed.

Lemma cycle_generator : forall a x, generator <[a]> x -> x \in <[a]>.
Proof. move=> a x; move/(<[a]> =P _)->; exact: cyclenn. Qed.

Lemma generator_order : forall a b,
  generator <[a]> b -> #[a] = #[b].
Proof. by rewrite /order => a b; move/(<[a]> =P _)->. Qed.

Lemma cycle_subset : forall a n, <[a ^+ n]> \subset <[a]>.
Proof. move=> a n; apply: cycle_h; exact: cycle_in. Qed.

Lemma cycleV : forall a, <[a^-1]> = <[a]>.
Proof.
move=> a; symmetry; apply/eqP; rewrite eqset_sub.
by rewrite !cycle_h // -groupV ?invgK cyclenn.
Qed.

Lemma orderV : forall x, #[x^-1] = #[x].
Proof. by move=> x; rewrite /order cycleV. Qed.

End Cyclic.

Section CyclicSubGroup.

Variable gT : finGroupType.

(*  G. 1.3.1 (i) *)

Lemma cycle_sub_group : forall (a : gT) m, m %| #[a] ->
  [set H : {group gT} | (H \subset <[a]>) && (#|H| == m)]
     = [set <[a ^+ (#[a] %/ m)]>%G].
Proof.
move=> a m Hdiv.
have Hpos: 0 < m by apply (ltn_0dvd (ltn_0order a) Hdiv).
have Hcardm: #|<[a ^+ (#[a] %/ m)]>| == m.
  have Hdivpos: 0 < #[a] %/ m by
    rewrite -(ltn_pmul2r Hpos) mul0n (divnK Hdiv) ltn_0order.
  rewrite [card ( _)](order_gcd _ Hdivpos).
  rewrite {2}(divn_eq #[a] m) mulnC; move:{+}Hdiv; rewrite /dvdn.
  move/eqP->; rewrite gcdnC gcdn_addl_mul gcdn0.
  rewrite -{2}(@divn_mulr m (#[a] %/ m)) ?Hdivpos //=.
  by rewrite (divnK Hdiv) eqxx.
apply/eqP; rewrite eqset_sub sub1set inE /= cycle_subset Hcardm !andbT.
apply/subsetP=> X; rewrite in_set1 inE -val_eqE /= eqset_sub_card (eqP Hcardm).
case/andP=> sXa; move/eqP=> oX; rewrite oX leqnn andbT.
apply/subsetP=> x Xx; case/cycleP: (subsetP sXa _ Xx) => k def_x.
have: (x ^+ m == 1)%g by rewrite -oX -order_dvd cardSg // gen_subG sub1set.
rewrite -def_x -expgn_mul -order_dvd -[#[a]](LaGrange sXa) -oX mulnC.
rewrite dvdn_pmul2r // divn_mull //; case/dvdnP=> i ->{def_x k}.
by rewrite mulnC expgn_mul groupX // cyclenn.
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
Proof. by rewrite order_dvd -morphX // order_expn1 morph1. Qed.

End MorphicImage.

(***********************************************************************)
(*                                                                     *)
(*       Automorphisms of cyclic groups                                *)
(*                                                                     *)
(***********************************************************************)

Section CyclicAutomorphism.

Variables gT1 gT2 : finGroupType.

Variable f : {perm gT1}.

Lemma cycle_aut_stable : forall x, f \in Aut <[x]> -> f @: <[x]> = <[f x]>.
Proof.
move=> x autf; rewrite -(autmE autf) -morphimEdom morphim_cycle //.
exact: cyclenn.
Qed.

Lemma order_aut_stable : forall x, f \in Aut <[x]> -> #[x]  = #[f x].
Proof.
move=> x autf; rewrite /order -cycle_aut_stable ?card_imset //.
exact: perm_inj.
Qed.

(* From the multiplicative group to automorphisms *)

Lemma cycle_gexpn_clos : forall (x : gT1) k,
  (expgn^~ k) @: <[x]> \subset <[x]>.
Proof.
move=> x k; apply/subsetP=> a; case/imsetP=> y; case/cycleP=> n <- -> {a y}.
by rewrite -expgn_mul cycle_in.
Qed.

Lemma cycle_dcan_gexpn : forall (a : gT1) k, coprime #[a] k ->
  exists g, {in <[a]>, cancel (expgn^~ k) g}.
Proof.
move=> a k; case Hpos: (0 < k) => Hcop; last first.
  move: Hcop; move/idPn: Hpos; rewrite -eqn0Ngt; move/eqP->.
  rewrite coprime_sym /coprime gcd0n /order => Hcard.
  have Heq: (1%g : {set gT1}) =i <[a]>.
    apply/subset_cardP; last by rewrite sub1set; apply:group1.
    by move/eqP:Hcard->; rewrite cardsE card1.
  by exists (@id gT1) => x; rewrite expg0 //= -(Heq x); move/set1P=> <-.
case: (bezoutl #[a] Hpos); move=> x xinf.
rewrite coprime_sym /coprime in Hcop; move/eqP: Hcop->; move/dvdnP=> [k0 Hk0].
exists (fun z:gT1 => z ^+ k0)%g; move=> x0 Hx0 //=.
rewrite -expgn_mul mulnC -Hk0 expgn_add mulnC; case/cycleP: Hx0 => i <-.
by rewrite expg1 -!expgn_mul mulnCA expgn_mul order_expn1 exp1gn mulg1.
Qed.

Lemma inj_gexpn : forall (a : gT1) k,
  coprime #[a] k -> {in <[a]> &, injective (expgn^~ k)}.
Proof.
move=> k a Hcop; move: (cycle_dcan_gexpn Hcop)=> [g dcan].
by apply (in_can_inj dcan).
Qed.

Definition cycle_expgm of gT1 := fun k x => x ^+ k : gT1.

Lemma cycle_expgm_morphM : forall a k,
  {in <[a]> &, {morph cycle_expgm a k : x y / x * y}}.
Proof.
move=> a k x y cax cay; apply: expMgn; exact: commute_cycle_com cay.
Qed.

Canonical Structure cycle_expgm_morphism a k :=
  Morphism (@cycle_expgm_morphM a k).

Lemma cycle_expgm_inj : forall a k, coprime #[a] k -> 'injm (cycle_expgm a k).
Proof. move=> a k coak; apply/injmP; exact: inj_gexpn. Qed.

Lemma cycle_expgm_on : forall a k, coprime #[a] k -> 
  cycle_expgm a k @* <[a]> = <[a]>.
Proof.
move=> a k coak; apply/morphim_fixP=> //; first exact: cycle_expgm_inj.
by rewrite morphimEdom cycle_gexpn_clos.
Qed.

Definition cycle_aut_of a k (coak : coprime #[a] k) :=
  aut_of (cycle_expgm_inj coak) (cycle_expgm_on coak).

(* GG: Aut_aut_of proves cycle_aut_of coak \in Aut <[a]>. *)

(* The converse : from automorphisms to the multiplicative group *)

Lemma cycle_to_fp_loc_corr : forall x : gT1,
  f \in Aut <[x]> -> coprime #[x] (cycle_to_zp x (f x)).
Proof.
move=> x autf /=; set n := cycle_to_zp x (f x).
have Hfx: f x \in <[x]>.
  by rewrite -[<[x]>](autm_dom autf) mem_imset // setIid cyclenn.
have:= cycle_to_zp_corr Hfx; rewrite eq_sym -/n. 
case: (posnP n) => [-> {n} | npos Hn].
  rewrite -{3}(permK f x); move/eqP->.
  by rewrite -groupV in autf; rewrite -(autmE autf) morph1 order1.
have: gcdn #[x] n <= 1.
  rewrite leqNgt; apply/negP=> Hgcd; move: (divn_lt Hgcd (ltn_0order x)).
  rewrite ltn_neqAle; move: (order_gcd x npos); rewrite -(eqP Hn).
  move/eqP; rewrite -(order_aut_stable autf); move/eqP=> Hg.
  by rewrite {3}Hg eqxx andFb.
by rewrite leq_eqVlt orbC ltnNge ltn_0gcd npos ltn_0group.
Qed.

Lemma cycle_to_fp_loc_repr : forall x,
  f \in Aut <[x]> ->
 (forall z, z \in <[x]> ->
    f z = z ^+ (cycle_to_zp x (f x)))%g.
Proof.
move=> x autf; have Cxx := cyclenn x.
move=> z; case/cycleP=> n <- {z}; rewrite -{1}(autmE autf) morphX //=.
have Cfx: f x \in <[x]>.
  by rewrite -[<[x]>](autm_dom autf) mem_imset // setIid.
by rewrite -expgn_mul mulnC expgn_mul (eqP (cycle_to_zp_corr Cfx)).
Qed.

(* Note 1 : This construction is necessary, see Note 2 below *)

Definition cycle_to_fp_loc (a : gT1) : perm gT1 -> 'I_(#[a]) :=
  fun f => if coprime #[a] (cycle_to_zp a (f a))
    then
     (cycle_to_zp a (f a))
    else
      (zp1 [pos_nat of #[a]]).

Lemma cycle_to_fp_corr : forall a, coprime #[a] (cycle_to_fp_loc a f).
Proof.
move=> a; rewrite /cycle_to_fp_loc.
case e: (coprime #[a] (cycle_to_zp a (f a))); [apply: (idP e) |apply: coprime_zp1].
Qed.

Lemma cycle_to_fp_repr : forall a,
  f \in Aut <[a]> ->
  (cycle_to_fp_loc a f) = (cycle_to_zp a (f a)).
Proof.
by move=> a Haut; rewrite /cycle_to_fp_loc (cycle_to_fp_loc_corr Haut).
Qed.

End CyclicAutomorphism.

(***********************************************************************)
(*                                                                     *)
(*        Bijection with Fp                                            *)
(*                                                                     *)
(***********************************************************************)

Section FpAut.

Variable gT : finGroupType.

Definition fp_to_cycle (x : gT) :=
  fun (D : fp_mul #[x]) => cycle_aut_of (valP D).

Definition cycle_to_fp (a : gT) : perm gT -> fp_mul #[a] :=
  fun f => Sub (cycle_to_fp_loc a f) (cycle_to_fp_corr f a).

Lemma fp_morph : forall x : gT,
  {in Aut <[x]> &, {morph cycle_to_fp x : y z / y * z}}.
Proof.
move=> a x y Hx Hy; do 2!apply: val_inj => /=.
rewrite !cycle_to_fp_repr ?groupM //= permM.
rewrite {1}(cycle_to_fp_loc_repr Hx) ?cyclenn //=.
rewrite (cycle_to_fp_loc_repr Hy) ?(groupX, cyclenn) //=.
by rewrite -expgn_mul cycle_to_zp_id.
Qed.

Canonical Structure cycle_to_fp_morphism x := Morphism (@fp_morph x).

  (* Note 2 : notice how this is a partial cancel, in particular we could prove
     forall a, ~~(Aut <[a]> \subset (@fp_to_cycle a) @* setT)

     ==> it's as long to proceed with cycle_to_zp as it is with fp_to_cyclic
   *)

Lemma fp_can : forall a : gT,
  {in Aut <[a]>, cancel (cycle_to_fp a) (@fp_to_cycle a)}.
Proof.
move=> a f Haut; symmetry; apply/permP=> x.
rewrite permE /= (cycle_to_fp_repr Haut) /=.
case cax: (x \in <[a]>); first exact: cycle_to_fp_loc_repr.
by move: Haut; rewrite inE; case/andP; move/out_perm->; rewrite ?cax.
Qed.

Lemma fp_inj : forall x : gT, 'injm (cycle_to_fp x).
Proof. move=> a; apply/injmP; exact: in_can_inj (@fp_can a). Qed.

Lemma fp_isom : forall a : gT, isom (Aut <[a]>) setT (cycle_to_fp a).
Proof.
move=> a; apply/isomP; split; first exact: fp_inj.
apply/setP=> x; rewrite inE morphimEdom.
apply/imsetP; exists (fp_to_cycle x); first exact: Aut_aut_of.
do 2!apply: val_inj; rewrite /= cycle_to_fp_repr ?Aut_aut_of //=.
by rewrite permE cyclenn -cycle_to_zp_id modn_small.
Qed.

End FpAut.

(***********************************************************************)
(*                                                                     *)
(*       Automorphism with Zp, consequences on generators              *)
(*                                                                     *)
(***********************************************************************)

Section GenAut.

Variables aT rT : finGroupType.

Lemma generator_bij : forall (G H : {group aT}) (f : {morphism G >-> rT}) a,
   'injm f -> H \subset G -> a \in G ->
    generator H a = generator (f @* H) (f a).
Proof.
move=> G H f a injf sHG Ga.
rewrite /generator -morphim_cycle // !eqset_sub.
by rewrite !morphimSGK //= ?(subset_trans injf, sub1G, cycle_h).
Qed.

End GenAut.

Section ZpAut.

Variable gT : finGroupType.
Variable a : gT.

Lemma expgn_muln : forall k (n : pos_nat) p (H : p < n),
  Ordinal H ^+ k = Ordinal (ltn_pmod (p * k) (valP n)).
Proof.
elim=> [|k IH] n p H; apply: val_inj=> //=; first by rewrite muln0 modn_small.
by rewrite expgS IH //= modn_addmr -{1}(muln1 p) -muln_addr add1n.
Qed.

Lemma zp_group_cycle : forall (n : pos_nat) k (lt_k_n : k < n),
  coprime k n -> setT = <[Ordinal lt_k_n]>.
Proof.
move=> n k H Hcop; symmetry; apply/setP; apply/subset_eqP; apply/andP.
split; first by apply/subsetP=> x //= Hx ; rewrite inE.
apply/subsetP; move=> x _ /=; apply/cycleP; move: k H Hcop x.
case=> [|k] H Hcop /= x0.
  rewrite /coprime gcd0n in Hcop; exists 1%N; move: (valP x0).
  move/eqP:Hcop=> Hn; rewrite {3}Hn !ltnS !leqn0; move/eqP => H0.
  by apply: val_inj; rewrite /= addn0 /= H0 modn_small.
case: (egcdnP n (ltn0Sn k))=> kk kn Heq Hineq.
exists (kk * x0)%N; rewrite /= expgn_muln; apply: val_inj => /=.
rewrite mulnA (mulnC (k.+1)) Heq muln_addl -(mulnA kn) (mulnC n) mulnA.
move: Hcop; rewrite modn_addl_mul /coprime; move/eqP->.
by rewrite mul1n modn_small.
Qed.

Lemma zp_ord : forall (n : pos_nat) (i : zp_group n),
  i = Ordinal (valP (i : 'I_n)).
Proof. by move=> n i; apply: val_inj. Qed.

Lemma zp_gen : forall (n : pos_nat) (i : 'I_n),
  generator setT i = coprime i n.
Proof.
move=> n i; apply/idP/idP; last first.
  move=> Hcop; apply/eqP.
  apply:zp_group_cycle=> /=; by [apply: (valP (i : 'I_n)) | apply: Hcop].
move/(setT =P _)=> Hcop.
case e: (0 < (i : 'I_n)).
  apply:modn_coprime; first exact: (idP e).
  have H1: (1 < n) by apply: leq_ltn_trans (valP (i : 'I_n)); apply:(idP e).
  have: Ordinal H1 \in <[i]> by rewrite -Hcop inE.
  by case/cycleP=> n1; rewrite (zp_ord i) expgn_muln /=; case; exists n1.
move/negbT:e; rewrite lt0n negbK; move/eqP=> i0.
have i1 : i = 1 by exact: val_inj.
by rewrite i0 -(card_ord n) -cardsT Hcop i1 cycle_unit cards1.
Qed.

Lemma generator_coprime : forall m,
  coprime m #[a] = generator <[a]> (a ^+ m).
Proof.
move=> m; rewrite (generator_bij (zp_inj a));
rewrite /= ?morphimEdom ?zp_to_cycle_imset ?cycle_in //=.
move: (zp_isom a); case/isomP => _ /=.
rewrite -morphimEdom => ->; rewrite /coprime -gcdn_modl.
have Hmod: m %% #[a] < #[a] by rewrite ltn_mod (ltn_0order a).
have:= @zp_gen [is #[a] : _ <: pos_nat] (Ordinal Hmod).
rewrite /= /coprime => <-; congr generator; apply: val_inj=> /=.
by rewrite cycle_to_zp_id.
Qed.

Lemma phi_gen : phi #[a] = #|[pred x | generator <[a]> x]|.
Proof.
rewrite /phi /=; set n := #[a].
have: [pred x : 'I_n | coprime n x] =i
      [pred x : 'I_n | generator <[a]> (a ^+ x)].
  by move=> x /=; rewrite !inE /= -generator_coprime coprime_sym.
move/eq_card=> ->.
suff: (image (cycle_to_zp a) (generator <[a]>)) =i
        [pred x : 'I_n | generator <[a]> (a ^+ x)].
  move/eq_card <-; apply: card_dimage; move/injmP: (zp_inj a).
  apply:subin2; exact: cycle_generator.
move=> /= x; apply/imageP/idP; rewrite inE /=.
  move=> [x0 Hx0 ->]; move: (cycle_generator Hx0); move/cycle_to_zp_corr.
  by move/eqP; rewrite /cycle_to_zp /= => ->.
move=> Hgen; exists (a ^+ x)%g; first by trivial.
apply: val_inj; rewrite /cycle_to_zp /=.
move: (cycle_to_zp_corr (cycle_generator Hgen)); rewrite eq_sym.
move/(conj (valP x))=> /=; move/andP; move/decomp_order_unicity=> /=.
by rewrite ltn_ord; move/(_ is_true_true).
Qed.

End ZpAut.

Section CyclicAutomorphism_Abelian.

(* G. 1.3.10 *)

Variable gT : finGroupType.

Lemma aut_cycle_commute : forall x : gT, abelian (Aut <[x]>).
Proof.
move=> x; have:= isom_isog _ (subset_refl _) (fp_isom x); rewrite isog_sym.
case/isogP=> f _ /= <-; apply: morphim_cents.
by apply/centsP=> m _ n _; do 2!apply: val_inj => /=; rewrite mulnC.
Qed.

End CyclicAutomorphism_Abelian.
