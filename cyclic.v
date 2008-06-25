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
Require Import seq fintype paths connect div.
Require Import finset bigops groups normal group_perm automorphism zp fp.

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
by move/isom_isog; move/isog_card; rewrite !cardsT card_prod !cardphi.
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

Section CyclicDef.

Variable gT : finGroupType.

Definition cyclic (a : gT) := << [set a] >>.

Definition orderg x := #|cyclic x|.

Definition cyclicpred (a : gT) := set_of (fconnect (mulg a) 1).

End CyclicDef.

Notation "#[ x ]" := (orderg x) (at level 0, format "#[ x ]"): group_scope.

Prenex Implicits cyclic cyclicpred.

Section Cyclic.

Variable gT : finGroupType.
Implicit Types a x y : gT.

Canonical Structure cyclic_group a := Eval hnf in [group of cyclic a].

Lemma cyclic1 : forall a, 1 \in cyclic a.
Proof. move=> a; exact: group1. Qed.

(*
Lemma expgn_itern: forall (a : gT) n, a ^+ n = iter n (mulg a) 1.
Proof. by move=> a; elim=> /= [|n Rec]; [|rewrite /comp Rec]. Qed.
*)
Lemma cyclicpredP : forall a b,
  reflect (exists n, a ^+ n = b) (b \in cyclicpred a).
Proof.
move=> a b; rewrite inE; apply: (iffP idP) => [| [n <-{b}]].
  exists (findex (mulg a) 1 b); exact: iter_findex.
exact: fconnect_iter.
Qed.

Lemma group_cyclicpred : forall a : gT, group_set (cyclicpred a).
Proof.
move=> a; apply/group_setP; split=> [|x y]; first by rewrite inE /= connect0.
case/cyclicpredP=> m <-{x}; case/cyclicpredP=> n <-{y}.
by apply/cyclicpredP; exists (m + n); rewrite expgn_add.
Qed.

Lemma cyclic_h : forall a (H : {group gT}), a \in H -> cyclic a \subset H.
Proof. by move=> a H Ha; rewrite gen_subG sub1set. Qed.

Lemma cyclicnn: forall a, a \in cyclic a.
Proof. by move=> a; rewrite mem_geng // set11. Qed.

Lemma cyclic_expgn: forall a b n, b \in cyclic a -> b ^+ n \in cyclic a.
Proof. move=> a; exact: groupX. Qed.

Lemma cyclic_in: forall a m, a ^+ m \in cyclic a.
Proof. by move=> a m; rewrite cyclic_expgn // cyclicnn. Qed.

Lemma cyclic_cyclicpred : forall a : gT, cyclic a = cyclicpred a.
Proof.
move=> a; apply/eqP; pose Ca := Group (group_cyclicpred a).
rewrite eqset_sub (@cyclic_h _ Ca); last rewrite inE connect1 /= ?mulg1 //.
apply/subsetP=> x; case/cyclicpredP=> n <-{x}; exact: cyclic_in.
Qed.

Lemma cyclicpred_order : forall a : gT, #[a] = order (mulg a) 1.
Proof. by move=> a; rewrite /orderg cyclic_cyclicpred cardsE. Qed.

Lemma cyclicP : forall a b,
  reflect (exists n, a ^+ n = b) (b \in cyclic a).
Proof. move=> a b; rewrite cyclic_cyclicpred; exact: cyclicpredP. Qed.

Lemma cyclic_decomp : forall a b,
  b \in cyclic a -> {m : nat | m < #[a] & a ^+ m = b}.
Proof.
move=> a b; rewrite cyclic_cyclicpred cyclicpred_order inE => Hcyc.
exists (findex (mulg a) 1 b); [exact: findex_max | exact: iter_findex].
Qed.

Lemma cyclicPmin : forall a b,
  reflect (exists2 m, m < #[a] & a ^+ m = b) (b \in cyclic a).
Proof.
move => a b; apply: (iffP idP) => [|[m _ <-]]; last exact: cyclic_in.
by case/cyclic_decomp=> m; exists m.
Qed.

(***********************************************************************)
(*                                                                     *)
(*        Order Properties (1/2)                                       *)
(*                                                                     *)
(***********************************************************************)

Lemma orderg1 : #[1 : gT] = 1%N.
Proof.
apply/eqP; rewrite eqn_leq pos_card_group andbT -trivg_card.
apply: cyclic_h; exact: set11.
Qed.

Lemma orderg_pos: forall a, 0 < #[a].
Proof. by move => a; exact: pos_card_group. Qed.
Hint Resolve orderg_pos.
Canonical Structure orderg_pos_nat a := PosNat (orderg_pos a).

Lemma cyclic_conjgs: forall a b, cyclic (a ^ b) = cyclic a :^ b.
Proof.
move=> a b; apply/setP=> x; rewrite mem_conjg; apply/cyclicP/idP=> [[n <-]|].
  by rewrite conjXg conjgK cyclic_in.
by case/cyclicP=> [n a_n_x]; exists n; rewrite -conjXg a_n_x conjgKV.
Qed.

Lemma orderg_conjg: forall a b, #[a ^ b] = #[a].
Proof. by move=> a b; rewrite /orderg cyclic_conjgs card_conjg. Qed.

Lemma orderg_expn1: forall a, a ^+ #[a] = 1.
Proof.
move=> a; rewrite cyclicpred_order [a ^+ _]iter_order //; exact: mulg_injl.
Qed.

Lemma orderg_inf : forall a n, (a ^+ n.+1 == 1) -> #[a] <= n.+1.
Proof.
move=> a n H2; apply/idPn; rewrite -ltnNge cyclicpred_order; move/findex_iter.
by rewrite [iter _ _ _](eqP H2) findex0.
Qed.

Lemma expgn_modnorder : forall a k, a ^+ k = a ^+ (k %% #[a]).
Proof.
move=> a k; rewrite {1}(divn_eq k #[a]) expgn_add mulnC expgn_mul.
by rewrite orderg_expn1 exp1gn mul1g.
Qed.

Lemma cyclic_unit : cyclic 1 = 1 :> {set gT}.
Proof. by apply/eqP; rewrite eqset_sub gen_subG !sub1G. Qed.

(***********************************************************************)
(*                                                                     *)
(*        Commutativity Properties                                     *)
(*                                                                     *)
(***********************************************************************)


Lemma commute_cyclic_com : forall a b : gT,
  commute a b -> {in cyclic a, central (cyclic b)}.
Proof.
move=> a b Hcom x; case/cyclicP=> kx <-{x} y; case/cyclicP=> ky <- {y}.
apply: commuteX; apply: commute_sym; exact: commuteX.
Qed.

Lemma commute_cyclic_normal : forall a b : gT,
  commute a b -> cyclic (a * b) \subset 'N(cyclic a).
Proof.
move=> a b Hcom; apply: subset_trans (sub_centg _).
apply/centralP; apply: commute_cyclic_com.
apply: commute_sym; exact: commuteM.
Qed.

Lemma commute_cyclic_sub : forall a b : gT,
  commute a b -> coprime #[a] #[b] -> cyclic a \subset cyclic (a * b).
Proof.
move=> a b c_ab; move/eqnP=> co_ab; apply/subsetP=> x; case/cyclicP=> k <-{x}.
case: (egcdnP #[a] (orderg_pos b))=> kb ka Heq Hineq.
apply/cyclicP; exists (kb * #[b] * k)%N.
rewrite (expMgn _ c_ab) {2}(mulnC kb) -(mulnA #[b]).
rewrite (expgn_mul b #[b]) orderg_expn1 exp1gn mulg1.
rewrite Heq gcdnC co_ab muln_addl mul1n expgn_add -(mulnC #[a]).
by rewrite -(mulnA #[a]) expgn_mul orderg_expn1 exp1gn mul1g.
Qed.

Lemma cyclic_mul : forall (a b : gT),
  commute a b -> coprime #[a] #[b] -> cyclic (a * b) = cyclic a * cyclic b.
Proof.
move=> a b c_ab co_ab; apply/eqP; rewrite eqset_sub_card coprime_card_mulG //.
have ->: cyclic (a * b) \subset cyclic a * cyclic b.
  have CaCb := central_mulgenE (commute_cyclic_com c_ab).
  by rewrite -CaCb gen_subG sub1set /= CaCb mem_mulg ?cyclicnn.
rewrite dvdn_leq ?orderg_pos // gauss_inv //=.
by rewrite {2}c_ab !group_dvdn // commute_cyclic_sub // coprime_sym.
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
rewrite -{1}(subnK ltmn) addSnnS expgn_add mulKg; move/orderg_inf.
by rewrite leqNgt (leq_trans _ lt_n_oa) // -leq_subS // ltnS subSS leq_subr.
Qed.

Lemma decomp_order_unicity :  forall a m (lt_m_oa : m < #[a]) n,
  (n < #[a]) && (a ^+ n == a ^+ m) -> m = n.
Proof.
move=> a m; rewrite -[m < _]andbT -(eqxx (a ^+ m)) => def_m n def_n.
by case: (decomp_irr (Sub m def_m) (Sub n def_n)).
Qed.

Fixpoint ctzl (a b : gT) (k : nat) : nat :=
  if k is n.+1 then
    if b == a ^+ (#[a] - k)
      then #[a] - k
      else ctzl a b n
    else 0.

Lemma ltn_subSn : forall m n, 0 < m -> m - n.+1 < m.
Proof. case=> // m n _; exact (leq_subr n m). Qed.

Lemma ctzl_pos : forall k a b, ctzl a b k < #[a].
Proof.
elim=> //= [n IH] a b; case (b == a ^+ (#[a] - n.+1)); last exact: IH.
rewrite ltn_neqAle leq_subr andbT neq_ltn; apply/orP; left.
elim: #[a] (orderg_pos a) => [|n0 IH0 Hineq]; first by rewrite ltn0.
exact: ltn_subSn.
Qed.

Lemma ctzl_repr : forall k (a b : gT) (H : b \in cyclic a),
  #[a] - s2val (cyclic_decomp H) <= k ->  a ^+ (ctzl a b k) == b.
Proof.
move=> k a b; case/cyclic_decomp=> /= m ltma <- {b}.
elim: k => [|k IHk /=]; first by rewrite leq_sub_add addn0 leqNgt ltma.
case: ifP => diff_am; first by rewrite eq_sym.
rewrite leq_eqVlt; case/predU1P=> {IHk}// def_am; case/eqP: diff_am.
by rewrite -(subnK (ltnW ltma)) def_am addnK.
Qed.

Definition cyclic_to_zp_loc (a b : gT) : nat := ctzl a b #[a].

Lemma cyclic_to_zp_ord : forall a b, cyclic_to_zp_loc a b < #[a].
Proof. move=> a; exact: ctzl_pos. Qed.

Lemma cyclic_to_zp_corr : forall a b,
  b \in cyclic a -> a ^+ (cyclic_to_zp_loc a b) == b.
Proof.
move=> a b Hcyc; rewrite /cyclic_to_zp_loc.
apply: (@ctzl_repr #[a] _ _ Hcyc ); apply:leq_subr.
Qed.

Lemma cyclic_to_zp_id : forall a n,
  cyclic_to_zp_loc a (a ^+ n) = n %% #[a].
Proof.
move=> a n; move: (cyclic_to_zp_corr (cyclic_in a n)).
rewrite {2}(expgn_modnorder a n); move/(conj (cyclic_to_zp_ord a (a ^+ n))).
move/andP; move/decomp_order_unicity; rewrite ltn_mod (orderg_pos a).
by move/(_ is_true_true); symmetry.
Qed.

Lemma cyclic_to_zp_decomp : forall a b (Cb : b \in cyclic a),
  cyclic_to_zp_loc a b = s2val (cyclic_decomp Cb).
Proof.
move=> a b Hcyc; move: (cyclic_to_zp_ord a b) (cyclic_to_zp_corr Hcyc)=> Hord1.
case: (cyclic_decomp Hcyc)=> m Hord2 Hcor2 /=; rewrite -{2}Hcor2.
move/(conj Hord1); move/andP.
by move/(decomp_order_unicity Hord2); symmetry.
Qed.

Definition cyclic_to_zp (a : gT) : gT -> 'I_(#[a]) :=
  fun x => Ordinal (cyclic_to_zp_ord a x).

Definition zp_to_cyclic a (n : 'I_(#[a])) : FinGroup.sort gT := a ^+ n.

Lemma zp_morph : forall a,
   {in cyclic a &, {morph cyclic_to_zp a : x y / x * y}}.
Proof.
move=> a x y Hx Hy.
move: (cyclic_to_zp_corr Hx) (cyclic_to_zp_corr Hy); move/eqP=> Hcorx.
move/eqP=> Hcory; rewrite -{1}Hcorx -{1}Hcory -expgn_add.
by apply: val_inj; rewrite /= cyclic_to_zp_id.
Qed.

Canonical Structure zp_morphism a := Morphism (@zp_morph a).

Lemma zp_inj : forall a, 'injm (cyclic_to_zp a).
Proof.
move=> a; apply/injmP=> x y /= Hx Hy [Heq].
move/eqP: (cyclic_to_zp_corr Hx); move/eqP: (cyclic_to_zp_corr Hy) => <- <-.
by rewrite Heq.
Qed.

Lemma zp_isom : forall a, isom (cyclic a) setT (cyclic_to_zp a).
Proof.
move=> a; apply/isomP; split; first exact: zp_inj.
apply/eqP; rewrite eqset_sub_card subsetT cardsT card_ord morphimEdom /=.
rewrite card_dimset //; apply/injmP; exact: zp_inj.
Qed.

(***********************************************************************)
(*                                                                     *)
(*        Order properties  (2/2)                                      *)
(*                                                                     *)
(***********************************************************************)

Lemma orderg_dvd : forall a n, (#[a] %| n) = (a ^+ n == 1).
Proof.
move=> a n; rewrite expgn_modnorder /dvdn; apply/idP/idP.
  by move/eqP->; rewrite expg0.
rewrite -(expg0 a); move : (orderg_pos a); rewrite -(ltn_mod n)=> H.
by move/(conj H); move/andP; move/(decomp_order_unicity (orderg_pos a))=> <-.
Qed.

Lemma orderg_dvd_g : forall (H : group gT) a, a \in H -> #[a] %| #|H|.
Proof. move=> H a Ha; apply: group_dvdn; exact: cyclic_h. Qed.

Lemma orderg_gexp_dvd : forall a n, #[a ^+ n] %| #[a].
Proof. move=> a n; apply: orderg_dvd_g; exact: cyclic_in. Qed.

Lemma orderg_gcd : forall a n, 0 < n -> #[a ^+ n] = #[a] %/ gcdn #[a] n.
Proof.
move => a n H.
apply/eqP; rewrite eqn_dvd; apply/andP; split.
  rewrite orderg_dvd -expgn_mul -gcdn_divnC //.
  by rewrite expgn_mul orderg_expn1 exp1gn.
suff: #[a] %| #[a ^+ n] * gcdn #[a] n.
  move: (dvdn_gcdl #[a] n) (divn_eq #[a] (gcdn #[a] n)).
  rewrite {1}/dvdn; move/eqP=> H1; rewrite {1}H1 addn0=> {H1} H1.
  by rewrite {1}H1 dvdn_pmul2r // ltn_0gcd H orbT.
rewrite orderg_dvd mulnC expgn_mul -[a ^+ _]mulg1.
case: (egcdnP #[a] H)=> z2 z1 H1 H2.
rewrite -{1}(@exp1gn _ z1) -{1}(orderg_expn1 a) -expgn_mul.
rewrite mulnC -expgn_add addnC gcdnC -H1 -expgn_mul -mulnA mulnC.
by rewrite 2!expgn_mul orderg_expn1 exp1gn.
Qed.

Lemma orderg_mul : forall a b : gT,
  commute a b -> coprime #[a] #[b] -> #[a * b] = (#[a] * #[b])%N.
Proof.
by move=> a b Hcom Hcop; rewrite -coprime_card_mulG -?cyclic_mul.
Qed.

(***********************************************************************)
(*                                                                     *)
(*        Generator                                                    *)
(*                                                                     *)
(***********************************************************************)

Definition generator (A : {set gT}) a := A == cyclic a.

Lemma generator_cyclic : forall a, generator (cyclic a) a.
Proof. by move=> a; exact: eqxx. Qed.

Lemma cyclic_generator : forall a x, generator (cyclic a) x -> x \in cyclic a.
Proof. move=> a x; move/(cyclic a =P _)->; exact: cyclicnn. Qed.

Lemma generator_orderg: forall a b,
  generator (cyclic a) b -> #[a] = #[b].
Proof. by rewrite /orderg => a b; move/(cyclic a =P _)->. Qed.

Lemma cyclic_subset : forall a n, cyclic (a ^+ n) \subset cyclic a.
Proof. move=> a n; apply: cyclic_h; exact: cyclic_in. Qed.

Lemma cyclicV : forall a, cyclic a = cyclic a^-1.
Proof.
move=> a; apply/eqP; rewrite eqset_sub.
by rewrite !cyclic_h // -groupV ?invgK cyclicnn.
Qed.

End Cyclic.

Section CyclicSubGroup.

Variable gT : finGroupType.

(*  G. 1.3.1 (i) *)

Lemma cyclic_sub_group : forall (a : gT) m, m %| #[a] ->
  [set H : {group gT} | (H \subset cyclic a) && (#|H| == m)]
     = [set [is cyclic (a ^+ (#[a] %/ m)) : _ <: group _]].
Proof.
move=> a m Hdiv.
have Hpos: 0 < m by apply (ltn_0dvd (orderg_pos a) Hdiv).
have Hcardm: #|cyclic (a ^+ (#[a] %/ m))| == m.
  have Hdivpos: 0 < #[a] %/ m by
    rewrite -(ltn_pmul2r Hpos) mul0n (divnK Hdiv) orderg_pos.
  rewrite [card ( _)](orderg_gcd _ Hdivpos).
  rewrite {2}(divn_eq #[a] m) mulnC; move:{+}Hdiv; rewrite /dvdn.
  move/eqP->; rewrite gcdnC gcdn_addl_mul gcdn0.
  rewrite -{2}(@divn_mulr m (#[a] %/ m)) ?Hdivpos //=.
  by rewrite (divnK Hdiv) eqxx.
apply/eqP; rewrite eqset_sub sub1set inE /= cyclic_subset Hcardm !andbT.
apply/subsetP=> X; rewrite in_set1 inE -val_eqE /= eqset_sub_card (eqP Hcardm).
case/andP=> sXa; move/eqP=> oX; rewrite oX leqnn andbT.
apply/subsetP=> x Xx; case/cyclicP: (subsetP sXa _ Xx) => k def_x.
have: (x ^+ m == 1)%g by rewrite -oX -orderg_dvd group_dvdn // gen_subG sub1set.
rewrite -def_x -expgn_mul -orderg_dvd -[#[a]](LaGrange sXa) -oX mulnC.
rewrite dvdn_pmul2r // divn_mull //; case/dvdnP=> i ->{def_x k}.
by rewrite mulnC expgn_mul groupX // cyclicnn.
Qed.

Lemma cyclic_subgroup_char : forall a (H : {group gT}),
  H \subset cyclic a -> H \char cyclic a.
Proof.
move=> a H sHa; apply: lone_subgroup_char => // J sJa isoJH.
have dvHa: #|H| %| #[a] by exact: group_dvdn.
have{dvHa} Huniq := esym (cyclic_sub_group dvHa).
move/setP: Huniq => Huniq; move: (Huniq H) (Huniq J); rewrite !inE /=.
by rewrite sHa sJa (isog_card isoJH) eqxx; do 2!move/eqP <-.
Qed.

End CyclicSubGroup.

Section MorphicImage.

Variables aT rT : finGroupType.

Lemma morphim_cyclic : forall (G : {group aT}) (f : {morphism G >-> rT}) x,
  x \in G -> f @* cyclic x = cyclic (f x).
Proof. by move=> G f x Gx; rewrite morphim_gen (sub1set, morphim_set1). Qed.

End MorphicImage.

(***********************************************************************)
(*                                                                     *)
(*       Automorphisms of cyclic groups                                *)
(*                                                                     *)
(***********************************************************************)

Section CyclicAutomorphism.

Variables gT1 gT2 : finGroupType.

Variable f : {perm gT1}.

Lemma cyclic_aut_stable : forall x,
  f \in Aut (cyclic x) -> f @: cyclic x = cyclic (f x).
Proof.
move=> x autf; rewrite -(autmE autf) -morphimEdom morphim_cyclic //.
exact: cyclicnn.
Qed.

Lemma order_aut_stable : forall x, f \in Aut (cyclic x) -> #[x]  = #[f x].
Proof.
move=> x autf; rewrite /orderg -cyclic_aut_stable ?card_imset //.
exact: perm_inj.
Qed.

(* From the multiplicative group to automorphisms *)

Lemma cyclic_gexpn_clos : forall (x : gT1) k,
  (expgn^~ k) @: cyclic x \subset cyclic x.
Proof.
move=> x k; apply/subsetP=> a; case/imsetP=> y; case/cyclicP=> n <- -> {a y}.
by rewrite -expgn_mul cyclic_in.
Qed.

Lemma cyclic_dcan_gexpn : forall (a : gT1) k, coprime #[a] k ->
  exists g, {in cyclic a, cancel (expgn^~ k) g}.
Proof.
move=> a k; case Hpos: (0 < k) => Hcop; last first.
  move: Hcop; move/idPn: Hpos; rewrite -eqn0Ngt; move/eqP->.
  rewrite coprime_sym /coprime gcd0n /orderg => Hcard.
  have Heq: (1%g : {set gT1}) =i cyclic a.
    apply/subset_cardP; last by rewrite sub1set; apply:group1.
    by move/eqP:Hcard->; rewrite cardsE card1.
  by exists (@id gT1) => x; rewrite expg0 //= -(Heq x); move/set1P=> <-.
case: (bezoutl #[a] Hpos); move=> x xinf.
rewrite coprime_sym /coprime in Hcop; move/eqP: Hcop->; move/dvdnP=> [k0 Hk0].
exists (fun z:gT1 => z ^+ k0)%g; move=> x0 Hx0 //=.
rewrite -expgn_mul mulnC -Hk0 expgn_add mulnC; case/cyclicP: Hx0 => i <-.
by rewrite expg1 -!expgn_mul mulnCA expgn_mul orderg_expn1 exp1gn mulg1.
Qed.

Lemma inj_gexpn : forall (a : gT1) k,
  coprime #[a] k -> {in cyclic a &, injective (expgn^~ k)}.
Proof.
move=> k a Hcop; move: (cyclic_dcan_gexpn Hcop)=> [g dcan].
by apply (in_can_inj dcan).
Qed.

Definition cycle_expgn of gT1 := fun k x => x ^+ k : gT1.

Lemma cycle_expgn_morphM : forall a k,
  {in cyclic a &, {morph cycle_expgn a k : x y / x * y}}.
Proof.
move=> a k x y cax cay; apply: expMgn; exact: commute_cyclic_com cay.
Qed.

Canonical Structure cycle_expgn_morphism a k :=
  Morphism (@cycle_expgn_morphM a k).

Lemma cycle_expgn_inj : forall a k, coprime #[a] k -> 'injm (cycle_expgn a k).
Proof. move=> a k coak; apply/injmP; exact: inj_gexpn. Qed.

Lemma cycle_expgn_on : forall a k, coprime #[a] k -> 
  cycle_expgn a k @* cyclic a = cyclic a.
Proof.
move=> a k coak; apply/morphim_fixP=> //; first exact: cycle_expgn_inj.
by rewrite morphimEdom cyclic_gexpn_clos.
Qed.

Definition cycle_aut_of a k (coak : coprime #[a] k) :=
  aut_of (cycle_expgn_inj coak) (cycle_expgn_on coak).

(* GG: Aut_aut_of proves cycle_aut_of coak \in Aut (cyclic a). *)

(* The converse : from automorphisms to the multiplicative group *)

Lemma cyclic_to_fp_loc_corr : forall x : gT1,
  f \in Aut (cyclic x) -> coprime #[x] (Ordinal (cyclic_to_zp_ord x (f x))).
Proof.
move=> x autf /=; set n := _ x (f x).
have Hfx: f x \in cyclic x.
  by rewrite -[cyclic x](autm_dom autf) mem_imset // setIid cyclicnn.
have:= cyclic_to_zp_corr Hfx; rewrite eq_sym -/n. 
case: (posnP n) => [-> {n} | npos Hn].
  rewrite (canF_eq (permK f)); move/eqP->.
  by rewrite -groupV in autf; rewrite -(autmE autf) morph1 orderg1.
have: gcdn #[x] n <= 1.
  rewrite leqNgt; apply/negP=> Hgcd; move: (divn_lt Hgcd (orderg_pos x)).
  rewrite ltn_neqAle; move: (orderg_gcd x npos); rewrite -(eqP Hn).
  move/eqP; rewrite -(order_aut_stable autf); move/eqP=> Hg.
  by rewrite {3}Hg eqxx andFb.
by rewrite leq_eqVlt orbC ltnNge ltn_0gcd npos pos_card_group.
Qed.

Lemma cyclic_to_fp_loc_repr : forall x,
  f \in Aut (cyclic x) ->
 (forall z, z \in cyclic x ->
    f z = z ^+ (Ordinal (cyclic_to_zp_ord x (f x))))%g.
Proof.
move=> x autf; have Cxx := cyclicnn x.
move=> z; case/cyclicP=> n <- {z}; rewrite -{1}(autmE autf) morphX //=.
have Cfx: f x \in cyclic x.
  by rewrite -[cyclic x](autm_dom autf) mem_imset // setIid.
by rewrite -expgn_mul mulnC expgn_mul (eqP (cyclic_to_zp_corr Cfx)).
Qed.

Definition cyclic_to_fp_loc (a : gT1) : perm gT1 -> 'I_(#[a]) :=
  fun f => if coprime #[a] (cyclic_to_zp_loc a (f a))
    then
      Ordinal (cyclic_to_zp_ord a (f a))
    else
      (zp1 [pos_nat of #[a]]).

Lemma cyclic_to_fp_corr : forall a, coprime #[a] (cyclic_to_fp_loc a f).
Proof.
move=> a; rewrite /cyclic_to_fp_loc.
case e: (coprime #[a] (cyclic_to_zp_loc a (f a))); [apply: (idP e) |apply: coprime_zp1].
Qed.

Lemma cyclic_to_fp_repr : forall a,
  f \in Aut (cyclic a) ->
  (cyclic_to_fp_loc a f) = Ordinal (cyclic_to_zp_ord a (f a)).
Proof.
by move=> a Haut; rewrite /cyclic_to_fp_loc (cyclic_to_fp_loc_corr Haut).
Qed.

End CyclicAutomorphism.

(***********************************************************************)
(*                                                                     *)
(*        Bijection with Fp                                            *)
(*                                                                     *)
(***********************************************************************)

Section FpAut.

Variable gT : finGroupType.

Definition cyclic_to_fp (a : gT) : perm gT -> fp_mul #[a] :=
  fun f => Sub (cyclic_to_fp_loc a f) (cyclic_to_fp_corr f a).

Definition fp_to_cyclic (x : gT) :=
  fun (D : fp_mul #[x]) => cycle_aut_of (valP D).

Lemma fp_morph : forall x : gT,
  {in Aut (cyclic x) &, {morph cyclic_to_fp x : y z / y * z}}.
Proof.
move=> a x y Hx Hy; do 2!apply: val_inj => /=.
rewrite !cyclic_to_fp_repr ?groupM //= permM.
rewrite {1}(cyclic_to_fp_loc_repr Hx) ?cyclicnn //=.
rewrite (cyclic_to_fp_loc_repr Hy) ?(groupX, cyclicnn) //=.
by rewrite -expgn_mul cyclic_to_zp_id.
Qed.

Canonical Structure cyclic_to_fp_morphism x := Morphism (@fp_morph x).

Lemma fp_can : forall a : gT,
  {in Aut (cyclic a), cancel (cyclic_to_fp a) (@fp_to_cyclic a)}.
Proof.
move=> a f Haut; symmetry; apply/permP=> x.
rewrite permE /= (cyclic_to_fp_repr Haut) /=.
case cax: (x \in cyclic a); first exact: cyclic_to_fp_loc_repr.
by move: Haut; rewrite inE; case/andP; move/out_perm->; rewrite ?cax.
Qed.

Lemma fp_inj : forall x : gT, 'injm (cyclic_to_fp x).
Proof. move=> a; apply/injmP; exact: in_can_inj (@fp_can a). Qed.

Lemma fp_isom : forall a : gT, isom (Aut (cyclic a)) setT (cyclic_to_fp a).
Proof.
move=> a; apply/isomP; split; first exact: fp_inj.
apply/setP=> x; rewrite inE morphimEdom.
apply/imsetP; exists (fp_to_cyclic x); first exact: Aut_aut_of.
do 2!apply: val_inj; rewrite /= cyclic_to_fp_repr ?Aut_aut_of //=.
by rewrite permE cyclicnn cyclic_to_zp_id modn_small.
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
rewrite /generator -morphim_cyclic // !eqset_sub.
by rewrite !morphimSGK //= ?(subset_trans injf, sub1G, cyclic_h).
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

Lemma zp_group_cyclic : forall (n : pos_nat) k (H : k < n),
  coprime k n -> setT = cyclic (Ordinal H).
Proof.
move=> n k H Hcop; symmetry; apply/setP; apply/subset_eqP; apply/andP.
split; first by apply/subsetP=> x //= Hx ; rewrite inE.
apply/subsetP; move=> x _ /=; apply/cyclicP; move: k H Hcop x.
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
  apply:zp_group_cyclic=> /=; by [apply: (valP (i : 'I_n)) | apply: Hcop].
move/(setT =P _)=> Hcop.
case e: (0 < (i : 'I_n)).
  apply:modn_coprime; first exact: (idP e).
  have H1: (1 < n) by apply: leq_ltn_trans (valP (i : 'I_n)); apply:(idP e).
  have: Ordinal H1 \in cyclic i by rewrite -Hcop inE.
  by case/cyclicP=> n1; rewrite (zp_ord i) expgn_muln /=; case; exists n1.
move/negbT:e; rewrite lt0n negbK; move/eqP=> i0.
have i1 : i = 1 by exact: val_inj.
by rewrite i0 -(card_ord n) -cardsT Hcop i1 cyclic_unit cards1.
Qed.

Lemma generator_coprime : forall m,
  coprime m #[a] = generator (cyclic a) (a ^+ m).
Proof.
move=> m; rewrite (generator_bij (zp_inj a)) ?cyclic_in //=.
case/isomP: (zp_isom a) => _ /= ->; rewrite /coprime -gcdn_modl.
have Hmod: m %% #[a] < #[a] by rewrite ltn_mod (orderg_pos a).
have:= @zp_gen [is #[a] : _ <: pos_nat] (Ordinal Hmod).
rewrite /= /coprime => <-; congr generator; apply: val_inj=> /=.
by rewrite cyclic_to_zp_id.
Qed.

Lemma phi_gen : phi #[a] = #|[pred x | generator (cyclic a) x]|.
Proof.
rewrite /phi /=; set n := #[a].
have: [pred x : 'I_n | coprime n x] =i
      [pred x : 'I_n | generator (cyclic a) (a ^+ x)].
  by move=> x /=; rewrite !inE /= -generator_coprime coprime_sym.
move/eq_card=> ->.
suff: (image (cyclic_to_zp a) (generator (cyclic a))) =i
        [pred x : 'I_n | generator (cyclic a) (a ^+ x)].
  move/eq_card <-; apply: card_dimage; move/injmP: (zp_inj a).
  apply: subin2; exact: cyclic_generator.
move=> x; apply/imageP/idP; rewrite inE /=.
  move=> [x0 Hx0 ->]; move: (cyclic_generator Hx0); move/cyclic_to_zp_corr.
  by move/eqP; rewrite /cyclic_to_zp /= => ->.
move=> Hgen; exists (a ^+ x)%g; first by trivial.
apply: val_inj; rewrite /cyclic_to_zp /=.
move: (cyclic_to_zp_corr (cyclic_generator Hgen)); rewrite eq_sym.
move/(conj (valP x))=> /=; move/andP; move/decomp_order_unicity=> /=.
by rewrite cyclic_to_zp_ord; move/(_ is_true_true).
Qed.

End ZpAut.

Section CyclicAutomorphism_Abelian.

(* G. 1.3.10 *)

Variable gT : finGroupType.

Lemma aut_cyclic_commute : forall x : gT, abelian (Aut (cyclic x)).
Proof.
move=> x; have:= isom_isog (fp_isom x); rewrite isog_sym.
case/isogP=> f _ /= <-; apply/centralP; apply: morphim_central.
by apply/centralP=> m _ n _; do 2!apply: val_inj => /=; rewrite mulnC.
Qed.

End CyclicAutomorphism_Abelian.
