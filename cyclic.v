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
Require Import seq fintype paths connect.
Require Import groups normal div zp finset bigops group_perm automorphism.
Require Import fp.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Phi.

(***********************************************************************)
(*                                                                     *)
(*  Euler phi function                                                 *)
(*                                                                     *)
(***********************************************************************)

Definition phi n := #|[eta coprime n] : pred I_(n)|.

Lemma phi_mult: forall m n,
  coprime m n -> phi (m * n) = phi m * phi n.
Proof.
move => m n H0; rewrite /phi -![@card {I_(_) : as finType} _]card_sig /=.
rewrite (mulnC (card _)) -card_prod /=.
pose cops u := sig_finType (fun x : fzp u => coprime u x).
change (#|cops (m * n)| = #|@predT (cops n * cops m)|).
apply: bij_eq_card_predT.
have Hf1: forall x : cops (m * n), val x %% n < n.
  move => [[x Hx] Hx1] /=.
  by rewrite ltn_mod; move: (Hx); case n => //; rewrite mulnC.
have Hf2: forall x : cops (m * n),
  coprime n (Ordinal (Hf1 x)).
  move => [[x Hx] Hx1] /=; rewrite /= in Hx1.
  rewrite /coprime gcdn_modr.
  rewrite coprime_mull in Hx1.
  by case/andP: Hx1.
have Hf3: forall x: cops (m * n), val x %% m < m.
  move => [[x Hx] Hx1] /=.
  by rewrite ltn_mod; move: (Hx); case m => //; rewrite mulnC.
have Hf4: forall x : cops (m * n),
  coprime m (Ordinal (Hf3 x)).
  move => [[x Hx] Hx1] /=; rewrite /= coprime_mull in Hx1.
  case/andP: Hx1 => Hx1 Hx2.
  by rewrite /coprime gcdn_modr.
pose f (x : cops (m * n)) : cops n * cops m :=
   (exist (fun y : fzp n => coprime n y) _ (Hf2 x),
    exist (fun y : fzp m => coprime m y) _ (Hf4 x)).
have Hf5: forall x: prod_finType (cops n) (cops m),
   chinese m n (val x.2) (val x.1) %% (m * n) < m * n.
    move => [[[x Hx] Hx1] [[y Hy] Hy1]] /=; rewrite ltn_mod.
    by move: (Hx) (Hy); case m; case n.
have Hf6: forall x : prod_finType (cops n) (cops m),
  coprime (m * n) (Ordinal (Hf5 x)).
(*    (val (EqSig  (fun p : nat_eqType => p < m * n) _ (Hf5 x))).*)
  move => [[[x Hx] Hx1] [[y Hy] Hy1]] /=.
  have F1: 0 < n; first by move: (Hx); case n.
  have F2: 0 < m; first by move: (Hy); case m.
  rewrite /coprime /= gcdn_modr [_ == _]coprime_mull /coprime.
  rewrite gcdnC -gcdn_modl chinese_modl // gcdn_modl gcdnC [_ == _]Hy1.
  by rewrite gcdnC -gcdn_modl chinese_modr // gcdn_modl gcdnC [_ == _]Hx1.
pose g x : cops (m * n) :=
  exist (fun x : fzp (m * n) => coprime (m * n) x) _ (Hf6 x).
exists f; exists g.
  move => [[x Hx] Hx1].
  have F1: 0 < n; first by move: (Hx); rewrite mulnC; case n.
  have F2: 0 < m; first by move: (Hx); case m.
  do !apply: val_inj; rewrite /f /g /=.
  by rewrite -chinese_remainderf // modn_small.
move => [[[x Hx] Hx1] [[y Hy] Hy1]].
have F1: 0 < n; first by move: (Hx); case n.
have F2: 0 < m; first by move: (Hy); case m.
congr (_, _); do ![apply: val_inj] => /=; set e := chinese _ _ _ _.
- rewrite -(modn_addl_mul (e %/ (m * n) * m)) -mulnA -divn_eq.
  by rewrite chinese_modr // modn_small.
rewrite -(modn_addl_mul (e %/ (m * n) * n)) -mulnA (mulnC n) -divn_eq.
by rewrite chinese_modl // modn_small.
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
suff: p %| x = ~~ predC a (Ordinal Hx) by move=>->; apply/negPn/idP.
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

Definition cyclic_to_zp (a : gT) : gT -> I_(#[a]) :=
  fun x => Ordinal (cyclic_to_zp_ord a x).

Definition zp_to_cyclic a (n : I_(#[a])) : FinGroup.sort gT := a ^+ n.

Lemma zp_morph (a : gT) : morphic (cyclic a) (cyclic_to_zp a).
Proof.
move=>a; apply/morphP=> x y Hx Hy.
move: (cyclic_to_zp_corr Hx) (cyclic_to_zp_corr Hy); move/eqP=> Hcorx.
move/eqP=> Hcory; rewrite -{1}Hcorx -{1}Hcory -expgn_add.
by apply: val_inj; rewrite /= cyclic_to_zp_id.
Qed.

Lemma zp_inj (a : gT) : injm (cyclic_to_zp a) (cyclic a).
Proof.
move=> a; apply/(injmorphicP (zp_morph a))=> x y /= Hx Hy Heq.
move:(cyclic_to_zp_corr Hx) (cyclic_to_zp_corr Hy); move/eqP=><-; move/eqP=><-.
congr expgn.
replace (cyclic_to_zp_loc a x) with (val (cyclic_to_zp a x)); last by trivial.
replace (cyclic_to_zp_loc a y) with (val (cyclic_to_zp a y)); last by trivial.
by rewrite Heq.
Qed.

Lemma zp_isom (a : gT) : isom (cyclic_to_zp a) (cyclic a) setT.
Proof.
move=> a; rewrite /isom zp_inj andbT; apply/eqP; apply/setP.
apply/subset_cardP; last by apply/subsetP=> x Hx; rewrite inE.
rewrite card_dimset; last by apply/(injmorphicP (zp_morph a)); exact: zp_inj.
by rewrite cardsT card_zp.
Qed.

(***********************************************************************)
(*                                                                     *)
(*        Order properties  (2/2)                                      *)
(*                                                                     *)
(***********************************************************************)

Lemma orderg_dvd: forall a n, (#[a] %| n) = (a ^+ n == 1).
Proof.
move=> a n; rewrite expgn_modnorder /dvdn; apply/idP/idP.
  by move/eqP=>->; rewrite expg0.
rewrite -(expg0 a); move : (orderg_pos a); rewrite -(ltn_mod n)=>H.
by move/(conj H); move/andP; move/(decomp_order_unicity (orderg_pos a))=><-.
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
  rewrite {1}/dvdn; move/eqP=>H1; rewrite {1}H1 addn0=>{H1} H1.
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
     = [set {cyclic (a ^+ (#[a] %/ m)) as group _}].
Proof.
move=> a m Hdiv.
have Hpos: 0 < m by apply (ltn_0dvd (orderg_pos a) Hdiv).
have Hcardm: #|cyclic (a ^+ (#[a] %/ m))| == m.
  have Hdivpos: 0 < #[a] %/ m by
    rewrite -(ltn_pmul2r Hpos) mul0n (divnK Hdiv) orderg_pos.
  rewrite [card ( _)](orderg_gcd _ Hdivpos).
  rewrite {2}(divn_eq #[a] m) mulnC; move:{+}Hdiv; rewrite /dvdn.
  move/eqP=>->; rewrite gcdnC gcdn_addl_mul gcdn0.
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
  H \subset (cyclic a) ->
  characteristic (cyclic a) H.
Proof.
move=> a H Hsub.
case e: #|H| => [|k]; first by move: (pos_card_group H); rewrite e //.
apply: (lone_subgroup_char _ e)=>// J HsubJ HcardJ.
move/setP: (cyclic_sub_group (group_dvdn Hsub)); move/subset_eqP.
move/andP=>[Hcyc _]; move/subsetP: Hcyc=> Hcyc; move/implyP: (Hcyc H).
rewrite /= in_set1 inE eqxx /= Hsub andTb /=; move/eqP->.
move/implyP: (Hcyc J); rewrite in_set1 inE HcardJ HsubJ -e andTb eqxx /=.
by move/eqP.
Qed.

End CyclicSubGroup.

Section MorphicImage.

Variables G G' : finGroupType.

Lemma cyclic_morph_stable : forall (f : G -> G') x,
  morphic (cyclic x) f -> f @: cyclic x = cyclic (f x).
Proof.
move=> f x Hmorph.
rewrite (dfequal_imset (dfequal_morphicrestr Hmorph)) /=.
case e: (trivm_(cyclic x) f)%g; last first.
  rewrite gen_f_com /=.
    by rewrite imset_set1 -(dfequal_morphicrestr Hmorph (cyclicnn x)).
  rewrite /morphicrestr Hmorph /= (dom_mrestr Hmorph _ ); last by rewrite e.
  by rewrite sub1set cyclicnn.
rewrite (dfequal_morphicrestr Hmorph (cyclicnn x)).
move: (trivm_mrestr f (cyclic x)); rewrite e orTb /morphicrestr Hmorph /=.
move/trivm_is_cst=> Htriv; move: (Htriv x) => /= ->.
apply/setP=> y; apply/imsetP/cyclicP=> [[z _ ->] | [n <-]].
  by exists 0; rewrite Htriv.
by exists x; rewrite ?cyclicnn // exp1gn Htriv.
Qed.

End MorphicImage.

(***********************************************************************)
(*                                                                     *)
(*       Automorphisms of cyclic groups                                *)
(*                                                                     *)
(***********************************************************************)

Section CyclicAutomorphism.

Variables G G' : finGroupType.

Variable f : {perm G}.

Lemma cyclic_aut_stable : forall x,
  Aut (cyclic x) f -> f @: cyclic x = cyclic (f x).
Proof.
move=> x HAut; move:{+}HAut; move/andP=> [Hperm Hmorph].
apply: (cyclic_morph_stable Hmorph).
Qed.

Lemma order_aut_stable : forall x, Aut (cyclic x) f -> #[x]  = #[f x].
Proof.
move=> x Haut; rewrite /orderg; apply eq_card.
move: (isom_morph_of_aut Haut)=>//=; rewrite /isom.
move/andP=> [Hmorph _]; move/eqP: Hmorph=><-.
rewrite (@dfequal_imset _ _ (morph_of_aut f (cyclic x)) f).
  by apply/setP; apply: cyclic_aut_stable.
exact: (morph_of_aut_ondom Haut).
Qed.

(* From the multiplicative group to automorphisms*)

Lemma cyclic_gexpn_clos : forall (x : G) k,
  (expgn^~ k) @: cyclic x \subset cyclic x.
Proof.
move=> x k; apply/subsetP=> a; case/imsetP=> y; case/cyclicP=> n <- -> {a y}.
by rewrite -expgn_mul cyclic_in.
Qed.

Lemma cyclic_dcan_gexpn : forall (a : G) k, coprime #[a] k ->
  exists g, {in cyclic a, cancel (expgn^~ k) g}.
Proof.
move=> a k; case Hpos: (0 < k) => Hcop; last first.
  move: Hcop; move/idPn: Hpos; rewrite -eqn0Ngt; move/eqP=>->.
  rewrite coprime_sym /coprime gcd0n /orderg => Hcard.
  have Heq: (1%g : {set G}) =i cyclic a.
    apply/subset_cardP; last by rewrite sub1set; apply:group1.
    by move/eqP:Hcard=>->; rewrite cardsE card1.
  by exists (@id G) => x; rewrite expg0 //= -(Heq x); move/set1P=><-.
case: (bezoutl #[a] Hpos); move=> x xinf.
rewrite coprime_sym /coprime in Hcop; move/eqP: Hcop=>->; move/dvdnP=>[k0 Hk0].
exists (fun z:G => z ^+ k0)%g; move=> x0 Hx0 //=.
rewrite -expgn_mul mulnC -Hk0 expgn_add mulnC; case/cyclicP: Hx0 => i <-.
by rewrite expg1 -!expgn_mul mulnCA expgn_mul orderg_expn1 exp1gn mulg1.
Qed.

Lemma inj_gexpn : forall (a : G) k,
  coprime #[a] k -> {in cyclic a &, injective (expgn^~ k)}.
Proof.
move=> k a Hcop; move: (cyclic_dcan_gexpn Hcop)=>[g dcan].
by apply (in_can_inj dcan).
Qed.

Lemma gexpn_automorphic : forall a k (D : coprime #[a] k),
  Aut (cyclic a) (perm_of_restriction (cyclic_gexpn_clos _ _) (inj_gexpn D)).
Proof.
move=> a k D.
apply/andP; split.
  apply/subsetP=> x; rewrite inE /= permE /restr.
  by case e: (x \in (cyclic a)); rewrite ?eqxx.
apply/morphP=> x y Hx Hy; rewrite !permE /restr Hx Hy (groupM Hx Hy) expMgn //.
exact: commute_cyclic_com Hx y Hy.
Qed.

(* The converse : from automorphisms to the multiplicative group *)

Lemma cyclic_to_fp_loc_corr : forall x : G,
  Aut (cyclic x) f -> coprime #[x] (Ordinal (cyclic_to_zp_ord x (f x))).
Proof.
move=> x Haut; rewrite coprime_sym.
case e: (trivm_(cyclic x) f).
  move/forallP: e=> e; move: (e x); rewrite cyclicnn /=; move/eqP .
  move=> Hfx; move:{+}Haut {+}Hfx; move/andP=>[_]; move/morphic1=><-.
  move/perm_inj; rewrite Hfx=>->.
  by rewrite /cyclic_to_zp_loc /ctzl !orderg1 subnn exp1gn eqxx coprimen1.
have Hfx: f x \in cyclic x.
  move/andP: Haut=>[Hperm _].
  by rewrite (perm_closed x Hperm) cyclicnn.
move: (cyclic_to_zp_corr Hfx); set n:= (cyclic_to_zp_loc x (f x)) =>Hn.
have: (0 < n) || (x == 1).
  case x1: (x == 1)%g; first by rewrite orbT.
  rewrite orbF ltnNge leqn0; apply/negP=> //= H; move:Hn; move/eqP: H=>->.
  rewrite expg0 eq_sym -(morph_of_aut_ondom Haut (cyclicnn x)).
  move/eqP; move/kerMP; rewrite (dom_morph_of_aut Haut (negbT e)) ?cyclicnn.
  move/(_ is_true_true); move/setP: (ker_injm (morph_of_aut_injm Haut)).
  move/(_ x); rewrite inE cyclicnn andbT=>->; move/set1P; move/eqP.
  by rewrite x1.
move/orP=>[Hpos|H1] /=; last by move/eqP:H1=>->; rewrite orderg1; apply:coprimen1.
have: (gcdn #[x] n <= 1).
  rewrite leqNgt; apply/negP=> Hgcd; move: (divn_lt Hgcd (orderg_pos x)).
  rewrite ltn_neqAle; move: (orderg_gcd x Hpos); move/eqP: Hn=>->.
  move/eqP; rewrite -(order_aut_stable Haut); move/eqP=>Hg.
  by rewrite {3}Hg eqxx andFb.
rewrite leq_eqVlt ltnS leqn0 eqn0Ngt ltn_0gcd Hpos orbT orbF.
by rewrite gcdnC; apply.
Qed.

Lemma cyclic_to_fp_loc_repr : forall (x:G),
  Aut (cyclic x) f ->
 (forall z, z \in cyclic x ->
     f z = z ^+ (Ordinal (cyclic_to_zp_ord x (f x))))%g.
Proof.
move=> x Haut; have Cxx := cyclicnn x.
case e: (trivm_(cyclic x) f)%g => /=.
  move/forallP: e => e z Hcyc; move: (e z); rewrite Hcyc /=; move/eqP=> Hfz.
  move: (cyclicnn x); rewrite -(perm_closed _ (proj1 (andP Haut)))=> Hfx.
  rewrite Hfz; move:{+}Haut {+}Hfz; move/andP=>[_]; move/morphic1=>Hf1.
  by rewrite -{1}Hf1; move/perm_inj=>->; rewrite exp1gn.
move=> z; case/cyclicP=> n <- {z}; have fE := morph_of_aut_ondom Haut.
rewrite -fE (groupX, morphX) // ?(dom_morph_of_aut, e) // [_ x]fE //.
have Cfx: f x \in cyclic x by rewrite perm_closed //; case/andP: Haut.
by rewrite -expgn_mul mulnC expgn_mul (eqP (cyclic_to_zp_corr Cfx)).
Qed.

(* the unit for the multiplicative group *)

Definition zp1 (n : pos_nat) : ordinal_finType n.
case; case; first by case/negP; rewrite ltn0.
case; first by exists (Ordinal (ltnSn 0)).
move=>n i; by exists (Ordinal (ltnSSn n)).
Defined.

Lemma zp11 : forall (n:nat) (H: 0 < n.+2),
  (zp1 (PosNat H)) = (Ordinal (ltnSSn n)).
Proof.  by case=> [|n] H; apply: val_inj=>//=. Qed.

Lemma zp10 : forall (H : 0 < 1), (zp1 (PosNat H)) = (Ordinal H).
Proof. trivial. Qed.

Lemma coprime_zp1 : forall n: pos_nat, coprime n (zp1 n).
Proof.
case; case; first by case/negP; rewrite ltn0.
case=> [|n] H; first by rewrite zp10.
by rewrite zp11; apply coprimen1.
Qed.

Definition cyclic_to_fp_loc (a : G) : perm G -> I_(#[a]) :=
  fun f => if coprime #[a] (cyclic_to_zp_loc a (f a))
    then
      Ordinal (cyclic_to_zp_ord a (f a))
    else 
      (zp1 {#[a] as pos_nat}).

Lemma cyclic_to_fp_corr : forall a, coprime #[a] (cyclic_to_fp_loc a f).
Proof.
move=> a; rewrite /cyclic_to_fp_loc.
case e: (coprime #[a] (cyclic_to_zp_loc a (f a))); [apply: (idP e) |apply: coprime_zp1].
Qed.

Lemma cyclic_to_fp_repr : forall a,
  Aut (cyclic a) f -> 
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

Variable G : finGroupType.

Definition cyclic_to_fp (a : G) : perm G -> fp_mul #[a] :=
  fun f => Sub (cyclic_to_fp_loc a f) (cyclic_to_fp_corr f a).

Definition fp_to_cyclic (x:G) :=
  fun (D : fp_mul #[x]) =>
    (perm_of_restriction (cyclic_gexpn_clos _ _) (inj_gexpn (valP D))).

Lemma fp_morph : forall (x:G),
  morphic (set_of (Aut (cyclic x))) (cyclic_to_fp x).
Proof.
move=> a; apply/morphP=> x y; rewrite !inE=> Hx Hy.
rewrite /cyclic_to_fp; apply: val_inj=>/=.
rewrite (cyclic_to_fp_repr Hx) (cyclic_to_fp_repr Hy) /=.
have: (x * y)%g \in set_of (Aut (cyclic a)) by apply: groupM; rewrite inE.
rewrite inE=> Haut; rewrite (cyclic_to_fp_repr Haut); apply: val_inj=>/=.
rewrite /mulg /perm_mul /= /perm_mul permE /comp /=.
rewrite {1}(cyclic_to_fp_loc_repr Hx (cyclicnn a)) /=.
move: (cyclic_in a (cyclic_to_zp_loc a (x a))).
by move/(cyclic_to_fp_loc_repr Hy)=>/=->; rewrite -expgn_mul cyclic_to_zp_id.
Qed.

Lemma fp_can : forall (a:G),
  {in (set_of (Aut (cyclic a))), cancel (cyclic_to_fp a) (@fp_to_cyclic a)}.
Proof.
move=> a f; rewrite inE=> Haut; apply/permP.
move=> x; rewrite permE=>/=.
rewrite (cyclic_to_fp_repr Haut) /= /restr.
case e:(x \in cyclic a).
  by symmetry; move: (cyclic_to_fp_loc_repr Haut (idP e))=>/=.
by symmetry; apply: (out_perm (proj1 (andP Haut)) (negbT e)).
Qed.

Lemma fp_inj : forall x : G, injm (cyclic_to_fp x) (set_of (Aut (cyclic x))).
Proof.
move=> a; apply/(injmorphicP (fp_morph a)); apply (in_can_inj  (@fp_can a)).
Qed.

Lemma fp_isom : forall a : G,
  isom (cyclic_to_fp a) (set_of (Aut (cyclic a))) setT.
Proof.
move=> a; rewrite /isom fp_inj andbT eqset_sub subsetT; apply/subsetP=> /= x _.
apply/imsetP; exists (fp_to_cyclic x).
  rewrite inE /fp_to_cyclic; exact: gexpn_automorphic.
apply: val_inj=> /=; rewrite (cyclic_to_fp_repr (gexpn_automorphic (valP x))).
by apply: val_inj; rewrite /= permE /restr cyclicnn cyclic_to_zp_id modn_small.
Qed.

End FpAut.

(***********************************************************************)
(*                                                                     *)
(*       Automorphism with Zp, consequences on generators              *)
(*                                                                     *)
(***********************************************************************)

Section GenAut.

Variables G G' : finGroupType.

Lemma generator_bij : forall (f : G -> G') (H : group G),
  injm f H -> morphic H f ->
  forall a, a \in H -> generator H a = generator (f @: H) (f a).
Proof.
move=> f H Hinj Hmorph a Ha.
have:= morphic_subgroup (cyclic_h Ha) Hmorph => /=.
move/cyclic_morph_stable=> Hcyc; apply/eqP/eqP=> [-> //| fH].
apply/eqP; rewrite eq_sym eqset_sub_card cyclic_h //=.
move/(injmorphicP Hmorph): Hinj => Hinj.
by rewrite -(card_dimset Hinj) fH -Hcyc leq_imset_card.
Qed.

End GenAut.

Section ZpAut.

Variable G : finGroupType.
Variable a : G.

Lemma expgn_muln : forall k (n : pos_nat) p (H : p < n),
  Ordinal H ^+ k = Ordinal (ltn_pmod (p * k) (valP n)).
Proof.
elim=>[|k IH] n p H; apply: val_inj=> //=; first by rewrite muln0 modn_small.
by rewrite expgS IH //= modn_addmr -{1}(muln1 p) -muln_addr add1n.
Qed.

Lemma zp_group_cyclic : forall (n : pos_nat) k (H : k < n),
  coprime k n -> setT = cyclic (Ordinal H).
Proof.
move=>n k H Hcop; symmetry; apply/setP; apply/subset_eqP; apply/andP.
split; first by apply/subsetP=> x //= Hx ; rewrite inE.
apply/subsetP; move=> x _ /=; apply/cyclicP; move: k H Hcop x.
case=> [|k] H Hcop /= x0.
  rewrite /coprime gcd0n in Hcop; exists 1%N; move: (valP x0).
  move/eqP:Hcop=>Hn; rewrite {3}Hn !ltnS !leqn0; move/eqP => H0.
  by apply: val_inj; rewrite /= addn0 /= H0 modn_small.
case: (egcdnP n (ltn0Sn k))=> kk kn Heq Hineq.
exists (kk * x0)%N; rewrite /= expgn_muln; apply: val_inj => /=.
rewrite mulnA (mulnC (k.+1)) Heq muln_addl -(mulnA kn) (mulnC n) mulnA.
move: Hcop; rewrite modn_addl_mul /coprime; move/eqP=>->.
by rewrite mul1n modn_small.
Qed.

Lemma zp_ord : forall (n : pos_nat) (i : zp_group n),
  i = Ordinal (valP (i : I_(n))).
Proof. by move=> n i; apply: val_inj. Qed.

Lemma zp_gen : forall (n : pos_nat) (i : I_(n)),
  generator setT i = coprime i n.
Proof.
move=> n i; apply/idP/idP; last first.
  move=> Hcop; apply/eqP.
  apply:zp_group_cyclic=>/=; by [apply: (valP (i : I_(n))) | apply: Hcop].
move/(setT =P _)=> Hcop.
case e: (0 < (i : I_(n))).
  apply:modn_coprime; first exact: (idP e).
  have H1: (1 < n) by apply: leq_ltn_trans (valP (i : I_(n))); apply:(idP e).
  have: Ordinal H1 \in cyclic i by rewrite -Hcop inE.
  by case/cyclicP=> n1; rewrite (zp_ord i) expgn_muln /=; case; exists n1.
move/negbT:e; rewrite lt0n negbK; move/eqP=> i0.
have i1 : i = 1 by exact: val_inj.
by rewrite i0 -(card_ord n) -cardsT Hcop i1 cyclic_unit cards1.
Qed.

Lemma generator_coprime : forall m,
  coprime m #[a] = generator (cyclic a) (a ^+ m).
Proof.
move=> m; rewrite (generator_bij (zp_inj a) (zp_morph a)); last exact: cyclic_in.
rewrite coprime_sym /coprime gcdnE (negbET (lt0n_neq0 (orderg_pos a))).
move/andP:(zp_isom a)=> [H _]; move/eqP:H =>->.
have Hmod: m %% #[a] < #[a] by rewrite ltn_mod (orderg_pos a).
have:= (@zp_gen {#[a] as pos_nat} (Ordinal Hmod)); rewrite /= /coprime =><-.
congr generator; rewrite /cyclic_to_zp;  apply: val_inj=>/=.
by rewrite cyclic_to_zp_id.
Qed.

Lemma phi_gen : phi #[a] = #|[pred x | generator (cyclic a) x]|.
Proof.
rewrite /phi /=; set n := #[a].
have: [pred x : I_(n) | coprime n x] =i
      [pred x : I_(n) | generator (cyclic a) (a ^+ x)].
  by move=> x /=; rewrite !inE /= -generator_coprime coprime_sym.
move/eq_card=>->.
suff: (image (cyclic_to_zp a) (generator (cyclic a))) =i
        [pred x : I_(n) | generator (cyclic a) (a ^+ x)].
  move/eq_card <-; apply: card_dimage; move/injmorphicP: (zp_inj a).
  move/(_ (zp_morph a)); apply: subin2; exact: cyclic_generator.
move=> x; apply/imageP/idP; rewrite inE /=.
  move=> [x0 Hx0 ->]; move: (cyclic_generator Hx0); move/cyclic_to_zp_corr.
  by move/eqP; rewrite /cyclic_to_zp /= =>->.
move=> Hgen; exists (a ^+ x)%g; first by trivial.
apply: val_inj; rewrite /cyclic_to_zp /=.
move: (cyclic_to_zp_corr (cyclic_generator Hgen)); rewrite eq_sym.
move/(conj (valP x))=>/=; move/andP; move/decomp_order_unicity=>/=.
by rewrite cyclic_to_zp_ord; move/(_ is_true_true).
Qed.

End ZpAut.

Section CyclicAutomorphism_Abelian.

(* G. 1.3.10 *)

Variable G : finGroupType.

Lemma aut_cyclic_commute : forall (x : G) f g,
  Aut (cyclic x) f -> Aut (cyclic x) g -> commute f g.
Proof.
move=> x f g Hautf Hautg.
move: (cyclic_to_fp_loc_corr Hautf) (cyclic_to_fp_loc_repr Hautf).
set kf := (Ordinal (cyclic_to_zp_ord x (f x))) => Hcop_kf Heq_kf.
move: (cyclic_to_fp_loc_corr Hautg) (cyclic_to_fp_loc_repr Hautg).
set kg := (Ordinal (cyclic_to_zp_ord x (g x))) => Hcop_kg Heq_kg.
apply/permP=> z; rewrite !permE.
case e: (z \in cyclic x); last first.
  move: Hautf Hautg; move/andP=> [Hpermf _]; move/andP=> [Hpermg _].
  have Hf := out_perm Hpermf (negbT e); have Hg := out_perm Hpermg (negbT e).
  by rewrite /= Hf Hg Hf.
move/idP: e => e; rewrite /= (Heq_kf _ e) (Heq_kg _ e).
case/cyclicP: e=> n <-.
rewrite -!expgn_mul (Heq_kf _ (cyclic_in _ (n * kg))).
rewrite  (Heq_kg _ (cyclic_in _ (n * kf))) -!expgn_mul -mulnA.
by rewrite [(kf * kg) %N]mulnC mulnA.
Qed.

End CyclicAutomorphism_Abelian.
