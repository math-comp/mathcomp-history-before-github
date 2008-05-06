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

Open Scope nat_scope.

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

Section Cyclic.

Open Scope group_scope.

Variable G : finGroupType.

Definition cyclic (a:G) := << [set a] >>.

Definition orderg x := #|cyclic x|.

Lemma cyclic1 : forall a : G, 1 \in cyclic a.
Proof. move=> a; exact: group1. Qed.

Definition cyclicpred (a : G) := set_of (fconnect (mulg a) 1).

(*
Lemma expgn_itern: forall (a: G) n, a ^+ n = iter n (mulg a) 1.
Proof. by move=> a; elim=> /= [|n Rec]; [|rewrite /comp Rec]. Qed.
*)
Lemma cyclicpredP : forall a b,
  reflect (exists n, a ^+ n == b) (b \in cyclicpred a).
Proof.
move=> a b; rewrite inE; apply: (iffP connectP) => [[p]|[n Heq]].
  by case/fpathP=> m <- {p} <-; exists m; rewrite last_traject eqxx.
exists (traject (mulg a) (a * 1) n); first exact: fpath_traject.
rewrite last_traject; exact/eqP.
Qed.

Lemma group_cyclicpred : forall a, group_set (cyclicpred a).
Proof.
move=> a; apply/group_setP; split; first by apply/cyclicpredP; exists 0.
move=> x y; move/cyclicpredP=> [nx Hnx]; move/cyclicpredP=> [ny Hny].
apply/cyclicpredP; exists (nx + ny); move/eqP: Hnx; move/eqP: Hny => <- <-.
by rewrite expgn_add.
Qed.

Lemma cyclic_cyclicpred : forall a, (cyclic a) = (cyclicpred a).
Proof.
move=> a; apply/setP.
apply/subset_eqP; apply/andP; split; last first.
  apply/bigcap_inP; move=> i; rewrite sub1set=> Hi.
  apply/subsetP=>x; move/cyclicpredP =>[n Heq].
  by move/eqP: Heq => <-; apply: groupX.
apply: (@bigcap_inf _ _  _ _ (Group (group_cyclicpred a))).
by rewrite sub1set; apply/cyclicpredP; exists 1%N; rewrite expg1.
Qed.

Lemma cyclicpred_order : forall a, orderg a = order (mulg a) 1.
Proof.
move=> a; rewrite /orderg cyclic_cyclicpred /order.
by apply eq_card=> x; rewrite inE.
Qed.

Lemma cyclicP : forall a b,
  reflect (exists n, a ^+ n == b) (b \in cyclic a).
Proof. move=> a b; rewrite cyclic_cyclicpred; exact: cyclicpredP. Qed.

Lemma cyclic_h : forall a (H : {group G}), a \in H -> cyclic a \subset H.
Proof.
move=> a h Ha; apply/subsetP=>x; move/bigcapP; move/(_ h).
by rewrite sub1set; apply.
Qed.

Lemma cyclic_decomp : forall a b,
  b \in cyclic a -> {m : nat | (m < orderg a) && (a ^+ m == b)}.
Proof.
move=> a b; rewrite cyclic_cyclicpred cyclicpred_order inE.
move=> Hcyc.
move: (findex_max Hcyc) (iter_findex Hcyc) => Hindex Hval.
exists (findex (mulg a) 1 b); move: Hval.
by rewrite Hindex andTb; move/eqP.
Qed.

Lemma cyclicPmin : forall a b,
  reflect (exists m, (m < orderg a) && (a ^+ m == b)) (b \in cyclic a).
Proof.
move => a b; apply: (iffP idP).
  by move=> H; case: (cyclic_decomp H) => m Hm; exists m.
by case=> m; case/andP=> H1 H2; apply/cyclicP; exists m.
Qed.

Lemma cyclic_in: forall a m, a ^+ m \in cyclic a.
Proof. by move=> a m; apply/cyclicP; exists m; rewrite eq_refl. Qed.

Lemma cyclic_expgn: forall a b n, b \in cyclic a -> b ^+ n \in cyclic a.
Proof. move=> a; exact: groupX. Qed.

Lemma cyclicnn: forall a, a \in cyclic a.
Proof. move=> a; rewrite -{1}(expg1 a); exact: cyclic_in. Qed.

(***********************************************************************)
(*                                                                     *)
(*        Order Properties (1/2)                                       *)
(*                                                                     *)
(***********************************************************************)


Lemma orderg1: orderg 1 = 1%N.
Proof.
rewrite /orderg (cardD1 1) cyclicnn -(addn0 1%N); congr addn.
apply: eq_card0 => x; apply/negP.
case/andP => H1; case/cyclicP => n; rewrite exp1gn eq_sym => H2.
by case/negP: H1.
Qed.

Lemma orderg_pos: forall a, 0 < orderg a.
Proof. by move => a; rewrite /orderg (cardD1 a) cyclicnn. Qed.
Hint Resolve orderg_pos.
Canonical Structure orderg_pos_nat a := PosNat (orderg_pos a).

Canonical Structure group_cyclic a := [group of cyclic a].

Lemma cyclic_conjgs: forall a b,
   cyclic (a ^ b) =i (cyclic a) :^ b.
Proof.
move=> a b x; rewrite mem_conjg; apply/cyclicP/idP=> [[n]|].
  by move/eqP <-; rewrite conjXg conjgK cyclic_in.
by move/cyclicP => [n Hn]; exists n; rewrite -conjXg (eqP Hn) conjgKV.
Qed.

Lemma orderg_conjg: forall a b, orderg (a ^ b) = orderg a.
Proof.
move=> a b; rewrite /orderg -(card_imset (mem (cyclic a)) (conjg_inj b)).
by apply eq_card => x; rewrite cyclic_conjgs.
Qed.

Lemma orderg_expn1: forall a, a ^+ (orderg a) == 1.
Proof.
move=> a; rewrite cyclicpred_order [a ^+ _]iter_order //; exact: mulg_injl.
Qed.

Lemma orderg_inf : forall a n, (a ^+ n.+1 == 1) -> orderg a <= n.+1.
Proof.
move=> a n H2; apply/idPn; rewrite -ltnNge cyclicpred_order; move/findex_iter.
by rewrite [iter _ _ _](eqP H2) findex0.
Qed.

Lemma expgn_modnorder : forall a x, a ^+ x = a ^+ (x %% orderg a).
Proof.
move=> a x; rewrite {1}(divn_eq x (orderg a)) expgn_add mulnC expgn_mul.
by rewrite (eqP (orderg_expn1 _)) exp1gn mul1g.
Qed.

Lemma cyclic_unit : cyclic 1 = [set 1].
symmetry; apply/setP; apply/subset_cardP.
  by have:= orderg1; rewrite cards1 /orderg=>->.
by apply/subsetP=> x; move/set1P=><-; rewrite cyclicnn.
Qed.

(***********************************************************************)
(*                                                                     *)
(*        Commutativity Properties                                     *)
(*                                                                     *)
(***********************************************************************)


Lemma commute_cyclic_com : forall a b : G,
  commute a b -> {in cyclic a, central (cyclic b)}.
Proof.
move=> a b Hcom x; case/cyclicP=> kx; move/eqP=> <- {x}.
move=> y; case/cyclicP=> ky; move/eqP=> <- {y}.
apply: commuteX; apply: commute_sym; exact: commuteX.
Qed.

Lemma commute_cyclic_normal : forall a b : G,
  commute a b -> cyclic (a * b) \subset 'N(cyclic a).  
Proof.
move=> a b Hcom; apply: subset_trans (sub_centg _).
apply/centralP; apply: commute_cyclic_com.
apply: commute_sym; exact: commuteM.
Qed.

Lemma commute_cyclic_sub : forall a b : G,
  commute a b ->
  coprime (orderg a) (orderg b) ->
  cyclic a \subset cyclic (a * b).
Proof.
move=> a b Hcom; move/eqnP=> Hcop.
apply/subsetP=> x; case/cyclicP=> k; move/eqP=> <-{x}.
case: (egcdnP (orderg a) (orderg_pos b))=> kb ka Heq Hineq.
apply/cyclicP; exists (kb * orderg b * k)%N.
rewrite (expMgn _ Hcom) {2}(mulnC kb) -(mulnA (orderg b)).
rewrite (expgn_mul b (orderg b)) (eqP (orderg_expn1 b)) exp1gn mulg1.
rewrite Heq gcdnC Hcop muln_addl mul1n expgn_add -(mulnC (orderg a)).
by rewrite -(mulnA (orderg a)) expgn_mul (eqP (orderg_expn1 a)) exp1gn mul1g.
Qed.

Lemma cyclic_mul : forall (a b : G),
  commute a b ->
  coprime (orderg a) (orderg b) ->
  cyclic (a * b) = cyclic a * cyclic b.
Proof.
move=> a b Hcom Hcop.
have Hsub: cyclic (a * b) \subset cyclic a * cyclic b.
  apply/subsetP=> x; move/cyclicP=> [k]; move/eqP=> <-.
  by rewrite expMgn // mem_mulg ?cyclic_in.
apply/eqP; rewrite eqset_sub_card Hsub /= coprime_card_mulG //.
rewrite dvdn_leq ?orderg_pos // gauss_inv //=.
by rewrite {2}Hcom !group_dvdn // commute_cyclic_sub // coprime_sym.
Qed.

(***********************************************************************)
(*                                                                     *)
(*        Bijection with Zp                                            *)
(*                                                                     *)
(***********************************************************************)

Lemma decomp_irr : forall a b
  (x y : {m : nat | (m < orderg a) && (a ^+ m == b)}), x = y.
Proof.
move=> a b; case=> [x Hx]; case=> [y Hy].
apply: val_inj=>//=; move/andP: Hy=> [Hy1 Hyeq]; move/andP: Hx=> [Hx1].
move/eqP: Hyeq=><-; move: x y Hx1 Hy1; elim=>[|n IHn]; case=>[|y] Hn Hy //=.
- by rewrite expgS eq_sym; move/orderg_inf; rewrite leqNgt Hy.
- by rewrite expgS; move/orderg_inf; rewrite leqNgt Hn.
move/eqP; move/mulg_injl; move/eqP.
by move/(IHn y (ltn_trans (ltnSn n) Hn) (ltn_trans (ltnSn y) Hy))=>->.
Qed.

Lemma decomp_order_unicity :  forall a x (Hx: x < orderg a) x0,
  (x0 < orderg a) && (a ^+ x0 == a ^+ x) -> x = x0.
Proof.
move=> a x Hx //=.
move: (eq_refl (a ^+ x)); move/(conj Hx); move/andP=> H.
pose P:= (fun x0 => (x0 < orderg a) && (a ^+ x0 == a ^+ x)).
have:= (decomp_irr (exist P x H))=> HH; move=> x0 Hx0.
by move: (HH (exist P _ Hx0)); case.
Qed.

Fixpoint ctzl (a b:G) (k:nat): nat :=
  if k is n.+1 then
    if b == (a ^+ (orderg a - k))
      then (orderg a - k)
      else (ctzl a b n)
    else 0.

Lemma ltn_subSn : forall m n, 0 < m -> m - n.+1 < m.
Proof.
elim=> [|m IH] n; first by rewrite ltn0.
rewrite subSS.
case e1:(0< m); last by move/negbT: e1; rewrite lt0n negbK; move/eqP=>-> //=.
case e2: (0 < m - n); last by move/negbT: e2; rewrite lt0n negbK; move/eqP=>->.
move: (IH n (idP e1)); rewrite -(ltn_add2r 1) (addn1 m) -(addn1 n) -subn_sub.
by rewrite subn1 addn1 prednK // (idP e2).
Qed.

Lemma ctzl_pos : forall k a b, (ctzl a b k) < (orderg a).
Proof.
elim=> //=[n IH] a b; case (b == a ^+ (orderg a - n.+1)); last by apply IH.
rewrite ltn_neqAle leq_subr andbT neq_ltn; apply/orP; left.
elim: (orderg a) (orderg_pos a)=>[|n0 IH0 Hineq]; first by rewrite ltn0.
exact: ltn_subSn.
Qed.

Lemma ctzl_repr : forall k a b (H: b \in cyclic a),
 (orderg a) - val (cyclic_decomp H) <= k ->  a ^+ (ctzl a b k) == b.
Proof.
elim => [|n IH] a b Hcyc; case e:(cyclic_decomp Hcyc)=> //=[m H].
  by move/andP: (H)=>[H1]; rewrite leqn0 eqn_sub0 leqNgt H1.
case g:(b == a ^+ (orderg a - n.+1)); first by rewrite (eqP (idP g)).
rewrite leq_eqVlt; case f: (orderg a - m ==n.+1);
last by rewrite orFb=> Hineq; move: (IH a b Hcyc); rewrite e; move/(_ Hineq).
case/negP: g; move/andP: (H) => [H1].
move: (@subnK m (orderg a)); rewrite leq_eqVlt H1 orbT (eqP (idP f)).
by move/(_ is_true_true)=><-; rewrite addnK eq_sym.
Qed.

Definition cyclic_to_zp_loc (a:G) (b:G): nat := ctzl a b (orderg a).

Lemma cyclic_to_zp_ord : forall a b, (cyclic_to_zp_loc a b < (orderg a)).
Proof. move=>a; exact: ctzl_pos. Qed.

Lemma cyclic_to_zp_corr : forall a b,
  b \in cyclic a -> a ^+ (cyclic_to_zp_loc a b) == b.
Proof.
move=> a b Hcyc; rewrite /cyclic_to_zp_loc.
apply: (@ctzl_repr (orderg a) _ _ Hcyc ); apply:leq_subr.
Qed.

Lemma cyclic_to_zp_id : forall a n,
  cyclic_to_zp_loc a (a ^+ n) = n %% (orderg a).
Proof.
move=> a n; move: (cyclic_to_zp_corr (cyclic_in a n)).
rewrite {2}(expgn_modnorder a n); move/(conj (cyclic_to_zp_ord a (a ^+ n))).
move/andP; move/decomp_order_unicity; rewrite ltn_mod (orderg_pos a).
by move/(_ is_true_true); symmetry.
Qed.

Lemma cyclic_to_zp_decomp : forall a b (H: b \in cyclic a),
  cyclic_to_zp_loc a b = val (cyclic_decomp H).
Proof.
move=> a b Hcyc; move: (cyclic_to_zp_ord a b) (cyclic_to_zp_corr Hcyc)=> Hord1.
case: (cyclic_decomp Hcyc)=> [m Hm]; move/andP: (Hm)=>[Hord2].
move/eqP=>Hcor2 /=; rewrite -{2}Hcor2; move/(conj Hord1); move/andP.
by move/(decomp_order_unicity Hord2); symmetry.
Qed.

Definition cyclic_to_zp (a : G) : G -> I_(orderg a) :=
  fun x => Ordinal (cyclic_to_zp_ord a x).

Definition zp_to_cyclic (a : G) (n : I_(orderg a)) : FinGroup.sort G :=
  a ^+ n.

Lemma zp_morph (a : G) : morphic (cyclic a) (cyclic_to_zp a).
Proof.
move=>a; apply/morphP=> x y Hx Hy.
move: (cyclic_to_zp_corr Hx) (cyclic_to_zp_corr Hy); move/eqP=> Hcorx.
move/eqP=> Hcory; rewrite -{1}Hcorx -{1}Hcory -expgn_add.
by apply: val_inj; rewrite /= cyclic_to_zp_id.
Qed.

Lemma zp_inj (a:G) : injm (cyclic_to_zp a) (cyclic a).
Proof.
move=> a; apply/(injmorphicP (zp_morph a))=> x y /= Hx Hy Heq.
move:(cyclic_to_zp_corr Hx) (cyclic_to_zp_corr Hy); move/eqP=><-; move/eqP=><-.
congr expgn.
replace (cyclic_to_zp_loc a x) with (val (cyclic_to_zp a x)); last by trivial.
replace (cyclic_to_zp_loc a y) with (val (cyclic_to_zp a y)); last by trivial.
by rewrite Heq.
Qed.

Lemma zp_isom (a:G) : isom (cyclic_to_zp a) (cyclic a)
  (set_of I_(orderg a)).
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

Lemma orderg_dvd: forall a n, (orderg a %| n) = (a ^+ n == 1).
Proof.
move=> a n; rewrite expgn_modnorder /dvdn; apply/idP/idP.
  by move/eqP=>->; rewrite expg0.
rewrite -(expg0 a); move : (orderg_pos a); rewrite -(ltn_mod n)=>H.
by move/(conj H); move/andP; move/(decomp_order_unicity (orderg_pos a))=><-.
Qed.

Lemma orderg_dvd_g : forall (H : group G) a, a \in H -> orderg a %| #|H|.
Proof.
move => H a Ha.
have sCaH: cyclic a \subset H.
  by apply/subsetP=> x; move/cyclicP=> [n Dx]; rewrite -(eqP Dx) groupX.
by rewrite -(LaGrange sCaH) dvdn_mulr.
Qed.

Lemma orderg_gexp_dvd: forall a n, orderg (a ^+ n) %| orderg a.
Proof.
move=> a n; rewrite orderg_dvd -expgn_mul mulnC expgn_mul.
by rewrite (eqP (orderg_expn1 a)) exp1gn.
Qed.

Lemma orderg_gcd: forall a n, 0 < n ->
  orderg (a ^+ n) = orderg a %/ gcdn (orderg a) n.
Proof.
move => a n H.
apply/eqP; rewrite eqn_dvd; apply/andP; split.
  rewrite orderg_dvd -expgn_mul -gcdn_divnC //.
  by rewrite expgn_mul (eqP (orderg_expn1 a)) exp1gn.
suff : (orderg a %| orderg (a ^+ n) * gcdn (orderg a) n)%N.
  move: (dvdn_gcdl (orderg a) n) (divn_eq (orderg a) (gcdn (orderg a) n)).
  rewrite {1}/dvdn; move/eqP=>H1; rewrite {1}H1 addn0=>{H1} H1.
  by rewrite {1}H1 dvdn_pmul2r // ltn_0gcd H orbT.
rewrite orderg_dvd mulnC expgn_mul -[a ^+ _]mulg1.
case : (egcdnP (orderg a) H)=> z2 z1 H1 H2.
rewrite -{1}(@exp1gn _ z1) -{1}(eqP (orderg_expn1 a)) -expgn_mul.
rewrite mulnC -expgn_add addnC gcdnC -H1 -expgn_mul -mulnA mulnC.
by rewrite 2!expgn_mul (eqP (orderg_expn1 _)) exp1gn.
Qed.

Lemma orderg_mul : forall a b : G,
  commute a b -> coprime (orderg a) (orderg b) ->
  orderg (a * b) = (orderg a * orderg b)%N.
Proof. 
by move=> a b Hcom Hcop; rewrite /orderg cyclic_mul ?coprime_card_mulG.
Qed.

(***********************************************************************)
(*                                                                     *)
(*        Generator                                                    *)
(*                                                                     *)
(***********************************************************************)

Definition generator (H : {set G}) a :=
  (cyclic a \subset H) && (H \subset cyclic a).

Lemma generator_cyclic: forall a, generator (cyclic a) a.
Proof. by move => a; apply/subset_eqP. Qed.

Lemma cyclic_generator : forall a x, generator (cyclic a) x -> x \in cyclic a.
Proof. by move=> a x; move/subset_eqP=><-; apply: cyclicnn. Qed.

Lemma generator_orderg: forall a b,
  generator (cyclic a) b -> orderg a = orderg b.
Proof.
move => a b; case/andP => H1 H2.
apply: eq_card => x; apply/idP/idP => H3.
  by apply: (subsetP H2).
by apply: (subsetP H1).
Qed.

Lemma cyclic_subset: forall a n, cyclic (a ^+ n) \subset cyclic a.
Proof.
move => a n; apply/subsetP => x.
move/cyclicP => [n1 Hn1].
apply/cyclicP; exists (muln n n1).
by rewrite -(eqP Hn1) expgn_mul eq_refl.
Qed.

Lemma cyclicV: forall a, cyclic a = cyclic a^-1.
Proof.
move=> a; apply/setP=> x; apply/idP/idP; move/cyclicP => [n1 Hn1].
  by apply: groupVl; apply/cyclicP; exists n1; rewrite expVgn (eqP Hn1).
by apply: groupVl; apply/cyclicP; exists n1; rewrite -(inv_eq invgK) -expVgn.
Qed.

End Cyclic.

Section CyclicSubGroup.

Variable elt : finGroupType.

(*  G. 1.3.1 (i) *)

Lemma cyclic_sub_group : forall (a : elt) m, m %| (orderg a) ->
  [set H : {group elt} | (H \subset cyclic a) && (#|H| == m)]
     = [set {cyclic (a ^+ (orderg a %/ m)) as group _}].
Proof.
move=> a m Hdiv.
have Hpos: (0 < m) by apply (ltn_0dvd (orderg_pos a) Hdiv).
have Hcardm: #|cyclic (a ^+ (orderg a %/ m))| == m.
  have Hdivpos: (0 < (orderg a %/ m)) by
    rewrite -(ltn_pmul2r Hpos) mul0n (divnK Hdiv) orderg_pos.
  rewrite [card ( _)](orderg_gcd _ Hdivpos).
  rewrite {2}(divn_eq (orderg a) m) mulnC; move:{+}Hdiv; rewrite /dvdn.
  move/eqP=>->; rewrite gcdnC gcdn_addl_mul gcdn0.
  rewrite -{2}(@divn_mulr m ((orderg a) %/ m)) ?Hdivpos //=.
  by rewrite (divnK Hdiv) eqxx.
apply/setP; apply/subset_eqP; apply/andP; split; last first.
  rewrite sub1set inE //=; apply/andP.
  split; [exact: cyclic_subset|by rewrite Hcardm].
apply/subsetP=>x; rewrite !inE; move/andP=> [Hsub Hcard]; apply/eqP.
apply: val_inj=> /=; apply/setP.
apply/subset_cardP; first by rewrite (eqP Hcard) (eqP Hcardm).
apply/subsetP=> i Hi; move: (orderg_dvd_g Hi); rewrite orderg_dvd.
move/subsetP: Hsub; move/(_ i Hi).
move/cyclicP=> [k Hk]; move/eqP:Hk=><-; rewrite -expgn_mul.
rewrite -orderg_dvd; move/dvdnP=>[k0 Hdivk0]; apply/cyclicP.
exists k0; rewrite -expgn_mul; apply/eqP; congr (_ ^+ _)%g.
rewrite (divn_eq (orderg a) m) (eqnP Hdiv) addn0 !mulnA in Hdivk0.
move/eqP: Hdivk0; rewrite (eqP Hcard) eqn_mul2r; rewrite lt0n in Hpos.
by move/negbET: Hpos=>->; rewrite orFb mulnC; move/eqP=>->.
Qed.

Lemma cyclic_subgroup_char : forall a (H : {group elt}),
  H \subset (cyclic a) ->
  characteristic (cyclic a) H.
Proof.
move=> a H Hsub.
case e: #|H| => [|k]; first by move: (pos_card_group H); rewrite e //.
apply: (lone_subgroup_char _ e)=>// J HsubJ HcardJ.
move/setP: (cyclic_sub_group (group_dvdn Hsub)); move/subset_eqP.
move/andP=>[Hcyc _]; move/subsetP: Hcyc=> Hcyc; move: (Hcyc H).
rewrite inE eqxx /= Hsub andTb; move/(_ is_true_true); move/set1P=>->.
move: (Hcyc J); rewrite inE HcardJ HsubJ -e andTb eq_refl.
by move/(_ is_true_true); move/set1P=>->.
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
move/trivm_is_cst=>Htriv; move: (Htriv x)=>/=->.
by apply/setP=>y; apply/imsetP/cyclicP=>[[n _ ->]|[n]];
[exists 1%N| move/eqP=><-; exists x; rewrite ?cyclicnn //]; rewrite exp1gn Htriv.
Qed.

End MorphicImage.

(***********************************************************************)
(*                                                                     *)
(*       Automorphisms of cyclic groups                                *)
(*                                                                     *)
(***********************************************************************)

Section CyclicAutomorphism.

Variables G G' : finGroupType.

Variable f : perm G.

Lemma cyclic_aut_stable : forall x,
  Aut (cyclic x) f -> f @: cyclic x = cyclic (f x).
Proof.
move=> x HAut; move:{+}HAut; move/andP=> [Hperm Hmorph].
apply: (cyclic_morph_stable Hmorph).
Qed.

Lemma order_aut_stable : forall x, Aut (cyclic x) f ->
  orderg x  = orderg (f x).
Proof.
move=> x Haut; rewrite /orderg; apply eq_card.
move: (isom_morph_of_aut Haut)=>//=; rewrite /isom.
move/andP=> [Hmorph _]; move/eqP: Hmorph=><-.
rewrite (@dfequal_imset _ _ (morph_of_aut f (cyclic x)) f).
  by apply/setP; apply: cyclic_aut_stable.
exact: (morph_of_aut_ondom Haut).
Qed.

(* From the multiplicative group to automorphisms*)

Lemma cyclic_gexpn_clos : forall (x: G) k, (coprime (orderg x) k) ->
  (fun a => a ^+ k)%g @: (cyclic x) \subset (cyclic x).
Proof.
move=> x k Hcop; apply/subsetP=> a.
move/imsetP=> [y]; move/cyclicP=> [n]; move/eqP=><- ->.
by apply/cyclicP; exists (n * k)%N; rewrite -expgn_mul.
Qed.

Lemma cyclic_dcan_gexpn : forall (a : G) k, (coprime (orderg a) k) ->
  exists g, {in (cyclic a), cancel (fun z => z ^+ k)%g g}.
Proof.
move=> a k; case Hpos: (0 < k) => Hcop; last first.
  move: Hcop; move/idPn: Hpos; rewrite -eqn0Ngt; move/eqP=>->.
  rewrite coprime_sym /coprime gcd0n /orderg => Hcard.
  have Heq: (1%g : {set G}) =i cyclic a.
    apply/subset_cardP; last by rewrite sub1set; apply:group1.
    by move/eqP:Hcard=>->; rewrite cardsE card1.
  by exists (@id G) => x; rewrite expg0 //= -(Heq x); move/set1P=><-.
case: (bezoutl (orderg a) Hpos); move=> x xinf.
rewrite coprime_sym /coprime in Hcop; move/eqP: Hcop=>->; move/dvdnP=>[k0 Hk0].
exists (fun z:G => z ^+ k0)%g; move=> x0 Hx0 //=.
rewrite -expgn_mul mulnC -Hk0 expgn_add mulnC; move/cyclicP: Hx0 => [i].
move/eqP=><-; rewrite expg1.
by rewrite -!expgn_mul mulnCA expgn_mul (eqP (orderg_expn1 a)) exp1gn mulg1.
Qed.

Lemma inj_gexpn : forall a k,
  coprime (orderg a) k ->
  {in (cyclic a) &, injective (fun x : G => x ^+ k)%g}.
Proof.
move=> k a Hcop; move: (cyclic_dcan_gexpn Hcop)=>[g dcan].
by apply (in_can_inj dcan).
Qed.

Lemma gexpn_automorphic : forall a k (D:coprime (orderg a) k),
  Aut (cyclic a) (perm_of_restriction (cyclic_gexpn_clos D) (inj_gexpn D)).
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
  Aut (cyclic x) f -> coprime (orderg x) (Ordinal (cyclic_to_zp_ord x (f x))).
Proof.
move=> x Haut; rewrite coprime_sym.
case e: (trivm_(cyclic x) f)%g.
  move/forallP: e=> e; move: (e x); rewrite cyclicnn /=; move/eqP .
  move=> Hfx; move:{+}Haut {+}Hfx; move/andP=>[_]; move/morphic1=><-.
  move/perm_inj; rewrite Hfx=>->.
  by rewrite /cyclic_to_zp_loc /ctzl !orderg1 subnn exp1gn eqxx coprimen1.
have Hfx: f x \in cyclic x.
  move/andP: Haut=>[Hperm _].
  by rewrite (perm_closed x Hperm) cyclicnn.
move: (cyclic_to_zp_corr Hfx);set n:= (cyclic_to_zp_loc x (f x)) =>Hn.
have: (0 < n) || (x == 1)%g.
  case x1: (x == 1)%g; first by rewrite orbT.
  rewrite orbF ltnNge leqn0; apply/negP=> //= H; move:Hn; move/eqP: H=>->.
  rewrite expg0 eq_sym -(morph_of_aut_ondom Haut (cyclicnn x)).
  move/eqP; move/kerMP; rewrite (dom_morph_of_aut Haut (negbT e)) ?cyclicnn.
  move/(_ is_true_true); move/setP: (ker_injm (morph_of_aut_injm Haut)).
  move/(_ x); rewrite inE cyclicnn andbT=>->; move/set1P; move/eqP.
  by rewrite x1.
move/orP=>[Hpos|H1] /=; last by move/eqP:H1=>->; rewrite orderg1; apply:coprimen1.
have: (gcdn (orderg x) n <= 1).
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
move=> x Haut.
 case e: (trivm_(cyclic x) f)%g => /=.
  move/forallP: e => e z Hcyc; move: (e z); rewrite Hcyc /=; move/eqP=> Hfz.
  move: (cyclicnn x); rewrite -(perm_closed _ (proj1 (andP Haut)))=> Hfx.
  rewrite Hfz; move:{+}Haut {+}Hfz; move/andP=>[_]; move/morphic1=>Hf1.
  by rewrite -{1}Hf1; move/perm_inj=>->; rewrite exp1gn.
move=> z; move/cyclicP=> [n Hn]; move/eqP: Hn=><-.
rewrite -(morph_of_aut_ondom Haut (cyclic_in x n)) morphX.
  have:= (morph_of_aut_ondom Haut (cyclicnn x)); rewrite /==>->.
  move: (cyclicnn x); rewrite -(perm_closed _ (proj1 (andP Haut))).
  by move/cyclic_to_zp_corr; move/eqP; rewrite -expgn_mul mulnC expgn_mul=>->.
by rewrite (dom_morph_of_aut Haut (negbT e)) (cyclicnn x).
Qed.

(* the unit for the multiplicative group *)

Definition zp1 (n:pos_nat): ordinal_finType n.
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

Definition cyclic_to_fp_loc (a:G) : perm G -> I_(orderg a) :=
  fun f => if (coprime (orderg a) (cyclic_to_zp_loc a (f a)))
    then
      Ordinal (cyclic_to_zp_ord a (f a))
    else 
      (zp1 {orderg a as pos_nat}).

Lemma cyclic_to_fp_corr : forall a, coprime (orderg a) (cyclic_to_fp_loc a f).
Proof.
move=> a; rewrite /cyclic_to_fp_loc.
case e: (coprime (orderg (G:=G) a) (cyclic_to_zp_loc (G:=G) a (f a)));
[apply: (idP e)|apply: coprime_zp1].
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

Definition cyclic_to_fp (a:G) : perm G -> fp_mul (orderg a) :=
  fun f => exist (fun x:fzp (orderg a) => coprime (orderg a) x) 
                 _
                 (cyclic_to_fp_corr f a).

Definition fp_to_cyclic (x:G) :=
  fun (D:fp_mul (orderg x)) =>
    (perm_of_restriction (cyclic_gexpn_clos (valP D)) (inj_gexpn (valP D))).

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
move: (cyclic_in a (cyclic_to_zp_loc (G:=G) a (x a))).
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
move/cyclic_morph_stable=> Hcyc; apply/subset_eqP/subset_eqP=> H1.
  by rewrite -Hcyc; move/setP: H1 => ->.
move: {+}H1; rewrite -Hcyc; move=> H2.
apply/subset_cardP; last exact: (cyclic_h Ha).
move/(injmorphicP Hmorph): Hinj => Hinj; move/card_dimset: (Hinj) => <-.
move/card_dimset: (subin2 (subsetP (cyclic_h Ha)) Hinj) <-.
by move/setP: H2 => ->.
Qed.

End GenAut.

Section ZpAut.

Variable G : finGroupType.
Variable a:G.

Lemma expgn_muln : forall (k:nat) (n:pos_nat) (p:nat) (H: p < n),
  (Ordinal H ^+ k)%g = Ordinal (ltn_pmod (p * k) (valP n)).
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
  move/eqP:Hcop=>Hn; rewrite {3}Hn !ltnS !leqn0; move/eqP=>H0; apply/eqP.
  by apply: val_inj=>/=; rewrite addn0 /= H0 modn_small.
case: (egcdnP n (ltn0Sn k))=> kk kn Heq Hineq; exists (kk * x0)%N =>/=.
rewrite expgn_muln; apply/eqP; apply: val_inj=>/=.
rewrite mulnA (mulnC (k.+1)) Heq muln_addl -(mulnA kn) (mulnC n) mulnA.
move: Hcop; rewrite modn_addl_mul /coprime; move/eqP=>->.
by rewrite mul1n modn_small.
Qed.

Lemma zp_ord : forall (n : pos_nat) (i : zp_group n),
  i = Ordinal (valP (i : I_(n))).
Proof. by move=> n i; apply: val_inj. Qed.

Lemma zp_gen : forall (n : pos_nat) i,
  generator (set_of I_(n)) i = coprime (i : I_(n)) n.
Proof.
move=> n i; apply/idP/idP; last first.
  move=>Hcop; apply/subset_eqP; apply/setP; symmetry.
  apply:zp_group_cyclic=>/=; by [apply: (valP (i : I_(n))) | apply: Hcop].
move/subset_eqP=>Hcop.
case e: (0 < (i : I_(n))).
  apply:modn_coprime; first exact: (idP e).
  have H1: (1 < n) by apply: leq_ltn_trans (valP (i : I_(n))); apply:(idP e).
  have: (I_(n) (Ordinal H1)) by trivial.
  rewrite -inE -Hcop; move/cyclicP=>[n1]; move/eqP.
  rewrite (zp_ord i) (expgn_muln).
  exists n1; replace 1%N with (val (@Ordinal n 1 H1)); last by trivial.
  by rewrite -elimTF /=.
move/negbT:e; rewrite lt0n negbK; move/eqP=>Hi.
move: (eq_card Hcop); rewrite cardsT card_zp Hi /coprime gcd0n.
replace (@cyclic (zp_group n) i) with (@cyclic (zp_group n) 1).
  by move: orderg1; rewrite /orderg=>-> <-.
by congr cyclic; rewrite /unitg /= /zp0; apply: val_inj.
Qed.

Lemma generator_coprime : forall m,
  coprime m (orderg a) = generator (cyclic a) (a ^+ m).
Proof.
move=> m; rewrite (generator_bij (zp_inj a) (zp_morph a)); last exact: cyclic_in.
rewrite coprime_sym /coprime gcdnE (negbET (lt0n_neq0 (orderg_pos a))).
move/andP:(zp_isom a)=> [H _]; move/eqP:H =>->.
have Hmod: (m %% orderg a < orderg a) by rewrite ltn_mod (orderg_pos a).
have:= (@zp_gen {orderg a as pos_nat} (Ordinal Hmod)); rewrite /= /coprime =><-.
congr generator; rewrite /cyclic_to_zp;  apply: val_inj=>/=.
by rewrite cyclic_to_zp_id.
Qed.


Lemma phi_gen : phi (orderg a) = #|generator (cyclic a) : pred _|.
Proof.
rewrite /phi /=; set n := orderg a.
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
move/cyclicP: e=>[n Hn]; move/eqP: Hn=><-.
rewrite -!expgn_mul (Heq_kf _ (cyclic_in _ (n * kg))).
rewrite  (Heq_kg _ (cyclic_in _ (n * kf))) -!expgn_mul -mulnA.
by rewrite [(kf * kg) %N]mulnC mulnA.
Qed.

End CyclicAutomorphism_Abelian.


Unset Implicit Arguments. 
