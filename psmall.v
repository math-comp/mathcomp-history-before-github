Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq paths div.
Require Import choice fintype finfun bigops ssralg finset prime binomial.
Require Import groups zmodp morphisms automorphism normal perm action gprod.
Require Import commutators cyclic center pgroups sylow nilpotent maximal hall.
Require Import transfer.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(*
Local Open Scope ring_scope.
*)

Lemma binn1 : forall n, bin n 1 = n.
Proof.
elim=> [|n ih]; by [|rewrite binS bin0 ih addn1].
Qed.

Lemma binn2 : forall n, bin n 2 = (n * n.-1)./2.
Proof.
case; first by rewrite muln0 -divn2 div0n.
case=>[| n]; first by rewrite mul1n -subn1 subnn -divn2 div0n.
have g1 : 1 < n.+2 by []; move: (bin_fact g1) => {g1}.
rewrite -{2}add2n addnC addnK !factS !fact0 !muln1 !mulnA.
move/eqP; rewrite eqn_mul2r; case/orP; move/eqP.
  by move=> facteq; move: (fact_gt0 n); rewrite facteq //=.
move/eqP; rewrite -eqn_div //=; first by move/eqP; rewrite divn2.
rewrite dvdn2 odd_mul -addn2 -addn1 -(addn1 n) !odd_add //=.
by case: (odd n); rewrite //=.
Qed.

(* another proof 
Lemma binn2 : forall n, bin n 2 = (n * n.-1)./2.
Proof.
case; first by rewrite muln0 -divn2 div0n.
elim; first by rewrite mul1n -subn1 subnn -divn2 div0n.
move=> n ih; rewrite binS ih binn1 -[n.+1.-1]/n -[n.+2.-1]/n.+1.
have calc : (n.+2 * n.+1 = n.+1 * n + n.+1.*2)%N.
  rewrite -addn2 -(addn1 n) -muln2 !muln_addl !muln_addr !muln1 !mul1n.
  by rewrite (mulnC 2).
by move: calc => ->; rewrite half_add odd_mul andNb andFb add0n //= doubleK.
Qed.
*)

Lemma dvdn_fact : forall m, 0 < m -> forall n, m <= n -> (m %| fact n).
Proof.
move=> m mpos; elim=>[|n ih]; first by case: m mpos.
rewrite leq_eqVlt; case/orP; first by move/eqP=> ->; rewrite factS dvdn_mulr.
by rewrite ltnS=> mlen; rewrite factS dvdn_mull // ih.
Qed.

Lemma prime_dvd_fact : forall p n, prime p -> (p %| fact n) = (p <= n).
Proof.
move=> p n primep; apply/idP/idP; last exact: (dvdn_fact (prime_gt0 _)).
elim: n => [|n ih].
  by rewrite fact0 dvdn1; move/eqP=>p1; move: p1 primep => ->; case/primeP.
rewrite factS euclid //; case/orP; first by exact: dvdn_leq. 
by move/ih; move/leq_trans; apply.
Qed.

Lemma prime_dvd_bin : forall p, prime p -> 
  forall n, 0 < n -> n < p -> p %| bin p n.
Proof.
move=> p primep n ng0 nlp.
have pnlp : p - n < p by rewrite -{2}(subn0 p) ltn_sub2l // prime_gt0.
have pdvd : p %| (fact p) by rewrite dvdn_fact // prime_gt0.
move: pdvd; rewrite -(bin_fact (ltnW nlp)).
by rewrite !euclid // !prime_dvd_fact // leqNgt nlp //= leqNgt pnlp //= orbF.
Qed.

Import GroupScope.

(*
Import GRing.Theory FiniteModule.
*)

Section pGroupsSmallRank.

Variables (gT : finGroupType) (R : {group gT}) (p : nat).
Hypotheses (primep : prime p) (oddp : odd p) (pgroupR : p.-group R).

(* Note: I still have to clean up the proof below. Perhaps the following lemma
   will help. *)
Lemma commute_lcommute : forall (x : gT) y, commute x y -> 
  forall z, z * x * y = z * y * x.
Proof.
by move=> x y commxy z; rewrite -!mulgA commxy.
Qed.

Lemma four_dot_three : (nil_class R <= 2 \/ (nil_class R <= 3 /\ p > 3)) ->
  (exponent 'Ohm_1(R) %| p /\ (R^`(1) \subset 'Ohm_1(R) -> 
    morphic R (fun x => x ^+ p))).
Proof.
move=> hyp.
have classle3 : nil_class R <= 3.
  case: (hyp); by [case | move/leq_trans; apply].
have RRRsub: [~: R, R, R] \subset 'Z(R) by rewrite -nil_class3.
have RRRcom: forall x y z w, x \in R -> y \in R -> z \in R -> w \in R ->
  commute [~ x, y, z] w.
  move=> x y z w Rx Ry Rz Rw; apply: commute_sym; apply: (centerC Rw). 
  by rewrite (subsetP RRRsub) // !mem_commg //.
have eq42: forall u w n, u \in R -> w \in R -> 
  [~ u ^+ n, w] = [~ u, w] ^+ n * [~ u, w, u] ^+ (n * n.-1)./2.
  move=> u w; elim=> [|n ih] Ru Rw; first by rewrite !expg0 comm1g mulg1.
  rewrite expgS commMgR commgX; last first. 
    by apply: (centerC Ru); rewrite (subsetP RRRsub) ?mem_commg //.
  rewrite ih //; rewrite mulgA -(mulgA [~ _ , _]).
  rewrite (commute_sym (commuteX n _)); last first.
    by apply: commute_sym; apply RRRcom; rewrite // groupX ?groupR //.
  rewrite mulgA -expgS -mulgA -expgn_add.
  by rewrite -!triangular_sum big_nat_recr addnC.
pose f n := bin n 3; pose g n := 2 * bin n 3 + bin n 2.
have fS : forall n, f (n.+1) = bin n 2 + f n.
  by move=> n; rewrite /f binS //= addnC. 
have gS : forall n, g (n.+1) = 2 * bin n 2 + bin n 1 + g n.
  move=> n. rewrite /g !binS !muln_addr (addnC (2 * _)%N).
  by rewrite (addnC (bin n 2)) 2!addnA (addnAC (2 * _)%N) //=.
have pdivbin2: p %| bin p 2.
  apply: prime_dvd_bin; rewrite //= ltn_neqAle prime_gt1 // andbT.
  by apply/eqP=> peq; move: peq oddp => <-.
have pdivfp : p > 3 -> p %| f p.
  by apply: prime_dvd_bin; rewrite  //.
have pdivgp : p > 3 -> p %| g p.
  by move=> pg3; rewrite dvdn_add // dvdn_mull // pdivfp.
have nilclass2 : nil_class R <= 2 -> forall u v w, u \in R -> v \in R -> 
  w \in R -> [~ u, v, w] = 1.
  move=> R1sub u v w Ru Rv Rw. 
  have RRsub: [~: R, R] \subset 'Z(R) by rewrite -nil_class2.
  have uvcomm: forall z, z \in R -> commute z [~ u, v].
    move=> z Rz; apply: (centerC Rz). 
    by rewrite (subsetP RRsub) // mem_commg.
  by rewrite commgEr conjgE uvcomm ?groupV // mulKg mulVg.
have {fS gS} eq44 : forall u v, u \in R -> v \in R -> forall n,
  (u * v) ^+ n = u ^+ n * v ^+ n * [~ v, u] ^+ bin n 2 * 
  [~v, u, u] ^+ f n * [~ v, u, v] ^+ g n.
  move=> u v Ru Rv; elim=> [| n ih]; first by rewrite !expg0 !mulg1.
  rewrite expgSr ih -!mulgA.
  rewrite (commute_sym (commuteX (g n) _)); last first.
    apply: commute_sym; apply: RRRcom; rewrite // groupM //.
  rewrite (mulgA (_ ^+ f n)) (commute_sym (commuteX (f n) _)); last first.
    apply: commute_sym; apply: RRRcom; rewrite // groupM //.
  rewrite !mulgA -(mulgA  _ u) -(mulgA _ _ (u * v)) (commgC _ (u * v)).
  rewrite commXg; last first.
    apply: commute_sym; apply: RRRcom; rewrite // ?groupR ?groupM //.
  rewrite commgMR {6}/commg /conjg (RRRcom v u u v) // mulKg mulVg mulg1.
  rewrite expMgn; last by apply: RRRcom; rewrite ?groupR. 
  rewrite !mulgA -(mulgA _ _ u) (commgC _ u) eq42 // !mulgA -expgSr.
  rewrite -(mulgA _ _ v) (commute_sym (commuteX (_./2) _)); last first.
    by rewrite /commute RRRcom.
  rewrite !mulgA -(mulgA _ _ v) (commgC _ v).
  rewrite 2!mulgA -(mulgA _ _ v) -(expgSr v).
  rewrite commXg; last by rewrite /commute RRRcom ?groupR //.
  rewrite -(mulgA _ _ (_ ^+ _./2)) -expgn_add.
  rewrite -(mulgA _ _ (_ ^+ f n)) -expgn_add -fS.
  rewrite -(mulgA _ _ (_ ^+ f n.+1)). 
  rewrite (commuteX (f n.+1)); last first.
    by rewrite /commute RRRcom // groupX // !groupR //.
  rewrite mulgA -mulgA -expgn_add. 
  rewrite -!mulgA (commute_sym (commuteX (_ + _) _)); last first.
    by rewrite /commute RRRcom ?(groupX, groupR, groupM).
  rewrite !mulgA -(mulgA _ _ (_ ^+ bin n 2)) -expgn_add.
  rewrite -mulgA -expgn_add gS -binn2 binS binn1 addnC. 
  rewrite (addnC (_ + _) (_ + _)). rewrite addnCA 2!addnA.
  by rewrite -[(2 * _)%N]/((1 + 1) * _)%N muln_addl mul1n.
have expOhm : exponent 'Ohm_1(R) %| p.
  move: {-2 4}R (ltnSn #|R|) (subxx R).
  elim: (#|_|.+1) => [| n ih] R'; first by rewrite ltn0.
  move=> R'lt R'subR; rewrite (OhmE 1 (pgroupS R'subR pgroupR)). 
  apply/exponentP; rewrite /= gen_set_id expn1 => [x|].
    by rewrite inE; case/andP=> _; move/eqP. 
  apply/group_setP; rewrite !inE; split; first by rewrite group1 exp1gn eqxx. 
  move=> x y; rewrite !inE; case/andP=> R'x; case/eqP=> xp1; 
  case/andP=> R'y; case/eqP=> yp1.
  rewrite groupM //=; apply/eqP; case genxy: (y \in <[x]>).
    rewrite expMgn; first by rewrite xp1 yp1 mulg1.
    apply: commute_sym; apply/cent1P.
    move: (cycle_abelian x); rewrite abelianE cent_gen cent_set1=> genxsubCx.
    exact: (subsetP genxsubCx).
  have genxsubR' : <[ x ]> \subset R' by rewrite gen_subG sub1set.
  case: (maximal_exists genxsubR').
    move/setP; move/(_ y); rewrite genxy R'y //=.
  case=> S maxS genXsubS.
  have pgroupR' := (pgroupS R'subR pgroupR).
  have cardSR' := (proper_card (maxgroupp maxS)).
  have SsubR' := (proper_sub (maxgroupp maxS)).
  have pgroupS := (pgroupS SsubR' pgroupR').
  move: (leq_ltn_trans cardSR' R'lt); rewrite ltnS=> cardSn.
  move/exponentP: (ih _ cardSn (subset_trans SsubR' R'subR)) => expS.
  have normSR' := (p_maximal_normal pgroupR' maxS).
  have {normSR'} normOR' := normal_norm (char_normal_trans (Ohm_char 1 S) normSR').
  have Ox : x \in 'Ohm_1(S).
    rewrite (OhmE 1 pgroupS) (subsetP (subset_gen _)) // inE expn1 xp1 eqxx andbT.
    by apply: (subsetP genXsubS); exact: cycle_id.
  have Oyx : [~ y,x] \in 'Ohm_1(S).
    by rewrite commgEr groupM // memJ_norm ?groupV // (subsetP normOR') //.
  have Oyxx : [~ y, x, x] \in 'Ohm_1(S) by rewrite groupR //.
  have Oyxy : [~ y, x, y] \in 'Ohm_1(S).
    by rewrite commgEl groupM // ?groupV // memJ_norm // (subsetP normOR').
  rewrite eq44 ?(subsetP R'subR) // xp1 yp1.
  case/dvdnP: (pdivbin2) => k ->.
  rewrite (mulnC k) expgn_mul (expS _ Oyx) exp1gn !mulg1 mul1g //.
  case: (hyp).
    by move=> ncR2; rewrite !(nilclass2 ncR2) ?(subsetP R'subR) // !exp1gn !mulg1.
  case=> _ pg3; case/dvdnP: (pdivfp pg3) => k1 ->.
  rewrite (mulnC k1) expgn_mul (expS _ Oyxx) exp1gn mul1g // => {k1}.
  case/dvdnP: (pdivgp pg3) => k2 ->.
  by rewrite (mulnC k2) expgn_mul (expS _ Oyxy) exp1gn //.
split; first exact: expOhm. 
move=> R1subO.
have commp : forall u v, u \in R -> v \in R -> [~ u, v]^+ p = 1. 
  move=> u v Ru Rv.
  have Ouv : [~ u, v] \in 'Ohm_1(R).
    by apply: (subsetP R1subO); apply: mem_commg.
  by move/exponentP: expOhm; apply.
apply/morphicP=> x y Rx Ry; rewrite eq44 //.
case/dvdnP: (pdivbin2) => k ->.
rewrite (mulnC k) expgn_mul commp // exp1gn mulg1.
case: (hyp).
  by move=> ncR2; rewrite !(nilclass2 ncR2) ?(subsetP R'subR) // !exp1gn !mulg1.
case=> _ pg3; case/dvdnP: (pdivfp pg3) => k1 ->.
rewrite (mulnC k1) expgn_mul commp ?groupR // exp1gn mulg1 => {k1}.
case/dvdnP: (pdivgp pg3) => k2 ->.
by rewrite (mulnC k2) expgn_mul commp ?groupR // exp1gn mulg1.
Qed.

End pGroupsSmallRank.

