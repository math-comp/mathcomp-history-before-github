(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop ssralg poly polydiv orderedalg zmodp polydiv.

Import GRing.Theory.
Import OrderedRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Defensive.

Open Scope ring_scope.

Section PolyRFC.

Variable R : oFieldType.
Hypothesis tvi : (poly_ivt R).

Fixpoint var (s : seq R) :=
  match s with 
    | [::]  => 0%N
    | a::q => match q with
                | [::] => 0%N
                | b::q' => if a * b < 0 then (var q).+1 else var q
              end
  end.

Definition varp (p : seq {poly R}) x := 
  var (map (fun (p : {poly _}) => p.[x]) p).

Fixpoint der_rec (p : {poly R}) n :=
  if n is m.+1 
    then if p == 0 then [::] else p::(der_rec p^`() m)
    else [::].
Definition der (p : {poly R}) := der_rec p (size p).

Fixpoint sremps_rec (p q : {poly R}) n := 
    if n is m.+1 
      then if p == 0 then [::] else p::(sremps_rec q (p %% q) m)
      else [::].
Definition sremps (p q : {poly R}):= 
  if ((size q) < (size p))%N then sremps_rec p q (size p)
  else  sremps_rec q p (size q).+1.

Lemma sremps_recq0 : forall n (p : {poly R}), p != 0 ->
  sremps_rec p 0 n.+1 = [::p].
Proof.
move=> n p //= pn0; rewrite (negPf pn0).
by case:n=> [|n] //=; rewrite eqxx.
Qed.

Lemma sremps_recp0 : forall n (p : {poly R}), sremps_rec 0 p n = [::].
Proof. by case=>[|n] p => //=; rewrite eqxx. Qed.

Lemma last1_neq0 : forall (R : ringType) (s: seq R) (c:R), c != 0 -> 
  (last c s != 0) = (last 1 s != 0).
Proof.
by move=> R'; elim=> [|t s ihs] c cn0 /=; first by rewrite oner_eq0 cn0.
Qed.

Lemma sremps_recP : forall n (p q : {poly R}), ((size q) < (size p))%N ->
  (size p <= n)%N -> sremps_rec p q n = sremps_rec p q (size p).
Proof.
move=> n p.
elim: (size p) {-2 7}p (leqnn (size p)) n 
  => [|sp ihsp] {p} p hp n q /= sqp spn.
  by move: (leq_trans sqp hp).
case: n spn=> [|n] spn /=; first by move: (leq_trans sqp spn); rewrite ltn0.
case p0: (p==0)=> /=; first by move: sqp; rewrite (eqP p0) size_poly0 ltn0.
congr (_::_); case q0: (q == 0); first by rewrite (eqP q0) !sremps_recp0.
apply: ihsp; first by move: (leq_trans sqp hp).
  by rewrite modp_spec// q0.
by move: (leq_trans sqp spn).
Qed.

Lemma sremps_lastn0 : forall p q, last 1 (sremps p q) != 0.
Proof.
move=> p q; rewrite /sremps.
wlog spq: p q/ (size q < size p)%N=> [hpq|]; [|rewrite spq].
  case: ltnP=> spq/=; first by have:= (hpq _ _ spq); rewrite spq.
  case q0: (q == 0)=> /=; first by rewrite oner_eq0.
  rewrite last1_neq0 ?q0//.
  case p0: (p == 0); first by rewrite (eqP p0) sremps_recp0 //= oner_eq0.
  rewrite sremps_recP 1?modp_spec ?p0//.
  by move: (hpq p (q %% p)); rewrite modp_spec ?p0// => ->.
elim: (size p) {-2 5}p (leqnn (size p)) q spq=> [|n ihn] {p} p hp q spq /=.
  by rewrite oner_eq0.
case p0: (p == 0)=> /=; first by rewrite oner_eq0.
rewrite last1_neq0 ?p0//.
case q0: (q == 0); first by rewrite (eqP q0) sremps_recp0 //= oner_eq0.
apply: ihn; first by move: (leq_trans spq hp).
by rewrite modp_spec ?q0//.
Qed.

Definition inf_poly (p : {poly R}) := 2%:R * \sum_(c <- p) `| c / lead_coef p |.

Lemma addr_eq0 : forall (x y : R), 0 <= x -> 0 <= y -> 
  (x + y == 0) = (x == 0) && (y == 0).
Proof. Admitted.

Lemma sumr_ler : forall I r (F1 F2 : I -> R),
  (all (fun i => (F1 i <=  F2 i)) r) ->
  \sum_(i <- r) (F1 i) <= \sum_(i <- r) (F2 i).
Proof. Admitted.

Lemma sumr_ge0 : forall I r (F : I -> R),
  (all (fun i => (0 <=  F i)) r) ->
  0 <= \sum_(i <- r) (F i).
Proof. Admitted.

Lemma sumr_eq0 :  forall I r (F : I -> R), 
  (all (fun i => (F i >= 0)) r) ->
  (\sum_(i <- r) (F i) == 0) =  (all (fun i => (F i == 0)) r).
Proof.
move=> I; elim=> [|a r ihr] //= F arP. 
  by rewrite big_nil eqxx; constructor.
case/andP:arP=> aP rP; rewrite big_cons; apply/idP/idP.
  rewrite addr_eq0 1?sumr_ge0//; case/andP=> Fa0 sFj0.
  by rewrite Fa0/= -ihr.
by case/andP; move/eqP->; rewrite add0r ihr.
Qed.

Lemma sign_inf : forall p x, `|x| >= (inf_poly p) -> 
  \s (p.[x]) = \s ((lead_coef p) * x ^+ (size p).-1).
Admitted.

Lemma inf_poly0 : inf_poly 0 = 0.
Proof. by rewrite /inf_poly seq_poly0 big_nil mulr0. Qed.

Lemma rootp_div : forall p q (x : R), root p x -> ~~root q x -> root (p %/ q) x.
Admitted.

(* to put in polydiv *)
Lemma poly_maxn_root : forall (rs : seq R) (p : {poly R}),
  uniq rs -> (size rs >= size p)%N -> all (root p) rs -> p == 0.
Proof.
move=> rs p; elim: {p} (size p) {-2 3}p (leqnn (size p)) rs
  => [|n ihn] p esp rs up hp rsP.
  by move: esp; rewrite leqn0 size_poly_eq0.
case: rs up hp rsP=> //= r rs. case/andP=> hr hrs; 
rewrite ltnS=> nr; case/andP=> rP rsP.
case p0: (p == 0) => //=.
have sp1: (size p > 1)%N.
  rewrite ltnNge leqn1 size_poly_eq0 p0/=.
  apply/negP; move/size1_is_polyC=> [c [c0 pc]].
  by move: pc rP->; rewrite /root hornerC (negPf c0).
suff: (p %/ ('X - r%:P) == 0).
  rewrite -size_poly_eq0 size_divp -?size_poly_eq0 ?size_XMa//=.
  by rewrite subn_eq0 leqNgt sp1.
apply: (ihn _ _ rs)=> //. 
  by rewrite size_divp -?size_poly_eq0 size_XMa //= ?leq_sub_add.
apply/allP=> x xrs; rewrite rootp_div//; first by move/allP:rsP; apply.
rewrite /root !horner_lin (can2_eq (addrNK _) (addrK _)) add0r.
by apply/eqP=> xr; move: hr; rewrite -xr xrs.
Qed.

(* to put in orderedalg *)
Lemma mulrnI : injective (@GRing.natmul R 1).
Proof.
move=>  m n.
wlog lnm : m n / (n < m)%N=> [wh hxnm|].
   case: (ltngtP n m)=> hmn //; first exact: wh.
   by symmetry; apply: wh=> //.
move/eqP. rewrite -{1}[m](@subnK n) 1?ltnW// mulrn_addr.
rewrite -subr_eq0 -addrA subrr addr0.
case hmn: (m - n)%N; last by rewrite charor.
by move/eqP:hmn; rewrite subn_eq0 leqNgt lnm.
Qed.

(* to put in polyorder, under tvi hypothesis *)
Lemma poly_eq0 : forall p : {poly R}, reflect (forall x, root p x) (p == 0).
Proof.
move=> p; apply: (iffP idP); first by move/eqP=> -> x; rewrite /root hornerC.
move=> pP. 
pose fix test n : seq R := if n is m.+1 then (m%:R)::(test m) else [::].
apply: (@poly_maxn_root (test (size p))); last exact/allP.
  elim: (size p)=> //= n ->; rewrite andbT.
  elim: n {2 3}n (leqnn n)=> [|n ihn] m //= ltnm.
  rewrite inE negb_or ihn 1?ltnW// andbT (inj_eq mulrnI).
  by move:ltnm; apply: contraL; move/eqP->; rewrite ltnn.
by apply: eq_leq; symmetry; elim: (size p)=> //= n ->.
Qed.


Lemma inf_poly_eq0 : forall p, (inf_poly p == 0) = (p == 0).
Proof.
move=> p; apply/idP/idP; last by move/eqP->; rewrite inf_poly0.
rewrite/inf_poly mulf_eq0 sumr_eq0; last by apply/allP=> *; rewrite absrE.
case lp0: (lead_coef p == 0); first by move: lp0; rewrite lead_coef_eq0=> ->.
move: (lead_coef p) lp0=> l l0.
rewrite charor/=; move/allP=> hp.
apply/eqP; apply/polyP; move=> i; rewrite coef0.
case: (ltnP i (size p))=> hi; last exact: nth_default.
have: (`| p`_i / l | == 0); first by rewrite hp// mem_nth.
by rewrite absrE mulf_eq0 invr_eq0 l0 orbF; move/eqP.
Qed.

Lemma inf_poly_ge0 : forall p, inf_poly p >= 0.
Proof.
move=> p; rewrite /inf_poly.
rewrite mulr_cp0p//= 1?gtef0Sn// sumr_ge0//.
by apply/allP=> x; rewrite absrE.
Qed.

Lemma inf_noroot : forall p x, p != 0 -> `|x| > (inf_poly p) -> ~~ (root p x).
Proof.
move=> p x p0 xinf; rewrite /root -signr_cp0 sign_inf ?ltrW// signr_cp0.
rewrite mulf_neq0// 1?lead_coef_eq0//.
rewrite expf_neq0// -absr_eq0.
by rewrite eq_sym ltrWN // (ler_lte_trans (inf_poly_ge0 p)).
Qed.

Definition roots (p : {poly R}) (z : seq R) := forall x, root p x = (x \in z).

Fixpoint sorted (s : seq R) := 
  if s is a::s' 
    then (sorted s') && (if s' is b::s then a <= b else true)
    else true.

Definition sroots p z := (roots p z) /\ (uniq z) /\ (sorted z).  

Definition rootsI (p : {poly R}) (z : seq R) (a b : R) := 
  forall x, ((a < x < b) && root p x) = (x \in z).

Lemma roots_rootsI : forall p z a b,
  -(inf_poly p) <= a -> b <= inf_poly p ->
  roots p z <-> rootsI p z a b.
Admitted.

Definition srootsI p z a b := (rootsI p z a b) /\ (uniq z) /\ (sorted z).  

Definition multiplicity (p : {poly R}) x := 
  let fix aux p x n :=
    if n is m.+1
      then if (root p x) then (aux (p %/ ('X - x%:P)) x m).+1 else 0%N
      else 0%N
        in aux p x (size p).

Lemma root_multi : forall p x, ('X - x%:P)^+(multiplicity p x) %| p.
Admitted.

Lemma root_multiN : forall p x, p != 0 -> 
  (('X - x%:P)^+(multiplicity p x).+1 %| p) = false.
Admitted.

Require Import relative.

Fixpoint valp_right (p : {poly R}) z x := 
  if z is r1::z' then 
    if x < r1 then p.[x]
      else if x == r1 then
        if z' is r2::z'' then p.[(r1+r2)/2%:R]
          else p.[x+1]
        else valp_right p z' x
    else p.[x].

Definition ind (q p : {poly R}) a b (s : relative) := forall z z', 
  srootsI p z a b -> 
  srootsI q z' a b -> 
  s = \sum_(x <- z) 
  if ((odd ((multiplicity p x) - (multiplicity q x))) 
  && (valp_right q z' x > 0)) then 1 else -1.

Definition taq (q p : {poly R}) a b (s : relative) := forall z,
  srootsI p z a b -> s = \sum_(x <- z) (\s q.[x]) ?* 1.

Lemma taq_ind : forall q p a b s, taq q p a b s <-> ind (p^`() * q) p  a b s.
Admitted.

Definition varpI p a b := ((varp p a) - (varp p b))%N.

Lemma var_rem_ind : forall q p a b, ind q p a b (varpI (sremps p q) a b)%:R.
Admitted.

Lemma tarski : forall q p a b, taq q p a b ((varpI (sremps p (p^`() * q)) a b)%:R).
Proof. by move=> q p a b; apply/taq_ind; apply: var_rem_ind. Qed.

End PolyRFC.