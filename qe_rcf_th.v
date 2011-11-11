Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype path.
Require Import bigop ssralg poly polydiv orderedalg zmodp div zint.
Require Import polyorder polyrcf interval matrix mxtens perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory ORing.Theory.

Local Open Scope nat_scope.
Local Open Scope ring_scope.

Section extra.

Lemma sgp_rightc (R : rcfType) (x c : R) : sgp_right c%:P x = sgr c.
Proof.
rewrite /sgp_right size_polyC.
case cn0: (_ == 0)=> /=; first by rewrite (eqP cn0) sgr0.
by rewrite rootC hornerC cn0.
Qed.

Lemma sgp_right_eq0 (R : rcfType) (x : R) p :
  (sgp_right p x == 0) = (p == 0).
Proof.
case: (altP (p =P 0))=> p0; first by rewrite p0 sgp_rightc sgr0 eqxx.
rewrite /sgp_right.
elim: (size p) {-2}p (erefl (size p)) p0=> {p} [|sp ihsp] p esp p0.
  by move/eqP:esp; rewrite size_poly_eq0 (negPf p0).
rewrite esp /=; case px0: root=> //=; rewrite ?sgr_cp0 ?px0//.
have hsp: sp = size p^`() by rewrite size_deriv esp.
rewrite hsp ihsp // -size_poly_eq0 -hsp; apply/negP; move/eqP=> sp0.
move: px0; rewrite root_factor_theorem.
by move/(dvdp_leq p0); rewrite size_factor esp sp0.
Qed.

(* Todo : move in polydiv *)
(* Todo : in polydiv, exchange eqp_mull and eqp_mulr *)



End extra.

Section QeRcfTh.

Variable R : rcfType.

Fixpoint var (s : seq R) :=
  match s with
    | [::]  => 0%N
    | a :: q => ((a * (head 0 q) < 0)%R + (var q))%N
  end.

Definition varp (p : seq {poly R}) x := var (map (fun p => p.[x]) p).

Lemma var_cons a s : var (a::s) = ((a * (head 0 s) < 0)%R + var s)%N.
Proof. by case: s=> [|b s] //=; case hab: (_ < 0). Qed.

Fixpoint sremps_rec (p q : {poly R}) n :=
    if n is m.+1
      then if p == 0
        then [::]
        else p::(sremps_rec q (- (p %% q)) m)
      else [::].

Definition sremps (p q : {poly R}):= sremps_rec p q (maxn (size p) (size q).+1) .

Lemma sremps_recq0 : forall n (p : {poly R}), p != 0 ->
  sremps_rec p 0 n.+1 = [::p].
Proof.
move=> n p //= pn0; rewrite (negPf pn0).
by case:n=> [|n] //=; rewrite eqxx.
Qed.

Lemma sremps_recp0  n p : sremps_rec 0 p n = [::].
Proof. by case: n=> [|n] //=; rewrite eqxx. Qed.

Lemma sremps_recP_subproof n (p q : {poly R}) :
  (size q < size p)%N -> (size p <= n)%N ->
  sremps_rec p q n = sremps_rec p q (size p).
Proof.
elim: (size p) {-2 7}p (leqnn (size p)) n q
  => [|sp ihsp] {p} p hp n q /= sqp spn.
  by move: (leq_trans sqp hp).
case: n spn=> [|n] spn /=; first by move: (leq_trans sqp spn); rewrite ltn0.
case p0: (p==0)=> /=; first by move: sqp; rewrite (eqP p0) size_poly0 ltn0.
congr (_::_); case q0: (q == 0); first by rewrite (eqP q0) !sremps_recp0.
apply: ihsp; first by move: (leq_trans sqp hp).
  by rewrite size_opp ltn_modp q0.
by rewrite -ltnS; apply: leq_trans spn.
Qed.

Lemma sremps_recP n (p q : {poly R}) :
 ((if size p > size q then size p else (size q).+1) <= n)%N ->
 sremps_rec p q n = sremps p q.
Proof.
case: ltnP=> hpq hn.
  rewrite sremps_recP_subproof//; symmetry.
  by rewrite /sremps sremps_recP_subproof// maxnl.
rewrite /sremps maxnr ?leqW//=.
case: n hn=> // n; rewrite ltnS=> hn /=.
case p0: (_ == 0)=> //; congr (_ :: _).
rewrite sremps_recP_subproof // size_opp ltn_modp.
by rewrite -size_poly_eq0 -lt0n (leq_trans _ hpq) // lt0n size_poly_eq0 p0.
Qed.

Lemma sremps_recW : forall n (p q : {poly R}),
 ((maxn (size p) (size q).+1) <= n)%N -> sremps_rec p q n = sremps p q.
Proof.
move=> n p q hn; rewrite sremps_recP//; apply: leq_trans hn.
case: ltnP=> hpq; first by rewrite maxnl.
by rewrite maxnr ?ltnS ?leqW.
Qed.

Definition varpI a b p := (varp p a)%:Z - (varp p b)%:Z.

Definition nb_var (s : seq R) :=
  \sum_(n <- pairmap (fun x y => (sgz y) * (x * y < 0)) 0 s) n.

Lemma nb_varP : forall s, 0 \notin s ->
  nb_var s = (sgz (last 0 s)) * ((head 0 s) * (last 0 s) < 0).
Proof.
rewrite /nb_var; move=> s h0s.
case: s h0s=> /= [|a s]; first by rewrite big_nil sgz0 mul0r.
  rewrite in_cons negb_or eq_sym; case/andP=> a0 h0s.
  rewrite big_cons mul0r ltrr mulr0 add0r.
elim: s h0s a a0=> //= [|b s hs] h0s a a0 /=.
    by rewrite big_nil -sgz_cp0 sgzM; case: sgzP.
move: h0s; rewrite in_cons negb_or eq_sym; case/andP=> b0 h0s.
rewrite big_cons hs//.
rewrite -!sgz_cp0 !sgzM.
have: sgz (last b s) != 0.
  move: (mem_last b s); rewrite in_cons sgz_cp0; case/orP; first by move/eqP->.
  by apply: contraL; move/eqP->.
move: b0; rewrite -sgz_cp0; move: a0; rewrite -sgz_cp0.
by do 3!case: sgzP=> ? //.
Qed.

Implicit Types a b  : R.
Implicit Types p q : {poly R}.

Notation midf a b := ((a + b) / 2%:~R).

Notation seq_mids a s b := (pairmap (fun x y => midf x y) a (rcons s b)).

Definition jump q p x: zint :=
  ((-1) ^+ (sgp_right (q * p) x < 0)%R) *+
  [&& q != 0 & odd ((\mu_x p) - (\mu_x q))].

Definition sjump q p x: zint :=
  ((-1) ^+ (sgp_right (q * p) x < 0)%R) *+ (odd ((\mu_x (q*p)))).

Lemma sjumpC : forall q p x, sjump q p x = sjump p q x.
Proof. by move=> q p x; rewrite /sjump mulrC. Qed.

Lemma jump_coprime : forall p q, p != 0 -> coprimep p q
  -> forall x, root p x -> jump q p x = sjump q p x.
Proof.
move=> p q pn0 cpq x rpx; rewrite /jump /sjump; have q0: q != 0.
  apply/negP; move/eqP=> q0; move: cpq rpx; rewrite q0.
  rewrite coprimep0 -size_poly_eq1; case/size1P=> c c0 ->.
  by rewrite rootC; apply/negP.
rewrite q0 mu_mul ?mulf_neq0//; congr (_ *+ _).
rewrite odd_add odd_sub 1?addbC// (@leq_trans 0)//.
rewrite leqNgt mu_gt0//.
apply/negP; move: rpx; rewrite !root_factor_theorem=> hp hq.
move: cpq; apply/negP; apply/coprimepPn=> //.
by exists ('X - x%:P); rewrite dvdp_gcd hp hq -size_poly_eq1 size_factor.
Qed.

(* Todo : move in polydiv *)
Lemma mu_eq0 : forall p x, p != 0 -> (\mu_x p == 0%N) = (~~root p x).
Proof. by move=> p x p0; rewrite -mu_gt0 // -leqNgt leqn0. Qed.

Lemma exp1n_sgp_neigh : forall a b p x, p != 0 ->
  {in neighpl p a x & neighpr p x b, forall yl yr,
    (-1) ^+ (sgp_right p x < 0)%R *+ odd (\mu_x p)
    = (sgz ((p.[yr]))) * ((p.[yl] * p.[yr]) < 0)}.
Proof.
move=> a b p x pn0=> yl yr; rewrite !inE.
case/andP=> yll ylr; case/andP=> yrl yrr.
rewrite -!sgr_cp0 sgrM.
have yln: yl \in neighpl p a x by apply/andP.
have yrn: yr \in neighpr p x b by apply/andP.
move: (neighpr_root yrn).
rewrite (sgr_neighpl yln) -!(sgr_neighpr yrn) rootE -[_==0]sgr_cp0.
rewrite sgr_id sgrEz zintr_eq0 -[- 1 : R]mulrN1z.
rewrite (inj_eq (mulrIz _)) ?oner_eq0 //.
rewrite [_ ^+ odd _]exprnP exprz_pzintl //.
rewrite -!rmorphM (inj_eq (mulrIz _)) ?oner_eq0 //.
by case ho: (odd _); case: (sgzP p.[yr]).
Qed.


Lemma sjump_neigh : forall a b p q x, q * p != 0 ->
  {in neighpl (q * p) a x & neighpr (q * p) x b, forall yl yr,
    sjump q p x = (sgz (((q * p).[yr])))
                   * (((q * p).[yl] * (q * p).[yr]) < 0)}.
Proof.
move=> a b p q x pqn0 yl yr hyl hyr.
by rewrite /sjump (exp1n_sgp_neigh _ hyl hyr).
Qed.

Lemma jump_neigh : forall a b p q x, q * p != 0 ->
  {in neighpl (q*p) a x & neighpr (q*p) x b, forall yl yr,
    jump q p x = ((sgz (((q*p).[yr]))) * (((q*p).[yl] * (q*p).[yr]) < 0))
    *+ ((q != 0) && (\mu_x p > \mu_x q)%N)}.
Proof.
move=> a b p q x pqn0 yl yr hyl hyr.
move: (pqn0); rewrite mulf_eq0 negb_or; case/andP=> qn0 pn0.
rewrite /jump qn0 /=; case: ltnP=> hmuxpq.
  rewrite odd_sub 1?ltnW // addbC -odd_add -mu_mul //.
  by rewrite (exp1n_sgp_neigh _ hyl hyr).
by move: hmuxpq; rewrite -subn_eq0; move/eqP->.
Qed.

Lemma jump_mul2l : forall (p q r : {poly R}), p != 0 ->
  jump (p * q) (p * r) =1 jump q r.
Proof.
move=> p q r p0 x; rewrite /jump.
case q0: (q == 0); first by rewrite (eqP q0) mulr0 eqxx.
have ->: p * q != 0 by rewrite mulf_neq0 ?p0 ?q0.
case r0: (r == 0); first by rewrite (eqP r0) !mulr0 mu0 !sub0n.
rewrite !mu_mul ?mulf_neq0 ?andbT ?q0 ?r0 //; rewrite subn_add2l.
rewrite mulrAC mulrA -mulrA.
rewrite (@sgp_right_mul _ (p * p)) // sgp_right_mul // sgp_right_square //.
by rewrite mul1r mulrC /=.
Qed.

Lemma jump_mul2r : forall p q r : {poly R}, p != 0 ->
  jump (q * p) (r * p) =1 jump q r.
Proof. by move=> p q r p0 x; rewrite ![_ * p]mulrC jump_mul2l. Qed.

Lemma jump0p : forall q, forall x, jump 0 q x = 0.
Proof. by move=>  q x; rewrite /jump eqxx mulr0n. Qed.

Lemma jumppc : forall p c, forall x, jump p c%:P x = 0.
Proof. by move=> p c x; rewrite /jump mu_polyC sub0n !andbF. Qed.

Lemma jump_mulCp : forall c p q,
  forall x, jump (c *: p) q x = (sgz c) * jump p q x.
Proof.
move=> c p q x; case c0: (c == 0).
  by rewrite (eqP c0) sgz0 scale0r jump0p mul0r.
case p0: (p == 0); first by rewrite (eqP p0) scaler0 jump0p mulr0.
case q0: (q == 0); first by rewrite (eqP q0) !jumppc mulr0.
(* Todo : rename mu_mulC *)
rewrite /jump scale_poly_eq0 mu_mulC ?c0 // orFb.
rewrite -scaler_mull sgp_right_scale //.
case: sgzP c0=> //; first by rewrite !mul1r.
(* Todo : replace nat by zint everywhere *)
move=> _ _; rewrite !mulN1r !natmulP -mulNrz ?p0 /= ?oppr_cp0; congr (_ *~ _).
by case: ltrgtP=> //; move/eqP; rewrite sgp_right_eq0 mulf_eq0 p0 q0.
Qed.

Lemma jump_pmulC : forall c p q,
  forall x, jump p (c *: q) x = (sgz c) * jump p q x.
Proof.
move=> c p q x; case c0: (c == 0).
  by rewrite (eqP c0) sgz0 scale0r mul0r jumppc.
case p0: (p == 0); first by rewrite (eqP p0) !jump0p mulr0.
case q0: (q == 0); first by rewrite (eqP q0) scaler0 !jumppc mulr0.
rewrite /jump mu_mulC ?c0 //= -scaler_mulr sgp_right_scale //.
case: sgzP c0 => //; first by rewrite !mul1r.
move=> _ _; rewrite !mulN1r !natmulP -mulNrz lter_oppl/= oppr0; congr (_ *~ _).
by case: ltrgtP=> //; move/eqP; rewrite sgp_right_eq0 mulf_eq0 p0 q0.
Qed.

(* Lemma jumpX : forall p q p' q' : {poly R}, q != 0 -> q' != 0 -> *)
(*   p * q' == p' * q -> jump p q =1 jump p' q'. *)
(* Proof. *)
(* move=> p q p' q' q0 q'0. *)
(* move/eqpP=> [u [v [hu hv]]] hpq x. *)
(* case p0: (p == 0). *)
(*   move/eqP: hpq; rewrite (eqP p0) mul0r mulr0. *)
(*   rewrite eq_sym !mulf_eq0 (negPf q0) orbF polyC_eq0 (negPf hv)/=; move/eqP->. *)
(*   by rewrite !jump0p. *)
(* case p'0: (p' == 0). *)
(*   move/eqP: hpq; rewrite (eqP p'0) mul0r mulr0. *)
(*   rewrite !mulf_eq0 (negPf q'0) orbF polyC_eq0 (negPf hu)/=; move/eqP->. *)
(*   by rewrite !jump0p. *)
(* rewrite -(@jump_mul2l ((u%:P * v%:P) * (p' * q'))) *)
(*   ?mulf_neq0 ?p'0 ? polyC_eq0 ?hu ?hv//. *)
(* rewrite -mulrA mulrAC {1}[_ * q']mulrC {1}[v%:P * _]mulrCA. *)
(* rewrite -![_ * q]mulrA [_ * q]mulrC [p' * _]mulrA [v%:P * (_ * _)]mulrA. *)
(* rewrite -hpq !mulrA -{1}[u%:P * _ * q']mulrA. *)
(* rewrite mulrAC mulrC -!mulrA !jumpcp !jumppc. *)
(* do 2?rewrite mulrA mulss (hv,hu) mul1r. *)
(* rewrite [p' * _]mulrC mulr. *)
(* rewrite -mulrA [_ * p]mulrC hpq mulrAC -hpq. *)
(* by rewrite [p' * _]mulrC jump_mul2l ?mulf_neq0 ?p0. *)
(* Qed. *)

(* Todo : move to polydiv *)
(* Lemma scalp_size : forall p q, p != 0 -> (size p < size q)%N -> (lead_coef q) ^+ scalp p q = 1. *)
(* Proof. *)
(* move=> p q p0 hpq; have := (divCp_spec p q). *)
(* rewrite divp_size // modp_size // mul0r add0r; move/eqP. *)
(* rewrite -subr_eq0 -{3}[p]scale1r -scaler_subl scaler_eq0. *)
(* by rewrite (negPf p0) orbF subr_eq0; move/eqP. *)
(* Qed. *)

(* Todo : move to polydiv *)
Lemma mu_mod : forall p q x, (\mu_x p < \mu_x q)%N ->
 \mu_x (p %% q) =  \mu_x p.
Proof.
move=> p q x mupq; case p0: (p == 0); first by rewrite (eqP p0) mod0p.
have qn0 : q != 0 by apply/negP; move/eqP=> q0; rewrite q0  mu0 ltn0 in mupq.
move/eqP: (divp_eq p q).
rewrite eq_sym (can2_eq (addKr _ ) (addNKr _)); move/eqP->.
case qpq0: ((p %/ q) == 0); first by rewrite (eqP qpq0) mul0r oppr0 add0r.
rewrite mu_addl ?p0 // mu_opp mu_mul; last by rewrite mulf_neq0 // qpq0.
by rewrite (leq_trans mupq) ?leq_addl.
Qed.

(* Todo : move to polydiv *)
Lemma mu_add : forall p q x, p + q != 0 ->
  (minn (\mu_x p) (\mu_x q) <= \mu_x (p + q)%R)%N .
Proof.
move=> p q x pq0.
case p0: (p == 0); first by rewrite (eqP p0) mu0 min0n add0r.
case q0: (q == 0); first by rewrite (eqP q0) mu0 minn0 addr0.
case: (ltngtP (\mu_x p) (\mu_x q))=> hmupq.
* by rewrite mu_addr ?p0 // minnl // ltnW.
* by rewrite mu_addl ?q0 // minnr // ltnW.
* case: (@mu_spec _ p x)=> [|p' nrp'x hp]; first by rewrite p0.
  case: (@mu_spec _ q x)=> [|q' nrq'x hq]; first by rewrite q0.
  rewrite hmupq minnn hp {2}hq hmupq -mulr_addl mu_mul; last first.
     by rewrite mulr_addl -{1}hmupq -hp -hq.
  by rewrite mu_exp mu_factor mul1n leq_addl.
Qed.

(* Todo : move to polydiv *)
Lemma mu_mod_leq : forall p q x, ~~ (q %| p) ->
  (\mu_x q <= \mu_x p)%N ->
  (\mu_x q <= \mu_x (p %% q)%R)%N.
Proof.
move=> p q x. rewrite /dvdp => rn0 mupq.
case q0: (q == 0); first by rewrite (eqP q0) mu0 leq0n.
move/eqP: (divp_eq p q).
rewrite eq_sym (can2_eq (addKr _ ) (addNKr _)); move/eqP=> hr.
rewrite hr; case qpq0: (p %/ q == 0).
  by rewrite (eqP qpq0) mul0r oppr0 add0r.
rewrite  (leq_trans _ (mu_add _ _)) // -?hr //.
by rewrite leq_minr mu_opp mu_mul ?mulf_neq0 ?qpq0 ?q0 // leq_addl.
Qed.

(* Lemma sgp_right0 : forall (x : R), sgp_right 0 x = 0. *)
(* Proof. by move=> x; rewrite /sgp_right size_poly0. Qed. *)

Lemma sgp_right_mod : forall p q x, (\mu_x p < \mu_x q)%N ->
  sgp_right (p %% q) x =  sgp_right p x.
Proof.
move=> p q x mupq; case p0: (p == 0).
  by rewrite (eqP p0) mod0p !sgp_right0.
have qn0 : q != 0.
  by apply/negP; move/eqP=> q0; rewrite q0  mu0 ltn0 in mupq.
move/eqP: (divp_eq p q).
rewrite eq_sym (can2_eq (addKr _ ) (addNKr _)); move/eqP->.
case qpq0: ((p %/ q) == 0); first by rewrite (eqP qpq0) mul0r oppr0 add0r. 
by rewrite sgp_right_addp0 ?p0 // mu_opp mu_mul ?mulf_neq0 ?qpq0 // ltn_addl.
Qed.


(* Todo : system to solve neighbordhood dependency automatically *)
Lemma jump_mod : forall p q, forall x, jump p q x = jump (p %% q) q x.
Proof.
move=> p q x.
case p0: (p == 0); first by rewrite (eqP p0) mod0p jump0p.
case q0: (q == 0); first by rewrite (eqP q0) modp0 jumppc.
case r0: (p %% q == 0).
  rewrite (eqP r0) jump0p //.
  move: (r0); rewrite -/(_ %| _) dvdp_eq; move/eqP->.
  case qq0: (p %/ q == 0); first by rewrite (eqP qq0) mul0r jump0p.
  by rewrite -{3}[q]mul1r jump_mul2r// ?oner_eq0 ?q0 ?qq0 ?coprimep1// jumppc.
rewrite /jump.
case: (ltnP (\mu_x p) (\mu_x q)) => hpq; last first.
  move: (hpq); rewrite -subn_eq0; move/eqP->; rewrite andbF mulr0n.
  move/mu_mod_leq:(hpq); rewrite /dvdp -subn_eq0=> hqr.
  by rewrite (eqP (hqr _)) ?r0 // mulr0.
rewrite mu_mod // p0 r0 /=; congr (_ *+ _).
move/eqP: (divp_eq p q).
rewrite eq_sym (can2_eq (addKr _ ) (addNKr _)); move/eqP=> hr.
by rewrite !sgp_right_mul // sgp_right_mod // -mulrA.
Qed.


Definition cind (a b : R) (q p : {poly R}) : zint :=
  \sum_(x <- roots p a b) jump q p x.

Lemma cind0p : forall a b, a < b -> forall q, cind a b 0 q = 0.
Proof.
move=> a b hab q; rewrite /cind /jump.
by apply: big1_seq=> x; rewrite eqxx mulr0n.
Qed.

Lemma rootsC : forall a b c, roots c%:P a b = [::].
Proof.
move=> a b c; case: (altP (c =P 0))=> hc; first by rewrite hc roots0.
by apply: no_root_roots=> x hx; rewrite rootC.
Qed.

Lemma cindpc : forall a b, a < b -> forall p c,
  cind a b p (c%:P) = 0.
Proof. by move=> a b hab p c; rewrite /cind /jump rootsC big_nil. Qed.

Lemma cind_mul2r : forall a b, a < b -> forall p q (r : {poly R}),
  p != 0 -> q != 0 -> r != 0 ->
  cind a b (p * r) (q * r) = cind a b p q.
Proof.
move=> a b hab p q r p0 q0 r0; rewrite /cind.
rewrite (eq_big_perm _ (roots_mul _ _ _))//= big_cat/=.
rewrite -[\sum_(x <- _) jump p _ _]addr0; congr (_+_).
  rewrite !big_seq; apply: congr_big => // x hx.
  by rewrite jump_mul2r.
rewrite big1_seq//= => x hx; rewrite jump_mul2r // /jump.
suff ->: \mu_x q = 0%N by rewrite andbF.
apply/eqP; rewrite -leqn0 leqNgt mu_gt0 //.
apply/negP; rewrite root_factor_theorem => rqx; move/root_roots:hx.
case: gdcopP=> g hg; rewrite (negPf r0) orbF => cgq hdg.
rewrite root_factor_theorem=> rgx.
move/coprimepP:cgq rqx rgx=> cgq; move/cgq=> hgq; move/hgq.
by rewrite -size_poly_eq1 size_factor.
Qed.

Lemma cind_mulCp : forall a b, a < b -> forall p q c, p != 0 -> q != 0 ->
  cind a b (c *: p) q = (sgz c) * cind a b p q.
Proof.
move=> a b hab p q c p0 q0; rewrite /cind big_distrr.
by apply: congr_big=> //= x _; rewrite jump_mulCp.
Qed.

(* Todo : add root_scale *)
Lemma cind_pmulC : forall a b, a < b -> forall p q c, p != 0 -> q != 0 ->
  cind a b p (c *: q) = (sgz c) * cind a b p q.
Proof.
move=> a b hab p q c p0 q0.
case c0: (c == 0); first by rewrite (eqP c0) scale0r sgz0 mul0r cindpc.
rewrite /cind big_distrr (* ![\sum_(x <- _) _]big_seq_cond *).
set rcq := roots  _ _ _; set rq := roots  _ _ _.
have hrcq: rcq = rq.
  apply/roots_eq=> //; first by rewrite scaler_eq0 c0.
  by move=> x hx; rewrite /= rootE !horner_lin mulf_eq0 c0.
apply: congr_big; rewrite ?hrcq //= => x _.
by rewrite jump_pmulC.
Qed.
(* rewrite p0 !andbT mu_mulC ?c0//= mulrCA (sgp_right_mul c%:P) sgp_rightc. *)
(* case: (sgrP c); first by move/eqP; rewrite sgr_cp0 c0. *)
(*   by rewrite !mul1r. *)
(* move=>_; rewrite !mulN1r -mulNrz; congr (_ *+ _). *)
(* rewrite lter_oppl/= oppr0; case: ltrgtP=> //. *)
(* by move/eqP; rewrite sgp_right_eq0 mulf_eq0 (negPf p0) (negPf q0). *)
(* Qed. *)


Lemma cind_mod : forall a b, a < b -> forall p q,
   cind a b p q = cind a b (p %% q) q.
Proof.
move=> a b hab p q; rewrite /cind.
by apply: congr_big=> //= x _; rewrite jump_mod.
Qed.


Lemma cind_seq_mids : forall a b, a < b -> forall p q, p != 0 -> q != 0 ->
  coprimep p q ->  cind a b q p + cind a b p q =
  nb_var (map (horner (p * q)) (seq_mids a (roots (p * q) a b) b)).
Proof.
move=> a b hab p q p0 q0 cpq.
rewrite /cind /nb_var 2!big_seq.
have jumpP : forall (p q : {poly R}), p != 0 -> coprimep p q  ->
  forall x, x \in roots p a b -> jump q p x = sjump q p x.
  by move=> ? ? ? ? ?; move/root_roots=> ?; rewrite jump_coprime.
rewrite !(eq_bigr _ (jumpP _ _ _ _))// 1?coprimep_sym//.
rewrite -!big_seq (eq_bigr _ (fun x _ => sjumpC q p x)).
rewrite -big_cat /= -(eq_big_perm _ (roots_mul_coprime _ _ _ _)) //=.
move: {1 4}a (erefl (roots (p * q) a b))=> //=.
elim: (roots _ _ _)=> [|x s /= ihs] a' hxs.
  by rewrite big_nil/= mul0r ltrr mulr0 big_cons big_nil addr0.
move/eqP: hxs; rewrite roots_cons; case/and5P=> _.
case/andP=> ax xs hax hx hs.
rewrite mul0r ltrr mulr0 !big_cons add0r (ihs x) ?(eqP hs)//.
have pq0: p * q == 0 = false by apply: negbTE; rewrite mulf_neq0.
case: s ihs hs xs=> [|y s]//= ihs hs xs.
  rewrite !big_cons !big_nil !addr0 mul0r ltrr mulr0 addr0.
  apply: (@sjump_neigh a' b); rewrite ?mulf_neq0// !inE /= ?midf_lte //=.
    by rewrite /prev_root pq0 (eqP hax) /= minr_l ?(ltrW ax) // midf_lte.
  by rewrite /next_root pq0 (eqP hs) /= maxr_l ?(ltrW xs) // midf_lte.
rewrite !big_cons mul0r ltrr mulr0 add0r; congr (_+_).
move: hs; rewrite roots_cons; case/and5P=> _.
case/andP=> xy ys hxy pqy0 hs.
apply: (@sjump_neigh a' y); rewrite ?mulf_neq0// !inE /= ?midf_lte //=.
  by rewrite /prev_root pq0 (eqP hax) /= minr_l ?(ltrW ax) // midf_lte.
by rewrite /next_root pq0 (eqP hxy) /= maxr_l ?(ltrW xy) // midf_lte.
Qed.

Lemma cind_inv : forall a b, a < b -> forall p q,
  ~~ root (p * q) a -> ~~ root (p * q) b ->
  cind a b q p + cind a b p q =
  (sgz ((p * q).[b])) * (((p * q).[a])*((p * q).[b]) < 0).
Proof.
move=> a b hab p q hpqa hpqb.
have hlab: a <= b by apply: ltrW.
have p0: p != 0.
  by move: hpqa; apply: contra; move/eqP->; rewrite mul0r rootC.
have q0: q != 0.
  by move: hpqa; apply: contra; move/eqP->; rewrite mulr0 rootC.
wlog cpq: p q p0 q0 hpqa hpqb / coprimep p q.
  move=> hc; move: (dvdp_gcdr p q) (dvdp_gcdl p q).
  rewrite !dvdp_eq.
  set gpq := gcdp p q.
  set qp := (p %/ _);  set qq := (q %/ _).
  move/eqP=> hq; move/eqP=> hp.
  move: (p0). rewrite hp !(mulf_eq0, scaler_eq0, negb_or).
  case/andP=> qp0 gpq0.
  move: (q0); rewrite hq !(mulf_eq0, scaler_eq0, negb_or).
  case/andP=> qq0 _.
  move: (hpqa) (hpqb).
  rewrite hp hq.
  have csqpqq: coprimep qp qq.
    by rewrite /qp /qq; apply: coprimep_div_gcd; rewrite p0.
  rewrite !rootE.
  rewrite !{1}horner_mul.
  rewrite !sgzM /=.
  rewrite !mulf_eq0 !negb_or.
  case/and3P =>/andP [qpa gq] qqa _.
  case/and3P=> /andP [qpb gb] qqb _.
  rewrite !cind_mul2r //.
  rewrite hc ?rootE ?{1}horner_mul;
    do ?by rewrite ?sgrM ?(mulf_neq0, negb_or, qp0, qq0) //=.
  rewrite -!sgr_cp0 !sgrM.
  have hss (R' : oIdomainType) s s' (c : R') : c != 0 ->
    (s * sgr c) * s' * sgr c = s * s'.
    by move=> nc0; rewrite ![_ * sgr _]mulrC !mulrA mulr_sg nc0 mul1r.
  have hss' (R' : oIdomainType) s s' (c : R') : c != 0 ->
    (s * sgz c) * s' * sgz c = s * s'.
    by move=> nc0; rewrite ![_ * sgz _]mulrC !mulrA mulz_sg nc0 mul1r.
  by rewrite mulrA mulrA hss' // !mulrA !hss // sgzM.
rewrite cind_seq_mids//.
have pq0 : p * q == 0 = false by apply: negPf; rewrite mulf_neq0.
rewrite nb_varP//= -cats1 pairmap_cat/= cats1 map_rcons.
  rewrite last_rcons -sgr_cp0 !sgrM -sgz_sgr.
  rewrite [sgr _.[_]](@sgr_neighplN _ _ a b) //; last first.
    by rewrite /neighpl /prev_root pq0 minr_l // mid_in_int //= last_roots_le.
  case hr: (roots (p * q) a b)=> [|x r] //=.
    rewrite (@sgr_neighprN _ _ a b _ (_/2%:~R)) //; last first.
      by rewrite /neighpr /next_root pq0 maxr_l // hr mid_in_int.
    by rewrite -[_<_]sgr_cp0 sgz_sgr sgrM.
  move/eqP:(hr); rewrite roots_cons; case/and5P=> _.
  case/andP=> ax xr hax rpqx hr'.
  rewrite -sgz_sgr.
  rewrite (@sgr_neighprN _ _ a b _ (_/2%:~R)) //; last first.
    by rewrite /neighpr /next_root pq0 maxr_l // hr mid_in_int.
  by rewrite -[_<_]sgr_cp0 !sgz_sgr sgrM.
rewrite -cats1 mem_cat negb_or in_cons in_nil orbF eq_sym; apply/andP; split.
  elim: (roots (p * q) a b) {-2}a (erefl (roots (p * q) a b)).
    by move=> a' ->.
  move=> x s ihs a' hxs; rewrite hxs /= in_cons negb_or eq_sym.
  move/eqP: (hxs); rewrite roots_cons; case/and5P=> _.
  case/andP=> ax xs hax rpqx hs.
  rewrite -(eqP hs) ihs ?(eqP hs)// andbT.
  rewrite (@neighpl_root _ _ a' x)//.
  by rewrite /neighpl /prev_root pq0 minr_l ?(ltrW ax) // (eqP hax) mid_in_int.
rewrite (@neighpl_root _ _ a b) // /neighpl /prev_root.
rewrite mulf_eq0 (negPf p0) (negPf q0) minr_l //= mid_in_int //=.
by rewrite last_roots_le.
Qed.

(* Todo : move to ssrnat ? *)
Lemma maxnSS: forall m n, maxn m.+1 n.+1 = (maxn m n).+1.
Proof. by move=> m n; rewrite /maxn ltnS; case: ifP. Qed.

Lemma sremps_ind : forall p q, p != 0 ->
  sremps p q = p :: (sremps q (- (p %% q))).
Proof.
move=> p q np0; rewrite {1}/sremps /=.
case hsp: (size p)=> [|sp] /=.
  by move/eqP: hsp np0; rewrite size_poly_eq0; move/eqP->; rewrite eqxx.
rewrite maxnSS /= (negPf np0); congr cons.
case q0: (q == 0); first by rewrite /sremps (eqP q0) !sremps_recp0.
rewrite sremps_recW // size_opp maxnl; first by rewrite !leq_maxr leqnn orbT.
by rewrite ltn_modp q0.
Qed.

Lemma var_rem_cind : forall a b, a < b -> forall p q,
  p != 0 -> q != 0 ->
  all (fun p => ~~ root p a) (sremps p q) ->
  all (fun p => ~~ root p b) (sremps p q) ->
  varpI a b (sremps p q) = (cind a b q p).
Proof.
move=> a b hab p q hp hq.
rewrite 2?{1 2}sremps_ind//=.
  case/and3P=> pa0 qa0 allra0.
  case/and3P=> pb0 qb0 allrb0.
(* have hpqab : ((p * q).[a])*((p * q).[b]) != 0 by rewrite mulf_neq0. *)
elim: (sremps _ _) {-2}p {-2}q (erefl (sremps p q)) hp hq pa0 pb0 qa0 qb0
  allra0 allrb0 => [|r s hs] {p q} p q hr hp hq pa0 pb0 qa0 qb0 allra0 allrb0.
  rewrite hr /varpI /varp subrr /=.
  suff: (p == 0) by rewrite (negPf hp).
  move/eqP: hr; apply: contraLR=> pn0; rewrite /sremps.
  case hm: (maxn (size p) (size q).+1)=> [|m] //=.
    by move/eqP:hm; rewrite -leqn0 leq_maxl leqn0 size_poly_eq0 (negPf pn0).
  by rewrite (negPf pn0).
rewrite hr; move: hr; rewrite /sremps.
case hm: (maxn (size p) (size q).+1)=> [|m] //=.
have q0 := (negPf hq); have p0 := (negPf hp); rewrite p0.
case=> er es; rewrite -er -es.
rewrite /varpI /varp !map_cons !var_cons.
have aux : (maxn (size q) (size (- (p %% q)%R)).+1 <= m)%N.
  by rewrite size_opp maxnl ?ltn_modp // -ltnS -hm leq_maxr ltnSn orbT.
rewrite sremps_recW // in es.
have m0 x : 0 = (0 : {poly R}).[a] by rewrite hornerC.
rewrite !PoszD addrAC oppr_add -!addrA addrA [- _ + _]addrC.
rewrite -[(varp _ _)%:Z - _]/(varpI _ _ _).
rewrite {3}sremps_recW //.
case: m hm es {aux} => [|m hm es] //=.
  move/eqP; rewrite eqn_leq; case/andP; rewrite leq_maxl; case/andP=> _.
  by rewrite ltnS leqn0 size_poly_eq0 q0.
rewrite q0 /=; apply/eqP; rewrite (can2_eq (addrK _) (addrNK _)); apply/eqP.
transitivity (cind a b q p + cind a b p q).
  rewrite cind_inv // ?root_mul; do ?by apply/norP.
  rewrite -!sgr_cp0 !horner_mul [sgr (_*_*_)]sgrM.
  rewrite !sgrEz -rmorphM -[- 1 : R]mulrN1z !(inj_eq (mulrIz _)) ?oner_eq0 //.
  have: (sgz (p.[a] * q.[a]) != 0) by rewrite sgz_cp0 mulf_neq0.
  have: (sgz (p.[b] * q.[b]) != 0) by rewrite sgz_cp0 mulf_neq0.
  by do 2?case: sgzP => _ //.
case r0: (p %% q == 0).
  move: (r0); rewrite -/(_ %| _) dvdp_eq; move/eqP=> hr.
  have: cind a b (p %/ q * q) q = 0.
    rewrite -{3}[q]mul1r cind_mul2r ?cindpc ?oner_eq0 ?coprimep1 //.
    by move/eqP: hr; apply: contraL; move/eqP->; rewrite mul0r p0.
  rewrite -hr; move->. rewrite (eqP r0) addr0.
  rewrite /sremps; case hmn: (maxn _ _)=> [|mn] /=.
    by rewrite /varpI /varp /= subr0.
  by rewrite q0 oppr0 sremps_recp0 /varpI /varp /= !mulr0 ltrr subrr subr0.
move: allra0 allrb0.
rewrite sremps_ind ?oppr_eq0 ?r0 //=.
rewrite !rootE.
case/andP=> rpqa allra0; case/andP=> rpqb allrb0; rewrite hs ?oppr_eq0 ?r0 //.
by rewrite -scaleN1r cind_mulCp ?r0 // sgzN1 mulNr opprK mul1r -cind_mod.
Qed.

Definition taq (z : seq R) (q : {poly R}) : zint := \sum_(x <- z) (sgz q.[x]).

Lemma taq_cind : forall a b, a < b -> forall p q,
  taq (roots p a b) q = cind a b (p^`() * q) p.
Proof.
move=> a b hab p q.
rewrite /taq /cind /jump !big_seq.
apply: eq_bigr => x hxz.
have rpx: root p x by exact:(root_roots hxz).
case p'q0: (p^`()*q == 0) => //.
  rewrite (eqP p'q0) mulr0n /=.
  move: p'q0; rewrite mulf_eq0; case/orP; last first.
    by move/eqP->; rewrite horner0 sgz0.
  rewrite -size_poly_eq0 size_deriv.
  case hsp: (size p)=> [|sp] /=.
    move/eqP:hsp; rewrite size_poly_eq0; move/eqP=> p0 _.
    by move: hxz; rewrite p0 roots0.
  move/eqP=> sp0; move/eqP: hsp; rewrite sp0.
  move/size1P=> [c c0 hp].
  by move: rpx; rewrite hp rootC (negPf c0).
move/negP: p'q0; move/negP=> p'q0.
move:(p'q0); rewrite mulf_eq0 negb_or; case/andP=> p'0 q0.
have p0: p != 0 by move: p'0; apply: contra; move/eqP->; rewrite derivC.
rewrite mu_mul// {1}(@mu_deriv_root _ _ p)// addn1.
case emq: (\mu_(_) q)=> [|m].
  move/eqP: emq; rewrite -leqn0 leqNgt mu_gt0// => qxn0.
  rewrite addn0 subSnn mulr1n.
  rewrite !sgp_right_mul// (sgp_right_deriv rpx) mulrAC.
  rewrite sgp_right_square// mul1r sgp_rightNroot//.
  rewrite sgr_lt0 -sgz_cp0.
  by move: qxn0; rewrite -[root q x]sgz_cp0; case: sgzP.
rewrite addnS subSS -{1}[\mu_(_) _]addn0 subn_add2l sub0n mulr0n.
by apply/eqP; rewrite sgz_cp0 -[_ == 0]mu_gt0// emq.
Qed.

(* Todo : sremps0p *)
Lemma tarski : forall a b, a < b -> forall q p,
  p != 0 -> q != 0 ->
  all (fun p => p.[a] != 0) (sremps p (p^`() * q)) ->
  all (fun p => p.[b] != 0) (sremps p (p^`() * q)) ->
  taq (roots p a b) q = (varpI a b (sremps p (p^`() * q))).
Proof.
move=> a b hab q p p0 q0 allrpa0 allrpb0.
case p'0: (p^`() == 0).
  rewrite (eqP p'0) mul0r.
  symmetry; transitivity 0%N.
    rewrite /sremps; case hmn: (maxn _ _)=> [|mn] /=.
      by rewrite /varpI /varp /=.
    by rewrite (negPf p0) sremps_recp0 /varpI /varp /= !mulr0 ltrr subrr.
   move: p'0; rewrite -size_poly_eq0 size_deriv=> sp.
   rewrite [p]size1_polyC -?subn_eq0 ?subn1 //.
   by rewrite ?rootsC /taq ?big_nil //.
by rewrite taq_cind// -var_rem_cind// mulf_neq0 // p'0.
Qed.

Definition croots (z : seq R) (sq : seq {poly R}) (sc : seq zint) : nat :=
  (\sum_(x <- z) \prod_(i < size sq) (sgz (sq`_i).[x] == sc`_ i))%N.

Lemma taq_croots1 : forall z q,
  taq z q = (croots z [::q] [::1])%:~R - (croots z [::q] [::-1])%:~R.
Proof.
move=> z q; rewrite /croots /taq !sumMz -sumr_sub /=; apply: congr_big=> //.
move=> x _; rewrite !big_ord_recl big_ord0 !muln1 /=.
by case: sgzP.
Qed.

Lemma taq_croots0 : forall z q,
  taq z 1 = (croots z [::q] [::0])%:~R + (croots z [::q] [::1])%:~R + (croots z [::q] [::-1])%:~R.
Proof.
move=> z q; rewrite /croots /taq !sumMz //= -!big_split /=; apply: congr_big=> //.
move=> x _; rewrite hornerC sgz1 !big_ord_recl big_ord0 !muln1 /=.
by case: sgzP.
Qed.

Lemma taq_croots_nil : forall z, taq z 1 = (croots z [::] [::])%:~R.
Proof.
move=> z; rewrite /croots /taq !sumMz; apply: congr_big=> //.
by move=> x _; rewrite hornerC sgz1 big_ord0.
Qed.

Lemma taq_croots2 : forall z q,
  taq z (q^+2) = (croots z [::q] [::1])%:~R + (croots z [::q] [::-1])%:~R.
Proof.
move=> z q; rewrite /croots /taq !sumMz -big_split /=; apply: congr_big=> //.
move=> x _; rewrite !big_ord_recl big_ord0 !muln1 /=.
rewrite horner_exp sgzX.
by case: (sgzP q.[x])=> _.
Qed.

Definition comb_exp (R : oIdomainType) (s : R) :=
  match sgz s with Posz 1 => 1%N | Negz 0 => 2 | _ => 0%N end.

Definition poly_comb (sq : seq {poly R}) (sc : seq zint) : {poly R} :=
  \prod_(i < size sq) ((sq`_i) ^+ (comb_exp sc`_i)).

Fixpoint sg_tab n : seq (seq zint) :=
  if n is m.+1
    then flatten (map (fun x => map (fun l => x :: l) (sg_tab m)) [::1;-1;0])
    else [::[::]].

(* Eval compute in sg_tab 4. *)

Definition cvec z sq := let sg_tab := sg_tab (size sq) in
  \row_(i < 3^size sq) ((croots z sq (nth [::] sg_tab i))%:~R : zint).
Definition tvec z sq := let sg_tab := sg_tab (size sq) in
  \row_(i < 3^size sq) (taq z (map (poly_comb sq) sg_tab)`_i).

Definition ctmat1 := \matrix_(i < 3, j < 3)
  (nth [::]
    [:: [:: 1%:Z ; 1 ; 1 ]
      ; [:: -1   ; 1 ; 1 ]
      ; [::  0   ; 0 ; 1 ] ] i)`_j.

Lemma det_ctmat1 : \det ctmat1 = 2.
Proof.
(* Developpement direct ? *)
by do ?[rewrite (expand_det_row _ ord0) //=;
  rewrite ?(big_ord_recl,big_ord0) //= ?mxE //=;
    rewrite /cofactor /= ?(addn0, add0n, expr0, exprS);
      rewrite ?(mul1r,mulr1,mulN1r,mul0r,mul1r,addr0) /=;
        do ?rewrite [row' _ _]mx11_scalar det_scalar1 !mxE /=].
Qed.

Notation zmxR := ((map_mx ((zintmul 1) : zint -> R)) _ _).

Lemma ctmat1_unit : zmxR ctmat1 \in unitmx.
Proof.
rewrite /mem /in_mem /= /unitmx det_map_mx //.
by rewrite det_ctmat1 unitfE zintr_eq0.
Qed.

Lemma tvec_cvec1 : forall z q,
  tvec z [::q] = (cvec z [::q]) *m ctmat1.
Proof.
move=> z q //=.
apply/rowP=> j.
rewrite /tvec !mxE /poly_comb /= !big_ord_recl !big_ord0 //=.
rewrite !(expr0,expr1,mulr1) /=.
case: j=> [] [|[|[|j]]] hj //.
* by rewrite !mxE /= mulr0 add0r mulr1 mulrN1 addr0 taq_croots1.
* by rewrite !mxE /= mulr0 !mulr1 add0r addr0 taq_croots2.
* by rewrite !mxE /= addrA (@taq_croots0 _ q) !mulr1 addr0 -addrA addrC.
Qed.

Lemma exp3n : forall n, (3 ^ n)%N = (3 ^ n).-1.+1.
Proof.
move=> n; rewrite prednK//.
by elim: n => //= n ihn; rewrite expnS muln_gt0.
Qed.

Local Notation sgp_is q s := (fun x => (sgr q.[x] == s)).

Lemma mul3n : forall n, (3 * n = n + (n + n))%N.
Proof. by move=> n; rewrite !mulSn addn0. Qed.

Definition exp3S n : (3 ^ n.+1 = 3 ^ n + (3 ^ n + 3 ^ n))%N
  := etrans (expnS 3 n) (mul3n (3 ^ n)).

Import fintype. (* Remark : why ? *)

Lemma sg_tab_nil : forall n, sg_tab n == [::] = false.
Proof. by elim=> //= n; case: sg_tab. Qed.

Lemma size_sg_tab : forall n, size (sg_tab n) = (3 ^ n)%N.
Proof.
by elim=> [|n] // ihn; rewrite !size_cat !size_map ihn addn0 exp3S.
Qed.

Lemma cvec_rec : forall z q sq,
  cvec z (q :: sq) =
  castmx (erefl _, esym (exp3S _))
  (row_mx (cvec (filter (sgp_is q 1) z) (sq))
    (row_mx (cvec (filter (sgp_is q (-1)) z) (sq))
      (cvec (filter (sgp_is q 0) z) (sq)))).
Proof.
move=> z q sq.
apply/eqP; rewrite -(can2_eq (castmxKV _ _) (castmxK _ _)); apply/eqP.
apply/rowP=> [] i; rewrite !(mxE, castmxE, esymK, cast_ord_id) /=.
symmetry; case: splitP=> j hj /=; rewrite !mxE hj.
  case hst: sg_tab (sg_tab_nil (size sq))=> [|l st] // _.
  have sst: (size st).+1 = (3 ^ size sq)%N.
    transitivity (size (sg_tab (size sq))); first by rewrite hst //.
    by rewrite size_sg_tab.
  rewrite /croots big_filter big_mkcond !sumMz; apply: congr_big=> // x _.
  rewrite nth_cat size_map ![size (_::_)]/= sst ltn_ord.
  rewrite (nth_map [::]) /= ?sst ?ltn_ord // big_ord_recl /=.
  by rewrite sgr_cp0 sgz_cp0; case: (_ < _); first by rewrite mul1n.
case: splitP=> k hk; rewrite !mxE /= hk.
  case hst: sg_tab (sg_tab_nil (size sq))=> [|l st] // _.
  have sst: (size st).+1 = (3 ^ size sq)%N.
    transitivity (size (sg_tab (size sq))); first by rewrite hst //.
    by rewrite size_sg_tab.
  rewrite /croots big_filter big_mkcond !sumMz; apply: congr_big=> // x _.
  rewrite nth_cat nth_cat !size_map ![size (_ :: _)]/= sst ltnNge leq_addr.
  rewrite (@nth_map _ [::] _ _ [eta cons (-1)] _ (l::st)) /= ?sst addKn ltn_ord //.
  rewrite big_ord_recl /= sgr_cp0 sgz_cp0.
  by case: (_ < _); first by rewrite mul1n.
case hst: sg_tab (sg_tab_nil (size sq))=> [|l st] // _.
have sst: (size st).+1 = (3 ^ size sq)%N.
  transitivity (size (sg_tab (size sq))); first by rewrite hst //.
  by rewrite size_sg_tab.
rewrite /croots big_filter big_mkcond !sumMz; apply: congr_big=> // x _.
rewrite nth_cat nth_cat nth_cat !size_map ![size (_ :: _)]/= sst.
rewrite (@nth_map _ [::] _ _ [eta cons 0] _ (l::st)) /=; last first.
  by rewrite !addKn sst ltn_ord.
rewrite ltnNge leq_addr /= !addKn ltnNge leq_addr /= ltn_ord.
rewrite big_ord_recl /= sgr_cp0 sgz_cp0.
by case: (_ == _); first by rewrite mul1n.
Qed.

Definition ctmat n := (ctmat1 ^t n).

Lemma ctmat_unit : forall n, zmxR (ctmat n) \in unitmx.
Proof.
case=> [|n] /=; first by rewrite map_mx1 ?unitmx1//; apply: zinjR_morph.
elim:n=> [|n ihn] /=; first by  apply: ctmat1_unit.
rewrite map_mxT //.
apply: tensmx_unit=> //; last exact: ctmat1_unit.
by elim: n {ihn}=> // n ihn; rewrite muln_eq0.
Qed.

Lemma ctmat1_blocks : ctmat1 =
  (block_mx 1 (row_mx 1 1)
    (col_mx (-1) 0) (block_mx 1 1 0 1 : 'M_(1+1)%N)).
Proof.
apply/matrixP=> i j; rewrite !mxE //=.
case: splitP=> i'; rewrite !mxE ?[i']ord1=> ->.
  case: splitP=> j'; rewrite !mxE ?[j']ord1=> -> //.
  by case: splitP=> j''; rewrite !mxE [j'']ord1=> ->.
by case: splitP=> j'; rewrite !mxE ?[j']ord1=> ->;
  case: splitP=> i''; rewrite !mxE ?[i'']ord1=> -> //;
    case: splitP=> j''; rewrite !mxE ?[j'']ord1=> -> //.
Qed.


Lemma mul2n : forall n, (2 * n = n + n)%N.
Proof. by move=> n; rewrite mulSn mul1n. Qed.

Lemma tens_I3_mx : forall (R : comRingType) m n (M : 'M[R]_(m,n)), 1%:M *t M =
  castmx (esym (mul3n _ ), esym (mul3n _ )) (block_mx M 0
    0 (block_mx M 0 0 M : 'M_(m+m,n+n)%N)).
Proof.
move=> R0 m n M.
rewrite [1%:M : 'M_(1+2)%N]scalar_mx_block.
rewrite [1%:M : 'M_(1+1)%N]scalar_mx_block.
rewrite !tens_block_mx.
apply/eqP; rewrite -(can2_eq (castmxKV _ _) (castmxK _ _)); apply/eqP.
rewrite castmx_comp !tens_scalar_mx !tens0mx !scale1r.
rewrite (castmx_block (mul1n _) (mul1n _) (mul2n _) (mul2n _)).
rewrite !castmx_comp /= !castmx_id.
rewrite (castmx_block (mul1n _) (mul1n _) (mul1n _) (mul1n _)).
by rewrite !castmx_comp /= !castmx_id !castmx_const /=.
Qed.

Lemma mul_1tensmx : forall (R : comRingType) (m n p: nat)
  (e3n : (n + (n + n) = 3 * n)%N)
  (A B C : 'M[R]_(m,n))  (M : 'M[R]_(n,p)),
  castmx (erefl _, e3n) (row_mx A (row_mx B C)) *m (1%:M *t M)
    = castmx (erefl _, esym (mul3n _)) (row_mx (A *m M) (row_mx (B *m M) (C *m M))).
Proof.
move=> R0 m n p e3n A B C M.
apply/eqP; rewrite -(can2_eq (castmxKV _ _) (castmxK _ _)); apply/eqP.
rewrite tens_I3_mx mulmx_cast castmx_mul !castmx_comp /= !castmx_id /=.
by rewrite !mul_row_block /= !mulmx0 !addr0 !add0r.
Qed.

Lemma tvec_sub : forall n, (3 * (3 ^ n).-1.+1 = 3 ^ (n.+1) )%N.
Proof. by move=> n; rewrite -exp3n expnS. Qed.

Lemma tens_ctmat1_mx : forall n (M : 'M_n), ctmat1 *t M =
  castmx (esym (mul3n _ ), esym (mul3n _ )) (block_mx M (row_mx M M)
    (col_mx (-M) 0) (block_mx M M 0 M : 'M_(n+n)%N)).
Proof.
move=> n M.
rewrite ctmat1_blocks !tens_block_mx !tens_row_mx !tens_col_mx.
rewrite [-1]mx11_scalar !mxE /= !tens_scalar_mx !tens0mx scaleNr !scale1r.
apply/eqP; rewrite -(can2_eq (castmxKV _ _) (castmxK _ _)); apply/eqP.
rewrite !castmx_comp !esymK /=.
rewrite !(castmx_block (mul1n _) (mul1n _) (mul2n _) (mul2n _)).
rewrite !castmx_comp !castmx_id /=.
rewrite !(castmx_row (mul1n _) (mul1n _)).
rewrite !(castmx_block (mul1n _) (mul1n _) (mul1n _) (mul1n _)) /=.
rewrite !(castmx_col (mul1n _) (mul1n _)) !castmx_comp !castmx_id /=.
by rewrite !castmx_const.
Qed.

Lemma poly_comb_cons : forall q sq s ss,
  poly_comb (q :: sq) (s :: ss) = (q ^ (comb_exp s)) * poly_comb sq ss.
Proof. by move=> q sq s ss; rewrite /poly_comb /= big_ord_recl /=. Qed.

Lemma comb_expE : forall (R : oIdomainType),
  (comb_exp (1 : R) = 1%N) * (comb_exp (-1 : R) = 2%N) * (comb_exp (0 : R) = 0%N).
Proof. by move=> R0; rewrite /comb_exp sgzN sgz1 sgz0. Qed.

Lemma tvec_rec : forall z q sq,
  tvec z (q :: sq) =
  castmx (erefl _, esym (exp3S _)) (
    (row_mx (tvec (filter (sgp_is q 1) z) (sq))
      (row_mx (tvec (filter (sgp_is q (-1)) z) (sq))
        (tvec (filter (sgp_is q 0) z) (sq)))) *m
    (castmx (mul3n _, mul3n _) (ctmat1 *t 1%:M))).
Proof.
move=> z q sq.
rewrite tens_ctmat1_mx !castmx_comp !castmx_id /=.
rewrite !(mul_row_block, mul_row_col, mul_mx_row) !(mulmx1, mulmx0, mulmxN, addr0) /=.
apply/eqP; rewrite -(can2_eq (castmxKV _ _) (castmxK _ _)); apply/eqP.
apply/matrixP=> i j; rewrite !(castmxE, mxE) /=.
symmetry; case: splitP=> l hl; rewrite !mxE hl.
  case hst: sg_tab (sg_tab_nil (size sq))=> [|s st] // _.
  have sst: (size st).+1 = (3 ^ size sq)%N.
    transitivity (size (sg_tab (size sq))); first by rewrite hst //.
    by rewrite size_sg_tab.
  rewrite /taq !big_filter !(big_mkcond (sgp_is _ _)) -sumr_sub.
  apply: congr_big=> // x _.
  rewrite cats0 !map_cat nth_cat !size_map /= sst ltn_ord /=.
  rewrite !poly_comb_cons /= !comb_expE expr1z.
  rewrite -!(nth_map _ 0 (fun p => p.[_])) /= ?size_map ?sst ?ltn_ord //.
  rewrite -!map_comp /= horner_mul.
  set f := _ \o _; set g := _ \o _.
  set h := fun sc => q.[x] * (poly_comb sq sc).[x].
  have hg : g =1 h.
    by move=> sx; rewrite /g /h /= poly_comb_cons comb_expE expr1z horner_mul.
  rewrite -/(h _) -hg -[g _ :: _]/(map g (_ ::_)).
  rewrite (nth_map [::]) /= ?sst ?ltn_ord // hg /h sgzM.
  rewrite -![(poly_comb _ _).[_]]/(f _) -[f _ :: _]/(map f (_ ::_)).
  rewrite (nth_map [::]) /= ?sst ?ltn_ord // !sgr_cp0.
  by case: (sgzP q.[x]); rewrite ?(mul0r, mul1r, mulN1r, subr0, sub0r).
case: splitP=> k hk /=; rewrite !mxE hk.
  case hst: sg_tab (sg_tab_nil (size sq))=> [|s st] // _.
  have sst: (size st).+1 = (3 ^ size sq)%N.
    transitivity (size (sg_tab (size sq))); first by rewrite hst //.
    by rewrite size_sg_tab.
  rewrite /taq !big_filter !(big_mkcond (sgp_is _ _)) -big_split.
  apply: congr_big=> // x _.
  rewrite cats0 !map_cat !nth_cat !size_map /= sst.
  rewrite ltnNge leq_addr /= addKn ltn_ord /=.
  rewrite !poly_comb_cons /= !comb_expE.
  rewrite -!(nth_map _ 0 (fun p => p.[_])) /= ?size_map ?sst ?ltn_ord //.
  rewrite -!map_comp /= horner_mul.
  set f := _ \o _; set g := _ \o _.
  set h := fun sc => (q ^ 2).[x] * (poly_comb sq sc).[x].
  have hg : g =1 h.
    by move=> sx; rewrite /g /h /= poly_comb_cons comb_expE horner_mul.
  rewrite -/(h _) -hg -[g _ :: _]/(map g (_ ::_)).
  rewrite (nth_map [::]) /= ?sst ?ltn_ord // hg /h sgzM.
  rewrite -![(poly_comb _ _).[_]]/(f _) -[f _ :: _]/(map f (_ ::_)).
  rewrite (nth_map [::]) /= ?sst ?ltn_ord //.
  rewrite horner_mul sgzM !sgr_cp0.
  by case: (sgzP q.[x]); rewrite ?(mul0r, mul1r, mulN1r, addr0, add0r).
case hst: sg_tab (sg_tab_nil (size sq))=> [|s st] // _.
have sst: (size st).+1 = (3 ^ size sq)%N.
  transitivity (size (sg_tab (size sq))); first by rewrite hst //.
  by rewrite size_sg_tab.
rewrite /taq !big_filter !(big_mkcond (sgp_is _ _)) -!big_split.
apply: congr_big=> // x _.
rewrite cats0 !map_cat !nth_cat !size_map /= sst.
rewrite !addKn 2!ltnNge !leq_addr /=.
rewrite !poly_comb_cons /= !comb_expE expr0z mul1r.
rewrite -!(nth_map _ 0 (fun p => p.[_])) /= ?size_map ?sst ?ltn_ord //.
rewrite -!map_comp /=.
set f := _ \o _; set g := _ \o _.
have hg : g =1 f.
  by move=> sx; rewrite /g /f /= poly_comb_cons comb_expE expr0z mul1r.
rewrite -[(poly_comb _ _).[_]]/(f _) -{4}hg.
rewrite -![_ _ :: _]/(map _ (_ ::_)) (eq_map hg) !sgr_cp0.
by case: (sgzP q.[x])=> _; rewrite ?(addr0, add0r).
Qed.

Lemma tvec_cvec : forall z sq,
  tvec z sq = (cvec z sq) *m (ctmat (size sq)).
Proof.
move=> z sq; elim: sq z => [|q sq ihsq] z /=. 
  rewrite mulmx1; apply/rowP=> [] [i hi] /=; rewrite !mxE /=.
  move: hi; rewrite expn0 ltnS leqn0; move/eqP=> -> /=.
  rewrite /poly_comb big_ord0 /taq /croots /=.
  rewrite sumMz; apply: (congr_big)=> //= x _.
  by rewrite hornerC sgz1 big_ord0.
rewrite /ctmat /ntensmx /=. (* simpl in trunk is "weaker" here *)
case: sq ihsq=> /= [|q' sq] ihsq; first by apply: tvec_cvec1.
rewrite cvec_rec tensmx_decl mulmxA tvec_rec.
apply/eqP; rewrite (can2_eq (castmxK _ _) (castmxKV _ _)); apply/eqP.
rewrite !castmx_mul !castmx_id [row_mx _ _ *m _]mulmx_cast.
congr (_ *m _); last by congr (castmx (_, _) _); apply: nat_irrelevance.
rewrite /=; have->: forall n, exp3S n.+1 = mul3n (3^n.+1)%N.
  by move=> n; apply: nat_irrelevance.
by rewrite mul_1tensmx !ihsq.
Qed.

Lemma cvec_tvec : forall z sq,
  zmxR (cvec z (sq)) = (zmxR (tvec z (sq))) *m (invmx (zmxR (ctmat (size (sq))))).
Proof.
move=> z sq; apply/eqP; set A := zmxR (ctmat _).
rewrite -(@can2_eq _ _ (fun (x : 'rV_(_)) => x *m A) (fun x => x *m (invmx A))).
* by rewrite /A -map_mxM ?tvec_cvec//; apply: zinjR_morph.
* by apply: mulmxK; rewrite /A ctmat_unit.
* by apply: mulmxKV; rewrite /A ctmat_unit.
Qed.

Lemma size_sg_tab_neq0 : forall n, size (sg_tab n) != 0%N.
Proof. by move=> n; rewrite size_sg_tab exp3n. Qed.

Lemma croots_varpI : forall z sq,
  (croots z (sq) (nseq (size (sq)) 1))%:~R = (castmx (erefl _, exp3n _)
    (zmxR (tvec z (sq)) *m (invmx (zmxR (ctmat (size (sq))))))) ord0 ord0.
Proof.
move=> z sq.
rewrite -cvec_tvec castmxE /= cast_ord_id /= /cvec !mxE //= zintz.
congr ((croots _ _ _)%:~R); elim: sq=> //=  _ s -> /=.
set l := sg_tab _; suff: size l != 0%N by case: l.
exact: size_sg_tab_neq0.
Qed.

Notation taq' p a b q := (varpI a b (sremps p (p^`() * q))).

Definition tvec' p a b sq := let sg_tab := sg_tab (size sq) in
  \row_(i < 3^size sq) (taq' p a b (map (poly_comb sq) sg_tab)`_i).

Lemma tarski' : forall a b, a < b -> forall sq p,
  p^`() != 0 -> all (xpredC1 0) sq ->
  (forall j : 'I_(3 ^ size sq), all (fun p0 => p0.[a] != 0)
  (sremps p (p^`() * (map (poly_comb sq) (sg_tab (size sq)))`_j)))
  -> (forall j : 'I_(3 ^ size sq), all (fun p0 => p0.[b] != 0)
  (sremps p (p^`() * (map (poly_comb sq) (sg_tab (size sq)))`_j)))
  -> tvec (roots p a b) sq = tvec' p a b sq.
Proof.
move=> a b hab sq p np0 nq0 ha hb.
rewrite /tvec /tvec'; apply/matrixP=> i j; rewrite !mxE tarski //.
  by apply: contra np0; move/eqP->; rewrite derivE.
set q := _`_j; suff: (p^`() * q).[a] != 0.
  by apply: contra; move/eqP->; rewrite mulr0 hornerC.
case hq: (_ != _)=> //; rewrite -hq.
move: (ha j); move/allP; apply; rewrite -/q.
rewrite 2?sremps_ind ?in_cons ?eqxx 1?orbT //; last first.
  by apply: contra np0; move/eqP->; rewrite derivE.
rewrite mulf_neq0 // /q=> {q ha hb hq i np0 hab p}.
rewrite (@nth_map _ [::]); last by rewrite size_sg_tab.
case: j=> j hj.
elim: sq nq0 j hj=> /=  [|q sq ihsq].
  rewrite expn0=> _ j; rewrite ltnS leqn0; move/eqP->.
  by rewrite /poly_comb /= big_ord0 oner_eq0.
case/andP=> nq0 hsq j hj.
rewrite nth_cat size_map size_sg_tab.
case: ltnP=> cj.
  rewrite (@nth_map _ [::]) ?size_sg_tab //.
  by rewrite poly_comb_cons comb_expE expr1z mulf_neq0 // ihsq.
rewrite nth_cat size_map size_sg_tab.
case: ltnP=> cj2.
  rewrite (@nth_map _ [::]) ?size_sg_tab //.
  by rewrite poly_comb_cons comb_expE !mulf_neq0 // ihsq.
rewrite nth_cat size_map size_sg_tab.
case: ltnP=> cj3.
  rewrite (@nth_map _ [::]) ?size_sg_tab //.
  by rewrite poly_comb_cons comb_expE expr0z mul1r ihsq.
rewrite nth_default // /poly_comb.
rewrite big1 ?oner_eq0 // => i _.
by rewrite [nth _ [::] _]nth_default.
Qed.

Lemma all_prodn_gt0 : forall (I : finType) r (P : pred I) (F : I -> nat),
  (\prod_(i <- r | P i) F i > 0)%N ->
  forall i, i \in r -> P i -> (F i > 0)%N.
Proof.
move=> I r P F; elim: r => [_|a r hr] //.
rewrite big_cons; case hPa: (P a).
  rewrite muln_gt0; case/andP=> Fa0; move/hr=> hF x.
  by rewrite in_cons; case/orP; [move/eqP-> | move/hF].
move/hr=> hF x; rewrite in_cons; case/orP; last by move/hF.
by move/eqP->; rewrite hPa.
Qed.

Definition staq p a b sq i : R :=
  (taq' p a b (map (poly_comb sq) (sg_tab (size sq)))`_i)%:~R.

Definition coefs n i :=
  [seq (castmx (erefl _, exp3n _) (invmx (zmxR (ctmat n)))) i ord0 | i <- enum 'I__] `_i.

Definition prod_staq_coefs p a b sq : R :=
  let fix aux s (i : nat) := if i is i'.+1
    then aux (staq p a b sq i' * coefs (size sq) i' + s) i'
    else s in aux 0 (3 ^ size sq)%N.

Lemma prod_staq_coefsP (p : {poly R}) (a b : R) (sq : seq {poly R}) :
prod_staq_coefs p a b sq =
  (castmx (erefl _, exp3n _)
    (zmxR (tvec' p a b (sq)) *m (invmx (zmxR (ctmat (size (sq))))))) ord0 ord0.
Proof.
rewrite castmxE mxE /= /prod_staq_coefs.
transitivity (\sum_(0 <= i < 3 ^ size sq) staq p a b sq i * coefs (size sq) i).
  rewrite unlock /reducebig /= -foldr_map /= /index_iota subn0 foldr_map.
  elim: (3 ^ size sq)%N 0%R => [|n ihn] u //.
  by rewrite -[X in iota _ X]addn1 iota_add add0n /= foldr_cat ihn.
rewrite big_mkord; apply: congr_big=> // i _.
rewrite /staq /coefs /tvec' /=.
have o : 'I_(3 ^ size sq) by rewrite exp3n; apply: ord0.
rewrite (@nth_map _ o); last by rewrite size_enum_ord.
by rewrite !castmxE !cast_ord_id !mxE /= nth_ord_enum.
Qed.


Lemma ex_roots_in : forall a b, a < b -> forall p (sq : seq {poly R}), p^`() != 0 ->
  all (xpredC1 0) sq ->
  (forall j : 'I_(3 ^ size sq), all (fun p0 => ~~ root p0 a)
  (sremps p (p^`() * (map (poly_comb sq) (sg_tab (size sq)))`_j)))
  -> (forall j : 'I_(3 ^ size sq), all (fun p0 => ~~ root p0 b)
  (sremps p (p^`() * (map (poly_comb sq) (sg_tab (size sq)))`_j)))
  ->
  reflect (exists x, [&& (p.[x] == 0) ,
    (\big[andb/true]_(q <- sq) (q.[x] > 0)) & x \in`]a, b[ ])
  (prod_staq_coefs p a b sq > 0).
Proof.
move=> a b hab p sq dp0 sq0 ha hb.
rewrite prod_staq_coefsP -tarski' // -croots_varpI.
have p0 : p != 0 by apply: contra dp0; move/eqP->; rewrite derivE.
case: rootsP p0=> // p0; pose z := (roots p a b)=> hz sz _.
rewrite ltr0z ltz_nat lt0n /croots.
rewrite (big_nth 0 xpredT) big_mkord sum_nat_eq0 negb_forall.
apply: (iffP idP); last first.
  case=> x hx.
  case/and3P: hx; move/eqP=> px0.
  rewrite (big_nth 0%:P xpredT (fun q => 0 < q.[x])).
  rewrite big_mkord big_andE.
  move/forallP=> hx laxb.
  apply/existsP.
  have: exists i : 'I_(size z), z`_i = x.
    have := hz x.
    rewrite laxb rootE px0 /= eqxx; move/esym.
    move=> hxz; move: (hxz); rewrite -index_mem=> pi.
    by exists (Ordinal pi); rewrite /= nth_index.
  case=> i hi; exists i; rewrite hi.
  rewrite implyTb -lt0n prodn_gt0//.
  case=> j hj; rewrite nth_nseq/= hj lt0n.
  case hs: (_ == 1)=> //=; rewrite -hs.
  have := (hx (Ordinal hj)); rewrite implyTb /=.
  by rewrite sgz_cp0; apply.
move/existsP=> [i]; rewrite implyTb -lt0n.
move/all_prodn_gt0; move/(_ _ _ isT)=> /= hsq.
exists z`_i=> //=.
have := hz z`_i.
have ->: (z`_i \in z) by rewrite mem_nth.
case/andP=> ->; move/rootP->; rewrite eqxx /= andbT.
rewrite (big_nth 0%:P xpredT (fun q => 0 < q.[z`_i])).
rewrite big_mkord big_andE.
apply/forallP; case=> m hm; rewrite implyTb.
have := hsq (Ordinal hm)=> /=.
rewrite nth_nseq /= hm lt0n polyC0.
have ->: forall b : bool, ((b : nat) != 0%N) = b :> bool by case.
by rewrite sgz_cp0 /index_enum unlock mem_ord_enum; apply.
Qed.

(* Todo : generalize, move to polydiv, and rename root_bigmul *)
Lemma root_prod_fintype :
   forall (x : R) (I : finType) (p : I -> {poly R}),
   ~~ root (\prod_(i : I) p i) x = forallb i : I, ~~ root (p i) x.
Proof.
move=> x I p; rewrite (@big_morph _ _ (fun p => ~~ root p x) true andb).
* by rewrite big_andE.
* by move=> a b /=; rewrite root_mul negb_or.
by rewrite root1.
Qed.

(* Todo : move to polyrcf *)
Lemma cauchy_bound_ge0 : forall (p : {poly R}), 0 <= cauchy_bound p.
Proof.
move=> p; rewrite /cauchy_bound mulr_ge0 // ?invr_ge0 ?absr_ge0 //.
by rewrite sumr_ge0 // => i; rewrite absr_ge0.
Qed.

Definition ccount_weak  p (sq : seq {poly R}) : R :=
  if size p == 1%N then 0
    else if has (xpred1 0) sq then 0
      else
        let bound := (cauchy_bound (\prod_(j : 'I_(3 ^ size sq))
          (\prod_(r <- sremps p (p^`() * (map (poly_comb sq) (sg_tab (size sq)))`_j))
              r))) + 1 in
        prod_staq_coefs p (-bound) bound sq.

Lemma mem0_sremps p q : 0 \notin sremps p q.
Proof.
rewrite /sremps; move: (maxn _ _) => n; elim: n p q => [|n ihn] p q //=.
by case: ifP=> hp //=; rewrite in_cons eq_sym hp /= ihn.
Qed.

Lemma ex_roots_weak : forall p (sq : seq {poly R}), p != 0 ->
  reflect (exists x, (p.[x] == 0) && \big[andb/true]_(q <- sq) (q.[x] > 0))
    (ccount_weak p sq > 0).
Proof.
move=> p sq np0; rewrite /ccount_weak.
case: (boolP (_ == 1%N)); [rewrite size_poly_eq1|]=> hsp.
  rewrite ltrr; apply: (iffP idP)=> // [] [] x; rewrite -rootE=> /andP [].
  by rewrite (eqp_root hsp) (negPf (root1 _)).
case: (boolP (has _ _))=> hsq.
  rewrite ltrr; apply: (iffP idP)=> // [] [] x /andP [px0].
  case/hasP:hsq=> q hq /eqP q0; rewrite q0 in hq=> {q q0}.
  elim: sq hq=> // q sq ihsq.
  rewrite in_cons eq_sym big_cons=> /orP [/eqP|/ihsq hsq /andP [] //].
  by move->; rewrite horner0 ltrr.
rewrite -all_predC in hsq.
set s := \prod_(j : _) _.
have hs: s != 0.
  rewrite prodf_seq_neq0; apply/allP=> i _ /=.
  rewrite prodf_seq_neq0; apply/allP=> j /= hj.
  apply: contraL hj=> /eqP->.
  by rewrite mem0_sremps.
apply: (iffP (ex_roots_in _ _ _ _ _))=> //.
* by rewrite gt0_cp // ltr_spaddr ?ltr01 ?cauchy_bound_ge0.
* by move: np0 hsp; rewrite -!size_poly_eq0 size_deriv; case: size.
* move=> j; rewrite -root_bigmul; move: j; apply/forallP.
  rewrite -root_prod_fintype; apply/negP=> /rootP /cauchy_boundP /= /(_ hs).
  by rewrite absrN ler_absl ger_addl ler10 andbF.
* move=> j; rewrite -root_bigmul; move: j; apply/forallP.
  rewrite -root_prod_fintype; apply/negP=> /rootP /cauchy_boundP /= /(_ hs).
  by rewrite ler_absl -/s ger_addl ler10 andbF.
* by case=> x /and3P [hpx hsqx xb]; exists x; rewrite hpx.
case=> x /andP [hpx hsqx]; exists x; rewrite hpx hsqx /=.
rewrite -[_ \in _]ltr_absl addrC ltr_spaddl ?ltr01 //.
apply: cauchy_boundP=> //.
rewrite horner_prod; apply/eqP; rewrite prodf_seq_eq0; apply/hasP.
have o : 'I_(3 ^ size sq) by rewrite exp3n; apply: ord0.
exists o.
  have -> : index_enum _ = enum 'I__ by move=> n; rewrite enumT.
  by rewrite mem_enum.
rewrite horner_prod prodf_seq_eq0 /=; apply/hasP.
exists p=> //.
move: (_ * _)=> q; rewrite /sremps; case hm: (maxn _ _)=> [|n] /=.
  by move/eqP:hm; rewrite -leqn0 leq_maxl leqn0 size_poly_eq0 (negPf np0).
by rewrite (negPf np0) in_cons eqxx.
Qed.

Lemma size_prod_seq_id (R' : idomainType) (I : eqType)
  (s : seq I) (P : pred I) (F : I -> {poly R'}) :
  (forall i : I, i \in s -> P i -> F i != 0) ->
((size (\prod_(i <- s | P i) F i)%R).-1 = (\sum_(i <- s | P i) (size (F i)).-1))%N.
Proof.
elim: s=> [|i s ihs] //=; first by rewrite !big_nil size_poly1.
move=> hI; have Fi0: P i -> F i != 0 by apply: hI; rewrite in_cons eqxx.
have Fs j : j \in s -> P j -> F j != 0.
  by move=> hj; apply: hI; rewrite in_cons hj orbT.
have pFs : \prod_(j <- s | P j) F j != 0.
  by rewrite prodf_seq_neq0; apply/allP=> j hj; apply/implyP; apply: Fs.
rewrite !big_cons; case: (boolP (P _))=> pi; last by rewrite ihs.
rewrite -ihs //; rewrite size_mul_id ?(Fi0) //.
rewrite -{1}[size _]prednK ?lt0n ?size_poly_eq0 ?Fi0 // addSn /=.
move: (size _).-1 => n1.
by rewrite -{1}[size _]prednK ?lt0n ?size_poly_eq0 // addnS.
Qed.

Lemma sum_seq_nat_eq0 (I : eqType) (s : seq I) (P : pred I) (E : I -> nat) :
   (((\sum_(i <- s | P i) E i) == 0) = (all (fun i => P i ==> (E i == 0)) s))%N.
Proof. by rewrite (big_morph _ addn_eq0 (eqxx _)) big_all_cond. Qed.

Definition bounding_poly (sq : seq {poly R}) :=
  let b := cauchy_bound (\prod_(q <- sq) q) + 1 in
    ('X - (-b)%:P) * ('X - b%:P) * (\prod_(q <- sq) q)^`().

(* Lemma bounding_poly_eq0 sq : bounding_poly sq == 0 = ((\prod_(q <- sq) q)^`()) == 0. *)

(* Todo : move in polyrcf *)
Notation noroot p := (forall x, ~~ root p x).

(* Definition neighp (p : {poly R}) (x : R) : interval R :=  *)
(*   if p.[x] == 0 then `]x, x[ *)
(*     else let bnd := cauchy_bound p + 1 in *)
(*       let a := prev_root p (- bnd) x in *)
(*         let b := next_root p x bnd in *)
(*           Interval (if a == minr (- bnd) x then BInfty _ else BClose false a) *)
(*           (if b == maxr bnd x then BInfty _ else BClose false b). *)

(* Lemma noroot_neighp (p : {poly R}) (x : R) : {in neighp p x, noroot p}. *)
(* Proof. *)
(* move=> y; rewrite /neighp /=. *)
(* case: (boolP (p.[x] == 0))=> px0; first by rewrite int_xx. *)
(* case: prev_rootP px0; first by move->; rewrite horner0 eqxx. *)
(*   move=> a p0 pa0 ha hpa px0. *)
(*   case: ifP ha; first by case: minrP=> _ /eqP->; rewrite bound_in_int. *)
(*   move=> ea ha. *)
(*   case: next_rootP p0; first by move->; rewrite eqxx. *)
(*     move=> b p0 pb0 hb hpb _. *)
(*     case: ifP hb; first by case: maxrP=> _ /eqP->; rewrite bound_in_int. *)
(*     move=> eb hb. *)
(*     rewrite (@int_splitU2 _ x); last by rewrite inE /= (intP hb) (intP ha). *)
(*     by case/or3P=> [/hpa|/eqP ->|/hpb]. *)
(*   move=> b p0 -> {b}; rewrite eqxx=> hb _. *)
(*   rewrite (@int_splitU2 _ x); last by rewrite inE /= (intP ha). *)
(*   case/or3P=> [/hpa|/eqP ->|] //. *)
(*   case: (lerP (cauchy_bound p + 1) x). *)
(*     rewrite inE /= andbT=> /ler_lt_trans hbnd /hbnd. *)
(*     apply: contraL=> /rootP /(cauchy_boundP p0). *)
(*     rewrite ler_absl=> /andP [_ ybnd]. *)
(*     by rewrite -lerNgt addrC ger0_ler_add ?ler01. *)
(*   move=> xbnd. *)
(*   rewrite (@int_splitU _ (cauchy_bound p + 1) false) //=; last first. *)
(*     by rewrite inE /= xbnd. *)
(*   case/orP; first exact: hb. *)
(*   rewrite inE /= andbT; apply: contraL=> /rootP /(cauchy_boundP p0). *)
(*   rewrite ler_absl=> /andP [_ ybnd]. *)
(*   by rewrite -ltrNge addrC ltr_spaddl ?ltr01. *)
(* move=> a p0 -> {a}; rewrite eqxx=> ha px0. *)
(* case: next_rootP p0; first by move->; rewrite eqxx. *)
(*   move=> b p0 pb0 hb hpb _. *)
(*   case: ifP hb; first by case: maxrP=> _ /eqP->; rewrite bound_in_int. *)
(*   move=> eb hb. *)
(*   rewrite (@int_splitU2 _ x); last by rewrite inE /= (intP hb). *)
(*   case/or3P=> [|/eqP ->|/hpb] //. *)
(*   case: (lerP x (- (cauchy_bound p + 1))). *)
(*     rewrite inE /= => hy /ltr_le_trans /(_ hy). *)
(*     apply: contraL=> /rootP /(cauchy_boundP p0). *)
(*     rewrite ler_absl=> /andP [ybnd _]. *)
(*     by rewrite -lerNgt oppr_add addrC ler0_ler_add ?oppr_le0 ?ler01. *)
(*   move=> xbnd. *)
(*   rewrite (@int_splitU _ (- (cauchy_bound p + 1)) true) //=. *)
(*   case/orP; last exact: ha. *)
(*   rewrite inE /=; apply: contraL=> /rootP /(cauchy_boundP p0). *)
(*   rewrite ler_absl=> /andP [ybnd _]. *)
(*   by rewrite -ltrNge oppr_add addrC ltr0_ler_add ?oppr_lt0 ?ltr01. *)
(* move=> b p0 -> {b}; rewrite eqxx=> hb _ _. *)
(* admit. *)
(* Qed. *)

Let shrink (sq : seq {poly R}) :
  ((exists x, ((bounding_poly sq).[x] == 0) && \big[andb/true]_(q <- sq) (q.[x] > 0))
     <-> exists x, \big[andb/true]_(q <- sq) (q.[x] > 0)).
Proof.
split=> [] [x]; first by case/andP=> [] *; exists x.
rewrite big_all => /allP hsq.
rewrite /bounding_poly; set q := \prod_(q <- _) _; set bnd := _ + 1.
have sqn0 : {in sq, forall q, q != 0}.
  by move=> q' /= /hsq; apply: contraL=> /eqP->; rewrite horner0 ltrr.
case: (boolP (q == 0))=> [|q0].
  by rewrite prodf_seq_eq0=> /hasP [q' /= /sqn0 /negPf->].
case: (lerP x (-bnd))=> hxMbnd.
  exists (-bnd); rewrite 2!horner_mul {1}horner_factor subrr !mul0r eqxx /=.
  rewrite big_all; apply/allP=> r hr; have:= hsq r hr.
  rewrite -!sgr_cp0 => /eqP <-.
  apply/eqP; apply: (@polyrN0_int _ `](x - 1), (-bnd + 1)[).
  * move=> y hy /=; apply/negP=> /rootP ry0.
    have /(cauchy_boundP q0) : q.[y] = 0.
      apply/eqP; rewrite horner_prod prodf_seq_eq0 /=.
      by apply/hasP; exists r=> //; rewrite ry0.
    rewrite ler_absl=> /andP [hy' _]; move: hy'; apply/negP.
    by rewrite -ltrNge; move: hy; rewrite /bnd oppr_add addrNK=> /intP->.
  * rewrite inE /= -subr_gt0 oppr_sub addrCA subrr addr0 ltr01 /=.
    by rewrite ltr_spaddr ?ltr01.
  * by rewrite inE /= ltr_snaddr ?ltrN10 //= ltr_spaddr ?ltr01.
case: (lerP bnd x)=> hxPbnd.
  exists bnd; rewrite 2!horner_mul !{1}horner_factor subrr !(mulr0,mul0r) eqxx /=.
  rewrite big_all; apply/allP=> r hr; have:= hsq r hr.
  rewrite -!sgr_cp0=> /eqP <-.
  apply/eqP; apply: (@polyrN0_int _ `](bnd - 1), (x + 1)[).
  * move=> y hy /=; apply/negP=> /rootP ry0.
    have /(cauchy_boundP q0) : q.[y] = 0.
      apply/eqP; rewrite horner_prod prodf_seq_eq0 /=.
      by apply/hasP; exists r=> //; rewrite ry0.
    rewrite ler_absl=> /andP [_]; apply/negP.
    by rewrite -ltrNge; move: hy; rewrite /bnd addrK=> /intP->.
  * rewrite inE /= addrC ltr_snaddl ?oppr_lt0 ?ltr01 //=.
    by rewrite addrC ltr_spaddl ?ltr01.
  * rewrite inE /= -subr_gt0 oppr_sub addrCA subrr addr0 ltr01 /=.
    by rewrite addrC ltr_spaddl ?ltr01.
have hxM: x \in `[(- bnd), x] by rewrite bound_in_int /= ltrW.
have hxP: x \in `[x, bnd] by rewrite bound_in_int /= ltrW.
have hbndM: (- bnd) \in `[(- bnd), x] by rewrite bound_in_int /= ltrW.
have hbndP: bnd \in `[x, bnd] by rewrite bound_in_int /= ltrW.
case: (prev_rootP q (-bnd) x) q0; first by move->; rewrite eqxx.
  move=> a q0 qa0 ha hqa _.
  case: (next_rootP q x bnd) q0; first by move->; rewrite eqxx.
    move=> b q0 qb0 hb hqb _.
    have hx: x \in `]a, b[  by rewrite inE /= (intP ha) (intP hb).
    case: (@rolle _ a b q).
    * by rewrite (intP hx).
    * by rewrite qa0 qb0.
    move=> y hy q'y0; exists y; rewrite horner_lin q'y0 !mulr0 eqxx /=.
    rewrite big_all; apply/allP=> r rsq; have:= hsq r rsq.
    rewrite -!sgr_cp0=> /eqP <-.
    apply/eqP; apply: (@polyrN0_int _ `]a, b[)=> //.
    move=> z /=; rewrite (@int_splitU2 _ x) // => /or3P [|/eqP->|].
    * move/hqa; apply: contra; rewrite !rootE horner_prod=> rz.
      by rewrite prodf_seq_eq0 /=; apply/hasP; exists r.
    * by move/hsq:rsq; apply: contraL=> /rootP->; rewrite ltrr.
    move/hqb; apply: contra; rewrite !rootE horner_prod=> rz.
    by rewrite prodf_seq_eq0 /=; apply/hasP; exists r.
  move=> b q0 _ {b} hqb _; exists bnd.
  rewrite 2!horner_mul !{1}horner_factor subrr !(mul0r,mulr0) eqxx /=.
  rewrite big_all; apply/allP=> r hr.
  have:= hsq r hr; rewrite -!sgr_cp0; congr (_ == 1).
  apply: (@polyrN0_int _ `[x, bnd]) => //= y.
  rewrite (@int_splitU _ bnd false) // int_xx /=.
  case/orP=> [|/eqP ->]; last first.
    suff: ~~ root q bnd.
      apply: contra=> r0; rewrite /root horner_prod prodf_seq_eq0 /=.
      by apply/hasP; exists r.
    apply/negP=> /rootP /(cauchy_boundP q0).
    rewrite /bnd ler_absl=> /andP [_].
    by rewrite -subr_ge0 oppr_add addrA subrr sub0r lerNgt oppr_lt0 ltr01.
  rewrite (@int_splitU _ x true) // ?bound_in_int // int_xx /=.
  case/orP=> [/eqP ->|/hqb] //.
    by move/hsq:hr; apply: contraTneq=> ->; rewrite ltrr.
  apply: contra=> r0; rewrite /root horner_prod prodf_seq_eq0 /=.
  by apply/hasP; exists r.
move=> a q0 _ {a} hqa _; exists (-bnd).
rewrite 2!horner_mul {1}horner_factor subrr !mul0r eqxx /=.
rewrite big_all; apply/allP=> r hr.
have:= hsq r hr; rewrite -!sgr_cp0; congr (_ == 1).
apply: (@polyrN0_int _ `[(- bnd), x]) => //= y.
rewrite (@int_splitU _ (- bnd) true) // int_xx /= inE /=.
case/orP=> [/eqP ->|].
  suff: ~~ root q (- bnd).
    apply: contra=> r0; rewrite /root horner_prod prodf_seq_eq0 /=.
    by apply/hasP; exists r.
  apply/negP=> /rootP /(cauchy_boundP q0).
  rewrite /bnd absrN ler_absl=> /andP [_].
  by rewrite -subr_ge0 oppr_add addrA subrr sub0r lerNgt oppr_lt0 ltr01.
rewrite (@int_splitU _ x false) // ?bound_in_int // int_xx /=.
case/orP=> [/hqa|/eqP ->] //.
  apply: contra=> r0; rewrite /root horner_prod prodf_seq_eq0 /=.
  by apply/hasP; exists r.
by move/hsq:hr; apply: contraTneq=> ->; rewrite ltrr.
Qed.

Definition ccount (sp sq : seq {poly R}) :=
  let p := \big[@gcdp _/0%R]_(p <- sp) p in
    ccount_weak (if p != 0 then p else
        let bq := bounding_poly sq in
    if bq != 0 then bq else 'X) sq.

Lemma ex_roots (sp sq : seq {poly R}) :
  reflect (exists x, \big[andb/true]_(p <- sp) (p.[x] == 0)
                  && \big[andb/true]_(q <- sq) (q.[x] > 0))
    (ccount sp sq > 0).
Proof.
rewrite /ccount.
case: (boolP (_ == 0))=> hsp /=.
  move: hsp; rewrite (big_morph  _ (@gcdp_eq0 _) (eqxx _)).
  rewrite big_all => /allP /= hsp.
  case: (boolP (_ == 0))=> bq0 /=.
    apply: (iffP (ex_roots_weak _ _)).
    * by rewrite -size_poly_eq0 size_polyX.
    * case=> x; rewrite hornerX=> /andP [/eqP hx].
      rewrite hx; exists x; rewrite hx b andbT.
      rewrite big_all; apply/allP=> /= p hp.
      by rewrite (eqP (hsp _ hp)) horner0.
    case=> x; rewrite !big_all => /andP[/allP hspx /allP hsq].
    exists 0; rewrite hornerX eqxx /=.
    move: bq0; rewrite !mulf_eq0 !{1}factor_eq0 /=.
    rewrite -size_poly_eq0 size_deriv -leqn0.
    rewrite size_prod_seq_id; last first.
      by move=> i /hsq hi _; apply: contraTneq hi=> ->; rewrite horner0 ltrr.
    rewrite leqn0 sum_seq_nat_eq0 /= => /allP ssq.
    rewrite big_all; apply/allP=> q hq /=.
    move: (ssq _ hq) (hsq _ hq); rewrite -subn1 subn_eq0 => /size1_polyC->.
    by rewrite !hornerC.
  apply: (iffP (ex_roots_weak _ _))=> //; last first.
    by case=> x /andP [_ hsq]; apply/shrink=> //; exists x.
  case/shrink=> x hx; exists x; rewrite hx andbT.
  by rewrite big_all; apply/allP=> y /hsp /eqP ->; rewrite horner0.
by apply: (iffP (ex_roots_weak _ _))=> [] // [x hx];
exists x; move: hx; rewrite [_ == _]root_biggcd !big_all.
Qed.


End QeRcfTh.
