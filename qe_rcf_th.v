Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype path.
Require Import bigop ssralg poly polydiv orderedalg zmodp div zint.
Require Import polyorder polyrcf interval matrix mxtens perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory ORing.Theory RPdiv ComRing.

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
by move=> /rdvdp_leq // /(_ p0); rewrite size_factor esp sp0.
Qed.

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
        else p::(sremps_rec q ((-(lead_coef q ^+ rscalp p q)) *: (rmodp p q)) m)
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

(* :TODO: backport to polydiv *)
Lemma lc_expn_rscalp_neq0 (p q : {poly R}): lead_coef q ^+ rscalp p q != 0.
Proof.
case: (eqVneq q 0) => [->|nzq]; last by rewrite expf_neq0 ?lead_coef_eq0.
by rewrite /rscalp /redivp /= eqxx /= expr0 nonzero1r.
Qed.

Notation lcn_neq0 := lc_expn_rscalp_neq0.

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
  by rewrite size_scaler ?oppr_eq0 ?lcn_neq0 // ltn_rmodp ?q0.
by move: (leq_trans sqp spn).
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
rewrite sremps_recP_subproof //.
rewrite size_scaler ?oppr_eq0 ?lcn_neq0 // ltn_rmodp //.
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
exists ('X - x%:P); rewrite  -size_poly_eq1 size_factor andbT.
by rewrite dvdp_gcd !dvdpE hp hq.
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
have yln: yl \in neighpl p a x by rewrite !inE; apply/andP.
have yrn: yr \in neighpr p x b by rewrite !inE; apply/andP.
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
Lemma mu_mod : forall p q x, (\mu_x p < \mu_x q)%N ->
 \mu_x (rmodp p q) =  \mu_x p.
Proof.
move=> p q x mupq; case p0: (p == 0).
  by rewrite (eqP p0) rmod0p.
have qn0 : q != 0.
  by apply/negP; move/eqP=> q0; rewrite q0  mu0 ltn0 in mupq.
move/eqP: (rdivp_eq q p).
rewrite eq_sym (can2_eq (addKr _ ) (addNKr _)); move/eqP->.
case qpq0: ((rdivp p q) == 0).
  by rewrite (eqP qpq0) mul0r oppr0 add0r mu_mulC // ?lcn_neq0.
rewrite mu_addl ?mu_mulC ?scaler_eq0 ?negb_or ?p0 ?lcn_neq0 //.
rewrite mu_opp mu_mul.
  by rewrite (leq_trans mupq) // leq_addl.
by rewrite mulf_neq0 // qpq0.
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
  (\mu_x q <= \mu_x (rmodp p q)%R)%N.
Proof.
move=> p q x; rewrite dvdpE /rdvdp=> rn0 mupq.
case q0: (q == 0); first by rewrite (eqP q0) mu0 leq0n.
move/eqP: (rdivp_eq q p).
rewrite eq_sym (can2_eq (addKr _ ) (addNKr _)); move/eqP=> hr.
rewrite hr; case qpq0: (rdivp p q == 0).
  by rewrite (eqP qpq0) mul0r oppr0 add0r mu_mulC // lcn_neq0.
rewrite  (leq_trans _ (mu_add _ _)) // -?hr //.
rewrite leq_minr mu_opp mu_mul ?mulf_neq0 ?qpq0 ?q0 // leq_addl.
by rewrite mu_mulC // lcn_neq0.
Qed.

(* Lemma sgp_right0 : forall (x : R), sgp_right 0 x = 0. *)
(* Proof. by move=> x; rewrite /sgp_right size_poly0. Qed. *)

Lemma sgp_right_mod : forall p q x, (\mu_x p < \mu_x q)%N ->
  sgp_right (rmodp p q) x = (sgr (lead_coef q)) ^+ (rscalp p q) * sgp_right p x.
Proof.
move=> p q x mupq; case p0: (p == 0).
  by rewrite (eqP p0) rmod0p !sgp_right0 mulr0.
have qn0 : q != 0.
  by apply/negP; move/eqP=> q0; rewrite q0  mu0 ltn0 in mupq.
move/eqP: (rdivp_eq q p).
rewrite eq_sym (can2_eq (addKr _ ) (addNKr _)); move/eqP->.
case qpq0: ((rdivp p q) == 0).
  by rewrite (eqP qpq0) mul0r oppr0 add0r sgp_right_scale // sgrX.
rewrite sgp_right_addp0 ?sgp_right_scale ?sgrX //.
  by rewrite scaler_eq0 negb_or p0 lcn_neq0.
rewrite mu_mulC ?lcn_neq0 // mu_opp mu_mul ?mulf_neq0 ?qpq0 //.
by rewrite ltn_addl.
Qed.


(* Todo : system to solve neighbordhood dependency automatically *)
Lemma jump_mod : forall p q, forall x,
  jump p q x = sgz (lead_coef q) ^+ (rscalp p q) * jump (rmodp p q) q x.
Proof.
move=> p q x.
case p0: (p == 0); first by rewrite (eqP p0) rmod0p jump0p mulr0.
case q0: (q == 0); first by rewrite (eqP q0) rmodp0 jumppc mulr0.
rewrite -sgzX; set s := sgz _.
apply: (@mulfI _ s); first by rewrite /s sgz_eq0 lcn_neq0.
rewrite mulrA mulz_sg lcn_neq0 mul1r -jump_mulCp rdivp_eq.
have [->|rpq_eq0] := altP (rmodp p q =P 0).
  by rewrite addr0 jump0p -[X in jump _ X]mul1r jump_mul2r ?q0 // jumppc.
rewrite /jump. set r := _ * q + _.
have muxp : \mu_x p = \mu_x r by rewrite /r -rdivp_eq mu_mulC ?lcn_neq0.
have r_neq0 : r != 0 by rewrite /r -rdivp_eq scaler_eq0 p0 orbF lcn_neq0.
have [hpq|hpq] := leqP (\mu_x q) (\mu_x r).
  rewrite 2!(_ : _ - _ = 0)%N ?andbF //; apply/eqP; rewrite -/(_ <= _)%N //.
  by rewrite mu_mod_leq ?dvdpE // muxp.
rewrite mu_mod ?muxp // rpq_eq0 (negPf r_neq0); congr (_ ^+ _ *+ _).
rewrite !sgp_right_mul sgp_right_mod ?muxp // /r -rdivp_eq.
by rewrite -mul_polyC sgp_right_mul sgp_rightc sgrX.
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
move/coprimepP:cgq rqx rgx=> cgq; rewrite -!dvdpE=> /cgq hgq /hgq.
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
   cind a b p q = (sgz (lead_coef q) ^+ rscalp p q) * cind a b (rmodp p q) q.
Proof.
move=> a b hab p q; rewrite /cind big_distrr.
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
  apply: (@sjump_neigh a' b); rewrite ?mulf_neq0// !inE ?midf_lte//=.
    by rewrite /prev_root pq0 (eqP hax) /= minr_l ?(ltrW ax) // !midf_lte.
  by rewrite /next_root pq0 (eqP hs) /= maxr_l ?(ltrW xs) // !midf_lte.
rewrite !big_cons mul0r ltrr mulr0 add0r; congr (_+_).
move: hs; rewrite roots_cons; case/and5P=> _.
case/andP=> xy ys hxy pqy0 hs.
apply: (@sjump_neigh a' y); rewrite ?mulf_neq0// !inE ?midf_lte//=.
  by rewrite /prev_root pq0 (eqP hax) /= minr_l ?(ltrW ax) // !midf_lte.
by rewrite /next_root pq0 (eqP hxy) /= maxr_l ?(ltrW xy) // !midf_lte.
Qed.

(* :TODO: backport to polydiv *)
Lemma coprimep_rdiv_gcd p q : (p != 0) || (q != 0) ->
  coprimep (rdivp p (gcdp p q)) (rdivp q (gcdp p q)).
Proof.
move=> hpq.
have gpq0: gcdp p q != 0 by rewrite gcdp_eq0 negb_and.
rewrite -gcdp_eqp1 -(@eqp_mul2r _ (gcdp p q)) // mul1r.
have: gcdp p q %| p by rewrite dvdp_gcdl.
have: gcdp p q %| q by rewrite dvdp_gcdr.
rewrite !dvdpE !rdvdp_eq eq_sym; move/eqP=> hq; rewrite eq_sym; move/eqP=> hp.
rewrite (eqp_ltrans (mulp_gcdl _ _ _)) hq hp.
have lcn0 k : (lead_coef (gcdp p q)) ^+ k != 0.
  by rewrite expf_neq0 ?lead_coef_eq0.
by apply: eqp_gcd; rewrite ?eqp_scale.
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
  rewrite !dvdpE !rdvdp_eq -!mul_polyC.
  set gpq := gcdp p q; set qp := (rdivp p _);  set qq := (rdivp q _).
  move=> /eqP /(canRL (mulKr _)).
  rewrite poly_unitE size_polyC lcn_neq0 andTb coefC /= unitfE lcn_neq0.
  rewrite poly_invE.
  rewrite poly_unitE size_polyC lcn_neq0 andTb coefC /= unitfE lcn_neq0.
  rewrite [(_ ^- _)%:P * _]mul_polyC scaler_mull=> /(_ isT); set sq := _ ^-1 => hq.
  move=> /eqP /(canRL (mulKr _)).
  rewrite poly_unitE size_polyC lcn_neq0 andTb coefC /= unitfE lcn_neq0.
  rewrite poly_invE.
  rewrite poly_unitE size_polyC lcn_neq0 andTb coefC /= unitfE lcn_neq0.
  rewrite mul_polyC scaler_mull=> /(_ isT); set sp := _ ^-1 => hp.
  move: (p0); rewrite hp !(mulf_eq0, scaler_eq0, negb_or) -andbA.
  case/and3P=> sp0 qp0 gpq0.
  move: (q0); rewrite hq !(mulf_eq0, scaler_eq0, negb_or) -andbA.
  case/and3P=> sq0 qq0 _.
  move: (hpqa) (hpqb).
  rewrite hp hq.
  have csqpqq: coprimep (sp *: qp) (sq *: qq).
    (* Todo : eqp_coprimel *)
    rewrite coprimep_def.
    rewrite (eqp_size (eqp_gcdr _ (eqp_scale _ _))) //.
    rewrite (eqp_size (eqp_gcdl _ (eqp_scale _ _))) //.
    rewrite -coprimep_def.
    by rewrite coprimep_rdiv_gcd ?p0.
  rewrite !{1}cind_mul2r // ?(mulf_neq0, scaler_eq0, negb_or, sp0, sq0) //.
  rewrite !rootE.
  rewrite !{1}horner_mul.
  rewrite !{1}horner_scaler.
  rewrite !sgzM /=.
  rewrite !mulf_eq0 !negb_or -!andbA.
  case/andP=> hsp; case/and5P=> qpa gpqa hsq qqa _.
  case/andP=> _; case/and5P=> qpb gpqb _ qqb _.
  rewrite hc ?rootE ?{1}horner_mul ?{1}horner_scaler;
    do ?by rewrite ?sgrM ?(mulf_neq0, scaler_eq0, negb_or, sp0, sq0) //=.
  rewrite -!sgr_cp0 !sgrM.
  have hss (R' : oIdomainType) s s' s'' (c : R') : c != 0 ->
    (s * sgr c) * s' * s'' * sgr c = s * s' * s''.
    by move=> nc0; rewrite ![_ * sgr _]mulrC !mulrA mulr_sg nc0 mul1r.
  have hss' (R' : oIdomainType) s s' s'' (c : R') : c != 0 ->
    (s * sgz c) * s' * s'' * sgz c = s * s' * s''.
    by move=> nc0; rewrite ![_ * sgz _]mulrC !mulrA mulz_sg nc0 mul1r.
  by rewrite !(hss, hss', mulrA) // !sgzM.
have pq0 : p * q == 0 = false by apply: negbTE; rewrite mulf_neq0.
rewrite cind_seq_mids//.
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
  sremps p q = p :: (sremps q ((- lead_coef q ^+ rscalp p q) *: (rmodp p q))).
Proof.
move=> p q np0; rewrite {1}/sremps /=.
case hsp: (size p)=> [|sp] /=.
  by move/eqP: hsp np0; rewrite size_poly_eq0; move/eqP->; rewrite eqxx.
rewrite maxnSS /= (negPf np0); congr cons.
case q0: (q == 0); first by rewrite /sremps (eqP q0) !sremps_recp0.
rewrite sremps_recW // maxnl; first by rewrite !leq_maxr leqnn orbT.
by rewrite size_scaler ?oppr_eq0 ?lcn_neq0 ?ltn_rmodp ?q0.
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
have hmqr: (maxn (size q) (size ((- lead_coef q ^+ rscalp p q) *: (rmodp p q))%R).+1 <= m)%N.
  rewrite size_scaler ?oppr_eq0 ?lcn_neq0 //.
  case: (ltnP (size p) (size q).+1) hm=> hpq.
    move/ltnW: hpq; move/maxnr=> hpq; rewrite hpq => [[hm]].
    by rewrite hm leq_maxl leqnn/= -hm ltn_rmodp ?q0.
  move/maxnl: (hpq)=> hmpq; rewrite hmpq=> hm.
  by move: hpq; rewrite maxnl ?ltn_rmodp ?q0// hm ltnS.
rewrite sremps_recW// in es.
have m0 x : 0 = (0 : {poly R}).[a] by rewrite hornerC.
rewrite !PoszD addrAC oppr_add -!addrA addrA [- _ + _]addrC.
rewrite -[(varp _ _)%:Z - _]/(varpI _ _ _).
rewrite {3}sremps_recW//.
case: m hm es {hmqr} => [|m hm es] //=.
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
case r0: (rmodp p q == 0).
  move: (r0); rewrite [_ == _]rdvdp_eq; move/eqP=> hr.
  have: cind a b (rdivp p q * q) q = 0.
    rewrite -{3}[q]mul1r cind_mul2r ?cindpc ?oner_eq0 ?coprimep1 //.
    move/eqP: hr; apply: contraL; move/eqP->; rewrite mul0r.
      by rewrite scaler_eq0 negb_or lcn_neq0.
  rewrite -hr cind_mulCp//; move/eqP; rewrite mulf_eq0 sgz_cp0.
  rewrite (negPf (lcn_neq0 _ _))/=.
  move/eqP->; rewrite (eqP r0) addr0.
  rewrite /sremps; case hmn: (maxn _ _)=> [|mn] /=.
    by rewrite /varpI /varp /= subr0.
  by rewrite q0 scaler0 sremps_recp0 /varpI /varp /= !mulr0 ltrr subrr subr0.
move: allra0 allrb0.
rewrite sremps_ind // ?(scaler_eq0, oppr_eq0, negb_or, lcn_neq0, r0) //=.
rewrite !rootE !horner_lin !mulf_eq0 !oppr_eq0 !negb_or !lcn_neq0 !andTb.
case/andP=> rpqa allra0; case/andP=> rpqb allrb0.
rewrite hs // ?rootE ?{1}horner_lin
  ?(mulf_neq0, scaler_eq0, negb_or, oppr_eq0, r0, lcn_neq0) //.
rewrite cind_mulCp ?r0 //.
by rewrite sgzN mulNr opprK sgzX -cind_mod.
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
Proof.
move=> n; rewrite size_sg_tab.
by rewrite exp3n.
Qed.

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


Lemma lead_coef_scale p r : lead_coef (r *: p) = r * (lead_coef p).
Proof.
case: (r =P 0); first by move->; rewrite scale0r mul0r lead_coef0.
by move/eqP=> rn0; rewrite /lead_coef coefZ size_scaler.
Qed.

Lemma lead_coef_addr p q :
  (size q > size p)%N -> lead_coef (p + q) = lead_coef q.
Proof. by move/lead_coef_addl<-; rewrite addrC. Qed.

Lemma leq1_size_polyC (c : R) : (size c%:P <= 1)%N.
Proof. by rewrite size_polyC; case: (c == 0). Qed.

Lemma my_size_exp_id p n : p != 0 ->
       (size (p ^+ n)) = ((size p).-1 * n).+1%N.
Proof.
by move=> hp; rewrite -size_exp_id prednK // lt0n size_poly_eq0 expf_neq0.
Qed.

(* this is too long ..*)
Lemma lead_coef_comp_poly p q : (size q > 1)%N ->
  lead_coef (p \Po q) = (lead_coef p) * (lead_coef q)^+(size p).-1.
Proof.
move=> sq.
rewrite comp_polyE; elim: {2}(size p) (leqnn (size p)) q sq => [|n ihn hsp q sq].
  rewrite leqn0 size_poly_eq0; move/eqP=> -> q; rewrite size_poly0 big_ord0.
  by rewrite lead_coef0 mul0r.
move: hsp; rewrite leq_eqVlt ltnS; case/orP; last by move/ihn=> ->.
move/eqP=> hs; rewrite hs big_ord_recr /= {ihn}.
case: n hs => [|n hs].
  rewrite big_ord0 add0r lead_coef_scale !expr0; move/eqP; case/size1P=> c _ ->.
  by rewrite !lead_coefC !mulr1 coefC eqxx.
rewrite lead_coef_addr.
  by rewrite lead_coef_scale /(lead_coef p)  hs /= lead_coef_exp_id.
apply: leq_ltn_trans (size_sum _ _ _) _.
have qn0 : q != 0 by rewrite -size_poly_eq0 -lt0n; apply: leq_trans sq.
have lcp : p`_n.+1 != 0.
  by rewrite -[n.+1]/(n.+2.-1) -hs -/(lead_coef p) lead_coef_eq0 -size_poly_eq0 hs.
have h: (\max_(i < n.+1) size (p`_i *: q ^+ i) <= size (q ^+ n))%N.
  apply/bigmax_leqP=> [[i hi]] _; case: (p`_i =P 0).
    by move->; rewrite scale0r size_poly0.
  move=> pn0; rewrite size_scaler; last by move/eqP: pn0.
  by rewrite !my_size_exp_id //= ltnS leq_mul2l -ltnS hi orbT.
apply: leq_ltn_trans h _; rewrite size_scaler ?my_size_exp_id //.
by rewrite ltnS ltn_mul2l ltnS; case: (size q) sq => [|m] //; case: m => [|m] //=.
Qed.

Lemma gt_size_poly p n : (size p > n)%N -> p != 0.
Proof.
by move=> h; rewrite -size_poly_eq0 lt0n_neq0 //; apply: leq_ltn_trans h.
Qed.

Definition to_even n : nat := ((odd n) + n)%N.

Lemma even_to_even n : ~~ odd (to_even n).
Proof. by rewrite /to_even; case hn: (odd n); rewrite /= hn. Qed.

Definition change_varp (p : {poly R}) :=
  'X^(size p).-1 +
  \poly_(i < (size p).-1) (lead_coef p ^+ (size p - i.+2) * p`_i).

Lemma change_varpP p x : (1 < size p)%N ->
  (change_varp p).[lead_coef p * x] = lead_coef p ^+ (size p).-2 * p.[x].
Proof.
move=> sp_gt1; have p_neq0 : p != 0.
   by rewrite -size_poly_gt0 (ltn_trans _ sp_gt1).
rewrite horner_add horner_exp hornerX horner_poly.
rewrite horner_coef polySpred //= big_ord_recr /= -lead_coefE.
rewrite mulr_addr mulrA -exprSr [RHS]addrC; congr (_ + _).
  by rewrite prednK ?exprn_mull // -subn1 subn_gt0.
rewrite -mulr_sumr; apply: eq_big=> // i _.
rewrite subSS exprn_mull mulrCA -mulrA mulrA -exprn_addr.
by rewrite addn_subA // addnC -predn_sub addnK.
Qed.

Lemma size_change_varp p : p != 0 -> size (change_varp p) = size p.
Proof.
move=> p_neq0; rewrite /change_varp size_addl ?size_polyXn -?polySpred //.
by rewrite (leq_ltn_trans (size_poly _ _)) // -polySpred.
Qed.

Lemma monic_change_varp p : monic (change_varp p).
Proof.
rewrite /change_varp /monic lead_coef_addl ?lead_coefXn //.
by rewrite size_polyXn (leq_ltn_trans (size_poly _ _)).
Qed.

Definition change_varq a (q : {poly R}) :=
  \poly_(i < size q) (a ^+ (to_even (size q) - i) * q`_i).

Lemma change_varqP a (q : {poly R}) x :
  (change_varq a q).[a * x] = a ^+ (to_even (size q)) * q.[x].
Proof.
rewrite horner_poly horner_coef -mulr_sumr; apply: eq_big=> // i _.
rewrite exprn_mull mulrCA -mulrA mulrA -exprn_addr.
by rewrite subnKC // (leq_trans _ (leq_addl _ _)) // ltnW.
Qed.

Lemma size_change_varq a q : a != 0 -> size (change_varq a q) = size q.
Proof.
move=> a_neq0; have [->|q_neq0] := eqVneq q 0.
  by rewrite /change_varq size_poly0; unlock poly; rewrite /= size_poly0.
rewrite /change_varq size_poly_eq // -lead_coefE.
by rewrite mulf_eq0 negb_or lead_coef_eq0 q_neq0 andbT expf_neq0.
Qed.

Lemma change_varq_eq0 a q : a != 0 -> (change_varq a q) == 0 = (q == 0).
Proof.
by move=> a_neq0; rewrite -size_poly_eq0 size_change_varq // size_poly_eq0.
Qed.

Lemma change_varp_eq0 p : change_varp p == 0 = false.
Proof. by rewrite (negPf (monic_neq0 _)) // monic_change_varp. Qed.

Definition to_monic (p : {poly R})(sq : seq {poly R}) :=
  let a := lead_coef p in (change_varp p, map (change_varq a) sq).

(* polyX or X suffix in poly ? *)
Lemma monic_to_monic p sq : (size p > 1)%N -> monic (to_monic p sq).1.
Proof. by move=> hsp /=; apply: monic_change_varp. Qed.

Lemma has_root_size_gt1 (a : R) (p : {poly R}) :
  (p != 0)%B -> root p a -> (1 < size p)%N.
Proof.
move=> p_neq0 rootpa.
rewrite ltnNge leq_eqVlt ltnS leqn0 size_poly_eq0 (negPf p_neq0) orbF.
by apply: contraL rootpa=> /size1P [c c_neq0 ->]; rewrite rootE hornerC.
Qed.

Lemma to_monicP p sq : p != 0 ->
  let psq' := to_monic p sq in
  (exists x, (((psq'.1).[x] == 0) && \big[andb/true]_(q <- psq'.2) (q.[x] > 0)))
  <-> exists x, ((p.[x] == 0) && \big[andb/true]_(q <- sq) (q.[x] > 0)).
Proof.
move=> sp /=; set a := lead_coef _.
have a_neq0 : a != 0 by rewrite lead_coef_eq0.
have hsub : forall x,
  ((change_varp p).[a * x] == 0) &&
      \big[andb/true]_(q <- map (change_varq a) sq) (0 < q.[a * x]) =
   ((p.[x] == 0) && \big[andb/true]_(q <- sq) (0 < q.[x])).
  move=> x.
  have [] := ltngtP (size p) 1; first 2 last.
  + move=> /eqP sp_eq1; move: (sp_eq1); rewrite -size_change_varp=> // scp_eq1.
    case/size1P: scp_eq1=> c c_neq0 ->; case/size1P: sp_eq1=> c' c'_neq0 ->.
    by rewrite !hornerC (negPf c_neq0) (negPf c'_neq0).
  + by rewrite ltnS leqn0 size_poly_eq0 (negPf sp).
  + move=> sp_gt1; rewrite change_varpP //.
    rewrite mulf_eq0 expf_eq0 (negPf a_neq0) andbF /=; congr andb.
    rewrite big_map; apply: eq_big=> // i _.
    rewrite change_varqP pmulr_rgt0 //.
    rewrite ltr_neqAle expf_eq0 (negPf a_neq0) andbF /=.
    by rewrite exprn_even_ge0 // even_to_even.
split => [] [] x hx; last by exists (a * x); rewrite hsub.
by exists (a ^-1 * x); rewrite -hsub !mulVKf.
Qed.


Definition maj_not_root (x : R)(p : {poly R}) :=
     x + (odflt ord0 [pick i : 'I_(size p).+1 |
              (~~root p (x + i.+1%:R))]).+1%:R.

(*assia : that one is missing  in fintype *)
Lemma size_ord_enum n : size (ord_enum n) = n.
Proof. by rewrite -{3}(size_iota 0 n) -val_ord_enum size_map. Qed.

(* Lemmas in poly implemented with predn are impossible to use *)
Lemma my_size_comp_poly_id p q : p != 0 -> (size q > 1)%N ->
  (size (p \Po q)) = ((size p).-1 * (size q).-1).+1%N.
Proof.
move=> nz_p nc_q.
have nz_q: q != 0 by rewrite -size_poly_eq0 -(subnKC nc_q).
rewrite mulnC comp_polyE (polySpred nz_p) /= big_ord_recr Monoid.mulmC.
rewrite size_addl size_scaler ?lead_coef_eq0 ?my_size_exp_id //=.
rewrite ltnS.
rewrite (leq_trans (size_sum _ _ _)) //; apply/bigmax_leqP => i _.
rewrite (leq_trans (size_poly _ _)) // polySpred ?expf_neq0 // size_exp_id.
by rewrite -(subnKC nc_q) ltn_pmul2l.
Qed.

(* assia : pnatr_eq should be provided in ssralg and name is bad *)
(* the proof is really too long *)
Lemma too_many_roots_eq0 x p :
(forall i : 'I_(size p).+1, root p (x + i.+1%:R)) -> p = 0.
Proof.
move=> h; case: (altP (p =P 0)) => //; move/max_poly_roots => habs.
pose s :=
  (map ((+%R x) \o (fun x : 'I_(size p).+1 => x.+1%:R)) (ord_enum (size p).+1)).
have sroots : all (root p) s by apply/allP=> xi; case/mapP=> i hi ->; apply: h.
have : uniq s.
  rewrite map_inj_uniq ?ord_enum_uniq //; apply: inj_comp; first exact: addrI.
   move=> i j /= /eqP; case: (leqP i j) => hij.
    rewrite eq_sym -subr_eq0 -natr_sub // pnatr_eq0 subn_eq0 => hij'.
    by apply/val_inj => /=; apply/eqP; rewrite eqn_leq hij.
  rewrite -subr_eq0 -natr_sub  1?ltnW // pnatr_eq0 subn_eq0 => hij'.
  by apply/val_inj => /=; apply/eqP; rewrite eqn_leq (ltnW hij) andbT.
by move/(habs _ sroots); rewrite size_map /= size_ord_enum ltnNge leqnSn.
Qed.

Lemma maj_not_root_lt x p : x < maj_not_root x p.
Proof. by rewrite /maj_not_root ltr_addl // ltr0Sn. Qed.

Lemma maj_not_root_lt0 x p : 0 <= x -> 0 < maj_not_root x p.
Proof. by move=> /ler_lt_trans -> //; apply: maj_not_root_lt. Qed.

Let size_aux p : p != 0 -> size (p \Po (- 'X)) = size p.
Proof.
move=> pn0.
rewrite  my_size_comp_poly_id // ?size_opp ?size_polyX //= muln1 prednK //.
by rewrite lt0n size_poly_eq0.
Qed.

Lemma maj_not_rootP x p : p != 0 -> ~~ (root p (maj_not_root x p)).
Proof.
move=> pn0; rewrite /maj_not_root.
case: pickP=> [y hy | habs] //=.
  suff : p = 0 by move/eqP; rewrite (negPf pn0).
by apply: (@too_many_roots_eq0 x) => i; move/negbT: (habs i); rewrite negbK.
Qed.

Definition pick_right x p := maj_not_root x ((p \Po (- 'X)) * p).

Lemma pick_right_lt x p : x < pick_right x p.
Proof. rewrite /pick_right; exact: maj_not_root_lt. Qed.

Lemma pick_right_lt0 x p : 0 <= x -> 0 < pick_right x p.
Proof. by move=> /ler_lt_trans -> //; apply: maj_not_root_lt. Qed.

Lemma pick_rightP x p : p != 0 -> ~~ root p (pick_right x p).
Proof.
move=> pn0; rewrite /pick_right.
have ppn0 : (p \Po - 'X) * p != 0.
  by rewrite mulf_eq0 // negb_or -size_poly_eq0 size_aux // size_poly_eq0 andbb.
by have := (maj_not_rootP x ppn0); rewrite root_mul negb_or; case/andP.
Qed.

Lemma pick_rightPop x p : p != 0 ->  ~~ root p (-(pick_right x p)).
Proof.
move=> pn0; rewrite /pick_right.
have ppn0 : (p \Po - 'X) * p != 0.
  by rewrite mulf_eq0 // negb_or -size_poly_eq0 size_aux // size_poly_eq0 andbb.
have := (maj_not_rootP x ppn0); rewrite root_mul negb_or /root !horner_comp_poly.
by rewrite !horner_opp !hornerX; case/andP.
Qed.

Definition ccount_weak  p (sq : seq {poly R}) : R :=
  if p == 0 then 0 else
  if size p == 1%N then 0
    else if has (xpred1 0) sq then 0
      else
       let: (p', sq') := to_monic p sq in
       let sq_aux := (\prod_(j : 'I_(3 ^ size sq'))
           (\prod_(r <- sremps p' (p'^`() * (map (poly_comb sq') (sg_tab (size sq')))`_j)) r)) in
        let bound := pick_right (cauchy_bound p') sq_aux in
        prod_staq_coefs p' (-bound) bound sq'.

Lemma mem0_sremps p q : 0 \notin sremps p q.
Proof.
rewrite /sremps; move: (maxn _ _) => n; elim: n p q => [|n ihn] p q //=.
by case: ifP=> hp //=; rewrite in_cons eq_sym hp /= ihn.
Qed.


Lemma ex_roots_weak : forall p (sq : seq {poly R}), p != 0 ->
  reflect (exists x, (p.[x] == 0) && \big[andb/true]_(q <- sq) (q.[x] > 0))
    (ccount_weak p sq > 0).
Proof.
move=> p sq np0; apply: (@equivP _ _ _ _  (@to_monicP _ sq np0)).
rewrite /ccount_weak.
have -> : size p = size (to_monic p sq).1 by rewrite /= size_change_varp.
have -> : has (eq_op^~ 0) sq = has (eq_op^~ 0) (to_monic p sq).2.
  apply/hasP/hasP=> [] /= [q hq] q_neq0.
    exists (change_varq (lead_coef p) q); first by apply/mapP; exists q.
    by rewrite change_varq_eq0 ?lead_coef_eq0.
  move/mapP: hq=> [q' hq' qq']; exists q'=> //.
  by move: q_neq0; rewrite qq' change_varq_eq0 ?lead_coef_eq0.
rewrite (negPf np0).
have {np0} : (to_monic p sq).1 != 0 by rewrite change_varp_eq0.
case: (to_monic p sq) => {p sq} p sq /= np0.
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
* by rewrite gt0_cp // pick_right_lt0 // ?cauchy_bound_ge0.
* by move: np0 hsp; rewrite -!size_poly_eq0 size_deriv; case: size.
* move=> j; rewrite -root_bigmul. move: j; apply/forallP.
  rewrite -root_prod_fintype; exact: pick_rightPop.
* move=> j; rewrite -root_bigmul. move: j; apply/forallP.
  rewrite -root_prod_fintype; exact: pick_rightP.
* by case=> x /and3P [hpx hsqx xb]; exists x; rewrite hpx.
case=> x /andP [hpx hsqx]; exists x; rewrite hpx hsqx /=.
rewrite -[_ \in _]ltr_absl.
apply: ler_lt_trans (pick_right_lt _ _ ).
by apply: cauchy_boundP=> //; apply/eqP.
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

(*Set Printing Width 30.*)

Definition bounding_poly (sq : seq {poly R}) := (\prod_(q <- sq) q)^`().

Lemma myprodf_eq0 (S : idomainType)(I : eqType) (r : seq I) P (F : I -> S) : 
  reflect (exists2 i, ((i \in r) && (P i)) & (F i == 0))
  (\prod_(i <- r| P i) F i == 0).
Proof.
apply: (iffP idP) => [|[i Pi /eqP Fi0]]; last first.
  by case/andP: Pi => ri Pi; rewrite (big_rem _ ri) /= Pi Fi0 mul0r.
elim: r => [|i r IHr]; first by rewrite big_nil oner_eq0.
rewrite big_cons /=; have [Pi | ?] := ifP.
  rewrite mulf_eq0; case/orP=> [Fi0|]; first by exists i => //; rewrite mem_head.
  by case/IHr=> j /andP [rj Pj] Fj; exists j; rewrite // in_cons rj orbT.
by case/IHr=> j  /andP [rj Pj] Fj; exists j; rewrite // in_cons rj orbT.
Qed.

Lemma pol_sg_pinfty x y p : (forall z, z >= x -> p.[z] != 0) -> 
  y >= x-> sgr p.[y] = sgr (lead_coef p).
Proof.
Admitted.

Lemma pol_sg_minfty x y p : (forall z, z <= x -> p.[z] != 0) -> 
  y <= x-> sgr p.[y] = sgr ((-1)^+(size p).-1 * (lead_coef p)).
Proof.
move=> hnr hyx; pose q := p \Po (- 'X).
have hq z : z >= -x -> q.[z] != 0.
  move=> hxz; rewrite /q horner_comp_poly horner_opp hornerX; apply: hnr.
  by rewrite ler_oppl.
have : - y >= - x by rewrite ler_opp2.
  move/(pol_sg_pinfty hq); rewrite /q  horner_comp_poly horner_opp hornerX.
  rewrite opprK; move->; rewrite lead_coef_comp_poly ?size_opp ?size_polyX //.
  by rewrite lead_coef_opp lead_coefX mulrC.
Qed.

(* assia : i should at least use trichotomy *)

Let shrink (sq : seq {poly R}) :
  (exists x, 
    [|| ((bounding_poly sq).[x] == 0) && \big[andb/true]_(q <- sq) (q.[x] > 0),
        \big[andb/true]_(q <- sq)(lead_coef q > 0) |
        \big[andb/true]_(q <- sq)((-1)^+(size q).-1 * (lead_coef q) > 0)])
     <->
     exists x, \big[andb/true]_(q <- sq) (q.[x] > 0).
Proof.
split=> [] [x].
  case/or3P; first by case/andP=> [] ? h; exists x; rewrite h.
  - rewrite big_all => /allP hsq.
    have sqn0 : {in sq, forall q, q != 0}.
      by move=> q' /= /hsq; apply: contraL=> /eqP->; rewrite lead_coef0 ltrr.
    have pn0 : (\prod_(q <- sq) q) != 0.
      by apply/negP=> /myprodf_eq0 [] q; rewrite andbT => /sqn0 /negPf ->.
    pose b := cauchy_bound (\prod_(q <- sq) q) + 1; exists b.
    rewrite big_all; apply/allP=> r hr; have:= hsq r hr.
    rewrite -!sgr_cp0=> /eqP <-; apply/eqP. 
    apply: (@pol_sg_pinfty b) => // z; apply: contraL => /eqP rx0; rewrite -ltrNge.
     apply: (@ler_lt_trans _ (cauchy_bound (\prod_(q <- sq) q))); last first.
       by rewrite ltr_addl ltr01.
    have : (\prod_(q <- sq) q).[z] = 0.
      rewrite horner_prod; apply/eqP; apply/myprodf_eq0. 
      by exists r; rewrite ?hr //; apply/eqP.
    by move/(cauchy_boundP pn0) => /=; rewrite ler_absl => /andP [].
  - rewrite big_all => /allP hsq.
    have sqn0 : {in sq, forall q, q != 0}.
      by move=> q' /= /hsq; apply: contraL=> /eqP->; rewrite lead_coef0 mulr0 ltrr.
    have pn0 : (\prod_(q <- sq) q) != 0.
      by apply/negP=> /myprodf_eq0 [] q; rewrite andbT => /sqn0 /negPf ->.
    pose b := - cauchy_bound (\prod_(q <- sq) q) - 1; exists b.
    rewrite big_all; apply/allP=> r hr; have:= hsq r hr.
    rewrite -!sgr_cp0=> /eqP <-; apply/eqP. 
    apply: (@pol_sg_minfty b) => // z; apply: contraL => /eqP rx0; rewrite -ltrNge.
     apply: (@ltr_le_trans _ (- cauchy_bound (\prod_(q <- sq) q))).
       by rewrite /b -oppr_add ltr_opp2 ltr_addl ltr01.
    have : (\prod_(q <- sq) q).[z] = 0.
      rewrite horner_prod; apply/eqP; apply/myprodf_eq0. 
      by exists r; rewrite ?hr //; apply/eqP.
    by move/(cauchy_boundP pn0) => /=; rewrite ler_absl => /andP [].
rewrite big_all => /allP hsq; set bnd := cauchy_bound (\prod_(q <- sq) q) + 1.
rewrite /bounding_poly; set q := \prod_(q <- _) _.
have sqn0 : {in sq, forall q, q != 0}.
  by move=> q' /= /hsq; apply: contraL=> /eqP->; rewrite horner0 ltrr.
case: (boolP (q == 0))=> [|q0].
  by rewrite prodf_seq_eq0=> /hasP [q' /= /sqn0 /negPf->].
case: (next_rootP q x bnd); [by move/eqP; rewrite (negPf q0)| |]; last first.
- move=> c _ ex hc.
  suff -> : \big[andb/true]_(q1 <- sq) (0 < lead_coef q1).
    by exists 0; rewrite orbT.
  rewrite big_all; apply/allP=> r hr; have rxp := hsq r hr.
  rewrite -sgr_cp0 -(@pol_sg_pinfty x x) ?sgr_cp0 // => z hxz.
  case: (ltrP z bnd) => [hzb|].
    move: hxz; rewrite ler_eqVlt; case/orP=> [/eqP-> | hxz].
      by rewrite neqr_lt rxp orbT.
    have : z \in `]x, bnd[ by apply/int_dec.
    rewrite -/(root r z); move/(hc z); apply: contra; rewrite /root /q => hrx.
    by rewrite horner_prod; apply/myprodf_eq0; exists r; rewrite // hr.
   apply: contraL => /eqP rx0; rewrite -ltrNge.
   apply: (@ler_lt_trans _ (cauchy_bound (\prod_(q <- sq) q))); last first.
     by rewrite ltr_addl ltr01.
   have : (\prod_(q <- sq) q).[z] = 0.
     rewrite horner_prod; apply/eqP; apply/myprodf_eq0. 
     by exists r; rewrite ?hr //; apply/eqP.
   have pn0 : (\prod_(q <- sq) q) != 0.
     by apply/negP=> /myprodf_eq0 [] ?; rewrite andbT => /sqn0 /negPf ->.
   by move/(cauchy_boundP pn0) => /=; rewrite ler_absl => /andP [].
move=> y1 _ rqy1 hy1xb hy1.
have hnr r z :  r \in sq -> ~~(root q z) -> ~~(root r z).
    move=> hr; apply: contra; rewrite /root /q => hrx.
    by rewrite horner_prod; apply/myprodf_eq0; exists r; rewrite // hr.
case: (prev_rootP q (- bnd) x); [by move/eqP; rewrite (negPf q0)| |]; last first.
- move=> c _ ex hc. (* assia : what is the use of c ? *)
  suff -> : \big[andb/true]_(q1 <- sq) (0 < (-1) ^+ (size q1).-1 * lead_coef q1).
    by exists 0; rewrite !orbT.
  rewrite big_all; apply/allP=> r hr; have rxp := hsq r hr.
  rewrite -sgr_cp0 -(@pol_sg_minfty x x) ?sgr_cp0 // => z hxz.
  case: (lerP z (- bnd)) => [|hzb]; last first.
    move: hxz; rewrite ler_eqVlt; case/orP=> [/eqP<- | hxz].
      by rewrite neqr_lt rxp orbT.
    have : z \in `] (- bnd), x[ by apply/int_dec. (* assia : int not? *)
    rewrite -/(root r z); move/(hc z); exact: hnr.
  apply: contraL => /eqP rx0; rewrite -ltrNge.
    apply: (@ltr_le_trans _ (- cauchy_bound (\prod_(q <- sq) q))).
      by rewrite /bnd  ltr_opp2 ltr_addl ltr01.
    have : (\prod_(q <- sq) q).[z] = 0.
      rewrite horner_prod; apply/eqP; apply/myprodf_eq0. 
      by exists r; rewrite ?hr //; apply/eqP.
    have pn0 : (\prod_(q <- sq) q) != 0.
      by apply/negP=> /myprodf_eq0 [] ?; rewrite andbT => /sqn0 /negPf ->.
    by move/(cauchy_boundP pn0) => /=; rewrite ler_absl => /andP [].
move=> y2 _ rqy2 hy2xb hy2.
have lty12 : y2 < y1.
  by apply: (@ltr_trans _ x); rewrite 1?(intP hy1xb) 1?(intP hy2xb).
have : q.[y2] = q.[y1] by rewrite rqy1 rqy2.
case/(rolle lty12) => z hz rz; exists z.
suff -> : ((q^`()).[z] == 0) && \big[andb/true]_(q1 <- sq) (0 < q1.[z]) by [].
rewrite rz eqxx /= big_all; apply/allP=> r hr; have rxp := hsq r hr.
suff hs: sgr r.[x] = sgr r.[z] by rewrite -sgr_cp0 -hs sgr_cp0.
suff : {in `]y2, y1[, forall x : R, ~~ root r x}.
move/polyrN0_int; apply=> //.
  by apply/int_dec; split; rewrite 1?(intP hy1xb) 1?(intP hy2xb).
move=> t; case/int_dec=> htl htr; case: (ltrgtP t x)=>[htx | hxt|->].
- suff : ~~ root q t by apply: hnr.
  by apply: hy2; apply/int_dec.
- suff : ~~ root q t by apply: hnr.
  by apply: hy1; apply/int_dec.
- by rewrite /root neqr_lt rxp orbT.
Qed.

(* Definition ccount (sp sq : seq {poly R}) := *)
(*   let p := \big[@rgcdp _/0%R]_(p <- sp) p in *)
(*     ccount_weak (if p != 0 then p else *)
(*         let bq := bounding_poly sq in *)
(*     if bq != 0 then bq else 'X) sq. *)
 
Definition ccount_gt0 (sp sq : seq {poly R}) :=
  let p := \big[@rgcdp _/0%R]_(p <- sp) p in
    if p != 0 then 0 < ccount_weak p sq
    else let bq := bounding_poly sq in
	[|| 0 < ccount_weak bq sq,
            \big[andb/true]_(q <- sq)(lead_coef q > 0)|
            \big[andb/true]_(q <- sq)((-1)^+(size q).-1 *(lead_coef q) > 0)].

(* :TODO: generalize to non idomainTypes and backport to polydiv *)
Lemma rgcdp_eq0 p q : rgcdp p q == 0 = (p == 0) && (q == 0).
Proof. by rewrite -eqp0 (eqp_ltrans (eqp_rgcd_gcd _ _)) eqp0 gcdp_eq0. Qed.

Lemma root_bigrgcd (x : R) (ps : seq {poly R}) :
  root (\big[(@rgcdp _)/0]_(p <- ps) p) x = all (root^~ x) ps.
Proof.
elim: ps; first by rewrite big_nil root0.
move=> p ps ihp; rewrite big_cons /=.
by rewrite (eqp_root (eqp_rgcd_gcd _ _)) root_gcd ihp.
Qed.

Lemma size_prod_eq1 (sq : seq {poly R}) :  
  reflect (forall q, q \in sq -> size q = 1%N)  (size (\prod_(q0 <- sq) q0) == 1%N). 
Proof.
apply: (iffP idP).
  elim: sq => [| q sq ih]; first by move=> _ q; rewrite in_nil.
  rewrite big_cons; case: (altP (q =P 0)) => [-> | qn0].
    by rewrite mul0r size_poly0.
  case: (altP ((\prod_(j <- sq) j) =P 0)) => [-> | pn0].
    by rewrite mulr0 size_poly0.
  rewrite size_mul_id //; case: (ltngtP (size q) 1).
  - by rewrite ltnS leqn0 size_poly_eq0 (negPf qn0).
  - case: (size q) => [|n] //; case: n => [|n] // _; rewrite !addSn /= eqSS.
    by rewrite addn_eq0 size_poly_eq0 (negPf pn0) andbF.
  - move=> sq1; case: (ltngtP (size (\prod_(j <- sq) j)) 1).
    + by rewrite ltnS leqn0 size_poly_eq0 (negPf pn0).
    + case: (size (\prod_(j <- sq) j)) => [|n] //; case: n => [|n] // _.
      by rewrite !addnS /= eqSS addn_eq0 size_poly_eq0 (negPf qn0).
    move=> sp1 _ p; rewrite in_cons; case/orP => [/eqP -> |] //; apply: ih.
    by apply/eqP.
elim: sq => [| q sq ih] hs; first by rewrite big_nil size_poly1 eqxx.
case: (altP (q =P 0)) => [ | qn0].
  by  move/eqP; rewrite -size_poly_eq0 hs ?mem_head.
case: (altP ((\prod_(q0 <- sq) q0) =P 0)) => [ | pn0].
  move/eqP; rewrite -size_poly_eq0 (eqP (ih _)) // => t ht; apply: hs.
  by rewrite in_cons ht orbT.
rewrite big_cons size_mul_id // (eqP (ih _)) //; last first. 
  by move=> t ht; apply: hs; rewrite in_cons ht orbT.
rewrite addnS addn0; apply/eqP; apply: hs; exact: mem_head.
Qed.

Lemma ex_roots (sp sq : seq {poly R}) :
  reflect (exists x, \big[andb/true]_(p <- sp) (p.[x] == 0)
                  && \big[andb/true]_(q <- sq) (q.[x] > 0))
    (ccount_gt0 sp sq).
Proof.
rewrite /ccount_gt0.
case: (boolP (_ == 0))=> hsp /=.

  move: hsp; rewrite (big_morph  _ rgcdp_eq0 (eqxx _)).
  rewrite big_all => /allP /= hsp.
  apply: (@equivP (exists x, \big[andb/true]_(q <- sq) (0 < q.[x]))); last first. 
    split; case=> x; [move=>hx | case/andP=> _ hx]; exists x; rewrite hx //.
    by rewrite andbT big_all; apply/allP=> p /hsp /eqP ->; rewrite horner0.
  apply: (@equivP (exists x, 
    [|| ((bounding_poly sq).[x] == 0) && \big[andb/true]_(q <- sq) (q.[x] > 0),
        \big[andb/true]_(q <- sq)(lead_coef q > 0) |
        \big[andb/true]_(q <- sq)((-1)^+(size q).-1 * (lead_coef q) > 0)])); last exact: shrink.
   apply: (iffP idP).
   - case/or3P.
     + case: (altP (bounding_poly sq =P 0))=> [-> | bsqn0].
         by rewrite /ccount_weak eqxx ltrr.
       by move/ex_roots_weak; case/(_ bsqn0)=> y hy; exists y; rewrite hy.
     + by move->; exists 0; rewrite orbT.
     + by move->; exists 0; rewrite !orbT.
    - case=> y; case/or3P=> [ hy| -> | ->]; rewrite ?orbT //.
      case: (altP (bounding_poly sq =P 0))=> [bsq0 | bsqn0]; last first.
        suff -> :  0 < ccount_weak (bounding_poly sq) sq by [].
        by apply/ex_roots_weak => //; exists y.
      suff -> : \big[andb/true]_(q <- sq) (0 < lead_coef q) by rewrite orbT.
      case/andP: hy => _; rewrite !big_all; move/allP=> hy; apply/allP=> q qsq.
      move/eqP: bsq0; rewrite /bounding_poly.
      rewrite -derivn1 -derivn_poly0 leq_eqVlt ltnS leqn0; case/orP; last first.
        rewrite size_poly_eq0; case/myprodf_eq0=> q1; rewrite andbT; move/hy.
        by move=> habs /eqP q10; move: habs; rewrite q10 horner0 ltrr.
(* assia : ltrr could be hint resolve *)
     move/size_prod_eq1; move/(_ _ qsq) => /eqP; case/size1P=> c cn0 eqc.
     by move: (hy _ qsq); rewrite eqc hornerC lead_coefC.
apply: (iffP (ex_roots_weak _ _))=> [] // [x hx];
   by exists x; move: hx; rewrite [_ == _]root_bigrgcd !big_all.
Qed.

End QeRcfTh.
