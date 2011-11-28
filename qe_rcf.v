Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import finfun path.
Require Import bigop ssralg poly polydiv orderedalg zmodp div zint.
Require Import polyorder polyrcf interval polyXY.
Require Import qe_rcf_th ordered_qelim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory ORing.Theory.

Local Open Scope nat_scope.
Local Open Scope ring_scope.

Local Notation term := GRing.term.
Local Notation rterm := GRing.rterm.
Local Notation eval := GRing.eval.
Local Notation Const := GRing.Const.

Import ord.
Import RPdiv.

Section proj_qe_rcf.

Variable F : rcfType.

Definition polyF := seq (term F).

Notation fF := (formula  F).
Notation qf f := (qf_form f && rformula f).

Lemma qfP (f : formula F) (fP : qf f) : qf f * qf_form f * rformula f.
Proof. by do ?split=> //; case/andP: fP. Qed.

(* Lemma And_qf (f g : qf_rformula) : qf (f /\ g). *)
(* Proof. by rewrite /= !qfrP. Qed. *)
(* Canonical And_qfr f g := QfrForm (And_qf f g). *)

(* Lemma Or_qf (f g : qf_rformula) : qf (f \/ g). *)
(* Proof. by rewrite /= !qfrP. Qed. *)
(* Canonical Or_qfr f g := QfrForm (Or_qf f g). *)

Section If.

Implicit Types (pf tf ef : formula F).

Definition If := locked (fun pf tf ef => (pf /\ tf \/ ~ pf /\ ef)%oT).

Lemma If_form_qf pf tf ef:
  qf_form pf -> qf_form tf -> qf_form ef -> qf_form (If pf tf ef).
Proof. by unlock If; move=> /= -> -> ->. Qed.

Lemma If_form_rf pf tf ef :
  rformula pf -> rformula tf -> rformula ef -> rformula (If pf tf ef).
Proof. by unlock If; move=> /= -> -> ->. Qed.

Lemma qf_If pf tf ef : qf pf -> qf tf -> qf ef -> qf (If pf tf ef).
Proof. by unlock If; move=> * /=; do !rewrite qfP //. Qed.

Lemma eval_If e pf tf ef :
  let ev := qf_eval e in ev (If pf tf ef) = (if ev pf then ev tf else ev ef).
Proof. by unlock If=> /=; case: ifP => _; rewrite ?orbF. Qed.

End If.

Notation "'If' c1 'Then' c2 'Else' c3" := (If c1 c2 c3)
  (at level 200, right associativity, format
"'[hv   ' 'If'  c1  '/' '[' 'Then'  c2  ']' '/' '[' 'Else'  c3 ']' ']'").

Notation cps T := ((T -> fF) -> fF).

Section Pick.

Variables (I : finType) (pred_f then_f : I -> fF) (else_f : fF).

Definition Pick :=
  \big[Or/False]_(p : {ffun pred I})
    ((\big[And/True]_i (if p i then pred_f i else ~ pred_f i))
    /\ (if pick p is Some i then then_f i else else_f))%oT.

Lemma Pick_form_qf :
   (forall i, qf_form (pred_f i)) ->
   (forall i, qf_form (then_f i)) ->
    qf_form else_f ->
  qf_form Pick.
Proof.
move=> qfp qft qfe; have mA := (big_morph (@qf_form _)) true andb.
rewrite mA // big1 //= => p _.
rewrite mA // big1 => [|i _]; first by case: pick.
by rewrite fun_if if_same /= qfp.
Qed.

Lemma eval_Pick e (qev := qf_eval e) :
  let P i := qev (pred_f i) in
  qev Pick = (if pick P is Some i then qev (then_f i) else qev else_f).
Proof.
move=> P; rewrite ((big_morph qev) false orb) //= big_orE /=.
apply/existsP/idP=> [[p] | true_at_P].
  rewrite ((big_morph qev) true andb) //= big_andE /=.
  case/andP=> /forallP eq_p_P.
  rewrite (@eq_pick _ _ P) => [|i]; first by case: pick.
  by move/(_ i): eq_p_P => /=; case: (p i) => //=; move/negbTE.
exists [ffun i => P i] => /=; apply/andP; split.
  rewrite ((big_morph qev) true andb) //= big_andE /=.
  by apply/forallP=> i; rewrite /= ffunE; case Pi: (P i) => //=; apply: negbT.
rewrite (@eq_pick _ _ P) => [|i]; first by case: pick true_at_P.
by rewrite ffunE.
Qed.

End Pick.

Fixpoint eval_poly (e : seq F) pf :=
  if pf is c :: qf then (eval_poly e qf) * 'X + (eval e c)%:P else 0.

Definition rpoly p := (all (@rterm F) p).

Notation "'bind' x <- y ; z" :=
  (y (fun x => z)) (at level 99, x at level 0, y at level 0,
    format "'[hv' 'bind'  x  <-  y ; '/' z ']'").

Fixpoint Size (p : polyF) : cps nat := fun k =>
  if p is c :: q then
    bind n <- Size q;
    if n is m.+1 then k m.+2
      else If c == 0 Then k 0%N Else k 1%N
    else k O%N.

Lemma eval_Size k p e :
  qf_eval e (Size p k) = qf_eval e (k (size (eval_poly e p))).
Proof.
elim: p e k=> [|c p ihp] e k; first by rewrite size_poly0.
rewrite ihp /= size_amulX -size_poly_eq0; case: size=> //.
by rewrite eval_If /=; case: (_ == _).
Qed.

Lemma qf_Size k p : (forall n, qf (k n)) -> rpoly p -> qf (Size p k).
Proof.
elim: p k => //= c q ihp k qf_k /andP[rc rq]; apply: ihp=> [] // [|n] //=.
by rewrite qf_If //= rc.
Qed.

Definition Isnull (p : polyF) : cps bool := fun k =>
  bind n <- Size p; k (n == 0%N).

Lemma eval_Isnull k p e : qf_eval e (Isnull p k) = qf_eval e (k (eval_poly e p == 0)).
Proof. by rewrite eval_Size size_poly_eq0. Qed.

Lemma qf_Isnull k p : (forall b, qf (k b)) -> rpoly p -> qf (Isnull p k).
Proof. by move=> *; apply: qf_Size. Qed.

Definition LtSize (p q : polyF) : cps bool := fun k =>
  bind n <- Size p; bind m <- Size q; k (n < m)%N.

Fixpoint LeadCoef p : cps (term F) := fun k =>
  if p is c :: q then
    bind l <- LeadCoef q; If l == 0 Then k c Else k l
    else k (Const 0).

Lemma eval_LeadCoef e p k k' :
  (forall x, qf_eval e (k x) = (k' (eval e x))) ->
  qf_eval e (LeadCoef p k) = k' (lead_coef (eval_poly e p)).
Proof.
move=> Pk; elim: p k k' Pk=> [|a p ihp] k k' Pk //=.
  by rewrite lead_coef0 Pk.
rewrite (ihp _ (fun l => if l == 0 then qf_eval e (k a) else (k' l))); last first.
  by move=> x; rewrite eval_If /= !Pk.
rewrite lead_coef_eq0; have [->|p_neq0] := altP (_ =P 0).
  by rewrite mul0r add0r lead_coefC.
rewrite lead_coef_addl ?lead_coef_mul_monic ?monicX //.
rewrite size_mul_id ?polyX_eq0 // size_polyX addn2 /= ltnS size_polyC.
by case: (_ == _)=> //=; rewrite size_poly_gt0.
Qed.

Implicit Arguments eval_LeadCoef [e p k].
Prenex Implicits eval_LeadCoef.

Lemma qf_LeadCoef k p : (forall c, rterm c -> qf (k c))
  -> rpoly p -> qf (LeadCoef p k).
Proof.
elim: p k => /= [k kP _|c q ihp k kP /andP[rc rq]]; first exact: kP.
by rewrite ihp // => c' rc'; rewrite qf_If //= ?andbT // kP.
Qed.

Fixpoint AmulXn (a : term F) (n : nat) : polyF:=
  if n is n'.+1 then (Const 0) :: (AmulXn a n') else [::a].

Lemma eval_AmulXn a n e : eval_poly e (AmulXn a n) = (eval e a)%:P * 'X^n.
Proof.
elim: n=> [|n] /=; first by rewrite expr0 mulr1 mul0r add0r.
by move->; rewrite addr0 -mulrA -exprSr.
Qed.

Lemma rAmulXn a n : rterm a -> rpoly (AmulXn a n).
Proof. by elim: n a=> [a /= -> //|n ihn a ra]; apply: ihn. Qed.

Fixpoint AddPoly (p q : polyF) :=
  if p is a::p' then
    if q is b::q' then (a + b)%oT :: (AddPoly p' q')
      else p
    else q.

Lemma eval_AddPoly p q e :
  eval_poly e (AddPoly p q) = (eval_poly e p) + (eval_poly e q).
Proof.
elim: p q=> [|a p Hp] q /=; first by rewrite add0r.
case: q=> [|b q] /=; first by rewrite addr0.
by rewrite Hp mulr_addl rmorphD /= !addrA [X in _ = X + _]addrAC.
Qed.

Lemma rAddPoly p q : rpoly p -> rpoly q -> rpoly (AddPoly p q).
Proof.
by elim: p q=> //= a p ihp [|b q] //= /andP[-> /ihp hp] /andP[-> /hp].
Qed.

Fixpoint MulPoly (p q : polyF) := if p is a :: p'
    then AddPoly (map (GRing.Mul a) q) (Const 0 :: (MulPoly p' q)) else [::].


Lemma map_poly0 (R R' : ringType) (f : R -> R') : map_poly f 0 = 0.
Proof. by rewrite map_polyE polyseq0. Qed.

Lemma eval_map_mul e t p :
  eval_poly e (map (GRing.Mul t) p) = (eval e t) *: (eval_poly e p).
Proof.
elim: p=> [|a p ihp] /=; first by rewrite scaler0.
by rewrite ihp scaler_addr scaler_mull -!mul_polyC rmorphM.
Qed.

Lemma eval_MulPoly e p q :
  eval_poly e (MulPoly p q) = (eval_poly e p) * (eval_poly e q).
Proof.
elim: p q=> [|a p Hp] q /=; first by rewrite mul0r.
rewrite eval_AddPoly /= eval_map_mul Hp.
by rewrite addr0 mulr_addl addrC mulrAC mul_polyC.
Qed.

Lemma rpoly_map_mul t p : rterm t -> rpoly (map (GRing.Mul t) p) = rpoly p.
Proof.
move=> rt; rewrite /rpoly all_map /=.
by rewrite (@eq_all _ _ (@rterm _)) // => x; rewrite /= rt.
Qed.

Lemma rMulPoly p q : rpoly p -> rpoly q -> rpoly (MulPoly p q).
Proof.
elim: p q=> // a p ihp q /andP[ra rp] rq //=.
by apply: rAddPoly; [rewrite rpoly_map_mul|apply: ihp].
Qed.

Definition ExpPoly p n := iterop n MulPoly p [::1%oT].

Lemma eval_ExpPoly e p n : eval_poly e (ExpPoly p n) = (eval_poly e p) ^+ n.
Proof.
case: n=> [|n]; first by rewrite /= expr0 mul0r add0r.
rewrite /ExpPoly iteropS exprSr; elim: n=> [|n ihn] //=.
  by rewrite expr0 mul1r.
by rewrite eval_MulPoly ihn exprS mulrA.
Qed.

Lemma rExpPoly p n : rpoly p -> rpoly (ExpPoly p n).
Proof.
move=> rp; case: n=> // n; rewrite /ExpPoly iteropS.
by elim: n=> //= n ihn; rewrite rMulPoly.
Qed.

Definition OppPoly := map (GRing.Mul (@Const F (-1))).

Lemma eval_OppPoly p e : eval_poly e (OppPoly p) = - eval_poly e p.
Proof.
elim: p; rewrite //= ?oppr0 // => t ts ->.
by rewrite !mulNr !oppr_add polyC_opp mul1r.
Qed.

Lemma rOppPoly p : rpoly p -> rpoly (OppPoly p).
Proof. by move=> rp; rewrite rpoly_map_mul. Qed.

Definition NatMulPoly n := map (GRing.Mul (@GRing.NatConst F n)).
Lemma eval_NatMulPoly p n e :
  eval_poly e (NatMulPoly n p) = (eval_poly e p) *+ n.
Proof.
elim: p; rewrite //= ?mul0rn // => c p ->.
rewrite mulrn_addl mulr_natl polyC_natmul; congr (_+_).
by rewrite -mulr_natl mulrAC -mulrA mulr_natl mulrC.
Qed.

Lemma rNatMulPoly n p : rpoly p -> rpoly (NatMulPoly n p).
Proof. by move=> rp; rewrite rpoly_map_mul. Qed.

Definition eval_OpPoly :=
  (eval_MulPoly, eval_AmulXn, eval_AddPoly, eval_OppPoly, eval_NatMulPoly).

Fixpoint Rediv_rec_loop (q : polyF) sq cq
  (c : nat) (qq r : polyF) (n : nat) {struct n} :
  cps (nat * polyF * polyF) := fun k =>
  bind sr <- Size r;
  if (sr < sq)%N then k (c, qq, r) else
    bind lr <- LeadCoef r;
    let m := AmulXn lr (sr - sq) in
    let qq1 := AddPoly (MulPoly qq [::cq]) m in
    let r1 := AddPoly (MulPoly r ([::cq])) (OppPoly (MulPoly m q)) in
    if n is n1.+1 then Rediv_rec_loop q sq cq c.+1 qq1 r1 n1 k
    else k (c.+1, qq1, r1).

Fixpoint redivp_rec_loop (q : {poly F}) sq cq
   (k : nat) (qq r : {poly F})(n : nat) {struct n} :=
    if (size r < sq)%N then (k, qq, r) else
    let m := (lead_coef r) *: 'X^(size r - sq) in
    let qq1 := qq * cq%:P + m in
    let r1 := r * cq%:P - m * q in
    if n is n1.+1 then redivp_rec_loop q sq cq k.+1 qq1 r1 n1 else (k.+1, qq1, r1).

(* Lemma eval_ConstPoly e c : eval_poly e [::c] = (eval e c)%:P. *)
(* Proof. by rewrite /= mul0r add0r. Qed. *)

(* Lemma eval_Rediv_rec_loop e q sq cq c qq r n k k' *)
(*   (d := redivp_rec_loop (eval_poly e q) sq (eval e cq) *)
(*       c (eval_poly e qq) (eval_poly e r) n) : *)
(*   (forall c qq r, qf_eval e (k (c, qq, r))  *)
(*     = k' (c, eval_poly e qq, eval_poly e r)) -> *)
(*   qf_eval e (Rediv_rec_loop q sq cq c qq r n k) *)
(*   = k' (d.1.1, d.1.2, d.2)%PAIR. *)
(* Proof. *)
(* move=> Pk; elim: n c qq r k k' Pk @d => [|n ihn] c qq r k k' Pk /=. *)
(*   rewrite eval_Size /=; case: (_ < _)%N; rewrite ?Pk //=. *)
(*   rewrite -!eval_ConstPoly -!eval_OpPoly. *)
(*   apply: eval_LeadCoef. *)
(*     by rewrite Pk !eval_OpPoly /= ?(mul0r, add0r) mul_polyC. *)
(*   by move=> x; rewrite Pk [RHS]Pk !eval_OpPoly /= mul_polyC ?(mul0r,add0r). *)
(* rewrite eval_Size /=; have [//=|gtq] := ltnP. *)
(* rewrite eval_LeadCoef /=. *)
(*   by rewrite ihn // !eval_OpPoly /= ?(mul0r, add0r) mul_polyC. *)
(* by move=> x; rewrite !ihn // !eval_OpPoly /= ?(mul0r, add0r) mul_polyC. *)
(* Qed. *)


Lemma eval_Rediv_rec_loop e q sq cq c qq r n k k'
  (d := redivp_rec_loop (eval_poly e q) sq (eval e cq)
    c (eval_poly e qq) (eval_poly e r) n) :
  (forall c qq r, qf_eval e (k (c, qq, r))
    = k' (c, eval_poly e qq, eval_poly e r)) ->
  qf_eval e (Rediv_rec_loop q sq cq c qq r n k) = k' d.
Proof.
move=> Pk; elim: n c qq r k Pk @d=> [|n ihn] c qq r k Pk /=.
  rewrite eval_Size /=; have [//=|gtq] := ltnP.
  rewrite (eval_LeadCoef (fun lr =>
    let m := lr *: 'X^(size (eval_poly e r) - sq) in
    let qq1 := (eval_poly e qq) * (eval e cq)%:P + m in
    let r1 := (eval_poly e r) * (eval e cq)%:P - m * (eval_poly e q) in
      k' (c.+1, qq1, r1))) //.
   by move=> x /=; rewrite Pk /= !eval_OpPoly /= mul0r add0r !mul_polyC.
rewrite eval_Size /=; have [//=|gtq] := ltnP.
rewrite (eval_LeadCoef (fun lr =>
  let m := lr *: 'X^(size (eval_poly e r) - sq) in
  let qq1 := (eval_poly e qq) * (eval e cq)%:P + m in
  let r1 := (eval_poly e r) * (eval e cq)%:P - m * (eval_poly e q) in
    k' (redivp_rec_loop (eval_poly e q) sq (eval e cq) c.+1 qq1 r1 n))) //=.
by move=> x; rewrite ihn // !eval_OpPoly /= mul0r add0r !mul_polyC.
Qed.

Implicit Arguments eval_Rediv_rec_loop [e q sq cq c qq r n k].
Prenex Implicits eval_Rediv_rec_loop.

Definition rOpPoly :=
  (rMulPoly, rAmulXn, rAddPoly, rOppPoly, rNatMulPoly).

Lemma qf_Rediv_rec_loop q sq cq c qq r n k :
  rpoly q -> rterm cq -> rpoly qq -> rpoly r ->
  (forall r, [&& rpoly r.1.2 & rpoly r.2] -> qf (k r))%PAIR
  -> qf (Rediv_rec_loop q sq cq c qq r n k).
Proof.
elim: n q sq cq c qq r k=> [|n ihn] q sq cq c qq r k rq rcq rqq rr rk.
  apply: qf_Size=> //= n; case: (_ < _)%N; first by rewrite rk //= rqq rr.
  by apply: qf_LeadCoef=> // l rl; rewrite rk //= !rOpPoly //= ?rcq ?rqq.
rewrite /= qf_Size=> // n'; case: (_ < _)%N; first by rewrite rk //= rqq rr.
by apply: qf_LeadCoef=> // l rl; rewrite ihn //= !rOpPoly //= ?rcq ?rqq.
Qed.

Definition Rediv (p : polyF) (q : polyF) : cps (nat * polyF * polyF) :=
  fun k =>
  bind b <- Isnull q;
  if b then k (0%N, [::Const 0], p)
    else bind sq <- Size q;
      bind sp <- Size p;
      bind lq <- LeadCoef q;
      Rediv_rec_loop q sq lq 0 [::Const 0] p sp k.

Lemma redivp_rec_loopP q c qq r n : redivp_rec q c qq r n
    = redivp_rec_loop q (size q) (lead_coef q) c qq r n.
Proof. by elim: n c qq r => [| n Pn] c qq r //=; rewrite Pn. Qed.

Lemma eval_Rediv e p q k k' (d := (redivp (eval_poly e p) (eval_poly e q))) :
  (forall c qq r,  qf_eval e (k (c, qq, r)) = k' (c, eval_poly e qq, eval_poly e r)) ->
  qf_eval e (Rediv p q k) = k' d.
Proof.
move=> Pk; rewrite eval_Isnull /d /redivp.
have [_|p_neq0] /= := boolP (_ == _); first by rewrite Pk /= mul0r add0r.
rewrite !eval_Size; set p' := eval_poly e p; set q' := eval_poly e q.
rewrite (eval_LeadCoef (fun lq =>
  k' (redivp_rec_loop q' (size q') lq 0 0 p' (size p')))) /=; last first.
  by move=> x; rewrite (eval_Rediv_rec_loop k') //= mul0r add0r.
by rewrite redivp_rec_loopP.
Qed.

Implicit Arguments eval_Rediv [e p q k].
Prenex Implicits eval_Rediv.

Lemma qf_Rediv : forall p k q,
  (forall r, [&& rpoly r.1.2 & rpoly r.2] -> qf (k r))%PAIR
  -> rpoly p -> rpoly q -> qf (Rediv p q k).
Proof.
move=> p k q kP rp rq; rewrite /Rediv.
apply: qf_Isnull=> // b.
case b; first by apply: kP=> /=.
apply: qf_Size => // sq.
apply: qf_Size=> // sp.
apply: qf_LeadCoef=> // lq rlq.
exact: qf_Rediv_rec_loop.
Qed.

Definition Rmod (p : polyF) (q : polyF) (k : polyF -> fF) : fF :=
  Rediv p q (fun d => k d.2)%PAIR.
Definition Rdiv (p : polyF) (q : polyF) (k : polyF -> fF) : fF :=
  Rediv p q (fun d => k d.1.2)%PAIR.
Definition Rscal (p : polyF) (q : polyF) (k : nat -> fF) : fF :=
  Rediv p q (fun d => k d.1.1)%PAIR.
Definition Rdvd (p : polyF) (q : polyF) (k : bool -> fF) : fF :=
  bind r <- Rmod p q; bind r_null <- Isnull r; k r_null.

Fixpoint rgcdp_loop n (pp qq : {poly F}) {struct n} :=
  if rmodp pp qq == 0 then qq
    else if n is n1.+1 then rgcdp_loop n1 qq (rmodp pp qq)
        else rmodp pp qq.

Fixpoint Rgcd_loop n pp qq k {struct n} :=
  bind r <- Rmod pp qq; bind b <- Isnull r;
  if b then (k qq)
    else if n is n1.+1 then Rgcd_loop n1 qq r k else k r.

Lemma eval_Rgcd_loop e n p q k k' :
  (forall p, qf_eval e (k p) = k' (eval_poly e p))
  -> qf_eval e (Rgcd_loop n p q k) =
    k' (rgcdp_loop n (eval_poly e p) (eval_poly e q)).
Proof.
elim: n p q k k'=> [|n ihn] p q k k' Pk /=.
  rewrite (eval_Rediv (fun r =>
    if r.2%PAIR == 0 then k' (eval_poly e q) else k' r.2%PAIR)) /=.
    by case: eqP.
  by move=> _ _ r; rewrite eval_Isnull; case: eqP.
pose q' := eval_poly e q.
rewrite (eval_Rediv (fun r =>
  if r.2%PAIR == 0 then k' q' else k' (rgcdp_loop n q' r.2%PAIR))) /=.
  by case: eqP.
move=> _ _ r; rewrite eval_Isnull; case: eqP; first by rewrite Pk.
by rewrite (ihn _ _ _ k').
Qed.

Lemma qf_Rgcd_loop p q n k : (forall r, rpoly r -> qf (k r)) ->
  rpoly p -> rpoly q -> qf (Rgcd_loop n p q k).
Proof.
move=> kP; elim: n p q k kP => [|n ihn] p q k kP rp rq /=.
  apply: qf_Rediv=> // r; case/andP=> _ rr.
  by apply: qf_Isnull=> // [[]]; apply: kP.
apply: qf_Rediv=> // r; case/andP=> _ rr.
apply: qf_Isnull=> // [[]]; first exact: kP.
exact: ihn.
Qed.

Definition Rgcd (p : polyF) (q : polyF) : cps polyF := fun k =>
  let aux p1 q1 k := (bind b <- Isnull p1;
    if b then k q1 else bind n <- Size p1; Rgcd_loop n p1 q1 k) in
  bind b <- LtSize p q;
  if b then aux q p k else aux p q k.

Lemma eval_Rgcd e p q k k' :
  (forall p, qf_eval e (k p) = k' (eval_poly e p)) ->
  qf_eval e (Rgcd p q k) =
  k' (rgcdp (eval_poly e p) (eval_poly e q)).
Proof.
move=> Pk; rewrite /Rgcd /LtSize !eval_Size /rgcdp.
case: ltnP=> _; rewrite !eval_Isnull; case: eqP=> // _;
by rewrite eval_Size; apply: eval_Rgcd_loop.
Qed.

Implicit Arguments eval_Rgcd [e p q k].
Prenex Implicits eval_Rgcd.

Lemma qf_Rgcd p q k :  (forall r, rpoly r -> qf (k r)) ->
  rpoly p -> rpoly q -> qf (Rgcd p q k).
Proof.
move=> kP rp rq; apply: qf_Size=> // n; apply: qf_Size=> // m.
case:(_ < _)%N; apply: qf_Isnull=> //;
by case; do ?apply: kP=> //; apply: qf_Size=> // n'; apply: qf_Rgcd_loop.
Qed.

Fixpoint BigRgcd (ps : seq polyF) k : fF :=
  if ps is p :: pr then bind r <- BigRgcd pr; Rgcd p r k else k [::Const 0].

Lemma eval_BigRgcd e ps k k' :
  (forall p, qf_eval e (k p) = k' (eval_poly e p)) ->
  qf_eval e (BigRgcd ps k) =
  k' (\big[@rgcdp _/0%:P]_(i <- ps)(eval_poly e i)).
Proof.
elim: ps k k'=> [|p sp ihsp] k k' Pk /=.
  by rewrite big_nil Pk /= mul0r add0r.
rewrite big_cons (ihsp _ (fun r => k' (rgcdp (eval_poly e p) r))) //.
by move=> r; apply: eval_Rgcd.
Qed.

Definition rseq_poly ps := all rpoly ps.

Lemma qf_BigRgcd ps k : (forall r, rpoly r -> qf (k r)) ->
  rseq_poly ps -> qf (BigRgcd ps k).
Proof.
move=> kP; elim: ps k kP=> [k kP *|c p ihp k kP] ; first exact: kP.
by move=> /andP[rc rp]; apply: ihp=> // r rr; apply: qf_Rgcd.
Qed.

Fixpoint Rgdco_rec (q: polyF) (p : polyF) n k :=
  if n is m.+1 then
    bind d <- Rgcd p q; bind sd <- Size d;
    if sd == 1%N then k p
      else bind r <- Rdiv p d; Rgdco_rec q r m k
    else bind b <- Isnull q; k [:: Const b%:R].

Lemma eval_Rgdco_rec e p q n k k' :
  (forall p, qf_eval e (k p) = k' (eval_poly e p)) ->
  qf_eval e (Rgdco_rec p q n k)
  = k' (rgdcop_rec (eval_poly e p) (eval_poly e q) n).
Proof.
elim: n p q k k'=> [|n ihn] p q k k' Pk /=.
 by rewrite eval_Isnull Pk; case: eqP; rewrite /= mul0r add0r.
pose q' := eval_poly e q; pose p' := eval_poly e p.
rewrite (eval_Rgcd (fun d => if size d == 1%N then k' q'
  else k' (rgdcop_rec p' (rdivp q' d) n))).
  by rewrite /rcoprimep; case: eqP.
move=> d; rewrite eval_Size; case: eqP=> _; first by rewrite Pk.
rewrite (eval_Rediv (fun r => k' (rgdcop_rec p' r.1.2%PAIR n))) //.
by move=> /= _ qq _; apply: ihn.
Qed.

Implicit Arguments eval_Rgdco_rec [e p q n k].
Prenex Implicits eval_Rgdco_rec.

Lemma qf_Rgdco_rec p q n k : (forall r, rpoly r -> qf (k r)) ->
  rpoly p -> rpoly q -> qf (Rgdco_rec p q n k).
Proof.
move=> Pk rp rq; elim: n p q k Pk rp rq=> [|n ihn] p q k Pk rp rq /=.
apply: qf_Isnull=> //; first by case; rewrite Pk.
apply: qf_Rgcd=> // g rg; apply: qf_Size=> // n'.
case:(_ == _); first exact: Pk.
by apply: qf_Rediv=> // g' /andP[rg12 rg2]; apply: ihn.
Qed.

Definition Rgdco q p : cps polyF :=
  fun k => bind sp <- Size p; (Rgdco_rec q p sp k).

Lemma eval_Rgdco e p q k k' :
  (forall p, qf_eval e (k p) = k' (eval_poly e p)) ->
  qf_eval e (Rgdco p q k)
  = k' (rgdcop (eval_poly e p) (eval_poly e q)).
Proof. by move=> Pk; rewrite eval_Size (eval_Rgdco_rec k'). Qed.

Lemma qf_Rgdco p q k : (forall r, rpoly r -> qf (k r))
  -> rpoly p -> rpoly q -> qf (Rgdco p q k).
Proof. by move=> Pk rp rq; apply: qf_Size => // n; apply: qf_Rgdco_rec. Qed.


(* Definition ex_elim_seq (ps : seq polyF) (q : polyF) := *)
(*   bind r <- BigRgcd ps; bind g <- Rgdco q r; *)
(*   bind sg <- Size g; Bool (sg != 1%N). *)

(* Lemma eval_ex_elim_seq e ps q : *)
(*   let gp := (\big[@rgcdp _/0%:P]_(p <- ps)(eval_poly e p)) in *)
(*     qf_eval e (ex_elim_seq ps q) = (size (rgdcop (eval_poly e q) gp) != 1%N). *)
(* Proof. *)
(* by do ![rewrite (eval_BigRgcd,eval_Rgdco,eval_Size,eval_lift) //= | move=> * //=]. *)
(* Qed. *)

(* Lemma qf_ex_elim_seq ps q : rseq_poly ps -> rpoly q *)
(*   -> qf (ex_elim_seq ps q). *)
(* Proof. *)
(* move=> rps rq; apply: qf_BigRgcd=> // g rg. *)
(* by apply: Rgdco_qf=> // d rd; apply: qf_Size. *)
(* Qed. *)

Fixpoint Var (s : seq (term F)) : cps nat := fun k =>
  if s is a :: q then
    bind v <- Var q;
    If (Lt (a * head 0 q) 0)%oT Then k (1 + v)%N Else k v
    else k 0%N.

Lemma eval_Var e s k : qf_eval e (Var s k)
  = qf_eval e (k (var (map (eval e) s))).
Proof.
elim: s k=> //= a q ihq k; rewrite ihq eval_If /= -nth0.
have [->|q_neq0] := eqVneq q [::]; first by rewrite /= mulr0 ltrr add0n.
by rewrite -(nth_map _ 0) ?lt0n ?size_eq0 // ?nth0; case: ltrP.
Qed.

Lemma qf_Var s k : all (@rterm _) s -> (forall n, qf (k n)) -> qf (Var s k).
Proof.
elim: s k=> [|a s ihs] k //= /andP[ra rs] qfk //=.
rewrite ihs // => n; rewrite qf_If //= ra /= andbT.
by case: s rs {ihs}=> //= h ? /andP[].
Qed.

Fixpoint Horner (p : polyF) (x : term F) : term F :=
  if p is a :: p then (Horner p x * x + a)%oT else 0%oT.

Lemma eval_Horner e p x : eval e (Horner p x) = (eval_poly e p).[eval e x].
Proof.
elim: p=> //= [|a p ihp]; first by rewrite horner0.
by rewrite !horner_lin ihp.
Qed.

Lemma rHorner p x : rpoly p -> rterm x -> rterm (Horner p x).
Proof. by elim: p=> //= a p ihp /andP[-> rp] rx; rewrite rx ihp. Qed.

Definition Varp sp x := Var [seq (Horner p x) | p <- sp].

Lemma eval_Varp e sp x k : qf_eval e (Varp sp x k) =
  qf_eval e (k (varp (map (eval_poly e) sp) (eval e x))).
Proof.
rewrite eval_Var /varp; congr (qf_eval _ (k (var _))).
by rewrite -!map_comp; apply: eq_map=> p /=; rewrite eval_Horner.
Qed.

Lemma qf_Varp sp x k : all rpoly sp -> rterm x ->
  (forall n : nat, qf (k n)) -> qf (Varp sp x k).
Proof.
move=> rsp rx qfk; rewrite qf_Var // all_map; apply/allP=> p hp /=.
by rewrite rHorner // (allP rsp).
Qed.

Definition VarpI (a b : term F) (sp : seq polyF) (k : zint -> fF) : fF :=
  bind va <- Varp sp a; bind vb <- Varp sp b; k (va%:Z - vb%:Z).

Lemma eval_VarpI e a b sp k :
  qf_eval e (VarpI a b sp k) =
  qf_eval e (k (varpI (eval e a) (eval e b) (map (eval_poly e) sp))).
Proof. by rewrite !eval_Varp. Qed.

Lemma qf_VarpI a b sp k : rterm a -> rterm b -> all rpoly sp ->
  (forall n : zint, qf (k n)) -> qf (VarpI a b sp k).
Proof. by move=> ra rb rsp qfk; rewrite qf_Varp=> // n; rewrite qf_Varp. Qed.

Fixpoint Sremps_rec (p q : polyF) n : cps (seq polyF) := fun k =>
  if n is n.+1 then
    bind p_null <- Isnull p;
    if p_null then k [::]
      else
        bind lq <- LeadCoef q;
        bind spq <- Rscal p q;
        bind mpq <- Rmod p q;
        bind r <- Sremps_rec q (MulPoly [::(- lq ^+ spq)%oT] mpq) n;
        k (p :: r)
    else k [::].

Implicit Arguments eval_Rediv [e p q k].
Prenex Implicits eval_Rediv.

Lemma eval_Sremps_rec e p q n k k' :
  (forall sp, qf_eval e (k sp) = k' (map (eval_poly e) sp)) ->
  qf_eval e (Sremps_rec p q n k) =
  k' (sremps_rec (eval_poly e p) (eval_poly e q) n).
Proof.
elim: n p q k k'=> [|n ihn] p q k k' Pk; first by rewrite /= Pk.
rewrite /= eval_Isnull; have [|ep_neq0] := altP (_ =P _); first by rewrite Pk.
pose q' := eval_poly e q; pose p' := eval_poly e p.
rewrite (eval_LeadCoef (fun lq =>
  k' (p' :: sremps_rec q' (- lq ^+ rscalp p' q' *: rmodp p' q') n))) //.
move=> lq; rewrite (eval_Rediv (fun spq =>
  k' (p' :: sremps_rec q' (- (eval e lq)  ^+ spq.1.1%PAIR *: rmodp p' q') n))) //.
move=> /= spq _ _; rewrite (eval_Rediv (fun mpq =>
  k' (p' :: sremps_rec q' (- (eval e lq)  ^+ spq *: mpq.2%PAIR) n))) //.
move=> /= _ _ mpq; rewrite (ihn _ _ _ (fun r => k' (p' :: r))) //.
  by rewrite !eval_OpPoly /= mul0r add0r addr0 eval_map_mul /=.
by move=> sp; rewrite Pk.
Qed.

Definition Sremps (p q : polyF) : cps (seq polyF) := fun k =>
  bind sp <- Size p; bind sq <- Size q;
  Sremps_rec p q (maxn sp sq.+1) k.

Lemma eval_Sremps e p q k k' :
  (forall sp, qf_eval e (k sp) = k' (map (eval_poly e) sp)) ->
  qf_eval e (Sremps p q k) = k' (sremps (eval_poly e p) (eval_poly e q)).
Proof. by move=> Pk; rewrite !eval_Size; apply: eval_Sremps_rec. Qed.

Implicit Arguments eval_Sremps [e p q k].
Prenex Implicits eval_Sremps.

Fixpoint Deriv (p : polyF) : polyF :=
  if p is a :: q then (AddPoly q (0%oT :: Deriv q)) else [::].

Lemma eval_Deriv e p : eval_poly e (Deriv p) = (eval_poly e p)^`().
Proof.
elim: p=> [|a p ihp] /=; first by rewrite deriv0.
by rewrite eval_AddPoly /= addr0 ihp !derivE.
Qed.

Notation taq' p a b q := (varpI a b (sremps p (p^`() * q))).

Definition Taq (p : polyF) (a b : term F) (q : polyF) : cps zint := fun k =>
  bind r <- Sremps p (MulPoly (Deriv p) q); VarpI a b r k.

Lemma eval_Taq e a b p q k :
  qf_eval e (Taq p a b q k) =
  qf_eval e (k (taq' (eval_poly e p) (eval e a) (eval e b) (eval_poly e q))).
Proof.
rewrite (eval_Sremps (fun r => qf_eval e (k (varpI (eval e a) (eval e b) r)))).
  by rewrite eval_MulPoly eval_Deriv.
by move=> sp; rewrite !eval_Varp.
Qed.

Definition PolyComb (sq : seq polyF) (sc : seq zint) :=
  \big[MulPoly/[::1%oT]]_(i < size sq)
  ExpPoly (nth [::] sq i) (comb_exp sc`_i).

Lemma eval_PolyComb e sq sc :
  eval_poly e (PolyComb sq sc) = poly_comb (map (eval_poly e) sq) sc.
Proof.
rewrite /PolyComb /poly_comb size_map.
apply: (big_ind2 (fun u v => eval_poly e u = v)).
+ by rewrite /= mul0r add0r.
+ by move=> x x' y y'; rewrite eval_MulPoly=> -> ->.
by move=> i _; rewrite eval_ExpPoly /= (nth_map [::]).
Qed.

Definition pcq (sq : seq {poly F}) i :=
  (map (poly_comb sq) (sg_tab (size sq)))`_i.

Definition Pcq sq i := (nth [::] (map (PolyComb sq) (sg_tab (size sq))) i).

Lemma eval_Pcq e sq i :
  eval_poly e (Pcq sq i) = pcq (map (eval_poly e) sq) i.
Proof.
rewrite /Pcq /pcq size_map; move: (sg_tab _)=> s.
have [ge_is|lt_is] := leqP (size s) i.
  by rewrite !nth_default ?size_map // /=.
rewrite -(nth_map _ 0) ?size_map //; congr _`_i; rewrite -map_comp.
by apply: eq_map=> x /=; rewrite eval_PolyComb.
Qed.

Definition Staq (p : polyF) (a b : term F) (sq : seq polyF) (i : nat) :
  cps (term F) := fun k => bind n <- Taq p a b (Pcq sq i); k ((n%:~R) %:T)%oT.

Lemma eval_Staq e p a b sq i k k' :
  (forall x, qf_eval e (k x) = k' (eval e x)) ->
  qf_eval e (Staq p a b sq i k) =
  k' (staq (eval_poly e p) (eval e a) (eval e b) (map (eval_poly e) sq) i).
Proof. by move=> Pk; rewrite /Staq /staq eval_Taq Pk /= eval_Pcq. Qed.

Implicit Arguments eval_Staq [e p a b sq i k].
Prenex Implicits eval_Staq.

Definition ProdStaqCoefs (p : polyF) (a b : term F)
  (sq : seq polyF) : cps (term F) := fun k =>
  let fix aux s (i : nat) k := if i is i'.+1
    then bind x <- Staq p a b sq i';
      aux (x * (coefs _ (size sq) i')%:T + s)%oT i' k
    else k s in
   aux 0%oT (3 ^ size sq)%N k.

Lemma eval_ProdStaqCoefs e p a b sq k k' :
  (forall x, qf_eval e (k x) = k' (eval e x)) ->
  qf_eval e (ProdStaqCoefs p a b sq k) =
  k' (prod_staq_coefs (eval_poly e p)
    (eval e a) (eval e b) (map (eval_poly e) sq)).
Proof.
move=> Pk; rewrite /ProdStaqCoefs /prod_staq_coefs.
set Aux := (fix Aux s i k := match i with 0 => _ | _ => _ end).
set aux := (fix aux s i := match i with 0 => _ | _ => _ end).
rewrite size_map -[0]/(eval e 0%oT); move: 0%oT=> x.
elim: (_ ^ _)%N k k' Pk x=> /= [|n ihn] k k' Pk x.
  by rewrite Pk.
rewrite (eval_Staq
  (fun y => k' (aux (y * (coefs F (size sq) n) + eval e x) n))).
  by rewrite size_map.
by move=> y; rewrite (ihn _ k').
Qed.

Implicit Arguments eval_ProdStaqCoefs [e p a b sq k].
Prenex Implicits eval_ProdStaqCoefs.

Import AbsrNotation.

Definition Absr (x : term F) : cps (term F) := fun k =>
  (If Lt 0 x Then k x Else k (- x))%oT.

Lemma eval_Absr e x k k' : (forall x, qf_eval e (k x) = k' (eval e x)) ->
  qf_eval e (Absr x k) = k' `|(eval e x)|.
Proof. by move=> Pk; rewrite eval_If !Pk /=;case: absrP; rewrite ?oppr0. Qed.

Implicit Arguments eval_Absr [e x k].
Prenex Implicits eval_Absr.

Lemma qf_Absr x k : (forall x, rterm x -> qf (k x)) -> rterm x
  -> qf (Absr x k).
Proof. by move=> qfk rx; rewrite qf_If ?qfk. Qed.

Fixpoint SumAbs n (f : nat -> term F) : cps (term F) := fun k =>
  if n is n.+1 then
    bind a <- Absr (f n);
    bind c <- SumAbs n f;
    k (c + a)%oT else k 0%oT.

Lemma eval_SumAbs e n f k k' :
  (forall x, qf_eval e (k x) = k' (eval e x)) ->
  qf_eval e (SumAbs n f k) = k' (\sum_(i < n) `|eval e (f i)|).
Proof.
elim: n k k'=> /= [|n ihn] k k' Pk.
 by rewrite big_ord0 Pk.
rewrite big_ord_recr /=.
rewrite (eval_Absr (fun a => k' (\sum_(i < n) `|eval e (f i)| + a))) //.
move=> x; rewrite (ihn _ (fun c => k' (c + eval e x))) //.
by move=> y; rewrite Pk.
Qed.

Implicit Arguments eval_SumAbs [e n f k].
Prenex Implicits eval_SumAbs.

Lemma qf_SumAbs n f k :
  (forall x, rterm x -> qf (k x)) -> (forall i, rterm (f i)) ->
  qf (SumAbs n f k).
Proof.
elim: n k=> [|n ihn] /= k qfk rf; first by rewrite qfk.
by rewrite qf_Absr=> // x rx; rewrite ihn // => y ry; rewrite qfk //= ry.
Qed.

Definition CauchyBound (p : polyF) : cps (term F) := fun k =>
  bind sp <- Size p; SumAbs sp (nth 0%oT p) k.

Lemma eval_CauchyBound e p k k' :
  monic (eval_poly e p) -> (forall x, qf_eval e (k x) = k' (eval e x)) ->
  qf_eval e (CauchyBound p k) = k' (cauchy_bound (eval_poly e p)).
Proof.
move=> mp Pk; rewrite /CauchyBound /cauchy_bound.
rewrite eval_Size (monicP mp) absr1 invr1 mul1r (eval_SumAbs k') //.
congr k'; apply: eq_big=> //= i _.
elim: p {mp} i=> /= [|a p ihp] i; first by rewrite nth_nil coef0.
move: i; rewrite size_amulX.
have [->|ep_neq0//] /= := altP (_ =P 0).
  have [->|ea_neq0//] /= := altP (_ =P 0); first by case.
  rewrite size_poly0=> i.
  by rewrite ord1 mul0r add0r polyseqC ea_neq0 /=.
rewrite -poly_cons_def polyseq_cons /nilp size_poly_eq0 ep_neq0.
rewrite -add1n; move=> i; have [j ->|j ->] := fintype.splitP i.
  by rewrite ord1 /=.
by rewrite add1n /= ihp.
Qed.

Implicit Arguments eval_CauchyBound [e p k].
Prenex Implicits eval_CauchyBound.

Lemma qf_CauchyBound p k : (forall x, rterm x -> qf (k x)) ->
  rpoly p -> qf (CauchyBound p k).
Proof.
move=> qfk rp; rewrite /CauchyBound qf_Size => // n; rewrite qf_SumAbs=> // i.
by elim: p rp i=> [_|a p ihp /= /andP[ra rp]] [|i] //=; apply: ihp.
Qed.

Fixpoint Has T (P : T -> cps bool) (s : seq T) : cps bool := fun k =>
  if s is x :: s then bind Px <- P x; if Px then k true else Has P s k
  else k false.

Lemma eval_Has T e s P' k P k' : (forall b, qf_eval e (k b) = k' b) ->
  (forall s k k', (forall b, qf_eval e (k b) = k' b) ->
    qf_eval e (P' s k) = k' (P s)) ->
  qf_eval e (@Has T P' s k) = k' (has P s).
Proof.
move=> hk hP; elim: s=> //= x s ihs.
rewrite (hP _ _ (fun Px => if Px then k' true else k' (has P s))).
  by case: (P x).
by case.
Qed.

Implicit Arguments eval_Has [T e s P' k].
Prenex Implicits eval_Has.

Lemma qf_Has T P s k : (forall b, qf (k b)) ->
  (forall x k, (forall b, qf (k b)) -> qf (P x k)) ->
  qf (@Has T P s k).
Proof. by move=> qfk qfP; elim: s=> //= x s ihs; rewrite qfP // => [] []. Qed.

Definition ChangeVarp (p : polyF) : cps polyF := fun k =>
  bind sp <- Size p; bind lp <- LeadCoef p;
  k (AddPoly (ExpPoly [::0; 1] sp.-1)
  (\big[AddPoly/[::]]_(i < sp.-1) (MulPoly
    [::lp ^+ (sp - i.+2) * nth 0 p i] (ExpPoly [::0; 1] i))))%oT.

Lemma eval_polyP e p : eval_poly e p = Poly (map (eval e) p).
Proof. by elim: p=> // a p /= ->; rewrite poly_cons_def. Qed.

Lemma eval_ChangeVarp e p k k' :
  (forall p, monic (eval_poly e p) -> qf_eval e (k p) = k' (eval_poly e p)) ->
  qf_eval e (ChangeVarp p k) = k' (change_varp (eval_poly e p)).
Proof.
move=> Pk; rewrite eval_Size; pose p' := eval_poly e p.
rewrite (eval_LeadCoef (fun lp => k' ('X^(size p').-1 +
  \poly_(i < (size p').-1) (lp ^+ (size p' - i.+2) * p'`_i)))) //.
move=> lp; set q := AddPoly _ _; set q' := _ + _.
suff eqq': eval_poly e q = q'.
  rewrite Pk eqq' // /monic lead_coef_addl ?lead_coefXn //.
  by rewrite size_polyXn (leq_ltn_trans (size_poly _ _)).
rewrite /q /q' !eval_OpPoly eval_ExpPoly /= mul0r add0r addr0 mul1r.
congr (_ + _); move: (size _)=> n; rewrite poly_def.
apply: (big_ind2 (fun u v => eval_poly e u = v))=> //.
  by move=> u u' v v'; rewrite eval_AddPoly=> -> ->.
move=> i _; rewrite !eval_OpPoly /= mul0r add0r addr0.
rewrite eval_map_mul eval_ExpPoly /= !(mul0r, add0r, mul1r, addr0).
rewrite [p']eval_polyP /= coef_Poly.
have [hi|hi] := ltnP i (size p); first by rewrite (nth_map 0%oT).
by rewrite !nth_default // size_map.
Qed.

Implicit Arguments eval_ChangeVarp [e p k].
Prenex Implicits eval_ChangeVarp.

Definition ChangeVarq (a : term F) (q : polyF) : cps polyF := fun k =>
  bind sq <- Size q;
  k (\big[AddPoly/[::]]_(i < sq) (MulPoly
    [::a ^+ (to_even sq - i) * nth 0 q i] (ExpPoly [::0; 1] i)))%oT.

Lemma eval_ChangeVarq e a q k k' :
  (forall p, qf_eval e (k p) = k' (eval_poly e p)) ->
  qf_eval e (ChangeVarq a q k) = k' (change_varq (eval e a) (eval_poly e q)).
Proof.
move=> Pk; rewrite eval_Size /change_varq.
pose a' := eval e a; pose q' := eval_poly e q.
rewrite Pk; congr (k' _); move: (size _)=> n; rewrite poly_def.
apply: (big_ind2 (fun u v => eval_poly e u = v))=> //.
  by move=> u u' v v'; rewrite eval_AddPoly=> -> ->.
move=> i _; rewrite !eval_OpPoly /= !(mul0r, add0r).
rewrite eval_ExpPoly /= !(mul0r, add0r, mul1r, addr0).
rewrite mul_polyC eval_polyP /= coef_Poly.
have [hi|hi] := ltnP i (size q); first by rewrite (nth_map 0%oT).
by rewrite !nth_default // size_map.
Qed.

Implicit Arguments eval_ChangeVarq [e a q k].
Prenex Implicits eval_ChangeVarq.

Fixpoint ChangeVarSq a sq k :=
  if sq is q :: sq
    then bind cq <- ChangeVarq a q; bind csq <- ChangeVarSq a sq;
      k (cq :: csq)
    else k [::].

Lemma eval_ChangeVarSq e a sq k k' :
  (forall sq, qf_eval e (k sq) = k' (map (eval_poly e) sq)) ->
  qf_eval e (ChangeVarSq a sq k) =
  k' (map (change_varq (eval e a)) (map (eval_poly e) sq)).
Proof.
elim: sq k k'=> /= [|q sq ihsq] k k' Pk; first by rewrite Pk.
rewrite (eval_ChangeVarq (fun cq =>
  k' (cq :: map (change_varq (eval e a)) (map (eval_poly e) sq)))) //.
move=> q'; rewrite (ihsq _ (fun csq => k' (eval_poly e q' :: csq))) //.
by move=> sq'; rewrite Pk.
Qed.

Implicit Arguments eval_ChangeVarSq [e a sq k].
Prenex Implicits eval_ChangeVarSq.

Definition ToMonic (p : polyF) (sq : seq polyF) :
  cps (polyF * seq polyF) := fun k =>
  bind lp <- LeadCoef p;
  bind cp <- ChangeVarp p; bind csq <- ChangeVarSq lp sq;
  k (cp, csq).

Lemma eval_ToMonic e p sq k k' :
  (forall p sq, monic (eval_poly e p) -> qf_eval e (k (p, sq)) =
    k' (eval_poly e p, map (eval_poly e) sq)) ->
  qf_eval e (ToMonic p sq k) =
  k' (to_monic (eval_poly e p) (map (eval_poly e) sq)).
Proof.
move=> Pk; pose p' := eval_poly e p; pose sq' := map (eval_poly e) sq.
rewrite (eval_LeadCoef (fun lp => k'
  (change_varp p', map (change_varq lp) sq'))) //.
move=> lp; rewrite (eval_ChangeVarp (fun cp => k'
  (cp, map (change_varq (eval e lp)) sq'))) //.
move=> cp mcp.
rewrite (eval_ChangeVarSq (fun csq => k' (eval_poly e cp, csq))) //.
by move=> csq; apply: Pk.
Qed.

Implicit Arguments eval_ToMonic [e p sq k].
Prenex Implicits eval_ToMonic.

Definition MajNotRoot (x : term F) (p : polyF) : cps (term F) := fun k =>
  bind sp <- Size p;
  Pick (fun i : 'I_sp.+1 => Horner p (x + i.+1%:R) != 0)%oT
  (fun i => k (x + i.+1%:R))%oT (k (x + 1)%oT).

Lemma eval_MajNotRoot e x p k k' :
  (forall x, qf_eval e (k x) = k' (eval e x)) ->
  qf_eval e (MajNotRoot x p k) = k' (maj_not_root (eval e x) (eval_poly e p)).
Proof.
move=> Pk; rewrite eval_Size eval_Pick /maj_not_root /=.
set f := (fun i => ~~ root _ _); rewrite (@eq_pick _ _ f); last first.
  by move=> i; rewrite /= eval_Horner.
by case: pickP=> ?; rewrite Pk.
Qed.

Implicit Arguments eval_MajNotRoot [e x p k].
Prenex Implicits eval_MajNotRoot.

Fixpoint SymPoly p :=
  if p is a :: p
    then AddPoly (MulPoly (OppPoly (SymPoly p)) [::0; 1]%oT) [::a]
    else [::].

Lemma eval_SymPoly e p : eval_poly e (SymPoly p) = (eval_poly e p) \Po (-'X).
Proof.
elim: p=> [|a p ihp]; first by rewrite comp_poly0p //.
rewrite /= !eval_OpPoly /= !(mul0r, add0r, mul1r, addr0) ihp.
by rewrite comp_poly_addl comp_polyCp comp_poly_mull comp_polyXp mulrN mulNr.
Qed.

Definition PickRight x p := MajNotRoot x (MulPoly (SymPoly p) p).

Lemma eval_PickRight e x p k k' :
  (forall x, qf_eval e (k x) = k' (eval e x)) ->
  qf_eval e (PickRight x p k) = k' (pick_right (eval e x) (eval_poly e p)).
Proof.
move=> Pk; rewrite (eval_MajNotRoot k'); last by [].
by rewrite /pick_right !eval_OpPoly eval_SymPoly.
Qed.

Implicit Arguments eval_PickRight [e x p k].
Prenex Implicits eval_PickRight.

Fixpoint ProdPoly T (s : seq T) (f : T -> cps polyF) : cps polyF := fun k =>
  if s is a :: s then
    bind fa <- f a;
    bind fs <- ProdPoly s f;
    k (MulPoly fa fs)
    else k [::1%oT].

Lemma eval_ProdPoly e T s f k f' k' :
  (forall x k k', (forall p, (qf_eval e (k p) = k' (eval_poly e p))) ->
  qf_eval e (f x k) = k' (f' x)) ->
  (forall p, qf_eval e (k p) = k' (eval_poly e p)) ->
  qf_eval e (@ProdPoly T s f k) = k' (\prod_(x <- s) f' x).
Proof.
move=> Pf; elim: s k k'=> [|a s ihs] k k' Pk /=.
  by rewrite big_nil Pk /= !(mul0r, add0r).
rewrite (Pf _ _ (fun fa => k' (fa * \prod_(x <- s) f' x))).
  by rewrite big_cons.
move=> fa; rewrite (ihs _ (fun fs => k' (eval_poly e fa * fs))) //.
by move=> fs; rewrite Pk eval_OpPoly.
Qed.

Implicit Arguments eval_ProdPoly [e T s f k].
Prenex Implicits eval_ProdPoly.

Definition CcountWeak (p : polyF) (sq : seq polyF) : cps (term F) := fun k =>
  bind sp <- Size p;
  if sp == 1%N then k 0%T
    else bind sq0 <- Has Isnull sq;
      if sq0 then k 0%oT
      else
        bind cpsq <- ToMonic p sq;
        let (p', sq') := cpsq in
        bind sq_aux <- ProdPoly (index_enum [finType of 'I_(3 ^ size sq')])
        (fun i k =>
          bind sr <- Sremps p' (MulPoly (Deriv p') (Pcq sq' i));
          k (\big[MulPoly/[::1%oT]]_(r <- sr) r));
        bind cbound <- CauchyBound p';
        bind bound <- PickRight cbound sq_aux;
        ProdStaqCoefs p' (- bound) bound sq' k.

Lemma eval_CcountWeak e p sq k k' :
  (forall x, qf_eval e (k x) = k' (eval e x)) ->
  qf_eval e (CcountWeak p sq k) =
  k' (ccount_weak (eval_poly e p) (map (eval_poly e) sq)).
Proof.
move=> Pk; rewrite eval_Size /ccount_weak.
have [|sp_neq1] := altP eqP; first by rewrite Pk.
pose isnull p := eval_poly e p == 0.
rewrite (eval_Has isnull (fun n =>
  if n then k' 0 else
  let '(p', sq') := to_monic (eval_poly e p) (map (eval_poly e) sq) in
       let sq_aux :=
         \prod_(j < 3 ^ size sq')
            \prod_(r <- sremps p'
                          (p'^`() *
                           (map (poly_comb sq') (sg_tab (size sq')))`_j)) r in
       let bound := pick_right (cauchy_bound p') sq_aux in
       k' (prod_staq_coefs p' (- bound) bound sq')
)); first 2 last.
+ by move=> *; rewrite eval_Isnull.
+ rewrite has_map [has (preim _ _) _](@eq_has _ _ isnull) //.
  by case: has.
move=> []; first by rewrite Pk.
rewrite (eval_ToMonic (fun cpsq =>
  let '(p', sq') := cpsq in
       let sq_aux :=
         \prod_(j < 3 ^ size sq')
            \prod_(r <- sremps p'
                          (p'^`() *
                           (map (poly_comb sq') (sg_tab (size sq')))`_j)) r in
       let bound := pick_right (cauchy_bound p') sq_aux in
       k' (prod_staq_coefs p' (- bound) bound sq')
)) //.
move=> cp csq mcp; pose cp' := eval_poly e cp.
pose csq' := map (eval_poly e) csq.
rewrite (eval_ProdPoly (fun j : 'I__ => \prod_(r <- sremps cp'
  (cp'^`() *
    (map (poly_comb csq') (sg_tab (size csq')))`_j)) r)
(fun sq_aux => let bound := pick_right (cauchy_bound cp') sq_aux in
  k' (prod_staq_coefs cp' (- bound) bound csq'))).
+ by rewrite !size_map.
+ move=> i {k k' Pk} k k' Pk.
  rewrite (eval_Sremps (fun sr => k' (\prod_(r <- sr) r))).
    by rewrite eval_MulPoly eval_Deriv eval_Pcq /pcq size_map.
  move=> sp; rewrite Pk big_map; congr k'.
  apply: (big_ind2 (fun u v => eval_poly e u = v))=> //.
    by rewrite /= mul0r add0r.
  by move=> u u' v v'; rewrite eval_MulPoly=> -> ->.
move=> r; rewrite (eval_CauchyBound (fun cbound =>
       let bound := pick_right cbound (eval_poly e r) in
       k' (prod_staq_coefs cp' (- bound) bound csq'))) //.
move=> cbound; rewrite (eval_PickRight (fun bound =>
  k' (prod_staq_coefs cp' (- bound) bound csq'))) //.
by move=> bound; rewrite (eval_ProdStaqCoefs k').
Qed.

Fixpoint abstrX (i : nat) (t : term F) :=
  match t with
    | (GRing.Var n) => if n == i then [::Const 0; Const 1] else [::t]
    | (GRing.Opp x) => OppPoly (abstrX i x)
    | (GRing.Add x y) => AddPoly (abstrX i x) (abstrX i y)
    | (GRing.Mul x y) => MulPoly (abstrX i x) (abstrX i y)
    | (GRing.NatMul x n) => NatMulPoly n (abstrX i x)
    | (GRing.Exp x n) => let ax := (abstrX i x) in
      iter n (MulPoly ax) [::Const 1]
    | _ => [::t]
  end.

Lemma abstrXP e i t x : rterm t
  -> (eval_poly e (abstrX i t)).[x] = eval (set_nth 0 e i x) t.
Proof.
move=> rt; elim: t rt.
- move=> n /= rt; case ni: (_ == _);
    rewrite //= ?(mul0r,add0r,addr0,polyC1,mul1r,hornerX,hornerC);
    by rewrite // nth_set_nth /= ni.
- by move=> r rt; rewrite /= mul0r add0r hornerC.
- by move=> r rt; rewrite /= mul0r add0r hornerC.
- by move=> t tP s sP; case/andP=>??; rewrite /= eval_AddPoly horner_add tP ?sP.
- by move=> t tP rt; rewrite /= eval_OppPoly horner_opp tP.
- by move=> t tP n rt; rewrite /= eval_NatMulPoly horner_mulrn tP.
- by move=> t tP s sP; case/andP=>??; rewrite /= eval_MulPoly horner_mul tP ?sP.
- by move=> t tP.
- move=> t tP /=; elim; first by rewrite /= expr0 mul0r add0r hornerC.
  by move=> n ihn rt; rewrite /= eval_MulPoly exprSr horner_mul ihn ?tP // mulrC.
Qed.

Lemma rabstrX i t : rterm t -> rpoly (abstrX i t).
Proof.
elim: t; do ?[ by move=> * //=; do ?case: (_ == _)].
- move=> t irt s irs /=; case/andP=> rt rs.
  by apply: rAddPoly; rewrite ?irt ?irs //.
- by move=> t irt /= rt; rewrite rpoly_map_mul ?irt //.
- by move=> t irt /= n rt; rewrite rpoly_map_mul ?irt //.
- move=> t irt s irs /=; case/andP=> rt rs.
  by apply: rMulPoly; rewrite ?irt ?irs //.
- move=> t irt /= n rt; move: (irt rt)=> {rt} rt; elim: n => [|n ihn] //=.
  exact: rMulPoly.
Qed.

Implicit Types tx ty : term F.

Lemma abstrX_mul i : {morph abstrX i : x y / GRing.Mul x y >-> MulPoly x y}.
Proof. done. Qed.
Lemma abstrX1  i : abstrX i (Const 1) = [::Const 1].
Proof. done. Qed.

Lemma eval_poly_mul : forall e, {morph eval_poly e : x y / MulPoly x y >-> GRing.mul x y}.
Proof. by move=> e x y; rewrite eval_MulPoly. Qed.
Lemma eval_poly1 : forall e, eval_poly e [::Const 1] = 1.
Proof. by move=> e //=; rewrite mul0r add0r. Qed.

Notation abstrX_bigmul := (big_morph _ (abstrX_mul _) (abstrX1 _)).
Notation eval_bigmul := (big_morph _ (eval_poly_mul _) (eval_poly1 _)).
Notation bigmap_id := (big_map _ (fun _ => true) id).

Lemma rseq_poly_map x ts : all (@rterm _) ts -> rseq_poly (map (abstrX x) ts).
Proof. by elim: ts=> //= t ts iht /andP[rt rts]; rewrite rabstrX // iht. Qed.

End proj_qe_rcf.