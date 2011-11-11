Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype path.
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

Fixpoint eval_poly (e : seq F) pf :=
  if pf is c :: qf then (eval_poly e qf) * 'X + (eval e c)%:P else 0.

Definition rpoly p := (all (@rterm F) p).

Notation "'bind' x <- y ; z" :=
  (y (fun x => z)) (at level 200, x at level 0, y at level 0,
    format "'[hv' 'bind'  x  <-  y ; '/' z ']'").

Fixpoint Size (p : polyF) (k : nat -> fF) :=
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

Definition Isnull (p : polyF) (k : bool -> fF) :=
  bind n <- Size p; k (n == 0%N).

Lemma eval_Isnull k p e : qf_eval e (Isnull p k) = qf_eval e (k (eval_poly e p == 0)).
Proof. by rewrite eval_Size size_poly_eq0. Qed.

Lemma qf_Isnull k p : (forall b, qf (k b)) -> rpoly p -> qf (Isnull p k).
Proof. by move=> *; apply: qf_Size. Qed.

Definition LtSize (p q : polyF) (k : bool -> fF) : fF :=
  bind n <- Size p; bind m <- Size q; k (n < m)%N.

Definition lift (p : {poly F}) := let: q := p in map Const q.

Lemma eval_lift e p : eval_poly e (lift p) = p.
Proof.
elim/poly_ind: p => [|p c {2}<-]; first by rewrite /lift polyseq0.
rewrite -poly_cons_def /lift polyseq_cons /nilp /=.
case: polyseq=> //=; rewrite mul0r add0r polyseqC.
by have [->|c_neq0] //= := altP (_ =P _); rewrite mul0r add0r.
Qed.

Fixpoint LeadCoef p (k : term F -> fF) :=
  if p is c :: q then
    bind l <- LeadCoef q; If l == 0 Then k c Else k l
    else k (Const 0).

(* Lemma eval_LeadCoef e p k k' : *)
(*   (forall x, qf_eval e (k x) = (k' (eval e x))) -> *)
(*   qf_eval e (LeadCoef p k) = k' (lead_coef (eval_poly e p)). *)
(* Proof. *)
(* move=> Pk; elim: p k k' Pk=> [|a p ihp] k k' Pk //=. *)
(*   by rewrite lead_coef0 Pk. *)
(* rewrite (ihp _ (fun l => if l == 0 then qf_eval e (k a) else (k' l))); last first. *)
(*   by move=> x; rewrite eval_If /= !Pk. *)
(* rewrite lead_coef_eq0; have [->|p_neq0] := altP (_ =P 0). *)
(*   by rewrite mul0r add0r lead_coefC. *)
(* rewrite lead_coef_addl ?lead_coef_mul_monic ?monicX //. *)
(* rewrite size_mul_id ?polyX_eq0 // size_polyX addn2 /= ltnS size_polyC. *)
(* by case: (_ == _)=> //=; rewrite size_poly_gt0. *)
(* Qed. *)

Lemma eval_LeadCoef e p k :
  (forall x, qf_eval e (k x) = qf_eval e (k (Const (eval e x))))
  ->  qf_eval e (LeadCoef p k)
    = qf_eval e (k (Const (lead_coef (eval_poly e p)))).
Proof.
move=> Pk; elim: p k Pk=> [|a p ihp] k Pk //=; first by rewrite lead_coef0.
rewrite ihp ?eval_If /=; last by move=> x; rewrite !eval_If /= -Pk.
rewrite -ihp // lead_coef_eq0; have [->|p_neq0] := altP (_ =P _).
  by rewrite mul0r add0r lead_coefC.
rewrite lead_coef_addl ?lead_coef_mul_monic ?monicX ?ihp //.
rewrite size_mul_id ?polyX_eq0 // size_polyX addn2 /= ltnS size_polyC.
by case: (_ == _)=> //=; rewrite size_poly_gt0.
Qed.

Lemma qf_LeadCoef k p : (forall c, rterm c -> qf (k c))
  -> rpoly p -> qf (LeadCoef p k).
Proof.
elim: p k => /= [k kP _|c q ihp k kP /andP[rc rq]]; first exact: kP.
by rewrite ihp // => c' rc'; rewrite qf_If //= ?andbT // kP.
Qed.

Fixpoint AmulXn (a:term F) (n:nat) : polyF:=
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

Lemma eval_MulPoly p q e :
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
  (c : nat) (qq r : polyF) (n : nat)  (k : nat * polyF * polyF -> fF) {struct n}:=
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


Lemma eval_Rediv_rec_loop e q sq cq c qq r n k
  (d := redivp_rec_loop (eval_poly e q) sq (eval e cq)
      c (eval_poly e qq) (eval_poly e r) n) :
  (forall c qq r, qf_eval e (k (c, qq, r))
    = qf_eval e (k (c, lift (eval_poly e qq), lift (eval_poly e r)))) ->
    qf_eval e (Rediv_rec_loop q sq cq c qq r n k)
    = qf_eval e (k (d.1.1, lift d.1.2, lift d.2)%PAIR).
Proof.
move=> Pk; elim: n c qq r k Pk @d=> [|n ihn] c qq r k Pk /=.
  rewrite eval_Size /=; have [//=|gtq] := ltnP.
  rewrite eval_LeadCoef /=.
    by rewrite Pk !eval_OpPoly /= ?(mul0r, add0r) mul_polyC.
  by move=> x; rewrite Pk [RHS]Pk !eval_OpPoly /= mul_polyC ?(mul0r,add0r).
rewrite eval_Size /=; have [//=|gtq] := ltnP.
rewrite eval_LeadCoef /=.
  by rewrite ihn // !eval_OpPoly /= ?(mul0r, add0r) mul_polyC.
by move=> x; rewrite !ihn // !eval_OpPoly /= ?(mul0r, add0r) mul_polyC.
Qed.

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

Definition Rediv (p : polyF) (q : polyF) (k : nat * polyF * polyF -> fF) : fF :=
  bind b <- Isnull q;
  if b then k (0%N, [::Const 0], p)
    else bind sq <- Size q;
      bind sp <- Size p;
      bind lq <- LeadCoef q;
      Rediv_rec_loop q sq lq 0 [::Const 0] p sp k.

Lemma redivp_rec_loopP q c qq r n : redivp_rec q c qq r n
    = redivp_rec_loop q (size q) (lead_coef q) c qq r n.
Proof. by elim: n c qq r => [| n Pn] c qq r //=; rewrite Pn. Qed.

Lemma eval_Rediv e p q k (d := (redivp (eval_poly e p) (eval_poly e q))) :
  (forall c qq r,  qf_eval e (k (c,qq,r))
    = qf_eval e (k (c, lift (eval_poly e qq), lift (eval_poly e r)))) ->
  qf_eval e (Rediv p q k) = qf_eval e (k (d.1.1, lift d.1.2, lift d.2))%PAIR.
Proof.
move=> Pk; rewrite eval_Isnull /d /redivp.
have [_|p_neq0] /= := boolP (_ == _); first by rewrite Pk /= mul0r add0r.
rewrite !eval_Size eval_LeadCoef /=; last first.
  by move=> x; rewrite !eval_Rediv_rec_loop.
rewrite eval_Rediv_rec_loop /=; last by move=> *; rewrite Pk.
by rewrite mul0r add0r redivp_rec_loopP.
Qed.

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

Fixpoint Rgcd_loop pp n qq k {struct n} :=
  bind r <- Rmod pp qq; bind b <- Isnull r;
  if b then (k qq)
    else if n is n1.+1 then Rgcd_loop qq n1 r k else k r.

Lemma eval_Rgcd_loop e n p q k :
  (forall p, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p))))
  -> qf_eval e (Rgcd_loop p n q k) =
    qf_eval e (k (lift (rgcdp_loop n (eval_poly e p) (eval_poly e q)))).
Proof.
move=> Pk; elim: n p q k Pk => [|n ihn] p q k Pk /=.
  rewrite eval_Rediv; last first.
    by move=> *; rewrite !eval_Isnull eval_lift //= !fun_if -!Pk; do !case: ifP.
  by rewrite eval_Isnull eval_lift /=; case: (_ == _); rewrite -?Pk.
rewrite eval_Rediv /=; last first.
   move=> *; rewrite !eval_Isnull !eval_lift //= !fun_if !ihn //.
   by do !case: ifP=> //; rewrite eval_lift.
rewrite eval_Isnull !eval_lift; case: (_ == _); first by rewrite Pk.
by rewrite ihn //= eval_lift.
Qed.

Lemma qf_Rgcd_loop p q n k : (forall r, rpoly r -> qf (k r)) ->
  rpoly p -> rpoly q -> qf (Rgcd_loop p n q k).
Proof.
move=> kP; elim: n p q k kP => [|n ihn] p q k kP rp rq /=.
  apply: qf_Rediv=> // r; case/andP=> _ rr.
  by apply: qf_Isnull=> // [[]]; apply: kP.
apply: qf_Rediv=> // r; case/andP=> _ rr.
apply: qf_Isnull=> // [[]]; first exact: kP.
exact: ihn.
Qed.

Definition Rgcd (p:polyF) (q:polyF) k : fF :=
  let aux p1 q1 k := bind b <- Isnull p1;
    if b then k q1 else bind n <- Size p1; Rgcd_loop p1 n q1 k in
  bind b <- LtSize p q;
  if b then aux q p k else aux p q k.

Lemma eval_Rgcd e p q k :
  (forall p, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p)))) ->
  qf_eval e (Rgcd p q k) =
  qf_eval e (k (lift (rgcdp (eval_poly e p) (eval_poly e q)))).
Proof.
move=> Pk; rewrite /Rgcd !eval_Size.
case lqp: (_ < _)%N.
  rewrite eval_Isnull.
  case q0: (_ == _); first by rewrite Pk (eqP q0) rgcdp0.
  rewrite eval_Size eval_Rgcd_loop; first by rewrite /rgcdp lqp q0.
  by move=> p'; rewrite Pk.
rewrite eval_Isnull.
case p0: (_ == _); first by rewrite Pk (eqP p0) rgcd0p.
rewrite eval_Size eval_Rgcd_loop; first by rewrite /rgcdp lqp p0.
by move=> q'; rewrite Pk.
Qed.

Lemma qf_Rgcd p q k :  (forall r, rpoly r -> qf (k r)) ->
  rpoly p -> rpoly q -> qf (Rgcd p q k).
Proof.
move=> kP rp rq; apply: qf_Size=> // n; apply: qf_Size=> // m.
case:(_ < _)%N; apply: qf_Isnull=> //;
by case; do ?apply: kP=> //; apply: qf_Size=> // n'; apply: qf_Rgcd_loop.
Qed.

Fixpoint BigRgcd (ps : seq polyF) k : fF :=
  if ps is p :: pr then bind r <- BigRgcd pr; Rgcd p r k else k [::Const 0].

Lemma eval_BigRgcd e ps k :
  (forall p, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p)))) ->
  qf_eval e (BigRgcd ps k) =
  qf_eval e (k (lift (\big[@rgcdp _/0%:P]_(i <- ps)(eval_poly e i)))).
Proof.
move=> Pk; elim: ps k Pk=> [|p ps ihps] k Pk.
  by rewrite /= big_nil Pk /= mul0r add0r.
rewrite big_cons ihps; first by rewrite eval_Rgcd // eval_lift.
by move=> p'; rewrite !eval_Rgcd; first by rewrite Pk !eval_lift .
Qed.

Definition rseq_poly ps := all rpoly ps.

Lemma qf_BigRgcd ps k :  (forall r, rpoly r -> qf (k r)) ->
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

Lemma eval_Rgdco_rec e p q n k :
  (forall p, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p)))) ->
  qf_eval e (Rgdco_rec p q n k)
    = qf_eval e (k (lift (rgdcop_rec (eval_poly e p) (eval_poly e q) n))).
Proof.
move=> Pk; elim: n p q k Pk => [|n ihn] p q k Pk /=.
  rewrite eval_Isnull /=.
  by case: (_ == _); rewrite Pk /= mul0r add0r ?(polyC0,polyC1).
rewrite eval_Rgcd ?eval_Size ?eval_lift //.
  rewrite /rcoprimep; case se : (_==_); rewrite Pk //.
  by do ?[rewrite (eval_Rgcd, ihn, eval_lift, eval_Rediv) | move=> * //=].
move=> p'; rewrite ?(eval_Size, eval_lift) //; case: (_ == _)=> //.
rewrite // eval_Rediv //=; last by move=> _ qq _; rewrite !ihn // !eval_lift.
rewrite eval_Rediv /=; last by move=> _ qq _; rewrite !ihn // !eval_lift.
by rewrite eval_lift.
Qed.

Lemma qf_Rgdco_rec p q n k : (forall r, rpoly r -> qf (k r)) ->
  rpoly p -> rpoly q -> qf (Rgdco_rec p q n k).
Proof.
move=> Pk rp rq; elim: n p q k Pk rp rq=> [|n ihn] p q k Pk rp rq /=.
apply: qf_Isnull=> //; first by case; rewrite Pk.
apply: qf_Rgcd=> // g rg; apply: qf_Size=> // n'.
case:(_ == _); first exact: Pk.
by apply: qf_Rediv=> // g' /andP[rg12 rg2]; apply: ihn.
Qed.

Definition Rgdco q p k := bind sp <- Size p; (Rgdco_rec q p sp k).

Lemma eval_Rgdco e p q k :
  (forall p, qf_eval e (k p) = qf_eval e (k (lift (eval_poly e p)))) ->
  qf_eval e (Rgdco p q k)
  = qf_eval e (k (lift (rgdcop (eval_poly e p) (eval_poly e q)))).
Proof. by move=> *; rewrite eval_Size eval_Rgdco_rec 1?Pk. Qed.

Lemma Rgdco_qf : forall p k q, (forall r, rpoly r -> qf (k r))
  -> rpoly p -> rpoly q -> qf (Rgdco p q k).
Proof.
by move=> p k q kP rp rq; apply: qf_Size => // n; apply: qf_Rgdco_rec.
Qed.


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

Definition Ediv p q k :=
  bind r <- Rediv p q;
  let: (c, d, r) := r in
    bind l <- LeadCoef q;
    If (l != 0) Then k (0%N, MulPoly [::l ^- c] d, MulPoly [::l ^- c] r)%oT
    Else k (c, d, r).

Definition Mod (p : polyF) (q : polyF) (k : polyF -> fF) : fF :=
  Ediv p q (fun d => k d.2)%PAIR.
Definition Div (p : polyF) (q : polyF) (k : polyF -> fF) : fF :=
  Ediv p q (fun d => k d.1.2)%PAIR.
Definition Scal (p : polyF) (q : polyF) (k : nat -> fF) : fF :=
  Ediv p q (fun d => k d.1.1)%PAIR.
Definition Dvd (p : polyF) (q : polyF) (k : bool -> fF) : fF :=
  bind r <- Mod p q; bind r_null <- Isnull r; k r_null.


Lemma eval_Ediv e p q k (d := (edivp (eval_poly e p) (eval_poly e q))) :
  (forall c qq r,  qf_eval e (k (c,qq,r))
    = qf_eval e (k (c, lift (eval_poly e qq), lift (eval_poly e r)))) ->
  qf_eval e (Ediv p q k) = qf_eval e (k (d.1.1, lift d.1.2, lift d.2))%PAIR.
Proof.
move=> Pk; rewrite eval_Isnull /d /edivp /=.
rewrite unitfE lead_coef_eq0; have [q_eq0|q_neq0] /= := altP (_ =P _).
  rewrite eval_LeadCoef /=; last first.
    move=> x; rewrite !eval_If /=.
    by rewrite Pk [in RHS]Pk /= !eval_OpPoly !expr0 !eval_map_mul.
  rewrite eval_If /= lead_coef_eq0 q_eq0 eqxx /=.
  rewrite redivp_def /= rdivp0 rmodp0 Pk /= mul0r add0r /=.
  admit.
rewrite !eval_Size eval_LeadCoef; last first.
  move=> x; rewrite !eval_Rediv_rec_loop //.
Admitted.
(* This shows the limits of this method *)

(*  first by rewrite Pk /= mul0r add0r. *)
(* rewrite !eval_Size eval_LeadCoef /=; last first. *)
(*   by move=> x; rewrite !eval_Rediv_rec_loop. *)
(* rewrite eval_Rediv_rec_loop /=; last by move=> *; rewrite Pk. *)
(* by rewrite mul0r add0r redivp_rec_loopP. *)
(* Qed. *)

(* Definition ex_elim (x : nat) (pqs : seq (term F) * seq (term F)) := *)
(*   ex_elim_seq (map (abstrX x) pqs.1)%PAIR  *)
(*   (abstrX x (\big[GRing.Mul/Const 1]_(q <- pqs.2) q))%PAIR. *)

(* Lemma qf_ex_elim x pqs : dnf_rterm pqs -> qf (ex_elim x pqs). *)
(* Proof. *)
(* move=> x [ps qs]; case/andP=> /= rps rqs. *)
(* apply: qf_ex_elim_seq; first exact: rseq_poly_map. *)
(* apply: rabstrX=> /=. *)
(* elim: qs rqs=> [|t ts iht] //=; first by rewrite big_nil. *)
(* by case/andP=> rt rts; rewrite big_cons /= rt /= iht. *)
(* Qed. *)

(* Lemma holds_conj : forall e i x ps, all (@rterm _) ps -> *)
(*   (holds (set_nth 0 e i x) (foldr (fun t : term F => And (t == 0)) True ps) *)
(*   <-> all ((@root _)^~ x) (map (eval_poly e \o abstrX i) ps)). *)
(* Proof. *)
(* move=> e i x; elim=> [|p ps ihps] //=. *)
(* case/andP=> rp rps; rewrite rootE abstrXP //. *)
(* constructor; first by case=> -> hps; rewrite eqxx /=; apply/ihps. *)
(* by case/andP; move/eqP=> -> psr; split=> //; apply/ihps.  *)
(* Qed. *)

(* Lemma holds_conjn : forall e i x ps, all (@rterm _) ps -> *)
(*   (holds (set_nth 0 e i x) (foldr (fun t : term F => And (t != 0)) True ps) *)
(*   <-> all (fun p => ~~root p x) (map (eval_poly e \o abstrX i) ps)). *)
(* Proof. *)
(* move=> e i x; elim=> [|p ps ihps] //=. *)
(* case/andP=> rp rps; rewrite rootE abstrXP //. *)
(* constructor; first by case=> /eqP-> hps /=; apply/ihps. *)
(* by case/andP=> pr psr; split; first apply/eqP=> //; apply/ihps.  *)
(* Qed. *)


(* Lemma holds_ex_elim : GRing.valid_QE_proj ex_elim. *)
(* Proof. *)
(* move=> i [ps qs] /= e; case/andP=> /= rps rqs. *)
(* rewrite eval_ex_elim_seq big_map. *)
(* have -> : \big[@rgcdp _/0%:P]_(j <- ps) eval_poly e (abstrX i j) *)
(*     =  \big[@rgcdp _/0%:P]_(j <- (map (eval_poly e) (map (abstrX i) (ps)))) j. *)
(*   by rewrite !big_map. *)
(* rewrite -!map_comp. *)
(*   have aux I (l : seq I) (P : I -> {poly F}) : *)
(*     \big[(@gcdp F)/0]_(j <- l) P j %= \big[(@rgcdp F)/0]_(j <- l) P j. *)
(*     elim: l => [| u l ihl] /=; first by rewrite !big_nil eqpxx. *)
(*     rewrite !big_cons; move: ihl; move/(eqp_gcdr (P u)) => h. *)
(*     apply: eqp_trans h _; rewrite eqp_sym; exact: eqp_rgcd_gcd. *)
(* case g0: (\big[(@rgcdp F)/0%:P]_(j <- map (eval_poly e \o abstrX i) ps) j == 0). *)
(*   rewrite (eqP g0) rgdcop0. *)
(*   case m0 : (_ == 0)=> //=; rewrite ?(size_poly1,size_poly0) //=. *)
(*     rewrite abstrX_bigmul eval_bigmul -bigmap_id in m0. *)
(*     constructor=> [[x] // []] //. *)
(*     case=> _; move/holds_conjn=> hc; move/hc:rqs. *)
(*     by rewrite -root_bigmul //= (eqP m0) root0. *)
(*   constructor; move/negP:m0; move/negP=>m0. *)
(*   case: (ex_px_neq0 axiom m0)=> x {m0}. *)
(*   rewrite abstrX_bigmul eval_bigmul -bigmap_id. *)
(*   rewrite root_bigmul=> m0. *)
(*   exists x; do 2?constructor=> //. *)
(*     apply/holds_conj; rewrite //= -root_biggcd. *)
(*     by rewrite (eqp_root (aux _ _ _ )) (eqP g0) root0. *)
(*   by apply/holds_conjn. *)
(* apply:(iffP (root_size_neq1 axiom _)); case=> x Px; exists x; move:Px => //=. *)
(*   rewrite (eqp_root (eqp_rgdco_gdco _ _)). *)
(*   rewrite root_gdco ?g0 //. *)
(*   rewrite -(eqp_root (aux _ _ _ )) root_biggcd. *)
(*   rewrite abstrX_bigmul eval_bigmul -bigmap_id root_bigmul. *)
(*   case/andP=> psr qsr. *)
(*   do 2?constructor. *)
(*     by apply/holds_conj. *)
(*   by apply/holds_conjn. *)
(* rewrite (eqp_root (eqp_rgdco_gdco _ _)). *)
(* rewrite root_gdco ?g0 // -(eqp_root (aux _ _ _ )) root_biggcd. *)
(* rewrite abstrX_bigmul eval_bigmul -bigmap_id root_bigmul=> [[] // [hps hqs]]. *)
(* apply/andP; constructor. *)
(*   by apply/holds_conj. *)
(* by apply/holds_conjn. *)
(* Qed. *)

(* Lemma wf_ex_elim : GRing.wf_QE_proj ex_elim. *)
(* Proof. by move=> i bc /= rbc; apply: qf_ex_elim. Qed. *)

(* Definition closed_fields_QEMixin :=  *)
(*   QEdecFieldMixin wf_ex_elim holds_ex_elim. *)


End proj_qe_rcf.