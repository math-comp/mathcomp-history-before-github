Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import finfun path.
Require Import bigop ssralg poly polydiv ssrnum zmodp div ssrint.
Require Import polyorder polyrcf interval polyXY.
Require Import qe_rcf_th ordered_qelim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Local Open Scope nat_scope.
Local Open Scope ring_scope.

Import ord.

Section QF.

Variable R : Type.

Inductive term : Type :=
| Var of nat
| Const of R
| NatConst of nat
| Add of term & term
| Opp of term
| NatMul of term & nat
| Mul of term & term
| Exp of term & nat.

Inductive formula : Type :=
| Bool of bool
| Equal of term & term
| Lt of term & term
| Le of term & term
| And of formula & formula
| Or of formula & formula
| Implies of formula & formula
| Not of formula.

Coercion rterm_to_term := fix loop (t : term) : GRing.term R :=
  match t with
    | Var x => GRing.Var _ x
    | Const x => GRing.Const x
    | NatConst n => GRing.NatConst _ n
    | Add u v => GRing.Add (loop u) (loop v)
    | Opp u => GRing.Opp (loop u)
    | NatMul u n  => GRing.NatMul (loop u) n
    | Mul u v => GRing.Mul (loop u) (loop v)
    | Exp u n => GRing.Exp (loop u) n
  end.

Coercion qfr_to_formula := fix loop (f : formula) : ord.formula R :=
  match f with
    | Bool b => ord.Bool b
    | Equal x y => ord.Equal x y
    | Lt x y => ord.Lt x y
    | Le x y => ord.Le x y
    | And f g => ord.And (loop f) (loop g)
    | Or f g => ord.Or (loop f) (loop g)
    | Implies f g => ord.Implies (loop f) (loop g)
    | Not f => ord.Not (loop f)
  end.

Definition to_rterm := fix loop (t : GRing.term R) : term :=
  match t with
    | GRing.Var x => Var x
    | GRing.Const x => Const x
    | GRing.NatConst n => NatConst n
    | GRing.Add u v => Add (loop u) (loop v)
    | GRing.Opp u => Opp (loop u)
    | GRing.NatMul u n  => NatMul (loop u) n
    | GRing.Mul u v => Mul (loop u) (loop v)
    | GRing.Exp u n => Exp (loop u) n
    | _ => NatConst 0
  end.

End QF.

Bind Scope qf_scope with term.
Bind Scope qf_scope with formula.
Arguments Scope Add [_ qf_scope qf_scope].
Arguments Scope Opp [_ qf_scope].
Arguments Scope NatMul [_ qf_scope nat_scope].
Arguments Scope Mul [_ qf_scope qf_scope].
Arguments Scope Mul [_ qf_scope qf_scope].
Arguments Scope Exp [_ qf_scope nat_scope].
Arguments Scope Equal [_ qf_scope qf_scope].
Arguments Scope And [_ qf_scope qf_scope].
Arguments Scope Or [_ qf_scope qf_scope].
Arguments Scope Implies [_ qf_scope qf_scope].
Arguments Scope Not [_ qf_scope].

Implicit Arguments Bool [R].
Prenex Implicits Const Add Opp NatMul Mul Exp Bool Unit And Or Implies Not Lt.
Prenex Implicits to_rterm.

Notation True := (Bool true).
Notation False := (Bool false).

Delimit Scope qf_scope with qfT.
Notation "''X_' i" := (Var _ i) : qf_scope.
Notation "n %:R" := (NatConst _ n) : qf_scope.
Notation "x %:T" := (Const x) : qf_scope.
Notation "0" := 0%:R%qfT : qf_scope.
Notation "1" := 1%:R%qfT : qf_scope.
Infix "+" := Add : qf_scope.
Notation "- t" := (Opp t) : qf_scope.
Notation "t - u" := (Add t (- u)) : qf_scope.
Infix "*" := Mul : qf_scope.
Infix "*+" := NatMul : qf_scope.
Infix "^+" := Exp : qf_scope.
Notation "t ^- n" := (t^-1 ^+ n)%qfT : qf_scope.
Infix "==" := Equal : qf_scope.
Infix "<%" := Lt : qf_scope.
Infix "<=%" := Le : qf_scope.
Infix "/\" := And : qf_scope.
Infix "\/" := Or : qf_scope.
Infix "==>" := Implies : qf_scope.
Notation "~ f" := (Not f) : qf_scope.
Notation "x != y" := (Not (x == y)) : qf_scope.

Section evaluation.

Variable R : realDomainType.

Fixpoint eval (e : seq R) (t : term R) {struct t} : R :=
  match t with
  | ('X_i)%qfT => e`_i
  | (x%:T)%qfT => x
  | (n%:R)%qfT => n%:R
  | (t1 + t2)%qfT => eval e t1 + eval e t2
  | (- t1)%qfT => - eval e t1
  | (t1 *+ n)%qfT => eval e t1 *+ n
  | (t1 * t2)%qfT => eval e t1 * eval e t2
  | (t1 ^+ n)%qfT => eval e t1 ^+ n
  end.

Lemma evalE (e : seq R) (t : term R) : eval e t = GRing.eval e t.
Proof. by elim: t=> /=; do ?[move->|move=>?]. Qed.

Definition qf_eval e := fix loop (f : formula R) : bool :=
  match f with
  | Bool b => b
  | t1 == t2 => (eval e t1 == eval e t2)%bool
  | t1 <% t2 => (eval e t1 < eval e t2)%bool
  | t1 <=% t2 => (eval e t1 <= eval e t2)%bool
  | f1 /\ f2 => loop f1 && loop f2
  | f1 \/ f2 => loop f1 || loop f2
  | f1 ==> f2 => (loop f1 ==> loop f2)%bool
  | ~ f1 => ~~ loop f1
  end%qfT.

Lemma qf_evalE (e : seq R) (f : formula R) : qf_eval e f = ord.qf_eval e f.
Proof. by elim: f=> /=; do ?[rewrite evalE|move->|move=>?]. Qed.

Lemma to_rtermE (t : GRing.term R) :
  GRing.rterm t -> to_rterm t = t :> GRing.term _.
Proof.
elim: t=> //=; do ?
  [ by move=> u hu v hv /andP[ru rv]; rewrite hu ?hv
  | by move=> u hu *; rewrite hu].
Qed.

End evaluation.

Import Pdiv.Ring.

Section proj_qe_rcf.

Variable F : rcfType.

Notation fF := (formula  F).
Notation tF := (term  F).
Definition polyF := seq tF.

Lemma qf_formF (f : fF) : qf_form f.
Proof. by elim: f=> // *; apply/andP; split. Qed.

Lemma rtermF (t : tF) : GRing.rterm t.
Proof. by elim: t=> //=; do ?[move->|move=>?]. Qed.

Lemma rformulaF (f : fF) : rformula f.
Proof. by elim: f=> /=; do ?[rewrite rtermF|move->|move=>?]. Qed.

(* Lemma And_qf (f g : qf_rformula) : qf (f /\ g). *)
(* Proof. by rewrite /= !qfrP. Qed. *)
(* Canonical And_qfr f g := QfrForm (And_qf f g). *)

(* Lemma Or_qf (f g : qf_rformula) : qf (f \/ g). *)
(* Proof. by rewrite /= !qfrP. Qed. *)
(* Canonical Or_qfr f g := QfrForm (Or_qf f g). *)

Section If.

Implicit Types (pf tf ef : formula F).

Definition If := locked (fun pf tf ef => (pf /\ tf \/ ~ pf /\ ef)%qfT).

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
    /\ (if pick p is Some i then then_f i else else_f))%qfT.

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

Notation "'bind' x <- y ; z" :=
  (y (fun x => z)) (at level 99, x at level 0, y at level 0,
    format "'[hv' 'bind'  x  <-  y ;  '/' z ']'", only parsing).

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
rewrite ihp /= size_MXaddC -size_poly_eq0; case: size=> //.
by rewrite eval_If /=; case: (_ == _).
Qed.

Definition Isnull (p : polyF) : cps bool := fun k =>
  bind n <- Size p; k (n == 0%N).

Lemma eval_Isnull k p e : qf_eval e (Isnull p k)
  = qf_eval e (k (eval_poly e p == 0)).
Proof. by rewrite eval_Size size_poly_eq0. Qed.

Definition LtSize (p q : polyF) : cps bool := fun k =>
  bind n <- Size p; bind m <- Size q; k (n < m)%N.

Fixpoint LeadCoef p : cps tF := fun k =>
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
rewrite lead_coefDl ?lead_coef_Mmonic ?monicX //.
rewrite size_mul ?polyX_eq0 // size_polyX addn2 /= ltnS size_polyC.
by case: (_ == _)=> //=; rewrite size_poly_gt0.
Qed.

Implicit Arguments eval_LeadCoef [e p k].
Prenex Implicits eval_LeadCoef.

Fixpoint AmulXn (a : tF) (n : nat) : polyF:=
  if n is n'.+1 then (Const 0) :: (AmulXn a n') else [::a].

Lemma eval_AmulXn a n e : eval_poly e (AmulXn a n) = (eval e a)%:P * 'X^n.
Proof.
elim: n=> [|n] /=; first by rewrite expr0 mulr1 mul0r add0r.
by move->; rewrite addr0 -mulrA -exprSr.
Qed.

Fixpoint AddPoly (p q : polyF) :=
  if p is a::p' then
    if q is b::q' then (a + b)%qfT :: (AddPoly p' q')
      else p
    else q.

Lemma eval_AddPoly p q e :
  eval_poly e (AddPoly p q) = (eval_poly e p) + (eval_poly e q).
Proof.
elim: p q=> [|a p Hp] q /=; first by rewrite add0r.
case: q=> [|b q] /=; first by rewrite addr0.
by rewrite Hp mulrDl rmorphD /= !addrA [X in _ = X + _]addrAC.
Qed.

Fixpoint MulPoly (p q : polyF) := if p is a :: p'
    then AddPoly (map (Mul a) q) (Const 0 :: (MulPoly p' q)) else [::].

Lemma map_poly0 (R R' : ringType) (f : R -> R') : map_poly f 0 = 0.
Proof. by rewrite map_polyE polyseq0. Qed.

Lemma eval_map_mul e t p :
  eval_poly e (map (Mul t) p) = (eval e t) *: (eval_poly e p).
Proof.
elim: p=> [|a p ihp] /=; first by rewrite scaler0.
by rewrite ihp scalerDr scalerAl -!mul_polyC rmorphM.
Qed.

Lemma eval_MulPoly e p q :
  eval_poly e (MulPoly p q) = (eval_poly e p) * (eval_poly e q).
Proof.
elim: p q=> [|a p Hp] q /=; first by rewrite mul0r.
rewrite eval_AddPoly /= eval_map_mul Hp.
by rewrite addr0 mulrDl addrC mulrAC mul_polyC.
Qed.

Definition ExpPoly p n := iterop n MulPoly p [::1%qfT].

Lemma eval_ExpPoly e p n : eval_poly e (ExpPoly p n) = (eval_poly e p) ^+ n.
Proof.
case: n=> [|n]; first by rewrite /= expr0 mul0r add0r.
rewrite /ExpPoly iteropS exprSr; elim: n=> [|n ihn] //=.
  by rewrite expr0 mul1r.
by rewrite eval_MulPoly ihn exprS mulrA.
Qed.

Definition OppPoly := map (Mul (@Const F (-1))).

Lemma eval_OppPoly p e : eval_poly e (OppPoly p) = - eval_poly e p.
Proof.
elim: p; rewrite //= ?oppr0 // => t ts ->.
by rewrite !mulNr !opprD polyC_opp mul1r.
Qed.

Definition NatMulPoly n := map (Mul (NatConst F n)).
Lemma eval_NatMulPoly p n e :
  eval_poly e (NatMulPoly n p) = (eval_poly e p) *+ n.
Proof.
elim: p; rewrite //= ?mul0rn // => c p ->.
rewrite mulrnDl mulr_natl polyC_muln; congr (_+_).
by rewrite -mulr_natl mulrAC -mulrA mulr_natl mulrC.
Qed.

Fixpoint Horner (p : polyF) (x : tF) : tF :=
  if p is a :: p then (Horner p x * x + a)%qfT else 0%qfT.

Lemma eval_Horner e p x : eval e (Horner p x) = (eval_poly e p).[eval e x].
Proof.
elim: p=> //= [|a p ihp]; first by rewrite horner0.
by rewrite !hornerE ihp.
Qed.

Lemma eval_ConstPoly e c : eval_poly e [::c] = (eval e c)%:P.
Proof. by rewrite /= mul0r add0r. Qed.

Fixpoint Deriv (p : polyF) : polyF :=
  if p is a :: q then (AddPoly q (0%qfT :: Deriv q)) else [::].

Lemma eval_Deriv e p : eval_poly e (Deriv p) = (eval_poly e p)^`().
Proof.
elim: p=> [|a p ihp] /=; first by rewrite deriv0.
by rewrite eval_AddPoly /= addr0 ihp !derivE.
Qed.

Fixpoint SymPoly p :=
  if p is a :: p
    then AddPoly (MulPoly (OppPoly (SymPoly p)) [::0; 1]%qfT) [::a]
    else [::].

Lemma eval_SymPoly e p : eval_poly e (SymPoly p) = (eval_poly e p) \Po (-'X).
Proof.
elim: p=> [|a p ihp]; first by rewrite comp_poly0 //.
rewrite /= eval_AddPoly eval_MulPoly eval_OppPoly /=.
rewrite  !(mul0r, add0r, mul1r, addr0) ihp.
by rewrite comp_polyD comp_polyC comp_polyM comp_polyX mulrN mulNr.
Qed.

Definition eval_OpPoly :=
  (eval_MulPoly, eval_AmulXn, eval_AddPoly, eval_OppPoly, eval_NatMulPoly,
  eval_ConstPoly, eval_Horner, eval_ExpPoly, eval_SymPoly, eval_Deriv,
  eval_map_mul).

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
   by move=> x /=; rewrite Pk /= !eval_OpPoly /= !mul_polyC.
rewrite eval_Size /=; have [//=|gtq] := ltnP.
rewrite (eval_LeadCoef (fun lr =>
  let m := lr *: 'X^(size (eval_poly e r) - sq) in
  let qq1 := (eval_poly e qq) * (eval e cq)%:P + m in
  let r1 := (eval_poly e r) * (eval e cq)%:P - m * (eval_poly e q) in
    k' (redivp_rec_loop (eval_poly e q) sq (eval e cq) c.+1 qq1 r1 n))) //=.
by move=> x; rewrite ihn // !eval_OpPoly /= !mul_polyC.
Qed.

Implicit Arguments eval_Rediv_rec_loop [e q sq cq c qq r n k].
Prenex Implicits eval_Rediv_rec_loop.

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
move=> Pk; rewrite eval_Isnull /d unlock.
have [_|p_neq0] /= := boolP (_ == _); first by rewrite Pk /= mul0r add0r.
rewrite !eval_Size; set p' := eval_poly e p; set q' := eval_poly e q.
rewrite (eval_LeadCoef (fun lq =>
  k' (redivp_rec_loop q' (size q') lq 0 0 p' (size p')))) /=; last first.
  by move=> x; rewrite (eval_Rediv_rec_loop k') //= mul0r add0r.
by rewrite redivp_rec_loopP.
Qed.

Implicit Arguments eval_Rediv [e p q k].
Prenex Implicits eval_Rediv.

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

Fixpoint BigRgcd (ps : seq polyF) k : fF :=
  if ps is p :: pr then bind r <- BigRgcd pr; Rgcd p r k else k [::Const 0].

Lemma eval_BigRgcd e ps k k' :
  (forall p, qf_eval e (k p) = k' (eval_poly e p)) ->
  qf_eval e (BigRgcd ps k) =
  k' (\big[@rgcdp _/0%:P]_(i <- ps) (eval_poly e i)).
Proof.
elim: ps k k'=> [|p sp ihsp] k k' Pk /=.
  by rewrite big_nil Pk /= mul0r add0r.
rewrite big_cons (ihsp _ (fun r => k' (rgcdp (eval_poly e p) r))) //.
by move=> r; apply: eval_Rgcd.
Qed.

Fixpoint Variation (s : seq tF) : cps nat := fun k =>
  if s is a :: q then
    bind v <- Variation q;
    If (Lt (a * head 0 q) 0)%qfT Then k (1 + v)%N Else k v
    else k 0%N.

Lemma eval_Variation e s k : qf_eval e (Variation s k)
  = qf_eval e (k (var (map (eval e) s))).
Proof.
elim: s k=> //= a q ihq k; rewrite ihq eval_If /= -nth0.
by case: q {ihq}=> /= [|b q]; [rewrite /= mulr0 ltrr add0n | case: ltrP].
Qed.

Definition Varp sp x := Variation [seq Horner p x | p <- sp].

Lemma eval_Varp e sp x k : qf_eval e (Varp sp x k) =
  qf_eval e (k (varp (map (eval_poly e) sp) (eval e x))).
Proof.
rewrite eval_Variation /varp; congr (qf_eval _ (k (var _))).
by rewrite -!map_comp; apply: eq_map=> p /=; rewrite eval_Horner.
Qed.

Definition VarpI (a b : tF) (sp : seq polyF) (k : int -> fF) : fF :=
  bind va <- Varp sp a; bind vb <- Varp sp b; k (va%:Z - vb%:Z).

Lemma eval_VarpI e a b sp k :
  qf_eval e (VarpI a b sp k) =
  qf_eval e (k (varpI (eval e a) (eval e b) (map (eval_poly e) sp))).
Proof. by rewrite !eval_Varp. Qed.

Fixpoint Sremps_rec (p q : polyF) n : cps (seq polyF) := fun k =>
  if n is n.+1 then
    bind p_null <- Isnull p;
    if p_null then k [::]
      else
        bind lq <- LeadCoef q;
        bind spq <- Rscal p q;
        bind mpq <- Rmod p q;
        bind r <- Sremps_rec q (MulPoly [::(- lq ^+ spq)%qfT] mpq) n;
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
  by rewrite !eval_OpPoly addr0 /=.
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

Notation taq' p a b q := (varpI a b (sremps p (p^`() * q))).

Definition Taq (p : polyF) (a b : tF) (q : polyF) : cps int := fun k =>
  bind r <- Sremps p (MulPoly (Deriv p) q); VarpI a b r k.

Lemma eval_Taq e a b p q k :
  qf_eval e (Taq p a b q k) =
  qf_eval e (k (taq' (eval_poly e p) (eval e a) (eval e b) (eval_poly e q))).
Proof.
rewrite (eval_Sremps (fun r => qf_eval e (k (varpI (eval e a) (eval e b) r)))).
  by rewrite !eval_OpPoly.
by move=> sp; rewrite !eval_Varp.
Qed.

Definition PolyComb (sq : seq polyF) (sc : seq int) :=
  \big[MulPoly/[::1%qfT]]_(i < size sq)
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

Definition Staq (p : polyF) (a b : tF) (sq : seq polyF) (i : nat) : cps tF :=
  fun k => bind n <- Taq p a b (Pcq sq i); k ((n%:~R) %:T)%qfT.

Lemma eval_Staq e p a b sq i k k' :
  (forall x, qf_eval e (k x) = k' (eval e x)) ->
  qf_eval e (Staq p a b sq i k) =
  k' (staq (eval_poly e p) (eval e a) (eval e b) (map (eval_poly e) sq) i).
Proof. by move=> Pk; rewrite /Staq /staq eval_Taq Pk /= eval_Pcq. Qed.

Implicit Arguments eval_Staq [e p a b sq i k].
Prenex Implicits eval_Staq.

Definition ProdStaqCoefs (p : polyF) (a b : tF)
  (sq : seq polyF) : cps tF := fun k =>
  let fix aux s (i : nat) k := if i is i'.+1
    then bind x <- Staq p a b sq i';
      aux (x * (coefs _ (size sq) i')%:T + s)%qfT i' k
    else k s in
   aux 0%qfT (3 ^ size sq)%N k.

Lemma eval_ProdStaqCoefs e p a b sq k k' :
  (forall x, qf_eval e (k x) = k' (eval e x)) ->
  qf_eval e (ProdStaqCoefs p a b sq k) =
  k' (prod_staq_coefs (eval_poly e p)
    (eval e a) (eval e b) (map (eval_poly e) sq)).
Proof.
move=> Pk; rewrite /ProdStaqCoefs /prod_staq_coefs.
set Aux := (fix Aux s i k := match i with 0 => _ | _ => _ end).
set aux := (fix aux s i := match i with 0 => _ | _ => _ end).
rewrite size_map -[0]/(eval e 0%qfT); move: 0%qfT=> x.
elim: (_ ^ _)%N k k' Pk x=> /= [|n ihn] k k' Pk x.
  by rewrite Pk.
rewrite (eval_Staq
  (fun y => k' (aux (y * (coefs F (size sq) n) + eval e x) n))).
  by rewrite size_map.
by move=> y; rewrite (ihn _ k').
Qed.

Implicit Arguments eval_ProdStaqCoefs [e p a b sq k].
Prenex Implicits eval_ProdStaqCoefs.

Definition Normr (x : tF) : cps tF := fun k =>
  (If Lt 0 x Then k x Else k (- x))%qfT.

Lemma eval_Normr e x k k' : (forall x, qf_eval e (k x) = k' (eval e x)) ->
  qf_eval e (Normr x k) = k' `|(eval e x)|.
Proof. by move=> Pk; rewrite eval_If !Pk /=; case: ler0P. Qed.

Implicit Arguments eval_Normr [e x k].
Prenex Implicits eval_Normr.

Fixpoint SumNorm n (f : nat -> tF) : cps tF := fun k =>
  if n is n.+1 then
    bind a <- Normr (f n);
    bind c <- SumNorm n f;
    k (c + a)%qfT else k 0%qfT.

Lemma eval_SumNorm e n f k k' :
  (forall x, qf_eval e (k x) = k' (eval e x)) ->
  qf_eval e (SumNorm n f k) = k' (\sum_(i < n) `|eval e (f i)|).
Proof.
elim: n k k'=> /= [|n ihn] k k' Pk.
 by rewrite big_ord0 Pk.
rewrite big_ord_recr /=.
rewrite (eval_Normr (fun a => k' (\sum_(i < n) `|eval e (f i)| + a))) //.
move=> x; rewrite (ihn _ (fun c => k' (c + eval e x))) //.
by move=> y; rewrite Pk.
Qed.

Implicit Arguments eval_SumNorm [e n f k].
Prenex Implicits eval_SumNorm.

Definition CauchyBound (p : polyF) : cps tF := fun k =>
  bind sp <- Size p; SumNorm sp (nth 0%qfT p) k.

Lemma eval_CauchyBound e p k k' :
  eval_poly e p \is monic -> (forall x, qf_eval e (k x) = k' (eval e x)) ->
  qf_eval e (CauchyBound p k) = k' (cauchy_bound (eval_poly e p)).
Proof.
move=> mp Pk; rewrite /CauchyBound /cauchy_bound.
rewrite eval_Size (monicP mp) normr1 invr1 mul1r (eval_SumNorm k') //.
congr k'; apply: eq_big=> //= i _.
elim: p {mp} i=> /= [|a p ihp] i; first by rewrite nth_nil coef0.
move: i; rewrite size_MXaddC.
have [->|ep_neq0//] /= := altP (_ =P 0).
  have [->|ea_neq0//] /= := altP (_ =P 0); first by case.
  rewrite size_poly0=> i.
  by rewrite ord1 mul0r add0r polyseqC ea_neq0 /=.
rewrite -cons_poly_def polyseq_cons /nilp size_poly_eq0 ep_neq0.
rewrite -add1n; move=> i; have [j ->|j ->] := fintype.splitP i.
  by rewrite ord1 /=.
by rewrite add1n /= ihp.
Qed.

Implicit Arguments eval_CauchyBound [e p k].
Prenex Implicits eval_CauchyBound.

Fixpoint HasPoly (P : polyF -> cps bool) (s : seq polyF) : cps bool := fun k =>
  if s is x :: s then bind Px <- P x; if Px then k true else HasPoly P s k
  else k false.

Lemma eval_HasPoly e s P' k P k' : (forall b, qf_eval e (k b) = k' b) ->
  (forall s k k', (forall b, qf_eval e (k b) = k' b) ->
    qf_eval e (P' s k) = k' (P s)) ->
  qf_eval e (@HasPoly P' s k) = k' (has P s).
Proof.
move=> hk hP; elim: s=> //= x s ihs.
rewrite (hP _ _ (fun b => if b then k' true else k' (has P s))); last by case.
by case: (P x).
Qed.

Implicit Arguments eval_HasPoly [e s P' k].
Prenex Implicits eval_HasPoly.

Definition ChangeVarp (p : polyF) : cps polyF := fun k =>
  bind sp <- Size p; bind lp <- LeadCoef p;
  k (AddPoly (ExpPoly [::0; 1] sp.-1)
  (\big[AddPoly/[::]]_(i < sp.-1) (MulPoly
    [::lp ^+ (sp - i.+2) * nth 0 p i] (ExpPoly [::0; 1] i))))%qfT.

Lemma eval_polyP e p : eval_poly e p = Poly (map (eval e) p).
Proof. by elim: p=> // a p /= ->; rewrite cons_poly_def. Qed.

Lemma eval_ChangeVarp e p k k' :
  (forall p, eval_poly e p \is monic -> qf_eval e (k p) = k' (eval_poly e p)) ->
  qf_eval e (ChangeVarp p k) = k' (change_varp (eval_poly e p)).
Proof.
move=> Pk; rewrite eval_Size; pose p' := eval_poly e p.
rewrite (eval_LeadCoef (fun lp => k' ('X^(size p').-1 +
  \poly_(i < (size p').-1) (lp ^+ (size p' - i.+2) * p'`_i)))) //.
move=> lp; set q := AddPoly _ _; set q' := _ + _.
suff eqq': eval_poly e q = q'.
  rewrite Pk eqq' // monicE lead_coefDl ?lead_coefXn //.
  by rewrite size_polyXn (leq_ltn_trans (size_poly _ _)).
rewrite /q /q' !eval_OpPoly /= mul0r add0r addr0 mul1r.
congr (_ + _); move: (size _)=> n; rewrite poly_def.
apply: (big_ind2 (fun u v => eval_poly e u = v))=> //.
  by move=> u u' v v'; rewrite eval_AddPoly=> -> ->.
move=> i _; rewrite !eval_OpPoly /= !(mul0r, add0r, mul1r, addr0).
rewrite [p']eval_polyP /= coef_Poly.
have [hi|hi] := ltnP i (size p); first by rewrite (nth_map 0%qfT).
by rewrite !nth_default // size_map.
Qed.

Implicit Arguments eval_ChangeVarp [e p k].
Prenex Implicits eval_ChangeVarp.

Definition ChangeVarq (a : tF) (q : polyF) : cps polyF := fun k =>
  bind sq <- Size q;
  k (\big[AddPoly/[::]]_(i < sq) (MulPoly
    [::a ^+ (to_even sq - i) * nth 0 q i] (ExpPoly [::0; 1] i)))%qfT.

Lemma eval_ChangeVarq e a q k k' :
  (forall p, qf_eval e (k p) = k' (eval_poly e p)) ->
  qf_eval e (ChangeVarq a q k) = k' (change_varq (eval e a) (eval_poly e q)).
Proof.
move=> Pk; rewrite eval_Size /change_varq.
pose a' := eval e a; pose q' := eval_poly e q.
rewrite Pk; congr (k' _); move: (size _)=> n; rewrite poly_def.
apply: (big_ind2 (fun u v => eval_poly e u = v))=> //.
  by move=> u u' v v'; rewrite eval_AddPoly=> -> ->.
move=> i _; rewrite !eval_OpPoly /= !(mul0r, add0r, mul1r, addr0).
rewrite mul_polyC eval_polyP /= coef_Poly.
have [hi|hi] := ltnP i (size q); first by rewrite (nth_map 0%qfT).
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
  (forall p sq, eval_poly e p \is monic -> qf_eval e (k (p, sq)) =
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

Definition MajNotRoot (x : tF) (p : polyF) : cps tF := fun k =>
  bind sp <- Size p;
  Pick (fun i : 'I_sp.+1 => Horner p (x + i.+1%:R) != 0)%qfT
  (fun i => k (x + i.+1%:R))%qfT (k (x + 1)%qfT).

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

Definition PickRight x p := MajNotRoot x (MulPoly (SymPoly p) p).

Lemma eval_PickRight e x p k k' :
  (forall x, qf_eval e (k x) = k' (eval e x)) ->
  qf_eval e (PickRight x p k) = k' (pick_right (eval e x) (eval_poly e p)).
Proof.
move=> Pk; rewrite (eval_MajNotRoot k'); last by [].
by rewrite /pick_right !eval_OpPoly.
Qed.

Implicit Arguments eval_PickRight [e x p k].
Prenex Implicits eval_PickRight.

Fixpoint ProdPoly T (s : seq T) (f : T -> cps polyF) : cps polyF := fun k =>
  if s is a :: s then
    bind fa <- f a;
    bind fs <- ProdPoly s f;
    k (MulPoly fa fs)
    else k [::1%qfT].

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

Definition CcountWeak (p : polyF) (sq : seq polyF) : cps tF := fun k =>
  bind p0 <- Isnull p;
  if p0 then k 0%qfT else
  bind sp <- Size p;
  if sp == 1%N then k 0%qfT
    else bind sq0 <- HasPoly Isnull sq;
      if sq0 then k 0%qfT
      else
        bind cpsq <- ToMonic p sq;
        let (p', sq') := cpsq in
        bind sq_aux <- ProdPoly (index_enum [finType of 'I_(3 ^ size sq')])
        (fun i k =>
          bind sr <- Sremps p' (MulPoly (Deriv p') (Pcq sq' i));
          k (\big[MulPoly/[::1%qfT]]_(r <- sr) r));
        bind cbound <- CauchyBound p';
        bind bound <- PickRight cbound sq_aux;
        ProdStaqCoefs p' (- bound) bound sq' k.

Lemma eval_CcountWeak e p sq k k' :
  (forall x, qf_eval e (k x) = k' (eval e x)) ->
  qf_eval e (CcountWeak p sq k) =
  k' (ccount_weak (eval_poly e p) (map (eval_poly e) sq)).
Proof.
move=> Pk; rewrite eval_Isnull /ccount_weak //.
case: eqP=> _; first by rewrite Pk.
rewrite eval_Size; have [|sp_neq1] := altP eqP; first by rewrite Pk.
pose isnull p := eval_poly e p == 0.
rewrite (eval_HasPoly isnull (fun n => if n then k' 0 else
  let '(p', sq') := to_monic (eval_poly e p) (map (eval_poly e) sq) in
       let sq_aux :=  \prod_(j < 3 ^ size sq') \prod_(r <-
    sremps p' (p'^`() * (map (poly_comb sq') (sg_tab (size sq')))`_j)) r in
       let bound := pick_right (cauchy_bound p') sq_aux in
       k' (prod_staq_coefs p' (- bound) bound sq')
)); first 2 last.
+ by move=> *; rewrite eval_Isnull.
+ rewrite has_map [has (preim _ _) _](@eq_has _ _ isnull) //.
  by case: has.
move=> []; first by rewrite Pk.
rewrite (eval_ToMonic (fun cpsq => let '(p', sq') := cpsq in
       let sq_aux := \prod_(j < 3 ^ size sq') \prod_(r <-
       sremps p' (p'^`() * (map (poly_comb sq') (sg_tab (size sq')))`_j)) r in
       let bound := pick_right (cauchy_bound p') sq_aux in
       k' (prod_staq_coefs p' (- bound) bound sq'))) //.
move=> cp csq mcp; pose cp' := eval_poly e cp.
pose csq' := map (eval_poly e) csq.
rewrite (eval_ProdPoly (fun j : 'I__ => \prod_(r <- sremps cp'
  (cp'^`() * (map (poly_comb csq') (sg_tab (size csq')))`_j)) r)
(fun sq_aux => let bound := pick_right (cauchy_bound cp') sq_aux in
  k' (prod_staq_coefs cp' (- bound) bound csq'))).
+ by rewrite !size_map.
+ move=> i {k k' Pk} k k' Pk.
  rewrite (eval_Sremps (fun sr => k' (\prod_(r <- sr) r))).
    by rewrite !eval_OpPoly eval_Pcq /pcq size_map.
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

Implicit Arguments eval_CcountWeak [e p sq k].
Prenex Implicits eval_CcountWeak.

Definition BoundingPoly (sq : seq polyF) : polyF :=
  Deriv (\big[MulPoly/[::1%qfT]]_(q <- sq) q).

Lemma eval_BoundingPoly e sq :
  eval_poly e (BoundingPoly sq) = bounding_poly (map (eval_poly e) sq).
Proof.
rewrite eval_Deriv /bounding_poly big_map (@big_morph _ _ _ 1 *%R) //=.
  by move=> p q /=; rewrite eval_MulPoly.
by rewrite mul0r add0r.
Qed.

Definition CcountGt0 (sp sq : seq polyF) : fF :=
  bind p <- BigRgcd sp; bind p0 <- Isnull p;
  if ~~ p0 then
    bind c <- CcountWeak p sq;
    Lt 0%qfT c
  else
    let bq := BoundingPoly sq in
      bind cw <- CcountWeak bq sq;
      (Lt 0 cw \/ (
        (\big[And/True]_(q <- sq) (LeadCoef q (fun lq => Lt 0 lq)))
        \/ (\big[And/True]_(q <- sq) (
          bind sq <- Size q;
          bind lq <- LeadCoef q;
          Lt 0 ((Opp 1) ^+ (sq).-1 * lq)
        ))))%qfT.

Lemma eval_CcountGt0 e sp sq : qf_eval e (CcountGt0 sp sq) =
  ccount_gt0 (map (eval_poly e) sp) (map (eval_poly e) sq).
Proof.
pose sq' := map (eval_poly e) sq; rewrite /ccount_gt0.
rewrite (@eval_BigRgcd _ _ _ (fun p => if p != 0
  then 0 < ccount_weak p sq'
  else let bq := bounding_poly sq' in
    [|| 0 < ccount_weak bq sq', \big[andb/true]_(q <- sq') (0 < lead_coef q)
    | \big[andb/true]_(q <- sq') (0 < (-1) ^+ (size q).-1 * lead_coef q)])).
  by rewrite !big_map.
move=> p; rewrite eval_Isnull; case: eqP=> _ /=; last first.
  by rewrite (eval_CcountWeak (>%R 0)).
rewrite (eval_CcountWeak (fun n =>
   [|| 0 < n, \big[andb/true]_(q <- sq') (0 < lead_coef q)
   | \big[andb/true]_(q <- sq') (0 < (-1) ^+ (size q).-1 * lead_coef q)])).
  by rewrite eval_BoundingPoly.
move=> n /=; rewrite !big_map; congr [|| _, _| _].
  apply: (big_ind2 (fun u v => qf_eval e u = v))=> //=.
    by move=> u v u' v' -> ->.
  by move=> i _; rewrite (eval_LeadCoef (>%R 0)).
apply: (big_ind2 (fun u v => qf_eval e u = v))=> //=.
  by move=> u v u' v' -> ->.
by move=> i _; rewrite eval_Size (eval_LeadCoef (fun lq =>
  (0 < (-1) ^+ (size (eval_poly e i)).-1 * lq))).
Qed.

Fixpoint normtrX (i : nat) (t : tF) : polyF :=
  (match t with
    | 'X_n => if n == i then [::0; 1] else [::t]
    | - x => OppPoly (normtrX i x)
    | x + y => AddPoly (normtrX i x) (normtrX i y)
    | x * y => MulPoly (normtrX i x) (normtrX i y)
    | x *+ n => NatMulPoly n (normtrX i x)
    | x ^+ n => let ax := (normtrX i x) in
      iter n (MulPoly ax) [::1]
    | _ => [::t]
  end)%qfT.

Lemma normtrXP e i t x :
  (eval_poly e (normtrX i t)).[x] = eval (set_nth 0 e i x) t.
Proof.
elim: t.
- move=> n /=; case ni: (_ == _);
    rewrite //= ?(mul0r,add0r,addr0,polyC1,mul1r,hornerX,hornerC);
    by rewrite // nth_set_nth /= ni.
- by move=> r; rewrite /= mul0r add0r hornerC.
- by move=> r; rewrite /= mul0r add0r hornerC.
- by move=> t tP s sP; rewrite /= eval_AddPoly hornerD tP ?sP.
- by move=> t tP; rewrite /= eval_OppPoly hornerN tP.
- by move=> t tP n; rewrite /= eval_NatMulPoly hornerMn tP.
- by move=> t tP s sP; rewrite /= eval_MulPoly hornerM tP ?sP.
- move=> t tP /=; elim; first by rewrite /= expr0 mul0r add0r hornerC.
  by move=> n ihn; rewrite /= eval_MulPoly exprSr hornerM ihn ?tP // mulrC.
Qed.

Definition wproj (n : nat) (s : seq (GRing.term F) * seq (GRing.term F)) :
  formula F :=
  let sp := map (normtrX n \o to_rterm) s.1%PAIR in
  let sq := map (normtrX n \o to_rterm) s.2%PAIR in
    CcountGt0 sp sq.

Lemma wf_QE_wproj i bc (bc_i := wproj i bc) :
  dnf_rterm (w_to_oclause bc) -> qf_form bc_i && rformula bc_i.
Proof.
case: bc @bc_i=> sp sq /=; rewrite /dnf_rterm /= /wproj andbT=> /andP[rsp rsq].
by rewrite qf_formF rformulaF.
Qed.

Lemma valid_QE_wproj i bc (bc' := w_to_oclause bc)
    (ex_i_bc := ('exists 'X_i, odnf_to_oform [:: bc'])%oT) e :
  dnf_rterm bc' -> reflect (holds e ex_i_bc) (ord.qf_eval e (wproj i bc)).
Proof.
case: bc @bc' @ex_i_bc=> sp sq /=; rewrite /dnf_rterm /wproj /= andbT.
move=> /andP[rsp rsq]; rewrite -qf_evalE.
rewrite eval_CcountGt0 /=; apply: (equivP (ex_roots _ _)).
set P1 := (fun x => _); set P2 := (fun x => _).
suff: forall x, P1 x <-> P2 x.
  by move=> hP; split=> [] [x Px]; exists x; rewrite (hP, =^~ hP).
move=> x; rewrite /P1 /P2 {P1 P2} !big_map !(big_seq_cond xpredT) /=.
rewrite (eq_bigr (fun t => GRing.eval (set_nth 0 e i x) t == 0)); last first.
  by move=> t /andP[t_in_sp _]; rewrite normtrXP evalE to_rtermE ?(allP rsp).
rewrite [X in _ && X](eq_bigr (fun t => 0 < GRing.eval (set_nth 0 e i x) t));
  last by move=> t /andP[tsq _]; rewrite normtrXP evalE to_rtermE ?(allP rsq).
rewrite -!big_seq_cond !(rwP (qf_evalP _ _)); first last.
+ elim: sp rsp => //= p sp ihsp /andP[rp rsp]; first by rewrite ihsp.
+ elim: sq rsq => //= q sq ihsq /andP[rq rsq]; first by rewrite ihsq.
rewrite !(rwP andP) (rwP orP) orbF !andbT /=.
have unfoldr P s : foldr (fun t => ord.And (P t)) ord.True s =
  \big[ord.And/ord.True]_(t <- s) P t by rewrite unlock /reducebig.
rewrite !unfoldr; set e' := set_nth _ _ _ _.
by rewrite !(@big_morph _ _ (ord.qf_eval _) true andb).
Qed.

Definition rcf_sat := proj_sat wproj.

Lemma rcf_satP e f : reflect (holds e f) (rcf_sat e f).
Proof. exact: (proj_satP wf_QE_wproj valid_QE_wproj). Qed.

End proj_qe_rcf.
