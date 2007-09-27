Require Import ssreflect ssrbool funs eqtype ssrnat seq fintype.
Require Import ssralg ssrbig.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import Ring.

Reserved Notation "\C c" (at level 10, c at level 8).
Reserved Notation "\X" (at level 0).
Reserved Notation "f .[ x ]"
  (at level 2, x at level 200, format "f .[ x ]").

Reserved Notation "\poly_ ( i < n ) E"
  (at level 36, E at level 36, i, n at level 50,
   format "\poly_ ( i  <  n )  E").

Notation Local simp := Monoid.Equations.simpm.

Section Polynomial.

Variable R : Ring.basic.

(* Define a polynomial as a sequence *)

(* A coef sequence is normal if its last element is <> 0 *)
Definition normal (s : seq R) := last 1 s != 0.

CoInductive polynomial : Type := Poly s & normal s.

Bind Scope ring_scope with polynomial.

Notation poly := polynomial.

Coercion seq_of_poly p := let: Poly s _ := p in s.

Lemma seq_of_poly_inj : injective seq_of_poly.
Proof.
move=> [s1 ns1] [s2 ns2] /= eq_s12.
rewrite eq_s12 in ns1 *; congr Poly; exact: bool_irrelevance.
Qed.

Lemma poly_eqP : reflect_eq (fun p1 p2 : poly => p1 == p2 :> seq R).
Proof.
by move=> p1 p2; apply: (iffP eqP); [exact: seq_of_poly_inj | move->].
Qed.

Canonical Structure poly_eqType := EqType poly_eqP.

Lemma normal_seq0 : normal seq0.
Proof. by apply/eqP; case: R. Qed.

Definition polyC c :=
  if insub normal (Seq c) is Some (EqSig s ns)
    then Poly ns
    else Poly normal_seq0.

Notation "\C c" := (polyC c).

Definition poly0 := polyC 0.
Definition poly1 := polyC 1.

Notation Local "\C0" := poly0 (at level 0).
Notation Local "\C1" := poly1 (at level 0).

Lemma seq_polyC : forall c,
  polyC c = (if c == 0 then seq0 else Seq c) :> seq R.
Proof.
move=> c; rewrite /polyC /normal -if_neg.
by case insubP => [[? ?] -> //|]; move/negbET->.
Qed.

Lemma polyC_inj : injective polyC.
Proof.
move=> c1 c2; move/(congr1 seq_of_poly); rewrite !seq_polyC.
by case: eqP => [->|_]; case: eqP => // _ [].
Qed.

Lemma seq_poly0 : \C0 = seq0 :> seq R.
Proof. by rewrite /poly0 seq_polyC set11. Qed.

Lemma seq_poly1 : \C1 = Seq 1 :> seq R.
Proof. by rewrite /poly1 seq_polyC (negbET normal_seq0). Qed.

Definition horner c p : poly :=
  if p is Poly (Adds _ _ as s) ns then Poly (ns : normal (Adds c s)) else \C c.

Lemma seq_horner : forall c p,
  horner c p = (if p : seq R is seq0 then \C c else Adds c p) :> seq R.
Proof. by move=> c [[|c' s] ns] /=. Qed.

Lemma horner_inj : forall c1 c2 p1 p2,
  horner c1 p1 = horner c2 p2 -> c1 = c2 /\ p1 = p2.
Proof.
move=> c1 c2 p1 p2; move/(congr1 seq_of_poly); rewrite !seq_horner => eq_h.
suffices [->]: Adds c1 p1 = Adds c2 p2 by move/seq_of_poly_inj.
case: (p1 : seq R) (p2 : seq R) eq_h => [|? ?] [|? ?];
 by [| move/seq_of_poly_inj; move/polyC_inj-> | rewrite seq_polyC; case: eqP].
Qed.

Lemma horner_eq : forall c1 c2 p1 p2,
  (horner c1 p1 == horner c2 p2) = (c1 == c2) && (p1 == p2).
Proof.
move=> c1 c2 p1 p2; apply/eqP/andP; last by case; do 2!move/eqP->.
by case/horner_inj=> -> ->.
Qed.

Definition mkPoly := foldr horner \C0.

Definition polyX := mkPoly (Seq 0 1).

Notation "\X" := polyX.
Notation "\poly_ ( i < n ) E" := (mkPoly (mkseq (fun i : nat => E) n)).

Lemma seq_polyX : \X = Seq 0 1 :> seq R.
Proof. by rewrite !seq_horner seq_poly0 seq_poly1. Qed.

Lemma mkPoly_seq : forall p : poly, mkPoly p = p.
Proof.
move=> [[|c s] ns] /=; apply seq_of_poly_inj=> /=; first exact: seq_poly0.
elim: s => [|c' s IHs] /= in c ns *; rewrite seq_horner ?IHs //.
by rewrite seq_poly0 seq_polyC (negbET ns).
Qed.

(* Extensional interpretation (poly <=> nat -> R) *)

Definition coef (p : poly) := sub 0 p.
Definition lead_coef (p : poly) := last 1 p.

Lemma lead_coef_nz : forall p, lead_coef p != 0.
Proof. by case. Qed.

Lemma coefE : forall p, coef p = sub 0 p. Proof. done. Qed.

Lemma coef0 : forall i, coef \C0 i = 0.
Proof. by case; rewrite /coef seq_poly0. Qed.

Lemma coef_polyC : forall c i,
  coef (polyC c) i = if i is 0%N then c else 0.
Proof. by move=> c [|[|i]]; rewrite /coef seq_polyC //=; case: eqP. Qed.

Lemma coef_horner : forall c p i,
  coef (horner c p) i = if i is j.+1 then coef p j else c.
Proof.
move=> c p i; rewrite /coef seq_horner.
by case: i (p : seq R) => [|i] [] //; rewrite -coefE coef_polyC ?sub_seq0.
Qed.

Lemma coef_mkPoly : forall s, coef (mkPoly s) =1 sub 0 s.
Proof. by elim=> [|c s IHs] /= [|i]; rewrite (coef0, coef_horner) /=. Qed.

Lemma coef_poly_of : forall n F k,
  coef (\poly_(i < n) F i) k = (if k < n then F k else 0).
Proof.
move=> n F k; case: (ltnP k n) => ?; first by rewrite coef_mkPoly sub_mkseq.
by rewrite coef_mkPoly sub_default // size_mkseq.
Qed.

Lemma coef_polyX : forall i, coef \X i = if i == 1%N then 1 else 0.
Proof. by case=> [|[|[|i]]]; rewrite coef_mkPoly. Qed.

Lemma coef_eqP : forall p1 p2, coef p1 =1 coef p2 <-> p1 = p2.
Proof.
rewrite /coef => p1 p2; split=> [eq_coef | -> //]; apply: seq_of_poly_inj.
without loss: p1 p2 eq_coef / size p1 <= size p2 => [wleq|].
  by case: (leqP (size p1) (size p2)); last move/ltnW; move/wleq->.
rewrite leq_eqVlt; case/orP; first by move/eqP; move/(@eq_from_sub _ 0); exact.
move/leq_add_sub=> sz_p2; case/eqP: (lead_coef_nz p2).
by rewrite /lead_coef -(sub_last 0) -sz_p2 /= -eq_coef sub_default ?leq_addr.
Qed.

(* Ring structure *)

Fixpoint add_poly_seq (s1 s2 : seq R) {struct s1} : seq R :=
  match s1, s2 with
  | Seq0, _ => s2
  | _, Seq0 => s1
  | Adds c1 s1', Adds c2 s2' => Adds (c1 + c2) (add_poly_seq s1' s2')
  end.

Definition add_poly (p1 p2 : poly) := mkPoly (add_poly_seq p1 p2).

Notation Local "p1 +p p2" := (add_poly p1 p2) (at level 50).

Lemma sub_add_poly_seq : forall s1 s2 i,
  sub 0 (add_poly_seq s1 s2) i = sub 0 s1 i + sub 0 s2 i.
Proof. by elim=> [|c1 s1 IHs] [|c2 s2] [|i] //=; rewrite simp. Qed.

Lemma coef_add_poly : forall p1 p2 i,
  coef (p1 +p p2) i = coef p1 i + coef p2 i.
Proof. by move=> *; rewrite /add_poly coef_mkPoly sub_add_poly_seq. Qed.

Lemma poly_add0P : forall p, \C0 +p p = p.
Proof. by move=> p; apply/coef_eqP=> i; rewrite coef_add_poly coef0 simp. Qed.

Lemma poly_addC : forall p1 p2, p1 +p p2 = p2 +p p1.
Proof. by move=> *; apply/coef_eqP=> i; rewrite !coef_add_poly addrC. Qed.

Lemma poly_addA : forall p1 p2 p3, p1 +p (p2 +p p3) = p1 +p p2 +p p3.
Proof. by move=> *; apply/coef_eqP=> i; rewrite !coef_add_poly addrA. Qed.

Fixpoint mul_poly_seq (s1 s2 : seq R) {struct s1} : seq R :=
  if s1 is Adds c1 s1' then
    add_poly_seq (maps (fun c2 => c1 * c2) s2) (Adds 0 (mul_poly_seq s1' s2))
  else seq0.

Definition mul_poly (p1 p2 : poly) := mkPoly (mul_poly_seq p1 p2).

Notation Local "p1 *p p2" := (mul_poly p1 p2) (at level 40).

Lemma coef_mul_poly : forall p1 p2 i,
  coef (p1 *p p2) i = \sum_(j <= i) coef p1 j * coef p2 (i - j).
Proof.
move=> [s1 ns1] [s2 ns2] i; rewrite coef_mkPoly /coef {ns1 ns2}/=.
elim: s1 i => [|c1 s1 IHs1] /= i.
  by rewrite sub_seq0 big1 // => j _; rewrite sub_seq0 simp.
rewrite sub_add_poly_seq big_ord_recl subn0 /=; congr (_ + _).
  case: (ltnP i (size s2)) => lti; first by rewrite (sub_maps 0).
  by rewrite !sub_default ?size_maps // simp.
by case: i => [|i] /=; rewrite (big_seq0, IHs1).
Qed.

Lemma coef_mul_poly_rev : forall p1 p2 i,
  coef (p1 *p p2) i = \sum_(j <= i) coef p1 (i - j) * coef p2 j.
Proof.
move=> p1 p2 i; rewrite coef_mul_poly (reindex ord_opp) /=.
  by apply: eq_bigr => j _; rewrite sub_ordK.
exists (@ord_opp i) => j _; exact: ord_oppK.
Qed.

Lemma coef_mul_C_poly : forall c p i, coef (polyC c *p p) i = c * coef p i.
Proof.
move=> c p i; rewrite coef_mul_poly big_ord_recl coef_polyC subn0 /=.
by rewrite big1 => [|j _]; rewrite /= ?coef_polyC simp.
Qed.

Lemma poly_mul1P : forall p, \C1 *p p = p.
Proof. by move=> p; apply/coef_eqP => i; rewrite coef_mul_C_poly simp. Qed.

Lemma coef_mul_poly_C : forall c p i, coef (p *p polyC c) i = coef p i * c.
Proof.
move=> c p i; rewrite coef_mul_poly_rev big_ord_recl coef_polyC subn0 /=.
by rewrite big1 => [|j _]; rewrite /= ?coef_polyC simp.
Qed.

Lemma poly_mulP1 : forall p, p *p \C1 = p.
Proof. by move=> p; apply/coef_eqP => i; rewrite coef_mul_poly_C simp. Qed.

Lemma poly_mulA : forall p1 p2 p3, p1 *p (p2 *p p3) = p1 *p p2 *p p3.
Proof.
move=> p1 p2 p3; apply/coef_eqP=> i; rewrite coef_mul_poly coef_mul_poly_rev.
pose coef3 j k := coef p1 j * (coef p2 (i - j - k) * coef p3 k).
transitivity (\sum_(j <= i) \sum_(k <= i | k <= i - j) coef3 j k).
  apply: eq_bigr => /= j _; rewrite coef_mul_poly_rev big_distrr /=.
  by rewrite (big_ord_narrow_leq (leq_subr _ _)).
rewrite (exchange_big_dep (setA _)) //=; apply: eq_bigr => k _.
transitivity (\sum_(j <= i | j <= i - k) coef3 j k).
  apply: eq_bigl => j; rewrite -ltnS -(ltnS j) -!leq_subS ?leq_ord //.
  by rewrite -ltn_0sub -(ltn_0sub j) !subn_sub addnC.
rewrite (big_ord_narrow_leq (leq_subr _ _)) coef_mul_poly big_distrl /=.
by apply: eq_bigr => j _; rewrite /coef3 !subn_sub addnC mulrA.
Qed.

Lemma poly_mul_addl : forall p1 p2 p3, p1 *p (p2 +p p3) = p1 *p p2 +p p1 *p p3.
Proof.
move=> *; apply/coef_eqP=> i; rewrite coef_add_poly !coef_mul_poly -big_split.
by apply: eq_bigr => j _; rewrite coef_add_poly mulr_addr.
Qed.

Lemma poly_mul_addr : forall p1 p2 p3, (p1 +p p2) *p p3 = p1 *p p3 +p p2 *p p3.
Proof.
Proof.
move=> *; apply/coef_eqP=> i; rewrite coef_add_poly !coef_mul_poly -big_split.
by apply: eq_bigr => j _; rewrite coef_add_poly mulr_addl.
Qed.

Lemma poly_nontriv : poly1 <> poly0.
Proof. by move/(congr1 seq_of_poly); rewrite seq_poly0 seq_poly1. Qed.

Definition opp_poly p := mul_poly (polyC (-1)) p.

Lemma poly_oppP : forall p, opp_poly p +p p = \C0.
Proof.
move=> p; apply/coef_eqP=> i; rewrite coef_add_poly coef_mul_C_poly coef0.
by rewrite mulNr simp addNr.
Qed.

Canonical Structure poly_additive_group :=
  AdditiveGroup poly_addA poly_addC poly_add0P poly_oppP.

Canonical Structure poly_basic_ring :=
  Ring.Basic poly_mulA poly_mul1P poly_mulP1
             poly_mul_addr poly_mul_addl poly_nontriv.

Lemma coef_opp : forall p i, coef (- p) i = - coef p i.
Proof. by move=> p i; rewrite coef_mul_C_poly mulN1r. Qed.

Lemma coef_mul_poly_X : forall p i,
  coef (p * \X) i = if i is j.+1 then coef p j else 0.
Proof.
move=> p i; rewrite coef_mul_poly_rev big_ord_recl coef_polyX !simp.
case: i => [|i]; first by rewrite big_seq0.
rewrite big_ord_recl coef_polyX /= subn1 /= big1 ?simp // => j _.
by rewrite coef_polyX simp.
Qed.

Lemma horner_def : forall c p, horner c p = p * \X + polyC c.
Proof.
move=> c p; apply/coef_eqP=> i.
rewrite coef_horner coef_add_poly coef_mul_poly_X coef_polyC.
by case: i => [|i]; rewrite simp.
Qed.

Lemma coef_sum : forall I (r : seq I) P F k,
  coef (\sum_(i <- r | P i) F i) k = \sum_(i <- r | P i) coef (F i) k.
Proof.
move=> I r P F k; apply: (big_morph (coef^~ k)).
by split=> *; rewrite (coef0, coef_add_poly).
Qed.

(* "degree" should be a proper type (see Sean's files). *)
(* Here we just use size directly, via the coercion to sequences. *)

Lemma size_poly0 : size poly0 = 0%N.
Proof. by rewrite seq_poly0. Qed.

Lemma size_poly0_eq : forall p : poly, (p == 0) = (size p == 0%N).
Proof. by rewrite /set1 /= seq_poly0; case/seq_of_poly. Qed.

Lemma size_polyC : forall c, c != 0 -> size (polyC c) = 1%N.
Proof. by move=> c c_nz; rewrite seq_polyC (negbET c_nz). Qed.

Lemma size_horner : forall p c, p != 0 -> size (horner c p) = (size p).+1.
Proof. by move=> p c; rewrite size_poly0_eq seq_horner; case (p : seq R). Qed.

Lemma coef_default : forall (p : poly) i, size p <= i -> coef p i = 0.
Proof. move=> *; exact: sub_default. Qed.

End Polynomial.

Bind Scope ring_scope with polynomial.
Notation "\poly_ ( i < n ) E" := (mkPoly (mkseq (fun i : nat => E) n))
   : ring_scope.
Notation "\C c" := (polyC c) : ring_scope.
Notation "\X" := (polyX _) : ring_scope.

Section PolynomialComRing.

Variable R : Ring.commutative_.

Lemma poly_mulC : forall p1 p2 : polynomial R, p1 * p2 = p2 * p1.
Proof.
move=> p1 p2; apply/coef_eqP=> i; rewrite coef_mul_poly coef_mul_poly_rev.
by apply: eq_bigr => j _; rewrite mulrC.
Qed.

Canonical Structure poly_commutative_ring := Ring.Commutative poly_mulC.

End PolynomialComRing.

Section EvalPolynomial.

Variable R : Ring.basic.

Fixpoint eval_poly_seq (s : seq R) (x : R) {struct s} : R :=
  if s is (Adds a s') then eval_poly_seq s' x * x + a else 0.

Definition eval_poly (p : polynomial R) := eval_poly_seq p.

Notation "p .[ x ]" := (eval_poly p x) : ring_scope.

Lemma eval_poly0 : forall x, 0.[x]= 0.
Proof. by rewrite /eval_poly seq_poly0. Qed.

Lemma eval_polyC : forall c x, (\C c).[x] = c.
Proof.
by move=> c x; rewrite /eval_poly seq_polyC; case: eqP; rewrite //= !simp.
Qed.

Lemma eval_polyX : forall x : R, \X.[x] = x.
Proof. by move=> x; rewrite /eval_poly seq_polyX /= !simp. Qed.

Lemma eval_horner : forall p c x, (horner c p).[x] = p.[x] * x + c.
Proof.
move=> p c x; rewrite /eval_poly seq_horner.
case/seq_of_poly: p; rewrite //= !simp; exact: eval_polyC.
Qed.

Lemma eval_mkPoly : forall s x, (mkPoly s).[x] = eval_poly_seq s x.
Proof.
by move=> s x; elim: s => [|a s /= <-] /=; rewrite (eval_poly0, eval_horner).
Qed.

Lemma eval_poly_expansion : forall p x,
  p.[x] = \sum_(i < size p) coef p i * x ^+i.
Proof.
rewrite /eval_poly /coef => p x.
elim: {p}(p : seq R) => /= [|a s ->]; first by rewrite big_seq0.
rewrite big_ord_recl simp addrC big_distrl /=; congr (_ + _).
by apply: eq_bigr => i _; rewrite -mulrA commr_exp.
Qed.

Lemma eval_add_poly_seq : forall s1 s2 x,
  eval_poly_seq (add_poly_seq s1 s2) x
    = eval_poly_seq s1 x + eval_poly_seq s2 x.
Proof.
elim=> [s2 | a1 s1 IHs [|a2 s2]] x /=; rewrite ?simp //= {}IHs.
by rewrite mulr_addl -!addrA (addrCA a1).
Qed.

Lemma eval_poly_plus : forall p q x, (p + q).[x] = p.[x] + q.[x].
Proof. by move=> p q x; rewrite eval_mkPoly eval_add_poly_seq. Qed.

Definition com_coef p (x : R) := forall i, (coef p i) * x = x * (coef p i).

Definition com_poly p (x : R) := x * p.[x] = p.[x] * x.

Lemma com_coef_poly : forall p x, com_coef p x -> com_poly p x.
Proof.
move=> p x com; rewrite /com_poly !eval_poly_expansion big_distrl big_distrr.
by apply: eq_bigr => i _; rewrite /= mulrA -com -!mulrA commr_exp.
Qed.

Lemma com_poly0 : forall x, com_poly 0 x.
Proof. by move=> *; rewrite /com_poly !eval_poly0 !simp. Qed.

Lemma com_poly1 : forall x, com_poly 1 x.
Proof. by move=> *; rewrite /com_poly !eval_polyC !simp. Qed.

Lemma com_polyX : forall x, com_poly \X x.
Proof. by move=> *; rewrite /com_poly !eval_polyX. Qed.

Lemma eval_poly_mult : forall p q x,
  com_poly q x -> (p * q).[x] = p.[x] * q.[x].
Proof.
move=> p q x com_qx; rewrite eval_mkPoly {1}/eval_poly.
elim: {p}(p : seq R) => /= [|a s IHs]; first by rewrite simp.
rewrite eval_add_poly_seq /= {}IHs simp addrC mulr_addl /eval_poly.
congr (_ + _); first by rewrite -!mulrA com_qx.
elim: {s q com_qx}(q : seq R) => /= [|b s ->]; first by rewrite simp.
by rewrite -mulrA -mulr_addr.
Qed.

Lemma eval_poly_Cmult : forall c p x, (\C c * p).[x] = c * p.[x].
Proof.
move=> c p x; rewrite eval_mkPoly seq_polyC /eval_poly.
case: eqP => [->|_] /=; rewrite ?eval_add_poly_seq /= !simp //.
by elim: (p : seq R) => /= [|a s ->]; rewrite ?simp // mulr_addr mulrA.
Qed.

Lemma eval_poly_opp : forall p x, (- p).[x] = - p.[x].
Proof. by move=> p x; rewrite eval_poly_Cmult mulN1r. Qed.

Definition eval_poly_lin :=
  (eval_poly_plus, eval_poly_opp, eval_polyX, eval_polyC, eval_horner,
   simp, eval_poly_Cmult, (fun p x => eval_poly_mult p (com_polyX x))).

Lemma factor0 : forall a, (\X - \C a).[a] = 0.
Proof. by move=> a; rewrite !eval_poly_lin addrN. Qed.

Lemma coef_factor : forall (a : R) i,
  coef (\X - \C a) i = match i with 0%N => - a | 1%N => 1 | _ => 0 end.
Proof.
move=> a i; rewrite coef_add_poly coef_polyX coef_opp coef_polyC.
by case: i => [|[|i]]; rewrite !(oppr0, simp).
Qed.

Theorem factor_theorem : forall p c,
  reflect (exists q, p = q * (\X - \C c)) (p.[c] == 0).
Proof.
move=> p c; apply: (iffP eqP) => [root_p_c | [q -> {p}]]; last first.
  by rewrite eval_poly_mult /com_poly factor0 ?simp.
exists (\poly_(i < size p) eval_poly_seq (drop i.+1 p) c).
apply/coef_eqP => [] [|i {root_p_c}]; rewrite coef_mul_poly_rev.
  rewrite big_ord_recl big_seq0 simp /=.
  move: root_p_c; rewrite  coef_factor coef_poly_of /eval_poly /coef drop1.
  case/seq_of_poly: p => [|a s]; rewrite /= ?simp // mulrN.
  by move=> eq_a0; rewrite (canRL eq_a0 (addKr _)) simp.
rewrite 2!big_ord_recl /= big1 => [|j _]; rewrite /= ?(coef_factor, simp) //.
rewrite !coef_poly_of subn0 subn1 /= mulrN; case: leqP => [le_p_i|lt_i_p].
  by rewrite drop_oversize // if_same !simp oppr0 coef_default.
by rewrite ltnW // (drop_sub 0 lt_i_p) addKr.
Qed.

End EvalPolynomial.

Notation "p .[ x ]" := (eval_poly p x) : ring_scope.

Unset Implicit Arguments.

