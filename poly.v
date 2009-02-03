Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice fintype.
Require Import ssralg bigops.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Open Local Scope ring_scope.

Reserved Notation "\C c" (at level 10, c at level 8).
Reserved Notation "\X" (at level 0).

Reserved Notation "\poly_ ( i < n ) E"
  (at level 36, E at level 36, i, n at level 50,
   format "\poly_ ( i  <  n )  E").

Notation Local simp := Monoid.simpm.

Section Polynomial.

Variable R : ringType.

(* Define a polynomial as a sequence *)

(* A coef sequence is normal if its last element is <> 0 *)
Definition normal (s : seq R) := last 1 s != 0.

Record polynomial : Type :=
  Poly {seq_of_poly :> seq R; _ : normal seq_of_poly}.

Notation poly := polynomial.

Bind Scope ring_scope with polynomial.

Canonical Structure poly_subType :=
  Eval hnf in [subType for seq_of_poly by polynomial_rect].
Definition poly_eqMixin := Eval hnf in [eqMixin of poly by <:].
Canonical Structure poly_eqType := Eval hnf in EqType poly_eqMixin.
Definition poly_choiceMixin := [choiceMixin of poly by <:].
Canonical Structure poly_choiceType := Eval hnf in ChoiceType poly_choiceMixin.

Lemma seq_of_poly_inj : injective seq_of_poly. Proof. exact: val_inj. Qed.

Lemma normal_seq0 : normal [::]. Proof. exact: nonzero1r. Qed.

Definition polyC c : poly := insubd (Poly normal_seq0) [:: c].

Notation "\C c" := (polyC c).

Definition poly0 := polyC 0.
Definition poly1 := polyC 1.

Notation Local "\C0" := poly0 (at level 0).
Notation Local "\C1" := poly1 (at level 0).

Lemma seq_polyC : forall c,
  polyC c = (if c == 0 then seq0 else [:: c]) :> seq R.
Proof. by move=> c; rewrite val_insubd if_neg. Qed.

Lemma polyC_inj : injective polyC.
Proof.
move=> c1 c2; move/(congr1 seq_of_poly); rewrite !seq_polyC.
by case: eqP => [->|_]; case: eqP => // _ [].
Qed.

Lemma seq_poly0 : \C0 = seq0 :> seq R.
Proof. by rewrite /poly0 seq_polyC eqxx. Qed.

Lemma seq_poly1 : \C1 = [:: 1] :> seq R.
Proof. by rewrite /poly1 seq_polyC (negbTE normal_seq0). Qed.

Definition horner c p : poly :=
  if p is Poly ((_ :: _) as s) ns then Poly (ns : normal (c :: s)) else \C c.

Lemma seq_horner : forall c p,
  horner c p = (if p : seq R is seq0 then \C c else c :: p) :> seq R.
Proof. by move=> c [[|c' s] ns] /=. Qed.

Lemma horner_inj : forall c1 c2 p1 p2,
  horner c1 p1 = horner c2 p2 -> c1 = c2 /\ p1 = p2.
Proof.
move=> c1 c2 p1 p2; move/(congr1 seq_of_poly); rewrite !seq_horner => eq_h.
suffices [->]: c1 :: p1 = c2 :: p2 by move/seq_of_poly_inj.
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

Definition polyX := mkPoly [:: 0; 1].

Notation "\X" := polyX.
Notation "\poly_ ( i < n ) E" := (mkPoly (mkseq (fun i : nat => E) n)).

Lemma seq_polyX : \X = [:: 0; 1] :> seq R.
Proof. by rewrite !seq_horner seq_poly0 seq_poly1. Qed.


Lemma mkPoly_seq : forall p : poly, mkPoly p = p.
Proof.
move=> [[|c s] ns] /=; apply seq_of_poly_inj=> /=; first exact: seq_poly0.
elim: s => [|c' s IHs] /= in c ns *; rewrite seq_horner ?IHs //.
by rewrite seq_poly0 seq_polyC (negbTE ns).
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
move/subnK=> sz_p2; case/eqP: (lead_coef_nz p2).
by rewrite /lead_coef -(sub_last 0) -sz_p2 /= -eq_coef sub_default ?leq_addr.
Qed.

(* Ring structure *)

Fixpoint add_poly_seq (s1 s2 : seq R) {struct s1} : seq R :=
  match s1, s2 with
  | seq0, _ => s2
  | _, seq0 => s1
  | c1 :: s1', c2 :: s2' => c1 + c2 :: add_poly_seq s1' s2'
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
  if s1 is c1 :: s1' then
    add_poly_seq (maps (fun c2 => c1 * c2) s2) (0 :: mul_poly_seq s1' s2)
  else seq0.

Definition mul_poly (p1 p2 : poly) := mkPoly (mul_poly_seq p1 p2).

Notation Local "p1 *p p2" := (mul_poly p1 p2) (at level 40).

Lemma coef_mul_poly : forall p1 p2 i,
  coef (p1 *p p2) i = \sum_(j < i.+1) coef p1 j * coef p2 (i - j).
Proof.
move=> [s1 ns1] [s2 ns2] i; rewrite coef_mkPoly /coef {ns1 ns2}/=.
elim: s1 i => [|c1 s1 IHs1] /= i.
  by rewrite sub_seq0 big1 // => j _; rewrite sub_seq0 simp.
rewrite sub_add_poly_seq big_ord_recl subn0 /=; congr (_ + _).
  case: (ltnP i (size s2)) => lti; first by rewrite (sub_maps 0).
  by rewrite !sub_default ?size_maps // simp.
case: i => [|i] /=; last exact: IHs1; by rewrite big_pred0 //; case.
Qed.

Lemma coef_mul_poly_rev : forall p1 p2 i,
  coef (p1 *p p2) i = \sum_(j < i.+1) coef p1 (i - j) * coef p2 j.
Proof.
move=> p1 p2 i; rewrite coef_mul_poly (reindex ord_opp) /=.
  by apply: eq_bigr => j _; rewrite (sub_ordK j).
exists (@ord_opp _ : 'I_(i.+1) -> _) => j _; exact: ord_oppK.
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
transitivity (\sum_(j < i.+1) \sum_(k < i.+1 | k <= i - j) coef3 j k).
  apply: eq_bigr => /= j _; rewrite coef_mul_poly_rev big_distrr /=.
  by rewrite (big_ord_narrow_leq (leq_subr _ _)).
rewrite (exchange_big_dep predT) //=; apply: eq_bigr => k _.
transitivity (\sum_(j < i.+1 | j <= i - k) coef3 j k).
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
move=> *; apply/coef_eqP=> i; rewrite coef_add_poly !coef_mul_poly -big_split.
by apply: eq_bigr => j _; rewrite coef_add_poly mulr_addl.
Qed.

Lemma poly_mul0P : forall p, \C0 *p p = \C0.
Proof. 
by move=> p; apply/coef_eqP=> i; rewrite coef_mul_C_poly coef0 mul0r. 
Qed.

Lemma poly_mulP0 : forall p, p *p \C0 = \C0.
Proof. 
by move=> p; apply/coef_eqP=> i; rewrite coef_mul_poly_C coef0 mulr0. 
Qed.

Lemma poly_nontriv : poly1 != poly0.
Proof. by rewrite -val_eqE /= seq_poly0 seq_poly1. Qed.

Definition opp_poly p := mul_poly (polyC (-1)) p.

Lemma poly_oppP : forall p, opp_poly p +p p = \C0.
Proof.
move=> p; apply/coef_eqP=> i; rewrite coef_add_poly coef_mul_C_poly coef0.
by rewrite mulNr simp addNr.
Qed.

Definition poly_zmodMixin :=
  ZmodMixin poly_addA poly_addC poly_add0P poly_oppP.
Canonical Structure poly_zmodType := Eval hnf in ZmodType poly_zmodMixin.

Definition poly_ringMixin :=
  RingMixin poly_mulA poly_mul1P poly_mulP1
            poly_mul_addr poly_mul_addl poly_nontriv.
Canonical Structure poly_ringType := Eval hnf in RingType poly_ringMixin.

Lemma polyC_0n: forall (c: R), c != 0 -> \C c != 0.
Proof.
by move=> c; move/eqP => Ec; apply/eqP; move/polyC_inj => HH; case Ec.
Qed. 

Definition simpl01 := (mul0r, mulr0, mul1r, mulr1, add0r, addr0, oppr0).

Lemma coef_opp : forall p i, coef (- p) i = - coef p i.
Proof. by move=> p i; rewrite coef_mul_C_poly mulN1r. Qed.

Lemma opp_polyC : forall c : R, - \C c = \C -c.
Proof.
by move=> c; apply/coef_eqP=> [[|i]]; rewrite !(coef_opp, coef_polyC, oppr0).
Qed.

Lemma coef_mul_poly_X : forall p i,
  coef (p * \X) i = if i is j.+1 then coef p j else 0.
Proof.
move=> p i; rewrite coef_mul_poly_rev big_ord_recl coef_polyX !simp.
case: i => [|i]; first by rewrite big_pred0 => [|[]].
rewrite big_ord_recl coef_polyX /= subn1 /= big1 ?simp // => j _.
by rewrite coef_polyX simp.
Qed.

Lemma horner_def : forall c p, horner c p = p * \X + polyC c.
Proof.
move=> c p; apply/coef_eqP=> i.
rewrite coef_horner coef_add_poly coef_mul_poly_X coef_polyC.
by case: i => [|i]; rewrite simp.
Qed.

Lemma coef_sum : forall (I : eqType) r (P : pred I) F k,
  coef (\sum_(i <- r | P i) F i) k = \sum_(i <- r | P i) coef (F i) k.
Proof.
move=> I r P F k; apply: (big_morph (coef^~ k)).
by split=> [|p q]; rewrite (coef0, coef_add_poly).
Qed.

(* "degree" should be a proper type (see Sean's files). *)
(* Here we just use size directly, via the coercion to sequences. *)

Lemma size_poly0 : size poly0 = 0%N.
Proof. by rewrite seq_poly0. Qed.

Lemma size_poly0_eq : forall p : poly, (p == 0) = (size p == 0%N).
Proof. by rewrite {1}/eq_op /= seq_poly0; case/seq_of_poly. Qed.

Lemma size_polyC : forall c, c != 0 -> size (polyC c) = 1%N.
Proof. by move=> c c_nz; rewrite seq_polyC (negbTE c_nz). Qed.

Lemma size_poly1 : size (1 : poly) = 1%N.
Proof. by rewrite size_polyC ?nonzero1r. Qed.

Lemma size_horner : forall p c, p != 0 -> size (horner c p) = (size p).+1.
Proof. by move=> p c; rewrite size_poly0_eq seq_horner; case (p : seq R). Qed.

Lemma size_polyX : size \X = 2.
Proof. by rewrite seq_polyX. Qed.

Lemma size_polyX_n : forall n, size (\X ^+ n) = n.+1.
Proof.
elim=> [|n IHn]; first exact: size_poly1.
rewrite -{1}addn1 exprn_addr expr1 -[_ * _]addr0 -horner_def.
by rewrite size_horner ?size_poly0_eq IHn.
Qed.

Lemma coef_default : forall (p : poly) i, size p <= i -> coef p i = 0.
Proof. move=> *; exact: sub_default. Qed.

Lemma leq_size_coef : forall (p: poly) i,
  (forall j, i <= j -> coef p j = 0) -> size p <= i.
Proof.
move=> p i p_i_0; case: leqP => lt_i_p //.
case/eqP: (lead_coef_nz p); rewrite /lead_coef -(sub_last 0).
case: {+}(size _) lt_i_p => [| s] //=; exact: p_i_0.
Qed.

Lemma leq_coef_size : forall (p: poly) i, coef p i <> 0 -> i < size p.
Proof.
by move=> p i H; case: leqP => Cspi //; case H; rewrite coef_default.
Qed.

Lemma size_opp : forall p : poly, size (- p) = size p.
Proof.
suffices: forall p : poly, size (- p) <= size p.
  by move=> le_sz p; apply/eqP; rewrite eqn_leq -{3}(opprK p) !le_sz.
move=> p; apply: leq_size_coef => j le_p_j.
by rewrite coef_opp coef_default ?oppr0.
Qed.

Lemma size_add : forall p q : poly, size (p + q) <= maxn (size p) (size q).
Proof.
move=> p q; apply: leq_size_coef => j; rewrite leq_maxl; case/andP=> Cpj Cqj.
by rewrite coef_add_poly !coef_default // !simpl01.
Qed.

Lemma size_addl : forall p q : poly,
  size p > size q -> size (p + q) = size p.
Proof.
move=> p q ltqp; apply/eqP; rewrite eqn_leq (leq_trans (size_add _ _)).
  have szp := ltn_predK ltqp; rewrite -szp leq_coef_size // coef_add_poly.
  rewrite addrC coef_default ?add0r; last by rewrite -ltnS szp.
  by move/eqP: (lead_coef_nz p); rewrite /lead_coef /coef -(sub_last 0) -szp.
by rewrite leq_maxl leqnn ltnW.
Qed.

Lemma size_mul : forall p q: poly, p != 0 -> size (p * q) < size p + size q.
Proof.
move=> p q Dp; have Pp: 0 < size p.
 by case: size (size_poly0_eq p) => // HH; case/negP: Dp; rewrite HH.
rewrite -(ltn_predK Pp) addSn; apply: leq_size_coef => j Hj. 
rewrite coef_mul_poly; apply: big1 => [[i Hi]] /= _.
case: (leqP (size p) i) => Cpi; first by rewrite (coef_default Cpi) !simpl01.
suff Cqi: size q <= j - i by rewrite (coef_default Cqi) !simpl01.
by rewrite -(leq_add2l (size p).-1) (leq_trans Hj) // -{1}(subnK (Hi: i <= _))
           leq_add2r -ltnS (ltn_predK Pp).
Qed.

Lemma size_exp : forall (p : poly) n, size (p ^+ n) <= ((size p).-1 * n).+1.
Proof.
move=> p n; case: (eqVneq p 0) => [-> | nzp].
  by case: n => [|n]; rewrite ?exprS ?mul0r size_poly0 ?size_poly1.
elim: n => [|n IHn]; first by rewrite size_poly1.
rewrite /= mulnS -ltnS -addSn -addnS (leq_trans (size_mul _ nzp)) ?leq_add //.
by rewrite prednK // lt0n -size_poly0_eq.
Qed.

Lemma size1P : forall p, reflect (exists c, p = \C c) (size p <= 1).
Proof.
move=> p; apply: (iffP eqP); last first.
  by case=> c ->; rewrite  val_insubd; case: normal.
move=> HH; exists (coef p 0).
apply/coef_eqP=> [[|i]]; rewrite coef_polyC // coef_default //.
by case: size HH => // [[|n]].
Qed.

Lemma lead_coefE : forall p : poly,
  lead_coef p = if p == 0 then 1 else coef p (size p).-1.
Proof.
move=> p; rewrite /lead_coef /coef -(sub_last 0).
by case: {+}(size _) (size_poly0_eq p) => [| s] ->.
Qed.

Lemma lead_coef_polyC : forall c, lead_coef (\C c) = if c == 0 then 1 else c.
Proof.
move=> c; rewrite lead_coefE coefE seq_polyC.
case: (@eqP _  c 0); move/eqP => Ec; first by rewrite (eqP Ec) eqxx.
by rewrite (negPf (polyC_0n Ec)).
Qed.

(* monomial *)

(* GG : This concept is completely redundant with \X ^+ n, which is *)
(* used later in the file, and benefits from generic ring lemmas    *)
(* from ssralg and bigops; please consider removing it.             *)
(* The notation doesn't seem all that essential, either; if you     *)
(* decide to keep it, it should come earlier.                       *)
Definition polyXn n := mkPoly (addsn n (0: R) [::1]).

(* GG: added format to suppress spurrious whitespace, raised level *)
(* to 8 to allow for \X^n.-1, etc.                                 *)
Notation "\X^ n" := (polyXn n) (at level 8, format "\X^ n").

Lemma polyXn0 : \X^0 = 1.
Proof. by rewrite  /polyXn /= horner_def !simpl01. Qed.

Lemma polyXn1 : \X^1 = \X.
Proof.  by rewrite  /polyXn /= !horner_def !simpl01. Qed.

Lemma seq_polyXn : forall n, polyXn n = addsn n (0: R) [:: 1] :> seq R.
Proof.
elim=> [|n]; first by rewrite seq_horner seq_poly0 seq_poly1.
by rewrite /polyXn /= seq_horner => ->; case: n.
Qed.

Lemma coef_polyXn : forall n i, coef \X^ n i = if i == n then 1 else 0.
Proof.
move=> n i; rewrite /coef seq_polyXn -cat_seqn sub_cat size_seqn.
case: ltngtP => Hl; last by rewrite Hl subnn.
  by rewrite -(subnK (ltnW Hl)); elim: {Hl}i (n - i)%N => [[|n1] | n1 Hrec].
elim: n i Hl => [| n Hrec] [| i] //; first by case: i.
by move=> Hi; rewrite Hrec.
Qed.

Lemma coef_mul_Xn_poly : forall n p i, 
  coef (\X^n * p) i = if i < n then 0 else coef p (i - n).
Proof.
move=> n p i; rewrite coef_mul_poly; case: ltnP => Cin.
  apply: big1 => [[j Hj] _] /=.
  rewrite !coef_polyXn; case: eqP; last by rewrite !simpl01.
  by move=> Ejn; move: Hj; rewrite  ltnNge Ejn Cin.
rewrite (bigD1 (Ordinal (Cin: n < i.+1))) //= coef_polyXn eqxx big1 ?simpl01 //.
move=> [j Hj] Hd /=.
rewrite coef_polyXn; case: eqP; last by rewrite !simpl01.
move=> Ejn; case/negP: Hd.
by do 2 apply/val_eqP => /=; apply/eqP.
Qed.

Lemma coef_mul_poly_Xn : forall n p i, 
  coef (p * \X^ n) i = if i < n then 0 else coef p (i - n).
Proof.
move=> n p i; rewrite coef_mul_poly_rev; case: ltnP => Cin.
  apply: big1 => [[j Hj] _] /=.
  rewrite !coef_polyXn; case: eqP; last by rewrite !simpl01.
  by move=> Ejn; move: Hj; rewrite  ltnNge Ejn Cin.
rewrite (bigD1 (Ordinal (Cin: n < i.+1))) //= coef_polyXn eqxx big1 ?simpl01 //.
move=> [j Hj] Hd /=.
rewrite coef_polyXn; case: eqP; last by rewrite !simpl01.
move=> Ejn; case/negP: Hd.
by do 2 apply/val_eqP => /=; apply/eqP.
Qed.

Lemma polyXnXm : forall n m,  \X^n * \X^m = \X^(n + m).
Proof.
move=> n m; apply/coef_eqP=> i.
rewrite coef_mul_Xn_poly !coef_polyXn.
case: ltnP => Cin.
  by rewrite eqn_leq [_ + _ <= _]leqNgt (leq_trans Cin (leq_addr _ _)) andbF.
(do 2 case: eqP) => //; first by move=> NEi Ei; case NEi; rewrite -Ei subnK.
by move=> Ei NEi; case NEi; rewrite Ei addKn.
Qed.

Lemma polyXnC : forall n p,  \X^n * p = p * \X^n.
Proof.
move=> n m; apply/coef_eqP=> i.
by rewrite coef_mul_Xn_poly coef_mul_poly_Xn.
Qed.

Lemma size_polyXn : forall n, size (\X^ n) = n.+1.
Proof. by move=> n; rewrite seq_polyXn size_addsn addnC. Qed.

Lemma polyC_mul: forall c1 c2, \C (c1 * c2) = \C c1 * \C c2.
Proof.
move=> c1 c2; apply/coef_eqP => i.
by rewrite coef_mul_C_poly !coef_polyC; case i; rewrite // mulr0. 
Qed.

(* Monic *)

(* GG: according to this definition, 0 is monic. I don't think that's *)
(* correct (it spoils lemmas about the degree of products with monic  *)
(* polynomials).                                                      *)
Definition monic p := lead_coef p == 1.

Lemma monic1 : monic 1.
Proof. by rewrite /monic /lead_coef seq_poly1. Qed.

Lemma monicX : monic \X.
Proof. by rewrite /monic /lead_coef seq_polyX. Qed.

Lemma monicXn : forall n, monic \X^n.
Proof.
by move=> n; rewrite /monic /lead_coef !seq_polyXn; elim: n {1}1 =>/=.
Qed.

Lemma lead_coef_mul : forall p q,
  coef (p * q) (size p + size q).-2 = coef p (size p).-1 * coef q (size q).-1.
Proof.
move=> p q.
case: (@eqP _ p 0) => Dp; first by rewrite Dp mul0r !coef0 mul0r.
case: (@eqP _ q 0) => Dq; first by rewrite Dq mulr0 !coef0 mulr0.
have Cp1: 0 < size p.
  by case: size (size_poly0_eq p) => // HH; case Dp; apply/eqP; rewrite HH.
have Cq1: 0 < size q.
  by case: size (size_poly0_eq q) => // HH; case Dq; apply/eqP; rewrite HH.
rewrite coef_mul_poly (@ltn_predK 0); last first.
  by move: Cp1 Cq1; (do 2 (case: size => //)) => *; rewrite addnS.
have Opq: (size p).-1 < (size p + size q).-1.
  by move: Cp1 Cq1; (do 2 (case: size => //)) => *; rewrite addnS leq_addr.
rewrite (bigD1 (Ordinal Opq)) //=  big1 /=  ?simpl01.
  by move: Cp1 Cq1; (do 2 (case: size => //)) => *; rewrite addnS addKn.
move=> [i Hi] /= Di.
case: (@leqP (size p) i) => Cip; first by rewrite coef_default // !simpl01.
rewrite (@coef_default q); first by rewrite ?simpl01 //.
move: Cip; rewrite leq_eqVlt; case/orP => Cip.
  by case/eqP: Di; apply/val_eqP; rewrite /= -(eqP Cip).
case: size Cq1 {Di}Hi => [|s1 _] //; case: size Cp1 Cip => [|s2 _] // Cip Hi.
by rewrite addnS -ltn_add_sub ltn_add2r.
Qed.

Lemma monic_mul: forall p q, monic p -> monic q -> monic (p * q).
Proof.
move=> p q; rewrite /monic !lead_coefE.
case: (@eqP _ p) => [->| Dp Cp]; first by rewrite simpl01 !eqxx.
case: (@eqP _ q) => [->| Dq Cq]; first by rewrite simpl01 !eqxx.
case: (@eqP _ (p * q)) => [//| Dpq].
have Cp1: 0 < size p.
  by case: size (size_poly0_eq p) => // HH; case Dp; apply/eqP; rewrite HH.
have Cq1: 0 < size q.
  by case: size (size_poly0_eq q) => // HH; case Dq; apply/eqP; rewrite HH.
have F1: 0 < size p + size q.
  by move: Cp1 Cq1; (do 2 (case: size => //)) => *; rewrite addnS addKn.
move/eqP: Dp => Dp.
have Cpq: coef (p * q) (size p + size q).-2 == 1.
  by rewrite lead_coef_mul (eqP Cp) (eqP Cq) !simpl01.
suff->: size (p * q) =  (size p + size q).-1 by done.
apply: anti_leq.
rewrite -ltnS (@ltn_predK 0) // size_mul //=.
rewrite -(@ltn_predK 0 (_.-1)).
  by apply: leq_coef_size; apply/eqP; rewrite (eqP Cpq) nonzero1r.
by move: Cp1 Cq1; (do 2 (case: size => //)) => *; rewrite addnS.
Qed.

Lemma monic_exp : forall p n, monic p -> monic (p ^+ n).
Proof. by move=> p n ?; elim: n => [|n IHn]; rewrite ?monic1 ?monic_mul. Qed.


(* Pseudo division *)
Definition edivp_rec (q : poly)  :=
  let sq := size q in
  let cq := lead_coef q in
  fix loop (n: nat) (c: R) (qq r: poly) {struct n} :=
      if size r < sq then (c,qq,r) else
      let m := \C (lead_coef r) * \X^ (size r - sq) in
      let c1 := cq * c in
      let qq1 := qq * \C cq + m in
      let r1 := r * \C cq - m * q in
      if n is (S n1) then loop n1 c1 qq1 r1 else (c1,qq1,r1).

Lemma edivp_mon_spec: forall p q n c qq r, monic q ->
 let d := edivp_rec q n c qq r in
 p = qq * q + r -> p = (d.1).2 * q + d.2.
Proof.
move=> p q; elim=> [| n Hrec] c qq r /=; case: ltnP => Hp //=.
  rewrite /monic; move/eqP->; rewrite !simpl01 => ->.
  rewrite mulr_addl -!addrA; congr (_ + _).
  by rewrite addrC -addrA addrC -!addrA addKr.
move=> Mq HH; apply: Hrec => //.
move:  Mq; rewrite /monic; move/eqP->; rewrite !simpl01.
rewrite HH mulr_addl -!addrA; congr (_ + _).
by rewrite addrC -addrA addrC -!addrA addKr.
Qed.

Lemma edivp_mod_spec: forall q n c (qq r: poly), q != 0 -> 
  size r <= n -> size (edivp_rec q n c qq r).2 < size q.
Proof.
move=> q; elim=> [| n Hrec] c qq r Hq Hqq /=; case: (@ltnP (size r)) => Hl //=.
   case/negP: Hq; rewrite size_poly0_eq.
   by case: size (leq_trans Hl Hqq).
apply: Hrec => //.
apply: leq_size_coef => j Hj.
rewrite coef_add_poly coef_opp -!mulrA coef_mul_poly_C 
        coef_mul_C_poly coef_mul_Xn_poly.
move: Hj; rewrite leq_eqVlt; case/orP => Hj; last first.
  rewrite coef_default; last by rewrite (leq_trans Hqq).
  rewrite coef_default; first by case: ltnP; rewrite !simpl01.
  by rewrite -{1}(subKn Hl) leq_sub2r // (leq_trans Hqq).
rewrite -(eqP Hj); move: Hqq; rewrite leq_eqVlt; case/orP => Hqq; last first.
  rewrite !coef_default //; first by case: ltnP; rewrite !simpl01.
  by rewrite -{1}(subKn Hl) leq_sub2r // (leq_trans Hqq).
move: Hl; rewrite /lead_coef /coef -!(sub_last 0) (eqP Hqq) /=.
have: 0 < size q by rewrite lt0n -size_poly0_eq.
case: {+}(size _) => [| n1] //= _ Cnn1.
by rewrite subKn // ltnNge subSS leq_subr addrN.
Qed.

Lemma edivp_scal_spec: forall q n c (qq r : poly),
  exists m, (edivp_rec q n c qq r).1.1 = (lead_coef q) ^+ m * c.
Proof.
move=> q; elim=> [|n IHn] c qq r /=.
  case: ifP; first by exists 0%N; rewrite mul1r.
  by exists 1%N; rewrite expr1.
case: ifP => _; first by exists 0%N; rewrite mul1r.
set c1 := _ * c; set qq1 := _ + _; set r1 := _ - _.
by have [m ->]:= IHn c1 qq1 r1; exists m.+1; rewrite exprSr -mulrA.
Qed.

Definition edivp (p q: poly): R * poly * poly :=
  if q == 0 then (1,0,p) else
  let cq := lead_coef q in
  let sq := size q in
  edivp_rec q (size p) 1 0 p.

Definition divp p q := ((edivp p q).1).2.
Definition modp p q := (edivp p q).2.
Definition scalp p q := ((edivp p q).1).1.
Definition dvdp p q := modp q p == 0.

Notation "m %/ d" := (divp m d) (at level 40, no associativity).
Notation "m %% d" := (modp m d) (at level 40, no associativity).
Notation "p %| q" := (dvdp p q) (at level 70, no associativity).

Lemma divp_size: forall p q: poly, size p < size q -> p %/ q = 0.
Proof.
move=> p q; rewrite /divp /edivp; case: eqP => Eq.
  by rewrite Eq size_poly0.
by case E1: (size p) => [| s] Hs /=; rewrite E1 Hs.
Qed.

Lemma modp_size: forall p q: poly, size p < size q -> p %% q = p.
Proof.
move=> p q; rewrite /modp /edivp; case: eqP => Eq.
  by rewrite Eq size_poly0.
by case E1: (size p) => [| s] Hs /=; rewrite E1 Hs /=.
Qed.

Lemma divp_mon_spec: forall p q, monic q -> p = p %/ q * q + p %% q.
Proof.
move=> p q Mq.
rewrite /divp /modp /scalp /edivp.
case: eqP => [->| Hq]; first by rewrite !simpl01.
by apply: edivp_mon_spec; rewrite // !simpl01.
Qed.

Lemma modp_spec: forall p q, q != 0 -> size (p %% q) < size q.
Proof.
move=> p q Hq.
rewrite /divp /modp /scalp /edivp.
case: eqP => He; first by case/negP: Hq; apply/eqP.
by apply: edivp_mod_spec.
Qed.

Lemma scalp_spec : forall p q, exists m, scalp p q = lead_coef q ^+ m.
Proof.
move=> p q; rewrite /divp /modp /scalp /edivp.
case: eqP => He; first by exists 0%N.
by have [m ->]:= (edivp_scal_spec q (size p) 1 0 p); rewrite mulr1; exists m.
Qed.

Lemma div0p: forall p, 0 %/ p = 0.
Proof.
move=> p; rewrite /divp /edivp; case: eqP => // Hp.
rewrite /edivp_rec !size_poly0.
case: (size p) (size_poly0_eq p) => //=.
by rewrite eqxx; move/idP; move/eqP => HH; case Hp.
Qed.

Lemma modp0: forall p, p %% 0 = p.
Proof. by rewrite /modp /edivp eqxx. Qed.

Lemma mod0p: forall p, 0 %% p = 0.
Proof.
move=> p; rewrite /modp /edivp; case: eqP => // Hp.
rewrite /edivp_rec !size_poly0.
case: (size p) (size_poly0_eq p) => //=.
by rewrite eqxx; move/idP; move/eqP->; rewrite !simpl01.
Qed.

Lemma dvdpPm: forall p q: poly, monic q ->
  reflect (exists qq, p = qq * q) (q %| p).
Proof.
move=> p q Mq; apply: (iffP idP).
  rewrite /dvdp; move/eqP=> Dqp.
  by exists (p %/ q); rewrite {1}(divp_mon_spec p Mq) Dqp !simpl01.
case=> qq Dqq; rewrite /dvdp.
pose d := qq - p %/ q.
have Epq: p %% q = d * q.
    rewrite mulr_addl mulNr -Dqq {2}(divp_mon_spec p Mq).
    by rewrite -addrA addrC -addrA addNr !simpl01.
case: (@eqP _ q 0) => Eq; first by rewrite Eq modp0 Dqq Eq !simpl01.
move/eqP: Eq => Eq; move: (modp_spec p Eq); rewrite Epq.
case: (@eqP _ d 0) => Em; first by rewrite Em !simpl01.
move/eqP: Em => Em; rewrite ltnNge; case/negP.
apply: leq_trans (leq_addr (size d).-1 _) _.
rewrite -(@prednK (_ + _)) ?ltn_0add ?lt0n -?size_poly0_eq ?Eq //.
rewrite -!subn1 addn_subA ?lt0n -?size_poly0_eq // !subn1 addnC.
apply: leq_coef_size; apply/eqP; rewrite lead_coef_mul.
have:= lead_coef_nz d; move/eqP: Mq; rewrite !lead_coefE (negPf Eq) => ->.
by rewrite mulr1 (negPf Em).
Qed.

Lemma dvdp0: forall p, p %| 0.
Proof. move=> p; apply/eqP; exact: mod0p. Qed.

Lemma modpC: forall p c, c != 0 -> p %% \C c = 0.
Proof.
move=> p c Hc; move/polyC_0n: (Hc); move/(@modp_spec p); rewrite size_polyC //.
by move=> HH1; apply/eqP; rewrite size_poly0_eq; case: size HH1.
Qed.

Lemma modp1: forall p, p %% 1 = 0.
Proof. move=> p; apply: modpC; exact: nonzero1r. Qed.

Lemma divp1: forall p, p %/ 1 = p.
Proof.
by move=> p; rewrite {2}(divp_mon_spec p monic1) modp1 !simpl01.
Qed. 

Lemma dvd1p: forall p, 1 %| p.
Proof. move=> p; apply/eqP; exact: modp1. Qed.

Lemma modp_mon_mull : forall p q: poly, monic q -> p * q %% q = 0.
Proof.
move=> p q Mq.
pose qq := p - (p * q) %/ q.
have Eq:  (p * q) %% q = qq * q.
  by rewrite mulr_addl {2}(divp_mon_spec (p * q) Mq) [_ * _ + _]addrC
             mulNr -addrA addrN simpl01.
case: (@eqP _ q 0) => Cq; first by rewrite Cq modp0 simpl01.
case: (@eqP _ qq 0) => Cp; first by rewrite Eq Cp simpl01.
move/eqP: Cp => Cp; move/eqP: Cq => Cq.
move: (modp_spec (p * q) Cq); rewrite Eq ltnNge; case/negP.
apply: leq_trans (leq_addr (size qq).-1 _) _.
rewrite -(@prednK (_ + _)) ?ltn_0add ?lt0n -?size_poly0_eq ?Cq //.
rewrite -!subn1 addn_subA ?lt0n -?size_poly0_eq // !subn1 addnC.
apply: leq_coef_size; apply/eqP; rewrite lead_coef_mul.
have:= lead_coef_nz qq; move/eqP: Mq; rewrite !lead_coefE (negPf Cq) => ->.
by rewrite mulr1 (negPf Cp).
Qed.

Lemma divp_mon_mull : forall p q: poly, q != 0 -> monic q -> p * q %/ q = p.
Proof.
move=> p q Cq Mq.
pose qq := p - (p * q) %/ q.
have Eq:  (p * q) %% q = qq * q.
  by rewrite mulr_addl {2}(divp_mon_spec (p * q) Mq) [_ * _ + _]addrC
             mulNr -addrA addrN simpl01.
suff Hqq: qq  = 0 by rewrite -[_ %/ _]add0r -Hqq addrAC addrK.
apply/eqP; case: eqP => //; move/eqP => Cqq.
move: (modp_spec (p * q) Cq); rewrite ltnNge Eq; case/negP.
apply: leq_trans (leq_addr (size qq).-1 _) _.
rewrite -(@prednK (_ + _)) ?ltn_0add ?lt0n -?size_poly0_eq ?Cq //.
rewrite -!subn1 addn_subA ?lt0n -?size_poly0_eq // !subn1 addnC.
apply: leq_coef_size; apply/eqP; rewrite lead_coef_mul.
have:= lead_coef_nz qq; move/eqP: Mq; rewrite !lead_coefE (negPf Cq) => ->.
by rewrite mulr1 (negPf Cqq).
Qed.

Lemma dvdp_mon_mull : forall p q: poly, monic q -> q %| p * q.
Proof. move=> p q Mq; apply/eqP; exact: modp_mon_mull. Qed.

(* Pseudo gcd *)
Definition gcdp (p q: poly)  :=
  let (p1,q1) := if size p < size q then (q,p) else (p,q) in
  if p1 == 0 then q1 else
  (fix loop (n: nat) (pp qq: poly) {struct n} :=
      let rr := pp %% qq in
      if rr == 0 then qq else 
      if n is (S n1) then loop n1 qq rr else rr) (size p1) p1 q1.

Lemma gcd0p: left_id 0 gcdp.
Proof.
move=> p; rewrite /gcdp size_poly0.
case: size (size_poly0_eq p) => [| n] /=.
  by rewrite eqxx; move/eqP->; rewrite /= eqxx.
move-> => /=; case: size => [| s]; rewrite modp0;
  case: eqP => Ep //.
by case: s => [| s]; rewrite mod0p eqxx.
Qed.

Lemma gcdp0: right_id 0 gcdp.
Proof.
move=> p; rewrite /gcdp size_poly0.
case: size (size_poly0_eq p) => [| n] /=.
  by rewrite eqxx; move/eqP->; rewrite /= eqxx.
move-> => /=; case: size => [| s]; rewrite modp0;
  case: eqP => Ep //.
by case: s => [| s]; rewrite mod0p eqxx.
Qed.

Lemma gcdpE : forall m n, 
  gcdp m n = if size m < size n then gcdp (n %% m) m else gcdp (m %% n) n.
Proof.
pose gcdp_rec := 
  fix loop (n: nat) (pp qq: poly) {struct n} :=
      let rr := pp %% qq in
      if rr == 0 then qq else 
      if n is (S n1) then loop n1 qq rr else rr.
have Irec: forall m n (p q: poly), size q <= m -> size q <= n 
      -> size q < size p -> gcdp_rec m p q = gcdp_rec n p q.
  elim=> [| m Hrec] [|n ] //= p q.
  - case: size (size_poly0_eq q) => [| s] //.
    rewrite eqxx; move/eqP-> => _ _; rewrite modp0.
    by case: n => [| n] //=; rewrite mod0p eqxx.
  - case: size (size_poly0_eq q) => [| s] //.
    rewrite eqxx; move/eqP-> => _ _; rewrite modp0.
    by case: (m) => [| m1] //=; rewrite mod0p eqxx.
  case: eqP=> Epq => // Sm Sn Sq.
  case: (@eqP _ q 0); move/eqP => Eq.
    by rewrite (eqP Eq) modp0; case: (m); case: (n) => //=;
       move=>*; rewrite mod0p eqxx.
  apply: Hrec; last apply: modp_spec => //.
    by rewrite -ltnS (leq_trans _ Sm) // modp_spec.
  by rewrite -ltnS (leq_trans _ Sn) // modp_spec.
move => m n; case:  (@eqP _ m 0); move/eqP=> Em.
  by rewrite (eqP Em) mod0p modp0 gcd0p gcdp0; case: ltnP.
case: (@eqP _ n 0); move/eqP => En.
  by case: ltnP; rewrite (eqP En) !(gcd0p,gcdp0,mod0p,modp0).
rewrite {2 3}/gcdp !modp_spec // (negPf Em) (negPf En).
rewrite /gcdp;  case: ltnP; rewrite (negPf Em,negPf En).
  case E1: (size n) => [|s] //.
  case: eqP => Enm.
    rewrite Enm; case: size => [| s1]; rewrite modp0 /= (negPf Em) //.
    by case: s1 => [| s1]; rewrite mod0p eqxx.
  rewrite  ltnS => HH.
  by apply: Irec => //; [apply: leq_trans HH; apply ltnW |apply ltnW|];
     apply modp_spec.
case E1: (size m) (size_poly0_eq m) => [|sm] //.
  rewrite eqxx;move/eqP->; rewrite mod0p eqxx.
  case E2: (size n) (size_poly0_eq n) => [|sn] //.
  by rewrite eqxx;move/eqP->; rewrite mod0p eqxx.
move=> _ Esn; case: eqP=> HH; try rewrite HH.
  case E2: (size n) (size_poly0_eq n) => [|sn] //.
    by rewrite eqxx;move/eqP->; rewrite mod0p eqxx.
  rewrite modp0 (negPf En) => _.
  case: (sn); rewrite mod0p /= eqxx //.
apply: Irec; last by apply modp_spec.
  by rewrite -ltnS (leq_trans (modp_spec _ _)).
by rewrite ltnW  //(modp_spec _ _).
Qed.

End Polynomial.

Bind Scope ring_scope with polynomial.
Notation "\poly_ ( i < n ) E" := (mkPoly (mkseq (fun i : nat => E) n))
   : ring_scope.
Notation "\C c" := (polyC c) : ring_scope.
Notation "\X" := (polyX _) : ring_scope.
Notation "\X^ n" := (polyXn _ n) (at level 8, format "\X^ n"): ring_scope.
Notation "m %/ d" := (divp m d) (at level 40, no associativity) : ring_scope.
Notation "m %% d" := (modp m d) (at level 40, no associativity) : ring_scope.
Notation "p %| q" := (dvdp p q) (at level 70, no associativity) : ring_scope.

Section PolynomialComRing.

Variable R : comRingType.

Lemma poly_mulC : forall p1 p2 : polynomial R, p1 * p2 = p2 * p1.
Proof.
move=> p1 p2; apply/coef_eqP=> i; rewrite coef_mul_poly coef_mul_poly_rev.
by apply: eq_bigr => j _; rewrite mulrC.
Qed.

Canonical Structure poly_commutative_ring := Eval hnf in ComRingType poly_mulC.

(* Pseudo-division in a commutative setting *)

Notation poly := (polynomial R).

Lemma edivp_spec: forall (p q: poly) n c qq r,
 let d := edivp_rec q n c qq r in
 \C c * p = qq * q + r -> \C (d.1).1 * p = (d.1).2 * q + d.2.
Proof.
move=> p q; elim=> [| n Hrec] c qq r /=; case: ltnP => Hp //=.
  rewrite polyC_mul -mulrA => ->.
  rewrite mulr_addl mulr_addr !mulrA -!addrA !(mulrC (\C _)).
  by congr (_ + _) => //; rewrite addrC -addrA addrC -addrA addKr.
move=> HH; apply: Hrec.
rewrite polyC_mul -mulrA HH.
rewrite mulr_addl mulr_addr !mulrA -!addrA !(mulrC (\C _)).
by congr (_ + _) => //; rewrite addrC -addrA addrC -addrA addKr.
Qed.

Lemma divp_spec: forall p q: poly, \C (scalp p q) * p = p %/ q * q + p %% q.
Proof.
move=> p q.
rewrite /divp /modp /scalp /edivp.
case: eqP => [->| Hq]; first by rewrite !simpl01.
by apply: edivp_spec; rewrite !simpl01.
Qed.

End PolynomialComRing.

Module BeforeIdomain. End BeforeIdomain.

Section PolynomialIdomain.

Variable R : idomainType.
Implicit Types x y : R.
Implicit Types p q : polynomial R.

Lemma size_mul_id : forall p q,
  p != 0 -> q != 0 -> size (p * q) = (size p + size q).-1.
Proof.
move=> p q Dp Dq; apply: anti_leq.
have Cp1: 0 < size p.
  by case: size (size_poly0_eq p) => // HH; case/negP: Dp; rewrite HH.
have Cq1: 0 < size q.
  by case: size (size_poly0_eq q) => // HH; case/negP: Dq; rewrite HH.
have F1: 0 < size p + size q.
  by move: Cp1 Cq1; (do 2 (case: size => //)) => *; rewrite addnS addKn.
rewrite -ltnS (ltn_predK F1) size_mul //.
rewrite -(@ltn_predK 0 (_.-1)); last first.
  by move: Cp1 Cq1; (do 2 (case: size => //)) => *; rewrite addnS.
apply: leq_coef_size; rewrite lead_coef_mul.
apply/eqP; rewrite mulr_neq0 //.
  by case: eqP Dp (lead_coefE p) (lead_coef_nz p)=> // _ _ ->.
by case: eqP Dq (lead_coefE q) (lead_coef_nz q)=> // _ _ ->.
Qed.

Lemma size_polyC_mul: forall c p, c != 0 -> size (\C c * p) = size p.
Proof.
move=> c p Ec; case: (@eqP _ p 0); move/eqP => Ep.
  by rewrite (eqP Ep) simpl01 size_poly0.
by rewrite size_mul_id // ?polyC_0n // size_polyC.
Qed.

Lemma lead_coef_mul_id: forall p q, 
  p != 0 -> q != 0 -> lead_coef (p * q) = lead_coef p * lead_coef q.
Proof.
move=> p q p_nz q_nz; move: (lead_coef_nz p) (lead_coef_nz q).
rewrite !lead_coefE (negbTE p_nz) (negbTE q_nz) => lp_nz lq_nz.
case: ifP => [|_]; last by rewrite size_mul_id // lead_coef_mul.
move/eqP=> pq0; have:= lead_coef_mul p q; rewrite pq0 coef0.
by move/eqP; rewrite eq_sym mulr_eq0; case/norP.
Qed.

Lemma scalp_id: forall p q, scalp p q != 0.
Proof.
move=> p q; case (scalp_spec p q) => m ->.
by rewrite expr_neq0 ?lead_coef_nz.
Qed.

(* idomain structure *)

Lemma poly_idomainMixin : forall p q, p * q = 0 -> (p == 0) || (q == 0).
Proof.
move=> p q pq0; apply/norP=> [[p_nz q_nz]]; move/eqP: (size_mul_id p_nz q_nz).
rewrite eq_sym pq0 size_poly0 -leqn0 -subn1 leq_sub_add leqNgt -addnS.
by rewrite leq_add // lt0n -size_poly0_eq.
Qed.

Definition poly_unit : pred (polynomial R) :=
  fun p => (size p == 1%N) && GRing.unit (coef p 0).

Definition poly_inv p := if poly_unit p then \C (coef p 0)^-1 else p.

Lemma poly_mulVp : {in poly_unit, left_inverse 1 poly_inv *%R}.
Proof.
move=> p Up; rewrite /poly_inv [poly_unit p]Up /coef.
case: p Up => [[|c []] //]; rewrite /normal /= => c0 Uc.
rewrite (_ : Poly _ = \C c); first by rewrite -polyC_mul mulVr.
by apply: seq_of_poly_inj; rewrite /= seq_polyC (negPf c0).
Qed.

Lemma poly_intro_unit : forall p q, q * p = 1 -> poly_unit p.
Proof.
move=> p q pq1; have: size (q * p) == 1%N by rewrite pq1 size_poly1.
case: (eqVneq p 0) => [-> | p_nz]; first by rewrite mulr0 size_poly0.
case: (eqVneq q 0) => [-> | q_nz]; first by rewrite mul0r size_poly0.
rewrite size_mul_id //.
rewrite -1?[size p]prednK -1?[size q]prednK ?lt0n -?size_poly0_eq //.
rewrite addnS eqSS eqn_add0 -!subn1 !eqn_sub0.
do 2!rewrite leq_eqVlt ltnS leqNgt lt0n -size_poly0_eq (p_nz, q_nz) orbF.
case/andP=> sz_q sz_p; rewrite /poly_unit sz_p; apply/unitrP=> /=.
have:= lead_coef_mul_id q_nz p_nz; rewrite pq1 mulrC.
rewrite !lead_coefE !size_poly0_eq size_poly1 coef_polyC (eqP sz_p) (eqP sz_q).
by move/esym=> qp1_0; exists q`_0%N; rewrite mulrC.
Qed.

Lemma poly_inv_out : {in predC poly_unit, poly_inv =1 id}.
Proof. by move=> p nUp; rewrite /poly_inv -if_neg [~~ _]nUp. Qed.

Definition poly_unitRingMixin :=
  ComUnitRingMixin poly_mulVp poly_intro_unit poly_inv_out.

Canonical Structure poly_unitRingType :=
   Eval hnf in UnitRingType poly_unitRingMixin.

Canonical Structure poly_comUnitRingType :=
   Eval hnf in ComUnitRingType poly_unitRingMixin.

Canonical Structure poly_idomainType :=
   Eval hnf in IdomainType poly_idomainMixin.

Lemma modp_mull : forall p q, p * q %% q = 0.
Proof.
move=> p q.
pose qq := \C (scalp (p* q) q) * p - (p * q) %/ q.
have Eq:  (p * q) %% q = qq * q.
   by rewrite mulr_addl -mulrA (divp_spec (p * q) q) [_ * _ + _]addrC
              mulNr -addrA addrN simpl01.
case: (@eqP _ q 0) => Cq; first by rewrite Cq modp0 simpl01.
case: (@eqP _ qq 0) => Cp; first by rewrite Eq Cp simpl01.
move/eqP: Cp => Cp; move/eqP: Cq => Cq.
move: (modp_spec (p * q) Cq); rewrite Eq (size_mul_id Cp Cq).
case: (size qq) (size_poly0_eq qq) => [| n _]; last by rewrite ltnNge leq_addl.
by rewrite eqxx; move/idP; move/eqP => HH; case/negP: Cp; apply/eqP.
Qed.

Lemma modpp : forall p, p %% p = 0.
Proof. by move=> p; rewrite -{1}(mul1r p) modp_mull. Qed.

Lemma dvdpp : forall p, p %| p.
Proof. move=> p; apply/eqP; exact: modpp. Qed.

Lemma divp_mull : forall p q, q != 0 -> p * q %/ q = \C(scalp (p * q) q) * p.
Proof.
move=> p q Cq.
pose qq := \C (scalp (p* q) q) * p - (p * q) %/ q.
have Eq:  (p * q) %% q = qq * q.
   by rewrite mulr_addl -mulrA (divp_spec (p * q) q) [_ * _ + _]addrC
              mulNr -addrA addrN simpl01.
suff Hqq: qq  = 0.
  by apply: (@addIr  _ (-((p * q) %/ q))); rewrite addrN -/qq Hqq.
apply/eqP; case: eqP => //; move/eqP => Cqq.
move: (modp_spec (p * q) Cq); rewrite Eq size_mul_id //.
case: (size qq) (size_poly0_eq qq) => [| n _]; last by rewrite ltnNge leq_addl.
by rewrite eqxx; move/idP; move/eqP => HH; case/negP: Cqq; apply/eqP.
Qed.

Lemma dvdpPc: forall p q, 
  reflect (exists c, exists qq, (c != 0) /\ (\C c * p = qq * q)) (q %| p).
Proof.
move=> p q; apply: (iffP idP).
  rewrite /dvdp; move/eqP=> Dqp.
  exists (scalp p q); exists (p %/ q).
  by split; [exact: scalp_id | rewrite divp_spec Dqp !simpl01].
case=> c; case=> qq; case=> Dc Dqq.
have Ecc: \C c != 0 by apply: polyC_0n.
case: (@eqP _ p 0); move/eqP => Ep; first by rewrite (eqP Ep) dvdp0.
pose p1 := \C (scalp p q)  * qq - \C c * (p %/ q).
have E1: \C c * (p %% q) = p1 * q.
  rewrite mulr_addl {1}mulNr -mulrA -Dqq mulrCA.
  by rewrite divp_spec mulr_addr [\C c * _ + _]addrC !mulrA addrK.
rewrite /dvdp; apply/idPn=> m_nz.
have: p1 * q != 0 by rewrite -E1 mulr_neq0.
rewrite mulr_eq0; case/norP=> p1_nz q_nz.
move: (size_mul_id p1_nz q_nz) (modp_spec p q_nz).
rewrite -E1 size_mul_id // size_polyC // add1n /= => ->.
by rewrite ltnNge -[size p1]prednK ?leq_addl // lt0n -size_poly0_eq.
Qed.

Lemma size_dvdp: forall p1 p2, p2 != 0 -> p1 %| p2 -> size p1 <= size p2.
Proof.
move=> p1 p2 Ep2; case/dvdpPc => c1 [q1 [Ec1 Ec1p2]].
have: q1 * p1 != 0 by rewrite -Ec1p2 !size_poly0_eq size_polyC_mul in Ep2 *. 
rewrite mulr_eq0; case/norP=> Ep1 Eq1.
rewrite -(size_polyC_mul p2 Ec1) Ec1p2 size_mul_id //.
by rewrite -[size q1]prednK ?leq_addl // lt0n -size_poly0_eq.
Qed.

Lemma dvdp_mull : forall d m n : polynomial R, d %| n -> d %| m * n.
Proof.
move=> d m n; case/dvdpPc => c [q [Hc Hq]].
apply/dvdpPc; exists c; exists (m * q); split => //.
by rewrite -mulrA -Hq !mulrA [m * _]mulrC.
Qed.

Lemma dvdp_mulr: forall d m n: polynomial R, d %| m -> d %|  m * n.
Proof. by move=> d m n d_m; rewrite mulrC dvdp_mull. Qed.

Lemma dvdp_mul: forall d1 d2 m1 m2 : polynomial R, 
  d1 %| m1 -> d2 %| m2 -> d1 * d2 %| m1 * m2.
Proof.
move=> d1 d2 m1 m2; case/dvdpPc=> c1 [q1 [Hc1 Hq1]];
  case/dvdpPc=> c2 [q2 [Hc2 Hq2]].
apply/dvdpPc; exists (c1 * c2); exists (q1 * q2); split.
  by rewrite mulr_neq0.
by rewrite polyC_mul mulrCA -!mulrA mulrCA mulrA Hq1 Hq2 mulrCA -!mulrA mulrCA.
Qed.

Lemma dvdp_trans: forall n d m : polynomial R, d %| n -> n %| m -> d %| m.
Proof. 
move=> n d m; case/dvdpPc=> c1 [q1 [Hc1 Hq1]];
  case/dvdpPc=> c2 [q2 [Hc2 Hq2]].
apply/dvdpPc; exists (c2 * c1); exists (q2 * q1); split.
  by apply: mulr_neq0.
rewrite -mulrA -Hq1 [_ * n]mulrC mulrA -Hq2 polyC_mul -!mulrA; congr (_ * _).
by rewrite mulrC.
Qed.

Lemma dvdp_addr : forall m d n : polynomial R,
  d %| m -> (d %| m + n) = (d %| n).
Proof.
move=> n d m; case/dvdpPc=> c1 [q1 [Hc1 Hq1]];
     apply/dvdpPc/dvdpPc; case=> c2 [q2 [Hc2 Hq2]].
  exists (c1 * c2); exists (\C c1 * q2 - \C c2 * q1); split.
    by apply: mulr_neq0.
  by rewrite mulr_addl mulNr -![_ * _ * d]mulrA -Hq1 -Hq2 !mulrA 
            [\C c2 * _]mulrC -polyC_mul -mulrN -mulr_addr [n + _]addrC addrK.
exists (c1 * c2); exists (\C c1 * q2 + \C c2 * q1); split.
  by apply: mulr_neq0.
by rewrite mulr_addl -![_ * _ * d]mulrA -Hq1 -Hq2 !mulrA
          [\C c2 * _]mulrC -polyC_mul -mulr_addr [n + _]addrC.
Qed.

Lemma dvdp_addl : forall n d m : polynomial R,
  d %| n -> (d %| m + n) = (d %| m).
Proof. by move=> n d m; rewrite addrC; exact: dvdp_addr. Qed.

Lemma dvdp_add : forall d m n: polynomial R, d %| m -> d %| n -> d %| m + n.
Proof. by move=> n d m; move/dvdp_addr->. Qed.

Lemma dvdp_add_eq : forall d m n: polynomial R,
  d %| m + n -> (d %| m) = (d %| n).
Proof. by move=> *; apply/idP/idP; [move/dvdp_addr <-| move/dvdp_addl <-]. Qed.

Lemma dvdp_subr : forall d m n: polynomial R,
  d %| m -> (d %| m - n) = (d %| n).
Proof. by move=> *; apply dvdp_add_eq; rewrite -addrA addNr simpl01. Qed.

Lemma dvdp_subl : forall d m n: polynomial R,
  d %| n -> (d %| m - n) = (d %| m).
Proof. by move=> d m n Hn; rewrite dvdp_addl // dvdp_mull. Qed.

Lemma dvdp_sub : forall d m n: polynomial R, d %| m -> d %| n -> d %| m - n.
Proof.  by move=> d n m Dm Dn; rewrite dvdp_subl. Qed.

Lemma dvdp_mod : forall d m n: polynomial R,
  d %| m -> (d %| n) = (d %| n %% m).
Proof.
move=> d n m; case/dvdpPc => c1 [q1 [Ec1 Eq1]].
apply/dvdpPc/dvdpPc=> [] [] c2 [q2 [Ec2 Eq2]]; last first.
  exists (c1 * c2 * scalp m n).
  exists (\C c2 * (m  %/ n) * q1 + \C c1 * q2); split.
    by rewrite !mulr_neq0 ?scalp_id.
  rewrite polyC_mul -mulrA divp_spec polyC_mul mulr_addr.
  by rewrite -!mulrA [\C c1 * _]mulrC -!mulrA [n * _]mulrC Eq1 Eq2 mulr_addl -!mulrA .
exists (c1 * c2); exists (\C c1 * \C (scalp m n) * q2 - \C c2 * (m %/ n) * q1); split.
    by rewrite !mulr_neq0 ?scalp_id.
by rewrite mulr_addl -!mulrA -Eq2 !mulrA [_ * \C c2] mulrC -!mulrA
           divp_spec mulr_addr [_ * n]mulrC !mulrA Eq1
           polyC_mul mulr_addr -!mulrA [ m %/ _ * _]mulrC !mulrA
           [_ * _ + _]addrC -!mulrA addrK !mulrA [_ * \C c2] mulrC.
Qed.

Lemma gcdpp : idempotent (@gcdp R).
Proof. by move=> p; rewrite gcdpE ltnn modpp gcd0p. Qed.

Lemma dvdp_gcd2 : forall m n: polynomial R, (gcdp m n %| m) && (gcdp m n %| n).
Proof.
move=> m n.
elim: {m n}minn {-2}m {-2}n (leqnn (minn (size n) (size m))) => [|r Hrec] m n.
  case: size (size_poly0_eq n) => [| s].
    by rewrite eqxx; move/eqP->; rewrite gcdp0 dvdpp dvdp0.
  case: size (size_poly0_eq m) => [| t] //.
    by rewrite eqxx; move/eqP->; rewrite gcd0p dvdpp dvdp0.
  by rewrite /minn; case: ltnP.
case: (@eqP _ m  0); move/eqP => Em; first by rewrite (eqP Em) gcd0p dvdp0 dvdpp.
move=> HH; rewrite gcdpE; case: ltnP => Cnm.
  suff: minn (size m) (size (n %% m)) <= r.
    by move/Hrec; case/andP => E1 E2; rewrite E2 (dvdp_mod _ E2).
  rewrite leq_minl orbC -ltnS (leq_trans _ HH) //.
  by rewrite (leq_trans (modp_spec _ Em)) // leq_minr ltnW // leqnn.
case: (@eqP _ n  0); move/eqP => En.
  by rewrite (eqP En) modp0 gcdp0 dvdp0 dvdpp.
suff: minn (size n) (size (m %% n)) <= r.
  by move/Hrec; case/andP => E1 E2; rewrite E2 andbT (dvdp_mod _ E2).
rewrite leq_minl orbC -ltnS (leq_trans _ HH) //.
by rewrite (leq_trans (modp_spec _ En)) // leq_minr leqnn.
Qed.

Lemma dvdp_gcdl : forall m n: polynomial R, gcdp m n %| m.
Proof. by move=> m n; case/andP: (dvdp_gcd2 m n). Qed.

Lemma dvdp_gcdr : forall m n: polynomial R, gcdp m n %| n.
Proof. by move=> m n; case/andP: (dvdp_gcd2 m n). Qed.

Lemma dvdp_gcd : forall p m n: polynomial R, p %| gcdp m n = (p %| m) && (p %| n).
Proof.
move=> p m n; apply/idP/andP=> [dv_pmn | [dv_pm dv_pn]].
  by rewrite ?(dvdp_trans dv_pmn) ?dvdp_gcdl ?dvdp_gcdr.
elim: {m n}minn {-2}m {-2}n (leqnn (minn (size n) (size m))) dv_pm dv_pn
        => [|r Hrec] m n.
  case: size (size_poly0_eq n) => [| s].
    by rewrite eqxx; move/eqP->; rewrite gcdp0.
  case: size (size_poly0_eq m) => [| t] //.
    by rewrite eqxx; move/eqP->; rewrite gcd0p.
  by rewrite /minn; case: ltnP.
case: (@eqP _ m  0); move/eqP => Em; first by rewrite (eqP Em) gcd0p.
move=> HH Dm Dn; rewrite gcdpE; case: ltnP => Cnm.
  apply: Hrec => //; last by rewrite -(dvdp_mod _ Dm).
  rewrite leq_minl orbC -ltnS (leq_trans _ HH) //.
  by rewrite (leq_trans (modp_spec _ Em)) // leq_minr ltnW // leqnn.
case: (@eqP _ n  0); move/eqP => En; first by rewrite (eqP En) modp0 gcdp0.
apply: Hrec => //; last by rewrite -(dvdp_mod _ Dn).
rewrite leq_minl orbC -ltnS (leq_trans _ HH) //.
by rewrite (leq_trans (modp_spec _ En)) // leq_minr leqnn.
Qed.

(* Equality modulo a factor *)

Definition eqp (p1 p2: polynomial R) :=  (p1 %| p2) && (p2 %| p1).

Notation "p1 '%=' p2" := (eqp p1 p2)
  (at level 70, no associativity).

Lemma eqpP: forall m n: polynomial R,
  reflect (exists c1, exists c2, [/\ c1 !=0, c2 != 0 & \C c1 * m = \C c2 *  n])
          (m %= n).
Proof.
move=> m n; apply: (iffP idP); last first.
  case=> c1; case=> c2; case => Hc1 Hc2 Ec1c2.
  by apply/andP; split; apply/dvdpPc;
      [exists c2; exists (\C c1) | exists c1; exists (\C c2)].
case/andP; case/dvdpPc => c1 [q1 [Hc1 Hq1]].
case/dvdpPc => c2 [q2 [Hc2 Hq2]].
have: (\C c1 * \C c2 - q1 * q2) * m == 0.
  by rewrite mulr_addl -mulrA Hq2 [q2 * _]mulrC mulrA Hq1
         [q1 * _]mulrC -mulrA mulrC mulNr addrN.
rewrite mulr_eq0; case/pred2P=> Em; last first.
  by exists c2; exists c1; split => //; rewrite Hq1 Em !simpl01.
have Eq1q2: q1 * q2 = \C c1 * \C c2.
 by apply: (@addIr _ (- (q1 * q2))); rewrite Em addrN.
have: q1 * q2 != 0.
  by rewrite Eq1q2 -[\C c2] mulr1 size_poly0_eq 2?size_polyC_mul ?size_poly1.
rewrite mulr_eq0; case/norP=> Eq1 Eq2.
have: size q2 <= 1.
  move: (size_mul_id Eq1 Eq2); rewrite Eq1q2 -polyC_mul size_polyC; last first.
    exact: mulr_neq0.
  by move->; rewrite -[size q1]prednK ?leq_addl // lt0n -size_poly0_eq.
case/size1P=> c3 Ec3; exists c2; exists c3; split => //; last by rewrite -Ec3.
by apply/eqP=> HH; case/eqP: Eq2; rewrite Ec3 HH.
Qed.

Lemma eqpxx: forall p, p %= p.
Proof. by move=> p; rewrite /eqp dvdpp. Qed. 

Lemma eqp_sym: forall p1 p2, (p1 %= p2) = (p2 %= p1).
Proof. by move=> p1 p2; rewrite /eqp andbC. Qed.

Lemma eqp_trans : forall p1 p2 p3, p1 %= p2 -> p2 %= p3 -> p1 %= p3.
Proof.
move=> p1 p2 p3; case/andP => Dp1 pD1; case/andP => Dp2 pD2.
by rewrite /eqp (dvdp_trans Dp1) // (dvdp_trans pD2).
Qed.

Lemma eqp0E : forall p, (p %= 0) = (p == 0).
Proof.
move=> p; case: eqP; move/eqP=> Ep; first by rewrite (eqP Ep) eqpxx.
by apply/negP; case/andP=> _; rewrite /dvdp modp0 (negPf Ep).
Qed.

Lemma size_eqp: forall p1 p2, p1 %= p2 -> size p1 = size p2.
Proof.
move=> p1 p2.
case: (@eqP _ p2 0); move/eqP => Ep2.
  by rewrite (eqP Ep2) eqp0E; move/eqP->.
rewrite eqp_sym; case: (@eqP _ p1 0); move/eqP => Ep1.
  by rewrite (eqP Ep1) eqp0E; move/eqP->.
by case/andP => Dp1 Dp2; apply: anti_leq; rewrite !size_dvdp.
Qed.

(* Now we can state that gcd is commutative modulo a factor *)
Lemma gcdpC: forall p1 p2, gcdp p1 p2 %= gcdp p2 p1.
Proof.
by move=>p1 p2; rewrite /eqp !dvdp_gcd !dvdp_gcdl !dvdp_gcdr.
Qed.

End PolynomialIdomain.

Section EvalPolynomial.

Variable R : ringType.

Fixpoint eval_poly_seq (s : seq R) (x : R) {struct s} : R :=
  if s is a :: s' then eval_poly_seq s' x * x + a else 0.

Canonical Structure poly_exprType :=
  @ExprType _ _ (polynomial R) [eta eval_poly_seq].

Lemma eval_poly0 : forall x, (0 : polynomial R).[x] = 0.
Proof. by move=> x; rewrite evalE /= seq_poly0. Qed.

Lemma eval_polyC : forall c x, (\C c).[x] = c.
Proof.
by move=> c x; rewrite evalE /= seq_polyC; case: eqP; rewrite //= !simp.
Qed.

Lemma eval_polyX : forall x : R, \X.[x] = x.
Proof. by move=> x; rewrite evalE /= seq_polyX /= !simp. Qed.

Lemma eval_horner : forall p c x, (horner c p).[x] = p.[x] * x + c.
Proof.
move=> p c x; rewrite !evalE /= seq_horner.
case/seq_of_poly: p; rewrite //= !simp; exact: eval_polyC.
Qed.

Lemma eval_mkPoly : forall s x, (mkPoly s).[x] = eval_poly_seq s x.
Proof.
by move=> s x; elim: s => [|a s /= <-] /=; rewrite (eval_poly0, eval_horner).
Qed.

Lemma eval_poly_expansion : forall (p : polynomial R) x,
  p.[x] = \sum_(i < size p) coef p i * x ^+ i.
Proof.
move=> p x; rewrite evalE /= /coef.
elim: {p}(p : seq R) => /= [|a s ->]; first by rewrite big_pred0 => [|[]].
rewrite big_ord_recl simp addrC big_distrl /=; congr (_ + _).
by apply: eq_bigr => i _; rewrite -mulrA exprSr.
Qed.

Lemma eval_add_poly_seq : forall s1 s2 x,
  eval_poly_seq (add_poly_seq s1 s2) x
    = eval_poly_seq s1 x + eval_poly_seq s2 x.
Proof.
elim=> [s2 | a1 s1 IHs [|a2 s2]] x /=; rewrite ?simp //= {}IHs.
by rewrite mulr_addl -!addrA (addrCA a1).
Qed.

Lemma eval_poly_add : forall (p q : polynomial R) x,
  (p + q : polynomial R).[x] = p.[x] + q.[x].
Proof. by move=> p q x; rewrite eval_mkPoly eval_add_poly_seq. Qed.

Definition com_coef p (x : R) := forall i, (coef p i) * x = x * (coef p i).

Definition com_poly (p : polynomial R) x := x * p.[x] = p.[x] * x.

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

Lemma eval_poly_mul : forall (p q : polynomial R) x,
  com_poly q x -> (p * q : polynomial R).[x] = p.[x] * q.[x].
Proof.
move=> p q x com_qx; rewrite eval_mkPoly evalE /=.
elim: {p}(p : seq R) => /= [|a s IHs]; first by rewrite simp.
rewrite eval_add_poly_seq /= {}IHs simp addrC mulr_addl evalE /=.
congr (_ + _); first by rewrite -!mulrA com_qx.
elim: {s q com_qx}(q : seq R) => /= [|b s ->]; first by rewrite simp.
by rewrite -mulrA -mulr_addr.
Qed.

Lemma eval_poly_exp : forall p x n,
  com_poly p x -> (p ^+ n : polynomial R).[x] = p.[x] ^+ n.
Proof.
move=> p x n com_px; elim: n => [|n IHn]; first by rewrite eval_polyC.
by rewrite -addn1 !exprn_addr !expr1 -IHn eval_poly_mul.
Qed.

Lemma eval_polyX_n : forall x n, (\X ^+ n : polynomial R).[x] = x ^+ n.
Proof. by move=> x n; rewrite eval_poly_exp /com_poly eval_polyX. Qed.

Lemma eval_poly_Cmul : forall c (p : polynomial R) x,
  (\C c * p : polynomial R).[x] = c * p.[x].
Proof.
move=> c p x; rewrite eval_mkPoly seq_polyC evalE /=.
case: eqP => [->|_] /=; rewrite ?eval_add_poly_seq /= !simp //.
by elim: (p : seq R) => /= [|a s ->]; rewrite ?simp // mulr_addr mulrA.
Qed.

Lemma eval_poly_opp : forall (p : polynomial R) x,
  (- p : polynomial R).[x] = - p.[x].
Proof. by move=> p x; rewrite eval_poly_Cmul mulN1r. Qed.

Definition eval_poly_lin :=
  (eval_poly_add, eval_poly_opp, eval_polyX, eval_polyC, eval_horner,
   simp, eval_poly_Cmul, (fun p x => eval_poly_mul p (com_polyX x))).

Lemma factor0 : forall a, (\X - \C a : polynomial R).[a] = 0.
Proof. by move=> a; rewrite !eval_poly_lin addrN. Qed.

Lemma coef_factor : forall (a : R) i,
  coef (\X - \C a) i = match i with 0%N => - a | 1%N => 1 | _ => 0 end.
Proof.
move=> a i; rewrite coef_add_poly coef_polyX coef_opp coef_polyC.
by case: i => [|[|i]]; rewrite !(oppr0, simp).
Qed.

Lemma seq_polyXc: forall c: R, \X + \C c = [::c;1] :> seq R.
Proof.
move=> c; rewrite /(_ + _) /= /add_poly seq_polyX seq_polyC /=.
by case: eqP => [->| _];
   rewrite ?simpl01 !seq_horner !seq_polyC !eqxx ?simpl01 // -if_neg nonzero1r.
Qed.

Theorem factor_theorem : forall (p : polynomial R) c,
  reflect (exists q, p = q * (\X - \C c)) (p.[c] == 0).
Proof.
move=> p c; apply: (iffP eqP) => [root_p_c | [q -> {p}]]; last first.
  by rewrite eval_poly_mul /com_poly factor0 ?simp.
rewrite opp_polyC; exists (p %/ (\X + \C -c)).
have MXc: monic (\X + \C (-c)) by rewrite /monic /lead_coef seq_polyXc.
move: (divp_mon_spec p MXc) root_p_c => HH; rewrite {1 2}HH.
have Dxc: \X + \C (- c) != 0 by rewrite size_poly0_eq seq_polyXc.
have:= modp_spec p Dxc.
rewrite seq_polyXc /= ltnS; case/size1P => c1 ->.
pose f := (eval_poly_add,eval_poly_mul,eval_polyX, eval_polyC, addrN, simpl01).
by rewrite !f => [->|]; rewrite /com_poly ?f.
Qed.

End EvalPolynomial.

Section MaxRoots.

Variable R : unitRingType.

Definition roots (p : polynomial R) : pred R := fun x => p.[x] == 0.

Definition diff_root (x y : R) := (x * y == y * x) && GRing.unit (y - x).

Fixpoint uniq_roots (rs : seq R) {struct rs} :=
  if rs is x :: rs' then all (diff_root x) rs' && uniq_roots rs' else true.

Theorem max_ring_poly_roots : forall (p : polynomial R) rs,
  p != 0 -> all (roots p) rs -> uniq_roots rs -> size rs < size p.
Proof.
move=> p rs; elim: rs p => [|x rs IHrs] p nzp /=.
  by rewrite lt0n -size_poly0_eq.
case/andP=> p_x p_rs; case/andP=> x_rs Urs.
case/factor_theorem: p_x => q def_p.
have nzq: q != 0 by apply: contra nzp => q0; rewrite def_p (eqP q0) mul0r.
have szXx: size (\X - \C x) = 2 by rewrite opp_polyC seq_polyXc.
have ->: size p = (size q).+1.
  apply/eqP; rewrite eqn_leq def_p -ltnS (leq_trans (size_mul _ nzq)).
    apply: leq_coef_size; apply/eqP.
    rewrite -[size q]/(2 + size _).-2 addnC -szXx.
    rewrite lead_coef_mul /coef opp_polyC seq_polyXc mulr1.
    by have:= lead_coef_nz q; rewrite lead_coefE (negPf nzq).
  by rewrite szXx addnS addn1.
apply: IHrs Urs => //; apply/allP=> y rs_y.
case/andP: (allP x_rs _ rs_y) => cxy Uxy.
have:= allP p_rs _ rs_y; rewrite /roots def_p eval_poly_mul; last first.
  by rewrite /com_poly !eval_poly_lin mulr_addl mulr_addr mulrN mulNr (eqP cxy).
by rewrite !eval_poly_lin (can2_eq (mulrK Uxy) (divrK Uxy)) mul0r.
Qed.

End MaxRoots.

Theorem max_poly_roots : forall (F : fieldType) (p : polynomial F) rs,
  p != 0 -> all (roots p) rs -> uniq rs -> size rs < size p.
Proof.
move=> F p rs nzp p_rs Urs; apply: max_ring_poly_roots nzp p_rs _ => {p}//.
elim: rs Urs => //= x rs IHrs; case/andP=> rs_x; move/IHrs->; rewrite andbT.
apply/allP=> y rs_y; rewrite /diff_root mulrC eqxx unitfE.
by rewrite (can2_eq (subrK _) (addrK _)) add0r; apply: contra rs_x; move/eqP<-.
Qed.
