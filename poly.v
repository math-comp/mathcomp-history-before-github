Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype.
Require Import ssralg bigops.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import Ring.

Reserved Notation "\C c" (at level 10, c at level 8).
Reserved Notation "\X" (at level 0).

Reserved Notation "\poly_ ( i < n ) E"
  (at level 36, E at level 36, i, n at level 50,
   format "\poly_ ( i  <  n )  E").

Notation Local simp := Monoid.Equations.simpm.

Section Polynomial.

Variable R : Ring.basic.

(* Define a polynomial as a sequence *)

(* A coef sequence is normal if its last element is <> 0 *)
Definition normal (s : seq R) := last 1 s != 0.

Record polynomial : Type :=
  Poly {seq_of_poly :> seq R; _ : normal seq_of_poly}.

Notation poly := polynomial.

Bind Scope ring_scope with polynomial.

Canonical Structure poly_subType := SubType seq_of_poly polynomial_rect vrefl.
Canonical Structure poly_eqType := [subEqType for seq_of_poly].

Lemma seq_of_poly_inj : injective seq_of_poly. Proof. exact: val_inj. Qed.

Lemma normal_seq0 : normal [::].
Proof. by apply/eqP; case: R. Qed.

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
Proof. by rewrite /poly1 seq_polyC (negbET normal_seq0). Qed.

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


Definition simpl01 := (mul0r,mulr0,mul1r,mulr1,add0r,addr0,oppr0).

Lemma coef_opp : forall p i, coef (- p) i = - coef p i.
Proof. by move=> p i; rewrite coef_mul_C_poly mulN1r. Qed.

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
Proof. by rewrite {1}/eqd /= seq_poly0; case/seq_of_poly. Qed.

Lemma size_polyC : forall c, c != 0 -> size (polyC c) = 1%N.
Proof. by move=> c c_nz; rewrite seq_polyC (negbET c_nz). Qed.

Lemma size_horner : forall p c, p != 0 -> size (horner c p) = (size p).+1.
Proof. by move=> p c; rewrite size_poly0_eq seq_horner; case (p : seq R). Qed.

Lemma coef_default : forall (p : poly) i, size p <= i -> coef p i = 0.
Proof. move=> *; exact: sub_default. Qed.

Lemma leq_size_coef: forall (p: poly) i,
  (forall j, i <= j -> coef p j = 0) -> size p <= i.
Proof.
move=> p i H; case: leqP => Cspi //.
move: (lead_coef_nz p); rewrite /lead_coef -(sub_last 0).
case: size Cspi => [| s] //= Cspi.
by move: (H _ Cspi); rewrite /coef => ->; case/negP.
Qed.

Lemma leq_coef_size: forall (p: poly) i, coef p i <> 0 -> i < size p.
Proof.
by move=> p i H; case: leqP => Cspi //; case H; rewrite coef_default.
Qed.

Lemma size_add: forall p q: poly, size (p + q) <= maxn (size p) (size q).
Proof.
move=> p q; apply: leq_size_coef => j; rewrite  leq_maxl; case/andP=> Cpj Cqj.
by rewrite coef_add_poly !coef_default // !simpl01.
Qed.

Lemma size_mul: forall p q: poly, p != 0 -> size (p * q) < size p + size q.
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

Lemma size1P: forall p, reflect (exists c, p = \C c) (size p <= 1).
Proof.
move=> p; apply: (iffP eqP); last first.
  by case=> c ->; rewrite  val_insubd; case: normal.
move=> HH; exists (coef p 0).
apply/coef_eqP=> [[|i]]; rewrite coef_polyC // coef_default //.
by case: size HH => // [[|n]].
Qed.

Lemma lead_coefE: forall p: poly, lead_coef p = if p == 0 then 1 else coef p (size p).-1.
Proof.
move=> p; rewrite /lead_coef /coef -(sub_last 0).
by case: size (size_poly0_eq p) => [| s] ->.
Qed.

(* monomial *)

Definition polyXn n := mkPoly (addsn n (0: R) [::1]).

Notation "\X^ n" := (polyXn n) (at level 1).

Lemma polyXn0 : \X^ 0 = 1.
Proof. by rewrite  /polyXn /= horner_def !simpl01. Qed.

Lemma polyXn1 : \X^ 1 = \X.
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
  coef (\X^ n * p) i = if i < n then 0 else coef p (i - n).
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

Lemma polyXnXm : forall n m,  \X^ n * \X^m = \X^ (n+m).
Proof.
move=> n m; apply/coef_eqP=> i.
rewrite coef_mul_Xn_poly !coef_polyXn.
case: ltnP => Cin.
  by rewrite eqn_leq [_ + _ <= _]leqNgt (leq_trans Cin (leq_addr _ _)) andbF.
(do 2 case: eqP) => //; first by move=> NEi Ei; case NEi; rewrite -Ei subnK.
by move=> Ei NEi; case NEi; rewrite Ei addKn.
Qed.

Lemma polyXnC : forall n p,  \X^ n * p = p * \X^n.
Proof.
move=> n m; apply/coef_eqP=> i.
by rewrite coef_mul_Xn_poly coef_mul_poly_Xn.
Qed.

Lemma size_polyXn : forall n, size (\X^ n) = n.+1.
Proof. by move=> n; rewrite seq_polyXn size_addsn addnC. Qed.


Lemma polyC_mul: forall c1 c2, \C (c1 * c2) = \C c1 * \C c2.
Proof.
move=> c1 c2; 
apply/val_eqP; apply/eqP; rewrite /polyC {2}/mul /= /mul_poly /= !val_insubd /normal /=.
(do 3 (case: (@eqP R))) => Hc1 Hc2; rewrite ?(seq_horner, seq_poly0) //=; 
    try (by rewrite (Hc1, Hc2) (mul0r, mulr0); case).
- by move=> ->; rewrite /= add0r seq_poly0.
by rewrite addr0 /polyC val_insubd /normal; move/eqP->.
Qed.

Lemma opp_polyC: forall c: R, - \C c = \C -c.
Proof. by move=> c; rewrite -mulN1r polyC_mul. Qed.

(* Monic *)

Definition monic p := lead_coef p == 1.

Lemma monic1: monic 1.
Proof. by rewrite /monic /lead_coef seq_poly1. Qed.

Lemma monicX: monic \X.
Proof. by rewrite /monic /lead_coef seq_polyX. Qed.

Lemma monicXn: forall n, monic \X^n.
Proof.
by move=> n; rewrite /monic /lead_coef !seq_polyXn; elim: n {1}1 =>/=.
Qed.

Lemma lead_coef_mul: forall p q,
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
rewrite -ltnS (@ltn_predK 0) ?size_mul //.
rewrite -(@ltn_predK 0 (_.-1)).
apply: leq_coef_size; first by rewrite (eqP Cpq); exact: nonzero1r.
by move: Cp1 Cq1; (do 2 (case: size => //)) => *; rewrite addnS.
Qed.

(* Integral domain (we may need to introduce integral ring as an object) *)

Definition idomain := forall r1 r2: R, r1 * r2 = 0 -> r1 = 0 \/ r2 = 0.

Hypothesis idR : idomain.
Lemma iter_mul_id: forall m (r1 r2: R), r1 != 0 -> r2 != 0 -> iter m (mul r1) r2 != 0.
Proof.
by move=> m r1 r2 Dr1 Dr2; elim: m => [| m Hrec] //=;
   apply/eqP; case/idR=> Dr; [case/eqP: Dr1 | case/eqP: Hrec].
Qed.

Lemma size_mul_id: forall p q: poly, 
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
case: eqP Dp Dq (lead_coefE p) (lead_coefE q) (lead_coef_nz p) (lead_coef_nz q);
  case: eqP => // _ _ _ _ -> -> Cp Cq.
by case/idR=> Cpq; [case/negP: Cp | case/negP: Cq]; apply/eqP.
Qed.

Lemma lead_coef_mul_id: forall p q: poly, 
  p != 0 -> q != 0 -> lead_coef (p * q) = lead_coef p * lead_coef q.
Proof.
move=> p q; rewrite !lead_coefE; 
    (do 3 (case: eqP)) => // E1 E2 E3 _ _; last first.
  by rewrite size_mul_id // ?lead_coef_mul //; apply/eqP.
move: (lead_coef_mul p q); rewrite E1 coef0.
move/eqP; rewrite eq_sym; move/eqP; case/idR => Hd.
  move: (lead_coef_nz p); rewrite (lead_coefE p) Hd.
  by move/eqP: E3; case: eqP => // _ _; case/negP.
move: (lead_coef_nz q); rewrite (lead_coefE q) Hd.
by move/eqP: E2; case: eqP => // _ _; case/negP.
Qed.


(* Pseudo division *)
Definition edivp_rec (q: poly)  :=
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
  rewrite mulr_addl -!addrA; congr add.
  by rewrite addrC -addrA addrC -!addrA addKr.
move=> Mq HH; apply: Hrec => //.
move:  Mq; rewrite /monic; move/eqP->; rewrite !simpl01.
rewrite HH mulr_addl -!addrA; congr add.
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
have: 0 < size q.
  case: q Hq; case => // i; case/negP; apply/eqP => /=.
  by apply/val_eqP; rewrite /zero /= seq_poly0.
case: size => [| n1] //= _ Cnn1.
by rewrite subKn // ltnNge subSS leq_subr addrN.
Qed.

Lemma edivp_scal_spec: forall q n c (qq r: poly),
  exists m, (edivp_rec q n c qq r).1.1 = iter m (mul (lead_coef q)) c.
Proof.
move=> q; elim=> [| n Hrec] c qq r /=; case: (_ <= _); try by exists 0%N.
  by exists (1%N).
set c1 := _ * c; set qq1 := _ + _; set r1 := _ - _.
case (Hrec c1 qq1 r1) => m ->; exists m.+1.
by elim: m => [|m] //= ->.
Qed.


Definition edivp (p q: poly): R * poly * poly :=
  if q == 0 then (1,0,p) else
  let cq := lead_coef q in
  let sq := size q in
  edivp_rec q (size p) 1 0 p.

Definition divp p q := ((edivp p q).1).2.
Definition modp p q := (edivp p q).2.
Definition scalp p q := ((edivp p q).1).1.

Lemma divp_mon_spec: forall p q, monic q -> p = divp p q * q + modp p q.
Proof.
move=> p q Mq.
rewrite /divp /modp /scalp /edivp.
case: eqP => [->| Hq]; first by rewrite !simpl01.
by apply: edivp_mon_spec; rewrite // !simpl01.
Qed.

Lemma modp_spec: forall p q, q != 0 -> size (modp p q) < size q.
Proof.
move=> p q Hq.
rewrite /divp /modp /scalp /edivp.
case: eqP => He; first by case/negP: Hq; apply/eqP.
by apply: edivp_mod_spec.
Qed.

Lemma scalp_spec: forall p q,
  exists m, scalp p q = iter m (mul (lead_coef q)) 1.
Proof.
move=> p q; rewrite /divp /modp /scalp /edivp.
case: eqP => He; first by exists 0%N.
apply: edivp_scal_spec.
Qed.

Lemma scalp_id: forall p q, scalp p q != 0.
Proof.
move=> p q; case (scalp_spec p q) => m ->.
apply: iter_mul_id; [apply: lead_coef_nz | apply/eqP; exact: nonzero1r].
Qed.

End Polynomial.

Bind Scope ring_scope with polynomial.
Notation "\poly_ ( i < n ) E" := (mkPoly (mkseq (fun i : nat => E) n))
   : ring_scope.
Notation "\C c" := (polyC c) : ring_scope.
Notation "\X" := (polyX _) : ring_scope.
Notation "\X^ n" := (polyXn _ n) (at level 1): ring_scope.

Section PolynomialComRing.

Variable R : Ring.commutative_.

Lemma poly_mulC : forall p1 p2 : polynomial R, p1 * p2 = p2 * p1.
Proof.
move=> p1 p2; apply/coef_eqP=> i; rewrite coef_mul_poly coef_mul_poly_rev.
by apply: eq_bigr => j _; rewrite mulrC.
Qed.

Canonical Structure poly_commutative_ring := Ring.Commutative poly_mulC.


(* Pseudo-division in a commutative setting *)

Notation poly := (polynomial R).

Lemma edivp_spec: forall (p q: poly) n c qq r,
 let d := edivp_rec q n c qq r in
 \C c * p = qq * q + r -> \C (d.1).1 * p = (d.1).2 * q + d.2.
Proof.
move=> p q; elim=> [| n Hrec] c qq r /=; case: ltnP => Hp //=.
  rewrite polyC_mul -mulrA => ->.
  rewrite mulr_addl mulr_addr !mulrA -!addrA !(mulrC (\C _)).
  by congr add => //; rewrite addrC -addrA addrC -addrA addKr.
move=> HH; apply: Hrec.
rewrite polyC_mul -mulrA HH.
rewrite mulr_addl mulr_addr !mulrA -!addrA !(mulrC (\C _)).
by congr add => //; rewrite addrC -addrA addrC -addrA addKr.
Qed.

Lemma divp_spec: forall p q: poly, \C (scalp p q) * p = divp p q * q + modp p q.
Proof.
move=> p q.
rewrite /divp /modp /scalp /edivp.
case: eqP => [->| Hq]; first by rewrite !simpl01.
by apply: edivp_spec; rewrite !simpl01.
Qed.

End PolynomialComRing.

Section EvalPolynomial.

Variable R : Ring.basic.

Fixpoint eval_poly_seq (s : seq R) (x : R) {struct s} : R :=
  if s is a :: s' then eval_poly_seq s' x * x + a else 0.

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
elim: {p}(p : seq R) => /= [|a s ->]; first by rewrite big_pred0 => [|[]].
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

Lemma eval_poly_add : forall p q x, (p + q).[x] = p.[x] + q.[x].
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

Lemma eval_poly_mul : forall p q x,
  com_poly q x -> (p * q).[x] = p.[x] * q.[x].
Proof.
move=> p q x com_qx; rewrite eval_mkPoly {1}/eval_poly.
elim: {p}(p : seq R) => /= [|a s IHs]; first by rewrite simp.
rewrite eval_add_poly_seq /= {}IHs simp addrC mulr_addl /eval_poly.
congr (_ + _); first by rewrite -!mulrA com_qx.
elim: {s q com_qx}(q : seq R) => /= [|b s ->]; first by rewrite simp.
by rewrite -mulrA -mulr_addr.
Qed.

Lemma eval_poly_Cmul : forall c p x, (\C c * p).[x] = c * p.[x].
Proof.
move=> c p x; rewrite eval_mkPoly seq_polyC /eval_poly.
case: eqP => [->|_] /=; rewrite ?eval_add_poly_seq /= !simp //.
by elim: (p : seq R) => /= [|a s ->]; rewrite ?simp // mulr_addr mulrA.
Qed.

Lemma eval_poly_opp : forall p x, (- p).[x] = - p.[x].
Proof. by move=> p x; rewrite eval_poly_Cmul mulN1r. Qed.

Definition eval_poly_lin :=
  (eval_poly_add, eval_poly_opp, eval_polyX, eval_polyC, eval_horner,
   simp, eval_poly_Cmul, (fun p x => eval_poly_mul p (com_polyX x))).

Lemma factor0 : forall a, (\X - \C a).[a] = 0.
Proof. by move=> a; rewrite !eval_poly_lin addrN. Qed.

Lemma coef_factor : forall (a : R) i,
  coef (\X - \C a) i = match i with 0%N => - a | 1%N => 1 | _ => 0 end.
Proof.
move=> a i; rewrite coef_add_poly coef_polyX coef_opp coef_polyC.
by case: i => [|[|i]]; rewrite !(oppr0, simp).
Qed.

Lemma seq_polyXc: forall c: R, \X + \C c = [::c;1] :> seq R.
Proof.
move=> c; rewrite /add /= /add_poly seq_polyX seq_polyC /=.
 by case: eqP => [->| _]; rewrite ?simpl01 !seq_horner !seq_polyC !eqxx ?simpl01;
    case: eqP => // HH; case (@nonzero1r R).
Qed.

Theorem factor_theorem : forall p c,
  reflect (exists q, p = q * (\X - \C c)) (p.[c] == 0).
Proof.
move=> p c; apply: (iffP eqP) => [root_p_c | [q -> {p}]]; last first.
  by rewrite eval_poly_mul /com_poly factor0 ?simp.
rewrite opp_polyC; exists (divp p (\X + \C -c)).
have MXc: monic (\X + \C (-c)) by rewrite /monic /lead_coef seq_polyXc.
move: (divp_mon_spec p MXc) root_p_c => HH; rewrite {1 2}HH.
have Dxc: \X + \C (- c) != 0.
  by apply/negP; move/eqP;move/val_eqP; rewrite /= seq_polyXc seq_poly0.
have:=  modp_spec p Dxc.
rewrite seq_polyXc /= ltnS; case/size1P => c1 ->.
pose f := (eval_poly_add,eval_poly_mul,eval_polyX, eval_polyC, addrN, simpl01).
by rewrite !f => [->|]; rewrite /com_poly ?f.
Qed.

End EvalPolynomial.

Notation "p .[ x ]" := (eval_poly p x) : ring_scope.

Unset Implicit Arguments.
