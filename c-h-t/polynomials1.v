Add LoadPath "../".
Require Import ssreflect ssrbool funs eqtype ssrnat seq fintype tuple
 indexed_products div groups determinantET (*polynomials*) rings.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope rings_scope.

Section Polynomial.
Variable R : ringsType.

(* define a polynomial as a sequence *)

Section PolynomialCoef.

Notation "'poly_coef'" := (seq R).

(* definition of the equality of polynomial *)

Definition eq_p0 (p : poly_coef) : bool :=
  all (set1 0) p.

Fixpoint eq_p (p q : poly_coef) {struct p}: bool :=
  if p is (Adds a p') then
    if q is (Adds b q') then (a == b) && (eq_p p' q') 
   else eq_p0 p 
  else eq_p0 q.

Notation "x1 '==' x2" := (eq_p x1 x2) (at level 70) : local_scope.
Notation "00" := (@Seq0 _: poly_coef) (at level 0): local_scope.

Lemma eq_p0_eq_p: forall p, eq_p0 p = (p == 00).
Proof. elim => //= [a p Hrec H]. Qed.

Lemma eq_p_refl: forall p, p == p.
Proof.
by elim => [|a p Hrec] //=; rewrite eq_refl.
Qed.

Lemma eq_p_sym: forall p q, p == q -> q == p.
Proof.
elim => [|a p Hrec] // [|b q] //=.
by case/andP => H1 H2; rewrite eq_sym H1 Hrec.
Qed.

Lemma eq_p0_trans: forall p q, eq_p0 p -> p == q -> eq_p0 q.
Proof.
elim => [|a p Hrec] // [|b q] //=.
case/andP => H1 H2; case/andP => H3 H4.
by rewrite -(eqP H3) H1 Hrec.
Qed.

Lemma eq_p_trans: forall p q r, p == q -> q == r -> p == r.
Proof.
elim => [|a p Hrec] //=; first exact: eq_p0_trans.
move => [|b q] // [|c r] //=; case/andP => H1 H2; 
                              case/andP => H3 H4.
  by rewrite -(eqP H1) H3 (Hrec 00) // -eq_p0_eq_p.
 -by rewrite (eqP H1) H3 (eq_p0_trans H4) // eq_p_sym.
by rewrite (eqP H1) H3 (Hrec _ _ H2).
Qed.

Lemma eq_p0_subP : forall p, reflect (sub 0 p =1 sub 0 seq0) (eq_p0 p).
Proof.
elim=> //=[|x s Hp]; apply: (iffP idP) => //=.
  move=> Heq [|i] //=; elim (andP Heq) => //; move/eqP => // _; move/Hp => // H1.
  by move: (H1 i) => ->; rewrite sub_seq0.
move=> H1; move: (H1 0%N) => //= ->; rewrite eq_refl andTb.
apply/Hp=> i; move: (H1 (S i)) => //=.
by rewrite sub_seq0.
Qed.

Lemma eq_p_subP : forall p q, reflect (sub 0 p =1 sub 0 q) (p == q).
Proof.
move=> p q.
elim: q p => // [p| b q Hq]; 
  first (rewrite -eq_p0_eq_p; apply: eq_p0_subP).
case=>//=[|a p ].
  move: (eq_p0_subP (Adds b q)) => //= H1.
  apply: (@iffP (sub 0 (Adds b q) =1 sub 0 seq0) _ _) => //; apply: fsym.
apply: (iffP idP) => H1.
move=> [|i] //=; 
 [elim: (andP H1); move/eqP => //=|
  move: i; apply/Hq; elim: (andP H1) => //].
move: (H1 0%N)=> /= ->; rewrite eq_refl andTb.
apply/Hq => i; apply: (H1 (S i)).
Qed.

(* --- *)

(* normal polynomial *)

(* A polynomial is normal if its last element is <> 0 *)
Definition normal (p : poly_coef) := last 1 p != 0.

Fixpoint norm3 (p q r : poly_coef) {struct p} : poly_coef :=
  if p is (Adds a p') then
    if (a == 0)%EQ then norm3 p' q (Adds a r) 
              else norm3 p' (Adds a r) (Adds a r)
  else rev q.

(* Normalizer *)
Definition norm p := norm3 p (Seq0 _) (Seq0 _).

(* 00 is normal *)
Lemma normal0: normal 00.
Proof.
by rewrite /normal /=; apply/negP => H1; case (@one_diff_0 R); apply/eqP.
Qed.

Lemma normal_behead: forall a p, normal (Adds a p) -> normal p.
Proof.
move => a [|b p] // _; exact: normal0.
Qed.

(* Equality on normal polynomials is structural *)
Lemma normal_eq:
  forall p q, normal p -> normal q -> p == q -> p = q.
Proof.
have F1: forall p, eq_p0 p -> last 0 p = 0.
  elim => [|a p] //= H; first by case/andP; move/eqP => <-.
elim => [|a p Hrec].
  elim => [|b q Hrec] //=.
  move => _ H; case/andP; move/eqP => H1 H2.
  by case/negP: H; rewrite -H1 /=; apply/eqP; apply F1.
case => [|b q H1 H2] //=.
  move => H _; case/andP; move/eqP => H1 H2.
  by case/negP: H; rewrite -H1 /=; apply/eqP; apply F1.
case/andP; move/eqP => -> H3.
by rewrite (Hrec q)  ?(normal_behead H1) ?(normal_behead H2).
Qed.

Lemma norm3_eq:
  forall p q r, (rev q) == (rev r) -> norm3 p q r == cat (rev r) p.
Proof.
elim => [|a p Hrec] q r H1 //=; first by rewrite cats0.
case E1: (a == 0)%EQ.
  rewrite (eq_p_trans (Hrec q (Adds a r) _)) //=.
    rewrite rev_adds {H1}(eq_p_trans H1) //.
    elim: (rev r) => [|b r1 Hrec1] //=.
      by rewrite eq_sym E1.
    by rewrite Hrec1 eq_refl.
  by rewrite rev_adds cat_add_last eq_p_refl.
rewrite (eq_p_trans (Hrec (Adds a r) (Adds a r) _)) //=.
  by rewrite eq_p_refl.
by rewrite rev_adds cat_add_last eq_p_refl.
Qed.

(* Normalizing returns an equal polynomial *)
Lemma norm_eq: forall p, norm p == p.
Proof.
by move => p; rewrite /norm (eq_p_trans (norm3_eq _ _)) //= eq_p_refl.
Qed.

Lemma norm3_normal: forall p q r, normal (rev q) -> normal (norm3 p q r).
Proof.
elim => [|a p Hrec] q r H1 //=.
by case E1: (a == 0)%EQ; rewrite Hrec // /normal rev_adds last_add_last E1.
Qed.

(* Normalizing normalises *)
Lemma norm_normal: forall p, normal (norm p).
Proof.
by move => p; rewrite /norm norm3_normal //; exact: normal0.
Qed.

Lemma normal_norm_eq : forall p, normal p -> norm p = p.
Proof.
move=> p Hp; apply: normal_eq=> //; last (by apply: norm_eq).
apply: norm_normal.
Qed.

(* --- *)

End PolynomialCoef.

(* Definition of the sigma type of normal polynomial *)

CoInductive polynomial : Type := Poly p of normal p.

Definition poly0 := locked Poly seq0 normal0.

Definition const_poly c :=
  if insub normal (Seq c) is Some (EqSig p np) then locked Poly p np
  else poly0.

Definition horner p c : polynomial :=
  if p is Poly (Adds _ _ as sp) norm_p then locked Poly (Adds c sp) norm_p
  else const_poly c.

Definition coef p :=
  let: Poly sp _ := p in sub 0 sp.

Lemma coef0 : forall i, coef poly0 i = 0.
Proof. by unlock poly0; case. Qed.

Lemma coef_const_0 : forall c, coef (const_poly c) 0 = c.
Proof.
unlock const_poly => c /=; case: insubP => [[_ _] _ /= -> //|].
by rewrite negbK coef0; move/eqP.
Qed.

Lemma coef_const_S : forall c i, coef (const_poly c) i`+1 = 0.
Proof.
by unlock const_poly poly0 => c [|i] /=; case: insubP => [[_ _] _ /= ->|].
Qed.

Lemma coef_horner_0 : forall p c, coef (horner p c) 0 = c.
Proof.
unlock horner => [] [[|_ _] _] c //=; exact: coef_const_0.
Qed.

Lemma coef_horner_S : forall p c i, coef (horner p c) i`+1 = coef p i.
Proof.
unlock horner => [] [[|_ _] _] c [|i] //=; exact: coef_const_S.
Qed.

Lemma coef_norm : forall p , coef (Poly (norm_normal p)) =1 sub 0 p.
Proof. move=> p //=; apply/eq_p_subP; apply: norm_eq. Qed.

Lemma coef_eqP : forall p q, coef p =1 coef q <-> p = q.
Proof.
move=> [p np] [q nq]; split=> [/= eq_pq | -> //].
suffices eq_pq': p = q.
  by rewrite eq_pq' in np *; rewrite (bool_irrelevance np nq).
suffices: size p = size q by move/eq_from_sub; eauto.
without loss lt_pq: p q np nq eq_pq / size p < size q.
  case: (ltnP (size p) (size q)); auto.
  rewrite leq_eqVlt; case/orP; first by move/eqP.
  move=> ? wlog; symmetry; exact: wlog.
case/eqP: nq {np}; rewrite -(sub_last 0) -(leq_add_sub lt_pq) /= addnI.
by rewrite -eq_pq sub_default // leq_addr.
Qed.

Lemma poly_rect P :
  P poly0 -> (forall p c, P p -> P (horner p c)) -> forall p, P p.
Proof.
unlock poly0 horner => P P_0 P_H [].
elim=> [|c [|c' p] /= IHp] np; last exact: P_H (IHp np).
  by rewrite (bool_irrelevance np normal0).
have:= P_H _ c P_0; unlock const_poly.
case: insubP np => [[q nq] _ /= <- np|]; last by move/negP.
by rewrite (bool_irrelevance np nq).
Qed.

Definition poly_ind (P : polynomial -> Prop) := @poly_rect P.
Definition poly_rec (P : polynomial -> Set) := @poly_rect P.

Fixpoint add_poly_rec (p q : seq R) {struct p} : 
  normal p -> normal q -> polynomial := 
  if p is (Adds a p') return normal p -> normal q -> polynomial then 
    if q is (Adds b q') return (normal (Adds a p')) -> normal q -> polynomial then
      fun np nq => 
      horner (add_poly_rec (normal_behead np) (normal_behead nq)) (a + b)
    else fun np _ => Poly np
  else fun _ nq => Poly nq.

Definition add_poly p1 p2 :=
  let: Poly _ np1 := p1 in
  let: Poly _ np2 := p2 in
  (add_poly_rec np1 np2).

Lemma coef_add_poly p1 p2 i : 
  coef (add_poly p1 p2) i = coef p1 i + coef p2 i.
Proof.
move=> [p1 np1] [p2 np2].
elim: p1 np1 p2 np2 => [|c1 p1 IHp] np1 [|c2 p2] np2 [|i] //=;
  rewrite (plus0r, plus0l, coef_horner_0, coef_horner_S) // IHp //=.
Qed.

Lemma poly_add0P p : add_poly poly0 p = p.
Proof.
by move=> p; apply/coef_eqP=> i; rewrite coef_add_poly coef0 plus0l.
Qed.  

Lemma poly_addC p1 p2 : add_poly p1 p2 = add_poly p2 p1.
Proof.
by move=> p1 p2; apply/coef_eqP=> i; rewrite !coef_add_poly plusC.
Qed.

Lemma poly_addA p1 p2 p3 :
  add_poly p1 (add_poly p2 p3) = add_poly (add_poly p1 p2) p3.
Proof.
by move=> p1 p2 p3; apply/coef_eqP=> i; rewrite !coef_add_poly plusA.
Qed.

Fixpoint mult_cst_poly_l c p : normal p -> polynomial :=
  if p is Adds a p' return normal p -> polynomial then 
    fun np => horner (mult_cst_poly_l c (normal_behead np)) (c * a)
  else fun _ => poly0.

Lemma coef_mult_cst_poly_l c p (np : normal p) i : 
  coef (mult_cst_poly_l c np) i = c * (sub 0 p i).
Proof.
move=> c p np.
elim: p np => [|a p IHp] np [|i] //=;
  rewrite (mult0r, mult0r, coef_horner_0, coef_horner_S) //; apply: coef0.
Qed. 

Fixpoint mult_cst_poly_r c p : normal p -> polynomial :=
  if p is Adds a p' return normal p -> polynomial then 
    fun np => horner (mult_cst_poly_r c (normal_behead np)) (a * c)
  else fun _ => poly0.

Lemma coef_mult_cst_poly_r c p (np : normal p) i : 
  coef (mult_cst_poly_r c np) i = (sub 0 p i) * c.
Proof.
move=> c p np.
elim: p np => [|a p IHp] np [|i] //=;
  rewrite (mult0l, mult0l, coef_horner_0, coef_horner_S) //; apply: coef0.
Qed.

Fixpoint mult_poly_rec (p q : seq R) {struct p} : 
  normal p -> normal q -> polynomial := 
  if p is (Adds a p') return normal p -> normal q -> polynomial then 
    if q is (Adds b q') return (normal (Adds a p')) -> normal q -> polynomial then
      fun np nq => horner 
       (add_poly (mult_cst_poly_l a (normal_behead nq))
        (add_poly (mult_cst_poly_r b (normal_behead np))
          (horner (mult_poly_rec (normal_behead np) (normal_behead nq)) 0)))
       (a * b)
    else fun _ _ => poly0
  else fun _ _ => poly0.

Definition mult_poly p1 p2 :=
  let: Poly _ np1 := p1 in
  let: Poly _ np2:= p2 in
  (mult_poly_rec np1 np2).

Lemma normal1 : normal (Seq 1).
Proof. apply/eqP; by case R. Qed.

Definition poly1 := locked Poly (Seq 1) normal1.

Lemma coef_poly1_0: coef poly1 0 = 1.
Proof. unlock poly1 => //. Qed.

Lemma coef_poly1_S: forall i, coef poly1 (S i) = 0.
Proof. by unlock poly1 => //= i; rewrite sub_seq0. Qed.

Lemma coef_mult_poly p1 p2 i :
  coef (mult_poly p1 p2) i = 
    iprod _ plus 0 I_(i`+1) (setA I_(i`+1)) 
      (fun k => (coef p1 (nat_of_ord k)) * coef p2 (i - (nat_of_ord k))).
Proof.
move=> [p1 np1] [p2 np2].
elim: p1 np1 p2 np2 => [|c1 p1 IHp] np1 [|c2 p2] np2 i //=;
  rewrite ?coef0.
- rewrite 
   -{1}(@iprod_1 R plus 0 (@plus0l R) I_(i`+1) (setA (ordinal_eqType (i`+1)))).
  apply: eq_iprod_f => x _ ; rewrite sub_seq0 mult0l //.
- rewrite 
   -{1}(@iprod_1 R plus 0 (@plus0l R) I_(i`+1) (setA (ordinal_eqType (i`+1)))).
  apply: eq_iprod_f => x _ ; rewrite sub_seq0 mult0l //.
- rewrite 
   -{1}(@iprod_1 R plus 0 (@plus0l R) I_(i`+1) (setA (ordinal_eqType (i`+1)))).
  apply: eq_iprod_f => x _ ; rewrite sub_seq0 mult0r //.
case: i => [|i]//.
  rewrite coef_horner_0 -(add0n 1).
  rewrite iprod_rec //=; 
    try (apply: plusC); try (apply: plus0l); try (apply: plusA).
  suffices : (setA (ordinal_eqType 0)) =1 set0; last by case=>//.
  by move=> H1; rewrite (eq_iprod_set R plus 0 I_(0) _ _ _ H1) 
    iprod0 plus0l.
rewrite coef_horner_S -(addn1).
rewrite iprod_rec //; 
  try (apply: plusC); try (apply: plus0l); try (apply: plusA).
rewrite //= subnn //=.
rewrite !coef_add_poly coef_mult_cst_poly_r coef_mult_cst_poly_l.
case: i => [|i] //.
  rewrite coef_horner_0 -(add0n 1) plus0r.
  rewrite iprod_rec //; 
    try (apply: plusC); try (apply: plus0l); try (apply: plusA).
  suffices : (setA (ordinal_eqType 0)) =1 set0; last by case=>//.
  move=> H1; rewrite (eq_iprod_set R plus 0 I_(0) _ _ _ H1) 
    iprod0 !plus0l //.
rewrite plusC -plusA plusC ; congr plus.
rewrite -[(i`+1)`+1](addn1) iprod_rec_inv //; 
    try (apply: plusC); try (apply: plus0l); try (apply: plusA).
rewrite coef_horner_S plusC //; congr plus.
  congr mult => //.
  rewrite {1}addn1 //.
rewrite IHp.
apply: eq_iprod_f => x Hx //=.
congr mult => //=.
  suffices : S (nat_of_ord x) = nat_of_ord (inj_ord (i`+1 + 1) 1 (inj_ord_add i`+1 1 x)).
    move => <- //=.
  by clear Hx; case: x => //= [x Hx]; rewrite addn1.
suffices : S (i - nat_of_ord x) = (i`+1 + 1 - inj_ord (i`+1 + 1) 1 (inj_ord_add i`+1 1 x)).
  move => <- //=.
clear Hx; case: x => //= [x Hx]. rewrite !addn1 subSS //=.
rewrite leq_subS //.
Qed.


Lemma normalX : normal (Seq 0 1).
Proof. apply/eqP; by case R. Qed.

Definition polyX := locked Poly (Seq 0 1) normalX.

Lemma poly_mult1P : forall p, mult_poly poly1 p = p.
Proof.
move=> p; apply/coef_eqP=> i.
rewrite coef_mult_poly //=.
rewrite -addn1 iprod_rec_inv //; 
    try (apply: plusC); try (apply: plus0l); try (apply: plusA).
rewrite //= coef_poly1_0 mult1l subn0 -{2}(plus0r (coef p i)).
congr plus.


 