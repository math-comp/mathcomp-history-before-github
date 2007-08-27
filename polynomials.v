Require Import ssreflect ssrbool funs eqtype ssrnat seq fintype tuple
 indexed_products div groups algebraic_struct ring.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.
Delimit Scope local_scope with loc.
Open Scope local_scope.

Section Polynomial.
Variable R : ring.

Notation "'\sum_' ( 'in' r ) F" := (@iprod R _ r F)
  (at level 40, F at level 40,
  format "'\sum_' ( 'in'  r )  F") : local_scope.
Notation "'\prod_' ( 'in' r ) F" := (@iprod (r2m R) _ r F)
  (at level 35, F at level 35,
  format "'\prod_' ( 'in'  r )  F") : local_scope.

Notation "'\sum_' () F" := (@iprod R _ (setA _) F)
  (at level 40, F at level 40, format "'\sum_' ()  F") : local_scope.
Notation "'\prod_' () F" := (@iprod (r2m R) _ (setA _) F)
  (at level 35, F at level 35, format "'\prod_' () F") : local_scope.

Notation "'\sum_' ( i 'in' r ) E" := (@iprod R _ r (fun i => E))
  (at level 40, E at level 40, i at level 50,
  format "'\sum_' ( i  'in'  r )  E") : local_scope.
Notation "'\prod_' ( i 'in' r ) E" := (@iprod (r2m R) _ r (fun i => E))
  (at level 35, E at level 35, i at level 50,
  format "'\prod_' ( i  'in'  r )  E") : local_scope.

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
  move=> Heq [|i] //=; elim (andP Heq) => //; move/eqP => // _;
  by  move/Hp => // H1; move: (H1 i) => ->; rewrite sub_seq0.
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
by case E1: (a == 0)%EQ;
  rewrite Hrec // /normal rev_adds last_add_last E1.
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

Definition coef p :=
  let: Poly sp _ := p in sub 0 sp.

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

(* Polynomial eqType *)

Lemma eq_pP : reflect_eq (fun (p1 p2 : polynomial) => 
      let: Poly p1 _ := p1 in let: Poly p2 _ := p2 in (eq_p p1 p2)).
Proof.
move=> [[|a1 p1] np1] [[|a2 p2] np2] ; apply: (iffP idP) => //=.
 - by move=> _ ; rewrite /= (bool_irrelevance np1 np2).
 - move=> H1; move: np2; rewrite / normal //= => H2.
   suffices: (last a2 p2) != 0 => //=.
   suffices: (last a2 p2) = 0 => //=; 
     first (move=> ->; move/eqP=>//=).
   elim: (andP H1) =>  //=; move/eqP=><-.
   rewrite / eq_p0 //= ; elim: p2 {H1 H2} => //= [x s Hs] H1.
   by elim: (andP H1); move/eqP=> <-; exact Hs.
 - move=> H1; move: np1; rewrite / normal //= => H2.
   suffices: (last a1 p1) != 0 => //=.
   suffices: (last a1 p1) = 0 => //=; 
     first (move=> ->; move/eqP=>//=).
   elim: (andP H1) =>  //=; move/eqP=><-.
   rewrite / eq_p0 //= ; elim: p1 {H1 H2} => //= [x s Hs] H1.
   by elim: (andP H1); move/eqP=> <-; exact Hs.
 - move=> H1; elim: (andP H1); move/eqP=> {H1} H1 H2.
   move/eq_p_subP: H2 => H2.
   by apply/coef_eqP => //=; move=> [|i] //=.
move/coef_eqP=> //= H1; apply/andP.
split; first (apply/eqP; apply: (H1 0%N)).
apply/eq_p_subP=>i; apply: (H1 (S i)).
Qed.

Canonical Structure polynomial_eqType := EqType eq_pP.

Section PolynomialRing.

Definition poly0 := locked Poly seq0 normal0.

Definition const_poly c :=
  if insub normal (Seq c) is Some (EqSig p np) then locked Poly p np
  else poly0.

Definition horner p c : polynomial :=
  if p is Poly (Adds _ _ as sp) norm_p then
    locked Poly (Adds c sp) norm_p
  else const_poly c.


Lemma coef0 : forall i, coef poly0 i = 0.
Proof. by unlock poly0; case. Qed.

Lemma coef_const_0 : forall c, coef (const_poly c) 0 = c.
Proof.
unlock const_poly => c /=; case: insubP => [[_ _] _ /= -> //|].
by rewrite negbK coef0; move/eqP.
Qed.

Lemma coef_const_S : forall c i, coef (const_poly c) i.+1 = 0.
Proof.
by unlock const_poly poly0 => c [|i] /=; case: insubP => [[_ _] _ /= ->|].
Qed.

Lemma coef_horner_0 : forall p c, coef (horner p c) 0 = c.
Proof.
unlock horner => [] [[|_ _] _] c //=; exact: coef_const_0.
Qed.

Lemma coef_horner_S : forall p c i, coef (horner p c) i.+1 = coef p i.
Proof.
unlock horner => [] [[|_ _] _] c [|i] //=; exact: coef_const_S.
Qed.

Lemma coef_norm : forall p , coef (Poly (norm_normal p)) =1 sub 0 p.
Proof. move=> p //=; apply/eq_p_subP; apply: norm_eq. Qed.

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
    if q is (Adds b q')
      return (normal (Adds a p')) -> normal q -> polynomial then
      fun np nq => 
        horner (add_poly_rec (normal_behead np) (normal_behead nq))
               (a + b)
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
  rewrite (plus_r0r, plus_r0l, coef_horner_0, coef_horner_S) // IHp //=.
Qed.

Lemma poly_add0P p : add_poly poly0 p = p.
Proof.
by move=> p; apply/coef_eqP=> i; rewrite coef_add_poly coef0 plus_r0l.
Qed.  

Lemma poly_addC p1 p2 : add_poly p1 p2 = add_poly p2 p1.
Proof.
by move=> p1 p2; apply/coef_eqP=> i; rewrite !coef_add_poly plus_rC.
Qed.

Lemma poly_addA p1 p2 p3 :
  add_poly p1 (add_poly p2 p3) = add_poly (add_poly p1 p2) p3.
Proof.
by move=> p1 p2 p3; apply/coef_eqP=> i; rewrite !coef_add_poly plus_rA.
Qed.

Fixpoint mult_cst_poly_l_rec c p : normal p -> polynomial :=
  if p is Adds a p' return normal p -> polynomial then 
    fun np => horner (mult_cst_poly_l_rec c (normal_behead np)) (c * a)
  else fun _ => poly0.

Lemma coef_mult_cst_poly_l_rec c p (np : normal p) i : 
  coef (mult_cst_poly_l_rec c np) i = c * (sub 0 p i).
Proof.
move=> c p np.
elim: p np => [|a p IHp] np [|i] //=;
  rewrite (mult_r0r, mult_r0r, coef_horner_0, coef_horner_S) // ?IHp //;
  apply: coef0.
Qed. 

Definition mult_cst_poly_l c p :=
  let: Poly _ np := p in
  (mult_cst_poly_l_rec c np).

Lemma coef_mult_cst_poly_l c p i : 
  coef (mult_cst_poly_l c p) i = c * (coef p i).
Proof. move=> c [p np]; by apply: coef_mult_cst_poly_l_rec. Qed. 

Fixpoint mult_cst_poly_r_rec  p c : normal p -> polynomial :=
  if p is Adds a p' return normal p -> polynomial then 
    fun np => horner (mult_cst_poly_r_rec c (normal_behead np)) (a * c)
  else fun _ => poly0.

Lemma coef_mult_cst_poly_r_rec c p (np : normal p) i : 
  coef (mult_cst_poly_r_rec c np) i = (sub 0 p i) * c.
Proof.
move=> c p np.
elim: p np => [|a p IHp] np [|i] //=;
  rewrite (mult_r0l, mult_r0l, coef_horner_0, coef_horner_S) // ?IHp //;
  apply: coef0.
Qed.

Definition mult_cst_poly_r p c :=
  let: Poly _ np := p in
  (mult_cst_poly_r_rec c np).

Lemma coef_mult_cst_poly_r c p i : 
  coef (mult_cst_poly_r p c) i = (coef p i) * c.
Proof. move=> c [p np]; by apply: coef_mult_cst_poly_r_rec. Qed.

Fixpoint mult_poly_rec (p q : seq R) {struct p} : 
  normal p -> normal q -> polynomial := 
  if p is (Adds a p') return normal p -> normal q -> polynomial then 
    if q is (Adds b q') 
      return (normal (Adds a p')) -> normal q -> polynomial then
      fun np nq => horner 
       (add_poly (mult_cst_poly_l_rec a (normal_behead nq))
                 (add_poly (mult_cst_poly_r_rec b (normal_behead np))
                           (horner (mult_poly_rec (normal_behead np)
                                   (normal_behead nq)) 0)))
       (a * b)
    else fun _ _ => poly0
  else fun _ _ => poly0.

Definition mult_poly p1 p2 :=
  let: Poly _ np1 := p1 in
  let: Poly _ np2:= p2 in
  (mult_poly_rec np1 np2).

Definition poly1 := const_poly 1.

(* Some useful constant *)

Definition polyX := locked horner poly1 0.
Definition polyX_a a := locked horner poly1 (-a).
(* --- *)

Lemma coef_poly1_0: coef poly1 0 = 1.
Proof. by rewrite coef_const_0. Qed.

Lemma coef_poly1_S: forall i, coef poly1 (S i) = 0.
Proof. by move=> i; rewrite coef_const_S. Qed.

Lemma coef_mult_poly p1 p2 i :
  coef (mult_poly p1 p2) i = 
  \sum_() (fun k :I_(i.+1) =>
              (coef p1 (nat_of_ord k)) * coef p2 (i - (nat_of_ord k))).
Proof.
move=> [p1 np1] [p2 np2].
elim: p1 np1 p2 np2 => [|c1 p1 IHp] np1 [|c2 p2] np2 i //=;
  rewrite ?coef0.
- symmetry; apply: isum0 => //= x Hx; rewrite sub_seq0 mult_r0l //.
- symmetry; apply: isum0 => //= x Hx; rewrite sub_seq0 mult_r0l //.
- symmetry; apply: isum0 => //= x Hx; rewrite sub_seq0 mult_r0r //.
case: i => [|i]//.
  pose x0:= Ordinal (ltnSn 0).  
  rewrite coef_horner_0 (@iprod_set1_ R I_(1) x0)// {}/x0.
  case=>//= i i0; rewrite / setA; symmetry.
  apply/eqP; case: i i0 =>//= i0; congr Ordinal.
  by apply: bool_irrelevance.
rewrite coef_horner_S (@iprod_ord_rec_r R) //. 
rewrite !coef_add_poly coef_mult_cst_poly_r_rec coef_mult_cst_poly_l_rec.
case: i => [|i] //.
  rewrite coef_horner_0 plus_r0r.
  pose x0:= Ordinal (ltnSn 0).  
  rewrite (@iprod_set1_ R I_(1) x0)// {}/x0.
  case=>//= i i0; rewrite / setA; symmetry.
  apply/eqP; case: i i0 =>//= i0; congr Ordinal.
  by apply: bool_irrelevance.
rewrite plus_rC -plus_rA plus_rC // ; congr (_ + _).
  rewrite (@iprod_ord_rec_l R) // coef_horner_S plus_rC //; congr (_ + _).
  rewrite IHp.
  apply: (@eq_iprod_f_ R) => x _ //=; congr (_ * _).
  rewrite subSS leq_subS //; last (case: x =>//).
by congr (_ * _) => //=; rewrite subnn.
Qed.

Lemma poly_mult1P : forall p, mult_poly poly1 p = p.
Proof.
move=> p; apply/coef_eqP=> i.
rewrite coef_mult_poly //=.
rewrite (@iprod_ord_rec_l R) //.
rewrite //= coef_poly1_0 mult_r1l subn0 -{2}(plus_r0r (coef p i)).
congr (_ + _); apply: (@iprod_f1_ R).
by move=> x _ //=; rewrite coef_poly1_S mult_r0l.
Qed.

Lemma poly_multP1 : forall p, mult_poly p poly1 = p.
Proof.
move=> p; apply/coef_eqP=> i.
rewrite coef_mult_poly //=.
rewrite (@iprod_ord_rec_r R) //.
rewrite //= subnn coef_poly1_0 mult_r1r -{2}(plus_r0l (coef p i)).
congr (_ + _); apply: (@iprod_f1_ R).
case=>//= x Hx _ //=; rewrite -ltn_0sub in Hx.
by case: (i-x) Hx =>//= n Hn; rewrite coef_poly1_S mult_r0r.
Qed.

Notation "'no' x" := (nat_of_ord x) (at level 0) : local_scope.

Lemma poly_multA p1 p2 p3 :
  mult_poly p1 (mult_poly p2 p3) = mult_poly (mult_poly p1 p2) p3.
Proof.
move=> p1 p2 p3; apply/coef_eqP=> n.
rewrite !coef_mult_poly.
have : forall (k: I_(n.+1)) p q,
  coef (mult_poly p q) k = 
    iprod (R:= R) (fun x : I_(n.+1) => x <= k)
      (fun i => (coef p i) * coef q (k - i)).
  move=>k p q.
  rewrite !coef_mult_poly.
  case: k => [k Hk] //=.
  have Ht : forall i, i <k.+1 -> i < n.+1.
    move=> i Hi; apply: (leq_trans Hi) => //=.
  set h : I_(k.+1) -> I_(n.+1) := 
    fun x => (let: Ordinal _ Hx := x in (Ordinal (Ht _ Hx))).
  set r:=(fun x : I_(n.+1) => (no x) <= k).
  have H1 : ibijective r h.
     rewrite / ibijective.
  set f' : I_(n.+1) -> I_(k.+1) := 
    fun x => 
      (if @idP ((no x) < k.+1) is Reflect_true H
    then (Ordinal H)
    else 
      (Ordinal (ltn0Sn k))).
    exists f'.
      rewrite / icancel //= => x Hx.
      rewrite / r -ltnS in Hx.
      rewrite / f' //=.
      case: idP=> //= Hi {Hx}.
      apply: ordinal_inj => {Hi} //=.
      rewrite / h //=; case: x => //.
    rewrite / dcancel //= => x Hx.
    rewrite / r -ltnS in Hx.
    rewrite / f' //=.
    case: idP=> //= Hi {Hx}.
    apply: ordinal_inj => {Hi} //=.
  rewrite (reindex_isum 
            (fun i : I_(n.+1) => coef p i * coef q (k - i)) H1).
  apply: eq_isum => //=.
    move=>i; rewrite / setA / h; case: i => //=.
  rewrite / dfequal => x Hx; congr (_ * _) => //=; congr coef=> //=.
    rewrite / h; case: x {Hx} => //=.
    congr minus; rewrite / h; case: x {Hx} => //=.
move=> Heq.
set f := fun k i : I_(n.+1) =>
  coef p1 k * (coef p2 i * coef p3 ((n - k) - i)).
set g1:= fun k i : I_(n.+1) =>
  (coef p1 i * coef p2 (k - i)) * coef p3 (n - k).
set g2 := fun k i : I_(n.+1) =>
  coef p1 k * (coef p2 (i - k) * coef p3 (n - i)).
have H1: 
  (fun k : I_(n.+1) => coef p1 k * coef (mult_poly p2 p3) (n - k)) =1
  (fun k : I_(n.+1) =>
       iprod (R:=R) (fun x : I_(n.+1) => x <= (n - k)) (f k)).
  move=>k => //=; rewrite -isum_distrL; congr (_ * _). 
  case: k => k Hk.
  have Hnk : n-k <n.+1.
    rewrite ltnS; apply: leq_subr.
  set nk:= Ordinal Hnk.
  move: (Heq nk p2 p3) => //.
have H2:
  (fun k : I_(n.+1) => coef (mult_poly p1 p2) k * coef p3 (n - k)) =1
  (fun k : I_(n.+1) => 
       iprod (R:=R) (fun x : I_(n.+1) => x <= k) (g1 k)).
  move=>k //=; rewrite -isum_distrR; congr (_ * _); apply: Heq.
have H3 :
  (fun k : I_(n.+1) => iprod (R:=R) (fun x : I_(n.+1) => x <= (n - k))
                                    (fun i : I_(n.+1) => f k i)) =1
  (fun k : I_(n.+1) => iprod (R:=R) 
                         (fun x : I_(n.+1) => (k <= x) && (x <= n))
                         (fun i : I_(n.+1) => g2 k i)).
  move=>  k //=.
  have Ht1: forall x : I_(n.+1), x - k < n.+1.
    move=> x //=.
    case: x => //= x Hx.
    case: k => //= k Hk.
    rewrite ltnS; apply: (@leq_trans x _ _) => //=; exact: leq_subr.
    set h : I_(n.+1) -> I_(n.+1) := 
      fun x => Ordinal (Ht1 x).
  have hP: forall x, (h x) <= n - k.
    move=> x; rewrite / h //=.
    apply: leq_sub2r.
    case: x => //=.
  rewrite (@eq_isumR _ _ _ (g2 k) (fun i => f k (h i))).
    symmetry; rewrite -(@iprod_image_ R) //=.
      apply: eq_isumL => //=.
      move=> x //=.
      case cx: (x <= n - k); move/idP:cx=>cx.
        apply/imageP.
        have Ht: forall x, x <= n - k -> x + k < S n.
          move=>x0; rewrite -(leq_add2r k) [((n - k) + k)%N]addnC.
          rewrite leq_add_sub //=.
          case: k {Ht1 h cx hP}=> //= k Hk.      
        exists (Ordinal (Ht _ cx)) => //=.
          rewrite {1}[(x + k)%N]addnC leq_addr andTb.
          rewrite -(leq_add2r k) [(n - k + k)%N]addnC
            leq_add_sub //= in cx.
          by case: k Ht1 h Ht hP=> //=.
        by rewrite / h //=; apply: ordinal_inj => //=; rewrite subn_addl.
      move/idP: cx => cx; apply/idP.
      move=>Him; move/imageP: Him => Him.
      elim: Him => x0 _ Hxx0; move: (hP x0) => cxf; rewrite -Hxx0 in cxf.
      by rewrite cxf //= in cx.
    rewrite / dinjective //= => x y Hx Hy Hxy.
    rewrite / h //= in Hxy.
    case: Hxy => Hxy.
    move/eqP: Hxy => Hxy; rewrite -(eqn_addr k) in Hxy.
    apply/eqP.
    rewrite ![(_ - k + k)%N]addnC !leq_add_sub //= in Hxy; 
      by elim: (andP Hx) => //=; elim: (andP Hy) => //=.
  move=> x //= Hx; rewrite / h / g2 / f //=.
  congr (_ * _); congr (_ * _); congr coef.
  rewrite subn_sub leq_add_sub //=.
  by elim: (andP Hx).
clear Heq.
rewrite (eq_isumR  
  (F:=(fun k : I_(n.+1) => coef p1 k * coef (mult_poly p2 p3) (n - k)))
  (F':=(fun k : I_(n.+1) => iprod (R:=R)
                                  (fun x : I_(n.+1) => x <= (n - k))
                                  (f k))));
  last move=> x _ //=.
rewrite (eq_isumR 
  (F:= (fun k : I_(n.+1) => coef (mult_poly p1 p2) k * coef p3 (n - k))) 
  (F':= (fun k : I_(n.+1) => iprod (R:=R)
                                   (fun x : I_(n.+1) => x <= k)
                                   (g1 k))));
  last move=> x _ //=.
rewrite (eq_isumR 
  (F:= (fun k : I_(n.+1) => iprod (R:=R) (fun x : I_(n.+1) => x <= n - k)
                                  (fun i : I_(n.+1) => f k i)))
  (F':= (fun k : I_(n.+1) => iprod (R:=R)
                                (fun x : I_(n.+1) => (k <= x) && (x <= n))
                                (fun i : I_(n.+1) => g2 k i))));
  last move=> x _ //=.
rewrite !pair_isum_dep //=.
set h :
  prod_finType I_(n.+1) I_(n.+1) -> prod_finType I_(n.+1) I_(n.+1) :=
  fun u => ((snd u), (fst u)).
clear H1 H2 H3 f.
set f:= (fun u : I_(n.+1) * I_(n.+1) => g2 (fst u) (snd u)).
set g:= (fun u : I_(n.+1) * I_(n.+1) => g1 (fst u) (snd u)).
rewrite (eq_isumR (F:= g) (F':= (fun i => f (h i)))); 
  last (move=> x _; rewrite / f / g / h / g1 / g2 mult_rA //=).
symmetry; rewrite -(@iprod_image_ R)//.
  apply: eq_isumL => x //=.
  have: snd x <= n by case: (snd x) => //=.
  move=> -> //=; rewrite andbT.
  case cx: (fst x <= snd x); move/idP:cx=>cx.
    apply/imageP.
    exists ((snd x), (fst x)) => //=.
    rewrite / h //=; case: x cx => //=.
  move/idP: cx => cx; apply/idP.
  move=>Him; move/imageP: Him => Him.
  elim: Him => x0 H1 Hxx0.
  rewrite / h //= in Hxx0.
  move/eqP: Hxx0 => Hxx1.
  have Hxx2: x == (snd x0, fst x0) by auto.
  move/pair_eq1: Hxx1 => //= Hxx1.
  move/pair_eq2: Hxx2 => //= Hxx2.
  by rewrite (eqP Hxx1) (eqP Hxx2) H1 in cx.
rewrite / dinjective //= => x y _ _ Hxy.
rewrite / h //= in Hxy; move/eqP: Hxy => Hxy.
apply/pair_eqP; rewrite / pair_eq //=.
apply/andP.
split; [move/pair_eq2: Hxy => //=|move/pair_eq1: Hxy => //=].
Qed.

Lemma poly_mult_addl: forall p1 p2 p3, 
  mult_poly p1 (add_poly p2 p3) = 
  add_poly (mult_poly p1 p2) (mult_poly p1 p3).
Proof.
move=> p1 p2 p3; apply/coef_eqP=> n.
rewrite !coef_add_poly !coef_mult_poly -isum_plus.
apply: eq_isumR => i _.
rewrite -plus_mult_l coef_add_poly; congr (_ * _).
Qed.

Lemma poly_mult_addr: forall p1 p2 p3, 
  mult_poly (add_poly p1 p2) p3= 
  add_poly (mult_poly p1 p3) (mult_poly p2 p3).
Proof.
move=> p1 p2 p3; apply/coef_eqP=> n.
rewrite !coef_add_poly !coef_mult_poly -isum_plus.
apply: eq_isumR => i _.
rewrite -plus_mult_r coef_add_poly; congr (_ * _).
Qed.

Fixpoint opp_poly_rec p : normal p -> polynomial :=
  if p is Adds a p' return normal p -> polynomial then 
    fun np => horner (opp_poly_rec (normal_behead np)) (- a)
  else fun _ => poly0.

Definition opp_poly p :=
  let: Poly _ np := p in
  (opp_poly_rec np).

Lemma coef_opp_poly p i : 
  coef (opp_poly p) i = - (coef p i).
Proof.
move=> [p np].
by elim: p np => [|a p IHp] np [|i] //=;
  rewrite (coef0, opp_r0, coef_horner_0, coef_horner_S) // ?IHp // opp_r0.
Qed.

Lemma opp_poly_P : forall p, add_poly (opp_poly p) p = poly0.
Proof.
move=> p; apply/coef_eqP=> n.
by rewrite !coef_add_poly !coef_opp_poly plus_opp_rl coef0.
Qed.

Lemma poly1_diff_poly0 : poly1 <> poly0.
Proof.
unlock poly0; unlock poly1; unlock const_poly.
case: insubP => [[[] _] _  //=  |].
by rewrite / normal //=; move/negbE2; move/eqP; move/one_diff_0.
Qed.

Definition poly_ring : ring.
exists polynomial_eqType poly0 poly1 opp_poly add_poly mult_poly.
split=>//=; [ | | (* 3 *) exact: poly_mult_addl |
  (* 4 *) exact: poly_mult_addr | (* 5 *) exact: poly1_diff_poly0].
  split; last exact: poly_addC.
  split; last exact: opp_poly_P.
  split; [ exact: poly_addA | exact: poly_add0P | ].
  by move=> *; rewrite poly_addC poly_add0P.
split; [ exact: poly_multA | exact: poly_mult1P | exact: poly_multP1 ].
Defined.

Canonical Structure poly_ring.

End PolynomialRing.

Section PolynomialDegree.

Definition deg_poly (p : polynomial) := let: Poly sp _ := p in size sp.

Lemma deg_poly0: deg_poly poly0 = 0%N.
Proof. rewrite / deg_poly; unlock poly0=>//. Qed.

Lemma deg_poly0_eq : forall p, reflect (p=poly0) (deg_poly p == 0%N).
Proof.
move=> [p np]; apply: (iffP idP); last (by move=> ->; rewrite deg_poly0).
move/eqP=>//= H; apply/coef_eqP=>//= i; unlock poly0=>//=; congr sub.
clear np i; case: p H=>//.
Qed.


Lemma deg_const_poly: forall c, c!=0 -> deg_poly (const_poly c) = 1%N.
Proof.
unlock const_poly => c /=; case: insubP => [[_ _] _ /= -> //|].
by rewrite / normal//=; move=> H1 H2; rewrite H2 in H1.
Qed.

Lemma deg_horner : forall p c,
  p != poly0 -> deg_poly (horner p c) = (deg_poly p + 1)%N.
Proof.
unlock horner => [] [[|a p'] np] c //=; last by rewrite addn1.
unlock poly0=>//.
Qed.

Lemma deg_coef : forall p i, deg_poly p <= i -> coef p i = 0.
Proof. by move=> [p np] i //= Hd; apply: sub_default. Qed.

(*
Lemma deg_add_poly: forall p1 p2,
  deg_poly (add_poly p1 p2) <=  maxn (deg_poly p1) (deg_poly p2).
Proof.
*)

End PolynomialDegree.

End Polynomial.

Section PolynomialComRing.
Variable R : com_ring.

Lemma poly_multC : forall p1 p2 :polynomial R,
  mult_poly p1 p2 = mult_poly p2 p1.
Proof.
move=> p1 p2; apply/coef_eqP=> n.
rewrite !coef_mult_poly.
have Hk: forall (k: I_(n.+1)), n - k < n.+1
  by move=>k; apply: leq_subr.
pose g: I_(n.+1) -> I_(n.+1) := fun k => Ordinal (Hk k).
suffices : setA I_(n.+1) =1 image g (setA I_(n.+1)).
  move/(eq_iprod_set_(R:=R)
   (fun k : I_(n.+1) => coef p2 k * coef p1 (n - k))) => ->.
  rewrite (iprod_image_ (R:=R)) / g //=; first apply: (@eq_iprod_f_ R).
    move=> k _ //=; rewrite mult_rC; congr (_ * _).
    rewrite leq_sub_sub//; case: k=>//.
  move=> //= x y _ _; case=>//= H1; apply: ordinal_inj.
  rewrite -(@leq_sub_sub x n); last (rewrite -ltnS; apply: ordinal_ltn).
  rewrite H1 leq_sub_sub// -ltnS; apply: ordinal_ltn.
move=> x; symmetry; apply/imageP; rewrite / setA //.
exists (Ordinal (Hk x))=>//.
rewrite {}/g //=; case: x => x x0; apply: ordinal_inj=>//=.
rewrite leq_sub_sub//.
Qed.

Definition poly_com_ring : com_ring.
exists (poly_ring R).
rewrite //=; apply: poly_multC.
Defined.

Canonical Structure poly_com_ring.

End PolynomialComRing.

Section EvalPolynomial.
Open Scope ring_scope.
Variable R: ring.

Fixpoint eval_poly_rec (p : seq R) : normal p -> R -> R :=
  if p is (Adds a p') return normal p -> R -> R then
    fun np x => a + x * (eval_poly_rec (normal_behead np) x)
  else fun _ _ => 0.

Definition eval_poly (p : poly_ring R) (x : R) : R :=
  let: Poly _ np := p in (eval_poly_rec np x).

Lemma eval_poly0 : forall x, eval_poly (@poly0 R) x = 0.
Proof. by unlock poly0=>//. Qed.

Lemma eval_poly_const : forall c x, eval_poly (const_poly c) x = c.
Proof.
unlock const_poly => c x /=; case: insubP => [[[] a [] ns ] //= _ [] ->|].
  by rewrite mult_r0r plus_r0r.
by rewrite eval_poly0 / normal //=; move/negbE2; move/eqP => ->.
Qed.

Lemma eval_poly_horner : forall p c x,
  eval_poly (horner p c) x = x * (eval_poly p x) + c.
Proof.
unlock horner => [] [[|a p'] np] c x //=.
  by move=> *; rewrite mult_r0r plus_r0l eval_poly_const.
rewrite plus_rC//=; congr (_+_); congr (_*_); congr (_+_); congr (_*_).
congr eval_poly_rec; apply: bool_irrelevance.
Qed.

Lemma eval_poly_plus : forall p q x,
  eval_poly (p + q) x = (eval_poly p x) + (eval_poly q x).
Proof.
case=>//; elim=>// [|a p Hp np].
  by move=> //=_; case=>//= q nq x; rewrite plus_r0l.
case=>//; case=>// [|b q nq] x; first (by move=> *; rewrite plus_r0r).
rewrite //= eval_poly_horner.
move: (Hp (normal_behead np) (Poly (normal_behead nq)) x)=>//= ->.
rewrite plus_rCA -plus_rA; congr (_+_).
rewrite -plus_rCA plus_rC; congr (_+_).
apply: plus_mult_l.
Qed.

Definition com_coef p (x :R) := forall k, (coef p k) * x = x * (coef p k).

Lemma com_coefP : forall p x, com_coef p x ->
  x * (eval_poly p x) = (eval_poly p x) * x.
Proof.
case=>//; elim=> //=; first (by move=> *; rewrite mult_r0r mult_r0l).
move=> a p Hp np x H; rewrite plus_mult_r plus_mult_l; congr (_+_).
  (by move: (H 0%N) =>//).
rewrite -mult_rA Hp //.
(move=> i; move: (H (S i))=>//).
Qed.

Lemma eval_poly_mult_cst_poly_l : forall c (p : poly_ring R) x,
  (x * c = c * x) ->
  eval_poly (mult_cst_poly_l c p) x = c * (eval_poly p x).
Proof.
move=> c []; elim=>//= [| a p Hp np x Hc].
  (by move=> *; rewrite eval_poly0 mult_r0r).
by rewrite eval_poly_horner//= Hp// mult_rA Hc -mult_rA
  -plus_mult_l plus_rC.
Qed.

Lemma eval_poly_mult_cst_poly_r : forall c (p : poly_ring R) x,
  eval_poly (mult_cst_poly_r p c) x = (eval_poly p x) * c.
Proof.
move=> c []; elim=>//= [| a p Hp np x].
  (by move=> *; rewrite eval_poly0 mult_r0l).
by rewrite eval_poly_horner//= Hp// mult_rA -plus_mult_r plus_rC.
Qed.

Lemma eval_poly_mult : forall (p q : poly_ring R) x, (com_coef p x) ->
  eval_poly (p * q) x = (eval_poly p x) * (eval_poly q x).
Proof.
case=>//; elim=>// [ /= np [] |a p Hp np].
  by move=> *; rewrite eval_poly0 mult_r0l.
case=>//; case=>// [ /= |b q nq] x Hc.
  by move=> *;  rewrite eval_poly0 mult_r0r.
rewrite //= !eval_poly_horner !eval_poly_plus !eval_poly_horner.
rewrite (eval_poly_mult_cst_poly_l (Poly (normal_behead nq))) //;
  last (by move: (Hc 0%N) =>//).
rewrite (eval_poly_mult_cst_poly_r b (Poly (normal_behead np))).
move: (Hp (normal_behead np) (Poly (normal_behead nq)) x)=>//= ->;
  last by (move=> i; move: (Hc (S i))=>//).
rewrite !plus_mult_r !plus_mult_l plus_rC !mult_rA !plus_rA
  mult_r0r plus_r0r; move: (Hc 0%N) => //= ->.
rewrite -[x * x * (eval_poly_rec _ _)]mult_rA /=
  {2}[x * eval_poly_rec _ _](@com_coefP (Poly (normal_behead np)))/=
  ?mult_rA//.
by move=> i; move: (Hc (S i))=>//.
Qed.

Lemma factor_th : forall (p p1 p2 : poly_ring R) a,
  com_coef p1 a -> (p = p1 * (polyX_a a) * p2) -> eval_poly p a = 0.
Proof.
move => p p1 p2 a Hp1 ->; rewrite -mult_rA.
rewrite !eval_poly_mult; unlock polyX_a=>//=;
  last (by case=>//=[|[|n]];
    rewrite ?coef_horner_0 -?mult_opp_rl -?mult_opp_rr// ?coef_horner_S
      ?coef_poly1_0 ?mult_r1l ?mult_r1r // ?coef_poly1_S
      ?mult_r0l ?mult_r0r).
by rewrite eval_poly_horner eval_poly_const mult_r1r plus_opp_rr mult_r0l
  mult_r0r.
Qed.

End EvalPolynomial.

Unset Implicit Arguments.
