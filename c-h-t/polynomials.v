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

Lemma eq_p0_subP : forall p, reflect (sub 0 p =1 sub 0 seq0) (eq_p0 p).
Proof.
elim=> //=[|x s Hp]; apply: (iffP idP) => //=.
  move=> Heq [|i] //=; elim (andP Heq) => //; move/eqP => // _;
  by  move/Hp => // H1; move: (H1 i) => ->; rewrite sub_seq0.
move=> H1; move: (H1 0%N) => //= ->; rewrite eq_refl andTb.
apply/Hp=> i; move: (H1 (S i)) => //=.
by rewrite sub_seq0.
Qed.

Lemma eq_p0_eq_p: forall p, eq_p0 p = (eq_p p seq0).
Proof. elim => //= [a p Hrec H]. Qed.

Lemma eq_p_subP : forall p q, reflect (sub 0 p =1 sub 0 q) (eq_p p q).
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

(* normal polynomial *)

(* A polynomial is normal if its last element is <> 0 *)
Definition normal (p : poly_coef) := last 1 p != 0.

Lemma normal0: normal seq0.
Proof.
by rewrite /normal /=; apply/negP => H1; case (@one_diff_0 R); apply/eqP.
Qed.

Lemma normal_behead: forall a p, normal (Adds a p) -> normal p.
Proof.
move => a [|b p] // _.
by rewrite /normal /=; apply/negP => H1; case (@one_diff_0 R); apply/eqP.
Qed.

(* --- *)

End PolynomialCoef.

(* Definition of the sigma type of normal polynomial *)

CoInductive polynomial : Type := Poly p of normal p.

Notation poly := polynomial.

Coercion seq_of_poly p := let: Poly s _ := p in s.

Definition coef p := let: Poly p _:= p in sub 0 p.

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
   rewrite / eq_p0 //=; elim: p2 {H1 H2} => //= [x s Hs] H1.
   by elim: (andP H1); move/eqP=> <-; exact Hs.
 - move=> H1; move: np1; rewrite / normal //= => H2.
   suffices: (last a1 p1) != 0 => //=.
   suffices: (last a1 p1) = 0 => //=; 
     first (move=> ->; move/eqP=>//=).
   elim: (andP H1) =>  //=; move/eqP=><-.
   rewrite / eq_p0 //= ; elim: p1 {H1 H2} => //= [x s Hs] H1.
   by elim: (andP H1); move/eqP=> <-; exact Hs.
 - move=> H1; elim: (andP H1); move/eqP=> {H1} H1 H2.
   by apply/coef_eqP; apply/eq_p_subP => /=; rewrite H1 H2 eq_refl.
move/coef_eqP=> //= H1; apply/andP.
split; first (apply/eqP; apply: (H1 0%N)).
apply/eq_p_subP=>i; apply: (H1 (S i)).
Qed.

Canonical Structure polynomial_eqType := EqType eq_pP.

Section PolynomialRing.

Definition const_poly c :=
  if insub normal (Seq c) is Some (EqSig p np) then locked Poly p np
  else Poly normal0.

Notation Local "\C c" := (const_poly c) (at level 0).

Definition poly0 := const_poly 0.
Definition poly1 := const_poly 1.

Notation Local "\C0" := poly0 (at level 0).
Notation Local "\C1" := poly1 (at level 0).

Definition horner c p : polynomial :=
  if p is Poly (Adds _ _ as sp) np then
    locked Poly (Adds c sp) np
  else \C c.

Definition mkPoly := foldr horner \C0.

Definition polyX := mkPoly (Seq 0 1).
Notation "\X" := polyX.

Lemma coef0 : forall i, coef poly0 i = 0.
Proof.
rewrite /poly0; unlock const_poly.
by case: insubP => [[_ _] _ /= -> //|] /= [] *;
   rewrite //= ?sub_seq0.
Qed.

Lemma coef_const_0 : forall c, coef (const_poly c) 0 = c.
Proof.
unlock const_poly => c /=.
case: insubP => [[_ _] _ /= -> //|].
by rewrite negbK //=; move/eqP.
Qed.

Lemma coef_const_S : forall c i, coef (const_poly c) i.+1 = 0.
Proof.
by unlock const_poly poly0 => c [|i] /=; case: insubP => [[_ _] _ /= ->|].
Qed.

Lemma coef_horner_0 : forall p c, coef (horner c p) 0 = c.
Proof.
unlock horner => [] [[|_ _] _] c //=; exact: coef_const_0.
Qed.

Lemma coef_horner_S : forall p c i, coef (horner c p) i.+1 = coef p i.
Proof.
unlock horner => [] [[|_ _] _] c [|i] //=; exact: coef_const_S.
Qed.

Lemma coef_horner_foldr : forall (n :nat) (f: nat -> R),
  (forall k, n<=k -> f k = 0) ->
  (forall k, coef (foldr (fun k p => horner (f k) p) poly0 (iota 0 n)) k =
   f k).
Proof.
move=> n f Hfk k.
case Ck:(k<n); move/idP: Ck => Ck.
  elim: n k f {Hfk} Ck=>//= n Hn k f Ck.
  rewrite -(iota_maps 1 n) foldr_maps.
  case: k Ck =>//= [_ | k Ck]; first (by rewrite coef_horner_0).
  by rewrite !coef_horner_S Hn// addn1.
rewrite Hfk; last (by move/idP: Ck; rewrite -leqNgt).
elim: n k f {Hfk} Ck=>//= [k f Ck|n Hn k f Ck]; first by rewrite coef0.
rewrite -(iota_maps 1 n) foldr_maps.
case: k Ck =>//= [ k Ck].
by rewrite coef_horner_S Hn//.
Qed.

Lemma coef_mkPoly : forall s, coef (mkPoly s) =1 sub 0 s.
Proof.
by elim=> [|c s IHs] /= [|i];
  rewrite (coef0, coef_horner_0, coef_horner_S) /=.
Qed.

Fixpoint add_poly_seq (s1 s2 : seq R) {struct s1} : seq R :=
  match s1, s2 with
  | Seq0, _ => s2
  | _, Seq0 => s1
  | Adds c1 s1', Adds c2 s2' => Adds (c1 + c2) (add_poly_seq s1' s2')
  end.

Definition add_poly (p1 p2 : polynomial) := mkPoly (add_poly_seq p1 p2).

Notation Local "p1 +p p2" := (add_poly p1 p2) (at level 50).

Lemma sub_add_poly_seq : forall s1 s2 i,
  sub 0 (add_poly_seq s1 s2) i = sub 0 s1 i + sub 0 s2 i.
Proof.
by elim=> [|c1 s1 IHs] [|c2 s2] [|i] //=; rewrite ?plus_r0r ?plus_r0l.
Qed.

Lemma coef_add_poly p1 p2 i : 
  coef (p1 +p p2) i = coef p1 i + coef p2 i.
Proof.
move=> [p1 np1] [p2 np2] i.
by rewrite coef_mkPoly /coef /= {np1 np2} sub_add_poly_seq.
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

Fixpoint mult_poly_seq (s1 s2 : seq R) {struct s1} : seq R :=
  if s1 is Adds c1 s1' then
    add_poly_seq (maps (fun c2 => c1 * c2) s2)
                 (Adds 0 (mult_poly_seq s1' s2))
  else seq0.

Definition mult_poly (p1 p2 : poly) := mkPoly (mult_poly_seq p1 p2).

Notation Local "p1 *p p2" := (mult_poly p1 p2) (at level 40).

(* Some useful constant *)

Lemma coef_mult_poly p1 p2 i :
  coef (p1 *p p2) i =
  \sum_() (fun k :I_(i.+1) => (coef p1 k) * coef p2 (i - k)).
Proof.
move=> [p1 np1] [p2 np2] i.
rewrite coef_mkPoly /coef /= {np1 np2}.
elim: p1 p2 i => [|c1 p1 /= IHp] [|c2 p2] [|i] //=;
  rewrite ?coef0;
  try (symmetry; apply: isum0 => //= x Hx; rewrite sub_seq0 mult_r0l //).
- symmetry; apply: isum0 => //= x Hx; rewrite mult_r0r //.
- rewrite IHp !iprod_f1_//= => x _; rewrite sub_seq0 mult_r0r //.
- pose x0:= (@Ordinal 1%N 0%N (ltnSn 0)).  
  rewrite (@iprod_set1_ R I_(1) x0)/= {}/x0 ?plus_r0r//.
  move=> [x Hx]=>/=; rewrite /setA; symmetry; apply/eqP.
  by apply: ordinal_inj=>//=; case: x Hx.
rewrite sub_add_poly_seq IHp (@iprod_ord_rec_l R (i.+1)) /=; congr (_ + _).
by elim: p2 i {IHp p1}=>[|x p2 IHp] [|i]/=; rewrite ?sub_seq0 ?mult_r0r.
Qed.

Lemma coef_mult_poly_rev : forall p1 p2 i,
  coef (p1 *p p2) i =
  \sum_() (fun k :I_(i.+1) => (coef p1 (i - k)) * coef p2 k).
Proof.
move=> p1 p2 i; rewrite coef_mult_poly.
set f:=(fun k : I_(i.+1) => coef p1 k * coef p2 (i - k)).
rewrite (reindex_isum f (h := (@ord_opp i))).
  apply: eq_isum=> [x|x _]; rewrite /setA // {}/f.
  congr (_*_); congr coef=>//=; exact: sub_ordK.
exists (@ord_opp i)=> x _; apply: ordinal_inj=>/=; 
  apply: leq_sub_sub; case: x=>//=.
Qed.



Definition polyX_a a := locked horner (-a) poly1.
(* --- *)

Lemma coef_poly1_0: coef poly1 0 = 1.
Proof. by rewrite coef_const_0. Qed.

Lemma coef_poly1_S: forall i, coef poly1 (S i) = 0.
Proof. by move=> i; rewrite coef_const_S. Qed.

Lemma poly_mult1P : forall p, \C1 *p p = p.
Proof.
move=> p; apply/coef_eqP=> i.
rewrite coef_mult_poly //=.
rewrite (@iprod_ord_rec_l R) //.
rewrite //= coef_poly1_0 mult_r1l subn0 -{2}(plus_r0r (coef p i)).
congr (_ + _); apply: (@iprod_f1_ R).
by move=> x _ //=; rewrite coef_poly1_S mult_r0l.
Qed.

Lemma poly_multP1 : forall p, p *p \C1 = p.
Proof.
move=> p; apply/coef_eqP=> i.
rewrite coef_mult_poly //=.
rewrite (@iprod_ord_rec_r R) //.
rewrite //= subnn coef_poly1_0 mult_r1r -{2}(plus_r0l (coef p i)).
congr (_ + _); apply: (@iprod_f1_ R).
case=>//= x Hx _ //=; rewrite -ltn_0sub in Hx.
by case: (i-x) Hx =>//= n Hn; rewrite coef_poly1_S mult_r0r.
Qed.

Lemma poly_multA : forall p1 p2 p3, p1 *p (p2 *p p3) = p1 *p p2 *p p3.
Proof.
move=> p1 p2 p3; apply/coef_eqP=> i.
rewrite coef_mult_poly coef_mult_poly_rev.
pose coef3 j k := coef p1 j * (coef p2 (i - j - k) * coef p3 k).
transitivity (\sum_() (fun j :I_(i.+1) => 
              \sum_( in (fun k :I_(i.+1) => k <= i - j))
                   (fun k => coef3 j k))).
  apply: eq_isumR => /= j _.
  rewrite coef_mult_poly_rev isum_distrL //.
  rewrite (iprod_ord_inj (R:=R) _ (leq_subr _ _)); apply: eq_isumR => x _ //=.
set r': I_(i.+1) -> set I_(i.+1) := (fun j k : I_(i.+1) => k <= i - j).
rewrite (@exchange_isum_dep _ _ _ _ r' (setA I_(i.+1)) _) //=.
apply: eq_isumR => x _ //=.
transitivity (\sum_( in (fun k :I_(i.+1) => k <= i - x)) (fun k => coef3 k x)).
  apply: eq_isumL=> k; rewrite {}/r' -ltnS -(ltnS k) -!leq_subS ?leq_ord //.
  by rewrite -ltn_0sub -(ltn_0sub k) !subn_sub addnC.
rewrite (iprod_ord_inj (R:=R) _ (leq_subr _ _)) coef_mult_poly isum_distrR /=.
by apply: eq_isumR => k _ //=; rewrite /coef3 !subn_sub addnC mult_rA.
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

Fixpoint opp_poly_seq p : normal p -> polynomial :=
  if p is Adds a p' return normal p -> polynomial then 
    fun np => horner (- a) (opp_poly_seq (normal_behead np))
  else fun _ => poly0.

Definition opp_poly p :=
  let: Poly _ np := p in
  (opp_poly_seq np).

Lemma coef_opp_poly p i : 
  coef (opp_poly p) i = - (coef p i).
Proof.
move=> [p np].
by elim: p np => [|a p IHp] np [|i] //=;
  rewrite (coef0, opp_r0, coef_horner_0, coef_horner_S) // ?IHp // opp_r0.
Qed.

Lemma opp_poly_P : forall p, add_poly (opp_poly p) p = \C0.
Proof.
move=> p; apply/coef_eqP=> n.
by rewrite !coef_add_poly !coef_opp_poly plus_opp_rl coef0.
Qed.

Lemma poly1_diff_poly0 : \C1 <> \C0.
Proof.
unlock poly0; unlock poly1; unlock const_poly=>//=.
case insubP => [[? ?] //|]/=.

move/(congr1 seq_of_poly).

case: insubP => [[_ _] _ //= |].
case: insubP => [[[] x] y u //=  |].
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

(* eval poly fun need that the variable commute with all coef *)

Fixpoint eval_poly_rec (p : seq R) : normal p -> R -> R :=
  if p is (Adds a p') return normal p -> R -> R then
    fun np x => a + (eval_poly_rec (normal_behead np) x) * x
  else fun _ _ => 0.

Definition eval_poly (p : poly_ring R) (x : R) : R :=
  let: Poly _ np := p in (eval_poly_rec np x).

Lemma eval_poly0 : forall x, eval_poly (@poly0 R) x = 0.
Proof. by unlock poly0=>//. Qed.

Lemma eval_poly_const : forall c x, eval_poly (const_poly c) x = c.
Proof.
unlock const_poly => c x /=; case: insubP => [[[] a [] ns ] //= _ [] ->|].
  by rewrite mult_r0l plus_r0r.
by rewrite eval_poly0 / normal //=; move/negbE2; move/eqP => ->.
Qed.

Lemma eval_poly_horner : forall p c x,
  eval_poly (horner p c) x = c + (eval_poly p x) * x.
Proof.
unlock horner => [] [[|a p'] np] c x //=.
  by move=> *; rewrite mult_r0l plus_r0r eval_poly_const.
congr (_+_); congr (_*_); congr (_+_); congr (_*_).
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
by rewrite plus_mult_r -plus_rA plus_rC -plus_rCA plus_rC plus_rA.
Qed.

Definition com_coef p (x :R) := forall k, (coef p k) * x = x * (coef p k).

Lemma com_coefP : forall p x, com_coef p x ->
  x * (eval_poly p x) = (eval_poly p x) * x.
Proof.
case=>//; elim=> //=; first (by move=> *; rewrite mult_r0r mult_r0l).
move=> a p Hp np x H; rewrite plus_mult_r plus_mult_l; congr (_+_).
  (by move: (H 0%N) =>//).
rewrite mult_rA Hp //; move=> i; move: (H (S i))=>//.
Qed.

Lemma eval_poly_mult_cst_poly_l : forall c (p : poly_ring R) x,
  eval_poly (mult_cst_poly_l c p) x = c * (eval_poly p x).
Proof.
move=> c []; elim=>//= [| a p Hp np x].
  (by move=> *; rewrite eval_poly0 mult_r0r).
by rewrite eval_poly_horner//= Hp// plus_mult_l -mult_rA.
Qed.

Lemma eval_poly_mult_cst_poly_r : forall c (p : poly_ring R) x,
  (x * c = c * x) ->
  eval_poly (mult_cst_poly_r p c) x = (eval_poly p x) * c.
Proof.
move=> c []; elim=>//= [| a p Hp np x Hc].
  (by move=> *; rewrite eval_poly0 mult_r0l).
by rewrite eval_poly_horner//= Hp// -mult_rA -Hc mult_rA -plus_mult_r.
Qed.

Lemma eval_poly_mult : forall (p q : poly_ring R) x, (com_coef q x) ->
  eval_poly (p * q) x = (eval_poly p x) * (eval_poly q x).
Proof.
case=>//; elim=>// [ /= np [] |a p Hp np].
  by move=> *; rewrite eval_poly0 mult_r0l.
case=>//; case=>// [ /= |b q nq] x Hc.
  by move=> *;  rewrite eval_poly0 mult_r0r.
rewrite //= !eval_poly_horner !eval_poly_plus !eval_poly_horner.
rewrite (eval_poly_mult_cst_poly_l a (Poly (normal_behead nq))) //.
rewrite (eval_poly_mult_cst_poly_r (Poly (normal_behead np)));
  last (by move: (Hc 0%N) =>//).
move: (Hp (normal_behead np) (Poly (normal_behead nq)) x)=>//= ->;
  last by (move=> i; move: (Hc (S i))=>//).
rewrite !plus_mult_r !plus_mult_l !plus_rA !mult_rA 
  mult_r0l plus_r0r -[eval_poly_rec _ _ * b * x]mult_rA  (Hc 0%N) /=.
rewrite -[(eval_poly_rec _ _) * x * (eval_poly_rec _ _)]mult_rA /=.
rewrite [x * eval_poly_rec _ _](@com_coefP (Poly (normal_behead nq)) x)/=
  ?mult_rA //.
by move=> i; move: (Hc (S i))=>/=.
Qed.

Lemma factor_th : forall (p p1 p2 : poly_ring R) a,
  com_coef p2 a -> (p = p1 * (polyX_a a) * p2) -> eval_poly p a = 0.
Proof.
move => p p1 p2 a Hp1 ->.
rewrite !eval_poly_mult//; unlock polyX_a=>//=;
  first ( by rewrite eval_poly_horner eval_poly_const mult_r1l
          plus_opp_rl mult_r0r mult_r0l).
by case=>//=[|[|n]]; 
  rewrite ?coef_horner_0 -?mult_opp_rr -?mult_opp_rl// ?coef_horner_S
    ?coef_poly1_0 ?mult_r1r ?mult_r1l // ?coef_poly1_S ?mult_r0r ?mult_r0l.
Qed.

End EvalPolynomial.

Unset Implicit Arguments.
