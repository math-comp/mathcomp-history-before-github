Require Import ssreflect ssrbool funs eqtype ssrnat seq fintype tuple
 indexed_products div groups determinant ring polynomials.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.

Section Cayley.
Variable R : com_ring.
Variable (n : nat).
Hypothesis (Hn : 0 < n).

Notation "\P[x]" := (poly_com_ring R).
Notation "\M_(n)" := (matrix_ring R Hn).

Notation "\Mp_(n)" := (matrix_ring \P[x] Hn).
Notation "\Pm[x]" := (poly_ring \M_(n)).

Lemma m2f_iprod : forall k (f : I_(k) -> \M_(n)) i j,
  (iprod (R:=\M_(n)) (setA I_(k)) f) i j =
   iprod (R:=R) (setA I_(k)) (fun k => (f k) i j).
Proof.
elim=>//[f i j| k Hk f i j].
  rewrite !(iprod_set0_) /= ?m2f //; case=>//=.
rewrite (@iprod_ord_rec_r R) (@iprod_ord_rec_r \M_(n)) m2f; congr (_ + _).
by rewrite (Hk (fun x => f (lshiftSn x))); apply (@eq_iprod_f_ R)=> x Hx.
Qed.

Lemma coef_iprod : forall m (f : I_(m) -> \P[x]) k,
  coef (iprod (R:=\P[x]) (setA I_(m)) f) k =
  iprod (R:=R) (setA I_(m)) (fun i => coef (f i) k).
Proof.
elim=>//[f k| m Hm f k].
  rewrite !(iprod_set0_) /= ?coef0 //; case=>//=.
rewrite (@iprod_ord_rec_r R) (@iprod_ord_rec_r \P[x]) coef_add_poly;
  congr (_ + _).
by rewrite (Hm (fun x => f (lshiftSn x))); apply (@eq_iprod_f_ R)=> x Hx.
Qed.

Section DegMatrixOfPoly.

Definition deg_mx_of_poly (M : \Mp_(n)) : nat :=
  maxn_seq (fun x => (deg_poly (M (fst x) (snd x)))) (prod_enum I_(n) I_(n)).

Lemma deg_mx_of_polyP: forall (M : \Mp_(n)) i j, 
  deg_poly (M i j) <= deg_mx_of_poly M.
Proof.
move=>M i j.
rewrite / deg_mx_of_poly.
apply: (@maxn_seqP _ (fun x => (deg_poly (M (fst x) (snd x))))
                     (prod_enum I_(n) I_(n)) (i,j)).
by rewrite mem_enum / setA.
Qed.

End DegMatrixOfPoly.

Definition phi (M : \Mp_(n)) : \Pm[x] :=
  foldr (fun k p => 
             (horner p (matrix_of_fun (fun i j=> coef (M i j) k))))
  (@poly0 _) (iota 0 (deg_mx_of_poly M)).

Lemma phi_coef : forall (M : \Mp_(n)) i j k,
  coef (M i j) k = (coef (phi M) k) i j.
Proof.
move=> M i j k.
rewrite / phi.
set fk: nat -> \M_(n) :=
  (fun k => (matrix_of_fun (fun i0 j0 => (coef (M i0 j0) k)))).
have Hfk: forall k', (deg_mx_of_poly M) <= k' -> fk k' = 0.
  move=> k' Hk'; rewrite / fk /=.
  apply/matrix_eqP; apply: EqMatrix => x y; rewrite !m2f.
  by apply: deg_coef; apply: (leq_trans (deg_mx_of_polyP M x y) Hk').
move/matrix_eqP: (coef_horner_foldr Hfk k); case=>//= ->.
by rewrite m2f.
Qed.

(* --- phi is ring morphism --- *)
Lemma phi_plus : forall (M1 M2 : \Mp_(n)),
  phi (M1 + M2) = (phi M1) + (phi M2).
Proof.
move=> M1 M2.
apply/coef_eqP => k.
apply/matrix_eqP; apply: EqMatrix=> i j.
by rewrite -!phi_coef coef_add_poly //= !m2f -!phi_coef coef_add_poly.
Qed.

Lemma phi_mult : forall (M1 M2 : \Mp_(n)),
  phi (M1 * M2) = (phi M1) * (phi M2).
Proof.
move=> M1 M2.
apply/coef_eqP => k.
apply/matrix_eqP; apply: EqMatrix=> i j.
rewrite -!phi_coef !m2f !coef_mult_poly m2f_iprod coef_iprod.
have H1: dfequal (setA I_(n))
  (fun i0 => coef (M1 i i0 * M2 i0 j) k)
  (fun i0 => (iprod (R:=R) (setA I_(k.+1))
        (fun k0 => (coef (M1 i i0) k0 * coef (M2 i0 j) (k - k0))))).
  move=> i0 _ //=; rewrite -coef_mult_poly//=.
rewrite (eq_iprod_f_ (R:=R) H1) (exchange_iprod_ (R:=R)); clear H1.
apply: (eq_iprod_f_ (R:=R))=> i0 _//; rewrite m2f.
apply: (eq_iprod_f_ (R:=R))=> i1 _//.
by rewrite -!phi_coef.
Qed.

Lemma phi_one : phi 1 = 1.
Proof.
apply/coef_eqP => k.
apply/matrix_eqP; apply: EqMatrix=> i j.
rewrite -!phi_coef.
case: k=>// [|k].
  rewrite coef_poly1_0 !m2f//=.
  by case Hij: (i==j); rewrite ?coef_poly1_0 ?coef0.
rewrite coef_poly1_S !m2f//=.
by case Hij: (i==j); rewrite ?coef_poly1_S ?coef0.
Qed.

(* --- *)

Fixpoint poly2poly_of_mx_rec (p : seq R) : normal p -> \Pm[x] :=
  if p is (Adds a p') return normal p -> \Pm[x] then
    fun np =>
      horner (poly2poly_of_mx_rec (normal_behead np)) 
             (matrix_scale a (@unit_matrix R n))
  else fun _ => (@poly0 \M_(n)).

Definition poly2poly_of_mx (p : \P[x]) :=
  let: Poly _ np := p in
  poly2poly_of_mx_rec np.

Notation "'p2pm'" := poly2poly_of_mx : local_scope.

Lemma coef_poly2poly_of_mx : forall p k i j,
  coef (p2pm p) k i j =
  (coef p k) * (unit_matrix R n i j).
Proof.
case=>//; elim=>//=.
  move=> np k i j; rewrite coef0 sub_seq0 mult_r0l m2f//.
move=> x s Hr np [|k] i j; first rewrite coef_horner_0 m2f//=.
by rewrite coef_horner_S m2f//= Hr m2f.
Qed.

Lemma phi_polyP : forall (p : \P[x]),
  (phi (matrix_scale p (unit_matrix \P[x] n))) = p2pm p.
Proof.
move=>p; apply/coef_eqP=>k.
apply/matrix_eqP; apply: EqMatrix=> i j.
rewrite -phi_coef coef_poly2poly_of_mx !m2f.
by case Hc:(i==j); rewrite ?mult_r1r ?mult_r0r ?coef0.
Qed.

Definition poly_car (A : \M_(n)) : \P[x] :=
  (@determinant \P[x] n 
                (matrix_of_fun
                  (fun i j=>
                    if i==j then ((@polyX R) + - (const_poly (A i j)))
                    else (- const_poly (A i j))))).

Theorem Cayley_Hamilton : forall A,
  eval_poly (p2pm (poly_car A)) A = 0.
Proof.
move=> A.
set X_I_A:=(matrix_of_fun
                  (fun i j=>
                    if i==j then ((@polyX R) + - (const_poly (A i j)))
                    else (- const_poly (A i j)))).
move: (mult_adugateR X_I_A) => H1.
suffices: phi (X_I_A * (adjugate X_I_A)) = 
          phi (matrix_scale (poly_car A) (unit_matrix \P[x] n));
  last (by rewrite //= H1 ); clear H1=>H1.
(* How can i do this automaticly *)
rewrite phi_mult in H1; symmetry in H1.
rewrite -phi_polyP.
suffices: (phi X_I_A) = polyX_a A; first (move=> H2 ).
  rewrite H2 in H1.
  apply: (factor_th (p1:=1) (p2:=(phi (adjugate X_I_A))))=>//;
    rewrite ?mult_r1l//.
  by move=> [|k]; rewrite ?coef_poly1_0 ?coef_poly1_S ?mult_r0l ?mult_r0r
    ?mult_r1r ?mult_r1l.
apply/coef_eqP => k;  apply/matrix_eqP; apply: EqMatrix=> i j.
rewrite -phi_coef m2f; unlock polyX_a; unlock polyX.
case: k=>//= [|k].
  rewrite !coef_horner_0; case Hij:(i==j)=>//=.
    by rewrite coef_add_poly coef_horner_0 coef_opp_poly coef_const_0 
      m2f plus_r0l -mult_opp_rl mult_r1l.
  by rewrite coef_opp_poly coef_const_0 m2f -mult_opp_rl mult_r1l.
rewrite !coef_horner_S; case Hij:(i==j)=>//=.
  rewrite coef_add_poly coef_horner_S coef_opp_poly coef_const_S
    opp_r0 plus_r0r //=.
  case: k =>//=[|k]; by rewrite ?coef_poly1_0 ?coef_poly1_S !m2f// Hij.
rewrite coef_opp_poly coef_const_S opp_r0.
case: k =>//=[|k]; by rewrite ?coef_poly1_0 ?coef_poly1_S !m2f// Hij.
Qed.

End Cayley.
