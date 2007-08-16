Add LoadPath "../".
Require Import ssreflect ssrbool funs eqtype ssrnat seq fintype tuple
 indexed_products div groups determinant ring polynomials.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.
(* Delimit Scope local_scope with loc.
Open Scope local_scope. *)

Section Cayley.
Variable R : com_ring.
Variable (n : nat).
Hypothesis (Hn : 0 < n).

Notation "\P[x]" := (poly_com_ring R).
Notation "\M_(n)" := (matrix_ring R Hn).

Notation "\Mp_(n)" := (matrix_ring \P[x] Hn).
Notation "\Pm[x]" := (poly_ring \M_(n)).

Section DegMatrixOfPoly.

Definition deg_mx_of_poly (M : \Mp_(n)) : nat :=
  foldr (fun (x : {(I_(n)*I_(n))%type as eqType}) x0 =>
           maxn x0 (deg_poly (M (fst x) (snd x))))
    0%N (enum (prod_finType I_(n) I_(n))).

Lemma deg_mx_of_polyP: forall (M : \Mp_(n)) i j, 
  deg_poly (M i j) <= deg_mx_of_poly M.
Proof.
move=> M i j.
Admitted.

End DegMatrixOfPoly.


Definition phi (M : \Mp_(n)) : \Pm[x] :=
  foldr (fun k p => 
             (@horner \M_(n) p (matrix_of_fun (fun i j=> coef (M i j) k))))
  (@poly0 \M_(n)) (rev (iota 0 (deg_mx_of_poly M))).

Lemma phi_coeff : forall (M : \Mp_(n)) i j k,
  coef (M i j) k = (coef (phi M) k) i j.
Proof.
move=> M.
rewrite / phi.
elim: (deg_mx_of_poly M)=>//=.

Admitted.

End Cayley.

(*

Fixpoint phi' (p:polynomial \M_(n)) : \M_(x)_(n) :=
match p with seq0 => null_matrix \P[x] n n | 
Adds s p' => (mx_to_mx_of_poly s) +mp (X *smp (phi' p'))
end.

Definition phi (pm : \M_[x]_(n)) : \M_(x)_(n) := phi' pm.

Lemma phi'_eqP : forall p q, eq_P p q -> phi' p = phi' q.
Proof.
elim=>//[|a p Hrec].
  elim=>//=[x s Hrec H].
  move/andP:H=>H; elim: H=> H1 H2; move/eqP:H1=> <-.
  rewrite mx_to_mx_of_poly_0 //= / zeroMP /plusMP.
  move: (@matrix_plus0x \P[x] n n (X *smp phi' s)) => ->.
  rewrite -(Hrec H2); clear H2.
  symmetry; apply: (@matrix_scale_0m \P[x] n n X).
elim=> [|b q Hrec2].
  move=> //= H; move/andP:H=>H; elim: H => H1 H2.
  move/eqP: H1 => <-.
  move: (eqP0_eqP H2) => H3; move: (Hrec _ H3) => H4.
  by rewrite mx_to_mx_of_poly_0 H4 //= / zeroMP /plusMP matrix_plus0x
    / scaleMP matrix_scale_0m.
move=> //= H; move/andP:H=>H; elim: H => H1 H2.
move/eqP: H1 => <-.
congr plusMP.
congr scaleMP.
by apply: Hrec.
Qed.  

Lemma phi'_norm : forall p, phi' (norm p) = phi' p.
Proof.
move=> p; apply: phi'_eqP.
apply: norm_eq.
Qed.

Lemma phi'_plus : forall Ax Bx, phi' (plusP Ax Bx) = (phi' Ax) +mp (phi' Bx).
Proof.
elim=>//[ | a p Hrec1].
  case=>//= *;
    symmetry; apply: (@matrix_plus0x \P[x] n n).
case=> // [|b q].
  rewrite //=.
  set T:=(mx_to_mx_of_poly a +mp X *smp phi' p).
  by rewrite [T +mp _]matrix_plusC (@matrix_plus0x \P[x] n n).
rewrite //=.
move: (Hrec1 q) => //= ->; clear Hrec1.
rewrite / scaleMP / plusMP matrix_scale_distrL.
rewrite  (mx_to_mx_poly_plus a b).
rewrite -!matrix_plusA; congr (_ +m _).
rewrite matrix_plusC -matrix_plusA; congr (_ +m _).
by rewrite matrix_plusC.
Qed.

Lemma phi_plus : forall Ax Bx, phi (Ax +pm Bx) = (phi Ax) +mp (phi Bx).
Proof.
rewrite / phi.
case=>//[A Ha].
case=>//[B Hb].
rewrite phi'_norm.
exact: phi'_plus.
Qed.

Lemma phi'_mult : forall Ax Bx, phi' (multP Ax Bx) = (phi' Ax) *mp (phi' Bx).
Proof.
elim=>//[ | a p Hrec1].
  case=>//= *;
  symmetry; apply: (@matrix_mult0lx \P[x] n).
move=> Bx.
move: (Hrec1 Bx) => H1; clear Hrec1.
rewrite adds_multl //= phi'_plus.
rewrite (@phi'_eqP (multPX (multP p Bx)) (Adds 0 (multP p Bx)));
  last first.
  set q:=  (multP p Bx).
  case: q => //=[|x q]; by rewrite !eq_refl ?eqP_refl.
rewrite //= H1 mx_to_mx_of_poly_0 / plusMP / multMP / scaleMP.
rewrite (@matrix_plus0x \P[x] n n) matrix_distrR; congr (_ +m _); 
  last by rewrite matrix_scaleA.
clear H1.
elim: Bx => //= [|b q Hrec].
  symmetry; apply: (@matrix_mult0rx \P[x] n).
rewrite Hrec matrix_distrL /plusMP /scaleMP; congr (_ +m _);
  first apply: mx_to_mx_poly_mult.
by rewrite matrix_scaleA matrix_scaleC.
Qed.

Lemma phi_mult : forall Ax Bx, phi (Ax *pm Bx) = (phi Ax) *mp (phi Bx).
Proof.
rewrite / phi.
case=>//[A Ha].
case=>//[B Hb].
rewrite phi'_norm.
exact: phi'_mult.
Qed.

Lemma phi_one : (phi \1pm_(n)) = \1mp_(n).
Proof.
rewrite / phi //= / plusMP / scaleMP matrix_scale_0m matrix_plusC matrix_plus0x.
rewrite / mx_to_mx_of_poly.
apply/matrix_eqP; apply: EqMatrix => i j; rewrite !m2f.
case H:(i==j)=> //; apply: eqPP => //=; rewrite / R_to_poly ?eq_refl //.
move: (@one_diff_0 R) => H1; move/eqP: H1=>-> //=.
by rewrite eq_refl.
Qed.

Fixpoint phi'_inv (m :nat) (mx : \M_(x)_(n)) {struct m} : \M_[x]_(n) := 
  if m is (S m') then
      (R_to_polyNorm (head_mxp mx)) +pm (Xpm phi'_inv m' (tail_mxp mx))
  else (PolyNorm (normal0 \M_(n))).

Definition phi_inv (mx : \M_(x)_(n)) : \M_[x]_(n) := 
  phi'_inv (@mx_poly_deg n mx) mx.

Lemma phi_inv_eval : forall Ax,
  (mx_poly_deg Ax) >= 1 -> 
    phi_inv Ax = (R_to_polyNorm (head_mxp Ax)) +pm (Xpm phi_inv (tail_mxp Ax)).
Proof.
move=> Ax.
rewrite / phi_inv.
move: (tail_mxp_deg Ax).
case: (mx_poly_deg Ax) => //=.
move=> n0 H1 H2; congr (_ +pm _).
rewrite H1 -addn1 subn_addl //=.
Qed.

Lemma phi_inv_eval0: forall Ax, 
  (mx_poly_deg Ax = 0%N) ->
    phi_inv Ax = (PolyNorm (normal0 \M_(n))).
Proof.
move=> Ax.
rewrite / phi_inv.
case: (mx_poly_deg Ax) => //=.
Qed.

Lemma phi_inv_evalP : 
forall Ax,
    phi_inv Ax = (R_to_polyNorm (head_mxp Ax)) +pm (Xpm phi_inv (tail_mxp Ax)).
Proof.
move=> Ax.
case: (posnP (mx_poly_deg Ax)) => H1; last apply: phi_inv_eval => //.
rewrite / phi_inv H1 //=.
rewrite tail_mxp_deg H1 //=.
rewrite (head_mxp_deg_0 H1) //=.

Admitted.

Lemma max2_leql : forall m n, m <= max2 m n.
Proof.
move=> m n0.
rewrite / max2.
case H:(m < n0)=>//=.
apply: ltnW => //=.
Qed.

Lemma max2_leqr : forall m n, n <= max2 m n.
Proof.
move=> m n0.
rewrite / max2.
case H:(m < n0)=>//=.
by rewrite leqNgt H.
Qed.

Definition sub_mx_poly (Ax : \M_(x)_(n)) (k :nat) : \M_(n) := 
(*   if k < (mx_poly_deg Ax) then *)
     (matrix_of_fun (fun i j => sub 0 (poly (fun_of_matrix Ax i j)) k)) 
(*  else \0m_(n) *).

Definition poly_mx_poly (Ax : \M_(x)_(n)) : (polynomial \M_(n)) := 
  mkseq (sub_mx_poly Ax) (mx_poly_deg Ax).

Lemma poly_mx_poly_0 : poly_mx_poly (null_matrix \P[x] n n) = seq0.
Proof.
rewrite / poly_mx_poly // mx_poly_deg_0 //=.
Qed.

(* TO ADD TO SEQ PROP *)
Lemma last_iota : forall m n :nat, last 0%N (iota m n) = (n + m - 1%N)%N.
Proof.
elim => //= [|m' Hrec].
  elim => //=[n' _].
  rewrite -(@sub_last _ 0%N 0%N(iota 1 n')) size_iota //=.
  have H: iota 0%N (1%N + n') = (Adds 0%N (iota 1 n')).
    by rewrite //=.
  rewrite -H sub_iota //.

Admitted.


Lemma last_mkseq : forall (d : eqType) (f : nat -> d) (x : d) (m :nat),
       (0<m) -> last x (mkseq f m) = f (pred m).
Proof.
move => d f x.
elim => //= [m' Hrec Hm].
rewrite last_maps.
case H:(m'==0%N); move/eqtype.eqP: H => H.
  rewrite H //=.
by rewrite last_iota subn_addl.
Qed.

Lemma normal_poly_mx_poly :
  forall pm: \M_(x)_(n), normal (poly_mx_poly pm).
Admitted.

Lemma cancel_phi_phi_inv : cancel phi phi_inv.
Proof.
move=> A; rewrite /phi /phi_inv.

Admitted.

Lemma cancel_phi_inv_phi : cancel phi_inv phi.
Proof.
move=> A.
rewrite / phi_inv.

Admitted.

Lemma phi_iso: bijective phi.
Proof.


Admitted.

Lemma phi_inv_plus: forall x y, phi_inv (x +mp y) = (phi_inv x) +pm (phi_inv y).
Proof.
move => x y.
have hx : x = phi(phi_inv x) by rewrite cancel_phi_inv_phi.
have hy : y = phi(phi_inv y) by rewrite cancel_phi_inv_phi.
by rewrite {1}hx {1}hy -phi_plus cancel_phi_phi_inv.
Qed.

Lemma phi_inv_mult: forall x y, phi_inv (x *mp y) = (phi_inv x) *pm (phi_inv y).
Proof.
move => x y.
have hx : x = phi(phi_inv x) by rewrite cancel_phi_inv_phi.
have hy : y = phi(phi_inv y) by rewrite cancel_phi_inv_phi.
by rewrite {1}hx {1}hy -phi_mult cancel_phi_phi_inv.
Qed.

Lemma phi_inv_one : phi_inv \1mp_(n) = \1pm_(n).
Proof.
by rewrite -phi_one cancel_phi_phi_inv.
Qed.

Lemma phi_inv_zero : phi_inv \0mp_(n) = \0pm_(n).
Proof.
Admitted.


(* 
Lemma phi_inv_id_poly: forall p,
  phi_inv (p *smp \1mp_(n)) = poly_to_poly_of_mx Hn p.
*)
End PHI_MORPH.

Definition evalPM : \M_[x]_(n) -> \M_(n) -> \M_(n) := @evalP \M_(n).

Definition PMX : \M_[x]_(n) := multXPM (unitPM Hn).

Lemma binom_pm :
  forall a, poly (PolyNorm (norm_normal (Seq a)) +pm Xpm \1pm_(n)) = (Seq a \1m_(n)).
have H10: (\1m_(n) == (zero (mx_n_type Hn))) = false
  by apply/eqP; exact: (@Rings.one_diff_zero \M_(n)).
move => a; case Ha : (a==\0m_(n)); rewrite ?(eqP Ha) /plusPM /plusPn /poly /unitPM
 /multXPM /multPnX /poly /multPX /norm /norm3.
by rewrite eq_refl /rev /catrev H10 /plusP H10 eq_refl /rev /catrev.
by rewrite Ha eq_refl /rev /catrev H10 /plusP H10 plus0r Ha /rev /catrev.
Qed.

Lemma binom_normal : forall a, normal (R:=mx_n_type Hn) (Seq a \1m_(n)).
have H10: (\1m_(n) == (zero (mx_n_type Hn))) = false
  by apply/eqP; exact: (@Rings.one_diff_zero \M_(n)).
by move => a; rewrite /normal /last H10.
Qed.

Lemma binom_pm' : 
  forall a,  (norm (Seq a) ++ (Xpm \1pm_(n)))%P = (Seq a \1m_(n)).
have H10: (\1m_(n) == (zero (mx_n_type Hn))) = false
  by apply/eqP; exact: (@Rings.one_diff_zero \M_(n)).
by move => a; case Ha :(a==\0m_(n)); rewrite /unitPM ?(eqP Ha) /multXPM /multPnX
  /poly /multPX /norm /norm3 ?Ha eq_refl /rev /catrev H10 /plusP ?plus0r
  ?eq_refl ?H10 ?Ha /rev /catrev.
Qed.

Lemma factor_th_PM : forall (p p1 : \M_[x]_(n)) A,
  (com_coeff p A) -> 
    p = (PolyNorm (norm_normal (R:= mx_n_type Hn) (Seq ((-1) *sm A))) +pm
          Xpm \1pm_(n)) *pm p1 ->
   evalPM p A = \0m_(n).
Proof.
have H10: (\1m_(n) == (zero (mx_n_type Hn))) = false
  by apply/eqP; exact: (@Rings.one_diff_zero \M_(n)).
move=> p p1 A Hcom Heq;  apply: (@factor_th _ _ p1) => //. 
rewrite Heq.
rewrite /multPM /multPn /plusPM /plusPn.
rewrite {1 2 3}/poly. 
apply: (eqP_trans (norm_eq _)). 
rewrite (binom_pm'  (-1 *sm A)). 
apply eqP_mult; last by apply eqP_refl.
rewrite /norm /norm3; case: (-1 *sm A == \0m_(n)); 
  by rewrite H10 /rev /catrev eqP_refl.
Qed.

Lemma poly_to_poly_of_mx_phi_inv :
  forall p, poly_to_poly_of_mx Hn p = phi_inv (p *smp \1mp_(n)).
move => p; case: p => p; elim: p => [ | a p] /=.
rewrite /poly_to_poly_of_mx /=.
rewrite /scaleMP.

Admitted.

Theorem Cayley_Hamilton : forall A : \M_(n), 
  evalPM (poly_to_poly_of_mx Hn ( poly_car A)) A = \0m_(n).
Proof.
move => A.
set pcA := (poly_to_poly_of_mx Hn ( poly_car A)).
pose X_A := ((x_I n) +mp (mx_to_mx_of_poly (matrix_scale (-1) A))).
move: (mult_adugateR_MP X_A) => H1.
have H2: (poly_car A) = det_MP X_A by done.
rewrite -H2 in H1; clear H2.

move: cancel_phi_phi_inv => Hphi1.
move: (bij_can_bij phi_iso Hphi1) => H2.
move: (bij_inj H2) => H3.
have H4: phi_inv (X_A *mp adjugateMP X_A) = phi_inv (poly_car A *smp \1mp_(n)) by rewrite H1.
rewrite phi_inv_mult // in H4.
apply (factor_th_PM  (p:=pcA)(p1:=phi_inv (adjugateMP X_A))).
apply: com_coeff_poly_to_poly_of_mx.
set Hnorm' := norm_normal (R:= mx_n_type Hn) (Seq (-1 *sm A) \1m_(n)).
have Hxa2: X_A = phi (PolyNorm Hnorm').
  rewrite/X_A /phi /= /plusMP matrix_plusC /scaleMP.
  rewrite normal_norm_eq; last by apply: binom_normal.
  congr matrix_plus.
  apply/matrix_eqP; apply EqMatrix => i j; rewrite !m2f.
  case Hij:(i==j).
    have H11: (PolyNorm (poly:=R_to_poly (R0:=R) 1) (R_to_poly_normal (R0:=R) 1)
          =  1).
      rewrite /one /polyNormRings /= /R_to_poly.
    apply/eqPP => /=.
    move/eqP: (@ Rings.one_diff_zero R) => ->. 
    by rewrite /one; rewrite eqP_refl.
  by rewrite H11 mult0r plus0r Rings.onePr.
  have H00: (PolyNorm (poly:=R_to_poly (R0:=R) 0) (R_to_poly_normal (R0:=R) 0)
          =  0).
    rewrite /zero /polyNormRings /= /R_to_poly; apply/eqPP => /=.
    by rewrite (@eq_refl R 0) /=.
  by rewrite H00 mult0r plus0r mult0r.
have Hxa2' : PolyNorm Hnorm' = phi_inv X_A
  by apply:(bij_inj phi_iso); rewrite cancel_phi_inv_phi.
change  (Seq (- 1 *sm A) \1m_(n)) with (poly (PolyNorm Hnorm')).

rewrite /plusPM /plusPn binom_pm'.
rewrite Hxa2' H4 /pcA.
apply: poly_to_poly_of_mx_phi_inv.
Qed.

End MatrixPoly.

*)
