Add LoadPath "../".
Require Import ssreflect ssrbool funs eqtype ssrnat seq fintype tuple
 indexed_products div groups determinantET rings polynomials.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section PolyNorm.
Open Scope rings_scope.
Variable R : ringsType.

Open Scope poly_scope.

Record polyNorm: Type := PolyNorm {
  poly :> (polynomial R);
  normP : normal poly
}.

(* Lemma inj_PolyNorm: injective PolyNorm. *)

Lemma no_normal : forall p: (polynomial R), p <> 00 -> (eqP0 p) -> ~ normal p.
Proof.
move=> p H1 H2.
elim: p H1 H2 => //= [a s Hrec H1 H2].
rewrite / normal //=; apply/idP; apply/eqtype.eqP; clear Hrec H1.
elim: s H2 => //= [|a1 s1 Hrec1 H2]; first (by rewrite andbT=> H1; rewrite -(eqtype.eqP H1)).
move/and3P: H2 => H2; elim: H2=> H2 H3 H4; move/eqtype.eqP: H2 => H2; move/eqtype.eqP: H3 => H3.
rewrite -H2 in Hrec1; rewrite -H3; apply: Hrec1; apply/andP; split=> //=.
Qed.

Lemma eqPP : reflect_eq (fun (p1 p2 : polyNorm) => (eq_P p1 p2)).
Proof.
move; elim=> //= [[|x1 s1] N1] [[|x2 s2] N2] //=; apply: (iffP idP) => //=.
(* 1 *) by move=> _ //=; rewrite /= (eq_irrelevance N1 N2).
(* 2 *) move=> H1; have H2: eqP0 (Adds x2 s2) by rewrite //=.
          have H3: (Adds x2 s2) <> 00 by rewrite //=. 
          by move: (no_normal H3 H2) => *.
(* 3 *) move=> H1; have H2: eqP0 (Adds x1 s1) by rewrite //=.
          have H3: (Adds x1 s1) <> 00 by rewrite //=. 
          by move: (no_normal H3 H2) => *.
(* 4 *) move=> H1 //=; elim: (andP H1); clear H1=> H1 H2; move: (normal_inv N1) (normal_inv N2)=> H3 H4.
          move: (normal_eq H3 H4 H2) => H5; move/eqtype.eqP: H1 => H1.
          move: N1 N2; rewrite H5 H1 => N1 N2; by rewrite /= (eq_irrelevance N1 N2).
(* 5 *) move=> H1; have H2: (eq_P (PolyNorm N1) (PolyNorm N2)) by rewrite H1 eqP_refl.
          move: (normal_eq N1 N2 H2)=> //=.
Qed.

Canonical Structure polyNormET := EqType eqPP.



(* degree of a normal polynomial *)
Definition poly_deg : polyNorm ->  nat := fun x => size (poly x).


Definition plusPn (p1 p2 :polyNorm) : polyNorm := 
  PolyNorm (norm_normal (p1 ++ p2)).

Definition multPn (p1 p2 :polyNorm) : polyNorm := 
  PolyNorm (norm_normal (p1 ** p2)).

Definition multPnX (p1 : polyNorm) : polyNorm :=
  PolyNorm (norm_normal (Xp p1)).

Definition multRPnl (c :R) (p1 : polyNorm) : polyNorm := 
  PolyNorm (norm_normal (c sp p1)).

Definition multRPnr (c :R) (p1 : polyNorm) : polyNorm :=
  PolyNorm (norm_normal (p1 ps c)).

Definition opPn (p1 :polyNorm) : polyNorm :=
  PolyNorm (norm_normal (-- p1)).

Notation "\00n" := (PolyNorm (normal0 R)) (at level 0): local_scope.

Notation "\11n" := (PolyNorm (normal1 R)) (at level 0): local_scope.
Notation "x1 '++n' x2" := (plusPn x1 x2) (at level 50) : local_scope.
Notation "'--n' x" := (opPn x) (at level 10) : local_scope.
Notation "'Xpn' x" := (multPnX x) (at level 40) : local_scope.
Notation "c 'spn' x" := (multRPnl c x) (at level 40) : local_scope.
Notation "x 'pns' c" := (multRPnr c x) (at level 40) : local_scope.
Notation "x1 '**n' x2" := (multPn x1 x2) (at level 50) : local_scope.

(*
Definition tata : polyNorm -> polyNorm.
case=> //=.
case=> //= [Hp|x s Hp].
  exists (@Seq0 R); apply: normal0.
case H:(x==(@zero R)).
*)

Lemma multPn0 : forall p : polyNorm, multPn \00n p = \00n.
Proof. move=> p //=.
rewrite / multPn //=.
(* Set Printing All. *)
congr PolyNorm; apply: eq_irrelevance.
Qed.

Lemma plusPn0l : forall p:  polyNorm, plusPn \00n p = p.
Proof. by move=> p //=; apply/eqPP => //=; apply: norm_eq. Qed.

(* 
Lemma plusPn0r: forall p:  polyNorm, plusPn p \00n = p.
Proof. by move=> p //=; apply/eqPP => //=; rewrite plusP0r; apply: norm_eq. Qed.
*)

Lemma plusPnC : forall p q : polyNorm,  plusPn p q = plusPn q p.
Proof.
move=> p q //=.
by apply/eqPP => //=; rewrite plusPC eqP_refl.
Qed.

Lemma plusPnA: forall p q r :polyNorm,
  plusPn p (plusPn q r) = plusPn (plusPn p q) r.
Proof.
move=> p q r //=.
apply/eqPP => //=.
have H1: (eq_P (norm (plusP p (norm (plusP q r)))) (plusP p (norm (plusP q r))) ).
  apply: norm_eq.
rewrite (eqP_trans H1) //=.
have H2: (eq_P (norm (plusP (norm (plusP p q)) r)) (plusP (norm (plusP p q)) r) ).
  apply: norm_eq.
rewrite eqP_sym //= (eqP_trans H2) //=.
have H3: eq_P (plusP p (norm (plusP q r))) (norm (plusP p (plusP q r))). 
apply: norm_plusP.
rewrite eqP_sym // (eqP_trans H3) //= plusPA eqP_sym //.
rewrite [plusP (plusP p q) r]plusPC plusPC.
apply: norm_plusP.
Qed.

Lemma plusPn0p: forall p :polyNorm, plusPn p (opPn p) = \00n.
Proof.
move => p; apply/eqPP => //=. 
rewrite (eqP_trans (norm_eq _)) // (eqP_trans (norm_plusP _ _)) //
  (eqP_trans (norm_eq _)) // (eqP_trans (plusP0pr _)) //.
Qed.

Lemma multPn1l : forall p : polyNorm, multPn \11n p = p.
Proof.
move=> p //=.
rewrite / multPn // multP1.
apply/eqPP => //=.
apply: norm_eq.
Qed.

Lemma multPn1r : forall p : polyNorm, multPn p \11n = p.
Proof.
move=> p //=.
apply/eqPP => //=.
rewrite multP1r; apply: norm_eq.
Qed.

Lemma multPnA: forall p q r :polyNorm, p **n (q **n r) = (p **n q) **n r.
Proof.
move => p q r;apply/eqPP => //=.
apply: (eqP_trans (norm_eq _)).
apply: (@eqP_trans _ _ (p ** (q ** r))).
  by apply eqP_mult; rewrite ?norm_eq ?eqP_refl.
apply eqP_sym; apply: (eqP_trans (norm_eq _)).
apply: (@eqP_trans _ _ ((p ** q) ** r)).
  by apply eqP_mult; rewrite ?norm_eq ?eqP_refl.
by rewrite multPA eqP_refl.
Qed.

Lemma plusPn_multPnr: forall p q r :polyNorm, 
  multPn (plusPn p q) r = plusPn (multPn p r) (multPn q r).
Proof.
Admitted.

Lemma plusPn_multPnl: forall p q r :polyNorm, 
  multPn p (plusPn q r) = plusPn (multPn p q) (multPn p r).
Proof.
Admitted.

Definition polyNormRings : ringsType.
exists polyNormET \00n \11n plusPn multPn opPn.
(* 1 *) move=> x; apply: plusPn0l.
(* 2 *) move=> x; rewrite plusPnC; apply: plusPn0p.
(* 3 *) apply: (plusPnA).
(* 4 *) apply: plusPnC.
(* 5 *) apply: multPn1l.
(* 6 *) apply: multPn1r.
(* 7 *) apply: multPnA.
(* 8 *) apply: plusPn_multPnl.
(* 9 *) apply: plusPn_multPnr.
rewrite //=.
Defined.

Canonical Structure polyNormRings.


Definition R_to_polyNorm (x :R) : polyNorm := 
  (@PolyNorm (R_to_poly x) (R_to_poly_normal x)).

Lemma inj_R_to_polyNorm : injective R_to_polyNorm.
Proof.
move => x y H.
move/eqPP: H => H.
move/normal_eq: H => H.
rewrite //= in H.
apply: inj_R_to_poly.
apply: H; apply: R_to_poly_normal.
Qed.

Lemma R_to_polyNorm_plus: forall x y, 
  R_to_polyNorm (x + y) = (R_to_polyNorm x) ++n (R_to_polyNorm y).
Proof.
move=> x y.
apply/eqPP.
rewrite / R_to_polyNorm //= (eqP_trans (R_to_poly_plus x y)) // eqP_sym //.
apply: norm_eq.
Qed.

Lemma R_to_polyNorm_mult: forall x y, 
  R_to_polyNorm (x * y) = (R_to_polyNorm x) **n (R_to_polyNorm y).
Proof.
move=> x y.
apply/eqPP.
rewrite / R_to_polyNorm //= (eqP_trans (R_to_poly_mult x y)) // eqP_sym //.
apply: norm_eq.
Qed.

Lemma R_to_polyNorm_iprod :
  forall n (f : I_(n) -> R),
    R_to_polyNorm (@indexed_products.iprod R plus 0 I_(n) (setA I_(n)) f) =
    (@indexed_products.iprod polyNorm plusPn \00n I_(n) (setA I_(n)) (fun j : I_(n) => R_to_polyNorm (f j))).
Proof.
move=> n f.
apply/eqPP.
rewrite / R_to_polyNorm // (eqP_trans (R_to_poly_iprod f)) //.
have H1: eq_P (iprod polyNorm plusPn \00n I_(n) (setA I_(n))
     (fun j : I_(n) =>
      PolyNorm (poly:=R_to_poly (R0:=R) (f j))
        (R_to_poly_normal (R0:=R) (f j))))
     (iprod (@polynomial R) (@plusP R) 00 I_(n) (setA I_(n))
     (fun j : I_(n) =>
      PolyNorm (poly:=R_to_poly (R0:=R) (f j))
        (R_to_poly_normal (R0:=R) (f j)))).
  elim: n f =>// [n Hrec].
  rewrite -addn1 => f.
  set f1:=(fun j : I_(n + 1) =>
      PolyNorm (poly:=R_to_poly (R0:=R) (f j))
        (R_to_poly_normal (R0:=R) (f j))).
  set f2:=(fun j : I_(n + 1) =>
      PolyNorm (poly:=R_to_poly (R0:=R) (f j))
        (R_to_poly_normal (R0:=R) (f j))).
  move: (iprod_rec (@polynomial R) (@plusP R) (Seq0 R) (@plusPA R) (@plusPC R) (@plusP0l R) n f1) => ->.
  move: (iprod_rec polyNorm plusPn \00n plusPnA plusPnC plusPn0l n f2 ) => ->.
  rewrite // (eqP_trans (norm_eq _)) //.
  apply: eqP_plus.
    set ff:=(fun x : I_(n) => f (inj_ord n 1 x)).
    move: (Hrec ff) => -> //.
rewrite //= eqP_refl //.
rewrite eqP_sym // (eqP_trans H1).
Qed.

Lemma R_to_polyNorm0 : R_to_polyNorm 0 = \00n.
Proof.
apply/eqPP.
rewrite / R_to_polyNorm / R_to_poly //= eq_refl //=.
Qed.


Definition head_polyn (p :polyNorm) : R:= (head_poly (poly p)).

(*
Lemma head_polyn_poly: forall p, (eqP (head_polyn p) (head_poly p)).
Proof.
case=>//.
case=> //= [x s Hs].
rewrite / R_to_poly //.
case H:(x==0) => //=; move/eqtype.eqP: H => H; by rewrite ?H eq_refl.
Qed.
*)

Definition tail_polyn : polyNorm -> polyNorm :=
  fun p => (PolyNorm (normal_tail_poly (normP p))).

Lemma headn_tailn_prop : forall p, p = (R_to_polyNorm (head_polyn p)) ++n (Xpn tail_polyn p).
Proof.
move=> p.
apply/eqPP.
rewrite / plusPn //=.
move: (head_tail_prop p) => H1.
move: (norm_eq (plusP (R_to_poly (R0:=R) (head_polyn p)) (norm (multPX (tail_poly p))))) => H2.
rewrite (eqP_trans H1) // eqP_sym // (eqP_trans H2) //; clear H1 H2.
apply: eqP_plus; last (apply: norm_eq).
by rewrite / head_polyn eqP_refl.
Qed.

Lemma head_polyn_plus: 
  forall p q, head_polyn (p ++n q) = (head_polyn p) + (head_polyn q).
Proof.
move=> p q.
rewrite / head_polyn -head_poly_plus.
apply: head_poly_eqP.
rewrite / plusPn //=.
apply: norm_eq.
Qed.

Lemma tail_polyn_plus:
  forall p q, tail_polyn (p ++n q) = (tail_polyn p) ++n (tail_polyn q).
Proof.
move=> p q; apply/eqPP.
rewrite / plusPn //=.
move: (norm_eq (plusP (tail_poly p) (tail_poly q))) => H1.
rewrite eqP_sym // (eqP_trans H1) //; clear H1.
move: (tail_poly_plus p q) => H1.
move: (eqP_sym H1)=> H2; clear H1.
rewrite (eqP_trans H2) //; clear H2.
apply: tail_poly_eqP.
apply: eqP_sym.
apply: norm_eq.
Qed.

Lemma head_polyn_multX :
  forall p, head_polyn (Xpn p) = 0.
Proof.
move=> p.
rewrite / head_polyn -(head_poly_multX p).
rewrite / multPnX //=.
apply: head_poly_eqP.
apply: norm_eq.
Qed.

Lemma tail_polyn_multX :
  forall p, tail_polyn (Xpn p) = p.
Proof.
move=> p; apply/eqPP.
rewrite / multPnX //=.
move: (norm_eq (multPX p)) => H1.
move: (tail_poly_eqP H1) => H2.
rewrite (eqP_trans H2) //.
apply: tail_poly_multX.
Qed.

Lemma head_polyn_multRP :
  forall p c, head_polyn (c spn p) = c * (head_polyn p).
Proof.
move=> p c.
rewrite / head_polyn -(head_poly_multRP).
rewrite / multRPnl //=.
apply: head_poly_eqP.
apply: norm_eq.
Qed.

Lemma tail_polyn_multRP :
  forall p c, tail_polyn (c spn p) = c spn (tail_polyn p).
Proof.
move=> p c; apply/eqPP.
rewrite / multRPnl //=.
move: (norm_eq (multRPl c (tail_poly p))) => H1.
rewrite eqP_sym // (eqP_trans H1) //; clear H1.
move: (norm_eq (multRPl c p)) => H1.
move: (tail_poly_eqP H1) => H2.
rewrite eqP_sym // (eqP_trans H2) //; clear H1 H2.
apply: tail_poly_multRP.
Qed.

Lemma head_polyn_multPR :
  forall p c, head_polyn (p pns c) = (head_polyn p) * c.
Proof. 
move=> p c.
rewrite / head_polyn -(head_poly_multPR).
apply: head_poly_eqP.
apply: norm_eq.
Qed.

Lemma tail_polyn_multPR :
  forall p c, tail_polyn (p pns c) = (tail_polyn p) pns c.
Proof.
move=> p c; apply/eqPP.
rewrite / multRPnr //=.
move: (norm_eq (multRPr c (tail_poly p))) => H1.
rewrite eqP_sym // (eqP_trans H1) //; clear H1.
move: (norm_eq (multRPr c p)) => H1.
move: (tail_poly_eqP H1) => H2.
rewrite eqP_sym // (eqP_trans H2) //; clear H1 H2.
apply: tail_poly_multPR.
Qed.

Lemma head_polyn_mult : 
  forall p q, head_polyn (p **n q) = (head_polyn p) * (head_polyn q).
Proof.
move=> p q.
rewrite / head_polyn -(head_poly_mult).
apply: head_poly_eqP.
apply: norm_eq.
Qed.

Lemma head_polyn_iprod :
  forall n (f : I_(n) -> polyNorm),
  head_polyn (@indexed_products.iprod _ plusPn \00n I_(n) (setA I_(n)) f) =
  (@indexed_products.iprod _ plus 0 I_(n) (setA I_(n)) (fun j : I_(n) => head_polyn (f j))).
Proof.
move=> n f.
rewrite / head_polyn -(head_poly_iprod).
apply: head_poly_eqP.
elim: n f => // [n Hrec ].
rewrite -addn1 => f.
rewrite (iprod_rec (@polynomial R) (@plusP R) (Seq0 R) (@plusPA R) (@plusPC R) (@plusP0l R) n _).
rewrite (iprod_rec polyNorm plusPn \00n plusPnA plusPnC plusPn0l n _).
rewrite // (eqP_trans (norm_eq _)) //.
apply: eqP_plus.
  set ff:=(fun x : I_(n) => f (inj_ord n 1 x)).
  move: (Hrec ff) => -> //.
rewrite //= eqP_refl //.
Qed.

Lemma head_polyn_deg: forall p, poly_deg (R_to_polyNorm (head_polyn p)) <= 1.
Proof.
move=> p.
rewrite / R_to_polyNorm / R_to_poly / poly_deg //=.
case H1:(head_polyn p==0)%EQ => //.
Qed.

Lemma tail_polyn_deg: forall p, poly_deg (tail_polyn p) = poly_deg p - 1.
Proof.
case=>//.
case=>// [ a p H].
by rewrite / poly_deg //= -addn1 subn_addl.
Qed.

End PolyNorm.

Section Cayley.

Section PolyNormComRings.
Variable elt: comRings.

Definition polyNormComRings: comRings.
exists (polyNormRings elt).
move=> x y; apply/eqPP => //=.
rewrite multPC; first by apply: eqP_refl.
move=> x0 Hx0; apply/com_coeffP=> y0 Hy0; apply: multC.
Defined.

(* Canonical Structure polyNormComRings. *)

End PolyNormComRings.

Variable R : comRings.


Open Scope rings_scope.

Notation "\P[x]" := (polyNormComRings R) : local_scope.

Notation "'M_' ( n )" := (matrix R n n)
  (at level 9, m, n at level 50, format "'M_' ( n )") : local_scope.

Section MatrixPoly.

Section MatrixOfPoly.

Open Scope local_scope.

Definition matrix_of_polynomial (n :nat) := (matrix_eqType \P[x] n n).

Notation "'\M_(x)_' ( n )" := (matrix_of_polynomial n)
  (at level 9, m, n at level 50, format "'\M_(x)_' ( n )") : local_scope.


Definition max2 (m n:nat) := if (m < n) then n else m.

(* computes the maximum of x and the elements of s *)

Fixpoint max_seq (d :eqType) (x :nat) (f :d->nat) (s :seq d) {struct s} : nat :=
  if s is (Adds a s') then (if (x < f a) then (max2 (f a) (max_seq (f a) f s')) 
    else (max_seq x f s'))
  else x.

Lemma max_seq_min :  forall (d :eqType) (f:d->nat) s o, o <= max_seq o f s.
Proof.
move=> d f; elim => //= [x s Hrec o].
case H:(o < f x); last by apply: Hrec.
move: (Hrec (f x)) => H2.
apply: (@leq_trans (f x) _ _)=> //.
  by apply: ltnW.
rewrite /max2; case H1:(f x < max_seq (f x) f s); move/idP: H1 => H1 //=.
Qed.

Fixpoint get_max_seq (d :eqType) (x0 :d) (f :d->nat) (s :seq d) {struct s} : d :=
  if s is (Adds a s') then (if (f a == max_seq (f x0) f s) then a 
     else (get_max_seq x0 f s')) 
  else x0.

(* TO ADD TO SSRNAT *)

Lemma leq_ltn_trans : forall n m p, m <= n -> n < p -> m < p.
Proof. by elim=> [|m Hrec] [|n] [|p];  try exact (Hrec n p). Qed.

Lemma ltn_leq_trans : forall n m p, m < n -> n <= p -> m < p.
Proof. by elim=> [|m Hrec] [|n] [|p];  try exact (Hrec n p). Qed.

Lemma max_seq_trans : forall (d :eqType) (f: d->nat) s o p, 
  o <= p -> max_seq o f s <= max_seq p f s.
Proof.
move=> d f; elim => //= [x s Hrec o p Hop].
case H:(p < f x). 
  move/idP: H => H; by rewrite (@leq_ltn_trans p o (f x) Hop H).
case H2:(o < f x); last apply: Hrec=> //.
rewrite / max2.
case H3:(f x < max_seq (f x) f s); first by apply: Hrec; rewrite leqNgt H //=.
apply: (@leq_trans p _ _); first by rewrite leqNgt H.
apply: max_seq_min.
Qed.

Lemma max_seq_max : forall (d :eqType) (f :d->nat) (s :seq d) (o :nat), 
  (forall x, s x -> f x <= max_seq o f s).
Proof.
move=> d f; elim => //= [x s Hrec o xx Hxx].
move/orP: Hxx => Hxx.
  elim: Hxx => H.
  move/eqtype.eqP: H => <-.
  case H:(o < f x); rewrite / max2 //=.
    case H1:(f x < max_seq (f x) f s)=> //=; apply: max_seq_min.
  move/negbT: H => H; rewrite -leqNgt in H.
  apply: (@leq_trans o _ _)=> //; apply: max_seq_min.
case H2:(o < f x); rewrite / max2; last apply: Hrec => //.
move/ltnW: H2 => H2.
move: (max_seq_trans f s H2) => H3.
apply: (@leq_trans (max_seq o f s) _ _) => //; first by apply: Hrec.
case H1:(f x < max_seq (f x) f s) => //=.
apply: (@leq_trans (max_seq (f x) f s) _ _) => //=.
by rewrite leqNgt H1.
Qed.

Lemma max_seq_maxf : forall (d :eqType) (f :d->nat) (s :seq d) (o p:nat),
  (o<=p) -> (forall x, s x ->  f x <= p) -> (max_seq o f s <= p).
Proof.
move=> d f; elim=>//=[x s Hrec o p H1 H2].
case H4:(o < f x) => //; 
  last (by apply: (Hrec o p) => //= y Hy; apply: H2; rewrite /setU1 Hy orbT).
rewrite / max2.
case H3:(f x < max_seq (f x) f s) => //=;
  last (by apply: H2; rewrite / setU1 //= eq_refl orTb).
apply: (Hrec (f x) p); first (by apply: H2; rewrite / setU1 eq_refl orTb).
by move=> y Hy; apply: H2; rewrite / setU1 Hy orbT.
Qed.

Lemma max_seq_trans_eq : 
  forall (d :eqType) (f :d->nat) (s :seq d) a b, 
    a<=b -> b < max_seq b f s -> max_seq a f s = max_seq b f s.
Proof.
move=> d f.
elim=>//=[a b| x s Hrecs a b H1 H2]; first rewrite ltnn //=.
case Hc1:(a < f x) => //=; move/idP: Hc1 => Hc1.
  case Hc2: (b < f x) => //=. rewrite Hc2 in H2.
  rewrite / max2.
  move/idP: Hc2=>Hc2; move/negP: Hc2=>Hc2; rewrite -ltnNge ltnS //= in Hc2.
  case Hc3:(f x < max_seq (f x) f s) => //=; move/idP:Hc3=>Hc3.
    apply: (Hrecs (f x) b) => //=.
  rewrite -(Hrecs (f x) b Hc2 H2).
  move/negP: Hc3=>Hc3; rewrite -ltnNge ltnS //= in Hc3.
  rewrite leq_eqVlt in Hc3; move/orP: Hc3 => Hc3; elim: Hc3=>Hc3;
    first (by apply/eqtype.eqP; rewrite eq_sym).
  move: (Hrecs (f x) b Hc2 H2) => HT1; rewrite -HT1 in H2.
  move: (leq_ltn_trans Hc2 H2) => HT2; move: (ltn_trans HT2 Hc3).
  by rewrite ltnn.
move/negP: Hc1=>Hc1; rewrite -ltnNge ltnS //= in Hc1.
case Hc2: (b < f x) => //=; rewrite Hc2 in H2; last apply: Hrecs => //=.
move/idP:Hc2=>Hc2.
rewrite / max2 in H2; rewrite / max2.
case Hc3:(f x < max_seq (f x) f s) => //=; rewrite Hc3 in H2; 
  move/idP:Hc3=>Hc3.
  congr max_seq.
  move: (leq_ltn_trans H1 Hc2) => H3.
  rewrite leq_eqVlt in Hc1; move/orP: Hc1 => Hc1; elim: Hc1=>Hc1;
    first (by apply/eqtype.eqP; rewrite eq_sym).
  by move: (ltn_trans H3 Hc1); rewrite ltnn.
move: (max_seq_min f s (f x)) => H3.
move/negP: Hc3=>Hc3; rewrite -ltnNge ltnS //= in Hc3.
move: (eqn_leq (f x) (max_seq (f x) f s)) => H4.
rewrite H3 Hc3 //= in H4; move/eqtype.eqP:H4=>H5; clear H3 Hc3.
symmetry.
rewrite H5; apply: Hrecs => //.
move: (max_seq_trans f s Hc1) => H4.
rewrite -H5 in H4; clear H5.
apply: (@ltn_leq_trans (f x) _ _) => //.
apply: (@leq_ltn_trans b _ _) => //.
Qed.

Lemma max_seq_max_rel : 
  forall (d :eqType) (x1 x2 :d) (f :d->nat) (s1 s2 :seq d) (o p:nat),
     (forall i, f (sub x1 s1 i) = (f (sub x2 s2 i) - p)%N) -> (size s1 = size s2) ->
    max_seq (o-p) f s1 = (max_seq o f s2 - p)%N.
Proof.
move=> d x1 x2 f.
elim=>//=[|a1 s1 Hrec].
  case=>//=.
case=>//=[a2 s2 o p H1 H2].
move/eqtype.eqP: H2=> H2; rewrite eqSS in H2; move/eqtype.eqP: H2 => H2.
have H3: forall i, f (sub x1 s1 i) = f (sub x2 s2 i) - p.
  move=> i; apply: (H1 (S i)).
move: (H1 0%N) => //= H4.
move: (Hrec s2 (f a2) p H3 H2) => H5.
move: (Hrec s2 o p H3 H2) => H6.
rewrite H4 H5 H6.
case Hc1:(o - p < f a2 - p) => //=; move/idP: Hc1=> Hc1.
  case Hc2:(o < f a2) => //=; move/idP: Hc2 => Hc2.
    rewrite / max2.
    case Hc3:(f a2 < (max_seq (f a2) f s2)) => //=; move/idP: Hc3 => Hc3.
      case Hc4:(f a2 - p < max_seq (f a2) f s2 -p) => //=; move/idP: Hc4=>Hc4.
      have HT1:(p<f a2) by rewrite -ltn_0sub; 
        apply: (@leq_ltn_trans 0%N _ _) => //;
        apply: (@leq_ltn_trans (o-p) _ _) => //.
      have HT2: (p < max_seq (f a2) f s2) by apply: (@ltn_trans (f a2) _ _) => //.
      move: (ltn_sub2r HT2 Hc3) => HT3.
      move/negP: Hc4=>Hc4; rewrite -ltnNge ltnS //= in Hc4.
      move: (leq_ltn_trans Hc4 HT3); rewrite ltnn //=.
    case Hc4:(f a2 - p < max_seq (f a2) f s2 -p) => //=; move/idP: Hc4=>Hc4.
    have HT1: (p < (f a2)) by rewrite -ltn_0sub;
      apply: (@leq_ltn_trans (o - p) _ _) => //.
    move/negP: Hc3=>Hc3; rewrite -ltnNge ltnS //= in Hc3.
    case Hc5:(max_seq (f a2) f s2 == f a2); move/eqtype.eqP: Hc5 => Hc5;
      rewrite ?Hc5 //=.
    move/eqtype.eqP: Hc5 => Hc5.
    move: (@ltn_neqAle (max_seq (f a2) f s2) (f a2)) => HT4.
    rewrite Hc5 Hc3 //= in HT4; move/idP: HT4=> HT4.
    clear Hc3 Hc5.
    move: (ltn_sub2r HT1 HT4) => HT5.
    move: (ltn_trans Hc4 HT5); rewrite ltnn //=.
  rewrite / max2.
  move/negP: Hc2=>Hc2; rewrite -ltnNge ltnS //= in Hc2.
  move: (max_seq_min f s2 (f a2)) => HT1.
  rewrite leq_eqVlt in Hc2; move/orP: Hc2 => Hc2; elim: Hc2=>Hc2.
    move/eqtype.eqP:Hc2=> Hc2; rewrite Hc2; rewrite Hc2 in HT1.
    move: (leq_sub2r p HT1) => HT2.
    rewrite leq_eqVlt in HT2.
    case Hc3:(o - p < max_seq o f s2 - p)=>//.
    rewrite Hc3 orbF in HT2; by apply/eqtype.eqP.
  have HT2: (p < (f a2)) by rewrite -ltn_0sub;
    apply: (@leq_ltn_trans (o - p) _ _) => //.
  move: (ltn_trans HT2 Hc2) => HT3.
  move: (ltn_sub2r HT3 Hc2) => HT4; move: (ltn_trans Hc1 HT4); rewrite ltnn //=.
case Hc2:(o< f a2) => //=.
move/idP: Hc2 => Hc2.
rewrite / max2.
move/negP: Hc1=>Hc1; rewrite -ltnNge ltnS //= in Hc1.
case Hc3:(f a2 < max_seq (f a2) f s2); move/idP: Hc3=>Hc3.
  congr minus; apply: max_seq_trans_eq => //=.
  apply: ltnW => //.
move: (max_seq_min f s2 (f a2 )) => HT1.
move/negP: Hc3=>Hc3; rewrite -ltnNge ltnS //= in Hc3.
move: (eqn_leq (f a2) (max_seq (f a2) f s2)) => HT2.
rewrite HT1 Hc3 //= in HT2; move/eqtype.eqP:HT2=>HT2.
rewrite HT2.
case Hc4:(f a2 <= p); move/idP: Hc4 => Hc4.
move: (ltnW Hc2)=> HT3.
move: (max_seq_trans f s2 HT3) => HT4.
rewrite HT2 in Hc4.
move: (leq_trans HT4 Hc4)=> HT5.
rewrite -eqn_sub0 in Hc4; rewrite -eqn_sub0 in HT5.
by move/eqtype.eqP: Hc4 => ->; move/eqtype.eqP: HT5 => ->.
move/negP: Hc4=>Hc4; rewrite -ltnNge //= in Hc4.
have HT5: p < f a2 by done.
rewrite -ltn_0sub in Hc4. 
move: (ltn_leq_trans Hc4 Hc1)=> HT3.
rewrite ltn_0sub in HT3.
rewrite -(leq_add2l p) in Hc1.
rewrite !leq_add_sub in Hc1; try by apply: ltnW.
rewrite ltnNge in Hc2; by rewrite Hc1 in Hc2.
Qed.

Lemma get_max_seq_prop : 
  forall (d :eqType) (f :d->nat) (s :seq d) (x0 :d), 
    f (get_max_seq x0 f s) = max_seq (f x0) f s.
Proof.
(*
move=> d f.
elim => // [x s Hrec x0].
rewrite //=.
case H:(f x0 < f x) => //.
  move: (Hrec x0) => H2.
  case H1:( f x == max_seq (f x) f s) => //.
    by move/eqtype.eqP: H1.
  rewrite H2.
  move: (ltnW H) => H3.
  move: (max_seq_trans f s H3) => H4.
*)
Admitted.

(* END MAX SEQ *)

Definition mx_poly_deg (n :nat):  \M_(x)_(n) -> nat := 
  fun x => (@max_seq \P[x] (0%N) (@poly_deg R) (fval (mval x))).

Lemma mx_poly_deg_prop: forall n (A : \M_(x)_(n)) i j, 
  poly_deg (fun_of_matrix A i j) <= mx_poly_deg A.
Proof.
move=> n A i j.
apply: max_seq_max.
unlock fun_of_matrix => //.
rewrite mem_sub // fproof index_mem.
rewrite (@mem_enum (prod_finType I_(n) I_(n)) _) //.
Qed.

Lemma mx_poly_deg_0 : forall n, mx_poly_deg (null_matrix \P[x] n n) = 0%N.
Proof.
move=> n.
rewrite / mx_poly_deg //=.
set ss:= (fval (mval (null_matrix \P[x] n n))).
have Hss: forall x, ss x -> x = 0.
  move=> x Hx //.
  rewrite / ss / null_matrix in Hx.
  unlock matrix_of_fun in Hx.
  unlock fgraph_of_fun in Hx.
  rewrite //= in Hx.
  move/mapsP: Hx => Hx.
  by elim: Hx => _ _ H1.
elim: ss Hss => // [ xx ss Hrec Hss].
rewrite //=.
have H: (@poly_deg R 0 = 0%N) by rewrite //=.
move: (@get_max_seq_prop \P[x] (poly_deg (R:=R)) ss xx) => H1.
case H2:(0 < poly_deg xx); last first.
  apply: Hrec => x Hx; apply: Hss => //=.
  by rewrite / setU1 Hx orbT.
move/idP: H2 => H2.
move: (Hss xx) => //= H3.
rewrite / setU1 eq_refl orTb //= in H3.
move: (H3 is_true_true) => H4; clear H3.
rewrite -H4 in H.
by rewrite H in H2.
Qed.

(* 
Definition get_mx_poly_deg_index (n :nat) (Ax : \M_(x)_(n))
  : (prod_finType I_(n) I_(n)).
move=> n Ax.
pose nx:= get_max_seq (PolyNorm (normal0 R)) (@poly_deg R) (fval (mval Ax)).
index
*)

(* Operation for Matrix of Poly *)

Notation "\00n" := (PolyNorm (normal0 R)) (at level 0): local_scope.
Notation "\11n" := (PolyNorm (normal1 R)) (at level 0): local_scope.
Notation "x1 '++n' x2" := (plusPn x1 x2) (at level 50) : local_scope.
Notation "'--n' x" := (opPn x) (at level 10) : local_scope.
Notation "x1 '**n' x2" := (multPn x1 x2) (at level 50) : local_scope.

Definition plusMP (n :nat) : \M_(x)_(n) -> \M_(x)_(n) -> \M_(x)_(n) :=
 (@matrix_plus \P[x] n n).
Notation "x1 '+mp' x2" := (plusMP x1 x2) (at level 50) : local_scope.

Definition multMP (n :nat) : \M_(x)_(n) -> \M_(x)_(n) -> \M_(x)_(n) :=
  (@matrix_mul \P[x] n n n).
Notation "x1 '*mp' x2" := (multMP x1 x2) (at level 50) : local_scope.

Definition unitMP (n :nat) : \M_(x)_(n) := (unit_matrix \P[x] n).
Notation "'\1mp_' ( n )" := (unitMP n)
  (at level 0, format "'\1mp_' ( n )") : local_scope.

Definition zeroMP (n :nat) : \M_(x)_(n) := (null_matrix \P[x] n n).
Notation "'\0mp_' ( n )" := (zeroMP n)
  (at level 0, format "'\0mp_' ( n )") : local_scope.

Definition scaleMP (n :nat) : \P[x] -> \M_(x)_(n) -> \M_(x)_(n) := 
  (@matrix_scale \P[x] n n).
Notation "x '*smp' A" := (scaleMP x A) (at level 40) : local_scope.

Definition adjugateMP (n :nat) : \M_(x)_(n) -> \M_(x)_(n) :=
   (@adjugate \P[x] n).

(* ---- *)

Lemma normalX : @normal R (Adds 0 (Adds 1 seq0)).
Proof. rewrite / normal //=; apply/eqtype.eqP; apply: one_diff_0. Qed.

Notation "'X'" := (PolyNorm normalX) (at level 0): local_scope.

Definition mx_to_mx_of_poly (n :nat) (A :M_(n)): \M_(x)_( n ) := 
   @matrix_of_fun \P[x] n n (fun i j => (PolyNorm (R_to_poly_normal (A i j)))).

Lemma mx_to_mx_poly_plus : forall n (A B : M_(n)),
  mx_to_mx_of_poly (matrix_plus A B) =
    (@matrix_plus \P[x] n n (mx_to_mx_of_poly A) (mx_to_mx_of_poly B)).
Proof.
move=> n A B.
apply/matrix_eqP; apply: EqMatrix => i j.
rewrite / mx_to_mx_of_poly !m2f //=.
apply: R_to_polyNorm_plus.
Qed.

Lemma mx_to_mx_poly_mult : forall n (A B : M_(n)),
  mx_to_mx_of_poly (matrix_mul A B) =
    (@matrix_mul \P[x] n n n (mx_to_mx_of_poly A) (mx_to_mx_of_poly B)).
Proof.
move=> n A B.
apply/matrix_eqP; apply: EqMatrix => i j.
rewrite / mx_to_mx_of_poly !m2f //.
set ff:= (fun j0 : I_(n) =>
   matrix_of_fun (R0:=\P[x])
     (fun i0 j1 : I_(n) =>
      PolyNorm (poly:=R_to_poly (R0:=R) (A i0 j1))
        (R_to_poly_normal (R0:=R) (A i0 j1))) i j0 *
   matrix_of_fun (R0:=\P[x])
     (fun i0 j1 : I_(n) =>
      PolyNorm (poly:=R_to_poly (R0:=R) (B i0 j1))
        (R_to_poly_normal (R0:=R) (B i0 j1))) j0 j).
set gg:=(fun j0 : I_(n) =>
     (R_to_polyNorm ((A i j0) * (B j0 j)))).
move: (@eq_iprod_f (@polyNorm R) (@plusPn R) (PolyNorm (normal0 R)) I_(n) 
  (setA I_(n)) ff gg) => ->; last first.
  move=> x Hx; rewrite / ff / gg !m2f // R_to_polyNorm_mult //.
clear ff; rewrite / gg; clear gg.
move: (R_to_polyNorm_iprod (fun j0 : I_(n) => A i j0 * B j0 j)) => <- //.
Qed.

Lemma inj_mx_to_mx_of_poly : forall n, injective (@mx_to_mx_of_poly n).
Proof.
move=> n x y H.
apply/matrix_eqP; apply: EqMatrix => i j.
apply: inj_R_to_polyNorm.
rewrite / mx_to_mx_of_poly in H.
unlock matrix_of_fun in H.
move/Matrix_inj: H => // H.
set f1:= (fun x0 : prod_finType I_(n) I_(n) =>
       R_to_polyNorm (R0:=R) (fun_of_matrix x (eq_pi1 x0) (eq_pi2 x0))).
set f2 := (fun x : prod_finType I_(n) I_(n) =>
       R_to_polyNorm (R0:=R) (fun_of_matrix y (eq_pi1 x) (eq_pi2 x))).
move: (g2f f1)=> Hf1.
move: (g2f f2)=> Hf2.
move/fgraphP: H => H.
move: (H (EqPair i j)) => H1.
by rewrite Hf1 Hf2 / f1 / f2 in H1.
Qed.

Lemma mx_to_mx_of_poly_0: forall n, @mx_to_mx_of_poly n (null_matrix R n n) = \0mp_(n).
Proof.
rewrite / mx_to_mx_of_poly=> n.
apply/matrix_eqP; apply: EqMatrix => i j.
rewrite !m2f.
apply: R_to_polyNorm0.
Qed.

Definition x_I n : \M_(x)_(n) := 
  (@matrix_of_fun \P[x] n n (fun i j => (if i == j then X else \00n ))).

Definition det_MP (n :nat) : \M_(x)_(n) -> \P[x] := 
  (@determinant \P[x] n).

Definition poly_car (n :nat) (A :M_(n)) : \P[x] :=
  det_MP ((x_I n) +mp (mx_to_mx_of_poly (matrix_scale (-1) A))).

Lemma mult_adugateR_MP : forall n (A : \M_(x)_(n)), A *mp adjugateMP A = det_MP A *smp \1mp_(n).
Proof.
move=> n A; apply:mult_adugateR.
Qed.

End MatrixOfPoly.


(* --- STOP ----*)
Section PolyOfMatrix.
Open Scope local_scope.
Variable n:nat.
Hypothesis (Hn : 0 < n).

Definition mx_n_type:= (@matrixRings R n Hn).
Notation "\M_(n)" := (mx_n_type) : local_scope.

Definition polynomial_of_matrix := (@polyNorm \M_(n)).

Notation "\M_[x]_(n)" := polynomial_of_matrix : local_scope.

(* Operation for Poly of Matrix *)
Notation "\1m_( n )" := (unit_matrix R n) : local_scope.
Notation "\0m_( n )" := (null_matrix R n n) : local_scope.
Notation "A '+m' B" := (matrix_plus A B) (at level 50) : local_scope.
Notation "x '*sm' A" := (matrix_scale x A) (at level 40) : local_scope.
Notation "A '*m' B" := (matrix_mul A B) (at level 40) : local_scope.

Definition plusPM : \M_[x]_(n) -> \M_[x]_(n) -> \M_[x]_(n) := @plusPn \M_(n).
Notation "x1 '+pm' x2" := (plusPM x1 x2) (at level 50) : local_scope.

Definition multPM : \M_[x]_(n) -> \M_[x]_(n) -> \M_[x]_(n) := @multPn \M_(n).
Notation "x1 '*pm' x2" := (multPM x1 x2) (at level 50) : local_scope.

Definition multXPM : \M_[x]_(n) -> \M_[x]_(n) :=(@multPnX \M_(n)).
Notation "'Xpm' x" := (multXPM x) (at level 40) : local_scope.

Lemma normal_M0 : @normal \M_(n) (@Seq0 \M_(n)).
Proof.
apply: normal0.
Qed.

Definition zeroPM : \M_[x]_(n) := (PolyNorm normal_M0).
Notation "\0pm_(n)" := zeroPM
  (at level 0, format "\0pm_(n)") : local_scope.

Lemma normal_M1 : @normal \M_(n) (Adds\1m_(n) seq0).
Proof.
apply: normal1.
Qed.

Definition unitPM : \M_[x]_(n) := (PolyNorm normal_M1).
Notation "\1pm_(n)" := unitPM
  (at level 0, format "\1pm_(n)") : local_scope.

(* --- *)

Definition R_to_mx (x :R) : \M_[x]_(n) := 
  PolyNorm (norm_normal (R:= mx_n_type) (Seq (x *sm \1m_(n)))).

Fixpoint poly_to_poly_of_mx' (p: seq R) : \M_[x]_(n) :=
  match p with
    seq0 => \0pm_(n)
  | Adds x p' => R_to_mx x +pm Xpm poly_to_poly_of_mx' p'
  end.

Definition poly_to_poly_of_mx (p : \P[x]) : \M_[x]_(n):=
  poly_to_poly_of_mx' (poly p).

Lemma inj_poly_to_poly_of_mx : injective (poly_to_poly_of_mx).
Proof.
Admitted.

Lemma com_coeff_poly_to_poly_of_mx :
  forall p A, com_coeff (poly_to_poly_of_mx p) A.
Proof.
Admitted.

End PolyOfMatrix.
Variable n:nat.
Hypothesis (Hn : 0 < n).

Notation "\M_(n)" := (@mx_n_type n Hn) 
  (at level 9, m, n at level 50, format "\M_(n)") : local_scope.

Notation "\M_(x)_(n)" := (matrix_of_polynomial n)
  (at level 9, m, n at level 50, format "\M_(x)_(n)") : local_scope.
Notation "\M_[x]_(n)" := (@polynomial_of_matrix n Hn)
  (at level 9, m, n at level 50, format "\M_[x]_(n)") : local_scope.

Notation "\1m_( n )" := (unit_matrix R n) : local_scope.
Notation "\0m_( n )" := (null_matrix R n n) : local_scope.
Notation "A '+m' B" := (matrix_plus A B) (at level 50) : local_scope.
Notation "x '*sm' A" := (matrix_scale x A) (at level 40) : local_scope.
Notation "A '*m' B" := (matrix_mul A B) (at level 40) : local_scope.

Notation "x1 '+mp' x2" := (plusMP x1 x2) (at level 50) : local_scope.
Notation "x1 '*mp' x2" := (multMP x1 x2) (at level 50) : local_scope.
Notation "\1mp_(n)" := (unitMP n)
  (at level 0, format "\1mp_(n)") : local_scope.
Notation "x '*smp' A" := (scaleMP x A) (at level 40) : local_scope.
Notation "x1 '+pm' x2" := (plusPM x1 x2) (at level 50) : local_scope.
Notation "x1 '*pm' x2" := (multPM x1 x2) (at level 50) : local_scope.
Notation "\1pm_(n)" := (unitPM n)
  (at level 0, format "\1pm_(n)") : local_scope.
Notation "\0pm_(n)" := (zeroPM n)
  (at level 0, format "\0pm_(n)") : local_scope.

Notation "\0mp_(n)" := (zeroMP n)
  (at level 0, format "\0mp_(n)") : local_scope.

Notation "\0m_(n)" := (null_matrix R n n)
  (at level 0, format "\0m_(n)") : local_scope.

Notation "\1m_(n)" := (unit_matrix R n)
  (at level 0, format "\1m_(n)") : local_scope.

Notation "'Xpm' x" := (multXPM x) (at level 40) : local_scope.

Notation "\1pm_(n)" := (unitPM Hn)
  (at level 0, format "\1pm_(n)") : local_scope.

Notation "\0pm_(n)" := (zeroPM Hn)
  (at level 0, format "\0pm_(n)") : local_scope.

Section PHI_MORPH.

(*
Definition mx_to_mx_poly : \M_(n) -> \M_(x)_(n) := 
  fun A => (@matrix_of_fun \P[x] n n (fun i j => (R_to_polyNorm (fun_of_matrix A i j)))).

*)


Notation "'X'" := (PolyNorm normalX) (at level 0): local_scope.

Definition head_mxp : \M_(x)_(n) -> \M_(n) := 
  fun Ax : \M_(x)_(n) => 
     @matrix_of_fun R _ _ (fun (i j : I_(n)) => head_polyn (fun_of_matrix Ax i j)).

Lemma head_mxp_plus: 
  forall Ax Bx, (head_mxp (Ax +mp Bx)) = (head_mxp Ax +m head_mxp Bx).
Proof.
move=> Ax Bx.
rewrite / head_mxp.
apply/matrix_eqP; apply: EqMatrix => i j; rewrite !m2f.
apply: head_polyn_plus.
Qed.

Lemma head_mxp_scale: 
  forall Ax p, (head_mxp (p *smp Ax)) = ((head_polyn p) *sm head_mxp Ax).
Proof.
move=> Ax p.
rewrite / head_mxp.
apply/matrix_eqP; apply: EqMatrix => i j; rewrite !m2f.
apply: head_polyn_mult.
Qed.

(* not sure this one is used. *)

Lemma head_mxp_scaleR:
  forall Ax c, (head_mxp (((R_to_polyNorm c) *smp Ax)) =
    ( c *sm head_mxp Ax)).
Proof.
move=> Ax c.
rewrite head_mxp_scale  //=; congr (_ *sm _).
rewrite / head_polyn //= / R_to_poly //=.
case H:(c==0)%EQ =>//=.
by apply/eqtype.eqP; rewrite eq_sym H.
Qed.

Lemma head_mxp_mult: 
  forall Ax Bx, (head_mxp (Ax *mp Bx)) = ((head_mxp Ax) *m (head_mxp Bx)).
Proof.
move=> Ax Bx.
rewrite / head_mxp //.
apply/matrix_eqP; apply: EqMatrix => i j; rewrite !m2f //.
rewrite  head_polyn_iprod.
apply: indexed_products.eq_iprod_f.
move=> x Hx //.
rewrite !m2f.
apply: head_polyn_mult.
Qed.


Lemma head_mxp_deg :
  forall Ax, @mx_poly_deg n (mx_to_mx_of_poly (head_mxp Ax)) <= 1.
Proof.
move=> Ax //=.
rewrite / mx_to_mx_of_poly / mx_poly_deg.
unlock matrix_of_fun => /=; unlock fgraph_of_fun => /=.
apply: (@max_seq_maxf _ (@poly_deg R) _ 0 1)=> //=.
move=> x Hx.
move/mapsP: Hx => Hx.
case: Hx => y Hy <-.
rewrite / head_mxp m2f.
apply: head_polyn_deg.
Qed.

Lemma head_mxp_deg_0 :
  forall Ax, @mx_poly_deg n Ax = 0%N ->
    Ax = \0mp_(n).
Proof.
move=> Ax H1.
apply/matrix_eqP; apply: EqMatrix => i j.
rewrite !m2f.
rewrite / mx_poly_deg in H1.
apply/eqPP => //=.
move: (@max_seq_max _ (@poly_deg R) (fval (mval Ax)) 0%N 
  (fun_of_matrix Ax i j)) => H2.
rewrite H1 //= in H2.

Admitted.

Lemma head_mxp_deg_1 :
  forall Ax, @mx_poly_deg n Ax = 1%N ->
    Ax = (mx_to_mx_of_poly (head_mxp Ax)).
Proof.
move=>Ax H1.
rewrite / mx_to_mx_of_poly / head_mxp.
apply/matrix_eqP; apply: EqMatrix => i j.
rewrite !m2f.
rewrite / mx_poly_deg in H1.
apply/eqPP => //=.
move: (@max_seq_max _ (@poly_deg R) (fval (mval Ax)) 0%N 
  (fun_of_matrix Ax i j)) => H2.
rewrite H1 //= in H2.
(*
rewrite / head_polyn / head_poly.
have H3: (fval (mval Ax) (fun_of_matrix Ax i j)).
  
  unlock fun_of_matrix => //=.
  unlock fun_of_fgraph => //=.
*)

Admitted.

Definition tail_mxp : \M_(x)_(n) -> \M_(x)_(n) := 
  fun Ax : \M_(x)_(n) => 
     @matrix_of_fun \P[x] _ _ (fun (i j : I_(n)) => tail_polyn (fun_of_matrix Ax i j)).

Lemma tail_mxp_scaleR:
  forall Ax c, (tail_mxp (((R_to_polyNorm c) *smp Ax)) =
    ( (R_to_polyNorm c) *smp tail_mxp Ax)).
Proof.
move=> Ax c.
rewrite / tail_mxp.
apply/matrix_eqP; apply: EqMatrix => i j; rewrite !m2f.
rewrite / tail_polyn.
apply/eqPP => //=.
Admitted.

Lemma tail_mxp_plus: 
  forall Ax Bx, (tail_mxp (Ax +mp Bx)) = (tail_mxp Ax +mp tail_mxp Bx).
Proof.
move=> Ax Bx.
rewrite / tail_mxp.
apply/matrix_eqP; apply: EqMatrix => i j; rewrite !m2f.
apply: tail_polyn_plus.
Qed.

Lemma tail_mxp_deg :
  forall Ax, @mx_poly_deg n (tail_mxp Ax) = (@mx_poly_deg n Ax) - 1.
Proof.
move=> Ax //=.
rewrite / mx_to_mx_of_poly / mx_poly_deg //=.
have H1: (0 - 1 = 0)%N by done.
rewrite -{1}H1.
apply: (@max_seq_max_rel _ (PolyNorm (normal0 R)) (PolyNorm (normal0 R))) => //=; 
  last by rewrite !fproof.
move=> i //=.
rewrite / tail_mxp //.
unlock matrix_of_fun => //=; unlock fgraph_of_fun => //=.
rewrite -tail_polyn_deg.
clear H1.
congr poly_deg.
have HT1: forall p x j, 
  tail_polyn (sub x p j) = sub (tail_polyn x) (maps (@tail_polyn R) p) j.
  elim=>//=[|x s Hrec x0 j]; first (move=> *; by rewrite !sub_seq0).
  case: j=>//=.
rewrite HT1.
congr sub; last first.
set g:= (fun
     x :(prod_finType I_(n) I_(n)) => (fun_of_matrix Ax (eq_pi1 x) (eq_pi2 x))).
move: (maps_comp (@tail_polyn R) g (prod_enum I_(n) I_(n))) => HT2.
rewrite HT2 / g; clear HT2 g.
congr maps.
set f1 := (fun x : prod_finType I_(n) I_(n) => (fun_of_matrix Ax) (eq_pi1 x) (eq_pi2 x)).
set f2 := (fun x : prod_finType I_(n) I_(n) => (mval Ax) x).
have HT2: forall x : prod_finType I_(n) I_(n), f1 x = f2 x.
  move=> x; rewrite / f1 / f2 //.
  unlock fun_of_matrix => //=.
  unlock fun_of_fgraph => //=.
  congr sub => //=; last first; case:x =>//=.
move: (@eq_maps _ _ f1 f2 HT2) => HT3.
move: (HT3 (prod_enum I_(n) I_(n))) => ->.
rewrite / f2.
clear HT1 f1 f2 HT2 HT3.
set mAx := (mval Ax).
set f1 := (fun x : prod_finType I_(n) I_(n) => mAx x).
have F1: forall (d1: finType)(d2:eqType) (m : fgraphType d1 d2), 
        maps m (enum d1) = fval (m).
  move => d1 d2 m /=.
  move: (g2f m) => H1.
  move/fgraphP: H1 => H1.
  rewrite -{2}H1.
  unlock fgraph_of_fun =>//=.
rewrite -F1 //.
apply/eqPP; rewrite / tail_polyn //.
Qed.

Lemma tail_mxp_deg_eq0 :
  forall Ax, (mx_poly_deg Ax) <= 1 -> tail_mxp Ax = \0mp_(n).
Proof.

Admitted.

Lemma head_tail_mxp_prop : forall Ax,
  Ax = (mx_to_mx_of_poly (head_mxp Ax)) +mp (X *smp (tail_mxp Ax)).
Proof.
move=>Ax.
rewrite / plusMP / mx_to_mx_of_poly.
apply/matrix_eqP; apply: EqMatrix => i j; rewrite !m2f.
move: (headn_tailn_prop (fun_of_matrix Ax i j)) => H1.
rewrite {1}H1; congr plus.
(* Proof this prop in generale case *)
move: (@adds_multl _ 0 (Seq 1) (tail_polyn (fun_of_matrix Ax i j)))=> H2.
rewrite / multPnX / mult //= /multPn //.
apply/eqPP=> //.
apply: (eqP_trans (norm_eq _)); apply: eqP_sym; 
  apply: (eqP_trans (norm_eq _)).
rewrite H2 //.
move: (eqP0_multRPl0 (tail_polyn (fun_of_matrix Ax i j))) => H3.
move: (eqP0_eqP_plusl 
       (multPX (multP (Seq 1) (tail_polyn (fun_of_matrix Ax i j)))) H3) => H4.
apply: (eqP_trans (eqP_sym H4)).
apply: eqP_multPX.
clear H1 H2 H3 H4.
have H1:eq_P (tail_polyn (fun_of_matrix Ax i j)) 
      (tail_poly (poly (fun_of_matrix Ax i j))).
  rewrite //=; apply: eqP_refl.
move: (eqP_mult (eqP_refl (Seq 1)) H1)=> H2.
apply: (eqP_trans H2).
elim: (tail_poly (poly (fun_of_matrix Ax i j))) => // x s Hrec.
rewrite //= mult1l eq_refl andTb !plusP0r eqP_sym //.
apply: (eqP_trans (eqP_sym Hrec)).
clear H1 H2 Hrec.
elim: s =>// x0 s0 Hrec //=.
by rewrite !mult1l eq_refl andTb !plusP0r eqP_sym // eqP_refl.
(* -- *)
Qed.

Lemma head_mxp_scaleX : forall Ax, 
  (head_mxp (X *smp Ax)) = \0m_(n).
Proof.
move=> Ax; rewrite head_mxp_scale.
rewrite / head_polyn //=.
apply: matrix_scale_0.
Qed.

Lemma tail_mxp_scaleX : forall Ax, 
  (tail_mxp (X *smp Ax)) = Ax.
Proof.
move=> Ax //=.
rewrite / tail_mxp.
apply/matrix_eqP; apply: EqMatrix => i j; rewrite !m2f //=.
rewrite -{2}(tail_polyn_multX (fun_of_matrix Ax i j)).
congr tail_polyn.
rewrite / mult //=.
have HT: (forall p, multPn X p = multPnX p).
  case=>//= p Hp.
  rewrite / multPn / multPnX //.
  apply/eqPP => //=.
  apply: (eqP_trans (norm_eq _)); apply: eqP_sym; 
    apply: (eqP_trans (norm_eq _)).
  apply: eqP_sym.
  clear Hp.
  case: p => //= x s.
  case: s => //=; rewrite !mult0l !mult1l ?eq_refl //.
  move=> x0 s; rewrite andTb mult0l plus0l plus0r eq_refl andTb.
  rewrite !plusP0r mult1l.
  apply: (eqP_trans (eqP_sym (eqP0_eqP_plusl _ (eqP0_multRPl0 s)))) => //=.
  rewrite eq_refl andTb.
  clear x x0.
  by elim: s =>//= x s ->; rewrite mult1l eq_refl.
apply: HT.
Qed.

(* TO ADD TO POLY PROP *)

Lemma sub_poly: 
  forall (p q : polynomial R) i, sub 0 (plusP p q) i = (sub 0 p i) + (sub 0 q i).
Proof.
elim => //[|x p Hrec].
  move=> q i; by rewrite //= sub_seq0 plus0l.
elim => //[|y q Hrec2].
  move=> i; by rewrite //= sub_seq0 plus0r.
move=> i.
rewrite //=.
elim: i => //= n0 Hrec3.
Qed.

(* TO ADD TO RING *)

Lemma opp_plus_eqr : forall (R : ringsType) (x1 x2 : R), x1 + x2 = 0 -> x1 = -x2.
Proof.
move=> R0 x1 x2 H.
by apply: (@plusInj R0 x2); rewrite plus_opr plusC.
Qed.


(* *** *)

(*
Fixpoint phi (pm : \M_[x]_(n)) {struct pm} : \M_(x)_(n) :=
 match pm with 
  | PolyNorm ppm H => 
    (if ppm is (Adds a pm') then 
      (mx_to_mx_poly a) +mp (X *smp (phi (PolyNorm (normal_inv (normP pm)))))
    else (null_matrix \P[x] n n))
  end.
    (if poly (pm) is (Adds a pm') then ) 
      else 
*)

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


