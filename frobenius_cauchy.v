
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import fintype.
Require Import connect.
Require Import groups.
Require Import baux.
Require Import action.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section prod.
Variable d1 d2 : finType.
Variables (V:set d1) (W: set d2).

Variable S:set (prod_finType d1 d2).
Hypothesis SsubsetVxW: subset S (prod_set V W).

Definition proj1 (x:d1):set d2:= (fun (y : d2) => S (EqPair x  y)).
Definition proj2 (y:d2):set d1:= (fun (x : d1) => S (EqPair x  y)).

Definition dproj1 (x:d1):= (fun (y : (prod_finType d1 d2)) => S y && (eq_pi1 y == x)).
Definition dproj2 (x:d2):= (fun (y : (prod_finType d1 d2)) => S y && (eq_pi2 y == x)).

Lemma two_way_counting1: (sum V (fun x => (card (proj1 x))))=card S.
Proof.
rewrite (@card_partition d1  (prod_finType d1 d2) V  dproj1 S).
 apply eq_sumf; rewrite /proj1 /dproj1 => x Vx.
 set f :=  (fun (z:d2)  => EqPair x z).
 have finj: injective f; first  by move => a b; rewrite /f;case/pair_eqP ; case /andP=>_; case/eqP.
 set a : (set d2):= (fun y : d2 => S (EqPair (d1:=d1) (d2:=d2) x y)).
 have fdinj: (@dinjective _ _ a  f ).
  by move => x0 y0; rewrite /a /f => _ _ ;case/pair_eqP; case/andP => _ h;  by apply:(eqP h).
 symmetry; have: (fun y : prod_finType d1 d2 => S y && (eq_pi1 y == x)) =1 image f a.
  move => z; case:z => [z1 z2] /=;apply eqb_imp.
   case/andP=> [H3 H2];rewrite /f;apply/imageP;   exists z2 ;rewrite /a;rewrite -(eqP H2) //.
  case/imageP;rewrite /f  => x0 Hx0 H3;apply/andP;split.
  rewrite H3 => //; by apply:Hx0.
 apply/eqP;by case:H3.
 move => H1; rewrite (eq_card H1);apply:card_dimage => z.
 by rewrite /f =>  y hz hy; case/pair_eqP; case/andP => _ Hxy;exact:(eqP Hxy).
rewrite/ partition/disjointn;split.
 by move => u v0 x Hu Hv0; unfold dproj1; case/andP => [H1 H2];case/andP => [H3 H4]; rewrite -(eqP H2) -(eqP H4).
rewrite /cover;apply/andP;split.
 by apply/subsetP => y ; case/setnUP =>  x; case/andP;rewrite /dproj1 => HVx; case/andP => [H1 H2].
apply/subsetP => y Hy;apply/setnUP;rewrite /dproj1;exists (eq_pi1 y );apply/andP;split.
 by move/subsetP: SsubsetVxW;rewrite /sub_set =>  H1;move : (H1 y Hy) ;by case/andP.
by  apply/andP; split.
Qed.

Lemma two_way_counting2: (sum W (fun z => (card (proj2 z))))=card S.
Proof.
rewrite (@card_partition d2  (prod_finType d1 d2) W  dproj2 S).
 apply eq_sumf;rewrite /proj2 /dproj2 => y Wy;set f :=  (fun (z:d1)  => EqPair z y).
 have finj: injective f.
  by move => a b;rewrite /f;case/pair_eqP=> H1;move/andP:H1=> [H2 H3]; apply(eqP H2).
 set a : (set d1):= (fun x : d1 => S (EqPair (d1:=d1) (d2:=d2) x y)).
 have fdinj: (@dinjective _ _ a  f ).
  by move => x0 y0;rewrite /a /f  => _ _ ;case/pair_eqP; case/andP => h _;  by apply:(eqP h).
 symmetry;have: (fun y0 : prod_finType d1 d2 => S y0 && (eq_pi2 y0 == y)) =1 image f a.
    move => z; case:z => [z1 z2] /=;apply eqb_imp.
   case/andP=> [H3 H2];rewrite /f;apply/imageP;   exists z1 ;rewrite /a;rewrite -(eqP H2) //.
  case/imageP;rewrite /f  => x0 Hx0 H3;apply/andP;split.
  rewrite H3 => //; by apply:Hx0.
 apply/eqP;by case:H3.
 move => H1; rewrite (eq_card H1);apply:card_dimage => z.
 rewrite /f =>  x hz hx; case/pair_eqP; case/andP =>  Hxy _;exact:(eqP Hxy).
rewrite /partition /disjointn;split. 
 by move => u v0 x Hu Hv0; rewrite /dproj2;case/andP => [H1 H2];case/andP => [H3 H4]; rewrite -(eqP H2) -(eqP H4).
rewrite/ cover;apply/andP;split.
 by apply/subsetP => y ;case/setnUP  => x; case/andP;rewrite  /dproj1; move => HVx; case/andP => [H1 H2].
apply/subsetP => y Hy;apply/setnUP;rewrite /dproj1;exists (eq_pi2 y );apply/andP;split.
 by move/subsetP: SsubsetVxW; rewrite /sub_set  => H1; move : (H1 y Hy); case/andP.
by  apply/andP; split.
Qed.
 
End prod.

Section Frob_Cauchy.
Variable G: finGroupType.
Open Scope group_scope.

Variable S: finType.
Variable to : S -> G -> S.
Variable H: setType G.
Hypothesis group_H: group H.

Hypothesis to_1: forall x, to x 1 = x.
Hypothesis to_morph : forall (x y:G) z, H x -> H y -> to z (x * y) = to (to z x) y.


(*Fg : x of S, left fixed by g *)
Definition F (g:G): set  S := fun (x:S) =>H g && (to x g == x).
(* pairs (g,x); g in stabilizer of x *)
Definition B:set (prod_finType G S):= fun z => let (g, s) := z in (H g) && (to s g == s).


Lemma subsetBS: subset B  (prod_set (setA G)( setA S)).
Proof.
by apply/subsetP  => z; rewrite /B /=;case z => g s Hgs //=;rewrite /prod_set;apply/andP;split => /=;  rewrite /setA /iset_of_fun // s2f.
Qed.

Lemma card1_B: card B = (sum (setA G) (fun x => card (F x))).
Proof.
by rewrite -(two_way_counting1 subsetBS).
Qed.

Lemma card2_B: card B = (sum (setA S) (fun x => card (stabilizer H to  x))).
Proof.
by rewrite - (two_way_counting2 subsetBS)  /B /proj2 /stabilizer;apply: eq_sumf  =>x _;apply: eq_card =>y;rewrite s2f.
Qed.

Definition indexs := (roots (action.orbit H to)).

Lemma indexs_partition: partition indexs  (action.orbit H to) (setA S).
Proof.
split;first  (move => u v x   Hu1 Hv1 H1 H2;  rewrite -(eqP Hu1) -(eqP Hv1); apply/rootP;first by exact:orbit_csym).
 by apply connect_trans with (x2:=x);rewrite orbit_trans // orbit_sym //.
apply/coverP;split => x Kx; first  by apply /subsetP => y Hy.
exists (root  (action.orbit H to)x);rewrite /indexs roots_root//=; last exact:orbit_csym.
by move: (connect_root (action.orbit H to) x);rewrite orbit_trans  // orbit_sym //.
Qed.

Definition t := (card indexs).

Lemma orbit_eq :forall x y , (action.orbit H to x) y -> (action.orbit H to x) =1(action.orbit H to y).
Proof.
move => x y Hxy z; apply eqb_imp;
 rewrite  orbit_sym // -orbit_trans // => H1;rewrite orbit_sym //.
 move : Hxy ;rewrite -orbit_trans // => Hxy;rewrite -orbit_trans //.
 by apply connect_trans with (x2:=x).
move : Hxy ;rewrite orbit_sym // -orbit_trans // => Hxy; rewrite -orbit_trans //.
by apply connect_trans with (x2:=y).
Qed.

Lemma orbit_eq_card: forall x y , (action.orbit H to x) y -> card (action.orbit H to x) = card (action.orbit H to y).
Proof.
by move => x y Hxy;apply: eq_card;exact: orbit_eq.
Qed.

Lemma indexg_stab_eq: forall x y , (action.orbit H to x) y -> indexg (stabilizer H to  x) H=  indexg (stabilizer H to  y)H.
Proof.
by move => x y Hxy;rewrite -!card_orbit//;exact:orbit_eq_card.
Qed.

Lemma indexg_gt0:  forall (g: finGroupType) h k ,  group (elt:=g) h ->  group (elt:=g) k ->  subset h k -> 0< indexg (elt:=g) h k.
Proof.
move => g h k h_group k_group h_k;move:(ltn_0mul (card h) (indexg (elt:=g) h k)) => H1.
have: ((0<(card h))&&(0 < indexg (elt:=g) h k));last by case/andP.
by rewrite -H1;rewrite LaGrange //;exact:(pos_card_group k_group).
Qed.

Lemma card_stab_eq: forall x y , (action.orbit H to x) y -> card (stabilizer H to  x) = card (stabilizer H to  y).
Proof.
move => x y H1;
set n1:= (stabilizer (G:=G) H (S:=S) to x) ;set n2:=  (stabilizer (G:=G) H (S:=S) to y);
set i1 := indexg  (stabilizer H to  x) H.
apply/eqP;have  hi1: 0< i1.
 apply:  indexg_gt0 => //;try  apply:group_stab => //; apply : subset_stab => //.
rewrite -(eqn_pmul2r (n1:=card n1) (n2:=card n2) hi1)  /i1 LaGrange //;try apply:group_stab => //; try apply:subset_stab => //.
 rewrite ( indexg_stab_eq H1) /n2 LaGrange//; try  apply:group_stab => //; apply : subset_stab => //.
 Qed.

Theorem Frobenius_Cauchy: 
 (sum (setA G) (fun x => card (F x))) = (t * (card H))%N.
Proof.
rewrite -card1_B /t  card2_B.
rewrite (eq_sum (b:= (setnU indexs (action.orbit H to)) ));
 last by apply/subset_eqP;case:indexs_partition => _;case/andP=> [H1 H2];apply/andP;split.
rewrite sum_setnU; last by case:indexs_partition.
rewrite (eq_sumf (N2:= (fun z =>  (card (action.orbit H  to z) * card (stabilizer  H  to z))%N))).
rewrite (eq_sumf (N2:=(fun z => card H))); first by apply:sum_id.
move => x _;rewrite mulnC; move:(LaGrange  (H:= stabilizer H  to x) (K:= H)).
 by rewrite card_orbit//;move=> -> =>//;first apply:group_stab => //;last apply : subset_stab => //.
move => z _;apply: sum_id=> x Hx;apply: card_stab_eq;rewrite orbit_sym //.
Qed.
End  Frob_Cauchy.

