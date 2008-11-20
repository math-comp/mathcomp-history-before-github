Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.


Section HilbertSaxiom.

Variables A B C : Prop.

Lemma HilbertS : (A -> B -> C) -> (A -> B) -> A -> C. 
Proof.
move=> hAiBiC hAiB hA.
move: hAiBiC.
apply.
  exact.
by apply: hAiB. 
Qed.

Variables (hAiBiC : A -> B -> C)(hAiB : A -> B)(hA : A).

Lemma HilbertS2 : C. 
Proof.
apply: hAiBiC; first by apply: hA. 
exact: hAiB.
Qed.

Check (hAiB hA).

Lemma HilbertS3 : C. 
Proof. by apply: hAiBiC; last apply: hAiB. Qed.

Lemma HilbertS4 : C. 
Proof. exact:  (hAiBiC _ (hAiB _)). Qed.

End HilbertSaxiom.



Section Symmetric_Conjunction_Disjunction.

Print bool.

Lemma andb_sym : forall A B : bool, A && B -> B && A.
Proof. 
case.
  by case.
by []. 
Qed.

Lemma andb_sym2 : forall A B : bool, A && B -> B && A.
Proof. by case; case. Qed.

Lemma andb_sym3 : forall A B : bool, A && B -> B && A.
Proof. by do 2 case. Qed.

Variables (C D : Prop)(hC : C)(hD : D).
Check (and C D).
Print and.
Check conj.
Check (conj hC hD).

Lemma and_sym : forall A B : Prop, A /\ B -> B /\ A.
Proof. by move=> A1 B []. Qed.

Print or.

Check or_introl.

Lemma or_sym : forall A B : Prop, A \/ B -> B \/ A.
Proof. by move=> A B [hA | hB]; [apply: or_intror | apply: or_introl]. Qed.

Lemma or_sym2 : forall A B : bool, A \/ B -> B \/ A.
Proof. by move=> [] [] AorB; apply/orP; move/orP : AorB. Qed.

End Symmetric_Conjunction_Disjunction.



Section R_sym_trans.

Variables (D : Type)(R : D -> D -> Prop).

Variable R_sym : forall x y, R x y -> R y x.

Variable R_trans : forall x y z, R x y -> R y z -> R x z.

Lemma refl_if : forall x : D, (exists y, R x y) -> R x x.
Proof. 
move=> x [y Rxy]. 
by apply: R_trans _ (R_sym _ y _). 
Qed.

End R_sym_trans.



Section Smullyan_drinker.

Variables (D : Type)(d : D)(P : D -> Prop)(EM : forall A, A \/ ~A).

Lemma drinker : exists x, P x -> forall y, P y.
Proof.
case: (EM (exists y, ~P y))=> [[y notPy]| nonotPy]; first by exists y.
exists d => _ y; case: (EM (P y)) => // notPy.
by case: nonotPy; exists y. 
Qed.

End Smullyan_drinker.



Section Equality.

Variable f : nat -> nat.
Variable foo : f 0 = 0.

Lemma fkk : forall k, k = 0 -> f k = k.
Proof. move=> k k0. by rewrite k0. Qed.

Lemma fkk2 : forall k, k = 0 -> f k = k.
Proof. by move=> k ->. Qed.

Variable f10 : f 1 = f 0.

Lemma ff10 : f (f 1) = 0.
Proof. by rewrite f10 foo. Qed.

Variables (D : eqType)(x y : D).

Lemma eq_prop_bool : x = y -> x == y.
Proof. by move/eqP. Qed.

Lemma eq_bool_prop : x == y -> x = y.
Proof. by move/eqP. Qed.

End Equality.



Section Using_Definition.

Variable U : Type.

Definition ens := U -> Prop.

Definition sousens (A B : ens) := forall x, A x -> B x.

Definition transitive (T : Type)(R : T -> T -> Prop) :=
 forall x y z, R x y -> R y z -> R x z.

Lemma sousens_trans : transitive ens sousens.
Proof.
rewrite /transitive /sousens => x y z sousxy sousyz t xt.
by apply: sousyz; apply: sousxy.
Qed.

Lemma sousens_trans2 : transitive ens sousens.
Proof.
move=> x y z sousxy sousyz t.
by move/sousxy; move/sousyz. 
Qed.

End Using_Definition.
 

Section Basic_ssrnat.


Lemma three : S (S (S O)) = 3 /\ 3 = 0.+1.+1.+1. 
Proof. by []. Qed.

Lemma concrete_plus : plus 16 64 = 80.
Proof. (*simpl.*) by []. Qed.

Lemma concrete_addn : 16 + 64 = 80.
Proof. (*simpl.*)  by []. Qed.

Lemma concrete_le : le 1 3.
Proof. by apply: (Le.le_trans _ 2); apply: Le.le_n_Sn. Qed.

Lemma concrete_big_le : le 16 64.
Proof. by auto 47 with arith. Qed.

Lemma concrete_big_leq : 0 <= 51.
Proof. by []. Qed.

Lemma semi_concrete_leq : forall n m, n <= m -> 51 + n <= 51 + m. 
Proof. by []. Qed.

Lemma concrete_arith : (50 < 100) && (3 + 4 < 3 * 4 <= 17 - 2).
Proof. by []. Qed.

Lemma plus_com : forall m1 n1, n1 + m1 = m1 + n1.
Proof.
by elim=> [| n co m]; [elim | rewrite -[n.+1 + m]/(n + m).+1 -co; elim: m].
Qed.

End Basic_ssrnat.


Section Euclidean_division.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition edivn_rec d := fix loop (m q : nat) {struct m} :=
  if m - d is m'.+1 then loop m' q.+1 else (q, m).

Definition edivn m d := if d is d'.+1 then edivn_rec d' m 0 else (0, m).

CoInductive edivn_spec (m d : nat) : nat * nat -> Type :=
  EdivnSpec q r of m = q * d + r & (d > 0) ==> (r < d) : edivn_spec m d (q, r).

Lemma edivnP : forall m d, edivn_spec m d (edivn m d).
Proof.
move=> m [|d] //=; rewrite -{1}[m]/(0 * d.+1 + m).
elim: m {-2}m 0 (leqnn m) => [|n IHn] [|m] q //=; rewrite ltnS => le_mn.
rewrite subn_if_gt; case: ltnP => // le_dm.
rewrite -{1}(subnK le_dm) -addSn addnA -mulSnr; apply: IHn.
apply: leq_trans le_mn; exact: leq_subr.
Qed.

Lemma edivn_eq : forall d q r, r < d -> edivn (q * d + r) d = (q, r).
Proof.
move=> d q r lt_rd; have d_pos: 0 < d by exact: leq_trans lt_rd.
case: edivnP lt_rd => q' r'; rewrite d_pos /=.
wlog: q q' r r' / q <= q' by case (ltnP q q'); last symmetry; eauto.
rewrite leq_eqVlt; case: eqP => [-> _|_] /=; first by move/addn_injl->.
rewrite -(leq_pmul2r d_pos); move/leq_add=> Hqr Eqr _; move/Hqr {Hqr}.
by rewrite addnS ltnNge mulSn -addnA Eqr addnCA addnA leq_addr.
Qed.

CoInductive edivn_spec_right : nat -> nat -> nat * nat -> Type :=
  EdivnSpec_right m d q r of m = q * d + r & (d > 0) ==> (r < d) : 
  edivn_spec_right m d (q, r).

CoInductive edivn_spec_left (m d : nat)(qr : nat * nat) : Type :=
EdivnSpec_left of m = (fst qr) * d + (snd qr) & (d > 0) ==> (snd qr < d) :
   edivn_spec_left m d qr.


Lemma edivnP_left : forall m d, edivn_spec_left m d (edivn m d).
Proof.
move=> m [|d] //=; rewrite -{1}[m]/(0 * d.+1 + m).
elim: m {-2}m 0 (leqnn m) => [|n IHn] [|m] q //=; rewrite ltnS => le_mn.
rewrite subn_if_gt; case: ltnP => // le_dm.
rewrite -{1}(subnK le_dm) -addSn addnA -mulSnr; apply: IHn.
apply: leq_trans le_mn; exact: leq_subr.
Qed.

Lemma edivnP_right : forall m d, edivn_spec_right m d (edivn m d).
Proof.
move=> m [|d] //=; rewrite -{1}[m]/(0 * d.+1 + m).
elim: m {-2}m 0 (leqnn m) => [|n IHn] [|m] q //=; rewrite ltnS => le_mn.
rewrite subn_if_gt; case: ltnP => // le_dm.
rewrite -{1}(subnK le_dm) -addSn addnA -mulSnr; apply: IHn.
apply: leq_trans le_mn; exact: leq_subr.
Qed.

Lemma edivn_eq_right : forall d q r, r < d -> edivn (q * d + r) d = (q, r).
Proof.
move=> d q r lt_rd; have d_pos: 0 < d by exact: leq_trans lt_rd.
set m := q * d + r; have: m = q * d + r by [].
set d' := d; have: d' = d by [].
case: (edivnP_right m d') => {m d'} m d' q' r' -> lt_r'd' d'd q'd'r'.
move: q'd'r' lt_r'd' lt_rd; rewrite d'd d_pos {d'd m} /=.
wlog: q q' r r' / q <= q' by case (ltnP q q'); last symmetry; eauto.
rewrite leq_eqVlt; case: eqP => [-> _|_] /=; first by move/addn_injl->.
rewrite -(leq_pmul2r d_pos); move/leq_add=> Hqr Eqr _; move/Hqr {Hqr}.
by rewrite addnS ltnNge mulSn -addnA -Eqr addnCA addnA leq_addr.
Qed.


Lemma edivn_eq_left : forall d q r, r < d -> edivn (q * d + r) d = (q, r).
Proof.
move=> d q r lt_rd; have d_pos: 0 < d by exact: leq_trans lt_rd.
case: (edivnP_left (q * d + r) d) lt_rd; rewrite d_pos /=.
set q':= (edivn (q * d + r) d).1; set r':= (edivn (q * d + r) d).2.
rewrite (surjective_pairing (edivn (q * d + r) d)) -/q' -/r'. 
wlog: q r q' r' / q <= q' by case (ltnP q q'); last symmetry; eauto.
rewrite leq_eqVlt; case: eqP => [-> _|_] /=; first by move/addn_injl->.
rewrite -(leq_pmul2r d_pos); move/leq_add=> Hqr Eqr _; move/Hqr {Hqr}.
by rewrite addnS ltnNge mulSn -addnA Eqr addnCA addnA leq_addr.
Qed.


End Euclidean_division.