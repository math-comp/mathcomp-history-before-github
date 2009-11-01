(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import paths.
Require Import fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Properties of relations on finite sets, mainly related to  (decidable)   *)
(* transitive closure ("connect"), and with application to the orbits and   *)
(* inverses of injective functions.                                         *)

Section Connect.

Variables (d : finType) (e : rel d).

(* The depth-first search computation of transitive closure.       *)

Fixpoint dfs (n : nat) (a : seq d) (x : d) {struct n} : seq d :=
  if n is S n' then
    if a x then a else foldl (dfs n') (Adds x a) (filter (e x) (enum d))
  else a.

Definition connect : rel d := fun x => dfs (card d) seq0 x.

Lemma subset_dfs : forall n (a b : seq d), subset a (foldl (dfs n) a b).
Proof.
have Hs := @subset_refl d; elim=> [|n Hrec] a b; first by elim: b.
elim: b a => [|x b Hrecb] a //; apply: subset_trans (Hrecb _).
simpl; case (a x); first done; apply: subset_trans (Hrec _ _).
by apply/subsetP => y Ht; apply/orP; right.
Qed.

Inductive dfs_path (x y : d) (a : seq d) : Prop :=
  DfsPath p (_ : path e x p) (_ : last x p = y) (_ : disjoint (Adds x p) a).

Lemma dfsP : forall n x y (a : seq d), card d <= card a + n ->
  negb (a y) -> reflect (dfs_path x y a) (dfs n a x y).
Proof.
elim=> [|n Hrec] x y a Hn Hy /=.
  case/idPn: (max_card (setU1 y a)).
  by rewrite -ltnNge cardU1 (negbET Hy) /= addSn addnC.
case Hx: (a x).
  rewrite (negbET Hy); right; move=> [p Hp Ep Hpa].
  by case/negP: (set0P Hpa x); rewrite /setI /= setU11.
move Da': (Adds x a) => a'; case Hya': (a' y).
  rewrite (subsetP (subset_dfs n _ _) _ Hya'); left.
  exists (Seq0 d); repeat split; last by rewrite disjoint_has /= Hx.
  by rewrite -Da' /= in Hya'; case/setU1P: Hya'; last by rewrite (negbET Hy).
have Hna': card d <= card a' + n.
  by rewrite -Da' /= cardU1 Hx /= add1n addSnnS.
move Db: (filter (e x) (enum d)) => b.
suff Hrec':
    reflect (exists2 x', b x' & dfs_path x' y a') (foldl (dfs n) a' b y).
- apply: {Hrec Hrec'}(iffP Hrec') => [[x' Hx' [p Hp Ep Hpa]] | [p Hp Ep Hpa]].
    rewrite -Da' /= disjoint_sym disjointU1 in Hpa.
    move/andP: Hpa => [Hpx Hpa].
    exists (Adds x' p); try by rewrite //= disjointU1 Hx disjoint_sym.
    by rewrite -Db filter_enum in Hx'; rewrite /= Hx'.
  case/shortenP: Hp Ep => [[|y' p']] /= Hp' Up' Hp'p Dy.
    by rewrite -Da' Dy /= setU11 in Hya'.
  move/andP: Hp' => [Hxy' Hp']; move/andP: Up' => [Hp'x' _].
  exists y'; [ by rewrite -Db filter_enum | exists p'; auto ].
  rewrite disjoint_sym -Da' /= disjointU1 Hp'x' /= disjoint_sym.
  by apply: disjoint_trans Hpa; apply/subsetP => z Hz; apply: setU1r; auto.
elim: b a' Hya' Hna' {a x Da' Db Hy Hn Hx} => [|x b Hrecb] a Hy Hn /=.
  by rewrite Hy; right; case.
have Ha := subset_dfs n a (Seq x); simpl in Ha.
case Hdfs_y: (dfs n a x y).
  rewrite (subsetP (subset_dfs n _ b) _ Hdfs_y); left.
  exists x; [ apply setU11 | apply: (Hrec _); auto; exact (negbT Hy) ].
have Hca := subset_leq_card Ha; rewrite -(leq_add2r n) in Hca.
apply: {Hrecb Hca}(iffP (Hrecb _ Hdfs_y (leq_trans Hn Hca))).
  move=> [x' Hx' [p Hp Ep Hpa]]; rewrite disjoint_sym in Hpa.
  exists x'; [ by apply setU1r | exists p; try split; try done ].
  rewrite disjoint_sym; exact (disjoint_trans Ha Hpa).
move=> [x' Hx' [p Hp Ep Hpa]].
case Hpa': (disjoint (Adds x' p) (dfs n a x)).
  case/orP: Hx' => [Dx'|Hx']; last by exists x'; auto; exists p.
  move: (set0P Hpa x') => Hax'; rewrite /setI /= setU11 /= in Hax'.
  case/negP: (set0P Hpa' x'); rewrite /setI /= setU11 /=.
  apply/(Hrec _ _ _ Hn (negbT Hax')).
  exists (Seq0 d); auto; first by apply: eqP.
  by rewrite disjoint_has /= (eqP Dx') Hax'.
case/(Hrec _ _ _ Hn (negbT Hy)): Hdfs_y.
case/set0Pn: Hpa' => [x'' H]; case/andP: H => [Hpx'' Hdfs_x''].
have Hax'' := set0P Hpa x''; rewrite /setI (Hpx'') /= in Hax''.
case/(Hrec _ _ _ Hn (negbT Hax'')): Hdfs_x'' => [q Hq Eq Hqa].
case/splitPl: p / Hpx'' Hp Ep Hpa => [p1 p2 Ep1].
rewrite path_cat -cat_adds disjoint_cat last_cat Ep1.
move/andP=> [Hp1 Hp2] Ep2; case/andP=> [Hp1a Hp2a]; exists (cat q p2).
- by rewrite path_cat Hq Eq.
- by rewrite last_cat Eq.
by rewrite -cat_adds disjoint_cat Hqa.
Qed.

Lemma connectP : forall x y,
  reflect (exists2 p, path e x p & last x p = y) (connect x y).
Proof.
move=> x y; apply: (iffP (@dfsP _ x _ seq0 _ _)); trivial.
- by rewrite /= card0 leqnn.
- by move=> [p Hp Ep _]; exists p.
by move=> [p Hp Ep]; exists p; try rewrite disjoint_has has_sym.
Qed.

Lemma connect_trans : forall x1 x2 x3,
  connect x1 x2 -> connect x2 x3 -> connect x1 x3.
Proof.
move=> x1 x2 x3; move/connectP=> [p1 Hp1 Ep1]; move/connectP=> [p2 Hp2 Ep2].
by apply/connectP; exists (cat p1 p2); rewrite ?path_cat ?Hp1 ?last_cat Ep1.
Qed.

Lemma connect0 : forall x, connect x x.
Proof. by move=> x; apply/connectP; exists (Seq0 d). Qed.

Lemma eq_connect0 : forall x y : d, x = y -> connect x y.
Proof. move=> x y <-; apply connect0. Qed.

Lemma connect1 : forall x y, e x y -> connect x y.
Proof. by move=> x y Hxy; apply/connectP; exists (Seq y); rewrite /= ?Hxy. Qed.

Lemma path_connect : forall x p, path e x p -> sub_set (Adds x p) (connect x).
Proof.
move=> x p Hp x' Hx'; apply/connectP; case/splitPl: p / Hx' Hp => [p p' Ep].
by rewrite path_cat; case/andP; exists p.
Qed.

Definition repr x := if pick (connect x) is Some y then y else x.

Definition traversal : set d := fun x => repr x == x.

Definition n_comp a := card (setI traversal a).

Lemma connect_repr : forall x, connect x (repr x).
Proof.
by move=> x; rewrite /repr; case: (pickP (connect x)); rewrite // connect0.
Qed.

Definition connect_sym := forall x y, connect x y = connect y x.

Lemma same_connect : connect_sym -> forall x y,
  connect x y -> connect x =1 connect y.
Proof.
by move=> He x y Hxy z; apply/idP/idP; apply: connect_trans; rewrite // He.
Qed.

Lemma same_connect_r : connect_sym -> forall x y,
  connect x y -> forall z, connect z x = connect z y.
Proof. move=> He x y Hxy z; rewrite !(He z); exact: same_connect. Qed.

Lemma reprP : forall x y, connect_sym -> reflect (repr x = repr y) (connect x y).
Proof.
move=> x y He; apply introP=> [Hxy|Hxy Hr].
  rewrite /repr -(eq_pick (same_connect He Hxy)).
  by case: (pickP (connect x)) => [H|Hx] //; case/negP: (Hx y).
case/negP: Hxy; apply: (connect_trans (connect_repr x)).
rewrite Hr He; apply connect_repr.
Qed.

Lemma repr_repr : connect_sym -> forall x, repr (repr x) = repr x.
Proof. move=> He x; symmetry; apply/(reprP _ _ He); exact: connect_repr. Qed.

Lemma traversal_repr : connect_sym -> forall x, traversal (repr x).
Proof. move=> *; apply/eqP; exact: repr_repr. Qed.

Lemma repr_connect : connect_sym -> forall x y, (repr x == repr y) = connect x y.
Proof. move=> He *; exact: sameP eqP (reprP _ _ He). Qed.

End Connect.

Prenex Implicits connect repr traversal n_comp.

Implicit Arguments connectP [d e x y].
Implicit Arguments reprP [d e x y].
Prenex Implicits connectP reprP.

Notation "'fconnect' f" := (connect (set1f f))
  (at level 10, f at level 8) : seq_scope.

Notation "'frepr' f" := (repr (set1f f))
  (at level 10, f at level 8) : seq_scope.

Notation "'ftraversal' f" := (traversal (set1f f))
  (at level 10, f at level 8) : seq_scope.

Notation "'fcard' f" := (n_comp (set1f f))
  (at level 10, f at level 8) : seq_scope.

Section EqConnect.

Variable d : finType.

Lemma connect_sub : forall e e' : rel d,
  sub_rel e (connect e') -> sub_rel (connect e) (connect e').
Proof.
move=> e e' He x y; move/connectP=> [p Hp <-] {y}.
elim: p x Hp => [|y p Hrec] x; [ clear 1; exact: connect0 | simpl ].
move/andP=> [Hx Hp]; exact (connect_trans (He _ _ Hx) (Hrec _ Hp)).
Qed.

Lemma relU_sym : forall e e' : rel d,
  connect_sym e -> connect_sym e' -> connect_sym (relU e e').
Proof.
move=> e e' He He'.
suff Hsub: forall x y, connect (relU e e') x y -> connect (relU e e') y x.
  move=> x y; apply/idP/idP; auto.
move=> x y; move/connectP=> [p Hp <-] {y}.
elim: p x Hp => [|y p Hrec] x /=; first by rewrite connect0.
case/andP=> [Hxp Hp]; apply: {Hrec Hp}(connect_trans (Hrec _ Hp)).
case/orP: Hxp; move/(@connect1 d); rewrite 1?He 1?He';
 apply: connect_sub y x => [x y Hy]; apply connect1; apply/orP; auto.
Qed.

Lemma eq_connect : forall e e' : rel d, e =2 e' -> connect e =2 connect e'.
Proof.
by move=> e e' Ee x y; apply/connectP/connectP=> [] [p Hp Ep]; exists p;
  move: Hp; rewrite // (eq_path Ee).
Qed.

Lemma eq_n_comp : forall e e' : rel d,
  connect e =2 connect e' -> n_comp e =1 n_comp e'.
Proof.
move=> e e' Hee' a; apply: eq_card => x.
by rewrite /setI /traversal /repr (eq_pick (Hee' x)).
Qed.

Lemma eq_n_comp_r : forall a a' : set d, a =1 a' ->
  forall e, n_comp e a = n_comp e a'.
Proof. by move=> a a' Ha e; apply: eq_card => x; rewrite /setI Ha. Qed.

Lemma n_compC : forall a e, n_comp e d = n_comp e a + n_comp e (setC a).
Proof.
move=> a e; rewrite /n_comp cardIC.
by apply: eq_card => x; rewrite /setI andbT.
Qed.

Lemma eq_repr : forall e1 e2 : rel d, e1 =2 e2 -> repr e1 =1 repr e2.
Proof. by move=> e1 e2 He x; rewrite /repr (eq_pick (eq_connect He x)). Qed.

Lemma eq_traversal : forall e1 e2 : rel d, e1 =2 e2 -> traversal e1 =1 traversal e2.
Proof. by move=> e1 e2 He x; rewrite /traversal (eq_repr He). Qed.

End EqConnect.

Section Closure.

Variables (d : finType) (e : rel d).
Hypothesis He : connect_sym e.

Lemma same_connect_rev : connect e =2 connect (fun x y => e y x).
Proof.
suff Hrev: forall e',
    sub_rel (connect (fun x y : d => e' y x)) (fun x y => connect e' y x).
- move=> x y; rewrite He; apply/idP/idP => [Hyx|Hxy]; apply: Hrev; auto.
move=> e' x y; move/connectP=> [p Hp <-] {y}.
elim: p x Hp => [|y p Hrec] x /=; first by rewrite connect0.
move/andP=> [Hyx Hp]; exact (connect_trans (Hrec _ Hp) (connect1 Hyx)).
Qed.

Definition closed (a : set d) := forall x y, e x y -> a x = a y.

Lemma intro_closed : forall a : set d,
  (forall x y, e x y -> a x -> a y) -> closed a.
Proof.
move=> a Ha x y Hxy; apply/idP/idP; first by apply: Ha.
move/connectP: {Hxy}(etrans (He _ _) (connect1 Hxy)) => [p Hp <-].
by elim: p y Hp => [|z p Hrec] y //=; move/andP=> [Hxp Hp]; eauto.
Qed.

Lemma closed_connect : forall a, closed a ->
  forall x y, connect e x y -> a x = a y.
Proof.
move=> a Ha x y; move/connectP=> [p Hp <-] {y}.
elim: p x Hp => [|y p Hrec] x //=; move/andP=> [Hxp Hp].
rewrite (Ha _ _ Hxp); auto.
Qed.

Lemma connect_closed : forall x, closed (connect e x).
Proof. by move=> x y z Hyz; apply (same_connect_r He); apply connect1. Qed.

Lemma setC_closed : forall a, closed a -> closed (setC a).
Proof. by move=> a Ha x y Hxy; rewrite /setC (Ha x y Hxy). Qed.

Definition closure a : set d := fun x => ~~ disjoint (connect e x) a.

Lemma closure_closed : forall a, closed (closure a).
Proof.
move=> a; apply intro_closed; move=> x y Hxy.
by rewrite /closure (eq_disjoint (same_connect He (connect1 Hxy))).
Qed.

Lemma subset_closure : forall a, subset a (closure a).
Proof.
by move=> a; apply/subsetP => x Hx; apply/set0Pn; exists x; rewrite /setI connect0.
Qed.

Lemma n_comp_closure2 : forall x y,
  n_comp e (closure (set2 x y)) = S (~~ connect e x y).
Proof.
move=> x y; rewrite -(repr_connect He) -card2.
apply: eq_card => z; apply/idP/idP.
  case/andP=> Hrz; case/set0Pn=> z'; case/andP=> Hzz' Hxyz'.
  rewrite -(eqP Hrz) (reprP He Hzz').
  by case: (orP Hxyz'); move/eqP=> Dz'; rewrite /set2 Dz' set11 ?orbT.
case/orP; move/eqP=> <-; rewrite /setI (traversal_repr He);
  apply/set0Pn; [ exists x | exists y ];
  by rewrite /setI /set2 set11 ?orbT He connect_repr.
Qed.

Lemma n_comp_connect : forall x, n_comp e (connect e x) = 1.
Proof.
move=> x; rewrite -(card1 (repr e x)); apply: eq_card => [y].
apply/andP/eqP => [[Hy Hxy]|<-]; first by rewrite (reprP He Hxy) (eqP Hy).
by rewrite (traversal_repr He) connect_repr.
Qed.

End Closure.

Notation "'fclosed' f" := (closed (set1f f))
  (at level 10, f at level 8) : seq_scope.

Notation "'fclosure' f" := (closure (set1f f))
  (at level 10, f at level 8) : seq_scope.

Prenex Implicits closed closure.

Section Forbit.

Variables (d : finType) (f : d -> d).

Definition forder x := card (fconnect f x).

Definition forbit x := traject f x (forder x).

Definition findex x y := index y (forbit x).

Definition finv x := iter (pred (forder x)) f x.

Lemma fconnect_iter : forall n x, fconnect f x (iter n f x).
Proof.
move=> n x; apply/connectP.
exists (traject f (f x) n); [ apply fpath_traject | apply last_traject ].
Qed.

Lemma fconnect1 : forall x, fconnect f x (f x).
Proof. exact (fconnect_iter 1). Qed.

Lemma fconnect_finv : forall x, fconnect f x (finv x).
Proof. move=> x; apply: fconnect_iter. Qed.

Lemma forderSpred : forall x, S (pred (forder x)) = forder x.
Proof. by move=> x; rewrite /forder (cardD1 x) connect0. Qed.

Lemma size_forbit : forall x : d, size (forbit x) = forder x.
Proof. move=> x; apply: size_traject. Qed.

Lemma looping_forder : forall x, looping f x (forder x).
Proof.
move=> x; apply/idPn => [Ux]; rewrite -looping_uniq in Ux.
case/negP: (ltnn (forder x)).
move: (card_uniqP Ux); rewrite size_traject; move <-.
apply: subset_leq_card; apply/subsetP=> z.
move/trajectP=> [i _ <-]; apply fconnect_iter.
Qed.

Lemma fconnect_forbit : forall x, fconnect f x =1 forbit x.
Proof.
move=> x y; symmetry; apply/idP/idP.
  move/trajectP=> [i _ <-]; apply fconnect_iter.
move/connectP=> [q' Hq' <-]; move/fpathP: Hq' => [m <-] {q'}.
rewrite last_traject; apply: loopingP; apply looping_forder.
Qed.

Lemma uniq_forbit : forall x, uniq (forbit x).
Proof.
move=> x; rewrite /forbit -forderSpred looping_uniq.
apply/trajectP => [[i Hi Ei]]; set (n := pred (forder x)); case/negP: (ltnn n).
rewrite {1}/n forderSpred /forder -(size_traject f x n).
apply: (leq_trans (subset_leq_card _) (card_size _)); apply/subsetP => [z].
rewrite fconnect_forbit; move/trajectP=> [j Hj <-] {z}; apply/trajectP.
rewrite -forderSpred -/n ltnS leq_eqVlt in Hj.
by case/setU1P: Hj => [Dj|Hj]; [ rewrite Dj; exists i | exists j ].
Qed.

Lemma findex_max : forall x y, fconnect f x y -> findex x y < forder x.
Proof. by move=> x y; rewrite fconnect_forbit -index_mem size_forbit. Qed.

Lemma findex_iter : forall x i, i < forder x -> findex x (iter i f x) = i.
Proof.
move=> x i Hi; rewrite -(sub_traject f Hi); rewrite -size_forbit in Hi.
exact (index_uniq x Hi (uniq_forbit x)).
Qed.

Lemma iter_findex : forall x y, fconnect f x y -> iter (findex x y) f x = y.
Proof.
move=> x y; rewrite fconnect_forbit; move=> Hy.
have Hi := Hy; rewrite -index_mem size_forbit in Hi.
by rewrite -(sub_traject f Hi) -/(forbit x) sub_index.
Qed.

Lemma findex0 : forall x, findex x x = 0.
Proof. by move=> x; rewrite /findex /forbit -forderSpred /= set11. Qed.

Lemma fconnect_invariant : forall (d' : eqType) (k : d -> d'),
  invariant f k =1 d -> forall x y : d, fconnect f x y -> k x = k y.
Proof.
move=> d' k Hk x y; move/iter_findex=> <-; elim: {y}(findex x y) => //= n ->.
exact (esym (eqP (Hk _))).
Qed.

Section Loop.

Variable p : seq d.
Hypotheses (Hp : fcycle f p) (Up : uniq p).
Variable x : d.
Hypothesis Hx : p x.

(* The first lemma does not depend on Up : (uniq p) *)
Lemma fconnect_cycle : fconnect f x =1 p.
Proof.
case/rot_to: Hx => [i q Dp] y; rewrite -(mem_rot i) Dp.
have Hp' := Hp; rewrite -(cycle_rot i) {i}Dp (cycle_path x) /= {1}/set1f in Hp'.
case/andP: Hp'; move/eqP=> Eq Hq; apply/idP/idP; last by apply path_connect.
move/connectP=> [q' Hq' <-] {y}; case/fpathP: Hq' => [m <-] {q'}.
case/fpathP: Hq Eq => [n <-]; rewrite !last_traject f_iter; move=> Dx.
by apply: (@loopingP _ f x (S n) _ m); rewrite /looping Dx /= setU11.
Qed.

Lemma forder_cycle : forder x = size p.
Proof. rewrite -(card_uniqP Up); exact (eq_card fconnect_cycle). Qed.

Lemma forbit_rot_cycle : {i : nat | forbit x = rot i p}.
Proof.
case/rot_to: Hx => [i q Dp]; exists i; rewrite (Dp).
have Hp' := Hp; rewrite -(cycle_rot i) (Dp) (cycle_path x) /= in Hp'.
case/andP: Hp' => _; move/fpathP=> [m Dq].
by rewrite /forbit forder_cycle -(size_rot i) Dp /= -Dq size_traject.
Qed.

End Loop.

Hypothesis Hf : injective f.

Lemma f_finv : cancel finv f.
Proof.
move=> x; move: (looping_forder x) (uniq_forbit x).
rewrite /looping /forbit -forderSpred looping_uniq /= /looping.
set n := pred (forder x); case/setU1P; first done.
move/trajectP=> [i Hi Dnx]; rewrite iter_f -f_iter in Dnx.
by case/trajectP; exists i; last by apply Hf.
Qed.

Lemma finv_f : cancel f finv.
Proof. exact (inj_can_sym f_finv Hf). Qed.

Lemma fin_inj_bij : bijective f.
Proof. exists finv; [ exact finv_f | exact f_finv ]. Qed.

Lemma finv_bij : bijective finv.
Proof. exists f; [ exact f_finv | exact finv_f ]. Qed.

Lemma finv_inj : injective finv.
Proof. exact (can_inj f_finv). Qed.

Lemma fconnect_sym : forall x y, fconnect f x y = fconnect f y x.
Proof.
suff: forall x y, fconnect f x y -> fconnect f y x.
  move=> *; apply/idP/idP; auto.
move=> x y; move/connectP=> [p Hp <-] {y}.
elim: p x Hp => [|y p Hrec] x /=; first by rewrite connect0.
move/andP=> [Hx Hp]; rewrite -(finv_f x) (eqP Hx).
apply: (connect_trans _ (fconnect_finv _)); auto.
Qed.

Lemma iter_forder : forall x, iter (forder x) f x = x.
Proof. move=> x; rewrite -forderSpred -f_iter; exact (f_finv x). Qed.

Lemma iter_finv : forall n x, n <= forder x ->
  iter n finv x = iter (forder x - n) f x.
Proof.
move=> n x Hn; set m := forder x - n.
rewrite -{1}[x]iter_forder -(subnKl Hn) -/m iter_addn.
move: {m x Hn}(iter m f x) => x.
by elim: n => // [n Hrec]; rewrite -iter_f /= finv_f.
Qed.

Lemma cycle_forbit : forall x, fcycle f (forbit x).
Proof.
move=> x; rewrite /forbit -forderSpred (cycle_path x) /= last_traject -/(finv x).
by rewrite fpath_traject /set1f f_finv set11.
Qed.

Lemma fpath_finv : forall x p,
  fpath finv x p = fpath f (last x p) (rev (belast x p)).
Proof.
move=> x p; elim: p x => [|y p Hrec] x //=.
rewrite rev_adds -cats1 path_cat -{}Hrec andbC /= {2 4}/set1f eq_sym andbT.
bool_congr; rewrite -(inj_eq Hf) f_finv.
by case: p => [|z p] //=; rewrite rev_adds last_add_last.
Qed.

Lemma same_fconnect_finv : fconnect finv =2 fconnect f.
Proof.
move=> x y; rewrite (same_connect_rev fconnect_sym).
apply: {x y}eq_connect => x y.
by rewrite /set1f -(inj_eq Hf) f_finv eq_sym.
Qed.

Lemma fcard_finv : fcard finv =1 fcard f.
Proof. exact (eq_n_comp same_fconnect_finv). Qed.

Definition of_forder (n : nat) := preimage forder (set1 n).

Lemma forder_div_card : forall n a,
    subset a (of_forder n) -> fclosed f a -> card a = n * fcard f a.
Proof.
move=> n a Han Ha; rewrite /n_comp mulnC; set b := setI (ftraversal f) a.
have{Han} Hb: forall x, b x -> frepr f x = x /\ forder x = n.
  move=> x; move/andP=> [Hrx Hax]; split; apply/eqP => //.
  rewrite eq_sym; exact: subsetP Han _ Hax.
have{Ha} <-: card (preimage (frepr f) b) = card a.
  apply: eq_card => x; rewrite /preimage /b /setI (traversal_repr fconnect_sym).
  by rewrite -(closed_connect Ha (connect_repr _ x)).
elim: {a b}(S _) {-3}b Hb (ltnSn (card b)) => // [m IHm] b Hb.
case: (pickP b) => [x Hx|Hb0 _]; last first.
  by rewrite (eq_card Hb0) -(@eq_card _ set0) ?card0 // => y; rewrite /preimage.
rewrite (cardD1 x) Hx /=; move/IHm <- => {m IHm}[|y]; last by case/andP; auto.
case: (Hb _ Hx) => [Dx Hex]; rewrite -(cardIC (fconnect f x)); congr addn.
  rewrite -{}Hex /setI /preimage; apply: eq_card => y; rewrite andbC.
  by case Hy: (fconnect f x y); rewrite //= -(reprP fconnect_sym Hy) Dx.
apply: eq_card => y; rewrite /preimage /setI /setD1 /setC; do 2 bool_congr.
by rewrite -(repr_connect fconnect_sym) Dx. 
Qed.

Lemma fclosed1 : forall a, fclosed f a -> forall x, a x = a (f x).
Proof. move=> a Ha x; exact (Ha x _ (set11 _)). Qed.

Lemma same_fconnect1 : forall x, fconnect f x =1 fconnect f (f x).
Proof. move=> x; exact (same_connect fconnect_sym (fconnect1 x)). Qed.

Lemma same_fconnect1_r : forall x y, fconnect f x y = fconnect f x (f y).
Proof. by move=> x y; rewrite /= !(fconnect_sym x) -same_fconnect1. Qed.

End Forbit.

Prenex Implicits forder forbit findex finv of_forder.

Section FinCancel.

Variables (d : finType) (f f' : d -> d).
Hypothesis Ef : cancel f f'.

Let Hf := can_inj Ef.

Lemma finv_eq_can : finv f =1 f'.
Proof. exact (bij_can_eq (fin_inj_bij Hf) (finv_f Hf) Ef). Qed.

Lemma canF_sym : cancel f' f.
Proof. exact (eq_can (f_finv Hf) finv_eq_can (frefl f)). Qed.

Lemma canF_LR : forall x y, x = f' y -> f x = y.
Proof. move=> *; exact: canLR canF_sym. Qed.

Lemma canF_RL : forall x y, f' x = y -> x = f y.
Proof. move=> *; exact: canRL canF_sym. Qed.

Lemma canF_eq : forall x y, (f x == y) = (x == f' y).
Proof. exact (can2_eq Ef canF_sym). Qed.

End FinCancel.

Section FconnectEq.

Variables (d : finType) (f f' : d -> d).
Hypothesis Eff' : f =1 f'.

Lemma eq_set1f : set1f f =2 set1f f'.
Proof. move=> x y; rewrite /set1f Eff'; done. Qed.

Lemma eq_fpath : fpath f =2 fpath f'.
Proof. exact: eq_path eq_set1f. Qed.

Lemma eq_fconnect : fconnect f =2 fconnect f'.
Proof. exact: eq_connect eq_set1f. Qed.

Lemma eq_fcard : fcard f =1 fcard f'.
Proof. exact: eq_n_comp eq_fconnect. Qed.

Lemma eq_finv : finv f =1 finv f'.
Proof.
move=> x; rewrite /finv /forder (eq_card (eq_fconnect x)); exact: (eq_iter Eff').
Qed.

Lemma eq_frepr : frepr f =1 frepr f'.
Proof. exact: eq_repr eq_set1f. Qed.
 
Lemma eq_ftraversal : ftraversal f =1 ftraversal f'.
Proof. exact: eq_traversal eq_set1f. Qed.

Hypothesis Hf : injective f.

Lemma finv_inv : finv (finv f) =1 f.
Proof. exact (finv_eq_can (f_finv Hf)). Qed.

Lemma forder_finv : forder (finv f) =1 forder f.
Proof. move=> x; exact (eq_card (same_fconnect_finv Hf x)). Qed.

Lemma of_forder_finv : of_forder (finv f) =2 of_forder f.
Proof. by move=> n x; rewrite /of_forder /preimage forder_finv. Qed.

End FconnectEq.

Section RelAdjunction.

Variables (d d' : finType) (h : d' -> d) (e : rel d) (e' : rel d').
Hypotheses (He : connect_sym e) (He' : connect_sym e').

Variable a : set d.
Hypothesis Ha : closed e a.

Record rel_adjunction : Type := RelAdjunction
  {rel_unit : forall x,
     a x -> {x' : d' | connect e x (h x')};
   rel_functor : forall x' y',
     a (h x') -> connect e' x' y' = connect e (h x') (h y')}.

Lemma intro_adjunction : forall h' : (forall x, a x -> d'),
   (forall x Hx, connect e x (h (h' x Hx))
             /\ (forall y Hy, e x y -> connect e' (h' x Hx) (h' y Hy))) ->
   (forall x' Hx, connect e' x' (h' (h x') Hx)
             /\ (forall y', e' x' y' -> connect e (h x') (h y'))) ->
  rel_adjunction.
Proof.
move=> h' Hee' He'e; split.
  by move=> y Hy; exists (h' y Hy); case (Hee' _ Hy).
move=> x' z' Hx'; apply/idP/idP.
  move/connectP=> [p Hp <-] {z'}.
  elim: p x' Hp Hx' => [|y' p Hrec] x' /=; first by rewrite connect0.
  move/andP=> [Hx' Hp] Hx.
  move: (He'e _ Hx) => [_ H]; move/H: {H}Hx' => Hxp.
  apply: (connect_trans Hxp (Hrec _ Hp _)).
  by rewrite -(closed_connect Ha Hxp).
case: (He'e _ Hx') => [Hx'x'' _] Hxz; apply: (connect_trans Hx'x'').
move/connectP: Hxz Hx' {Hx'x''} => [p Hp Hpz].
elim: p {x'}(h x') Hp Hpz => [|y' p Hrec] x /=.
  by move=> _ Dx; rewrite Dx; move=> Hz'; rewrite He'; case (He'e _ Hz').
move/andP=> [Hx' Hp] Dz' Hy.
move: (Hy) (Hee' _ Hy) => Hx [_ Hhxy]; rewrite (Ha Hx') in Hy.
apply: connect_trans (Hrec _ Hp Dz' Hy); auto.
Qed.

Lemma strict_adjunction :
  injective h -> subset a (codom h) -> rel_base h e e' (setC a) -> rel_adjunction.
Proof.
rewrite /setC; move=> Hh Hha He'e.
apply intro_adjunction with (fun x Hx => iinv (subsetP Hha x Hx)).
  move=> x Hx; split; first by rewrite f_iinv; apply connect0.
  by move=> y Hy Hxy; apply connect1; rewrite -He'e !f_iinv ?Hx.
move=> x' Hx'; split; first by rewrite (iinv_f Hh); apply connect0.
by move=> y' Hx'y'; apply connect1; rewrite He'e ?Hx'.
Qed.

Lemma adjunction_closed : rel_adjunction -> closed e' (preimage h a).
Proof.
move=> [Hu He'e]; apply (intro_closed He').
move=> x' y'; move/(@connect1 d')=> Hx'y' Hx'.
by rewrite He'e // in Hx'y'; rewrite /preimage -(closed_connect Ha Hx'y').
Qed.

Lemma adjunction_n_comp : rel_adjunction -> n_comp e a = n_comp e' (preimage h a).
Proof.
move=> [Hu He'e]; apply: bij_eq_card; have Hac := closed_connect Ha.
have Hf1: forall w : sub_eqType (setI (traversal e) a),
    let x' := let: EqSig x Hw := w in let: conj _ Hx := andP Hw in
      let: exist x' _ := Hu x Hx in x' in
    setI (traversal e') (preimage h a) (repr e' x').
  move=> [x Hw]; move: (andP Hw) => [_ Hx]; move: (Hu x Hx) => [x' Hxx'].
  move: (connect_repr e' x'); rewrite /setI (traversal_repr He') /preimage /=.
  rewrite He'e /=; last by rewrite -(Hac _ _ Hxx').
  by move=> Hx'rx'; rewrite -(Hac _ _ (connect_trans Hxx' Hx'rx')).
have Hf2: forall w : sub_eqType (setI (traversal e') (preimage h a)),
    setI (traversal e) a (repr e (h (val w))).
  move=> [x' Hw]; case: (andP Hw); rewrite /preimage /= => _ Hx.
  by rewrite /setI (traversal_repr He) -(Hac _ _ (connect_repr e (h x'))).
exists (fun w => @EqSig d' _ _ (Hf1 w)); exists (fun w => @EqSig d _ _ (Hf2 w)).
  move=> [x Hw]; apply: val_inj => /=.
  move: (andP Hw) => [Hrx Hx]; move: (Hu x Hx) => [x' Hx'].
  rewrite -(eqP Hrx); apply: (esym (reprP He (connect_trans Hx' _))).
  rewrite -He'e /preimage -?(Hac _ _ Hx') //; exact: connect_repr.
move=> w; apply: val_inj => /=.
case: (andP (Hf2 w)) => _; case/Hu; case: w => [x' Hw] y' /=.
move: (andP Hw) => [Hrx' Hx'] Hrxy; rewrite /traversal in Hrx'.
rewrite -(eqP Hrx'); apply: (reprP He').
rewrite He' He'e //; exact: connect_trans (connect_repr _ _) Hrxy.
Qed.

End RelAdjunction.

Definition fun_adjunction d d' h f f' := @rel_adjunction d d' h (set1f f) (set1f f').

Implicit Arguments intro_adjunction [d d' h e e' a].
Implicit Arguments adjunction_n_comp [d d' e e' a].

Unset Implicit Arguments.

