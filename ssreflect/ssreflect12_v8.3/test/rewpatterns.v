Require Import ssreflect ssrbool ssrfun eqtype ssrnat.

Lemma test1 : forall x y (f : nat -> nat), f (x + y).+1 = f (y + x.+1).
by move=> x y f; rewrite [_.+1](addnC x.+1).
Qed.

Lemma test2 : forall x y f, x + y + f (y + x) + f (y + x) = x + y + f (y + x) + f (x + y).
by move=> x y f; rewrite {2}[in f _]addnC. 
Qed.

Lemma test2' : forall x y f, true && f (x * (y + x)) = true && f(x * (x + y)).
by move=> x y f; rewrite [in f _](addnC y).
Qed.

Lemma test2'' : forall x y f, f (y + x) + f(y + x) + f(y + x)  = f(x + y) + f(y + x) + f(x + y).
by move=> x y f; rewrite {1 3}[in f _](addnC y).
Qed.

(* patterns catching bound vars not supported *)
Lemma test2_1 : forall x y f, true && (let z := x in f (z * (y + x))) = true && f(x * (x + y)).
by move=> x y f; rewrite [in f _](addnC x). (* put y when bound var will be OK *)
Qed.

Lemma test3 : forall x y f, x + f (x + y) (f (y + x) x) = x + f (x + y) (f (x + y) x).
by move=> x y f; rewrite [in X in (f _ X)](addnC y). 
Qed.

Lemma test3' : forall x y f, x = y -> x + f (x + x) x + f (x + x) x = 
                                      x + f (x + y) x + f (y + x) x.
by move=> x y f E; rewrite {2 3}[in X in (f X _)]E.
Qed.

Lemma test3'' : forall x y f, x = y -> x + f (x + y) x + f (x + y) x = 
                                       x + f (x + y) x + f (y + y) x.
by move=> x y f E; rewrite {2}[in X in (f X _)]E. 
Qed.

Lemma test4 : forall x y f, x = y -> x + f (fun _ : nat => x + x) x + f (fun _ => x + x) x = 
                                     x + f (fun _       => x + y) x + f (fun _ => y + x) x.
by move=> x y f E; rewrite {2 3}[in X in (f X _)]E.
Qed.

Lemma test4' : forall x y f, x = y -> x + f (fun _ _ _ : nat => x + x) x = 
                                      x + f (fun _ _ _       => x + y) x.
by move=> x y f E; rewrite {2}[in X in (f X _)]E.
Qed.

Lemma test5 : forall x y f, x = y -> x + f (y + x) x + f (y + x) x = 
                                     x + f (x + y) x + f (y + x) x.
by move=> x y f E; rewrite {1}[X in (f X _)]addnC. Show Proof.
Qed.

Lemma test3''' : forall x y f, x = y -> x + f (x + y) x + f (x + y) (x + y) = 
                                        x + f (x + y) x + f (y + y) (x + y).
by move=> x y f E; rewrite {1}[in X in (f X X)]E. 
Qed.

Lemma test3'''' : forall x y f, x = y -> x + f (x + y) x + f (x + y) (x + y) = 
                                         x + f (x + y) x + f (y + y) (y + y).
by move=> x y f E; rewrite [in X in (f X X)]E. 
Qed.

Lemma test3x : forall x y f, y+y = x+y -> x + f (x + y) x + f (x + y) (x + y) = 
                                         x + f (x + y) x + f (y + y) (y + y).
by move=> x y f E; rewrite -[X in (f X X)]E. 
Qed.

Lemma test6 : forall x y (f : nat -> nat), f (x + y).+1 = f (y.+1 + x).
by move=> x y f; rewrite [(x + y) in X in (f X)]addnC.
Qed.

Lemma test7 : forall x y (f : nat -> nat), f (x + y).+1 = f (y + x.+1).
by move=> x y f; rewrite [(x.+1 + y) as X in (f X)]addnC.
Qed.
(*
Lemma testM7: forall x y, 0 = x + y -> y = 0 -> x = 0 -> 0 = y + x.
move=> x y E H1 H2; rewrite -[x + y as X in _ = X]E.
*)
(*
Lemma testM7': forall x y, 0 = x + y -> y = 0 -> x = 0 -> 0 = y + x.
move=> x y E H1 H2; rewrite -[y + x as X in _ = X]E.
*)
(*
Lemma testM6: forall x y, 0 = x + y -> y = 0 -> x = 0 -> 0 = y + x.
move=> x y E H1 H2; rewrite -[y + x in X in _ = X]E.
*)
(*
Lemma testM6': forall x y, 0 = x + y -> y = 0 -> x = 0 -> 0 = y + x.
move=> x y E H1 H2; rewrite -[x + y in X in _ = X]E.
*)
(*
Lemma testM5: forall x y, 0 = x + y -> y = 0 -> x = 0 -> 0 = y + x.
move=> x y E H1 H2; rewrite -[in X in _ = X]E.
*)
(*
Lemma testM4: forall x y, 0 = x + y -> y = 0 -> x = 0 -> 0 = y + x.
move=> x y E H1 H2; rewrite -[X in _ = X]E.
*)
(*
Lemma testM3: forall x y, 0 = x + y -> y = 0 -> x = 0 -> 0 = y + x.
move=> x y E H1 H2; rewrite -[in _ = _]E.
*)
(*
Lemma testM2 : forall x y, 0 = x + y -> y = 0 -> x = 0 -> 0 = y + x.
move=> x y E H1 H2; rewrite -[x + y]E.
*)
(*
Lemma testM1 : forall x y, 0 = x + y -> y = 0 -> x = 0 -> 0 = y + x.
move=> x y E H1 H2; rewrite -E.
*)
