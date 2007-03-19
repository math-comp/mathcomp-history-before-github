Require Import ssreflect ssrbool funs eqtype ssrnat seq fintype paths.
Require Import connect div groups group_perm zp.

Section Determinant.

(* used as index set for matrices *)


Variables (d:finType)(R:Type)(plus mult : R -> R -> R)(a:d->d->R).


Definition zerolt2 : 0 < 2 := is_true_true.

Definition z2 := zp_group zerolt2.

Definition zero := zp0 zerolt2.

Definition onelt2 : 1 < 2 := is_true_true.

Definition one : z2 := @EqSig _ (fun m => m < 2) _ onelt2.

Definition bool_to_z2 (b:bool) := if b then zero else one.

Definition z2_to_bool (x:z2) := if x == zero then true else false.

Section sign.

Variable sigma : permType d.

Definition inversion (k l :d) : z2 :=
 bool_to_z2 ((index l (enum d) < index k (enum d)) 
   == (index (sigma l) (enum d) < index (sigma k) (enum d))).

Definition signature :=
  foldr (fun i x => foldr
           (fun j y => 
              add_zp zerolt2
               (if index i (enum d) < index j (enum d) then
                    inversion i j else zero) y)
           x (enum d)) zero (enum d).

End sign.

Lemma foldr_step : forall (A B:eqType)(f: A -> B -> B) x s v,
  foldr f v (Adds x s) = f x (foldr f v s).
done.
Qed.

Theorem all_zeros_foldr :
forall (A B: eqType)(g:A->A->A)(z:A)(f:B->B->A),
  (forall x, g z x = x) -> (forall i j, f i j = z) ->
forall (l1 l2: seq B),
  foldr (fun i a => foldr (fun j b => g (f i j) b) a l1) z l2 == z.
Proof.
move => A B g z f H H0 l0; elim l0 => /=; first by move => l; elim l.
move: l0 => _ x l0 Hl0 l; elim l; first done.
by move: l=>_ y l; move/eqP=>Hl; rewrite /= H0 H Hl; apply: Hl0 (Adds y seq0).
Qed.

Lemma sign_unit : signature (perm_unit d) == zero.
Proof.
rewrite /signature.
apply (all_zeros_foldr (fzp 2) d (add_zp zerolt2) zero
 (fun i j => if index i (FinType.enum d) < index j (FinType.enum d)
               then inversion (perm_unit d) i j else zero)).
by rewrite /zero; apply unit_zp. 
move => i j; rewrite /inversion.
case: (index i (FinType.enum d)<index j (FinType.enum d)); last done.
by rewrite /fun_of_perm !g2f eq_refl. 
Qed.

(* to prove this lemma, I will need to partition the set over which the
sum is performed and show that two parts of the partition can be computed
together, yielding differences that add up to 0, that all other parts of
the partition add to the same value as for the initial permutation, except
for a single value (inversion i j), which is always one.

However, nothing has to be done to define summations over finite sets when
the target type is an arbitrary associative commutative group.
*)
Lemma sign_transpose :
  forall i j s, signature (perm_mul (transperm i j) s) == 
       add_zp zerolt2 one (signature s).
Proof.

Admitted.


