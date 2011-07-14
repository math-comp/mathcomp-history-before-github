Require Import ssreflect ssrbool ssrfun eqtype ssrnat div.
Require Import fintype finfun ssralg finalg finset fingroup abelian morphism.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope ring_scope.
Import GRing.Theory.

Section AppendixC.

Variables p q : nat.
Hypothesis Hpq : ~~ (q %| p.-1).

Variable G : finGroupType.
Variables P U : {group G}.

CoInductive finFieldImage : Type :=
  FinFieldImage : forall (F : finFieldType) (sigma : {morphism P >-> F}%g)
                         (tau : G -> F), #|F| = p^q -> isom P [set: F] sigma ->
                         (#|tau @: U| * p.-1)%N = (p ^ q).-1 ->
                         (forall p u, p \in P -> u \in U -> 
                                      sigma (p ^ u)%g = tau u * sigma p) -> 
                         finFieldImage.

Variable FSigmaTau : finFieldImage.

Let F : finFieldType :=
  let: FinFieldImage F _ _ _ _ _ _ := FSigmaTau in F.

Let sigma : {morphism P >-> F}%g :=
  let (F,sigma,_,_,_,_,_) as FST
  return {morphism P >-> ((let: FinFieldImage F _ _ _ _ _ _ := FST in F)
                          : finFieldType)}%g
  := FSigmaTau in sigma.

Let Fp := <[(1%R : F)]>%g.

Let W2 := sigma @^-1: Fp.

Variable Q : {group G}.
Hypothesis HQPU : Q \in ('E_q(P <*> U))%g.
Hypothesis HFpQ : W2 \subset 'N(Q)%g.

Variable y : G.
Hypothesis HyQ : y \in Q.
Hypothesis HFpUy : W2 \subset 'N(U :^ y)%g.

(* Lemma appendixC : p <= q. *)

End AppendixC.