Require Import ssreflect ssrbool ssrfun eqtype ssrnat div.
Require Import fintype finfun ssralg finalg finset fingroup morphism.
Require Import abelian frobenius.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope ring_scope.
Import GRing.Theory.

Section AppendixC.

Variables p q : nat.
Hypothesis Hpq : ~~ (q %| p.-1).

Variable gT : finGroupType.
Variables G P U : {group gT}.
Hypothesis HGPU : [Frobenius G = P ><| U]%g.
Hypothesis Pcard : #|P| = p ^ q.
Hypothesis Ucard : (#|U| * p.-1)%N = (p ^ q).-1.

Variable Q : {group gT}.
Hypothesis HQ : Q \in ('E_q(G))%g.

Variable W2 : {group gT}. 
Hypothesis HW2P : W2 \subset P.
Hypothesis HFpQ : W2 \subset 'N(Q)%g.

Variable y : gT.
Hypothesis HyQ : y \in Q.
Hypothesis HFpUy : W2 \subset 'N(U :^ y)%g.

CoInductive finFieldImage : Type :=
  FinFieldImage (F : finFieldType) (sigma : {morphism P >-> F}%g)
                (tau : gT -> F) (_ : isom P [set: F] sigma)
                (_ : forall p u, p \in P -> u \in U -> 
                                 sigma (p ^ u)%g = tau u * sigma p).

Variable FSigmaTau : finFieldImage.

Let F : finFieldType :=
  let: FinFieldImage F _ _ _ _ := FSigmaTau in F.

Let sigma : {morphism P >-> F}%g :=
  let (F,sigma,_,_,_) as FST
  return {morphism P >-> ((let: FinFieldImage F _ _ _ _ := FST in F)
                          : finFieldType)}%g
  := FSigmaTau in sigma.

Let Fp := <[(1%R : F)]>%g.

Hypothesis HW2Fp : sigma @: W2 = Fp.

(* Lemma appendixC : p <= q. *)

End AppendixC.