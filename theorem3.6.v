Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import prime fintype paths finfun ssralg bigops finset.
Require Import groups morphisms normal commutators.
Require Import cyclic center pgroups sylow dirprod schurzass hall. 
Require Import coprime_act nilpotent.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.
Section fitting.
Variable T : finGroupType.
(* waiting for the actual definition *)
Axiom fitting: {set T} -> {set T}.
End fitting.

Notation "''F' ( G )" := (fitting G)
  (at level 8, format "''F' ( G )") : group_scope.

Section three_dot_six.
Variable T : finGroupType.
Variables H R R0 G: {group T}.
Hypothesis solvG: solvable G.
Hypothesis oddG: odd #|G|.
Hypothesis nH: H <| G.
Hypothesis hallG: coprime #|G| #|G : H|.
Hypothesis HR: G = H * R :> (set _).
Hypothesis trivHR: trivg (H :&: R). 
Hypothesis subR0R: R0 \subset R.
Hypothesis primeR0: prime #|R0|.
Hypothesis zg: forall V p, sylow p V 'C_H(R0) -> cyclic V.

(* theorem 3.6 
Theorem p_length_1_comm: forall p, prime p -> 
  p_length_1 p [~: H, R].
*)

Section by_contradiction.
Variable p: nat.
Hypothesis negpl1: ~ p_length_1 p [~: H, R].

(* lemma 3.6 *)
Axiom eqHcommHK: H = [~: H, R] :> (set _).

(* lemma 3.7 *)
Axiom pl1quotient: forall X: {group T}, 
  X <| H -> ~ trivg X -> R \subset 'N(X) ->
  p_length_1 p (H / X).

(* lemma 3.8 *)
Axiom triv_Osub: trivg 'O_[~ p](H).

Definition V := 'F(H). 

(* lemma 3.9 *)
Axiom eq_F_Osub: V = 'O_[p](H) /\ elementary_abelian V.

(* lemma 3.10 *)
Axiom centV: 'C_H(V) = V.

(* lemma 3.11  ?? *)

Definition U := coset_of V @*^-1 'F(H / V).
(* lemma 3.12 *)

(* lemma 3.12 *)
Axiom K: {group T}.
Axiom VK: V * K = U.
Axiom trivVK: trivg (V :&: K). 
Axiom RnormK: R \subset 'N(K).

Axiom eqH: H = U * 'N_H(K) :> (set _)  /\ H = V * 'N_H(K) :> (set _).

(* lemma 3.13 *)
Axiom P: {group T}.
Axiom sylowP: sylow p P 'N_H(K).
Axiom RnormP: R \subset 'N(P).
Axiom not_triv_commKP: ~ trivg [~: K, P].

(* lemma 3.14 *)
Axiom commVK: [~: V, K] = V.
Axiom triv_centK: trivg 'C_V(K).
Axiom triv_VInormK: trivg (V :&: 'N_H(K)).

(* lemma 3.15 *)
Axiom KeqF: K = 'F('N_H(K)) :> (set _).

(* lemma 3.16 *)
Axiom subK: 'C_H(K) \subset 'C_('N_H(K))(K) /\ 'C_('N_H(K))(K) \subset K.

(* action of R0 over H *)
(* lemma 3.17 *)
Axiom not_triv_commKR0: ~ trivg [~: K, R0].

(* lemma 3.18 *)
Axiom triv_centV: trivg 'C_(K * R0)(V).

(* lemma 3.19 *)
Axiom centVR0_p: #|'C_V(R0)| = p.

(* lemma 3.20 *)
Axiom triv_centPR0: trivg 'C_P(R0).

(* lemma 3.21 *)
Axiom commPR0: P = [~: P, R0] :> (set _).

(* theorem 3.6 
Theorem p_length_1_comm: forall p, prime p -> 
  p_length_1 p [~: H, R].
*)


End by_contradiction.

End three_dot_six.
