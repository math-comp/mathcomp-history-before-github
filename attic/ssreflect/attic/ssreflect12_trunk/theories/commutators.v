(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat fintype bigops finset.
Require Import binomial groups morphisms automorphism normal gfunc gprod.

(******************************************************************************)
(*   This files contains the proofs of several key properties of commutators, *)
(* including the Hall-Witt identity and the Three Subgroup Lemma.             *)
(*   The definition and notation for both pointwise and set wise commutators  *)
(* ([~x, y, ...] and [~: A, B ,...], respectively) are give in groups.v. This *)
(* file defines the derived group series:                                     *)
(*           G^`(0) ==  G                                                     *)
(*       G^`(n.+1) == [~: G^`(n), G^`(n)]                                     *)
(* as several classical results involve the (first) derived group G^`(1),     *)
(* such as the equivalence H <| G /\ G / H abelian <-> G^`(1) \subset H. The  *)
(* connection between the derived series and solvable groups will only be     *)
(* established in nilpotent.v, however.                                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Definition derived_at_rec n (gT : finGroupType) (A : {set gT}) :=
  iter n (fun B => [~: B, B]) A.

(* Note: 'nosimpl' MUST be used outside of a section -- the end of section   *)
(* "cooking" destroys it.                                                    *)
Definition derived_at := nosimpl derived_at_rec.

Notation "G ^` ( n )" := (derived_at n G)
  (at level 8, format "G ^` ( n )") : group_scope.

Section DerivedBasics.

Variables gT : finGroupType.
Implicit Type A : {set gT}.
Implicit Types G : {group gT}.

Lemma derg0 : forall A, A^`(0) = A. Proof. by []. Qed.
Lemma derg1 : forall A, A^`(1) = [~: A, A]. Proof. by []. Qed.
Lemma dergSn : forall n A, A^`(n.+1) = [~: A^`(n), A^`(n)]. Proof. by []. Qed.

Lemma der_group_set : forall G n, group_set G^`(n).
Proof. move=> G [|n]; exact: groupP. Qed.

Canonical Structure derived_at_group G n := Group (der_group_set G n).

End DerivedBasics.

Notation "G ^` ( n )" := (derived_at_group G n) : subgroup_scope.

Section Basic_commutator_properties.

Variable gT : finGroupType.
Implicit Types x y z : gT.

Lemma conjg_mulR : forall x y, x ^ y = x * [~ x, y].
Proof. by move=> x y; rewrite mulKVg. Qed.

Lemma conjg_Rmul : forall x y, x ^ y = [~ y, x^-1] * x.
Proof. by move=> x y; rewrite commgEr invgK mulgKV. Qed.

Lemma commMgJ : forall x y z, [~ x * y, z] = [~ x, z] ^ y * [~ y, z].
Proof. by move=> x y z; rewrite !commgEr conjgM mulgA -conjMg mulgK. Qed.

Lemma commgMJ : forall x y z, [~ x, y * z] = [~ x, z] * [~ x, y] ^ z.
Proof. by move=> x y z; rewrite !commgEl conjgM -mulgA -conjMg mulKVg. Qed.

Lemma commMgR : forall x y z,
  [~ x * y, z] = [~ x, z] * [~ x, z, y] * [~ y, z].
Proof. by move=> x y z; rewrite commMgJ conjg_mulR. Qed.

Lemma commgMR : forall x y z,
  [~ x, y * z] = [~ x, z] * [~ x, y] * [~ x, y, z].
Proof. by move=> x y z; rewrite commgMJ conjg_mulR mulgA. Qed.

Lemma Hall_Witt_identity : forall x y z,
  [~ x, y^-1, z] ^ y * [~ y, z^-1, x] ^ z * [~ z, x^-1, y] ^ x = 1.
Proof. (* gsimpl *)
pose a x y z : gT := x * z * y ^ x.
suffices hw_aux: forall x y z, [~ x, y^-1, z] ^ y = (a x y z)^-1 * (a y z x).
  by move=> x y z; rewrite !hw_aux 2!mulgA !mulgK mulVg.
by move=> *; rewrite commgEr conjMg -conjgM -conjg_Rmul 2!invMg conjgE !mulgA.
Qed.

(* the following properties are useful for studying p-groups of class 2 *)

Section LeftComm.

Variables (i : nat) (x y : gT).
Hypothesis cxz : commute x [~ x, y].

Lemma commVg : [~ x^-1, y] = [~ x, y]^-1.
Proof.
apply/eqP; rewrite commgEl eq_sym eq_invg_mul invgK mulgA -cxz.
by rewrite -conjg_mulR -conjMg mulgV conj1g.
Qed.

Lemma commXg : [~ x ^+ i, y] = [~ x, y] ^+ i.
Proof.
elim: i => [|i' IHi]; first exact: comm1g.
by rewrite !expgS commMgJ /conjg commuteX // mulKg IHi.
Qed.

End LeftComm.

Section RightComm.

Variables (i : nat) (x y : gT).
Hypothesis cyz : commute y [~ x, y].

Lemma commgV : [~ x, y^-1] = [~ x, y]^-1.
Proof.
rewrite -invg_comm commVg -(invg_comm x y) ?invgK //; exact: commuteV.
Qed.

Lemma commgX : [~ x, y ^+ i] = [~ x, y] ^+ i.
Proof.
rewrite -invg_comm commXg -(invg_comm x y) ?expVgn ?invgK //; exact: commuteV.
Qed.

End RightComm.

Section LeftRightComm.

Variables (i j : nat) (x y : gT).
Hypotheses (cxz : commute x [~ x, y]) (cyz : commute y [~ x, y]).

Lemma commXXg : [~ x ^+ i, y ^+ j] = [~ x, y] ^+ (i * j).
Proof. rewrite expgn_mul commgX commXg //; exact: commuteX. Qed.

Lemma expMg_Rmul : (y * x) ^+ i = y ^+ i * x ^+ i * [~ x, y] ^+ 'C(i, 2).
Proof.
rewrite -triangular_sum; symmetry.
elim: i => [|k IHk] /=; first by rewrite big_geq ?mulg1.
rewrite big_nat_recr /= addnC expgn_add !expgS -{}IHk !mulgA; congr (_ * _).
by rewrite -!mulgA commuteX2 // -commgX // [mulg y]lock 3!mulgA -commgC.
Qed.

End LeftRightComm.

End Basic_commutator_properties.

(***** Set theoretic commutators *****)
Section Commutator_properties.

Variable gT : finGroupType.
Implicit Type rT : finGroupType.
Implicit Types A B C : {set gT}.
Implicit Types D G H K : {group gT}.

Lemma commG1 : forall A, [~: A, 1] = 1.
Proof. by move=> A; apply/commG1P; rewrite centsC sub1G. Qed.

Lemma comm1G : forall A, [~: 1, A] = 1.
Proof. by move=> A; rewrite commGC commG1. Qed.

Lemma commg_sub : forall A B, [~: A, B] \subset A <*> B.
Proof. by move=> A B; rewrite comm_subG // (mulgen_subl, mulgen_subr). Qed.

Lemma commg_norml : forall G A, G \subset 'N([~: G, A]).
Proof.
move=> G A; apply/subsetP=> x Gx; rewrite inE -genJ gen_subG.
apply/subsetP=> yzx; case/imsetP=> yz; case/imset2P=> y z Gy Az -> -> {yz yzx}.
by rewrite -(mulgK [~ x, z] (_ ^ x)) -commMgJ !(mem_commg, groupMl, groupV).
Qed.

Lemma commg_normr : forall G A, G \subset 'N([~: A, G]).
Proof. by move=> G A; rewrite commGC commg_norml. Qed.

Lemma commg_norm : forall G H, G <*> H \subset 'N([~: G, H]).
Proof. by move=> G H; rewrite mulgen_subG ?commg_norml ?commg_normr. Qed.

Lemma commg_normal : forall G H, [~: G, H] <| G <*> H.
Proof. by move=> G H; rewrite /(_ <| _) commg_sub commg_norm. Qed.

Lemma normsRl : forall A G B, A \subset G -> A \subset 'N([~: G, B]).
Proof. by move=> A G B sAG; exact: subset_trans (commg_norml G B). Qed.

Lemma normsRr : forall A G B, A \subset G -> A \subset 'N([~: B, G]).
Proof. by move=> A G B sAG; exact: subset_trans (commg_normr G B). Qed.

Lemma commg_subr : forall G H, ([~: G, H] \subset H) = (G \subset 'N(H)).
Proof.
move=> G H; rewrite gen_subG; apply/subsetP/subsetP=> [sRH x Gx | nGH xy].
  rewrite inE; apply/subsetP=> yx; case/imsetP=> y Ky ->{yx}.
  by rewrite conjg_Rmul groupMr // sRH // mem_imset2 ?groupV.
case/imset2P=> x y Gx Hy ->{xy}.
by rewrite commgEr groupMr // memJ_norm (groupV, nGH).
Qed.

Lemma commg_subl : forall G H, ([~: G, H] \subset G) = (H \subset 'N(G)).
Proof. by move=> G H; rewrite commGC commg_subr. Qed.

Lemma commg_subI : forall A B G H,
  A \subset 'N_G(H) -> B \subset 'N_H(G) -> [~: A, B] \subset G :&: H.
Proof.
move=> A B G H; rewrite !subsetI -(gen_subG _ 'N(G)) -(gen_subG _ 'N(H)).
rewrite -commg_subr -commg_subl; case/andP=> sAG sRH; case/andP=> sBH sRG.
by rewrite (subset_trans _ sRG) ?(subset_trans _ sRH) ?commgSS ?subset_gen.
Qed.

Lemma quotient_cents2 : forall A B K,
    A \subset 'N(K) -> B \subset 'N(K) ->
  (A / K \subset 'C(B / K)) = ([~: A, B] \subset K).
Proof.
move=> A B K nKA nKB.
by rewrite (sameP commG1P trivgP) /= -quotientR // quotient_sub1 // comm_subG.
Qed.

Lemma quotient_cents2r : forall A B K,
  [~: A, B] \subset K -> (A / K) \subset 'C(B / K).
Proof.
move=> A B K sABK; rewrite -2![_ / _]morphimIdom -!quotientE.
by rewrite quotient_cents2 ?subsetIl ?(subset_trans _ sABK) ?commgSS ?subsetIr.
Qed.

Lemma sub_der1_norm : forall G H,
   G^`(1) \subset H -> H \subset G -> G \subset 'N(H).
Proof.
by move=> G H sG'H sHG; rewrite -commg_subr (subset_trans _ sG'H) ?commgS.
Qed.

Lemma sub_der1_normal : forall G H, G^`(1) \subset H -> H \subset G -> H <| G.
Proof. by move=> G H sG'H sHG; rewrite /(H <| G) sHG sub_der1_norm. Qed.

Lemma sub_der1_abelian : forall G H, G^`(1) \subset H -> abelian (G / H).
Proof. move=> G H sG'H; exact: quotient_cents2r. Qed.

Lemma der1_min : forall G H,
  G \subset 'N(H) -> abelian (G / H) -> G^`(1) \subset H.
Proof. by move=> G H nHG abGH; rewrite -quotient_cents2. Qed.

Lemma der_abelian : forall n G, abelian (G^`(n) / G^`(n.+1)).
Proof. by move=> n G; rewrite sub_der1_abelian // der_subS. Qed.

Lemma commg_normSl :  forall G H K,
  G \subset 'N(H) -> [~: G, H] \subset 'N([~: K, H]).
Proof. by move=> G H K nHG; rewrite normsRr // commg_subr. Qed.

Lemma commg_normSr :  forall G H K,
  G \subset 'N(H) -> [~: H, G] \subset 'N([~: H, K]).
Proof. by move=> G H K nHG; rewrite !(commGC H) commg_normSl. Qed.

Lemma commMGr : forall G H K,
  [~: G, K] * [~: H, K] \subset [~: G * H , K].
Proof. by move=> G H K; rewrite mul_subG ?commSg ?(mulG_subl, mulG_subr). Qed.

Lemma commMG : forall G H K,
  H \subset 'N([~: G, K]) -> [~: G * H , K] = [~: G, K] * [~: H, K].
Proof.
move=> G H K nRH; apply/eqP; rewrite eqEsubset commMGr andbT.
have nRHK: [~: H, K] \subset 'N([~: G, K]) by rewrite comm_subG ?commg_normr.
have defM := norm_mulgenEr nRHK; rewrite -defM gen_subG /=.
apply/subsetP=> r; case/imset2P=> m z; case/imset2P=> x y Gx Hy -> Kz ->{r m}.
by rewrite commMgJ {}defM mem_mulg ?memJ_norm ?mem_commg // (subsetP nRH).
Qed.

Lemma comm3G1P : forall A B C,
  reflect {in A & B & C, forall h k l, [~ h, k, l] = 1} ([~: A, B, C] :==: 1).
Proof.
move=> A B C; have R_C := sameP trivgP commG1P.
rewrite -subG1 R_C gen_subG -{}R_C gen_subG.
apply: (iffP subsetP) => [cABC x y z Ax By Cz | cABC xyz].
  by apply/set1P; rewrite cABC // !mem_imset2.
by case/imset2P=> xy z; case/imset2P=> x y Ax By -> Cz ->; rewrite cABC.
Qed.

Lemma three_subgroup : forall G H K,
  [~: G, H, K] :=: 1 -> [~: H, K, G] :=: 1-> [~: K, G, H] :=: 1.
Proof.
move=> G H K; move/eqP; move/comm3G1P=> cGHK; move/eqP; move/comm3G1P=> cHKG.
apply/eqP; apply/comm3G1P=> x y z Kx Gy Hz; symmetry.
rewrite -(conj1g y) -(Hall_Witt_identity y^-1 z x) invgK.
by rewrite cGHK ?groupV // cHKG ?groupV // !conj1g !mul1g conjgKV.
Qed.

Lemma der1_mulgen_cycles : forall x y : gT, 
  let XY := <[x]> <*> <[y]> in let xy := [~ x, y] in
  xy \in 'C(XY) -> XY^`(1) = <[xy]>.
Proof. 
move=> x y; rewrite mulgen_idl mulgen_idr /= -sub_cent1; move/norms_gen=> nRxy.
apply/eqP; rewrite eqEsubset cycle_subG mem_commg ?mem_gen ?set21 ?set22 //.
rewrite der1_min // quotient_gen -1?gen_subG // quotientU abelian_gen.
rewrite /abelian subUset centU !subsetI andbC centsC -andbA -!abelianE.
rewrite !quotient_abelian ?(abelianS (subset_gen _) (cycle_abelian _)) //=.
by rewrite andbb quotient_cents2r ?genS // /commg_set imset2_set1l imset_set1.
Qed.

(* GG -- unsure about the usefulness of this lemma; keeping it for now. *)
Lemma commgAC : forall G x y z, x \in G -> y \in G -> z \in G ->
  commute y z -> abelian [~: [set x], G] -> [~ x, y, z] = [~ x, z, y].
Proof.
move=> G x y z Gx Gy Gz cyz; move/centsP=> cRxG; pose cx' u := [~ x^-1, u].
have xR3: forall u v, [~ x, u, v] = x^-1 * (cx' u * cx' v) * x ^ (u * v).
  move=> u v; rewrite mulgA -conjg_mulR conjVg [cx' v]commgEl mulgA -invMg.
  by rewrite -mulgA conjgM -conjMg -!commgEl.
suffices RxGcx': forall u, u \in G -> cx' u \in [~: [set x], G].
  by rewrite !xR3 {}cyz; congr (_ * _ * _); rewrite cRxG ?RxGcx'.
move=> u Gu; suffices: [~ x, u] ^ x^-1 \in [~: [set x], G].
  by move/groupMl <-; rewrite -commMgJ mulgV comm1g group1.
by rewrite memJ_norm ?mem_commg ?set11 // groupV (subsetP (commg_normr _ _)).
Qed.

(* Aschbacher, exercise 3.6 (used in proofs of Aschbacher 24.7 and B & G 1.10 *)
Lemma comm_norm_cent_cent : forall H G K,
    H \subset 'N(G) -> H \subset 'C(K) -> G \subset 'N(K) ->
  [~: G, H] \subset 'C(K).
Proof.
move=> H G K nGH; move/centsP=> cKH nKG; rewrite commGC gen_subG centsC.
apply/centsP=> x Kx yz; case/imset2P=> y z Hy Gz ->{yz}; red.
rewrite mulgA -[x * _]cKH ?groupV // -!mulgA; congr (_ * _).
rewrite (mulgA x) (conjgC x) (conjgCV z) 3!mulgA; congr (_ * _).
by rewrite -2!mulgA (cKH y) // -mem_conjg (normsP nKG).
Qed.

Lemma charR : forall H K G, H \char G -> K \char G -> [~: H, K] \char G.
Proof.
move=> H K G; case/charP=> sHG chH; case/charP=> sKG chK; apply/charP.
by split=> [|f infj Gf]; [rewrite comm_subG | rewrite morphimR // chH // chK].
Qed.

Lemma der_char : forall n G, G^`(n) \char G.
Proof.
by move=> n G; elim: n => [|n IHn]; rewrite ?char_refl // dergSn charR.
Qed.

Lemma der_sub : forall n G, G^`(n) \subset G.
Proof. by move=> n G; rewrite char_sub ?der_char. Qed.

Lemma der_norm : forall n G, G \subset 'N(G^`(n)).
Proof. by move=> n G; rewrite char_norm ?der_char. Qed.

Lemma der_normal : forall n G, G^`(n) <| G.
Proof. by move=> n G; rewrite char_normal ?der_char. Qed.

Lemma der_subS : forall n G, G^`(n.+1) \subset G^`(n).
Proof. by move=> n G; rewrite comm_subG. Qed.

Lemma der_normalS : forall n G, G^`(n.+1) <| G^`(n).
Proof. by move=> n G; rewrite sub_der1_normal // der_subS. Qed.

Lemma morphim_der : forall rT D (f : {morphism D >-> rT}) n G,
   G \subset D -> f @* G^`(n) = (f @* G)^`(n).
Proof.
move=> rT D f n G sGD; elim: n => // n IHn.
by rewrite !dergSn -IHn morphimR ?(subset_trans (der_sub n G)).
Qed.

Lemma dergS : forall n G H, G \subset H -> G^`(n) \subset H^`(n).
Proof. by move=> n G H sGH; elim: n => // n IHn; exact: commgSS. Qed.

Lemma quotient_der : forall n G H, G \subset 'N(H) -> G^`(n) / H = (G / H)^`(n).
Proof. by move=> n G H; exact: morphim_der. Qed.

End Commutator_properties.

Lemma der_cont : forall n, cont (derived_at n).

Proof. by move=> n aT rT G f; rewrite morphim_der. Qed.

Canonical Structure bgFunc_der n :=
  [bgFunc by fun gT => @der_sub gT n & der_cont n].
Canonical Structure gFunc_der n := GFunc (der_cont n).
Canonical Structure mgFunc_der n := MGFunc (fun _ => dergS n).


