(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*  Commutators  *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat fintype finset.
Require Import groups morphisms automorphism normal.

(* Require Import seq paths connect div ssralg bigops group_perm. *)

Set Implicit Arguments.
Unset Strict Implicit. 
Import Prenex Implicits.

Import GroupScope.

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
by rewrite expgS commMgJ /conjg commuteX // mulKg IHi.
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

Lemma expMg_Rmul : (y * x) ^+ i = y ^+ i * x ^+ i * [~ x, y] ^+ (i * i.-1)./2.
Proof.
elim: i => [|k IHk]; first by rewrite !mulg1.
rewrite expgS {}IHk mulgA -(mulgA y) (mulgA x) (commgC x _) commgX // 3!mulgA.
rewrite -expgS -[_ * x ^+ k]mulgA -commuteX2 // -(mulgA _ x) (mulgA x).
rewrite -expgS -2!mulgA mulgA -expgn_add; congr (_ * _ ^+ _); case: k => // k.
by rewrite -add2n muln_addl mul2n half_add odd_double half_double mulnC.
Qed.

End LeftRightComm.

End Basic_commutator_properties.

(* GG -- outcommenting the whole section -- lemmas are not used
Section Commutators_and_centralizers.

Variable T : finGroupType.
(* should not be a group but a set *)
Variable H : {set T}.

(* This is a composite reflections, so it should be a reflection as well. *)
(* I don't see why the centraliser has to be localised. *)
Lemma commg_to_centraliser : forall y,
  {in H, forall x, [~ x, y] = 1} -> H \subset 'C_H[y].
Proof.
move=> y comm1; rewrite subsetI subxx /=.
by apply/subsetP=> x Hx; apply/cent1P; apply/commgP; rewrite comm1. 
Qed.

Lemma centraliser_to_commg: forall x y, x \in 'C_H[y] -> [~ x, y] = 1.
Proof.
move=> x y; case/setIP=> _; rewrite (sameP cent1P commgP); exact: eqP.
Qed.

End Commutators_and_centralizers.
*)

(***** Set theoretic commutators *****)
Section Commutator_properties.

Variable gT : finGroupType.
Implicit Types A B C : {set gT}.
Implicit Types G H K : {group gT}.

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

Lemma commg_normal: forall G H, [~: G, H] <| G <*> H.
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
move=> A B K sABK.
rewrite -2![_ / _]morphimIdom -!quotientE quotient_cents2 ?subsetIl //.
by apply: subset_trans sABK; rewrite commgSS ?subsetIr.
Qed.

Lemma sub_der1_norm : forall G H,
  [~: G, G] \subset H -> H \subset G -> G \subset 'N(H).
Proof.
by move=> G H sG'H sHG; rewrite -commg_subr (subset_trans _ sG'H) ?commgS.
Qed.

Lemma sub_der1_normal : forall G H,
  [~: G, G] \subset H -> H \subset G -> H <| G.
Proof. by move=> G H sG'H sHG; rewrite /(H <| G) sHG sub_der1_norm. Qed.

Lemma sub_der1_abelian : forall G H, [~: G, G] \subset H -> abelian (G / H).
Proof. move=> G H sG'H; exact: quotient_cents2r. Qed.

Lemma der1_min : forall G H,
  G \subset 'N(H) -> abelian (G / H) -> [~: G, G] \subset H.
Proof. by move=> G H nHG abGH; rewrite -quotient_cents2. Qed.

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
    H \subset 'N(G) -> H \subset 'N(K) ->
  [~: G * H , K] = [~: G, K] * [~: H, K].
Proof.
move=> G H K nGH nKH; apply/eqP; rewrite eqEsubset commMGr andbT.
have defM := norm_mulgenEr (commg_normSl G nKH); rewrite -defM gen_subG /=.
apply/subsetP=> r; case/imset2P=> m z; case/imset2P=> x y Gx Hy -> Kz ->{r m}.
rewrite commMgJ {}defM mem_mulg ?memJ_norm ?mem_commg //.
apply: subsetP Hy; exact: normsR.
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

Lemma charR : forall H K G, H \char G -> K \char G -> [~: H, K] \char G.
Proof.
move=> H K G; case/charP=> sHG chH; case/charP=> sKG chK; apply/charP.
by split=> [|f infj Gf]; [rewrite comm_subG | rewrite morphimR // chH // chK].
Qed.

End Commutator_properties.
