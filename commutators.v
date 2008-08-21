(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*  Commutators  *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat.
Require Import fintype finset.
Require Import groups morphisms automorphism normal.

(* Require Import seq paths connect div ssralg bigops group_perm. *)

Set Implicit Arguments.
Unset Strict Implicit. 
Import Prenex Implicits.

Import GroupScope.

Section Basic_commutator_properties.

Variable T : finGroupType.
Implicit Types x y z : T.

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

Theorem hall_witt_identity : forall x y z,
  [~ x, y^-1, z] ^ y * [~ y, z^-1, x] ^ z * [~ z, x^-1, y] ^ x = 1.
Proof.
(* gsimpl *)
pose a x y z : T := x * z * y ^ x.
suffices hw_aux: forall x y z, [~ x, y^-1, z] ^ y = (a x y z)^-1 * (a y z x).
  by move=> x y z; rewrite !hw_aux 2!mulgA !mulgK mulVg.
by move=> *; rewrite commgEr conjMg -conjgM -conjg_Rmul 2!invMg conjgE !mulgA.
Qed.

End Basic_commutator_properties.

(* the following properties are useful for studying p-groups of class 2 *)
Section Commutator_powers.

Variable T : finGroupType.
Variables x y : T.

Let z := [~ x, y].

Hypotheses (cxz : commute x z) (cyz : commute y z).

Lemma commXXg : forall i j, [~ x ^+ i, y ^+ j] = z ^+ (i * j).
Proof.
move=> i j; apply: (canLR (mulKg _)).
rewrite conjXg mulnC expgn_mul -expMgn; [congr (_ ^+ i) | exact: commuteX].
rewrite [x ^ _]mulgA -expVgn [_ * x]conjgC conjXg conjg_Rmul invgK -/z -mulgA.
by rewrite -expMgn /commute mulgKV // mulgA cyz mulgK.
Qed.

Lemma expMg_Rmul : forall i,
  (y * x) ^+ i = y ^+ i * x ^+ i * z ^+ (i * i.-1)./2.
Proof.
elim=> [|i IHi]; first by rewrite !mulg1.
rewrite !expgS {}IHi mulgA -(mulgA y) (mulgA x) (commgC x _) -{2}(expg1 x).
rewrite commXXg mul1n -(mulgA _ _ (x ^+ i)) -commuteX2 // !mulgA -mulgA.
congr (_ * _); rewrite -expgn_add /=; congr (_ ^+ _); case: i => // i.
by rewrite -add2n muln_addl mul2n half_add odd_double half_double mulnC.
Qed.

End Commutator_powers.

Section Commutators_and_centralizers.

Variable T : finGroupType.
(* should not be a group but a set *)
Variable H : {set T}.

(* This is a composite reflections, so it should be a reflection as well. *)
(* I don't see why the centraliser has to be localised. *)
Lemma commg_to_centraliser : forall y,
  {in H, forall x, [~ x, y] = 1} -> H \subset 'C_H[y].
Proof.
move=> y comm1; rewrite subsetI subset_refl /=.
by apply/subsetP=> x Hx; apply/cent1P; apply/commgP; rewrite comm1. 
Qed.

Lemma centraliser_to_commg: forall x y, x \in 'C_H[y] -> [~ x, y] = 1.
Proof.
move=> x y; case/setIP=> _; rewrite (sameP cent1P commgP); exact: eqP.
Qed.

End Commutators_and_centralizers.

(***** Set theoretic commutators *****)
Section Commutator_properties.

Variable T : finGroupType.

Lemma commG1: forall H: {set T}, [~: H, 1] = 1.
Proof. 
by move=> H; apply/trivgP; apply/commG1P; apply/centsP; rewrite centsC; apply: sub1G. 
Qed.

Lemma comm1G: forall H: {set T}, [~: 1, H] = 1.
Proof. move=> H; rewrite commsgC; apply: commG1. Qed.

Lemma commg_subset: forall H K : {set T}, [~: H, K] \subset H <*> K.
Proof.
by move=> H K; rewrite comm_subG // -gen_subG genS // (subsetUl, subsetUr).
Qed.

Lemma normGR : forall (H : {group T}) (K : {set T}), H \subset 'N([~: H, K]).
Proof.
move=> H K; apply/subsetP=> x Hx; rewrite inE -genJ gen_subG.
apply/subsetP=> yzx; case/imsetP=> yz; case/imset2P=> y z Hy Kz -> -> {yz yzx}.
have Rxz: [~ x, z] \in [~: H, K] by rewrite mem_commg.
by rewrite -(groupMr _ Rxz) -commMgJ mem_gen ?mem_imset2 ?groupMl.
Qed.

Theorem normal_commutator: forall H K : {group T}, [~: H, K] <| H <*> K.
Proof.
move=> H K; rewrite /(_ <| _) commg_subset /= gen_subG subUset normGR.
by rewrite commsgC normGR.
Qed.

Lemma subcomm_normal : forall H K : {group T},
  ([~: H, K] \subset K) = (H \subset 'N(K)).
Proof.
move=> H K; rewrite gen_subG; apply/subsetP/subsetP=> [sRK x Hx | nKH xy].
  rewrite inE; apply/subsetP=> yx; case/imsetP=> y Ky ->{yx}.
  by rewrite conjg_Rmul groupMr // sRK // mem_imset2 ?groupV.
case/imset2P=> x y Hx Ky ->{xy}; rewrite commgEr groupMr //.
by rewrite memJ_norm (groupV, nKH). 
Qed.

Lemma sub_der1_normal : forall G H : {group T},
  [~: G, G] \subset H -> H \subset G -> H <| G.
Proof.
move=> G H sG'H sHG; rewrite /(H <| G) sHG -subcomm_normal.
apply: subset_trans sG'H; exact: commgS.
Qed.

Lemma sub_der1_abelian : forall G H : {group T},
  [~: G, G] \subset H -> H \subset G -> abelian (G / H).
Proof.
move=> G H sG'H sHG; have [_ nHG] := andP (sub_der1_normal sG'H sHG).
apply/centsP; apply/commG1P.
by rewrite -morphimR // trivg_quotient // comm_subG.
Qed.

Lemma center_commgl: forall G H K : {group T},
     G \subset 'N(K) -> H \subset 'N(K) ->
  (H / K) \subset 'C(G / K) -> [~: H, G] \subset K.
Proof.
move=> G H K GnormK HnormK.
by rewrite (sameP centsP commG1P) -morphimR // trivg_quotient // comm_subG //.
Qed. 

Lemma center_commgr : forall G H K : {group T}, 
  [~: H, G] \subset K -> (H / K) \subset 'C(G / K).
Proof.
move=> G H K sHGK; rewrite /quotient -morphimIdom -(morphimIdom _ G).
rewrite (sameP centsP commG1P) -morphimR ?subsetIl //.
rewrite trivg_quotient //; last by rewrite comm_subG ?subsetIl.
by apply: subset_trans sHGK; rewrite commgSS ?subsetIr.
Qed.

Lemma distr_sgcomml : forall (H K L: group T),
  [~: H, L] * [~: K, L] \subset [~: H * K , L] .
Proof. 
move=> H K L; apply/subsetP=> x; case/mulsgP=> c1 c2.
move/generatedP=>gen1; move/generatedP=>gen2 ->; apply: groupM.
- apply: gen1; rewrite -gen_subG; apply: genS; apply/subsetP=> c.
  case/imset2P=> h l hin lin -> ; apply/imset2P; apply: (Imset2spec _ lin); last done. 
  by move: h hin; apply:subsetP; apply: mulg_subl.
- apply: gen2; rewrite -gen_subG; apply: genS; apply/subsetP=> c.
  case/imset2P=> h l hin lin -> ; apply/imset2P; apply: (Imset2spec _ lin); last done. 
  by move: h hin; apply:subsetP; apply: mulg_subr.
Qed.

Lemma distr_commg_set: forall (H K L: group T), K \subset 'N(H) -> K \subset 'N(L) ->
commg_set (H * K)  L \subset [~: H, L] * [~: K, L].
Proof.
move=> H K L normalH normalL.
apply/subsetP=> c. case/imset2P=> hk l.
case/imset2P=> h k hin kin -> lin -> {hk}. 
rewrite commMgJ.
apply/imset2P; apply: Imset2spec; last done.
- rewrite/commg conjMg conjJg conjVg -/(commg (h ^ k) (l ^ k)).
  apply: mem_gen; apply/imset2P; apply: Imset2spec; last done.
  - by rewrite memJ_norm; first done; apply (subsetP normalH).
  - by rewrite memJ_norm; first done; apply (subsetP normalL).
- by apply: mem_gen; apply/imset2P; apply: Imset2spec; last done.
Qed.

Theorem normal_scommg:  forall H K L : {group T},
  K \subset 'N(L) -> [~: K, L] \subset 'N([~: H, L]).
Proof.
move=> H K L normalK. 
have subL: [~: K, L] \subset L by rewrite subcomm_normal.
by apply: (subset_trans subL); rewrite commsgC; apply: normGR.
Qed.

Lemma group_set_scommgM: forall H K L : {group T},
  K \subset 'N(H) -> K \subset 'N(L) -> group_set ([~: H, L] * [~: K, L]).
Proof.
move=> H K L normalH normalL; apply/comm_group_setP.
by apply:commute_sym; apply: normC; apply: normal_scommg.
Qed.

Theorem distr_sgcommG : forall (H K L: {group T})
   (nh: K \subset 'N(H)) (nl: K \subset 'N(L)),
   [~: H * K , L] = Group (group_set_scommgM  nh nl).
Proof. 
move=> H K L normalH normalL.
apply/eqP; rewrite eqset_sub; apply/andP; split.
- by rewrite gen_subG /=; apply: distr_commg_set.
- apply: distr_sgcomml.
Qed.

Theorem distr_sgcomm: forall H K L : {group T},
  K \subset 'N(H) -> K \subset 'N(L) -> [~: H * K , L] = [~: H, L] * [~: K, L]. 
Proof. by move=> H K L nH nL; rewrite (distr_sgcommG nH nL).
Qed.

(* Used the trivg predicate, and folded the two lemmas into a reflection *)
(* predicate.                                                            *)
Lemma gen_trivgP : forall H : {set T}, reflect (<<H>> = 1) (trivg H).
Proof.
move=> H; rewrite /trivg -gen_subG [_ \subset _](sameP (trivgP _) eqP).
exact: eqP.
Qed.

(* redundant -- GG
Lemma gen_setr: forall H:set T, H \subset [set 1] -> <<H>> = [set 1].
Proof.
move=> H subH; apply/setP => x; apply/idP/idP.
- move :x; apply /subsetP. by rewrite gen_subG. 
- by move/set1P=> xis1; rewrite xis1; apply: (group1 (generated_group H)).
Qed.
*)

Lemma triv_comm_centr: forall G A: {set T}, [~: 'C_G(A), A] = 1. 
move=> G A.
apply/eqP; rewrite eqset_sub; apply/andP; split.
- rewrite gen_subG /=; apply/subsetP=> c; case/imset2P=> x y; case/setIP=> xinG xinC yin ->.
  by apply/set1P; apply/eqP; apply/commgP; apply: (centP xinC).
- by apply/subsetP=> one; move/set1P ->; apply: group1.
Qed.

Lemma comm3G1P : forall H K L : {set T},
  reflect {in H & K & L, forall h k l, [~ h, k, l] = 1} ([~: H, K, L] == 1).
Proof.
move=> H K L; have R_C := sameP commG1P centsP; rewrite /trivg in R_C.
rewrite eqset_sub sub1G andbT R_C gen_subG -{}R_C gen_subG.
apply: (iffP subsetP) => [cHKL h k l Hh Kk Ll | cHKL hkl].
  by apply/set1P; rewrite cHKL // !mem_imset2.
by case/imset2P=> hk l; case/imset2P=> h k Hh Kk -> Ll ->; rewrite cHKL.
Qed.

(* Stated the result with ==, as this is likely to be more convenient. *)
Theorem big_hall_witt_identity: forall H K L : {group T},
  [~: H, K, L] == 1 -> [~: K, L, H] == 1 -> [~: L, H, K] == 1.
Proof.
move=> H K L; move/comm3G1P=> cHKL; move/comm3G1P=> cKLH.
apply/comm3G1P=> l h k Ll Hh Kk; symmetry.
rewrite -(conj1g h) -(hall_witt_identity h^-1 k l) invgK.
by rewrite cHKL ?groupV // cKLH ?groupV // !conj1g !mul1g conjgKV.
Qed.

End Commutator_properties.

Section Specialized_results.

Variable T : finGroupType.
Implicit Types x y z : T.

Lemma tech1 : forall (G : {group T}) x y z, x \in G -> y \in G -> z \in G ->
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
rewrite memJ_norm ?mem_gen ?mem_imset2 ?set11 //.
by rewrite groupV commsgC (subsetP (normGR _ _)).
Qed.

(* Removed unnecessary assumption -- GG *)
Lemma tech2 : forall x y, commute [~ x, y] x -> [~ x, y]^-1 = [~ x^-1, y].
Proof.
move=> x y; set u := [~ x, y]; move/commgP; move/conjg_fixP=> cux; apply/eqP.
by rewrite eq_invg_mul -(conjgK x u) cux -commMgJ mulgV comm1g.
Qed.

(* Removed unnecessary assumption, and used duality -- GG *)
Lemma tech3 : forall x y, commute [~ x, y] y -> [~ x, y]^-1 = [~ x, y^-1].
Proof.
move=> x y; move/commute_sym; move/commuteV; move/commute_sym=> cyu.
by rewrite -invg_comm tech2 -invg_comm ?invgK.
Qed.

End Specialized_results.

Section Characteristic.

Variable gT1 : finGroupType.

Lemma charR : forall H1 H2 G : {group gT1},
  H1 \char G -> H2 \char G -> [~: H1, H2] \char G.
Proof.
move=> H1 H2 G; case/charP=> sH1G chH1; case/charP=> sH2G chH2; apply/charP.
by split=> [|f infj Gf]; [rewrite comm_subG | rewrite morphimR // chH1 // chH2].
Qed.

End Characteristic.
