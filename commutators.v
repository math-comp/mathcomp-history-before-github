(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*  Commutators  *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat.
Require Import seq fintype paths connect.
Require Import groups normal center div zp finset group_perm automorphism.
Require Import abelian cyclic.

Set Implicit Arguments.
Unset Strict Implicit. 
Import Prenex Implicits.

Import GroupScope.

(* Both of these lemmas are redundant with the current basis
   conjg_to_eq1 is better handled via canRL / canLR and conjg_inj as below
   conjg_simpl is the symmetric of conjgC and identical to mulKVg.
Section Conjg_addenda.
Variable T: finGroupType.
Variables x y: T.

(* A couple of lemmas about conjugation. move it in group.v ? *)
Lemma conjg_to_eq1: x ^ y = 1 -> x = 1.
Proof.
by move/(canRL (conjgK _)); rewrite conj1g.
Qed.

Lemma conjg_simpl: y * x ^ y = x * y.
Proof.
by rewrite /conjg !mulgA mulgV mul1g.
Qed.

End Conjg_addenda.
*)

Section Basic_commutator_properties.

Variable T : finGroupType.
Implicit Types x y z : T.

(* redundant with commgEl, commgEr, and commgC in groups.v  
Lemma commg_eq1: [~ x, y ] = x^-1 * y^-1 * x * y.
Proof. by rewrite /commg /conjg !mulgA. Qed.

Lemma commg_eq2: [~ x, y ] = (y ^-1) ^x * y.
Proof. by rewrite /commg /conjg !mulgA. Qed.

Lemma commg_eq3: x * y =y * x * [~ x, y ].
Proof. 
by rewrite /commg /conjg mulgA -(mulgA y) mulgV mulg1 !mulgA mulgV mul1g.
Qed.
*)

(* This is useful -- so I added the inverted version. *)
Lemma conjg_mulR : forall x y, x ^ y = x * [~ x, y].
Proof. by move=> x y; rewrite mulKVg. Qed.

Lemma conjg_Rmul : forall x y, x ^ y = [~ y, x^-1] * x.
Proof. by move=> x y; rewrite commgEr invgK mulgKV. Qed.

(* invg_comm, commg1, comm1g in groups.v
Lemma commg_inv: [~ x, y ]^-1 = [~ y, x ].
Proof. by rewrite /commg !invMg !invgK !mulgA. Qed.

Lemma commg1r: [~ x, 1] = 1. 
Proof. by rewrite /commg conjg1 mulVg. Qed.

Lemma commg1l: [~ 1, y] = 1. 
Proof. by rewrite /commg invg1 mul1g conj1g. Qed.
*)

(* Shorter names, shorter proofs, consistent whitespace. *)
Lemma commg_gmult_left : forall x y z, [~ x * y, z] = [~ x, z] ^ y * [~ y, z].
Proof. by move=> x y z; rewrite !commgEr conjgM mulgA -conjMg mulgK. Qed.

Lemma commg_gmult_right : forall x y z, [~ x, y * z] = [~ x, z] * [~ x, y] ^ z.
Proof. by move=> x y z; rewrite !commgEl conjgM -mulgA -conjMg mulKVg. Qed.

Lemma commg_gmultl : forall x y z,
  [~ x * y, z] = [~ x, z] * [~ x, z, y] * [~ y, z].
Proof. by move=> x y z; rewrite commg_gmult_left conjg_mulR. Qed.

Lemma commg_gmultr : forall x y z,
  [~ x, y * z] = [~ x, z] * [~ x, y] * [~ x, y, z].
Proof. by move=> x y z; rewrite commg_gmult_right conjg_mulR mulgA. Qed.

(* reduandant with the reflection lemmas eqP and commgP
Lemma commg_to_commute: [~ x, y ] = 1 -> commute x y.
Proof.
rewrite /commg /commute => comm.
apply /eqP.
by rewrite -(mulg1 (y*x)) -comm -commg_eq3. 
Qed.

Lemma commute_to_commg: commute x y -> [~ x, y ] = 1.
Proof.
rewrite /commute => comm.
by rewrite commg_eq1 -invMg -comm -mulgA mulVg.
Qed.
*)

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

(* a lemma about commutation *)
Lemma commuteX2 : forall (T : finGroupType) (x y : T) m n,
  commute x y ->  commute (x ^+ m) (y ^+ n).
Proof. move=> *; apply: commuteX; apply: commute_sym; exact: commuteX. Qed.

(* the following properties are useful for studying p-groups of class 2 *)
Section Commutator_powers.

Variable T : finGroupType.
Variables x y : T.

Let z := [~ x, y].

Hypotheses (cxz : commute x z) (cyz : commute y z).

(* is conjXg in groups.v
(* another lemma about conjugation *)
Lemma conj_power : forall x y i, (x ^+ i) ^ y = (x ^ y) ^+ i.
Proof.
elim; first by rewrite !expg0; apply conj1g.
by move=> n indh; rewrite !expgS -indh conjMg.
Qed.
*)

Lemma invXg : forall j, y ^- j = y^-1 ^+ j.
Proof.
move=> j; apply/eqP; rewrite eq_invg_mul.
by rewrite -expMgn /commute mulgV (mulVg, exp1gn).
Qed.

Lemma commXXg : forall i j, [~ x ^+ i, y ^+ j] = z ^+ (i * j).
Proof.
move=> i j; apply: (canLR (mulKg _)).
rewrite conjXg mulnC expgn_mul -expMgn; [congr (_ ^+ i) | exact: commuteX].
rewrite [x ^ _]mulgA invXg [_ * x]conjgC conjXg conjg_Rmul invgK -/z -mulgA.
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
  {in H, forall x, [~ x, y] = 1} -> H \subset C_(H)[y].
Proof.
move=> y comm1; rewrite subsetI subset_refl /=.
by apply/subsetP=> x Hx; apply/centg1P; apply/commgP; rewrite comm1. 
Qed.

Lemma centraliser_to_commg: forall x y, x \in C_(H)[y] -> [~ x, y] = 1.
Proof.
move=> x y; case/setIP=> _; rewrite (sameP centg1P commgP); exact: eqP.
Qed.

End Commutators_and_centralizers.

(***** Set theoretic commutators *****)
Section Commutator_properties.

Variable T : finGroupType.

Lemma sub_sgcomm : forall H K : {set T}, [~: H, K] \subset [~: K, H].
Proof.
move=> H K.
rewrite gen_subG; apply/subsetP=> xy; case/imset2P=> x y Hx Ky ->{xy}.
by rewrite -groupV invg_comm mem_geng // imset2_f_imp.
Qed.

Theorem sym_sgcomm: forall (H K : set T), [~: H, K] = [~: K, H].
Proof. by move=> H K; apply/eqP; rewrite eqset_sub !sub_sgcomm. Qed.

(* a couple of lemmas about set conjugation *)
Lemma subset_conjugate_of: forall (H K : {set T}) (z : T), 
  (H :^ z \subset K) = (H \subset K :^ z^-1).
Proof. by move=> H K z; rewrite -{2}(conjsgK z H) conjSg. Qed.

(* redundant -- proved the boolean equality instead.
Lemma subset_conjugate_of2: forall (H K: set T) (z: T), 
H \subset K:^ z^-1 -> H:^z \subset K.
Proof.
move=> H K z sub.
by rewrite -(conjsg1 K) -(mulVg z) conjsgM conjSg.
Qed.
*)

Lemma genJg : forall (H : {set T}) z,  <<H :^z>> = <<H>> :^ z.
Proof.
move=> H z; apply/eqP; rewrite eqset_sub subset_conjugate_of.
by rewrite !gen_subG conjSg -?subset_conjugate_of !sub_geng.
Qed.

Lemma commg_subset: forall H K : {set T}, [~: H, K] \subset H <*> K.
Proof.
move=> H K; rewrite gen_subG.
apply/subsetP=> xy; case/imset2P=> x y Hx Ky ->{xy}.
by rewrite groupR ?mem_geng //; apply/setUP; auto.
Qed.

Lemma normGR : forall (H : {group T}) (K : {set T}), H \subset 'N([~: H, K]).
Proof.
move=> H K; apply/subsetP=> x Hx; rewrite inE -genJg gen_subG.
apply/subsetP=> yzx; case/imsetP=> yz; case/imset2P=> y z Hy Kz -> -> {yz yzx}.
have Rxz: [~ x, z] \in [~: H, K] by rewrite mem_geng ?imset2_f_imp.
by rewrite -(groupMr _ Rxz) -commg_gmult_left mem_geng ?imset2_f_imp ?groupMl.
Qed.

Theorem normal_commutator: forall H K : {group T}, [~: H, K] <| H <*> K.
Proof.
move=> H K; rewrite /(_ <| _) commg_subset /= gen_subG subUset normGR.
by rewrite sym_sgcomm normGR.
Qed.

Lemma subcomm_normal : forall H K : {group T},
  ([~: H, K] \subset K) = (H \subset 'N(K)).
Proof.
move=> H K; rewrite gen_subG; apply/subsetP/subsetP=> [sRK x Hx | nKH xy].
  rewrite inE; apply/subsetP=> yx; case/imsetP=> y Ky ->{yx}.
  by rewrite conjg_Rmul groupMr // sRK // imset2_f_imp ?groupV.
case/imset2P=> x y Hx Ky ->{xy}; rewrite commgEr groupMr //.
by rewrite memJ_normg (groupV, nKH). 
Qed.

(* redundant -- proved the equality
Lemma normalized_commutator2: forall H K: group T, [~: H, K] \subset K -> H \subset 'N(K).
Proof.
move=> H K. 
rewrite sym_sgcomm /commutator; move /subsetP=> subK.
rewrite /normaliser; apply /subsetP => h hin.
rewrite in_set; apply /subsetP =>x. 
move/imsetP; case => k kin ->. 
rewrite conjg_mulR; apply: groupM; first done; apply: subK; apply: mem_geng.
by rewrite /commg_set; apply/imset2P; apply: (Imset2spec kin hin).
Qed.
*)

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

Lemma comm3G1P : forall H K L : {set T},
  reflect {in H & K & L, forall h k l, [~ h, k, l] = 1} ([~: H, K, L] == 1).
Proof.
move=> H K L; have R_C := sameP commG1P centralP; rewrite /trivg in R_C.
rewrite eqset_sub sub1G andbT R_C gen_subG -{}R_C gen_subG.
apply: (iffP subsetP) => [cHKL h k l Hh Kk Ll | cHKL hkl].
  by apply/set1P; rewrite cHKL // !imset2_f_imp.
by case/imset2P=> hk l; case/imset2P=> h k Hh Kk -> Ll ->; rewrite cHKL.
Qed.

(* again, redundant -- GG
Lemma eq_commutator_1_to_eq_commg_1: forall H K L: set T, 
  [~: H, K, L] = 1 -> {in H & K & L, forall h k l, 1 = [~ h, k, l]}.
Proof.
move=> H K L.
rewrite /commutator => HKL h k l hin kin lin.
have{HKL} HKL1 := (@gen_setl _ HKL).
apply/set1P; apply: subsetP HKL1 [~ h, k, l] _.
rewrite/commg_set; apply/imset2P.
apply: Imset2spec; last by reflexivity.
- rewrite (subsetP (sub_geng _)) //.
  by apply/imset2P; apply:  Imset2spec; last by reflexivity.
- done.
Qed.
*)

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
  commute y z -> abel [~: [set x], G] -> [~ x, y, z] = [~ x, z, y].
Proof.
move=> G x y z Gx Gy Gz cyz; move/abelP=> cRxG; pose cx' u := [~ x^-1, u].
have xR3: forall u v, [~ x, u, v] = x^-1 * (cx' u * cx' v) * x ^ (u * v).
  move=> u v; rewrite mulgA -conjg_mulR conjVg [cx' v]commgEl mulgA -invMg.
  by rewrite -mulgA conjgM -conjMg -!commgEl.
suffices RxGcx': forall u, u \in G -> cx' u \in [~: [set x], G].
  by rewrite !xR3 {}cyz; congr (_ * _ * _); rewrite cRxG ?RxGcx'.
move=> u Gu; suffices: [~ x, u] ^ x^-1 \in [~: [set x], G].
  by move/groupMl <-; rewrite -commg_gmult_left mulgV comm1g group1.
rewrite memJ_normg ?mem_geng ?imset2_f_imp ?set11 //.
by rewrite groupV sym_sgcomm (subsetP (normGR _ _)).
Qed.

(* Removed unnecessary assumption -- GG *)
Lemma tech2 : forall x y, commute [~ x, y] x -> [~ x, y]^-1 = [~ x^-1, y].
Proof.
move=> x y; set u := [~ x, y]; move/commgP; move/conjg_fixP=> cux; apply/eqP.
by rewrite eq_invg_mul -(conjgK x u) cux -commg_gmult_left mulgV comm1g.
Qed.

(* Removed unnecessary assumption, and used duality -- GG *)
Lemma tech3 : forall x y, commute [~ x, y] y -> [~ x, y]^-1 = [~ x, y^-1].
Proof.
move=> x y; move/commute_sym; move/commuteV; move/commute_sym=> cyu.
by rewrite -invg_comm tech2 -invg_comm ?invgK.
Qed.

End Specialized_results.

