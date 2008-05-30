(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*  Commutators  *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat.
Require Import seq fintype paths connect.
Require Import groups normal center div zp finset group_perm automorphism.
Require Import abelian cyclic.

Set Implicit Arguments.
Unset Strict Implicit. 
Import Prenex Implicits.
Open Scope group_scope. 

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

Section Basic_commutator_properties.
Variable T:finGroupType.
Variables x y z: T.

Lemma commg_eq1: [~ x, y ] = x^-1 * y^-1 * x * y.
Proof. by rewrite /commg /conjg !mulgA. Qed.

Lemma commg_eq2: [~ x, y ] = (y ^-1) ^x * y.
Proof. by rewrite /commg /conjg !mulgA. Qed.

Lemma commg_eq3: x * y =y * x * [~ x, y ].
Proof. 
by rewrite /commg /conjg mulgA -(mulgA y) mulgV mulg1 !mulgA mulgV mul1g.
Qed.

Lemma conjg_as_commg: x ^ y = x * [~ x, y].
Proof. by rewrite /commg mulgA mulgV mul1g. Qed.

Lemma commg_inv: [~ x, y ]^-1 = [~ y, x ].
Proof. by rewrite /commg !invMg !invgK !mulgA. Qed.

Lemma commg1r: [~ x, 1] = 1. 
Proof. by rewrite /commg conjg1 mulVg. Qed.

Lemma commg1l: [~ 1, y] = 1. 
Proof. by rewrite /commg invg1 mul1g conj1g. Qed.

Lemma commg_gmult_left : [~ x * y, z] = [~ x, z]  ^ y * [~ y, z].
Proof.
rewrite /commg /conjg. 
(* gsimpl *)
(* getting rid of y *)
rewrite invMg !mulgA -(mulgA _ _ y^-1) mulgV mulg1.
(* getting rid of z *)
by rewrite -(mulgA _ z) mulgV mulg1.
Qed.

Lemma commg_gmult_right: [~ x, y * z] = [~ x, z]  * [~ x, y]^z.
Proof.
rewrite /commg /conjg . 
(* gsimpl *)
(* getting rid of z *)
rewrite invMg !mulgA  -(mulgA _ z) mulgV mulg1.
(* getting rid of x *)
by rewrite -(mulgA _ x (x^-1)) mulgV mulg1.
Qed.

Lemma commg_gmultl: [~ x * y, z] = [~ x, z] * [~ x, z, y] * [~ y, z].
Proof.
by rewrite commg_gmult_left {4}/commg mulgA mulgV mul1g.
Qed.

Lemma commg_gmultr: [~ x, y * z] = [~ x, z] * [~ x, y] * [~ x, y, z].
Proof.
rewrite commg_gmult_right {5}/commg -mulgA.
by rewrite (mulgA [~ x, y]) mulgV mul1g.
Qed.

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

Theorem hall_witt_identity: 
[~ x, y^-1, z]^y * [~ y, z^-1, x]^z * [~z, x^-1, y]^x = 1.
Proof.
(* gsimpl *)
pose a x y z := x * z * x^-1 * y * x.
have hw_aux: forall x y z:T, [~ x, y^-1, z]^y = (a T x y z)^-1 * (a T y z x).
clear x y z => x y z. 
  by rewrite /commg /a /conjg !invMg !invgK !mulgA mulVg mul1g. 
rewrite !hw_aux mulgA mulgA -(mulgA _ (a T y z x) _) mulgV mulg1.
by rewrite -(mulgA _ (a T z x y)) mulgV mulg1 mulVg.
Qed.

End Basic_commutator_properties.

(* a lemma about commutation *)
Lemma commute_expnm: forall (T: finGroupType) (x y:T) m n,
  commute x y ->  commute (x ^+ m) (y ^+ n).
Proof.
move=>T x y m n comm.
by apply: commuteX; apply: commute_sym; apply commuteX.
Qed.

(* the following properties are useful for studying p-groups of class 2 *)
Section Commutator_powers.
Variable T: finGroupType.
Variables x y: T.

(* another lemma about conjugation *)
Lemma conj_power: forall i, (x ^+ i) ^ y = (x ^ y) ^+ i.
Proof.
elim; first by rewrite !expg0; apply conj1g.
by move=> n indh; rewrite !expgS -indh conjMg.
Qed.

Lemma commute_to_power: commute x [~ x, y] -> commute y [~ x, y] -> 
forall (i j: nat) , [~ x ^+ i, y ^+ j] = [~ x, y] ^+ (i * j).
Proof.
move => commx commy. 
have lem: forall i, (x ^+ i) ^ y = (x ^+ i) * ([~ x, y] ^+ i).
  move=> i; rewrite conj_power conjg_as_commg.
  by rewrite expMgn. 
move => i j. rewrite {1} /commg. 
apply: (canLR (mulKg _)).
elim: j; first by rewrite muln0 /= conjg1 mulg1. 
move=> n indh; rewrite expgS conjgM lem /conjg -!mulgA. 
rewrite -(commute_expnm n i commy).
rewrite /conjg in indh.
by rewrite (mulgA (x ^+ i)) mulgA indh -mulgA -expgn_add mulnSr.
Qed.

Lemma commute_power1: commute x [~ x, y] -> commute y [~ x, y] -> 
forall (i: nat) ,(y * x) ^+ i = ([~ x, y] ^+ ( i * i.-1)./2) * (y ^+ i) * (x ^+ i).
Proof.
set z := [~ x, y] => commx commy.
elim=> [|n indh]; first by rewrite /= !mulg1.
rewrite expgSr {}indh -mulgA (mulgA _ y).
have ->: ((x ^+ n) * y = ([~ x, y] ^+ n) * y * (x ^+ n)).
  rewrite -(commuteX n commy) -mulgA.
  apply: (canRL (mulKVg _)); rewrite -/(conjg (x ^+ n) y). 
  rewrite -(commute_expnm n  n commx) /conjg. 
  apply: (canRL (mulKVg _)); rewrite (mulgA _ _ y) -{1 2}(expg1 y).
  rewrite -mulgA -/(commg (x ^+ n) (y ^+ 1)) -{2}(muln1 n).
  by apply: commute_to_power.
rewrite -2!mulgA -expgSr -mulgA (mulgA (y ^+n)).
rewrite (commute_expnm n  n commy).
rewrite -mulgA (mulgA _ y) -expgSr; rewrite 2!mulgA -expgn_add.
congr ((_ ^+ _ ) * _ * _); case: n => // n.
by rewrite -{1}add2n mulnC muln_addl mul2n half_add odd_double half_double addnC.
(* by rewrite -!dvdn2_half addnC -divn_addl_mul //=; congr (_ %/ 2); ring. *)
Qed.

End Commutator_powers.

Section Commutators_and_centralizers.
Variable T: finGroupType.
(* should not be a group but a set *)
Variable H: group T.

Check centraliser.

Lemma commg_to_centraliser: forall y, (forall x, x \in H -> [~ x, y ] = 1 ) ->
    H \subset C_(H)[y].
Proof.
move => y comm1.
apply/subsetP => x0 xinH; rewrite /centraliser in_set; apply/andP.
split; first by [].
by apply/centg1P; apply /commgP; apply/eqP; apply:comm1.
Qed.

Lemma centraliser_to_commg: forall x y, x \in C_(H)[y] -> [~ x, y] = 1.
Proof.
rewrite /centraliser => x y.
by case/setIP=> inx comm; apply/eqP; apply/commgP; apply/centg1P. 
Qed.

End Commutators_and_centralizers.

(***** Set theoretic commutators *****)
Section Commutator_properties.
Variable T: finGroupType.

Lemma sub_sgcomm: forall (H K : set T), [~: H, K] \subset [~: K, H].
Proof.
move=> H K.
rewrite /commutator; apply /subsetP=> c; move /generatedP=> cin.
apply: cin; rewrite {c} /=; apply /subsetP=> c.
rewrite {1}/commg_set; move/imset2P; case => h k hin kin ceq.
rewrite -groupV /=; suff lem: (c^-1 \in commg_set K H).
  by move:c^-1 lem; apply /subsetP; apply sub_geng.
rewrite ceq commg_inv.
by rewrite /commg_set; apply/imset2P; apply: (Imset2spec kin hin).
Qed.

Theorem sym_sgcomm: forall (H K : set T), [~: H, K] = [~: K, H].
Proof.
move=> H K; apply /setP => x.
by apply/idP/idP; move:x; apply /subsetP; apply sub_sgcomm.
Qed.

(* a couple of lemmas about set conjugation *)
Lemma subset_conjugate_of: forall (H K: set T) (z: T), 
H:^ z \subset K -> H \subset K:^ z^-1.
Proof.
move=> H K z sub.
by rewrite -(conjsg1 H) -(mulgV z) conjsgM conjSg.
Qed.

Lemma subset_conjugate_of2: forall (H K: set T) (z: T), 
H \subset K:^ z^-1 -> H:^z \subset K.
Proof.
move=> H K z sub.
by rewrite -(conjsg1 K) -(mulVg z) conjsgM conjSg.
Qed.

Lemma generated_conjg: forall (H :set T) (z: T),  
<<H>>:^z \subset << H:^z>>.
Proof.
move => H z.
apply: subset_conjugate_of2; apply/subsetP => x; move/generatedP => h.
apply: h; apply: subset_conjugate_of; apply: sub_geng.
Qed.

Lemma commg_subset: forall H K: group T, [~: H, K] \subset << H :|: K >>.
Proof.
move=> H K; 
rewrite /commutator; apply/subsetP => c; move /generatedP; apply {c}.  
apply/subsetP => c; rewrite/commg_set; move/imset2P; case => h k hin kin ceq.
apply/generatedP; move => G; rewrite subUset; move/andP=> HKsubG.
case HKsubG => HsubG KsubG; rewrite ceq {ceq} /commg.
apply: groupM; first by  apply: groupVr; move : h hin; apply/subsetP.
rewrite /conjg; apply groupM; first by  apply: groupVr; move : k kin; apply/subsetP.
apply: groupM; first by  move : h hin; apply/subsetP.
by  move : k kin; apply/subsetP.
Qed.

Theorem normal_commutator: forall H K: group T, [~: H, K] <| << H :|: K >>.
Proof.
move=> H K.
rewrite /normal_subset; apply/andP; split; first by apply: commg_subset.
apply/subsetP=> z; move/generatedP => zinG.
apply: {z} zinG; apply/subsetP => z; rewrite !in_set /commutator.
move /orP => zinHorK.
suff lem: (<<(commg_set H K):^ z >> \subset <<commg_set H K>>).
  by apply: (subset_trans (generated_conjg _ _ ) lem).
apply /subsetP => c; move /generatedP; apply.
rewrite /= /conjugate_of; apply /subsetP => {c} c. 
move /imsetP; elim => x.
rewrite /commg_set.
move/imset2P; case => h k hin kin xeq ceq.
apply /generatedP => G; move /subsetP => sub.
case zinHorK => zin.
- have ceq1: c = [~ h * z, k] * [~ z, k]^-1.
    by rewrite commg_gmult_left -mulgA mulgV mulg1 ceq xeq.
  rewrite ceq1; apply: groupM.
  + by apply: sub; apply /imset2P; apply: (Imset2spec (groupM hin zin ) kin).
  + by apply: groupVr; apply sub; apply /imset2P; apply: (Imset2spec zin  kin).
- have ceq1: c = [~ h, z] ^-1 * [~ h, k * z].
    by rewrite commg_gmult_right mulgA mulVg mul1g ceq xeq.
  rewrite ceq1; apply: groupM.
  + by apply: groupVr; apply sub; apply /imset2P; apply: (Imset2spec hin zin).
  + by apply: sub; apply /imset2P; apply: (Imset2spec hin (groupM kin zin )).
Qed.

Lemma normalized_commutator1: forall H K: group T, H \subset 'N(K) -> [~: H, K] \subset K.
Proof.
move=> H K. move /normalP=> Hsub; rewrite /commutator /commg_set.
apply /subsetP=> c; move /generatedP; apply {c}. 
apply /subsetP=> c. move /imset2P; case => h k hin kin ceq.
rewrite ceq commg_eq2; apply: groupM; last done.
suff g: k^-1 ^ h \in K:^ h.
  move: (k^-1 ^ h) g; apply /subsetP; rewrite (Hsub _ hin); apply subset_refl_hint.
rewrite /conjugate_of; apply/imsetP; exists k^-1; last done.
by apply: groupVr.
Qed.

Lemma normalized_commutator2: forall H K: group T, [~: H, K] \subset K -> H \subset 'N(K).
Proof.
move=> H K. 
rewrite sym_sgcomm /commutator; move /subsetP=> subK.
rewrite /normaliser; apply /subsetP => h hin.
rewrite in_set; apply /subsetP =>x. 
move/imsetP; case => k kin ->. 
rewrite conjg_as_commg; apply: groupM; first done; apply: subK; apply: mem_geng.
by rewrite /commg_set; apply/imset2P; apply: (Imset2spec kin hin).
Qed.

Lemma gen_setl: forall H: set T, <<H>> = [set 1] -> H \subset [set 1].
Proof.
move=> H eq_gen.
by have sgH:= sub_geng H; rewrite eq_gen in sgH; apply: sgH.
Qed.

Lemma gen_setr: forall H:set T, H \subset [set 1] -> <<H>> = [set 1].
Proof.
move=> H subH; apply/setP => x; apply/idP/idP.
- move :x; apply /subsetP. by rewrite gen_subG. 
- by move/set1P=> xis1; rewrite xis1; apply: (group1 (generated_group H)).
Qed.

Lemma eq_commg_1_to_eq_commutator_1: forall H K L: set T,
(forall h k l, h \in H -> k \in K -> l \in L -> 1=[~ h, k, l]) ->[~: H, K, L ] =[set 1].
Proof.
move=> H K L comm.
rewrite /commutator; apply gen_setr; apply/subsetP => hkl; rewrite !in_set.
move/imset2P; case => hk l. 
move /generatedP=> hkin lin hkleq.
apply /eqP; rewrite hkleq {hkleq}.
apply: (@centraliser_to_commg _ (commutator_group H K)).
apply: hkin; apply/subsetP=> z. 
rewrite/commg_set; move/imset2P; case => h k hin kin zeq. 
apply/setIP; split. 
- rewrite //= /commutator; apply: (subsetP (sub_geng _)).
  by apply/imset2P; apply: (Imset2spec hin kin).
- rewrite //= /normaliser in_set; apply/subsetP => x; rewrite/conjugate_of. 
  move/imsetP; case => x0; move /set1P => -> ->.
  rewrite /conjg -(@commg_to_commute _ z l). 
  - by rewrite mulgA mulVg mul1g; apply/set1P.
  - by rewrite zeq; apply:sym_eq; apply comm.
Qed.

Lemma eq_commutator_1_to_eq_commg_1: forall H K L: set T, 
[~: H, K, L] = [set 1] -> forall (h k l: T), h \in H -> k \in K -> l \in L -> [~ h, k, l] = 1.
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

Theorem big_hall_witt_identity: forall H K L: group T,
  [~: H, K, L ] = [set 1] -> [~: K, L, H] = [set 1]  -> [~: L, H, K] = [set 1].
Proof.
move=> H K L eq1 eq2.
apply: eq_commg_1_to_eq_commutator_1 => l h k lin hin kin.
apply: sym_eq. rewrite -(invgK h).
apply: (@conjg_to_eq1 _ _ (h^-1)).
have hall_witt:= hall_witt_identity h^-1 k l.
have hkl: [~ h^-1, k^-1, l] = 1.
  by apply: (eq_commutator_1_to_eq_commg_1 eq1) ;  do ? apply: groupVr.
have klh: [~ k, l^-1, h^-1] = 1.
  by apply: (eq_commutator_1_to_eq_commg_1 eq2) ; do ? apply: groupVr.
by rewrite hkl conj1g mul1g klh conj1g mul1g in hall_witt.
Qed.

End Commutator_properties.

Section Specialized_results.
Variable T: finGroupType.
Variable G: group T.
Variables x y z: T.
Hypothesis xinG: x \in G.
Hypothesis yinG: y \in G.
Hypothesis zinG: z \in G.

Lemma tech1: commute y z -> (abel [~: [set x], G]) -> [~ x, y, z] = [~ x, z, y].
Proof.
move=> comm; move /abelP=> abl.
have lem: forall w, w \in G -> [~ x^-1, w] \in [~: [set x], G].
  have eqinv: exists m, x^-1 = (x ^+ m).
    exists (orderg x).-1; apply: (mulg_injl x).
    rewrite mulgV -{1}(expg1 x) -expgn_add addnC addn1.
    rewrite prednK; last by apply: orderg_pos.
    apply: sym_eq; apply: orderg_expn1.
  case: eqinv=> m ->.
  elim m; first by move => w winG; rewrite /= commg1l; apply: group1.
  move=> n indh w winG; rewrite commg_gmultl.
  apply: groupM; last by apply: indh.
  apply: groupM.
  - rewrite /= /commutator; apply /generatedP => G0.
    move /subsetP=> sub; apply: sub. 
    rewrite /commg_set. apply/imset2P; apply:(Imset2spec _ winG); last by reflexivity.
    by apply/set1P.
  - rewrite -(groupV _ [~ x, w, x ^+ n]) commg_inv; apply: indh. 
    by rewrite /commg /conjg; do ! apply: groupM; do ? apply: groupVr.
have lem2: [~ x, y, z] = x^-1 * [~ x^-1, y] * [~ x^-1, z] * z^-1 * y^-1 * x * y * z.
  by rewrite /commg /conjg ! invMg !mulgA -(mulgA _ z) !mulgV mul1g mulg1 !invgK.
(* rewrite /abelian. /com in abl; rewrite lem2. *)
rewrite lem2.
rewrite -(mulgA x^-1) (abl [~ x^-1, y] _ [~ x^-1, z]).
- rewrite {1 2}/commg !invgK. 
  rewrite -(mulgA x) (mulgA x^-1) mulVg mul1g mulgA -commg_eq2.
  rewrite -(mulgA _ _ y^-1) -invMg comm invMg mulgA.
  rewrite /conjg -(mulgA [~ z, x]) -(mulgA _ _ y^-1) -(mulgA _ _ y^-1) mulgV mulg1.
  rewrite -mulgA comm mulgA -!(mulgA [~ z, x]) -!(mulgA y^-1). 
  rewrite -2!(mulgA x^-1) -(mulgA z^-1)  -/(conjg x z) -/(commg x z).
  by rewrite -/(conjg [~ x, z] y) -commg_inv.
- by apply lem.
- by apply lem.
Qed.

Lemma tech2: commute [~ x, y] x -> commute [~ x, y] y ->[~ x, y]^-1 = [~ x^-1, y].
Proof.
move=> commx commy.
have lem: [~ x, y, x^-1] = 1.
  apply/eqP; apply/commgP; rewrite /commute; apply (mulg_injl x).
  by rewrite 2!mulgA -commx -mulgA mulgV mul1g mulg1.
rewrite -(mulg1 [~ x, y] ^-1); apply (@canLR _ _ _ _ 1 [~ x^-1, y] (mulKg [~ x, y])).
by rewrite -(mulg1 [~ x, y]) -{2}lem -commg_gmultl mulgV commg1l.
Qed.

Lemma tech3: commute [~ x, y] x -> commute [~ x, y] y ->[~ x, y]^-1 = [~ x, y^-1].
Proof.
move=> commx commy.
have lem: [~ x, y, y^-1] = 1.
  apply/eqP; apply/commgP; rewrite /commute; apply (mulg_injl y).
  by rewrite 2!mulgA -commy -mulgA mulgV mul1g mulg1.
rewrite -(mul1g [~ x, y] ^-1); apply (@canLR _ _ _ _ 1 [~ x,y^-1] (mulgK [~ x, y])).
by rewrite -(mulg1 [~ x, y]) mulgA -{2}lem -commg_gmultr mulgV commg1r.
Qed.

End Specialized_results.

