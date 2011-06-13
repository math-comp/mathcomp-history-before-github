(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup frobenius.
Require Import matrix mxalgebra mxrepresentation vector algC classfun character.
Require Import inertia vcharacter PFsection1.

(******************************************************************************)
(* This file covers Peterfalvi, Section 2: the Dade isometry                  *)
(* Defined here:                                                              *)
(*   Dade_hypothesis G L A H <-> G, L, A and H satisfy the hypotheses under   *)
(*                               which the Dade isometry relative to G, L and *)
(*                               A is well-defined.                           *)
(* For ddH : Dade_hypothesis G L A H, we also define                          *)
(*             Dade ddH == the Dade isometry relative to G, L and A.          *)
(*  Dade_support1 ddH a == the set of elements identified with a by the Dade  *)
(*                         isometry.                                          *)
(*     Dade_support ddH == the natural support of the Dade isometry.          *)
(* The following are used locally in expansion of the Dade isometry as a sum  *)
(* of induced characters:                                                     *)
(*         Dade_transversal ddH == a transversal of the L-conjugacy classes   *)
(*                                 of non empty subsets of A.                 *)
(*    Dade_set_signalizer ddH B == the generalization of H to B \subset A,    *)
(*                                 denoted 'H(B) below.                       *)
(*    Dade_set_normalizer ddH B == the generalization of 'C_G[a] to B.        *)
(*                                 denoted 'M(B) = 'H(B) ><| 'N_L(B) below.   *)
(*    Dade_cfun_restriction ddH B aa == the composition of aa \in 'CF(L, A)   *)
(*                                 with the projection of 'M(B) onto 'N_L(B), *)
(*                                 parallel to 'H(B).                         *)
(* In addition, if sA1A : A1 \subset A and nA1L : L \subset 'N(A1), we have   *)
(*  restr_Dade_hyp ddH sA1A nA1L : Dade_hypothesis G L A1 H                   *)
(*      restr_Dade ddH sA1A nA1L == the restriction of the Dade isometry to   *)
(*                                  'CF(L, A1).                               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

Section Two.

Variable gT : finGroupType.

(* This is Peterfalvi (2.1). *)
Lemma partition_cent_rcoset (H : {group gT}) g (C := 'C_H[g]) (Cg := C :* g) :
    g \in 'N(H) -> coprime #|H| #[g] ->
  partition (Cg :^: H) (H :* g) /\ #|Cg :^: H| = #|H : C|.
Proof.
move=> nHg coHg; pose pi := \pi(#[g]).
have notCg0: Cg != set0 by apply/set0Pn; exists g; exact: rcoset_refl.
have id_pi: {in Cg, forall u, u.`_ pi = g}.
  move=> _ /rcosetP[u /setIP[Hu cgu] ->]; rewrite consttM; last exact/cent1P.
  rewrite (constt_p_elt (pgroup_pi _)) (constt1P _) ?mul1g //.
  by rewrite (mem_p_elt _ Hu) // /pgroup -coprime_pi' // coprime_sym.
have{id_pi} /andP[tiCg /eqP defC]: normedTI Cg H C.
  apply/normedTI_P; rewrite // subsetI subsetIl normsM ?normG ?subsetIr //.
  split=> // x Hx /pred0Pn[u /andP[/= Cu Cxu]]; rewrite !inE Hx /= conjg_set1.
  by rewrite -{2}(id_pi _ Cu) -(conjgKV x u) consttJ id_pi -?mem_conjg.
have{tiCg} partCg := partition_class_support notCg0 tiCg.
have{defC} oCgH: #|Cg :^: H| = #|H : C| by rewrite -defC -astab1Js -card_orbit.
split=> //; congr (partition _ _): (partCg); apply/eqP.
rewrite eqEcard card_rcoset {1}class_supportEr; apply/andP; split.
  apply/bigcupsP=> x Hx; rewrite conjsgE -rcosetM conjgCV rcosetM mulgA.
  by rewrite mulSg ?mul_subG ?subsetIl // sub1set ?memJ_norm ?groupV.
have oCg Cx: Cx \in Cg :^: H -> #|Cx| = #|C|.
  by case/imsetP=> x _ ->; rewrite cardJg card_rcoset.
by rewrite (card_uniform_partition oCg partCg) oCgH mulnC LaGrange ?subsetIl.
Qed.

(* This is Peterfalvi Definition (2.2). *)
Inductive Dade_hypothesis G L (H : gT -> {group gT}) (A : {set gT}) :=
  DadeHypothesis of
    A \subset L^# & L \subset 'N_G(A)
 & (*a*) {in A & G, forall a g,
          a ^ g \in A -> exists2 k, k \in L & a ^ g = a ^ k}
 & (*b*) {in A, forall a, H a ><| 'C_L[a] = 'C_G[a]}
 & (*c*) {in A &, forall a b, coprime #|H a| #|'C_L[b]| }.

Variables (G L : {group gT}) (H : gT -> {group gT}).

Section Definitions.

Variables (A : {set gT}) (ddA : Dade_hypothesis G L H A).

Definition Dade_support1 of Dade_hypothesis G L H A :=
  fun a => class_support (H a :* a) G.

(* This is Peterfalvi Definition (2.5). *)
Definition Dade (alpha : {cfun gT}) : {cfun gT} :=
  [ffun x => oapp alpha 0 [pick a \in A | x \in Dade_support1 ddA a]].

Lemma Dade_is_linear : linear Dade.
Proof.
move=> mu alpha beta; apply/ffunP=> x; rewrite !ffunE.
by case: pickP => [a _ | _] /=; rewrite ?scaler0 ?addr0 ?ffunE.
Qed.

Canonical Structure Dade_additive := Additive Dade_is_linear.
Canonical Structure Dade_linear := Linear Dade_is_linear.

End Definitions.

Variable A : {set gT}.

(* This is Peterfalvi (2.3). *)
Lemma Dade_TI_P : A \subset G^# -> A != set0 -> {in A, forall a, H a :=: 1%g} ->
  reflect (Dade_hypothesis G L H A) (normedTI A G L).
Proof.
move=> /subsetD1P[sAG notA1] notA0 trivH.
apply: (iffP idP) => [tiAG | [_ /subsetIP[sLG nAL] /= conjA_L defCa _]].
  have [tiAG_L sLG] := normedTI_memJ_P notA0 tiAG.
  split=> // [||a g Aa Gg /= Aag | a Aa | a b Aa _]; last 1 first.
  - by rewrite trivH // cards1 coprime1n.
  - rewrite subsetD1 notA1 andbT /=; apply/subsetP=> a Aa.
    by rewrite -(tiAG_L a) ?(subsetP sAG) // conjgE mulKg.
  - by case/normedTI_P: tiAG.
  - by exists g; rewrite -?(tiAG_L a).
  apply/eqP; rewrite trivH // sdprod1g eqEsubset setSI //.
  apply/subsetP=> g /setIP[Gg cag]; rewrite inE cag -(tiAG_L a g) //.
  by rewrite conjgE -(cent1P cag) mulKg Aa.
apply/normedTI_memJ_P=> //; split=> // a g Aa Gg.
apply/idP/idP=> [Aag | Lg]; last by rewrite memJ_norm ?(subsetP nAL).
have [k Lk def_ag] := conjA_L a g Aa Gg Aag.
suffices: (g * k^-1)%g \in 'C_G[a].
  by rewrite -defCa ?trivH // sdprod1g; case/setIP; rewrite groupMr ?groupV.
rewrite !inE groupM ?groupV // ?(subsetP sLG) //=.
by rewrite conjg_set1 conjgM def_ag conjgK.
Qed.

Hypothesis ddA : Dade_hypothesis G L H A.

Local Notation dd1 := (Dade_support1 ddA).

Let sAL : A \subset L. Proof. by have [/subsetD1P[]] := ddA. Qed.
Let notA1 : 1%g \notin A. Proof. by have [/subsetD1P[]] := ddA. Qed.
Let sLG : L \subset G. Proof. by have [_ /subsetIP[]] := ddA. Qed.
Let nAL : L \subset 'N(A). Proof. by have [_ /subsetIP[]] := ddA. Qed.
Let conjAG : {in A & G, forall a g,
        a ^ g \in A -> exists2 k, k \in L & a ^ g = a ^ k}.
Proof. by case: ddA. Qed.
Let defCa : {in A, forall a, H a ><| 'C_L[a] = 'C_G[a]}.
Proof. by case: ddA. Qed.
Let coHL : {in A &, forall a b, coprime #|H a| #|'C_L[b]| }.
Proof. by case: ddA. Qed.
Let nsHC : {in A, forall a, H a <| 'C_G[a]}.
Proof. by move=> a /defCa/sdprod_context[]. Qed.
Let sHG : {in A, forall a, H a \subset G}.
Proof. by move=> a /nsHC/normal_sub/subsetIP[]. Qed.
Let notHa0 a : H a :* a :!=: set0.
Proof. by rewrite -cards_eq0 -lt0n card_rcoset cardG_gt0. Qed.

(* This is Peterfalvi (2.4), with an essential strengthening of part (c),    *)
(* which asserts that the Dade cover sets are TI-subsets of G.               *)
Lemma Dade_conjg :
  [/\ (*a*) {in A & L, forall a x, H (a ^ x) :=: H a :^ x},
      (*b*) {in A &, forall a b,
             ~~ [disjoint dd1 a & dd1 b] -> exists2 x, x \in L & b = a ^ x}
   &  (*c*) {in A, forall a, normedTI (H a :* a) G 'C_G[a]}].
Proof.
pose pi := [pred p | existsb a, (a \in A) && (p \in \pi('C_L[a]))].
have pi'H: {in A, forall a, pi^'.-group (H a)}.
  move=> a Aa; apply/pgroupP=> p p_pr; apply: contraL; case/exists_inP=> b Ab.
  rewrite mem_primes p_pr cardG_gt0 /= => p_dv_L.
  by rewrite -prime_coprime // coprime_sym (coprime_dvdr p_dv_L) ?coHL.
have piL: {in A, forall a, pi.-group 'C_L[a]}.
  move=> a Aa; apply: sub_pgroup (pgroup_pi _) => p piLp.
  by apply/exists_inP; exists a.
have pi_Ha a u: a \in A -> u \in H a :* a -> u.`_pi = a.
  move=> Aa /rcosetP[{u}u Hu ->].
  have pi_a: pi.-elt a.
    by rewrite (mem_p_elt (piL a Aa)) // inE cent1id (subsetP sAL).
  have cua: u \in 'C[a] by case/setIP: (subsetP (normal_sub (nsHC Aa)) u Hu).
  rewrite (consttM _ (cent1P cua)) (constt_p_elt pi_a) (constt1P _) ?mul1g //.
  exact: mem_p_elt (pi'H a Aa) Hu.
have defH: {in A, forall a, H a :=: 'O_pi^'('C_G[a])}.
  move=> a Aa; have [_ mulHC _ _] := sdprodP (defCa Aa).
  have [hallH _] := coprime_mulGp_Hall mulHC (pi'H a Aa) (piL a Aa).
  by rewrite -(normal_Hall_pcore hallH) ?nsHC.
split=> [a x Aa Lx /= | a b Aa Ab | a Aa].
- rewrite !defH ?memJ_norm ?(subsetP nAL) //.
  by rewrite -pcoreJ conjIg (conjGid (subsetP sLG x Lx)) -normJ conjg_set1.
- case/pred0Pn=> _ /andP[/imset2P[x u Ha_u Gx ->] /imset2P[y v Ha_v Gy]].
  move/(congr1 (fun w => w.`_pi)); rewrite !consttJ (pi_Ha a) // (pi_Ha b) //.
  move/(canLR (conjgK _)); rewrite -conjgM => def_b; rewrite -def_b in Ab *.
  by apply: conjAG; rewrite // groupM ?groupV.
apply/normedTI_P=> //; split=> [g Gg|]; last first.
  by rewrite subsetI subsetIl normsM ?subsetIr ?normal_norm ?nsHC.
rewrite disjoint_sym; case/pred0Pn=> /= _ /andP[/imsetP[u Ha_u ->] Ha_ug].
by rewrite !inE Gg conjg_set1 -{1}(pi_Ha a u) //= -consttJ (pi_Ha a).
Qed.

(* This is Peterfalvi (2.4)(a). *)
Lemma DadeJ : {in A & L, forall a x, H (a ^ x) :=: H a :^ x}.
Proof. by case: Dade_conjg. Qed.

(* This is Peterfalvi (2.4)(b). *)
Lemma Dade_support1_TI : {in A &, forall a b,
    ~~ [disjoint Dade_support1 ddA a & Dade_support1 ddA b] ->
  exists2 x, x \in L & b = a ^ x}.
Proof. by case: Dade_conjg. Qed.

Lemma Dade_cover_TI : {in A, forall a, normedTI (H a :* a) G 'C_G[a]}.
Proof. by case: Dade_conjg. Qed.

(* This is Peterfalvi (2.4)(c). *)
Lemma norm_Dade_cover : {in A, forall a, 'N_G(H a :* a) = 'C_G[a]}.
Proof. by move=> a /Dade_cover_TI /andP[_ /eqP]. Qed.

Local Notation "alpha ^\tau" := (Dade ddA alpha)
  (at level 2, format "alpha ^\tau").

(* This is the validity of Peterfalvi, Definition (2.5) *)
Lemma DadeE alpha a u :
  alpha \in 'CF(L, A) -> a \in A -> u \in dd1 a -> alpha^\tau u = alpha a.
Proof.
move=> /cfun_memfP[_ CFalpha] Aa Ha_u; rewrite ffunE.
have [b /= /andP[Ab Hb_u] | ] := pickP; last by move/(_ a); rewrite Aa Ha_u.
have [|x Lx ->] := Dade_support1_TI Aa Ab; last by rewrite CFalpha.
by apply/pred0Pn; exists u; rewrite /= Ha_u.
Qed.

Lemma Dade_id : {in 'CF(L, A) & A, forall alpha a, alpha^\tau a = alpha a}.
Proof.
move=> alpha a CFalpha Aa; apply: DadeE => //.
by rewrite (subsetP (sub_class_support _ _)) // rcoset_refl.
Qed.

Definition Dade_support := \bigcup_(a \in A) dd1 a.
Local Notation Atau := Dade_support.

Lemma support_Dade alpha : support alpha^\tau \subset Atau.
Proof.
apply/subsetP=> x; rewrite !inE; apply: contraR; rewrite ffunE.
by case: pickP => [a /andP[Aa Ha_x] /bigcupP[] | //=]; exists a.
Qed.

Lemma not_support_Dade_1 : 1%g \notin Atau.
Proof.
apply: contra notA1 => /bigcupP[a Aa /imset2P[u x Ha_u _ ux1]].
suffices /set1P <-: a \in [1] by [].
have [_ _ _ <-] := sdprodP (defCa Aa).
rewrite 2!inE cent1id (subsetP sAL) // !andbT.
by rewrite -groupV -(mul1g a^-1)%g -mem_rcoset -(conj1g x^-1) ux1 conjgK.
Qed.

Lemma Dade1 alpha : alpha^\tau 1%g = 0.
Proof. by rewrite (off_support (support_Dade _) not_support_Dade_1). Qed.

Lemma Dade_id1 : {in 'CF(L, A) & 1%g |: A,
  forall alpha a, alpha^\tau a = alpha a}.
Proof.
move=> alpha a CFalpha; case/setU1P=> [-> |]; last exact: Dade_id.
by rewrite Dade1 (cfunS0 CFalpha).
Qed.

Lemma Dade_support_sub : Atau \subset G.
Proof.
apply/bigcupsP=> a Aa; rewrite class_support_subG // mul_subG ?sHG //.
by rewrite sub1set (subsetP sLG) ?(subsetP sAL).
Qed.

Lemma Dade_cfunS alpha : alpha \in 'CF(L, A) -> alpha^\tau \in 'CF(G, Atau).
Proof.
move=> CFalpha; apply/cfun_memfP; split=> [u | u y Gy].
  rewrite (setIidPl Dade_support_sub).
  by move/(off_support (support_Dade alpha)).
rewrite [alpha^\tau u]ffunE; have [a /= /andP[Aa Ha_u] | no_a /=] := pickP.
  by rewrite (DadeE CFalpha Aa) // -mem_conjgV class_supportGidr ?groupV.
apply/(off_support (support_Dade _))/bigcupP=> [[a Aa]].
apply/negP/(contraFN _ (no_a a)); rewrite Aa -mem_conjgV.
by rewrite class_supportGidr ?groupV.
Qed.

Lemma Dade_cfun alpha : alpha \in 'CF(L, A) -> alpha^\tau \in 'CF(G).
Proof. by move/Dade_cfunS/memcW. Qed.

Lemma Dade_support1_id : {in A & L, forall a x, dd1 (a ^ x) = dd1 a}.
Proof.
move=> a x Aa Lx; rewrite {1}/Dade_support1 DadeJ // -conjg_set1 -conjsMg.
by rewrite class_supportGidl ?(subsetP _ x Lx) //; case ddA => _; case/subsetIP.
Qed.

(* This is Peterfalvi (2.7), main part *)
Lemma general_Dade_reciprocity alpha xi psi :
    alpha \in 'CF(L, A) -> xi \in 'CF(G) -> psi \in 'CF(L) ->
  {in A, forall a, psi a = #|H a|%:R ^-1 * (\sum_(x \in H a) xi (x * a)%g)} ->
  '[alpha^\tau, xi]_G = '[alpha, psi]_L.
Proof.
move=> CFalpha CFxi CFpsi psiA.
rewrite inner_prodE (big_setID Dade_support) /= addrC.
rewrite (setIidPr Dade_support_sub) big1 => [|x /setDP[_ notHx]]; last first.
  by rewrite (cfunS0 (Dade_cfunS CFalpha)) ?mul0r.
pose T := [set repr (a ^: L) | a <- A].
have sTA: {subset T <= A}.
  move=> ax; case/imsetP=> a Aa ->; have [x Lx ->{ax}] := repr_class L a.
  by rewrite memJ_norm ?(subsetP nAL).
pose P_G := [set dd1 x | x <- T].
have dd1_id: {in A, forall a, dd1 (repr (a ^: L)) = dd1 a}.
  by move=> a Aa /=; have [x Lx ->] := repr_class L a; exact: Dade_support1_id.
have ->: Atau = cover P_G.
  apply/setP=> u; apply/bigcupP/bigcupP=> [[a Aa Fa_u] | [Fa]]; last first.
    by case/imsetP=> a; move/sTA=> Aa -> Fa_u; exists a. 
  by exists (dd1 a) => //; rewrite -dd1_id //; do 2!apply: mem_imset.
have [tiP_G inj_dd1]: trivIset P_G /\ {in T &, injective dd1}.
  apply: trivIimset => [_ _ /imsetP[a Aa ->] /imsetP[b Ab ->] |]; last first.
    apply/imsetP=> [[a]]; move/sTA=> Aa; move/esym; move/eqP; case/set0Pn.
    by exists (a ^ 1)%g; apply: mem_imset2; rewrite ?group1 ?rcoset_refl.
  rewrite !dd1_id //; apply: contraR.
  by case/Dade_support1_TI=> // x Lx ->; rewrite classGidl.
have big_andT := eq_bigl _ _ (fun _ => andbT _).
rewrite add0r -big_andT big_trivIset //= big_imset {P_G tiP_G inj_dd1}//=.
symmetry; rewrite inner_prodE (big_setID A) (setIidPr sAL) /= addrC.
rewrite big1 ?add0r => [|x /setDP[_ notAx]]; last first.
  by rewrite (cfunS0 CFalpha) ?mul0r.
pose P_A := [set a ^: L | a <- T].
have rLid: forall x, repr (x ^: L) ^: L = x ^: L.
  by move=> x; have [y Ly ->] := repr_class L x; rewrite classGidl.
have {1}<-: cover P_A = A.
  apply/setP=> a; apply/bigcupP/idP=> [[_ /imsetP[d /sTA Ab ->]] | Aa].
    by case/imsetP=> x Lx ->; rewrite memJ_norm ?(subsetP nAL).
  by exists (a ^: L); rewrite ?class_refl // -rLid; do 2!apply: mem_imset.
have [tiP_A injFA]: trivIset P_A /\ {in T &, injective (class^~ L)}.
  apply: trivIimset => [_ _ /imsetP[a Aa ->] /imsetP[b Ab ->] |]; last first.
    by apply/imsetP=> [[a _ /esym/eqP/set0Pn[]]]; exists a; exact: class_refl.
  rewrite !rLid; apply: contraR => /pred0Pn[c /andP[/=]].
  by do 2!move/class_transr <-.
rewrite -big_andT big_trivIset //= big_imset {P_A tiP_A injFA}//=.
apply: canRL (mulKf (neq0GC G)) _; rewrite mulrA big_distrr /=.
apply: eq_bigr => a /sTA=> {T sTA}Aa.
have [La def_Ca] := (subsetP sAL a Aa, defCa Aa).
rewrite !big_andT (eq_bigr (fun _ => alpha a * (psi a)^*)) => [|ax]; last first.
  by case/imsetP=> x Lx ->{ax}; rewrite (cfunJ _ CFalpha) ?(cfunJ _ CFpsi).
rewrite sumr_const -index_cent1 mulrC -mulr_natr -!mulrA.
rewrite (eq_bigr (fun xa => alpha a * (xi xa)^*)) => [|xa Fa_xa]; last first.
  by rewrite (DadeE CFalpha Aa).
rewrite -big_distrr /= -rmorph_sum; congr (_ * _).
rewrite mulrC mulrA -natr_mul mulnC -(LaGrange (subsetIl G 'C[a])).
rewrite -mulnA mulnCA -(sdprod_card def_Ca) -mulnA LaGrange ?subsetIl //.
rewrite mulnA natr_mul mulfK ?neq0GC // -conjC_nat -rmorphM; congr (_ ^*).
have /andP[tiHa _] := Dade_cover_TI Aa.
rewrite -big_andT (set_partition_big _ (partition_class_support _ _)) //=.
rewrite (eq_bigr (fun _ => \sum_(x \in H a) xi (x * a)%g)) => [|Vx]; last first.
  case/imsetP=> x Gx ->{Vx}; rewrite big_andT -rcosetE.
  rewrite (big_imset _ (in2W (conjg_inj x))) (big_imset _ (in2W (mulIg a))) /=.
  by apply: eq_bigr => u Hu; rewrite (cfunJ _ CFxi) ?groupM ?(subsetP sLG a).
rewrite sumr_const card_orbit astab1Js norm_Dade_cover //.
by rewrite natr_mul -mulrA mulr_natl psiA // mulVKf ?neq0GC.
Qed.

(* This is Peterfalvi (2.7), second part. *)
Lemma Dade_reciprocity alpha xi :
    alpha \in 'CF(L, A) -> xi \in 'CF(G) ->
    {in A, forall a, {in H a, forall u, xi (u * a)%g = xi a}} ->
  '[alpha^\tau, xi]_G = '[alpha, 'Res[L] xi]_L.
Proof.
move=> CFalpha CFxi xiH; apply: general_Dade_reciprocity => // [|a Aa].
  exact: memc_restrict CFxi.
rewrite crestrictE ?(subsetP sAL) // mulrC.
rewrite (eq_bigr (fun _ => xi a)) ?sumr_const => [|u Hu]; last exact: xiH.
by rewrite -[_ *+ _]mulr_natr mulfK ?neq0GC.
Qed.

(* This is Peterfalvi (2.6)(a). *)
Lemma Dade_isometry : {in 'CF(L, A) &, forall alpha beta,
  '[alpha^\tau, beta^\tau]_G = '[alpha, beta]_L}.
Proof.
move=> alpha beta CFalpha CFbeta.
have sub_supp := subsetP (sub_class_support _ _).
rewrite /= Dade_reciprocity ?Dade_cfun => // [|a Aa u Hu]; last first.
  by rewrite !(DadeE CFbeta Aa) ?sub_supp ?rcoset_refl // mem_rcoset mulgK.
congr (_ * _); apply: eq_bigr => x Lx.
have [Ax | notAx] := boolP (x \in A); last by rewrite (cfunS0 CFalpha) ?mul0r.
by rewrite ffunE cfuniE Lx mul1r (DadeE CFbeta Ax) // sub_supp ?rcoset_refl.
Qed.

(* Supplement to Peterfalvi (2.3)/(2.6)(a); implies Isaacs Lemma 7.7. *)
Lemma Dade_Ind : {in A, forall a, H a :=: 1%g} -> 
  {in 'CF(L, A), forall alpha, alpha^\tau = 'Ind[G, L] alpha}.
Proof.
move=> trivH aa CFaaA; have CFaa := memcW CFaaA.
have [CFaa1 CFaa2] := (Dade_cfun CFaaA, memc_induced sLG CFaa).
rewrite -(sum_inner_prodE CFaa1) -(sum_inner_prodE CFaa2).
apply: eq_bigr => xi _.
rewrite -frobenius_reciprocity ?memc_irr //.
rewrite -Dade_reciprocity ?memc_irr // => a Aa u.
by rewrite trivH // => /set1P ->; rewrite mul1g.
Qed.

Definition Dade_set_signalizer (B : {set gT}) := \bigcap_(a \in B) H a.
Local Notation "''H' ( B )" := (Dade_set_signalizer B)
  (at level 8, format "''H' ( B )") : group_scope.
Canonical Structure Dade_set_signalizer_group B := [group of 'H(B)].
Definition Dade_set_normalizer B := 'H(B) <*> 'N_L(B).
Local Notation "''M' ( B )" := (Dade_set_normalizer B)
  (at level 8, format "''M' ( B )") : group_scope.
Canonical Structure Dade_set_normalizer_group B := [group of 'M(B)].

Let calP := [set B : {set gT} | (B \subset A) && (B != set0)].

(* This is Peterfalvi (2.8). *)
Lemma Dade_set_sdprod : {in calP, forall B, 'H(B) ><| 'N_L(B) = 'M(B)}.
Proof.
move=> B /setIdP[sBA notB0]; apply: sdprodEY => /=.
  apply/subsetP=> x /setIP[Lx nBx]; rewrite inE.
  apply/bigcapsP=> a Ba; have Aa := subsetP sBA a Ba.
  by rewrite sub_conjg -DadeJ ?groupV // bigcap_inf // memJ_norm ?groupV.
have /set0Pn[a Ba] := notB0; have Aa := subsetP sBA a Ba.
have [_ /mulG_sub[sHaC _] _ tiHaL] := sdprodP (defCa Aa).
rewrite -(setIidPl sLG) -setIA setICA (setIidPl sHaC) in tiHaL.
by rewrite setICA ['H(B)](bigD1 a) //= !setIA tiHaL !setI1g.
Qed.

Section DadeExpansion.

Variable aa : {cfun gT}.
Hypothesis CFaa : aa \in 'CF(L, A).

Definition Dade_cfun_restriction B : {cfun gT} :=
  [ffun x => if x \in 'M(B) then aa (remgr 'H(B) 'N_L(B) x) else 0].

Local Notation "''aa_' B" := (Dade_cfun_restriction B)
  (at level 3, B at level 2, format "''aa_' B") : ring_scope.

Definition Dade_transversal := [set repr (B :^: L) | B <- calP].
Local Notation calB := Dade_transversal.

Lemma Dade_restriction_classfun : {in calP, forall B, 'aa_B \in 'CF('M(B))}.
Proof.
move=> B /Dade_set_sdprod defMB.
apply/cfun_memfP; split=> /= [x | x y My].
  by rewrite setIid ffunE -if_neg => ->.
rewrite !ffunE groupJr //; case: ifP => //= Mx.
have [nsHN _ mulHN _ _] := sdprod_context defMB.
pose fB := Morphism (remgrM (sdprod_compl defMB) nsHN).
rewrite -[remgr _ _ _]/(fB _) morphJ //.
by rewrite (cfunJ _ CFaa) ?(subsetP (subsetIl L 'N(B))) ?mem_remgr ?mulHN.
Qed.
Local Notation CFaa_ := Dade_restriction_classfun.

Lemma Dade_restriction_char :
  is_char L aa -> {in calP, forall B, is_char 'M(B) 'aa_B}.
Proof.
case/is_charP=> d [rA def_aa] B /Dade_set_sdprod defMB.
have [nsHN _ mulHN _ _] := sdprod_context defMB.
pose fB := Morphism (remgrM (sdprod_compl defMB) nsHN).
have subNL: fB @* 'M(B) \subset L.
  apply/subsetP=> y; case/morphimP=> x /= _ Mx ->{y}.
  by rewrite (subsetP (subsetIl L 'N(B))) ?mem_remgr ?mulHN.
apply/is_charP; exists d; exists (morphim_repr (subg_repr rA subNL) (subxx _)).
apply/ffunP=> x //=; rewrite !ffunE -def_aa ffunE.
case Mx: (x \in 'M(B)); last by rewrite mul0r.
by rewrite (subsetP subNL) ?mul1r //; exact: mem_morphim.
Qed.

(* This is Peterfalvi (2.10.1) *)
Lemma Dade_Ind_restr_J : {in L & calP, forall x B,
  'Ind[G, 'M(B :^ x)] 'aa_(B :^ x) = 'Ind[G, 'M(B)] 'aa_B}.
Proof.
move=> x B Lx dB; have [defMB [sBA _]] := (Dade_set_sdprod dB, setIdP dB).
have dBx: B :^ x \in calP.
  by rewrite !inE -{2}(normsP nAL x Lx) conjSg -!cards_eq0 cardJg in dB *.
have defHBx: 'H(B :^ x) = 'H(B) :^ x.
  rewrite /'H(_) (big_imset _ (in2W (conjg_inj x))) -bigcapJ /=.
  by apply: eq_bigr => a Ba; rewrite DadeJ ?(subsetP sBA).
have defNBx: 'N_L(B :^ x) = 'N_L(B) :^ x by rewrite conjIg -normJ (conjGid Lx).
have [_ mulHNB _ tiHNB] := sdprodP defMB.
have defMBx: 'M(B :^ x) = 'M(B) :^ x.
  rewrite -mulHNB conjsMg -defHBx -defNBx.
  by case/sdprodP: (Dade_set_sdprod dBx).
have def_aa_x: forall y, 'aa_(B :^ x) (y ^ x) = 'aa_B y.
  move=> y /=; rewrite !ffunE defMBx memJ_conjg -mulHNB /=.
  have [[h z Hh Nz ->] | //] := altP mulsgP; have [Lz _] := setIP Nz.
  rewrite defHBx defNBx conjMg !remgrMid ?(cfunJ _ CFaa) ?memJ_conjg //.
  by rewrite -conjIg tiHNB conjs1g.
apply/ffunP=> y; rewrite !ffunE defMBx cardJg; congr (_ * _).
rewrite (reindex_astabs 'R x) ?astabsR ?(subsetP sLG) //=.
by apply: eq_bigr => z _; rewrite conjgM def_aa_x.
Qed.

(* This is Peterfalvi (2.10.2) *)
Lemma Dade_setU1 : {in calP & A, forall B a, 'H(a |: B) = 'C_('H(B))[a]}.
Proof.
move=> B a dB Aa; pose pi := \pi('C_L[a]).
rewrite /'H(_) bigcap_setU big_set1 -/'H(B).
have pi'H: {in A, forall b, pi^'.-group(H b)}.
  by move=> b Ab; rewrite /pgroup -coprime_pi' ?cardG_gt0 // coprime_sym coHL.
have [sHBG pi'HB]: 'H(B) \subset G /\ pi^'.-group('H(B)).
  have [sBA /set0Pn[b Bb]] := setIdP dB; have Ab := subsetP sBA b Bb.
  have sHBb: 'H(B) \subset H b by rewrite ['H(B)](bigD1 b) ?subsetIl.
  by rewrite (pgroupS sHBb) ?pi'H ?(subset_trans sHBb) ?sHG.
have [nsHa _ def_Ca _ _] := sdprod_context (defCa Aa).
have [_ caH] := subsetIP (normal_sub nsHa).
have [hallHa _] := coprime_mulGp_Hall def_Ca (pi'H a Aa) (pgroup_pi _).
apply/eqP; rewrite setIC eqEsubset setIS // subsetI subsetIl /=.
by rewrite (sub_normal_Hall hallHa) ?(pgroupS (subsetIl _ _)) ?setSI.
Qed.

Let calA g (X : {set gT}) := [set x \in G | g ^ x \in X]%g.

(* This is Peterfalvi (2.10.3) *)
Lemma Dade_Ind_expansion B g :
    B \in calP ->
  [/\ g \notin Atau -> ('Ind[G, 'M(B)] 'aa_B) g = 0
    & {in A, forall a, g \in dd1 a ->
       ('Ind[G, 'M(B)] 'aa_B) g =
          (aa a / #|'M(B)|%:R) *
               \sum_(b \in 'N_L(B) :&: a ^: L) #|calA g ('H(B) :* b)|%:R}].
Proof.
move=> dB; set LHS := ('Ind[G, _] _) g.
have ->: LHS = #|'M(B)|%:R^-1 * \sum_(x \in calA g 'M(B)) 'aa_B (g ^ x).
  rewrite [LHS]ffunE; congr (_ * _); rewrite (bigID [pred x | g ^ x \in 'M(B)]).
  rewrite /= addrC big1 ?add0r => [|x].
    by apply: eq_bigl => x; rewrite inE.
  by case/andP=> _ notMgx; rewrite (cfun0 (CFaa_ dB)).
have defMB := Dade_set_sdprod dB; have [_ mulHNB nHNB tiHNB] := sdprodP defMB.
have [sHMB sNMB] := mulG_sub mulHNB.
pose fBg x := remgr 'H(B) 'N_L(B) (g ^ x).
pose supp_aBg := [pred b \in A | g \in dd1 b].
have supp_aBgP: {in calA g 'M(B), forall x,
  ~~ supp_aBg (fBg x) -> 'aa_B (g ^ x)%g = 0}.
- move=> x /setIdP[]; set b := fBg x => Gx MBgx notHGx; rewrite ffunE MBgx. 
  have Nb: b \in 'N_L(B) by rewrite mem_remgr ?mulHNB.
  have Cb: b \in 'C_L[b] by rewrite inE cent1id; have [-> _] := setIP Nb.
  rewrite (cfunS0 CFaa) // -/(fBg x) -/b; apply: contra notHGx => Ab.
  have nHb: b \in 'N('H(B)) by rewrite (subsetP nHNB).
  have [sBA /set0Pn[a Ba]] := setIdP dB; have Aa := subsetP sBA a Ba.
  have [|/= partHBb _] := partition_cent_rcoset nHb.
    rewrite (coprime_dvdr (order_dvdG Cb)) //= ['H(B)](bigD1 a) //=.
    by rewrite (coprimeSg (subsetIl _ _)) ?coHL. 
  have Hb_gx: g ^ x \in 'H(B) :* b by rewrite mem_rcoset mem_divgr ?mulHNB.
  have [defHBb _ _] := and3P partHBb; rewrite -(eqP defHBb) in Hb_gx.
  case/bigcupP: Hb_gx => Cy; case/imsetP=> y HBy ->{Cy} Cby_gx.
  have sHBa: 'H(B) \subset H a by rewrite bigcap_inf.
  have sHBG: 'H(B) \subset G := subset_trans sHBa (sHG Aa).
  rewrite Ab -(memJ_conjg _ x) class_supportGidr //  -(conjgKV y (g ^ x)).
  rewrite mem_imset2 // ?(subsetP sHBG) {HBy}// -mem_conjg.
  apply: subsetP Cby_gx; rewrite {y}conjSg mulSg //.
  pose pi := \pi('C_L[b]).
  have pi'H: {in A, forall c, pi^'.-group (H c)}.
    by move=> c Ac; rewrite /pgroup -coprime_pi' ?cardG_gt0 // coprime_sym coHL.
  have [nsHbC _ defHbC _ _] := sdprod_context (defCa Ab).
  have [hallHb _] := coprime_mulGp_Hall defHbC (pi'H _ Ab) (pgroup_pi _).
  rewrite (sub_normal_Hall hallHb) ?setSI // (pgroupS _ (pi'H a Aa)) //=.
  by rewrite subIset ?sHBa.  
split=> [notHGg | a Aa Hag].
  rewrite big1 ?mulr0 // => x; move/supp_aBgP; apply; set b := fBg x.
  by apply: contra notHGg; case/andP=> Ab Hb_x; apply/bigcupP; exists b.
rewrite -mulrA mulrCA; congr (_ * _); rewrite big_distrr /=.
set nBaL := _ :&: _; rewrite (bigID [pred x | fBg x \in nBaL]) /= addrC.
rewrite big1 ?add0r => [|x /andP[calAx not_nBaLx]]; last first.
  apply: supp_aBgP => //; apply: contra not_nBaLx.
  set b := fBg x => /andP[Ab Hb_g]; have [Gx MBx] := setIdP calAx.
  rewrite inE mem_remgr ?mulHNB //; apply/imsetP/Dade_support1_TI => //.
  by apply/pred0Pn; exists g; exact/andP.
rewrite (partition_big fBg (mem nBaL)) /= => [|x]; last by case/andP.
apply: eq_bigr => b; case/setIP=> Nb aLb; rewrite mulr_natr -sumr_const.
apply: eq_big => x; rewrite ![x \in _]inE -!andbA.
  apply: andb_id2l=> Gx; apply/and3P/idP=> [[Mgx _] /eqP <- | HBb_gx].
    by rewrite mem_rcoset mem_divgr ?mulHNB.
  suffices ->: fBg x = b.
    by rewrite inE Nb (subsetP _ _ HBb_gx) // -mulHNB mulgS ?sub1set.
  by rewrite /fBg; have [h Hh ->] := rcosetP HBb_gx; exact: remgrMid.
move/and4P=> [_ Mgx _ /eqP def_fx].
rewrite ffunE Mgx -/(fBg x) def_fx; case/imsetP: aLb => y Ly ->.
by rewrite (cfunJ _ CFaa) // (subsetP sAL).
Qed.

(* This is Peterfalvi (2.10) *)
Lemma Dade_expansion :
  aa^\tau = - \sum_(B \in calB) (- 1) ^+ #|B| *: 'Ind[G, 'M(B)] 'aa_B.
Proof.
apply/ffunP=> g; rewrite !ffunE sum_ffunE ffunE.
pose n1 (B : {set gT}) : algC := (-1) ^+ #|B| / #|L : 'N_L(B)|%:R.
pose aa1 B := ('Ind[G, 'M(B)] 'aa_B) g.
have dBJ: {acts L, on calP | 'Js}.
  move=> x Lx /= B; rewrite !inE -!cards_eq0 cardJg.
  by rewrite -{1}(normsP nAL x Lx) conjSg.
transitivity (- (\sum_(B \in calP) n1 B * aa1 B)); last first.
  congr (- _); rewrite {1}(partition_big_imset (fun B => repr (B :^: L))) /=.
  apply: eq_bigr => B /imsetP[B1 dB1 defB].
  have B1L_B: B \in B1 :^: L by rewrite defB (mem_repr B1) ?orbit_refl.
  have{dB1} dB1L: {subset B1 :^: L <= calP}.
    by move=> _ /imsetP[x Lx ->]; rewrite dBJ.
  have dB: B \in calP := dB1L B B1L_B.
  rewrite (eq_bigl (mem (B :^: L))) => [|B2 /=]; last first.
    apply/andP/idP=> [[_ /eqP <-] | /(orbit_trans B1L_B) B1L_B2].
      by rewrite orbit_sym (mem_repr B2) ?orbit_refl.
    by rewrite [B2 :^: L](orbit_transl B1L_B2) -defB dB1L.
  rewrite (eq_bigr (fun _ => n1 B * aa1 B)) => [|_ /imsetP[x Lx ->]].
    rewrite ffunE sumr_const -mulr_natr mulrAC card_orbit astab1Js divfK //.
    by rewrite -neq0N_neqC -lt0n indexg_gt0.
  rewrite /aa1 Dade_Ind_restr_J //; congr (_ * _).
  by rewrite /n1 cardJg -{1 2}(conjGid Lx) normJ -conjIg indexJg.
case: pickP => /= [a /andP[Aa Ha_g] | notHAg]; last first.
  rewrite big1 ?oppr0 // /aa1 => B dB.
  have [->] := Dade_Ind_expansion g dB; first by rewrite mulr0.
  by apply/bigcupP=> [[a Aa Ha_g]]; case/andP: (notHAg a).
pose P_ b := [set B \in calP | b \in 'N_L(B)].
pose aa2 B b : algC := #|calA g ('H(B) :* b)|%:R.
pose nn2 (B : {set gT}) : algC := (-1) ^+ #|B| / #|'H(B)|%:R.
pose sumB b := \sum_(B \in P_ b) nn2 B * aa2 B b.
transitivity (- aa a / #|L|%:R * \sum_(b \in a ^: L) sumB b); last first.
  rewrite !mulNr; congr (- _).
  rewrite (exchange_big_dep (mem calP)) => [|b B _] /=; last by case/setIdP.
  rewrite big_distrr /aa1; apply: eq_bigr => B dB; rewrite -big_distrr /=.
  have [_ /(_ a) -> //] := Dade_Ind_expansion g dB; rewrite !mulrA.
  congr (_ * _); last by apply: eq_bigl => b; rewrite inE dB /= andbC -in_setI.
  rewrite -mulrA mulrCA -!mulrA; congr (_ * _).
  rewrite -invf_mul mulrCA -invf_mul -!natr_mul; congr (_ / _%:R).
  rewrite -(sdprod_card (Dade_set_sdprod dB)) mulnA mulnAC; congr (_ * _)%N.
  by rewrite mulnC LaGrange ?subsetIl.
rewrite (eq_bigr (fun _ => sumB a)) /= => [|_ /imsetP[x Lx ->]]; last first.
  rewrite {1}/sumB (reindex_inj (@conjsg_inj _ x)) /=.
  symmetry; apply: eq_big => B.
    rewrite ![_ \in P_ _]inE dBJ //.
    by rewrite -{2}(conjGid Lx) normJ -conjIg memJ_conjg.
  case/setIdP=> dB Na; have [sBA _] := setIdP dB.
  have defHBx: 'H(B :^ x) = 'H(B) :^ x.
    rewrite /'H(_) (big_imset _ (in2W (conjg_inj x))) -bigcapJ /=.
    by apply: eq_bigr => b Bb; rewrite DadeJ ?(subsetP sBA).
  rewrite /nn2 /aa2 defHBx !cardJg; congr (_ * _%:R).
  rewrite -(card_rcoset _ x); apply: eq_card => y.
  rewrite !(inE, mem_rcoset, mem_conjg) conjMg conjVg conjgK -conjgM.
  by rewrite groupMr // groupV (subsetP sLG).
rewrite sumr_const mulrC [sumB a](bigD1 [set a]) /=; last first.
  by rewrite 3!inE cent1id sub1set Aa -cards_eq0 cards1 (subsetP sAL).
rewrite -[_ *+ _]mulr_natr -mulrA mulr_addl -!mulrA ['H(_)]big_set1 cards1.
have ->: aa2 [set a] a = #|'C_G[a]|%:R.
  have [u x Ha_ux Gx def_g] := imset2P Ha_g.
  rewrite -(card_lcoset _ x^-1); congr _%:R; apply: eq_card => y.
  rewrite ['H(_)]big_set1 mem_lcoset invgK inE def_g -conjgM.
  rewrite -(groupMl y Gx) inE; apply: andb_id2l => Gxy.
  have [-> // _] := normedTI_memJ_P (notHa0 a) (Dade_cover_TI Aa).
  by rewrite inE Gxy.
rewrite mulN1r mulrC mulrA -natr_mul -(sdprod_card (defCa Aa)).
rewrite -mulnA card_orbit astab1J LaGrange ?subsetIl // mulnC natr_mul.
rewrite mulrAC mulfK ?neq0GC // mulrC divfK ?neq0GC // opprK.
rewrite (bigID [pred B : {set gT} | a \in B]) /= mulr_addl addrA.
apply: canRL (subrK _) _; rewrite -mulNr -sumr_opp; congr (_ + _ * _).
symmetry.
rewrite (reindex_onto (fun B => a |: B) (fun B => B :\ a)) /=; last first.
  by move=> B; case/andP=> _; exact: setD1K.
symmetry; apply: eq_big => B.
  rewrite setU11 andbT -!andbA; apply/and3P/and3P; case.
    do 2![case/setIdP] => sBA ntB /setIP[La nBa] _ notBa.
    rewrite 3!inE subUset sub1set Aa sBA La setU1K // -cards_eq0 cardsU1 notBa.
    rewrite -sub1set normsU ?sub1set ?cent1id //= eq_sym eqEcard subsetUl /=.
    by rewrite cards1 cardsU1 notBa ltnS leqn0 cards_eq0.
  do 2![case/setIdP] => /subUsetP[_ sBA] _ /setIP[La].
  rewrite inE conjUg (normP (cent1id a)) => /subUsetP[_ sBa_aB].
  rewrite eq_sym eqEcard subsetUl cards1 (cardsD1 a) setU11 ltnS leqn0 /=.
  rewrite cards_eq0 => notB0 /eqP defB.
  have notBa: a \notin B by rewrite -defB setD11.
  split=> //; last by apply: contraNneq notBa => ->; exact: set11.
  rewrite !inE sBA La -{1 3}defB notB0 subsetD1 sBa_aB.
  by rewrite mem_conjg /(a ^ _) invgK mulgA mulgK.
do 2![case/andP] => /setIdP[dB Na] _ notBa.
suffices ->: aa2 B a = #|'H(B) : 'H(a |: B)|%:R * aa2 (a |: B) a.
  rewrite /nn2 cardsU1 notBa exprS mulN1r !mulNr; congr (- _).
  rewrite !mulrA; congr (_ * _); rewrite -!mulrA; congr (_ * _).
  apply: canLR (mulKf (neq0GC _)) _; apply: canRL (mulfK (neq0GC _)) _ => /=.
  by rewrite -natr_mul mulnC LaGrange //= Dade_setU1 ?subsetIl.
rewrite /aa2 Dade_setU1 //= -natr_mul; congr _%:R.
have defMB := Dade_set_sdprod dB; have [_ mulHNB nHNB tiHNB] := sdprodP defMB.
have [sHMB sNMB] := mulG_sub mulHNB; have [La nBa] := setIP Na.
have nHa: a \in 'N('H(B)) by rewrite (subsetP nHNB).
have Ca: a \in 'C_L[a] by rewrite inE cent1id La.
have [|/= partHBa nbHBa] := partition_cent_rcoset nHa.
  have [sBA] := setIdP dB; case/set0Pn=> b Bb; have Ab := subsetP sBA b Bb.
  rewrite (coprime_dvdr (order_dvdG Ca)) //= ['H(B)](bigD1 b) //=.
  by rewrite (coprimeSg (subsetIl _ _)) ?coHL. 
pose pHBa := [pred y \in 'H(B) :* a | true].
rewrite -sum1_card (partition_big (fun x => g ^ x) pHBa) /= => [|x]; last first.
  by case/setIdP=> _ ->.
rewrite (set_partition_big _ partHBa) /= -nbHBa -sum_nat_const.
apply: eq_bigr => _ /imsetP[x Hx ->].
rewrite (eq_bigl _ _ (fun _ => andbT _)) (big_imset _ (in2W (conjg_inj x))) /=.
rewrite -(card_rcoset _ x) -sum1_card; symmetry; set HBaa := 'C_(_)[a] :* a.
rewrite (partition_big (fun y => g ^ (y * x^-1)) (mem HBaa)) => [|y]; last first.
  by rewrite mem_rcoset => /setIdP[].
apply: eq_bigr => /= u Ca_u; apply: eq_bigl => z.
rewrite -(canF_eq (conjgKV x)) -conjgM; apply: andb_id2r; move/eqP=> def_u.
have sHBG: 'H(B) \subset G.
  have [sBA /set0Pn[b Bb]] := setIdP dB; have Ab := subsetP sBA b Bb.
  by rewrite (bigcap_min b) ?sHG.
rewrite mem_rcoset !inE groupMr ?groupV ?(subsetP sHBG x Hx) //=.
congr (_ && _); have [/eqP defHBa _ _] := and3P partHBa.
symmetry; rewrite def_u Ca_u -defHBa -(mulgKV x z) conjgM def_u -/HBaa.
by rewrite cover_imset -class_supportEr mem_imset2.
Qed.

End DadeExpansion.

(* This is Peterfalvi (2.6)(b) *)
Lemma Dade_vchar alpha : alpha \in 'Z[irr L, A] -> alpha^\tau \in 'Z[irr G].
Proof.
move=> VCaa; move: (VCaa); rewrite vchar_split; case/andP=> VCa _.
have CFaa := memc_vchar VCaa.
rewrite Dade_expansion // vchar_opp // vchar_sum // => B /andP[dB _].
have{dB} dB: B \in calP.
  case/imsetP: dB => B0; case/setIdP=> sB0A notB00 defB.
  have [x Lx ->]: exists2 x, x \in L & B = B0 :^ x.
    by apply/imsetP; rewrite defB (mem_repr B0) ?orbit_refl.
  by rewrite inE -cards_eq0 cardJg cards_eq0 -(normsP nAL x Lx) conjSg sB0A.
set aaBt := 'Ind[G, _] _; suff ZGaaBt: aaBt \in 'Z[irr G].
  by rewrite -signr_odd; case: odd; rewrite ?scale1r // scaleN1r vchar_opp.
apply: vchar_induced => /=.
  have [sBA /set0Pn[b Bb]] := setIdP dB; have Ab := subsetP sBA b Bb.
  by rewrite gen_subG subUset (bigcap_min b) ?sHG // subIset ?sLG.
have [a1 [a2 [ch_a1 ch_a2 ->]]] := vcharP _ _ VCa.
set rB := Dade_cfun_restriction.
have ->: rB (a1 - a2) B = rB a1 B - rB a2 B.
  by apply/ffunP=> x; rewrite !ffunE; case: (x \in 'M(B)) => //; rewrite subr0.
by rewrite vchar_sub ?vchar_char ?Dade_restriction_char.
Qed.

Variable A1 : {set gT}.
Hypotheses (sA1A : A1 \subset A) (nA1L : L \subset 'N(A1)).

(* This is Peterfalvi (2.11), first part. *)
Lemma restr_Dade_hyp : Dade_hypothesis G L H A1.
Proof.
have [sAL1 _ _ _ _] := ddA; have sLN: L \subset 'N_G(A1) by exact/subsetIP.
have [sA1L1 ssA1A] := (subset_trans sA1A sAL1, subsetP sA1A).
split=> //; [|exact: sub_in1 defCa | exact: sub_in2 coHL] => a g A1a Gg A1ag.
by apply: conjAG => //; exact: ssA1A.
Qed.

Definition restr_Dade := Dade restr_Dade_hyp.

(* This is Peterfalvi (2.11), second part. *)
Lemma restr_DadeE : {in 'CF(L, A1), restr_Dade =1 Dade ddA}.
Proof.
move=> aa CF1aa; apply/ffunP=> g; rewrite ffunE.
have CFaa: aa \in 'CF(L, A) := memc_subset sA1A CF1aa.
have [a /= /andP[A1a Ha_g] | no_a /=] := pickP.
  by rewrite (DadeE _ (subsetP sA1A a A1a)).
rewrite ffunE; case: pickP => //= a /andP[A1a Ha_g].
by rewrite (cfunS0 CF1aa) //; apply: contraFN (no_a a) => ->.
Qed.

End Two.

Section Frobenius.

Variables (gT : finGroupType) (G L : {group gT}) (A : {set gT}).
Hypotheses (sAG1 : A \subset G^#) (tiAG : normedTI A G L).

(* This is the identity part of Isaacs, Lemma 7.7. *)
Lemma Frobenius_Ind_id1 :
  {in 'CF(L, A) & 1%g |: A, forall alpha, 'Ind[G, L] alpha =1 alpha}.
Proof.
move=> aa a CFaa A1a; have [A0 | notA0] := eqVneq A set0.
  have ->: aa = 0 by apply/ffunP=> y; rewrite (cfunS0 CFaa) ?ffunE // A0 inE.
  by rewrite linear0.
have ddA: Dade_hypothesis G L (fun _ => 1%G) A by exact/Dade_TI_P.
by rewrite -(Dade_Ind ddA) // Dade_id1.
Qed.

(* A more restricted, but more useful form. *)
Lemma Frobenius_Ind_id :
  {in 'CF(L, A) & A, forall alpha, 'Ind[G, L] alpha =1 alpha}.
Proof. by apply: sub_in11 Frobenius_Ind_id1 => //; exact/subsetP/subsetUr. Qed.

(* This is the isometry part of Isaacs, Lemma 7.7. *)
(* The statement in Isaacs is slightly more general in that it allows for     *)
(* beta \in 'CF(L, 1%g |: A); this appears to be more cumbersome than useful. *)
Lemma Frobenius_isometry : {in 'CF(L, A) &, forall alpha beta,
  '['Ind[G, L] alpha, 'Ind[G, L] beta]_G = '[alpha, beta]_L}.
Proof.
move=> aa bb CFaa CFbb; have [A0 | notA0] := eqVneq A set0.
  have ->: aa = 0 by apply/ffunP=> x; rewrite (cfunS0 CFaa) ?ffunE // A0 inE.
  by rewrite linear0 !inner_prod0l.
have ddA: Dade_hypothesis G L (fun _ => 1%G) A by exact/Dade_TI_P.
by rewrite -!(Dade_Ind ddA) // Dade_isometry.
Qed.

End Frobenius.