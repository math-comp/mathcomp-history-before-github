(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup.
Require Import matrix mxalgebra mxrepresentation vector algC classfun character.
Require Import inertia PFsection1.

(******************************************************************************)
(* This file covers Peterfalvi, Section 2: the Dade isometry                  *)
(* Defined here:                                                              *)
(*   Dade_hypothesis G L A H <-> G, L, A and H satisfy the hypotheses under   *)
(*                               which the Dade isometry relative to G, L and *)
(*                               A is well-defined.                           *)
(* For ddH : Dade_hypothesis G L A H, we also define                          *)
(*    Dade_isometry ddH == the Dade isometry relative to G, L and A.          *)
(*  Dade_support1 ddH a == the set of elements identified with a by the Dade  *)
(*                         isometry.                                          *)
(*     Dade_support ddH == the natural support of the Dade isometry.          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(* This is Peterfalvi (2.1). *)
Lemma partition_cent_rcoset : forall (gT : finGroupType) (G H : {group gT}) g,
  H \subset G -> g \in 'N_G(H) -> coprime #|H| #[g] ->
  let P := ('C_H[g] :* g) :^: H in partition P (H :* g) /\ #|P| = #|H : 'C[g]|.
Proof.
move=> gT G H g sHG; case/setIP=> Gg nHg coHg P; pose K := cover P.
rewrite -indexgI; do [set C := 'C_H[g]; set Cg := C :* g] in P K *.
have sKHg: K \subset H :* g.
  apply/bigcupsP=> Cgx; case/imsetP=> x Hx ->{Cgx}.
  rewrite conjsgE -rcosetM conjgCV rcosetM mulgA mulSg //.
  by rewrite !mul_subG ?subsetIl // sub1set ?memJ_norm ?groupV.
pose pi := \pi(#[g]); have id_pi: forall u x, u \in Cg -> (u ^ x).`_ pi = g ^ x.
  move=> ug x; case/rcosetP=> u; case/setIP=> Hu cgu ->{ug}.
  rewrite consttJ consttM; last exact/cent1P.
  rewrite (constt_p_elt (pgroup_pi _)) (constt1P _) ?mul1g //.
  by rewrite (mem_p_elt _ Hu) // /pgroup -coprime_pi' // coprime_sym.
have{id_pi} C'tiP: {in H &,
  forall x y, y \notin C :* x -> [disjoint Cg :^ x & Cg :^ y]}.
- move=> x y Hx Hy; apply: contraR; case/pred0Pn=> ugx; case/andP=> /=.
  case/imsetP=> u Cgu ->{ugx}; case/imsetP=> v Cgv eq_ux_vy.
  rewrite mem_rcoset inE groupM ?groupV //= cent1C (sameP cent1P commgP). 
  by apply/conjg_fixP; rewrite conjgM -(id_pi v) // -eq_ux_vy id_pi ?conjgK.
have nzCg: #|Cg| != 0%N by rewrite card_rcoset -lt0n cardG_gt0.
have defC: 'C_H[Cg | 'Js] = C.
  apply/setP=> z; apply/idP/idP=> Cz; have [Hz cz] := setIP Cz; last first.
    by rewrite !inE Hz sub1set inE /= conjsMg (normP cz) conjGid.
  apply: contraR nzCg; rewrite -{1}(mulg1 C); move/(C'tiP _ _ (group1 H) Hz).
  by rewrite (astab1P cz) act1 -setI_eq0 setIid -cards_eq0.
have oP: #|P| = #|H : C| by rewrite card_orbit defC.
have tiP: trivIset P.
  apply/trivIsetP=> Cgx Cgy.
  case/imsetP=> x Hx ->{Cgx}; case/imsetP=> y Hy ->{Cgy}.
  have [Cx_y | not_Cx_y] := boolP (y \in C :* x); last by right; exact: C'tiP.
  rewrite mem_rcoset -defC in Cx_y; have [_ cCg_xy] := setIP Cx_y.
  by left; rewrite -{1}(astab1P cCg_xy) actM actKV.
split=> //; apply/and3P; split=> //; rewrite -/K; last first.
  apply: contra nzCg; case/imsetP=> x _ Cx0.
  by rewrite -(cardJg _ x) -Cx0 cards0.
rewrite eqEcard sKHg -(eqnP tiP) card_rcoset /=.
rewrite (eq_bigr (fun _ => #|C|)) => [|Cgx]; last first.
  by case/imsetP=> x _ ->; rewrite cardJg card_rcoset.
by rewrite sum_nat_const oP mulnC LaGrange ?subsetIl.
Qed.

Section Two.

Variable gT : finGroupType.

(* This is Peterfalvi Definition (2.2). *)
Inductive Dade_hypothesis (G L A : {set gT}) H :=
  DadeHypothesis of
    A \subset L^# & L \subset 'N_G(A)
 & (*a*) {in A & G, forall a g,
          a ^ g \in A -> exists2 k, k \in L & a ^ g = a ^ k}
 & (*b*) {in A, forall a, H a ><| 'C_L[a] = 'C_G[a]}
 & (*c*) {in A &, forall a b, coprime #|H a| #|'C_L[b]| }.

Variables (G L : {group gT}) (A : {set gT}).

(* This is Peterfalvi (2.3). *)
Lemma Dade_TI_P : A \subset G^# -> A != set0 ->
  reflect (Dade_hypothesis G L A (fun _ => [1]))
          (trivIset (A :^: G) && ('N_G(A) == L)).
Proof.
rewrite subsetD1; case/andP=> sAG notA1 notA0.
apply: (iffP andP) => [[tiAG defL] | [_ sLN conjA_L defCa _]].
  have{tiAG} tiAG_L: {in A & G, forall a g, (a ^ g \in A) = (g \in L)}.
    move=> a g Aa Gg; rewrite -(eqP defL) inE Gg /=.
    apply/idP/normP=> [Aag | <-]; last by rewrite memJ_conjg.
    have AG_A: A \in A :^: G := orbit_refl _ _ _.
    have [//|] := trivIsetP tiAG (A :^ g) A (mem_imset _ Gg) AG_A.
    by case/pred0Pn; exists (a ^ g); rewrite /= memJ_conjg Aa.
  split=> [||a g Aa Gg /= Aag | a Aa | a b _ _]; last 1 first.
  - by rewrite cards1 coprime1n.
  - rewrite subsetD1 notA1 andbT /=; apply/subsetP=> a Aa.
    by rewrite -(tiAG_L a a) ?(subsetP sAG) // conjgE mulKg.
  - by rewrite (eqP defL).
  - by exists g => //; rewrite -(tiAG_L a g).
  apply/eqP; rewrite sdprod1g eqEsubset -{1}(eqP defL) setSI ?subsetIl //=.
  apply/subsetP=> g; case/setIdP=> Gg cag; rewrite inE cag -(tiAG_L a g) //.
  by rewrite conjgE -(cent1P cag) mulKg Aa.
have [sLG nAL] := subsetIP sLN.
have tiAG_L: {in A & G, forall a g, (a ^ g \in A) = (g \in L)}.
  move=> a g Aa Gg; apply/idP/idP=> [Aag | Lg]; last first.
    by rewrite memJ_norm ?(subsetP nAL).
  have [k Lk def_ag] := conjA_L a g Aa Gg Aag.
  suffices: (g * k^-1)%g \in 'C_G[a].
    by rewrite -defCa // sdprod1g; case/setIP; rewrite groupMr ?groupV.
  rewrite !inE groupMl // groupV (subsetP sLG) //=.
  by rewrite conjg_set1 conjgM def_ag conjgK.
rewrite eqEsubset sLN andbT; split; last first.
  have [a Aa] := set0Pn _ notA0.
  by apply/subsetP=> g; case/setIP=> Gg nAG; rewrite -(tiAG_L a g) ?memJ_norm.
apply/trivIsetP=> Ax Ay; case/imsetP=> x Gx ->; case/imsetP=> y Gy ->{Ax Ay}.
have [Lxy | notLxy] := boolP (x * y^-1 \in L)%g; [left | right].
  by rewrite -{2}(normsP nAL _ Lxy) actM actKV.
apply: contraR notLxy; case/pred0Pn=> a; case/andP=> /= Ax_a Ay_a.
rewrite -(tiAG_L (a ^ x^-1)) -?mem_conjg //; last by rewrite groupM ?groupV.
by rewrite actM actKV -mem_conjg.
Qed.

Definition Dade_support1 H of Dade_hypothesis G L A H :=
  fun a => class_support (H a :* a) G.

Definition Dade_support H ddH := \bigcup_(a \in A) @Dade_support1 H ddH a.

(* This is Peterfalvi Definition (2.5). *)
Definition Dade_isometry H ddH (alpha : cfun gT algC) :=
  cfun_of_fun
    (fun x => oapp alpha 0 [pick a \in A | x \in @Dade_support1 H ddH a]).

Lemma Dade_is_linear : forall H ddH, linear (@Dade_isometry H ddH).
Proof.
move=> H ddH mu alpha beta; apply/cfunP=> x.
by rewrite !cfunE; case: pickP => [a _ | _] /=; rewrite ?mulr0 ?addr0 ?cfunE.
Qed.

Canonical Structure Dade_additive H ddH := Additive (@Dade_is_linear H ddH).
Canonical Structure Dade_linear H ddH := Linear (@Dade_is_linear H ddH).

Lemma support_Dade_isometry : forall H ddH alpha,
  has_support (@Dade_isometry H ddH alpha) (Dade_support ddH).
Proof.
move=> H ddH alpha; apply/forall_inP=> x; rewrite cfunE.
case: pickP => [a | _]; last by rewrite eqxx.
by case/andP=> Aa Ha_x _; apply/bigcupP; exists a.
Qed.

Variable H : gT -> {group gT}.
Hypothesis ddH: Dade_hypothesis G L A [eta H].

(* This is Peterfalvi (2.4), with an essential result restored: the Dade *)
(* cover sets are TI-subsets of G.                                       *)
Lemma Dade_conjg :
  [/\ (*a*) {in A & L, forall a x, H (a ^ x) :=: H a :^ x},
      (*b*) {in A &, forall a b,
               ~~ [disjoint Dade_support1 ddH a & Dade_support1 ddH b] ->
             exists2 x, x \in L & b = a ^ x},
      (*c*) {in A, forall a, 'N_G(H a :* a) = 'C_G[a]}
   &  (*d*) {in A, forall a,
              partition ((H a :* a) :^: G) (Dade_support1 ddH a)}].
Proof.
pose pi := [pred p | existsb a, (a \in A) && (p \in \pi('C_L[a]))].
have [sAL1 sLN conjAG defCa coHL] := ddH.
have sAL: A \subset L := subset_trans sAL1 (subsetDl _ _).
have [sLG nAL] := subsetIP sLN.
have nsHC: {in A, forall a, H a <| 'C_G[a]}.
  by move=> a Aa; case/sdprod_context: (defCa a Aa).
have pi'H: {in A, forall a, pi^'.-group (H a)}.
  move=> a Aa; apply/pgroupP=> p p_pr; apply: contraL; case/exists_inP=> b Ab.
  rewrite mem_primes p_pr cardG_gt0 /= => p_dv_L.
  by rewrite -prime_coprime // coprime_sym (coprime_dvdr p_dv_L) ?coHL.
have piL: {in A, forall a, pi.-group 'C_L[a]}.
  move=> a Aa; apply: sub_pgroup (pgroup_pi _) => p piLp.
  by apply/exists_inP; exists a.
have pi_Ha: forall a u, a \in A -> u \in H a :* a -> u.`_pi = a.
  move=> a ua Aa; case/rcosetP=> u Hu ->{ua}.
  have pi_a: pi.-elt a.
    by rewrite (mem_p_elt (piL a Aa)) // inE cent1id (subsetP sAL).
  have cua: u \in 'C[a] by case/setIP: (subsetP (normal_sub (nsHC a Aa)) u Hu).
  rewrite (consttM _ (cent1P cua)) (constt_p_elt pi_a) (constt1P _) ?mul1g //.
  exact: mem_p_elt (pi'H a Aa) Hu.
have tiHa: {in A & G, forall a g (Ha := H a :* a),
              ~~ [disjoint Ha & Ha :^ g] -> g \in 'C_G[a]}.
- move=> a g Aa Gg /=; case/pred0Pn=> u; rewrite /= mem_conjg.
  case/andP=> Ha_u Ha_ug; rewrite !inE conjg_set1 -{1}(pi_Ha a (u ^ g^-1)) //.
  by rewrite Gg /= consttJ conjgKV (pi_Ha a).
have nHa_Ca: {in A, forall a, 'N_G(H a :* a) = 'C_G[a]}.
  move=> a Aa; apply/eqP; rewrite eqEsubset andbC subsetI subsetIl.
  rewrite normsM ?subsetIr ?andbT //=; last by rewrite normal_norm ?nsHC.
  apply/subsetP=> x; case/setIP=> Gx nHax; apply: tiHa => //.
  by rewrite (normP nHax) -setI_eq0 setIid -cards_eq0 -lt0n card_rcoset.
split=> [| a b Aa Ab | // | a Aa] /=.
- suffices defH: {in A, forall a, H a :=: 'O_pi^'('C_G[a])}.
    move=> a x Aa Lx /=; rewrite !defH ?memJ_norm ?(subsetP nAL) //.
    by rewrite -pcoreJ conjIg (conjGid (subsetP sLG x Lx)) -normJ conjg_set1.
  move=> a Aa; have [_ mulHC _ _] := sdprodP (defCa a Aa).
  have [hallH _] := coprime_mulGp_Hall mulHC (pi'H a Aa) (piL a Aa).
  by rewrite -(normal_Hall_pcore hallH) ?nsHC.
- case/pred0Pn=> w; case/andP.
  case/imset2P=> x u Hau Gx ->{w}; case/imset2P=> y v Hav Gy.
  move/(congr1 (fun w => w.`_pi)); rewrite !consttJ (pi_Ha a) // (pi_Ha b) //.
  move/(canLR (conjgK _)); rewrite -conjgM => def_b; rewrite -def_b in Ab *.
  by apply: conjAG; rewrite // groupM ?groupV.
apply/and3P; split; first by rewrite cover_imset -class_supportEr.
  apply/trivIsetP=> Vx Vy; case/imsetP=> x Gx ->; case/imsetP=> y Gy ->{Vx Vy}.
  apply/predU1P; rewrite orbC -implyNb -setI_eq0 -cards_eq0; apply/implyP.
  rewrite -[_ :^ y](conjsgKV x) -conjIg cardJg cards_eq0 -conjsgM setI_eq0.
  move/tiHa; rewrite -nHa_Ca // inE groupM ?groupV // => nHa_xy.
  by rewrite (normP (nHa_xy _ _)).
apply/imsetP=> [[x _]]; move/eqP; case/idPn; rewrite eq_sym.
by rewrite -cards_eq0 -lt0n cardJg card_rcoset.
Qed.

(* This is Peterfalvi (2.4)(a). *)
Lemma DadeJ : {in A & L, forall a x, H (a ^ x) :=: H a :^ x}.
Proof. by case: Dade_conjg. Qed.

(* This is Peterfalvi (2.4)(b). *)
Lemma Dade_support1_TI : {in A &, forall a b,
    ~~ [disjoint Dade_support1 ddH a & Dade_support1 ddH b] ->
  exists2 x, x \in L & b = a ^ x}.
Proof. by case: Dade_conjg. Qed.

(* This is Peterfalvi (2.4)(c). *)
Lemma norm_Dade_cover : {in A, forall a, 'N_G(H a :* a) = 'C_G[a]}.
Proof. by case: Dade_conjg. Qed.

Lemma Dade_partition : {in A, forall a,
  partition ((H a :* a) :^: G) (Dade_support1 ddH a)}.
Proof. by case: Dade_conjg. Qed.

Local Notation "alpha ^\tau" := (Dade_isometry ddH alpha)
  (at level 2, format "alpha ^\tau").

(* This is the validity of Peterfalvi, Definition (2.5) *)
Lemma Dade_isoE : forall alpha a u,
    alpha \in 'CF(L, A) -> a \in A -> u \in Dade_support1 ddH a ->
  alpha^\tau u = alpha a.
Proof.
move=> alpha a u; case/cfun_memfP=> _ CFalpha Aa Ha_u; rewrite cfunE.
have [b /= | ] := pickP; last by move/(_ a); rewrite Aa Ha_u.
case/andP=> Ab Hb_u; have [|x Lx ->] := Dade_support1_TI Aa Ab.
  by apply/pred0Pn; exists u; rewrite /= Ha_u.
rewrite CFalpha // (subsetP _ a Aa) //.
by have [sAL1 _ _ _ _] := ddH; exact: subset_trans sAL1 (subsetDl _ _).
Qed.

Lemma Dade_support_sub : Dade_support ddH \subset G.
Proof.
apply/bigcupsP=> a Aa; have [sAL1 sLN _ defCa _] := ddH.
have [sAL [sLG _]] := (subset_trans sAL1 (subsetDl _ _), subsetIP sLN).
rewrite class_support_subG // mul_subG //; last first.
  by rewrite sub1set (subsetP sLG) ?(subsetP sAL).
by case/sdprodP: (defCa a Aa) => _; case/mulG_sub; case/subsetIP.
Qed.

Lemma Dade_cfun : forall alpha, alpha \in 'CF(L, A) -> alpha^\tau \in 'CF(G).
Proof.
move=> alpha CFalpha; apply/cfun_memP; split=> [u | u y Gu Gy].
  apply: contraNeq; move/(forall_inP (support_Dade_isometry ddH _)).
  exact: (subsetP Dade_support_sub).
rewrite [alpha^\tau u]cfunE.
have [a /= | no_a /=] := pickP; last first.
  apply/eqP; apply/idPn; move/(forall_inP (support_Dade_isometry ddH _)).
  case/bigcupP=> a Aa; rewrite -mem_conjgV class_supportGidr ?groupV // => Ha_u.
  by case/andP: (no_a a).
case/andP=> Aa Ha_u; rewrite (Dade_isoE CFalpha Aa) //.
by rewrite -mem_conjgV class_supportGidr ?groupV.
Qed.

Lemma Dade_support1_id :
  {in A & L, forall a x, Dade_support1 ddH (a ^ x) = Dade_support1 ddH a}.
Proof.
move=> a x Aa Lx; rewrite {1}/Dade_support1 DadeJ // -conjg_set1 -conjsMg.
by rewrite class_supportGidl ?(subsetP _ x Lx) //; case ddH => _; case/subsetIP.
Qed.

(* This is Peterfalvi (2.7), main part *)
Lemma general_Dade_reciprocity : forall alpha xi psi,
    alpha \in 'CF(L, A) -> xi \in 'CF(G) -> psi \in 'CF(L) ->
  {in A, forall a, psi a = #|H a|%:R ^-1 * (\sum_(x \in H a) xi (x * a)%g)} ->
  '[alpha^\tau, xi]_G = '[alpha, psi]_L.
Proof.
have [sAL1 sLN _ defCa _] := ddH.
have [sAL [sLG nAL]] := (subset_trans sAL1 (subsetDl _ _), subsetIP sLN).
move=> alpha xi psi CFalpha CFxi CFpsi psiA.
rewrite inner_prodE (big_setID (Dade_support ddH)) /= addrC.
rewrite (setIidPr Dade_support_sub) big1 ?add0r => [|x]; last first.
  case/setDP=> _ notHx.
  by rewrite (contraNeq (forall_inP (support_Dade_isometry ddH _) _)) ?mul0r.
pose T := [set repr (a ^: L) | a <- A].
have sTA: {subset T <= A}.
  move=> ax; case/imsetP=> a Aa ->; have [x Lx ->{ax}] := repr_class L a.
  by rewrite memJ_norm ?(subsetP nAL).
set F := Dade_support1 ddH; pose P_G := [set F a | a <- T].
have F_id: {in A, forall a, F (repr (a ^: L)) = F a}.
  by move=> a Aa /=; have [x Lx ->] := repr_class L a; exact: Dade_support1_id.
have ->: Dade_support ddH = cover P_G.
  apply/setP=> u; apply/bigcupP/bigcupP=> [[a Aa Fa_u] | [Fa]]; last first.
    by case/imsetP=> a; move/sTA=> Aa -> Fa_u; exists a. 
  by exists (F a) => //; rewrite -F_id //; do 2!apply: mem_imset.
have [tiP_G injF]: trivIset P_G /\ {in T &, injective F}.
  apply: trivIimset => [a0 b0 |]; last first.
    apply/imsetP=> [[a]]; move/sTA=> Aa; move/esym; move/eqP; case/set0Pn.
    by exists (a ^ 1)%g; apply: mem_imset2; rewrite ?group1 ?rcoset_refl.
  case/imsetP=> a Aa ->; case/imsetP=> b Bb ->{a0 b0}; rewrite !F_id //.
  by apply: contraR; case/Dade_support1_TI=> // x Lx ->; rewrite classGidl.
have big_andT := eq_bigl _ _ (fun _ => andbT _).
rewrite -big_andT big_trivIset //= big_imset {P_G tiP_G injF}//=.
symmetry; rewrite inner_prodE (big_setID A) (setIidPr sAL) /= addrC.
rewrite big1 ?add0r => [|x]; last first.
  by case/setDP=> _ notAx; rewrite (cfunS0 CFalpha) ?mul0r.
pose P_A := [set a ^: L | a <- T].
have rLid: forall x, repr (x ^: L) ^: L = x ^: L.
  by move=> x; have [y Ly ->] := repr_class L x; rewrite classGidl.
have <-: cover P_A = A.
  apply/setP=> a; apply/bigcupP/idP=> [[bL] | Aa].
    case/imsetP=> b; move/sTA=> Ab ->{bL}; case/imsetP=> x Lx ->.
    by rewrite memJ_norm ?(subsetP nAL).
  by exists (a ^: L); rewrite ?class_refl // -rLid; do 2!apply: mem_imset.
have [tiP_A injFA]: trivIset P_A /\ {in T &, injective (class^~ L)}.
  apply: trivIimset => [a0 b0 |]; last first.
    apply/imsetP=> [[a _]]; move/esym; move/eqP; case/set0Pn.
    by exists a; exact: class_refl.
  case/imsetP=> a Aa ->; case/imsetP=> b Bb ->{a0 b0}; rewrite !rLid.
  by apply: contraR; case/pred0Pn=> c; case/andP; do 2!move/class_transr <-.
rewrite -big_andT big_trivIset //= big_imset {P_A tiP_A injFA}//=.
apply: canRL (mulKf (neq0GC G)) _; rewrite mulrA big_distrr /=.
apply: eq_bigr => a; move/sTA=> {T sTA}Aa.
have{defCa} [La defCa] := (subsetP sAL a Aa, defCa a Aa).
rewrite !big_andT (eq_bigr (fun _ => alpha a * (psi a)^*)) => [|ax]; last first.
  by case/imsetP=> x Lx ->{ax}; rewrite (cfunJ CFalpha) ?(cfunJ CFpsi).
rewrite sumr_const -index_cent1 mulrC -mulr_natr -!mulrA.
rewrite (eq_bigr (fun xa => alpha a * (xi xa)^*)) => [|xa Fa_xa]; last first.
  by rewrite (Dade_isoE CFalpha Aa).
rewrite -big_distrr /= -rmorph_sum; congr (_ * _).
rewrite mulrC mulrA -natr_mul mulnC -(LaGrange (subsetIl G 'C[a])).
rewrite -mulnA mulnCA -(sdprod_card defCa) -mulnA LaGrange ?subsetIl //.
rewrite mulnA natr_mul mulfK ?neq0GC // -conjC_nat -rmorphM; congr (_ ^*).
rewrite -big_andT (set_partition_big _ (Dade_partition Aa)) /=.
rewrite (eq_bigr (fun _ => \sum_(x \in H a) xi (x * a)%g)) => [|Vx]; last first.
  case/imsetP=> x Gx ->{Vx}; rewrite big_andT -rcosetE.
  rewrite (big_imset _ (in2W (conjg_inj x))) (big_imset _ (in2W (mulIg a))) /=.
  apply: eq_bigr => u Hu; rewrite (cfunJ CFxi) ?groupM ?(subsetP sLG a) //.
  by apply: subsetP Hu; case/sdprodP: defCa => _; case/mulG_sub; case/subsetIP.
rewrite sumr_const card_orbit astab1Js norm_Dade_cover //.
by rewrite natr_mul -mulrA mulr_natl psiA // mulVKf ?neq0GC.
Qed.

(* This is Peterfalvi (2.7), second part. *)
Lemma Dade_reciprocity : forall alpha xi,
    alpha \in 'CF(L, A) -> xi \in 'CF(G) ->
    {in A, forall a, {in H a, forall u, xi (u * a)%g = xi a}} ->
  '[alpha^\tau, xi]_G = '[alpha, 'Res[L] xi]_L.
Proof.
have [sAL1 sLN _ defCa _] := ddH.
have [sAL [sLG nAL]] := (subset_trans sAL1 (subsetDl _ _), subsetIP sLN).
move=> alpha xi CFalpha CFxi xiH.
apply: general_Dade_reciprocity => // [|a Aa].
  exact: crestrict_in_cfun CFxi.
rewrite crestrictE ?(subsetP sAL) // mulrC.
rewrite (eq_bigr (fun _ => xi a)) ?sumr_const => [|u Hu]; last exact: xiH.
by rewrite -[_ *+ _]mulr_natr mulfK ?neq0GC.
Qed.

(* This is Peterfalvi (2.6)(a). *)
Lemma Dade_isom : {in 'CF(L, A) &, forall alpha beta,
  '[alpha^\tau, beta^\tau]_G = '[alpha, beta]_L}.
Proof.
move=> alpha beta CFalpha CFbeta.
have sub_supp := subsetP (sub_class_support _ _).
rewrite /= Dade_reciprocity ?Dade_cfun => // [|a Aa u Hu]; last first.
  by rewrite !(Dade_isoE CFbeta Aa) ?sub_supp ?rcoset_refl // mem_rcoset mulgK.
congr (_ * _); apply: eq_bigr => x Lx.
have [Ax | notAx] := boolP (x \in A); last by rewrite (cfunS0 CFalpha) ?mul0r.
by rewrite cfunE Lx mul1r (Dade_isoE CFbeta Ax) // sub_supp ?rcoset_refl.
Qed.

Definition Dade_set_signalizer (B : {set gT}) := \bigcap_(a \in B) H a.
Local Notation "''H' ( B )" := (Dade_set_signalizer B)
  (at level 8, format "''H' ( B )") : group_scope.
Canonical Structure Dade_set_signalizer_group B := [group of 'H(B)].
Definition Dade_set_normalizer B := 'H(B) <*> 'N_L(B).
Local Notation "''M' ( B )" := (Dade_set_normalizer B)
  (at level 8, format "''M' ( B )") : group_scope.
Canonical Structure Dade_set_normalizer_group B := [group of 'M(B)].

Let domB := [set B : {set gT} | (B \subset A) && (B != set0)].

(* This is Peterfalvi (2.8). *)
Lemma Dade_set_sdprod : {in domB, forall B, 'H(B) ><| 'N_L(B) = 'M(B)}.
Proof.
move=> B; case/setIdP=> sBA notB0; apply: sdprodEY => /=.
  apply/subsetP=> x; case/setIP=> Lx nBx; rewrite inE.
  apply/bigcapsP=> a Ba; have Aa := subsetP sBA a Ba.
  by rewrite sub_conjg -DadeJ ?groupV // bigcap_inf // memJ_norm ?groupV.
have [a Ba] := set0Pn _ notB0; have Aa := subsetP sBA a Ba.
have [_ sLN _ defCa _] := ddH; have [sLG _] := subsetIP sLN.
have [_] := sdprodP (defCa a Aa); case/mulG_sub=> sHaC _ _ tiHaL.
rewrite -(setIidPl sLG) -setIA setICA (setIidPl sHaC) in tiHaL.
by rewrite setICA ['H(B)](bigD1 a) //= !setIA tiHaL !setI1g.
Qed.

Section DadeExpansion.

Variables (aa : cfun gT algC).
Hypothesis CFaa : aa \in 'CF(L, A).

Definition Dade_cfun_restriction B :=
  cfun_of_fun (fun x => if x \in 'M(B) then aa (remgr 'H(B) 'N_L(B) x) else 0).

Local Notation "''aa_' B" := (Dade_cfun_restriction B)
  (at level 3, B at level 2, format "''aa_' B") : ring_scope.

Definition Dade_transversal :=
  [set repr (B :^: L) | B <- [set B : {set gT} | (B \subset A) && (B != set0)]].
Local Notation calB := Dade_transversal.

Lemma Dade_restriction_classfun : {in domB, forall B, 'aa_B \in 'CF('M(B))}.
Proof.
move=> B; move/Dade_set_sdprod=> defMB.
apply/cfun_memfP; split=> /= [x | x y Mx My].
  by rewrite setIid cfunE -if_neg => ->.
rewrite !cfunE groupJ ?Mx //=.
have [nsHN _ mulHN _ _] := sdprod_context defMB.
pose fB := Morphism (remgrM (sdprod_compl defMB) nsHN).
rewrite -[remgr _ _ _]/(fB _) morphJ //.
by rewrite (cfunJ CFaa) ?(subsetP (subsetIl L 'N(B))) ?mem_remgr ?mulHN.
Qed.
Local Notation CFaa_ := Dade_restriction_classfun.

Lemma Dade_restriction_char :
  is_char L aa -> {in domB, forall B, is_char 'M(B) 'aa_B}.
Proof.
case/is_charP=> d [rA def_aa] B; move/Dade_set_sdprod=> defMB.
have [nsHN _ mulHN _ _] := sdprod_context defMB.
pose fB := Morphism (remgrM (sdprod_compl defMB) nsHN).
have subNL: fB @* 'M(B) \subset L.
  apply/subsetP=> y; case/morphimP=> x /= _ Mx ->{y}.
  by rewrite (subsetP (subsetIl L 'N(B))) ?mem_remgr ?mulHN.
apply/is_charP; exists d; exists (morphim_repr (subg_repr rA subNL) (subxx _)).
apply/cfunP=> x //=; rewrite !cfunE -def_aa cfunE.
case Mx: (x \in _); last by rewrite mul0r.
by rewrite (subsetP subNL) ?mul1r //; exact: mem_morphim.
Qed.

Lemma bigcapJ : forall I r (P : pred I) (B : I -> {set gT}) x,
  \bigcap_(i <- r | P i) (B i :^ x) = (\bigcap_(i <- r | P i) B i) :^ x.
Proof.
move=> I r P B x; symmetry; apply: (big_morph (conjugate^~ x)) => [B1 B2|].
  by rewrite conjIg.
by apply/normP; rewrite inE subsetT.
Qed.

(* This is Peterfalvi (2.10.1) *)
Lemma Dade_Ind_restr_J : {in L & domB, forall x B,
  'Ind[G, 'M(B :^ x)] 'aa_(B :^ x) = 'Ind[G, 'M(B)] 'aa_B}.
Proof.
move=> x B Lx dB; have [defMB [sBA _]] := (Dade_set_sdprod dB, setIdP dB).
have [_ sLN _ _ _] := ddH; have [sLG nAL] := subsetIP sLN.
have dBx: B :^ x \in domB.
  by rewrite !inE -{2}(normsP nAL x Lx) conjSg -!cards_eq0 cardJg in dB *.
have defHBx: 'H(B :^ x) = 'H(B) :^ x.
  rewrite /'H(_) (big_imset _ (in2W (conjg_inj x))) -bigcapJ /=.
  by apply: eq_bigr => a Ba; rewrite DadeJ ?(subsetP sBA).
have defNBx: 'N_L(B :^ x) = 'N_L(B) :^ x.
  by rewrite conjIg -normJ (conjGid Lx).
have [_ mulHNB _ tiHNB] := sdprodP defMB.
have defMBx: 'M(B :^ x) = 'M(B) :^ x.
  rewrite -mulHNB conjsMg -defHBx -defNBx.
  by case/sdprodP: (Dade_set_sdprod dBx).
have def_aa_x: forall y, 'aa_(B :^ x) (y ^ x) = 'aa_B y.
  move=> y /=; rewrite !cfunE defMBx memJ_conjg -mulHNB /=.
  have [[h z Hh Nz ->] | //] := altP mulsgP; have [Lz _] := setIP Nz.
  rewrite defHBx defNBx conjMg !remgrMid ?(cfunJ CFaa) ?memJ_conjg //.
  by rewrite -conjIg tiHNB conjs1g.
apply/cfunP=> y; rewrite !cfunE defMBx cardJg; congr (_ * _).
rewrite (reindex_astabs 'R x) ?astabsR ?(subsetP sLG) //=.
by apply: eq_bigr => z _; rewrite conjgM def_aa_x.
Qed.

(* This is Peterfalvi (2.10.2) *)
Lemma Dade_setU1 : {in domB & A, forall B a, 'H(a |: B) = 'C_('H(B))[a]}.
Proof.
move=> B a dB Aa; rewrite /'H(_) bigcap_setU big_set1 -/'H(B).
pose pi := \pi('C_L[a]); have [_ _ _ defCa coH_L] := ddH.
have{coH_L} pi'H: {in A, forall b, pi^'.-group(H b)}.
  by move=> b Ab; rewrite /pgroup -coprime_pi' ?cardG_gt0 // coprime_sym coH_L.
have [sHBG pi'HB]: 'H(B) \subset G /\ pi^'.-group('H(B)).
  have [sBA] := setIdP dB; case/set0Pn=> b Bb; have Ab := subsetP sBA b Bb.
  have sHBb: 'H(B) \subset H b by rewrite ['H(B)](bigD1 b) ?subsetIl.
  rewrite (pgroupS sHBb) ?pi'H ?(subset_trans sHBb) //.
  by case/sdprod_context: (defCa b Ab); case/andP; case/subsetIP.
have{defCa} [nsHa _ defCa _ _] := sdprod_context (defCa a Aa).
have [_ caH] := subsetIP (normal_sub nsHa).
have [hallHa _] := coprime_mulGp_Hall defCa (pi'H a Aa) (pgroup_pi _).
apply/eqP; rewrite setIC eqEsubset setIS // subsetI subsetIl /=.
by rewrite (sub_normal_Hall hallHa) ?(pgroupS (subsetIl _ _)) ?setSI.
Qed.

Let calA g (X : {set gT}) := [set x \in G | g ^ x \in X]%g.

(* This is Peterfalvi (2.10.3) *)
Lemma Dade_Ind_expansion : forall B g,
  B \in domB ->
    [/\ g \notin Dade_support ddH -> ('Ind[G, 'M(B)] 'aa_B) g = 0
      & {in A, forall a, g \in Dade_support1 ddH a ->
         ('Ind[G, 'M(B)] 'aa_B) g =
              (aa a / #|'M(B)|%:R) *
                  \sum_(b \in 'N_L(B) :&: a ^: L) #|calA g ('H(B) :* b)|%:R}].
Proof.
move=> B g dB; set LHS := ('Ind[G, _] _) g.
have ->: LHS = #|'M(B)|%:R^-1 * \sum_(x \in calA g 'M(B)) 'aa_B (g ^ x).
  rewrite [LHS]cfunE; congr (_ * _); rewrite (bigID [pred x | g ^ x \in 'M(B)]).
  rewrite /= addrC big1 ?add0r => [|x].
    by apply: eq_bigl => x; rewrite inE.
  by case/andP=> _ notMgx; rewrite (cfun0 (CFaa_ dB)).
have defMB := Dade_set_sdprod dB; have [_ mulHNB nHNB tiHNB] := sdprodP defMB.
have [sHMB sNMB] := mulG_sub mulHNB.
have [sAL1 _ _ defCa coHL] := ddH; have{sAL1} [sAL _] := subsetD1P sAL1.
pose fBg x := remgr 'H(B) 'N_L(B) (g ^ x).
pose supp_aBg := [pred b \in A | g \in Dade_support1 ddH b].
have supp_aBgP: {in calA g 'M(B), forall x,
  ~~ supp_aBg (fBg x) -> 'aa_B (g ^ x)%g = 0}.
- move=> x; case/setIdP; set b := fBg x => Gx MBgx notHGx; rewrite cfunE MBgx. 
  have Nb: b \in 'N_L(B) by rewrite mem_remgr ?mulHNB.
  have Cb: b \in 'C_L[b] by rewrite inE cent1id; have [-> _] := setIP Nb.
  rewrite (cfunS0 CFaa) // -/(fBg x) -/b; apply: contra notHGx => Ab.
  have nHb: b \in 'N_('M(B))('H(B)).
    by rewrite inE (subsetP sNMB) // (subsetP nHNB).
  have [sBA] := setIdP dB; case/set0Pn=> a Ba; have Aa := subsetP sBA a Ba.
  have [|/= partHBb _] := partition_cent_rcoset sHMB nHb.
    rewrite (coprime_dvdr (order_dvdG Cb)) //= ['H(B)](bigD1 a) //=.
    by rewrite (coprimeSg (subsetIl _ _)) ?coHL. 
  have Hb_gx: g ^ x \in 'H(B) :* b by rewrite mem_rcoset mem_divgr ?mulHNB.
  have [defHBb _ _] := and3P partHBb; rewrite -(eqP defHBb) in Hb_gx.
  case/bigcupP: Hb_gx => Cy; case/imsetP=> y HBy ->{Cy} Cby_gx.
  have sHBa: 'H(B) \subset H a by rewrite bigcap_inf.
  have sHBG: 'H(B) \subset G.
    apply: subset_trans sHBa _.
    by case/sdprodP: (defCa a Aa) => _; case/mulG_sub; case/subsetIP=> ->.
  rewrite Ab -(memJ_conjg _ x) class_supportGidr //  -(conjgKV y (g ^ x)).
  rewrite mem_imset2 // ?(subsetP sHBG) {HBy}// -mem_conjg.
  apply: subsetP Cby_gx; rewrite {y}conjSg mulSg //.
  pose pi := \pi('C_L[b]).
  have pi'H: {in A, forall c, pi^'.-group (H c)}.
    by move=> c Ac; rewrite /pgroup -coprime_pi' ?cardG_gt0 // coprime_sym coHL.
  have [nsHbC _ defHbC _ _] := sdprod_context (defCa b Ab).
  have [hallHb _] := coprime_mulGp_Hall defHbC (pi'H _ Ab) (pgroup_pi _).
  rewrite (sub_normal_Hall hallHb) ?setSI // (pgroupS _ (pi'H a Aa)) //=.
  by rewrite subIset ?sHBa.  
split=> [notHGg | a Aa Hag].
  rewrite big1 ?mulr0 // => x; move/supp_aBgP; apply; set b := fBg x.
  by apply: contra notHGg; case/andP=> Ab Hb_x; apply/bigcupP; exists b.
rewrite -mulrA mulrCA; congr (_ * _); rewrite big_distrr /=.
set nBaL := _ :&: _; rewrite (bigID [pred x | fBg x \in nBaL]) /= addrC.
rewrite big1 ?add0r => [|x]; last first.
  case/andP=> calAx not_nBaLx; apply: supp_aBgP => //; apply: contra not_nBaLx.
  set b := fBg x; case/andP=> Ab Hb_g; have [Gx MBx] := setIdP calAx.
  rewrite inE mem_remgr ?mulHNB //; apply/imsetP; apply: Dade_support1_TI => //.
  by apply/pred0Pn; exists g; exact/andP.
rewrite (partition_big fBg (mem nBaL)) /= => [|x]; last by case/andP.
apply: eq_bigr => b; case/setIP=> Nb aLb; rewrite mulr_natr -sumr_const.
apply: eq_big => x; rewrite ![x \in _]inE -!andbA.
  apply: andb_id2l=> Gx; apply/and3P/idP=> [[Mgx _]|HBb_gx].
    by move/eqP <-; rewrite ?andbF // mem_rcoset mem_divgr ?mulHNB.
  suff ->: fBg x = b.
    by rewrite inE Nb (subsetP _ _ HBb_gx) // -mulHNB mulgS ?sub1set.
  by rewrite /fBg; have [h Hh ->] := rcosetP HBb_gx; exact: remgrMid.
case/and4P=> _ Mgx _; move/eqP=> def_fx.
rewrite cfunE Mgx -/(fBg x) def_fx; case/imsetP: aLb => y Ly ->.
by rewrite (cfunJ CFaa) // (subsetP _ a Aa) //; case: ddH; case/subsetD1P.
Qed.

End DadeExpansion.
  
  
End Two.