(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup.
Require Import matrix mxalgebra mxrepresentation vector algC classfun character.
Require Import inertia vcharacter PFsection1 PFsection2 PFsection5.

(******************************************************************************)
(* This file covers Peterfalvi, Section 7:                                    *)
(* Non-existence of a Certain Type of Group of Odd Order                      *)
(* Defined here:                                                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.


Section Remove1.


Variable (T : eqType).
Implicit Type s : seq T.

Definition remove1 s x := filter (predC1 x) s.

Lemma remove1_cons s x : x \in s -> s =i x :: remove1 s x.
Proof.
move => xs y; rewrite in_cons mem_filter; apply/idP/orP.
  by move ->; rewrite andbT /=; apply/orP; rewrite orbN.
by case => [/eqP ->| /andP []].
Qed.

Lemma remove1_cons_size s x : uniq s -> x \in s ->
  size (x :: remove1 s x) = size s.
Proof.
move => us xs; apply/eqP; rewrite -uniq_size_uniq //; last by exact: remove1_cons.
by rewrite cons_uniq filter_uniq // andbT mem_filter negb_and negbK eqxx orTb.
Qed.


Lemma remove1_size s x : uniq s -> x \in s -> 
  size (remove1 s x) = (size s).-1.
Proof. by move => us xs; rewrite -(remove1_cons_size us xs) -pred_Sn. Qed.


End Remove1.


Section MoreVChar.

Variable gT : finGroupType.

Lemma vchar_scale (S : seq {cfun gT}) K f z :
  isZC z -> f \in 'Z[S, K] -> z *: f \in 'Z[S, K].
Proof.
rewrite isZCE.
case/orP; case/isNatCP => a.
  by move => -> fZ; rewrite scaler_nat; exact: vchar_scal.
move => za fZ; rewrite -vchar_opp -scaleNr.
by rewrite za scaler_nat; exact: vchar_scal.
Qed.


End MoreVChar.




Section Seven.


Lemma tnthP : forall (T : eqType) m (t : m.-tuple T) (x : T),
  reflect (exists j, x = tnth t j) (x \in t).
Proof.
move => T m t x.
apply: (iffP idP); last first.
  case => j ->; apply/(@nthP T t _ x).
  by exists j; rewrite ?(size_tuple, ltn_ord) -?tnth_nth.
move => xt; move/nthP: (xt) => /(_ x) [] j.
rewrite size_tuple => j_lt_m <-.
exists (Ordinal j_lt_m).
by rewrite (@tnth_nth m T x t (Ordinal j_lt_m)).
Qed.


Variable (gT : finGroupType) (G : {group gT}).



Section Prelim1.

Variables (A : {set gT}) (L : {group gT}) (H : gT -> {group gT}).
Hypothesis ddA : Dade_hypothesis G L H A.


Local Notation "alpha ^\tau" := (Dade ddA alpha)
  (at level 2, format "alpha ^\tau").


Local Notation Atau := (Dade_support ddA).


Let sAL : A \subset L. Proof. by have [/subsetD1P[]] := ddA. Qed.
Let notA1 : 1%g \notin A. Proof. by have [/subsetD1P[]] := ddA. Qed.
Let nAL : L \subset 'N(A). Proof. by have [_ /subsetIP[]] := ddA. Qed.
Let sLG : L \subset G. Proof. by have [_ /subsetIP[]] := ddA. Qed.




(* Some ideas on 5.9 *)
Section Five.




Lemma Dade_conjC (alpha : {cfun gT}) : alpha \in 'CF(L, A) ->
  ((alpha^\tau)^*)%CH = (alpha^*)%CH^\tau.
Proof.
move => alphaC; apply/ffunP => g; rewrite cfunE.
have alpha_conjC : (alpha^*)%CH \in 'CF(L, A).
  move/cfun_memfP: alphaC => [alpha_supp alphaJ].
  apply/cfun_memfP; split => [x xnAL | x y yA].
    by rewrite cfunE (alpha_supp x xnAL) conjC0.
  by rewrite !cfunE (alphaJ x y yA).
case: (boolP (g \in Atau)).
  case/bigcupP => a aA gD1.
  rewrite (DadeE alphaC aA gD1).
  have := DadeE alpha_conjC aA gD1.
  by rewrite ffunE => <-.
move => gnAtau.
rewrite (off_support (support_Dade ddA alpha) gnAtau).
have := off_support (support_Dade ddA (alpha^*)%CH) gnAtau.
by rewrite conjC0 => <-.
Qed.



Lemma Dade0 : 0^\tau = 0.
Proof.
apply/ffunP => x; rewrite !cfunE.
by case: pickP => //= x0; rewrite cfunE.
Qed.


Let irr_diff a b f g h k : a%:R *: f - b%:R *: g = a%:R *: h - b%:R *: k ->
  f \in irr G -> g \in irr G -> h \in irr G -> k \in irr G ->
  (a == 0)%N || (f == g) || (f == h).
Proof.
move => diff.
have inner: '[a%:R *: f + b%:R *: k, f]_G = '[a%:R *: h + b%:R *: g, f]_G.
  congr ('[_, _]_ _).
  rewrite -{1}(subrK (b%:R *: g) (a%:R *: f)) diff (addrAC (a%:R *: h) _ _).
  by rewrite -addrA [- _ + _]addrC subrr addr0.
case/irrIP => i fi; case/irrIP => j gj; case/irrIP => r hr; case/irrIP => t kt.
rewrite -fi -gj -hr -kt in inner * => {fi gj hr kt f g h k diff}.
case ij: (i == j); first by move/eqP: ij ->; rewrite eqxx orbT orTb.
case a0: (a == 0)%N; first by [].
apply/orP; right.
have := inner.
rewrite !inner_prodDl !inner_prodZl !irr_orthonormal.
rewrite [j == i]eq_sym eqxx ij mulr0 addr0.
rewrite -!natr_mul -natr_add => /eqP; rewrite -eqN_eqC muln1.
case: (t == i); case ri: (r == i); rewrite ?muln1 ?muln0 ?addn0.
- by move/eqP: ri ->.
- by rewrite addn_eq0 a0 andFb.
- by move/eqP: ri ->.
by rewrite a0.
Qed.



(* This is taken from PF1. This lemma is simpler to use in the proof of
PF 5.9b rather than the general theorem 1.4 *)
Let vchar_isometry_base2 f : f \in 'Z[irr G, G^#] -> '[f]_G = 2%:R ->
   exists e1, exists e2, (f = 'xi[G]_e1 - 'xi[G]_e2) /\ e2 != e1.
Proof.
move=> Hf.
rewrite (inner_prod_vchar Hf) //.
move/memc_vchar: (Hf)=>/memcW F1.
move=> HH.
pose h (t : Iirr G) := getNatC `|'[f, 'xi_t]_G|.
have Hh t: (h t)%:R = `|'[f, 'xi_t]_G|.
  exact/esym/eqP/normCZ_nat/(isZC_inner_prod_vchar t Hf).
have: (\sum_t (h t) * h t = 2)%N.
  apply/eqP; rewrite eqN_eqC -HH natr_sum; apply/eqP.
  apply: eq_bigr=> i _; rewrite natr_mul Hh -expr2 int_normCK //.
  exact: (isZC_inner_prod_vchar _ Hf).
case: (boolP (forallb i : Iirr G, '[f, 'xi_i]_G == 0)).
  move/forallP=> {HH}HH.
  rewrite big1=> // i _.
  apply/eqP; rewrite eqN_eqC natr_mul Hh.
  by rewrite (eqP (HH i)) normC0 mul0r.
rewrite negb_forall; case/existsP=> /= e1 He1.
rewrite (bigD1 e1) //=.
case E1: (h e1)=> [|[|k]] //; first 2 last.
  - by rewrite !mulnS addnA !addnS.
  - by move/eqP: E1; rewrite eqN_eqC Hh normC_eq0 (negPf He1).
case: (boolP (forallb i, (i == e1) || ('[f, 'xi_i]_G == 0))).
  move/forallP=> {HH}HH.
  rewrite big1=> // i Hi.
  apply/eqP; rewrite eqN_eqC natr_mul Hh.
  move: (HH i); rewrite (negPf Hi) /=; move/eqP->.
  by rewrite normC0 mul0r.
rewrite negb_forall; case/existsP=> /= e2; rewrite negb_or.
case/andP=> Hd He2.
rewrite (bigD1 e2) //=.
case E2: (h e2)=> [|[|k]] //.
  by move/eqP: E2; rewrite eqN_eqC Hh normC_eq0 (negPf He2).
do 2 move/addnI; move/eqP; rewrite sum_nat_eq0.
move/forall_inP=> HH1.
have: f 1%g = 0.
  case/and3P: Hf=> _ _; move/off_support; apply.
  by rewrite !inE eqxx.
have Hfc: f = '[f, 'xi_e1]_G *: 'xi_e1 + '[f, 'xi_e2]_G *: 'xi_e2.
  rewrite -{1}(sum_inner_prodE F1) (bigD1 e1) //; congr (_ + _).
  rewrite (bigD1 e2) // big1 /= ?addr0 // => i Hi.
  case Ei: (h i) (HH1 _ Hi)=> // _.
  by move/eqP: Ei; rewrite eqN_eqC Hh normC_eq0; move/eqP->; rewrite scale0r.
rewrite Hfc ffunE [_ 1%g]ffunE [(_ (_ *: _)) 1%g]ffunE.
have /andP[/negP F _]: 0 < 'xi_e1 1%g + 'xi_e2 1%g.
  apply: sposC_addl; try apply: ltCW; apply/andP; split;
     try exact:irr1_neq0; rewrite irr1_degree ; apply: posC_nat.
rewrite (isZC_signE (isZC_inner_prod_vchar e1 Hf)) -Hh E1 mulr1 !scaler_sign.
rewrite (isZC_signE (isZC_inner_prod_vchar e2 Hf)) -Hh E2 mulr1 !scaler_sign.
move/eqP; do 2![case: ifP => _] => //; last by exists e1, e2.
  by rewrite -oppr_add oppr_eq0.
by exists e2, e1; rewrite addrC eq_sym.
Qed.


Lemma pf59b chi : chi \in irr L -> support chi \subset 1%g |: A ->
  exists2 mu, mu \in irr G & (chi - (chi^*)%CH)^\tau = mu - (mu^*)%CH.
Proof.
move => chiIrr suppChi.
case: (boolP (chi == (chi^*)%CH)).
  move/eqP <-.
  exists '1_G; first by rewrite irr_cfuni.
  by rewrite cfun_conjC1 !subrr Dade0.
move => chi_n_conj.
set f := _ - _.
have fC : f \in 'CF(L, A).
  rewrite memcE; apply/andP; split; last first.
    rewrite /f; case/irrIP: chiIrr => r <-.
    apply: memv_sub; first by rewrite memc_irr.
    by apply: memc_is_char; rewrite is_char_conjC ?is_char_irr.
  apply/subsetP => x; apply: contraR => xnA; rewrite !cfunE.
  move/subsetP: suppChi => /(_ x) => suppChi.
  have {suppChi} := contra suppChi; rewrite !inE negb_or xnA andbT negbK /fcf.
  case x1: (x == 1%g); last by move => /(_ isT) /eqP ->; rewrite conjC0 subrr.
  move/eqP: x1 -> => _; case/irrIP: chiIrr => r <-.
  case/isNatCP: (isNatC_irr1 r) => n; rewrite /fcf => ->.
  by rewrite conjC_nat subrr.
have fZ : f^\tau \in 'Z[irr G, G^#].
  have fZ : f^\tau \in 'Z[irr G].
    apply: Dade_vchar.
    rewrite vchar_split; apply/andP; split; last by exact: support_memc fC.
    rewrite /f; case/irrIP: chiIrr => r <-.
    apply/vcharP; exists 'xi_r; rewrite ?is_char_irr //.
    by exists (('xi_r)^*)%CH; rewrite ?is_char_conjC ?is_char_irr.
  rewrite vchar_split fZ andTb.
  have: Atau \subset G^#.
    by rewrite subsetD1 Dade_support_sub not_support_Dade_1.
  by apply: subset_trans; exact: support_Dade.
have norm_f_tau : '[f^\tau]_G = 2%:R.
  rewrite Dade_isometry // /f; move: chi_n_conj.
  case/irrIP: chiIrr => r <-.
  case/irrIP: (irr_conjC r) => t <-.
  rewrite inner_prodDl !inner_prodDr !inner_prodNl !inner_prodNr.
  rewrite !irr_orthonormal !eqxx [r == t]eq_sym.
  case tr: (t == r); first by move/eqP: tr ->; rewrite eqxx.
  by rewrite opprK subr0 mulr0n oppr0 add0r -natr_add addn1.
case: (vchar_isometry_base2 fZ norm_f_tau) => i; case => j [f_tau jni].
exists 'xi_i; first by exact: irr_xi.
suff <-: 'xi_j = (('xi_i)^*)%CH by [].
have: ((f^\tau)^*)%CH = - (f^\tau).
  rewrite (Dade_conjC fC).
  suff ->: (f^*)%CH = -f by rewrite linearN.
  by apply/ffunP => x; rewrite !cfunE rmorph_sub conjCK oppr_sub.
rewrite f_tau oppr_sub.
have ->: (('xi_i - 'xi_j)^*)%CH = (('xi_i)^*)%CH - (('xi_j)^*)%CH.
  by apply/ffunP => x; rewrite !cfunE rmorph_sub.
move/eqP; rewrite eq_sym; move/eqP => diff.
have := @irr_diff 1%N 1%N 'xi_j 'xi_i (('xi_i)^*)%CH (('xi_j)^*)%CH.
rewrite !scale1r !irr_xi !irr_conjC.
have ->: (1 == 0)%N = false by [].
have ->: 'xi_j == 'xi_i = false.
  case eq: (_ == _); last by [].
  by move/eqP: eq => eq; have := xi_inj eq => ji; move: jni; rewrite ji eqxx.
by rewrite !orFb => /(_ diff isT isT isT isT) /eqP.
Qed.


(**************************************)
(* PF 5.9(a) *)

(* Should be an automorphism of Q_|G| *)
Variable u : {rmorphism algC -> algC}.


Let u_fix_Z z : isZC z -> u z = z.
Proof.
rewrite isZCE; case/orP; case/isNatCP=> n; first by move ->; rewrite rmorph_nat.
by move/eqP; rewrite eqr_oppC => /eqP ->; rewrite rmorphN rmorph_nat.
Qed.


Definition u_map (alpha : {cfun gT}) : {cfun gT} :=
  [ffun x => u (alpha x)].


Lemma u_map_is_rmorphism : rmorphism u_map.
Proof.
split => [f g|]; first by apply/ffunP => x; rewrite !cfunE rmorph_sub.
by split => [f g|]; apply/ffunP => x; rewrite !cfunE (rmorphM, rmorph1).
Qed.


Canonical u_map_additive := Additive u_map_is_rmorphism.
Canonical u_map_rmorphism := RMorphism u_map_is_rmorphism.


Hypothesis u_map_irrG_inv : forall i, u_map ('xi[G]_i) \in irr G.


Let u_map_Z_mul z (f : {cfun gT}) : isZC z -> u_map (z *: f) = z *: u_map f.
Proof.
by move => isZ; apply/ffunP => x; rewrite !cfunE rmorphM [u z]u_fix_Z.
Qed.


Let u_map_natr_mul n (f : {cfun gT}): u_map (n%:R *: f) = n%:R *: u_map f.
Proof. apply: u_map_Z_mul; exact: isZC_nat. Qed.


Let u_map_inj : injective u_map.
Proof.
move => f g /ffunP => feg; apply/ffunP => x.
by move: (feg x); rewrite !ffunE => /fmorph_inj.
Qed.


Local Notation "alpha ^\u" := (u_map alpha)
  (at level 2, format "alpha ^\u").


Let support_umap (f : {cfun gT}) (S : {set gT}) : 
  (support f) \subset S -> support (f^\u) \subset S.
Proof.
move/subsetP => supp_fS; apply/subsetP => x.
apply: contraR => xnS.
move/contra: (supp_fS x) => /(_ xnS); rewrite inE /= negbK cfunE => /eqP ->.
by rewrite rmorph0.
Qed.



Lemma map_memc (K : {group gT}) S chi : 
  chi \in 'CF(K, S) -> chi^\u \in 'CF(K, S).
Proof.
move/cfun_memfP => [chi_supp chiJ].
apply/cfun_memfP; split => [x xnSK | x y yK]; last first.
  by rewrite !cfunE; congr (_ _); exact: chiJ.
by rewrite cfunE -(rmorph0 u); congr (_ _); exact: chi_supp.
Qed.

Lemma Dade_invariant alpha : alpha \in 'CF(L, A) ->
  (alpha^\tau) ^\u = (alpha^\u)^\tau.
Proof.
move => alphaC; apply/ffunP => g; rewrite cfunE -/fcf.
have alphauC := map_memc alphaC.
case: (boolP (g \in Atau)).
  case/bigcupP => a aA gD1.
  by rewrite (DadeE alphaC aA gD1) (DadeE alphauC aA gD1) cfunE.
move => gnAtau.
rewrite (off_support (support_Dade ddA alpha) gnAtau).
by rewrite (off_support (support_Dade ddA (alpha^\u)) gnAtau) rmorph0.
Qed.


(* Variables and assumptions of 5.9(a) *)

Variable calS : seq {cfun gT}.
Variable tau1 : {additive {cfun gT} -> {cfun gT}}.
Variable chi : {cfun gT}.

Hypothesis size_ge2 : size calS >= 2.
Hypothesis freeS : free calS.
Hypothesis sSirrL : {subset calS <= irr L}.
Hypothesis ZL_eq_ZA : 'Z[calS, L^#] = 'Z[calS, A].
Hypothesis S_inv : {in calS, forall f, f^\u \in calS}.
Hypothesis tau1_to : {in 'Z[calS], forall f, tau1 f \in 'Z[irr G]}.
Hypothesis tau1_isom : {in 'Z[calS] &, isometry L G tau1}.
Hypothesis tau1_tau : {in 'Z[calS, A], forall f, tau1 f = f^\tau}.
Hypothesis chiS : chi \in calS.


(* Basic ideas *)
Let psi_inZ psi : psi \in calS -> psi \in 'Z[calS].
Proof. by move => psiS; apply: memv_vchar => //; apply/subsetP => x. Qed.

Let psiVC psi : psi \in calS -> psi \in 'Z[calS, L].
Proof.
move => psiS; apply: memv_vchar => //. 
by case/irrIP: (sSirrL psiS) => r <-; exact: support_memc (memc_irr r).
Qed.


Let val1scaleZ f g (S : seq {cfun gT}) K : 
  f \in calS -> g \in 'Z[S, K] -> f 1%g *: g \in 'Z[S, K].
Proof.
move => fS gZ.
case/irrIP: (sSirrL fS) => r <-; rewrite -/fcf.
case/isNatCP: (isNatC_char1 (is_char_irr r)) => nn ->.
by rewrite scaler_nat; apply: vchar_scal.
Qed.


Let val1scale f g : f \in calS -> g \in calS -> f 1%g *: g \in 'Z[calS].
Proof. move => fS gS; apply: val1scaleZ => //; exact: psi_inZ. Qed.



Let diff_ZA (psi : {cfun gT}) : psi \in calS -> 
  psi 1%g *: chi - chi 1%g *: psi \in 'Z[calS, A].
Proof.
move => psiS; rewrite -ZL_eq_ZA.
rewrite vchar_split; apply/andP; split.
  by apply: vchar_sub; exact: val1scale.
apply/subsetP => x; apply: contraR; rewrite inE negb_and in_set1 negbK.
case/orP.
  by move/eqP ->; rewrite !cfunE /GRing.scale /= mulrC subrr.
move => xnL; rewrite !cfunE.
rewrite -!/fcf !(off_support (support_vchar (psiVC _)) xnL) //.
by rewrite !scaler0 subrr.
Qed.


Let sSCF : {subset calS <= 'CF(L)}.
Proof.
move => psi psiS; apply: memc_vchar.
have := vchar_subset freeS (free_irr L) sSirrL.
by move => /(_ L) /(_ _ (psiVC psiS)).
Qed.


Let vcharCF psi : psi \in 'Z[calS, A] -> psi \in 'CF(L, A).
Proof.
move => psiZ; apply: memc_vchar.
have := vchar_subset freeS (free_irr L) sSirrL.
by move => /(_ A psi psiZ).
Qed.


Let natr_psi1 (psi : {cfun gT}) : psi \in calS -> exists m, psi 1%g = m%:R.
Proof.
move => psiS; case/irrIP: (sSirrL psiS) => r <-.
by apply/isNatCP; exact: isNatC_irr1.
Qed.




Let free_uS : free (map u_map calS).
Proof.
have uniq_uS : uniq (map u_map calS).
  rewrite map_inj_in_uniq ?(uniq_free freeS) //.
  by move => f g _ _; exact: u_map_inj.
have uS_ieq_S : map u_map calS =i calS.
  have sub: {subset (map u_map calS) <= calS}.
    by move => f; case/mapP => g gS ->; exact: S_inv.
  have := leq_size_perm uniq_uS sub.
  by rewrite size_map leqnn => /(_ isT) [].
have uS_perm_S : perm_eq (map u_map calS) calS.
  by apply: uniq_perm_eq; rewrite ?uniq_uS ?(uniq_free freeS) ?uS_ieq_S.
by rewrite (free_perm_eq uS_perm_S); exact: freeS.
Qed.


Let sum_cast_ord (R : zmodType) (m n : nat) (eq : n = m) (F : 'I_m -> R) :
   \sum_(i < m) F i = \sum_(j < n) F (cast_ord eq j).
Proof.
case: (ltngtP n 0); first 2 last.
  move => n0; rewrite n0 in eq *; rewrite big_ord0.
  by rewrite big1 // => i; have := ltn_ord i; rewrite -{2}eq ltn0.
by rewrite ltn0.
move => n_gt0.
pose i0 := cast_ord eq (Ordinal n_gt0).
pose F1 i := F (odflt i0 (insub i)).
have ->: \sum_(i < m) F i = \sum_(i < m) F1 i.
  apply: eq_bigr => i _; rewrite /F1.
  case: insubP => [u0 _ /ord_inj -> | ] //=.
  by rewrite ltn_ord.
have m_le_n: (m <= n)%N by rewrite eq.
rewrite (big_ord_widen n F1 m_le_n).
apply: eq_big; first by move => i /=; rewrite -eq ltn_ord.
move => i _; rewrite /F1; case: insubP => /=; last by rewrite -{1}eq ltn_ord.
move => j _.
have ->: nat_of_ord i = nat_of_ord (cast_ord eq i) by [].
by move/ord_inj ->.
Qed.


Let uZS_inv f : f \in 'Z[calS] -> f^\u \in 'Z[calS].
Proof.
move => fZ; set uS := map u_map calS.
have suSS: {subset uS <= calS}.
  by move => g; case/mapP => g0 g0S ->; exact: S_inv.
have := vchar_subset free_uS freeS suSS.
move => /(_ [set: gT]); apply; apply/and3P.
pose S := in_tuple calS.
have f_span : f \in span S by exact: (span_vchar fZ).
have := coord_span f_span => {1 2}->.
set n := size _.
have ->: (\sum_(i < n) (coord S f) i *: S`_i)^\u =
         \sum_(i < n) (coord S f) i *: uS`_i.
  rewrite rmorph_sum; apply: eq_bigr => i _ /=.
  rewrite u_map_Z_mul; last by exact: (@isZC_coord_vchar _ _ _ [set: gT]).
  congr (_ *: _).
  by rewrite (@nth_map _ 0 _ 0 u_map i calS) // size_tuple ltn_ord.
split; last by [].
  rewrite /span (@big_nth _ _ _ _ 0) size_map big_mkord -/n.
  by apply: memv_sumr => i _; apply: memvZl; exact: memv_inj.
apply/forallP => j; rewrite -/uS.
have size_eq: size uS = n by rewrite size_map.
suff ->: \sum_(i < n) (coord S f) i *: uS`_i = 
  \sum_(i < size uS) (coord S f) (cast_ord size_eq i) *: uS`_(cast_ord size_eq i).
  by rewrite free_coords //; exact: (@isZC_coord_vchar _ _ _ [set: gT]).
pose F (i : 'I_n) := (coord S f) i *: uS`_i.
by rewrite (sum_cast_ord size_eq).
Qed.



Let uZSA_inv f : f \in 'Z[calS, A] -> f^\u \in 'Z[calS, A].
Proof.
rewrite [f \in _]vchar_split => /andP [] fZ supp_f.
rewrite vchar_split (uZS_inv fZ) andTb.
exact: support_umap.
Qed.


Let equation1 (psi : {cfun gT}) : psi \in calS ->
  psi 1%g *: (tau1 chi)^\u - chi 1%g *: (tau1 psi)^\u =
  psi 1%g *: tau1 (chi^\u) - chi 1%g *: tau1 (psi^\u).
Proof.
move => psiS; move: (diff_ZA psiS).
case: (natr_psi1 psiS) => a ->; case: (natr_psi1 chiS) => b -> diff.
transitivity ((a%:R *: chi - b%:R *: psi)^\tau)^\u.
  rewrite -tau1_tau ?diff // !scaler_nat raddf_sub !raddfMn /=.
  by rewrite rmorphD !rmorphMn rmorphN /=.
rewrite Dade_invariant; last by apply: vcharCF; exact: diff.
rewrite -tau1_tau; last by exact: uZSA_inv.
by rewrite rmorph_sub !scaler_nat !rmorphMn /= raddf_sub !raddfMn.
Qed.

  

Lemma vchar_norm1_irr f : f \in 'Z[irr G] -> '[f]_G = 1%:R ->
  (f \in irr G) || (- f \in irr G).
Proof.
move=> Hf.
rewrite (inner_prod_vchar Hf) //.
move/memc_vchar: (Hf)=>/memcW F1.
move=> HH.
pose h (t : Iirr G) := getNatC `|'[f, 'xi_t]_G|.
have Hh t: (h t)%:R = `|'[f, 'xi_t]_G|.
  exact/esym/eqP/normCZ_nat/(isZC_inner_prod_vchar t Hf).
have: (\sum_t (h t) * h t = 1)%N.
  apply/eqP; rewrite eqN_eqC -HH natr_sum; apply/eqP.
  apply: eq_bigr=> i _; rewrite natr_mul Hh -expr2 int_normCK //.
  exact: (isZC_inner_prod_vchar _ Hf).
case: (boolP (forallb i : Iirr G, '[f, 'xi_i]_G == 0)).
  move/forallP=> {HH}HH.
  rewrite big1=> // i _.
  apply/eqP; rewrite eqN_eqC natr_mul Hh.
  by rewrite (eqP (HH i)) normC0 mul0r.
rewrite negb_forall; case/existsP=> /= e1 He1.
rewrite (bigD1 e1) //=.
case E1: (h e1)=> [|[|k]] //.
  by move/eqP: E1; rewrite eqN_eqC Hh normC_eq0 (negPf He1).
rewrite muln1 -{2}add1n.
move/addnI/eqP; rewrite sum_nat_eq0.
move/forall_inP => HH1.
have Hfc: f = '[f, 'xi_e1]_G *: 'xi_e1.
  rewrite -{1}(sum_inner_prodE (memc_vchar Hf)) (bigD1 e1) //=.
  rewrite big1 ?addr0 // => i Hi.
  suff ->: '[f, 'xi_i]_G = 0 by rewrite scale0r.
  apply/eqP; rewrite -normC_eq0.
  case Ei: (h i) (HH1 _ Hi) => //.
  by rewrite -(Hh i) Ei.
rewrite Hfc.
suff [-> | ->]: '[f, 'xi_e1]_G = 1 \/ '[f, 'xi_e1]_G = -1.
- by apply/orP; left; rewrite scale1r irr_xi.
- by apply/orP; right; rewrite -scaleNr opprK scale1r irr_xi.
have: (isZC '[f, 'xi_e1]_G) by apply: (isZC_inner_prod_vchar _ Hf).
rewrite isZCE; move/orP; case => /isNatCP [k].
  by move => nk; left; move: (Hh e1); rewrite nk E1 normC_nat => <-.
move/eqP; rewrite eqr_oppC => /eqP nk; right; move: (Hh e1). 
rewrite /normC nk rmorphN conjC_nat mulrNN sqrtC_sqr_pos ?posC_nat //.
by rewrite E1 => <-.
Qed.


Let tau1_irr : exists eps : bool, forall (psi : {cfun gT}), psi \in calS ->
  exists2 mu, mu \in irr G & tau1 psi = (-1) ^+ eps *: mu.
Proof.
have psi_norm : forall psi, psi \in calS -> '[tau1 psi]_G = 1%:R.
  move => psi psiS; rewrite (tau1_isom (psi_inZ psiS)) ?(psi_inZ _) //.
  by case/irrIP: (sSirrL psiS) => r <-; rewrite irr_orthonormal eqxx.
have chi_irr := vchar_norm1_irr (tau1_to (psi_inZ chiS)) (psi_norm chi chiS).
have: exists eps : bool, exists2 zi, zi \in irr G & tau1 chi = (-1) ^+ eps *: zi.
  case/orP: chi_irr => H1.
    exists false; exists (tau1 chi) => //.
    by rewrite expr0 scale1r.
  exists true; exists (- tau1 chi) => //.
  by rewrite expr1 scaleN1r opprK.
case => eps [zi zi_irr zi_chi].
exists eps => psi psiS.
exists ((-1) ^+ eps *: tau1 psi); last first.
  rewrite scalerA.
  case: {zi_chi} eps; first by rewrite expr1 mulrNN mul1r scale1r.
  by rewrite expr0 mul1r scale1r.
set e := (-1) ^+ eps.
have e_cases: (e == 1) || (e == -1).
  by rewrite /e; case: {zi_chi e}eps; rewrite ?expr1 ?expr0 eqxx ?orbT ?orTb.
have: 0 < (e *: tau1 psi) 1%g.
  have: (psi 1%g *: tau1 chi - chi 1%g *: tau1 psi) 1%g = 0.
    move: (diff_ZA psiS).
    case: (natr_psi1 psiS) => a ->.
    case: (natr_psi1 chiS) => b ->.
    rewrite !scaler_nat => diff.
    by rewrite -!raddfMn -raddf_sub tau1_tau // -/fcf Dade1.
  rewrite zi_chi -/e !cfunE.
  move/eqP; rewrite subr_eq0 => /eqP.
  set lhs := _ *: _; set rhs := _ *: _; move => eq1.
  have: (e * (chi 1%g)^-1) * rhs = (e * (chi 1%g)^-1) * lhs by congr (_ * _).
  have /andP [/andP [chi0 psi0] zi0]: (0 < chi 1%g) && (0 < psi 1%g) && (0 < zi 1%g).
    case/irrIP: (sSirrL chiS) => ? <-.
    case/irrIP: (sSirrL psiS) => ? <-.
    case/irrIP: zi_irr => ? <-.
    by rewrite !ltC_irr1 andTb.
  have chi1_unit: GRing.unit (chi 1%g).
    by rewrite unitfE; rewrite ltCE in chi0; move/andP: chi0 => [].
  have ->: e / chi 1%g * rhs = e * (tau1 psi) 1%g.
    by rewrite /rhs mulrA -[e * _ * _]mulrA mulVr // mulr1.
  rewrite /GRing.scale /= => ->.
  have ->: e / chi 1%g * lhs = (chi 1%g)^-1 * psi 1%g * zi 1%g.
    rewrite /lhs /GRing.scale /=.
    rewrite mulrA mulrCA !mulrA.
    suff ->: e * e = 1 by rewrite mul1r.
    by case/orP: e_cases; move/eqP ->; rewrite ?mulrNN mul1r.
  by apply: sposC_mul => //; apply: sposC_mul => //; rewrite sposC_inv.
move => posH.
have psi_irr := vchar_norm1_irr (tau1_to (psi_inZ psiS)) (psi_norm psi psiS).
have anti_ltC a : 0 < a -> 0 < -a -> False.
  rewrite !ltCE eqr_oppC oppr0.
  move/andP => [an0 age0] /andP [_ nage0].
  have ale0: a <= 0.
    by move: nage0; rewrite -leC_sub -[a <= 0]leC_sub addrC oppr0.
  by move: (leC_anti ale0 age0) => aeq0; move: an0; rewrite aeq0 eqxx.
case/orP: psi_irr; case/orP: e_cases; move/eqP => ee; rewrite ee ?scaleNr scale1r //.
  move => psi_irr.
  have negH: 0 < (tau1 psi) 1%g.
    by case/irrIP: psi_irr => ? <-; rewrite ltC_irr1.
  rewrite ee scaleNr scale1r ffunE in posH.
  by have:= anti_ltC _ negH posH.
move => psi_irr.
have negH: 0 < (- tau1 psi) 1%g.
  by case/irrIP: psi_irr => ? <-; rewrite ltC_irr1.
rewrite ee scale1r in posH; rewrite ffunE in negH.
by have:= anti_ltC _ posH negH.
Qed.


Let exists_psi : exists2 psi, psi \in calS & chi != psi.
Proof.
pose S := remove1 calS chi.
pose psi := S`_0.
have: psi \in S.
  apply: mem_nth; rewrite remove1_size ?uniq_free //.
  rewrite -(ltn_add2l 1) !add1n prednK //.
  by apply: (ltn_trans _ size_ge2).
by rewrite mem_filter /= eq_sym => /andP [chi_n_psi psiS]; exists psi.
Qed.


Lemma pf59a : (tau1 chi)^\u = tau1 (chi^\u).
Proof.
case: exists_psi => psi psiS chi_n_psi.
have := equation1 psiS.
case: (natr_psi1 psiS) => a a_psi1; rewrite a_psi1.
case: (natr_psi1 chiS) => b ->.
case: tau1_irr => eps; set e := _ ^+ _; move => psi_irr.
have: (tau1 chi)^\u != (tau1 psi)^\u.
  move: chi_n_psi; apply: contra.
  move/eqP/u_map_inj/eqP; rewrite -subr_eq0 => /eqP diff0.
  rewrite -subr_eq0 -(@inner_prod0 _ L); last by apply: memv_sub; apply: sSCF.
  rewrite -tau1_isom ?vchar_sub ?psi_inZ //.
  by rewrite raddf_sub diff0 inner_prod0l.
case: (psi_irr _ (S_inv psiS)) => g2 g2_irr ->.
case: (psi_irr _ (S_inv chiS)) => f2 f2_irr ->.
case: (psi_irr _ psiS) => g1 g1_irr ->.
case: (psi_irr _ chiS) => f1 f1_irr ->.
have isZe : isZC e.
  have isZ1 : isZC 1 by have <-: 1%:R = 1 by []; rewrite isZC_nat.
  rewrite /e; case: {e psi_irr} eps; rewrite ?expr1 ?expr0 ?isZC_opp //.
have e_n0: e != 0.
  rewrite /e; case: {e isZe psi_irr} eps; rewrite ?expr1 ?expr0 ?nonzero1r //.
  by rewrite eqr_oppC oppr0 nonzero1r.
rewrite !u_map_Z_mul // => H1.
rewrite !scalerA mulrC [_ * e]mulrC -!scalerA -!scaler_subr.
move/(scalerI e_n0) => diff.
have := irr_diff diff.
have ->: f1^\u \in irr G by case/irrIP: f1_irr => r <-; exact: u_map_irrG_inv.
have ->: g1^\u \in irr G by case/irrIP: g1_irr => r <-; exact: u_map_irrG_inv.
move => /(_ isT isT f2_irr g2_irr).
have ->: (f1^\u == g1^\u) = false.
  by move: H1; apply: contraNF => /eqP ->.
have ->: (a == 0)%N = false.
  apply/negP; apply/negP; rewrite neq0N_neqC -a_psi1.
  by case/irrIP: (sSirrL psiS) => r <-; rewrite irr1_neq0.
by rewrite !orFb => /eqP ->.
Qed.


End Five.



Section FiveSpecial.

Variable calS : seq {cfun gT}.
Variable tau1 : {additive {cfun gT} -> {cfun gT}}.
Variable chi : {cfun gT}.

Hypothesis size_ge2 : size calS >= 2. 
Hypothesis freeS : free calS.
Hypothesis sSirrL : {subset calS <= irr L}.
Hypothesis ZL_eq_ZA : 'Z[calS, L^#] = 'Z[calS, A].
Hypothesis S_inv : forall f, f \in calS -> (f^*)%CH \in calS.
Hypothesis tau1_to : {in 'Z[calS], forall f, tau1 f \in 'Z[irr G]}.
Hypothesis tau1_isom : {in 'Z[calS] &, isometry L G tau1}.
Hypothesis tau1_tau : {in 'Z[calS, A], forall f, tau1 f = f^\tau}.
Hypothesis chiS : chi \in calS.


Lemma pf59a_conjC : ((tau1 chi)^*)%CH = tau1 ((chi^*)%CH).
Proof.
apply: (pf59a _ size_ge2 freeS sSirrL) => //.
by move => i; rewrite irr_conjC.
Qed.


End FiveSpecial.


(**********************************)
(* 7.1 *)

Definition rho_fun (chi : {cfun gT}) : {cfun gT} :=
  [ffun a => 
    if a \in A then #|H a|%:R ^-1 * (\sum_(x \in H a) chi (x * a)%g) else 0].



Lemma rho_is_linear : linear rho_fun.
Proof.
move=> mu alpha beta; apply/ffunP=> a; rewrite !cfunE.
case: (_ \in _); last by rewrite scaler0 addr0.
rewrite scaler_mulr scaler_sumr -mulr_addr -big_split.
by congr (_ * _); apply: eq_bigr=> i _; rewrite !cfunE.
Qed.


Canonical rho_linear := Linear rho_is_linear.
Canonical rho_additive := Additive rho_is_linear.


Local Notation "alpha ^\rho" := (rho_fun alpha)
  (at level 2, format "alpha ^\rho").




Lemma support_rho chi : support chi^\rho \subset A.
Proof.
apply/subsetP=> x; rewrite !inE /rho_fun cfunE;
by case: (_ \in _); rewrite ?(eqxx 0).
Qed.



Lemma rho_cfunS chi : chi \in 'CF(G) -> chi^\rho \in 'CF(L, A).
Proof.
move => chiC; apply/cfun_memfP; split=> [a | a x xL].
  by rewrite (setIidPl sAL) => aA; rewrite (off_support (support_rho chi)).
have aaxA: (a \in A) = (a ^ x \in A).
  by rewrite -mem_conjgV (normP _) // in_group (subsetP nAL x xL).
case aA: (a \in A); last by rewrite !(off_support (support_rho chi)) -?aaxA ?aA.
rewrite !cfunE -aaxA aA (DadeJ ddA) // cardJg.
congr (_ * _); rewrite big_imset /=; last first.
  by move=> y y0 _ _ /=; exact: conjg_inj.
apply: eq_bigr => i _; rewrite -conjMg.
by move/cfun_memP: chiC => [_]; apply; exact: subsetP sLG x xL.
Qed.



(* 7.2(a) *)
Lemma pf72a alpha : alpha \in 'CF(L, A) -> (alpha^\tau)^\rho = alpha.
Proof.
move => alphaC.
apply/ffunP => a; rewrite ffunE.
case aA: (_ \in _); last by symmetry; apply: (cfunS0 alphaC); rewrite aA.
rewrite -[alpha _]mul1r.
rewrite -{2}(@mulVr _ (#|H a|%:R)) -?mulrA; first last.
  rewrite unitfE -neq0N_neqC cards_eq0.
  by apply/eqP => h0; apply: (@group_not0 gT (H a)); rewrite h0.
congr (_ * _); rewrite -sum1_card natr_sum -mulr_suml mul1r.
apply: eq_bigr => u uHa.
rewrite (DadeE alphaC aA) //; apply: (subsetP (sub_class_support _ _)).
by apply: mem_mulg; first by []; exact: set11.
Qed.



Lemma rho_Dade_reciprocity chi alpha : chi \in 'CF(G) -> alpha \in 'CF(L, A) ->
  '[alpha^\tau, chi]_G = '[alpha, chi^\rho]_L.
Proof.
move => chiC alphaC.
apply: (general_Dade_reciprocity _ _ _ _) => //.
  exact: memcW (rho_cfunS chiC).
by move => a aA /=; rewrite /rho_fun ffunE aA.
Qed.



(* 7.2(b) *)
Lemma pf72b chi : chi \in 'CF(G) -> 
  '[chi^\rho]_L <= '[chi]_G ?= iff (chi == (chi^\rho)^\tau).
Proof.
move => chiC.
set w := (chi^\rho)^\tau.
have chi_rhoC := rho_cfunS chiC.
have ortho: '[w, chi - w]_G = 0.
  rewrite /w rho_Dade_reciprocity; last by [].
    by rewrite linear_sub /= pf72a ?subrr ?inner_prod0r ?rho_cfunS.
  by apply: memv_sub; first by []; apply: Dade_cfun.
move: (ortho); rewrite inner_conj => /eqP; rewrite conjC_eq0 => /eqP ortho2.
have <-: '[w]_G = '[chi^\rho]_L by rewrite Dade_isometry //.
rewrite -{1 2}(subrK w chi).
set v := chi - w in ortho ortho2 *.
rewrite inner_prodDl 2!inner_prodDr ortho ortho2 addr0 add0r.
apply/leCifP; case eq: (_ == _); move/eqP: eq => eq.
  by rewrite /v eq subrr inner_prod0l add0r.
rewrite ltCE -leC_sub -addrA subrr addr0 posC_inner_prod andbT.
apply/eqP => hyp; apply: eq.
rewrite -{2}['[w]_G]add0r in hyp; move/addIr/eqP: hyp.
rewrite inner_prod0 /v ?subr_eq0; first by move/eqP ->.
by apply: memv_sub; first by []; apply: Dade_cfun.
Qed.


Lemma inner_prod_supportE (S : {set gT}) (K : {group gT}) (f g : {cfun gT}) :
  support f \subset S -> S \subset K ->
  '[f, g]_K = #|K|%:R ^-1 * (\sum_(x \in S) f x * (g x)^*).
Proof.
move => supp_f sSK; rewrite inner_prodE.
congr (_ * _); rewrite (big_setID S) /= addrC (setIidPr sSK) big1 ?add0r //.
move => x /setDP [_ xnS].
apply/eqP; rewrite mulf_eq0; apply/orP; left; apply/eqP.
by apply: (off_support supp_f).
Qed.



Lemma norm_supportE (S : {set gT}) (K : {group gT}) (f : {cfun gT}) : 
  support f \subset S -> S \subset K ->
  '[f]_K = #|K|%:R ^-1 * (\sum_(x \in S) normC (f x) ^+ 2).
Proof.
move => supp_f sSK; rewrite (inner_prod_supportE f supp_f sSK).
by congr (_ * _); apply: eq_bigr => x _; rewrite sqrtCK.
Qed.



Lemma norm_chi_rho chi : chi \in 'CF(G) ->
  '[chi^\rho]_L 
  = #|L|%:R ^-1 * (\sum_(a \in A) normC (chi^\rho a) ^+ 2).
Proof. by move => chiC; apply norm_supportE; rewrite ?sAL ?(support_rho). Qed.


Lemma Dade_supportJ g : g \in G -> Atau :^ g = Atau.
Proof.
move => gG; rewrite /Atau -bigcupJ; apply: eq_bigr => a aA.
rewrite /Dade_support1 class_supportEl -bigcupJ; apply: eq_bigr => x _.
by rewrite -class_rcoset (rcoset_id gG).
Qed.



(* 7.3 *)
Lemma pf73 chi : chi \in 'CF(G) ->
  '[chi^\rho]_L <=
  #|G|%:R ^-1 * (\sum_(g \in Atau) normC (chi g) ^+ 2) ?= iff
    (forallb a, (a \in A) ==> 
      (forallb u, (u \in H a) ==> (chi (u * a)%g == chi a))).
Proof.
move => chiC.
pose chi1 := [ffun g => if g \in Atau then chi g else 0].
have chi1C: chi1 \in 'CF(G).
  apply/cfun_memP; split => [x | x y yG].
    apply: contraNeq; rewrite /chi1 cfunE.
    case xAtau: (_ \in _); last by move/eqP; case.
    move => _; exact: (subsetP (Dade_support_sub ddA) x xAtau).
  have xy: (x \in Atau) = (x ^ y \in Atau).
    by rewrite -[x \in _](memJ_conjg Atau y) Dade_supportJ.
  symmetry; rewrite /chi1 !cfunE -xy; case xAtau: (_ \in _) => //.
  by symmetry; apply: (cfunJ x chiC).
have <-: chi1^\rho = chi^\rho.
  apply/ffunP => a; rewrite !ffunE.
  case aA: (_ \in _); last by [].
  congr (_ * _); apply: eq_bigr => x xHa; rewrite cfunE.
  suff ->: (x * a)%g \in Atau by [].
  apply/bigcupP; exists a; first by [].
  rewrite /Dade_support1 class_supportEr; apply/bigcupP. 
  exists 1%g; rewrite ?in_group ?conjsg1 //.
  by apply/rcosetP; exists x.
set RHS := _ * _.
have <-: '[chi1, chi1]_G = RHS.
  have supp1: support chi1 \subset Atau.
    apply/subsetP => x.
    rewrite !inE /chi1 ffunE.
    by case: (_ \in _); [ | move/eqP; case].
  rewrite (norm_supportE supp1 (Dade_support_sub _)) /RHS.
  congr (_ * _); apply: eq_bigr => x xAtau; congr (_ _ ^+ 2).
  by rewrite cfunE xAtau.
have := pf72b chi1C.
set C1 := chi1 == _.
set C2 := (forallb a, _).
suff ->: C1 = C2; first by [].
have xa: forall a x, a \in A -> x \in H a -> chi (x * a)%g = chi1 (x * a)%g.
  move => a x aA xHa; rewrite !ffunE.
  suff ->: (x * a)%g \in Atau by [].
  apply/bigcupP; exists a => //.
  rewrite /Dade_support1 class_supportEr; apply/bigcupP.
  exists 1%g; first by rewrite in_group.
  by rewrite conjsg1; apply/rcosetP; exists x.
apply/eqP/forallP.
  move => chi1_eq a.
  apply/implyP => aA; apply/forallP => x; apply/implyP => xHa; apply/eqP.
  rewrite -{2}[a]mul1g !xa ?in_group // mul1g chi1_eq.
  rewrite -/fcf !(DadeE (rho_cfunS chi1C) aA) // /Dade_support1 class_supportEr.
    apply /bigcupP; exists 1%g; first by rewrite in_group.
    by rewrite conjsg1; apply/rcosetP; exists 1%g; rewrite ?in_group ?mul1g.
  apply/bigcupP; exists 1%g; first by rewrite in_group.
  by rewrite conjsg1; apply/rcosetP; exists x.
move => hyp; apply/ffunP => g.
rewrite cfunE.
case gAtau: (_ \in _); last first.
  symmetry; apply (off_support (support_Dade ddA chi1^\rho)).
  by rewrite gAtau.
case/bigcupP: gAtau => a aA.
rewrite /Dade_support1 class_supportEr.
case/bigcupP => x xG.
case/imsetP => y.
case/rcosetP => u uHa -> -> {y}.
rewrite -/fcf (cfunJ _ chiC xG).
rewrite -/fcf (cfunJ _ (Dade_cfun ddA (rho_cfunS chi1C)) xG) => {x xG}.
rewrite (DadeE (rho_cfunS chi1C) aA); last first.
  rewrite /Dade_support1 class_supportEr; apply/bigcupP.
  exists 1%g; first by rewrite in_group.
  by rewrite conjsg1; apply/rcosetP; exists u.
rewrite /rho_fun cfunE aA.
rewrite /fcf -[chi _]mul1r.
rewrite -{1}(@mulVf _ (#|H a|%:R)) -?mulrA ?neq0GC //.
congr (_ * _); rewrite -sum1_card natr_sum -mulr_suml mul1r.
apply: eq_bigr => x xHa; rewrite !/fcf -xa //.
move/implyP: {hyp}(hyp a) => /(_ aA) /forallP => hyp.
by move: (hyp x) (hyp u)=> /implyP/(_ xHa)/eqP=> -> /implyP/(_ uHa)/eqP=> ->.
Qed.


(* 7.6 & 7.7 *)
Section PF77.

(* 7.6 *)
(* K == H in the text *)
Variable K : {group gT}.
Hypothesis nKL : K <| L.
Hypothesis AK1 : A = K ^#.

Let sKL : K \subset L. Proof. by move/andP: nKL => []. Qed.

Let k := #|K|%:R : algC.
Let e := #|L : K|%:R : algC.

Let unit_k : k != 0. Proof. by rewrite -neq0N_neqC -lt0n cardG_gt0. Qed.

Let unit_e : e != 0. Proof. by rewrite -neq0N_neqC -lt0n indexg_gt0. Qed.

Let ke : k * e = #|L|%:R.
Proof. by apply/eqP; rewrite -natr_mul -eqN_eqC LaGrange. Qed.



Variable zi : seq {cfun gT}.

Hypothesis zi_uniq : uniq zi.
Hypothesis ziP : forall t,
  reflect (exists i, t = 'Ind[L, K] ('xi[K]_i)) (t \in zi).

Let size_zi_gt0 : (0 < size zi)%N.
Proof.
case nn: (size zi); last by [].
have: ('Ind[L, K] 'xi[K]_0 \in zi) by apply/ziP; exists 0.
by rewrite (size0nil nn) in_nil.
Qed.

Let n := size zi.

Let in_zi (i : 'I_n) : zi`_i \in zi. Proof. exact: mem_nth. Qed.

Let i0 := Ordinal size_zi_gt0.
Let d i := zi`_i 1%g / zi`_0 (1%g).

Let zi0 : zi`_0 = zi`_i0. Proof. by []. Qed.

Let zi_val1 i : zi`_i (1%g) = d i * zi`_0 (1%g).
Proof.
rewrite -mulrA mulVf ?mulr1 // zi0.
case/ziP: (in_zi i0) => r ->.
by rewrite -/fcf cinduced1 // mulf_neq0 ?irr1_neq0.
Qed.


(* 7.7 *)

Variable chi : {cfun gT}.
Hypothesis chiC : chi \in 'CF(G).

Let c i := '[(zi`_i - d i *: zi`_0)^\tau, chi]_G.

Let zi_ind (i : 'I_n) : exists r, zi`_i = 'Ind[L, K] 'xi[K]_r.
Proof. by move/ziP: (in_zi i). Qed.

Let ziC (i : 'I_n) : zi`_i \in 'CF(L, K).
Proof.
case: (zi_ind i) => r ->; rewrite memcE; apply/andP; split.
  by apply: support_induced; rewrite ?memc_irr.
by apply: memc_induced; [by move/andP: nKL => [] | by rewrite memc_irr].
Qed.


Let zi1_neq_0 (i : 'I_n) : zi`_i (1%g) != 0.
case: (zi_ind i) => r ->.
rewrite -/fcf cinduced1; last by move/andP: nKL => [].
by rewrite mulf_neq0 ?irr1_neq0.
Qed.


Let norm_zi_unit (i : 'I_n) : '[zi`_i]_L != 0.
Proof.
case eq0: ('[_, _]_L == 0); last by [].
move: eq0; rewrite (inner_prod0 (memcW (ziC i))).
move/eqP => eq0; move: (zi1_neq_0 i).
by rewrite eq0 ffunE eqxx.
Qed.



Let inner_zi0 (i j : 'I_n) : i != j -> '[zi`_i, zi`_j]_L = 0.
Proof.
move => i_neq_j.
have: zi`_i != zi`_j.
  move: i_neq_j; apply: contraR; rewrite negbK => zi_eq.
  have := nth_uniq 0 (ltn_ord i) (ltn_ord j) zi_uniq.
  rewrite zi_eq => /eqP; rewrite eq_sym => /eqP /eqP h1.
  apply/eqP; exact: ord_inj.
case/ziP: (in_zi i) => r ->.
case/ziP: (in_zi j) => t ->.
have := cconjugates_irr_induced r t nKL.
by case: (_ \in _) => //; move ->; rewrite eqxx.
Qed.


Let inner0 (X : {group gT}) m (psi : 'I_m -> {cfun gT}) (f : {cfun gT}) f_ :
  (forall i, psi i \in 'CF(X)) ->
  f = \sum_(i < m) f_ i *: psi i -> 
  (forall i, '[psi i, f]_X = 0) -> f = 0.
Proof.
move => psiC f_eq inner0.
have fC : f \in 'CF(X).
  by rewrite f_eq; apply: memv_suml => i _; apply: memvZl.
apply/eqP; rewrite -(inner_prod0 fC) {1}f_eq.
rewrite -inner_prodbE linear_sum big1 //= => i _.
rewrite linearZ /=; apply/eqP; rewrite scaler_eq0.
by apply/orP; right; rewrite /= inner_prodbE; move/eqP: (inner0 i).
Qed.


Let crestr1 (X : {group gT}) (S : {set gT}) (f : {cfun gT})
  (h := [ffun g => if g \in S^# then f g else 0]) :
    f \in 'CF(X, S) -> h \in 'CF(X, S^#)
    /\ {in S^#, forall g, f g = h g}
    /\ {in 'CF(X, S^#), forall psi, '[psi, f]_X = '[psi, h]_X}.
Proof.
move => fC.
pose c1 := [ffun g => if g == 1%g then 1 else 0] : {cfun gT}.
have c1C : c1 \in 'CF(X).
  apply/cfun_memP; split => [x xnG | x y yG]; rewrite !cfunE.
    case x1: (_ == _) => //.
    by move/eqP: x1 => x1; move: xnG; rewrite x1 in_group.
  case x1: (x == _); first by move/eqP: x1 ->; rewrite conj1g eqxx.
  case xy1: (_ == _) => //.
  move/eqP: xy1.
  rewrite conjgE -(mulVg y) => h1.
  have {h1} := mulgI _ _ _ h1.
  rewrite -{2}[y]mul1g => h1.
  have {h1} := mulIg _ _ _ h1.
  by move => xx1; move: x1; rewrite xx1 eqxx.
have: h = f - (f (1%g)) *: c1.
  apply/ffunP => g; rewrite !ffunE.
  case gS1: (_ \in _); rewrite in_setD1 in gS1.
    move/andP: gS1 => [].
    by case: (_ == _) => //; rewrite scaler0 subr0.
  move/negP: gS1 => /negP; rewrite negb_and negbK.
  case/orP; first by move/eqP ->; rewrite /GRing.scale /= eqxx mulr1 subrr.
  move => gnS; rewrite -/fcf (cfunS0 fC gnS).
  case g1: (_ == _); last by rewrite scaler0 subrr.
  rewrite (cfunS0 fC) /GRing.scale /= ?(mulr1, subrr) //.
  by move/eqP: g1 <-.
move => h_def.
split.
  rewrite memcE.
  apply/andP; split.
    apply/subsetP => x.
    rewrite inE /= /h ffunE.
    by case: (_ \in _) => //; rewrite eqxx.
  rewrite h_def.
  apply: memv_sub; first by rewrite (memcW fC).
  exact: memvZl.
split; first by move => g gS1 /=; rewrite ffunE gS1.
move => psi psiC /=.
rewrite !inner_prodE.
congr (_ * _).
apply: eq_bigr => g gG.
rewrite cfunE.
case gS1: (_ \in _) => //.
rewrite conjC0 mulr0.
apply/eqP; rewrite mulf_eq0; apply/orP; left.
by rewrite (cfunS0 psiC) // gS1.
Qed.



(* 7.7(a) *)
Lemma pf77a x : x \in A ->
  (chi^\rho) x = 
  \sum_(i < n) (c i)^* / '[zi`_i]_L * zi`_i x.
Proof.
move/andP: (nKL) => [_] sLNK xA.
pose psi (i : 'I_n) := zi`_i - d i *: zi`_0.
have psiC: forall i, psi i \in 'CF(L, A).
  move => i; rewrite memcE.
  apply/andP; split; last first.
    apply: memv_sub; first by exact: (memcW (ziC _)).
    by apply: memvZl; rewrite zi0; exact: (memcW (ziC _)).
  apply/subsetP => g; rewrite inE /=; apply: contraR.
  rewrite AK1 inE negb_and negbK in_set1 !ffunE.
  case/orP => [| gnK]; first by move/eqP ->; rewrite zi_val1 subrr.
  suff [-> ->]: zi`_i g = 0 /\ zi`_0 g = 0 by rewrite scaler0 subrr.
  by rewrite zi0; split; apply: (off_support (support_memc (ziC _)) gnK).
have f_eq: forall f, f \in 'CF(L, A) -> f = e^-1 *: 'Ind[L, K] ('Res[K] f).
  move => f fC; apply/ffunP => g; rewrite ffunE.
  case: (boolP (g \in K)) => gK.
    rewrite !ffunE -/k.
    set S := \sum_(y \in _) _.
    have {S}->: S = \sum_(y \in L) f g.
      apply: eq_bigr => u uL.
      rewrite crestrictE; first by exact: (cfunJ _ fC).
      by rewrite memJ_norm //; move/subsetP: sLNK => /(_ u uL).
    rewrite sumr_const /GRing.scale /= mulrA -invf_mul [e * k]mulrC ke.
    rewrite -[f g *+ _]mulr_natl mulrA mulVf ?mul1r //.
    by rewrite -neq0N_neqC -lt0n cardG_gt0.
  have suppInd := support_induced (memc_restrict sKL (memcW fC)) nKL.
  rewrite -!/fcf (off_support suppInd gK) scaler0.
  apply: (off_support (support_memc fC)).
  by move: gK; apply: contra; rewrite AK1 inE => /andP [].
have: forall f, f \in 'CF(L, A) -> f \in (\sum_(i < n) (zi`_i)%:VS)%VS.
  move => f fC; rewrite (f_eq f fC).
  rewrite -(sum_inner_prodE (memc_restrict sKL (memcW fC))).
  apply: memvZl; rewrite linear_sum /=; apply: memv_suml => r _.
  rewrite linearZ /=; apply: memvZl.
  apply/memv_sumP.
  have: exists j : 'I_n, 'Ind[L, K] 'xi_r = zi`_j.
    have: 'Ind[L, K] 'xi_r \in zi by apply/ziP; exists r.
    by case/(nthP 0) => j j_lt_n j_ind; exists (Ordinal j_lt_n); rewrite j_ind.
  case => i ->.
  exists (fun j => if j == i then zi`_i else 0); split.
    move => j _; case ji: (_ == _); last by exact: mem0v.
    by move/eqP: ji ->; exact: memv_inj.
  by rewrite -big_mkcond big_pred1_eq.
move => {f_eq} f_in_zi.
have: forall f, f \in 'CF(L, A) -> exists f_, f = \sum_(i < n) (f_ i *: psi i).
  move => f fC; have := f_in_zi f fC.
  case/memv_sumP => fv [fv_def f_sum].
  have: exists f_, forall i, fv i = f_ i *: zi`_i.
    exists (fun i => (fv i (1%g)) / zi`_i 1%g) => i.
    have:= fv_def  i => /(_ isT).
    case/injvP => fc ->.
    congr (_ *: _); rewrite ffunE /GRing.scale /= -mulrA.
    by rewrite mulrV ?mulr1 ?unitfE ?(zi1_neq0 i).
  case => f_ f_def; exists f_.
  have ->: \sum_(i < n) f_ i *: psi i = 
       \sum_(i < n) f_ i *: zi`_i - (\sum_(i < n) f_ i * d i) *: zi`_0.
    rewrite scaler_suml -sumr_sub.
    by apply: eq_bigr => i _; rewrite scaler_subr scalerA.
  suff ->: \sum_(i < n) f_ i * d i = 0.
    by rewrite scale0r subr0 f_sum; apply: eq_bigr => i _; exact: f_def.
  have: (\sum_(i < n) f_ i * d i) * zi`_0 1%g = f 1%g.
    rewrite -mulr_suml f_sum /= sum_ffunE ffunE.
    by apply: eq_bigr => i _; rewrite -mulrA -zi_val1 f_def ffunE.
  rewrite -!/fcf (cfunS0 fC); last first.
    by rewrite AK1 in_setD1 negb_and negbK eqxx orTb.
  move/eqP; rewrite mulf_eq0; move: (zi1_neq_0 i0).
  case: (zi`_0 _ == 0); first by [].
  by rewrite orbF => _ /eqP.
move => {f_in_zi} f_in_psi.
have {f_in_psi}f_eq0: forall f, f \in 'CF(L, A) ->
  (forall j, '[psi j, f]_L = 0) -> f = 0.
  move => f fC prod0; have := f_in_psi f fC; case => f_ f_sum.
  apply: (@inner0 L n psi f f_ _ f_sum prod0).
  by move => i; exact: (memcW (psiC i)).
pose b i := (c i)^* / '[zi`_i, zi`_i]_L.
have b0 : b i0 = 0.
  rewrite /b; suff ->: c i0 = 0 by rewrite conjC0 mul0r.
  rewrite /c (rho_Dade_reciprocity chiC (psiC i0)).
  suff ->: psi i0 = 0 by rewrite inner_prod0l.
  rewrite /psi; suff ->: d i0 = 1 by rewrite scale1r subrr.
  by rewrite /d mulrV // unitfE zi1_neq_0.
pose f := chi^\rho - \sum_(i < n) b i *: zi`_i.
have fC : f \in 'CF(L, K).
  apply: memv_sub; last by apply: memv_suml => i _; apply: memvZl; exact: ziC.
  by apply: (memc_subset _ (rho_cfunS chiC)); rewrite AK1 subsetDl.
have := crestr1 fC.
set h := [ffun _ => _]; rewrite -AK1.
case => hC; case => /(_ x xA) f_eq_h h_inner; move: f_eq_h.
suff ->: h = 0.
  rewrite [in X in _ = X]cfunE cfunE => /eqP.
  rewrite -!/fcf addr_eq0 => /eqP ->; rewrite sum_cfunE cfunE opprK ffunE.
  by apply: eq_bigr => i _; rewrite cfunE /GRing.scale /= -mulrA.
apply: (f_eq0 h hC) => j; rewrite -h_inner ?psiC // raddf_sub /=.
have ->: '[psi j, chi^\rho]_L = c j.
  by rewrite -(rho_Dade_reciprocity chiC (psiC j)).
rewrite inner_prodDl inner_prodNl !raddf_sum /=.
have ->: \sum_(i < n) '[zi`_j, b i *: zi`_i]_L = 
      \sum_(i < n) if (i == j) then (b j)^* * '[zi`_j]_L else 0.
  apply: eq_bigr => i _; rewrite inner_prodZ.
  case ij: (_ == _); first by move/eqP: ij ->.
  rewrite eq_sym in ij; move/negP: ij => /negP => inj.
  by rewrite (inner_zi0 inj) mulr0.
rewrite -big_mkcond big_pred1_eq big1; last first.
  move => i _; rewrite inner_prodZr inner_prodZl.
  case i_eq0: (i == i0).
    by move/eqP: i_eq0 ->; rewrite b0 conjC0 mul0r oppr0.
  rewrite eq_sym in i_eq0; move/negP: i_eq0 => /negP => in0.
  by rewrite (inner_zi0 in0) !mulr0 oppr0.
rewrite /b rmorphM conjCK.
rewrite fmorphV // -inner_conj -mulrA mulVf //.
by rewrite addr0 mulr1 subrr.
Qed.



Lemma mulr_sum (I J : finType) (f : I -> algC) (g : J -> algC) :
  (\sum_(i \in I) f i) * (\sum_(j \in J) g j) = 
  \sum_(i \in I) \sum_(j \in J) f i * g j.
Proof.
elim/big_rec2: _; first by rewrite mul0r.
by move => i y1 y2 _ <-; rewrite mulr_addl mulr_sumr.
Qed.


Lemma pf77b : '[chi^\rho]_L = 
  \sum_(i < n) \sum_(j < n) 
  ((c i)^* * c j / '[zi`_i]_L / '[zi`_j]_L
    * ('[zi`_i, zi`_j]_L - zi`_i 1%g * zi`_j 1%g / (e * k))).
Proof.
rewrite (norm_supportE (support_rho chi) sAL) -ke.
have ->: \sum_(x \in A) normC (chi^\rho x) ^+ 2 =
  \sum_(x \in A) (\sum_(i < n) \sum_(j < n) (c i)^* * (c j) / 
    '[zi`_i, zi`_i]_L / '[zi`_j, zi`_j]_L * (zi`_i x * (zi`_j x)^*)).
  apply: eq_bigr => x xA; rewrite (pf77a xA).
  rewrite sqrtCK rmorph_sum mulr_sum.
  apply: eq_bigr => i _; apply: eq_bigr => j _.
  rewrite [(_ / _ * _)^*]rmorphM [(_ / _)^*]rmorphM conjCK.
  rewrite fmorphV // -[in X in (_ / X * _^*)]inner_conj.
  set X := _ ^-1; set Y := _ ^-1; set C1 := _^*; set C2 := c j.
  rewrite (mulrAC C1 C2 X) 2!mulrA; congr (_ * _).
  by rewrite mulrA (mulrAC (C1 * X) _ _) (mulrAC (C1 * X * C2) _ _).
have ke_unit: k * e != 0 by exact: mulf_neq0.
rewrite -[X in _ = X]mul1r -(mulVf ke_unit) -[X in _ = X]mulrA; congr (_ * _).
rewrite -mulr_sumr exchange_big /=; apply: eq_bigr => i _.
rewrite -mulr_sumr exchange_big /=; apply: eq_bigr => j _.
rewrite mulr_sumr.
rewrite (mulrCA (k * e) _ _); congr (_ * _).
rewrite mulr_addr mulrN [e * k]mulrC.
rewrite (mulrCA (k * e) _ (_ ^-1)) mulfV // mulr1.
set X := \sum_(x \in _) _; set Y := _ * _ 1%g.
suff ->: k * e * '[zi`_i, zi`_j]_L = Y + X by rewrite addrAC subrr add0r.
rewrite (inner_prod_supportE zi`_j (support_memc (ziC i)) sKL) -ke.
rewrite mulrA mulfV // mul1r.
rewrite (big_setID 1%g) /= setIg1 big_set1 -AK1 -/X /Y.
congr (_ * _ + _).
rewrite posC_conjK //; apply: (@posC_char1 _ L _); case: (zi_ind j) => r ->.
by apply: is_char_induced; rewrite ?sKL ?is_char_irr.
Qed.



End PF77.


End Prelim1.


(*************************************)

Section Prelim2.


(* 7.4 *)
Variable m : nat.

Variable A : m.-tuple {set gT}.
Variable L : m.-tuple {group gT}.
Variable H : m.-tuple (gT -> {group gT}).

Hypothesis ddI : forall i, Dade_hypothesis G (tnth L i) (tnth H i) (tnth A i).

Local Notation "alpha ^\tau_ i" := (Dade (ddI i) alpha)
  (at level 2, format "alpha ^\tau_ i").

Local Notation "''Atau_' i" := (Dade_support (ddI i))
  (at level 2, format "''Atau_' i").

Local Notation "alpha ^\rho_ i" := (rho_fun (tnth A i) (tnth H i) alpha)
  (at level 2, format "alpha ^\rho_ i").


Hypothesis disjointA : forall i j, i != j -> [disjoint 'Atau_i & 'Atau_j].


Local Notation G0 := (G :\: \bigcup_(i < m) 'Atau_i).


Section PartitionLemma.

Variables (R : Type) (idx : R) (op : Monoid.com_law idx).
Variables T I : finType.


Lemma partition_big_images (F : I -> {set T}) E :
  let P := [set (F i) | i <- I] in
    (forall i j, i != j -> [disjoint (F i) & (F j)]) ->
    \big[op/idx]_(x \in cover P) E x =
    \big[op/idx]_(i \in I) \big[op/idx]_(x \in F i) E x.
Proof.
move => P disjF.
have trivP: trivIset P.
  apply/trivIsetP => X Y.
  case/imsetP => i _ ->; case/imsetP => j _ -> neq.
  by apply: disjF; move: neq; apply: contra => /eqP ->.
rewrite big_trivIset //.
set f := fun i => \big[op/idx]_(x \in F i) E x.
have ->: \big[op/idx]_(i \in I) (f i) = \big[op/idx]_(i \in setT) (f i).
  by apply: eq_bigl => x; rewrite inE in_setT.
rewrite (partition_big_imset (fun i => F i)).
have ->: [set F i | i <- [set: I]] = P.
  rewrite -setP /P => x.
  by apply/imsetP/imsetP => [[] | []] y _ xFy; exists y.
apply: eq_bigr => S SP.
case: (boolP (S == set0)).
  move/eqP ->.
  rewrite !big1 //; last by move => i; rewrite in_set0.
  by move => i /andP [_ /eqP f0]; rewrite /f f0 big_set0.
move: SP; rewrite /P => /imsetP [j _ ->] Fjn0.
have ->: \big[op/idx]_(i \in [set: I] | F i == F j) (f i) = f j.
  apply: big_pred1 => i /=; rewrite in_setT andTb.
  apply/eqP/eqP; last by move ->.
  move/eqP => Feq; apply/eqP; move: Feq.
  apply: contraTT => ij.
  have := disjoint_setI0 (disjF i j ij).
  case: (boolP (F i == F j)); last by [].
  move/eqP ->; rewrite setIid => hyp; move: Fjn0.
  by rewrite hyp; move/eqP.
by rewrite /f; apply: eq_bigl => x.
Qed.


End PartitionLemma.
  


(* 7.5 *)
Lemma pf75 (r : Iirr G) : 
  #|G|%:R ^-1 * ((\sum_(g \in G0) normC ('xi_r g) ^+ 2) - #|G0|%:R)
    + \sum_(i < m) ('[('xi_r)^\rho_i, ('xi_r)^\rho_i]_(tnth L i)
                      - #|tnth A i|%:R / #|tnth L i|%:R) <= 0.
Proof.
set G0 := G :\: _.
rewrite mulr_addr.
set X := _ * (\sum_(g \in G0) _).
rewrite big_split /=.
set Y := \sum_(i < m) _.
pose f (j : Iirr G) i := #|G|%:R ^-1 * \sum_(g \in 'Atau_i) normC ('xi_j g) ^+ 2.
have F1: forall j, 
  1 = #|G|%:R^-1 * (\sum_(g \in G0) normC ('xi_j g) ^+ 2)
    + \sum_(i < m) f j i.
  move => j; rewrite /f.
  have {1}<-: '['xi_j, 'xi_j]_G = 1.
    by apply/eqP; rewrite -irr_inner_prod_charE ?is_char_irr ?irr_xi.
  rewrite mulr_sumr -mulr_addr inner_prodE.
  congr (_ * _).
  have sG0G: G0 \subset G by exact: subsetDl.
  have DGG0: G :\: G0 = \bigcup_(i < m) 'Atau_i.
    rewrite setDDr setDv set0U.
    by apply/setIidPr; apply/bigcupsP => i _; exact: Dade_support_sub.
  rewrite (big_setID G0) /= (setIidPr sG0G) DGG0.
  congr (_ + _); first by apply: eq_bigr => g _; rewrite sqrtCK.
  pose F i := 'Atau_i.
  have ->: \bigcup_(i0 < m) 'Atau_i0 = cover [set F i | i <- 'I_m].
    rewrite /cover -setP => x.
    apply/bigcupP/bigcupP => [[] | []].
      move => i _ xA.
      by exists 'Atau_i => //; apply/imsetP; exists i.
    by move => S; case/imsetP => i _ -> xF; exists i.
  rewrite partition_big_images /=; last by exact: disjointA.
  by apply: eq_bigr => i _; apply: eq_bigr => x _; rewrite sqrtCK.
have: Y <= \sum_(i < m) f r i.
  rewrite -leC_sub -sumr_sub.
  apply: posC_sum => i _; rewrite leC_sub.
  by apply: pf73; exact: memc_irr.
have: \sum_(i < m) f 0 i = \sum_(i < m) #|tnth A i|%:R / #|tnth L i|%:R.
  apply: eq_bigr => i _.
  have := pf73 (ddI i) (memc_irr 0).
  set cond := forallb a, _.
  have auG: forall a u, a \in tnth A i -> u \in tnth H i a -> a \in G /\ u \in G.
    move => a u aA uH; split.
      have: tnth A i \subset tnth L i by  have [/subsetD1P[]] := ddI i.
      move/subsetP => /(_ a aA); apply: (subsetP _).
      by have [_ /subsetIP[]] := ddI i.
    move: uH; apply: (subsetP _).
    have [_ _ _ /(_ a aA) /sdprod_context []] := ddI i.
    by move/andP; rewrite subsetI => [] [] /andP [].
  have: cond.
    apply/forallP => {cond}x; apply/implyP => xA.
    apply/forallP => u; apply/implyP => uH.
    move: (auG x u xA uH) => [xG uG].
    by rewrite -!/fcf -cfuni_xi0 (char_ckerMr (is_char1 G)) ?cker1 //.
  move => C /leCifP; rewrite C {C} /(f 0) => /eqP <-.
  rewrite (norm_chi_rho (ddI i) (memc_irr 0)).
  rewrite mulrC; congr (_ * _).
  rewrite -sum1_card natr_sum; apply: eq_bigr => g gA.
  have <-: normC (1%:R) ^+ 2 = 1%:R by rewrite normC1 exp1rn.
  congr (_ _ ^+ 2).
  rewrite /rho_fun cfunE gA.
  rewrite -{2}(@mulVr _ (#|tnth H i g|%:R)) -?mulrA; first last.
    rewrite unitfE -neq0N_neqC cards_eq0.
    by apply/eqP => h0; apply: (@group_not0 gT (tnth H i g)); rewrite h0.
  congr (_ * _); rewrite -sum1_card natr_sum.
  apply: eq_bigr => u uH; move: (auG g u gA uH) => [gG uG].
  rewrite -cfuni_xi0 cfuniE in_group ?gG ?uG //.
move => h1 h2.
rewrite sumr_opp -h1.
rewrite -addrA [_ + (Y - _)]addrA [_ + Y]addrC -!addrA.
rewrite mulrN -mulN1r -[- \sum_(i < m) _]mulN1r -mulr_addr.
set S := #|G|%:R^-1 * #|G0|%:R + _.
have ->: S = 1.
  rewrite (F1 0); congr (_ + _); congr (_ * _).
  rewrite -sum1_card natr_sum; apply: eq_bigr => g gG0.
  rewrite -cfuni_xi0 (clinear_norm (clinear1 _)) ?expr2 ?mul1r //.
  by apply: subsetP gG0; exact: subsetDl.
rewrite addrA mulr1 -(subrr 1) leC_add2r.
by rewrite (F1 r) -/X leC_add2l h2.
Qed.


End Prelim2.



Section Prelim3.


(* PF 7.8 *)
Variables (A : {set gT}) (L : {group gT}) (H : gT -> {group gT}).
Hypothesis ddA : Dade_hypothesis G L H A.



Local Notation "alpha ^\tau" := (Dade ddA alpha)
  (at level 2, format "alpha ^\tau").

Local Notation "alpha ^\rho" := (rho_fun A H alpha)
  (at level 2, format "alpha ^\rho").


Local Notation Atau := (Dade_support ddA).


Let sAL : A \subset L. Proof. by have [/subsetD1P[]] := ddA. Qed.
Let notA1 : 1%g \notin A. Proof. by have [/subsetD1P[]] := ddA. Qed.
Let nAL : L \subset 'N(A). Proof. by have [_ /subsetIP[]] := ddA. Qed.
Let sLG : L \subset G. Proof. by have [_ /subsetIP[]] := ddA. Qed.

Let defCa : {in A, forall a, H a ><| 'C_L[a] = 'C_G[a]}.
Proof. by case: ddA. Qed.
Let coHL : {in A &, forall a b, coprime #|H a| #|'C_L[b]| }.
Proof. by case: ddA. Qed.
Let nsHC : {in A, forall a, H a <| 'C_G[a]}.
Proof. by move=> a /defCa/sdprod_context[]. Qed.
Let sHG : {in A, forall a, H a \subset G}.
Proof. by move=> a /nsHC/normal_sub/subsetIP[]. Qed.


Variable K : {group gT}.
Hypothesis nKL : K <| L.
Hypothesis AK1 : A = K ^#.

Let sKL : K \subset L. Proof. by move/andP: nKL => []. Qed.

Let k := #|K|%:R : algC.
Let e := #|L : K|%:R : algC.

Let unit_k : k != 0.
Proof. by rewrite -neq0N_neqC -lt0n cardG_gt0. Qed.

Let unit_e : e != 0.
Proof. by rewrite -neq0N_neqC -lt0n indexg_gt0. Qed.

Let ke : k * e = #|L|%:R.
Proof. by apply/eqP; rewrite -natr_mul -eqN_eqC LaGrange. Qed.


Variable zi : seq {cfun gT}.

Hypothesis zi_uniq : uniq zi.
Hypothesis ziP : forall t,
  reflect (exists i, t = 'Ind[L, K] ('xi[K]_i)) (t \in zi).


Let size_zi_gt0 : (0 < size zi)%N.
Proof.
case nn: (size zi); last by [].
have: ('Ind[L, K] 'xi[K]_0 \in zi) by apply/ziP; exists 0.
by rewrite (size0nil nn) in_nil.
Qed.

Let n := size zi.

Let in_zi (i : 'I_n) : zi`_i \in zi. Proof. exact: mem_nth. Qed.

Let i0 := Ordinal size_zi_gt0.
Let zi0 : zi`_0 = zi`_i0. Proof. by []. Qed.

Let zi_ind (i : 'I_n) : exists r, zi`_i = 'Ind[L, K] 'xi[K]_r.
Proof. by move/ziP: (in_zi i). Qed.

Let ziC (i : 'I_n) : zi`_i \in 'CF(L, K).
Proof.
case: (zi_ind i) => r ->; rewrite memcE; apply/andP; split.
  by apply: support_induced; rewrite ?memc_irr.
by apply: memc_induced; [by move/andP: nKL => [] | by rewrite memc_irr].
Qed.

Let zi1_neq_0 (i : 'I_n) : zi`_i (1%g) != 0.
case: (zi_ind i) => r ->.
rewrite -/fcf cinduced1; last by move/andP: nKL => [].
by rewrite mulf_neq0 ?irr1_neq0.
Qed.

Let norm_zi_unit (i : 'I_n) : '[zi`_i]_L != 0.
Proof.
case eq0: ('[_, _]_L == 0); last by [].
move: eq0; rewrite (inner_prod0 (memcW (ziC i))).
move/eqP => eq0; move: (zi1_neq_0 i).
by rewrite eq0 ffunE eqxx.
Qed.


Let zi_distinct (i j : 'I_n) : i != j -> zi`_i != zi`_j.
Proof.
apply: contraR; rewrite negbK => zi_eq.
have := nth_uniq 0 (ltn_ord i) (ltn_ord j) zi_uniq.
rewrite zi_eq => /eqP; rewrite eq_sym => /eqP /eqP h1.
by apply/eqP; exact: ord_inj.
Qed.


Let zi_ortho (i j : 'I_n) : zi`_i != zi`_j -> '[zi`_i, zi`_j]_L = 0.
Proof.
case/ziP: (in_zi i) => r ->.
case/ziP: (in_zi j) => t ->.
have := cconjugates_irr_induced r t nKL.
by case: (_ \in _) => //; move ->; rewrite eqxx.
Qed.


Let free_zi : free zi.
Proof.
apply/(freeP (in_tuple zi)) => s; set S := \sum_(i < n) _ => S0 i.
have: '[zi`_i, S]_L = (s i)^* * '[zi`_i, zi`_i]_L.
  rewrite raddf_sum /=.
  rewrite (bigID (pred1 i)) /= big_pred1_eq big1 ?addr0 ?inner_prodZr //.
  move => j; rewrite eq_sym inner_prodZr.
  by move/zi_distinct/zi_ortho ->; rewrite mulr0.
rewrite S0 inner_prod0r => /eqP; rewrite eq_sym mulf_eq0 conjC_eq0.
case/orP; first by move/eqP.
by move/eqP => eq0; have := norm_zi_unit i; rewrite eq0 eqxx.
Qed.


(* 7.8 *)


Let calS := remove1 zi ('Ind[L, K] '1_K).

Let one_in_zi : 'Ind[L, K] '1_K \in zi.
Proof. by apply/ziP; exists 0; rewrite cfuni_xi0. Qed.

Let size_calS : size (calS) == n.-1.
Proof. by rewrite (remove1_size zi_uniq one_in_zi). Qed.


Hypothesis sizeS : size calS >= 2.

Variable nu : {additive {cfun gT} -> {cfun gT}}.

Hypothesis nu_to : {in 'Z[calS], forall f, nu f \in 'Z[irr G]}.
Hypothesis nu_isom : {in 'Z[calS] &, isometry L G nu}.
Hypothesis nu_tau : {in 'Z[calS, A], forall f, nu f = f^\tau}.

(* chi == zi in 7.8 *)
Variable chi : {cfun gT}.

Hypothesis (chiS : chi \in calS) (chi_irrL : chi \in irr L).
Hypothesis chi1 : chi 1%g = e.

Let beta := ('Ind[L, K] '1_K - chi)^\tau.


Let norm_chi : '[chi, chi]_L = 1.
Proof. by case/irrIP: chi_irrL => r <-; rewrite irr_orthonormal eqxx. Qed.


Let sSzi psi : psi \in calS -> exists i : 'I_n, psi = zi`_i.
Proof.
rewrite mem_filter => /andP [_] /nthP => /(_ 0).
by case => i i_lt_n <-; exists (Ordinal i_lt_n).
Qed.

Let calSP psi : 
  reflect (exists2 i : 'I_n, psi = zi`_i & zi`_i != 'Ind[L, K] '1_K) (psi \in calS).
Proof.
apply: (iffP idP).
  move => psiS; case: (sSzi psiS) => i psi_eq.
  by exists i => //; move: psiS; rewrite psi_eq mem_filter => /andP /= [].
by case => i ->; rewrite mem_filter /= in_zi andbT.
Qed.

Let uniqS : uniq calS.
Proof. exact: filter_uniq. Qed.

Let orthoS psi phi : psi \in calS -> phi \in calS -> psi != phi ->
  '[psi, phi]_L = 0.
Proof. by case/sSzi => i ->; case/sSzi => j ->; exact: zi_ortho. Qed.

Let orthoS_ind1 psi : psi \in calS -> '[psi, 'Ind[L, K] '1_K]_L = 0.
Proof.
case/calSP => i ->.
case/(nthP 0): one_in_zi => j j_lt_n.
pose j1 := Ordinal j_lt_n.
have ->: zi`_j = zi`_j1 by [].
by move <-; exact: zi_ortho.
Qed.


Lemma cinduced_1 : 'Ind[L, K] '1_K = e *: '1_K.
Proof.
apply/ffunP => x; rewrite !ffunE.
have norm c: c \in L -> (x ^ c \in K) = (x \in K).
  move => cL; apply: memJ_norm.
  by move/andP: nKL => [_] /subsetP /(_ c cL).
case xK: (_ \in _); last first.
  rewrite scaler0 big1 ?mulr0 // => c cL.
  by rewrite cfunE (norm c cL) xK.
apply: (mulfI unit_k); rewrite !mulrA -/k (mulfV unit_k) ke mul1r mulr1.
rewrite -sum1_card natr_sum; apply: eq_bigr => c cL.
by rewrite cfunE (norm c cL) xK.
Qed.

Let orthoS_1K psi : psi \in calS -> '[psi, '1_K]_L = 0.
Proof.
move/orthoS_ind1; rewrite cinduced_1 inner_prodZ => /eqP.
rewrite mulf_eq0; case/orP; last by move/eqP.
by rewrite conjC_eq0 => /eqP e0; move: e0 unit_e ->; rewrite eqxx.
Qed.

Let supportS psi : psi \in calS -> support psi \subset K.
Proof. by case/sSzi => i ->; exact: support_memc. Qed.


Lemma dot_support_res (X : {group gT}) (Y : {set gT}) (f g : {cfun gT}):
  support f \subset Y -> '[f, g]_X = '[f, 'Res[Y] g]_X.
Proof.
move => supp_f; rewrite !inner_prodE; congr (_ * _).
apply: eq_bigr => x xX; rewrite !cfunE.
case: (boolP (x \in Y)); first by rewrite mul1r.
by move => xnY; rewrite (off_support supp_f xnY) !mul0r.
Qed.

Let orthoS_1L psi : psi \in calS -> '[psi, '1_L]_L = 0.
Proof.
move => psiS; rewrite (dot_support_res L _ (supportS psiS)).
by rewrite crestrict1 (setIidPl sKL) orthoS_1K.
Qed.


Lemma raddfMZ z f : isZC z -> nu (z *: f) = z *: nu f.
Proof.
rewrite isZCE; case/orP; case/isNatCP => m.
  by move ->; rewrite !scaler_nat raddfMn.
move/eqP; rewrite eqr_oppC => /eqP ->.
by rewrite !scaleNr !scaler_nat raddfMNn.
Qed.


Let exists_psi : exists2 psi, psi \in calS & chi != psi.
Proof.
pose S := remove1 calS chi.
pose psi := S`_0.
have: psi \in S.
  apply: mem_nth; rewrite remove1_size //.
  rewrite -(ltn_add2l 1) !add1n prednK //.
  by apply: (ltn_trans _ sizeS).
by rewrite mem_filter /= eq_sym => /andP [chi_n_psi psiS]; exists psi.
Qed.


Let psi_inZS psi : psi \in calS -> psi \in 'Z[calS].
Proof. by move => psiS; apply: memv_vchar => //; exact: free_filter. Qed.


Let psi_inZSK psi : psi \in calS -> psi \in 'Z[calS, K].
Proof.
move => psiS; apply: memv_vchar => //; first by exact: free_filter.
case: (sSzi psiS) => i ->; exact: (support_memc (ziC i)).
Qed.


Let rho_1 : ('1_G)^\rho = '1_A.
Proof.
apply/ffunP => x; rewrite !ffunE; case xA: (_ \in _); last by [].
rewrite -{2}(@mulVr _ (#|H x|%:R)) -?mulrA; first last.
  by rewrite unitfE -neq0N_neqC -lt0n cardG_gt0.
congr (_ * _); rewrite -sum1_card natr_sum.
apply: eq_bigr => u uH; rewrite cfunE in_group.
  by move/subsetP: sAL => /(_ x xA); move/(subsetP sLG) ->.
by move/subsetP: (sHG xA); exact.
Qed.

Let coefZ g : g \in calS -> isZC (g 1%g / e).
Proof.
move => gS; case: (sSzi gS) => i ->; case: (zi_ind i) => r ->.
rewrite -/fcf cinduced1 // -/e mulrC mulrA mulVf // mul1r. 
by rewrite isZCE isNatC_irr1 orTb.
Qed.

Let diff_ZA g : g \in calS -> g - (g 1%g / e) *: chi \in 'Z[calS, A].
Proof.
move => gS; rewrite vchar_split; apply/andP; split.
  apply: vchar_sub; first by exact: psi_inZS.
  by apply: vchar_scale; [exact: coefZ | exact: psi_inZS].
rewrite AK1; apply/subsetP => x; apply: contraR.
rewrite !inE !cfunE negb_and negbK.
case/orP => [/eqP -> | xnK].
  by rewrite -!/fcf chi1 /GRing.scale /= -mulrA mulVf // mulr1 subrr.
by rewrite -!/fcf !(off_support (support_vchar (psi_inZSK _)) xnK) // scaler0 subrr.
Qed.


Let psi_inC g : g \in calS -> g \in 'CF(L).
Proof.
move => gS; case: (sSzi gS) => i ->.
by have := ziC i; rewrite memcE => /andP [].
Qed.

Let diff_CA g : g \in calS -> g - (g 1%g / e) *: chi \in 'CF(L, A).
Proof.
move => gS; rewrite memcE (support_vchar (diff_ZA gS)) andTb.
by apply: memv_sub; [| apply: memvZl]; exact: psi_inC.
Qed.

Let beta_ZA : 'Ind[L, K] '1_K - chi \in 'Z[irr L, A].
Proof.
rewrite vchar_split; apply/andP; split.
  apply: vchar_sub; apply: vchar_char.
    by apply: is_char_induced sKL; rewrite cfuni_xi0 is_char_irr.
  by case/irrIP: chi_irrL => r <-; exact: is_char_irr.
rewrite AK1; apply/subsetP => x; apply: contraR.
rewrite !inE cinduced_1 !cfunE negb_and negbK.
case/orP => [/eqP -> | xnK].
  by rewrite -!/fcf chi1 in_group /GRing.scale /= mulr1 subrr.
rewrite -!/fcf (off_support (support_vchar (psi_inZSK chiS)) xnK) subr0.
by move: xnK; case: (_ \in _); first by []; rewrite scaler0.
Qed.


Lemma pf78a1 f : f \in calS -> '[nu f, '1_G]_G = 0.
Proof.
move => fS.
have eq_g g : g \in calS -> '[nu (g - (g 1%g / e) *: chi), '1_G]_G = 0.
  move => gS; rewrite nu_tau; last by exact: diff_ZA.
  rewrite rho_Dade_reciprocity ?(cfuni_xi0, memc_irr) ?diff_CA //.
  rewrite -cfuni_xi0 rho_1.
  set mu := _ - _.
  have ->: '[mu, '1_A]_L = '[mu, '1_L]_L.
    rewrite [in X in _ = X](dot_support_res L _ (support_vchar (diff_ZA gS))).
    by rewrite crestrict1 (setIidPl sAL).
  by rewrite inner_prodDl inner_prodNl inner_prodZl !orthoS_1L // mulr0 subr0.
suff {f fS}: '[nu chi, '1_G]_G = 0.
  move => eq0; have := eq_g f fS.
  rewrite raddf_sub (raddfMZ _ (coefZ fS)).
  by rewrite inner_prodDl inner_prodNl inner_prodZl eq0 mulr0 subr0.
have norm_chi1 : '[nu chi, nu chi]_G = 1 by rewrite nu_isom ?(psi_inZS chiS).
have chi_irr := vchar_norm1_irr (nu_to (psi_inZS chiS)) norm_chi1.
have: exists2 e, e * e = 1 & exists r, nu chi = e *: 'xi[G]_r.
  case/orP: chi_irr.
    by case/irrIP => r <-; exists 1; [rewrite mul1r|] => //;
      exists r; rewrite scale1r.
  case/irrIP => r /eqP; rewrite -eqr_oppC => /eqP <-.
  by exists (-1); [rewrite mulrNN mul1r|] => //;
    exists r; rewrite scaleNr scale1r.
case => eps eps_1; case => r chi_eq; rewrite chi_eq inner_prodZl.
case r0: (r == 0); last first.
  by rewrite cfuni_xi0 irr_orthonormal r0 mulr0.
case: exists_psi => f fS chi_n_f.
have prod0 : '[nu f, '1_G]_G = 0.
  have ->: '1_G = eps *: nu chi.
    by rewrite chi_eq scalerA eps_1 (eqP r0) scale1r cfuni_xi0.
  apply/eqP; rewrite inner_prodZ mulf_eq0; apply/orP; right; apply/eqP.
  rewrite nu_isom ?(psi_inZS fS) ?(psi_inZS chiS) //.
  move: chi_n_f; case: (sSzi fS) => i ->; case: (sSzi chiS) => j ->.  
  by rewrite eq_sym; exact: zi_ortho.
have := eq_g f fS.
rewrite raddf_sub (raddfMZ _ (coefZ fS)).
rewrite inner_prodDl inner_prodNl chi_eq !inner_prodZl prod0 mulrA.
move/eqP; rewrite subr_eq eq_sym add0r mulf_eq0.
suff ->: (f 1%g /e * eps == 0) = false.
  by rewrite orFb => /eqP ->; rewrite mulr0.
apply/negP/negP; apply: mulf_neq0; last first.
  case: (boolP (eps == 0)); last by [].
  move/eqP => eq0; move: eps_1; rewrite eq0 mulr0 => /eqP.
  by rewrite eq_sym oner_eq0.
apply: mulf_neq0; last by exact: invr_neq0.
case: (sSzi fS) => i ->; case: (zi_ind i) => t ->.
rewrite -/fcf cinduced1 //; apply: mulf_neq0; first by [].
by rewrite irr1_neq0.
Qed.



(* 7.8(a)-2 *)

Lemma filter_pred1_uniq (T : eqType) (s : seq T) x :
  uniq s -> x \in s -> filter [pred i | i == x] s = [:: x].
Proof.
elim: s => //= h t IHt /andP [] hnt uniq_t.
rewrite in_cons; case/orP => [/eqP ->|].
  rewrite eqxx; congr (_ :: _); apply/eqP; apply: contraNT hnt.
  rewrite -has_filter; case/hasP => y /=.
  by case yh: (_ == _); [ move/eqP: yh -> | ].
move => xt; case hx: (_ == _); last by exact: IHt.
by move/eqP: hx xt hnt -> => ->.
Qed.


Lemma big_pred1_uniq R (idx : R) (op : Monoid.law idx) (T : eqType) (s : seq T) x F : 
  uniq s -> x \in s -> \big[op/idx]_(i <- s | i == x) F i = F x.
Proof.
move => uniq_s xs.
rewrite -big_filter filter_pred1_uniq // big_cons big_nil.
by rewrite Monoid.mulm1.
Qed.


Lemma pf78a2 : exists a, exists Gamma,
  [/\ isZC a, 
    '[Gamma, '1_G]_G = 0, 
    {in calS, forall f, '[Gamma, nu f]_G = 0} &
    beta = Gamma + '1_G - nu chi + 
           a *: (\sum_(f <- calS) (f 1%g / e / '[f]_L) *: nu f)].
Proof.
exists ('[beta, nu chi]_G + 1).
exists (beta - '[beta, '1_G]_G *: '1_G - 
  \sum_(f <- calS) ('[beta, nu f]_G / '[f]_L) *: nu f).
split.
- have ->: (1 : algC) = 1%:R by []. 
  apply: isZC_add; last by exact: isZC_nat.
  apply: isZC_inner_Zirr; last by apply: nu_to; exact: psi_inZS.
  by apply: Dade_vchar; exact: beta_ZA.
- rewrite !inner_prodDl !inner_prodNl inner_prodZl.
  rewrite {3 4}cfuni_xi0 irr_orthonormal eqxx mulr1 subrr.
  apply/eqP; rewrite subr_eq0 eq_sym; apply/eqP.
  rewrite -inner_prodbE linear_sum big1_seq //.
  move => f /andP [_] fS.
  by rewrite linearZ /= inner_prodbE (pf78a1 fS) scaler0.
- move => f fS /=.
  rewrite !inner_prodDl !inner_prodNl inner_prodZl.
  rewrite ['['1_G, _]_G]inner_conj (pf78a1 fS) conjC0 mulr0 subr0.
  apply/eqP; rewrite subr_eq0 eq_sym; apply/eqP.
  rewrite -inner_prodbE linear_sum.
  rewrite (bigID [pred i | i == f]) /= addrC.
  rewrite big1_seq; last first.
    move => g /andP [gnf gS]; move: gnf.
    rewrite linearZ /= inner_prodbE nu_isom ?(psi_inZS _) //.
    case: (sSzi gS) => r ->; case: (sSzi fS) => t -> rnt.
    by rewrite (zi_ortho rnt) ?scaler0.
  rewrite add0r big_pred1_uniq ?(filter_uniq _ zi_uniq) //.
  rewrite linearZ /= inner_prodbE.
  rewrite nu_isom ?(psi_inZS fS) // /GRing.scale /= -mulrA.
  by rewrite mulVf ?mulr1 //; case: (sSzi fS) => r ->.
set SG := \sum_(_ <- _) _.
set S := (_ + _) *: _.
have ->: '[beta, '1_G]_G = 1.
  rewrite rho_Dade_reciprocity ?(cfuni_xi0, memc_irr) //; last first.
    by rewrite -cfuni_xi0; exact: memc_vchar.
  rewrite -!cfuni_xi0 rho_1.
  set mu := _ - _.
  have ->: '[mu, '1_A]_L = '[mu, '1_L]_L.
    rewrite [in X in _ = X](dot_support_res L _ (support_vchar beta_ZA)).
    by rewrite crestrict1 (setIidPl sAL).
  rewrite inner_prodDl inner_prodNl (orthoS_1L chiS) subr0.
  rewrite -(frobenius_reciprocity sKL) ?(cfuni_xi0, memc_irr) //.
  rewrite -['xi[L]_0]cfuni_xi0 crestrict1 (setIidPl sKL) cfuni_xi0.
  by rewrite irr_orthonormal eqxx.
rewrite scale1r [_ - _ - _]addrAC.
rewrite -[_ - '1_G + _]addrA [- _ + _]addrC subrr addr0.
rewrite -!addrA -{1}[beta]addr0; congr (_ + _).
rewrite addrC; apply/eqP; rewrite eq_sym subr_eq0 eq_sym; apply/eqP.
rewrite /S /SG (bigID (pred1 chi)) /=.
rewrite [in X in _ = X](bigID (pred1 chi)) /=.
rewrite scaler_addr addrA; congr (_ + _).
  rewrite !big_pred1_uniq ?(filter_uniq _ zi_uniq) //.
  rewrite -/fcf chi1 (mulfV unit_e).
  case/irrIP: chi_irrL => r <-. 
  rewrite irr_orthonormal eqxx invr1 mul1r scale1r scaler_addl.
  by rewrite mulr1 scale1r -addrCA [- _ + _]addrC subrr addr0.
rewrite scaler_sumr big_seq_cond [in X in _ = X]big_seq_cond.
apply: eq_bigr => f /andP [fS f_n_chi].
rewrite scalerA !mulrA; congr ((_ / _) *: _).
have: '[beta, nu (f - f 1%g / e *: chi)]_G = f 1%g / e.
  set c := _ / _.
  rewrite nu_tau ?diff_ZA //.
  rewrite Dade_isometry ?diff_CA //; last by exact: memc_vchar.
  rewrite inner_prodDr !inner_prodDl !inner_prodNl !inner_prodNr !inner_prodZ.
  rewrite inner_conj (orthoS_ind1 fS) inner_conj (orthoS fS chiS f_n_chi).
  rewrite inner_conj (orthoS_ind1 chiS) conjC0 mulr0 oppr0 addr0 !add0r opprK.
  by rewrite norm_chi mulr1; apply: isZC_conj; exact: coefZ.
rewrite raddf_sub raddfMZ ?coefZ // inner_prodDr inner_prodNr.
move/eqP; rewrite subr_eq => /eqP ->.
rewrite -mulrA mulr_addl mul1r addrC inner_prodZ mulrC.
by congr (_ * _ + _); apply: isZC_conj; exact: coefZ.
Qed.


(*********************************)
(* 7.8(b) *)


Let inv_ind (f : {cfun gT}) : Iirr K :=
  odflt 0 [pick r | 'Ind[L, K] 'xi[K]_r == f].

Let cconj_sum (F : ({cfun gT} * {cfun gT}) -> algC) :
\sum_(i < Nirr K) F ('Ind[L, K] 'xi_i, 'xi_i) = 
\sum_(i < n) \sum_(f <- cconjugates L 'xi_(inv_ind zi`_i)) F (zi`_i, f).
Proof.
pose alpha (f : {cfun gT}) := ('Ind[L, K] f, f).
transitivity (\sum_(p <- map alpha (irr K)) F p).
  rewrite big_map [in X in _ = X](big_nth 0) big_mkord size_tuple.
  by apply: eq_bigr => i _; rewrite /alpha (tnth_nth 0).
transitivity (\sum_(p <- map alpha (irr K)) \sum_(i < n | p.1 == zi`_i) F p).
  rewrite big_seq_cond [in X in _ = X]big_seq_cond.
  apply: eq_bigr => f /andP [f_map _].
  set rhs := \sum_(i < n | _) _.
  have {rhs}->: rhs = \sum_(x <- zi | x == f.1) F f.
    rewrite (big_nth 0) big_mkord.
    by apply: eq_bigl => x; rewrite eq_sym.
  rewrite big_pred1_uniq //.
  apply/ziP; case/mapP: f_map => a; case/irrIP => r <- ->.
  by exists r.
rewrite (big_nth (0, 0)) big_mkord size_map size_tuple.
pose ss := map alpha (irr K).
rewrite -/ss (exchange_big_dep predT) //=.
apply: eq_bigr => i _.
rewrite -cconjugates_sum ?nKL //=.
have nth_ss (j : Iirr K) : nth (0, 0) ss j = ('Ind[L, K] 'xi_j, 'xi_j).
  by rewrite (nth_map 'xi[K]_0) ?size_tuple ?ltn_ord // -tnth_nth.
apply: congr_big => //; last first.
  by move => j; rewrite nth_ss => /= /eqP ->.
move => j; rewrite /= nth_ss /=.
have inv (r : Iirr K) : 'Ind[L, K] 'xi_(inv_ind ('Ind[L, K] 'xi_r)) = 'Ind[L, K] 'xi_r.
  rewrite /inv_ind; case: pickP => [x /eqP | ] //=.
  by move => /(_ r); rewrite eqxx.
apply/eqP/idP; last first.
  move => hyp.
  have := cconjugates_irr_induced (inv_ind zi`_i) j nKL.
  by rewrite hyp; case: (zi_ind i) => r ->; rewrite inv => ->.
case: (zi_ind i) => r ->.
case hyp: (_ \in _); first by []; move => jr.
have := cconjugates_irr_induced (inv_ind ('Ind[L, K] 'xi_r)) j nKL.
rewrite hyp inv jr => /eqP. 
rewrite inner_prod0 ?cinduced_eq0 ?memc_induced ?is_char_irr ?memc_irr //.
move/eqP/ffunP => /(_ 1%g); rewrite ffunE => contr.
by have := irr1_neq0 r; rewrite /fcf contr eqxx.
Qed.

(* The sequence for b *)

Let zb_tail := remove1 calS chi.

Let size_zb_tail : size zb_tail = n.-2.
Proof. by rewrite remove1_size // (eqP size_calS). Qed.

Let n1_gt0 : (0 < n.-1)%N.
Proof.
rewrite lt0n; have := sizeS; rewrite (eqP size_calS).
by case: (boolP (n.-1 == 0)%N); [move/eqP ->; rewrite ltn0 | ].
Qed.

Let n2_gt0 : (0 < n.-2)%N.
Proof.
have := sizeS; rewrite (eqP size_calS) -{1}(prednK n1_gt0).
by rewrite -addn1 -[n.-2.+1]addn1 leq_add2r.
Qed.

Let z0 := zb_tail`_0.

Let z0_in_tail : z0 \in zb_tail. 
Proof. by rewrite mem_nth // size_zb_tail. Qed.

Let chi_n_z0 : chi != z0.
Proof. by move: z0_in_tail; rewrite mem_filter eq_sym => /andP []. Qed.

Let z0_inS : z0 \in calS.
Proof. by move: z0_in_tail; rewrite mem_filter => /andP []. Qed.

Let z0_neq_ind1 : z0 != 'Ind[L, K] '1_K.
Proof. by case/calSP: z0_inS => i ->. Qed.

(* The sequence for (b) *)
Let zb := z0 :: 'Ind[L, K] '1_K :: chi :: remove1 zb_tail z0.


Let size_zb : size zb = n.
Proof.
rewrite /= remove1_size ?z0_in_tail ?filter_uniq // size_zb_tail.
by rewrite (prednK n2_gt0) (prednK n1_gt0) (prednK size_zi_gt0).
Qed.

Let zb0 : zb`_0 = z0. Proof. by []. Qed.
Let zb1 : zb`_1 = 'Ind[L, K] '1_K. Proof. by []. Qed.
Let zb2 : zb`_2 = chi. Proof. by []. Qed.

Let zbi (i : 'I_n) : (3 <= nat_of_ord i)%N -> 
  [/\ zb`_i \in calS, zb`_i != z0 & zb`_i != chi].
Proof.
move => i_ge3; apply/and3P.
have i_eq: nat_of_ord i = (i - 3).+3.
  by rewrite -{1}(subnK i_ge3) -{2}[3]addn1 addnA addn1 addn2.
have n_eq: n = (n - 3).+3.
  rewrite -{1}[3]addn1 -subn_sub subn2 subn1.
  by rewrite (prednK n2_gt0) (prednK n1_gt0) (prednK size_zi_gt0).
rewrite i_eq /=.
set el := (_)`_ _.
have: el \in remove1 zb_tail z0.
  apply: mem_nth; rewrite remove1_size ?filter_uniq // size_zb_tail.
  rewrite -(ltn_add2r 3) -subn1 -subn2 subn_sub addn1.
  by rewrite -{2 4}[3]addn1 !addnA !addn2 !addn1 -i_eq -n_eq ltn_ord.
rewrite mem_filter /= => /andP [] ->.
by rewrite mem_filter /= => /andP [] -> ->.
Qed.

Let zb_calS (i : 'I_n) : (nat_of_ord i != 1)%N -> zb`_i \in calS.
Proof.
move => i_neq1.
case: (ltngtP i 2); [| by move/zbi => []| by move ->; rewrite zb2].
rewrite -addn1 -[2]addn1 leq_add2r leq_eqVlt (negPf i_neq1) orFb.
by rewrite -addn1 -{2}[1%N]addn1 leq_add2r leqn0 => /eqP ->; rewrite zb0.
Qed.

Let uniq_zb : uniq zb.
Proof.
rewrite /= !filter_uniq // !inE !mem_filter !negb_or !negb_and !negbK !eqxx.
rewrite /= !orbT z0_neq_ind1 eq_sym chi_n_z0 eq_sym.
by case/calSP: chiS => _ <- ->.
Qed.

Let zbP t : reflect (exists i : Iirr K, t = 'Ind[L, K] 'xi_i) (t \in zb).
Proof.
apply: (iffP idP).
  case/(nthP 0) => i; rewrite size_zb => i_lt_n <-.
  case: (boolP (i == 1)%N).
    by move/eqP ->; rewrite zb1; exists 0; rewrite cfuni_xi0.
  move => i_n_1; pose i1 := Ordinal i_lt_n.
  have: (nat_of_ord i1 != 1)%N by apply: contra i_n_1.
  move/zb_calS; case/calSP => j -> _.
  by case: (zi_ind j) => r ->; exists r.
case => r ->.
rewrite !inE !mem_filter /=.
do 3 case: (_ == _); move => //=.
by apply/ziP; exists r.
Qed.

Let zbi_in_zb (i : 'I_n) : zb`_i \in zb.
Proof. by apply: mem_nth; rewrite size_zb ltn_ord. Qed.


(* Variables & Assumptions *)
Variable a : algC.
Variable Gamma : {cfun gT}.

Hypothesis ortho_Gamma1 : '[Gamma, '1_G]_G = 0.
Hypothesis ortho_GammaS : {in calS, forall f, '[Gamma, nu f]_G = 0}.
Hypothesis beta_sum : beta = Gamma + '1_G - nu chi + 
  a *: (\sum_(f <- calS) (f 1%g / e / '[f]_L) *: nu f).

Hypothesis ineq : e <= (k - 1) / 2%:R.


Let a_eq : '[beta, nu chi]_G = a - 1.
Proof.
rewrite beta_sum !inner_prodDl inner_prodNl inner_prodZl.
rewrite (ortho_GammaS chiS) inner_conj (pf78a1 chiS).
rewrite conjC0 !add0r nu_isom ?(psi_inZS chiS) // addrC.
rewrite norm_chi; congr (_ - _).
rewrite -inner_prodbE linear_sum.
rewrite (bigID [pred i | i == chi]) /= big_pred1_uniq // big1_seq.
  rewrite -!/fcf inner_prodbE inner_prodZl chi1 (mulfV unit_e) norm_chi invr1.
  by rewrite nu_isom ?(psi_inZS chiS) // norm_chi addr0 !mulr1.
move => f /andP [f_n_chi fS]; rewrite inner_prodbE inner_prodZl.
by rewrite nu_isom ?(psi_inZS _) // (orthoS fS chiS f_n_chi) mulr0.
Qed.


Let isZC_a : isZC a.
Proof.
move/eqP: a_eq; rewrite eq_sym subr_eq => /eqP ->.
have ->: (1 : algC) = 1%:R by []. 
apply: isZC_add; last by exact: isZC_nat.
apply: isZC_inner_Zirr; last by apply: nu_to; exact: psi_inZS.
by apply: Dade_vchar; exact: beta_ZA.
Qed.


Let c i := '[(zb`_i - zb`_i 1%g / z0 1%g *: z0)^\tau, nu chi]_G.

Let z01_neq0 : z0 1%g != 0.
Proof. by case/sSzi: z0_inS => i ->. Qed.

Let isZC_psi1 psi : psi \in calS -> isZC (psi 1%g).
Proof.
case/sSzi => r ->; case: (zi_ind r) => j ->; rewrite -/fcf (cinduced1 _ sKL).
apply: isZC_mul; first by exact: isZC_nat.
by case/isNatCP: (isNatC_irr1 j) => t ->; exact: isZC_nat.
Qed.


Let c0 : c 0 = 0.
Proof. by rewrite /c zb0 (mulfV z01_neq0) scale1r subrr Dade0 inner_prod0l. Qed.


Let diff1_ZS psi : psi \in calS -> z0 1%g *: psi - psi 1%g *: z0 \in 'Z[calS].
Proof.
move => psiS; apply: vchar_sub; apply: vchar_scale;
  [exact: isZC_psi1 | exact: psi_inZS | exact: isZC_psi1 | exact: psi_inZS].
Qed.


Let diff1_ZSA psi : psi \in calS -> z0 1%g *: psi - psi 1%g *: z0 \in 'Z[calS, A].
Proof.
move => psiS; rewrite vchar_split (diff1_ZS psiS) andTb AK1.
apply/subsetP => x; apply: contraR.
rewrite !inE !cfunE negb_and negbK.
case/orP => [/eqP -> | xnK]; first by rewrite /GRing.scale /= mulrC subrr.
by rewrite -!/fcf !(off_support (support_vchar (psi_inZSK _)) xnK) // !scaler0 subr0.
Qed.


Let diff2_ZS psi : psi \in calS -> 
  z0 1%g *: psi - ('Ind[L, K] '1_K) 1%g *: z0 \in 'Z[calS].
Proof.
move => psiS; apply: vchar_sub; apply: vchar_scale;
  [exact: isZC_psi1 | exact: psi_inZS | | exact: psi_inZS].
rewrite (cinduced1 _ sKL); apply: isZC_mul; first by exact: isZC_nat.
by rewrite cfunE in_group; exact: isZC_nat.
Qed.


Let diff2_ZSA : z0 1%g *: chi - ('Ind[L, K] '1_K) 1%g *: z0 \in 'Z[calS, A].
Proof.
rewrite vchar_split (diff2_ZS chiS) andTb AK1.
apply/subsetP => x; apply: contraR.
rewrite !inE (cinduced1 _ sKL) -/e !cfunE negb_and negbK in_group mulr1 -!/fcf.
case/orP => [/eqP -> | xnK]; first by rewrite chi1 /GRing.scale /= mulrC subrr.
by rewrite !(off_support (support_vchar (psi_inZSK _)) xnK) // !scaler0 subr0.
Qed.



Let c1 : c 1 = a.
Proof.
transitivity ('[beta + (chi - zb`_1 1%g / z0 1%g *: z0)^\tau, nu chi]_G).
  congr ('[_, _]_G); rewrite /beta zb1 -linearD.
  by rewrite addrA -[_ - _ + _]addrA [- _ + _]addrC subrr addr0.
set rhs := '[_, _]_ _.
suff: z0 1%g * rhs = z0 1%g * a by move/(mulfI z01_neq0).
rewrite /rhs inner_prodDl mulr_addr a_eq.
rewrite -inner_prodZl -linearZ scaler_subr scalerA -mulrCA mulfV // !mulr1.
rewrite /= -nu_tau ?nu_isom ?diff2_ZS ?diff2_ZSA ?psi_inZS //.
rewrite inner_prodDl inner_prodNl !inner_prodZl norm_chi.
rewrite orthoS //; last by rewrite eq_sym.
by rewrite mulr0 mulr1 subr0 mulr_subr addrAC mulr1 -addrA subrr addr0.
Qed.


Let c2 : c 2 = 1.
Proof.
suff: z0 1%g * c 2 = z0 1%g * 1 by move/(mulfI z01_neq0).
rewrite /c -inner_prodZl -linearZ scaler_subr scalerA -mulrCA mulfV // !mulr1.
rewrite /= -nu_tau ?nu_isom ?diff1_ZS ?diff1_ZSA ?psi_inZS //.
rewrite inner_prodDl inner_prodNl !inner_prodZl norm_chi.
by rewrite orthoS ?mulr0 ?mulr1 ?subr0 // eq_sym.
Qed.


Let ci0 i : (3 <= i)%N -> c i = 0.
Proof.
move => i_ge3; case: (boolP (i < n)%N); last first.
  rewrite -leqNgt -size_zb => zb_le_i.
  by rewrite /c nth_default // ffunE mul0r scale0r subrr Dade0 inner_prod0l.
move => i_lt_n; pose j := Ordinal i_lt_n; have: (3 <= j)%N by [].
move/zbi => [] ziS zi_n_z0 zi_n_chi.
suff: z0 1%g * c i = z0 1%g * 0 by move/(mulfI z01_neq0).
rewrite /c -inner_prodZl -linearZ scaler_subr scalerA -mulrCA mulfV // !mulr1.
rewrite /= -nu_tau ?nu_isom ?diff1_ZS ?diff1_ZSA ?psi_inZS //.
rewrite inner_prodDl inner_prodNl !inner_prodZl.
by rewrite !orthoS ?(mulr0, subr0) // eq_sym.
Qed.


Let u := e^-1 * (1 - k^-1).
Let v := k^-1.
Let w := 1 - e / k.




Let norm_ind1K : '['Ind[L, K] '1_K]_L = e.
Proof.
rewrite cinduced_1; rewrite (norm_supportE _ sKL); last first.
  by apply: (@support_memc _ K); apply: memvZl; rewrite cfuni_xi0 memc_irr.
apply: (mulfI (neq0GC L)); rewrite mulrA (mulfV (neq0GC L)) mul1r -ke.
rewrite /k -sum1_card natr_sum -!mulr_suml.
apply: eq_bigr => y yK; rewrite !cfunE yK /GRing.scale /= mulr1.
by rewrite /e normC_nat expr2 mul1r.
Qed.



Let norm_nu_chi_rho : 
  '[(nu chi)^\rho]_L = u * a ^+ 2 - 2%:R * v * a + w.
Proof.
have n_gt1 : (1 < size zb)%N.
  by have := n1_gt0; rewrite size_zb -(ltn_add2r 1) !addn1 (prednK size_zi_gt0).
have n_gt2 : (2 < size zb)%N.
  have := n2_gt0; rewrite size_zb -(ltn_add2r 2) !addn2.
  by rewrite (prednK n1_gt0) (prednK size_zi_gt0).
have nu_chiZ: nu chi \in 'Z[irr G] by apply: nu_to; exact: psi_inZS.
have := vchar_norm1_irr nu_chiZ; rewrite nu_isom ?(psi_inZS chiS) // norm_chi.
have eq: (1 : algC) = 1%:R by [] => /(_ eq) {eq} nu_chi_irr.
have {nu_chi_irr} nu_chiS : nu chi \in 'CF(G).
  case/orP: nu_chi_irr; case/irrIP => r; first by move <-; rewrite memc_irr.
  by move => hyp; rewrite -memvN -hyp memc_irr.
rewrite (pf77b ddA nKL AK1 uniq_zb zbP nu_chiS) -/e -/k.
pose i1 := Ordinal n_gt1.
pose i2 := Ordinal n_gt2.
pose pred12 := predU (pred1 i1) (pred1 i2).
have i1v: nat_of_ord i1 = 1%N by [].
have i2v: nat_of_ord i2 = 2%N by [].
have neg_pred12 : predC pred12 =1 [pred i | (nat_of_ord i == 0)%N || (3 <= nat_of_ord i)%N].
  move => x /=; rewrite negb_or; apply/andP/orP => [[] xn1 xn2 | []].
  - have /negPf: (nat_of_ord x != 1)%N.
      by apply: contra xn1; rewrite -i1v => /eqP /ord_inj ->.
    have /negPf: (nat_of_ord x != 2)%N.
      by apply: contra xn2; rewrite -i2v => /eqP /ord_inj ->.
    case: (ltngtP x 2); [ | by move => _ _ _; right | by []].
    case: (ltngtP x 1) => //; first by rewrite ltnS leqn0 => -> _ _ _; left.
    by rewrite [(x < 2)%N]ltnS ltnNge => /negPf ->.
  - by move=> x0; split; apply: contraL x0=> /eqP ->; rewrite ?(i1v, i2v).
  by move => x2; split; apply: contraL x2 => /eqP ->; rewrite ?(i1v, i2v).
rewrite (bigID pred12) /= addrC big1 ?add0r; last first.
  move => i; have := neg_pred12 i => /= -> i_cases.
  apply: big1 => j _; case/orP: i_cases.
    by move/eqP ->; have := c0; rewrite /c => ->; rewrite conjC0 !mul0r.
  by move/ci0; rewrite /c => ->; rewrite conjC0 !mul0r.
have sumU F : \sum_(i < size zb | (i == i1) || (i == i2)) (F i : algC) = F i1 + F i2.
  rewrite (bigID (pred1 i1)) /=; congr (_ + _).
    by apply: big_pred1 => j /=; case: (_ == _) => //=; rewrite andbF.
  apply: big_pred1 => j /=; case ji1: (_ == _) => /=; last by rewrite andbT.
  by move/eqP: ji1 ->.
rewrite sumU.
rewrite (bigID pred12) [in X in _ + X](bigID pred12) !sumU !big1 /=; first last.
- move => j; have := neg_pred12 j => /= ->; case/orP.
    by move/eqP ->; have := c0; rewrite /c => ->; rewrite mulr0 !mul0r.
  by move/ci0; rewrite /c => ->; rewrite mulr0 !mul0r.
- move => j; have := neg_pred12 j => /= ->; case/orP.
    by move/eqP ->; have := c0; rewrite /c => ->; rewrite mulr0 !mul0r.
  by move/ci0; rewrite /c => ->; rewrite mulr0 !mul0r.
move: c1 c2; rewrite /c => -> ->.
rewrite -!/fcf norm_chi chi1 (cinduced1 _ sKL) norm_ind1K -/e cfunE in_group !mulr1.
rewrite inner_conj (orthoS_ind1 chiS) conjC0 conjC1.
rewrite invr1 !addr0 !sub0r !mul1r !mulr1 (isZC_conj isZC_a).
rewrite addrA -[_ + _ + a / e * -(e * e / (e * k))]addrA.
congr (_ + _ + _); last by rewrite invf_mul mulrA mulfK.
  rewrite -[e * e / _]mulrA -{3}[e]mulr1 -mulr_subr mulrA divfK //.
  by rewrite invf_mul mulrA mulfV // mul1r -mulrA mulrC expr2.
rewrite invf_mul mulrN !mulrA mulfK // divfK // -mulr2n.
by rewrite -mulrA mulNrn mulr_natl mulrC.
Qed.


Let ineq1 : 0 <= u * a ^+ 2 - 2%:R * v * a.
Proof.
have k_gt0: 0 < k by rewrite /k -(ltn_ltC 0) cardG_gt0.
have e_gt0: 0 < e by rewrite /e -(ltn_ltC 0) indexg_gt0.
have u_ge0: 0 <= u.
  rewrite -(posC_mulr _ e_gt0) mulrA mulfV // mul1r.
  rewrite -(posC_mulr _ k_gt0) mulr_subr mulfV // mulr1 leC_sub.
  by rewrite -(leq_leC 1) cardG_gt0.
have vu: 2%:R * v <= u.
  rewrite -leC_sub /u /v.
  rewrite -(posC_mulr _ k_gt0) mulr_subr mulrCA mulr_subr mulrCA mulfV // !mulr1.
  rewrite -(posC_mulr _ e_gt0) mulr_subr mulrA mulfV // mul1r mulrC.
  move: ineq; have two_gt0: 0 < 2%:R by rewrite -(ltn_ltC 0).
  rewrite -leC_sub -(posC_mulr _ two_gt0) mulr_subr mulrCA mulfV ?mulr1 //.
  by rewrite -neq0N_neqC.
move: isZC_a; rewrite expr2 mulrA -mulr_subl isZCE.
case a0: (a == 0); first by move/eqP: a0 ->; rewrite mulr0 leC_refl.
case/orP; case/isNatCP => r.
  move => ar; move: ar a0 -> => a0; apply: posC_mul; last by exact: posC_nat.
  rewrite leC_sub; apply: (leC_trans vu); rewrite -leC_sub.
  rewrite -{2}[u]mulr1 -mulr_subr; apply: posC_mul; first by [].
  rewrite leC_sub -(leq_leC 1).
  by case: (ltnP 0 r) => //; rewrite leqn0 eqN_eqC a0.
move => ar; move: a0; rewrite -mulrNN -eqr_opp oppr0 ar oppr_sub => a0.
apply: posC_mul; last by exact: posC_nat.
apply: posC_add.
  apply: posC_mul; first by rewrite -(leq_leC 0).
  by rewrite posC_inv posC_nat.
by rewrite -mulrN ar posC_mul // posC_nat.
Qed.

Lemma pf78b1 : w <= '[(nu chi)^\rho]_L. 
Proof. by rewrite norm_nu_chi_rho -{1}[w]add0r leC_add2r. Qed.



Let norm_sum_ortho (X : {group gT}) (f g : {cfun gT}) :
  '[f, g]_X = 0 -> '[f + g, f + g]_X = '[f, f]_X + '[g, g]_X.
Proof.
rewrite inner_prodDl !inner_prodDr.
by rewrite ['[g, f]_X]inner_conj => ->; rewrite conjC0 addr0 add0r.
Qed.


Let norm_beta : '[beta]_G = '[Gamma]_G + 1 + (a - 1) ^+ 2 +
  a ^+ 2 * \sum_(f <- remove1 calS chi) (f 1%g / e) ^+ 2 / '[f]_L.
Proof.
have := beta_sum.
rewrite (bigID [pred f | f == chi]) /= big_pred1_uniq // -big_filter.
rewrite -!/fcf chi1 mulfV // norm_chi invr1 mulr1 scale1r scaler_addr addrA.
set v1 := _ + '1_G + _ + _.
set v2 := a *: _.
move ->; rewrite norm_sum_ortho; last first.
  rewrite inner_prodZ raddf_sum big1_seq ?mulr0 //.
  move => f; rewrite mem_filter andTb => /andP [] f_n_chi fS.
  rewrite /= inner_prodZ !inner_prodDl inner_prodZl inner_prodNl.
  rewrite ortho_GammaS // nu_isom ?(psi_inZS _) //.
  apply/eqP; rewrite mulf_eq0; apply/orP; right.
  by rewrite inner_conj pf78a1 // inner_conj orthoS // conjC0 mulr0 !addr0 subr0.
congr (_ + _).
  rewrite /v1 -!addrA 2?norm_sum_ortho ?inner_prodDl ?inner_prodDr; first last.
  - by rewrite inner_prodNr inner_prodZ ortho_Gamma1 ortho_GammaS // mulr0 addr0 subr0.
  - by rewrite inner_prodNr inner_prodZ inner_conj pf78a1 // conjC0 mulr0 addr0 oppr0.
  congr (_ + _); rewrite !inner_prodNl !inner_prodNr !inner_prodZl !inner_prodZ.
  rewrite cfuni_xi0 irr_orthonormal eqxx nu_isom ?(psi_inZS _) // norm_chi.
  rewrite (isZC_conj isZC_a) mulr1 opprK; congr (_ + _).
  rewrite expr2 mulr_subr mulr_subl mulr1 mul1r.
  by rewrite oppr_sub !addrA addrC -!addrA; congr (_ + _); rewrite addrCA.
rewrite inner_prodZl inner_prodZ (isZC_conj isZC_a) expr2 mulrA; congr (_ * _).
have norm_sum (s : seq {cfun gT}) (F : {cfun gT} -> {cfun gT}) :
  uniq s -> {in s &, forall f g, f != g -> '[F f, F g]_G = 0} ->
  '[\sum_(f <- s) F f, \sum_(f <- s) F f]_G = \sum_(f <- s) '[F f, F f]_G.
  move => uniq_s ortho_s.
  rewrite raddf_sum big_seq_cond [in X in _ = X]big_seq_cond /=.
  apply: eq_bigr => f /andP [] fS _.
  rewrite (bigID [pred g | g == f]) /= big_pred1_uniq //.
  rewrite inner_prodDl -{2}['[_, _]_G]addr0; congr (_ + _).
  rewrite -inner_prodbE linear_sum big1_seq //=.
  by move => g /andP [] gS g_n_f; rewrite inner_prodbE ortho_s.
rewrite norm_sum ?(filter_uniq) //; last first.
  move => f g; rewrite mem_filter => /andP [_] fS.
  rewrite mem_filter => /andP [_] gS f_n_g.
  rewrite inner_prodZl inner_prodZ nu_isom ?(psi_inZS _) //.
  by rewrite ['[f, g]_L]orthoS // !mulr0.
rewrite big_seq_cond [in X in _ = X]big_seq_cond.
apply: eq_bigr => f /andP []; rewrite mem_filter => /andP [_] fS _.
rewrite inner_prodZ inner_prodZl nu_isom ?(psi_inZS _) // divfK; last first.
  by case/sSzi: fS => r ->.
rewrite !rmorphM !fmorphV conjC_nat -/e.
rewrite !(isZC_conj _); first by rewrite mulrC expr2 !mulrA.
  by rewrite -nu_isom ?isZC_inner_Zirr ?nu_to ?(psi_inZS fS) //.
exact: isZC_psi1.
Qed.



Let sum_zi : \sum_(f <- zi) (f 1%g / e) ^+ 2 / '[f]_L = 
  e ^- 1 * \sum_(i < Nirr K) ('xi_i 1%g) ^+ 2.
Proof.
apply/(mulfI unit_e); rewrite mulrA mulfV // mul1r -mulr_sumr.
rewrite (big_nth 0) big_mkord -/n.
set S1 := \sum_(i < n) _.
set S2 := \sum_(i < Nirr K) _.
have := cconj_sum (fun (p : {cfun gT} * {cfun gT}) => (p.2 1%g) ^+ 2).
set S3 := \sum_(i < Nirr K) _.
have ->: S3 = S2 by apply: eq_bigr => i _ /=.
move ->; apply: eq_bigr => i _.
set t := inv_ind _.
have zi_t: zi`_i = 'Ind[L, K] 'xi_t.
  rewrite /t /inv_ind; case: pickP => /=; first by move => r /eqP ->.
  by case: (zi_ind i) => j -> /(_ j); rewrite eqxx.
rewrite expr2 mulrCA !mulrA divfK //.
rewrite -[_ / e]mulrC -!mulrA.
apply/(mulfI unit_e); rewrite !mulrA mulfV // mul1r.
have := induced_sum_rcosets1 t nKL => /=; rewrite -zi_t.
move/ffunP => /(_ 1%g); rewrite sum_ffunE !ffunE in_group -/e.
rewrite mul1r /GRing.scale /= mulrAC => ->.
congr (_ * _); apply: eq_bigr => f => f_conj.
by rewrite ffunE /GRing.scale /= expr2.
Qed.



Let norm_gamma : 
  '[Gamma]_G = e - (a - 1) ^+ 2 - a ^+ 2 * (k * u - 1).
Proof.
have := norm_beta.
have ->: '[beta, beta]_G = e + 1.
  rewrite Dade_isometry ?(memc_vchar beta_ZA) //.
  rewrite inner_prodDl !inner_prodDr !inner_prodNl !inner_prodNr.
  rewrite norm_ind1K inner_conj orthoS_ind1 // norm_chi opprK conjC0.
  by rewrite oppr0 add0r addr0.
rewrite -!addrA => /eqP; rewrite -subr_eq => /eqP <-.
rewrite !oppr_add !addrA addrK.
congr (_ - _ - _ * _).
have := sum_zi.
rewrite irr_sum_square -/k.
rewrite (bigID (pred1 ('Ind[L, K] '1_K))) /= big_pred1_uniq //.
rewrite norm_ind1K (cinduced1 _ sKL) -/e cfunE in_group mulr1 mulfV //.
rewrite -big_filter (bigID (pred1 chi)) /= big_pred1_uniq //.
rewrite chi1 norm_chi mulfV // invr1 expr2 !mul1r.
rewrite addrA addrC => /eqP; rewrite eq_sym -subr_eq => /eqP.
rewrite -big_filter => <-.
by rewrite oppr_add addrA /u mulrCA mulr_subr mulfV // mulr_subr !mulr1.
Qed.




Lemma pf78b2 : '[Gamma]_G <= e - 1.
Proof.
rewrite norm_gamma expr2 !mulr_subr !mulr_subl !mulr1 mul1r -expr2.
rewrite !oppr_add !opprK.
rewrite addrAC !addrA addrK.
rewrite addrC !addrA [-1 + e]addrC.
rewrite -[(e - 1) - _ + _]addrA -addrA -{2}[e - 1]addr0.
rewrite leC_add2l -leC_sub sub0r !oppr_add opprK mulrC expr2.
have := ineq1.
have k_gt0: 0 < k by rewrite /k -(ltn_ltC 0) cardG_gt0.
rewrite -mulrA mulr_natl mulr2n -(posC_mulr _ k_gt0).
by rewrite mulr_subr mulr_addr !mulrA mulfV // mul1r oppr_add addrA.
Qed.








(***************************************)
(* 7.8c *)

Let zc := chi :: 'Ind[L, K] '1_K :: remove1 calS chi.

Let zc_alt : zc = chi :: remove1 ('Ind[L, K] '1_K :: calS) chi.
Proof.
congr (_ :: _).
case/calSP: chiS => _ <- => chi_n_1; rewrite eq_sym in chi_n_1.
by rewrite /= chi_n_1.
Qed.

Let size_zc : size zc = n.
Proof.
rewrite zc_alt !remove1_cons_size ?size_tuple ?(inE, chiS, orbT) //.
rewrite cons_uniq (filter_uniq _ zi_uniq) andbT.
by rewrite mem_filter negb_and negbK eqxx orTb.
Qed.

Let zc0 : zc`_0 = chi. Proof. by []. Qed.
Let zc1 : zc`_1 = 'Ind[L, K] '1_K. Proof. by []. Qed.

Let zci (i : 'I_n) : (nat_of_ord i != 1)%N -> zc`_i \in calS.
Proof.
move => i_neq1.
case: (ltngtP i 1); last by move => eq1; move: i_neq1; rewrite eq1 eqxx.
  by rewrite ltnS leqn0 => /eqP ->; rewrite zc0.
move => i_ge2.
have i_eq: nat_of_ord i = (i.-2).+2.
  rewrite !(@ltn_predK 0) // -ltnS; last by rewrite (ltn_predK i_ge2).
  by rewrite -[i.+1]addn1; exact: (ltn_addr 1 i_ge2).
have n_eq: n = (n.-2).+2.
  have n_ge2: (2 <= n)%N by exact: (ltn_trans i_ge2 (ltn_ord i)).
  by rewrite -{1}(subnK n_ge2) subn2 addn2.
rewrite i_eq /=.
suff : (remove1 calS chi)`_i.-2 \in remove1 calS chi.
  by rewrite mem_filter => /andP [].
apply: mem_nth.
have ->: size (remove1 calS chi) = n.-2.
  by rewrite remove1_size ?(eqP size_calS) ?filter_uniq.
by rewrite -(ltn_add2r 2) !addn2 -i_eq -n_eq (ltn_ord i).
Qed.

Let uniq_zc : uniq zc.
Proof.
rewrite /= !filter_uniq // andbT inE !mem_filter !negb_and !negb_or.
rewrite /= !negbK !eqxx orbT !andbT.
by case/calSP: chiS => _ <-.
Qed.


Let zcP t : reflect (exists i : Iirr K, t = 'Ind[L, K] 'xi_i) (t \in zc).
Proof.
apply: (iffP idP).
  case/(nthP 0) => i; rewrite size_zc => i_lt_n <-.
  case: (boolP (i == 1)%N).
    by move/eqP ->; rewrite zc1; exists 0; rewrite cfuni_xi0.
  move => i_n_1; pose i1 := Ordinal i_lt_n; have: (nat_of_ord i1 != 1)%N by [].
  move/zci; case/calSP => j -> _.
  by case: (zi_ind j) => r ->; exists r.
case => r ->.
rewrite zc_alt inE mem_filter !inE mem_filter !inE.
do 2 case: (_ == _); move => //=.
by apply/ziP; exists r.
Qed.



Lemma pf78c1 f : f \in irr G -> 
  (forall psi, psi \in calS -> '[nu psi, f]_G = 0) ->
  {in A, forall x, f^\rho x = '[beta, f]_G}.
Proof.
move => f_irr f_ortho x xA.
have fZ: f \in 'Z[irr G] by case/irrIP: f_irr => r <-; rewrite vchar_irr.
have fC : f \in 'CF(G).
  apply: memc_vchar; rewrite vchar_split fZ andTb.
  by case/irrIP: f_irr => r <-; rewrite (support_memc (memc_irr r)).
rewrite (pf77a ddA nKL AK1 uniq_zc zcP fC xA).
rewrite size_zc.
have n_gt1 : (1 < n)%N.
  by have := n1_gt0; rewrite -(ltn_add2r 1) !addn1 (prednK size_zi_gt0).
pose i1 := Ordinal n_gt1.
rewrite (bigID (pred1 i1)) /= big_pred1_eq big1; last first.
  move => i i_neq1.
  have i_n_1: (nat_of_ord i != 1)%N by apply: contra i_neq1.
  rewrite -!/fcf chi1 -nu_tau; last by apply: diff_ZA; rewrite (zci i_n_1).
  rewrite raddf_sub raddfMZ; last by apply: coefZ; exact: zci.
  rewrite inner_prodDl inner_prodNl !inner_prodZl.
  by rewrite !f_ortho ?zci // mulr0 subrr conjC0 !mul0r.
rewrite zc1 /beta !cinduced_1 !ffunE in_group.
rewrite AK1 in_setD1 in xA; move/andP: xA => [_] ->.
rewrite -!/fcf [e *: true%:R]/GRing.scale /= mulr1 chi1 mulfV // scale1r.
rewrite -cinduced_1 norm_ind1K divfK // addr0.
by rewrite isZC_conj // isZC_inner_Zirr // Dade_vchar.
Qed.



Lemma pf78c2 f : f \in irr G -> 
  (forall psi, psi \in calS -> '[nu psi, f]_G = 0) ->
  '[f^\rho]_L = #|A|%:R / #|L|%:R * '[beta, f]_G ^+ 2.
Proof.
move => f_irr f_ortho.
have fZ: f \in 'Z[irr G] by case/irrIP: f_irr => r <-; rewrite vchar_irr.
have fC : f \in 'CF(G).
  apply: memc_vchar; rewrite vchar_split fZ andTb.
  by case/irrIP: f_irr => r <-; rewrite (support_memc (memc_irr r)).
rewrite (norm_chi_rho ddA fC).
rewrite [_ / _]mulrC -mulrA; congr (_ * _).
rewrite -sum1_card natr_sum -!mulr_suml; apply: eq_bigr => x xA.
rewrite pf78c1 // mul1r sqrtCK expr2; congr (_ * _).
apply: isZC_conj; apply: isZC_inner_Zirr => //.
by apply: Dade_vchar; exact: beta_ZA.
Qed.


End Prelim3.

End Seven.
