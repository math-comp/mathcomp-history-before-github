(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup.
Require Import matrix mxalgebra mxrepresentation vector algC classfun character.
Require Import frobenius inertia vcharacter PFsection1 PFsection2 PFsection5.

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


Section MoreSequence.

Variable (T : eqType).
Implicit Type s : seq T.

Definition filter1 s x := filter (predC1 x) s.

Lemma filter1_cons s x : x \in s -> s =i x :: filter1 s x.
Proof.
move => xs y; rewrite in_cons mem_filter; apply/idP/orP.
  by move ->; rewrite andbT /=; apply/orP; rewrite orbN.
by case => [/eqP ->| /andP []].
Qed.

Lemma filter1_cons_size s x : uniq s -> x \in s ->
  size (x :: filter1 s x) = size s.
Proof.
move => us xs; apply/eqP; rewrite -uniq_size_uniq //; last by exact: filter1_cons.
by rewrite cons_uniq filter_uniq // andbT mem_filter negb_and negbK eqxx orTb.
Qed.

Lemma filter1_size s x : uniq s -> x \in s -> 
  size (filter1 s x) = (size s).-1.
Proof. by move => us xs; rewrite -(filter1_cons_size us xs) -pred_Sn. Qed.


Lemma filter_pred1_uniq s x :
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


Lemma tnthP m (t : m.-tuple T) x : reflect (exists j, x = tnth t j) (x \in t).
Proof.
apply: (iffP idP); last first.
  case => j ->; apply/(@nthP T t _ x).
  by exists j; rewrite ?(size_tuple, ltn_ord) -?tnth_nth.
move => xt; move/nthP: (xt) => /(_ x) [] j.
rewrite size_tuple => j_lt_m <-.
exists (Ordinal j_lt_m).
by rewrite (@tnth_nth m T x t (Ordinal j_lt_m)).
Qed.

End MoreSequence.


Section MoreBig.

Variable T : eqType.
Variable R : Type.
Variable idx : R.
Variable op : Monoid.law idx.

Lemma big_pred1_uniq (s : seq T) x F : 
  uniq s -> x \in s -> \big[op/idx]_(i <- s | i == x) F i = F x.
Proof.
move => uniq_s xs.
rewrite -big_filter filter_pred1_uniq // big_cons big_nil.
by rewrite Monoid.mulm1.
Qed.

End MoreBig.


(* Useful results about the Dade isometry *)
Section MoreDade.

Variable (gT : finGroupType) (G : {group gT}).
Variables (A : {set gT}) (L : {group gT}) (H : gT -> {group gT}).
Hypothesis ddA : Dade_hypothesis G L H A.

Local Notation "alpha ^\tau" := (Dade ddA alpha)
  (at level 2, format "alpha ^\tau").

Local Notation Atau := (Dade_support ddA).


Lemma Dade_conjC (alpha : {cfun gT}) : alpha \in 'CF(L, A) ->
  ((alpha^\tau)^*)%CH = (alpha^*)%CH^\tau.
Proof.
move => alphaC; apply/cfunP => g; rewrite cfunE.
have alpha_conjC : (alpha^*)%CH \in 'CF(L, A).
  move/cfun_memfP: alphaC => [alpha_supp alphaJ].
  apply/cfun_memfP; split => [x xnAL | x y yA].
    by rewrite cfunE (alpha_supp x xnAL) conjC0.
  by rewrite !cfunE (alphaJ x y yA).
case: (boolP (g \in Atau)) => [ | gnAtau].
  case/bigcupP => a aA gD1.
  by rewrite (DadeE alphaC aA gD1) (DadeE alpha_conjC aA gD1) cfunE.
by rewrite !(supportP (support_Dade ddA _) _ gnAtau) conjC0.
Qed.

Lemma Dade0 : 0^\tau = 0.
Proof.
apply/cfunP => x; rewrite !cfunE.
by case: pickP => //= x0; rewrite cfunE.
Qed.

Lemma Dade_supportJ g : g \in G -> Atau :^ g = Atau.
Proof.
move => gG; rewrite /Atau -bigcupJ; apply: eq_bigr => a aA.
rewrite /Dade_support1 class_supportEl -bigcupJ; apply: eq_bigr => x _.
by rewrite -class_rcoset (rcoset_id gG).
Qed.

End MoreDade.



(********************************)
(* The proof of 5.9 *)
Section MoreFive.

Variable (gT : finGroupType) (G : {group gT}).
Variables (A : {set gT}) (L : {group gT}) (H : gT -> {group gT}).
Hypothesis ddA : Dade_hypothesis G L H A.

Local Notation "alpha ^\tau" := (Dade ddA alpha)
  (at level 2, format "alpha ^\tau").

Local Notation Atau := (Dade_support ddA).

Let sAL : A \subset L. Proof. by have [/subsetD1P[]] := ddA. Qed.
Let notA1 : 1%g \notin A. Proof. by have [/subsetD1P[]] := ddA. Qed.
Let nAL : L \subset 'N(A). Proof. by have [_ /subsetIP[]] := ddA. Qed.
Let sLG : L \subset G. Proof. by have [_ /subsetIP[]] := ddA. Qed.


Section Five59.


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
  case/and3P: Hf=> _ _; move/supportP; apply.
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
  have {suppChi} := contra suppChi; rewrite !inE negb_or xnA andbT negbK -/fcf.
  case x1: (x == 1%g); last by move => /(_ isT) /eqP ->; rewrite conjC0 subrr.
  move/eqP: x1 -> => _; case/irrIP: chiIrr => r <-.
  case/isNatCP: (isNatC_irr1 r) => n ->.
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
  rewrite (Dade_conjC ddA fC).
  suff ->: (f^*)%CH = -f by rewrite linearN.
  by apply/cfunP => x; rewrite !cfunE rmorph_sub conjCK oppr_sub.
rewrite f_tau oppr_sub.
have ->: (('xi_i - 'xi_j)^*)%CH = (('xi_i)^*)%CH - (('xi_j)^*)%CH.
  by apply/cfunP => x; rewrite !cfunE rmorph_sub.
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

Definition u_map (alpha : {cfun gT}) : {cfun gT} :=
  [ffun x => u (alpha x)].

Hypothesis u_map_irrG_inv : forall i, u_map ('xi[G]_i) \in irr G.

Local Notation "alpha ^\u" := (u_map alpha)
  (at level 2, format "alpha ^\u").

Let u_fix_Z z : isZC z -> u z = z.
Proof.
rewrite isZCE; case/orP; case/isNatCP=> n; first by move ->; rewrite rmorph_nat.
by move/eqP; rewrite eqr_oppC => /eqP ->; rewrite rmorphN rmorph_nat.
Qed.

Lemma u_map_is_rmorphism : rmorphism u_map.
Proof.
split => [f g|]; first by apply/cfunP => x; rewrite !cfunE rmorph_sub.
by split => [f g|]; apply/cfunP => x; rewrite !cfunE (rmorphM, rmorph1).
Qed.

Canonical u_map_additive := Additive u_map_is_rmorphism.
Canonical u_map_rmorphism := RMorphism u_map_is_rmorphism.


Let u_map_scalZ z (f : {cfun gT}) : isZC z -> u_map (z *: f) = z *: u_map f.
Proof.
by move => isZ; apply/ffunP => x; rewrite !cfunE rmorphM [u z]u_fix_Z.
Qed.

Let u_map_scaln n (f : {cfun gT}): u_map (n%:R *: f) = n%:R *: u_map f.
Proof. apply: u_map_scalZ; exact: isZC_nat. Qed.

Let u_map_inj : injective u_map.
Proof.
move => f g /ffunP => f_e_g; apply/ffunP => x.
by move: (f_e_g x); rewrite !ffunE => /fmorph_inj.
Qed.


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
move => alphaC; apply/cfunP => g; rewrite cfunE.
have alphauC := map_memc alphaC.
case: (boolP (g \in Atau)).
  case/bigcupP => a aA gD1.
  by rewrite (DadeE alphaC aA gD1) (DadeE alphauC aA gD1) cfunE.
move => gnAtau.
rewrite (supportP (support_Dade ddA alpha) _ gnAtau).
by rewrite (supportP (support_Dade ddA (alpha^\u)) _ gnAtau) rmorph0.
Qed.


(* Variables and assumptions of 5.9(a) *)

Variable calS : seq {cfun gT}.
Variable tau1 : {additive {cfun gT} -> {cfun gT}}.
Variable chi : {cfun gT}.

Hypothesis size_ge2 : size calS >= 2.
Hypothesis freeS : free calS.
Hypothesis sSirrL : {subset calS <= irr L}.
Hypothesis ZL_eq_ZA : 'Z[calS, L^#] =i 'Z[calS, A].
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


Let val1scaleZ (f g : {cfun gT}) (S : seq {cfun gT}) K : 
  f \in calS -> g \in 'Z[S, K] -> f 1%g *: g \in 'Z[S, K].
Proof.
move => fS gZ.
case/irrIP: (sSirrL fS) => r <-.
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
case/orP => [/eqP -> | xnL]; rewrite !cfunE; first by rewrite [_ *: _]mulrC subrr.
by rewrite -!/fcf !(supportP (support_vchar (psiVC _)) _ xnL) // !scaler0 subrr.
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
  rewrite u_map_scalZ; last by exact: (@isZC_coord_vchar _ _ _ [set: gT]).
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
  exists eps : bool, exists r : Iirr G, f = (-1) ^+ eps *: 'xi_r.
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
- by exists false; exists e1; rewrite expr0.
- by exists true; exists e1; rewrite expr1.
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
case: (vchar_norm1_irr (tau1_to (psi_inZ chiS)) (psi_norm chi chiS)) => eps.
case => t zi_chi.
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
  have /andP [chi0 psi0]: (0 < chi 1%g) && (0 < psi 1%g).
    case/irrIP: (sSirrL chiS) => ? <-.
    case/irrIP: (sSirrL psiS) => ? <-.
    by rewrite !ltC_irr1 andTb.
  have chi1_unit: chi 1%g != 0.
    by rewrite ltCE in chi0; move/andP: chi0 => [].
  rewrite !mulrA divfK // => lhs_eq; rewrite [_ *: _]lhs_eq.
  rewrite mulrAC mulrC !mulrA.
  rewrite 3?sposC_mul ?ltC_irr1 ?sposC_inv //.
  by case/orP: e_cases => /eqP ->; rewrite ?mulrNN mul1r sposC1.
move => posH.
have psi_irr := vchar_norm1_irr (tau1_to (psi_inZ psiS)) (psi_norm psi psiS).
have anti_ltC a : 0 < a -> 0 < -a -> False.
  rewrite !ltCE eqr_oppC oppr0.
  move/andP => [an0 age0] /andP [_ nage0].
  have ale0: a <= 0.
    by move: nage0; rewrite -leC_sub -[a <= 0]leC_sub addrC oppr0.
  by move: (leC_anti ale0 age0) => aeq0; move: an0; rewrite aeq0 eqxx.
case: psi_irr => ee [r] tau1_eq; move: posH; rewrite tau1_eq scalerA.
case/orP: e_cases => /eqP ->; case: {tau1_eq} ee;
  rewrite (expr1, expr0) ?mulrNN ?mulr1 ?mul1r ?scaleNr scale1r ?irr_xi //.
  by rewrite cfunE; move/(anti_ltC _ (ltC_irr1 r)).
by rewrite cfunE; move/(anti_ltC _ (ltC_irr1 r)).
Qed.



Let exists_psi : exists2 psi, psi \in calS & chi != psi.
Proof.
pose S := filter1 calS chi.
pose psi := S`_0.
have: psi \in S.
  apply: mem_nth; rewrite filter1_size ?uniq_free //.
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
rewrite !u_map_scalZ // => H1.
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


End Five59.


Section Five59Special.

Variable calS : seq {cfun gT}.
Variable tau1 : {additive {cfun gT} -> {cfun gT}}.
Variable chi : {cfun gT}.

Hypothesis size_ge2 : size calS >= 2. 
Hypothesis freeS : free calS.
Hypothesis sSirrL : {subset calS <= irr L}.
Hypothesis ZL_eq_ZA : 'Z[calS, L^#] =i 'Z[calS, A].
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

End Five59Special.


End MoreFive.


(* The main section *)
Section Seven.

Variable (gT : finGroupType) (G : {group gT}).

(* 7.1 - 7.3, 7.6 - 7.8 *)
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


(**********************************)
(* 7.1 *)

Definition rho_fun (chi : {cfun gT}) : {cfun gT} :=
  [ffun a => 
    if a \in A then #|H a|%:R ^-1 * (\sum_(x \in H a) chi (x * a)%g) else 0].


Lemma rho_is_linear : linear rho_fun.
Proof.
move=> mu alpha beta; apply/cfunP=> a; rewrite !cfunE.
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
  by rewrite (setIidPl sAL) => aA; rewrite (supportP (support_rho chi)).
have aaxA: (a \in A) = (a ^ x \in A).
  by rewrite -mem_conjgV (normP _) // in_group (subsetP nAL x xL).
case aA: (a \in A); last by rewrite !(supportP (support_rho chi)) -?aaxA ?aA.
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
rewrite -[alpha _]mul1r -{2}(mulVf (neq0GC (H a))) -mulrA.
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
by apply: (supportP supp_f).
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
  symmetry; apply (supportP (support_Dade ddA chi1^\rho)).
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


(* Hypothesis 7.6 and the proofs of 7.7 and 7.8 *)
Section PF76.

(* 7.6 *)
(* K == H in the text *)
Variable K : {group gT}.
Variable zi : seq {cfun gT}.

Hypothesis nKL : K <| L.
Hypothesis AK1 : A = K ^#.

Hypothesis zi_uniq : uniq zi.
Hypothesis ziP : forall t,
  reflect (exists i, t = 'Ind[L, K] ('xi[K]_i)) (t \in zi).


Let sKL : K \subset L. Proof. by move/andP: nKL => []. Qed.

Let k := #|K|%:R : algC.
Let e := #|L : K|%:R : algC.

Let unit_k : k != 0. Proof. by rewrite -neq0N_neqC -lt0n cardG_gt0. Qed.

Let unit_e : e != 0. Proof. by rewrite -neq0N_neqC -lt0n indexg_gt0. Qed.

Let ke : k * e = #|L|%:R.
Proof. by apply/eqP; rewrite -natr_mul -eqN_eqC LaGrange. Qed.


Let size_zi_gt0 : (0 < size zi)%N.
Proof.
case nn: (size zi); last by [].
have: ('Ind[L, K] 'xi[K]_0 \in zi) by apply/ziP; exists 0.
by rewrite (size0nil nn) in_nil.
Qed.


Let zi_ind f : f \in zi -> exists r, f = 'Ind[L, K] 'xi[K]_r.
Proof. by move/ziP. Qed.

Let ziC f : f \in zi -> f \in 'CF(L, K).
Proof.
case/zi_ind => r ->; rewrite memcE; apply/andP; split.
  by apply: support_induced; rewrite ?memc_irr.
by apply: memc_induced; [by move/andP: nKL => [] | by rewrite memc_irr].
Qed.

Let zi1_neq0 f : f \in zi -> f (1%g) != 0.
Proof.
case/zi_ind => r ->.
rewrite -/fcf cinduced1; last by move/andP: nKL => [].
by rewrite mulf_neq0 ?irr1_neq0.
Qed.

Let norm_zi_unit f : f \in zi -> '[f]_L != 0.
Proof.
move => f_zi; case eq0: ('[_, _]_L == 0); last by [].
move: eq0; rewrite (inner_prod0 (memcW (ziC f_zi))).
move/eqP => eq0; move: (zi1_neq0 f_zi).
by rewrite eq0 cfunE eqxx.
Qed.

Let zi_pairwise_ortho : pairwise_orthogonal L zi.
Proof.
apply/pairwise_orthogonalP; split.
- by move => f /ziC /memcW.
- rewrite cons_uniq zi_uniq andbT.
  apply: contraT; rewrite negbK => /ziP [r] /esym/eqP.
  rewrite cinduced_eq0 ?is_char_irr // => /eqP/cfunP /(_ 1%g) xi1_0.
  by move: (irr1_neq0 r); rewrite xi1_0 cfunE eqxx.
move => f g; case/ziP => r ->; case/ziP => t -> {f g}.
have := cconjugates_irr_induced r t nKL.
by case: (_ \in _) => //; move ->; rewrite eqxx.
Qed.


Let zi_ortho f g : f \in zi -> g \in zi -> f != g -> '[f, g]_L = 0.
Proof.
move => fZ gZ fng; case/pairwise_orthogonalP: zi_pairwise_ortho => _ _.
by move => /(_ f g fZ gZ fng).
Qed.

Let n := size zi.

Let in_zi (i : 'I_n) : zi`_i \in zi. Proof. exact: mem_nth. Qed.


(********************)
(* 7.7 *)
Section PF77.

Variable zi0 : {cfun gT}.
Hypothesis zi0_in_zi : zi0 \in zi.

Variable chi : {cfun gT}.
Hypothesis chiC : chi \in 'CF(G).


Let d (f : {cfun gT}) := f 1%g / zi0 1%g.

Let zi_val1 (f : {cfun gT}) : f (1%g) = d f * zi0 (1%g).
Proof. by rewrite -mulrA mulVf ?zi1_neq0 ?mulr1. Qed.


Let c (f : {cfun gT}) := '[(f - d f *: zi0)^\tau, chi]_G.


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
  \sum_(f <- zi) (c f)^* / '[f]_L * f x.
Proof.
move/andP: (nKL) => [_] sLNK xA.
pose psi (f : {cfun gT}) := f - d f *: zi0.
have psiC (f : {cfun gT}): f \in zi -> psi f \in 'CF(L, A).
  move => f_zi; rewrite memcE.
  apply/andP; split; last first.
    apply: memv_sub; first by exact: (memcW (ziC _)).
    by apply: memvZl; exact: (memcW (ziC _)).
  apply/subsetP => g; rewrite inE /=; apply: contraR.
  rewrite AK1 inE negb_and negbK in_set1 !cfunE -!/fcf.
  case/orP => [| gnK]; first by move/eqP ->; rewrite zi_val1 subrr.
  suff [-> ->]: f g = 0 /\ zi0 g = 0 by rewrite scaler0 subrr.
  by split; apply: (supportP (support_memc (ziC _)) _ gnK).
have f_eq (f : {cfun gT}): f \in 'CF(L, A) -> f = e^-1 *: 'Ind[L, K] ('Res[K] f).
  move => fC; apply/cfunP => g; rewrite cfunE.
  case: (boolP (g \in K)) => gK.
    rewrite !cfunE -/k.
    set S := \sum_(y \in _) _.
    have {S}->: S = \sum_(y \in L) f g.
      apply: eq_bigr => u uL.
      rewrite crestrictE; first by exact: (cfunJ _ fC).
      by rewrite memJ_norm //; move/subsetP: sLNK => /(_ u uL).
    rewrite sumr_const /GRing.scale /= mulrA -invf_mul [e * k]mulrC ke.
    rewrite -[f g *+ _]mulr_natl mulrA mulVf ?mul1r //.
    by rewrite -neq0N_neqC -lt0n cardG_gt0.
  have suppInd := support_induced (memc_restrict sKL (memcW fC)) nKL.
  rewrite -!/fcf (supportP suppInd _ gK) scaler0.
  apply: (supportP (support_memc fC)).
  by move: gK; apply: contra; rewrite AK1 inE => /andP [].
have {f_eq} f_in_zi f: f \in 'CF(L, A) -> f \in (\sum_(g <- zi) g%:VS)%VS.
  move => fC; rewrite (f_eq f fC).
  rewrite -(sum_inner_prodE (memc_restrict sKL (memcW fC))).
  apply: memvZl; rewrite linear_sum /=; apply: memv_suml => r _.
  rewrite linearZ /=; apply: memvZl.
  rewrite (big_nth 0) big_mkord.
  apply/memv_sumP.
  have: exists j : 'I_n, 'Ind[L, K] 'xi_r = zi`_j.
    have: 'Ind[L, K] 'xi_r \in zi by apply/ziP; exists r.
    by case/(nthP 0) => j j_lt_n j_ind; exists (Ordinal j_lt_n); rewrite j_ind.
  case => i ->.
  exists (fun j => if j == i then zi`_i else 0); split.
    move => j _; case ji: (_ == _); last by exact: mem0v.
    by move/eqP: ji ->; exact: memv_inj.
  by rewrite -big_mkcond big_pred1_eq.
have {f_in_zi} f_in_psi f: f \in 'CF(L, A) -> 
                           exists f_, f = \sum_(i < n) (f_ i *: psi zi`_i).
  move => fC; have := f_in_zi f fC.
  rewrite (big_nth 0) big_mkord; case/memv_sumP => fv [fv_def f_sum].
  have: exists f_, forall i, fv i = f_ i *: zi`_i.
    exists (fun i => (fv i (1%g)) / zi`_i 1%g) => i.
    have:= fv_def  i => /(_ isT).
    case/injvP => fc ->.
    by congr (_ *: _); rewrite cfunE -mulrA mulfV ?(zi1_neq0, in_zi) // mulr1.
  case => f_ f_def; exists f_.
  have ->: \sum_(i < n) f_ i *: psi zi`_i = 
       \sum_(i < n) f_ i *: zi`_i - (\sum_(i < n) f_ i * d zi`_i) *: zi0.
    rewrite scaler_suml -sumr_sub.
    by apply: eq_bigr => i _; rewrite scaler_subr scalerA.
  suff ->: \sum_(i < n) f_ i * d zi`_i = 0.
    by rewrite scale0r subr0 f_sum; apply: eq_bigr => i _; exact: f_def.
  have: (\sum_(i < n) f_ i * d zi`_i) * zi0 1%g = f 1%g.
    rewrite -mulr_suml f_sum /= sum_ffunE cfunE.
    by apply: eq_bigr => i _; rewrite -mulrA -zi_val1 f_def cfunE.
  rewrite -!/fcf (cfunS0 fC); last first.
    by rewrite AK1 in_setD1 negb_and negbK eqxx orTb.
  move/eqP; rewrite mulf_eq0; move: (zi1_neq0 zi0_in_zi).
  by case: (zi0 _ == 0); first by []; rewrite orbF => _ /eqP.
have {f_in_psi}f_eq0 f: f \in 'CF(L, A) ->
  (forall g, g \in zi -> '[psi g, f]_L = 0) -> f = 0.
  move => fC prod0; have := f_in_psi f fC; case => f_ f_sum.
  apply/eqP; rewrite -(inner_prod0 (memcW fC)).
  rewrite {2}f_sum raddf_sum big1 //= => i _.
  by rewrite inner_prodZr inner_conj prod0 ?in_zi // conjC0 mulr0.
pose b (f : {cfun gT}) := (c f)^* / '[f]_L.
have b0 : b zi0 = 0.
  by rewrite /b/c/d mulfV ?zi1_neq0 // scale1r subrr Dade0 inner_prod0l conjC0 mul0r.
pose f := chi^\rho - \sum_(g <- zi) b g *: g.
have fC : f \in 'CF(L, K).
  apply: memv_sub; last first.
    rewrite big_seq_cond; apply: memv_suml => g /andP [g_zi _].
    by apply: memvZl; exact: ziC.
  by apply: (memc_subset _ (rho_cfunS chiC)); rewrite AK1 subsetDl.
have := crestr1 fC.
set h := [ffun _ => _]; rewrite -AK1.
case => hC; case => /(_ x xA) f_eq_h h_inner; move: f_eq_h.
suff ->: h = 0.
  rewrite [in X in _ = X]cfunE cfunE => /eqP.
  rewrite -!/fcf addr_eq0 => /eqP ->; rewrite sum_cfunE cfunE opprK cfunE.
  by apply: eq_bigr => i _; rewrite cfunE /b -[_ *: _]mulrA -mulrA.
apply: (f_eq0 h hC) => g g_zi; rewrite -h_inner ?psiC // raddf_sub /=.
have ->: '[psi g, chi^\rho]_L = c g.
  by rewrite -(rho_Dade_reciprocity chiC (psiC g g_zi)).
rewrite inner_prodDl inner_prodNl !raddf_sum /=.
rewrite (bigID (pred1 g)) /= big_pred1_uniq // !big1_seq ?addr0.
- rewrite /b inner_prodZr rmorphM fmorphV {1}inner_conj !conjCK.
  by rewrite divfK (subrr, norm_zi_unit).
- move => ff /andP [_ ff_zi]; rewrite inner_prodZr inner_prodZl.
  case ff_e_zi0: (ff == zi0).
    by move/eqP: ff_e_zi0 ->; rewrite b0 conjC0 mul0r oppr0.
  by rewrite zi_ortho ?mulr0 ?oppr0 // eq_sym ff_e_zi0.
move => ff /andP [ff_n_g ff_zi]; rewrite inner_prodZr.
by rewrite zi_ortho ?mulr0 // eq_sym.
Qed.



Lemma mulr_sum (I J : finType) (f : I -> algC) (g : J -> algC) :
  (\sum_(i \in I) f i) * (\sum_(j \in J) g j) = 
  \sum_(i \in I) \sum_(j \in J) f i * g j.
Proof.
elim/big_rec2: _; first by rewrite mul0r.
by move => i y1 y2 _ <-; rewrite mulr_addl mulr_sumr.
Qed.


Lemma pf77b : '[chi^\rho]_L = 
  \sum_(f <- zi) \sum_(g <- zi) ((c f)^* * c g / '[f]_L / '[g]_L
    * ('[f, g]_L - f 1%g * g 1%g / (e * k))).
Proof.
rewrite (norm_supportE (support_rho chi) sAL) -ke.
have ->: \sum_(x \in A) normC (chi^\rho x) ^+ 2 =
  \sum_(x \in A) (\sum_(i < n) \sum_(j < n) (c zi`_i)^* * (c zi`_j) / 
    '[zi`_i, zi`_i]_L / '[zi`_j, zi`_j]_L * (zi`_i x * (zi`_j x)^*)).
  apply: eq_bigr => x xA; rewrite (pf77a xA) (big_nth 0) big_mkord.
  rewrite normCK rmorph_sum mulr_sum.
  apply: eq_bigr => i _; apply: eq_bigr => j _.
  rewrite [(_ / _ * _)^*]rmorphM [(_ / _)^*]rmorphM conjCK.
  rewrite fmorphV // -[in X in (_ / X * _^*)]inner_conj.
  set X := _ ^-1; set Y := _ ^-1; set C1 := _^*; set C2 := c zi`_j.
  rewrite (mulrAC C1 C2 X) 2!mulrA; congr (_ * _).
  by rewrite mulrA (mulrAC (C1 * X) _ _) (mulrAC (C1 * X * C2) _ _).
have ke_unit: k * e != 0 by exact: mulf_neq0.
rewrite -[X in _ = X]mul1r -(mulVf ke_unit) -[X in _ = X]mulrA; congr (_ * _).
rewrite -mulr_sumr (big_nth 0) big_mkord exchange_big /=; apply: eq_bigr => i _.
rewrite -mulr_sumr (big_nth 0) big_mkord exchange_big /=; apply: eq_bigr => j _.
rewrite mulr_sumr.
rewrite (mulrCA (k * e) _ _); congr (_ * _).
rewrite mulr_addr mulrN [e * k]mulrC.
rewrite (mulrCA (k * e) _ (_ ^-1)) mulfV // mulr1.
set X := \sum_(x \in _) _; set Y := _ * _ 1%g.
suff ->: k * e * '[zi`_i, zi`_j]_L = Y + X by rewrite addrAC subrr add0r.
rewrite (inner_prod_supportE zi`_j (support_memc (ziC (in_zi i))) sKL) -ke.
rewrite mulrA mulfV // mul1r.
rewrite (big_setID 1%g) /= setIg1 big_set1 -AK1 -/X /Y.
congr (_ * _ + _).
rewrite posC_conjK //; apply: (@posC_char1 _ L _); case: (zi_ind (in_zi j)) => r ->.
by apply: is_char_induced; rewrite ?sKL ?is_char_irr.
Qed.



End PF77.


(*************************)

(* 7.8 *)

Section PF78.

Let calS := filter1 zi ('Ind[L, K] '1_K).

Definition my_coherent L G (S : seq {cfun gT}) A 
  (tau : {cfun gT} -> {cfun gT}) (tau1 : {additive {cfun gT} -> {cfun gT}}) :=
  [/\ exists2 theta, theta \in 'Z[S, A] & theta != 0,
      {in 'Z[S] &, isometry L G tau1},
      {in 'Z[S], forall phi, tau1 phi \in 'Z[irr G]}
    & {in 'Z[S, A], tau1 =1 tau}].

Variable nu : {additive {cfun gT} -> {cfun gT}}.

Hypothesis calS_coherent : my_coherent L G calS A (Dade ddA) nu.

(* chi == zi in 7.8 *)
Variable chi : {cfun gT}.

Hypothesis (chiS : chi \in calS) (chi_irrL : chi \in irr L).
Hypothesis chi1 : chi 1%g = e.

Let beta := ('Ind[L, K] '1_K - chi)^\tau.




Let sSzi : {subset calS <= zi}.
Proof. by move => f; rewrite mem_filter => /andP []. Qed.

Let uniqS : uniq calS.
Proof. exact: filter_uniq. Qed.


(*
Let sSZL : {subset calS <= 'Z[irr L]}.
Proof.
move => f; case/sSzi => i ->; case: (zi_ind i) => r ->.
by rewrite vchar_char // is_char_induced // is_char_irr.
Qed.


Let tau_isometry : {in 'Z[in_tuple calS, A] &, isometry L G (Dade ddA)}.
Proof.
move => f g fZ gZ /=.
suff sZC: {subset 'Z[calS, A] <= 'CF(L, A)} by rewrite Dade_isometry // sZC.
move => psi psiS; apply: memc_vchar.
by rewrite (vchar_sub_irr _ sSZL) // free_filter.
Qed.


Hypothesis calS_coherent : coherent tau_isometry.
*)


Let defCa : {in A, forall a, H a ><| 'C_L[a] = 'C_G[a]}.
Proof. by case: ddA. Qed.
Let coHL : {in A &, forall a b, coprime #|H a| #|'C_L[b]| }.
Proof. by case: ddA. Qed.
Let nsHC : {in A, forall a, H a <| 'C_G[a]}.
Proof. by move=> a /defCa/sdprod_context[]. Qed.
Let sHG : {in A, forall a, H a \subset G}.
Proof. by move=> a /nsHC/normal_sub/subsetIP[]. Qed.


Let zi_distinct (i j : 'I_n) : i != j -> zi`_i != zi`_j.
Proof.
apply: contraR; rewrite negbK => zi_eq.
have := nth_uniq 0 (ltn_ord i) (ltn_ord j) zi_uniq.
rewrite zi_eq => /eqP; rewrite eq_sym => /eqP /eqP h1.
by apply/eqP; exact: ord_inj.
Qed.


Let free_zi : free zi.
Proof. exact: (orthogonal_free zi_pairwise_ortho). Qed.


(* The consequence of coherence and that A = K^# *)
Let sizeS : size calS >= 2.
Proof.
case: calS_coherent => [[]] f fZ fn0 _ _ _.
case: (ltngtP (size calS) 1) => //.
  rewrite -addn1 -{2}[1%N]addn1 leq_add2r leqn0 size_eq0 => /eqP S_nil.
  move/span_vchar: fZ; rewrite S_nil span_nil memv0 => /eqP f0.
  by move: fn0; rewrite f0 eqxx.
case S: calS => [| g t] //=.
rewrite -addn1 -{2}[1%N]addn1 => /addIn /eqP; rewrite size_eq0 => /eqP t_nil.
move/span_vchar: (fZ); rewrite S t_nil span_seq1.
case/injvP => a f_ag; move/cfunP/(_ 1%g): (f_ag); rewrite cfunE.
rewrite (supportP (support_vchar fZ)); last first.
  by rewrite AK1 !inE negb_and negbK eqxx orTb.
move/esym => /eqP; rewrite mulf_eq0; case/orP.
  by move/eqP => a0; move: f_ag fn0; rewrite a0 scale0r => ->; rewrite eqxx.
have : g \in calS by rewrite S inE eqxx orTb.
by move/sSzi/zi1_neq0/negPf ->.
Qed.


Let one_in_zi : 'Ind[L, K] '1_K \in zi.
Proof. by apply/ziP; exists 0; rewrite cfuni_xi0. Qed.

Let size_calS : size (calS) == n.-1.
Proof. by rewrite (filter1_size zi_uniq one_in_zi). Qed.

Let nu_to : {in 'Z[calS], forall f, nu f \in 'Z[irr G]}.
Proof. by case: calS_coherent => []. Qed.
Let nu_isom : {in 'Z[calS] &, isometry L G nu}.
Proof. by case: calS_coherent => []. Qed.
Let nu_tau : {in 'Z[calS, A], forall f, nu f = f^\tau}.
Proof. by case: calS_coherent => []. Qed.

Let norm_chi : '[chi, chi]_L = 1.
Proof. by case/irrIP: chi_irrL => r <-; rewrite irr_orthonormal eqxx. Qed.

Let calS_not1 psi : psi \in calS -> psi != 'Ind[L, K] '1_K.
Proof. by rewrite mem_filter /= => /andP []. Qed.


Let orthoS psi phi : psi \in calS -> phi \in calS -> psi != phi ->
  '[psi, phi]_L = 0.
Proof. by move/sSzi => psi_zi; move/sSzi => phi_zi; exact: zi_ortho. Qed.


Let orthoS_ind1 psi : psi \in calS -> '[psi, 'Ind[L, K] '1_K]_L = 0.
Proof. by move => psiS; rewrite zi_ortho // ?sSzi ?calS_not1. Qed.

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
by move/negPf: unit_e; rewrite conjC_eq0 => ->.
Qed.

Let supportS psi : psi \in calS -> support psi \subset K.
Proof. by move/sSzi => psi_zi; exact: (support_memc (ziC psi_zi)). Qed.

Lemma dot_support_res (X : {group gT}) (Y : {set gT}) (f g : {cfun gT}):
  support f \subset Y -> '[f, g]_X = '[f, 'Res[Y] g]_X.
Proof.
move => supp_f; rewrite !inner_prodE; congr (_ * _).
apply: eq_bigr => x xX; rewrite !cfunE.
case: (boolP (x \in Y)); first by rewrite mul1r.
by move => xnY; rewrite (supportP supp_f _ xnY) !mul0r.
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
pose S := filter1 calS chi.
pose psi := S`_0.
have: psi \in S.
  apply: mem_nth; rewrite filter1_size //.
  rewrite -(ltn_add2l 1) !add1n prednK //.
  by apply: (ltn_trans _ sizeS).
by rewrite mem_filter /= eq_sym => /andP [chi_n_psi psiS]; exists psi.
Qed.


Let psi_inZS psi : psi \in calS -> psi \in 'Z[calS].
Proof. by move => psiS; apply: memv_vchar => //; exact: free_filter. Qed.


Let psi_inZSK psi : psi \in calS -> psi \in 'Z[calS, K].
Proof.
move => psiS; apply: memv_vchar => //; first by exact: free_filter.
by move: (sSzi psiS) => psi_zi; exact: (support_memc (ziC psi_zi)).
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
move => gS; move: (sSzi gS) => g_zi; case: (zi_ind g_zi) => r ->.
rewrite -/fcf cinduced1 // -/e mulrC mulrA mulVf // mul1r. 
by rewrite isZCE isNatC_irr1 orTb.
Qed.

Let diff_ZA g : g \in calS -> g - (g 1%g / e) *: chi \in 'Z[calS, A].
Proof.
move => gS; rewrite vchar_split; apply/andP; split.
  apply: vchar_sub; first by exact: psi_inZS.
  by apply: vchar_scalZ; [exact: coefZ | exact: psi_inZS].
rewrite AK1; apply/subsetP => x; apply: contraR.
rewrite !inE !cfunE negb_and negbK -!/fcf.
case/orP => [/eqP -> | xnK].
  by rewrite chi1 -[_ *: _]mulrA mulVf // mulr1 subrr.
by rewrite !(supportP (support_vchar (psi_inZSK _)) _ xnK) // scaler0 subrr.
Qed.


Let psi_inC g : g \in calS -> g \in 'CF(L).
Proof.
move => gS; move: (sSzi gS) => psi_zi.
by have := ziC psi_zi; rewrite memcE => /andP [].
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
rewrite !inE cinduced_1 !cfunE negb_and negbK -!/fcf.
case/orP => [/eqP -> | xnK].
  by rewrite chi1 in_group /GRing.scale /= mulr1 subrr.
rewrite (supportP (support_vchar (psi_inZSK chiS)) _ xnK) subr0.
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
case: chi_irr => e0 [] r; set eps := _ ^+ _; move => chi_eq.
have eps_1: eps * eps = 1.
  by rewrite /eps=> {eps chi_eq}; case: e0; rewrite (expr1, expr0) ?mulrNN mulr1.
rewrite chi_eq inner_prodZl.
case r0: (r == 0); last first.
  by rewrite cfuni_xi0 irr_orthonormal r0 mulr0.
case: exists_psi => f fS chi_n_f.
have prod0 : '[nu f, '1_G]_G = 0.
  have ->: '1_G = eps *: nu chi.
    by rewrite chi_eq scalerA eps_1 (eqP r0) scale1r cfuni_xi0.
  apply/eqP; rewrite inner_prodZ mulf_eq0; apply/orP; right; apply/eqP.
  rewrite nu_isom ?(psi_inZS fS) ?(psi_inZS chiS) //.
  move: chi_n_f; move: (sSzi fS) => f_zi; move: (sSzi chiS) => chi_zi.
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
move: (sSzi fS) => f_zi; case: (zi_ind f_zi) => t ->.
rewrite -/fcf cinduced1 //; apply: mulf_neq0; first by [].
by rewrite irr1_neq0.
Qed.



(* 7.8(a)-2 *)

Lemma dot_beta_1 : '[beta, '1_G]_G = 1.
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
    move: (sSzi gS) => g_zi; case: (sSzi fS) => f_zi gnf.
    by rewrite (zi_ortho _ _ gnf) ?scaler0.
  rewrite add0r big_pred1_uniq ?(filter_uniq _ zi_uniq) //.
  rewrite linearZ /= inner_prodbE.
  rewrite nu_isom ?(psi_inZS fS) // /GRing.scale /= -mulrA.
  by rewrite mulVf ?mulr1 // norm_zi_unit ?sSzi.
set SG := \sum_(_ <- _) _.
set S := (_ + _) *: _.
rewrite dot_beta_1 scale1r [_ - _ - _]addrAC.
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
  by rewrite hyp; case: (zi_ind (in_zi i)) => r ->; rewrite inv => ->.
case: (zi_ind (in_zi i)) => r ->.
case hyp: (_ \in _); first by []; move => jr.
have := cconjugates_irr_induced (inv_ind ('Ind[L, K] 'xi_r)) j nKL.
rewrite hyp inv jr => /eqP. 
rewrite inner_prod0 ?cinduced_eq0 ?memc_induced ?is_char_irr ?memc_irr //.
move/eqP/cfunP => /(_ 1%g); rewrite cfunE => contr.
by have := irr1_neq0 r; rewrite contr eqxx.
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
  by case: (zi_ind (in_zi i)) => j -> /(_ j); rewrite eqxx.
rewrite expr2 mulrCA !mulrA divfK //.
rewrite -[_ / e]mulrC -!mulrA.
apply/(mulfI unit_e); rewrite !mulrA mulfV // mul1r.
have := induced_sum_rcosets1 t nKL => /=; rewrite -zi_t.
move/cfunP => /(_ 1%g); rewrite sum_cfunE !cfunE in_group -/e.
rewrite mul1r [_ *: _]mulrAC => ->.
congr (_ * _); apply: eq_bigr => f => f_conj.
by rewrite cfunE expr2.
Qed.


Let norm_ind1K : '['Ind[L, K] '1_K]_L = e.
Proof.
rewrite cinduced_1; rewrite (norm_supportE _ sKL); last first.
  by apply: (@support_memc _ K); apply: memvZl; rewrite cfuni_xi0 memc_irr.
apply: (mulfI (neq0GC L)); rewrite mulrA (mulfV (neq0GC L)) mul1r -ke.
rewrite /k -sum1_card natr_sum -!mulr_suml.
apply: eq_bigr => y yK; rewrite !cfunE yK /GRing.scale /= mulr1.
by rewrite /e normC_nat expr2 mul1r.
Qed.


Lemma sum_squares_calS : \sum_(f <- calS) (f 1%g / e) ^+ 2 / '[f]_L =
  (k - 1) / e.
Proof.
have := sum_zi; rewrite irr_sum_square -/k.
rewrite (bigID (pred1 ('Ind[L, K] '1_K))) /= big_pred1_uniq //.
rewrite norm_ind1K cinduced1 // cfunE in_group mulr1 mulfV // expr2 mulr1.
move/eqP; rewrite eq_sym addrC -subr_eq mulrC -mulr_subl => /eqP ->.
by rewrite -[in X in _ = X]big_filter.
Qed.


(* The sequence for b *)

Let zb_tail := filter1 calS chi.

Let size_zb_tail : size zb_tail = n.-2.
Proof. by rewrite filter1_size // (eqP size_calS). Qed.

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
Proof. exact: calS_not1. Qed.


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


Let c (f : {cfun gT}) := '[(f - f 1%g / z0 1%g *: z0)^\tau, nu chi]_G.

Let z01_neq0 : z0 1%g != 0.
Proof. by apply: zi1_neq0; exact: sSzi. Qed.


Let isZC_psi1 psi : psi \in calS -> isZC (psi 1%g).
Proof.
move/sSzi => psi_zi; case: (zi_ind psi_zi) => j ->.
rewrite -/fcf (cinduced1 _ sKL); apply: isZC_mul; first by exact: isZC_nat.
by case/isNatCP: (isNatC_irr1 j) => t ->; exact: isZC_nat.
Qed.


Let c0 : c z0 = 0.
Proof. by rewrite /c mulfV // scale1r subrr Dade0 inner_prod0l. Qed.


Let diff1_ZS psi : psi \in calS -> z0 1%g *: psi - psi 1%g *: z0 \in 'Z[calS].
Proof.
move => psiS; apply: vchar_sub; apply: vchar_scalZ;
  [exact: isZC_psi1 | exact: psi_inZS | exact: isZC_psi1 | exact: psi_inZS].
Qed.


Let diff1_ZSA psi : psi \in calS -> z0 1%g *: psi - psi 1%g *: z0 \in 'Z[calS, A].
Proof.
move => psiS; rewrite vchar_split (diff1_ZS psiS) andTb AK1.
apply/subsetP => x; apply: contraR.
rewrite !inE !cfunE negb_and negbK.
case/orP => [/eqP -> | xnK]; first by rewrite [_ *: _]mulrC subrr.
by rewrite -!/fcf !(supportP (support_vchar (psi_inZSK _)) _ xnK) // !scaler0 subr0.
Qed.


Let diff2_ZS psi : psi \in calS -> 
  z0 1%g *: psi - ('Ind[L, K] '1_K) 1%g *: z0 \in 'Z[calS].
Proof.
move => psiS; apply: vchar_sub; apply: vchar_scalZ;
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
by rewrite !(supportP (support_vchar (psi_inZSK _)) _ xnK) // !scaler0 subr0.
Qed.

Let c1 : c ('Ind[L, K] '1_K) = a.
Proof.
transitivity ('[beta + (chi - 'Ind[L, K] '1_K 1%g / z0 1%g *: z0)^\tau, nu chi]_G).
  congr ('[_, _]_G); rewrite /beta -linearD.
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


Let c2 : c chi = 1.
Proof.
suff: z0 1%g * c chi = z0 1%g * 1 by move/(mulfI z01_neq0).
rewrite /c -inner_prodZl -linearZ scaler_subr scalerA -mulrCA mulfV // !mulr1.
rewrite /= -nu_tau ?nu_isom ?diff1_ZS ?diff1_ZSA ?psi_inZS //.
rewrite inner_prodDl inner_prodNl !inner_prodZl norm_chi.
by rewrite orthoS ?mulr0 ?mulr1 ?subr0 // eq_sym.
Qed.


Let ci0 f : f \in zi -> f != 'Ind[L, K] '1_K -> f != chi -> c f = 0.
Proof.
move => f_zi f_n_1 f_n_chi.
have fS: f \in calS by rewrite mem_filter /= f_zi f_n_1.
suff: z0 1%g * c f = z0 1%g * 0 by move/(mulfI z01_neq0).
rewrite /c -inner_prodZl -linearZ scaler_subr scalerA -mulrCA mulfV // !mulr1.
rewrite /= -nu_tau ?nu_isom ?diff1_ZS ?diff1_ZSA ?psi_inZS //.
rewrite inner_prodDl inner_prodNl !inner_prodZl.
by rewrite !orthoS ?(mulr0, subr0) // eq_sym.
Qed.


Let u := e^-1 * (1 - k^-1).
Let v := k^-1.
Let w := 1 - e / k.




Let norm_nu_chi_rho : 
  '[(nu chi)^\rho]_L = u * a ^+ 2 - 2%:R * v * a + w.
Proof.
have nu_chiS: nu chi \in 'CF(G) by rewrite memc_Zirr // nu_to // psi_inZS.
rewrite (pf77b (sSzi z0_inS) nu_chiS).
pose pred12 := predU (pred1 ('Ind[L, K] '1_K)) (pred1 chi).
rewrite (bigID pred12) /= addrC big1_seq ?add0r; last first.
  move => f; rewrite negb_or => /andP [/andP [f_n_1 f_n_chi] f_zi].
  apply: big1_seq => g /andP [_ g_zi].
  by move: (ci0 f_zi f_n_1 f_n_chi); rewrite /c => ->; rewrite conjC0 !mul0r.
have sumU F f1 f2: f1 \in zi -> f2 \in zi -> f1 != f2 ->
     \sum_(i <- zi | (i == f1) || (i == f2)) (F i : algC) = F f1 + F f2.
  move => f1_zi f2_zi f1_n_f2; rewrite (bigID (pred1 f1)) /=.
  set S := \sum_(i <- zi | _) _; have {S}->: S = \sum_(i <- zi | i == f1) F i.
    by apply: eq_bigl => x; case: (_ == _) => //; rewrite andbF.
  rewrite big_pred1_uniq //.
  set S := \sum_(i <- zi | _) _; have {S}->: S = \sum_(i <- zi | i == f2) F i.
    apply: eq_bigl => x; case xf1: (_ == _) => /=; last by rewrite andbT.
    by move/eqP: xf1 ->; move/negPf: f1_n_f2 ->.
  by rewrite big_pred1_uniq.
have one_n_chi: 'Ind[L, K] '1_K != chi by rewrite eq_sym calS_not1.
rewrite sumU // ?sSzi //.
rewrite (bigID pred12) [in X in _ + X](bigID pred12) !sumU // ?sSzi //=.
rewrite !big1_seq; first last.
- move => f; rewrite negb_or => /andP [/andP [f_n_1 f_n_chi] f_zi].
  by move: (ci0 f_zi f_n_1 f_n_chi); rewrite /c => ->; rewrite mulr0 !mul0r.
- move => f; rewrite negb_or => /andP [/andP [f_n_1 f_n_chi] f_zi].
  by move: (ci0 f_zi f_n_1 f_n_chi); rewrite /c => ->; rewrite mulr0 !mul0r.
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
  a ^+ 2 * \sum_(f <- filter1 calS chi) (f 1%g / e) ^+ 2 / '[f]_L.
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
  by move/sSzi: fS => f_zi; exact: norm_zi_unit.
rewrite !rmorphM !fmorphV conjC_nat -/e.
rewrite !(isZC_conj _); first by rewrite mulrC expr2 !mulrA.
  by rewrite -nu_isom ?isZC_inner_Zirr ?nu_to ?(psi_inZS fS) //.
exact: isZC_psi1.
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
have := sum_squares_calS.
rewrite (bigID (pred1 chi)) /= big_pred1_uniq //.
rewrite -/fcf chi1 norm_chi mulfV // invr1 expr2 !mul1r.
rewrite addrC => /eqP; rewrite eq_sym -subr_eq => /eqP.
rewrite -big_filter => <-.
by rewrite /u mulrCA mulr_subr mulfV // mulr1 mulrC.
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


Lemma pf78c1 f : f \in irr G -> 
  (forall psi, psi \in calS -> '[nu psi, f]_G = 0) ->
  {in A, forall x, f^\rho x = '[beta, f]_G}.
Proof.
move => f_irr f_ortho x xA.
have fZ: f \in 'Z[irr G] by case/irrIP: f_irr => r <-; rewrite vchar_irr.
have fC := memc_Zirr fZ.
rewrite (pf77a (sSzi chiS) fC xA).
rewrite (bigID (pred1 ('Ind[L, K] '1_K))) /= big_pred1_uniq // big1_seq; last first.
  move => g /andP [g_n_1 g_zi].
  have gS: g \in calS by rewrite mem_filter /= g_n_1 g_zi.
  rewrite chi1 -nu_tau ?diff_ZA // raddf_sub raddfMZ ?coefZ //.
  rewrite inner_prodDl inner_prodNl !inner_prodZl.
  by rewrite !f_ortho // mulr0 subrr conjC0 !mul0r.
rewrite /beta !cinduced_1 !cfunE in_group.
rewrite AK1 in_setD1 in xA; move/andP: xA => [_] ->.
rewrite [e *: true%:R]mulr1 chi1 mulfV // scale1r.
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
rewrite (norm_chi_rho fC).
rewrite [_ / _]mulrC -mulrA; congr (_ * _).
rewrite -sum1_card natr_sum -!mulr_suml; apply: eq_bigr => x xA.
rewrite pf78c1 // mul1r sqrtCK expr2; congr (_ * _).
apply: isZC_conj; apply: isZC_inner_Zirr => //.
by apply: Dade_vchar; exact: beta_ZA.
Qed.


End PF78.


End PF76.

End Prelim1.


(*************************************)
(* 7.4 & 7.5 *)
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


(******************************)
(* 7.9 *)

Section PF79.

Hypothesis oddG : odd #|G|.

Variables (A1 : {set gT}) (L1 : {group gT}) (H1 : gT -> {group gT}).
Variables (A2 : {set gT}) (L2 : {group gT}) (H2 : gT -> {group gT}).

Hypothesis ddA1 : Dade_hypothesis G L1 H1 A1.
Hypothesis ddA2 : Dade_hypothesis G L2 H2 A2.

Local Notation "alpha ^\tau1" := (Dade ddA1 alpha)
  (at level 2, format "alpha ^\tau1").

Local Notation Atau1 := (Dade_support ddA1).

Local Notation "alpha ^\tau2" := (Dade ddA2 alpha)
  (at level 2, format "alpha ^\tau2").

Local Notation Atau2 := (Dade_support ddA2).

Hypothesis disjointA : [disjoint Atau1 & Atau2].


Variables K1 K2 : {group gT}.
Variables zi1 zi2 : seq {cfun gT}.
Variables nu1 nu2 : {additive {cfun gT} -> {cfun gT}}.
Variables chi1 chi2 : {cfun gT}.


Hypotheses (A1K1 : A1 = K1 ^#) (A2K2 : A2 = K2 ^#).
Hypotheses (nK1L1 : K1 <| L1) (nK2L2 : K2 <| L2).

Hypothesis (zi1_uniq : uniq zi1) (zi2_uniq : uniq zi2).
Hypothesis zi1P : forall t, reflect (exists i : Iirr K1, t = 'Ind[L1, K1] 'xi_i) (t \in zi1).
Hypothesis zi2P : forall t, reflect (exists i : Iirr K2, t = 'Ind[L2, K2] 'xi_i) (t \in zi2).

Let S1 := filter1 zi1 ('Ind[L1, K1] '1_K1).
Let S2 := filter1 zi2 ('Ind[L2, K2] '1_K2).

Hypothesis coherentS1 : my_coherent L1 G S1 A1 (Dade ddA1) nu1.
Hypothesis coherentS2 : my_coherent L2 G S2 A2 (Dade ddA2) nu2.

Let e1 := #|L1 : K1|%:R : algC.
Let e2 := #|L2 : K2|%:R : algC.

Hypotheses (chi1S1 : chi1 \in S1) (chi2S2 : chi2 \in S2).
Hypotheses (irr_chi1 : chi1 \in irr L1) (irr_chi2 : chi2 \in irr L2).
Hypotheses (chi1_1 : chi1 1%g = e1) (chi2_1 : chi2 1%g = e2).

Let beta1 := ('Ind[L1, K1] '1_K1 - chi1)^\tau1.
Let beta2 := ('Ind[L2, K2] '1_K2 - chi2)^\tau2.



(************************************)

Let sA1L1 : A1 \subset L1. Proof. by have [/subsetD1P[]] := ddA1. Qed.
Let nA1L1 : L1 \subset 'N(A1). Proof. by have [_ /subsetIP[]] := ddA1. Qed.
Let sL1G : L1 \subset G. Proof. by have [_ /subsetIP[]] := ddA1. Qed.
Let sK1L1 : K1 \subset L1. Proof. by move/andP: nK1L1 => []. Qed.

Let nu1_to : {in 'Z[S1], forall f, nu1 f \in 'Z[irr G]}.
Proof. by case: coherentS1 => []. Qed.
Let nu1_isom : {in 'Z[S1] &, isometry L1 G nu1}.
Proof. by case: coherentS1 => []. Qed.
Let nu1_tau : {in 'Z[S1, A1], forall f, nu1 f = f^\tau1}.
Proof. by case: coherentS1 => []. Qed.

Let inS1_C f : f \in S1 -> f \in 'CF(L1, K1).
Proof.
rewrite mem_filter => /andP [_]; case/zi1P => r ->.
by rewrite memcE memc_induced ?support_induced ?memc_irr.
Qed.

Let uniq_subset_zi1_ortho (S : seq {cfun gT}) : 
  {subset S <= zi1} -> uniq S -> pairwise_orthogonal L1 S.
Proof.
move => sSzi uniqS.
apply/pairwise_orthogonalP; split.
- move => f /sSzi; case/zi1P => r ->.
  by rewrite memc_induced ?memc_irr.
- rewrite cons_uniq uniqS andbT.
  apply: contraT; rewrite negbK => /sSzi /zi1P [r] /esym/eqP.
  rewrite cinduced_eq0 ?is_char_irr // => /eqP/cfunP /(_ 1%g) xi1_0.
  by move: (irr1_neq0 r); rewrite xi1_0 cfunE eqxx.
move => f g /sSzi/zi1P [r ->] /sSzi/zi1P [t ->].
have := cconjugates_irr_induced r t nK1L1.
by case: (_ \in _) => //; move ->; rewrite eqxx.
Qed.


Let S1_pairwise_ortho : pairwise_orthogonal L1 S1.
Proof.
rewrite uniq_subset_zi1_ortho ?filter_uniq //.
by move => f; rewrite mem_filter => /andP [].
Qed.


Let freeS1 : free S1. Proof. exact: (orthogonal_free S1_pairwise_ortho). Qed.

Let supportS1 f : f \in S1 -> support f \subset K1.
Proof. by move/inS1_C; rewrite memcE => /andP []. Qed.

Let inS1_ZS1 f : f \in S1 -> f \in 'Z[S1].
Proof. by move => fS; apply: memv_vchar. Qed.

Let inS1_ZS1K1 f : f \in S1 -> f \in 'Z[S1, K1].
Proof. by move => fS; rewrite vchar_split inS1_ZS1 ?supportS1. Qed.

Let beta1_ZA1 : 'Ind[L1, K1] '1_K1 - chi1 \in 'Z[irr L1, A1].
Proof.
rewrite vchar_split; apply/andP; split.
  rewrite vchar_sub ?vchar_char ?is_char_induced ?cfuni_xi0 ?is_char_irr //.
  by case/irrIP: irr_chi1 => r <-; exact: is_char_irr.
rewrite A1K1; apply/subsetP => x; apply: contraR.
rewrite !inE cinduced_1 // !cfunE negb_and negbK -!/fcf.
case/orP => [/eqP -> | xnK].
  by rewrite chi1_1 in_group [_ *: _]mulr1 subrr.
by rewrite /fcf (supportP (supportS1 chi1S1) _ xnK) (negPf xnK) [_ *: _]mulr0 subr0.
Qed.

Let beta1_Z : beta1 \in 'Z[irr G].
Proof. exact: Dade_vchar. Qed.

Let cchi1_n_chi1 : (chi1^*)%CH != chi1.
Proof.
case/irrIP: irr_chi1 => r chi_r.
rewrite -chi_r odd_eq_conj_irr1 ?(oddSg sL1G) // chi_r.
case: (boolP (K1 :==: L1)) => [/eqP KL |].
  move: chi1S1; rewrite mem_filter => /andP [chi_n_1 _].
  by move: chi_n_1; rewrite cinduced_1 //= KL indexgg scale1r.
apply: contra => /eqP/cfunP/(_ 1%g); rewrite chi1_1 cfunE in_group.
by move/eqP; rewrite -eqN_eqC indexg_eq1 eqEsubset sK1L1 => ->.
Qed.


Let cchi1_inS1 : (chi1^*)%CH \in S1.
Proof.
have := chi1S1; rewrite !mem_filter /= => /andP [chi1_n_1].
case/zi1P => r chi1_ind; apply/andP; split.
  apply: contra chi1_n_1 => /eqP cchi1_1.
  have := cfun_conjCK chi1.
  by rewrite cchi1_1 cinduced_conjC cfun_conjC1 => <-.
apply/zi1P; case/irrIP: (irr_conjC r) => t tr.
by exists t; rewrite chi1_ind cinduced_conjC tr.
Qed.


Let norm_chi1 : '[chi1, chi1]_L1 = 1.
Proof. by case/irrIP: irr_chi1 => r <-; rewrite irr_orthonormal eqxx. Qed.

Let norm_cchi1 : '[(chi1^*)%CH, (chi1^*)%CH]_L1 = 1.
Proof. by rewrite cfun_conjC_inner norm_chi1 conjC1. Qed.


Let chi1_cchi1_ortho : '[chi1, (chi1^*)%CH]_L1 = 0.
Proof.
move: cchi1_n_chi1; case/irrIP: irr_chi1 => r <-.
case/irrIP: (irr_conjC r) => t <-; rewrite irr_orthonormal.
by case: (boolP (r == t)) => // /eqP ->; rewrite eqxx.
Qed.


Let diff_chi1_ZS1A1 : chi1 - (chi1^*)%CH \in 'Z[S1, A1].
Proof.
rewrite vchar_split ?vchar_sub ?inS1_ZS1 // andTb.
rewrite A1K1; apply/subsetP => x; apply: contraR.
rewrite !inE !cfunE negb_and negbK -!/fcf.
case/orP => [/eqP -> | xnK]; first by rewrite chi1_1 conjC_nat subrr.
by rewrite /fcf (supportP (supportS1 chi1S1) _ xnK) conjC0 subr0.
Qed.

Let diff_chi1_irrL1A1 : chi1 - (chi1^*)%CH \in 'Z[irr L1, A1].
Proof.
rewrite vchar_split ?(support_vchar diff_chi1_ZS1A1) andbT.
by rewrite vchar_sub ?vchar_char ?is_char_conjC //;
  case/irrIP: irr_chi1 => r <-; rewrite is_char_irr.
Qed.



(*********************************)
Let sA2L2 : A2 \subset L2. Proof. by have [/subsetD1P[]] := ddA2. Qed.
Let nA2L2 : L2 \subset 'N(A2). Proof. by have [_ /subsetIP[]] := ddA2. Qed.
Let sL2G : L2 \subset G. Proof. by have [_ /subsetIP[]] := ddA2. Qed.
Let sK2L2 : K2 \subset L2. Proof. by move/andP: nK2L2 => []. Qed.

Let nu2_to : {in 'Z[S2], forall f, nu2 f \in 'Z[irr G]}.
Proof. by case: coherentS2 => []. Qed.
Let nu2_isom : {in 'Z[S2] &, isometry L2 G nu2}.
Proof. by case: coherentS2 => []. Qed.
Let nu2_tau : {in 'Z[S2, A2], forall f, nu2 f = f^\tau2}.
Proof. by case: coherentS2 => []. Qed.

Let inS2_C f : f \in S2 -> f \in 'CF(L2, K2).
Proof.
rewrite mem_filter => /andP [_]; case/zi2P => r ->.
by rewrite memcE memc_induced ?support_induced ?memc_irr.
Qed.

Let uniq_subset_zi2_ortho (S : seq {cfun gT}) : 
  {subset S <= zi2} -> uniq S -> pairwise_orthogonal L2 S.
Proof.
move => sSzi uniqS.
apply/pairwise_orthogonalP; split.
- move => f /sSzi; case/zi2P => r ->.
  by rewrite memc_induced ?memc_irr.
- rewrite cons_uniq uniqS andbT.
  apply: contraT; rewrite negbK => /sSzi /zi2P [r] /esym/eqP.
  rewrite cinduced_eq0 ?is_char_irr // => /eqP/cfunP /(_ 1%g) xi1_0.
  by move: (irr1_neq0 r); rewrite xi1_0 cfunE eqxx.
move => f g /sSzi/zi2P [r ->] /sSzi/zi2P [t ->].
have := cconjugates_irr_induced r t nK2L2.
by case: (_ \in _) => //; move ->; rewrite eqxx.
Qed.


Let S2_pairwise_ortho : pairwise_orthogonal L2 S2.
Proof.
rewrite uniq_subset_zi2_ortho ?filter_uniq //.
by move => f; rewrite mem_filter => /andP [].
Qed.


Let freeS2 : free S2. Proof. exact: (orthogonal_free S2_pairwise_ortho). Qed.

Let supportS2 f : f \in S2 -> support f \subset K2.
Proof. by move/inS2_C; rewrite memcE => /andP []. Qed.

Let inS2_ZS2 f : f \in S2 -> f \in 'Z[S2].
Proof. by move => fS; apply: memv_vchar. Qed.

Let inS2_ZS2K2 f : f \in S2 -> f \in 'Z[S2, K2].
Proof. by move => fS; rewrite vchar_split inS2_ZS2 ?supportS2. Qed.

Let beta2_ZA2 : 'Ind[L2, K2] '1_K2 - chi2 \in 'Z[irr L2, A2].
Proof.
rewrite vchar_split; apply/andP; split.
  rewrite vchar_sub ?vchar_char ?is_char_induced ?cfuni_xi0 ?is_char_irr //.
  by case/irrIP: irr_chi2 => r <-; exact: is_char_irr.
rewrite A2K2; apply/subsetP => x; apply: contraR.
rewrite !inE cinduced_1 // !cfunE negb_and negbK -!/fcf.
case/orP => [/eqP -> | xnK].
  by rewrite chi2_1 in_group [_ *: _]mulr1 subrr.
by rewrite /fcf (supportP (supportS2 chi2S2) _ xnK) (negPf xnK) [_ *: _]mulr0 subr0.
Qed.

Let beta2_Z : beta2 \in 'Z[irr G].
Proof. exact: Dade_vchar. Qed.

Let cchi2_n_chi2 : (chi2^*)%CH != chi2.
Proof.
case/irrIP: irr_chi2 => r chi_r.
rewrite -chi_r odd_eq_conj_irr1 ?(oddSg sL2G) // chi_r.
case: (boolP (K2 :==: L2)) => [/eqP KL |].
  move: chi2S2; rewrite mem_filter => /andP [chi_n_1 _].
  by move: chi_n_1; rewrite cinduced_1 //= KL indexgg scale1r.
apply: contra => /eqP/cfunP/(_ 1%g); rewrite chi2_1 cfunE in_group.
by move/eqP; rewrite -eqN_eqC indexg_eq1 eqEsubset sK2L2 => ->.
Qed.


Let cchi2_inS2 : (chi2^*)%CH \in S2.
Proof.
have := chi2S2; rewrite !mem_filter /= => /andP [chi2_n_1].
case/zi2P => r chi2_ind; apply/andP; split.
  apply: contra chi2_n_1 => /eqP cchi2_1.
  have := cfun_conjCK chi2.
  by rewrite cchi2_1 cinduced_conjC cfun_conjC1 => <-.
apply/zi2P; case/irrIP: (irr_conjC r) => t tr.
by exists t; rewrite chi2_ind cinduced_conjC tr.
Qed.

Let norm_chi2 : '[chi2, chi2]_L2 = 1.
Proof. by case/irrIP: irr_chi2 => r <-; rewrite irr_orthonormal eqxx. Qed.


Let norm_cchi2 : '[(chi2^*)%CH, (chi2^*)%CH]_L2 = 1.
Proof. by rewrite cfun_conjC_inner norm_chi2 conjC1. Qed.

Let chi2_cchi2_ortho : '[chi2, (chi2^*)%CH]_L2 = 0.
Proof.
move: cchi2_n_chi2; case/irrIP: irr_chi2 => r <-.
case/irrIP: (irr_conjC r) => t <-; rewrite irr_orthonormal.
by case: (boolP (r == t)) => // /eqP ->; rewrite eqxx.
Qed.


Let diff_chi2_ZS2A2 : chi2 - (chi2^*)%CH \in 'Z[S2, A2].
Proof.
rewrite vchar_split ?vchar_sub ?inS2_ZS2 // andTb.
rewrite A2K2; apply/subsetP => x; apply: contraR.
rewrite !inE !cfunE negb_and negbK -!/fcf.
case/orP => [/eqP -> | xnK]; first by rewrite chi2_1 conjC_nat subrr.
by rewrite /fcf (supportP (supportS2 chi2S2) _ xnK) conjC0 subr0.
Qed.


Let diff_chi2_irrL2A2 : chi2 - (chi2^*)%CH \in 'Z[irr L2, A2].
Proof.
rewrite vchar_split ?(support_vchar diff_chi2_ZS2A2) andbT.
by rewrite vchar_sub ?vchar_char ?is_char_conjC //;
  case/irrIP: irr_chi2 => r <-; rewrite is_char_irr.
Qed.



(**********************************)

Let d1 := beta1 - '1_G + nu1 chi1.
Let d2 := beta2 - '1_G + nu2 chi2.


Let d1_conjC : (d1^*)%CH = d1.
Proof.
apply/eqP; rewrite -subr_eq0 /d1 /d2.
rewrite rmorphD rmorph_sub /= cfun_conjC1 !oppr_add !addrA !subr_eq add0r.
rewrite addrAC [in X in _ == X]addrAC; apply/eqP; congr (_ - _).
apply/eqP; rewrite -subr_eq addrAC eq_sym -subr_eq eq_sym.
rewrite Dade_conjC ?memc_vchar //.
rewrite -linear_sub rmorph_sub /= cinduced_conjC cfun_conjC1.
rewrite addrAC oppr_add addrA subrr opprK add0r.
pose S := [:: chi1; (chi1^*)%CH].
have sSS1 : {subset S <= S1}.
  by move => f; rewrite !inE; case/orP => /eqP ->.
have freeS : free S.
  apply: (@orthogonal_free _ L1 S).
  rewrite uniq_subset_zi1_ortho ?cons_uniq ?inE //=; last by rewrite eq_sym cchi1_n_chi1.
  by move => f /sSS1; rewrite mem_filter => /andP [].
have sZS_ZS1 : {subset 'Z[S] <= 'Z[S1]} by apply: vchar_subset.
have sizeS : (1 < size S)%N by [].
have irrS: {subset S <= irr L1}.
  move => f; rewrite !inE; case/irrIP: irr_chi1 => r <-.
  by case/orP => /eqP ->; rewrite ?irr_conjC ?irr_xi.
have ZA : 'Z[S, L1^#] =i 'Z[S, A1].
  move => f; rewrite vchar_split [in X in _ = X]vchar_split.
  apply/andP/andP => [] []; last first.
    move => -> fA1; apply/andP; rewrite (subset_trans fA1) // A1K1.
    by apply/subsetP => x; rewrite !inE => /andP [] -> /(subsetP sK1L1) ->.
  move => fZ fL; rewrite fZ; apply/andP; rewrite andTb.
  apply/subsetP => x; apply: contraR.
  rewrite A1K1 !inE negb_and negbK; case/orP => [/eqP -> | xnK].
    by rewrite (supportP fL) // !inE negb_and negbK eqxx orTb.
  have /coord_span/cfunP/(_ x) := span_vchar fZ.
  rewrite sum_cfunE cfunE => -> /=; apply/eqP.
  apply: big1 => i _; apply/eqP.
  rewrite cfunE mulf_eq0; apply/orP; right.
  have: S`_i \in S by exact: mem_nth.
  by rewrite !inE; case/orP => /eqP ->; rewrite (supportP (supportS1 _) _ xnK).
rewrite (@pf59a_conjC _ _ _ _ _ ddA1 S nu1 chi1) //.
- rewrite -nu1_tau; first by rewrite raddf_sub.
  rewrite vchar_split ?vchar_sub ?inS1_ZS1 // andTb.
  apply/subsetP => x; apply: contraR.
  rewrite A1K1 !inE !cfunE negb_and negbK.
  case/orP => [/eqP -> | xnK]; first by rewrite -/fcf chi1_1 conjC_nat subrr.
  by rewrite !/fcf (supportP (supportS1 _) _ xnK) // conjC0 subr0.
- move => f; rewrite !inE; case/orP => /eqP ->; first by rewrite eqxx orbT.
  by rewrite cfun_conjCK eqxx orTb.
- by move => f /sZS_ZS1/nu1_to.
- by move => f g /sZS_ZS1 fS1 /sZS_ZS1 gS1; rewrite nu1_isom.
- move => f; have sZA1 := vchar_subset freeS freeS1 sSS1.
  by move/sZA1 => fZA1; rewrite nu1_tau.
by rewrite !inE eqxx orTb.
Qed.


Let d1_ortho1 : '[d1, '1_G]_G = 0.
Proof.
rewrite !inner_prodDl inner_prodNl.
rewrite (dot_beta_1 ddA1 nK1L1 A1K1 zi1_uniq) //.
rewrite (pf78a1 nK1L1 A1K1 zi1_uniq _ coherentS1 chi1S1) //.
by rewrite cfuni_xi0 irr_orthonormal eqxx subrr addr0.
Qed.


(******)

Let d2_conjC : (d2^*)%CH = d2.
Proof.
apply/eqP; rewrite -subr_eq0 /d1 /d2.
rewrite rmorphD rmorph_sub /= cfun_conjC1 !oppr_add !addrA !subr_eq add0r.
rewrite addrAC [in X in _ == X]addrAC; apply/eqP; congr (_ - _).
apply/eqP; rewrite -subr_eq addrAC eq_sym -subr_eq eq_sym.
rewrite Dade_conjC ?memc_vchar //.
rewrite -linear_sub rmorph_sub /= cinduced_conjC cfun_conjC1.
rewrite addrAC oppr_add addrA subrr opprK add0r.
pose S := [:: chi2; (chi2^*)%CH].
have sSS2 : {subset S <= S2}.
  by move => f; rewrite !inE; case/orP => /eqP ->.
have freeS : free S.
  apply: (@orthogonal_free _ L2 S).
  rewrite uniq_subset_zi2_ortho ?cons_uniq ?inE //=; last by rewrite eq_sym cchi2_n_chi2.
  by move => f /sSS2; rewrite mem_filter => /andP [].
have sZS_ZS2 : {subset 'Z[S] <= 'Z[S2]} by apply: vchar_subset.
have sizeS : (1 < size S)%N by [].
have irrS: {subset S <= irr L2}.
  move => f; rewrite !inE; case/irrIP: irr_chi2 => r <-.
  by case/orP => /eqP ->; rewrite ?irr_conjC ?irr_xi.
have ZA : 'Z[S, L2^#] =i 'Z[S, A2].
  move => f; rewrite vchar_split [in X in _ = X]vchar_split.
  apply/andP/andP => [] []; last first.
    move => -> fA; apply/andP; rewrite (subset_trans fA) // A2K2.
    by apply/subsetP => x; rewrite !inE => /andP [] -> /(subsetP sK2L2) ->.
  move => fZ fL; rewrite fZ; apply/andP; rewrite andTb.
  apply/subsetP => x; apply: contraR.
  rewrite A2K2 !inE negb_and negbK; case/orP => [/eqP -> | xnK].
    by rewrite (supportP fL) // !inE negb_and negbK eqxx orTb.
  have /coord_span/cfunP/(_ x) := span_vchar fZ.
  rewrite sum_cfunE cfunE => -> /=; apply/eqP.
  apply: big1 => i _; apply/eqP.
  rewrite cfunE mulf_eq0; apply/orP; right.
  have: S`_i \in S by exact: mem_nth.
  by rewrite !inE; case/orP => /eqP ->; rewrite (supportP (supportS2 _) _ xnK).
rewrite (@pf59a_conjC _ _ _ _ _ ddA2 S nu2 chi2) //.
- rewrite -nu2_tau; first by rewrite raddf_sub.
  rewrite vchar_split ?vchar_sub ?inS2_ZS2 // andTb.
  apply/subsetP => x; apply: contraR.
  rewrite A2K2 !inE !cfunE negb_and negbK.
  case/orP => [/eqP -> | xnK]; first by rewrite -/fcf chi2_1 conjC_nat subrr.
  by rewrite !/fcf (supportP (supportS2 _) _ xnK) // conjC0 subr0.
- move => f; rewrite !inE; case/orP => /eqP ->; first by rewrite eqxx orbT.
  by rewrite cfun_conjCK eqxx orTb.
- by move => f /sZS_ZS2/nu2_to.
- by move => f g /sZS_ZS2 fS2 /sZS_ZS2 gS2; rewrite nu2_isom.
- move => f; have sZA2 := vchar_subset freeS freeS2 sSS2.
  by move/sZA2 => fZA2; rewrite nu2_tau.
by rewrite !inE eqxx orTb.
Qed.


Let d2_ortho1 : '[d2, '1_G]_G = 0.
Proof.
rewrite !inner_prodDl inner_prodNl.
rewrite (dot_beta_1 ddA2 nK2L2 A2K2 zi2_uniq) //.
rewrite (pf78a1 nK2L2 A2K2 zi2_uniq _ coherentS2 chi2S2) //.
by rewrite cfuni_xi0 irr_orthonormal eqxx subrr addr0.
Qed.



Let beta12_ortho : '[beta1, beta2]_G = 0.
Proof.
rewrite (@memc_class_ortho _ G Atau1) //.
  by rewrite Dade_cfunS ?memc_vchar.
have: beta2 \in 'CF(G, Atau2) by rewrite Dade_cfunS ?memc_vchar.
rewrite memcE [in X in _ -> X]memcE => /andP [sA] ->; rewrite andbT.
apply: (subset_trans sA).
by rewrite subsetD disjoint_sym disjointA Dade_support_sub.
Qed.


Let nu_chi12_ortho : '[nu1 chi1, nu2 chi2]_G = 0.
Proof.
pose ab := [:: nu1 chi1; nu1 ((chi1^*)%CH)].
pose cd := [:: nu2 chi2; nu2 ((chi2^*)%CH)].
have ab_ortho : orthonormal G ab.
  have nu1_n: nu1 chi1 != nu1 ((chi1^*)%CH).
    apply: contraR cchi1_n_chi1; rewrite negbK -subr_eq0 -raddf_sub.
    rewrite -(@inner_prod0 _ G) ?nu1_isom ?vchar_sub ?inS1_ZS1 //.
      by rewrite inner_prod0 ?memv_sub ?(memcW (inS1_C _)) // subr_eq0 eq_sym.
    by rewrite memc_Zirr ?nu1_to ?vchar_sub ?inS1_ZS1.
  apply/orthonormalP; split.
  - by move => f; rewrite !inE; case/orP => /eqP ->; rewrite memc_Zirr ?nu1_to ?inS1_ZS1.
  - by rewrite !cons_uniq !inE in_nil /= andbT.
  move => f g; rewrite !inE; do 2 case/orP => /eqP ->; 
    rewrite ?eqxx ?(negPf nu1_n) ?nu1_isom ?inS1_ZS1 //.
  by rewrite eq_sym inner_conj (negPf nu1_n) chi1_cchi1_ortho conjC0.
have cd_ortho : orthonormal G cd.
  have nu2_n: nu2 chi2 != nu2 ((chi2^*)%CH).
    apply: contraR cchi2_n_chi2; rewrite negbK -subr_eq0 -raddf_sub.
    rewrite -(@inner_prod0 _ G) ?nu2_isom ?vchar_sub ?inS2_ZS2 //.
      by rewrite inner_prod0 ?memv_sub ?(memcW (inS2_C _)) // subr_eq0 eq_sym.
    by rewrite memc_Zirr ?nu2_to ?vchar_sub ?inS2_ZS2.
  apply/orthonormalP; split.
  - by move => f; rewrite !inE; case/orP => /eqP ->; rewrite memc_Zirr ?nu2_to ?inS2_ZS2.
  - by rewrite !cons_uniq !inE in_nil /= andbT.
  move => f g; rewrite !inE; do 2 case/orP => /eqP ->; 
    rewrite ?eqxx ?(negPf nu2_n) ?nu2_isom ?inS2_ZS2 //.
  by rewrite eq_sym inner_conj (negPf nu2_n) chi2_cchi2_ortho conjC0.
have ab_cdZ: {subset ab <= 'Z[irr G]} /\ {subset cd <= 'Z[irr G]}.
  by split; move => f; rewrite 2!inE; case/orP => /eqP ->; 
    rewrite ?nu1_to ?nu2_to ?inS1_ZS1 ?inS2_ZS2.
have ortho_ab_cd : orthonormal G ab && orthonormal G cd by rewrite ab_ortho cd_ortho.
have /(_ 1 1):= vchar_pairs_orthonormal ab_cdZ ortho_ab_cd.
have ->: isRealC 1.
  have ->: 1 = ((1%:R) : algC) by [].
  by rewrite isZC_real ?isZC_nat.
rewrite nonzero1r !andbT !scale1r -!raddf_sub.
rewrite [nu1 (_ - _)]nu1_tau ?[nu2 (_ - _)]nu2_tau //.
rewrite -!/fcf !Dade1 eqxx.
set prod := '[_, _]_G.
have ->: prod == 0.
  rewrite /prod (@memc_class_ortho _ G Atau1) //.
    by rewrite Dade_cfunS ?memc_vchar.
  have: (chi2 - (chi2^*)%CH)^\tau2 \in 'CF(G, Atau2) by rewrite Dade_cfunS ?memc_vchar.
  rewrite memcE [in X in _ -> X]memcE => /andP [sA] ->; rewrite andbT.
  apply: (subset_trans sA).
  by rewrite subsetD disjoint_sym disjointA Dade_support_sub.
move => /(_ isT isT) /orthonormalP [] _ => uniq_abcd.
move => /(_ (nu1 chi1) (nu2 chi2)); rewrite !inE !eqxx !orbT /=.
move => /(_ isT isT) ->; move: uniq_abcd => /=.
by rewrite !inE !negb_or => /andP [] /and3P [] => _ /negPf ->.
Qed.


Let equation1 : '[beta1, nu2 chi2]_G + '[beta2, nu1 chi1]_G = 1 + '[d1, d2]_G.
Proof.
rewrite !inner_prodDl !inner_prodDr !inner_prodNl !inner_prodNr.
rewrite beta12_ortho (dot_beta_1 ddA1 nK1L1 A1K1 zi1_uniq) // nu_chi12_ortho.
rewrite !addrA !addr0 subrr add0r -!addrA; congr (_ + _); symmetry.
rewrite inner_conj (dot_beta_1 ddA2 nK2L2 A2K2 zi2_uniq) //.
rewrite {1 2}cfuni_xi0 irr_orthonormal eqxx opprK !addrA conjC1 addNr add0r.
rewrite inner_conj (pf78a1 nK2L2 _ zi2_uniq _ coherentS2 chi2S2) //.
rewrite (pf78a1 nK1L1 _ zi1_uniq _ coherentS1 chi1S1) //.
rewrite conjC0 oppr0 add0r addr0 inner_conj isZC_conj //.
by rewrite isZC_inner_Zirr ?nu1_to ?inS1_ZS1 ?Dade_vchar.
Qed.



Let I0 := filter [pred xi | (xi^*)%CH == xi] (irr G).
Let I1 := map (tnth (irr G)) (filter [pred i : Iirr G | (i < conj_idx i)%N] (enum (Iirr G))).
Let I2 := map (@cfun_conjC gT) I1.


Let irr_uniq : uniq (irr G).
Proof. by rewrite uniq_free ?(free_is_basis (is_basis_irr _)). Qed.

Let I0_uniq : uniq I0. Proof. exact: filter_uniq. Qed.
Let I1_uniq : uniq I1. 
Proof. 
by rewrite map_inj_uniq ?filter_uniq -?enumT ?enum_uniq //; exact: xi_inj.
Qed.
Let I2_uniq : uniq I2.
Proof. by rewrite map_inj_uniq //; apply: inv_inj; exact: cfun_conjCK. Qed.

Let I1_prop xi : xi \in I1 -> (xi^*)%CH \notin I1.
Proof.
case/mapP => i; rewrite mem_filter /= => /andP [] i_lt_conj _ ->.
apply: contraL i_lt_conj; rewrite -conj_idxE.
case/mapP => j; rewrite mem_filter /= => /andP [] j_lt_conj _ /xi_inj ij.
move: j_lt_conj; rewrite ij -{2}ij conj_idxK.
by rewrite -leqNgt [(j <= i)%N]leq_eqVlt => ->; rewrite orbT.
Qed.

Let I1_I0_disjoint : [predI I0 & I1] =1 pred0.
Proof.
move => xi /=.
case xiI0: (_ \in I0); rewrite (andTb, andFb) //.
case xiI1: (_ \in I1) => //; move: xiI0 (I1_prop xiI1).
by rewrite mem_filter /= => /andP [] /eqP ->; rewrite xiI1.
Qed.

Let I1_I2_disjoint : [predI I1 & I2] =1 pred0.
Proof.
move => xi /=; case xiI1: (_ \in I1); rewrite (andTb, andFb) //.
case xiI2: (_ \in I2) => //.
by case/mapP: xiI2 xiI1 => f /I1_prop fnI1 ->; rewrite (negPf fnI1).
Qed.

Let I0_I2_disjoint : [predI I0 & I2] =1 pred0.
Proof.
move => xi /=; case xiI0: (_ \in I0); rewrite (andTb, andFb) //.
case xiI2: (_ \in I2) => //.
case/mapP: xiI2 xiI0 => f fI1 ->; rewrite mem_filter /= => /andP [].
rewrite cfun_conjCK => /eqP ffc.
by move/I1_prop: (fI1); rewrite -ffc fI1.
Qed.


Let uniq_catI : uniq (I0 ++ I1 ++ I2).
Proof.
rewrite !cat_uniq I0_uniq I1_uniq I2_uniq has_cat negb_or /=.
have has_disj (I J : seq {cfun gT}) : ([predI I & J] =1 pred0) -> ~~ has (mem I) J.
  move => disj; case h: (has _ _) => //.
  case/hasP: h => x; rewrite inE => xJ xI.
  by move: (disj x) => /=; rewrite xJ xI andbT.
by rewrite !has_disj.
Qed.


Let irr_eq_catI : irr G =i I0 ++ I1 ++ I2.
Proof.
move => xi; rewrite !mem_cat; apply/idP/idP; last first.
  case/or3P; first by rewrite mem_filter => /andP [].
    by case/mapP => i _ ->; exact: irr_xi.
  by case/mapP => f; case/mapP => i _ -> ->; exact: irr_conjC.
case/irrIP => i <-.
case: (ltngtP i (conj_idx i)) => i_idx.
- apply/orP; right; apply/orP; left; apply/mapP.
  by exists i => //; rewrite mem_filter /= i_idx andTb mem_enum.
- apply/orP; right; apply/orP; right; apply/mapP.
  exists (('xi_i)^*)%CH; rewrite ?cfun_conjCK //.
  rewrite -conj_idxE; apply/mapP.
  by exists (conj_idx i) => //; rewrite mem_filter /= conj_idxK i_idx mem_enum.
by apply/orP; left; rewrite mem_filter irr_xi andbT /= -conj_idxE -(ord_inj i_idx).
Qed.


Let perm_eq_irr_catI : perm_eq (irr G) (I0 ++ I1 ++ I2).
Proof. exact: uniq_perm_eq. Qed.


Let dot_d12_even : exists2 a, isZC a & '[d1, d2]_G = a + a.
Proof.
have /andP [d1Z d2Z]: (d1 \in 'Z[irr G]) && (d2 \in 'Z[irr G]).
  by rewrite !vchar_add // ?vchar_opp ?cfuni_xi0 ?vchar_irr // (nu2_to, nu1_to) ?inS1_ZS1 ?inS2_ZS2.
have ->: '[d1, d2]_G = \sum_(xi <- irr G) '[d1, xi]_G * '[d2, xi]_G.
  symmetry; rewrite (inner_prod_vchar d1Z d2Z) (big_nth 0) big_mkord.
  rewrite size_tuple; apply: eq_bigr => i _.
  by rewrite (tnth_nth 0).
rewrite (eq_big_perm _ perm_eq_irr_catI) !big_cat /=.
set sum0 := \sum_(i <- I0) _.
set sum1 := \sum_(i <- I1) _.
set sum2 := \sum_(i <- I2) _.
exists sum1.
  rewrite /sum1 big_seq_cond; apply: isZC_sum => f /andP [].
  case/mapP => i _ -> _.
  by rewrite isZC_mul ?(isZC_inner_prod_vchar i d1Z) ?(isZC_inner_prod_vchar i d2Z).
have ->: sum0 = 0.
  rewrite /sum0 big1_seq // => f /andP [] _.
  rewrite mem_filter /= => /andP [] cf_f; case/irrIP => i f_xi.
  move: cf_f; rewrite -f_xi odd_eq_conj_irr1 // => /eqP ->.
  by rewrite d1_ortho1 d2_ortho1 mulr0.
suff ->: sum2 = sum1 by rewrite add0r.
rewrite /sum2 /sum1 big_map big_seq_cond [in X in _ = X]big_seq_cond.
apply: eq_bigr => f /andP []; case/mapP => i _ -> _.
do 2 rewrite inner_conj -cfun_conjC_inner cfun_conjCK inner_conj mulrC.
rewrite d1_conjC d2_conjC !isZC_conj //.
  by rewrite (isZC_inner_prod_vchar i d2Z).
by rewrite (isZC_inner_prod_vchar i d1Z).
Qed.




Lemma pf79 : ('[beta1, nu2 chi2]_G != 0) || ('[beta2, nu1 chi1]_G != 0).
Proof.
move/eqP: equation1; apply: contraTT; rewrite negb_or !negbK.
move/andP => [] /eqP -> /eqP ->; rewrite addr0.
case: dot_d12_even => a; rewrite isZCE; case/orP => /isNatCP [m].
  by move => -> ->; rewrite -natr_add -(natr_add _ 1) eq_sym -neq0N_neqC.
move/eqP; rewrite eqr_oppC => /eqP -> ->.
rewrite -!mulNrn -mulrn_addr mulNrn eq_sym subr_eq0 -(eqN_eqC 1).
have : odd 1 by [].
apply: contraL => /eqP ->.
by rewrite addnn odd_double.
Qed.

End PF79.




(*************************)
Section PF7_10.

Hypothesis oddG : odd #|G|.

Variable k : nat.
(* L = K ><| H, Frobenius with kernel K *)
Variables (L K H : k.-tuple {group gT}).


Local Notation "'L_ i" := (tnth L i)
  (at level 2).
Local Notation "'K_ i" := (tnth K i)
  (at level 2).

Hypothesis k_ge2: (k >= 2)%N.
Hypothesis sLG : forall i : 'I_k, 'L_i \subset G.
Hypothesis frobeniusL : 
  forall i : 'I_k, [Frobenius 'L_i = 'K_i ><| (tnth H i)].
Hypothesis normedTI_KL :
  forall i : 'I_k, normedTI ('K_i)^# G 'L_i.
Hypothesis card_coprime :
  forall i j : 'I_k, i != j -> coprime #|'K_i| #|'K_j|.

Let G0 := G :\: \bigcup_(i < k) class_support ('K_i^#) G.

(* Connection with the Dade hypothesis *)

Let nKL i : 'K_i <| 'L_i.
Proof. by case/Frobenius_context: (frobeniusL i); case/sdprod_context. Qed.

Let sKL i : 'K_i \subset 'L_i.
Proof. by move/andP: (nKL i) => []. Qed.

Let DadeH (a : gT) : {group gT} := [group of [1 gT]].

Let ddA i : Dade_hypothesis G 'L_i DadeH ('K_i)^#.
Proof.
apply/Dade_TI_P => //.
  rewrite subsetD1 !inE negb_and negbK eqxx orTb andbT.
  have sKG: 'K_i \subset G by rewrite (subset_trans (sKL i)) ?sLG.
  by rewrite (subset_trans _ sKG) // subsetDl.
case/Frobenius_context: (frobeniusL i) => _ Kn1 _ _ _.
apply: contra Kn1 => /eqP KD1.
by rewrite -(@setD1K _ 1%g 'K_i) ?in_group // KD1 setUC set0U.
Qed.

Local Notation tau i := (Dade (ddA i)).
Local Notation rho i := (rho_fun ('K_i)^# DadeH).
Local Notation Atau i := (Dade_support (ddA i)).

Let Dade_supp i : Atau i = class_support ('K_i)^# G.
Proof.
rewrite /Dade_support class_supportEl.
apply: eq_bigr => x _.
by rewrite /Dade_support1 /DadeH mul1g class_supportEl big_set1.
Qed.


Let G0_def : G0 = G :\: \bigcup_(i < k) Atau i.
Proof. by congr (_ :\: _); apply: eq_bigr => i; rewrite Dade_supp. Qed.


(* Local definitions *)

Let h (i : 'I_k) := #|'K_i|%:R : algC.
Let e (i : 'I_k) := #|'L_i : 'K_i|%:R : algC.


Let zi (i : 'I_k) := undup (map (cinduced 'L_i 'K_i) (irr 'K_i)).
Let S (i : 'I_k) := filter1 (zi i) ('Ind['L_i, 'K_i] '1_('K_i)).
Let chi (i : 'I_k) := oapp (tnth (in_tuple (S i))) 0 
  [pick j : (ordinal (size (S i))) | (S i)`_j 1%g == e i].

Let i1 := arg_min (Ordinal k_ge2) predT (fun i => #|'K_i|).

Let i1_prop i : h i1 <= h i.
Proof.
rewrite -leq_leC.
have := @arg_minP _ (Ordinal k_ge2) predT (fun i => #|'K_i|).
by rewrite -/i1 => /(_ isT); case => j _ /(_ i isT).
Qed.


(*
Let chiS i : chi i \in S i.
Proof.
rewrite /chi; case: pickP => /=.
  move => j _.
  suff: tnth (in_tuple (S i)) j \in in_tuple (S i) by [].
  by apply/tnthP; exists j.
*)


(*************************)
(* Additional hypotheses *)
(*************************)
(* This follows from Isaacs 6.34 *)
Hypothesis sSirrL : forall i : 'I_k, {subset S i <= irr 'L_i}.

Hypothesis chi1 : forall i : 'I_k, chi i 1%g = e i.
Hypothesis chiS : forall i : 'I_k, chi i \in S i.

(* This follows from PF 6.8 *)
Variable nu : 'I_k -> {additive {cfun gT} -> {cfun gT}}.

Hypothesis coherentS : 
  forall i : 'I_k, my_coherent 'L_i G (S i) ('K_i)^# (tau i) (nu i).


(************************************)

Let rho_res i : rho i =1 crestrict ('K_i)^#.
Proof.
move => f; apply/cfunP => x; rewrite !cfunE.
case: (_ \in _); last by rewrite mul0r.
by rewrite /DadeH big_set1 mul1g cards1 invr1.
Qed.


Let disjoint_Atau i j : i != j -> [disjoint (Atau i) & (Atau j)].
Proof.
move => i_n_j.
rewrite disjoint_subset; apply/subsetP => x; rewrite !inE.
rewrite !Dade_supp class_supportEr.
case/bigcupP => g gG; rewrite conjD1g !inE => /andP [] xn1 xKi.
apply: contraT; rewrite negbK class_supportEr.
case/bigcupP => y yG; rewrite conjD1g !inE => /andP [] _ xKj.
move: (order_dvdG xKi) (order_dvdG xKj); rewrite !cardJg => x_i x_j.
have: #[x] == 1%N.
  rewrite -dvdn1; move: (card_coprime i_n_j); rewrite /coprime => /eqP <-.
  by rewrite dvdn_gcd x_i x_j.
by rewrite order_eq1 (negPf xn1).
Qed.


Let zi_uniq i : uniq (zi i). Proof. exact: undup_uniq. Qed.

Let ziP i : forall t, 
  reflect (exists r : Iirr 'K_i, t = 'Ind['L_i, 'K_i] 'xi_r) (t \in zi i).
Proof.
move => t; apply: (iffP idP); rewrite mem_undup.
  by case/mapP => f; case/irrIP => r <- ->; exists r.
by case => r ->; apply/mapP; exists 'xi_r => //; exact: irr_xi.
Qed.



(******************************)

Local Notation beta i := ((tau i) ('Ind['L_i, 'K_i] '1_('K_i) - chi i)).

Let calA := [pred i : 'I_k | ('[beta i, (nu i1) (chi i1)]_G != 0) && (i != i1)].
Let calB := [pred i : 'I_k | ('[beta i, (nu i1) (chi i1)]_G == 0) && (i != i1)].

Local Notation e1 := (e i1).
Local Notation h1 := (h i1).
Local Notation nu1 := (nu i1).


Let en0 i : e i != 0.
Proof. by rewrite -neq0N_neqC -lt0n indexg_gt0. Qed.

Let hn0 i : h i != 0. Proof. exact: neq0GC. Qed.

Let eh i : e i * h i = #|'L_i|%:R.
Proof. by rewrite -(LaGrange (sKL i)) natr_mul mulrC. Qed.

Let e_cardH i : e i = #|tnth H i|%:R.
Proof.
apply/eqP; rewrite -eqN_eqC.
have/Frobenius_context [KH_L _ _ _ _] := frobeniusL i.
have := LaGrange (sKL i); move/sdprod_card: KH_L <-.
move/eqP; rewrite eqn_mul2l.
case cK: (_ == 0)%N; last by rewrite orFb.
by have := cardG_gt0 'K_i; move/eqP: cK ->.
Qed.

Let e_gt1 i : 1 < e i.
Proof.
rewrite e_cardH -(ltn_ltC 1).
case: (ltngtP 1 #|tnth H i|) => //.
  by apply: contraTT; rewrite -leqNgt cardG_gt0.
have/Frobenius_context [_ _ Hn1 _ _] := frobeniusL i.
by move/esym/eqP; rewrite -trivg_card1 (negPf Hn1).
Qed.


Let h_gt1 i : 1 < h i.
rewrite -(ltn_ltC 1).
case: (ltngtP 1 #|'K_i|) => //.
  by apply: contraTT; rewrite -leqNgt cardG_gt0.
have/Frobenius_context [_ Kn1 _ _ _] := frobeniusL i.
by move/esym/eqP; rewrite -trivg_card1 (negPf Kn1).
Qed.


Let cardA i : #|('K_i)^#|%:R = h i - 1.
Proof.
have := cardsD1 1%g 'K_i; rewrite in_group => /eqP.
by rewrite eqN_eqC natr_add addrC -subr_eq => /eqP ->.
Qed.

Let eh_ineq i : e i <= (h i - 1) / 2%:R.
Proof.
have two_n0: 2%:R != (0 : algC) by rewrite -neq0N_neqC.
rewrite -[e i]mulr1 -{1}[1](mulfV two_n0) mulrA leC_mul2r ?posC_inv ?posC_nat //.
rewrite -(leC_add2r 1) subrK e_cardH /h.
rewrite -natr_mul -[_ + 1%:R]natr_add -leq_leC.
have := Frobenius_dvd_ker1 (frobeniusL i).
set a := #|_|; set b := #|_|.
have/Frobenius_context [KH_L Kn1 _ _ /proper_sub sHL]:= (frobeniusL i).
have b_gt0: (0 < b)%N by rewrite /b cardG_gt0.
have b_gt1: (1 < b)%N.
  case: (ltngtP 1 b) => //; first by rewrite ltnNge b_gt0.
  by move/esym/eqP; rewrite /b -trivg_card1 (negPf Kn1).
have b_eq: exists m, b = m.+2 by exists (b - 2)%N; rewrite -addn2 (subnK b_gt1).
case/dvdnP => q; case: q => [| q].
  by case: b_eq => m ->; rewrite mul0n.
case: q => [| q]; last first.
  case: b_eq => m ->.
  rewrite -{2}(prednK (ltn0Sn (m.+1))) => ->.
  rewrite -[(_ * _).+1]addn1 leq_add2r -[q.+2]addn2 muln_addl mulnC.
  by rewrite -{1}[(_ * _)%N]add0n leq_add2r leq0n.
rewrite mul1n => b1_a.
have: ~~ odd (b.-1).
  by rewrite -subn1 (odd_sub b_gt0) /b (oddSg (sKL i)) ?(oddSg (sLG i)).
have: odd a by rewrite /a (oddSg sHL) ?(oddSg (sLG i)).
by rewrite -b1_a => ->.
Qed.


Let h1_lt_others i : i != i1 -> h1 + 2%:R <= h i.
Proof.
move => i_n_1; move: (i1_prop i).
rewrite -natr_add -!leq_leC.
set a := #|_|; set b := #|_|; move => a_le_b.
case: (ltngtP (a + 1%N) b).
- by rewrite -[2]addn1 addnA !addn1.
- rewrite -addn1 leq_add2r => b_le_a.
  have ab: a = b by apply: anti_leq; rewrite a_le_b b_le_a.
  have := card_coprime i_n_1.
  rewrite -/a -/b ab /coprime gcdnn => /eqP b1.
  by have := h_gt1 i; rewrite -(ltn_ltC 1) -/b b1 ltnn.
move => a1_b.
have: ~~ odd (a + 1) by rewrite odd_add (oddSg (sKL i1)) ?(oddSg (sLG i1)).
have: odd b by rewrite (oddSg (sKL i)) ?(oddSg (sLG i)).
by rewrite a1_b => ->.
Qed.




Let inSP i t : reflect (exists2 r : Iirr 'K_i, t = 'Ind['L_i, 'K_i] 'xi_r &
  t != 'Ind['L_i, 'K_i] '1_('K_i)) (t \in S i).
Proof.
rewrite mem_filter; apply: (iffP andP) => /=.
  by move => [t_n_1] /ziP [r] t_eq; exists r; rewrite t_eq in t_n_1 *.
by case => r -> ->; split => //; apply/ziP; exists r.
Qed.
  

Let sSCL i : {subset (S i) <= 'CF('L_i)}.
Proof. by move => f /inSP [r] -> _; rewrite memc_induced // memc_irr. Qed.


Let sSCLK i : {subset (S i) <= 'CF('L_i, 'K_i)}.
Proof.
move => f fS; rewrite memcE (sSCL fS) andbT.
by case/inSP: fS => r -> _; rewrite support_induced // memc_irr.
Qed.


Let orthonormal_S i: orthonormal 'L_i (S i).
Proof.
apply/orthonormalP; split => //; first by rewrite filter_uniq.
move => f g /sSirrL/irrIP [r] <- /sSirrL/irrIP [t] <-.
rewrite irr_orthonormal; apply/esym; case xi_eq: (_ == _).
  by move/eqP/xi_inj: xi_eq ->; rewrite eqxx.
by case rt: (r == t) xi_eq => //; move/eqP: rt ->; rewrite eqxx.
Qed.


Let sSZS i : {subset (S i) <= 'Z[S i]}.
Proof.
by move => f fS; rewrite memv_vchar // (orthonormal_free (orthonormal_S i)).
Qed.

Let sSZSK i : {subset (S i) <= 'Z[S i, 'K_i]}.
Proof.
by move => f fS; rewrite vchar_split (sSZS fS) (support_memc (sSCLK fS)).
Qed.


Let pre_betaZA i : 'Ind['L_i, 'K_i] '1_('K_i) - chi i \in 'Z[irr 'L_i, ('K_i)^#].
Proof.
rewrite vchar_split; apply/andP; split.
  rewrite vchar_sub ?vchar_char ?is_char_induced ?cfuni_xi0 ?is_char_irr //.
  by case/irrIP: (sSirrL (chiS i)) => r <-; exact: is_char_irr.
apply/subsetP => x; apply: contraR.
rewrite !inE cinduced_1 // !cfunE negb_and negbK !/fcf.
case/orP => [/eqP -> | xnK].
  by rewrite (chi1 i) in_group [_ *: _]mulr1 subrr.
rewrite (supportP (support_memc (sSCLK (chiS i))) _ xnK).
by rewrite (negPf xnK) [_ *: _]mulr0 subr0.
Qed.

Let betaZG i : beta i \in 'Z[irr G].
Proof. exact: Dade_vchar. Qed.

Let nu_to i : {in 'Z[S i], forall f, (nu i) f \in 'Z[irr G]}.
Proof. by case: (coherentS i). Qed.

Let nu_isom i : {in 'Z[S i] &, isometry 'L_i G (nu i)}.
Proof. by case: (coherentS i). Qed.

Let nu_tau i : {in 'Z[S i, ('K_i)^#], nu i =1 tau i}.
Proof. by case: (coherentS i). Qed.


Let orthonormal_nuS i : orthonormal G (map (nu i) (S i)).
Proof.
have nu_inj: {in S i &, injective (nu i)}.
  move => f g fS gS /= /eqP.
  rewrite -subr_eq0 -raddf_sub -(@inner_prod0 _ G); last first.
    by rewrite memc_Zirr ?nu_to ?vchar_sub ?sSZS.
  rewrite nu_isom ?vchar_sub ?sSZS // inner_prod0 ?memv_sub ?sSCL //.
  by rewrite subr_eq0 => /eqP ->.
apply/orthonormalP; split.
- by move => f /mapP [g] gS ->; rewrite memc_Zirr ?nu_to ?(sSZS gS).
- by rewrite map_inj_in_uniq ?filter_uniq.
move => f g /mapP [x] xS -> /mapP [y] yS ->.
rewrite nu_isom ?sSZS //.
case/orthonormalP: (orthonormal_S i) => _ _ -> //.
case: (boolP (x == y)) => [/eqP -> | xny]; first by rewrite eqxx.
case: (boolP (_ == _)) => // /eqP/nu_inj => /(_ xS yS) /eqP.
by rewrite (negPf xny).
Qed.


Let norm_nuS i f : f \in S i -> '[(nu i) f, (nu i) f]_G = 1.
Proof.
move => fS; case/orthonormalP: (orthonormal_nuS i) => _ _.
by do 2 move/(_ ((nu i) f)); rewrite eqxx; apply; apply/mapP; exists f.
Qed.


Lemma isZC_normC_ge1 a : isZC a -> a != 0 -> 1 <= `|a|.
Proof.
rewrite isZCE; case/orP; case/isNatCP => n.
  by move ->; case: n => [| n]; rewrite ?eqxx // normC_nat -(leq_leC 1).
move/eqP; rewrite eqr_oppC => /eqP ->; rewrite normC_opp oppr_eq0 normC_nat.
by case: n => [| n]; rewrite ?eqxx // -(leq_leC 1).
Qed.


Lemma isZC_expr2_ge1 a : isZC a -> a != 0 -> 1 <= a ^+ 2.
Proof.
move => aZ /(isZC_normC_ge1 aZ) abs_a; rewrite -int_normCK //.
have ->: 1 = ((1 : algC) ^+ 2) by rewrite expr2 mulr1.
by rewrite leC_square // posC1.
Qed.



(*************************************)
(* The next results are copied from the proof of 7.9 *)

Let cf_n_f i f : f \in S i -> (f^*)%CH != f.
Proof.
move => fS; case/irrIP: (sSirrL fS) => r chi_r.
rewrite -chi_r odd_eq_conj_irr1 ?(oddSg (sLG i)) // chi_r.
case: (boolP ('K_i :==: 'L_i)) => [/eqP KL | KnL].
  move: fS; rewrite mem_filter => /andP [f_n_1 _].
  by move: f_n_1; rewrite cinduced_1 //= KL indexgg scale1r.
have: 'K_i \proper 'L_i by rewrite properEneq KnL (sKL i).
case/properP => _ [x] xL.
apply: contra => /eqP/cfunP/(_ x); rewrite cfunE xL.
move/eqP; apply: contraTT => xnK.
by rewrite /fcf (supportP (support_memc (sSCLK fS)) _ xnK) -(eqN_eqC 0).
Qed.


Let cf_inS i f : f \in S i -> (f^*)%CH \in S i.
Proof.
rewrite !mem_filter /= => /andP [f_n_1].
case/ziP => r f_ind; apply/andP; split.
  apply: contra f_n_1 => /eqP cf_1.
  have := cfun_conjCK f.
  by rewrite cf_1 cinduced_conjC cfun_conjC1 => <-.
apply/ziP; case/irrIP: (irr_conjC r) => t tr.
by exists t; rewrite f_ind cinduced_conjC tr.
Qed.


Let ortho_S i f g : f \in S i -> g \in S i -> '[f, g]_('L_i) = (f == g)%:R.
Proof. 
by move => fS gS; case/orthonormalP: (orthonormal_S i) => _ _ /(_ f g fS gS).
Qed.

Let f_cf_ortho i f : f \in S i -> '[f, (f^*)%CH]_('L_i) = 0.
Proof.
by move => fS; rewrite ortho_S ?cf_inS // eq_sym (negPf (cf_n_f fS)).
Qed.

Let diff_f_cf_ZSA i f : f \in S i -> f - (f^*)%CH \in 'Z[S i, ('K_i)^#].
Proof.
move => fS; rewrite vchar_split ?vchar_sub ?sSZS ?cf_inS // andTb.
apply/subsetP => x; apply: contraR.
rewrite !inE !cfunE negb_and negbK -!/fcf.
case/orP => [/eqP -> | xnK].
  case/irrIP: (sSirrL fS) => r <-.
  by case/isNatCP: (isNatC_irr1 r) => n ->; rewrite conjC_nat subrr.
by rewrite /fcf (supportP (support_memc (sSCLK fS)) _ xnK) conjC0 subr0.
Qed.

Let diff_f_cf_ZirrLA i f : f \in S i -> f - (f^*)%CH \in 'Z[irr 'L_i, ('K_i)^#].
Proof.
move => fS; rewrite vchar_split ?(support_vchar (diff_f_cf_ZSA fS)) andbT.
by rewrite vchar_sub ?vchar_char ?is_char_conjC //;
  case/irrIP: (sSirrL fS) => r <-; rewrite is_char_irr.
Qed.


Let nu_ij_ortho i j f g : i != j -> f \in S i -> g \in S j ->
  '[(nu i) f, (nu j) g]_G = 0.
Proof.
move => i_n_j fS gS.
pose ab := [:: (nu i) f; (nu i) ((f^*)%CH)].
pose cd := [:: (nu j) g; (nu j) ((g^*)%CH)].
have ab_ortho : orthonormal G ab.
  have nu1_n: (nu i) f != (nu i) ((f^*)%CH).
    apply: contraR (cf_n_f fS); rewrite negbK -subr_eq0 -raddf_sub.
    rewrite -(@inner_prod0 _ G) ?nu_isom ?vchar_sub ?sSZS ?cf_inS //.
      by rewrite inner_prod0 ?memv_sub ?sSCL ?cf_inS // subr_eq0 eq_sym.
    by rewrite memc_Zirr ?nu_to ?vchar_sub ?sSZS ?cf_inS.
  apply/orthonormalP; split.
  - by move => x; rewrite !inE; case/orP => /eqP ->; rewrite memc_Zirr ?nu_to ?sSZS ?cf_inS.
  - by rewrite !cons_uniq !inE in_nil /= andbT.
  by move => x y; rewrite !inE; do 2 case/orP => /eqP ->; 
    rewrite ?eqxx ?(negPf nu1_n) ?nu_isom ?sSZS ?cf_inS //;
    rewrite ortho_S ?cf_inS ?eqxx // ?(negPf (cf_n_f fS)) eq_sym;
    rewrite (negPf (cf_n_f fS), negPf nu1_n).
have cd_ortho : orthonormal G cd.
  have nu2_n: (nu j) g != (nu j) ((g^*)%CH).
    apply: contraR (cf_n_f gS); rewrite negbK -subr_eq0 -raddf_sub.
    rewrite -(@inner_prod0 _ G) ?nu_isom ?vchar_sub ?sSZS ?cf_inS //.
      by rewrite inner_prod0 ?memv_sub ?sSCL ?cf_inS // subr_eq0 eq_sym.
    by rewrite memc_Zirr ?nu_to ?vchar_sub ?sSZS ?cf_inS.
  apply/orthonormalP; split.
  - by move => x; rewrite !inE; case/orP => /eqP ->; rewrite memc_Zirr ?nu_to ?sSZS ?cf_inS.
  - by rewrite !cons_uniq !inE in_nil /= andbT.
  by move => x y; rewrite !inE; do 2 case/orP => /eqP ->; 
    rewrite ?eqxx ?(negPf nu2_n) ?nu_isom ?sSZS ?cf_inS //;
    rewrite ortho_S ?cf_inS ?eqxx // ?(negPf (cf_n_f gS)) eq_sym;
    rewrite (negPf (cf_n_f gS), negPf nu2_n).
have ab_cdZ: {subset ab <= 'Z[irr G]} /\ {subset cd <= 'Z[irr G]}.
  by split; move => x; rewrite 2!inE; case/orP => /eqP ->; 
    rewrite ?nu_to ?sSZS ?cf_inS.
have ortho_ab_cd : orthonormal G ab && orthonormal G cd by rewrite ab_ortho cd_ortho.
have /(_ 1 1):= vchar_pairs_orthonormal ab_cdZ ortho_ab_cd.
have ->: isRealC 1.
  have ->: 1 = ((1%:R) : algC) by [].
  by rewrite isZC_real ?isZC_nat.
rewrite nonzero1r !andbT !scale1r -!raddf_sub.
rewrite [(nu i) (_ - _)]nu_tau ?[(nu j) (_ - _)]nu_tau ?diff_f_cf_ZSA //.
rewrite -!/fcf !Dade1 eqxx.
set prod := '[_, _]_G.
have ->: prod == 0.
  rewrite /prod (@memc_class_ortho _ G (Atau i)) //.
    by rewrite Dade_cfunS ?memc_vchar ?diff_f_cf_ZirrLA.
  have: (tau j) (g - (g^*)%CH) \in 'CF(G, Atau j).
    by rewrite Dade_cfunS ?memc_vchar ?diff_f_cf_ZirrLA.
  rewrite memcE [in X in _ -> X]memcE => /andP [sA] ->; rewrite andbT.
  apply: (subset_trans sA).
  by rewrite subsetD disjoint_sym disjoint_Atau // Dade_support_sub.
move => /(_ isT isT) /orthonormalP [] _ => uniq_abcd.
move => /(_ ((nu i) f) ((nu j) g)); rewrite !inE !eqxx !orbT /=.
move => /(_ isT isT) ->; move: uniq_abcd => /=.
by rewrite !inE !negb_or => /andP [] /and3P [] => _ /negPf ->.
Qed.




(*************************************)


Let ineq1 : 1 - e1 / h1 - (h1 - 1) / (e1 * h1) - 
  \sum_(i \in calB) (h i - 1) / (e i * h i) <= (#|G0|%:R - 1) / #|G|%:R.
Proof.
set lhs := 1 - _ - _ - _.
set rhs := _ / _.
have nu_chi1_Z: nu1 (chi i1) \in 'Z[irr G] by rewrite nu_to ?sSZS.
case: (vchar_norm1_irr nu_chi1_Z (norm_nuS (chiS i1))) => eps [r] nu_chi1_irr.
have: #|G|%:R ^-1 * (#|G0|%:R - \sum_(g \in G0) `|'xi_r g| ^+ 2) <= rhs.
  rewrite mulrC leC_pmul2r ?sposC_inv ?sposGC // leC_add2l leC_opp G0_def.
  rewrite (big_setD1 1%g) /=; last first.
    rewrite inE in_group andbT; apply: contraT; rewrite negbK.
    case/bigcupP => i _; rewrite Dade_supp class_supportEr.
    by case/bigcupP => x _; rewrite conjD1g !inE eqxx andFb.
  rewrite -[1]addr0 leC_add //; last first.
    by apply: posC_sum => g _; rewrite -normC_exp posC_norm.
  have rZ: isZC ('xi_r 1%g) by rewrite isZCE; apply/orP; left; exact: isNatC_irr1.
  by rewrite int_normCK // isZC_expr2_ge1 ?irr1_neq0.
pose A := [tuple of (map (fun X : {group gT} => X^#) K)].
pose HH := [tuple of (map (fun X : {group gT} => DadeH) K)].
have ddI i : Dade_hypothesis G 'L_i (tnth HH i) (tnth A i).
  by rewrite !tnth_map.
have D_supp i: Dade_support (ddI i) = Atau i.
  rewrite /Dade_support {1}tnth_map; apply: eq_bigr => g _.
  by rewrite /Dade_support1 tnth_map.
have Dade_disj i j : i != j -> [disjoint Dade_support (ddI i) & Dade_support (ddI j)].
  by move => i_n_j; rewrite !D_supp (disjoint_Atau i_n_j).
have := @pf75 _ A L HH ddI Dade_disj r.
set G0_0 := _ :\: _.
have ->: G0_0 = G0.
  by rewrite G0_def /G0_0; congr (_ :\: _); apply: eq_bigr => i _.
rewrite -[_ * _]opprK -mulrN oppr_sub -leC_opp oppr0 oppr_add opprK leC_sub.
rewrite /rhs => {rhs}; set rhs := \sum_(i < k) _.
suff: lhs <= rhs.
  by move => ineq1 ineq2; move: (leC_trans ineq1 ineq2); exact: leC_trans.
rewrite /rhs (bigD1 i1) //= (bigID calB) /=.
rewrite /lhs leC_add //.
  rewrite leC_add //; last by rewrite leC_opp tnth_map eh cardA leC_refl.
  set X := '[_]_ _.
  have {X}->: X = '[(rho i1) (nu1 (chi i1))]_('L_i1).
    rewrite /X !tnth_map nu_chi1_irr linearZ inner_normZ.
    rewrite int_normCK ?isZC_sign //= expr2.
    by case: {nu_chi1_irr} eps; rewrite (expr1, expr0) (mulrNN, mulr1) !mul1r.
  (* Change the interface of pf78b1: remove dependencies on Gamma, a *)
  (* The result of pf78a2 should be not required here *)
  have := @pf78a2 _ _ _ (ddA i1) 'K_i1 (zi i1) (nKL i1) 
    (erefl ('K_i1)^#) (zi_uniq i1) (ziP i1) nu1 (coherentS i1) (chi i1)
    (chiS i1) (sSirrL (chiS i1)) (chi1 i1).
  case => a; case => Gamma [] _ => Gamma1 Gamma_nu beta_eq.
  have := @pf78b1 _ _ _ (ddA i1) 'K_i1 (zi i1) (nKL i1)
    (erefl ('K_i1)^#) (zi_uniq i1) (ziP i1) nu1 (coherentS i1) (chi i1)
    (chiS i1) (sSirrL (chiS i1)) (chi1 i1) a Gamma Gamma_nu 
    beta_eq (eh_ineq i1).
  by [].
rewrite -[- _]addr0 leC_add //.
  have ->: \sum_(i \in calB) (h i - 1) / (e i * h i) =
    \sum_(i < k | [&& i != i1, '[beta i, nu1 (chi i1)]_G == 0 & i != i1]) (h i - 1) / (e i * h i).
    apply: eq_bigl => i; rewrite /calB !inE; apply/idP/idP.
      by move/andP => [] -> ->.
    by move/andP => [] -> ->.
  rewrite -leC_sub opprK -big_split posC_sum //= => i _.
  rewrite -[0]addr0 -addrA leC_add ?posC_inner_prod //.
  by rewrite addrC tnth_map cardA eh subrr leC_refl.
apply: posC_sum => i /andP [] i_n1; rewrite i_n1 negb_and orbF => beta_chi_n0.
rewrite leC_sub !tnth_map.
have := pf78c2 (nKL i) (erefl ('K_i)^#) (zi_uniq i) (ziP i) (coherentS i) 
   (chiS i) (sSirrL (chiS i))(chi1 i) (irr_xi r).
move ->; last first.
  move => f fS; have := nu_ij_ortho i_n1 fS (chiS i1).
  rewrite nu_chi1_irr inner_prodZr => /eqP; rewrite mulf_eq0; case/orP.
    by rewrite conjC_eq0 signr_eq0.
  by move/eqP.
rewrite -leC_sub -{2}[_ / _]mulr1 -mulr_subr !posC_mul ?posC_inv ?posC_nat //.
rewrite leC_sub isZC_expr2_ge1 //; first by rewrite isZC_inner_Zirr ?vchar_irr.
move: beta_chi_n0; rewrite nu_chi1_irr inner_prodZr mulf_eq0 negb_or.
by move/andP => [].
Qed.


(**************************************)



Let ineq2 : \sum_(i \in calB) (h i - 1) / (e i) <= e1 - 1.
Proof.
have := @pf78a2 _ _ _ (ddA i1) 'K_i1 (zi i1) (nKL i1) 
  (erefl ('K_i1)^#) (zi_uniq i1) (ziP i1) nu1 (coherentS i1) (chi i1)
  (chiS i1) (sSirrL (chiS i1)) (chi1 i1).
rewrite -/(S i1) -/e1.
move => [a] [Gamma] [] _ Gamma1 Gamma_nu beta_eq.
have fe_nat i f: f \in S i -> exists m, (f 1%g / e i) = m%:R.
  move => fS; apply/isNatCP; case/inSP: fS => r -> _.
  by rewrite -/fcf cinduced1 -/(e i) // mulrAC mulfV // mul1r isNatC_irr1.
pose cx i := '[beta i1, (nu i) (chi i)]_G.
pose X : {cfun gT} := \sum_(i < k | i != i1) cx i *: 
  \sum_(f <- S i) f 1%g / e i *: (nu i) f.
have X_ortho: '[Gamma - X, X]_G = 0.
  suff ortho i f: i != i1 -> f \in S i -> '[Gamma - X, (nu i) f]_G = 0.
    rewrite {2}/X raddf_sum big1 // => i i_n_1 /=.
    rewrite inner_prodZr raddf_sum big1_seq ?mulr0 // => f /andP [_ fS] /=.
    by rewrite inner_prodZr ortho // mulr0.
  move => i_n_1 fS.
  rewrite inner_prodDl inner_prodNl.
  have ->: '[X, (nu i) f]_G = f 1%g / e i * cx i.
    rewrite -inner_prodbE /X linear_sum (bigD1 i) //=.
    rewrite linearZ linear_sum (bigID (pred1 f)) /=.
    rewrite big_pred1_uniq ?filter_uniq // big1_seq; last first.
      move => g /andP [g_n_f gS]; rewrite inner_prodbE inner_prodZl.
      by rewrite nu_isom ?ortho_S ?sSZS // (negPf g_n_f) mulr0.
    rewrite addr0 inner_prodbE inner_prodZl norm_nuS // mulr1 [_ *: _]mulrC.
    rewrite big1 ?addr0 // => j /andP [_ j_n_i].
    rewrite linearZ linear_sum big1_seq ?scaler0 // => g /andP [_ gS].
    by rewrite /= inner_prodbE inner_prodZl nu_ij_ortho ?mulr0.
  have ->: '[Gamma, (nu i) f]_G = '[beta i1, (nu i) f]_G.
    rewrite beta_eq !inner_prodDl inner_prodNl inner_prodZl.
    rewrite nu_ij_ortho //; last by rewrite eq_sym.
    rewrite ['['1_G, _]_G]inner_conj.
    rewrite (pf78a1 _ (erefl ('K_i)^#) (zi_uniq i) _ 
      (coherentS i) (chiS i) (sSirrL (chiS i)) (chi1 i)) //.
    rewrite conjC0 addr0 subr0 addrC; apply/esym.
    rewrite -inner_prodbE linear_sum big1_seq ?mulr0 ?add0r // => g /andP [_ gS].
    by rewrite /= inner_prodbE inner_prodZl nu_ij_ortho ?mulr0 // eq_sym.
  have [m fe_m] := fe_nat i f fS.
  have diff_ZSA : f - chi i *+ m \in 'Z[S i, ('K_i)^#].
    rewrite vchar_split vchar_sub ?vchar_scal ?sSZS // andTb.
    apply/subsetP => x; apply: contraR.
    rewrite -scaler_nat -fe_m !inE !cfunE negb_and negbK !/fcf.
    case/orP => [/eqP -> | xnK].
      by rewrite (chi1 i) -[_ *: _]mulrA mulVf ?mulr1 ?subrr.
    by rewrite !(supportP (support_memc (sSCLK _)) _ xnK) // scaler0 subr0.
  have diff_ZLA : f - chi i *+ m \in 'Z[irr 'L_i, ('K_i)^#].
    by rewrite (vchar_subset _ _ (@sSirrL i)) 
      ?free_irr ?(orthonormal_free (orthonormal_S i)).
  rewrite /cx fe_m -conjC_nat -inner_prodZr -inner_prodNr -inner_prodDr.
  rewrite scaler_nat -raddfMn -raddf_sub nu_tau //.
  rewrite (@memc_class_ortho _ G (Atau i1)) //.
    by rewrite Dade_cfunS ?memc_vchar ?diff_f_cf_ZirrLA.
  have: (tau i) (f - chi i *+ m) \in 'CF(G, Atau i).
    by rewrite Dade_cfunS ?memc_vchar.
  rewrite memcE [in X in _ -> X]memcE => /andP [sA] ->; rewrite andbT.
  apply: (subset_trans sA).
  by rewrite subsetD disjoint_Atau // Dade_support_sub.
have norm_X : '[X]_G <= e1 - 1.
  have := @pf78b2 _ _ _ (ddA i1) 'K_i1 (zi i1) (nKL i1) (erefl ('K_i1)^#) 
    (zi_uniq i1) (ziP i1) nu1 (coherentS i1) (chi i1) (chiS i1) 
    (sSirrL (chiS i1)) (chi1 i1) a Gamma Gamma1 Gamma_nu beta_eq (eh_ineq i1).
  rewrite -/e1; apply: leC_trans.
  have ->: Gamma = (Gamma - X) + X by rewrite subrK.
  by rewrite inner_normD X_ortho conjC0 !addr0 -leC_sub addrK posC_inner_prod.
apply: leC_trans norm_X.
have x_Z i : isZC (cx i) by rewrite /cx isZC_inner_Zirr ?nu_to ?sSZS.
have ->: '[X]_G = \sum_(i < k | i != i1) (cx i) ^+ 2 *
                       \sum_(f <- S i) (f 1%g / e i) ^+ 2 / '[f]_('L_i).
  rewrite {2}/X raddf_sum; apply: eq_bigr => i i_n_1 /=.
  rewrite inner_prodZr /X -inner_prodbE linear_sum (bigD1 i) //= addrC.
  rewrite big1 ?add0r; last first.
    move => j /andP [_ j_n_i]; rewrite linearZ linear_sum big1_seq ?scaler0 //=.
    move => f fS; rewrite inner_prodbE raddf_sum big1_seq //=.
    by move => g gS; rewrite inner_prodZl inner_prodZr nu_ij_ortho ?mulr0.
  rewrite inner_prodbE inner_prodZl isZC_conj // mulrA -expr2; congr (_ * _).
  rewrite raddf_sum big_seq [in X in _ = X]big_seq /=.
  apply: eq_bigr => f fS; rewrite -inner_prodbE linear_sum.
  have [m fe_m] := fe_nat i f fS.
  rewrite (bigID (pred1 f)) /= big_pred1_uniq ?filter_uniq // big1_seq.
    rewrite inner_prodbE addr0 inner_normZ fe_m normC_nat.
    by rewrite norm_nuS ?ortho_S // eqxx invr1.
  move => g /andP [g_n_f] gS; rewrite inner_prodbE inner_prodZl inner_prodZr.
  by rewrite nu_isom ?sSZS // ortho_S // (negPf g_n_f) !mulr0.
rewrite -[\sum_(i \in calB) _]addr0 [in X in _ <= X](bigID calB) /=.
rewrite leC_add //; last first.
  apply: posC_sum => i _; rewrite -int_normCK // -normC_exp posC_mul ?posC_norm //.
  rewrite big_seq posC_sum // => f fS; case: (fe_nat i f fS) => m ->.
  by rewrite posC_mul ?posC_inv ?posC_inner_prod // expr2 posC_mul ?posC_nat.
have ->: \sum_(i \in calB) (h i - 1) / e i =
  \sum_(i < k | [&& i != i1, '[beta i, nu1 (chi i1)]_G == 0 & i != i1]) (h i - 1) / e i.
    by apply: eq_bigl => i; rewrite /calB !inE; apply/idP/idP; move/andP => [] -> ->.
rewrite -leC_sub -sumr_sub posC_sum // => i /and3P [] i_n_1 beta_nu0 _.
rewrite sum_squares_calS // -/(e i) -/(h i).
have cx_n0: cx i != 0.
  have := pf79 oddG (disjoint_Atau i_n_1) (erefl ('K_i)^#) (erefl ('K_i1)^#)
      (nKL i) (nKL i1) (zi_uniq i) (zi_uniq i1) (ziP i) (ziP i1)
      (coherentS i) (coherentS i1) (chiS i) (chiS i1) (sSirrL (chiS i))
      (sSirrL (chiS i1)) (chi1 i) (chi1 i1).
  by rewrite beta_nu0 orFb.
rewrite leC_sub -{1}[_ / _]mul1r leC_mul2r ?isZC_expr2_ge1 //.
rewrite posC_mul ?posC_inv /e ?posC_nat // leC_sub.
by rewrite /h -(leq_leC 1) cardG_gt0.
Qed.




Let ineq3 : \sum_(i \in calB) (h i - 1) / (e i * h i) <= (e1 - 1) / (h1 + 2%:R).
Proof.
suff ineq: \sum_(i \in calB) (h i - 1) / (e i * h i) <= 
  \sum_(i \in calB) (h i - 1) / e i / (h1 + 2%:R).
  apply: (leC_trans ineq).
  by rewrite mulr_suml leC_mul2r ?posC_inv -?natr_add -?(leq_leC 0) ?addn2.
rewrite -leC_sub -sumr_sub posC_sum // => i.
rewrite /calB !inE => /andP [_] i_n_1.
rewrite invf_mul mulrA leC_sub leC_mul2l ?posC_mul ?posC_inv -?cardA ?posC_nat //.
rewrite -[(h i)^-1]mul1r -[(_ + _)^-1]mulr1 -{3}(mulfV (hn0 i)) mulrA.
rewrite leC_mul2r ?posC_inv ?posC_nat //.
have h2_n0 : h1 + 2%:R != 0 by rewrite -natr_add -neq0N_neqC addn2.
rewrite -{1}(mulVf h2_n0) leC_mul2l ?posC_inv -?natr_add ?posC_nat //.
by rewrite natr_add h1_lt_others.
Qed.


Lemma pf7_10 : exists i,
  (e i - 1) * ((h i - 2%:R * e i - 1) / (e i * h i) + 2%:R / (h i * (h i + 2%:R))) <=
    (#|G0|%:R - 1) / #|G|%:R.
Proof.
exists i1.
apply: leC_trans ineq1.
rewrite mulr_addr mulr_subl mulrCA mul1r {1}invf_mul !mulrA mulfK //.
rewrite 2!mulr_subl mulr_natl mulr2n mulfV // mulr_addl oppr_add.
rewrite [_ - _ - 1]addrAC mulr_subl oppr_add -!addrA !leC_add2l.
rewrite addrA addrC -addrA leC_add2l opprK -[_ + _]opprK leC_opp.
rewrite !oppr_add !opprK mulr_addl !invf_mul mulrA mulfV // addrC oppr_add.
rewrite 2!addrA addrK -mulr_subl -mulrA -mulr_subr.
have h1_2: h1 + 2%:R != 0 by rewrite -natr_add -neq0N_neqC addn2.
rewrite [_ * (_ / _)]mulrC -{1}[h1^-1]mulr1 -{3}(mulVf h1_2) mulrA.
by rewrite -mulr_subr -addrA subrr addr0 mulrAC mulVf // mul1r ineq3.
Qed.




(***************************************)

(* PF 7.11 *)


Theorem pf7_11 : G0 != [1 gT].
Proof.
case: pf7_10 => i; apply: contraL => /eqP ->.
rewrite cards1 subrr mul0r ltC_geF //.
rewrite sposC_mul -?ltC_sub //.
set X := _ / _; set Y := _ / _.
have: X <= Y + X.
  rewrite -leC_sub addrK /Y eh posC_mul ?posC_inv ?posC_nat //.
  have two_n0: 2%:R != (0 : algC) by rewrite -neq0N_neqC.
  rewrite addrAC leC_sub -[_ - _]mul1r -{2}(mulfV two_n0) -mulrA.
  by rewrite leC_mul2l -?(leq_leC 0) // mulrC.
apply: ltC_leC_trans.
rewrite sposC_mul ?sposC_inv -?(ltn_ltC 0) //.
by rewrite sposC_mul -?natr_add -?(ltn_ltC 0) ?cardG_gt0 // addn2.
Qed.


End PF7_10.


End Seven.



