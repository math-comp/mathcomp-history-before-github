(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import tuple finfun bigops ssralg poly.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* General polynomials *)

Open Scope ring_scope.
Import GRing.Theory.

(* Should be included in ssralg.v. *)

Section PolyRingMorphism.

Variables aR' aR rR : ringType.
Variables (f : aR -> rR) (g : aR' -> aR).
Hypotheses (fM : ring_morphism f) (gM : ring_morphism g).

Definition map_poly (p : {poly aR}) := Poly (map f p).

Lemma coef_map : forall p i, (map_poly p)`_i = f p`_i.
Proof.
move=> p i; rewrite coef_Poly.
by elim: i (p : seq _) => [|i IHi] [|//]; rewrite ringM_0.
Qed.

Lemma map_polyC : forall x, map_poly x%:P = (f x)%:P.
Proof.
by move=> x; apply/polyP=> i; rewrite coef_map !coefC (fun_if f) ringM_0.
Qed.

Lemma map_polyX : map_poly 'X = 'X.
Proof. by apply/polyP=> i; rewrite coef_map !coefX ringM_nat. Qed.

Lemma map_polyM : ring_morphism map_poly.
Proof.
split=> [x y | x y|]; apply/polyP=> i; last by rewrite map_polyC ringM_1.
  by rewrite !(coef_sub, coef_map) ringM_sub.
rewrite coef_map !coef_mul ringM_sum //; apply: eq_bigr => j _.
by rewrite !coef_map ringM_mul.
Qed.

End PolyRingMorphism.

Section CatPoly.
(* The categorical characterizaion of polynomials. *)

Lemma map_poly_id : forall R, @map_poly R R id =1 id.
Proof. by move=> R p; rewrite /map_poly map_id polyseqK. Qed.

Variables (aR : ringType) (rR : comRingType).

Definition morph_poly (f : aR -> rR) x (p : {poly aR}) := (map f p).[x].

Lemma eq_morph_poly : forall f g, f =1 g -> morph_poly f =2 morph_poly g.
Proof. by move=> f g eq_fg x p; rewrite /morph_poly (eq_map eq_fg). Qed.

Lemma horner_map : forall f x p, (map_poly f p).[x] = morph_poly f x p.
Proof. by move=> f x p; rewrite horner_Poly. Qed.

Lemma morph_polyC : forall f x y, ring_morphism f -> morph_poly f x y%:P = f y.
Proof. by move=> f x y fM; rewrite -horner_map map_polyC // hornerC. Qed.

Lemma morph_polyX : forall f x, ring_morphism f -> morph_poly f x 'X = x.
Proof. by move=> f x fM; rewrite -horner_map map_polyX // hornerX. Qed.

Lemma morph_polyM : forall f x,
  ring_morphism f -> ring_morphism (morph_poly f x).
Proof.
move=> f x; move/map_polyM=> fM.
split=> [p q | p q |]; rewrite -!horner_map; last 1 first.
- by rewrite ringM_1 // hornerC.
- by rewrite ringM_sub // horner_add horner_opp.
by rewrite ringM_mul // horner_mul //; exact: mulrC.
Qed.

Lemma polyC_morph : forall R, ring_morphism (@polyC R).
Proof. by split=> // x y; rewrite ?polyC_sub ?polyC_mul. Qed.

Lemma poly_initial : forall f : {poly aR} -> rR,
  ring_morphism f -> f =1 morph_poly (f \o (@polyC aR)) (f 'X).
Proof.
move=> f fM; set g := f \o _; set h := morph_poly g _.
have gM: ring_morphism g := comp_ringM fM (@polyC_morph _).
have hM: ring_morphism h := morph_polyM _ gM.
apply: (@poly_ind _ (fun p => f p = h p)) => [|p x f_p].
  by rewrite 2?ringM_0.
by rewrite 2?ringM_add 2?ringM_mul // -{}f_p /h morph_polyX ?morph_polyC.
Qed.


End CatPoly.

Lemma morph_poly_id : forall R x p, @morph_poly _ R id x p = p.[x].
Proof. by move=> R x p; rewrite /morph_poly map_id. Qed.

(* Multinomials as iterated polynomials. *)
Section MultinomialDef.

Variable R : idomainType.

Fixpoint multi n := if n is n'.+1 then poly_idomainType (multi n') else R.

Fixpoint inject n m (p : multi n) {struct m} : multi (m + n) :=
  if m is m'.+1 return multi (m + n) then (inject m' p)%:P else p.

Lemma inject_inj : forall i m, injective (@inject i m).
Proof. by move=> i; elim=> //= m IHm p q; move/polyC_inj; move/IHm. Qed.

Lemma inject0 : forall i m, @inject i m 0 = 0.
Proof. by move=> i; elim=> //= m ->. Qed.

Lemma inject_eq0 : forall i m p, (@inject i m p == 0) = (p == 0).
Proof. by move=> i m p; rewrite -(inj_eq (@inject_inj i m)) inject0. Qed.

Lemma size_inject : forall i m p, size (@inject i m.+1 p) = (p != 0 : nat).
Proof. by move=> i m p; rewrite size_polyC inject_eq0. Qed.

Definition cast_multi i m n Emn : multi i -> multi n :=
  let: erefl in _ = n' := Emn return _ -> multi n' in inject m.

Definition multi_var n (i : 'I_n) := cast_multi (subnK (valP i)) 'X.

Notation "'X_ i" := (multi_var i).

Definition multiC n : R -> multi n := cast_multi (addn0 n).

Lemma inject_morph : forall m n, ring_morphism (@inject n m).
Proof. elim=> // m IHm n; exact: comp_ringM (@polyC_morph _) (IHm n). Qed.

Lemma cast_multiM : forall i m n Enm, ring_morphism (@cast_multi i m n Enm).
Proof. by move=> i m n; case: n /; exact: inject_morph. Qed.

Lemma multiC_morph : forall n, ring_morphism (multiC n).
Proof. by move=> n; exact: (cast_multiM (addn0 n)). Qed.

Section eval_multi.

Variables (rR : comRingType) (fC : R -> rR) (fX : seq rR).
Hypothesis fCM : ring_morphism fC.

Fixpoint morph_multi n : multi n -> rR :=
  if n is i.+1 return multi n -> rR then morph_poly (@morph_multi i) fX`_i
  else fC.

Lemma morph_multiM : forall n, ring_morphism (@morph_multi n).
Proof. elim=> //= n; exact: morph_polyM. Qed.

Lemma morph_multiX : forall n (i : 'I_n), morph_multi 'X_i = fX`_i.
Proof.
move=> n [i lt_i_n]; rewrite /multi_var /=.
move: (n - _)%N {lt_i_n}(subnK _) => m; case: n /.
elim: m => [|m <-] /=; first exact: morph_polyX (morph_multiM _).
exact: morph_polyC (morph_multiM _).
Qed.

Lemma morph_multiC : forall n x, morph_multi (multiC n x) = fC x.
Proof.
move=> n x; rewrite /multiC /=.
case: {2 3 5}n / (addn0 n) => /=; elim: n => //= n <-.
exact: morph_polyC (morph_multiM _).
Qed.

End eval_multi.

Lemma eq_morph_multi : forall (rR : comRingType) n (f g : R -> rR) fX gX,
  f =1 g -> (fun i : 'I_n => fX`_i) =1 (fun i => gX`_i) ->
  (morph_multi f fX) n =1 (morph_multi g gX) n.
Proof.
move=> rR n f g fX gX eqfg; elim: n => [|n IHn] eqfgX p //=.
rewrite (eqfgX ord_max); apply: eq_morph_poly; apply: IHn => // i.
by rewrite (eqfgX (widen_ord (leqnSn n) i)).
Qed.

Lemma multi_initial : forall (rR : comRingType) n (f : multi n -> rR),
  ring_morphism f ->
  f =1 (morph_multi (f \o multiC n) (fgraph [ffun i => f 'X_i])) n.
Proof.
move=> rR; elim=> [|n IHn] f fM p /=.
  by rewrite /multiC [addn0 _]eq_axiomK.
rewrite (poly_initial fM) -/multi (_ : _`_n = f 'X); last first.
  rewrite (nth_fgraph_ord 0 ord_max) ffunE /multi_var /=; congr (f _).
  by move: (subnK _); rewrite subnn => eq_nn; rewrite (eq_axiomK eq_nn).
apply: eq_morph_poly => {p}p; rewrite {}IHn; last first.
  exact: comp_ringM (@polyC_morph _).
apply: eq_morph_multi => {p fM}[p | i].
  rewrite /multiC /=; congr f; move: (addn0 n.+1).
  by case: {-1 3 7 9}n / (addn0 n) => /= eqnn; rewrite (eq_axiomK eqnn).
rewrite nth_fgraph_ord (nth_fgraph_ord 0 (widen_ord (leqnSn n) i)) !ffunE.
congr (f _); symmetry; rewrite /multi_var /=; do 2!move: (subnK _).
rewrite leq_subS //=; move: {i}(i : nat) (n - _)%N => m i.
by case: {f}n / => /= eqnn; rewrite (eq_axiomK eqnn).
Qed.

End MultinomialDef.

Notation "''X_' i" := (multi_var _ i) : ring_scope.

(* An application : the Ashcbacher definition of the parity of *)
(* permutations, via the group action on the Van der Monde     *)
(* determinant polynomial.                                     *)
Section SignPerm.

Require Import finset groups perm zmodp morphisms.
Import GroupScope.
(* Open Scope ring_scope. *)

Let R := @Fp_field 3 is_true_true.

Variable T : finType.

Let n := #|T|.

Let fX (s : {perm T}) : seq (multi R n) :=
  fgraph [ffun x => 'X_(enum_rank (s x))].

Let to s := @morph_multi R _ (multiC n) (fX s) n.

Let VdM : multi R n :=
  (\prod_(ij : 'I_n * 'I_n | ij.1 < ij.2) ('X_ij.1 - 'X_ij.2))%R.

Definition odd_perm' s := to s VdM != VdM.

Lemma odd_perm'M : {morph odd_perm' : a b / a * b >-> a (+) b}.
Proof.
have to_morph : ring_morphism (to _).
  move=> s; apply: morph_multiM; exact: multiC_morph.
pose si (s : {perm T}) i := enum_rank (s (enum_val i)).
have siK: forall s, cancel (si s) (si s^-1).
  by move=> s i; rewrite /si !(enum_rankK, permK, enum_valK).
have toX : forall s i, to s 'X_i = 'X_(si s i).
  move=> s i; rewrite /to (morph_multiX _  (multiC_morph _ _)).
  by rewrite -tnth_nth tnth_fgraph ffunE.
have toC : forall s x, to s (multiC n x) = multiC n x.
  by move=> s x; rewrite /to (morph_multiC _  (multiC_morph _ _)).
have toM : forall s t, to (s * t) =1 to t \o to s.
  move=> /= s t q; rewrite multi_initial ?(multi_initial (comp_ringM _ _ )) //.
  apply: eq_morph_multi => {q}[q | i]; first by rewrite /= !toC.
  by rewrite !nth_fgraph_ord !ffunE /= !toX /si enum_rankK permM.

pose eq_sign (p1 p2 : multi R n) := {e : bool | p1 = (- 1) ^+ e * p2}%R.
suffices ss: forall s, eq_sign (to s VdM) VdM.
  move=> s t /=; rewrite /odd_perm' toM /=.
  case: (to s VdM =P VdM) => [-> // | ]; move/eqP.
  case: (ss s) => [[] ->]; rewrite ?mul1r ?eqxx // mulN1r ringM_opp //= negbK.
  case: (ss t) => [[] ->]; rewrite ?mul1r ?mulN1r ?opprK eqxx //.
  by move/negbTE.
pose pi (i j : 'I_n) := if i < j then (i, j) else (j, i).
have piC : forall i j, pi i j = pi j i.
  by move=> i j; rewrite /pi; case: ltngtP => //; move/ord_inj->.

have pi_lt: forall i j (p := pi i j), (p.1 < p.2) = (i != j).
  move=> i j; rewrite {1}/pi; case: ltnP => /=.
    by rewrite neq_ltn => ->.
  by rewrite ltn_neqAle eq_sym  andbC => ->.
pose psi s ij := pi (si s ij.1) (si s ij.2).
have psiK: forall s i j, psi s^-1 (psi s (i, j)) = pi i j.
  move=> s i j; rewrite {2}/psi {1}/pi fun_if /psi /= piC.
  by rewrite if_same !siK.
move=> s; rewrite {2}/VdM (reindex_onto (psi s) (psi s^-1)) /=; last first.
  by case=> /= i j ltij; rewrite -{1}[s]invgK psiK /pi ltij.
rewrite big_mkcond ringM_prod //= big_mkcond /=.
apply: (big_rel eq_sign); first by exists false; rewrite mul1r.
  move=> /= _ p1 _ p2 [e1 ->] [e2 ->]; exists (e1 (+) e2).
  by rewrite mulrCA !mulrA -signr_addb addbC.
case=> /= i j _; rewrite psiK pi_lt (inj_eq (can_inj (siK _))) /= /psi /pi.
case: ifP => lt_ij; last first.
  by exists false; rewrite lt_ij andbC -andbA andbN andbF mul1r.
rewrite neq_ltn {}lt_ij eqxx /=; move: (_ < _) => e; exists (~~ e).
rewrite ringM_sub // !toX; case: e; rewrite ?mulNr mul1r //=.
by rewrite oppr_add opprK addrC.
Qed.

Definition bool_groupMixin := FinGroup.Mixin addbA addFb addbb.
Canonical Structure bool_baseGroup :=
  Eval hnf in BaseFinGroupType bool_groupMixin.
Canonical Structure boolGroup := Eval hnf in FinGroupType addbb. 

Canonical Structure odd_perm'_morphism :=
  @Morphism _ _ setT _ (in2W odd_perm'M).

Lemma odd_tperm' : forall x y : T, odd_perm' (tperm x y) = (x != y).
Proof.
have to_morph : ring_morphism (to _).
  move=> s; apply: morph_multiM; exact: multiC_morph.
pose si (s : {perm T}) i := enum_rank (s (enum_val i)).
have toX : forall s i, to s 'X_i = 'X_(si s i).
  move=> s i; rewrite /to (morph_multiX _  (multiC_morph _ _)).
  by rewrite -tnth_nth tnth_fgraph ffunE.
move=> x y; case eq_xy: (x == y).
  have: tperm x y \in 'ker odd_perm' by rewrite (eqP eq_xy) tperm1 group1.
  by rewrite !inE /=; move/eqP.
have lt1n: 1 < n by rewrite /n (cardD1 y) (cardD1 x) !inE eq_xy.
pose i0 := Ordinal (ltnW lt1n); pose i1 := Ordinal lt1n.
pose x0 := enum_val i0; pose x1 := enum_val i1.
pose s0 := tperm x x0; pose s := (s0 * tperm y (s0 x1)).
have ->: x = s x0.
  rewrite permM /= permE /= (inj_eq (@perm_inj _ _)) tpermR eq_xy.
  by rewrite (inj_eq (@enum_val_inj _)).
have ->: y = s x1 by rewrite permM tpermR.
rewrite -tpermJ 2!odd_perm'M addbCA -!odd_perm'M mulgA {x y eq_xy s s0}mulgKV.
set t := tperm x0 x1; rewrite /odd_perm' -subr_eq0.
rewrite {2}/VdM (bigD1 (i0, i1)) //= big_mkcond /=.
rewrite ringM_prod // (bigD1 (i0, i1)) //= big_mkcond /=.
rewrite ringM_sub // !toX /si tpermL tpermR !enum_valK.
pose mi i := @morph_multi R R id (set_nth 0 [::] i 1%R) n.
have miM: ring_morphism (mi _) by move=> i; exact: morph_multiM.
rewrite -mulNr (addrC 'X_i0) oppr_add opprK -mulr_addr mulf_neq0 //.
  apply/eqP; move/(congr1 (mi 1%N)); move/eqP.
  by rewrite ringM_sub // ringM_0 // /mi !morph_multiX.
pose h ij := (tperm i0 i1 ij.1, ij.2 : 'I_n).
have hD: forall j : 'I_n, j > 1 -> tperm i0 i1 j = j.
  move=> j; rewrite ltn_neqAle lt0n -(eq_sym 0%N).
  by case/andP=> ne1j ne0j; exact: tpermD.
have sit: si t =1 tperm i0 i1.
  move=> j; rewrite /si !permE /= 2!(fun_if (@enum_rank _)) !enum_valK.
  by rewrite !(inj_eq (@enum_val_inj _)).
rewrite (reindex h) /=; last first.
  by exists h => [] [i j] _ /=; rewrite /h tpermK.
elim: (index_enum _) => [|[i j] e IHe].
  rewrite !big_nil; apply/eqP; move/(congr1 (mi 2)); apply/eqP.
  by rewrite ringM_add // ringM_0 // !(ringM_1 (miM _)).
rewrite !big_cons /= {1}/h /= !negb_andb /=; case eq_j1: (j == i1).
  by rewrite !orbF (eqP eq_j1) !ltnS !leqn0 !andbN !mul1r.
rewrite !orbT !andbT; case: (leqP j 1) => [| {eq_j1}lt_1j].
  by rewrite leq_eqVlt [_ == _]eq_j1 ltnS leqn0; move/eqnP->; rewrite !mul1r.
case: (leqP j i) => [le_ji | lt_ij].
  by rewrite ltnNge hD ?(leq_trans lt_1j) ?le_ji // !mul1r.
case: ifP => [_|]; last first.
  by case/idP; case: tpermP => //; rewrite ltnW.
rewrite ringM_sub // !toX !sit tpermK hD // -mulr_addr mulf_neq0 {IHe}//.
apply/eqP; move/(congr1 (mi j)); apply/eqP.
rewrite ringM_0 // ringM_sub // /mi !morph_multiX // !nth_set_nth /= !nth_nil.
by rewrite eqxx -if_neg neq_ltn lt_ij.
Qed.
  
End SignPerm.



Unset Implicit Arguments.
