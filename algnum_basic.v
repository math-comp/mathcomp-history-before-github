Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple div.
Require Import bigop prime finset fingroup ssralg finalg zmodp abelian.
Require Import matrix vector falgebra finfield action poly ssrint cyclotomic.
Require Import fieldext mxalgebra mxpoly.

Import GRing.Theory.
Import DefaultKeying GRing.DefaultPred.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section Integral.

Variable (F : fieldType) (L0 : fieldExtType F) (A : pred L0) (K L : {subfield L0}).

Hypothesis Asubr : subring_closed A.

Definition integral l := exists p, [/\ p \is monic, p \is a polyOver A & root p l].
Definition int_closed := {in A, forall a b, integral (a / b) -> (a / b) \in A}.
Definition int_closure := fun l => l \in L /\ integral l.
Definition is_frac_field := {subset A <= K} /\ exists f, forall k, f k != 0 /\
  (k \in K -> f k \in A /\ f k * k \in A).

Hypothesis AfracK : is_frac_field.

Lemma frac_field_alg_int : exists f, forall l, [/\ f l != 0, f l \in A & integral (f l * l)].
Proof.
have [Aid _ Amcl] := Asubr; have Amulr : mulr_closed A := Asubr.
have [AsubK [f /all_and2-[fH0 /(_ _)/all_and2-/all_and2-[fHa fHk]]]] := AfracK.
pose g := fun l => let p := minPoly K l in \prod_(i < size p) f p`_i; exists g => l.
pose p := minPoly K l; pose n := (size p).-1.
pose s := mkseq (fun i => p`_i * (g l) ^+ (n - i)%N) (size p).
have kI (i : 'I_(size p)) : p`_i \in K by apply/all_nthP => //; apply/minPolyOver.
have glA : g l \in A by rewrite/g; elim/big_ind: _ => // i _; apply/fHa.
have pmon: p`_n = 1 by have /monicP := monic_minPoly K l.
have an1: nth 0 s n = 1 by rewrite /n nth_mkseq ?pmon ?mul1r ?subnn ?size_minPoly. 
have eqPs: (Poly s) = s :> seq L0.
  by rewrite (PolyK (c := 0)) // -nth_last size_mkseq an1 oner_neq0.
have ilen i : i < size p -> i <= n by move => iB; rewrite /n -ltnS prednK // size_minPoly.
split => //; first by apply/prodf_neq0 => i _.
exists (Poly s); split; last first; last by rewrite monicE lead_coefE eqPs // size_mkseq an1.
  rewrite /root -(mulr0 ((g l) ^+ n)); have <- := minPolyxx K l.
  rewrite !horner_coef eqPs size_mkseq big_distrr; apply/eqP/eq_bigr => i _.
  rewrite nth_mkseq // exprMn //=; rewrite !mulrA; congr (_ * _); rewrite -mulrA mulrC.
  by congr (_ * _); rewrite -exprD subnK ?ilen.
apply/(all_nthP 0) => i; rewrite eqPs size_mkseq => iB; rewrite nth_mkseq //.
  have := ilen _ iB; rewrite leq_eqVlt => /orP.
  case; first by move /eqP ->; rewrite subnn pmon mulr1.
  rewrite -subn_gt0 => {pmon ilen eqPs an1} /prednK <-; rewrite exprS mulrA /= Amcl ?rpredX //.
  rewrite /g (bigD1 (Ordinal iB)) //= mulrA; apply/Amcl.
    by rewrite mulrC; apply/fHk/(kI (Ordinal iB)).
  by rewrite rpred_prod => // j _; apply/fHa. 
Qed.

Lemma int_clos_incl : forall a, a \in A -> integral a.
Proof.
move=> a ainA; exists ('X - a%:P); rewrite monicXsubC root_XsubC.
rewrite polyOverXsubC => //; by exact Asubr.
Qed.

Lemma intPl (I : eqType) G (r : seq I) l : has (fun x => G x != 0) r ->
  (forall e, e \in r -> {f | \sum_(e' <- r) f e' * G e' = l * G e & forall e', f e' \in A}) ->
  integral l.
Proof.
have Aaddr : addr_closed A := Asubr; have Amulr : mulr_closed A := Asubr.
have Aoppr : oppr_closed A := Asubr; have [Aid _ _] := Asubr.
move => rn gen; pose s := in_tuple r; pose g j := gen (tnth s j) (mem_tnth j s).
pose f j := sval (g j); pose fH j := svalP (g j).
pose M := \matrix_(i, j < size r) f j (tnth s i).
exists (char_poly M); rewrite char_poly_monic; split => //.
  apply/rpred_sum => p _; apply/rpredM; first by apply/rpredX; rewrite rpredN polyOverC.
  apply/rpred_prod => i _; rewrite !mxE /= rpredB ?rpredMn ?polyOverX ?polyOverC ?/f //.
  by have [_ fH2] := fH (perm.PermDef.fun_of_perm p i).
rewrite -eigenvalue_root_char; apply/eigenvalueP; move: rn => /hasP[x] /(nthP x)[k kB <- xn].
exists (\row_(i < size r) G (tnth s i)); last first.
  move: xn; apply/contra => /eqP/matrixP-v0; have := v0 0 (Ordinal kB).
  by rewrite !mxE (tnth_nth x) => <-.
rewrite -rowP => j; rewrite !mxE; have [fH1 _] := fH j; rewrite -fH1 (big_nth x) big_mkord.
by apply/eq_bigr => /= i _; rewrite /M !mxE (tnth_nth x) mulrC.
Qed.

Lemma intPr l : integral l -> exists r : seq L0,
  [/\ r != nil, all A r & \sum_(i < size r) r`_i * l ^+ i = l ^+ (size r)].
Proof.
move => [p [pm pA pr]]; pose n := size p; pose r := take n.-1 (- p).
have ps : n > 1.
  rewrite ltnNge; apply/negP => /size1_polyC pc; rewrite pc in pr pm => {pc}.
  move: pr => /rootP; rewrite hornerC => pc0.
  by move: pm; rewrite monicE lead_coefC pc0 eq_sym oner_eq0.
have rs : size r = n.-1 by rewrite /r size_takel // size_opp leq_pred.
exists r; split.
  apply/eqP => /nilP; rewrite /nilp /r size_takel; last by rewrite size_opp leq_pred.
  by rewrite -subn1 subn_eq0 leqNgt ps.
  have : - p \is a polyOver A by rewrite rpredN //; exact Asubr.
  by move => /allP-popA; apply/allP => x /mem_take /popA.
move: pr => /rootP; rewrite horner_coef -(prednK (n := size p)); last by rewrite ltnW.
rewrite big_ord_recr /= rs; have := monicP pm; rewrite /lead_coef => ->; rewrite mul1r => /eqP.
rewrite addrC addr_eq0 -sumrN => /eqP => ->; apply/eq_bigr => i _; rewrite /r nth_take //.    
by rewrite coefN mulNr.
Qed.

Lemma int_subring_closed a b : integral a -> integral b ->
  integral (a - b) /\ integral (a * b).
Proof.
have [A0 _ ] := (Asubr : zmod_closed A); have [A1 Asubr2 Amulr2] := Asubr.
move => /intPr[ra [/negbTE-ran raA raS]] /intPr[rb [/negbTE-rbn rbA rbS]].
pose n := size ra; pose m := size rb; pose r := Finite.enum [finType of 'I_n * 'I_m].
pose G (z : 'I_n * 'I_m) := let (k, l) := z in a ^ k * b ^l.
have [nz mz] : 0 < n /\ 0 < m.
  by rewrite !lt0n; split; apply/negP; move => /nilP/eqP; rewrite ?ran ?rbn.
have rnn : has (fun x => G x != 0) r.
  apply/hasP; exists (Ordinal nz, Ordinal mz); first by rewrite /r -enumT mem_enum.
  by rewrite /G mulr1 oner_neq0.
pose h s i : 'I_(size s) -> L0 := fun k => if (i != size s) then (i == k)%:R else s`_k.
pose f i j (z : 'I_n * 'I_m) : L0 := let (k, l) := z in h ra i k * h rb j l.
have fA i j : forall z, f i j z \in A.
  have hA s k l : all A s -> h s k l \in A.
    move => /allP-sa; rewrite /h; case (eqVneq k (size s)) => [/eqP ->|->].
      by apply/sa/mem_nth. 
    by case (eqVneq k l) => [/eqP ->|/negbTE ->].
  by move => [k l]; rewrite /f; apply/Amulr2; apply/hA.
have fS i j : (i <= n) -> (j <= m) -> \sum_(z <- r) f i j z * G z = a ^ i * b ^ j.
  have hS s k c : (k <= size s) -> \sum_(l < size s) s`_l * c ^ l = c ^ (size s) ->
    \sum_(l < size s) h s k l * c ^ l = c ^ k.
    move => kB sS; rewrite /h; case (eqVneq k (size s)) => [->|kn {sS}]; first by rewrite eqxx.
    rewrite kn; rewrite leq_eqVlt (negbTE kn) /= in kB => {kn}.
    rewrite (bigD1 (Ordinal kB)) //= eqxx mul1r /= -[RHS]addr0; congr (_ + _).
    by apply/big1 => l; rewrite eq_sym => kl; have : k != l := kl => /negbTE ->; rewrite mul0r.
  move => iB jB; rewrite -(hS ra i a) // -(hS rb j b) // mulr_suml.
  rewrite (eq_bigr (fun k => \sum_(l < m) (h ra i k * a ^ k) * (h rb j l * b ^ l))).
    rewrite pair_bigA; apply eq_bigr => [[k l] _]; rewrite !mulrA; congr (_ * _).
    by rewrite -!mulrA [in h rb j l * a ^ k] mulrC.
  by move => k _; rewrite mulr_sumr.
pose fB i j z := f i.+1 j z - f i j.+1 z; pose fM i j z := f i.+1 j.+1 z.
have fBA i j z : fB i j z \in A by rewrite /fB Asubr2.
have fBM i j z : fM i j z \in A by rewrite /fM.
split; apply/(@intPl _ G r) => //= [[i j] _]; [exists (fB i j) | exists (fM i j)] => //.
  rewrite /fB [in RHS]/G mulrBl mulrA -exprS [in b * (a ^ i * b ^ j)] mulrC -mulrA -exprSr.
  rewrite -(fS _ _ (ltnW (ltn_ord i))) // -(fS _ _ _ (ltnW (ltn_ord j))) //.
  by rewrite -sumrB; apply/eq_bigr => [[k l] _]; apply/mulrBl.
by rewrite /fM [in RHS]/G mulrA [in (a * b) * a ^ i] mulrC mulrA -exprSr -mulrA -exprS -!fS.
Qed.

Lemma int_zmod_closed a b : integral a -> integral b -> integral (a - b).
Proof. by move => aI bI; have [Azmod] := int_subring_closed aI bI. Qed.

Lemma int_mulr_closed a b : integral a -> integral b -> integral (a * b).
Proof. by move => aI bI; have [_] := int_subring_closed aI bI. Qed.

End Integral.

Section Trace.

Variable (F : fieldType) (L0 : fieldExtType F) (L : {subfield L0}).

Implicit Types k l : L0.

Definition tr : L0 -> L0 -> F := fun l k =>
  let X := vbasis L in
    let M := \matrix_(i, j) coord X i (l * k * X`_j)
      in \tr M.

Fact tr_is_scalar l : scalar (tr l).
Proof.
move => c a b; rewrite /tr  -!linearP /=; congr (\tr _); apply/matrixP => i j; rewrite !mxE.
by rewrite mulrDr mulrDl linearD /= -scalerAr -scalerAl linearZ.
Qed.

Canonical tr_additive l := Additive (@tr_is_scalar l).
Canonical tr_linear l := AddLinear (@tr_is_scalar l).
  
Lemma tr_sym : commutative tr.
Proof. by move => a b; rewrite /tr mulrC. Qed.

Lemma tr_int A k l : subring_closed A -> int_closed A -> is_frac_field A 1%AS ->
  integral A k -> integral A l -> (tr k l)%:A \in A.
Proof. admit. Qed.

Section NDeg.

Variable (vT : vectType F) (R : ringType) (Q : vT -> vT -> R) (V : {vspace vT}).

Definition ndeg := forall (l : vT), l != 0 -> l \in V ->
  exists (k : vT), k \in V /\ Q l k != 0.

End NDeg.

Variable (U : {vspace L0}).
Let m := \dim U.
Variable (X : m.-tuple L0).

Lemma dual_basis_def :
  {Y : m.-tuple L0 | ndeg tr U -> basis_of U X -> basis_of U Y /\
  forall (i : 'I_m), tr X`_i Y`_i = 1 /\
  forall (j : 'I_m), j != i -> tr X`_i Y`_j = 0}.
Proof.
pose Uv := subvs_vectType U; pose Fv := subvs_FalgType (1%AS : {aspace L0}); 
pose HomV := [vectType _ of 'Hom(Uv, Fv)].
pose tr_sub : Uv -> Uv -> Fv := fun u v => (tr (vsval u) (vsval v))%:A.
have HomVdim : \dim {:HomV} = m by rewrite dimvf /Vector.dim /= /Vector.dim /= dimv1 muln1.
have [f fH] : {f : 'Hom(Uv, HomV) | forall u, f u =1 tr_sub u}.
  have lf1 u : linear (tr_sub u) by move => c x y; rewrite /tr_sub linearP scalerDl scalerA.
  have lf2 : linear (fun u => linfun (Linear (lf1 u))).
    move => c x y; rewrite -lfunP => v; rewrite add_lfunE scale_lfunE !lfunE /= /tr_sub.
    by rewrite tr_sym linearP scalerDl scalerA /=; congr (_ + _); rewrite tr_sym.
  by exists (linfun (Linear lf2)) => u v; rewrite !lfunE.
have [Xdual XdualH] : {Xdual : m.-tuple HomV |
  forall (i : 'I_m) u, Xdual`_i u = (coord X i (vsval u))%:A}.
  have lg (i : 'I_m) : linear (fun u : Uv => (coord X i (vsval u))%:A : Fv).
    by move => c x y; rewrite linearP /= scalerDl scalerA.
  exists (mktuple (fun i => linfun (Linear (lg i)))) => i u.
  by rewrite -tnth_nth tnth_mktuple !lfunE.
have [finv finvH] : {finv : 'Hom(HomV, L0) | finv =1 vsval \o (f^-1)%VF}.
  by exists (linfun vsval \o f^-1)%VF => u; rewrite comp_lfunE lfunE. 
pose Y := map_tuple finv Xdual; exists Y => Und Xb.
have Ydef (i : 'I_m) : Y`_i = finv Xdual`_i by rewrite -!tnth_nth tnth_map.
have XiU (i : 'I_m) : X`_i \in U by apply/(basis_mem Xb)/mem_nth; rewrite size_tuple.
have Xii (i : 'I_m) : coord X i X`_i = 1%:R.
  by rewrite coord_free ?eqxx //; exact (basis_free Xb).
have Xij (i j : 'I_m) : j != i -> coord X i X`_j = 0%:R.
  by rewrite coord_free; [move => /negbTE -> | exact (basis_free Xb)].
have Xdualb : basis_of fullv Xdual.
  suffices Xdualf : free Xdual.
    rewrite /basis_of Xdualf andbC /= -dimv_leqif_eq ?subvf // eq_sym HomVdim.
    by move: Xdualf; rewrite /free => /eqP => ->; rewrite size_tuple.
  apply/freeP => k sX i.  
  suffices: (\sum_(i < m) k i *: Xdual`_i) (vsproj U X`_i) = (k i)%:A.
    by rewrite sX zero_lfunE => /esym /eqP; rewrite scaler_eq0 oner_eq0 orbF => /eqP.
  rewrite sum_lfunE (bigD1 i) //= scale_lfunE XdualH vsprojK // Xii.
  rewrite scaler_nat -[RHS]addr0; congr (_ + _); apply/big1 => j; rewrite eq_sym => ineqj.
  by rewrite scale_lfunE XdualH vsprojK ?Xij // scaler_nat scaler0.
have finj : (lker f = 0)%VS.
  apply/eqP; rewrite -subv0; apply/subvP=> u; rewrite memv_ker memv0 => /eqP-f0.
  apply/contraT => un0; have {un0} [k [kiU /negP[]]] := Und (vsval u) un0 (subvsP u).
  have /eqP := fH u (vsproj U k).
  by rewrite /tr_sub vsprojK // f0 zero_lfunE eq_sym scaler_eq0 oner_eq0 orbF.
have flimg : limg f = fullv.
  apply/eqP; rewrite -dimv_leqif_eq ?subvf // limg_dim_eq; last by rewrite finj capv0.
  by rewrite HomVdim dimvf /Vector.dim.
have finvK : cancel finv (f \o vsproj U).
  by move => u; rewrite finvH /= vsvalK; apply/limg_lfunVK; rewrite flimg memvf.
have finv_inj : (lker finv = 0)%VS by apply/eqP/lker0P/(can_inj finvK).
have finv_limg : limg finv = U. 
  apply/eqP; rewrite -dimv_leqif_eq; first by rewrite limg_dim_eq ?HomVdim ?finv_inj ?capv0.   
  by apply/subvP => u /memv_imgP [h _] ->; rewrite finvH subvsP.
have Xt (i j : 'I_m) : (f \o vsproj U) Y`_j (vsproj U X`_i) = (tr Y`_j X`_i)%:A.
  by rewrite fH /tr_sub !vsprojK // Ydef finvH subvsP.
have Xd (i j : 'I_m) : (f \o vsproj U) Y`_j (vsproj U X`_i) = Xdual`_j (vsproj U X`_i).
  by rewrite Ydef finvK.
have Ainj := fmorph_inj [rmorphism of in_alg Fv].
split => [| i]; first by rewrite -{1}finv_limg limg_basis_of // capfv finv_inj.
split => [| j]; first by have := Xt i i; rewrite tr_sym Xd XdualH vsprojK // Xii => /Ainj.
by rewrite eq_sym => inj; have := Xt i j; rewrite tr_sym Xd XdualH vsprojK // Xij // => /Ainj.
Qed.

Definition dual_basis : m.-tuple L0 := sval dual_basis_def.

Hypothesis Und : ndeg tr U.
Hypothesis Xb : basis_of U X.

Lemma dualb_basis : basis_of U dual_basis.
Proof. have [Yb _] := svalP dual_basis_def Und Xb; exact Yb. Qed.

Lemma dualb_orth :
  forall (i : 'I_m), tr X`_i dual_basis`_i = 1 /\
  forall (j : 'I_m), j != i -> tr X`_i dual_basis`_j = 0.
Proof. by have [_] := svalP dual_basis_def Und Xb. Qed.

End Trace.

Section TraceFieldOver.

Variable (F : fieldType) (L0 : fieldExtType F) (K L : {subfield L0}).

Implicit Types k l : L0.

Let K' := subvs_fieldType K.
Let L0' := fieldOver_fieldExtType K.

Definition trK : L0 -> L0 -> K' := tr (aspaceOver K L).

Lemma trK_ndeg (U : {aspace L0}) : (K <= U)%VS ->
  (ndeg trK U <-> ndeg (tr (aspaceOver K L)) (aspaceOver K U)).
Proof.
move => UsubL; have UU' : aspaceOver K U =i U := mem_aspaceOver UsubL.
split => [ndK l lnz | nd l lnz].
  by rewrite UU' => liU; have [k] := ndK l lnz liU; exists k; rewrite UU'.
by rewrite -UU' => liU'; have [k] := nd l lnz liU'; exists k; rewrite -UU'.
Qed.

End TraceFieldOver.

Section BasisLemma.

Section Modules.

Variable (F : fieldType) (L0 : fieldExtType F) (A : pred L0).

Implicit Types M N : L0 -> Prop.

Definition module M := M 0 /\ forall a k l, a \in A -> M k -> M l -> M (a * k - l).
Definition span_mod X m := exists2 r : (size X).-tuple L0,
  all A r & m = \sum_(i < size X) r`_i * X`_i.
Definition submod M N := forall m, M m -> N m.
Definition basis_of_mod M X := free X /\ submod M (span_mod X) /\ forall m, m \in X -> M m.
Definition ideal N := submod N A /\ module N.
Definition PID := forall (N : L0 -> Prop), ideal N ->
  exists2 a, N a & forall v, N v -> exists2 d, d \in A & d * a = v.

Variable L : {subfield L0}.

Hypothesis Asubr : subring_closed A.
Hypothesis AsubL : {subset A <= L}.

Lemma int_mod_closed : module (int_closure A L).
Proof.
have [A0 _] : zmod_closed A := Asubr; split.
  by rewrite /int_closure mem0v; split => //; apply/int_clos_incl.
move => a k l aA [kI kL] [lI lL]; split; first by rewrite rpredB ?rpredM //; apply/AsubL.
by apply/int_zmod_closed => //; apply/int_mulr_closed => //; apply/int_clos_incl. 
Qed.

End Modules.

Variable (F0 : fieldType) (E : fieldExtType F0) (I : pred E) (Ifr K : {subfield E}).

Hypothesis Isubr : subring_closed I.
Hypothesis Iint : int_closed I.
Hypothesis Ipid : PID I.
Hypothesis Ifrac : is_frac_field I Ifr. 
Hypothesis IsubK : {subset I <= K}.
Hypothesis Knd :  ndeg (trK Ifr K) K.

Lemma basis_lemma : exists X : (\dim_Ifr K).-tuple E, basis_of_mod I (int_closure I K) X.
Proof.
suffices FisK (F : fieldType) (L0 : fieldExtType F) (A : pred L0) (L : {subfield L0}) :
  subring_closed A -> int_closed A -> PID A -> is_frac_field A 1 -> ndeg (tr L) L ->
  exists2 X, size X == \dim L & basis_of_mod A (int_closure A L) X.
  have [Isub [f /all_and2[fH0 fHk]]] := Ifrac; pose F := subvs_fieldType Ifr;
  pose L0 := fieldOver_fieldExtType Ifr; pose L := aspaceOver Ifr K.
  have Ifrsub : (Ifr <= K)%VS.
    apply/subvP=> x /fHk-[fHx fHxx]; rewrite -(mulKf (fH0 x) x).
    by apply/memvM; rewrite ?memvV; apply/IsubK.
  have LK : L =i K := mem_aspaceOver Ifrsub; have Lnd : ndeg (tr L) L by rewrite -trK_ndeg. 
  have Ifrac1 : is_frac_field (I : pred L0) 1.
    split; first by move => a; rewrite /= trivial_fieldOver; apply/Isub.
    by exists f => k; split => //; rewrite trivial_fieldOver => /fHk.
  have [X Xsize [Xf [Xs Xi]]] := FisK _ L0 _ _ Isubr Iint Ipid Ifrac1 Lnd.
  rewrite -dim_aspaceOver => //; have /eqP <- := Xsize; exists (in_tuple X); split; last first.
    split => m; last by move => /Xi; rewrite /int_closure LK.  
    by rewrite /int_closure -LK; move => /Xs.
  move: Xf; rewrite -{1}(in_tupleE X); move => /freeP-XfL0; apply/freeP => k.
  have [k' kk'] : exists k' : 'I_(size X) -> F, forall i, (k i)%:A = vsval (k' i).
    by exists (fun i => vsproj Ifr (k i)%:A) => i; rewrite vsprojK ?rpredZ ?mem1v.
  pose Ainj := fmorph_inj [rmorphism of in_alg E].
  move => kS i; apply/Ainj => {Ainj} /=; rewrite scale0r kk'; apply/eqP.
  rewrite raddf_eq0; last by apply/subvs_inj.
  by apply/eqP/XfL0; rewrite -{3}kS => {i}; apply/eq_bigr => i _; rewrite -[RHS]mulr_algl kk'.
move => Asubr Aint Apid Afrac1 Lnd; pose n := \dim L; have Amulr : mulr_closed A := Asubr.
have [A0 _] : zmod_closed A := Asubr; have [Asub1 _] := Afrac1.
have AsubL : {subset A <= L} by move => a /Asub1; exact (subvP (sub1v L) a).
have [b1 [b1B b1H]] : exists (b1 : n.-tuple L0), [/\ basis_of L b1 &
  forall i : 'I_n, integral A b1`_i].
  pose b0 := vbasis L; have [f /all_and3-[fH0 fHa fHi]] := frac_field_alg_int Asubr Afrac1.
  pose d := \prod_(i < n) f b0`_i; pose b1 := map_tuple (amulr d) b0.
  exists b1; split; last first => [i|].
    rewrite (nth_map 0) /d; last by rewrite size_tuple.
    rewrite lfunE /= (bigD1 i) //= mulrA; apply/int_mulr_closed => //; first by rewrite mulrC.
    by apply/int_clos_incl => //; rewrite rpred_prod.
  have dun : d \is a GRing.unit by rewrite unitfE /d; apply/prodf_neq0 => i _.
  have lim : (amulr d @: L = L)%VS.
    have dinA : d \in A by rewrite rpred_prod.
    rewrite limg_amulr; apply/eqP; rewrite -dimv_leqif_eq; first by rewrite dim_cosetv_unit.
    by apply/prodv_sub => //; apply/AsubL.
  rewrite -lim limg_basis_of //; last by apply/vbasisP. 
  by have /eqP -> := lker0_amulr dun; rewrite capv0.
have [b2 [/andP[/eqP-b2s b2f] b2H]] : exists (b2 : n.-tuple L0), [/\ basis_of L b2 &
  forall b, b \in L -> integral A b -> forall i, (coord b2 i b)%:A \in A].
  pose b2 := dual_basis L b1; have b2B := dualb_basis Lnd b1B; exists b2; rewrite b2B.
  split => // b biL bint i; suffices <-: tr L b1`_i b = coord b2 i b by rewrite tr_int.
  have -> : tr L b1`_i b = \sum_(j < n) coord b2 j b * tr L b1`_i b2`_j.
    by rewrite {1}(coord_basis b2B biL) linear_sum; apply/eq_bigr => j _; rewrite linearZ.
  rewrite (bigD1 i); have [oi oj //] := dualb_orth Lnd b1B i; rewrite /= oi mulr1 -[RHS]addr0.
  by congr (_ + _); apply/big1 => j jneqi; rewrite (oj j jneqi) mulr0.
have Mbasis k (X : k.-tuple L0) M : free X -> module A M -> submod M (span_mod A X) ->
  exists B, basis_of_mod A M B.
  move: k X M; elim => [X M _ _ Ms | k IH X M Xf [M0 Mm] Ms].
    by exists [::]; rewrite /basis_of_mod nil_free; move: Ms; rewrite tuple0. 
  pose X1 := [tuple of behead X]; pose v := thead X.
  pose M1 := fun m => M m /\ coord X ord0 m = 0.
  pose M2 := fun (a : L0) => exists2 m, M m & (coord X ord0 m)%:A = a.
  have scr r m : r \in A -> exists c, r * m = c *: m.
    by move => /Asub1/vlineP[c ->]; exists c; rewrite mulr_algl.
  have span_coord m : M m -> exists r : (k.+1).-tuple L0,
    [/\ all A r, m = \sum_(i < k.+1) r`_i * X`_i & forall i, (coord X i m)%:A = r`_i].
    have seqF (s : seq L0) : all A s -> exists s', s = [seq c%:A | c <- s'].
      elim: s => [_| a l IHl /= /andP[/Asub1/vlineP[c ->]]]; first by exists [::].
      by move => /IHl[s' ->]; exists (c :: s').
    move => mM; have := Ms m mM; rewrite /span_mod !size_tuple; move => [r rA rS].
    exists r; split => //; have [rF rFr] := seqF r rA => {seqF}; rewrite rFr in rA.
    have rFs : size rF = k.+1 by rewrite -(size_tuple r) rFr size_map.
    have -> : m = \sum_(i < k.+1) rF`_i *: X`_i.
      by rewrite rS; apply/eq_bigr => i _; rewrite rFr (nth_map 0) ?rFs // mulr_algl.
    by move => i; rewrite coord_sum_free // rFr (nth_map 0) ?rFs. 
  have [B1 [B1f [B1s B1A]]] : exists B1, basis_of_mod A M1 B1.
    have X1f : free X1 by move: Xf; rewrite (tuple_eta X) free_cons => /andP[_].
    apply/(IH X1) => //.
      rewrite /module /M1 linear0; split => // a x y aA [xM xfc0] [yM yfc0].
      have := Mm a x y aA xM yM; move: aA => /Asub1/vlineP[r] ->; rewrite mulr_algl => msc.
      by rewrite /M1 linearB linearZ /= xfc0 yfc0 subr0 mulr0.
    move => m [mM mfc0]; have := span_coord m mM; move => [r [rA rS rC]].
    move: mfc0 (rC 0) ->; rewrite scale0r; move => r0; rewrite /span_mod size_tuple.
    exists [tuple of behead r]; first by apply/allP => a /mem_behead/(allP rA).
    by rewrite rS big_ord_recl -r0 mul0r add0r; apply/eq_bigr => i _; rewrite !nth_behead.
  have [a [w wM wC] aG] : exists2 a, M2 a & forall v, M2 v -> exists2 d, d \in A & d * a = v.
    apply/Apid; split.
      move => c [m mM <-]; have := span_coord m mM; move => [r [/all_nthP-rA _ rC]].
      by move: rC ->; apply/rA; rewrite size_tuple.
    split; first by exists 0 => //; rewrite linear0 scale0r.
    move => c x y cA [mx mxM mxC] [my myM myC]; have := Mm c mx my cA mxM myM. 
    move: cA => /Asub1/vlineP[r] ->; rewrite !mulr_algl => mC.
    by exists (r *: mx - my) => //; rewrite linearB linearZ /= scalerBl -scalerA mxC myC.
  pose Ainj := fmorph_inj [rmorphism of in_alg L0].
  have mcM1 m : M m -> exists2 d, d \in A & d * a = (coord X 0 m)%:A.
    by move => mM; apply/aG; exists m.
  case: (eqVneq a 0) => [| an0].
    exists B1; split => //; split => [m mM |]; last by move => m /B1A[mM].
    apply/B1s; split => //; apply/Ainj => /=; have [d _ <-] := mcM1 m mM.
    by rewrite a0 mulr0 scale0r.      
  exists (w :: B1); split.
    rewrite free_cons B1f andbT; move: an0; apply/contra; move: wC <-.
    rewrite -(in_tupleE B1); move => /coord_span ->; apply/eqP.
    rewrite linear_sum big1 ?scale0r => //= i _; rewrite linearZ /=.
    by have [_] := B1A B1`_i (mem_nth 0 (ltn_ord _)) => ->; rewrite mulr0.
  split => [m mM | m]; last by rewrite in_cons; move => /orP; case => [/eqP ->|/B1A[mM]].
  have [d dA dam] := mcM1 m mM; have mdwM1 : M1 (m - d * w).
    split; [have Mdwm := Mm d w m dA wM mM; have := Mm _ _ _ A0 Mdwm Mdwm |].
      by rewrite mul0r sub0r opprB.
    move: dA dam => /Asub1/vlineP[r] -> {d}; rewrite !mulr_algl linearB linearZ /= => rac.
    by apply/Ainj => /=; rewrite scalerBl -scalerA wC rac subrr scale0r.
  have [r rA rS] := B1s _ mdwM1; exists [tuple of d :: r]; first by rewrite /= rA andbT.
  by move: rS => /eqP; rewrite subr_eq addrC => /eqP ->; rewrite /= big_ord_recl.
have [X Xb] : exists X, basis_of_mod A (int_closure A L) X.
  apply/(Mbasis _ b2 _ b2f) => [| m [mL mI]]; first by apply/int_mod_closed.
  pose r : n.-tuple L0 := [tuple (coord b2 i m)%:A | i < n]; rewrite /span_mod size_tuple.
  exists r; have rci (i : 'I_n) : r`_i = (coord b2 i m)%:A by rewrite -tnth_nth tnth_mktuple.
    apply/(all_nthP 0) => i; rewrite size_tuple; move => iB.
    by have -> := rci (Ordinal iB); apply/b2H. 
  move: mL; rewrite -b2s; move => /coord_span ->; apply/eq_bigr => i _.
  by rewrite rci mulr_algl.
exists X => //; move: Xb => [/eqP-Xf [Xs Xg]]; rewrite -Xf eqn_leq; apply/andP; split.
  by apply/dimvS/span_subvP => m /Xg[mL _].
have /andP[/eqP-b1s _] := b1B; rewrite -b1s; apply/dimvS/span_subvP => b /tnthP-[i ->] {b}.
rewrite (tnth_nth 0); have [r /all_tnthP-rA ->] : span_mod A X b1`_i.
  by apply/Xs; rewrite /int_closure (basis_mem b1B) ?mem_nth ?size_tuple => //.
apply/rpred_sum => j _; have := rA j; rewrite (tnth_nth 0); move => /Asub1/vlineP[c ->].
by rewrite mulr_algl; apply/rpredZ/memv_span/mem_nth. 
Qed.

End BasisLemma.