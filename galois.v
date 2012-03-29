Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
Require Import tuple finfun bigop ssralg poly polydiv.
Require Import finset fingroup zmodp morphism perm quotient cyclic.
Require Import matrix mxalgebra vector falgebra fieldext separable.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope ring_scope.
Import GRing.Theory.

(* This should be moved to vector.v *)

Section Eigenspace.

Variable (K: fieldType) (V : vectType K) (f:'End(V)) (lambda:K).

Definition eigenspace := lker (f - lambda *: \1%VF).

Lemma eigenspaceIn : forall x, (x \in eigenspace) = (f x == lambda *: x) .
Proof.
move => x.
by rewrite memv_ker add_lfunE opp_lfunE scale_lfunE GRing.subr_eq0 id_lfunE.
Qed.

Lemma eigensubspaceImage :  forall vs, 
  (vs <= eigenspace)%VS -> (f @: vs <= vs)%VS.
Proof.
move => vs.
move/subvP => Hvs.
apply/subvP => x.
case/memv_imgP => y Hy ->.
move/Hvs:(Hy).
rewrite eigenspaceIn.
move/eqP ->.
by apply: memvZ.
Qed.

Lemma eigensubspaceImageEq :
 forall vs, (lambda != 0) -> (vs <= eigenspace)%VS -> (f @: vs = vs)%VS.
Proof.
move => vs Hl Hvs.
apply: subv_anti.
apply/andP.
split; first by apply: eigensubspaceImage.
move/subvP: Hvs => Hvs.
apply/subvP => x Hx.
apply/memv_imgP.
have Hlx : (lambda^-1 *: x \in vs) by rewrite memvZ.
exists (lambda^-1 *: x) => //.
move/Hvs: Hlx.
rewrite eigenspaceIn.
move/eqP ->.
by rewrite scalerA divff // scale1r.
Qed.

End Eigenspace.

Section Galois.

Variable F0 : fieldType.
Variable L : fieldExtType F0.

Let F : {subfield L} := aspace1 _.

Section Definitions.

Variables (K E: {vspace L}).

(* Should I make this canonical by setting fixing (f @: E)^C ? *)
Definition kHom : pred 'End(L) :=
  fun f => (K <= eigenspace f 1)%VS &&
  (all (fun v1 => all (fun v2 => f (v1 * v2) == f v1 * f v2) (vbasis E))
       (vbasis E)).

Lemma kHomP (f : 'End(L)) :
 reflect ((forall x, x \in K -> f x = x) /\
          (forall x y, x \in E -> y \in E -> f (x * y) = f x * f y))
 (kHom f).
Proof.
apply: (iffP andP); case; last first.
 move => HK HE.
 split.
  apply/subvP => v Hv.
  by rewrite eigenspaceIn scale1r HK.
 apply/allP => x; move/vbasis_mem => Hx.
 apply/allP => y; move/vbasis_mem => Hy.
 apply/eqP.
 by apply: HE.
move/subvP => HK.
move/all_nthP => HE.
split.
 move => x Hx.
 apply/eqP.
 by rewrite -{2}[x]scale1r -eigenspaceIn HK.
move => x y.
do 2 move/coord_vbasis ->.
rewrite mulr_suml ![f _]linear_sum mulr_suml.
apply: eq_bigr => i _ /=.
rewrite !mulr_sumr linear_sum.
apply: eq_bigr => j _ /=.
rewrite !linearZ /= -!scalerAr -!scalerAl 2!linearZ /=; congr (_ *: (_ *: _)).
by apply/eqP/(all_nthP 0 (HE 0 _ _)); rewrite size_tuple.
Qed.

Lemma kHom1 : kHom \1%VF.
Proof. apply/kHomP. by split; move => ? ?; rewrite !id_lfunE. Qed.

Variable (f : 'End(L)).

Lemma kHomFixedPoly p : kHom f -> p \is a polyOver K -> map_poly f p = p.
Proof.
case/kHomP => HK _ /polyOverP Hp.
by apply/polyP => i; rewrite coef_map /= HK ?Hp.
Qed.

Definition kAut : pred 'End(L) := fun f => kHom f && (f @: E == E)%VS.

Fact kHomExtendF_subproof x y :
  linear (fun z => (map_poly f (poly_for_Fadjoin E x z)).[y]).
Proof.
move=> k a b; rewrite linearP /= raddfD hornerE; congr (_ + _).
rewrite -[rhs in _ = rhs]mulr_algl -hornerZ /=; congr _.[_].
by apply/polyP => i; rewrite !(coefZ, coef_map) /= !mulr_algl linearZ.
Qed.
Definition kHomExtend x y := linfun (Linear (kHomExtendF_subproof x y)).

Lemma kHomExtendE : forall x y z,
 kHomExtend x y z = (map_poly f (poly_for_Fadjoin E x z)).[y].
Proof. by move => x y z; rewrite lfunE. Qed.

End Definitions.

Lemma subv_kHom : forall K0 K1 E f, (K0 <= K1)%VS ->
 kHom K1 E f -> kHom K0 E f.
Proof.
move => K0 K1 E f HK.
case/andP => HK1 HE.
by rewrite /kHom HE (subv_trans _ HK1).
Qed.

Lemma kHom_subv : forall K E0 E1 f, (E0 <= E1)%VS ->
 kHom K E1 f -> kHom K E0 f.
Proof.
move => K E0 E1 f.
move/subvP => HE.
case/kHomP => HK HE1.
apply/kHomP; split => // x y Hx Hy.
by apply: HE1; apply: HE.
Qed.

Section kHomExtend.

Variables (K E : {subfield L}) (f : 'End(L)).

Lemma kHomExtendX x y : kHom K E f -> x \notin E -> kHomExtend E f x y x = y.
Proof.
move=> homEf E'x; rewrite kHomExtendE poly_for_X //.
by rewrite (kHomFixedPoly homEf) ?hornerX ?polyOverX.
Qed.

Lemma kHom_inv : kHom K E f -> forall x, x \in E -> f x^-1 = (f x)^-1.
Proof.
  case/kHomP => HK HE.
move => x Hx.
case (eqVneq x 0) => [->|Hx0]; first by rewrite linear0 invr0 linear0.
move: (Hx).
rewrite -memv_inv.
move/(HE _ _ Hx).
rewrite divff // HK ?mem1v // => H1.
rewrite -[(f x)^-1]mulr1 H1 mulrA mulVf ?mul1r //.
move/eqP: H1.
apply: contraL.
move/eqP ->.
by rewrite mul0r oner_neq0.
Qed.

Hypothesis Hf : kHom K E f.
Hypothesis HKE : (K <= E)%VS.

Lemma kHom_dim : \dim (f @: E) = \dim E.
Proof.
case/kHomP: (Hf) => HK HE.
apply/limg_dim_eq/eqP.
rewrite -subv0.
apply/subvP => v.
rewrite memv_cap memv0 memv_ker.
case/andP => HvE.
apply: contraLR => Hv.
by rewrite -unitfE unitrE -kHom_inv // -HE ?memv_inv // mulfV // HK // mem1v.
Qed.

Lemma kHomRmorph_subproof : rmorphism (f \o @vsval _ _ E).
Proof. 
case/kHomP: Hf => HK HE.
split; first by move => a b; rewrite /= linearB.
split; first by move => a b; rewrite /= HE // subvsP.
by rewrite /= algid1 HK // mem1v.
Qed.

Lemma kHom_horner p x :
  p \is a polyOver E -> x \in E -> f p.[x] = (map_poly f p).[f x].
Proof.
case/polyOver_subvs=> {p}p -> Ex; rewrite (horner_map _ _ (Subvs Ex)).
by rewrite -[f _](horner_map (RMorphism kHomRmorph_subproof)) map_poly_comp.
Qed.

Lemma kHom_root p x :
  p \is a polyOver E -> x \in E -> root p x -> root (map_poly f p) (f x).
Proof.
by move=> Ep Ex /rootP px0; rewrite /root -kHom_horner // px0 linear0.
Qed.

Lemma kHom_rootK p x :
  p \is a polyOver K -> x \in E -> root p x -> root p (f x).
Proof.
move=> Kp Ex /kHom_root; rewrite (kHomFixedPoly Hf) //.
by apply; rewrite ?(polyOverSv HKE).
Qed.

Variables (x y : L).
Hypothesis Hy : root (map_poly f (minPoly E x)) y.

Lemma kHomExtendExt : forall z, z \in E -> kHomExtend E f x y z = f z.
Proof.
move => z Hz.
by rewrite kHomExtendE poly_for_K // map_polyC hornerC.
Qed.

Lemma kHomExtend_poly : forall p,
  p \in polyOver E -> kHomExtend E f x y (p.[x]) = (map_poly f p).[y].
Proof.
move => p Hp.
rewrite kHomExtendE.
move/(poly_for_modp x): (Hp) ->.
case/kHomP: Hf => HK HE.
have Hfmin : map_poly f (minPoly E x) \is monic.
 by rewrite monicE lead_coef_map_eq;
  move/eqP: (monic_minPoly E x) ->;
  rewrite /= HK ?mem1v // oner_neq0.
rewrite (divp_eq (map_poly f p) (map_poly f (minPoly E x))) !hornerE.
move/eqP: Hy ->.
rewrite mulr0 add0r.
case/polyOver_subvs: Hp => p' ->.
case/polyOver_subvs: (minPolyOver E x) => q' ->.
rewrite -map_modp -!map_poly_comp ?linear0 //=.
by rewrite (map_modp (RMorphism kHomRmorph_subproof)) !map_polyE /=.
Qed.

Lemma kHomExtendkHom : kHom K (Fadjoin E x) (kHomExtend E f x y).
Proof.
case/kHomP: Hf => HK HE.
move/subvP: HKE => HKE'.
apply/kHomP; split.
 move => z Hz.
 rewrite kHomExtendE.
 move/HKE'/poly_for_K: (Hz) ->.
 by rewrite map_polyC hornerC /= HK.
move => a b.
case/poly_Fadjoin => p [Hp ->].
case/poly_Fadjoin => q [Hq ->].
rewrite -hornerM !kHomExtend_poly ?rpredM // -hornerM.
congr (_.[_]).
apply/polyP => i.
rewrite coef_map !coefM /= linear_sum.
apply: eq_bigr => j _.
by rewrite !coef_map /= HE ?(polyOverP _).
Qed.

End kHomExtend.

Implicit Types (K E : {subfield L}) (U V : {vspace L}).

Lemma kAutE K E f : kAut K E f = kHom K E f && (f @: E <= E)%VS.
Proof.
apply/andP/andP; case => Hhom; first by move/eqP->.
move => HfE; split => //.
by rewrite -(dimv_leqif_eq HfE) (kHom_dim Hhom).
Qed.

Lemma LAut_lrmorph (f : 'End(L)) : reflect (lrmorphism f) (kHom F fullv f).
Proof.
apply: (iffP (kHomP _ _ _)).
 case => HF HL.
 repeat split => //.
 - by apply: linearB.
 - by move => x y; apply: HL; rewrite memvf.
 - by rewrite HF // mem1v.
 - by apply: linearZZ.
move => Hf.
split; last by move => x y _ _; apply: (rmorphM (RMorphism Hf)).
move => ?; case/vlineP => k ->.
rewrite linearZ /=.
by rewrite [f 1](rmorph1 (RMorphism Hf)).
Qed.

Lemma kAut_lker0 K f : kHom K fullv f -> lker f == 0%VS.
Proof.
move/(subv_kHom (sub1v _))/LAut_lrmorph=> fM.
by apply/lker0P; exact: (fmorph_inj (RMorphism fM)).
Qed.

Lemma inv_kAut K f : kHom K fullv f -> kHom K fullv f^-1%VF.
Proof.
move=> homFf; have [/kHomP[fKid fM] kerf0] := (homFf, kAut_lker0 homFf).
have f1K: cancel f^-1%VF f by exact: lker0_lfunVK.
apply/kHomP; split=> [x Kx | x y _ _]; apply: (lker0P kerf0).
  by rewrite f1K fKid.
by rewrite fM ?memvf ?{1}f1K.
Qed.

Lemma comp_kAut K E f g : kHom K fullv f -> kHom K E g -> kHom K E (f \o g)%VF.
Proof.
move=> /kHomP[fKid fM] /kHomP[gKid gM]; apply/kHomP; split=> [x Kx | x y Ex Ey].
  by rewrite lfunE /= gKid ?fKid.
by rewrite !lfunE /= gM // fM ?memvf.
Qed.  

Definition splittingFieldFor U p V :=
  exists2 rs, p %= \prod_(z <- rs) ('X - z%:P) & genField U rs = V.

Lemma splittingFieldForS K E p :
  (K <= E)%VS -> splittingFieldFor K p fullv -> splittingFieldFor E p fullv.
Proof.
move=> sKE [rs Dp genL]; exists rs => //; apply/eqP.
by rewrite eqEsubv subvf -genL genFieldSl.
Qed.

Lemma kHom_extends K E f p U :
    (K <= E)%VS -> kHom K E f ->
    p \is a polyOver K -> splittingFieldFor E p U ->
  {g | kHom K U g & {in E, f =1 g}}.
Proof.
move=> sKE homEf Kp /sig2_eqW[rs Dp <-{U}]; set r := rs.
have rs_r: all (mem rs) r by exact/allP.
elim: r rs_r => [_|z r IHr /=/andP[rs_z rs_r]] /= in E f sKE homEf *.
  by exists f.
set Ez := Fadjoin E z; pose fpEz := map_poly f (minPoly E z).
suffices{IHr} /sigW[y fpEz_y]: exists y, root fpEz y.
  have homEz_fz: kHom K Ez (kHomExtend E f z y) by exact: kHomExtendkHom.
  have sKEz: (K <= Ez)%VS := subv_trans sKE (subsetKFadjoin E z).
  have [g homGg Dg] := IHr rs_r _ _ sKEz homEz_fz; exists g => // x Ex.
  by rewrite -Dg ?memK_Fadjoin // kHomExtendExt.
have [m DfpEz]: {m | fpEz %= \prod_(w <- mask m rs) ('X - w%:P)}.
  apply: dvdp_prod_XsubC; rewrite -(eqp_dvdr _ Dp) -(kHomFixedPoly homEf Kp).
  have /polyOver_subvs[q Dq] := polyOverSv sKE Kp.
  have /polyOver_subvs[qz Dqz] := minPolyOver E z.
  rewrite /fpEz Dq Dqz -2?{1}map_poly_comp.
  rewrite (dvdp_map (RMorphism (kHomRmorph_subproof homEf))).
  rewrite -(dvdp_map [rmorphism of @vsval _ _ E]) -Dqz -Dq.
  rewrite minPoly_dvdp ?(polyOverSv sKE) //.
  by rewrite (eqp_root Dp) root_prod_XsubC.
exists (mask m rs)`_0; rewrite (eqp_root DfpEz) root_prod_XsubC mem_nth //.
rewrite -ltnS -(size_prod_XsubC _ id) -(eqp_size DfpEz).
rewrite size_poly_eq ?coef_map -?lead_coefE ?size_minPoly //.
rewrite (monicP (monic_minPoly E z)).
by have /kHomP[fK _] := homEf; rewrite fK ?mem1v ?oner_eq0.
Qed.

Lemma enum_kHom K p :
    p \is a polyOver K -> splittingFieldFor K p fullv ->
  {homK : (\dim_K {:L}).-tuple 'End(L) | separablePolynomial p -> uniq homK
        & forall f, kHom K fullv f = (f \in homK)}.
Proof.
move=> Kp /sig2_eqW[rs Dp]; set r := rs; set E := K => defL.
have [sKE rs_r]: (K <= E)%VS /\ all (mem rs) r by split=> //; exact/allP.
elim: r rs_r => [_|z r IHr /=/andP[rs_z rs_r]] /= in (E) sKE defL *.
  rewrite defL divnn ?adim_gt0 //; exists [tuple \1%VF] => // f.
  rewrite inE; apply/idP/eqP=> [/kHomP[f1 _] | ->]; last exact: kHom1.
  by apply/lfunP=> x; rewrite id_lfunE f1 ?memvf.
have [Ez | E'z] := boolP (z \in E).
  by rewrite FadjoinxK in Ez; apply: IHr => //; rewrite -(eqP Ez).
set Ez := Fadjoin E z in defL; pose pEz := minPoly E z.
have sEEz: (E <= Ez)%VS := subsetKFadjoin E z; have sKEz := subv_trans sKE sEEz.
have{IHr} [homEz UhomEz DhomEz] := IHr rs_r _ sKEz defL.
have Ep: p \in polyOver E := polyOverSv sKE Kp.
have [m DpEz]: {m | pEz %= \prod_(w <- mask m rs) ('X - w%:P)}.
  apply: dvdp_prod_XsubC; rewrite -(eqp_dvdr _ Dp).
  rewrite minPoly_dvdp ?(polyOverSv sKE) //.
  by rewrite (eqp_root Dp) root_prod_XsubC.
set rz := mask m rs in Dp; pose n := \dim_E Ez.
have sz_rz: size rz == n.
  rewrite /n dim_Fadjoin mulKn ?adim_gt0 // -eqSS.
  by rewrite -size_minPoly -(size_prod_XsubC _ id) -(eqp_size DpEz).
have fEz i (y := tnth (Tuple sz_rz) i): {f | kHom E fullv f & f z = y}.
  have homEfz: kHom E Ez (kHomExtend E \1%VF z y).
    rewrite kHomExtendkHom ?kHom1 // map_poly_id => [|u]; last by rewrite lfunE.
    by rewrite (eqp_root DpEz) -/rz root_prod_XsubC mem_tnth.
  have splitFp: splittingFieldFor Ez p fullv.
    exists rs => //; apply/eqP; rewrite eqEsubv subvf -defL genFieldSr //.
    exact/allP.
  have [f homLf Df] := kHom_extends sEEz homEfz Ep splitFp.
  by exists f => //; rewrite -Df ?memx_Fadjoin ?(kHomExtendX _ (kHom1 E E)).
pose mkHom ij := let: (i, j) := ij in (s2val (fEz i) \o tnth homEz j)%VF.
have mkHom_z i j: mkHom (i, j) z = rz`_i.
  have /kHomP[fj_id _]: kHom Ez {:L} (tnth homEz j) by rewrite DhomEz mem_tnth.
  rewrite /= lfunE /= fj_id ?memx_Fadjoin //.
  by case: (fEz i) => _ /= _ ->; rewrite (tnth_nth 0).
have ->: \dim_E {:L} = #|{: 'I_n * 'I_(\dim_Ez {:L})}|.
  rewrite card_prod mulnC !card_ord muln_divA ?field_dimS ?subsetKFadjoin //.
  by rewrite -dim_sup_field ?subvf.
exists [tuple of codom mkHom] => [sepP | f].
  apply/injectiveP => /= [[i1 j1]] [i2 j2] /= /lfunP Eij12.
  have /eqP Ei12: i1 == i2.
    have /eqP := Eij12 z; rewrite !mkHom_z nth_uniq ?(eqP sz_rz) //.
    by rewrite mask_uniq // -separable_prod_XsubC -(eqp_separable Dp).
  rewrite -Ei12 in Eij12 *; congr (_, _); apply/val_inj/eqP.
  case: (fEz i1) Eij12 => f /= /(subv_kHom (sub1v _))/LAut_lrmorph fM _ Ej12.
  rewrite -(nth_uniq 0 _ _ (UhomEz sepP)) ?size_tuple // -!tnth_nth.
  apply/eqP/lfunP=> u; apply: (fmorph_inj (RMorphism fM)) => /=.
  by have:= Ej12 u; rewrite !lfunE.
apply/idP/imageP=> [homLf | [[i j] _ ->] /=]; last first.
  case: (fEz i) => fi /= /comp_kAut->; rewrite ?(subv_kHom sEEz) //.
  by rewrite DhomEz mem_tnth.
have /tnthP[i Dfz]: f z \in Tuple sz_rz.
  rewrite memtE /= -root_prod_XsubC -(eqp_root DpEz).
  by rewrite (kHom_rootK homLf) ?memvf ?subvf ?minPolyOver ?root_minPoly.
case Dfi: (fEz i) => [fi homLfi fi_z]; have kerfi0 := kAut_lker0 homLfi.
set fj := (fi^-1 \o f)%VF; suffices /tnthP[j Dfj]: fj \in homEz.
  by exists (i, j) => //=; rewrite {}Dfi /= -Dfj lker0_compVKf.
rewrite -DhomEz; apply/kHomP.
have homLfj: kHom E fullv fj := comp_kAut (inv_kAut homLfi) homLf.
split=> [_ /poly_Fadjoin[q [Eq ->]]|]; last by case/kHomP: homLfj.
have /LAut_lrmorph fjM := subv_kHom (sub1v _) homLfj.
rewrite -[fj _](horner_map (RMorphism fjM)) (kHomFixedPoly homLfj) //.
by rewrite /= lfunE /= Dfz -fi_z lker0_lfunK.
Qed.

(* The lemma for discharging this assumption for splitting fields is in a     *)
(* separate section because its proof needs to apply kHom_extends to a larger *)
(* extension field.                                                           *)

Definition isNormalFieldExt :=
  forall K x, exists r, minPoly K x == \prod_(y <- r) ('X - y%:P).

Hypothesis NormalFieldExt : isNormalFieldExt.

Lemma normal_field_splitting :
  {p : {poly L} & p \is a polyOver 1%VS & splittingFieldFor 1 p fullv}.
Proof.
pose r i := sval (sigW (NormalFieldExt F (tnth (vbasis fullv) i))).
have sz_r i: (size (r i) <= \dim {:L})%N.
  rewrite -ltnS -(size_prod_XsubC _ id) /r; case: (sigW _) => _ /= /eqP <-.
  rewrite size_minPoly ltnS; move: (tnth _ _) => x.
  by rewrite -[_ x]mul1n -(dimv1 L) -dim_Fadjoin dimvS ?subvf.
pose mkf (z : L) := 'X - z%:P; pose mkfr i j := mkf (r i)`_j.
exists (\prod_i \prod_(j < \dim {:L} | (j < size (r i))%N) mkfr i j).
  apply: rpred_prod => i _; rewrite big_ord_narrow /=.
  rewrite -(big_mkord xpredT (mkfr i)) -(big_nth _ xpredT mkf) /r.
  by case: (sigW _) => _ /= /eqP <-; exact: minPolyOver.
rewrite pair_big_dep /= -big_filter filter_index_enum -(big_map _ xpredT mkf).
set rF := map _ _; exists rF; first exact: eqpxx.
apply/eqP; rewrite eqEsubv subvf -(span_basis (vbasisP fullv)).
apply/span_subvP=> _ /tnthP[i ->]; set x := tnth _ i.
have /(nthP 0)[j lt_j_ri <-]: x \in r i.
  rewrite -root_prod_XsubC /r -/x; case: (sigW _) => _ /= /eqP <-.
  exact: root_minPoly.
by apply/mem_genField/imageP; exists (i, Ordinal (leq_trans lt_j_ri (sz_r i))).
Qed.

Definition LAut_enum : seq 'End(L):=
 let b := vbasis fullv in
 let mkEnd (b' : seq L) := linfun (fun v => \sum_i coord b i v *: b'`_i) in
 undup (filter (kHom F fullv)
   (map mkEnd (foldr (allpairs cons) [:: [::]]
     (map (fun x => xchoose (NormalFieldExt F x)) b)))).

Lemma LAut_is_enum : forall f : 'End(L), 
  reflect (lrmorphism f) (f \in LAut_enum).
Proof.
move => f.
rewrite /LAut_enum mem_undup mem_filter.
apply: (iffP idP).
 rewrite andbC.
 case/andP.
 case/mapP => x Hx ->.
 by move/LAut_lrmorph.
move/LAut_lrmorph => Hf.
rewrite Hf.
apply/mapP.
exists (map f (vbasis fullv)).
 elim: (tval (vbasis fullv)) => [//|v vs IH].
 apply/allpairsP.
 exists (f v, map f vs); split => //.
 move: (xchooseP (NormalFieldExt F v)).
 rewrite -root_prod_XsubC.
 move/eqP <-.
 by rewrite (kHom_rootK Hf) ?subvf ?minPolyOver ?memvf ?root_minPoly.
apply/lfunP => v.
rewrite (lfunE (Linear (_ : linear _))) => [x a b | linE].
 rewrite linear_sum -big_split.
 apply: eq_bigr => i _ /=.
 by rewrite scalerA -scalerDl linearP.
have Hv := coord_vbasis (memvf v).
rewrite {1}Hv linear_sum.
apply: eq_bigr => i _.
rewrite linearZ (nth_map 0) //.
case : vbasis => ? /=.
by move/eqP ->.
Qed.

Definition LAut := seq_sub LAut_enum.

Canonical Structure LAut_subType := Eval hnf in [subType of LAut].
Canonical Structure LAut_eqType := Eval hnf in [eqType of LAut].
Canonical Structure LAut_choiceType := Eval hnf in [choiceType of LAut].
Canonical Structure LAut_countType := Eval hnf in [countType of LAut].
Canonical Structure LAut_subCountType := Eval hnf in [subCountType of LAut].
Canonical Structure LAut_finType := Eval hnf in [finType of LAut].
Canonical Structure LAut_subFinType := Eval hnf in [subFinType of LAut].

Lemma LAut_is_rmorphism : forall f : LAut, lrmorphism (ssval f).
Proof. move => f. by apply/LAut_is_enum/ssvalP. Qed.

Lemma LAut_is_scalable : forall f : LAut, scalable (ssval f).
Proof. move => f. by apply/LAut_is_enum/ssvalP. Qed.

Canonical Structure LAut_rmorphism := 
  fun f => RMorphism (LAut_is_rmorphism f).
Canonical Structure LAut_lrmorphism := 
  fun f => AddLRMorphism (LAut_is_scalable f).

Definition comp_in_LAut : forall (f g : LAut),
 (ssval f \o ssval g)%VF \in LAut_enum.
Proof.
move => f g.
apply/LAut_is_enum.
split; last first.
 move => a b.
 by rewrite linearZ.
split.
 move => a b.
 by rewrite linearB.
by split;[move => a b|]; rewrite !lfunE ?rmorph1 ?rmorphM.
Qed.

Definition id_in_LAut : \1%VF \in LAut_enum.
Proof. apply/LAut_is_enum/LAut_lrmorph. by apply: kHom1. Qed.

Lemma LAut_ker0 : forall (f : LAut), lker (ssval f) = 0%VS.
Proof.
move => f.
apply/eqP.
rewrite -subv0.
apply/subvP => v.
rewrite memv_ker fmorph_eq0.
move/eqP ->.
by rewrite mem0v.
Qed.

Definition inv_in_LAut : forall (f : LAut),
 (ssval f)^-1%VF \in LAut_enum.
Proof.
move => f.
move/LAut_is_enum/LAut_lrmorph: (ssvalP f) => Hf.
apply/LAut_is_enum.
apply:(@can2_lrmorphism _ _ _ [lrmorphism of (ssval f)]).
  by move => a; rewrite lker0_lfunK ?LAut_ker0.
move => a.
move:(memvf a).
rewrite -(addv_complf (limg (ssval f))).
case/memv_addP=> _ /memv_imgP[b _ ->] [z].
rewrite (_ : _^C = 0)%VS; last first.
 apply/eqP.
 by rewrite -dimv_eq0 dimv_compl (kHom_dim Hf) dimvf subnn.
rewrite memv0.
move/eqP => -> ->.
by rewrite addr0 lker0_lfunK ?LAut_ker0.
Qed.

(* the group operation is the categorical composition operation *)
Definition comp_LAut (f g : LAut) : LAut := SeqSub (comp_in_LAut g f).
Definition inv_LAut (f : LAut) : LAut := SeqSub (inv_in_LAut f).
Definition id_LAut : LAut := SeqSub id_in_LAut.

Lemma comp_LAutA : associative comp_LAut.
Proof. move => f g h. apply: val_inj. symmetry. apply: comp_lfunA. Qed.

Lemma comp_1LAut : left_id id_LAut comp_LAut.
Proof. by move=> f; apply/val_inj/comp_lfun1r. Qed.

Lemma comp_LAutK : left_inverse id_LAut inv_LAut comp_LAut.
Proof.
by move=> f; apply/val_inj/lfunP => v; rewrite /= lker0_compfV ?LAut_ker0.
Qed.

Definition LAut_baseFinGroupMixin := FinGroup.Mixin
   comp_LAutA comp_1LAut comp_LAutK.

Canonical LAut_baseFinGroupType := Eval hnf in 
   BaseFinGroupType LAut LAut_baseFinGroupMixin.
Canonical LAut_finGroupType := Eval hnf in
   @FinGroupType LAut_baseFinGroupType comp_LAutK.

Canonical LAut_of_baseFinGroupType := Eval hnf in
   [baseFinGroupType of LAut].
Canonical LAut_of_finGroupType := Eval hnf in
   [finGroupType of LAut].

Lemma kHomExtendLAut : forall (K E : {subfield L}) x,
  (K <= E)%VS -> kHom K E x ->
  exists y : LAut, kHom K fullv (val y) && (E <= lker (val y - x))%VS.
Proof.
move => K E x.
pose n := (\dim E^C).
move : {2}(n.+1) (ltnSn n) => m.
rewrite /n {n}.
elim: m E x => [//|m IH] E x.
case (eqVneq (\dim E^C) 0%N).
 move/eqP.
 rewrite dimv_eq0.
 move/eqP => HEC _ _.
 move: (addv_complf E).
 rewrite HEC addv0 => -> Hx.
 move: (Hx).
 move/(subv_kHom (sub1v _))/LAut_lrmorph/LAut_is_enum => xP.
 exists (SeqSub xP).
 by rewrite Hx subrr lkerE lim0g eqxx.
move => Hdim Hm HKE Hx.
have [a [Ha Ha0]] : exists a, a \in (E^C)%VS /\ a != 0.
 exists (vpick (E^C)%VS); split; first by apply: memv_pick.
 by rewrite vpick0 -dimv_eq0.
have HaE : a \notin E.
 move: Ha0.
 apply: contra.
 move/(conj Ha)/andP.
 rewrite -memv_cap -memv0.
 apply/subvP.
 by rewrite capvC capv_compl subv_refl.
have HminE: minPoly K a \in polyOver E.
 by rewrite (polyOverSv HKE) // minPolyOver.
have : (1 < size (minPoly E a)) by rewrite size_minPoly ltnS.
move: (minPoly_dvdp HminE (root_minPoly K a)).
case/polyOver_subvs : HminE => p Hp.
case/polyOver_subvs : (minPolyOver E a) => q Hq.
have Hmorph := (kHomRmorph_subproof Hx).
rewrite Hp Hq dvdp_map size_map_poly -(dvdp_map (RMorphism Hmorph)).
rewrite -(size_map_poly (RMorphism Hmorph)) !map_poly_comp ?linear0 // -Hp /=.
rewrite [map_poly x (minPoly K a)](kHomFixedPoly Hx) -?Hq; last first.
 by apply: minPolyOver.
clear p Hp q Hq Hmorph.
case: (NormalFieldExt K a) => r.
move/eqP => -> Hdiv Hsz.
(* TODO Abstract this *)
have [b] : exists b, root (map_poly x (minPoly E a)) b.
 clear -Hdiv Hsz.
 elim: r (map_poly x (minPoly E a)) Hdiv Hsz => [|z r IH] p.
  rewrite big_nil.
  move/(dvdp_leq (oner_neq0 _)).
  rewrite size_poly1 leqNgt.
  by move/negbTE ->.
 rewrite big_cons mulrC.
 case (eqVneq (size (gcdp p ('X - z%:P))) 1%N).
  move/eqP/Gauss_dvdpl ->.
  by apply: IH => a Ha.
 rewrite -coprimep_def => Hcoprime _ _.
 exists z.
 move: Hcoprime.
 apply: contraR.
 rewrite root_factor_theorem.
 move/(conj (dvdpp ('X - z%:P)))/andP.
 rewrite -size2_dvdp_gdco -?size_poly_eq0 ?size_XsubC //.
 case: gdcopP => q _.
 rewrite -size_poly_eq0 size_XsubC orbF.
 move/coprimepP => Hpq Hq Hzq.
 apply/coprimepP => d Hdp Hdz.
 apply: Hpq; last done.
 by rewrite (dvdp_trans Hdz).
move => Hb.
case: (IH _ _ _ _ (kHomExtendkHom Hx HKE Hb)).
- rewrite ltnS in Hm.
  apply: (leq_trans _ Hm).
  rewrite !dimv_compl -subSn; last by rewrite dimvS // subvf.
  rewrite -[rhs in _ <= rhs]subSS leq_sub2l // ltnNge.
  apply: contra HaE.
  move/dimv_leqif_sup/geq_leqif: (subsetKFadjoin E a) ->.
  move/subvP/(_ a).
  rewrite memx_Fadjoin.
  by apply.
- by rewrite (subv_trans HKE) // subsetKFadjoin.
move => g.
rewrite lkerE -subv0.
case/andP => Hg.
move/subvP => Hker.
exists g.
rewrite Hg lkerE -subv0.
apply/subvP => ?.
case/memv_imgP => z Hz ->.
apply: Hker.
apply/memv_imgP.
exists z; first by rewrite memK_Fadjoin.
rewrite !add_lfunE !opp_lfunE.
congr (_ - _).
by rewrite kHomExtendExt.
Qed.

Lemma LAut_img_is_aspace (f : LAut) (K : {subfield L}) :
   let Kf := ((val f) @: K)%VS in
   has_algid Kf && (Kf * Kf <= Kf)%VS.
Proof.
apply/andP; split.
 apply has_algid1.
 by rewrite -(rmorph1 [rmorphism of (val f)]) memv_img // mem1v.
apply/prodvP => _ _ /memv_imgP [a Ha ->] /memv_imgP [b Hb ->].
by rewrite -rmorphM memv_img // memv_mul.
Qed.

Canonical Structure LAut_img_aspace a Z : {subfield L} := Eval hnf in
  ASpace (LAut_img_is_aspace a Z).

Definition LAut_FixedField (f : LAut) : {vspace L} :=
  eigenspace (val f) 1.

Lemma LAut_FixedField_is_aspace_subproof f : let FF := LAut_FixedField f in
  (has_algid FF  && (FF * FF <= FF)%VS).
Proof.
apply/andP; split.
 by rewrite has_algid1 // eigenspaceIn rmorph1 scale1r eqxx.
apply/prodvP => a b.
rewrite !eigenspaceIn !scale1r rmorphM /=.
by do 2 move/eqP ->.
Qed.
Canonical LAut_FixedField_aspace f : {subfield L} :=
  ASpace (LAut_FixedField_is_aspace_subproof f).

Lemma LAut_independent (E : {subfield L}) n (f_ : 'I_n -> LAut)
  (c_ : 'I_n -> L) : (forall i, (val (f_ i) @: E)%VS = E) -> 
  uniq [seq (val (f_ i) \o projv E)%VF | i <- enum 'I_n] ->
  (forall i, c_ i \in E) ->
  (E <= lker (\sum_i (amull (c_ i) \o val (f_ i))%VF)%R)%VS ->
  (forall i, c_ i = 0).
Proof.
elim: n f_ c_ => [|n IH] f_ c_ Hf Huniq Hc Hsum; first by move => [].
move => i; apply/eqP; move: i; apply/forallP.
case: (altP forallP); first done.
move/existsP => [i Hi].
have [j /andP [Hji Hcj]] : exists j, (j != i) && (c_ j != 0).
 apply/existsP.
 case: (altP existsP); first done.
 rewrite negb_exists.
 move/forallP => Hci.
 move: Hsum.
 rewrite (bigD1 i) //= big1.
  move: (introNf idP Hi) <-.
  rewrite negbK addr0 => Hcfi.
  rewrite -[c_ i]mulr1 -(rmorph1 ([rmorphism of (val (f_ i))])).
  by have:= subvP Hcfi _ (mem1v _); rewrite memv_ker lfunE /= lfunE.
 move => j Hji.
 move: (Hci j).
 rewrite negb_and Hji negbK.
 move/eqP ->.
 apply/lfunP => a.
 by rewrite !lfun_simp /= mul0r.
have [a HaE] : exists2 a, a \in E & val (f_ j) a != val (f_ i) a.
 move: Hji.
 rewrite -(inj_eq (@ord_inj _)).
 rewrite -(nth_uniq 0 _ _ Huniq) 1?size_map ?size_enum_ord ?ltn_ord //.
 do 2 rewrite (nth_map ord0) ?size_enum_ord ?ltn_ord // nth_ord_enum.
 case/lfunPn => a.
 rewrite !lfunE /= => Ha.
 exists (projv E a); last done.
 by apply: memv_proj.
rewrite -subr_eq0.
pose f'_ := (f_ \o lift j).
pose c'_ m := let m' := lift j m in (c_ m') * (val (f_ j) a - val (f_ m') a).
have : forall i : 'I_n, c'_ i = 0.
 apply: (IH f'_).
 - by move => k; apply Hf.
 - rewrite /f'_.
   (* abstract this proof (same as in LAut_matrix) *)
   rewrite (map_comp (fun i => val (f_ i) \o _)%VF).
   rewrite map_inj_uniq.
    rewrite map_inj_uniq ?enum_uniq //.
    apply: lift_inj.
   move => k1 k2 /eqP Hk.
   apply/eqP.
   rewrite -[k1 == k2](nth_uniq 0 _ _ Huniq)
           1?size_map ?size_enum_ord ?ordP ?ltn_ord //.
   by do 2 rewrite (nth_map ord0) ?size_enum_ord ?ordP ?ltn_ord // nth_ord_enum.
 - move => k.
   apply: memv_mul; first by apply: Hc.
   apply: memvB; first by rewrite -(Hf j) memv_img.
   by rewrite -(Hf (lift j k)) memv_img.
 - set S := \sum_ _ _.
   have -> : (S = (\sum_i (amull ((c_ i) * (val (f_ j) a - val (f_ i) a))%R
                         \o val (f_ i))%VF)).
    rewrite (bigD1 j) //= {1}subrr mulr0.
    (* TODO abstract this into algebra.v *)
    have -> : (amull 0 = 0 :> 'End(L)).
      by apply/lfunP => v; rewrite !lfunE /= mul0r.
    rewrite comp_lfun0l add0r.
    pose G m := (amull (c_ m * ((ssval (f_ j)) a - (ssval (f_ m)) a))%R
                \o ssval (f_ m))%VF.
    set h := lift j.
    have n_gt0 : 0 < n.
     clear -Hji.
     case : n i j Hji; last done.
     by move => [[|//] Hi] [[|//] Hj].
    set h' := odflt (Ordinal n_gt0) \o unlift j.
    rewrite (reindex_onto h h' (F:=G)) /=.
     apply: eq_big => k; last done.
     by rewrite /h /h' /= {1}eq_sym neq_lift liftK eqxx.
    move => k.
    rewrite /h /h' /=.
    case: unliftP; last by move ->; rewrite eqxx.
    by move => ? <-.
   apply/subvP => v Hv.
   rewrite memv_ker.
   rewrite -[X in _ == X]addr0 -[X in 0 + X]oppr0.
   rewrite sum_lfunE.
   have HsumA : \sum_i (amull (c_ i * val (f_ j) a)%R \o val (f_ i))%VS v = 0.
    move/subvP/(_ _ Hv): Hsum.
    rewrite memv_ker.
    move/eqP/(f_equal (fun x => val (f_ j) a * x)).
    rewrite mulr0 => H0.
    rewrite -[X in _ = X]H0 sum_lfunE mulr_sumr.
    apply: eq_bigr => m _.
    by rewrite !{1}lfun_simp /= lfunE /= mulrCA mulrA. 
   have HsumB : \sum_i (amull (c_ i * val (f_ i) a)%R \o val (f_ i))%VF v = 0.
    move/subvP/(_ _ (memv_mul HaE Hv)): Hsum.
    rewrite memv_ker.
    move/eqP => H0.
    rewrite -[X in _ = X]H0 sum_lfunE.
    apply: eq_bigr => m _.
    by rewrite !{1}comp_lfunE /= !lfunE /= rmorphM mulrA.
   rewrite -[X in (X - _)]HsumA -[X in (_ - X)]HsumB -sumrB.
   apply/eqP.
   apply: eq_bigr => m _.
   by rewrite !{1}lfunE /= !{1}lfunE /= -mulrBl -mulrBr.
move : Hji.
case/unlift_some => i' Hii' Hi'i.
move/(_ i')/eqP.
rewrite /c'_ mulf_eq0 -Hii'.
case/orP.
 move/eqP => Hci.
 move: Hi.
 by rewrite Hci eqxx.
move/eqP ->.
by rewrite eqxx.
Qed.

Lemma LAut_matrix_subproof (E : {subfield L}) n (f_ : 'I_n -> LAut) :
  (forall i, (val (f_ i) @: E)%VS = E) ->
  uniq [seq (val (f_ i) \o (projv E))%VF | i <- enum 'I_n] ->
  exists2 w_ : 'I_n -> L, (forall j, w_ j \in E) &
   \matrix_(i, j) (val (f_ i) (w_ j)) \in unitmx.
Proof.
elim: n f_ => [|n IH] f_ Hf Huniq.
 exists (fun _ => 0).
  by move => [].
 by rewrite unitmxE det_mx00 unitr1.
pose f'_ i := f_ (rshift 1 i).
case: (IH f'_ _ _).
  by move => i; apply Hf.
 (* abstract this proof (same as in LAut_independent) *)
 rewrite /f'_.
 rewrite (map_comp (fun i => val (f_ i) \o _)%VF) map_inj_uniq.
  rewrite (eq_map (@rshift1 _)).
  rewrite map_inj_uniq ?enum_uniq //.
  apply: lift_inj.
 move => k1 k2 /eqP Hk.
 apply/eqP.
 rewrite -[k1 == k2](nth_uniq 0 _ _ Huniq)
         1?size_map ?size_enum_ord ?ordP ?ltn_ord //.
 by do 2 rewrite (nth_map ord0) ?size_enum_ord ?ordP ?ltn_ord // nth_ord_enum.
move => w'_ Hw'.
set M' := \matrix_(_,_) _ => HM'.
pose x := \row_(j < n) (val (f_ 0) (w'_ j)).
pose c' := (x *m invmx M').
pose c_ := row_mx 1 (-c').
pose comb := \sum_i (amull (c_ 0 i) \o val (f_ i))%VF.
have Hc : forall i, c_ 0 i \in E.
 move => i.
 rewrite mxE.
 case: splitP.
  move => ? _.
  by rewrite ord1 mxE mem1v.
 move => i' _.
 rewrite mxE memvN mxE.
 apply: memv_suml => j _.
 apply: memv_mul.
  by rewrite mxE -(Hf 0) memv_img.
 move: j i'.
 apply/matrixOverP.
 rewrite -invmx_matrixOver.
 apply/matrixOverP => j i'.
 by rewrite mxE -(Hf (rshift 1 j)) memv_img.
case (eqVneq (E :\: lker comb) 0)%VS.
 move/eqP; rewrite diffv_eq0.
 move/(LAut_independent Hf Huniq Hc)/(_ ord0)/eqP.
 rewrite -[ord0](@lshift0 _ 0) row_mxEl mxE eqxx -[_ == _]negbK.
 by rewrite oner_neq0.
rewrite -vpick0.
set w0 := vpick _ => Hw0.
have Hw0E : w0 \in E.
 by apply: (subvP (diffvSl _ _) _ (memv_pick (E :\: lker comb)%VS)).
have Hw0comb : comb w0 != 0.
 move: Hw0.
 apply: contra.
 rewrite -memv_ker.
 move/(conj (memv_pick (E :\: lker comb)%VS))/andP.
 by rewrite -memv_cap capv_diff memv0 vpick0.
pose w_ := row_mx (w0%:M) (\row_j w'_ j).
exists (w_ 0).
 move => j.
 rewrite /w_.
 rewrite mxE.
 case: splitP.
  move => ? ?.
  rewrite mxE.
  case: (_ == _); first done.
  by rewrite mem0v.
 move => ? _.
 by rewrite mxE.
rewrite unitmxE.
rewrite -[\det _]mul1r.
pose B := block_mx 1 (-c') 0 1%:M.
have <- : \det B = 1 by rewrite det_ublock !det1 mulr1.
set M := \matrix_(_,_) _.
rewrite -det_mulmx -[M](@submxK _ 1 n 1 n) mulmx_block.
rewrite !mul0mx !mul1mx !add0r.
set DR := drsubmx _.
have -> : DR = M'.
 apply/matrixP => i j.
 by rewrite /M' 4!mxE /w_ row_mxEr mxE.
set C := ursubmx (_) + _.
have -> : C = 0.
 apply/matrixP => ? j.
 by rewrite ord1 mxE mulNmx mulmxKV // !(row_mxEr, mxE) lshift0 subrr.
rewrite det_lblock unitrM andbC -unitmxE HM'.
rewrite [_ + _](_ : _ = (comb w0)%:M); first by rewrite det_scalar1 unitfE.
set UL := ulsubmx _.
have -> : UL = (val (f_ 0) w0)%:M.
 apply/matrixP => i j.
 by rewrite !ord1 !(row_mxEl, mxE) lshift0.
apply/matrixP => ? ?.
rewrite !ord1 !mxE !eqxx /comb sum_lfunE big_ord_recl {1}lfunE /= lfunE /=.
rewrite -[ord0](@lshift0 _ 0) row_mxEl mxE eqxx mul1r lshift0.
congr (_ + _).
apply eq_bigr => i _.
rewrite -rshift1 row_mxEr {1}lfunE /= lfunE /=.
congr (_ * _).
by rewrite !(row_mxEl, mxE).
Qed.

(* In most definitions I give the smaller field first, since the larger
   field can be seen as algebra over the smaller, and so in some moral sense
   the larger field depends on the smaller one.  However standard mathematical
   notation for Aut(E/K) puts the larger field first. *)
Definition Aut (E K : {vspace L}) :=
  ([set x : LAut | kAut K E (val x)] /
             [set x : LAut | kAut E fullv (val x)])%g.

Reserved Notation "''Aut' ( A | B )"
  (at level 8, format "''Aut' ( A  |  B )").
Notation "''Aut' ( A | B )" := (Aut A B) : group_scope.

Lemma kAut_group_set : forall K E : {subfield L}, 
  group_set [set x : LAut | kAut K E (val x)].
Proof.
move => K E.
apply/group_setP; split.
 rewrite in_set kAutE.
 apply/andP; split; last by rewrite SubK lim1g subv_refl.
 apply/kHomP; split; last by move => ? ? _ _; rewrite rmorphM.
 move => a _.
 by rewrite SubK id_lfunE.
move => x y.
rewrite !in_set !kAutE.
case/andP; case/kHomP => Hx1 Hx2 Hx3.
case/andP; case/kHomP => Hy1 Hy2 Hy3.
apply/andP; split; last first.
 by rewrite SubK limg_comp (subv_trans _ Hy3) // limg_ker0 // LAut_ker0.
apply/kHomP; split; last by move => ? ? _ _; rewrite rmorphM.
move => a Ha.
by rewrite SubK lfunE /= Hy1 // Hx1.
Qed.

Canonical kAut_group K E := Eval hnf in group (kAut_group_set K E).

Lemma kAut_normal : forall K E : {subfield L},
 ([set x : LAut | kAut K E (val x)] \subset
   'N([set x : LAut | kAut E fullv (val x)]))%g.
Proof.
move => K E.
apply/subsetP.
move => x.
rewrite !{1}in_set.
case/andP => _.
move/eqP => Hx.
apply/subsetP => ?.
case/imsetP => y.
rewrite !in_set.
case/andP.
case/kHomP => Hy _ _ ->.
rewrite kAutE subvf andbT.
apply/kHomP; split; last by move => ? ? _ _; rewrite rmorphM.
move => a Ha.
rewrite -{2}[a](id_lfunE) -[\1%VF]/(val (1%g : LAut)) -(mulVg x).
rewrite !SubK !lfunE /= lfunE [X in ((val x) X) = _]Hy //.
rewrite -Hx in Ha.
case/memv_imgP: Ha => [b Hb ->].
by rewrite lker0_lfunK ?LAut_ker0.
Qed.

(* Move this to vector.v *)
Lemma eqvP (V : {vspace L}) (f g: 'End(L)) :
  reflect (forall a, a \in V -> f a = g a)
          (V <= lker (f - g))%VS.
Proof.
apply: (iffP idP).
 rewrite lkerE.
 move/eqP => Hfg a /(memv_img (f - g)).
 rewrite Hfg memv0 !lfun_simp /= subr_eq0.
 by move/eqP.
move => Hfg.
apply/subvP => v Hv.
rewrite memv_ker !lfun_simp subr_eq0.
apply/eqP.
by apply: Hfg.
Qed.

Lemma Aut_eq (E : {subfield L}) 
  (x y : coset_of [set x : LAut | kAut E fullv (val x)]) (f g : LAut) : 
  f \in x -> g \in y ->
  reflect (forall a, a \in E -> val f a = val g a)%VS (x == y).
Proof.
move => Hf Hg.
move/subsetP/(_ _ Hf): (coset_norm x) => HfN.
move/subsetP/(_ _ Hg): (coset_norm y) => HgN.
apply: (iffP idP).
 move/eqP => Hxy.
 move: Hf Hg.
 rewrite Hxy.
 move/coset_mem <-.
 rewrite val_coset //.
 case/rcosetP => h.
 rewrite inE kAutE subvf andbT.
 case/kHomP => Hh _ -> a Ha.
 rewrite /= lfunE /= Hh //.
move/coset_mem: Hf <-.
move/coset_mem: (Hg) => <- Hfg.
apply/eqP/coset_mem.
rewrite val_coset // mem_rcoset /=.
rewrite inE kAutE subvf andbT.
apply/kHomP; split; last by move => ? ? _ _; rewrite rmorphM.
move => a Ha.
by rewrite comp_lfunE /= Hfg // lker0_lfunK ?LAut_ker0.
Qed.

Lemma Aut_mul (E : {subfield L})
 (x y : coset_of [set x : LAut | kAut E fullv (val x)]) :
 forall a, a \in E -> val (repr (x*y)%g) a = val (repr y) (val (repr x) a).
Proof.
move => a Ha.
transitivity (val (repr x * repr y)%g a); last by rewrite /= comp_lfunE.
move: a Ha.
apply/(@Aut_eq _ (x*y) (x*y)) => //; first by rewrite mem_repr_coset.
rewrite -{2}(coset_mem (mem_repr_coset x)).
rewrite -{2}(coset_mem (mem_repr_coset y)).
rewrite -coset_morphM ?repr_coset_norm //.
rewrite val_coset; first by apply: rcoset_refl.
by apply: groupM; apply: repr_coset_norm.
Qed.

(* I probably should write an Aut_inv lemma. *)

Section Automorphism.

Variables K E : {subfield L}.
Hypothesis HKE : (K <= E)%VS.

Lemma kAut_Aut f : kAut K E f -> exists2 x, x \in 'Aut(E | K)%g &
  forall g, g \in x -> forall a, a \in E -> f a = val g a.
Proof.
move => Hf.
case/andP: (Hf) => HfHom /eqP HfE.
case: (kHomExtendLAut HKE HfHom) => g /andP [HKg /eqvP HEgf].
have Hgf : (val g @: E <= E)%VS.
 rewrite -{2}HfE.
 apply/subvP => ? /memv_imgP [v Hv ->].
 move/HEgf: (Hv) ->.
 by rewrite memv_img.
exists (coset _ g).
 rewrite /Aut -imset_coset. 
 apply: mem_imset.
 by rewrite inE kAutE (kHom_subv (subvf _)).
move => h.
rewrite val_coset.
 case/rcosetP => {h} h Hh -> a HaE.
 rewrite -HEgf // comp_lfunE.
 move: Hh.
 rewrite inE.
 case/andP.
 case/kHomP => Hh _ _.
 by rewrite [X in _ = (val g X)]Hh // HEgf // -HfE memv_img.
move/subsetP: (kAut_normal K E).
apply.
rewrite inE kAutE Hgf andbT.
apply/kHomP; split; last by move => ? ? _ _; rewrite rmorphM.
by case/kHomP: HKg.
Qed.

Lemma Aut_kAut x f : x \in 'Aut(E | K)%g -> f \in x -> kAut K E (val f).
Proof.
rewrite /Aut -imset_coset.
case/imsetP => {x} x Hx ->.
rewrite val_coset; last by move/subsetP: (kAut_normal K E); apply.
case/rcosetP => {f} f Hf ->.
rewrite kAutE.
move: Hx Hf; rewrite !inE.
case/andP => /kHomP [Hx _] /eqP HxE.
case/andP => /kHomP [Hf _] _.
apply/andP; split; last first.
 apply/subvP => ? /memv_imgP [a Ha ->].
 by rewrite comp_lfunE /= Hf // -HxE; apply: memv_img.
apply/kHomP; split; last by move => ? ? _ _; rewrite rmorphM.
move => a Ha.
move/subvP/(_ _ Ha): HKE => HaE.
by rewrite comp_lfunE /= Hf // Hx.
Qed.

End Automorphism.

(* kAut_pick is another way of phrasing kAut_Aut *)
Lemma kAut_pick_subproof (K E : {subfield L}) f :
 exists x, (x \in 'Aut(E | K)%g) && (((K <= E)%VS && kAut K E f) ==> 
    forallb g, (g \in x) ==> (E <= lker (f - val g))%VS).
Proof.
case Hf : ((K <= E)%VS && kAut K E f); last first.
 exists 1%g.
 by rewrite group1.
case/andP: Hf => HKE /(kAut_Aut HKE) [x Hx1 Hx2].
exists x.
rewrite Hx1.
apply/forallP => g.
apply/implyP => Hg.
apply/eqvP.
by apply: Hx2.
Qed.

(* TODO: make E not an algebra *)
Definition kAut_pick U (E : {subfield L}) f : 
  coset_of [set x : LAut | kAut E fullv (val x)] :=
  if insub U is Some K 
     then xchoose (kAut_pick_subproof K E f)
     else (coset_one _).

Lemma kAut_pick_Aut (K E : {subfield L}) f : kAut_pick K E f \in 'Aut(E | K)%g.
Proof.
rewrite /kAut_pick valK.
by case/andP: (xchooseP (kAut_pick_subproof K E f)).
Qed.

Lemma kAut_pick_eq (K E : {subfield L}) f : (K <= E)%VS -> kAut K E f -> 
  forall g, g \in kAut_pick K E f -> forall a, a \in E -> f a = val g a.
Proof.
move => HKE Hf g.
rewrite /kAut_pick valK.
case/andP: (xchooseP (kAut_pick_subproof K E f)) => _.
move/andP: (conj HKE Hf) => HKEf.
move/implyP/(_ HKEf)/forallP/(_ g)/implyP => Hpick Hg.
apply/eqvP.
by apply: Hpick.
Qed.

Lemma Aut_conjg (K E : {subfield L})
  (x : coset_of [set x : LAut | kAut E fullv (val x)]) (f : LAut) :
  (K <= E)%VS -> (val f @: E = E)%VS -> f \in x -> 
  ('Aut(E | K) :^ x = 'Aut(E | (val f @: K)%VS))%g.
Proof.
move => HKE HfE Hfx.
apply/eqP.
have HKfE : (val f @: K <= E)%VS.
 apply/subvP => _ /memv_imgP [a Ha ->].
 rewrite -HfE memv_img //.
 by move/subvP: HKE; apply.
wlog suff : x f K HKE HfE HKfE Hfx / 
  (('Aut(E | K) :^ x)%g \subset ('Aut(E | (val f @: K)%VS))%g).
 move => Hsuff.
 rewrite eqEsubset Hsuff // -sub_conjgV -[X in _ \subset ('Aut(E | X))%g]lim1g.
 rewrite -[\1%VF]/(val (1 : LAut)%g) -[(1 : LAut)%g](mulgV f) limg_comp.
 apply: Hsuff; first done.
 - by rewrite -{1}HfE -limg_comp -[(_ \o _)%VF]/(val (f * f^-1)%g) mulgV lim1g.
 - by rewrite -limg_comp -[(_ \o _)%VF]/(val (f * f^-1)%g) mulgV lim1g.
 - by rewrite inE invgK.
have Hfxb : forall b, b \in E -> (val f b) = (val (repr x) b).
 apply/(Aut_eq Hfx (mem_repr_coset _)).
 by rewrite eqxx.
apply/subsetP => y.
rewrite mem_conjg conjgE invgK.
move/(Aut_kAut HKE)/(_ (mem_repr_coset _)).
case/andP => HxyxV /eqP HxyxVE.
suff: (kAut (val f @: K)%VS E (val (repr y))).
 case/(kAut_Aut HKfE) => z Hz /(_ _ (mem_repr_coset _)).
 by move/(Aut_eq (mem_repr_coset _) (mem_repr_coset _))/eqP => ->.
rewrite kAutE.
apply/andP; split; last first.
 apply/subvP => _ /memv_imgP [a Ha ->].
 move: Ha.
 rewrite -{1}HfE.
 case/memv_imgP => b Hb Hfb.
 rewrite Hfb Hfxb // -Aut_mul // -[in X in _ \in X]HfE.
 apply/memv_imgP.
 exists (val (repr (x * (y * x^-1))%g) b).
   by rewrite -[in X in _ \in X]HxyxVE memv_img.
 rewrite Hfxb; last by rewrite -[in X in _ \in X]HxyxVE memv_img.
 by rewrite -Aut_mul // mulgA mulgKV.
apply/kHomP; split; last by move => ? ? _ _; rewrite rmorphM.
move => _ /memv_imgP [a Ha ->].
case/kHomP: HxyxV => /(_ _ Ha) => HxyxVa _.
move: HxyxVa.
have HaE : a \in E by move/subvP: HKE; apply.
move/(f_equal (val f)).
rewrite Hfxb; last by rewrite -[in X in _ \in X]HxyxVE // memv_img.
rewrite -Aut_mul // mulgA mulgKV Aut_mul; last done.
by rewrite -Hfxb.
Qed.

Lemma memv_aut (K E : {subfield L}) x a : (K <= E)%VS ->
 x \in 'Aut(E | K)%g -> a \in E -> val (repr x) a \in E.
Proof.
move => HKE.
case/(Aut_kAut HKE)/(_ (mem_repr_coset _))/andP => _ /eqP HE HaE.
by rewrite -[in X in _ \in X]HE memv_img.
Qed.

Lemma uniq_aut (K E : {subfield L}) n f_ :
 (forall i, f_ i \in 'Aut(E | K)%g) ->
 uniq [seq f_ i | i <- enum 'I_n] ->
 uniq [seq (val (repr (f_ i)) \o projv E)%VF |  i <- enum 'I_n].
Proof.
move => Hf.
set (s := [seq f_ i |  i <- enum 'I_n]).
pose g (x : coset_of [set x : LAut | kAut E fullv (val x)]):= 
     (val (repr x) \o projv E)%VF.
suff Hs : {in s &, injective g} by rewrite -(map_inj_in_uniq Hs) -map_comp.
move=> x y Hx Hy /= Hg.
apply/eqP/(Aut_eq (mem_repr_coset _) (mem_repr_coset _)) => a /projv_id <-.
by rewrite -[_ (projv E a)]comp_lfunE [(_ \o _)%VF]Hg comp_lfunE.
Qed.

Definition FixedField (E : {vspace L})
  (s : {set coset_of [set x : LAut | kAut E fullv (val x)]}) :=
  (E :&: \bigcap_( i \in cover [set (set_of_coset x) | x <- s])
          (LAut_FixedField i))%VS.

Lemma FixedFieldP (E : {subfield L})
   (s : {set coset_of [set x : LAut | kAut E fullv (val x)]}) a :
 reflect (a \in E /\ forall x, (x \in s) -> (val (repr x) a = a))
         (a \in FixedField s).
Proof.
rewrite /FixedField big_trivIset; last first.
 apply/trivIsetP => ? ? /imsetP [x Hx ->] /imsetP [y Hy ->].
 by apply: contraR => /pred0Pn [f /andP [/coset_mem <- /coset_mem <-]].
rewrite memv_cap /=.
case HaE : (a \in E); last first.
 apply: ReflectF.
 by case.
apply: (iffP subv_bigcapP).
 move => Hcap; split; first done.
 move => x Hx.
 apply/eqP.
 move/subv_bigcapP/(_ (repr x)): (Hcap _ (mem_imset _ Hx)).
 move/(_ (mem_repr_coset _)).
 by rewrite [(_ <= _)%VS]eigenspaceIn scale1r.
move => [_ HFixed] ? /imsetP [x Hx ->].
apply/subv_bigcapP => i.
rewrite [(_ <= _)%VS]eigenspaceIn scale1r => Hi.
rewrite -{2}(HFixed x) //.
apply/eqP.
move: {HFixed} a HaE.
apply/(@Aut_eq _ x x) => //.
apply: mem_repr_coset.
Qed.

Lemma galoisAdjuctionA (K E : {subfield L}) :
  (K <= E)%VS ->
  (K <= FixedField ('Aut(E | K))%g)%VS.
Proof.
move => HKE.
apply/subvP => a HaK.
apply/FixedFieldP; split; first by move/subvP: HKE; apply.
move => x Hx.
by move: (Aut_kAut HKE Hx (mem_repr_coset _)) => /andP [/kHomP [->]].
Qed.

Lemma FixedField_is_aspace_subproof  (E : {subfield L})
   (s : {set coset_of [set x : LAut | kAut E fullv (val x)]}) :
  let FF := FixedField s in
  (has_algid FF  && (FF * FF <= FF)%VS).
Proof.
rewrite /FixedField -big_filter.
move : (filter _ _) => {s} r.
elim : r E => [|r rs IH] E; first by rewrite big_nil capvf; case: E.
rewrite big_cons capvA.
by apply: IH.
Qed.

Canonical Structure FixedField_aspace (E : {subfield L})
   (s : {set coset_of [set x : LAut | kAut E fullv (val x)]}) : {subfield L}
   := ASpace (FixedField_is_aspace_subproof s).

Lemma FixedField_subset (E : {subfield L})
   (s1 s2 : {set coset_of [set x : LAut | kAut E fullv (val x)]}) :
   (s1 \subset s2) -> (FixedField s2 <= FixedField s1)%VS.
Proof.
move => /subsetP Hs.
apply/subvP => a /FixedFieldP [HaE Ha].
apply/FixedFieldP; split; first done.
move => x Hx.
by rewrite Ha // Hs.
Qed.

Definition galoisTrace (K E : {vspace L}) a := 
 \sum_(i | i \in ('Aut(E | K))%g) (val (repr i) a).

Definition galoisNorm (K E : {vspace L}) a := 
 \prod_(i | i \in ('Aut(E | K))%g) (val (repr i) a).

Section TraceAndNorm.

Variables (K E : {subfield L}).

Lemma galoisTrace_is_additive : additive (galoisTrace K E).
Proof.
move => a b /=.
rewrite -sumrB.
apply: eq_bigr => i _.
by rewrite rmorphB.
Qed.

Canonical galoisTrace_additive := Eval hnf in Additive galoisTrace_is_additive.

Lemma autTraceFixedField a :
 (K <= E)%VS -> a \in E -> galoisTrace K E a \in FixedField 'Aut(E | K)%g.
Proof.
move => HKE Ha.
apply/FixedFieldP.
split.
 apply: memv_suml => i.
 case/(Aut_kAut HKE)/(_ (mem_repr_coset _))/andP => _ /eqP HE.
 by rewrite -[in X in _ \in X]HE memv_img.
move => x Hx.
rewrite rmorph_sum /galoisTrace -{2}['Aut(E | K)%g](rcoset_id Hx).
rewrite (reindex_inj (mulIg (x^-1)%g)).
symmetry.
apply: eq_big => i; first by rewrite /= mem_rcoset.
by rewrite -[LAut_rmorphism _ _]Aut_mul // mulgKV.
Qed.

Lemma traceAut a x : a \in E -> x \in 'Aut(E | K)%g -> 
  galoisTrace K E (val (repr x) a) = galoisTrace K E a.
Proof.
move => Ha Hx.
rewrite /galoisTrace -{2}['Aut(E | K)%g](lcoset_id Hx).
rewrite (reindex_inj (mulgI (x^-1)%g)).
apply: eq_big => i;first by rewrite /= mem_lcoset.
by rewrite -[LAut_rmorphism _ _]Aut_mul // mulKVg.
Qed.

Lemma galoisNormM : multiplicative (galoisNorm K E).
Proof.
split; last by apply big1 => i _; rewrite rmorph1.
move => a b /=.
rewrite -big_split.
apply: eq_bigr => i _.
by rewrite rmorphM.
Qed.

Lemma galoisNormV a : galoisNorm K E (a^-1) = (galoisNorm K E a)^-1.
Proof.
rewrite -prodf_inv.
apply: eq_bigr => i _.
by rewrite fmorphV //.
Qed.

Lemma galoisNorm0 : galoisNorm K E 0 = 0.
Proof. by rewrite /galoisNorm (bigD1 1%g) ?group1 // rmorph0 /= mul0r. Qed.

Lemma galoisNorm_eq0 a : (galoisNorm K E a == 0) = (a == 0).
Proof.
apply/idP/eqP; last by move ->; rewrite galoisNorm0.
case/prodf_eq0 => i Hi.
rewrite fmorph_eq0.
by move/eqP.
Qed.

Lemma autNormFixedField a :
 (K <= E)%VS -> a \in E -> galoisNorm K E a \in FixedField 'Aut(E | K)%g.
Proof.
move => HKE Ha.
apply/FixedFieldP.
split.
 apply: memv_prodl => i.
 case/(Aut_kAut HKE)/(_ (mem_repr_coset _))/andP => _ /eqP HE.
 by rewrite -[in X in _ \in X]HE memv_img.
move => x Hx.
rewrite rmorph_prod /galoisNorm -{2}['Aut(E | K)%g](rcoset_id Hx).
rewrite (reindex_inj (mulIg (x^-1)%g)).
symmetry.
apply: eq_big => i; first by rewrite /= mem_rcoset.
by rewrite -[LAut_rmorphism _ _]Aut_mul // mulgKV.
Qed.

Lemma normAut a x : a \in E -> x \in 'Aut(E | K)%g -> 
  galoisNorm K E (val (repr x) a) = galoisNorm K E a.
Proof.
move => Ha Hx.
rewrite /galoisNorm -{2}['Aut(E | K)%g](lcoset_id Hx).
rewrite (reindex_inj (mulgI (x^-1)%g)).
apply: eq_big => i;first by rewrite /= mem_lcoset.
by rewrite -[LAut_rmorphism _ _]Aut_mul // mulKVg.
Qed.

End TraceAndNorm.

Definition normal (K E : {vspace L}) :=
 forallb x : LAut, kHom K fullv (val x) ==> ((val x) @: E == E)%VS.

Lemma normalP : forall (K E : {subfield L}), 
 reflect (forall a, a \in E -> exists2 r, all (fun y => y \in E) r
                                 & minPoly K a = \prod_(b <- r) ('X - b%:P))
         (normal K E).
Proof.
move => K E.
apply: (iffP forallP); last first.
 move => Hnorm x.
 apply/implyP => Hx.
 suff: (kAut K E (val x)) by case/andP.
 rewrite kAutE (kHom_subv (subvf E)) //=.
 apply/subvP => a.
 case/memv_imgP => {a} a Ha ->.
 case: (Hnorm _ Ha) => r.
 move/allP => Hr Har.
 apply: Hr.
 rewrite -root_prod_XsubC.
 move/(f_equal (map_poly (fun_of_lfun (val x)))): (Har).
 rewrite (kHomFixedPoly Hx) ?minPolyOver //= Har => ->.
 by rewrite rmorph_root // -Har root_minPoly.
move => Hnorm a HaE.
case: (NormalFieldExt K a) => r.
move/eqP => Hr.
exists r => //.
apply/allP => b.
rewrite -root_prod_XsubC -Hr -[minPoly K a]polyseqK.
rewrite -[polyseq _](@map_id_in _ [rmorphism of (val (1:LAut))%g]); last first.
 move => z _ /=.
 by rewrite id_lfunE.
rewrite -map_polyE => Hab.
set y := kHomExtend K \1%VF a b.
rewrite -[b]hornerX -(map_polyX [rmorphism of (val (1:LAut))%g]).
have H1 : kHom K K (val (1:LAut))%g.
 apply/kHomP.
 split; last by move => ? ? _ _; rewrite rmorphM.
 move => x _ /=.
 by rewrite id_lfunE.
rewrite -(kHomExtend_poly H1 Hab) ?polyOverX // hornerX -/y.
have Hy : kHom K (Fadjoin K a) y by exact: kHomExtendkHom.
case: (kHomExtendLAut (subsetKFadjoin K a) Hy) => z.
case/andP => Hz Hzy.
move/implyP/(_ Hz)/eqP: (Hnorm z) (subv_refl E) => HzE.
rewrite -{1}HzE.
move/subvP; apply.
suff -> : y a = (val z) a by apply: memv_img.
symmetry.
apply/eqP.
rewrite -subr_eq0 -opp_lfunE -add_lfunE -memv_ker.
move/subvP: Hzy; apply.
by rewrite memx_Fadjoin.
Qed.

Definition galois U V := [&& (U <= V)%VS, separable U V & normal U V].

Lemma separable_dim : forall (K : {subfield L}) x, separableElement K x ->
  normal K (Fadjoin K x) -> elementDegree K x = #|'Aut(Fadjoin K x | K)%g|.
Proof.
move => K x Hsep.
set E := Fadjoin K x.
case/normalP/(_ _ (memx_Fadjoin K x)) => r.
move/allP => Hr Hmin.
apply/succn_inj.
rewrite -size_minPoly Hmin size_prod_XsubC.
congr (_.+1).
apply/eqP.
move: Hsep.
rewrite /separableElement Hmin separable_prod_XsubC => Huniq.
rewrite eqn_leq.
apply/andP; split; last first.
 rewrite cardE.
 pose f (y : coset_of [set g : LAut | kAut E fullv (val g)]) :=
    val (repr y) x.
 rewrite -(size_map f).
 apply: uniq_leq_size.
  rewrite map_inj_in_uniq ?enum_uniq //.
  move => a b.
  rewrite 2!mem_enum => Ha Hb Hab.
  apply/eqP/(Aut_eq (mem_repr_coset _) (mem_repr_coset _)) => ?.
  case/poly_Fadjoin => p [Hp ->].
  rewrite -!horner_map /= -/(f a) -/(f b) Hab.
  case/andP: (Aut_kAut (subsetKFadjoin _ _) Ha (mem_repr_coset _)).
  move/(kHomFixedPoly)/(_ Hp) => -> _.
  case/andP: (Aut_kAut (subsetKFadjoin _ _) Hb (mem_repr_coset _)).
  by move/(kHomFixedPoly)/(_ Hp) => -> _.
 move => ? /mapP [a Ha ->].
 rewrite mem_enum in Ha.
 rewrite -root_prod_XsubC -Hmin /f.
 case/andP: (Aut_kAut (subsetKFadjoin _ _) Ha (mem_repr_coset _)).
 move/(kHom_rootK)/(_ (subsetKFadjoin _ _) _ _
                      (minPolyOver K x) (memx_Fadjoin _ _)) => Hroot _.
 by rewrite Hroot // root_minPoly.
pose f y := kAut_pick K (Fadjoin_aspace K x) (kHomExtend K \1%VF x y).
rewrite -(size_map f).
suff/card_uniqP <- : uniq (map f r).
 apply: subset_leq_card.
 apply/subsetP.
 move => ? /mapP [a _ ->].
 by apply: kAut_pick_Aut.
rewrite map_inj_in_uniq // => a b Ha Hb.
rewrite /f.
set fa := (kHomExtend _ _ x a).
set fb := (kHomExtend _ _ x b).
move => Hab.
have Hroot : forall c, c \in r -> root (map_poly \1%VF (minPoly K x)) c.
 move => c Hc.
 rewrite (eq_map_poly (fun x => id_lfunE x)).
 rewrite map_polyE map_id polyseqK.
 by rewrite Hmin root_prod_XsubC.
have Hpoly : forall c, c \in r -> c = (kHomExtend K \1%VF x c) x.
 move => c Hc.
 rewrite -{2}[x]hornerX.
 rewrite (kHomExtend_poly (kHom1 K K) (Hroot _ Hc)); last first.
   exact: (@polyOverX _ K).
 by rewrite map_poly_id ?hornerX => [|? _]; rewrite /= ?id_lfunE.
rewrite (Hpoly _ Ha) (Hpoly _ Hb) {Hpoly} -/fa -/fb.
pose g := val (repr (kAut_pick K (Fadjoin_aspace K x) fa)).
have HAuta : kAut K (Fadjoin K x) fa.
 rewrite kAutE (kHomExtendkHom (kHom1 K K) (subv_refl K) (Hroot _ Ha)).
 apply/subvP => ? /memv_imgP [? /poly_Fadjoin [p [Hp ->]] ->].
 rewrite (kHomExtend_poly (kHom1 K K) (Hroot _ Ha) Hp).
 rewrite (eq_map_poly (fun x => id_lfunE x)).
 rewrite map_polyE map_id polyseqK.
 case/poly_Fadjoin: (Hr _ Ha) => q [Hq ->].
 by rewrite -horner_comp mempx_Fadjoin ?polyOver_comp.
transitivity (g x).
 apply: (kAut_pick_eq (subsetKFadjoin K x) HAuta).
  by apply: mem_repr_coset.
 by apply: memx_Fadjoin.
rewrite /g {}Hab.
symmetry.
apply: (kAut_pick_eq (subsetKFadjoin K x)); first last.
  by apply: memx_Fadjoin.
 by apply: mem_repr_coset.
rewrite kAutE (kHomExtendkHom (kHom1 K K) (subv_refl K) (Hroot _ Hb)).
apply/subvP => ? /memv_imgP [? /poly_Fadjoin [p [Hp ->]] ->].
rewrite (kHomExtend_poly (kHom1 K K) (Hroot _ Hb) Hp).
rewrite map_poly_id => [|xx _ /=]; last by rewrite id_lfunE.
case/poly_Fadjoin: (Hr _ Hb) => q [Hq ->].
by rewrite -horner_comp mempx_Fadjoin ?polyOver_comp.
Qed.

Lemma galois_dim : forall (K E : {subfield L}), galois K E ->
 \dim E = (\dim K * #|'Aut(E | K)%g|)%N.
Proof.
move => K E.
case/and3P => HKE.
move/(separableSeparableGenerator)/(_ HKE) => -> Hnorm.
rewrite dim_Fadjoin.
congr (_ * _)%N.
by rewrite separable_dim // separableGeneratorSep.
Qed.

(* This theorem is stated backwards from the usual theorem.  This is 
   because I was folling theorem VI.8.7(ii) from "A Course in
   Constructive Algebra".  They give the result this way because it is,
   in general, a stronger form than saying that K is the fixed field of
   'Aut(E | K).  However, we are not in a general setting and all our
   subfields are detachable subfields.  In our case the ususal
   formulation is equivalent.  I should rewrite this theorem in the
   usual way. *)
Lemma GaloisUnfixedField (K E : {subfield L}) : galois K E ->
 forall a, a \in E -> a \notin K -> exists x, (x \in 'Aut(E | K)%g) && 
   (val (repr x) a != a).
Proof.
case/and3P => [HKE Hsep Hnorm] a HaE.
rewrite elemDeg1 -eqSS -size_minPoly.
case/normalP/(_ a HaE): (Hnorm) (root_minPoly K a) => r Hr Hmin.
rewrite Hmin root_prod_XsubC => Har.
move: (size_prod_XsubC r id) => Hsz1 Hsz2.
have [b Hbr Hba] : exists2 b, b \in r & b != a.
 move/separableP/(_ _ HaE): Hsep.
 rewrite /separableElement Hmin separable_prod_XsubC.
 move: r {Hr Hmin} Har Hsz1 Hsz2 => [//|x [|y r]]; first by move => _ ->.
 rewrite /= !inE.
 case: (eqVneq a x) => [->|Hax] _ _ _.
  rewrite negb_or.
  move => /andP [/andP [Hxy _] _].
  exists y; last by rewrite eq_sym.
  by rewrite !inE eqxx orbT.
 move => _.
 exists x; last by rewrite eq_sym.
 by rewrite !inE eqxx.
have: kHom K (Fadjoin K a) (kHomExtend K \1%VF a b).
 rewrite kHomExtendkHom ?kHom1 ?subv_refl //.
 rewrite (eq_map_poly (fun x => id_lfunE x)) map_polyE map_id polyseqK.
 by rewrite Hmin root_prod_XsubC.
case/(kHomExtendLAut (subsetKFadjoin K a)) => f /andP [HKf /eqvP Hf].
move/forallP/(_ f)/implyP/(_ HKf): Hnorm => HfE.
have: kAut K E (val f).
 by rewrite /kAut HfE andbT (kHom_subv _ HKf) // subvf.
case/(kAut_Aut HKE) => x HxAut /(_ _ (mem_repr_coset _)) Hx.
exists x.
rewrite HxAut -Hx // Hf ?memx_Fadjoin //.
rewrite -{2}[a]hornerX.
have Hminb : root (map_poly \1%VF (minPoly K a)) b.
 rewrite (eq_map_poly (fun x => id_lfunE x)) map_polyE map_id polyseqK.
 by rewrite Hmin root_prod_XsubC.
rewrite (kHomExtend_poly (kHom1 K K) Hminb) ?polyOverX //.
rewrite (eq_map_poly (fun x => id_lfunE x)) map_polyE map_id polyseqK.
by rewrite hornerX.
Qed.

Lemma galois_factors_subproof (K E : {subfield L}) : (K <= E)%VS ->
 (forall a, a \in E -> a \notin K -> exists x, (x \in 'Aut(E | K)%g) && 
   (val (repr x) a != a)) ->
 (forall a, a \in E -> 
   exists r, [/\
     r \subset 'Aut(E | K)%g,
     uniq (map (fun i : coset_of [set x : LAut | kAut E fullv (val x)] =>
                         ((val (repr i)) a)) r) &
     minPoly K a = \prod_(i <- r)('X - (val (repr i) a)%:P)]).
Proof.
pose f (j : L) := ('X - j%:P).
move => HKE Hgal a HaE.
pose h (i : coset_of [set x : LAut | kAut E fullv (val x)])
      := ((val (repr i)) a).
suff : forall n, n.+1 < size (minPoly K a) -> 
        exists r, let r' := 
           map (fun i : coset_of [set x : LAut | kAut E fullv (val x)] =>
                         ((val (repr i)) a)) r 
         in [/\ r \subset 'Aut(E | K)%g,  uniq r',
                (size r') = n.+1 &
                \prod_(i <- r')('X - i%:P) %| minPoly K a].
 rewrite size_minPoly.
 case/(_ _ (leqnn _)) => r [Haut Hr Hnr Hmin].
 exists r; split => //.
 apply/eqP.
 rewrite -(big_map h predT f).
 rewrite -eqp_monic ?monic_minPoly ?monic_prod_XsubC //.
 rewrite eqp_sym -dvdp_size_eqp // size_prod_XsubC.
 by rewrite size_minPoly Hnr.
elim => [|n IH] Hn.
 exists [:: 1%g]; split => //; last first.
  rewrite big_cons big_nil mulr1 dvdp_XsubCl repr_coset1 /= id_lfunE.
  by rewrite root_minPoly.
 apply/subsetP.
 move => x.
 rewrite inE.
 move/eqP ->.
 apply: group1.
case/(ltn_trans (leqnn _))/IH: (Hn) => {IH} r [Haut Hr Hnr Hmin].
set g := \prod_ (i <- _) _ in Hmin.
have := (minPoly_irr _ Hmin).
move/contra.
rewrite negb_or -size_poly_eq1 {2}/g size_prod_XsubC Hnr andbT.
rewrite -(dvdp_size_eqp Hmin) {1}/g size_prod_XsubC Hnr neq_ltn Hn.
case/(_ isT)/allPn => c Hcg HcK.
have/allP : g \in polyOver E.
 rewrite /g big_map.
 rewrite (big_nth 1%g) big_mkord.
 apply: rpred_prod => i _.
 rewrite polyOverXsubC /=.
 move/subsetP/allP/(all_nthP 1%g)/(_ _ (@ltn_ord _ i))/(Aut_kAut HKE): Haut.
 case/(_ _ (mem_repr_coset _))/andP => _ /eqP => HE.
 by rewrite -[in X in (_ \in X)]HE memv_img.
move/(_ _ Hcg) => HcE.
case/(_ _ HcE HcK): Hgal => x /andP [Hx Hxc].
have/allPn : ~~(all (fun x => x \in (map h r)) (map (val (repr x)) (map h r))).
 move: Hxc.
 apply: contra.
 move/allP => Hsubset.
 case/(nthP 0): Hcg => i _ <-.
 rewrite -coef_map.
 apply/eqP.
 move: i.
 apply/polyP.
 rewrite rmorph_prod.
 transitivity (\prod_(i <- map h r)('X - (val (repr x) i)%:P)).
  apply: eq_bigr => i _.
  by rewrite rmorphB /= map_polyX map_polyC.
 rewrite -(big_map (val (repr x)) predT f).
 apply/eqP.
 rewrite -eqp_monic ?monic_prod_XsubC // -dvdp_size_eqp.
  by rewrite !size_prod_XsubC size_map.
 apply: uniq_roots_dvdp.
  apply/allP => b Hb.
  rewrite root_prod_XsubC.
  by apply: Hsubset.
 rewrite uniq_rootsE map_inj_uniq //.
 (* TODO: abstract this *)
 move => b d Hbd.
 rewrite -[b]id_lfunE -[d]id_lfunE.
 move/eqP/lker0_compVf: (LAut_ker0 (repr x)) <-.
 by rewrite !comp_lfunE /= Hbd.
rewrite -map_comp.
case => ? /mapP [y Hyr ->] Hyx.
have Hy : y \in ('Aut(E | K))%g by move/subsetP: Haut; apply.
have Huniq : uniq (map h ((y * x)%g :: r)).
 by rewrite /= Hr andbT [h _]Aut_mul.
exists (cons (y * x)%g r); split.
- by rewrite subset_all /= -subset_all Haut groupM.
- by apply: Huniq.
- by rewrite /= Hnr.
- rewrite uniq_roots_dvdp //; last by rewrite uniq_rootsE; apply: Huniq.
  apply/allP => ? /mapP [z Hz ->].
  apply: (kHom_rootK _ HKE); rewrite ?minPolyOver ?root_minPoly //.
  suff HyAut : z \in 'Aut(E | K)%g.
   by case/andP: (Aut_kAut HKE HyAut (mem_repr_coset _)).
  move: Hz.
  rewrite inE.
  case/orP; last by move: z; apply/subsetP.
  move/eqP ->.
  by rewrite groupM.
Qed.

Lemma galois_factors (K E : {subfield L}) : 
 reflect ((K <= E)%VS /\ (forall a, a \in E -> 
   exists r, [/\
     r \subset 'Aut(E | K)%g,
     uniq (map (fun i : coset_of [set x : LAut | kAut E fullv (val x)] =>
                         ((val (repr i)) a)) r) &
     minPoly K a = \prod_(i <- r)('X - (val (repr i) a)%:P)]))
   (galois K E).
Proof.
pose f (j : L) := ('X - j%:P).
apply: (iffP idP).
 move => Hgal.
 case/and3P: (Hgal) => HKE _ _.
 split; first done.
 move/GaloisUnfixedField: Hgal => Hgal.
 by apply: galois_factors_subproof.
move => [HKE H].
apply/and3P; split; first done.
 apply/separableP => a /H [r [_ Hr Hmin]].
 pose h (i : coset_of [set x : LAut | kAut E fullv (val x)])
       := ((val (repr i)) a).
 by rewrite /separableElement Hmin -(big_map h predT f) separable_prod_XsubC.
apply/normalP => a Ha.
case/H: (Ha) => r [/subsetP Haut Hr Hmin].
pose h (i : coset_of [set x : LAut | kAut E fullv (val x)])
      := ((val (repr i)) a).
exists (map h r); last by rewrite big_map.
apply/allP => ? /mapP [x Hx ->].
case/andP: (Aut_kAut HKE (Haut _ Hx) (mem_repr_coset _)) => _.
move/eqP <-.
by rewrite memv_img.
Qed.

Lemma galois_fixedField (K E : {subfield L}) : reflect
 ((K <= E)%VS /\ FixedField 'Aut(E | K)%g = K)
 (galois K E).
Proof.
apply: (iffP idP).
 move => Hgal.
 case/and3P: (Hgal) => HKE _ _.
 split; first done.
 apply: subv_anti.
 apply/andP; split; last by apply: galoisAdjuctionA.
 apply/subvP => a /FixedFieldP [HaE HFF].
 rewrite -[_ \in _]negbK.
 apply/negP.
 move/GaloisUnfixedField/(_ _ HaE): Hgal => Hgal.
 case/Hgal => x /andP [Hx].
 apply/negP.
 rewrite negbK.
 apply/eqP.
 by apply HFF.
move => [HKE H].
apply/galois_factors.
split; first done.
apply: galois_factors_subproof => //.
move => a HaE HaK.
apply/existsP.
move: HaK.
apply: contraR.
rewrite negb_exists -{2}H.
move/forallP => Hall.
apply/FixedFieldP; split; first done.
move => // x Hx.
apply/eqP.
move: (Hall x).
by rewrite negb_and Hx negbK.
Qed.

Lemma mem_galoisTrace (K E : {subfield L}) a :
 galois K E -> a \in E -> galoisTrace K E a \in K.
Proof.
case/galois_fixedField => HKE HK.
rewrite -{2}HK.
by apply: autTraceFixedField.
Qed.

Lemma mem_galoisNorm (K E : {subfield L}) a :
 galois K E -> a \in E -> galoisNorm K E a \in K.
Proof.
case/galois_fixedField => HKE HK.
rewrite -{2}HK.
by apply: autNormFixedField.
Qed.

Lemma HilbertsTheorem90 (K E : {subfield L}) x a :
 galois K E -> (<[x]> = 'Aut(E | K))%g -> a \in E ->
 reflect (exists2 b, b \in E /\ b != 0 & a = b / (val (repr x) b))
         (galoisNorm K E a == 1).
Proof.
case/and3P => HKE _ _ Hx HaE.
apply: (iffP eqP); last first.
 case => b [HbE Hb0] ->.
 have HxEK : x \in 'Aut(E | K)%g by rewrite -Hx cycle_id.
 by rewrite galoisNormM galoisNormV normAut // mulfV // galoisNorm_eq0.
move => Hnorm.
have Ha0 : a != 0 by rewrite -(galoisNorm_eq0 K E) Hnorm oner_neq0.
pose n := #[x]%g.
pose c_ i := \prod_(j < i) (val (repr (x ^+ j)%g) a).
have HcE i : c_ i \in E.
 elim: i => [|i IH]; first by rewrite [c_ _]big_ord0 mem1v.
 by rewrite /c_ big_ord_recr memv_mul // (memv_aut HKE) // -Hx mem_cycle.
have Hxc i : (val (repr x) (c_ i)) = a ^-1 * (c_ i.+1).
 rewrite rmorph_prod /c_ big_ord_recl expg0 repr_coset1 id_lfunE mulKf //.
 apply: eq_bigr => j _.
 by rewrite expgSr Aut_mul.
pose f_ i := repr (x ^+ i)%g.
have HxE i : (val (f_ i) @: E)%VS = E.
 move: (mem_cycle x i).
 rewrite Hx.
 by case/(Aut_kAut HKE)/(_ (mem_repr_coset _))/andP => _ /eqP.
have Hexp_inj : injective (fun i : ordinal_finType n => (x ^+ i)%g).
 case Hxn : n => [|m]; first by case.
 case: m Hxn => [|m] Hxn; first by move => i j; rewrite !ord1.
 have Hxn' : m.+2 = #[x]%g.-2.+2 by rewrite [#[x]%g]Hxn.
 rewrite Hxn'.
 move => i j Hij.
 by move/injmP: (cyclic.injm_Zpm x); apply; last done; 
      rewrite /= /Zp [X in (1 < X)%N]Hxn inE.
have Huniq : uniq [seq (val (f_ (nat_of_ord i)) \o projv E)%VF| i <- enum 'I_n].
 apply: (@uniq_aut K) => [i |]; first by rewrite -Hx mem_cycle.
 by rewrite map_inj_uniq ?enum_uniq.
have Hexistb : (existsb i : 'I_n, c_ i != 0).
 apply/existsP.
 exists (Ordinal (order_gt0 _)).
 by rewrite /c_ big_ord0 oner_neq0.
pose Sigma := \sum_(i : 'I_n) (amull (c_ i) \o val (f_ i))%VF.
have: ((E <= lker Sigma)%VS -> forallb i : 'I_n, c_ i == 0).
 move => HE.
 apply/forallP => i.
 apply/eqP.
 apply:(LAut_independent (fun i : 'I_n => HxE i) Huniq (fun i : 'I_n => HcE i)).
 done.
move/contra/(_ Hexistb).
rewrite -diffv_eq0.
set V := (_ :\: _)%VS.
move: (subvP (diffvSl _ _) _ (memv_pick V)) => HbE.
rewrite -vpick0 => Hb.
have : vpick V \notin lker Sigma.
 apply: contra Hb.
 move/(conj (memv_pick V))/andP.
 by rewrite -memv_cap capv_diff memv0.
rewrite memv_ker => HSigmaV.
exists (Sigma (vpick V)).
 split; last done.
 rewrite sum_lfunE.
 apply: memv_suml => i _.
 rewrite comp_lfunE /= lfunE /=.
 by rewrite memv_mul // -[in X in _ \in X](HxE i) memv_img.
apply: (canRL (mulfK _)); first by rewrite fmorph_eq0.
rewrite sum_lfunE rmorph_sum mulr_sumr /n -(prednK (order_gt0 x)).
rewrite big_ord_recr /=; symmetry; rewrite addrC big_ord_recl.
congr (_ + _).
  rewrite !lfun_simp /=.
  rewrite [c_ 0%N]big_ord0 /f_ expg0 repr_coset1 id_lfunE.
  rewrite rmorphM /= -Aut_mul //.
  rewrite -expgSr (prednK (order_gt0 x)) expg_order repr_coset1 id_lfunE.
  rewrite rmorph_prod -{1}Hnorm mulrA.
  congr (_ * _).
  rewrite /galoisNorm -Hx /n.
  have [-> | nt_x] := eqVneq x 1%g.
    by rewrite order1 cycle1 big_set1 big_ord0 mulr1 repr_group id_lfunE.
  rewrite -im_Zpm morphimEdom big_imset; last by apply/injmP; exact: injm_Zpm.
  rewrite -order_gt1 in nt_x; rewrite /= /Zp nt_x.
  rewrite (eq_bigl _ _ (fun i => in_setT i)) big_ord_recl repr_group id_lfunE.
  rewrite /Zpm /= -(subnKC nt_x) /=; congr (_ * _).
  by apply: eq_bigr => i _ /=; rewrite -Aut_mul // -expgSr.
apply: eq_bigr => i _.
rewrite !lfun_simp /= rmorphM mulrA.
rewrite rmorph_prod [c_ _]big_ord_recl expg0 repr_coset1 id_lfunE.
congr (_ * _ * _).
  apply eq_bigr => j _.
  by rewrite /= -Aut_mul // -expgSr.
by rewrite /= -Aut_mul // -expgSr.
Qed.

Section GaloisDim.

Variable E : {subfield L}.

Let Coset :=
 [finGroupType of coset_of [set x : LAut | kAut E fullv (val x)]].

Let g_ (i : Coset) := val (repr i).

Lemma uniq_projv_subproof 
  (s : {set Coset}) :
  uniq [seq (g_ (enum_val i) \o (projv E))%VF | i <- enum 'I_#|s|].
Proof.
rewrite map_inj_uniq; first by rewrite enum_uniq.
move => i j /= /lfunP Hij.
apply: enum_val_inj.
apply/eqP/(Aut_eq (mem_repr_coset _) (mem_repr_coset _)) => a /projv_id <-.
by rewrite -[_ (_ a)]comp_lfunE Hij comp_lfunE.
Qed.

Lemma dim_FixedField_subproof
  (s : {set Coset}) :
  (forall i : Coset, i \in s -> (g_ i @: E)%VS = E) ->
  #|s| * \dim (FixedField s) <= \dim E /\ 
  (group_set s -> \dim E <= #|s| * \dim (FixedField s)).
Proof.
move => HE.
pose f_ i := repr (@enum_val _ (pred_of_set s) i).
case: (@LAut_matrix_subproof E _ f_).
  move => i.
  apply: HE.
  by apply: enum_valP.
 apply: uniq_projv_subproof.
move => w_ HwE.
set M := \matrix_(_,_) _ => Hw.
set K := FixedField s.
rewrite [(_ * _)%N](_: _ = \dim (\sum_(i < #|s|) K * <[w_ i]>)); last first.
 suff/directvP-> : directv (\sum_i K * <[w_ i]>).
  rewrite -{1}[#|s|]subn0 -sum_nat_const_nat big_mkord.
  apply: eq_bigr => i _.
  rewrite /= dim_cosetv //.
  move: Hw.
  rewrite unitmxE unitfE.
  apply: contra => /eqP Hwi.
  rewrite (expand_det_col _ i).
  apply/eqP.
  apply: big1 => j _.
  by rewrite mxE Hwi rmorph0 mul0r.
 apply/directv_sum_independent => u_ Hu Hsum i _.
 pose x := \col_j (u_ j / w_ j).
 suff : M *m x = 0.
  move/(f_equal (fun a => invmx M *m a)).
  rewrite mulmx0 mulKmx // (memv_prodv_line_coef (Hu i isT)).
  move/colP/(_ i).
  rewrite !mxE => ->.
  by rewrite mul0r.
 apply/colP => j.
 rewrite !{1}mxE -[X in _ = X](rmorph0 [rmorphism of (val (f_ j))]) -{2}Hsum.
 rewrite rmorph_sum.
 apply: eq_bigr => k _.
 rewrite !mxE.
 move: (Hu k isT) => Huk.
 suff <- : val (f_ j) (u_ k / w_ k) = (u_ k / w_ k).
  by rewrite -rmorphM mulrC -(memv_prodv_line_coef Huk).
 case/FixedFieldP: (prodv_line_coefK Huk) => _; apply.
 by apply: enum_valP.
split.
 apply: dimvS.
 apply/subv_sumP => i _.
 apply/subvP => v Hv.
 move/memv_prodv_line_coef: (Hv) ->.
 apply: memv_mul; last done.
 by case/prodv_line_coefK/FixedFieldP: Hv.
move => Hs.
apply: dimvS.
apply/subvP => v HvE.
pose x := invmx M *m \col_i val (f_ i) v.
move: (group1 (Group Hs)).
rewrite -mem_enum -index_mem -cardE => H1.
have HMx : M *m x = \col_i val (f_ i) v by rewrite mulKVmx.
move/colP/(_ (Ordinal H1)): (HMx).
have H1s : 1%g \in enum s by rewrite mem_enum; apply: group1 (Group Hs).
rewrite !mxE /f_ (enum_val_nth 1%g) nth_index; last done.
rewrite repr_coset1 id_lfunE => <-.
apply: memv_sumr => i _.
rewrite mulrC memv_prod //; last first.
 rewrite mxE /f_ (enum_val_nth 1%g) nth_index; last done.
 by rewrite repr_coset1 id_lfunE memv_line.
apply/FixedFieldP.
split.
 move: i (0 : 'I_1).
 apply/matrixOverP.
 by rewrite mulmx_matrixOver -?invmx_matrixOver //; apply/matrixOverP => i j;
    rewrite mxE -(HE (enum_val i)) ?memv_img // enum_valP.
move => y Hy.
apply/eqP; rewrite -subr_eq0; apply/eqP.
transitivity ((map_mx (val (repr y)) x - x) i 0).
 by move: (x) => x'; rewrite !mxE.
transitivity ((0:'cV[L]_#|s|) i 0); last by rewrite mxE.
congr (fun_of_matrix _ i 0).
move: (Hy).
rewrite -mem_enum -index_mem -cardE => Hj.
have <- : enum_val (Ordinal Hj) = y.
 by rewrite (enum_val_nth 1%g) nth_index // mem_enum.
rewrite -[X in X = _](mulKmx Hw) -[X in _ = X](mulmx0 _ (invmx M)).
congr (_ *m _).
apply/eqP; rewrite mulmxBr HMx subr_eq0; apply/eqP.
set (j := Ordinal Hj).
clear -Hs HMx HvE HwE.
apply/colP => i.
rewrite !mxE.
suff [k Hk] : exists k, forall z, z \in E -> 
                                  val (f_ i) z = val (f_ j) (val (f_ k) z).
 rewrite Hk //.
 transitivity (val (f_ j) ((\col_i (val (f_ i)) v) k 0)); last by rewrite mxE.
 rewrite -HMx mxE rmorph_sum.
 apply: eq_bigr => l _.
 rewrite rmorphM.
 congr (_ * _); last by rewrite mxE.
 by rewrite !mxE Hk.
have Hks : (enum_val i * (enum_val j)^-1)%g \in Group Hs.
 by rewrite groupM ?groupV // enum_valP.
move: (Hks).
rewrite -mem_enum -index_mem -cardE.
move => Hk.
exists (Ordinal Hk) => z HzE.
rewrite -Aut_mul // (enum_val_nth 1%g) nth_index ?mulgKV //.
by rewrite mem_enum.
Qed.

Lemma maxDim_FixedField 
   (s : {set Coset}) :
   (forall i, i \in s -> (g_ i @: E)%VS = E) ->
   #|s|*\dim (FixedField s) <= \dim E.
Proof.
by case/dim_FixedField_subproof.
Qed.

Lemma dim_FixedField 
  (s : {group Coset}) :
  (forall i, i \in s -> (g_ i @: E)%VS = E) ->
  (#|s| * \dim (FixedField s) = \dim E)%N.
Proof.
case: s => s Hs.
case/dim_FixedField_subproof => Hle1.
move/(_ Hs) => Hle2.
apply/eqP.
by rewrite eqn_leq Hle1 Hle2.
Qed.

Lemma Aut_FixedField 
  (s : {group Coset}) :
  (forall i, i \in s -> (g_ i @: E)%VS = E) ->
  'Aut(E | (FixedField s))%g = s.
Proof.
move => HE.
symmetry.
apply/eqP.
rewrite eqEcard.
suff HsAut : (s \subset ('Aut(E | FixedField s))%g).
 rewrite HsAut.
 suff : #|('Aut(E | FixedField s))%g| * \dim (FixedField s) <= 
        #|s| * \dim (FixedField s).
  rewrite leq_mul2r.
  case/orP; last done.
  rewrite dimv_eq0 -subv0.
  move/subvP/(_ _ (mem1v _)).
  by rewrite memv0 -[_ == _]negbK oner_neq0.
 rewrite mulnC dim_FixedField // -galois_dim ?leqnn //.
 apply/galois_fixedField.
 have HFFE : (FixedField_aspace s <= E)%VS by apply: capvSl.
 split; first done.
 apply: subv_anti.
 by rewrite galoisAdjuctionA // FixedField_subset.
apply/subsetP => x.
case: (cosetP x) => f Hf -> Hfs.
rewrite mem_morphim //.
rewrite inE.
rewrite kAutE.
have Hff : f \in coset [set x : LAut | kAut E fullv (val x)] f.
 by rewrite val_coset // rcoset_refl.
apply/andP; split.
 apply/kHomP; split; last by move => ? ? _ _; rewrite rmorphM.
 move => a /FixedFieldP [HaE /(_ _ Hfs) Ha].
 rewrite -[X in _ = X]Ha.
 move: {Ha} a HaE. 
 by apply/(Aut_eq Hff (mem_repr_coset _)).
move: (HE _ Hfs) => HEfs.
rewrite -[X in (_ <= X)%VS]HEfs.
apply/subvP => _ /memv_imgP [a Ha ->].
apply/memv_imgP.
exists a; first done.
move: {Ha} a Ha.
by apply/(Aut_eq Hff (mem_repr_coset _)).
Qed.

End GaloisDim.

Section FundamentalTheoremOfGaloisTheory.

Variables E K : {subfield L}.
Hypothesis HKE : galois K E.

Section IntermediateField.

Variable M : {subfield L}.
Hypothesis HME : (M <= E)%VS.
Hypothesis HKM : (K <= M)%VS.

Lemma SubFieldGalois : galois M E.
Proof.
case/and3P : HKE => /subvP Hsub Hsep Hnorm.
rewrite /galois HME /=.
apply/andP; split.
 apply/separableP => a Ha.
 apply: (subsetSeparable HKM).
 by move/separableP: Hsep; apply.
apply/forallP => a.
apply/implyP => Ha.
by move/forallP/(_ a)/implyP/(_ (subv_kHom HKM Ha)): Hnorm.
Qed.

Lemma SubGroupGalois : 'Aut(E | M)%g \subset 'Aut(E | K)%g.
Proof.
rewrite quotientS //.
apply/subsetP => a.
rewrite !inE !kAutE.
case/andP => Ha ->.
rewrite andbT.
by apply: subv_kHom HKM Ha.
Qed.

Lemma FixedField_of_Aut : FixedField 'Aut(E | M)%g = M.
Proof.
by case/galois_fixedField: SubFieldGalois.
Qed.

Lemma OrderGaloisGroup : (#|'Aut(E | M)%g| * \dim(M) = \dim(E))%N.
Proof.
move/galois_dim: SubFieldGalois ->.
by rewrite mulnC.
Qed.

Hypothesis Hnorm : normal K M.

Lemma NormalGalois : galois K M.
Proof.
rewrite /galois HKM Hnorm /= andbT.
apply/separableP => a Ha.
move/(subvP)/(_ _ Ha): HME => HaE.
case/and3P: HKE => _.
move/separableP => Hsep _.
by apply: Hsep.
Qed.

Let f (y : coset_of [set x : LAut | kAut E fullv (val x)]) :=
     (coset [set x : LAut | kAut M fullv (val x)] (repr y)).

Let Aut_normal z : z \in 'Aut (E | K)%g -> kAut K M (val (repr z)).
Proof.
case/and3P: HKE => Hsub _ _.
move/(Aut_kAut Hsub)/(_ (mem_repr_coset _)) => /andP [HKz HEz].
apply/andP; split.
 apply/kHomP; split; last by move => ? ? _ _; rewrite rmorphM.
 by case/kHomP: HKz.
move/forallP/(_ (repr z))/implyP: Hnorm; apply.
apply/kHomP; split; last by move => ? ? _ _; rewrite rmorphM.
by case/kHomP: HKz.
Qed.

Let in_f x : x \in ('Aut(E | K))%g -> repr x \in f x.
move => Hfx.
rewrite val_coset; first by apply: rcoset_refl.
move/subsetP: (kAut_normal K M); apply.
rewrite inE.
by apply: Aut_normal.
Qed.

Let val_f x a : x \in ('Aut(E | K))%g -> a \in M ->
                val (repr x) a = val (repr (f x)) a.
Proof.
move => Hx.
move: a.
apply/(Aut_eq (in_f Hx) (mem_repr_coset _)).
by rewrite eqxx.
Qed.

Let f_is_morph :
  {in 'Aut(E | K)%g &, {morph f : x y / (x * y)%g >-> (x * y)%g}}.
Proof.
move => x y Hx Hy /=.
apply/eqP/(Aut_eq (in_f (groupM Hx Hy)) (mem_repr_coset _)) => b Hb.
have HbE : b \in E by move/subvP: HME; apply.
do 2 (rewrite Aut_mul; last done).
rewrite (val_f Hx); last done.
rewrite (val_f Hy); first done.
rewrite -(val_f Hx); last done.
case/andP: (Aut_normal Hx) => _.
move/eqP <-.
by rewrite memv_img.
Qed.

Let fmorph := Morphism f_is_morph.

Let f_ker : ('ker fmorph = 'Aut(E | M))%g.
Proof.
apply/eqP.
rewrite eqEsubset.
apply/andP; split; apply/subsetP => x.
 rewrite inE.
 case/andP => Hx.
 rewrite 2!inE.
 move/(Aut_eq (in_f Hx) (mem_repr_coset _)) => HxM.
 rewrite -[x]coset_reprK mem_quotient // inE.
 apply/andP; split.
  apply/kHomP; split; last by move => ? ? _ _; rewrite rmorphM.
  move => a Ha.
  by rewrite HxM // repr_coset1 id_lfunE.
 case/and3P: HKE => Hsub _ _.
 by case/andP: (Aut_kAut Hsub Hx (mem_repr_coset _)).
move => Hx.
have HxE : x \in ('Aut(E | K))%g by move/subsetP: SubGroupGalois; apply.
apply/kerP; first done.
apply/eqP.
apply/(Aut_eq (in_f HxE) (mem_repr_coset _)).
move => a Ha.
rewrite repr_coset1.
move/(Aut_kAut HME)/(_ (mem_repr_coset _))/andP : Hx => [/kHomP [Hx _] _].
move:(Hx _ Ha) ->.
by rewrite id_lfunE.
Qed.

Let f_img : (fmorph @* 'Aut(E | K) = 'Aut(M | K))%g.
Proof.
apply/eqP.
rewrite eqEsubset.
apply/andP; split; apply/subsetP => x.
 case/imsetP => y.
 rewrite inE.
 case/andP => Hy _ ->.
 case/(kAut_Aut HKM): (Aut_normal Hy) => z Hz /(_ _ (mem_repr_coset _)).
 rewrite /=.
 by move/(Aut_eq (in_f Hy) (mem_repr_coset _))/eqP ->.
move => Hx.
have HxKE : kAut K E (val (repr x)).
 apply/andP; split.
  apply/kHomP; split; last by move => ? ? _ _; rewrite rmorphM.
  case/andP: (Aut_kAut HKM Hx (mem_repr_coset _)) => /kHomP.
  by case.
 case/and3P: HKE => _ _.
 move/forallP/(_ (repr x))/implyP; apply.
 apply/kHomP; split; last by move => ? ? _ _; rewrite rmorphM.
 case/andP: (Aut_kAut HKM Hx (mem_repr_coset _)) => /kHomP.
 by case.
have : (coset _ (repr x)) \in ('Aut(E | K))%g.
 apply: mem_quotient.
 by rewrite inE.
set y := coset _ (repr x) => Hy.
suff -> : x = (fmorph y) by apply: mem_morphim.
apply/eqP.
apply/(Aut_eq (mem_repr_coset _) (mem_repr_coset _)).
move => a Ha.
rewrite -val_f //.
have Hxy : (repr x) \in y.
 rewrite val_coset; first by apply: rcoset_refl.
 move/subsetP: (kAut_normal K E); apply.
 by rewrite inE.
apply/(Aut_eq Hxy (mem_repr_coset _)); first by rewrite eqxx.
by move/subvP: HME; apply.
Qed.

Lemma NormalGaloisGroup : ('Aut(E | M) <| 'Aut(E | K))%g.
Proof.
rewrite -f_ker.
apply: ker_normal.
Qed.

Lemma NormalGaloisGroupIso : ('Aut(E | K) / 'Aut(E | M) \isog 'Aut(M | K))%g.
Proof.
rewrite -f_ker -f_img.
apply: first_isog.
Qed.

End IntermediateField.

Section IntermediateGroup.

Variable g : {group coset_of [set x : LAut | kAut E fullv (val x)]}.
Hypothesis Hg : g \subset 'Aut(E | K)%g.

Lemma SubGaloisField : (K <= FixedField g <= E)%VS.
Proof.
rewrite capvSl andbT.
apply/subvP => a Ha.
case/and3P: HKE => Hsub _ _.
apply/FixedFieldP; split.
 by move/subvP: Hsub; apply.
move => x Hxg.
move/subsetP/(_ _ Hxg): Hg.
move/(Aut_kAut Hsub)/(_ (mem_repr_coset _)).
rewrite kAutE.
by case/andP; case/kHomP; move/(_ _ Ha).
Qed.

Lemma FixedFieldGalois : galois (FixedField g) E.
Proof.
case/andP: SubGaloisField => HKFF HFFE.
apply/and3P; split; first done.
 apply/separableP => a Ha.
 apply: (subsetSeparable HKFF).
 by case/and3P: HKE => _ /separableP/(_ _ Ha).
apply/forallP => a.
apply/implyP => Ha.
case/and3P: HKE => _ _ /forallP/(_ a)/implyP; apply.
move: Ha.
by apply: subv_kHom.
Qed.

Lemma Aut_of_FixedField : 'Aut (E | FixedField g)%g = g.
Proof.
apply: Aut_FixedField => x Hx.
apply/eqP.
case/and3P: HKE => Hsub _ _.
move/subsetP/(_ _ Hx): Hg.
move/(Aut_kAut Hsub)/(_ (mem_repr_coset _)).
by case/andP.
Qed.

Lemma FixedField_dim : (#|g| * \dim (FixedField g))%N = \dim E.
Proof.
apply: dim_FixedField => x Hx.
apply/eqP.
case/and3P: HKE => Hsub _ _.
move/subsetP/(_ _ Hx): Hg.
move/(Aut_kAut Hsub)/(_ (mem_repr_coset _)).
by case/andP.
Qed.

Hypothesis Hnorm : 'Aut(E | K)%g \subset 'N(g)%g.

Lemma NormalGaloisField : galois K (FixedField g).
Proof.
case/andP: SubGaloisField => HKFF HFFE.
apply/and3P; split; first done.
 apply/separableP => a Ha.
 move/subvP/(_ _ Ha): HFFE => HaE.
 by case/and3P: HKE => _ /separableP/(_ _ HaE) Hsep.
apply/forallP => a.
apply/implyP => HaK.
have HaE : (val a @: E)%VS = E.
 case/and3P: HKE => _ _.
 by move/forallP/(_ a)/implyP/(_ HaK)/eqP.
pose x := coset [set x : LAut | kAut E fullv (val x)] a.
have HaKE : a \in [set x0 | kAut K E (val x0)].
 rewrite inE.
 apply/andP; split; last by apply/eqP.
 apply/kHomP; split; last by move => ? ? _ _; rewrite rmorphM.
 by case/kHomP: HaK.
have Hx : x \in 'Aut(E | K)%g.
 apply: mem_morphim; last done.
 by move/subsetP: (kAut_normal K E); apply.
move/subsetP/(_ _ Hx)/normP: Hnorm => Hxg.
set Ma := (val a @: _)%VS.
have : galois Ma E.
 apply: SubFieldGalois.
  by rewrite -[X in (_ <= X)%VS]HaE limgS.
 apply/subvP => b Hb.
 case/kHomP: HaK => /(_ _ Hb) <- _.
 rewrite memv_img //.
 by move/subvP: HKFF; apply.
rewrite /Ma.
case/galois_fixedField => _ <-.
case/galois_fixedField: FixedFieldGalois => _ <-.
apply/eqP; apply: f_equal; symmetry.
rewrite Aut_of_FixedField -[X in X = _]Hxg -[X in (X :^ x)%g]Aut_of_FixedField.
apply: Aut_conjg => //.
rewrite val_coset; first by apply: rcoset_refl.
move: (a) HaKE.
apply/subsetP.
by apply: kAut_normal.
Qed.

End IntermediateGroup.

End FundamentalTheoremOfGaloisTheory.

End Galois.

Section UseGalois.

Variables (F0 : fieldType) (L : fieldExtType F0).

Lemma splitting_field_normal p  :
  p \is a polyOver 1%VS -> splittingFieldFor 1 p {:L} -> isNormalFieldExt L.
Proof.
move=> F0p splitLp K x; pose q1 := minPoly 1 x.
have [autL _ DautL] := enum_kHom F0p splitLp.
suffices{K} autL_px q:
  q %| q1 -> size q > 1 -> has (fun f : 'End(L) => root q (f x)) autL.
- set q := minPoly K x; have: q \is monic by exact: monic_minPoly.
  have: q %| q1.
    by rewrite minPoly_dvdp ?root_minPoly ?(polyOverSv (sub1v K)) ?minPolyOver.
  elim: {q}_.+1 {-2}q (ltnSn (size q)) => // d IHd q leqd q_dv_q1.
  move=> mon_q; have [/size1_polyC Dq | q_gt1] := leqP (size q) 1.
    exists nil; rewrite big_nil Dq (inj_eq (@polyC_inj _)).
    by rewrite qualifE Dq lead_coefC in mon_q.
  have /hasP[f autLf /factor_theorem[q2 Dq]] := autL_px q q_dv_q1 q_gt1.
  have mon_q2: q2 \is monic by rewrite -(monicMr _ (monicXsubC (f x))) -Dq.
  rewrite Dq size_monicM -?size_poly_eq0 ?size_XsubC ?addn2 //= in leqd.
  have q2_dv_q1: q2 %| q1 by rewrite (dvdp_trans _ q_dv_q1) // Dq dvdp_mulr.
  rewrite Dq; have [r /eqP->] := IHd q2 leqd q2_dv_q1 mon_q2.
  by exists (f x :: r); rewrite big_cons mulrC.
elim: {q}_.+1 {-2}q (ltnSn (size q)) => // d IHd q leqd q_dv_q1 q_gt1.
without loss{d leqd IHd q_gt1} irr_q: q q_dv_q1 / irreducible_poly q.
  move=> IHq; apply: wlog_neg => not_autLx_q; apply: IHq => //.
  split=> // q2 q2_neq1 q2_dv_q; apply: contraR not_autLx_q => ltq2q.
  have{q2_neq1} q2_gt1: size q2 > 1.
    rewrite ltn_neqAle eq_sym q2_neq1 size_poly_gt0.
    apply: contraTneq q_gt1 => q2_0; rewrite -(divpK q2_dv_q) q2_0 mulr0.
    by rewrite size_poly0.
  have ltq2d: size q2 < d.
    rewrite -ltnS (leq_trans _ leqd) // ltnS ltn_neqAle dvdp_size_eqp //.
    by rewrite ltq2q dvdp_leq // -size_poly_eq0 -(subnKC q_gt1).
  apply: sub_has (IHd _ ltq2d (dvdp_trans q2_dv_q q_dv_q1) q2_gt1) => f.
  by rewrite !root_factor_theorem => /dvdp_trans->.
have{irr_q} [Lz [inLz [z qz0]]]: {Lz : fieldExtType F0 &
  {inLz : {lrmorphism L -> Lz} & {z : Lz | root (map_poly inLz q) z}}}.
- have [Lz0 _ [z qz0 defLz]] := irredp_FAdjoin irr_q.
  pose Lz := baseField_extFieldType Lz0.
  pose inLz : {rmorphism L -> Lz} := [rmorphism of in_alg Lz0].
  suffices inLzZ: scalable inLz by exists Lz, (AddLRMorphism inLzZ), z.
  move=> a u; rewrite -{1}mulr_algl rmorphM /=.
  by rewrite -{1}baseField_scaleE mulr_algl.
have imL1: (linfun inLz @: 1 = 1)%VS by rewrite limg_line lfunE rmorph1.
have imLaspace: is_aspace (limg (linfun inLz)).
  rewrite /is_aspace has_algid1; last by rewrite memvE -imL1 limgS ?sub1v.
  apply/prodvP=> _ _ /memv_imgP[y1 _ ->] /memv_imgP[y2 _ ->].
  by rewrite !{1}lfunE -rmorphM -lfunE memv_img ?memvf.
pose imL := ASpace imLaspace; pose pz := map_poly inLz p.
have imLin u: inLz u \in imL by rewrite -lfunE memv_img ?memvf.
have F0pz: pz \is a polyOver 1%VS.
  apply/polyOverP=> i; rewrite -imL1 coef_map /= -lfunE memv_img //.
  exact: (polyOverP F0p).
have{splitLp} splitLpz: splittingFieldFor 1 pz imL.
  have [r def_p defL] := splitLp; exists (map inLz r).
    move: def_p; rewrite -(eqp_map inLz) rmorph_prod big_map; congr (_ %= _).
    by apply: eq_big => // y _; rewrite rmorphB /= map_polyX map_polyC.
  apply/eqP; rewrite eqEsubv; apply/andP; split.
    by apply/genFieldP; rewrite sub1v; split=> // _ /mapP[y r_y ->].
  rewrite /= -{def_p}defL.
  elim/last_ind: r => [|r y IHr] /=; first by rewrite imL1.
  rewrite map_rcons !genField_rcons /=.
  apply/subvP=> _ /memv_imgP[_ /poly_Fadjoin[p1 [r_p1 ->]] ->].
  rewrite lfunE -horner_map /= mempx_Fadjoin //=; apply/polyOverP=> i.
  by rewrite coef_map (subvP IHr) //= -lfunE memv_img ?(polyOverP r_p1).
have [f homLf fxz]: exists2 f : 'End(Lz), kHom 1 imL f & f (inLz x) = z.
  pose q1z := minPoly 1 (inLz x).
  have Dq1z: map_poly inLz q1 %| q1z.
    have F0q1z i: exists a, q1z`_i = a%:A by exact/vlineP/polyOverP/minPolyOver.
    have [q2 Dq2]: exists q2, q1z = map_poly inLz q2.
      exists (\poly_(i < size q1z) (sval (sig_eqW (F0q1z i)))%:A).
      rewrite -{1}[q1z]coefK; apply/polyP=> i; rewrite coef_map !{1}coef_poly.
      by case: sig_eqW => a; case: ifP; rewrite /= ?rmorph0 ?linearZ ?rmorph1. 
    rewrite Dq2 dvdp_map minPoly_dvdp //.
      apply/polyOverP=> i; have[a] := F0q1z i; rewrite -(rmorph1 inLz) -linearZ.
      by rewrite Dq2 coef_map => /fmorph_inj->; rewrite rpredZ ?mem1v.
    by rewrite -(fmorph_root inLz) -Dq2 root_minPoly.
  have q1z_z: root q1z z.
    rewrite !root_factor_theorem in qz0 *.
    by apply: dvdp_trans qz0 (dvdp_trans _ Dq1z); rewrite dvdp_map.
  have map1q1z_z: root (map_poly \1%VF q1z) z.
    by rewrite map_poly_id => // ? _; rewrite lfunE.
  pose f0 := kHomExtend 1 \1 (inLz x) z.
  have{map1q1z_z} hom_f0 : kHom 1 (Fadjoin 1 (inLz x)) f0.
    by apply: kHomExtendkHom map1q1z_z => //; apply: kHom1.
  have{splitLpz} splitLpz: splittingFieldFor (Fadjoin 1 (inLz x)) pz imL.
    have [r def_pz defLz] := splitLpz; exists r => //.
    apply/eqP; rewrite eqEsubv -{2}defLz genFieldSl ?sub1v // andbT.
    apply/genFieldP; split; last by rewrite -defLz; apply: mem_genField.
    by rewrite -subsetFadjoinE sub1v -lfunE memv_img ?memvf.
  have [f homLzf Df] := kHom_extends (sub1v _) hom_f0 F0pz splitLpz.
  have [-> | x'z] := eqVneq (inLz x) z.
    by exists \1%VF; rewrite ?lfunE ?kHom1.
  exists f => //; rewrite -Df ?memx_Fadjoin ?(kHomExtendX _ (kHom1 1 1)) //.
  apply: contra x'z; rewrite elemDeg1 -eqSS -size_minPoly -/q1z => sz_q1z.
  have{Dq1z} Dq1z: q1z %= 'X - (inLz x)%:P.
    rewrite eqp_sym -dvdp_size_eqp ?size_XsubC 1?eq_sym //.
    by rewrite dvdp_XsubCl root_minPoly.
  by rewrite (eqp_root Dq1z) root_XsubC eq_sym in q1z_z.
pose f1 := ((linfun inLz)^-1 \o f \o linfun inLz)%VF.
have /kHomP[f1id fM] := homLf.
have Df1 u: inLz (f1 u) = f (inLz u).
  rewrite !lfunE /= !lfunE /= -lfunE limg_lfunVK //= -[limg _]/(asval imL).
  have [r def_pz defLz] := splitLpz.
  have []: all (mem r) r /\ inLz u \in imL by split; first exact/allP.
  rewrite -{1}defLz; elim/last_ind: {-1}r {u}(inLz u) => [|r1 y IHr1] u.
    by move=> _ F0u; rewrite f1id // (subvP (sub1v _)).
  rewrite all_rcons genField_rcons => /andP[rr1 ry] /poly_Fadjoin[pu [r1pu ->]].
  rewrite (kHom_horner homLf) -defLz; last exact: mem_genField; last first.
    by apply: polyOverS r1pu; apply/subvP/genFieldSr/allP.
  apply: rpred_horner.
    by apply/polyOverP=> i; rewrite coef_map /= defLz IHr1 ?(polyOverP r1pu).
  rewrite mem_genField // -root_prod_XsubC -(eqp_root def_pz).
  rewrite (kHom_rootK homLf) ?sub1v //; first by rewrite -defLz mem_genField.
  by rewrite (eqp_root def_pz) root_prod_XsubC.
apply/hasP; exists f1; last by rewrite -(fmorph_root inLz) /= Df1 fxz.
rewrite -DautL; apply/kHomP; split=> [_ /vlineP[a ->] | u v _ _].
  by apply: (fmorph_inj inLz); rewrite /= Df1 !linearZ rmorph1 /= f1id ?mem1v.
by apply: (fmorph_inj inLz); rewrite rmorphM /= !Df1 rmorphM fM ?imLin.
Qed.

Lemma splitting_field_galois p :
    p \is a polyOver 1%VS -> splittingFieldFor 1 p {:L} ->
    separablePolynomial p ->
  {normL : isNormalFieldExt L & galois normL 1 fullv}.
Proof.
move=> F0p splitLp sep_p; have nL := splitting_field_normal F0p splitLp.
exists nL; apply/and3P; split; first exact: subvf; last first.
  apply/normalP=> y _; have [r /eqP->] := nL 1%AS y.
  by exists r => //; apply/allP=> cy _; rewrite /= memvf.
have [r Dp <-] := splitLp; apply/separableP=> x /separableinK/=.
have{Dp}: all (root p) r.
  by apply/allP=> z r_z; rewrite (eqp_root Dp) root_prod_XsubC.
elim/last_ind: r => [//| r z IHr].
rewrite all_rcons genField_rcons => /andP[pz0 pr0] sep_x; apply: IHr pr0 _.
apply: separableFadjoinExtend sep_x; apply: subsetSeparable (sub1v _) _.
by apply/separableElementP; exists p.
Qed.

End UseGalois.
