Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
Require Import tuple finfun bigop ssralg poly polydiv.
Require Import finset fingroup zmodp morphism perm quotient cyclic.
Require Import matrix mxalgebra vector falgebra fieldext separable.

(******************************************************************************)
(*                                                                            *)
(*       f \is a kHom K E == (f:'End(L)) is a ring morphism on E and fixes K. *)
(*       f \is a kAut K E == (f:'End(L)) is a kHom K E and f @: E == E.       *)
(*                                                                            *)
(*            'Aut(E / K) == the group of automorphisms of E that fix K.      *)
(*              Aut K E f == Constructs an 'Aut(E / K) when f \is a kAut K E. *)
(*           fixedField G == The field fixed by the set of automorphisms G .  *)
(*                           fixedField set0 == E when G \subset 'Aut(E / K). *)
(*        normalField K E == E is a normal field extension of K.              *)
(*             galois K E == E is a normal and separable field extension of K.*)
(*        pickAut K M E f == picks some 'Aut(E|K) extending f \is a kHom K M  *)
(*                           when normalfield E K.                            *)
(*      galoisTrace K E a == \sum_(x | x \in ('Aut(E / K))) (x a)             *)
(*       galoisNorm K E a == \prod_(x | x \in ('Aut(E / K))) (x a)            *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "''Aut' ( A / B )"
  (at level 8, A at level 2, format "''Aut' ( A  /  B )").

Open Local Scope ring_scope.
Import GRing.Theory.
Import FalgLfun.

(* Move this to vector.v *)
Lemma limg_eq (F:fieldType) (vT wT:vectType F) (V : {vspace vT})
  (f g : 'Hom(vT, wT)) : {in V, f =1 g} -> (f @: V = g @: V)%VS.
Proof.
move => Hfg.
apply:subv_anti.
apply/andP; split; apply/subvP => ? /memv_imgP [y Hy ->].
  by rewrite Hfg // memv_img.
by rewrite -Hfg // memv_img.
Qed.

(* Move this to vector.v *)
Lemma eqvP (F:fieldType) (vT wT:vectType F) (V : {vspace vT})
  (f g: 'Hom(vT,wT)) : reflect {in V, f =1 g} (V <= lker (f - g))%VS.
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

Section SplittingFieldFor.

Variables (F : fieldType) (L : fieldExtType F).

Definition splittingFieldFor (U : {vspace L}) (p : {poly L}) (V : {vspace L}) :=
  exists2 rs, p %= \prod_(z <- rs) ('X - z%:P) & <<U & rs>>%AS = V.

Lemma splittingFieldForS (K E : {subfield L}) p :
  (K <= E)%VS -> splittingFieldFor K p fullv -> splittingFieldFor E p fullv.
Proof.
move=> sKE [rs Dp genL]; exists rs => //; apply/eqP.
by rewrite eqEsubv subvf -genL adjoin_seqSl.
Qed.

End SplittingFieldFor.

Section kHom.

Variable F0 : fieldType.
Variable L : fieldExtType F0.

Let F : {subfield L} := 1%AS.

Implicit Types (U V : {vspace L}).
Implicit Types (K Ka Kb E Ea Eb : {subfield L}).
Implicit Types (f g : 'End(L)).

Section Definitions.

(* Should I make this canonical by setting fixing (f @: E)^C ? *)
Definition kHom U V :=
  [qualify a f : 'End(L) | (U <= fixedSpace f)%VS && (f \is ahom_in V)].

Lemma kHom1 U V : \1%VF \is a kHom U V.
Proof.
rewrite qualifE (id_is_ahom V) andbT.
apply/subvP => u _.
apply/fixedSpaceP.
by rewrite id_lfunE.
Qed.

Lemma kHomP K V f :
 reflect ({in K, forall x, f x = x} /\
          {in V &, forall x y, f (x * y) = f x * f y})
 (f \is a kHom K V).
Proof.
apply: (iffP andP); case.
  move/subvP => HK /is_ahom_inP [HV _].
  split; last done.
  move => x Hx.
  apply/fixedSpaceP.
  by apply: HK.
move => HK HV.
split.
  apply/subvP => v Hv.
  apply/fixedSpaceP.
  by apply HK.
apply/is_ahom_inP; split; first done.
apply: HK.
by rewrite mem1v.
Qed.

Lemma kHomFixedPoly K E f p : f \is a kHom K E -> p \is a polyOver K ->
  map_poly f p = p.
Proof.
case/kHomP => HK _ /polyOverP Hp.
by apply/polyP => i; rewrite coef_map /= HK ?Hp.
Qed.

Definition kAut U V := [qualify a f | (f \is a kHom U V) && (f @: V == V)%VS].

Fact kHomExtendF_subproof E f x y :
  linear (fun z => (map_poly f (poly_for_Fadjoin E x z)).[y]).
Proof.
move=> k a b; rewrite linearP /= raddfD hornerE; congr (_ + _).
rewrite -[rhs in _ = rhs]mulr_algl -hornerZ /=; congr _.[_].
by apply/polyP => i; rewrite !(coefZ, coef_map) /= !mulr_algl linearZ.
Qed.
Definition kHomExtend E f x y := linfun (Linear (kHomExtendF_subproof E f x y)).

Lemma kHomExtendE E f x y z :
  kHomExtend E f x y z = (map_poly f (poly_for_Fadjoin E x z)).[y].
Proof. by rewrite lfunE. Qed.

End Definitions.

Lemma kHomSl Ka Kb E f : (Ka <= Kb)%VS -> f \in kHom Kb E -> f \in kHom Ka E.
Proof.
move => HK.
case/andP => HKb HE.
apply/andP.
by rewrite (subv_trans _ HKb).
Qed.

Lemma kHomSr K Ea Eb f : (Ea <= Eb)%VS -> f \in kHom K Eb -> f \in kHom K Ea.
Proof.
move/subvP => HE.
case/kHomP => HK HEb.
apply/kHomP; split => // x y Hx Hy.
by apply: HEb; apply: HE.
Qed.

Lemma kHomS Ka Kb Ea Eb f : (Ka <= Kb)%VS -> (Ea <= Eb)%VS ->
  f \in kHom Kb Eb -> f \in kHom Ka Ea.
Proof. by move => HK HE /(kHomSl HK); apply kHomSr. Qed.

Lemma kHom_eq K E f g : (K <= E)%VS -> {in E, f =1 g} ->
  (f \is a kHom K E) = (g \is a kHom K E).
Proof.
move => HKE Hfg.
wlog suff: f g Hfg / f \is a kHom K E -> g \is a kHom K E.
  move => H.
  apply/idP/idP; first by apply: H.
  by apply: H => ? ?; symmetry; apply Hfg.
move => /kHomP [HfK HfE].
apply/kHomP; split => [a Ha | a b Ha Hb].
  rewrite /= -Hfg ?HfK //.
  by move/subvP: HKE; apply.
by rewrite -!Hfg ?HfE ?rpredM.
Qed.

Section kHomExtend.

Lemma kHomExtendX K E f x y : f \is a kHom K E -> x \notin E ->
  kHomExtend E f x y x = y.
Proof.
move=> homEf E'x; rewrite kHomExtendE poly_for_X //.
by rewrite (kHomFixedPoly homEf) ?hornerX ?polyOverX.
Qed.

Lemma kHom_inv K E f : f \in kHom K E -> forall x, x \in E -> f x^-1 = (f x)^-1.
Proof.
case/kHomP => HK HE.
move => x Hx.
case (eqVneq x 0) => [->|Hx0]; first by rewrite linear0 invr0 linear0.
move: (Hx).
rewrite -rpredV.
move/(HE _ _ Hx).
rewrite divff // HK ?mem1v // => H1.
rewrite -[(f x)^-1]mulr1 H1 mulrA mulVf ?mul1r //.
move/eqP: H1.
apply: contraL.
move/eqP ->.
by rewrite mul0r oner_neq0.
Qed.

Lemma kHom_dim K E f : f \in kHom K E -> \dim (f @: E) = \dim E.
Proof.
move => Hf.
case/kHomP: (Hf) => HK HE.
apply/limg_dim_eq/eqP.
rewrite -subv0.
apply/subvP => v.
rewrite memv_cap memv0 memv_ker.
case/andP => HvE.
apply: contraLR => Hv.
by rewrite -unitfE unitrE -(kHom_inv Hf) // -HE ?rpredV // mulfV // HK // mem1v.
Qed.

Lemma kHomRmorph_subproof K E f : f \in kHom K E ->
  rmorphism (f \o @vsval _ _ E).
Proof.
case/kHomP => HK HE.
split; first by move => a b; rewrite /= linearB.
split; first by move => a b; rewrite /= HE // subvsP.
by rewrite /= algid1 HK // mem1v.
Qed.

Lemma kHom_horner K E f p x : f \in kHom K E ->
  p \is a polyOver E -> x \in E -> f p.[x] = (map_poly f p).[f x].
Proof.
move => Hf /polyOver_subvs [{p}p -> Ex]; rewrite (horner_map _ _ (Subvs Ex)).
rewrite -[f _](horner_map (RMorphism (kHomRmorph_subproof Hf))).
by rewrite map_poly_comp.
Qed.

Lemma kHom_root K E f p x : f \in kHom K E -> 
  p \is a polyOver E -> x \in E -> root p x -> root (map_poly f p) (f x).
Proof.
by move=> Hf Ep Ex /rootP px0; rewrite /root -(kHom_horner Hf) // px0 linear0.
Qed.

Lemma kHom_rootK K E f p x : (K <= E)%VS -> f \in kHom K E ->
  p \is a polyOver K -> x \in E -> root p x -> root p (f x).
Proof.
move=> HKE Hf Kp Ex /(kHom_root Hf); rewrite (kHomFixedPoly Hf) //.
by apply; rewrite ?(polyOverSv HKE).
Qed.

Variables (K E : {subfield L}) (f : 'End(L)) (x y : L).
Hypothesis HKE :  (K <= E)%VS.
Hypothesis Hf : f \in kHom K E.
Hypothesis Hy : root (map_poly f (minPoly E x)) y.

Lemma kHomExtendExt z : z \in E -> kHomExtend E f x y z = f z.
Proof. move => Hz. by rewrite kHomExtendE poly_for_K // map_polyC hornerC. Qed.

Lemma kHomExtend_poly p :
  p \in polyOver E -> kHomExtend E f x y (p.[x]) = (map_poly f p).[y].
Proof.
move => Hp.
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
by rewrite (map_modp (RMorphism (kHomRmorph_subproof Hf))) !map_polyE /=.
Qed.

Lemma kHomExtendkHom : kHomExtend E f x y \is a kHom K <<E; x>>%AS .
Proof.
case/kHomP: Hf => HK HE.
move/subvP: HKE => HKE'.
apply/kHomP; split.
  move => z Hz.
  rewrite /= kHomExtendE.
  move/HKE'/poly_for_K: (Hz) ->.
  by rewrite map_polyC hornerC /= HK.
move => a b.
case/poly_Fadjoin => p Hp ->.
case/poly_Fadjoin => q Hq ->.
rewrite -hornerM !kHomExtend_poly ?rpredM // -hornerM.
congr (_.[_]).
apply/polyP => i.
rewrite coef_map !coefM /= linear_sum.
apply: eq_bigr => j _.
by rewrite !coef_map /= HE ?(polyOverP _).
Qed.

End kHomExtend.

Lemma kAutE K E f : f \is a kAut K E = (f \is a kHom K E) && (f @: E <= E)%VS.
Proof.
apply/andP/andP; case => Hhom; first by move/eqP->.
move => HfE; split => //.
by rewrite -(dimv_leqif_eq HfE) (kHom_dim Hhom).
Qed.

Lemma kAutS Ka Kb E f : (Ka <= Kb)%VS -> f \in kAut Kb E -> f \in kAut Ka E.
Proof.
move => HK.
case/andP => HKb HE.
apply/andP.
by rewrite (kHomSl _ HKb).
Qed.

Lemma kHom_kAut_sub K E : {subset kAut K E <= kHom K E}.
Proof. by move => f /andP []. Qed.

Lemma kAut_eq K E (f g : 'End(L)) : (K <= E)%VS -> {in E, f =1 g} ->
  (f \is a kAut K E) = (g \is a kAut K E).
Proof.
move => HKE Hfg.
rewrite !kAutE (kHom_eq HKE Hfg).
case:(g \is a kHom K E) => /=; last done.
wlog suff: f g Hfg / (f @: E <= E -> g @:E <= E)%VS.
  move => H.
  apply/idP/idP; first by apply: H.
  by apply: H => ? ?; symmetry; apply Hfg.
move/subvP => HfE.
apply/subvP => ? /memv_imgP [a Ha ->].
rewrite -Hfg //.
apply: HfE.
by apply: memv_img.
Qed.

Lemma kHomL_kAutL K : kHom K {:L} =i kAut K {:L}.
Proof.
move => f.
apply: (sameP idP); apply: (iffP idP); first by apply: kHom_kAut_sub.
by move => Hf; rewrite kAutE Hf subvf.
Qed.

Lemma fAutL_lrmorph (f : 'End(L)) :
  reflect (lrmorphism f) (f \is a kHom F {:L}).
Proof.
apply: (iffP (kHomP _ _ _)).
  case => HF HL.
  apply/is_ahomP/is_ahom_inP.
  split; first by apply: HL.
  by apply: HF; rewrite mem1v.
move => Hf.
split; last by move => x y _ _; apply: (rmorphM (RMorphism Hf)).
move => ?; case/vlineP => k ->.
rewrite linearZ /=.
by rewrite [f 1](rmorph1 (RMorphism Hf)).
Qed.

Lemma fAutL_is_kHom (f : 'AEnd(L)) : val f \is a kHom F {:L}.
Proof. by apply/fAutL_lrmorph; apply: lrmorphismP. Qed.

Lemma kAutL_lker0 K f : f \is a kHom K {:L} -> lker f == 0%VS.
Proof.
move/(kHomSl (sub1v _))/fAutL_lrmorph=> fM.
by apply/lker0P; exact: (fmorph_inj (RMorphism fM)).
Qed.

Fact fAutL_img_is_aspace (f : 'AEnd(L)) (K : {subfield L}) :
   let Kf := (f @: K)%VS in
   has_algid Kf && (Kf * Kf <= Kf)%VS.
Proof.
apply/andP; split.
  apply has_algid1.
  by rewrite -(rmorph1 [rmorphism of (val f)]) memv_img // mem1v.
apply/prodvP => _ _ /memv_imgP [a Ha ->] /memv_imgP [b Hb ->].
by rewrite -rmorphM memv_img // memv_mul.
Qed.
Canonical Structure fAutL_img_aspace a Z : {subfield L} := Eval hnf in
  ASpace (fAutL_img_is_aspace a Z).

Lemma inv_kAutL K f : f \is a kHom K {:L} -> f^-1%VF \is a kHom K {:L}.
Proof.
move=> homFf; have [/kHomP[fKid fM] kerf0] := (homFf, kAutL_lker0 homFf).
have f1K: cancel f^-1%VF f by exact: lker0_lfunVK.
apply/kHomP; split=> [x Kx | x y _ _]; apply: (lker0P kerf0).
  by rewrite f1K fKid.
by rewrite fM ?memvf ?{1}f1K.
Qed.

Lemma inv_fAutL_in (f : 'AEnd(L)) : f^-1%VF \is ahom_in {:L} .
Proof.
move/is_ahomP/fAutL_lrmorph: (valP f) => Hf.
apply/is_ahomP/fAutL_lrmorph.
by apply: inv_kAutL.
Qed.

Canonical inv_fAutL (f : 'AEnd(L)) : 'AEnd(L) := AHom (inv_fAutL_in f).

Notation "f ^-1" := (inv_fAutL f) : lrfun_scope.

Lemma unit_fAutL (f : 'AEnd(L)) : val f \is a GRing.unit.
Proof.
rewrite qualifE; apply: (kAutL_lker0 (K:=F)); apply: fAutL_is_kHom.
Qed.

Lemma comp_kHom K E f g : f \is a kHom K fullv -> g \is a kHom K E ->
  (f \o g)%VF \is a kHom K E.
Proof.
move=> /kHomP[fKid fM] /kHomP[gKid gM]; apply/kHomP; split=> [x Kx | x y Ex Ey].
  by rewrite lfunE /= gKid ?fKid.
by rewrite !lfunE /= gM // fM ?memvf.
Qed.

Lemma kHom_extends K E f p U :
    (K <= E)%VS -> f \is a kHom K E ->
    p \is a polyOver K -> splittingFieldFor E p U ->
  {g | g \is a kHom K U & {in E, f =1 g}}.
Proof.
move=> sKE homEf Kp /sig2_eqW[rs Dp <-{U}]; set r := rs.
have rs_r: all (mem rs) r by exact/allP.
elim: r rs_r => [_|z r IHr /=/andP[rs_z rs_r]] /= in E f sKE homEf *.
  by exists f; rewrite ?Fadjoin_nil.
set Ez := <<E; z>>%AS; pose fpEz := map_poly f (minPoly E z).
suffices{IHr} /sigW[y fpEz_y]: exists y, root fpEz y.
  have homEz_fz: kHomExtend E f z y \is a kHom K Ez by exact: kHomExtendkHom.
  have sKEz: (K <= Ez)%VS := subv_trans sKE (subv_adjoin E z).
  have [g homGg Dg] := IHr rs_r _ _ sKEz homEz_fz.
  exists g => [|x Ex]; first by rewrite adjoin_cons.
  by rewrite -Dg ?memv_mem_adjoin // kHomExtendExt.
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

Lemma enum_kAutL K p :
    p \is a polyOver K -> splittingFieldFor K p {:L} ->
  {homK : (\dim_K {:L}).-tuple 'AEnd(L) | separablePolynomial p -> uniq homK
        & forall f : 'AEnd(L), (val f \is a kHom K {:L}) = (f \in homK)}.
Proof.
move=> Kp /sig2_eqW[rs Dp]; set r := rs; set E := K => defL.
have [sKE rs_r]: (K <= E)%VS /\ all (mem rs) r by split=> //; exact/allP.
elim: r rs_r => [_|z r IHr /=/andP[rs_z rs_r]] /= in (E) sKE defL *.
  rewrite Fadjoin_nil in defL.
  rewrite defL divnn ?adim_gt0 //; exists [tuple \1%AF] => // f.
  rewrite inE; apply/idP/eqP => [/kHomP[f1 _] | ->]; last exact: kHom1.
  by apply/val_inj/lfunP=> x; rewrite id_lfunE f1 ?memvf.
have [Ez | E'z] := boolP (z \in E).
  rewrite memv_adjoin_eq in Ez.
  apply: IHr => //; rewrite -(eqP Ez).
  by rewrite -adjoin_cons.
set Ez := <<E; z>>%AS in defL; pose pEz := minPoly E z.
have sEEz: (E <= Ez)%VS := subv_adjoin E z; have sKEz := subv_trans sKE sEEz.
rewrite adjoin_cons in defL.
have{IHr} [homEz UhomEz DhomEz] := IHr rs_r _ sKEz defL.
have Ep: p \in polyOver E := polyOverSv sKE Kp.
have [m DpEz]: {m | pEz %= \prod_(w <- mask m rs) ('X - w%:P)}.
  apply: dvdp_prod_XsubC; rewrite -(eqp_dvdr _ Dp).
  rewrite minPoly_dvdp ?(polyOverSv sKE) //.
  by rewrite (eqp_root Dp) root_prod_XsubC.
set rz := mask m rs in Dp; pose n := \dim_E Ez.
have sz_rz: size rz == n.
  rewrite /n -elementDegreeE -eqSS.
  by rewrite -size_minPoly -(size_prod_XsubC _ id) -(eqp_size DpEz).
have fEz i (y := tnth (Tuple sz_rz) i) :
    {f : 'AEnd(L) | val f \is a kHom E fullv & f z = y}.
  have homEfz: kHomExtend E \1%VF z y \in kHom E Ez.
    rewrite kHomExtendkHom ?kHom1 // map_poly_id => [|u]; last by rewrite lfunE.
    by rewrite (eqp_root DpEz) -/rz root_prod_XsubC mem_tnth.
  have splitFp: splittingFieldFor Ez p fullv.
    exists rs => //; apply/eqP; rewrite eqEsubv subvf -defL adjoin_seqSr //.
    exact/allP.
  have [f homLf Df] := kHom_extends sEEz homEfz Ep splitFp.
  case/andP: (homLf) => _ ahomf.
  exists (AHom ahomf) => //.
  by rewrite -Df ?memv_adjoin ?(kHomExtendX _ (kHom1 E E)).
pose mkHom ij := let: (i, j) := ij in (s2val (fEz i) \o tnth homEz j)%AF.
have mkHom_z i j: mkHom (i, j) z = rz`_i.
  have /kHomP[fj_id _]: val (tnth homEz j) \is a kHom Ez {:L}.
    by rewrite DhomEz mem_tnth.
  rewrite /= lfunE /= fj_id ?memv_adjoin //.
  by case: (fEz i) => _ /= _ ->; rewrite (tnth_nth 0).
have ->: \dim_E {:L} = #|{: 'I_n * 'I_(\dim_Ez {:L})}|.
  rewrite card_prod mulnC !card_ord muln_divA ?field_dimS ?subsetKFadjoin //.
  by rewrite -dim_sup_field ?subvf.
exists [tuple of codom mkHom] => [sepP | f].
  apply/injectiveP => /= [[i1 j1]] [i2 j2] /= /(f_equal val)/lfunP Eij12.
  have /eqP Ei12: i1 == i2.
    have /eqP := Eij12 z; rewrite !mkHom_z nth_uniq ?(eqP sz_rz) //.
    by rewrite mask_uniq // -separable_prod_XsubC -(eqp_separable Dp).
  rewrite -Ei12 in Eij12 *; congr (_, _); apply/val_inj/eqP.
  case: (fEz i1) Eij12 => f /= /(kHomSl (sub1v _))/fAutL_lrmorph fM _ Ej12.
  rewrite -(nth_uniq \1%AF _ _ (UhomEz sepP)) ?size_tuple // -!tnth_nth.
  apply/eqP/val_inj/lfunP=> u; apply: (fmorph_inj (RMorphism fM)) => /=.
  by have:= Ej12 u; rewrite !lfunE.
apply/idP/imageP=> [homLf | [[i j] _ ->] /=]; last first.
  case: (fEz i) => fi /= /comp_kHom->; rewrite ?(kHomSl sEEz) //.
  by rewrite DhomEz mem_tnth.
have /tnthP[i Dfz]: f z \in Tuple sz_rz.
  rewrite memtE /= -root_prod_XsubC -(eqp_root DpEz).
  by rewrite (kHom_rootK _ homLf) ?memvf ?subvf ?minPolyOver ?root_minPoly.
case Dfi: (fEz i) => [fi homLfi fi_z]; have kerfi0 := kAutL_lker0 homLfi.
set fj := (fi ^-1 \o f)%AF; suffices /tnthP[j Dfj]: fj \in homEz.
  by exists (i, j) => //=; apply/val_inj; rewrite {}Dfi /= -Dfj lker0_compVKf.
rewrite -DhomEz; apply/kHomP.
have homLfj: val fj \is a kHom E fullv := comp_kHom (inv_kAutL homLfi) homLf.
split=> [_ /poly_Fadjoin[q Eq ->]|]; last by case/kHomP: homLfj.
have /fAutL_lrmorph fjM := kHomSl (sub1v _) homLfj.
rewrite -[fj _](horner_map (RMorphism fjM)) (kHomFixedPoly homLfj) //.
by rewrite /= lfunE /= Dfz -fi_z lker0_lfunK.
Qed.

End kHom.

Module SplittingField.

Import GRing.

Section ClassDef.

Variable F : fieldType.

Definition axiom (L : fieldExtType F) :=
  exists2 p : {poly L}, p \is a polyOver 1%VS & splittingFieldFor 1%VS p {:L}.

Record class_of (L : Type) : Type :=
  Class {base : FieldExt.class_of F L; _ : axiom (FieldExt.Pack _ base L)}.
Local Coercion base : class_of >-> FieldExt.class_of.

Structure type (phF : phant F) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (phF : phant F) (T : Type) (cT : type phF).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition clone c of phant_id class c := @Pack phF T c T.

Definition pack b0 (ax0 : axiom (@FieldExt.Pack F (Phant F) T b0 T)) :=
 fun bT b & phant_id (@FieldExt.class F phF bT) b =>
 fun   ax & phant_id ax0 ax => Pack (Phant F) (@Class T b ax) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @Ring.Pack cT xclass xT.
Definition unitRingType := @UnitRing.Pack cT xclass xT.
Definition comRingType := @ComRing.Pack cT xclass xT.
Definition comUnitRingType := @ComUnitRing.Pack cT xclass xT.
Definition idomainType := @IntegralDomain.Pack cT xclass xT.
Definition fieldType := @Field.Pack cT xclass xT.
Definition lmodType := @Lmodule.Pack F phF cT xclass xT.
Definition lalgType := @Lalgebra.Pack F phF cT xclass xT.
Definition algType := @Algebra.Pack F phF cT xclass xT.
Definition unitAlgType := @UnitAlgebra.Pack F phF cT xclass xT.
Definition vectType := @Vector.Pack F phF cT xclass xT.
Definition FalgType := @Falgebra.Pack F phF cT xclass xT.
Definition fieldExtType := @FieldExt.Pack F phF cT xclass xT.

End ClassDef.

Module Exports.

Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion base : class_of >-> FieldExt.class_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Coercion comUnitRingType : type >-> ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> IntegralDomain.type.
Canonical idomainType.
Coercion fieldType : type >-> Field.type.
Canonical fieldType.
Coercion lmodType : type >-> Lmodule.type.
Canonical lmodType.
Coercion lalgType : type >-> Lalgebra.type.
Canonical lalgType.
Coercion algType : type >-> Algebra.type.
Canonical algType.
Coercion unitAlgType : type >-> UnitAlgebra.type.
Canonical unitAlgType.
Coercion vectType : type >-> Vector.type.
Canonical vectType.
Coercion FalgType : type >-> Falgebra.type.
Canonical FalgType.
Coercion fieldExtType : type >-> FieldExt.type.
Canonical fieldExtType.

Notation splittingFieldType F := (type (Phant F)).
Notation SplittingFieldType F L ax := (@pack _ (Phant F) L _ ax _ _ id _ id).
Notation "[ 'splittingFieldType' F 'of' L 'for' K ]" :=
  (@clone _ (Phant F) L K _ idfun)
  (at level 0, format "[ 'splittingFieldType'  F  'of'  L  'for'  K ]")
  : form_scope.
Notation "[ 'splittingFieldType' F 'of' L ]" :=
  (@clone _ (Phant F) L _ _ idfun)
  (at level 0, format "[ 'splittingFieldType'  F  'of'  L ]") : form_scope.

End Exports.
End SplittingField.
Export SplittingField.Exports.

Lemma normal_field_splitting (F : fieldType) (L : fieldExtType F) :
  (forall (K : {subfield L}) x,
    exists r, minPoly K x == \prod_(y <- r) ('X - y%:P)) ->
  SplittingField.axiom L.
Proof.
move => normalL.
pose r i := sval (sigW (normalL 1%AS (tnth (vbasis fullv) i))).
have sz_r i: (size (r i) <= \dim {:L})%N.
  rewrite -ltnS -(size_prod_XsubC _ id) /r; case: (sigW _) => _ /= /eqP <-.
  rewrite size_minPoly ltnS; move: (tnth _ _) => x.
  by rewrite elementDegreeE dimv1 divn1 dimvS // subvf.
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
apply: seqv_sub_adjoin.
by apply/imageP; exists (i, Ordinal (leq_trans lt_j_ri (sz_r i))).
Qed.

Section SplittingFieldTheory.

Variables (F : fieldType) (L : splittingFieldType F).

Implicit Types (K E : {aspace L}).

Lemma splittingFieldP : SplittingField.axiom L.
Proof. by case: L => ? []. Qed.

Lemma splitting_field_normal (K : {subfield L}) x :
  exists r, minPoly K x == \prod_(y <- r) ('X - y%:P).
Proof.
pose q1 := minPoly 1 x.
have [p F0p splitLp] := splittingFieldP.
have [autL _ DautL] := enum_kAutL F0p splitLp.
suffices{K} autL_px q:
  q %| q1 -> size q > 1 -> has (fun f : 'AEnd(L) => root q (f x)) autL.
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
have{irr_q} [Lz [inLz [z qz0]]]: {Lz : fieldExtType F &
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
    by apply/Fadjoin_seqP; rewrite sub1v; split=> // _ /mapP[y r_y ->].
  rewrite /= -{def_p}defL.
  elim/last_ind: r => [|r y IHr] /=; first by rewrite !Fadjoin_nil imL1.
  rewrite map_rcons !adjoin_rcons /=.
  apply/subvP=> _ /memv_imgP[_ /poly_Fadjoin[p1 r_p1 ->] ->].
  rewrite lfunE -horner_map /= mempx_Fadjoin //=; apply/polyOverP=> i.
  by rewrite coef_map (subvP IHr) //= -lfunE memv_img ?(polyOverP r_p1).
have [f homLf fxz]: exists2 f : 'End(Lz), f \is a kHom 1 imL & f (inLz x) = z.
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
  have{map1q1z_z} hom_f0 : f0 \is a kHom 1 <<1; (inLz x)>>%AS.
    by apply: kHomExtendkHom map1q1z_z => //; apply: kHom1.
  have{splitLpz} splitLpz: splittingFieldFor <<1; inLz x>>%AS pz imL.
    have [r def_pz defLz] := splitLpz; exists r => //.
    apply/eqP; rewrite eqEsubv -{2}defLz adjoin_seqSl ?sub1v // andbT.
    apply/Fadjoin_seqP; split; last by rewrite -defLz; apply: seqv_sub_adjoin.
    by apply/FadjoinP/andP; rewrite sub1v -lfunE memv_img ?memvf.
  have [f homLzf Df] := kHom_extends (sub1v _) hom_f0 F0pz splitLpz.
  have [-> | x'z] := eqVneq (inLz x) z.
    by exists \1%VF; rewrite ?lfunE ?kHom1.
  exists f => //; rewrite -Df ?memv_adjoin ?(kHomExtendX _ (kHom1 1 1)) //.
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
    by rewrite Fadjoin_nil; move=> _ F0u; rewrite f1id // (subvP (sub1v _)).
  rewrite all_rcons adjoin_rcons => /andP[rr1 ry] /poly_Fadjoin[pu r1pu ->].
  rewrite (kHom_horner homLf) -defLz; last exact: seqv_sub_adjoin; last first.
    by apply: polyOverS r1pu; apply/subvP/adjoin_seqSr/allP.
  apply: rpred_horner.
    by apply/polyOverP=> i; rewrite coef_map /= defLz IHr1 ?(polyOverP r1pu).
  rewrite seqv_sub_adjoin // -root_prod_XsubC -(eqp_root def_pz).
  rewrite (kHom_rootK _ homLf) ?sub1v //.
    by rewrite -defLz seqv_sub_adjoin.
  by rewrite (eqp_root def_pz) root_prod_XsubC.
suff f1_is_ahom : f1 \is ahom_in fullv.
  apply/hasP; exists (AHom f1_is_ahom); last first.
    by rewrite -(fmorph_root inLz) /= Df1 fxz.
  rewrite -DautL; apply/kHomP; split; last first.
    by move => ? ?; cbv beta; rewrite rmorphM.
  by move => _ /vlineP[a ->]; rewrite linearZ rmorph1.
apply/is_ahom_inP; split.
  move => a b _ _.
  by apply: (fmorph_inj inLz); rewrite rmorphM /= !Df1 rmorphM fM ?imLin.
apply: (fmorph_inj inLz).
by rewrite /= Df1 /= f1id ?rmorph1 ?mem1v.
Qed.

Lemma splittingPoly : { p : {poly L} | 
  p \is a polyOver 1%VS & splittingFieldFor 1%VS p {:L}}.
Proof.
have H : exists prs : {poly L}*(seq L), 
  [&& prs.1 \is a polyOver 1%VS
  , prs.1 %= \prod_(z <- prs.2) ('X - z%:P)
  & <<1 & prs.2>>%AS == fullv].
  have [p F0p [rs splitLp gen]] := splittingFieldP.
  by exists (p,rs); rewrite F0p splitLp gen eqxx.
case/and3P: (xchooseP H) => [HP1 HP2 HP3].
exists (xchoose H).1; first done.
exists (xchoose H).2; first done.
by apply/eqP.
Qed.

End SplittingFieldTheory.

Section Galois.

Variables (F0 : fieldType) (L : splittingFieldType F0).

Let F : {subfield L} := aspace1 _.

Implicit Types (U V W : {vspace L}).
Implicit Types (K M E : {subfield L}).

Lemma fAutL_lker0 (f : 'AEnd(L)) : lker f == 0%VS.
Proof. by move: (fAutL_is_kHom f); apply: kAutL_lker0. Qed.

Lemma enum_fAutL :
  {fAutL : (\dim {:L}).-tuple 'AEnd(L) | forall f, (f \in fAutL)}.
Proof.
have [p Hp Hsfp] := (splittingPoly L).
move: (enum_kAutL Hp Hsfp).
rewrite dimv1 divn1; move => [fAutL _ HfAutL].
exists fAutL => f.
by rewrite -HfAutL fAutL_is_kHom.
Qed.

Lemma index_fAutL f : index f (sval enum_fAutL) < \dim {:L}.
Proof.
elim: enum_fAutL => s Hs /=.
move: (Hs f).
by rewrite -index_mem size_tuple.
Qed.

Lemma cancel_fAutL_ord : 
  cancel (fun f => Ordinal (index_fAutL f)) (tnth (sval enum_fAutL)).
Proof.
move => [f Hf].
rewrite /tnth /= nth_index //.
apply/(svalP enum_fAutL).
Qed.

Definition fAutL_countMixin := Eval hnf in CanCountMixin cancel_fAutL_ord.
Canonical fAutL_countType := Eval hnf in CountType 'AEnd(L) fAutL_countMixin.
Canonical fAutL_subCountType := Eval hnf in [subCountType of 'AEnd(L)].
Definition fAutL_finMixin := Eval hnf in CanFinMixin cancel_fAutL_ord.
Canonical fAutL_finType := Eval hnf in FinType 'AEnd(L) fAutL_finMixin.
Canonical fAutL_subFinType := Eval hnf in [subFinType of 'AEnd(L)].

(* the group operation is the categorical composition operation *)
Definition comp_fAutL (f g : 'AEnd(L)) : 'AEnd(L) := (g \o f)%AF.

Lemma comp_fAutLA : associative comp_fAutL.
Proof. by move => f g h; apply: val_inj; symmetry; apply: comp_lfunA. Qed.

Lemma comp_fAutL1l : left_id \1%AF comp_fAutL.
Proof. by move=> f; apply/val_inj/comp_lfun1r. Qed.

Lemma comp_fAutLK : left_inverse \1%AF (@inv_fAutL _ L) (fun f g => g \o f)%AF.
Proof.
move=> f; apply/val_inj => /=.
rewrite lker0_compfV ?(kAutL_lker0 (K:=1%AS)) //.
by apply: fAutL_is_kHom.
Qed.

Definition fAutL_baseFinGroupMixin := FinGroup.Mixin (T:='AEnd(L))
   comp_fAutLA comp_fAutL1l comp_fAutLK.

Canonical fAutL_baseFinGroupType := Eval hnf in 
   BaseFinGroupType 'AEnd(L) fAutL_baseFinGroupMixin.
Canonical fAutL_finGroupType := Eval hnf in
   @FinGroupType fAutL_baseFinGroupType comp_fAutLK.

Lemma kHom_extend_fAutL K E f : f \is a kHom K E ->
  exists g : 'AEnd(L), {in E, f =1 val g}.
Proof.
move/(kHomSl (capvSl K E)) => Hf.
have [p Hp Hsfp] := (splittingPoly L).
move/(polyOverSv (mem1v [aspace of K :&: E])): Hp => Hp.
move/(splittingFieldForS (mem1v E)): Hsfp => Hsfp.
have [g0 Hg Hfg] := kHom_extends (capvSr K E) Hf Hp Hsfp.
suff Hg_aend : g0 \is ahom_in {:L} by exists (AHom Hg_aend).
by apply/is_ahomP/fAutL_lrmorph; apply: (kHomSl _ Hg); apply: mem1v.
Qed.

Definition kAAut U V := [set f : 'AEnd(L) | val f \in kAut U V ].

Definition kAAutL U := kAAut U {:L}.

Lemma kAAut_group_set K E : group_set (kAAut K E).
Proof.
apply/group_setP; split; first by rewrite inE qualifE kHom1 lim1g eqxx.
move => x y.
rewrite !inE !kAutE.
case/andP; case/kHomP => Hx1 Hx2 Hx3.
case/andP; case/kHomP => Hy1 Hy2 Hy3.
apply/andP; split; last first.
  rewrite SubK limg_comp (subv_trans _ Hy3) // limg_ker0 //.
  by apply: fAutL_lker0.
apply/kHomP; split; first by move => a Ha;rewrite SubK lfunE /= Hy1 // Hx1.
by move => ? ? _ _; rewrite /= rmorphM.
Qed.

Canonical kAAut_group K E := Eval hnf in group (kAAut_group_set K E).

(* ???
Lemma kAAut_normal K E : kAAut F E = 'N(kAAutL E)%g.
*)

Lemma kAAut_normal K E : kAAut K E \subset 'N(kAAutL E)%g.
Proof.
apply/subsetP.
move => x.
rewrite !{1}in_set.
case/andP => _ /eqP Hx.
apply/subsetP => ? /imsetP [y].
rewrite !in_set.
case/andP => /kHomP [Hy _] _ ->.
rewrite -kHomL_kAutL.
apply/kHomP; split; last by move => ? ? _ _; rewrite /= rmorphM.
move => a Ha /=.
rewrite -{2}[a](id_lfunE) -[\1%VF]/(val (1%g : 'AEnd(L))) -(mulVg x).
rewrite !SubK !lfunE /= lfunE [X in ((val x) X) = _]Hy //.
rewrite -Hx in Ha.
case/memv_imgP: Ha => [b Hb ->].
by rewrite -comp_lfunE -[(x^-1 \o x)%VF]/(ahval (x * x^-1)%g) mulgV id_lfunE.
Qed.

Lemma mem_kAut_coset K E (g : 'AEnd(L)) : val g \is a kAut K E -> 
  g \in coset (kAAutL E) g.
Proof.
move => Hg.
rewrite val_coset; first by apply: rcoset_refl.
move/subsetP: (kAAut_normal K E).
apply.
by rewrite inE.
Qed.

Lemma aut_mem_eqP E (x y : coset_of (kAAutL E)) f g : 
  f \in x -> g \in y -> reflect {in E, f =1 g} (x == y).
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
apply/kHomP; split; last by move => ? ? _ _; rewrite /= rmorphM.
move => a Ha.
rewrite /= comp_lfunE /= Hfg //.
by rewrite -comp_lfunE -[(_ \o _)%VF]/(ahval (g * g^-1)%g) mulgV id_lfunE.
Qed.

(* We wrap coset_of (kAAutL V) in a new type in order to create a suitable
   coercion class for f_aut_repr to coerce from. *)
Section f_aut_Definition.

Variable (V : {vspace L}).

Inductive f_aut := FAut of coset_of (kAAutL V).
Definition f_aut_val A := let: FAut x := A in x.

Canonical f_aut_subType := Eval hnf in [newType for f_aut_val by f_aut_rect].
Definition f_aut_eqMixin := Eval hnf in [eqMixin of f_aut by <:].
Canonical f_aut_eqType := Eval hnf in EqType f_aut f_aut_eqMixin.
Definition f_aut_choiceMixin := [choiceMixin of f_aut by <:].
Canonical f_aut_choiceType := Eval hnf in ChoiceType f_aut f_aut_choiceMixin.
Definition f_aut_countMixin := [countMixin of f_aut by <:].
Canonical f_aut_countType := Eval hnf in CountType f_aut f_aut_countMixin.
Canonical f_aut_subCountType := Eval hnf in [subCountType of f_aut].
Definition f_aut_finMixin := [finMixin of f_aut by <:].
Canonical f_aut_finType := Eval hnf in FinType f_aut f_aut_finMixin.
Canonical f_aut_subFinType := Eval hnf in [subFinType of f_aut].

Definition f_aut_one := FAut 1%g.
Definition f_aut_inv u := FAut (f_aut_val u)^-1.
Definition f_aut_mul u v := FAut (f_aut_val u * f_aut_val v).
Lemma f_aut_oneP : left_id f_aut_one f_aut_mul.
Proof. move=> u; apply: val_inj; exact: mul1g. Qed.

Lemma f_aut_invP : left_inverse f_aut_one f_aut_inv f_aut_mul.
Proof. move=> u; apply: val_inj; exact: mulVg. Qed.
Lemma f_aut_mulP : associative f_aut_mul.
Proof. move=> u v w; apply: val_inj; exact: mulgA. Qed.

Definition f_aut_finGroupMixin :=
  FinGroup.Mixin f_aut_mulP f_aut_oneP f_aut_invP.
Canonical f_aut_finBaseGroupType :=
  Eval hnf in BaseFinGroupType f_aut f_aut_finGroupMixin.
Canonical f_aut_finGroupType := Eval hnf in FinGroupType f_aut_invP.

Lemma FAut_is_morph : {in setT &, {morph FAut : x y / (x * y)%g}}.
Proof. done. Qed.
Canonical FAut_morphism := Morphism FAut_is_morph.

Coercion f_aut_repr (x : f_aut) : 'AEnd(L) := repr (val x).

(*
Lemma f_aut_repr_is_ahom x : f_aut_repr x \is ahom_in {:L}.
Proof. by apply/is_ahomP; apply: lrmorphismP. Qed.
Canonical f_aut_repr_ahom x := AHom (f_aut_repr_is_ahom x).
*)

End f_aut_Definition.

Lemma aut_eqP E (x y : f_aut E) : 
  reflect {in E, x =1 y} (x == y).
Proof. by apply: aut_mem_eqP; apply: mem_repr_coset. Qed.

Lemma aut_id E a : (1:f_aut E)%g a = a.
Proof. by rewrite /f_aut_repr repr_coset1 id_lfunE. Qed.

Lemma aut_mul E (x y : f_aut E) :
 {in E, (x * y)%g =1  val (f_aut_repr x) * val (f_aut_repr y)}.
Proof.
apply/(@aut_mem_eqP _ (val (x * y)%g) (val (x * y)%g)); last done.
  by rewrite mem_repr_coset.
rewrite [val _]/=.
rewrite -[in X in _ \in X](coset_mem (mem_repr_coset (val x))).
rewrite -[in X in _ \in X](coset_mem (mem_repr_coset (val y))).
rewrite -coset_morphM ?repr_coset_norm //.
rewrite val_coset; first by apply: rcoset_refl.
by apply: groupM; apply: repr_coset_norm.
Qed.

Lemma aut_inv E (x : f_aut E) : {in E, (x^-1)%g =1 x^-1%VF}.
Proof.
case: x => x /= a Ha.
apply: (canRL (lker0_lfunK _)); first by apply: fAutL_lker0.
by rewrite -comp_lfunE -(aut_mul (FAut x)^-1%g (FAut x)) // mulVg aut_id.
Qed.

Definition aut U V := ((@FAut V) @* (kAAut U V / kAAutL V))%g.

(* Standard mathematical notation for Aut(E/K) puts the larger field first. *)
Notation "''Aut' ( V / U )" := (aut U V).

Section Automorphism.

Definition pickAut U V W f : f_aut W :=
  odflt 1%g
    [pick x \in 'Aut(W / U)
    | (V <= lker (ahval x - f))%VS].

(* Aut is the main "constructor" used for the aut type
   it converts (f: kAut K E) into 'Aut(E / K) *)
Definition Aut U W f := pickAut U W W f.

Variables K E : {subfield L}.

(* with some effort this can probably be generalized to arbitrary vspaces*)
Lemma pickAut_aut V f : pickAut K V E f \in 'Aut(E / K).
Proof.
rewrite /pickAut.
case:pickP; last by rewrite group1.
by move => ? /andP [].
Qed.

Lemma Aut_aut f : Aut K E f \in 'Aut(E / K).
Proof. apply: pickAut_aut. Qed.

Lemma memv_aut x a : x \in 'Aut(E / K) -> a \in E -> x a \in E.
Proof.
rewrite /aut -imset_coset.
case/imsetP => h; rewrite inE => /andP [_ Hh] -> {x} /=.
case/imsetP: Hh => g; rewrite inE => Hg -> Ha {h} /=.
move: (eqxx (coset (kAAutL E) g)).
move/(aut_mem_eqP (mem_repr_coset _) (mem_kAut_coset Hg)) => -> //.
case/andP: Hg => _ /eqP Hg.
by rewrite -[in X in _ \in X]Hg memv_img.
Qed.

Hypothesis HKE : (K <= E)%VS.

Lemma Aut_eq f : f \is a kAut K E -> {in E, Aut K E f =1 f}.
Proof.
move => Hf a Ha.
rewrite /Aut /pickAut.
case:pickP; first by move => x /andP [_ /eqvP Hx]; apply: Hx.
move/pred0P.
apply: contraTeq => _.
apply/existsP.
move: (Hf); rewrite kAutE; case/andP => HfKE HfE.
case: (kHom_extend_fAutL HfKE) => g Hg.
have HgKE : val g \is a kAut K E by rewrite -(kAut_eq HKE Hg).
exists (FAut (coset _ g)); apply/andP; split.
  by rewrite mem_morphim // ?mem_quotient // inE.
apply/eqvP.
move => b Hb /=; rewrite Hg //.
move: b Hb.
by apply/(aut_mem_eqP (mem_repr_coset _) (mem_kAut_coset HgKE)).
Qed.

Lemma aut_kAut x : x \in 'Aut(E / K) = (val (f_aut_repr x) \is a kAut K E).
Proof.
case: x => x /=.
rewrite /aut -imset_coset.
apply/idP/idP.
  case/imsetP => y.
  rewrite inE => /andP [_ Hy] [->].
  case/imsetP: Hy => g; rewrite inE => {y} Hg ->.
  rewrite (kAut_eq (g:=val g) HKE _) //.
  by apply/(aut_mem_eqP (mem_repr_coset _) (mem_kAut_coset Hg)).
move => Hx.
apply: mem_morphim; first by rewrite inE.
apply/imsetP.
exists (repr x); first by rewrite inE.
by rewrite coset_reprK.
Qed.

Lemma aut_repr x : x \in 'Aut(E / K) -> Aut K E x = x.
Proof.
rewrite aut_kAut => Hx.
apply/eqP/(aut_mem_eqP (mem_repr_coset _) (mem_repr_coset _)).
by apply: Aut_eq.
Qed.

Lemma fixed_aut x a : x \in 'Aut(E / K) -> a \in K -> x a = a.
Proof.
rewrite aut_kAut.
case/andP => /kHomP [Hx _] _ Ha.
by rewrite Hx.
Qed.

Lemma fixedPoly_aut x p : x \in 'Aut(E / K) -> p \is a polyOver K ->
  map_poly x p = p.
Proof.
move => Hx /polyOverP Hp.
apply/polyP => i.
by rewrite coef_map /= fixed_aut //.
Qed.

Lemma root_minPoly_aut x a : x \in 'Aut(E / K) -> a \in E ->
  root (minPoly K a) (x a).
Proof.
move => Hx Ha.
rewrite -[minPoly K a](fixedPoly_aut Hx) ?minPolyOver //.
rewrite aut_kAut kAutE andbC in Hx.
case/andP: Hx => _.
move/kHom_root; apply => //; last by apply: root_minPoly.
move/subvP: HKE.
move/polyOverS; apply.
by apply: minPolyOver.
Qed.

End Automorphism.

Lemma aut_eq_Fadjoin K a x y :
  x \in 'Aut(<<K; a>>%AS / K) -> y \in 'Aut(<<K; a>>%AS / K) ->
  (x == y) = (x a == y a).
Proof.
move => Hx Hy.
apply/eqP/eqP; first by move ->.
move => Ha.
apply/eqP/aut_eqP => _ /poly_Fadjoin [p Hp ->].
by rewrite -!horner_map !(fixedPoly_aut (subv_adjoin K a)) //= Ha.
Qed.

Lemma autS K M E : (K <= M <= E)%VS -> 
  ('Aut(E / M) \subset 'Aut(E / K)).
Proof.
case/andP => HKM HME.
apply/subsetP => x.
rewrite !aut_kAut //; last by apply:(subv_trans (y:=M)).
by move/(kAutS HKM).
Qed.

Lemma Aut_conjg K E x : (K <= E)%VS -> x \in 'Aut(E / F) ->
  ('Aut(E / K) :^ x)%g = 'Aut(E / (x @: K)%VS).
Proof.
move => HKE Hx.
apply/eqP.
have HxKE : (x @: K <= E)%VS.
  apply/subvP => _ /memv_imgP [a Ha ->].
  apply: (memv_aut Hx).
  by move/subvP: HKE; apply.
wlog suff Hsuff : x K HKE Hx HxKE / 
  (('Aut(E / K) :^ x)%g \subset ('Aut(E / (x @: K)%VS))).
  rewrite eqEsubset Hsuff // -sub_conjgV -[X in _ \subset ('Aut(E / X))]lim1g.
  rewrite -[\1%VF]/((1:'AEnd(L))%g:'End(L)) -(mulgV (f_aut_repr x)) limg_comp.
  suff: {in (x @: K)%VS, (x^-1)%g =1 x^-1%VF}.
    move/limg_eq <-.
    apply: Hsuff; first done.
    - by rewrite groupV.
    - rewrite -limg_comp.
      move/eqvP/(subv_trans HKE)/eqvP/limg_eq: (aut_mul x (x^-1)%g) <-.
      by rewrite mulgV /f_aut_repr repr_coset1 lim1g.
  move => z Hz; apply: aut_inv.
  by move/subvP: HxKE; apply.
apply/subsetP => y.
rewrite mem_conjg !aut_kAut //=.
have /(kAut_eq HKE) -> : {in E, (y ^ (x^-1))%g =1 (x^-1%g \o y \o x)%AF}.
  rewrite conjgE invgK => z Hz.
  have Hxz : x z \in E by apply: (memv_aut Hx).
  by rewrite !(aut_mul,comp_lfunE) //.
rewrite !kAutE.
case/andP => HyKE.
rewrite !limg_comp.
move: (groupVr Hx).
rewrite aut_kAut; last by apply: sub1v.
case/andP => _ /eqP HxE.
rewrite -[X in (_ <= X)%VS]HxE {HxE} limg_ker0; last by apply: fAutL_lker0.
move: Hx.
rewrite aut_kAut; last by apply: sub1v.
case/andP => Hx /eqP HxE.
rewrite HxE => HyE.
rewrite HyE andbT.
apply/kHomP; split; last by move => ? ? _ _; rewrite /= rmorphM.
move => _ /memv_imgP [a Ha ->].
case/kHomP: HyKE => /(_ _ Ha) HyVa _.
rewrite -[in X in _ = X]HyVa !comp_lfunE /= -[X in _ = X]comp_lfunE.
rewrite -(aut_mul (x^-1)%g x) ?mulVg ?aut_id ?id_lfunE //.
move/subvP: HyE; apply.
rewrite memv_img // -[in X in _ \in X]HxE memv_img //.
by move/subvP: HKE; apply.
Qed.

Definition fixedField V (s : {set f_aut V}) :=
  (V :&: \bigcap_(x \in s) (fixedSpace x))%VS.

Lemma fixedFieldP E (s : {set f_aut E}) a :
 reflect (a \in E /\ (forall x, x \in s -> x a = a))
         (a \in fixedField s).
Proof.
rewrite /fixedField.
apply/(iffP memv_capP); case => HaE H; (split; first done).
  move => x Hx.
  by move/subv_bigcapP/(_ _ Hx)/fixedSpaceP: H.
apply/subv_bigcapP => i Hi.
by apply/fixedSpaceP; apply: H.
Qed.

Fact fixedField_is_aspace_subproof E (s : {set f_aut E}) :
  let FF := fixedField s in
  (has_algid FF  && (FF * FF <= FF)%VS).
Proof.
rewrite /fixedField -big_filter.
move : (filter _ _) => /= {s} r.
pose f (i: f_aut E) := f_aut_repr i.
have -> : (\bigcap_(i <- r) fixedSpace i
        = \bigcap_(i <- [seq f i | i <- r]) fixedSpace i)%VS by rewrite big_map.
move : {r f} (map _ r) => r.
elim : r E => [|r rs IH] E; first by rewrite big_nil capvf; case: E.
rewrite big_cons capvA.
by apply: IH.
Qed.
Canonical fixedField_aspace (E : {subfield L})
   (s : {set f_aut E}) : {subfield L}
   := ASpace (fixedField_is_aspace_subproof s).

Lemma fixedField_bound E (s : {set f_aut E}) : (fixedField s <= E)%VS.
Proof. by apply: capvSl. Qed.

Lemma fixedFieldS E (s1 s2 : {set f_aut E}) :
   (s1 \subset s2) -> (fixedField s2 <= fixedField s1)%VS.
Proof.
move => /subsetP Hs.
apply/subvP => a /fixedFieldP [HaE Ha].
apply/fixedFieldP; split; first done.
move => x Hx.
by rewrite Ha // Hs.
Qed.

Lemma galoisConnectionA K E : (K <= E)%VS -> (K <= fixedField ('Aut(E / K)))%VS.
Proof.
move => HKE.
apply/subvP => a HaK.
apply/fixedFieldP; split; first by move/subvP: HKE; apply.
move => x Hx.
by apply: (fixed_aut HKE).
Qed.

Lemma galoisConnectionB M E (s : {set f_aut E}):
 s \subset 'Aut(E / M) -> s \subset 'Aut(E / fixedField s).
Proof.
move => /subsetP HsEK.
apply/subsetP => x Hxs.
have HxEK := HsEK _ Hxs.
rewrite aut_kAut ?capvSl // kAutE.
apply/andP; split; last first.
  by apply/subvP => _ /memv_imgP [v Hv ->]; apply: (memv_aut HxEK).
apply/kHomP; split; last by move => ? ? _ _; rewrite /= rmorphM.
by move => a /fixedFieldP [_]; apply.
Qed.

Lemma galoisConnection M K E (s : {set f_aut E}):
  (K <= E)%VS -> s \subset 'Aut(E / M) ->
  s \subset 'Aut(E / K) = (K <= fixedField s)%VS.
Proof.
move => HKE HsEK.
apply/idP/idP.
  by move/fixedFieldS; apply: subv_trans; apply galoisConnectionA.
move => HKs.
have : (K <= fixedField s <= E)%VS by rewrite HKs capvSl.
by move/autS; apply: subset_trans; apply: (galoisConnectionB HsEK).
Qed.

Definition galoisTrace U V a := \sum_(i | i \in ('Aut(V / U))) (i a).

Definition galoisNorm U V a := \prod_(i | i \in ('Aut(V / U))) (i a).

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
 (K <= E)%VS -> a \in E -> galoisTrace K E a \in fixedField 'Aut(E / K).
Proof.
move => HKE Ha.
apply/fixedFieldP.
split.
  apply: memv_suml => i.
  rewrite (aut_kAut HKE).
  case/andP => _ /eqP HE.
  by rewrite -[in X in _ \in X]HE memv_img.
move => x Hx.
rewrite rmorph_sum /galoisTrace -{2}['Aut(E / K)](rcoset_id Hx).
rewrite (reindex_inj (mulIg (x^-1)%g)).
symmetry.
apply: eq_big => i; first by rewrite /= mem_rcoset.
by rewrite /= -comp_lfunE -aut_mul // mulgKV.
Qed.

Lemma traceAut a x : a \in E -> x \in 'Aut(E / K) -> 
  galoisTrace K E (x a) = galoisTrace K E a.
Proof.
move => Ha Hx.
rewrite /galoisTrace -{2}['Aut(E / K)](lcoset_id Hx).
rewrite (reindex_inj (mulgI (x^-1)%g)).
apply: eq_big => i;first by rewrite /= mem_lcoset.
by rewrite -comp_lfunE -aut_mul // mulKVg.
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
 (K <= E)%VS -> a \in E -> galoisNorm K E a \in fixedField 'Aut(E / K).
Proof.
move => HKE Ha.
apply/fixedFieldP.
split.
  apply: rpred_prod => i.
  rewrite (aut_kAut HKE).
  case/andP => _ /eqP HE /=.
  by rewrite -[in X in _ \in X]HE memv_img.
move => x Hx.
rewrite rmorph_prod /galoisNorm -{2}['Aut(E / K)](rcoset_id Hx).
rewrite (reindex_inj (mulIg (x^-1)%g)).
symmetry.
apply: eq_big => i; first by rewrite /= mem_rcoset.
by rewrite /= -comp_lfunE -(aut_mul (i * x^-1)%g) // mulgKV.
Qed.

Lemma normAut a x : a \in E -> x \in 'Aut(E / K) -> 
  galoisNorm K E (x a) = galoisNorm K E a.
Proof.
move => Ha Hx.
rewrite /galoisNorm -{2}['Aut(E / K)](lcoset_id Hx).
rewrite (reindex_inj (mulgI (x^-1)%g)).
apply: eq_big => i;first by rewrite /= mem_lcoset.
by rewrite -comp_lfunE -aut_mul // mulKVg.
Qed.

End TraceAndNorm.

Definition normalField U V := forallb x, (x \in kAAutL U) ==> (x @: V == V)%VS.

Lemma normalFieldP K E :
 reflect (forall a, a \in E -> exists2 r, all (fun y => y \in E) r
                                 & minPoly K a = \prod_(b <- r) ('X - b%:P))
         (normalField K E).
Proof.
apply: (iffP forallP); last first.
  move => Hnorm x.
  apply/implyP.
  rewrite inE kAutE.
  case/andP => Hx _.
  suff: val x \is a kAut K E by case/andP.
  rewrite kAutE (kHomSr (subvf E)) //=.
  apply/subvP => a.
  case/memv_imgP => {a} a Ha ->.
  case: (Hnorm _ Ha) => r.
  move/allP => Hr Har.
  apply: Hr.
  rewrite -root_prod_XsubC.
  move/(f_equal (map_poly (fun_of_lfun x))): (Har).
  rewrite (kHomFixedPoly Hx) ?minPolyOver //= Har => ->.
  by rewrite rmorph_root // -Har root_minPoly.
move => Hnorm a HaE.
case: (splitting_field_normal K a) => r.
move/eqP => Hr.
exists r => //.
apply/allP => b.
have [Ka | K'a] := boolP (a \in K).
  move: Ka (size_prod_XsubC r id) (root_minPoly K a).
  rewrite -Hr size_minPoly elemDeg1 => /eqP ->.
  case: r Hr => [|c]; first done; case; last done.
  rewrite big_seq1 => -> _.
  rewrite root_XsubC.
  move/eqP <-.
  rewrite mem_seq1.
  by move/eqP ->.
rewrite -root_prod_XsubC -Hr => Hroot.
set y := kHomExtend K \1%VF a b.
have Hy : y \is a kHom K <<K; a>>%AS.
  apply: kHomExtendkHom.
  - by apply subv_refl.
  - by apply kHom1.
  - by rewrite map_poly_id // => ? ?; rewrite id_lfunE.
case: (kHom_extend_fAutL Hy) => g Hg.
have <- : g a = b by rewrite -Hg ?memv_adjoin // (kHomExtendX _ (kHom1 K _)).
have HgK : (g \in kAAutL K).
  rewrite inE kAutE subvf andbT.
  apply/kHomP; split; last by move => ? ? _ _; rewrite /= rmorphM.
  move/subvP: (subv_adjoin K a) => HKa x Hx /=; rewrite -Hg; last first.
    by apply: HKa.
  by move/kHomP: Hy => [Hy _]; apply Hy.
move/implyP/(_ HgK)/eqP: (Hnorm g) <-.
by apply: memv_img.
Qed.

Lemma normalFieldS K M E : (K <= M)%VS -> normalField K E -> normalField M E.
Proof.
move => HKM /normalFieldP Hnorm.
apply/normalFieldP => a Ha.
have [r /allP Hr Har] := Hnorm _ Ha.
have := minPolyS a HKM.
rewrite Har.
case/dvdp_prod_XsubC => m Hm.
exists (mask m r); first by apply/allP => x Hx; apply: Hr; apply: (mem_mask Hx).
by apply/eqP; rewrite -eqp_monic ?monic_prod_XsubC // monic_minPoly.
Qed.

Lemma splitting_normalField E K p :
  p \is a polyOver K -> splittingFieldFor K p E -> normalField K E.
Proof.
move => HpK [rs Hp HE].
apply/forallP => x.
rewrite inE kAutE.
apply/implyP => /andP [Hx _].
rewrite -dimv_leqif_eq ?limg_dim_eq //.
  have /eqP -> := fAutL_lker0 x.
  by rewrite capv0.
rewrite -HE aimg_adjoin_seq.
case/andP: (Hx) => /fixedSpace_subv -> _.
apply/adjoin_seqSr.
move => _ /mapP [y Hy ->].
move: Hy.
rewrite -!root_prod_XsubC -!(eqp_root Hp).
by apply: (kHom_rootK _ Hx) => //; rewrite ?subvf ?memvf.
Qed.

(* Find a way to merge the proofs of Aut_eq and pickAut_eq *)
Lemma pickAut_eq K M E f : (K <= M)%VS -> (M <= E)%VS ->
 normalField K E -> f \is a kHom K M -> {in M, pickAut K M E f =1 f}.
Proof.
move => HKM HME /forallP Hnorm Hf a Ha.
rewrite /pickAut.
case:pickP; first by move => x /andP [_ /eqvP Hx]; apply: Hx.
move/pred0P.
apply: contraTeq => _.
apply/existsP.
case: (kHom_extend_fAutL Hf) => g Hg.
suff HgKE : val g \is a kAut K E.
  exists (FAut (coset _ g)); apply/andP; split.
    by rewrite mem_morphim // ?mem_quotient // inE.
  apply/eqvP.
  move => b Hb /=; rewrite Hg //.
  move/subvP/(_ _ Hb): {Hb} HME.
  by move: b; apply/(aut_mem_eqP (mem_repr_coset _) (mem_kAut_coset HgKE)).
have HgK : g \in kAAutL K.
  rewrite inE kAutE subvf andbT.
  apply/kHomP; split; last by move => ? ? _ _; rewrite /= rmorphM.
  move/subvP: HKM => HKM x Hx /=.
  rewrite -Hg ?HKM //.
  by case/kHomP: Hf x Hx.
rewrite qualifE.
move/implyP/(_ HgK): {Hnorm} (Hnorm g) ->.
rewrite andbT.
apply/kHomP; split; last by move => ? ? _ _; rewrite /= rmorphM.
move: HgK; rewrite inE kAutE.
by case/andP => /kHomP [].
Qed.

Lemma aut_root_minPoly K E a b : (K <= E)%VS -> normalField K E ->
  a \in E -> root (minPoly K a) b ->
  exists2 x, x \in 'Aut(E / K) & x a = b.
Proof.
move => HKE Hnormal Ha Hb.
pose f := (kHomExtend K \1 a b).
have HfK : f \is a kHom K <<K; a>>%AS.
  apply: kHomExtendkHom; rewrite ?kHom1 ?subv_refl // map_poly_id // => ? _.
  by rewrite id_lfunE.
exists (pickAut K <<K; a>>%AS E f); first by rewrite pickAut_aut.
rewrite (pickAut_eq _ _ Hnormal HfK) ?subv_adjoin ?memv_adjoin //; last first.
  by apply/FadjoinP.
case: (boolP (a \in K)) => HaK; last by rewrite (kHomExtendX _ (kHom1 K K)).
rewrite kHomExtendExt // id_lfunE.
rewrite elemDeg1 in HaK.
apply/eqP.
have: all (root (minPoly K a)) [::a; b] by rewrite /= root_minPoly Hb.
move/(max_poly_roots (monic_neq0 (monic_minPoly K a))) => /=.
rewrite inE andbT size_minPoly.
by move/contraR; apply; move/eqP: HaK ->.
Qed.

Lemma normalField_factors K E : (K <= E)%VS ->
 reflect (forall a, a \in E -> 
   exists2 r : seq (f_aut E),
     r \subset 'Aut(E / K) &
     minPoly K a = \prod_(i <- r) ('X - (i a)%:P))
   (normalField K E).
Proof.
move => HKE.
apply: (iffP idP); last first.
  move => Hfactor.
  apply/normalFieldP => a Ha.
  case: (Hfactor a Ha) => r /subsetP Hr ->.
  exists (map (fun i : f_aut E => i a) r); last first.
    by rewrite big_map.
  apply/allP => _ /mapP [b /(Hr _) Hb ->].
  by apply: (memv_aut Hb).
move => Hnorm a Ha.
case/normalFieldP/(_ a Ha): (Hnorm) => r Hr Hmin.
pose f b := [pick x \in 'Aut(E / K) | x a == b].
exists (pmap f r).
  apply/subsetP => x.
  rewrite mem_pmap /f.
  case/mapP => b _.
  by case: (pickP _) => // c /andP [Hc _] [->].
rewrite Hmin.
have : all (root (minPoly K a)) r.
  by apply/allP => b; rewrite Hmin root_prod_XsubC.
elim: r {Hmin} Hr => [|b s IH /andP [Hb Hs] /andP [Hrootb Hroots]].
  by rewrite !big_nil.
rewrite /= [f b]/f.
case: (pickP _) => /=; last first.
  move/pred0P.
  apply: contraTeq => _.
  case: (aut_root_minPoly HKE Hnorm Ha Hrootb) => x Hx /eqP Hxa.
  apply/existsP; exists x.
  by apply/andP.
move => x /andP [Hx /eqP Hxa].
by rewrite !big_cons IH ?Hxa.
Qed.

Definition galois U V := [&& (U <= V)%VS, separable U V & normalField U V].

Lemma galoisS K M E : (K <= M <= E)%VS -> galois K E -> galois M E.
Proof.
move => /andP [HKM HME] /and3P [_ Hsep Hnorm].
by rewrite /galois HME (separableSl HKM) // (normalFieldS HKM).
Qed.

Lemma splitting_galoisField K E p :
  p \is a polyOver K -> splittingFieldFor K p E -> separablePolynomial p ->
  galois K E.
Proof.
move => Hp Hsplit Hsep.
apply/and3P; split.
- have [? _ <-] := Hsplit.
  by apply: subv_adjoin_seq.
- have [rs Hrs <-] := Hsplit.
  apply: separable_Fadjoin_seq.
  apply/allP => x Hx.
  apply/separableElementP.
  exists p.
  rewrite Hp Hsep; repeat split => //.
  by rewrite (eqp_root Hrs) root_prod_XsubC.
- by apply: splitting_normalField Hp Hsplit.
Qed.

Lemma galois_dim K E : galois K E ->
 \dim_K E = #|'Aut(E / K)|.
Proof.
case/and3P => HKE.
move/(separableSeparableGenerator)/(_ HKE) => -> Hnorm.
set (a:= separableGenerator K E).
case/normalFieldP/(_ _ (memv_adjoin K a)): (Hnorm) => rs /allP /= Hrs Hmin.
rewrite (dim_sup_field (subv_adjoin K a)) mulnK ?adim_gt0 //.
apply: succn_inj.
rewrite -elementDegreeE -size_minPoly Hmin size_prod_XsubC.
congr (_.+1)%N.
move: (separableGeneratorSep E K).
rewrite /separableElement Hmin separable_prod_XsubC.
move/card_seq_sub <-.
have Hex : forall r : seq_sub rs, exists x,
  (x \in 'Aut(<<K; a>>%AS / K)) && (x a == val r).
  move => r.
  have : root (minPoly K a) (val r).
    by rewrite Hmin root_prod_XsubC; apply: valP.
  case/(aut_root_minPoly (subv_adjoin _ _) Hnorm (memv_adjoin _ _)).
  move => x HxK /eqP Hxa.
  by exists x; rewrite HxK Hxa.
set (f r := xchoose (Hex r)).
have /card_imset <- : injective f.
  move => x y /eqP.
  case/andP: (xchooseP (Hex x)) => HxK /eqP Hxa.
  case/andP: (xchooseP (Hex y)) => HyK /eqP Hya.
  rewrite aut_eq_Fadjoin // Hxa Hya.
  by move/eqP/val_inj.
rewrite [_ @: _](_ : _ = 'Aut(<<K; a>>%AS / K)) //.
apply/eqP; rewrite eqEsubset; apply/andP; split.
  apply/subsetP => _ /imsetP [r Hr ->].
  by case/andP: (xchooseP (Hex r)).
apply/subsetP => x Hx.
have Hxa : x a \in rs.
  by rewrite -root_prod_XsubC -Hmin root_minPoly_aut ?memv_adjoin ?subv_adjoin.
have -> : x = f (SeqSub Hxa); last by apply: mem_imset.
apply/eqP; case/andP: (xchooseP (Hex (SeqSub Hxa))) => ? ?.
by rewrite aut_eq_Fadjoin // eq_sym.
Qed.

Lemma galois_factors K E : 
 reflect ((K <= E)%VS /\ (forall a, a \in E -> 
   exists r : seq (f_aut E), [/\
     r \subset 'Aut(E / K)%g,
     uniq (map (fun i : f_aut E => i a) r) &
     minPoly K a = \prod_(i <- (map (fun j : f_aut E => j a) r))
                         ('X - i%:P)]))
   (galois K E).
Proof.
apply: (iffP idP).
case/and3P => HKE Hsep /(normalField_factors HKE) Hnorm; split; first done.
  move => a HaE.
  case/Hnorm: (HaE) => r Hr Hmin.
  exists r; split => //; last by rewrite big_map.
  rewrite -separable_prod_XsubC big_map -Hmin.
  by move/separableP/(_ _ HaE): Hsep.
case => HKE Hfixed.
apply/and3P; split => //.
  apply/separableP => a /Hfixed [rs [_ Huniq Hmin]].
  by rewrite /separableElement Hmin separable_prod_XsubC.
apply/(normalField_factors HKE) => a.
case/Hfixed => r [Hrs _ Hmin].
exists r => //.
by rewrite Hmin big_map.
Qed.

Lemma fixedField_aut K E : galois K E -> fixedField 'Aut(E / K)%g = K.
Proof.
case/and3P => HKE /separableP Hsep Hnorm.
apply:subv_anti.
rewrite galoisConnectionA ?andbT => //.
apply/subvP => a /fixedFieldP [HaE Ha].
case/normalFieldP/(_ _ HaE): (Hnorm) => rs /allP HrsE Hmin.
move/(_ _ HaE): Hsep.
rewrite elemDeg1 -eqSS -size_minPoly Hmin size_prod_XsubC eqSS.
rewrite /separableElement Hmin separable_prod_XsubC.
move/(count_uniq_mem a).
have -> : a \in rs by rewrite -root_prod_XsubC -Hmin root_minPoly.
move => /= <-; rewrite eq_sym -all_count.
apply/allP => b Hb.
have : root (minPoly K a) b by rewrite Hmin root_prod_XsubC.
case/(aut_root_minPoly HKE Hnorm HaE) => x Hx <-.
by rewrite /= Ha.
Qed.

Lemma galois_fixedField K E : reflect 
 ((K <= E)%VS /\ fixedField 'Aut(E / K)%g = K) (galois K E).
Proof.
apply (iffP idP).
  move => Hgalois.
  split; last by apply: fixedField_aut.
  by case/and3P: Hgalois.
case => HKE Hfixed.
apply/galois_factors; split; first done.
move => a HaE.
pose roots :=
  seq_sub (map (fun x : f_aut E => x a) (enum 'Aut(E / K))).
have Hroot_aut (b : roots) :
    exists x, (x \in 'Aut(E / K)) && (x a == val b).
  case/mapP: (valP b) => [x Hx Hxb].
  by exists x; rewrite Hxb eqxx andbT -mem_enum.
pose root_repr b := xchoose (Hroot_aut b).
have : forall b, root_repr b a = val b.
  by move => b; case/andP: (xchooseP (Hroot_aut b)) => _ /eqP ->.
have : forall b, root_repr b \in 'Aut(E / K).
  by move => b;  case/andP: (xchooseP (Hroot_aut b)).
move: root_repr => root_repr Hroot_repr_aut Hroot_repr.
have Hroot_map_uniq : uniq
    (map (fun x : f_aut E => x a) (map root_repr (enum predT))).
  rewrite -map_comp map_inj_uniq ?enum_uniq //.
  by move => b c //=; rewrite !Hroot_repr; apply: val_inj.
exists (map root_repr (enum predT)); split => //.
  by apply/subsetP => _ /mapP [b Hb ->].
apply/eqP; rewrite -eqp_monic ?monic_minPoly ?monic_prod_XsubC //.
apply/andP; split; last first.
  apply uniq_roots_dvdp; last first.
    by rewrite -[map _ _]map_id -[map _ ]/(map idfun) map_uniq_roots.
  rewrite -map_comp; apply/allP => _ /mapP [b Hb ->] /=.
  by rewrite root_minPoly_aut.
apply minPoly_dvdp; last first.
  rewrite root_prod_XsubC.
  apply/mapP.
  have Haroot :
      a \in map (fun x : f_aut E => x a) (enum 'Aut(E / K)).
    apply/mapP; exists 1%g; last by rewrite aut_id.
    by rewrite mem_enum group1.
  exists (root_repr (SeqSub Haroot)); last by rewrite Hroot_repr.
  by apply: map_f; rewrite mem_enum.
rewrite -map_comp big_map.
apply/polyOverP => i /=.
rewrite -[in X in _ \in X]Hfixed.
apply/fixedFieldP; split.
  apply: polyOverP i.
  apply: rpred_prod => b Hb.
  by rewrite rpredB ?polyOverX // polyOverC (memv_aut (K:=K)).
move => x Hx.
rewrite -coef_map rmorph_prod. congr ((polyseq _) `_ _).
symmetry.
have Hreindex (b : roots) : x (val b) \in
     (map (fun x : f_aut E => x a) (enum 'Aut(E / K))).
  rewrite -Hroot_repr -comp_lfunE -aut_mul //; apply: map_f.
  by rewrite mem_enum groupM.
pose h (b : roots) := SeqSub (Hreindex b) : roots.
rewrite -filter_index_enum filter_predT (reindex_inj (h:=h)) /=.
  apply: eq_bigr => {i} i _.
  rewrite rmorphB /= map_polyX map_polyC /=; congr (_ - _%:P).
  by rewrite !Hroot_repr.
move => b c; move/(f_equal val) => /=.
by move/fmorph_inj/val_inj.
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

Lemma aut_independent E (P : pred (f_aut E))
  (c_ : f_aut E -> L) :
  (forall a, a \in E -> \sum_(x | P x) (c_ x) * (x a) = 0) ->
  (forall x, P x -> c_ x = 0).
Proof.
move => Hsum; move: {2}(#|P|) (erefl #|P|) => n.
elim: n c_ P Hsum => [|n IHn] c_ P Hsum.
  by move/card0_eq => HP0 x; rewrite -[P x]/(x \in P) HP0.
move => Hcard x Hx.
suff Hcy : forall y, P y && (y != x) -> c_ y = 0.
  move: (Hsum _ (mem1v E)).
  rewrite (bigD1 _ Hx) big1 /=; first by rewrite rmorph1 mulr1 addr0.
  by move => y Hy; rewrite (Hcy _ Hy) mul0r.
move => y Hyx; case/andP:(Hyx) => HyP /aut_eqP/eqvP/subvPn [a HaE].
rewrite memv_ker !lfun_simp => Hyxa.
pose d_ y := c_ y * (y a - x a).
apply: (mulIf Hyxa); rewrite mul0r.
apply: (IHn d_ (fun i => P i && (i != x))) => //; last first.
  by move: Hcard; rewrite (cardD1x Hx) add1n; case.
move => b HbE.
have HabE :  a * b \in E by rewrite memv_mul.
rewrite -[X in _ = X]subr0 -[X in _ - X](mulr0 (x a)).
rewrite -[X in _ * X](Hsum _ HbE) -[X in X - _](Hsum _ HabE).
symmetry; rewrite mulr_sumr -sumrB (bigD1 _ Hx) rmorphM /=.
rewrite !mulrA -[X in X * _]mulrC subrr add0r; apply eq_bigr => i Hi.
by rewrite rmorphM /= /d_ mulrBr mulrBl !mulrA -[X in _ - X * _]mulrC.
Qed.

Lemma aut_independent_contra E (P : pred (f_aut E))
  (c_ : f_aut E -> L) x : P x -> c_ x != 0 ->
  exists2 a, a \in E & \sum_(x | P x) (c_ x) * (x a) != 0.
Proof.
move => HPx Hcx.
pose f : 'End(L) := \sum_(y | P y) (val (f_aut_repr y)) * (amull (c_ y)).
suff /lfunPn [a] : projv E * f != 0.
  rewrite zero_lfunE comp_lfunE sum_lfunE => Ha.
  exists (projv E a); first by apply:memv_proj.
  move: Ha; apply: contra; move/eqP => Ha; apply/eqP.
  apply:{Ha} (eq_trans _ Ha); apply: eq_bigr => i _.
  by rewrite comp_lfunE lfunE.
have /existsP : exists x, P x && (c_ x != 0) by exists x; rewrite HPx.
apply: contraL => /eqP/lfunP Hf {x HPx Hcx}.
rewrite negb_exists_in; apply/forallP => x; apply/implyP => HPx; rewrite negbK.
apply/eqP; apply: (aut_independent (P:=P)) => // a Ha; rewrite -(projv_id Ha).
move: (Hf a); rewrite zero_lfunE comp_lfunE sum_lfunE /=; apply: eq_trans.
apply: eq_bigr => i _.
by rewrite comp_lfunE lfunE.
Qed.

Lemma HilbertsTheorem90 K E x a :
 <[x]>%g = 'Aut(E / K) -> a \in E ->
 reflect (exists2 b, b \in E /\ b != 0 & a = b / (x b))
         (galoisNorm K E a == 1).
Proof.
move => Hx HaE.
have HxEK : x \in 'Aut(E / K)%g by rewrite -Hx cycle_id.
apply: (iffP eqP); last first.
  case => b [HbE Hb0] ->.
  by rewrite galoisNormM galoisNormV normAut // mulfV // galoisNorm_eq0.
move => Hnorm.
have Hlog y : {i : 'I_#[x] | y \in <[x]> -> x ^+ i = y}%g.
  case: (boolP (y \in <[x]>%g)).
    by case/cyclePmin => [i Hix Hi]; exists (Ordinal Hix).
  by rewrite -(prednK (order_gt0 x)); exists ord0.
pose log y := sval (Hlog y).
have Hlog_small m : m < #[x]%g -> log (x ^+ m)%g = m :> nat.
  move => Hm.
  move: (svalP (Hlog (x ^+ m)%g) (groupX m (cycle_id _))).
  by move => /eqP; rewrite eq_expg_mod_order !modn_small //; move/eqP.
have Hlog1 : log 1%g = 0%N :> nat by rewrite -(expg0 x) Hlog_small.
pose d_ n := \prod_(i < n) (x ^+ i)%g a.
pose c_ y := d_ (log y).
have Hc0 : c_ 1%g != 0 by rewrite /c_ /d_ Hlog1 big_ord0 oner_neq0.
have : [pred i | i \in 'Aut(E / K)] 1%g by apply: group1.
case/(aut_independent_contra)/(_ Hc0) => d HdE /=.
set b := \sum_(i \in _) _ => Hb0.
exists b; first split => //.
  apply: rpred_sum => i Hi.
  apply: rpredM; last by apply: (memv_aut Hi).
  apply: rpred_prod => j _. by apply: (memv_aut (groupX _ HxEK)).
apply: (canRL (mulfK _)); first by rewrite fmorph_eq0.
have Hlog_bij : {on [pred i \in 'Aut(E / K)],
                    bijective (fun i : 'I_#[x]%g => (x ^+ i)%g)}.
  exists (fun x => sval (Hlog x)) => j Hj.
    by apply: ord_inj; apply: Hlog_small; apply: ltn_ord.
  apply: (svalP (Hlog j)).
  by rewrite inE -Hx in Hj.
move: Hnorm; rewrite /b /galoisNorm !(reindex _ Hlog_bij) /=.
have Hxj: [pred j : 'I_#[x]%g | (x ^+ j)%g \in 'Aut(E / K)] =1 [pred j | true].
  by move => j; rewrite !inE groupX.
rewrite !(eq_bigl _ _ Hxj) /= => Hnorm.
rewrite rmorph_sum mulr_sumr /=.
have Had i : a * x (d_ i) = d_ i.+1.
  rewrite /d_ rmorph_prod /=.
  rewrite big_ord_recl expg0 aut_id; congr (_ * _).
  by apply: eq_bigr => j _; rewrite expgSr aut_mul // comp_lfunE.
rewrite -(prednK (order_gt0 x)) big_ord_recr /= big_ord_recl.
rewrite addrC expg0 aut_id; congr (_ + _).
  rewrite rmorphM /= mulrA Had /c_ Hlog1 /d_ big_ord0.
  rewrite -comp_lfunE -aut_mul // -expgSr (prednK (order_gt0 x)).
  rewrite expg_order aut_id.
  by rewrite Hlog_small (prednK (order_gt0 x)) // Hnorm.
apply: eq_bigr => i _.
rewrite rmorphM /= -comp_lfunE -aut_mul // -expgSr mulrA.
rewrite /c_ Had !Hlog_small //.
  by move: (ltn_ord i); rewrite -ltnS (prednK (order_gt0 x)).
by move/ltnW: (ltn_ord i); rewrite -ltnS (prednK (order_gt0 x)).
Qed.

Section GaloisDim.

Variable (E : {subfield L}) (s : {set f_aut E}).

Lemma aut_matrix :
  {w_ : 'I_#|s| -> L | forall i, w_ i \in E &
    \matrix_(i < #|s|, j < #|s|) enum_val i (w_ j) \in unitmx}.
Proof.
suff [w_ Hw Hmatrix] : { w_ : 'I_#|s| -> L |
  forall i : 'I_#|s|, w_ i \in E &
  \matrix_(i, j) (nth 1%g (enum s) i) (w_ j) \in unitmx}.
  exists w_ => //.
  rewrite (_ : \matrix_(i, j) _ = 
               \matrix_(i, j) (nth 1%g (enum s) i) (w_ j)) //.
  apply/matrixP => i j.
  by rewrite !mxE -enum_val_nth.
rewrite cardE.
elim: (enum s) (enum_uniq (pred_of_set s)) => [_|x xs IH Huniq].
  exists (fun _ => 0) => [i|]; first by move: (ltn_ord i).
  by rewrite unitmxE det_mx00 unitr1.
move: (Huniq); rewrite cons_uniq => /andP [Hx].
move/(IH) => {IH} [w_ Hw].
set M := \matrix_(i, j) _ => HM /=.
pose a := \row_i x (w_ i) *m (invmx M).
pose c_ y := nth (-1) [tuple a 0 i | i < (size xs)] (index y xs).
pose P := [pred y | y \in (x :: xs)].
have HPy : P x by rewrite !inE eqxx.
have Pcx1 : c_ x = -1.
  by rewrite /c_ nth_default // size_tuple leqNgt index_mem.
have Pcx0 : c_ x != 0 by rewrite Pcx1 oppr_eq0 oner_neq0.
have w0ex : exists a : L, (a \in E) && (\sum_(x0 | P x0) c_ x0 * x0 a != 0).
  have [w0 Hw0E Hw0] := aut_independent_contra HPy Pcx0.
  by exists w0; rewrite Hw0E Hw0.
move: {w0ex} (xchoose w0ex) (xchooseP w0ex) => w0 /andP [Hw0E].
set S := BigOp.bigop _ _ _ _ _ => HS.
exists (fun i => if @split 1 (size xs) i is inr i' then w_ i' else w0) => [i|].
  by case: splitP.
rewrite unitmxE -[\det _]mul1r.
pose B := block_mx 1 (-a) 0 1%:M.
have <- : \det B = 1 by rewrite det_ublock !det1 mulr1.
set M' := \matrix_(_,_) _.
rewrite -det_mulmx -[M'](@submxK _ 1 _ 1 _) mulmx_block !mul0mx !mul1mx !add0r.
set DR := drsubmx _.
have -> : DR = M.
  apply/matrixP => i j.
  by rewrite !mxE -[rshift 1 j]/(unsplit (inr _ j)) unsplitK.
rewrite (_ : ursubmx (_) + _ = 0); last first.
  apply/matrixP => ? j.
  rewrite ord1 mxE mulNmx mulmxKV // !(row_mxEr, mxE).
  by rewrite -[rshift 1 j]/(unsplit (inr _ j)) unsplitK subrr.
rewrite det_lblock unitrM andbC -unitmxE HM /=.
rewrite (_ : ulsubmx _ = (x w0)%:M); last first.
  apply/matrixP => i j.
  rewrite !ord1 !(row_mxEl, mxE).
  by rewrite -[lshift (size xs) 0]/(unsplit (inl _ 0)) unsplitK.
rewrite unitfE (_ : _ + _ = -(S%:M)).
  by rewrite -scaleN1r detZ det_scalar1 expr1 mulN1r oppr_eq0.
apply/matrixP => i j.
rewrite !ord1 !mxE !eqxx /S -big_uniq // big_cons Pcx1 /=.
rewrite -mulNrn !mulr1n mulN1r opprD opprK -sumrN; congr (_ + _).
rewrite [X in _ = X](big_tnth 0); apply eq_bigr => k _.
rewrite /c_ index_uniq; last first.
- by case/andP: Huniq; rewrite in_tupleE.
- by rewrite in_tupleE; apply: ltn_ord.
- rewrite nth_mktuple.
  rewrite -mulNr mxE; congr (_ * _).
  rewrite !mxE -[lshift (size xs) 0]/(unsplit (inl _ 0)) unsplitK /=.
  by rewrite (tnth_nth 1%g).
Qed.

Let K := fixedField s.

Lemma direct_sum_fixedField :
  { w_ : 'I_#|s| -> L | 
    [/\ forall i, w_ i \in E,
        forall i, w_ i != 0 & directv (\sum_i K * <[w_ i]>)]
  & forall M : {subfield L}, group_set s -> s \subset 'Aut(E / M)->
    (\sum_i K * <[w_ i]>)%VS = E }.
Proof.
have [w_ HwE] := aut_matrix.
set M := \matrix_(i,j) _.
rewrite -unitmx_tr => HM.
exists w_ => [|? Hs /subsetP HsE].
  split => //.
    move => i.
    apply/contraL: HM => /eqP Hwi.
    rewrite unitmxE unitfE negbK.
    rewrite (expand_det_row _ i).
    apply/eqP; apply: big1 => j _.
    by rewrite !mxE Hwi rmorph0 mul0r.
  apply/directv_sum_independent => kw_ HkwKw Hkw j _.
  have Hk : forall i, exists k, (k \in K) && (k * w_ i == kw_ i).
    move => i.
    case/memv_cosetP : (HkwKw i isT) => kwi HkwiK Hkwi.
    by exists kwi; rewrite HkwiK Hkwi eqxx.
  set kv := \row_i (xchoose (Hk i)).
  suff /matrixP/(_ ord0 j) : kv = 0.
    rewrite !mxE => Hkj.
    have /andP [_ /eqP <-] := xchooseP (Hk j).
    by rewrite Hkj mul0r.
  rewrite {j} -(mul0mx _ (invmx M^T)).
  apply: (canRL (mulmxK HM)).
  apply/matrixP => ? i.
  rewrite ord1 !mxE -[X in _ = X](rmorph0 [rmorphism of enum_val i]).
  rewrite -[in X in _ = X]Hkw rmorph_sum; apply: eq_bigr => j _.
  rewrite !mxE /=.
  have /andP [/fixedFieldP [_ Hkj] /eqP] := xchooseP (Hk j).
  move/(f_equal (enum_val i)) <-.
  by rewrite rmorphM /= Hkj // enum_valP.
apply: subv_anti; apply/andP; split.
  apply/subv_sumP => i _.
  apply: (subv_trans _ (asubv _)).
  apply: prodvS; first by apply: capvSl.
  apply: HwE.
apply/subvP => w Hw.
apply/memv_sumP.
pose wv := (\row_(i < #|s|) enum_val i w).
pose v := wv *m invmx (M^T).
have HvE i : v 0 i \in E.
  rewrite mxE; apply: rpred_sum => j _.
  rewrite !mxE; apply: rpredM; first by apply: (memv_aut (HsE _ (enum_valP j))).
  have HME (a b : 'I_#|s|) : enum_val a (w_ b) \in E.
    by apply: (memv_aut (HsE _ (enum_valP a))).
  suff HmatrixE n (N : 'M_n) : (forall i j, N i j \in E) -> \det N \in E.
    by rewrite /invmx HM !mxE rpredM ?rpredV ?rpredM ?rpredX ?rpredN ?rpred1 //;
      apply: HmatrixE => a b; rewrite !mxE; apply HME.
  move => HN.
  apply: rpred_sum => k _.
  by rewrite rpredM ?rpredX ?rpredN ?rpred1 //; apply: rpred_prod => l _.
exists (fun i => v 0 i * w_ i) => [i _|]; last first.
  pose j := (enum_rank_in (group1 (group Hs)) 1%g).
  transitivity (wv 0 j).
    by rewrite mxE enum_rankK_in ?aut_id // (group1 (group Hs)).
  rewrite -[wv](mulmxKV HM) -/v.
  move: {HvE} v => v.
  rewrite !mxE; apply eq_bigr => i _; rewrite !mxE.
  by rewrite enum_rankK_in ?aut_id // (group1 (group Hs)).
apply: memv_prod; last by rewrite memv_line.
apply/fixedFieldP; split => [//|x Hxs].
transitivity (map_mx x v 0 i); first by rewrite [X in _ = X]mxE.
move: 0 i; apply/matrixP.
apply: (canRL (mulmxK HM)).
apply: (map_mx_inj (f:= [rmorphism of x^-1%g])).
apply/matrixP => ? i; rewrite ord1.
rewrite !mxE rmorph_sum /= -comp_lfunE -aut_mul //.
pose h (i : 'I_#|s|) :=
  enum_rank_in (group1 (group Hs)) (enum_val i * x^-1)%g.
have Hh : enum_val (h i) = (enum_val i * x^-1)%g.
  rewrite enum_rankK_in //.
  by rewrite -[s]/(group Hs : {set f_aut E}) groupM ?groupV ?enum_valP.
transitivity ((v *m M^T) 0 (h i)); last by rewrite mulmxKV // mxE Hh. 
rewrite mxE; apply: eq_bigr => j _.
rewrite rmorphM mxE /= -comp_lfunE -aut_mul // mulgV aut_id; congr (_ * _).
by rewrite !mxE Hh aut_mul // comp_lfunE.
Qed.

End GaloisDim.

Lemma dim_fixedField K E (g : {group f_aut E}) :
  g \subset 'Aut(E / K) ->
  (#|g| = \dim_(fixedField g) E)%N.
Proof.
move => Hg.
have [w [_ Hw0 Hdirect] /(_ _ (groupP g) Hg) HE] := (direct_sum_fixedField g).
rewrite directvE /= in Hdirect.
rewrite -[X in dimv X]HE.
move/eqP: Hdirect ->.
rewrite [(\sum_ _ _)%N](_ : _ = \sum_(i < #|g|) \dim (fixedField g))%N.
  by rewrite sum_nat_const mulnK ?adim_gt0 // cardT -cardE card_ord.
apply: eq_bigr => i _.
by rewrite dim_cosetv.
Qed.

Lemma aut_fixedField (K E : {subfield L}) (g : {group f_aut E}) :
  g \subset 'Aut(E / K)-> 'Aut(E / fixedField g) = g.
Proof.
move => Hg.
symmetry; apply/eqP; rewrite eqEcard; apply/andP; split.
  by apply: (galoisConnectionB Hg).
rewrite [X in _ <= X](_ : _ = \dim_(fixedField g) E) ?(dim_fixedField Hg) //.
rewrite galois_dim ?leqnn //.
apply/galois_fixedField; split; first by apply: capvSl.
apply: subv_anti.
rewrite galoisConnectionA ?capvSl // fixedFieldS //.
by apply: (galoisConnectionB Hg).
Qed.

Section FundamentalTheoremOfGaloisTheory.

Variables E K : {subfield L}.
Hypothesis Hgalois : galois K E.

Section IntermediateField.

Variable M : {subfield L}.
Hypothesis HKME : (K <= M <= E)%VS.
Hypothesis Hnorm : normalField K M.

Lemma normal_galois : galois K M.
Proof.
case/andP: HKME => HKM HME.
case/and3P: Hgalois => HKE Hsep HnormKE. 
by rewrite /galois HKM (separableSr HME).
Qed.

Definition normalField_cast (x : f_aut E) : f_aut M := Aut K M x.

Lemma normalField_castM :
  {in 'Aut(E / K) &, {morph normalField_cast : x y / (x * y)%g}}.
Proof.
case/andP: HKME => HKM /subvP HME.
case/and3P: Hgalois => HKE _ _.
move => x y Hx Hy /=.
apply/eqP/aut_eqP => a Ha.
have HM z : z \in 'Aut(E / K) -> val (f_aut_repr z) \is a kAut K M.
  move => Hz.
  have HzK : (f_aut_repr z) \in kAAutL K.
    rewrite inE -kHomL_kAutL.
    apply/kHomP; split; last by move => ? ? _ _; rewrite /= rmorphM.
    by move => b Hb; apply: (fixed_aut HKE).
  rewrite kAutE.
  move/forallP/(_ z)/implyP/(_ HzK)/eqP: Hnorm => HM.
  rewrite HM subv_refl andbT.
  apply/kHomP; split; last by move => ? ? _ _; rewrite /= rmorphM.
  by move => b Hb; apply: (fixed_aut HKE).
rewrite Aut_eq // ?aut_mul ?HME // ?comp_lfunE ?Aut_eq //; try apply: HM => //;
  last by rewrite groupM.
have := HM _ Hx.
rewrite kAutE; case/andP => _ /subvP; apply.
by apply: memv_img.
Qed.

Canonical normalField_cast_morphism := Morphism normalField_castM.

(* This proof seems unecessarily difficult and should probably be redone. *)
Lemma normalField_ker : ('ker normalField_cast)%g = 'Aut(E / M).
Proof.
case/andP: HKME => HKM HME.
case/and3P: Hgalois => HKE _ _.
apply/eqP; rewrite eqEsubset; apply/andP; split; apply/subsetP; last first.
  move => x Hx.
  apply/morphpreP; split; first by apply: (subsetP (autS HKME)).
  rewrite inE; apply/aut_eqP => a Ha.
  rewrite /= /normalField_cast aut_id Aut_eq ?(fixed_aut _ Hx) //.
  rewrite kAutE; apply/andP; split; last first.
    by apply/subvP => _ /memv_imgP [b Hb ->]; rewrite (fixed_aut _ Hx).
  apply/kHomP; split; last by move => ? ? _ _; rewrite /= rmorphM.
  move => b Hb /=; rewrite (fixed_aut _ Hx) //.
  by move/subvP: HKM; apply.
move => x /morphpreP []; rewrite inE !aut_kAut // !kAutE.
case/andP => /kHomP [HxK _] -> /aut_eqP Hcastx.
rewrite andbT.
apply/kHomP; split; last by move => ? ? _ _; rewrite /= rmorphM.
move => b Hb /=.
rewrite -(Aut_eq HKM) ?Hcastx ?aut_id // kAutE.
apply/andP; split.
  apply/kHomP; split => //; last by move => ? ? _ _; rewrite /= rmorphM.
have HxLK : (f_aut_repr x) \in kAAutL K.
  rewrite inE -kHomL_kAutL.
  apply/kHomP; split => //; last by move => ? ? _ _; rewrite /= rmorphM.
by move/forallP/(_ x)/implyP/(_ HxLK)/eqP:Hnorm ->.
Qed.

Lemma normalField_normal : ('Aut(E / M) <| 'Aut(E / K))%g.
Proof.
rewrite -normalField_ker.
apply: ker_normal.
Qed.

Lemma normalField_img : (normalField_cast @* 'Aut(E / K))%g = 'Aut(M / K).
Proof.
apply/eqP; rewrite eqEsubset; apply/andP; split; apply/subsetP.
  by move => _ /imsetP [x _ ->]; apply: Aut_aut.
case/andP: HKME => HKM HME.
move => x; rewrite aut_kAut // => Hx.
apply/imsetP; rewrite setIid.
exists (pickAut K M E x); first by apply: pickAut_aut.
apply/eqP/aut_eqP => a Ha.
rewrite /= /normalField_cast.
case/and3P: Hgalois => HKE _ HnormKE.
by rewrite Aut_eq ?pickAut_eq ?(kAut_eq _ (pickAut_eq _ _ _ _)) //;
   move: Hx; rewrite kAutE; case/andP.
Qed.

Lemma NormalGaloisGroupIso : ('Aut(E / K) / 'Aut(E / M) \isog 'Aut(M / K))%g.
Proof.
rewrite -normalField_ker -normalField_img.
apply: first_isog.
Qed.

End IntermediateField.

Section IntermediateGroup.

Variable g : {group f_aut E}.
Hypothesis Hg : g \subset 'Aut(E / K)%g.

Lemma fixedField_galois : galois (fixedField g) E.
Proof.
case/and3P: Hgalois => HKE Hsep _.
apply/and3P; split; first by rewrite capvSl.
  apply: (separableSl _ Hsep).
  by rewrite -(galoisConnection HKE Hg).
apply/forallP => a.
apply/implyP => Ha.
case/and3P: Hgalois => _ _ /forallP/(_ a)/implyP; apply.
move: Ha.
rewrite !inE.
apply: kAutS.
by rewrite -(galoisConnection HKE Hg).
Qed.

Hypothesis Hnorm : 'Aut(E / K)%g \subset 'N(g)%g.

Lemma NormalGaloisField : galois K (fixedField g).
Proof.
case/and3P: Hgalois => HKE Hsep HnormEK.
move: (Hg); rewrite (galoisConnection HKE Hg) => HKFF.
have HFFE : (fixedField g <= E)%VS by rewrite capvSl.
apply/and3P; split; first done.
  by apply: (separableSr _ Hsep).
apply/forallP => a.
apply/implyP => HaK.
have HaE : (val a @: E)%VS = E.
 by move/forallP/(_ a)/implyP/(_ HaK)/eqP: HnormEK.
move: HaK; rewrite inE kAutE => /andP [HaK _].
pose x := coset (kAAutL E) a.
have HaKE : a \in (kAAut K E).
 rewrite inE.
 apply/andP; split; last by apply/eqP.
 apply/kHomP; split; last by move => ? ? _ _; rewrite /= rmorphM.
 by case/kHomP: HaK.
have Hx : FAut x \in 'Aut(E / K)%g.
 rewrite mem_morphim ?inE //.
 apply: mem_morphim; last done.
 by move/subsetP: (kAAut_normal K E); apply.
move/subsetP/(_ _ Hx)/normP: Hnorm => Hxg.
set Ma := (val a @: _)%VS.
have : galois Ma E.
 apply: (@galoisS K) => //.
 rewrite -[X in (_ <= _ <= X)%VS]HaE limgS ?capvSl // andbT.
 apply/subvP => b Hb.
 rewrite /=.
 case/kHomP: HaK => /(_ _ Hb) <- _.
 rewrite memv_img //.
 by move/subvP: HKFF; apply.
rewrite /Ma.
case/galois_fixedField => _ <-.
case/galois_fixedField: fixedField_galois => _ <-.
apply/eqP; apply: f_equal; symmetry.
rewrite (aut_fixedField Hg) -[X in X = _]Hxg.
rewrite -[X in (X :^ FAut x)%g](aut_fixedField Hg).
rewrite Aut_conjg //=; last first.
  by move/andP/autS/subsetP: (conj (sub1v K) HKE); apply.
suff -> : (repr x @: fixedField g = a @: fixedField g)%VS by done.
apply: limg_eq => z Hz.
rewrite inE in HaKE.
move/(aut_mem_eqP (mem_repr_coset x) (mem_kAut_coset HaKE)): (eqxx x); apply.
by move/subvP: HFFE; apply.
Qed.

End IntermediateGroup.

End FundamentalTheoremOfGaloisTheory.

End Galois.

Notation "''Aut' ( V / U )" := (aut U V).
