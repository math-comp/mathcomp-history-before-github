Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
Require Import tuple finfun bigop ssralg poly polydiv.
Require Import finset fingroup zmodp morphism perm quotient cyclic.
Require Import matrix mxalgebra vector falgebra fieldext separable.

(******************************************************************************)
(*                                                                            *)
(*       f \is a kHom K E == (f:'End(L)) is a ring morphism on E and fixes K. *)
(*       f \is a kAut K E == (f:'End(L)) is a kHom K E and f @: E == E.       *)
(*                                                                            *)
(*              'Aut(E|K) == the group of automorphisms of E that fix K.      *)
(*              Aut K E f == Constructs an 'Aut(E|K) when f \is a kAut K E.   *)
(*           fixedField G == The field fixed by the set of automorphisms G .  *)
(*                           fixedField set0 == E when G \subset 'Aut(E|K).   *)
(*        normalField K E == E is a normal field extension of K.              *)
(*             galois K E == E is a normal and separable field extension of K.*)
(*        pickAut K M E f == picks some 'Aut(E|K) extending f \is a kHom K M  *)
(*                           when normalfield E K.                            *)
(*      galoisTrace K E a == \sum_(x | x \in ('Aut(E / K))%g) (x a)           *)
(*       galoisNorm K E a == \prod_(x | x \in ('Aut(E / K))%g) (x a)          *)
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
(*
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
*)


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

Section kHom.

Variable F0 : fieldType.
Variable L : fieldExtType F0.

Let F : {subfield L} := aspace1 _.

Implicit Types (K Ka Kb E Ea Eb : {aspace L}).

Section Definitions.

(* Should I make this canonical by setting fixing (f @: E)^C ? *)
Definition kHom (U V: {vspace L}) :=
  [qualify a f : 'End(L) | (U <= fixedSpace f)%VS && (f \is ahom_in V)].

Lemma kHom1 (U V: {vspace L}) : \1%VF \is a kHom U V.
Proof.
rewrite qualifE (id_is_ahom V) andbT.
apply/subvP => u _.
apply/fixedSpaceP.
by rewrite id_lfunE.
Qed.

Lemma kHomP (K : {aspace L}) (V : {vspace L}) (f : 'End(L)) :
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

Variables (K E : {aspace L}).

Variable (f : 'End(L)).

Lemma kHomFixedPoly p : f \is a kHom K E -> p \is a polyOver K ->
  map_poly f p = p.
Proof.
case/kHomP => HK _ /polyOverP Hp.
by apply/polyP => i; rewrite coef_map /= HK ?Hp.
Qed.

Definition kAut (U V: {vspace L}) :=
  [qualify a f | (f \is a kHom U V) && (f @: V == V)%VS].

Fact kHomExtendF_subproof x y :
  linear (fun z => (map_poly f (poly_for_Fadjoin E x z)).[y]).
Proof.
move=> k a b; rewrite linearP /= raddfD hornerE; congr (_ + _).
rewrite -[rhs in _ = rhs]mulr_algl -hornerZ /=; congr _.[_].
by apply/polyP => i; rewrite !(coefZ, coef_map) /= !mulr_algl linearZ.
Qed.
Definition kHomExtend x y := linfun (Linear (kHomExtendF_subproof x y)).

Lemma kHomExtendE x y z :
  kHomExtend x y z = (map_poly f (poly_for_Fadjoin E x z)).[y].
Proof. by rewrite lfunE. Qed.

End Definitions.

Lemma subv_kHom Ka Kb E f : (Ka <= Kb)%VS -> f \in kHom Kb E -> f \in kHom Ka E.
Proof.
move => HK.
case/andP => HKb HE.
apply/andP.
by rewrite (subv_trans _ HKb).
Qed.

Lemma subv_kAut Ka Kb E f : (Ka <= Kb)%VS -> f \in kAut Kb E -> f \in kAut Ka E.
Proof.
move => HK.
case/andP => HKb HE.
apply/andP.
by rewrite (subv_kHom _ HKb).
Qed.

Lemma kHom_subv K Ea Eb f : (Ea <= Eb)%VS -> f \in kHom K Eb -> f \in kHom K Ea.
Proof.
move/subvP => HE.
case/kHomP => HK HEb.
apply/kHomP; split => // x y Hx Hy.
by apply: HEb; apply: HE.
Qed.

Lemma kHom_extensional K E (f g : 'End(L)) : (K <= E)%VS -> {in E, f =1 g} ->
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

Variables (K E : {subfield L}) (f : 'End(L)).

Lemma kHomExtendX x y : f \is a kHom K E -> x \notin E ->
  kHomExtend E f x y x = y.
Proof.
move=> homEf E'x; rewrite kHomExtendE poly_for_X //.
by rewrite (kHomFixedPoly homEf) ?hornerX ?polyOverX.
Qed.

Lemma kHom_inv : f \in kHom K E -> forall x, x \in E -> f x^-1 = (f x)^-1.
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

Hypothesis Hf : f \in kHom K E.
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

(* kHom_horner and kHom_root don't depend on Hf *)
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
by rewrite (map_modp (RMorphism kHomRmorph_subproof)) !map_polyE /=.
Qed.

Lemma kHomExtendkHom : kHomExtend E f x y \is a kHom K (Fadjoin E x) .
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

Implicit Types (U V : {vspace L}).

Lemma kAutE K E f : f \is a kAut K E = (f \is a kHom K E) && (f @: E <= E)%VS.
Proof.
apply/andP/andP; case => Hhom; first by move/eqP->.
move => HfE; split => //.
by rewrite -(dimv_leqif_eq HfE) (kHom_dim Hhom).
Qed.

Lemma kAut_lrmorph (f : 'End(L)) : reflect (lrmorphism f) (f \is a kHom F {:L}).
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

Lemma kAut_extensional K E (f g : 'End(L)) : (K <= E)%VS -> {in E, f =1 g} ->
  (f \is a kAut K E) = (g \is a kAut K E).
Proof.
move => HKE Hfg.
rewrite !kAutE (kHom_extensional HKE Hfg).
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

Lemma kAut_lker0 K f : f \is a kHom K fullv -> lker f == 0%VS.
Proof.
move/(subv_kHom (sub1v _))/kAut_lrmorph=> fM.
by apply/lker0P; exact: (fmorph_inj (RMorphism fM)).
Qed.

Lemma inv_kAut K f : f \is a kHom K fullv -> f^-1%VF \is a kHom K fullv.
Proof.
move=> homFf; have [/kHomP[fKid fM] kerf0] := (homFf, kAut_lker0 homFf).
have f1K: cancel f^-1%VF f by exact: lker0_lfunVK.
apply/kHomP; split=> [x Kx | x y _ _]; apply: (lker0P kerf0).
  by rewrite f1K fKid.
by rewrite fM ?memvf ?{1}f1K.
Qed.

Lemma inv_fAutL_in (f : 'AEnd(L)) : f^-1%VF \is ahom_in fullv .
Proof.
move/is_ahomP/kAut_lrmorph: (valP f) => Hf.
apply/is_ahomP/kAut_lrmorph.
by apply: inv_kAut.
Qed.

Canonical inv_fAutL (f : 'AEnd(L)) : 'AEnd(L) := AHom (inv_fAutL_in f).

Notation "f ^-1" := (inv_fAutL f) : lrfun_scope.

Lemma unit_fAutL (f : 'AEnd(L)) : val f \is a GRing.unit.
Proof.
rewrite qualifE.
apply: (kAut_lker0 (K:=F)).
apply/kAut_lrmorph.
apply: lrmorphismP.
Qed.

Lemma comp_kHom K E f g : f \is a kHom K fullv -> g \is a kHom K E ->
  (f \o g)%VF \is a kHom K E.
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
    (K <= E)%VS -> f \is a kHom K E ->
    p \is a polyOver K -> splittingFieldFor E p U ->
  {g | g \is a kHom K U & {in E, f =1 g}}.
Proof.
move=> sKE homEf Kp /sig2_eqW[rs Dp <-{U}]; set r := rs.
have rs_r: all (mem rs) r by exact/allP.
elim: r rs_r => [_|z r IHr /=/andP[rs_z rs_r]] /= in E f sKE homEf *.
  by exists f.
set Ez := Fadjoin E z; pose fpEz := map_poly f (minPoly E z).
suffices{IHr} /sigW[y fpEz_y]: exists y, root fpEz y.
  have homEz_fz: kHomExtend E f z y \is a kHom K Ez by exact: kHomExtendkHom.
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
  {homK : (\dim_K {:L}).-tuple 'AEnd(L) | separablePolynomial p -> uniq homK
        & forall f : 'AEnd(L), (val f \is a kHom K fullv) = (f \in homK)}.
Proof.
move=> Kp /sig2_eqW[rs Dp]; set r := rs; set E := K => defL.
have [sKE rs_r]: (K <= E)%VS /\ all (mem rs) r by split=> //; exact/allP.
elim: r rs_r => [_|z r IHr /=/andP[rs_z rs_r]] /= in (E) sKE defL *.
  rewrite defL divnn ?adim_gt0 //; exists [tuple \1%AF] => // f.
  rewrite inE; apply/idP/eqP => [/kHomP[f1 _] | ->]; last exact: kHom1.
  by apply/val_inj/lfunP=> x; rewrite id_lfunE f1 ?memvf.
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
have fEz i (y := tnth (Tuple sz_rz) i) :
    {f : 'AEnd(L) | val f \is a kHom E fullv & f z = y}.
  have homEfz: kHomExtend E \1%VF z y \in kHom E Ez.
    rewrite kHomExtendkHom ?kHom1 // map_poly_id => [|u]; last by rewrite lfunE.
    by rewrite (eqp_root DpEz) -/rz root_prod_XsubC mem_tnth.
  have splitFp: splittingFieldFor Ez p fullv.
    exists rs => //; apply/eqP; rewrite eqEsubv subvf -defL genFieldSr //.
    exact/allP.
  have [f homLf Df] := kHom_extends sEEz homEfz Ep splitFp.
  case/andP: (homLf) => _ ahomf.
  exists (AHom ahomf) => //.
  by rewrite -Df ?memx_Fadjoin ?(kHomExtendX _ (kHom1 E E)).
pose mkHom ij := let: (i, j) := ij in (s2val (fEz i) \o tnth homEz j)%AF.
have mkHom_z i j: mkHom (i, j) z = rz`_i.
  have /kHomP[fj_id _]: val (tnth homEz j) \is a kHom Ez {:L}.
    by rewrite DhomEz mem_tnth.
  rewrite /= lfunE /= fj_id ?memx_Fadjoin //.
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
  case: (fEz i1) Eij12 => f /= /(subv_kHom (sub1v _))/kAut_lrmorph fM _ Ej12.
  rewrite -(nth_uniq \1%AF _ _ (UhomEz sepP)) ?size_tuple // -!tnth_nth.
  apply/eqP/val_inj/lfunP=> u; apply: (fmorph_inj (RMorphism fM)) => /=.
  by have:= Ej12 u; rewrite !lfunE.
apply/idP/imageP=> [homLf | [[i j] _ ->] /=]; last first.
  case: (fEz i) => fi /= /comp_kHom->; rewrite ?(subv_kHom sEEz) //.
  by rewrite DhomEz mem_tnth.
have /tnthP[i Dfz]: f z \in Tuple sz_rz.
  rewrite memtE /= -root_prod_XsubC -(eqp_root DpEz).
  by rewrite (kHom_rootK homLf) ?memvf ?subvf ?minPolyOver ?root_minPoly.
case Dfi: (fEz i) => [fi homLfi fi_z]; have kerfi0 := kAut_lker0 homLfi.
set fj := (fi ^-1 \o f)%AF; suffices /tnthP[j Dfj]: fj \in homEz.
  by exists (i, j) => //=; apply/val_inj; rewrite {}Dfi /= -Dfj lker0_compVKf.
rewrite -DhomEz; apply/kHomP.
have homLfj: val fj \is a kHom E fullv := comp_kHom (inv_kAut homLfi) homLf.
split=> [_ /poly_Fadjoin[q Eq ->]|]; last by case/kHomP: homLfj.
have /kAut_lrmorph fjM := subv_kHom (sub1v _) homLfj.
rewrite -[fj _](horner_map (RMorphism fjM)) (kHomFixedPoly homLfj) //.
by rewrite /= lfunE /= Dfz -fi_z lker0_lfunK.
Qed.

End kHom.

Section Galois.

Variable F0 : fieldType.
Variable L : fieldExtType F0.

Let F : {subfield L} := aspace1 _.

Implicit Types (K E : {aspace L}).

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

Lemma enum_fAutL : {fAutL : (\dim {:L}).-tuple 'AEnd(L)
  | forall f, (f \in fAutL)}.
Proof.
have [p Hp Hsfp] := normal_field_splitting.
move: (enum_kHom Hp Hsfp).
rewrite dimv1 divn1; move => [fAutL _ HfAutL].
exists fAutL => f.
rewrite -HfAutL.
by apply/kAut_lrmorph/ahom_is_lrmorphism.
Qed.

(*
Definition LAut_enum : seq 'End(L) := 
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
*)

(*
Record LAut : Type := 
  laut { LAut_end : 'End(L); LAutP : kHom F fullv LAut_end }.

Canonical LAut_subType := Eval hnf in [subType for LAut_end by LAut_rect].
Definition LAut_eqMixin := Eval hnf in [eqMixin of LAut by <:].
Canonical LAut_eqType := Eval hnf in EqType LAut LAut_eqMixin.
*)

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

(*
Definition comp_in_LAut (f g : LAut) :
  (val f \o val g)%VF \in sval (enum_LAut).
Proof. by rewrite -(svalP enum_LAut) comp_kAut ?(svalP enum_LAut) ?ssvalP. Qed.

Definition id_in_LAut : \1%VF \in sval (enum_LAut).
Proof. by rewrite -(svalP enum_LAut) kHom1. Qed.

Lemma LAut_lker0 (f : LAut) : lker (ssval f) = 0%VS.
Proof.
apply/eqP.
apply: (kAut_lker0 (K:=F)).
rewrite (svalP enum_LAut).
by apply: ssvalP.
Qed.

Definition inv_in_LAut (f : LAut) : (ssval f)^-1%VF \in sval (enum_LAut).
Proof.
Proof. by rewrite -(svalP enum_LAut) inv_kAut ?(svalP enum_LAut) ?ssvalP. Qed.
*)

(* the group operation is the categorical composition operation *)
Definition comp_fAutL (f g : 'AEnd(L)) : 'AEnd(L) := (g \o f)%AF.
(*
Definition id_LAut : LAut := laut (kHom1 _ _).
*)

Lemma comp_fAutLA : associative comp_fAutL.
Proof. move => f g h. apply: val_inj. symmetry. apply: comp_lfunA. Qed.

Lemma comp_fAutL1l : left_id \1%AF comp_fAutL.
Proof. by move=> f; apply/val_inj/comp_lfun1r. Qed.

Lemma comp_fAutLK : left_inverse \1%AF (@inv_fAutL _ L) (fun f g => g \o f)%AF.
Proof.
move=> f.
apply/val_inj/lfunP => v.
rewrite /= lker0_compfV ?(kAut_lker0 (K:=1%AS)) //.
by apply/kAut_lrmorph/is_ahomP/valP.
Qed.

Definition fAutL_baseFinGroupMixin := FinGroup.Mixin (T:='AEnd(L))
   comp_fAutLA comp_fAutL1l comp_fAutLK.

Canonical fAutL_baseFinGroupType := Eval hnf in 
   BaseFinGroupType 'AEnd(L) fAutL_baseFinGroupMixin.
Canonical fAutL_finGroupType := Eval hnf in
   @FinGroupType fAutL_baseFinGroupType comp_fAutLK.

Canonical fAutL_of_baseFinGroupType := Eval hnf in
   [baseFinGroupType of 'AEnd(L)].
Canonical fAutL_of_finGroupType := Eval hnf in
   [finGroupType of 'AEnd(L)].

Lemma kHom_extend_fAutL K E f :
  (K <= E)%VS -> f \is a kHom K E ->
  existsb g : 'AEnd(L), (E <= lker (val g - f))%VS.
Proof.
move => HKE Hf.
have [p Hp Hsfp] := normal_field_splitting.
move/(polyOverSv (mem1v K)): Hp => Hp.
move/(splittingFieldForS (mem1v E)): Hsfp => Hsfp.
have [g0 Hg Hfg] := kHom_extends HKE Hf Hp Hsfp.
have Hg_aend : g0 \is ahom_in fullv.
  apply/is_ahomP/kAut_lrmorph.
  apply: (subv_kHom _ Hg).
  by apply: mem1v.
apply/existsP.
exists (AHom Hg_aend).
apply/eqvP => x Hx.
by rewrite Hfg.
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

(*
Lemma LAut_is_lrmorphism (f : LAut) : lrmorphism (LAut_end f).
Proof. by apply: LAut_lrmorph; apply: valP. Qed.

Canonical LAut_addrmorphism f := AddRMorphism (LAut_is_lrmorphism f).
Canonical LAut_addlrmorphism f := AddLRMorphism (LAut_is_lrmorphism f).
*)

Lemma fAutL_mulr (f : 'AEnd(L)) a : amulr a * val f = val f * amulr (f a).
Proof. by apply/lfunP => b; rewrite !comp_lfunE !lfunE /= rmorphM. Qed.

(* The standard proof considers 'End(L) as a vector space over L, but
   'End(L) is canonically a vector space over F.  I'm not sure if it is better
   to put an L-vector space structure on 'End(L) or just use amulr. *)
Lemma fAutL_independent (c_ : 'AEnd(L) -> L) :
  (\sum_f val f * (amulr (c_ f)) == 0)%VF = (forallb i, c_ i == 0).
Proof.
apply/eqP/forallP; last first.
  move => Hc.
  apply: big1 => f _.
  move/(_ f)/eqP:Hc ->.
  by rewrite rmorph0 mulr0.
move => Hf a.
have : true by done.
apply/implyP; move: a; apply/forallP; rewrite -big_andE.
have: uniq (index_enum [finType of 'AEnd(L)]).
  by rewrite /index_enum -enumT enum_uniq.
elim: (index_enum _) c_ Hf => [|f r IH] c_ Hf; first by rewrite big_nil.
rewrite cons_uniq.
case/andP => Hfr Hr.
rewrite big_all.
suff Hcr : all (fun i : fAutL_finType => c_ i == 0) r.
  move:(Hcr) => /= ->.
  move/allP:Hcr => Hcr.
  move: Hf.
  rewrite big_cons big1_seq ?addr0; last first.
    move => i Hi.
    move/eqP: (Hcr i Hi) ->.
    by rewrite rmorph0 mulr0.
  move/(canRL (mulKr (unit_fAutL _)))/eqP.
  rewrite mulr0 -(rmorph0 [rmorphism of (@amulr _ _)]).
  by rewrite (inj_eq (@amulr_inj _ _)) => ->.
apply/allP => i Hi.
have /lfunPn [a] : f != i by apply: contraNneq Hfr => ->.
rewrite -subr_eq0 => Ha.
pose d_ i := c_ i * (f a - i a).
move/eqP: Hf; rewrite big_cons addrC addr_eq0 => /eqP Hf.
suff Hsum : \sum_(f <- r) val f * (amulr (d_ f))%VF = 0.
  move: (IH _ Hsum Hr).
  rewrite big_all.
  move/allP/(_ _ Hi).
  by rewrite /d_ mulf_eq0 orbC (negbTE Ha).
transitivity (\sum_(i <- r) ( val i * amulr (c_ i) * amulr (f a)
                            - amulr a * (val i * amulr (c_ i)))%VF).
apply: eq_bigr => j _.
  rewrite /d_ mulrBr rmorphB rmorphM mulrC rmorphM /=.
  by rewrite mulrBr !mulrA fAutL_mulr.
apply/eqP.
rewrite sumrB -mulr_suml -mulr_sumr Hf addrC mulNr mulrN opprK subr_eq0.
by rewrite -mulrA -rmorphM mulrC rmorphM /= !mulrA fAutL_mulr.
Qed.

Lemma old_fAutL_independent (E : {subfield L}) n (f_ : 'I_n -> 'AEnd(L))
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
    pose G m := (amull (c_ m * ((val (f_ j)) a - (val (f_ m)) a))%R
                \o val (f_ m))%VF.
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

Lemma fAutL_matrix_subproof (E : {subfield L}) n (f_ : 'I_n -> 'AEnd(L)) :
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
 move/(old_fAutL_independent Hf Huniq Hc)/(_ ord0)/eqP.
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

Definition kAut_in (K E : {vspace L}) := 
  [set f : 'AEnd(L) | val f \in kAut K E ].

Definition kAutL (K : {vspace L}) := kAut_in K fullv.

Definition aut (K E : {vspace L}) := (kAut_in K E / kAutL E)%g.

(* Standard mathematical notation for Aut(E/K) puts the larger field first. *)
Notation "''Aut' ( V / U )" := (aut U V) : group_scope.

Lemma kAut_in_group_set (K E : {subfield L}) :
  group_set (kAut_in K E).
Proof.
apply/group_setP; split; first by rewrite inE qualifE kHom1 lim1g eqxx.
move => x y.
rewrite !inE !kAutE.
case/andP; case/kHomP => Hx1 Hx2 Hx3.
case/andP; case/kHomP => Hy1 Hy2 Hy3.
apply/andP; split; last first.
  rewrite SubK limg_comp (subv_trans _ Hy3) // limg_ker0 //.
  apply: (kAut_lker0 (K:=F)).
  apply/kAut_lrmorph.
  apply:lrmorphismP.
apply/kHomP; split; first by move => a Ha;rewrite SubK lfunE /= Hy1 // Hx1.
by move => ? ? _ _; rewrite /= rmorphM.
Qed.

Canonical kAutL_group K E := Eval hnf in group (kAut_in_group_set K E).

Lemma kAut_normal (K E : {subfield L}) :
  kAut_in K E \subset 'N(kAut_in E fullv)%g.
Proof.
apply/subsetP.
move => x.
rewrite !{1}in_set.
case/andP => _ /eqP Hx.
apply/subsetP => ? /imsetP [y].
rewrite !in_set.
case/andP => /kHomP [Hy _] _ ->.
rewrite kAutE subvf andbT.
apply/kHomP; split; last by move => ? ? _ _; rewrite /= rmorphM.
move => a Ha /=.
rewrite -{2}[a](id_lfunE) -[\1%VF]/(val (1%g : 'AEnd(L))) -(mulVg x).
rewrite !SubK !lfunE /= lfunE [X in ((val x) X) = _]Hy //.
rewrite -Hx in Ha.
case/memv_imgP: Ha => [b Hb ->].
by rewrite -comp_lfunE -[(x^-1 \o x)%VF]/(ahval (x * x^-1)%g) mulgV id_lfunE.
Qed.

Lemma aut_refl (K E : {subfield L}) (g : 'AEnd(L)) : val g \is a kAut K E -> 
  g \in coset (kAutL E) g.
Proof.
move => Hg.
rewrite val_coset; first by apply: rcoset_refl.
move/subsetP: (kAut_normal K E).
apply.
by rewrite inE.
Qed.

Lemma aut_mem_eqP (E : {subfield L}) (x y : coset_of (kAutL E)) f g : 
  f \in x -> g \in y -> reflect {in E, val f =1 val g} (x == y).
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

Lemma aut_eqP (E : {subfield L}) (x y : coset_of (kAutL E)) : 
  reflect {in E, repr x =1 repr y} (x == y).
Proof. by apply: aut_mem_eqP; apply: mem_repr_coset. Qed.

Lemma aut_id (E : {subfield L}) a :
  repr (1:coset_of (kAutL E))%g a = a.
Proof. by rewrite repr_coset1 id_lfunE. Qed.

Lemma aut_mul (E : {subfield L}) (x y : coset_of (kAutL E)) :
 {in E, repr (x*y)%g =1 (repr y \o repr x)%AF}.
Proof.
move => a Ha.
transitivity (val (repr x * repr y)%g a); last by rewrite /= comp_lfunE.
move: a Ha.
apply/(@aut_mem_eqP _ (x*y) (x*y)) => //; first by rewrite mem_repr_coset.
rewrite -{2}(coset_mem (mem_repr_coset x)).
rewrite -{2}(coset_mem (mem_repr_coset y)).
rewrite -coset_morphM ?repr_coset_norm //.
rewrite val_coset; first by apply: rcoset_refl.
by apply: groupM; apply: repr_coset_norm.
Qed.

(*
Lemma aut_mul_limg U (E : {subfield L}) (x y : coset_of (kAutL E)) :
 (U <= E -> repr (x*y)%g @: U = (repr y \o repr x) @: U)%VS.
Proof.
move => HUE.
apply: limg_eq => z Hz.
rewrite aut_mul.
*)

Lemma aut_inv (E : {subfield L}) (x : coset_of (kAutL E)) :
 {in E, repr (x^-1)%g =1 (repr x)^-1%VF}.
Proof.
move => a Ha /=.
apply: (canRL (lker0_lfunK _)); last first.
  by rewrite -comp_lfunE -(aut_mul (x^-1)%g x) // mulVg aut_id.
rewrite (kAut_lker0 (K:=F)) //; apply/kAut_lrmorph.
apply: lrmorphismP.
Qed.

Section Automorphism.

Definition pickAut U V W f :=
  odflt (coset _ 1%g)
    [pick x \in 'Aut(W / U)%g
    | (V <= lker (val (repr x) - f))%VS].

(* Aut is the main "constructor" used for the aut type
   it converts (f: kAut K E) into 'Aut(E|K) *)
Definition Aut U W f := pickAut U W W f.

Variables K E : {subfield L}.

(* with some effor this can probably be generalized to arbitrary vspaces*)
Lemma pickAut_aut V f : pickAut K V E f \in 'Aut(E / K)%g.
Proof.
rewrite /pickAut.
case:pickP; last by rewrite coset_id group1.
by move => ? /andP [? ?].
Qed.

Lemma Aut_aut f : Aut K E f \in 'Aut(E / K)%g.
Proof. apply: pickAut_aut. Qed.

Hypothesis HKE : (K <= E)%VS.

Lemma Aut_eq f : f \is a kAut K E -> {in E, repr (Aut K E f) =1 f}.
Proof.
move => Hf a Ha.
rewrite /Aut /pickAut.
case:pickP; first by move => x /andP [_ /eqvP Hx]; apply: Hx.
move/pred0P.
apply: contraTeq => _.
apply/existsP.
move: (Hf); rewrite kAutE; case/andP => HfKE HfE.
case/existsP: (kHom_extend_fAutL HKE HfKE) => g /eqvP Hg.
have HgKE : val g \is a kAut K E by rewrite (kAut_extensional HKE Hg).
exists (coset _ g); apply/andP; split; first by rewrite mem_quotient // inE.
apply/eqvP.
move => b Hb /=; rewrite -Hg //.
move: b Hb.
by apply/(aut_mem_eqP (mem_repr_coset _) (aut_refl HgKE)).
Qed.

Lemma memv_aut x a : x \in 'Aut(E / K)%g -> a \in E -> repr x a \in E.
Proof.
rewrite /aut -imset_coset.
move/imsetP.
case => g; rewrite inE => {x} Hg -> Ha.
move/(aut_mem_eqP (mem_repr_coset _) (aut_refl Hg)):(eqxx (coset (kAutL E) g)).
move => -> //.
case/andP: Hg => _ /eqP Hg.
by rewrite -[in X in _ \in X]Hg memv_img.
Qed.

Lemma aut_kAut x : x \in 'Aut(E / K)%g = (val (repr x) \is a kAut K E).
Proof.
rewrite /aut -imset_coset.
apply/imsetP/idP.
  case => g; rewrite inE => {x} Hg ->.
  rewrite (kAut_extensional (g:=val g) HKE _) //.
  by apply/(aut_mem_eqP (mem_repr_coset _) (aut_refl Hg)).
move => Hx.
exists (repr x); first by rewrite inE.
by rewrite coset_reprK.
Qed.

Lemma fixed_aut x a : x \in 'Aut(E / K)%g -> a \in K -> repr x a = a.
Proof.
rewrite aut_kAut.
case/andP => /kHomP [Hx _] _ Ha.
by rewrite Hx.
Qed.

End Automorphism.

Lemma subv_aut (E K1 K2 : {subfield L}) : (K1 <= K2)%VS -> (K2 <= E)%VS -> 
  ('Aut(E / K2) \subset 'Aut(E / K1))%g.
Proof.
move => HK HKE.
apply/subsetP => x.
rewrite !aut_kAut //; last by apply:(subv_trans (y:=K2)).
by move/(subv_kAut HK).
Qed.

Lemma Aut_conjg (K E : {subfield L}) x : (K <= E)%VS -> x \in 'Aut(E / F)%g ->
  ('Aut(E / K) :^ x = 'Aut(E / (repr x @: K)%VS))%g.
Proof.
move => HKE Hx.
apply/eqP.
have HxKE : (repr x @: K <= E)%VS.
  apply/subvP => _ /memv_imgP [a Ha ->].
  apply: (memv_aut Hx).
  by move/subvP: HKE; apply.
wlog suff Hsuff : x K HKE Hx HxKE / 
  (('Aut(E / K) :^ x)%g \subset ('Aut(E / (repr x @: K)%VS))%g).
  rewrite eqEsubset Hsuff // -sub_conjgV -[X in _ \subset ('Aut(E / X))%g]lim1g.
  rewrite -[\1%VF]/((1:'AEnd(L))%g:'End(L)) -(mulgV (repr x)) limg_comp.
  suff: {in (repr x @: K)%VS, (repr (x^-1) =1 (repr x)^-1)%g}.
    move/limg_eq <-.
    apply: Hsuff; first done.
    - by rewrite groupV.
    - rewrite -limg_comp.
      move/eqvP/(subv_trans HKE)/eqvP/limg_eq: (aut_mul x (x^-1)%g) <-.
      by rewrite mulgV repr_coset1 lim1g.
  move => z Hz; apply: aut_inv.
  by move/subvP: HxKE; apply.
apply/subsetP => y.
rewrite mem_conjg !aut_kAut //=.
have /(kAut_extensional HKE) -> : 
  {in E, repr (y ^ (x^-1))%g =1 (repr x^-1%g \o repr y \o repr x)%AF}.
  rewrite conjgE invgK => z Hz.
  have Hxz : repr x z \in E by apply: (memv_aut Hx).
  by rewrite !(aut_mul,comp_lfunE) //.
rewrite !kAutE.
case/andP => HyKE.
rewrite !limg_comp.
move: (groupVr Hx).
rewrite aut_kAut; last by apply: sub1v.
case/andP => _ /eqP HxE.
rewrite -[X in (_ <= X)%VS]HxE {HxE} limg_ker0; last first.
  apply: (kAut_lker0 (K:=F)); apply/kAut_lrmorph; apply:lrmorphismP.
move: Hx.
rewrite aut_kAut; last by apply: sub1v.
case/andP => Hx /eqP HxE.
rewrite HxE => HyE.
rewrite HyE andbT.
apply/kHomP; split; last by move => ? ? _ _; rewrite /= rmorphM.
move => _ /memv_imgP [a Ha ->].
case/kHomP: HyKE => /(_ _ Ha) HyVa _.
rewrite -[in X in _ = X]HyVa !comp_lfunE /= -[X in _ = X]comp_lfunE.
rewrite -(aut_mul (x^-1) x) ?mulVg ?repr_coset1 ?id_lfunE //.
move/subvP: HyE; apply.
rewrite memv_img // -[in X in _ \in X]HxE memv_img //.
by move/subvP: HKE; apply.
Qed.

Lemma uniq_aut (K E : {subfield L}) n f_ :
 (forall i, f_ i \in 'Aut(E / K)%g) ->
 uniq [seq f_ i | i <- enum 'I_n] ->
 uniq [seq (val (repr (f_ i)) \o projv E)%VF |  i <- enum 'I_n].
Proof.
move => Hf.
set (s := [seq f_ i |  i <- enum 'I_n]).
pose g (x : coset_of (kAutL E)) := (val (repr x) \o projv E)%VF.
suff Hs : {in s &, injective g} by rewrite -(map_inj_in_uniq Hs) -map_comp.
move=> x y Hx Hy /= Hg.
apply/eqP/(aut_eqP) => a /projv_id <-.
by rewrite -[_ (projv E a)]comp_lfunE [(_ \o _)%VF]Hg comp_lfunE.
Qed.

Definition fixedField (E : {vspace L})
  (s : {set coset_of (kAutL E)}) :=
  (E :&: \bigcap_(x \in s) (fixedSpace (repr x)))%VS.

Lemma fixedFieldP (E : {subfield L})
   (s : {set coset_of (kAutL E)}) a :
 reflect (a \in E /\ (forall x, x \in s -> repr x a = a))
         (a \in fixedField s).
Proof.
rewrite /fixedField.
apply/(iffP memv_capP); case => HaE H; (split; first done).
  move => x Hx.
  by move/subv_bigcapP/(_ _ Hx)/fixedSpaceP: H.
apply/subv_bigcapP => i Hi.
by apply/fixedSpaceP; apply: H.
Qed.

Lemma galoisAdjuctionA (K E : {subfield L}) :
  (K <= E)%VS ->
  (K <= fixedField ('Aut(E / K))%g)%VS.
Proof.
move => HKE.
apply/subvP => a HaK.
apply/fixedFieldP; split; first by move/subvP: HKE; apply.
move => x Hx.
by apply: (fixed_aut HKE).
Qed.

Fact fixedField_is_aspace_subproof  (E : {subfield L})
   (s : {set coset_of (kAutL E)}) :
  let FF := fixedField s in
  (has_algid FF  && (FF * FF <= FF)%VS).
Proof.
rewrite /fixedField -big_filter.
move : (filter _ _) => /= {s} r.
pose f (i:coset_of (kAutL E)) := repr i.
have -> : (\bigcap_(i <- r) fixedSpace (repr i)
        = \bigcap_(i <- [seq f i | i <- r]) fixedSpace i)%VS by rewrite big_map.
move : {r f} (map _ r) => r.
elim : r E => [|r rs IH] E; first by rewrite big_nil capvf; case: E.
rewrite big_cons capvA.
by apply: IH.
Qed.
Canonical fixedField_aspace (E : {subfield L})
   (s : {set coset_of (kAutL E)}) : {subfield L}
   := ASpace (fixedField_is_aspace_subproof s).

Lemma fixedField_subset (E : {subfield L})
   (s1 s2 : {set coset_of (kAutL E)}) :
   (s1 \subset s2) -> (fixedField s2 <= fixedField s1)%VS.
Proof.
move => /subsetP Hs.
apply/subvP => a /fixedFieldP [HaE Ha].
apply/fixedFieldP; split; first done.
move => x Hx.
by rewrite Ha // Hs.
Qed.

Definition galoisTrace (K E : {vspace L}) a := 
 \sum_(i | i \in ('Aut(E / K))%g) (repr i a).

Definition galoisNorm (K E : {vspace L}) a := 
 \prod_(i | i \in ('Aut(E / K))%g) (repr i a).

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
 (K <= E)%VS -> a \in E -> galoisTrace K E a \in fixedField 'Aut(E / K)%g.
Proof.
move => HKE Ha.
apply/fixedFieldP.
split.
  apply: memv_suml => i.
  rewrite (aut_kAut HKE).
  case/andP => _ /eqP HE.
  by rewrite -[in X in _ \in X]HE memv_img.
move => x Hx.
rewrite rmorph_sum /galoisTrace -{2}['Aut(E / K)%g](rcoset_id Hx).
rewrite (reindex_inj (mulIg (x^-1)%g)).
symmetry.
apply: eq_big => i; first by rewrite /= mem_rcoset.
by rewrite /= -comp_lfunE -(aut_mul (i * x^-1)) // mulgKV.
Qed.

Lemma traceAut a x : a \in E -> x \in 'Aut(E / K)%g -> 
  galoisTrace K E (repr x a) = galoisTrace K E a.
Proof.
move => Ha Hx.
rewrite /galoisTrace -{2}['Aut(E / K)%g](lcoset_id Hx).
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
 (K <= E)%VS -> a \in E -> galoisNorm K E a \in fixedField 'Aut(E / K)%g.
Proof.
move => HKE Ha.
apply/fixedFieldP.
split.
  apply: memv_prodl => i.
  rewrite (aut_kAut HKE).
  case/andP => _ /eqP HE.
  by rewrite -[in X in _ \in X]HE memv_img.
move => x Hx.
rewrite rmorph_prod /galoisNorm -{2}['Aut(E / K)%g](rcoset_id Hx).
rewrite (reindex_inj (mulIg (x^-1)%g)).
symmetry.
apply: eq_big => i; first by rewrite /= mem_rcoset.
by rewrite /= -comp_lfunE -(aut_mul (i * x^-1)%g) // mulgKV.
Qed.

Lemma normAut a x : a \in E -> x \in 'Aut(E / K)%g -> 
  galoisNorm K E (repr x a) = galoisNorm K E a.
Proof.
move => Ha Hx.
rewrite /galoisNorm -{2}['Aut(E / K)%g](lcoset_id Hx).
rewrite (reindex_inj (mulgI (x^-1)%g)).
apply: eq_big => i;first by rewrite /= mem_lcoset.
by rewrite -comp_lfunE -aut_mul // mulKVg.
Qed.

End TraceAndNorm.

Definition normalField (K E : {vspace L}) :=
 forallb x, (x \in kAutL K) ==> (x @: E == E)%VS.

Lemma normalFieldP : forall (K E : {subfield L}), 
 reflect (forall a, a \in E -> exists2 r, all (fun y => y \in E) r
                                 & minPoly K a = \prod_(b <- r) ('X - b%:P))
         (normalField K E).
Proof.
move => K E.
apply: (iffP forallP); last first.
  move => Hnorm x.
  apply/implyP.
  rewrite inE kAutE.
  case/andP => Hx _.
  suff: val x \is a kAut K E by case/andP.
  rewrite kAutE (kHom_subv (subvf E)) //=.
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
case: (NormalFieldExt K a) => r.
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
have Hy : y \is a kHom K (Fadjoin K a).
  apply: kHomExtendkHom.
  - by apply kHom1.
  - by apply subv_refl.
  - by rewrite map_poly_id // => ? ?; rewrite id_lfunE.
case/existsP: (kHom_extend_fAutL (subsetKFadjoin K a) Hy) => g /eqvP Hg.
have <- : g a = b by rewrite Hg ?memx_Fadjoin // (kHomExtendX _ (kHom1 K _)).
have HgK : (g \in kAutL K).
  rewrite inE kAutE subvf andbT.
  apply/kHomP; split; last by move => ? ? _ _; rewrite /= rmorphM.
  move/subvP: (subsetKFadjoin K a) => HKa x Hx /=; rewrite Hg; last first.
    by apply: HKa.
  by move/kHomP: Hy => [Hy _]; apply Hy.
move/implyP/(_ HgK)/eqP: (Hnorm g) <-.
by apply: memv_img.
Qed.

Definition galois U V := [&& (U <= V)%VS, separable U V & normalField U V].

Lemma separable_dim (K : {subfield L}) x : separableElement K x ->
  normalField K (Fadjoin K x) ->
  elementDegree K x = #|'Aut((Fadjoin K x) / K)%g|.
Proof.
move => Hsep.
set E := Fadjoin K x.
case/normalFieldP/(_ _ (memx_Fadjoin K x)) => r.
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
 pose f (y : coset_of (kAutL E)) := repr y x.
 rewrite -(size_map f).
 apply: uniq_leq_size.
  rewrite map_inj_in_uniq ?enum_uniq //.
  move => a b.
  rewrite 2!mem_enum => Ha Hb Hab.
  apply/eqP/aut_eqP => ?.
  case/poly_Fadjoin => p Hp ->.
  rewrite -!horner_map /= -/(f a) -/(f b) Hab.
  move: Ha; rewrite (aut_kAut (subsetKFadjoin _ _ )); case/andP.
  move/(kHomFixedPoly)/(_ Hp) => -> _.
  move: Hb; rewrite (aut_kAut (subsetKFadjoin _ _ )); case/andP.
  by move/(kHomFixedPoly)/(_ Hp) => -> _.
 move => ? /mapP [a Ha ->].
 rewrite mem_enum in Ha.
 rewrite -root_prod_XsubC -Hmin /f.
 move: Ha; rewrite (aut_kAut (subsetKFadjoin _ _ )); case/andP.
 move/(kHom_rootK)/(_ (subsetKFadjoin _ _) _ _
                      (minPolyOver K x) (memx_Fadjoin _ _)) => Hroot _.
 by rewrite Hroot // root_minPoly.
pose f y := Aut K (Fadjoin_aspace K x) (kHomExtend K \1%VF x y).
rewrite -(size_map f).
suff/card_uniqP <- : uniq (map f r).
 apply: subset_leq_card.
 apply/subsetP.
 move => ? /mapP [a _ ->].
 by apply: Aut_aut.
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
pose g := repr (Aut K (Fadjoin_aspace K x) fa).
have HAuta : fa \is a kAut K (Fadjoin K x).
 rewrite kAutE (kHomExtendkHom (kHom1 K K) (subv_refl K) (Hroot _ Ha)).
 apply/subvP => ? /memv_imgP [? /poly_Fadjoin [p Hp ->] ->].
 rewrite (kHomExtend_poly (kHom1 K K) (Hroot _ Ha) Hp).
 rewrite (eq_map_poly (fun x => id_lfunE x)).
 rewrite map_polyE map_id polyseqK.
 case/poly_Fadjoin: (Hr _ Ha) => q Hq ->.
 by rewrite -horner_comp mempx_Fadjoin ?polyOver_comp.
have HAutb : fb \is a kAut K (Fadjoin K x).
 rewrite kAutE (kHomExtendkHom (kHom1 K K) (subv_refl K) (Hroot _ Hb)).
 apply/subvP => ? /memv_imgP [? /poly_Fadjoin [p Hp ->] ->].
 rewrite (kHomExtend_poly (kHom1 K K) (Hroot _ Hb) Hp).
 rewrite map_poly_id => [|xx _ /=]; last by rewrite id_lfunE.
 case/poly_Fadjoin: (Hr _ Hb) => q Hq ->.
 by rewrite -horner_comp mempx_Fadjoin ?polyOver_comp.
by rewrite -(Aut_eq (subsetKFadjoin K x) HAuta)
           -?(Aut_eq (subsetKFadjoin K x) HAutb) ?Hab ?memx_Fadjoin.
Qed.

Lemma galois_dim : forall (K E : {subfield L}), galois K E ->
 \dim E = (\dim K * #|'Aut(E / K)%g|)%N.
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
 forall a, a \in E -> a \notin K -> exists x, (x \in 'Aut(E / K)%g) && 
   (repr x a != a).
Proof.
case/and3P => [HKE Hsep Hnorm] a HaE.
rewrite elemDeg1 -eqSS -size_minPoly.
case/normalFieldP/(_ a HaE): (Hnorm) (root_minPoly K a) => r Hr Hmin.
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
have: kHomExtend K \1%VF a b \is a kHom K (Fadjoin K a) .
 rewrite kHomExtendkHom ?kHom1 ?subv_refl //.
 rewrite (eq_map_poly (fun x => id_lfunE x)) map_polyE map_id polyseqK.
 by rewrite Hmin root_prod_XsubC.
(*  todo: try to generalize kAut_pick to support this *)
case/(kHom_extend_fAutL (subsetKFadjoin K a))/existsP => f /eqvP Hf.
have HfK: f \in kAutL K.
  rewrite inE kAutE subvf andbT.
  apply/kHomP; split; last by move => ? ? _ _; rewrite /= rmorphM.
  move => x Hx.
  rewrite /= Hf ?kHomExtendExt ?id_lfunE //.
  by move/subvP: (subsetKFadjoin K a); apply.
move/forallP/(_ f)/implyP/(_ HfK): Hnorm => HfE.
exists (Aut K E f).
rewrite Aut_aut Aut_eq //.
  rewrite Hf ?memx_Fadjoin // (kHomExtendX (K:=F)) ?kHom1 //.
  by rewrite elemDeg1 -eqSS -size_minPoly Hmin.
rewrite qualifE /kAut HfE andbT.
rewrite inE kAutE in HfK.
case/andP: HfK.
by move/(kHom_subv (subvf E)).
Qed.

Lemma galois_factors_subproof (K E : {subfield L}) : (K <= E)%VS ->
 (forall a, a \in E -> a \notin K -> exists x, (x \in 'Aut(E / K)%g) && 
   (repr x a != a)) ->
 (forall a, a \in E -> 
   exists r, [/\
     r \subset 'Aut(E / K)%g,
     uniq (map (fun i : coset_of (kAutL E) => repr i a) r) &
     minPoly K a = \prod_(i <- r)('X - (repr i a)%:P)]).
Proof.
pose f (j : L) := ('X - j%:P).
move => HKE Hgal a HaE.
pose h (i : coset_of (kAutL E)) := repr i a.
suff : forall n, n.+1 < size (minPoly K a) -> 
        exists r, let r' := 
           map (fun i : coset_of (kAutL E) => repr i a) r
         in [/\ r \subset 'Aut(E / K)%g,  uniq r',
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
 move/subsetP/allP/(all_nthP 1%g)/(_ _ (@ltn_ord _ i)): Haut.
 rewrite aut_kAut //; case/andP => _ /eqP HE.
 by rewrite -[in X in (_ \in X)]HE memv_img.
move/(_ _ Hcg) => HcE.
case/(_ _ HcE HcK): Hgal => x /andP [Hx Hxc].
have/allPn : ~~(all (fun x => x \in (map h r)) (map (repr x) (map h r))).
 move: Hxc.
 apply: contra.
 move/allP => Hsubset.
 case/(nthP 0): Hcg => i _ <-.
 rewrite -coef_map.
 apply/eqP.
 move: i.
 apply/polyP.
 rewrite rmorph_prod.
 transitivity (\prod_(i <- map h r)('X - (repr x i)%:P)).
  apply: eq_bigr => i _.
  by rewrite rmorphB /= map_polyX map_polyC.
 rewrite -(big_map (repr x) predT f).
 apply/eqP.
 rewrite -eqp_monic ?monic_prod_XsubC // -dvdp_size_eqp.
  by rewrite !size_prod_XsubC size_map.
 apply: uniq_roots_dvdp.
  apply/allP => b Hb.
  rewrite root_prod_XsubC.
  by apply: Hsubset.
 rewrite uniq_rootsE map_inj_uniq //.
 apply: (can_inj (g:= (repr x)^-1)%g).
 move => z; rewrite -comp_lfunE.
 by rewrite -[(_ \o _)%VF]/(ahval ((repr x) *(repr x)^-1)%g) mulgV id_lfunE.
rewrite -map_comp.
case => ? /mapP [y Hyr ->] Hyx.
have Hy : y \in ('Aut(E / K))%g by move/subsetP: Haut; apply.
have Huniq : uniq (map h ((y * x)%g :: r)).
 by rewrite /= Hr andbT [h _]aut_mul ?comp_lfunE.
exists (cons (y * x)%g r); split.
- by rewrite subset_all /= -subset_all Haut groupM.
- by apply: Huniq.
- by rewrite /= Hnr.
- rewrite uniq_roots_dvdp //; last by rewrite uniq_rootsE; apply: Huniq.
  apply/allP => ? /mapP [z Hz ->].
  apply: (kHom_rootK _ HKE); rewrite ?minPolyOver ?root_minPoly //.
  suff HyAut : z \in 'Aut(E / K)%g.
    by move: HyAut; rewrite aut_kAut //; case/andP.
  move: Hz.
  rewrite inE.
  case/orP; last by move: z; apply/subsetP.
  move/eqP ->.
  by rewrite groupM.
Qed.

Lemma galois_factors (K E : {subfield L}) : 
 reflect ((K <= E)%VS /\ (forall a, a \in E -> 
   exists r, [/\
     r \subset 'Aut(E / K)%g,
     uniq (map (fun i : coset_of (kAutL E) => repr i a) r) &
     minPoly K a = \prod_(i <- r)('X - (repr i a)%:P)]))
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
 pose h (i : coset_of (kAutL E)) := repr i a.
 by rewrite /separableElement Hmin -(big_map h predT f) separable_prod_XsubC.
apply/normalFieldP => a Ha.
case/H: (Ha) => r [/subsetP Haut Hr Hmin].
pose h (i : coset_of (kAutL E)) := repr i a.
exists (map h r); last by rewrite big_map.
apply/allP => ? /mapP [x Hx ->].
move: (Haut _ Hx); rewrite aut_kAut //; case/andP => _ /eqP <-.
by rewrite memv_img.
Qed.

Lemma galois_fixedField (K E : {subfield L}) : reflect
 ((K <= E)%VS /\ fixedField 'Aut(E / K)%g = K)
 (galois K E).
Proof.
apply: (iffP idP).
 move => Hgal.
 case/and3P: (Hgal) => HKE _ _.
 split; first done.
 apply: subv_anti.
 apply/andP; split; last by apply: galoisAdjuctionA.
 apply/subvP => a /fixedFieldP [HaE HFF].
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
apply/fixedFieldP; split; first done.
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
 galois K E -> (<[x]> = 'Aut(E / K))%g -> a \in E ->
 reflect (exists2 b, b \in E /\ b != 0 & a = b / (repr x b))
         (galoisNorm K E a == 1).
Proof.
case/and3P => HKE _ _ Hx HaE.
apply: (iffP eqP); last first.
 case => b [HbE Hb0] ->.
 have HxEK : x \in 'Aut(E / K)%g by rewrite -Hx cycle_id.
 by rewrite galoisNormM galoisNormV normAut // mulfV // galoisNorm_eq0.
move => Hnorm.
have Ha0 : a != 0 by rewrite -(galoisNorm_eq0 K E) Hnorm oner_neq0.
pose n := #[x]%g.
pose c_ i := \prod_(j < i) (repr (x ^+ j)%g a).
have HcE i : c_ i \in E.
 elim: i => [|i IH]; first by rewrite [c_ _]big_ord0 mem1v.
 by rewrite /c_ big_ord_recr memv_mul // (memv_aut (K:=K)) // -Hx mem_cycle.
have Hxc i : (repr x (c_ i)) = a ^-1 * (c_ i.+1).
 rewrite rmorph_prod /c_ big_ord_recl expg0 repr_coset1 id_lfunE mulKf //.
 apply: eq_bigr => j _.
 by rewrite expgSr aut_mul ?comp_lfunE.
pose f_ i := repr (x ^+ i)%g.
have HxE i : (val (f_ i) @: E)%VS = E.
 move: (mem_cycle x i).
 rewrite Hx aut_kAut //.
 by case/andP => _ /eqP. 
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
 by apply:(old_fAutL_independent
   (fun i : 'I_n => HxE i) Huniq (fun i : 'I_n => HcE i)).
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
  rewrite rmorphM /= -comp_lfunE -aut_mul //.
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
  by apply: eq_bigr => i _ /=; rewrite -comp_lfunE -aut_mul // -expgSr.
apply: eq_bigr => i _.
rewrite !lfun_simp /= rmorphM mulrA.
rewrite rmorph_prod [c_ _]big_ord_recl expg0 repr_coset1 id_lfunE.
congr (_ * _ * _).
  apply eq_bigr => j _.
  by rewrite /= -comp_lfunE -aut_mul // -expgSr.
by rewrite /= -comp_lfunE -aut_mul // -expgSr.
Qed.

Section GaloisDim.

Variable E : {subfield L}.

Let Coset :=
 [finGroupType of coset_of (kAutL E)].

Let g_ (i : Coset) := val (repr i).

Lemma uniq_projv_subproof 
  (s : {set Coset}) :
  uniq [seq (g_ (enum_val i) \o (projv E))%VF | i <- enum 'I_#|s|].
Proof.
rewrite map_inj_uniq; first by rewrite enum_uniq.
move => i j /= /lfunP Hij.
apply: enum_val_inj.
apply/eqP/aut_eqP => a /projv_id <-.
by rewrite -[_ (_ a)]comp_lfunE Hij comp_lfunE.
Qed.

Lemma dim_FixedField_subproof
  (s : {set Coset}) :
  (forall i : Coset, i \in s -> (g_ i @: E)%VS = E) ->
  #|s| * \dim (fixedField s) <= \dim E /\ 
  (group_set s -> \dim E <= #|s| * \dim (fixedField s)).
Proof.
move => HE.
pose f_ i := repr (@enum_val _ (pred_of_set s) i).
case: (@fAutL_matrix_subproof E _ f_).
  move => i.
  apply: HE.
  by apply: enum_valP.
 apply: uniq_projv_subproof.
move => w_ HwE.
set M := \matrix_(_,_) _ => Hw.
set K := fixedField s.
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
 case/fixedFieldP: (prodv_line_coefK Huk) => _; apply.
 by apply: enum_valP.
split.
 apply: dimvS.
 apply/subv_sumP => i _.
 apply/subvP => v Hv.
 move/memv_prodv_line_coef: (Hv) ->.
 apply: memv_mul; last done.
 by case/prodv_line_coefK/fixedFieldP: Hv.
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
apply/fixedFieldP.
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
rewrite -comp_lfunE -aut_mul // (enum_val_nth 1%g) nth_index ?mulgKV //.
by rewrite mem_enum.
Qed.

Lemma maxDim_FixedField 
   (s : {set Coset}) :
   (forall i, i \in s -> (g_ i @: E)%VS = E) ->
   #|s|*\dim (fixedField s) <= \dim E.
Proof.
by case/dim_FixedField_subproof.
Qed.

Lemma dim_FixedField 
  (s : {group Coset}) :
  (forall i, i \in s -> (g_ i @: E)%VS = E) ->
  (#|s| * \dim (fixedField s) = \dim E)%N.
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
  'Aut(E / fixedField s)%g = s.
Proof.
move => HE.
symmetry.
apply/eqP.
rewrite eqEcard.
suff HsAut : (s \subset ('Aut(E / fixedField s))%g).
 rewrite HsAut.
 suff : #|('Aut(E / fixedField s))%g| * \dim (fixedField s) <= 
        #|s| * \dim (fixedField s).
  rewrite leq_mul2r.
  case/orP; last done.
  rewrite dimv_eq0 -subv0.
  move/subvP/(_ _ (mem1v _)).
  by rewrite memv0 -[_ == _]negbK oner_neq0.
 rewrite mulnC dim_FixedField // -galois_dim ?leqnn //.
 apply/galois_fixedField.
 have HFFE : (fixedField_aspace s <= E)%VS by apply: capvSl.
 split; first done.
 apply: subv_anti.
 by rewrite galoisAdjuctionA // fixedField_subset.
apply/subsetP => x.
case: (cosetP x) => f Hf -> Hfs.
rewrite mem_morphim //.
rewrite inE.
rewrite kAutE.
have Hff : f \in coset (kAutL E) f.
 by rewrite val_coset // rcoset_refl.
apply/andP; split.
 apply/kHomP; split; last by move => ? ? _ _; rewrite /= rmorphM.
 move => a /fixedFieldP [HaE /(_ _ Hfs) Ha].
 rewrite -[X in _ = X]Ha.
 move: {Ha} a HaE. 
 by apply/(aut_mem_eqP Hff (mem_repr_coset _)).
move: (HE _ Hfs) => HEfs.
rewrite -[X in (_ <= X)%VS]HEfs.
apply/subvP => _ /memv_imgP [a Ha ->].
apply/memv_imgP.
exists a; first done.
move: {Ha} a Ha.
by apply/(aut_mem_eqP Hff (mem_repr_coset _)).
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
apply/implyP; rewrite inE => /(subv_kAut HKM) Ha.
move/forallP/(_ a)/implyP: Hnorm; apply.
by rewrite inE.
Qed.

Lemma SubGroupGalois : 'Aut(E / M)%g \subset 'Aut(E / K)%g.
Proof.
rewrite quotientS //.
apply/subsetP => a.
rewrite !inE !kAutE.
case/andP => Ha ->.
rewrite andbT.
by apply: subv_kHom HKM Ha.
Qed.

Lemma FixedField_of_Aut : fixedField 'Aut(E / M)%g = M.
Proof.
by case/galois_fixedField: SubFieldGalois.
Qed.

Lemma OrderGaloisGroup : (#|'Aut(E / M)%g| * \dim(M) = \dim(E))%N.
Proof.
move/galois_dim: SubFieldGalois ->.
by rewrite mulnC.
Qed.

Hypothesis Hnorm : normalField K M.

Lemma NormalGalois : galois K M.
Proof.
rewrite /galois HKM Hnorm /= andbT.
apply/separableP => a Ha.
move/(subvP)/(_ _ Ha): HME => HaE.
case/and3P: HKE => _.
move/separableP => Hsep _.
by apply: Hsep.
Qed.

Let f (y : coset_of (kAutL E)) := (coset (kAutL M) (repr y)).

Let Aut_normal z : z \in 'Aut (E / K)%g -> val (repr z) \is a kAut K M.
Proof.
case/and3P: HKE => Hsub _ _.
rewrite aut_kAut // => /andP [HKz HEz].
apply/andP; split.
 apply/kHomP; split; last by move => ? ? _ _; rewrite /= rmorphM.
 by case/kHomP: HKz.
move/forallP/(_ (repr z))/implyP: Hnorm; apply.
rewrite inE kAutE subvf andbT.
apply/kHomP; split; last by move => ? ? _ _; rewrite /= rmorphM.
by case/kHomP: HKz.
Qed.

Let in_f x : x \in ('Aut(E / K))%g -> repr x \in f x.
move => Hfx.
rewrite val_coset; first by apply: rcoset_refl.
move/subsetP: (kAut_normal K M); apply.
rewrite inE.
by apply: Aut_normal.
Qed.

Let val_f x a : x \in ('Aut(E / K))%g -> a \in M ->
                repr x a = repr (f x) a.
Proof.
move => Hx.
move: a.
apply/(aut_mem_eqP (in_f Hx) (mem_repr_coset _)).
by rewrite eqxx.
Qed.

Let f_is_morph :
  {in 'Aut(E / K)%g &, {morph f : x y / (x * y)%g >-> (x * y)%g}}.
Proof.
move => x y Hx Hy /=.
apply/eqP/(aut_mem_eqP (in_f (groupM Hx Hy)) (mem_repr_coset _)) => b Hb.
have HbE : b \in E by move/subvP: HME; apply.
do 2 (rewrite aut_mul ?comp_lfunE; last done).
rewrite (val_f Hx) // (val_f Hy) // -(val_f Hx) //.
case/andP: (Aut_normal Hx) => _ /eqP <-.
by rewrite memv_img.
Qed.

Let fmorph := Morphism f_is_morph.

Let f_ker : ('ker fmorph = 'Aut(E / M))%g.
Proof.
apply/eqP.
rewrite eqEsubset.
apply/andP; split; apply/subsetP => x.
 rewrite inE.
 case/andP => Hx.
 rewrite 2!inE.
 move/(aut_mem_eqP (in_f Hx) (mem_repr_coset _)) => HxM.
 rewrite -[x]coset_reprK mem_quotient // inE.
 apply/andP; split.
  apply/kHomP; split; last by move => ? ? _ _; rewrite /= rmorphM.
  move => a Ha.
  by rewrite /= HxM // repr_coset1 id_lfunE.
 case/and3P: HKE => Hsub _ _.
 by move: Hx; rewrite aut_kAut //; case/andP.
move => Hx.
have HxE : x \in ('Aut(E / K))%g by move/subsetP: SubGroupGalois; apply.
apply/kerP; first done.
apply/eqP.
apply/(aut_mem_eqP (in_f HxE) (mem_repr_coset _)).
move => a Ha.
rewrite repr_coset1.
move: Hx; rewrite aut_kAut //; case/andP => [/kHomP [Hx _] _].
move:(Hx _ Ha) ->.
by rewrite id_lfunE.
Qed.

Let f_img : (fmorph @* 'Aut(E / K) = 'Aut(M / K))%g.
Proof.
apply/eqP.
rewrite eqEsubset.
apply/andP; split; apply/subsetP => x.
 case/imsetP => y.
 rewrite inE.
 case/andP => Hy _ ->.
 have HyKM := Aut_normal Hy.
 set z := Aut K M (repr y).
 have := (Aut_eq HKM HyKM).
 rewrite /=.
 move/(aut_mem_eqP (mem_repr_coset _) (in_f Hy))/eqP <-.
 by apply: Aut_aut.
move => Hx.
have HxKE : val (repr x) \is a kAut K E.
 apply/andP; split.
  apply/kHomP; split; last by move => ? ? _ _; rewrite /= rmorphM.
  by move: Hx; rewrite aut_kAut //; case/andP => /kHomP; case.
 case/and3P: HKE => _ _.
 move/forallP/(_ (repr x))/implyP; apply.
 rewrite inE kAutE subvf andbT.
 apply/kHomP; split; last by move => ? ? _ _; rewrite /= rmorphM.
 by move: Hx; rewrite aut_kAut //; case/andP => /kHomP; case.
have : (coset _ (repr x)) \in ('Aut(E / K))%g.
 apply: mem_quotient.
 by rewrite inE.
set y := coset _ (repr x) => Hy.
suff -> : x = (fmorph y) by apply: mem_morphim.
apply/eqP.
apply/aut_eqP.
move => a Ha.
rewrite /= -val_f //.
have Hxy : (repr x) \in y.
 rewrite val_coset; first by apply: rcoset_refl.
 move/subsetP: (kAut_normal K E); apply.
 by rewrite inE.
apply/(aut_mem_eqP Hxy (mem_repr_coset _)); first by rewrite eqxx.
by move/subvP: HME; apply.
Qed.

Lemma NormalGaloisGroup : ('Aut(E / M) <| 'Aut(E / K))%g.
Proof.
rewrite -f_ker.
apply: ker_normal.
Qed.

Lemma NormalGaloisGroupIso : ('Aut(E / K) / 'Aut(E / M) \isog 'Aut(M / K))%g.
Proof.
rewrite -f_ker -f_img.
apply: first_isog.
Qed.

End IntermediateField.

Section IntermediateGroup.

Variable g : {group coset_of (kAutL E)}.
Hypothesis Hg : g \subset 'Aut(E / K)%g.

Lemma SubGaloisField : (K <= fixedField g <= E)%VS.
Proof.
rewrite capvSl andbT.
apply/subvP => a Ha.
case/and3P: HKE => Hsub _ _.
apply/fixedFieldP; split.
 by move/subvP: Hsub; apply.
move => x Hxg.
move/subsetP/(_ _ Hxg): Hg.
rewrite aut_kAut //.
rewrite kAutE.
by case/andP; case/kHomP; move/(_ _ Ha).
Qed.

Lemma FixedFieldGalois : galois (fixedField g) E.
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
rewrite !inE.
by apply: subv_kAut.
Qed.

Lemma Aut_of_FixedField : 'Aut (E / fixedField g)%g = g.
Proof.
apply: Aut_FixedField => x Hx.
apply/eqP.
case/and3P: HKE => Hsub _ _.
move/subsetP/(_ _ Hx): Hg.
rewrite aut_kAut //.
by case/andP.
Qed.

Lemma FixedField_dim : (#|g| * \dim (fixedField g))%N = \dim E.
Proof.
apply: dim_FixedField => x Hx.
apply/eqP.
case/and3P: HKE => Hsub _ _.
move/subsetP/(_ _ Hx): Hg.
rewrite aut_kAut //.
by case/andP.
Qed.

Hypothesis Hnorm : 'Aut(E / K)%g \subset 'N(g)%g.

Lemma NormalGaloisField : galois K (fixedField g).
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
move: HaK; rewrite inE kAutE => /andP [HaK _].
pose x := coset (kAutL E) a.
have HaKE : a \in (kAut_in K E).
 rewrite inE.
 apply/andP; split; last by apply/eqP.
 apply/kHomP; split; last by move => ? ? _ _; rewrite /= rmorphM.
 by case/kHomP: HaK.
have Hx : x \in 'Aut(E / K)%g.
 apply: mem_morphim; last done.
 by move/subsetP: (kAut_normal K E); apply.
move/subsetP/(_ _ Hx)/normP: Hnorm => Hxg.
set Ma := (val a @: _)%VS.
have : galois Ma E.
 apply: SubFieldGalois.
  by rewrite -[X in (_ <= X)%VS]HaE limgS.
 apply/subvP => b Hb.
 rewrite /=.
 case/kHomP: HaK => /(_ _ Hb) <- _.
 rewrite memv_img //.
 by move/subvP: HKFF; apply.
rewrite /Ma.
case/galois_fixedField => _ <-.
case/galois_fixedField: FixedFieldGalois => _ <-.
apply/eqP; apply: f_equal; symmetry.
rewrite Aut_of_FixedField -[X in X = _]Hxg -[X in (X :^ x)%g]Aut_of_FixedField.
rewrite Aut_conjg //=; last first.
  case/and3P: HKE => KE _ _.
  by move/subsetP: (subv_aut (sub1v K) KE); apply.
suff -> : (repr x @: fixedField g = a @: fixedField g)%VS by done.
apply: limg_eq => z Hz.
rewrite inE in HaKE.
move/(aut_mem_eqP (mem_repr_coset x) (aut_refl HaKE)): (eqxx x); apply.
by move/subvP: HFFE; apply.
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
  have{map1q1z_z} hom_f0 : f0 \is a kHom 1 (Fadjoin 1 (inLz x)).
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
  rewrite all_rcons genField_rcons => /andP[rr1 ry] /poly_Fadjoin[pu r1pu ->].
  rewrite (kHom_horner homLf) -defLz; last exact: mem_genField; last first.
    by apply: polyOverS r1pu; apply/subvP/genFieldSr/allP.
  apply: rpred_horner.
    by apply/polyOverP=> i; rewrite coef_map /= defLz IHr1 ?(polyOverP r1pu).
  rewrite mem_genField // -root_prod_XsubC -(eqp_root def_pz).
  rewrite (kHom_rootK homLf) ?sub1v //; first by rewrite -defLz mem_genField.
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

Lemma splitting_field_galois p :
    p \is a polyOver 1%VS -> splittingFieldFor 1 p {:L} ->
    separablePolynomial p ->
  {normL : isNormalFieldExt L & galois normL 1 fullv}.
Proof.
move=> F0p splitLp sep_p; have nL := splitting_field_normal F0p splitLp.
exists nL; apply/and3P; split; first exact: subvf; last first.
  apply/normalFieldP=> y _; have [r /eqP->] := nL 1%AS y.
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
