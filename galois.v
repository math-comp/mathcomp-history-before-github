Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq tuple.
Require Import fintype finfun bigop ssralg poly polydiv.
Require Import zmodp vector algebra fieldext.
Require Import fingroup perm finset matrix mxalgebra.
Require Import separable choice.
Require Import quotient morphism.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Local Scope ring_scope.
Import GRing.Theory.

(******************************************************************************)

(* This should be moved to vector.v *)

Section Eigenspace.

Variable (K: fieldType) (V:vspaceType K) (f:'End(V)) (lambda:K).

Definition eigenspace := lker (f - lambda *: \1)%VS.

Lemma eigenspaceIn : forall x, (x \in eigenspace) = (f x == lambda *: x) .
Proof.
move => x.
by rewrite memv_ker add_lappE opp_lappE scale_lappE GRing.subr_eq0 unit_lappE.
Qed.

Lemma eigensubspaceImage :  forall vs, 
  (vs <= eigenspace)%VS -> (f @: vs <= vs)%VS.
Proof.
move => vs.
move/subvP => Hvs.
apply/subvP => x.
case/memv_imgP => y [Hy ->].
move/Hvs:(Hy).
rewrite eigenspaceIn.
move/eqP ->.
by apply: memvZl.
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
exists (lambda^-1 *: x).
have Hlx : (lambda^-1 *: x \in vs) by rewrite memvZ Hx orbT.
split=>//.
move/Hvs: Hlx.
rewrite eigenspaceIn.
move/eqP ->.
by rewrite GRing.scalerA GRing.divff // GRing.scale1r.
Qed.

End Eigenspace.

Section Galois.

Variable F0 : fieldType.
Variable L : fieldExtType F0.

Let F : {algebra L} := aspace1 _.

Section Definitions.

Variables (K E: {vspace L}) (f : 'End(L)).

(* Should I make this canonical by setting fixing (f @: E)^C ? *)
Definition kHom : pred 'End(L) :=
fun f => (K <= eigenspace f 1)%VS &&
  (all (fun v1 => all (fun v2 => f (v1 * v2) == f v1 * f v2) (vbasis E))
       (vbasis E)).

Lemma kHomP :
 reflect ((forall x, x \in K -> f x = x) /\
          (forall x y, x \in E -> y \in E -> f (x * y) = f x * f y))
 (kHom f).
Proof.
apply: (iffP andP); case; last first.
 move => HK HE.
 split.
  apply/subvP => v Hv.
  by rewrite eigenspaceIn scale1r HK.
 apply/allP => x; move/memv_basis => Hx.
 apply/allP => y; move/memv_basis => Hy.
 apply/eqP.
 by apply: HE.
move/subvP => HK.
move/all_nthP => HE.
split.
 move => x Hx.
 apply/eqP.
 by rewrite -{2}[x]scale1r -eigenspaceIn HK.
move => x y.
do 2 move/coord_basis ->.
rewrite -mulr_suml ![f _]linear_sum -mulr_suml.
apply: eq_bigr => i _ /=.
rewrite -!mulr_sumr linear_sum.
apply: eq_bigr => j _ /=.
rewrite !linearZ /= -!scaler_mull linearZ.
repeat apply: f_equal.
apply/eqP.
move: (ltn_ord i).
rewrite -{2}(size_tuple (vbasis _)).
move/(HE 0).
move/all_nthP.
apply.
by rewrite (size_tuple (vbasis _)).
Qed.

Lemma kHomFixedPoly : forall p, kHom f -> (polyOver K p) -> map_poly f p = p.
Proof.
move => p.
case/kHomP => HK _.
move/polyOverP => Hp.
apply/polyP => i.
by rewrite coef_map /= HK.
Qed.

Definition kAut : pred 'End(L) := fun f =>  kHom f && (f @: E == E)%VS.

Let kHomExtendF (x y z: L) :=
 (map_poly f (poly_for_Fadjoin E x z)).[y].

Let kHomExtendF_linear : forall x y,
 linear (kHomExtendF x y).
Proof.
move => x y k a b.
rewrite /kHomExtendF poly_for_linear raddfD horner_lin.
congr (_ + _).
rewrite -[(map_poly f (poly_for_Fadjoin E x a)).[y]]mul1r.
rewrite scaler_mull -horner_scaler.
congr (_.[_]).
apply/polyP => i.
rewrite !(coef_scaler, coef_map [linear of f]).
by rewrite -!scaler_mull !mul1r /= linearZ.
Qed.

Definition kHomExtend x y := lapp_of_fun (kHomExtendF x y).

Lemma kHomExtendE : forall x y z,
 kHomExtend x y z = (map_poly f (poly_for_Fadjoin E x z)).[y].
Proof. by move => x y z; rewrite lapp_of_funK. Qed.

End Definitions.

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

Variables (K E : {algebra L}) (f : 'End(L)).

Lemma kHom_inv : kHom K E f -> forall x, x \in E -> f x^-1 = (f x)^-1.
Proof.
case/kHomP => HK HE.
move => x Hx.
case (eqVneq x 0) => [->|Hx0]; first by rewrite linear0 invr0 linear0.
move: (Hx).
rewrite memv_inv.
move/(HE _ _ Hx).
rewrite divff // HK ?memv1 // => H1.
rewrite -[(f x)^-1]mulr1 H1 mulrA mulVf ?mul1r //.
move/eqP: H1.
apply: contraL.
move/eqP ->.
by rewrite mul0r nonzero1r.
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
by rewrite -unitfE unitrE -kHom_inv // -HE -?memv_inv // mulfV // HK // memv1.
Qed.

Lemma kHomRmorph_subproof : rmorphism (f \o (sa_val (als:=E))).
Proof.
case/kHomP: Hf => HK HE.
split; first by move => a b; rewrite /= linear_sub.
split; first by move => a b; rewrite /= HE // subaP.
by rewrite /= aunit_eq1 HK // memv1.
Qed.

Lemma kHom_root : forall p x, polyOver E p -> x \in E ->
 root p x -> root (map_poly f p) (f x).
Proof.
rewrite/root.
move => ? x.
case/polyOver_suba => p -> Hx.
set (f' := (RMorphism kHomRmorph_subproof)).
set (g := (RMorphism (sa_val_rmorph E))).
rewrite -[x]/(sa_val (Suba Hx)) -map_poly_comp ?linear0 //.
rewrite (horner_map f') horner_map.
move/eqP => /= ->.
by rewrite linear0.
Qed.

Lemma kHom_rootK : forall p x, polyOver K p -> x \in E ->
 root p x -> root p (f x).
Proof.
move => p x Hp Hx Hroot.
by rewrite -(kHomFixedPoly Hf Hp) kHom_root // (polyOver_subset HKE).
Qed.

Variables (x y : L).
Hypothesis Hy : root (map_poly f (minPoly E x)) y.

Lemma kHomExtendExt : forall z, z \in E -> kHomExtend E f x y z = f z.
Proof.
move => z Hz.
by rewrite kHomExtendE poly_for_K // map_polyC hornerC.
Qed.

Lemma kHomExtend_poly : forall p,
 polyOver E p -> kHomExtend E f x y (p.[x]) = (map_poly f p).[y].
Proof.
move => p Hp.
rewrite kHomExtendE.
move/(poly_for_modp x): (Hp) ->.
case/kHomP: Hf => HK HE.
have Hfmin : monic (map_poly f (minPoly E x)).
 by rewrite /monic lead_coef_map_eq;
  move/eqP: (monic_minPoly E x) ->;
  rewrite /= HK ?memv1 // nonzero1r.
rewrite (divp_mon_spec (map_poly f p) Hfmin) !horner_lin.
move/eqP: Hy ->.
rewrite mulr0 add0r.
case/polyOver_suba: Hp => p' ->.
case/polyOver_suba: (minPolyOver E x) => q' ->.
rewrite -map_modp -!map_poly_comp ?linear0 //=.
have Hmorph := kHomRmorph_subproof.
rewrite -[f \o sa_val_rmorphism E]/(GRing.RMorphism.apply (RMorphism Hmorph)).
by rewrite map_modp !map_polyE /= 2![map (_ \o _) _]map_comp.
Qed.

Lemma kHomExtendkHom : kHom K (Fadjoin E x) (kHomExtend E f x y).
Proof.
case/kHomP: Hf => HK HE.
move/subvP: HKE => HKE'.
apply/kHomP; split.
 move => z Hz.
 rewrite kHomExtendE.
 move/HKE'/poly_for_K: (Hz) ->.
 by rewrite (map_polyC [linear of f]) hornerC /= HK.
move => a b.
case/poly_Fadjoin => p [Hp ->].
case/poly_Fadjoin => q [Hq ->].
rewrite -horner_mul !kHomExtend_poly ?mulp_polyOver // -horner_mul.
congr (_.[_]).
apply/polyP => i.
rewrite coef_map !coef_mul /= linear_sum.
apply: eq_bigr => j _.
move/polyOverP: Hp => Hp.
move/polyOverP: Hq => Hq.
by rewrite !coef_map /= HE.
Qed.

End kHomExtend.

Lemma kAutE : forall (K E : {algebra L}) f,
  kAut K E f = kHom K E f && (f @: E <= E)%VS.
Proof.
move => K E f.
apply/andP/andP; case => Hhom.
 move/eqP ->; split => //.
 by rewrite subv_refl.
move => HfE; split => //.
by rewrite -(dimv_leqif_eq HfE) (kHom_dim Hhom).
Qed.
(*
Lemma kHomExtendAut : forall (K E J : {algebra L}) f,
  (K <= E)%VS -> (K <= J)%VS -> kHom K E f -> (f @: E <= J)%VS ->
  normal K J -> exists g, kAut K J g && (E <= lker (g - f))%VS.
Proof.
move => K E J f.
pose n := (\dim (J :\: E)%VS).
move : {2}(n.+1) (ltnSn n) => m.
rewrite /n {n}.
elim: m E f => [//|m IH] E f.
case (eqVneq (\dim (J :\: E)) 0%N).
 move/eqP.
 rewrite dimv_eq0 -subv_diffv0 => HJE _ _ _ Hf HfE _.
 exists f.
 rewrite kAutE subrr -lkerE lim0g eq_refl andbT (kHom_subv HJE) //=.
 by rewrite (subv_trans _ HfE) // limg_monotone.
move => Hdim Hm HKE HKJ Hf.
move/subvP => HfE HJ.
have [x [Hx Hx0]] : exists x, x \in (J :\: E)%VS /\ x != 0.
 exists (vpick (J :\: E)%VS); split; first by apply: memv_pick.
 by rewrite vpick0 -dimv_eq0.
move/subvP/(_ _ Hx): (diffvSl J E) => HxJ.
have HxE : x \notin E.
 move: Hx0.
 apply: contra.
 move/(conj Hx)/andP.
 rewrite -memv_cap -memv0.
 apply/subvP.
 rewrite subv0.
 apply/eqP.
 by apply: capv_diff.
have HminE : polyOver E (minPoly K x).
 by rewrite (polyOver_subset HKE) // minPolyOver.
have : (1 < size (minPoly E x)) by rewrite size_minPoly ltnS elementDegreegt0.
move: (minPoly_dvdp HminE (root_minPoly K x)).
case/polyOver_suba : HminE => p Hp.
case/polyOver_suba : (minPolyOver E x) => q Hq.
have Hmorph := (kHomRmorph_subproof Hf).
rewrite Hp Hq dvdp_map size_map_poly -(dvdp_map (RMorphism Hmorph)).
rewrite -(size_map_poly (RMorphism Hmorph)) !map_poly_comp ?linear0 // -Hp /=.
rewrite [map_poly f (minPoly K x)](kHomFixedPoly Hf) -?Hq; last first.
 by apply: minPolyOver.
clear p Hp q Hq Hmorph.
case: (HJ _ HxJ) => r; case/andP.
move/allP => Hr.
move/eqP => -> Hdiv Hsz.
have [y] : exists2 y, y \in J & root (map_poly f (minPoly E x)) y.
 clear -Hr Hdiv Hsz.
 elim: r Hr (map_poly f (minPoly E x)) Hdiv Hsz => [|z r IH] Hr p.
  rewrite big_nil.
  move/(size_dvdp (nonzero1r _)).
  rewrite size_poly1 leqNgt.
  by move/negbTE ->.
 rewrite big_cons mulrC.
 case (eqVneq (size (gcdp p ('X - z%:P))) 1%N).
  move/eqP/gaussp ->.
  apply: IH => a Ha.
  apply: Hr.
  by rewrite in_cons Ha orbT.
 rewrite -coprimep_def => Hcoprime _ _.
 exists z; first by apply Hr; rewrite in_cons eq_refl.
 move: Hcoprime.
 apply: contraR.
 rewrite root_factor_theorem.
 move/(conj (dvdpp ('X - z%:P)))/andP.
 rewrite -dvdp_gdco -?size_poly_eq0 ?size_factor //.
 case: gdcopP => q _.
 rewrite -size_poly_eq0 size_factor orbF.
 move/coprimepP => Hpq Hq Hzq.
 apply/coprimepP => d Hdp Hdz.
 apply: Hpq; last done.
 by rewrite (dvdp_trans Hdz).
move => HyJ Hy. 
case: (IH (Fadjoin E x) (kHomExtend E f x y)).
- rewrite ltnS in Hm.
  apply: (leq_trans _ Hm).
  rewrite -(ltn_add2l (\dim (J :&: Fadjoin E x))) dimv_cap_compl addnC.
  rewrite -(ltn_add2l (\dim (J :&: E))) addnA dimv_cap_compl addnC ltn_add2l.
  rewrite ltnNge.
  move: HxE.
  apply: contra.
  have: (J :&: E <= J :&: Fadjoin E x)%VS.
   by rewrite subv_cap capvSl /= (subv_trans (capvSr _ _)) // subsetKFadjoin.
  move/dimv_leqif_sup/geq_leqif ->.
  move/subvP/(_ x).
  rewrite !memv_cap memx_Fadjoin andbT.
  by case/(_ HxJ)/andP.
- by rewrite (subv_trans HKE) // subsetKFadjoin.
- done.
- by rewrite kHomExtendkHom.
- apply/subvP => ?.
  case/memv_imgP => ?; case.
  case/poly_Fadjoin => p [Hp ->] ->.
  rewrite (kHomExtend_poly Hf) //.
  apply: (memv_horner _ (subv_refl _)) => //.
  apply/polyOverP => i.
  rewrite coef_map HfE // memv_img //.
  by move/polyOverP: Hp.
- done.
move => g.
rewrite -lkerE -subv0.
case/andP => Hg.
move/subvP => Hker.
exists g.
rewrite Hg -lkerE -subv0.
apply/subvP => ?.
case/memv_imgP => z [Hz ->].
apply: Hker.
apply/memv_imgP.
exists z; split; first by rewrite memK_Fadjoin.
rewrite !add_lappE !opp_lappE.
congr (_ - _).
by rewrite kHomExtendExt.
Qed.
*)
Lemma LAut_lrmorph : forall f : 'End(L), 
  reflect (lrmorphism f) (kHom F (fullv L) f).
Proof.
move => f.
apply: (iffP (kHomP _ _ _)).
 case => HF HL.
 repeat split => //.
 - by apply: linear_sub.
 - by move => x y; apply: HL; rewrite memvf.
 - by rewrite HF // memv1.
 - by apply: linearZ.
move => Hf.
split; last by move => x y _ _; apply: (rmorphM (RMorphism Hf)).
move => ?; case/injvP => k ->.
rewrite linearZ /=.
(* There has got to be a better way than this *)
rewrite -[fun_of_lapp f]/(GRing.RMorphism.apply 
                          (RMorphism (GRing.LRMorphism.base Hf))).
by rewrite (rmorph1 (RMorphism Hf)).
Qed.

Hypothesis NormalFieldExt : forall x : L,
  exists r : seq L, minPoly F x == \prod_(y <- r) ('X - y%:P).

Definition LAut_enum :=
 let b := vbasis (fullv L) in
 let mkEnd (b' : seq L) := lapp_of_fun 
  (fun v : L => \sum_i coord b v i *: b'`_i) in
 undup (filter (kHom F (fullv L))
   (map mkEnd (foldr (allpairs cons) [:: [::]]
     (map (fun x => xchoose (NormalFieldExt x)) b)))).

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
exists (map f (vbasis (fullv L))).
 elim: (tval (vbasis (fullv L))) => [//|v vs IH].
 apply/allpairsP.
 exists (f v, map f vs); split => //.
 case: (xchooseP (NormalFieldExt v)).
 rewrite -root_prod_factors.
 move/eqP <-.
 by rewrite (kHom_rootK Hf) ?subvf ?minPolyOver ?memvf ?root_minPoly.
apply/eqP/eq_lapp => v.
rewrite lapp_of_funK; last first.
 move => x a b.
 rewrite linear_sum -big_split.
 apply: eq_bigr => i _ /=.
 by rewrite scalerA -scaler_addl coord_is_linear !ffunE.
have Hv := coord_basis (memvf v).
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

Canonical Structure map_poly_rmorphism := 
  fun f => RMorphism (LAut_is_rmorphism f).
Canonical Structure map_poly_lrmorphism := 
  fun f => LRMorphism (LAut_is_scalable f).

Definition comp_in_LAut : forall (f g : LAut),
 (ssval f \o ssval g)%VS \in LAut_enum.
Proof.
move => f g.
apply/LAut_is_enum.
split; last first.
 move => a b.
 by rewrite linearZ.
split.
 move => a b.
 by rewrite linear_sub.
by split;[move => a b|]; rewrite !lappE ?rmorph1 ?rmorphM.
Qed.

Definition id_in_LAut : \1%VS \in LAut_enum.
Proof.
apply/LAut_is_enum.
by repeat split;try (move => a b); rewrite !unit_lappE.
Qed.

Lemma LAut_ker0 : forall (f : LAut), lker (ssval f) = 0%:VS.
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
 (ssval f\^-1)%VS \in LAut_enum.
Proof.
move => f.
move/LAut_is_enum/LAut_lrmorph: (ssvalP f) => Hf.
apply/LAut_is_enum.
apply:(@can2_lrmorphism _ _ _ [lrmorphism of (ssval f)]).
 move => a.
 rewrite -[_ (_ a)]comp_lappE inv_lker0 ?unit_lappE // -subv0.
 by rewrite LAut_ker0 subv_refl.
move => a.
move:(memvf a).
rewrite -(addv_complf (ssval f @: fullv L)%VS).
move/memv_addP => [? [z []]].
case/memv_imgP => b [_ ->].
rewrite (_ : (ssval f @: fullv L)^C = 0%:VS)%VS; last first.
 apply/eqP.
 by rewrite -dimv_eq0 dimv_compl (kHom_dim Hf) dimvf subnn.
rewrite memv0.
move/eqP => -> ->.
rewrite addr0 -[_ (_ (_ b))]comp_lappE -[fun_of_lapp _ (_ b)]comp_lappE.
by rewrite -comp_lappA inv_lapp_def.
Qed.

Definition comp_LAut (f g : LAut) : LAut := SeqSub (comp_in_LAut f g).
Definition inv_LAut (f : LAut) : LAut := SeqSub (inv_in_LAut f).
Definition id_LAut : LAut := SeqSub id_in_LAut. 

Lemma comp_LAutA : associative comp_LAut.
Proof. move => f g h. apply: val_inj. apply: comp_lappA. Qed.

Lemma comp_1LAut : left_id id_LAut comp_LAut.
Proof. move => f. apply: val_inj. apply: comp_1lapp. Qed.

Lemma comp_LAutK : left_inverse id_LAut inv_LAut comp_LAut.
Proof.
move => f.
apply: val_inj.
by rewrite /= inv_lker0 // -subv0 LAut_ker0 subv_refl.
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

(* can I remove val below? *)
Lemma kAut_normal : forall K E : {algebra L},
 ([set x : LAut | kAut K E (val x)] \subset
   'N([set x : LAut | kHom K (fullv L) (val x)]))%g.
Proof.
move => K E.
apply/subsetP.
move => x.
rewrite !{1}in_set.
case/andP.
case/kHomP => Hx1 Hx2 _.
apply/subsetP => ?.
case/imsetP => y.
rewrite !in_set.
case/kHomP => Hy _ ->.
apply/kHomP; split; last by move => ? ? _ _; rewrite rmorphM.
move => a Ha.
rewrite -{2}[a](unit_lappE) -[\1%VS]/(val (1%g : LAut)) -(mulVg x).
rewrite !SubK !lappE /=.
apply: f_equal.
rewrite lappE.
apply Hy.
by rewrite Hx1.
Qed.

(* In most definitions I give the smaller field first, since the larger
   field can be seen as algebra over the smaller, and so in some moral sense
   the larger field depends on the smaller one.  However standard mathematical
   notation for Aut(E/K) puts the larger field first. *)
Definition Aut (E K : {vspace L}) :=
  ([set x : LAut | kAut K E (val x)] /
             [set x : LAut | kHom E (fullv L) (val x)])%g.

Reserved Notation "''Aut' ( A | B )" (at level 8, format "''Aut' ( A | B )").
Notation "''Aut' ( A | B )" := (Aut A B) : group_scope.

Lemma kAut_group_set : forall K E : {algebra L}, 
  group_set [set x : LAut | kAut K E (val x)].
Proof.
move => K E.
apply/group_setP; split.
 rewrite in_set kAutE.
 apply/andP; split; last by rewrite SubK lim1g subv_refl.
 apply/kHomP; split; last by move => ? ? _ _; rewrite rmorphM.
 move => a _.
 by rewrite SubK unit_lappE.
move => x y.
rewrite !in_set !kAutE.
case/andP; case/kHomP => Hx1 Hx2 Hx3.
case/andP; case/kHomP => Hy1 Hy2 Hy3.
apply/andP; split; last first.
 by rewrite SubK limg_comp (subv_trans _ Hx3) // limg_ker0 // LAut_ker0.
apply/kHomP; split; last by move => ? ? _ _; rewrite rmorphM.
move => a Ha.
by rewrite SubK lappE /comp Hy1 // Hx1.
Qed.

Lemma Aut_group_set : forall K E : {algebra L}, 
  group_set ('Aut  ( E | K ) )%g.
Proof.
move => K E.
rewrite /Aut.
apply/isgroupP.
by exists (group (kAut_group_set K E) / 
            [set x : LAut | kHom E (fullv L) (val x)])%G.
Qed.

Notation "''Aut' ( A | B )" := (group (Aut_group_set B A)) : subgroup_scope.

(* Test our ability to state parts of Galois's great theorem. *)
Hypothesis foo : forall (E Q K: {algebra L}), (K <= Q)%VS ->
  ('Aut (E | Q) \subset 'Aut (E | K))%g.
Hypothesis bar : forall (E Q K: {algebra L}),
  ('Aut (Q | K) \isog ('Aut (E | K) / 'Aut (E | Q)))%G.

(*
Definition FieldAutomorphism (E:{vspace L}) (f : 'End(L) ) : bool :=
 [&& (f @: E == E)%VS, (E^C <= eigenspace f 1)%VS &
 (all (fun v1 => all (fun v2 => f (v1 * v2) == f v1 * f v2) (vbasis E))
      (vbasis E))].

Definition FixedField E f := (E :&: @eigenspace F0 L f 1)%VS.

Implicit Types (E K:{algebra L}).

Lemma AutomorphMul : forall E f, FieldAutomorphism E f -> 
forall u v, u \in E -> v \in E -> f (u * v) = f u * f v.
Proof.
move => E f.
case/and3P => _ _.
move/all_nthP => fmult u v.
move/coord_basis => -> Hv.
rewrite -mulr_suml !linear_sum -mulr_suml.
apply: eq_bigr => i _.
move/coord_basis: Hv ->.
rewrite -mulr_sumr !linear_sum.
apply: eq_bigr => j _ /=.
rewrite ![f (_ *: _)]linearZ -scaler_mull linearZ -scaler_mulr linearZ.
rewrite -scaler_mull -scaler_mulr.
do 2 apply: f_equal.
apply/eqP.
move: (ltn_ord i).
rewrite -{2}(size_tuple (vbasis _)).
move/(fmult 0 _).
move/all_nthP.
apply.
by rewrite size_tuple.
Qed.

Lemma AutomorphismIsUnit : forall E f, 
 FieldAutomorphism E f -> lker f = 0%:VS.
Proof.
move => E f.
case/and3P => Hf1 Hf2 _.
apply/eqP.
rewrite -(capfv (lker f)) -dimv_eq0 -(eqn_addr (\dim (f @: (fullv _)))).
rewrite add0n limg_ker_dim -(addv_complf E) limg_add.
move/eqP: Hf1 ->.
rewrite (eigensubspaceImageEq _ Hf2) //.
apply: nonzero1r.
Qed.

Lemma idAutomorphism : forall E, FieldAutomorphism E \1%VS.
Proof.
move => E.
apply/and3P; split; do ? (apply/allP => i _ ;apply/allP => j _);
 rewrite ?unit_lappE ?lim1g //.
apply/subvP => v _.
by rewrite eigenspaceIn unit_lappE scale1r.
Qed.

Lemma compAutomorphism : forall E f g, 
 FieldAutomorphism E f ->  FieldAutomorphism E g ->
 FieldAutomorphism E (f \o g)%VS.
Proof.
move => E f g Ff Fg.
case/and3P: (Ff); move/eqP => Hf1; move/subvP => Hf2; move/eqP => _.
case/and3P: (Fg); move/eqP => Hg1; move/subvP => Hg2; move/eqP => _.
apply/and3P; split; do 2? apply/allP => ? ?;
  rewrite ?limg_comp ?comp_lappE /= ?Hg1 ?Hf1 //.
  apply/subvP => v Hv.
  rewrite eigenspaceIn comp_lappE /=.
  move/(_ _ Hv): Hg2; rewrite eigenspaceIn; move/eqP->.
  move/(_ _ Hv): Hf2; rewrite eigenspaceIn.
  by rewrite  GRing.scale1r.
by rewrite (AutomorphMul Fg);
 first (rewrite (AutomorphMul Ff) // -[g _ \in E]/(g _ \in a2vs E) -Hg1);
 do ? apply memv_img; apply: memv_basis.
Qed.

Lemma invAutomorphism : forall E f,
 FieldAutomorphism E f -> FieldAutomorphism E (f \^-1)%VS.
Proof.
move => E f Ff.
have kerf := AutomorphismIsUnit Ff.
case/and3P: (Ff); move/eqP => Hf1; move/subvP => Hf2; move/eqP => _.
have H1 : (f \^-1 @: E = E)%VS.
 apply/eqP.
 by rewrite -{1}Hf1 -limg_comp inv_lker0 ?kerf // lim1g.
apply/and3P; split.
- by rewrite H1.
- apply/subvP => v.
  move/Hf2=> Hv; rewrite eigenspaceIn GRing.scale1r in Hv.
  rewrite eigenspaceIn scale1r.
  rewrite -{1}(eqP Hv) /=.
  by rewrite -[(f \^-1)%VS (f _)](comp_lappE) inv_lker0 ?kerf // unit_lappE.
- rewrite <- Hf1.
  do 2 (apply/allP => ?; move/memv_basis;
        case/memv_imgP => ? [? ->]).
  rewrite -(AutomorphMul Ff) // -!{1}[(f \^-1)%VS (f _)](comp_lappE).
  by rewrite inv_lker0 ?kerf // !unit_lappE.
Qed.

Lemma FixedField_is_subfield : forall E f,
  FieldAutomorphism E f ->
  let K0 := FixedField E f in
  (has_aunit K0 && (K0 * K0 <= K0))%VS.
Proof.
move => E f Hf /=.
apply/andP; split.
 rewrite has_aunit1 // memv_cap.
 apply/andP; split.
  by apply: memv1.
 rewrite eigenspaceIn.
 apply/eqP.
 have Hf1 : f 1 != 0.
  by rewrite -memv_ker (AutomorphismIsUnit Hf) memv0 nonzero1r.
 apply: (mulfI Hf1).
 by rewrite -(AutomorphMul Hf) ?memv1 // scale1r !mulr1.
apply/prodvP => u v.
rewrite !memv_cap !eigenspaceIn !scale1r.
case/andP => uE; move/eqP => fu.
case/andP => vE; move/eqP => fv.
apply/andP; split.
 by rewrite memv_mul.
by rewrite (AutomorphMul Hf) // fu fv.
Qed.

Canonical Structure FixedField_subfield E f Hf : {algebra L} :=
 Eval hnf in ASpace (@FixedField_is_subfield E f Hf).

Lemma AutomorphsimEE_id : 
 forall E f, FieldAutomorphism E f -> FixedField E f = E -> f = \1%VS.
Proof.
move => E f.
case/and3P => _.
move/subvP => Hf _ HE.
apply/eqP.
apply/eq_lapp => v.
move: (memvf v).
rewrite unit_lappE -(addv_complf (FixedField E f)).
move/memv_addP => [va [vb [Hva Hvb ->]]].
move: Hva Hvb.
rewrite memv_cap HE.
rewrite linearD eigenspaceIn /=.
case/andP => _.
move/eqP ->.
move/Hf.
rewrite eigenspaceIn.
move/eqP ->.
by rewrite !scale1r.
Qed.
*)
End Galois.
