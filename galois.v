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
rewrite mulr_suml ![f _]linear_sum mulr_suml.
apply: eq_bigr => i _ /=.
rewrite !mulr_sumr linear_sum.
apply: eq_bigr => j _ /=.
rewrite !linearZ /= -!scalerAl linearZ.
repeat apply: f_equal.
apply/eqP.
move: (ltn_ord i).
rewrite -{2}(size_tuple (vbasis _)).
move/(HE 0).
move/all_nthP.
apply.
by rewrite (size_tuple (vbasis _)).
Qed.

Lemma kHom1 : kHom \1%VS.
Proof. apply/kHomP. by split; move => ? ?; rewrite !unit_lappE. Qed.

Variable (f : 'End(L)).

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
rewrite /kHomExtendF poly_is_linear raddfD horner_lin.
congr (_ + _).
rewrite -[(map_poly f (poly_for_Fadjoin E x a)).[y]]mul1r.
rewrite scalerAl -horner_scaler.
congr (_.[_]).
apply/polyP => i.
rewrite !(coefZ, coef_map [linear of f]).
by rewrite -!scalerAl !mul1r /= linearZ.
Qed.

Definition kHomExtend x y := lapp_of_fun (kHomExtendF x y).

Lemma kHomExtendE : forall x y z,
 kHomExtend x y z = (map_poly f (poly_for_Fadjoin E x z)).[y].
Proof. by move => x y z; rewrite lapp_of_funK. Qed.

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

Variables (K E : {algebra L}) (f : 'End(L)).

Lemma kHom_inv : kHom K E f -> forall x, x \in E -> f x^-1 = (f x)^-1.
Proof.
case/kHomP => HK HE.
move => x Hx.
case (eqVneq x 0) => [->|Hx0]; first by rewrite linear0 invr0 linear0.
move: (Hx).
rewrite memv_inv.
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
by rewrite -unitfE unitrE -kHom_inv // -HE -?memv_inv // mulfV // HK // mem1v.
Qed.

Lemma kHomRmorph_subproof : rmorphism (f \o (sa_val (als:=E))).
Proof.
case/kHomP: Hf => HK HE.
split; first by move => a b; rewrite /= linearB.
split; first by move => a b; rewrite /= HE // subaP.
by rewrite /= aunit_eq1 HK // mem1v.
Qed.

Lemma kHom_root : forall p x, polyOver E p -> x \in E ->
 root p x -> root (map_poly f p) (f x).
Proof.
rewrite/root.
move => ? x.
case/polyOver_suba => p -> Hx.
set (f' := (RMorphism kHomRmorph_subproof)).
set (g := (RMorphism (sa_val_rmorph E))).
rewrite -[x]/(sa_val (Suba Hx)) -map_comp_poly ?linear0 //.
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
  rewrite /= HK ?mem1v // oner_neq0.
rewrite (divp_eq (map_poly f p) (map_poly f (minPoly E x))) !horner_lin.
move/eqP: Hy ->.
rewrite mulr0 add0r.
case/polyOver_suba: Hp => p' ->.
case/polyOver_suba: (minPolyOver E x) => q' ->.
rewrite -map_modp -!map_comp_poly ?linear0 //=.
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
rewrite coef_map !coefM /= linear_sum.
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
apply/andP/andP; case => Hhom; first by move/eqP->.
move => HfE; split => //.
by rewrite -(dimv_leqif_eq HfE) (kHom_dim Hhom).
Qed.

Lemma LAut_lrmorph : forall f : 'End(L), 
  reflect (lrmorphism f) (kHom F (fullv L) f).
Proof.
move => f.
apply: (iffP (kHomP _ _ _)).
 case => HF HL.
 repeat split => //.
 - by apply: linearB.
 - by move => x y; apply: HL; rewrite memvf.
 - by rewrite HF // mem1v.
 - by apply: lmod_linearZ.
move => Hf.
split; last by move => x y _ _; apply: (rmorphM (RMorphism Hf)).
move => ?; case/injvP => k ->.
rewrite linearZ /=.
(* There has got to be a better way than this *)
rewrite -[fun_of_lapp f]/(GRing.RMorphism.apply 
                          (RMorphism (GRing.LRMorphism.base Hf))).
by rewrite (rmorph1 (RMorphism Hf)).
Qed.

(* To prove this hypothesis it is suffices to prove NormalFieldExt F.
   Actually, it suffices to prove 
    (forall x, x \in basis -> NormalFieldExt F x)
   for some basis of L.
   The proof that this suffices should eventually be done. *)

Definition isNormalFieldExt :=
    forall (K : {algebra L}) x,
  exists r, minPoly K x == \prod_(y <- r) ('X - y%:P).

Hypothesis NormalFieldExt : isNormalFieldExt.

Definition LAut_enum : seq 'End(L):=
 let b := vbasis (fullv L) in
 let mkEnd (b' : seq L) := lapp_of_fun 
  (fun v : L => \sum_i coord b v i *: b'`_i) in
 undup (filter (kHom F (fullv L))
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
exists (map f (vbasis (fullv L))).
 elim: (tval (vbasis (fullv L))) => [//|v vs IH].
 apply/allpairsP.
 exists (f v, map f vs); split => //.
 move: (xchooseP (NormalFieldExt F v)).
 rewrite -root_prod_factors.
 move/eqP <-.
 by rewrite (kHom_rootK Hf) ?subvf ?minPolyOver ?memvf ?root_minPoly.
apply/eqP/eq_lapp => v.
rewrite lapp_of_funK; last first.
 move => x a b.
 rewrite linear_sum -big_split.
 apply: eq_bigr => i _ /=.
 by rewrite scalerA -scalerDl coord_is_linear !ffunE.
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

Canonical Structure LAut_rmorphism := 
  fun f => RMorphism (LAut_is_rmorphism f).
Canonical Structure LAut_lrmorphism := 
  fun f => AddLRMorphism (LAut_is_scalable f).

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
 by rewrite linearB.
by split;[move => a b|]; rewrite !lappE ?rmorph1 ?rmorphM.
Qed.

Definition id_in_LAut : \1%VS \in LAut_enum.
Proof. apply/LAut_is_enum/LAut_lrmorph. by apply: kHom1. Qed.

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

(* the group operation is the categorical composition operation *)
Definition comp_LAut (f g : LAut) : LAut := SeqSub (comp_in_LAut g f).
Definition inv_LAut (f : LAut) : LAut := SeqSub (inv_in_LAut f).
Definition id_LAut : LAut := SeqSub id_in_LAut.

Lemma comp_LAutA : associative comp_LAut.
Proof. move => f g h. apply: val_inj. symmetry. apply: comp_lappA. Qed.

Lemma comp_1LAut : left_id id_LAut comp_LAut.
Proof. move => f. apply: val_inj. apply: comp_lapp1. Qed.

Lemma comp_LAutK : left_inverse id_LAut inv_LAut comp_LAut.
Proof.
move => f.
apply: val_inj.
(* TODO: abstract this into vector. v *)
apply/eqP/eq_lapp => v.
rewrite unit_lappE /=.
move: (memvf v).
rewrite -(addv_complf (val f @: (fullv L))%VS).
suff/eqP -> : ((val f @: fullv L)^C == 0%:VS)%VS.
 rewrite addv0.
 move/memv_imgP => [x [_ ->]].
 by rewrite -[X in X = _]comp_lappE -comp_lappA inv_lapp_def.
rewrite -dimv_eq0.
rewrite dimv_compl.
by rewrite limg_dim_eq ?dimvf ?subnn // capfv LAut_ker0.
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

Lemma kHomExtendLAut : forall (K E : {algebra L}) x,
  (K <= E)%VS -> kHom K E x ->
  exists y : LAut, kHom K (fullv L) (val y) && (E <= lker (val y - x))%VS.
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
 by rewrite Hx subrr -lkerE lim0g eqxx.
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
have HminE : polyOver E (minPoly K a).
 by rewrite (polyOver_subset HKE) // minPolyOver.
have : (1 < size (minPoly E a)) by rewrite size_minPoly ltnS.
move: (minPoly_dvdp HminE (root_minPoly K a)).
case/polyOver_suba : HminE => p Hp.
case/polyOver_suba : (minPolyOver E a) => q Hq.
have Hmorph := (kHomRmorph_subproof Hx).
rewrite Hp Hq dvdp_map size_map_poly -(dvdp_map (RMorphism Hmorph)).
rewrite -(size_map_poly (RMorphism Hmorph)) !map_comp_poly ?linear0 // -Hp /=.
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
  move/eqP/gausspl ->.
  by apply: IH => a Ha.
 rewrite -coprimep_def => Hcoprime _ _.
 exists z.
 move: Hcoprime.
 apply: contraR.
 rewrite root_factor_theorem.
 move/(conj (dvdpp ('X - z%:P)))/andP.
 rewrite -size2_dvdp_gdco -?size_poly_eq0 ?size_factor //.
 case: gdcopP => q _.
 rewrite -size_poly_eq0 size_factor orbF.
 move/coprimepP => Hpq Hq Hzq.
 apply/coprimepP => d Hdp Hdz.
 apply: Hpq; last done.
 by rewrite (dvdp_trans Hdz).
move => Hb.
case: (IH _ _ _ _ (kHomExtendkHom Hx HKE Hb)).
  rewrite ltnS in Hm.
  apply: (leq_trans _ Hm).
  rewrite -(ltn_add2l (\dim (Fadjoin E a))).
  rewrite dimv_compl subnKC; last by rewrite -dimvf dimvS // subvf.
  rewrite -(ltn_add2r (\dim E)) -addnA.
  rewrite dimv_compl subnK; last by rewrite -dimvf dimvS // subvf.
  rewrite ltnNge addnC leq_add2l.
  move: HaE.
  apply: contra.
  move/dimv_leqif_sup/geq_leqif: (subsetKFadjoin E a) ->.
  move/subvP/(_ a).
  rewrite memx_Fadjoin.
  by apply.
 by rewrite (subv_trans HKE) // subsetKFadjoin.
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

Lemma LAut_img_is_aspace (f : LAut) (K : {algebra L}) :
   let Kf := ((val f) @: K)%VS in
   has_aunit Kf && (Kf * Kf <= Kf)%VS.
Proof.
apply/andP; split.
 apply has_aunit1.
 by rewrite -(rmorph1 [rmorphism of (val f)]) memv_img // mem1v.
apply/prodvP => _ _ /memv_imgP [a [Ha ->]] /memv_imgP [b [Hb ->]].
by rewrite -rmorphM memv_img // memv_mul.
Qed.

Canonical Structure LAut_img_aspace a Z : {algebra L} := Eval hnf in
  ASpace (LAut_img_is_aspace a Z).

Definition LAut_FixedField (f : LAut) : {vspace L} :=
  eigenspace (val f) 1.

Lemma LAut_FixedField_is_aspace_subproof f : let FF := LAut_FixedField f in
  (has_aunit FF  && (FF * FF <= FF)%VS).
Proof.
apply/andP; split.
 by rewrite has_aunit1 // eigenspaceIn rmorph1 scale1r eqxx.
apply/prodvP => a b.
rewrite !eigenspaceIn !scale1r rmorphM /=.
by do 2 move/eqP ->.
Qed.

Canonical Structure LAut_FixedField_aspace f : {algebra L} :=
  ASpace (LAut_FixedField_is_aspace_subproof f).

Lemma LAut_independent (E : {algebra L}) n (f_ : 'I_n -> LAut)
  (c_ : 'I_n -> L) : (forall i, (val (f_ i) @: E)%VS = E) -> 
  uniq [seq (val (f_ i) \o projv E)%VS | i <- enum 'I_n] ->
  (forall i, c_ i \in E) ->
  (E <= lker (\sum_i (amull (c_ i) \o val (f_ i))))%VS ->
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
  rewrite -(lapp_of_funK (amull_linear_p (c_ i))).
  rewrite -[_ (_ 1)]comp_lappE -memv_ker.
  move/subvP: Hcfi; apply.
  by rewrite mem1v.
 move => j Hji.
 move: (Hci j).
 rewrite negb_and Hji negbK.
 move/eqP ->.
 apply/eqP/eq_lapp => a.
 rewrite !lappE /= /amull lapp_of_funK ?mul0r //.
 by apply: amull_linear_p.
have [a HaE] : exists2 a, a \in E & val (f_ j) a != val (f_ i) a.
 move: Hji.
 rewrite -(inj_eq (@ord_inj _)).
 rewrite -(nth_uniq \0%VS _ _ Huniq) 1?size_map ?size_enum_ord ?ltn_ord //.
 do 2 rewrite (nth_map ord0) ?size_enum_ord ?ltn_ord // nth_ord_enum.
 case/neq_lapp => a.
 rewrite !lappE => Ha.
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
   rewrite (@map_comp _ _ _ (fun i => val (f_ i) \o projv E)%VS (lift j)).
   rewrite map_inj_uniq.
    rewrite map_inj_uniq ?enum_uniq //.
    apply: lift_inj.
   move => k1 k2 /eqP Hk.
   apply/eqP.
   rewrite -[k1 == k2](nth_uniq \0%VS _ _ Huniq)
           1?size_map ?size_enum_ord ?ordP ?ltn_ord //.
   by do 2 rewrite (nth_map ord0) ?size_enum_ord ?ordP ?ltn_ord // nth_ord_enum.
 - move => k.
   apply: memv_mul; first by apply: Hc.
   apply: memv_sub; first by rewrite -(Hf j) memv_img.
   by rewrite -(Hf (lift j k)) memv_img.
 - set S := \sum_ _ _.
   have -> : (S = (\sum_i (amull ((c_ i) * (val (f_ j) a - val (f_ i) a))%R
                         \o val (f_ i))%VS)).
    rewrite (bigD1 j) //= {1}subrr mulr0.
    (* TODO abstract this into algebra.v *)
    have -> : (amull 0 = \0%VS :> 'End(L)).
     apply/eqP/eq_lapp => v.
     rewrite {1}lapp_of_funK; last by apply: amull_linear_p.
     by rewrite mul0r lappE.
    rewrite comp_0lapp add0r.
    set (G m := (amull (c_ m * ((ssval (f_ j)) a - (ssval (f_ m)) a))%R
                \o ssval (f_ m))%VS).
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
   rewrite sum_lappE.
   have HsumA : \sum_i (amull (c_ i * val (f_ j) a)%R \o val (f_ i))%VS v = 0.
    move/subvP/(_ _ Hv): Hsum.
    rewrite memv_ker.
    move/eqP/(f_equal (fun x => val (f_ j) a * x)).
    rewrite mulr0 => H0.
    rewrite -[X in _ = X]H0 sum_lappE mulr_sumr.
    apply: eq_bigr => m _.
    rewrite !{1}comp_lappE /=.
    do 2 (rewrite lapp_of_funK; last by apply: amull_linear_p).
    by rewrite [c_ m * _]mulrC mulrA.
   have HsumB : \sum_i (amull (c_ i * val (f_ i) a)%R \o val (f_ i))%VS v = 0.
    move/subvP/(_ _ (memv_mul HaE Hv)): Hsum.
    rewrite memv_ker.
    move/eqP => H0.
    rewrite -[X in _ = X]H0 sum_lappE.
    apply: eq_bigr => m _.
    rewrite !{1}comp_lappE /=.
    do 2 (rewrite lapp_of_funK; last by apply: amull_linear_p).
    by rewrite !rmorphM mulrA.
   rewrite -[X in (X - _)]HsumA -[X in (_ - X)]HsumB -sumrB.
   apply/eqP.
   apply: eq_bigr => m _.
   rewrite !{1}(opp_lappE,lappE) /=.
   do 3 (rewrite {1}lapp_of_funK; last by apply: amull_linear_p).
   by rewrite mulrBr mulrBl.
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

Lemma LAut_matrix_subproof (E : {algebra L}) n (f_ : 'I_n -> LAut) :
  (forall i, (val (f_ i) @: E)%VS = E) ->
  uniq [seq (val (f_ i) \o (projv E))%VS | i <- enum 'I_n] ->
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
 rewrite (@map_comp _ _ _ (fun i => val (f_ i) \o projv E)%VS
                          (fun i => rshift 1 i)).
 rewrite map_inj_uniq.
  rewrite (eq_map (@rshift1 _)).
  rewrite map_inj_uniq ?enum_uniq //.
  apply: lift_inj.
 move => k1 k2 /eqP Hk.
 apply/eqP.
 rewrite -[k1 == k2](nth_uniq \0%VS _ _ Huniq)
         1?size_map ?size_enum_ord ?ordP ?ltn_ord //.
 by do 2 rewrite (nth_map ord0) ?size_enum_ord ?ordP ?ltn_ord // nth_ord_enum.
move => w'_ Hw'.
set M' := \matrix_(_,_) _ => HM'.
pose x := \row_(j < n) (val (f_ 0) (w'_ j)).
pose c' := (x *m invmx M').
pose c_ := row_mx 1 (-c').
pose comb := \sum_i (amull (c_ 0 i) \o val (f_ i))%VS.
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
case (eqVneq (E :\: lker comb)%VS 0%:VS).
 move/eqP.
 rewrite -subv_diffv0.
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
rewrite !ord1 !mxE !eqxx /comb sum_lappE big_ord_recl {1}lappE.
rewrite /= lapp_of_funK; last by apply: amull_linear_p.
rewrite -[ord0](@lshift0 _ 0) row_mxEl mxE eqxx mul1r lshift0.
congr (_ + _).
apply eq_bigr => i _.
rewrite -rshift1 row_mxEr {1}lappE.
rewrite /= lapp_of_funK; last by apply: amull_linear_p.
congr (_ * _).
by rewrite !(row_mxEl, mxE).
Qed.

(* In most definitions I give the smaller field first, since the larger
   field can be seen as algebra over the smaller, and so in some moral sense
   the larger field depends on the smaller one.  However standard mathematical
   notation for Aut(E/K) puts the larger field first. *)
Definition Aut (E K : {vspace L}) :=
  ([set x : LAut | kAut K E (val x)] /
             [set x : LAut | kAut E (fullv L) (val x)])%g.

Reserved Notation "''Aut' ( A | B )"
  (at level 8, format "''Aut' ( A  |  B )").
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
 by rewrite SubK limg_comp (subv_trans _ Hy3) // limg_ker0 // LAut_ker0.
apply/kHomP; split; last by move => ? ? _ _; rewrite rmorphM.
move => a Ha.
by rewrite SubK lappE /comp Hy1 // Hx1.
Qed.

Canonical kAut_group K E := Eval hnf in group (kAut_group_set K E).

Lemma kAut_normal : forall K E : {algebra L},
 ([set x : LAut | kAut K E (val x)] \subset
   'N([set x : LAut | kAut E (fullv L) (val x)]))%g.
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
rewrite -{2}[a](unit_lappE) -[\1%VS]/(val (1%g : LAut)) -(mulVg x).
rewrite !SubK !lappE /= lappE [X in ((val x) X) = _]Hy //.
rewrite -Hx in Ha.
case/memv_imgP: Ha => [b [Hb ->]].
by rewrite -[X in X \in _]comp_lappE inv_lker0 ?unit_lappE // LAut_ker0.
Qed.

(* Move this to vector.v *)
Lemma eqvP (V : {vspace L}) (f g: 'End(L)) :
  reflect (forall a, a \in V -> f a = g a)
          (V <= lker (f - g))%VS.
Proof.
apply: (iffP idP).
 rewrite -lkerE.
 move/eqP => Hfg a /(memv_img (f - g)).
 rewrite Hfg memv0 lappE opp_lappE subr_eq0.
 by move/eqP.
move => Hfg.
apply/subvP => v Hv.
rewrite memv_ker lappE opp_lappE subr_eq0.
apply/eqP.
by apply: Hfg.
Qed.

Lemma Aut_eq (E : {algebra L}) 
  (x y : coset_of [set x : LAut | kAut E (fullv L) (val x)]) (f g : LAut) : 
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
 rewrite /= lappE /= Hh //.
move/coset_mem: Hf <-.
move/coset_mem: (Hg) => <- Hfg.
apply/eqP/coset_mem.
rewrite val_coset // mem_rcoset /=.
rewrite inE kAutE subvf andbT.
apply/kHomP; split; last by move => ? ? _ _; rewrite rmorphM.
move => a Ha.
rewrite comp_lappE /= Hfg //.
rewrite -[X in X = _]comp_lappE.
rewrite inv_lker0; last by rewrite LAut_ker0 eqxx.
by rewrite unit_lappE.
Qed.

Lemma Aut_mul (E : {algebra L})
 (x y : coset_of [set x : LAut | kAut E (fullv L) (val x)]) :
 forall a, a \in E -> val (repr (x*y)%g) a = val (repr y) (val (repr x) a).
Proof.
move => a Ha.
transitivity (val (repr x * repr y)%g a); last by rewrite /= comp_lappE.
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

Variables K E : {algebra L}.
Hypothesis HKE : (K <= E)%VS.

Lemma kAut_Aut f : kAut K E f -> exists2 x, x \in 'Aut(E | K)%g &
  forall g, g \in x -> forall a, a \in E -> f a = val g a.
Proof.
move => Hf.
case/andP: (Hf) => HfHom /eqP HfE.
case: (kHomExtendLAut HKE HfHom) => g /andP [HKg /eqvP HEgf].
have Hgf : (val g @: E <= E)%VS.
 rewrite -{2}HfE.
 apply/subvP => ? /memv_imgP [v [Hv ->]].
 move/HEgf: (Hv) ->.
 by rewrite memv_img.
exists (coset _ g).
 rewrite /Aut -imset_coset. 
 apply: mem_imset.
 by rewrite inE kAutE (kHom_subv (subvf _)).
move => h.
rewrite val_coset.
 case/rcosetP => {h} h Hh -> a HaE.
 rewrite -HEgf // comp_lappE.
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
 apply/subvP => ? /memv_imgP [a [Ha ->]].
 by rewrite comp_lappE /= Hf // -HxE; apply: memv_img.
apply/kHomP; split; last by move => ? ? _ _; rewrite rmorphM.
move => a Ha.
move/subvP/(_ _ Ha): HKE => HaE.
by rewrite comp_lappE /= Hf // Hx.
Qed.

End Automorphism.

(* kAut_pick is another way of phrasing kAut_Aut *)
Lemma kAut_pick_subproof (K E : {algebra L}) f :
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
Definition kAut_pick K0 (E : {algebra L}) f : 
  coset_of [set x : LAut | kAut E (fullv L) (val x)] :=
  if insub K0 is Some K 
     then xchoose (kAut_pick_subproof K E f)
     else (coset_one _).

Lemma kAut_pick_Aut (K E : {algebra L}) f : kAut_pick K E f \in 'Aut(E | K)%g.
Proof.
rewrite /kAut_pick valK.
by case/andP: (xchooseP (kAut_pick_subproof K E f)).
Qed.

Lemma kAut_pick_eq (K E : {algebra L}) f : (K <= E)%VS -> kAut K E f -> 
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

Lemma Aut_conjg (K E : {algebra L})
  (x : coset_of [set x : LAut | kAut E (fullv L) (val x)]) (f : LAut) :
  (K <= E)%VS -> (val f @: E = E)%VS -> f \in x -> 
  ('Aut(E | K) :^ x = 'Aut(E | (val f @: K)%VS))%g.
Proof.
move => HKE HfE Hfx.
apply/eqP.
have HKfE : (val f @: K <= E)%VS.
 apply/subvP => _ /memv_imgP [a [Ha ->]].
 rewrite -HfE memv_img //.
 by move/subvP: HKE; apply.
wlog suff : x f K HKE HfE HKfE Hfx / 
  (('Aut(E | K) :^ x)%g \subset ('Aut(E | (val f @: K)%VS))%g).
 move => Hsuff.
 rewrite eqEsubset Hsuff // -sub_conjgV -[X in _ \subset ('Aut(E | X))%g]lim1g.
 rewrite -[\1%VS]/(val (1 : LAut)%g) -[(1 : LAut)%g](mulgV f) limg_comp.
 apply: Hsuff; first done.
 - by rewrite -{1}HfE -limg_comp -[(_ \o _)%VS]/(val (f * f^-1)%g) mulgV lim1g.
 - by rewrite -limg_comp -[(_ \o _)%VS]/(val (f * f^-1)%g) mulgV lim1g.
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
 apply/subvP => _ /memv_imgP [a [Ha ->]].
 move: Ha.
 rewrite -{1}HfE.
 case/memv_imgP => b [Hb Hfb].
 rewrite Hfb Hfxb // -Aut_mul // -[X in _ \in X]HfE.
 apply/memv_imgP.
 exists (val (repr (x * (y * x^-1))%g) b).
 split; first by rewrite -[X in _ \in X]HxyxVE memv_img.
 rewrite Hfxb; last by rewrite -[X in _ \in X]HxyxVE memv_img.
 by rewrite -Aut_mul // mulgA mulgKV.
apply/kHomP; split; last by move => ? ? _ _; rewrite rmorphM.
move => _ /memv_imgP [a [Ha ->]].
case/kHomP: HxyxV => /(_ _ Ha) => HxyxVa _.
move: HxyxVa.
have HaE : a \in E by move/subvP: HKE; apply.
move/(f_equal (val f)).
rewrite Hfxb; last by rewrite -[X in _ \in X]HxyxVE // memv_img.
rewrite -Aut_mul // mulgA mulgKV Aut_mul; last done.
by rewrite -Hfxb.
Qed.

Lemma memv_aut (K E : {algebra L}) x a : (K <= E)%VS ->
 x \in 'Aut(E | K)%g -> a \in E -> val (repr x) a \in E.
Proof.
move => HKE.
case/(Aut_kAut HKE)/(_ (mem_repr_coset _))/andP => _ /eqP HE HaE.
by rewrite -[X in _ \in X]HE memv_img.
Qed.

Lemma uniq_aut (K E : {algebra L}) n f_ :
 (forall i, f_ i \in 'Aut(E | K)%g) ->
 uniq [seq f_ i | i <- enum 'I_n] ->
 uniq [seq (val (repr (f_ i)) \o projv E)%VS |  i <- enum 'I_n].
Proof.
move => Hf.
set (s := [seq f_ i |  i <- enum 'I_n]).
set (g (x : coset_of [set x : LAut | kAut E (fullv L) (val x)]):= 
     (val (repr x) \o projv E)%VS).
suff Hs : {in s &, injective g} by rewrite -(map_inj_in_uniq Hs) -map_comp.
move=> x y Hx Hy /= Hg.
apply/eqP/(Aut_eq (mem_repr_coset _) (mem_repr_coset _)) => a /projv_id <-.
by rewrite -[_ (projv E a)]comp_lappE [(_ \o _)%VS]Hg comp_lappE.
Qed.

Definition FixedField (E : {vspace L})
  (s : {set coset_of [set x : LAut | kAut E (fullv L) (val x)]}) :=
  (E :&: \bigcap_( i \in cover [set (set_of_coset x) | x <- s])
          (LAut_FixedField i))%VS.

Lemma FixedFieldP (E : {algebra L})
   (s : {set coset_of [set x : LAut | kAut E (fullv L) (val x)]}) a :
 reflect (a \in E /\ forall x, (x \in s) -> (val (repr x) a = a))
         (a \in FixedField s).
Proof.
rewrite /FixedField big_trivIset; last first.
 apply/trivIsetP => ? ? /imsetP [x Hx ->] /imsetP [y Hy ->].
 by apply: contraR => /pred0Pn [f /andP [/coset_mem <- /coset_mem <-]].
rewrite memv_cap.
case HaE : (a \in E); last first.
 apply: ReflectF.
 by case.
apply: (iffP (subv_bigcapP _ _ _)).
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

Lemma galoisAdjuctionA (K E : {algebra L}) :
  (K <= E)%VS ->
  (K <= FixedField ('Aut(E | K))%g)%VS.
Proof.
move => HKE.
apply/subvP => a HaK.
apply/FixedFieldP; split; first by move/subvP: HKE; apply.
move => x Hx.
by move: (Aut_kAut HKE Hx (mem_repr_coset _)) => /andP [/kHomP [->]].
Qed.

Lemma FixedField_is_aspace_subproof  (E : {algebra L})
   (s : {set coset_of [set x : LAut | kAut E (fullv L) (val x)]}) :
  let FF := FixedField s in
  (has_aunit FF  && (FF * FF <= FF)%VS).
Proof.
rewrite /FixedField -big_filter.
move : (filter _ _) => {s} r.
elim : r E => [|r rs IH] E; first by rewrite big_nil capvf; case: E.
rewrite big_cons capvA.
by apply: IH.
Qed.

Canonical Structure FixedField_aspace (E : {algebra L})
   (s : {set coset_of [set x : LAut | kAut E (fullv L) (val x)]}) : {algebra L}
   := ASpace (FixedField_is_aspace_subproof s).

Lemma FixedField_subset (E : {algebra L})
   (s1 s2 : {set coset_of [set x : LAut | kAut E (fullv L) (val x)]}) :
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

Variables (K E : {algebra L}).

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
 by rewrite -[X in _ \in X]HE memv_img.
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
 by rewrite -[X in _ \in X]HE memv_img.
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
 forallb x : LAut, kHom K (fullv L) (val x) ==> ((val x) @: E == E)%VS.

(* Move this to poly.v *)
Lemma eqpMP : forall (R : idomainType) (p q : {poly R}),
  monic p -> monic q -> (p %= q) = (p == q).

Proof.
move => R p q Hp Hq.
case: eqP; first by move ->; rewrite eqpxx.
move => neqpq.
apply/negbTE/negP.
move/eqpP => [[a b]] /= /andP [Ha Hb] Hpq.
apply: neqpq.
have : a%:P != 0 by rewrite polyC_eq0.
move/mulfI; apply.
rewrite !mul_polyC Hpq.
congr (_ *: _).
move: (f_equal (fun f => lead_coef f) Hpq).
by rewrite -!mul_polyC !lead_coef_mul_monic // !lead_coefC.
Qed.

Lemma normalP : forall (K E : {algebra L}), 
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
 case/memv_imgP => {a} a [Ha ->].
 case: (Hnorm _ Ha) => r.
 move/allP => Hr Har.
 apply: Hr.
 rewrite -root_prod_factors.
 move/(f_equal (map_poly (fun_of_lapp (val x)))): (Har).
 rewrite (kHomFixedPoly Hx) ?minPolyOver //= Har => ->.
 by rewrite root_map_poly // -Har root_minPoly.
move => Hnorm a HaE.
case: (NormalFieldExt K a) => r.
move/eqP => Hr.
exists r => //.
apply/allP => b.
rewrite -root_prod_factors -Hr -[minPoly K a]polyseqK.
rewrite -[polyseq _](@map_id_in _ [rmorphism of (val (1:LAut))%g]); last first.
 move => z _ /=.
 by rewrite unit_lappE.
rewrite -map_polyE => Hab.
set y := kHomExtend K \1%VS a b.
rewrite -[b]hornerX -(map_polyX [rmorphism of (val (1:LAut))%g]).
have H1 : kHom K K (val (1:LAut))%g.
 apply/kHomP.
 split; last by move => ? ? _ _; rewrite rmorphM.
 move => x _ /=.
 by rewrite unit_lappE.
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
rewrite -subr_eq0 -opp_lappE -add_lappE -memv_ker.
move/subvP: Hzy; apply.
by rewrite memx_Fadjoin.
Qed.

Definition galois K E := [&& (K <= E)%VS, separable K E & normal K E].

Lemma separable_dim : forall (K : {algebra L}) x, separableElement K x ->
  normal K (Fadjoin K x) -> elementDegree K x = #|'Aut(Fadjoin K x | K)%g|.
Proof.
move => K x Hsep.
set E := Fadjoin K x.
case/normalP/(_ _ (memx_Fadjoin K x)) => r.
move/allP => Hr Hmin.
apply/succn_inj.
rewrite -size_minPoly Hmin size_prod_factors.
congr (_.+1).
apply/eqP.
move: Hsep.
rewrite /separableElement Hmin separable_factors => Huniq.
rewrite eqn_leq.
apply/andP; split; last first.
 rewrite cardE.
 pose f (y : coset_of [set g : LAut | kAut E (fullv L) (val g)]) :=
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
 rewrite -root_prod_factors -Hmin /f.
 case/andP: (Aut_kAut (subsetKFadjoin _ _) Ha (mem_repr_coset _)).
 move/(kHom_rootK)/(_ (subsetKFadjoin _ _) _ _
                      (minPolyOver K x) (memx_Fadjoin _ _)) => Hroot _.
 by rewrite Hroot // root_minPoly.
pose f y := kAut_pick K (Fadjoin_aspace K x) (kHomExtend K \1%VS x y).
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
have Hroot : forall c, c \in r -> root (map_poly \1%VS (minPoly K x)) c.
 move => c Hc.
 rewrite (eq_map_poly (fun x => unit_lappE x)).
 rewrite map_polyE map_id polyseqK.
 by rewrite Hmin root_prod_factors.
have Hpoly : forall c, c \in r -> c = (kHomExtend K \1%VS x c) x.
 move => c Hc.
 rewrite -{2}[x]hornerX.
 rewrite (kHomExtend_poly (kHom1 K K) (Hroot _ Hc) (polyOverX _)).
 rewrite (eq_map_poly (fun x => unit_lappE x)).
 rewrite map_polyE map_id polyseqK.
 by rewrite hornerX.
rewrite (Hpoly _ Ha) (Hpoly _ Hb) {Hpoly} -/fa -/fb.
pose g := val (repr (kAut_pick K (Fadjoin_aspace K x) fa)).
have HAuta : kAut K (Fadjoin K x) fa.
 rewrite kAutE (kHomExtendkHom (kHom1 K K) (subv_refl K) (Hroot _ Ha)).
 apply/subvP => ? /memv_imgP [? [/poly_Fadjoin [p [Hp ->]] ->]].
 rewrite (kHomExtend_poly (kHom1 K K) (Hroot _ Ha) Hp).
 rewrite (eq_map_poly (fun x => unit_lappE x)).
 rewrite map_polyE map_id polyseqK.
 case/poly_Fadjoin: (Hr _ Ha) => q [Hq ->].
 by rewrite -horner_comp_poly mempx_Fadjoin ?compose_polyOver.
transitivity (g x).
 apply: (kAut_pick_eq (subsetKFadjoin K x) HAuta).
  by apply: mem_repr_coset.
 by apply: memx_Fadjoin.
rewrite /g Hab.
symmetry.
apply: (kAut_pick_eq (subsetKFadjoin K x)); first last.
  by apply: memx_Fadjoin.
 by apply: mem_repr_coset.
rewrite kAutE (kHomExtendkHom (kHom1 K K) (subv_refl K) (Hroot _ Hb)).
apply/subvP => ? /memv_imgP [? [/poly_Fadjoin [p [Hp ->]] ->]].
rewrite (kHomExtend_poly (kHom1 K K) (Hroot _ Hb) Hp).
rewrite (eq_map_poly (fun x => unit_lappE x)).
rewrite map_polyE map_id polyseqK.
case/poly_Fadjoin: (Hr _ Hb) => q [Hq ->].
by rewrite -horner_comp_poly mempx_Fadjoin ?compose_polyOver.
Qed.

Lemma galois_dim : forall (K E : {algebra L}), galois K E ->
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
Lemma GaloisUnfixedField (K E : {algebra L}) : galois K E ->
 forall a, a \in E -> a \notin K -> exists x, (x \in 'Aut(E | K)%g) && 
   (val (repr x) a != a).
Proof.
case/and3P => [HKE Hsep Hnorm] a HaE.
rewrite elemDeg1 -eqSS -size_minPoly.
case/normalP/(_ a HaE): (Hnorm) (root_minPoly K a) => r Hr Hmin.
rewrite Hmin root_prod_factors => Har.
move: (size_prod_factors r) => Hsz1 Hsz2.
have [b Hbr Hba] : exists2 b, b \in r & b != a.
 move/separableP/(_ _ HaE): Hsep.
 rewrite /separableElement Hmin separable_factors.
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
have: kHom K (Fadjoin K a) (kHomExtend K \1%VS a b).
 rewrite kHomExtendkHom ?kHom1 ?subv_refl //.
 rewrite (eq_map_poly (fun x => unit_lappE x)) map_polyE map_id polyseqK.
 by rewrite Hmin root_prod_factors.
case/(kHomExtendLAut (subsetKFadjoin K a)) => f /andP [HKf /eqvP Hf].
move/forallP/(_ f)/implyP/(_ HKf): Hnorm => HfE.
have: kAut K E (val f).
 by rewrite /kAut HfE andbT (kHom_subv _ HKf) // subvf.
case/(kAut_Aut HKE) => x HxAut /(_ _ (mem_repr_coset _)) Hx.
exists x.
rewrite HxAut -Hx // Hf ?memx_Fadjoin //.
rewrite -{2}[a]hornerX.
have Hminb : root (map_poly \1%VS (minPoly K a)) b.
 rewrite (eq_map_poly (fun x => unit_lappE x)) map_polyE map_id polyseqK.
 by rewrite Hmin root_prod_factors.
rewrite (kHomExtend_poly (kHom1 K K) Hminb) ?polyOverX //.
rewrite (eq_map_poly (fun x => unit_lappE x)) map_polyE map_id polyseqK.
by rewrite hornerX.
Qed.

Lemma galois_factors_subproof (K E : {algebra L}) : (K <= E)%VS ->
 (forall a, a \in E -> a \notin K -> exists x, (x \in 'Aut(E | K)%g) && 
   (val (repr x) a != a)) ->
 (forall a, a \in E -> 
   exists r, [/\
     r \subset 'Aut(E | K)%g,
     uniq (map (fun i : coset_of [set x : LAut | kAut E (fullv L) (val x)] =>
                         ((val (repr i)) a)) r) &
     minPoly K a = \prod_(i <- r)('X - (val (repr i) a)%:P)]).
Proof.
pose f (j : L) := ('X - j%:P).
move => HKE Hgal a HaE.
pose h (i : coset_of [set x : LAut | kAut E (fullv L) (val x)])
      := ((val (repr i)) a).
suff : forall n, n.+1 < size (minPoly K a) -> 
        exists r, let r' := 
           map (fun i : coset_of [set x : LAut | kAut E (fullv L) (val x)] =>
                         ((val (repr i)) a)) r 
         in [/\ r \subset 'Aut(E | K)%g,  uniq r',
                (size r') = n.+1 &
                \prod_(i <- r')('X - i%:P) %| minPoly K a].
 rewrite size_minPoly.
 case/(_ _ (leqnn _)) => r [Haut Hr Hnr Hmin].
 exists r; split => //.
 apply/eqP.
 rewrite -(big_map h predT f).
 rewrite -eqpMP ?monic_minPoly ?monic_prod_factors //.
 rewrite eqp_sym -dvdp_size_eqp // size_prod_factors.
 by rewrite size_minPoly Hnr.
elim => [|n IH] Hn.
 exists [:: 1%g]; split => //; last first.
  rewrite big_cons big_nil mulr1 dvdp_factorl repr_coset1 /= unit_lappE.
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
rewrite negb_or -size_poly_eq1 {2}/g size_prod_factors Hnr andbT.
rewrite -(dvdp_size_eqp Hmin) {1}/g size_prod_factors Hnr neq_ltn Hn.
case/(_ isT)/allPn => c Hcg HcK.
have/allP : polyOver E g.
 rewrite /g big_map.
 rewrite (big_nth 1%g) big_mkord.
 apply: prodp_polyOver => i _.
 rewrite polyOver_factor //.
 move/subsetP/allP/(all_nthP 1%g)/(_ _ (@ltn_ord _ i))/(Aut_kAut HKE): Haut.
 case/(_ _ (mem_repr_coset _))/andP => _ /eqP => HE.
 by rewrite -[X in (_ \in X)]HE memv_img.
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
 rewrite -eqpMP ?monic_prod_factors // -dvdp_size_eqp.
  by rewrite !size_prod_factors size_map.
 apply: uniq_roots_dvdp.
  apply/allP => b Hb.
  rewrite root_prod_factors.
  by apply: Hsubset.
 rewrite uniq_rootsE map_inj_uniq //.
 (* TODO: abstract this *)
 move => b d Hbd.
 rewrite -[b](unit_lappE) -[d](unit_lappE).
 move/eqP/inv_lker0: (LAut_ker0 (repr x)) <-.
 by rewrite !comp_lappE /= Hbd.
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

Lemma galois_factors (K E : {algebra L}) : 
 reflect ((K <= E)%VS /\ (forall a, a \in E -> 
   exists r, [/\
     r \subset 'Aut(E | K)%g,
     uniq (map (fun i : coset_of [set x : LAut | kAut E (fullv L) (val x)] =>
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
 pose h (i : coset_of [set x : LAut | kAut E (fullv L) (val x)])
       := ((val (repr i)) a).
 by rewrite /separableElement Hmin -(big_map h predT f) separable_factors.
apply/normalP => a Ha.
case/H: (Ha) => r [/subsetP Haut Hr Hmin].
pose h (i : coset_of [set x : LAut | kAut E (fullv L) (val x)])
      := ((val (repr i)) a).
exists (map h r); last by rewrite big_map.
apply/allP => ? /mapP [x Hx ->].
case/andP: (Aut_kAut HKE (Haut _ Hx) (mem_repr_coset _)) => _.
move/eqP <-.
by rewrite memv_img.
Qed.

Lemma galois_fixedField (K E : {algebra L}) : reflect
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

Lemma mem_galoisTrace (K E : {algebra L}) a :
 galois K E -> a \in E -> galoisTrace K E a \in K.
Proof.
case/galois_fixedField => HKE HK.
rewrite -{2}HK.
by apply: autTraceFixedField.
Qed.

Lemma mem_galoisNorm (K E : {algebra L}) a :
 galois K E -> a \in E -> galoisNorm K E a \in K.
Proof.
case/galois_fixedField => HKE HK.
rewrite -{2}HK.
by apply: autNormFixedField.
Qed.

Lemma HilbertsTheorem90 (K E : {algebra L}) x a :
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
 rewrite rmorph_prod /c_ big_ord_recl expg0 repr_coset1 unit_lappE mulKf //.
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
have Huniq : uniq [seq (val (f_ (nat_of_ord i)) \o projv E)%VS| i <- enum 'I_n].
 apply: (@uniq_aut K) => [i |]; first by rewrite -Hx mem_cycle.
 by rewrite map_inj_uniq ?enum_uniq.
have Hexistb : (existsb i : 'I_n, c_ i != 0).
 apply/existsP.
 exists (Ordinal (order_gt0 _)).
 by rewrite /c_ big_ord0 oner_neq0.
pose Sigma := \sum_(i : 'I_n) (amull (c_ i) \o val (f_ i))%VS.
have: ((E <= lker Sigma)%VS -> forallb i : 'I_n, c_ i == 0).
 move => HE.
 apply/forallP => i.
 apply/eqP.
 apply:(LAut_independent (fun i : 'I_n => HxE i) Huniq (fun i : 'I_n => HcE i)).
 done.
move/contra/(_ Hexistb).
rewrite subv_diffv0.
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
 rewrite sum_lappE.
 apply: memv_suml => i _.
 rewrite comp_lappE /= lapp_of_funK; last by apply: amull_linear_p.
 by rewrite memv_mul // -[X in _ \in X](HxE i) memv_img.
apply: (canRL (mulfK _)); first by rewrite fmorph_eq0.
rewrite sum_lappE rmorph_sum mulr_sumr /n -(prednK (order_gt0 x)).
rewrite big_ord_recr /=; symmetry; rewrite addrC big_ord_recl.
congr (_ + _).
 do 2 (rewrite comp_lappE /= lapp_of_funK; last by apply: amull_linear_p).
 rewrite [c_ 0%N]big_ord0 /f_ expg0 repr_coset1 unit_lappE.
 rewrite rmorphM /= -Aut_mul //.
 rewrite -expgSr (prednK (order_gt0 x)) expg_order repr_coset1 unit_lappE.
 rewrite rmorph_prod -{1}Hnorm mulrA.
 congr (_ * _).
 rewrite /galoisNorm.
 rewrite -Hx.
 suff Hbij : {on [pred i | i \in <[x]>%g],
                  bijective (fun i : 'I_n => (x ^+ i)%g)}.
  rewrite (reindex _ Hbij) (eq_bigl _ _ (fun i : 'I_n => mem_cycle x i)).
  rewrite -[n](prednK (order_gt0 x)) big_ord_recl.
  rewrite expg0 repr_coset1 unit_lappE.
  congr (_ * _).
  apply: eq_bigr => i _.
  by rewrite /= -Aut_mul // -expgSr.
 rewrite -[n](prednK (order_gt0 x)).
 (* This is way harder than it ought to be. *)
 exists (fun y => inord (index y (map (fun i : 'I_#[x]%g.-1.+1 => (x ^+ i)%g)
                                 (enum predT)))).
  move => i /= Hi.
  have -> : (x ^+ i)%g = nth 1%g [seq (x ^+ (nat_of_ord i0))%g
                                 | i0 <- enum 'I_#[x]%g.-1.+1] i.
   rewrite (nth_map ord0); first by rewrite [nth _ _ _]nth_ord_enum.
   by rewrite size_enum_ord; case: i {Hi}.
  rewrite index_uniq; first by apply: inord_val.
   by rewrite size_map size_enum_ord; case: i {Hi}.
  rewrite map_inj_uniq; first by apply: enum_uniq.
  by rewrite (prednK (order_gt0 x)).
 move => y /=.
 rewrite inE /= => /cyclePmin [i].
 rewrite -{1}(prednK (order_gt0 x)) => Hi.
 rewrite -{1}(inordK Hi) => ->.
 congr (x ^+ inord _)%g.
 set j := inord _.
 have -> : (x ^+ j)%g = nth 1%g [seq (x ^+ (nat_of_ord i0))%g
                                | i0 <- enum 'I_#[x]%g.-1.+1] j.
   rewrite (nth_map ord0); first by rewrite [nth _ _ _]nth_ord_enum.
   by rewrite size_enum_ord; case: j.
 rewrite index_uniq; first by apply: inordK.
  by rewrite size_map size_enum_ord.
 rewrite map_inj_uniq; first by apply: enum_uniq.
 by rewrite (prednK (order_gt0 x)).
apply: eq_bigr => i _.
do 2 (rewrite comp_lappE /= lapp_of_funK; last by apply: amull_linear_p).
rewrite rmorphM mulrA.
rewrite rmorph_prod [c_ _]big_ord_recl expg0 repr_coset1 unit_lappE.
congr (_ * _ * _).
 apply eq_bigr => j _.
 by rewrite /= -Aut_mul // -expgSr.
by rewrite /= -Aut_mul // -expgSr.
Qed.

Section GaloisDim.

Variable E : {algebra L}.

Let Coset :=
 [finGroupType of coset_of [set x : LAut | kAut E (fullv L) (val x)]].

Let g_ (i : Coset) := val (repr i).

Lemma uniq_projv_subproof 
  (s : {set Coset}) :
  uniq [seq (g_ (enum_val i) \o (projv E))%VS | i <- enum 'I_#|s|].
Proof.
rewrite map_inj_uniq; first by rewrite enum_uniq.
move => i j /= /eqP/eq_lapp Hij.
apply: enum_val_inj.
apply/eqP/(Aut_eq (mem_repr_coset _) (mem_repr_coset _)) => a /projv_id <-.
by rewrite -[_ (_ a)]comp_lappE Hij comp_lappE.
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
rewrite [(_ * _)%N](_: _ = \dim (\sum_(i < #|s|) K * (w_ i)%:VS)); last first.
 suff/directvP -> : (directv (\sum_i (K * (w_ i)%:VS))).
  rewrite -{1}[#|s|]subn0 -sum_nat_const_nat big_mkord.
  apply: eq_bigr => i _.
  rewrite /= dim_prodvf //.
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
  rewrite mulmx0 mulKmx // (memv_prodv_inj_coef (Hu i isT)).
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
  by rewrite -rmorphM mulrC -(memv_prodv_inj_coef Huk).
 case/FixedFieldP: (prodv_inj_coefK Huk) => _; apply.
 by apply: enum_valP.
split.
 apply: dimvS.
 apply/subv_sumP => i _.
 apply/subvP => v Hv.
 move/memv_prodv_inj_coef: (Hv) ->.
 apply: memv_mul; last done.
 by case/prodv_inj_coefK/FixedFieldP: Hv.
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
rewrite repr_coset1 unit_lappE => <-.
apply: memv_sumr => i _.
rewrite mulrC memv_prod //; last first.
 rewrite mxE /f_ (enum_val_nth 1%g) nth_index; last done.
 by rewrite repr_coset1 unit_lappE memv_inj.
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
have Hff : f \in coset [set x : LAut | kAut E (fullv L) (val x)] f.
 by rewrite val_coset // rcoset_refl.
apply/andP; split.
 apply/kHomP; split; last by move => ? ? _ _; rewrite rmorphM.
 move => a /FixedFieldP [HaE /(_ _ Hfs) Ha].
 rewrite -[X in _ = X]Ha.
 move: {Ha} a HaE. 
 by apply/(Aut_eq Hff (mem_repr_coset _)).
move: (HE _ Hfs) => HEfs.
rewrite -[X in (_ <= X)%VS]HEfs.
apply/subvP => _ /memv_imgP [a [Ha ->]].
apply/memv_imgP.
exists a; split; first done.
move: {Ha} a Ha.
by apply/(Aut_eq Hff (mem_repr_coset _)).
Qed.

End GaloisDim.

Section FundamentalTheoremOfGaloisTheory.

Variables E K : {algebra L}.
Hypothesis HKE : galois K E.

Section IntermediateField.

Variable M : {algebra L}.
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

Let f (y : coset_of [set x : LAut | kAut E (fullv L) (val x)]) :=
     (coset [set x : LAut | kAut M (fullv L) (val x)] (repr y)).

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
  by rewrite HxM // repr_coset1 unit_lappE.
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
by rewrite unit_lappE.
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

Variable g : {group coset_of [set x : LAut | kAut E (fullv L) (val x)]}.
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
pose x := coset [set x : LAut | kAut E (fullv L) (val x)] a.
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
  by rewrite -[X in (_ <= X)%VS]HaE limg_monotone.
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
