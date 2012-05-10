(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop ssralg ssrnum finset fingroup.
Require Import morphism perm automorphism quotient action zmodp center.
Require Import matrix mxalgebra mxrepresentation vector algC classfun character.
Require Import frobenius BGsection3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(******************************************************************************)
(* This file contains the definitions and properties of inertia groups:       *)
(*  (phi ^ y)%CF == the y-conjugate of phi : 'CF(G), i.e., the class function *)
(*                  mapping x ^ y to phi x, provided y normalises G. We take  *)
(*                  (phi ^ y)%CF = phi when y \notin 'N(G).                   *)
(* (phi ^: G)%CF == the sequence of all distinct y-conjugates of phi : 'CF(H) *)
(*                  for y in G.                                               *)
(*     'I_G[phi] == the inertia group of phi : CF(H) in G, i.e., the set of y *)
(*                  in G such that (phi ^ y)%CF = phi AND H :^ y = y.         *)
(* conjg_Iirr y i == the index j : Iirr G such that ('chi_i ^ y)%CF = 'chi_j. *)
(*     detRepr rG == the linear character afforded by the determinant of rG.  *)
(*      cfdet phi == the linear character afforded by the determinant of a    *)
(*                   representation affording phi.                            *)
(*        'o(phi) == the "determinential order" of phi (the multiplicative    *)
(*                   order of cfdet phi.                                      *)
(******************************************************************************)

Reserved Notation "''I_' G [ f ]"
  (at level 8, G at level 2, format "''I_' G [ f ]").

Section ConjDef.

Variables (gT : finGroupType) (B : {set gT}) (phi : 'CF(B)) (y : gT).
Local Notation G := <<B>>.

Fact cfConjg_subproof :
  is_class_fun G [ffun x => phi (if y \in 'N(G) then x ^ y^-1 else x)].
Proof.
apply: intro_class_fun => [x z _ Gz | x notGx].
  have [nGy | _] := ifP; last by rewrite cfunJgen.
  by rewrite -conjgM conjgC conjgM cfunJgen // memJ_norm ?groupV.
by rewrite cfun0gen //; case: ifP => // nGy; rewrite memJ_norm ?groupV.
Qed.
Definition cfConjg := Cfun 1 cfConjg_subproof.

End ConjDef.

Notation "f ^ y" := (cfConjg f y) : cfun_scope.

Section Conj.

Variables (gT : finGroupType) (G : {group gT}).
Implicit Type phi : 'CF(G).

Lemma cfConjgE phi y x : y \in 'N(G) -> (phi ^ y)%CF x = phi (x ^ y^-1)%g.
Proof. by rewrite cfunElock genGid => ->. Qed.

Lemma cfConjgEnorm phi y x : y \in 'N(G) -> (phi ^ y)%CF (x ^ y) = phi x.
Proof. by move/cfConjgE->; rewrite conjgK. Qed.

Lemma cfConjg_out phi y : y \notin 'N(G) -> (phi ^ y = phi)%CF.
Proof.
by move/negbTE=> notNy; apply/cfunP=> x; rewrite !cfunElock genGid notNy.
Qed.

Lemma cfConjgMnorm phi :
  {in 'N(G) &, forall y z, phi ^ (y * z) = (phi ^ y) ^ z}%CF.
Proof.
move=> y z nGy nGz.
by apply/cfunP=> x; rewrite !cfConjgE ?groupM // invMg conjgM.
Qed.

(* Isaacs' 6.1.b *)
Lemma cfConjgM L phi :
  G <| L -> {in L &, forall y z, phi ^ (y * z) = (phi ^ y) ^ z}%CF.
Proof. by case/andP=> _ /subsetP nGL; exact: sub_in2 (cfConjgMnorm phi). Qed.

Lemma cfConjg1 phi : (phi ^ 1)%CF = phi.
Proof. by apply/cfunP=> x; rewrite cfConjgE ?group1 // invg1 conjg1. Qed.

Lemma cfConjgK y : cancel ((@cfConjg _ G)^~ y) ((@cfConjg _ G)^~ y^-1%g).
Proof.
move=> phi; apply/cfunP=> x; rewrite !cfunElock groupV /=.
by case: ifP => -> //; rewrite conjgKV.
Qed.

Lemma cfConjgKV y : cancel ((@cfConjg _ G)^~ y^-1%g) ((@cfConjg _ G)^~ y).
Proof. by move=> phi /=; rewrite -{2}[y]invgK cfConjgK. Qed.

Lemma cfConjg_cfun0 y : (0 ^ y)%CF = 0 :> 'CF(G).
Proof. by apply/cfunP=> x; rewrite !cfunElock. Qed.

Lemma cfConjg_cfun1 y : (1 ^ y)%CF = 1 :> 'CF(G).
Proof.
apply/cfunP=> x; rewrite cfunElock // !cfun1E genGid.
by case: ifP => // nGy; rewrite memJ_norm ?groupV.
Qed.

Lemma cfConjg_val1 phi y : (phi ^ y)%CF 1%g = phi 1%g.
Proof. by rewrite cfunElock conj1g if_same. Qed.

Lemma cfConjg_Aut phi u y : cfAut u (phi ^ y) = (cfAut u phi ^ y)%CF.
Proof. by apply/cfunP=> x; rewrite !cfunElock. Qed.

Lemma cfConjg_conjC phi y : (phi ^ y)^*%CF = (phi^* ^ y)%CF.
Proof. exact: cfConjg_Aut. Qed.

Lemma cfker_conjg x phi : x \in 'N(G) -> cfker (phi ^ x) = cfker phi :^ x.
Proof.
move=> nGx; wlog suffices: phi x nGx / cfker phi :^ x \subset cfker (phi ^ x).
  move=> IH; apply/eqP; rewrite eqEsubset -{2}(cfConjgK x phi) -sub_conjgV.
  by rewrite !IH ?groupV.
apply/subsetP=> _ /imsetP[y Ky ->].
rewrite inE memJ_norm // (subsetP (cfker_sub phi)) //.
by apply/forallP=> z; rewrite !cfConjgE // conjMg conjgK cfkerMl.
Qed.

End Conj.

Section Inertia.

Variable gT : finGroupType.

Definition inertia (B A : {set gT}) (phi : 'CF(B)) :=  
  [set y \in 'N_A(B) | (phi ^ y)%CF == phi].

Local Notation "''I_' G [ phi ]" := (inertia G phi) : group_scope.

Fact group_set_inertia (H G : {group gT}) (phi : 'CF(H)) : group_set 'I_G[phi].
Proof.
apply/group_setP; split; first by rewrite inE group1 /= cfConjg1.
move=> y z /setIdP[/setIP[Gy nHy] /eqP n_phi_y] /setIdP[/setIP[Gz nHz] n_phi_z].
by rewrite 2!inE !groupM // cfConjgMnorm // n_phi_y.
Qed.
Canonical inertia_group H G phi := Group (@group_set_inertia H G phi).

Local Notation "''I_' G [ f ]" := (inertia_group G f) : Group_scope.

Variables G H : {group gT}.
Implicit Type phi : 'CF(H).

Lemma inertia_sub phi : 'I_G[phi] \subset G.
Proof. by rewrite ['I_G[_]]setIdE -setIA subsetIl. Qed.

Lemma norm_inertia phi : 'I_G[phi] \subset 'N(H).
Proof. by rewrite ['I_G[_]]setIdE setIAC subsetIr. Qed.

Lemma cfConjg_eqE phi :
    H <| G ->
  {in G &, forall y z, (phi ^ y == phi ^ z)%CF = (z \in 'I_G[phi] :* y)}.
Proof.
case/andP=> _ nHG y z; rewrite mem_rcoset inE (setIidPl nHG) -groupV => Gy' Gz.
rewrite groupM // (can2_eq (cfConjgK y) (cfConjgKV y)) eq_sym.
by rewrite cfConjgMnorm ?(subsetP nHG).
Qed.

Lemma inertia_center phi : H <| G -> 'Z(G) \subset 'I_G[phi].
Proof.
case/andP=> sHG nHG; apply/subsetP=> y /centerP[Gy cGy].
rewrite inE (setIidPl nHG) Gy.
apply/eqP/cfun_inP=> x Hx; rewrite cfConjgE ?(subsetP nHG) //.
by rewrite /conjg invgK mulgA cGy ?mulgK // (subsetP sHG).
Qed.

Lemma sub_inertia phi : H <| G -> H \subset 'I_G[phi].
Proof.
case/andP=> sHG nHG; apply/subsetP=> y Hy.
rewrite inE (setIidPl nHG) (subsetP sHG) //=.
by apply/eqP/cfunP=> x; rewrite cfunElock fun_if cfunJ ?groupV // if_same.
Qed.

Lemma normal_inertia phi : H <| G -> H <| 'I_G[phi].
Proof. by move/sub_inertia=> sHT; rewrite /normal sHT norm_inertia. Qed.

(* Isaacs' 6.1.c *)
Lemma cfdot_Conjg phi psi y : '[phi ^ y, psi ^ y] = '[phi, psi].
Proof.
have [nHy | not_nHy] := boolP (y \in 'N(H)); last by rewrite !cfConjg_out.
congr (_ * _); rewrite -{1}(normP nHy).
rewrite big_imset; last exact: in2W (conjg_inj y).
by apply: eq_bigr=> x _; rewrite !cfConjgEnorm.
Qed.
 
(* Isaacs' 6.1.d *)
Lemma cfdot_Res_Conjg psi phi y :
  y \in G -> '['Res[H, G] psi, phi ^ y] = '['Res[H] psi, phi].
Proof.
move=> Gy; rewrite -(cfdot_Conjg _ phi y).
congr (_ * _); apply: eq_bigr => x Hx; congr (_ * _).
rewrite !cfunElock !genGid Hx; case sHG: (H \subset G); rewrite ?andbF //.
by case: ifP => nHy; rewrite ?memJ_norm ?cfunJ ?groupV ?Hx.
Qed.

(* Isaac's 6.1.e *)
Lemma cfConjg_char (chi : 'CF(H)) y :
  chi \is a character -> (chi ^ y)%CF \is a character.
Proof.
have [nHy | /cfConjg_out-> //] := boolP (y \in 'N(H)).
case/char_reprP=> rG ->; apply/char_reprP.
have rGyP: mx_repr H (fun x => rG (x ^ y^-1)%g).
  split=> [|x1 x2 Hx1 Hx2]; first by rewrite conj1g repr_mx1.
  by rewrite conjMg repr_mxM ?memJ_norm ?groupV.
exists (Representation (MxRepresentation rGyP)) => /=.
by apply/cfunP=> x; rewrite cfConjgE // !cfunE memJ_norm ?groupV.
Qed.

Lemma irr_Conjg i y : ('chi_i ^ y)%CF \in irr H.
Proof.
rewrite irr_char1E cfConjg_char ?irr_char //=.
by rewrite cfdot_Conjg cfdot_irr eqxx.
Qed.
 
Definition conjg_Iirr i y := irr_Iirr (fun i => 'chi[H]_i ^ y)%CF i.

Lemma conjg_IirrE i y : 'chi_(conjg_Iirr i y) = ('chi_i ^ y)%CF.
Proof. by apply: irr_IirrE => j; exact: irr_Conjg. Qed.

Lemma conjg_Iirr0 x : conjg_Iirr 0 x = 0.
Proof. by apply: chi_inj; rewrite conjg_IirrE chi0_1 cfConjg_cfun1. Qed.

Lemma cfdot_irr_Conjg i y :
  H <| G -> y \in G -> '['chi_i, 'chi_i ^ y]_H = (y \in 'I_G['chi_i])%:R.
Proof.
move=> nsHG Gy; rewrite inE (setIidPl (normal_norm nsHG)) Gy eq_sym.
by rewrite -conjg_IirrE cfdot_irr inj_eq //; exact: chi_inj.
Qed.

Definition cfclass (A : {set gT}) (phi : 'CF(A)) (B : {set gT}) := 
  [image (phi ^ repr Tx)%CF | Tx <- rcosets 'I_B[phi] B].

Local Notation "phi ^: G" := (cfclass phi G) : cfun_scope.

Lemma cfclassP (A : {group gT}) phi psi :
  reflect (exists2 y, y \in A & psi = phi ^ y)%CF (psi \in phi ^: A)%CF.
Proof.
apply: (iffP (imageP _ _ _)) => [[_ /rcosetsP[y Ay ->] ->] | [y Ay ->]].
  case: repr_rcosetP => z /setIdP[/setIP[Az _] _].
  by exists (z * y)%g; rewrite ?groupM.
without loss nHy: y Ay / y \in 'N(H).
  have [nHy | /cfConjg_out->] := boolP (y \in 'N(H)); first exact.
  by move/(_ 1%g); rewrite !group1 !cfConjg1; exact.
exists ('I_A[phi] :* y); first by rewrite -rcosetE mem_imset.
case: repr_rcosetP => z /setIdP[/setIP[_ nHz] /eqP Tz].
by rewrite cfConjgMnorm ?Tz.
Qed.

Lemma cfclassInorm phi : (phi ^: 'N_G(H) =i phi ^: G)%CF.
Proof.
move=> xi; apply/cfclassP/cfclassP=> [[x /setIP[Gx _] ->] | [x Gx ->]].
  by exists x.
have [Nx | /cfConjg_out-> //] := boolP (x \in 'N(H)).
  by exists x; first exact/setIP.
by exists 1%g; rewrite ?group1 ?cfConjg1.
Qed.

Lemma cfclass_refl phi : phi \in (phi ^: G)%CF.
Proof. by apply/cfclassP; exists 1%g => //; rewrite cfConjg1. Qed.

Lemma cfclass_transl phi psi :
  (psi \in phi ^: G)%CF -> (phi ^: G =i psi ^: G)%CF.
Proof.
rewrite -cfclassInorm; case/cfclassP=> x Gx -> xi; rewrite -!cfclassInorm.
have nHN: {subset 'N_G(H) <= 'N(H)} by apply/subsetP; exact: subsetIr.
apply/cfclassP/cfclassP=> [[y Gy ->] | [y Gy ->]].
  by exists (x^-1 * y)%g; rewrite -?cfConjgMnorm ?groupM ?groupV ?nHN // mulKVg.
by exists (x * y)%g; rewrite -?cfConjgMnorm ?groupM ?nHN.
Qed.

Lemma cfclass_sym phi psi : (psi \in phi ^: G)%CF = (phi \in psi ^: G)%CF.
Proof. by apply/idP/idP=> /cfclass_transl <-; exact: cfclass_refl. Qed.

Lemma cfclass_uniq phi : H <| G -> uniq (phi ^: G)%CF.
Proof.
case/andP=> _ /subsetP nHG.
rewrite map_inj_in_uniq ?enum_uniq // => Ty Tz; rewrite !mem_enum.
move=> {Ty}/rcosetsP[y Gy ->] {Tz}/rcosetsP[z Gz ->].
rewrite -{2}(rcoset_repr _ y) -{2}(rcoset_repr _ z).
case: repr_rcosetP => u /setIdP[/setIP[Gu _] _].
case: repr_rcosetP => v /setIdP[/setIP[Gv _] _].
move=> eq_phi_uy_vz; apply: rcoset_transl; rewrite mem_rcoset.
rewrite 2!inE cfConjgMnorm ?(groupM, groupV) ?nHG //=.
by rewrite eq_phi_uy_vz cfConjgK.
Qed.

Lemma inertia1 : H <| G -> 'I_G[1 : 'CF(H)] = G.
Proof.
case/andP=> _ nHG; rewrite ['I_G[1]]setIdE (setIidPl nHG).
by apply/setIidPl/subsetP=> x Gx; rewrite inE cfConjg_cfun1.
Qed.

Lemma cfclass1 : H <| G -> (1 ^: G)%CF = [:: 1 : 'CF(H)].
Proof.
move=> nsHG; rewrite /cfclass inertia1 // rcosets_id.
by rewrite /(image _ _) enum_set1 /= cfConjg_cfun1.
Qed.

Lemma cfclass_sum R idx (op : Monoid.com_law idx) (F : 'CF(H) -> R) i :
     H <| G ->
  \big[op/idx]_(j | 'chi_j \in ('chi_i ^: G)%CF) F 'chi_j
     = \big[op/idx]_(chi <- ('chi_i ^: G)%CF) F chi.
Proof.
move/cfclass_uniq=> chiGuniq; rewrite -big_map -big_filter; apply: eq_big_perm.
rewrite -[index_enum _]enumT map_tnth_enum uniq_perm_eq // => [|chi].
  by rewrite filter_uniq // free_uniq // irr_free.
by rewrite mem_filter; apply: andb_idr => /imageP[Tx _ ->]; exact: irr_Conjg.
Qed.

(* This is Isaacs, Theorem (6.2) *)
Lemma Clifford_Res_sum_cfclass i j :
     H <| G -> j \in irr_constt ('Res[H, G] 'chi_i) ->
  'Res[H] 'chi_i = 
     '['Res[H] 'chi_i, 'chi_j] *: (\sum_(chi <- ('chi_j ^: G)%CF) chi).
Proof.
move=> nsHG chiHj; have [sHG /subsetP nHG] := andP nsHG.
rewrite -cfclass_sum //= big_mkcond.
rewrite {1}['Res _]cfun_sum_cfdot linear_sum /=; apply: eq_bigr => k _.
have [[y Gy ->] | ] := altP (cfclassP _ _ _); first by rewrite cfdot_Res_Conjg.
apply: contraNeq; rewrite scaler0 scaler_eq0 orbC => /norP[_ chiHk].
have{chiHk chiHj}: '['Res[H] ('Ind[G] 'chi_j), 'chi_k] != 0.
  rewrite !inE !cfdot_Res_l in chiHj chiHk *.
  apply: contraNneq chiHk; rewrite cfdot_sum_irr => /psumr_eq0P/(_ i isT)/eqP.
  rewrite -cfdotC cfdotC mulf_eq0 conjC_eq0 (negbTE chiHj) /= => -> // i1.
  by rewrite -cfdotC Cnat_ge0 // rpredM ?Cnat_cfdot_char ?cfInd_char ?irr_char.
have ->: 'Res ('Ind[G] 'chi_j) = #|H|%:R^-1 *: (\sum_(y \in G) 'chi_j ^ y)%CF.
  rewrite (reindex_inj invg_inj); apply/cfun_inP=> x Hx.
  rewrite cfResE // cfIndE // cfunE sum_cfunE; congr (_ * _).
  by apply: eq_big => [y | y Gy]; rewrite ?cfConjgE ?groupV ?invgK ?nHG.
rewrite cfdotZl mulf_eq0 cfdot_suml => /norP[_]; apply: contraR => not_chjGk.
rewrite big1 // => x Gx; apply: contraNeq not_chjGk.
rewrite -conjg_IirrE cfdot_irr pnatr_eq0; case: (_ =P k) => // <- _.
by rewrite conjg_IirrE; apply/cfclassP; exists x.
Qed.

(* This is Isaacs' 6.7 *)
Lemma constt0_Res_cfker i : 
  H <| G -> 0 \in irr_constt ('Res[H] 'chi[G]_i) -> H \subset cfker 'chi[G]_i.
Proof.
move=> nsHG /(Clifford_Res_sum_cfclass nsHG); have [sHG nHG] := andP nsHG.
rewrite chi0_1 cfdot_Res_l cfclass1 // big_seq1 cfInd_cfun1 //.
rewrite cfdotZr conjC_nat => def_chiH.
apply/subsetP=> x Hx; rewrite cfker_irrE inE -!(cfResE _ sHG) //.
by rewrite def_chiH !cfunE !cfun1E Hx group1.
Qed.

(* This is Isaacs' 6.8 *)
Lemma dvdn_constt_Res1_irr1 i j : 
    H <| G -> j \in irr_constt ('Res[H, G] 'chi_i) ->
  exists n, 'chi_i 1%g = n%:R * 'chi_j 1%g.
Proof.
move=> nsHG chiHj; have [sHG nHG] := andP nsHG; rewrite -(cfResE _ sHG) //.
rewrite {1}(Clifford_Res_sum_cfclass nsHG chiHj) cfunE sum_cfunE.
have /CnatP[n ->]: '['Res[H] 'chi_i, 'chi_j] \in Cnat.
  by rewrite Cnat_cfdot_char ?cfRes_char ?irr_char.
exists (n * size ('chi_j ^: G)%CF)%N; rewrite natrM -mulrA; congr (_ * _).
rewrite mulr_natl -[size _]card_ord big_tnth -sumr_const; apply: eq_bigr => k _.
by have /cfclassP[y Gy ->]:=  mem_tnth k (in_tuple _); rewrite cfConjg_val1.
Qed.

Lemma cfclass_Ind phi psi :
  H <| G ->  psi \in (phi ^: G)%CF -> 'Ind[G] phi = 'Ind[G] psi.
Proof.
move=> nsHG /cfclassP[y Gy ->]; have [sHG /subsetP nHG] := andP nsHG.
apply/cfun_inP=> x Hx; rewrite !cfIndE //; congr (_ * _).
rewrite (reindex_acts 'R _ (groupVr Gy)) ?astabsR //=.
by apply: eq_bigr => z Gz; rewrite conjgM cfConjgE ?nHG.
Qed.

Lemma cfclass_size i : size ('chi[H]_i ^: G)%CF =  #|G : 'I_G['chi_i]|.
Proof. by rewrite size_map -cardE. Qed.

End Inertia.

Arguments Scope inertia [_ group_scope group_scope cfun_scope].
Arguments Scope cfclass [_ group_scope cfun_scope group_scope].
Notation "''I_' G [ phi ] " := (inertia G phi) : group_scope.
Notation "''I_' G [ phi ] " := (inertia_group G phi) : Group_scope.
Notation "phi ^: G" := (cfclass phi G) : cfun_scope.

Section MoreInertia.

Variables (gT : finGroupType) (G H : {group gT}) (i : Iirr H).
Let T := 'I_G['chi_i].

Lemma inertia_id : 'I_T['chi_i] = T.
Proof.
rewrite ['I_T[_]]setIdE -{1}[T](setIidPl (inertia_sub _ _)) -/T.
by rewrite -!setIA (setIA G) -setIdE setIid.
Qed.

Lemma cfclass_inertia : ('chi[H]_i ^: T)%CF = [:: 'chi_i].
Proof.
rewrite /cfclass inertia_id rcosets_id /(image _ _) enum_set1 /=.
by rewrite repr_group cfConjg1.
Qed.

End MoreInertia.

Section S611.

Variable (gT : finGroupType).

Section S611A.

Variable (H G : {group gT}).

Variable t : Iirr H.

Let T := 'I_G['chi_t]%G.

Hypothesis HnG : H <| G.

Let TsG := inertia_sub G 'chi_t.

Let HsT : H \subset T.
Proof. exact: sub_inertia. Qed.

Let HnT : H <| T.
Proof. exact: normal_inertia. Qed.

Section Chi.

Variable p : Iirr T.

Hypothesis Hp : t \in irr_constt ('Res[H] 'chi_p).

Variable c : Iirr G.

Hypothesis Hc : c \in irr_constt ('Ind[G,T] 'chi_p).

Let ITC : 'Res[T] 'chi_c \is a character.
Proof. by rewrite cfRes_char ?irr_char. Qed.

Let ITP : 'Res[T] 'chi_p \is a character.
Proof. by rewrite cfRes_char ?irr_char. Qed.

Let IHC : 'Res[H] 'chi_c \is a character.
Proof. by rewrite cfRes_char ?irr_char. Qed.

Let IHP : 'Res[H] 'chi_p \is a character.
Proof. by rewrite cfRes_char ?irr_char. Qed.

Fact constt_Res_inertia_constt_Ind : p \in irr_constt ('Res[T] 'chi_c).
Proof. by rewrite !inE cfdotC_char ?irr_char ?Frobenius_reciprocity. Qed.

Fact constt_Res_constt_Ind : t \in irr_constt ('Res[H] 'chi_c).
Proof.
rewrite -(cfResRes _ HsT TsG).
exact: constt_Res_trans constt_Res_inertia_constt_Ind _ _.
Qed.

Let e := '['Res[H] 'chi_c, 'chi_t].

Let f := '['Res[H] 'chi_p, 'chi_t].

Let He : 'Res[H] 'chi_c = e *: (\sum_(f <- 'chi_t ^: G) f)%CF.
Proof. exact: (Clifford_Res_sum_cfclass HnG constt_Res_constt_Ind). Qed.

Let Hf : 'Res[H] 'chi_p = f *: 'chi_t.
Proof.
by have:= Clifford_Res_sum_cfclass HnT Hp; rewrite cfclass_inertia big_seq1.
Qed.

Let He1 : 'chi_c 1%g = e * #|G : T|%:R * 'chi_t 1%g.
Proof.
rewrite -(cfResE _ (normal_sub HnG)) // He cfunE -mulrA; congr (_ * _).
rewrite mulr_natl -cfclass_size -[size _]card_ord sum_cfunE big_seq big_tnth.
rewrite -sumr_const; apply: eq_big => k; first exact: mem_tnth.
by case/cfclassP=> y Gy ->; rewrite cfConjg_val1.
Qed.

Let Hpsi1  : ('Ind[G] 'chi_p) 1%g = f * #|G : T|%:R * ('chi_t 1%g).
Proof. by rewrite -mulrA mulrCA cfInd1 // -(cfResE _ HsT) // Hf cfunE. Qed.

Fact cfdot_constt_inertia_constt : f = e.
Proof.
have le_f_e: f <= e.
  have: '['Res 'chi_p, 'chi_t] <= '['Res[H] ('Res[T] 'chi_c), 'chi_t].
    by apply: cfdot_Res_ge_constt constt_Res_inertia_constt_Ind.
  rewrite Hf /= cfResRes // He !cfdotZl cfdot_irr eqxx mulr1.
  rewrite -cfclass_sum // cfdot_suml (bigD1 t) ?cfclass_refl //= cfdot_irr eqxx.
  rewrite big1 ?addr0 ?mulr1 // => i /andP[_ neq_it].
  by rewrite cfdot_irr (negbTE neq_it).
apply/eqP; rewrite eqr_le le_f_e /=.
have: 0 < #|G : T|%:R * 'chi_t 1%g.
  by rewrite pmulr_rgt0 // ?irr1_gt0 // ltr0n.
move/ler_pmul2r => <-; rewrite !mulrA -He1 -Hpsi1.
have IIP: 'Ind[G] 'chi_p \is a character := cfInd_char G (irr_char p).
case/(constt_charP _ IIP): Hc => chi' /= IC' ->.
by rewrite cfunE ler_addl Cnat_ge0 ?Cnat_char1.
Qed.

Fact cfInd_constt_inertia_constt : 'Ind[G] 'chi_p = 'chi_c.
Proof.
have ICI: 'Ind[G] 'chi_p \is a character := cfInd_char G (irr_char p).
case/(constt_charP _ ICI): Hc => chi' IC' /= Hchi'.
rewrite Hchi'; move/cfunP/(_ 1%g)/esym/eqP: Hchi'.
rewrite Hpsi1 cfdot_constt_inertia_constt -He1 cfunE addrC -subr_eq0 addrK.
by rewrite char1_eq0 // => /eqP->; rewrite addr0.
Qed.

End Chi.

Variable p : Iirr T.

Hypothesis Hp : t \in irr_constt ('Res[H] 'chi_p).

Let cP : 'Ind[G] 'chi_p != 0.
Proof. by rewrite cfInd_eq0 -?char1_eq0 ?irr_char ?irr1_neq0. Qed.

Let c := val (sigW (neq0_has_constt cP)).

Let Hc : c \in irr_constt ('Ind[G] 'chi_p).
Proof. exact: valP (sigW (neq0_has_constt cP)). Qed.

(* This is 6.11 (a) *)
Lemma cfInd_constt_inertia_irr : 'Ind[G] 'chi_p \in irr G.
Proof. by rewrite (cfInd_constt_inertia_constt Hp Hc); exact: irr_chi. Qed.

(* This is 6.11 (d) *)
Lemma cfdot_constt_inertia : 
 '['Res 'chi_p, 'chi_t] = '['Res ('Ind[G] 'chi_p), 'chi_t].
Proof. 
rewrite (cfInd_constt_inertia_constt Hp Hc).
by rewrite (cfdot_constt_inertia_constt Hp Hc).
Qed.

(* This is 6.11 (b) the domain of the induction is B *)
Lemma constt_Res_constt_inertia : t \in irr_constt ('Res ('Ind[G] 'chi_p)).
Proof. 
rewrite (cfInd_constt_inertia_constt Hp Hc).
by rewrite (constt_Res_constt_Ind Hp Hc).
Qed.

(* This is 6.11 c *)
Lemma single_constt_inertia (p' : Iirr T) :
    p' \in irr_constt ('Res ('Ind[G] 'chi_p)) ->
    t \in irr_constt('Res 'chi_p') ->
  p' = p.
Proof.
rewrite (cfInd_constt_inertia_constt Hp Hc) => Cp' Ct.
have IC: 'Res[T] 'chi_c \is a character := cfRes_char T (irr_char c).
case/(constt_charP _ IC): Cp' => chi1 IC1 Hchi1.
apply: contraTeq isT => Dpsi.
have /(constt_charP _ IC1)[chi2 IC2 Hchi2]: p \in irr_constt chi1.
  have: p \in irr_constt ('Res[T] 'chi_c).
    exact: constt_Res_inertia_constt_Ind.
  by rewrite !inE Hchi1 cfdotDl cfdot_irr (negPf Dpsi) add0r.
have: '['Res[H] 'chi_p, 'chi_t] < '['Res[H] ('Res[T] 'chi_c), 'chi_t].
  rewrite Hchi1 addrC Hchi2 !linearD !cfdotDl /=.
  rewrite -addrA addrC -subr_gt0 addrK ltr_paddl //.
    by rewrite Cnat_ge0 ?Cnat_cfdot_char_irr ?cfRes_char.
  rewrite ltr_def [~~ _]Ct Cnat_ge0 ?Cnat_cfdot_char_irr //.
  by rewrite cfRes_char ?irr_char.
rewrite cfdot_constt_inertia (cfInd_constt_inertia_constt Hp Hc).
by rewrite cfResRes // ltr_def eqxx.
Qed.

End S611A.

(* This is 6.11 b it is an injection *)
Lemma constt_inertia_inj (G H : {group gT}) (t : Iirr H) :
   H <| G ->
 {in [pred p | t \in irr_constt ('Res[H, 'I_G['chi_t]] 'chi_p)] &,
    injective (fun p => 'Ind[G, 'I_G['chi_t]] 'chi_p)}.
Proof.
move=> HnG p p' Hp Hp' Heq; set T := 'I_G[_].
have TsG: T \subset G := inertia_sub G 'chi_t.
apply: (single_constt_inertia HnG Hp' _ Hp).
have IC1: 'Ind[G] 'chi_p \is a character := cfInd_char G (irr_char p).
have IC2: 'Res[T] ('Ind[G] 'chi_p) \is a character := cfRes_char _ IC1.
rewrite -Heq !inE cfdotC_char ?irr_char //.
rewrite Frobenius_reciprocity /= cfnorm_eq0 cfInd_eq0 ?irr_char //.
exact: (free_not0 (irr_free _) (irr_chi p)).
Qed.

(* 6.11 b the inverse function *)
Definition inertia_Ind_inv (G H : {group gT}) t (chi : 'CF(G)) :=
  odflt 0 (pick [pred t' | (t \in irr_constt ('Res[H] 'chi_t')) && 
                           (t' \in irr_constt ('Res['I_G['chi_t]] chi))]).

Let inertia_coord (G H : {group gT}) (t : Iirr H) (c : Iirr G) :
    H <| G -> [pred p | (t \in irr_constt ('Res[H] 'chi_p)) &&
                        (p \in irr_constt ('Res['I_G['chi_t]] 'chi_c))]
               =1 xpred0 ->
   '['Res[H] 'chi_c, 'chi_t] == 0.
Proof.
set T := 'I_G['chi_t] => HnG HH.
have HsT: H \subset T := sub_inertia 'chi_t HnG.
rewrite -(cfResRes _ HsT) ?inertia_sub //= -/T.
rewrite ['Res 'chi_c]cfun_sum_cfdot linear_sum cfdot_suml big1 //= => i _.
move/negbT: (HH i); apply: contraNeq; rewrite linearZ cfdotZl mulf_eq0 //=.
by rewrite orbC negb_or.
Qed.

Lemma constt_inertia_Ind_inv (G H : {group gT}) t c :
    H <| G -> t \in irr_constt ('Res[H, G] 'chi_c) ->
  t \in irr_constt ('Res[H] 'chi_(inertia_Ind_inv t 'chi_c)).
Proof.
move=> HnG Ct.
rewrite /inertia_Ind_inv; case: pickP => [_ /andP[] //| HH].
by case/negP: Ct; apply: inertia_coord.
Qed.

Lemma inertia_Ind_inv_constt (G H : {group gT}) t c :
    H <| G -> t \in irr_constt ('Res[H, G] 'chi_c) ->
  inertia_Ind_inv t 'chi_c \in irr_constt ('Res['I_G['chi_t]] 'chi_c).
Proof.
move=> HnG Ct.
rewrite /inertia_Ind_inv; case: pickP => [_ /andP[] //| HH].
by case/negP: Ct; apply: inertia_coord.
Qed.

(* This is 6.11 b the surjective part *)
Lemma inertia_Ind_invE (G H : {group gT}) (t : Iirr H) (c : Iirr G) :
    H <| G -> t \in irr_constt ('Res[H] 'chi_c) ->
  'Ind[G] 'chi_(inertia_Ind_inv t 'chi_c) = 'chi_c.
Proof.
move=> HnG Cc.
apply: cfInd_constt_inertia_constt => //; first exact: constt_inertia_Ind_inv.
rewrite !inE -Frobenius_reciprocity cfdotC_char ?cfRes_char ?irr_char //.
exact: inertia_Ind_inv_constt.
Qed.

End S611.


(* Isaacs 6.28 preliminary *)
Section S628.

Variables (gT : finGroupType) (G : {group gT}).

Section DetRepr.

Variables (n : nat) (rG : mx_representation [fieldType of algC] G n).

Definition det_repr_mx x : 'M_1 := (\det (rG x))%:M.

Fact det_is_repr : mx_repr G det_repr_mx. 
Proof.
split=> [|g h Gg Gh]; first by rewrite /det_repr_mx repr_mx1 det1.
by rewrite /det_repr_mx repr_mxM // det_mulmx !mulmxE scalar_mxM.
Qed.

Canonical det_repr := MxRepresentation det_is_repr.
Definition detRepr := cfRepr det_repr.

Lemma detRepr_lin_char : detRepr \is a linear_char.
Proof.
by rewrite qualifE cfRepr_char cfunE group1 repr_mx1 mxtrace1 mulr1n /=.
Qed.

End DetRepr.

Definition cfdet phi := \prod_i detRepr 'Chi_i ^+ truncC '[phi, 'chi[G]_i].

Lemma cfdet_lin_char phi : cfdet phi \is a linear_char.
Proof. by apply: rpred_prod => i _; apply: rpredX; apply: detRepr_lin_char. Qed.

Lemma cfdetD :
  {in character &, {morph cfdet : phi psi / phi + psi >-> phi * psi}}.
Proof.
move=> phi psi Nphi Npsi; rewrite /= -big_split; apply: eq_bigr => i _ /=.
by rewrite -exprD cfdotDl truncCD ?nnegrE ?Cnat_ge0 // Cnat_cfdot_char_irr.
Qed.

Lemma cfdet0 : cfdet 0 = 1.
Proof. by rewrite /cfdet big1 // => i _; rewrite cfdot0l truncC0. Qed.

Lemma cfdetMn k :
  {in character, {morph cfdet : phi / phi *+ k >-> phi ^+ k}}.
Proof.
move=> phi Nphi; elim: k => [|k IHk]; rewrite ?cfdet0 // mulrS exprS -{}IHk.
by rewrite cfdetD ?rpredMn.
Qed.

Lemma cfdet_Repr n rG : cfdet (cfRepr rG) = @detRepr n rG.
Proof.
transitivity (\prod_W detRepr (socle_repr W) ^+ standard_irr_coef rG W).
  rewrite (reindex _ (socle_of_Iirr_bij _)) /cfdet /=.
  apply: eq_bigr => i _; congr (_ ^+ _).
  rewrite (cfRepr_sim (mx_rsim_standard rG)) cfRepr_standard.
  rewrite cfdot_suml (bigD1 i) ?big1 //= => [|j i'j]; last first.
    by rewrite cfdotZl cfdot_irr (negPf i'j) mulr0.
  by rewrite cfdotZl cfnorm_irr mulr1 addr0 natCK.
apply/cfun_inP=> x Gx; rewrite prod_cfunE //.
transitivity (detRepr (standard_grepr rG) x); last first.
  rewrite !cfunE Gx !trace_mx11 !mxE eqxx !mulrb.
  case: (standard_grepr rG) (mx_rsim_standard rG) => /= n1 rG1 [B Dn1].
  rewrite -{n1}Dn1 in rG1 B *; rewrite row_free_unit => uB rG_B.
  by rewrite -[rG x](mulmxK uB) rG_B // !det_mulmx mulrC -!det_mulmx mulKmx.
rewrite /standard_grepr; elim/big_rec2: _ => [|W y _ _ ->].
  by rewrite cfunE trace_mx11 mxE Gx det1.
rewrite !cfunE Gx /= !{1}trace_mx11 !{1}mxE det_ublock; congr (_ * _).
rewrite exp_cfunE //; elim: (standard_irr_coef rG W) => /= [|k IHk].
  by rewrite /muln_grepr big_ord0 det1.
rewrite exprS /muln_grepr big_ord_recl det_ublock -IHk; congr (_ * _).
by rewrite cfunE trace_mx11 mxE Gx.
Qed.

Lemma cfdet_id xi : xi \is a linear_char -> cfdet xi = xi.
Proof.
move=> lin_xi; have /irrP[i Dxi] := lin_char_irr lin_xi.
apply/cfun_inP=> x Gx; rewrite Dxi -cfun_Chi cfdet_Repr !cfunE trace_mx11 mxE.
move: lin_xi (_ x) => /andP[_]; rewrite Dxi irr1_degree pnatr_eq1 => /eqP-> X.
by rewrite {1}[X]mx11_scalar det_scalar1 trace_mx11.
Qed.

Definition cfdet_order phi := #[cfdet phi]%CF.

Definition cfdet_order_lin xi :
  xi \is a linear_char -> cfdet_order xi = #[xi]%CF.
Proof. by rewrite /cfdet_order => /cfdet_id->. Qed.

Lemma lin_char_group:
     {linG : finGroupType & {cF : linG -> 'CF(G) | 
         [/\ injective cF, forall l, cF l \is a linear_char
          & forall phi, phi \is a linear_char -> exists l, phi = cF l]
       & [/\ {morph cF : k l / (k * l)%g >-> (k * l)%R},
              cF 1%g = 1%R &
             {morph cF: l / l^-1%g >-> l^-1%CF} ]}}. 
Proof.
pose linT := {i : Iirr G | 'chi_i \is a linear_char}.
pose cF (k : linT) := 'chi_(sval k).
have cFlin k: cF k \is a linear_char := svalP k.
have cFinj: injective cF := inj_comp chi_inj val_inj.
have inT xi : xi \is a linear_char -> {k | cF k = xi}.
  move=> lin_xi; have /irrP/sig_eqW[i Dxi] := lin_char_irr lin_xi.
  by apply: (exist _ (Sub i _)) => //; rewrite -Dxi.
have [one cFone] := inT 1 (rpred1 _).
pose inv k := sval (inT _ (rpredVr (cFlin k))).
pose mul k l := sval (inT _ (rpredM (cFlin k) (cFlin l))).
have cFmul k l: cF (mul k l) = cF k * cF l := svalP (inT _ _).
have cFinv k: cF (inv k) = (cF k)^-1 := svalP (inT _ _).
have mulA: associative mul by move=> k l m; apply: cFinj; rewrite !cFmul mulrA.
have mul1: left_id one mul by move=> k; apply: cFinj; rewrite cFmul cFone mul1r.
have mulV: left_inverse one inv mul.
  by move=> k; apply: cFinj; rewrite cFmul cFinv cFone mulVr ?lin_char_unitr.
pose linB := BaseFinGroupType linT (FinGroup.Mixin mulA mul1 mulV).
by exists (@FinGroupType linB mulV), cF; split=> // xi /inT[k <-]; exists k.
Qed.

End S628.

Notation "''o' ( phi )" := (cfdet_order phi)
  (at level 8, format "''o' ( phi )") : cfun_scope.

Section Frobenius.

Variables (gT : finGroupType) (G K : {group gT}).

(* Because he only defines Frobenius groups in chapter 7, Isaacs does not     *)
(* state these theorems using the Frobenius property.                         *)
Hypothesis frobGK : [Frobenius G with kernel K].

(* This is Isaacs, Theorem 6.34(a1). *)
Theorem inertia_Frobenius_ker i : i != 0 -> 'I_G['chi[K]_i] = K.
Proof.
have [_ _ nsKG regK] := Frobenius_kerP frobGK; have [sKG nKG] := andP nsKG.
move=> nzi; apply/eqP; rewrite eqEsubset sub_inertia // andbT.
apply/subsetP=> x /setIdP[/setIP[Gx nKx] /eqP x_stab_i].
have actIirrK: is_action G (@conjg_Iirr _ K).
  split=> [y j k eq_jk | j y z Gy Gz].
    by apply/chi_inj/(can_inj (cfConjgK y)); rewrite -!conjg_IirrE eq_jk.
  by apply: chi_inj; rewrite !conjg_IirrE (cfConjgM _ nsKG).
pose ito := Action actIirrK; pose cto := ('Js \ (subsetT G))%act.
have acts_Js : [acts G, on classes K | 'Js].
  apply/subsetP=> y Gy; have nKy := subsetP nKG y Gy.
  rewrite !inE; apply/subsetP=> _ /imsetP[z Gz ->]; rewrite !inE /=.
  rewrite -class_rcoset norm_rlcoset // class_lcoset.
  by apply: mem_imset; rewrite memJ_norm.
have acts_cto : [acts G, on classes K | cto] by rewrite astabs_ract subsetIidl.
pose m := #|'Fix_(classes K | cto)[x]|.
have def_m: #|'Fix_ito[x]| = m.
  apply: card_afix_irr_classes => // j y _ Ky /imsetP[_ /imsetP[z Kz ->] ->].
  by rewrite conjg_IirrE cfConjgEnorm // cfunJ.
have: (m != 1)%N.
  rewrite -def_m (cardD1 (0 : Iirr K)) (cardD1 i) !(inE, sub1set) /=.
  by rewrite conjg_Iirr0 nzi eqxx -(inj_eq chi_inj) conjg_IirrE x_stab_i eqxx.
apply: contraR => notKx; apply/cards1P; exists 1%g; apply/esym/eqP.
rewrite eqEsubset !(sub1set, inE) classes1 /= conjs1g eqxx /=.
apply/subsetP=> _ /setIP[/imsetP[y Ky ->] /afix1P /= cyKx].
have /imsetP[z Kz def_yx]: y ^ x \in y ^: K.
  by rewrite -cyKx; apply: mem_imset; exact: class_refl.
rewrite inE classG_eq1; apply: contraR notKx => nty.
rewrite -(groupMr x (groupVr Kz)).
apply: (subsetP (regK y _)); first exact/setD1P.
rewrite !inE groupMl // groupV (subsetP sKG) //=.
by rewrite conjg_set1 conjgM def_yx conjgK.
Qed.

(* This is Isaacs, Theorem 6.34(a2) *)
Theorem irr_induced_Frobenius_ker i : i != 0 -> 'Ind[G, K] 'chi_i \in irr G.
Proof.
move/inertia_Frobenius_ker/group_inj=> defK.
have [_ _ nsKG _] := Frobenius_kerP frobGK.
have/(_ i):= cfInd_constt_inertia_irr nsKG; rewrite defK => -> //.
by rewrite inE /= cfRes_id cfnorm_eq0 irr_neq0.
Qed.

(* This is Isaacs, Theorem 6.34(b) *)
Theorem Frobenius_Ind_irrP j :
  reflect (exists2 i, i != 0 & 'chi_j = 'Ind[G, K] 'chi_i)
          (~~ (K \subset cfker 'chi_j)).
Proof.
have [_ _ nsKG _] := Frobenius_kerP frobGK; have [sKG nKG] := andP nsKG.
apply: (iffP idP) => [not_chijK1 | [i nzi ->]]; last first.
  by rewrite cfker_Ind_irr ?sub_gcore // subGcfker.
have /neq0_has_constt[i chijKi]: 'Res[K] 'chi_j != 0 by exact: Res_irr_neq0.
have nz_i: i != 0.
  by apply: contraNneq not_chijK1 => i0; rewrite constt0_Res_cfker // -i0.
have /irrP[k def_chik] := irr_induced_Frobenius_ker nz_i. 
have: '['chi_j, 'chi_k] != 0 by rewrite -def_chik -cfdot_Res_l.
by rewrite cfdot_irr pnatr_eq0; case: (j =P k) => // ->; exists i.
Qed.

End Frobenius.
