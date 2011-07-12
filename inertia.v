(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop ssralg finset fingroup.
Require Import morphism perm automorphism action quotient zmodp center.
Require Import matrix mxalgebra mxrepresentation vector algC.
Require Import classfun character.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(******************************************************************************)
(* This file contains the definitions and properties of inertia groups:       *)
(*  (phi ^ y)%CH == the y-conjugate of phi : 'CF(G), i.e., the class function *)
(*                  mapping x ^ y to phi x, provided y normalises G. We take  *)
(*                  (phi ^ y)%CH = phi when y \notin 'N(G).                   *)
(* (phi ^: G)%CH == the sequence of all distinct y-conjugates of phi : 'CF(H) *)
(*                  for y in G.                                               *)
(*     'I_G[phi] == the inertia group of phi : CF(H) in G, i.e., the set of y *)
(*                  in G such that (phi ^ y)%CH = phi AND H :^ y = y.         *)
(******************************************************************************)

Reserved Notation "''I_' G [ f ]"
  (at level 8, G at level 2, format "''I_' G [ f ]").

Section ConjDef.

Variables (gT : finGroupType) (B : {set gT}) (phi : 'CF(B)) (y : gT).
Local Notation G := <<B>>.

Fact cfunConjg_subproof :
  is_class_fun G [ffun x => phi (if y \in 'N(G) then x ^ y^-1 else x)].
Proof.
apply: intro_class_fun => [x z _ Gz | x notGx].
  have [nGy | _] := ifP; last by rewrite cfunJgen.
  by rewrite -conjgM conjgC conjgM cfunJgen // memJ_norm ?groupV.
by rewrite cfun0gen //; case: ifP => // nGy; rewrite memJ_norm ?groupV.
Qed.
Definition cfunConjg := Cfun 1 cfunConjg_subproof.

End ConjDef.

Notation "f ^ y" := (cfunConjg f y) : character_scope.

Section Conj.

Variables (gT : finGroupType) (G : {group gT}).
Implicit Type phi : 'CF(G).

Lemma cfunConjgE phi y x : y \in 'N(G) -> (phi ^ y)%CH x = phi (x ^ y^-1)%g.
Proof. by rewrite cfunElock genGid => ->. Qed.

Lemma cfunConjgEnorm phi y x : y \in 'N(G) -> (phi ^ y)%CH (x ^ y) = phi x.
Proof. by move/cfunConjgE->; rewrite conjgK. Qed.

Lemma cfunConjg_out phi y : y \notin 'N(G) -> (phi ^ y = phi)%CH.
Proof.
by move/negbTE=> notNy; apply/cfunP=> x; rewrite !cfunElock genGid notNy.
Qed.

Lemma cfunConjgMnorm phi :
  {in 'N(G) &, forall y z, phi ^ (y * z) = (phi ^ y) ^ z}%CH.
Proof.
move=> y z nGy nGz.
by apply/cfunP=> x; rewrite !cfunConjgE ?groupM // invMg conjgM.
Qed.

(* Isaacs' 6.1.b *)
Lemma cfunConjgM L phi :
  G <| L -> {in L &, forall y z, phi ^ (y * z) = (phi ^ y) ^ z}%CH.
Proof. by case/andP=> _ /subsetP nGL; exact: sub_in2 (cfunConjgMnorm phi). Qed.

Lemma cfunConjg1 phi : (phi ^ 1)%CH = phi.
Proof. by apply/cfunP=> x; rewrite cfunConjgE ?group1 // invg1 conjg1. Qed.

Lemma cfunConjgK y : cancel ((@cfunConjg _ G)^~ y) ((@cfunConjg _ G)^~ y^-1%g).
Proof.
move=> phi; apply/cfunP=> x; rewrite !cfunElock groupV /=.
by case: ifP => -> //; rewrite conjgKV.
Qed.

Lemma cfunConjgKV y : cancel ((@cfunConjg _ G)^~ y^-1%g) ((@cfunConjg _ G)^~ y).
Proof. by move=> phi /=; rewrite -{2}[y]invgK cfunConjgK. Qed.

Lemma cfunConjg_cfun0 y : (0 ^ y)%CH = 0 :> 'CF(G).
Proof. by apply/cfunP=> x; rewrite !cfunElock. Qed.

Lemma cfunConjg_cfun1 y : (1 ^ y)%CH = 1 :> 'CF(G).
Proof.
apply/cfunP=> x; rewrite cfunElock // !cfun1E genGid.
by case: ifP => // nGy; rewrite memJ_norm ?groupV.
Qed.

Lemma cfunConjg_val1 phi y : (phi ^ y)%CH 1%g = phi 1%g.
Proof. by rewrite cfunElock conj1g if_same. Qed.

Lemma cfunConjg_Aut phi u y : cfunAut u (phi ^ y) = (cfunAut u phi ^ y)%CH.
Proof. by apply/cfunP=> x; rewrite !cfunElock. Qed.

Lemma cfunConjg_conjC phi y : (phi ^ y)^*%CH = (phi^* ^ y)%CH.
Proof. exact: cfunConjg_Aut. Qed.

End Conj.

Section Inertia.

Variable gT : finGroupType.

Definition inertia (B A : {set gT}) (phi : 'CF(B)) :=  
  [set y \in 'N_A(B) | (phi ^ y)%CH == phi].

Local Notation "''I_' G [ phi ]" := (inertia G phi) : group_scope.

Fact group_set_inertia (H G : {group gT}) (phi : 'CF(H)) : group_set 'I_G[phi].
Proof.
apply/group_setP; split; first by rewrite inE group1 /= cfunConjg1.
move=> y z /setIdP[/setIP[Gy nHy] /eqP n_phi_y] /setIdP[/setIP[Gz nHz] n_phi_z].
by rewrite 2!inE !groupM // cfunConjgMnorm // n_phi_y.
Qed.
Canonical inertia_group H G phi := Group (@group_set_inertia H G phi).

Local Notation "''I_' G [ f ]" := (inertia_group G f) : subgroup_scope.

Variables (G H : {group gT}).
Implicit Type phi : 'CF(H).

Lemma inertia_sub phi : 'I_G[phi] \subset G.
Proof. by rewrite ['I_G[_]]setIdE -setIA subsetIl. Qed.

Lemma norm_inertia phi : 'I_G[phi] \subset 'N(H).
Proof. by rewrite ['I_G[_]]setIdE setIAC subsetIr. Qed.

Lemma cfunConjg_eqE phi :
    H <| G ->
  {in G &, forall y z, (phi ^ y == phi ^ z)%CH = (z \in 'I_G[phi] :* y)}.
Proof.
case/andP=> _ nHG y z; rewrite mem_rcoset inE (setIidPl nHG) -groupV => Gy' Gz.
rewrite groupM // (can2_eq (cfunConjgK y) (cfunConjgKV y)) eq_sym.
by rewrite cfunConjgMnorm ?(subsetP nHG).
Qed.

Lemma inertia_center phi : H <| G -> 'Z(G) \subset 'I_G[phi].
Proof.
case/andP=> sHG nHG; apply/subsetP=> y /centerP[Gy cGy].
rewrite inE (setIidPl nHG) Gy.
apply/eqP/cfun_inP=> x Hx; rewrite cfunConjgE ?(subsetP nHG) //.
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
have [nHy | not_nHy] := boolP (y \in 'N(H)); last by rewrite !cfunConjg_out.
congr (_ * _); rewrite -{1}(normP nHy).
rewrite big_imset; last exact: in2W (conjg_inj y).
by apply: eq_bigr=> x _; rewrite !cfunConjgEnorm.
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
Lemma is_char_Conjg (chi : 'CF(H)) y : is_char chi -> is_char (chi ^ y).
Proof.
have [nHy | /cfunConjg_out-> //] := boolP (y \in 'N(H)).
case/is_charP=> rG ->; apply/is_charP.
have rGyP: mx_repr H (fun x => rG (x ^ y^-1)%g).
  split=> [|x1 x2 Hx1 Hx2]; first by rewrite conj1g repr_mx1.
  by rewrite conjMg repr_mxM ?memJ_norm ?groupV.
exists (Representation (MxRepresentation rGyP)) => /=.
by apply/cfunP=> x; rewrite cfunConjgE // !cfunE memJ_norm ?groupV.
Qed.

Lemma irr_Conjg i y : ('chi_i ^ y)%CH \in irr H.
Proof.
rewrite irr_cfdot_charE; last by rewrite is_char_Conjg ?is_char_irr.
by rewrite cfdot_Conjg cfdot_irr eqxx.
Qed.
 
Definition conjg_idx i y := irr_idx (fun i => 'chi[H]_i ^ y)%CH i.

Lemma conjg_idxE i y : 'chi_(conjg_idx i y) = ('chi_i ^ y)%CH.
Proof. by apply: irr_idxE => j; exact: irr_Conjg. Qed.

Lemma cfdot_irr_Conjg i y :
  H <| G -> y \in G -> '['chi_i, 'chi_i ^ y]_H = (y \in 'I_G['chi_i])%:R.
Proof.
move=> nsHG Gy; rewrite inE (setIidPl (normal_norm nsHG)) Gy eq_sym.
by rewrite -conjg_idxE cfdot_irr inj_eq //; exact: chi_inj.
Qed.

Definition cfclass (A : {set gT}) (phi : 'CF(A)) (B : {set gT}) := 
  [seq (phi ^ repr Tx)%CH | Tx <- enum (rcosets 'I_B[phi] B)%g].

Local Notation "phi ^: G" := (cfclass phi G) : character_scope.

Lemma cfclassP phi psi :
  reflect (exists2 y, y \in G & psi = phi ^ y)%CH (psi \in phi ^: G)%CH.
Proof.
apply: (iffP (imageP _ _ _)) => [[_ /rcosetsP[y Gy ->] ->] | [y Gy ->]].
  case: repr_rcosetP => z /setIdP[/setIP[Gz _] _].
  by exists (z * y)%g; rewrite ?groupM.
without loss nHy: y Gy / y \in 'N(H).
  have [nHy | /cfunConjg_out->] := boolP (y \in 'N(H)); first exact.
  by move/(_ 1%g); rewrite !group1 !cfunConjg1; exact.
exists ('I_G[phi] :* y); first by rewrite topredE -rcosetE mem_imset.
case: repr_rcosetP => z /setIdP[/setIP[_ nHz] /eqP Tz].
by rewrite cfunConjgMnorm ?Tz.
Qed.

Lemma cfclass_refl phi : phi \in (phi ^: G)%CH.
Proof. by apply/cfclassP; exists 1%g => //; rewrite cfunConjg1. Qed.

Lemma cfclass_uniq phi : H <| G -> uniq (phi ^: G)%CH.
Proof.
case/andP=> _ /subsetP nHG.
rewrite map_inj_in_uniq ?enum_uniq // => Ty Tz; rewrite !mem_enum.
move=> {Ty}/rcosetsP[y Gy ->] {Tz}/rcosetsP[z Gz ->].
rewrite -{2}(rcoset_repr _ y) -{2}(rcoset_repr _ z).
case: repr_rcosetP => u /setIdP[/setIP[Gu _] _].
case: repr_rcosetP => v /setIdP[/setIP[Gv _] _].
move=> eq_phi_uy_vz; apply: rcoset_transl; rewrite mem_rcoset.
rewrite 2!inE cfunConjgMnorm ?(groupM, groupV) ?nHG //=.
by rewrite eq_phi_uy_vz cfunConjgK.
Qed.

Lemma inertia1 : H <| G -> 'I_G[1 : 'CF(H)] = G.
Proof.
case/andP=> _ nHG; rewrite ['I_G[1]]setIdE (setIidPl nHG).
by apply/setIidPl/subsetP=> x Gx; rewrite inE cfunConjg_cfun1.
Qed.

Lemma cfclass1 : H <| G -> (1 ^: G)%CH = [:: 1 : 'CF(H)].
Proof.
move=> nsHG; rewrite /cfclass inertia1 // rcosets_id enum_set1 /=.
by rewrite cfunConjg_cfun1.
Qed.

Lemma cfclass_sum R idx (op : Monoid.com_law idx) (F : 'CF(H) -> R) i :
     H <| G ->
  \big[op/idx]_(j | 'chi_j \in ('chi_i ^: G)%CH) F 'chi_j
     = \big[op/idx]_(chi <- ('chi_i ^: G)%CH) F chi.
Proof.
move/cfclass_uniq=> chiGuniq; rewrite -big_map -big_filter; apply: eq_big_perm.
rewrite -[index_enum _]enumT map_tnth_enum uniq_perm_eq // => [|chi].
  by rewrite filter_uniq // uniq_free // free_irr.
by rewrite mem_filter; apply: andb_idr => /imageP[Tx _ ->]; exact: irr_Conjg.
Qed.

(* This is Isaacs, Theorem (6.2) *)
Lemma is_comp_Clifford i j :
     H <| G -> is_comp j ('Res[H, G] 'chi_i) ->
  'Res[H] 'chi_i = 
     '['Res[H] 'chi_i, 'chi_j] *: (\sum_(chi <- ('chi_j ^: G)%CH) chi).
Proof.
move=> nsHG chiHj; have [sHG /subsetP nHG] := andP nsHG.
rewrite -cfclass_sum //= big_mkcond.
rewrite {1}['Res _]cfun_cfdot_sum linear_sum /=; apply: eq_bigr => k _.
have [[y Gy ->] | ] := altP (cfclassP _ _); first by rewrite cfdot_Res_Conjg.
apply: contraNeq; rewrite scaler0 scalev_eq0 orbC => /norP[_ chiHk].
have{chiHk chiHj}: '['Res[H] ('Ind[G] 'chi_j), 'chi_k] != 0.
  rewrite /is_comp !cfdot_Res_l in chiHj chiHk *.
  apply: contraNneq chiHk; rewrite cfdot_sum_irr => /posC_sum_eq0/(_ i isT)/eqP.
  rewrite -cfdotC cfdotC mulf_eq0 conjC_eq0 (negbTE chiHj) /= => -> // i1.
  rewrite -cfdotC posC_isNatC //.
  by rewrite isNatC_mul ?isNatC_cfdot_char ?is_char_Ind ?is_char_irr //.
have ->: 'Res ('Ind[G] 'chi_j) = #|H|%:R^-1 *: (\sum_(y \in G) 'chi_j ^ y)%CH.
  rewrite (reindex_inj invg_inj); apply/cfun_inP=> x Hx.
  rewrite cfunResE // cfunIndE // cfunE sum_cfunE; congr (_ * _).
  by apply: eq_big => [y | y Gy]; rewrite ?cfunConjgE ?groupV ?invgK ?nHG.
rewrite cfdotZl mulf_eq0 cfdot_suml => /norP[_]; apply: contraR => not_chjGk.
rewrite big1 // => x Gx; apply: contraNeq not_chjGk.
rewrite -conjg_idxE cfdot_irr -neq0N_neqC; case: (_ =P k) => // <- _.
by rewrite conjg_idxE; apply/cfclassP; exists x.
Qed.

(* This is Isaacs' 6.7 *)
Lemma cfker_is_comp0 i : 
  H <| G -> is_comp 0 ('Res[H] 'chi[G]_i) -> H \subset cfker 'chi[G]_i.
Proof.
move=> nsHG /(is_comp_Clifford nsHG); have [sHG nHG] := andP nsHG.
rewrite chi0_1 cfdot_Res_l cfclass1 // big_seq1 cfunInd_normal1 //.
rewrite cfdotZr conjC_nat => def_chiH.
apply/subsetP=> x Hx; rewrite cfker_irrE inE (subsetP sHG) //=.
by rewrite -!(cfunResE _ sHG) // def_chiH !cfunE !cfun1E Hx group1.
Qed.

(* This is Isaacs' 6.8 *)
Lemma is_comp_val1_div i j : 
    H <| G -> is_comp j ('Res[H, G] 'chi_i) ->
  exists n, 'chi_i 1%g = n%:R * 'chi_j 1%g.
Proof.
move=> nsHG chiHj; have [sHG nHG] := andP nsHG.
rewrite -(cfunResE _ sHG) // {1}(is_comp_Clifford nsHG chiHj) cfunE sum_cfunE.
have /isNatCP[n ->]: isNatC '['Res[H] 'chi_i, 'chi_j].
  by rewrite isNatC_cfdot_char ?is_char_Res ?is_char_irr.
exists (n * size ('chi_j ^: G)%CH)%N; rewrite natr_mul -mulrA; congr (_ * _).
rewrite mulr_natl -[size _]card_ord big_tnth -sumr_const; apply: eq_bigr => k _.
by have /cfclassP[y Gy ->]:=  mem_tnth k (in_tuple _); rewrite cfunConjg_val1.
Qed.

Lemma cfclass_Ind phi psi :
  H <| G ->  psi \in (phi ^: G)%CH -> 'Ind[G] phi = 'Ind[G] psi.
Proof.
move=> nsHG /cfclassP[y Gy ->]; have [sHG /subsetP nHG] := andP nsHG.
apply/cfun_inP=> x Hx; rewrite !cfunIndE //; congr (_ * _).
rewrite (reindex_acts 'R _ (groupVr Gy)) ?astabsR //=.
by apply: eq_bigr => z Gz; rewrite conjgM cfunConjgE ?nHG.
Qed.

Lemma cfclass_size i : size ('chi[H]_i ^: G)%CH =  #|G : 'I_G['chi_i]|.
Proof. by rewrite size_map -cardE. Qed.

End Inertia.

Arguments Scope inertia [_ group_scope group_scope character_scope].
Arguments Scope cfclass [_ group_scope character_scope group_scope].
Notation "''I_' G [ phi ] " := (inertia G phi) : group_scope.
Notation "''I_' G [ phi ] " := (inertia_group G phi) : subgroup_scope.
Notation "phi ^: G" := (cfclass phi G) : character_scope.

Section MoreInertia.

Variables (gT : finGroupType) (G H : {group gT}) (i : Iirr H).
Let T := 'I_G['chi_i].

Lemma inertia_id : 'I_T['chi_i] = T.
Proof.
rewrite ['I_T[_]]setIdE -{1}[T](setIidPl (inertia_sub _ _)) -/T.
by rewrite -!setIA (setIA G) -setIdE setIid.
Qed.

Lemma cfclass_inertia : ('chi[H]_i ^: T)%CH = [:: 'chi_i].
Proof.
by rewrite /cfclass inertia_id rcosets_id enum_set1 /= repr_group cfunConjg1.
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

Hypothesis Hp : is_comp t ('Res[H] 'chi_p).

Variable c : Iirr G.

Hypothesis Hc : is_comp c ('Ind[G,T] 'chi_p).

Let ITC : is_char ('Res[T] 'chi_c).
Proof. by rewrite is_char_Res ?is_char_irr. Qed.

Let ITP : is_char ('Res[T] 'chi_p).
Proof. by rewrite is_char_Res ?is_char_irr. Qed.

Let IHC : is_char ('Res[H] 'chi_c).
Proof. by rewrite is_char_Res ?is_char_irr. Qed.

Let IHP : is_char ('Res[H] 'chi_p).
Proof. by rewrite is_char_Res ?is_char_irr. Qed.

Fact is_comp_inertia_restrict_is_comp_i : is_comp p ('Res[T] 'chi_c).
Proof.
by rewrite /is_comp cfdot_charC ?is_char_irr ?Frobenius_reciprocity.
Qed.

Fact is_comp_inertia_restrict_is_comp_g : is_comp t ('Res[H] 'chi_c).
Proof.
rewrite -(cfunRes_subset _ HsT TsG).
exact: is_comp_restrict is_comp_inertia_restrict_is_comp_i _.
Qed.

Let e := '['Res[H] 'chi_c, 'chi_t].

Let f := '['Res[H] 'chi_p, 'chi_t].

Let He : 'Res[H] 'chi_c = e *: (\sum_(f <- 'chi_t ^: G) f)%CH.
Proof. exact: (is_comp_Clifford HnG is_comp_inertia_restrict_is_comp_g). Qed.

Let Hf : 'Res[H] 'chi_p = f *: 'chi_t.
Proof. by have:= is_comp_Clifford HnT Hp; rewrite cfclass_inertia big_seq1. Qed.

Let He1 : 'chi_c 1%g = e * #|G : T|%:R * 'chi_t 1%g.
Proof.
rewrite -(cfunResE _ (normal_sub HnG)) // He cfunE -mulrA; congr (_ * _).
rewrite mulr_natl -cfclass_size -[size _]card_ord sum_cfunE big_seq big_tnth.
rewrite -sumr_const; apply: eq_big => k; first exact: mem_tnth.
by case/cfclassP=> y Gy ->; rewrite cfunConjg_val1.
Qed.

Let Hpsi1  : ('Ind[G] 'chi_p) 1%g = f * #|G : T|%:R * ('chi_t 1%g).
Proof. by rewrite -mulrA mulrCA cfunInd1 // -(cfunResE _ HsT) // Hf cfunE. Qed.

Fact cfdot_is_comp_inertia_is_comp : f = e.
Proof.
have le_f_e: f <= e.
  have: '['Res 'chi_p, 'chi_t] <= '['Res[H] ('Res[T] 'chi_c), 'chi_t].
    by apply: is_comp_cfdot_le is_comp_inertia_restrict_is_comp_i.
  rewrite Hf /= cfunRes_subset // He !cfdotZl cfdot_irr eqxx mulr1.
  rewrite -cfclass_sum // cfdot_suml (bigD1 t) ?cfclass_refl //= cfdot_irr eqxx.
  rewrite big1 ?addr0 ?mulr1 // => i /andP[_ neq_it].
  by rewrite cfdot_irr (negbTE neq_it).
apply: leC_anti=> //.
have: 0 < #|G : T|%:R * 'chi_t 1%g.
  by rewrite sposC_mul // ?ltC_irr1 // -(ltn_ltC 0).
move/leC_pmul2r=> <-; rewrite mulrA -He1 mulrA -Hpsi1.
have IIP: is_char ('Ind[G] 'chi_p) := is_char_Ind G (is_char_irr p).
case/(is_comp_charP _ IIP): Hc => chi' /= IC' ->.
by rewrite cfunE addrC -leC_sub addrK posC_isNatC ?isNatC_char1.
Qed.

Fact is_comp_inertia_induced_is_comp : 'Ind[G] 'chi_p = 'chi_c.
Proof.
have ICI: is_char ('Ind[G] 'chi_p) := is_char_Ind G (is_char_irr p).
case/(is_comp_charP _ ICI): Hc => chi' IC' /= Hchi'.
rewrite Hchi'; move/cfunP/(_ 1%g)/esym/eqP: Hchi'.
rewrite Hpsi1 cfdot_is_comp_inertia_is_comp -He1 cfunE addrC -subr_eq0 addrK.
by rewrite char1_eq0 // => /eqP->; rewrite addr0.
Qed.

End Chi.

Variable p : Iirr T.

Hypothesis Hp : is_comp t ('Res[H] 'chi_p).

Let cP : 'Ind[G] 'chi_p != 0.
Proof. by rewrite cfunInd_eq0 -?char1_eq0 ?is_char_irr ?irr1_neq0. Qed.

Let c := val (sigW (is_comp_neq0 cP)).

Let Hc : is_comp c ('Ind[G] 'chi_p).
Proof. exact: valP (sigW (is_comp_neq0 cP)). Qed.

(* This is 6.11 (a) *)
Lemma irr_is_comp_inertia : 'Ind[G] 'chi_p \in irr G.
Proof. by rewrite (is_comp_inertia_induced_is_comp Hp Hc); exact: irr_chi. Qed.

(* This is 6.11 (d) *)
Lemma cfdot_is_comp_inertia : 
 '['Res 'chi_p, 'chi_t] = '['Res ('Ind[G] 'chi_p), 'chi_t].
Proof. 
rewrite (is_comp_inertia_induced_is_comp Hp Hc).
by rewrite (cfdot_is_comp_inertia_is_comp Hp Hc).
Qed.

(* This is 6.11 (b) the domain of the induction is B *)
Lemma is_comp_is_comp_inertia : is_comp t ('Res ('Ind[G] 'chi_p)).
Proof. 
rewrite (is_comp_inertia_induced_is_comp Hp Hc).
by rewrite (is_comp_inertia_restrict_is_comp_g Hp Hc).
Qed.

(* This is 6.11 c *)
Lemma unique_is_comp_inertia (p' : Iirr T) :
  is_comp p' ('Res ('Ind[G] 'chi_p)) -> is_comp t ('Res 'chi_p') -> p' = p.
Proof.
rewrite (is_comp_inertia_induced_is_comp Hp Hc) => Cp' Ct.
have IC: is_char ('Res[T] 'chi_c) := is_char_Res T (is_char_irr c).
case/(is_comp_charP _ IC): Cp' => chi1 IC1 Hchi1.
apply: contraTeq isT => Dpsi.
have /(is_comp_charP _ IC1)[chi2 IC2 Hchi2]: is_comp p chi1.
  have: is_comp p ('Res[T] 'chi_c).
    exact: is_comp_inertia_restrict_is_comp_i.
  by rewrite /is_comp Hchi1 cfdotDl cfdot_irr (negPf Dpsi) add0r.
have: '['Res[H] 'chi_p, 'chi_t] < '['Res[H] ('Res[T] 'chi_c), 'chi_t].
  rewrite Hchi1 addrC Hchi2 !linearD !cfdotDl /=.
  rewrite -addrA addrC ltC_sub addrK sposC_addl //.
    by rewrite posC_isNatC ?isNatC_cfdot_char_irr ?is_char_Res.
  rewrite ltCE [~~ _]Ct posC_isNatC ?isNatC_cfdot_char_irr //.
  by rewrite is_char_Res ?is_char_irr.
rewrite cfdot_is_comp_inertia (is_comp_inertia_induced_is_comp Hp Hc).
by rewrite cfunRes_subset // ltCE eqxx.
Qed.

End S611A.

(* This is 6.11 b it is an injection *)
Lemma injective_is_comp_inertia (G H : {group gT}) (t : Iirr H) :
   H <| G ->
 {in [pred p | is_comp t ('Res[H, 'I_G['chi_t]] 'chi_p)] &,
    injective (fun p => 'Ind[G, 'I_G['chi_t]] 'chi_p)}.
Proof.
move=> HnG p p' Hp Hp' Heq; set T := 'I_G[_].
have TsG: T \subset G := inertia_sub G 'chi_t.
apply: (unique_is_comp_inertia HnG Hp' _ Hp).
have IC1: is_char ('Ind[G] 'chi_p) := is_char_Ind G (is_char_irr p).
have IC2: is_char ('Res[T] ('Ind[G] 'chi_p)) := is_char_Res _ IC1.
rewrite -Heq /is_comp cfdot_charC ?is_char_irr //.
rewrite Frobenius_reciprocity /= cfnorm_eq0 cfunInd_eq0 ?is_char_irr //.
exact: (free_notin0 (free_irr _) (irr_chi p)).
Qed.

(* 6.11 b the inverse function *)
Definition inertia_induced_inv (G H : {group gT}) t (chi : 'CF(G)) :=
  odflt 0 (pick [pred t' | is_comp t ('Res[H] 'chi_t') && 
                           is_comp t' ('Res['I_G['chi_t]] chi)]).

Let inertia_coord (G H : {group gT}) (t : Iirr H) (c : Iirr G) :
    H <| G -> [pred p | is_comp t ('Res[H] 'chi_p) &&
                        is_comp p ('Res['I_G['chi_t]] 'chi_c)] =1 xpred0 ->
   '['Res[H] 'chi_c, 'chi_t] == 0.
Proof.
set T := 'I_G['chi_t] => HnG HH.
have HsT: H \subset T := sub_inertia 'chi_t HnG.
rewrite -(cfunRes_subset _ HsT) ?inertia_sub //= -/T.
rewrite ['Res 'chi_c]cfun_cfdot_sum linear_sum cfdot_suml big1 //= => i _.
move/negbT: (HH i); apply: contraNeq; rewrite linearZ cfdotZl mulf_eq0 //=.
by rewrite orbC negb_or.
Qed.

Lemma inertia_induced_inv_is_comp_h (G H : {group gT}) t c :
    H <| G -> is_comp t ('Res[H, G] 'chi_c) ->
  is_comp t ('Res[H] 'chi_(inertia_induced_inv t 'chi_c)).
Proof.
move=> HnG Ct.
rewrite /inertia_induced_inv; case: pickP => [_ /andP[] //| HH].
by case/negP: Ct; apply: inertia_coord.
Qed.

Lemma inertia_induces_inv_is_comp_i (G H : {group gT}) t c :
    H <| G -> is_comp t ('Res[H, G] 'chi_c) ->
  is_comp (inertia_induced_inv t 'chi_c) ('Res['I_G['chi_t]] 'chi_c).
Proof.
move=> HnG Ct.
rewrite /inertia_induced_inv; case: pickP => [_ /andP[] //| HH].
by case/negP: Ct; apply: inertia_coord.
Qed.

(* This is 6.11 b the surjective part *)
Lemma inertia_induced_invE (G H : {group gT}) (t : Iirr H) (c : Iirr G) :
    H <| G -> is_comp t ('Res[H] 'chi_c) ->
  'Ind[G] 'chi_(inertia_induced_inv t 'chi_c) = 'chi_c.
Proof.
move=> HnG Cc.
apply: is_comp_inertia_induced_is_comp => //.
  exact: inertia_induced_inv_is_comp_h.
rewrite /is_comp -Frobenius_reciprocity.
rewrite cfdot_charC ?is_char_Res ?is_char_irr //.
exact: inertia_induces_inv_is_comp_i.
Qed.

End S611.