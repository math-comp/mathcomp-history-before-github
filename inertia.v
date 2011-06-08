(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop ssralg finset zmodp.
Require Import fingroup morphism perm automorphism center.
Require Import matrix mxalgebra mxrepresentation vector algC.
Require Import classfun character.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(**************************************************************************)
(*                                                                        *)
(* This file contains the definitions and properties of inertia group     *)
(*                                                                        *)
(*                                                                        *)
(*  (f ^ g)%CH : the group conjugate function                             *)
(*                                                                        *)
(* 'I_(G)[f] :  the set of elements of G such that f ^ g = f              *)
(*                                                                        *)
(* cconjugates G f : the sequence of all distinct conjugates of f         *)
(*                   by elements of G                                     *)
(*                                                                        *)
(**************************************************************************)

Section Conj.

Variable gT : finGroupType.

Implicit Type f : {cfun gT}.

Definition cfun_conj f (g : gT) : {cfun _} :=
  [ffun h => f (h^(g^-1))].

Notation "f ^ g" := (cfun_conj f g) : character_scope.

Lemma cfun_conjE : forall f g h, (f ^ g)%CH h = f (h^(g^-1)).
Proof. by move=> f g h; rewrite ffunE. Qed.

(* Isaacs' 6.1.a *)
Lemma memc_cfun_conj : forall (G : {group gT}) f g,
  g \in G -> f \in 'CF(G) -> (f^g)%CH \in 'CF(G).
Proof.
move=> G f g GiG CFf.
apply/cfun_memP; split=> [h HniG|h1 h2 H2iG].
  rewrite ffunE (cfun0 CFf) //; apply/negP=> HGiG; case/negP: HniG.
  by rewrite -(groupJr h (groupVr GiG)).
by rewrite !ffunE !(cfunJ _ CFf, groupV) // groupJ.
Qed.

(* Isaacs' 6.1.b *)
Lemma cfun_conjM : forall f (g h : gT),
  (f ^ (g * h) = (f ^ g) ^ h)%CH.
Proof. by move=> f g h; apply/ffunP=> k; rewrite !cfun_conjE invMg conjgM. Qed.

Lemma cfun_conj1 : forall f, (f^1)%CH = f.
Proof. by move=> f; apply/ffunP=> g; rewrite ffunE invg1 conjg1. Qed.

Lemma cfun_conj_val1 : forall f g, (f^g)%CH 1%g = f 1%g.
Proof. by move=> f g; rewrite ffunE conj1g. Qed.

Lemma cfun_conj_conjC : forall f (g : gT),
  (f^g)^*%CH = (f^* ^ g)%CH.
Proof. by move=> f g; apply/ffunP=> h; rewrite !ffunE. Qed.

End Conj.

Notation "f ^ g" := (cfun_conj f g) : character_scope.

Section Inertia.

Variable gT : finGroupType.

Definition inertia (G : {set gT}) (f : {cfun gT}) :=  
  [set g \in G | (f ^ g)%CH == f].

Local Notation "'I_( G )[ f ]" := (inertia G f).

Lemma group_set_inertia : forall (G : {group gT}) f, group_set 'I_(G)[f].
Proof.
move=> G f; rewrite /inertia; apply/andP; split.
  rewrite inE group1; apply/eqP; apply/ffunP=> g.
  by rewrite ffunE invg1 conjg1.
apply/subsetP=> p; case/imset2P=> g1 g2; rewrite !inE.
case/andP=> G1iG CF1; case/andP=> G2iG CF2 ->; rewrite groupM //.
apply/eqP; apply/ffunP=> h; rewrite ffunE invMg conjgM.
move/ffunP: (eqP CF1); move/(_ (h^(g2^-1))); rewrite ffunE => ->.
by move/ffunP: (eqP CF2); move/(_ h); rewrite ffunE => ->.
Qed.

Canonical Structure inertia_group G f := Group (group_set_inertia G f).

Local Notation "'I_( G )[ f ]" := (inertia_group G f) : subgroup_scope.

Variable (G H : {group gT}).

Lemma inertia_sub : forall f, 'I_(G)[f] \subset G.
Proof. 
by move=> t; apply/subsetP=> g; rewrite inE; case/andP.
Qed.

Lemma cfun_conj_eqE : forall f (g h : gT), 
  g \in G -> h \in G -> (f^g == f^h)%CH = (h \in ('I_(G)[f] :* g)).
Proof.
move=> f g h GiG HiG; apply/eqP/rcosetP=> [Hx|]; last first.
  case=> g'; rewrite inE; case/andP=> G'iG; move/eqP=> CCi ->.
  apply/ffunP=> h'; rewrite ffunE -{1}CCi ffunE -conjgM.
  by rewrite cfun_conjE invMg.
exists (h * g^-1)%g; last by rewrite -mulgA mulVg mulg1.
rewrite inE !(groupM,groupV) //; apply/eqP; apply/ffunP=> g'.
rewrite ffunE invMg invgK conjgM.
move/ffunP: Hx; move/(_ (g'^g)); rewrite !cfun_conjE => <-.
by rewrite -conjgM mulgV conjg1.
Qed.

Lemma inertia_center : forall f,
  f \in 'CF(H) -> H <| G -> 'Z(G) \subset ('I_(G)[f]).
Proof.
move=> f FcF HnG.
apply/subsetP=> g; case/centerP=> GiG Cg; rewrite inE GiG.
apply/eqP; apply/ffunP=> h; rewrite ffunE.
case: (boolP (h \in H))=> [HiG|HniG].
  rewrite !conjgE invgK mulgA Cg ?(subsetP (normal_sub HnG)) //.
  by rewrite -mulgA mulgV mulg1.
rewrite !(cfun0 FcF) //.
by rewrite memJ_norm // (subsetP (normal_norm HnG)) // groupV.
Qed.

Lemma subset_inertia : forall f, f \in 'CF(H) -> H <| G -> H \subset 'I_(G)[f].
Proof.
move=> f FcF HnG; apply/subsetP=> h1 H1iH.
rewrite inE (subsetP (normal_sub HnG)) //.
apply/eqP; apply/ffunP=> h2; case: (boolP (h2 \in H))=> [H2iH|H2niH].
  by rewrite ffunE (cfunJ _ FcF) // groupV.
rewrite ffunE !(cfun0 FcF) //.
apply/negP=> HH; case/negP: H2niH.
by rewrite -(groupJr _ (groupVr H1iH)).
Qed.

(* Isaacs' 6.1.c *)
Lemma cfun_conj_inner : forall (f1 f2 : {cfun gT}) (g : gT),
 H <| G -> g \in G -> ('[f1 ^ g, f2 ^ g]_H = '[f1, f2]_H)%CH.
Proof.
move=> f1 f2 g HnG GiG; rewrite !inner_prodE.
congr (_ * _).
rewrite (reindex (conjg^~ g)); last first.
  by exists (conjg^~ g^-1%g)=> h; rewrite -conjgM (mulVg,mulgV) conjg1.
apply: eq_big=> [|h HiG].
  by move=> h; apply: memJ_norm; apply: (subsetP (normal_norm HnG)).
by rewrite !cfun_conjE -!conjgM mulgV conjg1.
Qed.
 
(* Isaacs' 6.1.d *)
Lemma cfun_conj_inner_restrict : forall (f1 f2 : {cfun _}) (g : gT),
 H <| G -> f1 \in 'CF(G) ->  g \in G -> 
   ('['Res[H] f1, f2 ^ g]_H = '['Res[H] f1, f2]_H)%CH.
Proof.
move=> f1 f2 g HnG CFf GiG.
rewrite -['[_,f2]_H](cfun_conj_inner _ _ HnG GiG).
rewrite !inner_prodE; congr (_ * _).
apply: eq_bigr=> h HiH; congr (_ * _); rewrite !ffunE (cfunJ _ CFf) ?groupV //.
by rewrite memJ_norm // (subsetP (normal_norm HnG)) // groupV.
Qed.

(* Isaac's 6.1.e *)
Lemma is_char_conj : forall chi  g, 
  is_char H chi -> H <| G -> g \in G -> is_char H (chi^g)%CH.
Proof.
move=> chi g; case/is_charP=> n [rG <-] HnG GiG.
have mx_reprj: mx_repr H (fun x => rG (x^(g^-1%g))).
  split=> [|h1 h2 H1iH H2iH]; first by rewrite conj1g repr_mx1.
  by rewrite conjMg repr_mxM ?(memJ_norm, groupV, (subsetP (normal_norm HnG))).
apply/is_charP; exists n; exists (MxRepresentation mx_reprj).
apply/ffunP=> h.
by rewrite !ffunE ?(memJ_norm, groupV, (subsetP (normal_norm HnG))).
Qed.

Lemma irr_cfun_conj : forall  (i : Iirr H) g,
  H <| G -> g \in G -> (('xi_i) ^ g)%CH \in irr H.
Proof.
move=> i g HnG GiG.
rewrite irr_inner_prod_charE ?(is_char_conj,is_char_irr) //.
by rewrite cfun_conj_inner // irr_orthonormal eqxx.
Qed.
 
Definition irr_conj (i : Iirr H) g := 
  irr_of_socle (socle_of_cfun H (('xi_i)^g)%CH).

Lemma irr_conjE : forall (i : Iirr H) g,
  H <| G -> g \in G -> 'xi_(irr_conj i g) = (('xi_i) ^ g)%CH.
Proof.
move=> i g HnG GiG.
case/irrP: (irr_cfun_conj i HnG GiG)=> j Hj.
by rewrite /irr_conj -Hj socle_of_cfunE irr_of_socleE Hj.
Qed.

Lemma is_irr_inner : forall (i : Iirr H) g, H <| G -> g \in G -> 
  '['xi_i, (('xi_i) ^ g)%CH]_H = (g \in 'I_(G)['xi_i])%:R.
Proof.
move=> i g HnG GiG.
rewrite -(irr_conjE i HnG GiG) irr_orthonormal.
rewrite inE GiG eq_sym /=; congr (_%:R); congr nat_of_bool.
rewrite -irr_conjE //.
by apply/eqP/eqP=> [->|] //; exact: xi_inj.
Qed.

Definition cconjugates (G : {set gT}) (f : {cfun gT}) := 
 map (fun i => (f ^ (repr i))%CH)
  (filter (fun i => i \in (mem (rcosets 'I_(G)[f] G)))
   (index_enum (set_of_finType (FinGroup.finType gT)))).

Lemma cconjugatesP : forall f1 f2,
  reflect (exists2 g : gT, g \in G & f2 = (f1 ^ g)%CH) 
          (f2 \in cconjugates G f1).
Proof.
move=> f1 f2.
have F1: forall g, g \in G -> repr ('I_(G)[f1] :* g) \in G.
  move=> g GiG; suff: 'I_(G)[f1] :* g \subset G.
    by move/subsetP; apply; exact: mem_repr_rcoset.
  apply/subsetP=> h; case/rcosetP=> h1 H1iG->; rewrite groupM //.
  by apply: (subsetP (inertia_sub f1)).
apply: (iffP idP)=> [|[g GiG ->]].
  case/mapP=> C; rewrite mem_filter.
  case/andP; case/rcosetsP=> g GiG -> _ ->.
  by exists (repr ('I_(G)[f1] :* g))=> //; exact: F1.
have:= (mem_repr_rcoset ('I_(G)[f1]) g).
rewrite -cfun_conj_eqE ?F1 //.
move/eqP->; apply: map_f.
  rewrite mem_filter; apply/andP; split; first by apply/rcosetsP; exists g.
by rewrite /index_enum -enumT mem_enum.
Qed.

Lemma mem_cconjugates : forall f, f \in cconjugates G f.
Proof.
by move=> f; apply/cconjugatesP; exists 1%g=> //; rewrite cfun_conj1.
Qed.

Lemma unique_cconjugates : forall f, uniq (cconjugates G f).
Proof.
move=> f; rewrite map_inj_in_uniq.
  by apply: filter_uniq; rewrite /index_enum -enumT; exact: enum_uniq.
have F1: forall g, g \in G -> repr ('I_(G)[f] :* g) \in G.
  move=> g GiG; suff: 'I_(G)[f] :* g \subset G.
    by move/subsetP; apply; exact: mem_repr_rcoset.
  apply/subsetP=> h; case/rcosetP=> h1 H1iG->; rewrite groupM //.
  by apply: (subsetP (inertia_sub f)).
move=> g=> C.
rewrite mem_filter; case/andP; case/rcosetsP=> h1 H1iG -> _.
rewrite mem_filter; case/andP; case/rcosetsP=> h2 H2iG -> _.
move=> HH; apply: sym_equal; apply: rcoset_transl.
rewrite -cfun_conj_eqE //.
have: (f ^ h1)%CH == (f ^ repr ('I_(G)[f] :* h1))%CH.
  by rewrite cfun_conj_eqE ?(mem_repr_rcoset,F1).
move/eqP->.
by rewrite HH eq_sym cfun_conj_eqE ?(mem_repr_rcoset,F1).
Qed.

Lemma cconjugates1 : H <| G ->  cconjugates G ('1_H) = [::'1_H].
Proof.
move=> HnG.
have: forall f, f \in cconjugates G ('1_H) -> f = '1_H .
  move=> f; case/cconjugatesP=> g GiG ->.
  apply/ffunP=> h; rewrite ffunE !cfuniE.
  (case: (boolP (_ \in _))=> HH; case: (boolP (_ \in _)))=> // [|HH1]; 
       [case/negP|case/negP:HH]; last first.
      case/normalP: HnG=> _; move/(_ _ (groupVr GiG))<-. 
      by apply/imsetP; exists h.
  rewrite -[h]conjg1 -[1%g](mulKg g) mulg1 conjgM.
  case/normalP: HnG=> _; move/(_ _ (GiG))<-. 
  by apply/imsetP; exists (h^g^-1)%g.
move: (mem_cconjugates ('1_H)) (unique_cconjugates ('1_H)).
case: cconjugates=> // f1 [|f2 s]; first by rewrite inE; move/eqP->.
move=> _ /=; case/andP=> HH _ HH1; case/negP: HH.
by rewrite /= (HH1 f1) ?(inE,eqxx) // (HH1 f2) ?(inE,eqxx,orTb,orbT).
Qed.

Lemma cconjugates_sum : forall (R : Type) (idx : R) (op : Monoid.com_law idx) 
                              (F: _ -> R) (i : Iirr H),
   H <| G ->
   \big[op/idx]_(j < Nirr H | 'xi_j \in cconjugates G 'xi_i) F 'xi_j = 
   \big[op/idx]_(j <- cconjugates G 'xi_i) F j.
Proof.
move=> R idx op F i HnG.
set u := \big[op/idx]_(j <- cconjugates G 'xi_i) F j.
rewrite -big_map -big_filter.
apply: eq_big_perm. 
apply: uniq_perm_eq; try apply: unique_cconjugates.
  apply: filter_uniq.
  rewrite map_inj_uniq; last exact: xi_inj.
  by rewrite -[index_enum _]enumT enum_uniq.
move=> j; apply/idP/idP; rewrite mem_filter; first by case/andP.
move=> HH; apply/andP; split=> //.
case/cconjugatesP: HH => g GiG->.
rewrite -(irr_conjE _ HnG GiG).
apply: map_f=> //.
by rewrite /index_enum -enumT  mem_enum.
Qed.

(* This is Isaacs 6.2 *)
Lemma is_comp_clifford :  forall i j,
   H <| G -> is_comp j ('Res[H] 'xi[G]_i) ->
  'Res[H] 'xi[G]_i = 
     '['Res[H] 'xi_i, 'xi[H]_j]_H *: (\sum_(f <- cconjugates G 'xi[H]_j) f).
Proof.
move=> i j HnG IC.
rewrite -(cconjugates_sum ) //=.
have CFchi: 'Res[H] 'xi_i \in 'CF(H).
  apply: memc_is_char; apply: is_char_restrict (is_char_irr _).
  by apply: normal_sub.
rewrite {1}(ncoord_sum CFchi).
rewrite (bigID (fun i : Iirr H => 'xi_i \in cconjugates G 'xi_j)) /=.
rewrite [\sum_(i | _ \notin _)_]big1 ?addr0=> [|k].
  rewrite scaler_sumr; apply: eq_bigr=> k Hk.
  rewrite (ncoord_inner_prod _ CFchi).
  case/cconjugatesP: Hk => g GiG ->.
  by rewrite cfun_conj_inner_restrict //; exact: memc_irr.
move=> HH.
have: '['Res[H] ('Ind[G,H] 'xi_j), 'xi_k]_H = 0.
  have->: 'Res[H] ('Ind[G,H] 'xi_j) = 
               #|H|%:R^-1 *: ((\sum_(c \in G) ('xi_j ^ c)%CH)).
    rewrite (reindex invg); last by exists invg=> g; rewrite invgK.
    apply/ffunP=> h; rewrite !(ffunE,sum_ffunE).
    case: (boolP (_ \in _))=> HiH; last first.
      rewrite mul0r big1 ?(scaler0) // => h1 H1iG.
      rewrite ffunE (cfun0 (memc_irr _)) // invgK.
      apply/negP=> HH1; case/negP: HiH.
      rewrite -[h]conjg1 -[1%g](mulgK h1) mul1g conjgM.
      move/normalP: HnG; case=> _; move/(_ _ H1iG) <-.
      by apply/imsetP; exists (h^ h1)%g.
    rewrite mul1r; congr (_ * _); apply: eq_big=> g1; first by rewrite groupV.
    by rewrite !(ffunE,invgK).
  rewrite -inner_prodbE linearZ linear_sum; rewrite big1 ?scaler0 // => g GiG.
  rewrite /= inner_prodbE -(irr_conjE _ HnG GiG) irr_orthonormal.
  case: eqP=> // HH1; case/negP: HH; rewrite -HH1 irr_conjE //.
  by apply/cconjugatesP; exists g.
rewrite (ncoord_inner_prod _ CFchi).
have CFInd: ('Ind[G, H] 'xi_j) \in 'CF(G).
   by apply: (memc_induced (normal_sub HnG)); exact: memc_irr.
rewrite {1}(ncoord_sum CFInd) linear_sum /=.
rewrite -inner_prodbE linear_sum /= => HH1. 
have: '['Res[H] (ncoord i ('Ind[G, H] 'xi_j) *: 'xi_i), 'xi_k]_H = 0.
  apply: (posC_sum_eq0 _ HH1)=> [j1 _|]; last first.
    by rewrite /index_enum -enumT mem_enum.
  apply: posC_isNatC.
  set u := 'Res[_] _; suff ICu: is_char H u.
    by apply: inner_prod_char_nat=> //; exact: is_char_irr.
  apply: (is_char_restrict (normal_sub HnG)).
  have II: is_char G ('Ind[G, H] 'xi_j).
    by apply: is_char_induced (is_char_irr _) (normal_sub _).
  case/isNatCP: (isNatC_ncoord_char j1 II)=> /= n ->.
  by rewrite scaler_nat is_char_scal // is_char_irr.
rewrite linearZ /= -inner_prodbE linearZ /= inner_prodbE.
move/eqP; rewrite mulf_eq0; case/orP; last first.
  by move/eqP->; rewrite scale0r.
move: IC.
rewrite /is_comp (ncoord_inner_prod _ CFchi) (ncoord_inner_prod _ CFInd).
rewrite inner_prod_charC ?(is_char_restrict (normal_sub HnG), is_char_irr) //.
rewrite (frobenius_reciprocity (normal_sub HnG)) ?memc_irr // => HH2 HH3.
by case/negP: HH2.
Qed.

(* This is Isaacs' 6.7 *)
Lemma cker_is_comp1 : forall i : Iirr G, 
  H <| G -> is_comp (0 : Iirr H) ('Res[H] 'xi[G]_i) -> H \subset cker G 'xi[G]_i.
Proof.
move=> chi HnG IC; apply/subsetP=> h HiH.
rewrite cker_irrE inE (subsetP (normal_sub HnG)) //.
move: (is_comp_clifford HnG IC).
rewrite -cfuni_xi0 cconjugates1 // big_cons big_nil addr0=> HH.
move/ffunP: (HH); move/(_ 1%g).
rewrite ffunE !cfuniE group1 mul1r.
rewrite [X in _ = X]ffunE cfuniE group1 [_ *: _]mulr1=> HH1.
move/ffunP: HH; move/(_ h).
rewrite -HH1 ffunE !cfuniE HiH mul1r => ->.
by rewrite ffunE cfuniE HiH [_ *: _]mulr1 eqxx.
Qed.

(* This is Isaacs' 6.8 *)
Lemma is_comp_val1_div : forall i j, 
  H <| G -> is_comp j ('Res[H] 'xi[G]_i) -> 
    exists n: nat, 'xi[G]_i 1%g = n%:R * 'xi[H]_j 1%g.
Proof.
move=> i j HnG IC.
exists (getNatC ('['Res[H] 'xi_i, 'xi_j]_ H) * (size (cconjugates G 'xi_j)))%N.
rewrite natr_mul.
have IC1: is_char H ('Res[H] 'xi_i).
  by apply: is_char_restrict (normal_sub _) (is_char_irr _).
move: (inner_prod_char_nat IC1 (is_char_irr j)).
rewrite /isNatC; move/eqP<-.
have->: 'xi_i 1%g = ('Res[H] 'xi_i) 1%g by rewrite !ffunE !(group1,mul1r).
rewrite {1}(is_comp_clifford HnG IC).
rewrite ffunE -mulrA; congr (_ * _).
rewrite sum_ffunE ffunE.
have: forall f, f \in cconjugates G 'xi_j -> f 1%g = 'xi_j 1%g.
  by move=> f; case/cconjugatesP=> g GiG ->; rewrite ffunE conj1g.
elim: (cconjugates _ _)=> [|f l IH HF]; first by rewrite big_nil mul0r.
rewrite big_cons HF ?(inE,eqxx) // IH=> [|f1 Hf1].
  by rewrite /= -[(size _).+1]add1n /= natr_add mulr_addl mul1r.
by rewrite HF // inE Hf1 orbT.
Qed.

Lemma cconjugates_induced : forall (f1 f2 : {cfun gT}),
   H <| G ->  f1 \in 'CF(H) -> f2 \in 'CF(H) -> f2 \in cconjugates G f1 ->  
   'Ind[G,H] f1 = 'Ind[G,H] f2.
Proof.
move=> f1 f2 HnG Cf1 Cf2 HH; case/cconjugatesP: HH Cf2=> g GiG -> Cf2.
apply/ffunP=> h; case: (boolP (h \in G))=> [HiG| HniG]; last first.
rewrite !(cfun0 (memc_induced _ _)) ?(normal_sub HnG) //.
rewrite !ffunE; congr (_ * _).
rewrite (reindex (mulg^~ g^-1%g)); last first.
  by exists (mulg^~ g)=> h1 _; rewrite -mulgA (mulgV,mulVg) mulg1.
apply: eq_big=> [|h1 H1iG]; last by rewrite cfun_conjE conjgM.
by move=> h1 /=; rewrite groupMr // groupV.
Qed.

Lemma cconjugates_size : forall (i : Iirr H), 
  size (cconjugates G 'xi_i) =  #|G : 'I_(G)['xi_i]|.
Proof.
move=> i.
suff->: size(cconjugates G 'xi_i) = 
       \big[addn/0%N]_(i <- cconjugates G 'xi_i) 1%N.
  rewrite big_map big_filter /=.
  rewrite big_const /= /indexg.
  by elim: #|_|=> //= n ->.
elim: cconjugates=> [|f1 l /= ->]; first by rewrite big_nil.
by rewrite big_cons.
Qed.

End Inertia.

Notation "''I_(' G ) [ f ] " := (inertia G f) 
  (at level 8, format "''I_(' G ) [ f ]").

Notation "''I_(' G ) [ f ] " := (inertia_group G f) 
  (at level 8, format "''I_(' G ) [ f ]") : subgroup_scope.

Section MoreInertia.

Variable gT : finGroupType.

Lemma cconjugates_inertia : forall (G H : {group gT}) (i : Iirr H),
   cconjugates 'I_(G)['xi_i] 'xi_i = [::'xi_i].
Proof.
move=> G H i.
set T := 'I_(G)['xi_i]%G.
have: forall f, f \in cconjugates T 'xi_i -> f = 'xi_i.
  move=> f; case/cconjugatesP=> g.
  by rewrite inE; case/andP=> _; move/eqP->.
move: (mem_cconjugates T 'xi_i) (unique_cconjugates T 'xi_i) => /=. 
case: cconjugates=> // f1 [|f2 s]; first by rewrite inE; move/eqP->.
move=> _ /=; case/andP=> HH _ HH1; case/negP: HH.
by rewrite /= (HH1 f1) ?(inE,eqxx) // (HH1 f2) ?(inE,eqxx,orTb,orbT).
Qed.

End MoreInertia.

Section S611.

Variable (gT : finGroupType).

Section S611A.

Variable (H G : {group gT}).

Variable t : Iirr H.

Let T := 'I_(G)['xi_t]%G.

Hypothesis HnG : H <| G.

Let TsG := inertia_sub G 'xi_t.

Let HsT : H \subset T.
Proof. by apply: subset_inertia=> //; exact: memc_irr. Qed.

Let HnT : H <| T.
Proof.
apply: normalS (HnG); last by exact: inertia_sub.
by apply: subset_inertia=> //; exact: memc_irr.
Qed.

Section Chi.

Variable p : Iirr T.

Hypothesis Hp : is_comp t ('Res[H] 'xi_p).

Variable c : Iirr G.

Hypothesis Hc : is_comp c ('Ind[G,T] 'xi_p).

Let ITC : is_char T ('Res[T] 'xi_c).
Proof. by apply: (is_char_restrict TsG (is_char_irr _)). Qed.

Let ITP : is_char T ('Res[T] 'xi_p).
Proof. by apply: (is_char_restrict _ (is_char_irr _)). Qed.

Let IHC : is_char H ('Res[H] 'xi_c).
Proof. by apply: (is_char_restrict (normal_sub _) (is_char_irr _)). Qed.

Let IHP : is_char H ('Res[H] 'xi_p).
Proof. by apply: (is_char_restrict _ (is_char_irr _)). Qed.

Fact is_comp_inertia_restrict_is_comp_i : is_comp p ('Res[T] 'xi_c).
Proof.
have FF := memc_restrict TsG (memc_is_char (is_char_irr c)).
rewrite /is_comp (ncoord_inner_prod _ FF).
move: Hc.
have FF1 := memc_induced TsG (memc_irr p).
rewrite /is_comp (ncoord_inner_prod _ FF1).
rewrite -frobenius_reciprocity ?memc_irr //.
by rewrite inner_prod_charC ?(is_char_restrict TsG,is_char_irr).
Qed.

Fact is_comp_inertia_restrict_is_comp_g : is_comp t ('Res[H] 'xi_c).
Proof.
have: '['Res[H] 'xi_p, 'xi_t]_ H <= '['Res[H] ('Res[T] 'xi_c), 'xi_t]_ H.
  by apply: is_comp_inner_prod_le is_comp_inertia_restrict_is_comp_i.
rewrite crestrict_subset //.
rewrite -!(ncoord_inner_prod _ (memc_is_char _)) //.
move: Hp; rewrite /is_comp /=.
case/isNatCP: (isNatC_ncoord_char t IHP)=> n ->.
case/isNatCP: (isNatC_ncoord_char t IHC)=> m ->.
by rewrite -!neq0N_neqC -leq_leC; case: m=> //; case: n.
Qed.

Let e := '['Res[H] 'xi_c, 'xi_t]_ H.

Let f := '['Res[H] 'xi_p, 'xi_t]_ H.

Let He : 'Res[H] 'xi_c = e *: ((\sum_(f <- cconjugates G 'xi_t) f)).
Proof. exact: (is_comp_clifford HnG is_comp_inertia_restrict_is_comp_g). Qed.

Let Hf  : 'Res[H] 'xi_p = f *: 'xi_t.
Proof.
move: (is_comp_clifford  HnT Hp).
rewrite cconjugates_inertia.
by rewrite big_cons big_nil addr0.
Qed.

Let He1 : 'xi_c 1%g = e * #|G : T|%:R * ('xi_t 1%g).
Proof.
move/ffunP: He; move/(_ 1%g).
rewrite ffunE !cfuniE group1 mul1r => ->.
rewrite ffunE sum_ffunE ffunE -mulrA; congr (_ * _).
rewrite -cconjugates_sum //=.
rewrite (eq_bigr (fun (i: Iirr H) => 'xi_t 1%g))=> [|i]; last first.
  case/cconjugatesP=> g GiG ->.
  by rewrite cfun_conj_val1.
rewrite (cconjugates_sum _ (fun i : {cfun _} => 'xi_t 1%g)) //=.
rewrite -cconjugates_size.
elim: cconjugates=> [|f1 l IH].
  by rewrite big_nil mul0r.
by rewrite big_cons IH /= -[(size _).+1]add1n natr_add mulr_addl mul1r.
Qed.

Let Hpsi1  : ('Ind[G, T] 'xi_p) 1%g = f * #|G : T|%:R * ('xi_t 1%g).
Proof.
have IGI: is_char G ('Ind[G,T] 'xi_p).
  by apply: is_char_induced=> //; exact: is_char_irr.
rewrite ffunE.
rewrite (eq_bigr (fun (c : gT) => 'xi_p 1%g))=> [|g GiG]; last first.
  by rewrite conj1g.
rewrite sumr_const.
move/ffunP: Hf; move/(_ 1%g).
rewrite ffunE !cfuniE group1 mul1r => ->.
rewrite ffunE.
apply: (mulfI (neq0GC T)).
rewrite mulrA mulfV ?neq0GC // mul1r. 
rewrite mulrCA  mulrA -[_ *+ #|_|]mulr_natl mulrA; congr (_ * _).
rewrite [_ * f]mulrC -[(f * _) * _]mulrA [#|_ : _|%:R * _]mulrC.
by rewrite -natr_mul LaGrange.
Qed.

Fact inner_prod_is_comp_inertia_is_comp : f = e.
have F3 : f <= e.
  have: '['Res[H] 'xi_p, 'xi_t]_ H <= '['Res[H] ('Res[T] 'xi_c), 'xi_t]_ H.
    by apply: is_comp_inner_prod_le is_comp_inertia_restrict_is_comp_i.
  rewrite Hf /= crestrict_subset // He.
  rewrite -!inner_prodbE linearZ [inner_prodb _ _ _]linearZ /= !inner_prodbE.
  rewrite irr_orthonormal eqxx {1}/GRing.scale /= mulr1.
  rewrite -cconjugates_sum //=.
  rewrite (bigD1 t) /=; last first.
    apply/cconjugatesP; exists 1%g; first by exact: group1.
    by rewrite cfun_conj1.
  rewrite-!inner_prodbE linearD /= !inner_prodbE.
  rewrite scaler_addr irr_orthonormal eqxx {1}/GRing.scale /= mulr1.
  rewrite -!inner_prodbE linear_sum.
  rewrite big1=> [|i Hi]; first by rewrite scaler0 addr0.
  rewrite /= inner_prodbE irr_orthonormal.
  by case/andP: Hi=> _; move/negPf->.    
apply: leC_anti=> //.
have: 0 <  #|G : T|%:R *  'xi_t 1%g.
  rewrite sposC_mul // ?ltC_irr1 //.
  rewrite /ltC -neq0N_neqC posC_nat.
  by case: #|_:_| (indexg_gt0 G T).
move/leC_pmul2r=> <-.
rewrite mulrA -He1 mulrA -Hpsi1.
have IIP: is_char G ('Ind[G, T] 'xi_p).
  by apply: is_char_induced=> //; exact: is_char_irr.
case/(is_comp_charP _ IIP): Hc=> chi' /= IC' ->.
rewrite [X in _ <= X]ffunE.
rewrite addrC -leC_sub addrK.
by apply: posC_isNatC; apply: isNatC_char1 IC'.
Qed.

Fact is_comp_inertia_induced_is_comp : 'Ind[G, T] 'xi_p = 'xi_c.
Proof.
have ICI: is_char G ('Ind[G, T] 'xi_p).
  by apply: is_char_induced (is_char_irr _) _.
case/(is_comp_charP _ ICI): Hc => chi' IC' /= Hchi'.
rewrite Hchi'; move/ffunP: Hchi'; move/(_ 1%g).
rewrite Hpsi1 inner_prod_is_comp_inertia_is_comp -He1.
rewrite [X in _ = X]ffunE -{1}['xi_c _]addr0; move/addrI.
move/eqP; rewrite eq_sym -(character0_eq0 IC'); move/eqP->.
by rewrite addr0.
Qed.

End Chi.

Variable p : Iirr T.

Hypothesis Hp : is_comp t ('Res[H] 'xi_p).

Let c := (odflt 0 (pick ((@is_comp _ G)^~ ('Ind[G,T] 'xi_p)))).

Let Hc : is_comp c ('Ind[G,T] 'xi_p).
Proof.
rewrite /c; case: pickP=> // HH.
have: 'Ind[G, T] 'xi_p == 0.
  rewrite (ncoord_sum (memc_induced _ _)) ?memc_irr //.
  rewrite big1 // => i _.
  move: (HH i); rewrite /is_comp; move/idP; move/negP.
  by rewrite negbK; move/eqP->; rewrite scale0r.
rewrite cinduced_eq0 ?is_char_irr //.
move/eqP; move/ffunP; move/(_ 1%g)=> HH1.
by case/negP: (irr1_neq0 p); rewrite HH1 ffunE.
Qed.

(* This is 6.11 (a) *)
Lemma irr_is_comp_inertia : 'Ind[G, 'I_(G)['xi_t]] 'xi_p \in irr G.
Proof. by rewrite (is_comp_inertia_induced_is_comp Hp Hc); apply: irr_xi. Qed.

(* This is 6.11 (d) *)
Lemma inner_prod_is_comp_inertia : 
 '['Res[H] 'xi_p, 'xi_t]_H = '['Res[H] ('Ind[G, 'I_(G)['xi_t]] 'xi_p), 'xi_t]_H.
Proof. 
rewrite (is_comp_inertia_induced_is_comp Hp Hc).
by rewrite (inner_prod_is_comp_inertia_is_comp Hp Hc).
Qed.

(* This is 6.11 (b) the domain of the induction is B *)
Lemma is_comp_is_comp_inertia :
  is_comp t ('Res[H] ('Ind[G, 'I_(G)['xi_t]] 'xi_p)).
Proof. 
rewrite (is_comp_inertia_induced_is_comp Hp Hc).
by rewrite (is_comp_inertia_restrict_is_comp_g Hp Hc).
Qed.

(* This is 6.11 c *)
Lemma unique_is_comp_inertia : forall p': Iirr T,
   is_comp p' ('Res['I_(G)['xi_t]] ('Ind[G, 'I_(G)['xi_t]] 'xi_p)) ->
   is_comp t ('Res[H] 'xi_p') -> p' = p.
Proof.
move=> p'; rewrite (is_comp_inertia_induced_is_comp Hp Hc)=> Cp' Ct.
have IC: is_char T ('Res[T] 'xi_c).
  by apply: is_char_restrict (is_char_irr _).
case/(is_comp_charP _ IC): Cp' => chi1 IC1 Hchi1.
apply/eqP; case: (_ =P _)=> //; move/eqP=> Dpsi.
have: is_comp p chi1.
  have: is_comp p ('Res[T] 'xi_c).
    by apply: is_comp_inertia_restrict_is_comp_i.
  rewrite /is_comp !(ncoord_inner_prod _ (memc_is_char _)) //.
  by rewrite Hchi1 -inner_prodbE linearD ![inner_prodb_linear _ _ _] /= 
            !inner_prodbE irr_orthonormal (negPf Dpsi) add0r.
case/(is_comp_charP _ IC1)=> chi2 IC2 Hchi2.
have: '['Res[H] 'xi_p, 'xi_t]_H < '['Res[H] ('Res[T] 'xi_c), 'xi_t]_H.
  rewrite Hchi1 addrC Hchi2 2!linearD /=.
  rewrite -!inner_prodbE 2!linearD /= !inner_prodbE.
  rewrite -addrA addrC ltC_sub addrK sposC_addl //.
    have FF := memc_restrict HsT (memc_is_char IC2).
    rewrite -(ncoord_inner_prod _ FF) //.
    apply: posC_isNatC; apply: isNatC_ncoord_char.
    by apply: (is_char_restrict HsT).
  have FF := memc_restrict HsT (memc_is_char (is_char_irr p')).
  move: Ct; rewrite /is_comp -(ncoord_inner_prod _ FF) //.
  rewrite /ltC => ->.
  apply: posC_isNatC; apply: isNatC_ncoord_char.
  by apply: (is_char_restrict HsT); exact: is_char_irr.
rewrite inner_prod_is_comp_inertia (is_comp_inertia_induced_is_comp Hp Hc).
by rewrite crestrict_subset // ltC_sub subrr /ltC eqxx.
Qed.

End S611A.

(* This is 6.11 b it is an injection *)
Lemma injective_is_comp_inertia : forall (G H : {group gT}) (t : Iirr H),
 H <| G ->
 {in [pred p: Iirr 'I_(G)['xi_t] | is_comp t ('Res[H] 'xi_p)] &,
    injective (fun p : Iirr 'I_(G)['xi_t] => 
                  'Ind[G, 'I_(G)['xi_t]] 'xi_p)}.
Proof.
move=> G H t HnG p p' Hp Hp' Heq.
have TsG := inertia_sub G 'xi_t.
apply: (unique_is_comp_inertia HnG Hp' _ Hp).
have FF := memc_restrict TsG (memc_induced TsG (memc_irr p)).
rewrite -Heq /is_comp (ncoord_inner_prod _ FF).
have IC1: is_char G ('Ind[G, 'I_(G)['xi_t]] 'xi_p).
  by apply: is_char_induced=> //; exact: is_char_irr.
have IC2: is_char 'I_(G)['xi_t]
            ('Res['I_(G)['xi_t]] ('Ind[G, 'I_(G)['xi_t]] 'xi_p)).
  by apply: is_char_restrict TsG _.
rewrite inner_prod_charC  ?is_char_irr //.
rewrite (frobenius_reciprocity TsG) ?(memc_is_char,is_char_irr) //.
rewrite inner_prod0; last first.
  by apply: memc_induced=> //; exact: memc_irr.
rewrite cinduced_eq0 ?is_char_irr //.
apply/eqP; move/ffunP; move/(_ 1%g).
rewrite /= [_ 0 _]ffunE=> HH.
by case/eqP: (irr1_neq0 p).
Qed.

(* 6.11 b the inverse function *)
Definition inertia_induced_inv (G H : {group gT})
                (t : Iirr H) (chi : {cfun gT}) :=
  odflt 0
           (pick [pred t' : Iirr 'I_(G)['xi_t] |
                   is_comp t ('Res[H] 'xi_t') && 
                   is_comp t' ('Res['I_(G)['xi_t]] chi)]).

Let inertia_ncoord :
 forall (G H : {group gT}) (t : Iirr H) (c : Iirr G),
    H <| G ->
   [pred p : Iirr 'I_(G)['xi_t] | 
                 is_comp t ('Res[H] 'xi_p) &&
                 is_comp p ('Res['I_(G)['xi_t]] 'xi_c)] =1 xpred0 ->
   ncoord t ('Res[H] 'xi_c) == 0.
Proof.
move=> G H t c HnG HH.
have FF := memc_restrict (normal_sub HnG) (memc_irr c).
rewrite (ncoord_inner_prod _ FF).
have HsT := subset_inertia (memc_irr t) HnG.
rewrite -(crestrict_subset 'xi_c HsT).
rewrite (ncoord_sum (memc_restrict (inertia_sub G 'xi_t) (memc_irr _))) //.
rewrite linear_sum -inner_prodbE linear_sum big1 //= => chi1 _.
rewrite inner_prodbE linearZ -inner_prodbE linearZ /= inner_prodbE.
have FF1 := memc_restrict HsT (memc_irr chi1).
rewrite -(ncoord_inner_prod _ FF1).
move: (HH chi1); rewrite inE !is_compE.
case: (_ =P _)=> [->|/= _]; first by rewrite scaler0.
by move/eqP->; rewrite scale0r.
Qed.

Lemma inertia_induced_inv_is_comp_h :
 forall (G H : {group gT}) (t : Iirr H) (c : Iirr G),
    H <| G -> is_comp t ('Res[H] 'xi_c) ->
    is_comp t ('Res[H] 'xi_(inertia_induced_inv G t 'xi_c)).
Proof.
move=> G H t c HnG Ct.
rewrite /inertia_induced_inv; case: pickP=> [c'| HH]; first by case/andP.
by case/negP: Ct; apply: inertia_ncoord.
Qed.

Lemma inertia_induces_inv_is_comp_i :
 forall (G H : {group gT}) (t : Iirr H) (c : Iirr G),
    H <| G -> is_comp t ('Res[H] 'xi_c) ->
    is_comp (inertia_induced_inv G t 'xi_c) ('Res['I_(G)['xi_t]] 'xi_c).
Proof.
move=> G H t c HnG Ct.
rewrite /inertia_induced_inv; case: pickP=> [c'| HH]; first by case/andP.
by case/negP: Ct; apply: inertia_ncoord.
Qed.

(* This is 6.11 b the surjective part *)
Lemma inertia_induced_invE : 
 forall (G H : {group gT}) (t : Iirr H) (c : Iirr G),
    H <| G -> is_comp t ('Res[H] 'xi_c) ->
    'Ind[G,'I_(G)['xi_t]] 'xi_(inertia_induced_inv G t 'xi_c) = 'xi_c.
Proof.
move=> G H t c HnG Cc.
apply: is_comp_inertia_induced_is_comp=> //.
  by apply: inertia_induced_inv_is_comp_h.
have FF := memc_induced (inertia_sub G 'xi_t) (memc_irr _).
rewrite /is_comp (ncoord_inner_prod _ (FF _)).
rewrite -frobenius_reciprocity; first last.
- by apply: memc_irr.
- by apply: memc_irr.
- by apply:inertia_sub.
move: (inertia_induces_inv_is_comp_i HnG Cc).
have FF1 := memc_restrict (inertia_sub G 'xi_t) (memc_irr c).
rewrite /is_comp (ncoord_inner_prod _ FF1).
rewrite inner_prod_charC ?is_char_irr //.
apply: is_char_restrict (is_char_irr _).
by apply: inertia_sub.
Qed.

End S611.