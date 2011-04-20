(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop ssralg finset.
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
(* 'I_(G)[f] :  the set of elements of G such that f^g=f                  *)
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
Lemma cfun_conj_in_cfun : forall (G : {group gT}) f g,
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

Lemma is_irr_conj : forall  (theta : irr H) g,
  H <| G -> g \in G -> is_irr H (theta^g)%CH.
Proof.
move=> t g HnG GiG.
rewrite is_irr_inner_prod_charE ?(is_char_conj,is_char_irr) //.
by rewrite cfun_conj_inner // irr_orthonormal eqxx.
Qed.
 
Definition irr_conj (theta : irr H) g := get_irr H (theta^g)%CH.

Lemma irr_conjE : forall (theta : irr H) g,
  H <| G -> g \in G -> irr_conj theta g = (theta^g)%CH :> {cfun _}.
Proof. by move=> t g HnG GiG; rewrite get_irrE // is_irr_conj. Qed.

Lemma is_irr_inner : forall (theta : irr H) g,
  H <| G -> g \in G -> '[theta,(theta^g)%CH]_H = (g \in 'I_(G)[theta])%:R.
Proof.
move=> t g HnG GiG.
rewrite -(irr_conjE t HnG GiG) irr_orthonormal.
rewrite inE GiG eq_sym /=; congr (_%:R); congr nat_of_bool.
apply/eqP/eqP=> HH; last by apply: cfun_of_irr_inj; rewrite irr_conjE.
by rewrite -(irr_conjE t HnG GiG) HH.
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

Lemma cconjugates1 : H <| G -> 
  cconjugates G (irr1 H) = [::(irr1 H : {cfun _})].
Proof.
move=> HnG.
have: forall f, f \in cconjugates G (irr1 H) -> f = irr1 H .
  move=> f; case/cconjugatesP=> g GiG ->.
  apply/ffunP=> h; rewrite ffunE !irr1E.
  (case: (boolP (_ \in _))=> HH; case: (boolP (_ \in _)))=> // [|HH1]; 
       [case/negP|case/negP:HH]; last first.
      case/normalP: HnG=> _; move/(_ _ (groupVr GiG))<-. 
      by apply/imsetP; exists h.
  rewrite -[h]conjg1 -[1%g](mulKg g) mulg1 conjgM.
  case/normalP: HnG=> _; move/(_ _ (GiG))<-. 
  by apply/imsetP; exists (h^g^-1)%g.
move: (mem_cconjugates (irr1 H)) (unique_cconjugates (irr1 H)).
case: cconjugates=> // f1 [|f2 s]; first by rewrite inE; move/eqP->.
move=> _ /=; case/andP=> HH _ HH1; case/negP: HH.
by rewrite /= (HH1 f1) ?(inE,eqxx) // (HH1 f2) ?(inE,eqxx,orTb,orbT).
Qed.

Lemma cconjugates_sum : forall (R : Type) (idx : R) (op : Monoid.com_law idx) 
                              (F: _ -> R) (theta : irr H),
   H <| G ->
   \big[op/idx]_(i : irr H | ((i : {cfun _}) \in cconjugates G theta)) 
       F (cfun_of_irr i) = 
   \big[op/idx]_(i <- cconjugates G theta) F i.
Proof.
move=> R idx op F theta HnG.
set u := \big[op/idx]_(i <- cconjugates G theta) F i.
rewrite -big_map -big_filter.
apply: eq_big_perm. 
apply: uniq_perm_eq; try apply: unique_cconjugates.
  apply: filter_uniq.
  rewrite map_inj_uniq; last by exact: cfun_of_irr_inj.
  by rewrite /index_enum -enumT enum_uniq.
move=> i; apply/idP/idP; rewrite mem_filter; first by case/andP.
move=> HH; apply/andP; split=> //.
case/cconjugatesP: HH => g GiG->.
rewrite -(irr_conjE _ HnG GiG).
apply: map_f=> //.
by rewrite /index_enum -enumT  mem_enum.
Qed.

(* This is Isaacs 6.2 *)
Lemma is_comp_clifford :  forall (chi : irr G) (theta : irr H),
   H <| G -> is_comp theta ('Res[H] chi) ->
  'Res[H] chi = 
     '['Res[H] chi, theta]_H *: (\sum_(f <- cconjugates G theta) f).
Proof.
move=> chi theta HnG IC.
rewrite -cconjugates_sum //=.
have CFchi: 'Res[H] chi \in 'CF(H).
  apply: memc_is_char; apply: is_char_restrict (is_char_irr _).
  by apply: normal_sub.
rewrite {1}(ncoord_sum CFchi).
rewrite (bigID (fun i : irr H => (i : {cfun _})  \in cconjugates G theta)) /=.
rewrite [\sum_(i | _ \notin _)_]big1 ?addr0=> [|phi].
  rewrite scaler_sumr; apply: eq_bigr=> phi Hp.
  rewrite (ncoord_inner_prod _ CFchi).
  case/cconjugatesP: Hp => g GiG ->.
  by rewrite cfun_conj_inner_restrict //; exact: memc_irr.
move=> HH.
have: '['Res[H] ('Ind[G,H] theta), phi]_H = 0.
  have->: 'Res[H] ('Ind[G,H] theta) = 
               #|H|%:R^-1 *: ((\sum_(c \in G) (theta ^ c)%CH)).
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
have CFInd: ('Ind[G, H] theta) \in 'CF(G).
   by apply: (memc_induced (normal_sub HnG)); exact: memc_irr.
rewrite {1}(ncoord_sum CFInd) linear_sum /=.
rewrite -inner_prodbE linear_sum /= => HH1. 
have: '['Res[H] (ncoord chi ('Ind[G, H] theta) *: (chi: {cfun _})),phi]_H = 0.
  apply: (posC_sum_eq0 _ HH1)=> [theta1 _|]; last first.
    by rewrite /index_enum -enumT mem_enum.
  apply: posC_isNatC.
  set u := 'Res[_] _; suff ICu: is_char H u.
    by apply: inner_prod_char_nat=> //; exact: is_char_irr.
  apply: (is_char_restrict (normal_sub HnG)).
  have II: is_char G ('Ind[G, H] theta).
    by apply: is_char_induced (is_char_irr _) (normal_sub _).
  case/isNatCP: (isNatC_ncoord_char theta1 II)=> /= n ->.
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
Lemma cker_is_comp1 : forall chi : irr G, 
  H <| G -> is_comp (irr1 H) ('Res[H] chi) -> H \subset cker G chi.
Proof.
move=> chi HnG IC; apply/subsetP=> h HiH.
rewrite cker_irrE inE (subsetP (normal_sub HnG)) //.
move: (is_comp_clifford HnG IC).
rewrite cconjugates1 // big_cons big_nil addr0=> HH.
move/ffunP: (HH); move/(_ 1%g).
rewrite ffunE group1 mul1r.
rewrite [X in _ = X]ffunE irr1E group1 [_ *: _]mulr1=> HH1.
move/ffunP: HH; move/(_ h).
rewrite -HH1 ffunE HiH mul1r => ->.
by rewrite ffunE irr1E HiH [_ *: _]mulr1 eqxx.
Qed.

(* This is Isaacs' 6.8 *)
Lemma is_comp_val1_div : forall (chi : irr G) (theta : irr H), 
  H <| G -> is_comp theta ('Res[H] chi) -> 
    exists n: nat, chi 1%g = n%:R * theta 1%g.
Proof.
move=> chi theta HnG IC.
exists (getNatC ('['Res[H] chi, theta ]_ H) * (size (cconjugates G theta)))%N.
rewrite natr_mul.
have IC1: is_char H ('Res[H] chi).
  by apply: is_char_restrict (normal_sub _) (is_char_irr _).
move: (inner_prod_char_nat IC1 (is_char_irr theta)).
rewrite /isNatC; move/eqP<-.
have->: chi 1%g = ('Res[H] chi) 1%g by rewrite !ffunE !(group1,mul1r).
rewrite {1}(is_comp_clifford HnG IC).
rewrite ffunE -mulrA; congr (_ * _).
rewrite sum_ffunE ffunE.
have: forall f, f \in cconjugates G theta -> f 1%g = theta 1%g.
  by move=> f; case/cconjugatesP=> g GiG ->; rewrite ffunE conj1g.
elim: (cconjugates _ _)=> [|f l IH HF]; first by rewrite big_nil mul0r.
rewrite big_cons HF ?(inE,eqxx) // IH=> [|f1 Hf1].
  by rewrite /= -add1n natr_add mulr_addl mul1r.
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

Lemma cconjugates_size : forall (theta : irr H), 
  size (cconjugates G theta) =  #|G : ('I_(G)[theta])%CH|.
Proof.
move=> theta.
suff->: size(cconjugates G theta) = 
       \big[addn/0%N]_(i <- cconjugates G theta) 1%N.
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

Lemma cconjugates_inertia : forall (G H : {group gT}) (theta : irr H),
   cconjugates 'I_(G)[theta] theta = [::(theta : {cfun _})].
Proof.
move=> G H theta.
set T := 'I_(G)[theta]%G.
have: forall f, f \in cconjugates T theta -> f = theta.
  move=> f; case/cconjugatesP=> g.
  by rewrite inE; case/andP=> _; move/eqP->.
move: (mem_cconjugates T theta) (unique_cconjugates T theta) => /=. 
case: cconjugates=> // f1 [|f2 s]; first by rewrite inE; move/eqP->.
move=> _ /=; case/andP=> HH _ HH1; case/negP: HH.
by rewrite /= (HH1 f1) ?(inE,eqxx) // (HH1 f2) ?(inE,eqxx,orTb,orbT).
Qed.

End MoreInertia.

Section S611.

Variable (gT : finGroupType).

Section S611A.

Variable (H G : {group gT}).

Variable theta : irr H.

Let T := 'I_(G)[theta]%G.

Hypothesis HnG : H <| G.

Let TsG := inertia_sub G theta.

Let HsT : H \subset T.
Proof.
apply: subset_inertia=> //.
by exact: memc_irr.
Qed.

Let HnT : H <| T.
apply: normalS (HnG).
  apply: subset_inertia=> //.
  by exact: memc_irr.
exact: inertia_sub.
Qed.

Section Chi.

Variable psi : irr T.

Hypothesis Hpsi : is_comp theta ('Res[H] psi).

Variable chi : irr G.

Hypothesis Hchi : is_comp chi ('Ind[G,T] psi).

Let ITC : is_char T ('Res[T] chi).
Proof. by apply: (is_char_restrict TsG (is_char_irr _)). Qed.

Let ITP : is_char T ('Res[T] psi).
Proof. by apply: (is_char_restrict _ (is_char_irr _)). Qed.

Let IHC : is_char H ('Res[H] chi).
Proof. by apply: (is_char_restrict (normal_sub _) (is_char_irr _)). Qed.

Let IHP : is_char H ('Res[H] psi).
Proof. by apply: (is_char_restrict _ (is_char_irr _)). Qed.

Fact is_comp_inertia_restrict_is_comp_i : is_comp psi ('Res[T] chi).
Proof.
rewrite /is_comp ncoord_inner_prod; last first.
  by apply: (memc_restrict TsG) (memc_is_char (is_char_irr _)).
move: Hchi.
rewrite /is_comp ncoord_inner_prod; last first.
by apply memc_induced=> //; apply: memc_irr.
rewrite -frobenius_reciprocity ?memc_irr //.
by rewrite inner_prod_charC ?(is_char_restrict TsG,is_char_irr).
Qed.

Fact is_comp_inertia_restrict_is_comp_g : is_comp theta ('Res[H] chi).
Proof.
have: '['Res[H] psi, theta ]_ H <= '['Res[H] ('Res[T] chi), theta ]_ H.
  by apply: is_comp_inner_prod_le is_comp_inertia_restrict_is_comp_i.
rewrite crestrict_subset // -!ncoord_inner_prod ?memc_is_char //.
move: Hpsi; rewrite /is_comp /=.
case/isNatCP: (isNatC_ncoord_char theta IHP)=> n ->.
case/isNatCP: (isNatC_ncoord_char theta IHC)=> m ->.
by rewrite -!neq0N_neqC -leq_leC; case: m=> //; case: n.
Qed.

Let e := '['Res[H] chi, theta ]_ H.

Let f := '['Res[H] psi, theta ]_ H.

Let He : 'Res[H] chi = e *: ((\sum_(f <- cconjugates G theta) f)).
Proof. exact: (is_comp_clifford HnG is_comp_inertia_restrict_is_comp_g). Qed.

Let Hf  : 'Res[H] psi = f *: (theta : {cfun _}).
Proof.
move: (is_comp_clifford  HnT Hpsi).
rewrite cconjugates_inertia.
by rewrite big_cons big_nil addr0.
Qed.

Let He1 : chi 1%g = e * #|G : T|%:R * (theta 1%g).
Proof.
move/ffunP: He; move/(_ 1%g).
rewrite ffunE group1 mul1r => ->.
rewrite ffunE sum_ffunE ffunE -mulrA; congr (_ * _).
rewrite -cconjugates_sum //=.
rewrite (eq_bigr (fun (i: irr H) => theta 1%g))=> [|i]; last first.
  case/cconjugatesP=> g GiG ->.
  by rewrite cfun_conj_val1.
rewrite (cconjugates_sum _ (fun i : {cfun _} => theta 1%g)) //=.
rewrite -cconjugates_size.
elim: cconjugates=> [|f1 l IH].
  by rewrite big_nil mul0r.
by rewrite big_cons IH /= -add1n natr_add mulr_addl mul1r.
Qed.

Let Hpsi1  : ('Ind[G, T] psi) 1%g = f * #|G : T|%:R * (theta 1%g).
Proof.
have IGI: is_char G ('Ind[G,T] psi).
  by apply: is_char_induced=> //; exact: is_char_irr.
rewrite ffunE.
rewrite (eq_bigr (fun (c : gT) => psi 1%g))=> [|g GiG]; last first.
  by rewrite conj1g.
rewrite sumr_const.
move/ffunP: Hf; move/(_ 1%g).
rewrite ffunE group1 mul1r => ->.
rewrite ffunE.
apply: (mulfI (neq0GC T)).
rewrite mulrA mulfV ?neq0GC // mul1r. 
rewrite mulrCA  mulrA -[_ *+ #|_|]mulr_natl mulrA; congr (_ * _).
rewrite [_ * f]mulrC -[(f * _) * _]mulrA [#|_ : _|%:R * _]mulrC.
by rewrite -natr_mul LaGrange.
Qed.

Fact inner_prod_is_comp_inertia_is_comp : f = e.
have F3 : f <= e.
  have: '['Res[H] psi, theta ]_ H <= '['Res[H] ('Res[T] chi), theta ]_ H.
    by apply: is_comp_inner_prod_le is_comp_inertia_restrict_is_comp_i.
  rewrite Hf /= crestrict_subset // He.
  rewrite -!inner_prodbE linearZ [inner_prodb _ _ _]linearZ /= !inner_prodbE.
  rewrite irr_orthonormal eqxx {1}/GRing.scale /= mulr1.
  rewrite -cconjugates_sum //=.
  rewrite (bigD1 theta) /=; last first.
    apply/cconjugatesP; exists 1%g; first by exact: group1.
    by rewrite cfun_conj1.
  rewrite-!inner_prodbE linearD /= !inner_prodbE.
  rewrite scaler_addr irr_orthonormal eqxx {1}/GRing.scale /= mulr1.
  rewrite -!inner_prodbE linear_sum.
  rewrite big1=> [|i Hi]; last first.
    rewrite /= inner_prodbE irr_orthonormal.
    by case/andP: Hi=> _; move/negPf->.    
  by rewrite scaler0 addr0.
apply: leC_anti=> //.
have: 0 <  #|G : T|%:R * theta 1%g.
  rewrite sposC_mul // ?ltC_irr1 //.
  rewrite /ltC -neq0N_neqC posC_nat.
  by case: #|_:_| (indexg_gt0 G T).
move/leC_pmul2r=> <-.
rewrite mulrA -He1 mulrA -Hpsi1.
have IIP: is_char G ('Ind[G, T] psi).
  by apply: is_char_induced=> //; exact: is_char_irr.
case/(is_comp_charP _ IIP): Hchi=> chi' /= IC' ->.
rewrite [X in _ <= X]ffunE.
rewrite addrC -leC_sub addrK.
by apply: posC_isNatC; apply: isNatC_char1 IC'.
Qed.

Fact is_comp_inertia_induced_is_comp : 'Ind[G, T] psi = chi.
Proof.
have ICI: is_char G ('Ind[G, T] psi).
  by apply: is_char_induced (is_char_irr _) _.
case/(is_comp_charP _ ICI): Hchi => chi' IC' /= Hchi'.
rewrite Hchi'; move/ffunP: Hchi'; move/(_ 1%g).
rewrite Hpsi1 inner_prod_is_comp_inertia_is_comp -He1.
rewrite [X in _ = X]ffunE -{1}[chi _]addr0; move/addrI.
move/eqP; rewrite eq_sym -(character0_eq0 IC'); move/eqP->.
by rewrite addr0.
Qed.

End Chi.

Variable psi : irr T.

Hypothesis Hpsi : is_comp theta ('Res[H] psi).

Let chi := (odflt (irr1 G) (pick ((@is_comp _ G)^~ ('Ind[G,T] psi)))).

Let Hchi : is_comp chi ('Ind[G,T] psi).
Proof.
rewrite /chi; case: pickP=> // HH.
have: 'Ind[G, T] psi == 0.
  rewrite (ncoord_sum (memc_induced _ _)) ?memc_irr //.
  rewrite big1 // => i _.
  move: (HH i); rewrite /is_comp; move/idP; move/negP.
  by rewrite negbK; move/eqP->; rewrite scale0r.
rewrite cinduced_eq0 ?is_char_irr //.
move/eqP; move/ffunP; move/(_ 1%g)=> HH1.
by case/negP: (irr1_neq0 psi); rewrite HH1 ffunE.
Qed.

(* This is 6.11 (a) *)
Lemma is_irr_is_comp_inertia : is_irr G ('Ind[G, 'I_(G)[theta]] psi).
Proof.
rewrite (is_comp_inertia_induced_is_comp Hpsi Hchi).
by apply: is_irr_irr.
Qed.

(* This is 6.11 (d) *)
Lemma inner_prod_is_comp_inertia : 
 '['Res[H] psi, theta]_H = '['Res[H] ('Ind[G, 'I_(G)[theta]] psi), theta]_H.
Proof. 
rewrite (is_comp_inertia_induced_is_comp Hpsi Hchi).
by rewrite (inner_prod_is_comp_inertia_is_comp Hpsi Hchi).
Qed.

(* This is 6.11 (b) the domain of the induction is B *)
Lemma is_comp_is_comp_inertia :
  is_comp theta ('Res[H] ('Ind[G, 'I_(G)[theta]] psi)).
Proof. 
rewrite (is_comp_inertia_induced_is_comp Hpsi Hchi).
by rewrite (is_comp_inertia_restrict_is_comp_g Hpsi Hchi).
Qed.

(* This is 6.11 c *)
Lemma unique_is_comp_inertia : forall psi': irr T,
   is_comp psi' ('Res['I_(G)[theta]] ('Ind[G, 'I_(G)[theta]] psi)) ->
   is_comp theta ('Res[H] psi') -> psi' = psi.
Proof.
move=> psi'; rewrite (is_comp_inertia_induced_is_comp Hpsi Hchi)=> Cpsi' Ct.
have IC: is_char T ('Res[T] chi).
  by apply: is_char_restrict (is_char_irr _).
case/(is_comp_charP _ IC): Cpsi' => chi1 IC1 Hchi1.
apply/eqP; case: (_ =P _)=> //; move/eqP=> Dpsi.
have: is_comp psi chi1.
  have: is_comp psi ('Res[T] chi).
    by apply: is_comp_inertia_restrict_is_comp_i.
  rewrite /is_comp !ncoord_inner_prod ?memc_is_char //.
  by rewrite Hchi1 -inner_prodbE linearD ![inner_prodb_linear _ _ _] /= 
            !inner_prodbE irr_orthonormal (negPf Dpsi) add0r.
case/(is_comp_charP _ IC1)=> chi2 IC2 Hchi2.
have: '['Res[H] psi, theta]_H < '['Res[H] ('Res[T] chi), theta]_H.
  rewrite Hchi1 addrC Hchi2 2!linearD /=.
  rewrite -!inner_prodbE 2!linearD /= !inner_prodbE.
  rewrite -addrA addrC ltC_sub addrK sposC_addl //.
    rewrite -ncoord_inner_prod //; last first.
      by apply: (memc_restrict HsT (memc_is_char _)).
    apply: posC_isNatC; apply: isNatC_ncoord_char.
    by apply: (is_char_restrict HsT).
  move: Ct; rewrite /is_comp -ncoord_inner_prod //.
    rewrite /ltC => ->.
    apply: posC_isNatC; apply: isNatC_ncoord_char.
    by apply: (is_char_restrict HsT); exact: is_char_irr.
  by apply: (memc_restrict HsT (memc_is_char _)); exact: is_char_irr.
rewrite inner_prod_is_comp_inertia (is_comp_inertia_induced_is_comp Hpsi Hchi).
by rewrite crestrict_subset // ltC_sub subrr /ltC eqxx.
Qed.

End S611A.

(* This is 6.11 b it is an injection *)
Lemma injective_is_comp_inertia : forall (G H : {group gT}) (theta : irr H),
 H <| G ->
 {in [pred psi: irr 'I_(G)[theta] | is_comp theta ('Res[H] psi)] &,
    injective (fun psi : irr 'I_(G)[theta] => 
                  'Ind[G, 'I_(G)[theta]] psi)}.
Proof.
move=> G H theta HnG psi psi' Hpsi Hpsi' Heq.
have TsG := inertia_sub G theta.
apply: (unique_is_comp_inertia HnG Hpsi' _ Hpsi).
rewrite -Heq /is_comp ncoord_inner_prod; last first.
  apply: (memc_restrict TsG).
  apply: (memc_induced TsG).
  by apply: memc_irr.
have IC1: is_char G ('Ind[G, 'I_(G)[theta]] psi).
  by apply: is_char_induced=> //; exact: is_char_irr.
have IC2: is_char 'I_(G)[theta]
            ('Res['I_(G)[theta]] ('Ind[G, 'I_(G)[theta]] psi)).
  by apply: is_char_restrict TsG _.
rewrite inner_prod_charC  ?is_char_irr //.
rewrite (frobenius_reciprocity TsG) ?(memc_is_char,is_char_irr) //.
rewrite inner_prod0; last first.
  by apply: memc_induced=> //; exact: memc_irr.
rewrite cinduced_eq0 ?is_char_irr //.
apply/eqP; move/ffunP; move/(_ 1%g).
rewrite /= [_ 0 _]ffunE=> HH.
by case/eqP: (irr1_neq0 psi).
Qed.

(* 6.11 b the inverse function *)
Definition inertia_induced_inv (G H : {group gT})
                (theta : irr H) (chi : {cfun gT}) :=
  odflt (irr1 'I_(G)[theta])
           (pick [pred t : irr 'I_(G)[theta] |
                   is_comp theta ('Res[H] t) && 
                   is_comp t ('Res['I_(G)[theta]] chi)]).

Let inertia_ncoord :
 forall (G H : {group gT}) (theta : irr H) (chi : irr G),
    H <| G ->
   [pred psi : irr 'I_(G)[theta] | 
                 is_comp theta ('Res[H] psi) &&
                 is_comp psi ('Res['I_(G)[theta]] chi)] =1 xpred0 ->
   ncoord theta ('Res[H] chi) == 0.
Proof.
move=> G H theta chi HnG HH.
rewrite ncoord_inner_prod; last first.
  by apply: (memc_restrict (normal_sub HnG) (memc_irr _)).
have HsT := subset_inertia (memc_irr theta) HnG.
rewrite -(crestrict_subset chi HsT).
rewrite (ncoord_sum (memc_restrict (inertia_sub G theta) (memc_irr _))) //.
rewrite linear_sum -inner_prodbE linear_sum big1 //= => chi1 _.
rewrite inner_prodbE linearZ -inner_prodbE linearZ /= inner_prodbE.
rewrite -ncoord_inner_prod ?(memc_restrict HsT, memc_irr) //.
move: (HH chi1); rewrite inE !is_compE.
case: (_ =P _)=> [->|/= _]; first by rewrite scaler0.
by move/eqP->; rewrite scale0r.
Qed.

Lemma inertia_induces_inv_is_comp_h :
 forall (G H : {group gT}) (theta : irr H) (chi : irr G),
    H <| G -> is_comp theta ('Res[H] chi) ->
    is_comp theta ('Res[H] (inertia_induced_inv G theta chi)).
Proof.
move=> G H theta chi HnG Ct.
rewrite /inertia_induced_inv; case: pickP=> [chi'| /= HH].
  by case/andP.
case/negP: Ct.
by apply: inertia_ncoord.
Qed.

Lemma inertia_induces_inv_is_comp_i :
 forall (G H : {group gT}) (theta : irr H) (chi : irr G),
    H <| G -> is_comp theta ('Res[H] chi) ->
    is_comp (inertia_induced_inv G theta chi) ('Res['I_(G)[theta]] chi).
Proof.
move=> G H theta chi HnG Ct.
rewrite /inertia_induced_inv; case: pickP=> [chi'| /= HH].
  by case/andP.
case/negP: Ct.
by apply: inertia_ncoord.
Qed.

(* This is 6.11 b the surjective part *)
Lemma inertia_induced_invE : 
 forall (G H : {group gT}) (theta : irr H) (chi : irr G),
    H <| G -> is_comp theta ('Res[H] chi) ->
    'Ind[G,'I_(G)[theta]] (inertia_induced_inv G theta chi) = chi.
Proof.
move=> G H theta chi HnG Cchi.
apply: is_comp_inertia_induced_is_comp=> //.
  by apply: inertia_induces_inv_is_comp_h.
rewrite /is_comp ncoord_inner_prod; last first.
  apply: memc_induced; last by apply: memc_irr.
  by apply:inertia_sub.
rewrite -frobenius_reciprocity; first last.
- by apply: memc_irr.
- by apply: memc_irr.
- by apply:inertia_sub.
move: (inertia_induces_inv_is_comp_i HnG Cchi).
rewrite /is_comp ncoord_inner_prod; last first.
  by apply: (memc_restrict (inertia_sub _ _) (memc_irr _)).
rewrite inner_prod_charC ?is_char_irr //.
apply: is_char_restrict (is_char_irr _).
by apply: inertia_sub.
Qed.

End S611.