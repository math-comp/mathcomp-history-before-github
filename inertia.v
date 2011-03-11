(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop ssralg finset.
Require Import fingroup morphism perm automorphism center.
Require Import matrix mxalgebra mxrepresentation vector algC character.

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

Implicit Type f : cfun gT algC.

Definition cfun_conj f (g : gT) :=
  cfun_of_fun (fun h => f (h^(g^-1))).

Notation "f ^ g" := (cfun_conj f g) : character_scope.

Lemma cfun_conjE : forall f g h, (f ^ g)%CH h = f (h^(g^-1)).
Proof. by move=> f g h; rewrite cfunE. Qed.

(* Isaacs' 6.1.a *)
Lemma cfun_conj_in_cfun : forall (G : {group gT}) f g,
  g \in G -> f \in 'CF(G) -> (f^g)%CH \in 'CF(G).
Proof.
move=> G f g GiG CFf.
apply/cfun_memP; split=> [h HniG|h1 h2 H1iG H2iG].
  rewrite cfunE (cfun0 CFf) //; apply/negP=> HGiG; case/negP: HniG.
  by rewrite -(groupJr h (groupVr GiG)).
by rewrite !cfunE !(cfunJ CFf, groupV) // groupJ.
Qed.

(* Isaacs' 6.1.b *)
Lemma cfun_conjM : forall f (g h : gT),
  (f ^ (g * h) = (f ^ g) ^ h)%CH.
Proof. by move=> f g h; apply/cfunP=> k; rewrite !cfun_conjE invMg conjgM. Qed.

Lemma cfun_conj1 : forall f, (f^1)%CH = f.
Proof. by move=> f; apply/cfunP=> g; rewrite cfunE invg1 conjg1. Qed.

Lemma cfun_conj_val1 : forall f g, (f^g)%CH 1%g = f 1%g.
Proof. by move=> f g; rewrite cfunE conj1g. Qed.

Lemma cfun_conj_conjC : forall f (g : gT),
  (f^g)^*%CH = (f^* ^ g)%CH.
Proof. by move=> f g; apply/cfunP=> h; rewrite !cfunE. Qed.

End Conj.

Notation "f ^ g" := (cfun_conj f g) : character_scope.

Section Inertia.

Variable gT : finGroupType.

Definition inertia (G : {set gT}) (f : cfun gT algC) :=  
  [set g \in G | (f ^ g)%CH == f].

Variable (G H : {group gT}).

Local Notation "'I_( G )[ f ]" := (inertia G f).

Lemma group_set_inertia : forall f, group_set 'I_(G)[f].
Proof.
move=> f; rewrite /inertia; apply/andP; split.
  rewrite inE group1; apply/eqP; apply/cfunP=> g.
  by rewrite cfunE invg1 conjg1.
apply/subsetP=> p; case/imset2P=> g1 g2; rewrite !inE.
case/andP=> G1iG CF1; case/andP=> G2iG CF2 ->; rewrite groupM //.
apply/eqP; apply/cfunP=> h; rewrite cfunE invMg conjgM.
move/cfunP: (eqP CF1); move/(_ (h^(g2^-1))); rewrite cfunE => ->.
by move/cfunP: (eqP CF2); move/(_ h); rewrite cfunE => ->.
Qed.

Canonical Structure inertia_group f := Group (group_set_inertia f).

Lemma inertia_sub : forall f, 'I_(G)[f] \subset G.
Proof. 
by move=> t; apply/subsetP=> g; rewrite inE; case/andP.
Qed.

Lemma cfun_conj_eqE : forall f (g h : gT), 
  g \in G -> h \in G -> (f^g == f^h)%CH = (h \in ('I_(G)[f] :* g)).
Proof.
move=> f g h GiG HiG; apply/eqP/rcosetP=> [Hx|]; last first.
  case=> g'; rewrite inE; case/andP=> G'iG; move/eqP=> CCi ->.
  apply/cfunP=> h'; rewrite cfunE -{1}CCi cfunE -conjgM.
  by rewrite cfun_conjE invMg.
exists (h * g^-1)%g; last by rewrite -mulgA mulVg mulg1.
rewrite inE !(groupM,groupV) //; apply/eqP; apply/cfunP=> g'.
rewrite cfunE invMg invgK conjgM.
move/cfunP: Hx; move/(_ (g'^g)); rewrite !cfun_conjE => <-.
by rewrite -conjgM mulgV conjg1.
Qed.

Lemma inertia_center : forall f,
  f \in 'CF(H) -> H <| G -> 'Z(G) \subset ('I_(G)[f]).
Proof.
move=> f FcF HnG.
apply/subsetP=> g; case/centerP=> GiG Cg; rewrite inE GiG.
apply/eqP; apply/cfunP=> h; rewrite cfunE.
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
apply/eqP; apply/cfunP=> h2; case: (boolP (h2 \in H))=> [H2iH|H2niH].
  by rewrite cfunE (cfunJ FcF) // groupV.
rewrite cfunE !(cfun0 FcF) //.
apply/negP=> HH; case/negP: H2niH.
by rewrite -(groupJr _ (groupVr H1iH)).
Qed.

(* Isaacs' 6.1.c *)
Lemma cfun_conj_inner : forall (f1 f2 : cfun gT algC) (g : gT),
 H <| G -> g \in G -> ('[f1^g,f2^g]_H = '[f1,f2]_H)%CH.
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
Lemma cfun_conj_inner_restrict : forall (f1 f2 : cfun _ _) (g : gT),
 H <| G -> f1 \in 'CF(G) ->  g \in G -> 
   ('['Res[H] f1,f2^g]_H = '['Res[H] f1,f2]_H)%CH.
Proof.
move=> f1 f2 g HnG CFf GiG.
rewrite -['[_,f2]_H](cfun_conj_inner _ _ HnG GiG).
rewrite !inner_prodE; congr (_ * _).
apply: eq_bigr=> h HiH; congr (_ * _); rewrite !cfunE (cfunJ CFf) ?groupV //.
  by rewrite memJ_norm // (subsetP (normal_norm HnG)) // groupV.
by apply: (subsetP (normal_sub HnG)).
Qed.

Lemma is_char_conj : forall (chi : character H) g, 
  H <| G -> g \in G -> is_char H (chi^g)%CH.
Proof.
move=> chi g HnG GiG; case: (charRE chi)=> n [rG <-].
have mx_reprj: mx_repr H (fun x => rG (x^(g^-1%g))).
  split=> [|h1 h2 H1iH H2iH]; first by rewrite conj1g repr_mx1.
  by rewrite conjMg repr_mxM ?(memJ_norm, groupV, (subsetP (normal_norm HnG))).
apply/is_charRP; exists n; exists (MxRepresentation mx_reprj).
by apply/cfunP=> h; rewrite !cfunE ?(memJ_norm, groupV, (subsetP (normal_norm HnG))).
Qed.

(* Isaac's 6.1.e *)
Definition character_conj (chi : character H) g 
                          (HnG : H <| G) (GiG : g \in G) :=
  Character (is_char_conj chi HnG GiG).

Definition character_conjE :
  forall (chi : character H) g (HnG : H <| G) (GiG : g \in G),
    character_conj chi HnG GiG = (chi^g)%CH :> cfun _ _.
Proof. by move=> chi g HnG GiG; apply/cfunP=> h; rewrite cfunE. Qed.

Lemma is_irr_conj : forall  (theta : irr H) g (HnG : H <| G) (GiG : g \in G), 
  is_irr H (character_conj (character_of_irr theta) HnG GiG)%CH.
Proof.
move=> t g HnG GiG.
rewrite char_irreducibleE character_conjE cfun_conj_inner //.
by rewrite -char_irreducibleE is_irr_irr.
Qed.
 
Definition irr_conj (theta : irr H) g (HnG : H <| G) (GiG : g \in G) :=
  get_irr H (character_conj (character_of_irr theta) HnG GiG)%CH.

Lemma irr_conjE : forall (theta : irr H) g (HnG : H <| G) (GiG : g \in G),
  irr_conj theta HnG GiG = (theta^g)%CH :> cfun _ _.
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

Definition cconjugates (G : {set gT}) (f : cfun gT algC) := 
 map (fun i => (f ^ (repr i))%CH)
  (filter (fun i => i \in (mem (rcosets 'I_(G)[f] G)))
   (index_enum (set_of_finType (FinGroup.finType gT)))).

Lemma cconjugatesP : forall f1 f2,
  reflect (exists2 g : gT, g \in G & f2 = (f1^g)%CH) (f2 \in cconjugates G f1).
Proof.
move=> f1 f2.
have F1: forall g, g \in G -> repr ('I_(G)[f1] :* g) \in G.
  move=> g GiG; suff: [group of 'I_(G)[f1]] :* g \subset G.
    by move/subsetP; apply; exact: mem_repr_rcoset.
  apply/subsetP=> h; case/rcosetP=> h1 H1iG->; rewrite groupM //.
  by apply: (subsetP (inertia_sub f1)).
apply: (iffP idP)=> [|[g GiG ->]].
  case/mapP=> C; rewrite mem_filter.
  case/andP; case/rcosetsP=> g GiG -> _ ->.
  by exists (repr ('I_(G)[f1] :* g))=> //; exact: F1.
have:= (mem_repr_rcoset [group of ('I_(G)[f1])] g).
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
  move=> g GiG; suff: [group of 'I_(G)[f]] :* g \subset G.
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

Lemma cconjugates1 : H <| G -> cconjugates G (irr1 H) = [::(irr1 H : cfun _ _)].
Proof.
move=> HnG.
have: forall f, f \in cconjugates G (irr1 H) -> f = irr1 H .
  move=> f; case/cconjugatesP=> g GiG ->.
  apply/cfunP=> h; rewrite cfunE !irr1E.
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
   \big[op/idx]_(i : irr H | ((i : cfun _ _) \in cconjugates G theta)) 
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
  'Res[H] chi = '['Res[H] chi, theta]_H *: \sum_(f <- cconjugates G theta) f.
Proof.
move=> chi theta HnG IC.
rewrite -cconjugates_sum //=.
pose cr := character_restrict (normal_sub HnG) (character_of_irr chi).
have CFchi: 'Res[H] chi \in 'CF(H) by apply: (character_in_cfun cr).
rewrite {1}(ncoord_sum CFchi).
rewrite (bigID (fun i : irr H => (i : cfun _ _)  \in cconjugates G theta)) /=.
rewrite [\sum_(i | _ \notin _)_]big1 ?addr0=> [|phi].
  rewrite scaler_sumr; apply: eq_bigr=> phi Hp; congr (_ *: _).
  rewrite (ncoord_inner_prod _ CFchi).
  case/cconjugatesP: Hp => g GiG ->.
  by apply: cfun_conj_inner_restrict=> //; exact: character_in_cfun.
move=> HH.
have: '['Res[H] ('Ind[G,H] theta), phi]_H = 0.
  have->: 'Res[H] ('Ind[G,H] theta) = 
               #|H|%:R^-1 *: (\sum_(c \in G) (theta ^ c)%CH).
    rewrite (reindex invg); last by exists invg=> g; rewrite invgK.
    apply/cfunP=> h; rewrite !(cfunE,sum_cfunE).
    case: (boolP (_ \in _))=> HiH; last first.
      rewrite mul0r big1 ?(mulr0) // => h1 H1iG.
      rewrite cfunE (cfun0 (irr_in_cfun _)) // invgK.
      apply/negP=> HH1; case/negP: HiH.
      rewrite -[h]conjg1 -[1%g](mulgK h1) mul1g conjgM.
      move/normalP: {cr}HnG; case=> _; move/(_ _ H1iG) <-.
      by apply/imsetP; exists (h^ h1)%g.
    rewrite mul1r; congr (_ * _); apply: eq_big=> g1; first by rewrite groupV.
    by rewrite !(cfunE,invgK).
  rewrite -inner_prodbE linearZ linear_sum; rewrite big1 ?scaler0 // => g GiG.
  rewrite /= inner_prodbE -(irr_conjE _ HnG GiG) irr_orthonormal.
  case: eqP=> // HH1; case/negP: HH; rewrite -HH1 irr_conjE.
  by apply/cconjugatesP; exists g.
rewrite (ncoord_inner_prod _ CFchi).
have CFInd: ('Ind[G, H] theta) \in 'CF(G).
   by apply: (cinduced_in_cfun (normal_sub HnG)); exact: irr_in_cfun.
rewrite {1}(ncoord_sum CFInd) linear_sum /=.
rewrite -inner_prodbE linear_sum /= => HH1. 
have: '['Res[H] (ncoord chi ('Ind[G, H] theta) *: (chi: cfun _ _)),phi]_H = 0.
  apply: (posC_sum_eq0 _ HH1)=> [theta1 _|]; last first.
    by rewrite /index_enum -enumT mem_enum.
  apply: posC_isNatC.
  pose ch1 := character_of_irr phi; set u := 'Res[_] _.
  suff ICu: is_char H u.
    by apply: (inner_prod_char_nat (Character ICu) ch1).
  apply: (is_char_restrict (normal_sub HnG)).
  pose cr1 := (character_induced (character_of_irr theta) (normal_sub HnG)).
  case/isNatCP: (char_isNatC_ncoord theta1 cr1)=> /= n ->.
  by rewrite scaler_nat is_char_scal // is_char_irr.
rewrite linearZ /= -inner_prodbE linearZ /= inner_prodbE.
move/eqP; rewrite mulf_eq0; case/orP; last first.
  by move/eqP->; rewrite scale0r.
move: IC.
rewrite /is_comp (ncoord_inner_prod _ CFchi) (ncoord_inner_prod _ CFInd).
rewrite (inner_prod_charC cr) (frobenius_reciprocity (normal_sub HnG))
        ?character_in_cfun //= => HH2 HH3.
by case/negP: HH2.
Qed.

(* This is Isaacs' 6.7 *)
Lemma cker_is_comp1 : forall chi : irr G, 
  H <| G -> is_comp (irr1 H) ('Res[H] chi) -> H \subset cker G chi.
Proof.
move=> chi HnG IC; apply/subsetP=> h HiH.
rewrite irr_ckerE inE (subsetP (normal_sub HnG)) //.
move: (is_comp_clifford HnG IC).
rewrite cconjugates1 // big_cons big_nil addr0=> HH.
move/cfunP: (HH); move/(_ 1%g).
rewrite cfunE group1 mul1r.
rewrite [fun_of_cfun (_ *: _) 1%g]cfunE irr1E group1 mulr1=> HH1.
move/cfunP: HH; move/(_ h).
rewrite -HH1 cfunE HiH mul1r => ->.
by rewrite cfunE irr1E HiH mulr1 eqxx.
Qed.

(* This is Isaacs' 6.8 *)
Lemma is_comp_val1_div : forall (chi : irr G) (theta : irr H), 
  H <| G -> is_comp theta ('Res[H] chi) -> 
    exists n: nat, chi 1%g = n%:R * theta 1%g.
Proof.
move=> chi theta HnG IC.
exists (getNatC ('['Res[H] chi, theta ]_ H) * (size (cconjugates G theta)))%N.
rewrite natr_mul.
pose cr := character_restrict (normal_sub HnG) (character_of_irr chi).
move: (inner_prod_char_nat cr (character_of_irr theta)).
rewrite getNatCP=> /=; move/eqP<-.
have->: chi 1%g = ('Res[H] chi) 1%g by rewrite !cfunE !(group1,mul1r).
rewrite {1}(is_comp_clifford HnG IC).
rewrite cfunE -mulrA; congr (_ * _).
rewrite sum_cfunE cfunE.
have: forall f, f \in cconjugates G theta -> f 1%g = theta 1%g.
  by move=> f; case/cconjugatesP=> g GiG ->; rewrite cfunE conj1g.
elim: (cconjugates _ _)=> [|f l IH HF]; first by rewrite big_nil mul0r.
rewrite big_cons HF ?(inE,eqxx) // IH=> [|f1 Hf1].
  by rewrite /= -add1n natr_add mulr_addl mul1r.
by rewrite HF // inE Hf1 orbT.
Qed.

Lemma cconjugates_induced : forall (f1 f2 : cfun gT algC),
   H <| G ->  f1 \in 'CF(H) -> f2 \in 'CF(H) -> f2 \in cconjugates G f1 ->  
   'Ind[G,H] f1 = 'Ind[G,H] f2.
Proof.
move=> f1 f2 HnG Cf1 Cf2 HH; case/cconjugatesP: HH Cf2=> g GiG -> Cf2.
apply/cfunP=> h; case: (boolP (h \in G))=> [HiG| HniG]; last first.
rewrite !(cfun0 (cinduced_in_cfun _ _)) ?(normal_sub HnG) //.
rewrite !cfunE; congr (_ * _).
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

Section MoreInertia.

Variable gT : finGroupType.

Lemma cconjugates_inertia : forall (G H : {group gT}) (theta : irr H),
   cconjugates 'I_(G)[theta] theta = [::(theta : cfun _ _)].
Proof.
move=> G H theta.
have: forall f, f \in cconjugates 'I_(G)[theta] theta -> f = theta.
  move=> f; case/cconjugatesP=> g.
  by rewrite inE; case/andP=> _; move/eqP->.
pose IG := [group of 'I_(G)[theta]].
move: (mem_cconjugates IG theta) (unique_cconjugates IG theta) => /=. 
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

Let T := [group of 'I_(G)[theta]].

Hypothesis HnG : H <| G.

Let TsG := inertia_sub G theta.

Let HsT : H \subset T.
Proof.
apply: subset_inertia=> //.
by exact: irr_in_cfun.
Qed.

Let HnT : H <| T.
apply: normalS (HnG).
  apply: subset_inertia=> //.
  by exact: irr_in_cfun.
exact: inertia_sub.
Qed.

Section Chi.

Variable psi : irr T.

Hypothesis Hpsi : is_comp theta ('Res[H] psi).

Variable chi : irr G.

Hypothesis Hchi : is_comp chi ('Ind[G,T] psi).

Let chir := character_restrict TsG (character_of_irr chi).

Fact is_comp_inertia_restrict_is_comp_i : is_comp psi chir.
Proof.
rewrite /is_comp ncoord_inner_prod; last first.
  by apply: (crestrict_in_cfun _ (character_in_cfun _)).
move: Hchi.
rewrite /is_comp ncoord_inner_prod; last first.
by apply cinduced_in_cfun=> //; apply: irr_in_cfun.
rewrite -frobenius_reciprocity ?(irr_in_cfun, character_in_cfun) //.
by rewrite (inner_prod_charC (character_of_irr psi) chir).
Qed.

Let psir :=  character_restrict HsT (character_of_irr psi).

Let chir' :=  character_restrict (normal_sub HnG) (character_of_irr chi).

Fact is_comp_inertia_restrict_is_comp_g : is_comp theta ('Res[H] chi).
Proof.
move: (is_comp_inner_prod_le theta HsT is_comp_inertia_restrict_is_comp_i).
rewrite crestrict_subset //.
rewrite -!ncoord_inner_prod ?(character_in_cfun psir) //; last first.
  exact: (character_in_cfun chir').
move: Hpsi; rewrite /is_comp /=.
case/isNatCP: (char_isNatC_ncoord theta psir)=> n ->.
case/isNatCP: (char_isNatC_ncoord theta chir')=> m ->.
by rewrite -!neq0N_neqC -leq_leC; case: m=> //; case: n.
Qed.

Let e := '['Res[H] chi, theta ]_ H.

Let f := '['Res[H] psi, theta ]_ H.

Let He : 'Res[H] chi = e *: (\sum_(f <- cconjugates G theta) f).
Proof. exact: (is_comp_clifford HnG is_comp_inertia_restrict_is_comp_g). Qed.

Let Hf  : 'Res[H] psi = f *: (theta : cfun _ _).
Proof.
move: (is_comp_clifford  HnT Hpsi).
rewrite cconjugates_inertia.
by rewrite big_cons big_nil addr0.
Qed.

Let He1 : chi 1%g = e * #|G : T|%:R * (theta 1%g).
Proof.
move/cfunP: He; move/(_ 1%g).
rewrite cfunE group1 mul1r => ->.
rewrite cfunE sum_cfunE cfunE -mulrA; congr (_ * _).
rewrite -cconjugates_sum //=.
rewrite (eq_bigr (fun (i: irr H) => theta 1%g))=> [|i]; last first.
  case/cconjugatesP=> g GiG ->.
  by rewrite cfun_conj_val1.
rewrite (cconjugates_sum _ (fun i : cfun _ _ => theta 1%g)) //=.
rewrite -cconjugates_size.
elim: cconjugates=> [|f1 l IH].
  by rewrite big_nil mul0r.
by rewrite big_cons IH /= -add1n natr_add mulr_addl mul1r.
Qed.

Let Hpsi1  : ('Ind[G, T] psi) 1%g = f * #|G : T|%:R * (theta 1%g).
Proof.
pose psii := character_induced (character_of_irr psi) TsG.
rewrite cfunE.
rewrite (eq_bigr (fun (c : gT) => psi 1%g))=> [|g GiG]; last first.
  by rewrite conj1g.
rewrite sumr_const.
move/cfunP: Hf; move/(_ 1%g).
rewrite cfunE group1 mul1r => ->.
rewrite [fun_of_cfun (_ *: _) _]cfunE.
apply: (mulfI (neq0GC T)).
rewrite mulrA mulfV ?neq0GC // mul1r. 
rewrite mulrCA  mulrA -[_ *+ #|_|]mulr_natl mulrA; congr (_ * _).
rewrite [_ * f]mulrC -[(f * _) * _]mulrA [#|_ : _|%:R * _]mulrC.
by rewrite -natr_mul LaGrange.
Qed.

Fact inner_prod_is_comp_inertia_is_comp : f = e.
have F3 : f <= e.
  move: (is_comp_inner_prod_le theta HsT is_comp_inertia_restrict_is_comp_i).
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
  rewrite sposC_mul // ?irr1_posC //.
  rewrite /ltC -neq0N_neqC posC_nat.
  by case: #|_:_| (indexg_gt0 G T).
move/leC_pmul2r=> <-.
rewrite mulrA -He1 mulrA -Hpsi1.
pose psii := character_induced (character_of_irr psi) TsG.
have: is_comp chi psii by [].
case/is_compP=> chi' /= ->.
rewrite [fun_of_cfun (_ + _) 1%g]cfunE.
rewrite addrC -leC_sub addrK.
by apply: posC_isNatC; apply: isNatC_character1.
Qed.

Fact is_comp_inertia_induced_is_comp : 'Ind[G, T] psi = chi.
Proof.
pose psii := character_induced (character_of_irr psi) TsG.
have: is_comp chi psii by [].
case/is_compP=> chi' /= Hchi'; rewrite Hchi'.
move/cfunP: Hchi'; move/(_ 1%g).
rewrite Hpsi1 inner_prod_is_comp_inertia_is_comp -He1.
rewrite [fun_of_cfun (_ + _) _]cfunE -{1}[chi _]addr0; move/addrI.
move/eqP; rewrite eq_sym -character0_eq0; move/eqP->.
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
  rewrite (ncoord_sum (cinduced_in_cfun _ _)) ?irr_in_cfun //.
  rewrite big1 // => i _.
  move: (HH i); rewrite /is_comp; move/idP; move/negP.
  by rewrite negbK; move/eqP->; rewrite scale0r.
rewrite (induced0 (character_of_irr psi) TsG).
move/eqP; move/val_eqP=>/=; move/eqP; move/cfunP; move/(_ 1%g)=> HH1.
by case/negP: (irr1_neq0 psi); rewrite HH1 cfunE.
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
pose chir := character_restrict TsG (character_of_irr chi).
have: is_comp psi' chir by [].
case/is_compP=> chi1 Hchi1.
apply/eqP; case: (_ =P _)=> //; move/eqP=> Dpsi.
have: is_comp psi chi1.
  have: is_comp psi chir.
    by apply: is_comp_inertia_restrict_is_comp_i.
  rewrite /is_comp !ncoord_inner_prod ?character_in_cfun //.
  by rewrite Hchi1 -inner_prodbE linearD ![inner_prodb_linear _ _ _] /= 
            !inner_prodbE irr_orthonormal (negPf Dpsi) add0r.
case/is_compP=> chi2 Hchi2.
have: '['Res[H] psi, theta]_H < '['Res[H] chir, theta]_H.
  rewrite Hchi1 addrC Hchi2 2!linearD /=.
  rewrite -!inner_prodbE 2!linearD /= !inner_prodbE.
  rewrite -addrA addrC ltC_sub addrK sposC_addl //.
    rewrite -ncoord_inner_prod //; last first.
      by apply: (crestrict_in_cfun HsT (character_in_cfun _)).
    apply: posC_isNatC; apply: is_char_isNatC_ncoord.
    by apply: (is_char_restrict HsT (is_char_character _)).
  move: Ct; rewrite /is_comp -ncoord_inner_prod //.
    rewrite /ltC => ->.
    apply: posC_isNatC; apply: is_char_isNatC_ncoord.
    by apply: (is_char_restrict HsT (is_char_character _)).
  by apply: (crestrict_in_cfun HsT (character_in_cfun _)).
rewrite inner_prod_is_comp_inertia (is_comp_inertia_induced_is_comp Hpsi Hchi).
by rewrite crestrict_subset // ltC_sub subrr /ltC eqxx.
Qed.

End S611A.

(* This is 6.11 b it is an injection *)
Lemma injective_is_comp_inertia : forall (G H : {group gT}) (theta : irr H),
 H <| G ->
 {in [pred psi: irr [group of 'I_(G)[theta]] | is_comp theta ('Res[H] psi)] &,
    injective (fun psi : irr [group of 'I_(G)[theta]] => 
                  'Ind[G, 'I_(G)[theta]] psi)}.
Proof.
move=> G H theta HnG psi psi' Hpsi Hpsi' Heq.
have TsG := inertia_sub G theta.
apply: (unique_is_comp_inertia HnG Hpsi' _ Hpsi).
rewrite -Heq /is_comp ncoord_inner_prod; last first.
  apply: (crestrict_in_cfun TsG).
  apply: (cinduced_in_cfun TsG).
  by apply: irr_in_cfun.
pose psii := character_induced (character_of_irr psi) TsG.
pose psiir := character_restrict TsG psii.
rewrite (inner_prod_charC psiir (character_of_irr psi)).
rewrite character_restE.
rewrite (frobenius_reciprocity TsG) ?character_in_cfun //.
rewrite inner_prod0; last first.
  by apply: cinduced_in_cfun=> //; exact: character_in_cfun.
rewrite induced0 //.
apply/negP; move/eqP; move/val_eqP; move/eqP; move/cfunP; move/(_ 1%g).
rewrite /= [_ 0 _]cfunE=> HH.
by case/eqP: (irr1_neq0 psi).
Qed.

(* 6.11 b the inverse function *)
Definition inertia_induced_inv (G H : {group gT})
                (theta : irr H) (chi : cfun gT algC) :=
  odflt (irr1 [group of 'I_(G)[theta]])
           (pick [pred t : irr  [group of 'I_(G)[theta]] |
                   is_comp theta ('Res[H] t) && 
                   is_comp t ('Res['I_(G)[theta]] chi)]).

Let inertia_ncoord :
 forall (G H : {group gT}) (theta : irr H) (chi : irr G),
    H <| G ->
   [pred psi : irr [group of 'I_(G)[theta]] | 
                 is_comp theta ('Res[H] psi) &&
                 is_comp psi ('Res['I_(G)[theta]] chi)] =1 xpred0 ->
   ncoord theta ('Res[H] chi) == 0.
Proof.
move=> G H theta chi HnG HH.
rewrite ncoord_inner_prod; last first.
  by apply: (crestrict_in_cfun (normal_sub HnG) (irr_in_cfun _)).
have HsT := subset_inertia (irr_in_cfun theta) HnG.
rewrite -(crestrict_subset chi HsT).
rewrite (ncoord_sum (crestrict_in_cfun (inertia_sub G theta) (irr_in_cfun _))) //.
rewrite linear_sum -inner_prodbE linear_sum big1 //= => chi1 _.
rewrite inner_prodbE linearZ -inner_prodbE linearZ /= inner_prodbE.
rewrite -ncoord_inner_prod ?(crestrict_in_cfun HsT, irr_in_cfun) //.
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
  apply: cinduced_in_cfun; last by apply: irr_in_cfun.
  by apply:inertia_sub.
rewrite -frobenius_reciprocity; first last.
- by apply: irr_in_cfun.
- by apply: irr_in_cfun.
- by apply:inertia_sub.
move: (inertia_induces_inv_is_comp_i HnG Cchi).
rewrite /is_comp ncoord_inner_prod; last first.
  by apply: (crestrict_in_cfun (inertia_sub _ _) (irr_in_cfun _)).
pose chir := character_restrict (inertia_sub G theta) (character_of_irr chi).
by rewrite (inner_prod_charC chir (character_of_irr _)) .
Qed.

End S611.