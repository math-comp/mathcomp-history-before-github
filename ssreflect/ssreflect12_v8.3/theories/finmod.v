(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq paths div.
Require Import choice fintype bigops ssralg finset groups morphisms perm.
Require Import finalg action gprod cyclic commutators.

(******************************************************************************)
(*  This file regroups constructions and results that are based on the most   *)
(* primitive version of representation theory -- viewing an abelian group as  *)
(* the additive group of a (finite) Z-module. This includes the Gaschutz      *)
(* splitting and transitivity theorem, from which we will later derive the    *)
(* Schur-Zassenhaus theorem and the elementary abelian special case of        *)
(* Measchke's theorem, the coprime abelian centraliser/commutator trivial     *)
(* intrsection theorem, from which we will derive that p-groups under coprime *)
(* action factor into special groups, and the construction of the transfer    *)
(* homomorphism and its expansion relative to a cycle, from which we derive   *)
(* the Higman Focal Subgroup and the Burside Normal Complement Theorems.      *)
(*   The definitions and lemmas for the finite Z-module induced by an abelian *)
(* are packaged in an auxiliary FiniteModule submodule: they should not be    *)
(* needed much outside this file, which contains all the results that exploit *)
(* this construction.                                                         *)
(*   FiniteModule defines the Z[N(A)]-module associated with a finite abelian *)
(* abelian group A, given a proof abelA : abelian A) :                        *)
(*  fmod_of abelA == the type of elements of the module (similar to but       *)
(*                   distinct from subg_of A).                                *)
(*   fmod abelA x == the injection of x into fmod_of abelA if x \in A, else 0 *)
(*        fmval u == the projection of u : fmod_of abelA onto A               *)
(*         u ^@ x == the action of x \in 'N(A) on u : fmod_of abelA           *)
(* The transfer morphism is be constructed from a morphism f : H >-> rT, and  *)
(* a group G, along with the two assumptions sHG : H \subset G and            *)
(* abfH : abelian (f @* H):                                                   *)
(*  transfer sGH abfH == the function gT -> FiniteModule.fmod_of abfH that    *)
(*                   implements the transfer morphism induced by f on G.      *)
(*  rcosets_transversal G H X == the function X : {set gT} -> gT defines a    *)
(*                   transversal of the right cosets of H in G: it maps each  *)
(*                   coset H :* x to some y_x \in H :* x, for each x \in G.   *)
(*                   The Lemma transfer_indep states that the transfer        *)
(*                   morphism can be expanded using any transversal.          *)
(*  rcosets_pcycle_transversal G H g X == X is a transversal of the orbits of *)
(*                   the regular action of the cycle <[g]> generated by g on  *)
(*                   the set of right cosets of H if H \subset G and g \in G, *)
(*                   and more generally the function r mapping x : gT to      *)
(*                   rcosets (H :* x) <[g]> is (constructively) a bijection   *)
(*                   from X to a partition of a partition of G: we have       *)
(*                   {in X &, injective r}, X \subset G  and                  *)
(*                   G \subset H * X * <[g]>. The transfer_pcycle_def Lemma   *)
(*                   gives a simplified expansion of the transfer morphism,   *)
(*                   given a set X with this property.                        *)
(*  rcosets_pcycle_transversal_witness G H g == the sigma Type associated     *)
(*                   with the predicate above; it encapsulates a set X, the   *)
(*                   rcosets_pcycle_transversal G H g X property, and an      *)
(*                   abbreviation n_ x for the coefficient #|r x| (with r     *)
(*                   defined as above), which is used in the expansion        *)
(*                   supplied by transfer_pcycle_def.                         *)
(* For applications that do not require a specific transversal, the           *)
(* rcosets_pcycle_transversal_exists Lemma provides a default instance of an  *)
(* rcosets_pcycle_transversal_witness.                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory FinRing.Theory.
Local Open Scope ring_scope.

Module FiniteModule.

Reserved Notation "u ^@ x" (at level 31, left associativity).

Inductive fmod_of (gT : finGroupType) (A : {group gT}) (abelA : abelian A) :=
  Fmod x & x \in A.

Bind Scope ring_scope with fmod_of.

Section OneFinMod.

Let f2sub (gT : finGroupType) (A : {group gT}) (abA : abelian A) :=
  fun u : fmod_of abA => let : Fmod x Ax := u in Subg Ax : FinGroup.arg_sort _.
Local Coercion f2sub : fmod_of >-> FinGroup.arg_sort.

Variables (gT : finGroupType) (A : {group gT}) (abelA : abelian A).
Local Notation fmodA := (fmod_of abelA).
Implicit Types x y z : gT.
Implicit Types u v w : fmodA.

Let sub2f (s : subg_of A) := Fmod abelA (valP s).

Definition fmval u := val (f2sub u).
Canonical Structure fmod_subType := [subType for fmval by @fmod_of_rect _ _ _].
Local Notation valA := (@val _ _ fmod_subType) (only parsing).
Definition fmod_eqMixin := Eval hnf in [eqMixin of fmodA by <:].
Canonical Structure fmod_eqType := Eval hnf in EqType fmodA fmod_eqMixin.
Definition fmod_choiceMixin := [choiceMixin of fmodA by <:].
Canonical Structure fmod_choiceType :=
  Eval hnf in ChoiceType fmodA fmod_choiceMixin.
Definition fmod_countMixin := [countMixin of fmodA by <:].
Canonical Structure fmod_countType :=
  Eval hnf in CountType fmodA fmod_countMixin.
Canonical Structure fmod_subCountType := Eval hnf in [subCountType of fmodA].
Definition fmod_finMixin := [finMixin of fmodA by <:].
Canonical Structure fmod_finType := Eval hnf in FinType fmodA fmod_finMixin.
Canonical Structure fmod_subFinType := Eval hnf in [subFinType of fmodA].

Definition fmod x := sub2f (subg A x).
Definition actr u x := if x \in 'N(A) then fmod (fmval u ^ x) else u.

Definition fmod_opp u := sub2f u^-1.
Definition fmod_add u v := sub2f (u * v).

Lemma fmod_add0r : left_id (sub2f 1) fmod_add.
Proof. move=> u; apply: val_inj; exact: mul1g. Qed.

Lemma fmod_addrA : associative fmod_add.
Proof. move=> u v w; apply: val_inj; exact: mulgA. Qed.

Lemma fmod_addNr : left_inverse (sub2f 1) fmod_opp fmod_add.
Proof. move=> u; apply: val_inj; exact: mulVg. Qed.

Lemma fmod_addrC : commutative fmod_add.
Proof. case=> x Ax [y Ay]; apply: val_inj; exact: (centsP abelA). Qed.

Definition fmod_zmodMixin := 
  ZmodMixin fmod_addrA fmod_addrC fmod_add0r fmod_addNr.
Canonical Structure fmod_zmodType := Eval hnf in ZmodType fmodA fmod_zmodMixin.
Canonical Structure fmod_finZmodType := Eval hnf in [finZmodType of fmodA].
Canonical Structure fmod_baseFinGroupType :=
  Eval hnf in [baseFinGroupType of fmodA for +%R].
Canonical Structure fmod_finGroupType :=
  Eval hnf in [finGroupType of fmodA for +%R].

Lemma fmodP : forall u, val u \in A. Proof. exact: valP. Qed.
Lemma fmod_inj : injective fmval. Proof. exact: val_inj. Qed.
Lemma congr_fmod : forall u v, u = v -> fmval u = fmval v.
Proof. exact: congr1. Qed.

Lemma fmvalA : {morph valA : x y / x + y >-> (x * y)%g}. Proof. by []. Qed.
Lemma fmvalN : {morph valA : x / - x >-> x^-1%g}. Proof. by []. Qed.
Lemma fmval0 : valA 0 = 1%g. Proof. by []. Qed.
Canonical Structure fmval_morphism := @Morphism _ _ setT fmval (in2W fmvalA).

Lemma fmvalZ : forall n, {morph valA : x / x *+ n >-> (x ^+ n)%g}.
Proof. by move=> n u; rewrite /= morphX ?inE. Qed.

Lemma fmodKcond : forall x, val (fmod x) = if x \in A then x else 1%g.
Proof. by move=> x; rewrite /= /fmval /= val_insubd. Qed.
Lemma fmodK : {in A, cancel fmod val}. Proof. exact: subgK. Qed.
Lemma fmvalK : cancel val fmod.
Proof. by case=> x Ax; apply: val_inj; rewrite /fmod /= sgvalK. Qed.
Lemma fmod1 : fmod 1 = 0. Proof. by rewrite -fmval0 fmvalK. Qed.
Lemma fmodM : {in A &, {morph fmod : x y / (x * y)%g >-> x + y}}.
Proof. by move=> x y Ax Ay /=; apply: val_inj; rewrite /fmod morphM. Qed.
Canonical Structure fmod_morphism := Morphism fmodM.
Lemma fmodX : forall n, {in A, {morph fmod : x / (x ^+ n)%g >-> x *+ n}}.
Proof. exact: morphX. Qed.
Lemma fmodV : {morph fmod : x / x^-1%g >-> - x}.
Proof. 
move=> x; apply: val_inj; rewrite fmvalN !fmodKcond groupV.
by case: (x \in A); rewrite ?invg1.
Qed.

Lemma injm_fmod : 'injm fmod.
Proof. 
apply/injmP=> x y Ax Ay []; move/val_inj; exact: (injmP _ (injm_subg A)).
Qed.

Notation "u ^@ x" := (actr u x) : ring_scope.

Lemma fmvalJcond : forall u x,
  val (u ^@ x) = if x \in 'N(A) then val u ^ x else val u.
Proof.
by move=> u x; case: ifP => Nx; rewrite /actr Nx ?fmodK // memJ_norm ?fmodP.
Qed.

Lemma fmvalJ : forall u x, x \in 'N(A) -> val (u ^@ x) = val u ^ x.
Proof. by move=> u x Nx; rewrite fmvalJcond Nx. Qed.

Lemma fmodJ : forall x y, y \in 'N(A) -> fmod (x ^ y) = fmod x ^@ y.
Proof.
move=> x y Ny; apply: val_inj; rewrite fmvalJ ?fmodKcond ?memJ_norm //.
by case: ifP => -> //; rewrite conj1g.
Qed.

Lemma actr_is_action : is_action 'N(A) actr.
Proof.
split=> [a u v eq_uv_a | u a b Na Nb].
  case Na: (a \in 'N(A)); last by rewrite /actr Na in eq_uv_a.
  by apply: val_inj; apply: (conjg_inj a); rewrite -!fmvalJ ?eq_uv_a.
by apply: val_inj; rewrite !fmvalJ ?groupM ?conjgM.
Qed.

Canonical Structure actr_action := Action actr_is_action.
Notation "''M'" := actr_action (at level 0) : action_scope.

Lemma act0r : forall x, 0 ^@ x = 0.
Proof. by move=> x; rewrite /actr conj1g morph1 if_same. Qed.

Lemma actAr : forall x, {morph actr^~ x : u v / u + v}.
Proof.
move=> x u v; apply: val_inj; rewrite !(fmvalA, fmvalJcond) conjMg.
by case: (x \in 'N(A)).
Qed.

Definition actr_sum x := big_morph _ (actAr x) (act0r x).

Lemma actNr : forall x, {morph actr^~ x : u / - u}.
Proof.
by move=> x u; apply: (@addrI _ (u ^@ x)); rewrite -actAr !subrr act0r.
Qed.

Lemma actZr : forall x n, {morph actr^~ x : u / u *+ n}.
Proof.
by move=> x n u; elim: n => [|n IHn]; rewrite ?act0r // !mulrS actAr IHn.
Qed.

Lemma actr_is_groupAction : is_groupAction setT 'M.
Proof.
move=> a Na /=; rewrite inE; apply/andP; split.
  by apply/subsetP=> u _; rewrite inE.
by apply/morphicP=> u v _ _; rewrite !permE /= actAr.
Qed.

Canonical Structure actr_groupAction := GroupAction actr_is_groupAction.
Notation "''M'" := actr_groupAction (at level 0) : groupAction_scope.

Lemma actr1 : forall u, u ^@ 1 = u.
Proof. exact: act1. Qed.

Lemma actrM : {in 'N(A) &, forall x y u, u ^@ (x * y) = u ^@ x ^@ y}.
Proof.
by move=> x y Nx Ny /= u; apply: val_inj; rewrite !fmvalJ ?conjgM ?groupM.
Qed.

Lemma actrK : forall x, cancel (actr^~ x) (actr^~ x^-1%g). 
Proof.
move=> x u; apply: val_inj; rewrite !fmvalJcond groupV.
by case: ifP => -> //; rewrite conjgK.
Qed.

Lemma actrKV : forall x, cancel (actr^~ x^-1%g) (actr^~ x). 
Proof. by move=> x u; rewrite -{2}(invgK x) actrK. Qed.

End OneFinMod.

Bind Scope ring_scope with fmod_of.
Prenex Implicits fmval fmod actr.
Notation "u ^@ x" := (actr u x) : ring_scope.
Notation "''M'" := actr_action (at level 0) : action_scope.
Notation "''M'" := actr_groupAction : groupAction_scope.

End FiniteModule.

Canonical Structure FiniteModule.fmod_subType.
Canonical Structure FiniteModule.fmod_eqType.
Canonical Structure FiniteModule.fmod_choiceType.
Canonical Structure FiniteModule.fmod_countType.
Canonical Structure FiniteModule.fmod_finType.
Canonical Structure FiniteModule.fmod_subCountType.
Canonical Structure FiniteModule.fmod_subFinType.
Canonical Structure FiniteModule.fmod_zmodType.
Canonical Structure FiniteModule.fmod_finZmodType.
Canonical Structure FiniteModule.fmod_baseFinGroupType.
Canonical Structure FiniteModule.fmod_finGroupType.

(* Still allow ring notations, but give priority to groups now. *)
Import FiniteModule GroupScope.

Section Gaschutz.

Variables (gT : finGroupType) (G H P : {group gT}).
Implicit Types K L : {group gT}.

Hypotheses (nsHG : H <| G) (sHP : H \subset P) (sPG : P \subset G).
Hypotheses (abelH : abelian H) (coHiPG : coprime #|H| #|G : P|).

Let sHG := normal_sub nsHG.
Let nHG := subsetP (normal_norm nsHG).

Let m := (expgn_inv H #|G : P|).

Implicit Types a b : fmod_of abelH.
Local Notation fmod := (fmod abelH).

Theorem Gaschutz_split : [splits G, over H] = [splits P, over H].
Proof.
apply/splitsP/splitsP=> [[K] | [Q]].
  case/complP=> trHK eqHK; exists (K :&: P)%G.
  rewrite inE setICA (setIidPl sHP) setIC trHK eqxx group_modl // eqHK.
  by rewrite (sameP eqP setIidPr).
case/complP=> trHQ eqHQ.
have sQP: Q \subset P by rewrite -eqHQ mulG_subr.
pose rP x := repr (P :* x); pose pP x := x * (rP x)^-1.
have PpP: pP _ \in P by move=> x; rewrite -mem_rcoset rcoset_repr rcoset_refl.
have rPmul : forall x y, x \in P -> rP (x * y) = rP y.
  by move=> x y Px; rewrite /rP rcosetM rcoset_id.
pose pQ x := remgr H Q x; pose rH x := pQ (pP x) * rP x.
have pQhq: {in H & Q, forall h q, pQ (h * q) = q} by exact: remgrMid.
have pQmul: {in P &, {morph pQ : x y / x * y}}.
  apply: remgrM; [exact/complP | exact: normalS (nsHG)].
have HrH: forall x, rH x \in H :* x.
  move=> x; rewrite rcoset_sym mem_rcoset invMg mulgA mem_divgr //.
  by rewrite eqHQ PpP.
have GrH: forall x, x \in G -> rH x \in G.
  move=> x Gx; case/rcosetP: (HrH x) => y Hy ->.
  by rewrite groupM // (subsetP sHG).
have rH_Pmul: forall x y, x \in P -> rH (x * y) = pQ x * rH y.
  by move=> *; rewrite /rH mulgA -pQmul; first by rewrite /pP rPmul ?mulgA.
have rH_Hmul: forall h y, h \in H -> rH (h * y) = rH y.
  by move=> h y Hh; rewrite rH_Pmul ?(subsetP sHP) // -(mulg1 h) pQhq ?mul1g.
pose mu x y := fmod ((rH x * rH y)^-1 * rH (x * y)).
pose nu y := (\sum_(Px \in rcosets P G) mu (repr Px) y)%R.
have rHmul : {in G &, forall x y, rH (x * y) = rH x * rH y * val (mu x y)}.
  move=> x y Gx Gy; rewrite /= fmodK ?mulKVg // -mem_lcoset lcoset_sym.
  rewrite -norm_rlcoset; last by rewrite nHG ?GrH ?groupM.
  by rewrite (rcoset_transl (HrH _)) -rcoset_mul ?nHG ?GrH // mem_mulg.
have actrH : forall a x, x \in G -> (a ^@ rH x = a ^@ x)%R.
  move=> a x Gx; apply: val_inj; rewrite /= !fmvalJ ?nHG ?GrH //.
  case/rcosetP: (HrH x) => b; move/(fmodK abelH)=> <- ->; rewrite conjgM.
  by congr (_ ^ _); rewrite conjgE -fmvalN -!fmvalA (addrC a) addKr.
have mu_Pmul: forall x y z, x \in P -> mu (x * y) z = mu y z.
  move=> x y z Px; congr fmod; rewrite -mulgA !(rH_Pmul x) ?rPmul //.
  by rewrite -mulgA invMg -mulgA mulKg.
have mu_Hmul: forall x y z, x \in G -> y \in H -> mu x (y * z) = mu x z.
  move=> x y z Gx Hy; congr fmod.
  rewrite (mulgA x) (conjgCV x) -mulgA 2?rH_Hmul //.
  by rewrite -mem_conjg (normP _) ?nHG.
have{mu_Hmul} nu_Hmul: forall y z, y \in H -> nu (y * z) = nu z.
  move=> y z Hy; apply: eq_bigr => Px; case/rcosetsP=> x Gx ->{Px}.
  apply: mu_Hmul y z _ Hy.
  by rewrite -(groupMl _ (subsetP sPG _ (PpP x))) mulgKV.
have cocycle_mu: {in G & &, forall x y z,
  mu (x * y)%g z + mu x y ^@ z = mu y z + mu x (y * z)%g}%R.
- move=> x y z Gx Gy Gz; apply: val_inj.
  apply: (mulgI (rH x * rH y * rH z)).
  rewrite -(actrH _ _ Gz) addrC fmvalA fmvalJ ?nHG ?GrH //.
  rewrite mulgA -(mulgA _ (rH z)) -conjgC mulgA -!rHmul ?groupM //.
  by rewrite mulgA -mulgA -2!(mulgA (rH x)) -!rHmul ?groupM.
move: mu => mu in rHmul mu_Pmul cocycle_mu nu nu_Hmul.
have{cocycle_mu} cocycle_nu : {in G &, forall y z,
  nu z + nu y ^@ z = mu y z *+ #|G : P| + nu (y * z)%g}%R.
- move=> y z Gy Gz; rewrite /= (actr_sum z) /=.
  have ->: (nu z = \sum_(Px \in rcosets P G) mu (repr Px * y)%g z)%R.
    rewrite /nu (reindex_acts _ (actsRs_rcosets P G) Gy) /=.
    apply: eq_bigr => Px; case/rcosetsP=> x Gx /= ->{Px}.
    rewrite rcosetE -rcosetM.
    case: repr_rcosetP=> p1 Pp1; case: repr_rcosetP=> p2 Pp2.
    by rewrite -mulgA [x * y]lock !mu_Pmul.
  rewrite -sumr_const -!big_split /=; apply: eq_bigr => Px.
  case/rcosetsP=> x Gx ->{Px}; rewrite -cocycle_mu //.
  by case: repr_rcosetP=> p1 Pp1; rewrite groupMr // (subsetP sPG).
move: nu => nu in nu_Hmul cocycle_nu.
pose f x := rH x * val (nu x *+ m)%R.
have{cocycle_nu} fM: {in G &, {morph f : x y / x * y}}.
  move=> x y Gx Gy; rewrite /f ?rHmul // -3!mulgA; congr (_ * _).
  rewrite (mulgA _ (rH y)) (conjgC _ (rH y)) -mulgA; congr (_ * _).
  rewrite -fmvalJ ?actrH ?nHG ?GrH // -!fmvalA actZr -mulrn_addl.
  rewrite  -(addrC (nu y)) cocycle_nu // mulrn_addl !fmvalA; congr (_ * _).
  by rewrite !fmvalZ expgnK ?fmodP.
exists (Morphism fM @* G)%G; apply/complP; split.
  apply/trivgP; apply/subsetP=> x; case/setIP=> Hx.
  case/morphimP=> y _ Gy eq_x.
  apply/set1P; move: Hx; rewrite {x}eq_x /= groupMr ?subgP //.
  rewrite -{1}(mulgKV y (rH y)) groupMl -?mem_rcoset // => Hy.
  rewrite -(mulg1 y) /f nu_Hmul // rH_Hmul //; exact: (morph1 (Morphism fM)).
apply/setP=> x; apply/mulsgP/idP=> [[h y Hh fy ->{x}] | Gx].
  rewrite groupMl; last exact: (subsetP sHG).
  case/morphimP: fy => z _ Gz ->{x Hx y}.
  by rewrite /= /f groupMl ?GrH // (subsetP sHG) ?fmodP.
exists (x * (f x)^-1) (f x); last first; first by rewrite mulgKV.
  by apply/morphimP; exists x.
rewrite -groupV invMg invgK -mulgA (conjgC (val _)) mulgA.
by rewrite groupMl -(mem_rcoset, mem_conjg) // (normP _) ?nHG ?fmodP.
Qed.

Theorem Gaschutz_transitive : {in [complements to H in G] &,
  forall K L,  K :&: P = L :&: P -> exists2 x, x \in H & L :=: K :^ x}.
Proof.
move=> K L /=; set Q := K :&: P; case/complP=> trHK eqHK cpHL QeqLP.
have [trHL eqHL] := complP cpHL.
pose nu x := fmod (divgr H L x^-1).
have sKG: {subset K <= G} by apply/subsetP; rewrite -eqHK mulG_subr.
have sLG: {subset L <= G} by apply/subsetP; rewrite -eqHL mulG_subr.
have val_nu: forall x, x \in G -> val (nu x) = divgr H L x^-1.
  by move=> x Gx; rewrite fmodK // mem_divgr // eqHL groupV.
have nu_cocycle: {in G &, forall x y, nu (x * y)%g = nu x ^@ y + nu y}%R.
  move=> x y Gx Gy; apply: val_inj; rewrite fmvalA fmvalJ ?nHG //.
  rewrite !val_nu ?groupM // /divgr conjgE !mulgA mulgK.
  by rewrite !(invMg, remgrM cpHL) ?groupV ?mulgA.
have nuL: forall x, x \in L -> nu x = 0%R.
  move=> x Lx; apply: val_inj; rewrite val_nu ?sLG //.
  by rewrite /divgr remgr_id ?groupV ?mulgV.
exists (fmval ((\sum_(X \in rcosets Q K) nu (repr X)) *+ m)).
  exact: fmodP.
apply/eqP; rewrite eq_sym eqEcard; apply/andP; split; last first.
  by rewrite cardJg -(leq_pmul2l (cardG_gt0 H)) -!TI_cardMg // eqHL eqHK.
apply/subsetP=> x_nu; case/imsetP=> x Kx ->{x_nu}.
rewrite conjgE mulgA (conjgC _ x).
have Gx: x \in G by rewrite sKG.
rewrite conjVg -mulgA -fmvalJ ?nHG // -fmvalN -fmvalA (_ : _ + _ = nu x)%R.
  by rewrite val_nu // mulKVg groupV mem_remgr // eqHL groupV.
rewrite actZr !oppr_muln -mulrn_addl actr_sum.
rewrite addrC (reindex_acts _ (actsRs_rcosets _ K) Kx) -sumr_sub /= -/Q.
rewrite (eq_bigr (fun _ => nu x)) => [|Qy]; last first.
  case/imsetP=> y Ky ->{Qy}; rewrite !rcosetE -rcosetM QeqLP.
  case: (repr_rcosetP (L :&: P) _) => z; case/setIP=> Lz _.
  case: (repr_rcosetP (L :&: P) _) => t; case/setIP=> Lt _.
  rewrite !nu_cocycle ?groupM ?(sKG y) // ?sLG //.
  by rewrite (nuL z) ?(nuL t) // !act0r !add0r addrC addKr.
apply: val_inj; rewrite sumr_const !fmvalZ.
rewrite -{2}(expgnK coHiPG (fmodP (nu x))); congr (_ ^+ _ ^+ _).
rewrite -[#|_|]divgS ?subsetIl // -(divn_pmul2l (cardG_gt0 H)).
rewrite -!TI_cardMg //; last by rewrite setIA setIAC (setIidPl sHP).
by rewrite group_modl // eqHK (setIidPr sPG) divgS.
Qed.

End Gaschutz.

(* This is the TI part of B & G, Proposition 1.6(d).                          *)
(* We go with B & G rather than Aschbacher and will derive 1.6(e) from (d),   *)
(* rather than the converse, because the derivation of 24.6 from 24.3 in      *)
(* Aschbacher requires a separate reduction to p-groups to yield 1.6(d),      *)
(* making it altogether longer than the direct Gaschutz-style proof.          *)
(* This Lemma is used in maximal.v for the proof of Aschbacher 24.7.          *)
Lemma coprime_abel_cent_TI : forall (gT : finGroupType) (A G : {group gT}),
  A \subset 'N(G) -> coprime #|G| #|A| -> abelian G -> 'C_[~: G, A](A) = 1.
Proof.
move=> gT A G nGA coGA abG; pose f x := val (\sum_(a \in A) fmod abG x ^@ a)%R.
have fM: {in G &, {morph f : x y / x * y}}.
  move=> x y Gx Gy /=; rewrite -fmvalA -big_split /=; congr (fmval _).
  by apply: eq_bigr => a Aa; rewrite fmodM // actAr.
have nfA: forall x a, a \in A -> f (x ^ a) = f x.
  move=> x a Aa; rewrite {2}/f (reindex_inj (mulgI a)) /=; congr (fmval _).
  apply: eq_big => [b | b Ab]; first by rewrite groupMl.
  by rewrite -!fmodJ ?groupM ?(subsetP nGA) // conjgM.
have kerR: [~: G, A] \subset 'ker (Morphism fM).
  rewrite gen_subG; apply/subsetP=> xa; case/imset2P=> x a Gx Aa -> {xa}.
  have Gxa: x ^ a \in G by rewrite memJ_norm ?(subsetP nGA).
  rewrite commgEl; apply/kerP; rewrite (groupM, morphM) ?(groupV, morphV) //=.
  by rewrite nfA ?mulVg.
apply/trivgP; apply/subsetP=> x; case/setIP=> Rx cAx; apply/set1P.
have Gx: x \in G by apply: subsetP Rx; rewrite commg_subl.
rewrite -(expgnK coGA Gx) (_ : x ^+ _ = 1) ?exp1gn //.
rewrite -(fmodK abG Gx) -fmvalZ -(mker (subsetP kerR x Rx)); congr fmval.
rewrite -GRing.sumr_const; apply: eq_bigr => a Aa.
by rewrite -fmodJ ?(subsetP nGA) // /conjg (centP cAx) // mulKg.
Qed.

Section Transfer.

Variables (gT aT : finGroupType) (G H : {group gT}).
Variable alpha : {morphism H >-> aT}.

Hypotheses (sHG : H \subset G) (abelA : abelian (alpha @* H)).

Lemma transfer_morph_subproof : H \subset alpha @*^-1 (alpha @* H).
Proof. by rewrite -sub_morphim_pre. Qed.

Let fmalpha := restrm transfer_morph_subproof (fmod abelA \o alpha).

Let V X g := \sum_(Hx \in rcosets H G) fmalpha (X Hx * g * (X (Hx :* g))^-1).

Definition transfer g := V repr g.

(* Aschbacher 37.2 *)
Lemma transferM : {in G &, {morph transfer : x y / (x * y)%g >-> x + y}}.
Proof.
move=> s t Gs Gt /=.
rewrite [transfer t](reindex_acts 'Rs _ Gs) ?actsRs_rcosets //= -big_split /=.
apply: eq_bigr => C; case/rcosetsP=> x Gx ->{C}; rewrite !rcosetE -!rcosetM.
rewrite -zmodMgE -morphM -?mem_rcoset; first by rewrite !mulgA mulgKV rcosetM.
  by rewrite rcoset_repr rcosetM mem_rcoset mulgK mem_repr_rcoset.
by rewrite rcoset_repr (rcosetM _ _ t) mem_rcoset mulgK mem_repr_rcoset.
Qed.

Canonical Structure transfer_morphism := Morphism transferM.

Definition coset_transversal X := 
  {in rcosets H G, forall Hx : {set gT}, X Hx \in Hx}.

(* Aschbacher 37.1 *)
Lemma transfer_indep : forall X, coset_transversal X -> {in G, transfer =1 V X}.
Proof.
move=> X repsX g Gg.
apply: (@addrI _ (\sum_(Hx \in rcosets H G) fmalpha (repr Hx * (X Hx)^-1))).
rewrite {1}(reindex_acts 'Rs _ Gg) ?actsRs_rcosets // -!big_split /=.
apply: eq_bigr => Hx; case/rcosetsP=> x Gx ->{Hx}; rewrite !rcosetE -!rcosetM.
case: repr_rcosetP => h1 Hh1; case: repr_rcosetP => h2 Hh2.
have: H :* (x * g) \in rcosets H G by rewrite -rcosetE mem_imset ?groupM.
have: H :* x \in rcosets H G by rewrite -rcosetE mem_imset.
move/repsX; case/rcosetP=> h3 Hh3 ->; move/repsX; case/rcosetP=> h4 Hh4 ->.
rewrite -!(mulgA h1) -!(mulgA h2) -!(mulgA h3) !(mulKVg, invMg).
by rewrite addrC -!zmodMgE -!morphM ?groupM ?groupV // -!mulgA !mulKg.
Qed.

Section FactorTransfer.

Variable g : gT.
Hypothesis Gg : g \in G.

Let Gcycg : <[g]> \subset G. Proof. by rewrite cycle_subG. Qed.
Let H_g_rcosets x := rcosets (H :* x) <[g]>.
Let n_ x := #|H_g_rcosets x|.

Lemma mulg_exp_card_rcosets : forall x, x * (g ^+ n_ x) \in H :* x.
Proof.
move=> x; rewrite /n_ /H_g_rcosets -orbitRs -pcycle_actperm ?inE //.
rewrite -{2}(iter_pcycle (actperm 'Rs g) (H :* x)) -permX -morphX ?inE //.
by rewrite actpermE //= rcosetE -rcosetM rcoset_refl. 
Qed.

Definition rcosets_pcycle_transversal (X : {set gT}) :=
  [/\ {in X &, injective H_g_rcosets}, X \subset G & G \subset H * X * <[ g ]>].

CoInductive rcosets_pcycle_transversal_witness : Prop :=
   RcosetPcycleTransversalWitness X (n_ := n_) of rcosets_pcycle_transversal X.

Lemma rcosets_pcycle_transversal_exists : rcosets_pcycle_transversal_witness.
Proof.
pose r1 x := repr (H_g_rcosets x); pose r2 x := repr (r1 x).
have mem_r1: forall x, x \in G -> r1 x \in H_g_rcosets x.
  by move=> x Gx; apply: (mem_repr (H :* x)); apply: orbit_refl.
have id_r2: forall x, x \in G -> H_g_rcosets (r2 x) = H_g_rcosets x.
  move=> x Gx; apply: orbit_transl; rewrite /r2.
  case/rcosetsP: (mem_r1 x Gx) => gi Ggi ->.
  by rewrite -rcosetM rcoset_repr rcosetM -rcosetE mem_orbit. 
exists (r2 @: G); split=> [w z||].
- case/imsetP=> x Gx ->{w}; case/imsetP=> y Gy ->{z}.
  by rewrite !id_r2 /r2 /r1 // => ->.
- apply/subsetP=> u; case/imsetP=> x Gx ->{u}.
  rewrite /r2; case/rcosetsP: (mem_r1 x Gx) => y; case/cycleP=> i ->{y} ->.
  rewrite -rcosetM; apply: subsetP (mem_repr_rcoset H _).
  by rewrite mul_subG // sub1set groupM ?groupX.
apply/subsetP=> x Gx; case/rcosetsP: (mem_r1 x Gx) => y gy def_r1x.
rewrite -[x](mulgK y) mem_mulg ?groupV // -sub1set -mulGS.
by rewrite -rcoset_repr mulgS // sub1set rcosetM -def_r1x -/(r2 x) mem_imset.
Qed.

Variable X : {set gT}.
Hypothesis trX : rcosets_pcycle_transversal X.

Lemma im_rcosets_pcycle_transversal :
  H_g_rcosets @: X = orbit 'Rs <[g]> @: rcosets H G.
Proof.
have [_ sXG sGHXg]:= trX.
apply/setP=> Hxg; apply/imsetP/imsetP=> [[x Xx ->{Hxg}]|[Hx]] /=.
  by exists (H :* x); rewrite // -rcosetE mem_imset ?(subsetP sXG).
case/rcosetsP=> hxgi; move/(subsetP sGHXg); case/mulsgP=> hx gi.
case/mulsgP=> h x Hh Xx -> g_gi -> -> -> {hx hxgi Hxg Hx}; exists x => //.
by apply: orbit_transl; rewrite !rcosetM rcoset_id // -rcosetE mem_orbit.
Qed.
Local Notation imHg_eq := im_rcosets_pcycle_transversal.

Lemma sum_card_rcosets_pcycles : (\sum_(x \in X) n_ x)%N = #|G : H|.
Proof.
have [injHg _ _]:= trX.
transitivity (\sum_(Hxg \in orbit 'Rs <[g]> @: rcosets H G) #|Hxg|)%N. 
  by rewrite -imHg_eq big_imset.
exact: (acts_sum_card_orbit (subset_trans Gcycg (actsRs_rcosets _ _))).
Qed.

Lemma transfer_pcycle_def :
  transfer g = \sum_(x \in X) fmalpha ((g ^+ n_ x) ^ x^-1).
Proof.
have [injHg sXG sGHXg] := trX.
pose repset := \bigcup_(x \in X) [set x * g ^+ (i : 'I__) | i <- 'I_(n_ x)].
pose transX Hy := repr (Hy :&: repset).
pose pcyc x := pcycle (actperm 'Rs g) (H :* x).
pose traj x := traject (actperm 'Rs g) (H :* x) #|pcyc x|.
have Hgr_eq : forall x, H_g_rcosets x = pcyc x.
  by move=> x; rewrite /H_g_rcosets -orbitRs -pcycle_actperm ?inE.
have pcyc_eq : forall x, pcyc x =i traj x by move=> x; apply: pcycle_traject.
have uniq_traj : forall x, uniq (traj x)
  by move=> x; apply: uniq_traject_pcycle.
have n_eq: forall x, n_ x = #|pcyc x| by move=> x; rewrite /n_ Hgr_eq.
have size_traj : forall x, size (traj x) = n_ x 
  by move=> x; rewrite n_eq size_traject.
have nth_traj : forall x j, 
  j < n_ x -> nth (H :* x) (traj x) j = H :* (x * g ^+ j). 
- move=> x j lt_j_x; rewrite nth_traject -?n_eq //.
  by rewrite  -permX -morphX ?inE // actpermE //= rcosetE rcosetM.
have transX_mem : forall y, y \in G -> transX (H :* y) \in H :* y :&: repset.
  move=> y Gy; case/mulsgP: (subsetP sGHXg _ Gy)=> t g0.
  case/mulsgP=> h x Hh Xx ->{t} cycGg0 ->; rewrite -mulgA rcosetM rcoset_id //.
  pose j := index (H :* (x * g0)) (traj x).
  have lt_j_x: j < n_ x.
    by rewrite -size_traj index_mem rcosetM -rcosetE -pcyc_eq -Hgr_eq mem_imset.
  apply: (subsetP _ _ (mem_repr (x * g ^+ j) _)); first by [].
  rewrite inE rcoset_sym -nth_traj // nth_index ?rcoset_refl //=; last first.
    by rewrite -pcyc_eq -Hgr_eq rcosetM -rcosetE mem_imset.
  by apply/bigcupP; exists x => //; apply/imsetP; exists (Ordinal lt_j_x).
have coset_transversal_transX : coset_transversal transX.
  move=> Hy HG_Hy /=; have [y Gy ->] := rcosetsP HG_Hy.
  exact: (subsetP (subsetIl _ _) _ (transX_mem _ _)).
have transXE : forall x i, 
    x \in X -> i < n_ x -> transX (H :* x :* g ^+ i) = x * g ^+ i.
- move=> x i Xx lt_i_x; rewrite -rcosetM.
  have Gxgi : x * g ^+ i \in G by rewrite groupM ?(subsetP sXG x) // ?groupX. 
  case/setIP: (transX_mem _ Gxgi) => Hxgi_transX {Gxgi}.
  case/bigcupP=> x' Xx'; case/imsetP=> j Ij transX_eq; rewrite transX_eq.
  have xx' : x = x'.
    apply: injHg => //; apply: orbit_transl; apply/orbitP. 
    exists (g ^+ j * g ^- i) => /=.
      by rewrite ?groupM ?groupV ?groupX //= ?cycle_id //.
    rewrite rcosetE -rcosetM mulgA rcosetM -transX_eq.
    by rewrite (rcoset_transl Hxgi_transX) -rcosetM mulgK.
  have lt_j_x : j < n_ x by rewrite xx'.
  rewrite xx'; congr (_ * _ ^+ _).
  apply/eqP; rewrite -(@nth_uniq _ (H :* x) (traj x)) ?size_traj //.
  apply/eqP; rewrite !nth_traj // -?size_traj //.
  by apply: rcoset_transl; rewrite {1}xx' -transX_eq.
rewrite (transfer_indep coset_transversal_transX Gg) /V.
rewrite (partition_big_imset (orbit 'Rs <[g]>)) /=.
rewrite -imHg_eq big_imset //=; apply eq_bigr=> x Xx.
rewrite (eq_bigl (mem (H_g_rcosets x))) //=; last first.
  move=> Hx; rewrite /H_g_rcosets orbit_eq_mem //=.
  apply/andP/idP; [case=> // | split=> //].
  apply: subsetP H0; apply/subsetP=> Hz; case/orbitP=> g0 cycgg0 <-.
  rewrite //= rcosetE -rcosetM -rcosetE mem_imset //.
  by rewrite groupM ?(subsetP sXG x) ?(subsetP Gcycg g0).
rewrite Hgr_eq (eq_bigl _ _ (pcyc_eq x)) -big_uniq // /traj /n_ Hgr_eq /=.
case def_n: {-}(#|_|) => [|n].
  by rewrite (cardD1 (H :* x)) pcycle_id in def_n.
rewrite conjgE invgK -{1}[H :* x]rcoset1 -{1}(expg0 g).
rewrite def_n; elim: {1 3}n 0%N (addn0 n) => [|m IHm] i def_i /=.
  rewrite big_cons big_nil addr0 {i}[i]def_i transXE // ?n_eq ?def_n //.
  rewrite  -(mulgA _ _ g) -rcosetM -expgSr -[(H :* x) :* _]rcosetE. 
  rewrite -actpermE morphX ?inE // permX // -def_n iter_pcycle mulgA.
  by rewrite -[H :* x]rcoset1 (transXE _ 0%N) ?mulg1 // n_eq def_n.
rewrite big_cons transXE //; last by rewrite n_eq def_n -def_i ltnS leq_addl. 
rewrite permE /= rcosetE -rcosetM -(mulgA _ _ g) -expgSr.
rewrite addSnnS in def_i; rewrite transXE //; last first.
  by rewrite n_eq def_n -def_i ltnS leq_addl.
by rewrite mulgV [fmalpha 1]morph1 add0r IHm.
Qed.

End FactorTransfer.

End Transfer.
