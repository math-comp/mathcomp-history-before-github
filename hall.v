Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import choice fintype finfun bigops ssralg finset prime.
Require Import groups morphisms automorphism normal perm action gprod.
Require Import commutators cyclic center pgroups sylow nilpotent maximal.

(****************************************************************************)
(*  Hall's generalization of Sylow's theorems to solvable groups, along     *)
(* with the splitting theorems (Gaschutz' and Schur-Zassenhaus) that lead   *)
(* up to them, and the special case of Maeshke's theorem for elementary     *)
(* abelian p-subgroups.                                                     *)
(*   We define at this point the Z[N(A)]-module associated with a finite    *)
(* abelian group A, given (abelA : abelian A) :                             *)
(*   fmod_of abelA : the type of elements of the module (== subg_of A)      *)
(*    fmod abelA x : the injection of x \in A into fmod_of abelA            *)
(*         fmval u : the projection of u : fmod_of abelA onto A             *)
(*          u ^@ x : the action of x \in 'N(A) on u : fmod_of abelA         *)
(* These definitions are packed into a FiniteModule submodule, as they will *)
(* only be reused for the definition of the transfer morphism.              *)
(****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.

Module FiniteModule.

Reserved Notation "u ^@ x" (at level 31, left associativity).

Section OneFinMod.

Variables (gT : finGroupType) (A : {group gT}) (abelA : abelian A).
Implicit Types x y z : gT.

Definition fmod_of of abelian A := subg_of A.
Bind Scope ring_scope with fmod_of.
Open Scope ring_scope.

Local Notation fmodA := (fmod_of abelA).
Implicit Types u v w : fmodA.

Definition fmval u := sgval (idfun u).
Definition fmod x : fmodA := subg A x.
Definition actr u x := if x \in 'N(A) then fmod (fmval u ^ x) else u.
Notation "u ^@ x" := (actr u x) : ring_scope.

Canonical Structure fmod_subType := [subType for fmval].
Local Notation valA := (@val _ _ fmod_subType) (only parsing).
Canonical Structure fmod_eqType := [eqType of fmodA].
Canonical Structure fmod_choiceType := [choiceType of fmodA].
Canonical Structure fmod_countType := [countType of fmodA].
Canonical Structure fmod_finType := [finType of fmodA].
Canonical Structure fmod_subCountType := [subCountType of fmodA].
Canonical Structure fmod_subFinType := [subFinType of fmodA].
Canonical Structure fmod_baseFinGroupType := [baseFinGroupType of fmodA].
Canonical Structure fmod_finGroupType := [finGroupType of fmodA].
Canonical Structure fmval_morphism := [morphism of fmval].
Canonical Structure fmod_morphism := [morphism of fmod].

Lemma fmod_mulgC : @commutative fmodA fmodA (@mulg _).
Proof. move=> x y; apply: val_inj; apply: (centsP abelA); exact: subgP. Qed.

Definition fmod_zmodMixin := 
  @ZmodMixin fmodA _ _ _ (@mulgA _) fmod_mulgC (@mul1g _) (@mulVg _).
Canonical Structure fmod_zmodType := ZmodType fmod_zmodMixin.

Lemma fmodP : forall u, valA u \in A. Proof. exact: valP. Qed.
Lemma fmod_inj : injective fmval. Proof. exact: val_inj. Qed.
Lemma congr_fmod : forall u v, u = v -> fmval u = fmval v.
Proof. exact: congr1. Qed.

Lemma fmvalA : {morph valA : x y / x + y >-> (x * y)%g}. Proof. by []. Qed.
Lemma fmvalN : {morph valA : x / - x >-> x^-1%g}. Proof. by []. Qed.
Lemma fmval0 : valA 0 = 1%g. Proof. by []. Qed.
Lemma fmvalZ : forall n, {morph valA : x / x *+ n >-> (x ^+ n)%g}.
Proof. by case=> // n x /=; elim: n => //= n IHn; congr (_ * _)%g. Qed.

Lemma fmodKcond : forall x, val (fmod x) = if x \in A then x else 1%g.
Proof. move=> x; case: ifP => Ax; [exact: subgK | exact: subg_default]. Qed.
Lemma fmodK : {in A, cancel fmod val}. Proof. exact: subgK. Qed.
Lemma fmvalK : cancel val fmod. Proof. exact: sgvalK. Qed.
Lemma fmod1 : fmod 1 = 0. Proof. by rewrite -fmval0 fmvalK. Qed.
Lemma fmodM : {in A &, {morph fmod : x y / (x * y)%g >-> x + y}}.
Proof. exact: subgM. Qed.
Lemma fmodX : forall n, {in A, {morph fmod : x / (x ^+ n)%g >-> x *+ n}}.
Proof.
by elim=> [|n IHn] x Ax; rewrite ?fmod1 // expgS mulrS fmodM ?groupX ?IHn.
Qed.
Lemma fmodV : {morph fmod : x / x^-1%g >-> - x}.
Proof.
move=> x; apply: val_inj; rewrite fmvalN !fmodKcond groupV.
by case: (x \in A); rewrite ?invg1.
Qed.

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

Lemma act0r : forall x, 0 ^@ x = 0.
Proof. by move=> x; rewrite /actr conj1g fmod1 if_same. Qed.

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

Lemma actr1 : forall u, u ^@ 1 = u.
Proof. by move=> u; apply: val_inj; rewrite fmvalJ ?group1 ?conjg1. Qed.

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

End FiniteModule.

Section Gaschutz.

Variables (gT : finGroupType) (G H P : {group gT}).
Implicit Types K L : {group gT}.

Hypotheses (nsHG : H <| G) (sHP : H \subset P) (sPG : P \subset G).
Hypotheses (abelH : abelian H) (coHiPG : coprime #|H| #|G : P|).

Let sHG := normal_sub nsHG.
Let nHG := subsetP (normal_norm nsHG).

Let m := (expgn_inv H #|G : P|).

Import FiniteModule.
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
  move=> x y Gx Gy; rewrite /= subgK ?mulKVg // -mem_lcoset lcoset_sym.
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
exists (val ((\sum_(X \in rcosets Q K) nu (repr X)) *+ m)%R).
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

(* This should be sufficient for B&G 1.20 *)
Theorem Maeshke_abelem : forall (gT : finGroupType) (G V U : {group gT}) p,
  p.-abelem V -> p^'.-group G -> U \subset V ->
    G \subset 'N(V) -> G \subset 'N(U) ->
  exists2 W : {group gT}, U \x W = V & G \subset 'N(W).
Proof.
move=> gT G V U p pV p'G sUV nVG nUG.
wlog pr_p: / prime p.
  case: (pgroup_1Vpr (abelem_pgroup pV)) => [V1 _ | [pr_p _ _]]; auto.
  exists 1%G; last by rewrite norms1.
  by rewrite dprodg1 V1; apply/trivgP; rewrite -V1.
have splitU: [splits V, over U] := abelem_splits pV sUV.
case/andP: pV; case/andP=> abV _ pV; have cUV := subset_trans sUV abV.
have sVVG := mulgen_subl V G.
have{nUG} nUVG: U <| V <*> G.
  by rewrite /(U <| _) mulgen_subG (subset_trans sUV) // cents_norm // centsC.
rewrite -{nUVG}(Gaschutz_split nUVG) ?(abelianS sUV) // in splitU; last first.
  rewrite -divgS ?mulgen_subl //= norm_mulgenEr //.
  have coVG: coprime #|V| #|G| := pnat_coprime pV p'G.
  by rewrite coprime_cardMg // mulnC mulnK // (coprimeSg sUV).
case/splitsP: splitU => WG; case/complP=> trUWG /= defVG.
exists (WG :&: V)%G.
  rewrite dprodE; last by rewrite setIA trUWG (setIidPl _) ?sub1G.
    by rewrite group_modl // defVG (setIidPr _).
  by rewrite (subset_trans cUV) ?centS ?subsetIr.
rewrite (subset_trans (mulgen_subr V _)) // -defVG mul_subG //.
   by rewrite cents_norm ?(subset_trans cUV) ?centS ?subsetIr.
rewrite normsI ?normG // (subset_trans (mulG_subr U _)) //.
by rewrite defVG mulgen_subG normG.
Qed.

Theorem SchurZass_split : forall (gT : finGroupType) (G H : {group gT}),
  Hall G H -> H <| G -> [splits G, over H].
Proof.
move=> gT G; move: {2}_.+1 (ltnSn #|G|) => n.
elim: n gT G => // n IHn gT G; rewrite ltnS => Gn H hallH nsHG.
have [sHG nHG] := andP nsHG.
case: (trivgVpdiv H) => [H1 | [p pr_p pH]].
  by apply/splitsP; exists G; rewrite inE H1 -subG1 subsetIl mul1g eqxx.
have [P sylP] := Sylow_exists p H.
case nPG: (P <| G); last first.
  pose N := ('N_G(P))%G.
  have sNG: N \subset G by rewrite subsetIl.
  have eqHN_G: H * N = G by exact: Frattini_arg sylP.
  pose H' := (H :&: N)%G.
  have nH'N: H' <| N.
    by rewrite /normal subsetIr normsI ?normG ?(subset_trans sNG).
  have eq_iH: #|G : H| = #|N| %/ #|H'|.
    rewrite -divgS // -(divn_pmul2l (cardG_gt0 H')) mulnC -eqHN_G.
    by rewrite -mul_cardG (mulnC #|H'|) divn_pmul2l // cardG_gt0.
  have hallH': Hall N H'.
    rewrite /Hall -divgS subsetIr //= -eq_iH.
    by case/andP: hallH => _; apply: coprimeSg; exact: subsetIl.
  have: [splits N, over H'].
    apply: IHn hallH' nH'N; apply: {n}leq_trans Gn.
    rewrite proper_card // properEneq sNG andbT; apply/eqP=> eqNG.
    by rewrite -eqNG normal_subnorm (subset_trans (pHall_sub sylP)) in nPG.
  case/splitsP=> K; case/complP=> trKN eqH'K.
  have sKN: K \subset N by rewrite -(mul1g K) -eqH'K mulSg ?sub1set.
  apply/splitsP; exists K; rewrite inE -subG1; apply/andP; split.
    by rewrite /= -(setIidPr sKN) setIA trKN.
  by rewrite eqEsubset -eqHN_G mulgS // -eqH'K mulGS mulSg ?subsetIl.
pose Z := 'Z(P); pose Gbar := G / Z; pose Hbar := H / Z.
have sZP: Z \subset P by exact: center_sub.
have sZH: Z \subset H by exact: subset_trans (pHall_sub sylP).
have sZG: Z \subset G by exact: subset_trans sHG.
have nZG: Z <| G by apply: char_normal_trans nPG; exact: center_char.
have nZH: Z <| H by exact: normalS nZG.
have nHGbar: Hbar <| Gbar by exact: morphim_normal.
have hallHbar: Hall Gbar Hbar by apply: morphim_Hall (normal_norm _) _.
have: [splits Gbar, over Hbar].
  apply: IHn => //; apply: {n}leq_trans Gn; rewrite ltn_quotient //.
  apply/eqP; move/(trivg_center_pgroup (pHall_pgroup sylP)); move/eqP.
  rewrite trivg_card1 (card_Hall sylP) p_part -(expn0 p).
  by rewrite eqn_exp2l ?prime_gt1 // lognE pH pr_p cardG_gt0.
case/splitsP=> Kbar; case/complP=> trHKbar eqHKbar.
have: Kbar \subset Gbar by rewrite -eqHKbar mulG_subr.
case/inv_quotientS=> //= ZK quoZK sZZK sZKG.
have nZZK: Z <| ZK by exact: normalS nZG.
have cardZK: #|ZK| = (#|Z| * #|G : H|)%N.
  rewrite -(LaGrange sZZK); congr (_ * _)%N.
  rewrite -card_quotient -?quoZK; last by case/andP: nZZK.
  rewrite -(divgS sHG) -(LaGrange sZG) -(LaGrange sZH) divn_pmul2l //.
  rewrite -!card_quotient ?normal_norm //= -/Gbar -/Hbar.
  by rewrite -eqHKbar (TI_cardMg trHKbar) mulKn.
have: [splits ZK, over Z].
  rewrite (Gaschutz_split nZZK _ sZZK) ?abelian_center //; last first.
    rewrite -divgS // cardZK mulKn ?cardG_gt0 //.
    by case/andP: hallH => _; exact: coprimeSg. 
  by apply/splitsP; exists 1%G; rewrite inE -subG1 subsetIr mulg1 eqxx.
case/splitsP=> K; case/complP=> trZK eqZK.
have sKZK: K \subset ZK by rewrite -(mul1g K) -eqZK mulSg ?sub1G.
have trHK: H :&: K = 1.
  apply/trivgP; rewrite /= -(setIidPr sKZK) setIA -trZK setSI //.
  rewrite -quotient_sub1; last by rewrite subIset 1?normal_norm.
  by rewrite /= quotientGI //= -quoZK trHKbar.
apply/splitsP; exists K; rewrite inE trHK ?eqEcard subxx leqnn /=.
rewrite mul_subG ?(subset_trans sKZK) //= TI_cardMg //.
rewrite -(@mulKn #|K| #|Z|) ?cardG_gt0 // -TI_cardMg // eqZK.
by rewrite cardZK mulKn ?cardG_gt0 // LaGrange.
Qed.

Theorem SchurZass_trans_sol : forall (gT : finGroupType) (H K K1 : {group gT}),
    solvable H -> K \subset 'N(H) -> K1 \subset H * K ->
    coprime #|H| #|K| -> #|K1| = #|K| ->
  exists2 x, x \in H & K1 :=: K :^ x.
Proof.
move=> gT H; move: {2}_.+1 (ltnSn #|H|) => n; elim: n => // n IHn in gT H *.
rewrite ltnS => leHn K K1 solH nHK; case: (eqsVneq H 1) => [H1 |].
  rewrite H1 mul1g => sK1K _ eqK1K.
  exists 1; first exact: set11.
  by apply/eqP; rewrite conjsg1 eqEcard sK1K eqK1K /=.
pose G := (H <*> K)%G.
have defG: G :=: H * K by rewrite -normC // -norm_mulgenEl // mulgenC.
have sHG: H \subset G by exact: mulgen_subl.
have sKG: K \subset G by exact: mulgen_subr.
have nHG: H <| G by rewrite /(H <| G) sHG mulgen_subG normG.
case/(solvable_norm_abelem solH nHG)=> M [sMH nMG ntM].
case/andP=> abelM _; rewrite -defG => sK1G coHK oK1K.
have nMsG: forall L : {set gT}, L \subset G -> L \subset 'N(M).
  by move=> L sLG; exact: subset_trans (normal_norm nMG).
have [coKM coHMK]: coprime #|M| #|K| /\ coprime #|H / M| #|K|.
  by apply/andP; rewrite -coprime_mull card_quotient ?nMsG ?LaGrange.
have oKM: forall K' : {group gT},
  K' \subset G -> #|K'| = #|K| -> #|K' / M| = #|K|.
- move=> K' sK'G oK'.
  rewrite -quotient_mulg -?norm_mulgenEl ?card_quotient ?nMsG //; last first.
    by rewrite gen_subG subUset sK'G; case/andP: nMG.
  rewrite -divgS /=; last by rewrite -gen_subG genS ?subsetUr.
  by rewrite norm_mulgenEl ?nMsG // coprime_cardMg ?mulnK // oK' coprime_sym.
have [xb]: exists2 xb, xb \in H / M & K1 / M = (K / M) :^ xb.
  apply: IHn; try by rewrite (quotient_sol, morphim_norms, oKM K) ?(oKM K1).
    by apply: leq_trans leHn; rewrite ltn_quotient.
  by rewrite -morphimMl ?nMsG // -defG morphimS.
case/morphimP=> x nMx Hx ->{xb} eqK1Kx; pose K2 := (K :^ x)%G.
have{eqK1Kx} eqK12: K1 / M = K2 / M by rewrite quotientJ.
suff [y My ->]: exists2 y, y \in M & K1 :=: K2 :^ y.
  by exists (x * y); [rewrite groupMl // (subsetP sMH) | rewrite conjsgM].
have nMK1: K1 \subset 'N(M) by case/andP: nMG => _; exact: subset_trans.
have defMK: M * K1 = M <*> K1 by rewrite -normC // -norm_mulgenEl // mulgenC.
have sMKM: M \subset M <*> K1 by rewrite -defMK mulG_subl.
have nMKM: M <| M <*> K1 by rewrite /(_ <| _) sMKM gen_subG subUset normG.
have trMK1: M :&: K1 = 1 by rewrite coprime_TIg ?oK1K.
have trMK2: M :&: K2 = 1 by rewrite coprime_TIg ?cardJg ?oK1K.
apply: (Gaschutz_transitive nMKM _ sMKM) => //=; last 2 first.
- by rewrite inE trMK1 defMK !eqxx.
- by rewrite -!(setIC M) trMK1.
- by rewrite -divgS //= -defMK coprime_cardMg oK1K // mulKn.
rewrite inE trMK2 eqxx eq_sym eqEcard /= -defMK andbC.
by rewrite !coprime_cardMg ?cardJg ?oK1K ?leqnn //= mulGS -quotientSK -?eqK12.
Qed.

Lemma SchurZassenhaus_trans_actsol :
    forall (gT : finGroupType) (G A B : {group gT}),
    solvable A -> A \subset 'N(G) -> B \subset A <*> G ->
    coprime #|G| #|A| -> #|A| = #|B| ->
  exists2 x, x \in G & B :=: A :^ x.
Proof.
move=> gT G A B; set AG := A <*> G; move: {2}_.+1 (ltnSn #|AG|) => n.
elim: n => // n IHn in gT A B G AG *.
rewrite ltnS => leAn solA nGA sB_AG coGA oAB.
case: (eqsVneq A 1) => [A1 | ntA].
  by exists 1; rewrite // conjsg1 A1 (@card1_trivg _ B) // -oAB A1 cards1.
have [M [sMA nsMA ntM]] := solvable_norm_abelem solA (normal_refl A) ntA.
case/abelemP=> q q_pr; move/abelem_pgroup=> qM; have nMA := normal_norm nsMA.
have defAG: AG = A * G := norm_mulgenEl nGA.
have sA_AG: A \subset AG := mulgen_subl _ _.
have sG_AG: G \subset AG := mulgen_subr _ _.
have sM_AG := subset_trans sMA sA_AG.
have oAG: #|AG| = (#|A| * #|G|)%N by rewrite defAG coprime_cardMg 1?coprime_sym.
have q'G: #|G|`_q = 1%N.
  rewrite part_p'nat ?p'natE -?prime_coprime // coprime_sym.
  case: (pgroup_1Vpr qM) ntM => [-> | [_ _ [k oM]] _]; first by case/eqP.
  by rewrite -(@coprime_pexpr k.+1) // -oM (coprimegS sMA).
have coBG: coprime #|B| #|G| by rewrite -oAB coprime_sym.
have defBG: B * G = AG.
  by apply/eqP; rewrite eqEcard mul_subG ?sG_AG //= oAG oAB coprime_cardMg.
case nMG: (G \subset 'N(M)).
  have nsM_AG: M <| AG by rewrite /normal sM_AG mulgen_subG nMA.
  have nMB: B \subset 'N(M) := subset_trans sB_AG (normal_norm nsM_AG).
  have sMB: M \subset B.
    have [Q sylQ]:= Sylow_exists q B; have sQB := pHall_sub sylQ.
    apply: subset_trans (normal_sub_max_pgroup (Hall_max _) qM nsM_AG) (sQB).
    rewrite pHallE (subset_trans sQB) //= oAG partn_mul // q'G muln1 oAB.
    by rewrite (card_Hall sylQ).
  have defAGq: AG / M = (A / M) <*> (G / M).
    by rewrite quotient_gen ?quotientU ?subUset ?nMA.
  have: B / M \subset (A / M) <*> (G / M) by rewrite -defAGq quotientS.
  case/IHn; rewrite ?morphim_sol ?quotient_norms ?coprime_morph //.
  - by rewrite -defAGq (leq_trans _ leAn) ?ltn_quotient.
  - by rewrite !card_quotient // -!divgS // oAB.
  move=> Mx; case/morphimP=> x Nx Gx ->{Mx} //; rewrite -quotientJ //= => defBq.
  exists x => //; apply: quotient_inj defBq; first by rewrite /normal sMB.
  by rewrite -(normsP nMG x Gx) /normal normJ !conjSg.
pose K := M <*> G; pose R := K :&: B; pose N := 'N_G(M).
have defK: K = M * G by rewrite -norm_mulgenEl ?(subset_trans sMA).
have oK: #|K| = (#|M| * #|G|)%N.
  by rewrite defK coprime_cardMg // coprime_sym (coprimegS sMA).
have sylM: q.-Sylow(K) M.
  by rewrite pHallE mulgen_subl /= oK partn_mul // q'G muln1 part_pnat.
have sylR: q.-Sylow(K) R.
  rewrite pHallE subsetIl /= -(card_Hall sylM) -(@eqn_pmul2r #|G|) // -oK.
  rewrite -coprime_cardMg ?(coprimeSg _ coBG) ?subsetIr //=.
  by rewrite group_modr ?mulgen_subr ?(setIidPl _) // defBG mulgen_subG sM_AG.
have [mx] := Sylow_trans sylM sylR.
rewrite /= -/K defK; case/imset2P=> m x Mm Gx ->{mx}.
rewrite conjsgM conjGid {m Mm}// => defR.
have sNG: N \subset G := subsetIl _ _.
have pNG: N \proper G by rewrite /proper sNG subsetI subxx nMG.
have nNA: A \subset 'N(N) by rewrite normsI ?norms_norm.
have: B :^ x^-1 \subset A <*> N.
  rewrite norm_mulgenEl ?group_modl // -defAG subsetI !sub_conjgV -normJ -defR.
  rewrite conjGid ?(subsetP sG_AG) // normsI ?normsG // (subset_trans sB_AG) //.
  by rewrite mulgen_subG normsM // -defK normsG ?mulgen_subr. 
do [case/IHn; rewrite ?cardJg ?(coprimeSg _ coGA) //= -/N] => [|y Ny defB].
  rewrite mulgenC norm_mulgenEr // coprime_cardMg ?(coprimeSg sNG) //.
  by rewrite (leq_trans _ leAn) // oAG mulnC ltn_pmul2l // proper_card.
exists (y * x); first by rewrite groupM // (subsetP sNG).
by rewrite conjsgM -defB conjsgKV.
Qed.

Lemma HallSolvable : forall pi (gT : finGroupType) (G : {group gT}),
  solvable G -> exists2 H : {group gT}, pi.-Hall(G) H
                & forall K : {group gT}, K \subset G -> pi.-group K ->
                  exists2 x, x \in G & K \subset H :^ x.
Proof.
move=> pi gT G; move: {2}_.+1 (ltnSn #|G|) => n.
elim: n gT G => // n IHn gT G; rewrite ltnS => leGn solG.
case: (eqsVneq G 1) => [G1 | ntG].
  exists G => [|K]; rewrite G1; last move/trivGP=> -> {K} _.
    by rewrite pHallE sub1G cards1 part_p'nat.
  by exists 1; rewrite ?set11 ?sub1G.
case: (solvable_norm_abelem solG (normal_refl _)) => // M [sMG nsMG ntM].
case/abelemP=> p pr_p; do 2![case/andP]=> abelM _ pM.
pose Gb := (G / M)%G; case: (IHn _ Gb) => [||Hb]; try exact: quotient_sol.
  by rewrite (leq_trans (ltn_quotient _ _)).
case/and3P=> [sHbGb piHb pi'Hb'] transHb.
case: (inv_quotientS nsMG sHbGb) => H def_H sMH sHG.
have nMG := normal_norm nsMG; have nMH := subset_trans sHG nMG.
have{transHb} transH: forall K : {group gT},
  K \subset G -> pi.-group K -> exists2 x, x \in G & K \subset H :^ x.
- move=> K sKG piK; have nMK := subset_trans sKG nMG.
  case: (transHb (K / M)%G) => [||xb Gxb sKHxb]; first exact: morphimS.
    exact: morphim_pgroup.
  case/morphimP: Gxb => x Nx Gx /= def_x; exists x => //.
  apply/subsetP=> y Ky.
  have: y \in coset M y by rewrite val_coset (subsetP nMK, rcoset_refl).
  have: coset M y \in (H :^ x) / M.
    rewrite /quotient morphimJ //=.
    rewrite def_x def_H in sKHxb; apply: (subsetP sKHxb); exact: mem_quotient.
  case/morphimP=> z Nz Hxz ->.
  rewrite val_coset //; case/rcosetP=> t Mt ->; rewrite groupMl //.
  by rewrite mem_conjg (subsetP sMH) // -mem_conjg (normP Nx).
have{pi'Hb'} pi'H': pi^'.-nat #|G : H|.
  move: pi'Hb'; rewrite -!divgS // def_H !card_quotient //.
  by rewrite -(divn_pmul2l (cardG_gt0 M)) !LaGrange.
case/orP: (orbN (p \in pi)) => pi_p.
  exists H => //; apply/and3P; split=> //; rewrite /pgroup.
  by rewrite -(LaGrange sMH) -card_quotient // pnat_mul -def_H (pi_pnat pM).
case: (ltnP #|H| #|G|) => [ltHG | leGH {n IHn leGn transH}].
  case: (IHn _ H (leq_trans ltHG leGn)) => [|H1]; first exact: solvableS solG.
  case/and3P=> sH1H piH1 pi'H1' transH1.
  have sH1G: H1 \subset G by exact: subset_trans sHG.
  exists H1 => [|K sKG piK].
    apply/and3P; split => //.
    rewrite -divgS // -(LaGrange sHG) -(LaGrange sH1H) -mulnA.
    by rewrite mulKn // pnat_mul pi'H1'.
  case: (transH K sKG piK) => x Gx def_K.
  case: (transH1 (K :^ x^-1)%G) => [||y Hy def_K1].
  - by rewrite sub_conjgV.
  - by rewrite /pgroup cardJg.
  exists (y * x); first by rewrite groupMr // (subsetP sHG).
  by rewrite -(conjsgKV x K) conjsgM conjSg.
have{leGH Gb sHbGb sHG sMH pi'H'} eqHG: H = G.
  by apply/eqP; rewrite -val_eqE eqEcard sHG.
have{H Hb def_H eqHG piHb nMH} hallM: pi^'.-Hall(G) M.
  rewrite /pHall /pgroup sMG pnatNK -card_quotient //=.
  by rewrite -eqHG -def_H (pi_pnat pM).
case/splitsP: (SchurZass_split (pHall_Hall hallM) nsMG) => H.
case/complP=> trMH defG.
have sHG: H \subset G by rewrite -defG mulG_subr.
exists H => [|K sKG piK].
  apply: etrans hallM; rewrite /pHall sMG sHG /= -!divgS // -defG andbC.
  by rewrite (TI_cardMg trMH) mulKn ?mulnK // pnatNK.
pose G1 := (K <*> M)%G; pose K1 := (H :&: G1)%G.
have nMK: K \subset 'N(M) by apply: subset_trans sKG nMG.
have defG1: M * K = G1 by rewrite -normC -?norm_mulgenEl.
have sK1G1: K1 \subset M * K by rewrite defG1 subsetIr.
have coMK: coprime #|M| #|K|.
  by rewrite coprime_sym (pnat_coprime piK) //; exact: (pHall_pgroup hallM).
case: (SchurZass_trans_sol _ nMK sK1G1 coMK) => [||x Mx defK1].
- exact: solvableS solG.
- apply/eqP; rewrite -(eqn_pmul2l (cardG_gt0 M)) -TI_cardMg //; last first.
    by apply/trivgP; rewrite -trMH /= setIA subsetIl.
  rewrite -coprime_cardMg // defG1; apply/eqP; congr #|(_ : {set _})|.
  rewrite group_modl; last by rewrite -defG1 mulG_subl.
  by apply/setIidPr;  rewrite defG gen_subG subUset sKG.
exists x^-1; first by rewrite groupV (subsetP sMG).
by rewrite -(_ : K1 :^ x^-1 = K) ?(conjSg, subsetIl) // defK1 conjsgK.
Qed.

Section HallCorollaries.

Variable gT : finGroupType.

Corollary HallExist : forall pi (G : {group gT}),
  solvable G -> exists H : {group gT}, pi.-Hall(G) H.
Proof. by move=> pi G solG; case: (HallSolvable pi solG) => H; exists H. Qed.

Corollary HallConj : forall pi (G H1 H2 : {group gT}),
  solvable G -> pi.-Hall(G) H1 -> pi.-Hall(G) H2 ->
  exists2 x, x \in G & H1 = (H2 :^ x)%G.
Proof.
move=> pi G H1 H2 solG; case: (HallSolvable pi solG) => H hallH transH.
have conjH: forall K : {group gT},
  pi.-Hall(G) K -> exists2 x, x \in G & K = (H :^ x)%G.
- move=> K hallK; case/and3P: (hallK) => sKG piK _.
  case: (transH K sKG piK) => x Gx sKH; exists x => //.
  apply/eqP; rewrite -val_eqE eqEcard sKH cardJg.
  by rewrite (card_Hall hallH) (card_Hall hallK) /=.
case/conjH=> x1 Gx1 ->{H1}; case/conjH=> x2 Gx2 ->{H2}.
exists (x2^-1 * x1); first by rewrite groupMl ?groupV.
by apply: val_inj; rewrite /= conjsgM conjsgK.
Qed.

Lemma hall_norm_conj : forall pi (G H : {group gT}) x,
  x \in 'N(G) -> pi.-Hall(G) (H :^ x) = pi.-Hall(G) H.
Proof.
by move=> pi G H x Nx; rewrite !pHallE cardJg -{1}(normP Nx) conjSg.
Qed.

Lemma hall_conj : forall pi (G H : {group gT}) x,
  x \in G -> pi.-Hall(G) (H :^ x) = pi.-Hall(G) H.
Proof. by move=> pi G *; rewrite hall_norm_conj ?(subsetP (normG G)). Qed.

Corollary HallSubset : forall pi (G K : {group gT}),
  solvable G -> K \subset G -> pi.-group K ->
    exists2 H : {group gT}, pi.-Hall(G) H & K \subset H.
Proof.
move=> pi G K solG sKG; case: (HallSolvable pi solG) => H hallH transH.
by case/transH=> // x Gx sKHx; exists (H :^ x)%G; rewrite ?hall_conj.
Qed.

Lemma Hall_Frattini_arg : forall pi (G K H : {group gT}),
  solvable K -> K <| G -> pi.-Hall(K) H -> K * 'N_G(H) = G.
Proof.
move=> pi G K H solK; case/andP=> sKG nKG hallH.
have sHG: H \subset G by apply: subset_trans sKG; case/andP: hallH.
rewrite setIC group_modl //; apply/setIidPr; apply/subsetP=> x Gx.
pose H1 := (H :^ x^-1)%G; have hallH1: pi.-Hall(K) H1.
  by rewrite hall_norm_conj // groupV (subsetP nKG).
case: (HallConj solK hallH hallH1) => y Ky defH.
rewrite -(mulKVg y x) mem_mulg //; apply/normP.
by rewrite conjsgM {1}defH conjsgK conjsgKV.
Qed.

Lemma hall_maximal : forall pi (G H K : {group gT}),
  pi.-Hall(G) H -> K \subset G -> pi.-group K -> H \subset K -> K = H.
Proof.
move=> pi G H K hallH sKG piK sHK; apply/eqP.
suff: pi.-Hall(G) K.
  rewrite eq_sym -val_eqE eqEcard sHK /= (card_Hall hallH).
  by move/card_Hall->.
rewrite /pHall sKG piK; case/and3P: hallH => _ _; apply: pnat_dvd.
rewrite -(dvdn_pmul2l (cardG_gt0 K)) LaGrange // -(LaGrange sHK) mulnAC.
by rewrite LaGrange (subset_trans sHK, dvdn_mulr).
Qed.

Lemma HallSubnormal : forall pi (G K H : {group gT}),
  solvable G -> K <| G -> pi.-Hall(G) H -> pi.-Hall(K) (H :&: K).
Proof.
move=> pi G K H solG; case/andP=> sKG nKG hallH.
case: (HallExist pi (solvableS sKG solG)) => H1 hallH1.
have [sH1G piH1]: H1 \subset G /\ pi.-group H1.
  case/and3P: hallH1=> sH1K piH1 _; split=> //; exact: subset_trans sKG.
case: (HallSubset solG sH1G piH1) => H2 hallH2 sH12.
case: (HallConj solG hallH hallH2) => x; move/(subsetP nKG) => Nx ->.
rewrite -{2}(normP Nx) -conjIg hall_norm_conj //.
rewrite (@hall_maximal _ _ _ (H2 :&: K)%G hallH1) //; first exact: subsetIr.
  apply: pgroupS (pHall_pgroup hallH2); exact: subsetIl.
by rewrite subsetI sH12; case/andP: hallH1.
Qed.

End HallCorollaries.




