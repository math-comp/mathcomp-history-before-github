(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat.
Require Import div seq fintype connect.
Require Import groups group_perm tuple finfun finset.

(* Require Import paths ssralg bigops. *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section Action.

Variable (gT : finGroupType) (sT : finType).

Record action : Type := Action {
  act_f :> sT -> gT -> sT;
  _ : forall x, act_f x 1 = x;
  _ : forall a x y, act_f a (x * y) = act_f (act_f a x) y
}.

Variable to : action.

Lemma act1 : forall x, to x 1 = x.
Proof. by case to. Qed.

Lemma actM : forall a x y, to a (x * y) = to (to a x) y.
Proof. by case to. Qed.

Lemma actK : forall x, cancel (to^~ x) (to^~ x^-1).
Proof. by move=> x e; rewrite -actM ?groupV // mulgV act1. Qed.

Lemma actKV : forall x, cancel (to^~ x^-1) (to^~ x).
Proof. move=> x; rewrite -{2}(invgK x); exact:actK. Qed.

Lemma inj_act : forall x, injective (to^~ x).
Proof. move=> x; exact: (can_inj (actK x)). Qed.

Variable G : group gT.
Variable a : sT.

Definition transitive (S : pred sT) := forall b, b \in S -> to b @: G =i S.

Definition orbit := to a @: G.

Lemma orbitP: forall b,
  reflect (exists2 x, x \in G & to a x = b) (b \in orbit).
Proof.
by move=> b; apply: (iffP (@imsetP _ _ _ _ _)); case=> x; exists x.
Qed.

Lemma orbit_to : forall x, x \in G -> to a x \in orbit.
Proof. by move=> x Gx; apply/orbitP; exists x. Qed.

Lemma orbit_refl : a \in orbit.
Proof. rewrite -[a]act1; apply: orbit_to; exact: group1. Qed.

Definition stabilizer := [set x \in G | to a x == a].

Lemma stabilizerP: forall x,
  reflect (x \in G /\ to a x = a) (x \in stabilizer).
Proof.
by move=> x; rewrite inE; apply: (iffP andP) => [] [Gx]; move/eqP.
Qed.

Definition act_fix := stabilizer == G.

Lemma act_fixP : reflect (forall x, x \in G -> to a x = a) act_fix.
Proof.
apply: (iffP eqP).
  by move/setP=> Gs x Gx; move/(_ x): Gs; rewrite Gx; case/stabilizerP.
move=> Ga; apply/setP=> x; move/(_ x): Ga.
by rewrite inE; case: (x \in G) => //= ->; rewrite // eqxx.
Qed.

Lemma orbit1P : reflect ([set a] = orbit) act_fix.
Proof.
apply: (iffP idP).
  move/act_fixP => Hto; apply/setP=> x; rewrite inE.
  apply/eqP/orbitP; last by move=> [z Gz Gtoz]; rewrite -(Hto z Gz).
  by move=> <-; exists (1 : gT); rewrite ?act1.
move/setP=> Horb; apply/act_fixP=> x Gx; move/(_ (to a x)): Horb.
by rewrite inE orbit_to //; move/eqP->.
Qed.

Lemma stab1 : 1 \in stabilizer.
Proof. by apply/stabilizerP; rewrite group1 act1. Qed.

Lemma group_set_stab : group_set stabilizer.
Proof.
apply/group_setP; split; first exact: stab1.
move=> x y; move/stabilizerP => [Hx Htox]; move/stabilizerP => [Hy Htoy].
apply/stabilizerP; split; first by rewrite groupMl.
by rewrite actM // Htox // Htoy.
Qed.

Canonical Structure group_stab := Group group_set_stab.

Lemma subset_stab : stabilizer \subset G.
Proof. by apply/subsetP=> x; case/stabilizerP. Qed.

Lemma to_repr_rcoset : forall z,
  z \in G -> to a (repr (stabilizer :* z)) = to a z.
Proof.
move=> z Gz; case: (repr _) / (repr_rcosetP group_stab z) => y.
by move/stabilizerP=> [Gy Dtoy]; rewrite actM Dtoy.
Qed.

Lemma card_orbit : #|orbit| = #|G : stabilizer|.
Proof.
pose f b := [set x \in G | to a x == b].
have injf: injective (fun u : {b | b \in orbit} => f (val u)).
  move=> [b Gb] [c Gc] /= eq_f; apply: val_inj => /=; apply: eqP.
  case/orbitP: Gb {Gc} => [x Gx Dxa]; move/setP: eq_f.
  by move/(_ x); rewrite !inE Dxa Gx eqxx.
have f_to: forall x, x \in G -> f (to a x) = stabilizer :* x.
  move=> x Gx; apply/setP=> y; have Gx1:= groupVr Gx.
  rewrite mem_rcoset !inE groupMr //; case Gy: (y \in G) => //=.
  by rewrite actM (canF_eq (actKV x)).
rewrite /= -(card_sig (mem orbit)) -(card_image injf); apply: eq_card=> A.
apply/imageP/rcosetsP=> [[[b Gb] _] | [x Gx]] -> {A}/=.
  by case/orbitP: Gb => [x Gx <-]; exists x; rewrite // f_to.
by exists (exist [eta mem orbit] _ (orbit_to Gx)); rewrite //= f_to.
Qed.

Lemma card_orbit_div : #|orbit| %| #|G|.
Proof. by rewrite -(LaGrange subset_stab) -card_orbit dvdn_mull. Qed.

Lemma card_orbit1 : #|orbit| = 1%N -> orbit = [set a].
Proof.
move=> c1; symmetry; apply/setP; apply/subset_cardP.
  by rewrite cards1 c1.
by rewrite sub1set orbit_refl.
Qed.

Lemma trans_orbit: forall S : pred sT,
  a \in S -> transitive S -> orbit =i S.
Proof.
move => S Ha Ht z.
rewrite -(Ht _ Ha) /orbit.
by apply/imsetP/imsetP.
Qed.

Lemma trans_div: forall S : pred sT, a \in S -> transitive S -> #|S| %| #|G|.
Proof.
move => S Ha Ht.
suff ->: #|S| = #|orbit| by apply: card_orbit_div.
by apply: sym_equal; apply: eq_card; apply: trans_orbit.
Qed.

End Action.

Notation "[ 'action' 'of' a ]" :=
  (match [is a : _ -> _ <: action _ _] as s
   return {type of @Action _ _ for s} -> _ with
  | Action _ a1 aM => fun k => k _ a1 aM end
  (@Action _ _ a)) (at level 0, only parsing) : form_scope.

Lemma normal_stab: forall gT sT (to : action gT sT) (H1 H2 : {group _}) a, 
  H2 \subset'N(H1) -> stabilizer to H2 a \subset 'N(stabilizer to H1 a).
Proof.
move=> gT sT to H1 H2 a Hnorm.
apply/subsetP => g; case/stabilizerP => Hg Hperm.
rewrite /normaliser inE; apply/subsetP => g1 /=.
rewrite mem_conjg; case/stabilizerP => Hg1 Hperm1.
apply/stabilizerP; split.
by move/normalP: Hnorm; move/(_ g Hg) => <-; rewrite mem_conjg.
move: Hperm1; rewrite !actM invgK Hperm -actM => Hperm1.
by rewrite -{2}Hperm -{2}Hperm1 -!actM; gsimpl.
Qed.

Section Faithful.

Variable sT : finType.
Variable gT : finGroupType.
Variable to : action gT sT.
Variable G : group gT.
Variable S : pred sT.

Definition akernel := \bigcap_(x \in S) stabilizer to G x.

Lemma akernelP : forall x,
  reflect (forall y, y \in S -> x \in G /\ to y x = y) (x \in akernel).
Proof.
move=> x; apply: (iffP (bigcapP _ _ _)) => stS y; move/stS {stS}.
  by rewrite inE; case/andP=> Gx; move/eqP->.
by rewrite inE => [] [-> ->] /=.
Qed.

Canonical Structure akernel_group := Eval hnf in [group of akernel].

Lemma akernel1 : 1 \in akernel.
Proof. exact: group1. Qed.

Definition faithful := #|akernel| == 1%N.

Lemma faithfulP:
  reflect (forall x, (forall y, y \in S -> x \in G /\ to y x = y) -> x = 1)
          faithful.
Proof.
rewrite /faithful (cardD1 1) akernel1 eqSS; apply: (iffP pred0P) => ker1 x /=.
  by move/akernelP=> Kx; have:= ker1 x; rewrite /= Kx andbT; move/eqP.
by case: akernelP=> Kx; rewrite (andbF, ker1 x) // eqxx.
Qed.

End Faithful.

Section FaithfulProp.

Variable sT : finType.
Variable gT : finGroupType.
Variable to : action gT sT.
Variable H G : group gT.
Variable S : pred sT.
Variable sHG : H \subset G.

Lemma subset_faithful: faithful to G S -> faithful to H S.
Proof.
move/faithfulP => HG.
apply/faithfulP => x HG1; apply: HG.
move=> y Gy; case: (HG1 _ Gy) => HG2 HG3.
by split; first by apply: (subsetP sHG).
Qed.

End FaithfulProp.

Section ModP.

Variable (gT : finGroupType) (sT : finType).

Variable to : action gT sT.

Variable G : group gT.

(***********************************************************************)
(*                                                                     *)
(*           The mod p lemma                                           *)
(*                                                                     *)
(***********************************************************************)


Lemma orbit_sym : forall x y, (y \in orbit to G x) = (x \in orbit to G y).
Proof.
move=> x y; apply/imsetP/imsetP; case=> z Gz ->;
  exists z^-1; rewrite ?groupV //; symmetry; apply: actK; eauto.
Qed.

Lemma orbit_trans : forall x y,
  connect [rel of orbit to G] x y = (y \in orbit to G x).
Proof.
move=> x y; apply/idP/idP; last by move => *; apply: connect1.
move/connectP=> [p Hp <- {y}]; rewrite orbit_sym.
elim: p x Hp => [|y p IHp] x /=; first by rewrite orbit_refl.
move/andP=> [Hxy Hp].
move: (IHp _ Hp) => H1; rewrite -/orbit orbit_sym in Hxy.
rewrite orbit_sym /orbit /imset !unlock !inE in H1 Hxy *.
rewrite -(f_diinv H1) -(f_diinv Hxy) -{1}(act1 to y) -(mulgV (diinv H1)).
set k := diinv H1.
set k1 := diinv Hxy.
have F1: k \in G by apply (a_diinv H1).
have F2: k1 \in G by apply (a_diinv Hxy).
rewrite actM -actM.
by apply: mem_image; rewrite /= groupM // groupV.
Qed.

Lemma orbit_csym : connect_sym [rel of orbit to G].
Proof. by move=> x y; rewrite !orbit_trans orbit_sym. Qed.

Lemma mpl : forall n p (S : pred sT),
   prime p -> #|G| = (p ^ n)%N -> closed [rel of orbit to G] (mem S) ->
   #|S| %% p = #|predI (act_fix to G) (mem S)| %% p.
Proof.
move=> n p S prime_p cardG; elim: {S}_.+1 {-2}S (ltnSn #|S|) => // m IHm S.
rewrite ltnS => leSm GactS.
case: (pickP (predD (mem S) (act_fix to G))) => [a | fixS]; last first.
  congr modn; apply: eq_card => a; rewrite !inE /= andbC; symmetry.
  by move/(_ a): fixS; rewrite /= andbC; case: (a \in S) => //=; move/negbEF.
pose aG := orbit to G a.
move/andP=> /= [nfixa Sa]; rewrite -(cardID (mem aG) S) memE.
have [i ->]: exists i, #|[predI S & aG]| = (p * p ^ i)%N.
  have ->: #|[predI S & aG]| = #|aG|.
    apply: eq_card => b; rewrite inE /= andbC; case aGb: (b \in aG) => //=.
    by rewrite -[b \in S](GactS a).
  have: #|aG| %| p ^ n by rewrite -cardG card_orbit_div.
  case/dvdn_exp_prime=> //= [] [_ fixa|i]; last by exists i.
  case/orbit1P: nfixa; symmetry; exact: card_orbit1.
rewrite mulnC modn_addl_mul {}IHm; last first.
- move=> b1 b2  /= orbGb12; rewrite !inE /= [b1 \in S](GactS _ b2) //=.
  congr (~~ _ && _).
  rewrite -!orbit_trans in orbGb12 *; apply: same_connect_r => //=.
  exact: orbit_csym.
- apply: leq_trans leSm => {m IHm}.
  rewrite -(cardID (mem aG) S) memE -add1n leq_add2r lt0n.
  by apply/pred0Pn; exists a; rewrite /= Sa /aG orbit_refl.
congr (_ %% p); apply: eq_card => b //=; rewrite !inE /= inE /= andbCA andbC.
case: (@andP _ (b \in S)) => //= [[fixb Sb]].
rewrite orbit_sym -(orbit1P _ _ _ fixb).
by apply/set1P=> eqab; rewrite eqab fixb in nfixa.
Qed.

End ModP.

(*  Definition of the right translation as an action on cosets.        *)

Definition trans_action G :=
  @Action G _ (fun A x => A :* x) (@rcoset1 G) (@rcosetM G).

Section Bij.

Variable (G : finGroupType) (H K : {group G}).

Hypothesis subset_HK : H \subset K.

Section LBij.

Variable L : group G.
Hypothesis subset_LK : L \subset K.

(***********************************************************************)
(*                                                                     *)
(*  Definition of the set of element of orbit 1 by the right           *)
(*    translation  of rcoset of H in K                                 *)
(*                                                                     *)
(***********************************************************************)

Definition rtrans_fix :=
  rcosets H K :&: [set s | act_fix (trans_action G) L s].

Lemma act_fix_sub : forall x,
  act_fix (trans_action G) L (H :* x) -> L \subset H :^ x.
Proof.
move=> x; move/act_fixP => H1.
apply/subsetP => y Hy.
move: (H1 _ Hy) => /= H2.
have F1: x \in H :* x := rcoset_refl _ _.
rewrite -H2 in F1; case/rcosetP: F1 => x1.
case/rcosetP => y1 Hy1 ->; move/(canLR (mulKg _)) <-.
by rewrite (conjgC y1) invMg mulgKV groupV memJ_conjg.
Qed.

End LBij.

Lemma act_fix_norm : forall x,
  act_fix (trans_action G) H (H :* x) = (x \in normaliser H).
Proof.
move=> x; apply/act_fixP/idP.
   rewrite -groupV inE => dHx; apply/subsetP=> y.
   rewrite mem_conjgV => Hxy.
   rewrite -(actK (trans_action G) x H) /= -(dHx _ Hxy) /=.
   by rewrite -!rcosetM mulgA -conjgC mulgK rcoset_refl.
by move=> Nx y Hy; rewrite /= (norm_rlcoset Nx) -mulgA rcoset_id.
Qed.

Lemma rtrans_fix_norm : rtrans_fix H = rcosets H 'N_K(H).
Proof.
apply/setP=> Hx; apply/setIP/rcosetsP=> [[]|[x]].
  case/rcosetsP=> x Kx ->{Hx}; rewrite inE act_fix_norm => Nx.
  by exists x; rewrite // inE Kx.
case/setIP=> Nx Kx ->; split; first by apply/rcosetsP; exists x.
by rewrite inE act_fix_norm.
Qed.

End Bij.


(**********************************************************************)
(*   Definition of the group action x |-> [ H |-> xHx^-1              *)
(**********************************************************************)

Section GroupAction.

Variable gT : finGroupType.
Implicit Type P : {group gT}.

Lemma gconj1 : forall P, (P :^ 1)%G = P.
Proof. move=> P; apply: group_inj; exact: conjsg1. Qed.

Lemma gconjM : forall P x y, (P :^ (x * y) = (P :^ x) :^ y)%G.
Proof. move=> P x y; apply: group_inj; exact: conjsgM. Qed.

Definition gconj_action := Action gconj1 gconjM.

End GroupAction.

(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Definition of permutation as an action                             *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)

Section PermAction.

Variable sT : finType.
Notation gT := {perm sT}.

Definition perm_to x (u : gT) := u x.

Lemma perm_act1 : forall x, perm_to x 1 = x.
Proof. exact: permE. Qed.

Lemma perm_actM : forall a (x y : gT),
  perm_to a (x * y) = perm_to (perm_to a x) y.
Proof. move=> *; exact: permM. Qed.

Canonical Structure perm_action := Action perm_act1 perm_actM.

Lemma perm_act1P : forall x, reflect (forall a, perm_to a x = a) (x == 1).
Proof.
move=> x; apply: (iffP eqP) => [-> a | idperm]; first exact: act1.
by apply/permP=> a; rewrite [x a]idperm perm1.
Qed.

End PermAction.

Implicit Arguments perm_act1P [sT x].
Prenex Implicits perm_act1P.

Section PermFact.

Variable sT : finType.
Variable gT : finGroupType.
Variable to : action gT sT.

Definition perm_of_act x := perm_of (@inj_act _ _ to x).

Lemma perm_of_op : forall x a, perm_of_act x a = to a x.
Proof. by move=> x a; rewrite permE. Qed.

Lemma perm_of_actM : forall x y,
  perm_of_act (x * y) = perm_of_act x * perm_of_act y.
Proof. by move=> x y; apply/permP => a; rewrite permM !permE actM. Qed.

Lemma perm_to_act : forall x a, perm_to a (perm_of_act x) = to a x.
Proof. exact: perm_of_op. Qed.

End PermFact.

Section Primitive.

Variables (gT : finGroupType) (sT : finType).
Variables (to : action gT sT) (G : group gT) (S : pred sT).

Definition primitive :=
  forallb P : {ffun sT -> {ffun pred sT}},
   [==> forallb a, (a \in S) ==> P a a,
        forallb a, forallb b, forallb x,
         [==> a \in S, b \in S, x \in G, P a b => P (to a x) == P (to b x)]
    => (forallb a, forallb b, [==> a \in S, b \in S, P a b => a == b])
    || (forallb a, forallb b, [==> a \in S, b \in S => P a b])].

Lemma primitiveP:
  reflect
  (forall (P : rel sT),
      (forall a, a \in S -> P a a)
   -> (forall a b x, a \in S -> b \in S -> x \in G ->
       P a b -> P (to a x) =1 P (to b x))
   -> (forall a b, a \in S -> b \in S -> P a b -> a = b)
   \/ (forall a b, a \in S -> b \in S -> P a b))
   primitive.
Proof.
apply: (iffP forallP) => /= [prim P Prefl Pinv | prim P].
  pose gP := [ffun a => [ffun b => P a b]]; simpl in gP.
  case: forallP {prim}(prim gP) => [_ | [a]]; last first.
    by apply/implyP; rewrite !ffunE; auto.
  case: forallP => [_ /= | [a]]; last first.
    apply/forallP=> b; apply/forallP=> x; rewrite !ffunE.
    apply/implyP=> Sa; apply/implyP=> Sb; apply/implyP=> Gx.
    apply/implyP=> Pab; apply/eqP; apply/ffunP=> c; rewrite !ffunE; exact: Pinv.
  case/orP; move/forallP=> prim; [left | right] => a b Sa Sb => [Pab|];
    move/forallP: {prim}(prim a); move/(_ b); rewrite Sa Sb !ffunE ?Pab //=.
  by move/eqP.
apply/implyP; move/forallP=> Prefl; apply/implyP; move/forallP=> Pinv.
apply/orP; case: {prim}(prim (fun x y => P x y)) => [a Sa | a b x Sa Sb Gx Pab | P1 | PS].
- by move/(_ a): Prefl; rewrite Sa.
- move/forallP: (Pinv a); move/(_ b); move/forallP; move/(_ x).
  by rewrite Sa Sb Gx Pab; case: eqP=> // ->.
- left; apply/forallP=> a; apply/forallP=> b; apply/implyP=> Sa; apply/implyP=> Sb.
  apply/implyP=> Pab; apply/eqP; exact: P1.
right; apply/forallP => a; apply/forallP => b; apply/implyP=> Sa; apply/implyP=> Sb; exact: PS.
Qed.

Hypothesis Gtrans : transitive to G S.

Lemma trans_closed : forall x, x \in G -> forall a, (to a x \in S) = (a \in S).
Proof.
move=> x Gx a; apply/idP/idP=> Sa; rewrite -(Gtrans Sa); apply/imsetP; last by exists x.
by exists x^-1; rewrite (groupV, actK).
Qed.

Lemma primitivePt:
  reflect
    (forall Y : pred sT,
        Y \subset S -> wdisjointn (mem G) (fun x => [image to^~ x of Y])
     -> #|Y| <= 1 \/ Y =i S)
   primitive.
Proof.
have impre: forall A x, image (to^~ x^-1) A =1 xpreim (to^~ x)  A.
  move=> A x a; rewrite -{1}[a](actK to x) image_f //; exact: inj_act.
apply: (iffP primitiveP) => [prim Y sYS impY| prim P Prefl Pinv].
  case: leqP => cardY; [by left | right]; apply/subset_eqP; rewrite sYS /=.
  case: (pickP Y) => [a Ya | Y0]; last by rewrite eq_card0 in cardY.
  move/subsetP: sYS => sYS; have Sa := sYS _ Ya.
  pose P b c := existsb x, [&& x \in G, Y (to b x) & Y (to c x)].
  case: {prim}(prim P) => [b Sb | {a Sa Ya} a b x Sa Sb Gx | P1 | PS].
  - move: Sa; rewrite -(Gtrans Sb); case/imsetP=> x Gx tobx.
    by apply/existsP; exists x; rewrite -tobx Gx Ya.
  - case/existsP=> [y]; case/and3P=> Gy Yay Yby c.
    wlog Pbxc: a b Sa Sb Yay Yby / P (to b x) c.
      by move=> impl; apply/idP/idP => P_y; move/impl: (P_y) ->.
    rewrite Pbxc; case/existsP: Pbxc => z; case/and3P=> Gz Ybxz Ycz.
    apply/existsP; exists z; rewrite Gz {c}Ycz /= andbT -actM -impre.
    by rewrite [_ a](impY _ y^-1 b) /= ?(groupM, groupV) // impre ?actM.
  - rewrite (cardD1 a) [a \in Y]Ya ltnS lt0n in cardY.
    case/pred0P: cardY => b /=; apply/andP=> [[nab Yb]]; case/eqP: nab.
    apply P1; auto; apply/existsP; exists (1 : gT).
    by rewrite group1 !act1 Ya andbT.
  apply/subsetP=> b Sb; case/existsP: (PS _ _ Sa Sb) => x; case/and3P=> Gx Yax.
  move: Sb; rewrite -(Gtrans Sa); case/imsetP=> y Gy ->{b} Yayx.
  rewrite -[_ \in Y](impre Y).
  by rewrite [_ a](impY _ (y * x)^-1 (to a y^-1)) /= ?(groupM, groupV) //;
     rewrite impre ?actM ?actKV.
case: (pickP S) => [a Sa | S0]; last by left=> x y; rewrite [_ \in S]S0.
pose Y := predI S (P a); case: {prim}(prim Y) => [|x y b Gx Gy | Y1 | YS].
- by apply/subsetP=> b; case/andP.
- rewrite -[x]invgK -[y]invgK !impre /= => Yxb Yyb c; rewrite !impre /=.
  wlog Yyc: x y Gx Gy Yxb Yyb / to c y^-1 \in Y.
     by move=> impl; apply/idP/idP => Y_c; move/impl: (Y_c) ->.
  rewrite Yyc; case/andP: Yyc => /= Syc Payc; rewrite inE /=.
  have Sxc: S (to c x^-1) by rewrite ![S _]trans_closed ?groupV in Syc *.
  case/andP: Yxb => Sxb Paxb; case/andP: Yyb => Syb Payb.
  rewrite Sxc -[a](act1 to); move/Pinv: Paxb ->; rewrite // act1.
  have Gyx: y * x^-1 \in G by rewrite groupM ?groupV.
  rewrite -[b](actKV to y) -actM; move/Pinv: Payb => <- //.
  by move/Pinv: Payc => -> //; rewrite actM actKV Prefl.
- left=> b c Sb; rewrite -(Gtrans Sa); case/imsetP=> x Gx ->{c} Pbax.
  rewrite (cardD1 a) inE /= Sa Prefl // ltnS leqn0 in Y1.
  move/pred0P: Y1; move/(_ (to b x^-1)); rewrite /= inE /= andbC.
  rewrite [S _]trans_closed ?groupV // Sb -{1}[a](actK to x) /=.
  move/Pinv: Pbax <-; rewrite ?(Prefl, trans_closed, groupV) //.
  by move/eqP <-; rewrite actKV.
right=> x y; rewrite -2!YS; case/andP=> Sx Pax; case/andP=> Sy.
by rewrite -[a](act1 to); move/Pinv: Pax ->; rewrite ?act1.
Qed.

Lemma prim_trans_norm : forall H : {group gT},
  primitive -> H <| G -> H \subset akernel to G S \/ transitive to H S.
Proof.
move=> H prim; case/normalsubP=> sHG nHG; pose P a := [image to a of H].
case: (primitiveP prim P) => [a Sa | a b x Sa _ Gx | P1 | PS].
- by apply/imageP; exists (1 : gT); rewrite /= ?act1.
- case/imageP=> y Hy ->{b} c; apply/imageP/imageP; case=> z Hz ->{c}.
    exists (y^-1 ^ x * z); last by rewrite !(actM, actK).
    by rewrite /= groupMl // -mem_conjgV nHG groupV.
  exists (y ^ x * z); last by rewrite !(actM, actK).
  by rewrite /= groupMl // -mem_conjgV nHG ?groupV.
- left; apply/subsetP => x Hx; have Gx: x \in G by apply: (subsetP sHG).
  apply/akernelP => a Sa; split=> //; apply: P1; rewrite ?trans_closed //.
  by apply/imageP; exists x^-1; rewrite /= (groupV, actK).
right=> a Sa b; apply/imsetP/idP=> [[x Hx ->{b}] | Sb].
  by rewrite trans_closed ?(subsetP sHG).
by case/imageP: (PS a b Sa Sb) => x Hx ->{b Sb}; exists x.
Qed.

End Primitive.

Section NTransitive.

Variable (gT : finGroupType) (sT : finType).
Variable to : action gT sT.
Variable G : group gT.
Variable S : pred sT.
Variable n :  nat.

Notation tT := (tuple n sT).

Definition n_act (t : tT) a : tT := [tuple of maps (to^~ a) t].

Lemma n_act1 : forall t, n_act t 1 = t.
Proof. by move=> t; apply: eq_from_tsub=> i; rewrite tsub_maps act1. Qed.

Lemma n_actM : forall t a b, n_act t (a * b) = n_act (n_act t a) b.
Proof. by move=> t a b; apply: eq_from_tsub=> i; rewrite !tsub_maps actM. Qed.

Canonical Structure n_act_action := Action n_act1 n_actM.

Definition dtuple_on (t : tT) := uniq t && all (mem S) t.
Definition ntransitive := transitive n_act_action G dtuple_on /\ n <= #|S|.

Lemma dtuple_onP : forall t : tT,
  reflect (injective (tsub t) /\ forall i, tsub t i \in S) (dtuple_on t).
Proof.
move=> t; rewrite /dtuple_on -maps_tsub_enum.
case: (uniq _) / (injectiveP (tsub t)) => f_inj; last by right; case.
rewrite -[all _ _]negbK -has_predC has_maps has_predC negbK /=.
by apply: (iffP allP) => [Sf|[]//]; split=> // i; rewrite Sf ?mem_enum.
Qed.

Lemma n_act_dtuple : forall t a,
  [preim to^~ a of S] =i S -> dtuple_on t -> dtuple_on (n_act t a).
Proof.
move=> t a toSa; case/dtuple_onP=> t_inj St; apply/dtuple_onP.
split=> [i j | i]; rewrite !tsub_maps ?[_ \in S]toSa //.
by move/inj_act; exact: t_inj.
Qed.

End NTransitive.

Implicit Arguments n_act [gT sT n].

Section NTransitveProp.

Variable (gT : finGroupType) (sT : finType).
Variable to : action gT sT.
Variable G : {group gT}.
Variable S : pred sT.

Lemma card_uniq_tuple m (t : tuple m sT) : uniq t -> #|t| = m.
Proof. move=> m t; move/card_uniqP->; exact: size_tuple. Qed.

Lemma n_act0 (t : tuple 0 sT) a : n_act to t a = [tuple].
Proof. move=> *; exact: tuple0. Qed.

Lemma dtuple_on_add m (x : sT) (t : tuple m sT) :
  dtuple_on S [tuple of x :: t] = [&& x \in S, x \notin t & dtuple_on S t].
Proof. move=> *; rewrite /dtuple_on -!andbA; do!bool_congr. Qed.

Lemma dtuple_on_add_D1 m (x : sT) (t : tuple m sT) :
  dtuple_on S [tuple of x :: t] = (x \in S) && dtuple_on [predD1 S & x] t.
Proof.
move=> m x t; rewrite /dtuple_on /= all_predI all_predC has_pred1 -!andbA.
by do!bool_congr.
Qed.

Lemma dtuple_on_subset m (S1 S2 : pred sT) (t : tuple m sT) :
  S1 \subset S2 -> dtuple_on S1 t -> dtuple_on S2 t.
Proof.
move=> m S1 S2 t sS12; rewrite /dtuple_on /=; case/andP=> ->.
move/allP=> tS1; apply/allP=> x; move/tS1; exact: (subsetP sS12).
Qed.

Lemma n_act_add m x (t : tuple m sT) a :
  n_act to [tuple of x :: t] a = [tuple of to x a :: n_act to t a].
Proof. by move=> *; exact: val_inj. Qed.

Lemma ntransitive0 : ntransitive to G S 0.
Proof.
split => // x _ y; rewrite [y]tuple0 [x]tuple0; apply/imsetP=> /=.
exists (1 : gT) => //; exact: val_inj.
Qed.

Lemma ntransitive_weak : forall k m,
  k <= m -> ntransitive to G S m -> ntransitive to G S k.
Proof.
move=> k m; move/subnK <-; rewrite addnC; elim: {m}(m - k) => // m IHm.
rewrite addSn => tr_m1; apply: IHm; move: {m k}(m + k) tr_m1 => m [tr_m1 lt_m].
have ext_t: forall t, (dtuple_on S) m t ->
  exists x, dtuple_on S [tuple of x :: t].
- move=> t dt; case sSt: (S \subset t); last first.
    case/subsetPn: sSt => x Sx ntx.
    by exists x; rewrite dtuple_on_add andbA /= Sx ntx.
  have:= subset_leq_card sSt; rewrite leqNgt card_uniq_tuple ?lt_m //.
  by case/andP: dt.
split=> [t dt u {lt_m}|]; last exact: ltnW.
case: (ext_t _ dt) => x; set xt := [tuple of _] => dxt.
apply/imsetP/idP=> [[a Ga ->{u}]| du].
  have: dtuple_on S (n_act to xt a).
    by rewrite -[dtuple_on _ _](tr_m1 _ dxt) mem_imset.
  by rewrite -topredE /= n_act_add dtuple_on_add; case/and3P.
case: (ext_t u du) => y; rewrite -[dtuple_on _ _](tr_m1 _ dxt).
case/imsetP=> a Ga; move/(congr1 val) => [_ def_u]; exists a => //.
exact: val_inj.
Qed.

Lemma ntransitive1 : forall m,
  0 < m -> ntransitive to G S m -> transitive to G S.
Proof.
have trdom1: forall x, dtuple_on S [tuple x] = S x by move=> x; exact: andbT.
move=> m m_pos; case/(ntransitive_weak m_pos) => {m m_pos} tr1 _ x Sx y.
rewrite -2![_ \in S]trdom1 in Sx *.
rewrite -[dtuple_on _ _](tr1 _ Sx [tuple y]).
apply/imsetP/imsetP; case=> a Ga def_y; exists a => {Ga}//.
  by apply: val_inj; rewrite def_y.
by case/(congr1 val): def_y.
Qed.

Lemma ntransitive_primitive : forall m,
  2 <= m -> ntransitive to G S m -> primitive to G S.
Proof.
move=> m lt1m; move/(ntransitive_weak lt1m) => {m lt1m} Ht2.
apply/primitiveP => f Hf1 Hf2.
case triv1: (forallb x, (x \in S) ==> (#|predI (mem S) (f x)| == 1%N)).
  left => x y Sx Sy Hf; apply/eqP; apply/idPn=> nxy.
  have:= forallP triv1 x; rewrite (cardD1 x) inE /= Sx Hf1 //=.
  by rewrite (cardD1 y) inE /= (eq_sym y) nxy inE /= Sy Hf.
case/existsP: triv1 => x; rewrite negb_imply; case/andP=> Sx.
rewrite (cardD1 x) inE /= Hf1 // Sx; case/pred0Pn => y /=.
case/and3P=> nxy Sy fxy; right=> x1 y1 Sx1 Sy1.
case: (x1 =P y1) => [-> //|]; [exact: Hf1 | move/eqP; rewrite eq_sym => nxy1].
pose t := [tuple y; x]; pose t1 := [tuple y1; x1].
have{Sx1 Sy1 nxy1} [dt dt1]: dtuple_on S t /\ dtuple_on S t1.
  by split; apply/and3P; rewrite /= ?mem_seq1 ?andbT.
case: (Ht2) dt1 => Ht _; rewrite -{Ht dt}[dtuple_on _ _](Ht t dt).
case/imsetP=> a Ga; case/(congr1 val)=> -> ->.
have trGS : transitive to G S by exact: ntransitive1 Ht2.
by move/Hf2: fxy => -> //; rewrite Hf1 // -(trGS _ Sy) mem_imset.
Qed.

Lemma trans_prim_stab : forall x,
  S x -> transitive to G S -> primitive to G S = maximal (group_stab to G x) G.
Proof.
move=> x Hx Ht; apply/(primitivePt Ht)/maximalP.
  move=> Hp; split; first by apply/subsetP => y; case/stabilizerP.
  move=> H Hk1 Hk2.
  pose Y := image (to x) (mem H).
  have Yx: Y x by apply/imageP; exists (1 : gT); rewrite //= ?act1.
  case: (Hp Y).
  - apply/subsetP => z; case/imageP => g1 Kg1 ->.
    have Hg1: g1 \in G by apply: (subsetP Hk2).
    by rewrite -(Ht _ Hx); apply/imsetP; exists g1.
  - move=> g1 g2 x1 Hg1 Hg2.
    pose YY := fun z => image (fun t => to t z) Y.
    case/imageP => u1; case/imageP => g3 Hg3 -> ->.
    case/imageP => u2; case/imageP => g4 Hg4 ->; rewrite -!actM => Heq.
    move=> z1; apply/imageP/imageP; case => u3; case/imageP => g5 Hg5 -> ->.
      exists (to x (g5 * g1 * g2^-1)); last by rewrite -!actM; gsimpl.
      have ->: g5 * g1 * g2^-1 = g5 * (g3^-1 * (g3 * g1 * g2^-1 * g4^-1) * g4) by gsimpl.
      set u := _ * _; apply/imageP; exists u => //=.
      rewrite groupM // groupM // ?groupV // groupM // ?groupV //.
      apply: (subsetP Hk1); apply/stabilizerP; split.
        by rewrite !groupM // ?groupV // (subsetP Hk2) //.
      by rewrite 2!actM Heq -!actM; gsimpl; rewrite act1.
    exists (to x (g5 * g2 * g1^-1)); last by rewrite -!actM; gsimpl.
    have ->: g5 * g2 * g1^-1 = g5 * (g4^-1 * (g4 * g2 * g1^-1 * g3^-1) * g3) by gsimpl.
    set u := _ * _; apply/imageP; exists u => //=.
    rewrite groupM // groupM // ?groupV // groupM // ?groupV //.
    apply: (subsetP Hk1); apply/stabilizerP; split.
      by rewrite !groupM // ?groupV // (subsetP Hk2) //.
    by rewrite 2!actM -Heq -!actM; gsimpl; rewrite act1.
  - move=> HY; left; apply/setP; apply/subset_eqP; rewrite Hk1; apply/subsetP => g1 Hg1.
    have F1: to x g1 \in Y  by apply/imageP; exists g1.
    apply/stabilizerP; split; [exact: (subsetP Hk2) | move: HY].
    by rewrite (cardD1 x) [x \in Y]Yx (cardD1 (to x g1)) inE /= F1; case: eqP.
  move=> HH; right; apply/setP; apply/subset_eqP; rewrite Hk2; apply/subsetP => g Hg.
  have F1: to x g \in S by rewrite -(Ht _ Hx); apply/imsetP; exists g.
  rewrite -HH in F1; case/imageP: F1 => g1 Hg1 Hg2.
  have ->: g = (g * g1^-1) * g1 by gsimpl.
  apply: groupM => //; apply: (subsetP Hk1).
  apply/stabilizerP; split; first by rewrite groupM // groupV (subsetP Hk2).
  by rewrite actM Hg2 -actM mulgV act1.
case=> Hs Hst Y Hsub Hd.
case E1: (#|Y| <= 1); first by left.
right; move/idP: E1; move/idP; rewrite -(ltnNge) => E1.
have F1: ~Y =1 pred0 by move => F1; move: E1; rewrite (eq_card F1) card0.
move/pred0P: F1; case/pred0Pn => y Hy.
have F1: ~ (predD1 Y y) =1 pred0.
  by move=> F1; move: E1; rewrite (cardD1 y) [y \in Y]Hy (eq_card F1) card0.
move/pred0P: F1; case/pred0Pn => y1; case/andP => Hy1 Yy1.
have Sy: y \in S by apply: (subsetP Hsub).
have Sy1: y1 \in S by apply: (subsetP Hsub).
have:= Hx; rewrite -[S x](Ht _ Sy); case/imsetP => g Hg He.
pose Y1 := image (to^~ g) Y.
have F1: Y1 x by apply/imageP; exists y.
have Fi: forall z, image (to^~ z) Y1 =1 image  (to^~(g * z)) Y.
  move=> g1 x1;apply/imageP/imageP; case => x2.
    by case/imageP => x3 Hx3 -> ->; exists x3; rewrite // actM.
  move=> Hx2 ->; exists (to x2 g); last by rewrite actM.
  by apply/imageP; exists x2.
have Hd1: wdisjointn (mem G) (fun z => image (to^~ z) Y1).
  move=> g1 g2 x1 Hg1 Hg2 /=; rewrite !Fi => HH HH1 z /=.
  by rewrite !Fi; apply: (Hd _ _ x1); try apply: groupM.
pose H := [set a \in G | to x a \in Y1].
have F2: group_set H.
  apply/andP; split; first by rewrite inE /= act1 group1.
  apply/subsetP => z; case/mulsgP => g1 g2.
  rewrite !inE /=; case/andP => Hg1 Yg1; case/andP => Hg2 Yg2 ->.
  apply/andP; split; first by apply: groupM.
  pose YY := fun z => image (to^~ z) Y1.
  have F2: YY 1 =i Y1.
    move => z1; apply/imageP/idP; first  by case => z2 Hz2 ->; rewrite act1.
    by move => Hz1; exists z1; rewrite // act1.
  have F3: YY g2 =1 YY 1.
    apply: (@Hd1 _ _ (to x g2)); rewrite //=.
      by apply/imageP; exists x.
    by apply/imageP; exists (to x g2); rewrite // act1.
  have F4: YY (g1 * g2) =i YY 1.
    apply: (@Hd1 _ _ (to x (g1 * g2))); rewrite /= ?in_group //.
      by apply/imageP; exists x.
    rewrite /YY in F3; rewrite -F3.
    by apply/imageP; exists (to x g1); rewrite // actM.
  by rewrite /= -F2 -F4; apply/imageP; exists x.
case (Hst (Group F2)) => // [|||F3].
- apply/subsetP => g1; case/stabilizerP => Hg1 Heq.
  by rewrite inE /= Hg1 /= Heq.
- by apply/subsetP=> g1 /=; rewrite inE; case/andP.
- have:= Hx; rewrite -[S x](Ht _ Sy1); case/imsetP=> g1 Hg1 He1.
  case=> HH; case/negP: Hy1; apply/eqP.
  have: g1^-1 * g \in H.
    rewrite inE /= groupM //; last by rewrite groupV.
    rewrite He1 -!actM mulgA mulgV mul1g.
    by apply/imageP; exists y1.
  rewrite -HH; case/stabilizerP=> _ HH1.
  apply: (@inj_act _ _ to g).
  by rewrite -He -HH1 actM {1}He1 -!actM !mulgA mulgV mul1g.
apply/subset_eqP; rewrite Hsub; apply/subsetP => x1 Hx1.
pose YY := fun z => image (to^~z) Y1.
have ->: Y =i YY g^-1.
  move=> z /=; rewrite [z \in YY _]Fi mulgV; apply/idP/imageP.
    by move=> HH; exists z; rewrite // act1.
  by case => x2 Hx2; rewrite act1 => ->.
have:= Hx1; rewrite -(Ht _ Hx); case/imsetP => g1 Hg1 He1.
apply/imageP; exists (to x (g1 * g)).
  have: g1 * g \in H by rewrite [H]F3 groupM.
  by rewrite inE; case/andP.
by rewrite -!actM -!mulgA mulgV mulg1.
Qed.

End NTransitveProp.

Section NTransitveProp1.

Variable (gT : finGroupType) (sT : finType).

Variable to : action gT sT.
Variable G : group gT.
Variable S : pred sT.

(* Corresponds to => of 15.12.1 Aschbacher *)
Theorem stab_ntransitive : forall m x,
     0 < m -> x \in S ->  ntransitive to G S m.+1
  -> ntransitive to (group_stab to G x) [predD1 S & x] m.
Proof.
move=> m x m_pos Sx Gntr; case: (Gntr) => [Gtr ltmS].
have sSxS: predD1 S x \subset S by apply/subsetP=> y; case/andP.
(split; move)=> /= [t1 dt1 t2|]; last by rewrite (cardD1 x) Sx in ltmS.
have dxt1: dtuple_on S [tuple of x :: t1] by rewrite dtuple_on_add_D1 Sx.
apply/imsetP/idP => [[a]|dt2].
  case/stabilizerP=> Ga toxa ->{t2}; rewrite [_ \in _]n_act_dtuple // => y /=.
  rewrite !inE /= inE /= -{1}toxa (inj_eq (@inj_act _ _ _ _)).
  by rewrite (trans_closed (ntransitive1 _ Gntr)).
have: dtuple_on S [tuple of x :: t2] by rewrite dtuple_on_add_D1 Sx.
rewrite -[dtuple_on _ _](Gtr _ dxt1) //; case/imsetP => [a Ga].
case/(congr1 val)=> tox def_t2; exists a; last exact: val_inj.
exact/stabilizerP.
Qed.

(* Correspond to <= of 15.12.1 Aschbacher *)
Theorem stab_ntransitiveI : forall m x,
     x \in S ->  transitive to G S
  -> ntransitive to (group_stab to G x) [predD1 S & x] m
  -> ntransitive to G S m.+1.
Proof.
move=> m x Sx Gtr [Gntr geS'm].
have t_to_x: forall t : tuple m.+1 sT, dtuple_on S t ->
  exists2 a, a \in G & exists2 t', dtuple_on [predD1 S & x] t'
       & t = n_act to [tuple of x :: t'] a.
- case/tupleP=> y t St.
  have Sy: S y by rewrite dtuple_on_add_D1 in St; case/andP: St.
  move/Gtr: Sy Sx => <-; case/imsetP=> a Ga toya.
  exists a^-1; first exact: groupVr.
  exists (n_act to t a); last by rewrite n_act_add toya !actK.
  move/(n_act_dtuple (trans_closed Gtr Ga)): St.
  by rewrite n_act_add -toya dtuple_on_add_D1; case/andP.
split=> [{geS'm} t1 St1 t2|]; last by rewrite (cardD1 x) Sx.
apply/imsetP/idP=> [[a Ga ->] | ].
  by apply: n_act_dtuple; first exact: (trans_closed Gtr).
case/t_to_x: St1 => a1 Ga1 [t St ->{t1}].
case/t_to_x=> a2 Ga2 [t2']; rewrite -[dtuple_on _ _](Gntr _ St).
case/imsetP=> a; case/stabilizerP=> Ga toxa -> -> {t2 t2'}.
exists (a1^-1 * (a * a2)); first by rewrite !groupMl ?groupV.
by rewrite !actM actK /= (n_act_add _ _ t) toxa.
Qed.

(* => of 5.20 Aschbacher *)
Theorem subgroup_transitive : forall (H : {group gT}) x,
     x \in S -> H \subset G -> transitive to G S -> transitive to H S
  -> stabilizer to G x * H = G.
Proof.
move=> H x Hx H1 H2 H3.
set G_x := stabilizer to G x.
apply/setP => z; apply/mulsgP/idP => [[hx1 k1 Hx1 Hk1 ->] | Hz].
  apply: groupM; last by apply: (subsetP H1).
  by apply (subsetP (subset_stab to G x)).
pose y := to x z.
have Hy: y \in S by rewrite -(H2 x Hx); apply/imsetP; exists z.
have:= Hy; rewrite -(H3 x Hx); case/imsetP => k Hk Hk1.
exists (z * k ^-1)  k => //; last by gsimpl.
apply/stabilizerP; split; first by rewrite groupM // groupV (subsetP H1).
by rewrite actM -/y Hk1 -actM mulgV act1.
Qed.

(* <= of 5.20 Aschbacher *)
Theorem subgroup_transitiveI : forall (H : {group gT}) x,
     x \in S -> H \subset G -> transitive to G S
  -> stabilizer to G x * H = G
  -> transitive to H S.
Proof.
move=> H x Hx Hkh Ht Heq x1 Hx1 y1.
apply/imsetP/idP => [[g1 Hg1 ->] | Hy1].
  have F: g1 \in G by apply: (subsetP Hkh).
  by rewrite -(Ht _ Hx1); apply/imsetP; exists g1.
have:= Hx1; rewrite -(Ht _ Hx); case/imsetP => [g1 Hg1 Hgg1].
have:= Hg1; rewrite <- Heq; case/mulsgP => h1 k1 Hh1 Hk1 Hhk1.
have:= Hy1; rewrite -(Ht _ Hx); case/imsetP => [g2 Hg2 Hgg2].
have:= Hg2; rewrite <- Heq; case/mulsgP => h2 k2 Hh2 Hk2 Hhk2.
exists (k1^-1 * k2); first by rewrite groupM // groupV.
rewrite Hgg1 Hhk1 -actM; gsimpl; rewrite Hgg2 Hhk2 !actM.
by case/stabilizerP: Hh1 => _ ->; case/stabilizerP: Hh2 => _ ->.
Qed.

End NTransitveProp1.
