(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import choice fintype finfun tuple.
Require Import bigop ssralg.
Require Import generic_quotient zmodp.

Require Import orderedalg.
Import ORing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Relative.

Definition axiom (z : nat*nat) := (z.1 == 0) || (z.2 == 0).
Definition type := { z | axiom z }.
Definition Build z (pz : axiom z) : type := @exist _ axiom _ pz.

Lemma one_diff_eq0 : forall x y, (x - y == 0) || (y - x == 0).
Proof. elim=> [| x Ih] [| y] //; exact: Ih. Qed.

Definition canon (x : nat*nat) :=
  @Build ((x.1-x.2),(x.2-x.1)) (one_diff_eq0 _ _).

Lemma canon_valK : forall x, canon (val x)  = x.
Proof.
move=> [[x y] Hx]; apply/val_eqP=> /=.
by case/orP: Hx; move/eqP=> /= ->; rewrite sub0n subn0.
Qed.

Definition quotType := Eval hnf in
  @QuotType _ type [eta val] [eta canon] canon_valK.

End Relative.

Notation relative := Relative.type.
Notation Relative := Relative.Build.

Canonical Structure relative_eqType := [eqType of relative].
Canonical Structure relative_quotType := Relative.quotType.
Canonical Structure relative_subType := [subType of [quotType of relative]].
Canonical Structure relative_choiceType := [choiceType of relative].

Notation "[ n ]%z" := (\pi_relative (n:nat,0)).
Notation "[- n ]%z" := (\pi_relative (0,n:nat)).

Section RelativeTheory.

Definition one_diff_eq0 := Relative.one_diff_eq0.

Lemma relPN : forall P:(relative -> Prop),
  (forall x: nat, P [x]%z) -> (forall x, P [-x]%z) -> forall x, P x.
Proof.
move=> P Ppos Pneg; apply:quotP=> x <- /=.
case/orP:(one_diff_eq0 x.1 x.2); move/eqP->; [exact:Pneg|exact:Ppos].
Qed.

(* Notation SubRel := (@Sub _ _ [subType of relative]). *)

Definition equivz (x y : nat*nat) := x.1 + y.2 == y.1 + x.2.

Lemma equivzP : forall x y, x == y mod relative = equivz x y.
Proof.
move=> x y; rewrite /equivz /= -(inj_eq val_inj) /=.
apply/eqP/eqP=> /= [[Hx Hy]|H]; last first.
  rewrite -(subn_add2r y.2) H addnC subn_add2l; congr (_,_).
  by rewrite -(subn_add2l y.1) -H [y.1 + _]addnC subn_add2l.
case:(leqP x.1 x.2); last move/ltnW; move=>Px.
  by rewrite -(subnK Px) Hy addnA subnKC /leq -?Hx // addnC.
by rewrite -(subnKC Px) Hx -addnA subnK // /leq -?Hy // addnC.
Qed.

Lemma addz_compat : \compat2_relative _
  (fun x y => \pi_relative (x.1 + y.1 , x.2 + y.2)).
Proof.
apply:compat2E=> x y x' y'.
rewrite !equivzP /equivz; move/eqP=>Px; move/eqP=>Py.
apply/eqP; rewrite equivzP; apply/eqP=> /=.
by rewrite addnAC addnA Px -addnA [y'.2 + _]addnC Py 
           addnAC -!addnA [x'.2 + _]addnC.
Qed.
Notation addz := (qT_op2 addz_compat).

Lemma oppz_compat : \compat1_relative _
  (fun x => \pi_relative (x.2 , x.1)).
Proof.
apply:compat1E=> x x'; rewrite !equivzP /equivz; move/eqP=>Px.
apply/eqP; rewrite equivzP /equivz /=.
by rewrite addnC -Px addnC.
Qed.
Notation oppz := (qT_op1 oppz_compat).

Lemma mulz_compat : \compat2_relative _ (fun x y => \pi_relative
    (x.1 * y.1 + x.2 * y.2 , x.1 * y.2 + x.2 * y.1)).
Proof.
apply:Compat2; elim/relPN=> x; elim/relPN=> y; move=> x' y';
  rewrite !in_qTE /pi_of !equivzP /equivz=> Px Py;
  apply/eqP; rewrite equivzP /=; apply/eqP;
  move/eqP: Px; move/eqP: Py;
  rewrite /= !(sub0n, subn0, mul0n, muln0, add0n, addn0)=> Px Py;
  rewrite (Px,esym Px) (Py,esym Py); ring.
Qed.
Notation mulz := (qT_op2 mulz_compat).

Lemma addzA : associative addz.
Proof.
apply:quotW=>x; apply:quotW=>y; apply:quotW=>z.
by rewrite !qTE; congr pi; rewrite !addnA.
Qed.

Lemma addzC : commutative addz.
Proof.
apply:quotW=>x; apply:quotW=>y.
by rewrite !qTE; congr pi; congr (_,_); rewrite addnC.
Qed.

Lemma add0z : left_id [0]%z addz.
Proof. by apply:quotW=> x; rewrite !qTE. Qed.

Lemma addzN : left_inverse [0]%z oppz addz.
Proof.
apply:quotW=>x; rewrite !qTE; apply/eqP.
by rewrite equivzP /equivz /= addn0 addnC.
Qed.

Definition z_zmodMixin :=  ZmodMixin addzA addzC add0z addzN.
Canonical Structure z_zmodType := Eval hnf in ZmodType relative z_zmodMixin.

Lemma mulzA : associative mulz.
Proof.
apply:quotW=>x; apply:quotW=>y; apply:quotW=>z; rewrite !qTE.
apply/eqP; rewrite equivzP /equivz /=; apply/eqP.
by rewrite !(muln_addl, muln_addr) !mulnA -!addnA; do ?nat_congr.
Qed.

Lemma mulzC : commutative mulz.
Proof.
apply:quotW=>x; apply:quotW=>y; rewrite !qTE; apply/eqP;
 rewrite equivzP /equivz /=; apply/eqP.
by congr (_+_+_); rewrite mulnC // addnC mulnC; congr (_+_).
Qed.

Lemma mul1z : left_id [1]%z mulz.
Proof.
apply:quotW=>x; rewrite !qTE; apply/eqP; rewrite equivzP /equivz /=.
by rewrite !mul0n !mul1n addnA !addn0.
Qed.


Lemma mulz_addl : left_distributive mulz addz.
Proof.
apply:quotW=>x; apply:quotW=>y; apply:quotW=>z; rewrite !qTE.
apply/eqP; rewrite equivzP /equivz /=; apply/eqP.
by rewrite !muln_addl -!addnA; do ?nat_congr.
Qed.

Lemma nonzero1z : [1]%z != [0]%z.
Proof. by rewrite -(inj_eq val_inj) /=. Qed.

Definition z_comRingMixin := ComRingMixin mulzA mulzC mul1z mulz_addl nonzero1z.
Canonical Structure  z_Ring := Eval hnf in RingType relative z_comRingMixin.
Canonical Structure z_comRing := Eval hnf in ComRingType relative mulzC.

Lemma relPM : forall P: relative -> Prop,
  (forall x: nat, P [x]%z) -> (forall x, P x -> P (- x)%R) -> forall x, P x.
Proof.
move=> P Ppos Pneg x; apply: relPN=> // y.
suff->: [-y]%z = oppz [y]%z by apply: Pneg; apply: Ppos.
by rewrite /oppz /= sub0n subn0.
Qed.

Definition unitz := [pred x : relative | ((repr x).1)+((repr x).2) == 1 ].
Definition invz (x : relative) : relative := x.

Lemma mulVz : {in unitz, left_inverse 1%R invz *%R}.
Proof.
elim/relPN=>x; rewrite /invz; rewrite in_simpl /= sub0n subn0 (add0n,addn0);
by move/eqP=> -> /=; apply:val_inj=>/=; congr(_,_).
Qed.


Lemma unitzPl : forall x y, mulz y x = [1]%z -> unitz x.
Proof.
elim/relPN=>x; elim/relPN=>y; move/eqP; rewrite !qTE -(inj_eq val_inj) /=;
rewrite !muln0 !mul0n !add0n ?addn0 !sub0n !subn0 //;
by case/eqP; move/eqP; rewrite muln_eq1; case/andP.
Qed.

Lemma  invz_out : {in predC unitz, invz =1 id}.
Proof. exact. Qed.

Definition z_comUnitRingMixin :=  ComUnitRingMixin mulVz unitzPl invz_out.
Canonical Structure z_unitRingType :=
  Eval hnf in UnitRingType relative z_comUnitRingMixin.

Canonical Structure z_comUnitRing := Eval hnf in [comUnitRingType of relative].

Lemma idomain_axiomz : forall x y,
  mulz x y = [0]%z -> (x == [0]%z) || (y == [0]%z).
Proof.
elim/relPN=>x; elim/relPN=>y; move/eqP; rewrite !qTE -!(inj_eq val_inj) /=;
rewrite !muln0 !mul0n !add0n ?addn0 !sub0n !subn0 //;
case/eqP; move/eqP; rewrite muln_eq0; case/orP; move/eqP->;
by rewrite eqxx (orbT,orTb).
Qed.

Canonical Structure z_iDomain := Eval hnf in IdomainType relative idomain_axiomz.

Lemma leqz_compat : \compat2_relative _ (fun x y => x.1 + y.2 <= y.1 + x.2).
Proof.
apply:Compat2; elim/relPN=> x; elim/relPN=> y; move=> x' y';
rewrite !in_qTE /pi_of !equivzP /equivz ?(addn0,add0n)=> /=;
move/eqP=> Px; move/eqP=> Py; rewrite ?(sub0n,subn0,addn0,add0n).
- by rewrite Px Py addnAC -!addnA leq_add2r.
- rewrite Px -Py addnA ![_+y]addnC !addnA -addnA.
  by rewrite -[y'.1+_]add0n [_+y'.1]addnC leq_add2r.
- rewrite -Px Py addnA ![_+x]addnC !addnA -addnA.
  by rewrite -[x'.1+_]add0n [_+x'.1]addnC leq_add2r.
- by rewrite -Px -Py !addnA [x'.1+_]addnC leq_add2l.
Qed.
Notation leqz := (qT_op2 leqz_compat).

Lemma leqz_anti : antisymmetric leqz.
Proof.
apply:quotW=> x; apply:quotW=> y; rewrite !qTE.
by rewrite -eqn_leq=> exy; apply/eqP; rewrite equivzP.
Qed.

Lemma leqz_trans : transitive leqz.
Proof.
apply:quotW=> x; apply:quotW=> y; apply:quotW=> z; rewrite !qTE.
rewrite -(leq_add2r z.2)=> lxy lxz.
rewrite -(leq_add2r x.2) addnAC; apply: (leq_trans lxy).
by rewrite addnAC -addnA addnAC addnA leq_add2r.
Qed.

Lemma leqz_total : total leqz.
Proof. by apply:quotW=> x; apply:quotW=> y; rewrite !qTE leq_total. Qed.

Lemma leqz_add2r : forall z x y, leqz x y -> leqz (qT_op2 addz_compat x  z) (qT_op2 addz_compat y z).
Proof.
apply:quotW=> z; apply:quotW=> x; apply:quotW=> y; rewrite !qTE /=.
by rewrite ![_+_+(_+_)]addnAC !addnA -![_+_+_+_]addnA leq_add2r.
Qed.

Lemma leq0z_mul : forall x y, leqz [0]%z x -> leqz [0]%z y -> leqz [0]%z (qT_op2 mulz_compat x  y).
Proof.
elim/relPN=> x; elim/relPN=> y; rewrite !qTE /=;
rewrite ?(addn0,add0n,subn0,sub0n,muln0,mul0n,leqn0) //.
  by move=> _; move/eqP->; rewrite muln0.
by move/eqP->; rewrite mul0n.
Qed.


Definition z_oRingMixin := ORing.Mixin leqz_anti 
  leqz_trans leqz_total leqz_add2r leq0z_mul.
Canonical Structure z_oIdomain := Eval hnf in OIdomainType relative z_oRingMixin.

End RelativeTheory.

Section zprojR.

Variable R : ringType.

Import GRing.Theory.

Open Scope ring_scope.

Definition zprojr (a : relative) : R := ((val a).1%:R) - ((val a).2%:R).

Definition zscaler a m := (zprojr a) * m.

Lemma zprojrM : GRing.morphism zprojr.
Proof.
rewrite /zprojr; split; last by rewrite /= sub0n subn0 subr0.
  elim/relPN=> a; elim/relPN=> b /=;
  rewrite ?(subn0,sub0n,add0n,addn0,subr0,sub0r).
  + case: (leqP a b); [move=> lxy | move/ltnW=> lxy].
      move:(lxy); rewrite -subn_eq0; move/eqP->.
      rewrite sub0r -{2}(subnK lxy) natrD.
      by rewrite -opprB -addrA subrr addr0.
    move:(lxy); rewrite -subn_eq0; move/eqP->.
    by rewrite subr0 -{2}(subnK lxy) natrD -addrA subrr addr0.
  + by rewrite opprK natrD.
  + by rewrite natrD opprD.
  + case: (leqP a b); [move=> lxy | move/ltnW=> lxy].
      move:(lxy); rewrite -subn_eq0; move/eqP->.
      rewrite subr0 -{2}(subnK lxy) natrD.
      by rewrite opprD opprB addrA addNr add0r opprK.
    move:(lxy); rewrite -subn_eq0; move/eqP->.
    rewrite sub0r opprK -{2}(subnK lxy) natrD. 
    by rewrite opprD -addrA addNr addr0.
elim/relPN=> a; elim/relPN=> b /=;
rewrite ?(subn0,sub0n,muln0,addn0,add0n,subr0,sub0r).
+ by rewrite natrM.
+ by rewrite natrM mulrN.
+ by rewrite natrM mulNr.
+ by rewrite natrM mulrN mulNr opprK.
Qed.
Hint Resolve zprojrM.


Lemma zscalerA : forall a b m, zscaler  a (zscaler b m) = zscaler (a * b) m.
Proof. 
by move=> a b m; rewrite /zscaler mulrA; congr (_*_); rewrite ringM_mul.
Qed.

Lemma zscale1r :  left_id 1 zscaler.
Proof. by move=> a; rewrite /zscaler /= ringM_1 // mul1r. Qed.

Lemma zscalerDrM : forall a, {morph zscaler a : m n / m + n}.
Proof. by move=> a m n; rewrite /zscaler mulrDr. Qed.

Lemma zscalerDzM : forall m,  {morph zscaler^~ m : a b / a + b}.
Proof. by move=> m a b; rewrite /zscaler ringM_add // mulrDl. Qed.

Definition Z_LmoduleMixin := LmodMixin zscalerA zscale1r
zscalerDrM zscalerDzM.

End zprojR.


Section ORingSign.
Variable F : oIdomainType.
Implicit Types x y z t : F.

Open Scope ring_scope.
(* Canonical Structure F_Zmodule := Z_LmoduleMixin. *)

Definition signr x : relative := if x==0 then 0 else if 0 <= x then 1 else -1.

Definition absr x := (zprojr _ (signr x)) * x.

End ORingSign.

Section zprojp.

Variable p: nat.

Lemma zprojp_compat : \compat1_relative _
  (fun x => (inZp (x.1 + (p.-2.+2- x.2%%p.-2.+2))): 'Z_p).
Proof.
apply:compat1E=> x x'; rewrite !equivzP /equivz; move/eqP=>Px.
apply/val_eqP.
rewrite -(modn_add2l x.2).
rewrite -modn_addml addnC -addnA subnK; last by rewrite ltnW // ltn_pmod.
rewrite modn_addr addnA [x.2 + _]addnC -Px [x.1 + _]addnC -addnA.
by rewrite -modn_addml addnC -addnA subnK ?modn_addr // ltnW // ltn_pmod.
Qed.

Definition zprojp: relative-> 'Z_p := (qT_op1 zprojp_compat).

Lemma zprojp_morph: GRing.morphism zprojp.
Proof.
have F1: forall x, x %% p.-2.+2 <= p.-2.+2.
  by move=>*; rewrite ltnW // ltn_pmod.
split; first 2 last.
- rewrite /zprojp !qTE; apply/val_eqP=>/=;apply/eqP.
  by rewrite subn0 modn_addr.
- elim/relPN=>x; elim/relPN=>y;
  rewrite /zprojp !qTE; apply/val_eqP=>/=;apply/eqP;
  rewrite !subn0 ?sub0n !add0n ?addn0 ?modn_addr ?modn_add2m //;
  set q := p.-2.+2.
  - by apply sym_eq;apply/eqP; 
       rewrite -(modn_add2l ((q - y %% q) %% q))
                addnC -addnA subnK ?F1 // modn_addml addnA modn_addr 
               -modn_addmr addnC addnA  subnKC ?modn_addl // F1.
  - by apply/eqP; 
       rewrite -(modn_add2l ((x + y) %% q)) subnKC ?F1 //
                -[(x + _) %% _]modn_add2m modn_addml [_ %% _ + _]addnC 
                -addnA addnC addnA subnKC ?F1 // -addnA subnK ?modn_addl // F1.
  apply/eqP; 
    by rewrite addnC -(modn_add2l (x %% q)) addnA subnKC ?F1 //
               modn_addl addnA subnKC ?F1 //
               eq_sym modn_addl -(modn_add2l ((q - y %% q) %% q)) subnKC
               ?F1 // modn_addml -modn_addmr subnK // F1.
elim/relPN=>x; elim/relPN=>y;
  rewrite /zprojp !qTE; apply/val_eqP=>/=;apply/eqP;
  rewrite !subn0 ?sub0n !mul0n !muln0 !add0n ?addn0 ?mod0n ?subn0 
          !modn_addr modn_mul2m //; set q := p.-2.+2.
  - by apply/eqP; 
       rewrite -(modn_add2l ((x*y) %% q)) subnKC ?F1 //
              -modn_mulmr modn_addml -muln_addr subnKC ?F1 // modn_mull modnn.
  - by apply/eqP;
       rewrite -(modn_add2l ((x*y) %% q)) subnKC ?F1 //
               -modn_mulml modn_addml -muln_addl subnKC ?F1 //
               modn_mulr modnn.
by apply sym_eq;apply/eqP; 
   rewrite -(modn_add2l ((x %% q) * (q - y %% q))) -muln_addl subnKC ?F1 //
           modn_mulr -modn_add2m modn_mulml -[(_ * y)%%_]modn_mulmr modn_add2m
          -muln_addr subnK ?modn_mull // F1.
Qed.

Lemma zp_opp: forall x: 'Z_p, 
  x <> 0%R -> [(-x)%R]%z = ([p.-2.+2]%z - [x]%z)%R.
Proof.
move=> [x Hx] Dx.
have {Dx}F1: x <> 0  by move=> F1; case Dx; apply/val_eqP; apply/eqP.
apply/val_eqP; case: eqP=> /=; rewrite !sub0n !subn0 !addn0 !add0n;
  set k := p.-2.+2; rewrite modn_small;
   try (by have ->: x - k = 0 by apply/eqP; rewrite subn_eq0 ltnW);
   by rewrite -subn_gt0 subKn; [case: x {Hx}F1 |rewrite ltnW].
Qed.

Lemma zprojp0: zprojp 0%R = 0%R.
Proof. by apply/val_eqP=> /=; rewrite !subn0 modnn. Qed.

Hypothesis Hp: p > 1.

Lemma zprojp0P: forall x, 
  reflect (exists n: relative, x = (n * [p]%z)%R)
          (zprojp x == 0%R).
Proof.
move=> x; apply: (iffP eqP); last first.
  move=> [n ->].
  rewrite /zprojp !qTE; apply/val_eqP=> /=.
  rewrite !subn0 !muln0 addn0 /= Zp_cast // modn_mull subn0.
  by rewrite -modn_add2m modnn modn_mull mod0n.
elim/relPN: x=> x.
  rewrite /zprojp !qTE; move/val_eqP=>/=.
  rewrite Zp_cast // mod0n subn0 modn_addr.
  case/dvdnP=> n ->; exists [n]%z.
    apply/val_eqP=> /=.
    by rewrite !subn0 !sub0n !addn0 muln0 subn0 sub0n.
rewrite /zprojp !qTE; move/val_eqP=>/=.
rewrite Zp_cast // => Hp1.
suff: p %| x.
  case/dvdnP=> n ->; exists [-n]%z.
  apply/val_eqP=> /=.
  by rewrite !subn0 !sub0n muln0 subn0 sub0n.
have: p %| (p - x %% p) by done.
rewrite -eqn_mod_dvd.
rewrite modnn modn_small.
by rewrite /dvdn; move/eqP<-.
by rewrite ltn_mod; case: p Hp.
by rewrite ltnW //ltn_mod; case: p Hp.
Qed.

Lemma zprojp_mul0l: forall n, zprojp (n * [p]%z)%R = 0%R.
Proof. by move=> n; apply/eqP; apply/zprojp0P; exists n. Qed.

Lemma zprojp_mul0r: forall n, zprojp ([p]%z * n)%R = 0%R.
Proof.
by move=> n; apply/eqP; apply/zprojp0P; exists n; rewrite GRing.mulrC.
Qed.

Lemma expn_expr: forall i n: nat, [n ^ i]%z = ([n]%z ^+ i)%R.
Proof.
elim=> [|i Hrec] n; apply/val_eqP; rewrite  /= !subn0 !sub0n //.
rewrite GRing.exprS /= !subn0 !sub0n !mul0n !addn0.
move: (Hrec n); move/val_eqP=>/=; rewrite !subn0 !sub0n //.
case: sval=> x y; rewrite xpair_eqE; case/andP.
by move/eqP<-; move/eqP<-; rewrite muln0 sub0n subn0 expnS.
Qed.

End zprojp.

Notation "p %% n" := (zprojp n p).

Require Import prime poly.

Section Pol.
Variable pol : {poly relative}.

Variable p : nat.
Hypothesis primep: prime p.
Variable i : nat.
Hypothesis Hi: i > 0.

Let Hpi: p ^ i > 1.
Proof. by rewrite -[1](exp1n i) ltn_exp2r // prime_gt1. Qed.
Let Hpi1: p ^ i.+1 > 1.
Proof.
apply: (leq_trans (prime_gt1 primep)).
by rewrite -{1}[p]muln1 expnS leq_pmul2l ltnW // prime_gt1.
Qed.

Hypothesis a: relative.
Hypothesis P: {poly relative}.

Let Pia := (P.[a])%R %% p^i.
Let Pa' := ((deriv P).[a])%R %% p.

Hypothesis Epia: Pia  = 0%R.
Hypothesis Ep'a: Pa' <> 0%R.

Lemma hensel: (P.[a - (P.[a] * [Pa'^-1]%z)])%R %% p^i.+1  = 0%R.
Proof.
rewrite nderiv_taylor; last by apply: mulzC.
move/eqP: Epia; case/(zprojp0P Hpi)=> n Hn.
case HP: (size P)=> [|[|s]]; first by rewrite big_ord0 zprojp0.
case: Ep'a. 
  have F1: size P <= 1 by rewrite HP.
  by rewrite /Pa' (size1_polyC F1) derivC horner0 zprojp0.
rewrite 2!big_ord_recl nderivn0 nderivn1 GRing.expr0 GRing.expr1 GRing.mulr1
        Hn GRing.addrA (GRing.ringM_add (zprojp_morph (p^ i.+1))).
set f := (n * [p ^ i]%z)%R.
rewrite -GRing.mulrN GRing.mulrA [(_ * f)%R]GRing.mulrC
        -GRing.mulrA -{1}[f](GRing.mulr1) -GRing.mulrDr.
have: (1 + (deriv P).[a] * - [Pa'^-1]%z)%R %% p == 0%R.
  move: Ep'a; rewrite/Pa'.
  elim/relPM : (horner _) => x Hx.
    rewrite /zprojp !qTE /= !sub0n !subn0 !muln0 !mul0n !add0n sub0n subn0.
    apply/eqP;apply/val_eqP=>/=.
    set k := p.-2.+2.
    have->: inZp (x + k) = (inZp x: 'Z_p).
      by apply/val_eqP=>/=; rewrite modn_addr.
    rewrite !addn0 -modn_mulml.
    have: ((inZp x: 'Z_p) * (inZp x)^-1)%R = 1%R.
      apply: GRing.divrr=> //.
      rewrite /GRing.unit /= -/k prime_coprime //.
        apply/negP=> Hh; case Hx; apply/val_eqP=>/=.
        rewrite subn0 sub0n mod0n subn0 modn_addr.
        by move: Hh; rewrite /dvdn modn_mod.
      by move: primep; rewrite /k; case: p => [|[|p1]].
    move/val_eqP=> /=; rewrite -/k; move/eqP=> ->.
    by rewrite [(1 %% k)%N]modn_small // subnKC // modnn.
  move=> H; rewrite (GRing.ringM_opp (zprojp_morph p)) GRing.invrN.
  rewrite (@zp_opp p ((zprojp p x)^-1)%R).
    rewrite GRing.mulrN GRing.mulNr GRing.opprK GRing.mulrDr
            [(x * _ + _)%R]GRing.addrC GRing.addrA
            (GRing.ringM_add (zprojp_morph p)).
    have F1: p.-2.+2 = p by rewrite Zp_cast // prime_gt1.
    rewrite {3}F1 zprojp_mul0l // ?prime_gt1 // GRing.addr0.
    apply Hx=> Hy; case H.
    by rewrite (GRing.ringM_opp (zprojp_morph p)) Hy // GRing.oppr0.
  apply/eqP; apply: GRing.invr_neq0; apply/eqP=> Hy; case H.
  by rewrite (GRing.ringM_opp (zprojp_morph p)) Hy // GRing.oppr0.
case/(zprojp0P (prime_gt1 primep))=> k ->.
have->: (f * (k * [p]%z) = [p ^ i.+1]%z * (n * k))%R.
  rewrite /f !expn_expr GRing.exprS.
  rewrite !GRing.mulrA GRing.mulrC !GRing.mulrA; congr (_ * _)%R.
  rewrite -!GRing.mulrA; congr (_ * _)%R; first by exact: GRing.mulrC.
  rewrite zprojp_mul0r // GRing.add0r  (GRing.ringM_sum (zprojp_morph _))
          (eq_bigr (fun i => 0%R)).
  by rewrite GRing.Theory.sumr_const GRing.mul0rn.
move=> j _; set v1 := (_.[a])%R.
rewrite /f [(n * _)%R]GRing.mulrC -[(([_]%z * _) * _)%R]GRing.mulrA.
set v2 := (n * _ )%R.
by rewrite GRing.mulrC [(_ * v2)%R]GRing.mulrC GRing.exprS -2!GRing.mulrA 
           GRing.mulrC GRing.exprS [(v2 * _)%R]GRing.mulrC !GRing.mulrA
           expn_expr -GRing.exprD -{4}(ltn_predK Hi) -addSnnS 
           GRing.exprD -!GRing.mulrA -!expn_expr zprojp_mul0r.
Qed.

End Pol.



