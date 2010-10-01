(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
Require Import ssralg poly polydiv zmodp fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.

Reserved Notation  "`| x |" (at level 0, x at level 99, format "`| x |").
Reserved Notation "x <= y :> T" (at level 70, y at next level).
Reserved Notation "x >= y :> T" (at level 70, y at next level).
Reserved Notation "x < y :> T" (at level 70, y at next level).
Reserved Notation "x > y :> T" (at level 70, y at next level).
Reserved Notation "'\s' x" (at level 20, x at next level).
Reserved Notation "s ?* x" (at level 20, right associativity, format "s ?* x").

Section ExtraSsrAlg.

Variable R : ringType.
Implicit Types x y z t : R.

Lemma eqr_opp : forall x y, (x == y) = (-x == -y).
Proof. by move=> x y; rewrite -subr_eq0 opprK addrC subr_eq0 eq_sym. Qed.

Lemma eqr_oppC : forall x y, (x == -y) = (-x == y).
Proof. by move=> x y; rewrite eqr_opp opprK. Qed. 

Lemma add2r : forall x, x + x = 2%:R * x.
Proof. by move=> x; rewrite -{1}[x]mulr1n -mulrSr mulr_natl. Qed.

End ExtraSsrAlg.

Module OrderedRing.

Record mixin_of (R : ringType) := Mixin {
  le : rel R;
  _ : antisymmetric le;
  _ : transitive le;
  _ : total le;
  _ : forall z x y, le x y -> le (x + z) (y + z);
  _ : forall x y, le 0%R x -> le 0%R y -> le 0%R (x * y)%R
}.


Local Notation ring_mixin_of T b := (mixin_of (@GRing.Ring.Pack T b T)).

Section Generic.

(* The BF-prefixed bound variable names are a backward-compatibility patch
   between coq-8.2-1 and coq-trunk r12661 and later 
*)

(* Implicits *)
Variables (BFtype base_type : Type) (BFclass_of base_of : Type -> Type).
Variable to_ring : forall T, base_of T -> GRing.Ring.class_of T.
Variable base_sort : base_type -> Type.

(* Explicits *)
Variable Pack : forall T, BFclass_of T -> Type -> BFtype.
Variable Class : forall T b, ring_mixin_of T (to_ring b) -> BFclass_of T.
Variable base_class : forall bT, base_of (base_sort bT).

(* Definition gen_pack T := *)
(*   fun bT b & phant_id (base_class bT) b => *)
(*   fun fT m & phant_id (Finite.class fT) (Finite.Class m) => *)
(*   Pack (@Class T b m) T. *)

Definition gen_pack T b0 (m0 : ring_mixin_of T b0) :=
  fun bT b & phant_id (base_class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

End Generic.

Implicit Arguments
   gen_pack [BFtype base_type BFclass_of base_of to_ring base_sort].

Module IntegralDomain.

Record class_of (R : Type) : Type := Class {
  base :> GRing.IntegralDomain.class_of R;
  ext :> mixin_of (GRing.Ring.Pack base R)
}.

Record type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type }.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.
Definition pack := gen_pack Pack Class GRing.IntegralDomain.class.

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Coercion ringType cT := GRing.Ring.Pack (class cT) cT.
Coercion comRingType cT := GRing.ComRing.Pack (class cT) cT.
Coercion unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Coercion comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Coercion idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.

End IntegralDomain.

Bind Scope ring_scope with IntegralDomain.sort.
Canonical Structure IntegralDomain.eqType.
Canonical Structure IntegralDomain.choiceType.
Canonical Structure IntegralDomain.zmodType.
Canonical Structure IntegralDomain.ringType.
Canonical Structure IntegralDomain.comRingType.
Canonical Structure IntegralDomain.unitRingType.
Canonical Structure IntegralDomain.comUnitRingType.
Canonical Structure IntegralDomain.idomainType.

Open Scope ring_scope.

Definition ler (R : IntegralDomain.type) : rel R := le (IntegralDomain.class R).
Notation "<=%R" := (@ler _) : ring_scope.
Notation "x <= y" := (ler x y) : ring_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T)) : ring_scope.
Notation "x >= y" := (y <= x) (only parsing) : ring_scope.
Notation "x >= y :> T" := ((x : T) >= (y : T)) : ring_scope.

Definition ltr (R : IntegralDomain.type) : rel R := fun x y => ~~(x >= y :> R).
Notation "<%R" := (@ltr _) : ring_scope.
Notation "x < y"  := (ltr x y) : ring_scope.
Notation "x < y :> T" := ((x : T) < (y : T)) : ring_scope.
Notation "x > y"  := (y < x) (only parsing) : ring_scope.
Notation "x > y :> T" := ((x : T) > (y : T)) : ring_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : ring_scope.
Notation "x < y <= z" := ((x < y) && (y <= z)) : ring_scope.
Notation "x <= y < z" := ((x <= y) && (y < z)) : ring_scope.
Notation "x < y < z" := ((x < y) && (y < z)) : ring_scope.


Definition signr (R : IntegralDomain.type) (x : R) : 'F_3 := 
  if x == 0 then 0 else if 0 <= x then 1 else -1.
Notation "'\s' x" := (@signr _ x).
Definition smul (R : IntegralDomain.type) (s : 'F_3) (x : R) := 
  if s == 0 then 0 else if s == 1 then x else -x.
Notation "s ?* x" := (@smul _ s x).
Definition absr (R : IntegralDomain.type) (x : R) := (\s x) ?* x.
Notation "`| x |" := (@absr _ x) : ring_scope.

Record lter (R : IntegralDomain.type) := Lter {
  lter_op :> rel R ;
  _ : (lter_op =2 (@ler R)) \/ (lter_op =2 (@ltr R))
}.
Lemma lterP : forall R (c : lter R), (c =2 (@ler R)) \/ (c =2 (@ltr R)).
Proof. by move=> ? []. Qed.
Canonical Structure ler_lterS R := @Lter R _ (or_introl _ (fun x y => refl_equal (_ x y))).
Canonical Structure ltr_lterS R := @Lter R _ (or_intror _ (fun x y => refl_equal (_ x y))).

Definition lte_let R (c : lter R) (x y : R) := ~~ (c y x). 

Lemma lte_letP : forall R (c : lter R) x y, ~~ (c x y) = (lte_let c) y x.
Proof. done. Qed.

Lemma lte_let_lterP : forall R (c: lter R),
  ((lte_let c) =2 (@ler R)) \/ ((lte_let c) =2 (@ltr R)).
Proof.
by rewrite /lte_let => R [o [] oP] /=; [right|left] => x y; rewrite oP // negbK.
Qed.

Canonical Structure lte_let_lter R (c : lter R) := Lter (lte_let_lterP c).

Module IntegralDomainTheory.

Section IntegralDomainTheory.

Variable R : IntegralDomain.type.
Implicit Types x y z t : R.

Lemma ler_anti : antisymmetric (@ler R). Proof. by case R => T [? []]. Qed.
Lemma ler_trans : transitive (@ler R). Proof. by case R => T [? []]. Qed.
Lemma ler_total : total (@ler R). Proof. by case R => T [? []]. Qed.
Lemma lerr : reflexive (@ler R).
Proof. by move=> x; rewrite -[_<=_]orbb; apply: ler_total. Qed.
Hint Resolve lerr.

Lemma lerNgt : forall x y, ~~(x <= y) = (x > y). Proof. done. Qed.
Lemma ltrr : irreflexive (@ltr R). Proof. by move=> x; rewrite /ltr lerr. Qed.

Definition lterr := (lerr, ltrr).

Lemma ltrNge : forall x y, ~~(x < y) = (x >= y).
Proof. by move=> x y; rewrite negbK. Qed.

Lemma ler_add2l : forall z x y, ((x + z) <= (y + z)) = (x <= y).
Proof. 
have w : forall z x y, x <= y -> (x + z) <= (y + z).
  by case R => T [? []].
move=> z x y; apply/idP/idP; last exact: w.
by move/(w (-z)); rewrite -!addrA subrr !addr0.
Qed.
Lemma lter_add2l : forall  z x y (c: lter R), (c (x + z) (y + z)) = (c x y).
Proof. by move=> x y z [c /= [] ec]; rewrite ?ec -?lerNgt ?ler_add2l. Qed.

Lemma lter_add2r : forall  z x y (c: lter R), c (z + x) (z + y) = c x y.
Proof. by move=> z x y c; rewrite ![z+_]addrC; exact: lter_add2l. Qed.

Lemma subr_gte0 : forall  x y (c: lter R), c 0 (y - x) = c x y.
Proof. by move=> x y c; rewrite -(lter_add2l x) add0r subrK. Qed.
Lemma subr_lte0 : forall  x y (c: lter R), c (y - x) 0 = c y x.
Proof. by move=> x y c; rewrite -(lter_add2l x) add0r addrNK. Qed.

Lemma lter_opp2 : forall  x y (c: lter R), c y x = c (-x) (-y).
Proof. by move=> c x y; symmetry; rewrite -subr_gte0 opprK addrC subr_gte0. Qed.

Lemma lter_oppr : forall  x y (c: lter R), c x (-y) = c y (-x).
Proof. by move=> x y c; rewrite lter_opp2 opprK. Qed.
Lemma lter_oppl : forall  x y (c: lter R), c (-x) y = c (-y) x.
Proof. by move=> x y c; rewrite lter_opp2 opprK. Qed.

Lemma oppr_gte0 : forall  x (c: lter R), c 0 (-x) = c x 0.
Proof. by move=> x c; rewrite lter_opp2 oppr0 opprK. Qed.
Lemma oppr_lte0 : forall  x (c: lter R), c (-x) 0 = c 0 x.
Proof. by move=> x c; rewrite lter_opp2 oppr0 opprK. Qed.
Definition oppr_cp0 := (oppr_gte0, oppr_lte0).

Lemma ltrW : forall x y, x < y -> x <= y.
Proof. by move=> x y; rewrite/ltr; case/orP:(ler_total x y)=> ->. Qed.
Hint Resolve ltrW.

Lemma eqr_le : forall x y, (x == y) = (x <= y <= x).
Proof.
move=> x y; apply/idP/idP; last by move/ler_anti->.
by move/eqP->; rewrite lerr.
Qed.

Lemma ler_lt : forall x y, x != y -> x <= y = (x < y).
Proof.
rewrite/ltr=> x y xy; apply/idP/idP; last exact: ltrW.
case lyx : (y<=x)=> // lxy; apply: contra xy=> _.
by rewrite eqr_le lxy lyx.
Qed.

Lemma ler_nlt : forall x y, x <= y = ~~(y < x).
Proof. by move=> x y; apply: negbRL. Qed.

Lemma ltr_neqAle : forall x y, (x < y) = (x != y) && (x <= y).
Proof. 
rewrite/ltr=> x y; case exy: (_==_)=> /=.
  by rewrite (eqP exy) lerr.
by symmetry; rewrite ler_lt ?exy.
Qed.

Lemma ltrWN : forall x y, x < y -> x == y = false.
Proof. by move=> x y; rewrite ltr_neqAle; case/andP; move/negPf=> ->. Qed.
Hint Resolve ltrWN.

Definition ltrE x y (hxy : x < y) := (hxy, (ltrWN hxy), (ltrW hxy)).

Lemma ler_lte_trans : forall  y x z (c: lter R), x <= y -> c y z -> c x z.
Proof.
move=> y x z [c /= [] ec]; rewrite !ec; first exact: ler_trans.
by move=> lxy; apply: contra=> lzx; rewrite (ler_trans lzx).
Qed.

Lemma lter_le_trans : forall  y x z (c: lter R), c x y -> y <= z -> c x z.
Proof.
move=> y x z [c /= [] ec]; rewrite !ec; first exact: ler_trans.
by move=> lxy lyz; move: lxy; apply: contra=> lzx; rewrite (ler_trans _ lzx).
Qed.

Lemma lter_trans : forall  y x z (c: lter R), c x y -> c y z -> c x z.
Proof.
move=> y x z [c /= [] ec]; rewrite !ec; first exact: ler_trans. 
by move=> lxy; move/ler_lte_trans ->; rewrite // ltrE. 
Qed.

Lemma neqr_lt : forall x y, (x < y < x) = false.
Proof.
move=> x y. apply/negP; case/andP=> lxy lyx. 
by move: (lter_trans lxy lyx); rewrite /= ltrr.
Qed.

CoInductive le_xor_gtr (x y : R) : bool -> bool -> Set :=
  | LeNotGtr of x <= y : le_xor_gtr x y true false
  | GtrNotLe of y < x  : le_xor_gtr x y false true.

Lemma lerP : forall x y, le_xor_gtr x y (x <= y) (y < x).
Proof. 
by rewrite/ltr=> x y; case hxy: (_ <= _); constructor; rewrite /ltr ?hxy. 
Qed.

CoInductive ltr_xor_geq (x y : R) : bool -> bool -> Set :=
  | LtrNotGeq of x < y  : ltr_xor_geq x y false true
  | GeqNotLtr of y <= x : ltr_xor_geq x y true false.

Lemma ltrP : forall x y, ltr_xor_geq x y (y <= x) (x < y).
Proof. by move=> x y; case: (lerP y x); constructor. Qed.

CoInductive cparer x y : bool -> bool -> bool -> Set :=
  | CparerLt of x < y : cparer x y true false false
  | CparerGt of x > y : cparer x y false true false
  | CparerEq of x = y : cparer x y false false true.

Lemma ltrgtP : forall x y, cparer x y (x < y) (x > y) (x == y).
Proof.
move=> x y; case exy: (_==_); first by rewrite (eqP exy) lterr; constructor.
case: (ltrP y x); rewrite /ltr ler_lt ?exy //; last first.
  by rewrite/ltr=> lxy; rewrite lxy; constructor.
rewrite negbK; move=> lyx; rewrite lyx; constructor.
by rewrite ltr_neqAle lyx eq_sym exy.
Qed.

Lemma lergeP : forall x y, (x <= y) || (y <= x).
Proof. by move=> x y; case: lerP=> //; move/ltrW->. Qed. 

Lemma lter_add : forall  x y z t (c: lter R), c x y -> c z t -> c (x + z) (y + t).
Proof.
move=> x y z t c lxy.
rewrite -(lter_add2r y)=> lyzyt; apply: lter_trans lyzyt.
by rewrite lter_add2l.
Qed.

Lemma ler_lte_add : forall  x y z t (c: lter R), x <= y -> c z t -> c (x + z) (y + t).
Proof.
move=> x y z t [c /= [] ec]; rewrite !ec; first exact: lter_add.
move=> lxy; apply: contra; rewrite lter_opp2=> /= lxzyt.
have:= (lter_add lxy lxzyt).
by rewrite !oppr_add !addrA !subrr !sub0r -lter_opp2.
Qed.

Lemma lter_le_add : forall  x y z t (c: lter R), c x y -> z <= t -> c (x + z) (y + t).
Proof. 
move=> x y z t c lxy lzt; rewrite addrC [y+_]addrC; exact: ler_lte_add. 
Qed.

Lemma lter_addrA : forall  z x y (c: lter R), c x (y + z) = c (x - z)  y.
Proof. by move=> z x y c; rewrite -(@lter_add2l (-z)) -addrA subrr addr0. Qed.
Lemma lter_addlA : forall  z x y (c: lter R), c x (z + y) = c (x - z) y.
Proof. by move=> z x y c; rewrite addrC lter_addrA. Qed.
Lemma lter_subrA : forall  z x y (c: lter R), c x (y - z) = c (x + z) y.
Proof. by move=> z x y c; rewrite lter_addrA opprK. Qed.
Lemma lter_sublA : forall  z x y (c: lter R), c x (y - z) = c (z + x) y.
Proof. by move=> z x y c; rewrite lter_addrA addrC opprK. Qed.
Definition lter_subr c z x y := (esym (lter_addrA z x y c), lter_subrA z x y c).
Definition lter_subl c z x y := (esym (lter_addlA z x y c), lter_sublA z x y c).

(* Lemma lter_addl : forall  x y z (c: lter R), c 0 x -> c y z -> c y (x + z). *)
(* Proof. move=> c x y z h1 h2; rewrite -(add0r y); exact: lter_add. Qed. *)

(* Lemma lter_addr : forall  x y z (c: lter R), c 0 z -> c x y -> c x (y + z). *)
(* Proof. move=> c x y z h1 h2; rewrite -(addr0 x); exact: lter_add. Qed. *)

Lemma lter_addrr : forall  x y (c: lter R),  c y (y + x) = c 0 x.
Proof. by move=> x y c; rewrite -{1}(addr0 y) lter_add2r. Qed.

Lemma lter_addrl : forall  x y (c: lter R), c y (x + y) = c 0 x.
Proof. by move=> x y c; rewrite addrC lter_addrr. Qed.

Lemma lter_addll : forall  x y (c: lter R), c (x + y) y = c x 0.
Proof. by move=> x y c; rewrite -{2}(add0r y) lter_add2l. Qed.

Lemma lter_addlr : forall  x y (c: lter R), c (y + x) y = c x 0.
Proof. by move=> x y c; rewrite addrC lter_addll. Qed.

Lemma lter_le_addpl : forall  x y z (c: lter R), c 0 x -> y <= z -> c y (x + z).
Proof. by move=> x y z c h1 h2; rewrite (@ler_lte_trans z) // lter_addrl. Qed.

Lemma lter_le_addpr : forall  x y z (c: lter R), c 0 x -> y <= z -> c y (z + x).
Proof. by move=> x y z c h1 h2; rewrite addrC lter_le_addpl. Qed.

Lemma lter_addpr : forall  x y z (c: lter R), 0 <= x -> c y z -> c y (x + z).
Proof. by move=> x y z c h1 h2; rewrite (@lter_le_trans z) // lter_addrl. Qed.

Lemma lter_addpl : forall  x y z (c: lter R), 0 <= x -> c y z -> c y (z + x).
Proof. by move=> x y z c h1 h2; rewrite addrC lter_addpr. Qed.


Lemma neq_ltr : forall x y, (x != y) = (x < y) || (y < x).
Proof. by move=> *; rewrite eqr_le negb_and orbC. Qed.

Lemma ler_eqVlt : forall x y, (x <= y) = (x == y) || (x < y).
Proof. 
move=> x y. rewrite ltr_neqAle. 
by case exy: (_==_); rewrite ? (andbT,andbF) // (eqP exy) lerr.
Qed.

Lemma mulr_ge0pp : forall x y, 0 <= x -> 0 <= y -> 0 <= (x * y).
Proof. by case R => T [? []]. Qed.
Lemma mulr_gte0pp : forall  x y (c: lter R), c 0 x -> c 0 y -> c 0 (x * y).
Proof.
move=> x y [c /= [] ec]; rewrite !ec; first exact: mulr_ge0pp.
rewrite !ltr_neqAle ![0==_]eq_sym; case/andP=> x0 px; case/andP=> y0 py.
by rewrite mulf_neq0 //= mulr_ge0pp.
Qed.
Lemma mulr_gte0nn : forall  x y (c: lter R), c x 0 -> c y 0 -> c 0 (x * y).
Proof. by move=> x y c hx hy; rewrite -mulrNN mulr_gte0pp ?oppr_cp0. Qed.
Lemma mulr_lte0pn : forall  x y (c: lter R), c 0 x -> c y 0 -> c (x * y) 0.
Proof. by move=> x y c hx hy; rewrite -oppr_cp0 -mulrN mulr_gte0pp ?oppr_cp0. Qed.
Lemma mulr_lte0np : forall  x y (c: lter R), c x 0 -> c 0 y -> c (x * y) 0.
Proof. by move=> x y c hx hy; rewrite mulrC mulr_lte0pn. Qed.
Definition mulr_cp0p := (mulr_gte0pp, mulr_lte0pn).
Definition mulr_cp0n := (mulr_gte0nn, mulr_lte0np).

Lemma ler01 : 0 <= 1 :> R.
Proof. 
case/orP:(ler_total 0 1); first done.
rewrite lter_opp2 oppr0=> l0m.
by move: (mulr_gte0pp l0m l0m); rewrite mulrN mulr1 opprK.
Qed.

Lemma ltr01 : 0 < 1 :> R.
Proof. by rewrite -ler_lt ?ler01 // eq_sym oner_eq0. Qed.

Lemma lter01 : forall c : lter R, c 0 1.
Proof. by case=> c /= [] ->; rewrite ?ltr01 ?ler01. Qed.

Lemma lter_mulpr : forall z x y (c: lter R), c 0 z -> c x y -> c (x * z) (y * z).
Proof.
move=> z x y c zp lxy; rewrite -subr_gte0 -mulr_subl.
by apply: mulr_gte0pp; rewrite ?subr_gte0.
Qed.
Lemma lter_mulpl : forall  z x y (c: lter R), c 0 z -> c x y -> c (z * x) (z * y).
Proof. by move=> z x y c *; rewrite ![z*_]mulrC lter_mulpr. Qed.
Lemma lter_mulnr : forall  z x y (c: lter R), c z 0 -> c x y -> c (y * z) (x * z).
Proof. by move=> z x y c zn lxy; rewrite lter_opp2 -!mulrN lter_mulpr// oppr_cp0. Qed.
Lemma lter_mulnl : forall  z x y (c: lter R), c z 0 -> c x y -> c (z * y) (z * x).
Proof. by move=> z x y c zn lxy; rewrite lter_opp2 -!mulNr lter_mulpl// oppr_cp0. Qed.
Definition lter_mulp z x y (c: lter R) (hz : c 0 z) (hxy : c x y) := 
  (lter_mulpr hz hxy, lter_mulpl hz hxy).
Definition lter_muln z x y (c: lter R) (hz : c z 0) (hxy : c x y) := 
  (lter_mulnr hz hxy, lter_mulnl hz hxy).

Lemma gtf0Sn : forall n, 0 < (n.+1)%:R :> R.
Proof.
elim=> [|n ihn]; first by rewrite ltr01.
by rewrite -addn1 natr_add mulr1n (lter_trans ihn)// -lter_subl//= subrr ltr01.
Qed.

Lemma lter_le : forall  (c: lter R) x y, c x y -> x <= y.
Proof. by move=> [c /= [] ec] x y; rewrite ec//; move/ltrW. Qed.

Lemma ltr_lte : forall  x y (c: lter R), x < y -> c x y.
Proof. by move=> x y [c /= [] ec]; rewrite ec; first move/ltrW. Qed.

Lemma gtef0Sn : forall  n (c: lter R), c 0 (n.+1)%:R.
Proof. by move=> n c; rewrite ltr_lte// gtf0Sn. Qed.

Definition null_char := forall n : nat, (n.+1)%:R == 0 :> R = false.
Lemma charor : null_char.
Proof. by move=> n; rewrite eq_sym ltrE// gtf0Sn. Qed.

(* signr section *)

Lemma signr_cp0 : forall x, 
  ((\s x == 1) = (0 < x)) *
  ((\s x == -1) = (0 > x)) *
  ((\s x == 0) = (x == 0)).
Proof.
move=> x; rewrite /signr; case: ltrgtP=> //; last by move/ltrW->.
by move/negPf->.
Qed.

Lemma gtr0_sign : forall x, 0 < x -> \s x = 1.
Proof. by move=> x hx; apply/eqP; rewrite signr_cp0. Qed.
Lemma ltr0_sign : forall x, x < 0 -> \s x = -1.
Proof. by move=> x hx; apply/eqP; rewrite signr_cp0. Qed.
Lemma signr0 : \s (0 : R) = 0. Proof. by rewrite /signr eqxx. Qed.
Lemma signr1 : \s (1 : R) = 1. Proof. by rewrite /signr oner_eq0 ler01. Qed.

Lemma signr_opp : forall x, \s (-x) = -\s x.
Proof.
move=> x; case: (ltrgtP x 0)=> hx; last by rewrite hx !(oppr0,signr0). 
  by rewrite gtr0_sign ?oppr_cp0// ltr0_sign// opprK.
by rewrite ltr0_sign ?oppr_cp0// gtr0_sign.
Qed.

Lemma inF3P : (forall s : 'F_3, [\/ s = 0,  s = 1 | s = -1]).
Proof. 
move=> s; suff : [|| s == 0,  s == 1 | s == -1].
  by case/or3P; move/eqP->; [constructor | constructor 2 | constructor 3 ].
by case:s ; elim=> //=; elim=> //=; elim. 
Qed.

Lemma mulss : forall s : 'F_3, s * s = (s != 0)%:R.
Proof. by move=> s; case: (inF3P s)=> -> //=; rewrite ?mulr0// mulrNN. Qed.

Lemma muls_eqA : forall (s sa sb : 'F_3), s != 0 -> 
  (sa * sb == s) = ((sa * s == sb) && (sb != 0)).
Proof.
move=> s sa sb.
by case: (inF3P s)=> ->; case: (inF3P sa)=> ->; case: (inF3P sb)=> ->.
Qed.

(* smul section *)

Lemma smulNr : forall s x, - s ?* x = (-s) ?* x.
Proof. by move=> s x; case: (inF3P s)=> ->; rewrite ? (opprK,oppr0). Qed.

Lemma smulrN : forall s x, - (s ?* x) = s ?* (-x).
Proof. by move=> s x; case: (inF3P s)=> -> /=; rewrite ?oppr0. Qed.

Lemma smulrNN : forall s x, (s ?* x) = (-s) ?* (-x).
Proof. by move=> s x; rewrite -smulNr -smulrN opprK. Qed.

Lemma smulA : forall s s' x, s ?* (s' ?* x) = (s*s')?* x.
Proof.
by rewrite /smul=> s s' x; case: (inF3P s)=> ->; case: (inF3P s')=> ->;
rewrite //= ? (opprK, oppr0).
Qed.

Lemma addr_smul : forall s s' x y, s != 0 -> 
    s ?* x + s' ?* y = s ?* (x + (s*s') ?* y).
Proof.
move=> s; case: (inF3P s)=> -> //= s' x y _; first by rewrite mul1r.
by rewrite [(-1)?*(_+_)]oppr_add mulN1r smulNr opprK.
Qed.

Lemma smul_add : forall s x y, s ?* (x + y) = s ?* x + s ?* y.
Proof.
move=> s; case: (inF3P s)=> -> x y //=; first by rewrite add0r.
by rewrite [(-1)?*_]oppr_add.
Qed.

Lemma smulr_mul : forall s x y, s ?* (x * y) = (s ?* x) * y.
Proof. by move=> s x y; case: (inF3P s)=> -> //=; rewrite ?mul0r// mulNr. Qed.

Lemma smul1_eq0 : forall s, ((s ?* 1) == 0 :> R) = (s == 0).
Proof. 
move=> s; case: (inF3P s)=> ->; rewrite ?eqxx ?oner_eq0//.
by rewrite -!eqr_oppC !oppr0 !oner_eq0.
Qed.

Lemma signr_smul : forall s x, \s (s ?* x) = s * \s x.
Proof.
move=> s x; case: (inF3P s)=> ->; rewrite ? (signr0,mul0r,mul1r) //.
by rewrite signr_opp mulN1r.
Qed.

Lemma smul_exp : forall s x n, (s ?* x)^+n.+1 = (s ^+ n.+1) ?* (x ^+ n.+1).
Proof.
move=> s x n; case: (inF3P s)=> ->; first by rewrite ![0^+_.+1]exprS !mul0r.
  by rewrite exp1rn.
rewrite [_^+_]exprN -![(-1)^+n.+1]signr_odd.
by case: (odd n.+1); rewrite !(expr0,expr1) !(mulNr,mul1r).
Qed.


(* absr section *)

Lemma absrP : forall x, `|x| = \s x ?* x.
Proof. done. Qed.

Lemma absr0 : `|0| = 0 :> R.
Proof. by rewrite /absr /signr eqxx. Qed.

Lemma absr_opp : forall x, `| -x | = `|x|.
Proof. by move=> x; rewrite /absr signr_opp -smulrNN. Qed.

Lemma ger0_abs : forall x, (x >= 0) -> `|x| = x.
Proof.
move=> x; rewrite /absr ler_eqVlt; case/orP=> hx; last by rewrite gtr0_sign.
by rewrite -(eqP hx) signr0.
Qed.
Definition gtr0_abs x (hx : x > 0) := ger0_abs (ltrW hx). 

Lemma ler0_abs : forall x, (x <= 0) -> `|x| = -x.
Proof.
move=> x hx; rewrite -{1}[x]opprK absr_opp //.
by apply:ger0_abs; rewrite oppr_cp0.
Qed.
Definition ltr0_abs x (hx : x < 0) := ler0_abs (ltrW hx). 

Lemma absr_idVN : forall x, (`|x| = x) \/ (`|x| = -x).
Proof.
move=> x; case/orP:(lergeP x 0); last by move/ger0_abs->; constructor.
by move/ler0_abs->; constructor 2.
Qed.

Lemma absr_ge0 : forall x, 0 <= `|x|.
Proof.
move=> x; case: (lerP x 0)=> hx; last by rewrite ger0_abs ltrW.
by rewrite ler0_abs // oppr_cp0.
Qed.
Hint Resolve absr_ge0.

Lemma smul_abs_id : forall x, x = (\s x) ?* `|x|.
Proof.
move=> x; case: (ltrgtP x 0)=> hx; last by rewrite hx absr0 signr0.
  by rewrite ltr0_sign// ltr0_abs// [(-1)?*_]opprK.
by rewrite gtr0_sign// gtr0_abs.
Qed.

Lemma absr_eq0 : forall x, (`|x| == 0) = (x == 0).
Proof.
move=> x; case: (ltrgtP x)=> hx; last by rewrite hx absr0 eqxx.
  by rewrite ltr0_abs// oppr_eq0 ltrE.
by rewrite gtr0_abs// eq_sym ltrE.
Qed.

Lemma absr_lt0 : forall x, `|x| < 0 = false.
Proof. by move=> x; apply/negP; apply/negP. Qed.

Lemma absr_le0 : forall x, (`|x| <= 0) = (x == 0).
Proof.
move=> x; rewrite -absr_eq0; case hx:(_==_).
  by move/eqP:hx->; rewrite lerr.
by rewrite ler_lt ?absr_lt0 ?hx.
Qed.

Lemma absr_gt0 : forall x, (`|x| > 0) = (x != 0).
Proof. by move=> x; rewrite /ltr absr_le0. Qed.

Lemma absr1 : `|1| = 1 :> R.
Proof. by rewrite ger0_abs// ler01. Qed.

Definition absrE x := (absr0, absr1, absr_ge0, absr_eq0, absr_lt0, absr_le0, absr_gt0).

Lemma absr_subC : forall x y, `|x - y| = `|y - x|.
Proof. by move=> x y; rewrite -oppr_sub absr_opp. Qed.

Lemma lter_addr_transl : forall  x y z t (c: lter R), c x y -> c (z + y) t -> c (z + x) t.
Proof.
by move=> c x y z t lxy lyzt; apply: lter_trans lyzt; rewrite lter_add2r.
Qed. 
Lemma lter_addl_transl : forall  x y z t (c: lter R), c x y -> c (y + z) t -> c (x + z) t.
Proof. move=> x y z t c; rewrite ![_+z]addrC; exact: lter_addr_transl. Qed.

Lemma lter_addr_transr : forall  x y z t (c: lter R), c x y -> c z (t + x) -> c z (t + y).
Proof.
by move=> x y z t c lxy lztx; apply: (lter_trans lztx); rewrite lter_add2r.
Qed.
Lemma lter_addl_transr : forall  x y z t (c: lter R), c x y -> c z (x + t) -> c z (y + t).
Proof. move=> x y z t c; rewrite ![_+t]addrC; exact: lter_addr_transr. Qed.

Lemma absr_add_le : forall x y, `| x + y | <= `|x| + `|y|.
Proof.
move=> x; wlog : x / (x > 0)=> [hxp | xp] y.
  case: (ltrgtP x 0)=> [xn|xp|->]; do ?exact: hxp; last by rewrite absr0 !add0r.
  rewrite -absr_opp -(absr_opp x) -(absr_opp y) oppr_add.
  by apply: hxp; rewrite oppr_cp0.
case: (ltrgtP y 0)=> hy; last by rewrite hy absr0 !addr0. 
  case: (lerP 0 (x+y))=> lnyx; [rewrite ger0_abs// | rewrite ler0_abs ?ltrW//];
  rewrite ger0_abs ?ler0_abs ?ltrW// -subr_gte0/= addrAC (opprK,oppr_add). 
    by rewrite addrA subrr sub0r -oppr_add add2r oppr_cp0/= mulr_cp0p//= gtf0Sn.
  by rewrite -!addrA subrr addr0 add2r mulr_cp0p//= gtf0Sn.
by rewrite !ger0_abs// ?ltrW// lter_addpl// ltrE.
Qed.

Lemma subr_abs_le : forall x y, `|x| - `|y| <= `| x + y |.
Proof.
move=> x y; rewrite -{1}[x](subr0) -[0](subrr y) oppr_sub addrA.
apply: (lter_addl_transl (absr_add_le _ _))=> //=. 
by rewrite absr_opp -addrA subrr addr0.
Qed.


Lemma absr_lte : forall  x y (c: lter R), 0 <= y -> (c `|x| y) = (c (-y) x && c x y).
Proof.
move=> x y c hy; wlog : x / x >= 0=> [hxp|xp].
  case: (lerP x 0) => hx; last by rewrite hxp// ?ltrW.
  by rewrite -absr_opp lter_oppl andbC [c x y]lter_opp2 hxp// oppr_cp0.
rewrite ger0_abs//; apply/idP/idP=> [cxy|]; last by case/andP.
rewrite cxy andbT lter_oppl//= (@ler_lte_trans x)//.
by rewrite -subr_gte0//= opprK add2r mulr_cp0p//= gtef0Sn.
Qed.

Lemma lter_abs : forall  x y (c: lter R), c `|x| y -> c x y.
Proof.
move=> x y c h; move: (h); rewrite absr_lte; first by case/andP.
by rewrite (@lter_le c)// (ler_lte_trans _ h).
Qed.

Lemma absr_abs_le : forall x y, `| `|x| - `|y| | <= `| x + y |.
Proof.
move=> x y; rewrite absr_lte// lter_oppl//=.
by rewrite oppr_sub {1}[_+y]addrC !subr_abs_le.
Qed.

Lemma absr_sub_lte : forall  z x y (c: lter R), 0 <= z -> 
  (c `|x - y| z) = (c (y - z) x && c x (y + z)).
Proof. by move=> z x y c hz; rewrite absr_lte// !lter_subl. Qed.

Lemma absr_le_lt0: forall x y, y < 0 -> (`|x| <= y = false).
Proof.
move=> x y hy; apply/negP; apply/negP; move:(absr_ge0 x).
by rewrite lerNgt; move/(lter_le_trans _)->.
Qed.

Lemma absr_lt_le0 : forall x y, y <= 0 -> (`|x| < y = false).
Proof.
move=> x y hy; apply/negP; apply/negP; move: (absr_ge0 x).
by move/(lter_trans _)->.
Qed.

Lemma absr_lte0 : forall  x y (c: lter R),  ~~(c 0 y) -> (c `|x| y = false).
Proof.
move=> x y [c /= [] ec]; rewrite !ec (ltrNge,lerNgt)=> hxy;
by rewrite (absr_le_lt0,absr_lt_le0).
Qed.

Lemma absr_smul : forall s x, s != 0 -> `|s ?* x| = `|x|.
Proof.
move=> s x; case: (ltrgtP x 0)=> hx; case: (inF3P s)=> -> //= _;
by rewrite absr_opp.
Qed.

Definition minr x y := if x<=y then x else y.

Lemma ltr_minr : forall x y z, (minr x y > z) = (x > z) && (y > z).
Proof.
rewrite /minr=> x y z; case: (lerP x y)=> lxy; apply/idP/idP.
- by move=> lzx; rewrite lzx (lter_le_trans _ lxy).
- by case/andP=> ->.
- by move=> lzy; rewrite lzy (lter_trans _ lxy).
- by case/andP=> _ ->.
Qed.

Lemma absfP : forall x, (x >= 0) = (`|x| == x).
Proof.
move=> x; case: lerP=> lx; first by move/ger0_abs:(lx)->; rewrite eqxx.
move/ltr0_abs:(lx)->; rewrite -eqr_oppC -subr_eq0 opprK add2r; symmetry.
by rewrite mulf_eq0 (ltrE lx) charor.
Qed.

Lemma absfn : forall x, (x <= 0) = (`|x| == -x).
Proof. move=> x; rewrite -oppr_cp0 -absr_opp; exact: absfP. Qed.


Lemma absf_lte : forall  x y (c: lter R), (c `|x| y) = (c (-y) x && c x y).
Proof.
move=> x y c; case: (lerP 0 y); first exact: absr_lte.
move=> hy. rewrite absr_lte0 ? (ltrE hy) //; last first.
  by apply/negP; move/lter_le; rewrite -ltrNge hy.
symmetry; apply/negP; case/andP=> hNyx hxy.
move: (lter_le_trans (lter_trans hNyx hxy) (ltrW hy)).
by rewrite oppr_cp0; move/lter_le; rewrite -ltrNge hy.
Qed.

Lemma absf_sub_lte : forall z x y (c : lter R), (c `|x - y| z) = (c (y - z) x && c x (y + z)).
Proof. by move=> z x y c; rewrite absf_lte // !lter_subl. Qed.

Lemma ltef_mulpr : forall  z x y (c: lter R), 0 < z ->  (c (x * z) (y * z)) = (c x y).
Proof.
move=> z x y c zp; apply/idP/idP; first do [apply: contraLR; rewrite !lte_letP];
by apply: lter_mulpr; rewrite ltr_lte.
Qed.
Lemma ltef_mulpl : forall  z x y (c: lter R), 0 < z ->  (c (z * x) (z * y)) = (c x y).
Proof. by move=> z x y c hz; rewrite ![z*_]mulrC ltef_mulpr. Qed.
Definition ltef_mulp z x y c (hz : 0 < z) := 
  (ltef_mulpr x y c hz, ltef_mulpl x y c hz).


Lemma ltef_mulnr : forall  z x y (c: lter R), 0 > z -> (c (x * z) (y * z)) = (c y x).
Proof. by move=> z x y c zn; rewrite lter_opp2 -!mulrN ltef_mulp // oppr_cp0. Qed.
Lemma ltef_mulnl : forall  z x y (c: lter R), 0 > z ->  (c (z * x) (z * y)) = (c y x).
Proof. by move=> z x y c hz; rewrite ![z*_]mulrC ltef_mulnr. Qed.
Definition ltef_muln z x y c (hz : 0 > z) := 
  (ltef_mulnr x y c hz, ltef_mulnl x y c hz).

Lemma absf_mul : forall x y, `|x * y| = `|x| * `|y|.
Proof.
move=> x y; case: (lerP x 0)=> hx; case: (lerP y 0)=> hy.
- by rewrite ger0_abs ?mulr_cp0n// ler0_abs// ler0_abs// mulrNN.
- by rewrite ler0_abs ?mulr_cp0n//= 1?ltrE// -mulNr ler0_abs// gtr0_abs.
- by rewrite ler0_abs ?mulr_cp0p//= 1?ltrE// -mulrN gtr0_abs// ler0_abs.
- by rewrite gtr0_abs ?mulr_cp0p//= gtr0_abs// gtr0_abs.
Qed.

Lemma ltf_expSSr : forall x n, 0 < x -> x < 1 -> x^+n.+2 < x.
Proof.
move=> x n l0x lx1; elim: n=> [|n ihn].
  by rewrite exprS expr1 -{3}[x]mul1r ltef_mulp.
by rewrite exprSr -{3}[x]mul1r ltef_mulp// (lter_trans _ lx1).
Qed.

Lemma ltf_exprSS : forall x n, 1 < x -> x < x^+n.+2.
Proof.
move=> x n l1x; elim: n=> [|n ihn].
  by rewrite exprS expr1 -{1}[x]mul1r ltef_mulp// (ler_lte_trans ler01)//.
rewrite exprSr -{1}[x]mul1r ltef_mulp//= ? (lter_trans l1x)//. 
by rewrite (lter_trans _ l1x)// lter01//.
Qed.

Lemma expf_gt0 : forall n x, (0 < x) -> (0 < x^+n).
Proof.
move=> n x l0x; elim: n=> [|n ihn]; first by rewrite expr0 ltr01.
by rewrite exprS mulr_cp0p.
Qed.

Lemma expf_ge0 : forall n x, (0 <= x) -> (0 <= x^+n).
Proof.
move=> n x; rewrite ler_eqVlt; case/orP=> hx; last by rewrite ltrE// expf_gt0.
rewrite -(eqP hx); elim: n => [|n ihn]; first by rewrite expr0 lter01.
by rewrite exprS mul0r lerr.
Qed.


Lemma absf_exp : forall x n, `|x^+n| = `|x|^+n.
Proof.
move=> x n; case: (ltrgtP x 0)=> hx; last first.
- rewrite hx; case: n=> [|n]; first by rewrite ?expr0 absr1.
  by rewrite absr0 exprS mul0r absr0.
- by rewrite !ger0_abs// ltrE// expf_gt0.
- case: n=> [|n]; first by rewrite !expr0 ger0_abs// ler01.
  rewrite {1}[x]smul_abs_id smul_exp absr_smul.
    by rewrite ger0_abs// expf_ge0// absrE.
  by rewrite (ltr0_sign hx) -signr_odd; case: (odd _).
Qed.

Lemma lef_expSr : forall x n, 0 <= x -> x <= 1 -> x^+n.+1 <= x.
Proof.
move=> x n; rewrite ler_eqVlt; case/orP=> lt0x.
  by rewrite -(eqP lt0x) exprS mul0r lerr.
rewrite ler_eqVlt; case/orP; first by move/eqP->; rewrite exp1rn.
move=> ltx1; case: n=> [|n]; first by rewrite expr1 lerr.
by rewrite ltrE// ltf_expSSr.
Qed.

Lemma lef_exprS : forall x n, 1 <= x -> x <= x^+n.+1.
Proof.
move=> x n; rewrite ler_eqVlt; case/orP=> hx.
  by rewrite -(eqP hx) exp1rn lerr.
case: n=> [|n]; first by rewrite expr1 lerr.
by rewrite ltrE// ltf_exprSS.
Qed.

Lemma lef_expS2 : forall n x y (c : lter R) , 0 <= x -> 0 <= y -> (c (x^+n.+1) (y^+n.+1)) = (c x y).
Proof.
move=> n x y c; wlog: x y c /(lter_op c) = (@ler R)=> [hle|].
  by case: c=> c /= [] ec hx hy; rewrite !ec -?lerNgt; do ? (congr (~~ _)); rewrite hle.
move->; rewrite ler_eqVlt; case/orP=> lt0x.
  by move=> hy; rewrite -(eqP lt0x) exprS mul0r expf_ge0//.
rewrite ler_eqVlt; case/orP=> lt0y.
  rewrite -(eqP lt0y) [0^+_]exprS mul0r.
  by apply/idP/idP; apply: contraLR; rewrite !lerNgt// expf_gt0.
elim:n =>[|n ihn]; first by rewrite !expr1.
rewrite ![_^+n.+2]exprSr; apply/idP/idP => hxy.
  case hyx: (x > y)=>//; last by rewrite -ltrNge hyx.
  rewrite -ihn -(@ltef_mulpr x)//= (lter_trans hxy)//=.
  by rewrite ltef_mulp//= ?expf_gt0// ltrE.
move:(hxy); rewrite -(@ltef_mulpl (x^+n.+1)) /=; last by rewrite expf_gt0.
by move/lter_trans->; rewrite // ltef_mulp//= ihn.
Qed.
End IntegralDomainTheory.
End IntegralDomainTheory.
Include IntegralDomainTheory.

Module Field.

Record class_of R :=
  Class { base1 :> GRing.Field.class_of R; ext :> ring_mixin_of R base1 }.
Coercion base2 R (c : class_of R) := IntegralDomain.Class c.
Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.
Definition pack := gen_pack Pack Class GRing.Field.class.

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Coercion ringType cT := GRing.Ring.Pack (class cT) cT.
Coercion comRingType cT := GRing.ComRing.Pack (class cT) cT.
Coercion unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Coercion comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Coercion idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.
Coercion oIdomainType cT := IntegralDomain.Pack (class cT) cT.
Coercion fieldType cT := GRing.Field.Pack (class cT) cT.
Coercion join_oIdomainType cT := @IntegralDomain.Pack (fieldType cT) (class cT) cT.

End Field.

Canonical Structure Field.eqType.
Canonical Structure Field.choiceType.
Canonical Structure Field.zmodType.
Canonical Structure Field.ringType.
Canonical Structure Field.comRingType.
Canonical Structure Field.unitRingType.
Canonical Structure Field.comUnitRingType.
Canonical Structure Field.idomainType.
Canonical Structure Field.oIdomainType.
Canonical Structure Field.fieldType.
Canonical Structure Field.join_oIdomainType.

Module FieldTheory.
Section FieldTheory.

Variable F : Field.type.
Implicit Types x y z t : F.

Lemma invf_gte0 : forall x (c : lter F), (c 0 x^-1) = (c 0 x).
Proof.
move=> x c; wlog: x c / (lter_op c) = (@ler F)=> [hle|->].
  case: c=> c /= [] ec; rewrite !ec; first by rewrite hle//.
  rewrite -?lerNgt//=; congr (~~ _)=> //.
  case x0: (x == 0); first by rewrite (eqP x0) invr0 lerr.
  by rewrite ![_<=0]ler_lt ?invr_eq0 ?x0// -?lerNgt hle.
case x0: (x == 0); first by rewrite (eqP x0) invr0.
case: (lerP 0 x)=> l0x; case: lerP=> l0i //; apply/eqP.
  move: (lter_mulnr (ltrW l0i) l0x); rewrite divff ?x0 //=.
  by rewrite mul0r -ltrNge lter01.
move: (lter_mulpr l0i (ltrW l0x)); rewrite divff ?x0 //=.
by rewrite mul0r -ltrNge lter01.
Qed.

Lemma invf_lte0 : forall x (c: lter F), (c (x^-1) 0) = (c x 0).
Proof. by move=> x c; rewrite -[c _ _]negbK lte_letP invf_gte0//= negbK. Qed.
Definition invf_cp0 := (invf_gte0, invf_lte0).

Lemma ltef_divpr : forall z x y (c: lter F), 0 < z -> (c x (y / z)) = (c (x * z) y).
Proof.
move=> z x y c z0; rewrite -(@ltef_mulp _ z)// mulrAC -mulrA divff ?mulr1//.
by rewrite eq_sym ltrE.
Qed.
Lemma ltef_divpl : forall z x y (c: lter F), 0 < z -> (c (x / z) y) = (c x (y * z)).
Proof. by move=> z x y c *; rewrite -[c _ _]negbK lte_letP ltef_divpr//= negbK. Qed.
Definition ltef_divp := (ltef_divpr, ltef_divpl).

Lemma ltef_divnr : forall z x y (c: lter F), 0 > z -> (c x (y / z)) = (c y (x * z)).
Proof.
move=> z x y c z0; rewrite -mulrNN -invrN ltef_divpr ?oppr_cp0//.
by rewrite mulrN -lter_opp2.
Qed.
Lemma ltef_divnl : forall z x y (c: lter F), 0 > z -> (c (x / z) y) = (c (y * z) x).
Proof. by move=> z x y c *; rewrite -[c _ _]negbK lte_letP ltef_divnr//= negbK. Qed.
Definition ltef_divn := (ltef_divnr, ltef_divnl).

Lemma lterrP : forall x (c: lter F), c x x <-> (c =2 (@ler F)).
Proof.
move=> x [c /= [] ec]; rewrite !ec lterr; split=> //=.
by move=> hc; move: (erefl (c x x)); rewrite {1}ec hc !lterr.
Qed.
Lemma lterrN : forall x (c: lter F), ~~ (c x x) <-> (c =2 (@ltr F)).
Proof.
move=> x [c /= [] ec]; rewrite !ec lterr; split=> //=.
by move=> hc; move: (erefl (c x x)); rewrite {1}ec hc !lterr.
Qed.

Lemma lteC : forall x y (c: lter F), c x y = ~~ ((lte_let c) y x).
Proof. by move=> *; rewrite negbK. Qed.

Lemma mulf_gte0 : forall x y (c: lter F), (c 0 (x * y))
  = ((c 0 x) && (c 0 y) || (c x 0) && (c y 0)).
Proof.
move=> x y c; case: (ltrgtP y 0)=> hy;
[rewrite -ltef_divnr// | rewrite -ltef_divpl// | rewrite hy];
rewrite !(mul0r, mulr0); do 1?[move/ltr_lte:hy=> hy].
- by rewrite [c 0 y]lteC !hy !(andbF,andbT) //=.
- by rewrite [c y 0]lteC !hy !(andbF,andbT,orbF) //=.
- apply/idP/idP; last by rewrite -andb_orl; case/andP.
  by move/lterrP=> ec; rewrite !ec lerr !andbT lergeP.
Qed.

Lemma mulf_lte0 : forall x y (c: lter F), (c (x * y) 0)
  = ((c x 0) && (c 0 y) || (c y 0) && (c 0 x)).
Proof.
move=> x y c; rewrite -mulrNN mulrN oppr_cp0/= mulf_gte0 !oppr_cp0.
by congr (_||_); rewrite andbC.
Qed.

Lemma ltef_invpp : forall x y (c: lter F), x > 0 -> y > 0 -> c x y -> c (y^-1) (x^-1).
Proof.
move=> x y c hx hy hxy; rewrite -(@ltef_mulpl _ x)// ltef_divpl//=.
by rewrite mulfV ?mul1r// eq_sym ?ltrWN.
Qed.

Lemma ltef_invnn : forall x y (c: lter F), x < 0 -> y < 0 -> c x y -> c (y^-1) (x^-1).
Proof.
move=> x y c; rewrite -(opprK x) -(opprK y) ![_ (- _) _]oppr_cp0.
rewrite invrN [(- - _)^-1]invrN -lter_opp2 -[_ (- _^-1) _]lter_opp2=> *.
exact: ltef_invpp.
Qed.

Lemma signr_mul : forall x y, \s (x * y) = \s x * \s y.
Proof.
move=> x y. rewrite /signr mulf_eq0.
case x0: (_ == _); case y0 : (_ == _)=> /=; rewrite ?(mulr0,mul0r) //.
rewrite mulf_gte0/= [x<=0]ler_nlt [y<=0]ler_nlt !ltr_neqAle ![0==_]eq_sym ?x0 ?y0.
by case: lerP=> ge0x; case: lerP=> ge0y //=; rewrite mulN1r opprK.
Qed.

Lemma signr_mulrn : forall x n, \s (x *+ n.+1) = \s x.
Proof.
move=> x n; rewrite -mulr_natr signr_mul -{2}[\s _]mulr1.
by congr (_*_); apply/eqP; rewrite signr_cp0 gtf0Sn.
Qed.


Lemma signr_exp : forall x n, \s (x^+n) = (\s x)^+n.
Proof.
move=> x; elim=> [|n ihn]; first by rewrite expr0 signr1.
by rewrite !exprSr signr_mul ihn mulrC.
Qed.

Lemma midf_lte : forall x y (c: lter F), c x y -> c x ((x + y)/2%:R) && c ((x + y)/2%:R) y.
Proof.
move=> x y c lxy; rewrite !ltef_divp ?gtf0Sn//.
by rewrite mulrSr !mulr_addr !mulr1 lter_add2r lter_add2l lxy.
Qed.

End FieldTheory.
End FieldTheory.
Include FieldTheory.

Module RealClosedField.

Definition axiom (F : Field.type) := forall (p : {poly F}) (a b : F), a <= b 
    -> p.[a] <= 0 <= p.[b] -> exists2 x, a <= x <= b & root p x.

Record mixin_of (F : Field.type) := Mixin {
  _ : axiom F
  (* _ : forall x : F, 0 <= x -> exists y, x = y ^+ 2; *)
  (* _ : forall (p : {poly F}), ~~ odd (size p) -> exists x : F, root p x *)
(* Should we replace it by a poly independant version, as in ClosedField ? *)
}.

Record class_of (R : Type) : Type := Class {
  base :> Field.class_of R; 
   (* In fact, this should be a new kind of Decidable Field 
      including the Le constructor ... *)
  ext :> mixin_of (Field.Pack base R)
}.

Record type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type }.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.
Definition pack T b0 (m0 : mixin_of (@Field.Pack T b0 T)) :=
  fun bT b & phant_id (Field.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Coercion ringType cT := GRing.Ring.Pack (class cT) cT.
Coercion comRingType cT := GRing.ComRing.Pack (class cT) cT.
Coercion unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Coercion comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Coercion idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.
Coercion oIdomainType cT := IntegralDomain.Pack (class cT) cT.
Coercion fieldType cT := GRing.Field.Pack (class cT) cT.
Coercion oFieldType cT := Field.Pack (class cT) cT.

End RealClosedField.

Bind Scope ring_scope with RealClosedField.sort.
Canonical Structure RealClosedField.eqType.
Canonical Structure RealClosedField.choiceType.
Canonical Structure RealClosedField.zmodType.
Canonical Structure RealClosedField.ringType.
Canonical Structure RealClosedField.comRingType.
Canonical Structure RealClosedField.unitRingType.
Canonical Structure RealClosedField.comUnitRingType.
Canonical Structure RealClosedField.idomainType.
Canonical Structure RealClosedField.fieldType.
Canonical Structure RealClosedField.oFieldType.

Module RealClosedFieldTheory.
Definition poly_ivt := RealClosedField.axiom.
End RealClosedFieldTheory.
Include RealClosedFieldTheory.

Module Theory.
Export IntegralDomainTheory.
Export FieldTheory.
Export RealClosedFieldTheory.
End Theory.

End OrderedRing.

Canonical Structure OrderedRing.ler_lterS.
Canonical Structure OrderedRing.ltr_lterS.
Canonical Structure OrderedRing.lte_let_lter.

Canonical Structure OrderedRing.IntegralDomain.eqType.
Canonical Structure OrderedRing.IntegralDomain.choiceType.
Canonical Structure OrderedRing.IntegralDomain.zmodType.
Canonical Structure OrderedRing.IntegralDomain.ringType.
Canonical Structure OrderedRing.IntegralDomain.comRingType.
Canonical Structure OrderedRing.IntegralDomain.unitRingType.
Canonical Structure OrderedRing.IntegralDomain.comUnitRingType.
Canonical Structure OrderedRing.IntegralDomain.idomainType.

Canonical Structure OrderedRing.Field.eqType.
Canonical Structure OrderedRing.Field.choiceType.
Canonical Structure OrderedRing.Field.zmodType.
Canonical Structure OrderedRing.Field.ringType.
Canonical Structure OrderedRing.Field.comRingType.
Canonical Structure OrderedRing.Field.unitRingType.
Canonical Structure OrderedRing.Field.comUnitRingType.
Canonical Structure OrderedRing.Field.idomainType.
Canonical Structure OrderedRing.Field.oIdomainType.
Canonical Structure OrderedRing.Field.fieldType.
Canonical Structure OrderedRing.Field.join_oIdomainType.

Canonical Structure OrderedRing.RealClosedField.eqType.
Canonical Structure OrderedRing.RealClosedField.choiceType.
Canonical Structure OrderedRing.RealClosedField.zmodType.
Canonical Structure OrderedRing.RealClosedField.ringType.
Canonical Structure OrderedRing.RealClosedField.comRingType.
Canonical Structure OrderedRing.RealClosedField.unitRingType.
Canonical Structure OrderedRing.RealClosedField.comUnitRingType.
Canonical Structure OrderedRing.RealClosedField.idomainType.
Canonical Structure OrderedRing.RealClosedField.oIdomainType.
Canonical Structure OrderedRing.RealClosedField.fieldType.
Canonical Structure OrderedRing.RealClosedField.oFieldType.

Bind Scope ring_scope with OrderedRing.IntegralDomain.sort.
Bind Scope ring_scope with OrderedRing.Field.sort.
Bind Scope ring_scope with OrderedRing.RealClosedField.sort.

Notation oIdomainType := OrderedRing.IntegralDomain.type.
Notation oFieldType := OrderedRing.Field.type.
Notation rFieldType := OrderedRing.RealClosedField.type.

Notation OIdomainType T m := (@OrderedRing.IntegralDomain.pack T _ m _ _ id _ id).
Notation OFieldType T m := (@OrderedRing.Field.pack T _ m _ _ id _ id).
Notation RFieldType T m := (@OrderedRing.RealClosedField.pack T _ m _ _ id _ id).

Notation "[ 'oIdomainType' 'of' T ]" :=
    (@OrderedRing.IntegralDomain.clone T _ _ id)
  (at level 0, format "[ 'oIdomainType'  'of'  T ]") : form_scope.
Notation "[ 'oFieldType' 'of' T ]" := (@OrderedRing.Field.clone T _ _ id)
  (at level 0, format "[ 'oFieldType'  'of'  T ]") : form_scope.
Notation "[ 'rFieldType' 'of' T ]" := (@OrderedRing.RealClosedField.clone T _ _ id)
  (at level 0, format "[ 'rFieldType'  'of'  T ]") : form_scope.

Notation "<=%R" := (@OrderedRing.ler _) : ring_scope.
Notation "x <= y" := (OrderedRing.ler x y) : ring_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T))
  (at level 70, y at next level) : ring_scope.
Notation "x >= y" := (y <= x) (only parsing) : ring_scope.
Notation "x >= y :> T" := ((x : T) >= (y : T))
  (at level 70, y at next level) : ring_scope.


Notation "<%R" := (@OrderedRing.ltr _) : ring_scope.
Notation "x < y"  := (OrderedRing.ltr x y) : ring_scope.
Notation "x < y :> T" := ((x : T) < (y : T))
  (at level 70, y at next level) : ring_scope.
Notation "x > y"  := (y < x) (only parsing) : ring_scope.
Notation "x > y :> T" := ((x : T) > (y : T))
  (at level 70, y at next level) : ring_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : ring_scope.
Notation "x < y <= z" := ((x < y) && (y <= z)) : ring_scope.
Notation "x <= y < z" := ((x <= y) && (y < z)) : ring_scope.
Notation "x < y < z" := ((x < y) && (y < z)) : ring_scope.
Notation "`| x |" := (OrderedRing.absr x) : ring_scope.
Notation "'\s' x" := (OrderedRing.signr x) : ring_scope.
Notation "s ?* x" := (OrderedRing.smul s x) : ring_scope.
