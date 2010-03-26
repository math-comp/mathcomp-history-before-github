Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
Require Import bigops ssralg poly polydiv.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.

Reserved Notation  "| x |" (at level 35, x at next level, format "| x |").
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

Module Ring.

Record class_of (R : Type) : Type := Class {
  base :> GRing.Ring.class_of R;
  ext :> mixin_of (GRing.Ring.Pack base R)
}.

Record type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type }.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.
Definition pack := gen_pack Pack Class GRing.Ring.class.

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Coercion ringType cT := GRing.Ring.Pack (class cT) cT.
(* Coercion comRingType cT := GRing.ComRing.Pack (class cT) cT. *)
(* Coercion unitRingType cT := GRing.UnitRing.Pack (class cT) cT. *)
(* Coercion comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT. *)
(* Coercion idomainType cT := GRing.IntegralDomain.Pack (class cT) cT. *)
(* Coercion fieldType cT := GRing.Ring.Pack (class cT) cT. *)

End Ring.

Bind Scope ring_scope with Ring.sort.
Canonical Structure Ring.eqType.
Canonical Structure Ring.choiceType.
Canonical Structure Ring.zmodType.
Canonical Structure Ring.ringType.
(* Canonical Structure OrderedRing.comRingType. *)
(* Canonical Structure OrderedRing.unitRingType. *)
(* Canonical Structure OrderedRing.comUnitRingType. *)
(* Canonical Structure OrderedRing.idomainType. *)
(* Canonical Structure OrderedRing.fieldType. *)


(* Notation oRingType := Ring.type. *)
(* Notation ORingType T m := (Ring.pack T _ m _ _ id _ id). *)
(* Notation "[ 'oRingType' 'of' T 'for' cT ]" := (Ring.clone T cT _ idfun) *)
(*   (at level 0, format "[ 'oRingType'  'of'  T  'for'  cT ]") : form_scope. *)
(* Notation "[ 'oRingType' 'of' T ]" := (Ring.clone T _ _ id) *)
(*   (at level 0, format "[ 'oRingType'  'of'  T ]") : form_scope. *)

Open Scope ring_scope.

Definition ler (R : Ring.type) : rel R := le (Ring.class R).
Notation "<=%R" := (@ler _) : ring_scope.
Notation "x <= y" := (ler x y) : ring_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T)) : ring_scope.
Notation "x >= y" := (y <= x) (only parsing) : ring_scope.
Notation "x >= y :> T" := ((x : T) >= (y : T)) : ring_scope.

Notation "x < y"  := (~~(y <= x)) : ring_scope.
Notation "x < y :> T" := ((x : T) < (y : T)) : ring_scope.
Notation "x > y"  := (y < x) (only parsing) : ring_scope.
Notation "x > y :> T" := ((x : T) > (y : T)) : ring_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : ring_scope.
Notation "x < y <= z" := ((x < y) && (y <= z)) : ring_scope.
Notation "x <= y < z" := ((x <= y) && (y < z)) : ring_scope.
Notation "x < y < z" := ((x < y) && (y < z)) : ring_scope.

Section RingTheory.

Variable R : Ring.type.
Implicit Types x y z t : R.

Lemma ler_anti : antisymmetric (@ler R). Proof. by case R => T [? []]. Qed.
Lemma ler_trans : transitive (@ler R). Proof. by case R => T [? []]. Qed.
Lemma ler_total : total (@ler R). Proof. by case R => T [? []]. Qed.
Lemma lerr : reflexive (@ler R).
Proof. by move=> x; rewrite -[_<=_]orbb; apply: ler_total. Qed.
Hint Resolve lerr.

Lemma ltrNge : forall x y, ~~(x < y) = (x >= y).
Proof. by move=> x y; rewrite negbK. Qed.

Lemma ler_add2l : forall z x y, ((x + z) <= (y + z)) = (x <= y).
Proof. 
have w : forall z x y, x <= y -> (x + z) <= (y + z).
  by case R => T [? []].
move=> z x y; apply/idP/idP; last exact: w.
by move/(w (-z)); rewrite -!addrA subrr !addr0.
Qed.

Lemma ler_add2r : forall z x y, ((z + x) <= (z + y)) = (x <= y).
Proof. move=> z x y; rewrite ![z+_]addrC; exact: ler_add2l. Qed.

Lemma le0r_mul : forall x y, 0 <= x -> 0 <= y -> 0 <= (x * y).
Proof. by case R => T [? []]. Qed.

Lemma ler_sub : forall x y,  (x <= y) = (0 <= y - x).
Proof. by move=> x y; symmetry; rewrite -(ler_add2l x) add0r subrK. Qed.

Lemma ler_opp : forall x y, (y <= x) = (-x <= -y).
Proof. by move=> x y; symmetry; rewrite ler_sub opprK addrC -ler_sub. Qed.

Lemma ler_opprC : forall x y, (x <= -y) = (y <= -x).
Proof. by move=> x y; rewrite ler_opp opprK. Qed.
Lemma ler_opplC : forall x y, (-x <= y) = (-y <= x).
Proof. by move=> x y; rewrite ler_opp opprK. Qed.

Lemma posNr : forall x, (0 <= -x) = (x <= 0).
Proof. by move=> x; rewrite ler_opp oppr0 opprK. Qed.
Lemma negNr : forall x, (0 >= -x) = (x >= 0).
Proof. by move=> x; rewrite ler_opp oppr0 opprK. Qed.
Definition signNr := (posNr,negNr).

Lemma ltrW : forall x y, x < y -> x <= y.
Proof. by move=> x y; case/orP:(ler_total x y)=> ->. Qed.
Hint Resolve ltrW.

Lemma eqr_le : forall x y, (x == y) = (x <= y <= x).
Proof.
move=> x y; apply/idP/idP; last by move/ler_anti->.
by move/eqP->; rewrite lerr.
Qed.

Lemma ler_lt : forall x y, x != y -> x <= y = (x < y).
Proof.
move=> x y xy; apply/idP/idP; last exact: ltrW.
case lyx : (y<=x)=> // lxy. apply: contra xy=> _.
by rewrite eqr_le lxy lyx.
Qed.

Lemma ler_nlt : forall x y, x <= y = ~~(y < x).
Proof. by move=> x y; apply: negbRL. Qed.

Lemma ltr_neqAle : forall x y, (x < y) = (x != y) && (x <= y).
Proof. 
move=> x y; case exy: (_==_)=> /=.
  by rewrite (eqP exy) lerr.
by symmetry; rewrite ler_lt ?exy.
Qed.

Lemma ltrWN : forall x y, x < y -> x == y = false.
Proof. by move=> x y; rewrite ltr_neqAle; case/andP; move/negPf=> ->. Qed.
Hint Resolve ltrWN.

Definition ltrE x y (hxy : x < y) := (hxy,(ltrWN hxy),(ltrW hxy)).

Lemma ler_lt_trans : forall y x z, x <= y -> y < z -> x < z.
Proof. move=> y x z lxy; apply: contra=> lzx; exact: ler_trans lxy. Qed.

Lemma ltr_trans : forall y x z, x < y -> y < z -> x < z.
Proof. move=> y x z; move/ltrW; exact: ler_lt_trans. Qed.

Lemma ltr_le_trans : forall y x z , x < y -> y <= z -> x < z.
Proof.
move=> y x z lxy lyz; move:lxy; apply: contra=> lzx; exact: ler_trans lzx.
Qed.

CoInductive le_xor_gtr (x y : R) : bool -> bool -> Set :=
  | LeNotGtr of x <= y : le_xor_gtr x y true false
  | GtrNotLe of y < x  : le_xor_gtr x y false true.

Lemma lerP : forall x y, le_xor_gtr x y (x <= y) (y < x).
Proof. by move=> x y; case hxy: (_<=_); constructor; rewrite ?hxy //. Qed.

CoInductive ltr_xor_geq (x y : R) : bool -> bool -> Set :=
  | LtrNotGeq of x < y  : ltr_xor_geq x y false true
  | GeqNotLtr of y <= x : ltr_xor_geq x y true false.

Lemma ltrP : forall x y, ltr_xor_geq x y (y <= x) (x < y).
Proof. by move=> x y; case: (lerP y x); constructor. Qed.

CoInductive comparer x y : bool -> bool -> bool -> Set :=
  | ComparerLt of x < y : comparer x y true false false
  | ComparerGt of x > y : comparer x y false true false
  | ComparerEq of x = y : comparer x y false false true.

Lemma ltrgtP : forall m n, comparer m n (m < n) (n < m) (m == n).
Proof.
move=> x y; case exy: (_==_); first by rewrite (eqP exy) lerr; constructor.
case: (ltrP y x); rewrite ler_lt ?exy //; last first.
  by move=> lxy; rewrite lxy; constructor.
rewrite negbK; move=> lyx; rewrite lyx; constructor.
by rewrite ltr_neqAle lyx eq_sym exy.
Qed.

Lemma legerP : forall x y, (x <= y) || (y <= x).
Proof. by move=> x y; case: lerP=> //; move/ltrW->. Qed. 

Lemma ler01 : 0 <= 1 :> R.
Proof. 
case/orP:(ler_total 0 1); first done.
rewrite ler_opp oppr0=> l0m.
by move: (le0r_mul l0m l0m); rewrite mulrN mulr1 opprK.
Qed.

Lemma ltr01 : 0 < 1 :> R.
Proof. by rewrite -ler_lt ?ler01 // eq_sym oner_eq0. Qed.

Lemma ler_add : forall x y z t, x <= y -> z <= t -> x + z <= y + t.
Proof.
move=> x y z t lxy.
rewrite -(ler_add2r y)=> lyzyt; apply: ler_trans lyzyt.
by rewrite ler_add2l.
Qed.

Lemma ler_lt_add : forall x y z t, x <= y -> z < t -> x + z < y + t.
Proof.
move=> x y z t lxy; apply: contra; rewrite ler_opp=> lxzyt.
have:= (ler_add lxy lxzyt).
by rewrite !oppr_add !addrA !subrr !sub0r -ler_opp.
Qed.

Lemma ler_addrA : forall z x y, (x <= y + z) = (x - z <= y).
Proof. by move=> z x y; rewrite -(@ler_add2l (-z)) -addrA subrr addr0. Qed.

Lemma ler_addlA : forall z x y, (x <= z + y) = (x - z <= y).
Proof. by move=> z x y; rewrite addrC ler_addrA. Qed.

Lemma ler_subrA : forall z x y, (x <= y - z) = (x + z <= y).
Proof. by move=> z x y; rewrite ler_addrA opprK. Qed.

Lemma ler_sublA : forall z x y, (x <= y - z) = (z + x <= y).
Proof. by move=> z x y; rewrite ler_addrA addrC opprK. Qed.

Definition ler_subr z x y := (esym (ler_addrA z x y), ler_subrA z x y).
Definition ler_subl z x y := (esym (ler_addlA z x y), ler_sublA z x y).

Lemma ltr_le_add : forall x y z t, x < y -> z <= t -> x + z < y + t.
Proof. 
move=> x y z t lxy lzt; rewrite addrC [x+_]addrC; exact: ler_lt_add. 
Qed.

Lemma ltr_add : forall x y z t, x < y -> z < t -> x + z < y + t.
Proof. move=> x y z t; move/ltrW; exact: ler_lt_add. Qed.

Lemma ler_mulP : forall z x y, 0 <= z -> (x <= y) -> (x * z <= y * z).
Proof.
move=> z x t zp lxy; rewrite ler_sub -mulr_subl.
by apply: le0r_mul; rewrite -?ler_sub.
Qed.

Lemma ler_mulN : forall z x y, 0 >= z -> (x <= y) -> (x * z >= y * z).
Proof.
move=> z x t zn lxy; rewrite ler_opp -!mulrN. 
by apply: ler_mulP=> //; rewrite posNr.
Qed.

Lemma neq_ltr : forall x y, (x != y) = (x < y) || (y < x).
Proof. by move=> *; rewrite eqr_le negb_and orbC. Qed.

Lemma ler_eqVlt : forall x y, (x <= y) = (x == y) || (x < y).
Proof. 
move=> x y. rewrite ltr_neqAle. 
by case exy: (_==_); rewrite ?(andbT,andbF) // (eqP exy) lerr.
Qed.

Definition null_characteristic := 
  forall n : nat, (n.+1)%:R == (GRing.zero R) = false.
Lemma oRing_carac : null_characteristic.
Proof.
suff lt0n: forall n : nat, (n.+1)%:R > 0 :> R. 
  by move=>n; rewrite eq_sym ltrE.
elim; first by rewrite mulr1n ltr01.
move=> n lt0Sn; rewrite -addn1 natr_add mulr1n; apply: (ltr_trans lt0Sn).
by rewrite -ler_subl subrr ltr01.
Qed.

Require Import zmodp.
Require Import fintype.

Definition signr x : 'F_3 :=  if x == 0 then 0 else if 0 <= x then 1 else -1.
Notation "'\s' x" := (signr x).

Lemma signr_comp0 : forall x, 
  ((0 < x) = (\s x == 1)) *
  ((x < 0) = (\s x == -1)) *
  ((x == 0) = (\s x == 0)).
Proof.
move=> x; rewrite /signr; case: ltrgtP=> //; last by move/ltrW->.
by move/negPf->.
Qed.

Lemma signrP : forall x, 0 < x -> \s x = 1.
Proof. by move=> x; rewrite signr_comp0; apply:(iffP idP); move/eqP. Qed.
Lemma signrN : forall x, x < 0 -> \s x = -1.
Proof. by move=> x; rewrite signr_comp0; apply:(iffP idP); move/eqP. Qed.
Lemma signr0 : \s 0 = 0.
Proof. by rewrite /signr eqxx. Qed.


Lemma signr_opp : forall x, \s (-x) = -\s x.
Proof.
move=> x; case: (ltrgtP x 0)=> hx; last by rewrite hx !(oppr0,signr0). 
  by rewrite signrP ?signNr// signrN// opprK.
by rewrite signrN ?signNr// signrP.
Qed.

Lemma inF3P : (forall s : 'F_3, [\/ s = 0,  s = 1 | s = -1]).
Proof. 
move=> s; suff : [|| s == 0,  s == 1 | s == -1].
  by case/or3P; move/eqP->; [constructor | constructor 2 | constructor 3 ].
by case:s ; elim=> //=; elim=> //=; elim. 
Qed.

Definition signmulr (s : 'F_3) (x : R) := 
  if s == 0 then 0 else if s == 1 then x else -x.
Notation "s ?* x" := (signmulr s x).

Lemma mulSN1r : forall x, (-1)?* x = -x. Proof. done. Qed.

Lemma oppSr : forall s x, - s ?* x = (-s) ?* x.
Proof.
by rewrite /signmulr=> s x; case: (inF3P s)=> -> //=; rewrite ?(opprK,oppr0).
Qed.
(* Lemma rsignE : (rsign 1 = 1) * (rsign 0 = 0) * (rsign (-1) = -1). *)
(* Proof. done. *)

Lemma mulSr : forall s s' x, s ?* (s' ?* x) = (s*s')?* x.
Proof.
by rewrite /signmulr=> s s' x; case: (inF3P s)=> ->; case: (inF3P s')=> ->;
rewrite //= ?(opprK, oppr0).
Qed.

Lemma addSr : forall s s' x y, s != 0 -> 
    s ?* x + s' ?* y = s ?* (x + (s*s') ?* y).
Proof.
move=> s; case: (inF3P s)=> -> //= s' x y _; first by rewrite mul1r.
(* Why do we still have "(-1)?*x" instead of -x ???? *)
by rewrite !mulSN1r mulN1r oppr_add oppSr opprK.
Qed.

Definition absr x := (\s x) ?* x.
Notation "| x |" := (absr x) : ring_scope.

Lemma absr0 : |0| = 0.
Proof. by rewrite /absr /signr eqxx. Qed.

Lemma absr_opp : forall x, | -x | = |x|.
Proof. by move=> x; rewrite /absr signr_opp -mulSN1r mulSr mulrN1 opprK. Qed.

Lemma absrP : forall x, (x >= 0) -> |x| = x.
Proof.
move=> x; rewrite /absr ler_eqVlt; case/orP=> hx; last by rewrite signrP.
by rewrite -(eqP hx) signr0.
Qed.
Definition absrNN x (hx : x > 0) := absrP (ltrW hx). 

Lemma absrN : forall x, (x <= 0) -> |x| = -x.
Proof.
move=> x hx; rewrite -{1}[x]opprK absr_opp //.
by apply:absrP; rewrite signNr.
Qed.
Definition absrNP x (hx : x < 0) := absrN (ltrW hx). 

Lemma absrPN : forall x, (|x| = x) \/ (|x| = -x).
Proof.
move=> x; case/orP:(legerP x 0); last by move/absrP->; constructor.
by move/absrN->; constructor 2.
Qed.

Lemma absr_ge0 : forall x, 0 <= |x|.
Proof.
move=> x; case: (lerP x 0)=> hx; last by rewrite absrP ltrW.
by rewrite absrN // signNr.
Qed.
Hint Resolve absr_ge0.

Lemma rsign_abs : forall x, x = (\s x) ?* |x|.
Proof.
move=> x; case: (ltrgtP x 0)=> hx; last by rewrite hx absr0 signr0.
  by rewrite signrN// absrNP// mulSN1r opprK.
by rewrite signrP// absrNN.
Qed.

Lemma absr_eq0 : forall x, (|x| == 0) = (x == 0).
Proof.
move=> x; case: (ltrgtP x)=> hx; last by rewrite hx absr0 eqxx.
  by rewrite absrNP// oppr_eq0 ltrE.
by rewrite absrNN// eq_sym ltrE.
Qed.

Lemma absr_lt0 : forall x, |x| < 0 = false.
Proof. by move=> x; apply/negP; apply/negP. Qed.

Lemma absr_le0 : forall x, (|x| <= 0) = (x == 0).
Proof.
move=> x; rewrite -absr_eq0; case hx:(_==_).
  by move/eqP:hx->; rewrite lerr.
by rewrite ler_lt ?absr_lt0 ?hx.
Qed.

Definition absrE x := (absr0, absr_ge0, absr_eq0, absr_lt0, absr_le0).

Lemma absr_subC : forall x y, |x - y| = |y - x|.
Proof. by move=> x y; rewrite -oppr_sub absr_opp. Qed.

Lemma ler_addr_transl : forall x y z t, x <= y -> z + y <= t -> z + x <= t.
Proof.
by move=> x y z t lxy lyzt; apply: ler_trans lyzt; rewrite ler_add2r.
Qed. 
Lemma ler_addl_transl : forall x y z t, x <= y -> y + z <= t -> x + z <= t.
Proof. move=> x y z t; rewrite ![_+z]addrC; exact: ler_addr_transl. Qed.

Lemma ler_addr_transr : forall x y z t, x <= y -> z <= t + x -> z <= t + y.
Proof.
by move=> x y z t lxy lztx; apply: (ler_trans lztx); rewrite ler_add2r.
Qed.
Lemma ler_addl_transr : forall x y z t, x <= y -> z <= x + t -> z <= y + t.
Proof. move=> x y z t; rewrite ![_+t]addrC; exact: ler_addr_transr. Qed.

Lemma absr_add_le : forall x y, | x + y | <= |x| + |y|.
Proof.
move=> x y; case/orP: (legerP y 0)=> hy; case/orP: (legerP x 0)=> hx.
- move:(ler_add hx hy); rewrite addr0; move/absrN->.
  by rewrite (absrN hx) (absrN hy) oppr_add.
- rewrite (absrP hx) (absrN hy); case: (absrPN (x+y))=> ->.
  + move: (hy); rewrite -signNr=> hNy.
    by apply: (ler_addr_transl hy); apply: (ler_addr_transr hNy).
  + rewrite oppr_add; move:(hx); rewrite -signNr=> hNx.
    by apply:(ler_addl_transl hNx); apply:(ler_addl_transr hx).
- rewrite (absrN hx) (absrP hy); case: (absrPN (x+y))=> ->.
  + move: (hx); rewrite -signNr=> hNx.
    by apply: (ler_addl_transl hx); apply: (ler_addl_transr hNx).
  + rewrite oppr_add; move:(hy); rewrite -signNr=> hNy.
    by apply:(ler_addr_transl hNy); apply:(ler_addr_transr hy).
- move:(ler_add hx hy); rewrite addr0; move/absrP->.
  by rewrite (absrP hx) (absrP hy).
Qed.

Lemma subr_abs_le : forall x y, |x| - |y| <= | x + y |.
Proof.
move=> x y; rewrite -{1}[x](subr0) -[0](subrr y) oppr_sub addrA.
apply: (ler_addl_transl (absr_add_le _ _)). 
by rewrite absr_opp -addrA subrr addr0.
Qed.

Lemma absr_lt : forall x y, y >= 0 -> (|x| < y) = (-y < x < y).
move=> x y hy; rewrite -negb_or; apply/idP/idP; apply: contra.
  case/orP; last by move=> hxy; move: (ler_trans hy hxy)=> hx; rewrite absrP.
  rewrite ler_opp opprK=> hxy; move: (ler_trans hy hxy)=> hx.
  by rewrite -absr_opp absrP.
case:(absrPN x)=> ->; first by move->; rewrite orbT.
by rewrite ler_opp opprK; move->.
Qed.

Lemma absr_le : forall x y, y >= 0 -> (|x| <= y) = (-y <= x <= y).
Proof.
move=> x y hy; move:(hy); rewrite -signNr=> hNy; rewrite ler_eqVlt !absr_lt //.
case: (ltrgtP x 0)=> hx.
- move:(ltr_le_trans hx hy)=>hxy. rewrite !(ltrE hxy).
  by rewrite !andbT absrNP // -eqr_oppC eq_sym -ler_eqVlt.
- by move:(ler_lt_trans hNy hx)=>hxy; rewrite !(ltrE hxy) absrNN// -ler_eqVlt.
- by rewrite hx absr0 posNr orb_andr -ler_eqVlt negNr.
Qed.

Lemma absr_abs_le : forall x y, | |x| - |y| | <= | x + y |.
Proof.
by move=> x y; rewrite absr_le// ler_opplC oppr_sub {1}[_+y]addrC !subr_abs_le.
Qed.

Lemma absr_leAle : forall z x y, z >= 0 -> (|x - y| <= z) = (y - z <= x <= y + z).
Proof. by move=> z x y hz; rewrite absr_le //; rewrite !ler_subl. Qed.

Lemma absr_sub_lt : forall z x y, z >= 0 -> (|x - y| < z) = (y - z < x < y + z).
Proof. by move=> z x y hz; rewrite absr_lt // !ler_subl. Qed.


Lemma absr_le_lt0: forall x y, y < 0 -> (|x| <= y = false).
Proof.
move=> x y hy; apply/negP; apply/negP; move:(absr_ge0 x).
by move/(ltr_le_trans _)->.
Qed.

Lemma absr_lt_le0 : forall x y, y <= 0 -> (|x| < y = false).
Proof.
move=> x y hy; apply/negP; apply/negP; move: (absr_ge0 x).
by move/(ler_trans _)->.
Qed.


End RingTheory.

Notation "| x |" := (absr x) : ring_scope.

Module ComRing.

Record class_of R :=
  Class { base1 :> GRing.ComRing.class_of R; ext :> ring_mixin_of R base1}.
Coercion base2 R (c : class_of R) := Ring.Class c.
Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.
Definition pack := gen_pack Pack Class GRing.ComRing.class.

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Coercion ringType cT := GRing.Ring.Pack (class cT) cT.
Coercion oRingType cT := Ring.Pack (class cT) cT.
Coercion comRingType cT := GRing.ComRing.Pack (class cT) cT.
Definition join_oRingType cT := @Ring.Pack (comRingType cT) (class cT) cT.

End ComRing.


Canonical Structure ComRing.eqType.
Canonical Structure ComRing.choiceType.
Canonical Structure ComRing.zmodType.
Canonical Structure ComRing.ringType.
Canonical Structure ComRing.oRingType.
Canonical Structure ComRing.comRingType.
Canonical Structure ComRing.join_oRingType.

Module UnitRing.

Record class_of R :=
  Class { base1 :> GRing.UnitRing.class_of R; ext :> ring_mixin_of R base1 }.
Coercion base2 R (c : class_of R) := Ring.Class c.
Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.
Definition pack := gen_pack Pack Class GRing.UnitRing.class.

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Coercion ringType cT := GRing.Ring.Pack (class cT) cT.
Coercion oRingType cT := Ring.Pack (class cT) cT.
Coercion unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Definition join_oRingType cT := @Ring.Pack (unitRingType cT) (class cT) cT.

End UnitRing.

Canonical Structure UnitRing.eqType.
Canonical Structure UnitRing.choiceType.
Canonical Structure UnitRing.zmodType.
Canonical Structure UnitRing.ringType.
Canonical Structure UnitRing.oRingType.
Canonical Structure UnitRing.unitRingType.
Canonical Structure UnitRing.join_oRingType.

Module ComUnitRing.

Record class_of R :=
  Class { base1 :> GRing.ComUnitRing.class_of R; ext :> ring_mixin_of R base1 }.
Coercion base2 R (c : class_of R) := ComRing.Class c.
Coercion base3 R (c : class_of R) := @UnitRing.Class R c c.
Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.
Definition pack := gen_pack Pack Class GRing.ComUnitRing.class.

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Coercion ringType cT := GRing.Ring.Pack (class cT) cT.
Coercion oRingType cT := Ring.Pack (class cT) cT.
Coercion comRingType cT := GRing.ComRing.Pack (class cT) cT.
Coercion oComRingType cT := ComRing.Pack (class cT) cT.
Coercion unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Coercion oUnitRingType cT := UnitRing.Pack (class cT) cT.
Coercion comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.

Section Joins.
Variable cT : type.
Let clT := class cT.
Let cT' := comUnitRingType cT.
Definition join_oRingType := @Ring.Pack cT' clT cT.
Definition join_oComRingType := @ComRing.Pack cT' clT cT.
Definition join_oUnitRingType := @UnitRing.Pack cT' clT cT.
Definition ujoin_oComRingType := @ComRing.Pack (unitRingType cT) clT cT.
Definition cjoin_oUnitRingType := @UnitRing.Pack (comRingType cT) clT cT.
Definition fcjoin_oUnitRingType := @UnitRing.Pack (oComRingType cT) clT cT.
End Joins.

End ComUnitRing.

Canonical Structure ComUnitRing.eqType.
Canonical Structure ComUnitRing.choiceType.
Canonical Structure ComUnitRing.zmodType.
Canonical Structure ComUnitRing.ringType.
Canonical Structure ComUnitRing.oRingType.
Canonical Structure ComUnitRing.comRingType.
Canonical Structure ComUnitRing.oComRingType.
Canonical Structure ComUnitRing.unitRingType.
Canonical Structure ComUnitRing.oUnitRingType.
Canonical Structure ComUnitRing.comUnitRingType.
Canonical Structure ComUnitRing.join_oRingType.
Canonical Structure ComUnitRing.join_oComRingType.
Canonical Structure ComUnitRing.join_oUnitRingType.
Canonical Structure ComUnitRing.ujoin_oComRingType.
Canonical Structure ComUnitRing.cjoin_oUnitRingType.
Canonical Structure ComUnitRing.fcjoin_oUnitRingType.

Module IntegralDomain.

Record class_of R :=
  Class { base1 :> GRing.IntegralDomain.class_of R; ext :> ring_mixin_of R base1 }.
Coercion base2 R (c : class_of R) := ComUnitRing.Class c.
Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.
Definition pack := gen_pack Pack Class GRing.IntegralDomain.class.

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.
Coercion zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Coercion ringType cT := GRing.Ring.Pack (class cT) cT.
Coercion oRingType cT := Ring.Pack (class cT) cT.
Coercion comRingType cT := GRing.ComRing.Pack (class cT) cT.
Coercion oComRingType cT := ComRing.Pack (class cT) cT.
Coercion unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Coercion oUnitRingType cT := UnitRing.Pack (class cT) cT.
Coercion comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Coercion oComUnitRingType cT := ComUnitRing.Pack (class cT) cT.
Coercion idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.

Section Joins.
Variable cT : type.
Let clT := class cT.
Let cT' := idomainType cT.
Definition join_oRingType := @Ring.Pack cT' clT cT.
Definition join_oUnitRingType := @UnitRing.Pack cT' clT cT.
Definition join_oComRingType := @ComRing.Pack cT' clT cT.
Definition join_oComUnitRingType := @ComUnitRing.Pack cT' clT cT.
End Joins.

End IntegralDomain.

Canonical Structure IntegralDomain.eqType.
Canonical Structure IntegralDomain.choiceType.
Canonical Structure IntegralDomain.zmodType.
Canonical Structure IntegralDomain.ringType.
Canonical Structure IntegralDomain.oRingType.
Canonical Structure IntegralDomain.comRingType.
Canonical Structure IntegralDomain.oComRingType.
Canonical Structure IntegralDomain.unitRingType.
Canonical Structure IntegralDomain.oUnitRingType.
Canonical Structure IntegralDomain.comUnitRingType.
Canonical Structure IntegralDomain.oComUnitRingType.
Canonical Structure IntegralDomain.idomainType.
Canonical Structure IntegralDomain.join_oRingType.
Canonical Structure IntegralDomain.join_oComRingType.
Canonical Structure IntegralDomain.join_oUnitRingType.
Canonical Structure IntegralDomain.join_oComUnitRingType.

Section IdomainTheory.

Variable F : IntegralDomain.type.
Implicit Types x y z t : F.

Lemma absfP : forall x, (x >= 0) = (|x| == x).
Proof.
move=> x; case: lerP=> lx; first by move/absrP:(lx)->; rewrite eqxx.
move/absrNP:(lx)->; rewrite -eqr_oppC -subr_eq0 opprK add2r; symmetry.
by rewrite mulf_eq0 (ltrE lx) oRing_carac.
Qed.

Lemma absfN : forall x, (x <= 0) = (|x| == -x).
Proof. move=> x; rewrite -signNr -absr_opp; exact: absfP. Qed.


Lemma absf_lt : forall x y, (|x| < y) = (-y < x < y).
Proof.
move=> x y; case: (lerP 0 y); first exact: absr_lt.
move=> hy; rewrite absr_lt_le0 ?(ltrE hy) //; symmetry.
apply/negP; case/andP=> hNyx hxy.
move: (ltr_trans (ltr_trans hNyx hxy) hy).
by rewrite signNr; move/(ltr_trans hy); rewrite lerr.
Qed.

Lemma absf_le : forall x y, (|x| <= y) = (-y <= x <= y).
Proof.
move=> x y; case: (lerP 0 y); first exact: absr_le.
move=> hy; move:(hy); move/absr_le_lt0->; symmetry.
apply/negP; case/andP=> hNyx hxy.
move: (ler_lt_trans (ler_trans hNyx hxy) hy).
by rewrite signNr; move/(ltr_trans hy); rewrite lerr.
Qed.

Lemma absf_leAle : forall z x y, (|x - y| <= z) = (y - z <= x <= y + z).
Proof. by move=> z x y; rewrite absf_le // !ler_subl. Qed.

Lemma absf_sub_lt : forall z x y, (|x - y| < z) = (y - z < x < y + z).
Proof. by move=> z x y; rewrite absf_lt // !ler_subl. Qed.

End IdomainTheory.

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
Coercion oRingType cT := Ring.Pack (class cT) cT.
Coercion comRingType cT := GRing.ComRing.Pack (class cT) cT.
Coercion oComRingType cT := ComRing.Pack (class cT) cT.
Coercion unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Coercion oUnitRingType cT := UnitRing.Pack (class cT) cT.
Coercion comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Coercion oComUnitRingType cT := ComUnitRing.Pack (class cT) cT.
Coercion idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.
Coercion oIdomainType cT := IntegralDomain.Pack (class cT) cT.
Coercion fieldType cT := GRing.Field.Pack (class cT) cT.

Section Joins.
Variable cT : type.
Let clT := class cT.
Let cT' := fieldType cT.
Definition join_oRingType := @Ring.Pack cT' clT cT.
Definition join_oUnitRingType := @UnitRing.Pack cT' clT cT.
Definition join_oComRingType := @ComRing.Pack cT' clT cT.
Definition join_oComUnitRingType := @ComUnitRing.Pack cT' clT cT.
Definition join_oIdomainType := @IntegralDomain.Pack cT' clT cT.
End Joins.

End Field.

Canonical Structure Field.eqType.
Canonical Structure Field.choiceType.
Canonical Structure Field.zmodType.
Canonical Structure Field.ringType.
Canonical Structure Field.oRingType.
Canonical Structure Field.comRingType.
Canonical Structure Field.oComRingType.
Canonical Structure Field.unitRingType.
Canonical Structure Field.oUnitRingType.
Canonical Structure Field.comUnitRingType.
Canonical Structure Field.oComUnitRingType.
Canonical Structure Field.idomainType.
Canonical Structure Field.oIdomainType.
Canonical Structure Field.fieldType.
Canonical Structure Field.join_oRingType.
Canonical Structure Field.join_oComRingType.
Canonical Structure Field.join_oUnitRingType.
Canonical Structure Field.join_oComUnitRingType.
Canonical Structure Field.join_oIdomainType.

Section FieldTheory.

Variable F : Field.type.
Implicit Types x y z t : F.

Lemma le0f_inv : forall x, (0 <= x) = (0 <= x^-1).
Proof.
move=> x; case x0: (x == 0); first by rewrite (eqP x0) invr0.
case lerP=> l0x; case lerP=> l0i //; apply/eqP.
  move: (ler_mulN (ltrW l0i) l0x); rewrite divff ?x0 //.
  by rewrite mul0r ler_nlt ltr01.
move: (ler_mulP l0i (ltrW l0x)); rewrite divff ?x0 //.
by rewrite mul0r ler_nlt ltr01.
Qed.

Lemma ltf_mulP : forall z x y, 0 < z ->  (x * z <= y * z) = (x <= y).
Proof.
move=> z x t; rewrite ltr_neqAle; case/andP; rewrite eq_sym=> zn0 zp.
apply/idP/idP; last exact: ler_mulP.
move:zp; rewrite le0f_inv=> zp; move/(ler_mulP zp).
by rewrite -!mulrA divff // !mulr1.
Qed.

Lemma ltf_mulN : forall z x y, 0 > z -> (x * z >= y * z) = (x <= y).
Proof. by move=> z x t zn; rewrite ler_opp -!mulrN ltf_mulP // signNr. Qed.

End FieldTheory.

Require Import poly.

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
Coercion oRingType cT := Ring.Pack (class cT) cT.
Coercion comRingType cT := GRing.ComRing.Pack (class cT) cT.
Coercion oComRingType cT := ComRing.Pack (class cT) cT.
Coercion unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Coercion oUnitRingType cT := UnitRing.Pack (class cT) cT.
Coercion comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Coercion oComUnitRingType cT := ComUnitRing.Pack (class cT) cT.
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

Section RealClosedFieldTheory.

Definition poly_ivt := RealClosedField.axiom.

End RealClosedFieldTheory.

Module Theory.


Definition ler_anti := ler_anti. 
Definition ler_trans := ler_trans. 
Definition ler_total := ler_total. 
Definition lerr := lerr. 
Hint Resolve lerr.

Definition ltrNge := ltrNge. 
Definition ler_add2l := ler_add2l. 
Definition ler_add2r := ler_add2r. 
Definition le0r_mul := le0r_mul.
Definition ler_sub := ler_sub. 
Definition ler_opp := ler_opp. 
Definition ler_opprC := ler_opprC. 
Definition ler_opplC := ler_opplC. 
Definition signNr := signNr.

Definition ltrW := ltrW. 
Hint Resolve ltrW.

Definition eqr_le := eqr_le. 
Definition ler_lt := ler_lt. 
Definition ler_nlt := ler_nlt. 
Definition ltr_neqAle := ltr_neqAle. 
Definition ltrWN := ltrWN. 
Hint Resolve ltrWN.

Definition ltrE := ltrE.
Definition ler_lt_trans := ler_lt_trans. 
Definition ltr_trans := ltr_trans. 
Definition ltr_le_trans := ltr_le_trans. 
Definition lerP := lerP. 
Definition ltrP := ltrP. 
Definition ltrgtP := ltrgtP. 
Definition legerP := legerP. 
Definition ler01 := ler01. 
Definition ltr01 := ltr01. 
Definition ler_add := ler_add. 
Definition ler_lt_add := ler_lt_add. 
Definition ler_addrA := ler_addrA. 
Definition ler_addlA := ler_addlA. 
Definition ler_subrA := ler_subrA. 
Definition ler_sublA := ler_sublA. 
Definition ler_subr := ler_subr.
Definition ler_subl := ler_subl.
Definition ltr_le_add := ltr_le_add. 
Definition ltr_add := ltr_add. 
Definition ler_mulP := ler_mulP. 
Definition ler_mulN := ler_mulN. 
Definition neq_ltr := neq_ltr. 
Definition ler_eqVlt := ler_eqVlt. 
Definition null_char := null_characteristic.
Definition oRing_carac := oRing_carac. 
Definition signr_comp0 := signr_comp0. 
Definition signrP := signrP. 
Definition signrN := signrN. 
Definition signr0 := signr0. 
Definition signr_opp := signr_opp. 
Definition inF3P := inF3P. 
Definition mulSN1r := mulSN1r. 
Definition oppSr := oppSr. 
Definition mulSr := mulSr. 
Definition addSr := addSr. 
Definition absr0 := absr0. 
Definition absr_opp := absr_opp. 
Definition absrP := absrP. 
Definition absrNN := absrNN.
Definition absrN := absrN. 
Definition absrNP := absrNP.
Definition absrPN := absrPN. 
Definition absr_ge0 := absr_ge0. 
Hint Resolve absr_ge0.
Definition rsign_abs := rsign_abs. 
Definition absr_eq0 := absr_eq0. 
Definition absr_lt0 := absr_lt0. 
Definition absr_le0 := absr_le0. 
Definition absrE := absrE.
Definition absr_subC := absr_subC. 
Definition ler_addr_transl := ler_addr_transl. 
Definition ler_addl_transl := ler_addl_transl. 
Definition ler_addr_transr := ler_addr_transr. 
Definition ler_addl_transr := ler_addl_transr. 
Definition absr_add_le := absr_add_le. 
Definition subr_abs_le := subr_abs_le. 
Definition absr_lt := absr_lt. 
Definition absr_le := absr_le. 
Definition absr_abs_le := absr_abs_le. 
Definition absr_leAle := absr_leAle. 
Definition absr_sub_lt := absr_sub_lt. 
Definition absr_le_lt0 := absr_le_lt0. 
Definition absr_lt_le0 := absr_lt_le0. 

Definition absfP := absfP. 
Definition absfN := absfN. 
Definition absf_lt := absf_lt. 
Definition absf_le := absf_le. 
Definition absf_leAle := absf_leAle. 
Definition absf_sub_lt := absf_sub_lt. 

Definition le0f_inv := le0f_inv. 
Definition ltf_mulP := ltf_mulP. 
Definition ltf_mulN := ltf_mulN. 

End Theory.

End OrderedRing.

Canonical Structure OrderedRing.Ring.eqType.
Canonical Structure OrderedRing.Ring.choiceType.
Canonical Structure OrderedRing.Ring.zmodType.
Canonical Structure OrderedRing.Ring.ringType.

Canonical Structure OrderedRing.ComRing.eqType.
Canonical Structure OrderedRing.ComRing.choiceType.
Canonical Structure OrderedRing.ComRing.zmodType.
Canonical Structure OrderedRing.ComRing.ringType.
Canonical Structure OrderedRing.ComRing.oRingType.
Canonical Structure OrderedRing.ComRing.comRingType.
Canonical Structure OrderedRing.ComRing.join_oRingType.

Canonical Structure OrderedRing.UnitRing.eqType.
Canonical Structure OrderedRing.UnitRing.choiceType.
Canonical Structure OrderedRing.UnitRing.zmodType.
Canonical Structure OrderedRing.UnitRing.ringType.
Canonical Structure OrderedRing.UnitRing.oRingType.
Canonical Structure OrderedRing.UnitRing.unitRingType.
Canonical Structure OrderedRing.UnitRing.join_oRingType.

Canonical Structure OrderedRing.ComUnitRing.eqType.
Canonical Structure OrderedRing.ComUnitRing.choiceType.
Canonical Structure OrderedRing.ComUnitRing.zmodType.
Canonical Structure OrderedRing.ComUnitRing.ringType.
Canonical Structure OrderedRing.ComUnitRing.oRingType.
Canonical Structure OrderedRing.ComUnitRing.comRingType.
Canonical Structure OrderedRing.ComUnitRing.oComRingType.
Canonical Structure OrderedRing.ComUnitRing.unitRingType.
Canonical Structure OrderedRing.ComUnitRing.oUnitRingType.
Canonical Structure OrderedRing.ComUnitRing.comUnitRingType.
Canonical Structure OrderedRing.ComUnitRing.join_oRingType.
Canonical Structure OrderedRing.ComUnitRing.join_oComRingType.
Canonical Structure OrderedRing.ComUnitRing.join_oUnitRingType.
Canonical Structure OrderedRing.ComUnitRing.ujoin_oComRingType.
Canonical Structure OrderedRing.ComUnitRing.cjoin_oUnitRingType.
Canonical Structure OrderedRing.ComUnitRing.fcjoin_oUnitRingType.

Canonical Structure OrderedRing.IntegralDomain.eqType.
Canonical Structure OrderedRing.IntegralDomain.choiceType.
Canonical Structure OrderedRing.IntegralDomain.zmodType.
Canonical Structure OrderedRing.IntegralDomain.ringType.
Canonical Structure OrderedRing.IntegralDomain.oRingType.
Canonical Structure OrderedRing.IntegralDomain.comRingType.
Canonical Structure OrderedRing.IntegralDomain.oComRingType.
Canonical Structure OrderedRing.IntegralDomain.unitRingType.
Canonical Structure OrderedRing.IntegralDomain.oUnitRingType.
Canonical Structure OrderedRing.IntegralDomain.comUnitRingType.
Canonical Structure OrderedRing.IntegralDomain.oComUnitRingType.
Canonical Structure OrderedRing.IntegralDomain.idomainType.
Canonical Structure OrderedRing.IntegralDomain.join_oRingType.
Canonical Structure OrderedRing.IntegralDomain.join_oComRingType.
Canonical Structure OrderedRing.IntegralDomain.join_oUnitRingType.
Canonical Structure OrderedRing.IntegralDomain.join_oComUnitRingType.

Canonical Structure OrderedRing.Field.eqType.
Canonical Structure OrderedRing.Field.choiceType.
Canonical Structure OrderedRing.Field.zmodType.
Canonical Structure OrderedRing.Field.ringType.
Canonical Structure OrderedRing.Field.oRingType.
Canonical Structure OrderedRing.Field.comRingType.
Canonical Structure OrderedRing.Field.oComRingType.
Canonical Structure OrderedRing.Field.unitRingType.
Canonical Structure OrderedRing.Field.oUnitRingType.
Canonical Structure OrderedRing.Field.comUnitRingType.
Canonical Structure OrderedRing.Field.oComUnitRingType.
Canonical Structure OrderedRing.Field.idomainType.
Canonical Structure OrderedRing.Field.oIdomainType.
Canonical Structure OrderedRing.Field.fieldType.
Canonical Structure OrderedRing.Field.join_oRingType.
Canonical Structure OrderedRing.Field.join_oComRingType.
Canonical Structure OrderedRing.Field.join_oUnitRingType.
Canonical Structure OrderedRing.Field.join_oComUnitRingType.
Canonical Structure OrderedRing.Field.join_oIdomainType.

Canonical Structure OrderedRing.RealClosedField.eqType.
Canonical Structure OrderedRing.RealClosedField.choiceType.
Canonical Structure OrderedRing.RealClosedField.zmodType.
Canonical Structure OrderedRing.RealClosedField.ringType.
Canonical Structure OrderedRing.RealClosedField.oRingType.
Canonical Structure OrderedRing.RealClosedField.comRingType.
Canonical Structure OrderedRing.RealClosedField.oComRingType.
Canonical Structure OrderedRing.RealClosedField.unitRingType.
Canonical Structure OrderedRing.RealClosedField.oUnitRingType.
Canonical Structure OrderedRing.RealClosedField.comUnitRingType.
Canonical Structure OrderedRing.RealClosedField.oComUnitRingType.
Canonical Structure OrderedRing.RealClosedField.idomainType.
Canonical Structure OrderedRing.RealClosedField.oIdomainType.
Canonical Structure OrderedRing.RealClosedField.fieldType.
Canonical Structure OrderedRing.RealClosedField.fieldType.
Canonical Structure OrderedRing.RealClosedField.oFieldType.

Bind Scope ring_scope with OrderedRing.Ring.sort.
Bind Scope ring_scope with OrderedRing.ComRing.sort.
Bind Scope ring_scope with OrderedRing.UnitRing.sort.
Bind Scope ring_scope with OrderedRing.ComUnitRing.sort.
Bind Scope ring_scope with OrderedRing.IntegralDomain.sort.
Bind Scope ring_scope with OrderedRing.Field.sort.
Bind Scope ring_scope with OrderedRing.RealClosedField.sort.

Notation oRingType := OrderedRing.Ring.type.
Notation oComRingType := OrderedRing.ComRing.type.
Notation oUnitRingType := OrderedRing.UnitRing.type.
Notation oComUnitRingType := OrderedRing.ComUnitRing.type.
Notation oIdomainType := OrderedRing.IntegralDomain.type.
Notation oFieldType := OrderedRing.Field.type.
Notation rFieldType := OrderedRing.RealClosedField.type.

Notation ORingType T m := (@OrderedRing.Ring.pack T _ m _ _ id _ id).
Notation OComRingType T m := (@OrderedRing.ComRing.pack T _ m _ _ id _ id).
Notation OUnitRingType T m := (@OrderedRing.UnitRing.pack T _ m _ _ id _ id).
Notation OComUnitRingType T m := (@OrderedRing.ComUnitRing.pack T _ m _ _ id _ id).
Notation OIdomainType T m := (@OrderedRing.IntegralDomain.pack T _ m _ _ id _ id).
Notation OFieldType T m := (@OrderedRing.Field.pack T _ m _ _ id _ id).
Notation RFieldType T m := (@OrderedRing.RealClosedField.pack T _ m _ _ id _ id).

Notation "[ 'oRingType' 'of' T ]" := (@OrderedRing.Ring.clone T _ _ id)
  (at level 0, format "[ 'oRingType'  'of'  T ]") : form_scope.
Notation "[ 'oComRingType' 'of' T ]" := (@OrderedRing.ComRing.clone T _ _ id)
  (at level 0, format "[ 'oComRingType'  'of'  T ]") : form_scope.
Notation "[ 'oUnitRingType' 'of' T ]" := (@OrderedRing.UnitRing.clone T _ _ id)
  (at level 0, format "[ 'oUnitRingType'  'of'  T ]") : form_scope.
Notation "[ 'oComUnitRingType' 'of' T ]" :=
    (@OrderedRing.ComUnitRing.clone T _ _ id)
  (at level 0, format "[ 'oComUnitRingType'  'of'  T ]") : form_scope.
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
Notation "x < y"  := (~~(y <= x)) : ring_scope.
Notation "x < y :> T" := ((x : T) < (y : T))
  (at level 70, y at next level) : ring_scope.
Notation "x > y"  := (y < x) (only parsing) : ring_scope.
Notation "x > y :> T" := ((x : T) > (y : T))
  (at level 70, y at next level) : ring_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : ring_scope.
Notation "x < y <= z" := ((x < y) && (y <= z)) : ring_scope.
Notation "x <= y < z" := ((x <= y) && (y < z)) : ring_scope.
Notation "x < y < z" := ((x < y) && (y < z)) : ring_scope.
Notation "| x |" := (OrderedRing.absr x) : ring_scope.
Notation "'\s' x" := (OrderedRing.signr x) : ring_scope.
Notation "s ?* x" := (OrderedRing.signmulr s x) : ring_scope.

