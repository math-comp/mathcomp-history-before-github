Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
Require Import bigops ssralg poly polydiv zmodp fintype.

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

Lemma subr_ge0 : forall x y, (0 <= y - x) = (x <= y).
Proof. by move=> x y; rewrite -(ler_add2l x) add0r subrK. Qed.

Lemma ler_opp2 : forall x y, (y <= x) = (-x <= -y).
Proof. by move=> x y; symmetry; rewrite -subr_ge0 opprK addrC subr_ge0. Qed.

Lemma ler_oppr : forall x y, (x <= -y) = (y <= -x).
Proof. by move=> x y; rewrite ler_opp2 opprK. Qed.
Lemma ler_oppl : forall x y, (-x <= y) = (-y <= x).
Proof. by move=> x y; rewrite ler_opp2 opprK. Qed.

Lemma oppr_ge0 : forall x, (0 <= -x) = (x <= 0).
Proof. by move=> x; rewrite ler_opp2 oppr0 opprK. Qed.
Lemma oppr_le0 : forall x, (0 >= -x) = (x >= 0).
Proof. by move=> x; rewrite ler_opp2 oppr0 opprK. Qed.
Definition oppr_cp0 := (oppr_ge0,oppr_le0).

Lemma mulr_ge0pp : forall x y, 0 <= x -> 0 <= y -> 0 <= (x * y).
Proof. by case R => T [? []]. Qed.
Lemma mulr_ge0nn : forall x y, 0 >= x -> 0 >= y -> 0 <= (x * y).
Proof. by move=> x y hx hy; rewrite -mulrNN mulr_ge0pp ?oppr_cp0. Qed.
Lemma mulr_le0pn : forall x y, 0 <= x -> 0 >= y -> 0 >= (x * y).
Proof. by move=> x y hx hy; rewrite -oppr_cp0 -mulrN mulr_ge0pp ?oppr_cp0. Qed.
Lemma mulr_le0np : forall x y, 0 >= x -> 0 <= y -> 0 >= (x * y).
Proof. by move=> x y hx hy; rewrite -oppr_cp0 -mulrN mulr_ge0nn ?oppr_cp0. Qed.
Definition mulr_cp0p := (mulr_ge0pp, mulr_le0pn).
Definition mulr_cp0n := (mulr_ge0nn, mulr_le0np).

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

Definition ltrE x y (hxy : x < y) := (hxy, (ltrWN hxy), (ltrW hxy)).

Lemma ler_lt_trans : forall y x z, x <= y -> y < z -> x < z.
Proof. move=> y x z lxy; apply: contra=> lzx; exact: ler_trans lxy. Qed.

Lemma ltr_trans : forall y x z, x < y -> y < z -> x < z.
Proof. move=> y x z; move/ltrW; exact: ler_lt_trans. Qed.

Lemma ltr_le_trans : forall y x z , x < y -> y <= z -> x < z.
Proof.
move=> y x z lxy lyz; move:lxy; apply: contra=> lzx; exact: ler_trans lzx.
Qed.

Lemma neqr_lt : forall x y, (x < y < x) = false.
Proof.
move=> x y. apply/negP; case/andP=> lxy lyx. 
by move: (ltr_trans lxy lyx); rewrite lerr.
Qed.

CoInductive le_xor_gtr (x y : R) : bool -> bool -> Set :=
  | LeNotGtr of x <= y : le_xor_gtr x y true false
  | GtrNotLe of y < x  : le_xor_gtr x y false true.

Lemma lerP : forall x y, le_xor_gtr x y (x <= y) (y < x).
Proof. by move=> x y; case hxy: (_ <= _); constructor; rewrite ?hxy //. Qed.

CoInductive ltr_xor_geq (x y : R) : bool -> bool -> Set :=
  | LtrNotGeq of x < y  : ltr_xor_geq x y false true
  | GeqNotLtr of y <= x : ltr_xor_geq x y true false.

Lemma ltrP : forall x y, ltr_xor_geq x y (y <= x) (x < y).
Proof. by move=> x y; case: (lerP y x); constructor. Qed.

CoInductive cparer x y : bool -> bool -> bool -> Set :=
  | CparerLt of x < y : cparer x y true false false
  | CparerGt of x > y : cparer x y false true false
  | CparerEq of x = y : cparer x y false false true.

Lemma ltrgtP : forall m n, cparer m n (m < n) (n < m) (m == n).
Proof.
move=> x y; case exy: (_==_); first by rewrite (eqP exy) lerr; constructor.
case: (ltrP y x); rewrite ler_lt ?exy //; last first.
  by move=> lxy; rewrite lxy; constructor.
rewrite negbK; move=> lyx; rewrite lyx; constructor.
by rewrite ltr_neqAle lyx eq_sym exy.
Qed.

Lemma lergeP : forall x y, (x <= y) || (y <= x).
Proof. by move=> x y; case: lerP=> //; move/ltrW->. Qed. 

Lemma ler01 : 0 <= 1 :> R.
Proof. 
case/orP:(ler_total 0 1); first done.
rewrite ler_opp2 oppr0=> l0m.
by move: (mulr_ge0pp l0m l0m); rewrite mulrN mulr1 opprK.
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
move=> x y z t lxy; apply: contra; rewrite ler_opp2=> lxzyt.
have:= (ler_add lxy lxzyt).
by rewrite !oppr_add !addrA !subrr !sub0r -ler_opp2.
Qed.

Lemma ltr_le_add : forall x y z t, x < y -> z <= t -> x + z < y + t.
Proof. 
move=> x y z t lxy lzt; rewrite addrC [x+_]addrC; exact: ler_lt_add. 
Qed.

Lemma ltr_add : forall x y z t, x < y -> z < t -> x + z < y + t.
Proof. move=> x y z t; move/ltrW; exact: ler_lt_add. Qed.

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

Lemma ler_addpl : forall x y z, 0 <= x -> y <= z -> y <= x + z.
Proof. move=> x y z h1 h2; rewrite -(add0r y); exact: ler_add. Qed.

Lemma ler_addpr : forall x y z, 0 <= z -> x <= y -> x <= y + z.
Proof. move=> x y z h1 h2; rewrite -(addr0 x); exact: ler_add. Qed.

Lemma ltr_addspl : forall x y z, 0 < x -> y < z -> y < x + z.
Proof. move=> x y z h1 h2; rewrite -(add0r y); exact: ltr_add. Qed.

Lemma ltr_addspr : forall x y z, 0 < z -> x < y -> x < y + z.
Proof. move=> x y z h1 h2; rewrite -(addr0 x); exact: ltr_add. Qed.


Lemma ler_addrr : forall x y,  (y <= y + x) = (0 <= x).
Proof. by move=> x y; rewrite -{1}(addr0 y) ler_add2r. Qed.

Lemma ler_addrl : forall x y, (y <= x + y) = (0 <= x).
Proof. by move=> x y; rewrite addrC ler_addrr. Qed.

Lemma ler_addll : forall x y, (x + y <= y) = (x <= 0).
Proof. by move=> x y; rewrite -{2}(add0r y) ler_add2l. Qed.

Lemma ler_addlr : forall x y, (y + x <= y) = (x <= 0).
Proof. by move=> x y; rewrite addrC ler_addll. Qed.

Lemma ltr_le_addpl : forall x y z, 0 < x -> y <= z -> y < x + z.
Proof. by move=> x y z h1 h2; rewrite (@ler_lt_trans z) // ler_addll. Qed.

Lemma ltr_le_addpr : forall x y z, 0 < x -> y <= z -> y < z + x.
Proof. by move=> x y z h1 h2; rewrite addrC ltr_le_addpl. Qed.

Lemma ltr_addpr : forall x y z, 0 <= x -> y < z -> y < x + z.
Proof. by move=> x y z h1 h2; rewrite (@ltr_le_trans z) // ler_addrl. Qed.

Lemma ltr_addpl : forall x y z, 0 <= x -> y < z -> y < z + x.
Proof. by move=> x y z h1 h2; rewrite addrC ltr_addpr. Qed.

Lemma ler_mulpr : forall z x y, 0 <= z -> (x <= y) -> (x * z <= y * z).
Proof.
move=> z x t zp lxy; rewrite -subr_ge0 -mulr_subl.
by apply: mulr_ge0pp; rewrite ?subr_ge0.
Qed.
Lemma ler_mulpl : forall z x y, 0 <= z -> (x <= y) -> (z * x <= z * y).
Proof.
move=> z x t zp lxy; rewrite -subr_ge0 -mulr_subr.
by apply: mulr_ge0pp; rewrite ?subr_ge0.
Qed.
Lemma ler_mulnr : forall z x y, 0 >= z -> (x <= y) -> (x * z >= y * z).
Proof. by move=> z x t zn lxy; rewrite ler_opp2 -!mulrN ler_mulpr// oppr_cp0. Qed.
Lemma ler_mulnl : forall z x y, 0 >= z -> (x <= y) -> (z * x >= z * y).
Proof. by move=> z x t zn lxy; rewrite ler_opp2 -!mulNr ler_mulpl// oppr_cp0. Qed.
Definition ler_mulp z x y (hz : 0 <= z) (hxy : x <= y) := 
  (ler_mulpr hz hxy, ler_mulpl hz hxy).
Definition ler_muln z x y (hz : 0 >= z) (hxy : x <= y) := 
  (ler_mulnr hz hxy, ler_mulnl hz hxy).

Lemma neq_ltr : forall x y, (x != y) = (x < y) || (y < x).
Proof. by move=> *; rewrite eqr_le negb_and orbC. Qed.

Lemma ler_eqVlt : forall x y, (x <= y) = (x == y) || (x < y).
Proof. 
move=> x y. rewrite ltr_neqAle. 
by case exy: (_==_); rewrite ?(andbT,andbF) // (eqP exy) lerr.
Qed.

Lemma gtf0Sn : forall n, 0 < (n.+1)%:R :> R.
Proof.
elim=> [|n ihn]; first by rewrite ltr01.
by rewrite -addn1 natr_add mulr1n (ltr_trans ihn)// -ler_subl subrr ltr01.
Qed.

Definition null_char := forall n : nat, (n.+1)%:R == 0 :> R = false.
Lemma charor : null_char.
Proof. by move=> n; rewrite eq_sym ltrE// gtf0Sn. Qed.

(* signr section *)
Definition signr x : 'F_3 :=  if x == 0 then 0 else if 0 <= x then 1 else -1.
Notation "'\s' x" := (signr x).

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
Lemma signr0 : \s 0 = 0. Proof. by rewrite /signr eqxx. Qed.
Lemma signr1 : \s 1 = 1. Proof. by rewrite /signr oner_eq0 ler01. Qed.

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

Definition smul (s : 'F_3) (x : R) := 
  if s == 0 then 0 else if s == 1 then x else -x.
Notation "s ?* x" := (smul s x).

Lemma smulNr : forall s x, - s ?* x = (-s) ?* x.
Proof. by move=> s x; case: (inF3P s)=> ->; rewrite ?(opprK,oppr0). Qed.

Lemma smulrN : forall s x, - (s ?* x) = s ?* (-x).
Proof. by move=> s x; case: (inF3P s)=> -> /=; rewrite ?oppr0. Qed.

Lemma smulrNN : forall s x, (s ?* x) = (-s) ?* (-x).
Proof. by move=> s x; rewrite -smulNr -smulrN opprK. Qed.

Lemma smulA : forall s s' x, s ?* (s' ?* x) = (s*s')?* x.
Proof.
by rewrite /smul=> s s' x; case: (inF3P s)=> ->; case: (inF3P s')=> ->;
rewrite //= ?(opprK, oppr0).
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
move=> s x; case: (inF3P s)=> ->; rewrite ?(signr0,mul0r,mul1r) //.
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
Definition absr x := (\s x) ?* x.
Notation "| x |" := (absr x) : ring_scope.

Lemma absrP : forall x, |x| = \s x ?* x.
Proof. done. Qed.

Lemma absr0 : |0| = 0.
Proof. by rewrite /absr /signr eqxx. Qed.

Lemma absr_opp : forall x, | -x | = |x|.
Proof. by move=> x; rewrite /absr signr_opp -smulrNN. Qed.

Lemma ger0_abs : forall x, (x >= 0) -> |x| = x.
Proof.
move=> x; rewrite /absr ler_eqVlt; case/orP=> hx; last by rewrite gtr0_sign.
by rewrite -(eqP hx) signr0.
Qed.
Definition gtr0_abs x (hx : x > 0) := ger0_abs (ltrW hx). 

Lemma ler0_abs : forall x, (x <= 0) -> |x| = -x.
Proof.
move=> x hx; rewrite -{1}[x]opprK absr_opp //.
by apply:ger0_abs; rewrite oppr_cp0.
Qed.
Definition ltr0_abs x (hx : x < 0) := ler0_abs (ltrW hx). 

Lemma absr_idVN : forall x, (|x| = x) \/ (|x| = -x).
Proof.
move=> x; case/orP:(lergeP x 0); last by move/ger0_abs->; constructor.
by move/ler0_abs->; constructor 2.
Qed.

Lemma absr_ge0 : forall x, 0 <= |x|.
Proof.
move=> x; case: (lerP x 0)=> hx; last by rewrite ger0_abs ltrW.
by rewrite ler0_abs // oppr_cp0.
Qed.
Hint Resolve absr_ge0.

Lemma smul_abs_id : forall x, x = (\s x) ?* |x|.
Proof.
move=> x; case: (ltrgtP x 0)=> hx; last by rewrite hx absr0 signr0.
  by rewrite ltr0_sign// ltr0_abs// [(-1)?*_]opprK.
by rewrite gtr0_sign// gtr0_abs.
Qed.

Lemma absr_eq0 : forall x, (|x| == 0) = (x == 0).
Proof.
move=> x; case: (ltrgtP x)=> hx; last by rewrite hx absr0 eqxx.
  by rewrite ltr0_abs// oppr_eq0 ltrE.
by rewrite gtr0_abs// eq_sym ltrE.
Qed.

Lemma absr_lt0 : forall x, |x| < 0 = false.
Proof. by move=> x; apply/negP; apply/negP. Qed.

Lemma absr_le0 : forall x, (|x| <= 0) = (x == 0).
Proof.
move=> x; rewrite -absr_eq0; case hx:(_==_).
  by move/eqP:hx->; rewrite lerr.
by rewrite ler_lt ?absr_lt0 ?hx.
Qed.

Lemma absr1 : |1| = 1 :> R.
Proof. by rewrite ger0_abs// ler01. Qed.

Definition absrE x := (absr0, absr1, absr_ge0, absr_eq0, absr_lt0, absr_le0).

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
move=> x y; case/orP: (lergeP y 0)=> hy; case/orP: (lergeP x 0)=> hx.
- move:(ler_add hx hy); rewrite addr0; move/ler0_abs->.
  by rewrite (ler0_abs hx) (ler0_abs hy) oppr_add.
- rewrite (ger0_abs hx) (ler0_abs hy); case: (absr_idVN (x+y))=> ->.
  + move: (hy); rewrite -oppr_cp0=> hNy.
    by apply: (ler_addr_transl hy); apply: (ler_addr_transr hNy).
  + rewrite oppr_add; move:(hx); rewrite -oppr_cp0=> hNx.
    by apply:(ler_addl_transl hNx); apply:(ler_addl_transr hx).
- rewrite (ler0_abs hx) (ger0_abs hy); case: (absr_idVN (x+y))=> ->.
  + move: (hx); rewrite -oppr_cp0=> hNx.
    by apply: (ler_addl_transl hx); apply: (ler_addl_transr hNx).
  + rewrite oppr_add; move:(hy); rewrite -oppr_cp0=> hNy.
    by apply:(ler_addr_transl hNy); apply:(ler_addr_transr hy).
- move:(ler_add hx hy); rewrite addr0; move/ger0_abs->.
  by rewrite (ger0_abs hx) (ger0_abs hy).
Qed.

Lemma subr_abs_le : forall x y, |x| - |y| <= | x + y |.
Proof.
move=> x y; rewrite -{1}[x](subr0) -[0](subrr y) oppr_sub addrA.
apply: (ler_addl_transl (absr_add_le _ _)). 
by rewrite absr_opp -addrA subrr addr0.
Qed.

Lemma absr_lt : forall x y, y >= 0 -> (|x| < y) = (-y < x < y).
move=> x y hy; rewrite -negb_or; apply/idP/idP; apply: contra.
  case/orP; last by move=> hxy; move: (ler_trans hy hxy)=> hx; rewrite ger0_abs.
  rewrite ler_opp2 opprK=> hxy; move: (ler_trans hy hxy)=> hx.
  by rewrite -absr_opp ger0_abs.
case:(absr_idVN x)=> ->; first by move->; rewrite orbT.
by rewrite ler_opp2 opprK; move->.
Qed.

Lemma absr_le : forall x y, y >= 0 -> (|x| <= y) = (-y <= x <= y).
Proof.
move=> x y hy; move:(hy); rewrite -oppr_cp0=> hNy; rewrite ler_eqVlt !absr_lt //.
case: (ltrgtP x 0)=> hx.
- move:(ltr_le_trans hx hy)=>hxy. rewrite !(ltrE hxy).
  by rewrite !andbT ltr0_abs // -eqr_oppC eq_sym -ler_eqVlt.
- by move:(ler_lt_trans hNy hx)=>hxy; rewrite !(ltrE hxy) gtr0_abs// -ler_eqVlt.
- by rewrite hx absr0 oppr_cp0 orb_andr -ler_eqVlt oppr_cp0.
Qed.

Lemma absr_abs_le : forall x y, | |x| - |y| | <= | x + y |.
Proof.
by move=> x y; rewrite absr_le// ler_oppl oppr_sub {1}[_+y]addrC !subr_abs_le.
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

Lemma absr_smul : forall s x, s != 0 -> |s ?* x| = |x|.
Proof.
move=> s x; case: (ltrgtP x 0)=> hx; case: (inF3P s)=> -> //= _;
by rewrite absr_opp.
Qed.

Definition minr x y := if x<=y then x else y.

Lemma ltr_minr : forall x y z, (minr x y > z) = (x > z) && (y > z).
Proof.
rewrite /minr=> x y z; case: (lerP x y)=> lxy; apply/idP/idP.
- by move=> lzx; rewrite lzx (ltr_le_trans _ lxy).
- by case/andP=> ->.
- by move=> lzy; rewrite lzy (ltr_trans _ lxy).
- by case/andP=> _ ->.
Qed.

End RingTheory.

Notation "| x |" := (absr x) : ring_scope.
Notation "s ?* x" := (smul s x).
Notation "'\s' x" := (signr x).

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
move=> x; case: lerP=> lx; first by move/ger0_abs:(lx)->; rewrite eqxx.
move/ltr0_abs:(lx)->; rewrite -eqr_oppC -subr_eq0 opprK add2r; symmetry.
by rewrite mulf_eq0 (ltrE lx) charor.
Qed.

Lemma absfn : forall x, (x <= 0) = (|x| == -x).
Proof. move=> x; rewrite -oppr_cp0 -absr_opp; exact: absfP. Qed.


Lemma absf_lt : forall x y, (|x| < y) = (-y < x < y).
Proof.
move=> x y; case: (lerP 0 y); first exact: absr_lt.
move=> hy; rewrite absr_lt_le0 ?(ltrE hy) //; symmetry.
apply/negP; case/andP=> hNyx hxy.
move: (ltr_trans (ltr_trans hNyx hxy) hy).
by rewrite oppr_cp0; move/(ltr_trans hy); rewrite lerr.
Qed.

Lemma absf_le : forall x y, (|x| <= y) = (-y <= x <= y).
Proof.
move=> x y; case: (lerP 0 y); first exact: absr_le.
move=> hy; move:(hy); move/absr_le_lt0->; symmetry.
apply/negP; case/andP=> hNyx hxy.
move: (ler_lt_trans (ler_trans hNyx hxy) hy).
by rewrite oppr_cp0; move/(ltr_trans hy); rewrite lerr.
Qed.


Lemma absf_leAle : forall z x y, (|x - y| <= z) = (y - z <= x <= y + z).
Proof. by move=> z x y; rewrite absf_le // !ler_subl. Qed.

Lemma absf_sub_lt : forall z x y, (|x - y| < z) = (y - z < x < y + z).
Proof. by move=> z x y; rewrite absf_lt // !ler_subl. Qed.

Lemma ltf_mulpr : forall z x y, 0 < z ->  (x * z <= y * z) = (x <= y).
Proof.
move=> z x t zp; apply/idP/idP; last exact: (ler_mulpr (ltrW _)).
apply: contraLR; rewrite !ltr_neqAle -subr_eq0; case/andP=> ntx ltx.
by rewrite ler_mulpr -1?subr_eq0 -?mulr_subl ?mulf_neq0// 1?eq_sym ltrE.
Qed.
Lemma ltf_mulpl : forall z x y, 0 < z ->  (z * x <= z * y) = (x <= y).
Proof. by move=> z x y hz; rewrite ![z*_]mulrC ltf_mulpr. Qed.
Definition ltf_mulp z x y (hz : 0 < z) := (ltf_mulpr x y hz, ltf_mulpl x y hz).


Lemma ltf_mulnr : forall z x y, 0 > z -> (x * z >= y * z) = (x <= y).
Proof. by move=> z x t zn; rewrite ler_opp2 -!mulrN ltf_mulp // oppr_cp0. Qed.
Lemma ltf_mulnl : forall z x y, 0 > z ->  (z * x >= z * y) = (x <= y).
Proof. by move=> z x y hz; rewrite ![z*_]mulrC ltf_mulnr. Qed.
Definition ltf_muln z x y (hz : 0 > z) := (ltf_mulnr x y hz, ltf_mulnl x y hz).

Lemma mulf_gt0pp : forall x y, x>0 -> y>0 -> (x*y)>0.
Proof. by move=> x y hx hy; rewrite -(mulr0 x) ltf_mulpl. Qed. 
Lemma mulf_gt0nn : forall x y, x<0 -> y<0 -> (x*y)>0.
Proof. by move=> x y hx hy; rewrite -mulrNN mulf_gt0pp ?oppr_cp0. Qed.
Lemma mulf_lt0pn : forall x y, x>0 -> y<0 -> (x*y)<0.
Proof. by move=> x y hx hy; rewrite -oppr_cp0 -mulrN mulf_gt0pp ?oppr_cp0. Qed.
Lemma mulf_lt0np : forall x y, x<0 -> y>0 -> (x*y)<0.
Proof. by move=> x y hx hy; rewrite mulrC mulf_lt0pn. Qed.
Definition mulf_cp0p := (mulf_gt0pp, mulf_lt0pn).
Definition mulf_cp0n := (mulf_gt0nn, mulf_lt0np).


Lemma absf_mul : forall x y, |x * y| = |x| * |y|.
Proof.
move=> x y; case: (lerP x 0)=> hx; case: (lerP y 0)=> hy.
- by rewrite ger0_abs ?mulr_cp0n// ler0_abs// ler0_abs// mulrNN.
- by rewrite ler0_abs ?mulr_cp0n// 1?ltrE// -mulNr ler0_abs// gtr0_abs.
- by rewrite ler0_abs ?mulr_cp0p// 1?ltrE// -mulrN gtr0_abs// ler0_abs.
- by rewrite gtr0_abs ?mulf_cp0p// gtr0_abs// gtr0_abs.
Qed.

Lemma ltf_expSSr : forall x n, 0 < x -> x < 1 -> x^+n.+2 < x.
Proof.
move=> x n l0x lx1; elim: n=> [|n ihn].
  by rewrite exprS expr1 -{1}[x]mul1r ltf_mulp.
by rewrite exprSr -{1}[x]mul1r ltf_mulp// (ltr_trans _ lx1).
Qed.

Lemma ltf_exprSS : forall x n, 1 < x -> x < x^+n.+2.
Proof.
move=> x n l1x; elim: n=> [|n ihn].
  rewrite exprS expr1 -{3}[x]mul1r ltf_mulp// (ler_lt_trans (ler01 _))//.
rewrite exprSr -{3}[x]mul1r ltf_mulp// ?(ltr_trans _ l1x)// ?ltr01//.
by rewrite (ltr_trans l1x)//.
Qed.

Lemma expf_gt0 : forall n x, (0 < x) -> (0 < x^+n).
Proof.
move=> n x l0x; elim: n=> [|n ihn]; first by rewrite expr0 ltr01.
by rewrite exprS mulf_gt0pp.
Qed.

Lemma expf_ge0 : forall n x, (0 <= x) -> (0 <= x^+n.+1).
Proof.
move=> n x; rewrite ler_eqVlt; case/orP=> hx; last by rewrite ltrE// expf_gt0.
by rewrite -(eqP hx) exprS mul0r lerr.
Qed.

Lemma absf_exp : forall x n, |x^+n| = |x|^+n.
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
move=> x n l0x l1x; case: (ltrgtP x 0); rewrite ?l0x//; last first.
  by move->; rewrite exprS mul0r lerr.
case: (ltrgtP x 1); rewrite ?l1x//; last by move->; rewrite exp1rn lerr.
move=> ltx1; case: n=> [|n]; first by rewrite expr1 lerr.
by move=> lt0x; rewrite ltrE// ltf_expSSr.
Qed.

Lemma lef_exprS : forall x n, 1 <= x -> x <= x^+n.+1.
Proof.
move=> x n; rewrite ler_eqVlt; case/orP=> hx.
  by rewrite -(eqP hx) exp1rn lerr.
case: n=> [|n]; first by rewrite expr1 lerr.
by rewrite ltrE// ltf_exprSS.
Qed.

Lemma lef_expS2 : forall n x y, 0 <= x -> 0 <= y -> (x <= y) = (x^+n.+1 <= y^+n.+1).
Proof.
move=> n x y l0x l0y; case: (ltrgtP x 0); rewrite ?l0x//; last first.
  by move->; rewrite exprS mul0r expf_ge0.
case: (ltrgtP y 0); rewrite ?l0y//; last first.
  move->; rewrite [0^+_]exprS mul0r=> lt0x.
  by apply/idP/idP; apply: contraLR; rewrite lt0x// expf_gt0.
elim:n =>[|n ihn]; first by rewrite !expr1.
move=> lt0y ltOx; rewrite ![_^+n.+2]exprSr; apply/idP/idP=> hxy.
  move:(hxy); rewrite -(@ltf_mulpl (x^+n.+1)); last by rewrite expf_gt0.
  by move/ler_trans=> -> //; rewrite ltf_mulp// -ihn.
apply/negP; move/negP=> hyx; move:(hyx); apply/negP; apply/negPn.
by rewrite ihn// -(@ltf_mulpr x)// (ler_trans hxy)// ltf_mulp ?expf_gt0// ltrE.
Qed.

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

Lemma invf_ge0 : forall x, (0 <= x) = (0 <= x^-1).
Proof.
move=> x; case x0: (x == 0); first by rewrite (eqP x0) invr0.
case lerP=> l0x; case lerP=> l0i //; apply/eqP.
  move: (ler_mulnr (ltrW l0i) l0x); rewrite divff ?x0 //.
  by rewrite mul0r ler_nlt ltr01.
move: (ler_mulpr l0i (ltrW l0x)); rewrite divff ?x0 //.
by rewrite mul0r ler_nlt ltr01.
Qed.
Lemma invf_le0 : forall x, (0 >= x) = (0 >= x^-1).
Proof.
move=> x; case x0: (x == 0); first by rewrite (eqP x0) invr0 lerr.
by rewrite ![_<=0]ler_lt ?invr_eq0 ?x0// invf_ge0.
Qed.
Definition invf_cp0 := (invf_ge0, invf_le0).

Lemma lef_divpr : forall z x y, 0 < z -> (x <= y / z) = (x * z <= y).
Proof.
move=> z x y z0; rewrite -(@ltf_mulp _ z)// mulrAC -mulrA divff ?mulr1//.
by rewrite eq_sym ltrE.
Qed.
Lemma lef_divpl : forall z x y, 0 < z -> (x / z <= y) = (x <= y * z).
Proof.
move=> z x y z0; rewrite -(@ltf_mulp _ z)// mulrAC -mulrA divff ?mulr1//.
by rewrite eq_sym ltrE.
Qed.
Definition lef_divp := (lef_divpr, lef_divpl).

Lemma lef_divnr : forall z x y, 0 > z -> (x <= y / z) = (x * z >= y).
Proof.
move=> z x y z0; rewrite -mulrNN -invrN lef_divpr ?oppr_cp0//.
by rewrite mulrN -ler_opp2.
Qed.
Lemma lef_divnl : forall z x y, 0 > z -> (x / z <= y) = (x >= y * z).
Proof.
move=> z x y z0; rewrite -mulrNN -invrN lef_divpl ?oppr_cp0//.
by rewrite mulrN -ler_opp2.
Qed.
Definition lef_divn := (lef_divnr, lef_divnl).

Lemma mulf_ge0 : forall x y, ((x * y) >= 0)
  = ((x >= 0) && (y >= 0) || (x <= 0) && (y <= 0)).
Proof.
move=> x y; case: (ltrgtP y 0)=> hy; first last.
- by rewrite ?hy ?mulr0 ?lerr ?andbT lergeP.
- by rewrite -lef_divpl// mul0r (ltrW hy) (negPf hy) andbT andbF orbF.
- by rewrite -lef_divnr// mul0r (ltrW hy) (negPf hy) andbT andbF.
Qed.

Lemma mulf_le0 : forall x y, ((x * y) <= 0)
  = ((x <= 0 <= y) || (y <= 0 <= x)).
Proof.
move=> x y; rewrite -mulrNN mulrN oppr_cp0 mulf_ge0 !oppr_cp0.
by congr (_||_); rewrite andbC.
Qed.

Lemma mulf_gt0 : forall x y, ((x * y) > 0) 
  = ((x > 0) && (y > 0) || (x < 0) && (y < 0)).
Proof.
move=> x y; rewrite mulf_le0 negb_or !negb_and.
by rewrite andb_orr !andb_orl !neqr_lt orbF //= [(_<0)&&_]andbC.
Qed.

Lemma mulf_lt0 : forall x y, ((x * y) < 0) 
  = ((x < 0 < y) || (y < 0 < x)).
Proof.
move=> x y; rewrite -mulrNN mulrN oppr_cp0 mulf_gt0 !oppr_cp0.
by congr (_||_); rewrite andbC.
Qed.

Lemma signr_mul : forall x y, \s (x * y) = \s x * \s y.
Proof.
move=> x y. rewrite /signr mulf_eq0.
case x0: (_ == _); case y0 : (_ == _)=> /=; rewrite ?(mulr0,mul0r) //.
rewrite mulf_ge0 [x<=0]ler_nlt [y<=0]ler_nlt !ltr_neqAle ![0==_]eq_sym ?x0 ?y0.
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

Lemma midf_le : forall x y, x <= y -> x <= (x+y)/2%:R <= y.
Proof.
move=> x y lxy; rewrite ?lef_divp ?gtf0Sn//.
by rewrite  mulrSr !mulr_addr !mulr1 ler_add2r ler_add2l lxy.
Qed.

Lemma midf_lt : forall x y, x < y -> x < (x+y)/2%:R < y.
Proof.
move=> x y lxy; rewrite ?lef_divp ?gtf0Sn//.
by rewrite  mulrSr !mulr_addr !mulr1 ler_add2r ler_add2l lxy.
Qed.


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

(* Ring Theory *)
Definition ler_anti := ler_anti. 
Definition ler_trans := ler_trans. 
Definition ler_total := ler_total. 
Definition lerr := lerr. 
Hint Resolve lerr.
Definition ler_add2r := ler_add2r.  
Definition ler_add2l := ler_add2l.  
Definition subr_ge0 := subr_ge0. 
Definition ler_opp2 := ler_opp2. 
Definition ler_oppr := ler_oppr. 
Definition ler_oppl := ler_oppl. 
Definition oppr_ge0 := oppr_ge0. 
Definition oppr_le0 := oppr_le0. 
Definition oppr_cp0 := oppr_cp0.
Definition mulr_ge0pp := mulr_ge0pp. 
Definition mulr_ge0nn := mulr_ge0nn. 
Definition mulr_le0pn := mulr_le0pn. 
Definition mulr_le0np := mulr_le0np. 
Definition mulr_cp0p := mulr_cp0p.
Definition mulr_cp0n := mulr_cp0n.
Definition ltrW := ltrW. 
Hint Resolve ltrW.
Definition eqr_le := eqr_le. 
Definition neqr_lt := neqr_lt.
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
Definition lergeP := lergeP. 
Definition ler01 := ler01. 
Definition ltr01 := ltr01. 
Definition ler_add := ler_add. 
Definition ler_lt_add := ler_lt_add. 
Definition ltr_le_add := ltr_le_add. 
Definition ltr_add := ltr_add. 
Definition ler_addrA := ler_addrA. 
Definition ler_addlA := ler_addlA. 
Definition ler_subrA := ler_subrA. 
Definition ler_sublA := ler_sublA. 
Definition ler_subr := ler_subr.
Definition ler_subl := ler_subl.
Definition ler_addpl := ler_addpl.
Definition ler_addpr := ler_addpr.
Definition ltr_addspl := ltr_addspl.
Definition ltr_addspr := ltr_addspr.
Definition ler_addrr := ler_addrr.
Definition ler_addrl := ler_addrl.
Definition ler_addll := ler_addll.
Definition ler_addlr := ler_addlr.
Definition ltr_le_addpl := ltr_le_addpl.
Definition ltr_le_addpr := ltr_le_addpr.
Definition ltr_addpr := ltr_addpr.
Definition ltr_addpl := ltr_addpl.
Definition ler_mulpr := ler_mulpr. 
Definition ler_mulpl := ler_mulpl. 
Definition ler_mulnr := ler_mulnr. 
Definition ler_mulnl := ler_mulnl. 
Definition ler_mulp := ler_mulp.
Definition ler_muln := ler_muln.
Definition neq_ltr := neq_ltr. 
Definition ler_eqVlt := ler_eqVlt. 
Definition gtf0Sn := gtf0Sn. 
Definition null_char := null_char.
Definition charor := charor. 

Definition mulss := mulss.
Definition muls_eqA := muls_eqA.
Definition signr_cp0 := signr_cp0. 
Definition gtr0_sign := gtr0_sign. 
Definition ltr0_sign := ltr0_sign. 
Definition signr0 := signr0. 
Definition signr_opp := signr_opp. 
Definition signr1 :=  signr1.
Definition inF3P := inF3P. 
Definition signr_smul := signr_smul.

Definition smulNr := smulNr.
Definition smulrN := smulrN.
Definition smulrNN := smulrNN.
Definition smulA := smulA.
Definition addr_smul := addr_smul.
Definition smul_add := smul_add.
Definition smulr_mul := smulr_mul.
Definition smul1_eq0 := smul1_eq0.

Definition absr :=  absr.
Definition absr0 := absr0. 
Definition absr1 := absr1. 
Definition absr_opp := absr_opp. 
Definition ger0_abs := ger0_abs. 
Definition gtr0_abs := gtr0_abs.
Definition ler0_abs := ler0_abs. 
Definition ltr0_abs := ltr0_abs.
Definition absr_idVN := absr_idVN. 
Definition absr_ge0 := absr_ge0. 
Definition smul_abs_id := smul_abs_id. 
Definition absr_eq0 := absr_eq0. 
Definition absr_lt0 := absr_lt0. 
Definition absr_le0 := absr_le0. 
Definition absrE := absrE.
Hint Resolve absrE.

Definition absr_subC := absr_subC. 
Definition absr_smul := absr_smul.

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
Definition absr_le_lt0:= absr_le_lt0. 
Definition absr_lt_le0 := absr_lt_le0. 

Definition minr := minr.
Definition ltr_minr := ltr_minr. 

Definition absrP := absrP.

(* Idomain Theory *)
Definition absfP := absfP. 
Definition absfn := absfn. 
Definition absf_lt := absf_lt. 
Definition absf_le := absf_le. 
Definition absf_leAle := absf_leAle. 
Definition absf_sub_lt := absf_sub_lt. 
Definition ltf_mulpr := ltf_mulpr. 
Definition ltf_mulpl := ltf_mulpl. 
Definition ltf_mulp := ltf_mulp.
Definition ltf_mulnr := ltf_mulnr. 
Definition ltf_mulnl := ltf_mulnl. 
Definition ltf_muln  := ltf_muln.
Definition mulf_gt0pp := mulf_gt0pp. 
Definition mulf_gt0nn := mulf_gt0nn. 
Definition mulf_lt0pn := mulf_lt0pn. 
Definition mulf_lt0np := mulf_lt0np. 
Definition mulf_cp0p := mulf_cp0p.
Definition mulf_cp0n := mulf_cp0n.
Definition absf_mul := absf_mul. 
Definition ltf_expSSr := ltf_expSSr. 
Definition ltf_exprSS := ltf_exprSS. 
Definition expf_gt0 := expf_gt0. 
Definition expf_ge0 := expf_ge0. 
Definition lef_expSr := lef_expSr. 
Definition lef_exprS := lef_exprS. 
Definition lef_expS2 := lef_expS2. 
Definition smul_exp := smul_exp. 
Definition absf_exp := absf_exp. 

(* Field Theory *)
Definition signr_mul := signr_mul.
Definition signr_mulrn := signr_mulrn.
Definition signr_exp := signr_exp.
Definition mulf_ge0 := mulf_ge0.
Definition mulf_le0 := mulf_le0.
Definition mulf_gt0 := mulf_gt0.
Definition mulf_lt0 := mulf_lt0.
Definition invf_ge0 := invf_ge0. 
Definition invf_le0 := invf_le0. 
Definition invf_cp0 := invf_cp0.
Definition lef_divpr := lef_divpr. 
Definition lef_divnr := lef_divnr.
Definition lef_divpl := lef_divpl. 
Definition lef_divnl := lef_divnl.
Definition lef_divp := lef_divp. 
Definition lef_divn := lef_divn.
Definition midf_le := midf_le.
Definition midf_lt := midf_lt.

(* RCF Theory *)
Definition poly_ivt := poly_ivt.

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
Notation "s ?* x" := (OrderedRing.smul s x) : ring_scope.

