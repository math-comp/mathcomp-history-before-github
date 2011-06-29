Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
Require Import bigop ssralg orderedalg poly.
Import GRing.Theory OrderedRing.Theory.

 (****************************************************************)
 (* zint has two constructors : Posz for positive integers       *)
 (*                         and Negz for non positive integers   *)
 (*         NegzE : turns (Negz n) into (- n.+1)                 *)
 (*                                                              *)
 (*        n%:Z == explicit cast from nat to zint (with n : nat) *)
 (*      x *~ n == n times x, with n in zint                     *)
 (*                convertible to x *+ m if n is Posz m          *)
 (*                convertible to x *- m.+1 if n is Negz m       *)
 (*       n%:~R := 1 *~ n                                        *)
 (*                                                              *)
 (*      x ^ n == x to the n, with n in zint                     *)
 (*                convertible to x ^+ m if n is Posz m          *)
 (*                convertible to x ^- m.+1 if n is Negz m       *)
 (*                                                              *)
 (*        sgz x == sign of x : R,                               *)
 (*                equals (0 : zint) if and only x == 0,         *)
 (*                equals (1 : zint) if x is positive            *)
 (*                and (-1 : zint) otherwise                     *)
 (*                                                              *)
 (*       absz n == (m : nat) such that m%:Z = `|n|              *)
 (****************************************************************)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope zint_scope with Z.
Local Open Scope zint_scope.

(* Defining zint *)
CoInductive zint : Set := Posz of nat | Negz of nat.
Coercion Posz : nat >-> zint.

Notation "n %:Z" := (n : zint)
  (at level 2, left associativity, format "n %:Z")  : zint_scope.

Definition natsum_of_zint (m : zint) : nat + nat :=
  match m with Posz p => inl _ p | Negz n => inr _ n end.

Definition zint_of_natsum (m : nat + nat) :=
  match m with inl p => Posz p | inr n => Negz n end.

Lemma natsum_of_zintK : cancel natsum_of_zint zint_of_natsum.
Proof. by case. Qed.

Definition zint_eqMixin := CanEqMixin natsum_of_zintK.
Definition zint_countMixin := CanCountMixin natsum_of_zintK.
Definition zint_choiceMixin := CountChoiceMixin zint_countMixin.
Canonical zint_eqType := Eval hnf in EqType zint zint_eqMixin.
Canonical zint_choiceType := Eval hnf in ChoiceType zint zint_choiceMixin.
Canonical zint_countType := Eval hnf in CountType zint zint_countMixin.

Lemma eqz_nat (m n : nat) : (m == n :> zint) = (m == n :> nat).
Proof. by move: m n=> [|m] [|n]. Qed.

Module zintZmod.

Definition addz (m n : zint) :=
  match m, n with
    | Posz m', Posz n' => Posz (m' + n')
    | Negz m', Negz n' => Negz (m' + n').+1
    | Posz m', Negz n' => if n' < m' then Posz (m' - n'.+1) else Negz (n' - m')
    | Negz n', Posz m' => if n' < m' then Posz (m' - n'.+1) else Negz (n' - m')
  end.

Definition oppz m := nosimpl
  match m with
    | Posz n => if n is (n'.+1)%N then Negz n' else Posz 0
    | Negz n => Posz (n.+1)%N
  end.

Local Notation "0" := (0 : zint) : zint_scope.
Local Notation "-%Z" := (@oppz) : zint_scope.
Local Notation "- x" := (oppz x) : zint_scope.
Local Notation "+%Z" := (@addz) : zint_scope.
Local Notation "x + y" := (addz x y) : zint_scope.
Local Notation "x - y" := (x + - y) : zint_scope.

Lemma PoszD : {morph Posz : m n / (m + n)%N >-> m + n}. Proof. done. Qed.

Lemma NegzE (n : nat) : Negz n = -(n.+1). Proof. done. Qed.

Lemma zint_rect (P : zint -> Type) :
  P 0 -> (forall n : nat, P n -> P (n.+1))
  -> (forall n : nat, P (- n) -> P (- (n.+1)))
  -> forall n : zint, P n.
Proof.
by move=> P0 hPp hPn []; elim=> [|n ihn]//; do? [apply: hPn | apply: hPp].
Qed.

Definition zint_rec := zint_rect.
Definition zint_ind := zint_rect.

CoInductive zint_spec (x : zint) : zint -> Type :=
| ZintNull of x = 0 : zint_spec x 0
| ZintPos n of x = n.+1 : zint_spec x n.+1
| ZintNeg n of x = - (n.+1)%:Z : zint_spec x (- n.+1).

Lemma zintP x : zint_spec x x. Proof. by move: x=> [] []; constructor. Qed.

Lemma addzC : commutative addz.
Proof. by move=> [] m [] n //=; rewrite addnC. Qed.

Lemma add0z : left_id 0 addz. Proof. by move=> [] [|]. Qed.

Lemma oppzK : involutive oppz. Proof. by do 2?case. Qed.

Lemma oppz_add : {morph oppz : m n / m + n}.
Proof.
move=> [[|n]|n] [[|m]|m] /=; rewrite ?NegzE ?oppzK ?addnS ?addn0 ?subn0 //;
  rewrite ?ltnS[m <= n]leqNgt [n <= m]leqNgt; case: ltngtP=> hmn /=;
    by rewrite ?hmn ?subnn // ?oppzK ?subSS -?predn_sub ?prednK // ?subn_gt0.
Qed.

Lemma add1Pz (n : zint) : 1 + (n - 1) = n.
Proof. by case: (zintP n)=> // n' /= _; rewrite ?(subn1, addn0). Qed.

Lemma subSz1 (n : zint) : 1 + n - 1 = n.
Proof.
by apply: (inv_inj oppzK); rewrite addzC !oppz_add oppzK [_ - n]addzC add1Pz.
Qed.

Lemma addSnz (m : nat) (n : zint) : (m.+1%N) + n = 1 + (m + n).
Proof.
move: m n=> [|m] [] [|n] //=; rewrite ?add1n ?subn1 // !(ltnS, subSS).
rewrite [n <= m]leqNgt; case: ltngtP=> hmn /=; rewrite ?hmn ?subnn //.
  by rewrite -predn_sub add1n prednK ?subn_gt0.
by rewrite ltnS leqn0 subn_eq0 leqNgt hmn /= -predn_sub subn1.
Qed.

Lemma addSz (m n : zint) : (1 + m) + n = 1 + (m + n).
Proof.
case: m => [] m; first by rewrite -PoszD add1n addSnz.
rewrite !NegzE; apply: (inv_inj oppzK).
rewrite !oppz_add !oppzK addSnz [-1%:Z + _]addzC addSnz add1Pz.
by rewrite [-1%:Z + _]addzC subSz1.
Qed.

Lemma addPz (m n : zint) : (m - 1) + n = (m + n) - 1.
Proof.
by apply: (inv_inj oppzK); rewrite !oppz_add oppzK [_ + 1]addzC addSz addzC.
Qed.

Lemma addzA : associative addz.
Proof.
elim=> [|m ihm|m ihm] n p; first by rewrite !add0z.
  by rewrite -add1n PoszD !addSz ihm.
by rewrite -add1n addnC PoszD oppz_add !addPz ihm.
Qed.

Lemma addNz : left_inverse (0:zint) oppz addz. Proof. by do 3?elim. Qed.

Lemma predn_zint (n : nat) : 0 < n -> n.-1%:Z = n - 1.
Proof. by case: n=> // n _ /=; rewrite subn1. Qed.

Definition Mixin := ZmodMixin addzA addzC add0z addNz.

End zintZmod.

Canonical zint_ZmodType := ZmodType zint zintZmod.Mixin.

Notation "n %:Z" := (n : zint)
  (at level 2, left associativity, format "n %:Z")  : ring_scope.

Local Open Scope ring_scope.

Section zintZmoduleTheory.

Lemma PoszD : {morph Posz : n m / (n + m)%N >-> n + m}. Proof. done. Qed.

Lemma NegzE (n : nat) : Negz n = -(n.+1)%:Z. Proof. done. Qed.

Lemma zint_rect (P : zint -> Type) :
  P 0 -> (forall n : nat, P n -> P (n.+1)%N)
  -> (forall n : nat, P (- (n%:Z)) -> P (- (n.+1%N%:Z)))
  -> forall n : zint, P n.
Proof.
by move=> P0 hPp hPn []; elim=> [|n ihn]//; do? [apply: hPn | apply: hPp].
Qed.

Definition zint_rec := zint_rect.
Definition zint_ind := zint_rect.

CoInductive zint_spec (x : zint) : zint -> Type :=
| ZintNull : zint_spec x 0
| ZintPos n : zint_spec x n.+1
| ZintNeg n : zint_spec x (- (n.+1)%:Z).

Lemma zintP x : zint_spec x x.
Proof. by move: x=> [] [] *; rewrite ?NegzE; constructor. Qed.

Definition oppz_add := (@oppr_add [zmodType of zint]).

Lemma subzn (m n : nat) : (n <= m)%N -> m%:Z - n%:Z = (m - n)%N.
Proof.
elim: n=> //= [|n ihn] hmn; first by rewrite subr0 subn0.
rewrite -predn_sub -addn1 !PoszD oppr_add addrA ihn 1?ltnW //.
by rewrite zintZmod.predn_zint // subn_gt0.
Qed.

Lemma subzSS (m n : nat) : m.+1%:Z - n.+1%:Z = m%:Z - n%:Z.
Proof. by elim: n m=> [|n ihn] m //; rewrite !subzn. Qed.

End zintZmoduleTheory.

Module zintRing.

Definition mulz (m n : zint) :=
  match m, n with
    | Posz m', Posz n' => (m' * n')%N%:Z
    | Negz m', Negz n' => (m'.+1%N * n'.+1%N)%N%:Z
    | Posz m', Negz n' => - (m' * (n'.+1%N))%N%:Z
    | Negz n', Posz m' => - (m' * (n'.+1%N))%N%:Z
  end.

Local Notation "1" := (1%N:zint) : zint_scope.
Local Notation "*%Z" := (@mulz) : zint_scope.
Local Notation "x * y" := (mulz x y) : zint_scope.

Lemma mul0z : left_zero 0 *%Z.
Proof. by case=> [n|[|n]] //=; rewrite muln0. Qed.

Lemma mulzC : commutative mulz.
Proof. by move=> [] m [] n //=; rewrite mulnC. Qed.

Lemma mulz0 : right_zero 0 *%Z.
Proof. by move=> x; rewrite mulzC mul0z. Qed.

Lemma mulzN (m n : zint) : (m * (- n))%Z = - (m * n)%Z.
Proof.
by case: (zintP m)=> {m} [|m|m]; rewrite ?mul0z //;
case: (zintP n)=> {n} [|n|n]; rewrite ?mulz0 //= mulnC.
Qed.

Lemma mulNz (m n : zint) : ((- m) * n)%Z = - (m * n)%Z.
Proof. by rewrite mulzC mulzN mulzC. Qed.

Lemma mulzA : associative mulz.
Proof.
by move=> [] m [] n [] p; rewrite ?NegzE ?(mulnA,mulNz,mulzN,opprK) //= ?mulnA.
Qed.

Lemma mul1z : left_id 1%Z mulz.
Proof. by case=> [[|n]|n] //=; rewrite ?mul1n// plusE addn0. Qed.

Lemma mulzS (x : zint) (n : nat) : (x * n.+1%:Z)%Z = x + (x * n)%Z.
Proof.
by case: (zintP x)=> [|m'|m'] //=; [rewrite mulnS|rewrite mulSn -oppr_add].
Qed.

Lemma mulz_addl : left_distributive mulz (+%R).
Proof.
move=> x y z; elim: z=> [|n|n]; first by rewrite !(mul0z,mulzC).
  by rewrite !mulzS=> ->; rewrite !addrA [X in X + _]addrAC.
rewrite !mulzN !mulzS -!oppr_add=> /(inv_inj (@opprK _))->.
by rewrite !addrA [X in X + _]addrAC.
Qed.

Lemma nonzero1z : 1%Z != 0. Proof. done. Qed.

Definition comMixin := ComRingMixin mulzA mulzC mul1z mulz_addl nonzero1z.

End zintRing.

Canonical zint_Ring := Eval hnf in RingType zint zintRing.comMixin.
Canonical zint_comRing := Eval hnf in ComRingType zint zintRing.mulzC.

Section zintRingTheory.

Implicit Types m n : zint.

Lemma PoszM : {morph Posz : n m / (n * m)%N >-> n * m}. Proof. done. Qed.

Lemma zintS (n : nat) : n.+1%:Z = 1 + n%:Z. Proof. by rewrite -PoszD. Qed.

Lemma predn_zint (n : nat) : (0 < n)%N -> n.-1%:Z = n%:Z - 1.
Proof. exact: zintZmod.predn_zint. Qed.

End zintRingTheory.

Module zintUnitRing.
Section zintUnitRing.
Implicit Types m n : zint.

Definition unitz := [pred n : zint | (n == 1) || (n == -1)].
Definition invz n : zint := n.

Lemma mulVz : {in unitz, left_inverse 1%R invz *%R}.
Proof. by move=> n; rewrite !inE; case/orP; move/eqP->. Qed.

Lemma mulzn_eq1 m (n : nat) : (m * n == 1) = (m == 1) && (n == 1%N).
Proof. by case: m=> m /=; [rewrite -PoszM [_==_]eqn_mul1 | case: n]. Qed.

Lemma unitzPl m n : n * m = 1 -> unitz m.
Proof.
case: m=> m; move/eqP; rewrite !inE //=.
* by rewrite mulzn_eq1; case/andP=> _; move/eqP->.
* by rewrite NegzE zintS mulrN -mulNr mulzn_eq1; case/andP=> _.
Qed.

Lemma  invz_out : {in predC unitz, invz =1 id}.
Proof. exact. Qed.

Lemma idomain_axiomz m n : m * n = 0 -> (m == 0) || (n == 0).
Proof.
by case: m n => m [] n //=; move/eqP; rewrite ?(NegzE,mulrN,mulNr);
  rewrite ?(inv_eq (@opprK _)) -PoszM [_==_]muln_eq0.
Qed.

Definition comMixin := ComUnitRingMixin mulVz unitzPl invz_out.

End zintUnitRing.
End zintUnitRing.

Canonical zint_unitRingType :=
  Eval hnf in UnitRingType zint zintUnitRing.comMixin.
Canonical zint_comUnitRing := Eval hnf in [comUnitRingType of zint].
Canonical zint_iDomain := Eval hnf in IdomainType zint
  zintUnitRing.idomain_axiomz.

Module zintOrdered.
Section zintOrdered.
Implicit Types m n p : zint.

Definition lez m n :=
  match m, n with
    | Posz m', Posz n' => (m' <= n')%N
    | Posz m', Negz n' => false
    | Negz m', Posz n' => true
    | Negz m', Negz n' => (n' <= m')%N
  end.

Fact addz_ge0 m n : lez 0 m -> lez 0 n -> lez 0 (m + n).
Proof. by move: m n=> [] ? []. Qed.

Fact mulz_ge0 m n : lez 0 m -> lez 0 n -> lez 0 (m * n).
Proof. by move: m n=> [] ? []. Qed.

Lemma lez0_anti n : lez 0 n -> lez 0 (- n) -> n = 0.
Proof. by move: n=> [[]|]. Qed.

Lemma lez_nat (m n : nat) : (lez m n) = (m <= n)%N. Proof. by []. Qed.

Lemma subz_ge0 m n : lez m n = lez 0 (n - m).
Proof.
case: (zintP m); case: (zintP n)=> // {m n} m n /=;
rewrite ?ltnS -?oppr_add ?oppr_sub ?subzSS;
case: leqP=> // hmn; do
  ?[ by rewrite subzn //
   | by rewrite -oppr_sub subzn ?(ltnW hmn) //;
     move: hmn; rewrite -subn_gt0; case: (_ - _)%N].
Qed.

Lemma lez0_total n : lez 0 n || lez 0 (- n). Proof. by case: n. Qed.

Definition Mixin :=
  TotalOrder_PartialMixin addz_ge0 mulz_ge0 lez0_anti subz_ge0 lez0_total.

End zintOrdered.
End zintOrdered.

Canonical zint_poIdomainType := POIdomainType zint zintOrdered.Mixin.
Canonical zint_oIdomainType := OIdomainType zint zintOrdered.lez0_total.

Section zintOrderedTheory.

Implicit Types m n p : nat.
Implicit Types x y z : zint.

Lemma lez_nat m n : (m <= n :> zint) = (m <= n)%N. Proof. by []. Qed.

Lemma ltz_nat  m n : (m < n :> zint) = (m < n)%N.
Proof. by rewrite ltnNge ltrNge lez_nat. Qed.

Definition ltez_nat := (lez_nat, ltz_nat).

Lemma leNz_nat m n : (- m%:Z <= n). Proof. by case: m. Qed.

Lemma ltNz_nat m n : (- m%:Z < n) = (m != 0%N) || (n != 0%N).
Proof. by move: m n=> [|?] []. Qed.

Definition lteNz_nat := (leNz_nat, ltNz_nat).

Lemma lezN_nat m n : (m%:Z <= - n%:Z) = (m == 0%N) && (n == 0%N).
Proof. by move: m n=> [|?] []. Qed.

Lemma ltzN_nat m n : (m%:Z < - n%:Z) = false.
Proof. by move: m n=> [|?] []. Qed.

Lemma le0z_nat n : 0 <= n :> zint. Proof. by []. Qed.

Lemma lez0_nat n : n <= 0 :> zint = (n == 0%N :> nat). Proof. by elim: n. Qed.

Definition ltezN_nat := (lezN_nat, ltzN_nat).
Definition ltez_natE := (ltez_nat, lteNz_nat, ltezN_nat, le0z_nat, lez0_nat).

Lemma gtz0_ge1 x : (0 < x) = (1 <= x). Proof. by case: (zintP x). Qed.

Lemma lez_add1r x y : (1 + x <= y) = (x < y).
Proof. by rewrite -subr_gt0 gtz0_ge1 lter_sub_addr. Qed.

Lemma lez_addr1 x y : (x + 1 <= y) = (x < y).
Proof. by rewrite addrC lez_add1r. Qed.

Lemma ltz_add1r x y : (x < 1 + y) = (x <= y).
Proof. by rewrite -lez_add1r ler_add2l. Qed.

Lemma ltz_addr1 x y : (x < y + 1) = (x <= y).
Proof. by rewrite -lez_addr1 ler_add2r. Qed.

End zintOrderedTheory.


(* definition of zintmul *)
Definition zintmul (R : zmodType) (x : R) (n : zint) := nosimpl
  match n with
    | Posz n => (x *+ n)%R
    | Negz n => (x *- (n.+1))%R
  end.

Notation "*~%R" := (@zintmul _) (at level 0) : ring_scope.
Notation "x *~ n" := (zintmul x n)
  (at level 40, left associativity, format "x  *~  n") : ring_scope.
Notation "n %:~R" := (1 *~ n)%R
  (at level 2, left associativity, format "n %:~R")  : ring_scope.

Lemma natmulP (R : zmodType) (x : R) (n : nat) : x *+ n = x *~ n.
Proof. by []. Qed.

Lemma natmulN (R : zmodType) (x : R) (n : nat) : x *- n = x *~ - n%:Z.
Proof. by case: n=> [] //; rewrite ?oppr0. Qed.

Module MzintLmod.
Section MzintLmod.

Variable M : zmodType.

Implicit Types m n : zint.
Implicit Types x y z : M.

Lemma mulrzA_rev m n x : (x *~ n) *~ m = x *~ (m * n).
Proof.
elim: m=> [|m _|m _]; elim: n=> [|n _|n _]; rewrite /zintmul //=;
rewrite ?(muln0, mulr0n, mul0rn, oppr0, mulNrn, opprK) //;
 do ?by rewrite mulnC mulrnA.
* by rewrite -mulrnA mulnC.
* by rewrite -mulrnA.
Qed.

Lemma mulr1z (x : M) : x *~ 1 = x. Proof. done. Qed.

Lemma mulrz_addr m : {morph ( *~%R^~ m : M -> M) : x y / x + y}.
Proof.
by elim: m=> [|m _|m _] x y;
  rewrite ?addr0 /zintmul //= ?mulrn_addl // oppr_add.
Qed.

Lemma mulrz_subl_nat (m n : nat) x : x *~ (m%:Z - n%:Z) = x *~ m - x *~ n.
Proof.
case: (leqP m n)=> hmn; rewrite /zintmul //=.
  rewrite addrC -{1}[m:zint]opprK -oppr_add subzn //.
  rewrite -{2}[n](@subnKC m)// mulrn_addr oppr_add addrA subrr sub0r.
  by case hdmn: (_ - _)%N=> [|dmn] /=; first by rewrite mulr0n oppr0.
have hnm := ltnW hmn.
rewrite  -{2}[m](@subnKC n)// mulrn_addr addrAC subrr add0r.
by rewrite subzn.
Qed.

Lemma mulrz_addl x : {morph *~%R x : m n / m + n}.
Proof.
elim=> [|m _|m _]; elim=> [|n _|n _]; rewrite /zintmul //=;
rewrite -?(oppr_add) ?(add0r, addr0, mulrn_addr, subn0) //.
* by rewrite -/(zintmul _ _) mulrz_subl_nat.
* by rewrite -/(zintmul _ _) addrC mulrz_subl_nat addrC.
* by rewrite -addnS -addSn mulrn_addr.
Qed.

Local Notation "n *z x" := (zintmul x n)
  (at level 41, right associativity, format "n  *z  x") : ring_scope.

Definition Mzint_LmodMixin :=
  @LmodMixin _ [zmodType of M] (fun n x => n *z x) mulrzA_rev mulr1z mulrz_addr mulrz_addl.
Canonical Mzint_LmodType := LmodType zint M Mzint_LmodMixin.

Lemma mulrzA x m n :  x *~ (m * n) = x *~ m *~ n.
Proof. by rewrite mulrC -mulrzA_rev. Qed.

Lemma mulr0z x : x *~ 0 = 0. Proof. done. Qed.
Lemma mul0rz n : 0 *~ n = 0 :> M. Proof. exact: scaler0. Qed.

Lemma mulrNz x n : x *~ (- n) = - (x *~ n).
Proof. by move: scaleNr x; apply. Qed.

Lemma mulrN1z x : x *~ (- 1) = - x. Proof. by move: scaleN1r x; apply. Qed.

Lemma mulNrz x n : (- x) *~ n = - (x *~ n). Proof. by move: scalerN x; apply. Qed.

Lemma mulrz_subr x m n : x *~ (m - n) = x *~ m - x *~ n.
Proof. by move: scaler_subl x; apply. Qed.

Lemma mulrz_subl x y n : (x - y) *~ n = x *~ n - y *~ n.
Proof. by move: scaler_subr x y; apply. Qed.

Lemma mulrz_nat (n : nat) x : n%:R *z x = x *+ n.
Proof. by move: scaler_nat x; apply. Qed.

Lemma mulrz_zint (n : nat) x : n%:~R *z x = x *~ n.
Proof. exact: mulrz_nat. Qed.

Lemma mulrz_sumr : forall x I r (P : pred I) F,
  x *~ (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) x *~ F i.
Proof. exact: scaler_suml. Qed.

Lemma mulrz_suml : forall n I r (P : pred I) (F : I -> M),
  (\sum_(i <- r | P i) F i) *~ n= \sum_(i <- r | P i) F i *~ n.
Proof. exact: scaler_sumr. Qed.

End MzintLmod.
End MzintLmod.

Definition mulrzA := MzintLmod.mulrzA.
Definition mulr1z := MzintLmod.mulr1z.
Definition mulrz_addl := MzintLmod.mulrz_addl.
Definition mulrz_addr := MzintLmod.mulrz_addr.
Definition mulr0z := MzintLmod.mulr0z.
Definition mul0rz := MzintLmod.mul0rz.
Definition mulNrz := MzintLmod.mulNrz.
Definition mulrN1z := MzintLmod.mulrN1z.
Definition mulrNz := MzintLmod.mulrNz.
Definition mulrz_subr := MzintLmod.mulrz_subr.
Definition mulrz_subl := MzintLmod.mulrz_subl.
Definition mulrz_nat := MzintLmod.mulrz_nat.
Definition mulrz_sumr := MzintLmod.mulrz_sumr.
Definition mulrz_suml := MzintLmod.mulrz_suml.

Lemma zintz n : n%:~R = n.
Proof.
elim: n=> //= n ihn; rewrite /zintmul /=.
  by rewrite -addn1 mulrn_addr /= PoszD -ihn.
by rewrite natmulN zintS oppr_add mulrz_addl ihn.
Qed.

Section RzintMod.

Variable R : ringType.

Implicit Types m n : zint.
Implicit Types x y z : R.

Lemma mulrzAl n x y : (x *~ n) * y = (x * y) *~ n.
Proof.
by elim: n=> //= *; rewrite ?mul0r ?mulr0z // /zintmul /= -mulrnAl -?mulNr.
Qed.

Lemma mulrzAr n x y : x * (y *~ n) = (x * y) *~ n.
Proof.
by elim: n=> //= *; rewrite ?mulr0 ?mulr0z // /zintmul /= -mulrnAr -?mulrN.
Qed.

Lemma mulrzl x n : n%:~R * x = x *~ n.
Proof. by rewrite mulrzAl mul1r. Qed.

Lemma mulrzr x n : x * n%:~R = x *~ n.
Proof. by rewrite mulrzAr mulr1. Qed.

Lemma mulNrNz n x : (-x) *~ (-n) = x *~ n.
Proof. by rewrite mulNrz mulrNz opprK. Qed.

Lemma mulrbz x (b : bool) : x *~ b = (if b then x else 0).
Proof. by case: b. Qed.

Lemma zintr_add m n : (m + n)%:~R = m%:~R + n%:~R :> R.
Proof. exact: mulrz_addl. Qed.

Lemma zintr_mul m n : (m * n)%:~R = m%:~R * n%:~R :> R.
Proof. by rewrite mulrzA -mulrzr. Qed.

Lemma zintmul1_is_rmorphism : rmorphism ( *~%R (1 : R)).
Proof.
by do ?split; move=> // x y /=; rewrite ?zintr_add ?mulrNz ?zintr_mul.
Qed.

Canonical zintmul1_rmorphism := RMorphism zintmul1_is_rmorphism.

End RzintMod.

Lemma mulrzz m n : m *~ n = m * n. Proof. by rewrite -mulrzr zintz. Qed.

Section LMod.

Variable R : ringType.
Variable V : (lmodType R).

Implicit Types m n : zint.
Implicit Types x y z : R.
Implicit Types u v w : V.

Lemma scalezr n v : n%:~R *: v = v *~ n.
Proof.
elim: n=> [|n ihn|n ihn]; first by rewrite scale0r.
  by rewrite zintS !mulrz_addl scaler_addl ihn scale1r.
by rewrite zintS oppr_add !mulrz_addl scaler_addl ihn scaleN1r.
Qed.

Lemma scaler_mulrzl a v n : (a *: v) *~ n = (a *~ n) *: v.
Proof. by rewrite -mulrzl -scalezr scalerA. Qed.

Lemma scaler_mulrzr a v n : (a *: v) *~ n = a *: (v *~ n).
Proof. by rewrite -!scalezr !scalerA mulrzr mulrzl. Qed.

End LMod.

Section MorphTheory.
Section Additive.
Variables (U V : zmodType) (f : {additive U -> V}).

Lemma raddfMz n : {morph f : x / x *~ n}.
Proof.
case: n=> n x /=; first exact: raddfMn.
by rewrite NegzE !mulrNz; apply: raddfMNn.
Qed.

End Additive.

Section Multiplicative.

Variables (R S : ringType) (f : {rmorphism R -> S}).

Lemma rmorphMz : forall n, {morph f : x / x *~ n}. Proof. exact: raddfMz. Qed.

Lemma rmorph_zint : forall n, f n%:~R = n%:~R.
Proof. by move=> n; rewrite rmorphMz rmorph1. Qed.

End Multiplicative.

Section Linear.

Variable R : ringType.
Variables (U V : lmodType R) (f : {linear U -> V}).

Lemma linearMn : forall n, {morph f : x / x *~ n}. Proof. exact: raddfMz. Qed.

End Linear.

Section Zintmul1rMorph.

Variable R : ringType.

Lemma commr_mulz (x y : R) n : GRing.comm x y -> GRing.comm x (y *~ n).
Proof. by rewrite /GRing.comm=> com_xy; rewrite mulrzAr mulrzAl com_xy. Qed.

Lemma commr_zint (x : R) n : GRing.comm x n%:~R.
Proof. by apply: commr_mulz; apply: commr1. Qed.

End Zintmul1rMorph.

Section ZintBigMorphism.

Variable R : ringType.

Lemma sumMz : forall I r (P : pred I) F,
 (\sum_(i <- r | P i) F i)%N%:~R = \sum_(i <- r | P i) ((F i)%:~R) :> R.
Proof. by apply: big_morph=> // x y; rewrite !natmulP -rmorphD. Qed.

Lemma prodMz : forall I r (P : pred I) F,
 (\prod_(i <- r | P i) F i)%N%:~R = \prod_(i <- r | P i) ((F i)%:~R) :> R.
Proof. by apply: big_morph=> // x y; rewrite !natmulP PoszM -rmorphM. Qed.

End ZintBigMorphism.

Section Frobenius.

Variable R : ringType.
Implicit Types x y : R.

Variable p : nat.
Hypothesis charFp : p \in [char R].

Local Notation "x ^f" := (Frobenius_aut charFp x).

Lemma Frobenius_aut_mulz x n : (x *~ n)^f = x^f *~ n.
Proof.
case: n=> n /=; first exact: Frobenius_aut_muln.
by rewrite !NegzE !mulrNz Frobenius_aut_opp Frobenius_aut_muln.
Qed.

Lemma Frobenius_aut_zint n : (n%:~R)^f = n%:~R.
Proof. by rewrite Frobenius_aut_mulz Frobenius_aut_1. Qed.

End Frobenius.

Section OrderedRingMorphism.

Section PO.

Variables (R : poIdomainType).

Implicit Types n m : zint.
Implicit Types x y : R.

Lemma rmorphzP (f : {rmorphism zint -> R}) : f =1 ( *~%R 1).
Proof.
move=> n; wlog : n / 0 <= n; case: n=> [] n //; do ?exact.
  by rewrite NegzE !rmorphN=>->.
move=> _; elim: n=> [|n ihn]; first by rewrite rmorph0.
by rewrite zintS !rmorphD !rmorph1 ihn.
Qed.

(* zintmul and ler/ltr *)
Lemma ltr_wpmulz2r n (hn : 0 < n) : {wmono *~%R^~ n :/ (>%R : rel R)}.
Proof.
by move=> x y xy; case: (zintP n) hn=> // {n} n; rewrite ltr_wmuln2r.
Qed.

Lemma ler_wpmulz2r n (hn : 0 <= n) : {wmono *~%R^~ n :/ (>=%R : rel R)}.
Proof. by move=> x y xy; case: n hn=> [] // n _; rewrite ler_wmuln2r. Qed.

Lemma ltr_wnmulz2r n (hn : n < 0) : {wmono *~%R^~ n :/~ (>%R : rel R)}.
Proof.
by move=> x y xy /=; rewrite -ltr_opp2 -!mulrNz ltr_wpmulz2r // oppr_gt0.
Qed.

Lemma ler_wnmulz2r n (hn : n <= 0) : {wmono *~%R^~ n :/~ (>=%R : rel R)}.
Proof.
by move=> x y xy /=; rewrite -ler_opp2 -!mulrNz ler_wpmulz2r // oppr_ge0.
Qed.

Lemma mulrz_ge0 x n (x0 : 0 <= x) (n0 : 0 <= n) : 0 <= x *~ n.
Proof. by rewrite -(mul0rz _ n) ler_wpmulz2r. Qed.

Lemma mulrz_le0 x n (x0 : x <= 0) (n0 : n <= 0) : 0 <= x *~ n.
Proof. by rewrite -(mul0rz _ n) ler_wnmulz2r. Qed.

Lemma mulrz_ge0_le0 x n (x0 : 0 <= x) (n0 : n <= 0) : x *~ n <= 0.
Proof. by rewrite -(mul0rz _ n) ler_wnmulz2r. Qed.

Lemma mulrz_le0_ge0 x n (x0 : x <= 0) (n0 : 0 <= n) : x *~ n <= 0.
Proof. by rewrite -(mul0rz _ n) ler_wpmulz2r. Qed.

Lemma mulrz_gt0 x n (x0 : 0 < x) (n0 : 0 < n) : 0 < x *~ n.
Proof. by rewrite -(mul0rz _ n) ltr_wpmulz2r. Qed.

Lemma mulrz_lt0 x n (x0 : x < 0) (n0 : n < 0) : 0 < x *~ n.
Proof. by rewrite -(mul0rz _ n) ltr_wnmulz2r. Qed.

Lemma mulrz_gt0_lt0 x n (x0 : 0 < x) (n0 : n < 0) : x *~ n < 0.
Proof. by rewrite -(mul0rz _ n) ltr_wnmulz2r. Qed.

Lemma mulrz_l0_gt0 x n (x0 : x < 0) (n0 : 0 < n) : x *~ n < 0.
Proof. by rewrite -(mul0rz _ n) ltr_wpmulz2r. Qed.

Lemma ler_wpmulz2l x (hx : 0 <= x) : {wmono *~%R x :/ >=%R}.
Proof.
by move=> m n /= hmn; rewrite -subr_ge0 -mulrz_subr mulrz_ge0 // subr_ge0.
Qed.

Lemma ler_wnmulz2l x (hx : x <= 0) : {wmono *~%R x :/~ >=%R}.
Proof.
by move=> m n /= hmn; rewrite -subr_ge0 -mulrz_subr mulrz_le0 // subr_le0.
Qed.

Lemma ler_pmulz2l x (hx : 0 < x) : {mono *~%R x :/ >=%R}.
Proof.
move=> m n; rewrite cpable_wmono_ler ?cpable_ordered // => {m n}.
by move=> m n /= hmn; rewrite -subr_gt0 -mulrz_subr mulrz_gt0 // subr_gt0.
Qed.

Lemma ler_nmulz2l x (hx : x < 0) : {mono *~%R x :/~ >=%R}.
Proof.
move=> m n; rewrite cpable_wnmono_ler ?cpable_ordered // => {m n}.
by move=> m n /= hmn; rewrite -subr_gt0 -mulrz_subr mulrz_lt0 // subr_lt0.
Qed.

Lemma ltr_pmulz2l x (hx : 0 < x) : {mono *~%R x :/ >%R}.
Proof. exact: lerW_mono (ler_pmulz2l _). Qed.

Lemma ltr_nmulz2l x (hx : x < 0) : {mono *~%R x :/~ >%R}.
Proof. exact: lerW_nmono (ler_nmulz2l _). Qed.

Lemma mulrIz x (hx : x != 0) : injective ( *~%R x).
Proof.
move=> y z; rewrite -![x *~ _]mulrzr => /(mulfI hx).
by apply: mono_inj y z; apply: ler_pmulz2l.
Qed.

Lemma ler0z n : (0 <= n%:~R :> R) = (0 <= n).
Proof. by rewrite -(mulr0z 1) ler_pmulz2l. Qed.

Lemma ltr0z n : (0 < n%:~R :> R) = (0 < n).
Proof. by rewrite -(mulr0z 1) ltr_pmulz2l. Qed.

Lemma lerz0 n : (n%:~R <= 0 :> R) = (n <= 0).
Proof. by rewrite -(mulr0z 1) ler_pmulz2l. Qed.

Lemma ltrz0 n : (n%:~R < 0 :> R) = (n < 0).
Proof. by rewrite -(mulr0z 1) ltr_pmulz2l. Qed.

Lemma zintr_eq0 n : (n%:~R == 0 :> R) = (n == 0).
Proof. by rewrite -(mulr0z 1) (inj_eq (mulrIz _)) // oner_eq0. Qed.

Lemma mulrz_eq0 x n : (x *~ n == 0) = ((n == 0) || (x == 0)).
Proof. by rewrite -mulrzl mulf_eq0 zintr_eq0. Qed.

Lemma mulrz_neq0 x n : x *~ n != 0 = ((n != 0) && (x != 0)).
Proof. by rewrite mulrz_eq0 negb_or. Qed.

Lemma cpablen m n : cpable (n%:~R : R) m%:~R.
Proof. by rewrite mono_cpable ?cpable_ordered //; apply: ler_pmulz2l. Qed.
Hint Resolve cpablen.

End PO.

Section Total.

Variables (R : oIdomainType).

Implicit Types n m : zint.
Implicit Types x y : R.

Lemma ler_pmulz2r n (hn : 0 < n) : {mono *~%R^~ n :/ (>=%R : rel R)}.
Proof. exact: wmono_mono (ltr_wpmulz2r _). Qed.

Lemma ltr_pmulz2r n (hn : 0 < n) : {mono *~%R^~ n :/ (>%R : rel R)}.
Proof. exact: lerW_mono (ler_pmulz2r _). Qed.

Lemma ler_nmulz2r n (hn : n < 0) : {mono *~%R^~ n :/~ (>=%R : rel R)}.
Proof. exact: wnmono_mono (ltr_wnmulz2r _). Qed.

Lemma ltr_nmulz2r n (hn : n < 0) : {mono *~%R^~ n :/~ (>%R : rel R)}.
Proof. exact: lerW_nmono (ler_nmulz2r _). Qed.

End Total.

End OrderedRingMorphism.

End MorphTheory.

Definition exprz (R : unitRingType) (x : R) (n : zint) := nosimpl
  match n with
    | Posz n => x ^+ n
    | Negz n => x ^- (n.+1)
  end.

Notation "x ^ n" := (exprz x n) : ring_scope.

Section ExprzUnitRing.

Variable R : unitRingType.
Implicit Types x y : R.
Implicit Types m n : zint.

Lemma exprnP x (n : nat) : x ^+ n = x ^ n. Proof. by []. Qed.

Lemma exprnN x (n : nat) : x ^- n = x ^ -n%:Z.
Proof. by case: n=> //; rewrite oppr0 expr0 invr1. Qed.

Lemma expr0z x : x ^ 0 = 1. Proof. by []. Qed.

Lemma expr1z x : x ^ 1 = x. Proof. by []. Qed.

Lemma exprN1z x : x ^ (-1) = x^-1. Proof. by []. Qed.

Lemma invr_expz x n : (x ^ n)^-1 = x ^ (- n).
Proof.
by case: (zintP n)=> // [|m]; rewrite ?opprK ?expr0z ?invr1 // invrK.
Qed.

Lemma exprz_inv x n : (x^-1) ^ n = x ^ (- n).
Proof.
by case: (zintP n)=> // m; rewrite -[_ ^ (- _)]expr_inv ?opprK ?invrK.
Qed.

Lemma exp1rz n : 1 ^ n = 1 :> R.
Proof.
by case: (zintP n)=> // m; rewrite -?exprz_inv ?invr1; apply: exp1rn.
Qed.

Lemma exprSz x (n : nat) : x ^ n.+1 = x * x ^ n. Proof. exact: exprS. Qed.

Lemma exprSzr x (n : nat) : x ^ n.+1 = x ^ n * x.
Proof. exact: exprSr. Qed.

Fact exprz_add_nat x (m n : nat) : x ^ (m%:Z + n) = x ^ m * x ^ n.
Proof. exact: exprn_addr. Qed.

Fact exprz_add_Nnat x (m n : nat) : x ^ (-m%:Z + -n%:Z) = x ^ (-m%:Z) * x ^ (-n%:Z).
Proof. by rewrite -oppr_add -!exprz_inv exprz_add_nat. Qed.

Lemma exprz_add_ss x m n : (0 <= m) && (0 <= n) || (m <= 0) && (n <= 0)
  ->  x ^ (m + n) = x ^ m * x ^ n.
Proof.
case: (zintP m)=> {m} [|m|m]; case: (zintP n)=> {n} [|n|n] //= _;
by rewrite ?expr0z ?mul1r ?exprz_add_nat ?exprz_add_Nnat ?sub0r ?addr0 ?mulr1.
Qed.

Lemma exp0rz n : 0 ^ n = (n == 0)%:~R :> R.
Proof. by case: (zintP n)=> // m; rewrite -?exprz_inv ?invr0 exprSz mul0r. Qed.

Lemma commr_expz x y n : GRing.comm x y -> GRing.comm x (y ^ n).
Proof.
rewrite /GRing.comm; elim: n x y=> [|n ihn|n ihn] x y com_xy //=.
* by rewrite expr0z mul1r mulr1.
* by rewrite -exprnP commr_exp //.
rewrite -exprz_inv -exprnP commr_exp //.
case: (boolP (GRing.unit y))=> uy; last by rewrite invr_out.
by apply/eqP; rewrite (can2_eq (mulrVK _) (mulrK _)) // -mulrA com_xy mulKr.
Qed.

Lemma commr_invr x y : GRing.comm x y -> GRing.comm x (y ^-1).
Proof. by move=> cxy; rewrite -exprN1z; exact: commr_expz. Qed.

Lemma commr_expz_mull x y n : GRing.unit x -> GRing.unit y ->
  GRing.comm x y -> (x * y) ^ n = x ^ n * y ^ n.
Proof.
move=> ux uy com_xy; elim: n => [|n _|n _]; first by rewrite expr0z mulr1.
  by rewrite -!exprnP commr_exp_mull.
rewrite -!exprnN -!expr_inv com_xy -commr_exp_mull ?invr_mul//.
by apply: commr_invr; apply: commr_sym; apply: commr_invr.
Qed.

Lemma commr_expz_wmulls x y n : 0 <= n -> GRing.comm x y -> (x * y) ^ n = x ^ n * y ^ n.
Proof.
move=> n0 com_xy; elim: n n0 => [|n _|n _] //; first by rewrite expr0z mulr1.
by rewrite -!exprnP commr_exp_mull.
Qed.

Lemma unitr_expz x n (ux : GRing.unit x) : GRing.unit (x ^ n).
Proof.
case: (zintP n)=> {n} [|n|n]; rewrite ?expr0z ?unitr1 ?unitr_exp //.
by rewrite -invr_expz unitr_inv unitr_exp.
Qed.

Lemma exprz_addr x (ux : GRing.unit x) m n : x ^ (m + n) = x ^ m * x ^ n.
Proof.
move: n m; apply: wlog_ler=> n m hnm.
  by rewrite addrC hnm commr_expz //; apply: commr_sym; apply: commr_expz.
case: (zintP m) hnm=> {m} [|m|m]; rewrite ?mul1r ?add0r //;
 case: (zintP n)=> {n} [|n|n _]; rewrite ?mulr1 ?addr0 //;
   do ?by rewrite exprz_add_ss.
rewrite -invr_expz subzSS !exprSzr invr_mul ?unitr_exp // -mulrA mulVKr //.
case: (leqP n m)=> [|/ltnW] hmn; rewrite -{2}(subnK hmn) exprz_add_nat -subzn //.
  by rewrite mulrK ?unitr_exp.
by rewrite invr_mul ?unitr_expz // mulVKr ?unitr_expz // -oppr_sub -invr_expz.
Qed.

Lemma exprz_exp x m n : (x ^ m) ^ n = (x ^ (m * n)).
Proof.
wlog: n / 0 <= n.
  by case: n=> [n -> //|n]; rewrite ?NegzE mulrN -?invr_expz=> -> /=.
elim: n x m=> [|n ihn|n ihn] x m // _; first by rewrite mulr0 !expr0z.
rewrite exprSz ihn // zintS mulr_addr mulr1 exprz_add_ss //.
by case: (zintP m)=> // m'; rewrite ?oppr_le0 //.
Qed.

Lemma exprzAC x m n : (x ^ m) ^ n = (x ^ n) ^ m.
Proof. by rewrite !exprz_exp mulrC. Qed.

Lemma exprz_out x n (nux : ~~ GRing.unit x) (hn : 0 <= n) : x ^ (- n) = x ^ n.
Proof. by case: (zintP n) hn=> //= m; rewrite -exprnN -expr_inv invr_out. Qed.

End ExprzUnitRing.

Section Exprz_Zint_UnitRing.

Variable R : unitRingType.
Implicit Types x y : R.
Implicit Types m n : zint.

Lemma exprz_pmulzl x m n : 0 <= n -> (x *~ m) ^ n = x ^ n *~ (m ^ n).
Proof.
by elim: n=> [|n ihn|n _] // _; rewrite !exprSz ihn // mulrzAr mulrzAl -mulrzA.
Qed.

Lemma exprz_pzintl m n (hn : 0 <= n) : m%:~R ^ n = (m ^ n)%:~R :> R.
Proof. by rewrite exprz_pmulzl // exp1rz. Qed.

Lemma exprz_mulzl x m n (ux : GRing.unit x) (um : @GRing.unit R m%:~R) :
   (x *~ m) ^ n = (m%:~R ^ n) * x ^ n :> R.
Proof.
rewrite -[x *~ _]mulrzl commr_expz_mull //.
by apply: commr_sym; apply: commr_zint.
Qed.

Lemma expNrz x n : (- x) ^ n = (-1) ^ n * x ^ n :> R.
Proof.
case: n=> [] n; rewrite ?NegzE; first by apply: exprN.
by rewrite -!exprz_inv !invrN invr1; apply: exprN.
Qed.

Lemma unitr_n0expz x n : n != 0 -> GRing.unit (x ^ n) = GRing.unit x.
Proof.
by case: n => *; rewrite ?NegzE -?exprz_inv ?unitr_pexp ?unitr_inv ?lt0n.
Qed.

End Exprz_Zint_UnitRing.

Section ExprzIdomain.

Variable R : idomainType.
Implicit Types x y : R.
Implicit Types m n : zint.

Lemma expfz_eq0 x n : (x ^ n == 0) = (n != 0) && (x == 0).
Proof.
by case: n=> n; rewrite ?NegzE -?exprz_inv ?expf_eq0 ?lt0n ?invr_eq0.
Qed.

Lemma expfz_neq0 x n : x != 0 -> x ^ n != 0.
Proof. by move=> x_nz; rewrite expfz_eq0; apply/nandP; right. Qed.

Lemma exprz_mull x y n (ux : GRing.unit x) (uy : GRing.unit y) :
  (x * y) ^ n = x ^ n * y ^ n.
Proof. by rewrite commr_expz_mull //; apply: mulrC. Qed.

End ExprzIdomain.

Section ExprzField.

Variable F : fieldType.
Implicit Types x y : F.
Implicit Types m n : zint.

Lemma expfz_addr x m n : x != 0 -> x ^ (m + n) = x ^ m * x ^ n.
Proof. by move=> hx; rewrite exprz_addr ?unitfE. Qed.

Lemma expfz_n0addr x m n : m + n != 0 -> x ^ (m + n) = x ^ m * x ^ n.
Proof.
have [-> hmn|nx0 _] := eqVneq x 0; last exact: expfz_addr.
rewrite !exp0rz (negPf hmn).
case: (altP (m =P 0)) hmn=> [->|]; rewrite (mul0r, mul1r) //.
by rewrite add0r=> /negPf->.
Qed.

Lemma expfz_mull x y n : (x * y) ^ n = x ^ n * y ^ n.
Proof.
have [->|/negPf n0] := eqVneq n 0; first by rewrite !expr0z mulr1.
case: (boolP ((x * y) == 0)); rewrite ?mulf_eq0.
  by case/orP=> /eqP->; rewrite ?(mul0r, mulr0, exp0rz, n0).
by case/norP=> x0 y0; rewrite exprz_mull ?unitfE.
Qed.

End ExprzField.

Section ExprzOrder.

Variable R : oFieldType.
Implicit Types x y : R.
Implicit Types m n : zint.

(* ler and exprz *)
Lemma exprz_ge0 n x (hx : 0 <= x) : (0 <= x ^ n).
Proof. by case: n=> n; rewrite ?NegzE -?invr_expz ?invr_ge0 ?exprn_ge0. Qed.

Lemma exprz_gt0 n x (hx : 0 < x) : (0 < x ^ n).
Proof. by case: n=> n; rewrite ?NegzE -?invr_expz ?invr_gt0 ?exprn_gt0. Qed.

Definition exprz_gte0 := (exprz_ge0, exprz_gt0).

Lemma ler_wpiexpz2l x (x0 : 0 <= x) (x1 : x <= 1) :
  {in >=%R 0 &, {wmono (exprz x) :/~ >=%R}}.
Proof.
move=> [] m [] n; rewrite -!topredE /= ?oppr_cp0 ?ltz_nat // => _ _.
by rewrite lez_nat -?exprnP=> /ler_wiexpn2l; apply.
Qed.

Lemma ler_wniexpz2l x (x0 : 0 <= x) (x1 : x <= 1) :
  {in <%R 0 &, {wmono (exprz x) :/~ >=%R}}.
Proof.
move=> [] m [] n; rewrite ?NegzE -!topredE /= ?oppr_cp0 ?ltz_nat // => _ _.
rewrite ler_opp2 lez_nat -?invr_expz=> hmn; move: (x0).
rewrite ler_eqVlt=> /orP [/eqP<-|lx0]; first by rewrite !exp0rz invr0.
by rewrite ler_pinv -?topredE /= ?exprz_gt0 // ler_wiexpn2l.
Qed.

Fact ler_wpeexpz2l x (x1 : 1 <= x) : {in >=%R 0 &, {wmono (exprz x) :/ >=%R}}.
Proof.
move=> [] m [] n; rewrite -!topredE /= ?oppr_cp0 ?ltz_nat // => _ _.
by rewrite lez_nat -?exprnP=> /ler_weexpn2l; apply.
Qed.

Fact ler_wneexpz2l x (x1 : 1 <= x) : {in <=%R 0 &, {wmono (exprz x) :/ >=%R}}.
Proof.
move=> m n hm hn /= hmn.
rewrite -ler_pinv -?topredE /= ?exprz_gt0 ?(ltr_le_trans ltr01) //.
by rewrite !invr_expz ler_wpeexpz2l ?ler_opp2 -?topredE //= oppr_cp0.
Qed.

Lemma ler_weexpz2l x (x1 : 1 <= x) : {wmono (exprz x) :/ >=%R}.
Proof.
move=> m n /= hmn; case: (lerP 0 m)=> [|/ltrW] hm.
  by rewrite ler_wpeexpz2l // [_ \in _](ler_trans hm).
case: (lerP n 0)=> [|/ltrW] hn.
  by rewrite ler_wneexpz2l // [_ \in _](ler_trans hmn).
apply: (@ler_trans _ (x ^ 0)); first by rewrite ler_wneexpz2l.
by rewrite ler_wpeexpz2l.
Qed.

Lemma pexprz_eq1 x n (x0 : 0 <= x) : (x ^ n == 1) = ((n == 0) || (x == 1)).
Proof.
case: n=> n; rewrite ?NegzE -?exprz_inv ?oppr_eq0 pexprn_eq1 // ?invr_eq1 //.
by rewrite invr_ge0.
Qed.

Lemma ieexprIz x (x0 : 0 < x) (nx1 : x != 1) : injective (exprz x).
Proof.
apply: wlog_ltr=> // m n hmn; first by move=> hmn'; rewrite hmn.
move=> /(f_equal ( *%R^~ (x ^ (- n)))).
rewrite -!expfz_addr ?ltrNW // subrr expr0z=> /eqP.
by rewrite pexprz_eq1 ?(ltrW x0) // (negPf nx1) subr_eq0 orbF=> /eqP.
Qed.

Lemma ler_piexpz2l x (x0 : 0 < x) (x1 : x < 1) :
  {in >=%R 0 &, {mono (exprz x) :/~ >=%R}}.
Proof.
apply: (wnmono_mono_in (wnmono_inj_in_lt _ _)).
  by move=> n m hn hm /=; apply: ieexprIz; rewrite // ltrWN.
by apply: ler_wpiexpz2l; rewrite ?ltrW.
Qed.

Lemma ltr_piexpz2l x (x0 : 0 < x) (x1 : x < 1) :
  {in >=%R 0 &, {mono (exprz x) :/~ >%R}}.
Proof. exact: (lerW_nmono_in (ler_piexpz2l _ _)). Qed.

Lemma ler_niexpz2l x (x0 : 0 < x) (x1 : x < 1) :
  {in <%R 0 &, {mono (exprz x) :/~ >=%R}}.
Proof.
apply: (wnmono_mono_in (wnmono_inj_in_lt _ _)).
  by move=> n m hn hm /=; apply: ieexprIz; rewrite // ltrWN.
by apply: ler_wniexpz2l; rewrite ?ltrW.
Qed.

Lemma ltr_niexpz2l x (x0 : 0 < x) (x1 : x < 1) :
  {in <%R 0 &, {mono (exprz x) :/~ >%R}}.
Proof. exact: (lerW_nmono_in (ler_niexpz2l _ _)). Qed.

Lemma ler_eexpz2l x (x1 : 1 < x) : {mono (exprz x) :/ >=%R}.
Proof.
apply: (wmono_mono (wmono_inj_lt _ _)).
  by apply: ieexprIz; rewrite ?(ltr_trans ltr01) // ltrNW.
by apply: ler_weexpz2l; rewrite ?ltrW.
Qed.

Lemma ltr_eexpz2l x (x1 : 1 < x) : {mono (exprz x) :/ >%R}.
Proof. exact: (lerW_mono (ler_eexpz2l _)). Qed.

Lemma ler_wpexpz2r n (hn : 0 <= n) :
{in >=%R 0 & , {wmono ((@exprz R)^~ n) :/ >=%R}}.
Proof. by case: n hn=> // n _; apply: ler_expn2r. Qed.

Lemma ler_wnexpz2r n (hn : n <= 0) :
{in >%R 0 & , {wmono ((@exprz R)^~ n) :/~ >=%R}}.
Proof.
move=> x y /= hx hy hxy; rewrite -ler_pinv ?[_ \in _]exprz_gt0 //.
by rewrite !invr_expz ler_wpexpz2r  ?[_ \in _]ltrW // oppr_cp0.
Qed.

Lemma pexpIrz n (n0 : n != 0) : {in >=%R 0 &, injective ((@exprz R)^~ n)}.
Proof.
move=> x y; rewrite ![_ \in _]ler_eqVlt => /orP [/eqP<- _ /eqP|hx].
  by rewrite exp0rz ?(negPf n0) eq_sym expfz_eq0=> /andP [_ /eqP->].
case/orP=> [/eqP<- /eqP|hy].
  by rewrite exp0rz ?(negPf n0) expfz_eq0=> /andP [_ /eqP].
move=> /(f_equal ( *%R^~ (y ^ (- n)))) /eqP.
rewrite -expfz_addr ?(ltrNW hy) // subrr expr0z -exprz_inv -expfz_mull.
rewrite pexprz_eq1 ?(negPf n0) /= ?mulr_ge0 ?invr_ge0 ?ltrW //.
by rewrite (can2_eq (mulrVK _) (mulrK _)) ?unitfE ?(ltrNW hy) // mul1r=> /eqP.
Qed.

Lemma nexpIrz n (n0 : n != 0) : {in <=%R 0 &, injective ((@exprz R)^~ n)}.
Proof.
move=> x y; rewrite ![_ \in _]ler_eqVlt => /orP [/eqP-> _ /eqP|hx].
  by rewrite exp0rz ?(negPf n0) eq_sym expfz_eq0=> /andP [_ /eqP->].
case/orP=> [/eqP-> /eqP|hy].
  by rewrite exp0rz ?(negPf n0) expfz_eq0=> /andP [_ /eqP].
move=> /(f_equal ( *%R^~ (y ^ (- n)))) /eqP.
rewrite -expfz_addr ?(ltrWN hy) // subrr expr0z -exprz_inv -expfz_mull.
rewrite pexprz_eq1 ?(negPf n0) /= ?mulr_le0 ?invr_le0 ?ltrW //.
by rewrite (can2_eq (mulrVK _) (mulrK _)) ?unitfE ?(ltrWN hy) // mul1r=> /eqP.
Qed.

Lemma ler_pexpz2r n (hn : 0 < n) :
  {in >=%R 0 & , {mono ((@exprz R)^~ n) :/ >=%R}}.
Proof.
apply: wmono_mono_in (wmono_inj_in_lt _ _).
  by move=> x y hx hy /=; apply: pexpIrz; rewrite // ltrNW.
by apply: ler_wpexpz2r; rewrite ltrW.
Qed.

Lemma ltr_pexpz2r n (hn : 0 < n) :
  {in >=%R 0 & , {mono ((@exprz R)^~ n) :/ >%R}}.
Proof. exact: lerW_mono_in (ler_pexpz2r _). Qed.

Lemma ler_nexpz2r n (hn : n < 0) :
  {in >%R 0 & , {mono ((@exprz R)^~ n) :/~ >=%R}}.
Proof.
apply: wnmono_mono_in (wnmono_inj_in_lt _ _); last first.
  by apply: ler_wnexpz2r; rewrite ltrW.
by move=> x y hx hy /=; apply: pexpIrz; rewrite ?[_ \in _]ltrW ?ltrWN.
Qed.

Lemma ltr_nexpz2r n (hn : n < 0) :
  {in >%R 0 & , {mono ((@exprz R)^~ n) :/~ >%R}}.
Proof. exact: lerW_nmono_in (ler_nexpz2r _). Qed.

Lemma eqr_expz2 n x y : n != 0 -> 0 <= x -> 0 <= y ->
  (x ^ n == y ^ n) = (x == y).
Proof. by  move=> *; rewrite (inj_in_eq (pexpIrz _)). Qed.

End ExprzOrder.

Section Sgz.

Variable R : oIdomainType.
Implicit Types x y z : R.
Implicit Types m n p : zint.

Definition sgz x : zint := if x == 0 then 0 else if 0 <= x then 1 else -1.

Lemma sgrEz x : sgr x = (sgz x)%:~R.
Proof. by rewrite /sgz /sgr !fun_if /=; case: (_ == _)=> //; case: lerP. Qed.

Lemma sgz_cp0 x :
  ((sgz x == 1) = (0 < x)) *
  ((sgz x == -1) = (x < 0)) *
  ((sgz x == 0) = (x == 0)).
Proof. by rewrite /sgz [_ <= _]lerNgt; case: ltrgtP. Qed.

Lemma gtr0_sgz x : 0 < x -> sgz x = 1.
Proof. by move=> hx; apply/eqP; rewrite sgz_cp0. Qed.

Lemma ltr0_sgz x : x < 0 -> sgz x = -1.
Proof. by move=> hx; apply/eqP; rewrite sgz_cp0. Qed.

Lemma sgz0 : sgz (0 : R) = 0. Proof. by rewrite /sgz eqxx. Qed.
Lemma sgz1 : sgz (1 : R) = 1. Proof. by rewrite gtr0_sgz // ltr01. Qed.
Lemma sgzN1 : sgz (-1 : R) = -1. Proof. by rewrite ltr0_sgz // ltrN10. Qed.

Definition sgzE := (sgz0, sgz1, sgzN1).

CoInductive sgz_val x : bool -> bool -> bool -> bool -> bool -> bool
  -> bool -> bool -> bool -> bool -> bool -> bool
  -> bool -> bool -> bool -> bool -> bool -> bool
  -> R -> zint -> Set :=
  | SgzNull of x = 0 : sgz_val x true true true true false false
    true false false true false false true false false true false false 0 0
  | SgzPos of x > 0 : sgz_val x false false true false false true
    false false true false false true false false true false false true 1 1
  | SgzNeg of x < 0 : sgz_val x false true false false true false
    false true false false true false false true false false true false (-1) (-1).

Lemma sgzP x :
  sgz_val x (0 == x) (x <= 0) (0 <= x) (x == 0) (x < 0) (0 < x)
  (0 == sgr x) (-1 == sgr x) (1 == sgr x)
  (sgr x == 0)  (sgr x == -1) (sgr x == 1)
  (0 == sgz x) (-1 == sgz x) (1 == sgz x)
  (sgz x == 0)  (sgz x == -1) (sgz x == 1) (sgr x) (sgz x).
Proof.
rewrite ![_ == sgz _]eq_sym ![_ == sgr _]eq_sym !sgr_cp0 !sgz_cp0.
by rewrite /sgr /sgz !lerNgt; case: ltrgtP; constructor.
Qed.

Lemma sgzN x : sgz (-x) = - sgz x.
Proof. by rewrite /sgz oppr_eq0 oppr_ge0; case: ltrgtP. Qed.

Lemma mulz_sg x : sgz x * sgz x = (x != 0)%:~R.
Proof. by case: sgzP; rewrite ?(mulr0, mulr1, mulrNN). Qed.

Lemma mulz_sg_eq1 x y : (sgz x * sgz y == 1) = (x != 0) && (sgz x == sgz y).
Proof.
do 2?case: sgzP=> _; rewrite ?(mulr0, mulr1, mulrN1, opprK, oppr0, eqxx);
  by rewrite ?[0 == 1]eq_sym ?oner_eq0 //= eqr_oppC oppr0 oner_eq0.
Qed.

Lemma mulz_sg_eqN1 x y : (sgz x * sgz y == -1) = (x != 0) && (sgz x == - sgz y).
Proof. by rewrite -eqr_oppC -mulrN -sgzN mulz_sg_eq1. Qed.

(* Lemma muls_eqA x y z : sgr x != 0 -> *)
(*   (sgr y * sgr z == sgr x) = ((sgr y * sgr x == sgr z) && (sgr z != 0)). *)
(* Proof. by do 3!case: sgrP=> _. Qed. *)

Lemma sgzM x y : sgz (x * y) = sgz x  * sgz y.
Proof.
case: (sgzP x)=> hx; first by rewrite hx ?mul0r sgz0.
  case: (sgzP y)=> hy; first by rewrite hy !mulr0 sgz0.
    by apply/eqP; rewrite mul1r sgz_cp0 mulr_gt0.
  by apply/eqP; rewrite mul1r sgz_cp0 mulr_gt0_lt0.
case: (sgzP y)=> hy; first by rewrite hy !mulr0 sgz0.
  by apply/eqP; rewrite mulr1 sgz_cp0 mulr_lt0_gt0.
by apply/eqP; rewrite mulN1r opprK sgz_cp0 mulr_lt0.
Qed.

Lemma sgzX (n : nat) x : sgz (x ^+ n) = (sgz x) ^+ n.
Proof. by elim: n => [|n ihn]; rewrite ?sgz1 // !exprS sgzM ihn. Qed.

Lemma sgz_eq0 x : (sgz x == 0) = (x == 0).
Proof. by rewrite sgz_cp0. Qed.

Lemma sgz_odd (n : nat) x : x != 0 -> (sgz x) ^+ n = (sgz x) ^+ (odd n).
Proof. by case: sgzP=> //=; rewrite ?exp1rn // signr_odd. Qed.

Lemma sgz_gt0 x : (sgz x > 0) = (x > 0).
Proof. by case: sgzP. Qed.

Lemma sgz_lt0 x : (sgz x < 0) = (x < 0).
Proof. by case: sgzP. Qed.

Lemma sgz_ge0 x : (sgz x >= 0) = (x >= 0).
Proof. by case: sgzP. Qed.

Lemma sgz_le0 x : (sgz x <= 0) = (x <= 0).
Proof. by case: sgzP. Qed.

End Sgz.

Lemma sgrz (n : zint) : sgr n = sgz n. Proof. by rewrite sgrEz zintz. Qed.
Lemma sgz_eq (R R' : oIdomainType) (x : R) (y : R') :
  (sgz x == sgz y) = ((x == 0) == (y == 0)) && ((0 < x) == (0 < y)).
Proof. by do 2!case: sgzP. Qed.

Section SgzIdomain.

Variable R : oIdomainType.
Implicit Types x y z : R.
Implicit Types m n p : zint.

Lemma sgz_id x : sgz (sgz x) = sgz x. Proof. by case: (sgzP x). Qed.
Lemma sgz_sgr x : sgz (sgr x) = sgz x.
Proof.
rewrite sgrEz.
by case: (sgzP x); rewrite (mulr0z, mulr1z, mulrN1z) (sgz0, sgz1, sgzN1).
Qed.

Lemma sgz_smul x y : sgz (y *~ (sgz x)) = (sgz x) * (sgz y).
Proof. by rewrite -mulrzl sgzM -sgrEz sgz_sgr. Qed.

Lemma sgz_zint m : sgz (m%:~R : R) = sgz m.
Proof. by apply/eqP; rewrite sgz_eq ?zintr_eq0 ?ltr0z !eqxx. Qed.

Lemma sgr_zint m : sgr (m%:~R : R) = (sgr m)%:~R.
Proof. by rewrite sgrEz sgz_zint -sgrz. Qed.

Lemma absr_zint m : `|m%:~R| = `|m|%:~R :> R.
Proof. by rewrite !absr_dec sgr_zint rmorphM. Qed.

Lemma sgrMz m x : sgr (x *~ m) = sgr x *~ sgr m.
Proof. by rewrite -mulrzr sgrM sgr_zint mulrzr. Qed.

Lemma absr_sgz x : `|sgz x| = (x != 0).
Proof. by case: sgzP. Qed.

Lemma absr_sg x :  `|sgr x| = (x != 0)%:~R.
Proof. by rewrite sgrEz absr_zint absr_sgz. Qed.

Lemma absrMz m x : `|x *~ m| = `|x| *~ `|m|.
Proof. by rewrite -mulrzl absrM absr_zint mulrzl. Qed.

End SgzIdomain.

Section Absz.

Implicit Types m n p : zint.

Definition absz m := match m with Posz p => p | Negz n => n.+1 end.

Lemma absz_nat (m : nat) : absz m = m. Proof. by []. Qed.

Lemma abszE (m : zint) : absz m = `|m| :> zint. Proof. by case: m. Qed.

Lemma absz_eq0 : forall m, (absz m == 0%N) = (m == 0). Proof. by case. Qed.

End Absz.

(* Todo : div theory of zint *)
Section PolyZintRing.

Variable R : ringType.
Implicit Types x y z: R.
Implicit Types m n : zint.
Implicit Types i j k : nat.
Implicit Types p q r : {poly R}.

Lemma coefMrz : forall p n i, (p *~ n)`_i = (p`_i *~ n).
Proof. by move=> p [] n i; rewrite ?NegzE (coefMNn, coefMn). Qed.

Lemma polyC_mulrz : forall n, {morph (@polyC R) : c / c *~ n}.
Proof.
move=> [] n c; rewrite ?NegzE -?natmulP ?polyC_natmul //.
by rewrite polyC_opp mulrNz polyC_natmul natmulN.
Qed.

Lemma horner_mulrz : forall n (p : {poly R}) x, (p *~ n).[x] = p.[x] *~ n.
Proof. by case=> *; rewrite ?NegzE ?mulNzr ?(horner_opp, horner_mulrn). Qed.

Lemma horner_zmul : forall n x, (n%:~R : {poly R}).[x] = n%:~R.
Proof. by move=> n x; rewrite horner_mulrz hornerC. Qed.

Lemma derivMz : forall n p, (p *~ n)^`() = p^`() *~ n.
Proof. by move=> [] n p; rewrite ?NegzE -?natmulP (derivMn, derivMNn). Qed.

End PolyZintRing.

Section PolyZintOIdom.

Variable R : oIdomainType.

Lemma mulpz : forall (p : {poly R}) n, p *~ n = n%:~R *: p.
Proof.
by move=> p n; rewrite -[p *~ n]mulrzl -mul_polyC polyC_mulrz polyC1.
Qed.

End PolyZintOIdom.