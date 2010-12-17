Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq ssralg bigop.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope zint_scope with Z.
Open Scope zint_scope.

CoInductive zint : Set := Posz of nat | Negz of nat.
Coercion Posz : nat >-> zint.

Definition zintmul (R : zmodType) (x : R) (n : zint) := nosimpl
  match n with
    | Posz n => (x *+ n)%R
    | Negz n => (x *- (n.+1))%R
  end.

Notation "*z%R" := (@zintmul _) (at level 0) : ring_scope.
Notation "n *z x" := (zintmul x n) 
  (at level 41, right associativity, format "n  *z  x") : ring_scope.
Notation "n %:zR" := (n *z 1)%R
  (at level 2, left associativity, format "n %:zR")  : ring_scope.
Notation "n %:Z" := (n : zint)
  (at level 2, left associativity, format "n %:Z")  : zint_scope.


Definition eqz (m n : zint) : bool :=
  match m, n with
    | Posz m', Posz n' => m' == n'
    | Negz m', Negz n' => m' == n'
    | _, _ => false
  end.

Lemma eqzP : Equality.axiom eqz.
Proof.
move=> n m; apply: (iffP idP) => [|<-]; last by case: n=> /=.
by move: n m=> [n|n] [m|m] //=; move/eqP->.
Qed.

Canonical Structure zint_eqMixin := EqMixin eqzP.
Canonical Structure zint_eqType := Eval hnf in EqType zint zint_eqMixin.

Definition natsum_of_zint (m : zint) : nat + nat := 
  match m with Posz p => inl _ p | Negz n => inr _ n end.

Definition zint_of_natsum (m : nat + nat) :=
  match m with inl p => Posz p | inr n => Negz n end.

Lemma natsum_of_zintK : cancel natsum_of_zint zint_of_natsum.
Proof. by case. Qed.

Definition zint_countMixin := CanCountMixin natsum_of_zintK.
Definition zint_choiceMixin := CountChoiceMixin zint_countMixin.
Canonical Structure zint_choiceType := Eval hnf in ChoiceType zint zint_choiceMixin.
Canonical Structure zint_countType := Eval hnf in CountType zint zint_countMixin.

Implicit Arguments eqzP [x y].
Prenex Implicits eqzP.

Lemma eqzE : eqz = eq_op. Proof. by []. Qed.
  
Lemma zint_irrelevance : forall (x y : zint) (E E' : x = y), E = E'.
Proof. exact: eq_irrelevance. Qed.

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

Lemma addzM : {morph Posz : n m / (n + m)%N >-> n + m}. Proof. done. Qed.

Lemma NegzE : forall (n : nat), Negz n = -(n.+1). Proof. done. Qed.

Lemma zint_rect : forall P : zint -> Type,
  P 0 -> (forall n : nat, P n -> P (n.+1))
  -> (forall n : nat, P (- n) -> P (- (n.+1)))
  -> forall n : zint, P n.
Proof.
by move=> P P0 hPp hPn []; elim=> [|n ihn]//; do? [apply: hPn | apply: hPp].
Qed.

Definition zint_rec := zint_rect.
Definition zint_ind := zint_rect.

Lemma addzC : commutative addz.
Proof. by move=> [] m [] n //=; rewrite addnC. Qed.

Lemma add0z : left_id 0 addz. Proof. by move=> [] [|]. Qed.

Lemma oppzK : involutive oppz. Proof. by do 2?case. Qed.

(* Lemma zint_opp_ind : forall P : zint -> Prop, *)
(*   P 0 -> (forall n : nat, P n -> P (n.+1)%N) *)
(*   -> (forall n : nat, P n -> P (- n))  *)
(*   -> forall n : zint, P n. *)
(* Proof. *)
(* move=> P P0 hPp hPopp. *)
(* suff Pn: forall n : nat, P n; last by elim. *)
(* by case=> [] // n; rewrite NegzE; apply: hPopp; apply: Pn. *)
(* Qed. *)

Lemma oppz_add : {morph oppz : m n / m + n}.
Proof.
suff aux: forall (m:nat) (n:zint),  -(m + n) = - m - n.
  move=> [m n|[|m] n]; first by rewrite //= aux.
    by case: n=> [] [|[|n]] //=; rewrite !subn1.
  by rewrite NegzE -[n]oppzK -aux !oppzK.
move=> [|[|m]] [] [|n] //=; rewrite -?addnE ?(subn0,addn0,addnS,subn1) //=.
rewrite !ltnS !subSS. rewrite leq_eqVlt; case: ltnP=> hnm.
  rewrite orbT //=; case hmn: (_-_)%N=>[|p]. 
    by move: hnm; rewrite -subn_gt0 hmn ltnn.
  by congr Negz; apply: succn_inj; rewrite -hmn -ltn_subS.
rewrite orbF; case hmn: (_ == _)=> //=.
  by rewrite -!(eqP hmn) subnn.
by rewrite /oppz -leq_subS//; rewrite ltn_neqAle eq_sym hmn hnm.
Qed.

(* Lemma oppzS : {morph oppz : n / n.+1 >-> n.-1}. Proof. by do 2?case. Qed. *)
(* Lemma oppzP : {morph oppz : n / n.-1 >-> n.+1}. Proof. by do 2?case. Qed. *)

(* Definition oppzE := (oppz_add, oppzS, oppzP). *)

Section SsrnatExt.

CoInductive compare_nat (m n : nat) : 
  bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | CompareNatLt of m < n : compare_nat m n true false false false true false 
  | CompareNatGt of m > n : compare_nat m n false true false false false true 
  | CompareNatEq of m = n : compare_nat m n true true true true false false.

Lemma ltngtP : forall m n, compare_nat m n 
  (m <= n) (n <= m) (n == m) (m == n) (m < n) (n < m).
Proof.
move=> m n; rewrite ltn_neqAle !eqn_leq.
case: ltnP=> [hmn|] /=; rewrite !(andbF, andbT).
  by rewrite (ltnW hmn); constructor.
by rewrite leq_eqVlt orbC; case: leqP => Hm; first move/eqnP; constructor.
Qed.

End SsrnatExt.

Lemma subSz1 : forall n : zint, 1 + n - 1 = n.
Proof.
elim=> // n _ /=; rewrite ltnS; case: ltngtP; rewrite ?ltn0//.
  by case: n=> // n _; rewrite subn1 /= addn0.
by move <-.
Qed.

Lemma add1Pz : forall n : zint, 1 + (n - 1) = n.
Proof. by elim=> // n _ /=; rewrite ?(subn1, addn0). Qed.

Lemma addSnz : forall (m:nat) (n:zint), (m.+1%N) + n = 1 + (m + n).
Proof.
move=> [|m] [] [|n] //=; rewrite ?add1n ?subn1 //.
rewrite !(ltnS, subSS); case: ltngtP=> hmn /=.
* rewrite -subn_gt0 subn_subA ?(ltnW hmn) // subn_gt0 ltnS leqNgt hmn /=.
  by rewrite -predn_sub subn1.
* by rewrite -predn_sub add1n /= prednK // subn_gt0.
* by rewrite hmn !subnn.
Qed.

(* Lemma subzSn : forall (m:nat) (n:zint), n - (m.+1%N) = (n - m) - 1. *)
(* Proof. *)
(* move=> m n; apply: (inv_inj oppzK). rewrite !oppzE !oppzK !addzSn. *)
(* Qed. *)

Lemma addSz :  forall (m n : zint), (1 + m) + n = 1 + (m + n).
Proof.
case=> [] m n; first by rewrite -addzM add1n addSnz.
rewrite !NegzE; apply: (inv_inj oppzK).
rewrite !oppz_add !oppzK addSnz [-1%:Z + _]addzC addSnz add1Pz.
by rewrite [-1%:Z + _]addzC subSz1.
Qed.

Lemma addPz : forall (m:zint) (n:zint), (n - 1) + m = (n + m) - 1.
Proof. 
move=> m n; apply: (inv_inj oppzK); rewrite !oppz_add oppzK.
by rewrite [_ + 1]addzC addSz addzC.
Qed.

Lemma addzA : associative addz.
Proof.
elim=> [|m ihm|m ihm] n p; first by rewrite !add0z.
  by rewrite -add1n addzM !addSz ihm.
by rewrite -add1n addnC addzM oppz_add !addPz ihm.
Qed.

Lemma addNz : left_inverse (0:zint) oppz addz. Proof. by do 3?elim. Qed.

Lemma predn_zint : forall n : nat, n > 0 -> n.-1%:Z = n - 1.
Proof. by case=> // n _ /=; rewrite subn1. Qed.

End zintZmod.

Definition zint_ZmodMixin := 
  ZmodMixin zintZmod.addzA zintZmod.addzC zintZmod.add0z zintZmod.addNz.
Canonical Structure zint_ZmodType := ZmodType zint zint_ZmodMixin.

Open Scope ring_scope.

Lemma eqz_nat : forall m n : nat, (m == n :> zint) = (m == n :> nat).
Proof. by move=> [|m] [|n]. Qed.

Lemma addzM : {morph Posz : n m / (n + m)%N >-> n + m}. Proof. done. Qed.

Lemma NegzE : forall (n : nat), Negz n = -(n.+1)%:Z. Proof. done. Qed.

Lemma zint_rect : forall P : zint -> Type,
  P 0 -> (forall n : nat, P n -> P (n.+1)%N)
  -> (forall n : nat, P (- (n%:Z)) -> P (- (n.+1%N%:Z)))
  -> forall n : zint, P n.
Proof.
by move=> P P0 hPp hPn []; elim=> [|n ihn]//; do? [apply: hPn | apply: hPp].
Qed.

Definition zint_rec := zint_rect.
Definition zint_ind := zint_rect.

Definition oppz_add := (@oppr_add [zmodType of zint]).

Lemma natmulP : forall (R : zmodType) (x : R) (n : nat), x *+ n = n *z x.
Proof. by move=> R x []. Qed.

Lemma natmulN : forall (R : zmodType) (x : R) (n : nat), x *- n = - n%:Z *z x.
Proof. by move=> R x []; rewrite ?oppr0. Qed.

Lemma predn_zint : forall n : nat, n > 0 -> n.-1%:Z = n%:Z - 1%N%:Z.
Proof. exact: zintZmod.predn_zint. Qed.

Lemma subzn : forall (m n : nat), n <= m -> (m : zint) - (n : zint) = (m - n)%N.
Proof.
move=> m; elim=> //= [|n ihn] hmn; first by rewrite subr0 subn0.
rewrite -predn_sub -addn1 !addzM oppr_add addrA ihn 1?ltnW //.
by rewrite predn_zint // subn_gt0.
Qed.


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

Lemma mulz_addl : left_distributive mulz (+%R).
Proof.
Admitted.

Lemma mulzN : forall (m n : zint), (m * (- n))%Z = - (m * n)%Z.
Proof.
move=> m n; apply: (@addrI _ (m * n)%Z). 
by rewrite ![(m*_)%Z]mulzC -mulz_addl !subrr mul0z.
Qed.
Lemma mulNz : forall (m n : zint), ((- m) * n)%Z = - (m * n)%Z.
Proof. by move=> m n; rewrite mulzC mulzN mulzC. Qed.

Lemma mulzA : associative mulz.
Proof.
by move=> [] m [] n [] p; 
  rewrite ?NegzE ?(mulnA,mulNz,mulzN,opprK) //= ?mulnA.
Qed.

Lemma mul1z : left_id 1%Z mulz.
Proof. by case=> [[|n]|n] //=; rewrite ?mul1n// plusE addn0. Qed.

Lemma nonzero1z : 1%Z != 0. Proof. done. Qed.

End zintRing.

Definition zint_comRingMixin := ComRingMixin zintRing.mulzA
  zintRing.mulzC zintRing.mul1z zintRing.mulz_addl zintRing.nonzero1z.
Canonical Structure zint_Ring := Eval hnf in RingType zint zint_comRingMixin.
Canonical Structure zint_comRing := Eval hnf in ComRingType zint zintRing.mulzC.

Section MoreZintRing.

Implicit Types m n : zint.

(* Lemma addSz : forall (m n : zint),  (1 + m) + n = 1 + (m + n). *)
(* Proof. by move=> m n; rewrite addrA. Qed. *)

(* Lemma addzS :  forall (m n : zint), m + (1 + n) = 1 + (m + n). *)
(* Proof. by move=> m n; rewrite addrCA. addSz addrC. Qed. *)

(* Lemma addzP : forall (m n : zint), n + (m.-1) = (n + m).-1. *)
(* Proof. by move=> m n; apply: (inv_inj (@opprK _)); rewrite !oppz_add addzS. Qed. *)

(* Lemma subzS : forall (m n : zint), n - (m.+1) = (n - m).-1. *)
(* Proof. by move=> m n; rewrite oppz_add addzP. Qed. *)

(* Lemma addPz : forall m n : zint, n.-1 + m = (n + m).-1. *)
(* Proof. by move=> m n; rewrite addrC addzP addrC. Qed. *)

(* Lemma addz1 : forall n, n + 1 = n.+1. *)
(* Proof. by move=> n; rewrite addrC add1z. Qed. *)

(* Lemma subz1 : forall n, n - 1 = n.-1. *)
(* Proof. *)
(* by elim=> // n ihn; rewrite succnSz ?oppz_add (addSz,addPz) ihn// predzK succzK. *)
(* Qed. *)

(* Lemma sub1z : forall n, 1 - n = 1 + (-n).+1. *)
(* Proof. by move=> n; rewrite -addz1 addrC. Qed. *)

Lemma mulzM : {morph Posz : n m / (n * m)%N >-> n * m}. Proof. done. Qed.

Lemma zintS : forall n : nat, n.+1%:Z = 1 + n%:Z.
Proof. by move=> n; rewrite -addzM. Qed.

Lemma zintP : forall n : nat, n > 0 -> n.-1%:Z = n%:Z - 1.
Proof. exact: predn_zint. Qed.

(* Lemma mulzS : forall m n, m * n.+1 = m * n + m. *)
(* Proof. by move=> m n; rewrite -addz1 mulr_addr mulr1. Qed. *)

(* Lemma mulzSr : forall m n, m * n.+1 = m + m * n. *)
(* Proof. by move=> m n; rewrite mulzS addrC. Qed. *)

(* Lemma mulSz : forall m n, m.+1 * n = m * n + n. *)
(* Proof. by move=> m n; rewrite -addz1 mulr_addl mul1r. Qed. *)

(* Lemma mulSzr : forall m n, m.+1 * n = n + m * n. *)
(* Proof. by move=> m n; rewrite mulSz addrC. Qed. *)

End MoreZintRing.

Module zintUnitRing.
Section zintUnitRing.
Implicit Types m n : zint.

Definition unitz := [pred n : zint | (n == 1) || (n == -1)].
Definition invz n : zint := n.

Lemma mulVz : {in unitz, left_inverse 1%R invz *%R}.
Proof. by move=> n; rewrite !inE; case/orP; move/eqP->. Qed.

Lemma mulzn_eq1 : forall m (n : nat), (m * n == 1) = (m == 1) && (n == 1%N).
Proof. by case=> m n /=; [rewrite -mulzM [_==_]eqn_mul1 | case: n]. Qed.

Lemma unitzPl : forall m n, n * m = 1 -> unitz m.
Proof.
case=> m n; move/eqP; rewrite !inE //=.
* by rewrite mulzn_eq1; case/andP=> _; move/eqP->.
* by rewrite NegzE zintS mulrN -mulNr mulzn_eq1; case/andP=> _.
Qed.

Lemma  invz_out : {in predC unitz, invz =1 id}.
Proof. exact. Qed.

Lemma idomain_axiomz : forall m n, m * n = 0 -> (m == 0) || (n == 0).
Proof.
by case=> m [] n //=; move/eqP; rewrite ?(NegzE,mulrN,mulNr);
  rewrite ?(inv_eq (@opprK _)) -mulzM [_==_]muln_eq0.
Qed.

End zintUnitRing.
End zintUnitRing.

Definition zint_comUnitRingMixin :=  ComUnitRingMixin zintUnitRing.mulVz 
  zintUnitRing.unitzPl zintUnitRing.invz_out.
Canonical Structure zint_unitRingType :=
  Eval hnf in UnitRingType zint zint_comUnitRingMixin.
Canonical Structure zint_comUnitRing := Eval hnf in [comUnitRingType of zint].
Canonical Structure zint_iDomain := Eval hnf in IdomainType zint 
  zintUnitRing.idomain_axiomz.


Module MzintLmod.
Section MzintLmod.

Variable M : zmodType.

Implicit Types m n : zint.
Implicit Types x y z : M.

Lemma mulzrA_rev : forall m n x,  m *z (n *z x) = (m * n) *z x.
Proof.
elim=> [|m _|m _]; elim=> [|n _|n _] x; rewrite /zintmul //=;
rewrite ?(muln0, mulr0n, mul0rn, oppr0, mulNrn, opprK) //; 
 do ?by rewrite mulnC mulrnA.
* by rewrite -mulrnA mulnC.
* by rewrite -mulrnA.
Qed.

Lemma mul1zr : forall x : M, 1 *z x = x. Proof. done. Qed.

Lemma mulzr_addr : forall m, {morph ( *z%R^~ m : M -> M) : x y / x + y}.
Proof.
by elim=> [|m _|m _] x y; rewrite ?addr0 /zintmul //= ?mulrn_addl // oppr_add.
Qed.

Lemma mulzr_subl_nat : forall (m n : nat) x, (m%:Z - n%:Z) *z x = m *z x - n *z x.
Proof.
move=> m n x; case: (leqP m n)=> hmn; rewrite /zintmul //=.
  rewrite addrC -{1}[m:zint]opprK -oppr_add subzn //.
  rewrite -{2}[n](@subnKC m)// mulrn_addr oppr_add addrA subrr sub0r.
  by case hdmn: (_ - _)%N=> [|dmn] /=; first by rewrite mulr0n oppr0.
have hnm := ltnW hmn.
rewrite  -{2}[m](@subnKC n)// mulrn_addr addrAC subrr add0r.
by rewrite subzn.
Qed.

Lemma mulzr_addl : forall x, {morph *z%R x : m n / m + n}.
Proof.
move=> x; elim=> [|m _|m _]; elim=> [|n _|n _]; rewrite /zintmul //=;
rewrite -?(oppr_add) ?(add0r, addr0, mulrn_addr, subn0) //.
* by rewrite -/(zintmul _ _) mulzr_subl_nat.
* by rewrite -/(zintmul _ _) addrC mulzr_subl_nat addrC.
* by rewrite -addnS -addSn mulrn_addr.
Qed.

Definition Mzint_LmodMixin := 
  @LmodMixin _ [zmodType of M] (fun (n : zint) (x : M) => n *z x) mulzrA_rev mul1zr mulzr_addr mulzr_addl.
Canonical Structure Mzint_LmodType := LmodType zint M Mzint_LmodMixin.


Lemma mulzrA : forall x m n, (m * n) *z x = m *z n *z x.
Proof. by move=> *; rewrite -mulzrA_rev. Qed.

Lemma mul0zr : forall x, 0 *z x = 0. Proof. done. Qed.

Lemma mulz0r : forall n, n *z 0 = 0 :> M.
Proof. exact: scaler0. Qed.

Lemma mulNzr : forall n x, (- n) *z x = - (n *z x).
Proof. exact: scaleNr. Qed.

Lemma mulN1zr : forall x, (- 1) *z x = - x.
Proof. exact: scaleN1r. Qed.

Lemma mulzNr: forall n x, n *z (- x) = - (n *z x).
Proof. exact: scalerN. Qed.

Lemma mulzr_subl: forall m n x, (m - n) *z x = m *z x - n *z x.
Proof. exact: scaler_subl. Qed.

Lemma mulzr_subr : forall n x y, n *z (x - y) = n *z x - n *z y.
Proof. exact: scaler_subr. Qed.

Lemma mulzr_nat : forall (n : nat) x, n%:zR *z x = n *z x.
Proof. exact: scaler_nat. Qed.

Lemma mulzr_suml : forall x I r (P : pred I) F,
  (\sum_(i <- r | P i) F i) *z x = \sum_(i <- r | P i) F i *z x.
Proof. exact: scaler_suml. Qed.

Lemma mulzr_sumr : forall n I r (P : pred I) (F : I -> M),
   n *z (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) n *z F i.
Proof. exact: scaler_sumr. Qed.

End MzintLmod.
End MzintLmod.

Definition mulzrA := MzintLmod.mulzrA.
Definition mul1zr := MzintLmod.mul1zr.
Definition mulzr_addl := MzintLmod.mulzr_addl.
Definition mulzr_addr := MzintLmod.mulzr_addr.
Definition mul0zr := MzintLmod.mul0zr.
Definition mulz0r := MzintLmod.mulz0r.
Definition mulzNr := MzintLmod.mulzNr.
Definition mulN1zr := MzintLmod.mulN1zr.
Definition mulNzr := MzintLmod.mulNzr.
Definition mulzr_subr := MzintLmod.mulzr_subr.
Definition mulzr_subl := MzintLmod.mulzr_subl.
Definition mulzr_nat := MzintLmod.mulzr_nat.
Definition mulzr_sumr := MzintLmod.mulzr_sumr.
Definition mulzr_suml := MzintLmod.mulzr_suml.

Lemma mulz1r : forall n, n%:zR = n.
Proof. 
elim=> //= n ihn; rewrite /zintmul /=.
  by rewrite -addn1 mulrn_addr /= addzM -ihn.
by rewrite natmulN zintS oppr_add mulzr_addl ihn.
Qed.

Section RzintMod.

Variable R : ringType.

Implicit Types m n : zint.
Implicit Types x y z : R.

Lemma mulzrAl : forall n x y, (n *z x) * y = n *z (x * y).
Proof. 
by elim=> //= *; rewrite ?mul0r ?mulr0z // /zintmul /= -mulrnAl -?mulNr.
Qed.

Lemma mulzrAr : forall n x y, x * (n *z y) = n *z (x * y).
Proof. 
by elim=> //= *; rewrite ?mul0r ?mulr0z // /zintmul /= -mulrnAr -?mulrN.
Qed.

Lemma mulzrl : forall x n, n%:zR * x = n *z x.
Proof. by move=> x n; rewrite mulzrAl mul1r. Qed.

Lemma mulzrr : forall x n, x * n%:zR = n *z x.
Proof. by move=> x n; rewrite mulzrAr mulr1. Qed.

Lemma mulNzNr : forall n x, (-n) *z (-x) = n *z x.
Proof. by move=> n x; rewrite mulzNr mulNzr opprK. Qed.

Lemma mulrbz : forall x (b : bool), b *z x = (if b then x else 0).
Proof. by move=> x []. Qed.

Lemma zintr_add : forall m n, (m + n)%:zR = m%:zR + n%:zR :> R.
Proof. exact: mulzr_addl. Qed.

Lemma zintr_mul : forall m n, (m * n)%:zR = m%:zR * n%:zR :> R.
Proof. by move=> m n; rewrite mulzrA -mulzrl. Qed.

End RzintMod.   

Lemma mulzzr : forall m n : zint, m *z n = m * n.
Proof. by move=> m n; rewrite -mulzrl mulz1r. Qed.

Section LMod.

Variable R : ringType.
Variable V : (lmodType R).

Implicit Types m n : zint.
Implicit Types x y z : R.
Implicit Types u v w : V.

Lemma scalezr : forall n v, n%:zR *: v = n *z v.
Proof.
move=> n v; elim: n=> [|n ihn|n ihn]; first by rewrite scale0r.
  by rewrite zintS !mulzr_addl scaler_addl ihn scale1r.
by rewrite zintS oppr_add !mulzr_addl scaler_addl ihn scaleN1r.
Qed.

Lemma scaler_mulzrl : forall a v n, n *z (a *: v) = (n *z a) *: v.
Proof. by move=> a v n; rewrite -mulzrl -scalezr scalerA. Qed.

Lemma scaler_mulzrr : forall a v n, n *z (a *: v) = a *: (n *z v).
Proof. by move=> a v n; rewrite -!scalezr !scalerA mulzrr mulzrl. Qed.

End LMod.

Section MorphTheory.
Section Additive.
Variables (U V : zmodType) (f : {additive U -> V}).

Lemma raddfMz : forall n, {morph f : x / n *z x}.
Proof. 
case=> n x /=; first exact: raddfMn.
by rewrite NegzE !mulNzr; apply: raddfMNn.
Qed.

End Additive.

Section Multiplicative.

Variables (R S : ringType) (f : {rmorphism R -> S}).

Lemma rmorphMz : forall n, {morph f : x / n *z x}. Proof. exact: raddfMz. Qed.

Lemma rmorph_zint : forall n, f n%:zR = n%:zR.
Proof. by move=> n; rewrite rmorphMz rmorph1. Qed.

End Multiplicative.

Section Linear.

Variable R : ringType.
Variables (U V : lmodType R) (f : {linear U -> V}).

Lemma linearMn : forall n, {morph f : x / n *z x}. Proof. exact: raddfMz. Qed.

End Linear.

Section Zintmul1rMorph.

Variable R : ringType.

Lemma zintmul1r_is_rmorphism : rmorphism ( *z%R (1 : R)).
Proof.
split; first by move=> m n /=; rewrite mulzr_subl.
by split; first by move=> m n /=; rewrite mulzrA mulzrl.
Qed.

Canonical Structure zintmul1r_rmorph := RMorphism zintmul1r_is_rmorphism.


Lemma commr_mulz : forall (x y : R) (n : zint), 
  GRing.comm x y -> GRing.comm x (n *z y).
Proof.
by rewrite /GRing.comm => x y n com_xy; rewrite mulzrAr mulzrAl com_xy.
Qed.

Lemma commr_zint : forall (x : R) n, GRing.comm x n%:zR.
Proof. move=> x n; apply: commr_mulz; exact: commr1. Qed.

End Zintmul1rMorph.

Section ZintBigMorphism.

Variable R : ringType.

Lemma sumMz : forall I r (P : pred I) F,
 (\sum_(i <- r | P i) F i)%N%:zR = \sum_(i <- r | P i) ((F i)%:zR) :> R.
Proof. by apply: big_morph=> // x y; rewrite !natmulP -rmorphD. Qed.

Lemma prodMz : forall I r (P : pred I) F,
 (\prod_(i <- r | P i) F i)%N%:zR = \prod_(i <- r | P i) ((F i)%:zR) :> R.
Proof. by apply: big_morph=> // x y; rewrite !natmulP mulzM -rmorphM. Qed.

End ZintBigMorphism.

Section Frobenius.

Variable R : ringType.
Implicit Types x y : R.

Variable p : nat.
Hypothesis charFp : p \in [char R].

Local Notation "x ^f" := (Frobenius_aut charFp x).

Lemma Frobenius_aut_mulz : forall x n, (n *z x)^f = n *z x^f.
Proof.
move=> x [] n /=; first exact: Frobenius_aut_muln.
by rewrite !NegzE !mulNzr Frobenius_aut_opp Frobenius_aut_muln.
Qed.

Lemma Frobenius_aut_nat : forall n, (n%:zR)^f = n%:zR.
Proof. by move=> n; rewrite Frobenius_aut_mulz Frobenius_aut_1. Qed.

End Frobenius.

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

Lemma exprnP : forall x (n : nat), x ^+ n = x ^ n. Proof. by []. Qed.

Lemma exprnN : forall x (n : nat), x ^- n = x ^ -n%:Z.
Proof. by move=> x [] //; rewrite oppr0 expr0 invr1. Qed.

Lemma expr0z : forall x, x ^ 0 = 1. Proof. by []. Qed.

Lemma expr1z : forall x, x ^ 1 = x. Proof. by []. Qed.

Lemma exprN1z : forall x, x ^ (-1) = x^-1. Proof. by []. Qed.

Lemma exprNz_nat : forall x (n : nat), x ^ (-n%:Z) = (x ^ n)^-1.
Proof. by move=> x [] //; rewrite oppr0 expr0z invr1. Qed.

Lemma exp1rz : forall n, 1 ^ n = 1 :> R. 
Proof.
elim=> // n //= _; first by rewrite -exprnP exp1rn.
by rewrite -exprnN exp1rn invr1.
Qed.

Lemma exprSz_nat : forall x (n : nat), x ^ n.+1 = x * x ^ n.
Proof. exact: exprS. Qed.

Lemma exprSzr_nat : forall x (n : nat), x ^ n.+1 = x ^ n * x.
Proof. exact: exprSr. Qed.

Lemma exprz_add_nat : forall x (m n : nat), x ^ (m%:Z + n) = x ^ m * x ^ n.
Proof. exact: exprn_addr. Qed.

Lemma exprz_add_Nnat : forall x (m n : nat), 
  x ^ (-m%:Z + -n%:Z) = x ^ (-m%:Z) * x ^ (-n%:Z).
Proof. 
move=> x m n; rewrite -oppr_add !exprNz_nat addnC.
case ux: (GRing.unit x); first by rewrite exprz_add_nat invr_mul ?unitr_exp //.
case: (leqP n 0)=> [|hn].
  by rewrite leqn0; move/eqP->; rewrite add0n expr0z divr1.
case: (leqP m 0)=> [|hm].
  by rewrite leqn0; move/eqP->; rewrite addn0 expr0z invr1 mul1r.
by rewrite !invr_out ?unitr_pexp ?ux ?addn_gt0 ?hn // addnC exprz_add_nat.
Qed.

Lemma exp0rz : forall n, 0 ^ n = (n == 0)%:zR :> R.
Proof.
elim=> // n _ /=; first by rewrite exprSz_nat mul0r.
by rewrite exprNz_nat exprSz_nat mul0r invr0.
Qed.

Lemma exprSz : forall x n, GRing.unit x -> x ^ (1 + n) = x * x ^ n.
Proof.
move=> x; elim=> [|n _|n _] hx //; first by rewrite addr0 expr1z expr0z mulr1.
rewrite zintS {1}oppr_add addNKr -!exprnN.
by rewrite exprSr invr_mul ?unitr_exp // mulVKr.
Qed.

Lemma exprz_exp_nat : forall x m (n : nat), (x ^ m) ^ n = (x ^ (m * n)).
Proof.
move=> x m; elim=> [|n ihn]; first by rewrite mulr0 !expr0z.
rewrite exprSz_nat ihn; case: m {ihn}=> m; rewrite ?NegzE.
  by rewrite -!mulzM mulnS exprz_add_nat.
rewrite mulNr -mulzM -exprz_add_Nnat [_ n.+1]zintS.
by rewrite mulr_addr mulr1 mulzM mulNr.
Qed.

Lemma invr_exp : forall x n, (x ^ n)^-1 = x ^ (-n).
Proof. by move=> x [] n; rewrite ?exprNz_nat ?NegzE ?invrK ?opprK. Qed.

Lemma exprz_exp : forall x m n, (x ^ m) ^ n = (x ^ (m * n)).
Proof.
move=> x m [] n; rewrite ?NegzE; first by rewrite exprz_exp_nat.
by rewrite exprNz_nat exprz_exp_nat invr_exp mulrN.
Qed.

Lemma exprz_inv : forall x n, x^-1 ^ n = x ^ (-n).
Proof. by move=> x n; rewrite -exprN1z exprz_exp mulN1r. Qed.

Lemma exprzAC : forall x m n, (x ^ m) ^ n = (x ^ n) ^ m.
Proof. by move=> x m n; rewrite !exprz_exp mulrC. Qed.

Lemma exprz_out : forall x (n : nat), ~~ GRing.unit x -> x ^ (-n%:Z) = x ^ n.
Proof. by move=> x n nux; rewrite -exprnN -expr_inv invr_out. Qed.

Lemma exprz_addr : forall x, GRing.unit x -> forall m n, x ^ (m + n) = x ^ m * x ^ n.
Proof.
move=> x hx; elim=> [|m ihm|m ihm]; elim=> [|n _|n _] //=;
  rewrite ?(addr0, add0r, expr0z, mulr1, mul1r) //.
* by rewrite -!exprnP exprn_addr.
* by rewrite zintS -addrA !exprSz // ihm mulrA.
* rewrite !zintS {1}oppr_add addrAC addNKr addrC ihm.
  rewrite -!exprnN -!exprnP !exprS invr_mul ?unitr_exp //.
  by rewrite mulrA mulrVK.
* by rewrite -oppr_add addrC -!exprnN exprn_addr invr_mul ?unitr_exp.
Qed.

Lemma commr_expz : forall (x y : R) n, GRing.comm x y -> GRing.comm x (y ^ n).
Proof.
rewrite /GRing.comm => x y n com_xy.
elim: n=> [|n ihn|n ihn] //=; first by rewrite expr0z mul1r mulr1.
  by rewrite -exprnP commr_exp //.
case uy: (GRing.unit y).
  rewrite zintS oppr_add exprz_addr // -mulrA exprN1z -ihn !mulrA; congr (_ * _).
  by apply/eqP; rewrite (can2_eq (mulrVK _) (mulrK _)) // -mulrA com_xy mulKr.
by rewrite exprz_out ?uy // commr_exp.
Qed.

Lemma commr_invr : forall (x y : R), GRing.comm x y -> GRing.comm x (y ^-1).
Proof. by move=> *; rewrite -exprN1z; exact: commr_expz. Qed.

Lemma commr_expz_mull : forall x y n, GRing.unit x -> GRing.unit y ->
  GRing.comm x y -> (x * y) ^ n = x ^ n * y ^ n.
Proof.
move=> x y n ux uy com_xy; elim: n => [|n _|n _]; first by rewrite expr0z mulr1.
  by rewrite -!exprnP commr_exp_mull.
rewrite -!exprnN -!expr_inv com_xy -commr_exp_mull ?invr_mul//.
by apply: commr_invr; apply: commr_sym; apply: commr_invr.  
Qed.

End ExprzUnitRing.

Section Exprz_Zint_UnitRing.

Variable R : unitRingType.
Implicit Types x y : R.
Implicit Types m n : zint. 

Lemma exprz_mulzl_nat : forall x m (n : nat), (m *z x) ^ n = (m ^ n) *z x ^ n.
Proof.
move=> x m n; elim: n=> [|n ihn] //.
by rewrite !exprSz_nat ihn mulzrAl mulzrAr -mulzrA.
Qed.

Lemma zint_exp_nat : forall m (n : nat), m%:zR ^ n = (m ^ n)%:zR :> R.
Proof. by move=> m n; rewrite exprz_mulzl_nat exp1rz. Qed.

Lemma exprz_mulzl : forall x m n, GRing.unit x -> (@GRing.unit R m%:zR)
  -> (m *z x) ^ n = (m%:zR ^ n) * x ^ n :> R.
Proof.
move=> x m n hm hn; rewrite -[_ *z x]mulzrl commr_expz_mull //.
by apply: commr_sym; apply: commr_zint.
Qed.

Lemma expNrz_nat : forall x (n : nat), (- x) ^ n = (-1) ^ n * x ^ n :> R.
Proof. exact: exprN. Qed.

Lemma expNrz : forall x n, (- x) ^ n = (-1) ^ n * x ^ n :> R.
move=> x [] n; rewrite ?NegzE 1?expNrz_nat //.
case ux: (GRing.unit x); last first.
  rewrite exprz_out ?[x ^ _]exprz_out ?unitr_opp ?ux //.
  by rewrite -exprz_inv invrN invr1 expNrz_nat.
rewrite exprNz_nat expNrz_nat.
rewrite invr_mul -?exprNz_nat -?commr_expz_mull 
    ?(mulrN1, mulN1r, unitr_opp, unitr1, unitr_pexp) //.
  by apply: commr_sym; apply: commrN1.
by apply: commrN1.
Qed.

Lemma unitr_expz : forall x n, GRing.unit x -> GRing.unit (x ^ n).
Proof. by move=> x [] *; rewrite ?NegzE -?exprz_inv ?unitr_exp ?unitr_inv. Qed.

Lemma unitr_n0expz : forall x n, n != 0 -> GRing.unit (x ^ n) = GRing.unit x.
Proof.
by move=> x [] *; rewrite ?NegzE -?exprz_inv ?unitr_pexp ?unitr_inv ?lt0n.
Qed.

End Exprz_Zint_UnitRing.

Section ExprzIdomain.

Variable R : idomainType.
Implicit Types x y : R.
Implicit Types m n : zint. 

Lemma expfz_eq0 : forall x n, (x ^ n == 0) = (n != 0) && (x == 0).
Proof.
by move=> x [] n; rewrite ?NegzE -?exprz_inv ?expf_eq0 ?lt0n ?invr_eq0.
Qed.

Lemma expfz_neq0 : forall x n, x != 0 -> x ^ n != 0.
Proof. by move=> x n x_nz; rewrite expfz_eq0; apply/nandP; right. Qed.

End ExprzIdomain.

Section ExprzField.

Variable F : fieldType.
Implicit Types x y : F.
Implicit Types m n : zint. 

Lemma expfz_addr : forall x m n, x != 0 -> x ^ (m + n) = x ^ m * x ^ n.
Proof. by move=> x m n hx; rewrite exprz_addr ?unitfE. Qed.

End ExprzField.

(* Todo : div theory of zint *)