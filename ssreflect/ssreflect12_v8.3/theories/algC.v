(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq bigop div ssralg.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.

(**************************************************************************)
(* This file deals is an axiomatic presentation of an algebraic closed    *)
(* field over R                                                           *)
(*    C : the closed field                                                *)
(*    x^* = conjugate                                                     *)
(*   0 <= x : x is a positive real                                        *)
(*   x <= y : (y - x) is a positive real                                  *)
(*    x < y : (y - x) is a real positive real                             *)
(*   sqrC x : square root such that sqrt x^2 = x for 0 <= x               *)
(*  normC x : norm of x i.e. sqrC(x * x^* )                               *)
(*  isRatC  : test for rationality                                        *) 
(*  getRatC : the rational components,                                    *)
(*            if isRatC x and (n,d) = getRatC x then                      *)
(*               x = (-1)^b * n%:R * (d.+1)%:R^-1                         *)
(*  isNatC  : test for naturality                                         *) 
(*  getNatC : the natural component                                       *)
(*            if isNatC x and x = getNatC x)%:R                           *)
(**************************************************************************)

Parameter C : closedFieldType.
Axiom Cchar : [char C] =i pred0.

Parameter conjC : {rmorphism C -> C}.
Notation "x ^* " := (conjC x) (at level 2, format "x ^*") : C_scope.
Open Scope C_scope.

Axiom conjCK : involutive conjC.

Parameter repC : C -> bool. (* C -> R^+ *)
Axiom repCD : forall x y, repC x -> repC y -> repC (x + y).
Axiom repCMl : forall x y, x != 0 -> repC x -> repC (x * y) = repC y.
Axiom repC_anti : forall x, repC x -> repC (-x) -> x = 0.
Axiom repC_unit_exp: forall x n, repC x -> ((x^+n.+1 == 1) = (x == 1)).
Axiom repC_pconj : forall x, repC (x * x ^*).
Axiom repC_conjI : forall x, repC x -> x^* = x.
Axiom repC1 : repC 1.

Lemma repC_inv : forall x, repC (x^-1) = repC x.
Proof.
move=> x; case: (x =P 0)=> [->|]; first by rewrite invr0.
move/eqP; move=> Hx; apply/idP/idP=> Hp.
  by rewrite -(repCMl _ (invr_neq0 Hx)) // mulVf // repC1.
by rewrite -(repCMl _ Hx) // mulfV // repC1.
Qed.

Lemma repC_conj : forall x, repC (x ^*) = repC (x).
Proof.
by move=>x; apply/idP/idP=>Hp; first rewrite -[x]conjCK; 
   rewrite (repC_conjI Hp).
Qed.

Lemma repC0 : repC 0.
Proof. by rewrite -[0](mul0r (0 ^*)) repC_pconj. Qed.

Lemma repC_nat : forall n, repC (n%:R).
Proof.
by elim=> [|n IH]; [exact: repC0 | rewrite -addn1 natr_add repCD // repC1].
Qed.

Lemma conjC_nat : forall n, (n%:R)^* = n%:R.
Proof. exact: rmorph_nat. Qed.

Lemma conjC0 : 0 ^* = 0.
Proof. exact: (conjC_nat 0). Qed.

Lemma conjC1 : 1 ^* = 1.
Proof. exact: (conjC_nat 1). Qed.

Lemma conjC_eq0 : forall x, (x ^* == 0) = (x == 0).
Proof.
move=> x; apply/eqP/eqP=> H; last by rewrite H (conjC_nat 0).
by rewrite -[x]conjCK H (conjC_nat 0).
Qed.

Definition leC x y := repC (y - x).

Notation "x <= y" := (leC x y) : C_scope.

Definition ltC x y := ((x != y) && (x <= y)).

Notation " x < y " := (ltC x y) : C_scope.

Lemma leC_nat : forall n, 0 <= n%:R.
Proof. by move=> n; rewrite /leC subr0 repC_nat. Qed.

Lemma leC_refl: reflexive leC.
Proof. move=> x; rewrite /leC subrr; exact repC0. Qed.

Lemma ltCW : forall x y, x < y -> x <= y.
Proof. by move=> x y; case/andP. Qed.

Lemma leC_add2l : forall z x y, (z + x <= z + y) = (x <= y).
Proof.
by move=> z x y; rewrite /leC oppr_add addrA [z + _]addrC addrK.
Qed.

Lemma leC_add2r : forall z x y, (x + z <= y + z) = (x <= y).
Proof. by move=> z x y; rewrite ![_ +z]addrC leC_add2l. Qed.

Lemma posC_add: forall x y, 0 <= x -> 0 <= y -> 0 <= x + y.
Proof. by move=> x y; rewrite /leC !subr0; exact: repCD. Qed.

Lemma leC_trans: transitive leC.
Proof.
move=> x y z Hx Hy.
by move: (repCD Hy Hx); rewrite addrA subrK.
Qed.

Lemma leC_add: forall x y z t : C, x <= z -> y <= t -> x + y <= z + t.
Proof.
move=> x y z t Hx Hy.
by apply: (@leC_trans (z + y)); [rewrite leC_add2r | rewrite leC_add2l].
Qed.

Lemma posC_mulr: forall x y, 0 < x -> 0 <= x * y = (0 <= y).
Proof. 
move=> x y; case/andP; rewrite /leC !subr0; move=>*.
by apply: repCMl; rewrite // eq_sym. 
Qed.

Lemma posC_mull: forall x y, 0 < x -> 0 <= y * x = (0 <= y).
Proof. move=> x y; rewrite mulrC; exact: posC_mulr. Qed.

Lemma posC_mul : forall x y : C, 0 <= x -> 0 <= y -> 0 <= x * y.
Proof.
move=> x y Hx Hy.
case: (boolP (x == 0)); first by move/eqP->; rewrite mul0r leC_refl.
by move=> Hdx; rewrite posC_mulr //; apply/andP; rewrite eq_sym.
Qed.

Lemma leC_anti: forall x y, x <= y -> y <= x -> x = y.
Proof.
move=> x y Hx Hy; apply/eqP; rewrite -subr_eq0; apply/eqP.
by apply: repC_anti; rewrite // oppr_sub.
Qed.

Lemma posC_unit_exp: forall x n, 0 <= x ->  (x ^+ n.+1 == 1) = (x == 1).
Proof. by move=> x n Hx; apply: repC_unit_exp; rewrite -[x]subr0. Qed.

Lemma posC_conjK: forall x, 0 <= x -> x^* = x.
Proof. by move=> x Hx; apply: repC_conjI; rewrite -[x]subr0. Qed.

Lemma posC1: 0 <= 1.
Proof. by rewrite /leC subr0 repC1. Qed.

Lemma posC_inv : forall x, (0 <= x^-1) = (0 <= x).
Proof. move=> x; rewrite /leC !subr0; exact: repC_inv. Qed.

Lemma posC_conj : forall x, (0 <= x ^*) = (0 <= x).
Proof. move=> x; rewrite /leC !subr0; exact: repC_conj. Qed.

Lemma posC_sum: 
   forall (I : Type) (r : seq I) (P : pred I) (F : I -> C),
   (forall i, P i -> 0 <= F i) -> 0 <= \sum_(j <- r | P j) F j.
Proof.
move=> i r P F1 H; elim: r=> [|y r Hrec].
  by rewrite big_nil=> *; exact: leC_refl.
rewrite big_cons; case E1: (P _)=> //.
by apply: posC_add=> //; exact: H.
Qed.

Lemma posC_add_eq0: forall x y,
  0 <= x -> 0 <= y -> (x + y == 0) = ((x == 0) && (y == 0)).
Proof.
move=> x y Hx Hy; apply/eqP/andP=>[Hxy|]; last first.
  by case; do 2 move/eqP->; exact: addr0.
split; apply/eqP; apply: leC_anti=> //.
  by rewrite -(leC_add2r y) Hxy add0r.
by rewrite -(leC_add2l x) Hxy addr0.
Qed.

Lemma posC_sum_eq0: 
   forall (I : eqType) (r : seq I) (P : pred I) (F : I -> C),
   (forall i, P i -> 0 <= F i) ->
   \sum_(j <- r | P j) F j = 0 ->
   (forall i, i \in r -> P i -> F i = 0).
Proof.
move=> I r P F HN; elim: r=> [|y r Hrec] //.
rewrite big_cons; case HP: (P _)=> Hs; last first.
  move=> i Hi Hp; apply: Hrec=> //.
  move: Hi; rewrite in_cons; case/orP=> //.
  by move/eqP=>Hi; case/negP: HP; rewrite -Hi.
move=> i Hi HP1.
move/eqP: Hs; rewrite posC_add_eq0 ?HN //.
  case/andP; move: Hi; rewrite in_cons; case/orP; first by do 2 move/eqP->.
  by move=> Hin _; move/eqP=> Hs; exact: Hrec.
by apply: posC_sum.
Qed.

Variable sqrC: C -> C.
Axiom sqrCK : forall c, (sqrC c) ^+ 2 = c.
Axiom repC_sqr : forall c, repC (sqrC c) = repC c.
Axiom sqrC_mul : {morph sqrC: x y / x * y}.

Lemma sqrC_sqr : forall c, (sqrC (c^+2) == c) || (sqrC (c^+2) == -c).
Proof.
move=> c; set sc := sqrC _.
suff: (sc - c) * (sc + c) == 0.
  rewrite mulf_eq0; case/orP; first by rewrite subr_eq0=>->.
  by rewrite orbC -{1}[c]opprK subr_eq0=>->.
rewrite mulr_addr !mulr_subl addrA [c * _]mulrC subrK subr_eq0.
by rewrite -{2}[sc]expr1 -exprS sqrCK.
Qed.

Lemma sqrC0 : sqrC 0 = 0.
Proof. 
have:= sqrCK 0; rewrite exprS expr1.
by move/eqP; rewrite mulf_eq0; case/orP; move/eqP.
Qed.

Lemma sqrC_eq0 : forall c, (sqrC c == 0) = (c == 0).
Proof.
move=> c; apply/eqP/eqP; last by move->; exact: sqrC0.
by rewrite -{2}[c]sqrCK=>->; rewrite exprS mul0r.
Qed.

Lemma sqrC_pos : forall c, (0 <= sqrC c) = (0 <= c).
Proof. by move=> c; rewrite /leC !subr0 repC_sqr. Qed.

Lemma sqrC_sqr_pos : forall c, 0 <= c -> sqrC (c^+2) = c.
Proof.
move=> c Hc; case/orP: (sqrC_sqr c)=>[|HH]; first by move/eqP.
suff->: c = 0 by rewrite exprS mul0r sqrC0.
apply: leC_anti=> //; rewrite /leC sub0r.
rewrite -(eqP HH) repC_sqr -[_^+_]subr0; by apply: posC_mul.
Qed.

Lemma sqrC1: sqrC 1 = 1.
Proof. by rewrite -{2}(sqrC_sqr_pos posC1) exprS mul1r. Qed. 
 
Definition normC x := sqrC (x * x^*).

Axiom normC_add: forall x y,  normC (x + y) <= normC x + normC y.
Axiom normC_add_eq: forall x y : C, 
  x != 0 -> normC (x + y) = normC(x) + normC(y) -> 0 <= y/x.

Lemma posC_norm : forall x, 0 <= normC x.
Proof. 
move=> x; rewrite /leC !subr0 repC_sqr; exact: repC_pconj.
Qed.

Lemma normC_pos : forall c, 0 <= c -> normC c = c.
Proof.
by move=> c Hc; rewrite /normC posC_conjK // (sqrC_sqr_pos Hc).
Qed.

Lemma normC0 : normC 0 = 0.
Proof. by rewrite normC_pos // leC_refl. Qed.

Lemma normC_eq0 : forall c, (normC c == 0) = (c == 0).
Proof.
move=> c; apply/idP/eqP; last by move->; rewrite normC0.
rewrite sqrC_eq0 mulf_eq0; case/orP; first by move/eqP.
by rewrite conjC_eq0; move/eqP.
Qed.

Lemma normC1 : normC 1 = 1.
Proof. by rewrite normC_pos // posC1. Qed.

Lemma normC_mul :  {morph normC: x y / x * y}.
Proof.
move=> x y; rewrite /normC rmorphM -sqrC_mul -!mulrA; 
by congr sqrC; congr (_ * _); rewrite mulrC -!mulrA [y * _]mulrC.
Qed.

Lemma normC_exp : forall x n, normC (x^+n) = normC x ^+ n.
Proof.
move=> x; elim=> [|n IH]; first by rewrite !expr0 normC1.
by rewrite exprS normC_mul IH exprS.
Qed.

Lemma normC_conj: forall x, normC (x^*) = normC x.
Proof. by move=> x; rewrite /normC conjCK mulrC. Qed.

Lemma normC_inv : forall x, x^-1 = (normC x)^-2 * x^*.
Proof.
move=> x; case: (x =P 0)=> [->|]; first by rewrite conjC0 mulr0 invr0.
move/eqP=> Hx.
have F1: normC x ^+ 2 != 0.
  by rewrite exprS expr1; apply: mulf_neq0; rewrite normC_eq0.
apply: (mulfI F1); rewrite mulrA divff // mul1r sqrCK [x * _]mulrC.
by rewrite -mulrA divff // mulr1.
Qed.

Lemma conjC_inv: forall x, (x^-1)^* = (x^*)^-1.
Proof.
move=> x; rewrite normC_inv rmorphM conjCK.
rewrite (normC_inv x^*) conjCK; congr (_ * _).
rewrite normC_conj; apply: posC_conjK.
by rewrite posC_inv exprS expr1 posC_mul // posC_norm.
Qed.

Lemma normC_sum: 
   forall (I : eqType) (r : seq I) (P : pred I) (F : I -> C),
   normC (\sum_(i <- r | P i) F i) <= \sum_(i <- r | P i) normC(F i).
Proof.
move=> I r P F; elim: r=> [|i r Hrec].
  by rewrite !big_nil normC0 leC_refl.
rewrite !big_cons; case HP: (P _)=> //.
by apply: (leC_trans (normC_add _ _)); rewrite leC_add2l.
Qed.

Variable getRatC : C -> (bool * nat * nat).
Definition isRatC c := 
   match getRatC c with (b,n,d) => c == (-1)^+b * n%:R * d.+1%:R^-1 end.

Axiom isRatCP :
  forall c,
   reflect
     (exists b: bool, exists p, c = (-1)^+b * p.1%:R * p.2.+1%:R^-1)
     (isRatC c).

Lemma isRatC_opp : forall c , isRatC (-c) = isRatC c.
Proof.
by move=>c;apply/isRatCP/isRatCP=> [] [b [[n d]] H];
   exists (~~b); exists (n,d); first rewrite -[c]opprK;
   rewrite H -!mulNr; case b; rewrite !(expr0,expr1,opprK).
Qed.

Lemma isRatC_add : forall c1 c2, isRatC c1 -> isRatC c2 -> isRatC (c1 + c2).
Proof.
move=> c1 c2; case/isRatCP=> b1 [[n1 d1] ->]; case/isRatCP=> b2 [[n2 d2] ->].
case: (b1 =P b2)=> [<-|Hb].
  apply/isRatCP; exists b1; exists (n1 * d2.+1 + n2 * d1.+1,(d1.+1 * d2.+1).-1)%N.
  rewrite -!mulrA -mulr_addr; congr (_ * _)%R.
  have F1: (d1.+1 * d2.+1)%:R != 0 :> C by move/GRing.charf0P: Cchar => ->.
  apply: (mulIf F1); apply: sym_equal.
  rewrite -mulrA prednK // mulVr ?GRing.unitfE // mulr1 natr_add !natr_mul.
  rewrite mulr_addl mulrA mulrVK; last first.
    by rewrite ?GRing.unitfE; move/GRing.charf0P: Cchar => ->.
  rewrite [d1.+1%:R * _]mulrC mulrA mulrVK // ?GRing.unitfE.
  by move/GRing.charf0P: Cchar => ->.
have->: (-1) ^+ b2 = -(-1) ^+ b1 :> C.
  by case: b1 Hb; case: b2=> // _; rewrite expr1 opprK.
rewrite !mulNr.
wlog HH : n1 d1 n2 d2 / (n2 * d1.+1 <= n1 * d2.+1)%N=> [HH|].
  case: (leqP  (n2 * d1.+1)%N (n1 * d2.+1)%N)=> H; first by apply: HH.
  by rewrite -isRatC_opp oppr_sub HH // ltnW.
apply/isRatCP; exists b1; 
  exists (n1 * d2.+1 - n2 * d1.+1,(d1.+1 * d2.+1).-1)%N.
rewrite -!mulrA -mulr_subr; congr (_ * _).
have F1: (d1.+1 * d2.+1)%:R != 0 :> C by move/GRing.charf0P: Cchar => ->.
apply: (mulIf F1); apply: sym_equal.
rewrite -mulrA prednK // mulVr ?GRing.unitfE // mulr1 natr_sub // !natr_mul.
rewrite mulr_subl mulrA mulrVK; last first.
  by rewrite ?GRing.unitfE; move/GRing.charf0P: Cchar => ->.
rewrite [d1.+1%:R * _]mulrC mulrA mulrVK // ?GRing.unitfE.
by move/GRing.charf0P: Cchar => ->.
Qed.

Lemma isRatC_addr : forall c1 c2, isRatC c1 -> isRatC (c1 + c2) = isRatC c2.
Proof.
move=> c1 c2 Hc; apply/idP/idP=> HH; last by apply: isRatC_add.
have->: c2 = (-c1) + (c1 + c2) by rewrite addrA addNr add0r.
by apply: isRatC_add; rewrite // isRatC_opp.
Qed.

Lemma isRatC_addl : forall c1 c2, isRatC c2 -> isRatC (c1 + c2) = isRatC c1.
Proof. by move=> c1 c2; rewrite addrC; exact: isRatC_addr. Qed.

Lemma isRatC_inv : forall c, isRatC c^-1 = isRatC c.
Proof.
have F1: forall b, GRing.unit ((-1)^+b : C).
  by move=> b; apply: GRing.unitr_exp; rewrite unitr_opp unitr1.
have F2: forall (b : bool), ((-1)^+b)^-1 = (-1)^+b :> C.
  by case; rewrite !(invrN,invr1).
have F3: forall n, GRing.unit ((n.+1)%:R : C).
  by move=> n; rewrite ?GRing.unitfE; move/GRing.charf0P: Cchar => ->.
move=> c; apply/isRatCP/isRatCP=> [] [b [[[|n] d] H]].
- exists true; exists (0,1)%N.
  by move: H; rewrite !(mulr0,mul0r); move/eqP; rewrite GRing.invr_eq0; move/eqP.
- exists b; exists (d.+1,n).
  rewrite -[c]invrK H !invr_mul ?(GRing.unitr_mulr,GRing.unitr_inv) //=.
  by rewrite invrK F2 -!mulrA [(-1) ^+ b * _]mulrC !mulrA.
- exists true; exists (0,1)%N.
  by move: H; rewrite !(mulr0,mul0r); move/eqP; rewrite -GRing.invr_eq0; move/eqP.
exists b; exists (d.+1,n); rewrite H.
rewrite !invr_mul ?(GRing.unitr_mulr,GRing.unitr_inv)  //=.
by rewrite invrK [_^+ _ * _]mulrC -!mulrA; congr (_ * _); rewrite F2 mulrC.
Qed.

Lemma isRatC_mul : forall c1 c2, isRatC c1 -> isRatC c2 -> isRatC (c1 * c2).
Proof.
move=> c1 c2; case/isRatCP=> b1 [[n1 d1] ->]; case/isRatCP=> b2 [[n2 d2] ->].
apply/isRatCP; exists (b1!=b2); exists (n1 * n2,(d1.+1 * d2.+1).-1)%N.
have->: (-1) ^+ (b1 != b2) = (-1) ^+ b1 * (-1) ^+ b2 :> C.
  by case: b1; case: b2; rewrite ?(mulNr,mul1r,opprK).
rewrite !natr_mul prednK // -!mulrA; congr (_ * _).
rewrite [_^+b2 * (n1%:R *_)]mulrC -!mulrA; congr (_ * _).
rewrite natr_mul invr_mul; last 2 first.
- by rewrite ?GRing.unitfE; move/GRing.charf0P: Cchar => ->.
- by rewrite ?GRing.unitfE; move/GRing.charf0P: Cchar => ->.
by rewrite mulrC -!mulrA mulrC -!mulrA.
Qed.

Lemma isRatC_mulr : forall c1 c2, c1 !=0 -> isRatC c1 -> isRatC (c1 * c2) = isRatC c2.
Proof.
move=> c1 c2 Hd Hc; apply/idP/idP=> HH; last by apply: isRatC_mul.
have->: c2 = (c1^-1) * (c1 * c2) by rewrite mulrA mulVf // mul1r.
by apply: isRatC_mul; rewrite // isRatC_inv.
Qed.

Lemma isRatC_mull : forall c1 c2, c2 !=0 -> isRatC c2 -> isRatC (c1 * c2) = isRatC c1.
Proof. by move=> c1 c2; rewrite mulrC; exact: isRatC_mulr. Qed.

Lemma isRatC_conj : forall c, isRatC c -> c^* = c.
Proof.
move=> c; case/isRatCP=> b [[n d]] ->.
by rewrite !rmorphM conjC_inv !conjC_nat rmorph_sign.
Qed.

Lemma isRatC_nat: forall n, isRatC n%:R.
Proof.
move=> n; apply/isRatCP; exists false; exists (n,0)%N.
by rewrite expr0 mul1r invr1 mulr1.
Qed.

Definition isNatC (c: C) : bool :=
 match getRatC c with (b,n,d) => c == (n %/ d.+1)%:R end.

Lemma isNatCP: forall c, reflect (exists n, c = n%:R) (isNatC c).
Proof.
move=> c; apply: (iffP idP)=>[|[n->]].
  by rewrite /isNatC; case getRatC=> [[b n] d]; move/eqP->; 
     exists (n %/ d.+1)%N.
move: (isRatC_nat n); rewrite /isRatC /isNatC; case getRatC=> [[b1 n1] d1].
have Hnd: GRing.unit (d1.+1%:R : C).
  by rewrite GRing.unitfE; move/GRing.charf0P: Cchar=> ->.
case: b1.
  rewrite expr1; move/eqP=> HC.
  have: (n1 + n * d1.+1)%:R = 0 :> C.
    rewrite natr_add natr_mul HC -!mulrA mulVr //.
    by rewrite mulr1 mulN1r subrr.
  move/eqP; move/GRing.charf0P: Cchar=> ->; rewrite addn_eq0.
  by case/andP; move/eqP=> ->; case: {HC}n.
rewrite mul1r;move/eqP=> Hn.
pose m := (n * d1.+1)%N.
have F1: n1%:R = m%:R :> C.
  by rewrite /m natr_mul Hn -mulrA mulVr // mulr1.
suff ->: n1 = m by rewrite mulnK.
case: (leqP n1 m)=> HN.
  suff F2: (m - n1 == 0)%N by rewrite -(subnKC HN) (eqP F2) addn0.
  by move/GRing.charf0P: Cchar=> <-; rewrite natr_sub // F1 subrr.
have Hnn := ltnW HN.
have F2: (n1 - m == 0)%N.
  by move/GRing.charf0P: Cchar=> <-; rewrite natr_sub // F1 subrr.
by rewrite -(subnKC Hnn) (eqP F2) addn0.
Qed.

Lemma isNatC_isRatC: forall c, isNatC c -> isRatC c.
Proof.
move=> c; case/isNatCP=> n ->; exact: isRatC_nat.
Qed.

Lemma isNatC_nat: forall n, isNatC (n%:R).
Proof. by move=> n; apply/isNatCP; exists n. Qed.

Lemma isNatC_add: forall c1 c2, isNatC c1 -> isNatC c2 -> isNatC (c1 + c2).
Proof.
move=> c1 c2; case/isNatCP=> n1 ->; case/isNatCP=> n2 ->.
by rewrite -natr_add isNatC_nat.
Qed.

Lemma isNatC_mul: forall c1 c2, isNatC c1 -> isNatC c2 -> isNatC (c1 * c2).
Proof.
move=> c1 c2; case/isNatCP=> n1 ->; case/isNatCP=> n2 ->.
by rewrite -natr_mul isNatC_nat.
Qed.

Lemma isNatC_sum: 
   forall (I : Type) (r : seq I) (P : pred I) (F : I -> C),
   (forall i, P i -> isNatC  (F i)) -> isNatC (\sum_(j <- r | P j) F j).
Proof.
move=> i r P F1 H; elim: r=> [|y r Hrec].
  by rewrite big_nil=> *; exact: (isNatC_nat 0).
rewrite big_cons; case E1: (P _)=> //.
by apply: isNatC_add=> //; exact: H.
Qed.

Lemma isNatCMn: forall x n, isNatC x -> isNatC (x*+n).
Proof.
move=> x; elim=> [|n IH Hx]; first by rewrite mulr0n (isNatC_nat 0).
by rewrite mulrSr isNatC_add // IH.
Qed.

Lemma posC_isNatC : forall c, isNatC c -> 0 <= c.
Proof.
by move=> c; case/isNatCP=> n ->; exact: leC_nat.
Qed.

Lemma isNatC_conj : forall c, isNatC c -> c^* = c.
Proof.
by move=> c; case/isNatCP=> n ->; exact: conjC_nat.
Qed.

Lemma isNatC_sum_eq1 : 
   forall (I : eqType) (r : seq I) (P : pred I) (F : I -> C),
   (forall i, P i -> isNatC (F i)) -> uniq r ->
   \sum_(j <- r | P j) F j = 1%:R ->
   (exists i, [/\ i \in r, P i, F i = 1 &
               forall j, j!=i -> j \in r -> P j -> F j = 0]).
Proof.
move=> I r P F HN; elim: r=> [_|y r Hrec].
  by rewrite big_nil; move/eqP; rewrite eq_sym (negPf (nonzero1r _)).
rewrite cons_uniq; case/andP=> [Hyr Hu].
rewrite big_cons; case HP: (P _)=> Hs; last first.
  case: Hrec=> // => i [Hin HPi HFi HF]; exists i; split=> //.
    by rewrite in_cons Hin orbT.
  move=> j Hji; rewrite in_cons; case/orP=> //; last by exact: HF.
  by move/eqP->; rewrite HP.
case/isNatCP: (HN _ (idP HP))=> n Hn.
have: isNatC (\sum_(j <- r | P j) F j) by apply: isNatC_sum.
case/isNatCP=> m Hm.
move: Hs; rewrite Hn Hm -natr_add.
case: n Hn=> [|n Hn]; case: m Hm=>[|m Hm].
- by move=> _ _; move/eqP; rewrite eq_sym (negPf (nonzero1r _)).
- case: m Hm.
    move=> Hs HF _; case: Hrec=> // => j [HInj HPj HFj HF0].
    exists j; split=> //; first by rewrite in_cons HInj orbT.
    move=> k Hk; rewrite in_cons; case/orP; first by move/eqP->.
    by exact: HF0.
  move=> n _ _.
  rewrite -[1%:R]add0r add0n -addn1 natr_add => HH.
  by move: (addIr HH); move/eqP; move/charf0P: Cchar->.
- case: n Hn=> [Hn Hs _|n Hn Hs].
    exists y; split=> //; first by rewrite in_cons eqxx.
    move=> j Hjy; rewrite in_cons; case/orP; first by rewrite (negPf Hjy).
    move=> Hj HPj; apply: (posC_sum_eq0 _ Hs)=> //.
    move=> i HPI; apply: posC_isNatC; exact: HN.
  rewrite -[1%:R]add0r addn0 -addn1 natr_add => HH.
  by move: (addIr HH); move/eqP; move/charf0P: Cchar->.
rewrite -[1%:R]add0r addnS -addn1 natr_add => HH.
by move: (addIr HH); move/eqP; move/charf0P: Cchar->.
Qed.

Definition getNatC (c: C) : nat :=
 match getRatC c with (b,n,d) => (n %/ d.+1)%N end.

Lemma getNatCP: forall c, isNatC c = (c == (getNatC c)%:R).
Proof.
move=> c;apply/idP/eqP=>[|->]; last by apply: isNatC_nat.
by rewrite /isNatC /getNatC; case: getRatC=> [[b n]] d; move/eqP.
Qed.