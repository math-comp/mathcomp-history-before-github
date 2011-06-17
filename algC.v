(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq choice div fintype.
Require Import bigop prime ssralg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(**************************************************************************)
(* This file deals is an axiomatic presentation of an algebraic closed    *)
(* field over R                                                           *)
(*       algC : the closed field                                          *)
(*        x^* : conjugate                                                 *)
(*     0 <= x : x is a positive real                                      *)
(*     x <= y : (y - x) is a positive real                                *)
(*      x < y : (y - x) is a real positive real                           *)
(*    sqrtC x : square root such that sqrt x^2 = x for 0 <= x             *)
(*    normC x : norm of x i.e. sqrC(x * x^* )                             *)
(*    isNatC  : test for natural numbers                                  *)
(*    getNatC : the natural component                                     *)
(*              if isNatC x then x = (getNatC x)%:R                       *)
(*      isZC  : test for integers                                         *)
(*      getZC : the integer component                                     *)
(*              if isZC x then x = let (n,b) := getZC x in (-1)^b * n%:R  *)
(**************************************************************************)

Parameter algC : closedFieldType.
Parameter conjC : {rmorphism algC -> algC}.
Parameter repC : algC -> bool. (* C -> R^+ *)

Notation "x ^* " := (conjC x) (at level 2, format "x ^*") : C_scope.
Open Scope C_scope.
Delimit Scope C_scope with C.

Axiom conjCK : involutive conjC.
Axiom repCD : forall x y, repC x -> repC y -> repC (x + y).
Axiom repCMl : forall x y, x != 0 -> repC x -> repC (x * y) = repC y.
Axiom repC_anti : forall x, repC x -> repC (- x) -> x = 0.
Axiom repC_pconj : forall x, repC (x * x ^*).
Axiom realC_archimedean : forall x, repC x ->
  exists n, [&& repC (x - n%:R), repC (n.+1%:R - x) & x != n.+1%:R].

(*   All these are redundant axioms / parametere.                             *)
(* Axiom Cchar : [char algC] =i pred0.                                        *)
(* Axiom Cchar : [char algC] =i pred0.                                        *)
(* Axiom repC_unit_exp : forall x n, repC x -> (x ^+ n.+1 == 1) = (x == 1).   *)
(* Axiom repC_conjI : forall x, repC x -> x^* = x.                            *)
(* Axiom repC1 : repC 1.                                                      *)
(* Variable sqrtC : algC -> algC.                                             *)
(* Axiom sqrtCK : forall c, (sqrtC c) ^+ 2 = c.                               *)
(* Axiom repC_sqrt : forall c, repC (sqrtC c) = repC c.                       *)
(* Axiom sqrtC_mul : {morph sqrtC: x y / x * y}. GG -- This is inconsistent!  *)
(* Axiom normC_add : forall x y,  normC (x + y) <= normC x + normC y.         *)
(* Axiom normC_add_eq : forall x y : algC,                                    *)
(*     normC (x + y) = normC(x) + normC(y) ->                                 *)
(*   exists2 k, normC k = 1 & ((x == normC x * k) && (y == normC y * k)).     *)
(* Parameter getNatC : algC -> nat.                                           *)
(* Axiom getNatC_def : forall c,                                              *)
(*  if (0 <= c) then ((getNatC c)%:R <= c) && (c < (getNatC c + 1)%:R)        *)
(*  else getNatC c == 0%N.                                                    *)

Lemma repC1 : repC 1.
Proof. by rewrite -(mulr1 1) -{2}(rmorph1 conjC) repC_pconj. Qed.

Lemma repC_inv x : repC (x^-1) = repC x.
Proof.
case: (x =P 0)=> [->|]; first by rewrite invr0.
move/eqP=> Hx; apply/idP/idP=> Hp.
  by rewrite -(repCMl _ (invr_neq0 Hx)) // mulVf // repC1.
by rewrite -(repCMl _ Hx) // mulfV // repC1.
Qed.

Lemma repC_conj x : repC x^* = repC x.
Proof.
wlog suffices: x / repC x -> repC x^*.
  by move=> IH; apply/idP/idP=> /IH; rewrite ?conjCK.
have [-> | nz_x pos_x] := eqVneq x 0; first by rewrite rmorph0.
by rewrite -(repCMl _ nz_x pos_x) repC_pconj.
Qed.

Lemma repC0 : repC 0.
Proof. by rewrite -[0](mul0r (0 ^*)) repC_pconj. Qed.

Lemma repC_nat n : repC n%:R.
Proof.
by elim: n=> [|n IH]; [exact: repC0 | rewrite -addn1 natr_add repCD // repC1].
Qed.

Lemma conjC_nat n : (n%:R)^* = n%:R.
Proof. exact: rmorph_nat. Qed.

Lemma conjC0 : 0^* = 0.
Proof. exact: (conjC_nat 0). Qed.

Lemma conjC1 : 1^* = 1.
Proof. exact: (conjC_nat 1). Qed.

Lemma conjC_eq0 x : (x^* == 0) = (x == 0).
Proof.
apply/eqP/eqP=> H; last by rewrite H (conjC_nat 0).
by rewrite -[x]conjCK H (conjC_nat 0).
Qed.

Definition leC x y := repC (y - x).

Notation "x <= y" := (leC x y) : C_scope.

Definition ltC x y := ((y != x) && (x <= y)).

Notation " x < y " := (ltC x y) : C_scope.

Lemma ltCE x y : (x < y) = ((y != x) && (x <= y)).
Proof. by []. Qed.

Lemma posC_pconj x : 0 <= x * x ^*.
Proof. by rewrite /leC subr0 repC_pconj. Qed.

Lemma posC_nat n : 0 <= n%:R.
Proof. by rewrite /leC subr0 repC_nat. Qed.

Lemma leC_refl : reflexive leC.
Proof. move=> x; rewrite /leC subrr; exact repC0. Qed.

Lemma ltCW x y : x < y -> x <= y.
Proof. by case/andP. Qed.

Lemma leC_add2l z x y : (z + x <= z + y) = (x <= y).
Proof. by rewrite /leC oppr_add addrA [z + _]addrC addrK. Qed.

Lemma leC_add2r z x y : (x + z <= y + z) = (x <= y).
Proof. by rewrite ![_ +z]addrC leC_add2l. Qed.

Lemma posC_add x y : 0 <= x -> 0 <= y -> 0 <= x + y.
Proof. by rewrite /leC !subr0; exact: repCD. Qed.

Lemma leC_trans : transitive leC.
Proof.
by move=> x y z Hx Hy; move: (repCD Hy Hx); rewrite addrA subrK.
Qed.

Lemma leC_add x y z t : x <= z -> y <= t -> x + y <= z + t.
Proof.
move=> Hx Hy.
by apply: (@leC_trans (z + y)); [rewrite leC_add2r | rewrite leC_add2l].
Qed.

Lemma posC_mulr x y : 0 < x -> (0 <= x * y) = (0 <= y).
Proof.
case/andP; rewrite /leC !subr0; move=>*.
by apply: repCMl; rewrite // eq_sym. 
Qed.

Lemma posC_mull x y : 0 < x -> (0 <= y * x) = (0 <= y).
Proof. rewrite mulrC; exact: posC_mulr. Qed.

Lemma posC_mul x y : 0 <= x -> 0 <= y -> 0 <= x * y.
Proof.
move=> Hx Hy.
case: (boolP (x == 0)); first by move/eqP->; rewrite mul0r leC_refl.
by move=> Hdx; rewrite posC_mulr //; apply/andP.
Qed.

Lemma leC_anti x y : x <= y -> y <= x -> x = y.
Proof.
move=> Hx Hy; apply/eqP; rewrite -subr_eq0; apply/eqP.
by apply: repC_anti; rewrite // oppr_sub.
Qed.

Lemma posC1 : 0 <= 1.
Proof. by rewrite /leC subr0 repC1. Qed.

Lemma leq_leC a b : (a <= b)%N = (a%:R <= b%:R).
Proof.
elim: a b => [b | a IH [|b]]; first 2 last.
- by rewrite -{2}add1n natr_add -{2}[b.+1]add1n natr_add leC_add2l -IH.
- by rewrite posC_nat.
apply/esym; apply: contraFF (oner_eq0 algC) => le_a1_0.
rewrite (leC_anti posC1) // -(leC_add2l a%:R) -mulrSr addr0.
exact: leC_trans (posC_nat a).
Qed.

Lemma eqN_eqC (a b : nat) : (a == b) = (a%:R == b%:R :> algC).
Proof.
apply/idP/eqP=> [/eqP-> // |]; rewrite eqn_leq !leq_leC => ->.
by rewrite !leC_refl.
Qed.

Lemma neq0N_neqC (a : nat) : (a != 0%N) = (a%:R != 0 :> algC).
Proof. by rewrite eqN_eqC. Qed.

Lemma Cchar : [char algC] =i pred0.
Proof.
by move=> p; apply/andP=> [[/prime_gt0]]; rewrite lt0n neq0N_neqC => /negP.
Qed.

Lemma ltC_add2l p m n : (p + m < p + n) = (m < n).
Proof.
rewrite ltCE leC_add2l; congr (_ && _).
apply/negP/negP=> HH HH1; case: HH; first by rewrite (eqP HH1).
by apply/eqP; apply: (addrI _ (eqP HH1)).
Qed.

Lemma ltC_add2r p m n : (m + p < n + p) = (m < n).
Proof. by rewrite ![_ + p]addrC ltC_add2l. Qed.

Lemma leC_ltC_trans n m p : m <= n -> n < p -> m < p.
Proof.
move=> Hm; rewrite !ltCE; case/andP=> H1m H2m.
rewrite (leC_trans Hm) // andbT.
apply/eqP=> HH; case/eqP: H1m; apply: leC_anti=> //.
by rewrite HH.
Qed.

Lemma ltC_leC_trans n m p : m < n -> n <= p -> m < p.
Proof.
rewrite !ltCE; case/andP=> H1m H2m Hn.
rewrite (leC_trans H2m) // andbT.
apply/eqP=> HH; case/eqP: H1m; apply: leC_anti=> //.
by rewrite -HH.
Qed.

Lemma ltC_trans n m p : m < n -> n < p -> m < p.
Proof.
by rewrite !ltCE; case/andP=> H1m H2m Hp; apply: leC_ltC_trans Hp.
Qed.

Lemma leC_sub x y : (0 <= y - x) = (x <= y).
Proof. by rewrite /leC subr0. Qed.

Lemma ltC_sub x y : (x < y) = (0 < y - x).
Proof. by rewrite -(ltC_add2r (-x)) subrr. Qed.

Lemma ltn_ltC m n : (m < n)%N = (m%:R < n%:R).
Proof. by rewrite !ltCE -leq_leC -eqN_eqC ltn_neqAle eq_sym. Qed.

Lemma leC_mul2l m n1 n2 : 0 <= m -> n1 <= n2 -> m * n1 <= m * n2.
Proof.
move=> Hm Hn; rewrite {1}/leC -mulr_subr -[_ * _]subr0.
by apply: posC_mul=> //; rewrite -(leC_add2r n1) add0r subrK.
Qed.

Lemma leC_mul2r m n1 n2 : 0 <= m -> n1 <= n2 -> n1 * m <= n2 * m.
Proof. by move=> Hm Hn; rewrite ![_ * m]mulrC leC_mul2l. Qed.

Lemma leC_pmul2l m n1 n2 : 0 < m -> (m * n1 <= m * n2) = (n1 <= n2).
Proof.
move=> H; apply/idP/idP=> HH; last by apply: leC_mul2l; case/andP: H.
by rewrite -leC_sub -(posC_mulr _ H) mulr_subr leC_sub.
Qed.

Lemma leC_pmul2r m n1 n2 : 0 < m -> (n1 * m  <= n2 * m) = (n1 <= n2).
Proof. by move=> H; rewrite ![_* m]mulrC leC_pmul2l. Qed.

Lemma leC_square a b : 0 <= a -> a <= b -> a ^+ 2 <= b ^+ 2.
Proof.
move=> Ha Hb; rewrite -leC_sub subr_sqr posC_mul ?leC_sub ?posC_add //.
exact: leC_trans Ha Hb.
Qed.

Lemma posC_inv x : (0 <= x^-1) = (0 <= x).
Proof. rewrite /leC !subr0; exact: repC_inv. Qed.

Lemma sposC_inv x : (0 < x^-1) = (0 < x).
Proof.
rewrite !ltCE posC_inv; congr (_ && _).
apply/idP/idP=>[HH|]; last by exact: invr_neq0.
by apply/eqP=> HH1;case/eqP: HH; rewrite HH1 invr0.
Qed.

Lemma posC_conj x : (0 <= x^*) = (0 <= x).
Proof. rewrite /leC !subr0; exact: repC_conj. Qed.

Lemma posC_sum (I : eqType) (r : seq I) (P : pred I) (F : I -> algC) :
   (forall i, (i \in r) && P i -> 0 <= F i) -> 0 <= \sum_(j <- r | P j) F j.
Proof.
rewrite big_cond_seq => posF.
elim/big_rec: _ => [|i x Pi pos_x]; first exact: leC_refl.
by rewrite posC_add ?posF // andbC.
Qed.

Lemma posC_add_eq0 x y :
  0 <= x -> 0 <= y -> (x + y == 0) = (x == 0) && (y == 0).
Proof.
move=> Hx Hy; apply/eqP/andP=> [Hxy | [/eqP-> /eqP->]]; last exact: addr0.
suffices x0: x = 0 by rewrite x0 add0r in Hxy *; rewrite Hxy.
by rewrite (leC_anti Hx) // -(leC_add2r y) Hxy add0r.
Qed.

Lemma posC_sum_eq0 (I : eqType) (r : seq I) (P : pred I) (F : I -> algC) :
   (forall i, (i \in r) && P i -> 0 <= F i) ->
   \sum_(j <- r | P j) F j = 0 -> (forall i, (i \in r) && P i -> F i = 0).
Proof.
move=> posF sumF0 i /andP[r_i Pi]; apply: leC_anti; last by rewrite posF ?r_i.
have lt_i_r: (index i r < size r)%N by rewrite index_mem.
rewrite -{}sumF0 (big_nth i) big_mkord -leC_sub.
rewrite (bigD1 (Ordinal lt_i_r)) ?nth_index //= addrC addKr posC_sum //.
by move=> j /and3P[_ Pj _]; rewrite posF ?mem_nth.
Qed.

Lemma sposC_addl m n : 0 <= m -> 0 < n -> 0 < m + n.
Proof.
by move=> Hm Hn; apply: (leC_ltC_trans Hm); rewrite -{1}[m]addr0 ltC_add2l.
Qed.

Lemma sposC_addr m n : 0 < m -> 0 <= n -> 0 < m + n.
Proof.
by move=> Hm Hn; rewrite addrC; apply: sposC_addl.
Qed.

Lemma sposC_mul m n : 0 < m -> 0 < n -> 0 < m * n.
Proof.
case/andP=> H1m H2m; case/andP=> H1n H2n; apply/andP; split.
  by rewrite mulf_eq0 (negPf H1m).
by apply: posC_mul.
Qed.

Definition leCif m n c := ((m <= n) * ((m == n) = c))%type.

Notation "m <= n ?= 'iff' c" := (leCif m n c)
    (at level 70, n at next level,
  format "m '[hv'  <=  n '/'  ?=  'iff'  c ']'") : C_scope.

Coercion leC_of_leqif m n c (H : m <= n ?= iff c) := H.1 : m <= n.

Lemma leCifP m n c :
   reflect (m <= n ?= iff c) (if c then m == n else m < n).
Proof.
apply: (iffP idP); last first.
  case: c=> [] [H1 H2]; last by rewrite ltCE eq_sym H2.
  by apply/eqP; apply: leC_anti=> //; rewrite (eqP H2) leC_refl.
case c; [move/eqP-> |]; split; rewrite ?eqxx //; first exact: leC_refl.
  by apply: ltCW.
by move: H; rewrite ltCE eq_sym; case: eqP.
Qed.

Fact sqrtC_subproof x : exists y : algC, y ^+ 2 == x.
Proof.
have [//|y def_y2] := @solve_monicpoly algC 2 [fun i => 0 with 0%N |-> x].
by exists y; rewrite def_y2 !big_ord_recl big_ord0 /= mulr1 mul0r !addr0.
Qed.

Definition sqrtC := locked (fun x =>
  let y := xchoose (sqrtC_subproof x) in if 0 <= y then y else - y).

Lemma sqrtCK x : sqrtC x ^+ 2 = x.
Proof.
unlock sqrtC; rewrite (fun_if (fun y => y ^+ 2)) sqrrN if_same.
exact/eqP/(xchooseP (sqrtC_subproof x)).
Qed.

Lemma sqrtC_sqr c : (sqrtC (c ^+ 2) == c) || (sqrtC (c ^+ 2) == - c).
Proof. by rewrite -subr_eq0 -addr_eq0 -mulf_eq0 -subr_sqr sqrtCK subrr. Qed.

Lemma sqrtC_sqr_pos c : 0 <= c -> sqrtC (c ^+ 2) = c.
Proof.
move=> le0c; case/pred2P: (sqrtC_sqr c) => //; unlock sqrtC.
case: ifPn => le0rc def_c; move: le0rc; last by rewrite (oppr_inj def_c) le0c.
by rewrite def_c -sub0r leC_sub => /leC_anti->; rewrite ?subrr.
Qed.

Lemma sqrtC0 : sqrtC 0 = 0.
Proof. by rewrite -{1}(mulr0 0) sqrtC_sqr_pos ?leC_refl. Qed.

Lemma sqrtC_eq0 c : (sqrtC c == 0) = (c == 0).
Proof.
apply/eqP/eqP=> [|->]; last exact: sqrtC0.
by rewrite -{2}[c]sqrtCK => ->; rewrite exprS mul0r.
Qed.

Lemma sqrtC1 : sqrtC 1 = 1.
Proof. by rewrite -{2}(sqrtC_sqr_pos posC1) exp1rn. Qed. 

Definition normC x := sqrtC (x * x^*).

Fact conjCid_norm z : (normC z)^* = normC z.
Proof.
set y := normC z; have [// | def_y]: y^* = y \/ y^* = - y.
  apply/pred2P; rewrite -subr_eq0 -addr_eq0 -mulf_eq0 -subr_sqr.
  by rewrite -rmorphX sqrtCK rmorphM conjCK mulrC subrr.
suffices /eqP: y ^+ 2 = 0 by rewrite expf_eq0 => /=/eqP->; rewrite rmorph0.
apply: leC_anti; last by rewrite sqrtCK posC_pconj.
by rewrite -leC_sub sub0r -mulrN -def_y posC_pconj.
Qed.

Fact leC_real_total x : x^* = x -> x <= 0 \/ 0 <= x.
Proof.
move=> Rx; pose y := sqrtC x; apply/orP; rewrite -leC_sub sub0r.
suffices [<- | <-]: y * y^* = x \/ y * y^* = - x by rewrite posC_pconj ?orbT.
apply/pred2P; rewrite -subr_eq0 -addr_eq0 -mulf_eq0 -subr_sqr.
by rewrite exprn_mull -rmorphX sqrtCK Rx subrr.
Qed.

Lemma normC_nat n : normC n%:R = n%:R.
Proof. by rewrite /normC rmorph_nat sqrtC_sqr_pos ?posC_nat. Qed.

Lemma normC0 : normC 0 = 0.
Proof. exact: normC_nat 0%N. Qed.

Lemma normC1 : normC 1 = 1.
Proof. exact: normC_nat 1%N. Qed.

Lemma posC_norm x : 0 <= normC x.
Proof.
have [| //] := leC_real_total (conjCid_norm x); rewrite -leC_sub sub0r.
by unlock normC sqrtC; case: ifP; rewrite // opprK => ->.
Qed.

Lemma normC_eq0 c : (normC c == 0) = (c == 0).
Proof. by rewrite -[_ == 0](expf_eq0 _ 2) sqrtCK mulf_eq0 conjC_eq0 orbb. Qed.

Lemma normC_mul : {morph normC: x y / x * y}.
Proof.
move=> x y; rewrite {1}/normC rmorphM mulrCA -mulrA mulrCA mulrA.
rewrite -[x * _]sqrtCK -[y * _]sqrtCK -exprn_mull sqrtC_sqr_pos //.
by rewrite posC_mul //; exact: posC_norm.
Qed.

Lemma normC_exp x n : normC (x ^+ n) = normC x ^+ n.
Proof.
elim: n => [|n IH]; first exact: normC1.
by rewrite exprS normC_mul IH exprS.
Qed.

Lemma normC_conj x : normC x^* = normC x.
Proof. by rewrite /normC conjCK mulrC. Qed.

Lemma normC_inv x : normC x^-1 = (normC x)^-1.
Proof.
have [|nz_x] := boolP (normC x == 0).
  by rewrite normC_eq0 => /eqP->; rewrite !(normC0, invr0).
by apply: (mulIf nz_x); rewrite mulVf // -normC_mul mulVf ?normC1 // -normC_eq0.
Qed.

Lemma invC_norm x : x^-1 = (normC x)^-2 * x^*.
Proof.
have [-> | nx_x] := eqVneq x 0; first by rewrite conjC0 mulr0 invr0.
by rewrite sqrtCK invf_mul divfK ?conjC_eq0.
Qed.

Lemma conjC_inv x : (x^-1)^* = (x^*)^-1.
Proof. exact: fmorphV. Qed.

(* This is the first use of Archimedean axiom. *)
Lemma normC_pos x : 0 <= x -> normC x = x.
Proof.
move=> le0x; have [-> | nzx] := eqVneq x 0; first by rewrite normC0.
rewrite -{2}[x]mul1r; apply: canRL (divfK nzx) _; set y := normC x / x.
have le0y: 0 <= y by rewrite posC_mul ?posC_inv ?posC_norm.
have ley1_sym: (y <= 1) = (1 <= y).
  rewrite -leC_sub -posC_conj rmorph_sub rmorph1 leC_sub.
  have lt0y: 0 < y by rewrite ltCE mulf_eq0 invr_eq0 normC_eq0 orbb nzx.
  rewrite -(leC_pmul2l _ _ lt0y) mulr1 fmorph_div conjCid_norm mulrCA !mulrA.
  by rewrite -expr2 sqrtCK (mulrC x) mulfK // divff ?conjC_eq0.
suffices ley1: y <= 1 by rewrite (leC_anti ley1) -?ley1_sym.
rewrite /leC subr0 in le0y.
have [[/and3P[] //| n /andP[le_n1_y _]]] := realC_archimedean le0y.
by rewrite ley1_sym (leC_trans _ le_n1_y) -?(leq_leC 1).
Qed.

Lemma posC_conjK x : 0 <= x -> x^* = x.
Proof. by move/normC_pos <-; rewrite conjCid_norm. Qed.

Lemma sqrtC_pos x : (0 <= sqrtC x) = (0 <= x).
Proof.
apply/idP/idP=> [le0rx | le0x]; first by rewrite -[x]sqrtCK posC_mul.
have [-> | nzx] := eqVneq x 0; first by rewrite sqrtC0 leC_refl.
pose y := sqrtC x * (sqrtC x)^*; suffices ->: x = y by exact: posC_norm.
have: x ^+ 2 == y ^+ 2 by rewrite exprn_mull -rmorphX sqrtCK posC_conjK.
rewrite -subr_eq0 subr_sqr mulf_eq0 subr_eq0 => /predU1P[] // /idPn[].
suffices: 0 < x + y by case/andP.
by rewrite sposC_addr ?posC_pconj // ltCE nzx.
Qed.

Lemma posC_unit_exp x n : 0 <= x -> (x ^+ n.+1 == 1) = (x == 1).
Proof.
move=> le0x; apply/idP/eqP=> [|->]; last by rewrite exp1rn.
apply: contraTeq => neq_x_1.
suffices: x ^+ n.+1 < 1 \/ 1 < x ^+ n.+1.
  by move/orP; rewrite ltCE eq_sym -andb_orr => /andP[].
have{neq_x_1}: x < 1 \/ 1 < x.
  rewrite !ltCE eq_sym neq_x_1 -(leC_sub 1) -leC_sub -oppr_sub -sub0r leC_sub.
  by apply: leC_real_total; rewrite rmorph_sub rmorph1 posC_conjK.
case=> [ltx1 | lt1x]; [left | right]; elim: n => // n /ltCW IHn.
  by apply: leC_ltC_trans ltx1; rewrite -{2}[x]mulr1 leC_mul2l. 
by apply: ltC_leC_trans lt1x _; rewrite -{1}[x]mulr1 leC_mul2l. 
Qed.

Lemma normC_add x y : normC (x + y) <= normC x + normC y.
Proof.
have [-> | ntx] := eqVneq x 0; first by rewrite normC0 !add0r leC_refl.
have [-> | nty] := eqVneq y 0; first by rewrite normC0 !addr0 leC_refl.
have /leC_pmul2r ltMxy: 0 < normC x + normC y + normC (x + y).
  by rewrite !sposC_addr ?ltCE ?posC_norm //= normC_eq0 ntx.
rewrite -leC_sub -{}ltMxy mul0r -subr_sqr sqrr_add !sqrtCK leC_sub rmorphD.
rewrite mulr_addl !mulr_addr addrA leC_add2r -addrA leC_add2l -normC_mul.
set z := _ + _; set p := _ *+ 2.
have le0p: 0 <= p by rewrite posC_add ?posC_norm.
have Rz: z^* = z by rewrite !(rmorphD, rmorphM) !conjCK mulrC addrC (mulrC _ x).
case/leC_real_total: Rz => [/leC_trans-> // | le0z].
have /leC_pmul2r ltMxy: 0 < p + z.
  by rewrite !sposC_addr ?ltCE ?posC_norm // normC_eq0 mulf_neq0.
rewrite -leC_sub -{}ltMxy mul0r -subr_sqr leC_sub -[p]mulr_natr exprn_mull.
rewrite -natr_exp mulr_natr sqrtCK rmorphM mulrA mulrC -mulrA mulrCA mulrA.
rewrite -subr_sqr_add_sub addrC -leC_sub addrK -mulNr oppr_sub.
rewrite -[_ - _]conjCK rmorph_sub !rmorphM !conjCK mulrC (mulrC x) (mulrC y).
exact: posC_pconj.
Qed.

Lemma normC_add_eq x y : 
    normC (x + y) = normC(x) + normC(y) -> 
  exists2 k, normC k = 1 & ((x == normC x * k) && (y == normC y * k)).
Proof.
pose s z := z / normC z; have congr_sqr := congr1 (fun z => z ^+ 2).
have norm1 z: z != 0 -> normC (s z) = 1 /\ z == normC z * s z.
  rewrite -normC_eq0 => nzz; rewrite mulrC divfK // /normC fmorph_div //.
  rewrite conjCid_norm mulrCA -mulrA -invf_mul mulrCA mulrA -expr2 -expr_inv.
  by rewrite -[z * _]sqrtCK -exprn_mull divff // exp1rn sqrtC1.
move=> def_Nxy; have [-> | ntx] := eqVneq x 0.
  have [-> | nty] := eqVneq y 0.
    by exists 1; rewrite ?normC1 // !normC0 mul0r eqxx.
  by have [? ?] := norm1 y nty; exists (s y); rewrite // normC0 mul0r eqxx.
have [ns1 def_x] := norm1 x ntx; exists (s x); rewrite ?def_x //=.
move/congr_sqr: def_Nxy; rewrite sqrr_add !sqrtCK rmorphD mulr_addl !mulr_addr.
rewrite addrA => /addIr; rewrite -addrA -normC_mul -mulr_natr => /addrI def2xy.
have eq_xy: x * y^* = y * x^*.
  apply/eqP; rewrite -subr_eq0 -normC_eq0 sqrtC_eq0 rmorph_sub !rmorphM !conjCK.
  rewrite -(mulrC x) -(mulrC y) [_ * _]mulrC -[_ - _]oppr_sub mulNr -expr2.
  move/congr_sqr/esym/eqP: def2xy; rewrite exprn_mull sqrtCK -natr_exp.
  rewrite mulr_natr rmorphM mulrA [_ * _]mulrC -mulrA mulrCA mulrA.
  by rewrite -subr_sqr_add_sub addrC -[_ == _]subr_eq0 addrK.
have{eq_xy def2xy} def_xy: y * x^* = normC (x * y).
  apply: (@mulIf _ 2%:R); first by rewrite -(eqN_eqC 2 0).
  by rewrite mulr_natr mulrS -{1}eq_xy.
apply/eqP/(@mulfI _ (normC x ^+ 2)); first by rewrite expf_eq0 normC_eq0.
rewrite {1}sqrtCK mulrAC -mulrA def_xy normC_mul mulrC -!mulrA; congr (_ * _).
by rewrite mulrCA; congr (_ * _); rewrite mulrC divfK ?normC_eq0.
Qed.

Lemma normC_sum I (r : seq I) (P : pred I) (F : I -> algC) :
   normC (\sum_(i <- r | P i) F i) <= \sum_(i <- r | P i) normC(F i).
Proof.
elim/big_rec2: _ => [|i u x _ le_ux]; first by rewrite normC0 leC_refl.
by apply: (leC_trans (normC_add _ _)); rewrite leC_add2l.
Qed.

Lemma normC_sum_eq (I : eqType) (r : seq I) (P : pred I) (F : I -> algC) :
     normC (\sum_(j <- r | P j) F j) = (\sum_(j <- r | P j) normC(F j)) ->
   exists2 k, normC k = 1 &
              forall i, (i \in r) && P i -> F i = normC (F i) * k.
Proof.
elim: r=> [|j r IH]; first by rewrite !big_nil; exists 1=> //; exact: normC1.
rewrite !big_cons; case HP: (P _)=> HH; last first.
  case: IH=> // k Hk Hr; exists k=> // j1.
  rewrite inE => /andP[/predU1P[-> | r_j1] Pj1]; first by rewrite HP in Pj1.
  by rewrite -Hr ?r_j1.
have F1: normC (\sum_(j <- r | P j) F j) = \sum_(j <- r | P j) normC (F j).
  apply: leC_anti; first by apply: normC_sum.
  by rewrite -(leC_add2l (normC (F j))) -HH normC_add.
move: HH; rewrite -F1; case/normC_add_eq=> k1 H1k1; case/andP=> H2k1 H3k1.
exists k1=> // j1; rewrite in_cons; case/andP; case/orP.
  by move/eqP->; rewrite -(eqP H2k1).
move=> Hj1 Pj1; case: IH=> // k2 H1k2 H2k2.
move: H3k1.
have HH: \sum_(j <- r | P j) F j = (\sum_(j <- r | P j) normC (F j)) * k2.
  elim: {F1 Hj1}r H2k2=> [|j2 r IH1 Hr]; first by rewrite !big_nil mul0r.
  rewrite !big_cons IH1 //; last first.
    by move=> j3; case/andP=> H1j3 H2j3; rewrite -Hr // in_cons H1j3 orbT.
  by case E1: (P _)=> //; rewrite {1}Hr ?(in_cons,eqxx) // mulr_addl.
rewrite {1}HH F1; move/eqP=> HH1.
case: ((\sum_(j0 <- r | P j0) normC (F j0)) =P 0)=> HH2.
suff: normC (F j1) = 0.
    by move/eqP; rewrite normC_eq0; move/eqP->; rewrite normC0 mul0r.
  apply: (posC_sum_eq0 _ HH2); last by rewrite Hj1.
  move=> j2; case/andP=> H1j2 H2j2 //.
  by apply: posC_norm; rewrite Hj1.
suff->: k1 = k2 by apply: H2k2; rewrite Hj1.
by move/eqP: HH2; move/mulfI; apply.
Qed.

Lemma normC_sum_eq1 (I : eqType) (r : seq I) (P : pred I) (F : I -> algC) :
   normC (\sum_(j <- r | P j) F j) = (\sum_(j <- r | P j) normC(F j)) ->
   (forall i, (i \in r) && P i -> normC (F i) = 1) ->
   exists2 k, normC k = 1 &
              forall i, (i \in r) && P i -> F i = k.
Proof.
move=> NN N1; case: (normC_sum_eq NN)=> k Nk Hk.
by exists k=> // i Hi; move: (Hk _ Hi); rewrite N1 // mul1r.
Qed.

Lemma normC_sum_upper (I : eqType) (r : seq I) (P : pred I) 
                      (F : I -> algC) (G : I -> algC) :
   (forall i, (i \in r) && P i -> normC (F i) <= G i) ->
   \sum_(j <- r | P j) F j = \sum_(j <- r | P j) (G j) ->
   forall i, (i \in r) && P i -> F i = G i.
Proof.
move=> Hn Hs.
have F0: forall i, (i \in r) && P i -> 0 <= G i.
  by move=> i Pi; apply: leC_trans (Hn _ Pi); exact: posC_norm.
have F1: normC (\sum_(j <- r | P j) F j) = 
          \sum_(j <- r | P j) normC (F j).
  apply: leC_anti=> //; first by apply: normC_sum.
  rewrite Hs normC_pos; last by apply: posC_sum.
  rewrite /leC -sumr_sub -[\sum_(i <- _| _)_]subr0.
  apply: posC_sum=> i Hi.
  by rewrite -(leC_add2r (normC (F i))) add0r subrK // Hn.
case: (normC_sum_eq F1)=> k H1k H2.
have F2: \sum_(j <- r | P j) F j = (\sum_(j <- r | P j) normC (F j)) * k.
  elim: {F0 Hn Hs F1}r H2=> [|j2 r IH1 Hr]; first by rewrite !big_nil mul0r.
  rewrite !big_cons IH1 //; last first.
    by move=> j3; case/andP=> H1j3 H2j3; rewrite -Hr // in_cons H1j3 orbT.
  by case E1: (P _)=> //; rewrite {1}Hr ?(in_cons,eqxx) // mulr_addl.
case: ((\sum_(j <- r | P j) normC (F j)) =P 0)=> H1.
  have F3 := (posC_sum_eq0 (fun i Hi => (posC_norm (F i))) H1).
  move: Hs; rewrite F2 H1 mul0r. move/(@sym_equal _ _ _)=> F4.
  move=> i; case/andP=> H1i H2i.
  rewrite (posC_sum_eq0 _ F4) ?H1i //.
  by apply/eqP; rewrite -normC_eq0 F3 // H1i.
have F3: k = 1.
  rewrite -[k]normC_pos ?H1k //.
  have F4: 0 <= (\sum_(j <- r | P j) normC (F j))^-1.
    by rewrite posC_inv; apply: posC_sum=> i Hi; exact: posC_norm.
  have F5: 0 <= (\sum_(j <- r | P j) normC (F j)) * k.
    by rewrite -F2 Hs posC_sum.
  by move: (posC_mul F4 F5); rewrite mulKr // GRing.unitfE; apply/eqP.
move=> i; case/andP=> Hi Pi; apply/eqP; rewrite eq_sym -subr_eq0; apply/eqP.
have F4: \sum_(j <- r | P j) (G j - F j) = 0.
  by rewrite sumr_sub Hs subrr.
apply: (posC_sum_eq0 _ F4)=> [j Hj|]; last by rewrite Hi.
rewrite -(leC_add2r (F j)) add0r subrK H2 //.
by rewrite F3 mulr1 Hn.
Qed.

Definition getNatC x :=
  if insub x : {? c | repC c} is Some c then
    val (sigW (realC_archimedean (valP c)))
  else 0%N.

Lemma getNatC_def x (n := getNatC x) :
  if (0 <= x) then (n%:R <= x) && (x < (n + 1)%:R) else n == 0%N.
Proof.
rewrite {}/n /getNatC /ltC /leC subr0 addn1 eq_sym (andbC (~~ _)).
case: ifPn => [le0x | not_le0x]; last by rewrite insubN.
by rewrite insubT //=; case: (sigW _).
Qed.

Lemma getNatC_nat n : getNatC (n%:R) = n.
Proof.
have:= getNatC_def n%:R; rewrite /= posC_nat -leq_leC -ltn_ltC.
case/andP=> H1 H2; apply: anti_leq => //.
by rewrite H1 // -ltnS -[(getNatC _).+1]addn1.
Qed.

Definition isNatC c := c == (getNatC c)%:R.

Lemma isNatCP c : reflect (exists n, c = n%:R) (isNatC c).
Proof.
apply: (iffP idP)=> [H | [n H]]; first by exists (getNatC c); apply/eqP.
by rewrite H /isNatC getNatC_nat.
Qed.

Lemma isNatC_nat n : isNatC (n%:R).
Proof. by apply/isNatCP; exists n. Qed.

Lemma isNatC_add c1 c2 : isNatC c1 -> isNatC c2 -> isNatC (c1 + c2).
Proof.
by case/isNatCP=> n1 ->; case/isNatCP=> n2 ->; rewrite -natr_add isNatC_nat.
Qed.

Lemma isNatC_mul c1 c2 : isNatC c1 -> isNatC c2 -> isNatC (c1 * c2).
Proof.
by case/isNatCP=> n1 ->; case/isNatCP=> n2 ->; rewrite -natr_mul isNatC_nat.
Qed.

Lemma isNatC_sum (I : Type) (r : seq I) (P : pred I) (F : I -> algC) :
   (forall i, P i -> isNatC  (F i)) -> isNatC (\sum_(j <- r | P j) F j).
Proof.
by move=> H; apply big_ind=> //; [exact: (isNatC_nat 0) | exact: isNatC_add].
Qed.

Lemma isNatCMn x n : isNatC x -> isNatC (x*+n).
Proof.
elim: n => [|n IH Hx]; first by rewrite mulr0n (isNatC_nat 0).
by rewrite mulrSr isNatC_add // IH.
Qed.

Lemma posC_isNatC c : isNatC c -> 0 <= c.
Proof. by case/isNatCP=> n ->; exact: posC_nat. Qed.

Lemma isNatC_conj c : isNatC c -> c^* = c.
Proof. by case/isNatCP=> n ->; exact: conjC_nat. Qed.

Lemma isNatC_sum_eq1 (I : eqType) (r : seq I) (P : pred I) (F : I -> algC) :
   (forall i, P i -> isNatC (F i)) -> uniq r ->
   \sum_(j <- r | P j) F j = 1%:R ->
   (exists i, [/\ i \in r, P i, F i = 1 &
               forall j, j != i -> j \in r -> P j -> F j = 0]).
Proof.
move=> HN; elim: r=> [_|y r Hrec].
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
- by move=> _ _; move/eqP; rewrite eq_sym oner_eq0.
- case: m Hm.
    move=> Hs HF _; case: Hrec=> // => j [HInj HPj HFj HF0].
    exists j; split=> //; first by rewrite in_cons HInj orbT.
    by move=> k Hk /predU1P[-> // | ]; exact: HF0.
  move=> n _ _.
  rewrite -[1%:R]add0r add0n -addn1 natr_add => HH.
  by move/eqP: (addIr _ HH); rewrite -(eqN_eqC _ 0).
- case: n Hn=> [Hn Hs _|n Hn Hs].
    exists y; split=> //; first by rewrite in_cons eqxx.
    move=> j Hjy; rewrite in_cons; case/orP; first by rewrite (negPf Hjy).
    move=> Hj HPj; apply: (posC_sum_eq0 _ Hs)=> //.
    move=> i; case/andP=> HNI HPI; apply: posC_isNatC; first by exact: HN.
    by rewrite Hj.
  rewrite -[1%:R]add0r addn0 -addn1 natr_add => HH.
  by move/eqP: (addIr _ HH); rewrite -(eqN_eqC _ 0).
rewrite -[1%:R]add0r addnS -addn1 natr_add => HH.
by move/eqP: (addIr _ HH); rewrite -(eqN_eqC _ 0).
Qed.

(* We mimic Z by a sign and a natural number *)
Definition getZC (c : algC) :=
 if 0 <= c then (false,getNatC c) else (true, getNatC (-c)).

Definition isZC c := c == let (b,n) := getZC c in (-(1))^+b * n%:R.

Lemma isZCE c : isZC c = (isNatC c || isNatC (-c)).
Proof.
rewrite /isZC /getZC.
case: (boolP (0 <= c))=> H.
  case: (boolP (isNatC (-c)))=> H1; last by rewrite orbF expr0 mul1r.
  suff->: c = 0 by rewrite (getNatC_nat 0) mulr0 eqxx orbT.
  by apply: leC_anti=> //; rewrite -leC_sub sub0r posC_isNatC.
case: (boolP (isNatC c))=> H1; first by case/negP: H; apply: posC_isNatC.
by rewrite expr1 mulNr -{1}[c]opprK eqr_opp mul1r.
Qed.

Lemma isZC_nat n : isZC (n%:R).
Proof. by rewrite isZCE isNatC_nat. Qed.

Lemma isZC_opp c : isZC c -> isZC (- c).
Proof. by rewrite !isZCE orbC opprK. Qed.

Lemma isZC_add c1 c2 : isZC c1 -> isZC c2 -> isZC (c1 + c2).
Proof.
rewrite !isZCE oppr_add.
case/orP; case/isNatCP=> n Hn; case/orP; case/isNatCP=> m Hm; rewrite !Hn !Hm.
- by rewrite -natr_add isNatC_nat.
- rewrite -[c2]opprK Hm.
  case: (orP (leq_total n m))=> HH.
    by rewrite [1 *- _ + _]addrC -natr_sub // isNatC_nat orbT.
  by rewrite -natr_sub // isNatC_nat.
- rewrite -[c1]opprK Hn.
  case: (orP (leq_total n m))=> HH.
    by rewrite [1 *- _ + _]addrC -[m%:R - _]natr_sub // isNatC_nat.
  by rewrite -natr_sub // isNatC_nat orbT.
by rewrite -natr_add isNatC_nat orbT.
Qed.

Lemma isZC_sub c1 c2 : isZC c1 -> isZC c2 -> isZC (c1 - c2).
Proof. by move=> Hc1 HC2; apply: isZC_add=> //; exact: isZC_opp. Qed.

Lemma isZC_mul c1 c2 : isZC c1 -> isZC c2 -> isZC (c1 * c2).
Proof.
rewrite 2!isZCE.
case/orP; case/isNatCP=> n Hn; case/orP; case/isNatCP=> m Hm; rewrite ?Hn ?Hm.
- by rewrite -natr_mul isZC_nat.
- by rewrite -[c2]opprK Hm mulrN isZC_opp // -natr_mul isZC_nat.
- by rewrite -[c1]opprK Hn mulNr isZC_opp // -natr_mul isZC_nat.
by rewrite -mulrNN Hn Hm -natr_mul isZC_nat.
Qed.

Lemma isZC_sum (I : Type) (r : seq I) (P : pred I) (F : I -> algC) :
   (forall i, P i -> isZC  (F i)) -> isZC (\sum_(j <- r | P j) F j).
Proof.
by move=> H; apply big_ind=> //; [exact: (isZC_nat 0) | exact: isZC_add].
Qed.

Lemma isZC_conj c : isZC c -> c^* = c.
Proof.
rewrite isZCE; case/orP=> Hc; first exact: isNatC_conj.
by rewrite -{1}[c]opprK rmorphN isNatC_conj // opprK.
Qed.

Definition absC x := if 0 <= x then x else -x.

Lemma absC_nat n : absC n%:R = n%:R.
Proof. by rewrite /absC posC_nat. Qed.

Lemma absC_eq0 x : (absC x == 0) = (x == 0).
Proof.
rewrite /absC; case: (_ <= _)=> //.
apply/eqP/eqP=>[|->]; last by rewrite oppr0.
by rewrite -{2}[x]opprK=> ->; rewrite oppr0.
Qed.

Lemma isNatC_absC z : isZC z -> isNatC (absC z).
Proof.
rewrite isZCE /absC; case/orP; case/isNatCP=> n Hn.
  by rewrite Hn posC_nat isNatC_nat.
rewrite -{1 2}[z]opprK Hn.
case: (boolP (0 <= _))=> HH; last by exact: isNatC_nat.
rewrite -(leC_anti (posC_nat n)) ?(oppr0,(isNatC_nat 0)) //.
by rewrite -leC_sub sub0r.
Qed.

Lemma absC_square z : isZC z -> z * z = absC z * absC z.
Proof.
rewrite isZCE /absC; case/orP; case/isNatCP=> n Hn.
  rewrite Hn posC_nat // isNatC_nat.
by case: (_ <= _)=> //; rewrite mulrNN.
Qed.
