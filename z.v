Require Import ssreflect ssrfun ssrbool eqtype ssrnat div choice.
Require Import bigops ssralg.

Require Import quotient.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Relatifs.

Definition pickz (x:nat*nat) := Some (x.1-x.2 , x.2-x.1).

Lemma pickz_axiom : forall x, obind pickz (pickz x) = pickz x.
Proof. 
move=> x; rewrite /pickz /=; move/orP:(leq_total x.1 x.2)=>[];
by rewrite -subn_eq0; move/eqP=> ->; rewrite subn0 sub0n //=.
Qed.

Definition reprChoicez := Eval hnf in (ReprChoice pickz_axiom).
Definition z := quotient reprChoicez.
Notation canonz := (canon reprChoicez).
Notation domz := (dom reprChoicez).
Notation rewz := (rew reprChoicez).


Canonical Structure z_eqType := Eval hnf in [eqType of z].
Canonical Structure z_subType := Eval hnf in [subType of z].
Canonical Structure z_choiceType := Eval hnf in
  [choiceType of z for (quotient_choiceType reprChoicez)].




Reserved Notation "x === y" (at level 70, no associativity).
Local Notation "x === y" := (@equiv _ reprChoicez x y).

Reserved Notation "\dom x" (at level 2, format "\dom  x").
Local Notation "\dom x" :=  (x === x).

Definition equivz x y := x.1 + y.2 == y.1 + x.2.

Lemma all_dom_lemma : forall x:nat*nat, \dom x.
Proof. by move=>x; rewrite dom_coincide. Qed.
Canonical Structure all_dom x := Dom (@all_dom_lemma x).


Lemma pairK : forall (A B:eqType) (a a':A) (b b':B), 
  ((a,b) == (a',b')) = ((a==a') && (b==b')).
Proof.
move=> A B a a' b b'. apply/eqP/idP=> [[] -> -> | ]; first by rewrite !eqxx /=.
by move/andP=> []; move/eqP=> ->; move/eqP=> ->.
Qed.


Lemma eq_sub_addu : forall m n p u, n <= m -> (u + (m - n) == p) = (u + m == n + p).
Proof. by move=> ? n *; rewrite -(inj_eq (@addnI n)) addnC -addnA subnK. Qed.

Lemma eq_sub_add : forall m n p, n <= m -> (m - n == p) = (m == n + p).
Proof. by move=> m n *; rewrite -(add0n (m-n)) eq_sub_addu // add0n. Qed.


(* equivs is coincides with === on domz *)
Lemma equivz_canon : forall x:domz, equivz (canonz x) (dom_elt x).
Proof.
move=> x; rewrite /equivz /canonz /=. move:x=>[x _] /=.
move/orP:(leq_total x.1 x.2)=>[] lx; move:(lx); rewrite -subn_eq0;move/eqP=>->;
by rewrite ?addn0 ?add0n ?subnKC ?subnK.
Qed.

Lemma equivz_canonN : forall x y:domz, 
  (equivz (canonz x) (canonz y)) -> (x === y).
Proof.
move=> x y; rewrite /equivz equiv_elim /canonz; move:x y=> [x _] [y _] /=.
move/orP:(leq_total x.1 x.2)=>[] lx; move:(lx);rewrite -subn_eq0;move/eqP=> ->;
move/orP:(leq_total y.1 y.2)=>[] ly; move:(ly);rewrite -subn_eq0;move/eqP=> ->;
rewrite ?add0n ?addn0 ?[0 == _]eq_sym ?addn_eq0 ?pairK ?[0 == _]eq_sym //;
by rewrite ?eqxx // ?andTb ?andbT eq_sym. 
Qed.

Lemma equivz_sym : symmetric equivz.
Proof. by move=> x y; rewrite /equivz eq_sym. Qed.

Lemma equivz_trans : transitive equivz.
Proof. 
rewrite /equivz=> x y t; move/eqP=>exy; move/eqP=>eyt. 
by rewrite -(inj_eq (@addIn x.2)) addnAC exy addnAC eyt addnAC eqxx.
Qed.

Definition equivz_left_trans := left_trans equivz_sym equivz_trans.

Definition equivzS := equiv_coincide equivz_sym equivz_trans 
  equivz_canon equivz_canonN.
(* equivz subsitutes === with equivz, which allows us to compute *)

Definition preaddz x y := (x.1+y.1, x.2+y.2).

Lemma preaddz_dom_lemma : forall x y : domz,
\dom (preaddz (dom_elt x) (dom_elt y)).
Proof. by move=> x y; rewrite /equiv eqxx /reprChoicez /=. Qed.
Canonical Structure preaddz_dom x y := Dom (preaddz_dom_lemma x y).

Definition addz (x y : z) : z :=
  @Quotient _ _ (canonz (preaddz (repr x) (repr y))) (canon_axiomq _).

Lemma preaddz_compat : compat2 reprChoicez preaddz.
Proof.
move=> x y xz yz. rewrite  !equivzS /= /equivz /preaddz /=.
move/eqP=> e1; move/eqP=> e2. rewrite ![_.1 + _.1 + _]addnAC.
by rewrite -addnA addnAC !addnA e1 -!addnA e2 [_.2 + _.1]addnC.
Qed.
Canonical Structure preaddz_rew_elt x y :=  
  Rew (compat_mod_op2 preaddz_compat x y).

Lemma canon0r : forall x, canonz (x,0) = (x,0).
Proof. by move=> x; rewrite /canonz /= subn0 sub0n. Qed.

Lemma canon0l : forall x, canonz (0,x) = (0,x).
Proof. by move=> x; rewrite /canonz /= subn0 sub0n. Qed.

Definition zeroz : z := @Quotient _ reprChoicez (0,0) is_true_true.
Definition onez : z := @Quotient _ reprChoicez (1,0) is_true_true.

Lemma natz_z : forall n : nat, (canonz (n, 0) == (n, 0)) && \dom (n, 0).
Proof. by move=>n; rewrite dom_coincide andbT /canonz /= sub0n subn0 eqxx. Qed.
Definition natz (n:nat) : z := @Quotient _ reprChoicez (n,0) (natz_z n).

Coercion natz : nat >-> z.

Lemma zpos_or_neg : forall x:z, ((repr x).1 == 0) || ((repr x).2 == 0).
Proof. 
move=> [[xp xn]] /=. case/andP. rewrite /canon /=. case/eqP=>Rxp Rxn _.
by rewrite -Rxp subn_eq0; case:leqP=>//= ltpn; rewrite -Rxn subn_eq0 ltnW.
Qed.

Definition premulz x y := (x.1*y.1+x.2*y.2, x.1*y.2+x.2*y.1).

Lemma premulz_dom_lemma : forall x y : domz,
\dom (premulz (dom_elt x) (dom_elt y)).
Proof. by move=> x y; rewrite /equiv eqxx /reprChoicez /=. Qed.
Canonical Structure premulz_dom x y := Dom (premulz_dom_lemma x y).

Definition mulz (x y : z) : z :=
  @Quotient _ _ (canonz (premulz (repr x) (repr y))) (canon_axiomq _).

Lemma premulz_compat : compat2 reprChoicez premulz.
Proof.
move=> x y xz yz. rewrite !equivzS /equivz /=.
case/orP:(zpos_or_neg xz); move/eqP->; rewrite ?mul0n ?muln0 ?addn0 ?add0n; 
case/orP:(zpos_or_neg yz); move/eqP->; rewrite ?mul0n ?muln0 ?addn0 ?add0n;
rewrite 2?[_ + _ == _]eq_sym; move/eqP->; move/eqP->;
rewrite !muln_addr !muln_addl; apply/eqP; 
by rewrite -!addnA; do !nat_congr.
Qed.

Canonical Structure premulz_rew x y := Rew (compat_mod_op2 premulz_compat x y).   


Lemma addzA : associative addz.
Proof.
move=> x y t. apply/equivP=>/=. apply: quot_inj=>/=.
by congr (_,_); rewrite addnA. 
Qed.

Lemma addzC : commutative addz.
Proof. 
move=> x y. apply/equivP=>/=. apply:quot_inj=>/=. 
by congr(_,_); rewrite addnC.
Qed.


Lemma add0z: left_id zeroz addz.
Proof.
move=>x. apply/equivP=>/=. apply: quot_inj=>/=.
by case:x=>[[]] /= *; rewrite /preaddz /= !add0n.
Qed.


Definition preoppz x : nat*nat := (x.2,x.1).

Lemma preoppz_dom_lemma : forall x : domz, \dom (preoppz (dom_elt x)).
Proof. move=> x. exact: all_dom_lemma. Qed.
Canonical Structure preoppz_dom x y := Dom (preaddz_dom_lemma x y).

Definition oppz (x : z) : z := 
  @Quotient _ _ (canonz (preoppz (repr x))) (canon_axiomq _).

Lemma preoppz_compat : compat1 reprChoicez preoppz.
Proof. 
move=> x xq. rewrite !equivzS /equivz /=.
by rewrite eq_sym addnC; move/eqP->; rewrite addnC.
Qed.
Canonical Structure preoppz_rew x  := Rew (compat_mod_op1 preoppz_compat x).


Lemma addzN : left_inverse zeroz oppz addz.
Proof.
move=> x. apply/equivP=>/=. rewrite rew_equiv /=.
by rewrite equivzS /equivz add0n addn0 /= addnC.
Qed.



Definition z_zmodMixin :=  ZmodMixin addzA addzC add0z addzN.
Canonical Structure z_zmodType := Eval hnf in ZmodType z_zmodMixin.


Lemma mulzA : associative mulz.
Proof.
move=> x y t. apply/equivP=>/=. apply: quot_inj=>/=. 
by congr (_,_); rewrite /= !muln_addr !muln_addl !mulnA -!addnA; 
  congr(_+_);  symmetry; rewrite addnC -addnA.
Qed.

Lemma mulzC : commutative mulz.
Proof. 
move=> x y. apply/equivP=>/=. apply:quot_inj=>/=. 
by congr(_,_); rewrite 2![(_ (repr y))*_]mulnC addnC.
Qed.



Lemma mul1z : left_id onez mulz.
Proof.
move=> x. apply/equivP=>/=. apply: quot_inj=>/=.
by rewrite /premulz /= !mul1n !mul0n !addn0; move:x=>[[]/=].
Qed.

Lemma mulz_addl : left_distributive mulz addz.
Proof.
move=> x y t. apply/equivP=>/=. rewrite rew_equiv /=.
rewrite equivzS /equivz /= !muln_addl; apply/eqP.
by rewrite -!addnA; do !nat_congr.
Qed.

Lemma nonzero1z : onez != 0%R.
Proof. by rewrite -quotientP. Qed.

Definition z_comRingMixin := ComRingMixin mulzA mulzC mul1z mulz_addl nonzero1z.
Canonical Structure  z_Ring := Eval hnf in RingType z_comRingMixin.
Canonical Structure z_comRing := Eval hnf in ComRingType mulzC.


Definition unitz := [pred x :z | ((repr x).1)+((repr x).2)==1 ].
Definition invz (x : z) : z := x.


Lemma mulVz : {in unitz, left_inverse 1%R invz *%R}.
Proof.
move=> x. rewrite /invz /mem /in_mem /=. move/eqP=>Ux; apply/equivP=>/=;
 rewrite rew_equiv /= equivzS /equivz /= addn0 add1n. move:Ux. 
case/orP:(zpos_or_neg x); 
   by move/eqP->; rewrite ?add0n ?addn0; move->; rewrite !mul1n eqxx.
Qed.

Lemma unitzPl : forall x y, (y * x = 1)%R -> unitz x.
Proof.
move=> x y. move/equivP=>/=. rewrite rew_equiv /= equivzS /equivz /=.
rewrite addn0 add1n. move/eqP. 
by case/orP:(zpos_or_neg x); case/orP:(zpos_or_neg y); move/eqP->; move/eqP->;
rewrite !mul0n !muln0 !add0n ?addn0; move/eqP; rewrite ?eqn_mul1; do ?case/andP.
Qed.

Lemma  invz_out : {in predC unitz, invz =1 id}.
Proof. exact. Qed.

Definition z_comUnitRingMixin :=  ComUnitRingMixin mulVz unitzPl invz_out.
Canonical Structure z_comUnitRing := Eval hnf in ComUnitRingType z_comUnitRingMixin.

Lemma idomain_axiomz : forall x y : z, (x * y = 0 -> (x == 0) || (y == 0))%R.
Proof.
move=> x y. move/equivP=>/=. rewrite rew_equiv /= equivzS /equivz /=.
rewrite addn0 add0n. move/eqP=> Hxy. rewrite -!quotientP /= rew_equiv /=.
rewrite !equivzS /equivz /= !add0n !addn0. move:Hxy.
by case/orP:(zpos_or_neg x); case/orP:(zpos_or_neg y); move/eqP->; move/eqP->;
  rewrite !mul0n !muln0 !add0n ?addn0; move/eqP; rewrite ?[0==_]eq_sym;
    rewrite muln_eq0.
Qed.

Canonical Structure z_iDomain := Eval hnf in IdomainType idomain_axiomz. 



End Relatifs.


Import GRing.Theory.


Section ZTheory.
Open Scope ring_scope.

Definition absz (x : z) := ((repr x).1+(repr x).2)%N.

Lemma abs_eq0 : forall x : z, (x == 0) = (absz x == 0%N).
Proof.
move=> x. rewrite -quotientP equivzS /equivz /= addn0 add0n.
case/orP:(zpos_or_neg x); rewrite /absz; move:x=>[[??]/=_]; move/eqP->;
  by rewrite ?add0n ?addn0 //.
Qed.

Definition signz (x : z) : z := 
  if ((repr x).2 == 0%N) then  
    if ((repr x).1 == 0%N) then 0 else 1 
    else -1.

Lemma signzP : forall (x:z), [||(signz x == 1), (signz x == 0) | (signz x == -1)] .
Proof.
move=> x. rewrite /signz. 
by case:((repr x).2 == 0)%N; case:((repr x).1 == 0)%N; rewrite eqxx /=.
Qed.


Lemma negz_sign : forall x:z, signz (-x) = -(signz x).
Proof.
move=>x. rewrite /signz. apply: val_inj=>/=.
case/orP:(zpos_or_neg x); move/eqP=>->/=; rewrite subn0.
   by case:((repr x).2==0%N); rewrite /preoppz /canon /= sub0n ?subn0.
by case:((repr x).1==0%N); rewrite /preoppz /canon /= sub0n ?subn0.
Qed.

(* Lemma z_signz_absz : forall x:z, (signz x)*((absz x):z) = x. *)
(* Proof. *)


(* move=> x. apply/equivP=>/=.  *)
(* rewrite !muln0 add0n addn0. *)
(* case/orP:(zpos_or_neg x); rewrite /signz /absz. *)
(*    move:x=>[[a b]/=_/=]. move/eqP=>->/=. rewrite !add0n. *)
(*    case eb0:(b==0%N). move/eqP:eb0=>-> /=.   *)
(*       by rewrite muln0 add0n eqxx. *)
(*    by rewrite /= sub0n subn0 mul0n add0n mul1n eqxx. *)
(* move:x=>[[a b]/=_/=]. move/eqP=>->/=. rewrite !addn0. *)
(*    case ea0:(a==0%N). move/eqP:ea0=>-> /=.   *)
(*       by rewrite muln0 add0n eqxx. *)
(*    by rewrite /=  mul0n. *)
(* Qed. *)
   
Lemma signz_sign : forall x y :z , signz ((signz x) * y) = (signz x)*(signz y).
Proof.
move=> x y. case/or3P:(signzP x); move/eqP->; rewrite ?mul1r ?mul0r //.
by rewrite !mulNr !mul1r negz_sign.
Qed.
 

Lemma z_signz_absz : forall x:z, (signz x)*((absz x):z) = x.
Proof.
move=> x. rewrite /signz /absz /natz /=. apply: val_inj=>/=.
rewrite /premulz /=. case:(zpos_or_neg x). move:x=>[[xn xp]/=_].
case xp0:(xp == 0%N);  case xn0:(xn == 0%N)=> /=; 
  do ?move/eqP:xp0->; do ?move/eqP:xn0->;
    by rewrite !mul0n !add0n ?addn0 ?mul1n ?canon0l ?canon0r.
Qed.


Lemma signz_nat : forall x : nat, x != 0%N -> signz (natz x) = 1.
Proof. by move=> x px; rewrite /signz /=; move/negPf:px->. Qed.


Lemma mulz_sign : forall x y : z, signz (x * y) = (signz x) * (signz y).
Proof.
move=> x y. rewrite -(z_signz_absz x)  -(z_signz_absz y) -!mulrA.
rewrite !signz_sign mulrCA signz_sign mulrAC -!mulrA; congr(_*(_*_)).
rewrite /natz /signz/= muln0 mul0n add0n sub0n eqxx mul0n addn0 subn0 muln_eq0.
case:ifP; last by case/orb_false_elim=>->->; rewrite mul1r.
  by case/orP; move/eqP->; rewrite eqxx ?mulr0 ?mul0r.
Qed.


Lemma signz_id : forall x : z, signz (signz x) = signz x.
Proof. by move=> x; case/or3P:(signzP x); move/eqP->. Qed.

Lemma signz_eq0 : forall x: z, signz x == 0 = (x == 0).
Proof. 
move=>x. apply/eqP/eqP=>[Sx|]; last by move->.
apply:val_inj=>/=. move:Sx. rewrite /signz. move:x=>[[xn xp] _ /=] Sx.
by apply/eqP; rewrite pairK; case:(xp == 0%N) Sx; case:(xn == 0%N).
Qed.

(* (* Alternative haut-niveau *) *)
(* Proof. *)
(* move=>x. rewrite -(z_signz_absz x) signz_sign !mulf_eq0. congr(_||_). *)
(* case x0:(x==0); first by move/eqP:x0->.  *)
(* by rewrite -!(inj_eq val_inj) /= pairK eqxx andbT signz_nat -abs_eq0 x0. *)
(* Qed. *)
  
Lemma gt_neq0 : forall x:z, signz x == 1 -> x != 0.
Proof. by move=> x; rewrite -signz_eq0; move/eqP->. Qed.

Lemma lt_neq0 : forall x:z, signz x == -1 -> x != 0.
Proof. by move=> x; rewrite -signz_eq0; move/eqP->. Qed.

Lemma eqz_abs_sign : forall x y : z, 
  (absz x == absz y) && (signz x == signz y) = (x == y).
Proof.
move=> x y. apply/andP/eqP=>[[ea es]|]; last by move->.
by rewrite -(z_signz_absz x) (eqP ea) (eqP es) z_signz_absz.
Qed.

Lemma mulz_muln : forall x y : nat,  (x:z) * (y:z) = (((x * y)%N):z).
Proof. 
move=> x y. apply: val_inj=>/=. rewrite /premulz /= !muln0 !mul0n /=.
by rewrite !addn0 canon0r.
Qed.

Lemma mulz_abs : forall x y : z, absz (x*y) = ((absz x) * (absz y))%N.
Proof.
move=> x y. rewrite /absz /premulz /canon /= muln_addr !muln_addl. 
case/orP:(zpos_or_neg x); move/eqP->; rewrite ?mul0n ?muln0 ?add0n ?addn0;
  case/orP:(zpos_or_neg y); move/eqP->; rewrite ?mul0n ?muln0 ?add0n ?addn0;
    by rewrite subn0.
Qed.

Lemma absz_sign : forall x : z, x!=0 -> absz (signz x) = 1%N.
Proof. 
move=> x px. case/or3P:(signzP x)=>sx; rewrite (eqP sx) //.
by move:sx px; rewrite signz_eq0=> ->.
Qed.

Lemma absz_nat : forall x : nat, absz x = x.
Proof. by move=>x; rewrite /absz /natz /= addn0. Qed.

Definition divz (x y : z) := (divn (absz x) (absz y):z)*(signz x)*(signz y).

Definition test (x:z) :=  (signz x)*(signz x).

End ZTheory.

