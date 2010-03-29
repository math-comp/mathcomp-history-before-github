Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigops ssralg poly polydiv orderedalg.

Reserved Notation "a ^`"(at level 3, format "a ^`").
(* Reserved Notation "a ^`( n )" (at level 3, format "a ^`( n )"). *)
(* Reserved Notation "a ^`N( n )" (at level 3, format "a ^`N( n )"). *)

Import GRing.Theory.
Import OrderedRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.


Section ExtraRelative.

Variable R : oFieldType.

Implicit Types a b c : R.
Implicit Types x y z t : R.

Import GRing.Theory.
Import OrderedRing.Theory.

End ExtraRelative.

Section PolyOrder.

Variable F : oFieldType.

Implicit Types a b c : F.
Implicit Types x y z t : F.
Implicit Types p q r : {poly F}.

Notation "a ^`( n )" := (derivn a n).
Notation "a ^`" := (deriv a).

End PolyOrder.

Section PolyReal.

Variable R : oFieldType.

Implicit Types a b c : R.
Implicit Types x y z t : R.
Implicit Types p q r : {poly R}.

Hypothesis ivt : OrderedRing.poly_ivt R.

Lemma polyrealN0_sign : forall p a b, 
  (forall x, a <= x <= b -> ~~ root p x) -> 
  exists s, (forall x, a <= x <= b -> \s (p.[x]) = s).
Proof.
rewrite /root=> p a b np0; exists (\s p.[a]); move=> x laxb; move:(np0 _ laxb).
case: (ltrgtP p.[x] 0)=> [spx npx0|spx npx0|]; last by move->; rewrite eqxx.
  case: (ltrP p.[a] 0)=> spa; first by rewrite !signrN.
  case/andP:laxb=>lax lxb; case:(@ivt (-p) a x)=> //.
    by rewrite !horner_opp !signNr spa ltrE.
  move=> y; case/andP=> lay lyx; rewrite /root horner_opp oppr_eq0.
  by rewrite (negPf (np0 _ _))// lay/= (ler_trans lyx).
case: (lerP p.[a] 0)=> spa; last by rewrite !signrP.
case/andP:laxb=>lax lxb; case:(@ivt p a x)=> //; first by rewrite spa ltrE.
move=> y; case/andP=> lay lyx; rewrite /root.
by rewrite (negPf (np0 _ _))// lay/= (ler_trans lyx).
Qed.



Lemma divpf_spec : forall p q,  
  p = (((scalp p q)^-1)%:P * (p %/ q)) * q + ((scalp p q)^-1)%:P * (p %% q).
Proof.
move=> p q; apply/eqP.
rewrite -(inj_eq (@mulfI _ (scalp p q)%:P  _)); last first.
  by rewrite polyC_eq0 scalp_id.
rewrite mulr_addr !mulrA -!polyC_mul divff ?scalp_id// polyC1 !mul1r.
by rewrite divp_spec.
Qed. 

Lemma maxdivp : forall p a, p != 0 -> 
  exists q : {poly R}, 
    exists2 n,  (q.[a] != 0) & (p = q * ('X - a%:P)^+n).
Proof.
move=> p; move: {-2}p (erefl (size p)); elim: (size p)=> {p} [p sp|n ihn p sp].
  by move=> a; move/eqP: sp; rewrite size_poly_eq0; move/eqP->; rewrite eqxx.
move=> a p0.
case pa0: (root p a); first last.
  by exists p; exists 0%N; rewrite /root in pa0; rewrite ?pa0// expr0 mulr1.
move: pa0; rewrite root_factor_theorem.
move/dvdpPc=> [c] [q] [c0]; move/eqP.
rewrite -(inj_eq (@mulfI _ c^-1%:P  _)); last by rewrite polyC_eq0 invr_eq0.
rewrite mulrA -polyC_mul [_^-1*_]mulrC divff// polyC1 mul1r mulrA=> hp.
case q0 : (q == 0); first by move: hp p0; rewrite (eqP q0) mulr0 mul0r=> ->.
have sx : size ('X - a%:P) = 2%N.
  by rewrite size_addl size_polyX// size_opp size_polyC; case: (_ != _).
move:sp; rewrite (eqP hp) size_mul_id; last 2 first.
- by rewrite mulf_neq0// ?polyC_eq0 ?invr_eq0 ?c0// q0.
- by rewrite -size_poly_eq0 sx.
rewrite sx size_mul_id ?polyC_eq0 ?invr_eq0 ?c0// ?q0//.
rewrite size_polyC invr_eq0 c0 add1n addnS addn1 //=. 
move/eqP; rewrite eqSS; move/eqP; move/ihn=> ihnq.
case: (ihnq a)=> [|r [m ra0 Pq]]; first by rewrite q0.
exists ((c^-1)%:P * r); exists m.+1.
  by rewrite horner_lin mulf_neq0 // invr_eq0.
by rewrite Pq -!mulrA -exprSr.
Qed.


Lemma divfp_eq0 : forall p q, q != 0 -> (p %/ q == 0) = (size p < size q)%N.
Proof.
move=> p q q0; apply/idP/idP=> hpq; last by rewrite divp_size.
case p0: (p == 0); first by rewrite (eqP p0) size_poly0 lt0n size_poly_eq0.
case: (divp_spec p q); rewrite (eqP hpq) mul0r add0r=> hpmpq.
apply: leq_ltn_trans (modp_spec p _); rewrite // -hpmpq size_mul_id ?p0//.
   by rewrite size_polyC scalp_id //=.
by rewrite polyC_eq0 scalp_id.
Qed.

Require Import polydiv.

Lemma poly_divXMa : forall (a:R) (P : {poly R} -> Prop),
  (forall k, P k%:P) -> 
  (forall p n k, p.[a] != 0 -> P p ->
    P (p * ('X - a%:P)^+(n.+1) + k%:P)%R)
  -> forall p, P p.
Proof.
move=> a P Pk Pq p.
move: {-2}p (leqnn (size p)); elim: (size p)=> {p} [|n ihn] p spn.
  move: spn; rewrite leqn0 size_poly_eq0; move/eqP->; rewrite -polyC0.
  exact: Pk.
case: (leqP (size p) 1)=> sp1; first by rewrite [p]size1_polyC ?sp1//.
case: (@divpf_spec p ('X - a%:P))=> ->.
set q := (_%:P * _); set c := (_%:P * _).
have sx : size ('X - a%:P) = 2%N.
  by rewrite size_addl size_polyX// size_opp size_polyC; case: (_ != _).
rewrite [c]size1_polyC; first last.
  rewrite (leq_trans (size_mul _ _))// size_polyC invr_eq0 scalp_id.
  rewrite addnC addn1 /= -ltnS (leq_trans (modp_spec _ _)) // ?sx//.
  by rewrite -size_poly_eq0 sx.
case: (@maxdivp q a (mulf_neq0 _ _)).
- by rewrite polyC_eq0 invr_eq0 scalp_id.
- by rewrite divfp_eq0 -?size_poly_eq0 sx// -leqNgt sp1.
move=> r [m ra0 hqr]; rewrite hqr -mulrA -exprSr.
apply: Pq=> //; apply: ihn.
rewrite (leq_trans (_ : size r <= size q)%N)//.
  have xam : ('X - a%:P) ^+ m != 0.  
    elim:m {hqr}=>[|m ihm]; rewrite ?expr0 ?oner_eq0//.
    by rewrite exprS mulf_neq0// -size_poly_eq0 sx.
  rewrite hqr size_mul_id //; last first.
    by move: ra0; apply: contra; move/eqP->; rewrite horner0.
  rewrite -[size (('X-_)^+_)]prednK; last by rewrite lt0n size_poly_eq0.
  by rewrite addnC leq_addl.
rewrite (leq_trans (size_mul _ _))// size_polyC invr_eq0 scalp_id //=.
by rewrite size_divp -?size_poly_eq0 sx//= subn1 -ltnS (ltn_predK sp1).
Qed.

Lemma ler_mulNN : forall x y, 0 >= x -> 0 >= y -> 0 <= (x * y).
Proof. by move=> x y hx hy; rewrite -mulrNN le0r_mul ?signNr. Qed.
Lemma ler_mulPN : forall x y, 0 <= x -> 0 >= y -> 0 >= (x * y).
Proof. by move=> x y hx hy; rewrite -signNr -mulrN le0r_mul ?signNr. Qed.
Lemma ler_mulNP : forall x y, 0 >= x -> 0 <= y -> 0 >= (x * y).
Proof. by move=> x y hx hy; rewrite mulrC ler_mulPN. Qed.

Lemma ltr_mulPP : forall x y, x>0 -> y>0 -> (x*y)>0.
Proof. by move=> x y hx; rewrite mulrC -[0](mul0r x) ltf_mulP// mul0r. Qed.
Lemma ltr_mulNN : forall x y, x<0 -> y<0 -> (x*y)>0.
Proof. by move=> x y hx hy; rewrite -mulrNN ltr_mulPP ?signNr. Qed.
Lemma ltr_mulPN : forall x y, x>0 -> y<0 -> (x*y)<0.
Proof. by move=> x y hx hy; rewrite -signNr -mulrN ltr_mulPP ?signNr. Qed.
Lemma ltr_mulNP : forall x y, x<0 -> y>0 -> (x*y)<0.
Proof. by move=> x y hx hy; rewrite mulrC ltr_mulPN. Qed.

Lemma absf_mul : forall x y, |x * y| = |x| * |y|.
Proof.
move=> x y; case: (lerP x 0)=> hx; case: (lerP y 0)=> hy.
- by rewrite absrP ?ler_mulNN// absrN// absrN// mulrNN.
- by rewrite absrN ?ler_mulNP// 1?ltrE// -mulNr absrN// absrNN.
- by rewrite absrN ?ler_mulPN// 1?ltrE// -mulrN absrNN// absrN.
- by rewrite absrNN ?ltr_mulPP// absrNN// absrNN.
Qed.

Lemma ltf1_exp : forall x n, 0 < x -> x < 1 -> x^+n.+2 < x.
Proof.
move=> x n l0x lx1; elim: n=> [|n ihn].
  by rewrite exprS expr1 -{1}[x]mul1r ltf_mulP.
by rewrite exprSr -{1}[x]mul1r ltf_mulP// (ltr_trans _ lx1).
Qed.

Lemma lt1f_exp : forall x n, 1 < x -> x < x^+n.+2.
Proof.
move=> x n l1x; elim: n=> [|n ihn].
  rewrite exprS expr1 -{3}[x]mul1r ltf_mulP// (ler_lt_trans (ler01 _))//.
rewrite exprSr -{3}[x]mul1r ltf_mulP// ?(ltr_trans _ l1x)// ?ltr01//.
by rewrite (ltr_trans l1x)//.
Qed.

Lemma lt0f_exp : forall n x, (0 < x) -> (0 < x^+n).
Proof.
move=> n x l0x; elim: n=> [|n ihn]; first by rewrite expr0 ltr01.
by rewrite exprS ltr_mulPP.
Qed.

Lemma le0f_exp : forall n x, (0 <= x) -> (0 <= x^+n.+1).
Proof.
move=> n x; rewrite ler_eqVlt; case/orP=> hx; last by rewrite ltrE// lt0f_exp.
by rewrite -(eqP hx) exprS mul0r lerr.
Qed.

Lemma lef1_exp : forall x n, 0 <= x -> x <= 1 -> x^+n.+1 <= x.
Proof.
move=> x n l0x l1x; case: (ltrgtP x 0); rewrite ?l0x//; last first.
  by move->; rewrite exprS mul0r lerr.
case: (ltrgtP x 1); rewrite ?l1x//; last by move->; rewrite exp1rn lerr.
move=> ltx1; case: n=> [|n]; first by rewrite expr1 lerr.
by move=> lt0x; rewrite ltrE// ltf1_exp.
Qed.

Lemma le1f_exp : forall x n, 1 <= x -> x <= x^+n.+1.
Proof.
move=> x n; rewrite ler_eqVlt; case/orP=> hx.
  by rewrite -(eqP hx) exp1rn lerr.
case: n=> [|n]; first by rewrite expr1 lerr.
by rewrite ltrE// lt1f_exp.
Qed.

Lemma lef_expP : forall n x y, 0 <= x -> 0 <= y -> (x <= y) = (x^+n.+1 <= y^+n.+1).
Proof.
move=> n x y l0x l0y; case: (ltrgtP x 0); rewrite ?l0x//; last first.
  by move->; rewrite exprS mul0r le0f_exp.
case: (ltrgtP y 0); rewrite ?l0y//; last first.
  move->; rewrite [0^+_]exprS mul0r=> lt0x.
  by apply/idP/idP; apply: contraLR; rewrite lt0x// lt0f_exp.
elim:n =>[|n ihn]; first by rewrite !expr1.
move=> lt0y ltOx; rewrite ![_^+n.+2]exprSr; apply/idP/idP=> hxy.
  move:(hxy); rewrite -(@ltf_mulP _ (x^+n.+1)); last by rewrite lt0f_exp.
  by rewrite mulrC; move/ler_trans=> -> //; rewrite mulrC ltf_mulP// -ihn.
apply/negP; move/negP=> hyx; move:(hyx); apply/negP; apply/negPn.
rewrite ihn// -(@ltf_mulP _ x)// (ler_trans hxy)// ![y^+_*_]mulrC.
by rewrite ltf_mulP ?lt0f_exp// ltrE.
Qed.

Require Import zmodp.

Lemma signr_exp : forall s x n, (s ?* x)^+n.+1 = (s ^+ n.+1) ?* (x ^+ n.+1).
Proof.
move=> s x n; case: (inF3P s)=> ->; first by rewrite ![0^+_.+1]exprS !mul0r.
  by rewrite exp1rn.
rewrite [_^+_]exprN -![(-1)^+n.+1]signr_odd.
by case: (odd n.+1); rewrite !(expr0,expr1) !(mulNr,mul1r).
Qed.

Lemma absr_sign : forall s x, s != 0 -> |s ?* x| = |x|.
Proof.
move=> s x; case: (ltrgtP x 0)=> hx; case: (inF3P s)=> -> //= _;
by rewrite absr_opp.
Qed.

Lemma absr1 : |1| = 1 :> R.
Proof. by rewrite absrP// ler01. Qed.

Lemma absf_exp : forall x n, |x^+n| = |x|^+n.
Proof.
move=> x n; case: (ltrgtP x 0)=> hx; last first.
- rewrite hx; case: n=> [|n]; first by rewrite ?expr0 absr1.
  by rewrite absr0 exprS mul0r absr0.
- by rewrite !absrP// ltrE// lt0f_exp.
- case: n=> [|n]; first by rewrite !expr0 absrP// ler01.
  rewrite {1}[x]rsign_abs signr_exp absr_sign; first by rewrite absrP// le0f_exp.
  by rewrite (signrN hx) -signr_odd; case: (odd _).
Qed.

Lemma unit1P : forall x n, x > 0 -> exists2 y, y>0 & y^+(n.+1) = x.
Proof.
move=> x n l0x.
case: (ltrgtP x 1)=> hx; last by exists 1; rewrite ?hx ?ltr01// exp1rn.
  case: (@ivt ('X ^+ n.+1 - x%:P) 0 1); first by rewrite ler01.
    rewrite ?(horner_lin,horner_exp).
    by rewrite exprS mul0r sub0r exp1rn signNr -ler_sub ltrE// ltrE.
  move=> y; case/andP=> [l0y ly1]; rewrite /root ?(horner_lin,horner_exp).
  rewrite subr_eq0; move/eqP=> hyx; exists y=> //; rewrite ltr_neqAle l0y.
  rewrite eq_sym andbT; apply/eqP=> y0; move: hyx; rewrite y0.
  by rewrite exprS mul0r=> x0; move: l0x; rewrite -x0 lerr.
case: (@ivt ('X ^+ n.+1 - x%:P) 0 x); first by rewrite ltrE.
  rewrite ?(horner_lin,horner_exp) exprS mul0r sub0r.
  by rewrite signNr -ler_sub ltrE//= le1f_exp// ltrE.
move=> y; case/andP=> l0y lyx; rewrite /root ?(horner_lin,horner_exp).
rewrite subr_eq0; move/eqP=> hyx; exists y=> //; rewrite ltr_neqAle l0y.
rewrite eq_sym andbT; apply/eqP=> y0; move: hyx; rewrite y0.
by rewrite exprS mul0r=> x0; move: l0x; rewrite -x0 lerr.
Qed.

Definition minr x y := if x<=y then x else y.

Lemma lt_minr : forall x y z, (minr x y > z) = (x > z) && (y > z).
Proof.
rewrite /minr=> x y z; case: (lerP x y)=> lxy; apply/idP/idP.
- by move=> lzx; rewrite lzx (ltr_le_trans _ lxy).
- by case/andP=> ->.
- by move=> lzy; rewrite lzy (ltr_trans _ lxy).
- by case/andP=> _ ->.
Qed.

Lemma ler_divr : forall z x y, 0 < z -> (x <= y / z) = (x * z <= y).
Proof.
move=> z x y z0; rewrite -(@ltf_mulP _ z)// mulrAC -mulrA divff ?mulr1//.
by rewrite eq_sym ltrE.
Qed.

Lemma lt0fSn : forall n, 0 < (n.+1)%:R :> R.
Proof.
elim=> [|n ihn]; first by rewrite ltr01.
rewrite (ltr_le_trans ihn)// -[_.+1%:R]add0r [_.+2%:R]mulrS.
by rewrite ler_add2l ler01.
Qed.

Lemma lef0_inv : forall x, (0 >= x) = (0 >= x^-1).
Proof.
move=> x; case x0: (x == 0); first by rewrite (eqP x0) invr0 lerr.
by rewrite ![_<=0]ler_lt ?invr_eq0 ?x0// le0f_inv.
Qed.


Lemma poly_cont : forall x p d, d > 0 -> exists2 e, 
  e > 0 & forall y, |y - x| < e -> |p.[y] - p.[x]| < d.
Proof.
move=> x; elim/(@poly_divXMa x).
  move=> d dp; exists 1; rewrite ?ltr01// => y hy. 
  by rewrite !hornerC subrr absr0.
move=> p n k pxn0 Pp d dp.
case: (Pp (|p.[x]|/2%:R)). 
  by rewrite ltr_mulPP// -?lef0_inv ?lt0fSn// absrE.
move=> e' e'p He'.
case: (@unit1P (d / ((3%:R/2%:R)*|p.[x]|)) n).
  by rewrite ltr_mulPP// -lef0_inv ?ltr_mulPP// -?lef0_inv ?lt0fSn// absrE.
move=> e ep roote.
exists (minr e e'); first by rewrite lt_minr ep.
move=> y. rewrite lt_minr. case/andP=> hxye hxye'.
move: (ler_lt_trans (subr_abs_le _ _) (He' _ hxye')).
rewrite ler_subr absr_opp.
rewrite (_:forall x, x / 2%:R + x = (3%:R / 2%:R)*x); last first.
  move=> a. symmetry. rewrite mulrSr mulr_addl divff ?oRing_carac//.
  by rewrite addrC mulr_addl !mul1r mulrC.
move=> hpypx.
have:= (He' _ hxye'); rewrite addrC.
move/(ler_lt_trans (subr_abs_le _ _)).
rewrite absr_opp ler_sub addrAC -ler_sub.
rewrite (_:forall x, x - x / 2%:R = x / 2%:R); last first.
  move=> a. rewrite -{1}[a]mulr1 -mulr_subr; congr (_*_).
  rewrite -{1}[1](@divff _ 2%:R) ?oRing_carac// -{2}[2%:R^-1]mul1r.
  by rewrite -mulr_subl {1}mulrSr -addrA subrr addr0 mulr1n mul1r.
move=> hpxpy.
rewrite !(horner_lin,horner_exp). rewrite subrr [0^+_]exprS mul0r mulr0 add0r.
rewrite -addrA subrr addr0 !absf_mul mulrC.
move: hxye. rewrite absf_exp (lef_expP n)//; last by rewrite ltrE. 
rewrite -(@ltf_mulP _ (|p.[y]|)); last first.
  by apply: ler_lt_trans hpxpy; rewrite le0r_mul// -le0f_inv ltrE// lt0fSn.
move/ltr_trans=> -> //. rewrite roote mulrC mulrA mulrAC -{1}[d]mul1r.
rewrite ltf_mulP// ler_divr; first by rewrite mul1r.
by rewrite !ltr_mulPP// -?lef0_inv ?lt0fSn// absrE.
Qed.



(* Lemma deriv_sign : forall p a b, *)
(*   (forall x, a <= x <= b -> p^`.[x] >= 0) *)
(*   -> (forall x y, (a <= x <= b) && (a <= y <= b)  *)
(*     ->  x <= y -> p.[x] <= p.[y] ). *)
(* Proof. *)
(* move=> p a b. *)



(* Definition signs lp := *)
(*   let fix loop lp n := *)
(*     if n is n.+1 then *)
      
(*       else *)
        

End PolyReal.



