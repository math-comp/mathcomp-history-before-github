(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
Require Import ssralg poly orderedalg zmodp polydiv.

(* Reserved Notation "a ^`"(at level 3, format "a ^`"). *)
(* Reserved Notation "a ^`( n )" (at level 3, format "a ^`( n )"). *)
(* Reserved Notation "a ^`N( n )" (at level 3, format "a ^`N( n )"). *)

Import GRing.Theory.
Import OrderedRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

(* Notation "a ^` ( n )" := (derivn a n). *)
(* Notation "a ^`" := (deriv a). *)

End PolyOrder.

Section PolyReal.

Variable R : oFieldType.

Implicit Types a b c : R.
Implicit Types x y z t : R.
Implicit Types p q r : {poly R}.

Hypothesis ivt : poly_ivt R.

Lemma polyrealN0_sign : forall p a b, 
  (forall x, a <= x <= b -> ~~ root p x) -> 
  exists s, (forall x, a <= x <= b -> \s (p.[x]) = s).
Proof.
rewrite /root=> p a b np0; exists (\s p.[a]); move=> x laxb; move:(np0 _ laxb).
case: (ltrgtP p.[x] 0)=> [spx npx0|spx npx0|]; last by move->; rewrite ?eqxx.
  case: (ltrP p.[a] 0)=> spa; first by rewrite !ltr0_sign.
  case/andP:laxb=>lax lxb; case:(@ivt (-p) a x)=> //.
    by rewrite !horner_opp !oppr_cp0/= spa ltrE.
  move=> y; case/andP=> lay lyx; rewrite /root horner_opp oppr_eq0.
  by rewrite (negPf (np0 _ _))// lay/= (ler_trans lyx).
case: (lerP p.[a] 0)=> spa; last by rewrite !gtr0_sign.
case/andP:laxb=>lax lxb; case:(@ivt p a x)=> //; first by rewrite spa ltrE.
move=> y; case/andP=> lay lyx; rewrite /root.
by rewrite (negPf (np0 _ _))// lay/= (ler_trans lyx).
Qed.

Lemma divFp_spec : forall p q, let k := lead_coef q ^- scalp p q in
  p = (k *: (p %/ q)) * q + k *: (p %% q).
Proof.
move=> p q k; apply/eqP.
rewrite -(inj_eq (@mulfI _ (k^-1)%:P  _)); last first.
  by rewrite polyC_eq0 invrK scalp_Ineq0.
rewrite !mul_polyC scaler_addr scaler_mull !scalerA mulVf.
  by rewrite invrK !scale1r divCp_spec.
by rewrite invr_neq0 // scalp_Ineq0.
Qed. 

Lemma maxdivFp : forall p a, p != 0 -> 
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
rewrite -!mul_polyC.
rewrite mulrA -polyC_mul [_^-1*_]mulrC divff // polyC1 mul1r mulrA=> hp.
case q0 : (q == 0); first by move: hp p0; rewrite (eqP q0) mulr0 mul0r=> ->.
move:sp; rewrite (eqP hp) size_mul_id; last 2 first.
- by rewrite mulf_neq0// ?polyC_eq0 ?invr_eq0 ?c0// q0.
- by rewrite -size_poly_eq0 size_XMa.
rewrite size_XMa size_mul_id ?polyC_eq0 ?invr_eq0 ?c0// ?q0//.
rewrite size_polyC invr_eq0 c0 add1n addnS addn1 //=. 
move/eqP; rewrite eqSS; move/eqP; move/ihn=> ihnq.
case: (ihnq a)=> [|r [m ra0 Pq]]; first by rewrite q0.
exists ((c^-1)%:P * r); exists m.+1.
  by rewrite horner_lin mulf_neq0 // invr_eq0.
by rewrite Pq -!mulrA -exprSr.
Qed.


Lemma divFp_eq0 : forall p q, q != 0 -> (p %/ q == 0) = (size p < size q)%N.
Proof.
move=> p q q0; apply/idP/idP=> hpq; last by rewrite divp_size.
case p0: (p == 0); first by rewrite (eqP p0) size_poly0 lt0n size_poly_eq0.
case: (divCp_spec p q); rewrite (eqP hpq) mul0r add0r=> hpmpq.
apply: leq_ltn_trans (modp_spec p _); rewrite // -hpmpq -mul_polyC size_mul_id ?p0//.
   by rewrite size_polyC scalp_Ineq0.
by rewrite polyC_eq0 scalp_Ineq0.
Qed.

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
case: (@divFp_spec p ('X - a%:P))=> ->.
set q := (_ *: _); set c := (_ *: _).
have qnz : q != 0.
  rewrite scaler_eq0 negb_or invr_neq0; last by rewrite scalp_Ineq0.
  by rewrite divFp_eq0 -?size_poly_eq0 size_XMa// -leqNgt sp1.
rewrite [c]size1_polyC; first last.
  rewrite -ltnS size_scaler; last by rewrite invr_neq0 // scalp_Ineq0.
  by rewrite -(size_XMa  a) modp_spec // -size_poly_eq0 size_XMa.
case: (@maxdivFp _ a qnz) => r [m ra0 hqr]; rewrite hqr -mulrA -exprSr.
apply: Pq=> //; apply: ihn.
rewrite (leq_trans (_ : size r <= size q)%N)//.
  have xam : ('X - a%:P) ^+ m != 0.  
    elim:m {hqr}=>[|m ihm]; rewrite ?expr0 ?oner_eq0//.
    by rewrite exprS mulf_neq0// -size_poly_eq0 size_XMa.
  rewrite hqr size_mul_id //; last first.
    by move: ra0; apply: contra; move/eqP->; rewrite horner0.
  rewrite -[size (('X-_)^+_)]prednK; last by rewrite lt0n size_poly_eq0.
  by rewrite addnC leq_addl.
rewrite size_scaler; last by rewrite invr_neq0 //scalp_Ineq0.
by rewrite size_divp -?size_poly_eq0 size_XMa//= subn1 -ltnS (ltn_predK sp1).
Qed.

Lemma nth_root : forall x n, x > 0 -> exists2 y, y>0 & y^+(n.+1) = x.
Proof.
move=> x n l0x.
case: (ltrgtP x 1)=> hx; last by exists 1; rewrite ?hx ?lter01// exp1rn.
  case: (@ivt ('X ^+ n.+1 - x%:P) 0 1); first by rewrite ler01.
    rewrite ?(horner_lin,horner_exp).
    by rewrite exprS mul0r sub0r exp1rn oppr_cp0 subr_gte0/= ltrE// ltrE.
  move=> y; case/andP=> [l0y ly1]; rewrite /root ?(horner_lin,horner_exp).
  rewrite subr_eq0; move/eqP=> hyx; exists y=> //; rewrite ltr_neqAle l0y.
  rewrite eq_sym andbT; apply/eqP=> y0; move: hyx; rewrite y0.
  by rewrite exprS mul0r=> x0; move: l0x; rewrite -x0 ltrr.
case: (@ivt ('X ^+ n.+1 - x%:P) 0 x); first by rewrite ltrE.
  rewrite ?(horner_lin,horner_exp) exprS mul0r sub0r.
  by rewrite oppr_cp0 subr_gte0/= ltrE//= lef_exprS// ltrE.
move=> y; case/andP=> l0y lyx; rewrite /root ?(horner_lin,horner_exp).
rewrite subr_eq0; move/eqP=> hyx; exists y=> //; rewrite ltr_neqAle l0y.
rewrite eq_sym andbT; apply/eqP=> y0; move: hyx; rewrite y0.
by rewrite exprS mul0r=> x0; move: l0x; rewrite -x0 ltrr.
Qed.

Lemma poly_cont : forall x p e, e > 0 -> exists2 d, 
  d > 0 & forall y, `|y - x| < d -> `|p.[y] - p.[x]| < e.
Proof.
move=> x; elim/(@poly_divXMa x).
  move=> e ep; exists 1; rewrite ?ltr01// => y hy. 
  by rewrite !hornerC subrr absr0.
move=> p n k pxn0 Pp e ep.
case: (Pp (`|p.[x]|/2%:R)). 
  by rewrite mulr_cp0p// ?invf_gte0//= ?gtf0Sn// absrE.
move=> d' d'p He'.
case: (@nth_root (e / ((3%:R/2%:R) * `|p.[x]|)) n).
  by rewrite mulr_cp0p// invf_gte0 ?mulr_cp0p//= ?invf_gte0/= ?gtf0Sn// absrE.
move=> d dp rootd.
exists (minr d d'); first by rewrite ltr_minr dp.
move=> y; rewrite ltr_minr. case/andP=> hxye hxye'.
move: (ler_lte_trans (subr_abs_le _ _) (He' _ hxye')).
rewrite lter_subr absr_opp.
rewrite (_:forall x, x / 2%:R + x = (3%:R / 2%:R)*x); last first.
  move=> a; apply/eqP; rewrite -(inj_eq (@mulfI _ 2%:R _))// ?charor//.
  rewrite mulr_addr mulrA mulrAC divff ?charor// -mulr_addl -{1}[1]mulr1n.
  by rewrite -natr_add add1n !mulrA [2%:R*_*_]mulrAC divff ?charor// mul1r.
move=> hpypx.
have:= (He' _ hxye'); rewrite addrC.
move/(ler_lte_trans (subr_abs_le _ _)).
rewrite absr_opp -subr_lte0/= addrAC subr_lte0.
rewrite (_:forall x, x - x / 2%:R = x / 2%:R); last first.
  move=> a; apply/eqP.
  rewrite -(inj_eq (@mulfI _ 2%:R _))// ?charor//.
  rewrite mulr_addr mulrN mulrA mulrAC divff ?charor//.
  rewrite mulr_natl mul1r -subr_eq0 -addrA -oppr_add -{2}[a]mulr1n.
  by rewrite -mulrSr subrr.
move=> hpxpy.
rewrite !(horner_lin,horner_exp) subrr [0^+_]exprS mul0r mulr0 add0r.
rewrite -addrA subrr addr0 !absf_mul mulrC.
move: hxye; rewrite absf_exp -(lef_expS2 n)// ?absrE//; last first.
  by rewrite ltrE. 
rewrite -(@ltef_mulpr _ (`|p.[y]|))/=; last first.
  apply: ler_lte_trans hpxpy; rewrite mulr_cp0p//= ?absrE//.
  by rewrite invf_gte0/= ltrE// gtf0Sn.
move/lter_trans=> -> //; rewrite rootd mulrC mulrA mulrAC -{2}[e]mul1r.
rewrite ltef_mulp// ltef_divpl/=; first by rewrite mul1r.
by rewrite !mulr_cp0p// ?invf_gte0/= ?gtf0Sn// ?absrE// gtf0Sn.
Qed.

(* Notation "a ^`( n )" := (derivn a n). *)
(* Notation "a ^`" := (deriv a). *)

(* Lemma size_poly_ind : forall K : {poly R} -> Prop, *)
(*   K 0 ->  *)
(*   (forall p sp, size p = sp.+1 ->   *)
(*     forall q, (size q <= sp)%N -> K q -> K p) *)
(*   -> forall p, K p. *)
(* Proof. *)
(* move=> K K0 ihK p. *)
(* move: {-2}p (leqnn (size p)); elim: (size p)=> {p} [|n ihn] p spn. *)
(*   by move: spn; rewrite leqn0 size_poly_eq0; move/eqP->. *)
(* case spSn: (size p == n.+1). *)
(*   move/eqP:spSn; move/ihK=> ihKp; apply: (ihKp 0)=>//. *)
(*   by rewrite size_poly0. *)
(* by move:spn; rewrite leq_eqVlt spSn /= ltnS; by move/ihn.  *)
(* Qed. *)

(* Lemma size_poly_indW : forall K : {poly R} -> Prop, *)
(*   K 0 ->  *)
(*   (forall p sp, size p = sp.+1 ->   *)
(*     forall q, size q = sp -> K q -> K p) *)
(*   -> forall p, K p. *)
(* Proof. *)
(* move=> K K0 ihK p. *)
(* move: {-2}p (leqnn (size p)); elim: (size p)=> {p} [|n ihn] p spn. *)
(*   by move: spn; rewrite leqn0 size_poly_eq0; move/eqP->. *)
(* case spSn: (size p == n.+1). *)
(*   move/eqP:spSn; move/ihK=> ihKp; case: n ihn spn ihKp=> [|n] ihn spn ihKp. *)
(*     by apply: (ihKp 0)=>//; rewrite size_poly0. *)
(*   apply: (ihKp 'X^n)=>//; first by rewrite size_polyXn. *)
(*   by apply: ihn; rewrite size_polyXn. *)
(* by move:spn; rewrite leq_eqVlt spSn /= ltnS; by move/ihn.  *)
(* Qed. *)

Definition has_lt_roots_in p n a b := 
  forall (t : seq R), size t == n -> uniq t ->
    (forall x, x \in t -> (a < x < b) && (p.[x] == 0)) 
    -> p == 0.

Lemma poly_ltsp_roots : forall p a b, has_lt_roots_in p (size p) a b.
Proof.
rewrite /has_lt_roots_in.
move=> p; move: {-2}p (erefl (size p)); elim: (size p)=> {p} [|n ihn] p spSn.
  by move/eqP: spSn; rewrite size_poly_eq0; move/eqP->.
move=> a b t; rewrite spSn=> st /=.
case: t st=> // x s /=.
rewrite eqSS => ss /=; case/andP=> xins us hs.
move: (hs x); rewrite inE eqxx /= => hx.
case/andP: (hx is_true_true)=> haxb hpx.
case: (ltngtP (size p) 1)=> p1; first 2 last.
- by rewrite [p]size1_polyC ?p1// hornerC -polyC_eq0 -size1_polyC// p1 in hpx.
- by move: p1; rewrite ltnS leqn0 size_poly_eq0.
case: (divFp_spec p ('X - x%:P)).
move: (hpx); rewrite [_==_]root_factor_theorem=> dvdxp.
move: (dvdxp); rewrite /dvdp; move/eqP ->.
rewrite scaler0 addr0; set q : {poly R} := _*: (_ %/ _)=> hpq.
rewrite hpq mulf_eq0 -[_-_==_]size_poly_eq0 size_XMa orbF.
have sqn : size q = n.
  rewrite size_scaler; last by rewrite invr_neq0 // scalp_Ineq0.
  by rewrite size_divp -?size_poly_eq0 size_XMa//= spSn subn1.
apply: (ihn _ _ a b s)=> //; first by rewrite sqn.
move=> y yins.
case exy: (y == x); first by move: xins; rewrite -(eqP exy) yins.
have := (hs y); rewrite inE exy /= yins hpq.
rewrite horner_mul horner_add horner_opp hornerX hornerC mulf_eq0.
by rewrite subr_eq0 exy orbF=> hq; apply: hq.
Qed.

Lemma ivt_sign : forall (p : {poly R}) (a b : R),
  a <= b -> \s p.[a] * \s p.[b] == -1 -> exists2 x : R, a < x < b & root p x.
Proof.
move=> p a b hab. 
rewrite muls_eqA// mulrN1; case/andP; move/eqP=> hpapb pb0.
case: (@ivt (((\s p.[b]) ?* 1)%:P *p) a b)=> //.
   rewrite -{1}hpapb !horner_lin -!smulr_mul !mul1r -smulNr.
   by rewrite -!absrP oppr_cp0/= !absrE.
move=> c; case/andP=> lac lcb; rewrite /root.
rewrite !horner_lin mulf_eq0 smul1_eq0 (negPf pb0) /= => pc0.
exists c=> //. rewrite !ltr_neqAle lac lcb !andbT.
apply/andP; split.
  move: pb0; rewrite -hpapb eqr_oppC oppr0; apply: contra.
  by move/eqP->; rewrite (eqP pc0) signr0.
by move: pb0; apply: contra; move/eqP<-; rewrite (eqP pc0) signr0.
Qed.

Lemma rolle_weak : forall a b p, a < b ->
  (p.[a] == 0) && (p.[b] == 0) ->
  exists2 c, a < c < b & (p^`().[c] == 0 \/ p.[c] == 0).
Proof.
move=> a b p lab; case/andP=> pa0 pb0.
case p0: (p == 0).
  rewrite (eqP p0); exists ((a+b)/2%:R); first exact: midf_lte.
  by left; rewrite derivC horner0 eqxx.
case: (@maxdivFp p a)=> [|p' []]; first by rewrite p0.
case; first by rewrite expr0 mulr1=> p'a0 pp'; rewrite -pp' pa0 in p'a0.
move=> n p'a0 hpp'.  
case: (@maxdivFp p' b)=> [|q []]. 
  by move:p'a0; apply: contra; move/eqP->; rewrite hornerC.
case; first rewrite expr0 mulr1=> qb0 p'q.
  move: (pb0); rewrite hpp' p'q ?(horner_lin,horner_exp) mulf_eq0.
  by rewrite orbC expf_eq0 subr_eq0 eq_sym ltrWN// andbF orFb (negPf qb0).
move=> m qb0 hp'q; rewrite hpp' hp'q.
case: (inF3P (\s q.[a] * \s q.[b])); first 2 last.
- move/eqP=> sqasb; case: (@ivt_sign q a b)=> //; first exact: ltrW.
  move=> c lacb rqc; exists c=> //; right.
  by rewrite !(horner_lin,horner_exp) (eqP rqc) !mul0r.
- move/eqP; rewrite mulf_eq0 !signr_cp0 (negPf qb0) orbF; move/eqP=> qa0.
  by move: p'a0; rewrite hp'q ?(horner_lin,horner_exp) qa0 mul0r eqxx.
- move/eqP; rewrite muls_eqA// mulr1; case/andP; move/eqP=> sab sbn0.
  rewrite !derivCE subr0 !mulr1 mulr_addl !exprS. 
  set xan := (_^+n); set xbm := (_^+m).
  rewrite !mulrnAr !mulrA ![_*xbm]mulrC -!mulrA [q*_]mulrC -!mulrnAr.
  rewrite ![_*(_*xan)]mulrA ![_*xan]mulrC !mulrA [xbm*_]mulrC.
  rewrite -![(_*_)*_*_]mulrA [_*(q*+_)]mulrC -![(_*_)*_+(_*_)*_]mulr_addr.
  set r := _ + _ + _.
  case: (@ivt_sign (((\s q.[b]) ?* 1)%:P * r) a b); first exact: ltrW.
  rewrite !horner_mul !hornerC !signr_mul !signr_smul !signr1 !mulr1.
  rewrite mulrAC !mulrA mulss signr_cp0 qb0 mul1r.
  rewrite /r !horner_add !horner_mul.
  rewrite !horner_add !hornerX !horner_opp !hornerC.
  rewrite !subrr !(mul0r,mulr0,add0r,addr0).
  rewrite !horner_mulrn !signr_mul !signr_mulrn sab.
  rewrite mulrAC !mulrA mulss signr_cp0 qb0 mul1r.
  rewrite -oppr_sub signr_opp mulNr mulss signr_cp0.
  by rewrite subr_eq0 [b == _]eq_sym ltrE.
move=> c lacb; rewrite /root horner_mul hornerC mulf_eq0.
rewrite smul1_eq0 signr_cp0 (negPf qb0) orFb=> rc0.
by exists c=> //; left; rewrite !horner_mul !mulf_eq0 rc0 !orbT.
Qed.



Lemma rolle : forall a b p, a < b ->
  (p.[a] == 0) && (p.[b] == 0) ->
  exists2 c, a < c < b & ((p^`()).[c] == 0).
Proof.
move=> a b p lab; case/andP=> pa0 pb0.
have := @poly_ltsp_roots p a b.
elim: (size p) a b lab pa0 pb0=> [|n ihn] a b lab pa0 pb0 max_roots; 
  first rewrite (eqP (@max_roots [::] _ _ _)) //=. 
  by exists ((a+b)/2%:R); first exact: midf_lte; rewrite derivC horner0.
case: (@rolle_weak a b p); rewrite // ?pa0 ?pb0 //=.
move=> c; case/andP=>lac lcb [] pc0; first by exists c; rewrite // lac.
suff: exists2 d : R, a < d < c & (p^`()).[d] == 0.
  case=> [d]; case/andP=> lad ldc p'd0.
  by exists d; rewrite // lad andTb (lter_trans ldc).
apply: ihn=> //.
move=> t stn ut Pt; apply: (max_roots (c::t))=> //=.
  rewrite ut andbT; apply/negP=> cint.
  by move: (Pt c cint); rewrite lterr andbF.
move=> x; rewrite inE; case/orP; first by move/eqP->; rewrite lac lcb.
by move/Pt; case/andP; case/andP=> -> lxc ->; rewrite (lter_trans  lxc).
Qed.

Lemma mvt : forall a b p, a < b ->
  exists2 c, a < c < b & p.[b] - p.[a] = (p^`()).[c] * (b - a).
Proof.
move=> a b p lab.
pose q := (p.[b] - p.[a])%:P * ('X - a%:P) - (b - a)%:P * (p - p.[a]%:P).
case: (@rolle a b q)=> //.
  by rewrite /q !horner_lin !(subrr, mulr0) mulrC subrr eqxx.
move=> c lacb q'x0; exists c=> //.
move: q'x0; rewrite /q !derivE !(mul0r,add0r,subr0,mulr1).
by rewrite !horner_lin mulrC subr_eq0; move/eqP.
Qed.

Lemma deriv_sign : forall a b p,
  (forall x, a < x < b -> (p^`()).[x] >= 0)
  -> (forall x y, (a < x < b) && (a < y < b)
    ->  x < y -> p.[x] <= p.[y] ).
Proof.
move=> a b p Pab x y; case/and3P; case/andP=> lax lxb lay lyb lxy.
rewrite -subr_gte0; case: (@mvt x y p)=> //.
move=> c; case/andP=> lxc lcy ->; rewrite mulr_cp0p//=.
  by rewrite Pab// (lter_trans lax)// (lter_trans lcy).
by rewrite subr_gte0/= ltrE.
Qed.



(* Definition signs lp := *)
(*   let fix loop lp n := *)
(*     if n is n.+1 then *)
      
(*       else *)
        

End PolyReal.



