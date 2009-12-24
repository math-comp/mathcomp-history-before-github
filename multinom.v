Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import tuple finfun bigops ssralg poly.

Require Import multi.

Require Import quotient.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Section EquivProps.

Lemma left_trans : forall T0 (e:rel T0),
  symmetric e -> transitive e -> left_transitive e.
Proof.
move=> T0 e sym tr x y exy z; apply/idP/idP; last do [move/tr:exy; exact].
move:exy; rewrite sym; move/tr; exact.
Qed.

End EquivProps.


Section ChoiceTheoryExt.

Variable T : choiceType.
Implicit Types P Q : pred T.

Lemma choosePn : forall P x0, P x0 = false -> choose P x0 = x0.
Proof. by move=> P x0 Px0; rewrite /choose insubF. Qed.

Lemma eq_choose_id : forall P Q x y,
  P =1 Q -> P x -> Q y -> choose P x = choose Q y.
Proof.
move=> P Q x y eQP; rewrite eQP => Qx Qy;
have ->: choose P x = choose Q x; [exact: eq_choose | exact: choose_id].
Qed.

End ChoiceTheoryExt.

Open Scope ring_scope.
Import GRing.Theory.


Section MultinomialTerm.

Variable R : idomainType.

Inductive multi_term :=
| Coef of R
| Var of nat
| Sum   of multi_term & multi_term
| Prod  of multi_term & multi_term.

Fixpoint deg_term t := 
  match t with
    | Coef _ => 0%N
    | Var n => n.+1
    | Sum u v => maxn (deg_term u) (deg_term v)
    | Prod u v => maxn (deg_term u) (deg_term v)
  end.

Fixpoint interp n m : multi R n :=
  match m with
    | Coef x => multiC n x
    | Var i => 
      (if i < n as b return (((i < n) = b -> multi R n))
        then fun iltn => cast_multi (subnK iltn) 'X_(Ordinal (leqnn i.+1))
        else fun _ => 0)   (refl_equal (i < n))
    | Sum p q => interp n p + interp n q
    | Prod p q => interp n p * interp n q
  end.

Definition equivm m1 m2 := 
  let n1 := deg_term m1 in
    let n2 := deg_term m2 in
      interp (maxn n1 n2) m1 == interp (maxn n1 n2) m2.

Lemma cast_multi_inj : forall n i i' n' (m1 m2 : multi R n) 
  (p1: (i+n)%N=n') (p2: (i'+n)%N=n'),
  cast_multi p1 m1 == cast_multi p2 m2 = (m1 == m2).
Proof.
move=> n i i' n' m1 m2 p1 p2.
have:=p2. rewrite -{1}[n']p1. move/eqP. rewrite eqn_addr.
move/eqP. move=> /= Eii. move:p2. rewrite Eii=> p2 {Eii}.
have <-: p1 = p2; first exact: nat_irrelevance.
apply/idP/idP; last by move/eqP->.
move => Hm {p2}.
have : inject i m1 = inject i m2; last first.
   by move/eqP; rewrite (inj_eq (@inject_inj _ _ _)).
pose f N (P:(i + n)%N = N) := cast_multi P m1 == cast_multi P m2.
have fn' : f n' p1; first exact: Hm.
have fni : f (i+n)%N (erefl (i+n)%N).
   have: {q | f (i+n)%N q}; first by rewrite {-1 3}p1; exists p1.
   case=>Pm. 
   by have ->: Pm=(@erefl nat (addn i n)); first exact: nat_irrelevance.
by move:fni; move/eqP.
Qed.

Lemma Emj_Enk : forall i j k m n (Emj : (m + i)%N = j) 
  (Enk : (n + j)%N = k), (n + m + i)%N = k.
Proof.
by move => i j k m n <-; rewrite addnA.
Defined.

Lemma cast_multiS : forall n i n' 
  (m: multi R n) (p: (i+n)%N=n') (pS: ((i.+1)+n)%N=n'.+1),
  (cast_multi pS m) = (cast_multi p m)%:P.
Proof.
move=> n i n' m p pS.
pose f N := forall (p : (i + n)%N = N) (pS : (i.+1 + n)%N = N.+1) ,  
  cast_multi pS m = (cast_multi p m)%:P.
have : f n'; last done. 
rewrite -p /f /= => p0 pS0.
have ->: (p0 = erefl (i + n)%N); first exact: nat_irrelevance.
have ->: (pS0 = erefl (i.+1 + n)%N); first exact: nat_irrelevance.
by rewrite /=.
Qed.

Lemma injectnm_cast_multi : forall i m n p, 
  inject (n+m)%N p = 
  ((@cast_multi R (m+i)%N n ((n+m)+i)%N (addnA _ _ _)) \o (inject m)) p.
Proof.
move=>i m n p; elim:n=>/=.
  move: (addnA 0%N m i) => EK.
  pose f c := forall (EK : (0+(m+i) = c+i)%N), 
    inject c p = cast_multi EK (inject m p).
  have: (f (0+m)%N); last done.
  rewrite !add0n /f => EK0. 
  by have ->: (EK0 = erefl (m + i)%N); first exact: nat_irrelevance.
move=> n ->; set inj := inject _ _ .
pose f N := forall (p : (n+(m+i))%N = N) (pS : (n.+1+(m+i))%N = N.+1) ,  
  (cast_multi p inj)%:P = cast_multi pS inj.
have: f (n+m+i)%N; last done.
rewrite -addnA /f /= => p0 pS0.
have ->: (p0 = erefl (n + (m + i))%N); first exact: nat_irrelevance.
by have ->: (pS0 = erefl (n.+1 + (m + i))%N); first exact: nat_irrelevance.
Qed.

Lemma cast_multi_add : forall i j k m n Emj Enk p,
  @cast_multi R j n k Enk (@cast_multi R i m j Emj p) =
  @cast_multi R i (n+m)%N k (Emj_Enk Emj Enk) p.
Proof.
move=> i j k m n Emj Enk p.
pose f J K := forall (Emj : (m + i)%N = J) (Enk : (n + J)%N = K),
   cast_multi Enk (cast_multi Emj p) = cast_multi (Emj_Enk Emj Enk) p.
have: f j k; last done.
rewrite -Enk -Emj addnA /f. move=> Emje Enke.
have ->: ((Emj_Enk Emje Enke) = erefl (n+m+i)%N); first exact: nat_irrelevance.
rewrite /=. rewrite injectnm_cast_multi /=.
apply/eqP. rewrite cast_multi_inj.
have ->: (Emje = erefl (m+i)%N); first exact: nat_irrelevance.
by rewrite (inj_eq (@inject_inj _ _ _)).
Qed.


Lemma interp_cast_multi : forall n n' m (nltn' : n <= n'),
  deg_term m <= n -> deg_term m <= n' ->
   interp n' m = cast_multi (subnK nltn') (interp n m).
Proof.
move=> n n'; elim.
- move=> a /= nltn' dmltn dmltn'. 
  apply/eqP; rewrite /multiC. 
  by rewrite cast_multi_add /= cast_multi_inj.
- move=> N /= nltn' dmltn dmltn'.
  have : {Nn : N < n = (N < n) | {Nn' : N < n' = (N < n') |
    (if N < n' as b return ((N < n') = b -> multi R n')
      then fun iltn  =>  cast_multi (subnK iltn) 'X_(Ordinal (leqnn N.+1))
      else fun _ => 0) Nn' =
  cast_multi (subnK nltn')
  ((if N < n as b return ((N < n) = b -> multi R n)
    then
      fun iltn => cast_multi (subnK iltn) 'X_(Ordinal (leqnn N.+1))
    else fun _ => 0) Nn) }}.
  rewrite {2 4 5}dmltn'.
  rewrite {2 4 5}dmltn.
  exists dmltn. exists dmltn'.
 
  

 Set Printing All.
  admit.
- move=> m1 Hm1 m2 Hm2 nltn' /=; rewrite !leq_maxl.
  move/andP=>[dm1n dm1n']; move/andP=>[dm2n dm2n'].
  rewrite (Hm1 nltn') // (Hm2 nltn') //.
  by rewrite (ringM_add (cast_multiM _ _)).
- move=> m1 Hm1 m2 Hm2 nltn' /=; rewrite !leq_maxl.
  move/andP=>[dm1n dm1n']; move/andP=>[dm2n dm2n'].
  rewrite (Hm1 nltn') // (Hm2 nltn') //.
  by rewrite (ringM_mul (cast_multiM _ _)).
Qed.

Lemma interp_gtn : forall n m1 m2, 
  maxn (deg_term m1) (deg_term m2) <= n -> 
  equivm m1 m2 = (interp n m1 == interp n m2).
Proof.
move=> n m1 m2 p.
rewrite !(interp_cast_multi p).
  - by rewrite cast_multi_inj.
  - by rewrite leq_maxr leqnn orbT.
  - by move:p; rewrite leq_maxl; move/andP=>[].
  - by rewrite leq_maxr leqnn.
  - by move:p; rewrite leq_maxl; move/andP=>[].
Qed.

Lemma equivm_refl : reflexive equivm.
Proof. by move=> x; rewrite /equivm. Qed.

Lemma equivm_sym : symmetric equivm.
Proof. by move=> x y; rewrite /equivm eq_sym maxnC. Qed.

Lemma equivm_trans : transitive equivm.
Proof.
move=> x y z.
rewrite !(@interp_gtn (maxn (maxn (deg_term x) (deg_term y)) (deg_term z))).
- by move/eqP->; move/eqP->.
- by rewrite -maxnA leq_maxr leqnn orbT.
- by rewrite maxnAC leq_maxr leqnn.
- by rewrite maxnC leq_maxr leqnn.
Qed.

Lemma multi_term_eqMixin : Equality.mixin_of multi_term. Admitted.
Canonical Structure multi_term_eqT := EqType _ multi_term_eqMixin.

Lemma multi_term_choiceMixin : Choice.mixin_of (seq (seq multi_term)). Admitted.
Canonical Structure multi_term_cT := ChoiceType _ multi_term_choiceMixin.

Definition equivm_ltrans := left_trans equivm_sym equivm_trans.

Definition canon m := choose (equivm m) m.
Lemma canon_id : forall m, canon (canon m) = canon m.
Proof.
move=> m; rewrite /canon; apply: eq_choose_id; rewrite ?equivm_refl //.
by apply: equivm_ltrans; rewrite equivm_sym chooseP // equivm_refl.
Qed.

Definition axiom m := canon m == m.
Definition multinom := { m | axiom m }.

Definition Multinom := @Sub _ _ [subType of multinom].


Lemma canon_axiom : forall x, axiom (canon x).
Proof. by move=> x; rewrite /axiom canon_id. Qed.

Definition canonM x := @Multinom (canon x) (canon_axiom x).


Lemma canonM_valK : forall x : multinom, canonM (val x) = x.
Proof.
by move=> [x /=]; rewrite /axiom=> Px; apply:val_inj=>/=; rewrite (eqP Px).
Qed.

Canonical Structure multinom_quotType := Eval hnf in
  @QuotType _ multinom [eta val] [eta canonM] canonM_valK.


Definition multiW := @quotW _ multinom_quotType.
Definition multiP := @quotP _ multinom_quotType.
Definition inRatP := insubP [subType of multinom].

Notation zerom := (\pi_multinom (Coef 0)).
Notation onem := (\pi_multinom (Coef 1)).
Notation varm n := (\pi_multinom (Var n)).

Lemma equivmP : forall x y, x == y mod multinom = equivm x y.
Proof.
move=> x y. rewrite -(inj_eq val_inj) /= /canon.
apply/eqP/idP => Hxy.
   apply: (@equivm_trans (choose (equivm x) x));
   last rewrite Hxy equivm_sym; by rewrite chooseP // equivm_refl.
apply: eq_choose_id; rewrite ?equivm_refl //.
exact: equivm_ltrans.
Qed.



Lemma addm_compat : \compat2_multinom _
  (fun x y => \pi_multinom (Sum x y)).
Proof.
apply:compat2Epi=> x y x' y'; rewrite !equivmP /equivm /=.
Admitted.
Notation addm := (qT_op2 addm_compat).

Lemma oppm_compat : \compat1_multinom _
  (fun x => \pi_multinom (Prod (Coef (-1)) x)).
Proof.
apply:compat1Epi=> x y; rewrite !equivmP /equivm /=.
by rewrite !max0n; move/eqP->.
Qed.
Notation oppm := (qT_op1 oppm_compat).

Lemma mulm_compat : \compat2_multinom _
  (fun x y => \pi_multinom (Prod x y)).
Proof.
apply:compat2Epi=> x y x' y'; rewrite !equivmP /equivm /=.
Admitted.
Notation mulm := (qT_op2 mulm_compat).




Lemma addmA : associative addm.
Proof.
elim/multiW=> x; elim/multiW=> y; elim/multiW=> z.
rewrite !qTE; apply/eqP; rewrite -equivP equivmP.
by rewrite /equivm /= addrA.
Qed.


Lemma addmC : commutative addm.
Proof.
elim/multiW=> x; elim/multiW=> y.
rewrite !qTE; apply/eqP; rewrite -equivP equivmP.
by rewrite /equivm /= addrC.
Qed.

Lemma add0m : left_id zerom addm.
Proof.
elim/multiW=> x.
rewrite !qTE; apply/eqP; rewrite -equivP equivmP.
by rewrite /equivm /= (ringM_0 (multiC_morph _ _)) add0r.
Qed.

Lemma addmN : left_inverse zerom oppm addm.
Proof.
elim/multiW=> x. rewrite !qTE. apply/eqP. rewrite -equivP.
rewrite equivmP /equivm /=.
rewrite (ringM_0 (multiC_morph _ _)).
rewrite (ringM_opp (multiC_morph _ _)).
rewrite (ringM_1 (multiC_morph _ _)).
by rewrite mulN1r addrC subrr.
Qed.


Definition multi_zmodMixin :=  ZmodMixin addmA addmC add0m addmN.
Canonical Structure multi_zmodType := Eval hnf in ZmodType _ multi_zmodMixin.










Definition canon_multinom (n:nat) : (multi R n) -> bool :=
  if n is m.+1 then fun (p:multi R m.+1) => size p >= 2
    else fun _ => true.

Fixpoint surj_multi (t : multi_term) : multi R (deg_term t) :=
  match t return multi R (deg_term t) with
    | Coef c => c
    | Monom n => ('X_(Ordinal (ltnSn n)))
    | Prod t1 t2 => 
      let p1 := (surj_multi t1) in
      let p2 := (surj_multi t2) in
        (cast_multi (to_maxn (deg_term t1) (deg_term t2)) p1) 
        * (cast_multi (to_maxm (deg_term t1) (deg_term t2)) p2) 
    | Sum t1 t2 => 
      let p1 := (surj_multi t1) in
      let p2 := (surj_multi t2) in
        (cast_multi (to_maxn (deg_term t1) (deg_term t2)) p1) 
        + (cast_multi (to_maxm (deg_term t1) (deg_term t2)) p2) 
  end.

Fixpoint inj_seq  (n:nat) (M:ringType) 
  (f : M -> multi_term)  (p:seq M) : multi_term :=
  if p is c::q 
    then Sum (f c) (Prod (Monom n) (inj_seq n f q))
    else Coef 0%R.

Fixpoint inj_multi (n:nat) : (multi R n)  -> multi_term :=
  if n is m.+1 return multi R n -> multi_term
    then  fun p => inj_seq  m (@inj_multi m) p
    else  fun (p:R) => Coef p.


Record pre_multinom := PreMultinom {
  preNbVar : nat ;
  prePoly : multi R preNbVar
}.

Record multinom := Multinom {
  nbVar : nat ;
  poly : multi R nbVar ;
  _ : canon_multinom poly
}.

Definition multinom_Sub pm (p : canon_multinom (prePoly pm)) :=  
  Multinom p.
Definition multinom_val p := PreMultinom (poly p).

Lemma multinom_subtype_rec : 
  forall K (_ : forall x Px, K (@multinom_Sub x Px)) u, K u.
Proof.
  move=> K Px [n m p].
  by rewrite (_ : Multinom p = @multinom_Sub (PreMultinom m) p).
Qed.

Lemma multinom_subtype_valSubK : 
  forall x Px, multinom_val (@multinom_Sub x Px) = x.
Proof. by case. Qed.

Canonical Structure multinom_subtype := SubType _ _ _ 
  multinom_subtype_rec multinom_subtype_valSubK.




Fixpoint canonize n : multi R n -> multinom :=
  if n is m.+1 return multi R n -> multinom 
    then (fun p =>
      match p with
        | Polynomial [::] _ => @Multinom 0 0%R is_true_true
        | Polynomial [::c] _ => canonize c
        | Polynomial (a::b::q) pr  => 
          @Multinom m.+1  (Polynomial pr) is_true_true
      end)
    else fun (p:multi R 0) => @Multinom _ p is_true_true.



(* Notation ord x y := (Ordinal (erefl _ : x<y)). *)

Function surj (t : multi_term) : multinom :=
  canonize (surj_multi t).
  (* match t with *)
  (*   | Coef c => @canonize 0 c *)
  (*   | Monom n => canonize ('X_(Ordinal (ltnSn n))) *)
  (*   | Prod t1 t2 =>  *)
  (*     let: Multinom n1 p1 _ := (surj t1) in *)
  (*     let: Multinom n2 p2 _ := (surj t2) in *)
  (*       canonize ((cast_multi (to_maxn n1 n2) p1) * (cast_multi (to_maxm n1 n2) p2)) *)
  (*   | Sum t1 t2 =>  *)
  (*     let: Multinom n1 p1 _:= (surj t1) in *)
  (*     let: Multinom n2 p2 _ := (surj t2) in *)
  (*       canonize ((cast_multi (to_maxn n1 n2) p1) + (cast_multi (to_maxm n1 n2) p2)) *)
  (* end. *)

Function inj (p : multinom) : multi_term := inj_multi (poly p).

Open Scope nat_scope.
Lemma strong_nat_ind : forall P : nat-> Type, 
  (forall n, (forall i : 'I_n, P i) -> P n) -> 
  forall n, P n.
Proof.
move=> P Hn.
suff: forall n, forall i : 'I_n, P i.
   move=> SP n; exact: (SP (n.+1) (ord_max)).
elim; first by case.
move=> n Pn [m]; case: (ltngtP n m) => /=.
   - by move=> Lnm Lmn; move: (leq_trans Lnm Lmn); rewrite ltnn.
   - move=> Lmn _. exact: (Pn (Ordinal Lmn)).
   - move=> <- /= _; exact: Hn.
Defined.
 
Open Scope ring_scope.


Lemma surj_injK : forall (m : multinom), surj (inj m) = m.
Proof.
case. elim/strong_nat_ind. case.
  move=> _ /= p i; congr Multinom; exact: bool_irrelevance.
move=> /= n /= Pt. rewrite /inj /=.
move=> [] /=. elim. exact.
move=> a. elim. exact.
move=> b. elim.
   move=>  /= _ _ bn0 i. rewrite /surj /=.
apply: val_inj=> /=.
   rewrite /maxn /=.
  move=>[n m c].
  move=> /= p i. exists (Coef p). congr Multinom. exact: bool_irrelevance.



Lemma surj_surj : forall m : multinom, {t | surj t = m}.
Proof.
case. elim.
  move=> /= p i. exists (Coef p). congr Multinom. exact: bool_irrelevance.


   
case; elim/strong_nat_ind; case.
   move=>  /= _ c i; exists (Coef c).
   rewrite /surj  /= /multiC /=. Set Printing All.
   congr Multinom. apply: bool_irrelevance.
move=> /= n /= Pt.
have: forall (poly0 : {poly multi R n}) (i : 1 < size poly0),
   {t : multi_term | surj t = Multinom i}.


 []. elim=> /=; first exact.
move=> a; elim=> /=; first exact.
move=> b; elim=> //=.
move=> _ _ . 
   - move=> bneq0 i.
   - have: exists i : ordinal n.+1 nbVar (canonize a) =  
   - have:=  (Pt _ (poly (canonize a))).
   - have:= (Pt (ord_max) b).
   

 exists (Sum (canonize a) (Prod (Monom n) (canonize b))).

 Hq j k. Set Printing All.

Admitted.



Definition inj (m : multinom) := sval (surj_surj m).
Lemma surj_injK : forall m : multinom, surj (inj m) = m.
Proof. move=> m. exact: (svalP (surj_surj m)). Qed.



have : (Hq










Lemma multi_var_max : forall n, 'X_(Ordinal (ltnSn n)) = 'X :> (multi R (n.+1)).
Proof.
move:R. move=>I n. elim:n I.
  rewrite /multi_var /cast_multi /=.
  by rewrite (nat_irrelevance (@subnK (S 0) (S 0) (valP (Ordinal (ltnSn 0)))) (erefl _)) /=.
move=> n EX J.
move:(@EX [idomainType of {poly J}]).
(* Set Printing All. *)

(* move<-.  *)
(* Check cast_multi. *)
(* move/eqP. *)
(* Check inj_eq. *)
(* rewrite -(inj_eq (@inject_inj _ _ 1%N)) /=. *)
(* move/eqP. *)


(* rewrite ((cast_multi (_:(1+n)%N = n.+1)) EX). *)

(* rewrite /multi_var /cast_multi /=. *)

Admitted.


Lemma surj_injK : forall p : multinom, surj (inj_multi p) = p.
Proof.
case. elim; first by move=> p i; congr Multinom; apply: bool_irrelevance.
move=> /= n Hp [[]]; first exact.
move=> /= a p i j /=.
rewrite multi_var_max. 
have -> : 'X = @Polynomial (multi R n) [::0;1] (GRing.nonzero1r _); last first.

rewrite H.


/polyX /= /poly_cons /= /polyC /insubd /odflt /oapp.
rewrite -!insub_eqE /= /insub_eq /=.


rewrite /multi_var. 


/cast_multi /=.
move=> /= b p i j /=.
Set Printing All.

rewrite Hp.

rewrite /inj_multi /=.
rewrite /poly_rect /=.
rewrite /eq_rect /=.


