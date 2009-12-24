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

(* Lemma interp : forall n (m : multi_term), multi R n. *)
(* Proof. *)
(* move=> n. elim. *)
(*  - exact : multiC. *)
(*  - move=> i. case iltn : (i<n). *)
(*       have: ((n - (i.+1)) + i.+1)%N = n; first by rewrite subnK //. *)
(*          move/cast_multi=>CM. apply: CM. *)
(*          apply: multi_var. *)
(*          by apply: (Ordinal ( _ : (i < i.+1)%N)) => //. *)
(*       exact: 0. *)
(*  - admit. *)
(*  - admit. *)
(* Defined. *)
(* Print interp.   *)
      

Fixpoint interp n m : multi R n :=
  match m with
    | Coef x => multiC n x
    | Var i => 
      (if i < n as b return (((i < n) = b -> multi R n))
        then
          fun iltn : (i < n) = true =>
            cast_multi (subnK iltn) 'X_(Ordinal (leqnn i.+1))
        else fun _ : (i < n) = false => 0) 
      (refl_equal (i < n))
    | Sum p q => interp n p + interp n q
    | Prod p q => interp n p * interp n q
  end.

Definition equivm m1 m2 := 
  let n1 := deg_term m1 in
    let n2 := deg_term m2 in
      interp (maxn n1 n2) m1 == interp (maxn n1 n2) m2.

Lemma test : forall i j k m n (Emj : (m + i)%N = j) 
  (Enk : (n + j)%N = k), (n + m + i)%N = k.
Proof.
by move => i j k m n <-; rewrite addnA.
Defined.
Print test. 
(* Function test2 =  *)
(* fun i j k m n : nat => *)
(* [eta eq_ind (m + i)%N *)
(*        (fun x : nat => (n + x)%N = k -> (n + m + i)%N = k) *)
(*        (eq_ind_r (fun x : nat => x = k -> (n + m + i)%N = k) id  *)
(*           (addnA n m i)) j] *)

Lemma cast_multi_add : forall i j k m n Emj Enk p,
  @cast_multi R j n k Enk (@cast_multi R i m j Emj p) =
  @cast_multi R i (n+m)%N k (test Emj Enk) p.
Proof.
move=> i j k m n Emj Enk. 

(*  Emj Enk Emnk p. *)

(* rewrite (_ : Emnk = test Emj Enk); last exact: nat_irrelevance. *)
(* rewrite /cast_multi /test //=.  *)
Admitted.

Lemma cast_multi_inj : forall n i i' n' (m1 m2 : multi R n) 
  (p1: (i+n)%N=n') (p2: (i'+n)%N=n'),
  cast_multi p1 m1 == cast_multi p2 m2 = (m1 == m2).
Proof.
Admitted.

Lemma bla : forall b:bool, b ->
  (if b as b' return (b = b' -> Prop) 
    then fun i : b = true => (i = i) else fun _ => False) (refl_equal b) = ((refl_equal b) = (refl_equal b)).
Proof. by move=> b tb /=; rewrite tb. Qed.

Lemma interp_cast_multi : forall n n' m (nltn' : n <= n'),
  deg_term m <= n -> deg_term m <= n' ->
   interp n' m = cast_multi (subnK nltn') (interp n m).
Proof.
move=> n n'.
elim.
- move=> a /= nltn' dmltn dmltn'. 
  apply/eqP; rewrite /multiC. 
  by rewrite cast_multi_add /= cast_multi_inj.
- move=> N /= nltn' dmltn dmltn'.
have: (if N < n' as b return ((N < n') = b -> multi R n')
    then
     fun iltn : (N < n') = true =>
     cast_multi (subnK iltn) 'X_(Ordinal (leqnn N.+1))
    else fun _ : (N < n') = false => 0) (refl_equal (N < n')) = _.
rewrite dmltn'.
Set Printing All.
move:(N<n).

rewrite !dmltn'.
case b: (ltnP N n') / dmltn nltn' N n' n.


case:(ltnP N n').
rewrite dmltn'.
rewrite  (_ : (refl_equal (N < n))=dmltn).

 Set Printing All.
/cast_multi /=.

   rewrite (eq_inj (@inject_inj _ _ _)).

Admitted.


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
rewrite /equivm.
 Admitted.

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


