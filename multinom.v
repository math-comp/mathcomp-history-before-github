(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import tuple finfun bigop ssralg poly.

(* Require Import multi. *)

Require Import generic_quotient.
Local Open Scope quotient_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.
Import GRing.Theory.


Module MultinomialTerm.
Section MultinomialTerm.

Variable R : ringType.
Variable X : countType.

Inductive multi_term :=
| Coef of R
| Var of X
| Sum   of multi_term & multi_term
| Prod  of multi_term & multi_term.

Fixpoint eqm m m':=
  match m with
    | Coef x => if m' is Coef y then x == y else false
    | Var n => if m' is Var n' then n == n' else false
    | Sum p q => if m' is Sum p' q' then (eqm p p') && (eqm q q') else false
    | Prod p q => if m' is Prod p' q' then (eqm p p') && (eqm q q') else false
  end.

Lemma eqm_eq : Equality.axiom eqm.
Proof.
move=> m m'.
apply:(@iffP (eqm m m')); first exact: idP.
move:m'; elim:m.
  - by move=> s [] //= s'; move/eqP->.
  - by move=> s [] //= s'; move/eqP->.
  - move=> p Hp q Hq [] //= p' q'.
    case/andP=> epp' eqq'. 
    by rewrite (Hp p') // (Hq q').
  - move=> p Hp q Hq [] //= p' q'.
    case/andP=> epp' eqq'. 
    by rewrite (Hp p') // (Hq q').
move->; elim:m'=>/=.
- by move=> s.
- by move=> n.
- by move=> p -> q ->.
- by move=> p -> q ->.
Qed.

Definition multi_term_eqMixin := EqMixin eqm_eq.
Canonical Structure multi_term_eqType := 
  Eval hnf in EqType multi_term multi_term_eqMixin.

Inductive multi_skel :=
| CoefS of nat
| VarS of nat
| SumS   of multi_skel & multi_skel
| ProdS  of multi_skel & multi_skel.

Fixpoint encode_multi_skel m :=
  match m with
    | CoefS i => [::0%N; i]
    | VarS n => [::1%N; n]
    | SumS p q => 2%N::(encode_multi_skel p)++(encode_multi_skel q)
    | ProdS p q => 3%N::(encode_multi_skel p)++(encode_multi_skel q)
  end.

Fixpoint decode_multi_skel_rec s :=
  match s with
    | 0%N::i::r => (CoefS i)::(decode_multi_skel_rec r)
    | 1%N::n::r => (VarS n)::(decode_multi_skel_rec r)
    | 2%N::r => match (decode_multi_skel_rec r) with
                  | p::q::r' => (SumS p q)::r'
                  | _ => [::]
                end
    | 3%N::r => match (decode_multi_skel_rec r) with
                  | p::q::r' => (ProdS p q)::r'
                  | _ => [::]
                end
    | _ => [::]
  end.

Definition decode_multi_skel s :=
  if (decode_multi_skel_rec s) is [::m] then Some m else None.

Lemma code_multi_skel_recK :
forall s m, decode_multi_skel_rec ((encode_multi_skel m) ++ s) 
  = m::(decode_multi_skel_rec s).
Proof.
by move=> s m; elim:m s=> //=; move=> p Hp q Hq s; rewrite -catA Hp Hq.
Qed. 

Lemma code_multi_skelK : pcancel encode_multi_skel decode_multi_skel.
Proof.
rewrite /decode_multi_skel=> m.
by have := (code_multi_skel_recK [::] m); rewrite cats0 => ->.
Qed.

Definition multi_skel_countMixin := PcanCountMixin code_multi_skelK. 

Definition multi_skel_choiceMixin := 
  CountChoiceMixin multi_skel_countMixin.
Definition multi_skel_eqMixin := 
  Countable.EqMixin multi_skel_countMixin.

Canonical Structure multi_skel_eqType := 
  EqType multi_skel multi_skel_eqMixin.
Canonical Structure multi_skel_choiceType := 
  ChoiceType multi_skel multi_skel_choiceMixin.
Canonical Structure multi_skel_countType := 
  CountType multi_skel multi_skel_countMixin.

Fixpoint encode_multi_term_rec (s:seq R) (m:multi_term):=
  match m with
    | Coef x => ((CoefS (size s)), (rcons s x))
    | Var x => ((VarS (pickle x)), s)
    | Sum p q => 
      let: (p',s') := encode_multi_term_rec s p in
      let: (q',s'') := encode_multi_term_rec s' q in
        ((SumS p' q'), s'')
    | Prod p q => 
      let: (p',s') := encode_multi_term_rec s p in
      let: (q',s'') := encode_multi_term_rec s' q in
        ((ProdS p' q'), s'')
end.

Definition encode_multi_term (m:multi_term) : multi_skel * (seq R):=
  encode_multi_term_rec [::] m.

Definition mkVar n : multi_term := odflt (Coef 0) (omap Var (pickle_inv _ n)).

Fixpoint decode_multi_term_rec (s:seq R) (m : multi_skel) :=
    match m with
    | CoefS i => Coef (nth (0:R) s i)
    | VarS n => mkVar n
    | SumS p q =>  
      Sum (decode_multi_term_rec s  p) (decode_multi_term_rec s  q)
    | ProdS p q =>  
      Prod (decode_multi_term_rec s  p) (decode_multi_term_rec s  q)
  end.

Definition decode_multi_term (ms : multi_skel * (seq R)) :=
  decode_multi_term_rec ms.2 ms.1.

Lemma encode_multi_term_ds : forall s m,
   s ++ (snd (encode_multi_term m)) = (snd (encode_multi_term_rec s m)).
Proof.
move=> s m; elim:m s=> //=.
- by move=> x s; rewrite cats1.
- by move=> x s; rewrite cats0.
- rewrite /encode_multi_term /=; move=> p Hp q Hq s.
  case:(encode_multi_term_rec [::] p) (Hp s)=> /= p0 sp0.
  case:(encode_multi_term_rec sp0 q) (Hq sp0) => /= qs0 sqsp0.
  case:(encode_multi_term_rec s p)=> /= ps sps.
  case:(encode_multi_term_rec sps q) (Hq sps)=> /= qss sqsps.
  case:(encode_multi_term_rec [::] q)=> /= q0 sq0.
  by move=> <- <-; rewrite catA; move->.
- rewrite /encode_multi_term /=; move=> p Hp q Hq s.
  case:(encode_multi_term_rec [::] p) (Hp s)=> /= p0 sp0.
  case:(encode_multi_term_rec sp0 q) (Hq sp0) => /= qs0 sqsp0.
  case:(encode_multi_term_rec s p)=> /= ps sps.
  case:(encode_multi_term_rec sps q) (Hq sps)=> /= qss sqsps.
  case:(encode_multi_term_rec [::] q)=> /= q0 sq0.
  by move=> <- <-; rewrite catA; move->.
Qed.

Lemma code_multi_term_recK : forall s ds m,
   decode_multi_term_rec 
   ((encode_multi_term_rec s m).2 ++ ds)
   (encode_multi_term_rec s m).1 = m.
Proof.
move=>s ds m; rewrite /decode_multi_term; elim:m s ds=> //=.
- by move=> x s ds; rewrite nth_cat size_rcons leqnn nth_rcons ltnn eqxx.
- by move=> x _ _; rewrite /mkVar pickleK_inv.
- move=> p Hp q Hq s ds.
  move:(Hp s ((snd (encode_multi_term q)++ds))).
  rewrite catA encode_multi_term_ds.
  case: (encode_multi_term_rec _ p)=> /= p' s'.
  move:(Hq s' ds).
  case: (encode_multi_term_rec _ q)=> /= q' s''.
  by move=> -> ->.
- move=> p Hp q Hq s ds.
  move:(Hp s ((snd (encode_multi_term q)++ds))).
  rewrite catA encode_multi_term_ds.
  case: (encode_multi_term_rec _ p)=> /= p' s'.
  move:(Hq s' ds).
  case: (encode_multi_term_rec _ q)=> /= q' s''.
  by move=> -> ->.
Qed.

Lemma code_multi_termK : cancel encode_multi_term decode_multi_term.
Proof.
rewrite /encode_multi_term /decode_multi_term=> m.
by have := (code_multi_term_recK [::] [::] m); rewrite cats0.
Qed.

Definition multi_term_choiceMixin := 
  @CanChoiceMixin _ multi_term _ _ code_multi_termK.
Canonical Structure multi_term_choiceType :=
  ChoiceType multi_term multi_term_choiceMixin.

Fixpoint nbvar_term t := 
  match t with
    | Coef _ => 0%N
    | Var x => (pickle x).+1
    | Sum u v => maxn (nbvar_term u) (nbvar_term v)
    | Prod u v => maxn (nbvar_term u) (nbvar_term v)
  end.

Fixpoint multi n := if n is n'.+1 then [ringType of {poly multi n'}] else R.

Fixpoint inject n m (p : multi n) {struct m} : multi (m + n) :=
  if m is m'.+1 return multi (m + n) then (inject m' p)%:P else p.

Lemma inject_inj : forall i m, injective (@inject i m).
Proof. by move=> i; elim=> //= m IHm p q; move/polyC_inj; move/IHm. Qed.

Lemma inject0 : forall i m, @inject i m 0 = 0.
Proof. by move=> i; elim=> //= m ->. Qed.

Lemma inject_eq0 : forall i m p, (@inject i m p == 0) = (p == 0).
Proof. by move=> i m p; rewrite -(inj_eq (@inject_inj i m)) inject0. Qed.

Lemma size_inject : forall i m p, size (@inject i m.+1 p) = (p != 0 : nat).
Proof. by move=> i m p; rewrite size_polyC inject_eq0. Qed.

Definition cast_multi i m n Emn : multi i -> multi n :=
  let: erefl in _ = n' := Emn return _ -> multi n' in inject m.

Definition multi_var n (i : 'I_n) := cast_multi (subnK (valP i)) 'X.

Notation "'X_ i" := (multi_var i).

Definition multiC n : R -> multi n := cast_multi (addn0 n).

Lemma inject_is_rmorphism : forall m n, rmorphism (@inject n m).
Proof. 
elim=> // m ihm n /=; have ->: inject m = RMorphism (ihm n) by [].
by rewrite -/(_ \o _); apply: rmorphismP.
Qed.
Canonical Structure inject_rmorphism m n := RMorphism (inject_is_rmorphism m n).

Lemma cast_multi_is_rmorphism :
  forall i m n Enm, rmorphism (@cast_multi i m n Enm).
Proof. by move=> i m n; case: n /; apply: rmorphismP. Qed.
Canonical Structure cast_multi_rmorphism i m n e := 
  RMorphism (@cast_multi_is_rmorphism i m n e).

Lemma multiC_morph : forall n, rmorphism (multiC n).
Proof.
move=> n; rewrite /multiC.
have ->: cast_multi (addn0 n) = [rmorphism of cast_multi (addn0 n)] by [].
exact: rmorphismP.
Qed.

Fixpoint interp n m : multi n :=
  match m with
    | Coef x => multiC n x
    | Var x => let i := pickle x in
      (if i < n as b return (i < n) = b -> multi n
        then fun iltn => cast_multi (subnK iltn) 'X_(Ordinal (leqnn i.+1))
        else fun _ => 0)   (refl_equal (i < n))
    | Sum p q => interp n p + interp n q
    | Prod p q => interp n p * interp n q
  end.

Lemma cast_multi_inj : forall n i i' n' (m1 m2 : multi n) 
  (p1: (i + n)%N=n') (p2: (i' + n)%N=n'),
  cast_multi p1 m1 == cast_multi p2 m2 = (m1 == m2).
Proof.
move=> n i i' n' m1 m2 p1 p2.
have:=p2. rewrite -{1}[n']p1. move/eqP. rewrite eqn_addr.
move/eqP. move=> /= Eii. move:p2. rewrite Eii=> p2 {Eii}.
have <-: p1 = p2; first exact: nat_irrelevance.
apply/idP/idP; last by move/eqP->.
move => Hm {p2}.
have : inject i m1 = inject i m2; last first.
   by move/eqP; rewrite (inj_eq (@inject_inj _ _)).
move: Hm; move:(p1); rewrite -p1 => p2. 
rewrite (_ : p2 = erefl (i+n)%N); last exact: nat_irrelevance. 
by move/eqP.
Qed.

Lemma Emj_Enk : forall i j k m n (Emj : (m + i)%N = j) 
  (Enk : (n + j)%N = k), (n + m + i)%N = k.
Proof.
by move => i j k m n <-; rewrite addnA.
Defined.

Lemma cast_multi_id : forall n (e : (0 + n)%N = n) m, cast_multi e m = m.
Proof. 
by move=> n e m; rewrite (_ : e = erefl _) //; apply: nat_irrelevance.
Qed.

Lemma cast_multiS : forall n i n' 
  (m: multi n) (p: (i+n)%N = n') (pS: ((i.+1)+n)%N = n'.+1),
  (cast_multi pS m) = (cast_multi p m)%:P.
Proof.
move=> n i n' m p pS.
move:(p) (pS); rewrite -p => pr pSr.
have ->: (pr = erefl (i + n)%N); first exact: nat_irrelevance.
by have ->: (pSr = erefl (i.+1 + n)%N); first exact: nat_irrelevance.
Qed.

Lemma injectnm_cast_multi : forall i m n p, 
  inject (n + m)%N p = 
  ((@cast_multi (m + i)%N n ((n + m) + i)%N (addnA _ _ _)) \o (inject m)) p.
Proof.
move=>i m n p; elim:n=>/=.
  move: (addnA 0%N m i); rewrite [(0+m)%N]add0n=> Hm.
  by have ->: (Hm = erefl (m + i)%N); first exact: nat_irrelevance.
move=> n ->; set inj := inject _ _ .
move:(addnA n m i) (addnA n.+1 m i).
change (n.+1 + m + i)%N with ((n + m + i).+1)%N.
change (addn_rec (addn_rec n m) i) with (n+m+i)%N.
rewrite -[(n+m+i)%N]addnA => pr pSr.
have ->: (pr = erefl (n + (m + i))%N); first exact: nat_irrelevance.
by have ->: (pSr = erefl (n.+1 + (m + i))%N); first exact: nat_irrelevance.
Qed.

Lemma cast_multi_add : forall i j k m n Emj Enk p,
  @cast_multi j n k Enk (@cast_multi i m j Emj p) =
  @cast_multi i (n + m)%N k (Emj_Enk Emj Enk) p.
Proof.
move=> i j k m n Emj Enk p.
move:(Emj) (Enk) (Emj_Enk Emj Enk).
rewrite -Enk -Emj.
change (addn_rec n (addn_rec m i)) with (n+m+i)%N.
rewrite {-1}[(n+(m+i))%N]addnA=> Emj0 Enk0 Enmi.
have ->: (Emj0 = erefl (m+i)%N); first exact: nat_irrelevance.
have ->: (Enmi = erefl (n+m+i)%N); first exact: nat_irrelevance.
rewrite /= injectnm_cast_multi /=.
by apply/eqP; rewrite cast_multi_inj.
Qed.


Lemma interp_cast_multi : forall n n' m (nltn' : n <= n'),
  nbvar_term m <= n -> interp n' m = cast_multi (subnK nltn') (interp n m).
Proof.
move=> n n' m nltn' dmltn; have dmltn' := (leq_trans dmltn nltn').
elim: m nltn' dmltn dmltn'.
- move=> a /= nltn' dmltn dmltn'. 
  apply/eqP; rewrite /multiC. 
  by rewrite cast_multi_add /= cast_multi_inj.
- move=> N /= nltn' dmltn dmltn'.
  move: (refl_equal (_ N < n')) (refl_equal (_ N < n)).
  rewrite {2 3}[_ N < n]dmltn {2 3}[_ N < n']dmltn' => Nn' Nn.
  by apply/eqP; rewrite cast_multi_add cast_multi_inj.
- move=> m1 Hm1 m2 Hm2 nltn' /=; rewrite !leq_maxl.
  move/andP=>[dm1n dm1n']; move/andP=>[dm2n dm2n'].
  rewrite (Hm1 nltn') // (Hm2 nltn') //.
  by rewrite rmorphD.
- move=> m1 Hm1 m2 Hm2 nltn' /=; rewrite !leq_maxl.
  move/andP=>[dm1n dm1n']; move/andP=>[dm2n dm2n'].
  rewrite (Hm1 nltn') // (Hm2 nltn') //.
  by rewrite rmorphM.
Qed.

(* Fixpoint reify n (m : multi n) :=  *)
(*   match n return multi n -> multi_term with *)
(*     | 0%N => fun m => Coef m *)
(*     | n'.+1 => fun m => *)
(*       let: Polynomial s _:= m in *)
(*         foldr (fun c p => Sum (reify c) (Prod (mkVar n') p)) (Coef 0) s *)
(*   end m. *)

(* Lemma nbvar_term_reify : forall n (m : multi n), nbvar_term (reify m) <= n. *)
(* Proof. *)
(* elim=> // n Hn /= [p]; elim: p => //; set f := foldr _ _. *)
(* move=> a s /= Hs ls; rewrite !leq_maxl (leqW (Hn _)). *)
(* rewrite Hs ?andbT; last by case: s ls {Hs}; rewrite //= oner_eq0. *)
(* rewrite /mkVar; case hx: pickle_inv => [x|] //=. *)
(* by have ->: pickle x = n by rewrite -(@pickle_invK X n) hx. *)
(* Qed. *)

(* Lemma interp_reify : forall n (m : multi n), interp n (reify m) = m. *)
(* Proof. *)
(* elim=> [|n Hn] m /=; first by rewrite /multiC cast_multi_id. *)
(* elim: m => p i. *)
(* apply: val_inj=> /=. *)
(* set f := foldr _ _. *)
(* elim: p i=> [_|]. *)
(*   by rewrite /= [_ 0]rmorph0 val_insubd /= eqxx. *)
(* move=> t s Hs. *)
(* rewrite [f _]/= [interp _ _]/=. *)
(* rewrite (interp_cast_multi (leqnSn n)); last by rewrite nbvar_term_reify. *)
(* rewrite [last _ _]/= => ls. *)
(* move: (subnK (leqnSn n)); rewrite subSnn => En. *)
(* have ->: En = (erefl (n.+1)); first exact: nat_irrelevance. *)
(* rewrite [cast_multi _ _]/=. *)
(* rewrite Hn. *)
(* move: (refl_equal (n < n.+1)). *)
(* rewrite /mkVar. *)
(* case:  *)
(* rewrite {2}[n < n.+1]ltnSn=> e. *)
(* rewrite /multi_var. *)
(* move:(subnK _) (subnK _).  *)
(* rewrite [val _]/= subnn=> subnK subnK'. *)
(* have ->: subnK = erefl (n.+1); first exact: nat_irrelevance. *)
(* have ->: subnK' = erefl (n.+1); first exact: nat_irrelevance. *)
(* rewrite ![cast_multi _ _]/= addrC mulrC -poly_cons_def polyseq_cons Hs. *)
(*   move=> {Hs En e subnK' subnK}. *)
(*   case:s ls; last by move=> a s /=. *)
(*   rewrite /=. *)
(*   move=> tn0. *)
(*   by rewrite val_insubd tn0. *)
(* move=> {Hs En e subnK' subnK}. *)
(* case:s ls; first by rewrite GRing.oner_neq0. *)
(* by move=> a s ->. *)
(* Qed. *)

(* Lemma interp_reify_cast_multi : forall n n' (ltnn' : n <= n') (m : multi R n) , *)
(*   interp n' (reify m) = cast_multi (subnK ltnn') m. *)
(* Proof. *)
(* move=> n n' ltnn' m. *)
(* rewrite (interp_cast_multi ltnn'); last by rewrite nbvar_term_reify.  *)
(* by apply/eqP; rewrite cast_multi_inj interp_reify. *)
(* Qed. *)
  
Definition equivm m1 m2 := 
  let n1 := nbvar_term m1 in
    let n2 := nbvar_term m2 in
      interp (maxn n1 n2) m1 == interp (maxn n1 n2) m2.

Lemma interp_gtn : forall n m1 m2, 
  maxn (nbvar_term m1) (nbvar_term m2) <= n -> 
  equivm m1 m2 = (interp n m1 == interp n m2).
Proof.
move=> n m1 m2 p.
rewrite !(interp_cast_multi p).
- by rewrite cast_multi_inj.
- by rewrite leq_maxr leqnn orbT.
- by rewrite leq_maxr leqnn.
Qed.

Lemma equivm_refl : reflexive equivm.
Proof. by move=> x; rewrite /equivm. Qed.

Lemma equivm_sym : symmetric equivm.
Proof. by move=> x y; rewrite /equivm eq_sym maxnC. Qed.

Lemma equivm_trans : transitive equivm.
Proof.
move=> x y z.
rewrite !(@interp_gtn (maxn (maxn (nbvar_term x) (nbvar_term y)) (nbvar_term z))).
- by move/eqP->; move/eqP->.
- by rewrite -maxnA leq_maxr leqnn orbT.
- by rewrite maxnAC leq_maxr leqnn.
- by rewrite maxnC leq_maxr leqnn.
Qed.

Canonical Structure equivm_equivRel := EquivRel equivm_refl equivm_sym equivm_trans.

Definition multinom := [m multi_term %/ equivm ].
Canonical Structure multinom_quotType := [quotType of multinom].
Canonical Structure multinom_eqType := [eqType of multinom].
Canonical Structure multinom_choiceType := [choiceType of multinom].

Local Notation zerom := (\pi_multinom (Coef 0)).
Local Notation onem := (\pi_multinom (Coef 1)).
Local Notation cstm c := (\pi_multinom (Coef c)).
Local Notation varm n := (\pi_multinom (Var n)).

Lemma addm_compat : mop2_spec Sum multinom.
Proof.
move=> x y; apply/equivP=> /=; set x' := repr _; set y' := repr _.
rewrite (@interp_gtn (nbvar_term (Sum (Sum x y) (Sum x' y')))) /=.
  apply/eqP; congr (_ + _); apply/eqP; do[
  rewrite -interp_gtn; do ?[by apply/equivP; rewrite reprK];
  by rewrite !(leq_maxl, leq_maxr, leqnn, orbT)].
by rewrite maxnC.
Qed.
Local Notation addm := (mop2 addm_compat).

Lemma oppm_compat : mop1_spec (Prod (Coef (-1))) multinom.
Proof.
move=> x; apply/equivP; rewrite /= /equivm /= !max0n; apply/eqP; congr (_ * _).
by apply/eqP; rewrite -interp_gtn //; apply/equivP; rewrite reprK.
Qed.
Local Notation oppm := (mop1 oppm_compat).


Lemma mulm_compat : mop2_spec Prod multinom.
Proof.
move=> x y; apply/equivP=> /=; set x' := repr _; set y' := repr _.
rewrite (@interp_gtn (nbvar_term (Sum (Sum x y) (Sum x' y')))) /=.
  apply/eqP; congr (_ * _); apply/eqP; do[
  rewrite -interp_gtn; do ?[by apply/equivP; rewrite reprK];
  by rewrite !(leq_maxl, leq_maxr, leqnn, orbT)].
by rewrite maxnC.
Qed.
Local Notation mulm := (mop2 mulm_compat).

Lemma addmA : associative addm.
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z.
by rewrite !mopP; apply/equivP; rewrite /= /equivm /= addrA.
Qed.

Lemma addmC : commutative addm.
Proof.
elim/quotW=> x; elim/quotW=> y.
by rewrite !mopP; apply/equivP; rewrite /= /equivm /= addrC.
Qed.

Lemma add0m : left_id zerom addm.
Proof.
elim/quotW=> x; rewrite !mopP; apply/equivP; rewrite /= /equivm /=.
by rewrite [_ 0]rmorph0 add0r.
Qed.

Lemma addmN : left_inverse zerom oppm addm.
Proof.
elim/quotW=> x; rewrite !mopP; apply/equivP; rewrite /= /equivm /=.
by rewrite ![_ 0]rmorph0 [_ (- _)]rmorphN rmorph1 mulN1r addNr.
Qed.

Definition multinom_zmodMixin :=  ZmodMixin addmA addmC add0m addmN.
Canonical Structure multinom_zmodType := ZmodType multinom multinom_zmodMixin.

Lemma mulmA : associative mulm.
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z.
by rewrite !mopP; apply/equivP; rewrite /= /equivm /= mulrA.
Qed.

(* Lemma mulmC : commutative mulm. *)
(* Proof. *)
(* elim/quotW=> x; elim/quotW=> y. *)
(* rewrite !mopP; apply/equivP; rewrite /= /equivm /=. *)
(* rewrite mulrC. *)
(* elim/quotW=> x; elim/quotW=> y. *)
(* rewrite !qTE; apply/eqP; rewrite -equivP equivmP. *)
(* by rewrite /equivm /= mulrC. *)
(* Qed. *)

(* Lemma mul1m : left_id onem mulm. *)
(* Proof. *)
(* Proof. *)
(* elim/quotW=> x. *)
(* rewrite !qTE; apply/eqP; rewrite -equivP equivmP. *)
(* by rewrite /equivm /= (ringM_1 (multiC_morph _ _)) mul1r. *)
(* Qed. *)

(* Lemma mulm_addl : left_distributive mulm addm. *)
(* Proof. *)
(* elim/quotW=> x; elim/quotW=> y; elim/quotW=> z. *)
(* rewrite !qTE; apply/eqP; rewrite -equivP equivmP. *)
(* by rewrite /equivm /= mulrDl. *)
(* Qed. *)

(* Lemma nonzero1m : onem != zerom. *)
(* Proof. *)
(* rewrite -equivP equivmP /equivm /=. *)
(* rewrite (ringM_0 (multiC_morph _ _)). *)
(* rewrite (ringM_1 (multiC_morph _ _)). *)
(* by rewrite GRing.oner_neq0. *)
(* Qed. *)


(* Definition multinom_comRingMixin :=  *)
(*   ComRingMixin mulmA mulmC mul1m mulm_addl nonzero1m. *)
(* Canonical Structure  multinom_Ring :=  *)
(*   Eval hnf in RingType multinom multinom_comRingMixin. *)
(* Canonical Structure multinom_comRing := Eval hnf in ComRingType multinom mulmC. *)

(* Lemma unit_interp : forall n m, (nbvar_term m) <= n -> *)
(*   GRing.unit (interp (nbvar_term m) m) = GRing.unit (interp n m). *)
(* Proof. *)
(* move=> n m dm; apply/idP/idP. *)
(*   move/(ringM_unit (cast_multiM _ (subnK dm))). *)
(*   by rewrite -interp_cast_multi. *)
(* elim:n dm; first by rewrite leqn0; move/eqP->. *)
(* move=> n Hn dmSn uiSn. *)
(* case:(ltngtP (nbvar_term m) n.+1); last by move->. *)
(*   rewrite ltnS=> i; apply:Hn=> {dmSn} //. *)
(*   move:uiSn.  *)
(*   have nltSn: n <= 1 + n; first by rewrite leqnSn. *)
(*   rewrite (interp_cast_multi nltSn i). *)
(*   move: (subnK nltSn); rewrite -[n.+1]/(1+n)%N. *)
(*   rewrite {2 3 5}(_ : (1 + n = 1 + n - n + n)%N) ?subnK // => EN.  *)
(*   have ->: EN = (erefl (1 + n - n + n)%N); first exact: nat_irrelevance. *)
(*   rewrite /= [(n.+1-n)%N]subSnn -[GRing.unit _]/(poly_unit _). *)
(*   by case/andP; rewrite coefC. *)
(* by move/(leq_ltn_trans dmSn); rewrite ltnn. *)
(* Qed. *)

(* Lemma unitm_compat : \compat1_multinom _ *)
(*   (fun m => GRing.unit (interp (nbvar_term m) m)). *)
(* Proof. *)
(* apply:compat1E=> x y. *)
(* rewrite equivmP (@interp_gtn (maxn (nbvar_term x) (nbvar_term y))); last first. *)
(*   by rewrite leqnn. *)
(* move/eqP=> ixy. *)
(* have xltxy : (nbvar_term x) <= (maxn (nbvar_term x) (nbvar_term y)). *)
(*    by rewrite leq_maxr leqnn. *)
(* have yltxy : (nbvar_term y) <= (maxn (nbvar_term x) (nbvar_term y)). *)
(*    by rewrite leq_maxr leqnn orbT. *)
(* by apply/idP/idP; rewrite (unit_interp xltxy) (unit_interp yltxy) ixy. *)
(* Qed. *)
(* Local Notation unitm := [pred m : multinom | qT_op1 unitm_compat m ]. *)

(* Lemma invm_compat : \compat1_multinom _ *)
(*   (fun m => \pi_multinom (reify ((interp (nbvar_term m) m)^-1))). *)
(* Proof. *)
(* apply:compat1Epi=> x y; rewrite !equivmP. *)
(* set ix := reify _; set iy := reify _. *)
(* rewrite {1}/equivm /=. *)
(* have ixyleqxy : maxn (nbvar_term ix) (nbvar_term iy)  *)
(*   <= maxn (nbvar_term x) (nbvar_term y). *)
(*   by rewrite leq_maxl !leq_maxr !nbvar_term_reify orbT. *)
(* rewrite (interp_gtn ixyleqxy). *)
(* have xleqxy : nbvar_term x <= maxn (nbvar_term x) (nbvar_term y). *)
(*   by rewrite leq_maxr leqnn. *)
(* have yleqxy : nbvar_term y <= maxn (nbvar_term x) (nbvar_term y). *)
(*   by rewrite leq_maxr leqnn orbT. *)
(* rewrite (interp_reify_cast_multi xleqxy).  *)
(* rewrite (interp_reify_cast_multi yleqxy). *)
(* move/eqP=> exy. *)
(* case ux: (GRing.unit (interp (nbvar_term x) x)); *)
(*     move:(ux); rewrite (unit_interp xleqxy) exy -(unit_interp yleqxy) => uy. *)
(*   rewrite !(ringM_inv (cast_multiM _ _)) //.  *)
(*   by rewrite -!interp_cast_multi // exy. *)
(* by rewrite !invr_out ?ux ?uy // -!interp_cast_multi // exy. *)
(* Qed. *)
(* Local Notation invm := (qT_op1 invm_compat). *)

(* Definition interpretable n := [pred m : multi_term | nbvar_term m <= n ]. *)

(* Lemma mulVm : {in unitm, left_inverse onem invm mulm}. *)
(* Proof. *)
(* elim/quotW=> m; rewrite !inE. *)
(* rewrite !qTE=> um; apply/eqP; rewrite -equivP equivmP. *)
(* set im :=  reify _. *)
(* rewrite /equivm /= maxn0. *)
(* have mlimm : nbvar_term m <= maxn (nbvar_term im) (nbvar_term m). *)
(*   by rewrite leq_maxr leqnn orbT. *)
(* rewrite (interp_reify_cast_multi mlimm). *)
(* rewrite (ringM_inv (cast_multiM _ _)) ?um //. *)
(* rewrite -interp_cast_multi //. *)
(* rewrite (ringM_1 (multiC_morph _ _)). *)
(* rewrite mulVr //. *)
(* by rewrite -(unit_interp mlimm). *)
(* Qed. *)


(* Lemma unitmPl : forall x y, mulm y x = onem -> unitm x. *)
(* Proof. *)
(* elim/quotW=> x; elim/quotW=> y; rewrite inE !qTE. *)
(* move/eqP; rewrite -!equivP !equivmP /=. *)
(* rewrite /equivm /= maxn0. *)
(* rewrite (ringM_1 (multiC_morph _ _)). *)
(* move/eqP=> ixiy1. *)
(* rewrite (unit_interp (_ : nbvar_term x <= maxn (nbvar_term y) (nbvar_term x))). *)
(*   apply/unitrP. *)
(*   exists (interp (maxn (nbvar_term y) (nbvar_term x)) y). *)
(*   by rewrite ixiy1 mulrC ixiy1. *)
(* by rewrite leq_maxr leqnn orbT. *)
(* Qed. *)


(* Lemma  invm_out : {in predC unitm, invm =1 id}. *)
(* Proof. *)
(* elim/quotW=> x; rewrite !inE !qTE=> nux. *)
(* rewrite invr_out //. *)
(* apply/eqP; rewrite -equivP equivmP /equivm /=. *)
(* set rx := reify _. *)
(* have xltrxx: nbvar_term x <= (maxn (nbvar_term rx) (nbvar_term x)). *)
(*   by rewrite leq_maxr leqnn orbT. *)
(* rewrite (interp_reify_cast_multi xltrxx). *)
(* by rewrite -interp_cast_multi. *)
(* Qed. *)

(* Definition multinom_comUnitRingMixin :=  ComUnitRingMixin mulVm unitmPl invm_out. *)
(* Canonical Structure multinom_unitRing :=  *)
(*   Eval hnf in UnitRingType multinom multinom_comUnitRingMixin. *)


(* Lemma idomain_axiomm : forall x y, *)
(*   (mulm x y = zerom -> (x == zerom) || (y == zerom)). *)
(* Proof. *)
(* elim/quotW=> x; elim/quotW=> y; rewrite !qTE. *)
(* move/eqP; rewrite -!equivP equivmP /equivm {1}[_ == _]/=. *)
(* rewrite maxn0 (ringM_0 (multiC_morph _ _)). *)
(* rewrite mulf_eq0. *)
(* case/orP. *)
(*   rewrite -!equivP equivmP. *)
(*   rewrite (@interp_gtn (maxn (nbvar_term x) (nbvar_term y))). *)
(*     by move/eqP->=> /=; rewrite (ringM_0 (multiC_morph _ _)) eqxx. *)
(*   by rewrite maxn0 leq_maxr leqnn. *)
(* move/eqP=> y0. *)
(* apply/orP; right. *)
(* rewrite -!equivP equivmP. *)
(* rewrite (@interp_gtn (maxn (nbvar_term x) (nbvar_term y))). *)
(*   by rewrite y0 /= (ringM_0 (multiC_morph _ _)) eqxx. *)
(* by rewrite maxn0 leq_maxr leqnn orbT. *)
(* Qed. *)

(* (* (* Why can't we have simply : *) *) *)
(* (* Canonical Structure multinom_iDomain := *) *)
(* (*   Eval hnf in IdomainType multi idomain_axiomm. *) *)

(* Canonical Structure multinom_iDomain :=  *)
(*   Eval hnf in IdomainType [comUnitRingType of multinom] idomain_axiomm. *)

End MultinomialTerm.
End MultinomialTerm.




