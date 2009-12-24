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
  EqType _ multi_skel_eqMixin.
Canonical Structure multi_skel_choiceType := 
  ChoiceType _ multi_skel_choiceMixin.
Canonical Structure multi_skel_countType := 
  CountType _ multi_skel_countMixin.

Fixpoint encode_multi_term_rec (s:seq R) (m:multi_term):=
  match m with
    | Coef x => ((CoefS (size s)), (rcons s x))
    | Var n => ((VarS n), s)
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

Fixpoint decode_multi_term_rec (s:seq R) (m : multi_skel) :=
    match m with
    | CoefS i => Coef (nth (0:R) s i)
    | VarS n => Var n
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
  ChoiceType _ multi_term_choiceMixin.

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
  deg_term m <= n -> interp n' m = cast_multi (subnK nltn') (interp n m).
Proof.
move=> n n' m nltn' dmltn; have dmltn' := (leq_trans dmltn nltn').
elim: m nltn' dmltn dmltn'.
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
     rewrite {2 4 5}dmltn; exists dmltn. 
     rewrite {2 4 5}dmltn'; exists dmltn'.
     rewrite cast_multi_add.
     by apply/eqP; rewrite cast_multi_inj.
   move=> [Nn] [Nn'].
   have ->: (Nn = (erefl (N<n))); first exact: bool_irrelevance.
   by have ->: (Nn' = (erefl (N<n'))); first exact: bool_irrelevance.
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
- by rewrite leq_maxr leqnn.
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

Definition canonm x := @Multinom (canon x) (canon_axiom x).

Lemma canonm_valK : forall x : multinom, canonm (val x) = x.
Proof.
by move=> [x /=]; rewrite /axiom=> Px; apply:val_inj=>/=; rewrite (eqP Px).
Qed.

Canonical Structure multinom_quotType := Eval hnf in
  @QuotType _ multinom [eta val] [eta canonm] canonm_valK.


Definition multiW := @quotW _ multinom_quotType.
Definition multiP := @quotP _ multinom_quotType.
Definition inRatP := insubP [subType of multinom].

Notation zerom := (\pi_multinom (Coef 0)).
Notation onem := (\pi_multinom (Coef 1)).
Notation cstm c := (\pi_multinom (Coef c)).
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
apply:compat2Epi=> x y x' y'; rewrite !equivmP /=.
rewrite !(@interp_gtn (maxn (maxn (deg_term x) (deg_term y))
  (maxn (deg_term x') (deg_term y')))) //=.
- by move/eqP->; move/eqP->.
- by rewrite !maxnA; rewrite [maxn (maxn (deg_term _) _) _]maxnAC.
- by rewrite leq_maxr leqnn orbT.
- by rewrite leq_maxr leqnn.
Qed.
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
apply:compat2Epi=> x y x' y'; rewrite !equivmP /=.
rewrite !(@interp_gtn (maxn (maxn (deg_term x) (deg_term y))
  (maxn (deg_term x') (deg_term y')))) //=.
- by move/eqP->; move/eqP->.
- by rewrite !maxnA; rewrite [maxn (maxn (deg_term _) _) _]maxnAC.
- by rewrite leq_maxr leqnn orbT.
- by rewrite leq_maxr leqnn.
Qed.
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

Definition multinom_zmodMixin :=  ZmodMixin addmA addmC add0m addmN.
Canonical Structure multinom_zmodType := Eval hnf in ZmodType 
  multinom multinom_zmodMixin.


Lemma mulmA : associative mulm.
Proof.
elim/multiW=> x; elim/multiW=> y; elim/multiW=> z.
rewrite !qTE; apply/eqP; rewrite -equivP equivmP.
by rewrite /equivm /= mulrA.
Qed.

Lemma mulmC : commutative mulm.
Proof.
elim/multiW=> x; elim/multiW=> y.
rewrite !qTE; apply/eqP; rewrite -equivP equivmP.
by rewrite /equivm /= mulrC.
Qed.


Lemma mul1m : left_id onem mulm.
Proof.
Proof.
elim/multiW=> x.
rewrite !qTE; apply/eqP; rewrite -equivP equivmP.
by rewrite /equivm /= (ringM_1 (multiC_morph _ _)) mul1r.
Qed.

Lemma mulm_addl : left_distributive mulm addm.
Proof.
elim/multiW=> x; elim/multiW=> y; elim/multiW=> z.
rewrite !qTE; apply/eqP; rewrite -equivP equivmP.
by rewrite /equivm /= mulr_addl.
Qed.

Lemma nonzero1m : onem != zerom.
Proof.
rewrite -equivP equivmP /equivm /=.
rewrite (ringM_0 (multiC_morph _ _)).
rewrite (ringM_1 (multiC_morph _ _)).
by rewrite GRing.nonzero1r.
Qed.


Definition multinom_comRingMixin := ComRingMixin mulmA mulmC mul1m mulm_addl nonzero1m.
Canonical Structure  multinom_Ring := 
  Eval hnf in RingType multinom multinom_comRingMixin.
Canonical Structure multinom_comRing := Eval hnf in ComRingType multinom mulmC.

Lemma unit_interp : forall n m, (deg_term m) <= n ->
  GRing.unit (interp (deg_term m) m) = GRing.unit (interp n m).
Proof.
move=> n m dm; apply/idP/idP.
  move/(ringM_unit (cast_multiM _ (subnK dm))).
  by rewrite -interp_cast_multi.
elim:n dm; first by rewrite leqn0; move/eqP->.
move=> n Hn dmSn uiSn.
case:(ltngtP (deg_term m) n.+1); last by move->.
  rewrite ltnS=> i; apply:Hn=> {dmSn} //.
  move:uiSn. 
  have nltSn: n <= 1 + n; first by rewrite leqnSn.
  rewrite (interp_cast_multi nltSn i) /=.
  pose f N := forall (EN : ((n.+1 - n)+ n = N)%N),
    GRing.unit (cast_multi EN (interp n m)) -> GRing.unit (interp n m).
  have: f  ((n.+1 - n) + n)%N.
    move=> EN.
    have ->: EN = (erefl ((n.+1 - n) + n)%N); first exact: nat_irrelevance.
    rewrite /=. 
    pose g N := GRing.unit (inject N (interp n m)) -> GRing.unit (interp n m).
    have: g (n.+1 - n)%N; last done.
    by rewrite subSnn /=; case/andP; rewrite coefC eqxx.
  rewrite subnK -add1n ?leq_addl // => fN.
  exact: (fN (subnK nltSn)).
by move/(leq_ltn_trans dmSn); rewrite ltnn.
Qed.

Lemma unitm_compat : \compat1_multinom _
  (fun m => GRing.unit (interp (deg_term m) m)).
Proof.
apply:compat1E=> x y.
rewrite equivmP (@interp_gtn (maxn (deg_term x) (deg_term y))); last first.
  by rewrite leqnn.
move/eqP=> ixy.
have xltxy : (deg_term x) <= (maxn (deg_term x) (deg_term y)).
   by rewrite leq_maxr leqnn.
have yltxy : (deg_term y) <= (maxn (deg_term x) (deg_term y)).
   by rewrite leq_maxr leqnn orbT.
by apply/idP/idP; rewrite (unit_interp xltxy) (unit_interp yltxy) ixy.
Qed.
Notation unitm := (qT_op1 unitm_compat).



Lemma invm_compat : \compat1_multinom _
  (fun m => \pi_multinom ((interp (deg_term m) m)^-1)).

Lemma mulVm : {in unitm, left_inverse onem invm mulm}.
Proof.
elim/multiW=> m; rewrite in_simpl.
case/orP; move/eqP->; rewrite /invm !qTE; 
apply/eqP; rewrite equivP equivmP /equivm /=.
  by rewrite (ringM_1 (multiC_morph _ _)) mulr1.
rewrite (ringM_opp (multiC_morph _ _)).
by rewrite (ringM_1 (multiC_morph _ _)) mulrNN mulr1.
Qed.


Lemma unitmPl : forall x y, mulm y x = onem -> unitm x.
Proof.
elim/multiW=> x; elim/multiW=> y; rewrite !qTE simpl_predE.
move/eqP; rewrite -!equivP !equivmP /=.
rewrite !(@interp_gtn (maxn (deg_term x) (deg_term y))) /=.
rewrite (ringM_opp (multiC_morph _ _)).
rewrite (ringM_1 (multiC_morph _ _)).
rewrite unitr_mul.
rewrite 
 
apply/orP; left.
rewrite equivmP.
move<-

Set Printing All.

 rewrite /pi_of !equivP !equivmP. rewrute -equivP. /equivm /=.
Qed.

Lemma  invm_out : {in predC unitm, invm =1 id}.
Proof.
Qed.

Definition multinom_comUnitRingMixin :=  ComUnitRingMixin mulVm unitmPl invm_out.
Canonical Structure multinom_comUnitRing := 
  Eval hnf in ComUnitRingType multinom_comUnitRingMixin.

Lemma idomain_axiomm : forall x y,
  (mulm x y = zerom -> (x == zerom) || (y == zerom)).
Proof.
Qed.

Canonical Structure multinom_iDomain := Eval hnf in IdomainType idomain_axiomm.

End MultinomialTerm.




