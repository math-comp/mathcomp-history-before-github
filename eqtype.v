(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import ssrfun.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Generic definitions and lemmas for datatypes with reflected (decidable) *)
(* equality. The structure includes the actual boolean predicate, not just *)
(* the decision procedure. A canonical structure for the booleans is given *)
(* here, and one will be provided for the integers in ssrnat.v.            *)
(*   Congruence properties of injective functions wrt reflected equality   *)
(* are established.                                                        *)
(*   The main technical result is the construction of the subdomain        *)
(* associated with a pred.                                                 *)
(*   Syntactic sugar is provided for the equality predicate and its        *)
(* reflection property.                                                    *)

Definition reflect_eq T eq :=
  forall x y : T, reflect (x = y) (eq x y).

Module EqType.

Structure mixin (T : Type) : Type := Mixin { eqd : rel T; _ : reflect_eq eqd }.
Structure class : Type := Class { sort :> Type; _ : mixin sort }.
Coercion mixin_of T := let: Class _ m := T return mixin T in m.

End EqType.

Delimit Scope eq_scope with EQ.
Open Scope eq_scope.

Notation eqType := EqType.class.
Notation EqClass := EqType.Class.
Notation EqMixin := EqType.Mixin.

Definition mkEqType T e eP := EqClass (@EqMixin T e eP).


Notation "[ 'eqType' 'of' T ]" :=
  (match [is T <: eqType] as s return {type of EqClass for s} -> _ with
  | EqClass _ m => fun k => k m end
  (@EqClass T)) (at level 0, only parsing) : form_scope.

Section EqOps.

Variable T : eqType.

Definition eqd : rel T := T.(EqType.eqd).

Lemma eqE : forall x, eqd x = T.(EqType.eqd) x. Proof. by []. Qed.

Lemma eqP : reflect_eq eqd. Proof. by rewrite /eqd; case: T => ? []. Qed.

End EqOps.

Implicit Arguments eqP [T x y].

Notation "x == y" := (eqd x y)
  (at level 70, no associativity) : bool_scope.
Notation "x == y :> T" := ((x : T) == (y : T))
  (at level 70, y at next level) : bool_scope.
Notation "x != y" := (~~ (x == y))
  (at level 70, no associativity) : bool_scope.
Notation "x != y :> T" := (~~ (x == y :> T))
  (at level 70, y at next level) : bool_scope.
Notation "x =P y" := (eqP : reflect (x = y) (x == y))
  (at level 70, no associativity) : eq_scope.
Notation "x =P y :> T" := (eqP : reflect (x = y :> T) (x == y :> T))
  (at level 70, y at next level, no associativity) : eq_scope.

Prenex Implicits eqd eqP.

Lemma eq_refl : forall (T : eqType) (x : T), x == x.
Proof. by move=> T x; apply/eqP. Qed.
Notation eqxx := eq_refl.

Lemma eq_sym : forall (T : eqType) (x y : T), (x == y) = (y == x).
Proof. by move=> T x y; apply/eqP/eqP. Qed.

Hint Resolve eq_refl eq_sym.

Theorem eq_irrelevance (T : eqType) (x y : T) (e1 e2 : x = y) : e1 = e2.
Proof.
move=> T x y e1 e2; pose join (e : x = _) := etrans (esym e).
pose proj z e := if x =P z is Reflect_true e0 then e0 else e.
suff{e1 e2}: injective (proj y) by apply; rewrite /proj; case: eqP.
apply: can_inj (join x y (proj x (erefl x))) _ => e; case: y / e.
by case: {-1}x / (proj x _).
Qed.

Corollary eq_axiomK : forall (T : eqType) (x : T) (e : x = x), e = erefl x.
Proof. move=> *; exact: eq_irrelevance. Qed.

(* We use the module system to circumvent a silly limitation that  *)
(* forbids using the same constant to coerce to different targets. *)
Module Type EqTypePredSig.
Parameter sort : eqType -> predArgType.
End EqTypePredSig.
Module MakeEqTypePred (eqmod : EqTypePredSig).
Coercion eqmod.sort : eqType >-> predArgType.
End MakeEqTypePred.
Module EqTypePred := MakeEqTypePred EqType.

(* Coercion eqTypeT (T : eqType) : simpl_pred T := predT. *)

(* Comparison for booleans. *)

Lemma eqbP : reflect_eq eqb.
Proof. by do 2 case; constructor. Qed.

Canonical Structure bool_eqMixin := EqMixin eqbP.
Canonical Structure bool_eqType := EqClass bool_eqMixin.

Lemma eqbE : eqb = eqd. Proof. done. Qed.

Lemma bool_irrelevance : forall (x y : bool) (E E' : x = y), E = E'.
Proof. exact: eq_irrelevance. Qed.

Lemma negb_add : forall b1 b2, ~~ (b1 (+) b2) = (b1 == b2).
Proof. by do 2!case. Qed.

Lemma negb_eqb : forall b1 b2, (b1 != b2) = b1 (+) b2.
Proof. by do 2!case. Qed.

(* Equality-based predicates.       *)

Notation xpred1 := (fun a1 x => x == a1).
Notation xpred2 := (fun a1 a2 x => (x == a1) || (x == a2)).
Notation xpred3 := (fun a1 a2 a3 x => [|| x == a1, x == a2 | x == a3]).
Notation xpred4 :=
   (fun a1 a2 a3 a4 x => [|| x == a1, x == a2, x == a3 | x == a4]).
Notation xpredU1 := (fun a1 (p : pred _) x => (x == a1) || p x).
Notation xpredC1 := (fun a1 x => x != a1).
Notation xpredD1 := (fun (p : pred _) a1 x => (x != a1) && p x).

Section EqPred.

Variable T : eqType.

Definition pred1 (a1 : T) := SimplPred (xpred1 a1).
Definition pred2 (a1 a2 : T) := SimplPred (xpred2 a1 a2).
Definition pred3 (a1 a2 a3 : T) := SimplPred (xpred3 a1 a2 a3).
Definition pred4 (a1 a2 a3 a4 : T) := SimplPred (xpred4 a1 a2 a3 a4).
Definition predU1 (a1 : T) p := SimplPred (xpredU1 a1 p).
Definition predC1 (a1 : T) := SimplPred (xpredC1 a1).
Definition predD1 p (a1 : T) := SimplPred (xpredD1 p a1).

Lemma pred1E : pred1 =2 eqd. Proof. move=> x y; exact: eq_sym. Qed.

Variables (x y : T) (b : bool).

Lemma predU1P : reflect (x = y \/ b) ((x == y) || b).
Proof. apply: (iffP orP) => [] []; by [right | move/eqP; left]. Qed.

Lemma predD1P : reflect (x <> y /\ b) ((x != y) && b).
Proof. by apply: (iffP andP)=> [] [] //; move/eqP. Qed.

Lemma predU1l : x = y -> (x == y) || b.
Proof. by move->; rewrite eqxx. Qed.

Lemma predU1r : b -> (x == y) || b.
Proof. by move->; rewrite orbT. Qed.

End EqPred.

Implicit Arguments predU1P [T x y b].
Prenex Implicits pred1 pred2 pred3 pred4 predU1 predC1 predD1 predU1P.

Notation "[ 'predU1' x & A ]" := (predU1 x [mem A])
  (at level 0, format "[ 'predU1'  x  &  A ]") : fun_scope.
Notation "[ 'predD1' A & x ]" := (predD1 [mem A] x)
  (at level 0, format "[ 'predD1'  A  &  x ]") : fun_scope.

(* Lemmas for reflected equality and functions.   *)

Section EqFun.

Lemma inj_eq : forall (aT rT : eqType) (h : aT -> rT),
  injective h -> forall x y, (h x == h y) = (x == y).
Proof. by move=> T T' h *; apply/eqP/eqP => *; [ auto | congr h ]. Qed.

Section Endo.

Variables (T : eqType) (f g : T -> T).

Definition frel := [rel x y : T | f x == y].

Lemma can_eq : cancel f g -> forall x y, (f x == f y) = (x == y).
Proof. move/can_inj; exact: inj_eq. Qed.

Lemma bij_eq : bijective f -> forall x y, (f x == f y) = (x == y).
Proof. move/bij_inj; apply: inj_eq. Qed.

Lemma can2_eq :
  cancel f g -> cancel g f -> forall x y, (f x == y) = (x == g y).
Proof. by move=> Ef Eg x y; rewrite -{1}[y]Eg; exact: can_eq. Qed.

Lemma inv_eq : involutive f -> forall x y, (f x == y) = (x == f y).
Proof. by move=> Ef x y; rewrite -(inj_eq (inv_inj Ef)) Ef. Qed.

End Endo.

Variable aT : Type.

(* The invariant of an function f wrt a projection k is the pred of points *)
(* that have the same projection as their image.                           *)

Definition invariant (rT : eqType) f (k : aT -> rT) :=
  [pred x | k (f x) == k x].

Variables (rT1 rT2 : eqType) (f : aT -> aT) (h : rT1 -> rT2) (k : aT -> rT1).

(* pouquoi Type -> Type demande de reecrire eqxx??? *)
Lemma invariant_comp : subpred (invariant f k) (invariant f (h \o k)).
Proof.  by move=> x eq_kfx; rewrite /comp /= (eqP eq_kfx) eqxx. Qed.
 
Lemma invariant_inj : injective h -> invariant f (h \o k) =1 invariant f k.
Proof. move=> inj_h x; exact: (inj_eq inj_h). Qed.

End EqFun.

Prenex Implicits frel.

Section FunWith.

Variables (aT : eqType) (rT : Type).

CoInductive fun_delta : Type := FunDelta of aT & rT.

Definition fwith x y (f : aT -> rT) := [fun z => if z == x then y else f z].

Definition app_fdelta df f z :=
  let: FunDelta x y := df in if z == x then y else f z.

End FunWith.

Prenex Implicits fwith.

Notation "x |-> y" := (FunDelta x y)
  (at level 190, no associativity,
   format "'[hv' x '/ '  |->  y ']'") : fun_delta_scope.

Delimit Scope fun_delta_scope with FUN_DELTA.
Arguments Scope app_fdelta [_ type_scope fun_delta_scope _ _].

Notation "[ 'fun' z : T => F 'with' df1 , .. , dfn ]" :=
  (SimplFunDelta (fun z : T =>
     app_fdelta df1 .. (app_fdelta dfn (fun _ => F)) ..))
  (at level 0, z ident, only parsing) : fun_scope.

Notation "[ 'fun' z => F 'with' df1 , .. , dfn ]" :=
  (SimplFunDelta (fun z =>
      app_fdelta df1%FUN_DELTA .. (app_fdelta dfn%FUN_DELTA (fun _ => F)) ..))
  (at level 0, z ident, format
  "'[hv' [ '[' 'fun'  z  => '/ '  F ']' '/'  'with'  '[' df1 , '/'  .. , '/'  dfn ']' ] ']'") : fun_scope.

Notation "[ 'eta' f 'with' df1 , .. , dfn ]" :=
  (SimplFunDelta (fun _ =>
      app_fdelta df1%FUN_DELTA .. (app_fdelta dfn%FUN_DELTA f) ..))
  (at level 0, z ident, format
  "'[hv' [ '[' 'eta' '/ '  f ']' '/'  'with'  '[' df1 , '/'  .. , '/'  dfn ']' ] ']'") : fun_scope.

(* Various EqType constructions.                                         *)

Section ComparableType.

Variable T : Type.

Definition comparable := forall x y : T, {x = y} + {x <> y}.

Hypothesis Hcompare : forall x y : T, {x = y} + {x <> y}.

Definition compareb x y := if Hcompare x y is left _ then true else false.

Lemma compareP : reflect_eq compareb.
Proof. by move=> x y; rewrite /compareb; case (Hcompare x y); constructor. Qed.

Definition comparableType := mkEqType compareP.

End ComparableType.


Definition eq_comparable (T : eqType) : comparable T :=
  fun x y => decP (x =P y).

Section SubType.

Variables (T : Type) (p : pred T).

Structure subType : Type := SubType {
  SubType_sort :> Type;
  val : SubType_sort -> T;
  Sub : forall x, p x -> SubType_sort;
  _ : forall P (_ : forall x p_x, P (Sub x p_x)) u, P u;
  _ : forall x p_x, val (Sub x p_x) = x
}.

Implicit Arguments Sub [s].

Section SubTypeOp.

Variable sT : subType.

CoInductive Sub_spec : sT -> Type := SubSpec x p_x : Sub_spec (Sub x p_x).

Lemma SubP : forall u, Sub_spec u.
Proof. by case: sT Sub_spec SubSpec => T' _ C rec _ /= s sC; elim/rec. Qed.

Lemma SubK : forall x p_x, @val sT (Sub x p_x) = x.
Proof. by case sT. Qed.

Definition insub x :=
  if @idP (p x) is Reflect_true p_x then @Some sT (Sub x p_x) else None.

Definition insubd u0 x := odflt u0 (insub x).

CoInductive insub_spec x : option sT -> Type :=
  | InsubSome u of p x & val u = x : insub_spec x (Some u)
  | InsubNone   of ~~ p x          : insub_spec x None.

Lemma insubP : forall x, insub_spec x (insub x).
Proof.
rewrite/insub => x; case: {2}(p x) / idP; last by right; exact/negP.
by left; rewrite ?SubK.
Qed.
  
Lemma insubT : forall x p_x, insub x = Some (Sub x p_x).
Proof.
move=> x p_x; case: insubP; last by case/negP.
case/SubP=> y p_y _ def_x; rewrite -def_x SubK in p_x *.
congr (Some (Sub _ _)); exact: bool_irrelevance.
Qed.

Lemma insubF : forall x, p x = false -> insub x = None.
Proof. by move=> x npx; case: insubP => // u; rewrite npx. Qed.

Lemma insubN : forall x, ~~ p x -> insub x = None.
Proof. by move=> x; move/negPf; exact: insubF. Qed.

Lemma isSome_insub : ([eta insub] : pred T) =1 p.
Proof. by apply: fsym => x; case: insubP => //; move/negPf. Qed.

Lemma insubK : ocancel insub (@val _).
Proof. by move=> x; case: insubP. Qed.

Lemma valP : forall u : sT, p (val u).
Proof. by case/SubP=> x p_x; rewrite SubK. Qed.

Lemma valK : pcancel (@val _) insub.
Proof. case/SubP=> x p_x; rewrite SubK; exact: insubT. Qed.

Lemma val_inj : injective (@val sT).
Proof. exact: pcan_inj valK. Qed.

Lemma val_insubd : forall u0 x, val (insubd u0 x) = if p x then x else val u0.
Proof.
by rewrite /insubd => u0 x; case: insubP => [u -> // | ]; move/negPf->.
Qed.

Lemma insubdK : forall u0, {in p, cancel (insubd u0) (@val _)}.
Proof. by move=> u0 x p_x; rewrite val_insubd [p x]p_x. Qed.

Definition insub_eq x :=
  let Some_sub p_x := Some (Sub x p_x : sT) in
  let None_sub _ := None in
  (if p x as p_x return p x = p_x -> _ then Some_sub else None_sub) (erefl _).

Lemma insub_eqE : insub_eq =1 insub.
Proof.
rewrite /insub_eq /insub => x.
case: {2 4 5}(p x) / idP (erefl _) => // p_x p_x'.
by congr Some; apply: val_inj; rewrite !SubK.
Qed.

End SubTypeOp.

Lemma vrefl : forall x, p x -> x = x. Proof. by []. Qed.

End SubType.

Implicit Arguments SubType [T p SubType_sort Sub].
Implicit Arguments Sub [T p s].
Implicit Arguments insub [T p sT].
Implicit Arguments vrefl [T p].
Implicit Arguments val_inj [T p sT].
Prenex Implicits val Sub insub insubd val_inj vrefl.

Notation "[ 'subType' 'of' T ]" :=
  (match [is T <: subType _] as s return {type of @SubType _ _ for s} -> _ with
  | SubType _ _ _ rec can => fun k => k _ _ rec can end
  (@SubType _ _ T)) (at level 0, only parsing) : form_scope.

Notation "[ 'subType' 'for' proj ]" :=
  (match [is argumentType proj : Type <: subType _] as s
     return {type of @SubType _ _ _ for @val _ _ s} -> _ with
  | SubType _ _ _ rec can => fun k => k _ rec can end
  (@SubType _ _ _ proj)) (at level 0, only parsing) : form_scope.

Notation "[ 'insub' x 'in' sT ]" := (insub x : option sT)
  (at level 0, format "[ 'insub'  x  'in'  sT ]") : form_scope.

Definition NewType T nT proj Con rec :=
  @SubType T xpredT nT proj (fun x _ => Con x)
   (fun P IH => rec P (fun x => IH x (erefl true))).

Implicit Arguments NewType [T nT Con].

Definition innew T nT x := @Sub T predT nT x (erefl true).

Implicit Arguments innew [T nT].
Prenex Implicits innew.

Lemma innew_val : forall T nT, cancel val (@innew T nT).
Proof. by move=> T nT u; apply: val_inj; exact: SubK. Qed.

Notation "[ 'innew' x 'in' nT ]" := (innew x : nT)
  (at level 0, format "[ 'innew'  x  'in'  nT ]") : form_scope.

(* Prenex Implicits and renaming. *)
Notation sval := (@proj1_sig _ _).
Notation "@ 'sval'" := (@proj1_sig) (at level 10, format "@ 'sval'").

Section SigProj.

Variables (T : Type) (P Q : T -> Prop).

Lemma svalP : forall u : sig P, P (sval u). Proof. by case. Qed.

Definition s2val (u : sig2 P Q) := let: exist2 x _ _ := u in x.

Lemma s2valP : forall u, P (s2val u). Proof. by case. Qed.

Lemma s2valP' : forall u, Q (s2val u). Proof. by case. Qed.

End SigProj.

Prenex Implicits svalP s2val s2valP s2valP'.

Canonical Structure sig_subType T (p : pred T) :=
  SubType (@sval T [eta p]) (@sig_rect _ _) vrefl.

(* Shorhand for the return type of insub. *)
Notation "{ ? x : T | P }" := (option {x : T | is_true P})
  (at level 0, x at level 69, only parsing) : type_scope.
Notation "{ ? x | P }" := {? x : _ | P}
  (at level 0, x at level 69, format  "{ ?  x  |  P }") : type_scope.
(* Because the standard prologue of Coq declares { x ... } with x   *)
(* at level 99, we can't give shorthand for {x | x \in A}, however. *)
Notation "{ ? x \in A }" := {? x | x \in A}
  (at level 0, x at level 69, format  "{ ?  x  \in  A }") : type_scope.
Notation "{ ? x \in A | P }" := {? x | (x \in A) && P}
  (at level 0, x at level 69, format  "{ ?  x  \in  A  |  P }") : type_scope.

(* A variant of injection with default that infers a collective predicate *)
(* from the membership proof for the default value.                       *)
Definition insigd T (A : mem_pred T) x (Ax : in_mem x A) :=
  insubd (exist [eta A] x Ax).

(* This should be a rel definition, but it seems this causes divergence  *)
(* of the simpl tactic on expressions involving == on 4+ nested subTypes *)
(* in a "strict" position (e.g., as the argument of ~~).                 *)

Notation feq := (fun f x y => f x == f y).

Section TransferEqType.

Variables (T : Type) (eT : eqType) (f : T -> eT).

Lemma inj_reflect_eq : injective f -> reflect_eq (feq f).
Proof. by move=> f_inj x y; apply: (iffP eqP) => [|-> //]; exact: f_inj. Qed.

Definition InjEqType f_inj := mkEqType (inj_reflect_eq f_inj).

Definition PcanEqType g (fK : pcancel f g) := InjEqType (pcan_inj fK).

Definition CanEqType g (fK : cancel f g) := InjEqType (can_inj fK).

End TransferEqType.

Section SubEqType.

Variables (T : eqType) (p : pred T) (sT : subType p).

Lemma val_eqP : @reflect_eq sT (feq val).
Proof. exact: inj_reflect_eq val_inj. Qed.

Canonical Structure sub_eqType := mkEqType val_eqP.

Lemma val_eqE : forall u v : sT, (val u == val v) = (u == v).
Proof. by []. Qed.

End SubEqType.

Implicit Arguments val_eqP [T p sT x y].
Prenex Implicits val_eqP.

Notation "[ 'subEqType' 'for' proj ]" :=
  (@mkEqType _ (feq proj) (@val_eqP _ _ _))
  (at level 0, only parsing) : form_scope.

Canonical Structure sig_eqType (T : eqType) (p : pred T) :=
  [subEqType for @sval T p].

Section ProdEqType.

Variable T1 T2 : eqType.

Definition pair_eq := [rel u v : T1 * T2 | (u.1 == v.1) && (u.2 == v.2)].

Lemma pair_eqP : reflect_eq pair_eq.
Proof.
move=> [x1 x2] [y1 y2] /=; apply: (iffP andP) => [[]|[<- <-]] //=.
by do 2!move/eqP->.
Qed.

Canonical Structure prod_eqType := mkEqType pair_eqP.

Lemma pair_eqE : pair_eq = eqd :> rel _. Proof. by []. Qed.

Lemma pair_eq1 : forall u v : T1 * T2, u == v -> u.1 == v.1.
Proof. by move=> [x1 x2] [y1 y2]; case/andP. Qed.

Lemma pair_eq2 : forall u v : T1 * T2, u == v -> u.2 == v.2.
Proof. by move=> [x1 x2] [y1 y2]; case/andP. Qed.

End ProdEqType.

Implicit Arguments pair_eqP [T1 T2].

Prenex Implicits pair_eqP.

Definition predX T1 T2 (p1 : pred T1) (p2 : pred T2) :=
  [pred z | p1 z.1 && p2 z.2].

Notation "[ 'predX' A1 & A2 ]" := (predX [mem A1] [mem A2])
  (at level 0, format "[ 'predX'  A1  &  A2 ]") : fun_scope.

Section OptionEqType.

Variable T : eqType.

Definition eq_opt (u v : option T) : bool :=
  oapp (fun x => oapp (eqd x) false v) (~~ v) u.

Lemma eq_optP : reflect_eq eq_opt.
Proof.
case=> [x|] [y|] /=; by [constructor | apply: (iffP eqP) => [|[]] ->].
Qed.

Canonical Structure option_eqMixin := EqMixin eq_optP.
Canonical Structure option_eqType := EqClass option_eqMixin.

End OptionEqType.

Section SumEqType.

Variables (I : eqType) (T : I -> eqType).

Record eq_sum : Type := EqSum {sum_tag : I; sum_tagged : T sum_tag}.

Definition tagged_as (u v : eq_sum) : T (sum_tag u) :=
  if sum_tag u =P sum_tag v is Reflect_true Huv then
    eq_rect_r T (sum_tagged v) Huv 
  else sum_tagged u.

Lemma tagged_as_same : forall i (x y : T i),
  tagged_as (EqSum x) (EqSum y) = y.
Proof.
move=> i x y; rewrite /tagged_as /=; case: (i =P i) => [Hii|[]]; auto.
by rewrite (eq_axiomK Hii).
Qed.

Definition sum_eq u v :=
  (sum_tag u == sum_tag v) && (sum_tagged u == tagged_as u v).

Lemma sum_eqP : reflect_eq sum_eq.
Proof.
move=> [i x] [j y]; rewrite /sum_eq /=.
case: (i =P j) y => [<-|Hij] y; last by right; case.
by apply: (iffP eqP) => [->|<-]; rewrite tagged_as_same.
Qed.

Canonical Structure sum_eqMixin := EqMixin sum_eqP.
Canonical Structure sum_eqType := EqClass sum_eqMixin.

Lemma sum_eqE : sum_eq = eqd. Proof. by []. Qed.

Lemma sum_eq_tag : forall u v : sum_eqType, u == v -> sum_tag u == sum_tag v.
Proof.
by move=> [i x] [j y]; rewrite -{1}sum_eqE /sum_eq /=; case (i == j).
Qed.

Lemma sum_eq_tagged : forall i (x y : T i), (EqSum x == EqSum y) = (x == y).
Proof. by move=> *; rewrite -{1}sum_eqE /sum_eq /= eqxx tagged_as_same. Qed.

End SumEqType.

Implicit Arguments sum_tagged [I T].
Implicit Arguments sum_eqP [I T x y].
Prenex Implicits sum_tag sum_tagged sum_eqP.

