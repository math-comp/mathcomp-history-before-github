Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop ssralg orderedalg zint qnum poly.

Import GRing.Theory ORing.Theory AbsrNotation.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope creal_scope with CR.

Module EpsilonReasonning.

Definition leq_maxE := (orTb, orbT, leqnn, leq_maxr).

Fixpoint max_seq s :=
  match s with
    | [::] => 0%N
    | a :: r => maxn a (max_seq r)
  end.

Definition closed T (i : T) := {j : T | j = i}.
Ltac close :=
  match goal with
      | |- ?G =>
        match G with
          | context [closed ?i] => instantiate (1 := [::]) in (Value of i); exists i
        end
  end.

Ltac pose_big_enough i :=
  evar (i : nat);
  suff : closed i;
    [move=> _; instantiate (1 := max_seq _) in (Value of i)|].

Ltac pose_big_modulus m F :=
  evar (m : F -> nat);
  suff : closed m;
    [move=> _; instantiate (1 := (fun e => max_seq _)) in (Value of m)|].

Ltac exists_big_enough m F :=
  evar (m : F -> nat);
  suff : closed m;
    [move=> _; instantiate (1 := (fun e => max_seq _)) in (Value of m);
      exists m
    |].

Definition selected := locked.
Lemma select T (x : T) : x = selected x. Proof. exact: lock. Qed.

Lemma instantiate_max_seq (P : bool -> Type) i s :
  P true -> P ((i <= selected max_seq (i :: s))%N).
Proof. by rewrite -select ?leq_maxE. Qed.

Ltac big_selected i :=
  rewrite ?[in X in selected X]/i;
    rewrite ?[in X in selected X]leq_maxE -/max_seq;
      do 1!
        [ rewrite -[selected true]select
          | rewrite [max_seq in X in selected X]select;
            apply instantiate_max_seq;
              rewrite ?[in X in selected X]leq_maxE -/max_seq;
                rewrite -?select].

Ltac big_enough :=
    match goal with
      | |- ?G =>
        match G with
        | context [(?x <= ?i)%N] =>
          rewrite [(x <= i)%N]select; big_selected i
        end
    end.

Ltac big :=
    match goal with
      | H : is_true (?m ?e <= ?i)%N |- ?G =>
        match G with
          | context [(?x <= i)%N] =>
            rewrite [(x <= i)%N](leq_trans _ H) /=; last by big_enough
        end
      | _ => big_enough
    end.

End EpsilonReasonning.
Import EpsilonReasonning.

Module Creals.
Section Creals.

Local Open Scope creal_scope.
Local Open Scope ring_scope.

Definition asympt1 (R : poIdomainType) (P : R -> nat -> Prop)
  := {m : R -> nat | forall eps i, 0 < eps -> (m eps <= i)%N -> P eps i}.

Definition asympt2 (R : poIdomainType)  (P : R -> nat -> nat -> Prop)
  := {m : R -> nat | forall eps i j, 0 < eps -> (m eps <= i)%N -> (m eps <= j)%N -> P eps i j}.

Notation "{ 'asympt' e : i / P }" := (asympt1 (fun e i => P))
  (at level 0, e ident, i ident, format "{ 'asympt'  e  :  i  /  P }") : type_scope.

Notation "{ 'asympt' e : i j / P }" := (asympt2 (fun e i j => P))
  (at level 0, e ident, i ident, j ident, format "{ 'asympt'  e  :  i  j  /  P }") : type_scope.

Variable F : oFieldType.

Lemma asympt_mulLR (k : F) (hk : 0 < k) (P : F -> nat -> Prop) :
  {asympt e : i / P e i} -> {asympt e : i / P (e * k) i}.
Proof.
case=> m hm; exists (fun e => m (e * k))=> e i he hi.
by apply: hm=> //; rewrite -ltr_pdivr_mulr // mul0r.
Qed.

Lemma asympt_mulRL (k : F) (hk : 0 < k) (P : F -> nat -> Prop) :
  {asympt e : i / P (e * k) i} -> {asympt e : i / P e i}.
Proof.
case=> m hm; exists (fun e => m (e / k))=> e i he hi.
rewrite -[e](@mulfVK _ k) ?gtr_eqF //.
by apply: hm=> //; rewrite -ltr_pdivr_mulr ?invr_gt0 // mul0r.
Qed.

Lemma asymptP (P1 : F -> nat -> Prop) (P2 : F -> nat -> Prop) :
  (forall e i, 0 < e -> P1 e i -> P2 e i) ->
  {asympt e : i / P1 e i} -> {asympt e : i / P2 e i}.
Proof.
by move=> hP; case=> m hm; exists m=> e i he me; apply: hP=> //; apply: hm.
Qed.

Lemma asympt2_mulLR (k : F) (hk : 0 < k) (P : F -> nat -> nat -> Prop) :
  {asympt e : i j / P e i j} -> {asympt e : i j / P (e * k) i j}.
Proof.
case=> m hm; exists (fun e => m (e * k))=> e i j he hi hj.
by apply: hm=> //; rewrite -ltr_pdivr_mulr // mul0r.
Qed.

Lemma asympt2_mulRL (k : F) (hk : 0 < k) (P : F -> nat -> nat -> Prop) :
  {asympt e : i j / P (e * k) i j} -> {asympt e : i j / P e i j}.
Proof.
case=> m hm; exists (fun e => m (e / k))=> e i j he hi hj.
rewrite -[e](@mulfVK _ k) ?gtr_eqF //.
by apply: hm=> //; rewrite -ltr_pdivr_mulr ?invr_gt0 // mul0r.
Qed.

Lemma asympt2P (P1 : F -> nat -> nat -> Prop) (P2 : F -> nat -> nat -> Prop) :
  (forall e i j, 0 < e -> P1 e i j -> P2 e i j) ->
  {asympt e : i j / P1 e i j} -> {asympt e : i j / P2 e i j}.
Proof.
move=> hP; case=> m hm; exists m=> e i j he mei mej.
by apply: hP=> //; apply: hm.
Qed.

Definition gtr0E := (invr_gt0, exprn_gt0, ltr0n, @ltr01).
Definition ger0E := (invr_ge0, exprn_ge0, ler0n, @ler01).

Lemma splitf (n : nat) (e : F) : e = iterop n +%R (e / n%:R) e.
Proof.
case: n=> // n; set e' := (e / _).
have -> : e = e' * n.+1%:R by rewrite mulfVK ?pnatr_eq0.
move: e'=> {e} e; rewrite iteropS.
by elim: n=> /= [|n <-]; rewrite !mulr_natr ?mulr1n.
Qed.

Definition creal_axiom (x : nat -> F) :=  {asympt e : i j / `| x i - x j | < e}.

CoInductive creal := CReal {cauchyseq :> nat -> F; _ : creal_axiom cauchyseq}.
Bind Scope creal_scope with creal.

Lemma crealP (x : creal) : {asympt e : i j / `| x i - x j | < e}.
Proof. by case: x. Qed.

Definition cauchymod :=
  nosimpl (fun (x : creal) => let: CReal _ m := x in projT1 m).

Lemma cauchymodP (x : creal) eps i j : 0 < eps ->
  (cauchymod x eps <= i)%N -> (cauchymod x eps <= j)%N -> `| x i - x j | < eps.
Proof. by case: x=> [x [m mP] //] /mP; apply. Qed.

Definition neq_creal (x y : creal) : Prop :=
  exists eps, (0 < eps) &&
    (eps * 3%:R <= `|x (cauchymod x eps) - y (cauchymod y eps)|).
Local Notation "!=%CR" := neq_creal : creal_scope.
Local Notation "x != y" := (neq_creal x  y) : creal_scope.

Definition eq_creal x y := (~ (x != y)%CR).
Local Notation "x == y" := (eq_creal x y) : creal_scope.

Lemma ltr_distl_creal (e : F) (i : nat) (x : creal) (j : nat) (a b : F) :
  0 < e -> (cauchymod x e <= i)%N -> (cauchymod x e <= j)%N ->
  `| x i - a | <= b - e -> `| x j - a | < b.
Proof.
move=> e_gt0 hi hj hb.
rewrite (ler_lt_trans (ler_dist_add (x i) _ _)) ?ltr_le_add //.
by rewrite -[b](addrNK e) addrC ler_lt_add ?cauchymodP.
Qed.

Lemma ltr_distr_creal (e : F) (i : nat) (x : creal) (j : nat) (a b : F) :
  0 < e -> (cauchymod x e <= i)%N -> (cauchymod x e <= j)%N ->
  a + e <= `| x i - b | -> a < `| x j - b |.
Proof.
move=> e_gt0 hi hj hb; apply: contraLR hb; rewrite -ltrNge -lerNgt.
by move=> ha; rewrite (@ltr_distl_creal e j) // addrK.
Qed.

(* Lemma asympt_neq (x y : creal) : x != y -> *)
(*   {e | 0 < e & forall i, (cauchymod x e <= i)%N -> *)
(*                          (cauchymod y e <= i)%N -> `|x i - y i| >= e}. *)
(* Proof. *)
(* case/sigW=> e /andP[e_gt0 hxy]. *)
(* exists e=> // i hi hj; move: hxy; rewrite !lerNgt; apply: contra=> hxy. *)
(* rewrite !mulr_addr !mulr1 distrC (@ltr_distl_creal i) //. *)
(* by rewrite distrC ltrW // (@ltr_distl_creal i) // ltrW. *)
(* Qed. *)

Definition lbound (x y : creal) (neq_xy : x != y) : F :=
  projT1 (sigW neq_xy).

Lemma lboundP (x y : creal) (neq_xy : x != y) i :
  (cauchymod x (lbound neq_xy) <= i)%N ->
  (cauchymod y (lbound neq_xy) <= i)%N -> lbound neq_xy <= `|x i - y i|.
Proof.
rewrite /lbound; case: (sigW _)=> /= d /andP[d_gt0 hd] hi hj.
apply: contraLR hd; rewrite -!ltrNge=> hd.
rewrite (@ltr_distl_creal d i) // distrC ltrW // (@ltr_distl_creal d i) //.
by rewrite distrC ltrW // !mulr_addr mulr1 !addrA !addrK.
Qed.

Notation lbound_of p := (@lboundP _ _ p _ _ _).

Lemma lbound_gt0 (x y : creal) (neq_xy : x != y) : lbound neq_xy > 0.
Proof. by rewrite /lbound; case: (sigW _)=> /= d /andP[]. Qed.

Lemma cst_crealP (x : F) : creal_axiom (fun _ => x).
Proof. by exists (fun _ => 0%N)=> *; rewrite subrr absr0. Qed.
Definition cst_creal (x : F) := CReal (cst_crealP x).
Local Notation "x %:CR" := (cst_creal x)
  (at level 2, left associativity, format "x %:CR") : creal_scope.
Local Notation "0" := (0 %:CR) : creal_scope.

Lemma lbound0P (x : creal) (x_neq0 : x != 0) i :
  (cauchymod x (lbound x_neq0) <= i)%N ->
  (cauchymod 0%CR (lbound x_neq0) <= i)%N -> lbound x_neq0 <= `|x i|.
Proof. by move=> cx c0; rewrite -[X in `|X|]subr0 -[0]/(0%CR i) lboundP. Qed.

Notation lbound0_of p := (@lbound0P _ p _ _ _).

Lemma neq_crealP e i j (e_gt0 : 0 < e) (x y : creal) :
  (cauchymod x (e / 5%:R) <= i)%N -> (cauchymod y (e / 5%:R) <= j)%N ->
  e <= `|x i - y j| ->  x != y.
Proof.
move=> hi hj he; exists (e / 5%:R); rewrite pmulr_rgt0 ?gtr0E //=.
rewrite distrC ltrW // (@ltr_distr_creal (e / 5%:R) j) ?pmulr_rgt0 ?gtr0E //.
rewrite distrC ltrW // (@ltr_distr_creal (e / 5%:R) i) ?pmulr_rgt0 ?gtr0E //.
by rewrite mulr_natr -!mulrSr -mulrnAr -mulr_natr mulVf ?pnatr_eq0 ?mulr1.
Qed.

Lemma eq_crealP (x y : creal) : {asympt e : i / `|x i - y i| < e} ->
  (x == y)%CR.
Proof.
case=> m hm neq_xy; pose d := lbound neq_xy.
pose_big_enough i.
  have := (hm d i); rewrite lbound_gt0; do ?big=> /(_ isT) /(_ isT).
  by apply/negP; rewrite -lerNgt lboundP; do ?big.
by close.
Qed.

Lemma eq0_crealP (x : creal) : {asympt e : i / `|x i| < e} -> x == 0.
Proof.
by move=> hx; apply: eq_crealP; apply: asymptP hx=> e i; rewrite subr0.
Qed.

Lemma asympt_eq (x y : creal) (eq_xy : x == y) :
  {asympt e : i / `|x i - y i| < e}.
Proof.
exists_big_enough m F.
   move=> e i e0 hi; rewrite ltrNge; apply/negP=> he; apply: eq_xy.
   by apply: (@neq_crealP e i i); do ?big.
by close.
Qed.

Lemma asympt_eq0 (x : creal) : x == 0 -> {asympt e : i / `|x i| < e}.
Proof. by move/asympt_eq; apply: asymptP=> e i; rewrite subr0. Qed.

Definition eqmod (x y : creal) (eq_xy : x == y) := projT1 (asympt_eq eq_xy).
Lemma eqmodP (x y : creal) (eq_xy : x == y) eps i : 0 < eps ->
                (eqmod eq_xy eps <= i)%N -> `|x i - y i| < eps.
Proof.
by move=> eps_gt0; rewrite /eqmod; case: (asympt_eq _)=> /= m hm /hm; apply.
Qed.
Lemma eq0modP (x : creal) (x_eq0 : x == 0) eps i : 0 < eps ->
                (eqmod x_eq0 eps <= i)%N -> `|x i| < eps.
Proof.
by move=> eps_gt0 hi; rewrite -[X in `|X|]subr0 -[0]/(0%CR i) eqmodP.
Qed.

Lemma eq_creal_refl x : x == x.
Proof.
apply: eq_crealP; exists (fun _ => 0%N).
by move=> e i e_gt0 _; rewrite subrr absr0.
Qed.

Lemma neq_creal_sym x y : x != y -> y != x.
Proof.
move=> neq_xy; pose_big_enough i.
  apply: (@neq_crealP (lbound neq_xy) i i);
  by rewrite ?lbound_gt0 1?distrC ?(lbound_of neq_xy); do ?big.
by close.
Qed.


Lemma eq_creal_sym x y : x == y -> y == x.
Proof. by move=> eq_xy /neq_creal_sym. Qed.

Lemma eq_creal_trans x y z : x == y -> y == z -> x == z.
Proof.
move=> eq_xy eq_yz; apply: eq_crealP; exists_big_enough m F.
  move=> e i e_gt0 hi; rewrite (ler_lt_trans (ler_dist_add (y i) _ _)) //.
  rewrite [e](splitf 2) /= ltr_add ?eqmodP ?pmulr_rgt0 ?invr_gt0 ?ltr0n //;
  by big.
by close.
Qed.

Definition lt_creal (x y : creal) : Prop :=
  exists eps, (0 < eps) &&
    (x (cauchymod x eps) + eps * 3%:R <= y (cauchymod y eps)).
Local Notation "<%CR" := lt_creal : creal_scope.
Local Notation "x < y" := (lt_creal x y) : creal_scope.

Definition le_creal (x y : creal) : Prop := ~ (y < x)%CR.
Local Notation "<=%CR" := le_creal : creal_scope.
Local Notation "x <= y" := (le_creal x y) : creal_scope.

Lemma ltr_creal (e : F) (i : nat) (x : creal) (j : nat) (a : F) :
  0 < e -> (cauchymod x e <= i)%N -> (cauchymod x e <= j)%N ->
  x i <= a - e -> x j < a.
Proof.
move=> e_gt0 hi hj ha; have := cauchymodP e_gt0 hj hi.
rewrite ltr_distl=> /andP[_ /ltr_le_trans-> //].
by rewrite -(ler_add2r (- e)) addrK.
Qed.

Lemma gtr_creal (e : F) (i : nat) (x : creal) (j : nat) (a : F) :
  0 < e -> (cauchymod x e <= i)%N -> (cauchymod x e <= j)%N ->
  a + e <= x i-> a < x j.
Proof.
move=> e_gt0 hi hj ha; have := cauchymodP e_gt0 hj hi.
rewrite ltr_distl=> /andP[/(ler_lt_trans _)-> //].
by rewrite -(ler_add2r e) addrNK.
Qed.

Definition diff (x y : creal) (lt_xy : (x < y)%CR) : F := projT1 (sigW lt_xy).

Lemma diff_gt0 (x y : creal) (lt_xy : (x < y)%CR) : diff lt_xy > 0.
Proof. by rewrite /diff; case: (sigW _)=> /= d /andP[]. Qed.

Lemma diffP (x y : creal) (lt_xy : (x < y)%CR) i :
  (cauchymod x (diff lt_xy) <= i)%N ->
  (cauchymod y (diff lt_xy) <= i)%N -> x i + diff lt_xy <= y i.
Proof.
rewrite /diff; case: (sigW _)=> /= e /andP[e_gt0 he] hi hj.
rewrite ltrW // (@gtr_creal e (cauchymod y e)) // (ler_trans _ he) //.
rewrite !mulr_addr mulr1 !addrA !ler_add2r ltrW //.
by rewrite (@ltr_creal e (cauchymod x e)) // addrK.
Qed.

Notation diff_of p := (@diffP _ _ p _ _ _).

Lemma diff0P (x : creal) (x_gt0 : (0 < x)%CR) i :
  (cauchymod x (diff x_gt0) <= i)%N ->
  (cauchymod 0%CR (diff x_gt0) <= i)%N -> diff x_gt0 <= x i.
Proof. by move=> cx c0; rewrite -[diff _]add0r -[0]/(0%CR i) diffP. Qed.

Notation diff0_of p := (@diff0P _ p _ _ _).

Lemma lt_crealP e i j (e_gt0 : 0 < e) (x y : creal) :
  (cauchymod x (e / 5%:R) <= i)%N -> (cauchymod y (e / 5%:R) <= j)%N ->
  x i + e <= y j ->  (x < y)%CR.
Proof.
move=> hi hj he; exists (e / 5%:R); rewrite pmulr_rgt0 ?gtr0E //=.
rewrite ltrW // (@gtr_creal (e / 5%:R) j) ?pmulr_rgt0 ?gtr0E //.
rewrite (ler_trans _ he) // -addrA (monoLR (addrNK _) (ler_add2r _)).
rewrite ltrW // (@ltr_creal (e / 5%:R) i) ?pmulr_rgt0 ?gtr0E //.
rewrite -!addrA ler_addl !addrA -mulrA -{1}[e]mulr1 -!(mulr_subr, mulr_addr).
rewrite pmulr_rge0 // {1}[1](splitf 5) /= !mul1r !mulr_addr mulr1.
by rewrite !oppr_add !addrA !addrK addrN.
Qed.

Lemma le_crealP i (x y : creal) :
  (forall j, (i <= j)%N -> x j <= y j) -> (x <= y)%CR.
Proof.
move=> hi lt_yx; pose_big_enough j.
  have := hi j; do ?big=> /(_ isT); apply/negP; rewrite -ltrNge.
  by rewrite (ltr_le_trans _ (diff_of lt_yx)) ?ltr_spaddr ?diff_gt0; do ?big.
by close.
Qed.

Lemma le_creal_refl (x : creal) : (x <= x)%CR.
Proof. by apply: (@le_crealP 0%N). Qed.

Lemma lt_neq_creal (x y : creal) : (x < y)%CR -> x != y.
Proof.
move=> ltxy; pose_big_enough i.
  apply: (@neq_crealP (diff ltxy) i i); do ?by big.
    by rewrite diff_gt0.
  rewrite distrC lerNgt ltr_distl negb_and -!lerNgt.
  rewrite diffP ?orbT //; do ?by big.
by close.
Qed.

Lemma eq_le_creal (x y : creal) : x == y -> (x <= y)%CR.
Proof. by move=> /eq_creal_sym ? /lt_neq_creal. Qed.

Lemma asympt_le (x y : creal) (le_xy : (x <= y)%CR) :
  {asympt e : i / x i < y i + e}.
Proof.
exists_big_enough m F.
  move=> e i e0 hm; rewrite ltrNge; apply/negP=> he; apply: le_xy.
  by apply: (@lt_crealP e i i)=> //; do ?big.
by close.
Qed.

Lemma asympt_ge0 (x : creal) : (0 <= x)%CR -> {asympt e : i / - e < x i}.
Proof. by move/asympt_le; apply: asymptP=> *; rewrite -subr_gt0 opprK. Qed.

Definition lemod (x y : creal) (le_xy : (x <= y)%CR) := projT1 (asympt_le le_xy).

Lemma lemodP (x y : creal) (le_xy : (x <= y)%CR) eps i : 0 < eps ->
                (lemod le_xy eps <= i)%N -> x i < y i + eps.
Proof.
by move=> eps_gt0; rewrite /lemod; case: (asympt_le _)=> /= m hm /hm; apply.
Qed.

Lemma ge0modP (x : creal) (x_ge0 : (0 <= x)%CR) eps i : 0 < eps ->
                (lemod x_ge0 eps <= i)%N -> - eps < x i.
Proof.
by move=> eps_gt0 hi; rewrite -(ltr_add2r eps) addNr -[0]/(0%CR i) lemodP.
Qed.

(* CoInductive cond_type : Type :=  *)
(* | CBound of creal & F  *)
(* | CEq x y of x == y & F  *)
(* | CLe x y of (x <= y)%CR & F  *)
(* | CNeq x y of x != y *)
(* | CLt x y of (x < y)%CR *)
(* | CNat of nat. *)
(* Notation cond_eval := [fun c =>  *)
(*   match c with  *)
(*     | CBound x e => cauchymod x e  *)
(*     | CEq x y exy e => eqmod exy e *)
(*     | CLe x y lxy e => lemod lxy e *)
(*     | CNeq x y nexy => maxn (cauchymod x (lbound nexy)) (cauchymod y (lbound nexy)) *)
(*     | CLt x y nexy => maxn (cauchymod x (diff nexy)) (cauchymod y (diff nexy)) *)
(*     | CNat n => n end]. *)
(* Notation "x # e" := (CBound x e) (at level 70, no associativity) : cauchy_cond_scope. *)
(* Notation "eq_xy ~ e" := (CEq eq_xy e) (at level 70, no associativity) : cauchy_cond_scope. *)
(* Notation "le_xy < e" := (CLe le_xy e) : cauchy_cond_scope. *)
(* Notation "! neq_xy" := (CNeq neq_xy) (at level 10) : cauchy_cond_scope. *)
(* Notation "< lt_xy" := (CLt lt_xy) (at level 10) : cauchy_cond_scope. *)
(* Notation "> i" := (CNat i) (at level 10) : cauchy_cond_scope. *)

(* Definition cond_path c0 (c : seq cond_type) : nat := *)
(*   foldr maxn (cond_eval c0) (map cond_eval c). *)
(* Definition cond_rec (c : seq cond_type) := *)
(*   (if c is c0 :: c' then cond_path c0 c' else 0%N). *)
(* Definition cond := nosimpl cond_rec. *)
(* Delimit Scope cauchy_cond_scope with CC. *)
(* Bind Scope cauchy_cond_scope with cond. *)

(* Notation "[ 'CC' s ]" := (cond s) (at level 0, format "[ 'CC'  s ]") : form_scope. *)

(* Notation "[ 'CC' x1 ; .. ; xn ]" := [CC x1%CC :: .. [:: xn%CC] ..] *)
(*   (at level 0, format "[ 'CC'  '['  x1 ; '/'  .. ; '/'  xn ']' ]") *)
(*   : form_scope. *)

Lemma opp_crealP (x : creal) : creal_axiom (fun i => - x i).
Proof. by case: x=> [x [m mP]]; exists m=> *; rewrite /= -oppr_add absrN mP. Qed.
Definition opp_creal (x : creal) := CReal (opp_crealP x).
Local Notation "-%CR" := opp_creal : creal_scope.
Local Notation "- x" := (opp_creal x) : creal_scope.

Lemma add_crealP (x y : creal) :  creal_axiom (fun i => x i + y i).
Proof.
exists_big_enough m F.
  move=> e i j e_gt0 hi hj.
  rewrite oppr_add addrAC addrA -addrA [- _ + _]addrC.
  rewrite (ler_lt_trans (ler_abs_add _ _)) //.
  have he' : 0 < e / 2%:R by rewrite ?pmulr_lgt0 ?invr_gt0 ?ltr0n.
  by rewrite [e](splitf 2) /= ltr_add // cauchymodP //; do ?big.
by close.
Qed.
Definition add_creal (x y : creal) := CReal (add_crealP x y).
Local Notation "+%R" := add_creal : creal_scope.
Local Notation "x + y" := (add_creal x y) : creal_scope.
Local Notation "x - y" := (x + - y)%CR : creal_scope.

Definition ubound (x : creal) : F :=
  let i := cauchymod x 1 in foldl maxr (`| x i | + 1)
    (map (fun i => `| x i |) (iota 0 (cauchymod x 1))).

Lemma uboundP (x : creal) i : `| x i | <= ubound x.
Proof.
rewrite /ubound /=; case: (ltnP i (cauchymod x 1))=> [|hi].
  elim: cauchymod (_ + 1)=> [|n ihn] m //.
  rewrite ltnS -addn1 iota_add add0n map_cat foldl_cat /= ler_maxr leq_eqVlt.
  by case/orP=> [/eqP->|/ihn->] //; rewrite lerr orbT.
rewrite (@ler_trans _ (`|x (cauchymod x 1)| + 1)) //; last first.
  set a := {1}(_ + _); set b:= (_ + _); have: a <= b by apply: lerr.
  by elim: iota a b=> // u l ihl a b hab /=; rewrite ihl // ler_maxr hab.
have := (cauchymodP ltr01 hi (@leqnn _))=> /(ler_lt_trans (ler_dist_dist _ _)).
by rewrite ltr_distl=> /andP [_ /ltrW].
Qed.

Lemma ubound_gt0 x : 0 < ubound x.
Proof.
rewrite /ubound; elim: {2}(cauchymod x 1)=> [|n ihn].
  by rewrite ltr_paddl ?ltr01 ?absr_ge0.
by rewrite -addn1 iota_add add0n /= map_cat foldl_cat /= ltr_maxr ihn.
Qed.

Lemma mul_crealP (x y : creal) :  creal_axiom (fun i => x i * y i).
Proof.
exists_big_enough m F.
(* exists (fun e => [CC x # e / 2%:R / ubound y; y # e / 2%:R / ubound x]). *)
  move=> e i j e_gt0 hi hj.
  rewrite -[_ * _]subr0 -(subrr (x j * y i)) oppr_add opprK addrA.
  rewrite -mulr_subl -addrA -mulr_subr.
  rewrite (ler_lt_trans (ler_abs_add _ _)) // !absrM.
  rewrite [e](splitf 2) /= ltr_add //.
    have /ler_wpmul2l /ler_lt_trans-> // := uboundP y i.
    by rewrite absr_ge0.
  rewrite -ltr_pdivl_mulr ?ubound_gt0 ?cauchymodP //; do ?by big.
    by rewrite !pmulr_rgt0 ?invr_gt0 ?ubound_gt0 ?ltr0n.
  rewrite mulrC.
  have /ler_wpmul2l /ler_lt_trans-> // := uboundP x j.
    by rewrite absr_ge0.
  rewrite -ltr_pdivl_mulr ?ubound_gt0 ?cauchymodP //; do ?by big.
  by rewrite !pmulr_rgt0 ?invr_gt0 ?ubound_gt0 ?ltr0n.
by close.
Qed.
Definition mul_creal (x y : creal) := CReal (mul_crealP x y).
Local Notation "*%R" := mul_creal : creal_scope.
Local Notation "x * y" := (mul_creal x y) : creal_scope.

(* Lemma sub_creal_neq0 (x y : creal): ((x - y != 0) <-> (x != y))%CR. *)
(* Proof. *)
(* split=> /asympt_neq [e e_gt0 he]; apply: (@neq_crealP e)=> //. *)
(* Admitted. *)

(* Lemma sub_creal_eq0 (x y : creal): ((x - y == 0) <-> (x == y))%CR. *)
(* Proof. by rewrite /eq_creal sub_creal_neq0. Qed. *)
(* Proof *)
(* by split=> /asympt_neq [m hm]; apply: neq_crealP; exists m=> e i he hi; *)
(* [rewrite -[X in `|X|]subr0 | rewrite subr0]; rewrite hm. *)
(* Qed. *)

Lemma inv_crealP (x : creal) (x_neq0 : x != 0) : creal_axiom (fun i => (x i)^-1).
Proof.
pose d := lbound x_neq0.
exists_big_enough m F.
 (* exists (fun e => [CC x # e * d ^+ 2; ! x_neq0]). *)
  move=> e i j e_gt0 hi hj.
  have /andP[xi_neq0 xj_neq0] : (x i != 0) && (x j != 0).
    rewrite -!absr_gt0 !(ltr_le_trans _ (lbound0_of x_neq0)) ?lbound_gt0 //;
    by big.
  rewrite -(@ltr_pmul2r _ `|x i * x j|); last by rewrite absr_gt0 mulf_neq0.
  rewrite -absrM !mulr_subl mulrA mulVf // mulrCA mulVf // mul1r mulr1.
  apply: (@ltr_le_trans _ (e * d ^+ 2)); first apply: cauchymodP; do ?by big.
    by rewrite !pmulr_rgt0 ?lbound_gt0.
  rewrite ler_wpmul2l ?(ltrW e_gt0) // absrM.
  have /(_ j) hx := lbound0_of x_neq0; rewrite /=.
  have -> // := (ler_trans (@ler_wpmul2l _ d _ _ _ (hx _ _))); do ?by big.
    by rewrite ltrW // lbound_gt0.
  by rewrite ler_wpmul2r ?absr_ge0 // lbound0P //; big.
by close.
Qed.
Definition inv_creal (x : creal) (x_neq0 : x != 0) := CReal (inv_crealP x_neq0).
Local Notation "x ^-1" := (inv_creal x) : creal_scope.

(* Lemma sub_creal_gt0 (x y : creal): (0 < y - x <-> (x < y))%CR. *)
(* Proof. *)
(* split=> /asympt_lt [e e_gt0 he]; do ?[ *)
(*   pose i := maxn (maxn (cauchymod x e) (cauchymod y e))  *)
(*     (maxn (cauchymod 0 e) (cauchymod (y - x) e)); *)
(*     apply: (@lt_crealP _ e_gt0 _ _ i i); rewrite ?leq_maxr ?leqnn ?orbT //]. *)
(*   move: (he i); rewrite ?leq_maxr ?leqnn ?orbT //= => /(_ isT) /(_ isT) add0r. *)


(* ; exists m=> e i he hi; *)
(* [rewrite -[X in `|X|]subr0 | rewrite subr0]; rewrite hm. *)
(* Qed. *)

Definition poly_bound (p : {poly F}) (a r : F) : F
  := 1 + \sum_(i < size p)  `|p`_i| * (`|a| + `|r|) ^+ i.

Lemma poly_boundP p a r x : `|x - a| <= r ->
  `|p.[x]| <= poly_bound p a r.
Proof.
have [r_ge0|r_lt0] := lerP 0 r; last first.
  by move=> hr; have := ler_lt_trans hr r_lt0; rewrite absr_lt0.
rewrite ler_distl=> /andP[lx ux].
rewrite ler_paddl //.
elim/poly_ind: p=> [|p c ihp].
  by rewrite horner0 absr0 size_poly0 big_ord0.
rewrite horner_amulX size_amulX.
have [->|p_neq0 /=] := altP eqP.
  rewrite horner0 !mul0r !add0r size_poly0.
  have [->|c_neq0] /= := altP eqP; first by rewrite absr0 big_ord0.
  rewrite big_ord_recl big_ord0 addr0 coefC /=.
  by rewrite ler_pmulr ?absr_gt0 // ler_addl ler_maxr !absr_ge0.
rewrite big_ord_recl coefD coefMX coefC eqxx add0r.
rewrite (ler_trans (ler_abs_add _ _)) // addrC ler_add //.
  by rewrite expr0 mulr1.
rewrite absrM.
move: ihp=> /(ler_wpmul2r (absr_ge0 x)) /ler_trans-> //.
rewrite -mulr_suml ler_sum // => i _.
rewrite coefD coefC coefMX /= addr0 exprSr mulrA.
rewrite ler_wpmul2l //.
  by rewrite ?mulr_ge0 ?exprn_ge0 ?ler_maxr ?addr_ge0 ?absr_ge0 // ltrW.
rewrite (ger0_abs r_ge0) ler_absl oppr_add.
rewrite (ler_trans _ lx) ?(ler_trans ux) // ler_add2r.
  by rewrite ler_absr lerr.
by rewrite ler_oppl ler_absr lerr orbT.
Qed.

Lemma poly_bound_gt0 p a r : 0 < poly_bound p a r.
Proof.
rewrite ltr_paddr // sumr_ge0 // => i _.
by rewrite mulr_ge0 ?exprn_ge0 ?addr_ge0 ?ler_maxr ?absr_ge0 // ltrW.
Qed.

Lemma poly_bound_ge0 p a r : 0 <= poly_bound p a r.
Proof. by rewrite ltrW // poly_bound_gt0. Qed.

Definition poly_accr_bound (p : {poly F}) (a r : F) : F
  := (maxr 1 (2%:R * r)) ^+ (size p).-1
  * (1 + \sum_(i < (size p).-1) poly_bound p^`N(i.+1) a r).

Lemma poly_accr_bound1P p a r x y :
  `|x - a| <= r ->  `|y - a| <= r ->
  `|p.[y] - p.[x]| <= `|y - x| * poly_accr_bound p a r.
Proof.
have [|r_lt0] := lerP 0 r; last first.
  by move=> hr; have := ler_lt_trans hr r_lt0; rewrite absr_lt0.
rewrite ler_eqVlt=> /orP[/eqP->|r_gt0 hx hy].
  by rewrite !absr_le0 !subr_eq0=> /eqP-> /eqP->; rewrite !subrr absr0 mul0r.
rewrite mulrA mulr_addr mulr1 ler_paddl ?mulr_ge0 ?absr_ge0 //=.
  by rewrite exprn_ge0 ?ler_maxr ?mulr_ge0 ?ger0E ?ltrW.
rewrite -{1}(addNKr x y) [- _ + _]addrC /= -mulrA.
rewrite nderiv_taylor; last exact: mulrC.
have [->|p_neq0] := eqVneq p 0.
  rewrite size_poly0 big_ord0 horner0 subr0 absr0 mulr_ge0 ?absr_ge0 //.
  by rewrite big_ord0 mulr0 lerr.
rewrite -[size _]prednK ?lt0n ?size_poly_eq0 //.
rewrite big_ord_recl expr0 mulr1 nderivn0 addrC addKr -!mulr_sumr.
have := ler_trans (ler_abs_sum _ _ _); apply.
rewrite ler_sum // => i _.
rewrite exprSr mulrA !absrM mulrC ler_wpmul2l ?absr_ge0 //.
suff /ler_wpmul2l /ler_trans :
  `|(y - x) ^+ i| <=  maxr 1 (2%:R * r) ^+ (size p).-1.
  apply; rewrite ?absr_ge0 // mulrC ler_wpmul2l ?poly_boundP //.
  by rewrite ?exprn_ge0 // ler_maxr ler01 mulr_ge0 ?ler0n ?ltrW.
case: maxrP=> hr.
  rewrite exp1rn absrX exprn_ile1 ?absr_ge0 //.
  rewrite (ler_trans (ler_dist_add a _ _)) // addrC distrC.
  by rewrite (ler_trans _ hr) // mulr_addl ler_add ?mul1r.
rewrite (@ler_trans _ ((2%:R * r) ^+ i)) //.
  rewrite absrX @ler_expn2r -?topredE /= ?absr_ge0 ?mulr_ge0 ?ler0n //.
    by rewrite ltrW.
  rewrite (ler_trans (ler_dist_add a _ _)) // addrC distrC.
  by rewrite mulr_addl ler_add ?mul1r.
by rewrite ler_eexpn2l // ltnW.
Qed.

Lemma poly_accr_bound_gt0 p a r : 0 < poly_accr_bound p a r.
Proof.
rewrite /poly_accr_bound pmulr_rgt0 //.
  rewrite ltr_paddr ?ltr01 //.
  by rewrite sumr_ge0 // => i; rewrite poly_bound_ge0.
by rewrite exprn_gt0 // ltr_maxr ltr01 pmulr_rgt0 ?ltr0n.
Qed.

Lemma poly_accr_bound_ge0 p a r : 0 <= poly_accr_bound p a r.
Proof. by rewrite ltrW // poly_accr_bound_gt0. Qed.

Lemma horner_crealP (p : {poly F}) (x : creal) :
  creal_axiom (fun i => p.[x i]).
Proof.
set a := x (cauchymod x 1).
apply: (@asympt2_mulRL (1 + poly_accr_bound p a 1)).
  by rewrite ltr_spaddl ?poly_accr_bound_ge0 ?ltr01.
(* exists (fun e => [CC x # e; x # 1])=> e i j /= e_gt0. *)
exists_big_enough m F.
  move=> e i j e_gt0 hi hj.
  rewrite (ler_lt_trans (@poly_accr_bound1P p a 1 _ _ _ _)) ?e_gt0 //.
  + by apply: ltrW; apply: cauchymodP; rewrite ?invr_gt0 ?ltr0n //; big.
  + by apply: ltrW; apply: cauchymodP; rewrite ?invr_gt0 ?ltr0n //; big.
  apply: (@ler_lt_trans _ (e * poly_accr_bound p a 1)).
    rewrite ler_wpmul2r ?poly_accr_bound_ge0 ?ltr01 // ltrW // cauchymodP //;
    by big.
  by rewrite ltr_pmul2l // ltr_spaddl ?ltr01 ?poly_accr_bound_ge0.
by close.
Qed.
Definition horner_creal (p : {poly F}) (x : creal) := CReal (horner_crealP p x).
Local Notation "p .[ x ]" := (horner_creal p x) : creal_scope.

CoInductive alg_creal := AlgCReal {
  creal_of_alg :> creal;
  poly_of_alg_creal : {poly F};
  _ : monic poly_of_alg_creal;
  _ : poly_of_alg_creal.[creal_of_alg] == 0
}.

CoInductive alg_dom := AlgDom {
  poly_of_alg : {poly F};
  center_alg : F;
  radius_alg : F;
  _ : monic poly_of_alg;
  _ : radius_alg >= 0;
  _ : poly_of_alg.[center_alg - radius_alg]
      * poly_of_alg.[center_alg + radius_alg] <= 0
}.

Lemma radius_alg_ge0 x : 0 <= radius_alg x. Proof. by case: x. Qed.

Lemma monic_poly_of_alg x : monic (poly_of_alg x). Proof. by case: x. Qed.

Lemma alg_domP x : (poly_of_alg x).[center_alg x - radius_alg x]
  * (poly_of_alg x).[center_alg x + radius_alg x] <= 0.
Proof. by case: x. Qed.

Definition alg_dom' := seq F.

Definition encode_alg_dom (x : alg_dom) : alg_dom' :=
  [:: center_alg x, radius_alg x & (poly_of_alg x)].

Definition decode_alg_dom  (x : alg_dom') : option alg_dom :=
  if x is [::r, c & p'] then let p := Poly p' in
      if (boolP (monic p), boolP (r >= 0), boolP (p.[c - r] * p.[c + r] <= 0))
        is (AltTrue monic_p, AltTrue r_gt0, AltTrue hp)
        then Some (AlgDom monic_p r_gt0 hp)
        else None
    else None.

Lemma encode_alg_domK : pcancel encode_alg_dom decode_alg_dom.
Proof.
case=> p c r monic_p r_ge0 hp /=; rewrite polyseqK.

Admitted.

Definition alg_dom_EqMixin := PcanEqMixin encode_alg_domK.
Canonical alg_dom_eqType := EqType alg_dom alg_dom_EqMixin.

Definition alg_dom_ChoiceMixin := PcanChoiceMixin encode_alg_domK.
Canonical alg_dom_choiceType := ChoiceType alg_dom alg_dom_ChoiceMixin.

Fixpoint to_alg_creal_of (p : {poly F}) (c r : F) (i : nat) : F :=
  match i with
    | 0 => c
    | i.+1 =>
      let c' := to_alg_creal_of p c r i in
        if p.[c' - r / 2%:R ^+ i] * p.[c'] <= 0
          then c' - r / 2%:R ^+ i.+1
          else c' + r / 2%:R ^+ i.+1
  end.


Lemma to_alg_creal_of_recP p c r i : 0 <= r ->
  `|to_alg_creal_of p c r i.+1 - to_alg_creal_of p c r i| <= r * 2%:R ^- i.+1.
Proof.
move=> r_ge0 /=; case: ifP=> _; rewrite addrAC subrr add0r ?absrN ger0_abs //;
by rewrite mulr_ge0 ?invr_ge0 ?exprn_ge0 ?ler0n.
Qed.

Lemma to_alg_creal_ofP p c r i j : 0 <= r -> (i <= j)%N ->
  `|to_alg_creal_of p c r j - to_alg_creal_of p c r i| <= r * 2%:R ^- i.
Proof.
move=> r_ge0 leij; pose r' := r * 2%:R ^- j * (2%:R ^+ (j - i) - 1).
rewrite (@ler_trans _ r') //; last first.
  rewrite /r' -mulrA ler_wpmul2l // ler_pdivr_mull ?exprn_gt0 ?ltr0n //.
  rewrite -{2}(subnK leij) exprn_addr mulfK ?gtr_eqF ?exprn_gt0 ?ltr0n //.
  by rewrite ger_addl lerN10.
rewrite /r' subr_expn_1 addrK mul1r -{1 2}(subnK leij); set f := _  c r.
elim: (_ - _)%N=> [|k ihk]; first by rewrite subrr absr0 big_ord0 mulr0 lerr.
rewrite addSn big_ord_recl /= mulr_addr.
rewrite (ler_trans (ler_dist_add (f (k + i)%N) _ _)) //.
rewrite ler_add ?expr0 ?mulr1 ?to_alg_creal_of_recP // (ler_trans ihk) //.
rewrite exprSr invf_mul -!mulrA !ler_wpmul2l ?invr_ge0 ?exprn_ge0 ?ler0n //.
by rewrite -mulr_sumr ler_sum // => l _ /=; rewrite exprS mulKf ?pnatr_eq0.
Qed.

Hypothesis F_archi : forall x : F, { n : nat | x < 2%:R ^+ n }.
(* Definition modulus2n (w : F) n := w * 2%:R ^- (projT1 (F_archi (e^-1))). *)
Definition upper_nthroot x := projT1 (F_archi x).
Lemma upper_nthrootP x : x < 2%:R ^+ (upper_nthroot x).
Proof. by rewrite /upper_nthroot; case: F_archi. Qed.

Lemma alg_to_crealP (x : alg_dom) :
  creal_axiom (to_alg_creal_of (poly_of_alg x) (center_alg x) (radius_alg x)).
Proof.
(* exists (fun e => projT1 (F_archi (radius_alg x / e))). *)
pose_big_modulus m F.
  exists m=> e i j e_gt0 hi hj.
  wlog leij : i j {hi} hj / (j <= i)%N.
    move=> hwlog; case/orP: (leq_total i j)=> /hwlog; last exact.
    by rewrite distrC; apply.
  rewrite (ler_lt_trans (to_alg_creal_ofP _ _ _ _)) ?radius_alg_ge0 //.
  rewrite ltr_pdivr_mulr ?gtr0E // -ltr_pdivr_mull //.
  rewrite (ltr_le_trans (upper_nthrootP _)) //.
  by rewrite ler_eexpn2l ?ltr1n // (leq_trans _ hj) //; big.
by close.
Qed.
Definition alg_to_creal x := CReal (alg_to_crealP x).

Lemma neq_creal_horner p (x y : creal) : p.[x] != p.[y] -> x != y.
Proof.
move=> neq_px_py.
pose d := lbound neq_px_py.
pose_big_enough i.
  pose k := 2%:R + poly_accr_bound p (y i) d.
  have /andP[d_gt0 k_gt0] : (0 < d) && (0 < k).
    rewrite ?(ltr_spaddl, poly_accr_bound_ge0);
    by rewrite ?ltr0n ?ltrW ?ltr01 ?lbound_gt0.
  pose_big_enough j.
    apply: (@neq_crealP (d / k) j j); do ?by big.
      by rewrite ?(pmulr_lgt0, invr_gt0, ltr0n).
    rewrite ler_pdivr_mulr //.
    have /(_ j) // := (lbound_of neq_px_py); big.
    big=> /(_ isT) /(_ isT).
    apply: contraLR; rewrite -!ltrNge=> hxy.
    rewrite (ler_lt_trans (@poly_accr_bound1P _ (y i) d _ _ _ _)) //.
    * by rewrite ltrW // cauchymodP //; big.
    * rewrite (ler_trans (ler_dist_add (y j) _ _)) //.
      rewrite [d](splitf 2) /= ler_add ?ltrW //; last first.
        by rewrite cauchymodP ?pmulr_rgt0 ?invr_gt0 ?ltr0n //; big.
      rewrite ltr_pdivl_mulr ?ltr0n // (ler_lt_trans _ hxy) // ler_wpmul2l //.
     by rewrite ler_paddr // poly_accr_bound_ge0.
   rewrite (ler_lt_trans _ hxy) // ler_wpmul2l ?absr_ge0 //.
   by rewrite ler_paddl // ?ler0n.
 by close.
by close.
Qed.

Lemma eq_creal_horner p (x y : creal) : x == y -> p.[x] == p.[y].
Proof. by move=> hxy /neq_creal_horner. Qed.

Lemma exp2k_crealP : creal_axiom (fun i => 2%:R ^- i).
Proof.
(* exists (fun e => projT1 (F_archi (1 / e))). *)
pose_big_modulus m F.
  exists m=> e i j e_gt0 hi hj.
  wlog leij : i j {hj} hi / (i <= j)%N.
    move=> hwlog; case/orP: (leq_total i j)=> /hwlog; first exact.
    by rewrite distrC; apply.
  rewrite ger0_abs ?subr_ge0; last first.
    by rewrite ?ler_pinv -?topredE /= ?gtr0E // ler_eexpn2l ?ltr1n.
  rewrite -(@ltr_pmul2l _ (2%:R ^+ i )) ?gtr0E //.
  rewrite mulr_subr mulfV ?gtr_eqF ?gtr0E //.
  rewrite (@ler_lt_trans _ 1) // ?ger_addl ?oppr_le0 ?mulr_ge0 ?ger0E //.
  rewrite -ltr_pdivr_mulr // mul1r (ltr_le_trans (upper_nthrootP _)) //.
  by rewrite ler_eexpn2l ?ltr1n //; big.
by close.
Qed.
Definition exp2k_creal := CReal exp2k_crealP.

Lemma exp2k_creal_eq0 : exp2k_creal == 0.
Proof.
apply: eq_crealP; exists (fun e => projT1 (F_archi (1 / e))).
move=> e i e_gt0; case: F_archi=> n /=.
rewrite ltr_pdivr_mulr // -ltr_pdivr_mull ?exprn_gt0 ?ltr0n // mulr1.
move=> he hni; rewrite subr0 ger0_abs ?invr_ge0 ?exprn_ge0 ?ler0n //.
rewrite (ler_lt_trans _ he) // ler_pinv -?topredE /= ?exprn_gt0 ?ltr0n //.
by rewrite ler_eexpn2l ?ltr1n.
Qed.

Import Setoid Relation_Definitions.

Add Relation creal eq_creal
  reflexivity proved by eq_creal_refl
  symmetry proved by eq_creal_sym
  transitivity proved by eq_creal_trans
as eq_creal_rel.

Add Morphism add_creal with
  signature eq_creal ==> eq_creal ==> eq_creal as add_creal_morph.
Proof.
move=> x y eq_xy z t eq_zt; apply: eq_crealP.
exists_big_enough m F.
  move=> e i e_gt0 hi; rewrite oppr_add addrA [X in X + _]addrAC -addrA.
  rewrite (ler_lt_trans (ler_abs_add _ _)) // [e](splitf 2) /=.
  by rewrite ltr_add ?eqmodP ?pmulr_rgt0 ?invr_gt0 ?ltr0n //; big.
by close.
Qed.

Add Morphism opp_creal with
  signature eq_creal ==> eq_creal as opp_creal_morph.
Proof.
move=> x y /asympt_eq [m hm]; apply: eq_crealP; exists m.
by move=> e i e_gt0 hi /=; rewrite -oppr_add absrN hm.
Qed.

Add Morphism mul_creal with
  signature eq_creal ==> eq_creal ==> eq_creal as mul_creal_morph.
Proof.
move=> x y eq_xy z t eq_zt; apply: eq_crealP.
exists_big_enough m F.
  move=> e i e_gt0 hi.
  rewrite (ler_lt_trans (ler_dist_add (y i * z i) _ _)) //.
  rewrite -mulr_subl -mulr_subr !absrM [e](splitf 2) ltr_add //.
  have /ler_wpmul2l /ler_lt_trans-> // := uboundP z i.
    by rewrite absr_ge0.
  rewrite -ltr_pdivl_mulr ?ubound_gt0 ?eqmodP //; do ?by big.
    by rewrite !pmulr_rgt0 ?invr_gt0 ?ubound_gt0 ?ltr0n.
  rewrite mulrC; have /ler_wpmul2l /ler_lt_trans-> // := uboundP y i.
    by rewrite absr_ge0.
  rewrite -ltr_pdivl_mulr ?ubound_gt0 ?eqmodP //; do ?by big.
  by rewrite !pmulr_rgt0 ?invr_gt0 ?ubound_gt0 ?ltr0n.
by close.
Qed.

Add Morphism horner_creal with
  signature (@eq _) ==> eq_creal ==> eq_creal as horner_creal_morph.
Proof. exact: eq_creal_horner. Qed.

Add Morphism lt_creal with
  signature eq_creal ==> eq_creal ==> iff as lt_creal_morph.
Proof.
move=> x y eq_xy z t eq_zt.
wlog lxz : x y z t eq_xy eq_zt / (x < z)%CR.
  move=> hwlog; split=> h1; move: (h1) => /hwlog; apply=> //;
  by apply: eq_creal_sym.
split=> // _.
pose e' := diff lxz / 4%:R.
have e'_gt0 : e' > 0 by rewrite pmulr_rgt0 ?gtr0E ?diff_gt0.
have le_zt : (z <= t)%CR by apply: eq_le_creal.
have le_xy : (y <= x)%CR by apply: eq_le_creal; apply: eq_creal_sym.
pose_big_enough i.
  apply: (@lt_crealP e' i i)=> //; do ?by big.
  rewrite ltrW // -(ltr_add2r e').
  rewrite (ler_lt_trans _ (@lemodP _ _ le_zt _ _ _ _)) //; last by big.
  rewrite -addrA (monoLR (@addrNK _ _) (@ler_add2r _ _)) ltrW //.
  rewrite (ltr_le_trans (@lemodP _ _ le_xy e' _ _ _)) //; first by big.
  rewrite -(monoLR (@addrNK _ _) (@ler_add2r _ _)) ltrW //.
  rewrite (ltr_le_trans _ (diff_of lxz)) //; do ?by big.
  rewrite -addrA ler_lt_add // /e' -!mulr_addr gtr_pmulr ?diff_gt0 //.
  by rewrite [X in _ < X](splitf 4) /=  mul1r !ltr_addr ?gtr0E.
by close.
Qed.

Add Morphism le_creal with
  signature eq_creal ==> eq_creal ==> iff as le_creal_morph.
Proof. by move=> x y exy z t ezt; rewrite /le_creal exy ezt. Qed.

Lemma neq_ltVgt (x y : creal) : x != y -> {(x < y)%CR} + {(y < x)%CR}.
Proof.
move=> neq_xy; pose_big_enough i.
  have := (@lboundP _ _ neq_xy i); do ?big; move=> /(_ isT) /(_ isT).
  have [le_xy|/ltrW le_yx'] := lerP (x i) (y i).
    rewrite ler0_abs ?subr_le0 // oppr_sub -(ler_add2r (x i)) ?addrNK addrC.
    by move=> /lt_crealP; rewrite ?lbound_gt0; do ?big; do ?move/(_ isT); left.
  rewrite ger0_abs ?subr_ge0 // -(ler_add2r (y i)) ?addrNK addrC.
  by move=> /lt_crealP; rewrite ?lbound_gt0; do ?big; do ?move/(_ isT); right.
by close.
Qed.

Lemma lt_neq (x y : creal) : (x < y -> x != y)%CR.
Proof.
move=> lxy; pose_big_enough i.
  apply: (@neq_crealP (diff lxy) i i); rewrite ?diff_gt0 //; do ?by big.
  rewrite distrC ler_absr (monoRL (addrK _) (ler_add2r _)) addrC.
  by rewrite (diff_of lxy); do ?big.
by close.
Qed.

Lemma gt_neq (x y : creal) : (y < x -> x != y)%CR.
Proof. by move/lt_neq /neq_creal_sym. Qed.

Add Morphism neq_creal with
  signature eq_creal ==> eq_creal ==> iff as neq_creal_morph.
Proof.
move=> x y eq_xy z t eq_zt; split=> /neq_ltVgt [].
+ by rewrite eq_xy eq_zt=> /lt_neq.
+ by rewrite eq_xy eq_zt=> /gt_neq.
+ by rewrite -eq_xy -eq_zt=> /lt_neq.
by rewrite -eq_xy -eq_zt=> /gt_neq.
Qed.

Lemma add_creal0 x : x + 0 == x.
Proof.
apply: eq_crealP; exists (fun _ => 0%N).
by move=> e i e_gt0 _; rewrite /= addr0 subrr absr0.
Qed.

Lemma mul_creal0 x : x * 0 == 0.
apply: eq_crealP; exists (fun _ => 0%N).
by move=> e i e_gt0 _; rewrite /= mulr0 subrr absr0.
Qed.

Lemma opp_creal0 : - 0 == 0.
Proof.
apply: eq_crealP; exists (fun _ => 0%N).
by move=> e i e_gt0 _; rewrite /= subr0 oppr0 absr0.
Qed.

Lemma horner_crealM (p q : {poly F}) (x : creal) :
  ((p * q).[x] == p.[x] * q.[x])%CR.
Proof.
apply: eq_crealP; exists (fun _ => 0%N).
by move=> e i e_gt0 _; rewrite /= horner_mul subrr absr0.
Qed.

Lemma to_alg_crealP (x : alg_dom) : (poly_of_alg x).[alg_to_creal x] == 0.
Proof.
set u := alg_to_creal _; set p := poly_of_alg _.
pose r := radius_alg x; pose cr := cst_creal r.
have: ((p).[u - cr * exp2k_creal] *  (p).[u + cr * exp2k_creal] <= 0)%CR.
  apply: (@le_crealP 0%N)=> i _ /=.
  rewrite -/p -/r; set c := center_alg _.
  elim: i=> /= [|i].
    by rewrite !expr0 divr1 alg_domP.
  set c' := to_alg_creal_of _ _ _=> ihi.
  have [] := lerP (_ * p.[c' i]).
    rewrite addrNK -addrA -oppr_add -mulr2n -[_ / _ *+ _]mulr_natr.
    by rewrite -mulrA exprSr invf_mul mulfVK ?pnatr_eq0.
  rewrite addrK -addrA -mulr2n -[_ / _ *+ _]mulr_natr.
  rewrite -mulrA exprSr invf_mul mulfVK ?pnatr_eq0 // => /ler_pmul2l<-.
  rewrite mulr0 mulrCA !mulrA [X in X * _]mulrAC -mulrA.
  by rewrite mulr_ge0_le0 // -expr2 exprn_even_ge0.
rewrite exp2k_creal_eq0 mul_creal0 opp_creal0 add_creal0.
move=> hu pu0; apply: hu; pose e := (lbound pu0).
pose_big_enough i.
  apply: (@lt_crealP (e * e) i i); do ?by big.
    by rewrite !pmulr_rgt0 ?invr_gt0 ?ltr0n ?lbound_gt0.
  rewrite add0r [u]lock /= -!expr2.
  rewrite -[_.[_] ^+ _]ger0_abs ?exprn_even_ge0 // absrX.
  rewrite ler_pexpn2r -?topredE /= ?(ltrW (lbound_gt0 _)) ?absr_ge0 //.
  by rewrite -lock (ler_trans _ (lbound0_of pu0)) //; do ?big.
by close.
Qed.

Definition to_alg_creal (x : alg_dom) :=
  AlgCReal (monic_poly_of_alg x) (@to_alg_crealP x).

Lemma mul_creal_neq0 x y : x != 0 -> y != 0 -> x * y != 0.
Proof.
move=> x_neq0 y_neq0.
pose d := lbound x_neq0 * lbound y_neq0.
have d_gt0 : 0 < d by rewrite pmulr_rgt0 lbound_gt0.
pose_big_enough i.
  apply: (@neq_crealP d i i)=> //; do ?by big.
  rewrite subr0 absrM.
  rewrite (@ler_trans _ (`|x i| * lbound y_neq0)) //.
    by rewrite ler_wpmul2r ?(ltrW (lbound_gt0 _)) // lbound0P; do ?big.
  by rewrite ler_wpmul2l ?absr_ge0 // lbound0P; do ?big.
by close.
Qed.

Require Import polydiv polyorder.

Lemma coprimep_bezout (p q : {poly F}) : coprimep p q ->
  {u : {poly F} & { v : {poly F} | u * p + v * q = 1} }.
Proof.
move/coprimep_bezout=> hpq.
have : exists uv, uv`_0 * p + uv`_1 * q %= 1.
  by move: hpq=> [u [v huv]]; exists [:: u; v].
move=> /sigW[uv huv].
admit.
Qed.

Lemma mul_neq0_creal x y : x * y != 0 -> y != 0.
Proof.
move=> xy_neq0.
pose_big_enough i.
  apply: (@neq_crealP ((ubound x)^-1 * lbound xy_neq0) i i); do ?by big.
    by rewrite pmulr_rgt0 ?invr_gt0 ?lbound_gt0 ?ubound_gt0.
  rewrite subr0 ler_pdivr_mull ?ubound_gt0 //.
  have /(_ i)-> := (ler_trans (lbound0_of xy_neq0))=> //; do ?by big.
  by rewrite absrM ler_wpmul2r ?absr_ge0 ?uboundP.
by close.
Qed.

Lemma poly_mul_creal_eq0_coprime p q x :
  coprimep p q ->
  p.[x] * q.[x] == 0 -> {p.[x] == 0} + {q.[x] == 0}.
Proof.
move=> /coprimep_bezout [u [v hpq]].
pose_big_enough i.
  have := (erefl ((1 : {poly F}).[x i])).
  rewrite -{1}hpq /= horner_add hornerC.
  set upxi := (u * _).[_].
  move=> hpqi.
  have [p_small|p_big] := lerP `|upxi| 2%:R^-1=> pqx0; [left|right].
    move=> px0; apply: pqx0; apply: mul_creal_neq0=> //.
    apply: (@mul_neq0_creal v.[x]).
    apply: (@neq_crealP 2%:R^-1 i i); rewrite ?gtr0E //; do ?by big.
    rewrite /= subr0 -horner_mul -(ler_add2l `|upxi|).
    rewrite (ler_trans _ (ler_abs_add _ _)) // hpqi absr1.
    rewrite (monoLR (addrNK _) (ler_add2r _)).
    by rewrite {1}[1](splitf 2) /= mul1r addrK.
  move=> qx0; apply: pqx0; apply: mul_creal_neq0=> //.
  apply: (@mul_neq0_creal u.[x]).
  apply: (@neq_crealP 2%:R^-1 i i); rewrite ?gtr0E //; do ?by big.
  by rewrite /= subr0 -horner_mul ltrW.
by close.
Qed.

Lemma poly_mul_creal_eq0 p q x :
  p.[x] * q.[x] == 0 -> {p.[x] == 0} + {q.[x] == 0}.
Proof.
Admitted.

Lemma monic_poly_of_alg_creal x : monic (poly_of_alg_creal x).
Proof. by case: x. Qed.

Lemma root_poly_of_alg_creal x : (poly_of_alg_creal x).[x] == 0.
Proof. by case: x. Qed.

Definition poly_accr_bound2 (p : {poly F}) (a r : F) : F
  := (maxr 1 (2%:R * r)) ^+ (size p).-2
  * (1 + \sum_(i < (size p).-2) poly_bound p^`N(i.+2) a r).

Lemma poly_accr_bound2_gt0 p a r : 0 < poly_accr_bound2 p a r.
Proof.
rewrite /poly_accr_bound pmulr_rgt0 //.
  rewrite ltr_paddr ?ltr01 //.
  by rewrite sumr_ge0 // => i; rewrite poly_bound_ge0.
by rewrite exprn_gt0 // ltr_maxr ltr01 pmulr_rgt0 ?ltr0n.
Qed.

Lemma poly_accr_bound2_ge0 p a r : 0 <= poly_accr_bound2 p a r.
Proof. by rewrite ltrW // poly_accr_bound2_gt0. Qed.

Lemma poly_accr_bound2P p (a r x y : F) : (x != y)%B ->
  `|x - a| <= r ->  `|y - a| <= r ->
  `|(p.[y] - p.[x]) / (y - x) - p^`().[x]|
    <= `|y - x| * poly_accr_bound2 p a r.
Proof.
have [|r_lt0] := lerP 0 r; last first.
  by move=> _ hr; have := ler_lt_trans hr r_lt0; rewrite absr_lt0.
rewrite ler_eqVlt=> /orP[/eqP->|r_gt0].
  rewrite !absr_le0 !subr_eq0.
  by move=> nxy /eqP xa /eqP xb; rewrite xa xb eqxx in nxy.
move=> neq_xy hx hy.
rewrite mulrA mulr_addr mulr1 ler_paddl ?mulr_ge0 ?absr_ge0 //=.
  by rewrite exprn_ge0 ?ler_maxr ?mulr_ge0 ?ger0E ?ltrW.
rewrite -{1}(addNKr x y) [- _ + _]addrC /= -mulrA.
rewrite nderiv_taylor; last exact: mulrC.
have [->|p_neq0] := eqVneq p 0.
  by rewrite derivC !horner0 size_poly0 !(big_ord0, subrr, mul0r) absr0 !mulr0.
rewrite -[size _]prednK ?lt0n ?size_poly_eq0 //.
rewrite big_ord_recl expr0 mulr1 nderivn0 /= -size_deriv.
have [->|p'_neq0] := eqVneq p^`() 0.
  by rewrite horner0 size_poly0 !big_ord0 addr0 !(subrr, mul0r) absr0 !mulr0.
rewrite -[size _]prednK ?lt0n ?size_poly_eq0 // big_ord_recl expr1.
rewrite addrAC subrr add0r mulr_addl mulfK; last by rewrite subr_eq0 eq_sym.
rewrite nderivn1 addrAC subrr add0r -mulr_sumr absrM absrV.
rewrite ler_pdivr_mulr ?absr_gt0; last by rewrite subr_eq0 eq_sym.
rewrite mulrAC -expr2 mulrC -mulr_suml.
have := ler_trans (ler_abs_sum _ _ _); apply.
rewrite ler_sum // => i _ /=; rewrite /bump /= !add1n.
rewrite absrM absrX 3!exprSr expr1 !mulrA !ler_wpmul2r ?absr_ge0 //.
suff /ler_wpmul2l /ler_trans :
  `|(y - x)| ^+ i <=  maxr 1 (2%:R * r) ^+ (size p^`()).-1.
  apply; rewrite ?absr_ge0 // mulrC ler_wpmul2l ?poly_boundP //.
  by rewrite ?exprn_ge0 // ler_maxr ler01 mulr_ge0 ?ler0n ?ltrW.
case: maxrP=> hr.
  rewrite exp1rn exprn_ile1 ?absr_ge0 //.
  rewrite (ler_trans (ler_dist_add a _ _)) // addrC distrC.
  by rewrite (ler_trans _ hr) // mulr_addl ler_add ?mul1r.
rewrite (@ler_trans _ ((2%:R * r) ^+ i)) //.
  rewrite @ler_expn2r -?topredE /= ?absr_ge0 ?mulr_ge0 ?ler0n //.
    by rewrite ltrW.
  rewrite (ler_trans (ler_dist_add a _ _)) // addrC distrC.
  by rewrite mulr_addl ler_add ?mul1r.
by rewrite ler_eexpn2l // ltnW.
Qed.

Definition accr_pos p (a r : F) :=
  { k | 0 < k & forall x y, (x != y)%B ->
    `|x - a| <= r -> `|y - a| <= r -> (p.[x] - p.[y]) / (x - y) > k }.

Definition accr_neg p (a r : F) :=
  { k | 0 < k & forall x y, (x != y)%B ->
    `|x - a| <= r -> `|y - a| <= r -> (p.[x] - p.[y]) / (x - y) < - k }.

Definition strong_mono p (a r : F) := (accr_pos p a r + accr_neg p a r)%type.

Lemma accr_pos_incr p a r : accr_pos p a r ->
  forall x y, `|x - a| <= r -> `|y - a| <= r -> (p.[x] <= p.[y]) = (x <= y).
Proof.
move=> [k k_gt0 hk] x y hx hy.
have [->|neq_xy] := eqVneq x y; first by rewrite !lerr.
have hkxy := hk _ _ neq_xy hx hy.
have := ltr_trans k_gt0 hkxy.
have [lpxpy|lpypx|->] := ltrgtP p.[x] p.[y].
+ by rewrite nmulr_rgt0 ?subr_lt0 // ?invr_lt0 subr_lt0=> /ltrW->.
+ by rewrite pmulr_rgt0 ?subr_gt0 // ?invr_gt0 subr_gt0 lerNgt=> ->.
by rewrite subrr mul0r ltrr.
Qed.

Lemma accr_neg_decr p a r : accr_neg p a r ->
  forall x y, `|x - a| <= r -> `|y - a| <= r -> (p.[x] <= p.[y]) = (y <= x).
Proof.
move=> [k]; rewrite -oppr_lt0=> Nk_lt0 hk x y hx hy.
have [->|neq_xy] := eqVneq x y; first by rewrite !lerr.
have hkxy := hk _ _ neq_xy hx hy.
have := ltr_trans hkxy  Nk_lt0.
have [lpxpy|lpypx|->] := ltrgtP p.[x] p.[y].
+ by rewrite nmulr_rlt0 ?subr_lt0 // ?invr_gt0 subr_gt0=> /ltrW->.
+ by rewrite pmulr_rlt0 ?subr_gt0 // ?invr_lt0 subr_lt0 lerNgt=> ->.
by rewrite subrr mul0r ltrr.
Qed.

Lemma coprimep_root (p q : {poly F}) x :
  coprimep p q -> p.[x] == 0 -> q.[x] != 0.
Proof.
move=> /coprimep_bezout [u [v hpq]] px0.
have upx_eq0 : u.[x] * p.[x] == 0.
  by rewrite px0 mul_creal0; apply: eq_creal_refl.
pose_big_enough i.
  have := (erefl ((1 : {poly F}).[x i])).
  rewrite -{1}hpq /= horner_add hornerC.
  set upxi := (u * _).[_]; move=> hpqi.
  apply: (@neq_crealP ((ubound v.[x])%CR^-1 / 2%:R) i i); do ?by big.
    by rewrite pmulr_rgt0 ?gtr0E // ubound_gt0.
  rewrite /= subr0 ler_pdivr_mull ?ubound_gt0 //.
  rewrite (@ler_trans _  `|(v * q).[x i]|) //; last first.
    by rewrite horner_mul absrM ler_wpmul2r ?absr_ge0 ?(uboundP v.[x]).
  rewrite -(ler_add2l `|upxi|) (ler_trans _ (ler_abs_add _ _)) // hpqi absr1.
  rewrite (monoLR (addrNK _) (ler_add2r _)).
  rewrite {1}[1](splitf 2) /= mul1r addrK ltrW // /upxi horner_mul.
  by rewrite (@eq0modP _ upx_eq0) ?gtr0E; do ?big.
by close.
Qed.

Lemma deriv_neq0_mono (p : {poly F}) (x : creal) : p^`().[x] != 0 ->
  { r : F & 0 < r &
    { i : nat & (cauchymod x r <= i)%N & (strong_mono p (x i) r)} }.
Proof.
move=> px_neq0.
wlog : p px_neq0 / (0 < p^`().[x])%CR.
  case/neq_ltVgt: (px_neq0)=> px_lt0; last exact.
  case/(_ (- p)).
  + pose_big_enough i.
      apply: (@neq_crealP (lbound px_neq0) i i); do ?by big.
        by rewrite lbound_gt0.
      rewrite /= derivN horner_opp subr0 absrN.
      by rewrite (lbound0_of px_neq0) //; big.
    by close.
  + pose_big_enough i.
      apply: (@lt_crealP (diff px_lt0) i i); do ?by big.
        by rewrite diff_gt0.
      rewrite /= add0r derivN horner_opp -subr_le0 opprK addrC.
      by rewrite (diff_of px_lt0) //; big.
    by close.
  move=> r r_ge0 [i hi [] [k k_gt0 hk]];
    exists r=> //; exists i=> //; [right|left];
    exists k=> // y z hyz hy hz; move: (hk _ _ hyz hy hz);
    by rewrite !horner_opp -oppr_add mulNr ltr_oppr ?opprK.
move=> px_gt0.
pose b1 := poly_accr_bound p^`() 0 (1 + ubound x).
pose b2 := poly_accr_bound2 p 0 (1 + ubound x).
pose r := minr 1 (minr
  (diff px_gt0 / 4%:R / b1)
  (diff px_gt0 / 4%:R / b2 / 2%:R)).
exists r.
  rewrite !ltr_minr ?ltr01 ?pmulr_rgt0 ?gtr0E ?diff_gt0;
  by rewrite ?poly_accr_bound2_gt0 ?poly_accr_bound_gt0.
pose_big_enough i.
  exists i; first by big.
  left; exists (diff px_gt0 / 4%:R).
    by rewrite pmulr_rgt0 ?gtr0E ?diff_gt0.
  move=> y z neq_yz hy hz.
  have := (@poly_accr_bound1P p^`() 0 (1 + ubound x) (x i) z).
  have := @poly_accr_bound2P p 0 (1 + ubound x) z y; rewrite eq_sym !subr0.
  rewrite neq_yz ?ler01 ?(ltrW (ubound_gt0 _))=> // /(_ isT).
  rewrite (@ler_trans _ (r + `|x i|)); last 2 first.
  + rewrite (monoRL (addrNK _) (ler_add2r _)).
    by rewrite (ler_trans (ler_sub_dist _ _)).
  + rewrite ler_add ?ler_minl ?lerr ?uboundP //.
  rewrite (@ler_trans _ (r + `|x i|)); last 2 first.
  + rewrite (monoRL (addrNK _) (ler_add2r _)).
    by rewrite (ler_trans (ler_sub_dist _ _)).
  + rewrite ler_add ?ler_minl ?lerr ?uboundP //.
  rewrite ler_paddl ?uboundP ?ler01 //.
  move=> /(_ isT isT); rewrite ler_distl=> /andP [haccr _].
  move=> /(_ isT isT); rewrite ler_distl=> /andP [hp' _].
  rewrite (ltr_le_trans _ haccr) // (monoRL (addrK _) (ltr_add2r _)).
  rewrite (ltr_le_trans _ hp') // (monoRL (addrK _) (ltr_add2r _)).
  rewrite (ltr_le_trans _ (diff0_of px_gt0)) //; do ?by big.
  rewrite {2}[diff _](splitf 4) /= -!addrA ltr_add2l ltr_spaddl //.
    by rewrite pmulr_rgt0 ?gtr0E ?diff_gt0.
  rewrite -/b1 -/b2 ler_add //.
    rewrite -ler_pdivl_mulr ?poly_accr_bound2_gt0 //.
    rewrite (@ler_trans _ (r * 2%:R)) //.
      rewrite (ler_trans (ler_dist_add (x i) _ _)) //.
        by rewrite mulr_addr mulr1 ler_add // distrC.
      by rewrite -ler_pdivl_mulr ?ltr0n // !ler_minl lerr !orbT.
    rewrite -ler_pdivl_mulr ?poly_accr_bound_gt0 //.
    by rewrite (@ler_trans _ r) // !ler_minl lerr !orbT.
by close.
Qed.

Lemma strong_mono_bound p a r : strong_mono p a r
  -> {k | 0 < k & forall x y, `|x - a| <= r -> `|y - a| <= r ->
    `| x - y | <= k * `| p.[x] - p.[y] | }.
Proof.
case=> [] [k k_gt0 hk]; exists k^-1; rewrite ?invr_gt0=> // x y hx hy;
have [->|neq_xy] := eqVneq x y; do ?[by rewrite !subrr absr0 mulr0];
move: (hk _ _ neq_xy hx hy); rewrite 1?ltr_oppr ler_pdivl_mull //;
rewrite -ler_pdivl_mulr ?absr_gt0 ?subr_eq0 // => /ltrW /ler_trans-> //;
by rewrite -absrV -absrM ler_absr lerr ?orbT.
Qed.

Lemma eq_creal_cst x y : reflect ((cst_creal x) == (cst_creal y)) (x == y).
Proof.
apply: (iffP idP); first by move/eqP->; apply: eq_creal_refl.
move=> eq_xy; apply: contraLR isT=> neq_xy /=.
pose_big_enough i.
  suff : `|x%:CR i - y%:CR i| < `|x - y| by rewrite ltrr.
  by rewrite eqmodP // ?absr_gt0 ?subr_eq0 //; big.
by close.
Qed.

Lemma le_creal_cst x y : reflect ((cst_creal x) <= (cst_creal y))%CR (x <= y).
Proof.
apply: (iffP idP)=> le_xy; first exact: (@le_crealP 0%N).
apply: contraLR isT; rewrite -ltrNge=> neq_xy /=.
pose_big_enough i.
  suff : x%:CR i < y%:CR i + (x - y) by rewrite addrCA subrr addr0 ltrr.
  by rewrite lemodP // ?subr_gt0 //; big.
by close.
Qed.

Lemma horner_creal_cst c x : c%:P.[x] == c%:CR.
Proof.
apply: eq_crealP; exists (fun _ => 0%N)=> e i e_gt0 _.
by rewrite /= hornerC subrr absr0.
Qed.

Lemma to_alg_dom_exists (x : alg_creal) :
  { y : alg_dom | to_alg_creal y == x }.
Proof.
pose p := poly_of_alg_creal x.
move: {2}(size p) (leqnn (size p))=> n.
elim: n x @p=> [x p|n ihn x p le_sp_Sn].
  rewrite leqn0 size_poly_eq0 /p => /eqP p_eq0.
  by have /monic_neq0 := monic_poly_of_alg_creal x; rewrite p_eq0 eqxx.
move: le_sp_Sn; rewrite leq_eqVlt.
have [|//|eq_sp_Sn _] := ltngtP.
  by rewrite ltnS=> /ihn ihnp _; apply: ihnp.
have px0 := @root_poly_of_alg_creal x; rewrite -/p in px0.
have [] := boolP (coprimep p p^`()).
  move=> /coprimep_root /(_ px0) /deriv_neq0_mono [r r_gt0 [i ir sm]].
  have p_chg_sign : p.[x i - r] * p.[x i + r] <= 0.
    have [/accr_pos_incr hp|/accr_neg_decr hp] := sm.
      have hpxj : forall j, (i <= j)%N ->
        (p.[x i - r] <= p.[x j]) * (p.[x j] <= p.[x i + r]).
        move=> j hj.
          suff:  p.[x i - r] <= p.[x j] <= p.[x i + r] by case/andP=> -> ->.
        rewrite !hp 1?addrAC ?subrr ?add0r ?absrN;
        rewrite ?(gtr0_abs r_gt0) //;
          do ?by rewrite ltrW ?cauchymodP ?(leq_trans _ hj).
        by rewrite -ler_distl ltrW ?cauchymodP ?(leq_trans _ hj).
      rewrite mulr_le0_ge0 //; apply/le_creal_cst; rewrite -px0;
      by apply: (@le_crealP i)=> h hj /=; rewrite hpxj.
    have hpxj : forall j, (i <= j)%N ->
      (p.[x i + r] <= p.[x j]) * (p.[x j] <= p.[x i - r]).
      move=> j hj.
        suff:  p.[x i + r] <= p.[x j] <= p.[x i - r] by case/andP=> -> ->.
      rewrite !hp 1?addrAC ?subrr ?add0r ?absrN;
      rewrite ?(gtr0_abs r_gt0) //;
        do ?by rewrite ltrW ?cauchymodP ?(leq_trans _ hj).
      by rewrite andbC -ler_distl ltrW ?cauchymodP ?(leq_trans _ hj).
    rewrite mulr_ge0_le0 //; apply/le_creal_cst; rewrite -px0;
    by apply: (@le_crealP i)=> h hj /=; rewrite hpxj.
  pose y := (AlgDom (monic_poly_of_alg_creal x) (ltrW r_gt0) p_chg_sign).
  have eq_py_px: p.[to_alg_creal y] == p.[x].
    by have := @to_alg_crealP y; rewrite /= -/p=> ->; apply: eq_creal_sym.
  exists y.
  move: sm=> /strong_mono_bound [k k_gt0 hk].
  rewrite -/p; apply: eq_crealP.
  exists_big_enough m F.
    move=> e j e_gt0 hj; rewrite (ler_lt_trans (hk _ _ _ _)) //.
    + rewrite (ler_trans (to_alg_creal_ofP _ _ _ (leq0n _))) ?(ltrW r_gt0) //.
      by rewrite expr0 divr1.
    + rewrite ltrW // cauchymodP //; do ?by big.
    rewrite -ltr_pdivl_mull //.
    by rewrite (@eqmodP _ _ eq_py_px) // ?pmulr_rgt0 ?invr_gt0 //; big.
  by close.
rewrite /coprimep; set d := gcdp _ _=> sd_neq1.
pose md : {poly F} := (lead_coef d)^-1 *: d.
pose q := p %/ md.
have ld_neq0 : lead_coef d != 0 :> F.
  rewrite lead_coef_eq0 gcdp_eq0 negb_and monic_neq0 //.
  by rewrite monic_poly_of_alg_creal.
have monic_md : monic md.
  by rewrite /monic /md -mul_polyC lead_coef_Imul lead_coefC mulVf.
have dvd_md_p : md %| p.
  by rewrite (@eqp_dvdl _ d) ?dvdp_gcdl ?eqp_mulC ?invr_eq0.
have eq_p_qmd: p = q * md.
  rewrite [p](divp_mon_spec _ monic_md).
  by move:dvd_md_p; rewrite /dvdp => /eqP->; rewrite addr0.
have monic_q : monic q.
  rewrite /monic /q -(inj_eq (@mulIf _ (lead_coef md) _)).
    rewrite -lead_coef_Imul mul1r.
    move: dvd_md_p; rewrite -dvdpP eq_sym=> /eqP->.
    by rewrite (eqP monic_md) exp1rn scale1r (eqP (monic_poly_of_alg_creal _)).
  by rewrite (eqP monic_md) oner_eq0.
have smd : (1 < size md)%N.
  rewrite ltn_neqAle eq_sym lt0n size_poly_eq0 monic_neq0 ?andbT //.
  by rewrite size_scaler ?invr_eq0.
move: (px0); rewrite eq_p_qmd=> qmdx_eq0.
have : (q.[x] * md.[x] == 0) by rewrite -horner_crealM.
case/poly_mul_creal_eq0=> [qx_eq0|mdx_eq0].
  have [/=|x' hx'] := ihn (AlgCReal monic_q qx_eq0).
    rewrite -ltnS -eq_sp_Sn // eq_p_qmd.
    rewrite size_proper_mul ?(eqP monic_q, eqP monic_md, mul1r, oner_eq0) //.
    by rewrite -(subnKC smd) !addSn add0n !addnS /= ltnS leq_addr.
  by exists x'; rewrite hx' /=; apply: eq_creal_refl.
have [/=|x' hx'] := ihn (AlgCReal monic_md mdx_eq0).
  rewrite size_scaler ?invr_eq0 //.
  rewrite (leq_trans (@size_dvdp _ _ p^`() _ _)) //.
  + rewrite -size_poly_eq0 size_deriv eq_sp_Sn /=.
    apply/negP=> /eqP n_eq0; move: eq_sp_Sn; rewrite n_eq0=> /eqP.
    move=> /size1P [c c_neq0 hp]; move: px0; rewrite hp /=.
    by rewrite horner_creal_cst; apply/eq_creal_cst.
  + by rewrite dvdp_gcdr.
  rewrite -ltnS (leq_trans (lt_size_deriv _)) ?monic_neq0 ?eq_sp_Sn //.
  by rewrite monic_poly_of_alg_creal.
by exists x'; rewrite hx' /=; apply: eq_creal_refl.
Qed.

Definition to_alg_dom x := projT1 (to_alg_dom_exists x).

Lemma to_alg_domP x : to_alg_creal (to_alg_dom x) == x.
Proof. by rewrite /to_alg_dom; case: to_alg_dom_exists. Qed.

Lemma creal_alg_comparison (x y : alg_creal) :
  {x == y} + {x != y}.
Proof.
pose p := poly_of_alg_creal x.
pose q := poly_of_alg_creal y.
move: {2}(_ + _)%N (leqnn (size p + size q))=> n.
elim: n x y @p @q => [x y p q|n ihn x y p q le_sp_Sn].
  rewrite leqn0 addn_eq0 !size_poly_eq0 /p /q.
  by rewrite -[_ && _]negbK negb_and !monic_neq0 ?monic_poly_of_alg_creal.
move: le_sp_Sn; rewrite leq_eqVlt.
have [|//|eq_sp_Sn _] := ltngtP.
  by rewrite ltnS=> /ihn ihnp _; apply: ihnp.
have px0 : p.[x] == 0 by apply: root_poly_of_alg_creal.
have qy0 : q.[y] == 0 by apply: root_poly_of_alg_creal.
have [cpq|] := boolP (coprimep p q).
  right; move: (cpq)=> /coprimep_root /(_ px0).
  rewrite -qy0=> neq_qx_qy.
  pose_big_enough i.
    apply: (@neq_crealP (lbound neq_qx_qy
      / poly_accr_bound q 0 (maxr (ubound x) (ubound y))) i i); do ?by big.
    + by rewrite ?pmulr_rgt0 ?invr_gt0 ?lbound_gt0 ?poly_accr_bound_gt0.
    rewrite ler_pdivr_mulr ?poly_accr_bound_gt0 //.
    rewrite (ler_trans _ (poly_accr_bound1P _ _ _));
    by rewrite ?subr0 ?ler_maxr ?uboundP ?orbT //; apply: lboundP; do ?big.
  by close.
Admitted.

Definition eq_alg_dom (x y : alg_dom) : bool :=
  creal_alg_comparison (to_alg_creal x) (to_alg_creal y).

Require Import generic_quotient.

Lemma eq_alg_domP (x y : alg_dom) :
  reflect (to_alg_creal x == to_alg_creal y) (eq_alg_dom x y).
Proof.
by rewrite /eq_alg_dom; case: creal_alg_comparison=> //= hx; constructor.
Qed.

Lemma eq_alg_dom_refl : ssrbool.reflexive eq_alg_dom.
Proof. by move=> x; apply/eq_alg_domP; apply eq_creal_refl. Qed.

Lemma eq_alg_dom_sym : ssrbool.symmetric eq_alg_dom.
Proof. by move=> x y; apply/eq_alg_domP/eq_alg_domP=> /eq_creal_sym. Qed.

Lemma eq_alg_dom_trans : ssrbool.transitive eq_alg_dom.
Proof.
move=> x y z /eq_alg_domP /eq_creal_trans hxy /eq_alg_domP /hxy hxz.
exact/eq_alg_domP.
Qed.

Canonical eq_alg_dom_rel :=
  EquivRel eq_alg_dom_refl eq_alg_dom_sym eq_alg_dom_trans.

Definition alg := [mod eq_alg_dom]%qT.

End Creals.
End Creals.

(* Canonical  *)

(* Section RealAlg. *)

(* Variable F : oFieldType. *)
(* Local Open Scope ring_scope. *)
(* Hypothesis F_archi : forall x : F, { n : nat | x < 2%:R ^+ n }. *)

(* Goal forall x y : Creals.alg F_archi, x == y -> x = y. *)