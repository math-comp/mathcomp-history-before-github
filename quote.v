(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Structure tProp := TProp {tProp_statement :> Prop; _ : tProp_statement}.
Lemma claim : forall P : tProp, P. Proof. by case. Qed.
Hint Resolve claim.

Canonical Structure True_tProp := TProp Logic.I.
Canonical Structure eq_tProp T (x : T) := TProp (erefl x).
Canonical Structure true_tProp := @TProp true (erefl _).
Canonical Structure and_tProp (P Q : tProp) :=
  TProp (conj (claim P) (claim Q)).

Delimit Scope n_ary_op_scope with QOP.
Delimit Scope quote_scope with QT.

Module Quotation.

Fixpoint n_ary n T := if n is n'.+1 then T -> n_ary n' T else T.
Notation "n .-ary" := (n_ary n) (at level 2, format "n .-ary") : type_scope.

CoInductive n_ary_op T := NaryOp n of n.-ary T.
Notation "f / n" := (@NaryOp _ n f) : n_ary_op_scope.
Definition bind_op T R (op : n_ary_op T) ifun : R :=
  let: NaryOp n f := op in ifun n f.

Structure type := Pack {sort :> Type; sym; _ : sym -> n_ary_op sort}.
Notation QuoteType sf := (Pack sf%QOP).
Definition symop T := let: Pack _ _ ops := T return sym T -> n_ary_op T in ops.

Inductive term S := Var of nat | App of S & seq (term S).

Lemma term_ind' : forall S (P : term S -> Type),
  (forall i, P (Var S i)) ->
  (forall s a, foldr prod True (map P a) -> P (App s a)) ->
  (forall t, P t).
Proof.
move=> S P P_V P_A; pose fix sz (t : term S) :=
  if t is App _ a then (foldr maxn 0 (map sz a)).+1 else 0.
move=> t; elim: {t}(sz t) {-2}t (leqnn (sz t)) => [|n IHn] [i | s a] //=.
rewrite ltnS => sz_a; apply: P_A; elim: a sz_a => //= t a IHa.
by rewrite leq_maxl; case/andP; move/IHn=> Pt; move/IHa.
Qed.

Bind Scope quote_scope with term.
Notation "''K_' i" := (Var _ i)
  (at level 8, i at level 2, format "''K_' i") : quote_scope.
Notation "''[' s x1 .. xn ]" := (App s (x1%QT :: .. [:: xn%QT] ..))
  (at level 0, s at level 2, x1, xn at level 8,
   format "''[' '[hv' s  x1  ..  xn ']' ]") : quote_scope.
Notation "''[' s ]" := (App s [::])
  (at level 0, s at level 2, format "''[' s ]") : quote_scope.

Section OneType.

Variable T : type.
Implicit Type P : Prop.
Implicit Type tP : tProp.

Definition Env := @id (seq T).

Fixpoint lookup i e : option T :=
  if i is i'.+1 then lookup i' (behead e) else ohead e.

Definition interp_app (iarg : term (sym T) -> option T) :=
  fix loop a n {struct a} : n.-ary T -> option T :=
  if n is n'.+1 return n.-ary T -> option T
  then fun f => if a is t :: a' then obind (loop a' n' \o f) (iarg t) else None
  else fun x => if a is [::] then Some x else None.

Fixpoint interp e t := match t with
 | Var i => lookup i e
 | App s a => bind_op (symop s) (interp_app (interp e) a)
 end.

Definition var_val := @id T.
Definition sym_val := var_val.
Definition op_val := sym_val.

Structure form e t P := Form {fval :> T; _ : P -> interp e t = Some fval}.
Lemma formP : forall e t tP (f : form e t tP), interp e t = Some (f : T).
Proof. by move=> e t tP [x <-]. Qed.

Structure store i x P := Store {stval; _ : P -> lookup i stval = Some x}.
Canonical Structure head_store x e :=
  @Store 0 x True (Env (x :: Env e)) (fun _ => erefl _).
Lemma tail_store_subproof : forall i x y e tP s,
  e = @stval i x tP s -> lookup i.+1 (y :: e) = Some x.
Proof. by move=> i x y _ tP [e /= <- //] ->. Qed.
Canonical Structure tail_store i x y e tP s :=
  Store (@tail_store_subproof i x y e tP s).

Lemma var_form_subproof : forall i x P (s : store i x P),
  P -> interp (stval s) 'K_i = Some (var_val x).
Proof. by move=> i x P []. Qed.
Canonical Structure var_form i x P s := Form (@var_form_subproof i x P s).

Lemma sym_form_subproof : forall e t tP (f : form e t tP) x,
  x = f :> T -> interp e t = Some (sym_val x).
Proof. by move=> e t tP f _ ->; exact: formP. Qed.

Canonical Structure sym_form e t tP f x :=
  Form (@sym_form_subproof e t tP f x).

Section OpForm.

Variables (s : sym T) (e : seq T).

Definition opform_axiom P a1 n (x1 : n.-ary T) :=
  P -> forall a, interp e (App s (catrev a a1)) = interp_app (interp e) a x1.

Structure opform a1 P :=
  OpForm { opfval :> T -> T; _ : @opform_axiom P a1 1 opfval }.

Lemma op_form_subproof : forall a1 t2 tP1 tP2 x1 x2 f1 f2,
  (x1, op_val x2) = (@opfval a1 tP1 f1, @fval e t2 tP2 f2) ->
  interp e (App s (catrev [::t2] a1)) = Some (op_val (x1 x2)).
Proof.
move=> a1 t2 tP1 tP2 _ x2 [x1 def_x1] [x2' def_x2'] [-> def_x2].
by rewrite [x2]def_x2 def_x1 /= ?def_x2'.
Qed.

Canonical Structure op_form a1 t2 tP1 tP2 x1 x2 f1 f2 :=
  Form (@op_form_subproof a1 t2 tP1 tP2 x1 x2 f1 f2).

Fixpoint nOpForm_type xaT (xa fa : xaT) a n :=
  if n is n'.+1 then
    forall x t tP (f : form e t tP),
      nOpForm_type (xa, op_val x) (fa, f : T) (t :: a) n'
  else opform a (xa = fa).

Definition nForm_type (ops : n_ary_op T):=
  if ops is (_/n.+1)%QOP then nOpForm_type 0 0 [::] n else form e '[s] True.
  
Definition nForm_rectype xaT (xa fa : xaT) a1 n :=
  forall x1, (opform_axiom (xa = fa) a1) n.+1 x1 -> nOpForm_type xa fa a1 n.

Lemma nForm_rec_subproof : forall xaT xa fa a1 n (x1 : n.+1.-ary T),
  forall x t tP (f : form e t tP), opform_axiom (xa = fa) a1 x1 ->
  opform_axiom ((xa, op_val x) = (fa : xaT, f : T)) (t :: a1) (x1 x).
Proof.
move=> xaT xa fa a1 n x1 x t tP f IHx [def_xa def_x] a.
by rewrite (IHx _ (t :: a)) //= [x]def_x (formP f).
Qed.

Fixpoint nForm_rec xaT xa fa a1 n : @nForm_rectype xaT xa fa a1 n :=
  if n is 0 return nForm_rectype _ _ _ n then fun _ IHx => OpForm IHx else
  fun _ IHx _ _ _ _ => nForm_rec (nForm_rec_subproof IHx).

Lemma nForm_base_subproof : forall n x,
  symop s = (x/n)%QOP -> opform_axiom (0 = 0) [::] x.
Proof. by move=> n x def_s _; rewrite /= def_s. Qed.

Lemma nForm_subproof : forall x,
  symop s = (x/0)%QOP -> True -> interp e '[s] = Some x.
Proof. by move=> x /= ->. Qed.

Definition nForm :=
  match symop s as ops return symop s = ops -> nForm_type ops with
  |  _/0   => fun def_s => Form (nForm_subproof def_s)
  | x/_.+1 => fun def_s => @nForm_rec _ _ _ _ _ x (nForm_base_subproof def_s)
  end%QOP (erefl _).

End OpForm.

Section GenSimp.

Variable simp : T -> seq T -> term (sym T) -> option T.

Definition simp_axiom := forall e t x0 x y,
  interp e t = Some x -> simp x0 e t = Some y -> x = y.

Hypothesis simpP : simp_axiom.

Structure post_opform e s a P P' := PostOpForm { pof_val :> opform e s a P }.

Canonical Structure process_post_opform e s a P tP x xP :=
  PostOpForm tP (@OpForm e s a P x xP).

Structure closed := Closed {closed_val :> seq T}.
Canonical Structure head_closed := Closed (Env [::]).
Canonical Structure tail_closed x (ce : closed) := Closed (x :: ce).
Inductive close : seq T -> Prop := Close (ce : closed) : close ce.
Canonical Structure close_tProp ce := TProp (Close ce).

Lemma simp_opform : forall e s a1 tP1 x2 t2 tP2,
  forall (f2 : form (Env e) t2 tP2) y,
  forall def_y :
    op_val x2 = f2 /\ close e /\ simp x2 e (App s (rev (t2 :: a1))) = Some y,
  forall (pp : forall P, P -> tProp) tP3,
  forall f1 : post_opform s (Env e) a1 tP1 (TProp def_y = pp _ (claim tP3)),
  f1 x2 = y.
Proof.
move=> e s a1 tP1 x2 t2 tP2 f2 y [def_x2 [_ def_y]] _ _ [[x1 /= def_x1]].
apply: simpP {y} def_y.
by rewrite (def_x1 _ [::t2]) //= (formP f2) // -def_x2.
Qed.

End GenSimp.

Fixpoint simp_term {S} (t : term S) := match t with
| App s a =>
  let ocons ot oa := obind (fun t' => omap (Cons _ t') oa) ot in
  omap (App s) (foldr ocons (Some [::]) (map simp_term a))
| _ => Some t
end.

Definition Econs := Cons.
Definition Etag of nat := @idfun.
Definition Enil := Nil.

Fixpoint simp_env {T'} e i :=
  if e is x :: e' then omap (Econs (Etag i x)) (simp_env e' i.+1)
  else Some (Enil T').

Notation "' 'K_' i := x" := (Etag i x)
  (at level 200, format "' 'K_' i  :=  x") : quote_tag_scope.
Arguments Scope Econs [type_scope quote_tag_scope _].

Notation "[ 'env' d1 ; .. ; d_n ]" := (Econs d1 .. (Econs d_n (Enil _)) ..)
  (at level 0, format "[ 'env' '['  d1 ; '/'  .. ; '/'  d_n ] ']'")
   : quote_scope.

Notation "[ 'env' ]" := (Enil _)
  (at level 0, format "[ 'env' ]") : quote_scope.

Definition unquote {x0} e t := odflt x0 (interp e t).
Arguments Scope unquote [_ quote_scope quote_scope].

Definition simp_quote x0 e t :=
  obind (fun e' => omap (@unquote x0 e') (simp_term t)) (simp_env e 0).

Lemma simp_quoteP : simp_axiom simp_quote.
Proof.
rewrite /simp_quote => e t x0 x y def_x.
have ->: simp_env e 0 = Some e.
  by elim: e {def_x} 0 => //= z e IHe i; rewrite IHe.
suffices ->: simp_term t = Some t.
  by rewrite /unquote; case: e def_x => /= [|z e] -> [].
elim/term_ind': t {x y x0 e def_x} => //= s.
by elim=> //= t a IHa [->]; move/IHa=> {IHa} /=; case: foldr => //= _ [->].
Qed.

Definition quote := simp_opform simp_quoteP.

End OneType.

End Quotation.

Canonical Structure Quotation.head_store.
Canonical Structure Quotation.tail_store.
Canonical Structure Quotation.var_form.
Canonical Structure Quotation.sym_form.
Canonical Structure Quotation.op_form.
Canonical Structure Quotation.head_closed.
Canonical Structure Quotation.tail_closed.
Canonical Structure Quotation.process_post_opform.
Canonical Structure Quotation.close_tProp.

Notation QuoteType sf := (Quotation.Pack sf%QOP).
Notation "f / n" := (@Quotation.NaryOp _ n f) : n_ary_op_scope.

Notation nForm := Quotation.nForm.

Notation "''K_' i" := (Quotation.Var _ i)
  (at level 8, i at level 2, format "''K_' i") : quote_scope.
Notation "''[' s x1 .. xn ]" :=
  (Quotation.App s (x1%QT :: .. [:: xn%QT] ..))
  (at level 0, s at level 2, x1, xn at level 8,
   format "''[' s '[hv'  x1 '/'  .. '/'  xn ']' ]") : quote_scope.
Notation "''[' s ]" := (Quotation.App s [::])
  (at level 0, s at level 2, format "''[' s ]") : quote_scope.
Notation "' 'K_' i := x" := (Quotation.Etag i x)
  (at level 200, format "' 'K_' i  :=  x") : quote_tag_scope.
Arguments Scope Quotation.Econs [type_scope quote_tag_scope _].
Notation "[ 'env' d1 ; .. ; d_n ]" :=
  (Quotation.Econs d1 .. (Quotation.Econs d_n (Quotation.Enil _)) ..)
  (at level 0, format "[ 'env' '['  d1 ; '/'  .. ; '/'  d_n ] ']'")
   : quote_scope.
Notation "[ 'env' ]" := (Quotation.Enil _)
  (at level 0, format "[ 'env' ]") : quote_scope.

Arguments Scope Quotation.unquote [_ quote_scope quote_scope].
Notation unquote e t := (Quotation.unquote e t%QT).
Definition quote := Quotation.quote.

CoInductive bool_sym := bTrue | bAnd.
Canonical Structure bool_quoteType :=
  QuoteType (fun s => match s with bTrue => true/0 | bAnd => andb/2 end).
Canonical Structure and_form := nForm bAnd.
Canonical Structure true_form := nForm bTrue.

Lemma try1 : forall b1 b2 b3 : bool,
  false && b1 && (b2 && true && b3) && (b2 && b1 && b2) = false && b2.
Proof.
move=> b1 b2 b3.
rewrite !quote.
done.
Qed.

Fixpoint bstore s bt := match bt with
| 'K_i => set_nth false s i true 
| '[bAnd t1 t2] => bstore (bstore s t1) t2
| _ => s
end%QT.

Fixpoint bread ot i s := match s with
| [::] => odflt '[bTrue] ot
| true :: s' => bread (Some (oapp (fun t => '[bAnd t 'K_i]) 'K_i ot)) i.+1 s'
| false :: s' => bread ot i.+1 s'
end%QT.

Fixpoint bnormed t i := match t with
| '[bAnd t' 'K_j] => (j > 0) && ((i == 0) || (i == j.+1)) && bnormed t' j
| 'K_j => (i <= 1) && (j == 0)
| '[bTrue] => i == 0
| _ => false
end%QT.

Definition bsimp_fn (x0 : bool) e t :=
  if bnormed t 0 then None else
  Quotation.interp e (bread None 0 (bstore [::] t)).

Lemma bsimpP : Quotation.simp_axiom bsimp_fn.
Proof.
pose oand ob1 ob2 := obind (fun b1 => omap (andb b1) ob2) ob1.
have [oaC oaA oaI]: [/\ commutative oand, associative oand & idempotent oand].
  by split; do 6?case=> //.
have oa1: left_id (Some true) oand by case=> [[]|].
rewrite /bsimp_fn => e t _ b b'; case: bnormed => //=.
set ie := Quotation.interp e; set s := [::] => def_b.
pose ir j s := ie (bread None j s).
suff{b'} storeP: ir 0 (bstore s t) = oand (ir 0 s) (Some b).
  by rewrite [ie _]storeP => [[]].
elim/Quotation.term_ind': t s => [i | op a IHa] /= s in b def_b *; last first.
  case: op def_b; first by case: a {IHa} => //= <-; rewrite oaC oa1.
  case: a IHa => //= t1; rewrite /ie /= -/ie; case: (ie _) => //= b1 [] //= t2.
  case: (ie t2) => //= b2 [] //= [IHb1 [IHb2 _]] [<-].
  by rewrite (IHb2 _ b2) // (IHb1 _ b1) // -oaA.
have irT: forall s' j, ir j (true :: s') = oand (ie 'K_j)%QT (ir j.+1 s').
  rewrite /ir /= => s' j; move: s' j ('K_j)%QT.
  by elim=> [|[|] s' IHs] j u; first 1 [rewrite oaC oa1] || rewrite !IHs -?oaA.
rewrite -{}def_b -{2}[i]addn0; elim: i 0 s => [|i IHi] j.
  case=> [|bj s]; first by rewrite oa1.
  by case: bj; rewrite !irT oaC // -oaA oaI.
rewrite addSnnS; case=> [|[|] s]; last exact: IHi.
  by rewrite /= -set_nth_nil [ir _ _]IHi.
by rewrite !irT IHi oaA.
Qed.

Definition bsimp := Quotation.simp_opform bsimpP.

Lemma try2 : forall b1 b2 b3,
  true && b1 && (b2 && b3) && (b2 && b1 && b2) = b1 && b2 && true && b3.
Proof.
move=> b1 b2 b3.
rewrite !bsimp.
done.
Qed.


