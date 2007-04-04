(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Set Implicit Arguments.
Unset Strict Implicit.

Module SsrSyntax.

Require Import Bool. (* For bool_scope delimiter 'bool'. *)

(* Declare Ssr keywords: 'is' 'by' 'of' '//' '/=' and '//='.                *)
(* We also declare the parsing level 8, as a workaround for a notation      *)
(* grammar factoring problem. Arguments of application-style notations      *)
(* (at level 10) should be declared at level 8 rather than 9 or the camlp4  *)
(* grammar will not factor properly.                                        *)

Reserved Notation "'(*' x 'is' y 'by' z 'of' '//' '/=' '//='" (at level 8).

(* Make the general "if" into a notation, so that we can override it below *)
(* The notations are "only parsing" because the Coq decompiler won't       *)
(* recognize the expansion of the boolean if; using the default printer    *)
(* avoids a spurrious trailing %GEN_IF.                                    *)

Delimit Scope general_if_scope with GEN_IF.

Notation "'if' c 'then' v1 'else' v2" :=
  (if c then v1 else v2)
  (at level 200, c, v1, v2 at level 200, only parsing) : general_if_scope.

Notation "'if' c 'return' t 'then' v1 'else' v2" :=
  (if c return t then v1 else v2)
  (at level 200, c, t, v1, v2 at level 200, only parsing) : general_if_scope.

Notation "'if' c 'as' x 'return' t 'then' v1 'else' v2" :=
  (if c as x return t then v1 else v2)
  (at level 200, c, t, v1, v2 at level 200, x ident, only parsing)
     : general_if_scope.

Open Scope general_if_scope.

(* Force boolean interpretation of simple if expressions.          *)

Delimit Scope boolean_if_scope with BOOL_IF.

Notation "'if' c 'return' t 'then' v1 'else' v2" :=
  (if c%bool is true return t then v1 else v2) : boolean_if_scope.

Notation "'if' c 'then' v1 'else' v2" :=
  (if c%bool is true return _ then v1 else v2) : boolean_if_scope.

Notation "'if' c 'as' x 'return' t 'then' v1 'else' v2" :=
  (if c%bool is true as x return t then v1 else v2) : boolean_if_scope.

(* Syntax for referring to canonical structures:                   *)
(*   {mytype as mystruct}                                          *)
(* denotes mytype_struct when mytype_struct : mystruct is a        *)
(* Canonical Structure that projects to mytype via the Sortclass   *)
(* coercion of the mystruct structure, i.e., such that we have     *)
(* mytype_struct : Type = mytype.                                  *)
(*  Although {mytype as mystruct} reduces (via simpl or /=) to     *)
(* mytype_struct, it does not actually denote mytype_struct, but   *)
(* a more complex term that gets displayed as                      *)
(*      mytype_struct (* mytype as mystruct *)                     *)

Module GetCanonical.

CoInductive phantom (t s : Type) (d : s) : Type := Phantom.

Definition get t s d (x : @phantom t s d) := let: Phantom := x in d.

End GetCanonical.

Notation "d '(*' t 'as' s '*)'" :=
  (@GetCanonical.get t s d _)
  (at level 10, t, s at level 200, format "d  '(*'  t  'as'  s  '*)'")
  : structure_scope.

Notation "{ t 'as' s }" :=
  (@GetCanonical.get t _ _ ((fun d : s => GetCanonical.Phantom d d) _))
  (at level 0, t at level 99, s at level 200)
   : structure_scope.

Delimit Scope structure_scope with STRUCT.
Open Scope structure_scope.

End SsrSyntax.

Export SsrSyntax.

Open Scope boolean_if_scope.

(* Internal tagging used by the implementation of the ssreflect elim. *)

Definition protect_term (A : Type) (x : A) : A := x.

(** Term tagging (user-level).                                              *)
(* We provide two strengths of term tagging :                               *)
(*  - (nosimpl t) simplifies to t EXCEPT in a definition; more precisely,   *)
(*    given Definition foo := (nosimpl bar), foo (or (foo t')) will NOT be  *)
(*    expanded by the simpl tactic unless it is in a forcing context (e.g., *)
(*    in match foo t' with ... end, foo t' will be reduced if this allows   *)
(*    match to be reduced. Note that nosimpl bar is simply notation for     *)
(*    a term that beta-iota reduces to bar; hence unfold foo will replace   *)
(*    foo by bar, and fold foo will replace bar by foo. A final warning:    *)
(*    nosimpl only works if no reduction is apparent in t; in particular    *)
(*    Definition foo x := nosimpl t. will usually not work.                 *)
(*  - (locked t) is provably equal to t, but is not convertible to t; it    *)
(*    provides support for abstract data types, and selective rewriting.    *)
(*    The equation t == (locked t) is provided as a lemma, but it should    *)
(*    only be used for selective rewriting (see below). For ADTs, the       *)
(*    unlock tactic should be used to remove locking.                       *)
(* locked is also used as a placeholder for the implementation of flexible  *)
(* matching.                                                                *)

Notation "'nosimpl' t" := (let: tt := tt in t) (at level 10, t at level 8).

Lemma master_key : unit. Proof. exact tt. Qed.

Definition locked A := let: tt := master_key in fun x : A => x.

Lemma lock : forall A x, x = locked x :> A.
Proof. rewrite /locked; case master_key; split. Qed.

(* Needed for locked predicates, in particular for eqType's. *)
Lemma not_locked_false_eq_true : locked false <> true.
Proof. rewrite -lock; discriminate. Qed.

(* The basic closing tactic "done".                                       *)
Ltac done :=
  trivial; hnf; intros; solve
   [ do ![solve [trivial | symmetry; trivial]
         | discriminate | contradiction | split]
   | case not_locked_false_eq_true; assumption
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end ].

(* The internal lemmas for the have tactics.                                *)

Definition ssr_have Plemma Pgoal (step : Plemma) rest : Pgoal := rest step.
Implicit Arguments ssr_have [Pgoal].

Definition ssr_suff Plemma Pgoal step (rest : Plemma) : Pgoal := step rest.
Implicit Arguments ssr_suff [Pgoal].

Definition ssr_wlog := ssr_suff.
Implicit Arguments ssr_wlog [Pgoal].

(* Internal  N-ary congruence lemma for the congr tactic *)

Fixpoint nary_congruence_statement (n : nat)
         : (forall B, (B -> B -> Prop) -> Prop) -> Prop :=
  match n with
  | O => fun k => forall B, k B (fun x1 x2 : B => x1 = x2)
  | S n' =>
    let k' A B e (f1 f2 : A -> B) :=
      forall x1 x2, x1 = x2 -> (e (f1 x1) (f2 x2) : Prop) in
    fun k => forall A, nary_congruence_statement n' (fun B e => k _ (k' A B e))
  end.

Lemma nary_congruence : forall n : nat,
 let k B e := forall y : B, (e y y : Prop) in nary_congruence_statement n k.
Proof.
move=> n k; have: k _ _ := _; rewrite {1}/k.
elim: n k  => [|n IHn] k Hk /= A; auto.
by apply: IHn => B e He; apply: Hk => f x1 x2 <-.
Qed.

(* View lemmas that don't use reflection.                       *)

Lemma iffLR : forall P Q, (P <-> Q) -> P -> Q. Proof. by move=> ? ? []. Qed.
Lemma iffRL : forall P Q, (P <-> Q) -> Q -> P. Proof. by move=> ? ? []. Qed.

Hint View iffLR|2 iffRL|2.

Unset Implicit Arguments.

