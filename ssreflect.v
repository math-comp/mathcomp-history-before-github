(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import Bool. (* For bool_scope delimiter 'bool'. *)

Set Implicit Arguments.
Unset Strict Implicit.

Module SsrSyntax.

(* Declare Ssr keywords: 'is' 'by' 'of' '//' '/=' and '//='.                *)
(* We also declare the parsing level 8, as a workaround for a notation      *)
(* grammar factoring problem. Arguments of application-style notations      *)
(* (at level 10) should be declared at level 8 rather than 9 or the camlp4  *)
(* grammar will not factor properly.                                        *)

Reserved Notation "(* x 'is' y 'by' z 'of' // /= //= *)" (at level 8).
Reserved Notation "(* 69 *)" (at level 69).

End SsrSyntax.

Export SsrSyntax.

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

(* Force boolean interpretation of simple if expressions.          *)

Delimit Scope boolean_if_scope with BOOL_IF.

Notation "'if' c 'return' t 'then' v1 'else' v2" :=
  (if c%bool is true in bool return t then v1 else v2) : boolean_if_scope.

Notation "'if' c 'then' v1 'else' v2" :=
  (if c%bool is true in bool return _ then v1 else v2) : boolean_if_scope.

Notation "'if' c 'as' x 'return' t 'then' v1 'else' v2" :=
  (if c%bool is true as x in bool return t then v1 else v2) : boolean_if_scope.

Open Scope boolean_if_scope.

(* Syntax for referring to canonical structures:                   *)
(*   [is carrier : carrier_type <: struct_type]                    *)
(* denotes carrier_struct when carrier_struct : struct_type is a   *)
(* Canonical Structure that projects to carrier via its coercion   *)
(* to carrier_type, i.e., such that                                *)
(*     carrier_struct : carrier_type = carrier.                    *)
(*  Although [is carrier : carrier_type <: struct_type] is         *)
(* convertible (and indeed simplifies) to carrier_struct, it does  *)
(* not actually denote carrier_struct, but a more complex term     *)
(* that is displayed as                                            *)
(*      (*is carrier*)carrier_struct                               *)
(* The ": carrier_type" is optional and defaults to ": Type" :     *)
(*      [is c <: sT] is equivalent to [c%type : Type <: sT]        *)
(* (The %type allows the casual use of notations like nat * nat.)  *)
(*   Alternatively, if "carrier_type" is left as "_" it will be    *)
(* inferred from c. However, this alternative should NOT be be     *)
(* when carrier_type is Type, because Coq infers that simple       *)
(* datatypes such as nat, nat * nat, or seq nat have the legacy    *)
(* type "Set" rather than "Type".                                  *)

Delimit Scope structure_scope with STRUCT.
Open Scope structure_scope.

Module AsCanonical.

CoInductive put cT sT (c1 c2 : cT) (s : sT) :  Type := Put.

Definition get cT sT c s (p : @put cT sT c c s) := let: Put := p in s.

End AsCanonical.

Import AsCanonical.

Notation "[ 'is' c : cT <: sT ]" := (get ((fun s : sT => Put (c : cT) s s) _))
  (at level 0, c, cT at level 99, only parsing) : structure_scope.

Notation "[ 'is' c <: sT ]" := [is c%type : Type <: sT]
  (at level 0, c at level 99, only parsing) : structure_scope.

Notation "[ 'i' 's' c : cT <: sT ]" := (@get cT sT c _ _)
  (at level 0, format "[ 'i' 's'  c  :  cT  <:  sT ]") : structure_scope.

Notation "[ 'i' 's' c <: sT ]" := (@get Type sT c _ _)
  (at level 0, format "[ 'i' 's'  c  <:  sT ]") : structure_scope.

(* Helper notation for canonical structure inheritance support.           *)
(* This is a workaround for the poor interaction between delta reduction  *)
(* and canonical projections in Coq's unification algorithm, by which     *)
(* transparent definitions hide canonical structures, i.e., in            *)
(*   Canonical Structure a_type_struct := @Struct a_type ...              *)
(*   Definition my_type := a_type.                                        *)
(* my_type doesn't effectively inherit the struct structure from a_type.  *)
(* Our solution is to redeclare the structure, as follows                 *)
(*   Canonical Structure my_type_struct :=                                *)
(*     Eval hnf in [struct of my_type].                                   *)
(* The special notation [str of _] must be defined for each Strucure      *)
(* "str" with constructor "Str", as follows                               *)
(*  Notation "[ 'str' 'of' t ]" :=                                        *)
(*    (StructureOf (@Str t)                                               *)
(*     match [is t <: str] as s                                           *)
(*       return {type of Str for s} -> str with                           *)
(*    | Str _ x y ... z => fun k => k _ x y ... z                         *)
(*    end) (at level 0, only parsing) : form_scope.                       *)
(*  Notation "[ 'str' 'o' 'f' t ]" := (StructureOf (@Str t) _)            *)
(*    (at level 0, format "[ 'str'  'o' 'f'  t ]") : form_scope.          *)
(* The notation for the match return predicate is defined below; note     *)
(* that the implementation of the [is t <: s] notation carefully avoids   *)
(* the delta reduction problem, crucially.                                *)
(* The StructureOf allows the second (unparsable) Notation to be used     *)
(* to display the result of the first; it can be omitted for structures   *)
(* like, e.g., eqType, that are only used statically.                     *)

Definition argumentType T P & forall x : T, P x := T.
Definition dependentReturnType T P & forall x : T, P x := P.
Definition returnType aT rT & aT -> rT := rT.
Definition StructureOf sT cT (construct : cT) K : sT := K construct. 

Notation "{ 'type' 'of' c 'for' s }" := (dependentReturnType c s)
  (at level 0, format "{ 'type'  'of'  c  'for'  s }") : type_scope.

Delimit Scope form_scope with FORM.
Open Scope form_scope.

(* A generic "phantom" type (actually, the unit type with a phantom      *)
(* parameter). This can be used for type definitions that require some   *)
(* Structure on one of their parameters, to allow Coq to infer said      *)
(* structure rather that having to supply it explicitly or to resort to  *)
(* the "[is _ <: _]" notation, which interacts poorly with Notation.     *)
(*   The definition of a (co)inductive type with a parameter p : p_type, *)
(* that uses the operations of a structure                               *)
(*  Structure p_str : Type := p_Str {                                    *)
(*    p_repr :> p_type; p_op : p_repr -> ...}                            *)
(* should be given as                                                    *)
(*  Inductive indt (p : p_str) : Type := Indt ... .                      *)
(*  Definition indt_for (p : p_str) & phantom p_type p := indt p.        *)
(*  Notation "{ 'indt' p }" := (indt_for (Phantom p)).                   *)
(*  Definition indt_of p x y ... z : {indt p} := @Indt p x y ... z.      *)
(*  Notation "[ 'indt' x y ... z ]" := (indt_of x y ... z).              *)
(* That is, the concrete type and its constructor should be shadowed by  *)
(* definitions that use a phantom argument to infer and display the true *)
(* value of p (in practice, the "indt_of" constructor often performs     *)
(* additional functions, like "locking" the representation (see below).  *)
(*   We also define a simpler version ("phant" / "Phant") for the common *)
(* case where p_type is Type.                                            *)

CoInductive phantom (T :  Type) (p : T) :  Type := Phantom.
Implicit Arguments phantom [].
CoInductive phant (p : Type) :  Type := Phant.

(* Internal tagging used by the implementation of the ssreflect elim. *)

Definition protect_term (A :  Type) (x : A) : A := x.

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
(*    CAVEAT: nosimpl should not be used inside a Section, because the end  *)
(*    of section "cooking" removes the iota redex.                          *)
(*  - (locked t) is provably equal to t, but is not convertible to t; it    *)
(*    provides support for abstract data types, and selective rewriting.    *)
(*    The equation t == (locked t) is provided as a lemma, but it should    *)
(*    only be used for selective rewriting (see below). For ADTs, the       *)
(*    unlock tactic should be used to remove locking.                       *)
(* locked is also used as a placeholder for the implementation of flexible  *)
(* matching.                                                                *)
(* Addendum: it appears that the use of a generic key confuses the term     *)
(* comparison heuristic of the Coq kernel, which thinks all locked terms    *)
(* have the same "head constant", and therefore immediately jumps to        *)
(* comparing their LAST argument. Furthermore, Coq still needs to delta     *)
(* expand a locked constant when comparing unequal terms, and, given the    *)
(* total absence of caching of comparisons, this causes an exponential      *)
(* blowup in comparisons that return false on terms that are built from     *)
(* many combinators, which is quite common in a modular development.        *)
(*   As a stopgap, we use the module system to create opaque constants      *)
(* with an expansion lemma; this is pretty clumsy because design of the     *)
(* module language does not support such small-scale usage very well. See   *)
(* the definiiton of card and subset in fintype.v for examples of this.     *)
(*   Of course the unlock tactic will not support the expansion of this new *)
(* kind of opaque constants; to compensate for that we use "unlockable"     *)
(* canonical structures to store the expansion lemmas, which can then be    *)
(* retrieved by a generic "unlock" rewrite rule. Note that because of a     *)
(* technical limitation of the implementation of canonical projection       *)
(* in ssreflect 1.1, unlock must weaken the intensional equality between    *)
(* the constant and its definition to an extensional one.                   *)

Notation "'nosimpl' t" := (let: tt := tt in t) (at level 10, t at level 8).

(* To unlock opaque constants. *)
Structure unlockable (T : Type) (v : T) : Type :=
  Unlockable {unlocked : T; _ : unlocked = v}.

Lemma unlock : forall aT rT (f : forall x : aT, rT x) (u : unlockable f) x,
  unlocked u x = f x.
Proof. move=> aT rT f [u /= ->]; split. Qed.

(*
Definition locked_with key A := let: tt := key in fun x : A => x.

Lemma unlock : forall key A, @locked_with key A = (fun x => x).
Proof. case; split. Qed.
*)

Lemma master_key : unit. Proof. exact tt. Qed.

(* This shoul be Definition locked := locked_with master_key, *)
(* but for compatibility with the ml4 code.                   *)
Definition locked A := let: tt := master_key in fun x : A => x.

Lemma lock : forall A x, x = locked x :> A.
Proof. rewrite /locked; case master_key; split. Qed.

(* Needed for locked predicates, in particular for eqType's. *)
Lemma not_locked_false_eq_true : locked false <> true.
Proof. rewrite -lock; discriminate. Qed.

(* The basic closing tactic "done".                                       *)
Ltac done :=
  trivial; hnf; intros; solve
   [ do ![solve [trivial | apply: sym_equal; trivial]
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

Section ApplyIff.

Variables P Q : Prop.
Hypothesis eqPQ : P <-> Q.

Lemma iffLR : P -> Q. Proof. by case eqPQ. Qed.
Lemma iffRL : Q -> P. Proof. by case eqPQ. Qed.

Lemma iffLRn : ~P -> ~Q. Proof. by move=> nP tQ; case: nP; case: eqPQ tQ. Qed.
Lemma iffRLn : ~Q -> ~P. Proof. by move=> nQ tP; case: nQ; case: eqPQ tP. Qed.

End ApplyIff.

Hint View for move/ iffLRn|2 iffRLn|2 iffLR|2 iffRL|2.
Hint View for apply/ iffRLn|2 iffLRn|2 iffRL|2 iffLR|2.

Unset Implicit Arguments.

