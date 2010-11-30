Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype bigop.
Require Import finfun tuple ssralg matrix zmodp vector.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Open Local Scope ring_scope.

Import GRing.Theory.

Section RingLmodule.

Variable (R : ringType).
Local Notation Regular  := (GRing.Lmodule.Regular R).

Definition r2rv (x:Regular): 'rV[R]_1 := \row_(i < 1) x .

Lemma r2rv_morph_p : linear r2rv.
Proof. by move=> k x y; apply/matrixP=> [] [[|i] Hi] j;rewrite !mxE. Qed.

Canonical Structure r2rv_morph := GRing.LinearFun r2rv_morph_p.

Definition rv2r (A: 'rV[R]_1): Regular := A 0 0.

Lemma r2rv_bij : bijective r2rv.
Proof.
exists rv2r; first by move => x; rewrite /r2rv /rv2r /= mxE.
by move => x; apply/matrixP=> i j; rewrite [i]ord1 [j]ord1 /r2rv /rv2r !mxE /=.
Qed.

Canonical Structure  RVMixin := Eval hnf in VectMixin r2rv_morph_p r2rv_bij.
Canonical Structure RVVectType := (@VectorType.pack R (Phant R) R   
                        (GRing.Lmodule.Class (GRing.Lmodule.RegularMixin R))
                         RVMixin Regular _ id _ id).

Lemma dimR : vdim RVVectType = 1%nat.
Proof. by rewrite /vdim /=. Qed.

End RingLmodule.

(* BiLinear & Sesquilinear & Quadratic Forms over a vectType *)
Section LinearForm.

Variable (F : fieldType) (V : vectType  F).

Section SesquiLinearFormDef.

Structure fautomorphism:= FautoMorph { fval :> (F -> F); 
                                      _ :GRing.morphism fval; 
                                      _ :  bijective fval}.

Local Notation vvf:= (V -> V -> F).


Structure sesquilinear_form  := 
              SesqlinearForm {formv :> vvf;
               teta: fautomorphism;
 	         _ : forall x, {morph formv x : y z / y + z};
 	         _ : forall x, {morph formv ^~  x : y z / y + z};
 	         _ : forall a x y,  formv  (a *: x) y = a * formv x y;
 		 _ : forall a x y , formv x (a *: y) = (teta a) * (formv x y)}.

Variable f : sesquilinear_form.

Lemma bilin1 :  forall x, {morph f x : y z / y + z}. Proof. by case f. Qed.
Lemma bilin2 :  forall x, {morph f ^~  x : y z / y + z}. Proof. by case f. Qed.
Lemma bilina1 :  forall a x y, f (a *: x) y = a * f x y. Proof. by case f. Qed.
Lemma bilina2 : forall a x y, f x (a *: y) = (teta f a) * (f x y). 
Proof. by case f. Qed.

End SesquiLinearFormDef.

Section SesquiLinearFormTheory.

Local Notation sqlf := sesquilinear_form.

Definition symmetric (f: sqlf):= (forall a, ( teta f a = a)) /\  
                                  forall x y, (f x y = f y x).
Definition skewsymmetric (f: sqlf):= (forall a , ( teta f a = a)) /\ 
                                      forall x y, f x y = -(f y x).

Definition hermitian_sym  (f: sqlf) := (forall x y, f x y = teta f (f y x)).

Lemma sym_form0: forall  (f: sqlf) x y, (symmetric f) ->  
                                        (f x y = 0  <-> f y x = 0).
Proof. by move => f x y [Hteta Hsym]; split => Hf; rewrite Hsym. Qed.

Lemma antisym_form0: forall  (f: sqlf) x y, (skewsymmetric f) ->  
                                            (f x y = 0  <-> f y x = 0).
Proof. by move => f x y [Hteta Hsym]; split => Hf; rewrite Hsym Hf oppr0. Qed.

(* Do not need the involutive hypothesis *)
Lemma hermit_form0: forall   (f: sqlf) x y, ( hermitian_sym f) ->  
                                            (f x y = 0  <-> f y x = 0).
Proof.
move => f x y  Hfxy; split.
  by rewrite (Hfxy y x); move->; case: (teta f) => f0 m b;rewrite /= ringM_0.
by rewrite (Hfxy x y);move ->; case: (teta f) => f0 m b;rewrite /= ringM_0.
Qed.

Definition symmetricf f:=  
                  (symmetric f) \/ (skewsymmetric f) \/ (hermitian_sym  f).

Lemma fsym_f0: forall f  , symmetricf f ->
                    forall x y , (f x y = 0  <-> f y x = 0).
Proof.
by move => f[Hf|[Hf|Hf]] x y;
   [apply:sym_form0|apply:antisym_form0|apply:hermit_form0].
Qed.

End SesquiLinearFormTheory.

Variable f: sesquilinear_form .
Hypothesis fsym: symmetricf f.

Section orthogonal.

Definition orthogonal x y := f x y = 0.

Lemma ortho_sym: forall x y, orthogonal x y <-> orthogonal y x.
Proof. by move=> x y; apply:fsym_f0. Qed.

Theorem Pythagore: forall u v, orthogonal u v -> f (u+v) (u+v)  = f u u  + f v v.
Proof.
move => u v Huv; elim:(ortho_sym  u v ) => Hvu _.
by rewrite !bilin1 !bilin2 Huv (Hvu Huv) add0r addr0.
Qed.

Lemma orthoD : forall u v w , orthogonal u v -> orthogonal u w -> orthogonal u (v + w).
Proof.
by move => u v w Huv Huw; rewrite  /orthogonal bilin1 Huv Huw add0r.
Qed.

Lemma orthoZ: forall u v a, orthogonal u v ->  orthogonal (a *: u) v.
Proof. by move => u v a Huv; rewrite  /orthogonal bilina1 Huv mulr0. Qed.

Variable x:V.

Definition alpha : V-> (RVVectType F) := fun y => f y x.

Definition alpha_lapp := (lapp_of_fun alpha).

Definition  xbar := lker alpha_lapp .

Lemma alpha_lin: linear alpha.
Proof. by move => a b c; rewrite /alpha bilin2 bilina1. Qed.



Lemma xbarP:  forall e1, reflect (orthogonal e1 x ) (e1 \in xbar).
move=> e1; rewrite memv_ker  lapp_of_funK //=.
  by apply: (iffP eqP).
by apply alpha_lin.
Qed.


Lemma dim_xbar :forall vs,(\dim vs ) -  1 <= \dim (vs :&: xbar).
Proof. 
move=> vs; rewrite -(addKn 1 (\dim (vs :&: xbar))) addnC leq_sub2r //.
have H :\dim  (alpha_lapp @v: vs )<= 1 by rewrite -(dimR F) -dimvf dimvS // subsetvf.
by rewrite -(limg_ker_dim alpha_lapp vs)(leq_add (leqnn (\dim(vs :&: xbar)))). 
Qed.

(* to be improved*)
Lemma xbar_eqvs: forall vs,  (forall v , v \in vs -> orthogonal v x )-> \dim (vs :&: xbar)= (\dim vs ).
move=> vs  Hvs.
rewrite -(limg_ker_dim alpha_lapp vs).
suff-> : \dim (alpha_lapp @v: vs) = 0%nat by rewrite addn0.
apply/eqP; rewrite dimv_eq0; apply /vspaceP => w.
rewrite memv0;apply/memv_imgP.
case e: (w==0).
  exists 0; split ;first by rewrite mem0v.
  apply sym_eq; rewrite (eqP e).
  rewrite (lapp_of_funK alpha_lin 0).
  rewrite /alpha_lapp /alpha /=.
  by move:(bilina1 f 0 x x); rewrite scale0r mul0r.
move/eqP:e =>H2;case=> x0 [Hx0 Hw].
apply H2;rewrite Hw;move: (Hvs x0 Hx0).
rewrite /orthogonal.
by rewrite (lapp_of_funK alpha_lin x0).
Qed.


End orthogonal.

Definition quadraticf (Q: V -> F) := 
     (forall x a, Q (a *: x) = a ^+ 2 * (Q x))%R *
     (forall x y, Q (x + y) = Q x + Q y + f x y)%R : Prop.
Variable Q : V -> F.
Hypothesis quadQ :  quadraticf Q.
Import GRing.Theory.

(* improved by Georges *)
Lemma f2Q:  forall x, Q x + Q x = f x x.
Proof.
move=> x; apply:(@addrI _ (Q x + Q x)).
rewrite !addrA  -quadQ -[x + x](scaler_nat 2) quadQ.
by rewrite  -mulrA !mulr_natl -addrA.
Qed.

End LinearForm.
