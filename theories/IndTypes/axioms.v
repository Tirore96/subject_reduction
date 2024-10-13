(** * General Header Autosubst - Assumptions and Definitions *)

(** ** Axiomatic Assumptions
    For our development, during rewriting of the reduction rules,  we have to extend Coq with two well known axiomatic assumptions, namely _functional extensionality_ and _propositional extensionality_. The latter entails _proof irrelevance_.
*)

(** *** Functional Extensionality
    We import the axiom from the Coq Standard Library and derive a utility tactic to make the assumption practically usable.
*)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Program.Tactics.
From mathcomp Require Import all_ssreflect.
Tactic Notation "nointr" tactic(t) :=
  let m := fresh "marker" in
  pose (m := tt);
  t; revert_until m; clear m.

Ltac fext := nointr repeat (
  match goal with
    [ |- ?x = ?y ] =>
    (refine (@functional_extensionality_dep _ _ _ _ _) ||
     refine (@forall_extensionality _ _ _ _) ||
     refine (@forall_extensionalityP _ _ _ _) ||
     refine (@forall_extensionalityS _ _ _ _)); intro
  end).


(** ** Functor Instances

Exemplary functor instances needed to make Autosubst's generation possible for functors.
Two things are important:
1. The names are fixed.
2. For Coq to check termination, also the proofs have to be closed with Defined.
 *)

(** *** List Instance *)
(*Require Import List.*)
From mathcomp Require Import seq.

Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y)  :=
  fun x => g (f x).

Definition seq_ext {A B} {f g : A -> B} :
  (forall x, f x = g x) -> forall xs,  map f xs = map g xs.
  intros H. induction xs. reflexivity.
  cbn. f_equal. apply H. apply IHxs.
Defined.

Definition seq_id {A}  { f : A -> A} :
  (forall x, f x = x) -> forall xs, map f xs = xs.
Proof.
  intros H. induction xs. reflexivity.
  cbn. rewrite H. rewrite IHxs; eauto.
Defined.

Definition seq_comp {A B C} {f: A -> B} {g: B -> C} {h} :
  (forall x, (funcomp  g f) x = h x) -> forall xs, map g (map f xs) = map h xs.
Proof.
  induction xs. reflexivity.
  cbn. rewrite <- H. f_equal. apply IHxs.
Defined.

(** *** Prod Instance *)

Definition prod_map {A B C D} (f : A -> C) (g : B -> D) (p : A * B) :
  C * D.
Proof.
  destruct p. split. auto. auto.
Defined.

Definition prod_id {A B} {f : A -> A} {g : B -> B} :
  (forall x, f x = x) -> (forall x, g x = x) -> forall p, prod_map f g p = p.
Proof.
  intros. destruct p. cbn. f_equal; auto.
Defined.

Definition prod_ext {A B C D} {f f' : A -> C} {g g': B -> D} :
  (forall x, f x = f' x) -> (forall x, g x = g' x) -> forall p, prod_map f g p = prod_map f' g' p.
Proof.
  intros. destruct p. cbn. f_equal; auto.
Defined.

Definition prod_comp {A B C D E F} {f1 : A -> C} {g1 : C -> E} { h1} {f2: B -> D} {g2: D -> F} {h2}:
  (forall x, (funcomp  g1 f1) x = h1 x) -> (forall x, (funcomp g2 f2) x = h2 x) -> forall p, prod_map g1 g2 (prod_map f1 f2 p) = prod_map h1 h2 p.
Proof.
  intros. destruct p. cbn. f_equal; auto.
  now rewrite <- H. now rewrite <- H0.
Defined.


(** *** Function Instance *)

Definition cod X A:  Type :=  X -> A.

Definition cod_map {X} {A B} (f : A -> B) (p : X -> A) :
  X -> B.
Proof. eauto. Defined.

(** Note that this requires functional extensionality. *)
Definition cod_id {X} {A} {f : A -> A} :
  (forall x, f x = x) -> forall (p: X -> A), cod_map f p = p.
Proof. intros H p. unfold cod_map. fext. congruence. Defined.

Definition cod_ext {X} {A B} {f f' : A -> B} :
  (forall x, f x = f' x) -> forall (p: X -> A), cod_map f p = cod_map f' p.
Proof. intros H p. unfold cod_map. fext. congruence. Defined.

Definition cod_comp {X} {A B C} {f : A -> B} {g : B -> C} {h} :
  (forall x, (funcomp g f) x =  h x) -> forall (p: X -> _), cod_map g (cod_map f p) = cod_map h p.
Proof. intros H p. unfold cod_map. fext. intros x. now rewrite <- H. Defined.

(*Hint Rewrite in_map_iff : FunctorInstances.*)

Definition sum_map {A B C D} (f0 : A -> B) (f1 : C -> D) (p : A + C) : B + D := 
match p with 
| inl a => inl (f0 a)
| inr c => inr (f1 c) 
end. 

Definition sum_ext {A B C D} {f0 f'0 : A -> B} {f1 f'1 : C -> D}  :
  (forall x, f0 x = f'0 x) -> (forall x, f1 x = f'1 x) ->  forall xs,  sum_map f0 f1 xs = sum_map f'0 f'1 xs.
Proof.
  intros. f_equal. fext. auto. fext. auto. 
Defined.

Definition sum_id {A B}  { f : A -> A} {f' : B -> B} :
  (forall x, f x = x) -> (forall x, f' x = x) -> forall x, sum_map f f' x = x.
Proof. intros. destruct x; simpl. rewrite H.  done. rewrite H0. done. 
Defined.

Definition sum_comp {A B C D E F} {f0: A -> B} {f1: B -> C} {f2} {g0 : D -> E} {g1 : E -> F} {g2} :
  (forall x, (funcomp f1 f0) x = f2 x) ->  (forall x, (funcomp g1 g0) x = g2 x) -> forall x, sum_map f1 g1 (sum_map f0 g0 x) = sum_map f2 g2 x.
Proof. intros. destruct x; simpl. rewrite -H. done. rewrite -H0. done. 
Defined.
