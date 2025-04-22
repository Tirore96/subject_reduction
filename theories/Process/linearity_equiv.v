From mathcomp Require Import all_ssreflect zify.
From Paco Require Import paco. 

Require Import MPSTSR.Projection.intermediateProj MPSTSR.Projection.projectDecide MPSTSR.Projection.indProj. 
Require Import MPSTSR.CoTypes.coLocal. 

Require Import MPSTSR.IndTypes.elimination.
Require Import MPSTSR.linearity.
Require Import MPSTSR.linearityDecide.
Require Import MPSTSR.harmony. 
Require Import MPSTSR.Process.processSyntax.
Require Import MPSTSR.Process.env. 
Require Import MPSTSR.Process.preds.
Require Import MPSTSR.Process.Congruence.
Require Import MPSTSR.Process.SubjectRed.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Definition Linear_aux2 (sg : gType) := 
forall a0 aa a1, 
Tr (a0::(aa++(cons a1 nil))) sg -> 
same_ch a0 a1 -> InDep2 a0 aa a1 /\ OutDep2 a0 aa a1.


Variant LinearF2  (R : gType -> Prop) : gType -> Prop :=
 | LF0 g : (forall g', g' \in nextg (full_unf g) -> R g') -> Linear_aux2 g -> LinearF2 R g.


Definition Linear2 := paco1 LinearF2 bot1. 

Lemma LinearF2_mon : monotone1 LinearF2.
Proof. 
intro. intros. inv IN;try con. auto. done.
Qed. 
Hint Resolve LinearF2_mon : paco.


Lemma Linear12 : forall g, Linear g -> Linear2 g.
Proof. 
intros. 
apply Linear_12 in H.
move : g H. pcofix CIH.
intros. punfold H0. inv H0.
pfold. con. intros. apply H in H2. inv H2. 
apply CIH in H3. right. done.
move : H1.
rewrite /Linear_aux /Linear_aux2.
intros. con.
apply H1 in H2. ssa. apply to_InDep2. done. done.
apply/to_OutDep2. apply H1 in H2. ssa. done.
Qed.

Lemma Linear21 : forall g, gclosed g -> gcontractive g -> Linear2 g -> Linear g.
Proof. 
intros. apply/Linear_decidable;ssa.
apply/sat1_complete_aux.
clear H H0.
move : g H1. pcofix CIH. intros. punfold H1. pfold.
inv H1. con. intros. apply H in H2. inv H2. apply CIH in H3. right. done.
clear  CIH H H1.
move : H0. rewrite /Linear_aux2 /Linear_aux.
ssa.
apply H0 in H;ssa.
clear H0 H2 H1.
move : H. clear.
rewrite /exists_dep.
elim. ssa.  exists nil. ssa.
ssa. exists (false::x). ssa.
ssa. exists (true::x). ssa.
apply H0 in H;ssa. 
move: H2. clear.
rewrite /exists_dep.
elim. ssa.  exists nil. ssa.
ssa. exists (false::x). ssa.
ssa. exists (true::x). ssa.
Qed.


Lemma Linear_equiv : forall g, gclosed g -> gcontractive g -> Linear g <-> Linear2 g.
Proof.
intros. split. apply Linear12. apply Linear21. done. done.
Qed. 


