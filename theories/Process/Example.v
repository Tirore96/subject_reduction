
From mathcomp Require Import all_ssreflect zify.
Require Import MPSTSR.Projection.intermediateProj MPSTSR.Projection.projectDecide MPSTSR.Projection.indProj. 
Require Import MPSTSR.CoTypes.coLocal. 

From Paco Require Import paco.
Require Import MPSTSR.IndTypes.elimination.
Require Import MPSTSR.harmony. 

Require Import MPSTSR.Process.processSyntax.
Require Import MPSTSR.Process.env. 
Require Import MPSTSR.Process.preds.
Require Import MPSTSR.linearity.
Require Import MPSTSR.linearityDecide.
Require Export MPSTSR.Process.SubjectRed4.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TypingDeclaration.

Check OFT.
Print s_env. Print value. Check EMsg.
Definition Ms := [::(((var_valBool 0)),SBool)].
Definition T :=  ERec (EMsg Sd (Ch 0) (VSort SBool) (EVar 0)).
Definition Ds := [::(SBool,[:: fe T])].

Definition P := ValSend (var_sch 0) 0 (valE ((var_valBool 0))) (PCall 0 (valE ((var_valBool 0))) [::(var_sch 0)]).
Definition L := [::(var_sch 0, fe T)].

Lemma typing : DOFT Ms Ds [::P] P L nil nil.
Proof.
con. rewrite /DefTyping. ssa.
ssa. rewrite inE in H. norm_eqs. 
rewrite /P. ssa.
ssa.
rewrite inE in H. norm_eqs.
rewrite /P in H0. ssa.
rewrite inE in H0. de (orP H0). norm_eqs. done.
rewrite inE in H. norm_eqs. done.

ssa. rewrite inE in H. norm_eqs. inv H.

rewrite /P. econ. done.
econ. econ. 
rewrite /insertS0 /insert_shift /=.
rewrite lookup_cons_eq. ssa. done.
simpl. rewrite lookup_cons_eq. simpl. rewrite /T /full_eunf.  simpl. eauto.
done.
econ. done. 7: { 
simpl. rewrite /partition. econ. } 
ssa. done.
econ. econ. rewrite lookup_cons_eq. eauto. done.
ssa. done.
intro. ssa.
ssa. rewrite inE in H0. norm_eqs. inv H0.
rewrite lookup_cons_eq in H1. inv H1. ssa.
apply/EQ2_refl.
apply:to_lInvPred. intro. ssa. ssa.
ssa.

econ.
done.
econ. econ. rewrite lookup_cons_eq. done. done. 
simpl. 
rewrite lookup_cons_eq. simpl.
rewrite /T. rewrite /full_eunf. simpl. eauto. done.
econ. done.

7: econ. ssa. done. econ. con. rewrite lookup_cons_eq. eauto. done.
ssa. done. intro. ssa.
ssa. 

rewrite lookup_cons_eq in H0. inv H0. ssa.
rewrite inE in H. norm_eqs. inv H.
apply/EQ2_refl.
apply:to_lInvPred. intro. ssa. ssa.
ssa.
rewrite inE in H. norm_eqs. inv H.
Qed.
