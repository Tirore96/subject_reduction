From mathcomp Require Import all_ssreflect zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section predDefs.
Implicit Type T : Type. 
Definition pred0 {T}  : T -> bool  := xpred0.
Definition predT {T} : T -> bool := xpredT. 
Definition predI {T} (p1 p2 : pred T) := (xpredI p1 p2).
Definition predU {T} (p1 p2 : pred T) :=  (xpredU p1 p2).
Definition predC {T} (p : pred T) := (xpredC p).

Lemma pred0_eq  T : @pred0 T = fun _ => false. 
Proof. done. Qed. 
Lemma predT_eq  T : @predT T = fun _ => true. 
Proof. done. Qed. 

Lemma predU_eq : forall T (p1 p2 : pred T), predU p1 p2 =  fun x => (p1 x) || (p2 x).  
Proof. done. Qed. 
Lemma predI_eq : forall T  (p1 p2 : pred T), predI p1 p2 = fun x => (p1 x) && (p2 x).   
Proof. done. Qed. 
Lemma predC_eq : forall T (p1 : pred T), predC p1 =  (fun x => ~~ p1 x).  
Proof.  done. Qed. 
End predDefs. 

Let peqs := (pred0_eq,predT_eq,predU_eq,predI_eq,predC_eq).


Section hrelDefs. 
Implicit Types A B : Type. 

Definition hrel A B := A -> pred B.
Identity Coercion fun_of_hrel : hrel >-> Funclass.

(*Definition simpl_hrel (A B : Type) := A -> simpl_pred B.

Coercion hrel_of_simpl (A B : Type) (sr : simpl_hrel A B) : hrel A B := fun a b => sr a b.
Arguments hrel_of_simpl {A B} sr a b /.*)

(*We don't use simplifying relations as the coercions hrel_of_simpl on the top-level formula prevents rewrites *)
(*Definition SimplHRel {A B : Type} (r : hrel A B) : simpl_hrel A B := fun x => SimplPred (r x).*)
(*Definition HRel {A B : Type} (r : hrel A B) : simpl_hrel A B := fun x => SimplHRel (r x).*)

Definition hrel0 A B := fun (_ : A) (_ : B) => false. 
Definition hrelT A B := fun (_ : A) (_ : B) => true. 
Definition hrelI A B (r1 r2 : hrel A B) := fun x y => (r1 x y) && (r2 x y).  
Definition hrelU A B (r1 r2 : hrel A B) := fun x y => (r1 x y) || (r2 x y).   
Definition hrelC A B (r1 : hrel A B) := (fun x y => ~~ r1 x y). 

Lemma hrel0_eq : forall A B (r : hrel A B), @hrel0 A B =  fun (_ : A) (_ : B) => false. 
Proof. done. Qed. 
Lemma hrelT_eq : forall A B (r : hrel A B), @hrelT A B =  fun (_ : A) (_ : B) => true. 
Proof. done. Qed. 
Lemma hrelU_eq : forall A B  (r1 r2 : hrel A B), hrelU r1 r2 =  fun x y => (r1 x y) || (r2 x y).  
Proof. done. Qed. 
Lemma hrelI_eq : forall  A B  (r1 r2 : hrel A B), hrelI r1 r2 = fun x y => (r1 x y) && (r2 x y).   
Proof. done. Qed. 
Lemma hrelC_eq : forall A B (r1 : hrel A B), hrelC r1 =  (fun x y => ~~ r1 x y).  
Proof.  done. Qed. 

End hrelDefs. 


Let heqs := (hrel0_eq,hrelT_eq,hrelU_eq,hrelI_eq,hrelC_eq).

Let pheqs := (peqs,heqs).

Ltac solve_ph := rewrite ?pheqs;lia. 
