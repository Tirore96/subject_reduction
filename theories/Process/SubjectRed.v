From mathcomp Require Import all_ssreflect zify.
Require Import MPSTSR.Projection.intermediateProj MPSTSR.Projection.projectDecide MPSTSR.Projection.indProj. 
Require Import MPSTSR.CoTypes.coLocal. 

Require Import MPSTSR.IndTypes.elimination.
Require Import MPSTSR.harmony. 
Require Import MPSTSR.Process.processSyntax.
Require Import MPSTSR.Process.env. 
Require Import MPSTSR.Process.preds.
Require Export MPSTSR.Process.Congruence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint par_seq (Ps : seq process) := 
match Ps with 
| nil => Inact 
| P::Ps' => Par P (par_seq Ps')
end. 

Inductive EvalE : exp -> valBool -> Prop := 
 | E1 v : EvalE (valE  v) v
 | E2 e0 e1 b b' b''  : EvalE e0 (boolB b) -> 
                        EvalE e1 (boolB b') ->  
                        b'' = b && b' ->  
                        EvalE (andE e0 e1) (boolB b'').

Definition defs := seq process.

Definition my_subst_schl (s : schl) (p : ptcp) (P: process) := subst_process ids ids ids (((schlT s p)).:ids) P.
Definition my_subst_valBool (vb : valBool) (P: process) := subst_process ids ((vb).:ids) ids ids P.  

(*CanLink shared-name, #ptcps in the sesson, number of queues, next ptcp expected, linkable process*)
Fixpoint get_high_p (P : process) := 
match P with 
| Par P0 P1 => get_high_p P1
| SessAcc _ p _ => Some p 
| _ => None
end. 

Definition get_name_p  (P : process) := if P is Par _ (SessAcc (valB v) p _) then Some (v,p) else None.

Definition make_queues (cs : seq schli) := par_seq (map (fun c => MsgQ c nil) cs). 

Definition all_left : ptcp -> lpath := fun _ => nil. 


Lemma can_split_all_left : forall E, can_split E all_left.
Proof. intros. 
rewrite /can_split. ssa. 
Qed. 
Lemma makeLs_all_left : forall E, makeLs E all_left = map (fun x => (x.1, full_eunf x.2)) E. 
Proof. elim;ssa. 
Qed. 
Lemma makeQs_all_left : forall E, makeQs E all_left = map (fun p => (p,nil)) (dom E). 
Proof. elim;ssa. destruct a. f_equal. done. 
Qed. 
Hint Resolve can_split_all_left makeLs_all_left makeQs_all_left.

Implicit Types A B : eqType.

Lemma lookup_uniq : forall A B (E : seq (A * B)) lk v v', lookup E lk = Some v -> lookup E lk = Some v' -> v = v'.
Proof.
move => A B.  elim;ssa.
apply lookup_or in H0,H1.  de H0. subst. 
de H1. rewrite eqxx in H0. done. 
de H1.  subst.  rewrite eqxx in H0. done.
eauto. 
Qed. 

Lemma proj_trans : forall g p T, proj g p = Some T -> T = trans p g. 
Proof. 
intros. rewrite /proj in H. move : H. rifliad. case. done. 
Qed. 

Definition env_not_rec (E : l_env) := all (snd >> fun l => ~~ is_erec l) E.

(*Follow revisited paper, assuming polarities present to allow reduction*)
(*Check the location of msg entries is correct, distinct from receiver ptcp*)
Definition get_ch  (P : process) := if P is MsgQ (schliT _ c) _ then Some c else None.  

Fixpoint make_cs (n : nat) := 
if n is n'.+1 then (schliT (var_schl 0) n')::(make_cs n') else nil. 

Inductive Accepts : nat -> val -> process -> Prop := 
| A1 v P : Accepts 0 v (SessAcc (valB v) (Ptcp 0) P)
| A2 n v P P' : Accepts n v P -> Accepts n.+1 v (Par (SessAcc (valB v) (Ptcp n.+1) P') P).

Fixpoint reduce_link (P : process) := 
match P with 
| Par P0 P1 => Par (reduce_link P0) (reduce_link P1)
| SessReq _ n _ P => subst_process ids ids (succn >> ids) (((schlT (var_schl 0) (Ptcp n))).:ids) P
| SessAcc _ p P => subst_process ids ids (succn >> ids) (((schlT (var_schl 0) p)).:ids) P
| _ => P
end. 


Inductive CanLink : nat -> process -> Prop := 
| CanLink1 n v q P R : 0 < n -> 0 < q ->  Accepts n.-1 v R -> CanLink q (Par (SessReq (valB v) n q P) R).


Inductive Sem : defs -> process -> process -> Prop :=
 | SLink D q P : CanLink q P -> Sem D P (ResCh (Par (reduce_link P) (make_queues (make_cs q.+1)))) (*CanLink n P, more general than link, n is a number for how many roles are missing from the session, to make it compositional*) (*q.+1 because make_ch 0 = nil*)
 | SSend D e v s i p P msgs: EvalE e v -> Sem D (Par (ValSend ((schlT s p)) i e P) (MsgQ (schliT s i) msgs))
                                             (Par P (MsgQ (schliT s i) (msgs ++ [::(msgT (valM v) p)])))
 | SDel D s s' i p p' P msgs: Sem D (Par (SessDel ( (schlT s p)) i (schlT s' p') P) (MsgQ (schliT s i) msgs))
                               (Par P (MsgQ (schliT s i) (msgs++[::msgT (schM (schlT s' p')) p]))) (*var_schP cannot happen in msg queue*)
 | SLabel D s l i p P msgs: Sem D (Par (LabelSel (( (schlT s p))) i l P) (MsgQ (schliT s i) msgs))
                                (Par P (MsgQ (schliT s i) (msgs++[::msgT (labelM l) p])))

 | SRec D v s i p p' P msgs: Sem D (Par (ValRec ( (schlT s p)) i P) 
                                     (MsgQ (schliT s i) ((msgT (valM v) p')::msgs)))
                              (Par (my_subst_valBool v P) 
                                   (MsgQ (schliT s i) (msgs)))

 | SSessRec D s s' i p p' p'' P msgs: Sem D (Par (SessRec ( (schlT s p)) i P) (MsgQ (schliT s i) ((msgT (schM (schlT s' p')) p'')::msgs)))
                                   (Par (my_subst_schl s' p' P) (MsgQ (schliT s i) (msgs)))
 | SBranch D s l i p p' P Ps msgs: lookup Ps l = Some P ->
                                          Sem D (Par (LabelBr ( (schlT s p)) i Ps) (MsgQ (schliT s i) ((msgT (labelM l) p')::msgs)))
                                                (Par P (MsgQ (schliT s i) (msgs)))
 | STrue D e P0 P1 : EvalE e (boolB true) -> Sem D (If e P0 P1) P0
 | SFalse D e P0 P1 : EvalE e (boolB false) -> Sem D (If e P0 P1) P1
 | SCall D defi e v ss : EvalE e v -> defi < size D -> Sem D (PCall defi e ss) 
                                           (subst_process ids (v .: ids) ids (fun n => nth ( (schlT (var_schl 0) (Ptcp 0))) ss n) (nth Inact D defi))
 | SScopCh D P P' : Sem D P P' -> Sem D (ResCh P) (ResCh P')
 | SScopName D P P' : Sem D P P' -> Sem D (ResVal P) (ResVal P')
 | SPar D P Q P' : Sem D P P' -> Sem D (Par P Q) (Par P' Q)
 | SStr D P P' Q' Q : Cong P P' -> Sem D P' Q' -> Cong Q' Q -> Sem D P Q.


Lemma make_queues_cons : forall a l, make_queues (a :: l) = Par (MsgQ a nil) (make_queues l).
Proof. 
intros. rewrite /make_queues. ssa. 
Qed. 

Lemma make_queues_typing : forall cs Ms Ds, uniq cs ->  OFT Ms Ds (make_queues cs) nil nil (map (fun x => (x,tt)) cs).
Proof.
elim;ssa. con. done. done.
rewrite make_queues_cons. econ. 
econ. econ. instantiate (3:= (fun k => k == a)). ssa. 
ssa. rewrite eqxx //=. erewrite filter_keys_eq. erewrite filter_keys_pred0. con. done. done. 
ssa. rewrite /dom -map_comp in H0. destruct (mapP H0). subst. ssa.
apply/negP. intro. norm_eqs.  rewrite H3 in H1.  done. 
ssa. rewrite eqxx //=. erewrite filter_keys_eq.  erewrite filter_keys_predT. eauto.
ssa. rewrite /dom -map_comp in H0. de (mapP H0). subst.  apply/eqP. intro. 
subst. rewrite H3 in H1. 
done. 
Unshelve. econ. econ.
Qed. 

Lemma make_queues_typing2 : forall cs Ms Ds E Q, uniq cs -> lType_done E -> qType_done Q ->  OFT Ms Ds (make_queues cs) E Q (map (fun x => (x,tt)) cs).
Proof.
elim;ssa. con. done. done.
rewrite make_queues_cons. econ. 
econ. econ. instantiate (3:= (fun k => k == a)). ssa. 
ssa. rewrite eqxx //=. erewrite filter_keys_eq. erewrite filter_keys_pred0. 
erewrite filter_keys_eq. erewrite filter_keys_pred0. 
econ. done. apply qType_done_filter_q. done.
ssa. rewrite /dom -map_comp in H0. de (mapP H0). subst.
apply/eqP.  intro. subst.  rewrite H5 in H3. done.
2 : {  simpl. have : predC (eq_op^~ a) a = false. tunf. rewrite eqxx //=. 
move => ->. 
erewrite (@filter_keys_eq _ _ (map _ _)). 
erewrite filter_keys_predT. 
apply/H. done.  apply/lType_done_filter_keys. done. apply/qType_done_filter_q.  done.
ssa. rewrite /dom -map_comp in H0.  de (mapP H0). subst. 
apply/eqP. intro. subst.  rewrite H5 in H3. done. }
ssa. 
Unshelve.
econ. 
Qed. 



Definition sch_fv (c : sch) :=
match c with 
| schlT _ _ => nil
| var_sch n => n::nil
end. 

Definition msgp_sch_fv (m : msgp) := 
match m with 
| msgT (schM c) _ => sch_fv c
| _ => nil 
end.


Fixpoint proc_sch_fv (P : process) := 
match P with 
| SessReq a b q P0 =>  map predn (filter (fun n => n != 0) (proc_sch_fv P0))
| SessAcc a b P0=>  map predn (filter (fun n => n != 0) (proc_sch_fv P0))
| ValSend a b c P0=> (sch_fv a)++ proc_sch_fv P0
| ValRec a b P0=> (sch_fv a)++( proc_sch_fv P0)
| SessDel a b c P0=>  (sch_fv a)++(sch_fv c)++(proc_sch_fv P0)
| SessRec a b P0 => (sch_fv a)++(map predn (filter (fun n => n != 0) (proc_sch_fv P0)))
| LabelSel a b c P0=>  (sch_fv a)++(proc_sch_fv P0)
| LabelBr a b Ps => (sch_fv a)++(flatten (map (snd>>proc_sch_fv) Ps))
| If a P0 P1=>  (proc_sch_fv P0) ++  (proc_sch_fv P1)
| Par P0 P1 => (proc_sch_fv P0) ++  (proc_sch_fv P1)
| Inact => nil
| ResCh P0 => proc_sch_fv P0
| ResVal P0 =>  proc_sch_fv P0 
| PCall a b c=> flatten (map sch_fv c)
| MsgQ a b => flatten (map msgp_sch_fv b)
end. 



Lemma make_queues_no_sch_var : forall c n, n \notin proc_sch_fv (make_queues c). 
Proof. 
elim;ssa.  
Qed. 


Lemma subst_sch_sch_fv : forall c n sig0 sig1, n \in sch_fv (subst_sch sig0 sig1 c) -> exists n', n' \in sch_fv c /\ sig1 n' = var_sch n. 
Proof. 
case;ssa. destruct (sig1 n) eqn:Heqn;ssa.
rewrite inE in H. norm_eqs. exists n. ssa.
Qed. 

Lemma subst_msgp_fv : forall c n sig0 sig1 sig2 sig3, n \in msgp_sch_fv (subst_msgp sig0 sig1 sig2 sig3 c) -> exists n', n' \in msgp_sch_fv c /\ sig3 n' = var_sch n. 
Proof. 
case;ssa. destruct m;ssa. apply subst_sch_sch_fv in H. done. 
Qed. 






Lemma subst_proc_sch_fv : forall P n sig0 sig1 sig2 sig3, n \in proc_sch_fv (subst_process sig0 sig1 sig2 sig3 P) -> exists n', n' \in proc_sch_fv P /\ sig3 n' = var_sch n. 
Proof.
 elim/process_ind;ssa.
- ptac. ptac. apply H in H1. ssa. asimpl in H2. de x0. inv H2. asimpl in H2. 
  exists x0.+1.-1. con. apply/map_f. rewrite mem_filter. ssa. ssa. de (sig3 x0). inv H2.

- ptac. ptac. apply H in H1. ssa. de x0. inv H2. asimpl in H2. 
  exists x0.+1.-1. con. apply/map_f. rewrite mem_filter. ssa. ssa. de (sig3 x0). inv H2.

- ctac. apply subst_sch_sch_fv in a. ssa. exists x. ssa. ctac. 

- apply H in b. ssa. exists x. ssa. ctac. 

- ctac. apply subst_sch_sch_fv in a. ssa. exists x. ssa. ctac. 
  apply H in b. ssa. asimpl in H1.  inv H1. exists x. ssa. ctac. 

- ctac. apply subst_sch_sch_fv in a. ssa. exists x. ssa. ctac. 
  lor. apply subst_sch_sch_fv in H0. ssa. exists x. ssa. ctac. rewrite H0. lia.
  apply H in H0. ssa. exists x. ssa. ctac. lia.

- ctac. apply subst_sch_sch_fv in a. ssa. exists x. ssa. ctac. 
  ptac. ptac. apply H in H1. ssa. asimpl in H2. de x0. inv H2.
  asimpl in H2. 
  exists x0.  ssa. ctac. right. asimpl in H2. apply/mapP. exists x0.+1. 
  rewrite mem_filter. ssa. done. de (sig3 x0). inv H2. 

- ctac. apply subst_sch_sch_fv in a. ssa. exists x. ssa. ctac. 
  apply H in b. ssa. exists x. ssa. ctac.

- ctac. apply subst_sch_sch_fv in a. ssa. exists x. ssa. ctac. 
  ptac. ptac. ptac. asimpl in q.  destruct x;ssa. 
  eapply H in p as p'. 2 : eauto. ssa. exists x. ssa. ctac. right.
  apply/flattenP. exists (proc_sch_fv p0). apply/mapP. exists (n0,p0). done.
  done. done.

- ctac. apply H in a. ssa. exists x. ssa. ctac.
  apply H0 in b. ssa. exists x. ssa. ctac. 

- ctac. apply H in a. ssa. exists x. ssa. ctac.
  apply H0 in b. ssa. exists x. ssa. ctac. 

- apply H in H0. ssa. exists x. ssa. 

- apply H in H0. ssa. asimpl in H1.  inv H1. exists x. ssa. 

- ptac. ptac. ptac. apply subst_sch_sch_fv in q. ssa.
  exists x0. ssa. apply/flattenP. exists (sch_fv x). apply/map_f.  done. 
  done.

- ptac. ptac. ptac. apply subst_msgp_fv in q. ssa. exists x0. 
  ssa. apply/flattenP. exists (msgp_sch_fv x). apply/map_f. done.
  done.
Qed. 

Hint Resolve map_f. 

Lemma sch_fv_subst : forall s sig2 sig3 n,  n \in sch_fv s ->
  sig3 n \in  (sch_fv (subst_sch (sig2 >> var_schl) (sig3 >> var_sch) s)). 
Proof.
elim;ssa. rewrite inE in H. norm_eqs. 
done.
Qed.

Lemma msgp_sch_fv_subst : forall s sig0 sig1 sig2 sig3 n,  n \in msgp_sch_fv s ->
   sig3 n \in  (msgp_sch_fv ((subst_msgp (sig0 >> var_val) (sig1 >> var_valBool) (sig2 >> var_schl) (sig3 >> var_sch)) s)). 
Proof.
elim;ssa.  de m. apply sch_fv_subst.  done.
Qed.

Lemma exp_valBool_fv_subst : forall s sig0 sig1  n, n \in exp_valBool_fv s ->
  sig1 n \in  (exp_valBool_fv (subst_exp (sig0 >> var_val) (sig1 >> var_valBool) s)). 
Proof.
elim;ssa. de v. rewrite inE in H. norm_eqs. done.
rewrite mem_cat in H1. de (orP H1). rewrite mem_cat. apply/orP. left. eauto. rewrite mem_cat. apply/orP. eauto.
Qed.

Lemma msgp_valBool_fv_subst : forall s sig0 sig1 sig2 sig3 n,  n \in msgp_valBool_fv s ->
   sig1 n \in  (msgp_valBool_fv ((subst_msgp (sig0 >> var_val) (sig1 >> var_valBool) (sig2 >> var_schl) (sig3 >> var_sch)) s)). 
Proof.
elim;ssa.  de m. de v.  rewrite inE in H. norm_eqs. done.
Qed.

Lemma ForallT_in : forall (A : Type) (P : A -> Prop) (l : seq A) a, In a  l -> ForallT P l -> P a.
Proof.
move=> A P. intros. induction X. done. ssa. de H. subst. eauto.
Qed.

Lemma proc_sch_subst : forall P n, n \in proc_sch_fv P -> forall sig0 sig1 sig2 sig3,  sig3 n \in (proc_sch_fv (subst_process (sig0 >> var_val) (sig1 >> var_valBool) (sig2 >> var_schl) (sig3 >> var_sch) P)).
Proof.
elim/process_ind2;ssa. 
- de (mapP H0). rewrite mem_filter in H1. ssa. 
  subst.  de x.
  move : (H _ H4 sig0 sig1 sig2 (0 .: sig3>> succn)).
  asimpl. simpl. intros. 
  apply/mapP. econ. rewrite mem_filter. apply/andP. con. 2:eauto. done. done.
- de (mapP H0). rewrite mem_filter in H1. ssa. 
  subst.  de x.
  move : (H _ H4 sig0 sig1 sig2 (0 .: sig3>> succn)).
  asimpl. simpl. intros. 
  apply/mapP. econ. rewrite mem_filter. apply/andP. con. 2:eauto. done. done.

- rewrite mem_cat in H0. de (orP H0).
  rewrite mem_cat. apply/orP. left. apply/sch_fv_subst. done.
  move: (H _ H1 sig0 sig1 sig2 sig3). rewrite mem_cat. move=>->//. by rewrite orbC //.

- rewrite mem_cat in H0. de (orP H0).
  rewrite mem_cat. apply/orP. left. apply/sch_fv_subst. done.
  move: (H _ H1 sig0 (0 .: sig1 >> succn) sig2 sig3). rewrite mem_cat. asimpl. move=>->//. by rewrite orbC //.
  
- rewrite mem_cat in H0. de (orP H0).
  rewrite mem_cat. apply/orP. left. apply/sch_fv_subst. done.
  rewrite mem_cat in H1. de (orP H1). rewrite !mem_cat. apply/orP. right. apply/orP. left.
  apply/sch_fv_subst. done.
  rewrite !mem_cat. apply/orP. right. apply/orP. right.
  by move: (H _ H2 sig0 sig1 sig2 sig3).

- rewrite mem_cat in H0. de (orP H0).
  rewrite mem_cat. apply/orP. left. apply/sch_fv_subst. done.
  de (mapP H1). rewrite mem_filter in H2. ssa.
  move: (H _ H5 sig0 sig1 sig2 (0 .: (sig3 >> succn)))=>HH. 
  asimpl.  rewrite mem_cat. apply/orP. right. apply/mapP. econ.
  rewrite mem_filter. apply/andP. con. 2: {   asimpl in HH. eauto. } 
                                     asimpl. de x. de x.

- rewrite mem_cat in H0. de (orP H0).
  rewrite mem_cat. apply/orP. left. apply/sch_fv_subst. done.
  move: (H _ H1 sig0 sig1 sig2 sig3).
  rewrite mem_cat. move=>->. rewrite orbC //.

- rewrite mem_cat in H. de (orP H).
  rewrite mem_cat. apply/orP. left. apply/sch_fv_subst. done.
  de (flattenP H0). de (mapP H1). subst.
  asimpl in H1. asimpl in H2. clear H1 H0 H.
  rewrite mem_cat. apply/orP. right.
  eapply ForallT_in in X. 2: { apply/inP. eauto. } 
                        ssa. 
  move: (X _ H2 sig0 sig1 sig2 sig3). 
  ssa. 
  apply/flattenP. econ.  asimpl. rewrite -!map_comp. apply/mapP. econ. eauto. econ. asimpl.
  rewrite /prod_map. ssa. de x0.

- rewrite mem_cat in H1. de (orP H1).
  rewrite mem_cat. apply/orP. left. eauto. rewrite mem_cat. apply/orP. eauto.
- rewrite mem_cat in H1. de (orP H1).
  rewrite mem_cat. apply/orP. left. eauto. rewrite mem_cat. apply/orP. eauto.

  move: (H _ H0 sig0 sig1 (0 .: sig2>> succn) sig3). asimpl. done.

  move: (H _ H0 (0 .: sig0>> succn) sig1 sig2 sig3). asimpl. done.

- de (flattenP H). apply/flattenP. de (mapP H0). subst.
  econ. apply/mapP. econ. apply/mapP. econ. eauto. econ. econ. asimpl.
  apply:sch_fv_subst. done.

- de (flattenP H). apply/flattenP. de (mapP H0). subst.
  econ. apply/mapP. econ. apply/mapP. econ. eauto. econ. econ. asimpl.
  move: (@msgp_sch_fv_subst _ sig0 sig1 sig2 sig3 _ H1). done.
Qed.




Lemma proc_valBool_subst : forall P n, n \in proc_valBool_fv P -> forall sig0 sig1 sig2 sig3,  sig1 n \in (proc_valBool_fv (subst_process (sig0 >> var_val) (sig1 >> var_valBool) (sig2 >> var_schl) (sig3 >> var_sch) P)).
Proof.
elim/process_ind2;ssa. 
-  move : (H _ H0 sig0 sig1 sig2 (0 .: sig3 >> succn)). asimpl.  done.
-  move : (H _ H0 sig0 sig1 sig2 (0 .: sig3 >> succn)). asimpl.  done.

- rewrite mem_cat in H0. de (orP H0).
  rewrite mem_cat. apply/orP. left. apply exp_valBool_fv_subst. done.
  rewrite mem_cat. apply/orP. eauto.

- de (mapP H0). rewrite mem_filter in H1. ssa. subst.
  move : (H _ H4 sig0 (0 .: sig1 >> succn) sig2 sig3). intros.
  apply/mapP. econ. rewrite mem_filter. apply/andP. con. 2: { asimpl. asimpl in H1. eauto. } 
                                                       de x. de x. 
  move : (H _ H0 sig0 sig1 sig2 (0.: sig3 >> succn)). asimpl.  done.

  de (flattenP H). de (mapP H0). subst.
  asimpl in H0. asimpl in H1. 
  eapply ForallT_in in X. 2: { apply/inP. eauto. } 
                        ssa. 
  move: (X _ H1 sig0 sig1 sig2 sig3). 
  ssa. 
  apply/flattenP. econ.  asimpl. rewrite -!map_comp. apply/mapP. econ. eauto. econ. asimpl.
  rewrite /prod_map. ssa. de x0.

- rewrite mem_cat in H1. de (orP H1).
  rewrite mem_cat. apply/orP. left.  apply/exp_valBool_fv_subst. done.
  rewrite !mem_cat in H2 *. de (orP H2). 
  right. apply/orP. left. eauto. right. apply/orP. eauto.

- rewrite mem_cat in H1. de (orP H1).
  rewrite mem_cat. apply/orP. left.  eauto. 
  rewrite !mem_cat in H2 *. apply/orP. eauto.

  move : (H _ H0 sig0 sig1 (0.: sig2 >> succn ) sig3). asimpl. done.

  move : (H _ H0 (0.: sig0 >> succn ) sig1 sig2 sig3). asimpl. done.

  apply/exp_valBool_fv_subst. eauto.

- de (flattenP H). apply/flattenP. de (mapP H0). subst.
  econ. apply/mapP. econ. apply/mapP. econ. eauto. econ. econ. 
  move: (@msgp_valBool_fv_subst _ sig0 sig1 sig2 sig3 _ H1). done.
Qed.


Lemma Cong_no_sch : forall P P' n, Cong P P' -> n \in proc_sch_fv P' <-> n \in proc_sch_fv P.  
Proof. 
move => P P' n H. 
elim : H n;ssa;rewrite ?mem_cat.
split;ssa.
de (orP H);ssa.
split;ssa. apply/orP. rewrite orbC. done.
rewrite orbC in H. apply/orP. done.
rewrite orbA. done.
split. move/orP. case. ssa.
move/subst_proc_sch_fv. ssa. eauto. rewrite /ids in H0.
inv H0. eauto.
move/orP. case. ssa.
intros. apply/orP. right. 
apply/proc_sch_subst. done.
split. move/orP. case. ssa.
move/subst_proc_sch_fv. ssa. rewrite /ids in H0. inv H0. ssa.
move/orP. case. ssa.
ssa. right. apply/proc_sch_subst. done.
rewrite H0. done.
rewrite -H0.
rewrite -H2. done.
Qed. 

Lemma in_reduce : forall P n, n \in proc_sch_fv (reduce_link P) -> n \in proc_sch_fv P.
Proof. 
elim/process_ind;ssa. 
apply subst_proc_sch_fv in H0. ssa. destruct x;ssa.   inv H1. apply/mapP.  exists n0.+1.
rewrite mem_filter. ssa. done.
apply subst_proc_sch_fv in H0. ssa. destruct x;ssa.   inv H1. apply/mapP.  exists n.+1.
rewrite mem_filter. ssa. done.
ctac.
Qed.

Lemma Sem_no_sch : forall D P P' n, Sem D P P' -> n \in proc_sch_fv P' -> n \in proc_sch_fv P.  
Proof. 
move => D P P' n H. 
elim : H n;ssa.
- rewrite mem_cat in H0. destruct (orP H0). apply in_reduce in H1. done.
  move : (@make_queues_no_sch_var (make_cs q) n). rewrite H1 //=. 
- rewrite mem_cat in H0. destruct (orP H0). rewrite mem_cat H1 //=. 
  destruct (flattenP H1). destruct (mapP H2). subst. rewrite mem_cat. apply/orP. right. 
  apply/flattenP. rewrite mem_cat in H4. destruct (orP H4). exists (msgp_sch_fv x0).  apply/map_f. ssa.  done.
  ssa. rewrite inE in H5. norm_eqs.  ssa.

- rewrite mem_cat in H. destruct (orP H). rewrite mem_cat H0 //=. 
  rewrite mem_cat.  apply/orP. right. 
  destruct (flattenP H0). destruct (mapP H1). subst. rewrite mem_cat in H3. 
  destruct (orP H3). apply/flattenP. exists (msgp_sch_fv x0). eauto. done. ssa. rewrite inE in H4. norm_eqs. ssa. 

- rewrite mem_cat in H. destruct (orP H). rewrite mem_cat H0 //=. 
  destruct (flattenP H0). destruct (mapP H1). subst. rewrite mem_cat. apply/orP. right. 
  apply/flattenP. rewrite mem_cat in H3. destruct (orP H3). exists (msgp_sch_fv x0).  apply/map_f. ssa.  done.
  ssa. rewrite inE in H4. norm_eqs.  ssa.

- rewrite mem_cat in H. destruct (orP H). rewrite /my_subst_valBool in H0. 
  apply subst_proc_sch_fv in H0. destruct H0. ssa. inv H1. rewrite mem_cat H0 //=.  
  rewrite mem_cat. apply/orP. right. done. 

- rewrite mem_cat in H. destruct (orP H). rewrite /my_subst_schl in H0. 
  apply subst_proc_sch_fv in H0. destruct H0. ssa. destruct x;ssa. inv H1. 
  rewrite mem_cat. apply/orP. left. apply/mapP. exists n.+1. rewrite mem_filter. ssa. done. 
  rewrite mem_cat. apply/orP. right. done. 

- rewrite mem_cat in H0. destruct (orP H0). 
  rewrite mem_cat. apply/orP. left. apply/flattenP. exists (proc_sch_fv P0).
  have : P0 = (l,P0).2 by done. move=>->. apply/map_f. apply/in_pair. done. done.
  rewrite mem_cat H1. lia.

- rewrite mem_cat H0 //=.

- rewrite mem_cat H0. lia. 

- ssa. apply subst_proc_sch_fv in H1. destruct H1. ssa. clear H1.
  elim : x ss n H2. case;ssa. rewrite mem_cat. rewrite H2 //= inE //= eqxx //=. 
  ssa. destruct ss;ssa. apply H1 in H2. rewrite mem_cat  H2 . lia.

- move : H1. rewrite !mem_cat. move/orP. case;eauto.  move/H0. move=>-> //=. 
  move=>->. lia. apply/Cong_no_sch. apply/CSym. eauto. 
  apply/H1. 
  apply/Cong_no_sch. apply/CSym. eauto. done.
Qed. 

Definition sch_closed (P : process) := (forall n, n \notin proc_sch_fv P).  
Definition valBool_closed (P : process) := (forall n, n \notin proc_valBool_fv P).  

Lemma Sem_closed : forall D P P', Sem D P P' -> sch_closed P -> sch_closed P'. 
Proof. 
intros.  intro. apply/negP. intro. apply/negP. apply/H0. 
2 : { apply/Sem_no_sch. eauto. eauto. } 
Qed. 

Lemma subst_sch_eq : forall s sig sig' sig'', (forall n, n \in sch_fv s -> sig' n = sig'' n) -> subst_sch sig sig' s = subst_sch sig sig'' s.
Proof. 
case;ssa.
Qed. 

Lemma subst_msgp_eq : forall s sig0 sig1 sig2 sig3 sig3', (forall n, n \in msgp_sch_fv s -> sig3 n = sig3' n) -> subst_msgp sig0 sig1 sig2 sig3 s = subst_msgp sig0 sig1 sig2 sig3' s.
Proof. 
case;ssa. f_equal. destruct m;ssa. f_equal. apply/subst_sch_eq. eauto.  
Qed. 

Lemma subst_proc_eq : forall P sig0 sig1 sig2 sig3 sig3', (forall n, n \in proc_sch_fv P -> sig3 n = sig3' n) ->  subst_process sig0 sig1 sig2 sig3 P = subst_process sig0 sig1 sig2 sig3' P.
Proof. 
elim/process_ind;ssa;asimpl. 
- f_equal. erewrite H. eauto. intros. destruct n0;ssa.  asimpl. rewrite H0 //=. apply/mapP. exists n0.+1. ssa. 
  rewrite mem_filter. ssa. done.

- f_equal. erewrite H. apply/H. eauto. intros. destruct n;ssa.  asimpl. rewrite H0 //=. 
  apply/mapP. exists n.+1. rewrite mem_filter. ssa. done.

- f_equal. apply/subst_sch_eq. intros. apply/H0. ctac. 
  apply/H. ssa. apply/H0. ctac.

- f_equal. apply/subst_sch_eq. intros. apply/H0. ctac. 
  apply/H. ssa. apply/H0. ctac.

- f_equal. apply/subst_sch_eq. intros. apply/H0. ctac. 
  apply/subst_sch_eq. intros. apply/H0. ctac. lia.
  apply/H. ssa. apply/H0. ctac. lia.

- f_equal. apply/subst_sch_eq. intros. apply/H0. ctac. 
  apply/H. ssa. de n. asimpl. rewrite H0 //=. ctac. right. 
  apply/mapP. exists (n.+1). rewrite mem_filter. ssa. done.

- f_equal. apply/subst_sch_eq. intros. apply/H0. ctac. 
  apply/H. ssa. apply/H0. ctac. 

- f_equal. apply/subst_sch_eq. intros. apply/H0. ctac. 
  apply/eq_in_map. intro. ssa. destruct x;ssa. f_equal. 
  have : p = (n,p).2 by done. move=>->. apply/H=>//=.
  intros. apply/H0. ctac. right. apply/flattenP. exists (proc_sch_fv p). 
  have : p = (n,p).2 by done. move=>->. apply/map_f=>//=. 
  done.

- f_equal. apply/H. intros. apply/H1. ctac. 
  apply/H0. intros. apply/H1. ctac.

- f_equal. apply/H. intros. apply/H1. ctac. 
  apply/H0. intros. apply/H1. ctac.

- f_equal. apply/H. intros. asimpl. rewrite H0 //=. 

- f_equal. apply/H. intros. asimpl. rewrite H0 //=. 

- f_equal. apply/eq_in_map. intro. ssa. de x. apply/H. apply/flattenP. 
  exists (sch_fv (var_sch n)). eauto.  ssa. 

- f_equal. apply/eq_in_map. intro. ssa. apply/subst_msgp_eq. intros. apply/H.
  apply/flattenP. exists (msgp_sch_fv x). eauto. done.
Qed. 


Lemma channel_replacement_shift : forall P v, (forall n, n \in proc_sch_fv P -> n = 0) ->  subst_process ids ids (succn >> ids) (v.:ids) P =
                                                                    subst_process ids ids (succn >> ids) (v.:(succn>>ids)) P.
Proof. 
intros. apply/subst_proc_eq. intros. apply H in H0. subst. done. 
Qed. 


Definition check_gs  (gs : seq (schl * gType)) (f : (schl * ptcp) -> lpath) :=
(forall s g, lookup gs s = Some g -> forall p, checkPath (f (s,p)) (trans p g)) /\ uniq (dom gs). 

Definition balancedL (l : l_env) (gs : seq (schl * gType)) (f : schl * ptcp -> lpath) :=  
forall s p T, lookup l (schlT s p) = Some T -> exists g, lookup gs s = Some g /\  (makeL (f (s,p)) (trans p g)) = T.

Definition balancedQ (q : q_env) (gs : seq (schl * gType)) (f : schl * ptcp -> lpath) :=  
forall s p T, lookup q (QKey s p) = Some T -> exists g, lookup gs s = Some g /\  (makeQ (f (s,p)) (trans p g)) = T.

Definition sub_domLQ (L : l_env) (Q : q_env) := forall s p, schlT s p \in dom L -> QKey s p \in dom Q.







Lemma lookup_filter_q_2 : forall (Q : q_env) s p l f, lookup (filter_q Q f) (QKey s p) = Some l -> exists l', filter_keys (f (QKey s p)) l' = l /\ lookup Q (QKey s p) = Some l'.
Proof.
elim;ssa.  de (eqVneq a.1 (QKey s p)). rewrite e in H0.  
rewrite lookup_cons_eq in H0. inv H0.  exists a.2.  ssa. rewrite lookup_cons_eq. done. done.
ssa. rewrite lookup_cons_neq //= in H0. apply H in H0. de H0. exists x. ssa. 
rewrite lookup_cons_neq.  ssa. done. 
Qed. 



Lemma filter_keys_cons_p : forall (A B : eqType) p (l : seq (A * B)) l' x, filter_keys p l = x::l' -> p x.1.
Proof.
move => A B p. elim;ssa.
move : H0. case_if;ssa. inv H1. eauto.
Qed.


Lemma filter_keys_cons : forall (A B : eqType) p (l : seq (A * B)) l' x, filter_keys p l = x::l' -> exists l0 l1, l = l0++(x::l1) /\ all (predC p \o fst) l0.
Proof.
move => A B p. elim;ssa.
move : H0. case_if;ssa. inv H1.
exists nil. econ. ssa.
apply H in H1. ssa. subst. exists (a::x0). exists x1. ssa.
rewrite /predC. rewrite H0. done.
Qed.



Lemma in_dom_exists : forall (A B : eqType) (l : seq (A * B)) x, x \in dom l -> exists T, lookup l x = Some T. 
Proof. 
move => A B. elim;ssa.
rewrite inE in H0. de (eqVneq a.1 x). exists a.2. rewrite lookup_cons_eq. ssa. done.
rewrite lookup_cons_neq.  eauto. done.
Qed.

(*Lemma can_step_fe : forall e l, can_step l (fe e) -> can_step l e. 
Proof. 
intros. rewrite /full_eunf in H. 
remember (emu_height e). 
clear Heqn. ssa.
elim : n l e H. ssa.
ssa. apply/H. destruct (is_erec (iter n eunf e)) eqn:Heqn. 
destruct (iter n eunf e);ssa.
 apply/can_step_subst.  2 : eauto. ssa. de n0. 
have : eunf (iter n eunf e) = iter n eunf e. 
de (iter n eunf e);ssa. move=><-. done. 
Qed. *)


Require Import Paco.paco.
Lemma makeQ_EQ2: forall p l l', EQ2 l l' -> makeQ p l = makeQ p l'.
Proof.
elim;ssa. 
rewrite /obs. punfold H0. inv H0. inv H1. de d;ssa. de a. 
rewrite -H2  -H3. f_equal. de H4. 
de d. de a.
rewrite -H2 -H3.
clear H2 H3.
elim: es0 es1 H4 n H5.
case;ssa.
move => a1 l1 IH. case;ssa.
inv H5. ssa. destruct (eqVneq a1.1 n). 
rewrite !lookup_cons_eq. f_equal.
apply/H. de H3. rewrite -H2. done. done.
rewrite !lookup_cons_neq;ssa. rewrite -H2. done.
Qed.


Lemma checkPath_EQ2: forall p l l', EQ2 l l' -> checkPath p l -> checkPath p l'.
Proof.
elim;ssa.
move : H2. 
rewrite /obs. punfold H0. inv H0. inv H1. 
move : H3. rewrite /nexte_wrap. de a.
punfold H0. inv H0. inv H1. by rewrite -H5 in H3.
by rewrite -H4 in H3.
rewrite -H4 in H3. clear H1 H4 H5 H0 H2.
elim: es0 es1 H6 H7 H3.
case;ssa.
move=> a l1 IH. case;ssa.
move : H3. destruct (eqVneq a.1 n). subst. rewrite !lookup_cons_eq. 
inv H7. ssa. de H2. eauto. ssa. inv H7. ssa. inv H7.
rewrite !lookup_cons_neq. inv H7. ssa.
inv H7. ssa. de H1. rewrite -H0. done. done. 
ssa.
rewrite /obs in H2.
punfold H0. inv H0. inv H1;ssa.
by rewrite -H5 in H3.
de H6. rewrite -H4 in H3. rewrite -H4 in H2.
de d. eauto.
rewrite -H4 in H3. ssa.
Qed.

Definition coherent_gTypes (Ms : seq (schl * gType )) := forall k v, lookup Ms k = Some v -> coherentG v. 

Definition balanced (l : l_env) (q : q_env) := exists gs (f : schl * ptcp -> lpath),
check_gs gs f /\ 
balancedL l gs f /\ 
balancedQ q gs f /\ coherent_gTypes gs.


Definition env_coherent  (l : l_env) (q : q_env) := exists gs (f : schl * ptcp -> lpath),
check_gs gs f /\ 
balancedL l gs f /\ 
balancedQ q gs f /\ coherent_gTypes gs /\
 (forall s g p, (s,g) \in gs -> p \in roles g -> schlT s (Ptcp p) \in dom l /\ QKey s (Ptcp p) \in dom q).

Definition partial_balanced (l : l_env) (q : q_env)  := exists l' f q' f', balanced l' q'  /\  filter_keys f l' = l /\ filter_q q' f' = q.


Lemma makeL_fe : forall p l, checkPath p l -> fe (makeL p l) = fe(makeL p (fe l)). 
Proof.
intros. de p;ssa. rewrite !full_eunf2. done.
rewrite /nexte_wrap. de o. rewrite full_eunf2.
 destruct (fe l) eqn:Heqn;ssa.
 destruct (fe l) eqn:Heqn;ssa.
Qed.



Require Import MPSTSR.linearity MPSTSR.linearityDecide.


(*The original definition of linearity using OutDep + masking is awkard. We derive something simpler below*)
Inductive OutDep2 : action -> seq action -> action -> Prop := 
| OD0 a0 a1 : IO_OO a0 a1 ->  OutDep2 a0 nil a1
| OD1 a0 a1 a2 l : OutDep2 a0 l a2 -> OutDep2 a0 (a1::l) a2
| OD2 a0 a1 a2 l : IO_OO a0 a1 -> OutDep2 a1 l a2 -> OutDep2 a0 (a1::l) a2.
Hint Constructors OutDep2.

Lemma to_OutDep2 : forall a0 aa a1, exists_dep OutDep a0 aa a1 -> OutDep2 a0 aa a1.
Proof.
move => a0 aa a1 [m [] Hsize [] Hout _].
elim : m aa a0 a1 Hsize Hout;
first by move => [] // a0 a1 _ /=; case Hcase: _/ =>// [af af'|]; case: Hcase=>Ha0 Hf;subst;eauto. 
move => a l IH [] // a0 l0 a1 a2 /= [] Hsize. 
case Hcase: a. case Hcase0: _/ =>// [af af' HIO|af af' aaf HIO Hout];first by case: Hcase0=>_ _; case: (mask l l0)=>//.
case: Hcase0=>Ha1 Ha0 Hmask. subst. apply/OD2=>//. by eauto.
move/IH=>/(_ Hsize) Hout. eauto.
Qed.

Inductive InDep2 : action -> seq action -> action -> Prop := 
| ID0 a0 a1 : II a0 a1 ->  InDep2 a0 nil a1
| ID1 a0 a1 a2 l : InDep2 a0 l a2 -> InDep2 a0 (a1::l) a2
| ID2 a0 a1 a2 l : IO a0 a1 -> InDep2 a1 l a2 -> InDep2  a0 (a1::l) a2.
Hint Constructors InDep2.

Lemma to_InDep2 : forall a0 aa a1, exists_dep InDep a0 aa a1 -> InDep2 a0 aa a1.
Proof.
move => a0 aa a1 [m [] Hsize [] Hout _].
elim : m aa a0 a1 Hsize Hout.
move => [] // a0 a1 _ /=. case Hcase: _/ =>// [af af' HIO| af af' aaf HIO Hin ];first by case: Hcase=>Ha0 Hf;subst;eauto. 
case: Hcase. move => Ha0 Ha1 Hnil;subst;eauto. case Hcase: _ / Hin =>//. 
move => a l IH [] // a0 l0 a1 a2 /= [] Hsize. 
case Hcase: a. case Hcase0: _/ =>// [af af' HIO|af af' aaf HIO Hout];first by case: Hcase0=>_ _; case: (mask l l0)=>//.
case: Hcase0=>Ha1 Ha0 Hmask. subst. apply/ID2=>//. by eauto.
move/IH=>/(_ Hsize) Hout. eauto.
Qed.


Lemma ch_diff : forall g a0 aa a1, Linear g -> Tr (a0::(aa++[::a1])) g -> Forall ( fun a' => (ptcp_to a') != ptcp_from a1) (a0::aa) -> 
                               ptcp_from a0 != ptcp_from a1 ->   action_ch a0 != action_ch a1. 
Proof.  
move => g a0 aa a1 Hlin Htr /List.Forall_cons_iff [] Ha0 Hfor.
move : Htr. have : a0 :: aa ++ [:: a1] = nil ++  a0 :: aa ++ [:: a1] by []. move=>-> Htr Hneq.
apply/eqP=>Hch. have : same_ch a0 a1. rewrite /same_ch Hch eqxx //. move => Hsame. clear Hch.
move/Linear_2 : (Hlin). move/(_ _ _ _ _ Htr Hsame)/to_OutDep2=>Hout.
clear Htr Hlin. have : ptcp_from a1 \notin a0. rewrite !inE negb_or neg_sym /= Hneq /= neg_sym Ha0 //.
clear Ha0 Hneq. move => Hnotin. suff : ~ same_ch a0 a1. rewrite Hsame //. clear Hsame g. exfalso.

move : Hout Hfor Hnotin =>/=. elim.
- move => a2 a3 + _. case/orP;first by move=>/eqP; rewrite !inE negb_or //; first by move=><-; rewrite eqxx//=; move=> /andP [] //.
  move/andP=>[] /eqP <-;  rewrite inE eqxx //.
- move => a2 a3 a4 l Hout IH /List.Forall_cons_iff [] H34 Hfor Hnotin. by eauto.
- move => a2 a3 a4 l. case/orP.
 * move/eqP=> Ha23 Hout IH /List.Forall_cons_iff [] Hneq Hfor Hnotin. apply/IH;eauto.
   move: Hnotin. rewrite !inE !negb_or !Ha23. ssa.
   rewrite neg_sym Hneq //.
 * move/andP=>[] /eqP Ha23 Hch Hout IH /List.Forall_cons_iff [] Ha4 Hfor Hnot. apply/IH;eauto.
   move: Hnot. rewrite !inE !negb_or !Ha23. ssa. rewrite neg_sym.  done. 
Qed.

Definition nextg_wrap (n : option nat) (T : gType) := 
match n,full_unf T with 
| None, GMsg  _ _ T' => Some T'
| Some l, GBranch _ es => lookup es l 
| _,_=> None
end. 

Fixpoint makeG (l : lpath) (T : gType) := 
match l with 
| nil => T
| a::l' =>  if nextg_wrap a T is Some x then makeG l' x else GEnd
end.

Inductive ETr : seq (dir * ch * (value + nat)) -> lType -> Prop := 
| ET0  e : ETr nil e
| ET1 d c l u e e0 :  full_eunf e = EMsg d c u e0 -> ETr l e0  -> ETr ((d,c,inl u)::l) e
| ET2 n e e0 es l d c : full_eunf e = EBranch d c es ->  (n,e0) \in es -> ETr l e0 -> ETr ((d,c,inr n)::l) e.
Hint Constructors ETr.


Lemma ETr_unf : forall d e' e, ETr d e' -> e' = (fe e) -> ETr d e.
Proof.
move=> d e' e HT. elim : HT e;ssa. subst.
econ. rewrite full_eunf_idemp in H.     eauto.  done.
subst. rewrite full_eunf_idemp in H. econstructor 3. eauto. eauto. eauto.
Qed.

Lemma ETr_unf2 : forall d e, ETr d e -> ETr d (fe e).
Proof.
move=> d e. elim;ssa. econ. rewrite full_eunf_idemp. eauto. done.
econstructor 3. rewrite full_eunf_idemp. eauto. eauto. done.
Qed.

Lemma size_part : forall p g, part_of_all2 p g -> ~ part_of2 p g ->  size_pred g ->  False.  
Proof. 
move => p g. elim/part_of_all2_ind2;intros;try done.  rewrite part_of2_iff in H1. 
rewrite H0 in H1. apply size_pred_full_unf in H2. rewrite H0 in H2. have : ~comp_dir p a by eauto. done. 
apply/H1. rewrite part_of2_iff H2 in H3. eauto. apply size_pred_full_unf in H4. rewrite H2 in H4. 
ssa'. rewrite part_of2_iff H0 in H1. have : ~ comp_dir p a by eauto. done.
apply  size_pred_full_unf in H4. rewrite H2 in H4. ssa'. destruct gs;try done. apply/H1. 
simpl. auto. apply/H0. simpl.  auto. rewrite part_of2_iff H2 in H3.
have : In p0 (p0::gs). simpl. auto. eauto. ssa'. 
Qed.


Definition proj_act (p : ptcp) (a : action) := 
if comp_dir p a is Some d then (d,action_ch a)::nil else nil.

Definition proj_tr p (l : seq action) := flatten (map (proj_act p) l).


Lemma In_zip1 : forall (A B : Type) (a : A) l (l1 : seq B), In a l -> size l = size l1 -> exists a1, In a1 l1 /\ In (a,a1) (zip l l1). 
Proof. 
move => A B a. elim=> [] //=.
move => a0 l IH [] //= a1 l0 [ -> [Hsize ] |  Hin [Hsize] ].
- exists a1=>//=. ssa. 
- move : (IH _ Hin Hsize)=>[] x [] Hin2 Hin3. exists x. ssa. 
Qed.

Arguments In_zip1 {_} {_} {_}. 

Lemma In_zip2 : forall (A B : Type) (a1 : B) (l : seq A) (l1 : seq B), In a1 l1 -> size l = size l1 -> exists a, In a l /\ In (a,a1) (zip l l1). 
Proof. 
move => A B a1. elim=> [] //=. move=>[] //=.
move => a l IH [] //= a0 l0 [ -> [Hsize ] |  Hin [Hsize] ].
- exists a=>//=. ssa. 
- move : (IH _ Hin Hsize)=>[] x [] Hin2 Hin3. exists x. ssa. 
Qed.
Arguments In_zip2 {_} {_} {_}. 



Lemma in_zip1 : forall {A B : eqType} a (l : seq A) (l1 : seq B), a \in l -> size l = size l1 -> exists b, b \in l1 /\ (a,b) \in (zip l l1). 
Proof.
move => A B a l l1 /inP + Hsize. move/In_zip1. move/(_ _ _ Hsize)=> []x [] Hin Hinzip. exists x. con;by apply/inP.
Qed.

Lemma in_zip2 : forall (A B : eqType) (a1 : B) (l : seq A) (l1 : seq B), a1 \in l1 -> size l = size l1 -> exists a, a \in l /\ (a,a1) \in (zip l l1). 
Proof. intros. move/inP : H. intros. eapply In_zip2 in H. ssa. 
exists x. 
ssa. apply/inP.  eauto. apply/inP. eauto. done. 
Qed.


Lemma to_Tr : forall l e p g, ETr l e -> Project g p e -> size_pred g ->  exists l', Tr l' g /\ proj_tr p l' = map fst l.
Proof.
elim. ssa. exists nil. ssa.
ssa.
apply part_of_all_step in H1 as Hor.
de Hor.
- move: H3 H1 H2.
  elim/part_of_all2_ind2;intros.
 punfold H3. inv H3. rewrite H2 in H5. inv H5;ssa. 2: { rewrite H9 in H1;ssa.  }
  2: { exfalso. apply/H7. eauto. }  
 de H11. apply ETr_unf2 in H0. rewrite -H10 in H0. inv H0.
  inv H11. eapply H in H13. 2:eauto. ssa.
  econ. con. apply/Tr_full_unf2. rewrite H2. econstructor 2. apply/H7.
  rewrite /proj_tr. ssa. rewrite {1}/proj_act H8 /=. f_equal. done.
  apply size_pred_full_unf in H4. rewrite H2 in H4. ssa.

 punfold H5. inv H5. rewrite H4 in H7. inv H7. de H13. rewrite H10 in H1;ssa.
  de H13.
  2: {  exfalso. apply/size_part;eauto. apply size_pred_full_unf in H6. rewrite H4 in H6. ssa. }
  apply Project_eunf in H8. 
  apply size_pred_full_unf in H6. rewrite H4 in H6. ssa.
  apply H3 in H8;eauto. ssa.
  econ. con. apply/Tr_full_unf2. rewrite H4. constructor 2. apply H8.
  rewrite /proj_tr. simpl. rewrite {1}/proj_act. destruct (comp_dir _ _);ssa.

  punfold H3. inv H3. rewrite H2 in H5. apply size_pred_full_unf in H4. rewrite H2 in H4.
  ssa. inv H5. 2: {  rewrite H9 in H1;ssa. } 2: {  exfalso. apply/H8. con. con. con. done. } 
  apply ETr_unf2 in H0. rewrite -H9 in H0. inv H0. 
  inv H13. move/in_zip2 : H14. move/( _ _ _ H11). ssa.
  move/inP : H8. move/H12. ssa. de H14.
  eapply H in H16;eauto. de x.
  econ. con. apply/Tr_full_unf2. rewrite H2. econstructor 3. eauto. apply H15. 
  rewrite /proj_tr. ssa. rewrite {1}/proj_act H10 //=.  f_equal. done.
  apply (allP H7). done.


  punfold H5. inv H5. rewrite H4 in H7. inv H7. rewrite H11 in H1. done.
  2: {  exfalso.
 apply/size_part;eauto. con. con. econstructor 4.
        move=> g0. move/H2. ssa. 
        apply size_pred_full_unf in H6. rewrite H4 in H6;ssa. } 
  apply H3 in H11 as HH. ssa. de g0.
  de x.
  econ.  con. apply Tr_full_unf2. rewrite  H4. econstructor 3.  apply/inP. eauto.  apply H8.
  rewrite /proj_tr. ssa. rewrite {1}/proj_act H10 //=. apply H13 in H11. ssa.
  apply H13 in H11. ssa. de H9. apply Project_eunf in H9. done.
  apply size_pred_full_unf in H6. rewrite H4 in H6. ssa. apply (allP H9). apply/inP. done.

  exfalso.
  have : full_eunf e <> EEnd. inv H0;ssa. rewrite H6. intro. inv H4.
  intro. rewrite H6 in H4. inv H4.
  intro. apply Project_not_part2 in H1. rewrite H1 in x. done. done.
Qed.

Lemma flatten_Rd : forall x0 x p' c, flatten (list_map (proj_act p') x0) = x ++ [:: (Rd, c)] -> exists l a l', x0 = l++(a::l') /\ comp_dir p' a = Some Rd /\ action_ch a = c /\ proj_tr p' l = x.  
Proof.
elim;ssa. de x.
rewrite {1}/proj_act in H0.  destruct (comp_dir _ _) eqn:heqn;ssa.
de x. inv H0.
exists nil. exists a. exists l. ssa. 
inv H0. apply H in H3. ssa.
exists (a::x0). exists x1. exists x2. ssa. subst. done. rewrite /proj_tr. ssa. rewrite {1}/proj_act. rewrite heqn. ssa. f_equal. subst. done.
apply H in H0. ssa.
exists (a::x0). exists x1. exists x2. ssa. rewrite H0. done.
subst. rewrite /proj_tr. ssa. rewrite /proj_act. rewrite heqn. done.
Qed.

Lemma proj_tr_has : forall p aa d c, (d,c) \in proj_tr p aa -> has (fun y => (comp_dir p y == Some d) && (action_ch y == c )) aa.
Proof.
move=> p. rewrite /proj_tr.  elim;ssa. 
rewrite mem_cat in H0. de (orP H0).
rewrite /proj_act in H1. destruct (comp_dir _ _) eqn:Heqn;ssa.
rewrite inE in H1. norm_eqs. inv H1. rewrite eqxx. ssa.
Qed.


Lemma Tr_action_pred : forall g s, Tr s g -> action_pred g -> forall x, x \in s -> ptcp_from x != ptcp_to x.
Proof.
move=> g s. elim;ssa.
rewrite !inE in H2. de (orP H2). norm_eqs. done. 
rewrite !inE in H3. de (orP H3). norm_eqs. done. apply/H1;eauto.
move/allP : H5. move/(_ _ H). ssa.
apply/H0;ssa. rewrite -action_pred_subst.  done. case;ssa.
Qed.


Lemma test_test : forall x v e c g p' ,ETr (x ++ [:: (Rd, c,v)]) e -> Project g p' e -> size_pred g -> Linear g ->  all (fun y => y.1.1 == Sd) x -> action_pred g -> all (fun y => y.1 != (Sd,c)) x.
Proof.
intros. 
eapply  to_Tr in H;eauto. ssa. rewrite map_cat in H5.
apply flatten_Rd in H5. ssa. subst. 
have : x2 :: x3 = [::x2] ++ x3. done.
intro. rewrite x0 in H.
rewrite catA in H. apply Tr_app in H. 
apply/allP. intro. ssa.
apply/eqP. intro. de x4. subst. 

eapply (@map_f _ _ fst) in H5. rewrite -H8 in H5.
apply proj_tr_has in H5. de (hasP H5). norm_eqs.
clear H5 x0.
apply in_split in H7. ssa. subst.
rewrite -catA in H.
have : forall y, y \in (x0 ++ (x4::x5) ++ [:: x2]) -> ptcp_from y != ptcp_to y.
intros.
apply/Tr_action_pred. eauto. done. done. 
move=> Hact.
apply H2 in H. have : same_ch x4 x2. rewrite /same_ch. apply/eqP. done.
move/H. ssa. clear H.
have : all (fun y => y.1 == Sd) (map fst x). rewrite all_map. ssa.
clear H3 => H3. rewrite -H8 in H3. clear H8.
clear H11.
move : H6 H10 H5 H7 H3 H4 Hact. 
move=>HC0 HC1. move/to_InDep2. move=>HI. move=>_ HA. clear HC1. move=> Hpred. 
elim : HI HC0 HA.
- ssa. rewrite /II in H. norm_eqs.
  move: HC0. rewrite /comp_dir. 
  case_if. norm_eqs.
  move: HA. rewrite /proj_tr. rewrite !map_cat. rewrite !flatten_cat. simpl. rewrite !all_cat.
  ssa. case_if;ssa. norm_eqs.
  move: HA. rewrite /proj_tr. rewrite !map_cat. rewrite !flatten_cat. simpl. rewrite !all_cat.
  ssa.  rewrite -H in H3. 
  rewrite /proj_act in H6. rewrite /comp_dir in H6. 
  have : ptcp_from a0 != ptcp_to a0. apply/Hact. rewrite mem_cat. rewrite !inE !eqxx orbC //=. 
  rewrite neg_sym. intro.  rewrite H in x1. rewrite (negbTE x1) in H6. rewrite H eqxx in H6. ssa.

- ssa. apply/H3;ssa.
  move: HA. rewrite /proj_tr. rewrite !map_cat. rewrite !flatten_cat. simpl. rewrite !all_cat.
  ssa. 
  apply/Hact. move: H4. rewrite !mem_cat !inE !mem_cat.
  move/orP. case. move=>->. ssa. move/orP. case. move=>->. ssa. move/orP. case.
  move=>->. ssa. right. rewrite orbA orbC //=.
  move=>->. ssa. right.  ssa. right. ssa.  right. rewrite orbC //=.

- ssa. apply H4;ssa.
  move: HA. rewrite /proj_tr. rewrite !map_cat. rewrite !flatten_cat. simpl. rewrite !all_cat.
  ssa. 
  apply/Hact.
  move: H5. rewrite !mem_cat !inE !mem_cat.  
  move/orP. case. move=>->. ssa.
  move/orP. case. move=>->. ssa. right.  rewrite orbC //=. 
  move/orP. case. move=>->.  ssa. right. ssa. right. ssa. 
  move=>->. repeat (ssa;right).
Qed.


Inductive canEstep : lType -> elabel ->  Prop :=
| estep1_msg d c v e0  : canEstep (EMsg d c v e0) (d,c, inl v)
| estep1_msg_async d vn c c' v e0  : canEstep e0 (d,c,vn) -> c <> c' -> 
                                         canEstep (EMsg Sd c' v e0) (d,c,vn) 
| estep1_branch n e es d c   : (n,e) \in es -> 
                              canEstep (EBranch d c es) (d,c, inr n)
| estep1_branch_async es vn d n e  c c'  : (n,e) \in es -> canEstep e (d,c,vn)  -> c <> c' ->
                                            canEstep (EBranch Sd c' es) (d,c,vn)
| estep1_rec e l : canEstep (e [e ERec e .: EVar]) l -> canEstep (ERec e) l.
Hint Constructors canEstep.

Lemma canEstep_unf : forall e0 l, canEstep (eunf e0) l -> canEstep e0 l.
Proof. 
intros. destruct e0;try done. simpl in H. constructor. done. 
Qed.

Lemma canEstep_full_unf : forall e0 l, canEstep (full_eunf e0) l -> canEstep e0 l.
Proof. 
intros. rewrite /full_eunf in H.  remember (emu_height e0). clear Heqn. elim : n e0 H;try done. 
intros. apply/canEstep_unf. apply/H. rewrite iterSr in H0. done. 
Qed.

Lemma canEstep_unf2 : forall e0 l, canEstep e0 l -> canEstep (eunf e0) l.
Proof. 
intros. destruct e0;try done. inversion H. simpl. done. 
Qed.

Lemma canEstep_full_unf2 : forall e0 l, canEstep e0 l -> canEstep (full_eunf e0) l.
Proof. 
intros. rewrite /full_eunf.  remember (emu_height e0). clear Heqn. elim : n e0 H;try done. 
intros. rewrite iterS.  apply/canEstep_unf2. eauto. 
Qed.

Fixpoint can_gstep1 (l : elabel) p (g: gType)  :=
match g with 
| GMsg a u g' => (to_elabel a (inl u) p == Some l) || ((ptcp_to a != p) && (implb (ptcp_from a == p) (action_ch a != l.1.2))) && (can_gstep1 l p g')
| GBranch a gs => ((to_elabel a l.2 p == Some l) && (if l.2 is inr n then n \in (map fst gs) else false)) || ((ptcp_to a != p) && 
      (if ptcp_from a == p then (action_ch a != l.1.2) &&  (has ((can_gstep1 l p) \o snd) gs) else (all ((can_gstep1 l p) \o snd) gs)))
| GRec e0 => can_gstep1 l p e0
| _ => false
end. 


Lemma can_gstep1_ren : forall g l p sigma, can_gstep1 l p (g ⟨g sigma⟩) -> can_gstep1 l p g. 
Proof. 
elim;intros. ssa'. ssa'. ssa'. eauto. ssa'. 
destruct (orP H0). apply/orP. left. done. apply/orP. right. ssa'. eauto. 
ssa'. destruct (orP H0). apply/orP. left. rewrite -map_comp in H1.  ssa'.  rewrite fst_c in H3. done.  
ssa'. 
apply/orP. right. ssa'.
case_if. ssa.
rewrite has_map in H5. de (hasP H5). apply/hasP. econ. eauto.  ssa. de x.
eauto. ssa.
rewrite all_map in H3. apply/allP. intro. ssa. apply (allP H3) in H4 as HH. ssa.
de x. eauto.
Qed. 



Lemma can_gstep1_subst : forall g l p sigma,  size_pred g -> can_gstep1 l p (g [g sigma]) ->can_gstep1 l p g \/ exists n, can_gstep1 l p (sigma n). 
Proof. elim;intros;ssa'. eauto. 
move : H0 H1 => Hsize H0.
apply H in H0. de H0. right.  move: H0. syntax.asimpl. destruct x. simpl. done. simpl. syntax.asimpl. 
move/can_gstep1_ren. eauto. done.
move : H0 H1 => Hsize H0.
destruct (orP H0).
- left. apply/orP. left. done. 
- ssa. apply H in H3. de H3.
  left. apply/orP. right. ssa'. 
  right. eauto. done.
move: H1 H2 H3 => H0 H00 Hall.
destruct (orP H0). 
- left. apply/orP. left. destruct l0,s. ssa'. ssa'. rewrite -map_comp fst_c in H3. done. 
  ssa'. rewrite has_map all_map in H3. 
  case_if. ssa.
  de (hasP H5). de x.
  eapply H in H6;eauto. de H6. left.
  apply/orP.
  right. ssa'. apply/hasP. econ. eauto. done.
  right. eauto. apply (allP Hall) in H3. done.
  have : nth (0,GEnd) l 0 \in l. apply/mem_nth. done.
  move=>Hin. 
  clear H0 H1 H00. clear Hin. 
  suff : (ptcp_to a != p) && all (can_gstep1 l0 p \o snd) l \/
  (exists n : fin, can_gstep1 l0 p (sigma n)). ssa. de x. left. apply/orP. right. ssa.
  right. eauto.
  elim : l H Hall H3;ssa.
  rewrite H2 //. ssa.
  de a0. eapply H0 in H1;ssa. de H1.  apply H in H4;ssa.
  de H4. left. ssa.  right. eauto.
  eapply H0 in H8;ssa. right. eauto.
  have:  forall (n0 : fin) (g0 : gType),
       (n0, g0) \in  l ->
       forall (l : elabel) (p : ptcp) (sigma : fin -> gType),
       size_pred g0 ->
       can_gstep1 l p g0 [gsigma] ->
       can_gstep1 l p g0 \/
       (exists n : fin, can_gstep1 l p (sigma n)).
  eauto. intro. apply H in x0;ssa. eauto.
Qed.

Lemma can_gstep1_unf : forall g l p, size_pred g -> can_gstep1 l p (unf g) -> can_gstep1 l p g. 
Proof. case;try done. ssa'. apply can_gstep1_subst in H0. de H0. de x. done.
Qed. 

Lemma size_pred_iter_unf : forall n g, size_pred g ->  size_pred (iter n unf g). 
Proof. 
elim;ssa. apply size_pred_unf. eauto.
Qed.

Lemma can_gstep1_full_unf : forall g l p, size_pred g -> can_gstep1 l p (full_unf g) -> can_gstep1 l p g. 
Proof. intros. rewrite /full_unf in H0. remember (mu_height g). clear Heqn. 
elim : n g H H0. done. ssa'.
apply/H. done.
apply/can_gstep1_unf. apply/size_pred_iter_unf.  done. eauto.
Qed.

(*canEstep = Ant **)

Lemma project_can_step : forall g p e l, canEstep e l  -> Project g p e -> action_pred g -> size_pred g  -> can_gstep1 l p g.
Proof. 
move => g p e l Hstep Hproj. 
move : Hstep g p Hproj.
elim;intros.
move : H0 => Hsize.
apply part_of2_or_end in Hproj as Hproj'. destruct Hproj';try done.
move : H0 d c v e0 Hproj H  Hsize l e.
elim/part_of_all2_ind2;intros.
apply can_gstep1_full_unf;ssa.  rewrite H0. ssa'. rewrite /to_elabel.
destruct (comp_dir p a)eqn:Heqn;try done. 
apply Project_unfg2 in Hproj. rewrite H0 in Hproj.
punfold Hproj. invc Hproj. invc H2. rewrite H5 in Heqn. inv Heqn. rewrite eqxx //=. rewrite eqxx //=. 
apply can_gstep1_full_unf;ssa.  rewrite H2. ssa'. apply/orP. right. 
ssa'. move : H. rewrite /comp_dir. case_if;try done. case_if;try done. rewrite neg_sym H4 //=. 
apply/implyP. move/eqP. intros. 
subst. move : H.  rewrite /comp_dir eqxx. done.
apply Project_unfg2 in Hproj. rewrite H2 in Hproj.
punfold Hproj. invc Hproj. invc H4.
apply/H1. move : H10. cbn. eauto. all :try done. 
apply action_pred_full_unf in H3. rewrite H2 in H3. ssa'. apply size_pred_full_unf in Hsize. by rewrite H2 in Hsize.

apply can_gstep1_full_unf;ssa.  rewrite H0. ssa'. rewrite /to_elabel.
apply Project_unfg2 in Hproj. rewrite H0 in Hproj.
punfold Hproj. invc Hproj. invc H2. 

apply can_gstep1_full_unf;ssa.  rewrite H2. ssa'. rewrite /to_elabel.
apply Project_unfg2 in Hproj. rewrite H2 in Hproj.
punfold Hproj. invc Hproj. invc H2. invc H4.
rewrite H7 //=. ssa'.
move : H7. rewrite /comp_dir. case_if;try done. case_if;try done. rewrite neg_sym H4 //=.

case_if. norm_eqs. ssa.
apply/allP=> x xIn. apply/H1. apply/inP. done. apply/H0/inP. done.
move/inP : xIn. move/H10. ssa'. pclearbot. move : H5.  cbn. eauto. 
apply action_pred_full_unf in H3. rewrite H6 in H3. ssa'. 
move /inP : H8 => H8.
apply (allP H5) in xIn. done.
apply size_pred_full_unf in Hsize. rewrite H6 in Hsize. ssa.
apply (allP H5) in xIn. ssa.
all : try done. 

apply part_of2_or_end in Hproj as Hproj'. destruct Hproj';try done.

clear l.

move : H3 H4 => Hsize H3.

move : H3 e0 H Hproj H0 H2 Hsize.  
elim/part_of_all2_ind2;intros.

apply can_gstep1_full_unf;ssa.  rewrite H0. ssa'. rewrite /to_elabel.
destruct (comp_dir p a)eqn:Heqn;try done. 
apply Project_unfg2 in Hproj. rewrite H0 in Hproj.
punfold Hproj. invc Hproj. invc H5. rewrite /comp_dir eqxx in Heqn. inv Heqn.  
apply/orP. right. ssa'. 
apply action_pred_full_unf in H4. rewrite H0 in H4. ssa'. rewrite neg_sym. done. 
apply/implyP.  rewrite neg_sym. move => _. apply/eqP. done. apply/H3. done. 
apply action_pred_full_unf in H4. rewrite H0 in H4. ssa'. 

apply size_pred_full_unf in Hsize. rewrite H0 in Hsize. ssa.


apply Project_unfg2 in Hproj. rewrite H3 in Hproj.
punfold Hproj. invc Hproj. invc H7. rewrite /comp_dir eqxx in H. done. 

apply can_gstep1_full_unf;ssa. rewrite H3. ssa'. apply/orP. right. 
ssa'. move : H. rewrite /comp_dir. case_if;try done. case_if;try done. rewrite neg_sym H7 //=. 
apply/implyP. move/eqP. intros. 
subst. move : H.  rewrite /comp_dir eqxx. done.
apply/H2.  eauto. move : H13. cbn. eauto. all: try done.   
apply action_pred_full_unf in H6. rewrite H3 in H6. ssa'. 
apply size_pred_full_unf in Hsize. rewrite H3 in Hsize. ssa.

apply Project_unfg2 in Hproj. rewrite H0 in Hproj.
punfold Hproj. invc Hproj. invc H5.

apply can_gstep1_full_unf;ssa. rewrite H3. ssa'. apply/orP. right. 
ssa'. move : H. rewrite /comp_dir. case_if;try done. case_if;try done. rewrite neg_sym H7 //=. 

case_if. norm_eqs. ssa.

apply/allP=> x xIn. apply/H2. apply/inP. done. apply/H0/inP. done. eauto.
apply Project_unfg2 in Hproj. rewrite H3 in Hproj.
punfold Hproj. invc Hproj. invc H8. 
move/inP : xIn. move/H14. ssa. de H9. eauto.

apply action_pred_full_unf in H6. rewrite H3 in H6. ssa'. de x. apply (allP H9) in xIn. done.
apply size_pred_full_unf in Hsize. rewrite H3 in Hsize. ssa. apply (allP H9) in xIn. done.

apply part_of2_or_end in Hproj as Hproj'. destruct Hproj';try done.

clear l e.
move : H1 H2 => Hsize H1.

move : H1 n d c es Hproj H H0 Hsize. 
elim/part_of_all2_ind2;intros.

apply can_gstep1_full_unf;ssa. rewrite H0. ssa'. rewrite /to_elabel.
destruct (comp_dir p a)eqn:Heqn;try done. 
apply Project_unfg2 in Hproj. rewrite H0 in Hproj.
punfold Hproj. invc Hproj. invc H3. 

apply Project_unfg2 in Hproj. rewrite H2 in Hproj.
punfold Hproj. invc Hproj. invc H5. 
apply can_gstep1_full_unf;ssa. rewrite H2. ssa'. apply/orP. right. 
ssa'. move : H. rewrite /comp_dir. case_if;try done. case_if;try done. rewrite neg_sym H5 //=. 
apply/implyP. move/eqP. intros. 
subst. move : H.  rewrite /comp_dir eqxx. done.

apply/H1. move : H11.   cbn. eauto. all : try done. 
apply action_pred_full_unf in H4. rewrite H2 in H4. ssa'. 
apply size_pred_full_unf in Hsize. rewrite H2 in Hsize. ssa.

apply Project_unfg2 in Hproj. rewrite H0 in Hproj.
punfold Hproj. invc Hproj. invc H3.

apply can_gstep1_full_unf;ssa. rewrite H0. ssa'. apply/orP. left. 
rewrite /to_elabel H8.
ssa'. 
have :  exists a1, In a1 gs /\ In (a1,(n,e0)) (zip gs es).
apply/In_zip2. apply/inP=>//=. done. case. 
move => x. case. move => HH. move/H11. 
ssa'. 
subst. apply/map_f/inP. done. 


apply can_gstep1_full_unf;ssa. rewrite H2. ssa'. 
apply Project_unfg2 in Hproj. rewrite H2 in Hproj.
punfold Hproj. invc Hproj. invc H5. apply H11 in H9 as H9'. ssa'. 
apply/orP. right. ssa'. 
move : H. rewrite /comp_dir. case_if;try done. case_if;try done. rewrite neg_sym H7 //=. 

case_if. ssa. norm_eqs. move : H8. 
subst. rewrite /comp_dir eqxx. done.

apply/hasP. de g0.  econ. apply/inP. eauto. apply: H1. done. apply H11 in H9. ssa. apply H11 in H9. ssa. de H6.  apply Project_eunf in p0. eauto. done.




apply action_pred_full_unf in H4. rewrite H2 in H4. ssa'.
move/inP : H9. intro.
apply size_pred_full_unf in Hsize. rewrite H2 in Hsize. ssa. apply (allP H10) in H9. ssa. ssa.
move/inP : H9. intro.
apply size_pred_full_unf in Hsize. rewrite H2 in Hsize. ssa. apply (allP H10) in H9. ssa. 

apply/allP=> x xIn. apply/H1. apply/inP. done. move/inP : xIn. auto. 
move/inP : xIn. move/H11. ssa'. de H12. move : H12. cbn. eauto. done. 
apply action_pred_full_unf in H4. rewrite H2 in H4. ssa'.
move/inP : H9. intro. apply (allP H12) in xIn. done.
apply size_pred_full_unf in Hsize.
rewrite H2 in Hsize. ssa. apply (allP H12) in xIn. done.

apply part_of2_or_end in Hproj as Hproj'. destruct Hproj';try done.

clear l e. 
move : H4 H5 => Hsize H4.

move : H4 d c c' vn es Hproj H H0 H1 H2 H3 Hsize. 
elim/part_of_all2_ind2;intros.
apply Project_unfg2 in Hproj. rewrite H0 in Hproj. 
punfold Hproj. invc Hproj. invc H6. 

apply Project_unfg2 in Hproj. rewrite H2 in Hproj. 
punfold Hproj. invc Hproj. invc H8. 
apply can_gstep1_full_unf;ssa. rewrite H2. ssa'. 
apply/orP. right. ssa'. 
move : H. rewrite /comp_dir. case_if;try done. case_if;try done. rewrite neg_sym H8 //=. 
apply/implyP. move/eqP. intros. 
subst. move : H.  rewrite /comp_dir eqxx. done.
apply/H1. move : H14. cbn.  eauto. eauto. all : try done.  
apply action_pred_full_unf in H7. rewrite H2 in H7. ssa'. 
apply size_pred_full_unf in Hsize. rewrite H2 in Hsize. ssa'. 

apply Project_unfg2 in Hproj. rewrite H0 in Hproj. 
punfold Hproj. invc Hproj. invc H6. 
apply can_gstep1_full_unf;ssa. rewrite H0. ssa'. 
rewrite /to_elabel /comp_dir eqxx //=. apply/orP. right.  
apply action_pred_full_unf in H5. rewrite H0 in H5. 
apply size_pred_full_unf in Hsize. rewrite H0 in Hsize. 
ssa'. 
rewrite neg_sym //=. rewrite neg_sym //=. apply/eqP. done. 

move/in_zip2 : H1. move/(_ _ _ H13). ssa. de x.
move/inP : H5. move/H14. ssa. de H10. eapply H3 in H10;ssa. apply/hasP. econ. eauto. done.
apply (allP H9) in H1. done.
apply (allP H7) in H1. done.

apply can_gstep1_full_unf;ssa. rewrite H2. ssa'. 
apply/orP. right. ssa'. 
move : H. rewrite /comp_dir. case_if;try done. case_if;try done. rewrite neg_sym H8 //=. 

case_if. ssa. norm_eqs. 
move : H.  rewrite /comp_dir eqxx. done.
norm_eqs. move : H.  rewrite /comp_dir eqxx. done.

apply Project_unfg2 in Hproj. rewrite H2 in Hproj. 
punfold Hproj. invc Hproj. invc H9. norm_eqs. 

apply/allP. intro. ssa.  eapply H1;eauto. apply/inP. done.
move/inP : H9. move/H15;ssa.
move/inP : H9. move/H15;ssa. de H10.

apply action_pred_full_unf in H7. rewrite H2 in H7. ssa'. apply (allP H11) in H9. done. 
apply size_pred_full_unf in Hsize. rewrite H2 in Hsize. ssa'. apply (allP H11) in H9. done. 

have : Project g p  (e0 [e ERec e0 .: EVar]).  
punfold Hproj. invc Hproj. rewrite full_eunf_subst in H3. 
pfold. con. done.  move/H0. move/(_ H1).  move=>HH. apply HH. done.
Qed. 

Lemma can_gstep1_guarded : forall g l p i, can_gstep1 l p g -> size_pred g -> eguarded i(trans p g). 
Proof.
elim;intros. ssa'. ssa'. ssa'. erewrite H.  ssa'. eauto. eauto. done. 
ssa'. destruct (orP H0). move/eqP : H2. rewrite /to_elabel. destruct (comp_dir p a) eqn:Heqn. ssa'. done. 
ssa'. eapply H in H4. destruct (comp_dir p a). done. eauto. ssa'.
ssa'. destruct (orP H0). move/eqP : H1. rewrite /to_elabel. destruct (comp_dir p a) eqn:Heqn. done. done. 
ssa'. destruct l;try done. ssa'. 
move : H5. case_if;ssa. norm_eqs. rewrite /comp_dir eqxx //=.
destruct (comp_dir p a). done. 
eapply H.
instantiate (1 := p0.1). destruct p0. ssa'. apply/orP. left. done.  eauto.
done.
Qed. 


Inductive Tr2 : seq (action * (value + nat)) -> gType  -> Prop :=
| TR2_nil G : Tr2 nil G 
| TR2Msg a u aa g0 : Tr2 aa g0 -> Tr2 ((a,inl u)::aa) (GMsg a u g0)
| TR2Branch a n gs g aa  : (n,g) \in gs -> Tr2 aa g ->  Tr2 ((a,inr n)::aa) (GBranch a gs)
| TR2Unf aa g : Tr2 aa (unfg g)  -> Tr2 aa (GRec g).
Hint Constructors Tr2.

Lemma Tr21 : forall s g, Tr2 s g -> Tr (dom s) g.
Proof.
move=> s g. elim;ssa. econ. eauto. done.
Qed.

Lemma Tr_to_canStep : forall s' g,  Tr s' g -> forall s a, s' =  (s++[::a]) -> all (fun x => ptcp_to x \notin a) s -> exists vn, canStep g (a,vn).
Proof.
move=> s' g. elim;ssa. de s.
de s. inv H1. econ. econ.
inversion H1. apply H0 in H6;ssa. econ. econ. eauto. ssa.
rewrite negb_or //. move : H3. inv H1. rewrite inE negb_or. ssa.
de s. inv H2. econ. econ. eauto.
inversion H2. apply H1 in H7. ssa. econ.
econ. apply/inP. eauto. eauto.

move : H4. ssa. ssa.
apply H0 in H1;ssa. exists x. con. done.
Qed.

Lemma Tr2_to_canStep : forall s' g,  Tr2 s' g -> forall s a, s' =  (s++[::a]) -> all (fun x => ptcp_to x.1 \notin a.1) s ->  canStep g a.
Proof.
move=> s' g. elim;ssa. de s.
de s. inv H1. 
inversion H1. apply H0 in H6;ssa. econ. done. ssa.
rewrite negb_or //. move : H3. inv H1. rewrite inE negb_or. ssa.
de s. inv H2. econ. eauto.
inversion H2. apply H1 in H7. econ. apply/inP. eauto. eauto. 
inv H2.
apply H1 in H7;ssa.
econ. eauto.
Qed.


Lemma makeQ_ETr : forall l e l0 k u l1, checkPath l e -> makeQ l e = l0++((k,u)::l1) -> all (fun x => x.1 != k) l0 -> exists s, ETr (s++[::(Sd,k,u)]) e /\ all (fun x => (x.1.2 != k) && (x.1.1 == Sd)) s.
Proof.
elim;ssa. de l0.
move : H2 H3 H4 => Hall H2 H3.
rewrite /obs in H2. destruct (fe e) eqn:Heqn;ssa. de d. de a.
rewrite Heqn in H3 H1. rewrite /obs Heqn in H1.  ssa. 
de l0. inversion H1. subst.
exists nil. ssa. econ. eauto. done.
inv H1. apply H in H7;ssa. 
exists ((Sd,c,inl v)::x). ssa. econ. eauto. eauto.


de a. de d. rewrite Heqn in H1 H3. 
rewrite /obs in H1. rewrite Heqn in H1.
destruct (lookup _ _) eqn:Heqn2;ssa.
de l0. inv H1.
exists nil. ssa. econ. eauto. apply in_pair in Heqn2. eauto. done.
inv H1. apply H in H7;ssa.
exists ((Sd,c,inr n)::x). ssa. econ. eauto. apply in_pair in Heqn2. eauto.
eauto.
de d.
Qed.

Inductive canEstep2 : lType -> elabel -> Prop :=
| canestep2_msg d c v e0  : canEstep2 (EMsg d c v e0) (d,c, inl v)
| canestep2_branch n e es d c   : (n,e) \in es -> 
                              canEstep2 (EBranch d c es) (d,c, inr n).


Lemma makeQ_ETr2_aux : forall l e k u, checkPath l e -> canEstep2 (makeL l e) (Rd,k,u) ->  exists s, ETr (s++[::(Rd,k,u)]) e /\ all (fun x => x.1.1 == Sd) s.
Proof.
elim;ssa.
exists nil. ssa. 
inv H0. econ. eauto. done.
econ. eauto. eauto. done.
de a. destruct (fe _) eqn:Heqn2;ssa. destruct (lookup _ _) eqn:Heqn3;ssa.
rewrite /obs in H2. rewrite Heqn2 in H2. de d.
apply H in H1;ssa. exists ((Sd,c,inr n)::x). ssa. econ. eauto. apply in_pair in Heqn3. eauto. done.
destruct (fe _) eqn:Heqn2;ssa. 
apply H in H1;ssa.
exists ((Sd,c,inl v)::x). ssa. 
rewrite /obs Heqn2 in H2. de d.
econ. eauto. done.
Qed.

Lemma makeQ_ETr2 : forall l p g e k u, Project g p e -> size_pred g -> Linear g -> action_pred g -> checkPath l e -> canEstep2 (makeL l e) (Rd,k,u) ->  exists s, ETr (s++[::(Rd,k,u)]) e /\ all (fun x => (x.1.2 != k) && (x.1.1 == Sd)) s.
Proof.
intros. 
apply makeQ_ETr2_aux in H4;ssa. exists x. ssa.
eapply test_test in H;eauto.
apply/allP. intro. ssa. apply (allP H) in H6 as HH. de x0. de p0. ssa.
apply (allP H5) in H6. ssa. norm_eqs. apply/eqP. intro. subst. apply/negP. apply HH. apply/eqP. f_equal.
apply (allP H5) in H6. ssa.
Qed.




Inductive Trp (p : ptcp) : seq (dir * ch * (value + nat)) -> gType -> Prop := 
| GT0  g : Trp p nil g
| GT1 g a u g0 l d c :  full_unf g = GMsg a u g0 -> comp_dir p a = Some d -> action_ch a = c -> Trp p l g0  -> Trp p ((d,c,inl u)::l) g
| GT2 g a u' g0 l x :  full_unf g = GMsg a u' g0 -> comp_dir p a = None -> Trp p (x::l) g0  -> Trp p (x::l) g
| GT3 n a g g0 gs l d c : full_unf g = GBranch a gs -> comp_dir p a = Some d -> action_ch a = c ->  (n,g0) \in gs -> Trp p l g0 -> Trp p ((d,c,inr n)::l) g
| GT4 a g gs l  x: full_unf g = GBranch a gs -> comp_dir p a = None ->   (forall n g, (n,g) \in gs -> Trp p (x::l) g) -> Trp p (x::l) g.
Hint Constructors Trp.

Lemma Trp_full_unf : forall p l g, Trp p l (full_unf g) -> Trp p l g.
Proof.
intros. move : H. move Heq : (full_unf _ ) => g' Htr.
elim : Htr g Heq;ssa;subst. rewrite full_unf2 in H.
econ. eauto. done. done. done.
rewrite full_unf2 in H.
econ. eauto. done. done.
rewrite full_unf2 in H. econstructor 4. eauto. done. done.  eauto. done. eauto.
rewrite full_unf2 in H.
econstructor 5. eauto. done. eauto.
Qed.

Lemma to_Trp : forall s e, ETr s e -> forall g p, Project g p e -> Trp p s g.
Proof.
move=> s e. elim.
ssa.
intros. apply Project_eunf2 in H2. rewrite H in H2.
apply part_of2_or_end in H2 as HH. de HH. clear H.
elim/part_of_all2_ind2 : H3 u c d H2 H1;intros.
punfold H2. inv H2. inv H4. de H11.
rewrite H1 in H5. inv H5.
econ. eauto. done. done. eauto. 
rewrite H1 in H5. inv H5.
by rewrite H6 in H.
rewrite H1 in H5. inv H5.
punfold H4. inv H4. inv H6.
rewrite H3 in H7. inv H7. de H13. by rewrite H10 in H. 
de H9.
rewrite H3 in H7. inv H7. eauto.
rewrite H3 in H7. inv H7.

punfold H2. inv H2. inv H4;ssa. de H11.
rewrite H1 in H5. inv H5.
rewrite H1 in H5. inv H5.
rewrite H1 in H5. inv H5. rewrite H6 in H. done.

punfold H4. inv H4. inv H6. 
rewrite H3 in H7. inv H7.
rewrite H3 in H7. inv H7.
rewrite H3 in H7. inv H7.

econstructor 5. eauto. done.
intros. move/inP : H11.
intro. eapply H2 in H11;eauto. ssa. apply H10 in H11. ssa. de H12.

intros. 
apply Project_eunf2 in H3. rewrite H in H3. clear H.
apply part_of2_or_end in H3 as HH. de HH.
elim/part_of_all2_ind2 : H d c n e1 es H1 H2 H3 H0;ssa.
punfold H3. inv H3. inv H5.
de H8. rewrite H0 in H6. inv H6.
rewrite H7 in H. done.
rewrite H0 in H6. inv H6.
rewrite H0 in H6. inv H6.


punfold H5. inv H5. inv H7. de H10. rewrite H2 in H8. inv H8. 
econ. eauto. done. 
eapply H1. 4:eauto. done. eauto. 
eauto. 
rewrite H2 in H8. inv H8.
rewrite H2 in H8. inv H8.

punfold H3. inv H3. inv H5. de H8. rewrite H0 in H6. inv H6.
rewrite H0 in H6. inv H6.

move/in_zip2 : H4. move/(_ _ _ H11). ssa.
de x. move/inP : H7. move/H12. ssa. de H8. subst. eauto.
rewrite H0 in H6. inv H6. by rewrite H7 in H.

punfold H5. inv H5. inv H7. de H10. rewrite H2 in H8. inv H8.
rewrite H2 in H8. inv H8.
rewrite H12 in H. done.
rewrite H2 in H8. inv H8.
econstructor 5. eauto.  done.
intros. move/inP : H12.
intro. eapply H1 in H12. 5: {  simpl.  apply H11 in H12. ssa. de H13. move : H13. cbn. eauto. } 
ssa. eauto. ssa. apply H11 in H12. ssa. apply H3.
eauto. done.
Qed.



Inductive Trp2 (p : ptcp) : seq (ch * (value + nat)) -> gType ->  (dir * ch * (value + nat)) -> Prop := 
| GT20 g a u g0 l d : full_unf g = GMsg a u g0 -> comp_dir p a = Some d -> l = (d,action_ch a,inl u) -> Trp2 p nil g l
| GT20' g a gs l n d : full_unf g = GBranch a gs -> comp_dir p a = Some d -> l = (d,action_ch a,inr n) -> n \in dom gs -> Trp2 p nil g l
| GT21 g a u g0 l s x :  full_unf g = GMsg a u g0 -> comp_dir p a = Some Sd -> x = (action_ch a,inl u) ->
                             action_ch a != l.1.2 -> Trp2 p s g0 l  -> Trp2 p (x::s) g l
| GT22 g a u' g0 l s :  full_unf g = GMsg a u' g0 -> comp_dir p a = None -> Trp2 p s g0 l  -> Trp2 p s g l
| GT23 n a g g0 gs l s x : full_unf g = GBranch a gs -> action_ch a != l.1.2 -> comp_dir p a = Some Sd -> x = (action_ch a,inr n) ->
                               (n,g0) \in gs -> Trp2 p s g0 l -> Trp2 p (x::s) g l
| GT24 a g gs s l : full_unf g = GBranch a gs ->  comp_dir p a = None ->   (forall n g, (n,g) \in gs -> Trp2 p s g l) -> Trp2 p s g l.
Hint Constructors Trp2.

Lemma Trp2_full_unf : forall p l g l', Trp2 p l (full_unf g) l' -> Trp2 p l g l'.
Proof.
intros. move : H. move Heq : (full_unf _ ) => g' Htr.
elim : Htr g Heq;ssa;subst. rewrite full_unf2 in H.
econ. eauto. eauto. done. 
rewrite full_unf2 in H.
econstructor 2. eauto. eauto. eauto. eauto.
rewrite full_unf2 in H. econstructor 3. eauto. done. done. done. eauto.
rewrite full_unf2 in H. econstructor 4. eauto. done. done. 
rewrite full_unf2 in H. econstructor 5. eauto. done. done. eauto. eauto. done.
rewrite full_unf2 in H. econstructor 6. eauto. done. done. 
Qed.

Lemma Trp2_full_unf2 : forall p l g l', Trp2 p l (g) l' -> Trp2 p l (full_unf g) l'.
Proof.
intros. 
elim : H;rewrite ?full_unf2;ssa.
econ. rewrite full_unf2. eauto. eauto. done.
econstructor 2. rewrite full_unf2. eauto. eauto. eauto. done.
econstructor 3. rewrite full_unf2. eauto. eauto. eauto. done. eauto.
econstructor 4. rewrite full_unf2. eauto. eauto. eauto. 
econstructor 5. rewrite full_unf2. eauto. eauto. eauto. eauto. eauto. done.
econstructor 6. rewrite full_unf2. eauto. eauto. eauto. 
Qed.

Lemma to_Trp2 : forall p s g l, Trp p (s++[::l]) g -> all (fun x => (x.1.1 == Sd) && (x.1.2 != l.1.2)) s -> Trp2 p (map (fun x => (x.1.2,x.2)) s) g l.
Proof.
move=> p s g l. move Heq : (_ ++_ ) => s' H.
elim : H s l Heq;ssa.
de s. de s. inv Heq. econ. eauto. eauto. done.
inv Heq. ssa. econ. eauto. norm_eqs. done. done. done. eauto.
apply H2 in Heq;ssa. 
econ. eauto. done. done.
de s. inv Heq. econstructor 2. eauto. eauto. eauto. apply/mapP. econ. eauto. done.
inv Heq. econstructor 5. eauto.  ssa. norm_eqs. ssa. subst. eauto. ssa. eauto. 
eauto.
econstructor 6; eauto. 
Qed.


Lemma checkPath_fe  : forall l  e, checkPath l e -> checkPath l ( fe e).
Proof. elim;ssa.
move: H1. rewrite /obs. rewrite full_eunf2 //=.
move  : H2. rewrite /nexte_wrap. rewrite full_eunf2 //=.
Qed.

Lemma checkPath_fe2  : forall l  e, checkPath l (fe e) -> checkPath l e.
Proof. elim;ssa.
move: H1. rewrite /obs. rewrite full_eunf2 //=.
move  : H2. rewrite /nexte_wrap. rewrite full_eunf2 //=.
Qed.

Lemma checkPath_cat2 : forall l0 l1 e, checkPath (l0 ++ l1) e -> checkPath l1 (makeL l0 e).
Proof.
elim;ssa. apply/checkPath_fe. done.
destruct (nexte_wrap _ _) eqn:Heqn. eauto. done.
Qed.

Lemma makeQ_fe : forall l e, makeQ l e = makeQ l (fe e).
Proof. elim;ssa.
rewrite /obs /nexte_wrap  !full_eunf2 //=. 
Qed.


Lemma makeQ_cat2 : forall l0 l1 e, checkPath l0 e -> makeQ (l0 ++ l1) e = makeQ l0 e ++ (makeQ l1 (makeL l0 e)).
Proof.
elim;ssa. rewrite -makeQ_fe. done.
destruct (nexte_wrap _ _) eqn:Heqn;ssa. 
destruct (obs _ _) eqn:Heqn2;ssa.
f_equal. eauto.
Qed.


Lemma makeQ_size : forall l e, checkPath l e -> size (makeQ l e) = size l. 
Proof. 
elim;ssa. edestruct (obs _ _). edestruct (nexte_wrap _ _).  ssa. ssa.
done. 
Qed. 
Lemma makeQ_split3 : forall p l x c v y, checkPath p l ->  makeQ p l = x ++ (c, v) :: y ->
                                    exists x' v' y', p = x' ++ (v'::y') /\ size x' = size x /\ size y' = size y /\ obs v' (makeL x' l). 
Proof.
elim;ssa. de x.
rewrite /obs in H2. destruct (nexte_wrap a l0) eqn:Heqn. destruct (fe l0) eqn:Heqn2;ssa.  de d.
de a.  rewrite Heqn2 in Heqn. ssa. rewrite /obs Heqn2 in H1. ssa.
de x. inv H1.
exists nil. simpl. exists None. exists l. con. 
ssa. rewrite makeQ_size //.  ssa. rewrite /obs Heqn2 //=.
inv H1.
apply H in H5. ssa. exists (None::x0). exists x1. exists x2. ssa. subst. done.  rewrite Heqn2 //=.  inv Heqn. done.
destruct (obs _ _) eqn:Heqn3;ssa. de d. de a. rewrite Heqn2 in Heqn.
de x. exists nil. econ. econ.  simpl. ssa. 
inv H1. rewrite makeQ_size //. inv H1. rewrite /obs Heqn2 //=.
inv H1.
apply H in H5. ssa. exists (Some n::x0). exists x1. exists x2. subst. ssa.  rewrite Heqn2 //= Heqn //=.  done. 
de d. de a. rewrite Heqn2 in Heqn. de x.
de a.
Qed.
Lemma checkPath_cat : forall l0 l1 e, checkPath (l0 ++ l1) e -> checkPath l0 e. 
Proof. 
elim;ssa. edestruct (nexte_wrap _ _).  eauto. done.
Qed. 

Lemma makeL_cat : forall l l' e,  makeL (l ++ l') e = makeL l' (makeL l e).
Proof.
elim;ssa. elim : l'. ssa. rewrite full_eunf2. done. ssa.
have: nexte_wrap a (fe e)  = nexte_wrap a e. rewrite /nexte_wrap full_eunf2. done.
move=>->.
destruct (nexte_wrap a e);ssa. 
destruct (nexte_wrap a e);ssa. 
de l'. de o.
Qed.



Lemma filter_keys_mid : forall (A B : eqType) (l l0 l1 : seq (A * B)) f x, filter_keys f l = l0++x::l1 -> exists l0' l1', l = l0' ++ x::l1'.
Proof.
move=> A B. elim;ssa. de l0.
move : H0. case_if. ssa. de l0. inv H1. 
exists nil. exists l. done.
inv H1. apply H in H4. ssa. exists (p::x0). exists x1. subst. ssa.
intros. apply H in H1. ssa.
exists (a::x0). exists x1. subst. done.
Qed.

Lemma filter_keys_mid2 : forall (A B : eqType) (l l0 l1 : seq (A * B)) f x (f' : A -> bool), filter_keys f l = l0++x::l1 -> (forall x, f' x -> f x ) -> f' x.1 -> all ( fst >>predC f') l0 -> exists l0' l1', l = l0' ++ x::l1' /\ all (fst >> predC f') l0'.
Proof.
move=> A B. elim;ssa. de l0.
move : H0. case_if. ssa. de l0. inv H4. 
exists nil. exists l. done.
inv H4. eapply H in H8. ssa. exists (p::x0). exists x1. subst. ssa.
3:apply H2. done. eauto. done.
intros. eapply H in H4. ssa. 4:eauto.
exists (a::x0). exists x1. subst. ssa.  asimpl. apply/negP. intro. apply H1 in H4. rewrite H0 in H4. done. eauto. done.
Qed.

Lemma makeQ_split4 : forall p l x c v y, checkPath p l ->  makeQ p l = x ++ (c, v) :: y ->
                                    exists x' v' y', p = x' ++ (v'::y') /\ x = makeQ x' l /\ y = makeQ y' (makeL (x'++[::v']) l). 
Proof.
intros. apply makeQ_split3 in H0 as HH. ssa.
exists x0,x1,x2. ssa.
subst. rewrite makeQ_cat2 in H0.
move : H4 => Hobs.
have : take (size (makeQ x0 l)) (makeQ x0 l ++ makeQ (x1 :: x2) (makeL x0 l)) = take (size x) (x ++ (c,v):: y).
rewrite H0. rewrite makeQ_size. rewrite H2 //.
by apply checkPath_cat in H.
rewrite !take_size_cat //.
by apply checkPath_cat in H.
move : H4 => Hobs.
subst.
rewrite makeQ_cat2 in H0.
have : drop (size (makeQ x0 l)) (makeQ x0 l ++ makeQ (x1 :: x2) (makeL x0 l)) = drop (size x) (x ++ (c,v):: y).
rewrite H0. rewrite makeQ_size. rewrite H2 //.
by apply checkPath_cat in H.
rewrite !drop_size_cat //.
have : x1::x2 = [::x1]++x2. done. move=>->.
rewrite makeQ_cat2.
apply checkPath_cat2 in H as HH0.
have : x1::x2 = [::x1]++x2. done. intro. rewrite x3 in HH0.
apply checkPath_cat in H as HH1.
have :  makeQ [:: x1] (makeL x0 l)  = (c,v)::nil.
ssa. rewrite /obs in H1 *. destruct (fe (makeL x0 l)) eqn:Heqn;ssa. de d. de x1. rewrite Heqn.
rewrite Heqn in H0 H4. rewrite /obs in H0. rewrite Heqn in H0. ssa.
have : drop (size (makeQ x0 l)) ( makeQ x0 l ++ (c0, inl v0) :: makeQ x2 l0) = drop (size x) ( x ++ (c, v) :: y).
rewrite H0.
rewrite !drop_size_cat //. rewrite makeQ_size //.
rewrite !drop_size_cat;ssa. inv x1.
de d. de x1. destruct (fe _) eqn:Heqn2;ssa. destruct (lookup _ _) eqn:Heqn3;ssa.
rewrite /obs in H0. rewrite Heqn2 in H0. de d.

have : drop (size (makeQ x0 l)) ( makeQ x0 l ++ (c1, inr n) :: makeQ x2 s) = drop (size x) ( x ++ (c, v) :: y).
rewrite H0.
rewrite !drop_size_cat //. rewrite makeQ_size //.
rewrite !drop_size_cat;ssa. inv x1. inv Heqn. move=>->.
simpl. case. move=><-. ssa.
rewrite makeL_cat. ssa.
apply checkPath_cat2 in H.
have : x1::x2 = [::x1]++x2. done. intro. rewrite x3 in H.
apply checkPath_cat in H. done.
apply checkPath_cat in H. done.
done.
Qed.

Lemma makeQ_split5 : forall p l x c v y, checkPath p l ->  makeQ p l = x ++ (c, v) :: y ->
                                    exists x' v' y', p = x' ++ (v'::y') /\ x = makeQ x' l /\ y = makeQ y' (makeL (x'++[::v']) l) /\ obs v' (makeL x' l) = Some (c,v). 
Proof.
intros. apply makeQ_split3 in H0 as HH. ssa.
exists x0,x1,x2. ssa.
subst. rewrite makeQ_cat2 in H0.
move : H4 => Hobs.
have : take (size (makeQ x0 l)) (makeQ x0 l ++ makeQ (x1 :: x2) (makeL x0 l)) = take (size x) (x ++ (c,v):: y).
rewrite H0. rewrite makeQ_size. rewrite H2 //.
by apply checkPath_cat in H.
rewrite !take_size_cat //.
by apply checkPath_cat in H.
move : H4 => Hobs.
subst.
rewrite makeQ_cat2 in H0.
have : drop (size (makeQ x0 l)) (makeQ x0 l ++ makeQ (x1 :: x2) (makeL x0 l)) = drop (size x) (x ++ (c,v):: y).
rewrite H0. rewrite makeQ_size. rewrite H2 //.
by apply checkPath_cat in H.
rewrite !drop_size_cat //.
have : x1::x2 = [::x1]++x2. done. move=>->.
rewrite makeQ_cat2.
apply checkPath_cat2 in H as HH0.
have : x1::x2 = [::x1]++x2. done. intro. rewrite x3 in HH0.
apply checkPath_cat in H as HH1.
have :  makeQ [:: x1] (makeL x0 l)  = (c,v)::nil.
ssa. rewrite /obs in H1 *. destruct (fe (makeL x0 l)) eqn:Heqn;ssa. de d. de x1. rewrite Heqn.
rewrite Heqn in H0 H4. rewrite /obs in H0. rewrite Heqn in H0. ssa.
have : drop (size (makeQ x0 l)) ( makeQ x0 l ++ (c0, inl v0) :: makeQ x2 l0) = drop (size x) ( x ++ (c, v) :: y).
rewrite H0.
rewrite !drop_size_cat //. rewrite makeQ_size //.
rewrite !drop_size_cat;ssa. inv x1.
de d. de x1. destruct (fe _) eqn:Heqn2;ssa. destruct (lookup _ _) eqn:Heqn3;ssa.
rewrite /obs in H0. rewrite Heqn2 in H0. de d.

have : drop (size (makeQ x0 l)) ( makeQ x0 l ++ (c1, inr n) :: makeQ x2 s) = drop (size x) ( x ++ (c, v) :: y).
rewrite H0.
rewrite !drop_size_cat //. rewrite makeQ_size //.
rewrite !drop_size_cat;ssa. inv x1. inv Heqn. move=>->.
simpl. case. move=><-. ssa.
rewrite makeL_cat. ssa.
apply checkPath_cat2 in H.
have : x1::x2 = [::x1]++x2. done. intro. rewrite x3 in H.
apply checkPath_cat in H. done.
apply checkPath_cat in H. done. subst.
rewrite makeQ_cat2 in H0.
have :  drop (size (makeQ x0 l)) (makeQ x0 l ++ makeQ (x1 :: x2) (makeL x0 l)) = drop (size x) (x ++ (c, v) :: y).
rewrite H0 //.  rewrite !drop_size_cat. done. done.
rewrite makeQ_size. rewrite H2//. apply checkPath_cat in H. done.
rewrite !drop_size_cat. 2:done. 2:done.
have : x1::x2 = [::x1]++x2. done.
move=>->. rewrite makeQ_cat2.
intros.
have : (c,v)::y = ((c,v)::nil)++y. done. move=>HH. rewrite HH in x3.
have : take (size (makeQ [:: x1] (makeL x0 l)))  (makeQ [:: x1] (makeL x0 l) ++ makeQ x2 (makeL [:: x1] (makeL x0 l)) )=
       take (size ([:: (c, v)] )) ([:: (c, v)] ++ y).
rewrite x3. rewrite !take_size_cat //. rewrite makeQ_size. done.
apply checkPath_cat2 in H. 
have : x1 :: x2 = [::x1] ++ x2. done. 
intro. rewrite x4 in H. apply checkPath_cat in H. done.
rewrite !take_size_cat. ssa. de x1.
rewrite /obs in x4 *. destruct (fe _) eqn:Heqn;ssa. de d. de d. 
destruct (lookup _ _) eqn:Heqn2;ssa. inv x4. 
rewrite /obs in x4 *. destruct (fe _) eqn:Heqn2;ssa. de d. inv x4. de d. done.
apply checkPath_cat2 in H. 
have : x1 :: x2 = [::x1] ++ x2. done. 
intro. rewrite x4 in H. apply checkPath_cat in H. done.
apply checkPath_cat2 in H. 
have : x1 :: x2 = [::x1] ++ x2. done. 
intro. rewrite x3 in H. apply checkPath_cat in H. done.
apply checkPath_cat in H. done. done.
Qed.


(*I think this is for showing p <> p'*)
Lemma makeQ_ETr3 : forall l s0 s1 e k u u', checkPath l e -> makeQ l e = s0++(k,u')::s1 -> canEstep2 (makeL l e) (Rd,k,u) ->  exists s, ETr (s++[::(Rd,k,u)]) e /\ all (fun x => (x.1.1 == Sd)) s /\ (Sd,k,u') \in s .
Proof.
elim;ssa.
de s0. de a. rewrite /obs in H3 H1. destruct (fe _) eqn:Heqn;ssa.
destruct (lookup _ _) eqn:Heqn2;ssa. de d. de s0.
inv H1. 


apply  makeQ_ETr2_aux in H2. ssa.
exists ((Sd,k,inr n)::x). ssa. econ. eauto. apply in_pair in Heqn2. eauto. done. done.
inv H1. eapply H in H6;ssa. 2:eauto.
exists ((Sd,c,inr n)::x). ssa. econ. eauto. apply in_pair in Heqn2. eauto. done. 


rewrite /obs in H3 H1. 
destruct (fe _) eqn:Heqn;ssa.
de d. de s0. inv H1.

apply  makeQ_ETr2_aux in H2;ssa.
exists ((Sd,k,inl v)::x). ssa. econ. eauto. eauto. 
inv H1. eapply H in H6;ssa. 2:eauto.
exists ((Sd,c,inl v)::x). ssa. econ. eauto. eauto. 
Qed.

Ltac neqt := match goal with |  [ H : is_true (?a != ?a) |- _ ] => by rewrite eqxx in H end.


Lemma Trp2_to_Tr' : forall p s g l, Trp2 p s g l -> size_pred g ->  exists ss x, Tr (ss++[::x]) g /\ comp_dir p x = Some l.1.1 /\ action_ch x = l.1.2 /\ all (fun y => comp_dir p y != Some Rd) ss.
Proof.
move=> p s g l. elim;ssa;subst.
- exists nil. exists a. ssa. apply/Tr_full_unf2. rewrite H. eauto.
- exists nil. exists a. ssa. apply/Tr_full_unf2. rewrite H. de (mapP H2). de x.
  econ. eauto. done.
- apply size_pred_full_unf in H5. rewrite H in H5. ssa. 
  de (H4 H5). subst_comp. exists (a::x). exists x0. ssa. apply/Tr_full_unf2. rewrite H. econ. eauto.
  rewrite /comp_dir eqxx //=.
- apply size_pred_full_unf in H3. rewrite H in H3. ssa. 
  de (H2 H3). exists (a::x). exists x0. ssa. apply/Tr_full_unf2. rewrite H. econ. eauto. rewrite H0 //=.
-  apply size_pred_full_unf in H6. rewrite H in H6. ssa.
   apply (allP H7) in H3 as HH. de (H5 HH).
   exists (a::x). exists x0. ssa. apply/Tr_full_unf2. rewrite H. econ. eauto. eauto. rewrite H1 //=.
- apply size_pred_full_unf in H3. rewrite H in H3. ssa.
  de gs. de p0. eapply H2 in H3;ssa.
  exists (a::x). exists x0. ssa. apply/Tr_full_unf2. rewrite H. econ. eauto. eauto. rewrite H0 //.
Qed.

Lemma Tr2_unf: forall s g, Tr2 s g -> Tr2 s (unf g).  
Proof.
intros. de g;ssa.
inv H.
Qed.

Lemma Tr2_full_unf : forall s g, Tr2 s g -> Tr2 s (full_unf g).
Proof.
intros. rewrite /full_unf. move : (mu_height _) => n.
elim : n g H. ssa.
ssa.  apply/Tr2_unf. eauto.
Qed. 

Lemma Tr2_unf2 : forall s g, Tr2 s (unf g) -> Tr2 s g. 
Proof. 
intros. destruct g;try done. ssa. 
Qed.

Lemma Tr2_full_unf2 : forall s g, Tr2 s (full_unf g) -> Tr2 s g. 
Proof. 
intros. rewrite /full_unf in H. remember (mu_height g). clear Heqn. elim : n g s H. done. 
intros. ssa. apply/Tr2_unf2. apply/H.  rewrite -iterSr iterS. done. 
Qed.




Lemma Trp2_to_Tr2' : forall p s g l, Trp2 p s g l -> size_pred g ->  exists ss x, Tr2 (ss++[::x]) g /\ comp_dir p x.1 = Some l.1.1 /\ action_ch x.1 = l.1.2 /\ all (fun y => comp_dir p y.1 != Some Rd) ss /\ x.2 = l.2.
Proof.
move=> p s g l. elim;ssa;subst.
- exists nil. exists (a,inl u). ssa. apply/Tr2_full_unf2. rewrite H. eauto.
- exists nil. exists (a,inr n). ssa. apply/Tr2_full_unf2. rewrite H. de (mapP H2). de x. subst.
  econ. eauto. done.
- apply size_pred_full_unf in H5. rewrite H in H5. ssa. 
  de (H4 H5). subst_comp. exists ((a,inl u)::x). exists x0. ssa. apply/Tr2_full_unf2. rewrite H. econ. eauto.
  rewrite /comp_dir eqxx //=.
- apply size_pred_full_unf in H3. rewrite H in H3. ssa. 
  de (H2 H3). exists ((a,inl u')::x). exists x0. ssa. apply/Tr2_full_unf2. rewrite H. econ. eauto. rewrite H0 //=.
-  apply size_pred_full_unf in H6. rewrite H in H6. ssa.
   apply (allP H7) in H3 as HH. de (H5 HH).
   exists ((a,inr n)::x). exists x0. ssa. apply/Tr2_full_unf2. rewrite H. econ. eauto. eauto. rewrite H1 //=.
- apply size_pred_full_unf in H3. rewrite H in H3. ssa.
  de gs. de p0. eapply H2 in H3;ssa.
  exists ((a,inr n)::x). exists x0. ssa. apply/Tr2_full_unf2. rewrite H. econ. eauto. eauto. rewrite H0 //.
Qed.



(*We must start by showing p and p' will occur along the same path before we by linearity can conclude they are in the same interaction*)

Lemma Linear_full_unf : forall g, Linear g -> Linear (full_unf g).
Proof.
intros. intro. intros. apply Tr_full_unf2 in H0. eauto.
Qed.

Lemma ch_diff2 : forall g a0 aa a1, Linear g -> Tr (a0::(aa++[::a1])) g -> Forall ( fun a' => (ptcp_to a') != ptcp_to a1) (a0::aa) -> 
                                action_ch a0 != action_ch a1. 
Proof.  
move => g a0 aa a1 Hlin Htr /List.Forall_cons_iff [] Ha0 Hfor.
move : Htr. have : a0 :: aa ++ [:: a1] = nil ++  a0 :: aa ++ [:: a1] by []. move=>-> Htr.
apply/eqP=>Hch. have : same_ch a0 a1. rewrite /same_ch Hch eqxx //. move => Hsame. clear Hch.
move/Linear_1 : (Hlin). move/(_ _ _ _ _ Htr Hsame)/to_InDep2=>Hout.
clear Htr Hlin Hsame. 
move : Hout Hfor Ha0.  elim.
- ssa. rewrite /II in H. norm_eqs. rewrite H in Ha0. neqt.
- ssa. inv Hfor. eauto.
- ssa. inv Hfor.  rewrite /IO in H. norm_eqs. rewrite H in Ha0.
  auto.
Qed.

Lemma comp_not : forall a, ptcp_from a != ptcp_to a -> comp_dir (ptcp_to a) a = Some Rd.
Proof.
intros. rewrite /comp_dir. case_if. case_if. norm_eqs. rewrite H0 in H. neqt. done.
Qed.

Lemma Tr_unf: forall s g, Tr s g -> Tr s (unf g).  
Proof.
intros. de g;ssa.
inv H.
Qed.

Lemma Tr_full_unf : forall s g, Tr s g -> Tr s (full_unf g).
Proof.
intros. rewrite /full_unf. move : (mu_height _) => n.
elim : n g H. ssa.
ssa.  apply/Tr_unf. eauto.
Qed.



Lemma to_Tr2 : forall p s l g, Trp2 p s g l -> size_pred g -> Linear g -> action_pred g -> forall  p' s' c u u', l = (Sd,c,u) ->  Trp2 p' s'  g  (Rd,c,u') -> p != p' ->  
                                          exists ss, Tr2 (ss++[:: (Action p p' c,u)]) g /\ all (fun y  => ptcp_to y.1 \notin Action p p' c) ss.
Proof.
move=> p s l g. elim.
- move=>g0 a u g1 l0 d Hunf Hcomp Hl0 Hsize Hlin Hact p' s' c u0 u' Hl0'. subst. inv Hl0';subst_comp. clear Hl0'.
  move/Trp2_full_unf2. rewrite Hunf.
  move=> HE Hnot.
  suff:  exists ss , Tr2 (ss ++ [:: (Action (ptcp_from a) p' (action_ch a),inl u)]) (full_unf g0) /\  all
      (fun y : action * (value + fin) =>
       ptcp_to y.1 \notin Action (ptcp_from a) p' (action_ch a)) ss.
  case. ssa. exists x. ssa. apply/Tr2_full_unf2. done.
  apply size_pred_full_unf in Hsize.
  apply Linear_full_unf in Hlin. 
  apply action_pred_full_unf in Hact. 
  rewrite Hunf in Hsize Hlin Hact *. clear Hunf. ssa.
  apply Trp2_to_Tr' in HE;ssa. subst_comp. inv H1. de x.
  de x. inv H2. exists nil. ssa. rewrite pack_act //=. eauto.
  inv H2. 
  apply ch_diff2 in H1;eauto. rewrite H3 in H1. neqt.
  con. apply/eqP. intro. rewrite -H4 in H5. rewrite comp_not in H5;ssa.
  apply/ForallP. intro. move/inP. move/[dup]=>Hin. move/(allP H7).
  move=>HH.
  apply/eqP. intro. rewrite -H4 in HH. rewrite comp_not //in HH.
  apply/Tr_action_pred. apply H1. ssa. rewrite inE mem_cat. erewrite Hin. rewrite orbC //=.

- move=> g0 a gs l0 n d Hunf Hcomp Hl0 Hdom /size_pred_full_unf + /Linear_full_unf + /action_pred_full_unf.
  rewrite Hunf /=. case/andP=> Hg0 Hall Hlin /andP [] Hneq Hall2 p' s' c u u' Hl0' HE Hneq'.
  suff:  exists ss , Tr2 (ss ++ [:: (Action p p' c,u)]) (full_unf g0) /\ all (fun y : action * (value + fin) => ptcp_to y.1 \notin Action p p' c) ss.
  ssa. exists x. ssa. apply/Tr2_full_unf2. eauto.
  rewrite Hunf. subst. inv Hl0'. subst_comp. clear Hl0'.
  
  apply Trp2_to_Tr' in HE;ssa. subst_comp.  apply Tr_full_unf in H. rewrite Hunf in H.
  inv H. de x. de x. inv H0. exists nil. ssa. rewrite pack_act. de (mapP Hdom). de x. subst.
  econ. eauto. done.
  inv H0.
  apply ch_diff2 in H;eauto. rewrite H1 in H. neqt.
  con. apply/eqP. intro. rewrite -H2 in H3. rewrite comp_not in H3;ssa.
  apply/ForallP. intro. move/inP. move/[dup]=>Hin. move/(allP H4). 
  move=>HH.
  apply/eqP. intro. rewrite -H2 in HH. rewrite comp_not //in HH.
  apply/Tr_action_pred. apply H. ssa. rewrite inE mem_cat. erewrite Hin. rewrite orbC //=.
  apply/size_pred_full_unf2. rewrite Hunf //=. ssa.

- move=> g0 a u g1 l0 s0 x Hunf Hcomp Hx Hact Htr IH /size_pred_full_unf + /Linear_full_unf + /action_pred_full_unf.
  rewrite Hunf /=. move => Hsize /linear_sgmsg Hlin /andP [] Hneq Hact2 p' s' c u0 u' Hl0 HE Hneq'.
  suff:  exists ss , Tr2 (ss ++ [:: (Action p p' c,u0)]) (full_unf g0)  /\
    all (fun y : action * (value + fin) => ptcp_to y.1 \notin Action p p' c) ss. ssa. exists x0. ssa.
  apply/Tr2_full_unf2. done. rewrite Hunf.
  subst. subst_comp.
  ssa.

  apply Trp2_full_unf2 in HE. rewrite Hunf in HE.
  inv HE.
 * inv H. inv H1. subst_comp. neqt.
 * inv H. subst_comp. ssa. neqt.
 * inv H. eapply IH in H1;eauto. ssa.
   exists ((a0,inl u'0)::x). ssa.

   rewrite inE !negb_or. ssa. rewrite neg_sym. done.  move : H0. rewrite /comp_dir. case_if;ssa.
   move : H3. case_if;ssa. rewrite neg_sym H3 //.

- move=> g0 a u' g1 l0 s0 Hunf Hcomp HE IH.
  move=> /size_pred_full_unf + + /action_pred_full_unf.
  rewrite Hunf /=. move=> Hsize Hlin /andP [] Hneq Hact.
  move=> p' s' c u u'0 Hl0 HT Hneq'. subst.
  apply Trp2_full_unf2 in HT. rewrite Hunf in HT.
  inv HT.
 * inv H. inv H1. subst_comp. 
   have: Trp2 p (s0) g0 (Sd,action_ch a0,u). eauto. move=>HH.
   apply Trp2_to_Tr2' in HH;ssa. subst_comp.
   apply Tr2_full_unf in H0. rewrite Hunf in H0.
   inv H0. de x. de x. inv H2.
   exists nil. ssa. apply: Tr2_full_unf2. rewrite Hunf. rewrite pack_act. econ. done.
   inv H2. 
   apply Tr21 in H0. simpl in H0. rewrite /dom /= map_cat in H0.
   apply ch_diff in H0.  rewrite H3 in H0. neqt.  apply Linear_full_unf in Hlin. rewrite Hunf in Hlin. done.
   con;ssa. rewrite neg_sym //.
   apply/ForallP. intro. move/inP. move/mapP.  case.  move=> x2. move/[dup]=>Hin. 
   move/(allP H7). move=>HH. move=> Hx1. subst.
   apply/eqP. intro. rewrite -H4 in HH.
   rewrite comp_not in HH;ssa.
   apply/Tr_action_pred. eauto. ssa. rewrite inE. apply/orP. right. rewrite mem_cat. apply/orP. left. apply/map_f. done.
   apply/eqP. intro. rewrite -H4 in Hcomp.
   move : Hcomp. rewrite /comp_dir eqxx //=. apply/size_pred_full_unf2. rewrite Hunf. ssa.
 * ssa. subst_comp. inv H.
   eapply IH in H3;eauto. ssa. exists ((a0,inl u0)::x). ssa. apply:Tr2_full_unf2. rewrite Hunf. econ. done.

   rewrite !inE !negb_or /=. ssa. rewrite neg_sym. 
   move : Hcomp. rewrite /comp_dir. case_if;ssa. move : Hcomp. case_if;ssa.
   rewrite neg_sym //.
   apply Linear_full_unf in Hlin. rewrite Hunf in Hlin. by apply linear_sgmsg in Hlin.
 * inv H.  eapply IH in H1;eauto. ssa. 
   exists ((a0,inl u'1)::x). ssa. apply/Tr2_full_unf2. rewrite Hunf. econ. done.

   rewrite inE !negb_or. ssa.  move : Hcomp. rewrite /comp_dir. case_if;ssa.
   move : Hcomp. case_if;ssa. rewrite neg_sym H4 //.
   move : H0. rewrite /comp_dir. case_if;ssa.
   move : H3. case_if;ssa. rewrite neg_sym H3 //. 

   apply Linear_full_unf in Hlin. rewrite Hunf in Hlin. apply linear_sgmsg in Hlin. done.

- move=> /= n a g0 g1 gs l0 s0 x Hunf Hc Hcomp Hx Hin HE IH.
  move=> /size_pred_full_unf + + /action_pred_full_unf. rewrite Hunf.
  move=>/= /andP [] H00 Hall Hlin /andP [] Hneq Hall2.
  move=> p' s' c u u' Hl0 HE' Hneq'. subst. subst_comp.
  
  apply Trp2_full_unf2 in HE'. rewrite Hunf in HE'.
  inv HE'. 
 * inv H. inv H1. subst_comp. ssa. neqt.
 * subst_comp. inv H. neqt.
   inv H. apply H1 in Hin as HH. eapply IH in HH;eauto. ssa.
   exists ((a0,inr n)::x). ssa. apply:Tr2_full_unf2. rewrite Hunf. econ. 2:eauto. eauto.

   rewrite !inE !negb_or /=. ssa. rewrite neg_sym. done.
   move : H0. rewrite /comp_dir. case_if;ssa. move : H4. case_if;ssa. 
   rewrite neg_sym H4 //.

   apply (allP Hall) in Hin. ssa.
   apply Linear_full_unf in Hlin. rewrite Hunf in Hlin.
   eapply linear_branch in Hlin. 2:eauto. ssa.
   apply (allP Hall2) in Hin. ssa.

- move=> /= a g0 gs s0 l0 Hunf Hcomp HT IH.
  move=> /size_pred_full_unf + Hlin /action_pred_full_unf. rewrite Hunf /=.
  move=>/andP [] H00 Hall /andP [] Hneq Hall'.
  move=> p' s' c u u' Hl0 HE Hneq'. subst.

  apply Trp2_full_unf2 in HE. rewrite Hunf in HE.
  inv HE.
 * inv H1. subst_comp. inv H.
   de (mapP H2). de x. subst. apply HT in H0.
   have : Trp2 p s0 g0 (Sd,action_ch a0,u). eauto.
   move=>HE2. 
   apply Trp2_to_Tr' in HE2;ssa. subst_comp.
   apply Tr_full_unf in H3. rewrite Hunf in H3.
   inv H3. de x. de x. inv H4. inv Hunf.
   move : Hcomp. rewrite /comp_dir eqxx //=. 
   inv H4. 
   apply ch_diff in H3;ssa. rewrite H5 in H3. neqt.
   apply Linear_full_unf in Hlin. rewrite Hunf in Hlin. done.
   con. apply/eqP. intro. rewrite -H6 in H7.
   rewrite comp_not in H7;ssa.
   apply/ForallP. move=> x'. move/inP. 
   move/[dup]=>Hin'.
   move/(allP H8). move=>HH. apply/eqP. intro. rewrite -H6 in HH.
   move : HH. rewrite comp_not //. apply/Tr_action_pred. eauto. 
   apply (allP Hall') in H9. ssa. rewrite mem_cat Hin' //=.
   apply/eqP. intro. rewrite -H6 in Hcomp.
   move : Hcomp. rewrite /comp_dir eqxx //=.
   apply size_pred_full_unf2. rewrite Hunf. ssa.
   
   subst_comp. inv H.
   eapply IH in H3 as HIH ;eauto. ssa. exists ((a0,inr n)::x). ssa. 
   apply:Tr2_full_unf2. rewrite Hunf. econ. eauto. done.


   rewrite !inE /= negb_or. ssa. 
   move : Hcomp. rewrite /comp_dir. case_if;ssa. move: Hcomp. case_if;ssa.
   rewrite neg_sym H6 //. rewrite neg_sym//.

   apply (allP Hall) in H3. done.
   apply Linear_full_unf in Hlin. rewrite Hunf in Hlin.
   eapply linear_branch in Hlin. 2:eauto. done.
   apply (allP Hall') in H3. done. inv H.
   have : nth (0,GEnd) gs0 0 \in gs0.  apply/mem_nth. done.
   intro. destruct (nth _ _ _) eqn:Heqn;ssa.
   apply H1 in x. eapply IH in x;eauto.
   ssa. exists ((a0,inr n)::x). ssa. apply:Tr2_full_unf2. rewrite Hunf. econ. apply/nthP. econ. 2:eauto. 
   done. done. 


   rewrite !inE negb_or. ssa. move : Hcomp. rewrite /comp_dir. case_if;ssa. move : Hcomp. case_if;ssa.
   rewrite neg_sym H5 //.
   move : H0. rewrite /comp_dir. case_if;ssa. move : H4. case_if;ssa. rewrite neg_sym H4 //.
   
   apply/nthP. econ. 2:eauto. done.
   have : (n,g1) \in gs0. rewrite -Heqn. apply/mem_nth. done.
   move=>HH.
   apply (allP Hall) in HH. ssa.
   apply Linear_full_unf in Hlin. rewrite Hunf in Hlin.
   eapply linear_branch in Hlin. move : Hlin. instantiate (1:= (n,g1)). ssa.
   apply/nthP. econ. 2:eauto. done.

   have : (n,g1) \in gs0. rewrite -Heqn. apply/mem_nth. done.
   move=>HH.
   apply (allP Hall') in HH. ssa.
Qed.



Lemma to_Tr2' : forall p s l g, Trp2 p s g l -> size_pred g -> Linear g -> action_pred g -> forall  p' s' c u u', l = (Sd,c,u) ->  Trp2 p' s'  g  (Rd,c,u') -> p != p' ->  
                                          exists ss, Tr2 (ss++[:: (Action p p' c,u')]) g /\ all (fun y  => ptcp_to y.1 \notin Action p p' c) ss.
Proof.
move=> p s l g. elim.
- move=>g0 a u g1 l0 d Hunf Hcomp Hl0 Hsize Hlin Hact p' s' c u0 u' Hl0'. subst. inv Hl0';subst_comp. clear Hl0'.
  move/Trp2_full_unf2. rewrite Hunf.
  move=> HE Hnot.
  suff:  exists ss , Tr2 (ss ++ [:: (Action (ptcp_from a) p' (action_ch a),u')]) (full_unf g0) /\  all
      (fun y : action * (value + fin) =>
       ptcp_to y.1 \notin Action (ptcp_from a) p' (action_ch a)) ss.
  case. ssa. exists x. ssa. apply/Tr2_full_unf2. done.
  apply size_pred_full_unf in Hsize.
  apply Linear_full_unf in Hlin. 
  apply action_pred_full_unf in Hact. 
  rewrite Hunf in Hsize Hlin Hact *. clear Hunf. ssa.
  apply Trp2_to_Tr2' in HE;ssa. subst_comp. inv H1. de x.
  de x. inv H2. exists nil. ssa. rewrite pack_act //=. 
  inv H2. apply Tr21 in H1. rewrite /= dom_cat in H1. 
  apply ch_diff2 in H1;eauto. rewrite H3 in H1. neqt.
  con. apply/eqP. intro. rewrite -H4 in H5. rewrite comp_not in H5;ssa.
  apply/ForallP. intro. move/inP. move/[dup]=>Hin. 
  move/mapP. case. move=> x2. move/[dup]. move=>Hin2.
  move/(allP H7).
  move=>HH. intros. subst.
  apply/eqP. intro. rewrite -H4 in HH. rewrite comp_not //in HH.
  apply/Tr_action_pred. apply H1. ssa. rewrite inE mem_cat. erewrite Hin. rewrite orbC //=.

- move=> g0 a gs l0 n d Hunf Hcomp Hl0 Hdom /size_pred_full_unf + /Linear_full_unf + /action_pred_full_unf.
  rewrite Hunf /=. case/andP=> Hg0 Hall Hlin /andP [] Hneq Hall2 p' s' c u u' Hl0' HE Hneq'.
  suff:  exists ss , Tr2 (ss ++ [:: (Action p p' c,u')]) (full_unf g0) /\
    all (fun y : action * (value + fin) => ptcp_to y.1 \notin Action p p' c) ss.
  ssa. exists x. ssa. apply/Tr2_full_unf2. eauto.
  rewrite Hunf. subst. inv Hl0'. subst_comp. clear Hl0'.
  
  apply Trp2_to_Tr2' in HE;ssa. subst_comp.  apply Tr2_full_unf in H. rewrite Hunf in H.
  inv H. de x. de x. inv H0. exists nil. ssa. rewrite pack_act. de (mapP Hdom). 
  inv H0. apply Tr21 in H. rewrite /= dom_cat in H.
  apply ch_diff2 in H;eauto. rewrite H1 in H. neqt.
  con. apply/eqP. intro. rewrite -H2 in H3. rewrite comp_not in H3;ssa.
  apply/ForallP. intro. move/inP. move/[dup]=>Hin. 

  move/mapP. case. move=> x2. move/[dup]. move=>Hin2.
  move/(allP H4). 
  move=>HH. intro. subst.
  apply/eqP. intro. rewrite -H2 in HH. rewrite comp_not //in HH.
  apply/Tr_action_pred. apply H. ssa. rewrite inE mem_cat. erewrite Hin. rewrite orbC //=.
  apply/size_pred_full_unf2. rewrite Hunf //=. ssa.

- move=> g0 a u g1 l0 s0 x Hunf Hcomp Hx Hact Htr IH /size_pred_full_unf + /Linear_full_unf + /action_pred_full_unf.
  rewrite Hunf /=. move => Hsize /linear_sgmsg Hlin /andP [] Hneq Hact2 p' s' c u0 u' Hl0 HE Hneq'.
  suff:  exists ss , Tr2 (ss ++ [:: (Action p p' c,u')]) (full_unf g0) /\ 
    all (fun y : action * (value + fin) => ptcp_to y.1 \notin Action p p' c) ss.
  ssa. exists x0. ssa.
  apply/Tr2_full_unf2. done. rewrite Hunf.
  subst. subst_comp.
  ssa.

  apply Trp2_full_unf2 in HE. rewrite Hunf in HE.
  inv HE.
 * inv H. inv H1. subst_comp. neqt.
 * inv H. subst_comp. ssa. neqt.
 * inv H. eapply IH in H1;eauto. ssa.
   exists ((a0,inl u'0)::x). ssa.

   rewrite inE !negb_or. ssa. rewrite neg_sym. done.  move : H0. rewrite /comp_dir. case_if;ssa.
   move : H3. case_if;ssa. rewrite neg_sym H3 //.
   

- move=> g0 a u' g1 l0 s0 Hunf Hcomp HE IH.
  move=> /size_pred_full_unf + + /action_pred_full_unf.
  rewrite Hunf /=. move=> Hsize Hlin /andP [] Hneq Hact.
  move=> p' s' c u u'0 Hl0 HT Hneq'. subst.
  apply Trp2_full_unf2 in HT. rewrite Hunf in HT.
  inv HT.
 * inv H. inv H1. subst_comp. 
   have: Trp2 p (s0) g0 (Sd,action_ch a0,u). eauto. move=>HH.
   apply Trp2_to_Tr2' in HH;ssa. subst_comp.
   apply Tr2_full_unf in H0. rewrite Hunf in H0.
   inv H0. de x. de x. inv H2.
   exists nil. ssa. apply: Tr2_full_unf2. rewrite Hunf. rewrite pack_act. econ. done.
   inv H2. 
   apply Tr21 in H0. simpl in H0. rewrite /dom /= map_cat in H0.
   apply ch_diff in H0.  rewrite H3 in H0. neqt.  apply Linear_full_unf in Hlin. rewrite Hunf in Hlin. done.
   con;ssa. rewrite neg_sym //.
   apply/ForallP. intro. move/inP. move/mapP.  case.  move=> x2. move/[dup]=>Hin. 
   move/(allP H7). move=>HH. move=> Hx1. subst.
   apply/eqP. intro. rewrite -H4 in HH.
   rewrite comp_not in HH;ssa.
   apply/Tr_action_pred. eauto. ssa. rewrite inE. apply/orP. right. rewrite mem_cat. apply/orP. left. apply/map_f. done.
   apply/eqP. intro. rewrite -H4 in Hcomp.
   move : Hcomp. rewrite /comp_dir eqxx //=. apply/size_pred_full_unf2. rewrite Hunf. ssa.
 * ssa. subst_comp. inv H.
   eapply IH in H3;eauto. ssa. exists ((a0,inl u0)::x). ssa. apply:Tr2_full_unf2. rewrite Hunf. econ. done.

   rewrite !inE !negb_or /=. ssa. rewrite neg_sym. 
   move : Hcomp. rewrite /comp_dir. case_if;ssa. move : Hcomp. case_if;ssa.
   rewrite neg_sym //.

   apply Linear_full_unf in Hlin. rewrite Hunf in Hlin. by apply linear_sgmsg in Hlin.
 * inv H.  eapply IH in H1;eauto. ssa. 
   exists ((a0,inl u'1)::x). ssa. apply/Tr2_full_unf2. rewrite Hunf. econ. done.

   rewrite inE !negb_or. ssa.  move : Hcomp. rewrite /comp_dir. case_if;ssa.
   move : Hcomp. case_if;ssa. rewrite neg_sym H4 //.
   move : H0. rewrite /comp_dir. case_if;ssa.
   move : H3. case_if;ssa. rewrite neg_sym H3 //. 

   apply Linear_full_unf in Hlin. rewrite Hunf in Hlin. apply linear_sgmsg in Hlin. done.

- move=> /= n a g0 g1 gs l0 s0 x Hunf Hc Hcomp Hx Hin HE IH.
  move=> /size_pred_full_unf + + /action_pred_full_unf. rewrite Hunf.
  move=>/= /andP [] H00 Hall Hlin /andP [] Hneq Hall2.
  move=> p' s' c u u' Hl0 HE' Hneq'. subst. subst_comp.
  
  apply Trp2_full_unf2 in HE'. rewrite Hunf in HE'.
  inv HE'. 
 * inv H. inv H1. subst_comp. ssa. neqt.
 * subst_comp. inv H. neqt.
   inv H. apply H1 in Hin as HH. eapply IH in HH;eauto. ssa.
   exists ((a0,inr n)::x). ssa. apply:Tr2_full_unf2. rewrite Hunf. econ. 2:eauto. eauto.

   rewrite !inE !negb_or /=. ssa. rewrite neg_sym. done.
   move : H0. rewrite /comp_dir. case_if;ssa. move : H4. case_if;ssa. 
   rewrite neg_sym H4 //.

   apply (allP Hall) in Hin. ssa.
   apply Linear_full_unf in Hlin. rewrite Hunf in Hlin.
   eapply linear_branch in Hlin. 2:eauto. ssa.
   apply (allP Hall2) in Hin. ssa.

- move=> /= a g0 gs s0 l0 Hunf Hcomp HT IH.
  move=> /size_pred_full_unf + Hlin /action_pred_full_unf. rewrite Hunf /=.
  move=>/andP [] H00 Hall /andP [] Hneq Hall'.
  move=> p' s' c u u' Hl0 HE Hneq'. subst.

  apply Trp2_full_unf2 in HE. rewrite Hunf in HE.
  inv HE.
 * inv H1. subst_comp. inv H.
   de (mapP H2). de x. subst. apply HT in H0.
   have : Trp2 p s0 g0 (Sd,action_ch a0,u). eauto.
   move=>HE2. 
   apply Trp2_to_Tr' in HE2;ssa. subst_comp.
   apply Tr_full_unf in H3. rewrite Hunf in H3.
   inv H3. de x. de x. inv H4. inv Hunf.
   move : Hcomp. rewrite /comp_dir eqxx //=. 
   inv H4. 
   apply ch_diff in H3;ssa. rewrite H5 in H3. neqt.
   apply Linear_full_unf in Hlin. rewrite Hunf in Hlin. done.
   con. apply/eqP. intro. rewrite -H6 in H7.
   rewrite comp_not in H7;ssa.
   apply/ForallP. move=> x'. move/inP. 
   move/[dup]=>Hin'.
   move/(allP H8). move=>HH. apply/eqP. intro. rewrite -H6 in HH.
   move : HH. rewrite comp_not //. apply/Tr_action_pred. eauto. 
   apply (allP Hall') in H9. ssa. rewrite mem_cat Hin' //=.
   apply/eqP. intro. rewrite -H6 in Hcomp.
   move : Hcomp. rewrite /comp_dir eqxx //=.
   apply size_pred_full_unf2. rewrite Hunf. ssa.
   
   subst_comp. inv H.
   eapply IH in H3 as HIH ;eauto. ssa. exists ((a0,inr n)::x). ssa. 
   apply:Tr2_full_unf2. rewrite Hunf. econ. eauto. done.

   rewrite !inE /= negb_or. ssa. 
   move : Hcomp. rewrite /comp_dir. case_if;ssa. move: Hcomp. case_if;ssa.
   rewrite neg_sym H6 //. rewrite neg_sym//.


   apply (allP Hall) in H3. done.
   apply Linear_full_unf in Hlin. rewrite Hunf in Hlin.
   eapply linear_branch in Hlin. 2:eauto. done.
   apply (allP Hall') in H3. done. inv H.
   have : nth (0,GEnd) gs0 0 \in gs0.  apply/mem_nth. done.
   intro. destruct (nth _ _ _) eqn:Heqn;ssa.
   apply H1 in x. eapply IH in x;eauto.
   ssa. exists ((a0,inr n)::x). ssa. apply:Tr2_full_unf2. rewrite Hunf. econ. apply/nthP. econ. 2:eauto. 
   done. done. 

   rewrite !inE negb_or. ssa. move : Hcomp. rewrite /comp_dir. case_if;ssa. move : Hcomp. case_if;ssa.
   rewrite neg_sym H5 //.
   move : H0. rewrite /comp_dir. case_if;ssa. move : H4. case_if;ssa. rewrite neg_sym H4 //.
   
   apply/nthP. econ. 2:eauto. done.
   have : (n,g1) \in gs0. rewrite -Heqn. apply/mem_nth. done.
   move=>HH.
   apply (allP Hall) in HH. ssa.
   apply Linear_full_unf in Hlin. rewrite Hunf in Hlin.
   eapply linear_branch in Hlin. move : Hlin. instantiate (1:= (n,g1)). ssa.
   apply/nthP. econ. 2:eauto. done.

   have : (n,g1) \in gs0. rewrite -Heqn. apply/mem_nth. done.
   move=>HH.
   apply (allP Hall') in HH. ssa.
Qed.

Lemma step_uniq : forall g l g', step g l g' -> size_pred g -> forall l' g'' u u', step g l' g'' -> l.1 = l'.1 -> l.2 = inl u -> l'.2 = inl u' -> u = u'.
Proof.
move=> g l g'. elim;ssa;subst.  inv H2.
inv H0.  de l'. inv H1. ssa. inv H5.
rewrite !inE eqxx orbC //= in H9. de l0. de l'. subst.
inv H3. rewrite !inE eqxx orbC //= in H1.
ssa. eauto.
de l0. de l'. subst. 
inv H4. ssa.
de gs. de gs'. de gs'0. ssa.
eapply H1. left. eauto. ssa. apply H7. eauto. ssa. done. done.

de l0. de l'. subst. inv H2. 
eapply H0;eauto. rewrite size_pred_subst;ssa. de x.
Qed.



Lemma step_uniq2 : forall g l g',  step g l g' -> uniqg_labels g ->  forall l' g'', step g l' g'' -> l = l' ->  g' = g''.
Proof.
move=> g l g'. elim;ssa;subst.  inv H0.
rewrite !inE eqxx orbC //= in H7. 
inv H1. 
apply uniq_in_pair in H, H7;ssa. rewrite H in H7. inv H7. ssa.
rewrite !inE eqxx orbC //= in H9.
ssa. 

inv H3. ssa.
rewrite !inE eqxx orbC //= in H1.
f_equal. eauto.
inv H4;ssa.
rewrite !inE eqxx orbC //= in H2.
f_equal.
clear H4 H6.
elim : gs gs' H gs'0 H8 H1 H0 H9 H7.
case. ssa. de gs'0.
move=> a0 l0. ssa.
move=> a0 l0 IH. case. done.
move=> a1 l1. simpl. case. move=> Ha0 Heq. case. done.
move=> a2 l2. case. move=> Ha3 Heq'.
move=> H0 H1 H2'. ssa.
f_equal.  de a0. de a1. de a2. subst.  
f_equal.
have : g1 = (n1,g1).2. done. move=>->.
apply:H0. eauto. done.  
have : g2 = (n1,g2).2. done. move=>->. apply H2'. eauto. done.
apply IH;eauto.
inv H2. eapply H0;eauto.
rewrite uniqg_labels_subst;ssa. case:n;ssa.
Qed.

Ltac split_and_in :=
  intros;
   repeat
    match goal with
    | H:is_true (_ && _) |- _ => destruct (andP H); clear H
    | H:_ && _ = true |- _ => destruct (andP H); clear H
    | H:_ /\ _ |- _ => destruct H
    | H : ex _ |- _ => destruct H
    end; auto.

Ltac ssa_in := rewrite ?inE;simpl in *; split_and_in;try done.

Lemma balanced_can_step : forall E Q s p' p k u u' l0 l  T, partial_balanced E Q -> all (fun x => x.1 != k) l0 ->
lookup Q (QKey s p') = Some (l0++(k,u)::l) -> 
lookup E (schlT s p) = Some T -> canEstep2 T (Rd,k,u')  -> (exists g, (exists g',step g (Action p' p k,u) g') /\ (exists g', step g (Action p' p k,u') g')) /\ (forall x y, u = inl x -> u' = inl y -> x = y). 
Proof.
ssa_in.
move : H3 => HCan.
inv H. ssa_in. inv H4. 
apply lookup_filter_q_2 in H1. ssa_in.
apply lookup_filter2 in H2. ssa_in.
inv H3. ssa_in.
apply H8 in H5.
apply H9 in H4. ssa_in. 
rewrite /check_gs in H7. ssa_in.
eapply H7 in H4 as Hcheck.
move : Hcheck. instantiate (1:= p). move=>Hcheck.
eapply H7 in H5 as Hcheck'. 
move : Hcheck'. instantiate (1:= p'). move=>Hcheck'.
clear H7.
rewrite H4 in H5. inv H5.
clear H5 H6.
suff:   
     (exists g' : gType, step x6 (Action p' p k, u) g') /\
     (exists g' : gType, step x6 (Action p' p k, u') g') /\
  (forall x3 y : value, u = inl x3 -> u' = inl y -> x3 = y).
ssa. eauto.
have : p' <> p.  apply filter_keys_mid in H1. ssa_in. intro. subst.
apply H10 in H4. inv H4. ssa_in. move : (H12 p). ssa_in.
eapply makeQ_ETr3 in HCan;eauto. ssa_in.
eapply test_test in H5;eauto. apply (allP H5) in H18. ssa_in. rewrite eqxx in H18. done.
apply/Project_EQ2. eauto. apply proj_proj. eauto.
move=>Hneq.

eapply filter_keys_mid2 in H1. 
move : H1. instantiate (1:= (fun x => x == k)). move=>H1.

apply H10 in H4. inv H4.

move : H6. case=> Hx0 [] Hx1 [] Hx2 [] Hproj Hgood. 
move: (Hproj p'). move: (Hproj p).
case. move=> x3 HP0.
case. move=> x7 HP1.
eapply Project_EQ2 in HP0 , HP1.
2: { apply/proj_proj. apply HP1. }  
2: { apply/proj_proj. apply HP0. }
destruct H1. destruct H1. destruct H1. move : H6 =>Hall.
apply makeQ_ETr in H1.
eapply makeQ_ETr2 in HCan;eauto. 
destruct H1. destruct H1.  
destruct HCan. destruct H7.
move : H1 H7 => HE0 HE1.
eapply to_Trp in HE0;eauto.
eapply to_Trp in HE1;eauto.
apply to_Trp2 in HE0,HE1.
have: canStep x6 (Action p' p k,u) /\ canStep x6 (Action p' p k,u').
con. 
- eapply to_Tr2 in HE0;eauto. ssa. 
  apply: Tr2_to_canStep;eauto. 
  by apply/eqP.
- eapply to_Tr2' in HE0;eauto. ssa. 
  apply: Tr2_to_canStep;eauto.
  by apply/eqP.

move=>HH2.
ssa_in. 
punfold Hgood. inv Hgood.  
apply H12 in H1,H7. ssa_in. 

ssa. eauto. eauto.
intros. subst. eapply step_uniq. apply H1. 2: apply H7. done. done. done. done.

ssa. apply/allP. intro. move/(allP H11). ssa.
apply/allP. intro. move/(allP H6). ssa.
done. done.
intros. ssa. norm_eqs.
have : (k,u) \in l0 ++ (k, u) :: l. rewrite mem_cat inE orbC eqxx //. rewrite -H1.
move/in_filter_keys. ssa. ssa. done.
Qed.

Inductive Estep2 : lType -> elabel -> lType -> Prop :=
| estep2_msg d c v e0  : Estep2 (EMsg d c v e0) (d,c, inl v) e0
| estep2_branch n e es d c   : (n,e) \in es -> 
                              Estep2 (EBranch d c es) (d,c, inr n) e.

Lemma lookup_map3 : forall (A B C : eqType) (l : seq A) T lk (f : A -> (B * C)) x, uniq (dom (map f l)) ->  x \in l -> f x = (lk,T) -> lookup (map f l) lk = Some T.
Proof.
move=> A B C. elim;ssa.
destruct (eqVneq x a). subst.
rewrite H2. rewrite lookup_cons_eq //=.
rewrite inE (negbTE i) /= in H1.
destruct (eqVneq (f a).1 lk). rewrite lookup_cons_eq. 
eapply H in H1;eauto. f_equal. apply in_pair in H1.
apply (map_f fst) in H1. rewrite e in H3. ssa. rewrite H1 in H3. done. done.
rewrite lookup_cons_neq //=. eauto.
Qed.

Lemma to_canEstep2 : forall e l e', Estep2 e l e' -> canEstep2 e l.
Proof.
move=> e l e'. elim;ssa. econ. econ.
eauto.
Qed.

Lemma action_pres : forall g l g', step g l g' ->  action_pred g -> action_pred g'.
Proof.
move=> g l g'. elim;ssa.
apply (allP H2) in H. done.
apply/allP. intro. ssa.
have : size gs = size gs'. eauto.
move=>Hsize.
move/in_zip2 : H3. move/(_ _ _ Hsize). ssa.
move/inP : H6. move/H1. move=>HH. apply HH. apply (allP H5) in H3. done.
apply H0. rewrite -action_pred_subst. done. case;ssa.
Qed.

Lemma uniqg_labels_pres : forall g l g', step g l g' -> uniqg_labels g -> uniqg_labels g'.
Proof.
move=> g l g'.
elim;ssa. apply (allP H2) in H. done.
rewrite -H. done.
apply/allP. intro.  have : size gs = size gs' by eauto. move=>Hsize.
move/in_zip2. move/( _ _ _ Hsize). ssa.
move/inP : H6. move/H1. move=>HH. apply : HH.
apply (allP H5) in H3. done.
apply H0. apply uniqg_labels_subst. case;ssa. done.
Qed.

Lemma to_canStep : forall g l g', step g l g' -> size_pred g -> canStep g l.
Proof.
move => g l g'. elim;ssa.
econ. eauto. de gs. de gs'. econ.  ssa.  eauto. done.
econ. apply H0. rewrite size_pred_subst. done. case;ssa. done.
Qed.

Lemma coherent_pres : forall g l g', step g l g' -> coherentG g -> coherentG g'.
Proof.
intros. 
inv H0. ssa. con. 
apply:Linear_step;eauto.
con. apply: size_pred_step;eauto.
con. apply:action_pres;eauto.
con. apply: uniqg_labels_pres;eauto.
con. intros.
move : (H5 p). ssa.
have : Project g p (trans p g). apply/Project_EQ2. eauto. apply:proj_proj. done.
clear H7 => H7.
eapply preserve_proj5 in H7. econ. eauto. eauto.
ssa. ssa.
punfold H6. inv H6.
apply to_canStep in H as HC;ssa.
apply H7 in HC.
ssa.
de H9. eapply step_uniq2 in H. 2: apply H8. subst. done. done. done.
Qed.

Lemma step_contained : forall g l g' p, linearity.step g l g' -> p \in roles g'   -> p \in roles g.
Proof.
intros. 
rewrite -!in_roles in H0 *. destruct (inp p g) eqn:Heqn;ssa.
have : ~~ inp p g. rewrite Heqn. done.
intros. 
eapply preserve_not_part in H;eauto. rewrite H0 in H.
done.
Qed.

Lemma checkPath_cat3 : forall s s' T, checkPath s T -> checkPath s' (makeL s T) -> checkPath (s ++ s') T.
Proof.
elim;ssa. apply checkPath_fe2. done.
de a. rewrite /obs in H2. destruct (fe _) eqn:Heqn2;ssa. de d.
destruct (lookup _ _) eqn:Heqn3;ssa. rewrite /obs in H2.
destruct (fe _ ) eqn:Heqn2;ssa.
Qed.

Lemma ETr_checkPath : forall s e, ETr s e -> uniq_labels e ->  (all (fun x => x.1.1 == Sd) s) -> checkPath (map (fun x => if x.2 is inr n then Some n else None) s) e.
Proof.
move=> s e. elim;ssa.
rewrite /obs H. norm_eqs. done.
rewrite H.  apply H1.  apply uniq_full_unf in H2. rewrite H in H2. ssa. done.
rewrite /obs H. norm_eqs. ssa.
rewrite H. norm_eqs.
apply uniq_in_pair in H0;ssa. rewrite H0;ssa. apply H2. 
apply uniq_full_unf in H3. rewrite H in H3. ssa. apply in_pair in H0.
apply (allP H5) in H0. done. done.
apply uniq_full_unf in H3. rewrite H in H3. ssa.
Qed.

Lemma checkPath_ETr : forall s e, checkPath s e -> exists ss, ETr ss e /\ (all (fun x => x.1.1 == Sd) ss) /\ map (fun x => if x.2 is inr n then Some n else None) ss = s.
Proof.
elim;ssa. exists nil. ssa.
de a. rewrite /obs in H1. destruct (fe _) eqn:Heqn2;ssa. de d.
destruct (lookup _ _) eqn:Heqn3;ssa. apply H in H2. ssa.
exists ((Sd,c,inr n)::x). ssa. econ. eauto. apply in_pair in Heqn3. eauto. done.
f_equal. done.
rewrite /obs in H1. destruct (fe _) eqn:Heqn2;ssa.
de d. apply H in H2. ssa.
exists ((Sd,c,inl v)::x). ssa. econ. eauto. done. f_equal. eauto.
Qed.


Lemma same_label : forall (A B C : eqType) (l : seq ( A * B)) (l' : seq (A * C)) n n' t t', dom l = dom l' -> uniq (dom l) ->  (n, t, (n', t')) \in zip l l' -> n = n'.
Proof.
move=> A B C. elim;ssa.
de l'. de l'. rewrite inE in H2. de (orP H2).
norm_eqs. inv H1. ssa. inv H0.
inv H0. eauto.
Qed.

Lemma step_ETr : forall e l e', Estep e l e' -> uniq_labels e ->  forall s, all (fun x => l.1.2 != x.1.2) s -> ETr (s++[::l]) e -> ETr s e'.
Proof.
move => e l e'. elim;ssa. inv H1. de s. inv H3. 
de s. inv H2. ssa. neqt.
inv H4. de s. inv H6. de s. inv H5. ssa. 
econ. econ. eauto.
inv H2. de s. de s. inv H0. ssa. 
inv H5. neqt.
inv H5. de s. de s. inv H3. ssa. inv H8.
have : size es = size es1 by eauto. move=>Hsize.
move/in_zip1: H9. move/(_ _ _ Hsize). ssa. de x.
apply same_label in H9 as HH;ssa. subst. 
econ. econ. eauto. have : l0 = (n0,l0).2. done. move=>->. eapply H1;eauto.
apply/inP. eauto. ssa.
apply mem_zip in H9. ssa.
apply (allP H7) in H9. ssa. eauto.
apply H0. rewrite uniq_labels_subst;ssa. case: n;ssa. done.
eapply ETr_unf2 in H3. rewrite full_eunf_subst in H3. eapply ETr_unf in H3. 2:econ. done.
Qed.

Lemma step_ETr2 : forall e l e', Estep e l e' -> uniq_labels e ->  forall s l', all (fun x => l.1.2 != x.1.2 ) s -> ETr (s++[::l']) e -> l.1.2 = l'.1.2 -> ETr s e'.
Proof.
move => e l e'. elim;ssa. inv H1. de s. inv H4. 
de s. inv H3. ssa. neqt.
inv H4. de s. inv H7. de s. inv H6. ssa. 
econ. econ. eauto. subst.
inv H2. de s. de s. inv H0. ssa. 
inv H3. neqt. subst.
inv H5. de s. de s. inv H3. ssa. inv H6.
have : size es = size es1 by eauto. move=>Hsize.
move/in_zip1: H9. move/(_ _ _ Hsize). ssa. de x.
apply same_label in H9 as HH;ssa. subst. 
econ. econ. eauto. have : l0 = (n0,l0).2. done. move=>->. eapply H1;eauto.
apply/inP. eauto. ssa.
apply mem_zip in H9. ssa.
apply (allP H8) in H9. ssa. eauto.
eapply H0. rewrite uniq_labels_subst;ssa. case: n;ssa. done.
eapply ETr_unf2 in H3. rewrite full_eunf_subst in H3. eapply ETr_unf in H3. 2:econ. eauto.
done.
Qed.

Definition to_lp := fun (x : dir * ch * (value + nat)) => if x.2 is inr n then Some n else None.

Lemma ETr_makeL : forall s0 s1 e, uniq_labels e ->  ETr (s0++s1) e -> ETr s1 (makeL (map to_lp s0) e).
Proof.
elim;ssa. apply ETr_unf2. done.
inv H1. ssa. rewrite H4. apply H.  apply  uniq_full_unf in H0. rewrite H4 in H0. ssa. done.
ssa. rewrite H4.
apply uniq_in_pair in H5. rewrite H5. 
apply uniq_full_unf in H0. rewrite H4 in H0. ssa.
apply H. apply in_pair in H5. apply (allP H3) in H5. done. done.
apply uniq_full_unf in H0. rewrite H4 in H0. ssa.
Qed.


Lemma ETr_makeQ : forall s e, ETr s e -> checkPath (map to_lp s) e -> uniq_labels e ->  map fst (makeQ (map to_lp s) e) = map (fun x => x.1.2) s.
Proof.
move=> s e. elim;ssa.
rewrite /obs. ssa. rewrite H in H4 H5 *. de d. f_equal. apply H1. done.
apply uniq_full_unf in H3. rewrite H in H3. ssa. 
rewrite /obs in H4. rewrite H in H4. done.
rewrite H in H5 H6 *.
apply uniq_in_pair in H0;ssa. rewrite /obs H0. rewrite H. rewrite H0 in H6. de d. f_equal. 
apply H2. done. apply uniq_full_unf in H4. rewrite H in H4. ssa. apply in_pair in H0. apply (allP H7) in H0. done.
ssa. rewrite /obs H in H5. done.
apply uniq_full_unf in H4. rewrite H in H4. ssa.
Qed.


Lemma ETr_cat : forall s0 s1 e, ETr (s0++s1) e -> ETr s0 e.
Proof.
elim;ssa. inv H0. econ. eauto. eauto.
econ. eauto. eauto. eauto.
Qed.

Lemma seq_split : forall (A : Type) (p l x  : seq A) v, l = p ++ v :: x -> exists x0 x1, p = x0 /\ x = x1 /\ l = x0 ++ v::x1.
Proof.
move=> A. elim;ssa. subst. exists nil. exists x. ssa.
de l0. inv H0. eauto.
Qed.

Lemma makeL_fe2 : forall p l, makeL p l = makeL p (fe l).
Proof.
elim;ssa. rewrite full_eunf2;ssa.
rewrite /nexte_wrap full_eunf2;ssa.
Qed.

Lemma checkPath_Estep2 : forall e l e',  Estep e l e' ->  forall p k u v x,  all (fun x => x.1 != k ) (makeQ p e) -> checkPath p e ->
                                                 obs v (makeL p e) = Some (k,u) -> checkPath (p++(v::x)) e -> uniq_labels e -> l.1.2 = k -> l.2 = u ->checkPath (p++x) e'.
Proof.
move=> e l e'. elim;ssa;subst.
- de p. ssa. rewrite /obs in H1. ssa. de d. de v0.
  ssa. rewrite /obs in H4 H0. ssa. de d. de o. neqt.
  rewrite /obs in H4 H0. ssa. de d. de o. neqt.
- de p. ssa. rewrite /obs in H4 H7. ssa. rewrite /nexte_wrap in H8. ssa.
  de v0. inv H4.
  rewrite /obs in H2 H5 H7. ssa. de o. eauto.
- de p. ssa. rewrite /obs in H2 H4. ssa. de d. de v.
  inv H2. apply uniq_in_pair in H;ssa. rewrite H in H5. done.
  rewrite /obs in H1 H4. ssa. de d. de o. 
  destruct (lookup es n0) eqn:Heqn;ssa. neqt.
  rewrite /obs in H1 H4. ssa. de d. de o. 
  destruct (lookup es n0) eqn:Heqn2;ssa. neqt.
- de p. rewrite /obs in H5 H7. ssa. de v. inv H5.
  rewrite /obs in H6 H7. ssa. de o. destruct (lookup es0 n) eqn:Heqn;ssa.
  apply in_pair in Heqn. have : size es0 = size es1 by eauto.
  move=>Hsize. move/in_zip1 : Heqn. move/(_ _ _ Hsize). ssa. de x0.
  apply uniq_in_pair in H3;ssa. apply same_label in H13 as HH;ssa. subst.
  rewrite H3. have : l0 = (n0,l0).2. done. move=>->. apply:H1.
  apply/inP. eauto. 2:eauto. 3:eauto. 2:eauto. ssa. ssa.
  apply mem_zip in H13. ssa. apply (allP H11) in H1. ssa. done. done.
  rewrite /dom -H. done.
- apply checkPath_fe in H4. rewrite full_eunf_subst in H4. apply checkPath_fe2 in H4. 
  apply:H0;eauto. by rewrite makeQ_fe full_eunf_subst -makeQ_fe in H1.
  apply checkPath_fe in H2. rewrite full_eunf_subst in H2. apply checkPath_fe2 in H2. done.
  by rewrite makeL_fe2 full_eunf_subst -makeL_fe2 in H3.
  rewrite uniq_labels_subst;ssa. case: n;ssa.
Qed.

Lemma checkPath_Estep3 : forall e l e',  Estep e l e' -> uniq_labels e ->  l.1.1 = Rd -> forall p, checkPath p e -> checkPath p e'.
Proof. 
move=> e l e'. elim;ssa;subst.
- de p.
- de p. rewrite /obs /nexte_wrap in H3 H5;ssa. de o.
- de p.
- de p. rewrite /obs /nexte_wrap in H3 H4. ssa. de o.
  destruct (lookup es0 n) eqn:Heqn;ssa.
  apply in_pair in Heqn. 
  have : size es0 = size es1 by eauto.
  move=>Hsize. move/in_zip1 : Heqn. move/(_ _ _ Hsize). ssa.
  de x. apply uniq_in_pair in H5;ssa. apply same_label in H8 as HH;ssa. subst.
  rewrite H5. have : l0 = (n0,l0).2. done. move=>->. eapply H1;eauto.
  apply/inP. eauto. ssa. apply mem_zip in H8. ssa. apply (allP H7) in H8.  ssa.
  ssa. rewrite /dom -H //.
- apply checkPath_fe in H3. rewrite full_eunf_subst in H3. apply checkPath_fe2 in H3. apply H0;eauto.
  rewrite uniq_labels_subst;ssa. case: n;ssa.
Qed.

Lemma Estep2_makeL : forall e l e', Estep2 e l e' -> uniq_labels e -> fe e' = makeL ((to_lp l)::nil) e.
Proof.
intros. inv H. ssa.
apply uniq_in_pair in H1. rewrite H1. done. done.
Qed.


  






Lemma in_rem :  forall (A B : eqType) (l : seq (A * B)) k k', k \in dom l -> k <> k' -> k \in dom (remove l k'). 
Proof. 
move => A B.  elim;ssa.   rewrite inE in H0. de (orP H0). norm_eqs. 
rifliad.  rewrite inE eqxx //=.  exfalso. apply/H1. move/eqP : H2. done. 
clear H0. rifliad;  eauto. 
rewrite /dom.  ssa.
Qed. 


Lemma qType_done_filter_nil : forall Q, qType_done Q -> qType_done (filter (fun kv => kv.2 == nil) Q).  
Proof. 
intros. rewrite /qType_done all_filter //=. apply/allP. intro. ssa. apply/implyP=>//=. 
Qed. 
Hint Resolve qType_done_filter_nil.


Lemma dom_filter_q : forall (Q : q_env) f, dom (filter_q Q f) = dom Q.
Proof. 
intros. rewrite /dom /filter_q //=.  rewrite -map_comp. apply/eq_in_map. 
ssa.
Qed. 

Lemma lookup_filter_q : forall Q k l l' f, lookup Q k = Some l' ->  (filter_keys (f k) l') = l  -> lookup (filter_q Q f) k = Some l.
Proof.
elim;ssa.  apply lookup_or in H0. de H0. subst.  
rewrite lookup_cons_eq.  ssa. ssa. 
rewrite lookup_cons_neq. eauto.  done. 
Qed. 

Lemma lookup_filter3
     : forall (A B : eqType) (l : seq (A * B)) (T : B) (k : A) (p : pred (A * B)),
       p (k,T) -> lookup l k = Some T -> lookup (filter p l) k = Some T.
Proof. 
move=> A B. elim;ssa. 
apply lookup_or in H1. de H1. subst. de a. rewrite H0. 
rewrite lookup_cons_eq //=. 
rifliad.  rewrite lookup_cons_neq.  eauto.  done. eauto. 
Qed. 

Lemma uniq_filter_q : forall Q f, uniq (dom Q) -> uniq (dom (filter_q Q f)).
Proof. 
intros. rewrite dom_filter_q //=. 
Qed. 

Hint Constructors OFT.
Lemma OFT_strength : forall Ms D P E Q C Ms', OFT Ms D P E Q C -> (forall k v, OFTV Ms k v -> OFTV Ms' k v) ->  OFT Ms' D P E Q C.
Proof.
intros. 
elim : H Ms' H0;intros; try solve [ econ;eauto].
econ;eauto. 
elim : H0 Ms' H4 ;eauto;ssa. con. eauto. 
con;eauto.
econ;eauto. apply/H2. ssa.
inv H4. de n. rewrite lookup_cons_eq in H5;ssa. inv H5. con. done.
con. rewrite lookup_insertS0_valBool in H5 *.
rewrite lookup_insertS0_valBool. 
suff : OFTV Ms' (var_valBool n) v. 
intros. inv x.
have: OFTV Ms0 (var_valBool n) v. 
con. done.
move=> HH. eauto. con.
rewrite lookup_insertS0_val in H5. con. 
rewrite lookup_insertS0_val.
suff : OFTV Ms' (valB (var_val n)) v.  intro. inv x.
have : OFTV Ms0 (valB (var_val n)) v. con. done.
eauto.
econ;eauto. 
elim : H4 Ms' H5;eauto.
ssa. con. eauto.
ssa. con;eauto.
econ;eauto.
apply/H1. ssa.

inv H3. con. rewrite lookup_insertS1_valBool in H4 *. 
rewrite lookup_insertS1_valBool. eauto.
suff : OFTV Ms' (var_valBool n) v. intro. inv x.
have : OFTV Ms0 (var_valBool n) v. con. done.
eauto. con.
de n. 
rewrite lookup_cons_eq in H4;ssa. inv H4. con. 
rewrite lookup_cons_eq;ssa. con.
rewrite lookup_insertS1_val in H4 *.
rewrite lookup_insertS1_val. 
suff: OFTV Ms' (valB (var_val n)) v. intro.  inv x.
have : OFTV Ms0 (valB (var_val n)) v. con. done.
eauto.
econ;eauto.
elim : H2 Ms' H8;eauto.
intros. econ;eauto.
intros. econ;eauto.
Qed.
Definition coherentG_env (Ms : s_env) := forall lk g, lookup Ms lk = Some (SGType g) -> coherentG g. 

(* Binary session types with polarities checks duality with the environment predicate balanced(), ensuring that when both k+ and k- are present, their session types are dual. Duality of multiparty session types is ensured by coherence, all the roles of a session have their local type derived from a global type. The question is then, do we need all roles of the global type to be in this environment? Leaving some out, means reduction can get stuck, but it allows compositionality as the typing of a single process can be coherent. I find it most natural to relax coherence: All local types are derived from a global type, but all roles of this global type need not be present in the environment.
*)

Lemma good_subst2_insertL02 : forall E kv p, good_subst2 (insertL0 E kv) (succn>>ids) (((schlT (var_schl 0) p).:ids)).
Proof.
ssa. intro. simpl.  ssa. rewrite !inE in H,H0. 
destruct (orP H);norm_eqs.
- destruct (orP H0);norm_eqs.
  * done. 
  * rewrite /dom -map_comp in H2. destruct (mapP H2). subst.  asimpl in H1. de x. de s. inv H1. de s. 
- rewrite /dom -map_comp in H2. destruct (mapP H2). subst.  destruct (orP H0);norm_eqs. ssa.
  asimpl in H1.   de x. de s. de s. 

  ssa. rewrite /dom -map_comp in H4.  destruct (mapP H4). ssa. subst.  asimpl in H1. de x. de x0. 
  de s. de s0. inv H1. de s0. asimpl. inv H1. de s. 
Qed. 

Definition only_schl (E: l_env) := all (fun c => if c is schlT _ _ then true else false) (dom E).


Lemma in_filter_keys3 : forall (A B : eqType) (l : seq ( A* B)) x p l', filter_keys p l = x::l' -> exists l0 l1, l = l0 ++ (x::l1) /\ all (fst >> predC p) l0 /\ p x.1. 
Proof. 
move => A B. elim;ssa. 
move : H0. rifliad.  case. intros. subst. 
exists nil.  exists l. ssa.
move/H. ssa.  subst.  exists (a::x0). exists x1. ssa. asimpl. 
rewrite H0 //=. 
Qed. 


Lemma makeQ_cat : forall l l0 l1 e, checkPath l e -> makeQ l e = l0++l1 -> exists f0 f1, l = f0++f1 /\ makeQ f0 e = l0. 
Proof. 
elim;ssa. de l0. de l1. exists nil. exists nil. ssa. 
edestruct (obs _ _) eqn:Heqn. edestruct (nexte_wrap _ _) eqn:Heqn2. de l0.
de l1. inv H1.  exists nil. exists (a::l). ssa. 
inv H1. 
apply H in H5; ssa.  exists (a::x). exists x0. ssa. subst.  done. 
rewrite Heqn Heqn2 //=. rewrite H4 //=. done. done.
Qed. 


Require Import MPSTSR.linearity. 

Lemma Proj_eq : forall g0 g1 p e, Project g0 p e -> Project g1 p e -> EQ2 (trans p g0) (trans p g1).
Proof.  
intros. apply proj_proj in H,H0. apply/EQ2_trans. apply/EQ2_sym. eauto. done.
Qed. 

Lemma Proj_eq2 : forall g p e e', Project g p e -> Project g p e' -> EQ2 e e'.  
Proof.  
intros. apply proj_proj in H as HH. apply proj_proj in H0 as HH'. apply/EQ2_trans. eauto.  apply/EQ2_sym.
apply/EQ2_trans. eauto. apply/EQ2_refl. apply/gInvPred_proj. 
apply/Unravel_gInvPred.
apply/Project_gtree. eauto. 
Qed. 


Lemma one_shot_eq : forall g f p, one_shot g f -> EQ2 (f p) (trans p g). 
Proof. 
intros. rewrite /one_shot in H. 
apply/proj_proj. done.
Qed. 

Lemma one_shot2 : forall g f, one_shot g f -> one_shot g (trans^~ g). 
Proof. 
intros. rewrite /one_shot. intros. apply/project_projT.  apply/H.
Qed. 

Definition both_closed P := sch_closed P /\ valBool_closed P /\ proc_pred P.

Lemma both_sch : forall P, both_closed P -> sch_closed P.
Proof. ssa. inv H.
Qed.

Lemma both_valBool : forall P, both_closed P -> valBool_closed P.
Proof. ssa. inv H. ssa.
Qed.
Hint Resolve both_sch both_valBool.

Definition is_var_val (v : valBool) :=
match v with 
| valB (var_val _) => true 
| _ => false 
end.

Definition only_var_val (Ms : s_env) := all is_var_val (dom Ms).

Lemma Cong_sch_fv : forall P P', Cong P P' -> forall n, n \in proc_sch_fv P -> n \in proc_sch_fv P'.
Proof.
intros. apply/Cong_no_sch. eauto. done.
Qed.

Lemma Cong_valBool_fv : forall P P', Cong P P' -> forall n, n \in proc_valBool_fv P <-> n \in proc_valBool_fv P'.
Proof.
move=> P P'. elim;ssa.
split;ssa.
rewrite cats0 in H. done. rewrite mem_cat. ssa.

split;ssa.
rewrite !mem_cat in H *. rewrite orbC //=.
rewrite !mem_cat in H *. rewrite orbC //=.

split;ssa.
rewrite !mem_cat in H *. rewrite orbA //. 
rewrite !mem_cat in H *. de (orP H). left.  ssa.
de (orP H0). left. ssa.

split;ssa.
rewrite !mem_cat in H *. ssa. de (orP H);ssa. right.
apply/proc_valBool_subst. done.
rewrite mem_cat in H. de (orP H). rewrite mem_cat. ssa.
rewrite mem_cat. apply/orP. right.
eapply proc_valBool_subst in H0. 
move : H0.
instantiate (1:= ids).
instantiate (1:= predn).
instantiate (1:= ids).
instantiate (1:= ids). asimpl. eauto.

rewrite !mem_cat. 
split;ssa. de (orP H). right.
apply/proc_valBool_subst. eauto. 
de (orP H). right.
eapply proc_valBool_subst in H0. 
move : H0.
instantiate (1:= ids).
instantiate (1:= ids).
instantiate (1:= ids).
instantiate (1:= predn). asimpl.  eauto.
rewrite H0. done.
rewrite H0. rewrite H2. done.
Qed.


Lemma Cong_sch_fv2 : forall P P', Cong P' P -> forall n, n \in proc_sch_fv P -> n \in proc_sch_fv P'.
Proof.
move=> P P'. intros. apply/Cong_no_sch. apply/CSym. eauto. done.
Qed.

Lemma subst_exp_valBool_fv : forall s sig0 sig1  n, n \in exp_valBool_fv (subst_exp sig0 sig1 s) ->
                                                     exists n', n' \in exp_valBool_fv s /\ sig1 n' = var_valBool n.
Proof.
elim;ssa. de v. destruct (sig1 n0) eqn:Heqn;ssa. rewrite inE in H. norm_eqs.
econ. con. eauto.  inv Heqn. 
rewrite mem_cat in H1. de (orP H1). 
apply H in H2. ssa. econ. rewrite mem_cat. ssa.
left. eauto. done.
apply H0 in H2. ssa. econ. 
rewrite mem_cat. ssa. right. eauto. done.
Qed.

Lemma subst_msgp_valBool_fv : forall c n sig0 sig1 sig2 sig3, n \in msgp_valBool_fv (subst_msgp sig0 sig1 sig2 sig3 c) -> exists n', n' \in msgp_valBool_fv c /\ sig1 n' = var_valBool n. 
Proof. 
case;ssa. destruct m;ssa. de v. destruct (sig1 n0) eqn:Heqn;ssa. rewrite inE in H. norm_eqs. 
econ. con. eauto. done.
Qed. 



Lemma subst_proc_valBool_fv
 : forall P n sig0 sig1 sig2 sig3, n \in proc_valBool_fv (subst_process sig0 sig1 sig2 sig3 P) -> exists n', n' \in proc_valBool_fv P /\ sig1 n' = var_valBool n. 
Proof.
 elim/process_ind;ssa. 

 apply H in H0. ssa. ssa. econ. con. eauto.  rewrite -H1. asimpl. done.
apply H in H0. ssa. econ. con. eauto. rewrite -H1. asimpl. done.
rewrite mem_cat in H0. de (orP H0). 
apply subst_exp_valBool_fv in H1. ssa. 
econ. rewrite mem_cat. ssa. left. eauto. done.
apply H in H1. ssa. econ. con. rewrite mem_cat. apply/orP. eauto. done.
de (mapP H0). rewrite mem_filter in H1. ssa.
subst. de x.

apply H in H4. ssa. 
asimpl in H2. ssa. de x0. asimpl in H2. 
destruct (sig1 x0) eqn:Heqn;ssa. inv H2.
econ. con. apply/mapP. econ. rewrite mem_filter.  apply/andP.
con. 2:eauto. done. simpl. done. done.
apply H in H0. ssa. econ. con. eauto. done.
apply H in H0. ssa. econ. con. eauto. subst. 
asimpl in H1. done.
apply H in H0. ssa. econ. con. eauto. done.

de (flattenP H0). de (mapP H1). subst.
de (mapP H3). subst. ssa.
de x. ssa. asimpl in H2.  ssa. eapply H in H4 as H4'. 2:eauto.
ssa. econ. con. apply/flattenP. econ.  
apply/mapP. econ.
3:eauto. eauto. done. done.

rewrite mem_cat in H1. de (orP H1). 
apply subst_exp_valBool_fv in H2. ssa. econ. con. rewrite mem_cat.
apply/orP. eauto. done.
rewrite mem_cat in H2. de (orP H2).
apply H in H3. ssa. econ. rewrite mem_cat. ssa. right. rewrite mem_cat.
ssa. eauto. eauto.
apply H0 in H3. ssa. econ. rewrite !mem_cat. ssa. right. ssa. eauto. eauto.
rewrite mem_cat in H1. de (orP H1). apply H in H2. ssa.
econ. ssa. rewrite mem_cat. ssa. eauto. done.
apply H0 in H2. ssa. econ. rewrite mem_cat. ssa. eauto. done.

apply H in H0. ssa. asimpl in H1. econ. con. eauto. done.

apply H in H0. ssa. asimpl in H1. destruct (sig1 x) eqn:Heqn;ssa.
inv H1. econ. ssa. eauto. done.
apply subst_exp_valBool_fv in H. ssa. econ. ssa. eauto. eauto.
de (flattenP H). de (mapP H0). subst.
de (mapP H2). subst.

apply subst_msgp_valBool_fv in H1. ssa. econ. 
ssa. apply/flattenP. econ. apply/mapP. econ. eauto. econ.
2:eauto. done.
Qed.



Lemma Cong_valBool_fv2 : forall P P', Cong P' P -> forall n, n \in proc_valBool_fv P -> n \in proc_valBool_fv P'.
Proof.
ssa. apply/Cong_valBool_fv. eauto. done.
Qed.

Lemma proc_pred_red : forall P D P', Sem D P P' -> (forall d, d \in D -> proc_pred d) -> proc_pred P -> proc_pred P'.
Proof.
move=> P D P'.
elim;ssa. 
- elim : H H0 H1. ssa. apply/proc_pred_subst. ssa.
  de n. clear H H0 H2. elim : H1 H5. ssa. apply/proc_pred_subst. done.
  ssa. apply/proc_pred_subst. eauto.
-  clear H H0 H1. elim :q. ssa. ssa.
  apply/proc_pred_subst. done.
  apply/proc_pred_subst. done.
  apply in_pair in H. apply (allP H4) in H. done.
- apply proc_pred_subst. apply/H1. apply/mem_nth. done.
- apply/proc_pred_pres. apply/CSym. apply H2. apply H1. eauto.
  apply/proc_pred_pres. apply/CSym. eauto. done.
Qed.


Definition envP (A B : eqType) (E : seq ( A* B)) (P : B -> Prop) := forall lk T, lookup E lk = Some T -> P T.

Definition good_defs (Ds : def_env) := forall l, l \in Ds -> (all (fun x => (~~ is_erec x) && (uniq_labels x)) l.2). 

Definition side_conds  Ds Ps Ms P E Q := coherentG_env Ms /\  env_not_rec E /\  partial_balanced E Q /\ both_closed P /\ only_schl E /\ only_var_val Ms /\ uniq (dom Q) /\ uniq (dom E) /\ sub_domLQ E Q /\ DefTyping Ds Ps /\ envP E uniq_labels /\ good_defs Ds.

Lemma weak_coherentP : forall E, coherent E -> weak_coherent (makeLs E all_left) (makeQs E all_left).  
Proof. 
intros. rewrite /weak_coherent. exists E. exists all_left. ssa.
Qed. 

Lemma OFT_req : forall Ms Ds v n q P1 R E Q C, OFT Ms Ds (Par (SessReq (valB v) n q P1) R) E Q C ->  coherentG_env Ms  -> exists G, lookup Ms (valB v) = Some (SGType G) /\ coherentG G.
Proof. 
intros. inv H. inv H8.  inv H10. econ. ssa. eauto. eauto. 
Qed. 

Ltac ssa := utils.ssa.

Lemma qType_done_filter_hrel0 : forall (Q : q_env), qType_done (filter_q Q (@hrel0 qkey ch)). 
Proof. 
intros. apply/allP. intro. intros.  ssa. 
rewrite /filter_q in H. destruct (mapP H). subst.
ssa.
ssa. rewrite filter_keys_pred0 //=. 
Qed. 

Lemma filter_q_pred0_2 : forall (Q : q_env),  (filter_q Q (@hrel0 qkey ch)) = map (fun k => (k,nil)) (dom Q). 
Proof.
elim;ssa.   f_equal. rewrite filter_keys_pred0. done.
done.
Qed. 



Definition is_role (p : ptcp) (l : lkey) := l == schlT (var_schl 0) p. 
Definition is_qrole (p : ptcp) (l : qkey) := l == QKey (var_schl 0) p. 



Lemma pred_dom_not : forall (E : l_env)  f0 x, pred_dom (dom E) shiftL1 f0 (schlT (var_schl 0) x) = false.
Proof. 
ssa. rewrite /pred_dom.  ssa. apply/hasPn. intro. ssa. 
rewrite negb_and. de x0. de s. 
Qed. 

Lemma filter_keys_uniq_dom : forall (E : l_env) (p : lkey -> bool) lk, lk \in dom E -> uniq (dom E) -> 
  dom (filter_keys (fun lk' => lk' == lk) E) = lk::nil.  
Proof. 
intros. 
rewrite /filter_keys /dom.   elim : E H H0;ssa.
de (orP H0). norm_eqs. rewrite eqxx //=. f_equal. 
clear H H0 H3. elim : l H2;ssa. 
rifliad. norm_eqs. rewrite inE negb_or in H2.  ssa. 
rewrite H0 eqxx in H1.  done. 
rewrite inE negb_or in H2. ssa.
rifliad. norm_eqs. ssa. f_equal. 
clear H H1 H0. 
clear H3.  elim : l H2;ssa. 
rifliad. norm_eqs. rewrite inE negb_or in H2.  ssa. 
rewrite H0 eqxx in H1.  done. 
rewrite inE negb_or in H2. ssa.
rifliad. norm_eqs. ssa. 
Qed. 

Lemma filter_keys_uniq : forall (E : l_env) lk T, lk \in dom E -> uniq (dom E) -> lookup E lk = Some T ->
  (filter_keys (fun lk' => lk' == lk) E) = (lk,T)::nil.  
Proof. 
intros. 
rewrite /filter_keys /dom.   elim : E H H0 H1;ssa.
de (orP H0). norm_eqs. rewrite eqxx //=. 
rewrite lookup_cons_eq in H2. inv H2. de a. 
f_equal. 
clear H H0 H4 H2. elim : l H3;ssa. 
rifliad. norm_eqs. rewrite inE negb_or in H3.  ssa. 
rewrite eqxx in H0.  done. 
rewrite inE negb_or in H3. ssa. done.
rifliad. norm_eqs. rewrite lookup_cons_eq in H2.  inv H2. 
ssa. f_equal. de a. 
clear H H0 H4 H2 H1. elim : l H3;ssa. 
rifliad. norm_eqs. rewrite inE negb_or in H3.  ssa. 
rewrite H0 eqxx in H1.  done. 
rewrite inE negb_or in H3. ssa.
rifliad. norm_eqs. ssa. f_equal.
apply/H.   done.  done. rewrite lookup_cons_neq in H2.  done. done.
Qed. 

Lemma filter_keys_map : forall (l : seq nat) (E : l_env) f0 g n, uniq l -> n \in l ->
  filter_keys (predU (is_role n) (pred_dom (dom E) shiftL1 f0))
       (list_map (initL1 \o (fun p : nat => (Ptcp p, fe (trans p g)))) l) = (schlT (var_schl 0) n,fe (trans n g))::nil.
Proof. 
ssa. 
erewrite filter_keys_eq. 2 : { intros.   instantiate (1 := is_role n). 
ssa. rewrite /dom -!map_comp in H1. de (mapP H1). subst. Congruence.ssa.
rewrite pred_dom_not.  lia. } 
have : is_role n = fun lk => lk == (schlT (var_schl 0) n). done. 
move=>->.
erewrite filter_keys_uniq.  eauto.
apply/mapP. econ. apply/map_f. eauto. ssa.
rewrite /dom -!map_comp. rewrite map_inj_uniq //=.  
intro. ssa. inv H1. 
rewrite /lookup.  
elim : l n H H0;ssa. 
rewrite inE in H1. de (orP H1). norm_eqs.
rewrite eqxx //=. rifliad. 

move/eqP : H4. case. intros. subst. 
rewrite H0 in H2. done. 
eauto. 
Qed. 

Lemma is_role_shift x n :   is_role n (shiftL1 x) = false.
Proof. rewrite /is_role.  de x. de s. 
Qed. 




Lemma filter_qkey0 : forall Q Q0 q, (filter_q (insertQ Q Q0) (pred_dom2 (dom Q) shiftQ q)) = (map (fun k => (QKey (var_schl 0) k,nil)) (dom Q0))++ ( map_keys shiftQ (filter_q Q q)). 
Proof. 
intros. rewrite /insertQ /insert_shift /insert. ssa.
rewrite filter_q_cat. f_equal. 
rewrite /filter_q.  ssa. rewrite /dom.  rewrite -!map_comp. 
apply/eq_in_map. intro. ssa.  erewrite filter_keys_eq.
erewrite filter_keys_pred0. done.
ssa. rewrite /pred_dom2. apply/hasPn. intro. ssa.
rewrite negb_and. ssa. de x1. de s. 

rewrite filter_q_map_keys.  f_equal.
erewrite filter_q_eq. eauto.
intros. ssa. 
rewrite pred_dom2P. done. done. done.
Qed. 

Lemma pred_dom_shiftC : forall  (C : c_env)  (q : ckey -> bool)  a, pred_dom (dom C) shiftC q (schliT (var_schl 0) a) = false. 
Proof. 
ssa. rewrite /pred_dom. apply/hasPn. intro. ssa.
de x.  de s. 
Qed. 

Lemma filter_ckey0 : forall C C0 q, (filter_keys (pred_dom (dom C) shiftC q) (insertC C C0) ) = 
                                 ( map_keys shiftC (filter_keys q C)). 
Proof. 
intros. rewrite /insertC /insert_shift /insert. ssa.
rewrite filter_keys_cat. 
erewrite filter_keys_eq. erewrite filter_keys_pred0. ssa.
rewrite filter_keys_map_keys. f_equal. 
apply/filter_keys_eq. intro. ssa.
rewrite pred_domP //=. eauto.
ssa. rewrite /dom -map_comp in H. de (mapP H). subst. 
rewrite pred_dom_shiftC //=.
Qed. 

Lemma filter_keys_insertL0_f_aux : forall E E1 f0, (filter_keys (predU (is_lkey0) (pred_dom (dom E) shiftL0 f0))  (insertL0 E E1)) =
 (insertL0 (filter_keys f0 E) E1). 
Proof. 
intros. 
rewrite /insertL0 /insert_shift /insert. ssa. f_equal.
rewrite filter_keys_map_keys. f_equal.
erewrite filter_keys_eq. eauto. 
ssa. Congruence.ssa. rewrite is_lkey0_shift /=. rewrite pred_domP //=. eauto.
Qed. 

Lemma filter_keys_insertL0_f : forall E E1 f0,  (insertL0 (filter_keys f0 E) E1) = (filter_keys (predU (is_lkey0) (pred_dom (dom E) shiftL0 f0))  (insertL0 E E1)).
Proof. 
intros. rewrite filter_keys_insertL0_f_aux //=.
Qed. 


Definition is_ptcp (p : ptcp) : pred sch :=  fun s => match s with | schlT (var_schl 0) p' => p == p'
                                                                         | _ => false 
                                                                                 end. 

Lemma predCT : forall (A : Type), predC predT = @pred0 A.
Proof. 
ssa.
Qed. 

Lemma dom_insertQ : forall ( Q: q_env) Q', dom (insertQ Q Q') = (map (QKey (var_schl 0)) (dom Q')) ++ dom (map_keys shiftQ Q). 
Proof. 
intros. rewrite /insertQ /insert_shift /insert dom_cat.  f_equal. 
rewrite /dom -!map_comp. done.
Qed. 

Lemma map_eq : forall (A B : eqType) (l : seq A) (f f' : A -> B), (forall x, x \in l -> f x = f' x) -> map f l = map f' l.
Proof. 
intros. apply/eq_in_map. intro. ssa. 
Qed. 



Lemma in_filter_q2 : forall (Q : q_env) (x : qkey* qType) f, x.1 \in dom Q -> x.1 \in dom (filter_q Q f).
Proof. 
intros. de (mapP H). rewrite dom_filter_q //=. 
Qed. 

Lemma in_filter_q3 : forall (Q : q_env) (x : qkey* qType) (f : hrel qkey ch)  y, x \in  Q -> y \in dom (x.2) -> f x.1 y ->
                                                                           exists y', (x.1,y') \in (filter_q Q f) /\ y \in (dom y'). 
Proof. 
intros. ssa. elim : Q x y H H0 H1;ssa. 
rewrite inE in H0. de (orP H0). norm_eqs. econ.
rewrite inE.  ssa. rewrite dom_filter_keys. rewrite mem_filter. ssa. 
eapply H in H3. de H3.  2 : eauto. exists x0. 
rewrite inE. ssa. done.
Qed. 

Lemma in_filter_q4 : forall (l : q_env) (x : qkey) (f : hrel qkey ch) (y : qType) (y' : ch), 
(x, y) \in filter_q l f ->
 f x y' = false -> y' \notin dom y.
Proof. 
elim;ssa.  rewrite inE in H0. de (orP H0).  norm_eqs. inv H2.  
rewrite dom_filter_keys mem_filter negb_and H1. ssa.
eauto. 
Qed. 

Lemma in_filter_q5 : forall (Q : q_env) (x : qkey* qType) (f : hrel qkey ch)  y, x \in  Q -> y \in dom (x.2) -> f x.1 y = false -> forall y', (x.1,y') \in (filter_q Q f) -> y \notin (dom y'). 
Proof. 
intros. ssa. elim : Q x y y' H H0 H1 H2;ssa. 
rewrite inE in H0. de (orP H0). norm_eqs. 
rewrite inE in H3. de (orP H3). norm_eqs. inv H4. 
rewrite dom_filter_keys. rewrite mem_filter negb_and. ssa. rewrite H2. ssa.

apply/negP. intro.  eapply in_filter_q4 in H4. erewrite H5 in H4. done.
done. rewrite inE in H3. de (orP H3). norm_eqs. inv H5. rewrite dom_filter_keys. rewrite mem_filter. rewrite negb_and. rewrite H2 //=. eauto. 
Qed. 

Lemma  qType_done_filter_q : forall (Q : q_env) (f : hrel qkey ch)  x y, qType_done (filter_q Q f) -> x \in Q -> y \in  dom x.2 -> f x.1 y = false.
Proof. 
intros. apply/negP. intro. apply (@in_filter_q3 _ _ f y) in H0. ssa.  apply (allP H) in H0. 2 : eauto. ssa. 
norm_eqs. done. done. 
Qed. 



Lemma  qType_done_filter_q2 : forall (Q : q_env) (f : hrel qkey ch)  x, qType_done (filter_q Q f) -> x \in Q -> filter_keys (f x.1) x.2 = nil.  
Proof. 
intros. ssa. rewrite /qType_done in H. ssa.
rewrite /filter_q in H. rewrite all_map in H.
apply (allP H) in H0. ssa. norm_eqs. done. 
Qed. 

Lemma qType_done_cat : forall (Q0 Q1 : q_env), qType_done (Q0 ++ Q1) = (qType_done Q0) && (qType_done Q1).
Proof. 
intros. rewrite /qType_done. ssa. rewrite all_cat.  f_equal. 
Qed. 

Lemma IndexSet_mem : forall n l, IndexSet n l -> n \in l.
Proof. 
intros. elim : H;ssa.
Qed. 

Hint Resolve IndexSet_mem.

Lemma lt_memI : forall n x l, x \in l -> IndexSet n l -> x <= n.
Proof. 
intros. elim : H0 H;ssa. norm_eqs. done. de (orP H1). norm_eqs. done. 
Qed. 

Lemma side_conds_to v n1 q P1 R E Q Ms Ds Ps : 
side_conds Ds Ps Ms (Par (SessReq (valB v) n1.+1 q P1) R) E Q ->
side_conds Ds Ps Ms  R E Q.
Proof. rewrite /side_conds. ssa.
rewrite /sch_closed in H2. inv H2.  con;ssa.
intro.
apply/negP. intro. apply/negP.  apply/H11. 2: {  rewrite //= mem_cat. apply/orP. eauto. } 
intro. apply/negP. intro. apply/negP. apply/H12. 2: {  rewrite //= mem_cat. apply/orP. eauto. } 
Qed. 

Lemma side_conds_to2 v n1 P1 R E Q Ms Ds Ps : 
side_conds Ds Ps Ms (Par (SessAcc (valB v) n1.+1 P1) R) E Q ->
side_conds Ds Ps Ms  R E Q.
Proof. rewrite /side_conds. ssa. 
rewrite /sch_closed in H2. ssa. 
inv H2. ssa. con.
intro. ssa. apply/negP. intro. apply/negP. apply H11.
rewrite /= mem_cat. apply/orP. eauto. 
ssa. ssa.
intro. ssa. apply/negP. intro. apply/negP. apply H12.
rewrite /= mem_cat. apply/orP. eauto. 
Qed. 

Fixpoint is_msg (P : process) := 
match P with 
| MsgQ _ _ => true 
| Par P0 P1 => is_msg P0 || is_msg P1
| ResCh P0 => is_msg P0
| ResVal P0 => is_msg P0
| _ => false 
end. 

Lemma partition_nil : forall ( A B : eqType) (l : seq (A * B)) (p : pred A), partition l p = (nil,nil) -> l = nil. 
Proof.
move => A B. elim;ssa. 
move : H0. rewrite /partition. ssa.  move : H0. rifliad.  eauto. move/H. 
tunf_in H1.
rewrite H0 in H1. done. 
Qed. 

Lemma oft_no_coin : forall Ms Ds E P Q C, OFT Ms Ds P E Q C -> is_msg P = false -> C = nil.
Proof. intros. elim : H H0;ssa.
move/negP : H6. move/negP. rewrite negb_or. ssa. 
have : C0 = nil. apply/H3. lia. intros. subst.  
have : C1 = nil. apply/H5. lia. intros. subst.
apply partition_nil in H1. done.
apply H1 in H2. de C0. de C1.
Qed. 

Lemma oft_qType_done : forall Ms Ds E P Q C, OFT Ms Ds P E Q C -> is_msg P = false -> qType_done Q. 
Proof. intros. elim : H H0;ssa.
destruct (is_msg P0) eqn:Heqn. ssa. ssa.
apply H5 in H6.  have : qType_done Q0. eauto. intros. 
inv H0. apply/allP. intro. ssa. 
move : x. rewrite /qType_done.  rewrite /filter_q.  rewrite all_map. ssa.
apply (allP x) in H7 as HH. 
move : H6.
rewrite /qType_done.  rewrite /filter_q.  rewrite all_map. ssa.
apply (allP H6) in H7 as HH'. ssa.
de x0.  clear x H6 H7. move/eqP : HH. move/eqP : HH'. intros. 
elim : l HH HH';ssa. move : HH HH'. tunf. rifliad. 
apply H1 in H2. rewrite /insertQ /insert_shift qType_done_cat in H2. ssa.
move : H4. rewrite /qType_done all_map. ssa.
Qed. 

Lemma accept_not_queue : forall n v P, Accepts n v P ->  is_msg P = false.  
Proof. 
intros. elim : H. ssa. ssa.
Qed. 

Lemma qType_done_eq_nil : forall (Q : q_env), qType_done Q -> Q = map (fun k => (k,nil)) (dom Q).
Proof. 
elim;ssa. norm_eqs. de a. subst. f_equal. auto. 
Qed. 

Lemma filter_keys_op : forall (A B : eqType) (l : seq (A * B)) f, filter_keys f l = nil -> filter_keys (predC f) l = l.
Proof. 
move => A B. elim;ssa.
move : H0. tunf.  rifliad. ssa. f_equal. eauto. 
Qed. 

Lemma partition_right : forall Q Q0 Q1 f,
  partition_q Q f = (Q0,Q1) -> qType_done Q0 -> Q = Q1.
Proof.
ssa. inv H. clear H. elim : Q H0;ssa.
norm_eqs. f_equal. rewrite filter_keys_op. de a. 
done. eauto.
Qed. 

Lemma partition_first : forall Q Q0 Q1 f, qType_done Q ->
  partition_q Q f = (Q0,Q1) -> Q = Q0. 
Proof.
ssa. inv H0. clear H0. intros. rewrite /qType_done in H. ssa. rewrite /filter_q. 
rewrite -{1}(@map_id _ Q). apply/eq_in_map. intro. 
ssa. apply (allP H) in H0.  rewrite (eqP H0). ssa. norm_eqs. de x. ssa. subst. done. 
Qed. 

Lemma qType_done_filter_keys : forall Q f, qType_done Q  -> qType_done (filter_keys f Q).
Proof. 
rewrite /qType_done. 
ssa.  
Qed. 

Lemma env_not_rec_f : forall E f0, env_not_rec E -> env_not_rec (filter_keys f0 E).
Proof. 
move => E f0. rewrite /env_not_rec. ssa. apply/allP. intro. ssa. 
apply in_filter_keys in H0.  ssa.  apply (allP H) in H1. done. 
Qed. 


Lemma balanced_f : forall E Q f, balanced E Q -> balanced (filter_keys f E) Q.
Proof. 
move => E Q f. rewrite /balanced. ssa.  
exists x.  exists x0. ssa.
move : H0. rewrite /balancedL. ssa.
apply lookup_filter2 in H3. ssa.
Qed. 

Lemma partial_balanced_f : forall E Q f, partial_balanced E Q -> partial_balanced (filter_keys f E) Q.
Proof. 
move => E Q f. rewrite /partial_balanced. 
ssa. econ. econ. econ. econ. ssa.
subst. apply/balanced_f. eauto.
subst. done.
Qed. 

Lemma only_schl_f : forall E f, only_schl E -> only_schl (filter_keys f E).
Proof.
move => E f.  rewrite /only_schl. intros. apply/allP. intro. ssa.
rewrite dom_filter_keys in H0. rewrite mem_filter in H0.  ssa.
apply (allP H).  done. 
Qed. 


Lemma match_ch : forall n l, IndexSet n l ->
 list_map ((fun c : ch => (schliT (var_schl 0) c, tt)) \o Ch) l = list_map (pair^~ tt) (make_cs n.+1).
Proof. 
intros. elim : H;ssa.
f_equal.  done. 
Qed. 

Lemma uniq_make_cs : forall n, uniq (make_cs n).
Proof. 
elim;ssa.
clear H. 
suff : forall n', n <= n' -> schliT (var_schl 0) n' \notin make_cs n.
intros. apply/x. done.
elim : n;ssa.
 rewrite inE negb_or. ssa.
apply/eqP. intro. inv H1. lia. 
Qed. 

Lemma filter_keys_update : forall (A B : eqType) (l : seq (A * B)) f k v, filter_keys f (update l k v) = update (filter_keys f l) k v.
Proof. 
move => A B. elim;ssa.
rifliad. norm_eqs. ssa. rewrite eqxx //=. f_equal.  auto. 
ssa. rewrite H1.  f_equal. auto.
move : H0. rifliad.  norm_eqs. ssa. rewrite eqxx //=. rewrite H1 in H0. done.
intros. norm_eqs. simpl. rewrite (negbTE H0). rewrite H1 in H2. done.
Qed. 

Lemma filter_q_update : forall (l : q_env) f k v, filter_q (update l k v) f = update (filter_q l f) k (filter_keys (f k) v).
Proof. 
elim;ssa.
rifliad. norm_eqs. ssa. f_equal. eauto. f_equal.  auto. 
Qed. 

Lemma side_conds_par : forall Ds Ps Ms P0 P1 E Q, side_conds Ds Ps Ms (Par P0 P1) E Q -> side_conds Ds Ps Ms P0 E Q /\ side_conds Ds Ps Ms P1 E Q.
Proof. intros.  inv H. rewrite /side_conds.  ssa.
move : H3. rewrite /sch_closed. intros. ssa. inv H3. con. 
intro. apply/negP. intro. apply/negP. apply H12. rewrite /= mem_cat. apply/orP. eauto.
ssa.
intro. apply/negP. intro. apply/negP. apply H13. rewrite /= mem_cat. apply/orP. eauto.

inv H3. con.
intro. apply/negP. intro. apply/negP. apply H12. rewrite /= mem_cat. apply/orP. eauto.
ssa.
intro. apply/negP. intro. apply/negP. apply H13. rewrite /= mem_cat. apply/orP. eauto.
Qed. 

Lemma update_same : forall (A B : eqType) (E : seq (A * B)) k v, lookup E k = Some v -> uniq (dom E) -> update E k v = E.
Proof. 
move => A B. elim;ssa. 
apply lookup_or in H0. de H0;subst.  rewrite eqxx.  de a. f_equal.  
rewrite /update. 
rewrite -{2}(@map_id _ l). apply/eq_in_map. intro. ssa.
rifliad.  norm_eqs. eapply map_f in H0. erewrite H0 in H2. done.
rewrite (negbTE H0). f_equal.  eauto. 
Qed. 

Lemma update_none : forall (A B : eqType) (E : seq (A * B)) k v, k \notin dom E -> update E k v = E.
Proof. 
move => A B. elim;ssa. rewrite inE in H0. rewrite negb_or in H0.
ssa. rifliad. norm_eqs. f_equal. eauto. 
Qed. 


Lemma uniq_filter_keys : forall (A B : eqType) (E : seq ( A * B)) f, uniq (dom E) -> uniq (dom (filter_keys f E)).
Proof. 
move => A B. elim;ssa.
rifliad.  rewrite /dom //=. ssa. 
apply/negP. intro. apply/negP. apply H1. de (mapP H3). 
apply in_filter_keys in H4. ssa. rewrite H5. apply/map_f.  done. 
eauto.  eauto. 
Qed. 

Lemma qType_done_both : forall Q f, qType_done (filter_q Q f) -> qType_done (filter_q Q (hrelC f)) -> qType_done Q.
Proof. 
rewrite /qType_done. 
rewrite /filter_q.  move => Q f.  rewrite !all_map. ssa. apply/allP. intro. 
ssa. apply (allP H) in H1 as HH.  apply (allP H0) in H1. clear H H0. ssa.
move/eqP : HH. intro.
apply filter_keys_op in HH. rewrite -HH. rewrite H1.  done. 
Qed. 


Lemma filter_q_done : forall Q f, qType_done Q -> filter_q Q f = Q. 
Proof. 
rewrite /qType_done /filter_q.  intros. 
rewrite -{2}(@map_id _ Q). apply/eq_in_map. intro. ssa.
apply (allP H) in H0.  norm_eqs. rewrite H0. ssa. de x.  subst. done. 
Qed. 

Lemma EvalE_pres : forall Ms e v m, EvalE e v -> OFTE Ms e m -> OFTV Ms v m.
Proof. 
intros. elim : H Ms H0;ssa. inv H0. 
inv H4.  econ. 
Qed. 

Lemma in_update : forall (A B : eqType) (l : seq ( A * B)) x (k : A)  v, x \in update l k v -> x = (k,v) \/ x \in l.
Proof. 
move => A B. elim;ssa.
rewrite inE in H0. move : H0. rifliad. norm_eqs. move/orP. case. move/eqP. move=>->. ssa.
intros.  apply H in b. de b.  rewrite H0.  lia. 
move/orP. case. move/eqP. intros. subst.  rewrite inE eqxx. lia. 
move/H. case. ssa. ssa. rewrite b. lia.
Qed. 

Lemma sub_domLQ_f : forall E Q f, sub_domLQ E Q ->  sub_domLQ (filter_keys (predC f) E) Q.
Proof. rewrite /sub_domLQ. ssa. rewrite dom_filter_keys mem_filter in H0. ssa.
Qed. 

Lemma qType_done_nil : forall (Q : q_env) k v, qType_done Q -> lookup Q k = Some v -> v = nil. 
Proof. 
intros. ssa. apply in_pair in H0.  apply (allP H) in H0.  ssa. norm_eqs. done.
Qed. 

Lemma update2 : forall (A B: eqType) (l : seq (A * B)) k v v', update (update l k v) k v' = update l k v'.
Proof. intros. rewrite /update -map_comp.  apply/eq_in_map. intro. ssa. 
de (eqVneq x.1 k).  rewrite e.  rifliad. de x. rifliad. 
Qed. 

Lemma in_filter_q : forall Q k v f, (k,v) \in filter_q Q f -> all (f k) (dom v).
Proof. 
intros. rewrite /filter_q in H.   de (mapP H). subst. inv H1. 
rewrite /dom all_map.  apply/allP. intro. ssa.  apply in_filter_keys in H2. ssa.
Qed. 



Lemma filter_q_eq2 : forall (Q : q_env) (f0 f1 : hrel qkey ch), (forall x y z, (x,y) \in Q -> z \in dom y -> f0 x z = f1 x z) ->
filter_q Q f0 = filter_q Q f1.
Proof. 
intros. rewrite /filter_q. 
apply/eq_in_map. intro. ssa. erewrite filter_keys_eq. eauto. intros.  apply/H. 
instantiate (1 := x.2). de x. done.
Qed. 


Lemma uniq_pair : forall (A B : eqType) (l : seq (A * B)) a b c, uniq (dom l) -> (a,b) \in l -> (a,c) \in l -> b = c. 
Proof. 
move => A B. elim;ssa.
rewrite !inE in H1,H2. de (orP H1). norm_eqs.
de (orP H1). norm_eqs. inv H0.  de (orP H2). norm_eqs. inv  H5. 
eapply (@map_f _ _ fst) in H5. erewrite H5 in H3. done. 
eapply (@map_f _ _ fst) in H0. erewrite H0 in H3. done. 
de (orP H2). norm_eqs.
eapply (@map_f _ _ fst) in H0. erewrite H0 in H3. done. 
eauto.
Qed. 

Definition get_s (P : process) := if P is MsgQ s _ then Some s else None. 

Lemma queue_coin : forall Ms Ds P E Q C s, OFT Ms Ds P E Q C -> get_s P = some s ->  C = [::(s,tt)]. 
Proof. 
intros. elim : H H0;ssa. inv H1. 
Qed. 

Lemma filter_q_none2 : forall Q f, qType_done (filter_q Q f) -> filter_q Q (hrelC f) = Q. 
Proof.
intros.  rewrite filter_q_none.  done. 
move : H. rewrite /predC /hrelC.  intros. erewrite filter_q_eq. eauto. 
ssa. fext. ssa. rewrite negb_involutive. done.
Qed. 

Lemma update_com : forall (A B: eqType) (l : seq (A* B)) k k' v v', k <> k' -> update (update l k v) k' v' = update (update l k' v') k v.
Proof. 
move => A B. intros. rewrite /update -!map_comp. apply/eq_in_map. intro. 
ssa. de (eqVneq x.1 k). rewrite e . 
de (eqVneq k k').  rewrite e. rifliad. 
rifliad.  ssa.  norm_eqs.
Qed. 

Lemma queue_add : forall msgs Ms Ds s i v m p E Q C l, OFT Ms Ds (MsgQ (schliT s i) msgs) E (update Q (QKey s p) l) C ->  OFTV Ms v m -> QKey s p \in dom Q ->
                                                OFT Ms Ds (MsgQ (schliT s i) (msgs ++ [::msgT (valM v) p])) E (update Q (QKey s p) (l ++ [::(i,inl (VSort m))])) C.
Proof. 
elim;ssa. inv H.
have : l = nil. have : (QKey s p,l) \in update Q (QKey s p) l. apply/in_pair.
rewrite lookup_update_in.  done.  done. intros. 
apply (allP H6) in x.  ssa. norm_eqs. done. intros. subst. 
econ;eauto. simpl. rewrite lookup_update_in. econ. done. 
ssa. rewrite update2.  done.
inv H0. 
- de (eqVneq p p0). subst.  rewrite update2 in H14. rewrite lookup_update_in in H13. inv H13. 
  econ. eauto. rewrite lookup_update_in. ssa. done. rewrite update2 //=. 
  apply/H. done.  done.  done.  done. 
  apply lookup_update_neq2 in H13. 
  econ;eauto. erewrite lookup_update_neq. eauto.  eauto. intro. inv H3. rewrite eqxx in i0. done. 
  rewrite update_com.
  apply H. rewrite update_com.  eauto.  intro. inv H3. rewrite eqxx in i0. done. done. 
  rewrite dom_update.  done. intro. inv H3. rewrite eqxx in i0. done. 
  intro. inv H3. rewrite eqxx in i0. done. 

- de (eqVneq p p0). subst.  rewrite update2 in H15. rewrite lookup_update_in in H9. inv H9. 
  econ.   rewrite lookup_update_in. ssa. done. eauto. done. rewrite update2 //=. 
  apply/H. done.  done.  done.  done. 
  apply lookup_update_neq2 in H9. 
  econ;eauto. erewrite lookup_update_neq. eauto.  eauto. intro. inv H3. rewrite eqxx in i0. done. 
  rewrite update_com.
  apply H. rewrite update_com.  eauto.  intro. inv H3. rewrite eqxx in i0. done. done. 
  rewrite dom_update.  done. intro. inv H3. rewrite eqxx in i0. done. 
  intro. inv H3. rewrite eqxx in i0. done. 

- de (eqVneq p p0). subst.  rewrite update2 in H13. rewrite lookup_update_in in H12. inv H12. 
  econ.   rewrite lookup_update_in. ssa. done. rewrite update2 //=. 
  apply/H. done.  done.  done.  done. 
  apply lookup_update_neq2 in H12. 
  econ;eauto. erewrite lookup_update_neq. eauto.  eauto. intro. inv H3. rewrite eqxx in i0. done. 
  rewrite update_com.
  apply H. rewrite update_com.  eauto.  intro. inv H3. rewrite eqxx in i0. done. done. 
  rewrite dom_update.  done. intro. inv H3. rewrite eqxx in i0. done. 
  intro. inv H3. rewrite eqxx in i0. done. 
Qed. 

Lemma queue_add3 : forall msgs Ms Ds s i n p E Q C l, OFT Ms Ds (MsgQ (schliT s i) msgs) E (update Q (QKey s p) l) C ->  
 QKey s p \in dom Q ->
                                                
OFT Ms Ds (MsgQ (schliT s i) (msgs ++ [::msgT (labelM n) p])) E (update Q (QKey s p) (l ++ [::(i,inr n)])) C.
Proof. 
elim;ssa. inv H.
have : l = nil. have : (QKey s p,l) \in update Q (QKey s p) l. apply/in_pair.
rewrite lookup_update_in.  done.  done. intros. 
apply (allP H5) in x.  ssa. norm_eqs. done. intros. subst. 
econ;eauto. simpl. rewrite lookup_update_in. econ. done. 
ssa. rewrite update2.  done.
inv H0. 
- de (eqVneq p p0). subst.  rewrite update2 in H13. rewrite lookup_update_in in H12. inv H12. 
  econ. eauto. rewrite lookup_update_in. ssa. done. rewrite update2 //=. 
  apply/H. done.  done.  done.  
  apply lookup_update_neq2 in H12.  
  econ;eauto. erewrite lookup_update_neq. eauto.  eauto. intro. inv H2. rewrite eqxx in i0. done. 
  rewrite update_com.
  apply H. rewrite update_com.  eauto.  intro. inv H2. rewrite eqxx in i0. done. 
  rewrite dom_update.  done. intro. inv H2. rewrite eqxx in i0. done. 
  intro. inv H2. rewrite eqxx in i0. done. 

- de (eqVneq p p0). subst.  rewrite update2 in H14. rewrite lookup_update_in in H8. inv H8. 
  econ.   rewrite lookup_update_in. ssa. done. eauto. done. rewrite update2 //=. 
  apply/H. done.  done.  done.  
  apply lookup_update_neq2 in H8. 
  econ;eauto. erewrite lookup_update_neq. eauto.  eauto. intro. inv H2. rewrite eqxx in i0. done. 
  rewrite update_com.
  apply H. rewrite update_com.  eauto.  intro. inv H2. rewrite eqxx in i0. done. 
  rewrite dom_update.  done. intro. inv H2. rewrite eqxx in i0. done. 
  intro. inv H2. rewrite eqxx in i0. done. 

- de (eqVneq p p0). subst.  rewrite update2 in H12. rewrite lookup_update_in in H11. inv H11. 
  econ.   rewrite lookup_update_in. ssa. done. rewrite update2 //=. 
  apply/H. done.  done.  done.  
  apply lookup_update_neq2 in H11. 
  econ;eauto. erewrite lookup_update_neq. eauto.  eauto. intro. inv H2. rewrite eqxx in i0. done. 
  rewrite update_com.
  apply H. rewrite update_com.  eauto.  intro. inv H2. rewrite eqxx in i0. done. 
  rewrite dom_update.  done. intro. inv H2. rewrite eqxx in i0. done. 
  intro. inv H2. rewrite eqxx in i0. done. 
Qed. 



Definition lookupT (A B : eqType) (l : seq ( A* B)) (a : A) (d : B) : B := if lookup l a is Some b then b else d. 

Fixpoint gfind (g : gType) (k : ch) (d : dir) (p : ptcp) (n : value + nat) := 
match g with 
| GMsg a u' g' => if (action_ch a == k) && (comp_dir p a == Some d) then g' else gfind g' k d p n
| GBranch a gs => if (action_ch a == k) && (comp_dir p a == Some d) then if n is inr n' then lookupT gs n GEnd else GEnd
                                                                        else nth GEnd (map (snd >> (fun g'' => gfind g'' k d p n)) gs) 0
| GRec g' => (gfind g' k d p n)[g GRec g' .: GVar]
| _ => g
end. 

Require Import MPSTSR.linearity. 

Lemma can_stepP'2 : forall g p0 p1 c vn vn', can_step (Sd,c,vn) (trans p0 g)  -> can_step (Rd,c,vn') (trans p1 g) -> action_pred g /\ size_pred g -> p0 <> p1.
Proof. 
elim;intros. ssa'. ssa'. ssa'. 
move : H0. case_if;try done.  move : H1. case_if;try done. eauto. 
- ssa'. move => HH. subst. destruct (comp_dir  p1 a) eqn:Heqn. 
 * move : H0. simpl. move/orP. case. 
  ** move/eqP. case. intros. subst. subst_comp. move : H1. simpl. rewrite eqxx //=. 
  ** ssa'. move/eqP : H6;intros;subst. subst_comp. ssa'. apply/H;eauto. 
     move : Heqn. rewrite /comp_dir. rifliad. move => _. apply/H;eauto.
- ssa'. move => HH. subst. destruct (comp_dir  p1 a) eqn:Heqn. 
 * move : H0. simpl. move/orP. case. 
  ** destruct vn;try done.  ssa'. move/eqP : H0.  case. intros. subst. subst_comp. move : H1. simpl. rewrite eqxx //=. 
  ** rewrite orbC //=. de vn'. ssa'. move/eqP : H7;intros;subst. subst_comp. ssa'. 
     move : H1. destruct vn';ssa. simpl. ssa'. destruct l;try done.  destruct p. ssa'. apply/H. rewrite inE. apply/orP.  eauto.
     
eauto. eauto. ssa'. ssa'.

     destruct l;try done. destruct p. ssa'. apply/H. simpl. ssa'. apply/orP. left. eauto. eauto. eauto. ssa'. ssa'.
     destruct l;try done.   ssa'. destruct p. ssa'. apply/H. rewrite inE. apply/orP. eauto. eauto. eauto. ssa'. done.
Qed. 



Lemma can_stepP_values : forall g p0 p1 c vn vn', can_gstep2 (Sd,c,vn) p0 g  -> can_gstep2 (Rd,c,vn') p1 g -> action_pred g /\ size_pred g /\ Linear g -> can_gstep (Action p0 p1 c,vn) g.
Proof. 
elim;intros. ssa'. ssa'. 
ssa'. apply/H;eauto. ssa'.   apply linear_unf in H4. apply/Linear_subst.  eauto. 

have : p0 <> p1. apply/can_stepP'2. apply can_gstep2P. eauto. ssa'. apply can_gstep2P. eauto. ssa'. ssa'. 
intros. ssa'. destruct (orP H0),(orP H1).
- move/eqP : H6. move/eqP : H7. rewrite /to_elabel.
  destruct (comp_dir p1 a) eqn:Heqn;try done. 
  destruct (comp_dir p0 a) eqn:Heqn2;try done. case. intros. invc H9. rewrite pack_act eqxx //=.  
- ssa'. apply can_gstep2P in H9. apply estep_tr2 in H9;eauto. destruct H9,H8. ssa'. 
  move/eqP : H6. rewrite /to_elabel. destruct (comp_dir p0 a) eqn:Heqn. case. intros. subst. subst_comp. 
  have :  Tr ((a::x0) ++ [:: Action x1 p1 (action_ch a)]) (GMsg a v g). simpl. by con;done. clear H0. 
  ssa'. rewrite /Linear in H3. 
  move : (@H3 nil a x0 (Action x1 p1 (action_ch a))). simpl. move/(_ x2)=>//=.  rewrite /same_ch /= eqxx.
  move/(_ is_true_true). ssa'.  apply exists_dep_in in H0. destruct H0. ssa'. rewrite inE in H0. 
  destruct (orP H0). move/eqP : H12. intros. subst. rewrite eqxx //= in H7. 
  apply H9 in H12. subst. done. done. done. 
- ssa'. apply can_gstep2P in H9;try done. apply estep_tr1 in H9;eauto. destruct H9,H8. ssa'. 
  move/eqP : H7. rewrite /to_elabel. destruct (comp_dir p1 a) eqn:Heqn. case. intros. subst. subst_comp. 
  have :  Tr ((a::x0) ++ [:: Action p0 x1 (action_ch a)]) (GMsg a v g). simpl.
  con. done. clear H0. 
  ssa'. rewrite /Linear in H3. 
  move : (@H3 nil a x0 (Action p0 x1 (action_ch a))). simpl. move/(_ x2)=>//=.  rewrite /same_ch /= eqxx.
  move/(_ is_true_true). ssa'.  apply exists_dep_out in H7. destruct H7. ssa'. rewrite inE in H7. 
  destruct (orP H7). move/eqP : H12. intros. subst. rewrite eqxx //= in H7. 
  apply H9 in H12. subst. done. apply/negP. move => HH. apply/negP. move/implyP: H10. intros. apply/H10. done. done. done. 
- ssa'. apply/orP. right. rewrite negb_or. ssa'. apply/H. done. eauto. ssa'. apply/linear_sgmsg. eauto.



have : p0 <> p1. apply/can_stepP'2. apply can_gstep2P. eauto. ssa'. apply can_gstep2P. eauto. ssa'. ssa'. 
intros. ssa'. destruct (orP H0),(orP H1).
- ssa'.  move/eqP : H9. move/eqP : H8. rewrite /to_elabel.
  destruct (comp_dir p0 a) eqn:Heqn;try done. 
  destruct (comp_dir p1 a) eqn:Heqn2;try done. case. intros. invc H9. rewrite pack_act eqxx //=.  rewrite H11 //= .
- ssa'. have : (nth (0,GEnd) l 0 \in l). apply/mem_nth. done. move => Hin. apply (allP H10) in Hin. apply can_gstep2P in Hin. apply estep_tr2 in Hin;eauto. 
  destruct Hin,H2. ssa'. 
  move/eqP : H9. rewrite /to_elabel. destruct (comp_dir p0 a) eqn:Heqn. case. intros. subst. subst_comp. 
  have :  Tr ((a::x0) ++ [:: Action x1 p1 (action_ch a)]) (GBranch a l). simpl.



  destruct l. ssa'. destruct p. ssa'. econ. eauto. done.
  move : (@H3 nil a x0 (Action x1 p1 (action_ch a)))=>//=.
 intros. apply H9 in x2. ssa'.  apply exists_dep_in in H14. destruct H14.  ssa'. 
 rewrite inE in H14. destruct (orP H14). move/eqP : H17. intros. subst. rewrite eqxx //=.  
  destruct vn . ssa'. apply/orP. left. rewrite pack_act. ssa'. 
  apply H13 in H16.  done. subst. done. rewrite /same_ch. simpl. done. done. ssa'. destruct l. ssa'. ssa'. destruct l. ssa'. ssa'. destruct l. ssa'. ssa'. 
- ssa'. have : (nth (0,GEnd) l 0 \in l). apply/mem_nth. done. move => Hin. apply (allP H11) in Hin. apply can_gstep2P in Hin. apply estep_tr1 in Hin;eauto. 
  destruct Hin,H8. ssa'. 
  move/eqP : H9. rewrite /to_elabel. destruct (comp_dir p1 a) eqn:Heqn. case. intros. subst. subst_comp. 
  have :  Tr ((a::x0) ++ [:: Action p0 x1 (action_ch a)]) (GBranch a l). simpl. destruct l. done.  destruct p. econstructor. eauto. eauto. 
  ssa'. rewrite /Linear in H3. 
  move : (@H3 nil a x0 (Action p0 x1 (action_ch a))). simpl. move/(_ x2)=>//=.  rewrite /same_ch /= eqxx.
  move/(_ is_true_true). ssa'.  apply exists_dep_out in H14. destruct H14. ssa'. rewrite inE in H14. 
  destruct (orP H14). move/eqP : H16. intros. subst. rewrite eqxx //= in H2. 
  apply H13 in H16. subst. done. apply/negP. move => HH. apply/negP. move/implyP: H12. intros. apply/H12. done. done. done. ssa'.
  apply (allP H5). apply/mem_nth. done. apply (allP H7). apply/mem_nth. done. 
  apply (allP H7). apply/mem_nth. done. 
- ssa'. apply/orP. right. rewrite negb_or. ssa'. apply/allP. move => x' xIn. destruct l. ssa'. destruct p. ssa'. 
  rewrite inE in xIn.  destruct (orP xIn). rewrite (eqP H5).  ssa'. apply/H. eauto. done. eauto. ssa'. 
  eapply linear_branch_aux in H3. move/ForallP : H3. intros. 
  have : g = (n,g).2. done. move=>->. apply/H3. simpl.   auto. 
  apply/H. instantiate (1:= x'.1). rewrite inE. apply/orP. right. destruct x'.   eauto. 


  apply (allP H14). done. apply (allP H15). done. ssa'. apply (allP H17). done. apply (allP H16). done.
  apply/linear_branch. eauto.  done. 
Qed. 

Lemma can_stepP_values2 : forall g p0 p1 c vn vn', can_gstep2 (Sd,c,vn) p0 g  -> can_gstep2 (Rd,c,vn') p1 g -> action_pred g /\ size_pred g /\ Linear g -> can_gstep (Action p0 p1 c,vn') g.
Proof. 
elim;intros. ssa'. ssa'. 
ssa'. apply/H;eauto. ssa'.   apply linear_unf in H4. apply/Linear_subst.  eauto. 

have : p0 <> p1. apply/can_stepP'2. apply can_gstep2P. eauto. ssa'. apply can_gstep2P. eauto. ssa'. ssa'. 
intros. ssa'. destruct (orP H0),(orP H1).
- move/eqP : H6. move/eqP : H7. rewrite /to_elabel.
  destruct (comp_dir p1 a) eqn:Heqn;try done. 
  destruct (comp_dir p0 a) eqn:Heqn2;try done. case. intros. invc H9. rewrite pack_act eqxx //=.  
- ssa'. apply can_gstep2P in H9. apply estep_tr2 in H9;eauto. destruct H9,H8. ssa'. 
  move/eqP : H6. rewrite /to_elabel. destruct (comp_dir p0 a) eqn:Heqn. case. intros. subst. subst_comp. 
  have :  Tr ((a::x0) ++ [:: Action x1 p1 (action_ch a)]) (GMsg a v g). simpl. by con;done. clear H0. 
  ssa'. rewrite /Linear in H3. 
  move : (@H3 nil a x0 (Action x1 p1 (action_ch a))). simpl. move/(_ x2)=>//=.  rewrite /same_ch /= eqxx.
  move/(_ is_true_true). ssa'.  apply exists_dep_in in H0. destruct H0. ssa'. rewrite inE in H0. 
  destruct (orP H0). move/eqP : H12. intros. subst. rewrite eqxx //= in H7. 
  apply H9 in H12. subst. done. done. done. 
- ssa'. apply can_gstep2P in H9;try done. apply estep_tr1 in H9;eauto. destruct H9,H8. ssa'. 
  move/eqP : H7. rewrite /to_elabel. destruct (comp_dir p1 a) eqn:Heqn. case. intros. subst. subst_comp. 
  have :  Tr ((a::x0) ++ [:: Action p0 x1 (action_ch a)]) (GMsg a v g). simpl.
  con. done. clear H0. 
  ssa'. rewrite /Linear in H3. 
  move : (@H3 nil a x0 (Action p0 x1 (action_ch a))). simpl. move/(_ x2)=>//=.  rewrite /same_ch /= eqxx.
  move/(_ is_true_true). ssa'.  apply exists_dep_out in H7. destruct H7. ssa'. rewrite inE in H7. 
  destruct (orP H7). move/eqP : H12. intros. subst. rewrite eqxx //= in H7. 
  apply H9 in H12. subst. done. apply/negP. move => HH. apply/negP. move/implyP: H10. intros. apply/H10. done. done. done. 
- ssa'. apply/orP. right. rewrite negb_or. ssa'. apply/H. eauto. done. eauto. ssa'. apply/linear_sgmsg. eauto.



have : p0 <> p1. apply/can_stepP'2. apply can_gstep2P. eauto. ssa'. apply can_gstep2P. eauto. ssa'. ssa'. 
intros. ssa'. destruct (orP H0),(orP H1).
- ssa'.  move/eqP : H9. move/eqP : H8. rewrite /to_elabel.
  destruct (comp_dir p0 a) eqn:Heqn;try done. 
  destruct (comp_dir p1 a) eqn:Heqn2;try done. case. intros. invc H9. rewrite pack_act eqxx //=.  rewrite H10 //= .
- ssa'. have : (nth (0,GEnd) l 0 \in l). apply/mem_nth. done. move => Hin. apply (allP H10) in Hin. apply can_gstep2P in Hin. apply estep_tr2 in Hin;eauto. 
  destruct Hin,H2. ssa'. 
  move/eqP : H9. rewrite /to_elabel. destruct (comp_dir p0 a) eqn:Heqn. case. intros. subst. subst_comp. 
  have :  Tr ((a::x0) ++ [:: Action x1 p1 (action_ch a)]) (GBranch a l). simpl.



  destruct l. ssa'. destruct p. ssa'. econ. eauto. done.
  move : (@H3 nil a x0 (Action x1 p1 (action_ch a)))=>//=.
 intros. apply H9 in x2. ssa'.  apply exists_dep_in in H14. destruct H14.  ssa'. 
 rewrite inE in H14. destruct (orP H14). move/eqP : H17. intros. subst. rewrite eqxx //= in H8.  
  destruct vn' . simpl. subst. ssa'. rewrite negb_or. ssa. rewrite neg_sym //=. 

  apply H13 in H17. done. apply H13 in H17. subst. done.

rewrite /same_ch. simpl. done. done. ssa'. destruct l. ssa'. ssa'. destruct l. ssa'. ssa'. destruct l. ssa'. ssa'. 
- ssa'. have : (nth (0,GEnd) l 0 \in l). apply/mem_nth. done. move => Hin. apply (allP H11) in Hin. apply can_gstep2P in Hin. apply estep_tr1 in Hin;eauto. 
  destruct Hin,H8. ssa'. 
  move/eqP : H9. rewrite /to_elabel. destruct (comp_dir p1 a) eqn:Heqn. case. intros. subst. subst_comp. 
  have :  Tr ((a::x0) ++ [:: Action p0 x1 (action_ch a)]) (GBranch a l). simpl. destruct l. done.  destruct p. econstructor. eauto. eauto. 
  ssa'. rewrite /Linear in H3. 
  move : (@H3 nil a x0 (Action p0 x1 (action_ch a))). simpl. move/(_ x2)=>//=.  rewrite /same_ch /= eqxx.
  move/(_ is_true_true). ssa'.  apply exists_dep_out in H14. destruct H14. ssa'. rewrite inE in H14. 
  destruct (orP H14). move/eqP : H16. intros. subst. rewrite eqxx //= in H2. 
  apply H13 in H16. subst. done. apply/negP. move => HH. apply/negP. move/implyP: H12. intros. apply/H12. done. done. done. ssa'.
  apply (allP H5). apply/mem_nth. done. apply (allP H7). apply/mem_nth. done. 
  apply (allP H7). apply/mem_nth. done. 
- ssa'. apply/orP. right. rewrite negb_or. ssa'. apply/allP. move => x' xIn. destruct l. ssa'. destruct p. ssa'. 
  rewrite inE in xIn.  destruct (orP xIn). rewrite (eqP H5).  ssa'. apply/H. eauto. eauto. done. ssa'. 
  eapply linear_branch_aux in H3. move/ForallP : H3. intros. 
  have : g = (n,g).2. done. move=>->. apply/H3. simpl.   auto. 
  apply/H. instantiate (1:= x'.1). rewrite inE. apply/orP. right. destruct x'.   eauto. 


  apply (allP H14). done. apply (allP H15). done. ssa'. apply (allP H17). done. apply (allP H16). done.
  apply/linear_branch. eauto.  done. 
Qed. 

Lemma can_gstep_uniq : forall g a u u', can_gstep (a,inl u) g -> can_gstep (a,inl u') g -> size_pred g -> u = u'.
Proof. 
elim;ssa. eauto. 
de (orP H0). norm_eqs. inv H3. 
de (orP H1). norm_eqs. inv H4. rewrite inE negb_or in H5. ssa. rewrite inE eqxx //= in H7.
de (orP H1). norm_eqs. inv H3. rewrite inE negb_or in H4. ssa. rewrite inE eqxx //= in H7.
eauto. 
de l. de p. eapply H. done.  eauto. eauto. done. 
Qed.

Lemma can_stepP_values_eq : forall g p0 p1 c u u', can_gstep2 (Sd,c,inl u) p0 g  -> can_gstep2 (Rd,c,inl u') p1 g -> action_pred g /\ size_pred g /\ Linear g -> u = u'.  
Proof. 
intros. apply/can_gstep_uniq;eauto.
apply/can_stepP_values. eauto. eauto. ssa.
apply/can_stepP_values2. eauto. eauto. ssa. ssa.
Qed. 



Lemma is_var_is_var_val Ms : only_var_val Ms  ->all is_var (dom Ms).
Proof.
intros. apply/allP. intro.  intro. apply (allP H) in H0. de x.
Qed.
Hint Resolve is_var_is_var_val.

Definition is_bool (v : valBool) := 
match v with 
| boolB _ => true 
| _ => false 
end.





