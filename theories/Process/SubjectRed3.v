
From mathcomp Require Import all_ssreflect zify.
Require Import MPSTSR.Projection.intermediateProj MPSTSR.Projection.projectDecide MPSTSR.Projection.indProj. 
Require Import MPSTSR.CoTypes.coLocal. 

From Paco Require Import paco.
Require Import MPSTSR.IndTypes.elimination.
Require Import MPSTSR.harmony. 

Require Import MPSTSR.Process.processSyntax.
Require Import MPSTSR.Process.env. 
Require Import MPSTSR.Process.preds.
Require Export MPSTSR.Process.SubjectRed2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma qType_done_false : forall (Q : q_env) lk l c v, qType_done Q -> lookup Q lk = Some l -> (c,v) \in l -> False.
Proof.
intros. apply in_pair in H0. apply (allP H) in H0. ssa. norm_eqs. done.
Qed.

Lemma qType_done_false2 : forall (Q : q_env) lk l l' c v, qType_done Q -> lookup Q lk = Some (l++(c,v)::l') ->  False.
Proof.
intros. 
have : (c,v) \in  (l ++ (c, v) :: l'). rewrite mem_cat inE eqxx orbC //=. intros. apply/qType_done_false;eauto.
Qed.

Hint Resolve qType_done_false qType_done_false2.

Lemma msg_coin : forall msgs Ms Ds E Q C s i, OFT Ms Ds (MsgQ (schliT s i) msgs) E Q C -> schliT s i \in dom C.
Proof.
elim;ssa. inv H. ssa.
inv H0;ssa. eauto. eauto. eauto.
Qed.

Lemma msg_Q_entries : forall msgs Ms Ds E Q C s i p l, OFT Ms Ds (MsgQ (schliT s i) msgs) E Q C -> lookup Q (QKey s p) = Some l -> all (fun x => x.1== i )l.
Proof.
elim;ssa. inv H. apply in_pair in H0. apply (allP H5) in H0. norm_eqs. ssa. subst. done.
inv H0;ssa. 
destruct (eqVneq p p0). subst. rewrite H1 in H12.
inv H12. ssa. 
eapply H in H13. 2:{  erewrite lookup_update_in. eauto. apply in_dom in H1. done. } 
done. 
eapply H. eauto. rewrite lookup_update_neq2. eauto. apply/eqP. intro. inv H2.
rewrite eqxx in i0. done.

destruct (eqVneq p p0). subst. rewrite H1 in H8.
inv H8. ssa. 
eapply H in H14. 2:{  erewrite lookup_update_in. eauto. apply in_dom in H1. done. } 
done. 
eapply H. eauto. rewrite lookup_update_neq2. eauto. apply/eqP. intro. inv H2.
rewrite eqxx in i0. done.

destruct (eqVneq p p0). subst. rewrite H1 in H11.
inv H11. ssa. 
eapply H in H12. 2:{  erewrite lookup_update_in. eauto. apply in_dom in H1. done. } 
done. 
eapply H. eauto. rewrite lookup_update_neq2. eauto. apply/eqP. intro. inv H2.
rewrite eqxx in i0. done.
Qed.




Lemma has_coin : forall Ms Ds P E Q C, OFT Ms Ds P E Q C -> forall s p l c v, lookup Q (QKey s p) = Some l -> (c,v) \in l -> schliT s c \in dom C.
Proof.
move => Ms Ds P E Q C.
elim;try solve [intros; ssa; eauto].
- intros. ssa.  inv H0.  inv H1.
  destruct (f1 (QKey s p) c) eqn:Heqn.
  suff:  schliT s c \in dom (filter_keys f2 C2).
  rewrite dom_filter_keys mem_filter. ssa.
  apply/H3. eapply lookup_filter_q. eauto. econ.
  apply/in_filter_keys2. eauto. ssa.
  suff: schliT s c \in dom (filter_keys (predC f2) C2).
  rewrite dom_filter_keys mem_filter. ssa.
  apply/H5. eapply lookup_filter_q. eauto. econ.
  apply/in_filter_keys2. eauto. ssa. tunf. rewrite Heqn //.
- intros.  
  destruct (eqVneq (QKey s p) (QKey s0 p0)). inv e. 
  rewrite H0 in H3. inv H3. rewrite inE in H4. de (orP H4). norm_eqs. inv H5.
  apply msg_coin in H1. done.  eapply H2. 
  erewrite lookup_update_in. eauto.
  apply in_dom in H0. done. eauto.
  apply/H2. rewrite lookup_update_neq2. eauto. done. eauto.
- intros.  
  destruct (eqVneq (QKey s p) (QKey s0 p0)). inv e. 
  rewrite H in H4. inv H4. rewrite inE in H5. de (orP H5). norm_eqs. inv H6.
  apply msg_coin in H2. done. eapply H3. 
  erewrite lookup_update_in. eauto.
  apply in_dom in H. done. eauto.
  apply/H3. rewrite lookup_update_neq2. eauto. done. eauto.
- intros.  
  destruct (eqVneq (QKey s p) (QKey s0 p0)). inv e. 
  rewrite H in H2. inv H2. rewrite inE in H3. de (orP H3). norm_eqs. inv H4.
  apply msg_coin in H0. done. eapply H1. 
  erewrite lookup_update_in. eauto.
  apply in_dom in H. done. eauto.
  apply/H1. rewrite lookup_update_neq2. eauto. done. eauto.
- intros.  
  suff :  shiftC (schliT s c) \in dom (insertC C0 C1).
  rewrite /insertC /insert_shift /insert /=.
  rewrite /dom map_cat mem_cat. move/orP. case.
  move/mapP. case. ssa. de s.  de (mapP p0). subst. de x0.
  asimpl. move/mapP. case. ssa. de s. de x. asimpl in q. inv q.
  apply in_map_keys in p0. ssa.
  apply/mapP. econ. eauto.  ssa.
  apply/H1. 2:eauto.
  instantiate (1:= p ).  asimpl. de s. asimpl.
  rewrite lookup_insertQ_succ. done.
Qed.

Lemma has_coin_not : forall Ms Ds P E Q C, OFT Ms Ds P E Q C -> forall s p l c v, lookup Q (QKey s p) = Some l ->  schliT s c \notin dom C ->  (c,v) \notin l.
Proof.
intros. apply/negP. intro. apply/negP. apply/H1. apply/has_coin; eauto.
Qed.

Lemma uniq_dom_insertQ : forall Q0 Q1, uniq (dom Q0) -> uniq (dom Q1) ->   uniq (dom (insertQ Q0 Q1)).
Proof.
intros. rewrite dom_insertQ. rewrite cat_uniq. ssa.
rewrite map_inj_uniq //. intro. ssa. inv H1.
apply/hasPn. intro. ssa. 
rewrite dom_map_keys in H1. de (mapP H1). subst.
apply/negP. intro. de (mapP H3). de x0. de s.
rewrite dom_map_keys.
rewrite map_inj_uniq. done. done.
Qed.
Hint Resolve uniq_dom_insertQ.
 
Lemma OFT_msg_front : forall Ms Ds P E Q C, OFT Ms Ds P E Q C -> forall s p l c v l',  all (fun x => x.1 != c )l-> lookup Q (QKey s p) = Some (l ++ (c,v)::l') -> uniq (dom Q) -> OFT Ms Ds P E (update Q (QKey s p) ((c,v)::l++l')) C.
Proof. 
move=> Ms Ds P E Q C.
elim;try solve [intros; ssa;exfalso; eauto].
- intros. move : H8 => Hun. move : H6 H7 =>Hall H6. inv H. inv H0. inv H1.
  destruct (f1 (QKey s p) c) eqn:Heqn.
 * eapply lookup_filter_q in H6 as HH.
  move: HH. instantiate (2:= f1). 2:econ. rewrite filter_keys_cat.
  simpl. rewrite Heqn.
  econ. 4: {  apply H3. 2: apply HH. rewrite /filter_keys all_filter.
              apply/allP. intro. ssa. apply/implyP. intro. apply (allP Hall) in H7. done. 
              rewrite dom_filter_q //.
} econ.
   rewrite /partition_q. f_equal.
   rewrite filter_q_update. instantiate (1:= f1). 
   rewrite /= Heqn. 
   rewrite filter_keys_cat //. econ.
   have :  (filter_q Q2 (hrelC f1)) =   (filter_q (update Q2 (QKey s p) ((c, v) :: l ++ l')) (hrelC f1)). 
   rewrite filter_q_update.
   simpl. have : hrelC f1 (QKey s p) c = false.
   rewrite /hrelC Heqn //=. move=>->. rewrite filter_keys_cat.
   rewrite update_same. done. eapply lookup_filter_q. eauto.
   rewrite filter_keys_cat /=. 
   have : hrelC f1 (QKey s p) c = false. 
   rewrite /hrelC Heqn //=. move=>->//. rewrite dom_filter_q //=. 
   move=><-. done.
 *
 eapply lookup_filter_q in H6 as HH. move: HH. instantiate (2:= hrelC f1). 2:econ. rewrite filter_keys_cat.
 simpl. have: hrelC f1 (QKey s p) c = true. tunf. rewrite Heqn //. move=>->.
 
 


 econ. 5: {  apply H5. 2: apply HH. rewrite /filter_keys all_filter.
              apply/allP. intro. ssa. apply/implyP. intro. apply (allP Hall) in H7. done. 
             rewrite dom_filter_q //.
} 
     econ. 
   rewrite /partition_q. instantiate (2:= f1).
 f_equal.
   rewrite filter_q_update. simpl.
 simpl. have: hrelC f1 (QKey s p) c = true. tunf. rewrite Heqn //. move=>->.
   rewrite filter_keys_cat //. econ.
   have :  (filter_q Q2 (f1)) =   (filter_q (update Q2 (QKey s p) ((c, v) :: l ++ l')) (f1)). 
   rewrite filter_q_update.
   simpl. have : f1 (QKey s p) c = false.
   rewrite /hrelC Heqn //=. move=>->. rewrite filter_keys_cat.
   rewrite update_same. done. eapply lookup_filter_q. eauto.
   rewrite filter_keys_cat /=. 
   have : f1 (QKey s p) c = false. 
   rewrite /hrelC Heqn //=. move=>->//. rewrite dom_filter_q //=.
   move=><-. done.

- intros. econ. eauto. eauto.
- intros. move: H5 => Hun. move : H3 H4 => Hall H3.
  destruct (eqVneq (QKey s p) (QKey s0 p0)). 
 * inv e.
   rewrite H0 in H3. inv H3.
   de l0. 
  ** inv H5. econ. eauto. rewrite lookup_update_in. done.  apply in_dom in H0. done. 
     rewrite update2. done.
  ** inv H5. ssa. 
     have: OFT Ms0 Ds0 (MsgQ (schliT s0 i) ((msgT (valM v) p0)::msgs)) E0 Q0 C0. eauto.
     intros.  clear x.
     eapply msg_Q_entries in H1. 2: {  erewrite lookup_update_in. eauto. apply in_dom in H0. done. } 
                               ssa.
     rewrite all_cat in H1. ssa. norm_eqs.
    
 * econ. eauto. rewrite lookup_update_neq2. eauto. apply/eqP. intro. inv H4. rewrite eqxx in i0. done.
   rewrite update_com. 
   apply H2. ssa. rewrite lookup_update_neq2. done. done. rewrite dom_update //.
   apply/eqP. rewrite neg_sym //.

- intros. move : H6 => Hun. move : H4 H5 => Hall H4.
  destruct (eqVneq (QKey s p) (QKey s0 p0)). 
 * inv e.
   rewrite H in H4. inv H4.
   de l0. 
  ** inv H6. econ. eauto. rewrite lookup_update_in. done.  apply in_dom in H. done. eauto. done.
     rewrite update2. done.
  ** inv H6. ssa. 
     eapply msg_Q_entries in H2. 2: {  erewrite lookup_update_in. eauto. apply in_dom in H. done. } 
                               ssa.
     rewrite all_cat in H2. ssa. norm_eqs.
    
 * econ. eauto. rewrite lookup_update_neq2. eauto. apply/eqP. intro. inv H5. rewrite eqxx in i0. done.
   eauto. done.
   rewrite update_com. 
   apply H3. ssa. rewrite lookup_update_neq2. done. done. rewrite dom_update //.  apply/eqP. rewrite neg_sym //.
- intros. move : H4 => Hun.  move : H2 H3 => Hall H4.
  destruct (eqVneq (QKey s p) (QKey s0 p0)). 
 * inv e.
   rewrite H in H4. inv H4.
   de l0. 
  ** inv H3. econ. eauto. rewrite lookup_update_in. done.  apply in_dom in H. done. 
     rewrite update2. done.
  ** inv H3. ssa. 
     eapply msg_Q_entries in H0. 2: {  erewrite lookup_update_in. eauto. apply in_dom in H. done. } 
                               ssa.
     rewrite all_cat in H0. ssa. norm_eqs.
    
 * econ. eauto. rewrite lookup_update_neq2. eauto. apply/eqP. intro. inv H2. rewrite eqxx in i0. done.
   rewrite update_com. 
   apply H1. ssa. rewrite lookup_update_neq2. done. done. 
   rewrite dom_update //.
   apply/eqP. rewrite neg_sym //.

- intros. econ. eauto.  
  instantiate (1:= C1). de s. 
  rewrite -update_insertQ_succ.
  apply /H1. done. rewrite lookup_insertQ_succ. done.
  apply uniq_dom_insertQ. done.
  inv H. ssa. inv H7. inv H5. ssa. subst.
  rewrite /dom /makeQs -!map_comp.
  rewrite map_inj_uniq.  done.
  intro. ssa. inv H9.
Qed.  



Lemma envP_filter : forall (A B : eqType) (E : seq (A * B))  (P : B -> Prop) f, envP E P -> envP (filter_keys f E) P.
Proof.
intro. ssa. intro. ssa. apply lookup_filter2 in H0. ssa. eauto.
Qed.
Hint Resolve envP_filter.

Lemma makeL_uniq : forall p l, checkPath p l -> uniq_labels l -> uniq_labels (makeL p l).
Proof.
elim;ssa.
apply uniq_full_unf. done.
de a. destruct (fe _) eqn:Heqn;ssa. destruct (lookup _ _) eqn:Heqn2;ssa.
apply in_pair in Heqn2. 
apply uniq_full_unf in H1. rewrite Heqn in H1. ssa. apply (allP H4) in Heqn2. ssa.
destruct (fe _) eqn:Heqn2;ssa.
apply H. done. apply uniq_full_unf in H1. rewrite Heqn2 in H1. ssa.
Qed.


Inductive Estep3 : lType -> elabel -> lType -> Prop :=
| estep3_msg d c v e0  : Estep3 (EMsg d c v e0) (d,c, inl v) (fe e0)
| estep3_branch n e es d c   : (n,e) \in es -> 
                              Estep3 (EBranch d c es) (d,c, inr n) (fe e).



Lemma Estep_makeL :  forall e l e', Estep e l e' -> l.1.1 = Rd -> forall s e2, checkPath s e -> uniq_labels e ->  Estep2 (makeL s e) l e2 ->  Estep3 (makeL s e) l (makeL s e').
Proof.
move=> e l e'. elim;ssa.
- de s. subst. inv H1.  econ.
- de o. rewrite /obs in H2;ssa. de d.
- move : H4 H5 => Hun H4.
  de s.  ssa. inv H4.
  rewrite /obs /nexte_wrap in H4 H6;ssa. de o. eauto.
  move : H3 H4 H5 => H2 Hun Hall.
  subst. de s;ssa. 
  inv H2. econ. done.
  de s. subst. 
  move : H6 H7 H8 => H5 Hun Hall.
  inv H5.
  rewrite /obs /nexte_wrap in H5 H6 H7;ssa. de o. 
  destruct (lookup _ _) eqn:Heqn;ssa. 
  apply in_pair in Heqn. have : size es0 = size es1. eauto. move=>Hsize.
  move/in_zip1 : Heqn. move/(_ _ _ Hsize). ssa. de x.
  apply same_label in H10 as Hn. subst.
  move/inP : (H10). move/H1. move/(_ Logic.eq_refl). move=> /= HH.
  apply uniq_in_pair in H4 as HH2. rewrite HH2. apply : HH;eauto. 
  apply mem_zip in H10. ssa.
  apply (allP H8) in H3. done. rewrite /dom -H. done. done. done.

  rewrite makeL_fe2. rewrite full_eunf_subst -makeL_fe2. apply: H0. done.
  apply checkPath_fe in H2. rewrite full_eunf_subst in H2. apply checkPath_fe2 in H2. eauto.
  rewrite uniq_labels_subst;ssa. case: n;ssa. 
  rewrite makeL_fe2 in H4. rewrite full_eunf_subst -makeL_fe2 in H4. eauto. 
Qed.

Lemma Estep23 : forall e l e' e'', Estep2 e l e' -> Estep3 e l e'' -> lInvPred e -> uniq_labels e ->  EQ2 e' e''.
Proof. intros. inv H. inv H0. apply:EQ2_eunf2. apply:EQ2_refl. punfold H1. inv H1. inv H3. de H5.
inv H0. apply uniq_in_pair in H3, H9;ssa. rewrite H3 in H9. inv H9. apply:EQ2_eunf2. apply:EQ2_refl. 
punfold H1. inv H1. inv H2. apply in_pair in H3. move/ForallP : H7. move=>HH. move/inP : H3. move/HH.
case;ssa.
Qed.




Lemma check_makeL : forall s e e', checkPath s e -> EQ2 e e' -> uniq_labels e ->  EQ2 (makeL s e) (makeL s e').
Proof.
elim;ssa. apply/EQ2_eunf2. apply/EQ2_eunfl2. done.
rewrite /obs /nexte_wrap in H2 H3. ssa. de a. punfold H1. inv H1. inv H0. rewrite -H6 in H4. ssa.
rewrite -H5 in H3 H4. ssa. 
rewrite -H5 in H3 H4. ssa. de d.
destruct (lookup _ _) eqn:Heqn;ssa.
apply Forall_and in H7 as HH;ssa.
apply in_pair in Heqn. move/in_zip1 : Heqn. move/( _ _ _ H7). ssa. de x.
apply same_label in H10 as Hn;ssa. subst.
apply uniq_in_pair in H9. rewrite H9.  apply:H. done.
move/inP : H10. move/ForallP : H8. move=> HH2. move/HH2.
ssa. subst. de H8. 
apply mem_zip in H10. ssa. apply uniq_full_unf in H2. rewrite -H5 in H2. ssa.
apply (allP H12) in H. done.
apply Forall_and in H8;ssa. rewrite /dom -H8. 
apply uniq_full_unf in H2. rewrite -H5 in H2. ssa.
apply uniq_full_unf in H2. rewrite -H5 in H2. ssa.

punfold H1. inv H1. inv H0;ssa. pfold. con. con. 
rewrite -H5 in H3,H4. de d. apply:H;ssa. de H7.
apply uniq_full_unf in H2. rewrite -H5 in H2. ssa. 
pfold. con. con.
Qed.

Lemma lInvPred_makeL : forall s e, checkPath s e -> lInvPred e -> lInvPred (makeL s e).
Proof.
elim;ssa. rewrite -lInvPred_iff. done.
de a. rewrite /obs in H2. destruct (fe _) eqn:Heqn;ssa. de d.
destruct (lookup _ _) eqn:Heqn2;ssa. 
punfold H1. inv H1. rewrite Heqn in H0. inv H0. apply : H. done.
apply in_pair in Heqn2. move/inP : Heqn2. move=>Hin. move/ForallP : H5. move/(_ _ Hin). case;ssa. 
rewrite /obs in H2. destruct (fe _) eqn:Heqn2;ssa. de d. 
punfold H1. inv H1. rewrite Heqn2 in H0. inv H0. de H5.
Qed.


Lemma in_update2 : forall (A B : eqType) (l : seq ( A * B)) x (k : A)  v, x \in update l k v -> x = (k,v) \/ x \in l /\ x.1 != k.
Proof.
move => A B. elim;ssa.
rewrite inE in H0. move : H0. rifliad. norm_eqs. move/orP. case. move/eqP. move=>->. ssa.
intros.  apply H in b. de b.  rewrite H0.  lia. 
move/orP. case. move/eqP. intros. subst.  rewrite inE eqxx. lia. 
move/H. case. ssa. ssa. right. ssa.
Qed.


Lemma ECME : forall e l e', Estep e l e' -> forall p v, checkPath p e -> all (fun x => x.1 != l.1.2 )(makeQ p e) -> obs v (makeL p e) = Some (l.1.2,l.2) -> uniq_labels e -> lInvPred e -> EQ2 (makeL (p++[::v]) e) (makeL p e').
Proof. 
move=> e l e'. elim;ssa.
de p. rewrite /obs /nexte_wrap in H1 *. ssa. de d. de v0. apply:EQ2_refl. punfold H3. inv H3. inv H4. de H6. apply -> lInvPred_iff. done.

rewrite /obs /nexte_wrap in H1 H2 H3 H0 *. ssa. de o. de d.
neqt.
de p. rewrite /obs /nexte_wrap in H4 *. ssa. de v0. inv H4.
rewrite /obs /nexte_wrap in H3 H4 H5 H6 *. ssa. de o. apply H0;eauto. punfold H6. inv H6. inv H3. de H11.
de p. rewrite /obs /nexte_wrap in H2 *. ssa. de d. de v. inv H2. apply uniq_in_pair in H. rewrite H. apply:EQ2_refl. punfold H4. inv H4. inv H3.
apply in_pair in H. move/ForallP : H8. move=>HH. move/inP : H. move/HH. case;ssa. apply -> lInvPred_iff. done. done.

rewrite /nexte_wrap /obs in H1 H2 H3 H4 *. ssa. de d. de o.
destruct(lookup _ _) eqn:Heqn2;ssa. neqt.
de p. rewrite /nexte_wrap /obs in H5 *. ssa. de v. inv H5.
rewrite /obs /nexte_wrap in H5 H6 H7;ssa. de o.
destruct (lookup _ _)eqn:Heqn2;ssa. 
have : size es0 = size es1 by eauto.
move=>Hsize. apply in_pair in Heqn2.
move/in_zip1 : Heqn2. move/(_ _ _ Hsize). ssa. de x.
apply same_label in H12 as Hn. subst.
apply uniq_in_pair in H4. rewrite H4. 
have : s = (n0,s).2. done. move=>->.
have : l0 = (n0,l0).2. done. move=>->. apply:H1. apply/inP. done. done. done. done. 
ssa. apply mem_zip in H12. ssa. apply (allP H9) in H1. done. ssa.
punfold H7. inv H7. inv H1. move/ForallP : H14 => Hall. 
apply mem_zip in H12. ssa. 
move/inP : H12. move/Hall. case;ssa. rewrite /dom -H //. done. done.
rewrite makeL_fe2 full_eunf_subst -makeL_fe2.  apply:H0.
apply checkPath_fe in H1.  rewrite full_eunf_subst in H1. apply checkPath_fe2 in H1. done.
move : H2. rewrite makeQ_fe full_eunf_subst -makeQ_fe. done. 
move : H3. rewrite makeL_fe2 full_eunf_subst -makeL_fe2. done.
rewrite uniq_labels_subst;ssa. case :n;ssa.
apply lInvPred_iff in H5. rewrite full_eunf_subst in H5. apply <- lInvPred_iff in H5. done.
Qed.


Definition env_to (E'' E' : seq (ptcp * lType)) :=
       (forall (k : ptcp_eqType) (T : lType_EqType),
        lookup E'' k = Some T ->
        exists T' : lType_EqType,
          lookup E' k = Some T' /\ T << (ApplyF fe fe \o EQ2_gen) >> T' /\ ~~ is_erec T /\ ~~ is_erec T' /\ uniq_labels T)/\
       all (fun x : ptcp_eqType * lType_EqType => x.2 == EEnd) (filter_keys (predC (mem (dom E''))) E').

Inductive LQ_red2 : (seq (ptcp * lType)) -> (seq (ptcp * (seq (ch * (value + fin))))) -> 
                    (seq (ptcp * lType)) -> (seq (ptcp * (seq (ch * (value + fin))))) -> Prop :=
| LQ1' E Q  :  LQ_red2 E Q  E Q
| LQ2' E Q E' p c v Q' T T' l : lookup E p = Some T  ->
                                 lookup Q p = Some l  ->
                                 Estep2 T (Sd,c,v) T' ->
                                 E' = update E p (fe T') ->
                                 Q' = update Q p (l++[::(c,v)]) ->
                                  LQ_red2 E Q E' Q'
| LQ3' E Q E' p p' c v Q' T T' l l0 : all (fun x => x.1 != c) l0 ->
                                    lookup E p = Some T ->
                                    lookup Q p' = Some  (l0++(c,v)::l) ->
                                    Estep2 T (Rd,c,v) T' ->
                                    E' = update E p (fe T') -> 
                                    Q' = update Q p' (l0++l) ->
(*                                    uniq (dom E'') ->                                      
       (forall (k : ptcp_eqType) (T : lType_EqType),
        lookup E'' k = Some T ->
        exists T' : lType_EqType,
          lookup E' k = Some T' /\ T << (ApplyF fe fe \o EQ2_gen) >> T' /\ ~~ is_erec T /\ ~~ is_erec T' /\ uniq_labels T) ->
       all (fun x : ptcp_eqType * lType_EqType => x.2 == EEnd) (filter_keys (predC (mem (dom E''))) E') ->*)
                                    LQ_red2 E Q E' Q'.

(*
       uniq (dom E0) ->
       uniq (dom E1) ->
       (forall (k : ptcp_eqType) (T : lType_EqType),
        lookup E0 k = Some T ->
        exists T' : lType_EqType,
          lookup E1 k = Some T' /\ T << (ApplyF fe fe \o EQ2_gen) >> T' /\ ~~ is_erec T /\ ~~ is_erec T' /\ uniq_labels T) ->
       all (fun x : ptcp_eqType * lType_EqType => x.2 == EEnd) (filter_keys (predC (mem (dom E0))) E1) ->
*) 
(*Lemma env_to_refl : forall E, (forall e, e \in E ->  (~~ (is_erec e.2)) /\ lInvPred e.2 /\ uniq_labels e.2) -> env_to E E.
Proof.
ssa. rewrite /env_to. ssa. ssa. exists T. ssa. apply/EQ2_refl. 

apply in_pair in H0. apply H in H0. ssa.
apply in_pair in H0. apply H in H0. ssa.
apply in_pair in H0. apply H in H0. ssa.
apply in_pair in H0. apply H in H0. ssa.
erewrite filter_keys_eq. 
erewrite filter_keys_pred0. ssa.
ssa. tunf. apply/negP/negP. done.
Qed.

Definition E_assm (E : seq (ptcp * lType)) :=  (forall e, e \in E ->  (~~ (is_erec e.2)) /\ lInvPred e.2 /\ uniq_labels e.2).*)

(*equal domain is important for linear environments*)
Definition EQ_same (A : eqType) (E0 E1 : seq (A* lType)) := (forall k, k \in dom E0 <-> k \in dom E1) /\ forall p T T', lookup E0 p = Some T -> lookup E1 p = Some T' -> EQ2 T T'.

Lemma weak_coherent_lInv : forall E Q p T, weak_coherent E Q -> lookup E p = Some T -> lInvPred T.
Proof.
intros. inv H. ssa. inv H3. 
apply in_pair in H0 as H0'. de (mapP H0'). inv H5. 
apply:lInvPred_makeL.
rewrite /can_split in H2.  ssa. apply H2.
de x1.
apply uniq_in_pair.  inv H1. ssa. subst.

rewrite /dom -map_comp. rewrite map_inj_uniq. done.
intro. ssa. inv H8. done.

inv H1. ssa. subst.
de (mapP H4). subst. ssa.
apply -> lInvPred_iff.
apply:gInvPred_proj.
inv H6. ssa.
move: (H14 x).
ssa.
apply/gInvPred_iff/Project_gtree. eauto.
Qed.

Lemma weak_coherent_eq : forall E Q, weak_coherent E Q -> EQ_same E E.
Proof.
intros. con. done. intro. ssa. rewrite H0 in H1. inv H1.
apply/EQ2_refl. eapply weak_coherent_lInv. eauto. eauto.
Qed.

Lemma equiv_eq_dom : forall (A B : eqType) (E0 E1 : seq (A * B)), dom E0 = dom E1 ->  (forall k, k \in dom E0 <-> k \in dom E1).
Proof.
intros. rewrite H. done.
Qed.

Lemma coherence_pres  : forall E Q E' Q', LQ_red2 E Q E' Q' -> weak_coherent E Q -> exists E'', weak_coherent E'' Q' /\ EQ_same E'' E'.
Proof.
intros.
inv H.
- exists E'. ssa.  apply/weak_coherent_eq. eauto.
- exists ((update E p (fe T'))). 
  have :  weak_coherent (update E p (fe T'))
    (update Q p (l ++ [:: (c, v)])).

move : H0 H1 H2 H3 => H2 H4 H5 H6.
  inv H2.
  move : is_true_true => H3.
  move : is_true_true => H7.
  move : is_true_true => H8.
  ssa. 
  move : H0 H1 H7 H8 => H7 H8 H0 H1.
  
  inv H9. 
  econ. econ. con. eauto. con. 2:{ rewrite /split_set. 

instantiate (1:= (fun p' => if (p == p') && (p \in dom x) then (x0 p)++[::if v is inr n then Some n else None] else x0 p')).
 rewrite /update /makeLs -!map_comp. f_equal.
apply/eq_in_map. intro.
ssa. case_if. f_equal. 

norm_eqs. rewrite eqxx. ssa. eapply (map_f fst) in H10 as H_temp. rewrite H_temp. clear H_temp.

                                   rewrite /makeLs in H4.
                                   apply lookup_map2 in H4. ssa. inv H11. de x2. de x1. subst.
                                   have : uniq (dom x).
                                   inv H7. ssa. subst. de H12.  
                                                          move : H17 H18 H19 => Hun H17 Hgood.
                                   rewrite /dom -map_comp.
                                   rewrite map_inj_uniq. done. 

                                   intro. ssa. inv H18.
                                   intros. 
rewrite /can_split in H8. ssa.
remember H10. remember H4. 
clear Heqi Heqi0.
                                   apply uniq_in_pair in H10,H4;ssa. rewrite H10 in H4. inv H4.
                                   apply H8 in H10. move: H10 => HC. 
                                   rewrite makeL_cat. inv H6. ssa.
                                   apply uniq_in_pair in H17. rewrite H17. done. 
                                    

inv H7. ssa. subst.  inv H13. ssa.
de (mapP i0). inv H24. 
have : uniq_labels (trans x x2).
apply:uniq_trans. done.
intros.
apply uniq_full_unf in x4.
eapply uniq_makeL in x4. erewrite <- H10 in x4. ssa.

                                   case_if;ssa. norm_eqs.

rewrite /update /makeQs. 
apply/eq_in_map. intro.
ssa. case_if. f_equal. 

norm_eqs. rewrite eqxx. ssa.
rewrite /insertQ /insert_shift /insert /= //= in H5. 
                                    have: forall E p, lookup (list_map initQ E) (QKey (var_schl 0) p) = lookup E p. 
                               intros.
rewrite lookup_initQ //.

                                   move=>HHlook.
                                   rewrite /makeQs in H5.
                                   apply lookup_map2 in H5. ssa. inv H11. de x2. de x1. subst.

                                   have : uniq (dom x).
                                   inv H7. ssa. subst. de H12.  
                                   rewrite /dom -!map_comp.

move : H17 H18 H19 => Hun H17 Hgood.
have:  (list_map (fst \o (fun p : fin => (Ptcp p, fe (trans p x1)))) x2) = map Ptcp x2. apply/eq_in_map. intro. ssa. move=>->.
rewrite map_inj_uniq. done. intro. ssa. inv H18.

                                   intros. 
                                                          
                                   apply uniq_in_pair in H10,H5;ssa. rewrite H10 in H5. inv H5.


have : forall p p' l, checkPath p l -> makeQ (p ++ p') l = (makeQ p l)++(makeQ p' (makeL p l)). 
intros. rewrite makeQ_cat2 //. 

move=>HMakeQ. apply in_pair in H10 as HPP. apply (map_f fst) in HPP as H_tmep. rewrite H_tmep. clear H_tmep HPP. 
rewrite HMakeQ. f_equal.

                                   rewrite /makeLs in H4.
                                   apply lookup_map2 in H4. ssa. inv H12. de x2. de x1. 
                                   have : uniq (dom x).
                                   inv H7. 



                                   intros. 
                                                          rewrite /can_split in H8. ssa.
                                                          apply in_pair in H10.
remember H10. remember H4. clear Heqi0 Heqi.
                                   apply uniq_in_pair in H10,H4;ssa. rewrite H10 in H4. inv H4.


                                   apply H8 in H10. move: H10 => HC. 
                                                          inv H6. ssa. 
                                   apply uniq_in_pair in H18. rewrite H18. done. 



inv H7. ssa. subst.  inv H14. ssa.
de (mapP i0). inv H25. 
have : uniq_labels (trans x x2).
apply:uniq_trans. done.
intros.
apply uniq_full_unf in x4.
eapply uniq_makeL in x4. erewrite <- H10 in x4. ssa.



inv H8. apply H12. done.

destruct (eqVneq p (x1.1)). subst. ssa. ssa. } 
inv H8.
ssa. 


con. ssa. case_if;ssa. norm_eqs. inv H7. ssa. subst.
apply in_pair in H12 as Hpair. de (mapP Hpair). inv H15.
have: forall p p' l, checkPath p l -> checkPath p' (makeL p l) ->  checkPath (p ++ p') l. 
intros.
move : H19 H21. clear.
elim : p p' l0. ssa. 
ssa. by apply/checkPath_fe2. de a. destruct (fe _) eqn:Heqn;ssa. destruct (lookup _ _) eqn:Heqn2;ssa.
destruct (fe _) eqn:Heqn;ssa.
move=>HCheck. 

                                   rewrite /makeLs in H4.
                                   apply lookup_map2 in H4. ssa. 

                         inv H18. de x3. inv H19. subst.
                         apply HCheck. eauto. de (mapP H4). inv H22. 
                         inv H6. inv H22. 
                         inv H6. ssa. apply uniq_in_pair in H28. rewrite H28. done. 

have : uniq_labels (trans x3 x1).
apply:uniq_trans.  inv H13. ssa.
move/uniq_full_unf. move/uniq_makeL. move/(_ (x0 x3)).
rewrite -H23. ssa.

intros. 
 destruct (eqVneq p p0).  subst. rewrite (negbTE H12) andbC //=. eauto.
simpl. eauto. 
ssa. eapply weak_coherent_eq. eauto.

- 

move: H0 H1 H2 H3 H4 => H2 H4 H5 H6 H7.

move : H4 is_true_true H5 H6 H7 => Hall H4 H7 H5 H6.
move : is_true_true is_true_true is_true_true  => H0 H1 H3.
inv H2. ssa. inv H10. clear H10. inv H8. ssa. subst.



rewrite /makeQs -map_comp in H5. 
rewrite /makeLs -map_comp in H7. 
apply lookup_map2 in H5,H7. ssa. clear H4. inv H11. inv H14.  

rewrite /can_split in H9. ssa.
have: checkPath (x0 x) (fe (trans x x1)). apply /H4.
apply/lookup_map3.  eauto. 2:eauto. 
rewrite /dom -map_comp.
have: (list_map (fst \o (fun p : fin => (Ptcp p, fe (trans p x1)))) x2) = map Ptcp x2.
apply/eq_in_map. intro. ssa. move=>->. rewrite map_inj_uniq. done. intro. ssa. inv H15. done.
move=>HC.

have: checkPath (x0 x3) (fe (trans x3 x1)). apply /H4.
apply/lookup_map3. 
rewrite /dom -map_comp. 
rewrite map_inj_uniq. done. intro. ssa. inv H15. 2:econ. done.
move=>HC'.

(*clean up*)
clear H H0 (*Hoft*). 
clear H11. 
move: (*Hside*) Hall H12 H13 H2 H6 H8 H10 H5 H7 H14 H4 H9 HC HC' H3 H1. clear.
move: l x0 x1 x3 x => lp lp_fun G p_send p_receive.
move=> (*Hside*) Hall Hun HSub WC H_Estep2 HCo HCoG H_send_role H_receive_role H_makeQ.
move=> H_check_in H_check_notin H_check_receive H_check_send.
move=> H_oft H_LQ.

case : H_makeQ. move=>H_makeQ.




move : H_makeQ. move/[dup]. move=>H_makeQ.
move/makeQ_split4.
move/(_ H_check_send).
remember H_makeQ as H_makeQ_safe. clear HeqH_makeQ_safe.
case. move=> x [] v' [] y' [] Heq [] Hl0 Hl1. subst.
move: H_Estep2. move/[dup]. move=>H_Estep2.
move/to_canEstep2.


move=>HC.
have : Project G p_send (trans p_send G).
inv HCoG. ssa. move: (H3 p_send). ssa. apply:Project_EQ2. eauto. apply:proj_proj. eauto.
move=>HP_send.

have : Project G p_receive (trans p_receive G).
inv HCoG. ssa. move: (H3 p_receive). ssa. apply:Project_EQ2. eauto. apply:proj_proj. eauto.
move=>HP_receive.


apply makeQ_ETr in H_makeQ.
eapply makeQ_ETr2 in HC.
2: { apply:Project_eunf2. apply :HP_receive. } 
ssa. eapply to_Trp in H,H1.
2: { apply:Project_eunf2. apply:HP_send. } 
2: { apply:Project_eunf2. apply:HP_receive. } 
apply to_Trp2 in H1,H.
eapply to_Tr2 in H1. 6:eauto. 5:econ.
ssa.
eapply Tr2_to_canStep in H1. 2:econ.
inv HCoG. 
ssa. punfold H9. inv H9. apply H10 in H1. 
case : H1. move=> G' [] HStep [] //= HGood.



exists ((makeLs (list_map (fun p : fin => (Ptcp p, fe (trans p G'))) x2) (fun p : ptcp_eqType => if p == p_send then x ++ y' else lp_fun p))).


have:   weak_coherent
    (makeLs
       (list_map
          (fun p : fin =>
           (Ptcp p, fe (trans (Ptcp p) G'))) x2)
       (fun p : Equality.sort ptcp_eqType =>
        if p == Ptcp p_send then x ++ y' else lp_fun p))
    (update
       (makeQs
          (list_map
             (fun p : fin =>
              (Ptcp p, fe (trans (Ptcp p) G))) x2)
          lp_fun) (Ptcp p_send)
       (makeQ x (fe (trans (Ptcp p_send) G)) ++
        makeQ y'
          (makeL (x ++ [:: v'])
             (fe (trans (Ptcp p_send) G))))).

eapply (@preserve_proj _ _ _ p_send Sd) in HStep as H_send.
eapply Estep_full_unf2 in H_send.

eapply (@preserve_proj _ _ _ p_receive Rd) in HStep as H_receive.
eapply Estep_full_unf2 in H_receive.

clear H x3 H3 H0 H2.
move : H4 => H. 
move : H5 H6 H7 H8 => H0 H1 Hun' H2.
move : H_makeQ_safe => H_makeQ.
econ. 
exists (fun p => if p == Ptcp p_send then x++y' else lp_fun p).


con.



econ. exists x2. 
con. instantiate (1:= G'). econ. apply/linearity.Linear_step. eauto. inv HCoG.


ssa. apply/size_pred_step. eauto. done.
apply:action_pres. eauto. eauto.


apply: uniqg_labels_pres. eauto. done.
intros.
exists (trans p G'). ssa.
apply: preserve_proj5. eauto. ssa. done.
ssa.
move : (H2 p). ssa.
eapply Project_EQ2. eauto.
apply/proj_proj. done.



econ.
con. ssa. intro. intros. apply/HSub. apply/step_contained. eauto. done.
con. 


rewrite /can_split. ssa.
intros.  apply lookup_map2 in H3. ssa. inv H4. subst.
case_if. norm_eqs. rewrite H5.

eapply harmony_sound in HStep.
6: { instantiate (1:= ( fun x => trans x G)). rewrite /one_shot. intros. 
     move: (H2 p). ssa.
     apply:Project_EQ2. eauto. apply:proj_proj. done. } 
case : HStep. move=> f_one [] Hone HEnv.
inv HEnv. ssa.
have : EQ2 e (trans p_send G').
move : (Hone p_send). rewrite /update_action /=. rewrite /harmony.update eqxx /=.
intro.
apply:proj_proj. 


have : p_send != p_receive.
apply/eqP. intro. 
apply to_canEstep2 in H_Estep2.
eapply makeQ_ETr3 in H_Estep2;eauto.
ssa. eapply test_test in H11. 
7: {   eauto. rewrite H8 in H_makeQ. eauto. }
apply/negP.  apply (allP H11). apply : H13. done.
apply:Project_eunf2. apply:Project_EQ2. apply : HP_receive.
apply:EQ2_refl. apply:gInvPred_proj. 
apply/gInvPred_iff/Project_gtree. eauto. 
done. done. done. done.
intro. 
move : Hone0. case_if. norm_eqs. inv H8. neqt. done.

move=>HQ.


apply:checkPath_EQ2. apply:EQ2_eunf2.  apply:HQ.

apply:checkPath_Estep2. eauto.
rewrite makeQ_fe. eauto. 

Hint Resolve checkPath_fe checkPath_fe2 checkPath_cat. 
rewrite Heq in H_check_send. eauto.
2: {  rewrite Heq in H_check_send. eauto. } 
4:econ. ssa.



rewrite Heq in H_check_send. apply checkPath_cat2 in H_check_send as HC2. ssa.
clear H11. rewrite Heq in H_makeQ.
rewrite !makeQ_cat2 in H_makeQ.
have: drop (size (makeQ x (fe (trans p_send G)))) ((makeQ x (fe (trans p_send G)))  ++
                 makeQ (v' :: y') (makeL x (fe (trans p_send G)))) =
      drop (size ( makeQ x (fe (trans p_send G))))  (makeQ x (fe (trans p_send G)) ++
                 (c, v) :: makeQ y' (makeL (x ++ [:: v']) (fe (trans p_send G)))).
rewrite H_makeQ. rewrite !drop_size_cat //=.
rewrite !drop_size_cat.
simpl. de v'. rewrite /obs in H_makeQ x4. ssa.
rewrite /obs. ssa. destruct (fe (makeL _ _)) eqn:Heqn;ssa. de d. de d.
destruct (lookup _ _) eqn:Heqn2;ssa. rewrite -makeL_fe in Heqn. rewrite Heqn.
inv x4. apply checkPath_cat in H_check_send. apply:checkPath_fe2. done.
rewrite /obs in H_makeQ x4 *. ssa.
destruct (fe (makeL _ _))eqn:Heqn;ssa. de d. rewrite -makeL_fe in Heqn. rewrite Heqn.
inv x4. apply checkPath_cat in H_check_send. apply:checkPath_fe2. done.
de d. 
rewrite makeQ_size //. apply checkPath_cat in H_check_send. done.
rewrite makeQ_size //. apply checkPath_cat in H_check_send. done.
apply checkPath_cat in H_check_send. done.

apply:uniq_trans. done. done. done. done. done. done.

destruct (eqVneq x3 p_receive). subst.
apply:checkPath_fe.
apply:checkPath_Estep3. apply H_receive.
apply:uniq_full_unf. apply:uniq_trans. done. done.
apply H_check_in. apply:lookup_map3.
rewrite /dom -map_comp. rewrite map_inj_uniq. done. 
intro. ssa. inv H6. apply H3.  done.
move: (H2 x3). ssa.
apply:checkPath_EQ2.
apply:EQ2_eunf2. apply:preserve_proj2. eauto. eauto.
apply/gInvPred_iff/Project_gtree. eauto.
ssa. rewrite /comp_dir. ssa. rewrite H5. case_if. norm_eqs. inv H7. neqt. done. done.
done. apply:checkPath_fe2.  apply H_check_in. apply:lookup_map3. eauto.
rewrite /dom -map_comp. rewrite map_inj_uniq. done. 
intro. ssa. inv H7. apply H3.  de x3.




intros. rewrite /dom -map_comp in H3. case_if. norm_eqs. 
exfalso. apply/negP. apply H3. apply/mapP. econ. 2:econ. done. 
apply H_check_notin. apply/negP. intro. apply/negP. apply:H3. 
rewrite /dom -map_comp in H5. de (mapP H5).




rewrite /split_set.
rewrite /split_set. 

f_equal.
rewrite /update /makeQs -!map_comp.
subst. apply/eq_in_map. intro. ssa.
case_if. subst. norm_eqs.  rewrite H4. f_equal.
have : Project G' p_send  (trans p_send G').
apply:preserve_proj5. eauto. ssa. done.
move: (H2 p_send). ssa.

move/proj_proj.
move/EQ2_eunf2.
move/makeQ_EQ2=><-. inv H_makeQ.
move : H_send H6. move=>HE.

have : uniq_labels (fe (trans p_send G)).
apply:uniq_full_unf. apply:uniq_trans. done.
move : HE H_check_send.  move : (fe _) Heq Hall => e. clear.
move=>->.
move=> Hall HE HC Hun Hcat.

rewrite makeQ_cat2. f_equal.



 apply checkPath_cat in HC .
      move : HE HC Hall. clear Hcat.
      move Heq : (Sd,_,_) => l HE.
      move : HE x c v Heq Hun. clear.
      elim;ssa. de x. 
      de o. rewrite /obs in Hall. ssa. de d. inv Heq. rewrite eqxx in H1. done.
      de x.
      de o. inv Heq. ssa. f_equal. eauto.
      inv Heq. ssa. de x. ssa. 
      rewrite /nexte_wrap in H1. de o.
      destruct (lookup _ _) eqn:Heqn;ssa. neqt.
   de x.
      de o. destruct (lookup _ _) eqn:Heqn;ssa. inv Heq. 
      move/in_pair in Heqn.
      have : size es0 = size es1. eauto.
      move=>Hsize.
      move/in_zip1 : Heqn. move/(_ _ _ Hsize). ssa.  de x0.

      apply mem_zip in H10 as HH. ssa.
      have : dom es0 = dom es1. rewrite /dom H//.
      move=>Hdom. eapply same_label in Hdom. 3:eauto. subst.
      apply uniq_in_pair in H12. rewrite H12. f_equal. 

   move/inP : H10. move/H1. move=>HH2. simpl in HH2. eapply HH2;eauto.  
   apply (allP H4) in H11. done. rewrite /dom -H. done. done.
   rewrite makeQ_fe full_eunf_subst -makeQ_fe. 
   apply/H0. eauto. 
   rewrite uniq_labels_subst;ssa. case :n ;ssa.
   apply checkPath_fe in HC. rewrite full_eunf_subst in HC.
   apply checkPath_fe2 in HC. done.
   rewrite makeQ_fe full_eunf_subst -makeQ_fe in Hall. eauto. 

   have : v' :: y' = [::v']++ y'. done.
   move=>xeq. rewrite xeq catA in HC. 
   apply checkPath_cat in HC.

   have:  makeQ (x ++ [::v']) e =
          makeQ x e ++ [::(c, v)].
   have: makeQ ((x ++ [::v']) ++ y') e =
      (makeQ x e ++ [::(c, v)]) ++ (makeQ y' (makeL (x ++ [:: v']) e)).
   rewrite -!catA //=. clear Hcat =>Hcat.
   rewrite makeQ_cat2 in Hcat.
   have: take (size (makeQ (x ++ [:: v']) e)) (makeQ (x ++ [:: v']) e ++ makeQ y' (makeL (x ++ [:: v']) e)) =
         take (size ((makeQ x e ++ [:: (c, v)]))) ((makeQ x e ++ [:: (c, v)]) ++ makeQ y' (makeL (x ++ [:: v']) e)).
   rewrite Hcat //=. rewrite !take_size_cat //. rewrite makeQ_cat2. rewrite !size_cat. f_equal. rewrite makeQ_size;ssa.
   apply checkPath_cat2 in HC. ssa.
   apply checkPath_cat2 in HC.  ssa.
   apply checkPath_cat in HC. done.
   rewrite !take_size_cat. done.  done. done. done.
   clear Hcat => Hcat. 
   f_equal.
   clear xeq.
   apply checkPath_cat in HC as HC2.
   rewrite makeQ_cat2 in Hcat.
   have: makeQ [:: v'] (makeL x e) = [:: (c, v)].
   apply checkPath_cat2 in HC.
   have: drop (size (makeQ x e)) (makeQ x e ++ makeQ [:: v'] (makeL x e)) = drop (size (makeQ x e)) (makeQ x e ++ [:: (c, v)]).
   rewrite Hcat. done. rewrite !drop_size_cat //.
   clear Hcat => Hcat.
   rewrite makeL_cat. ssa. 
   apply checkPath_cat2 in HC.
   destruct (obs _ _) eqn:Heqn;last by de v'.
   destruct (nexte_wrap _ _) eqn:Heqn2;last by []. inv Hcat.
   clear Hcat.
 clear HC.
   move : HE HC2 Heqn2 Heqn Hall Hun. clear.
   move Heq : (Sd,_,_) => l'  HE.
   move : HE c v v' x s Heq.
   elim.
 * intros. inv Heq.
   de x. rewrite /obs in Heqn. ssa. de v'. inv Heqn2.
   de o. rewrite eqxx in H1. done.
 * intros. inv Heq. 
   de x. rewrite /obs in Heqn. ssa. de v'. inv Heqn2. inv Heqn. 
   de o. eauto.
 * intros. inv Heq.
   de x. rewrite /obs in Heqn. ssa. de v'. inv Heqn.
   apply uniq_in_pair in H. rewrite H in Heqn2. inv Heqn2. done. 
   rewrite /obs in H0. ssa. de o.
   destruct (lookup _ _) eqn:Heqn3. ssa. neqt. done. 
 * intros. inv Heq.
   de x. rewrite /obs in Heqn. ssa. de v'. inv Heqn.
   rewrite /obs in H3. ssa. de o. 
   
   rewrite /obs in Heqn. 
   destruct (lookup _ _) eqn:Heqn3. 
   apply in_pair in Heqn3. have : size es0 = size es1 by eauto.
   move=>Hsize. move/in_zip1 : Heqn3. move/(_ _ _ Hsize). ssa.
   de x0. move: (H10).
   have : uniq (dom es0). done.
   move=>Hun.
   move/same_label. move/(_ H Hun). intros. subst.
   move/inP:(H10).
   move/H1. simpl. move=>HH. 
   apply uniq_in_pair in H9. rewrite H9. eapply HH. eauto. done. eauto. done. done.
   apply mem_zip in H10. ssa. apply (allP H4) in H10. done. rewrite /dom -H //. ssa.

 * intros. apply/H0;eauto. apply checkPath_fe in HC2. rewrite full_eunf_subst in HC2. apply checkPath_fe2 in HC2. done. 
   rewrite makeL_fe2 full_eunf_subst -makeL_fe2  in Heqn2. eauto.
   rewrite makeL_fe2 full_eunf_subst -makeL_fe2  in Heqn. eauto.
   rewrite makeQ_fe full_eunf_subst -makeQ_fe  in Hall. eauto.
   rewrite uniq_labels_subst;ssa. case: n;ssa.
   done. 


   have : v' :: y' = [::v']++ y'. done.
   move=>xeq. rewrite xeq catA in HC Hcat.
   apply checkPath_cat in HC.
   rewrite makeQ_cat2 in Hcat.
   have:  makeQ x e ++ (c, v) :: makeQ y' (makeL (x ++ [:: v']) e) = 
          (makeQ x e ++ [::(c, v)]) ++ makeQ y' (makeL (x ++ [:: v']) e).
   rewrite -catA //. move=> xeq0. rewrite xeq0 in Hcat. clear xeq0.
   have : forall (A : Type) (l0 l1 l2 l3 : seq A), l0 ++ l1 = l2 ++ l3 -> size l0 = size l2 ->  l0 = l2.
   intros. have : take (size l0) (l0 ++ l1) = take (size l2) (l2++l3). rewrite H.
   rewrite !take_size_cat //.  rewrite !take_size_cat //. 
   move=>Hseq. apply Hseq in Hcat. 2: {  rewrite !size_cat !makeQ_size. rewrite !size_cat.  done.
  apply checkPath_cat in HC. done. done. } 
   clear xeq.
   rewrite makeQ_cat2 in Hcat.
   apply checkPath_cat in HC as HC2.
   have : forall (A : Type) (l0 l1 l2 l3 : seq A), l0 ++ l1 = l2 ++ l3 -> size l0 = size l2 ->  l1 = l3.
   intros. have : drop  (size l0) (l0 ++ l1) = drop (size l2) (l2++l3). rewrite H.
   rewrite !drop_size_cat //.  rewrite !drop_size_cat //. 
   clear Hseq => Hseq.
   apply Hseq in Hcat;last by []. ssa.
   destruct (obs _ _) eqn:Heqn;ssa. destruct (nexte_wrap _ _) eqn:Heqn2;ssa. inv Hcat.
   clear Hcat Hseq. clear Heqn2.
   
   move : HE x v' HC HC2 Heqn Hall Hun. clear.
   move Heq : (Sd,_,_) => l HE.
   move: HE c v Heq.
   elim.
* intros. inv Heq. de x. de o. by rewrite eqxx in H3. de o. by rewrite eqxx in H3. 
* intros. inv Heq. de x. de o. eauto.
* intros. inv Heq. de x. de o. destruct (lookup _ _) eqn:Heqn2;ssa. neqt.
  de o. destruct (lookup es n0) eqn:Heqn2;ssa. neqt. 
* intros. inv Heq. de x. de o. destruct (lookup es0 n) eqn:Heqn3;ssa.
  apply in_pair in Heqn3. have : size es0 = size es1 by eauto.
  move=>Hsize. move/in_zip1 : Heqn3. move/(_ _ _ Hsize). ssa.
  de x0. move: (H12).
  have : uniq (dom es0).  done.
  move=>Hun.
  move/same_label. move/(_ H Hun). intros. subst.
  move/inP:(H12).
  move/H1. simpl. move=>HH. 
  apply uniq_in_pair in H11. rewrite H11. eapply HH. eauto. eauto. done.  eauto. done. 
  apply mem_zip in H12. ssa. apply (allP H4) in H12. done. 
  rewrite /dom -H. done. 
 * intros. apply/H0;eauto. apply checkPath_fe in HC. rewrite full_eunf_subst in HC. apply checkPath_fe2 in HC. eauto.
   apply checkPath_fe in HC2. rewrite full_eunf_subst in HC2. apply checkPath_fe2 in HC2. eauto.
   rewrite makeL_fe2 full_eunf_subst -makeL_fe2  in Heqn. eauto.
   rewrite makeQ_fe full_eunf_subst -makeQ_fe  in Hall. eauto.
   rewrite uniq_labels_subst;ssa. case: n;ssa.

  
by apply checkPath_cat in HC.
by [].

  f_equal.

destruct (eqVneq x3 p_receive).
move : e => Hp_rec.
   have : Project G x3 (trans x3 G).
   move: (H2 x3). ssa. apply:Project_EQ2. eauto. apply:proj_proj. done.

  move/proj_proj. 
  move/EQ2_eunf2.
  move/makeQ_EQ2=><-.


rewrite Hp_rec.

have : uniq_labels (fe (trans p_receive G)).
apply:uniq_full_unf. apply:uniq_trans. done. clear Hun => Hun.

have : lInvPred (fe (trans p_receive G)).
apply -> lInvPred_iff. apply:gInvPred_proj.  
apply/gInvPred_iff. apply:Project_gtree. eauto. move=>Hinv.
rewrite makeQ_fe. symmetry. rewrite -makeQ_fe. symmetry.
move : H_receive. move=>HE.
move : HE H_check_receive Hun Hinv.  move : (fe _) => e. clear.
move : (lp_fun p_receive) => lp'.
move Heq : (Rd,c,v) => l.
move=>HE.
elim : HE c v Heq lp'.
- intros. de lp'. de o. rewrite /obs /= in H. de d. 
- intros. inv Heq. de lp'. de o. f_equal.  apply:H0;eauto. punfold Hinv.  inv Hinv. inv H0. de H5.
- intros. de lp'. de o. rewrite /obs /= in H0. de d.
- intros. de lp'. de o. destruct (lookup _ _) eqn:Heqn2;ssa. inv Heq.
  apply in_dom in Heqn2 as HH. rewrite /dom H in HH. apply in_dom_exists in HH. ssa. rewrite H7. f_equal.
  apply in_pair in Heqn2, H7.
  eapply uniq_in_zip in H7. 4:apply Heqn2. move/inP : H7. move/H1.
  move/(_ _ _ Logic.eq_refl)=>/=. move=>xx. apply:xx; eauto. 
  apply (allP H4) in Heqn2. done.
  punfold Hinv. inv Hinv. inv H7. move/ForallP : H9 => HAll. move/inP : Heqn2. move/HAll.
  case;ssa.
  rewrite /dom //. done. 
- intros. 
  erewrite makeQ_EQ2. apply/H0. eauto.
  apply checkPath_fe in H_check_receive. rewrite full_eunf_subst in H_check_receive.
  apply checkPath_fe2 in H_check_receive. done.
  apply uniq_full_unf in Hun. rewrite full_eunf_subst in Hun. 
  apply uniq_full_unf2 in Hun. done.

  apply lInvPred_iff in Hinv. rewrite full_eunf_subst in Hinv.
  apply <- lInvPred_iff in Hinv. done.

  apply/EQ2_eunfl. rewrite full_eunf_subst. apply/EQ2_eunfl2. 
  apply/EQ2_refl. 
  apply lInvPred_iff in Hinv. rewrite full_eunf_subst in Hinv.
  apply <- lInvPred_iff in Hinv. done.



apply/makeQ_EQ2.
apply:EQ2_eunf2. apply:EQ2_eunfl2.
move: (H2 x3). ssa.
apply:preserve_proj2. eauto. eauto.
apply/gInvPred_iff/Project_gtree. eauto.
simpl. rewrite /comp_dir /=.
rewrite H4. case_if. norm_eqs. inv H6.
rewrite eqxx in i. done. done. done.
done. 
rewrite /comp_dir /= eqxx. case_if;ssa.
apply label_pred in HStep. ssa. rewrite (eqP H1) in HStep.
neqt. done. done. done. done.
rewrite /comp_dir. ssa. rewrite eqxx. done.
done. done. 


ssa.






1: {  

con. apply/equiv_eq_dom.
rewrite dom_update. rewrite /makeLs /dom -!map_comp. 
intros.
apply/eq_in_map. intro. ssa.

intro. intros. 
move : H1 H11 => Hlook H1.

ssa.

apply in_pair in H1. 



apply in_update2 in H1. 
de H1.
inv H1.

apply/EQ2_sym.



eapply lookup_map2 in Hlook. ssa.
inv H12. de (mapP H11). subst. ssa.                           rewrite H14.

have : Ptcp p_send != Ptcp p_receive.
apply label_pred in HStep;ssa. rewrite neg_sym. move/negbTE=>->.


eapply harmony_sound in HStep.
6: { instantiate (1:= ( fun x => trans x G)). rewrite /one_shot. intros. 
     move: (H8 p). ssa.
     apply:Project_EQ2. eauto. apply:proj_proj. done. } 
case : HStep. move=> f_one [] Hone HEnv.
inv HEnv. ssa.
have : EQ2 e' (trans p_receive G').
move : (Hone p_receive). rewrite /update_action /=. rewrite /harmony.update eqxx /=.
intro.
apply:proj_proj. done.
move=>HQ.


(*FIND ME*)
eapply Estep_makeL in H_Estep2 as H_Estep3.
2: { apply Estep_full_unf2. eauto. } 
eapply Estep23 in H_Estep3.
2:eauto.




apply:EQ2_trans. apply:EQ2_eunfl2. 2: {  apply check_makeL.
2: { apply:EQ2_eunf2. apply:HQ. } 
apply:checkPath_Estep3. 4: { apply : H_check_receive. } 
apply:Estep_full_unf2. eauto.
apply: uniq_full_unf. apply:uniq_trans. done. done. apply:harmony.step_uniq. eauto. 
apply:uniq_trans. done. } 
done. apply:lInvPred_makeL. done. rewrite -lInvPred_iff. apply:gInvPred_proj. 
move : (H8 (Ptcp 0)). ssa. apply/gInvPred_iff. apply:Project_gtree. eauto.
apply uniq_makeL. 
apply uniq_full_unf. apply:uniq_trans. done. done.
done. 
apply uniq_full_unf. apply:uniq_trans. done. done.
done. done. done.

move : H11 => H_receive_not.


(*I added*)
eapply lookup_map2 in Hlook. ssa.
inv H12. de (mapP H11). subst. ssa.

apply/EQ2_sym.



clear H13 H12 H11.

de (mapP H1). inv H12. rewrite H14. clear H14. de (mapP H11). subst. ssa.
case_if. norm_eqs. 

rewrite H14.



eapply harmony_sound in HStep as Harm.
6: { instantiate (1:= ( fun x => trans x G)). rewrite /one_shot. intros. 
     move: (H8 p). ssa.
     apply:Project_EQ2. eauto. apply:proj_proj. done. } 

case : Harm. move=> f_one [] Hone HEnv.
inv HEnv. ssa.


(*HERE*)
have : EQ2 e (trans p_send  G').
move : (Hone p_send). rewrite /update_action /=. rewrite /harmony.update eqxx /=.
have : p_send != p_receive. apply label_pred in HStep. ssa. done. done. 
intro. case_if. norm_eqs. inv H17.  rewrite eqxx in x5. ssa.
move/proj_proj. done.
move=>HQ.


clear H16.


rewrite Heq.
have : x ++ (v'::y') = (x++[::v'])++y'.  rewrite -catA.  done.
move=>->. rewrite makeL_cat. apply/EQ2_sym. rewrite makeL_cat. apply/EQ2_sym.
apply check_makeL.
2: { rewrite -!makeL_fe2. apply:EQ2_trans.
     apply:ECME.  apply:H15. rewrite Heq in H_check_send. apply checkPath_cat in H_check_send.
apply checkPath_fe2.  done. simpl. rewrite makeQ_fe. done. 
ssa.
rewrite Heq in H_check_send. apply checkPath_cat2 in H_check_send as HC2. ssa.
clear H17. rewrite Heq in H_makeQ_safe.
rewrite !makeQ_cat2 in H_makeQ_safe.
have: drop (size (makeQ x (fe (trans p_send G)))) ((makeQ x (fe (trans p_send G)))  ++
                 makeQ (v' :: y') (makeL x (fe (trans p_send G)))) =
      drop (size ( makeQ x (fe (trans p_send G))))  (makeQ x (fe (trans p_send G)) ++
                 (c, v) :: makeQ y' (makeL (x ++ [:: v']) (fe (trans p_send G)))).
rewrite H_makeQ_safe. rewrite !drop_size_cat //=.
rewrite !drop_size_cat.
simpl. de v'. rewrite /obs in H_makeQ_safe x5. ssa.
rewrite /obs. ssa. destruct (fe (makeL _ _)) eqn:Heqn;ssa. de d. de d.
destruct (lookup _ _) eqn:Heqn2;ssa. rewrite -makeL_fe in Heqn. rewrite Heqn.
inv x5. apply checkPath_cat in H_check_send. apply:checkPath_fe2. done.
rewrite /obs in H_makeQ_safe x5 *. ssa.
destruct (fe (makeL _ _))eqn:Heqn;ssa. de d. rewrite -makeL_fe in Heqn. rewrite Heqn.
inv x5. apply checkPath_cat in H_check_send. apply:checkPath_fe2. done.
de d. 
rewrite makeQ_size //. apply checkPath_cat in H_check_send. done.
rewrite makeQ_size //. apply checkPath_cat in H_check_send. done.
apply checkPath_cat in H_check_send. done.

apply:uniq_trans. done.
apply:gInvPred_proj.
apply/gInvPred_iff/Project_gtree. eauto.


apply check_makeL.
have : x = x ++ nil. rewrite cats0. done. move=>->.
eapply checkPath_Estep2. eauto. rewrite makeQ_fe. eauto. apply:checkPath_fe2. 
rewrite Heq in H_check_send. apply checkPath_cat in H_check_send. done.
4:done. 4:done.
2: { rewrite Heq in H_check_send. have : x ++ v' :: y' = (x++ [::v']) ++ y'. rewrite -catA.  done.
     move=> xx. rewrite xx in H_check_send.
     apply checkPath_cat in H_check_send. apply checkPath_fe2. eauto. } 
ssa.

rewrite Heq in H_check_send. apply checkPath_cat2 in H_check_send as HC2. ssa.
clear H17. rewrite Heq in H_makeQ_safe.
rewrite !makeQ_cat2 in H_makeQ_safe.
have: drop (size (makeQ x (fe (trans p_send G)))) ((makeQ x (fe (trans p_send G)))  ++
                 makeQ (v' :: y') (makeL x (fe (trans p_send G)))) =
      drop (size ( makeQ x (fe (trans p_send G))))  (makeQ x (fe (trans p_send G)) ++
                 (c, v) :: makeQ y' (makeL (x ++ [:: v']) (fe (trans p_send G)))).
rewrite H_makeQ_safe. rewrite !drop_size_cat //=.
rewrite !drop_size_cat.
simpl. de v'. rewrite /obs in H_makeQ_safe x5. ssa.
rewrite /obs. ssa. destruct (fe (makeL _ _)) eqn:Heqn;ssa. de d. de d.
destruct (lookup _ _) eqn:Heqn2;ssa. rewrite -makeL_fe in Heqn. rewrite Heqn.
inv x5. apply checkPath_cat in H_check_send. apply:checkPath_fe2. done.
rewrite /obs in H_makeQ_safe x5 *. ssa.
destruct (fe (makeL _ _))eqn:Heqn;ssa. de d. rewrite -makeL_fe in Heqn. rewrite Heqn.
inv x5. apply checkPath_cat in H_check_send. apply:checkPath_fe2. done.
de d. 
rewrite makeQ_size //. apply checkPath_cat in H_check_send. done.
rewrite makeQ_size //. apply checkPath_cat in H_check_send. done.
apply checkPath_cat in H_check_send. done.

apply:uniq_trans. done. done.

apply:harmony.step_uniq. eauto.
apply:uniq_trans. done. 
} 
rewrite Heq in H_check_send.
have : x ++ v' :: y' = (x++ [::v']) ++ y'. rewrite -catA.  done.
move=> xx. rewrite xx in H_check_send.
apply checkPath_cat2 in H_check_send. done.

apply uniq_makeL. 
apply:uniq_full_unf. 
apply:uniq_trans. done. done. done. done. done.

eapply harmony_sound in HStep as Harm.
6: { instantiate (1:= ( fun x => trans x G)). rewrite /one_shot. intros. 
     move: (H8 p). ssa.
     apply:Project_EQ2. eauto. apply:proj_proj. done. } 

case : Harm. move=> f_one [] Hone HEnv.
inv HEnv. ssa.


(*HERE*)
have : EQ2 e' (trans p_receive  G').
move : (Hone p_receive). rewrite /update_action /=. rewrite /harmony.update eqxx /=.
move/proj_proj. done.
move=>HQ.





apply check_makeL.  apply:H_check_in.
apply:lookup_map3. rewrite /dom -map_comp. rewrite map_inj_uniq. done.
intro. ssa. inv H17. 2: { econ. }  done.

move : (H8 x7). ssa.
apply:EQ2_eunf2. apply:EQ2_eunfl2.
apply:preserve_proj2. eauto. eauto.  
apply/gInvPred_iff/Project_gtree. eauto. simpl. rewrite /comp_dir /=.
rewrite H14. inv H12.
 case_if. done. done. done. done. 
apply:uniq_full_unf. apply:uniq_trans. done.
done. done. done. done.


}

done. 

by inv HCoG;ssa.
by inv HCoG;ssa.
by inv HCoG;ssa.
apply/eqP. intro. subst.
 apply to_canEstep2 in H_Estep2.
eapply makeQ_ETr3 in H_Estep2;eauto.
ssa. eapply test_test in H4. 7:eauto.
7: {   rewrite H3 in H_makeQ_safe. eauto. }
apply/negP.  apply (allP H4). apply : H6. done.
apply:Project_eunf2. apply:Project_EQ2. apply : HP_receive.
apply:EQ2_refl. apply:gInvPred_proj. 
apply/gInvPred_iff/Project_gtree. eauto. 

by inv HCoG;ssa.
by inv HCoG;ssa. done.
by inv HCoG;ssa. ssa.
apply/allP. intro. move/(allP H0). ssa. 
apply/allP. intro. move/(allP H2). ssa.
by inv HCoG;ssa.
by inv HCoG;ssa.
by inv HCoG;ssa.
done. done. done.
Qed.




Definition L_from_env (E : l_env) := map_keys (fun x => if x is schlT s p then p else Ptcp 0) E.
Definition Q_from_env (Q : q_env) := map_keys (fun x => match x with QKey s p => p end) Q.

Definition l_sess (n : schl) (s : sch) := if s is schlT s' _ then s' == n else false.
Definition q_sess (n : schl) (s : qkey) := match s with QKey s' _  => s' == n end.

Definition coherent_exists (l : seq (ptcp * lType)) g :=
exists (S : seq fin),
  coherentG g /\
  l = list_map (fun p : fin => (Ptcp p, fe (trans p g))) S /\
  uniq S /\ subset (roles g) S.

Definition weak_coherent_exists l q g f := exists L, coherent_exists L g /\ can_split L f /\ 
  (l,q) = split_set L f.


Lemma coherent_to_exists : forall l, coherent l -> exists g, coherent_exists l g.
Proof. intros. inv H.
Qed.

Lemma coherent_to_exists2 : forall l g, coherent_exists l g -> coherent l.
Proof. intros. exists g. inv H.
Qed.

Lemma weak_coherent_to_exists : forall l q, weak_coherent l q -> exists g f, weak_coherent_exists l q g f.
Proof.
intros. inv H. ssa. inv H0. 
ssa. exists x1,x0.
rewrite /weak_coherent_exists.  exists x. ssa.
rewrite /coherent_exists.  eauto.
Qed.

Lemma weak_coherent_to_exists2 : forall l q g f,weak_coherent_exists l q g f ->  weak_coherent l q.
Proof.
intros.  
inv H.  exists x. exists f. ssa. eapply coherent_to_exists2. eauto.
Qed.

Definition env_coherent (E : l_env) (Q : q_env) := exists (Gs :seq (schl * gType)) (f : (schl * ptcp -> lpath)), check_gs Gs f /\  coherent_gTypes Gs /\ (forall s p, QKey s p \in dom Q -> s \in dom Gs) /\ forall s G, lookup Gs s = Some G -> weak_coherent_exists (L_from_env (filter_keys (l_sess s) E)) (Q_from_env (filter_keys (q_sess s) Q)) G (fun p => f (s,p)).

Lemma coherent_balanced : forall E Q, uniq (dom E) -> uniq (dom Q) -> env_coherent E Q -> sub_domLQ E Q  ->only_schl E -> balanced E Q.
Proof.
move=> E Q Hun HunQ.
intros. 
inv H. ssa.
move : H3 H4 H5 => Hco H3 H4.
exists x.  exists x0. con. done.
ssa.
intro. intros.
apply in_pair in H5 as Hin.
rewrite /sub_domLQ in H0. eapply (@map_f _ _ fst) in Hin. eapply H0 in Hin.
apply H3 in Hin.
apply in_dom_exists in Hin. ssa.
exists x1. con. done.
apply H4 in H6. 
remember (  (fun p : ptcp => x0 (s, p))).
inv H6. subst.
ssa. inv H9. rewrite /L_from_env in H11. 
have : lookup ( map_keys
          (fun x : sch_eqType =>
           match x with
           | var_sch _ => Ptcp 0
           | schlT _ p => p
           end) (filter_keys (l_sess s) E)) p = Some T.
apply/uniq_in_pair.
rewrite dom_map_keys dom_filter_keys. 
rewrite map_inj_in_uniq. 
apply:filter_uniq. done. intro.
ssa. rewrite !mem_filter in H10,H13. ssa. 
de x3. de y. subst. norm_eqs. done.
apply/mapP. econ. apply/in_pair.   apply/lookup_filter. 2:eauto. ssa. simpl. done.
rewrite H11.
intros. 
apply lookup_map2 in x3. ssa. inv H13. 
inv H7. ssa. subst. 
de (mapP H10). subst. ssa.
rewrite makeL_fe2. done.


intro. ssa. 
apply in_pair in H5 as Hin.
eapply (@map_f _ _ fst) in Hin. eapply H3 in Hin.
apply in_dom_exists in Hin. ssa.
exists x1. con. done.
apply H4 in H6. 
remember (  (fun p : ptcp => x0 (s, p))).
inv H6. subst.
ssa. inv H9. rewrite /Q_from_env in H12. 
have : lookup ( map_keys
          (fun x : qkey_eqType =>
           match x with
           | QKey _ p => p
           end) (filter_keys (q_sess s) Q)) p = Some T.
apply/uniq_in_pair.
rewrite dom_map_keys dom_filter_keys. 
rewrite map_inj_in_uniq. 
apply:filter_uniq. done. intro.
ssa. rewrite !mem_filter in H10,H13. ssa. 
de x3. de y. subst. norm_eqs. done.
apply/mapP. econ. apply/in_pair.   apply/lookup_filter. 2:eauto. ssa. simpl. done.
rewrite H12.
intros. 
apply lookup_map2 in x3. ssa. inv H13. 
inv H7. ssa. subst. 
de (mapP H10). subst. ssa.
rewrite makeQ_fe. done.
Qed.

Definition side_conds2  Ds Ps Ms P E Q := coherentG_env Ms /\  env_not_rec E /\  env_coherent E Q /\ both_closed P /\ only_schl E /\ only_var_val Ms /\ uniq (dom Q) /\ uniq (dom E) /\ sub_domLQ E Q /\ DefTyping Ds Ps /\ envP E uniq_labels /\ good_defs Ds.

Lemma from_LQ_red : forall E Q E' Q', uniq (dom E) -> uniq (dom Q) -> env_coherent E Q -> LQ_red E Q E' Q' -> E = E' /\ Q = Q' \/
exists s, weak_coherent (L_from_env (filter_keys (l_sess s) E)) (Q_from_env (filter_keys (q_sess s) Q)) /\
                                                         LQ_red2 (L_from_env (filter_keys (l_sess s) E)) (Q_from_env (filter_keys (q_sess s) Q))
                                                                  (L_from_env (filter_keys (l_sess s) E')) (Q_from_env (filter_keys (q_sess s) Q')) /\
                                                                              env_coherent (filter_keys (predC (l_sess s) ) E') (filter_keys (predC (q_sess s)) Q').
Proof.
move=> E Q E' Q' Hun HunQ.
intros.
inv H0. left. done.
right.
- exists s. con. de H. apply in_pair in H2 as Hin. apply (@map_f _ _ fst) in Hin. apply H5 in Hin. 
  apply in_dom_exists in Hin. ssa. apply H6 in H7.
  eapply weak_coherent_to_exists2. eauto. con.
  eapply LQ2'.
  apply/uniq_in_pair. 
  rewrite /L_from_env dom_map_keys. 
  rewrite map_inj_in_uniq. rewrite dom_filter_keys.
  apply filter_uniq. done. intro.
  intros. rewrite !dom_filter_keys !mem_filter in H4,H5. ssa. de x. de y. norm_eqs. eauto.

  apply in_pair in H1. apply/mapP. econ. apply/in_filter_keys2. eauto.  simpl. rewrite eqxx //=.
   simpl. done.
   
   apply/uniq_in_pair. 
  rewrite /Q_from_env dom_map_keys. 
  rewrite map_inj_in_uniq. rewrite dom_filter_keys.
  apply filter_uniq. done. intro.
  intros. rewrite !dom_filter_keys !mem_filter in H4,H5. ssa. de x. de y. norm_eqs. eauto.

   apply in_pair in H2. apply/mapP. econ. apply/in_filter_keys2. eauto. simpl. rewrite eqxx //=. simpl. eauto. 
   eauto.  
   rewrite filter_keys_update.
   rewrite /L_from_env /update /map_keys -!map_comp. 
   apply/eq_in_map.
   intro. ssa. case_if;ssa.  norm_eqs. rewrite H5 eqxx //=.
   de x. de s0. case_if. norm_eqs.
   apply in_filter_keys in H4. ssa. done.
   case_if. norm_eqs. 
   apply in_filter_keys in H4. ssa. norm_eqs. done.

   rewrite filter_keys_update.
   rewrite /Q_from_env /update /map_keys -!map_comp. 
   apply/eq_in_map.
   intro. ssa. case_if;ssa.  norm_eqs. rewrite H5 eqxx //=.
   de x. de q. case_if. norm_eqs.
   apply in_filter_keys in H4. ssa. norm_eqs. done.


   inv H. ssa.  rewrite !filter_keys_update. rewrite !update_none.



   exists (remove x s). exists x0. ssa.

   rewrite /check_gs in H4.

   rewrite /check_gs. ssa. intros. apply lookup_filter2 in H9. ssa. 
   rewrite /remove dom_filter_keys. apply filter_uniq. done.
   intro. intros. apply lookup_filter2 in H8. ssa. eauto. 
   intros. rewrite dom_filter_keys mem_filter in H8. ssa.
   move : H9. tunf. intros. rewrite /remove dom_filter_keys mem_filter. ssa.
   eauto.
   
   intros. apply lookup_filter2 in H8. ssa.
   apply H7 in H9. 
   rewrite !filter_keys2. 
   erewrite filter_keys_eq.
   erewrite (@filter_keys_eq _ _ Q). eauto.
   intro. intros. tunf. rewrite /q_sess //=. de x1. destruct (eqVneq s1 s0). subst. ssa. ssa.
   intro. intros. tunf. rewrite /l_sess //=. de x1. destruct (eqVneq s1 s0). subst. ssa. ssa.

   rewrite dom_filter_keys //= mem_filter. tunf.  rewrite negb_and negb_involutive.  ssa.
   rewrite dom_filter_keys //= mem_filter. tunf.  rewrite negb_and negb_involutive.  ssa.
   

- right. exists s. con. de H. move : H1 H2 H3 H4 H5 H6 H7 => Hall H1 H2 H3 H4 H5 H6.
  apply in_pair in H2 as Hin. apply (@map_f _ _ fst) in Hin. apply H5 in Hin. 
  apply in_dom_exists in Hin. ssa. apply H6 in H7.
  eapply weak_coherent_to_exists2. eauto. 

move : H1 H2 H3 H4 => Hall H1 H2 H3.
con.
  eapply LQ3'. 
2: {   apply/uniq_in_pair.   rewrite /L_from_env dom_map_keys. 
  rewrite map_inj_in_uniq. rewrite dom_filter_keys.
  apply filter_uniq. done. intro.
  intros. rewrite !dom_filter_keys !mem_filter in H4,H5. ssa. de x. de y. norm_eqs. eauto.

  apply in_pair in H1. apply/mapP. econ. apply/in_filter_keys2. eauto.  simpl. rewrite eqxx //=.
   simpl. done. } 
2: {
   
   apply/uniq_in_pair.
  rewrite /Q_from_env dom_map_keys. 
  rewrite map_inj_in_uniq. rewrite dom_filter_keys.
  apply filter_uniq. done. intro.
  intros. rewrite !dom_filter_keys !mem_filter in H4,H5. ssa. de x. de y. norm_eqs. eauto.

   apply in_pair in H2. apply/mapP. econ. apply/in_filter_keys2. eauto. simpl. rewrite eqxx //=. simpl. eauto. }

2:eauto. done.

   rewrite filter_keys_update.
   rewrite /L_from_env /update /map_keys -!map_comp. 
   apply/eq_in_map.
   intro. ssa. case_if;ssa.  norm_eqs. rewrite H5 eqxx //=.
   de x. de s0. case_if. norm_eqs.
   apply in_filter_keys in H4. ssa. done.
   case_if. norm_eqs. 
   apply in_filter_keys in H4. ssa. norm_eqs. done.

   rewrite filter_keys_update.
   rewrite /Q_from_env /update /map_keys -!map_comp. 
   apply/eq_in_map.
   intro. ssa. case_if;ssa.  norm_eqs. rewrite H5 eqxx //=.
   de x. de q. case_if. norm_eqs.
   apply in_filter_keys in H4. ssa. norm_eqs. done.


   inv H. ssa.  rewrite !filter_keys_update. rewrite !update_none.



   exists (remove x s). exists x0. ssa.

   rewrite /check_gs in H4.

   rewrite /check_gs. ssa. intros. apply lookup_filter2 in H9. ssa. 
   rewrite /remove dom_filter_keys. apply filter_uniq. done.
   intro. intros. apply lookup_filter2 in H8. ssa. eauto. 
   intros. rewrite dom_filter_keys mem_filter in H8. ssa.
   move : H9. tunf. intros. rewrite /remove dom_filter_keys mem_filter. ssa.
   eauto.
   
   intros. apply lookup_filter2 in H8. ssa.
   apply H7 in H9. 
   rewrite !filter_keys2. 
   erewrite filter_keys_eq.
   erewrite (@filter_keys_eq _ _ Q). eauto.
   intro. intros. tunf. rewrite /q_sess //=. de x1. destruct (eqVneq s1 s0). subst. ssa. ssa.
   intro. intros. tunf. rewrite /l_sess //=. de x1. destruct (eqVneq s1 s0). subst. ssa. ssa.

   rewrite dom_filter_keys //= mem_filter. tunf.  rewrite negb_and negb_involutive.  ssa.
   rewrite dom_filter_keys //= mem_filter. tunf.  rewrite negb_and negb_involutive.  ssa.
Qed.


Lemma env_coherent_filter : forall E Q p, env_coherent E Q -> env_coherent (filter_keys (predC (l_sess p)) E)
         (filter_keys (predC (q_sess p)) Q).
Proof.
intros.

  inv H. ssa.  



   exists (remove x p). exists x0. ssa.
   move : H0 => H4.

   rewrite /check_gs in H4.

   rewrite /check_gs. ssa. intros. apply lookup_filter2 in H5. ssa. 
   rewrite /remove dom_filter_keys. apply filter_uniq. done.
   intro. intros. apply lookup_filter2 in H4. ssa. eauto. 
   intros. rewrite dom_filter_keys mem_filter in H4. ssa.
   move : H5. tunf. intros. rewrite /remove dom_filter_keys mem_filter. ssa.
   eauto.
   
   intros. apply lookup_filter2 in H4. ssa.
   apply H3 in H5. 
   rewrite !filter_keys2. 
   erewrite filter_keys_eq.
   erewrite (@filter_keys_eq _ _ Q). eauto.
   intro. intros. tunf. rewrite /q_sess //=. de x1. destruct (eqVneq s0 s). subst. ssa. ssa.
   intro. intros. tunf. rewrite /l_sess //=. de x1. destruct (eqVneq s0 s). subst. ssa. ssa.
Qed.

Lemma filter_keys_seq_update : forall (A B : eqType) (p : A -> bool) (E' E : seq (A * B)), filter_keys p (seq_update E E') = seq_update (filter_keys p E) E'.
Proof.
move=> A B p.  elim;ssa.
de a.
rewrite filter_keys_update H //. 
Qed.

(*Definition Q_same (A : eqType) (Q0 Q1 : seq (A * qType)) :=
(forall k : A, k \in dom Q0 <-> k \in dom Q1) /\
(forall (p : A) q q',
 lookup Q0 p = Some q -> lookup Q1 p = Some q' -> q = q').
*)
Lemma env_coherent_eq : forall E Q, uniq (dom E) ->  env_coherent E Q ->  only_schl E -> sub_domLQ E Q ->  EQ_same E E.
Proof.
move=> E Q Hun.
intros. con. done. intro. ssa. rewrite H2 in H3. inv H3. apply in_pair in H2 as Hinn.
apply/EQ2_refl.
inv H. ssa.
apply in_dom in H2.  rewrite /sub_domLQ in H1.
rewrite /only_schl in H0. apply (allP H0) in H2 as Hc. de p.
apply H1 in H2. apply H6 in H2. apply in_dom_exists in H2. ssa. apply H7 in H2.
apply weak_coherent_to_exists2 in H2.
eapply weak_coherent_lInv.  eauto.
apply/uniq_in_pair. 
rewrite /L_from_env.

 rewrite dom_map_keys dom_filter_keys.
rewrite map_inj_in_uniq. rewrite /filter_keys. apply filter_uniq. done.
intro. intros. 
rewrite !mem_filter in H8 H9. ssa. de x2. de y. norm_eqs. done.
instantiate (1:= p). rewrite /L_from_env.
apply/mapP. econ. apply in_filter_keys2. eauto. ssa. ssa.
Qed.

Lemma env_coherent_lInvPred : forall E Q p T, uniq (dom E) ->  env_coherent E Q ->  only_schl E -> sub_domLQ E Q -> lookup E p = Some T -> lInvPred T. 
Proof.
move=> E Q p T Hun. intros. move : H2 => Hlook.
intros. apply in_pair in Hlook as Hinn.
inv H. ssa.
apply in_dom in Hlook.  rewrite /sub_domLQ in H1.
rewrite /only_schl in H0. apply (allP H0) in Hlook as Hc. de p.
apply H1 in Hlook. apply H4 in Hlook. apply in_dom_exists in Hlook. ssa. apply H5 in H6.
apply weak_coherent_to_exists2 in H6.
eapply weak_coherent_lInv.  eauto.
apply/uniq_in_pair. 
rewrite /L_from_env.

 rewrite dom_map_keys dom_filter_keys.
rewrite map_inj_in_uniq. rewrite /filter_keys. apply filter_uniq. done.
intro. intros. 
rewrite !mem_filter in H8 H9. ssa. 
rewrite /l_sess in H10.
de x2. de y. norm_eqs. 
rewrite mem_filter in H7. ssa. de y. norm_eqs. 
rewrite mem_filter in H7. ssa. norm_eqs. done.

instantiate (1:= p). rewrite /L_from_env.
apply/mapP. econ. apply in_filter_keys2. eauto. ssa. ssa.
Qed.

Lemma uniq_pres_red : forall E Q E' Q', LQ_red E Q E' Q' -> uniq (dom E) -> uniq (dom E').
Proof.
intros. inv H. rewrite dom_update. done. rewrite dom_update. done.
Qed.

Lemma uniq_pres_only : forall E Q E' Q', LQ_red E Q E' Q' -> only_schl E -> only_schl E'.
Proof.
intros. 
inv H. rewrite /only_schl.
rewrite dom_update. done.
rewrite /only_schl.
rewrite dom_update. done.
Qed.

Lemma pres_dom_same : forall E Q E' Q', LQ_red E Q E' Q' -> dom E = dom E' /\ dom Q = dom Q'.
Proof.
intros. inv H. rewrite !dom_update. ssa. rewrite !dom_update. ssa.
Qed.

Lemma env_coherent_not_rec : forall E Q (Hun : (uniq (dom E))), env_coherent E Q -> only_schl E -> sub_domLQ E Q ->  env_not_rec E.
Proof.
intros. inv H. ssa. apply/allP. intro.
de x1. apply uniq_in_pair in H6 as Hlook;ssa.
ssa. 

apply (@map_f _ _ fst) in H6. apply (allP H0) in H6 as HH. ssa. destruct s. done. apply H1 in H6. apply H4 in H6.
apply in_dom_exists in H6. ssa. apply H5 in H6. inv H6. ssa. inv H9.
have : lookup (filter_keys (l_sess s) E) (schlT s p) = Some s0.
apply lookup_filter. ssa. done.
intros. apply in_pair in x3. eapply map_f in x3. rewrite /L_from_env /map_keys in H11.
move : x3.
instantiate (1:= (fun kv : sch_eqType * lType_EqType =>
           (match kv.1 with
            | var_sch _ => Ptcp 0
            | schlT _ p => p
            end, kv.2))).
rewrite H11. ssa. de (mapP x3). inv H13. ssa.
asimpl. ssa.
de x4. 
apply not_erec_makeL. 
inv H7. ssa. subst. de (mapP H10). inv H18.
apply:lcontractive_full_eunf.
apply proj_lcontractive.
Qed.

(*only assert dom E'' is unique in conclusion, because this information is otherwise lost*)
Lemma env_coherence_pres  : forall E Q E' Q' (Hr : env_not_rec E), only_schl E -> sub_domLQ E Q -> uniq (dom E) -> uniq (dom Q) -> LQ_red E Q E' Q' -> env_coherent E Q -> exists E'', env_coherent E'' Q' /\ EQ_same E'' E' /\ uniq (dom E'') /\ env_not_rec E''. (* /\ Q_same Q'' Q'.*)
Proof.
move=> E Q E' Q' Hr Honly_s Hsub.
intros. remember H1 as HLQ. clear HeqHLQ.
apply from_LQ_red in H1;ssa. de H1.
- subst. exists E'. ssa. apply/env_coherent_eq;eauto.
- 
apply coherence_pres in H3;ssa.
  exists ((filter_keys (predC (l_sess x)) E')++ (map_keys (fun p => schlT x p ) x0)). 
(*  exists ((filter_keys (predC (q_sess x)) Q')++ ((filter_keys (q_sess x) Q'))). *)

 * clear H2.
   inv H3. inv H4. ssa. inv H2.
   exists ((x,x5)::(remove x2 x)). 
   exists (fun s => if s.1 == x then if s.2 \in dom x1 then x4 s.2 else nil else x3 s).
  ssa. rewrite /check_gs. con.
  ssa. 
  destruct (eqVneq x s). subst. 
  rewrite /dom -map_comp. case_if.
  de (mapP H13). subst. 
  apply checkPath_fe2.
  apply H10. 
  apply/uniq_in_pair.
  rewrite /dom -map_comp. rewrite map_inj_uniq. done. intro. ssa. inv H18.


  apply/mapP. econ. eauto. 
  rewrite lookup_cons_eq in H16. ssa. inv H16. done. de p.
  rewrite /check_gs in H6. ssa. apply H6.
  rewrite lookup_cons_neq in H16. 
  rewrite lookup_remove_neq2 in H16;ssa.
  ssa. 

  inv H6. ssa.
  rewrite /remove dom_filter_keys mem_filter negb_and eqxx //=. 
  rewrite /remove dom_filter_keys. apply filter_uniq. done.
  

  intro. ssa. destruct (eqVneq x k). subst. rewrite lookup_cons_eq in H16. ssa. inv H16. ssa.
  rewrite lookup_cons_neq in H16. 
  rewrite lookup_remove_neq2 in H16;ssa.
  eauto. done. 
  intros. 
  destruct (eqVneq s x). subst. done.
  rewrite inE. apply/orP. right. 

  rewrite /remove dom_filter_keys mem_filter i. ssa.
  eapply H8. 
(*  rewrite dom_cat mem_cat in H16.  de (orP H16). eauto.*)
(*  rewrite dom_filter_keys mem_filter in H17. ssa. rewrite (eqP H18) eqxx //= in i.*)

(*  rewrite dom_cat in H16.*)
  rewrite dom_filter_keys mem_filter. ssa. eauto.


**
  intros. destruct (eqVneq s x). subst. rewrite lookup_cons_eq in H16. ssa. inv H16.
  econ. con. exists x6. con. done. con. econ. con. done. done.
  con. 
  rewrite /can_split. con. 
  intros. apply in_dom in H13 as Hin. rewrite Hin.
  inv H10. apply H17. done.
  intros. rewrite (negbTE H13). done.


  rewrite /split_set. f_equal.


  inv H11. (*important*)
have: 

 makeLs
    (list_map (fun p : fin => (Ptcp p, fe (trans (Ptcp p) G))) x6)
    (fun p : ptcp =>
     if
      p
        \in dom
              (list_map
                 (fun p0 : fin =>
                  (Ptcp p0, fe (trans (Ptcp p0) G))) x6)
     then x4 p
     else [::]) =  makeLs
    (list_map (fun p : fin => (Ptcp p, fe (trans (Ptcp p) G))) x6) x4.

rewrite /makeLs -!map_comp. apply/eq_in_map. intro. ssa. f_equal.
case_if;ssa. exfalso. 
move/negP : H17. move=>HH. apply HH.
rewrite /dom -map_comp. apply/mapP. econ. eauto. done.
move=>->.
rewrite filter_keys_cat filter_keys2.
erewrite filter_keys_eq. erewrite filter_keys_pred0.
simpl.
erewrite filter_keys_eq. erewrite filter_keys_predT.
rewrite /L_from_env /seq_update /map_keys /makeLs -!map_comp.
apply/eq_in_map.
intro. ssa. move=> x0. rewrite dom_map_keys. rewrite /makeLs /dom -!map_comp.
move/mapP. case. intros. subst. ssa. rewrite eqxx. done.
ssa. tunf. destruct (l_sess x x0);ssa.

inv H11. rewrite H18.


have:   makeQs (list_map (fun p : fin => (Ptcp p, fe (trans (Ptcp p) G))) x6)
    (fun p : ptcp =>
     if p \in dom (list_map (fun p0 : fin => (Ptcp p0, fe (trans (Ptcp p0) G))) x6)
     then x4 p
     else [::]) =   makeQs (list_map (fun p : fin => (Ptcp p, fe (trans (Ptcp p) G))) x6) x4.
rewrite /makeQs -!map_comp. apply/eq_in_map. intro. ssa. f_equal.
case_if;ssa. exfalso. 
move/negP : H17. move=>HH. apply HH.
rewrite /dom -map_comp. apply/mapP. econ. eauto. done.
move=>->. done. done.






** rewrite lookup_cons_neq in H16;ssa.
   rewrite lookup_remove_neq2 in H16;ssa.

   apply H9 in H16.
   rewrite filter_keys_cat. 

   have : filter_keys (l_sess s) (map_keys (schlT x) x0) = nil.
   erewrite filter_keys_eq. erewrite filter_keys_pred0. done.
   move=> x7. rewrite dom_map_keys. rewrite /dom -map_comp. move/mapP. case. intros. subst. ssa.
   tunf. apply/negP. apply/negP. rewrite neg_sym. done.
   move=>->.  rewrite cats0.
   have : (Q_from_env (filter_keys (q_sess s) Q')) = 
(Q_from_env
             (filter_keys (q_sess s) (filter_keys (predC (q_sess x)) Q'))).
   rewrite /Q_from_env.
   rewrite filter_keys2.
 f_equal.

apply/filter_keys_eq. intro. ssa. tunf. 
rewrite /q_sess.  de x7. destruct (eqVneq s0 s). subst. ssa. ssa.
move=>->. eauto. rewrite neg_sym. done.

rewrite neg_sym. done.




con.
intros. 

have : forall k, k \in dom (map_keys (schlT x) x0) <-> k \in dom (filter_keys (l_sess x) E').
intros. inv H5. clear H13. 
rewrite dom_map_keys dom_filter_keys mem_filter.
split. move/mapP. case. move=> x5. rewrite H12. 
rewrite /dom /L_from_env /map_keys -!map_comp. 
move/mapP. case. intros. subst. apply in_filter_keys in p. ssa.
rewrite /l_sess in H13. de x6. de s. norm_eqs. apply/mapP. econ. eauto. done.
ssa. apply/mapP.
rewrite /l_sess in H14. de k0. norm_eqs.
 econ. apply/H12. 2:econ.
rewrite /L_from_env dom_map_keys. 
apply/mapP. econ. rewrite dom_filter_keys mem_filter. apply/andP. con. 2:eauto. ssa.
ssa.
move=>Heq. 

rewrite dom_cat. rewrite dom_filter_keys dom_map_keys mem_cat. 
move: (Heq k). rewrite dom_map_keys dom_filter_keys. move=> HH. 
rewrite mem_filter. 
split. ssa. de (orP H12). apply HH in H13. rewrite mem_filter in H13. ssa.
rewrite mem_filter in HH. intros. tunf. 
destruct (l_sess x k) eqn:Heqn. apply/orP. right.
simpl in HH. rewrite -HH in H12. done.
simpl. apply/orP. left. done.



intros.

destruct (p \in dom (filter_keys (predC (l_sess x)) E')) eqn:Heqn.
rewrite lookup_cat2 in H12;ssa.
apply lookup_filter2 in H12. ssa.  rewrite H13 in H14. inv H14. apply/EQ2_refl. 

eapply env_coherent_lInvPred. 2:eauto. rewrite dom_filter_keys. apply filter_uniq. 
apply:uniq_pres_red.  2:eauto. eauto.
apply uniq_pres_only in HLQ;ssa. rewrite /only_schl. rewrite dom_filter_keys all_filter.
apply/allP. intro. intros. apply/implyP. intros. apply (allP HLQ) in H15. done.
apply pres_dom_same in HLQ. ssa.
rewrite /sub_domLQ. move=> s p0. rewrite !dom_filter_keys !mem_filter. ssa.
rewrite /sub_domLQ in Hsub. rewrite -H16. apply Hsub. rewrite H15. done.
apply lookup_filter. 2:eauto. done.
(*apply Hsub.
apply:uniq_pres_only. 2:eauto. *)


rewrite lookup_cat in H12.
apply lookup_map2 in H12. ssa. inv H14.
inv H5. eapply H16. apply/uniq_in_pair. 


inv H3. ssa. inv H19. inv H17. ssa. subst.

rewrite /dom /makeLs -map_comp -!map_comp. rewrite map_inj_uniq. done. intro. ssa. inv H21.

instantiate (1:= x5.1). de x5.
apply/uniq_in_pair. 

rewrite /L_from_env dom_map_keys dom_filter_keys. 
rewrite map_inj_in_uniq. apply filter_uniq. apply pres_dom_same in HLQ. ssa. rewrite -H17. done.
intro. intros. rewrite !mem_filter in H17,H18. ssa. 
rewrite /l_sess in H20,H18. de x6. de y. norm_eqs. done.

apply in_pair in H13.
apply/mapP. econ. apply in_filter_keys2. eauto. simpl. rewrite eqxx //=. simpl. done.
rewrite dom_filter_keys mem_filter. ssa. rewrite negb_and. 
move : Heqn. rewrite dom_filter_keys mem_filter. move/negP. move/negP. rewrite negb_and. done.

rewrite dom_cat dom_filter_keys.
rewrite cat_uniq. ssa. apply filter_uniq. 
apply pres_dom_same in HLQ. ssa. rewrite -H12. done.
apply/hasPn. intro. rewrite dom_map_keys. move/mapP. case.
intros. subst. rewrite mem_filter negb_and. 
tunf. rewrite negb_involutive. rewrite /l_sess. rewrite eqxx. done.
rewrite dom_map_keys. rewrite map_inj_in_uniq. 
inv H11. 

inv H2. ssa. subst. 
rewrite /makeLs. rewrite /dom -!map_comp. 
rewrite map_inj_uniq.  done.
intro. ssa. inv H13.
intro. intros. inv H14.


have: uniq (dom (filter_keys (predC (l_sess x)) E' ++ map_keys (schlT x) x0)).
rewrite dom_cat dom_filter_keys.
rewrite cat_uniq. ssa. apply filter_uniq. 
apply pres_dom_same in HLQ. ssa. rewrite -H12. done.
apply/hasPn. intro. rewrite dom_map_keys. move/mapP. case.
intros. subst. rewrite mem_filter negb_and. 
tunf. rewrite negb_involutive. rewrite /l_sess. rewrite eqxx. done.
rewrite dom_map_keys. rewrite map_inj_in_uniq. 
inv H11. 

inv H2. ssa. subst. 
rewrite /makeLs. rewrite /dom -!map_comp. 
rewrite map_inj_uniq.  done.
intro. ssa. inv H13.
intro. intros. inv H14.
move=>Hun.

rewrite /env_not_rec.
rewrite all_cat. ssa.


apply: env_coherent_not_rec. 
rewrite dom_cat cat_uniq in Hun. ssa. eauto.
(*2:eauto.
rewrite dom_filter_keys. rewrite uniq
 apply filter_uniq.

Print env_coherent.


have: (filter_keys (predC (l_sess x)) E') = (filter_keys (predC (l_sess x)) E).
inv HLQ.

rewrite filter_keys_update. rewrite update_none. done.
rewrite dom_filter_keys mem_filter negb_and. ssa. apply in_pair in H12.
rewrite /predC. *)

apply/allP. intro. ssa. rewrite dom_filter_keys mem_filter in H12. ssa.
rewrite /predC in H13. 

apply pres_dom_same in HLQ. ssa. rewrite -H12 in H14. apply (allP Honly_s) in H14. done.


intro. ssa. rewrite dom_filter_keys mem_filter in H12. ssa.
rewrite /predC in H13.  rewrite dom_filter_keys mem_filter. ssa.
apply pres_dom_same in HLQ. ssa. rewrite -H15. rewrite -H12 in H14.

eauto.




apply/allP. intro. ssa. inv H11.
de (mapP H12). subst.
ssa. asimpl. ssa.
de (mapP H13). subst. ssa.

apply not_erec_makeL. 
inv H2. ssa. subst. de (mapP H14). inv H20. simpl.
apply:lcontractive_full_eunf.
apply proj_lcontractive.
Qed.



Lemma subject_reduction : forall D P P' Ms Ds E Q C, Sem D P P' -> side_conds Ds D Ms P E Q ->  OFT Ms Ds P E Q C ->  
exists E' Q', LQ_red E Q E' Q' /\ OFT Ms Ds P' E' Q' C.
Proof. 
move => D P P' Ms Ds E Q C Hsem Hside Hoft. 
elim : Hsem Ms E Q C Hside Hoft;intros. 
inv H. apply OFT_req in Hoft as Hoft'. de Hoft'.
inv Hoft. inv H7. inv H8. inv H9. inv H12.
econ. econ. con. apply/LQ1.  apply proj_trans in H21. subst.
econ. apply/weak_coherentP.
econ. exists (roles x). con. eauto. econ. econ. ssa.
rewrite makeLs_all_left. rewrite makeQs_all_left. 
instantiate (1 := map Ch (channels g)).
rewrite /dom -!map_comp /=.
inv H18. eapply lookup_uniq in H10. 2 : apply/H3. inv H10. clear H10.
econ. instantiate (3 := predT). econ. 
instantiate (3 := @hrel0 _ _). econ.
instantiate (3 := pred0). econ.
rewrite filter_keys_predT //=.
econ. 
instantiate (3 := predU (is_role n) (pred_dom (dom E) shiftL1 f0)). econ.
instantiate (3 := pred_dom2 (dom Q) shiftQ f1). econ.
rewrite /partition. rewrite filter_keys_pred0. instantiate (3 := f2). econ.

apply/OFT_weaken2. apply/OFT_subst. eauto. done.
apply good_subst2_insertL02. apply/injective_atP. eauto.
apply/injective_atP. eauto.
rewrite s_env_subst_id //=. 
inv Hside;ssa.
rewrite /insertL0 /insert_shift.
rewrite  /insertL1 /insert_shift  /insert filter_keys_cat map_keys_cat.  
f_equal. rewrite -!map_comp.
have:  ((fun x : ptcp * lType => (x.1, fe x.2)) \o (fun p : fin => (Ptcp p, fe (trans (Ptcp p) g))))
 =  (fun p : fin => (Ptcp p, fe (trans (Ptcp p) g))).  
fext. intros.  ssa.  rewrite full_eunf2. done.
move=>->.
erewrite filter_keys_map. ssa. rewrite /roles.
rewrite sort_uniq. 
apply/undup_uniq. eauto. 

rewrite filter_keys_map_keys.
rewrite map_keys2. asimpl. f_equal. 
apply/filter_keys_eq. intros.  tunf. ssa. 
rewrite is_role_shift /=.  rewrite pred_domP //=. eauto. econ.
done. econ. rewrite filter_q2.

erewrite filter_q_eq. 
erewrite filter_q_pred0_2.
rewrite dom_insertQ. rewrite -!map_comp.
rewrite map_cat. rewrite -!map_comp.
erewrite map_eq. 2 : { simpl. intros.  econ. } 
ssa. rewrite filter_keys_cat.
instantiate (1 := predC is_qkey).
erewrite filter_keys_eq. 
erewrite filter_keys_pred0. simpl.
erewrite filter_keys_eq. 
erewrite filter_keys_predT. 

rewrite /map_keys. ssa.
rewrite /filter_q. rewrite -map_comp. apply/eq_in_map. 
intro. ssa. f_equal.
erewrite filter_keys_eq. 
erewrite filter_keys_pred0. done.
ssa. 
apply/negP. intro. 
eapply qType_done_filter_q in H14. 2 : eauto. erewrite H14 in H10. done. done.
ssa. rewrite /dom -map_comp in H5. de (mapP H5). subst. tunf. 
rewrite is_qkey_shift //=.
ssa. rewrite /dom -map_comp in H5. de (mapP H5). subst. ssa. 
ssa. rewrite !filter_q2. rewrite predC2.
rewrite filter_q_pred0_2.
rewrite dom_insertQ -!map_comp map_cat filter_keys_cat. rewrite qType_done_cat. ssa.
rewrite -!map_comp. erewrite map_eq. 2: { simpl. intros. econ. } 
erewrite filter_keys_eq. erewrite filter_keys_predT. 
apply/allP. ssa. intro. ssa. destruct (mapP H5). ssa. rewrite H10.  done. 
ssa. rewrite /dom -map_comp in H5.  de (mapP H5). subst. done. 
erewrite filter_keys_eq. erewrite filter_keys_pred0. done.
ssa. rewrite /dom -!map_comp in H5. de (mapP H5). subst. 
rewrite is_qkey_shift //=.

apply partition_right in H8. rewrite -H8 in H16. 


clear H24. rewrite filter_q2. 
erewrite filter_q_eq. erewrite filter_q_pred0_2. rewrite dom_insertQ. 
rewrite !map_cat. rewrite -!map_comp. 
erewrite (@map_eq _ _ (roles g) (comp _ _)). 2 : { simpl.  ssa. } 
erewrite (@map_eq _ _ Q).  
2 : { simpl. ssa.  } 
inv H22. ssa.
have :  predC (predU (is_role n1.+1) (pred_dom (dom E) shiftL1 f0))
        (schlT (var_schl 0) n1.+1) = false.
tunf. rewrite /is_role /= eqxx //=. move=>->. 
rewrite /insertL1 /insert_shift /insert filter_keys_cat. 
rewrite -!map_comp.
rewrite !filter_keys_map_keys. 
have : (filter_keys (predC f2) C) = nil. 
apply oft_no_coin in H16. de C. eapply accept_not_queue. eauto.
move => HH2. rewrite HH2 in H16. clear HH2.
erewrite filter_keys_eq. 
2 : { intros. simpl. instantiate (1 := predC (pred_dom (dom E) shiftL1 f0)).
      tunf. rewrite /dom -map_comp in H6. de (mapP H6). subst. 
      rewrite /is_role. 
de (eqVneq (schlT (var_schl 0) x0) (schlT (var_schl 0) n1.+1)).
inv e.  eapply lt_memI in H10. 2 : eauto. lia. } 
erewrite (@filter_keys_eq _ _ E).
2 : { intros. simpl. instantiate (1 := predC f0). tunf. ssa. rewrite is_role_shift /= pred_domP //=. 
eauto. }  
have : (filter_keys (predC (pred_dom (dom E) shiftL1 f0))
       (list_map (initL1 \o (fun p : fin => (Ptcp p, fe (fe (trans p g))))) l) ++
     map_keys shiftL1 (filter_keys (predC f0) E)) = 
         (insertL1 (filter_keys (predC f0) E) (map (fun p => (Ptcp p, fe (trans p g))) l)). 
rewrite /insertL1 /insert_shift /insert.
f_equal. rewrite -map_comp.  
erewrite filter_keys_eq. 
erewrite  filter_keys_predT. apply/eq_in_map. intro. ssa.
rewrite full_eunf2.  done.
ssa. rewrite /dom -map_comp in H6. de (mapP H6). subst. 
tunf.  rewrite /pred_dom. apply/hasPn. intro. 
ssa. rewrite negb_and.  de x.  de s. 
move=>->. 
remember (filter_keys (predC f0) E) as E'. 
apply side_conds_to in Hside. 
have : side_conds Ds D0 Ms R E' Q.
subst.  inv Hside. rewrite /side_conds.  ssa. 

by apply env_not_rec_f.
apply partial_balanced_f. done.
apply only_schl_f. done.
apply uniq_filter_keys. done.
apply sub_domLQ_f. done.
clear Hside=>Hside.
clear HeqE'. clear H7 H12 f0. clear E Hoft.

apply/OFT_weaken2. 
2 : { econ. instantiate (2 := predC (is_qkey)). simpl.  
rewrite filter_keys_cat.
erewrite filter_keys_eq.
erewrite filter_keys_pred0. simpl. 
erewrite filter_keys_eq.
erewrite filter_keys_predT. simpl. eauto.
ssa.
rewrite /dom -map_comp in H6. de (mapP H6). subst. 
tunf. rewrite is_qkey_shift //=.
ssa. tunf. rewrite /dom -map_comp in H6. de (mapP H6). subst. 
rewrite /is_qkey //=. 

apply qType_done_filter_keys. rewrite /qType_done. ssa.
rewrite all_cat !all_map. ssa. apply/allP. intro. ssa. 
apply/allP. intro. ssa. } 

apply oft_qType_done in H16 as Hd. 
have :  (list_map (fun x : qkey * seq (ch * (value + fin)) => (shiftQ x.1, [::])) Q) = map_keys shiftQ Q. 
rewrite /map_keys //=.  apply/eq_in_map. intro. ssa.
apply (allP Hd) in H6. norm_eqs. rewrite H6.  done. 
move=>->.
clear H5 H13  H14 H9 H8  H18 H1  H H4 Hd.
clear H23 H22 H0. clear f1 f2. remember (var_val n0).  clear Heqv. clear n0 C. 

elim : H2 E' Q H16 Hside l H10 H3;ssa. 
inv H16.  
apply proj_trans in H7. subst. 
inv H4. eapply lookup_uniq in H1. 2 : {  apply/H3. } 
inv H1. clear H1. inv H10. ssa.

apply/OFT_subst. eauto. done.
apply good_subst2_insertL02. apply/injective_atP. eauto. apply/injective_atP. eauto.
rewrite s_env_subst_id //=. 
inv Hside;ssa. 
rewrite /insertL0 /insert_shift.
rewrite  /insertL1 /insert_shift  /insert. ssa. rewrite /initL1.
ssa. f_equal. rewrite map_keys2. asimpl. done. ssa. done. 


(*IH case of link*)
inv H16. have : C1 = nil. de C1. intro. subst. clear H6. inv H10. 
have :  (insertL1 E' (list_map (fun p : fin => (Ptcp p, fe (trans p g))) (n.+1 :: l0))) = 
           (schlT (var_schl 0) (Ptcp n.+1),fe (trans n.+1 g))::(insertL1 E' (list_map (fun p : fin => (Ptcp p, fe (trans p g))) (l0))).
rewrite /insertL1. ssa.  move=>->.
have : Q = Q0. eapply partition_first. 2 : eauto. apply/oft_qType_done. apply/H16. ssa.
eapply accept_not_queue. eauto. intros. 
subst. 
have : Q0 = Q1. eapply partition_right. eauto.  apply/oft_qType_done. apply/H16. ssa.
eapply accept_not_queue. eauto. intros. 
subst. 
inv H4. have : qType_done (map_keys shiftQ Q1). rewrite qType_done_map_keys.
apply/oft_qType_done. apply/H16.  ssa. apply/accept_not_queue. eauto.
intros.  inv H9. inv H11. eapply lookup_uniq in H3.  2 : {  apply/H7. } inv H3. 
apply proj_trans in H15. subst.

econ. 


econ. econ. econ.

instantiate (1:= (fun x => false)).
instantiate (1:= (fun x _ => false)).

eapply partition_first in x. 2 : econ.  
erewrite <- x. simpl.

instantiate (3 := predU (is_role n.+1) (pred_dom (dom E') shiftL1 f0)). 


have : predU (is_role n.+1) (pred_dom (dom E') shiftL1 f0) (schlT (var_schl 0) n.+1) = true.
tunf. rewrite /is_role //= eqxx //=. 
move=>->. 
rewrite /insertL1 /insert_shift /insert !filter_keys_cat. 
erewrite filter_keys_eq. erewrite filter_keys_pred0. simpl. 
erewrite filter_keys_eq. 
2 : { 
intros. instantiate (1 := pred_dom (dom E') shiftL1 f0).  tunf. rewrite dom_map_keys in H1. de (mapP H1). subst. 
rewrite is_role_shift /=. done. } 
2 : { ssa. rewrite /dom -map_comp in H1. de (mapP H1). subst. 
tunf.  de (mapP H6).  subst. ssa. rewrite /is_role. apply/negP/negP. rewrite negb_or. ssa. 
apply/eqP=>HH. inv HH. eapply lt_memI in H2.  2 : eauto. lia.
apply/negP. intro.  rewrite /pred_dom in H12.  de (hasP H13). move/eqP: H18. de x1. de s. } 

apply/OFT_subst. eauto. done.
apply good_subst2_insertL02. apply/injective_atP. eauto. apply/injective_atP. eauto.
rewrite s_env_subst_id //=. 
inv Hside;ssa. ssa. f_equal.
rewrite map_keys2. asimpl. rewrite filter_keys_map_keys. f_equal. 
apply/filter_keys_eq.  intro. ssa.
rewrite pred_domP //=. eauto. done. done.
simpl.
have :  predC (predU (is_role n.+1) (pred_dom (dom E') shiftL1 f0)) (schlT (var_schl 0) n.+1) = false.
tunf. rewrite negb_or. apply/negP. intro. ssa. rewrite /is_role eqxx //= in H6. 
move=>->.  erewrite filter_q_none.
2 : { apply/Congruence.qType_done_filter_q. rewrite qType_done_map_keys. done. } 
erewrite filter_keys_eq.  
2 : { intros.  instantiate (1 := predC (pred_dom (dom E') shiftL1 f0)). 
tunf.  rewrite negb_or. rewrite /insertL1 /insert_shift /insert /dom -!map_comp map_cat mem_cat in H1. 
de (orP H1). rewrite -map_comp in H6. de (mapP H6). subst. 
rewrite /is_role. 
de (eqVneq (schlT (var_schl 0) x1) (schlT (var_schl 0) n.+1)).
inv e. eapply lt_memI in H2.  2 : eauto. lia.  
rewrite -map_comp in H6. de (mapP H6). subst. 
rewrite is_role_shift /=. done. } 
have : (filter_keys (predC (pred_dom (dom E') shiftL1 f0)) (insertL1 E' (list_map (fun p : fin => (Ptcp p, fe (trans p g))) l0))) = 
insertL1 (filter_keys (predC f0) E') (list_map (fun p : fin => (Ptcp p, fe (trans p g))) l0).
rewrite /insertL1 /insert_shift /env.insert /=.
 rewrite filter_keys_cat. f_equal. 
erewrite filter_keys_eq. erewrite filter_keys_predT. done. 
ssa.  rewrite /dom -!map_comp in H1. de (mapP H1). subst. 
tunf.  rewrite /pred_dom. ssa. apply/hasPn. intro. ssa. 
rewrite negb_and. de x0. de s. 
rewrite filter_keys_map_keys.  f_equal.  apply/filter_keys_eq. 
intro. ssa. tunf. rewrite pred_domP //=. eauto.
move=>->.
apply/H0. done. inv Hside. apply side_conds_to2 in Hside.
rewrite /side_conds. inv Hside. ssa.
apply env_not_rec_f. done.
apply partial_balanced_f. done. 
apply only_schl_f. done. apply uniq_filter_keys. done. apply sub_domLQ_f. done. eauto. eauto. eapply accept_not_queue. eauto. 


intros. tunf. fext. ssa. econ. done.

erewrite filter_keys_eq. erewrite filter_keys_pred0.
2 : solve_ph. 
erewrite filter_keys_eq. erewrite filter_keys_predT.
have : C = nil.
apply oft_no_coin in H16.  eapply partition_nil. rewrite /partition. erewrite <- H13. rewrite H16. done. 
eapply accept_not_queue. eauto. intros. subst. ssa. rewrite /insertC /insert_shift /env.insert /= cats0.
rewrite /initC. rewrite -map_comp. ssa. 

erewrite match_ch. 2 : eauto. 

apply make_queues_typing2.
apply uniq_make_cs. done.
apply Congruence.qType_done_filter_q. 
rewrite /insertQ /insert_shift /insert qType_done_cat. ssa.
rewrite /qType_done all_map //=. apply/allP. intro . ssa.
de (mapP H5). subst.  done. rewrite qType_done_map_keys. 
eapply oft_qType_done. apply/Hoft. ssa. eapply accept_not_queue. eauto. 
ssa. apply side_conds_to in Hside;ssa. inv Hside. 


(*Finish link case*)

(*Msg send*)
- inv Hoft.  inv H2. inv H3. inv H4. inv H7. 
  have : exists l, lookup Q (QKey s p) = Some l. 
  inv Hside.  
  destruct H1. destruct H5. destruct H6. destruct H8.
  destruct H9. destruct H12. destruct H13.
  move: H18. case. move=>H18 [] HDef [] Henv Hgood.

  apply lookup_filter2 in H16. ssa. apply in_pair in H19.
  rewrite /sub_domLQ in H18. eapply (@map_f _ _ fst) in H19.
  eapply H18 in H19. apply in_dom_exists in H19. eauto.  
  intros. de x. 

  econ. econ.  con. apply lookup_filter2 in H16 as Hf. destruct Hf. apply/LQ2. 
  eauto. eauto. econ. econ. econ.

 
  econ. instantiate (3 := f0). econ. instantiate (3 := @hrel0 _ _). econ. apply/H4.
  rewrite filter_q_update /=. 

   rewrite filter_keys_cat /= cats0. 
  rewrite -filter_q_update. 

   rewrite (@update_same _ _ Q);eauto.
   rewrite filter_keys_update. rewrite -H10.
   erewrite filter_q_eq2. eauto.  
   intros. ssa. 
   eapply qType_done_filter_q in H14. 2 : eauto. ssa. erewrite H14. done. done. inv Hside. ssa.
  rewrite filter_q_predT. clear H17.
  rewrite filter_keys_update.
  erewrite update_none. 
  eapply EvalE_pres in H. 2 : eauto.
  apply queue_add.
  rewrite filter_q_none in H11. 
 rewrite update_same.  done.  done. inv Hside. ssa. 
  erewrite filter_q_eq. eauto.
  intro. ssa. rewrite /predC. fext. ssa. rewrite /hrelC negb_involutive. done. done.
apply/in_dom.  eauto. 
  apply/negP. intro.  rewrite dom_filter_keys mem_filter in H1. ssa.
  apply lookup_filter2 in H16.  ssa.  rewrite /predC H1 in H5. ssa.
(*Finish value send*)

(*Msg send*)
- inv Hoft.  inv H1. inv H2. inv H3. inv H6. 
  move: H8 H12 H16 => H11 H14 Heq. move: H17 H18 => H16 H17.
  have : exists l, lookup Q (QKey s p) = Some l. 
  inv Hside. 
  destruct H0. destruct H4. destruct H5. destruct H8.
  destruct H9. destruct H12. destruct H13.
  move: H18. case. move=>H18 [] HDef [] Henv Hgood.
  ssa.
  apply lookup_filter2 in H14. ssa. apply in_pair in H19.
  rewrite /sub_domLQ in H18. eapply (@map_f _ _ fst) in H19.
  eapply H18 in H19. apply in_dom_exists in H19. ssa.  eauto.  
  intros. de x.

  econ. econ.  con. 
  apply lookup_filter2 in H14 as Hf. destruct Hf.  apply/LQ2. 
  eauto. eauto. econ. econ. econ.

  econ.  

instantiate (3 := predI f0 (fun c => c != schlT s' p')). econ. instantiate (3 := @hrel0 _ _). econ. apply/H3.
  rewrite filter_q_update /=. 

   rewrite filter_keys_cat /= cats0. 
  rewrite -filter_q_update. 

   rewrite (@update_same _ _ Q);eauto.
  rewrite /remove filter_keys_update filter_keys2 in H17. 
   rewrite filter_keys_update. 
   erewrite filter_q_eq2. 
  erewrite filter_keys_eq.  rewrite -H7. eauto.
  ssa. tunf. rewrite andbC //=. 
  ssa. eapply qType_done_filter_q in H11. 2 : eauto. ssa. rewrite H11. done. ssa. eauto.
  inv Hside. ssa. apply lookup_filter2 in H15. ssa.
  erewrite filter_keys_eq. 
  2 : { intros. instantiate (1 :=  predC (predI (fun c : sch => c != schlT s' p') f0)). 
        tunf. rewrite andbC //=.  } 
  

  rewrite filter_q_predT. 
 apply/queue_add2'. 5:eauto.
  erewrite lookup_update_neq. 2:eauto. econ. eauto. done. eauto.
  rewrite filter_keys_update. rewrite update_none.
  rewrite update_same.  
  erewrite filter_q_none in H10. eauto.
  erewrite filter_q_eq. eauto.
  ssa. rewrite /predC /hrelC. fext. intro. rewrite negb_involutive. done. done.
inv Hside. ssa.
  apply/negP. intro. rewrite dom_filter_keys mem_filter in H5. ssa.
  apply lookup_filter2 in H14. ssa. 
  rewrite /predC in H8.  rewrite H5 in H8. done.
(*Deleg finished*)

(*Label send*)
- inv Hoft.  inv H1. inv H2. inv H3. inv H6. 
  have : exists l, lookup Q (QKey s p) = Some l. 
  inv Hside.

  destruct H0. destruct H4. destruct H5. destruct H7.
  destruct H8. destruct H11. destruct H12.
  move: H17. case. move=>H17 []  HDef []  Henv Hgood.

  apply lookup_filter2 in H15. ssa. apply in_pair in H18.
  rewrite /sub_domLQ in H17. eapply (@map_f _ _ fst) in H18.
  eapply H17 in H18. apply in_dom_exists in H18. eauto.  
  intros. de x. 

  econ. econ.  con. apply lookup_filter2 in H15 as Hf. destruct Hf. apply/LQ2. 
  eauto. eauto. econ. eauto. econ. econ.

 
  econ. instantiate (3 := f0). econ. instantiate (3 := @hrel0 _ _). econ. apply/H3.
  rewrite filter_q_update /=. 

   rewrite filter_keys_cat /= cats0. 
  rewrite -filter_q_update. 

   rewrite (@update_same _ _ Q);eauto.
   rewrite filter_keys_update. rewrite -H9.
   erewrite filter_q_eq2. eauto.  
   intros. ssa. 
   eapply qType_done_filter_q in H13. 2 : eauto. ssa. erewrite H13. done. done. inv Hside. ssa.
  rewrite filter_q_predT. clear H16.
  rewrite filter_keys_update.
  erewrite update_none. 
  apply queue_add3. rewrite update_same.  
  erewrite filter_q_none in H10. eauto.
  erewrite filter_q_eq. eauto. intros. rewrite /predC /hrelC.  fext. intros. rewrite negb_involutive //.
  done.  inv Hside. ssa. apply/in_dom.  eauto. 
  apply/negP. intro.  rewrite dom_filter_keys mem_filter in H0. ssa.
  apply lookup_filter2 in H15.  ssa.  rewrite /predC H0 in H4. ssa.
(*Finish Label send*)  

- inv Hoft. inv H1. inv H2. inv H3. inv H6. inv H10.
  have : m = u.

  rewrite filter_q_none2 in H19;ssa.
   inv Hside. 

  destruct H0. destruct H4. destruct H5. destruct H7.
  destruct H9. destruct H11. destruct H15.
  move: H16. case. move=>H16 [] HDef [] Henv Hgood.

  de H4. de H4. move : H22 H23 => HBL HBQ.
  move : H13 H19 => HE HQ. subst. 

  remember HE as X. clear HeqX.
  remember HQ as X'. clear HeqX'.
  rewrite filter_keys2 in HE.
  apply lookup_filter2 in HE. de HE.
  apply lookup_filter_q_2 in HQ. ssa.

  apply HBL in H17. 
  apply HBQ in H21. 
  ssa.
 rewrite H21 in H17. inv H17. clear H17.

  eapply H4 in H21. 
  move: H21.  instantiate (1:= p).
  move=> HC.

  apply filter_keys_cons_p in H19 as Hp. ssa.  
  apply filter_keys_cons in H19 as HH. ssa.
  rewrite H17 in H19.
  suff : VSort m = VSort u. case. done. symmetry.
  inv Hside. 

  destruct H25. destruct H26. destruct H27. destruct H28.
  destruct H29. destruct H30. destruct H31. 
  move: H32. case=>H32 Hdef. 

  eapply balanced_can_step in H26 as HH. 
  destruct HH. apply H34. econ. econ.
  instantiate (1:= nil). done. simpl. eauto. 

  apply lookup_filter2 in X. ssa. eauto.
  econ.


  move=> HU. subst.
  econ. econ. con.
  apply lookup_filter2 in H13. destruct H13.
  rewrite filter_q_none2 in H19;last by [].
  apply/LQ3. 2:eauto. instantiate (1:=nil). ssa. rewrite cat0s. eauto. 
  econ. econ. econ.

  econ. 
  4: { apply/OFT_strength. apply/OFT_subst. eauto.
       have : (is_var_val v) \/ (is_bool v).
       inv H18. ssa. apply in_pair in H.
       inv Hside. ssa. exfalso. 
       rewrite /only_var_val in H11. eapply map_f in H. apply (allP H11) in H. ssa.
       ssa. ssa. intro.
       intro. ssa. de x.
       have : (s_env_subst (insertS0 Ms u) ids v..) = (v,u)::(s_env_subst Ms ids ids).
       rewrite /s_env_subst. rewrite /insertS0 /insert_shift /env.insert map_keys_cat filter_keys_cat /=. 
       have : is_var v. de v. move=>->. ssa. f_equal. rewrite map_keys2.
       f_equal. apply/map_keys_eq. 

       intro. intro. asimpl. done.
       move=>->.
       inv H. de n. rewrite lookup_cons_eq in H4;ssa. inv H4.
       de v. de v. con. rewrite lookup_cons_eq;ssa.
       rewrite lookup_insertS0_valBool in H4.
       asimpl. con.
       destruct v;ssa. de v. inv H18. 
       rewrite lookup_cons_neq //=. 
       rewrite s_env_subst_id;ssa.
       inv Hside. ssa.  asimpl. con.
       con. rewrite lookup_insertS0_val in H4.
       de v. de v.
       destruct (eqVneq n0 n). subst.
       rewrite lookup_cons_eq. ssa. subst.
       inv H18. rewrite H4 in H9. inv H9. ssa.
       rewrite lookup_cons_neq //=. 
       rewrite s_env_subst_id;ssa. inv Hside. ssa.

       de v. 
       have: (s_env_subst (insertS0 Ms u) ids (boolB b)..) = map_keys id Ms.
       rewrite /s_env_subst.

       rewrite /insertS0. rewrite /insert_shift. rewrite /env.insert map_keys_cat !filter_keys_cat.
       ssa. 
       erewrite filter_keys_eq. erewrite filter_keys_predT.
       rewrite map_keys2. 
       apply/map_keys_eq. intro. ssa.
       asimpl. done. ssa.
       rewrite map_keys2 in H4. 
       rewrite dom_map_keys in H4. de (mapP H4). subst. asimpl. 
       suff : is_var x0. move=>->. done.
       inv Hside. ssa. apply (allP H17) in H5. de x0.
       move=>->. rewrite map_keys_id.
       
       inv H. de n. rewrite lookup_cons_eq in H4;ssa. inv H4.
       rewrite lookup_insertS0_valBool in H4.
       asimpl. con. done. con. asimpl. con.
       rewrite lookup_insertS0_val in H4. done.

       apply/good_subst2_update.
       apply/good_subst2_filter_keys. asimpl.
       apply/good_subst2_var. apply/injective_atP. eauto. apply/injective_atP. eauto.
       econ. econ. econ. econ.
       intros.

       move : H.
       rewrite /s_env_subst.
       rewrite /insertS0. rewrite /insert_shift. rewrite /env.insert map_keys_cat.
       ssa. move :H. case_if.
       intros. inv H0. con.
       
       destruct (eqVneq v (var_valBool n)).
       rewrite lookup_cons_eq in H4. ssa. inv H4. inv H18. ssa.
       rewrite lookup_cons_neq in H4. 
       rewrite map_keys2 in H4. 
       apply lookup_filter2 in H4. ssa.
       erewrite lookup_map_eq_inj in H5. eauto. asimpl. done.
       asimpl. done. ssa. con.
       destruct (eqVneq v (valB (var_val n))).
       rewrite lookup_cons_eq in H4; ssa. con. subst.
       inv H18. inv H4.
       rewrite lookup_cons_neq in H4;ssa.
       apply lookup_filter2 in H4. ssa.
       rewrite map_keys2 in H5.
       erewrite lookup_map_eq_inj in H5. con. eauto.
       asimpl. done. asimpl. done.
       erewrite filter_keys_eq.
       erewrite filter_keys_predT.
       erewrite map_keys2.
       erewrite map_keys_eq. erewrite map_keys_id. eauto.
       intros. ssa. asimpl. done.
       ssa. rewrite map_keys2 in H0.
       rewrite dom_map_keys in H0. de (mapP H0).
       subst. asimpl. suff : is_var x0. move=>->. done.
       inv Hside. ssa. 
       apply (allP H16) in H4. de x0. } 
       4 : eauto.
       asimpl. rewrite map_keys_id. 
       rewrite /partition. rewrite update_filter_keys. f_equal.
       rewrite filter_keys_update.
  rewrite update_none. done. 
  apply in_dom in H13. apply/negP. intro.

  rewrite !dom_filter_keys in H13,H. 
rewrite mem_filter in H13. ssa. rewrite mem_filter in H. ssa.
  rewrite /predC in H5. rewrite H0 in H5. done.
  rewrite subst_qkey_id map_keys_id. 
  rewrite filter_q_none2;ssa.
   rewrite /partition_q.  f_equal. 
  instantiate (1 := f1).

  rewrite filter_q_update. 


  have: filter_keys (f1 (QKey s p')) l = nil.


have:   [seq x <- l | (f1 (QKey s p') \o fst) x] =   [seq x <- l | false].
 apply/eq_in_filter. intro. ssa.
  apply in_pair in H19.  apply in_filter_q in H19.
  have : x.1 \in dom ((i,inl (VSort u))::l). apply/mapP. econ.
  rewrite inE. apply/orP. eauto. done. 
  move=>HH. 
 apply (allP H19) in HH. apply/negP. intro. rewrite /hrelC H0 in HH. done.
  rewrite filter_pred0. done.
  move=>->. rewrite update_same. done.
apply in_dom in H19. rewrite dom_filter_q in H19.
  erewrite <- dom_filter_q in H19. apply in_dom_exists in H19.
  ssa. 
 rewrite H.
apply in_pair in H. apply (allP H12) in H. ssa. norm_eqs. done.
  rewrite dom_filter_q. inv Hside. ssa.
  rewrite filter_q_update.   
  rewrite filter_q_none2;ssa. 
  erewrite filter_keys_eq. erewrite filter_keys_predT. done.
  ssa. suff : f1 (QKey s p') x = false. rewrite /hrelC. move=>->. done.
  apply lookup_filter_q_2 in H19. ssa.
  have : x \in dom (filter_keys (hrelC f1 (QKey s p')) x0).
  rewrite H0. de (mapP H). 
  rewrite dom_filter_keys. rewrite mem_filter. ssa. 
  rewrite /hrelC in H5 *. 
  destruct (f1 _ _) eqn:Heqn;ssa. 
  rewrite subst_schli_id map_keys_id.  rewrite H8. 
  econ.


(*Finish value recive case; missing value equality (we need to define global type constraint via projection*)


- inv Hoft. inv H1. inv H2. inv H3. inv H6. inv H10.
  move : H20 H21=> Heq H20.

  have: VLT T' ptcp0 = VLT T'0 ptcp0.


  rewrite filter_q_none2 in H18;ssa.
  inv Hside. 

  destruct H0. destruct H4. destruct H5. destruct H7. destruct H9.
  destruct H11. destruct H15. 
  case: H16. move=>H16 [] HDef Henv.
  apply lookup_filter2 in H13. ssa. 


  eapply balanced_can_step in H4.
  3: { instantiate (4:= nil). simpl. apply H18.  }
  3:eauto. destruct H4. symmetry. apply H23. done. econ. done.
  econ.

  move=> MU. 

  apply lookup_filter2 in H13. move: H13. case. move=> Hf0 H13.
  remember H18. clear Heqe.
  rewrite filter_q_none in H18. 



  econ. econ. con.
  apply/LQ3.  instantiate (1:=nil). ssa. 
  eauto. eauto.  inv MU. econ. econ. econ.

  (*We must update environment entry (s',p') to the syntactic local type the receiver expects: T'0*)
  have : E = update E (schlT s' p') (fe T'').
  rewrite update_same //=. apply lookup_filter2 in H19. ssa.
  rewrite not_rec_eq;ssa. 
  inv Hside. ssa. move : H23 => Hgood.  apply in_pair in H0. apply (allP H5) in H0. done. inv Hside. ssa.
  move=>->. rewrite update_com.
  eapply OFT_EQ4.  rewrite !dom_update. inv Hside. ssa.
  6: {  apply/EQ2_sym. apply EQ2_eunfl2 in Heq. apply Heq. } 
  4: {  instantiate (1:= schlT s' p'). rewrite lookup_update_in.  rewrite not_rec_eq. done. inv Hside. ssa. move : H22 => Hgood. apply lookup_filter2 in H19. ssa.
        apply in_pair in H22.
        apply (allP H0) in H22. done. rewrite dom_update. apply lookup_filter2 in H19. ssa. apply in_pair in H0. apply/mapP. econ. eauto. done. } 
  econ.
  4: { apply/OFT_swap. apply/OFT_subst.  eauto.  done.

       intro. simpl. rewrite !inE. move=> a'. move/orP. case. 
       move/eqP. intro. subst. rewrite !inE. move/orP. case. move/eqP. intro. subst.
       asimpl. done. 
       rewrite dom_map_keys. rewrite dom_update. rewrite dom_filter_keys.
       move/mapP. case. move=> x. rewrite mem_filter. ssa. subst. asimpl in H. subst.
       apply lookup_filter2 in H19. ssa. rewrite /predC H0 in H. done. (*Nice, check this later*)
       rewrite dom_map_keys. rewrite dom_update. rewrite dom_filter_keys.
       move/mapP. case. move=> x. rewrite mem_filter. ssa. subst.
       move/orP : H. case. move/eqP. intro. subst. asimpl in H0. subst.
       apply lookup_filter2 in H19. ssa. rewrite /predC H4 in H. ssa.
       move/mapP. case. move=> x0. rewrite mem_filter. ssa. subst.
       asimpl in H0. subst. done. apply/injective_atP. eauto. apply/injective_atP. eauto.
       rewrite s_env_subst_id. done.
       inv Hside. ssa. econ. econ.  econ. 
       instantiate (1:= filter_keys (fun x : sch_eqType => f0 x ||  (x == schlT s' p')) (update (update E (schlT s' p') (fe T')) (schlT s p) (fe T))). 
       intro. rewrite filter_keys_update. 
       rewrite /insertL0 /insert_shift /insert. 
       rewrite /map_keys. rewrite -!map_comp map_cat -!map_comp.
       ssa. destruct (eqVneq (schlT s' p') lk). subst.
       rewrite lookup_cons_eq; ssa.
       apply lookup_filter2 in H19. ssa.
       have : schlT s p <> schlT s' p'. intro. rewrite H4 in Hf0.  rewrite /predC Hf0 in H. done.
       intro.
       rewrite lookup_update_neq2;ssa.  
       rewrite lookup_filter_keys_in. rewrite lookup_update_in //. 
       apply in_pair in H0. apply/mapP. econ. eauto. done.

       rewrite eqxx. lia. 
       apply/eqP. done.

       rewrite lookup_cons_neq.
       rewrite update_filter_keys.
       rewrite (@lookup_filter_keys _ _ _ _ f0). 
       rewrite filter_keys_update.
       rewrite filter_keys_update_not.
       rewrite /update. 
       rewrite (@map_eq _ _ _ _ (fun x : sch_eqType * lType_EqType => if x.1 == schlT s p then (x.1, fe T) else x)). eauto.
       ssa. asimpl. case_if;ssa. de x.
       apply lookup_filter2 in H19. ssa. rewrite /predC in H. apply/negP/negP. rewrite H //. 
       rewrite neg_sym in i0. rewrite (negbTE i0). lia. ssa.
       rewrite dom_map_keys /dom -map_comp.
       rewrite /insertL0 /insert_shift /insert.  ssa.
       apply/negP. intro. rewrite /map_keys -map_comp in H. asimpl in H. de (mapP H).
       asimpl in H4. de x. subst. apply in_update in H0.
       de H0. inv H0.
       apply lookup_filter2 in H19. ssa. rewrite /predC in H4. rewrite Hf0 in H4. done.
       apply in_filter_keys in H0. ssa. apply lookup_filter2 in H19. ssa.
       rewrite /predC H0 in H5. done.
       have: (list_map (subst_sch ids (schlT s' p').. \o fst) (map_keys shiftL0 (update (filter_keys f0 E) (schlT s p) (fe T)))) = 
(list_map fst (update (filter_keys f0 E) (schlT s p) (fe T))).
       rewrite /map_keys -map_comp. 
       apply/eq_in_map. intro. ssa. asimpl. done.
       move=>->.  have: (list_map fst (update (filter_keys f0 E) (schlT s p) (fe T))) = dom (update (filter_keys f0 E) (schlT s p) (fe T)). done. move=>->. rewrite dom_update.
       rewrite dom_filter_keys.
       apply/filter_uniq. inv Hside. ssa.
       rewrite dom_filter_keys. rewrite dom_update. apply/filter_uniq. rewrite dom_update. inv Hside. ssa. }

4:eauto.
   
rewrite update2.
rewrite /partition.  


f_equal. rewrite update_com.
f_equal. econ. inv MU. intro. inv H. apply lookup_filter2 in H19. ssa. rewrite /predC Hf0 in H0. done.

  rewrite /remove filter_keys2. rewrite update_com.
  rewrite !filter_keys_update.
  rewrite !update_none.
  apply/filter_keys_eq. intro. ssa. rewrite /predC /predI. 
  rewrite !negb_or. lia. 
  apply/negP. intro. rewrite dom_filter_keys mem_filter in H.
  ssa. rewrite /predC  /= in H0.  rewrite negb_or eqxx //=in H0. ssa.
  apply/negP. intro. rewrite dom_filter_keys mem_filter in H.
  ssa. rewrite /predC  /= in H0.  rewrite negb_or  //=in H0. rewrite Hf0 in H0. ssa.
  apply/negP. intro. rewrite dom_filter_keys mem_filter in H.
  ssa. rewrite /predC  /= in H0.  rewrite negb_or  //=in H0. rewrite eqxx in H0. ssa.
  intro. inv H. apply lookup_filter2 in H19. ssa. rewrite /predC Hf0 in H0. done.

  rewrite subst_qkey_id map_keys_id. rewrite /partition_q.
  instantiate (1 := fun _ _ => false).

  f_equal.

  rewrite filter_q_update. 
  rewrite update_same. 
  apply filter_q_eq2. intros.
  destruct (f1 x z) eqn:Heqn;ssa.
  symmetry. rewrite -Heqn. have : x = (x,y).1. done. move=>->.
  apply:(@qType_done_filter_q Q f1).
  done. done. done.

  rewrite filter_keys_pred0.
  destruct ( lookup (filter_q Q (fun=> xpred0)) (QKey s p'') ) eqn:Heqn.
  apply lookup_filter_q_2 in Heqn.
  ssa. subst.
  rewrite filter_keys_pred0. done. 
  apply in_dom in H18.
  rewrite -(@dom_filter_q _ (fun _ _ => false)) in H18. 
  exfalso. have : QKey s p'' \notin dom ( (filter_q Q (fun=> xpred0)) ).
  apply /negP. intro. apply in_dom_exists in H. ssa. rewrite H in Heqn. done.
  intro. apply/negP. apply/x.  apply : H18.
  apply/uniq_filter_q. inv Hside. ssa.
  rewrite (@filter_q_eq _ _ (fun _ _ => true)). 
  rewrite filter_q_predT.
  symmetry.
  rewrite update_filter_q.
  have : update Q (QKey s p'') l  = filter_q (update Q (QKey s p'') l) (fun _ _ => true). 
  


  symmetry. rewrite filter_q_predT. done.
  intros. symmetry. rewrite {1}x.
  apply/filter_q_eq2.
  intros. ssa. 
  apply in_update in H. de H. inv H.
  apply in_pair in H18. 
  have : z \in dom (QKey s p'', (i, inl (VLT T'0 ptcp0)) :: l).2. ssa.
  move=>HH. 
  move:(@qType_done_filter_q Q f1  _ z H12 H18 HH ).
  simpl. rewrite /hrelC. move=>->//.

  move: (@qType_done_filter_q Q f1 _ z H12 H H0).
  simpl. rewrite /hrelC /=. move=>->//.


  ssa.
  apply lookup_filter_q_2 in e. ssa.
  de (mapP H). 
  have : x1 \in  (i, inl (VLT T'0 ptcp0)) :: l. rewrite inE H5 orbC //=.
  rewrite -H0. move/in_filter_keys.
  ssa. subst. done.
  ssa.  rewrite subst_schli_id map_keys_id. rewrite H8. econ.
  apply lookup_filter2 in H19. ssa. apply in_pair in H0. inv Hside. ssa. apply (allP H5) in H0. 
  ssa. suff : lInvPred T'0. intros. punfold x. inv x. inv H. apply/EQ2_tree. eauto.  
  eapply labels_preserve. apply/EQ2_sym. apply/EQ2_eunfl2. apply Heq.
  inv Hside. ssa. apply:H21. eauto. apply lookup_filter2 in H19. ssa. eauto.
  intro. inv H. apply lookup_filter2 in H19. ssa. rewrite /predC Hf0 in H0. done.



  rewrite (@filter_q_eq _ _ f1). eauto.
  intros. rewrite /predC. fext. intros. rewrite /hrelC negb_involutive. done.


(*finish session reception*)
- inv Hoft. inv H2. inv H3. inv H4. inv H7. inv H11.

  have : size Ps = size Ts.
  move : H14. clear. elim : Ps Ts;ssa. de Ts.
  de Ts. inv H14. f_equal. eauto.
  move=>Hsize.
  apply in_pair in H.
  move/in_zip1 : H. move/(_ _ _ Hsize).
  case. move=> T0 [] HT Hzip. clear HT.
  econ. econ. con. 
  2: {  econ. 4:{  apply H16. instantiate (1:= T0.2).
                   apply/inP.
rewrite -zip_map2.  apply/mapP. econ. eauto. ssa. } 
        4: eauto. 
        instantiate (1:= f0).
        instantiate (1:= update E (schlT s p) (fe T0.2)).
        rewrite /partition. f_equal.
        rewrite filter_keys_update. f_equal.
        rewrite filter_keys_update. 
        rewrite update_none. done.
        apply/negP. rewrite dom_filter_keys mem_filter. 
        move/andP. ssa.
        apply lookup_filter2 in H15. ssa. rewrite /predC H1 in H. ssa.
        
        instantiate (1:= f1).
        instantiate (1:= update Q (QKey s p') l0).
        rewrite /partition_q. f_equal.
        rewrite filter_q_update.
        rewrite update_same. done.

  apply lookup_filter_q_2 in H20. ssa.
  have: forall x, x \in l0 -> hrelC f1 (QKey s p') x.1.
  suff:  forall x, x \in (i,inr l)::l0 -> hrelC f1 (QKey s p') x.1.
  ssa. apply x0. rewrite inE. rewrite H1. lia.
  move=> x1. rewrite -H. move/in_filter_keys.
  ssa. move=>HH2.

  erewrite filter_keys_eq. erewrite filter_keys_pred0.
  
  apply in_dom in H0.  
  erewrite <- dom_filter_q in H0.
  apply in_dom_exists in H0. ssa.
  erewrite H0. apply qType_done_nil in H0;ssa. subst. done.
  ssa.  de (mapP H1).
  apply HH2 in H5. ssa. rewrite /hrelC in H5. 
  subst. rewrite (negbTE H5). done.
  rewrite dom_filter_q. inv Hside. ssa.

  rewrite filter_q_update. f_equal.
  erewrite filter_keys_eq. erewrite filter_keys_predT. done.
  intro. intros. de (mapP H).

  have: forall x, x \in l0 -> hrelC f1 (QKey s p') x.1.
  suff:  forall x, x \in (i,inr l)::l0 -> hrelC f1 (QKey s p') x.1.
  ssa. apply x1. rewrite inE. rewrite H5 orbC //=. 
  move=> x1.  apply lookup_filter_q_2 in H20. destruct H20. destruct H5.
        rewrite -H5. move/in_filter_keys.
  ssa. move=>HH2.
        subst. apply HH2 in H0. rewrite H0. done.
        rewrite H6. econ. } 


  destruct T0.
  move/nthP : Hzip. move/(_ ((0,Inact),(0,EEnd))).
  case. move=> xi Hle Hnth.
  have : map snd (zip Ps Ts) = Ts.
  move: H14. clear. elim : Ps Ts;ssa. de Ts;ssa. de Ts.
  inv H14. f_equal. eauto.
  move=>Hsnd. 
  eapply lookup_filter2 in H15.  ssa.
  erewrite filter_q_none in H20.
  have : l = s0.
  rewrite nth_zip in Hnth;ssa. inv Hnth.
  have: nth 0 (map fst Ps) xi = l. erewrite nth_map. erewrite H5. ssa.
  rewrite size_zip Hsize minn_same -Hsize // in Hle.
  have: nth 0 (map fst Ts) xi = s0. 
  erewrite nth_map.
  erewrite H8. ssa.
  rewrite size_zip Hsize minn_same// in Hle.
  rewrite H14. move=>->. lia.
  intros. subst.
  apply/LQ3. instantiate (1:= nil). ssa.
  eauto. eauto.
  econ. 
  apply/nthP. econ. rewrite size_zip Hsize minn_same in Hle. apply Hle.
  rewrite nth_zip in Hnth;ssa. inv Hnth.
  eauto. done. done.
  erewrite filter_q_eq. eauto.
  intros. fext. intros. rewrite /predC /hrelC negb_involutive //.
   
- inv Hoft. econ. econ. con. con. done.
- inv Hoft. econ. econ. con. con. eauto.
- (*Process call*) inv Hoft. inv Hside. ssa.  move : H20 H21 => Henv Hgood. rewrite /DefTyping in H19.
  ssa. move : H20 H21 H22 => Hproc HDD H20. 
  inv H16.

  econ. econ. con.  con. 
  
  apply/OFT_strength. apply/OFT_weaken_swap_EQ. 
  apply/OFT_weaken2.
apply/OFT_subst.  
  apply/H20.
       instantiate (1:=L).
       instantiate (1:=m). 
       have: (m, L) = nth (SBool,nil) Ds defi.
       move: H8. clear.
       elim: Ds defi m L. case;ssa.
       move=> a l IH. case;ssa.
       inv H8. move=>->.
       rewrite -nth_zip //.
       apply/mem_nth. rewrite size_zip H19 minn_same -H19 //.
  eauto. 

       intro. ssa. inv H21.
       de n. rewrite lookup_cons_eq in H22;ssa. inv H22. asimpl.
       rewrite /insertS0 /insert_shift /insert /= /initS0.
       rewrite /s_env_subst. ssa.
       case_if. de v. econ. rewrite lookup_cons_eq. done. done.
       de v. con.
       rewrite lookup_cons_eq. done. done.
        de v. inv H. inv H7. inv H26. con. inv H7. con.  con.
       intro. ssa.
       de (mapP H21). de (mapP H22). subst.
       de x. de x0. de s. 
       apply dom_Ls_to_env in H21 as Hle. rewrite addn0 in Hle.
       de s0.  f_equal.
       apply dom_Ls_to_env in H22. rewrite addn0 in H22.
have  : nth (schlT (var_schl 0) 0) ss n \in ss. apply/mem_nth. rewrite H9. done.
 move=>Hnth.
have  : nth (schlT (var_schl 0) 0) ss n0 \in ss. apply/mem_nth. rewrite H9. done.
move=>Hnth2. apply/unique_nth.  4:eauto. rewrite H9 //. rewrite H9 //. done.
    asimpl in H23.
exfalso. apply/negP. apply/Ls_to_env_not_schlT. 5: { eauto. } 
exfalso. apply/negP. apply/Ls_to_env_not_schlT. 5:eauto.
done. done. econ. 

rewrite nn_test2. econ. done.
rewrite subst_qkey_id map_keys_id. econ.
rewrite subst_schli_id map_keys_id. con.

econ. erewrite filter_keys_pred0. done.
apply/qType_done_filter_keys. done.




intros. rewrite /dom zip1. done. done.  done.
intros. apply in_dom in H21 as HH. rewrite /dom zip1 in HH;ssa. apply H12 in HH.
apply in_dom_exists in HH. ssa. 
apply in_pair in H21.
eapply H17 in H21 as HH. exists x. ssa. eauto.
rewrite /good_defs in Hgood.
apply List.nth_error_In in H8.
move/inP : H8. move/Hgood. move=>/= HHH. 
apply mem_zip in H21. ssa. 
apply (allP HHH) in H21. ssa.
apply in_pair in H22. apply (allP H2) in H22. done.

apply lookup_filter. apply mem_zip in H21. ssa. done.
rewrite /dom zip1;ssa.

intro. ssa. 
apply List.nth_error_In in H8. move/inP : H8.
move/Hgood. move=>HHH. ssa. apply in_pair in H21. apply mem_zip in H21.
ssa. apply (allP HHH) in H21. ssa.


  intros.
       rewrite /insertS0 /insert_shift /insert //= /s_env_subst in H21.
       ssa. move: H21. 

       case_if. intros. inv H22.
       de v. inv Hside. ssa. move : H35 => Hgood'. move : H34 => Henv'. inv H. inv H27.
       rewrite /valBool_closed in H35. ssa.
       move: (H35 n0). rewrite inE eqxx. done. con.

       de v. 

       de v. con.
       destruct (eqVneq n0 n);last by rewrite lookup_cons_neq in H23;ssa.
  rewrite e0 in H23. rewrite lookup_cons_eq in H23;ssa.
       inv H23.   inv H. inv H7. inv H26. intros. inv H22. con.

(*TODO:use preservation lemma instead of repeating long proof*)
- (*Channel restriction*) inv Hoft. 
  apply H0 in H5. 
  2: { 

    inv Hside. ssa. move: H13 H14 => Henv Hgood. con;ssa. 
    apply/allP. intro. ssa. asimpl.
    rewrite /insertL1 /insert_shift /insert mem_cat in H13.
    move/orP : H13. case. move/mapP. case.
    ssa. subst.
    inv H2. ssa. inv H15. de (mapP p). subst.
    ssa. apply/not_erec_makeL.
    inv H13. ssa. subst. 
    de x2. 
    de (mapP H16). inv H21. 
    apply/lcontractive_full_eunf.
    apply/proj_lcontractive. rewrite /map_keys.
    case/mapP. ssa. subst. ssa. apply (allP H3) in p. done.
    inv H4. ssa. subst.
    econ. econ. econ. econ. econ.

    2: {  con. 
    instantiate (1:= insertL1 x E1). 
     
    instantiate (1:= predU  (pred_dom (dom x) shiftL1 x0) (fun x => if x is schlT (var_schl 0) _ then true else false)).

    rewrite /insertL1 /insert_shift /insert. 
          rewrite filter_keys_cat.
f_equal.  erewrite filter_keys_eq. erewrite filter_keys_predT. done.
          ssa. tunf. rewrite /dom -map_comp in H14. de (mapP H14). subst.
          rewrite orbC //=.
          rewrite map_keys_filter_keys;ssa.
    erewrite filter_keys_eq.  eauto.
          ssa. tunf. rewrite dom_map_keys in H14. de (mapP H14). subst.
          rewrite pred_domP;ssa. rewrite /shiftL1. de x4;ssa. rewrite orbC //.
          de s. rewrite orbC //=.

          rewrite -filter_q_insertQ_f_aux. econ. } 
      rewrite /balanced in H13 *. ssa.
    inv H2. ssa. inv H19.
    inv H17.


 exists (((var_schl 0,x7))::(map_keys (subst_schl (succn >> ids)) x3)).
 exists (fun lk => match lk with | (var_schl n,p) => if n is n.+1 then x4 (var_schl n,p) else x6 p end).
destruct H20. destruct H20. destruct H21. 
case: H22. move=>Hun Hsub.
ssa. con.
 intro. ssa.


    destruct s. destruct n. 
    rewrite lookup_cons_eq in H22. ssa. inv H22.
     apply/ checkPath_EQ2. instantiate (1:= fe (trans p g)). apply/EQ2_eunfl2.
    apply/EQ2_refl. apply/gInvPred_proj.
    inv H20. ssa. 
    move : H25 H26 H27 => Hun' H25 Hgood'.
    move: (H25 (Ptcp 0)).
    case. intros.
    apply/gUnravel2_Rol. ssa.
    apply Project_gtree in p0. eauto.

    destruct (nat_of_ptcp p \in x8) eqn:Heqn.

    rewrite /can_split in H18. ssa.
    apply /H18.  subst.
    
    rewrite /checkPath. eapply lookup_map3.
    rewrite /dom -map_comp.
    rewrite map_inj_uniq. done.
    intro. ssa. inv H23. eauto.
    de p. 
    inv H20. destruct p. ssa.

    move : H25 H26 H27 => Hun' H25 Hgood'.

    have : projectable g. intro. de (H25 p). 
    move/proj_end. move=>HEnd. 
    have: n \notin roles g. 
    apply/negP. intro. apply Hsub in H26. rewrite Heqn in H26. done.
    move/HEnd. ssa. rewrite H27.
    inv H18. erewrite H29. ssa.
    rewrite /dom -map_comp.
    apply/negP. intro. de (mapP H30). inv H32.
    rewrite Heqn in H31. done. done. 
    rewrite lookup_cons_neq in H22;ssa.
    apply lookup_map in H22. ssa. subst. de x9. asimpl in H23. inv H23.
    
    apply H13. asimpl in H23.
    ssa. 
    ssa.
    apply/negP. intro. rewrite dom_map_keys in H22. de (mapP H22). de x9. 
    rewrite dom_map_keys.
    rewrite map_inj_uniq. inv H13. 
    intro. ssa. de x9. asimpl in H22. inv H22. de x10. inv H22.


    intro. ssa.
    destruct s. destruct n.
    
    rewrite /insertL1 /insert_shift /insert /= in H22. 
    destruct (nat_of_ptcp p \in x8) eqn:Heqn.

    rewrite lookup_cat2  in H22.
    apply lookup_map2 in H22. ssa.
    rewrite /initL1 in H23. inv H23.
    
    rewrite lookup_cons_eq. ssa. econ. con. econ. ssa.
    de (mapP H22). subst. ssa.
    de (mapP H21). subst. ssa. 
    rewrite -makeL_fe2. done. done. subst.
    inv H20.
    inv H18.
    rewrite /dom  /makeLs -!map_comp. apply/mapP. subst. econ.
    eauto.
    ssa. de p.
    rewrite lookup_cat in H22. apply lookup_map in H22. ssa.
    subst. de x9. de s. 
    rewrite /dom /makeLs -!map_comp. apply/negP. intro. de (mapP H22).
    subst. inv H24.
    de (mapP H23). subst. ssa. rewrite Heqn in H21. done.

    rewrite /insertL1 /insert_shift /insert /= in H22. 
    rewrite lookup_cat in H22. apply lookup_map in H22. ssa.
    subst. de x9. de s. asimpl in H23. inv H23.
    rewrite lookup_cons_neq //=. 
    apply H14 in H24. ssa.
    exists x5. ssa.
    have : var_schl n.+1 =  (subst_schl (succn >> VarInstance_schl)) (var_schl n). done.
    move=>->.
    rewrite -lookup_map_aux2. 
    rewrite /balancedL in H14.
    inv H20.
    intro. ssa. de x9. de x10. inv H25.
    apply/negP. intro.
    rewrite /dom /makeLs -!map_comp in H22. de (mapP H22).


    intro. ssa.
    destruct s. destruct n.
    
    rewrite /insertQ /insert_shift /insert /= in H22. 
    destruct (nat_of_ptcp p \in x8) eqn:Heqn.

    rewrite lookup_cat2  in H22.
    apply lookup_map2 in H22. ssa.
    rewrite /initL1 in H23. inv H23.
    
    rewrite lookup_cons_eq. ssa. econ. con. econ. ssa.
    de (mapP H22). subst. ssa.
    de (mapP H21). subst. ssa. 
    have: forall l p, makeQ p l = makeQ p (fe l). intros. rewrite makeQ_fe //.
    move=><-. done. done. subst.
    inv H20.
    inv H18.
    rewrite /dom  /makeLs -!map_comp. apply/mapP. subst. econ.
    eauto.
    ssa. de p.
    rewrite lookup_cat in H22. apply lookup_map in H22. ssa.
    subst. de x9. de s. 
    rewrite /dom /makeLs -!map_comp. apply/negP. intro. de (mapP H22).
    subst. inv H24.
    de (mapP H23). subst. ssa. rewrite Heqn in H21. done.

    rewrite /insertQ /insert_shift /insert /= in H22. 
    rewrite lookup_cat in H22. apply lookup_map in H22. ssa.
    subst. de x9. de s. asimpl in H23. inv H23.
    rewrite lookup_cons_neq //=. 
    apply H15 in H24. ssa.
    exists x5. ssa.
    have : var_schl n.+1 =  (subst_schl (succn >> VarInstance_schl)) (var_schl n). done.
    move=>->.
    rewrite -lookup_map_aux2. 
    rewrite /balancedL in H14.
    inv H20.
    intro. ssa. de x9. de x10. inv H25.
    apply/negP. intro.
    rewrite /dom /makeLs -!map_comp in H22. de (mapP H22).



(*coherent_gTypes*)
    intro. ssa. destruct k. destruct n. rewrite lookup_cons_eq in H22;ssa. inv H22.
    rewrite lookup_cons_neq in H22.
    apply lookup_map in H22. ssa. de x9. inv H23. eauto. done.
    rewrite /only_schl.
    rewrite /dom /insertL1 /insert_shift /insert /= map_cat all_cat. ssa.
    rewrite -map_comp.
    rewrite all_map. apply/allP. intro. ssa.
    rewrite /map_keys -map_comp.
    rewrite all_map. apply/allP. intro. ssa.
    rewrite /shiftL1. de x. de s.
    
    rewrite /only_schl in H7. apply (@map_f _ _ fst) in H13.
    apply (allP H7) in H13. done.



    rewrite /insertQ /insert_shift /insert /dom map_cat.
    rewrite cat_uniq. ssa. rewrite -map_comp /initQ.  
    have: (list_map (fst \o (fun pT : ptcp * qType => (QKey (var_schl 0) pT.1, pT.2))) Q1) = 
            map (fun p => QKey (var_schl 0) p) (dom Q1).
    rewrite /dom -map_comp. apply/eq_in_map. intro. ssa.
    move=>->. 
    rewrite map_inj_uniq.  inv H2. ssa. inv H15.
    rewrite /dom /makeQs -map_comp. 
    have:  (list_map (fst \o (fun x1 : ptcp * lType => (x1.1, makeQ (x0 x1.1) x1.2))) x) = dom x.
    rewrite /dom. apply/eq_in_map. intro. ssa.
    move=>->. inv H13. ssa. subst.
    have: (dom (list_map (fun p : fin => (Ptcp p, fe (trans (Ptcp p) x1))) x2)) = map Ptcp x2.
    rewrite /dom -map_comp. apply/eq_in_map. intro. ssa. 
    move=>->.  
    rewrite map_inj_uniq. done.
    intro. ssa. inv H17.
    intro. ssa. inv H13.

    apply/hasPn. intro. ssa.
    rewrite /map_keys -map_comp in H13. de (mapP H13). subst.
    apply/negP. intro. rewrite -map_comp in H15. de (mapP H15).
    de x0. de x. de q. de s.

    have:  (list_map fst (map_keys shiftQ Q)) = map shiftQ (dom Q).
    rewrite /map_keys /dom -!map_comp. apply/eq_in_map. intro. ssa.
    move=>->. 

    rewrite map_inj_uniq.   done. done.


    rewrite /insertL1 /insert_shift /insert /dom map_cat.
    rewrite cat_uniq. ssa. rewrite -map_comp /initQ. 
    have: (list_map (fst \o initL1) E1) = map (schlT (var_schl 0)) (dom E1).
    rewrite /dom -map_comp. apply/eq_in_map. intro. ssa.
    move=>->.
    rewrite map_inj_uniq.  
    inv H2. ssa. inv H15.
    rewrite /dom /makeLs -map_comp. 
    have:  (list_map (fst \o (fun x1 : ptcp * lType => (x1.1, makeL (x0 x1.1) x1.2))) x) = dom x.
    rewrite /dom. apply/eq_in_map. intro. ssa.
    move=>->. inv H13. ssa. subst.
    have: (dom (list_map (fun p : fin => (Ptcp p, fe (trans (Ptcp p) x1))) x2)) = map Ptcp x2.
    rewrite /dom -map_comp. apply/eq_in_map. intro. ssa. 
    move=>->.  
    rewrite map_inj_uniq. done.
    intro. ssa. inv H17.
    intro. ssa. inv H13.
    apply/hasPn. intro. ssa.
    rewrite /map_keys -map_comp in H13. de (mapP H13). subst.
    apply/negP. intro. rewrite -map_comp in H15. de (mapP H15).
    de x0. de s. de s. 


    have: (list_map fst (map_keys shiftL1 E)) = map shiftL1 (dom E).
    rewrite /map_keys /dom -!map_comp. apply/eq_in_map. intro. ssa.
    move=>->. 
    rewrite map_inj_uniq.   done. done.



    intro. ssa. rewrite dom_insertL1 mem_cat  in H13. de (orP H13).
    de (mapP H14). inv H16.
    rewrite dom_insertQ mem_cat. apply/orP. left.
    inv H2. ssa. inv H19. rewrite /dom /makeQs -!map_comp.
    rewrite /makeLs in H15. de (mapP H15). subst.
    apply/mapP. econ. eauto. done.
    de (mapP H14). de x. de s0. inv H16.
    rewrite /dom /insertQ /insert_shift /= /insert map_cat mem_cat. 
    apply/orP. right. asimpl. 
    apply H11 in H15. de (mapP H15).
    apply/mapP. econ.
    apply/mapP. econ. eauto. econ. ssa. de x. subst. done. 
    apply/env_insertL1;eauto. inv H2. ssa. inv H15. inv H13. ssa. subst.
    rewrite /dom /makeLs -!map_comp. 
    rewrite map_inj_uniq //=. intro. ssa. inv H17.
    intros.
    inv H2. ssa. inv H16. inv H14. ssa. subst. inv H17.
    ssa.  
    move : H23 H24 H5 => Hun H23 H24.
    rewrite /dom /makeLs -!map_comp in H13. 
    apply lookup_map2 in H13. ssa. inv H13.
    apply uniq_makeL.
    apply uniq_full_unf. apply uniq_trans. done.
} 



  ssa. inv H1.
 * econ. econ. con. 2: { econ. 2:eauto. done. } con.
 * destruct s. destruct n.
   rewrite update_insertL1_0 in H3.
   rewrite update_insertQ_0 in H3.
   econ. econ. con. 2: { econ. 2:eauto. inv H2. ssa. inv H9. 
                         econ. econ. con. eauto. con. 2:{ rewrite /split_set. 

instantiate (1:= (fun p' => if (p == p') && (p \in dom x) then (x0 p)++[::if v is inr n then Some n else None] else x0 p')).
 rewrite /update /makeLs -!map_comp. f_equal.
apply/eq_in_map. intro.
ssa. case_if. f_equal. 


norm_eqs. rewrite eqxx. ssa. eapply (map_f fst) in H10 as H_temp. rewrite H_temp. clear H_temp.
rewrite /insertL1 /insert_shift /insert /= //= in H4. 
                                   rewrite lookup_cat2 in H4. 
                                   rewrite lookup_initL1 in H4.
                                   rewrite /makeLs in H4.
                                   apply lookup_map2 in H4. ssa. inv H11. de x2. de x1. subst.
                                   have : uniq (dom x).
                                   inv H7. ssa. subst. de H12.  
                                                          move : H17 H18 H19 => Hun H17 Hgood.
                                   rewrite /dom -map_comp.
                                   rewrite map_inj_uniq. done. 

                                   intro. ssa. inv H18.
                                   intros. 
                                                          rewrite /can_split in H8. ssa.
remember H10. remember H4. clear Heqi Heqi0.
                                   apply uniq_in_pair in H10,H4;ssa. rewrite H10 in H4. inv H4.
                                   apply H8 in H10. move: H10 => HC. 
                                   rewrite makeL_cat. inv H6. ssa.
                                   apply uniq_in_pair in H17. rewrite H17. done. 
                                    

inv H7. ssa. subst.  inv H13. ssa.
de (mapP i0). inv H24. 
have : uniq_labels (trans x x2).
apply:uniq_trans. done.
intros.
apply uniq_full_unf in x4.
eapply uniq_makeL in x4. erewrite <- H10 in x4. ssa.

                                   ssa. rewrite /dom -map_comp. de x1.
                                   rewrite /makeLs -!map_comp.
                                   apply/mapP. econ. eauto. ssa. 
                                   case_if;ssa. norm_eqs.

rewrite /update /makeQs. 
apply/eq_in_map. intro.
ssa. case_if. f_equal. 

norm_eqs. rewrite eqxx. ssa.
rewrite /insertQ /insert_shift /insert /= //= in H5. 
                                   rewrite lookup_cat2 in H5.
                                    have: forall E p, lookup (list_map initQ E) (QKey (var_schl 0) p) = lookup E p. 
                               intros.
rewrite lookup_initQ //.

                                   move=>HHlook. rewrite HHlook in H5.
                                   rewrite /makeQs in H5.
                                   apply lookup_map2 in H5. ssa. inv H11. de x2. de x1. subst.
                                   have : uniq (dom x).
                                   inv H7. ssa. subst. de H12.  
                                   rewrite /dom -!map_comp.

move : H17 H18 H19 => Hun H17 Hgood.
have:  (list_map (fst \o (fun p : fin => (Ptcp p, fe (trans p x1)))) x2) = map Ptcp x2. apply/eq_in_map. intro. ssa. move=>->.
rewrite map_inj_uniq. done. intro. ssa. inv H18.

                                   intros. 
                                                          
                                   apply uniq_in_pair in H10,H5;ssa. rewrite H10 in H5. inv H5.


have : forall p p' l, checkPath p l -> makeQ (p ++ p') l = (makeQ p l)++(makeQ p' (makeL p l)). 
intros. rewrite makeQ_cat2 //. 

move=>HMakeQ. apply in_pair in H10 as HPP. apply (map_f fst) in HPP as H_tmep. rewrite H_tmep. clear H_tmep HPP. 
rewrite HMakeQ. f_equal.

                                   rewrite lookup_cat2 in H4. 
                                   rewrite lookup_initL1 in H4.
                                   rewrite /makeLs in H4.
                                   apply lookup_map2 in H4. ssa. inv H12. de x2. de x1. 
                                   have : uniq (dom x).
                                   inv H7. ssa. subst. de H12.  
                                   rewrite /dom -!map_comp.
have:  (list_map (fst \o (fun p : fin => (Ptcp p, fe (trans p x1)))) x2) = map Ptcp x2. apply/eq_in_map. intro. ssa. move=>->.
rewrite map_inj_uniq. done. intro. ssa. inv H12.


                                   intros. 
                                                          rewrite /can_split in H8. ssa.
                                                          apply in_pair in H10.
remember H10. remember H4. clear Heqi0 Heqi.
                                   apply uniq_in_pair in H10,H4;ssa. rewrite H10 in H4. inv H4.


                                   apply H8 in H10. move: H10 => HC. 
                                                          inv H6. ssa. 
                                   apply uniq_in_pair in H18. rewrite H18. done. 



inv H7. ssa. subst.  inv H14. ssa.
de (mapP i0). inv H25. 
have : uniq_labels (trans x x2).
apply:uniq_trans. done.
intros.
apply uniq_full_unf in x4.
eapply uniq_makeL in x4. erewrite <- H10 in x4. ssa.


apply in_pair in H10.
                                   ssa. rewrite /dom -map_comp. 
                                   rewrite /makeLs -!map_comp.
                                   apply/mapP. econ. eauto. ssa. 

inv H8. apply H12. done.

                                   rewrite /dom -map_comp. de x1.
                                   rewrite /makeQs -!map_comp.
                                   apply/mapP. econ. eauto. ssa.  
destruct (eqVneq p (x1.1)). subst. ssa. ssa. } 
inv H8.
ssa. 


con. ssa. case_if;ssa. norm_eqs. inv H7. ssa. subst.
apply in_pair in H12 as Hpair. de (mapP Hpair). inv H15.
have: forall p p' l, checkPath p l -> checkPath p' (makeL p l) ->  checkPath (p ++ p') l. 
intros.
move : H19 H21. clear.
elim : p p' l0. ssa.  
ssa. de a. destruct (fe _) eqn:Heqn;ssa. destruct (lookup _ _) eqn:Heqn2;ssa.
destruct (fe _) eqn:Heqn;ssa.
move=>HCheck. 
                                   rewrite lookup_cat2 in H4. 
                                   rewrite lookup_initL1 in H4.
                                   rewrite /makeLs in H4.
                                   apply lookup_map2 in H4. ssa. 

                         inv H18. de x3. inv H19. subst.
                         apply HCheck. eauto. de (mapP H4). inv H22. 
                         inv H6. inv H22. 
                         inv H6. ssa. apply uniq_in_pair in H28. rewrite H28. done. 

have : uniq_labels (trans x3 x1).
apply:uniq_trans.  inv H13. ssa.
move/uniq_full_unf. move/uniq_makeL. move/(_ (x0 x3)).
rewrite -H23. ssa.

                                   ssa. rewrite /dom -map_comp.
                                   rewrite /makeLs -!map_comp.
                                   apply/mapP. econ. eauto. ssa.  inv H18.




intros. 
 destruct (eqVneq p p0).  subst. rewrite (negbTE H12) andbC //=. eauto.
simpl. eauto. }  econ.
rewrite !lookup_insertL1_succ in H4,H3.
rewrite update_insertL1_succ in H3.
rewrite update_insertQ_succ in H3.
rewrite !lookup_insertQ_succ in H5,H3. 
econ. econ. con. 2:{  econ. eauto. eauto. } 
econstructor 2. eauto. eauto. eauto. econ. econ.




move : H4 H5 H6 H7 => Hall H4 H5 H6.
(*LQ3*)
destruct s.
apply lookup_insertL1 in H4. 
de H4. subst.
2: { 
subst. rewrite lookup_insertQ_succ in H5.
econ. econ. con. 2: { econ. eauto. rewrite update_insertL1_succ update_insertQ_succ in H3. eauto. } 
econstructor 3;eauto. } 


2: { 
rewrite /weak_coherent in H2. ssa. inv H8.
rewrite /makeLs. rewrite /dom -map_comp.
have: (list_map (fst \o (fun x1 : ptcp * lType => (x1.1, makeL (x0 x1.1) x1.2))) x) = dom x.
apply/eq_in_map. intro. ssa. move=>->. inv H2. ssa. subst.
have:  (dom (list_map (fun p0 : fin => (Ptcp p0, fe (trans (Ptcp p0) x1))) x2)) = map Ptcp x2.
rewrite /dom -map_comp. apply/eq_in_map. intro. ssa. move=>->.
rewrite map_inj_uniq. done. intro.  ssa.  inv H10. }

apply  lookup_insertQ in H5.
2: { 
rewrite /weak_coherent in H2. ssa. inv H8.
rewrite /makeQs. rewrite /dom -map_comp.
have: (list_map (fst \o (fun x1 : ptcp * lType => (x1.1, makeQ (x0 x1.1) x1.2))) x) = dom x.
apply/eq_in_map. intro. ssa. move=>->. inv H2. ssa. subst.
have:  (dom (list_map (fun p0 : fin => (Ptcp p0, fe (trans (Ptcp p0) x1))) x2)) = map Ptcp x2.
rewrite /dom -map_comp. apply/eq_in_map. intro. ssa. move=>->.
rewrite map_inj_uniq. done.  intro. ssa. inv H10.  } 

de H5. 


inv H2. ssa. inv H10. clear H10. inv H8. ssa. subst.
rewrite /makeQs -map_comp in H5. 
rewrite /makeLs -map_comp in H7. 
apply lookup_map2 in H5,H7. ssa. clear H4. inv H11. inv H14.  

rewrite /can_split in H9. ssa.
have: checkPath (x0 x) (fe (trans x x1)). apply /H4.
apply/lookup_map3.  eauto. 2:eauto. 
rewrite /dom -map_comp.
have: (list_map (fst \o (fun p : fin => (Ptcp p, fe (trans p x1)))) x2) = map Ptcp x2.
apply/eq_in_map. intro. ssa. move=>->. rewrite map_inj_uniq. done. intro. ssa. inv H15. done.
move=>HC.

have: checkPath (x0 x3) (fe (trans x3 x1)). apply /H4.
apply/lookup_map3. 
rewrite /dom -map_comp. 
rewrite map_inj_uniq. done. intro. ssa. inv H15. 2:econ. done.
move=>HC'.

rewrite !update_insertL1_0 !update_insertQ_0 in H3,H1.



(*clean up*)
clear H H0 Hoft. 
clear H11. 
move: Hside Hall H12 H13 H2 H6 H8 H10 H5 H7 H14 H4 H9 HC HC' H3 H1. clear.
move: l x0 x1 x3 x => lp lp_fun G p_send p_receive.
move=> Hside Hall Hun HSub WC H_Estep2 HCo HCoG H_send_role H_receive_role H_makeQ.
move=> H_check_in H_check_notin H_check_receive H_check_send.
move=> H_oft H_LQ.

case : H_makeQ. move=>H_makeQ.




move : H_makeQ. move/[dup]. move=>H_makeQ.
move/makeQ_split4.
move/(_ H_check_send).
remember H_makeQ as H_makeQ_safe. clear HeqH_makeQ_safe.
case. move=> x [] v' [] y' [] Heq [] Hl0 Hl1. subst.
move: H_Estep2. move/[dup]. move=>H_Estep2.
move/to_canEstep2.


move=>HC.
have : Project G p_send (trans p_send G).
inv HCoG. ssa. move: (H3 p_send). ssa. apply:Project_EQ2. eauto. apply:proj_proj. eauto.
move=>HP_send.

have : Project G p_receive (trans p_receive G).
inv HCoG. ssa. move: (H3 p_receive). ssa. apply:Project_EQ2. eauto. apply:proj_proj. eauto.
move=>HP_receive.


apply makeQ_ETr in H_makeQ.
eapply makeQ_ETr2 in HC.
2: { apply:Project_eunf2. apply :HP_receive. } 
ssa. eapply to_Trp in H,H1.
2: { apply:Project_eunf2. apply:HP_send. } 
2: { apply:Project_eunf2. apply:HP_receive. } 
apply to_Trp2 in H1,H.
eapply to_Tr2 in H1. 6:eauto. 5:econ.
ssa.
eapply Tr2_to_canStep in H1. 2:econ.
inv HCoG. 
ssa. punfold H9. inv H9. apply H10 in H1. 
case : H1. move=> G' [] HStep [] //= HGood.
econ. econ. con. con. 
econ.  2: { 
apply:OFT_weaken_swap_EQ_insertL1. apply H_oft. inv Hside. ssa.

rewrite dom_update. rewrite /makeLs /dom -!map_comp.
rewrite map_inj_uniq. done. intro. ssa. inv H1. 

instantiate (1:= (makeLs (list_map (fun p : fin => (Ptcp p, fe (trans p G'))) x2) (fun p : ptcp_eqType => if p == p_send then x ++ y' else lp_fun p))).
rewrite /makeLs /dom -!map_comp.
rewrite map_inj_uniq. done. intro. ssa. inv H1. 

intros.

ssa.

apply in_pair in H1. 



apply in_update2 in H1. 
de H1.
inv H1. econ.  



con. eapply lookup_map3.
rewrite /dom /makeLs -!map_comp.
rewrite map_inj_uniq. done. intro. ssa. inv H11. 
apply/mapP. econ. apply H_receive_role. econ. ssa.
con. 
have : Ptcp p_send != Ptcp p_receive.
apply label_pred in HStep;ssa. rewrite neg_sym. move/negbTE=>->.


eapply harmony_sound in HStep.
6: { instantiate (1:= ( fun x => trans x G)). rewrite /one_shot. intros. 
     move: (H8 p). ssa.
     apply:Project_EQ2. eauto. apply:proj_proj. done. } 
case : HStep. move=> f_one [] Hone HEnv.
inv HEnv. ssa.
have : EQ2 e' (trans p_receive G').
move : (Hone p_receive). rewrite /update_action /=. rewrite /harmony.update eqxx /=.
intro.
apply:proj_proj. done.
move=>HQ.


(*FIND ME*)
eapply Estep_makeL in H_Estep2 as H_Estep3.
2: { apply Estep_full_unf2. eauto. } 
eapply Estep23 in H_Estep3.
2:eauto.




apply:EQ2_trans. apply:EQ2_eunfl2. 2: {  apply check_makeL.
2: { apply:EQ2_eunf2. apply:HQ. } 
apply:checkPath_Estep3. 4: { apply : H_check_receive. } 
apply:Estep_full_unf2. eauto.
apply: uniq_full_unf. apply:uniq_trans. done. done. apply:harmony.step_uniq. eauto. 
apply:uniq_trans. done. } 
done. apply:lInvPred_makeL. done. rewrite -lInvPred_iff. apply:gInvPred_proj. 
move : (H8 (Ptcp 0)). ssa. apply/gInvPred_iff. apply:Project_gtree. eauto.
apply uniq_makeL. 
apply uniq_full_unf. apply:uniq_trans. done. done.
done. 
apply uniq_full_unf. apply:uniq_trans. done. done.
done. done. done. 
con.
inversion H_Estep2. rewrite -H11. 
suff : lInvPred e0. intro. punfold x4. inv x4. inv H16;ssa.
subst.
suff : lInvPred (trans p_receive G).
move/lInvPred_iff.
move/lInvPred_makeL.
move/(_ (lp_fun p_receive)). rewrite -H12.
move=>HH. suff : lInvPred (EMsg Rd c v0 T'). intros. punfold x4. inv x4.
inv H11. de H14. apply:HH. done. apply:gInvPred_proj.
move : (H8 (Ptcp 0)). ssa. apply/gInvPred_iff. apply:Project_gtree. eauto.

suff : lInvPred T'. intro. punfold x4. inv x4. inv H17;ssa.
subst.
suff : lInvPred (trans p_receive G).
move/lInvPred_iff.
move/lInvPred_makeL.
move/(_ (lp_fun p_receive)). rewrite -H11.
move=>HH. suff : lInvPred (EBranch Rd c es). intros. punfold x4. inv x4.
inv H12. 
move/inP : H16. move=>Hin2. move/ForallP : H14. move/(_ _ Hin2). case;ssa.
apply:HH. done. apply:gInvPred_proj.
move : (H8 (Ptcp 0)). ssa. apply/gInvPred_iff. apply:Project_gtree. eauto.

case_if. have : p_send != p_receive. apply label_pred in HStep. ssa. done. done.
norm_eqs. rewrite !H11.
intro. exfalso. apply/negP. apply:x4. apply/eqP. f_equal. inv H11.

con. rewrite -makeL_fe2.
have : lInvPred ((makeL (lp_fun p_receive) (trans p_receive G'))).
apply:lInvPred_makeL. 


eapply harmony_sound in HStep.
6: { instantiate (1:= ( fun x => trans x G)). rewrite /one_shot. intros. 
     move: (H8 p). ssa.
     apply:Project_EQ2. eauto. apply:proj_proj. done. } 
case : HStep. move=> f_one [] Hone HEnv.
inv HEnv. ssa.
have : EQ2 e' (trans p_receive G').
move : (Hone p_receive). rewrite /update_action /=. rewrite /harmony.update eqxx /=.
intro.
apply:proj_proj. done.
move=>HQ.


(*FIND ME*)
eapply Estep_makeL in H_Estep2 as H_Estep3.
2: { apply Estep_full_unf2. eauto. } 
eapply Estep23 in H_Estep3.
2:eauto.

apply:checkPath_EQ2. apply:HQ.



apply:checkPath_Estep3. eauto. 
apply:uniq_trans. done. done. apply:checkPath_fe2. done.

apply:lInvPred_makeL.  done.
apply -> lInvPred_iff.
apply:gInvPred_proj. 
apply/gInvPred_iff/Project_gtree. eauto. 



apply:uniq_makeL. apply:uniq_full_unf. apply:uniq_trans. done. done. done.
apply:uniq_full_unf. 
apply:uniq_trans. done. done. done. done. done.
apply:step_lInvPred. eauto.
apply/gInvPred_iff/Project_gtree. eauto. 
intros. punfold x4. 
rewrite makeL_fe3. inv x4. inv H12.

inv H_Estep2.
suff : uniq_labels (makeL (lp_fun p_receive) (fe (trans p_receive G))).
rewrite -H13. ssa.  
apply:uniq_full_unf. done.
apply:uniq_makeL. apply:uniq_full_unf. apply:uniq_trans. done.
suff : uniq_labels (makeL (lp_fun p_receive) (fe (trans p_receive G))).
rewrite -H12. ssa.  
apply:uniq_full_unf. apply (allP H14) in H17. done.
apply:uniq_makeL. apply:uniq_full_unf. apply:uniq_trans. done.

move : H11 => H_receive_not.

(*exists T'. (*instead of trans G' we use the reductum*)*)
econ. con. apply:lookup_map3.
de (mapP H1). ssa. de (mapP H11). subst.
inv H12.
rewrite /dom -!map_comp. rewrite map_inj_uniq. done. intro. ssa. inv H14.
instantiate (1:= (k,fe (trans k G'))). apply/mapP. econ. 
instantiate (1:= nat_of_ptcp k). 
de (mapP H1).   inv H12. de (mapP H11). subst. ssa.
de k. simpl. econ.
con. de (mapP H1). inv H12. de (mapP H11). subst. ssa.
case_if. norm_eqs. rewrite H14.



eapply harmony_sound in HStep as Harm.
6: { instantiate (1:= ( fun x => trans x G)). rewrite /one_shot. intros. 
     move: (H8 p). ssa.
     apply:Project_EQ2. eauto. apply:proj_proj. done. } 

case : Harm. move=> f_one [] Hone HEnv.
inv HEnv. ssa.


(*HERE*)
have : EQ2 e (trans p_send  G').
move : (Hone p_send). rewrite /update_action /=. rewrite /harmony.update eqxx /=.
have : p_send != p_receive. apply label_pred in HStep. ssa. done. done. 
intro. case_if. norm_eqs. inv H17.  rewrite eqxx in x4. ssa.
move/proj_proj. done.
move=>HQ.


clear H16.




















rewrite Heq.
have : x ++ (v'::y') = (x++[::v'])++y'.  rewrite -catA.  done.
move=>->. rewrite makeL_cat. apply/EQ2_sym. rewrite makeL_cat. apply/EQ2_sym.
apply check_makeL.
2: { rewrite -!makeL_fe2. apply:EQ2_trans.
     apply:ECME.  apply:H15. rewrite Heq in H_check_send. apply checkPath_cat in H_check_send.
apply checkPath_fe2.  done. simpl. rewrite makeQ_fe. done. 
ssa.
rewrite Heq in H_check_send. apply checkPath_cat2 in H_check_send as HC2. ssa.
clear H17. rewrite Heq in H_makeQ_safe.
rewrite !makeQ_cat2 in H_makeQ_safe.
have: drop (size (makeQ x (fe (trans p_send G)))) ((makeQ x (fe (trans p_send G)))  ++
                 makeQ (v' :: y') (makeL x (fe (trans p_send G)))) =
      drop (size ( makeQ x (fe (trans p_send G))))  (makeQ x (fe (trans p_send G)) ++
                 (c, v) :: makeQ y' (makeL (x ++ [:: v']) (fe (trans p_send G)))).
rewrite H_makeQ_safe. rewrite !drop_size_cat //=.
rewrite !drop_size_cat.
simpl. de v'. rewrite /obs in H_makeQ_safe x4. ssa.
rewrite /obs. ssa. destruct (fe (makeL _ _)) eqn:Heqn;ssa. de d. de d.
destruct (lookup _ _) eqn:Heqn2;ssa. rewrite -makeL_fe in Heqn. rewrite Heqn.
inv x4. apply checkPath_cat in H_check_send. apply:checkPath_fe2. done.
rewrite /obs in H_makeQ_safe x4 *. ssa.
destruct (fe (makeL _ _))eqn:Heqn;ssa. de d. rewrite -makeL_fe in Heqn. rewrite Heqn.
inv x4. apply checkPath_cat in H_check_send. apply:checkPath_fe2. done.
de d. 
rewrite makeQ_size //. apply checkPath_cat in H_check_send. done.
rewrite makeQ_size //. apply checkPath_cat in H_check_send. done.
apply checkPath_cat in H_check_send. done.

apply:uniq_trans. done.
apply:gInvPred_proj.
apply/gInvPred_iff/Project_gtree. eauto.


apply check_makeL.
have : x = x ++ nil. rewrite cats0. done. move=>->.
eapply checkPath_Estep2. eauto. rewrite makeQ_fe. eauto. apply:checkPath_fe2. 
rewrite Heq in H_check_send. apply checkPath_cat in H_check_send. done.
4:done. 4:done.
2: { rewrite Heq in H_check_send. have : x ++ v' :: y' = (x++ [::v']) ++ y'. rewrite -catA.  done.
     move=> xx. rewrite xx in H_check_send.
     apply checkPath_cat in H_check_send. apply checkPath_fe2. eauto. } 
ssa.

rewrite Heq in H_check_send. apply checkPath_cat2 in H_check_send as HC2. ssa.
clear H17. rewrite Heq in H_makeQ_safe.
rewrite !makeQ_cat2 in H_makeQ_safe.
have: drop (size (makeQ x (fe (trans p_send G)))) ((makeQ x (fe (trans p_send G)))  ++
                 makeQ (v' :: y') (makeL x (fe (trans p_send G)))) =
      drop (size ( makeQ x (fe (trans p_send G))))  (makeQ x (fe (trans p_send G)) ++
                 (c, v) :: makeQ y' (makeL (x ++ [:: v']) (fe (trans p_send G)))).
rewrite H_makeQ_safe. rewrite !drop_size_cat //=.
rewrite !drop_size_cat.
simpl. de v'. rewrite /obs in H_makeQ_safe x4. ssa.
rewrite /obs. ssa. destruct (fe (makeL _ _)) eqn:Heqn;ssa. de d. de d.
destruct (lookup _ _) eqn:Heqn2;ssa. rewrite -makeL_fe in Heqn. rewrite Heqn.
inv x4. apply checkPath_cat in H_check_send. apply:checkPath_fe2. done.
rewrite /obs in H_makeQ_safe x4 *. ssa.
destruct (fe (makeL _ _))eqn:Heqn;ssa. de d. rewrite -makeL_fe in Heqn. rewrite Heqn.
inv x4. apply checkPath_cat in H_check_send. apply:checkPath_fe2. done.
de d. 
rewrite makeQ_size //. apply checkPath_cat in H_check_send. done.
rewrite makeQ_size //. apply checkPath_cat in H_check_send. done.
apply checkPath_cat in H_check_send. done.

apply:uniq_trans. done. done.

apply:harmony.step_uniq. eauto.
apply:uniq_trans. done. 
} 
rewrite Heq in H_check_send.
have : x ++ v' :: y' = (x++ [::v']) ++ y'. rewrite -catA.  done.
move=> xx. rewrite xx in H_check_send.
apply checkPath_cat2 in H_check_send. done.

apply uniq_makeL. 
apply:uniq_full_unf. 
apply:uniq_trans. done. done. done. done. done.

eapply harmony_sound in HStep as Harm.
6: { instantiate (1:= ( fun x => trans x G)). rewrite /one_shot. intros. 
     move: (H8 p). ssa.
     apply:Project_EQ2. eauto. apply:proj_proj. done. } 

case : Harm. move=> f_one [] Hone HEnv.
inv HEnv. ssa.


(*HERE*)
have : EQ2 e' (trans p_receive  G').
move : (Hone p_receive). rewrite /update_action /=. rewrite /harmony.update eqxx /=.
move/proj_proj. done.
move=>HQ.





apply check_makeL.  apply:H_check_in.
apply:lookup_map3. rewrite /dom -map_comp. rewrite map_inj_uniq. done.
intro. ssa. inv H17. 2: { econ. }  done.

move : (H8 x5). ssa.
apply:EQ2_eunf2. apply:EQ2_eunfl2.
apply:preserve_proj2. eauto. eauto.  
apply/gInvPred_iff/Project_gtree. eauto. simpl. rewrite /comp_dir /=.
rewrite H14. case_if. done. done. done. done. 
apply:uniq_full_unf. apply:uniq_trans. done.
done. done. done. done.
ssa.
de (mapP H1). inv H12. ssa.




suff : lInvPred (makeL (lp_fun x4.1) x4.2).
intro. punfold x5. inv x5.




rewrite makeL_fe3. inv H13;ssa.
apply:lInvPred_makeL. 
de (mapP H11). subst. ssa.
apply H_check_in. apply:lookup_map3.
rewrite /dom -map_comp. rewrite map_inj_uniq. done.
intro. ssa. inv H14.  2: { econ. }  done.
de (mapP H11). subst. ssa. apply -> lInvPred_iff.
apply:gInvPred_proj. 
apply/gInvPred_iff/Project_gtree. eauto.

rewrite makeL_fe3.
suff : lInvPred (makeL (if k == p_send then x ++ y' else lp_fun k) (fe (trans k G'))).
intro. punfold x4. inv x4. inv H11.
case_if. apply:lInvPred_makeL.

eapply harmony_sound in HStep as Harm.
6: { instantiate (1:= ( fun x => trans x G)). rewrite /one_shot. intros. 
     move: (H8 p). ssa.
     apply:Project_EQ2. eauto. apply:proj_proj. done. } 

case : Harm. move=> f_one [] Hone HEnv.
inv HEnv. ssa.

have : EQ2 e (trans p_send  G').
move : (Hone p_send). rewrite /update_action /=. rewrite /harmony.update eqxx /=.
have : p_send != p_receive. apply label_pred in HStep. ssa. done. done. 
intro. case_if. norm_eqs. inv H14. rewrite eqxx in x4. ssa.
move/proj_proj. done.
move=>HQ.

norm_eqs.
apply:checkPath_EQ2. apply:EQ2_eunf2. eauto.

apply:checkPath_Estep2. eauto. rewrite makeQ_fe. eauto.
rewrite Heq in H_check_send. apply checkPath_cat in H_check_send. apply:checkPath_fe2. done.
2: { rewrite Heq in H_check_send. apply:checkPath_fe2. eauto. } 
4: done. ssa.


rewrite Heq in H_check_send. apply checkPath_cat2 in H_check_send as HC2. ssa.
clear H14. rewrite Heq in H_makeQ_safe.
rewrite !makeQ_cat2 in H_makeQ_safe.
have: drop (size (makeQ x (fe (trans p_send G)))) ((makeQ x (fe (trans p_send G)))  ++
                 makeQ (v' :: y') (makeL x (fe (trans p_send G)))) =
      drop (size ( makeQ x (fe (trans p_send G))))  (makeQ x (fe (trans p_send G)) ++
                 (c, v) :: makeQ y' (makeL (x ++ [:: v']) (fe (trans p_send G)))).
rewrite H_makeQ_safe. rewrite !drop_size_cat //=.
rewrite !drop_size_cat.
simpl. de v'. rewrite /obs in H_makeQ_safe x4. ssa.
rewrite /obs. ssa. destruct (fe (makeL _ _)) eqn:Heqn;ssa. de d. de d.
destruct (lookup _ _) eqn:Heqn2;ssa. rewrite -makeL_fe in Heqn. rewrite Heqn.
inv x4. apply checkPath_cat in H_check_send. apply:checkPath_fe2. done.
rewrite /obs in H_makeQ_safe x4 *. ssa.
destruct (fe (makeL _ _))eqn:Heqn;ssa. de d. rewrite -makeL_fe in Heqn. rewrite Heqn.
inv x4. apply checkPath_cat in H_check_send. apply:checkPath_fe2. done.
de d. 
rewrite makeQ_size //. apply checkPath_cat in H_check_send. done.
rewrite makeQ_size //. apply checkPath_cat in H_check_send. done.
apply checkPath_cat in H_check_send. done.

apply:uniq_trans. done. done. done. done. done. done.
apply -> lInvPred_iff. apply:step_lInvPred. eauto. 
move : (H8 p_send). ssa.
apply/gInvPred_iff/Project_gtree. eauto.
apply:lInvPred_makeL.

move : (H8 k). ssa.
apply:checkPath_EQ2. apply:EQ2_eunf2.
apply:preserve_proj2. eauto. eauto. 
apply/gInvPred_iff/Project_gtree. eauto. simpl. rewrite /comp_dir /=.
rewrite H11. rewrite (negbTE H_receive_not). done. done. done.
apply: checkPath_fe2. 
apply:H_check_in. apply:lookup_map3.
rewrite /dom -map_comp. rewrite map_inj_uniq. ssa.
intro. ssa. inv H13. 2: {  instantiate (1:= nat_of_ptcp k). de k. } 
de (mapP H1). ssa. inv H14. de (mapP H13). subst. ssa.
apply -> lInvPred_iff. apply:step_lInvPred. eauto. 
move : (H8 k). ssa.
apply/gInvPred_iff/Project_gtree. eauto.
de (mapP H1). inv H12. subst. 
apply uniq_makeL. de (mapP H11). subst. ssa.
apply:uniq_full_unf. apply:uniq_trans. done.

rewrite /filter_keys all_filter. simpl. rewrite dom_update. ssa.
rewrite /dom /makeLs -!map_comp. rewrite !all_map. 


apply/allP. intro. ssa. tunf. ssa.
apply/implyP. intro. ssa.
exfalso. apply/negP. apply : H11. apply/mapP. econ. eauto. ssa.

inv Hside. ssa.

intro. intros. apply in_pair in H22 as HP. apply (allP H11) in HP. ssa.
inv H12. ssa. subst. inv H23. ssa. 
rewrite /only_schl in H14. apply in_dom in H22 as HD. apply (allP H14) in HD. de lk.
apply lookup_filter2 in H22. ssa. apply H25 in H28. ssa. subst.
apply:lInvPred_makeL.
apply H24. done. 
apply:gInvPred_proj. 
apply H27 in H28. inv H28. ssa.
move : (H33 p_send). ssa.
apply/gInvPred_iff/Project_gtree. eauto.
apply H20 in H22. done. } 








eapply (@preserve_proj _ _ _ p_send Sd) in HStep as H_send.
eapply Estep_full_unf2 in H_send.

eapply (@preserve_proj _ _ _ p_receive Rd) in HStep as H_receive.
eapply Estep_full_unf2 in H_receive.

clear H x3 H3 H0 H2.
move : H4 => H. 
move : H5 H6 H7 H8 => H0 H1 Hun' H2.
move : H_makeQ_safe => H_makeQ.
econ. 
exists (fun p => if p == Ptcp p_send then x++y' else lp_fun p).


con. 


econ. exists x2. 
con. instantiate (1:= G'). econ. apply/linearity.Linear_step. eauto. inv HCoG.


ssa. apply/size_pred_step. eauto. done.
apply:action_pres. eauto. eauto.


apply: uniqg_labels_pres. eauto. done.
intros.
exists (trans p G'). ssa.
apply: preserve_proj5. eauto. ssa. done.
ssa.
move : (H2 p). ssa.
eapply Project_EQ2. eauto.
apply/proj_proj. done.



econ.
con. ssa. intro. intros. apply/HSub. apply/step_contained. eauto. done.
con. 


rewrite /can_split. ssa.
intros.  apply lookup_map2 in H3. ssa. inv H4. subst.
case_if. norm_eqs. rewrite H5.

eapply harmony_sound in HStep.
6: { instantiate (1:= ( fun x => trans x G)). rewrite /one_shot. intros. 
     move: (H2 p). ssa.
     apply:Project_EQ2. eauto. apply:proj_proj. done. } 
case : HStep. move=> f_one [] Hone HEnv.
inv HEnv. ssa.
have : EQ2 e (trans p_send G').
move : (Hone p_send). rewrite /update_action /=. rewrite /harmony.update eqxx /=.
intro.
apply:proj_proj. 


have : p_send != p_receive.
apply/eqP. intro. 
apply to_canEstep2 in H_Estep2.
eapply makeQ_ETr3 in H_Estep2;eauto.
ssa. eapply test_test in H11. 
7: {   eauto. rewrite H8 in H_makeQ. eauto. }
apply/negP.  apply (allP H11). apply : H13. done.
apply:Project_eunf2. apply:Project_EQ2. apply : HP_receive.
apply:EQ2_refl. apply:gInvPred_proj. 
apply/gInvPred_iff/Project_gtree. eauto. 
done. done. done. done.
intro. 
move : Hone0. case_if. norm_eqs. inv H8. neqt. done.

move=>HQ.


apply:checkPath_EQ2. apply:EQ2_eunf2.  apply:HQ.

apply:checkPath_Estep2. eauto.
rewrite makeQ_fe. eauto. 

Hint Resolve checkPath_fe checkPath_fe2 checkPath_cat. 
rewrite Heq in H_check_send. eauto.
2: {  rewrite Heq in H_check_send. eauto. } 
4:econ. ssa.



rewrite Heq in H_check_send. apply checkPath_cat2 in H_check_send as HC2. ssa.
clear H11. rewrite Heq in H_makeQ.
rewrite !makeQ_cat2 in H_makeQ.
have: drop (size (makeQ x (fe (trans p_send G)))) ((makeQ x (fe (trans p_send G)))  ++
                 makeQ (v' :: y') (makeL x (fe (trans p_send G)))) =
      drop (size ( makeQ x (fe (trans p_send G))))  (makeQ x (fe (trans p_send G)) ++
                 (c, v) :: makeQ y' (makeL (x ++ [:: v']) (fe (trans p_send G)))).
rewrite H_makeQ. rewrite !drop_size_cat //=.
rewrite !drop_size_cat.
simpl. de v'. rewrite /obs in H_makeQ x4. ssa.
rewrite /obs. ssa. destruct (fe (makeL _ _)) eqn:Heqn;ssa. de d. de d.
destruct (lookup _ _) eqn:Heqn2;ssa. rewrite -makeL_fe in Heqn. rewrite Heqn.
inv x4. apply checkPath_cat in H_check_send. apply:checkPath_fe2. done.
rewrite /obs in H_makeQ x4 *. ssa.
destruct (fe (makeL _ _))eqn:Heqn;ssa. de d. rewrite -makeL_fe in Heqn. rewrite Heqn.
inv x4. apply checkPath_cat in H_check_send. apply:checkPath_fe2. done.
de d. 
rewrite makeQ_size //. apply checkPath_cat in H_check_send. done.
rewrite makeQ_size //. apply checkPath_cat in H_check_send. done.
apply checkPath_cat in H_check_send. done.

apply:uniq_trans. done. done. done. done. done. done.

destruct (eqVneq x3 p_receive). subst.
apply:checkPath_fe.
apply:checkPath_Estep3. apply H_receive.
apply:uniq_full_unf. apply:uniq_trans. done. done.
apply H_check_in. apply:lookup_map3.
rewrite /dom -map_comp. rewrite map_inj_uniq. done. 
intro. ssa. inv H6. apply H3.  done.
move: (H2 x3). ssa.
apply:checkPath_EQ2.
apply:EQ2_eunf2. apply:preserve_proj2. eauto. eauto.
apply/gInvPred_iff/Project_gtree. eauto.
ssa. rewrite /comp_dir. ssa. rewrite H5. case_if. norm_eqs. inv H7. neqt. done. done.
done. apply:checkPath_fe2.  apply H_check_in. apply:lookup_map3. eauto.
rewrite /dom -map_comp. rewrite map_inj_uniq. done. 
intro. ssa. inv H7. apply H3.  de x3.




intros. rewrite /dom -map_comp in H3. case_if. norm_eqs. 
exfalso. apply/negP. apply H3. apply/mapP. econ. 2:econ. done. 
apply H_check_notin. apply/negP. intro. apply/negP. apply:H3. 
rewrite /dom -map_comp in H5. de (mapP H5).




rewrite /split_set.
rewrite /split_set. 

f_equal.
rewrite /update /makeQs -!map_comp.
subst. apply/eq_in_map. intro. ssa.
case_if. subst. norm_eqs.  rewrite H4. f_equal.
have : Project G' p_send  (trans p_send G').
apply:preserve_proj5. eauto. ssa. done.
move: (H2 p_send). ssa.

move/proj_proj.
move/EQ2_eunf2.
move/makeQ_EQ2=><-. inv H_makeQ.
move : H_send H6. move=>HE.

have : uniq_labels (fe (trans p_send G)).
apply:uniq_full_unf. apply:uniq_trans. done.
move : HE H_check_send.  move : (fe _) Heq Hall => e. clear.
move=>->.
move=> Hall HE HC Hun Hcat.

rewrite makeQ_cat2. f_equal.



 apply checkPath_cat in HC .
      move : HE HC Hall. clear Hcat.
      move Heq : (Sd,_,_) => l HE.
      move : HE x c v Heq Hun. clear.
      elim;ssa. de x. 
      de o. rewrite /obs in Hall. ssa. de d. inv Heq. rewrite eqxx in H1. done.
      de x.
      de o. inv Heq. ssa. f_equal. eauto.
      inv Heq. ssa. de x. ssa. 
      rewrite /nexte_wrap in H1. de o.
      destruct (lookup _ _) eqn:Heqn;ssa. neqt.
   de x.
      de o. destruct (lookup _ _) eqn:Heqn;ssa. inv Heq. 
      move/in_pair in Heqn.
      have : size es0 = size es1. eauto.
      move=>Hsize.
      move/in_zip1 : Heqn. move/(_ _ _ Hsize). ssa.  de x0.

      apply mem_zip in H10 as HH. ssa.
      have : dom es0 = dom es1. rewrite /dom H//.
      move=>Hdom. eapply same_label in Hdom. 3:eauto. subst.
      apply uniq_in_pair in H12. rewrite H12. f_equal. 

   move/inP : H10. move/H1. move=>HH2. simpl in HH2. eapply HH2;eauto.  
   apply (allP H4) in H11. done. rewrite /dom -H. done. done.
   rewrite makeQ_fe full_eunf_subst -makeQ_fe. 
   apply/H0. eauto. 
   rewrite uniq_labels_subst;ssa. case :n ;ssa.
   apply checkPath_fe in HC. rewrite full_eunf_subst in HC.
   apply checkPath_fe2 in HC. done.
   rewrite makeQ_fe full_eunf_subst -makeQ_fe in Hall. eauto. 

   have : v' :: y' = [::v']++ y'. done.
   move=>xeq. rewrite xeq catA in HC. 
   apply checkPath_cat in HC.

   have:  makeQ (x ++ [::v']) e =
          makeQ x e ++ [::(c, v)].
   have: makeQ ((x ++ [::v']) ++ y') e =
      (makeQ x e ++ [::(c, v)]) ++ (makeQ y' (makeL (x ++ [:: v']) e)).
   rewrite -!catA //=. clear Hcat =>Hcat.
   rewrite makeQ_cat2 in Hcat.
   have: take (size (makeQ (x ++ [:: v']) e)) (makeQ (x ++ [:: v']) e ++ makeQ y' (makeL (x ++ [:: v']) e)) =
         take (size ((makeQ x e ++ [:: (c, v)]))) ((makeQ x e ++ [:: (c, v)]) ++ makeQ y' (makeL (x ++ [:: v']) e)).
   rewrite Hcat //=. rewrite !take_size_cat //. rewrite makeQ_cat2. rewrite !size_cat. f_equal. rewrite makeQ_size;ssa.
   apply checkPath_cat2 in HC. ssa.
   apply checkPath_cat2 in HC.  ssa.
   apply checkPath_cat in HC. done.
   rewrite !take_size_cat. done.  done. done. done.
   clear Hcat => Hcat. 
   f_equal.
   clear xeq.
   apply checkPath_cat in HC as HC2.
   rewrite makeQ_cat2 in Hcat.
   have: makeQ [:: v'] (makeL x e) = [:: (c, v)].
   apply checkPath_cat2 in HC.
   have: drop (size (makeQ x e)) (makeQ x e ++ makeQ [:: v'] (makeL x e)) = drop (size (makeQ x e)) (makeQ x e ++ [:: (c, v)]).
   rewrite Hcat. done. rewrite !drop_size_cat //.
   clear Hcat => Hcat.
   rewrite makeL_cat. ssa. 
   apply checkPath_cat2 in HC.
   destruct (obs _ _) eqn:Heqn;last by de v'.
   destruct (nexte_wrap _ _) eqn:Heqn2;last by []. inv Hcat.
   clear Hcat.
 clear HC.
   move : HE HC2 Heqn2 Heqn Hall Hun. clear.
   move Heq : (Sd,_,_) => l'  HE.
   move : HE c v v' x s Heq.
   elim.
 * intros. inv Heq.
   de x. rewrite /obs in Heqn. ssa. de v'. inv Heqn2.
   de o. rewrite eqxx in H1. done.
 * intros. inv Heq. 
   de x. rewrite /obs in Heqn. ssa. de v'. inv Heqn2. inv Heqn. 
   de o. eauto.
 * intros. inv Heq.
   de x. rewrite /obs in Heqn. ssa. de v'. inv Heqn.
   apply uniq_in_pair in H. rewrite H in Heqn2. inv Heqn2. done. 
   rewrite /obs in H0. ssa. de o.
   destruct (lookup _ _) eqn:Heqn3. ssa. neqt. done. 
 * intros. inv Heq.
   de x. rewrite /obs in Heqn. ssa. de v'. inv Heqn.
   rewrite /obs in H3. ssa. de o. 
   
   rewrite /obs in Heqn. 
   destruct (lookup _ _) eqn:Heqn3. 
   apply in_pair in Heqn3. have : size es0 = size es1 by eauto.
   move=>Hsize. move/in_zip1 : Heqn3. move/(_ _ _ Hsize). ssa.
   de x0. move: (H10).
   have : uniq (dom es0). done.
   move=>Hun.
   move/same_label. move/(_ H Hun). intros. subst.
   move/inP:(H10).
   move/H1. simpl. move=>HH. 
   apply uniq_in_pair in H9. rewrite H9. eapply HH. eauto. done. eauto. done. done.
   apply mem_zip in H10. ssa. apply (allP H4) in H10. done. rewrite /dom -H //. ssa.

 * intros. apply/H0;eauto. apply checkPath_fe in HC2. rewrite full_eunf_subst in HC2. apply checkPath_fe2 in HC2. done. 
   rewrite makeL_fe2 full_eunf_subst -makeL_fe2  in Heqn2. eauto.
   rewrite makeL_fe2 full_eunf_subst -makeL_fe2  in Heqn. eauto.
   rewrite makeQ_fe full_eunf_subst -makeQ_fe  in Hall. eauto.
   rewrite uniq_labels_subst;ssa. case: n;ssa.
   done. 


   have : v' :: y' = [::v']++ y'. done.
   move=>xeq. rewrite xeq catA in HC Hcat.
   apply checkPath_cat in HC.
   rewrite makeQ_cat2 in Hcat.
   have:  makeQ x e ++ (c, v) :: makeQ y' (makeL (x ++ [:: v']) e) = 
          (makeQ x e ++ [::(c, v)]) ++ makeQ y' (makeL (x ++ [:: v']) e).
   rewrite -catA //. move=> xeq0. rewrite xeq0 in Hcat. clear xeq0.
   have : forall (A : Type) (l0 l1 l2 l3 : seq A), l0 ++ l1 = l2 ++ l3 -> size l0 = size l2 ->  l0 = l2.
   intros. have : take (size l0) (l0 ++ l1) = take (size l2) (l2++l3). rewrite H.
   rewrite !take_size_cat //.  rewrite !take_size_cat //. 
   move=>Hseq. apply Hseq in Hcat. 2: {  rewrite !size_cat !makeQ_size. rewrite !size_cat.  done.
  apply checkPath_cat in HC. done. done. } 
   clear xeq.
   rewrite makeQ_cat2 in Hcat.
   apply checkPath_cat in HC as HC2.
   have : forall (A : Type) (l0 l1 l2 l3 : seq A), l0 ++ l1 = l2 ++ l3 -> size l0 = size l2 ->  l1 = l3.
   intros. have : drop  (size l0) (l0 ++ l1) = drop (size l2) (l2++l3). rewrite H.
   rewrite !drop_size_cat //.  rewrite !drop_size_cat //. 
   clear Hseq => Hseq.
   apply Hseq in Hcat;last by []. ssa.
   destruct (obs _ _) eqn:Heqn;ssa. destruct (nexte_wrap _ _) eqn:Heqn2;ssa. inv Hcat.
   clear Hcat Hseq. clear Heqn2.
   
   move : HE x v' HC HC2 Heqn Hall Hun. clear.
   move Heq : (Sd,_,_) => l HE.
   move: HE c v Heq.
   elim.
* intros. inv Heq. de x. de o. by rewrite eqxx in H3. de o. by rewrite eqxx in H3. 
* intros. inv Heq. de x. de o. eauto.
* intros. inv Heq. de x. de o. destruct (lookup _ _) eqn:Heqn2;ssa. neqt.
  de o. destruct (lookup es n0) eqn:Heqn2;ssa. neqt. 
* intros. inv Heq. de x. de o. destruct (lookup es0 n) eqn:Heqn3;ssa.
  apply in_pair in Heqn3. have : size es0 = size es1 by eauto.
  move=>Hsize. move/in_zip1 : Heqn3. move/(_ _ _ Hsize). ssa.
  de x0. move: (H12).
  have : uniq (dom es0).  done.
  move=>Hun.
  move/same_label. move/(_ H Hun). intros. subst.
  move/inP:(H12).
  move/H1. simpl. move=>HH. 
  apply uniq_in_pair in H11. rewrite H11. eapply HH. eauto. eauto. done.  eauto. done. 
  apply mem_zip in H12. ssa. apply (allP H4) in H12. done. 
  rewrite /dom -H. done. 
 * intros. apply/H0;eauto. apply checkPath_fe in HC. rewrite full_eunf_subst in HC. apply checkPath_fe2 in HC. eauto.
   apply checkPath_fe in HC2. rewrite full_eunf_subst in HC2. apply checkPath_fe2 in HC2. eauto.
   rewrite makeL_fe2 full_eunf_subst -makeL_fe2  in Heqn. eauto.
   rewrite makeQ_fe full_eunf_subst -makeQ_fe  in Hall. eauto.
   rewrite uniq_labels_subst;ssa. case: n;ssa.

  
by apply checkPath_cat in HC.
by [].

  f_equal.

destruct (eqVneq x3 p_receive).
move : e => Hp_rec.
   have : Project G x3 (trans x3 G).
   move: (H2 x3). ssa. apply:Project_EQ2. eauto. apply:proj_proj. done.

  move/proj_proj. 
  move/EQ2_eunf2.
  move/makeQ_EQ2=><-.


rewrite Hp_rec.

have : uniq_labels (fe (trans p_receive G)).
apply:uniq_full_unf. apply:uniq_trans. done. clear Hun => Hun.

have : lInvPred (fe (trans p_receive G)).
apply -> lInvPred_iff. apply:gInvPred_proj.  
apply/gInvPred_iff. apply:Project_gtree. eauto. move=>Hinv.
rewrite makeQ_fe. symmetry. rewrite -makeQ_fe. symmetry.
move : H_receive. move=>HE.
move : HE H_check_receive Hun Hinv.  move : (fe _) => e. clear.
move : (lp_fun p_receive) => lp'.
move Heq : (Rd,c,v) => l.
move=>HE.
elim : HE c v Heq lp'.
- intros. de lp'. de o. rewrite /obs /= in H. de d. 
- intros. inv Heq. de lp'. de o. f_equal.  apply:H0;eauto. punfold Hinv.  inv Hinv. inv H0. de H5.
- intros. de lp'. de o. rewrite /obs /= in H0. de d.
- intros. de lp'. de o. destruct (lookup _ _) eqn:Heqn2;ssa. inv Heq.
  apply in_dom in Heqn2 as HH. rewrite /dom H in HH. apply in_dom_exists in HH. ssa. rewrite H7. f_equal.
  apply in_pair in Heqn2, H7.
  eapply uniq_in_zip in H7. 4:apply Heqn2. move/inP : H7. move/H1.
  move/(_ _ _ Logic.eq_refl)=>/=. move=>xx. apply:xx; eauto. 
  apply (allP H4) in Heqn2. done.
  punfold Hinv. inv Hinv. inv H7. move/ForallP : H9 => HAll. move/inP : Heqn2. move/HAll.
  case;ssa.
  rewrite /dom //. done. 
- intros. 
  erewrite makeQ_EQ2. apply/H0. eauto.
  apply checkPath_fe in H_check_receive. rewrite full_eunf_subst in H_check_receive.
  apply checkPath_fe2 in H_check_receive. done.
  apply uniq_full_unf in Hun. rewrite full_eunf_subst in Hun. 
  apply uniq_full_unf2 in Hun. done.

  apply lInvPred_iff in Hinv. rewrite full_eunf_subst in Hinv.
  apply <- lInvPred_iff in Hinv. done.

  apply/EQ2_eunfl. rewrite full_eunf_subst. apply/EQ2_eunfl2. 
  apply/EQ2_refl. 
  apply lInvPred_iff in Hinv. rewrite full_eunf_subst in Hinv.
  apply <- lInvPred_iff in Hinv. done.



apply/makeQ_EQ2.
apply:EQ2_eunf2. apply:EQ2_eunfl2.
move: (H2 x3). ssa.
apply:preserve_proj2. eauto. eauto.
apply/gInvPred_iff/Project_gtree. eauto.
simpl. rewrite /comp_dir /=.
rewrite H4. case_if. norm_eqs. inv H6.
rewrite eqxx in i. done. done. done.
done. 
rewrite /comp_dir /= eqxx. case_if;ssa.
apply label_pred in HStep. ssa. rewrite (eqP H1) in HStep.
neqt. done. done. done. done.
rewrite /comp_dir. ssa. rewrite eqxx. done.
done. done. done. 

by inv HCoG;ssa.
by inv HCoG;ssa.
by inv HCoG;ssa.
apply/eqP. intro. subst.
 apply to_canEstep2 in H_Estep2.
eapply makeQ_ETr3 in H_Estep2;eauto.
ssa. eapply test_test in H4. 7:eauto.
7: {   rewrite H3 in H_makeQ_safe. eauto. }
apply/negP.  apply (allP H4). apply : H6. done.
apply:Project_eunf2. apply:Project_EQ2. apply : HP_receive.
apply:EQ2_refl. apply:gInvPred_proj. 
apply/gInvPred_iff/Project_gtree. eauto. 

by inv HCoG;ssa.
by inv HCoG;ssa. done.
by inv HCoG;ssa. ssa.
apply/allP. intro. move/(allP H0). ssa. 
apply/allP. intro. move/(allP H2). ssa.
by inv HCoG;ssa.
by inv HCoG;ssa.
by inv HCoG;ssa.
done. done. done.

- inv Hoft. apply H0 in H5. ssa.
  econ. econ. con. 2: {  econ. eauto. eauto. }  done.
  inv Hside. ssa. move : H13 H14 => Henv Hgood.  con;ssa.
  intro. ssa. 
  apply in_dom in H13 as HH. rewrite dom_insertS1 in HH.
  rewrite inE in HH. de (orP HH). norm_eqs.
  rewrite /insertS1 /insert_shift /insert lookup_cons_eq //= in H13. inv H13.
  de (mapP H14).  subst.
  rewrite /insertS1 /insert_shift /insert lookup_cons_neq //= in H13. 
  apply lookup_map in H13. ssa. eauto. de x. de v.
  move : H8. rewrite /only_var_val. rewrite dom_insertS1. ssa.
  rewrite all_map. apply/allP. intro. ssa. apply (allP H8) in H13. 
  de x. de v.

- inv Hoft. inv H3. inv H4. inv H5. apply H0 in H8.
  ssa. inv H1.
  econ. econ. con. 2: { econ. 5:eauto. 4:eauto. econ. econ. econ. } econ.
  apply lookup_filter_q_2 in H7. ssa.

  have : forall (l : q_env) f a b, filter_q (update l a b) f = filter_q (update l a (filter_keys (f a) b)) f.
  intros. rewrite /filter_q /update /filter_keys -!map_comp. apply/eq_in_map.
  intro. ssa. case_if. ssa. f_equal.  rewrite -filter_predI. apply/eq_in_filter. intro.
  ssa. norm_eqs. lia.  f_equal.
  move=>HQ_lem. 

  destruct (f1 (QKey s p) c) eqn:Heqn.
  econ. econ. con. 2: { econ. 5:eauto. 4:eauto. rewrite update_filter_keys.
                        apply lookup_filter2 in H6. ssa.
                        have : filter_keys (predC f0) E = update (filter_keys (predC f0) E) (schlT s p) (fe T').
                        rewrite update_none. done.
                        apply/negP. intro. rewrite dom_filter_keys mem_filter in H11. ssa.
                        rewrite /predC H6 in H13. done. rewrite update_filter_keys. move=>->. econ.
                        instantiate (2:= update Q0 (QKey s p) (x ++ [:: (c,v)])).
                        rewrite /partition_q. f_equal.

instantiate (1:= f1). subst.
have: (filter_keys (f1 (QKey s p)) x ++ [:: (c, v)]) = (filter_keys (f1 (QKey s p)) (x ++ [:: (c, v)])).
rewrite filter_keys_cat.
have: filter_keys (f1 (QKey s p)) [:: (c, v)] = filter_keys predT [:: (c, v)].
apply/filter_keys_eq. intro. ssa. norm_eqs. rewrite Heqn. done.
move=>->. rewrite filter_keys_predT. done.
move=>->.
                        rewrite update_filter_q. 
rewrite -HQ_lem. done. 
intro. ssa. rewrite dom_filter_keys mem_filter in H7. ssa.

rewrite HQ_lem. rewrite filter_keys_cat.
have: filter_keys (hrelC f1 (QKey s p)) [:: (c, v)] = filter_keys pred0 [:: (c, v)].
apply/filter_keys_eq. intro. ssa. tunf. norm_eqs. rewrite Heqn. done.
move=>->. rewrite filter_keys_pred0 cats0.  rewrite -HQ_lem.
rewrite update_same;ssa. inv Hside. ssa. econ. } econ;eauto. apply lookup_filter2 in H6. ssa.


  econ. econ. con. 2: { econ. 5:eauto. 4:eauto. rewrite update_filter_keys.
                        apply lookup_filter2 in H6. ssa.
                        have : filter_keys (predC f0) E = update (filter_keys (predC f0) E) (schlT s p) (fe T').
                        rewrite update_none. done.
                        apply/negP. intro. rewrite dom_filter_keys mem_filter in H11. ssa.
                        rewrite /predC H6 in H13. done. rewrite update_filter_keys. move=>->. econ.
                        instantiate (2:= update Q0 (QKey s p) (x ++ [:: (c,v)])).
                        rewrite /partition_q. f_equal.

                        instantiate (1:= hrelU f1 (fun k v => (k == QKey s p)&& ((v == c)))).
have : all (fun v => v.1 != c) l.
apply/allP. intro. ssa. apply linearity.in_split in H10. ssa.
subst.
apply in_pair in H9.
apply/eqP. intro. de x0. subst.  
have : (c,s0) \in x1 ++ (c, s0) :: x2. rewrite mem_cat inE eqxx // orbC //. 
rewrite -H10. move/in_filter_keys. ssa. rewrite Heqn in H7. done.
move=>Hall.
subst.
move Hf : (hrelU f1 (fun k v => (k == QKey s p)&& ((v == c))))=> f3. 
eapply has_coin in H2. 2: { erewrite lookup_update_in. econ. rewrite dom_filter_q. apply in_dom in H9. done. } 
2: { rewrite mem_cat. apply/orP. right. done. } 
rewrite dom_filter_keys mem_filter in H2. ssa.
have : c \notin dom x.
apply/negP. intro. de (mapP H2). de x0. subst.



have : schliT s c0 \notin dom (filter_keys (predC f2) C). rewrite dom_filter_keys mem_filter negb_and /predC H7 //=. 
intros. eapply has_coin_not in x0. 2:eauto. 2: { apply/lookup_filter_q. eauto. econ. } 
move: x0.
instantiate (1:= s0). intro. apply/negP. apply/x0. apply/in_filter_keys2. subst. done.
tunf. ssa. rewrite Heqn. done.
move=>Hdom.
have: (filter_keys (f1 (QKey s p)) x ++ [:: (c, v)]) = (filter_keys (f3 (QKey s p)) (x ++ [:: (c, v)])).
rewrite filter_keys_cat.
have: filter_keys (f3 (QKey s p)) [:: (c, v)] = filter_keys predT [:: (c, v)].
apply/filter_keys_eq. intro. ssa. norm_eqs. 
tunf. rewrite Heqn !eqxx //=.
move=>->. rewrite filter_keys_predT. f_equal.
apply/filter_keys_eq. intro. ssa.  subst. tunf. rewrite eqxx. 

destruct (eqVneq x0 c). subst. rewrite H2 in Hdom. done. ssa. rewrite orbC //.

move=>->. 
have : forall (A B : eqType) (l l' : seq (A * B)), dom l = dom l' -> uniq (dom l) ->  (forall lk, lookup l lk = lookup l' lk) -> l = l'.
move=> A B. elim. de l'. ssa. de l'. inv H11. de a. de p0.
subst. move : (H14 s2). rewrite !lookup_cons_eq //=. case. move=>->. f_equal. 
apply/H2. done. done. intros. 
destruct (lk \in dom l) eqn:Heqn2.
move: (H14 lk). rewrite !lookup_cons_neq. done.  ssa.
apply/eqP. intro. subst. rewrite Heqn2 in H15. done.
ssa.
apply/eqP. intro. subst. rewrite Heqn2 in H15. done.
rewrite !lookup_notin //. rewrite -H18 Heqn2 //.  rewrite Heqn2 //.
move=> H_map_eq. apply/H_map_eq.
rewrite !dom_filter_q !dom_update dom_filter_q //. rewrite dom_filter_q dom_update. inv Hside. by ssa.
intros.
rewrite filter_q_update.
destruct (eqVneq (QKey s p) lk). subst.
rewrite !lookup_update_in. done. rewrite dom_filter_q //.  apply in_dom in H9. done.
rewrite dom_filter_q. apply in_dom in H9. done.
rewrite !lookup_update_neq2;ssa.
destruct (lookup (filter_q _ _) lk) eqn:Heqn2. ssa.
de lk.
apply lookup_filter_q_2 in Heqn2. ssa.
erewrite lookup_filter_q. eauto. eauto. subst.
apply/filter_keys_eq. intro. ssa. tunf. 
rewrite neg_sym in i. rewrite (negbTE i).
destruct (eqVneq x1 c). subst.  rewrite /= orbC /=. done.
rewrite orbC //=. rewrite lookup_notin. done.
rewrite dom_filter_q.
have : lk \notin dom (filter_q Q0 f3). apply/negP. intro.
apply in_dom_exists in H2. ssa. rewrite Heqn2 in H2. ssa.
rewrite dom_filter_q. done.

move Hf : (hrelU f1 (fun k v => (k == QKey s p)&& ((v == c))))=> f3. 
rewrite HQ_lem. rewrite filter_keys_cat.
have: filter_keys (hrelC f3 (QKey s p)) [:: (c, v)] = filter_keys pred0 [:: (c, v)].
apply/filter_keys_eq. intro. ssa.
tunf. norm_eqs. tunf. rewrite negb_or !eqxx // negb_and /= andbC //.
move=>->. rewrite filter_keys_pred0 cats0.
rewrite -HQ_lem. rewrite update_same;ssa.

have : all (fun v => v.1 != c) l.
apply/allP. intro. ssa. apply linearity.in_split in H10. ssa.
subst.
apply in_pair in H9.
apply/eqP. intro. de x0. subst.  
have : (c,s0) \in x1 ++ (c, s0) :: x2. rewrite mem_cat inE eqxx // orbC //. 
rewrite -H10. move/in_filter_keys. ssa. rewrite Heqn in H7. done.
move=>Hall.


eapply has_coin in H2. 2: { erewrite lookup_update_in. econ. rewrite dom_filter_q. apply in_dom in H9. done. } 
2: { rewrite mem_cat. apply/orP. right. done. } 
rewrite dom_filter_keys mem_filter in H2. ssa.
have : c \notin dom x.
apply/negP. intro. de (mapP H2). de x0. subst.
have : schliT s c0 \notin dom (filter_keys (predC f2) C). rewrite dom_filter_keys mem_filter negb_and /predC H10 //=. 
intros. eapply has_coin_not in x0. 2:eauto. 2: { apply/lookup_filter_q. eauto. econ. } 
move: x0.
instantiate (1:= s0). intro. apply/negP. apply/x0. apply/in_filter_keys2. subst. done.
tunf. ssa. rewrite Heqn. done.
move=>Hdom. 

apply/filter_q_eq2. intro. ssa. tunf.
subst. tunf. rewrite negb_or negb_and //=.
destruct (eqVneq z c). subst. ssa. rewrite orbC //=.
destruct (eqVneq x0 (QKey s p)). subst. ssa. rewrite andbC //=.

rewrite Heqn //=. 
apply uniq_in_pair in H2. rewrite H2 in H9. inv H9.  
rewrite H13 in Hdom. done. inv Hside. by ssa.
rewrite /= andbC //.
rewrite /= orbC //= andbC //. inv Hside. ssa. econ. } econ;eauto. apply lookup_filter2 in H6. ssa.

move : H6 H7 H8 H9 => Hall H6 H7 H8.

apply lookup_filter2 in H6. ssa. apply lookup_filter_q_2 in H7. ssa.
have : f1 (QKey s p') c.

have : (c,v) \in  l0 ++ (c, v) :: l. rewrite mem_cat inE eqxx orbC //=.
rewrite -H7. rewrite /filter_keys mem_filter. move/andP. case.
intros.  ssa.
move=>Hf1.

have : forall (A B : eqType) (l : seq (A * B)) l0 v l1 f, filter_keys f l = l0 ++ (v::l1) -> exists l0' l1', l = l0' ++ v::l1' /\ filter_keys f l0' = l0 /\ filter_keys f l1' = l1.
move=> A B. clear. elim;ssa. de l0. 
move : H0. case_if. de l0. inv H1.
exists nil. exists l. ssa. 
inv H1. apply H in H4. ssa. 
exists (p::x),x0. subst. ssa. rewrite H0. done.
move/H. ssa. exists (a::x),x0. subst. ssa. rewrite H0. done.
move=>Hfilter. apply Hfilter in H7.
ssa. clear Hfilter.
have : all (fun x => x.1 != c) x0.
apply/allP. intro. ssa.
destruct (f1 (QKey s p') x2.1) eqn:Heqn.
subst.
rewrite /filter_keys all_filter in Hall.

apply (allP Hall) in H14. ssa. apply (implyP H14). done.
apply/eqP. intro. de x2. subst. rewrite Hf1 in Heqn. done.

subst. move=>Hall2.

econ. econ. con. 
apply:LQ3. 2:eauto. 2:eauto. 2:eauto. done. econ. econ. 

econ. 4:eauto. 4:eauto.

rewrite /partition.

instantiate (1:= f0).
rewrite update_filter_keys. f_equal.
rewrite filter_keys_update. rewrite update_none. done.

rewrite dom_filter_keys mem_filter negb_and /predC H6 //=.  
rewrite /partition_q. instantiate (1:= f1).
f_equal. rewrite filter_q_update. rewrite filter_keys_cat. done. 
rewrite filter_q_update.
rewrite update_same. done.
eapply lookup_filter_q. eauto. 
rewrite !filter_keys_cat. f_equal.
ssa. rewrite /hrelC Hf1 /=. done.
rewrite dom_filter_q. inv Hside. by ssa. econ.
ssa.
move : Hside. rewrite /side_conds. ssa. move : H17 => Hgood.


rewrite /env_not_rec /filter_keys all_filter. 
apply/allP. intro. ssa. apply/implyP. intro. asimpl.
apply (allP H2) in H17. ssa.
move : H6. rewrite /partial_balanced. ssa.
subst. econ. econ. econ. econ. con. eauto. con. rewrite filter_keys2. econ.
rewrite filter_q2. econ. 
move : H7. rewrite /both_closed. ssa.
move : H7. rewrite /sch_closed. ssa. move: (H7 n).  rewrite mem_cat negb_or //. ssa.
move : H16. rewrite /valBool_closed. ssa. 

move: (H18 n). simpl. rewrite mem_cat negb_or //. ssa.
move : H9. rewrite /only_schl dom_filter_keys all_filter. ssa. apply/allP. intro.
ssa. apply (allP H9) in H18. apply/implyP. intro. done.
rewrite dom_filter_q //.
rewrite dom_filter_keys. rewrite filter_uniq;ssa.
move : H14. rewrite /sub_domLQ. ssa.
rewrite dom_filter_keys mem_filter in H18.  ssa. apply H14 in H20.
rewrite dom_filter_q. done.


-  have : DOFT Ms Ds D0 P0 E Q0 C. 
   con. inv Hside. ssa. done.
   intros. eapply DOFT_cong in x;eauto.
   inv x. apply H1 in H4.  
   ssa. 
   have : DOFT Ms Ds D0 Q' x0 x1 C. con. done. done.
   intros. eapply DOFT_cong in x2;eauto. 
   inv x2. econ. econ. con. 2:eauto. done.
   inv Hside. ssa. 
   inv H4. rewrite dom_update. done. rewrite dom_update. done.
   apply/proc_pred_red. eauto. 
   inv Hside. ssa. inv x2. inv H19. ssa.
   apply/proc_pred_pres. apply/CSym. eauto. inv Hside. ssa. inv H9. ssa.

   inv Hside. ssa.
   inv H4. rewrite dom_update. done. rewrite dom_update. done. 
   inv Hside. ssa.

   rewrite /only_vars. apply/allP. intro. ssa.
   apply (allP H11) in H18. de x3.
   inv Hside. ssa. con;ssa. 

   move : H8. rewrite /both_closed. ssa.
   intro. apply/negP. intro. apply/negP. apply (H8 n).
   apply:Cong_sch_fv2. 2:eauto.  done.
   intro. apply/negP. intro. apply/negP. apply (H17 n).
   apply:Cong_valBool_fv2. eauto. done.
   apply/proc_pred_pres. apply/CSym. apply:H. done.
   
   inv Hside. ssa.
   inv Hside. ssa. inv H6. ssa.
   inv Hside. ssa.
   inv Hside. ssa.
   move : H8. rewrite /only_var_val /only_vars.
   intros. apply/allP. intro. ssa. apply (allP H8) in H15. de x0.
Qed.


Lemma EQ_same_sym : forall (A : eqType) (E0 E1 : seq (A * lType)), EQ_same E0 E1 -> EQ_same E1 E0.
Proof.
intros. move : H. rewrite /EQ_same. ssa. intros. rewrite H. done.
intros. apply/EQ2_sym. eauto.
Qed.

Lemma OFT_EQ_same : forall Ms Ds P E E' Q C (Hun : (uniq (dom E))) (Hun' : uniq (dom E')) (He : envP E (fun e : lType_EqType => uniq_labels e)) (Hnr : env_not_rec E) (Hnr' : env_not_rec E'), OFT Ms Ds P E Q C -> EQ_same E E' -> OFT Ms Ds P E' Q C.
Proof.
intros.
apply/ OFT_weaken_swap_EQ. apply H. done. done.
2: { erewrite filter_keys_eq. erewrite filter_keys_pred0. done.
     intros. tunf. inv H0. rewrite -H2 in H1. apply/negP/negP. done. } 
2:done.
intros.

inv H0.
apply in_dom in H1 as Hd.
rewrite H2 in Hd. apply in_dom_exists in Hd. ssa.
eapply H3 in H1 as HH. 2:eauto. exists x. con. done.
ssa. apply in_pair in H1. apply (allP Hnr) in H1. done.
apply in_pair in H4. apply (allP Hnr') in H4. done.
Qed.


Lemma val_in_reduce : forall P n, n \in proc_valBool_fv (reduce_link P) -> n \in proc_valBool_fv P.
Proof. 
elim/process_ind;ssa.  
apply subst_proc_valBool_fv in H0. ssa. rewrite /ids in H1. inv H1.
apply subst_proc_valBool_fv in H0. ssa. rewrite /ids in H1. inv H1.
rewrite mem_cat in H1. de (orP H1).
rewrite mem_cat. ssa.
rewrite mem_cat. ssa.
Qed.

Lemma make_queues_no_valBool_var : forall c n, n \notin proc_valBool_fv (make_queues c). 
Proof. 
elim;ssa.  
Qed. 

Lemma Cong_no_valBool : forall P P' n, Cong P P' -> n \in proc_valBool_fv P' <-> n \in proc_valBool_fv P.  
Proof. 
move => P P' n H. 
elim : H n;ssa;rewrite ?mem_cat.
split;ssa.
de (orP H);ssa.
split;ssa. apply/orP. rewrite orbC. done.
rewrite orbC in H. apply/orP. done.
rewrite orbA. done.
split. move/orP. case. ssa.
move/subst_proc_valBool_fv. ssa. eauto. rewrite /ids in H0.
inv H0. eauto.
move/orP. case. ssa.
intros. apply/orP. right. 
apply/proc_valBool_subst. done.
split. move/orP. case. ssa.
move/subst_proc_valBool_fv. ssa. rewrite /ids in H0. inv H0. ssa.
move/orP. case. ssa.
ssa. right. apply/proc_valBool_subst. done.
rewrite H0. done.
rewrite -H0.
rewrite -H2. done.
Qed. 

Lemma Sem_no_val : forall D P P' n (Hd : (forall d n, d \in D -> n \in proc_valBool_fv d -> n = 0)), Sem D P P' ->  n \in proc_valBool_fv P' -> n \in proc_valBool_fv P.  
Proof. 
move => D P P' n Hd H. 
elim : H Hd n;ssa.
- rewrite mem_cat in H0. destruct (orP H0). apply val_in_reduce in H1. done.
  move : (@make_queues_no_valBool_var (make_cs q) n). rewrite H1 //=. 
- rewrite mem_cat in H0. destruct (orP H0). rewrite !mem_cat H1 //=. lia.
  destruct (flattenP H1). destruct (mapP H2). subst. rewrite !mem_cat. 
  rewrite mem_cat in H4.
  de (orP H4). right.
  apply/flattenP. econ. apply/mapP. econ. eauto. done. done.
  rewrite inE in H5. norm_eqs. inv H. ssa. rewrite H3. ssa.

- rewrite mem_cat in H. destruct (orP H). rewrite mem_cat H0 //=. 
  rewrite mem_cat.  apply/orP. right. 
  destruct (flattenP H0). destruct (mapP H1). subst. rewrite mem_cat in H3. 
  destruct (orP H3). apply/flattenP. econ. eauto. done. ssa. rewrite inE in H4. norm_eqs. ssa. 

- rewrite mem_cat in H. destruct (orP H). rewrite mem_cat H0 //=. 
  destruct (flattenP H0). destruct (mapP H1). subst. rewrite mem_cat. apply/orP. right. 
  apply/flattenP. rewrite mem_cat in H3. destruct (orP H3). exists (msgp_valBool_fv x0).  apply/map_f. ssa.  done.
  ssa. rewrite inE in H4. norm_eqs.  ssa.

- rewrite mem_cat in H. destruct (orP H). rewrite /my_subst_valBool in H0. 
  apply subst_proc_valBool_fv in H0. destruct H0. ssa. 
  asimpl in H1. de x. 
  rewrite mem_cat. apply/orP. right.  subst. ssa.

  rewrite mem_cat. apply/orP. left.
  apply/mapP. econ. rewrite mem_filter. apply/andP. con. 2:eauto. done. simpl.
  inv H1. rewrite !mem_cat. apply/orP. right. apply/orP. right. done.
  
- rewrite mem_cat in H. destruct (orP H). rewrite /my_subst_schl in H0. 
  apply subst_proc_valBool_fv in H0. destruct H0. ssa. rewrite /ids in H1. inv H1.
  rewrite mem_cat. apply/orP. left. done. 
  rewrite mem_cat. apply/orP. right. done. 

- rewrite mem_cat in H0. destruct (orP H0). 
  rewrite mem_cat. apply/orP. left. apply/flattenP. exists (proc_valBool_fv P0).
  have : P0 = (l,P0).2 by done. move=>->. apply/map_f. apply/in_pair. done. done.
  rewrite mem_cat H1. lia. 

- rewrite !mem_cat H0 //=. lia.

- rewrite !mem_cat H0. lia. 

- ssa. apply subst_proc_valBool_fv in H1. destruct H1. ssa. 
  asimpl in H2. de x. subst. inv H. ssa. inv H2. 
  apply Hd in H1. done.  apply/nthP. econ. eauto. done.
- move : H1. rewrite !mem_cat. move/orP. case;eauto.  move/H0. move=>-> //=. 
  move=>->. lia. 
  
apply/Cong_no_valBool. apply/CSym. eauto. 
  apply/H1. eauto.
  apply/Cong_no_valBool. apply/CSym. eauto. done.
Qed. 

Lemma envP_lq : forall E Q E' Q', LQ_red E Q E' Q' -> envP E (fun e : lType => uniq_labels e) ->
envP E' (fun e : lType => uniq_labels e).
Proof. 
intros.
intro. intros. inv H. apply/H0. eauto.
destruct (eqVneq (schlT s p) lk). subst.

rewrite lookup_update_in in H1;ssa.
inv H1.
apply/uniq_full_unf. apply H0 in H2. inv H4.
ssa. apply (allP H6) in H10. done.
apply in_dom in H2. done.
rewrite lookup_update_neq2 in H1;ssa.
apply/H0. eauto.

destruct (eqVneq (schlT s p) lk). subst.

rewrite lookup_update_in in H1;ssa.
inv H1.
apply/uniq_full_unf. apply H0 in H3. inv H5.
ssa. apply (allP H7) in H11. done.
apply in_dom in H3. done.
rewrite lookup_update_neq2 in H1;ssa.
apply/H0. eauto.
Qed.

Lemma not_rec_pres : forall E Q E' Q' (Ho : only_schl E) (Hsub:  sub_domLQ E Q),   uniq (dom E) ->
  env_coherent E Q -> LQ_red E Q E' Q' -> env_not_rec E -> env_not_rec E'.
Proof.
intros.
inv H1;ssa.
apply/allP. intro. ssa. apply in_update in H6. de H6. subst. 
asimpl. ssa.
eapply env_coherent_lInvPred in H0. 5:eauto.
inv H5. punfold H0. inv H0. inv H6. de H8. punfold H7. inv H7. inv H8.
punfold H0. inv H0. inv H6. move/ForallP : H8. move/inP : H11. move=>HH. move/(_ _ HH).
case;ssa. punfold a. inv a. inv H7. done.  done. done.
asimpl.

apply (allP H2) in H6. done.

apply/allP. intro. ssa. apply in_update in H7. de H7. subst. 
asimpl. ssa.
eapply env_coherent_lInvPred in H0. 5:eauto.
inv H6. punfold H0. inv H0. inv H7. de H9. punfold H8. inv H8. inv H9.
punfold H0. inv H0. inv H7. move/ForallP : H9. move/inP : H12. move=>HH. move/(_ _ HH).
case;ssa. punfold a. inv a. inv H8. done.  done. done.
asimpl. 

apply (allP H2) in H7. done.
Qed.

(*add no rec to EQ_same, and def var predicate*)
Lemma subject_reduction_full : forall D P P' Ms Ds E Q C, Sem D P P' -> side_conds2 Ds D Ms P E Q ->  OFT Ms Ds P E Q C ->  
exists E' E'' Q', LQ_red E Q E' Q' /\ EQ_same E' E'' /\ OFT Ms Ds P' E'' Q' C /\ side_conds2 Ds D Ms P' E'' Q'.
Proof.
intros.
eapply subject_reduction in H as Hu;eauto. ssa.
apply  env_coherence_pres in H2 as HH. ssa. move : H7 => Hnr.
econ. econ. econ. con. apply H2. con. apply/EQ_same_sym. apply H5. con. 
apply:OFT_EQ_same. 6:eauto.
apply pres_dom_same in H2. ssa. rewrite -H2 //. inv H0. ssa. done.

apply envP_lq in H2. 
intro. intros. inv H5.

apply in_dom in H7 as Hd. rewrite -H8 in Hd. apply in_dom_exists in Hd. ssa.
apply H2 in H7. done. inv H0. ssa. 
apply:not_rec_pres. 5:eauto.  all: try solve [inv H0;ssa].


apply/EQ_same_sym. done.
inv H0. con;ssa. 
con. apply/Sem_closed. eauto. inv H10. 
con. intro. apply/negP. intro. eapply Sem_no_val in H19. 3:eauto.
inv H10. ssa. apply/negP. apply H21. eauto. inv H16. ssa. eauto.


apply:proc_pred_red. eauto. inv H16. ssa. inv H10. ssa.
rewrite /only_schl.
apply/allP. intro. ssa. inv H5. 
de x2. rewrite H20 in H19.
apply pres_dom_same in H2. ssa. rewrite -H2 in H19.
rewrite /only_schl in H11.
apply (allP H11) in H19. done.

apply pres_dom_same in H2. ssa. rewrite -H19. done.
apply pres_dom_same in H2. ssa. 
intro. move=>p. inv H5. rewrite H20. rewrite -H2.
move/H15. rewrite H19. done.

suff : envP x uniq_labels.
intros. inv H5. ssa.
intro. intros. 
apply in_dom in H21 as Hdom. rewrite H19 in Hdom.
apply in_dom_exists in Hdom. ssa.
eapply H20 in H21. 2:eauto.
apply:labels_preserve. apply/EQ2_sym. eauto.
eauto.

apply:envP_lq. eauto.  done.

all: try solve [inv H0; ssa].


inv H0. ssa. con;ssa.
suff : balanced E Q. intros.
econ. econ. econ. econ. econ. eauto.
erewrite filter_keys_predT. erewrite filter_q_predT. done. 
apply:coherent_balanced;ssa.
Qed.

