From mathcomp Require Import all_ssreflect zify.

Require Export MPSTSR.IndTypes.elimination.
Require Export MPSTSR.CoTypes.coLocal.
Require Import Paco.paco.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition eenum ee := utils.compose (enum ee.1) (enum ee.2) pair. 
Definition unfee (ee : lType * lType) := (full_eunf ee.1,full_eunf ee.2).
Definition nextee ee := 
let (e0,e1) := unfee ee in (zip (nexte e0) (nexte e1)). 

Definition oute e := 
match e with 
| EMsg d c u g => Some (Some (d, c, inr u))
| EBranch d c gs => Some (Some (d, c,inl (map fst gs)))
| EEnd => Some None
| _ => None  
end. 


Definition outee (ee : lType * lType) := 
let (e0,e1) := unfee ee in
match oute e0,oute e1 with 
| Some e0, Some e1 => e0 == e1
| _,_ => false 
end. 


Lemma selfee : forall pp, pp \in eenum pp. 
Proof. case. intros. rewrite /eenum /=. apply/mem_compose; apply/selfe. 
Qed.

Lemma eenum_closed_nextee  : forall pp, next_closed (eenum pp) nextee. 
Proof. 
rewrite /next_closed. case. rewrite /eenum /=.  
intros. destruct a'. destruct a0. apply mem_compose2 in H. rewrite /nextee in H0. 
apply mem_zip in H0. ssa. apply/mem_compose; apply/enum_closed_nexte_unf;eauto. 
Qed.

Lemma eenum_subst_next_unf : forall e e' e'', e' \in nextee e -> e'' \in eenum e'  -> e'' \in eenum e.  
Proof. 
intros. rewrite /nextee in H.  rewrite /eenum. destruct e''.
apply mem_compose2 in H0. destruct H0.
destruct e. simpl. destruct e'. simpl in H0,H1.  
rewrite /unfee in H. ssa.
move/mem_zip : H. ssa. 
apply/mem_compose. apply/enum_subst_nexte_unf. 2 : eauto. done.
apply/enum_subst_nexte_unf. 2 : eauto. done. 
Qed.




Definition eemeasure (pp : lType * lType) (visited : seq (lType * lType)) := 
size (rep_rem visited (undup (eenum pp))). 


Lemma eemeasure_lt : forall l l0 l1 l2 visited,
  ((l1, l2) \in visited) = false ->
   In (l, l0) (nextee (l1, l2)) ->
  eemeasure (l, l0) ((l1, l2) :: visited) < eemeasure (l1, l2) visited.
Proof.
move=> l l0 l1 l2 visited e0 i. 
simpl. rewrite /eemeasure /=.
destruct ((l1,l2) \in ((eenum (l,l0)))) eqn:Heqn.
apply/size_strict_sub. 
apply/rem_uniq/rep_rem_uniq/undup_uniq. 
intros. destruct (eqVneq x (l1,l2)).  subst. rewrite -mem_rep_iff.  rewrite mem_undup. 
apply/selfee. rewrite e0 //=.
apply mem_rem2 in H;eauto. 
destruct (x \in visited) eqn:Heqn2.
eapply rep_rem_uniq2 in Heqn2. 2 : { apply/undup_uniq. apply (eenum (l,l0)). } 
rewrite H in Heqn2. done. 
move : H.  
rewrite -!mem_rep_iff. rewrite  !mem_undup. intros. apply/eenum_subst_next_unf.  apply/inP. eauto. 
done. rewrite Heqn2. done. rewrite Heqn2. done. 
instantiate (1 := (l1,l2)).  apply/negP=>HH. rewrite mem_rem_uniqF in HH. done. 



apply/rep_rem_uniq/undup_uniq. 
rewrite -mem_rep_iff.  rewrite mem_undup. apply/eenum_subst_next_unf. apply/inP. eauto. done. apply/negbT. done.

rewrite rem_id. 2 : { 
apply/negP=>HH. move : Heqn. move/negP=>H2. apply/H2.
apply/mem_rep_iff.  apply/negP. clear H2. eauto. apply/rep_rem2. rewrite e0.  done. 
  2 : { eauto. } intros. rewrite mem_undup in H. done.  }
apply/size_strict_sub.  apply/rep_rem_uniq. apply/undup_uniq. 
intros. 2 : {  apply/negP=>HH. move : Heqn. move/negP=>HH2. apply/HH2.
rewrite -mem_undup. 
rewrite mem_rep_iff.  eauto.  rewrite e0 //=. } 
destruct (x \in visited) eqn:Heqn2.
eapply rep_rem_uniq2 in Heqn2. 2 : { apply/undup_uniq. apply (eenum (l,l0)). } 
rewrite H in Heqn2. done. 
move : H.  
rewrite -!mem_rep_iff. rewrite  !mem_undup. intros. apply/eenum_subst_next_unf.  apply/inP. eauto. 
done. rewrite Heqn2. done. rewrite Heqn2. done. 
rewrite -mem_rep_iff. rewrite mem_undup. apply/selfee.
rewrite e0 //=. 
Qed.

Require Import Program. 
From Equations Require Import Equations. 
Equations bisim (pp : lType * lType) (visited : seq (lType * lType)) : bool by wf (eemeasure pp visited) := 
 bisim pp visited  with (dec (pp \in visited)) => {
  bisim _  _ (in_left) := true;
  bisim  pp visited (in_right) := (outee pp) && 
                                           (foldInAll (nextee pp) (fun e _ => bisim e (pp::visited)));
 }.
Next Obligation. 
apply/ltP. 
apply/eemeasure_lt;eauto.
Defined.

Lemma bisim_sound_aux : forall e0 e1 l_v (R : lType -> lType -> Prop), (forall x0 x1, (x0,x1) \in l_v -> R x0 x1) ->   bisim (e0,e1) l_v -> upaco2 ((ApplyF full_eunf full_eunf \o EQ2_gen)) R e0 e1. 
Proof. 
move => e0 e1 /= l_v R.  intros. funelim (bisim (e0,e1) l_v).
right.  apply/H=>//=.
left. pcofix CIH. pfold. rewrite -Heqcall in H1.
destruct (andP H1).  rewrite foldInAllP in H3. con. 
move : H2. rewrite /outee /unfee /=. 
destruct (full_eunf e1) eqn:Heqn,(full_eunf e2) eqn:Heqn1;try solve [done | intros;constructor].   
ssa. move/eqP : H2. case. ssa. subst. con. apply/H.  4 : { con. }
rewrite /nextee /unfee //= Heqn Heqn1 //=. auto.
intros. rewrite inE in H1. destruct (orP H1). move/eqP : H2. case. intros. subst.  eauto. eauto.
rewrite foldInAllP in H5. apply (allP H5).
rewrite /nextee /unfee //= Heqn Heqn1 //=. auto.

ssa. move/eqP : H2. case. ssa. 

ssa. move/eqP : H2. case. ssa. 

ssa. move/eqP : H2. case. ssa. 
subst. con. apply/size_map_snd. 
done. apply/List.Forall_and.  
clear Heqn Heqn1.
elim : l l0 H6. case. ssa. ssa. destruct l0.  ssa. ssa.  con. ssa. inv H6. 
apply/H1.  inv H6.  
apply/ForallP. intros. apply/H. 4 : con. 
rewrite /nextee /unfee /= Heqn Heqn1.
ssa. ssa. apply/inP.  clear Heqn Heqn1 H6.
elim : l l0 x H1. case.  ssa. ssa. ssa. destruct l0.  ssa. simpl. 
ssa. destruct H2. inv H2. ssa. apply/orP.  eauto.
apply/orP.  right.  apply/H1. 
done. ssa.  rewrite inE in H2. destruct (orP H2). move/eqP : H7. case. intros. subst. eauto. 
eauto. rewrite foldInAllP in H5. apply (allP H5).
rewrite /nextee /unfee /= Heqn Heqn1. simpl.  
clear Heqn Heqn1 H6.
elim : l l0 x H1. case.  ssa. ssa. ssa. destruct l0.  ssa. simpl. 
ssa. destruct H2. inv H2. ssa. apply/orP.  eauto.
apply/orP.  right.  apply/H1. 
done. 
done.
Qed.

Lemma bisim_sound : forall e0 e1, bisim (e0,e1) nil -> EQ2 e0 e1.  
Proof. move => e0 e1 H.
suff : upaco2 ((ApplyF full_eunf full_eunf \o EQ2_gen)) bot2 e0 e1. move => HH. pclearbot. done. 
apply/bisim_sound_aux;eauto.  move => //=. 
Qed.


Lemma Forall_and : forall l0 l1, size l0 = size l1 ->
          Forall
          (fun p : fin * lType * (fin * lType) =>
           p.1.1 = p.2.1 /\ upaco2 (ApplyF full_eunf full_eunf \o EQ2_gen) bot2 p.1.2 p.2.2) 
          (zip l0 l1) -> map fst l0 = map fst l1.
Proof. 
elim. case. ssa. ssa. 
move => a l IH. case. ssa. ssa. inv H.  inv H0. ssa. pc. 
f_equal. done. apply/IH. inv H. done. 
Qed. 

Lemma bisim_complete_aux : forall e0 e1 l_v,  EQ2 e0 e1 ->  bisim  (e0,e1) l_v.  
Proof. 
intros. funelim (bisim  (e0,e1) l_v).  rewrite -Heqcall. ssa.
rewrite -Heqcall. ssa.
punfold H0. 
rewrite /outee /=.
inv H0. inv H1;ssa. apply/eqP. f_equal. f_equal. 
apply Forall_and in H5. f_equal.  done.  done.
rewrite foldInAllP. apply/allP=> x xIn. destruct x. apply/H.
3:con. apply/inP.  done.  


move : xIn.
rewrite /nextee /unfee //=. 
punfold H0. inv H0.  inv H1. ssa. ssa. 
move/eqP : xIn. case. intros. subst. pc.  eauto. 
ssa. 
clear H2 H3. 
elim : es0 es1 H4 s s0 xIn H5. case. ssa.  ssa. move => a l IH. case.  ssa.  ssa. 
inv H4. rewrite inE in xIn.  destruct (orP xIn). move/eqP : H2.  case. intros. subst. 
inv H5.  ssa. pc. done.  
apply/IH.  eauto.  done.  inv H5.  done.
Qed. 

Definition bisim' e0 e1 := bisim (e0,e1) nil. 

Lemma bisim'P : forall e0 e1,  bisim' e0 e1 <-> EQ2 e0 e1.  
Proof. 
intros. rewrite /bisim'. split. apply/bisim_sound. apply/bisim_complete_aux. 
Qed.
