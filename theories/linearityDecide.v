From mathcomp Require Import all_ssreflect zify.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From deriving Require Import deriving.
From Paco Require Import paco. 
Require Import MPSTSR.IndTypes.elimination. 
Require Import MPSTSR.linearity. 
Require Import MPSTSR.CoTypes.coGlobal.
Require Import MPSTSR.Process.env. 
From Equations Require Import Equations. 
(*Require Import Program. *)

Let inE := linearity.inE.

Definition Linear_aux(sg : gType) := 
forall a0 aa a1, 
Tr (a0::(aa++(cons a1 nil))) sg -> 
same_ch a0 a1 -> 
exists_dep InDep a0 aa a1 /\ exists_dep OutDep a0 aa a1.

Fixpoint one_unf g  :=
match g with 
| GRec g0 =>  g0[g GRec g0 .: GVar]
| GMsg a u g0 => GMsg a u (one_unf g0)
| GBranch a gs => GBranch a (map_values one_unf gs)
| _ => g
end.




Fixpoint traces (g : gType) := 
[::nil] ++ match g with 
| GMsg a u g0 => (map (fun l => a::l) (traces g0))
| GBranch a gs => (map (fun l => a::l) (flatten (map (snd >> traces) gs)))
| GRec g' => (traces g')
| _ => [::nil]
end.



Lemma traces_nil : forall g, nil \in traces g.
Proof. 
elim;intros;try done. 
Qed.

Hint Resolve traces_nil. 


Lemma Tr_subst : forall g s sigma, Tr s g -> Tr s g [g sigma ] .
Proof. move => g s sigma H.  elim : H sigma;intros. done.
simpl.  con. done. simpl.  simpl. move: (H1 sigma)=>Htr.
econ. apply/mapP. econ. eauto. econ. eauto.
simpl. econ. asimpl.
move: (H0 sigma). asimpl. eauto.
Qed.


Lemma Linear_subst : forall g sigma, Linear g [g sigma] -> Linear g. 
Proof. 
move => g sigma.  rewrite /Linear. intros. apply/H. apply/Tr_subst. eauto. done.
Qed. 

Lemma mem_traces : forall g s, s \in traces g -> Tr s g. 
Proof. elim;intros;ssa.
move : H. rewrite inE. move/orP. case. move/eqP=>->. done. 
rewrite inE. move/eqP=>->. done.
move : H. rewrite inE. move/orP. case. move/eqP=>->. done. 
rewrite inE. move/eqP=>->. done.
rewrite inE in H0. destruct (orP H0).
move/eqP : H1=>->. done.
con. 
apply/Tr_subst. auto. 
rewrite inE in H0. destruct (orP H0). 
move/eqP : H1=>->. done.
destruct (mapP H1). subst. con. auto.
rewrite inE in H0. destruct (orP H0). 
move/eqP : H1=>->. done.
destruct (mapP H1). subst. 
destruct (flattenP H2). ssa.
destruct (mapP H3). subst. de x1. econ. eauto.
asimpl in H4. ssa. eauto.
Qed. 


Lemma one_unf_msg : forall n a u g, iter n one_unf (GMsg a u g) =  (GMsg a u (iter n one_unf g)).
Proof. 
elim;ssa. 
rewrite H. simpl. done. 
Qed. 

Lemma one_unf_branch : forall n a gs, iter n one_unf (GBranch a gs) =  (GBranch a (map_values (iter n one_unf) gs)).
Proof. 
elim;ssa.
f_equal. elim : gs;try done. ssa. f_equal. de a0. done. 
rewrite H /=. f_equal. rewrite /map_values. rewrite -map_comp. apply/eq_in_map=> x xIn=>//=.
Qed. 

Lemma tr_in_Tr : forall g s, Tr s g -> exists n, s \in traces (iter n one_unf g).
Proof.
move => g s.  elim;ssa. 
exists 0. ssa. exists x.
rewrite one_unf_msg. simpl.  rewrite inE. apply/orP. right. 
apply/map_f. done.
exists x. 
rewrite one_unf_branch /=. rewrite inE. apply/orP. right.
apply/map_f. apply/flattenP. 
econ. 2:eauto.
apply/mapP.  econ. apply/map_f. eauto. ssa.
exists (x.+1). rewrite iterSr. simpl. done.
Qed. 


Lemma traces_ren : forall g s sigma, s \in traces g ⟨g sigma ⟩ -> s \in traces g. 
Proof. 
elim;ssa. 
rewrite inE in H0. destruct (orP H0). rewrite (eqP H1). done. eauto.
rewrite inE in H0. destruct (orP H0). rewrite (eqP H1). done.
destruct (mapP H1). subst. apply H in H2. 
rewrite inE. apply/orP. right. apply/map_f. done. 
rewrite inE in H0. destruct (orP H0). rewrite (eqP H1). done. 
rewrite inE. apply/orP. right. destruct (mapP H1). subst. 
apply/map_f.  apply/flattenP. destruct (flattenP H2). 
rewrite -map_comp in H3. destruct (mapP H3). subst. 
asimpl in H4. ssa. de x1.
econ. 2 : {  apply/H.  eauto. asimpl in H4.   ssa. eauto. } 
apply/mapP. exists (n,g). ssa. done. 
Qed. 

Lemma traces_subst : forall g sigma s, s \in traces g[g sigma] -> exists s0 s1, s = s0 ++ s1 /\ s0 \in traces g /\ (exists n, s1 \in traces (sigma n)).
Proof. 
elim;ssa. 
exists nil,s.  ssa. exists n. ssa. 
rewrite inE in H. destruct (orP H). rewrite (eqP H0).  exists nil,nil. ssa. exists 0. done.
rewrite inE in H0. rewrite (eqP H0). exists nil,nil. ssa. exists 0. done. 
rewrite inE in H0. destruct (orP H0). 
rewrite (eqP H1). exists nil,nil. ssa. exists 0. done. 
apply H in H1;try done. destruct H1,H1. ssa. 
move : H3. asimpl. destruct x1. simpl. 
intros.   have : x0 = nil. rewrite inE in H3. destruct (orP H3);try done. 
rewrite (eqP H4). done. rewrite inE in H4. rewrite (eqP H4). done. 
intros. subst. exists x,nil.  ssa. exists 0. done.
simpl. intros. apply traces_ren in H3. subst. 
exists x,x0. ssa. eauto.
rewrite inE in H0. destruct (orP H0). rewrite (eqP H1). 
exists nil,nil. ssa. exists 0. done. 
destruct (mapP H1). subst. apply H in H2. destruct H2,H2. ssa. 
subst. exists (a::x0),x1. ssa. apply/map_f. done. 
eauto.
rewrite inE in H0. destruct (orP H0). rewrite (eqP H1). 
exists nil,nil. ssa. exists 0. done. 
destruct (mapP H1). subst. rewrite -map_comp in H2. destruct (flattenP H2). 
destruct (mapP H3). subst. de x1.
asimpl in H4. ssa. eapply H in H4. 2 : eauto. ssa. subst. 
exists (a::x0),x1. ssa. apply/map_f. apply/flattenP. ssa. exists (traces s0). 
apply/mapP. exists (s,s0). ssa. done. done. eauto.
Qed. 

Lemma Tr2 : forall g s0 s1 a a', Tr s0 g -> Tr s1 g -> ohead s0 = Some a -> ohead s1 = Some a' -> a = a'.
Proof. 
intros. elim : H s1 a a' H0 H1 H2;ssa;subst. 
inv H2. inv H1. ssa. inv H3. 
ssa.  inv H3.  inv H2. ssa. inv H4. 
inv H1. apply/H0;eauto.
Qed. 

Lemma traces_one_unf1 : forall g a, [::a] \in traces (one_unf g) -> [::a] \in traces g. 
Proof. 
elim;ssa. apply traces_subst in H0. ssa. destruct x1. ssa. 
destruct (eqVneq x0 nil). subst. rewrite cats0 in H0. subst. done. 
rewrite inE in H2. rewrite (negbTE i) /= in H2.
destruct (eqVneq x nil). subst. ssa. subst.  done. destruct x. done. ssa. inv H0. 
destruct x. destruct x0;try done. done. ssa. 
destruct (eqVneq x0 nil). subst.  rewrite cats0 in H0. subst.  done. 
rewrite inE in H2. destruct (orP H2). move/eqP : H3. intros. subst.  done. 
rewrite inE in H3. move/eqP : H3.  intros. subst.  done. 
rewrite inE in H0. destruct (orP H0). move/eqP : H1. done. destruct (mapP H1).
inv H3. apply/map_f. done.   
rewrite inE in H0. destruct (orP H0). move/eqP : H1. done. destruct (mapP H1).
inv H3. apply/map_f. destruct (flattenP H2). destruct l.  ssa. ssa. 
rewrite mem_cat. apply/orP. left. asimpl. eauto. 
Qed.


Lemma traces_cat : forall g s0 s1, s0 ++ s1 \in traces g -> s0 \in traces g. 
Proof. 
elim;ssa.
destruct (eqVneq (s0++s1) nil). destruct s0. done. destruct s1;done. 
rewrite inE in H. destruct (orP H). move/eqP : H0. intros. rewrite -H0 eqxx in i.  done. 
rewrite inE in H. destruct (orP H). move/eqP : H0. intros. rewrite H1  in i. done. 
rewrite -(eqP H1) eqxx //= in i.  

destruct (eqVneq (s0++s1) nil). destruct s0. done. destruct s1;done. 
rewrite inE in H. destruct (orP H). move/eqP : H0. intros. rewrite -H0 eqxx in i.  done. 
rewrite inE in H. destruct (orP H). move/eqP : H0. intros. rewrite H1  in i. done. 
rewrite -(eqP H1) eqxx //= in i.  

rewrite inE in H0. destruct (orP H0). destruct s0;try done. 

apply H in H1. rewrite inE H1 orbC //=. 

destruct (eqVneq (s0++s1) nil). destruct s0. done. destruct s1;done. 
rewrite inE in H0. rewrite (negbTE i) /= in H0. destruct (mapP H0).
destruct s0.  done. inv H2. apply/map_f.  apply/H.  eauto. 

destruct (eqVneq (s0++s1) nil). destruct s0. done. destruct s1;done. 
rewrite inE in H0. rewrite (negbTE i) /= in H0. destruct (mapP H0).
destruct s0.  done. inv H2. apply/map_f.  
destruct (flattenP H1). destruct (mapP H3). subst.  de x0. eapply H in H5 as H5'.  2 :eauto. 
apply/flattenP.  econ. apply/map_f.  eauto. done. 
Qed. 


Lemma traces_one_unf : forall g a s b, a::s++[::b] \in traces (one_unf g) -> (exists m, a::(mask m s)++[::b] \in traces g /\ size m = size s) \/ a = b. 
Proof. 
elim;ssa. 
apply traces_subst in H0. ssa. destruct x1. ssa.
destruct (eqVneq x0 nil).
- subst. rewrite cats0 in H0. subst.
  left. exists (nseq (size s) true). rewrite mask_true //=. ssa. rewrite size_nseq //=. 
- destruct (eqVneq x nil).
 * subst.  left. exists (nseq (size s) true). rewrite mask_true //=. ssa. 
   subst. done. 
   rewrite size_nseq //=. 
 * rewrite inE in H2. rewrite (negbTE i) /= in H2.
   move : (@split_list _ x0). case. intros. subst. done. intros.  destruct b0. destruct H3. subst. 
   rewrite !catA in H0. rewrite -cat_cons in H0.
   apply last_eq in H0. ssa. subst. destruct x;try done. ssa. inv H0.
   destruct (eqVneq a0 x2).  right. done. left. 
   destruct x1. ssa. apply mem_traces in H1,H2. eapply Tr2 in H1. 2 : eapply H2. 2: done. 2 : done. subst. rewrite eqxx in i1. done. 
   ssa. have : x ++ a :: x1 = x ++ [:: a] ++ x1. done.  move => ->. 
   exists ((nseq (size (x ++ [::a])) false) ++ ((nseq (size x1)) true)). rewrite catA. 
    rewrite mask_cat. 2 : { rewrite size_nseq.  done. } 
    rewrite size_cat. rewrite nseqD.  
    rewrite mask_cat. rewrite mask_false mask_true //=. rewrite inE. 
    apply mem_traces in H2 as H2'. apply mem_traces in H1. eapply Tr2 in H2'. 2 : apply H1. all : try done. subst.    
    rewrite H2 orbC //=. ssa. rewrite !size_cat !size_nseq. done. rewrite size_nseq //=.
    ssa.
    destruct (eqVneq x0 nil). 
  ** subst. rewrite cats0 in H0. subst. left. exists (nseq (size s) true). rewrite mask_true //=.
     rewrite inE in H2. destruct (orP H2);try done. ssa. rewrite size_nseq //=. 
      ssa. rewrite size_nseq //=. 
     rewrite inE in H2. destruct (orP H2). move/eqP : H3. intros. subst. done. 
     rewrite inE in H3. move/eqP : H3. intros. subst. done. 
- rewrite inE in H0. destruct (orP H0). move/eqP : H1. done. destruct (mapP H1). inv H3. 
  destruct s. ssa. left. exists nil. ssa. apply/map_f. apply/traces_one_unf1. done. 
  ssa. apply H in H2. destruct H2. destruct H2. left. exists (true::x). ssa. apply/map_f. simpl. done.
  subst. left. exists (nseq (size (b::s)) false). rewrite mask_false. 
  ssa. apply/map_f. destruct (mapP H0). inv H4. 
  have : b :: s ++ [::b] = [::b] ++ (s ++ [::b]). done.  intros. rewrite x in H2. 
  apply traces_cat in H2. apply/traces_one_unf1. done. rewrite size_nseq //=. 
- rewrite inE in H0. destruct (orP H0). move/eqP : H1. done. destruct (mapP H1). inv H3. 
  destruct s. ssa. left. exists nil. ssa. apply/map_f. 
  destruct (flattenP H2).  destruct (mapP H4). subst. destruct (mapP H6). subst. apply/flattenP. econ. 
  apply/map_f. eauto. ssa. asimpl. apply/traces_one_unf1. done. 
  ssa. 
  destruct (flattenP H2).  destruct (mapP H4). subst. destruct (mapP H6). subst. left. de x.
  eapply H in H5. destruct H5. destruct H5.  exists (true::x). ssa. apply/map_f. simpl. 
  apply/flattenP. econ. apply/map_f.  eauto. done.  
  subst. exists (nseq (size (b::s)) false). rewrite mask_false. 
  ssa.
  destruct (mapP H0).  destruct (flattenP H5).  destruct (mapP H9). subst. inv H8. 
  apply/map_f. 
  have : b :: s ++ [::b] = [::b] ++ (s ++ [::b]). done.  intros. rewrite x in H10. 
  apply traces_cat in H10. apply/flattenP. destruct (mapP H11).  subst. econ. apply/map_f. eauto. asimpl. 
  apply/traces_one_unf1. done. rewrite size_nseq //=. eauto. 
Qed. 


Fixpoint sub_seq {A : Type} (l : seq A) : seq (seq A) :=
match l with 
| nil => [::nil]
| a::l' => (sub_seq l') ++ (compose ([::a]) (sub_seq l') cons)
end. 

Definition exists_indep a0 aa a1 := has indep (map (fun l' => a0::l'++[::a1]) (sub_seq aa)).

Lemma mem_sub_seq_nil : forall (A : eqType) (l : seq A), nil \in sub_seq l.
Proof. move => A. elim. done. intros. ssa. rewrite mem_cat H //=. 
Qed.

Lemma mem_sub_seq : forall (A : eqType) (l : seq A) (m : bitseq), (mask m l) \in sub_seq l.
Proof. 
move => A. elim. ssa. rewrite mask0. done. 
intros. simpl.  ssa. destruct m. ssa. rewrite mem_cat. rewrite mem_sub_seq_nil. done. 
ssa. case_if. rewrite mem_cat. apply/orP. right. rewrite mem_cat. apply/orP. left. apply/map_f. done. 
rewrite mem_cat. apply/orP. left. done. 
Qed. 

Lemma mem_sub_seq2 : forall (A : eqType) (l : seq A) x, x \in sub_seq l -> exists m, x = mask m l /\ size m = size l.
Proof. 
move => A. elim. ssa. rewrite inE in H.  exists nil. ssa. apply/eqP. done. 
intros. simpl.  ssa. rewrite mem_cat in H0. destruct (orP H0). 
apply H in H1. destruct H1. exists (false::x0). ssa. 
rewrite mem_cat in H1. destruct (orP H1). destruct (mapP H2). subst. 
apply H in H3. destruct H3. exists (true::x). ssa. f_equal. done. done. 
Qed. 


Lemma indep_existsP : forall a0 aa a1, exists_indep a0 aa a1 -> exists_dep InDep a0 aa a1.
Proof. 
intros. rewrite /exists_dep. move/hasP : H. case. intros. ssa. 
destruct (mapP p). subst. clear p.  apply mem_sub_seq2 in H. destruct H. destruct H. 
subst. exists x. apply InDep_iff in q. ssa. 
Qed.

Lemma indep_existsP2 : forall a0 aa a1, exists_dep InDep a0 aa a1 -> exists_indep a0 aa a1.
Proof. 
intros. apply/hasP. ssa. destruct H. ssa. 
exists (a0::mask x aa ++ [::a1]). apply/map_f. apply/mem_sub_seq.
apply/InDep_iff. done. 
Qed. 

Lemma indep_eq : forall a0 aa a1, exists_dep InDep a0 aa a1 <-> exists_indep a0 aa a1.
Proof. intros. split. apply/indep_existsP2. apply/indep_existsP. Qed.

Definition exists_outdep a0 aa a1 := has outdep (map (fun l' => a0::l'++[::a1]) (sub_seq aa)).


Lemma outdep_existsP : forall a0 aa a1, exists_outdep a0 aa a1 -> exists_dep OutDep a0 aa a1.
Proof. 
intros. rewrite /exists_dep. move/hasP : H. case. intros. ssa. 
destruct (mapP p). subst. clear p.  apply mem_sub_seq2 in H. destruct H. destruct H. 
subst. exists x. apply OutDep_iff in q. ssa. 
Qed.

Lemma outdep_existsP2 : forall a0 aa a1, exists_dep OutDep a0 aa a1 -> exists_outdep a0 aa a1.
Proof. 
intros. apply/hasP. ssa. destruct H. ssa. 
exists (a0::mask x aa ++ [::a1]). apply/map_f. apply/mem_sub_seq.
apply/OutDep_iff. done. 
Qed. 


Lemma outdep_eq : forall a0 aa a1, exists_dep OutDep a0 aa a1 <-> exists_outdep a0 aa a1.
Proof. intros. split. apply/outdep_existsP2. apply/outdep_existsP. Qed.

(*Definition ad := Action (Ptcp 0) (Ptcp 0) (Ch 0).*)
Definition indep_wrap s := 
match s with 
| a::b::s' => exists_indep a (belast b s' ) (last b s')
| _ => false
end. 

Definition outdep_wrap s :=
match s with 
| a::b::s' =>  exists_outdep a (belast b s') (last b s')
| _ => false
end.

Definition linear_aux g := all (fun s =>  implb (if s is a::a'::s' then same_ch a (last a' s') else false) (indep_wrap s && outdep_wrap s)) (traces g).


Lemma linear_complete : forall g, Linear_aux g -> linear_aux g. 
Proof. 
intros. rewrite /Linear_aux in H. rewrite /linear_aux.
apply/allP. move=> x xIn.  apply/implyP. intro. apply/andP. 
rewrite /indep_wrap /outdep_wrap. 
destruct x;try done. destruct x;try done. 
rewrite -indep_eq -outdep_eq. apply/H;try done.
apply/mem_traces. 
rewrite cats1.  rewrite -lastI. done. 
Qed. 

Lemma indep_wrapP : forall s, indep_wrap s <-> exists a s' b, s = a::s'++[::b] /\ exists_dep InDep a s' b. 
Proof. 
intros. split. 
rewrite /indep_wrap. 
destruct s;try done. 
destruct s;try done. intros. exists a, (belast a0 s), (last a0 s). ssa. f_equal.
rewrite cats1.
rewrite -lastI //=.
rewrite indep_eq //=.
case=> x. case=> x0. case. intros. ssa. subst. 
rewrite /indep_wrap. destruct x0. simpl. rewrite -indep_eq //=. 
simpl. rewrite -indep_eq. rewrite cats1.  rewrite last_rcons.
rewrite belast_rcons //=. 
Qed.

Lemma outdep_wrapP : forall s, outdep_wrap s <-> exists a s' b, s = a::s'++[::b] /\ exists_dep OutDep a s' b. 
Proof. 
intros. split. 
rewrite /outdep_wrap. 
destruct s;try done. 
destruct s;try done. intros. exists a, (belast a0 s), (last a0 s). ssa. f_equal.
rewrite cats1.
rewrite -lastI //=.
rewrite outdep_eq //=.
case=> x. case=> x0. case. intros. ssa. subst. 
rewrite /outdep_wrap. destruct x0. simpl. rewrite -outdep_eq //=. 
simpl. rewrite -outdep_eq. rewrite cats1.  rewrite last_rcons.
rewrite belast_rcons //=. 
Qed.











Lemma in_traces : forall g s, s \in traces g -> Tr s g. 
Proof. 
elim;intros. ssa.
rewrite inE in H. move/orP : H. case. move/eqP=>->//=. 
rewrite inE. move/eqP=>->//=. ssa. 
move : H. rewrite inE. move/orP. case. move/eqP=>->//=. 
rewrite inE. move/eqP=>->//=.
ssa. move: H0. rewrite inE. move/orP. case. move/eqP=>->//=.
move/H. intros. con. apply/Tr_subst. done. 
ssa. rewrite inE in H0. destruct (orP H0). rewrite (eqP H1). done. 
destruct (mapP H1). subst. con. auto. 
ssa. rewrite inE in H0. destruct (orP H0). rewrite (eqP H1) //=.
destruct (mapP H1). subst. destruct (flattenP H2). 
destruct (mapP H3). subst. de x1. eapply H in H4. ssa. eauto. ssa. eauto.
Qed.

Lemma linear_aux_unf : forall g, linear_aux g -> linear_aux (unf g). 
Proof. 
case;try done. 
intros. move : H. rewrite /linear_aux. intros. apply/allP=> x xIn.
apply/implyP. intro. simpl in xIn. 
apply traces_subst in xIn. destruct  xIn,H1,H1,H2. 
destruct H3. 
destruct x2. simpl in H3.
rewrite inE in H3. destruct (orP H3). 
move/eqP : H4. intros. subst. rewrite cats0. simpl in H.  
move/allP : H. move/(_ _ H2). move => HH.
move/implyP : HH. rewrite cats0 in H0. move/(_ H0). done. 
clear H3. simpl in H. subst. remember H.   clear Heqi.
move/allP : i. move/(_ _ H4). move => Hmask0.
move/allP : H. move/(_ _ H2). move => Hmask2. 
have : exists a s b, x0 ++ x1 = a::s++[::b] /\ same_ch a b.
destruct (x0++x1)eqn:Heqn;try done. destruct l eqn:Heqn2;try done. 
subst. exists s,(belast s0 l0),(last s0 l0). ssa. rewrite cats1.
rewrite -lastI //=.
intros.
destruct x, H,H. destruct H. rewrite H in H0. clear H0. 
destruct x0. destruct x1. ssa. simpl in *.  
apply (implyP Hmask0). destruct x1. ssa. inv H. destruct x2;done. inv H.
rewrite cats1 in H5. rewrite lastI in H5.
apply rcons_inj in H5. inv H5. 
destruct x1. simpl in *. rewrite cats0. apply (implyP Hmask2).
inv H. destruct x0;try done. ssa. destruct x2;done. 
ssa. rewrite cats0 in H5. rewrite lastI cats1 in H5. apply rcons_inj in H5. inv H5. 
simpl in *. inv H. clear H.
apply in_traces in H2 as H2'.
apply in_traces in H4 as H4'.
eapply Tr2 in H2'. 2 : eauto.  2:ssa. 2:ssa.  subst. 
destruct x0. simpl in *.  destruct x1. simpl in *.   
apply/andP. rewrite -indep_eq -outdep_eq. ssa. rewrite /exists_dep. exists nil. ssa. 
con. rewrite /II eqxx //=.
rewrite /exists_dep. exists nil. ssa. con. rewrite /IO_OO. apply/orP. right. rewrite /OO. 
rewrite /same_ch eqxx //=. 
have : last a x1 = x3.
rewrite cats1 in H5. rewrite lastI /= in H5. destruct x1. ssa. 
destruct x2;try done. rewrite lastI in H5.  
apply rcons_inj in H5. inv H5. 
ssa. rewrite lastI in H5. apply rcons_inj in H5. inv H5. rewrite last_rcons. done. 
intros. subst. move/implyP : Hmask0. move/(_ H1). simpl.
ssa. rewrite -indep_eq. rewrite -indep_eq in H.  destruct H. ssa. 
rewrite /exists_dep. exists (false::x0). ssa. 
rewrite -outdep_eq. rewrite -outdep_eq in H0.  destruct H0. ssa. 
rewrite /exists_dep. exists (false::x0). ssa. 
simpl in *. destruct x1;try done. simpl in *.
have : x = x3. destruct x2;try done.  ssa. inv H5. destruct x0;done. 
ssa. rewrite !cats1 in H5. inv H5. apply rcons_inj in H3. inv H3. 
intros. subst. rewrite cats1 last_rcons. rewrite belast_rcons.
apply/andP. rewrite -indep_eq -outdep_eq. ssa. 
rewrite /exists_dep. exists (nseq (size (a::x0)) false). 
rewrite /exists_dep. rewrite !mask_false size_nseq. ssa. 
con. rewrite /II eqxx //=. 
exists (nseq (size (a::x0)) false). rewrite size_nseq mask_false. ssa. 
con. apply/orP. right. rewrite /OO /same_ch eqxx //=.
have : x3 = last a0 x1.  
rewrite cats1 in H5. rewrite lastI in H5.
apply rcons_inj in H5. inv H5. rewrite !last_cat //=.
intros. subst. move/implyP : Hmask0. move/(_ H1). move => HH.
ssa. 

rewrite lastI /=. rewrite last_cat /=. 
rewrite last_rcons. rewrite -indep_eq in H.
rewrite belast_cat. simpl. rewrite belast_rcons. 
destruct H.  ssa. rewrite -cat_rcons.  
rewrite -lastI -indep_eq.
exists ((nseq ((size x0).+2) false)++x3). ssa. f_equal. 
rewrite !size_cat size_nseq /= H /=. 
lia.
have : (x0 ++ x :: belast a0 x1) = (x0 ++ [::x] ++ belast a0 x1).
done. move=>->.
have : false :: (nseq (size x0) false) = nseq (size (x0 ++ [::x])) false. 
rewrite size_cat /= addnC //=.
 rewrite -!cat_cons. move=>->.
rewrite catA.
rewrite mask_cat.   rewrite mask_false //=.
rewrite size_nseq //=.

rewrite lastI /=. rewrite last_cat /=. 
rewrite last_rcons. rewrite -outdep_eq in H0.
rewrite belast_cat. simpl. rewrite belast_rcons. 
destruct H0.  ssa. rewrite -cat_rcons.  
rewrite -lastI -outdep_eq.
exists ((nseq ((size x0).+2) false)++x3). ssa. f_equal. 
rewrite !size_cat size_nseq /= H0 /=. 
lia.
have : (x0 ++ x :: belast a0 x1) = (x0 ++ [::x] ++ belast a0 x1).
done. move=>->.
have : false :: (nseq (size x0) false) = nseq (size (x0 ++ [::x])) false. 
rewrite size_cat /= addnC //=.
 rewrite -!cat_cons. move=>->.
rewrite catA.
rewrite mask_cat.   rewrite mask_false //=.
rewrite size_nseq //=.

simpl in H3.
have : x1 = nil. rewrite inE in H3. destruct (orP H3). apply/eqP. done. 
rewrite inE in H4. apply/eqP. done. 
intros. subst. rewrite cats0. simpl in H. 
move/allP : H. move/(_ _ H2). move => HH. apply (implyP HH).
rewrite cats0 in H0. done. 
Qed.

Fixpoint mask_mask (m0 m1 : seq bool) := 
match m0,m1 with 
| nil,_ => nil 
| _,nil=> nseq (size m0) false (*Need size to remain m0*)
| false::m0',_ => false::(mask_mask m0' m1)
| true::m0',b1::m1' => b1::(mask_mask m0' m1')
end. 



Lemma mask_maskP : forall (A : eqType) (l : seq A) m0 m1, mask (mask_mask m0 m1) l = mask m1 (mask m0 l). 
Proof. 
move => A. elim;ssa. 
rewrite !mask0 //=. 
destruct m0. ssa. rewrite mask0 //=. 
simpl. case_if. destruct m1. ssa. 
ssa. rewrite mask_false //=. ssa. case_if. f_equal. done. done.
destruct m1.  ssa. rewrite mask_false mask0s //=. ssa. 
Qed. 

Lemma mask_mask_size : forall m0 m1, size (mask_mask m0 m1) = size m0.
Proof. 
elim;ssa. case_if. destruct m1;try done. ssa. f_equal. rewrite size_nseq //=. 
ssa. destruct m1;try done. ssa. rewrite size_nseq //=. ssa. 
Qed. 


Lemma linear_aux_one_unf : forall g, linear_aux g -> linear_aux (one_unf g). 
Proof.  move => g. rewrite /linear_aux. intros. apply/allP. intro. intros. 
destruct x. done. destruct (@split_list _  x). subst. done. 
destruct H1,H1. subst. apply traces_one_unf in H0. destruct H0. 
destruct H0. move/allP : H. destruct H0.  move/(_ _ H). move => HH.  
apply/implyP. intros. 
have : match mask x x0 ++ [:: x1] with
       | [::] => false
       | a' :: s' => same_ch s (last a' s')
       end. clear HH H0. clear H. elim : x0 x x1 H1. ssa. rewrite mask0.  ssa. 
ssa. destruct x. ssa. rewrite last_cat in H1. ssa. 
ssa. case_if. ssa. move : H1.  rewrite !last_cat. ssa. 
apply/X. destruct l. ssa. ssa. move/implyP : HH. intros. 
have : indep_wrap (s :: mask x x0 ++ [:: x1]) && outdep_wrap (s :: mask x x0 ++ [:: x1]). 
apply/HH. destruct (mask x x0);try done.
intros. clear H HH (*x2*). destruct (andP x3).   apply/andP. clear x3 x2 H1. 
move : H H2. (*clear x3.*)
rewrite !indep_wrapP !outdep_wrapP. ssa. 
ssa. destruct H3. ssa. 
exists s,x0,x1. ssa. rewrite /exists_dep. 
inv H. apply last_eq in H8. ssa. subst. 
rewrite -mask_maskP in H4. exists (mask_mask x x8). ssa. 
(*subst. rewrite size_mask //= in H4. *)
rewrite mask_mask_size //=.
ssa.
exists s,x0,x1. ssa. rewrite /exists_dep. 
destruct H2.  ssa. inv H.
apply last_eq in H8. ssa. subst. 
inv H1.
apply last_eq in H8. ssa. subst.

(*destruct (mask x x0) eqn:Heqn;ssa.
Search _ exists_outdep.
apply outdep_existsP in H5. inv H5. ssa. de x1. 
econ. con.*)

exists (mask_mask x x8). rewrite mask_maskP.  ssa. 
rewrite mask_mask_size //=. 

subst. apply/implyP. intros. apply/andP.  
rewrite indep_wrapP outdep_wrapP. ssa. 
exists x1,x0,x1. ssa. exists (nseq (size x0) false). rewrite size_nseq //=. ssa. 
rewrite mask_false //=. con. rewrite /II  eqxx //=. 
exists x1,x0,x1. ssa. exists (nseq (size x0) false).
rewrite size_nseq //=. ssa. 
rewrite mask_false //=. con. apply/orP.  right. rewrite /OO  /same_ch  eqxx //=. 
Qed.

Lemma linear_aux_one_unf_iter : forall n g, linear_aux g -> linear_aux (iter n one_unf g). 
Proof. 
elim;ssa. apply/linear_aux_one_unf. auto. 
Qed. 


Lemma linear_aux_sound : forall g, linear_aux g -> Linear_aux g. 
Proof. 
intros. rewrite /Linear_aux. intros. 
apply tr_in_Tr in H0. destruct H0. 
eapply linear_aux_one_unf_iter in H.
move/allP : H.  move/(_ _ H0). move => HH.  
have :  indep_wrap (a0 :: aa ++ [:: a1]) && outdep_wrap (a0 :: aa ++ [:: a1]). 
apply (implyP HH).
destruct aa; ssa. rewrite last_cat //=. 

move/andP. rewrite indep_wrapP outdep_wrapP.
ssa. ssa. inv H. apply last_eq in H7. ssa. subst. 
destruct H4. ssa. exists x6. ssa. 

inv H2. apply last_eq in H7. ssa. subst. 
destruct H3. ssa. exists x6. ssa. 
Qed. 

Lemma Linear_aux_dec : forall g, Linear_aux g <-> linear_aux g.
Proof. intros. split. apply/linear_complete. apply/linear_aux_sound. Qed. 





Lemma guarded_fv : forall g v, v \notin gType_fv g -> guarded v g.
Proof.
elim;rewrite /=;try done;intros.
rewrite !inE in H. lia.
apply H. move : H0. move/mapP.  move=> HH'. apply/negP. intro. apply/HH'. 
exists v.+1;try done.  
rewrite mem_filter. ssa. 
Qed.

Lemma inotin : forall g i sigma, (forall n, i !=  sigma n) -> i \notin gType_fv g ⟨g sigma ⟩.
Proof.
elim;rewrite /=;try done;intros. rewrite !inE. specialize H with n. lia.
apply/mapP. intro. destruct H1.  subst. rewrite mem_filter in H1. ssa. apply/negP. apply/H. 2 : eauto.  
asimpl. case;try done. simpl. move=> n. asimpl. destruct x;try done. ssa. suff : x != sigma n. lia. done. 
apply/flattenP=>HH. destruct HH. rewrite /= -map_comp in H1. 
destruct (mapP H1). subst. de x0. apply/negP. apply/H. eauto. eauto. done. 
Qed.


Lemma guarded_ren : forall g sigma i , (forall n, sigma n != i) -> guarded i g -> guarded i g ⟨g sigma⟩.
Proof.
elim;rewrite /=;simpl;intros;try done.
asimpl. apply : H. intros. destruct n.  done. simpl. specialize H0 with n. rewrite /funcomp. lia.
done. 
Qed.

Lemma guarded_shift1 : forall g i sigma, injective sigma ->  guarded i g -> guarded (sigma i) g ⟨g sigma⟩.
Proof.
elim;rewrite /=;simpl;intros;try done.
apply/eqP. move=> HH. apply H in HH. lia. 
asimpl. 
have : (sigma i).+1 = ((0 .: sigma >> succn) i.+1).
destruct i.  simpl. rewrite /funcomp. done. simpl. rewrite /funcomp. done.
move=>->. apply H. intro. intros. destruct x1;destruct x2;try done. inversion H2. f_equal.  apply/H0. done. 
done. 
Qed.



Lemma guarded_shift2 : forall g i sigma, injective sigma ->  guarded (sigma i) g ⟨g sigma⟩ ->  guarded i g.
Proof.
elim;rewrite /=;simpl;intros;try done.
apply/eqP. move=> HH. apply (negP H0). apply/eqP. f_equal. done. 
apply :H.  2 : { apply : H1.  } 
asimpl. auto. 
Qed.


Lemma guarded_shift : forall g sigma i , injective sigma  -> guarded i g <-> guarded (sigma i) g ⟨g sigma⟩.

intros. split;intros; eauto using guarded_shift1, guarded_shift2.
Qed.


Lemma gcontractive_ren : forall g sigma, injective sigma -> (forall n, n <= sigma n) ->  gcontractive  g -> gcontractive g ⟨g sigma ⟩.
Proof.
elim;intros;simpl;try done. 
asimpl. split_and. have : 0 = ( 0 .: sigma >> succn) 0. done. intros. rewrite {1}x.

rewrite -guarded_shift. simpl in H2. split_and. auto.
apply H. auto.  case. done. done.  simpl in H2. split_and. apply H.  done. done. done.
rewrite all_map. apply/allP. intro. intros. simpl. de x. eapply H. eauto. done.  done. apply (allP H2) in H3. done.
Qed.



Lemma guarded_sig2_ren : forall g sigma sigma' i, guarded i g ⟨g sigma⟩ -> (forall n, (sigma n) != i ->  (sigma' n) != i) -> guarded i g ⟨g sigma'⟩.
Proof.
elim;rewrite /=;intros;try done.
apply H0. done.
asimpl. apply : H. eauto. move => n.  asimpl. simpl. intros. destruct n. done. simpl in *. 
move : H. rewrite /funcomp. intros. suff :  sigma' n != i.  lia. apply : H1. lia. 
Qed.

Lemma guarded_sig2 : forall g sigma sigma' i, guarded i g [g sigma] -> (forall n, guarded i (sigma n) -> guarded i (sigma' n)) -> guarded i g [g sigma'].
Proof.
elim;rewrite /=;intros;try done.
apply H0. done.
asimpl. apply : H. eauto. move => n.  asimpl. simpl. intros. destruct n. done. simpl in *.
move : H. rewrite /funcomp. specialize H1 with n. move : H0. asimpl.
intros. rewrite -guarded_shift. move : H. rewrite -guarded_shift.  move/H1. done. 
done. done. 
Qed.


Lemma gcontractive_subst : forall g sigma,gcontractive g -> (forall n, gcontractive (sigma n)) -> gcontractive g [g sigma].
Proof. 
elim;rewrite /=;intros;try done. 
asimpl. split_and. 
apply/guarded_sig2.
instantiate (1 := (GVar 0 .: GVar >>  ⟨g ↑ ⟩)).  asimpl. done.
case. done. simpl. intros. apply/guarded_fv. asimpl. apply/inotin. done.
apply H. done.  intros. destruct n.  done. simpl. asimpl.  apply/gcontractive_ren. done. done. done.
apply H. done.  intros. done. 
rewrite all_map. apply/allP. intro. intros. simpl. de x. eapply H. eauto. apply (allP H0) in H2. done. done.
Qed.






Lemma mu_height_subst_contractive : forall g0 sigma, (forall n, 0 < mu_height (sigma n) -> guarded n g0) -> gcontractive g0 -> mu_height (g0[g sigma]) = mu_height g0.
Proof. 
elim; try solve [by rewrite /=];intros.
asimpl. move : (H n). destruct (mu_height (sigma n)) eqn:Heqn. done. have : 0 < n0.+1 by lia. move => + HH. move/HH=>//=. lia. 
simpl. f_equal. asimpl. apply H. case. rewrite //=. move=> n/=. move => HH. apply/H0. move : HH. asimpl. rewrite mu_height_ren //=. ssa. 
Qed.


Lemma contractive_unf : forall g , gcontractive g -> gcontractive (unf g). 
Proof.
intros. rewrite /unf. destruct g;try done. apply/gcontractive_subst. ssa. case;done. 
Qed.

Lemma mu_height_unf_contractive : forall g , gcontractive g -> (mu_height g).-1 = mu_height (unf g).
Proof.
move => g. rewrite /=. case : g; try solve [intros;rewrite /=;done].
intros. rewrite /=. ssa. erewrite mu_height_subst_contractive. done. eauto. case. done. done. done. 
Qed.

Lemma contractive_iter_unf : forall k g , gcontractive g -> gcontractive (iter k unf g). 
Proof.
elim;try done. intros. simpl. apply/contractive_unf. ssa. 
Qed.

Lemma contractive_full_unf : forall g , gcontractive g -> gcontractive (full_unf g). 
Proof.
intros. rewrite /full_unf. apply/contractive_iter_unf. done. 
Qed.

(*Lemma mu_height_unf_contractive : forall g , gcontractive g -> (mu_height g).-1 = mu_height (unf g).
Proof.*)

Lemma mu_height_iter_unf : forall k g , gcontractive g -> (mu_height g) - k = (mu_height (iter k (fun g => unf g) g)). 
Proof.
elim;intros. rewrite /=. lia.
rewrite /=. have : mu_height g - n.+1 = (mu_height g - n).-1 by lia. move=>->. 
erewrite H. rewrite mu_height_unf_contractive //=. apply/contractive_iter_unf.  done. done. 
Qed.

Lemma iter_unf_not_rec : forall g k, gcontractive g -> mu_height g <= k -> forall g', iter k unf g <> GRec g'.
Proof.
intros. simpl in *. apply (mu_height_iter_unf k) in H. move : H. 
have : mu_height g - k  = 0 by lia. move=>->. intros. destruct (iter k unf g);try done.
Qed.


Lemma full_unf_not_rec : forall g, gcontractive g -> forall g', full_unf g <> GRec g'.
Proof.
intros. apply/iter_unf_not_rec. done. done. 
Qed.









Definition linearP g (bs : seq bool) := (linear_aux g)  && all id bs. 

Definition linear g := sat1 nil linearP (fun _ => true) g. 


Variant LinearF  (R : gType -> Prop) : gType -> Prop :=
 | LF0 g : (forall g', g' \in nextg (full_unf g) -> R g') -> Linear_aux g -> LinearF R g.

Definition LinearCo := paco1 LinearF bot1. 

Lemma LinearF_mon : monotone1 LinearF.
Proof. 
intro. intros. inv IN;try con. auto. done.
Qed. 
Hint Resolve LinearF_mon : paco.

Lemma Tr_unf2 : forall s g, Tr s (unf g) -> Tr s g. 
Proof. 
intros. destruct g;try done. ssa. 
Qed.

Lemma Tr_full_unf2 : forall s g, Tr s (full_unf g) -> Tr s g. 
Proof. 
intros. rewrite /full_unf in H. remember (mu_height g). clear Heqn. elim : n g s H. done. 
intros. ssa. apply/Tr_unf2. apply/H.  rewrite -iterSr iterS. done. 
Qed.

Lemma Tr_unf2' : forall s g, Tr s g -> Tr s (unf g). 
Proof. 
intros. destruct g;try done. ssa. inv H.
Qed.

Lemma Tr_full_unf2' : forall s g, Tr s g -> Tr s (full_unf g). 
Proof. 
intros. rewrite /full_unf. remember (mu_height g). clear Heqn. elim : n g s H. done. 
intros. ssa. apply/Tr_unf2'. apply/H.  done. 
Qed.



Lemma Linear_12 : forall g, Linear g -> LinearCo g.
Proof. 
pcofix CIH. intros. pfold. con. 
intros. right. apply/CIH. rewrite /Linear. intros. 
destruct (full_unf g) eqn:Henq;try done.
simpl in H. rewrite inE in H. move/eqP : H. intros. subst.
apply/H0;try done. apply/Tr_full_unf2. rewrite Henq. 
instantiate (1 := a :: aa_p). con. done.  
simpl in H. 
apply/H0;try done. apply/Tr_full_unf2. rewrite Henq. 
instantiate (1 := a :: aa_p). simpl.
move/nthP : H. move/(_ GEnd). case. intros. subst. 
have : nth (0,GEnd) l x \in l. apply/mem_nth. rewrite size_map in p. done.
intro. destruct ( nth (0, GEnd) l x) eqn:Heqn.
 econstructor. 2:eauto. 
erewrite nth_map.  erewrite Heqn. instantiate (1 := n). ssa.

rewrite size_map in p. done.
rewrite /Linear_aux. intros. apply/H0. instantiate (1 := nil). done. done. 
Unshelve.

Qed. 

(*We need gtocoind because exist statement for coinductive type doesn't give us coinduction hypothesis*)
Lemma linear_sound : forall e l   (R : gType ->  Prop) , sat1  l linearP (fun _ => true) e ->  (forall x, x \in l -> R x) ->
upaco1 LinearF R e. 
Proof.
intros. 
funelim (sat1  l linearP (fun _ => true) e). 
right. apply/H0. done. 
rewrite -Heqcall in H0.
left. pcofix CIH.
pfold. constructor. 
intros. apply/H. apply/inP=>//=.
rewrite /linearP in H0. ssa. rewrite foldInMapP in H4. apply (allP H4). apply/map_f. done. 
auto. intros. rewrite inE in H3. destruct (orP H3) . rewrite (eqP H4). done. auto. 
apply/Linear_aux_dec. rewrite /linearP in H0.  ssa. 
Qed.

Lemma sat1_complete_aux: forall e l, LinearCo e -> sat1 l linearP (fun _ => true) e.  
Proof. 
intros. funelim (sat1 l  linearP (fun _ => true) e). 
done. 
rewrite -Heqcall foldInMapP. ssa. 
punfold H0. inv H0.
rewrite /linearP. ssa. apply/Linear_aux_dec=>//=. 
apply/allP. move => x. intros. destruct (mapP H3). subst. 
rewrite /id. apply/H. apply/inP=>//=. apply H1 in H4. 
pclearbot. done. 
Qed. 

(*Theorem 11*)
Lemma Linear_decidable : forall g, gclosed g -> gcontractive g  -> Linear g <-> linear g.
Proof. 
move=> g HClosed Hcont.
intros. split.
move/Linear_12/sat1_complete_aux. eauto.
move/linear_sound. 
move=>HH. 
have : LinearCo g.
suff : upaco1 LinearF bot1 g. case. done. done.
apply HH. done.
clear HH. intros.
intro.
have : gInvPred g. apply unravelling_of_trans. done. done. move=>Hinv.
clear HClosed Hcont.
elim: aa_p g x Hinv. ssa. punfold x. inv x. apply H2. done. done.
punfold x. inv x. apply H2. done. done.
intros.

simpl in H0.
apply Tr_full_unf2' in H0.
punfold Hinv. inv Hinv. inv H2. 
destruct H4. 
rewrite -H3 in H0. inversion H0. subst.
eapply H. 3:eauto. 2:done. 
punfold x. inv x. rewrite -H3 in H5. ssa.
move: (H5 e0). rewrite inE eqxx. move/(_ is_true_true).
case;ssa. done.
done.

rewrite -H3 in H0. inv H0.
eapply H. 3:eauto. 
move/ForallP : H4. move/inP : H8. move=>HH.
move/(_ _ HH). case;ssa.
punfold x. inv x. rewrite -H3 in H4. ssa.
move: (H4 g0).
have: g0 \in [seq i.2 | i <- es]. apply/mapP. econ. apply/inP. eauto. done.
move=>HH2. move/(_ HH2). case;ssa. 
rewrite -H3 in H2. 
move/ForallP : H4. move=>HH. move/inP : H8. move/HH.
case;ssa. done.
rewrite -H4 in H0. inv H0.
Qed.

