Require Export MPSTSR.IndTypes.unscoped. 
From mathcomp Require Import all_ssreflect zify.
From deriving Require Import deriving.
Require Export MPSTSR.utils.
Require Import MPSTSR.Process.preds.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.





Section EnvBase. 
Implicit Type A B C : eqType.
Definition lookup A B (l : seq (A * B)) (k : A) := omap snd (ohead (filter (fun x => x.1 == k) l)).


Definition update A B (l : seq (A * B)) k b := map (fun x => if x.1 == k then (x.1,b) else x) l. 
Definition filter_keys A B (p : pred A) (l : seq (A * B))  :=  filter (p \o fst) l.
Definition remove A B (l : seq (A * B)) (k : A) :=  filter_keys (fun x => x != k) l. 
Definition partition A B (l : seq (A * B)) (p : pred A) := (filter_keys p l,filter_keys (predC p) l). 
Definition insert A B (l : seq (A * B) ) l' :=  l'++l.
Definition injective_at A B (l : seq A) (f : A -> B) := forall  a a', a \in l -> a' \in l -> f a = f a' -> a = a'.
Definition dom A B  (l : seq (A * B) ) := map fst l. 
Definition values A B (l : seq (A * B)) := map snd l. 
Definition subset (A : eqType) (l0 l1 : seq A) := forall x, x \in l0 -> x \in l1. 
Definition map_keys A B C (f : A -> B)  (l : seq (A * C))  : seq (B * C):= map (fun kv => (f kv.1,kv.2)) l.
Definition map_values A B C (f : B -> C)  (l : seq (A * B))  : seq (A * C):= map (fun kv => (kv.1,f kv.2)) l.
Definition insert_shift A B C (f : A -> A) (f_init : B -> (A * C)) (l : seq (A * C)) (bb : seq B) :=
insert (map_keys f l) (map f_init bb).

End EnvBase.

Section EnvTheory.
Implicit Type A B C : eqType.

Lemma lookup_cons_eq : forall A B (l : seq (A * B)) a k, a.1 = k -> lookup (a :: l) k = Some a.2.
Proof. intros. rewrite /lookup.  ssa. rifliad. Qed. 

Lemma lookup_cons_neq : forall A B (l : seq (A * B)) a k, a.1 != k -> lookup (a :: l) k = lookup l k. 
Proof. intros. rewrite /lookup.  ssa. rifliad. Qed.

Lemma lookup_or : forall A B (l : seq (A * B)) a k T, lookup (a::l) k = Some T ->  a.1 = k /\ T = a.2 \/  a.1 != k /\ lookup l k = Some T.  
Proof. intros. de (eqVneq a.1 k). left.  ssa. rewrite lookup_cons_eq in H. inv H. done.
right. ssa. rewrite lookup_cons_neq in H. done. done.
Qed. 


Lemma lookup_dom : forall A B (l : seq (A * B)) k T, lookup l k = Some T -> k \in dom l. 
Proof. 
move => A B. elim;ssa. de (eqVneq a.1 k). rewrite lookup_cons_eq //= in H0. inv H0. left. apply/eqP. done. 
rewrite lookup_cons_neq in H0. eauto. done.  
Qed. 


Lemma in_pair : forall  (A B : eqType) (E : seq (A * B)) lk T,  lookup E lk = Some T -> (lk,T) \in E.  
Proof. move => A B.  elim;ssa. 
apply lookup_or in H0. destruct H0. ssa. subst. de a;ssa.
ssa. 
Qed. 

Lemma in_dom : forall  (A B : eqType) (E : seq (A * B)) lk T,  lookup E lk = Some T ->  lk \in dom (E).
Proof. 
intros.  move/in_pair : H=>HH. apply/mapP. eauto. 
Qed. 

Lemma filter_keys_eq : forall (A B : eqType) (l : seq (A * B)) (p p' : pred A), (forall x, x \in dom l -> p x = p' x) ->  filter_keys p l = filter_keys p' l. 
Proof. 
intros. rewrite /filter_keys. apply/eq_in_filter. intro. ssa. apply/H. apply/map_f. done. 
Qed. 

Lemma map_keys_eq : forall (A B : eqType) (l : seq (A * B)) (f f' : A -> A), (forall x, x \in dom l -> f x = f' x) ->  map_keys f l = map_keys f' l. 
Proof. 
intros. rewrite /map_keys. apply/eq_in_map. intro. ssa. rewrite H //=. apply/map_f. done. 
Qed. 

Lemma map_keys_id : forall (A B : eqType) (l : seq (A * B)) , map_keys id l = l. 
Proof. 
intros. rewrite /map_keys. rewrite -{2}(@map_id _ l) . 
apply/eq_in_map. intro. ssa. de x. 
Qed. 

Lemma injective_atP : forall ( A B : eqType) (f : A -> B) (l : seq A), injective f -> injective_at l f.
Proof. intros. intro.  intros. apply/H.   eauto. 
Qed. 


Lemma injective_at_cons : forall A B (l : seq A) a (f : A -> B), injective_at (a :: l) f -> injective_at l f.
Proof. intros. move : H. rewrite /injective_at. ssa. 
Qed. 

Lemma eq_false : forall (A : eqType) (a : A), ~ ((a == a) = false).
Proof. ssa. intro. rewrite eqxx in H. done. 
Qed. 

Hint Resolve eq_false.


Lemma lookup_map_aux : forall A B (l : seq (A * B)) (k : A) (f : A -> A), injective_at (dom l) f -> k \in dom l ->
                                                                lookup l k = lookup (map_keys f l) (f k).
Proof. 
move => A B. intros. move : H. 
rewrite /lookup. elim : l H0;ssa. 
rifliad. rewrite inE in H0. destruct (orP H0);ssa. norm_eqs. 
norm_eqs. ssa. destruct (orP H0). ssa. move/eqP : H4.  intros. subst. norm_eqs. 
move/eqP :H3. intro. apply H1 in H3;ssa.  subst. auto. apply eq_false in H2.  done.
destruct (orP H0). norm_eqs.
apply/H. done. apply/injective_at_cons. eauto.
Qed.

Lemma lookup_map_aux2 : forall A B (l : seq (A * B)) (k : A) (f : A -> A), injective f -> 
                                                                lookup l k = lookup (map_keys f l) (f k).
Proof. 
move => A B. intros. move : H. 
rewrite /lookup. elim : l;ssa. 
rifliad. norm_eqs. norm_eqs. apply H0 in H2. subst. rewrite eqxx in H1. done. 
eauto. 
Qed.


Lemma lookup_map_eq : forall A B (l : seq (A * B)) (k : A) k' (f : A -> A), injective_at (dom l) f -> k \in dom l -> f k = k' ->
                                                             lookup (map_keys f l) k' =    lookup l k.
Proof. 
intros. subst. rewrite -lookup_map_aux //=. 
Qed. 

Lemma lookup_map_eq_inj : forall A B (l : seq (A * B)) (k : A) k' (f : A -> A), injective f -> f k = k' ->
                                                             lookup (map_keys f l) k' =    lookup l k.
Proof. 
intros. subst. rewrite -lookup_map_aux2 //=. 
Qed. 


Lemma lookup_map : forall A B (l : seq (A * B)) (k : A) k' (f : A -> A) T, injective_at (dom l) f -> k \in dom l -> f k = k' ->
                                                             lookup (map_keys f l) k' = Some T <->    lookup l k = Some T.
Proof. 
intros. subst. erewrite lookup_map_eq. reflexivity.  done. eauto. done. 
Qed. 

Hint Resolve lookup_cons_eq lookup_cons_neq.

Lemma lookup_filter : forall A B (l : seq (A * B)) T (k : A) (p : pred A), p k ->
lookup l k = Some T -> lookup (filter_keys p l) k = Some T.
Proof. move => A B. elim;ssa.  apply lookup_or in H1. destruct H1.  ssa. subst. 
ssa. rifliad. apply/lookup_cons_eq. done.
ssa. subst. rifliad. rewrite lookup_cons_neq //=. eauto. eauto.
Qed. 

Lemma lookup_filter2 : forall A B (l : seq (A * B)) T (k : A) (p : pred A), 
lookup (filter_keys p l) k = Some T -> p k /\ lookup l k = Some T.
Proof.
move => A B. elim;ssa. move : H0. rifliad. move/lookup_or. case. ssa. subst. auto. 
ssa. apply H in H2. ssa.  move/H. ssa.
move : H0. rifliad.
destruct (eqVneq a.1 k). subst. 
rewrite !lookup_cons_eq;ssa. 
rewrite !lookup_cons_neq;ssa.  apply H in H1. ssa. 
intros. de (eqVneq a.1 k). subst. 
apply H in H1.  ssa. rewrite H0 in H1. done. 
rewrite lookup_cons_neq;ssa.  apply H in H1. ssa.
Qed. 


Hint Resolve map_f.
Lemma update_map_keys : forall (A B : eqType) (l : seq (A * B)) (k : A) k' (f : A -> A) T, injective_at (dom l) f -> k \in dom l ->  f k = k' ->
                                                             update (map_keys f l) k' T =    map_keys f (update l k T).
Proof. 
intros. subst.
rewrite /update /map_keys -!map_comp. apply/eq_in_map.  intro. ssa. 
have : (f x.1 == f k) = (x.1 == k). apply/eq_iff. split. 
intros. apply/eqP. apply/H. apply/map_f. done. done. apply/eqP. done. 
move/eqP. intros. subst. rewrite eqxx //=.
move=>->. rifliad.
Qed. 

Lemma update_filter_keys : forall (A B : eqType) (l : seq (A * B)) (k : A) (p : pred A) T, 
                                                             update (filter_keys p l) k T =  filter_keys p (update l k T).
Proof. 
intros. 
rewrite /update /filter_keys. rewrite filter_map. f_equal. apply/eq_in_filter. 
intro. ssa. rifliad. 
Qed. 


Lemma filter_keys_map_keys : forall (A B : eqType) (l : seq (A * B)) (f : A -> A) (p : pred A),  filter_keys p (map_keys f l) = map_keys f (filter_keys (preim f p) l).
Proof. 
intros. rewrite /map_keys /filter_keys filter_map //=.  
Qed. 







Lemma dom_cat : forall (A B : eqType) (l0 l1 : seq (A * B)), dom (l0 ++ l1) = dom l0 ++ dom l1.
Proof. 
intros. rewrite /dom map_cat //=. 
Qed. 

Lemma dom_insert_shift : forall (A B C : eqType) (l : seq (A * C)) (f : A -> A) (f_init : B -> (A * C)) (bs : seq B), 
                             dom (insert_shift f f_init l bs) =  (dom (map f_init bs)) ++ (dom (map_keys f l)).
Proof. intros. rewrite /insert_shift /insert dom_cat //=. 
Qed. 




Lemma mapPzip : forall (A B C : eqType) (l : seq A) (l' : seq B) a b (f : A -> C), (a,b) \in zip (map f l) l' -> exists a', (a',b) \in zip l l' /\ f a' = a.
Proof. 
move => A B C. elim. case;ssa. 
ssa. destruct l';ssa. rewrite inE in H0. destruct (orP H0).
move/eqP :H1. case. intros. subst.  exists a. done.
apply H in H1. destruct H1. exists x. rewrite inE. ssa. 
Qed.

Lemma mapPzip2 : forall (A B C : eqType) (l : seq A) (l' : seq B) a b (f : A -> C), (a,b) \in zip l l' ->  (f a,b) \in zip (map f l) l'.
Proof. 
move => A B C. elim. case;ssa. 
ssa. destruct l';ssa'. rewrite inE in H0. destruct (orP H0).
move/eqP :H1. case. intros. subst.  rewrite eqxx //=. apply/orP. eauto. 
Qed.





Lemma map_keys_cat : forall (A B C : eqType) (l0 l1 : seq (A * B)) ( f : A -> C), map_keys f (l0 ++ l1) = map_keys f l0 ++ map_keys f l1.
Proof. 
intros. rewrite /map_keys map_cat //=.
Qed. 

Lemma filter_keys_cat : forall (A B : eqType) (l0 l1 : seq (A * B)) ( f : pred A), filter_keys f (l0 ++ l1) = filter_keys f l0 ++ filter_keys f l1.
Proof. 
intros. rewrite /filter_keys filter_cat //=.
Qed. 

Lemma map_keys2 : forall (A B C D : eqType) (l : seq (A * D)) (fm : A -> B) (f : B -> C), map_keys f (map_keys fm l) = map_keys (fm>>f) l. 
Proof. 
intros. rewrite /map_keys -map_comp //=.
Qed. 

Lemma filter_keys2 : forall (A B : eqType) (l : seq (A * B)) (p p' : pred A ), filter_keys p (filter_keys p' l) = filter_keys (predI p p') l. 
Proof. 
intros. rewrite /filter_keys -filter_predI //=. 
Qed. 



Lemma dom_map_keys : forall (A B C : eqType) (E : seq (A * B)) (f : A -> C), dom (map_keys f E) = map f (dom E).
Proof. 
ssa. rewrite /dom /map_keys -!map_comp //=.
Qed. 



Lemma dom_update : forall (A B: eqType) (E : seq (A * B)) lk T, dom ((update E lk T)) = dom (E).  
Proof. intros. rewrite /dom  /update. ssa.
rewrite /update. rewrite -map_comp. elim : E;ssa. 
case_if;ssa. f_equal. done. f_equal. done. 
Qed. 




Lemma dom_filter_keys : forall (A B : eqType) (E : seq (A * B)) (p : pred A), dom ((filter_keys p E)) = filter p (dom E). 
Proof. 
intros. rewrite /dom /filter_keys filter_map. done. 
Qed. 





Lemma inj_neq : forall (A B : eqType) (f : A -> B) x s' l, x \in l -> s' \in l -> injective_at l f ->
  (f x != f s') = (x != s').
Proof. 
intros. de (eqVneq x s'). subst.  apply/eqP. done. 
apply/negP. intro.  apply/negP. 
apply i. apply/eqP.  apply/H1;eauto. apply/eqP. done. 
Qed. 

Lemma inj_eq : forall (A B : eqType) (f : A -> B) x s' l, x \in l -> s' \in l -> injective_at l f ->
  (f x == f s') = (x == s').
Proof. 
intros. de (eqVneq x s'). apply/eqP. subst. done. 
apply/negP. intro.  apply/negP. 
apply i. apply/eqP.  apply/H1;eauto. apply/eqP. done. 
Qed. 

Lemma subset_same : forall (A : eqType) (l : seq A), subset l l. 
Proof. 
intros. intro. ssa. 
Qed. 

Lemma subset_nil : forall (A : eqType) (l : seq A), subset nil l. 
Proof. 
intros. intro. ssa. 
Qed. 

Lemma subset_cons : forall (A : eqType) (l0 l1 l2 l3 : seq A), subset l0 l1 -> subset l2 l3 -> subset (l0++l2) (l1++l3).
Proof. 
intros. intro. rewrite !mem_cat. move/orP. case. move/H. move=>->. lia.  
move/H0. move=>->. lia.
Qed. 

Lemma subset_map : forall (A B : eqType) (f : A -> B) (l l' : seq A), subset l l' -> subset (map f l) (map f l'). 
Proof. 
intros. intro. ssa. destruct (mapP H0). subst. apply/map_f. auto. 
Qed. 




Lemma mem_map_inj: forall (T1 T2 : eqType) (f : T1 -> T2) (s s' : seq T1) x, subset s s' -> x \in s' ->
  injective_at s' f -> (f x \in map f s) = (x \in s).
Proof.
intros.  apply/eq_iff. split. move/mapP. case. ssa. 
apply H1 in q. subst.  done.  done. apply/H. done. 
intros. apply/map_f. done.
Qed. 





Lemma in_map_keys : forall (A B C : eqType) (l : seq (A * B)) (f : A -> C) x, x \in map_keys f l -> exists y, f y.1 = x.1 /\ y \in l. 
Proof. 
intros. rewrite /map_keys in H. destruct (mapP H). subst. ssa. 
exists x0. ssa. 
Qed. 

Lemma in_filter_keys : forall (A B : eqType) (l : seq (A * B)) (f : pred A) x, x \in filter_keys f l -> f x.1 /\ x \in l.  
Proof. 
intros. rewrite /filter_keys mem_filter in H. ssa. 
Qed. 

Lemma notin_filter_keys : forall (A B : eqType) (l : seq (A * B)) (f : pred A) x, x \notin filter_keys f l -> 
(predC f) x.1 \/ x \notin l.  
Proof. 
intros. rewrite /filter_keys mem_filter in H. ssa.  rewrite negb_and in H. de (orP H).   
Qed. 







Definition pred_dom (A : eqType) (d : seq A) (f : A -> A) (p : pred A) : pred A := fun y => has (fun x => (f x == y) && (p x)) d.


Lemma pred_domP : forall (A : eqType) (l : seq A) x (f : A -> A) (p : pred A), injective_at l f -> x \in l ->
  pred_dom l f p (f x) = p x.
Proof. 
intros. rewrite /pred_dom. 
destruct (p x) eqn:Heqn;ssa.
apply/hasP. exists x.  ssa. ssa. 
apply/negP. intro. destruct (hasP H1). ssa.  
move/eqP : H4. intro.
apply H in H4;ssa. 
subst. rewrite Heqn in H5. done. 
Qed. 

Lemma uniq_in_pair : forall (A B : eqType) (l : seq (A * B)) k v, uniq (dom l) -> (k,v) \in l -> lookup l k = Some v. 
Proof. 
move => A B. 
elim;ssa.
rewrite inE in H1. 
de (eqVneq (k,v) a). subst. 
rewrite lookup_cons_eq //=.
rewrite lookup_cons_neq //=. eauto.  
apply H in H1;ssa.
de (eqVneq a.1 k). subst. apply in_pair in H1. 
 eapply (@map_f _ _ fst) in H1.  ssa. rewrite H1 in H2.  done.
Qed. 



Lemma filter_keys_predT : forall (A B : eqType) (l  : seq ( A* B)), filter_keys predT l = l.
Proof. intros. rewrite /filter_keys. rewrite filter_predT //=.
Qed. 

Lemma in_filter_keys2  : forall (A B : eqType) (l : seq (A * B)) x (p : pred A), x \in l -> p x.1  -> (x \in filter_keys p l).
Proof. 
intros. rewrite /filter_keys mem_filter. ssa.
Qed. 

Lemma in_update : forall (A B : eqType) (l : seq (A * B)) x s T, x \in update l s T -> x.1 <> s -> x \in l.
Proof.
move => A B.  elim;ssa. move : H0. rewrite inE. move/orP. case. intros. norm_eqs. 
move : H1. rifliad. norm_eqs. ssa.
eauto. 
Qed. 

Lemma filter_none : forall (A B : eqType) (l : seq (A * B)) (p : pred A), nil = filter_keys ((predC p)) l -> filter_keys p l = l.
Proof. 
intros. move : H. rewrite /filter_keys. ssa. 
elim : l H;ssa. rifliad. ssa. f_equal. rewrite /predC H1 in H0. ssa.
rewrite /predC H1 in H0. ssa.
Qed. 

Lemma filter_keys_pred0 : forall (A B : eqType) (l : seq ( A* B)), filter_keys pred0 l = nil. 
Proof. 
intros. rewrite /filter_keys. rewrite filter_pred0 //=.
Qed. 


End EnvTheory.









