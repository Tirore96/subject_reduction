
From mathcomp Require Import all_ssreflect zify.
Require Import MPSTSR.Projection.intermediateProj MPSTSR.Projection.projectDecide MPSTSR.Projection.indProj. 
Require Import MPSTSR.CoTypes.coLocal. 
Require Import MPSTSR.IndTypes.elimination.
Require Import MPSTSR.harmony. 
Require Import MPSTSR.Process.processSyntax.
Require Import MPSTSR.Process.env. 
Require Import MPSTSR.Process.preds.
Require Export MPSTSR.Process.SubjectRed.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma zip1 : forall (A B : eqType) (l : seq A) (l' : seq B), size l = size l' -> map fst (zip l l') = l.
Proof.
move=> A B.
elim;ssa. de l'. de l'. inv H0. f_equal. eauto.
Qed.

Lemma zip2 : forall (A B : eqType) (l : seq A) (l' : seq B), size l = size l' -> map snd (zip l l') = l'.
Proof.
move=> A B.
elim;ssa. de l'. de l'. inv H0. f_equal. eauto.
Qed.

(*Duplicated:Congruence.v as lookup_map'*)
Lemma lookup_map : forall (A B : eqType) (l : seq (A * B)) (f : A -> A) lk v,  
    lookup (map_keys f l) lk = Some v -> exists k, k \in dom l /\ f k = lk /\ lookup l k = Some v.
Proof.
move=> A B. elim;ssa.
destruct (eqVneq (f a.1) lk). subst.
rewrite lookup_cons_eq in H0. inv H0. ssa.
exists (a.1).  ssa. rewrite lookup_cons_eq. ssa. done.
ssa. rewrite lookup_cons_neq in H0. 
apply H in H0. ssa.
exists x. ssa.
rewrite lookup_cons_neq. eauto. 
apply/eqP. intro. apply/negP. apply /i. apply/eqP.  subst.
done.
ssa.
Qed.

Inductive EnvsStep : l_env -> option (schl * linearity.label) -> l_env -> Prop := 
 | E_same E : EnvsStep E None E
 | E_step E E' T0 T0' T1 T1' c v s p p'
   : lookup E (schlT s p) = Some T0 ->
            lookup E (schlT s p') = Some T1 ->
            Estep T0 (Sd,c,v) T0' -> Estep T1 (Rd,c,v) T1' -> 
            E' = update (update E (schlT s p) T0') (schlT s p') T1'  ->                      
            EnvsStep E (Some (s,(Action p p' c,v))) E'
 | E_swap E l E' E'' lk lk' T T' : EnvsStep E l E'' ->
                                   lookup E'' lk = Some T ->
                                   lookup E'' lk' = Some T' ->
                                   E' = update (update E'' lk T') lk' T ->
                                   EnvsStep E l E'.

(*Decomposing each rule of EnvsStep*)
Inductive LQ_red : l_env -> q_env ->  l_env -> q_env -> Prop :=
| LQ1 E Q  :  LQ_red E Q  E Q
| LQ2 E Q E' s p c v Q' T T' l : lookup E (schlT s p) = Some T  ->
                                 lookup Q (QKey s p) = Some l  ->
                                 Estep2 T (Sd,c,v) T' ->
                                 E' = update E (schlT s p) (fe T') ->
                                 Q' = update Q (QKey s p) (l++[::(c,v)]) ->
                                  LQ_red E Q E' Q'
| LQ3 E Q E' s p p' c v Q' T T' l l0 : all (fun x => x.1 != c) l0 ->
                                    lookup E (schlT s p) = Some T ->
                                    lookup Q (QKey s p') = Some  (l0++(c,v)::l) ->
                                    Estep2 T (Rd,c,v) T' ->
                                    E' = update E (schlT s p) (fe T') -> 
                                    Q' = update Q (QKey s p') (l0++l) ->
                                    LQ_red E Q E' Q'.
Hint Constructors LQ_red. 

Lemma dom_Ls_to_env : forall L n i, var_sch n \in dom (Ls_to_env L i) -> n < size L + i.
Proof.
elim;ssa.
rewrite inE in H0. de (orP H0). norm_eqs. inv H1. lia.
apply H in H1. lia.
Qed.

Lemma unique_nth : forall (A : eqType) (l : seq A) n n' d, n < size l -> n' < size l ->  uniq l -> nth d l n = nth d l n' -> n = n'.
Proof.
move=> A. elim;ssa. de n. de n'. subst.
have : n' < size l. lia. clear H1 =>H1.
exfalso. apply/negP. apply/H4.
apply/mem_nth. done.
de n'. exfalso. apply/negP. apply/H4. subst. apply/mem_nth. lia.
f_equal. eauto.
Qed.


Lemma Ls_to_env_not_schlT : forall L s p i, schlT s p \notin dom (Ls_to_env L i).
Proof.
elim;ssa.
rewrite !inE negb_or.  ssa.
Qed.

Lemma Ls_iota : forall L i, Ls_to_env L i = zip (map var_sch (iota i (size L))) L.
Proof.
elim;ssa.
f_equal. done.
Qed.

Lemma Ls_to_env_subst : forall (L : seq lType) (ss  : seq sch) i, 
                                                             (map_keys (subst_sch ids ((nth (schlT (var_schl 0) 0) ss))) (zip (map var_sch (iota i (size L))) L)) = 
                                                             zip ((map ((nth (schlT (var_schl 0) 0) ss))) (iota i (size L))) L.
Proof.
elim. case;ssa.
move=> a l IH. case;ssa. 
f_equal. rewrite IH. done.
ssa. f_equal. rewrite IH. done.
Qed.

Lemma nn_test : forall (L : seq lType) i ss, size L <= size ss - i -> zip ((map ((nth (schlT (var_schl 0) 0) ss))) (iota i (size L))) L =  zip (take (size L) (drop i ss)) L.
Proof.
intros. rewrite !map_nth_iota. done. done.
Qed.

Lemma nn_test2 : forall (L : seq lType) ss,  size L = size ss -> (map_keys (subst_sch ids ((nth (schlT (var_schl 0) 0) ss)))  (Ls_to_env L 0)) =
                                            zip ss L.
Proof.
intros. rewrite Ls_iota. rewrite Ls_to_env_subst. rewrite nn_test;last by lia.
rewrite drop0. rewrite H. rewrite take_size. done.
Qed.

Lemma lookup_notin : forall (A B : eqType) (l : seq (A * B)) k, k \notin dom l  -> lookup l k = None. 
Proof.
move=> A B. elim;ssa.
rewrite inE negb_or in H0. ssa. rewrite lookup_cons_neq;ssa. 
rewrite neg_sym. done.
Qed.

(*Overloads another lemma*)
Lemma lookup_update_neq2 : forall (A B : eqType) (l : seq (A * B)) lk lk' v, lk != lk' -> lookup (update l lk v) lk' = lookup l lk'.
Proof.
move=> A B.
elim;ssa. case_if. norm_eqs.
rewrite !lookup_cons_neq.  eauto. done. ssa.
destruct (eqVneq a.1 lk'). 
rewrite !lookup_cons_eq. eauto.  done. done.
rewrite !lookup_cons_neq. eauto. done. done.
Qed.

Lemma lookup_remove_neq2 : forall (A B : eqType) (l : seq (A * B)) lk lk', lk != lk' -> lookup (remove l lk) lk' = lookup l lk'.
Proof.
move=> A B.
elim;ssa. case_if. 
destruct (eqVneq a.1 lk').
rewrite !lookup_cons_eq. eauto.  done. done.
rewrite !lookup_cons_neq. eauto. done. done.
destruct (eqVneq a.1 lk').
rewrite !lookup_cons_eq.  subst. rewrite neg_sym in H0. rewrite H0 in H1. ssa. done.
rewrite !lookup_cons_neq. eauto. done. 
Qed.

Lemma lookup_remove_none : forall (A B : eqType) (l : seq (A * B)) lk lk', lk = lk' -> lookup (remove l lk) lk' = None.
Proof.
move=> A B.
elim;ssa. case_if. subst.
rewrite !lookup_cons_neq. eauto. done. 
eauto.
Qed.

Lemma lookup_update_forall : forall (A B : eqType) (l l' : seq (A * B)) lk' v, (forall lk, lookup l lk = lookup l' lk) -> 
                                                                      (forall lk, lookup (update l lk' v) lk = lookup (update l' lk' v) lk).
Proof.
intros. destruct (eqVneq lk' lk). subst. 
destruct (lk \in dom l) eqn:Heqn. rewrite !lookup_update_in //. 
apply in_dom_exists in Heqn. ssa. rewrite H in H0. apply in_dom in H0. done.
rewrite !lookup_notin //. apply/negP. intro.
rewrite dom_update  in H0. apply in_dom_exists in H0. ssa. rewrite -H in H0.
apply in_dom in H0. rewrite Heqn in H0. done.
 apply/negP. intro.
rewrite dom_update  in H0. rewrite Heqn in H0. done.
rewrite !lookup_update_neq2 //.
Qed.


Lemma lookup_filter_keys_in : forall (A B : eqType) (l : seq (A * B)) (f : A -> bool) lk, f lk ->  lookup (filter_keys f l) lk = lookup l lk.
Proof.
move=> A B. elim;ssa. case_if. destruct (eqVneq a.1 lk). rewrite !lookup_cons_eq //.  
rewrite !lookup_cons_neq //. eauto. 
destruct (eqVneq a.1 lk). rewrite !lookup_cons_eq //.   eauto.
subst. rewrite H1 in H0. done.
rewrite !lookup_cons_neq //. eauto. 
Qed.

Lemma lookup_filter_keys_notin : forall (A B : eqType) (l : seq (A * B)) (f : A -> bool) lk, ~~ f lk  ->  lookup (filter_keys f l) lk = None.
Proof.
move=> A B. elim;ssa. case_if. destruct (eqVneq a.1 lk). 
subst. rewrite H1 in H0. done.
rewrite !lookup_cons_neq //. eauto. eauto.
Qed.

Lemma lookup_filter_keys_all : forall (A B : eqType) (l l' : seq (A * B)) f, (forall lk, lookup l lk = lookup l' lk) -> 
                                               (forall lk, lookup (filter_keys f l) lk = lookup (filter_keys f l') lk).
Proof.
intros. 
destruct (f lk) eqn:Heqn.
rewrite !lookup_filter_keys_in //.
rewrite !lookup_filter_keys_notin //. rewrite Heqn. done. rewrite Heqn. done.
Qed.

Lemma lType_done_equiv : forall E, (uniq (dom E)) -> lType_done E <-> (forall lk T , lookup E lk = Some T -> T =EEnd).
Proof.
move=> E. move=> Hun.
split. clear Hun.
elim : E;ssa.
norm_eqs. de a. subst. 
destruct (eqVneq s lk). rewrite lookup_cons_eq in H1;ssa. inv H1.
rewrite lookup_cons_neq in H1;ssa. eauto.
elim: E Hun;ssa.
move: (H0 a.1 a.2). rewrite lookup_cons_eq. move/(_ Logic.eq_refl). move=>->//. done.
apply/H. done.
intros.   apply/H0. rewrite lookup_cons_neq. eauto.
apply in_dom in H3. apply/eqP. intro. subst. rewrite H3 in H1. done.
Qed.

Lemma qType_done_equiv : forall E, (uniq (dom E)) -> qType_done E <-> (forall lk T , lookup E lk = Some T -> T =nil).
Proof.
move=> E. move=> Hun.
split. clear Hun.
elim : E;ssa.
norm_eqs. de a. subst. 
destruct (eqVneq q lk). rewrite lookup_cons_eq in H1;ssa. inv H1.
rewrite lookup_cons_neq in H1;ssa. eauto.
elim: E Hun;ssa.
move: (H0 a.1 a.2). rewrite lookup_cons_eq. move/(_ Logic.eq_refl). move=>->//. done.
apply/H. done.
intros.   apply/H0. rewrite lookup_cons_neq. eauto.
apply in_dom in H3. apply/eqP. intro. subst. rewrite H3 in H1. done.
Qed.


Lemma dom_eq_in : forall (E0 E' : l_env), (forall lk : sch, lookup E0 lk = lookup E' lk) -> (forall n, n \in dom E0 <-> n \in dom E').
Proof.
intros. split. intros. apply in_dom_exists in H0. ssa. rewrite H in H0. 
apply in_dom in H0. done.
intros. apply in_dom_exists in H0. ssa.  rewrite -H in H0. 
apply in_dom in H0.  done.
Qed.


Lemma lType_done_eq E0 E' : uniq (dom E0) -> uniq (dom E') ->  (forall lk : sch, lookup E0 lk = lookup E' lk) -> lType_done E0 -> lType_done E'.
Proof.
intros. move: H2. rewrite !lType_done_equiv;ssa.
apply/H2.  rewrite H1. eauto.
Qed.

Lemma uniq_insertL0 E T :  uniq (dom E) ->
  uniq (dom (insertL0 E T)). 
Proof.
intros. rewrite /insertL0. ssa. apply/negP. intro. de (mapP H0).
de (mapP H1). de x. inv H4. ssa. de x0. de s.
rewrite dom_map_keys. 
rewrite map_inj_uniq. done. done.
Qed.

Lemma uniq_insertL1 (E : l_env) T : uniq (dom T) ->  uniq (dom E) ->
  uniq (dom (insertL1 E T)). 
Proof.
intros. rewrite /insertL1 /insert_shift. ssa. 
elim : T H H0. ssa. rewrite dom_map_keys. 
rewrite map_inj_uniq. done. done.
ssa. apply/negP. intro. 
rewrite /insert in H1. 
de (mapP H0).  de x.
rewrite /insert in H4. rewrite mem_cat in H4. de (orP H4).
de (mapP H6). de x. ssa. rewrite /initL1 in H8. ssa. inv H8.
ssa. de a. inv H8.
apply/negP. apply/H2. apply/mapP. econ. eauto. done.
apply H in H3;eauto.
 subst. de (mapP H6). inv H7.
de x. de a. de s. asimpl in H9. de p0. de n. inv H9. de s. asimpl in H9. de s.
Qed.

Lemma uniq_remove (E : l_env) lk :  uniq (dom E) ->
  uniq (dom (remove E lk)). 
Proof.
elim : E;ssa.
case_if. ssa. apply/negP. intro.  rewrite /dom /remove  in H3. rewrite /filter_keys in H3.
de (mapP H3). rewrite mem_filter in H4. ssa. de a. de x. subst. 
apply/negP. apply/H1. apply/mapP. econ. eauto. done.
eauto.
Qed.

Lemma uniq_filter (E : l_env) f :  uniq (dom E) ->
  uniq (dom (filter_keys f E )). 
Proof.
elim : E;ssa.
case_if. ssa. apply/negP. intro.  rewrite /dom /remove  in H3. rewrite /filter_keys in H3.
de (mapP H3). rewrite mem_filter in H4. ssa. de a. de x. subst. 
apply/negP. apply/H1. apply/mapP. econ. eauto. done.
eauto.
Qed.

Hint Resolve uniq_insertL0.

Lemma OFT_swap : forall  Ms Ds P E Q C, OFT Ms Ds P E Q C -> forall E', (forall lk, lookup E lk = lookup E' lk) -> uniq (dom E) -> uniq (dom E') -> OFT Ms Ds P E' Q C.
Proof.
move=> Ms Ds P E Q C. elim;try solve [ssa].
econ;eauto. apply/H5;eauto. intros. 
destruct (eqVneq (var_sch 0) lk). rewrite !lookup_cons_eq //.
rewrite !lookup_cons_neq //.
destruct lk. destruct n0. done.
rewrite !lookup_shiftL0_succ. eauto.
rewrite !lookup_shiftL0_id.
eauto.  


econ;eauto. apply/H4;eauto. intros. 
destruct (eqVneq (var_sch 0) lk). rewrite !lookup_cons_eq //.
rewrite !lookup_cons_neq //.
destruct lk. destruct n. done.
rewrite !lookup_shiftL0_succ. eauto.
rewrite !lookup_shiftL0_id. eauto.

econ;eauto;eauto. rewrite -H4. eauto.
apply/H3;eauto.
intros. 
destruct (eqVneq s lk). subst. 
rewrite !lookup_update_in;eauto. rewrite H4 in H1.
apply in_dom in H1. done.
rewrite !lookup_update_neq2 //. 
rewrite dom_update //.
rewrite dom_update //.

econ;eauto. rewrite -H3. eauto.
apply/H2;eauto.
intros. 
destruct (eqVneq s lk). subst. 
rewrite !lookup_update_in;eauto. rewrite H3 in H0.
apply in_dom in H0. done.
rewrite !lookup_update_neq2 //. 
rewrite dom_update //.
rewrite dom_update //.

econ;eauto. rewrite -H6. eauto.
rewrite -H6 //. 
apply/H5;eauto.
intros. 
destruct (eqVneq s' lk). subst. 
rewrite !lookup_remove_none //.
rewrite !lookup_remove_neq2 //=. 
destruct (eqVneq s lk). subst. 
rewrite !lookup_update_in //. rewrite H6 in H0. apply in_dom in H0. done.
apply in_dom in H0. done.
rewrite !lookup_update_neq2 //.
apply/uniq_remove. 
rewrite dom_update //.
apply/uniq_remove. 
rewrite dom_update //.


econ;eauto. rewrite -H3. eauto.
apply/H2;eauto.
intros. 
destruct (eqVneq (var_sch 0) lk). rewrite !lookup_cons_eq //.
rewrite !lookup_cons_neq //.
destruct lk. destruct n. done.
rewrite !lookup_shiftL0_succ. eauto.
destruct (eqVneq s (var_sch n)). subst. 
rewrite !lookup_update_in //.
rewrite H3 in H0. apply in_dom in H0. done.
apply in_dom in H0. done.
rewrite !lookup_update_neq2 //.
rewrite !lookup_shiftL0_id.
destruct (eqVneq s (schlT s0 p)). subst.
rewrite !lookup_update_in //. rewrite H3 in H0. apply in_dom in H0. done.
apply in_dom in H0. done.
rewrite !lookup_update_neq2 //.
apply/uniq_insertL0. rewrite dom_update //.
apply/uniq_insertL0. rewrite dom_update //.

econ;eauto. rewrite -H4. eauto.
apply/H3.
intros. apply/lookup_update_forall. eauto.
rewrite dom_update //.
rewrite dom_update //.

econ;eauto. rewrite -H4. eauto.
intros.  apply/H3. eauto.
intros. apply/lookup_update_forall. eauto.
rewrite dom_update //.
rewrite dom_update //.

intros.
inv H. inv H0. inv H1.
econ. 4: {  apply/H3.  intros. apply/lookup_filter_keys_all. eauto.  apply/uniq_filter. done. apply/uniq_filter. done. } 

4: {  apply/H5. intros. apply/lookup_filter_keys_all. eauto. apply/uniq_filter. done. apply/uniq_filter.  done. } 
econ. econ. econ.

con;eauto.

apply/lType_done_eq. 3:eauto.  done. done. done.


intros. econ;eauto.


intros.  inv H6.
econ. eauto.  7:{ econ. }  
apply/allP. intro. ssa.
apply in_filter_keys in H11. ssa.
apply (allP H0). rewrite mem_filter. ssa.
de x. apply uniq_in_pair in H12;ssa. rewrite -H8 in H12. apply in_pair in H12. done.
done. eauto. eauto. done.
intro. ssa. apply H5 in H11.
apply/dom_eq_in.  2:eauto. intros. rewrite -H8. eauto. 
intros.  apply/H7;eauto.
apply lookup_filter2 in H12. ssa.
apply/lookup_filter. done. rewrite H8. done.

intros. econ;eauto. eapply lType_done_eq. apply H2. done. eauto. done.

intros. econ;eauto.

intros. econ;eauto. 
rewrite -H4. eauto. apply H3;eauto.
intros. 
destruct (eqVneq s' lk). subst. rewrite !lookup_remove_none //.
rewrite !lookup_remove_neq2;ssa. apply uniq_remove. done. apply uniq_remove. done.

intros. econ;eauto.

intros. econ;eauto. apply/H1.
intros. 
destruct lk. rewrite /insertL1 /insert_shift /insert. 
rewrite !lookup_cat.
rewrite !lookup_shiftL1_id. done.
apply/negP. intro. de (mapP H5). de (mapP H6). subst. de x0.
apply/negP. intro. de (mapP H5). de (mapP H6). subst. de x0.
de s. de n.
destruct (p \in dom E1) eqn:Heqn.
rewrite !lookup_cat2. done. 
apply/mapP. de (mapP Heqn).
econ. apply/map_f. eauto. ssa. subst. done.

apply/mapP. de (mapP Heqn).
econ. apply/map_f. eauto. ssa. subst. done.

rewrite !lookup_cat. rewrite !lookup_notin //.
apply/negP. intro. de (mapP H5). de (mapP H6). subst. ssa. de x0. de s. de p0. de n. de s. de s.
apply/negP. intro. de (mapP H5). de (mapP H6). subst. ssa. de x0. de s. de p0. de n. de s. de s.
apply/negP. intro. de (mapP H5). de (mapP H6). subst. ssa. de x0. 
inv H7. eapply (map_f fst ) in H8. rewrite H8 in Heqn. done.
apply/negP. intro. de (mapP H5). de (mapP H6). subst. ssa. de x0. 
inv H7. eapply (map_f fst) in H8. rewrite H8 in Heqn. done.
rewrite !lookup_insertL1_succ //.
apply uniq_insertL1. 

inv H. ssa. rewrite /split_set in H7. inv H7.
rewrite /makeLs. rewrite /dom -map_comp.
inv H5. ssa. inv H8. rewrite /roles.
rewrite -map_comp.
rewrite map_inj_uniq. done.
intro. ssa. inv H9. done.
apply uniq_insertL1. 

inv H. ssa. rewrite /split_set in H7. inv H7.
rewrite /makeLs. rewrite /dom -map_comp.
inv H5. ssa. inv H8. rewrite /roles.
rewrite -map_comp.
rewrite map_inj_uniq. done.
intro. ssa. inv H9. done.
Qed.


Lemma insertL0_update : forall E lk v E', lk \in dom E -> insertL0 (update E lk v) E' = update (insertL0 E E') (shiftL0 lk) v.
Proof.
intros. rewrite /insertL0 /insert_shift /insert. ssa.
rewrite /shiftL0. asimpl. de lk. f_equal.
f_equal.
erewrite update_map_keys;eauto. f_equal.
erewrite update_map_keys;eauto. 
Qed.

Lemma update_cat : forall (A B : eqType) (l l' : seq (A * B)) k v, update (l ++ l') k v = (update l k v)++(update l' k v).
Proof.
move=> A B. elim;ssa.
case_if. norm_eqs. ssa. f_equal. eauto.
f_equal. eauto.
Qed.


Lemma insertL1_update : forall E lk v E', lk \in dom E -> insertL1 (update E lk v) E' = update (insertL1 E E') (shiftL1 lk) v.
Proof.
intros. rewrite /insertL1 /insert_shift /insert. ssa.
rewrite /shiftL0. asimpl. rewrite !update_cat.
have:   list_map initL1 E' =   update (list_map initL1 E') (shiftL1 lk) v.
rewrite /update -!map_comp. apply/eq_in_map.
intro. ssa. rewrite /shiftL1. asimpl. de lk. de s.
move=><-. 
have: map_keys shiftL1 (update E lk v) = update (map_keys shiftL1 E) (shiftL1 lk) v.
erewrite update_map_keys;eauto.
move=><-. done.
Qed.
From Paco Require Import paco.

Lemma not_rec_eq : forall T,  ~~ is_erec T -> fe T = T.
Proof.
intro. rewrite /fe. rewrite /is_erec. destruct T;ssa.
Qed.

Lemma update_remove : forall (A B : eqType) (E : seq (A * B))lk v a, update (remove E a) lk v = remove (update E lk v) a.
Proof.
intros. rewrite /update /remove /filter_keys.  rewrite filter_map.
f_equal. apply/eq_in_filter. intro. ssa. 
case_if. norm_eqs. ssa. lia.
Qed.

Lemma remove_update : forall  (A B : eqType) (E : seq (A * B))lk v, remove (update E lk v) lk = remove E lk.
Proof.
intros. rewrite -update_remove. rewrite update_none. done.
rewrite /remove. rewrite dom_filter_keys mem_filter eqxx //=. 
Qed.

Lemma uniq_in_zip : forall (A B C : eqType) (l  : seq (A * B)) ( l' :  seq (A * C)) k v v', uniq (dom l) ->
dom l = dom l' -> (k,v) \in l -> (k,v') \in l' -> ((k,v),(k,v')) \in zip l l'.
Proof.
move=> A B C.
elim;ssa.  destruct l'. ssa.
simpl. rewrite inE.
inv H1. de a. de p. subst.

rewrite !inE in H2 H3. 
de (orP H2). norm_eqs. inv H0.
de (orP H3). norm_eqs.  inv H6.
ssa. 
rewrite H7 in H4. apply (map_f fst) in H6. ssa. rewrite H6 in H4. done.
de (orP H3). norm_eqs. inv H6.
apply (map_f fst) in H0. ssa. rewrite H0  in H4. done.
Qed.

Lemma OFT_EQ2  : forall  Ms Ds P E Q C, OFT Ms Ds P E Q C -> forall lk T T', uniq_labels T -> lookup E lk = Some (fe T) -> EQ2 T T' ->   OFT Ms Ds P ( update E lk (fe T')) Q C.
Proof.
move=> Ms Ds P E Q C. elim;try solve [ssa].
intros. 
econ;eauto.
rewrite insertL0_update. eapply H5. eauto. 2:eauto.
rewrite /shiftL0. asimpl. de lk. asimpl.
rewrite lookup_insertL0_succ. done.
asimpl. rewrite lookup_cons_neq //=.
rewrite lookup_shiftL0_id //. eauto. 

intros. econ;eauto.
rewrite insertL0_update. eapply H4. eauto. 2:eauto.
rewrite /shiftL0. asimpl. de lk. asimpl.
rewrite lookup_insertL0_succ. done.
asimpl. rewrite lookup_cons_neq //=.
rewrite lookup_shiftL0_id //. eauto. 

intros.  destruct (eqVneq lk s). 
subst. 
move : H4 H5 H6 => Hun H4 H5.
rewrite H1 in H4. inv H4.
punfold H5. inv H5. rewrite -H7 in H6. inv H6. de H9.
econ. done. eauto. 
rewrite lookup_update_in.   econ. eauto.
rewrite update2. 
eapply H3 in H8. erewrite update2 in H8. done. 
apply uniq_full_unf in Hun. rewrite -H7 in Hun. ssa.
rewrite lookup_update_in. done. eauto.

econ;eauto. rewrite lookup_update_neq2;ssa. eauto.
rewrite update_com;ssa. apply/H3.  eauto.
rewrite lookup_update_neq2;eauto. rewrite neg_sym //. done.
apply/eqP=>//.


intros.  destruct (eqVneq lk s). 
subst. 
move : H3 H4 H5 => Hun H3 H4.
rewrite H0 in H3. inv H3.
punfold H4. inv H4. rewrite -H6 in H5. inv H5. de H8.
econ. done.  
rewrite lookup_update_in. econ. eauto.
rewrite update2. 
eapply H2 in H7. erewrite update2 in H7. done. 
apply uniq_full_unf in Hun. rewrite -H6 in Hun. ssa.
rewrite lookup_update_in. done. eauto.

econ;eauto. rewrite lookup_update_neq2;ssa. eauto.
rewrite update_com;ssa. apply/H2. eauto.
rewrite lookup_update_neq2;eauto. rewrite neg_sym //. done.
apply/eqP=>//.


intros. destruct (eqVneq lk s). 
subst. 
move: H6 H7 H8 => Hun H6 H7.
rewrite H0 in H6. inv H6.
punfold H7. inv H7. rewrite -H9 in H8. inv H8. de H11.
econ. done.  
rewrite lookup_update_in. econ. eauto.
rewrite lookup_update_neq2;eauto.  apply/eqP=>//. done. done.
rewrite update2. 
eapply H5 in H10. 
rewrite update_remove in H10.
erewrite update2 in H10. done.
apply uniq_full_unf in Hun. rewrite -H9 in Hun. ssa.


rewrite lookup_remove_neq2 //.
rewrite lookup_update_in. done. eauto.
rewrite neg_sym. apply/eqP=>//.

destruct (eqVneq lk s'). subst.
move: H6 H7 H8 => Hun H6 H7.
rewrite H1 in H6. inv H6.
apply EQ2_eunf in H2.
econ. done. 
rewrite lookup_update_neq2;ssa. eauto.
rewrite lookup_update_in. clear H6.
 econ. eauto.
apply/EQ2_eunf2. 
apply/EQ2_trans. eauto. done.
apply/eqP. rewrite neg_sym.  done.
rewrite -update_remove.
rewrite remove_update.  rewrite update_remove. eauto.
econ. done. 
rewrite lookup_update_neq2;ssa. eauto.
rewrite lookup_update_neq2;ssa. eauto.
done. done. rewrite update_com.
rewrite -update_remove.  eapply H5. eauto.
rewrite lookup_remove_neq2 //.
rewrite lookup_update_neq2;ssa. eauto.
rewrite neg_sym //.
rewrite neg_sym //. done.
by apply/eqP.



intros. destruct (eqVneq lk s). 
subst. 
move : H3 H4 H5 => Hun H3 H4.
rewrite H0 in H3. inv H3.
punfold H4. inv H4. rewrite -H6 in H5. inv H5. destruct H8;last by ssa.
econ.  done. 
rewrite lookup_update_in. eauto. eauto.
eapply (@H2 (shiftL0 s)) in H7.

rewrite update2. 
rewrite insertL0_update.
rewrite -insertL0_update in H7. rewrite update2 in H7.
rewrite -insertL0_update. eauto. eauto. 
rewrite dom_update. eauto. eauto.
apply uniq_full_unf in Hun. rewrite -H6 in Hun. ssa.

rewrite insertL0_update. 
rewrite lookup_update_in. econ.
suff : s \in dom E0. 
intro. de (mapP x).
rewrite /dom /insertL0. ssa. right. 
apply/mapP. econ.  apply/mapP. econ. eauto. econ. ssa. subst. done. eauto. eauto.

econ. done. 
rewrite lookup_update_neq2;ssa. eauto.
move : H3 H4 H5 => Hun H3 H4.

eapply H2 in H4.
rewrite update_com.
rewrite insertL0_update. eauto.
rewrite dom_update. eauto. apply/eqP. done. done.
rewrite /shiftL0. de lk. asimpl.
rewrite lookup_insertL0_succ. 
rewrite lookup_update_neq2;ssa. rewrite neg_sym. done.
asimpl.
rewrite /insertL0 /insert_shift /insert /=.  
rewrite lookup_cons_neq //=.
rewrite lookup_shiftL0_id //. 
rewrite lookup_update_neq2;ssa. 
rewrite neg_sym //.


intros.  destruct (eqVneq lk s). 
subst. 
move : H4 H5 H6 => Hun H4 H5.
rewrite H1 in H4. inv H4.
punfold H5. inv H5. rewrite -H7 in H6. inv H6.
have : l \in dom es1.
have: dom Ts = dom es1.
 move: H10 H13. clear.
elim : Ts es1;ssa. de es1. de es1. inv H13. ssa. de H1. rewrite H0. f_equal.
eauto.
move=><-. apply/mapP. econ. eauto. done.
move=>HDom. de (mapP HDom). de x. subst.
econ. done.  apply H8. 
rewrite lookup_update_in. econ. eauto. 
rewrite update2. 
eapply uniq_in_zip in H8. 4:apply H0.
move/inP : H8. move=>Hzip.
 move/ForallP : H13. move/(_ _ Hzip).
ssa. de H9. eapply H3 in H9.
erewrite update2 in H9. eauto. 
apply uniq_full_unf in Hun. rewrite -H7 in Hun. ssa. apply (allP H13) in H0. ssa.


rewrite lookup_update_in. done. eauto.  
apply uniq_full_unf in Hun. rewrite -H7 in Hun. ssa. 

apply Forall_and. done. eauto.


econ;eauto. rewrite lookup_update_neq2;ssa. 
move : H4 H5 H6 => Hun H4 H5.
rewrite update_com;ssa. apply/H3.  eauto.
rewrite lookup_update_neq2;eauto. rewrite neg_sym //. done.
apply/eqP=>//.


intros.  destruct (eqVneq lk s). 
subst. 
move: H4 H5 H6 => Hun H4 H5.
rewrite H1 in H4. inv H4.
punfold H5. inv H5. rewrite -H7 in H6. inv H6.
econ. done. 2: {  
rewrite lookup_update_in. econ. eauto.  } 
apply Forall_and in H13;ssa. rewrite -H13 //.
intros.
rewrite update2.
move/inP : H8. 
rewrite -zip_map2. move/mapP.
case. intros. inv q. de x. de s0. de s1.
apply same_label in p as Hp. subst.
move: p.
move/mem_zip. ssa.
have: n0 \in dom Ts.
apply Forall_and in H13;ssa. rewrite /dom H13. apply/mapP. econ. eauto. done.
move/mapP. case. ssa. subst. de x.
eapply uniq_in_zip in H9. 4: apply p.
move/inP : H9. move=>Hzip.
move/ForallP : H13.
move/(_ _ Hzip). ssa. de H11.
eapply H3 in H11. erewrite update2 in H11. eauto.
3: { rewrite lookup_update_in. eauto. eauto. } 
apply/inP. rewrite -zip_map2.
eapply uniq_in_zip in p. 4: apply H8.
apply/mapP. econ. eauto. done. rewrite /dom H0. 
apply uniq_full_unf in Hun. rewrite -H7 in Hun. ssa. 
done. 
apply uniq_full_unf in Hun. rewrite -H7 in Hun. ssa. 
apply (allP H14) in p. done.
apply uniq_full_unf in Hun. rewrite -H7 in Hun. ssa. 


apply Forall_and in H13;ssa.
apply Forall_and in H13;ssa.
rewrite /dom H0. done. 
apply uniq_full_unf in Hun. rewrite -H7 in Hun. ssa. 
rewrite /dom H0. done.



econ;eauto. rewrite lookup_update_neq2;ssa. 
intros.
move : H4 H5 H6 H7 => Hun H4 H5 H6.
rewrite update_com;ssa. eapply H3. done. eauto.
rewrite lookup_update_neq2;eauto. rewrite neg_sym //. done.
apply/eqP=>//.

intros.
destruct (f0 lk) eqn:Heqn.
inv H.
econ. 4: {  eapply H3.  eauto. rewrite lookup_filter_keys_in. eauto. done. eauto. } 
rewrite /partition. rewrite filter_keys_update. econ. eauto. eauto.
rewrite filter_keys_update.
rewrite update_none. eauto.
rewrite dom_filter_keys mem_filter /= negb_and /predC Heqn //=.

inv H.  
econ. 5: {  eapply H5. eauto. rewrite lookup_filter_keys_in. eauto. rewrite /predC Heqn //. eauto. } 
rewrite /partition.  f_equal. 
rewrite filter_keys_update. econ. eauto. eauto.

rewrite filter_keys_update.
rewrite update_none. eauto.
rewrite dom_filter_keys mem_filter /= negb_and /predC Heqn //=.  

intros. econ;eauto.

intros. econ;eauto. 
move : H1 H2 H3 => Hun H1 H2.
apply in_pair in H1. apply (allP H0) in H1. ssa. norm_eqs.
punfold H2. inv H2. rewrite H1 in H3. inv H3.
rewrite /lType_done /update. rewrite all_map. apply/allP.
intro. ssa. case_if;ssa. de x. apply (allP H0) in H5. ssa.

intros. econ;eauto.

intros.  
move : H8 H9 H10 => Hun H8 H9.
inv H6.
econ. done. 2:eauto. 2:eauto.
2:eauto. 2:done.
2: { 
intro. ssa. rewrite dom_update. eauto. } 
2 : { 
rewrite /partition. f_equal. }
rewrite filter_keys_update. 
rewrite /lType_done /update. rewrite all_map. apply/allP.
intro. ssa. 


apply in_filter_keys in H10. ssa.
rewrite /lType_done all_filter in H0.
apply (allP H0) in H11. ssa.
move/implyP : H11. move/(_ H10).
move=>HH. norm_eqs. de x. subst. 
case_if;ssa. norm_eqs.
apply in_pair in H8.
apply (allP H0) in H8. ssa.
move/implyP : H8. move/(_ H10). 
move/eqP=>HH. subst. punfold H9. inv H9. rewrite HH in H8. inv H8.
intros.  apply lookup_filter2 in H11. ssa.
destruct (eqVneq lk c). subst. 
rewrite lookup_update_in in H12;ssa. inv H12.
apply/EQ2_eunf2. apply/EQ2_trans. 2:eauto.
apply/EQ2_eunf.
eapply H7. eauto.
rewrite lookup_filter_keys_in. inv H12. eauto.
rewrite lookup_update_neq2 in H12;ssa.
eapply H7. eauto.
rewrite lookup_filter_keys_in. inv H12. eauto.

intros.
move : H1 H2 H3 => Hun H1 H2.
econ;eauto.
apply in_pair in H1. apply (allP H) in H1. ssa.
punfold H2. inv H2. rewrite (eqP H1) in H3. inv H3.
rewrite /lType_done /update. rewrite all_map. apply/allP.
intro. ssa. case_if;ssa. de x. 
apply (allP H) in H5. ssa.

intros. econ;eauto.

intros. 
move : H4 H5 H6 => Hun H4 H5.
destruct (eqVneq s' lk). subst.
econ. eauto. rewrite lookup_update_in. eauto. eauto.
rewrite H0 in H4. inv H4.
apply/EQ2_eunf2. apply/EQ2_trans. eauto. apply/EQ2_eunfl2. done.
rewrite remove_update. eauto.
econ;eauto. rewrite lookup_update_neq2;eauto. rewrite neg_sym //=.
rewrite -update_remove. eapply H3. eauto.
rewrite lookup_remove_neq2;eauto. done.

intros. econ;eauto.

intros.
move : H2 H3 H4 => Hun H2 H3.
econ.  eauto.
rewrite insertL1_update;eauto. instantiate (1:= C1).
eapply H1;eauto.  
destruct lk. ssa. 
rewrite /insertL1 /insert_shift /insert lookup_cat.
rewrite lookup_shiftL1_id. eauto. 
apply/negP. intro. de (mapP H4). de (mapP H5). subst.
de n.
ssa. asimpl. de s. asimpl.
rewrite lookup_insertL1_succ. eauto.
Qed.

Fixpoint seq_update {A B : eqType} (l : seq ( A* B)) (l' : seq (A * B)) {struct l'} := 
match l' with 
| nil => l 
| (k,v)::l'' => (update (seq_update l l'')) k v
end.

Lemma lookup_seq_update : forall (A B : eqType) (l E : seq (A * B)) s, s \notin dom l -> lookup (seq_update E l) s = lookup E s.
Proof.
move=> A B.
elim;ssa. de a. rewrite inE in H0. rewrite negb_or in H0. ssa.
rewrite lookup_update_neq2 //=. eauto.
rewrite neg_sym //.
Qed.


Lemma OFT_EQ_env  : forall E0 Ms Ds P E Q C, (forall k T, lookup E0 k = Some T -> exists T',  lookup E k = Some T' /\ EQ2 T T' /\ ~~ is_erec T /\ ~~ is_erec T')  -> uniq (dom E0) ->  OFT Ms Ds P E Q C -> envP E uniq_labels ->  OFT Ms Ds P (seq_update E E0) Q C.
Proof.
elim;ssa.  de a.
have: lookup ((s, l0) :: l) s = Some l0. rewrite lookup_cons_eq. done. done.
move/H0. ssa.
have: l0 = fe l0. de l0. move=>->.
apply/OFT_EQ2.  apply H.
intros. 
have : k <> s.
intro. subst. apply in_pair in H9. apply (map_f fst) in H9. ssa. rewrite /dom H9 in H4. done.
move=>Hneq.
have: lookup ((s,l0)::l) k = Some T. rewrite lookup_cons_neq //=. rewrite neg_sym. apply/eqP. done.
move/H0. ssa. exists x0. ssa. done. eauto. done. apply/H3. eauto.
rewrite lookup_seq_update;eauto.
2: {  apply/EQ2_sym. eauto. } 
have : fe x = x.  de x.
move=>->. done.
Qed.

Lemma OFT_EQ_env'  : forall E0 Ms Ds P E Q C,   OFT Ms Ds P E Q C -> (forall k T, lookup E0 k = Some T -> exists T',  lookup E k = Some T' /\ EQ2 T T' /\ ~~ is_erec T /\ ~~ is_erec T')  -> uniq (dom E0) -> envP E uniq_labels ->  OFT Ms Ds P (seq_update E E0) Q C.
Proof. intros. apply/OFT_EQ_env;eauto.
Qed.

Lemma seq_update_cat : forall (A B : eqType) (l l0 l1 : seq (A * B)), seq_update (l0 ++ l1) l = (seq_update l0 l) ++ (seq_update l1 l).
Proof.
move=> A B.
elim;ssa. de a. rewrite H. rewrite update_cat. done.
Qed.

Lemma seq_update_notin  : forall (A B : eqType) (l0 l : seq (A * B)), (forall x, x \in dom l0 -> x \notin dom l) -> seq_update l l0 = l.
Proof.
move=> A B.
elim;ssa. de a.  rewrite H.  rewrite update_none. done.
eauto. eauto.
Qed.

Lemma seq_update_dom_eq  : forall (A B : eqType) (l0 l : seq (A * B)), uniq (dom l0) -> dom l0 = dom l -> seq_update l l0 = l0.
Proof.
move=> A B.
elim;ssa. de l. de a.  de l0.  inv H1.
ssa. have : p :: l0 = (p :: nil)++l0. done.
move=>->. rewrite seq_update_cat. rewrite (H l0);ssa.
rewrite seq_update_notin. ssa. rewrite eqxx //=. f_equal.  
rewrite update_none. done. done.
ssa. rewrite inE. apply/eqP. intro. subst. rewrite H0 in H2.
done.
Qed.

Lemma OFT_EQ_env2  : forall E0 E1 Ms Ds P Q C, (forall k T T', lookup E0 k = Some T ->  lookup E1 k = Some T' -> EQ2 T T' /\ ~~ is_erec T /\ ~~ is_erec T')  -> uniq (dom E0) -> dom E0 = dom E1 ->  
OFT Ms Ds P E0 Q C -> envP E0 uniq_labels ->  OFT Ms Ds P E1 Q C.
Proof.
intros.
apply Logic.eq_sym in H1.
erewrite <- (@seq_update_dom_eq _ _ _ _ _ H1). apply/OFT_EQ_env;eauto.
intros. 
have: k \in dom E0. rewrite -H1. apply in_dom in H4. done.
move/in_dom_exists. ssa. exists x. eapply H in H4. 2:eauto. ssa. apply/EQ2_sym. done.
rewrite H1 //.
Unshelve. rewrite H1 //.
Qed.

Lemma OFT_EQ_env2'  : forall E0 E1 Ms Ds P Q C f, OFT Ms Ds P E0 Q C ->  uniq (dom E0) -> (forall k T T', lookup E0 k = Some T ->  lookup E1 k = Some T' -> EQ2 T T' /\ ~~ is_erec T /\ ~~ is_erec T')   -> weaken E0 f E1 -> envP E0 uniq_labels  ->
  OFT Ms Ds P E1 Q C.
Proof.
intros. 
apply/OFT_weaken. apply/OFT_EQ_env2. 5:eauto.  4:eauto. 4:econ. 4:econ. intros. apply lookup_filter2 in H5. destruct H5. eauto. done.
instantiate (1:= f). inv H2. 
inv H2.
Qed.

Lemma OFT_weaken_swap  : forall E0 E1 Ms Ds P Q C, OFT Ms Ds P E0 Q C -> uniq (dom E0) -> uniq (dom E1) -> (forall k T, lookup E0 k = Some T -> lookup E1 k = Some T) -> lType_done (filter_keys (predC (mem (dom E0))) E1) ->
  OFT Ms Ds P E1 Q C.
Proof.
move=> E0 E1 Ms Ds P Q C H Hun Hun' H0 H1.
intros. 
apply/OFT_weaken. 2: { econ. 2:eauto. econ. } 
apply/OFT_swap. eauto.
intros. 
destruct (lk \in dom E0) eqn:Heqn. apply in_dom_exists in Heqn. ssa.
rewrite H2. apply H0 in H2 as HH. rewrite lookup_filter_keys_in. done. apply in_dom in H2.  done.
rewrite !lookup_notin //=.
rewrite dom_filter_keys mem_filter negb_and /= Heqn //=. rewrite Heqn //. done.
rewrite dom_filter_keys. rewrite filter_uniq //.
Qed.


Lemma dom_seq_update  : forall (A B : eqType) (l0 l : seq (A * B)), dom (seq_update l l0)  = dom l.
Proof.
move=> A B. elim;ssa. de a. rewrite dom_update H //.
Qed.

Lemma lookup_seq_update_in  : forall (A B : eqType) (l0 l : seq (A * B)) lk v, lk \in dom l -> lookup l0 lk = Some v -> lookup (seq_update l l0) lk = Some v.
Proof.
move=> A B.
elim;ssa. de a.  destruct (eqVneq s lk). subst. rewrite lookup_cons_eq in H1;ssa. inv H1.
rewrite lookup_update_in //.  rewrite dom_seq_update. done.
rewrite lookup_cons_neq in H1;ssa. rewrite lookup_update_neq2;ssa.
Qed.

Lemma lookup_seq_update_in2  : forall (A B : eqType) (l0 l : seq (A * B)) lk v,  lookup (seq_update l l0) lk = Some v -> lk \in dom l0 -> lookup l0 lk = Some v.
Proof.
move=> A B.
elim;ssa. de a.   rewrite inE in H1. 
destruct (eqVneq lk s). subst.
norm_eqs. rewrite lookup_cons_eq//=.
remember H0. clear Heqe.
rewrite lookup_update_in in H0. inv H0. rewrite dom_seq_update.  apply in_dom in e. rewrite dom_update dom_seq_update in e. done.
ssa. rewrite lookup_cons_neq //=.  rewrite lookup_update_neq2 in H0;ssa. eauto. 
rewrite neg_sym//. rewrite neg_sym//.
Qed.


Lemma OFT_weaken_swap_EQ  : forall E0 E1 Ms Ds P Q C, OFT Ms Ds P E0 Q C -> uniq (dom E0) -> uniq (dom E1) -> (forall k T, lookup E0 k = Some T -> exists T', lookup E1 k = Some T' /\ EQ2 T T' /\ ~~ is_erec T /\  ~~ is_erec T') -> lType_done (filter_keys (predC (mem (dom E0))) E1) -> envP E0 uniq_labels ->
  OFT Ms Ds P E1 Q C.
Proof.
intros.
apply/OFT_weaken_swap.   
apply/OFT_EQ_env2.  4:eauto. 
instantiate (1:= seq_update E0 E1).
intros.  apply H2 in H5 as HH. ssa.
erewrite lookup_seq_update_in in H6. 3:eauto. inv H6. apply in_dom in H5. done. 
erewrite lookup_seq_update_in in H6. 3:eauto. inv H6. apply in_dom in H5. done. 
done. rewrite dom_seq_update. done. done.
rewrite dom_seq_update //. done.
intros. destruct (k \in dom E1) eqn:Heqn. apply lookup_seq_update_in2 in H5;ssa.
rewrite lookup_seq_update in H5;ssa.
apply H2 in H5. ssa. apply in_dom in H5. rewrite Heqn in H5. done. rewrite Heqn //.
rewrite dom_seq_update. done.
Qed.





Lemma lookup_insertL1 : forall E E1 n p T, lookup (insertL1 E E1) (schlT (var_schl n) p) = Some T ->  uniq (dom E1) -> (n = 0 /\ lookup E1 p = Some T) \/
                                                                                  exists n', n'.+1 = n /\ lookup E (schlT (var_schl n') p) = Some T.
Proof.
intros.  move: H0 => HDom.
de n. left. ssa.
rewrite /insertL1 /insert_shift /insert in H. 
destruct (p \in (dom E1)) eqn:Heqn.
rewrite lookup_cat2 in H. apply lookup_map2 in H. ssa. de x. inv H0.
rewrite /initL1 in H0. ssa. apply uniq_in_pair;ssa.
de (mapP Heqn).
apply/mapP. econ. apply/mapP. econ. eauto. done. ssa. de x. subst. done.
rewrite lookup_cat in H. apply lookup_map2 in H. ssa. inv H0. 
de x. de s. de s.
apply/negP. intro. de (mapP H). de x. de (mapP H0).  de x. ssa. inv H3. rewrite /initL1 in H3. ssa.
eapply (map_f fst) in H2. ssa.  inv H5. rewrite Heqn in H2. done.
right.
rewrite lookup_insertL1_succ in H.
econ. con. 2:eauto. done.
Qed.

Lemma lookup_insertL1_id : forall E0 E1 n, lookup (insertL1 E0 E1) (var_sch n) = lookup E0 (var_sch n).
Proof.
intros. rewrite /insertL1 /insert_shift /insert /=. rewrite lookup_cat.
rewrite lookup_shiftL1_id //.
apply/negP. intro. de (mapP H). de (mapP H0). subst. de x0.
Qed.


Lemma lookup_insertL1_0 : forall E0 E1 p, uniq (dom E1) -> lookup (insertL1 E0 E1) (schlT (var_schl 0) p) = lookup E1 p. 
Proof.
move=> E0 E1 p Hun.
intros. 
destruct (p \in dom E1) eqn:Heqn. apply in_dom_exists in Heqn. ssa. apply in_pair in H as HH.
rewrite /insertL1 /insert_shift /insert.  rewrite lookup_cat2.

erewrite lookup_map3. 3:eauto. 3:ssa. ssa.
have: (dom (list_map initL1 E1)) = map (schlT (var_schl 0)) (dom E1).
rewrite /dom -!map_comp. apply/eq_in_map. intro. ssa. move=>->.
rewrite map_inj_uniq.  done. intro. ssa. inv H0.
apply /mapP. econ. apply/mapP. econ. eauto. econ. done.
rewrite !lookup_notin. done.  rewrite Heqn. done.
apply/negP. intro. de (mapP H). de x. subst.
rewrite /insertL1 /insert_shift /insert /= in H0.  rewrite mem_cat in H0. de (orP H0).
de (mapP H1).  de x. ssa. de p0. ssa. rewrite /initL1 in H3. ssa. inv H3.
apply (map_f fst) in H2. ssa. rewrite H2 in Heqn. done.
de (mapP H1). inv H3. de x. de s. de s.
Qed.

Lemma env_insertL1 : forall E E0 , uniq (dom E0) -> (forall lk T, lookup E0 lk = Some T -> uniq_labels T) -> envP E uniq_labels -> envP (insertL1 E E0) uniq_labels.
Proof.
intros.
intro. ssa. de lk. 
rewrite lookup_insertL1_id in H2. eauto.
de s. de n. rewrite lookup_insertL1_0 in H2. eauto. done.
rewrite lookup_insertL1_succ in H2. eauto.
Qed.

Hint Resolve env_insertL1.

Lemma OFT_weaken_swap_EQ_insertL1  : forall E E0 E1 Ms Ds P Q C, OFT Ms Ds P (insertL1 E E0) Q C -> uniq (dom E) -> uniq (dom E0) -> uniq (dom E1) -> (forall k T, lookup E0 k = Some T -> exists T', lookup E1 k = Some T' /\ EQ2 T T' /\ ~~ is_erec T /\  ~~ is_erec T' /\ uniq_labels T) -> all (fun x => x.2 == EEnd) (filter_keys (predC (mem (dom E0))) E1) -> envP E (fun x => ~~ is_erec x /\ lInvPred x /\ uniq_labels x) ->
  OFT Ms Ds P (insertL1 E E1) Q C.
Proof.
intros.  move : H5 => Hinv.
apply/OFT_weaken_swap_EQ. apply:H.
rewrite /insertL1 /insert_shift  /insert /= dom_cat cat_uniq. ssa.
have : dom (map initL1 E0) = map (schlT (var_schl 0)) (dom E0).
rewrite /dom -!map_comp. apply/eq_in_map. intro. ssa. move=>->. 
rewrite map_inj_uniq.   done. intro. ssa. inv H5.
apply/hasPn. intro. rewrite dom_map_keys. move/mapP. case. ssa. subst. 
apply/negP. intro. 
have : dom (map initL1 E0) = map (schlT (var_schl 0)) (dom E0).
rewrite /dom -!map_comp. apply/eq_in_map. intro. ssa. move=>x. rewrite x in H5.
de (mapP H5). de x0. de s. rewrite dom_map_keys.
rewrite map_inj_uniq.   done. done.
rewrite /insertL1 /insert_shift  /insert /= dom_cat cat_uniq. ssa.
have : dom (map initL1 E1) = map (schlT (var_schl 0)) (dom E1).
rewrite /dom -!map_comp. apply/eq_in_map. intro. ssa. move=>->. 
rewrite map_inj_uniq.   done. intro. ssa. inv H5.
apply/hasPn. intro. rewrite dom_map_keys. move/mapP. case. ssa. subst. 
apply/negP. intro. 
have : dom (map initL1 E1) = map (schlT (var_schl 0)) (dom E1).
rewrite /dom -!map_comp. apply/eq_in_map. intro. ssa. move=>x. rewrite x in H5.
de (mapP H5). de x0. de s. rewrite dom_map_keys.
rewrite map_inj_uniq.   done. done.
ssa.  destruct k.  rewrite lookup_insertL1_id in H5. 
exists T. rewrite lookup_insertL1_id. ssa. apply/EQ2_refl. apply Hinv in H5.  ssa. apply Hinv in H5. ssa. apply Hinv in H5. ssa.
de s.
apply lookup_insertL1 in H5. de H5. subst. 
apply H3 in H6. ssa. exists x. ssa.
rewrite lookup_insertL1_0.  done. done.
subst.  exists T. rewrite lookup_insertL1_succ. ssa. apply/EQ2_refl. 
apply Hinv in H6.  ssa. apply Hinv in H6. ssa. apply Hinv in H6. ssa.
done.
rewrite dom_insertL1. move : H4. rewrite /insertL1 /insert_shift /insert /lType_done /= /filter_keys.
rewrite !all_filter all_cat -!map_comp !all_map /=.
ssa. apply/allP. intro. ssa. tunf. ssa. rewrite mem_cat negb_or. 
apply/implyP. intro. ssa. apply (allP H4) in H5. ssa. apply (implyP H5). tunf.
apply/negP. intro. ssa. apply/negP. apply/H7.
move/mapP : H6. case. ssa.
apply/mapP. econ.  eauto. de x. de x0. subst. done.
apply/allP. intro. ssa. tunf. ssa. rewrite mem_cat. rewrite negb_or.
apply/implyP. intro. ssa. 
exfalso. apply/negP. apply/H8. apply/map_f. done.
have : envP E uniq_labels. 
intro. ssa. apply Hinv in H5. ssa.
intros. apply/env_insertL1;eauto.
intros. apply H3 in H5. ssa.
Qed.

Lemma OFT_EQ_insertL1  : forall ps f f' Ms Ds P E Q C, uniq ps -> (forall p, p \in ps -> EQ2 (f p) (f' p) /\ ~~ is_erec (f p) /\  ~~ is_erec (f' p) /\ uniq_labels (f' p)) -> 
OFT Ms Ds P (insertL1 E (map (fun p => (p, f' p)) ps)) Q C -> envP E uniq_labels ->  OFT Ms Ds P (insertL1 E (map (fun p => (p, f p)) ps)) Q C.
Proof.
intros.  move : H2 => Hun.
rewrite /insertL1 /insert_shift /insert /=.
rewrite -map_comp.
erewrite <- (@seq_update_dom_eq _ _ (list_map (initL1 \o (fun p : ptcp => (p, f p))) ps)). 
erewrite <- (@seq_update_notin _ _ _ ( map_keys shiftL1 E)).
erewrite <-seq_update_cat.
apply OFT_EQ_env;eauto.
intros. eapply lookup_map2 in H2. ssa.
rewrite /initL1 in H3. ssa. inv H3.
apply H0 in H2 as Heq.
econ. con. 2:{  con. ssa. eauto. ssa. } 
rewrite lookup_cat2.
eapply lookup_map3.  rewrite /dom -!map_comp.
rewrite map_inj_uniq. done.
intro. ssa. inv H4. 2: {  rewrite /initL1. 
instantiate (1:= (x,f' x)). ssa. } 
apply/mapP. econ. eauto. done.
rewrite /dom -!map_comp. apply/mapP. econ. eauto. done.
 rewrite /dom -!map_comp.
rewrite map_inj_uniq. done. intro. ssa. inv H2.

eapply env_insertL1 in Hun.
move : Hun. instantiate (1:=  (list_map (fun p : ptcp_eqType => (p, f' p)) ps)).
rewrite /insertL1 /insert_shift /insert //=.
rewrite /dom -map_comp. rewrite map_inj_uniq. done.
intro. ssa. 

intros. apply lookup_map2 in H2. ssa. inv H3. apply H0 in H2. ssa.


intros.
rewrite /dom -!map_comp in H2. de (mapP H2).
rewrite dom_map_keys. subst. apply/negP. intro. de (mapP H4). de x. de s.
rewrite /dom -!map_comp.
rewrite map_inj_uniq. done. intro. ssa. inv H2.
rewrite /dom -!map_comp. apply/eq_in_map. intro. ssa.
Qed.
 

Lemma update_filter_q : forall Q (f : hrel qkey ch) lk v, (forall x, x \in dom v -> f lk x)->  update (filter_q Q f) lk v = filter_q (update Q lk v) f.
Proof.
elim;ssa.
case_if;ssa. f_equal. ssa. f_equal.   erewrite filter_keys_eq. erewrite filter_keys_predT. done.
ssa. apply H0 in H2. norm_eqs. done.
norm_eqs. eauto.
f_equal. eauto.
Qed.



Lemma update_insertL1_0 : forall E E1 p v,  update (insertL1 E E1) (schlT (var_schl 0) p) v = 
                                                     insertL1 E (update E1 p v).
Proof.
intros. rewrite /insertL1 /insert_shift /insert /=.
rewrite update_cat. f_equal.
rewrite /update. rewrite -!map_comp.
apply/eq_in_map. intro. ssa.  de x.
case_if. norm_eqs. inv H0. rewrite eqxx. done.
case_if. done.
rewrite /update /map_keys -!map_comp. apply/eq_in_map.
intro. ssa. case_if;ssa. norm_eqs. 
de x. de s. asimpl in H0. de s.
Qed.

Lemma update_insertL1_succ : forall E E1 p v n,  update (insertL1 E E1) (schlT (var_schl n.+1) p) v = 
                                                     insertL1 (update E (schlT (var_schl n) p) v) E1.
Proof.
intros. rewrite /insertL1 /insert_shift /insert /=.
rewrite update_cat. f_equal.
rewrite /update. rewrite -!map_comp.
apply/eq_in_map. intro. ssa.  
rewrite /update /map_keys -!map_comp. apply/eq_in_map.
intro. ssa. case_if;ssa. norm_eqs.  
de x. de s. asimpl in H0. de s. asimpl in H0. inv H0.
rewrite eqxx //=. case_if. ssa. norm_eqs. de x. 
subst. ssa.  asimpl. asimpl in H0. rewrite eqxx in H0. done.
de x.
Qed.

Lemma update_insertL1_var : forall E E1 v n,  update (insertL1 E E1) (var_sch n) v = 
                                                     insertL1 (update E (var_sch n) v) E1.
Proof.
intros. rewrite /insertL1 /insert_shift /insert /=.
rewrite update_cat. f_equal.
rewrite /update. rewrite -!map_comp.
apply/eq_in_map. intro. ssa.  
rewrite /update /map_keys -!map_comp. apply/eq_in_map.
intro. ssa. case_if;ssa. norm_eqs.  
de x. de s. asimpl in H0. inv H0. rewrite eqxx. ssa.
case_if;ssa. norm_eqs. de x. subst.
ssa. rewrite eqxx in H0. done.
Qed.




Lemma update_insertQ_0 : forall E E1 p v,  update (insertQ E E1) (QKey (var_schl 0) p) v = 
                                                     insertQ E (update E1 p v).
Proof.
intros. rewrite /insertQ /insert_shift /insert /=.
rewrite update_cat. f_equal.
rewrite /update. rewrite -!map_comp.
apply/eq_in_map. intro. ssa.  de x.
case_if. norm_eqs. inv H0. rewrite eqxx. done.
case_if. done.
rewrite /update /map_keys -!map_comp. apply/eq_in_map.
intro. ssa. case_if;ssa. norm_eqs. 
de x. de q. asimpl in H0. de s.
Qed.

Lemma update_insertQ_succ : forall E E1 p v n,  update (insertQ E E1) (QKey (var_schl n.+1) p) v = 
                                                     insertQ (update E (QKey (var_schl n) p) v) E1.
Proof.
intros. rewrite /insertQ /insert_shift /insert /=.
rewrite update_cat. f_equal.
rewrite /update. rewrite -!map_comp.
apply/eq_in_map. intro. ssa.  
rewrite /update /map_keys -!map_comp. apply/eq_in_map.
intro. ssa. case_if;ssa. norm_eqs.  
de x. de q. asimpl in H0. de s. asimpl in H0. inv H0.
rewrite eqxx //=. case_if. ssa. norm_eqs. de x. 
subst. ssa.  asimpl. asimpl in H0. rewrite eqxx in H0. done.
de x.
Qed.

Lemma lookup_initL1 : forall E p, lookup (list_map initL1 E) (schlT (var_schl 0) p) = lookup E p.
Proof.
elim;ssa. rewrite /initL1. destruct (eqVneq (schlT (var_schl 0) a.1) (schlT (var_schl 0) p)).
rewrite !lookup_cons_eq. ssa. inv e. ssa.
rewrite !lookup_cons_neq. eauto. apply/eqP. intro. subst.
rewrite eqxx in i. ssa.
ssa.
Qed.

Lemma lookup_initQ : forall E p, lookup (list_map initQ E) (QKey  (var_schl 0) p) = lookup E p.
Proof.
elim;ssa. rewrite /initQ. destruct (eqVneq (QKey (var_schl 0) a.1) (QKey (var_schl 0) p)).
rewrite !lookup_cons_eq. ssa. inv e. ssa.
rewrite !lookup_cons_neq. eauto. apply/eqP. intro. subst.
rewrite eqxx in i. ssa.
ssa.
Qed.

Lemma lookup_filter_keys  : forall (A B : eqType) (l : seq (A * B)) f f' lk, f lk = f' lk -> lookup (filter_keys f l) lk = lookup (filter_keys f' l) lk.
Proof.
move=> A B. elim;ssa.
destruct (eqVneq a.1 lk). subst. rewrite H0. case_if. 
rewrite !lookup_cons_eq //. eauto.
case_if. rewrite lookup_cons_neq;ssa. case_if.
rewrite lookup_cons_neq;ssa. eauto.
case_if. rewrite lookup_cons_neq;ssa. eauto.
Qed.



Lemma not_erec_makeL : forall p l, lcontractive l ->  ~~ is_erec (makeL p l).
Proof.
elim;ssa. destruct (fe l) eqn:Heqn;ssa. 
 eapply iter_eunf_not_rec in H.  exfalso. apply/H. eauto. done.
destruct (nexte_wrap a l0) eqn:Heqn.  apply H.
de a.
destruct (fe l0) eqn:Heqn2;ssa.
apply lcontractive_full_eunf in H0. rewrite Heqn2 in H0. ssa.
apply in_pair in Heqn.
apply (allP H0) in Heqn.  ssa.
destruct (fe l0) eqn:Heqn2;ssa.
apply lcontractive_full_eunf in H0. rewrite Heqn2 in H0. ssa.
inv Heqn. ssa.
Qed.


Lemma filter_keys_cancel_insertL1_2 : forall E E1 f0,
 (filter_keys ((((pred_dom (dom E) shiftL1 f0)))) (insertL1 E E1)) =  map_keys shiftL1 (filter_keys ( f0) E).
Proof. 
intros. rewrite /insertL1 /insert_shift /insert. ssa. rewrite filter_keys_cat. 
erewrite filter_keys_eq. erewrite filter_keys_pred0. ssa.
rewrite filter_keys_map_keys. f_equal. 
apply/filter_keys_eq. intro. ssa. 
rewrite pred_domP //=. 
ssa.
ssa.
de (mapP H). subst. de (mapP H0). subst. ssa.
rewrite /pred_dom. ssa. rewrite /pred0. apply/hasPn.
intro. ssa. rewrite negb_and. ssa.
left. apply/eqP. intro. de x0. de s.
Qed.

Lemma zip_swap : forall (A B : eqType) (l : seq A) (l' : seq B) x x', size l = size l' -> (x,x') \in zip l l' -> (x',x) \in zip l' l.
Proof.
move=> A B. elim;ssa.
de l'. de l'. rewrite inE in H1. de (orP H1). norm_eqs. inv H2. ssa.
Qed.


Lemma uniq_makeL : forall l e, uniq_labels e ->  uniq_labels (makeL l e).
Proof.
elim;ssa. apply/uniq_full_unf. done.
rewrite /nexte_wrap. de a. destruct (full_eunf e) eqn:Heqn;ssa.
destruct (lookup _ _) eqn:Heqn2;ssa.  apply/H.
apply uniq_full_unf in H0. rewrite Heqn in H0. ssa.
apply in_pair in Heqn2. apply (allP H2)in Heqn2. done.
destruct (fe e) eqn:Heqn2;ssa. apply/H.
apply uniq_full_unf in H0. rewrite Heqn2 in H0. ssa.
Qed.

Lemma esize0 : forall l, 0 < esize l. 
Proof. case;ssa.  elim: l;ssa.
lia.
Qed.

Lemma foldr0 : forall l, 0 < foldr (fun e0 : fin * lType => addn (esize e0.2)) 2 l.
Proof. case;ssa. 
move: (esize0 a.2). lia.
Qed.
Lemma in_foldr : forall  (es : seq (nat  * lType)) n e, (n,e) \in es -> esize e < foldr (fun e0 : fin * lType => addn (esize e0.2)) 2 es.
Proof.
elim;ssa.
rewrite inE in H0. de (orP H0). norm_eqs. ssa. 
move: (foldr0 l). lia.
apply H in H1. 
move: (esize0 a.2). lia.
Qed.

Lemma lookup_insertQ : forall E E1 n p T, lookup (insertQ E E1) (QKey (var_schl n) p) = Some T ->  uniq (dom E1) -> (n = 0 /\ lookup E1 p = Some T) \/
                                                                                  exists n', n'.+1 = n /\ lookup E (QKey (var_schl n') p) = Some T.
Proof.
intros.  move: H0 => HDom.
de n. left. ssa.
rewrite /insertL1 /insert_shift /insert in H. 
destruct (p \in (dom E1)) eqn:Heqn.
rewrite lookup_cat2 in H. apply lookup_map2 in H. ssa. de x. inv H0.
rewrite /initL1 in H0. ssa. apply uniq_in_pair;ssa.
de (mapP Heqn).
apply/mapP. econ. apply/mapP. econ. eauto. done. ssa. de x. subst. done.
rewrite lookup_cat in H. apply lookup_map2 in H. ssa. inv H0. 
de x. de q. de s.
apply/negP. intro. de (mapP H). de x. de (mapP H0).  de x. ssa. inv H3. rewrite /initL1 in H3. ssa.
eapply (map_f fst) in H2. ssa.  inv H5. rewrite Heqn in H2. done.
right.
rewrite lookup_insertQ_succ in H.
econ. con. 2:eauto. done.
Qed.


Lemma dom_roles : forall x1, uniq
       (dom
          (list_map (fun p : fin => (Ptcp p, fe (trans (Ptcp p) x1))) (roles x1))).
Proof.
intros.
have: dom (list_map (fun p : fin => (Ptcp p, fe (trans (Ptcp p) x1))) (roles x1)) = map Ptcp (roles x1).
rewrite /dom -!map_comp. apply/eq_in_map. intro. ssa.
move=>->. 
rewrite map_inj_uniq. rewrite sort_uniq. apply undup_uniq.
intro. ssa. inv H.
Qed.

Hint Resolve dom_roles.

Lemma queue_add2' : forall msgs Ms Ds s i p E Q C l s' p' T' T'' (f0 : pred sch),
lookup E (schlT s' p') = Some T'' -> f0 (schlT s' p') ->  QKey s p \in dom Q ->
OFT Ms Ds (MsgQ (schliT s i) (msgs))
    (filter_keys ((predC f0)) E)
    (update Q (QKey s p) l) C -> EQ2 T' T'' ->

OFT Ms Ds (MsgQ (schliT s i) (msgs ++ [:: msgT (schM (schlT s' p')) p]))
    (filter_keys  (predC (predI (fun c : sch => c != schlT s' p') f0)) E)
    (update Q (QKey s p) (l ++ [:: (i, inl (VLT T' ptcp0))])) C.
Proof. 
elim;ssa. inv H.
have : l = nil. have : (QKey s p,l) \in update Q (QKey s p) l. apply/in_pair.
rewrite lookup_update_in.  done.  done. intros. 
inv H2. apply (allP H9) in x.  ssa. norm_eqs. done. intros. subst. 
ssa.
econ. 
rewrite lookup_update_in. econ. done.
apply/lookup_filter. tunf.  rewrite eqxx //=. eauto.  eauto. 
inv H2.  
econ. rewrite /remove filter_keys2. apply/allP. intro. ssa. apply in_filter_keys in H4.  ssa.
tunf_in H4. ssa. rewrite negb_and negb_involutive in H10. 
de (orP H10). norm_eqs. rewrite H4 eqxx //= in H8.  apply (allP H6).
apply/in_filter_keys2. done. tunf. done. 
rewrite update2. done. 

inv H3. 
- de (eqVneq p p0). subst. rewrite lookup_update_in //= in H15. inv H15. 
  econ. eauto. rewrite lookup_update_in. ssa. done. rewrite update2 //=. 
  apply/H. eauto. done.  done.  rewrite update2 in H16. done. done.
  apply Congruence.lookup_update_neq2 in H15. 
  econ;eauto. erewrite lookup_update_neq. eauto.  eauto. intro. inv H5. rewrite eqxx in i0. done. 
  rewrite update_com.
  eapply H. eauto. done. rewrite dom_update. done. rewrite update_com.  eauto. intro.   inv H5. rewrite eqxx in i0. done. 
  eauto.
  intro. inv H5. rewrite eqxx in i0. done.
  intro. inv H5. rewrite eqxx in i0. done.


- de (eqVneq p p0). subst. rewrite lookup_update_in //= in H11. inv H11. 
  econ. eauto. rewrite lookup_update_in. ssa. done. 
  apply lookup_filter. tunf.  rewrite negb_and negb_involutive. 
  de (eqVneq s'0 (schlT s' p')). eapply lookup_filter2 in H15. ssa. 
  eapply lookup_filter2 in H15. ssa.  eauto. done.
  rewrite update2 //=. 
  rewrite /remove filter_keys2. erewrite filter_keys_eq. 
  apply/H.  5:eauto. done. instantiate (1 := predU f0 (fun c => c == s'0)). 
  tunf. rewrite H1 //=.  done.
2 : { 
                  intros. tunf. rewrite negb_and negb_involutive.  

                  apply lookup_filter2 in H15. ssa.
                  de (eqVneq x s'0). subst. rewrite orbC //=. rewrite andbC //=. rewrite negb_involutive. 
                  de (eqVneq s'0 (schlT s' p')). subst.  rewrite /predC H1 in H6.  done. 
                  de (eqVneq x (schlT s' p')).  rewrite negb_or andbC //=. } 
rewrite update2 in H17. erewrite filter_keys_eq.
rewrite /remove filter_keys2 in H17. 
 eauto. ssa.  tunf.  rewrite negb_or andbC. done.   



  apply Congruence.lookup_update_neq2 in H11. 
  econ;eauto. erewrite lookup_update_neq. eauto.  eauto. intro. inv H5. rewrite eqxx in i0. done. 
  apply lookup_filter. tunf. rewrite negb_and. de (eqVneq (s'0) (schlT s' p')). 
  apply lookup_filter2 in H15. ssa. apply lookup_filter2 in H15. ssa.
  rewrite update_com. rewrite /remove filter_keys2. erewrite filter_keys_eq. 
  eapply H. 5:eauto. eauto.
  4 : { intros. tunf.  instantiate (1 := predU f0 (fun c => c == s'0)). 
rewrite negb_and negb_involutive.  

                  apply lookup_filter2 in H15. ssa.
                  de (eqVneq x s'0). subst. rewrite negb_and.  tunf. rewrite negb_or. rewrite /predC in H6. rewrite H6 eqxx //= orbC //=. 
                  de (eqVneq s'0 (schlT s' p')). subst.  rewrite /predC H1 in H6.  done. 
                  de (eqVneq x (schlT s' p')).  rewrite negb_or andbC //=.
  rewrite i1 //=. } tunf. 
de (eqVneq s'0 (schlT s' p')). 

rewrite dom_update. done. rewrite update_com.  erewrite filter_keys_eq. 
  rewrite /remove filter_keys2 in H17.  eauto. 
  ssa. tunf. rewrite negb_or. rewrite andbC //=.
intro.   inv H5. rewrite eqxx in i0. done. 
  intro. inv H5. rewrite eqxx in i0. done.
  intro. inv H5. rewrite eqxx in i0. done.

- de (eqVneq p p0). subst.  rewrite update2 in H15. rewrite lookup_update_in in H14. inv H14. 
  econ.   rewrite lookup_update_in. ssa. done. rewrite update2 //=. 
  apply/H. eauto. done.  done.  done.  done. done.
  apply Congruence.lookup_update_neq2 in H14. 
  econ;eauto. erewrite lookup_update_neq. eauto.  eauto. intro. inv H5. rewrite eqxx in i0. done. 
  rewrite update_com.
  eapply H. eauto. done. rewrite dom_update. done. rewrite update_com.  eauto.  intro. inv H5. rewrite eqxx in i0. done. 
  eauto.
  intro. inv H5. rewrite eqxx in i0. done. 
  intro. inv H5. rewrite eqxx in i0. done. 
Qed.


Lemma OFT_EQ3  : forall  Ms Ds P E E' Q C, OFT Ms Ds P E Q C -> forall lk T T', ~~is_erec T -> ~~is_erec T' -> lookup E lk = Some T -> uniq_labels T -> EQ2 T T' -> E' = ( update E lk T')->   OFT Ms Ds P E'  Q C.
Proof.
intros. subst.  rewrite -(@not_rec_eq T');ssa.
apply/OFT_EQ2. done. 3:eauto. done. rewrite not_rec_eq;ssa.
Qed.

Lemma OFT_EQ4  : forall  Ms Ds P E Q C, forall lk T T', uniq (dom E) -> OFT Ms Ds P (update E lk T') Q C ->  ~~is_erec T -> ~~is_erec T' -> lookup E lk = Some T -> uniq_labels T' -> EQ2 T T' ->   OFT Ms Ds P E Q C.
Proof.
intros. eapply OFT_EQ3 in H0. eauto. 4:eauto.
5: {  erewrite update2. rewrite update_same. done. eauto. done. } 
4: { rewrite /EQ2 in H5.
apply/EQ2_sym. eauto. }  done. done.
rewrite lookup_update_in. done.
apply in_pair in H3. apply/mapP. econ. eauto. done.

Qed.



Lemma filter_keys_update_not : forall (A B : eqType) f k v (l : seq (A * B)), f k = false -> filter_keys f (update l k v) = filter_keys f l.
Proof.
intros. rewrite filter_keys_update. rewrite update_none. done.
apply/negP. intro. destruct (mapP H0). apply in_filter_keys in H1. ssa.
subst. rewrite H1 in H. done.
Qed.

Lemma dom_Ls_to_env2 : forall L, dom (Ls_to_env L 0) = map var_sch (iota 0 (size L)).
Proof.
intros. rewrite Ls_iota. rewrite /dom zip1 //. rewrite size_map size_iota //.
Qed.


Lemma mem_zip_iota : forall (A : eqType) n' n (l : seq A) d k v, size l = n' -> (k,v) \in zip (iota n n') l -> nth d l (k - n) = v.
Proof.
move=> A. elim.
ssa. de l.
ssa. de l. rewrite inE in H1. de (orP H1). norm_eqs. inv H2. have : n0 - n0 = 0. lia. move=>->. ssa.
inv H0.
eapply H in H2 as HH;ssa. rewrite -HH. 
apply mem_zip in H2. ssa. rewrite mem_iota in H2. ssa.
instantiate (1:= d). de k. have : k.+1 - n0.+1 = k - n0. lia. move=>->.
have : k.+1 - n0 = (k - n0).+1. lia. move=>->. done.
Qed.

Lemma mem_zip_iota2 : forall (A : eqType) n' n (l : seq A) d k v, size l = n' -> (var_sch k,v) \in zip (map var_sch (iota n n')) l -> nth d l (k - n) = v.
Proof.
move=> A. elim.
ssa. de l.
ssa. de l. rewrite inE in H1. de (orP H1). norm_eqs. inv H2. have : n0 - n0 = 0. lia. move=>->. ssa.
inv H0.
eapply H in H2 as HH;ssa. rewrite -HH. 
apply mem_zip in H2. ssa. de (mapP H2). rewrite mem_iota in H4. ssa.
instantiate (1:= d). inv H5. de x. have : x.+1 - n0.+1 = x - n0. lia. move=>->.
have : x.+1 - n0 = (x - n0).+1. lia. move=>->. done.
Qed.

Lemma uniq_roles x : uniq (roles x).
Proof.
rewrite sort_uniq undup_uniq //.
Qed.
Hint Resolve uniq_roles.
