
From mathcomp Require Import all_ssreflect zify.
Require Import MPSTSR.Projection.intermediateProj MPSTSR.Projection.projectDecide MPSTSR.Projection.indProj. 
Require Import MPSTSR.CoTypes.coLocal. 

From Paco Require Import paco.
Require Import MPSTSR.IndTypes.elimination.
Require Import MPSTSR.harmony. 

Require Import MPSTSR.Process.processSyntax.
Require Import MPSTSR.Process.env. 
Require Import MPSTSR.Process.preds.
Require Export MPSTSR.Process.SubjectRed3.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(*we need EQ_same because coherence depends on global type, and *)
(*global type reduction might unfold some projections. Thus all *)
(*environtmens Delta,Q are not directly coherent, because they are *)
(*derived as \Delta,Q = decomp(G) and proj(G,p) \approx proj(G',p) *)
(*can happen*)
Definition weak_coherent_as l q (L : seq (ptcp * lType)) := (*exists L', EQ_same L L' /\*) coherent L /\  exists f, can_split L f /\ 
  (l,q) = split_set L f.

Definition Estep_eq E l E' := exists E'', Estep E l E'' /\ EQ2 E'' E'.

Inductive EnvStep3 : seq (ptcp * lType)  -> linearity.label -> seq (ptcp * lType) -> Prop := 
| envstep_rule E p_from p_to T0 T1 T0' T1' c u E'
:  lookup E p_from = Some T0 -> lookup E p_to = Some T1 -> 
   lookup E' p_from = Some T0' -> lookup E' p_to = Some T1' -> 
   Estep_eq T0 (Sd,c,u) T0' -> Estep_eq T1 (Rd,c,u) T1' ->
   dom E = dom E' -> 
   (forall p T0 T1, p != p_from -> p != p_to -> lookup E p = Some T0 -> lookup E' p = Some T1 -> EQ2 T0 T1) ->
   EnvStep3 E (Action p_from p_to c,u) E'.
Hint Constructors EnvStep3.

Lemma from_weak_coherent_as : forall E Q L, weak_coherent_as E Q L -> weak_coherent E Q.
Proof.
intros. exists L.
inv H. ssa. eauto.
Qed.

Lemma weak_coherent_as_eq : forall E Q L, weak_coherent_as E Q L -> EQ_same E E.
Proof.
intros. apply/weak_coherent_eq.
apply from_weak_coherent_as in H. eauto.
Qed.

Lemma weak_coherent_as_eq2 : forall E Q L, weak_coherent_as E Q L -> EQ_same L L.
Proof.
intros.
con. ssa.
ssa. rewrite H0 in H1. inv H1.
apply/EQ2_refl.
apply in_pair in H0.
inv H. ssa. inv H2. ssa. subst.
de (mapP H0). inv H9.
apply -> lInvPred_iff.
apply gInvPred_proj.
inv H5.
ssa.
move: (H14 x2).
case. intros.
apply Project_gtree in p.
apply/gUnravel2_Rol.  eauto.
Qed.

Lemma to_EnvStep3 : forall G (Hlin : linearity.Linear G) (Hsize: size_pred G) (Hproj : projectable G) G' (Hinv : gInvPred G') (p0 p1 : nat) (Hneq : p1 == p0 = false)c v (x2 : seq nat ), linearity.step G (Action p0 p1 c,v) G' -> p0 \in x2 -> p1 \in x2 -> uniq x2 ->
    EnvStep3 (list_map (fun p : nat => ( Ptcp p, fe (trans p G))) x2) (Action p0 p1 c,v) (list_map (fun p : nat => ( Ptcp p, fe (trans p G'))) x2).
Proof.
intros. 
econ.

erewrite lookup_map3. 4:{ econ. } econ.
rewrite /dom -map_comp.
rewrite map_inj_uniq. done. intro. ssa. inv H3.
done.

erewrite lookup_map3. 4:{ econ. } econ.
rewrite /dom -map_comp.
rewrite map_inj_uniq. done. intro. ssa. inv H3. done.

erewrite lookup_map3. 4:{ econ. } econ.
rewrite /dom -map_comp.
rewrite map_inj_uniq. done. intro. ssa. inv H3. done.

erewrite lookup_map3. 4:{ econ. } econ.
rewrite /dom -map_comp.
rewrite map_inj_uniq. done. intro. ssa. inv H3. done.

exists (trans p0 G'). con.
apply/Estep_full_unf2.
eapply preserve_proj in H.
ssa. eauto.
ssa. rewrite /comp_dir //= eqxx //=.
done. done.
apply/EQ2_eunf2. 
apply/EQ2_refl.
apply/gInvPred_proj.
done.

exists (trans p1 G'). con.
apply/Estep_full_unf2.
eapply preserve_proj in H.
ssa. eauto.
ssa. rewrite /comp_dir //= eqxx //=.
case_if. done.
done. done.
apply/EQ2_eunf2. 
apply/EQ2_refl.
apply/gInvPred_proj.
done.

rewrite /dom -!map_comp.
apply/eq_in_map. intro.
ssa.
intros.


apply lookup_map2 in H5,H6. ssa.
inv H7.
inv H8.
apply/EQ2_eunf2.
apply/EQ2_eunfl2.

move : (Hproj x).
ssa.

eapply preserve_proj2 in H. eauto.
eauto.
apply/gUnravel2_Rol.
apply/Project_gtree. eauto.
simpl.
rewrite /comp_dir /= (negbTE H3) (negbTE H4) //=.
done. done.
Qed.


Lemma coherence_pres_as  : forall myCo E Q E' Q', LQ_red2 E Q E' Q' -> weak_coherent_as E Q myCo -> 
exists E'' myCo', weak_coherent_as E'' Q' myCo' /\  EQ_same E'' E' /\ (myCo = myCo' \/ exists l, EnvStep3 myCo l myCo').
Proof.
intros.
inv H. 
- (*reflexive*) exists E',myCo. ssa. apply/weak_coherent_as_eq. eauto.
- (*send*)
exists ((update E p (fe T'))),myCo. 
move : myCo H0 => x H0.
  have :  weak_coherent_as (update E p (fe T')) 
    (update Q p (l ++ [:: (c, v)])) x.

move : H0 H1 H2 H3 => H2 H4 H5 H6.
  inv H2.
  move : is_true_true => H3.
  move : is_true_true => H7.
  move : is_true_true => H8.
  ssa. 
  move : H0 H1 H7 H8 => H7 H8 H0 H1.
 inv H9. 
 econ. done. econ. con. 2:{ rewrite /split_set. 
instantiate (1:= (fun p' => if (p == p') && (p \in dom x) then (x0 p)++[::if v is inr n then Some n else None] else x0 p')).
 rewrite /update /makeLs -!map_comp. f_equal.
apply/eq_in_map. intro.
ssa. case_if. f_equal. 
norm_eqs. rewrite eqxx. ssa. 
eapply (map_f fst) in H10 as H_temp. rewrite/dom. rewrite H_temp. clear H_temp.

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
(*ssa. by apply/checkPath_fe2.*) (*removed*)
 de a. destruct (fe _) eqn:Heqn;ssa. destruct (lookup _ _) eqn:Heqn2;ssa.
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

ssa. 

apply/weak_coherent_as_eq. eauto.

- (*receive*)


move : myCo H0 => x H0.

move: H0 H1 H2 H3 H4 => H2 H4 H5 H6 H7.

move : H4 is_true_true H5 H6 H7 => Hall H4 H7 H5 H6.
move : is_true_true is_true_true is_true_true  => H0 H1 H3.
inv H2. ssa.
inv H10. clear H10. inv H8. ssa. subst.



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

exists ((list_map (fun p : fin => (Ptcp p, fe (trans p G'))) x2)). 

have:   weak_coherent_as
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
             (fe (trans (Ptcp p_send) G)))))
    (list_map (fun p : fin => (Ptcp p, fe (trans p G'))) x2).

eapply (@preserve_proj _ _ _ p_send Sd) in HStep as H_send.
eapply Estep_full_unf2 in H_send.

eapply (@preserve_proj _ _ _ p_receive Rd) in HStep as H_receive.
eapply Estep_full_unf2 in H_receive.

clear H x3 H3 H0 H2.
move : H4 => H. 
move : H5 H6 H7 H8 => H0 H1 Hun' H2.
move : H_makeQ_safe => H_makeQ. 
econ.
econ. 

exists x2.
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

exists (fun p => if p == Ptcp p_send then x++y' else lp_fun p).
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
1:{
apply/eqP. intro. 
apply to_canEstep2 in H_Estep2.
eapply makeQ_ETr3 in H_Estep2;eauto.
ssa. eapply test_test in H11. 
7: {   eauto. rewrite H8 in H_makeQ. eauto. }
apply/negP.  apply (allP H11). apply : H13. done.
apply:Project_eunf2. apply:Project_EQ2. apply : HP_receive.
apply:EQ2_refl. apply:gInvPred_proj. 
apply/gInvPred_iff/Project_gtree. eauto. 
done. done. done. done. }
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

(*econ. con. eauto.
ssa. eauto.
econ.*)

2: { right.

exists (Action p_send p_receive c,v).
apply/to_EnvStep3.
done. done. done.
apply/step_gInvPred.  eauto. 
move : (H8 p_send).
case. ssa.
apply/gUnravel2_Rol.
apply/Project_gtree. eauto.
simpl.



apply label_pred in HStep.
ssa. rewrite neg_sym in HStep. 
apply/eqP. intro. by rewrite H1 eqxx in HStep.
done. done. done. done. done. done.
}
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

Inductive EnvStep4 : l_env  -> linearity.label -> l_env -> Prop := 
| envstep_rule5 E p_from p_to T0 T1 T0' T1' c u E' s
:  lookup E (schlT s p_from) = Some T0 -> lookup E (schlT s p_to) = Some T1 -> 
   lookup E' (schlT s p_from) = Some T0' -> lookup E' (schlT s p_to) = Some T1' -> 
   Estep_eq T0 (Sd,c,u) T0' -> Estep_eq T1 (Rd,c,u) T1' ->
   dom E = dom E' -> 
   (forall p T0 T1, p != schlT s p_from -> p != schlT s p_to -> lookup E p = Some T0 -> lookup E' p = Some T1 -> EQ2 T0 T1) ->
   EnvStep4 E (Action p_from p_to c,u) E'.
Hint Constructors EnvStep4.



Lemma Linearity_GEnd : linearity.Linear GEnd.
Proof.
rewrite /linearity.Linear. ssa. 
inv H. de aa_p.
inv H. de aa_p.
Qed.



Lemma coherentG_GEnd : coherentG GEnd.
Proof.
rewrite /coherentG. ssa.
apply/Linearity_GEnd.
intros. exists EEnd. pfold. con. con.
move/part_of2_unf2.
move=> HH. inv HH. inv HH. inv H0. inv H1.
pfold. con. con.
pfold. con. intros. inv H.
Qed.




Lemma coherent_nil : coherent nil.
Proof.
rewrite /coherent. exists GEnd. exists nil. ssa. apply/coherentG_GEnd.
Qed.



Definition env_coherent_as (E : l_env) (Q : q_env) (L : l_env) := 
only_schl E /\ only_schl L /\
forall s, 
 weak_coherent_as (L_from_env (filter_keys (l_sess s) E)) (Q_from_env (filter_keys (q_sess s) Q)) (L_from_env (filter_keys (l_sess s) L)). 



Lemma  env_coherent_as_nil : env_coherent_as [::] [::] [::].
Proof.
rewrite /env_coherent_as. intros. rewrite /filter_keys /=. 
rewrite /weak_coherent_as. ssa. ssa.
apply/coherent_nil.
exists (fun _=> nil). ssa.
Qed.

Lemma  env_coherent_nil : env_coherent [::] [::].
Proof.
rewrite /env_coherent. 
exists nil. 
exists (fun _=> nil). ssa.
Qed.

Definition EQ_domLQ := fun (L : l_env) (Q : q_env) => only_schl L /\ uniq (dom L) /\ uniq (dom Q) /\ (forall s p, (schlT s p \in dom L) = (QKey s p \in dom Q)).

Lemma EQ_domLQ_nil : forall Q, EQ_domLQ nil Q -> Q = nil.
Proof.
rewrite /EQ_domLQ. ssa. 
de Q.  de p. de q.
move: (H2 s p ). rewrite !inE /= eqxx in_nil //=. 
Qed.

Lemma EQ_domLQ_nil' : forall L, EQ_domLQ L nil -> L = nil.
Proof.
rewrite /EQ_domLQ. ssa. 
de L.  de p. rewrite /only_schl in H. ssa. de l.
move:(H2 s p). rewrite !inE eqxx //=.
Qed.

Lemma EQ_domLQ_cons : forall L q Q, EQ_domLQ L (q::Q) -> exists l L', L = l::L'.
Proof.
rewrite /EQ_domLQ. ssa. 
de L. de q. de q.
move: (H2 s p ). rewrite !inE /= eqxx in_nil //=. 
eauto.
Qed.

Lemma EQ_domLQ_cons' : forall l L Q, EQ_domLQ (l::L) Q -> exists q Q', Q = q::Q'.
Proof.
rewrite /EQ_domLQ. ssa. 
de Q. de l. de l.
rewrite /only_schl in H. ssa.
move: (H1 s p ). rewrite !inE /= eqxx in_nil //=. 
eauto.
Qed.

Lemma dom_makeLs : forall l f, dom (makeLs l f) = dom l.
Proof.
elim;ssa. f_equal. eauto.
Qed.

Lemma env_coherent_as_dom : forall E Q L s p , env_coherent_as E Q L -> (schlT s p) \in dom L -> schlT s p \in dom E.
Proof.
intros. inv H. ssa. move: H H1 H2 H3 => _ Ho' Ho'' H.
move: (H s).
intros. inv H1. ssa. inv H4.
suff: schlT s p \in dom (filter_keys (l_sess s) E).
rewrite dom_filter_keys mem_filter. ssa.
have: p \in dom (makeLs (L_from_env (filter_keys (l_sess s) L)) x).
rewrite dom_makeLs.
rewrite /L_from_env. 
rewrite dom_map_keys dom_filter_keys.
apply/mapP. econ. 
rewrite /filter_keys mem_filter.
instantiate (1:= schlT s p). ssa. ssa.
rewrite -H6.

rewrite /L_from_env. 
rewrite dom_map_keys dom_filter_keys.
case/mapP. 
ssa. subst. rewrite mem_filter in p0. ssa.
de x0. norm_eqs.
rewrite mem_filter. ssa.
Qed.

Lemma env_coherent12 : forall E Q, EQ_domLQ E Q -> env_coherent E Q -> exists L, env_coherent_as E Q L.
Proof.
move=> E Q.
rewrite /env_coherent.
move=> Heq [] Gs [].
move: Gs E Q Heq.
elim.

- case.
 * move=>Q. move/EQ_domLQ_nil=>->. intros. exists nil. apply/env_coherent_as_nil.
 * move=> a L Q. move/EQ_domLQ_cons'. ssa. subst.
   de x0. de q. move:(H1 s p). rewrite inE eqxx /=. move/(_ is_true_true)=>//.
- move=> a l IH E Q HQ. ssa.
  have: EQ_domLQ (filter_keys (predC (l_sess a.1)) E) (filter_keys (predC (q_sess a.1)) Q).
  move : HQ. clear.
  rewrite /EQ_domLQ. ssa.
  move: H. rewrite /only_schl dom_filter_keys all_filter /dom !all_map. 
  intros. apply/allP. intro. ssa. apply/implyP. ssa.
  apply (allP H) in H3. ssa.
  rewrite dom_filter_keys.
  apply filter_uniq=>//.
  rewrite dom_filter_keys.
  apply filter_uniq=>//.
  ssa. rewrite !dom_filter_keys !mem_filter. 
  f_equal. done.
  move=> HQ2. 
  eapply IH in HQ2. ssa.
  have: lookup (a::l) a.1 = Some a.2.
  rewrite lookup_cons_eq. done. done.
  move/H2. move=> HH.
  inv HH. ssa.
  exists ((map_keys (fun p => schlT a.1 p) x1)++x0).
  have: a.1 \notin dom l.
  move : H. rewrite /check_gs. ssa.
  move=> Hnot.
  remember H3 as HHH. clear HeqHHH.
  move/env_coherent_as_dom: H3 => Hall.
  con. inv HQ. con.
  rewrite /only_schl.  rewrite dom_cat all_cat. apply/andP. con. 
  rewrite dom_map_keys all_map. apply/allP. intro. ssa.
  inv HHH. ssa.

  ssa.
  destruct (eqVneq s a.1).
  subst.
  have: (L_from_env (filter_keys (l_sess a.1) (map_keys (schlT a.1) x1 ++ x0))) = (L_from_env (filter_keys (l_sess a.1) (map_keys (schlT a.1) x1))).
  rewrite filter_keys_cat.
  erewrite filter_keys_eq. erewrite filter_keys_predT.
  erewrite filter_keys_eq. erewrite filter_keys_pred0. 
  rewrite cats0 //=.
  intros. tunf. 
  de x2. 
apply Hall in H3. 
  rewrite dom_filter_keys mem_filter in H3. ssa.
  apply/eqP. intro. subst.
  move : H7. tunf. rewrite /l_sess eqxx.  done.
  ssa. rewrite dom_map_keys in H3. de (mapP H3). subst. ssa. rewrite eqxx //=.
  move=>->.
  have: (L_from_env (filter_keys (l_sess a.1) (map_keys (schlT a.1) x1))) = x1. 
  erewrite filter_keys_eq. erewrite filter_keys_predT. 
  rewrite /L_from_env map_keys2.
  erewrite map_keys_eq. erewrite map_keys_id. done.
  ssa.
  move=> x2. rewrite dom_map_keys. case/mapP. ssa. subst. ssa.
  rewrite eqxx//=.
  move=>->.

  rewrite /weak_coherent_as. con.  inv H4. ssa. subst.
  rewrite /coherent. exists a.2. exists x2. ssa.
  exists (fun p => x (a.1,p)). ssa.


- have: (L_from_env (filter_keys (l_sess s) (map_keys (schlT a.1) x1 ++ x0))) = L_from_env (filter_keys (l_sess s) x0).
  rewrite filter_keys_cat.  
  erewrite filter_keys_eq. erewrite filter_keys_pred0. simpl. done.
  ssa. 
tunf. rewrite /l_sess. de x2.
  rewrite dom_map_keys in H3. de (mapP H3). inv H8.
  rewrite neg_sym in i. rewrite (negbTE i). done. 

  move=>->.
  rewrite /env_coherent_as in HHH. ssa.

  move: (H8 s).
  rewrite !filter_keys2.
  erewrite filter_keys_eq.
  erewrite (@filter_keys_eq _ _ Q). eauto.
  ssa. tunf. rewrite /q_sess. de x2.
  de (eqVneq s0 s). subst. rewrite i. done.
  ssa. tunf. rewrite /l_sess. de x2.
  de (eqVneq s0 s). subst. rewrite i. done.

  instantiate (1:=x). con.
  inv H. ssa.
  rewrite /check_gs. con.
  ssa. apply:H3.
  apply in_dom in H4 as Hdom.
  de (eqVneq a.1 s). subst. rewrite Hdom in H5. done.
  rewrite lookup_cons_neq. done. done. done.
  con. move : H0. rewrite /coherent_gTypes. ssa.
  apply/H0. instantiate (1:=k).
  inv H. ssa. 
  de (eqVneq a.1 k). subst. 
  apply in_dom in H3 as Hdom.
  rewrite Hdom in H6. done.
  rewrite lookup_cons_neq. done. done. 

  con. ssa. rewrite dom_filter_keys mem_filter in H3. ssa.
  apply H1 in H5. rewrite inE in H5.
  de (orP H5). norm_eqs. move: H4. rewrite /predC. ssa. by rewrite eqxx in H4.

  ssa. 

  rewrite !filter_keys2.
  erewrite filter_keys_eq.
  erewrite (@filter_keys_eq _ _ Q). 
  apply H2.
  de (eqVneq a.1 s). subst. 
  apply in_dom in H3 as Hdom.
  inv H. ssa.
  rewrite Hdom in H6. done.
  rewrite lookup_cons_neq. done. done. 

  ssa. tunf. rewrite /q_sess. de x0.
  de (eqVneq s0 s). subst. 
  inv H. ssa. 
  apply in_dom in H3. apply/eqP. intro. subst. rewrite H3 in H7. done.
  ssa. tunf. rewrite /l_sess. de x0.
  de (eqVneq s0 s). subst. apply/eqP. intro. 
  inv H. ssa. apply in_dom in H3.
  rewrite H3 in H5. done.
Qed.


(*define new undup because it takes the first of repeating elements *)
(*instead of the last, allows to match against a::l in induction on *)
(*number of sessions*)
Fixpoint undup2 (A : eqType) (l : seq A) :=
match l with 
| nil => nil
| a::l' => a::(filter (fun x => x != a ) (undup2 l'))
end.

Fixpoint  sess_count (q : seq qkey) := 
match q with 
| nil => nil 
| (QKey s p)::q' => s::(filter (fun x => x != s) (sess_count q') )
end.

Lemma only_schl_filter : forall L p, only_schl L -> only_schl (filter_keys p L).
Proof.
move=> L p. rewrite /only_schl. rewrite dom_filter_keys all_filter.
ssa. apply/allP. intro. ssa. apply/implyP. ssa.
apply (allP H) in H0. ssa.
Qed.
Hint Resolve only_schl_filter.

Lemma  weak_coherent_as_nil : weak_coherent_as [::] [::] [::].
Proof.
con. apply/coherent_nil. exists (fun _ => nil). ssa.
Qed.

Lemma env_coherent_as1 : forall E Q L, EQ_domLQ E Q -> env_coherent_as E Q L -> env_coherent E Q.
Proof.
move=> E Q.
move Heq: (sess_count (dom Q))=>n.
move: n E Q Heq.
elim.
- move=> E Q Hcount L HQ Hco.
  de Q. apply EQ_domLQ_nil' in HQ. subst.
  apply/env_coherent_nil.
  de p. de q.
- move=> a l IH L Q Hcount L0 HQ Hco.

  have: sess_count (dom (filter_keys (predC (q_sess a))Q)) = l.  

  de Q.
  de p. de q. inv Hcount.
  ssa. rewrite /predC /= eqxx /=.
  rewrite dom_filter_keys.
  inv HQ. ssa. move: H4. clear.
  elim: Q a. done.
  ssa.
  de a. de q. 
  case_if. ssa. f_equal.
  rewrite H.
  rewrite -!filter_predI.
  apply/eq_in_filter.
  intro. ssa. lia. done.
  rewrite H//=.
  rewrite -!filter_predI.
  apply/eq_in_filter.
  intro. ssa. 
  de (eqVneq x a0). 
  de (eqVneq x s). subst.
  rewrite i in H2. done.
  intros. 
  have: env_coherent_as (filter_keys (predC (l_sess a)) L) (filter_keys (predC (q_sess a))Q) (filter_keys (predC (l_sess a)) L0).
  move:Hco.
  rewrite /env_coherent_as. ssa.
  intro.
  destruct (eqVneq s a). subst.
  rewrite !filter_keys2.
  erewrite filter_keys_eq. erewrite filter_keys_pred0. simpl.
  erewrite filter_keys_eq. erewrite filter_keys_pred0. simpl.
  erewrite filter_keys_eq. erewrite filter_keys_pred0. simpl.
  apply/weak_coherent_as_nil.
  ssa. tunf. lia.
  ssa. tunf. lia.
  ssa. tunf. lia.

  rewrite !filter_keys2.
  erewrite filter_keys_eq.
  erewrite (@filter_keys_eq _ _ Q).
  erewrite (@filter_keys_eq _ _ L0).
  apply (H1 s).
  ssa. tunf. rewrite /l_sess. de x0. 
  de (eqVneq s0 s). subst. rewrite i//.
  ssa. tunf. rewrite /q_sess. de x0. 
  de (eqVneq s0 s). subst. rewrite i//.
  ssa. tunf. rewrite /l_sess. de x0. 
  de (eqVneq s0 s). subst. rewrite i//.
  intros. apply IH in x0. 2:done.
  inv Hco. ssa.
  move: (H1 a).
  intros. clear H1. 
  rewrite /env_coherent.
  move: H H0 H2 x0 HQ. clear.
  intros.
  rewrite /weak_coherent_as in H2.
  ssa. inv H1. ssa.
  inv x0. ssa.


  exists ((a,x1)::(filter_keys (fun x => x != a) x3)).
  exists (fun y => let:(s,p) := y in if s==a then x p else x4 y).
  ssa.
  move: H8. rewrite /check_gs. ssa. intros.
  case_if. norm_eqs.
  rewrite lookup_cons_eq in H13. ssa. inv H13.
  apply/checkPath_fe2.

  inv H2.
  destruct (p \in dom (L_from_env (filter_keys (l_sess a) L0))) eqn:Heqn.
 apply H14.
  rewrite H5.
  apply/lookup_map3.
  3: { instantiate (1:=nat_of_ptcp p). de p. }
  rewrite /dom -map_comp. rewrite map_inj_uniq. done.
  intro. ssa. inv H16. 
  rewrite H5 in Heqn.
  rewrite /dom /L_from_env -map_comp in Heqn.
  de (mapP Heqn). subst. de x1.
  erewrite H15. done. rewrite Heqn. done. done.
  
  rewrite lookup_cons_neq in H13;ssa. 
  rewrite lookup_filter_keys_in in H13;ssa. lia. 
  rewrite neg_sym. lia.
  rewrite dom_filter_keys. rewrite mem_filter eqxx //=.
  rewrite dom_filter_keys. apply filter_uniq. done.
  move: H9. rewrite /coherent_gTypes. ssa.
  destruct (eqVneq a k). subst. rewrite lookup_cons_eq in H12. ssa. inv H12. 
  done. rewrite lookup_cons_neq in H12;ssa. 
  rewrite lookup_filter_keys_in in H12;ssa.
  eauto. rewrite neg_sym. done.
  ssa.
  destruct (eqVneq s a). subst. done.
  rewrite inE. apply/orP. right.
  rewrite dom_filter_keys mem_filter i. ssa.
  apply:H10. rewrite dom_filter_keys mem_filter /predC /q_sess i. ssa. eauto.
  ssa.
  destruct (eqVneq a s). subst. rewrite lookup_cons_eq in H12.
  ssa. inv H12.
  rewrite /weak_coherent_exists.
  exists ((L_from_env (filter_keys (l_sess s) L0))). con.
  rewrite /coherent_exists. exists x2. ssa. con.  done. done. done.
  rewrite lookup_cons_neq in H12;ssa.
  rewrite lookup_filter_keys_in in H12;ssa.
  apply H11 in H12.
  move:H12. rewrite !filter_keys2.
  erewrite filter_keys_eq. 
  erewrite (@filter_keys_eq _ _ Q). eauto.
  ssa. tunf. rewrite /q_sess. de x5.
  de (eqVneq s0 s). subst. rewrite neg_sym in i. done.
  ssa. tunf. rewrite /l_sess. de x5.
  de (eqVneq s0 s). subst. rewrite neg_sym i. done.
  rewrite neg_sym. done.


  move : HQ. rewrite /EQ_domLQ. ssa.
  rewrite dom_filter_keys. apply filter_uniq. done.
  rewrite dom_filter_keys. apply filter_uniq. done.
  ssa. rewrite !dom_filter_keys !mem_filter. tunf.
  rewrite /l_sess /q_sess. f_equal. eauto.
Qed.

Lemma lookup_L_from_env : forall (E : l_env) s p T, 
lookup (filter_keys (l_sess s) E) (schlT s p) = Some T ->
lookup (L_from_env (filter_keys (l_sess s) E)) p = Some T.
Proof.
elim;ssa. de a.
move: H0. case_if.
destruct (eqVneq l0 (schlT s p)). subst.
rewrite lookup_cons_eq.  
case. move=>->. ssa.
rewrite lookup_cons_eq. done. done. done.
rewrite lookup_cons_neq.
move/H=>HH.
ssa. de l0. norm_eqs.
rewrite lookup_cons_neq. done. 
ssa. apply/eqP. intro. subst. rewrite eqxx in i. done.
ssa. 
move/H=>->. done.
Qed.

Lemma lookup_Q_from_env : forall (E : q_env) s p T, 
lookup (filter_keys (q_sess s) E) (QKey s p) = Some T ->
lookup (Q_from_env (filter_keys (q_sess s) E)) p = Some T.
Proof.
elim;ssa. de a.
move: H0. case_if.
destruct (eqVneq q (QKey s p)). subst.
rewrite lookup_cons_eq.  
case. move=>->. ssa.
rewrite lookup_cons_eq. done. done. done.
rewrite lookup_cons_neq.
move/H=>HH.
ssa. de q. norm_eqs.
rewrite lookup_cons_neq. done. 
ssa. apply/eqP. intro. subst. rewrite eqxx in i. done.
ssa. 
move/H=>->. done.
Qed.


Lemma env_coherent_as_eq : forall E Q L, env_coherent_as E Q L -> EQ_same E E.
Proof.
intros. 
rewrite /EQ_same. ssa.
ssa.
inv H. ssa.
de p. apply in_dom in H0. apply (allP H2) in H0. done.
move: (H4 s).
intros.
apply weak_coherent_as_eq in H5.
inv H5. eapply H7.
instantiate (1:= p). 
apply/lookup_L_from_env. 
apply/lookup_filter. ssa. done.
apply/lookup_L_from_env. 
apply/lookup_filter. ssa. done.
Qed.

Lemma L_from_env_update : forall (E : l_env) s p T, 
L_from_env (update (filter_keys (l_sess s) E) (schlT s p) T) =
update (L_from_env (filter_keys (l_sess s) E)) p T.
Proof.
elim;ssa. case_if. ssa.
de a. de l0. norm_eqs. case_if. ssa. move/eqP : H0. case.
move=>->. rewrite eqxx. f_equal. done.
ssa. move/eqP : H0. intro. case_if. norm_eqs. done.
f_equal. done.
done.
Qed.

Lemma Q_from_env_update : forall (E : q_env) s p T, 
Q_from_env (update (filter_keys (q_sess s) E) (QKey s p) T) =
update (Q_from_env (filter_keys (q_sess s) E)) p T.
Proof.
elim;ssa. case_if. ssa.
de a. de q. norm_eqs. case_if. ssa. move/eqP : H0. case.
move=>->. rewrite eqxx. f_equal. done.
ssa. move/eqP : H0. intro. case_if. norm_eqs. done.
f_equal. done.
done.
Qed.


Lemma LQ_red12 : forall E Q E' Q', LQ_red E Q E' Q' -> 
E = E' /\ Q = Q' \/
exists s, LQ_red2 (L_from_env (filter_keys (l_sess s) E)) (Q_from_env (filter_keys (q_sess s) Q))
     (L_from_env (filter_keys (l_sess s) E')) (Q_from_env (filter_keys (q_sess s) Q'))
  /\
(filter_keys (predC (l_sess s)) E) = (filter_keys (predC (l_sess s)) E') /\
(filter_keys (predC (q_sess s)) Q) = (filter_keys (predC (q_sess s)) Q').
Proof.
intros. inv H. 
- left. ssa.
- right. exists s. ssa.
  apply:LQ2'.
  apply/lookup_L_from_env. apply/lookup_filter. ssa. eauto.
  apply/lookup_Q_from_env. apply/lookup_filter. ssa. eauto. eauto.
  rewrite filter_keys_update.
  rewrite L_from_env_update. done.
  rewrite filter_keys_update.
  rewrite Q_from_env_update. done.
  rewrite filter_keys_update_not. done. tunf. ssa. by  apply/eqP. 
  rewrite filter_keys_update_not. done. tunf. ssa. by  apply/eqP. 
- right. exists s. ssa.
  apply:LQ3'. 
  2: { apply/lookup_L_from_env. apply/lookup_filter. ssa. eauto. }
  2: { apply/lookup_Q_from_env. apply/lookup_filter. ssa. eauto. }
  done. eauto.
  rewrite filter_keys_update.
  rewrite L_from_env_update. done.
  rewrite filter_keys_update.
  rewrite Q_from_env_update. done.
  rewrite filter_keys_update_not. done. tunf. ssa. by  apply/eqP. 
  rewrite filter_keys_update_not. done. tunf. ssa. by  apply/eqP. 
Qed.

Lemma L_from_env_seq_update : forall E' x E,
L_from_env
    (seq_update (filter_keys (l_sess x) E) (map_keys (schlT x) E')) =  
seq_update (L_from_env (filter_keys (l_sess x) E)) E'.
Proof.
elim;ssa. de a.
have: (seq_update (filter_keys (l_sess x) E) (map_keys (schlT x) l)) = 
filter_keys (l_sess x) (seq_update (filter_keys (l_sess x) E) (map_keys (schlT x) l)).
symmetry.
erewrite filter_keys_eq. 
erewrite filter_keys_predT. done.
ssa. rewrite dom_seq_update dom_filter_keys mem_filter in H0. ssa.
move=>->.
rewrite L_from_env_update. 
erewrite filter_keys_eq. 
erewrite filter_keys_predT. 
rewrite H. done.
ssa. rewrite dom_seq_update dom_filter_keys mem_filter in H0. ssa.
Qed.

Lemma EnvStep3_dom : forall L X Y, EnvStep3 L X Y -> dom L = dom Y.
Proof.
intros. inv H.
Qed.

Lemma L_from_env_map_keys : forall E s, L_from_env (map_keys (schlT s) E) = E.
Proof.
elim;ssa. de a. f_equal. done.
Qed.

Lemma weak_coherent_dom_eq : forall L Q E, weak_coherent_as L Q E -> dom L = dom E.
Proof.
intros.
inv H. ssa. inv H2. rewrite dom_makeLs. done.
Qed.


Lemma  dom_L_from_env : forall x p myCo,  (schlT x p) \in dom myCo <-> (p \in dom (L_from_env (filter_keys (l_sess x) myCo))).
Proof.      
intros.
split. intros.
move: H =>H11.
de (mapP H11).
apply/mapP. econ. apply/mapP. econ. apply/in_filter_keys2. eauto. move: H0 =>H13. rewrite -H13. ssa. econ. ssa. de x0. subst. 
done. case/mapP. move=> x2. case/mapP. intros. subst. de x0.
apply in_filter_keys in p0. ssa. de s. norm_eqs. 
apply/mapP. econ. eauto. done.
Qed.

Lemma lookup_map_aux3 : forall (A B C: eqType) (l : seq (A * B)) (k : A) (f : A -> C), injective f -> 
                                                                lookup l k = lookup (map_keys f l) (f k).
Proof. 
move => A B. intros. move : H. 
rewrite /lookup. elim : l;ssa. 
rifliad. norm_eqs. norm_eqs. apply H0 in H2. subst. rewrite eqxx in H1. done. 
eauto. 
Qed.


Lemma weak_coherent_as_lInvPred : forall E Q L k T, weak_coherent_as E Q L ->  lookup E k = Some T -> lInvPred T.
Proof.
intros. inv H. ssa. inv H3.
inv H1. ssa. subst.
apply in_pair in H0. rewrite /makeLs -map_comp in H0. de (mapP H0). inv H8.
apply/lInvPred_makeL.
inv H2. ssa.
apply H9.
eapply lookup_map3. rewrite /dom -map_comp. rewrite map_inj_uniq.
done. intro. ssa. inv H11. 2:econ.
done.
apply -> lInvPred_iff. 
apply/gInvPred_proj.
inv H4. ssa.
move: (H13 (Ptcp 0)).
ssa. apply/gInvPred_iff. apply/Project_gtree. eauto.
Qed.

Lemma weak_coherent_as_lInvPred2 : forall E Q L k T, weak_coherent_as E Q L ->  lookup L k = Some T -> lInvPred T.
Proof.
intros. inv H. ssa. inv H3.
inv H1. ssa. subst.
apply in_pair in H0. de (mapP H0). inv H8.
apply -> lInvPred_iff. 
apply/gInvPred_proj.
inv H4. ssa.
move: (H13 (Ptcp 0)).
ssa. apply/gInvPred_iff. apply/Project_gtree. eauto.
Qed.

Lemma env_coherent_as_lInvPred : forall E Q L k T, only_schl E -> env_coherent_as E Q L ->  lookup E k = Some T -> lInvPred T.
Proof.
intros.
apply in_dom in H1 as HH. 
de k. apply (allP H) in HH. done.
inv H0. ssa. move: (H4 s).
intros. apply/weak_coherent_as_lInvPred. eauto. 
erewrite lookup_L_from_env. eauto. 
erewrite lookup_filter. eauto. 2:eauto. ssa.
Qed.

Lemma env_coherent_as_lInvPred2 : forall E Q L k T (Hdom : dom E = dom L), only_schl E -> env_coherent_as E Q L ->  lookup L k = Some T -> lInvPred T.
Proof.
intros.
apply in_dom in H1 as HH. 
de k. rewrite -Hdom in HH.
apply (allP H) in HH. done.
inv H0. ssa. move: (H4 s).
intros. apply/weak_coherent_as_lInvPred2. eauto. 
erewrite lookup_L_from_env. eauto. 
erewrite lookup_filter. eauto. 2:eauto. ssa.
Qed.

Lemma seq_update_same : forall (E' E : l_env), uniq (dom E) ->  (forall lk T, (lk,T) \in E' -> lookup E lk = Some T) -> seq_update E E' = E.
Proof.
elim;ssa.
de a.
rewrite update_same. apply H. 
intros. apply H0. 
intros. apply H1.
rewrite inE H2 //=. lia.
rewrite H. apply H1. rewrite inE eqxx. done.
intros. apply H0. 
intros. apply H1.
rewrite inE H2 //=. lia.
rewrite dom_seq_update. done.
Qed.

Lemma lookup_L_from_env2 : forall (E : l_env) s p T, 
lookup (L_from_env (filter_keys (l_sess s) E)) p = Some T ->
lookup (filter_keys (l_sess s) E) (schlT s p) = Some T.
Proof.
elim;ssa. de a.
move: H0. case_if.
ssa. de l0. norm_eqs.
destruct (eqVneq p0 p). subst.
move: H1. rewrite !lookup_cons_eq;ssa.  
move: H1. rewrite !lookup_cons_neq;ssa.
apply/eqP. intro. inv H0.
by rewrite eqxx in i. 
ssa. 
Qed.

Lemma inj_schlT : forall x, injective (schlT x).
Proof.
intro. intro. ssa. inv H.
Qed.
Hint Resolve inj_schlT.

Lemma EnvStep34 : forall L l L' x (Honly : only_schl (filter_keys (l_sess x) L)) (HInv : forall lk T, lookup L lk = Some T -> lInvPred T),
 EnvStep3 (L_from_env (filter_keys (l_sess x) L)) l L' ->
 EnvStep4 L l (seq_update L (map_keys (schlT x) L')).
Proof. 
intros.
inv H.
econ.

- erewrite <- Congruence.lookup_filter3.
  apply lookup_L_from_env2 in H0.
  erewrite H0. eauto. ssa.
- erewrite <- Congruence.lookup_filter3.
  apply lookup_L_from_env2 in H1.
  erewrite H1. eauto. ssa.
- erewrite <- Congruence.lookup_filter3.
  rewrite filter_keys_seq_update.
  apply lookup_L_from_env2 in H0.
  apply lookup_seq_update_in.
  rewrite dom_filter_keys. 
  instantiate (1:= l_sess x).
  rewrite mem_filter. ssa.
  apply in_dom in H0. rewrite dom_filter_keys mem_filter in H0.
  ssa.
  erewrite <- lookup_map_aux3. eauto.
  intro. ssa. inv H8. ssa.
- erewrite <- Congruence.lookup_filter3.
  rewrite filter_keys_seq_update.
  apply lookup_L_from_env2 in H1.
  apply lookup_seq_update_in.
  rewrite dom_filter_keys. 
  instantiate (1:= l_sess x).
  rewrite mem_filter. ssa.
  apply in_dom in H1. rewrite dom_filter_keys mem_filter in H1.
  ssa.
  erewrite <- lookup_map_aux3. eauto.
  intro. ssa. inv H8. ssa.
- done. 
- done. 
- rewrite dom_seq_update //.
- move=>p T2 T3 Hp0 Hp1. ssa. 
  destruct (p \in dom (map_keys (schlT x) L')) eqn:Heqn.
  rewrite dom_map_keys in Heqn. de (mapP Heqn). subst.
  apply lookup_seq_update_in2 in H9.
  rewrite <- lookup_map_aux3 in H9;ssa.
  eapply H7.
  instantiate (1:= x0). apply/eqP. intro. subst. 
  by rewrite eqxx in Hp0.
  apply/eqP. intro. subst. by rewrite eqxx in Hp1.
  apply lookup_L_from_env.
  apply lookup_filter. ssa. done. done.
  rewrite dom_map_keys. apply/mapP. econ. eauto. done.
  rewrite dom_map_keys in Heqn. 
  rewrite lookup_seq_update in H9.
  rewrite H8 in H9. inv H9.
  apply/EQ2_refl.
  eauto.
  rewrite dom_map_keys. apply/negP.
  intro. de (mapP H9). subst. move/negP : Heqn.
  intro. apply Heqn. 
  apply/mapP. econ. eauto. done.
Qed.

Lemma lInvPred_pres2 : forall T l T', lInvPred T -> Estep2 T l T' -> lInvPred T'.
Proof.
intros. inv H0. 
punfold H. inv H. inv H1. inv H3.
punfold H. inv H. inv H2. 
move/ForallP : H4.
move/inP : H1. move=>HH. move/(_ _ HH).
case;ssa.
Qed.

Lemma lInvPred_not_rec :  forall T, lInvPred T -> ~~ is_erec (fe T).
Proof.
intros. punfold H. inv H. inv H0.
Qed.

Lemma env_not_rec_pres : forall E Q E' Q' (Hinv : forall lk T, lookup E lk = Some T -> lInvPred T), env_not_rec E ->  LQ_red E Q E' Q' -> env_not_rec E'.
Proof.
intros. inv H0.
move: H. rewrite /env_not_rec.
intros. apply/allP.
intro. ssa. apply in_update in H4 as Hor. de Hor.
subst. asimpl. ssa.
apply/lInvPred_not_rec.
apply/lInvPred_pres2. 2:eauto. eauto.
asimpl. apply (allP H) in H5. done.

move: H. rewrite /env_not_rec.
intros. apply/allP.
intro. ssa. asimpl.
apply in_update in H5 as Hor. de Hor.
subst. asimpl. ssa.
apply/lInvPred_not_rec.
apply/lInvPred_pres2. 2:eauto. eauto.
asimpl. apply (allP H) in H6. done.
Qed.


Lemma weak_coherent_as_env_not_rec : forall E Q L,  weak_coherent_as E Q L -> all (fun x => ~~ is_erec x.2) E.
Proof.
intros.
apply/allP. intro.
de x.
inv H. ssa. inv H3.
de (mapP H0). inv H5.
apply/not_erec_makeL.
inv H1. ssa. subst.
de (mapP H4). subst.
ssa.
apply:lcontractive_full_eunf.
apply:proj_lcontractive.
Qed.

Lemma env_coherence_pres_as  : forall myCo E Q E' Q' (Hdom' : dom E = dom myCo) (Hun' : uniq (dom E)) (Hnot : env_not_rec E), LQ_red E Q E' Q' -> env_coherent_as E Q myCo -> 
exists E'' myCo', env_coherent_as E'' Q' myCo' /\  EQ_same E'' E' /\ dom (E'') = dom E' /\ env_not_rec E'' /\ (myCo = myCo' \/ exists l, EnvStep4 myCo l myCo').
Proof.
intros.
remember H as Henv''. clear HeqHenv''.
apply LQ_red12 in H.
de H.
subst.
econ. econ. con. eauto. con. apply/env_coherent_as_eq. eauto. auto.
inv H0. ssa.
apply env_not_rec_pres in Henv'' as Hnot';ssa.

move: (H5 x).
intros.
eapply coherence_pres_as in H. 2:eauto.
ssa.


have: dom (L_from_env (filter_keys (l_sess x) myCo)) = dom x1.
de H8. rewrite H8 //.
apply EnvStep3_dom in H8. rewrite H8. done.
move=>Hdom.
exists (seq_update E (map_keys (fun p => schlT x p) x0)). 
exists (seq_update myCo (map_keys (fun p => schlT x p) x1)). 
ssa. 
- rewrite /env_coherent_as. ssa. 
 * rewrite /only_schl. rewrite dom_seq_update. done.
 * rewrite /only_schl. rewrite dom_seq_update. done.
 * move=>s. 
   rewrite filter_keys_seq_update.
   destruct (eqVneq s x).
   ** subst. 
      rewrite seq_update_dom_eq.
      rewrite filter_keys_seq_update.
      rewrite seq_update_dom_eq.
      rewrite !L_from_env_map_keys. done.
      rewrite dom_map_keys map_inj_uniq //=.
      inv H. ssa. inv H9. ssa. subst. 
      rewrite /dom -map_comp. rewrite map_inj_uniq. done.
      intro. ssa. inv H13.
      rewrite dom_map_keys -Hdom. 
      rewrite /dom -!map_comp.
      apply/eq_in_map.
      intro. ssa.
      apply in_filter_keys in H9. 
      ssa. de x2. de s. norm_eqs. done.
      inv H. ssa. inv H11. inv H9. ssa. subst. 
      rewrite /makeLs -map_comp dom_map_keys /dom -!map_comp.
      rewrite map_inj_uniq. done.
      intro. ssa. inv H13. 
      apply weak_coherent_dom_eq in H. 
      rewrite dom_map_keys. 
      rewrite H -Hdom dom_filter_keys Hdom'. 
      clear. elim : myCo. done.
      ssa. de a. case_if. ssa. de s. norm_eqs. 
      f_equal. done. done.
      rewrite !filter_keys_seq_update.
      rewrite !seq_update_notin.
      have: (filter_keys (q_sess s) Q') = (filter_keys (q_sess s) (filter_keys (predC (q_sess x)) Q')).
      rewrite filter_keys2.
      apply/filter_keys_eq. intro. ssa. tunf. de x2.
      de (eqVneq s0 s). subst. rewrite i. done.
      move=>->. rewrite -H2.
      rewrite filter_keys2. erewrite (@filter_keys_eq _ _ Q). eauto.
      intros. tunf. de x2. de (eqVneq s0 s). subst. rewrite i. done.
      move=>x2. rewrite dom_map_keys. case/mapP. ssa. subst.
      rewrite dom_filter_keys mem_filter negb_and. ssa. rewrite neg_sym i. auto.
      move=>x2. rewrite dom_map_keys. case/mapP. ssa. subst.
      rewrite dom_filter_keys mem_filter negb_and. ssa. rewrite neg_sym i. auto.
      rewrite /EQ_same. ssa.
      rewrite dom_seq_update. 
      inv H7. ssa.
      destruct (l_sess x k) eqn:Heqn.
      rewrite Hdom'.
      de k. norm_eqs. 
      rewrite (@dom_L_from_env x p). 
      rewrite Hdom. 
      apply weak_coherent_dom_eq in H.
      rewrite -H.
      rewrite H9.
      rewrite -dom_L_from_env. done.
      have : (k \in dom E) <-> (k \in dom (filter_keys (predC (l_sess x)) E)).
      rewrite dom_filter_keys mem_filter. tunf. rewrite Heqn /=. done.
      move=>->. rewrite H1.

      have : (k \in dom E') <-> (k \in dom (filter_keys (predC (l_sess x)) E')).
      rewrite dom_filter_keys mem_filter. tunf. rewrite Heqn /=. done.
      move=>->. done.
      
      intros.
      destruct (l_sess x p) eqn:Heqn.
      inv H7. 
      de p. norm_eqs.
      ssa. eapply H12.
      instantiate (1:=p). 
      apply lookup_seq_update_in2 in H9.
      rewrite -lookup_map_aux3 in H9. done.
      intro. ssa. inv H9.
      rewrite dom_map_keys. apply/mapP. econ. 2:econ.
      rewrite H11.
      apply in_dom in H10.
      rewrite -dom_L_from_env. done.
      erewrite <- lookup_L_from_env. eauto.
      rewrite lookup_filter_keys_in;ssa.
      rewrite lookup_seq_update in H9.
      erewrite <- lookup_filter_keys_in in H9,H10.
      erewrite <- H1 in H10.
      erewrite H10 in H9. inv H9.
      apply/EQ2_refl.
      apply:env_coherent_as_lInvPred. 2:eauto. done.
      rewrite lookup_filter_keys_in in H10. eauto. tunf. rewrite Heqn. done.
      tunf. rewrite Heqn. done.
      tunf. rewrite Heqn. done.
      rewrite dom_map_keys.
      apply/negP. intro. de (mapP H9). subst. ssa. rewrite eqxx //= in Heqn.
      rewrite dom_seq_update.
      apply pres_dom_same in Henv''.
      ssa.
      apply/allP. intro. ssa. asimpl.
      de x2.
      apply uniq_in_pair in H9.
      destruct (s \in dom (map_keys (schlT x) x0)) eqn:Heqn.
      rewrite dom_map_keys in Heqn. de (mapP Heqn). subst.
      apply lookup_seq_update_in2 in H9.
      rewrite -lookup_map_aux3 in H9.
      apply weak_coherent_as_env_not_rec in H.
      apply in_pair in H9.
      apply (allP H) in H9. done.
      done. rewrite dom_map_keys. apply/mapP. econ. eauto. done.
      rewrite dom_map_keys in Heqn. 
      rewrite lookup_seq_update in H9.
      apply in_pair in H9.
      apply (allP Hnot) in H9. done.
      rewrite dom_map_keys. rewrite Heqn. done.
      rewrite dom_seq_update. done.
      

     de H8. left. subst. 
     rewrite seq_update_same. done. rewrite -Hdom'. 
done.
     
     intros.
     apply uniq_in_pair in H8.
     have: (map_keys (schlT x) (L_from_env (filter_keys (l_sess x) myCo))) =  ((filter_keys (l_sess x) myCo)).
     rewrite /map_keys /L_from_env -map_comp.
     erewrite map_eq.
     erewrite map_id. done.
     intro. ssa. apply in_filter_keys in H9. ssa. de x1. de s. norm_eqs. done.
     move=>HH. rewrite HH in H8.
     apply lookup_filter2 in H8. ssa.
     rewrite dom_map_keys. 
     rewrite map_inj_uniq.
     rewrite /L_from_env dom_map_keys dom_filter_keys.
     rewrite map_inj_in_uniq.
     apply filter_uniq. rewrite -Hdom'. 
     done.
     

     intro. ssa. 
     rewrite !mem_filter in H9,H10. ssa. de x1. de y. norm_eqs. done.
     intro. ssa. inv H9.
     right.
     exists x2.
     apply:EnvStep34. 
     apply only_schl_filter. done.
     intros.
     apply:env_coherent_as_lInvPred2. 3:eauto. 3:eauto. done. done.
     done.
apply:env_coherent_as_lInvPred.
3:eauto. done. 
eauto.
Qed.

Definition side_conds3  Ds Ps Ms P E Q L := coherentG_env Ms /\  env_not_rec E /\  env_coherent_as E Q L /\ both_closed P /\ only_schl E /\ only_var_val Ms /\ uniq (dom Q) /\ uniq (dom E) /\ EQ_domLQ E Q /\ DefTyping Ds Ps /\ envP E uniq_labels /\ good_defs Ds /\ dom E = dom L.

Inductive env_red : l_env -> q_env ->  l_env -> q_env -> Prop :=
| ER1 E Q E' s p c v Q' T T' l : lookup E (schlT s p) = Some T  ->
                                 lookup Q (QKey s p) = Some l  ->
                                 Estep2 T (Sd,c,v) T' ->
                                 E' = update E (schlT s p) (fe T') ->
                                 Q' = update Q (QKey s p) (l++[::(c,v)]) ->
                                  env_red E Q E' Q'
| ER2 E Q E' s p p' c v Q' T T' l l0 : all (fun x => x.1 != c) l0 ->
                                    lookup E (schlT s p) = Some T ->
                                    lookup Q (QKey s p') = Some  (l0++(c,v)::l) ->
                                    Estep2 T (Rd,c,v) T' ->
                                    E' = update E (schlT s p) (fe T') -> 
                                    Q' = update Q (QKey s p') (l0++l) ->
                                    env_red E Q E' Q'.


Lemma EQ_same_trans : forall (E0 E1 E2 : l_env), EQ_same E0 E1 -> EQ_same E1 E2 -> EQ_same E0 E2.
Proof.
intros. inv H. inv H0.
rewrite /EQ_same. ssa.
intros. rewrite H1. done.
intros.
apply in_dom in H5 as Hdom.
rewrite H1 in Hdom.
apply in_dom_exists in Hdom.
ssa. eapply H2 in H5. 2:eauto.
eapply H4 in H7. 2:eauto.
apply/EQ2_trans. eauto. done.
Qed.

Lemma subject_reduction_final : forall D P P' Ms Ds E Q C L, Sem D P P' -> side_conds3 Ds D Ms P E Q L ->  OFT Ms Ds P E Q C ->  
exists E' Q' L', OFT Ms Ds P' E' Q' C /\ side_conds3 Ds D Ms P' E' Q' L' /\
 (L = L' \/ exists l, EnvStep4 L l L'). 
Proof.
intros.
eapply subject_reduction_full in H1;eauto.
move : H1.
move=>[]E' []E'' []Q' []HLQ []HEQ []HOFT Hside.
move: H0.
rewrite /side_conds3.
ssa.
eapply env_coherence_pres_as in H2.
4:eauto.
move: H2 => []E''' []myCo'.
ssa.
move : H15 H16 => Hnot' H15.
econ. econ. econ. con.
2:econ.
2:econ.
3:econ.
4:econ.
5:econ.
4:eauto. 
2:done.
apply:OFT_EQ_same. 6:eauto.
inv Hside;ssa.
rewrite H14.
apply pres_dom_same in HLQ. ssa. erewrite <- H16. ssa.
all:try solve [inv Hside;ssa].

apply/EQ_same_trans. apply/EQ_same_sym. eauto.
apply/EQ_same_sym. done.

move : Hside. rewrite /side_conds2;ssa.
rewrite /only_schl H14.
apply/allP. 
intro. ssa. 
inv HEQ.
ssa. rewrite H29 in H28.
apply (allP H20) in H28. done.
rewrite H14.
apply pres_dom_same in HLQ. ssa. 
rewrite -H28. done.
move: H24. rewrite /sub_domLQ /EQ_domLQ.
ssa. 
apply pres_dom_same in HLQ. ssa. 
rewrite /only_schl. rewrite H14.
apply/allP. intro. ssa.
inv  HEQ. rewrite H31 in H30. apply (allP H20) in H30. done.
rewrite H14.
apply pres_dom_same in HLQ. ssa. 
rewrite -H28. done.
move: H8.
rewrite /EQ_domLQ. ssa.
rewrite H14.
apply pres_dom_same in HLQ.
ssa. rewrite -H32 -H31. done.
rewrite /envP. intro. ssa.
inv H13.
apply in_dom in H28 as Hdom.
rewrite H29 in Hdom.
inv HEQ. 
move: Hdom. move/[dup]. move=>Hdom0 Hdom1.
rewrite H31 in Hdom1.
apply in_dom_exists in Hdom1.
ssa. 
apply in_dom_exists in Hdom0.
ssa.
have : EQ2 x T.
apply/EQ2_sym. 
apply/EQ2_trans. 
apply:H30. eauto. eauto.
apply:H32. eauto. done.
intros.
apply:labels_preserve.  eauto.
eapply H26. eauto.
rewrite H14.
apply pres_dom_same in HLQ.
ssa. rewrite -H28.
rewrite H12. inv H15.
ssa. inv H30.
move: H0. rewrite /side_conds3 /side_conds2;ssa.
apply env_coherent_as1 in H3. done. done.
move: H9. rewrite /EQ_domLQ /sub_domLQ.
ssa. rewrite -H17 H14 //.
Qed.


Lemma subject_reduction_empty : forall D P P' Ms Ds, Sem D P P' -> side_conds3 Ds D Ms P nil nil nil ->  OFT Ms Ds P nil nil nil ->  
OFT Ms Ds P' nil nil nil /\ side_conds3 Ds D Ms P' nil nil nil. 
Proof.
intros.
eapply subject_reduction_final in H;eauto.
ssa. de H3. subst.
move: H2. rewrite /side_conds3. ssa.
de x.
move : H10. rewrite /EQ_domLQ. ssa. de x0.
exfalso. 
de p. de q.
move: (H17 s p).
rewrite !inE eqxx /= in_nil. done.
inv H3.

ssa. de H3. subst.
move: H2. rewrite /side_conds3. ssa.
de x.
move : H10. rewrite /EQ_domLQ. ssa. de x0.
exfalso. 
de p. de q.
move: (H17 s p).
rewrite !inE eqxx /= in_nil. done.
inv H3.
Qed.

