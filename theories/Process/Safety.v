
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

Definition not_base (P : process) := 
match P with 
| Par _ _ => true 
| ResCh _ => true 
| ResVal _ => true 
| _ => false 
end.

Inductive Error : process -> Prop := 
 | VrVr s p q i P0 P1       : Error (Par (ValRec (schlT s p) i P0) (ValRec (schlT s q) i P1))
 | VrLr s p q i P0 Ps       : Error (Par (ValRec (schlT s p) i P0) (LabelBr (schlT s q) i Ps))
 | VrSr s p q i P0 P1       : Error (Par (ValRec (schlT s p) i P0) (SessRec (schlT s q) i P1))

 | LrLr s p q i Ps Ps'      : Error (Par (LabelBr (schlT s p) i Ps) (LabelBr (schlT s q) i Ps'))
 | LrSr s p q i Ps P        : Error (Par (LabelBr (schlT s p) i Ps) (SessRec (schlT s q) i P))

 | SrSr s p q i P0 P1       : Error (Par (SessRec (schlT s p) i P0) (SessRec (schlT s q) i P1))

 | VsVs s p q i e0 e1 P0 P1 : Error (Par (ValSend (schlT s p) i e0 P0) (ValSend (schlT s q) i e1 P1))
 | VsLs s p q i e l P0 Ps   : Error (Par (ValSend (schlT s p) i e P0) (LabelSel (schlT s q) i l Ps))
 | VsSs s p q i e l P0 P1   : Error (Par (ValSend (schlT s p) i e P0) (SessDel (schlT s q) i l P1))

 | LsLs s p q i l0 l1 P0 P1 : Error (Par (LabelSel (schlT s p) i l0 P0) (LabelSel (schlT s q) i l1 P1))
 | LsSs s p q i l0 s' Ps P  : Error (Par (LabelSel (schlT s p) i l0 Ps) (SessDel (schlT s q) i s' P))

 | SsSs s p q i s0 s1 P0 P1 : Error (Par (SessDel (schlT s p) i s0 P0) (SessDel (schlT s q) i s1 P1))

 | VrQl c p p' i n P qs : Error (Par (ValRec (schlT c p) i P) (MsgQ (schliT c i) ((msgT (labelM n) p')::qs)))
 | VrQs c p p' i s P qs : Error (Par (ValRec (schlT c p) i P) (MsgQ (schliT c i) ((msgT (schM s) p')::qs)))


 | LrQl c p p' i Ps v qs : Error (Par (LabelBr (schlT c p) i Ps) (MsgQ (schliT c i) ((msgT (valM v) p')::qs)))
 | LrQs c p p' i Ps s qs : Error (Par (LabelBr (schlT c p) i Ps) (MsgQ (schliT c i) ((msgT (schM s) p')::qs)))


 | SrQl c p i P v p' qs : Error (Par (SessRec (schlT c p) i P) (MsgQ (schliT c i) ((msgT (valM v) p')::qs)))
 | SrQs c p i P n p' qs : Error (Par (SessRec (schlT c p) i P) (MsgQ (schliT c i) ((msgT (labelM n) p')::qs)))

 | QQ c i qs qs' : Error (Par (MsgQ (schliT c i) qs) (MsgQ (schliT c i) qs'))

 | E_ResCh P : Error P -> Error (ResCh P)
 | E_ResVal P : Error P -> Error (ResVal P)
 | E_Par P P' : Error P -> Error (Par P P'). 

Definition Error_struct P := exists P', Cong P P' /\ Error P'.

Fixpoint error (P : process) := 
match P with 
| (Par (ValRec (schlT s p) i P0) (ValRec (schlT s' q) i' P1)) => (s,i) == (s',i')
| (Par (ValRec (schlT s p) i P0) (LabelBr (schlT s' q) i' Ps)) => (s,i) == (s',i')
| (Par (ValRec (schlT s p) i P0) (SessRec (schlT s' q) i' P1)) => (s,i) == (s',i')
| (Par (LabelBr (schlT s p) i Ps) (LabelBr (schlT s' q) i' Ps')) => (s,i) == (s',i')
| (Par (LabelBr (schlT s p) i Ps) (SessRec (schlT s' q) i' P)) => (s,i) == (s',i')
| (Par (SessRec (schlT s p) i P0) (SessRec (schlT s' q) i' P1)) => (s,i) == (s',i')
| (Par (ValSend (schlT s p) i e0 P0) (ValSend (schlT s' q) i' e1 P1)) => (s,i) == (s',i')
| (Par (ValSend (schlT s p) i e P0) (LabelSel (schlT s' q) i' l Ps)) => (s,i) == (s',i')
| (Par (ValSend (schlT s p) i e P0) (SessDel (schlT s' q) i' l P1)) => (s,i) == (s',i')
| (Par (LabelSel (schlT s p) i l0 P0) (LabelSel (schlT s' q) i' l1 P1)) => (s,i) == (s',i')
| (Par (LabelSel (schlT s p) i l0 Ps) (SessDel (schlT s' q) i' s'' P)) => (s,i) == (s',i')
| (Par (SessDel (schlT s p) i s0 P0) (SessDel (schlT s' q) i' s1 P1)) => (s,i) == (s',i')
| (Par (ValRec (schlT c p) i P) (MsgQ (schliT c' i') ((msgT (labelM n) p')::qs))) => (c,i) == (c',i')
| (Par (ValRec (schlT c p) i P) (MsgQ (schliT c' i') ((msgT (schM s) p')::qs))) => (c,i) == (c',i')
| (Par (LabelBr (schlT c p) i Ps) (MsgQ (schliT c' i') ((msgT (valM v) p')::qs))) => (c,i) == (c',i')
| (Par (LabelBr (schlT c p) i Ps) (MsgQ (schliT c' i') ((msgT (schM s) p')::qs))) => (c,i) == (c',i')
| (Par (SessRec (schlT c p) i P) (MsgQ (schliT c' i') ((msgT (valM v) p')::qs))) => (c,i) == (c',i')
| (Par (SessRec (schlT c p) i P) (MsgQ (schliT c' i') ((msgT (labelM n) p')::qs))) => (c,i) == (c',i')
| (Par (MsgQ (schliT c i) qs) (MsgQ (schliT c' i') qs')) => (c,i)==(c',i')
| ResCh P0 => error P0
| ResVal P0 => error P0
| Par P0 P1 => error P0
| _ => false
end.



(*Definition error2 (P : process) := has (fun x => has (fun y => (error x y) || (error y x)) (rem x (pflatten P))) (pflatten P).*)

Lemma errorP1 : forall P, Error P -> error P.
Proof.
move=>P.
elim;ssa;try solve [ ssa;rewrite !eqxx//=;rewrite eqxx //=;ssa ].
de P0.
Qed.

Lemma errorP2 : forall P, error P -> Error P.
Proof.
elim.
- ssa.
- ssa.
- ssa.
- ssa.
- ssa.
- ssa.
- ssa.
- ssa.
- ssa.
- intros. destruct (not_base p) eqn:Heqn2. 

  ssa. de p.

  con. eauto. ssa.
  con. eauto. 
  con. eauto. 

  ssa. de p. de s. de p0. de s0. norm_eqs. inv H1. con. de s0. 
  norm_eqs. inv H1. con. de s0. norm_eqs. inv H1. con.
  de s. de p0. de s0. norm_eqs. inv H1. con.
  de s0. norm_eqs. inv H1. con.
  de s0. norm_eqs. inv H1.
  con. de s0. de l. de m. de m. norm_eqs. inv H1.
  con. norm_eqs. inv H1. con. de s. de p0.
  de s1. norm_eqs. inv H1. con.
  de s. de p0. de s0. norm_eqs. inv H1. con.
  de s0. de l. de m. de m. norm_eqs. inv H1. con.
  norm_eqs. inv H1. con. de s. de p0. de s0. norm_eqs.
  inv H1. con. de s0. norm_eqs. inv H1. con.
  de s. de p0. de s0. norm_eqs. inv H1. con.
  de s0. norm_eqs. inv H1. con.
  de s0. de l0. de m. de m. norm_eqs. inv H1.
  con. norm_eqs. inv H1. con.

  de s. de p0. de s0. norm_eqs. inv H1. con.
  ssa. ssa. con. eauto.
  ssa. con. eauto.
  ssa. ssa.
Qed.

Lemma errorP : forall P, Error P <-> error P.
Proof.
intros. split. apply/errorP1. apply/errorP2.
Qed.


Lemma partial_balanced_proj : forall E Q p q s T T', uniq (dom E) ->  partial_balanced E Q ->  only_schl E -> sub_domLQ E Q -> lookup E (schlT s p) = Some T -> lookup E (schlT s q) = Some T' ->  
exists g s s', T = makeL s (fe (trans p g)) /\ T' = makeL s' (fe (trans q g))  /\ checkPath s (fe (trans p g)) /\ checkPath s' (fe (trans q g))  /\ Project g p (fe (trans p g))  /\ Project g q (fe (trans q g)) /\ size_pred g /\ action_pred g /\ linearity.Linear g.
Proof.
move=> E Q p q s T T' Hun. intros. move: H2 H3 => Hplook Hqlook.
inv H. ssa.
inv H2. ssa. clear H H2.
rewrite /coherent_gTypes in H6. rewrite /check_gs in H3.
rewrite /balancedL /balancedQ in H4 H5.

apply lookup_filter2 in Hplook,Hqlook. ssa. move: H3 H7 H8 H9 => Hppred Hplook Hqpred Hqlook.

apply H4 in Hplook,Hqlook. ssa. rewrite H8 in H3. inv H3.
apply H6 in H8 as HH'. inv HH'. ssa.
move: (H12 p) (H12 q). ssa. 
exists x5. exists (x4 (s,p)). exists (x4 (s,q)).
rewrite -!makeL_fe2. ssa.
apply/Project_EQ2. eauto. apply EQ2_eunf2. apply/proj_proj. done.
apply/Project_EQ2. eauto. apply EQ2_eunf2. apply/proj_proj. done.
Qed.


Lemma to_Tr2_false : forall p s l g, Trp2 p s g l -> size_pred g -> linearity.Linear g -> action_pred g -> forall  p' s' c u u', l = (Rd,c,u) ->  Trp2 p' s'  g  (Rd,c,u') -> p != p' -> False.
Proof.
move=> p s l g. elim.
- move=>g0 a u g1 l0 d Hunf Hcomp Hl0 Hsize Hlin Hact p' s' c u0 u' Hl0'. subst. inv Hl0';subst_comp. clear Hl0'.
  move/Trp2_full_unf2. rewrite Hunf.
  move=> HE Hnot.
  apply size_pred_full_unf in Hsize.
  apply Linear_full_unf in Hlin. 
  apply action_pred_full_unf in Hact. 
  rewrite Hunf in Hsize Hlin Hact *. clear Hunf. ssa.
  apply Trp2_to_Tr' in HE;ssa. subst_comp. inv H1. de x.
  de x. 
 * inv H2. by rewrite eqxx in Hnot.
 * inv H2. apply ch_diff2 in H1;eauto. 
  ** rewrite H3 in H1. by neqt.
  ** con. 
   *** apply/eqP. intro. rewrite -H4 in H5. by rewrite comp_not in H5;ssa.
   *** apply/ForallP. intro. move/inP. move/[dup]=>Hin. move/(allP H7).
       move=>HH. apply/eqP. intro. rewrite -H4 in HH. rewrite comp_not //in HH.
       apply/Tr_action_pred;[ apply H1| ssa | idtac]. rewrite inE mem_cat. erewrite Hin. by rewrite orbC //=.

- move=> g0 a gs l0 n d Hunf Hcomp Hl0 Hdom /size_pred_full_unf + /Linear_full_unf + /action_pred_full_unf.
  rewrite Hunf /=. case/andP=> Hg0 Hall Hlin /andP [] Hneq Hall2 p' s' c u u' Hl0' HE Hneq'.
  subst. inv Hl0'. subst_comp. clear Hl0'.
  apply Trp2_to_Tr' in HE;ssa. 
  * subst_comp. apply Tr_full_unf in H. rewrite Hunf in H.
    inv H;first by de x. 
    de x. 
    ** inv H0. by rewrite eqxx in Hneq'. 
    inv H0. apply ch_diff2 in H;eauto;first by rewrite H1 in H;neqt.
    con;first by apply/eqP;intro;rewrite -H2 in H3;rewrite comp_not in H3;ssa.
    apply/ForallP. intro. move/inP. move/[dup]=>Hin. move/(allP H4). 
    move=>HH. apply/eqP. intro. rewrite -H2 in HH. rewrite comp_not //in HH.
    apply/Tr_action_pred;[by apply H | by ssa | idtac]. rewrite inE mem_cat. erewrite Hin. by rewrite orbC //=.
 apply/size_pred_full_unf2. rewrite Hunf //=. by ssa.
  
- move=> g0 a u g1 l0 s0 x Hunf Hcomp Hx Hact Htr IH /size_pred_full_unf + /Linear_full_unf + /action_pred_full_unf.
  rewrite Hunf /=. move => Hsize /linear_sgmsg Hlin /andP [] Hneq Hact2 p' s' c u0 u' Hl0 HE Hneq'.
  subst. subst_comp. ssa.
  apply Trp2_full_unf2 in HE. rewrite Hunf in HE. inv HE.
  * inv H. inv H1. subst_comp. by neqt.
  * inv H. subst_comp. ssa. by neqt.
  * inv H. eapply IH in H1;eauto.

- move=> g0 a u' g1 l0 s0 Hunf Hcomp HE IH. (*p msg skip*)
  move=> /size_pred_full_unf + + /action_pred_full_unf.
  rewrite Hunf /=. move=> Hsize Hlin /andP [] Hneq Hact.
  move=> p' s' c u u'0 Hl0 HT Hneq'. subst.
  apply Trp2_full_unf2 in HT. rewrite Hunf in HT.
  inv HT.
 * inv H. inv H1. subst_comp. (*p' msg present*)
   have: Trp2 p (s0) g0 (Rd,action_ch a0,u) by eauto. move=>HH.
   apply Trp2_to_Tr2' in HH. ssa. subst.
   subst_comp. apply Tr2_full_unf in H0. rewrite Hunf in H0.
   inv H0;first by de x. de x. 
   * inv H2. ssa. 
     rewrite /comp_dir in Hcomp. move: Hcomp. rifliad.
   * inv H2. ssa. 
     apply Tr21 in H0. simpl in H0. rewrite /dom /= map_cat in H0.
  
     apply ch_diff2 in H0. by rewrite H3 eqxx in H0. eauto. 
     apply Linear_full_unf in Hlin. rewrite Hunf in Hlin. done.
      
     * con;ssa. rewrite neg_sym //.
       apply/ForallP. intro. move/inP. move/mapP.  case.  move=> x2. move/[dup]=>Hin. 
       move/(allP H7). move=>HH. move=> Hx1. subst.
       apply/eqP. intro. rewrite -H4 in HH.
       rewrite comp_not in HH;ssa.
       apply/Tr_action_pred;[ eauto | ssa | idtac ].
       rewrite inE. apply/orP. right. rewrite mem_cat. apply/orP. left. apply/map_f. done.

   apply/size_pred_full_unf2. rewrite Hunf. ssa.
 * ssa. subst_comp. inv H.
   eapply IH in H3;eauto. 
   * ssa.
   apply Linear_full_unf in Hlin. rewrite Hunf in Hlin. by apply linear_sgmsg in Hlin.
 * inv H. eapply IH in H1;eauto. 
   apply Linear_full_unf in Hlin. rewrite Hunf in Hlin. by apply linear_sgmsg in Hlin.

- move=> /= n a g0 g1 gs l0 s0 x Hunf Hc Hcomp Hx Hin HE IH.
  move=> /size_pred_full_unf + + /action_pred_full_unf. rewrite Hunf.
  move=>/= /andP [] H00 Hall Hlin /andP [] Hneq Hall2.
  move=> p' s' c u u' Hl0 HE' Hneq'. subst. subst_comp.
  apply Trp2_full_unf2 in HE'. rewrite Hunf in HE'.
  inv HE'. 
 * inv H. inv H1. subst_comp. ssa. by neqt.
 * subst_comp. inv H. by neqt.
 * inv H. apply H1 in Hin as HH. eapply IH in HH;eauto;last by apply (allP Hall2) in Hin;ssa. 
   * apply (allP Hall) in Hin. by ssa.
     apply Linear_full_unf in Hlin. rewrite Hunf in Hlin.
     eapply linear_branch in Hlin;last by eauto. by ssa.
 

- move=> /= a g0 gs s0 l0 Hunf Hcomp HT IH.
  move=> /size_pred_full_unf + Hlin /action_pred_full_unf. rewrite Hunf /=.
  move=>/andP [] H00 Hall /andP [] Hneq Hall'.
  move=> p' s' c u u' Hl0 HE Hneq'. subst.

  apply Trp2_full_unf2 in HE. rewrite Hunf in HE.


  inv HE.
 * inv H1. subst_comp. inv H.
   de (mapP H2). de x. subst. apply HT in H0.
   have : Trp2 p s0 g0 (Rd,action_ch a0,u) by eauto.
   move=>HE2. 
   apply Trp2_to_Tr' in HE2;ssa. 
   * subst_comp. apply Tr_full_unf in H3. rewrite Hunf in H3.
     inv H3;first by de x. 
     de x.  
     * inv H4. rewrite /comp_dir in Hcomp. move: Hcomp. rifliad.

     inv H4. apply ch_diff2 in H3;ssa. 
     * rewrite H5 in H3. neqt. (*4*)
     * apply Linear_full_unf in Hlin. rewrite Hunf in Hlin. done.
     * con;first by apply/eqP;intro;rewrite -H6 in H7;
       rewrite comp_not in H7;ssa.
       apply/ForallP. move=> x'. move/inP. 
       move/[dup]=>Hin'.
       move/(allP H8). move=>HH. apply/eqP. intro. rewrite -H6 in HH.
       move : HH. rewrite comp_not //. apply/Tr_action_pred;eauto.
       * apply (allP Hall') in H9. ssa. 
       rewrite mem_cat Hin' //=.
     * apply size_pred_full_unf2. rewrite Hunf. ssa.
   
   * subst_comp. inv H.
     eapply IH in H3 as HIH ;eauto. 
     * ssa.
     * apply (allP Hall) in H3. done.
     * apply Linear_full_unf in Hlin. rewrite Hunf in Hlin.
     * eapply linear_branch in Hlin. 2:eauto. done.
  * apply (allP Hall') in H3. done. 

  * inv H.
   have : nth (0,GEnd) gs0 0 \in gs0.  apply/mem_nth. done.
   intro. destruct (nth _ _ _) eqn:Heqn;ssa.
   apply H1 in x. eapply IH in x;eauto. 
   * apply/nthP. econ. 2:eauto. done.
   * have : (n,g1) \in gs0. rewrite -Heqn. apply/mem_nth. done.
     move=>HH.
     apply (allP Hall) in HH. ssa.
   * apply Linear_full_unf in Hlin. rewrite Hunf in Hlin.
     eapply linear_branch in Hlin. move : Hlin. instantiate (1:= (n,g1)). ssa.
     apply/nthP. econ. 2:eauto. done.
   * have : (n,g1) \in gs0. rewrite -Heqn. apply/mem_nth. done.
     move=>HH.
     apply (allP Hall') in HH. ssa.
Qed.

Inductive Trp3 (p : ptcp) : seq (value + nat) -> gType ->  (dir * ch * (value + nat)) -> Prop := 
| GT20 g a u g0 l d : full_unf g = GMsg a u g0 -> comp_dir p a = Some d -> l = (d,action_ch a,inl u) -> Trp3 p nil g l
| GT20' g a gs l n d : full_unf g = GBranch a gs -> comp_dir p a = Some d -> l = (d,action_ch a,inr n) -> n \in dom gs -> Trp3 p nil g l
| GT21 g a u' g0 l s :  full_unf g = GMsg a u' g0 -> comp_dir p a = Some Sd -> Trp3 p s g0 l  -> Trp3 p ((inl u')::s) g l
| GT22 g a u' g0 l s :  full_unf g = GMsg a u' g0 -> comp_dir p a = None -> Trp3 p s g0 l  -> Trp3 p s g l
| GT23 g a g0 n gs s l : full_unf g = GBranch a gs ->  comp_dir p a = Some Sd -> (n,g0) \in gs -> Trp3 p s g0 l -> Trp3 p ((inr n)::s) g l
| GT24 a g gs s l : full_unf g = GBranch a gs ->  comp_dir p a = None -> (forall n g, (n,g) \in gs -> Trp3 p s g l) -> Trp3 p s g l.
Hint Constructors Trp3.


Lemma Trp3_full_unf : forall p l g l', Trp3 p l (full_unf g) l' -> Trp3 p l g l'.
Proof.
intros. move : H. move Heq : (full_unf _ ) => g' Htr.
elim : Htr g Heq;ssa;subst. rewrite full_unf2 in H.
econ. eauto. eauto. done. 
rewrite full_unf2 in H.
econstructor 2. eauto. eauto. eauto. eauto.
rewrite full_unf2 in H. econstructor 3. eauto. done. done.
rewrite full_unf2 in H. econstructor 4. eauto. done. done.
rewrite full_unf2 in H. eauto.
rewrite full_unf2 in H. eauto.
Qed.

Lemma Trp3_full_unf2 : forall p l g l', Trp3 p l (g) l' -> Trp3 p l (full_unf g) l'.
Proof.
intros. 
elim : H;rewrite ?full_unf2;ssa.
econ. rewrite full_unf2. eauto. eauto. done.
econstructor 2. rewrite full_unf2. eauto. eauto. eauto. done.
econstructor 3. rewrite full_unf2. eauto. eauto. eauto. 
econstructor 4. rewrite full_unf2. eauto. eauto. eauto.
econstructor 5. rewrite full_unf2. eauto. eauto. eauto. done.
econstructor 6. rewrite full_unf2. eauto. eauto. eauto.
Qed.

Lemma to_Trp3 : forall p s g l, Trp p (s++[::l]) g -> all (fun x => (x.1.1 == Sd)) s -> Trp3 p (map (fun x => (x.2)) s) g l.
Proof.
move=> p s g l. move Heq : (_ ++_ ) => s' H.
elim : H s l Heq;ssa.
de s. de s. inv Heq. econ. eauto. eauto. done.
inv Heq. ssa. econ. eauto. norm_eqs. done. 
norm_eqs.  eauto. eauto.
de s. inv Heq. econstructor 2. eauto. eauto. eauto. apply/mapP. econ. eauto. done.
inv Heq. econstructor 5. eauto.  ssa. norm_eqs. ssa. subst. eauto. ssa. eauto. 
Qed.

Lemma Trp3_to_Tr' : forall p s g l, Trp3 p s g l -> size_pred g ->  exists ss x, Tr (ss++[::x]) g /\ comp_dir p x = Some l.1.1 /\ action_ch x = l.1.2 /\ all (fun y => comp_dir p y != Some Rd) ss.
Proof.
move=> p s g l. elim;ssa;subst.
- exists nil. exists a. ssa. 
apply/Tr_full_unf2. rewrite H. eauto.
- exists nil. exists a. ssa. apply/Tr_full_unf2. rewrite H. de (mapP H2). de x.
  econ. eauto. done.
- apply size_pred_full_unf in H3. rewrite H in H3. ssa. 
  de (H2 H3). subst_comp. exists (a::x). exists x0. ssa. apply/Tr_full_unf2. rewrite H. econ. eauto.
  rewrite /comp_dir eqxx //=.
- apply size_pred_full_unf in H3. rewrite H in H3. ssa. 
  de (H2 H3). exists (a::x). exists x0. ssa. apply/Tr_full_unf2. rewrite H. econ. eauto. rewrite H0 //=.
-  apply size_pred_full_unf in H4. rewrite H in H4. ssa.
   apply (allP H6) in H1 as HH. de (H3 HH).
   exists (a::x). exists x0. ssa. apply/Tr_full_unf2. rewrite H. econ. eauto. eauto. rewrite H0 //=.
- apply size_pred_full_unf in H3. rewrite H in H3. ssa.
  de gs. de p0. eapply H2 in H3;ssa.
  exists (a::x). exists x0. ssa. apply/Tr_full_unf2. rewrite H. econ. eauto. eauto. rewrite H0 //.
Qed.

Lemma Trp3_to_Tr2' : forall p s g l, Trp3 p s g l -> size_pred g ->  exists ss x, Tr2 (ss++[::x]) g /\ comp_dir p x.1 = Some l.1.1 /\ action_ch x.1 = l.1.2 /\ all (fun y => comp_dir p y.1 != Some Rd) ss /\ x.2 = l.2.
Proof.
move=> p s g l. elim;ssa;subst.
- exists nil. exists (a,inl u). ssa. apply/Tr2_full_unf2. rewrite H. eauto.
- exists nil. exists (a,inr n). ssa. apply/Tr2_full_unf2. rewrite H. de (mapP H2). de x. subst.
  econ. eauto. done.
- apply size_pred_full_unf in H3. rewrite H in H3. ssa. 
  de (H2 H3). subst_comp. exists ((a,inl u')::x). exists x0. ssa. apply/Tr2_full_unf2. rewrite H. econ. eauto.
  rewrite /comp_dir eqxx //=.
- apply size_pred_full_unf in H3. rewrite H in H3. ssa. 
  de (H2 H3). exists ((a,inl u')::x). exists x0. ssa. apply/Tr2_full_unf2. rewrite H. econ. eauto. rewrite H0 //=.
-  apply size_pred_full_unf in H4. rewrite H in H4. ssa.
   apply (allP H6) in H1 as HH. de (H3 HH).
   exists ((a,inr n)::x). exists x0. ssa. apply/Tr2_full_unf2. rewrite H. econ. eauto. eauto. rewrite H0 //=.
- apply size_pred_full_unf in H3. rewrite H in H3. ssa.
  de gs. de p0. eapply H2 in H3;ssa.
  exists ((a,inr n)::x). exists x0. ssa. apply/Tr2_full_unf2. rewrite H. econ. eauto. eauto. rewrite H0 //.
Qed.


Lemma to_Tr2_output_false : forall p s l g, Trp3 p s g l -> size_pred g -> linearity.Linear g -> action_pred g -> forall  p' s' c u u', l = (Sd,c,u) ->  Trp3 p' s' g (Sd,c,u') -> p != p' -> False.
Proof.
move=> p s l g. elim.
- move=>g0 a u g1 l0 d Hunf Hcomp Hl0 Hsize Hlin Hact p' s' c u0 u' Hl0'. subst. inv Hl0';subst_comp. clear Hl0'.
  move/Trp3_full_unf2. rewrite Hunf.
  move=> HE Hnot.
  apply size_pred_full_unf in Hsize.
  apply Linear_full_unf in Hlin. 
  apply action_pred_full_unf in Hact. 
  rewrite Hunf in Hsize Hlin Hact *. clear Hunf. ssa. 
  apply Trp3_to_Tr' in HE;ssa. subst_comp. inv H1. de x.
  de x. 
 * inv H2. by rewrite eqxx in Hnot.
 * inv H2. apply ch_diff in H1;eauto. 
  ** rewrite H3 in H1. by neqt.
  ** con. 
   *** apply/eqP. intro. rewrite -H4 in H5. by rewrite comp_not in H5;ssa.
   *** apply/ForallP. intro. move/inP. move/[dup]=>Hin. move/(allP H7).
       move=>HH. apply/eqP. intro. rewrite -H4 in HH. rewrite comp_not //in HH.
       apply/Tr_action_pred;[ apply H1| ssa | idtac]. rewrite inE mem_cat. erewrite Hin. by rewrite orbC //=.

- move=> g0 a gs l0 n d Hunf Hcomp Hl0 Hdom /size_pred_full_unf + /Linear_full_unf + /action_pred_full_unf.
  rewrite Hunf /=. case/andP=> Hg0 Hall Hlin /andP [] Hneq Hall2 p' s' c u u' Hl0' HE Hneq'.
  subst. inv Hl0'. subst_comp. clear Hl0'.
  apply Trp3_to_Tr' in HE;ssa. 
  * subst_comp. apply Tr_full_unf in H. rewrite Hunf in H.
    inv H;first by de x. 
    de x. 
    ** inv H0. by rewrite eqxx in Hneq'. 
    inv H0. apply ch_diff in H;eauto;first by rewrite H1 in H;neqt.
    con;first by apply/eqP;intro;rewrite -H2 in H3;rewrite comp_not in H3;ssa.
    apply/ForallP. intro. move/inP. move/[dup]=>Hin. move/(allP H4). 
    move=>HH. apply/eqP. intro. rewrite -H2 in HH. rewrite comp_not //in HH.
    apply/Tr_action_pred;[by apply H | by ssa | idtac]. rewrite inE mem_cat. erewrite Hin. by rewrite orbC //=.
 apply/size_pred_full_unf2. rewrite Hunf //=. by ssa.
  
- move=> g0 a u g1 l0 s0 Hunf Hcomp. 
(*Hx Hact Htr *)
  move=>Htr IH /size_pred_full_unf + /Linear_full_unf + /action_pred_full_unf.
  rewrite Hunf /=. move => Hsize /linear_sgmsg Hlin /andP [] Hneq Hact2 p' s' c u0 u' Hl0 HE Hneq'.
  subst. subst_comp. ssa.
  apply Trp3_full_unf2 in HE. rewrite Hunf in HE. inv HE.
  * inv H. inv H1. subst_comp. by neqt.
  * inv H. subst_comp. ssa. by neqt.
  * inv H. eapply IH in H1;eauto.

- move=> g0 a u' g1 l0 s0 Hunf Hcomp HE IH. (*p msg skip*)
  move=> /size_pred_full_unf + + /action_pred_full_unf.
  rewrite Hunf /=. move=> Hsize Hlin /andP [] Hneq Hact.
  move=> p' s' c u u'0 Hl0 HT Hneq'. subst.
  apply Trp3_full_unf2 in HT. rewrite Hunf in HT.
  inv HT.
 * inv H. inv H1. subst_comp. (*p' msg present*)
   have: Trp3 p (s0) g0 (Sd,action_ch a0,u) by eauto. move=>HH.
   apply Trp3_to_Tr2' in HH. ssa. subst.
   subst_comp. apply Tr2_full_unf in H0. rewrite Hunf in H0.
   inv H0;first by de x. de x. 
   * inv H2. ssa. 
     rewrite /comp_dir in Hcomp. move: Hcomp. rifliad.
   * inv H2. ssa. 
     apply Tr21 in H0. simpl in H0. rewrite /dom /= map_cat in H0.
  
     apply ch_diff in H0. by rewrite H3 eqxx in H0. 
     apply Linear_full_unf in Hlin. rewrite Hunf in Hlin. done.
      
     * con;ssa. rewrite neg_sym //. rewrite /comp_dir in H5. move: H5. case_if. done.
       case_if. done. done.
       apply/ForallP. intro. move/inP. move/mapP.  case.  move=> x2. move/[dup]=>Hin. 
       move/(allP H7). move=>HH. move=> Hx1. subst.
       apply/eqP. intro. rewrite -H4 in HH.
       rewrite comp_not in HH;ssa.
       apply/Tr_action_pred;[ eauto | ssa | idtac ].
       rewrite inE. apply/orP. right. rewrite mem_cat. apply/orP. left. apply/map_f. done.
       rewrite neg_sym. done.

   apply/size_pred_full_unf2. rewrite Hunf. ssa.
 * ssa. subst_comp. inv H.
   eapply IH in H1;eauto. 
   * ssa.
   apply Linear_full_unf in Hlin. rewrite Hunf in Hlin. by apply linear_sgmsg in Hlin.
 * inv H. eapply IH in H1;eauto. 
   apply Linear_full_unf in Hlin. rewrite Hunf in Hlin. by apply linear_sgmsg in Hlin.

- move=> /= n a g0 g1 gs l0 s0 Hunf (*Hc*) Hcomp (*Hx*) Hin HE IH.
  move=> /size_pred_full_unf + + /action_pred_full_unf. rewrite Hunf.
  move=>/= /andP [] H00 Hall Hlin /andP [] Hneq Hall2.
  move=> p' s' c u u' Hl0 HE' Hneq'. subst. subst_comp.
  apply Trp3_full_unf2 in HE'. rewrite Hunf in HE'.
  inv HE'. 
 * inv H. inv H1. subst_comp. ssa. by neqt.
 * subst_comp. inv H. by neqt.
 * inv H. apply H1 in Hin as HH. eapply IH in HH;eauto;last by apply (allP Hall2) in Hin;ssa. 
   * apply (allP Hall) in Hin. by ssa.
     apply Linear_full_unf in Hlin. rewrite Hunf in Hlin.
     eapply linear_branch in Hlin;last by eauto. by ssa.
 

- move=> /= a g0 gs s0 l0 Hunf Hcomp HT IH.
  move=> /size_pred_full_unf + Hlin /action_pred_full_unf. rewrite Hunf /=.
  move=>/andP [] H00 Hall /andP [] Hneq Hall'.
  move=> p' s' c u u' Hl0 HE Hneq'. subst.

  apply Trp3_full_unf2 in HE. rewrite Hunf in HE.


  inv HE.
 * inv H1. subst_comp. inv H.
   de (mapP H2). de x. subst. apply HT in H0.
   have : Trp3 p s0 g0 (Sd,action_ch a0,u) by eauto.
   move=>HE2. 
   apply Trp3_to_Tr' in HE2;ssa. 
   * subst_comp. apply Tr_full_unf in H3. rewrite Hunf in H3.
     inv H3;first by de x. 
     de x.  
     * inv H4. rewrite /comp_dir in Hcomp. move: Hcomp. rifliad.

     inv H4. apply ch_diff in H3;ssa. 
     * rewrite H5 in H3. neqt. (*4*)
     * apply Linear_full_unf in Hlin. rewrite Hunf in Hlin. done.
     * con;first by apply/eqP;intro;rewrite -H6 in H7;
       rewrite comp_not in H7;ssa.
       apply/ForallP. move=> x'. move/inP. 
       move/[dup]=>Hin'.
       move/(allP H8). move=>HH. apply/eqP. intro. rewrite -H6 in HH.
       move : HH. rewrite comp_not //. apply/Tr_action_pred;eauto.
       * apply (allP Hall') in H9. ssa. 
       rewrite mem_cat Hin' //=. rewrite neg_sym //=.
     * apply size_pred_full_unf2. rewrite Hunf. ssa.
   
   * subst_comp. inv H.
     eapply IH in H1 as HIH ;eauto. 
     * ssa.
     * apply (allP Hall) in H1. done.
     * apply Linear_full_unf in Hlin. rewrite Hunf in Hlin.
     * eapply linear_branch in Hlin. 2:eauto. done.
  * apply (allP Hall') in H1. done. 

  * inv H.
   have : nth (0,GEnd) gs0 0 \in gs0.  apply/mem_nth. done.
   intro. destruct (nth _ _ _) eqn:Heqn;ssa.
   apply H1 in x. eapply IH in x;eauto. 
   * apply/nthP. econ. 2:eauto. done.
   * have : (n,g1) \in gs0. rewrite -Heqn. apply/mem_nth. done.
     move=>HH.
     apply (allP Hall) in HH. ssa.
   * apply Linear_full_unf in Hlin. rewrite Hunf in Hlin.
     eapply linear_branch in Hlin. move : Hlin. instantiate (1:= (n,g1)). ssa.
     apply/nthP. econ. 2:eauto. done.
   * have : (n,g1) \in gs0. rewrite -Heqn. apply/mem_nth. done.
     move=>HH.
     apply (allP Hall') in HH. ssa.
Qed.


Lemma size_pred_trans : forall p g, size_pred g -> esize_pred (trans p g).
Proof.
move=> p. elim;ssa.
case_if;ssa.
destruct (comp_dir _ _) eqn:Heqn;ssa.
destruct (comp_dir _ _) eqn:Heqn;ssa. de l.
apply/allP. intro. move/mapP. case. move=> x0 Hin. move:(allP H2 _ Hin).
move=>/=. move=> Hs. move=>Hx. subst. de x0. eauto.
de l. eapply H. instantiate (1:= p0.1). de p0. done.
Qed.


Lemma esize_pred_ren : forall g sigma, esize_pred g = esize_pred g ⟨e sigma ⟩.
Proof. elim;rewrite //=;intros. ssa'. rewrite size_map.  f_equal. 
elim : l H. done. ssa'. erewrite H0. f_equal.  instantiate (1:= sigma). destruct a. ssa'. 
apply/H. intros. apply/H0. eauto.  eauto. instantiate (1:= a.1). destruct a. done. 
Qed. 

Lemma esize_pred_subst : forall g sigma, (forall n, esize_pred (sigma n)) ->  esize_pred g = esize_pred g[e sigma].
Proof. elim;rewrite //=;intros. 
rewrite H //=. apply/H. case. done. simpl. intros. asimpl. rewrite -esize_pred_ren. done. 
rewrite size_map. f_equal. 
elim : l H H0. done. ssa'. erewrite H0. f_equal.  instantiate (1 := sigma). destruct a. ssa'.
apply/H. intros. apply/H0. eauto.  eauto. done. instantiate (1:= a.1). destruct a. done.
done. 
Qed.

Lemma esize_pred_subst2 : forall g sigma, esize_pred g[e sigma] -> esize_pred g.  
Proof. elim;rewrite //=;intros. eauto. ssa'. rewrite size_map in H1. ssa'. 
apply/allP=> x xIn. apply/H. 
eauto. instantiate (1:= x.1). destruct x. done. 
instantiate (1:= sigma). ssa'. 
rewrite all_map in H2. move :  (allP H2 _ xIn). ssa'. destruct x. ssa'. 
Qed.


Lemma esize_pred_unf : forall g, esize_pred g ->  esize_pred (eunf g). 
Proof. case=>//=. intros. rewrite -esize_pred_subst. done. case. done. done. 
Qed.

Lemma esize_pred_full_unf : forall g, esize_pred g ->  esize_pred (full_eunf g). 
Proof. 
intros. rewrite /full_eunf. remember (emu_height g). clear Heqn. elim : n g H. done. 
intros. simpl. apply/esize_pred_unf. eauto. 
Qed.

Lemma makeL_size_pred : forall s e, esize_pred e -> esize_pred (makeL s e).
Proof.
elim;ssa.
apply esize_pred_full_unf. done.
de a. destruct (fe e) eqn:Heqn;ssa. destruct (lookup l0 n) eqn:Heqn2;ssa.
apply in_pair in Heqn2. apply H. apply esize_pred_full_unf in H0. rewrite Heqn in H0. ssa. apply (allP H2) in Heqn2. ssa.
destruct (fe e) eqn:Heqn;ssa. apply esize_pred_full_unf in H0. rewrite Heqn in H0. ssa. 
Qed.


Lemma flatten_Sd : forall x0 x p' c, flatten (list_map (proj_act p') x0) = x ++ [:: (Sd, c)] -> exists l a l', x0 = l++(a::l') /\ comp_dir p' a = Some Sd /\ action_ch a = c /\ proj_tr p' l = x.  
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

Lemma makeQ_ETr3_aux : forall l e k u, checkPath l e -> canEstep2 (makeL l e) (Sd,k,u) ->  exists s, ETr (s++[::(Sd,k,u)]) e /\ all (fun x => x.1.1 == Sd) s.
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

Lemma balanced_to_partial : forall E Q, balanced E Q -> partial_balanced E Q.
Proof.
intros. rewrite /partial_balanced. exists E. exists (fun _ => true). exists Q. exists (fun _ _ => true). ssa.
rewrite filter_keys_predT. done.
rewrite filter_q_predT. done.
Qed.


Definition SUB_domLQ (L : l_env) (Q : q_env) := only_schl L /\
uniq (dom L) /\ uniq (dom Q) /\ (forall (s : schl) (p : ptcp), (schlT s p \in dom L) -> (QKey s p \in dom Q)).

Lemma coherent_to_partial: forall E Q, env_coherent E Q -> SUB_domLQ E Q -> only_schl E -> partial_balanced E Q.
Proof. intros. eapply balanced_to_partial. inv H0.
eapply coherent_balanced;ssa.
Qed.

Inductive Temp : (value + nat) -> value + nat -> Prop := 
  | T0 u u' : u = u'  -> Temp (inl u) (inl u')
  | T1 l l' : Temp (inr l) (inr l').

Lemma step_uniq3 : forall g l g', step g l g' -> size_pred g -> forall l' g'', step g l' g'' -> l.1 = l'.1 -> Temp l.2 l'.2. 
Proof.
move=> g l g'. elim;ssa;subst. inv H0.
de l'. inv H1. con. done.
rewrite !inE negb_or eqxx //= in H7. ssa.

inv H1. de l'. con. 
rewrite !inE negb_or eqxx //= in H9. ssa.
inv H3. ssa. subst.
rewrite !inE negb_or eqxx //= in H1. ssa.
eauto.

inv H4. de l0. subst.
rewrite !inE negb_or eqxx //= in H2. ssa.
de gs. de gs'. de gs'0. eapply H1. eauto. done.
apply:H10. eauto. done.
inv H2.
eapply H0;eauto.
apply size_pred_subst. de x. done.
Qed.

Lemma balanced_can_step' : forall E Q s p' p k u u' l0 l  T, partial_balanced E Q -> all (fun x => x.1 != k) l0 ->
lookup Q (QKey s p') = Some (l0++(k,u)::l) -> 
lookup E (schlT s p) = Some T -> canEstep2 T (Rd,k,u')  -> (exists g, size_pred g /\ (exists g',step g (Action p' p k,u) g') /\ (exists g', step g (Action p' p k,u') g')) /\ (forall x y, u = inl x -> u' = inl y -> x = y). 
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
     size_pred x6 /\ ((exists g' : gType, step x6 (Action p' p k, u) g') /\
     (exists g' : gType, step x6 (Action p' p k, u') g')) /\
  (forall x3 y : value, u = inl x3 -> u' = inl y -> x3 = y).
ssa. eauto. exists x6. eauto.
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


Lemma OFT_not_error : forall P, Error P -> forall Ms Ds E Q C, partial_balanced E Q -> SUB_domLQ E Q -> ~ OFT Ms Ds P E Q C.
Proof.
move=>P. elim.

- move=> s p q i P0 P1 Ms Ds E Q C Hco Heq Hoft.
  inv Hoft. clear H2 H3. inv H1. clear H1. move: H6 H10 => Htp Htq.
  inv Htp. move: Htp H4 H8 H9 => _ _ Hplook Htp.
  inv Htq. move: Htq H4 H8 H9 => _ _ Hqlook Htq.
  apply lookup_filter2 in Hplook,Hqlook;ssa.   
  move: H1 H2 H H0 => Hppred Hplook Hqpred Hqlook.
  eapply partial_balanced_proj in Hco.
  5: apply Hplook.
  5: apply Hqlook. 
  ssa.
  move: H H0 H1 H2 H3 H4 H5 H6 H7 => Hpmake Hqmake Hpcheck Hqcheck Hpproj Hqproj Hsize Hact Hlin.

  2: inv Heq; ssa.
  2: inv Heq; ssa.
  2: inv Heq; ssa.
  have: p != q. apply/eqP. intro. subst. rewrite /predC in Hqpred. rewrite Hppred in Hqpred. done. move=>Hpq.
  
* have: canEstep2 (makeL x0 (fe (trans p x))) (Rd,i,inl (VSort m)). 
  rewrite -Hpmake. con.
  
  move=>HC.
  eapply makeQ_ETr2 in HC;eauto. 
  ssa.
  move: H H0 => Hetr Hall.
  eapply to_Trp in Hetr;eauto.
  apply to_Trp2 in Hetr;eauto.
  2: { apply/allP. intro. move/(allP Hall _). ssa. } 

* have: canEstep2 (makeL x1 (fe (trans q x))) (Rd,i,inl (VSort m0)).
  rewrite -Hqmake. con.
  
  move=>HC.
  eapply makeQ_ETr2 in HC;eauto. 
  ssa.
  move: H H0 => Hetr' Hall'.
  eapply to_Trp in Hetr';eauto.
  apply to_Trp2 in Hetr';eauto.
  2: { apply/allP. intro. move/(allP Hall' _). ssa. } 

  apply:to_Tr2_false. apply:Hetr. done. done. done. eauto. apply Hetr'. done.


- move=> s p q i P0 Ps Ms Ds E Q C Hco Heq Hoft.
  inv Hoft. clear H2 H3. inv H1. clear H1. move: H6 H10 => Htp Htq.
  inv Htp. move: Htp H4 H8 H9 => _ _ Hplook Htp.
  inv Htq. move: Htq H2 H5 H9 H10 => _ _ _ Hqlook Htq.
  apply lookup_filter2 in Hplook,Hqlook;ssa.   
  move: H1 H2 H H0 => Hppred Hplook Hqpred Hqlook.
  eapply partial_balanced_proj in Hco.
  5: apply Hplook.
  5: apply Hqlook. 
  ssa.
  move: H H0 H1 H2 H3 H4 H5 H6 H7 => Hpmake Hqmake Hpcheck Hqcheck Hpproj Hqproj Hsize Hact Hlin.
  2: inv Heq; ssa.
  2: inv Heq; ssa.
  2: inv Heq; ssa.
  have: p != q. apply/eqP. intro. subst. rewrite /predC in Hqpred. rewrite Hppred in Hqpred. done. move=>Hpq.
  
* have: canEstep2 (makeL x0 (fe (trans p x))) (Rd,i,inl (VSort m)). 
  rewrite -Hpmake. con.
  
  move=>HC.
  eapply makeQ_ETr2 in HC;eauto. 
  ssa.
  move: H H0 => Hetr Hall.
  eapply to_Trp in Hetr;eauto.
  apply to_Trp2 in Hetr;eauto. 

  2: { apply/allP. intro. move/(allP Hall _). ssa. } 

* apply (@size_pred_trans q) in Hsize as Hsize'. 
  apply esize_pred_full_unf in Hsize'.
  
  apply (@makeL_size_pred x1) in Hsize'. rewrite -Hqmake in Hsize'. ssa.
  have : exists x, x \in Ts. de Ts. eauto. ssa.
  have: canEstep2 (makeL x1 (fe (trans q x))) (Rd,i,inr (x3.1)).
  rewrite -Hqmake. de x3. econ.  eauto.
  move=>HC.
  eapply makeQ_ETr2 in HC;eauto. 
  ssa.
  move: H2 H3 => Hetr' Hall'.
  eapply to_Trp in Hetr';eauto.
  apply to_Trp2 in Hetr';eauto.
  2: { apply/allP. intro. move/(allP Hall' _). ssa. } 

  apply:to_Tr2_false. apply:Hetr. done. done. done. done. eauto. done.


- move=> s p q i P0 P1 Ms Ds E Q C Hco Heq Hoft.
  inv Hoft. clear H2 H3. inv H1. clear H1. move: H6 H10 => Htp Htq.
  inv Htp. move: Htp H4 H8 H9 => _ _ Hplook Htp.
  inv Htq. move: Htq H4 H8 H9 => _ _ Hqlook Htq.
  apply lookup_filter2 in Hplook,Hqlook;ssa.   
  move: H1 H2 H H0 => Hppred Hplook Hqpred Hqlook.
  eapply partial_balanced_proj in Hco.
  5: apply Hplook.
  5: apply Hqlook. 
  ssa.
  move: H H0 H1 H2 H3 H4 H5 H6 H7 => Hpmake Hqmake Hpcheck Hqcheck Hpproj Hqproj Hsize Hact Hlin.
  2: inv Heq; ssa.
  2: inv Heq; ssa.
  2: inv Heq; ssa.
  have: p != q. apply/eqP. intro. subst. rewrite /predC in Hqpred. rewrite Hppred in Hqpred. done. move=>Hpq.
  
* have: canEstep2 (makeL x0 (fe (trans p x))) (Rd,i,inl (VSort m)). 
  rewrite -Hpmake. con.
  
  move=>HC.
  eapply makeQ_ETr2 in HC;eauto. 
  ssa.
  move: H H0 => Hetr Hall.
  eapply to_Trp in Hetr;eauto.
  apply to_Trp2 in Hetr;eauto.
  2: { apply/allP. intro. move/(allP Hall _). ssa. } 

* have: canEstep2 (makeL x1 (fe (trans q x))) (Rd,i,inl (VLT T' ptcp0)).
  rewrite -Hqmake. con.
  
  move=>HC.
  eapply makeQ_ETr2 in HC;eauto. 
  ssa.
  move: H H0 => Hetr' Hall'.
  eapply to_Trp in Hetr';eauto.
  apply to_Trp2 in Hetr';eauto.
  2: { apply/allP. intro. move/(allP Hall' _). ssa. } 

  apply:to_Tr2_false. apply:Hetr. done. done. done. eauto. apply Hetr'. done.


- move=> s p q i Ps Ps' Ms Ds E Q C Hco Heq Hoft.
  inv Hoft. clear H2 H3. inv H1. clear H1. move: H6 H10 => Htp Htq.
  inv Htp. move: Htp H2 H5 H9 H10 => _ _ _ Hplook Htp.
  inv Htq. move: Htq H2 H5 H9 H10 => _ _ _ Hqlook Htq.
  apply lookup_filter2 in Hplook,Hqlook;ssa.   
  move: H1 H2 H H0 => Hppred Hplook Hqpred Hqlook.
  eapply partial_balanced_proj in Hco.
  5: apply Hplook.
  5: apply Hqlook. 
  ssa.
  move: H H0 H1 H2 H3 H4 H5 H6 H7 => Hpmake Hqmake Hpcheck Hqcheck Hpproj Hqproj Hsize Hact Hlin.
  2: inv Heq; ssa.
  2: inv Heq; ssa.
  2: inv Heq; ssa.
  have: p != q. apply/eqP. intro. subst. rewrite /predC in Hqpred. rewrite Hppred in Hqpred. done. move=>Hpq.
  
* apply (@size_pred_trans p) in Hsize as Hsize'. 
  apply esize_pred_full_unf in Hsize'.
  apply (@makeL_size_pred x0) in Hsize'. rewrite -Hpmake in Hsize'. ssa.
  have : exists x, x \in Ts. de Ts. eauto. ssa. move: H1 => Hexists.
  
  have: canEstep2 (makeL x0 (fe (trans p x))) (Rd,i,inr x2.1). 
  rewrite -Hpmake. de x2. econ. eauto.
  
  move=>HC.
  eapply makeQ_ETr2 in HC;eauto. 
  ssa.
  move: H1 H2 => Hetr Hall.
  eapply to_Trp in Hetr;eauto.
  apply to_Trp2 in Hetr;eauto. 

  2: { apply/allP. intro. move/(allP Hall _). ssa. } 

* apply (@size_pred_trans q) in Hsize as Hsize'. 
  apply esize_pred_full_unf in Hsize'.
  
  apply (@makeL_size_pred x1) in Hsize'. rewrite -Hqmake in Hsize'. ssa.
  have : exists x, x \in Ts0. de Ts0. eauto. ssa.
  have: canEstep2 (makeL x1 (fe (trans q x))) (Rd,i,inr (x4.1)).
  rewrite -Hqmake. de x4. econ. eauto.
  move=>HC.
  eapply makeQ_ETr2 in HC;eauto. 
  ssa.
  move: H4 H5 => Hetr' Hall'.
  eapply to_Trp in Hetr';eauto.
  apply to_Trp2 in Hetr';eauto.
  2: { apply/allP. intro. move/(allP Hall' _). ssa. } 

  apply:to_Tr2_false. apply:Hetr. done. done. done. done. eauto. done.

- move=> s p q i Ps P0 Ms Ds E Q C Hco Heq Hoft.
  inv Hoft. clear H2 H3. inv H1. clear H1. move: H6 H10 => Htp Htq.
  inv Htp. move: Htp H2 H5 H9 H10 => _ _ _ Hplook Htp.
  inv Htq. move: Htq H4 H8 H9 => _ _ Hqlook Htq.
  apply lookup_filter2 in Hplook,Hqlook;ssa.   
  move: H1 H2 H H0 => Hppred Hplook Hqpred Hqlook.
  eapply partial_balanced_proj in Hco.
  5: apply Hplook.
  5: apply Hqlook. 
  ssa.
  move: H H0 H1 H2 H3 H4 H5 H6 H7 => Hpmake Hqmake Hpcheck Hqcheck Hpproj Hqproj Hsize Hact Hlin.
  2: inv Heq; ssa.
  2: inv Heq; ssa.
  2: inv Heq; ssa.
  have: p != q. apply/eqP. intro. subst. rewrite /predC in Hqpred. rewrite Hppred in Hqpred. done. move=>Hpq.
  
* apply (@size_pred_trans p) in Hsize as Hsize'. 
  apply esize_pred_full_unf in Hsize'.
  apply (@makeL_size_pred x0) in Hsize'. rewrite -Hpmake in Hsize'. ssa.
  have : exists x, x \in Ts. de Ts. eauto. ssa. move: H1 => Hexists.
  
  have: canEstep2 (makeL x0 (fe (trans p x))) (Rd,i,inr x2.1). 
  rewrite -Hpmake. de x2. econ. eauto.
  
  move=>HC.
  eapply makeQ_ETr2 in HC;eauto. 
  ssa.
  move: H1 H2 => Hetr Hall.
  eapply to_Trp in Hetr;eauto.
  apply to_Trp2 in Hetr;eauto. 

  2: { apply/allP. intro. move/(allP Hall _). ssa. } 

* have: canEstep2 (makeL x1 (fe (trans q x))) (Rd,i,inl (VLT T' ptcp0)).
  rewrite -Hqmake. con.
  
  move=>HC.
  eapply makeQ_ETr2 in HC;eauto. 
  ssa.
  move: H1 H2 => Hetr' Hall'.
  eapply to_Trp in Hetr';eauto.
  apply to_Trp2 in Hetr';eauto.
  2: { apply/allP. intro. move/(allP Hall' _). ssa. } 

  apply:to_Tr2_false. apply:Hetr. done. done. done. eauto. apply Hetr'. done.


- move=> s p q i P0 P1 Ms Ds E Q C Hco Heq Hoft.
  inv Hoft. clear H2 H3. inv H1. clear H1. move: H6 H10 => Htp Htq.
  inv Htp. move: Htp H4 H8 H9 => _ _ Hplook Htp.
  inv Htq. move: Htq H4 H8 H9 => _ _ Hqlook Htq.
  apply lookup_filter2 in Hplook,Hqlook;ssa.   
  move: H1 H2 H H0 => Hppred Hplook Hqpred Hqlook.
  eapply partial_balanced_proj in Hco.
  5: apply Hplook.
  5: apply Hqlook. 
  ssa.
  move: H H0 H1 H2 H3 H4 H5 H6 H7 => Hpmake Hqmake Hpcheck Hqcheck Hpproj Hqproj Hsize Hact Hlin.
  2: inv Heq; ssa.
  2: inv Heq; ssa.
  2: inv Heq; ssa.
  have: p != q. apply/eqP. intro. subst. rewrite /predC in Hqpred. rewrite Hppred in Hqpred. done. move=>Hpq.
  
* have: canEstep2 (makeL x0 (fe (trans p x))) (Rd,i,inl (VLT T' ptcp0)). 
  rewrite -Hpmake. con.
  
  move=>HC.
  eapply makeQ_ETr2 in HC;eauto. 
  ssa.
  move: H H0 => Hetr Hall.
  eapply to_Trp in Hetr;eauto.
  apply to_Trp2 in Hetr;eauto.
  2: { apply/allP. intro. move/(allP Hall _). ssa. } 

* have: canEstep2 (makeL x1 (fe (trans q x))) (Rd,i,inl (VLT T'0 ptcp0)).
  rewrite -Hqmake. con.
  
  move=>HC.
  eapply makeQ_ETr2 in HC;eauto. 
  ssa.
  move: H H0 => Hetr' Hall'.
  eapply to_Trp in Hetr';eauto.
  apply to_Trp2 in Hetr';eauto.
  2: { apply/allP. intro. move/(allP Hall' _). ssa. } 

  apply:to_Tr2_false. apply:Hetr. done. done. done. eauto. apply Hetr'. done.

- move=> s p q i e0 e1 P0 P1 Ms Ds E Q C Hco Heq Hoft.
  inv Hoft. clear H2 H3. inv H1. clear H1. move: H6 H10 => Htp Htq.
  inv Htp. clear H9. move: Htp H5 H10 H11 => _ _ Hplook Htp.
  inv Htq. clear H9. move: Htq H5 H10 H11 => _ _ Hqlook Htq.
  apply lookup_filter2 in Hplook,Hqlook;ssa.   
  move: H1 H2 H H0 => Hppred Hplook Hqpred Hqlook.
  eapply partial_balanced_proj in Hco.
  5: apply Hplook.
  5: apply Hqlook. 
  ssa.
  move: H H0 H1 H2 H3 H4 H5 H6 H7 => Hpmake Hqmake Hpcheck Hqcheck Hpproj Hqproj Hsize Hact Hlin.
  2: inv Heq; ssa.
  2: inv Heq; ssa.
  2: inv Heq; ssa.
  have: p != q. apply/eqP. intro. subst. rewrite /predC in Hqpred. rewrite Hppred in Hqpred. done. move=>Hpq.
  
* have: canEstep2 (makeL x0 (fe (trans p x))) (Sd,i,inl (VSort m)). 
  rewrite -Hpmake. con.
  
  move=>HC. 
  eapply makeQ_ETr3_aux in HC;eauto. 
  ssa.
  move: H H0 => Hetr Hall.
  eapply to_Trp in Hetr;eauto.
  eapply to_Trp3 in Hetr.
  2: { apply/allP. intro. move/(allP Hall _). ssa. } 

* have: canEstep2 (makeL x1 (fe (trans q x))) (Sd,i,inl (VSort m0)).
  rewrite -Hqmake. con.
  
  move=>HC.
  eapply makeQ_ETr3_aux in HC;eauto. 
  ssa.
  move: H H0 => Hetr' Hall'.
  eapply to_Trp in Hetr';eauto.
  apply to_Trp3 in Hetr';eauto.

  apply:to_Tr2_output_false. apply:Hetr. done. done. done. eauto. apply Hetr'. done.


- move=> s p q i e l P0 Ps Ms Ds E Q C Hco Heq Hoft.
  inv Hoft. clear H2 H3. inv H1. clear H1. move: H6 H10 => Htp Htq.
  inv Htp. clear H9. move: Htp H5 H10 H11 => _ _ Hplook Htp.
  inv Htq. clear H9. move: Htq H5 H10 H11 => _ _ Hqlook Htq.
  apply lookup_filter2 in Hplook,Hqlook;ssa.   
  move: H1 H2 H H0 => Hppred Hplook Hqpred Hqlook.
  eapply partial_balanced_proj in Hco.
  5: apply Hplook.
  5: apply Hqlook. 
  ssa.
  move: H H0 H1 H2 H3 H4 H5 H6 H7 => Hpmake Hqmake Hpcheck Hqcheck Hpproj Hqproj Hsize Hact Hlin.
  2: inv Heq; ssa.
  2: inv Heq; ssa.
  2: inv Heq; ssa.
  have: p != q. apply/eqP. intro. subst. rewrite /predC in Hqpred. rewrite Hppred in Hqpred. done. move=>Hpq.
  
* have: canEstep2 (makeL x0 (fe (trans p x))) (Sd,i,inl (VSort m)). 
  rewrite -Hpmake. con.
  
  move=>HC. 
  eapply makeQ_ETr3_aux in HC;eauto. 
  ssa.
  move: H H0 => Hetr Hall.
  eapply to_Trp in Hetr;eauto.
  eapply to_Trp3 in Hetr.
  2: { apply/allP. intro. move/(allP Hall _). ssa. } 

* apply (@size_pred_trans q) in Hsize as Hsize'. 
  apply esize_pred_full_unf in Hsize'.
  apply (@makeL_size_pred x1) in Hsize'. rewrite -Hqmake in Hsize'. ssa.
  have : exists x, x \in Ts. de Ts. eauto. ssa. move: H1 => Hexists.
  have: canEstep2 (makeL x1 (fe (trans q x))) (Sd,i,inr x3.1). 
  rewrite -Hqmake. de x3. econ. eauto.
  
  move=>HC.
  eapply makeQ_ETr3_aux in HC;eauto. 
  ssa.
  move: H1 H2 => Hetr' Hall'.
  eapply to_Trp in Hetr';eauto.
  apply to_Trp3 in Hetr';eauto.

  apply:to_Tr2_output_false. apply:Hetr. done. done. done. eauto. apply Hetr'. done.



- move=> s p q i e l P0 P1 Ms Ds E Q C Hco Heq Hoft.
  inv Hoft. clear H2 H3. inv H1. clear H1. move: H6 H10 => Htp Htq.
  inv Htp. clear H9. move: Htp H5 H10 H11 => _ _ Hplook Htp.
  inv Htq. move: H3 H11 H12 Htq H7 H4 H13 => _ _ _ _ _ Hqlook Htq.
  apply lookup_filter2 in Hplook,Hqlook;ssa.   
  move: H1 H2 H H0 => Hppred Hplook Hqpred Hqlook.
  eapply partial_balanced_proj in Hco.
  5: apply Hplook.
  5: apply Hqlook. 
  ssa.
  move: H H0 H1 H2 H3 H4 H5 H6 H7 => Hpmake Hqmake Hpcheck Hqcheck Hpproj Hqproj Hsize Hact Hlin.
  2: inv Heq; ssa.
  2: inv Heq; ssa.
  2: inv Heq; ssa.
  have: p != q. apply/eqP. intro. subst. rewrite /predC in Hqpred. rewrite Hppred in Hqpred. done. move=>Hpq.
  
* have: canEstep2 (makeL x0 (fe (trans p x))) (Sd,i,inl (VSort m)). 
  rewrite -Hpmake. con.
  
  move=>HC. 
+  eapply makeQ_ETr3_aux in HC;eauto. 
  ssa.
  move: H H0 => Hetr Hall.
  eapply to_Trp in Hetr;eauto.
  eapply to_Trp3 in Hetr.
  2: { apply/allP. intro. move/(allP Hall _). ssa. } 

* have: canEstep2 (makeL x1 (fe (trans q x))) (Sd,i,inl (VLT T' ptcp0)). 
  rewrite -Hqmake. con.
  
  move=>HC. 
  eapply makeQ_ETr3_aux in HC;eauto. 
  ssa.
  move: H H0 => Hetr' Hall'.
  eapply to_Trp in Hetr';eauto.
  eapply to_Trp3 in Hetr'.
  2: { apply/allP. intro. move/(allP Hall' _). ssa. } 

  apply:to_Tr2_output_false. apply:Hetr. done. done. done. eauto. apply Hetr'. done.

- move=> s p q i l0 l1 P0 P1 Ms Ds E Q C Hco Heq Hoft.
  inv Hoft. clear H2 H3. inv H1. clear H1. move: H6 H10 => Htp Htq.
  inv Htp. move: Htp H5 H9 H10 H11 => _ _ Hpin Hplook Htp.
  inv Htq. move: Htq H5  H9 H10 H11 => _ _ Hqin Hqlook Htq.
  apply lookup_filter2 in Hplook,Hqlook;ssa.   
  move: H1 H2 H H0 => Hppred Hplook Hqpred Hqlook.
  eapply partial_balanced_proj in Hco.
  5: apply Hplook.
  5: apply Hqlook. 
  ssa.
  move: H H0 H1 H2 H3 H4 H5 H6 H7 => Hpmake Hqmake Hpcheck Hqcheck Hpproj Hqproj Hsize Hact Hlin.
  2: inv Heq; ssa.
  2: inv Heq; ssa.
  2: inv Heq; ssa.
  have: p != q. apply/eqP. intro. subst. rewrite /predC in Hqpred. rewrite Hppred in Hqpred. done. move=>Hpq.
  
* have: canEstep2 (makeL x0 (fe (trans p x))) (Sd,i,inr l0). 
  rewrite -Hpmake. econ. eauto.
  
  move=>HC. 
  eapply makeQ_ETr3_aux in HC;eauto. 
  ssa.
  move: H H0 => Hetr Hall.
  eapply to_Trp in Hetr;eauto.
  eapply to_Trp3 in Hetr.
  2: { apply/allP. intro. move/(allP Hall _). ssa. } 

* have: canEstep2 (makeL x1 (fe (trans q x))) (Sd,i,inr l1). 
  rewrite -Hqmake. econ. eauto.
  
  move=>HC. 
  eapply makeQ_ETr3_aux in HC;eauto. 
  ssa.
  move: H H0 => Hetr' Hall'.
  eapply to_Trp in Hetr';eauto.
  eapply to_Trp3 in Hetr'.
  2: { apply/allP. intro. move/(allP Hall' _). ssa. } 

  apply:to_Tr2_output_false. apply:Hetr. done. done. done. eauto. apply Hetr'. done.

- move=> s p q i l0 l1 P0 P1 Ms Ds E Q C Hco Heq Hoft.
  inv Hoft. clear H2 H3. inv H1. clear H1. move: H6 H10 => Htp Htq.
  inv Htp. move: Htp H5 H9 H10 H11 => _ _ Hpin Hplook Htp.
  inv Htq. move: Htq H7 H12 H11 H3 H4 H13 => _ _ _ _ _ Hqlook Htq.
  apply lookup_filter2 in Hplook,Hqlook;ssa.   
  move: H1 H2 H H0 => Hppred Hplook Hqpred Hqlook.
  eapply partial_balanced_proj in Hco.
  5: apply Hplook.
  5: apply Hqlook. 
  ssa.
  move: H H0 H1 H2 H3 H4 H5 H6 H7 => Hpmake Hqmake Hpcheck Hqcheck Hpproj Hqproj Hsize Hact Hlin.
  2: inv Heq; ssa.
  2: inv Heq; ssa.
  2: inv Heq; ssa.

  have: p != q. apply/eqP. intro. subst. rewrite /predC in Hqpred. rewrite Hppred in Hqpred. done. move=>Hpq.
  
* have: canEstep2 (makeL x0 (fe (trans p x))) (Sd,i,inr l0). 
  rewrite -Hpmake. econ. eauto.
  
  move=>HC. 
  eapply makeQ_ETr3_aux in HC;eauto. 
  ssa.
  move: H H0 => Hetr Hall.
  eapply to_Trp in Hetr;eauto.
  eapply to_Trp3 in Hetr.
  2: { apply/allP. intro. move/(allP Hall _). ssa. } 

* have: canEstep2 (makeL x1 (fe (trans q x))) (Sd,i,inl (VLT T' ptcp0)). 
  rewrite -Hqmake. con.
  
  move=>HC. 
  eapply makeQ_ETr3_aux in HC;eauto. 
  ssa.
  move: H H0 => Hetr' Hall'.
  eapply to_Trp in Hetr';eauto.
  eapply to_Trp3 in Hetr'.
  2: { apply/allP. intro. move/(allP Hall' _). ssa. } 

  apply:to_Tr2_output_false. apply:Hetr. done. done. done. eauto. apply Hetr'. done.


- move=> s p q i l0 l1 P0 P1 Ms Ds E Q C Hco Heq Hoft.
  inv Hoft. clear H2 H3. inv H1. clear H1. move: H6 H10 => Htp Htq.
  inv Htp. move: Htp H3 H7 H11 H12 H4 H13 => _ _ _ _ _ Hplook Htp.
  inv Htq. move: Htq H3 H7 H11 H12 H4 H13 => _ _ _ _ _ Hqlook Htq.
  apply lookup_filter2 in Hplook,Hqlook;ssa.   
  move: H1 H2 H H0 => Hppred Hplook Hqpred Hqlook.
  eapply partial_balanced_proj in Hco.
  5: apply Hplook.
  5: apply Hqlook. 
  ssa.
  move: H H0 H1 H2 H3 H4 H5 H6 H7 => Hpmake Hqmake Hpcheck Hqcheck Hpproj Hqproj Hsize Hact Hlin.
  2: inv Heq; ssa.
  2: inv Heq; ssa.
  2: inv Heq; ssa.

  have: p != q. apply/eqP. intro. subst. rewrite /predC in Hqpred. rewrite Hppred in Hqpred. done. move=>Hpq.
  
* have: canEstep2 (makeL x0 (fe (trans p x))) (Sd,i,inl (VLT T' ptcp0)). 
  rewrite -Hpmake. econ. eauto.
  
  move=>HC. 
  eapply makeQ_ETr3_aux in HC;eauto. 
  ssa.
  move: H H0 => Hetr Hall.
  eapply to_Trp in Hetr;eauto.
  eapply to_Trp3 in Hetr.
  2: { apply/allP. intro. move/(allP Hall _). ssa. } 

* have: canEstep2 (makeL x1 (fe (trans q x))) (Sd,i,inl (VLT T'0 ptcp0)). 
  rewrite -Hqmake. con.
  
  move=>HC. 
  eapply makeQ_ETr3_aux in HC;eauto. 
  ssa.
  move: H H0 => Hetr' Hall'.
  eapply to_Trp in Hetr';eauto.
  eapply to_Trp3 in Hetr'.
  2: { apply/allP. intro. move/(allP Hall' _). ssa. } 

  apply:to_Tr2_output_false. apply:Hetr. done. done. done. eauto. apply Hetr'. done.


- move=> c p p' i n P0 qs Ms Ds E Q C Hco Heq Hoft.
  inv Hoft. clear H3. inv H1. inv H2. clear H1 H2. move: H6 H10 => Htp Htq.
  inv Htp. move: Htp H4 H8 H9 => _ _ Hplook Htp.
  inv Htq. move: Htq H9 H10 => _ Hqlook Htq.

  apply lookup_filter2 in Hplook. ssa.
  apply lookup_filter_q_2 in Hqlook. ssa.
  apply in_filter_keys3 in H1. ssa. subst.
  eapply balanced_can_step' in Hco as HH.
  3:eauto.
  3:eauto.
  3:econ. 
  ssa.
  eapply step_uniq3 in H6. 2: apply H7. 
  ssa. inv H6. done. ssa.
  apply/allP. intro. move/(allP H3 _). asimpl. rewrite /predC /hrelC negb_involutive. 
  move=>HH2. apply/eqP. intro. subst. rewrite /hrelC HH2 in H4. done.

- move=> c p p' i s P0 qs Ms Ds E Q C Hco Heq Hoft.
  inv Hoft. clear H3. inv H1. inv H2. clear H1 H2. move: H6 H10 => Htp Htq.
  inv Htp. move: Htp H4 H8 H9 => _ _ Hplook Htp.
  inv Htq. move: Htq H9 H10 => _ Hqlook Htq.

  apply lookup_filter2 in Hplook. ssa.
  apply lookup_filter_q_2 in Hqlook. ssa.
  apply in_filter_keys3 in H1. ssa. subst.
  eapply balanced_can_step' in Hco as HH.
  3:eauto.
  3:eauto.
  3:econ. 
  ssa.
  eapply step_uniq3 in H6. 2: apply H7. 
  ssa. inv H6. done. ssa.
  apply/allP. intro. move/(allP H3 _). asimpl. rewrite /predC /hrelC negb_involutive. 
  move=>HH2. apply/eqP. intro. subst. rewrite /hrelC HH2 in H4. done.

- move=> c p p' i n P0 qs Ms Ds E Q C Hco Heq Hoft.
  inv Hoft. clear H3. inv H1. inv H2. clear H1 H2. move: H6 H10 => Htp Htq.
  inv Htp. move: Htp H2 H5 H9 H10 => _ _ _ Hplook Htp.
  inv Htq. move: Htq H9 H10 H11 =>  _ _ Hqlook Htq.


  apply lookup_filter2 in Hplook;ssa.   
  move: H H0 => Hppred Hplook.
  eapply partial_balanced_proj in Hco as Hco''.
  5: apply Hplook.
  5: apply Hplook. 
  ssa.
  move: H H0 H1 H2 H3 H4 H5 H6 H7 => Hpmake Hqmake Hpcheck Hqcheck Hpproj Hqproj Hsize Hact Hlin.
  2: inv Heq; ssa.
  2: inv Heq; ssa.
  2: inv Heq; ssa.

  apply (@size_pred_trans p) in Hsize as Hsize'. 
  apply esize_pred_full_unf in Hsize'.
  apply (@makeL_size_pred x1) in Hsize'. rewrite -Hqmake in Hsize'. ssa.
  have : exists x, x \in Ts. de Ts. eauto. ssa. move: H1 => Hexists. de x2.
  apply lookup_filter_q_2 in Hqlook. ssa.
  apply in_filter_keys3 in H1. ssa. subst.
  eapply balanced_can_step' in Hco as HH.
  3:eauto.
  3:eauto.
  3:econ. 
  ssa.
  eapply step_uniq3 in H6. 2: apply H7. 
  ssa. inv H6. done. ssa.
  apply/allP. intro. move/(allP H3 _). asimpl. rewrite /predC /hrelC negb_involutive. 
  move=>HH2. apply/eqP. intro. subst. rewrite /hrelC HH2 in H4. done. eauto.





- move=> c p p' i n P0 qs Ms Ds E Q C Hco Heq Hoft.
  inv Hoft. clear H3. inv H1. inv H2. clear H1 H2. move: H6 H10 => Htp Htq.
  inv Htp. move: Htp H2 H5 H9 H10 => _ _ _ Hplook Htp.
  inv Htq. move: Htq H10 H9 H11 =>  _ _ Hqlook Htq.


  apply lookup_filter2 in Hplook;ssa.   
  move: H H0 => Hppred Hplook.
  eapply partial_balanced_proj in Hco as Hco''.
  5: apply Hplook.
  5: apply Hplook. 
  ssa.
  move: H H0 H1 H2 H3 H4 H5 H6 H7 => Hpmake Hqmake Hpcheck Hqcheck Hpproj Hqproj Hsize Hact Hlin.
  2: inv Heq; ssa.
  2: inv Heq; ssa.
  2: inv Heq; ssa.

  apply (@size_pred_trans p) in Hsize as Hsize'. 
  apply esize_pred_full_unf in Hsize'.
  apply (@makeL_size_pred x1) in Hsize'. rewrite -Hqmake in Hsize'. ssa.
  have : exists x, x \in Ts. de Ts. eauto. ssa. move: H1 => Hexists. de x2.
  apply lookup_filter_q_2 in Hqlook. ssa.
  apply in_filter_keys3 in H1. ssa. subst.
  eapply balanced_can_step' in Hco as HH.
  3:eauto.
  3:eauto.
  3:econ. 
  ssa.
  eapply step_uniq3 in H6. 2: apply H7. 
  ssa. inv H6. done. ssa.
  apply/allP. intro. move/(allP H3 _). asimpl. rewrite /predC /hrelC negb_involutive. 
  move=>HH2. apply/eqP. intro. subst. rewrite /hrelC HH2 in H4. done. eauto.

- move=> c p p' i s P0 qs Ms Ds E Q C Hco Heq Hoft.
  inv Hoft. clear H3. inv H1. inv H2. clear H1 H2. move: H6 H10 => Htp Htq.
  inv Htp. move: Htp H4 H8 H9 => _ _ Hplook Htp.
  inv Htq. move: Htq H9 H10 H11 => _ _ Hqlook Htq.
  apply lookup_filter2 in Hplook. ssa.
  apply lookup_filter_q_2 in Hqlook. ssa.
  apply in_filter_keys3 in H1. ssa. subst.
  eapply balanced_can_step' in Hco as HH.
  3:eauto.
  3:eauto.
  3:econ. 
  ssa.
  eapply step_uniq3 in H6. 2: apply H7. 
  ssa. inv H6. done. ssa.
  apply/allP. intro. move/(allP H3 _). asimpl. rewrite /predC /hrelC negb_involutive. 
  move=>HH2. apply/eqP. intro. subst. rewrite /hrelC HH2 in H4. done.

- move=> c p p' i s P0 qs Ms Ds E Q C Hco Heq Hoft.
  inv Hoft. clear H3. inv H1. inv H2. clear H1 H2. move: H6 H10 => Htp Htq.
  inv Htp. move: Htp H4 H8 H9 => _ _ Hplook Htp.
  inv Htq. move: Htq H9 H10 => _ Hqlook Htq.
  apply lookup_filter2 in Hplook. ssa.
  apply lookup_filter_q_2 in Hqlook. ssa.
  apply in_filter_keys3 in H1. ssa. subst.
  eapply balanced_can_step' in Hco as HH.
  3:eauto.
  3:eauto.
  3:econ. 
  ssa.
  eapply step_uniq3 in H6. 2: apply H7. 
  ssa. inv H6. done. ssa.
  apply/allP. intro. move/(allP H3 _). asimpl. rewrite /predC /hrelC negb_involutive. 
  move=>HH2. apply/eqP. intro. subst. rewrite /hrelC HH2 in H4. done.


- intros. intro. inv H1.
  apply msg_coin in H9,H13. inv H6. clear H6.
  rewrite !dom_filter_keys !mem_filter in H9 H13. ssa.
  by rewrite /predC H6 in H2. 

- intros. intro. inv H3. eapply H0. 3:eauto.
 *  move: H1 H5. clear. move=> + Hw. rewrite /partial_balanced. ssa.
    subst.
    econ. econ. econ. econ. con.

    2: {  con. 
    instantiate (1:= insertL1 x E1). 
     
    instantiate (1:= predU  (pred_dom (dom x) shiftL1 x0) (fun x => if x is schlT (var_schl 0) _ then true else false)).

    rewrite /insertL1 /insert_shift /insert. 
          rewrite filter_keys_cat.
f_equal.  erewrite filter_keys_eq. erewrite filter_keys_predT. rewrite /env.insert. f_equal.
rewrite map_keys_filter_keys. apply filter_keys_eq. intro. rewrite dom_map_keys. intros. tunf.
de (mapP H0). subst. de x4. rewrite orbC /=. done. de s. lia.

intro. ssa.

          ssa. tunf. rewrite /dom -map_comp in H0. de (mapP H0). subst.
          rewrite orbC //=.
          rewrite -filter_q_insertQ_f_aux. econ. } 

*
  move: H => H13.
  move: Hw => H2.
  move: is_true_true is_true_true is_true_true is_true_true is_true_true is_true_true => H H0 H1 H3 H4 H5.
  move: is_true_true is_true_true is_true_true is_true_true is_true_true is_true_true is_true_true => H6 H7 H8 H9 H10 H11 H12.
  rewrite /balanced in H13 *. ssa.
  inv H2. ssa.
  inv H19.
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

 *  move: H2 H5. clear. rewrite /SUB_domLQ. ssa. move: H5 => Hw.
    rewrite /insertL1. rewrite /only_schl. rewrite /insert_shift /dom map_cat all_cat.
    ssa. rewrite /map_keys -map_comp. 
    apply/allP. intro. ssa. de (mapP H3). subst. done.
    apply/allP. intro. ssa. de (mapP H3). subst. de (mapP H4).
    subst. ssa. 
    eapply map_f in H5. apply (allP H) in H5. de x. de s.
    apply uniq_insertL1.  
    inv H5. ssa.
    inv H6. rewrite dom_makeLs. inv H3. ssa. subst. rewrite /dom -map_comp.
    rewrite map_inj_uniq. done. 
    intro. ssa. inv H8. done.
    apply: uniq_dom_insertQ. done.

    inv H5. ssa. inv H6. rewrite /dom /makeQs. rewrite -map_comp.
    inv H3. ssa. subst. 
    rewrite -!map_comp. rewrite map_inj_uniq. done.
    intro. ssa. inv H8.

    intros. rewrite dom_insertL1 in H3. rewrite dom_insertQ.
    rewrite mem_cat in H3. rewrite mem_cat. de (orP H3).
    left.
    have : dom E1 = dom Q1.
    inv H5. ssa. inv H8. rewrite dom_makeLs. rewrite /makeQs. rewrite /dom -map_comp.
    apply/eq_in_map. intro. ssa. 
    move=>Hdom. rewrite -Hdom.
    de (mapP H4). inv H7. apply/map_f. 
    apply/mapP. econ. eauto. done.
    right. de (mapP H4). de x. inv H7. asimpl. apply H2 in H6.
    rewrite dom_map_keys.
    apply/mapP. econ.  eauto. done.

- intros. intro. inv H3. apply:H0. eauto. done. eauto.

- intros. move: H1 H2 => H1 H2. intro.  inv H3. inv H6. inv H7. inv H8. apply:H0. 
  3:eauto.
 * move: H1. clear. 
   rewrite /partial_balanced.
    ssa. subst.
    econ. econ. econ. econ. con. eauto.
    rewrite !filter_keys2. con. eauto. 
    rewrite filter_q2. eauto.
    move: H2. clear. rewrite /SUB_domLQ. ssa.
    rewrite dom_filter_keys. apply filter_uniq. done. rewrite dom_filter_q. done.
    move=> s p. rewrite dom_filter_keys mem_filter dom_filter_q. ssa.
Qed.



Lemma Error_dec : forall P, Error P \/ ~ Error P.
Proof. 
intros. rewrite errorP. de (error P).
Qed.

Lemma OFT_not_error2 : forall P, Error P -> forall Ms Ds E Q C, env_coherent E Q -> EQ_domLQ E Q -> ~ OFT Ms Ds P E Q C.
Proof.
intros. apply:OFT_not_error;ssa.
apply coherent_to_partial. done.
move: H1. rewrite /EQ_domLQ /SUB_domLQ. ssa.
intros. rewrite -H4. done. inv H1.
move:H1. rewrite /EQ_domLQ /SUB_domLQ. ssa.
intros. rewrite -H4. done.
Qed.

Lemma OFT_not_error3 : forall P Ms Ds E Q C, env_coherent E Q -> EQ_domLQ E Q ->  OFT Ms Ds P E Q C -> ~ Error P.
Proof.
intros. de (Error_dec P). eapply OFT_not_error2 in H1;ssa.
Qed.



Theorem OFT_not_error_struct : forall P Ms Ds Ps E Q C L, side_conds3  Ds Ps Ms P E Q L -> OFT Ms Ds P E Q C -> ~ Error_struct P.
Proof.
intros. intro. inv H1. ssa.
have: OFT Ms Ds x E Q C.
apply -> OFT_cong;inv H;ssa.
2:eauto. done. 
move: H9. rewrite /only_var_val /only_vars. ssa.
inv H7. ssa.
intros. eapply OFT_not_error3 in x0;ssa.
inv H;ssa.
apply:env_coherent_as1.  done. eauto.
inv H. ssa.
Qed.

Corollary OFT_not_error_sem : forall P P' D Ms Ds E Q C L, side_conds3  Ds D Ms P E Q L -> OFT Ms Ds P E Q C -> Sem 
D P P' -> ~ Error_struct P'.
Proof.
intros. 
intro.
eapply subject_reduction_final in H1.
2:eapply H.
ssa.
eapply OFT_not_error_struct in H1. ssa.
eauto. 
eauto.
Qed.

Print Assumptions OFT_cong.
Print Assumptions subject_reduction_final.
Print Assumptions subject_reduction_empty.
Print Assumptions OFT_not_error_struct.
