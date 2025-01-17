From mathcomp Require Import all_ssreflect zify.
 Require Export MPSTSR.CoTypes.coProj.
Require Import Paco.paco.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Let eqs := (coLocal.eqs, coGlobal.eqs). 



Require Import Program. 
From Equations Require Import Equations. 




Variant part_ofF (p : ptcp) (R : gType -> Prop)  : gType -> Prop :=
| po2_msg a u g0 : comp_dir p a -> part_ofF p R (GMsg a u g0)
| po2_msg2 a u g0 : R g0 -> part_ofF p R (GMsg a u g0)
| po2_branch a gs : comp_dir p a -> part_ofF p R (GBranch a gs)
| po2_branch2 a g gs : In g gs -> (R \o snd) g ->  part_ofF p R (GBranch a gs).
Hint Constructors part_ofF. 

Notation part_ofFU := (fun p => ApplyF1 full_unf \o part_ofF p).


Inductive part_of2 (p : ptcp) : gType -> Prop := 
| part_of2C g : part_ofFU p (part_of2 p) g -> part_of2 p g.
Hint Constructors part_of2.

Lemma part_of2_ind2
     : forall (p : ptcp) (P : gType -> Prop),
       (forall (a : action) (u : value) (g0 g' : gType), comp_dir p a -> full_unf g' = (GMsg a u g0) -> P g') ->
       (forall (a : action) (u : value) (g0 g' : gType), ~ comp_dir p a -> part_of2 p g0 -> P g0 -> full_unf g' = (GMsg a u g0) -> P g') ->
       (forall (a : action) (g' : gType)  (gs : seq (nat * gType)), comp_dir p a -> full_unf g' = GBranch a gs -> P g') ->
       (forall (a : action) (g : nat * gType) g' (gs : seq (nat * gType)),  ~ comp_dir p a -> In g gs -> part_of2 p g.2 -> P g.2 -> full_unf g' = GBranch a gs -> P g') ->
       forall g : gType, part_of2 p g -> P g.
Proof.
intros.  move : g H3. fix IH 2. intros. destruct H3. inv H3.  
inv H4. 
apply/H. eauto. eauto. 
destruct (comp_dir p a) eqn:Heqn. 
apply/H. 2 : eauto. comp_disc. 
apply/H0. 4 : eauto. comp_disc. done. auto. 
apply/H1. 2 : eauto. done. 
destruct (comp_dir p a) eqn:Heqn. 
apply/H1. 2 : eauto. comp_disc.
apply/H2. 5 : eauto. comp_disc. eauto. eauto. eauto. 
Qed.


Lemma part_of2_unf : forall p e, part_of2 p e -> part_of2 p (full_unf e). 
Proof. intros. inv H. inv H0. con. con. rewrite full_unf_idemp //=. 
Qed.

Lemma part_of2_unf2 : forall p e, part_of2 p (full_unf e) -> part_of2 p e. 
Proof. intros. inv H. inv H0. con. con. rewrite full_unf_idemp in H1=>//=. 
Qed.

Lemma part_of2_iff : forall p g, part_of2 p g <-> part_of2 p (full_unf  g). 
Proof. intros. split. apply/part_of2_unf. apply/part_of2_unf2. 
Qed.

Lemma not_part2_msg : forall p a v g, ~ part_of2 p (GMsg a v g) -> ~ part_of2 p g.
Proof.  
intros. intro.  apply/H. con.  con. constructor 2. done. 
Qed.

Lemma not_part2_msg2 : forall p a v g, ~ part_of2 p (GMsg a v g) -> ~ comp_dir p a.
Proof.  
intros. intro.  apply/H. con. con. con. eauto. 
Qed.

Lemma not_part2_branch : forall p a g (gs : seq (nat * gType)), ~ part_of2 p (GBranch a gs) -> In g gs -> ~ part_of2 p g.2.
Proof.  
intros. intro.  apply/H. con. con. rewrite /full_unf /=. eauto.  
Qed.

Lemma not_part2_branch2 : forall p a (gs : seq (nat * gType)), ~ part_of2 p (GBranch a gs) -> ~ comp_dir p a.  
Proof.  
intros. intro.  apply/H. con. con. con. eauto. 
Qed.

Hint Resolve not_part2_msg not_part2_msg2  not_part2_branch  not_part2_branch2. 






Variant part_of_allF (p : ptcp) (R : gType -> Prop)  : gType -> Prop :=
| poa2_msg a u g0 : comp_dir p a -> part_of_allF p R (GMsg a u g0)
| poa2_msg2 a u g0 : R g0 -> part_of_allF p R (GMsg a u g0)
| poa2_branch a gs : comp_dir p a -> part_of_allF p R (GBranch a gs)
| poa2_branch2 a gs : (forall g, In g gs -> (R \o snd) g) ->  part_of_allF p R (GBranch a gs).
Hint Constructors part_of_allF. 

Notation part_of_allFU := (fun p => ApplyF1 full_unf \o part_of_allF p).


Inductive part_of_all2 (p : ptcp) : gType -> Prop := 
| part_of_allC g : part_of_allFU p (part_of_all2 p) g -> part_of_all2 p g.
Hint Constructors part_of_all2.

Lemma part_of_all2_ind2
     : forall (p : ptcp) (P : gType -> Prop),
       (forall (a : action) (u : value) (g0 g' : gType), comp_dir p a -> full_unf g' = (GMsg a u g0) -> P g') ->
       (forall (a : action) (u : value) (g0 g' : gType), ~ comp_dir p a -> part_of_all2 p g0 -> P g0 -> full_unf g' = (GMsg a u g0) -> P g') ->
       (forall (a : action) (g' : gType)  (gs : seq (nat * gType)), comp_dir p a -> full_unf g' = GBranch a gs -> P g') ->
       (forall (a : action) (g' : gType) (gs : seq (nat * gType)),  ~ comp_dir p a -> (forall g, In g gs -> part_of_all2 p g.2) -> (forall g, In g gs -> part_of_all2 p g.2 -> P g.2) -> full_unf g' = GBranch a gs -> P g') ->
       forall g : gType, part_of_all2 p g -> P g.
Proof.
intros.  move : g H3. fix IH 2. intros. destruct H3. inv H3.  
inv H4. 
apply/H. eauto. eauto. 
destruct (comp_dir p a) eqn:Heqn. 
apply/H. 2 : eauto. comp_disc. 
apply/H0. 4 : eauto. comp_disc. done. auto. 
apply/H1. 2 : eauto. done. 
destruct (comp_dir p a) eqn:Heqn. 
apply/H1. 2 : eauto. comp_disc. 
apply/H2. 4 : eauto. comp_disc. clear H5.
intros.  apply/H6. apply H5. intros. apply IH. apply H6. apply H7. 
Qed.


Lemma part_of_all2_unf : forall p e, part_of_all2 p e -> part_of_all2 p (full_unf e). 
Proof. intros. inv H. inv H0. con. con. rewrite full_unf_idemp //=. 
Qed.

Lemma part_of_all2_unf2 : forall p e, part_of_all2 p (full_unf e) -> part_of_all2 p e. 
Proof. intros. inv H. inv H0. con. con. rewrite full_unf_idemp in H1=>//=. 
Qed.

Lemma part_of_all2_iff : forall p g, part_of_all2 p g <-> part_of_all2 p (full_unf  g). 
Proof. intros. split. apply/part_of_all2_unf. apply/part_of_all2_unf2. 
Qed.


Lemma not_part_all2_msg : forall p a v g, ~ part_of_all2 p (GMsg a v g) -> ~ part_of_all2 p g.
Proof.  
intros. intro.  apply/H. con.  con. constructor 2. done. 
Qed.

Lemma not_part_all2_msg2 : forall p a v g, ~ part_of_all2 p (GMsg a v g) -> ~ comp_dir p a.
Proof.  
intros. intro.  apply/H. con. con. con. eauto. 
Qed.


Lemma not_part_all2_branch2 : forall p a (gs : seq (nat * gType)), ~ part_of_all2 p (GBranch a gs) -> ~ comp_dir p a.  
Proof.  
intros. intro.  apply/H. con. con. con. eauto. 
Qed.

Hint Resolve not_part_all2_msg not_part_all2_msg2    not_part_all2_branch2. 

(*Using (forall x , In x .... generates a stronger induction principle*)

Inductive project_gen (p : ptcp) (R : gType ->  lType -> Prop) : gType -> lType -> Prop :=
 | project_msg_s g0 a e0 u d : comp_dir p a = Some d ->
                                  R g0 e0 -> project_gen p R (GMsg a u g0) (EMsg d (action_ch a) u e0) (*Assumption does not have to build something*)
 | project_msg_n g0 a e0 u : comp_dir p a = None ->
                                 R g0 e0 -> part_of_all2 p g0 ->  project_gen p R (GMsg a u g0) e0(*assumption has to build something*)
 | project_gen_branch_f (gs : seq (nat * gType)) (es : seq (nat * lType)) a d :  comp_dir p a = Some d -> size gs = size es ->
                                        (forall p, In p (zip gs es) ->  p.1.1 = p.2.1 /\  R p.1.2 p.2.2 ) -> project_gen p R (GBranch a gs) (EBranch d (action_ch a) es)
 | project_gen_branch_o g (gs : seq (nat * gType))  a e : comp_dir p a = None -> In g gs ->  (*We need list to be non -empty otherweise it projects to anything*)
                                    (forall g', In g' gs ->  part_of_all2 p g'.2 /\  R g'.2 e) ->  project_gen p R (GBranch a gs) e
 | project_gen_end g : ~ part_of2 p g -> gInvPred g -> project_gen p R g EEnd. (*Need to preserve that all projectable g's satisfy gInvPred g*)
Hint Constructors project_gen. 

Notation UnfProj := (ApplyF full_unf full_eunf).

Definition Project g p e := paco2 (UnfProj \o (project_gen p)) bot2 g e. 

Lemma project_gen_mon p: monotone2 (project_gen p). 
Proof.
move => x0 x1. intros. induction IN;try done.
con;eauto. con;eauto. con;eauto. econstructor;eauto.  
intros. ssa. move/H1 : H2.  ssa. apply/LE. move/H1 : H2. ssa. econ;eauto.
ssa. move/H1 : H2. ssa. move/H1 : H2. ssa. eauto.
Qed.


Hint Resolve project_gen_mon : paco. 





Lemma part_of2_or_end : forall p g e r, paco2 (UnfProj \o project_gen p) r g e -> part_of_all2 p g \/ full_eunf e = EEnd. 
Proof. 
intros. punfold H. inv H;eauto.  rewrite part_of_all2_iff. 
inv H0. 
left. con.  con. con. comp_disc. 
left. con. con. constructor 2. done. 
left. repeat con.  comp_disc. 
left. con. con. econstructor 4. 
intros. move/H4 : H5. ssa. 
auto. 
Qed.



Lemma ICpart_of1 : forall p g gc, part_of2 p g -> gUnravel2 g gc -> part_of p gc.
Proof. 
intros. 
elim/part_of2_ind2 : H gc H0;intros. 
punfold H1. inv H1. rewrite H0 in H2. inv H2. eauto. 
punfold H3. inv H3. rewrite H2 in H4. inv H4. pclearbot. eauto. 
punfold H1. inv H1. rewrite H0 in H2. inv H2. eauto. 
punfold H4. inv H4. rewrite H3 in H5. inv H5. 
move : (@In_zip _ _ g0 gs ecs H0 H8) =>[]. ssa. 
econstructor 4. eauto. 
apply/H2. move/ForallP : H10. intros. 
apply H10 in H7. ssa. pc. done. 
Qed.

Lemma ICpart_of2 : forall p gc g, part_of p gc -> gUnravel2 g gc -> part_of2 p g.
Proof. 
intros. 
elim/part_of_ind2 : H g H0;intros. 
punfold H0. inv H0. con. con. inv H1. eauto. 
punfold H2. inv H2. inv H3. pclearbot. con. con. 
rewrite -H4. constructor 2. eauto. 
punfold H0. inv H0. con. con. inv H1. eauto. 
punfold H3. inv H3. con. con. inv H4. injt.
move : (@In_zip2 _ _ g es gs H0 H8)=>[]. ssa. 

econstructor 4.  eauto. apply/H2.
move/ForallP : H9. intro. apply H9 in H7. ssa. pc. done. 
Qed.

Lemma ICpart_of_iff : forall p g gc,  gUnravel2 g gc  ->  part_of2 p g <-> part_of p gc.
Proof. intros. split;intros. apply/ICpart_of1. eauto. eauto. 
apply/ICpart_of2. eauto. eauto. 
Qed.

Lemma ICpart_of_all1 : forall p g gc, part_of_all2 p g -> gUnravel2 g gc -> part_of_all p gc.
Proof. 
intros. 
elim/part_of_all2_ind2 : H gc H0;intros. 
punfold H1. inv H1. rewrite H0 in H2. inv H2. eauto. 
punfold H3. inv H3. rewrite H2 in H4. inv H4. pclearbot. eauto. 
punfold H1. inv H1. rewrite H0 in H2. inv H2. eauto.
punfold H3. inv H3. rewrite H2 in H4. inv H4. 
econstructor 4. intros.
move : (@In_zip2 _ _ g0 gs ecs H5 H7)=>[]. ssa. 

 apply/H1. eauto. apply/H0. done. forallApp H9 H8. case=>[] //=. 
ssa. pc. done. 
Qed.


Lemma ICpart_of_all2 : forall p gc g, part_of_all p gc -> gUnravel2 g gc -> part_of_all2 p g.
Proof. 
intros. 
elim/part_of_all_ind : H g H0;intros. 
punfold H0. inv H0. con. con. inv H1. eauto. 
punfold H1. inv H1. inv H2. pclearbot. con. con. rewrite -H3. 
constructor 2. eauto. 
punfold H0. inv H0. inv H1. con. con. rewrite -H2. econstructor. done. 
punfold H1. inv H1. con. con. inv H2. injt. econstructor 4. 
intros.
move: (@In_zip _ _ g0 es gs H4 H6)=>[].  ssa. apply/H0.  eauto. 
forallApp H7 H8. case=>[] //=.  ssa. pc. done. 
Qed.

Lemma ICpart_of_all2_iff : forall p g gc,  gUnravel2 g gc  ->  part_of_all2 p g <-> part_of_all p gc.
Proof. intros. split;intros. apply/ICpart_of_all1. eauto. done. 
apply/ICpart_of_all2. eauto. done. 
Qed.

Lemma unravel_finite : forall g gc, g << (UnfgUnravel \o gUnravel2_gen) >> gc -> Finite gc. 
Proof. 
pcofix CIH. intros. 
punfold H0. inv H0. pfold. inv H;pclearbot.  con. eauto. 
con. apply/ForallP=> x xIn. right. 
move : (@In_zip2 _ _ x es ecs xIn H2)=>[]. ssa. forallApp H3 H5.  case=>[] //=. 
eauto. ssa. pc. eauto. con. 
Qed.




Lemma gInvPred_msg : forall a u g0, gInvPred (GMsg a u g0) -> gInvPred g0. 
Proof. 
intros. punfold H. inv H. inv H0. pclearbot. done. 
Qed.

Lemma gInvPred_branch : forall a g gs, gInvPred (GBranch a gs) -> In g gs ->  gInvPred g.2. 
Proof. 
intros. punfold H. inv H. inv H1. forallApp H3 H0. case=>[] //=. 
Qed.

Hint Resolve gInvPred_msg gInvPred_branch. 



Lemma Project_not_part : forall g p, Project g p EEnd  ->  ~  part_of2 p g. 
Proof. intros. intro. 
elim/part_of2_ind2 : H0 H;intros. punfold H1. inv H1.  rewrite H0 in H2. inv H2;try comp_disc. 
apply/H3. con. con. con. done. 
punfold H3. inv H3. rewrite H2 in H4. inv H4;pclearbot;try comp_disc. 
apply/H1. pfold. con. con. rewrite -part_of2_iff. eauto. 
rewrite -gInvPred_unf_iff. eauto. 
punfold H1. inv H1. rewrite H0 in H2. inv H2. comp_disc. 
apply/H3. con. con. con. done. 
punfold H4. inv H4. rewrite H3 in H5. inv H5;try comp_disc;pclearbot. 
move/H11 : H0. ssa. pclearbot. move : H6.  cbn. move/H2. done. 
apply/H2. pfold. con. con. rewrite -part_of2_iff. eauto. 
rewrite -gInvPred_unf_iff. eauto. 
Qed.

Lemma ICProject : forall p g e gc ec, Project g p e -> gUnravel2 g gc -> lUnravel2 e ec -> CProject gc p ec. 
Proof. 
move => p. pcofix CIH. intros. apply part_of2_or_end in H0 as Hor. 
destruct Hor. 
punfold H0. inv H0;clear H0. 
punfold H1. inv H1;clear H1.  
punfold H2. inv H2;clear H2.  
elim/part_of_all2_ind2 : H H3 gc ec H0 H1;intros. 
- rewrite H0 in H3,H1,H2. inv H1;clear H1;pclearbot. 
  inv H3;try comp_disc;pclearbot;eauto. 
  rewrite -H7 in H2. inv H2;pclearbot. pfold. eauto. 
  rewrite -H1 in H2. inv H2. pfold. apply/cproject_gen_end. 
  rewrite -ICpart_of_iff;eauto. pfold. con. con. eauto.
  pfold.  con. left. apply/unravel_finite. eauto. 
- rewrite H2 in H3,H4. inv H3; try comp_disc;pclearbot. 
  inv H4;clear H4;pclearbot. pfold. con=>//=. left. apply/H1.  
  punfold H11. inv H11. rewrite full_eunf_idemp //= in H4. 
  punfold H13. inv H13. done. apply/ICpart_of_all2_iff;eauto. 
  rewrite -H6 in H5. inv H5. pfold. apply cproject_gen_end. 
  rewrite -ICpart_of_iff;eauto. pfold. con. done. 
  apply/unravel_finite. pfold. con. eauto. instantiate (1 := GMsg a u g0). done. 
- rewrite H0 in H1,H2,H3. inv H1. inv H3;pclearbot; try comp_disc. 
  rewrite -H7 in H2. inv H2. pfold. con=>//=. lia. 
  suff : Forall (fun p0 => p0.1.1 = p0.2.1 /\ upaco2 (cproject_gen p) r p0.1.2 p0.2.2) (zip ecs ecs0). 
  move/ForallP. done. 
  clear H1 H3 H2 H7 H0. 
  have : Forall (fun p0 => p0.1.1 = p0.2.1 /\ upaco2 (UnfProj \o project_gen p) bot2 p0.1.2 p0.2.2) (zip gs es). 
  apply/ForallP. eauto. clear H11.
  elim : gs ecs es ecs0 H6 H10 H14 H8 H15. 
  case=>//=. case=> //=. case=>//=. 
  move => a0 l IH. case=>//=. move => a1 l0.  case=>//=. 
  move => a2 l1. case=>//=. move => a3 l2. move=> [] Heq [] Heq0 [] Heq1. 
  intros. inv H8. inv H15. inv x. pclearbot. simpl in *. con;eauto. ssa. 
  rewrite -H2 -H4 //=. pc. eauto.
  rewrite -H4 in H2. inv H2. pfold. apply/cproject_gen_end. 
  rewrite -ICpart_of_iff;eauto. pfold. con. eauto. 
  apply/unravel_finite. pfold. con. instantiate (1 := GBranch a gs). done. 
- rewrite H2 in H3,H4. inv H4;clear H4.
  inv H3;try comp_disc;try done. 
  pfold.
  move : (@In_zip _ _ g0 gs ecs H9 H8)=>[]. ssa. 
  econstructor=>//=. eauto. clear H9 H4 H6.  
  apply/ForallP. clear H7. 
have : forall g ,
       In g gs ->
       forall gc ec,
       gUnravel2_gen (upaco2 (UnfgUnravel \o gUnravel2_gen) bot2) (full_unf g.2) gc ->
       lUnravel2_gen (upaco2 (UnflUnravel \o lUnravel2_gen) bot2) (full_eunf e) ec -> gc <<( r) (cproject_gen p) >> ec.
  intros. apply/H1;eauto. move/H12 : H4. ssa. pclearbot. punfold H9. inv H9. 
  rewrite full_eunf_idemp in H11. done. clear H1. clear H12. 
  move/ForallP. clear H2 H3.  move/ForallP : H0.  
  elim : gs ecs H8 H10. 
  case=>//=. move=> a0 l IH. case=>//=. move=> a1 l0 [] Heq Hfor Hfor2 Hfor3. inv Hfor. inv Hfor2. inv Hfor3. pclearbot. simpl in *. con;eauto.  ssa. apply/ICpart_of_all2_iff;eauto. pc.  done. left. apply/H7;eauto. pc.
  punfold H1. inv H1. 
  
  rewrite -H4 in H5. inv H5. pfold. apply/cproject_gen_end. 
  rewrite -ICpart_of_iff;eauto. pfold. con. con=>//=. 
  apply/unravel_finite. pfold. con. instantiate (1 := GBranch a gs). con=>//=. 
- punfold H0. inv H0. punfold H2.  inv H2. rewrite H in H3,H4.  inv H4.
  pfold. con. 
  inv H0. 
  have : Project g p EEnd. pfold. con. simpl.  cbn. rewrite -H. done. 
  intros. rewrite -ICpart_of_iff;eauto. apply/Project_not_part. done. 
  apply/unravel_finite. eauto. 
Qed.

Lemma Project_unfg : forall g p e r, paco2  (UnfProj \o project_gen p) r (full_unf g) e -> paco2  (UnfProj \o project_gen p) r  g e. 
Proof. 
intros. punfold H. inv H. pfold. con. rewrite full_unf_idemp in H0. done. 
Qed.

Lemma Project_eunf : forall g p e r, paco2  (UnfProj \o project_gen p) r g (full_eunf e) -> paco2  (UnfProj \o project_gen p) r  g e. 
Proof. 
intros. punfold H. inv H. pfold. con. rewrite full_eunf_idemp in H0. done. 
Qed.

Lemma Project_eunf2 : forall g p e r, paco2  (UnfProj \o project_gen p) r g e -> paco2  (UnfProj \o project_gen p) r  g (full_eunf e). 
Proof. 
intros. punfold H. inv H. pfold. con. rewrite full_eunf_idemp //=.  
Qed.

Lemma gUnravel2_Rol : forall g gc, gUnravel2 g gc -> gInvPred g. 
Proof. 
pcofix CIH. intros. punfold H0. inv H0. pfold. con. inv H;pclearbot.
con. eauto. con;eauto. apply/ForallP=> x xIn. eauto. right.
move : (@In_zip _ _ x es ecs xIn H2)=>[]. ssa. 
forallApp H3 H5. case=>[] //=. ssa. eauto. pc. eauto.
con. 
Qed.

Lemma gUnravel2_iff : forall e ec r,  e <<( r) (UnfgUnravel \o gUnravel2_gen) >> ec <-> (full_unf e) <<( r) (UnfgUnravel \o gUnravel2_gen) >> ec.
Proof. intros. split;intros. punfold H. inv H. pfold. con. rewrite full_unf_idemp. done. 
punfold H. inv H. pfold. con. rewrite full_unf_idemp in H0. done. 
Qed.

Lemma lUnravel2_iff : forall e ec r,  e <<( r) (UnflUnravel \o lUnravel2_gen) >> ec <-> (full_eunf e) <<( r) (UnflUnravel \o lUnravel2_gen) >> ec.
Proof. intros. split;intros. punfold H. inv H. pfold. con. rewrite full_eunf_idemp. done. 
punfold H. inv H. pfold. con. rewrite full_eunf_idemp in H0. done. 
Qed.


Ltac pc := pclearbot.

Lemma In_zip_and : forall (A B : Type) (a : A) (b : B) l0 l1, In (a,b) (zip l0 l1) -> In a l0 /\ In b l1. 
Proof. 
move => A B a b. elim. case=>//=. 
move => a0 l IH. case=>//=. 
intros. destruct H. inv H. auto. move/IH : H. ssa. 
Qed.

Lemma CIProject : forall p g e gc ec, CProject gc p ec -> gUnravel2 g gc -> lUnravel2 e ec -> Project g p e. 
Proof. 
move => p. pcofix CIH. intros. apply part_of_or_end in H0 as H0'. destruct H0'. 
elim/part_of_all_ind2 : H ec g e H0 H1 H2;intros. 
- punfold H1. inv H1;clear H1. 
  punfold H0. inv H0;pclearbot;try comp_disc.  punfold H2. inv H2. inv H1;pclearbot.
  inv H3. pfold. con. rewrite -H5 -H4. con=>//=. right. pclearbot. eauto.    
  punfold H2. inv H2. apply/Project_eunf. inv H5. pfold. con. con. 
  rewrite ICpart_of_iff;eauto. pfold. con. rewrite full_unf_idemp. done. 
  rewrite -gInvPred_unf_iff. apply/gUnravel2_Rol. pfold.  con. eauto. 
- punfold H3. inv H3. apply/Project_unfg. inv H5;pc.
  punfold H2. inv H2;try comp_disc;pc. 
  pfold. con. con=>//=. left. apply/H1;eauto. rewrite -lUnravel2_iff.   eauto. 
  apply/ICpart_of_all2_iff;eauto.  
  punfold H4. inv H4. apply/Project_eunf. inv H10.
  pfold. con. apply/project_gen_end. rewrite ICpart_of_iff;eauto.
  rewrite /full_unf /=.  eauto. 
  pfold. con. con. left. done. cbn. apply/gUnravel2_Rol. pfold. con. con. eauto. 
- punfold H1. inv H1. apply/Project_unfg. inv H3. 
  punfold H0. inv H0;try comp_disc;pclearbot. injt. punfold H2. inv H2.
  apply/Project_eunf. inv H5. injt. pfold. con. con=>//=. lia. 
  apply/ForallP. move/ForallP : H12. clear H6 H2 H0 H5 H1 H3 H4. 
  elim : es ecs es0 es1 H7 H10 H14 H8 H16. 
  case=>//=. case=>//=. case=>//=. move => a0 l IH. case=>//=.
  move => a1 l0 [] //=.  move => a2 l1 [] //=. 
  move => a3 l2 [] Heq [] Heq0 [] Heq1. intros. inv H8. inv H16. inv H12. pclearbot. 
  simpl in *. con;eauto. ssa. rewrite H2 H0 //=. pc. eauto. 
  punfold H2. inv H2. apply/Project_eunf. inv H9. pfold. con. apply/project_gen_end. 
  rewrite ICpart_of_iff;eauto. rewrite -gUnravel2_iff. pfold.  con. con. lia. done. 
  rewrite -gInvPred_unf_iff. apply/gUnravel2_Rol. pfold. con. con. 2 : eauto. eauto.
- punfold H3. inv H3.  apply/Project_unfg. inv H5. injt. 
  punfold H2. inv H2;pclearbot;try comp_disc. injt. 
   have :  forall g,
       In g gs ->
       forall (ec : lcType) (g0 : gType) (e : lType),
       CProject g.2 p ec ->
       g0 << (UnfgUnravel \o gUnravel2_gen) >> g.2 -> lUnravel2 e ec -> g0 <<( r) (UnfProj \o project_gen p) >> e.
  intros. apply/H1;eauto. clear H1 => H1. 
  move : (@In_zip2 _ _ g0 es gs H12 H9)=>[]. ssa. 
  pfold. con. econstructor=>//=. eauto.
  ssa. move : (@In_zip _ _ g' es gs H13 H9)=>[].  ssa. 
  apply/ICpart_of_all2_iff;eauto.  forallApp H10 H16. case=>[]//=. ssa. pc. done. 
  left. apply/Project_eunf2. (*apply In_zip_and in H8. ssa. *)
  move : (@In_zip _ _ g' es gs H13 H9)=>[].  ssa. 
  apply/H1. apply/H15.  all : eauto. 
  move/H14 : H15. ssa. pclearbot. done. 
  forallApp H10 H16. case=>[] //=. punfold H4. inv H4. ssa. pc. done. 
  apply/Project_eunf. punfold H4. inv H4. inv H11. pfold. con. apply/project_gen_end. 
  cbn. rewrite ICpart_of_iff;eauto. pfold. con. con=>//=. 
  cbn. apply/gUnravel2_Rol. pfold. con. con. 2 : eauto. lia. 
- subst. pfold. con. punfold H2. inv H2. inv H. con. 
  rewrite ICpart_of_iff. apply/CProject_not_part. eauto. 
  rewrite -gUnravel2_iff //=. 
  apply/gUnravel2_Rol. rewrite -gUnravel2_iff. eauto. 
Qed.


Let rwd := (etocoind'_eq, etocoind_eq, gtocoind'_eq, gtocoind_eq). 
Ltac seq := rewrite ?eqs -?rwd.
Ltac seq_in H := rewrite ?eqs -?rwd in H.



Lemma Project_gtree : forall p g e, Project g p e -> gUnravel2 g (gtocoind g). 
Proof. 
move => p. pcofix CIH. intros. punfold H0. inv H0. rewrite gtocoind_full_unf. apply/gUnravel2_iff.  inv H;seq.  
pfold. con. con. pclearbot.  eauto. 
pfold. con. 
con. pclearbot.  eauto. 
pfold. con. con. rewrite size_map=>//=.
move/ForallP : H5. clear H2 H1. elim : gs es H4. case=>//=. 
move => a0 l IH. case=>//=. move => a1 l0 [] Heq. intros. inv H5. pclearbot. simpl in *. 
con;eauto. ssa. pc.  eauto.
pfold. con. con. rewrite size_map //=. 
move/ForallP : H4. clear H2 H1 H3. elim : gs. 
simpl. done. move => a0 l IH HH. inv HH. ssa.  pclearbot. con;eauto. ssa. eauto.
rewrite -gtocoind_full_unf.  rewrite -gUnravel2_iff.
apply/paco2_mon.
apply/gInvPred_iff. rewrite gInvPred_unf_iff. done. done. 
Qed. 



Lemma Project_etree : forall p g e, Project g p e -> lUnravel2 e (etocoind e). 
Proof. 
move => p. pcofix CIH. intros. apply part_of2_or_end in H0 as H0'. 
destruct H0'. 
elim/part_of_all2_ind2 : H e H0;intros. 
punfold H1. inv H1. rewrite H0 in H2. rewrite etocoind_full_eunf.  apply/lUnravel2_iff. inv H2;pclearbot;try comp_disc. 
pfold. seq.  con. con. eauto. pfold. con. seq. con. 
apply/H1. punfold H3. inv H3. rewrite H2 in H4. inv H4;pclearbot ;try comp_disc. 
apply/Project_eunf. done. pfold. con. rewrite -H5. con. rewrite -part_of2_iff. eauto. 
rewrite -gInvPred_unf_iff.  eauto. 
punfold H1. inv H1. rewrite H0 in H2. rewrite etocoind_full_eunf.  apply/lUnravel2_iff. inv H2;pclearbot;try comp_disc. 
pfold. seq.  con. con. rewrite size_map //=. 
move/ForallP : H8. clear H5 H0 H2. elim : gs es H7. case=>//=. 
move => a0 l IH. case=>//=. move => a1 l0 [] Heq. intros. inv H8. pclearbot. simpl in *. 
con;eauto. 
seq. ssa. pc.  eauto. pfold. con. seq. con. 
punfold H3. inv H3. rewrite H2 in H4. rewrite etocoind_full_eunf. apply/lUnravel2_iff. inv H4;pclearbot;try comp_disc. 
rewrite -lUnravel2_iff. rewrite -etocoind_full_eunf. apply/H1. eauto. eauto. 
move/H10 : H8. ssa. pclearbot. apply/Project_eunf. done. 
seq. pfold. con. con. 
rewrite etocoind_full_eunf. apply/lUnravel2_iff. rewrite H. seq. pfold. con. con. 
Qed.

(*Lemma 15 in the paper*)
Lemma ICProject_iff : forall g p e, Project g p e <-> exists gc ec, gUnravel2 g gc /\ lUnravel2 e ec /\ CProject gc p ec. 
Proof. 
intros. split. intros. exists (gtocoind g). exists (etocoind e). ssa. 
apply/Project_gtree;eauto.  
apply/Project_etree;eauto.  
apply/ICProject;eauto. apply/Project_gtree;eauto. apply/Project_etree;eauto.  
case=> x []. intros. ssa. apply/CIProject;eauto. 
Qed.

