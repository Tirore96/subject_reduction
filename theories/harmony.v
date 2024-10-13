From mathcomp Require Import all_ssreflect zify.
From Equations Require Import Equations.
Require Import Paco.paco. 
Require Import MPSTSR.Projection.intermediateProj MPSTSR.Projection.projectDecide MPSTSR.Projection.indProj.
Require Import MPSTSR.IndTypes.elimination.
Require Import MPSTSR.CoTypes.coLocal MPSTSR.CoTypes.coGlobal MPSTSR.CoTypes.bisim.
Require Import MPSTSR.linearity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition elabel := (dir * ch * (value + nat))%type.

(*Prove rules equivalent to those from paper and argue error in permutation definition, missing rule*)
Inductive Estep : lType -> elabel -> lType -> Prop :=
| estep_msg d c v e0  : Estep (EMsg d c v e0) (d,c, inl v) e0
| estep_msg_async d vn c c' v e0 e0'  : Estep e0 (d,c,vn) e0' -> c <> c' -> 
                                        Estep (EMsg Sd c' v e0) (d,c,vn) 
                                              (EMsg Sd c' v e0')
| estep_branch n e es d c   : (n,e) \in es -> 
                              Estep (EBranch d c es) (d,c, inr n) e
| estep_branch_async es0 es1 vn d  c c'  : map fst es0 = map fst es1 ->  (*Ensure labels and branch size stays fixed*)
     (forall e0 e1, In (e0,e1) (zip es0 es1) -> Estep e0.2 (d,c,vn) e1.2)  -> c <> c'  ->  
                    Estep (EBranch Sd c' es0) (d,c,vn) (EBranch Sd c' es1)

| estep_rec e l e' : Estep (e [e ERec e .: EVar]) l e' -> Estep (ERec e) l e'.
Hint Constructors Estep.

Lemma Estep_unf : forall e0 l e1, Estep (eunf e0) l e1 -> Estep e0 l e1.
Proof. 
intros. destruct e0;try done. simpl in H. constructor. done. 
Qed.

Lemma Estep_full_unf : forall e0 l e1, Estep (full_eunf e0) l e1 -> Estep e0 l e1.
Proof. 
intros. rewrite /full_eunf in H.  remember (emu_height e0). clear Heqn. elim : n e0 H;try done. 
intros. apply/Estep_unf. apply/H. rewrite iterSr in H0. done. 
Qed.

Lemma Estep_unf2 : forall e0 l e1, Estep e0 l e1 -> Estep (eunf e0) l e1.
Proof. 
intros. destruct e0;try done. inversion H. simpl. done. 
Qed.

Lemma Estep_full_unf2 : forall e0 l e1, Estep e0 l e1 -> Estep (full_eunf e0) l e1.
Proof. 
intros. rewrite /full_eunf.  remember (emu_height e0). clear Heqn. elim : n e0 H;try done. 
intros. rewrite iterS.  apply/Estep_unf2. eauto. 
Qed.

(*reflect P(e,l) := exists e', Estep e l e' to support proofs by structural recursion on e *)
Fixpoint can_step l e := 
match e with 
| EMsg d c u e0 => (((d,c,inl u) == l) || ((d == Sd) && (c != l.1.2) && (can_step l e0)))
| EBranch d c es =>  (if l is (d',c',inr n) then ((d,c) == (d',c')) && (n \in map fst es) else false) || ((d == Sd) && (c != l.1.2) && (all ((can_step l \o snd)) es))
| ERec e0 => can_step l e0
| _ => false
end. 

Lemma minn_same : forall n, minn n n = n. Proof. lia. 
Qed.

Lemma Estep_subst2 : forall e l e' sigma, Estep e l e' -> Estep e [e sigma] l e'[e sigma]. 
Proof. intros. elim : H sigma;intros. con. 
simpl. 
con. apply H0. done. 
simpl. asimpl. econ.  
have :  (n, e0 [esigma]) = (prod_map ssrfun.id (subst_lType sigma)) (n,e0). done. 
move=>->.

apply/map_f. done. ssa.   
econ. 
elim : es0 es1 H   H0 H1. 
case=>//=. move => a l0 IH. case=>//=. intros. inv H.  f_equal. rewrite /prod_map. destruct a,a0. ssa. 
apply/IH.  done. eauto. eauto. clear H0.
move : es0 es1 H H1. 
elim. case. ssa. ssa. move => a l0 IH. case;ssa. inv H. destruct H0. 
inv H0. rewrite /prod_map. destruct a,a0. ssa. subst. 
have : (n0, l2, (n0, l3)) = (n0, l2, (n0, l3)) \/ In (n0, l2, (n0, l3)) (zip l0 l1). auto. 
move/H1.  eauto. eauto. done. 
simpl.   con.  asimpl. move: (H0 sigma). asimpl. done. 
Qed. 

Lemma can_step_sound : forall e l, can_step l e -> exists e', Estep e l e'. 
Proof. 
elim;intros;ssa.  apply H in H0. destruct H0. econstructor. con. apply/Estep_subst2. eauto. 
move : H0. move/orP. case. move/eqP. intros. subst. exists e. con. 
ssa. move/eqP : H2=> H2. subst. apply H in H1. destruct H1. exists (EMsg Sd c v x). destruct l. destruct p. con. done. 
ssa. rewrite neg_sym in H3. apply/eqP. done. 
destruct l0. destruct p. destruct s. ssa. move/eqP : H0. intros. subst. 
elim : l H2 H. ssa. exists (EBranch Sd c nil). con. done. done. rewrite neg_sym in H3. apply/eqP=>//=. 
intros. edestruct H0. rewrite inE. apply/orP. left. apply/eqP. eauto. ssa.  eauto. edestruct H. 
ssa. intros. apply/H0. rewrite inE. erewrite H2. lia. done. instantiate (1:= a.2). instantiate (1:= a.1). destruct a. done. 
ssa. instantiate (1 := (d0,c0, inl v)). done.
have :  exists e' : lType, Estep (EBranch Sd c l) (d0, c0, inl v) e'. apply/H. ssa. 
intros. apply/H0.  rewrite inE. apply/orP.  right. eauto. done. case. 
intros. inv p. 
exists (EBranch Sd c ((a.1,x)::es1)). con. ssa. ssa.  f_equal. done. 
ssa. 
destruct H4. 
 inv H2. ssa. eauto. 
ssa. destruct (orP H0). ssa.   move/eqP : H2. case. intros. subst. 
move/nthP : H3.  move/(_ 0). case. ssa. 
exists (nth EEnd (map snd l) x). con. 
apply/nthP. exists x. rewrite size_map in p. done. 
instantiate (1 := (0,EEnd)). subst. rewrite -nth_zip. f_equal. rewrite zip_fs //=. 
rewrite !size_map //=. 

ssa. move/eqP : H1. intros. subst. clear H0. 
elim : l H3 H. ssa. exists (EBranch Sd c nil). con. done. done. rewrite neg_sym in H4. apply/eqP=>//=. 
intros. destruct a.  edestruct H0. rewrite inE. apply/orP. left. apply/eqP. eauto. ssa.  eauto. edestruct H. 
ssa. intros. apply/H0. rewrite inE. apply/orP. right. eauto. done. 
inv H2;try done. rewrite eqxx in H4. done.  exists (EBranch Sd c ((n0,x)::es1)). con. ssa. f_equal. done. 
ssa. destruct H5. inv H3. simpl. eauto. done. 
Qed.

Lemma can_step_ren : forall e l sigma, can_step l e ⟨e sigma ⟩ = can_step l e.   
Proof. 
elim;intros;ssa. f_equal. f_equal. done. destruct l0.  destruct p. destruct s;ssa. f_equal. 
rewrite all_map. apply/eq_in_all. move=> x xIn. simpl. destruct x. ssa. apply/H. eauto. 
f_equal. f_equal. rewrite -map_comp. clear H. elim : l n. done. ssa.
ssa. f_equal. rewrite /prod_map. destruct a. ssa.  done. 
f_equal. rewrite all_map. apply/eq_in_all. move => x xIn. ssa. destruct x. ssa. eauto. 
Qed.

Lemma can_step_subst : forall e sigma l, (forall n, can_step l (sigma n) -> can_step l e) ->  can_step l (e [e sigma ]) ->  can_step l e.  
Proof. 
elim;intros. ssa'. eauto. ssa'. 
ssa'. apply/H. 2 : eauto. case. ssa'. ssa'. move : H2. asimpl. rewrite can_step_ren. eauto. 
ssa'.  destruct ( ((d, c, inl v) == l)) eqn:Heqn. 
rewrite Heqn //=. rewrite Heqn /=. rewrite Heqn /=  in H1. ssa'. apply/H. 
2 : eauto. intros. apply H0 in H2. rewrite Heqn //= in H2. ssa'. 
ssa'. destruct l0. destruct p. ssa'. destruct s. ssa'. apply/allP=> x xIn. destruct x.  apply/H. ssa'. eauto. 
instantiate (1 := sigma). intros. 2 : { ssa'. rewrite all_map in H3.  move : (allP H3). move/(_ _ xIn). simpl. done. }
move/H0 : H2. ssa'. move : (allP H6). move/(_ _ xIn). ssa'. 
destruct (((d, c) == (d0, c0)) && (n \in map fst (map (prod_map ssrfun.id (subst_lType sigma)) l))) eqn:Heqn. 
rewrite Heqn in H1. ssa'. rewrite H2 //=. move/mapP : H3. case. ssa'. subst. destruct (mapP p). 
subst. rewrite /prod_map. destruct x0. ssa'. apply/orP. left. clear p H0 H. 
elim : l s s0 H3. ssa'. ssa'. rewrite inE in H3. destruct (orP H3). rewrite -(eqP H0). ssa'. lia.  
rewrite inE. apply/orP. right. eauto. 
rewrite Heqn in H1. ssa'. rewrite (eqP H1). apply/orP. right. ssa'. 
apply/allP. intro. intros. cbn. rewrite all_map in H3. move : (allP H3 _ H2).  
simpl. rewrite /prod_map. destruct x. ssa'. apply/H. eauto. 2 : eauto. 
intros. apply H0 in H5. 
destruct (orP H5). 
ssa'. rewrite H7 in Heqn. ssa'. rewrite -map_comp in Heqn.
have :  (fst \o prod_map ssrfun.id (subst_lType sigma)) = fst. intros. fext. intros. 
cbn. rewrite /prod_map. destruct x. done. intros. rewrite x H8 in Heqn. done. 
ssa'. move/allP : H8. move/(_ _ H2). ssa'. 
Qed. 

Lemma can_step_complete : forall e l e', Estep e l e' ->  can_step l e. 
Proof. 
intros. elim : H;intros. ssa'. rewrite eqxx //=. 
rewrite /=. rewrite neg_sym. move/eqP : H1=>-> /=. rewrite H0. lia. ssa'.
apply/orP.  left. ssa'. elim : es n e0 H. ssa'. ssa'. rewrite inE in H0. destruct (orP H0). 
rewrite -(eqP H1). ssa'. lia. apply/orP. right. apply/H. eauto. 
ssa'. apply/orP. right. rewrite neg_sym. move/eqP :H2 =>-> /=. apply/allP. move => x xIn. 
move/nthP : xIn.  move/(_ (0,EEnd)). case. intros. subst. 
apply/H1. apply/inP/nthP. exists x0. rewrite size_zip. have : size es0 = size es1 by eauto. move=><-. 
rewrite minn_same //=. instantiate (2 := ((0,EEnd),(0,EEnd))). rewrite nth_zip.  f_equal. 
have : size es0 = size es1 by eauto. auto.
ssa'. apply can_step_subst in H0. done. case. simpl. done. 
ssa'. 
Qed.

Lemma can_step_rec : forall e l, can_step l (ERec e) -> can_step l e. 
Proof. done. Qed.

(*Allows structural recursion of g in projectT p g*)
Lemma Estep_rec : forall e l e', Estep (ERec e) l e' -> exists e'', Estep e l e''. 
Proof. intros. apply/can_step_sound. apply/can_step_rec. apply/can_step_complete. eauto. 
Qed.

Fixpoint can_gstep (l : label) (g: gType)  :=
match g with 
| GMsg a u g' => ((a,inl u) == l) || ((ptcp_to a \notin l.1) && (can_gstep l g'))
| GBranch a gs => (let (a',vn) := l in if vn is inr n then (a == a') && (n \in map fst gs) else false) ||  ((ptcp_to a \notin l.1) && (all ((can_gstep l) \o snd) gs))
| GRec e0 => can_gstep l e0
| _ => false
end. 

Lemma step_subst2 : forall e l e' sigma, step e l e' -> step e [g sigma] l e'[g sigma]. 
Proof. intros. elim : H sigma;intros. con. 
simpl. con. 
have :  (n, g [gsigma]) =  (prod_map ssrfun.id (subst_gType sigma)) (n,g). done. move=>->. 
apply/map_f. done. 
asimpl. simpl. con. done. done. simpl. con. rewrite -!map_comp. 
have : size gs = size gs' by eauto. intros. 
elim : gs gs' H0 H1 H x. case. ssa'. ssa'. 
move => a0 l1 IH. case. ssa'. ssa'. f_equal. rewrite /prod_map. destruct a0,a1. ssa'. inv H. 
apply/IH. ssa'. ssa'. inv H. inv x. 
intros.
have : size gs = size gs' by eauto. intros. 
elim : gs gs' g g' x H H0 H1 H3. case. ssa'. ssa'. 
move => a0 l1 IH. case. ssa'. ssa'. inv x. inv H. destruct H3. rewrite /prod_map in H3.
destruct a0,a1. ssa'. subst. inv H3. subst. asimpl. 
have :  (n0, g0, (n0, g1)) =  (n0, g0, (n0, g1)) \/ In  (n0, g0, (n0, g1)) (zip l1 l2). 
auto. 
move/H1.  simpl. auto. apply/IH; eauto. done. 

simpl. con.  asimpl. move: (H0 sigma). asimpl. done. 
Qed. 


Lemma can_gstep_sound : forall g l, can_gstep l g -> exists g', step g l g'.
Proof. 
elim;intros;ssa'.  apply H in H0. destruct H0. econstructor. con. apply/step_subst2. eauto. 
move : H0. move/orP. case. move/eqP. intros. subst. eauto. move/andP.   case. intros. 
ssa'. move/H : b. case. intros. exists (GMsg a v x). con. done. done. 
destruct l0. destruct s. ssa'. 
elim : l H H1 H2. ssa'. rewrite negb_or in H1. ssa'. exists (GBranch a nil). con. done. ssa'. ssa'. rewrite negb_or. ssa'. 
intros. ssa'. destruct a1.  edestruct H0. rewrite inE. apply/orP. left. eauto. eauto. 
edestruct H. intros. apply / H0. eauto. done. done. done. inv H5. ssa'.
exists (GBranch a ((n,x)::gs')). con.  ssa'. f_equal. done. ssa'. 
destruct H6. inv H6. ssa'. done. 
destruct (orP H0).
ssa'. move/nthP : H3. move/(_ 0). case. ssa'. 
 exists (nth GEnd (map snd l) x). ssa'. rewrite (eqP H2). con. 
apply/nthP. exists x. rewrite size_map in p. done. 

instantiate (1 := (0,GEnd)). subst. 
have : nth (0, GEnd) l x = nth (0, GEnd) (zip (map fst l) (map snd l)) x.  rewrite zip_fs.  done. 
move=>->. 
rewrite nth_zip. done.  f_equal. rewrite !size_map. done. 
ssa'. 
clear H0.
elim : l H H2 H3. ssa'. rewrite negb_or in H2. ssa'. 
exists (GBranch a nil). con. done. ssa'. ssa'. rewrite negb_or. ssa'. ssa'. 
have :  exists g' : gType, step a1.2 (a0,inr n) g'. apply/H0. apply/inP. simpl. instantiate (1 := a1.1).
destruct a1. ssa'. done. case. ssa'. 
have : exists g' : gType, step (GBranch a l) (a0, inr n) g'. apply/H. ssa'. apply/H0. 
rewrite inE. apply/orP. eauto.  done. done. done. case. intros. rewrite negb_or in H2.  inv p0. rewrite eqxx in H2. ssa'. 
exists (GBranch a ((a1.1,x)::gs')). con. ssa'. f_equal. done. 
ssa'. destruct H3. inv H2. ssa'.  done. 
Qed.

Definition to_elabel (a : action) (vn : value + nat) (p : ptcp) := if comp_dir p a is Some d then Some (d,action_ch a,vn) else None.


Fixpoint can_gstep2 (l : elabel) p (g: gType)  :=
match g with 
| GMsg a u g' => (to_elabel a (inl u) p == Some l) || ((ptcp_to a != p) && (implb (ptcp_from a == p) (action_ch a != l.1.2))) && (can_gstep2 l p g')
| GBranch a gs => ((to_elabel a l.2 p == Some l) && (if l.2 is inr n then n \in (map fst gs) else false)) || ((ptcp_to a != p) && (implb (ptcp_from a == p) (action_ch a != l.1.2))) && (all ((can_gstep2 l p) \o snd) gs)
| GRec e0 => can_gstep2 l p e0
| _ => false
end. 

Lemma can_gstep2_guarded : forall g l p i, can_gstep2 l p g -> size_pred g -> eguarded i(trans p g). 
Proof.
elim;intros. ssa'. ssa'. ssa'. erewrite H.  ssa'. eauto. eauto. done. 
ssa'. destruct (orP H0). move/eqP : H2. rewrite /to_elabel. destruct (comp_dir p a) eqn:Heqn. ssa'. done. 
ssa'. eapply H in H4. destruct (comp_dir p a). done. eauto. ssa'.
ssa'. destruct (orP H0). move/eqP : H1. rewrite /to_elabel. destruct (comp_dir p a) eqn:Heqn. done. done. 
ssa'. destruct l;try done. ssa'. eapply H in H4;eauto. destruct (comp_dir p a). done. eauto. 
instantiate (1 := p0.1). destruct p0. ssa'. apply/orP. left. done. 
Qed. 


Lemma  compSd : forall p a, comp_dir p a = Some Sd -> p = ptcp_from a. 
Proof. intros. rewrite /comp_dir in H. 
move : H. case_if. rewrite (eqP H) //=. case_if;done. 
Qed.

Lemma  compRd : forall p a, comp_dir p a = Some Rd -> p = ptcp_to a. 
Proof. intros. rewrite /comp_dir in H. 
move : H. case_if. done. case_if;try done. rewrite (eqP H0) //=. 
Qed.

Lemma pack_act a : Action (ptcp_from a) (ptcp_to a) (action_ch a) = a. 
Proof. destruct a;done. 
Qed. 

Ltac subst_comp := repeat (match goal with 
                   | [ H : comp_dir _ _ = Some Sd  |- _ ] =>  apply compSd in H;subst 
                   | [ H : comp_dir _ _ = Some Rd  |- _ ] =>  apply compRd in H;subst 
                  end).



Lemma can_gstep2P : forall g l p, can_gstep2 l p g ->  size_pred g -> can_step l (trans p g). 
Proof. 
elim;intros. ssa'. ssa'. ssa'. erewrite can_gstep2_guarded;eauto.
ssa'. destruct (orP H0). move/eqP : H2. rewrite /to_elabel. destruct (comp_dir p a) eqn:Heqn.
case. intros. subst. ssa'. rewrite eqxx //=. done. 
ssa'. apply H in H4. destruct (comp_dir p a) eqn:Heqn. ssa'. apply/orP. right. ssa'. 
destruct d;subst_comp;try done. rewrite eqxx in H2. done. destruct d;subst_comp.
apply (implyP H5).  done. rewrite eqxx in H2. done. done. done. 
ssa'. destruct (orP H0). ssa'. move/eqP : H4. rewrite /to_elabel. destruct (comp_dir p a) eqn:Heqn.
case. intros. subst. rewrite -H1.  ssa'. 
destruct l0,p0.  ssa'. inv H1. apply/orP. left.   destruct s;try done;ssa'. 
rewrite -map_comp. have : fst  =  (fst \o prod_map id (trans p)). intros. fext. case. ssa'. 
move=><-. done. 
 
ssa'. destruct (comp_dir p a) eqn:Heqn;try done.  
ssa'. destruct l0. destruct p0. ssa'. destruct s. ssa'. destruct d;subst_comp;try done. rewrite eqxx //= in H1. 
apply (implyP H6). destruct d;subst_comp. done. rewrite eqxx in H1. done.  rewrite all_map.
apply/allP. move => x xIn. simpl. destruct x. ssa'. apply/H. eauto. 
move : (allP H5). move/(_ _ xIn). done. move : (allP H3). move/(_ _ xIn). ssa'. 
destruct (orP H0). ssa'. move/eqP : H7. rewrite /to_elabel. rewrite Heqn. case. intros. subst. 
rewrite -map_comp. 
rewrite eqxx  //= //=. 
have : (fst \o prod_map id (trans p)) = fst. intro. fext. case. ssa'. move=>->. rewrite H8 //=.
apply/orP.  right. ssa'. destruct d;subst_comp. done. rewrite eqxx //=in H4. apply (implyP H9). 
destruct d;subst_comp. done. rewrite eqxx in H1. done. 
rewrite all_map.
apply/allP. move => x xIn. simpl. destruct x. ssa'. apply/H. eauto. 
move : (allP H5). move/(_ _ xIn). ssa'. move : (allP H3). move/(_ _ xIn). ssa'. 
destruct l;try done. ssa'. destruct p0. apply/H. eauto. done. done. 
Qed. 


Lemma Project_unfg2 : forall g p e r, paco2  (UnfProj \o project_gen p) r g e -> paco2  (UnfProj \o project_gen p) r  (full_unf g) e. 
Proof. 
intros. punfold H. inv H. pfold. con. rewrite full_unf_idemp. done. 
Qed.

Ltac pc := pclearbot.
Lemma comp_dir_part_msg : forall a u g0 p, comp_dir p a ->  part_of2 p (GMsg a u g0).
Proof. 
intros. con.  con. con. done. 
Qed. 
Lemma comp_dir_part_msg2 : forall a u g0 p, isSome(comp_dir p a) = true ->  part_of2 p (GMsg a u g0).
Proof. 
intros. con.  con. con. done. 
Qed. 

Hint Resolve comp_dir_part_msg comp_dir_part_msg2.
Ltac end_inv := repeat (match goal with 
                   | [ H : ~ (part_of2 _ (full_unf _)) |- _ ] => exfalso; rewrite -part_of2_iff in H; auto
                   | [ H : ?o = None, H' : isSome (?o) = true |- _ ] => rewrite H //= in H'
                   | [ H : ?o = Some _, H' : isSome (?o) = false |- _ ] => rewrite H //= in H'
                  end).

Ltac invc H := inv H;clear H;subst_comp;pc;try solve [comp_disc | end_inv].

Lemma fst_c : forall (A B C : Type) (f : B -> C), (@fst A C \o prod_map ssrfun.id f) = fst.
Proof. 
intros. fext. case. ssa'. 
Qed. 

Lemma can_gstep2_ren : forall g l p sigma, can_gstep2 l p (g ⟨g sigma⟩) -> can_gstep2 l p g. 
Proof. 
elim;intros. ssa'. ssa'. ssa'. eauto. ssa'. 
destruct (orP H0). apply/orP. left. done. apply/orP. right. ssa'. eauto. 
ssa'. destruct (orP H0). apply/orP. left. rewrite -map_comp in H1.  ssa'.  rewrite fst_c in H3. done.  
ssa'. 
apply/orP. right. ssa'. 
apply/allP. move => x xIn. destruct x.  apply/H. eauto. rewrite all_map in H3.  move : (allP H3). 
move/(_ _ xIn). simpl. eauto. 
Qed. 

Lemma can_gstep2_subst : forall g l p sigma, can_gstep2 l p (g [g sigma]) -> (forall n, can_gstep2 l p (sigma n) -> can_gstep2 l p g) -> can_gstep2 l p g. 
Proof. elim;intros;ssa'. eauto. 
apply/H. eauto. intros. move : H2.  asimpl. destruct n;try done.
simpl. move/can_gstep2_ren. eauto. 
destruct (orP H0). 
- apply/orP. left. done. 
- apply/orP. right. ssa'. apply/H. eauto.
  intros. apply H1 in H3.  destruct (orP H3). 
  move/eqP : H6. rewrite /to_elabel. destruct (comp_dir p a)eqn:Heqn;try done. 
  case. intros. subst. ssa'. destruct (ptcp_from a == p)eqn:Heqn2. rewrite eqxx in H5. done. 
  destruct d;subst_comp;try done. rewrite eqxx //= in Heqn2. rewrite eqxx //= in H2. ssa'. 

destruct (orP H0). 
- apply/orP. left. destruct l0,s. ssa'. ssa'. rewrite -map_comp fst_c in H4. done. 
  ssa'. apply/orP. right. ssa'. apply/allP=> x xIn. destruct x.  apply/H. eauto. rewrite all_map in H4.  
  move : (allP H4). move /(_ _ xIn). ssa'. eauto.
  intros. apply H1 in H3. destruct (orP H3). ssa'. move/eqP : H7.  rewrite /to_elabel.
  destruct (comp_dir p a)eqn:Hqen;try done. case. intros. rewrite -H6 in H8. ssa'. rewrite -H6. destruct l0;try done. ssa'. 
  destruct s;try done. ssa'. inv H6. 
  destruct (ptcp_from a == p)eqn:Heqn2. rewrite eqxx in H5. done. 
  destruct d;subst_comp;try done. rewrite eqxx //= in Heqn2. rewrite eqxx //= in H2. ssa'. ssa'.
  rewrite all_map in H4. destruct s1. ssa'. 
  have : s0 =  (s.+1, s0).2. done. move => ->. 
  move : (allP H4). move/(_ _ xIn). move => HH.  ssa'. inv H6. apply/H. inv H6. eauto. eauto. 
  intros. apply H1 in H7. destruct (orP H7). clear H7. ssa'. 
  move/eqP : H7. have : action_ch a != action_ch a. apply (implyP H5). destruct d. 
  subst_comp. done. subst_comp. rewrite eqxx //= in H2. move/eqP. done. 
  ssa'. move : (allP H11). move/(_ _ xIn). ssa'. ssa'. 
  move : (allP H8).  move/(_ _ xIn). ssa'. 
Qed. 

Lemma can_gstep2_unf : forall g l p, can_gstep2 l p (unf g) -> can_gstep2 l p g. 
Proof. case;try done. ssa'. apply/can_gstep2_subst. eauto. ssa'. 
destruct n. ssa'. done. 
Qed. 

Lemma can_gstep2_full_unf : forall g l p, can_gstep2 l p (full_unf g) -> can_gstep2 l p g. 
Proof. intros. rewrite /full_unf in H. remember (mu_height g). clear Heqn. 
elim : n g H. done. ssa'. apply/H. apply/can_gstep2_unf. done. 
Qed.


Lemma action_pred_ren : forall g sigma, action_pred g = action_pred g ⟨g sigma ⟩.
Proof. elim;rewrite //=;intros. ssa'. f_equal. done. f_equal. 
elim : l H. done. ssa'. erewrite H0. f_equal.  destruct a0. ssa'. apply/H. intros. apply/H0. eauto.
instantiate (1 := a0.1). destruct a0. ssa'. rewrite eqxx //=. 
Qed. 

Lemma action_pred_subst : forall g sigma, (forall n, action_pred (sigma n)) ->  action_pred g = action_pred g[g sigma].
Proof. elim;rewrite //=;intros. 
rewrite H //=. apply/H. case. done. simpl. intros. asimpl. rewrite -action_pred_ren. done. f_equal. 
auto. f_equal.  
elim : l H H0. done. ssa'. destruct a0.  ssa'. erewrite H0. f_equal.  ssa'. ssa'. eauto. apply/orP. eauto. intros. eauto. 
Qed.

Lemma action_pred_unf : forall g, action_pred g ->  action_pred (unf g). 
Proof. case=>//=. intros. rewrite -action_pred_subst. done. case. done. done. 
Qed.

Lemma action_pred_full_unf : forall g, action_pred g ->  action_pred (full_unf g). 
Proof. 
intros. rewrite /full_unf. remember (mu_height g). clear Heqn. elim : n g H. done. 
intros. simpl. apply/action_pred_unf . eauto. 
Qed.

Lemma EstepEQ2 : forall e0 e0' e1 l, Estep e0 l e1 -> EQ2 e0 e0' -> exists e1', Estep e0' l e1'. 
Proof. intros. 
elim : H e0' H0;intros. 
punfold H0. inv H0. inv H. pclearbot. exists e4. apply/Estep_full_unf. rewrite -H6. con. 
punfold H2. inv H2. inv H3. pclearbot. apply H0 in H5. destruct H5. 
exists (EMsg Sd c' v x). apply/Estep_full_unf. rewrite -H9. econstructor 2. done. done. 
punfold H0. inv H0. inv H1.  
move/nthP : H. move/(_ (0,EEnd)). case. ssa'. 
exists (nth EEnd (map snd es1) x). 
clear H0 H1. apply/Estep_full_unf. rewrite -H6. clear H6. con. 
elim : es x es1 H4 H7 p q. case. ssa'. ssa'.
move => a l0 IH x [] //=. ssa'. 
destruct x. ssa'. subst. ssa'. inv H7. ssa'. pc. subst. apply/orP. left. destruct a0. ssa'. 
rewrite inE. apply/orP. right. simpl. inv H4. apply/IH. done. inv H7. done. done. 

punfold H3. inv H3. inv H4. clear H3 H4. 
suff :  exists e1' : lType, Estep (full_eunf e0') (d, c, vn) e1'.
case. intros. exists x. apply/Estep_full_unf. done. 

have : size es0 = size es1 by eauto. 
intros. rewrite -H9.  clear H9. 
elim : es3 es0 es1 H7 x H H0 H1 H10. case. case. ssa'. 
exists (EBranch Sd c' nil). con. done. done. done. done. done. 
move => a l0 IH. case. done. move => a0 l1 [] //=. move => a1 l2. 
case=>HH0. case=>HH1. case. ssa'. inv H10. ssa'. pc. 
have :  exists e1' : lType, Estep a.2 (d, c, vn) e1'.
apply/H3. eauto. eauto. case. 
ssa'. 
have : exists e1' : lType, Estep (EBranch Sd c' l0) (d, c, vn) e1'. apply/IH. 4 : { eauto. } done. done. done.
intros.  eauto. done. case. intros. inv p0. destruct a. ssa'. 
exists (EBranch Sd c' ((n,x)::es1)). con. ssa'. f_equal. done.
ssa'. 
destruct H6.  inv H6. ssa'. eauto. 

apply/H0. move : H1. move/EQ2_eunfl2. rewrite full_eunf_subst. move/EQ2_eunfl. done. 
Qed.

Lemma EQ2_sym : forall e0 e1, EQ2 e0 e1 -> EQ2 e1 e0.
Proof. 
pcofix CIH. intros. punfold H0. invc H0. pfold. con. invc H;try con;pc;eauto.
clear H0 H1. elim : es1 es0 H2 H3. case=>//=.
move => a l IH [] //=. ssa'. inv H2.  inv H3. ssa'. pc. con;eauto. 
Qed. 




Lemma project_can_step : forall g p e e' l, Estep e l e' -> Project g p e -> action_pred g -> can_gstep2 l p g.
Proof. 
move => g p e e' l Hstep Hproj. 
move : Hstep g p Hproj.
elim;intros.
apply part_of2_or_end in Hproj as Hproj'. destruct Hproj';try done.
move : H0 d c v e0 Hproj H l e e'.
elim/part_of_all2_ind2;intros.
apply can_gstep2_full_unf. rewrite H0. ssa'. rewrite /to_elabel.
destruct (comp_dir p a)eqn:Heqn;try done. 
apply Project_unfg2 in Hproj. rewrite H0 in Hproj.
punfold Hproj. invc Hproj. invc H2. rewrite H5 in Heqn. inv Heqn. rewrite eqxx //=. rewrite eqxx //=. 
apply can_gstep2_full_unf. rewrite H2. ssa'. apply/orP. right. 
ssa'. move : H. rewrite /comp_dir. case_if;try done. case_if;try done. rewrite neg_sym H4 //=. 
apply/implyP. move/eqP. intros. 
subst. move : H.  rewrite /comp_dir eqxx. done.
apply Project_unfg2 in Hproj. rewrite H2 in Hproj.
punfold Hproj. invc Hproj. invc H4.
apply/H1. move : H10. cbn. eauto. all :try done. 
apply action_pred_full_unf in H3. rewrite H2 in H3. ssa'. 

apply can_gstep2_full_unf. rewrite H0. ssa'. rewrite /to_elabel.
apply Project_unfg2 in Hproj. rewrite H0 in Hproj.
punfold Hproj. invc Hproj. invc H2. 

apply can_gstep2_full_unf. rewrite H2. ssa'. rewrite /to_elabel.
apply Project_unfg2 in Hproj. rewrite H2 in Hproj.
punfold Hproj. invc Hproj. invc H2. invc H4.
rewrite H7 //=. ssa'.
move : H7. rewrite /comp_dir. case_if;try done. case_if;try done. rewrite neg_sym H4 //=.
apply/implyP. move/eqP. intros. 
subst. move : H.  rewrite /comp_dir eqxx. done.
apply/allP=> x xIn. apply/H1. apply/inP. done. apply/H0/inP. done.
move/inP : xIn. move/H10. ssa'. pclearbot. move : H4.  cbn. eauto.
apply action_pred_full_unf in H3. rewrite H6 in H3. ssa'. 
apply (allP H4). done. all : try done. 

apply part_of2_or_end in Hproj as Hproj'. destruct Hproj';try done.

clear l.

move : H3 e0 e0' H Hproj H0 H2.  
elim/part_of_all2_ind2;intros.

apply can_gstep2_full_unf. rewrite H0. ssa'. rewrite /to_elabel.
destruct (comp_dir p a)eqn:Heqn;try done. 
apply Project_unfg2 in Hproj. rewrite H0 in Hproj.
punfold Hproj. invc Hproj. invc H5. rewrite /comp_dir eqxx in Heqn. inv Heqn.  
apply/orP. right. ssa'. 
apply action_pred_full_unf in H4. rewrite H0 in H4. ssa'. rewrite neg_sym. done. 
apply/implyP.  rewrite neg_sym. move => _. apply/eqP. done. apply/H3. done. 
apply action_pred_full_unf in H4. rewrite H0 in H4. ssa'. 

apply Project_unfg2 in Hproj. rewrite H3 in Hproj.
punfold Hproj. invc Hproj. invc H7. rewrite /comp_dir eqxx in H. done. 

apply can_gstep2_full_unf. rewrite H3. ssa'. apply/orP. right. 
ssa'. move : H. rewrite /comp_dir. case_if;try done. case_if;try done. rewrite neg_sym H7 //=. 
apply/implyP. move/eqP. intros. 
subst. move : H.  rewrite /comp_dir eqxx. done.
apply/H2.  eauto. move : H13. cbn. eauto. all: try done.   
apply action_pred_full_unf in H6. rewrite H3 in H6. ssa'. 

apply Project_unfg2 in Hproj. rewrite H0 in Hproj.
punfold Hproj. invc Hproj. invc H5.

apply can_gstep2_full_unf. rewrite H3. ssa'. apply/orP. right. 
ssa'. move : H. rewrite /comp_dir. case_if;try done. case_if;try done. rewrite neg_sym H7 //=. 
apply/implyP. move/eqP. intros. 
subst. move : H.  rewrite /comp_dir eqxx. done.
apply/allP=> x xIn. apply/H2. apply/inP. done. apply/H0/inP. done.
eauto. apply Project_unfg2 in Hproj. rewrite H3 in Hproj.
punfold Hproj. invc Hproj. invc H7. move/inP : xIn. move/H13. ssa'. 
pclearbot. eauto. all : try done.  
apply action_pred_full_unf in H6. rewrite H3 in H6. ssa'. apply (allP H8). done. 


apply part_of2_or_end in Hproj as Hproj'. destruct Hproj';try done.

clear l e e'.

move : H1 n d c es Hproj H H0. 
elim/part_of_all2_ind2;intros.

apply can_gstep2_full_unf. rewrite H0. ssa'. rewrite /to_elabel.
destruct (comp_dir p a)eqn:Heqn;try done. 
apply Project_unfg2 in Hproj. rewrite H0 in Hproj.
punfold Hproj. invc Hproj. invc H3. 

apply Project_unfg2 in Hproj. rewrite H2 in Hproj.
punfold Hproj. invc Hproj. invc H5. 
apply can_gstep2_full_unf. rewrite H2. ssa'. apply/orP. right. 
ssa'. move : H. rewrite /comp_dir. case_if;try done. case_if;try done. rewrite neg_sym H5 //=. 
apply/implyP. move/eqP. intros. 
subst. move : H.  rewrite /comp_dir eqxx. done.

apply/H1. move : H11.   cbn. eauto. all : try done. 
apply action_pred_full_unf in H4. rewrite H2 in H4. ssa'. 

apply Project_unfg2 in Hproj. rewrite H0 in Hproj.
punfold Hproj. invc Hproj. invc H3.

apply can_gstep2_full_unf. rewrite H0. ssa'. apply/orP. left. 
rewrite /to_elabel H8.
ssa'. 
have :  exists a1, In a1 gs /\ In (a1,(n,e0)) (zip gs es).
apply/In_zip2. apply/inP=>//=. done. case. 
move => x. case. move => HH. move/H11. 
ssa'. pc. 
subst. apply/map_f/inP. done. 


apply can_gstep2_full_unf. rewrite H2. ssa'. 
apply Project_unfg2 in Hproj. rewrite H2 in Hproj.
punfold Hproj. invc Hproj. invc H5. apply H11 in H9. ssa'. pc. 
apply/orP. right. ssa'. 
move : H. rewrite /comp_dir. case_if;try done. case_if;try done. rewrite neg_sym H7 //=. 
apply/implyP. move/eqP. intros. 
subst. move : H.  rewrite /comp_dir eqxx. done.
apply/allP=> x xIn. apply/H1. apply/inP. done. move/inP : xIn. auto. 
move/inP : xIn. move/H11. ssa'. pc. move : H9. cbn. eauto. done. 
apply action_pred_full_unf in H4. rewrite H2 in H4. ssa'. apply (allP H9). done. 


apply part_of2_or_end in Hproj as Hproj'. destruct Hproj';try done.

clear l e e'. 

move : H4 d c c' vn es0 es1 Hproj H H0 H1 H2 H3. 
elim/part_of_all2_ind2;intros.
apply Project_unfg2 in Hproj. rewrite H0 in Hproj. 
punfold Hproj. invc Hproj. invc H6. 

apply Project_unfg2 in Hproj. rewrite H2 in Hproj. 
punfold Hproj. invc Hproj. invc H8. 
apply can_gstep2_full_unf. rewrite H2. ssa'. 
apply/orP. right. ssa'. 
move : H. rewrite /comp_dir. case_if;try done. case_if;try done. rewrite neg_sym H8 //=. 
apply/implyP. move/eqP. intros. 
subst. move : H.  rewrite /comp_dir eqxx. done.
apply/H1. move : H14. cbn.  eauto. eauto. all : try done.  
apply action_pred_full_unf in H7. rewrite H2 in H7. ssa'. 

apply Project_unfg2 in Hproj. rewrite H0 in Hproj. 
punfold Hproj. invc Hproj. invc H6. 
apply can_gstep2_full_unf. rewrite H0. ssa'. 
rewrite /to_elabel /comp_dir eqxx //=. apply/orP. right.  
apply action_pred_full_unf in H5. rewrite H0 in H5. ssa'. 
rewrite neg_sym //=. rewrite neg_sym //=. apply/eqP.  done. 
apply/allP=> x xIn.  clear H0.
elim : gs es0 es1 H13 H1 H14 H2 H3 H7 xIn. case=>//=. move => a0 l IH. 
case=>//=. move => a1 l0. case=>//=. move => a2 l1. intros.   invc H13. invc H1.  ssa'. 
rewrite inE in xIn. destruct (orP xIn). move/eqP: H7. intros. subst. apply/H3;eauto. 
edestruct H14. eauto. ssa'. pc. done. apply/IH;eauto. 

apply can_gstep2_full_unf. rewrite H2. ssa'. 
apply/orP. right. ssa'. 
move : H. rewrite /comp_dir. case_if;try done. case_if;try done. rewrite neg_sym H8 //=. 
apply/implyP. move/eqP. intros. 
subst. move : H.  rewrite /comp_dir eqxx. done.
apply/allP=> x xIn. 
apply Project_unfg2 in Hproj. rewrite H2 in Hproj. 
punfold Hproj. invc Hproj. invc H8. 
move : H. rewrite /comp_dir eqxx //=. 
apply/H1. apply/inP. done. move/inP : xIn. auto. 
move/inP : xIn. move/H14. ssa'. pc. move : H9. cbn. eauto. apply/H3.  
all : try done. 
apply action_pred_full_unf in H7. rewrite H2 in H7. ssa'. apply (allP H9). done. 

have : Project g p  (e0 [e ERec e0 .: EVar]).  
punfold Hproj. invc Hproj. rewrite full_eunf_subst in H2. 
pfold. con. done.  move/H0. move/(_ H1).  done. 
Qed. 

Fixpoint uniqg_labels (e : gType) := 
match e with 
| GMsg _ _ g0 => uniqg_labels g0 
| GBranch _ gs => (uniq (map fst gs)) && (all (uniqg_labels \o snd) gs)
| GRec g0 => uniqg_labels g0
| _ => true 
end. 

Lemma uniqg_labels_ren : forall g sigma, uniqg_labels g -> uniqg_labels g ⟨g sigma ⟩.
Proof. elim;rewrite //=;intros. ssa'. ssa'. 
rewrite -map_comp fst_c. done. 
rewrite all_map. apply/allP. intro. intros. simpl. 
destruct x. ssa'. apply/H. eauto. have : s0 = (s,s0).2 by done. 
move=>->.
apply (allP H2). done.  
Qed. 

Lemma uniqg_labels_subst : forall g sigma, (forall n, uniqg_labels (sigma n)) ->  uniqg_labels g -> uniqg_labels g [g sigma].
Proof. elim;rewrite //=;intros. ssa'. asimpl. apply/H. case. ssa'. ssa'. 
asimpl. apply/uniqg_labels_ren. done.  done. 
ssa'. rewrite -map_comp fst_c.  done. 
rewrite all_map. apply/allP. intro. intros. simpl. 
destruct x. ssa'. apply/H. eauto. done. have : s0 = (s,s0).2 by done. 
move=>->.
apply (allP H3). done.  
Qed. 

Fixpoint uniq_labels (e : lType) := 
match e with 
| EMsg _ _ _ e0 => uniq_labels e0 
| EBranch _ _ es => (uniq (map fst es)) && (all (uniq_labels \o snd) es)
| ERec e0 => uniq_labels e0
| _ => true 
end. 


Lemma uniq_trans : forall g p, uniqg_labels g -> uniq_labels (trans p g).
Proof. 
elim;ssa'. case_if. ssa'. done. destruct (comp_dir p a);ssa'. 
destruct (comp_dir p a);ssa'. rewrite -map_comp fst_c.  done. 
apply/allP. intro. move/mapP. case. ssa'. subst. destruct x0. ssa'. apply/H. eauto.
move: (allP H2 _ p0). ssa'. 
destruct l. ssa'. ssa'. apply/H. instantiate (1 := p0.1). destruct p0. ssa'. apply/orP. auto.
done.
Qed. 



Lemma mem_zip2 : forall (A B : eqType) aa bb n (a : A) (b : B) ad bd, size aa = size bb -> n < size aa -> nth ad aa n = a -> nth bd bb n = b ->  (a,b) \in zip aa bb.
Proof. 
move => A B. elim. case. ssa'. destruct n.  ssa'. ssa'. 
move => a l IH [] //=. ssa'.
destruct n. ssa'. subst. apply/orP.  auto. 
rewrite inE. apply/orP. right. ssa'. inv H. have : n < size l by lia.  intros. inv H.  apply/IH. done. eauto. eauto. eauto. Qed. 



Lemma uniq_index1 : forall {A : eqType} l n (e : A), uniq (map fst l) -> (n,e) \in l -> label_index l n = Some e.
Proof. 
move => A. elim. ssa'. ssa'. 
rewrite inE in H1. destruct (orP H1). rewrite -(eqP H0) eqxx //=.
destruct a. ssa'.
rewrite -(zip_fs l) in H0. apply mem_zip in H0. ssa'. case_if. rewrite (eqP H5) in H0.
rewrite H0 in H2. done. 
apply/H.  done. destruct (orP H1). move/eqP : H6. case. ssa'. subst. 
move/eqP : H5. done. eauto.
Qed. 

Lemma uniq_index2 : forall {A : eqType} l n (e : A), uniq (map fst l) -> label_index l n = Some e ->  (n,e) \in l.
Proof. 
move => A.  elim. ssa'. ssa'. destruct a. move : H1. case_if. 
rewrite (eqP H0). case. intros. subst. done. 
ssa'. apply/orP. right. apply/H. done. done. 
Qed. 

Lemma uniq_index : forall {A : eqType} l n (e : A), uniq (map fst l) -> (n,e) \in l <-> label_index l n = Some e.
Proof. 
intros. split. apply/uniq_index1. done. apply/uniq_index2. done. 
Qed. 

Lemma uniq_match : forall {A : eqType} l l' n (e e' : A) , uniq (map fst l) -> map fst l = map fst l' -> label_index l n = Some e -> 
label_index l' n = Some e' -> exists n, ((n,e),(n,e')) \in zip l l'.
Proof. 
move => A. elim. case. ssa'. ssa'. move => a l IH. case. ssa'. ssa'. 
destruct a. destruct a0. 
move : H1. case_if. case. intros. subst. 
move : H2. case_if. case. intros. subst. rewrite -(eqP H) -(eqP H1).
exists n. done. ssa'. inv H0. rewrite H1 in H. done. 
move : H2. case_if. case. intros. subst. ssa'. inv H0. rewrite H in H1. done. 
ssa'. inv H0.  eapply IH in H4.  2 : eauto. 2 : apply/H5. 2 : apply/H2. destruct H4. 
exists x. rewrite inE. apply/orP. right. done. 
Qed. 

Lemma uniq_labels_ren : forall g sigma, uniq_labels g -> uniq_labels g ⟨e sigma ⟩.
Proof. elim;rewrite //=;intros. ssa'. ssa'. 
rewrite -map_comp fst_c. done. 
rewrite all_map. apply/allP. intro. intros. simpl. 
destruct x. ssa'. apply/H. eauto. have : s0 = (s,s0).2 by done. 
move=>->.
apply (allP H2). done.  
Qed. 

Lemma uniq_labels_subst : forall g sigma, (forall n, uniq_labels (sigma n)) ->  uniq_labels g -> uniq_labels g [e sigma].
Proof. elim;rewrite //=;intros. ssa'. asimpl. apply/H. case. ssa'. ssa'. 
asimpl. apply/uniq_labels_ren. done.  done. 
ssa'. rewrite -map_comp fst_c.  done. 
rewrite all_map. apply/allP. intro. intros. simpl. 
destruct x. ssa'. apply/H. eauto. done. have : s0 = (s,s0).2 by done. 
move=>->.
apply (allP H3). done.  
Qed. 


Lemma step_uniq : forall e l e', Estep e l e' -> uniq_labels e -> uniq_labels e'. 
Proof. 
move => e l e'. elim;ssa'. 
move : (allP H2 _ H). ssa'.
elim : es0 es1 H4 H5 H H0 H1. case. ssa'. 
move => a l0. ssa'. move => a l0 IH. case. ssa'. move => a0 l1. ssa'. 
inv H. inv H. 
apply/allP. move => x xIn.
move/inP : xIn. intro. eapply In_zip2 in xIn. destruct xIn. 2 : { apply size_map_snd. eauto. }
ssa'. apply H1 in H6. done.
apply (allP H5). apply/inP.  done. 
apply/H0. 
apply/uniq_labels_subst. ssa'. destruct n. ssa'. ssa'. done. 
Qed. 

Lemma uniq_unf : forall g, uniq_labels g ->  uniq_labels (eunf g). 
Proof. case=>//=. intros. apply/uniq_labels_subst. case. done. done. done. 
Qed.

Lemma uniq_full_unf : forall g, uniq_labels g -> uniq_labels (full_eunf g). 
Proof. 
intros. rewrite /full_eunf. remember (emu_height g). clear Heqn. elim : n g H. done. 
intros. simpl. apply/uniq_unf . eauto. 
Qed.


Lemma Forall_and : forall l0 l1, size l0 = size l1 ->
          Forall
          (fun p : fin * lType * (fin * lType) =>
           p.1.1 = p.2.1 /\ upaco2 (ApplyF full_eunf full_eunf \o EQ2_gen) bot2 p.1.2 p.2.2) 
          (zip l0 l1) -> map fst l0 = map fst l1.
Proof. 
elim. case. ssa'. ssa'. 
move => a l IH. case. ssa'. ssa'. inv H.  inv H0. ssa'. pc. 
f_equal. done. apply/IH. inv H. done. 
Qed. 

Lemma Forall_and2 : forall l0 l1, map fst l0 = map fst l1 -> 
                             Forall (fun x0 : fin * lType * (fin * lType) => x0.1.1 = x0.2.1) (zip l0 l1).
Proof. 
elim. case. ssa'. ssa'. move => a l IH. case. ssa'. ssa'. con. ssa'. inv H. inv H. auto.
Qed. 



Lemma Estep_EQ2 : forall e0 e0' l e1 e1',EQ2 e0 e1 ->  uniq_labels e0 -> uniq_labels e1 ->   Estep e0 l e0' -> Estep e1 l e1' ->  EQ2 e0' e1'.  
Proof. 
pcofix CIH. move => e0 e0' l e1 e1' H0 H3 H4 H1 H2. elim : H1 e1 e1' H2 H0 H3 H4;intros. 
apply Estep_full_unf2 in H2. punfold H0. inv H0. inv H. pc. 
rewrite -H9 in H2. pc. inv H2. apply/paco2_mon. eauto. done. 
apply Estep_full_unf2 in H2. punfold H3. inv H3. inv H6. pc. rewrite -H12 in H2. pc. inv H2;try done.  
pfold. con. con. right. apply/CIH;eauto. apply/step_uniq. eauto. ssa'. 

apply uniq_full_unf in H5. rewrite -H12 in H5. ssa'. 
apply Estep_full_unf2 in H2. punfold H0. inv H0. inv H1. rewrite -H9 in H2. inv H2;try done. 
have : map fst es = map fst es1. 
clear H9 H2 H13 H H0 H3 H1.
elim : es es1 H10 H7. case. ssa'. ssa'. 
move => a l0 IH. case. ssa'. ssa'. f_equal. inv H10. ssa'. 
apply/IH. inv H10.  inv H7. ssa'.
have : exists n', ((n',e),(n',e1')) \in zip es es1. apply/uniq_match. 
ssa'. done. 
apply/uniq_index. done. eauto.
apply/uniq_index. rewrite -x. done. done. 
case. ssa'. 
move/ForallP : H10. move/inP : p => p. intro. apply H10 in p. ssa'.  pc.
apply/paco2_mon. eauto. done.

apply Estep_full_unf2 in H3. punfold H4. inv H4. inv H7. rewrite -H12 in H3. inv H3;try done. 
pfold. con. con. apply size_map_snd in H. rewrite -H H10. ssa'.
clear H3. apply size_map_snd in H17 as H17'. apply size_map_snd in H as H'. 
apply uniq_full_unf in H6. rewrite -H12 in H6.

have : uniq_labels (EBranch Sd c' es4). apply/step_uniq.
2 : apply/H6. apply estep_branch_async. rewrite -H17 //=.  
2 : eauto. intros. apply/H18.  done. ssa'. 
have : map fst es0 = map fst es3. apply/Forall_and.  done. done. 
intros. clear H12.
apply/List.Forall_and. apply/Forall_and2. rewrite -H17 -H //=.
clear H.
apply size_map_snd in x. clear H17 H4 H7.
elim : es0 es1 es3 es4 H' H17' H10 x H18 H3 H8 H13 H9 H11 H0 H1 H6 H14. 
case=>//=. case=>//=. case=>//=.
move => a l0 IH. case=>//=. 
move => a0 l1. case=>//=.
move => a1 l2. case=>//=.
move => a2 l3. case. move => Heq1. case. move => Heq2. case. move => Heq3. case. move=> Heq4.

ssa'. con. inv H13. ssa'. pc. right. apply/CIH. apply/H16.  done. done. apply/H0. auto. 
apply/H18. auto. apply/IH. done. 4 : { intros. apply/H18. eauto. } 
done.   done. done. done. done. inv H13.  done. done. 
eauto. eauto. done. done.

apply/H0.  eauto. apply EQ2_eunfl2 in H1. rewrite full_eunf_subst in H1. apply EQ2_eunfl in H1. done. 
apply/uniq_labels_subst. case;done. done. done. 
Unshelve. all : repeat con.
Qed.

Definition env := ptcp -> lType. 

Definition update (f : ptcp -> lType) p e := fun p0 => if p0 == p then e else f p0.
Definition update_action (f : ptcp -> lType) (a : action) e0 e1 := 
update (update f (ptcp_from a) e0) (ptcp_to a) e1. 

Inductive EnvStep : env -> label -> env -> Prop := 
| envstep_rule l (f : env) e e' :  Estep (f (ptcp_from l.1)) (Sd,action_ch l.1,l.2) e ->
                                   Estep (f (ptcp_to l.1)) (Rd,action_ch l.1,l.2) e' ->
                                   EnvStep f l (update_action f l.1 e e'). 
Hint Constructors EnvStep.
Definition EnvStep2 f l f'' := exists f', EnvStep f l f' /\ (forall p, EQ2 (f' p) ( (f'' p))). 

Definition projectable g := forall p, exists e, Project g p e. 

Lemma proj_msg_exists : forall a u g p, (exists e,  Project (GMsg a u g) p e) ->  (exists e,  Project g p e).
Proof. 
intros. destruct H. punfold H.  inv H. inv H0. exists e0. pclearbot.   done. 
pclearbot. exists (full_eunf x). done. exists EEnd. pfold. con. con.  move : H2. rewrite -!part_of2_iff.  eauto. 
move : H4. rewrite -!gInvPred_unf_iff. eauto. 
Qed.

Lemma projectable_msg : forall a u g, projectable (GMsg a u g) -> projectable g. 
Proof. 
intros. move : H. rewrite /projectable. intros. move : (H p). apply/proj_msg_exists . 
Qed.

Lemma proj_branch_exists : forall a gs g p, (exists e,  Project (GBranch a gs) p e) -> In g gs ->  (exists e,  Project g.2 p e).
Proof. 
intros. destruct H. punfold H. inv H. inv H1. 
move : H0. move/inP. move/nthP.  move/(_ (0,GEnd)). case. 
move => x0. intros. subst. 
have : In (nth ((0,GEnd),(0,EEnd)) (zip gs es) x0) (zip gs es). apply/inP. apply/mem_nth. 
rewrite size_zip H6 minnE. have : size es - size es = 0 by lia.  move=>->. rewrite -H6. have : size gs - 0 = size gs by lia. move=>->. done. 
move/H7. case=>//=. rewrite nth_zip //=. intros. exists (nth EEnd (map snd es) x0). 
pc. rewrite -(zip_fs es) in b. rewrite nth_zip in b. ssa'. rewrite !size_map //=.
move/H7 : H0. ssa'. pclearbot. eauto. 
exists EEnd. pfold. con. con.  move : H3. rewrite -!part_of2_iff.  eauto. 
move : H5. rewrite -!gInvPred_unf_iff. eauto. 
Qed.

Lemma projectable_branch : forall a gs, projectable (GBranch a gs) -> forall g, In g gs ->  projectable g.2. 
Proof. intros. move : H. rewrite /projectable. intros. move: (H p). move/proj_branch_exists. eauto. 
Qed.


Lemma size_pred_ren : forall g sigma, size_pred g = size_pred g ⟨g sigma ⟩.
Proof. elim;rewrite //=;intros. ssa'. rewrite size_map.  f_equal. 
elim : l H. done. ssa'. erewrite H0. f_equal.  instantiate (1:= sigma). destruct a0. ssa'. 
apply/H. intros. apply/H0. eauto.  eauto. instantiate (1:= a0.1). destruct a0. done. 
Qed. 

Lemma size_pred_subst : forall g sigma, (forall n, size_pred (sigma n)) ->  size_pred g = size_pred g[g sigma].
Proof. elim;rewrite //=;intros. 
rewrite H //=. apply/H. case. done. simpl. intros. asimpl. rewrite -size_pred_ren. done. 
rewrite size_map. f_equal. 
elim : l H H0. done. ssa'. erewrite H0. f_equal.  instantiate (1 := sigma). destruct a0. ssa'.
apply/H. intros. apply/H0. eauto.  eauto. done. instantiate (1:= a0.1). destruct a0. done.
done. 
Qed.

Lemma size_pred_subst2 : forall g sigma, size_pred g[g sigma] -> size_pred g.  
Proof. elim;rewrite //=;intros. eauto. ssa'. rewrite size_map in H1. ssa'. 
apply/allP=> x xIn. apply/H. 
eauto. instantiate (1:= x.1). destruct x. done. 
instantiate (1:= sigma). ssa'. 
rewrite all_map in H2. move :  (allP H2 _ xIn). ssa'. destruct x. ssa'. 
Qed.


Lemma size_pred_unf : forall g, size_pred g ->  size_pred (unf g). 
Proof. case=>//=. intros. rewrite -size_pred_subst. done. case. done. done. 
Qed.

Lemma size_pred_full_unf : forall g, size_pred g ->  size_pred (full_unf g). 
Proof. 
intros. rewrite /full_unf. remember (mu_height g). clear Heqn. elim : n g H. done. 
intros. simpl. apply/size_pred_unf . eauto. 
Qed.

Lemma size_pred_unf2 : forall g, size_pred (unf g) ->  size_pred g. 
Proof. intros.  destruct g;try done. simpl in H. ssa'. apply size_pred_subst2 in H. done. 
Qed. 

Lemma size_pred_full_unf2 : forall g, size_pred (full_unf g) ->  size_pred g. 
Proof. 
intros. rewrite /full_unf in H. remember (mu_height g). clear Heqn. elim : n g H;try done. 
ssa'. apply/H.  apply/size_pred_unf2. done. 
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

Lemma or_strong : forall g p e, Project g p e -> size_pred g -> part_of_all2 p g /\ full_eunf e <> EEnd \/ full_eunf e = EEnd.
Proof. 
intros. apply part_of2_or_end in H as H'. destruct H'. left. ssa'. 
move => HH. apply Project_eunf2 in H. rewrite HH in H. apply Project_not_part in H. 
apply/size_part;eauto. eauto. 
Qed.

Lemma comp_from : forall a,  comp_dir (ptcp_from a) a.
Proof. case. intros. simpl. rewrite /comp_dir /= eqxx. done. 
Qed.

Lemma comp_to : forall a,  comp_dir (ptcp_to a) a.
Proof. case. intros. simpl. rewrite /comp_dir /= eqxx. case_if;done. Qed.
Hint Resolve comp_from comp_to. 

Lemma preserve_proj  : forall g l g' p d,  step g l g' -> comp_dir p l.1 = Some d ->  Linear  g -> size_pred g ->  
Estep (trans p g) (d,action_ch l.1,l.2)  (trans p g'). 
Proof.
move => g l g' p c. elim;intros;simpl in *.  rewrite H.  con. rewrite H0. con.
have : (n, trans p g0) =  (prod_map id (trans p)) (n,g0). done. 
move=>->. apply/map_f. done.

remember H1. clear Heqi.
rewrite inE negb_or !inE in H1. ssa'. 
rewrite /comp_dir. case_if. 
- con. apply/H0. done. apply/linear_sgmsg.  eauto. ssa'. intro.  apply Logic.eq_sym in H7.
  move : H7. apply/distinct_ch. 3 : eauto. 
  done. ssa'. eauto. done.  
- case_if. rewrite /comp_dir in H2.  rewrite (eqP H7) in H2. move/negbTE : H6 =>HH. rewrite HH in H2. 
  move : H2. rewrite (negbTE H5) //=. 
  apply/H0;eauto.  apply/linear_sgmsg. eauto. 
- rewrite /comp_dir. case_if. con. 
  rewrite -!map_comp fst_c //=. ssa'.
  move/linear_branch : H4=>H4. move : H8=>H5. clear H5. 
  elim : gs gs' H H0 H1 H4 H7 H9. case=>//=. move => a0 l1 IH. case=>//=. move => a1 l2 [] Heq.
  intros.  destruct H7. inv H5. rewrite /prod_map. destruct a0,a1. ssa'. 
  have : g1 = (n0,g1).2. done. move=>->.
  have : g0 = (n,g0).2. done. move=>->.
  apply/H1. auto.
  done. eauto. done. apply/IH.  eauto. eauto. eauto. eauto. intros. done. ssa'. 

  intro. apply Logic.eq_sym in H7. move : H7.
  apply/distinct_ch. 3 : eauto. 
  done. ssa'. eauto. done.  
  move : H2 H3. rewrite !inE negb_or. ssa'. case_if.  
  move : H3. rewrite /comp_dir. rewrite (eqP H5). rewrite (negbTE H7) (negbTE H8) //=. 
- destruct gs;try done. simpl. destruct gs';try done. simpl. simpl in H1. apply/H1. eauto. done.  
  move/linear_branch : H4. move => HH. apply/HH. done. ssa'. 

- case_if. con. rewrite proj_subst /= in H0. move : H0. asimpl. simpl. rewrite H4. intros. apply/H0;eauto. 
  apply/linear_unf.  done. rewrite -size_pred_subst. done. case;done. 

  have :  Estep (trans p g0 [gGRec g0 .: GVar]) (c, action_ch l0.1, l0.2) (trans p g'0). 
  apply/H0;eauto. apply/linear_unf. done. rewrite -size_pred_subst. done. case;done. 
  rewrite proj_subst /=. asimpl. simpl. rewrite H4.  move/Estep_full_unf2.
  rewrite full_unf_com. apply eguarded_unfv  in H4.  rewrite H4. simpl. move => HH.  inv HH. 
  case. done.  done. 
Qed.

Lemma EQ2_refl : forall e, lInvPred e -> EQ2 e e.
Proof. 
pcofix CIH. intros . punfold H0. inv H0. pfold. con. inv H;con;pclearbot.  eauto. done. clear H1.
elim : es H2. intros.  simpl. auto. intros. inv H2. con;eauto. pclearbot. simpl. ssa'. 
Qed.

Lemma step_gInvPred : forall g l g', step g l g' -> gInvPred g -> gInvPred g'. 
Proof. 
move => g l g'. elim;intros. eauto. punfold H0. move/inP : H. intro. inv H0. inv H1. 
move/ForallP : H3. move/(_ _ H). case=>//=.
pfold. con. con. left. eauto. 
pfold. con. con. punfold H3. inv H3. inv H4. clear H3 H4.
elim : gs gs' H H0 H1 H6;try done. case=>//=. 
move => a0 l0' IH [] //=. intros. inv H. inv H6. pc. con;eauto. left. apply/H1. eauto. done. 
apply/ForallP. intros. left.
eapply (@In_zip2 _ _ _ l0' l1) in H3. destruct H3. ssa'. 


apply (@size_map_snd _ _ l0' l1) in H5. 
apply/H1.  eauto.
move/ForallP : H9. 
move/( _ _ H3). case=>//=. apply/size_map_snd.  done. 
apply/H0. rewrite gInvPred_unf_iff in H1. rewrite full_unf_subst in H1. rewrite -gInvPred_unf_iff in H1. done. 
Qed.

Lemma inotin : forall g i sigma, (forall n, i !=  sigma n) -> i \notin lType_fv g ⟨e sigma ⟩.
Proof.
elim;rewrite /=;try done;intros. rewrite !inE. specialize H with n. lia.
apply/negP=>HH. destruct (mapP HH). subst. rewrite mem_filter in H1. ssa'. 
apply/negP. apply/H. 2 : eauto. asimpl. case. done. simpl. intros. asimpl. destruct x;try done.  simpl in *. 
suff : x <> sigma n. lia. apply/eqP. done. 
apply/negP=>HH. destruct (flattenP HH). destruct (mapP H1). subst. destruct (mapP H3). subst. apply/negP. apply/H. eauto. 
eauto. instantiate (1:= x.2). instantiate (1 := x.1). destruct x. done. 2 : { ssa'. destruct x.   ssa'. eauto . }
done. 
Qed.

Lemma lcontractive_ren : forall g sigma, injective sigma -> (forall n, n <= sigma n) ->  lcontractive  g -> lcontractive g ⟨e sigma ⟩.
Proof.
elim;intros;simpl;try done. 
asimpl. split_and. have : 0 = ( 0 .: sigma >> succn) 0. done. intros. rewrite {1}x.

rewrite -eguarded_ren_iff. simpl in H2. split_and. auto.
apply H. auto.  case. done. done.  simpl in H2. split_and. apply H.  done. done. done.
rewrite all_map. apply/allP. intro. intros. simpl. destruct x. ssa'. apply/H. eauto. done. done. 
move : (allP H2 _ H3). ssa'. 
Qed.

Lemma lcontractive_subst : forall g sigma,lcontractive g -> (forall n, lcontractive (sigma n)) -> lcontractive g [e sigma].
Proof. 
elim;rewrite /=;intros;try done. 
asimpl. split_and. 
apply/eguarded_sig2.
instantiate (1 := (EVar 0 .: EVar  >>  ⟨e ↑ ⟩)).  asimpl. done.
case. done. simpl. intros. apply/eguarded_fv. asimpl. apply/inotin. done.
apply H. done.  intros. destruct n.  done. simpl. asimpl.  apply/lcontractive_ren. done. done. done.
apply H. done.  intros. done. 
rewrite all_map. apply/allP. intro. intros. simpl. destruct x. ssa'. apply/H. eauto. 
move : (allP H0 _ H2). ssa'. done.
Qed.

Lemma lcontractive_unf : forall g , lcontractive g -> lcontractive (eunf g). 
Proof.
intros. rewrite /eunf. destruct g;try done. apply/lcontractive_subst. ssa'. case;done. 
Qed.

Lemma lcontractive_iter_unf : forall k g , lcontractive g -> lcontractive (iter k eunf g). 
Proof.
elim;try done. intros. simpl. apply/lcontractive_unf. ssa'. 
Qed. 

Lemma lcontractive_full_eunf : forall g , lcontractive g -> lcontractive (full_eunf g). 
Proof. 
intros. rewrite /full_eunf. apply/lcontractive_iter_unf. done. 
Qed.

Lemma emu_height_subst_contractive : forall g0 sigma, (forall n, 0 < emu_height (sigma n) -> eguarded n g0) -> lcontractive g0 -> emu_height (g0[e sigma]) = emu_height g0.
Proof. 
elim; try solve [by rewrite /=];intros.
asimpl. move : (H n). destruct (emu_height (sigma n)) eqn:Heqn. done. have : 0 < n0.+1 by lia. move => + HH. move/HH=>//=. lia. 
simpl. f_equal. asimpl. apply H. case. rewrite //=. move=> n/=. move => HH. apply/H0. move : HH. asimpl. rewrite emu_height_ren //=. ssa'. 
Qed.

Lemma emu_height_unf_contractive : forall g , lcontractive g -> (emu_height g).-1 = emu_height (eunf g).
Proof.
move => g. rewrite /=. case : g; try solve [intros;rewrite /=;done].
intros. rewrite /=. ssa'. erewrite emu_height_subst_contractive. done. eauto. case. done. done. done. 
Qed.

Lemma emu_height_iter_unf : forall k g , lcontractive g -> (emu_height g) - k = (emu_height (iter k eunf g)). 
Proof.
elim;intros. rewrite /=. lia.
rewrite /=. have : emu_height g - n.+1 = (emu_height g - n).-1 by lia. move=>->. 
erewrite H. rewrite emu_height_unf_contractive //=.  apply/lcontractive_iter_unf.  done. done. 
Qed.

Lemma iter_eunf_not_rec : forall g k, lcontractive g -> emu_height g <= k -> forall g', iter k eunf g <> ERec g'.
Proof.
intros. simpl in *. apply (emu_height_iter_unf k) in H. move : H. 
have : emu_height g - k  = 0 by lia. move=>->. intros. destruct (iter k eunf g);try done.
Qed.

Lemma to_lInvPred : forall e, (forall n, n \notin lType_fv e) -> lcontractive e -> lInvPred e. 
Proof. 
pcofix CIH. 
intros. pfold. con. remember H1 as Hcont. clear HeqHcont. apply lcontractive_full_eunf in H1.
have : forall n : nat_eqType, n \notin lType_fv (full_eunf e). 
intros. rewrite -lType_fv_full_eunf. done. clear H0=>H0.
destruct (full_eunf e) eqn:Heqn. 
move : (H0 n). ssa'. lia. con. 
con. right. apply/CIH. ssa'. ssa'. 
con. 
ssa'. 
apply/ForallP=> x xIn. right. apply/CIH.
intros. apply/negP=> HH. apply (negP (H0 n)). apply/flattenP. exists (lType_fv x.2)=>//=. 
apply/map_f. apply/inP. done. 
apply (allP H1). apply/inP. done. rewrite /full_eunf in Heqn. have : emu_height e <= emu_height e by lia.  intros. 
move : (@iter_eunf_not_rec e (emu_height e) Hcont x l). rewrite Heqn. done. 
Qed.

Lemma gInvPred_proj : forall p g, gInvPred g -> lInvPred (trans p g). 
Proof. 
intros. apply/to_lInvPred. intros. apply/negP. move/fv_proj=>HH. 
move/gInvPred_no_fv : H. move/(_ n). rewrite HH //=.   
apply/proj_lcontractive. 
Qed.


Lemma step_lInvPred  : forall g l g' p,  step g l g' -> gInvPred g -> lInvPred (trans p g').  
Proof. 
intros. apply step_gInvPred in H;eauto. apply/gInvPred_proj. done. 
Qed.


Lemma EQ2_trans : forall e0 e1 e2, EQ2 e0 e1 -> EQ2 e1 e2 -> EQ2 e0 e2. 
Proof. 
pcofix CIH. intros. punfold H0. inv H0. punfold H1. inv H1. clear H0 H1. pfold. con. move : H2. 
inv H;intros.  inv H0. con. inv H3;con. pclearbot. eauto. 
inv H4;con. lia. clear H9 H1 H0 H H4. elim : es0 es1 es3 H2 H7 H3 H10. case=>//=. case=>//=. 
move => a l IH. case=>//=. move => a0 l0 [] //=. intros. inv H2.  inv H7. inv H3. inv H10. pclearbot. simpl in *. 
con;eauto. ssa'.  rewrite H5 H //=. pc.  eauto. 
Qed.

Lemma projectable_unf : forall g, projectable (GRec g) -> projectable (g [g GRec g .: GVar]). 
Proof. intros. move  : H. rewrite /projectable. intros. move : (H p). case. intros. punfold p0. inv p0. 
rewrite full_unf_subst in H0. exists x.   pfold. con. done. 
Qed.

Lemma preserve_proj2  : forall g l g' p e,  step g l g' -> Project g p e -> gInvPred g -> comp_dir p l.1 = None  ->  Linear  g -> size_pred g ->  
EQ2 (trans p g) (trans p g'). 
Proof.
move => g l g' p e Hstep. elim : Hstep e;intros;simpl in *.  rewrite H1.  apply/EQ2_refl. apply/gInvPred_proj. eauto. 
rewrite H2. ssa'.
have : forall g, In g gs -> Project g.2 p e. 
move : H0 => p0. punfold p0. inv p0. intros. apply/Project_eunf. inv H0. 
rewrite H10 in H2. done. move/H12 : H4. ssa'. destruct H7;try done.  
pfold. con. con. move : H8. rewrite -!part_of2_iff. eauto. 
move : H10. rewrite -!gInvPred_unf_iff.  eauto. 
intros. destruct gs;try done. simpl. 
have : In p0 (p0::gs). simpl. auto. move/x=>HH. 
move/inP : H. move/x. move/proj_complete_wrt_Project. case. ssa'. 
rewrite /proj in H7. move : H7. case_if;try done. case. move=>->. 
apply proj_complete_wrt_Project in HH. destruct HH. ssa'. 
rewrite /proj in H9. move : H9. case_if;try done. case. move=>->. 
apply/EQ2_trans. apply/EQ2_sym. eauto. done.

punfold H2. inv H2. inv H7. rewrite H10. pfold. con.   con. left. destruct H13;try done.  apply/H0;eauto. apply/linear_sgmsg. eauto.
rewrite H11. destruct H13;try done. apply/H0;eauto. apply/linear_sgmsg. eauto.
have : comp_dir p a = None. have : ~ comp_dir p a. rewrite -part_of2_iff in H9. eauto. destruct (comp_dir p a);done. 
move=>->. apply/H0. instantiate(1 := EEnd). pfold. con. con. rewrite -part_of2_iff. rewrite -part_of2_iff in H9. eauto. 
move : H11. rewrite -!gInvPred_unf_iff. eauto. rewrite -gInvPred_unf_iff in H11. eauto. done. apply/linear_sgmsg. eauto. ssa'.  
punfold H3. inv H3. inv H8. rewrite H12. pfold. con. con. rewrite !size_map //=. 
clear H3. punfold H4. punfold H4. inv H4. inv H9. clear H4 H3. move/linear_branch : H6. ssa'. clear H3. clear H12 H11 H8. 
elim : gs gs' es H H13 H15 H0 H1 H14 H6 H4 H9. case=>//=. move => a0 l1 IH. case=>//=. move => a1 l2 [] //=. move => a2 l3. case. 
intros. con;eauto.  ssa'. destruct a0,a1. ssa'. left. destruct a0,a1.  ssa'. 
have : In (n,g0) ((n,g0)::l1). ssa'.  intro. 
eapply (@In_zip _ _ _ _ (a2::l3)) in x. destruct x.
ssa'. apply H14 in H10. ssa'. case : H11=>//=;intros.  

have : g0 = (n,g0).2. done. move=>->.
have : g1 = (n0,g1).2. done. move=>->. 
apply/H3. eauto. eauto. inv H15. pc. ssa'.  done. eauto. done. done. apply/IH. done. 
instantiate (1:= l3). inv H13.  inv H15.  eauto. eauto. eauto. eauto. ssa'. ssa'. ssa'. con. eauto. inv H15. 

rewrite H11. punfold H4. inv H4. inv H9. clear H4 H9 H3. move/linear_branch : H6. intros.  
 destruct gs;try done. simpl. destruct gs';try done. simpl. 
have : In p0 (p0 ::gs). simpl. auto. move/H14. case=> HH [] //= HH2.  
apply/H1. ssa'.  eauto. inv H13.  pc.  ssa'. done. apply/H6. done. ssa'. 
have : comp_dir p a = None. have : ~ comp_dir p a. rewrite -part_of2_iff in H10. eauto. destruct (comp_dir p a);done. 
move=>->. 
have : In (nth ((0,GEnd),(0,GEnd)) (zip gs gs') 0) (zip gs gs'). apply/inP/mem_nth. apply size_map_snd in H. rewrite size_zip H minn_same //= -H //=. ssa'.
intros. rewrite nth_zip //= in x.
 eapply H1 in x. 
rewrite -!nth0. 
repeat erewrite  nth_map. 
have : In (nth (0,GEnd) gs 0) gs. apply/inP/mem_nth. ssa'. intros. eauto. ssa'. apply size_map_snd in H.  rewrite -H //=. ssa'. 
instantiate (1 := EEnd). pfold. con. con. rewrite -(zip_fs gs).  move : H10.  rewrite -!part_of2_iff. rewrite nth_zip. simpl. 
intros. intro.  apply/H10. con. con. erewrite nth_map in H11.  econstructor 4.  2: eauto. apply/inP/mem_nth. ssa'. ssa'. 
rewrite !size_map //=.  rewrite -(zip_fs gs). rewrite nth_zip.  ssa'. punfold H4. inv H4. inv H7. move/ForallP : H15. intros. 
erewrite nth_map.  instantiate (1:= (0,GEnd)).  
have : In (nth (0,GEnd) gs 0) (gs). apply/inP/mem_nth. done.  move/H15. case=>//=. ssa'.
rewrite -!gInvPred_unf_iff. eauto. done. rewrite !size_map //=.
have : In (nth (0,GEnd) gs 0) (gs). apply/inP/mem_nth. ssa'.
punfold H12.  done.  apply/linear_branch.  eauto. apply/mem_nth.  ssa'. ssa'. rewrite -(zip_fs gs) nth_zip. ssa'. 
erewrite nth_map. instantiate (1:= (0,GEnd)). 
have : (nth (0,GEnd) gs 0) \in gs.  apply/mem_nth.  done. move/(allP H13). ssa'. done. rewrite !size_map //i. 
 ssa'. 

case_if. pfold. con. rewrite full_eunf_subst. rewrite proj_subst in H0. move : H0. asimpl. simpl. rewrite H6. 
intros. have :  (trans p g0) [eERec (trans p g0) .: GVar >> trans p] << (ApplyF full_eunf full_eunf \o EQ2_gen) >>
       (trans p g'0). apply/H0. apply Project_unfg2 in H1. rewrite full_unf_subst in H1. apply Project_unfg in H1. eauto. 
move : H2. rewrite gInvPred_unf_iff. rewrite full_unf_subst -gInvPred_unf_iff. done. 
done. apply/linear_unf. done. rewrite -size_pred_subst. done. case;done. 
intros. punfold x. inv x. 

rewrite proj_subst in H0. move : H0. asimpl. simpl. rewrite H6. intros. 
have :  (trans p g0) [e EEnd .: GVar >> trans p] << (ApplyF full_eunf full_eunf \o EQ2_gen) >>
       (trans p g'0). apply/H0. 
apply Project_unfg2 in H1. rewrite full_unf_subst in H1. apply Project_unfg in H1. eauto. 
move : H2. rewrite gInvPred_unf_iff. rewrite full_unf_subst -gInvPred_unf_iff. done. 
done. apply/linear_unf. done. rewrite -size_pred_subst. done. case;done. 
intros. punfold x. inv x. rewrite full_unf_com in H7. apply eguarded_unfv in H6. rewrite H6 /= in H7. 
pfold. con. inv H7. con. case=>//=. 
Unshelve. repeat con.
Qed.


Lemma label_pred : forall g l g',  step g l g' -> size_pred g ->  action_pred g -> ptcp_from l.1 != ptcp_to l.1.
Proof. intros. induction H;try done; simpl. ssa'. ssa'. 
apply/IHstep. ssa'. ssa'. ssa'. destruct gs;try done. ssa'. destruct gs';try done. ssa'. apply/H3. eauto. ssa'. ssa'. 
apply/IHstep. rewrite -size_pred_subst. done. case=>//=. rewrite -action_pred_subst. ssa'. case=>//=. 
Qed.

Lemma preserve_proj3  : forall g l g',  step g l g' -> action_pred g -> gInvPred g -> Linear  g -> size_pred g ->  (forall p, exists e, Project g p e)  ->
EnvStep2 (trans^~ g) l  (trans^~ g'). 
Proof.
intros. rewrite /EnvStep2. econstructor. ssa'. con. 
apply/preserve_proj;eauto.   rewrite /comp_dir eqxx //=. 
apply/preserve_proj;eauto.   rewrite /comp_dir eqxx //=. 
eapply label_pred in H3. rewrite eq_sym. rewrite (negbTE H3). done. eauto. done. 
intros. rewrite /update_action /update. 
case_if. rewrite -(eqP H5). apply/EQ2_refl. apply/gInvPred_proj. apply/step_gInvPred;eauto.  
case_if. rewrite -(eqP H6). apply/EQ2_refl. apply/gInvPred_proj. apply/step_gInvPred;eauto.
destruct (H4 p).   
apply/preserve_proj2;eauto. eauto. rewrite /comp_dir H6 H5 //=. 
Qed.


Definition one_shot g f := forall p, Project g p (f p). 

Lemma size_pred_step : forall g l g', step g l g' -> size_pred g -> size_pred g'. 
Proof. 
intros. induction H;try done;ssa'. move : (allP H2 _ H). ssa'. apply size_map_snd in H. rewrite -H. done. 
apply/allP=> x xIn. cbn. move/inP : xIn. intro. eapply In_zip2 in xIn. destruct xIn. ssa'.  apply/H2. eauto. 
move/inP : H0. move/(allP H5). ssa'. apply size_map_snd.  done. 
apply/IHstep. rewrite -size_pred_subst. done. case=>//=. 
Qed. 

Lemma uniq_estep : forall e0 l e' e'', uniq_labels e0 ->  Estep e0 l e' -> Estep e0 l e'' -> e' = e''. 
Proof.
move => e0 l e' e'' H H0. elim : H0 H e'';intros. 
- inversion H0;subst. done. done. 
- inversion H3. subst. done. subst. f_equal. apply H0. ssa'. done. 
- inversion H1. apply uniq_index in H. apply uniq_index in H7. rewrite H in H7. inv H7. ssa'. ssa'. 
- inversion H1. subst. done. subst. done. inv H4. f_equal. 
  ssa'. clear H4 H5 H13 H2. 
  elim : es1 es3 es0 H H11 H0 H1 H12 H6. 
  case=>//=. move => a l0. case=>//=. move => a l0 IH. case=>//=.
  case=>//=. move=> a2 l1. case=>//=. move=> a0 l2. case. move => Heq1. case. move => Heq2.
  ssa' . inv H11. f_equal.  destruct a,a2. ssa'. f_equal. subst. done. subst. 
  have : l3 = (a0.1,l3).2. done. move=>->. apply/H1.  eauto.  done. 
  have: l4 = (a0.1,l4).2. done.  move=>->.
  apply/H12. eauto. apply/IH;eauto.
  inv H2. apply/H0. ssa'. apply/uniq_labels_subst. case. done. done. done. done. 
Qed.

Lemma part_of_all_step : forall g p e, Project g p e -> part_of_all2 p g \/ ~ part_of2 p g.
Proof. 
intros. apply part_of2_or_end in H as H'. destruct H';try done. ssa'. right. 
move => HH. apply Project_eunf2 in H. rewrite H0 in H. apply Project_not_part in H. eauto. 
Qed.

Lemma part_of_all_step2 : forall g p e, Project g p e -> ~ part_of_all2 p g -> ~ part_of2 p g.
Proof. 
intros. apply part_of_all_step in H. destruct H.   done. done. 
Qed.

Lemma project_projT : forall p g e, Project g p e -> Project g p (trans p g). 
Proof. 
intros. apply/Project_EQ2. eauto. apply/proj_proj. done .
Qed.

Lemma label_not_part : forall g l g' p,step g l g' -> size_pred g ->  ~ part_of2 p g ->  comp_dir p l.1 = None. 
Proof. 
intros. induction H;try done;ssa'.  have : ~ comp_dir p a by eauto. simpl. destruct (comp_dir _ _);done.  
have : ~ comp_dir p a. eauto. destruct (comp_dir p a);done. 
have : ~part_of2 p g1. eauto. intros.  apply/IHstep. done. done.
ssa'. destruct gs;try done. ssa'. destruct gs';try done. ssa'. apply/H3.  eauto. done. 
intro. apply/H1. con. con. econstructor 4. simpl. left.  eauto. done. 
apply/IHstep. rewrite -size_pred_subst //=. case=>//=. move => HH. apply/H1. rewrite part_of2_iff. rewrite full_unf_subst -part_of2_iff. done. 
Qed.

Lemma preserve_not_part : forall g l g' p, step g l g' ->  ~~inp p g   -> ~~inp  p g'. 
Proof. intros. induction H. ssa'. rewrite negb_or in H0. ssa'. 
ssa'. rewrite negb_or in H0. ssa'. move/hasPn : H2. move/(_ _ H). ssa'. 
ssa'. move : H0. rewrite !negb_or. ssa'. ssa'. 
move : H0. rewrite !negb_or.  ssa'. apply/hasPn. intro. intros.
move : H0. move/[dup]. move/inP.  move =>HI.  eapply (@In_zip2 _ _ _ gs gs' ) in HI. destruct HI. ssa'. 
 apply/H2. eauto.  apply (hasPn H5). apply/inP. done. apply/size_map_snd.  done. 
ssa'.
apply/IHstep. rewrite inp_subst_iff . done. case. ssa'. done. 
Qed. 

Lemma preserve_proj5  : forall g l g' p,  step g l g' -> size_pred g /\ uniqg_labels g -> Linear g ->  Project g p (trans p g) -> Project g' p (trans p g').
Proof. 
intros. move : H1. move => Hlinear. move : H2 => H1. 
elim : H H0 H1 Hlinear;intros. 
- simpl in H1.  punfold H1. inv H1. inv H. rewrite H4 in H6. move : H6. cbn. case. move=><-. pclearbot. done. 
  pclearbot. rewrite H5 in H7. apply/Project_eunf=>//=. rewrite -part_of2_iff in H3. 
  have : ~ comp_dir p a by eauto. destruct (comp_dir p a);try done.  move => _. apply/Project_eunf. rewrite -H2. 
  pfold. con. con. rewrite -part_of2_iff. eauto. move : H5.  rewrite -!gInvPred_unf_iff. eauto. 
- punfold H1. inv H1. inv H2. rewrite H6 in H5. move : H5. cbn. case. intros . subst. 
  move/inP : H => H. eapply In_zip in H. destruct H. destruct H. apply H8 in H3. destruct H3. case : H4=>//=. ssa'.
  apply/Project_EQ2. eauto. apply/proj_proj. eauto. rewrite !size_map //=.
  move/inP : H. move/H8. case=>//=.  ssa'. pc.  rewrite H5 in b.  apply/Project_EQ2. eauto. 
  apply/proj_proj. eauto.

  destruct (comp_dir p a);try done. apply/Project_EQ2. instantiate (1:= EEnd). pfold. con. con.
  move : H4. rewrite -!part_of2_iff. intros. have : g0 = (n,g0).2. done. move=>->. apply/not_part2_branch. eauto. apply/inP. done. 
  rewrite -gInvPred_unf_iff. punfold H6. inv H6. inv H5.
  have: g0 = (n,g0).2. done. move=>->. move/ForallP : H8. intro. move/inP : H. move/H8. case=>//=.  
   apply/proj_proj. pfold. con. con. have : g0 = (n,g0).2. done. move=>->. rewrite -part_of2_iff. apply/not_part2_branch. 
  rewrite -part_of2_iff in H4. eauto. apply/inP. done. move : H6. rewrite -!gInvPred_unf_iff.
  intros. punfold H6. inv H6. inv H5. move/inP : H. move/ForallP: H8.  intros. apply H8 in H. case : H =>//=. 

- simpl. destruct (comp_dir p a) eqn:Heqn. pfold. con. con. done. left. apply/H0. ssa'. 
  have : exists e, Project (GMsg a u g1) p e. eauto. move/proj_msg_exists. case. 
  intros. apply/Project_EQ2. eauto. apply/proj_proj. done. apply/linear_sgmsg. eauto. 
  have : exists e, Project (GMsg a u g1) p e. eauto. move/proj_msg_exists. case. 
  intros. have : Project g2 p (trans p g2). apply/H0. ssa'. 
  apply/Project_EQ2. eauto. apply/proj_proj. done. apply/linear_sgmsg. eauto. 
  intros. apply part_of2_or_end in x0 as x0'. destruct x0'. 
  pfold. con. con. done. left. apply/Project_eunf2. done. done. 
  apply/Project_eunf. rewrite H4. pfold. con. apply/project_gen_end. 
  rewrite -part_of2_iff. apply Project_eunf2 in x0. rewrite H4 in x0. apply Project_not_part in x0. 
  have : ~ comp_dir p a.  destruct (comp_dir p a);try done. intros.  move => HH. inv HH. inv H5. inv H6. 
  rewrite -gInvPred_unf_iff. pfold. con. con. left. move : x0. move/Project_gtree. move/gInvPred_iff. done. 
- punfold H4.  inv H4. inv H5.  rewrite H9 in H8. simpl. rewrite H9. inv H8. pfold. con. con. done. rewrite size_map. apply size_map_snd. done. 
  simpl in H3. clear H8 H10 H9 H4 H5 H2.  move/linear_branch : Hlinear. move => Hlinear. destruct H3.  
  destruct (andP H2). clear H4. destruct (andP H3). clear H3 H4. clear H2. 
  elim : gs gs' H H0 H1 H11 Hlinear H5 H6. case=>//=. move => a0 l1 IH [] //=. intros. destruct H2.  
  subst. ssa'. destruct a1;done. left. destruct a1. simpl. 
  have : g0 = (n,g0).2. done. move=>->.  apply/H1. eauto. done.
  move : (H11 ((a0, prod_map id (trans p) a0))). ssa'. edestruct H4. eauto. pc. 
  destruct a0. ssa'. inv H.  ssa'. edestruct H5.  eauto. pc. done. eauto. inv H.  apply/IH. apply/H7. eauto. eauto. eauto.
  ssa'. ssa'.   ssa'. eauto. 

  move : H11. rewrite /= H8. intros. 

have :  Forall
         (fun p0  =>
           Project p0.2.2 p (trans p p0.2.2)) 
         (zip gs gs').
  apply/ForallP. intros.
  remember H6. clear Heqi.
  move/inP : H6. destruct x. move/mem_zip. ssa'.  
  apply/H1. eauto. ssa'.  apply (allP H14). done. 
  apply (allP H13). done. 
  apply/Project_EQ2.
  move/inP : H6. move/H11. ssa'. pc.  eauto. 
  apply/proj_proj. 
  move/inP : H6. move/H11. ssa'. pc.  eauto. apply/linear_branch.  eauto. done. 

move : H3 => Hsize. clear H1  H4 H5. intros. 
  have : Forall (fun g' => Project g'.2 p (trans p g'.2)) gs'. 
  clear H0 H9. clear Hsize Hlinear H11. elim : gs gs' H x. case=>//=. move => a0 l1 IH [] //=. move => a1 l2 []. intros. inv x. con;eauto.
  
  move/ForallP. move => Hfor.  
  have :  Forall
         (fun g' =>
           Project g'.2 p (head EEnd ((map ((trans p) \o snd) gs')))) 
         gs'. apply/ForallP. intros. rewrite -nth0. erewrite nth_map. instantiate (1 := (0,GEnd)).
  move : H1. 
  move/inP/nthP. move/(_ (0,GEnd)). case. intros. subst.  apply/Project_EQ2. apply/Hfor. apply/inP/mem_nth. done.
  destruct (comp_dir p l0.1) eqn:Heqnl. apply/Estep_EQ2. 
  instantiate (2 :=  (trans p (nth (0,GEnd) gs x1).2)). 
  instantiate (1 :=  (trans p (nth (0,GEnd) gs 0).2)). 
  have : In (nth (0,GEnd) gs x1) gs. apply/inP/mem_nth=> //=. apply size_map_snd in H. rewrite H //=.
  move/H11. ssa'. pclearbot. apply/EQ2_sym.  apply/proj_proj. move : H3. 
  move/Project_eunf. rewrite -nth0. erewrite nth_map. eauto. done. 
  ssa'. have : (nth (0, GEnd) gs x1) \in gs.    apply/mem_nth. apply size_map_snd in H. rewrite H //=. intro. 
  move : (allP H5 _ x0). ssa'. apply/uniq_trans. eauto. ssa'. apply/uniq_trans. apply (allP H5). apply/mem_nth.  done. 

  apply/preserve_proj;eauto.  
  have : In (nth ((0,GEnd),(0,GEnd)) (zip gs gs') x1) (zip gs gs'). apply/inP/mem_nth. apply size_map_snd in H. rewrite size_zip H minn_same //=.
  intros. rewrite nth_zip in x0. apply H0 in x0.  ssa'. apply/size_map_snd. done. apply/linear_branch. eauto. apply/mem_nth. 
  apply size_map_snd in H.  rewrite H //=. ssa'.  apply (allP H6). apply/mem_nth. apply size_map_snd in H. rewrite H //=.

  apply/preserve_proj;eauto.  
  have : In (nth ((0,GEnd),(0,GEnd)) (zip gs gs') 0) (zip gs gs'). apply/inP/mem_nth. apply size_map_snd in H. rewrite size_zip H minn_same //=. destruct gs,gs';done. 
  intros. rewrite nth_zip in x0. apply H0 in x0. ssa'. apply/size_map_snd. done.  apply/linear_branch. eauto. apply/mem_nth. destruct gs;done. 
  ssa'. apply (allP H6). apply/mem_nth=>//=. 
  have : In (nth ((0,GEnd),(0,GEnd)) (zip gs gs') 0) (zip gs gs'). apply/inP/mem_nth. apply size_map_snd in H. rewrite size_zip H minn_same //=. destruct gs,gs';done. intros.
  have : In (nth (0,GEnd) gs 0) gs. apply/inP/mem_nth=> //=. apply size_map_snd in H. rewrite H //=. destruct gs,gs';done. 
  have : In (nth (0,GEnd) gs x1) gs. apply/inP/mem_nth=> //=. apply size_map_snd in H.  rewrite H //=. 
  intros.


  apply/EQ2_trans.  instantiate (1 :=  (trans p (nth (0,GEnd) gs x1).2)).
  2 : { apply/EQ2_trans. 2 : { instantiate (1 :=  (trans p (nth (0,GEnd) gs 0).2)). 
  apply/preserve_proj2. rewrite nth_zip in x0.  apply H0 in x0. ssa'. eauto. apply/size_map_snd. done.
  move/H11 : x3. ssa'. pc. eauto. apply/gInvPred_iff. apply/Project_gtree. 
  move/H11 : x3. ssa'. pclearbot. eauto. done. apply/linear_branch. eauto. destruct gs;done. 
  ssa'. apply (allP H6). apply/mem_nth => //=. } 
  apply/EQ2_sym.  apply/proj_proj. move/H11 : x2. ssa'. pclearbot. move : H3. 
  move/Project_eunf. rewrite -nth0. erewrite nth_map. eauto. done. } 
  apply/EQ2_sym. 
  have : In (nth ((0,GEnd),(0,GEnd)) (zip gs gs') x1) (zip gs gs'). apply/inP/mem_nth. apply size_map_snd in H.
  rewrite size_zip H minn_same //=. intros. 
  apply/preserve_proj2. rewrite nth_zip in x4. eauto. apply/size_map_snd. eauto. 
  apply H11 in x2. ssa'. pc. eauto.  
  apply H11 in x2. ssa'. pc. eauto.  apply/gInvPred_iff. eapply Project_gtree. eauto. done. apply/linear_branch. eauto. apply/mem_nth. 
  apply size_map_snd in H. rewrite -H in p0. done. ssa'.  apply (allP H6). apply/mem_nth. apply size_map_snd in H. rewrite H. done.
  destruct gs;try done. destruct gs';try done.

  move/ForallP. move => Hfor2. 
  destruct (inp_all p (GBranch a gs')) eqn:Heqn. 
  pfold. con. apply/project_gen_branch_o. done. instantiate (1 := nth (0,GEnd) gs' 0). apply/inP/mem_nth . destruct gs',gs;done. 
  intros. simpl in Heqn.  rewrite H8 /= in Heqn. ssa'. apply/inp_all_iff. apply (allP Heqn). apply/inP. done. 
  left. apply/Project_eunf2.  apply/Hfor2. done. 
  remember Heqn. clear Heqe. 
  simpl in Heqn. rewrite H8 /= in Heqn. move : Heqn.  move/negP/negP. move/allPn. case. 
  intros. remember p0. clear Heqi. move/inP : p0. move/Hfor2. move => HH. 
  apply or_strong in HH as HH'. destruct HH'.  destruct H1. rewrite -inp_all_iff in H1. move : q. cbn. move=> q. rewrite H1 in q. done. 
  apply/Project_eunf. rewrite H1. 
  have :  forall x , In x gs' -> Project x.2 p EEnd. 
  intros. rewrite -H1. apply/Project_eunf2. apply/Hfor2.   done. 
  intros. clear Hfor2. 
  have : ~ part_of2 p (GBranch a gs'). 
  rewrite -inp_iff /= H8 /=. apply/negP. apply/hasPn. move => x' xIn. 
  move/inP : xIn. move/x1. move => HH3.  apply Project_not_part in HH3. apply/negP/inp_iff. done. 
  intros. pfold. con. con. rewrite -part_of2_iff. done. 
  rewrite -gInvPred_unf_iff. pfold. con. con. apply/ForallP. intros. left. 
  apply/gInvPred_iff. apply/Project_gtree. apply/x1. done. 
  move : i. move/nthP. move/(_ (0,GEnd)). case. intros. subst. 
  have : In (nth ((0,GEnd),(0,GEnd)) (zip gs gs') x1) (zip gs gs'). apply/inP/mem_nth. apply size_map_snd in H. rewrite size_zip H minn_same //=.
  intros. apply/size_pred_step.
rewrite nth_zip in x0. apply H0 in x0. eauto. apply/size_map_snd. done. ssa'. apply (allP H6). apply/mem_nth. 
  apply size_map_snd in H. rewrite H //=.

- have : comp_dir p a = None. have : ~ comp_dir p a. rewrite -part_of2_iff in H7. eauto. destruct (comp_dir p a);done. 
  intros. rewrite x in H6. simpl. rewrite x.  
  have : In (nth ((0,GEnd),(0,GEnd)) (zip gs gs') 0) (zip gs gs'). apply/inP/mem_nth. apply size_map_snd in H. rewrite size_zip H minn_same -H. ssa'. 
  intros. remember H0. clear Heqs. rewrite nth_zip in x0. apply H0 in x0. 
  eapply label_not_part in x0. 3 : { rewrite -part_of2_iff in H7. move => H8. apply/H7.
  con.   con. econstructor 4. 
  have : In (nth (0,GEnd) gs 0) gs. apply/inP/mem_nth. ssa'. intros eauto. eauto. eauto. } 
  have : EQ2 (head EEnd (map ((trans p) \o snd) gs))  (head EEnd (map ((trans p) \o snd) gs')).    
  rewrite -!nth0. repeat erewrite nth_map.
  have : In (nth (0,GEnd) gs 0) gs. apply/inP/mem_nth. ssa'. intros.  

   apply/preserve_proj2. apply/s. apply/inP. rewrite -nth_zip. apply/mem_nth. apply size_map_snd in H. rewrite size_zip H minn_same.
  destruct gs;try done.  destruct gs';try done. apply/size_map_snd . done.
  instantiate (1 := EEnd). pfold. con. con.
  intro. apply/H7. con. con. econstructor 4.  eauto. cbn. rewrite part_of2_iff. eauto. 
  punfold H9. inv H9. inv H8. move/ForallP : H11. move/(_ _ x1). case=>//=. rewrite gInvPred_unf_iff //=. 
  punfold H9. inv H9. inv H8. move/ForallP : H11. move/(_ _ x1). case=>//=. done. 
  apply/linear_branch. eauto. apply/mem_nth. destruct gs ;done. ssa'. apply (allP H12). apply/mem_nth. done. apply size_map_snd in H. rewrite -H. ssa'. ssa'. 
  intros. apply/Project_EQ2;eauto. apply/Project_eunf. rewrite -H6. pfold. con. con. 
  intro.  apply/H7. rewrite -part_of2_iff in H8. inv H8. inv H10. inv H11. con. con. con. done. 
  con. con. move/inP : H14. move/nthP. move/(_ (0,GEnd)). case. intros. subst. 
  econstructor 4. instantiate (1 := nth (0,GEnd) gs x2). apply/inP/mem_nth. apply size_map_snd in H. rewrite H //=. 
  have : In (nth ((0,GEnd),(0,GEnd)) (zip gs gs') x2) (zip gs gs'). apply/inP/mem_nth. apply size_map_snd in H. rewrite size_zip H minn_same -H. ssa'. 
  rewrite H //=. intros. rewrite nth_zip in x3. apply s in x3. eapply preserve_not_part in x3. 
  move/negP :x3. move/inp_iff. instantiate (1 := p). done. apply/negP. 
  rewrite -part_of2_iff in H7. move/inp_iff. move => HH2.  apply/H7. con. con. have : In (nth (0,GEnd) gs x2) gs. apply/inP/mem_nth. 

  apply size_map_snd in H. rewrite H //=. intros. econstructor 4. eauto. done. apply/size_map_snd. done. rewrite -gInvPred_unf_iff. pfold. con. con. 
  apply/ForallP. intros. left. 
  move/inP : H8. move/nthP. move/(_ (0,GEnd)). case. intros. subst. 
  have : In (nth ((0,GEnd),(0,GEnd)) (zip gs gs') x3) (zip gs gs'). apply/inP/mem_nth. apply size_map_snd in H. rewrite size_zip H minn_same -H. ssa'. rewrite H //=.
  apply size_map_snd in H.
  intros. rewrite nth_zip in x2. apply H1 in x2. apply/gInvPred_iff/Project_gtree. eauto. ssa'. 
  apply (allP H12). apply/mem_nth. rewrite H //=. apply (allP H11). apply/mem_nth. rewrite H //=.
  apply/project_projT. instantiate (1 := EEnd). pfold. con. con.
  move : H7. rewrite -!part_of2_iff.  have : In (nth (0,GEnd) gs x3) gs. apply/inP/mem_nth . rewrite H //=. 
  intros. eauto. 
  move : H9. rewrite -!gInvPred_unf_iff. 
have : In (nth (0,GEnd) gs x3) gs. apply/inP/mem_nth . rewrite H //=. eauto. 
  apply/linear_branch. eauto. apply/mem_nth. rewrite H //=. ssa'. ssa'. apply (allP H12). apply/mem_nth. done. apply/size_map_snd. done.
- apply/H0. rewrite -size_pred_subst . ssa'. apply/uniqg_labels_subst. case.  ssa'.  done.  done. case;try done. ssa'. 
  move : H2. move/Project_unfg2. rewrite full_unf_subst. move/Project_unfg.
  move/Project_eunf2. rewrite proj_eq_full. rewrite full_unf_subst. rewrite -proj_eq_full. move/Project_eunf. done. 
  apply/linear_unf. done. 
Unshelve. repeat con. 
Qed.



(*Linearity is important for soundness, counterexample
  A -> B : k<int>; A -> C :k<string>*)

Lemma uniq_labels_ren2 : forall g sigma, uniq_labels g ⟨e sigma ⟩ -> uniq_labels g.  
Proof. elim;rewrite //=;intros. ssa'. ssa'. eauto.
ssa'. rewrite -map_comp fst_c in H1.  done. 
rewrite all_map in H2. apply/allP. intro. intros. simpl. 
destruct x. apply/H. eauto. 
move : (allP H2 _ H0). ssa'. eauto.
Qed. 

Lemma uniq_labels_subst2 : forall g sigma, uniq_labels g [e sigma] -> uniq_labels g.
Proof. elim;rewrite //=;intros. ssa'. apply/H. eauto. 
eauto. ssa'.
rewrite -map_comp fst_c //= in H1.
clear H1. apply/allP. intro. intros. cbn. destruct x.  apply/H. eauto. 
rewrite all_map in H2. move : (allP H2 _ H0). ssa'.  eauto.
Qed.

Lemma uniq_unf2 : forall g, uniq_labels (eunf g) ->  uniq_labels g. 
Proof. case=>//=. intros. apply/uniq_labels_subst2. eauto. 
Qed.

Lemma uniq_full_unf2 : forall g, uniq_labels (full_eunf g) -> uniq_labels g. 
Proof. 
intros. rewrite /full_eunf in H. remember (emu_height g). clear Heqn. elim : n g H. done. 
intros. simpl. apply/uniq_unf2. apply/H. rewrite iterSr in H0.  done. 
Qed.


Inductive Uniq_gen (P : lType -> Prop) :  lType  -> Prop :=
 | U1 c d u e' :  P e' -> Uniq_gen P (EMsg c d u e')
 | U2 c d es :  (forall e, e \in es -> P e.2) -> (uniq (map fst es)) ->  Uniq_gen P (EBranch c d es)
 | U3 : Uniq_gen P  EEnd
 | U4 n : Uniq_gen P (EVar n)
 | U5 e : Uniq_gen P e [e ERec e .: EVar]  -> Uniq_gen P (ERec e).

Lemma Uniq_gen_mon : monotone1 Uniq_gen. 
Proof. move => x0. intros. induction IN;try done. con;eauto. 
con;eauto. con. con. con. eauto. 
Qed .

Hint Resolve Uniq_gen_mon : paco. 

Notation Uniq e := (paco1 Uniq_gen bot1 e).


Inductive Uniq2_gen (P : lType -> Prop) :  lType  -> Prop :=
 | U12 c d u e' :  P e' -> Uniq2_gen P (EMsg c d u e')
 | U22 c d es :  (forall e, e \in es -> P e.2) -> (uniq (map fst es)) ->  Uniq2_gen P (EBranch c d es)
 | U32 : Uniq2_gen P  EEnd
 | U42 n : Uniq2_gen P (EVar n).

Notation Uniq2 e := (paco1 (ApplyF1 full_eunf \o Uniq2_gen) bot1 e).


Lemma Uniq2_gen_mon : monotone1 Uniq2_gen. 
Proof. move => x0. intros. induction IN;try done. con;eauto. 
con;eauto. con. con. 
Qed.

Hint Resolve Uniq2_gen_mon : paco. 


Lemma Uniq_unf2 : forall e r, paco1 Uniq_gen r (eunf e) -> paco1 Uniq_gen r e.  
Proof. 
intros. destruct e;try done. ssa'. pfold. con. pfold_reverse. 
Qed. 

Lemma Uniq_full_unf2 : forall e r, paco1 Uniq_gen r  (full_eunf e) -> paco1 Uniq_gen r  e. 
Proof. 
intros. rewrite /full_eunf in H. remember (emu_height e).  clear Heqn. 
elim : n e H. ssa'. ssa'. apply/H. apply/Uniq_unf2.  eauto. 
Qed. 

(*maybe lcontractive assumption not necessa'ry*)
Lemma UniqP1 : forall e, lcontractive e  -> uniq_labels e -> Uniq e. 
Proof. 
pcofix CIH.
move => e. remember (emu_height e). elim : n e Heqn. 
case;intros.  ssa'. pfold. con. pfold. con. ssa'. 
pfold. con. eauto. 
ssa'. pfold. con. intros. right. apply/CIH.  apply (allP H0). done. apply (allP H2). done. done.
ssa'. 
intros. 
destruct e;ssa'.  pfold. con. pfold_reverse. apply/H. 
rewrite -emu_height_unf. inv Heqn.  done. 
apply/lcontractive_subst.  done.  case. ssa'. done. 
apply/uniq_labels_subst. case. ssa'. ssa'.  done. 
Qed. 

Lemma Uniq_subst : forall e e' sigma, Uniq e' -> e' = e [e sigma] -> Uniq e. 
Proof. 
pcofix CIH. intros. punfold H0. elim : H0 e sigma H1;intros;pc. 
destruct e;try done. ssa'. pfold. con. 
ssa'. pfold. con. right. inv H1. apply/CIH. eauto. eauto. 
destruct e;try done. pfold. con. 
ssa'. inv H1. pfold. con. intros. right.
edestruct H.  apply/mapP.  exists e. ssa'. eauto.
apply/CIH. eauto. rewrite /prod_map. instantiate (1 := sigma). destruct e. ssa'. 
done. 
rewrite -map_comp fst_c in H0. done. 
destruct e;try done. pfold. con. pfold. con. 
destruct e;try done. pfold. con. 
destruct e0;try done. pfold. con. 
pfold. con. pfold_reverse. ssa'.  inv H1. apply/H0. 
instantiate (1 := sigma). asimpl. done. 
Qed. 

Lemma UniqP2 : forall e, Uniq e ->  uniq_labels e. 
Proof .
elim;ssa'.  apply/H. punfold H0. inv H0. punfold_reverse H2. 
intros. apply/Uniq_subst.   eauto. eauto. apply/H. 
punfold H0. inv H0. pc. done. 
punfold H0. inv H0. 
apply/allP=> x xIn.  apply/H. instantiate (1 := x.1). destruct x. ssa'. 
punfold H0. inv H0. edestruct H3. eauto. done. done. 
Qed. 

Lemma Uniq12 : forall e, Uniq e -> Uniq2 e. 
Proof.
pcofix CIH.  intros. punfold H0. elim : H0; ssa'; pc. 
pfold. con. con. eauto. 
pfold. con. con. intros. right. apply/CIH. edestruct H. 
eauto. done. done. done. pfold. con. con. pfold. con. con. 
pfold. con. rewrite full_eunf_subst. punfold H0. inv H0. 
Qed. 

Lemma Uniq21 : forall e, Uniq2 e -> Uniq e. 
Proof.
pcofix CIH.  intros. punfold H0. 
inv H0. apply Uniq_full_unf2. inv H;pc. 
pfold. con.  eauto. 
pfold. con.  intros. move/H2 : H4. case=>//=. eauto. done. 
pfold. con.  pfold. con. 
Qed. 

Lemma labels_preserve_aux : forall e e', EQ2 e e' -> Uniq2 e -> Uniq2 e'.  
Proof.
pcofix CIH.  intros. punfold H0. punfold H1. inv H0. inv H1. 
pfold. con. inv H. con. con. destruct H5;try done. right.   apply/CIH. eauto. rewrite -H3 in H2. inv H2. pc. done. 
con. intros. right.
move/inP : H7. intro. eapply (@In_zip2 _ _ _ es0 es1)  in H7. destruct H7. ssa'.
move/ForallP : H6.   move/(_ _ H8). ssa'. destruct H9;try done.    apply/CIH. eauto. 
rewrite -H3 in H2. inv H2. edestruct H12. apply/inP. eauto. 
done.  done.  done. 
have : map fst es0 = map fst es1. 
clear H4 H3.
elim : es0 es1 H5 H6. case. ssa'. ssa'. move => a l IH. case. ssa'. 
ssa'. inv H6. 
ssa'. rewrite H3.  f_equal. apply/IH. inv H5. done. 
move=><-. rewrite -H3 in H2. inv H2. 
Qed. 


Lemma labels_preserve : forall e e', EQ2 e e' -> uniq_labels e -> uniq_labels e'.  
Proof. intros. apply/UniqP2. apply/Uniq21. apply/labels_preserve_aux. eauto. 
apply/Uniq12. apply/UniqP1. apply/lInvPred_contractive.
apply/EQ2_tree. eauto. done. 
Qed. 

Lemma harmony_sound  : forall g l g' f,  step g l g' -> action_pred g -> size_pred g -> Linear g ->  uniqg_labels g ->  one_shot g f -> exists f', one_shot g' f' /\ EnvStep f l f'. 
Proof. intros.
remember H4. clear Heqo. move : o. rewrite /one_shot. 
move/(_ (ptcp_from l.1)). move/proj_complete_wrt_Project. case=> x [] Heq. rewrite /proj. case_if;try done. case. intros. 
subst. remember H. clear Heqs. eapply preserve_proj in s. 2 : { 
instantiate (2 := ptcp_from l.1). rewrite /comp_dir /ptcp_from eqxx. eauto. } 
eapply EstepEQ2 in s. 2 : { apply/EQ2_sym.  eauto. } 

remember H4. clear Heqo. move : o. rewrite /one_shot. 
move/(_ (ptcp_to l.1)). move/proj_complete_wrt_Project. case=> x [] Heq'. rewrite /proj. case_if;try done. case. intros. 
subst. remember H. clear Heqs0. eapply preserve_proj in s0. 2 : { 
instantiate (2 := ptcp_to  l.1). eapply label_pred in H0. 2 : eauto. rewrite /comp_dir eq_sym. rewrite (negbTE H0) eqxx //= . 
done. } 
eapply EstepEQ2 in s0. 2 : { apply/EQ2_sym.  eauto. } destruct s,s0. 
econstructor. split. 2 : { con. eauto. eauto. } 
intros.
rewrite /update_action /update. case_if. 
move/eqP : H9. intros. subst. apply/Project_EQ2. apply/preserve_proj5. eauto. done. done. 
remember H4. clear Heqo. apply/project_projT.  move : o. rewrite /one_shot. move/(_ (ptcp_to l.1)). eauto.
apply/Estep_EQ2. 5 :{  eauto. } apply/EQ2_sym. eauto. apply/uniq_trans=>//=. 
apply/labels_preserve. apply/EQ2_sym.  eauto. apply/uniq_trans=>//=. 

apply/preserve_proj;eauto. 
eapply label_pred in H0. 2 : eauto. rewrite /comp_dir. rewrite eq_sym (negbTE H0) eqxx //=. done.
case_if.  

move/eqP : H9. intros. subst. apply/Project_EQ2. apply/preserve_proj5. eauto. done. done. 
remember H4. clear Heqo. apply/project_projT.  move : o. rewrite /one_shot. move/(_ (ptcp_from l.1)). eauto. 
apply/Estep_EQ2. 5 :{ apply/H7.   } apply/EQ2_sym. eauto. 
apply/uniq_trans.  eauto. apply/labels_preserve. apply/EQ2_sym. eauto. apply/uniq_trans. eauto. 
rewrite (eqP H10).
apply/preserve_proj;eauto. 
eapply label_pred in H0. 2 : eauto. rewrite /comp_dir eqxx //=. done. remember H4.  clear Heqo. 
move : o. move/(_ p). move => HH.
apply proj_complete_wrt_Project in HH. destruct HH. ssa'. move : H12. rewrite /proj. case_if;try done. case. intros. subst. 
apply/Project_EQ2. 2 : { apply/EQ2_sym. eauto. } apply/Project_EQ2. apply/project_projT. 
apply/preserve_proj5;eauto. apply/project_projT. 
move : H4. move/(_ p). eauto. apply/EQ2_sym. apply/preserve_proj2;eauto. 
apply/gInvPred_iff. apply/Project_gtree. apply/H4. rewrite /comp_dir H9 H10 //=. done. done. done. done. 
Unshelve. repeat  con. 
Qed.


(*Add action pred condition in later proof *)


(*The same participant cannot both reduce as a sender and receiver*)
Lemma can_stepP' : forall g p0 p1 c vn, can_step (Sd,c,vn) (trans p0 g)  -> can_step (Rd,c,vn) (trans p1 g) -> action_pred g /\ size_pred g -> p0 <> p1.
Proof. 
elim;intros. ssa'. ssa'. ssa'. 
move : H0. case_if;try done.  move : H1. case_if;try done. eauto. 
- ssa'. move => HH. subst. destruct (comp_dir  p1 a) eqn:Heqn. 
 * move : H0. simpl. move/orP. case. 
  ** move/eqP. case. intros. subst. subst_comp. move : H1. simpl. rewrite eqxx //=. 
  ** ssa'. move/eqP : H6;intros;subst. subst_comp. ssa'. apply/H;eauto. ssa'. 
 * apply/H;eauto. 
- ssa'. move => HH. subst. destruct (comp_dir  p1 a) eqn:Heqn. 
 * move : H0. simpl. move/orP. case. 
  ** destruct vn;try done.  ssa'. move/eqP : H0.  case. intros. subst. subst_comp. move : H1. simpl. rewrite eqxx //=. 
  ** ssa'. move/eqP : H7;intros;subst. subst_comp. ssa'. 
     move : H1. destruct vn. simpl. ssa'. destruct l;try done.  destruct p. ssa'. apply/H. rewrite inE. apply/orP.  eauto. eauto. eauto. ssa'. ssa'. 
     ssa'. 

     destruct l;try done. destruct p. ssa'. apply/H. simpl. ssa'. apply/orP. left. eauto. eauto. eauto. ssa'. ssa'.
     destruct l;try done.   ssa'. destruct p. ssa'. apply/H. rewrite inE. apply/orP. eauto. eauto. eauto. ssa'. done.
Qed. 

Lemma Tr_subst : forall g s sigma, Tr s g -> Tr s g [g sigma ] .
Proof. move => g s sigma H.  elim : H sigma;intros. done.
simpl.  con. done. simpl.  econstructor. 2 : {  apply/H1. apply sigma.  } 
instantiate (1 := n).  have : (n, g0 [g sigma]) = prod_map ssrfun.id (subst_gType sigma) (n,g0) . done.
move=>->. apply/map_f.  done. 
con. 
move : H0. move/(_ sigma).  asimpl. done. 
Qed. 


Lemma Linear_subst : forall g sigma, Linear g [g sigma] -> Linear g. 
Proof. 
move => g sigma.  rewrite /Linear. intros. apply/H. apply/Tr_subst. eauto. done.
Qed. 

(*Seems like their is some circular dependencies in showing this lemma using linearity, 
 the case where comp_dir p a = Some d and comp_dir p' = None is contradictory because both
 p and p' reduce using same channel. Assuming we can show can_step (Sd,c,vn) (trans p g) -> can_gstep (p->p' : c,vn) 
 then we can the action ordering (p -> _ : k) < (_ -> p' : k), concretely  Tr a.g (p -> _ :k)..s..(_ -> p' :k) 
 where p' does not occur in any receiver of (p -> _ :k)..s.. This fact along with linearty means there can be no input dependency,
  since such dependency must end in an II and the prefix of the trace does not contain p'. 

  The problem is that I think we need linearity to show that p' is not in the receivers of the prefix.
  Without it you are stuck in the induction case of msg, by IH : can_gstep (p-> p' : c,vn) g, but to get 
  can_step (p->p' : c,vn) a.g we need ptcp_to a \notin [p,p']. Don't know how to show a <> p'.
  It seems like a property of linearity, the p' that matches the p we used in the IH, must by linearity
  be distinct from any receiver in the prefix a, since a.g is linear. And now we are back the square one,
  to use linearity we need this lemma.
*)

(*Show this lemma in two variants instead of generalizing, because it simplifies the existence of an action to
   existence of a participants*)

Lemma estep_tr1 : forall g p c vn, can_step (Sd,c,vn) (trans p g) -> action_pred g /\ size_pred g -> exists s p', Tr (s++[::(Action p p' c)]) g /\ (forall a, a \in s -> ptcp_to a <> p).
Proof. 
elim;intros. ssa'. ssa'. ssa'. 
- move :H0. case_if;try done. intros. eapply H in H3. destruct H3,H3. ssa'. exists x. exists x0. ssa'. con. 
  apply/Tr_subst. eauto. ssa'. 
- ssa'. destruct (comp_dir p a) eqn:Heqn.
 * ssa'. destruct (orP H0).
  ** move/eqP : H1. case. intros. subst. subst_comp. exists nil. exists (ptcp_to a). simpl. ssa'.    
     rewrite pack_act. con.  done. 
  ** ssa'. move/eqP :H1. intros. subst. subst_comp. apply H in H6;eauto. destruct H6,H1. ssa'. 
     exists (a::x),x0. ssa'. intros. rewrite inE in H6. destruct (orP H6). move/eqP : H8. intros. subst. apply/eqP.
     rewrite neg_sym. done. apply/H5. done. 
 * apply H in H0. destruct H0,H0. ssa'. exists (a::x),x0. simpl. ssa'. intros. rewrite inE in H5. destruct (orP H5).
   rewrite (eqP H6). move : Heqn. rewrite /comp_dir. case_if;try done. case_if;try done. intros. 
   apply/eqP. rewrite neg_sym H8.  done. eauto. ssa'. 
- ssa'. destruct (comp_dir p a) eqn:Heqn.
 * ssa'. destruct (orP H0).
  ** destruct vn;try done. ssa'. move/eqP : H6. case. intros. subst. subst_comp. exists nil. exists (ptcp_to a). simpl. ssa'.    
     rewrite pack_act. destruct l;try done.  destruct p. ssa'. econstructor.  eauto. done. 
  ** ssa'. clear H0. move/eqP :H1. intros. subst. subst_comp. destruct l;try done. ssa'. destruct p. ssa'. eapply H in H0;eauto. 
     destruct H0,H0. ssa'.
     exists (a::x),x0. ssa'. econstructor. rewrite inE. apply/orP. eauto. done. simpl. intros. rewrite inE in H10. destruct (orP H10). 
     rewrite (eqP H11). apply/eqP. rewrite neg_sym //=. auto.
 * rewrite -nth0 in H0. erewrite nth_map in H0;eauto. destruct l.  done. destruct p0. ssa'. eapply H in H0. destruct H0,H0. ssa'. 
   exists (a::x),x0. simpl.  
ssa'. econstructor. rewrite inE. apply/orP. eauto. eauto. intros. rewrite inE in H8. destruct (orP H8). 
   move/eqP : H9. intros. subst. rewrite /comp_dir in Heqn. move : Heqn. case_if. done.  case_if;try done. move => _. 
   intro.  subst.  rewrite eqxx in H10. done. eauto. eauto. ssa'.
Unshelve. all : repeat con. 
Qed. 

Lemma estep_tr2 : forall g p c vn, can_step (Rd,c,vn) (trans p g) -> action_pred g /\ size_pred g -> exists s p', Tr (s++[::(Action p' p c)]) g /\ (forall a, a \in s -> ptcp_to a <> p).
Proof. 
elim;intros. ssa'. ssa'. ssa'. 
- move :H0. case_if;try done. intros. eapply H in H3. destruct H3,H3. ssa'. exists x. exists x0. ssa'. con. 
  apply/Tr_subst. eauto. ssa'. 
- ssa'. destruct (comp_dir p a) eqn:Heqn.
 * ssa'. destruct (orP H0).
  ** move/eqP : H1. case. intros. subst. subst_comp. exists nil. exists (ptcp_from a). simpl. ssa'.    
     rewrite pack_act. con.  done. 
  ** ssa'. move/eqP :H1. intros. subst. subst_comp. apply H in H6;eauto. destruct H6,H1. ssa'. 
     exists (a::x),x0. ssa'. intros. rewrite inE in H8. destruct (orP H8). move/eqP : H9. intros. subst. apply/eqP.
     rewrite neg_sym. done. auto. 
 * apply H in H0. destruct H0,H0. ssa'. exists (a::x),x0. simpl. ssa'. intros. rewrite inE in H5. destruct (orP H5).
   rewrite (eqP H6). move : Heqn. rewrite /comp_dir. case_if;try done. case_if;try done. intros. 
   apply/eqP. rewrite neg_sym H8.  done. eauto. ssa'. 
- ssa'. destruct (comp_dir p a) eqn:Heqn.
 * ssa'. destruct (orP H0).
  ** destruct vn;try done. ssa'. move/eqP : H6. case. intros. subst. subst_comp. exists nil. exists (ptcp_from a). simpl. ssa'.    
     rewrite pack_act. destruct l. done. destruct p. ssa'. econstructor.  eauto. done. 
  ** ssa'. clear H0. move/eqP :H1. intros. subst. subst_comp. destruct l;try done. ssa'. destruct p. ssa'. eapply H in H0;eauto. 
     destruct H0,H0. ssa'.
     exists (a::x),x0. ssa'. econstructor. eauto. done. simpl. intros. rewrite inE in H10. destruct (orP H10). 
     rewrite (eqP H11). apply/eqP. rewrite neg_sym //=. auto.
 * destruct l;try done. destruct p0. ssa'. eapply H in H0; last eauto.  destruct H0,H0. ssa'. 
   exists (a::x),x0. simpl. ssa'. econstructor. eauto. done. intros.
   rewrite inE in H8. destruct (orP H8).
   rewrite (eqP H9). move : Heqn. rewrite /comp_dir. case_if;try done. case_if;try done. intros. 
   apply/eqP. rewrite neg_sym H11.  done. eauto. eauto. 
Qed. 



Lemma exists_dep_in : forall a s p0 p1 c, exists_dep InDep a s (Action p0 p1 c) -> exists a', a' \in a::s /\ ptcp_to a' = p1. 
Proof. 
intros. rewrite /exists_dep in H. destruct H. ssa'. clear H. 
apply InDep_iff in H0. 
suff : exists a', a' \in a::(mask x s) /\ ptcp_to a' = p1. 
case. ssa'. rewrite inE in H. destruct (orP H). exists a. rewrite -(eqP H3) inE H2 eqxx. ssa'.
apply mem_mask in H3. exists x0. rewrite inE H3. ssa'. lia.
rewrite -cat_cons in H0. 
remember (a::(mask x s)). clear Heql. 
rewrite /indep in H0.
 destruct l;try done. simpl in H0. destruct l;try done. ssa'.  
rewrite /II in H0. exists a0. rewrite inE //=.  ssa'.  apply/eqP. done. 
ssa'. rewrite /II in H2. rewrite belast_cat in H2. rewrite cats1 in H2. rewrite last_rcons in H2.   ssa'. 
rewrite cats1 last_rcons in H2. exists (last a1 l).  ssa'. apply/orP. right. 
clear H. elim : l a1 p1 H2. ssa'. rewrite eqxx //=. ssa'. apply H in H2. destruct (orP H2).
apply/orP. right. rewrite inE H0 //=. rewrite inE H0. lia. apply/eqP. done. 
Qed. 

Lemma exists_dep_out : forall a s p0 p1 c, exists_dep OutDep a s (Action p0 p1 c) -> ptcp_from a != p0 ->  (exists a', a' \in a::s /\ ptcp_to a' = p0).
Proof. 
intros. rewrite /exists_dep in H. destruct H. ssa'. clear H. 
apply OutDep_iff in H1. 
suff : (exists a', a' \in a::(mask x s) /\ ptcp_to a' = p0).
case. ssa'. rewrite inE in H. destruct (orP H). exists a. rewrite -(eqP H4) inE H3 eqxx. ssa'.
apply mem_mask in H4. exists x0. rewrite inE H3. ssa'. lia. intros. 
rewrite -cat_cons in H1. 
remember (a::(mask x s)). destruct l. done. inv Heql. clear Heql. 
rewrite /outdep in H1. ssa'. remember (mask x s). clear Heql. 
 destruct l;try done. simpl in H1. ssa'. 
rewrite /IO_OO in H. destruct (orP H). rewrite /IO in H1. ssa'. exists a. ssa'. apply/eqP. done. 
rewrite /OO in H1. ssa'. lia. ssa'. 
rewrite /IO_OO in H. destruct (orP H). 
rewrite /IO in H1. clear H H0. 
elim : l a a0 H1 H3.  
ssa'. destruct (orP H). rewrite /IO in H3. ssa'. exists a0. rewrite !inE eqxx. ssa'. lia.  apply/eqP. done. 
rewrite /OO in H3. ssa'. exists a. rewrite inE eqxx //=. ssa'.  rewrite (eqP H1). apply/eqP.   done. 
ssa'. destruct (orP H0). rewrite /IO in H3.  eapply H in H4;eauto. destruct H4. ssa'. 
exists x0. rewrite inE H4 //=. ssa'. lia. 
rewrite /OO in H3. ssa'.  rewrite (eqP H5) in H1. 
eapply H in H4;eauto. destruct H4. ssa'. exists x0. 
rewrite inE in H3. destruct (orP H3). rewrite inE (eqP H7) eqxx //=. ssa'. subst.  
rewrite (eqP H7). done. rewrite inE in H7. destruct (orP H7). rewrite (eqP H8). rewrite !inE eqxx. 
ssa'. apply/orP. right. rewrite orbC. done. 
rewrite -(eqP H8) //=. rewrite !inE H8. ssa'. apply/orP. right. apply/orP.  right. rewrite orbC. done. 
clear H. rewrite /OO in H1. ssa'. rewrite (eqP H) in H0. clear H4 H. 
suff : exists a' : action, a' \in [:: a0 & l] /\ ptcp_to a' = p0.
case. ssa'. exists x0. rewrite inE H. ssa'. rewrite orbC //=.
elim : l a0 p0 p1 c H3 H0. ssa'. exists a0. destruct (orP H). rewrite /IO in H3. ssa'. apply/eqP. done.  
rewrite /OO in H3. ssa'. lia. 
ssa'.
destruct (orP H1). rewrite /IO in H3. 
destruct (eqVneq (ptcp_from a0) p0). subst. exists a1. rewrite inE eqxx //=. ssa'. apply/eqP.  done .
apply H in H4. destruct H4. ssa'. exists x0. rewrite inE H4 //=. ssa'. rewrite orbC. done. done. 
rewrite /OO in H3. ssa'. apply H in H4. 2 : {  rewrite -(eqP H5). done. } destruct H4. 
ssa'. exists x0. rewrite inE H3. ssa'. rewrite orbC //=.
Qed. 


Lemma step_unf : forall g l g', step g l g' -> step (unf g) l g'. 
Proof. case;try done. intros. inv H. 
Qed. 
Lemma step_full_unf : forall g l g', step g l g' -> step (full_unf g) l g'. 
Proof. intros. rewrite /full_unf. remember (mu_height g). clear Heqn. elim : n g l g' H;try done. 
ssa'. apply/step_unf. eauto. 
Qed. 

Lemma step_unf2 : forall g l g', step (unf g) l g' -> step g l g'. 
Proof. case;try done. intros. con. done. 
Qed. 
Lemma step_full_unf2 : forall g l g', step (full_unf g) l g' -> step g l g'. 
Proof. intros. rewrite /full_unf in H. remember (mu_height g). clear Heqn. elim : n g l g' H;try done. 
ssa'. apply/step_unf2. apply/H.  rewrite -iterSr iterS. done. 
Qed. 

Lemma can_stepP : forall g p0 p1 c vn, can_gstep2 (Sd,c,vn) p0 g  -> can_gstep2 (Rd,c,vn) p1 g -> action_pred g /\ size_pred g /\ Linear g -> can_gstep (Action p0 p1 c,vn) g.
Proof. 
elim;intros. ssa'. ssa'. 
ssa'. apply/H;eauto. ssa'.   apply linear_unf in H4. apply/Linear_subst.  eauto. 

have : p0 <> p1. apply/can_stepP'. apply can_gstep2P. eauto. ssa'. apply can_gstep2P. eauto. ssa'. ssa'. 
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
- ssa'. apply/orP. right. rewrite negb_or. ssa'. apply/H. done. done. ssa'. apply/linear_sgmsg. eauto.



have : p0 <> p1. apply/can_stepP'. apply can_gstep2P. eauto. ssa'. apply can_gstep2P. eauto. ssa'. ssa'. 
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
 rewrite inE in H14. destruct (orP H14). move/eqP : H17. intros. subst. rewrite eqxx //=.  
  destruct vn . ssa'. apply/orP. left. rewrite pack_act. ssa'. 

  apply H13 in H16. done. subst. done. rewrite /same_ch. simpl. done. done. ssa'. destruct l. ssa'. ssa'. destruct l. ssa'. ssa'. destruct l. ssa'. ssa'. 
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
  rewrite inE in xIn.  destruct (orP xIn). rewrite (eqP H5).  ssa'. apply/H. eauto. done. done. ssa'. 
  eapply linear_branch_aux in H3. move/ForallP : H3. intros. 
  have : g = (n,g).2. done. move=>->. apply/H3. simpl.   auto. 
  apply/H. instantiate (1:= x'.1). rewrite inE. apply/orP. right. destruct x'.   eauto. 


  apply (allP H14). done. apply (allP H15). done. ssa'. apply (allP H17). done. apply (allP H16). done.
  apply/linear_branch. eauto.  done. 
Qed. 

 

Lemma harmony_complete_aux  : forall g l f f',  action_pred g -> size_pred g -> Linear g ->  one_shot g f ->  EnvStep f l f' -> 
                    exists g', step g l g'. 
Proof. 
intros. inv H3. 
have : EQ2 (f (ptcp_from l.1)) (trans (ptcp_from l.1) g).
move : (H2 (ptcp_from l.1)). intros. apply/proj_proj. done. 
intros. 
have : EQ2 (f (ptcp_to l.1)) (trans (ptcp_to l.1) g).
move : (H2 (ptcp_to l.1)). intros. apply/proj_proj. done. 
intros. 
eapply EstepEQ2 in H4;eauto. 
eapply EstepEQ2 in H5;eauto. destruct H4,H5. 
apply can_step_complete in H4,H5.
apply/can_gstep_sound. destruct l. destruct a. apply/can_stepP; ssa'.
apply can_step_sound in H4,H5. destruct H4,H5.
apply/project_can_step; eauto. apply/Project_EQ2. 2: { apply/proj_proj. rewrite /one_shot in H2. auto. }
apply H2.
apply can_step_sound in H4,H5. destruct H4,H5.
apply/project_can_step; eauto. apply/Project_EQ2. 2: { apply/proj_proj. rewrite /one_shot in H2. auto. }
apply H2.
Qed. 

Lemma EnvUniq : forall f0 l f1 f1', (forall p, uniq_labels (f0 p)) ->  EnvStep f0 l f1 -> EnvStep f0 l f1' -> f1 = f1'.
Proof. 
intros. fext. inv H0. inv H1. clear H0 H1. 
rewrite /update_action /update. intros. case_if. apply/uniq_estep;eauto. 
case_if. apply/uniq_estep;eauto. done. 
Qed. 


(*Following zooid, we collect the local projections by one_shot predicate*)
(*Follwing zooid, show step and derive one_shot by soundness*)
Lemma harmony_complete  : forall g l f f',  action_pred g -> size_pred g -> Linear g -> uniqg_labels g -> 
                                       one_shot g f ->  EnvStep f l f' ->  
                                       exists g', step g l g' /\ one_shot g' f'.
Proof. 
intros. have :   exists g' : gType, step g l g'. apply/harmony_complete_aux;eauto.  
case. intros. exists x. ssa'. eapply harmony_sound in p;eauto. destruct p. ssa'. eapply EnvUniq in H4;eauto. subst. done. 
intros. move: (H3 p). move/proj_complete_wrt_Project. case. intros. ssa'. 
move : H8. rewrite /proj. case_if;try done. case.  intros. 
apply/labels_preserve. apply/EQ2_sym. eauto. subst. apply/uniq_trans. eauto.
Qed. 

