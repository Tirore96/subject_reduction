From mathcomp Require Import all_ssreflect zify.

Require Export MPSTSR.IndTypes.elimination.
Require Import Paco.paco.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Definition eunf g := if g is ERec g' then g' [e g.:EVar]  else g.



Lemma emu_height_ren : forall g sigma, emu_height g ⟨e sigma ⟩  = emu_height g.
Proof.
elim;rewrite /=;try done;intros.
f_equal. apply : H. 
Qed.

Lemma emu_height_subst : forall g0 sigma, (forall n, ~~ eguarded n g0 -> emu_height (sigma n) = 0) ->  emu_height (g0[e sigma]) = emu_height g0.
Proof. 
elim; try solve [by rewrite /=];intros.
asimpl. move : (H n). destruct (emu_height (sigma n)) eqn:Heqn. done. have : 0 < n0.+1 by lia. move => + HH. simpl. 
simpl in HH. lia. 
simpl. f_equal. asimpl. apply H. case. done.  simpl. intros. asimpl. rewrite emu_height_ren. apply/H0. done. 
Qed.


Lemma emu_height_unf : forall g , eguarded 0 g -> (emu_height g) = emu_height (g [e ERec g .: EVar]).
Proof.
move => g. rewrite /=. case : g; try solve [intros;rewrite /=;done].
intros. rewrite /=. destruct n. done. done. ssa. erewrite emu_height_subst. done. case. done. 
intros. simpl. asimpl. destruct n. lia.  simpl. done. 
Qed.

Lemma emu_height_unf2 : forall g sigma i, ~~ eguarded i g -> (emu_height g) + emu_height (sigma i) = emu_height (g [e sigma]).
Proof. 
elim;rewrite //=;intros. have : n = i by lia.  intros. subst. lia. 
asimpl. erewrite <- H. 2 : { eauto. } simpl. asimpl. rewrite emu_height_ren. lia. 
Qed.


Lemma eguarded_test : forall e sigma i,  ~~ eguarded i e -> iter (emu_height e) eunf e [e sigma ] = sigma i. 
Proof. 
elim;rewrite //=;intros. 
have : n = i. lia.  move=>->. done.  asimpl. rewrite -iterS iterSr. simpl. asimpl. erewrite H. 
2 : { eauto. } simpl. done. 
Qed.


Definition full_eunf g := (iter (emu_height g) eunf g).

(*Even non contractive terms have the property that full unfolding equals full unfolding plus 1. This is what we need in projection lemma
 so we don't have to derive contractiveness of e from projection derivation*)
Lemma full_eunf_subst : forall e, full_eunf (ERec e) = full_eunf (e [e ERec e .: EVar]). 
Proof. 
intros. rewrite /full_eunf. 
intros. simpl.  rewrite -iterS iterSr. simpl. 
destruct (eguarded 0 e) eqn:Heqn.  rewrite emu_height_unf. done. done. 
 erewrite eguarded_test.  2 : { lia. } 
simpl. 
erewrite <-emu_height_unf2. 2 : { lia.  } simpl. 
rewrite addnC.  
rewrite iterD. erewrite eguarded_test. 2 : { lia.  } simpl. rewrite -iterS iterSr /=. 
erewrite eguarded_test. 2 : { lia. } done. 
Qed.




Lemma full_eunf2 : forall n e, full_eunf (iter n eunf e) = full_eunf e. 
Proof. 
elim. done. 
intros. rewrite iterS. 
destruct (if (iter n eunf e) is ERec _ then true else false) eqn:Heqn. 
destruct ((iter n eunf e))eqn:Heqn2;try done. simpl. 
rewrite -(H e) Heqn2. rewrite full_eunf_subst. done. 
have : eunf (iter n eunf e) = iter n eunf e. destruct ((iter n eunf e));try done. 
move=>->. rewrite H. done. 
Qed.


Lemma full_eunf_idemp : idemp full_eunf. 
Proof. 
intros. rewrite /idemp. intros. rewrite {2}/full_eunf. rewrite full_eunf2. done. 
Qed.


Lemma unf_eguarded  : forall g n, eguarded n g  -> eunf g <> EVar n.  
Proof. 
case=>//=. intros. move => HH. inv HH. lia. 
intros. destruct l;try done.   move : H. 
asimpl. destruct n0. done. asimpl. case. simpl. intros. move=> HH.  inv HH. lia. 
Qed.


Lemma eguarded_ren : forall g n sigma, injective sigma ->  eguarded n g -> eguarded (sigma n) (g ⟨e sigma ⟩).
Proof. 
elim=>//=;intros. apply/eqP. move => HH.  apply H in HH. lia. 
move : H1. asimpl. intros.
have : injective (0 .: sigma >> succn). eauto.  
move/H. move/(_ n.+1).  asimpl. eauto. 
Qed. 

Lemma eguarded_ren2 : forall g n sigma, eguarded (sigma n) (g ⟨e sigma ⟩) -> eguarded n g.
Proof. 
elim=>//=;intros. apply/eqP. move => HH.  apply/negP. apply/H. apply/eqP. f_equal. done. 
apply/H.
instantiate (1 := (0 .: sigma >> succn)). asimpl. done. 
Qed. 

Lemma eguarded_ren_iff : forall g n sigma, injective sigma ->  eguarded n g <-> eguarded (sigma n) (g ⟨e sigma ⟩).
Proof. intros. split;intros. apply/eguarded_ren;eauto. apply/eguarded_ren2. eauto. 
Qed. 

Lemma eguarded_subst : forall g n sigma , (forall n0, eguarded n0 g = false  -> eguarded n (sigma n0)) -> eguarded n (g [e sigma]). 
Proof. 
elim=>//=;intros. apply/H. lia. 
move : H0.  asimpl. intros. 

apply/H.  ssa. 
destruct n0;try done. asimpl. apply/eguarded_ren. done. eauto. 
Qed. 


Lemma eguarded_subst2 : forall g n n0 sigma ,  eguarded n (g [e sigma]) ->  eguarded n (sigma n0) = false -> eguarded n0 g. 
Proof. 
elim=>//=;intros. destruct (eqVneq n n1);try done. subst. rewrite H0 in H. done. 
move/H : H0. asimpl. move/(_ n0.+1). asimpl.
move => HH. apply HH. apply/negP=> HH2. apply/negP. move : H1. move/negP/negP. eauto. 
apply eguarded_ren2 in HH2. eauto. 
Qed. 

Lemma eguarded_eunf  : forall g n, eguarded n g -> eguarded n (eunf g).
Proof. 
case=>//=;intros.
apply/eguarded_subst. 
ssa. destruct n0;try done. simpl. destruct (eqVneq n0 n). subst. lia. done. 
Qed.

Lemma eguarded_eunf2  : forall g n, eguarded n (eunf g) -> eguarded n g.
Proof. 
case=>//=;intros.
eapply eguarded_subst2 in H. eauto. asimpl. simpl. lia. 
Qed.


Lemma eguarded_iter_unf : forall n0 g n,  eguarded n g -> eguarded n (iter n0 eunf g).
Proof. 
elim. case => //=. 
intros. simpl. apply/eguarded_eunf. eauto. 
Qed.

Lemma eguarded_iter_unf2 : forall n0 g n,  eguarded n (iter n0 eunf g) -> eguarded n g.
Proof. 
elim. case => //=. 
intros. simpl. rewrite iterSr in H0.  apply/eguarded_eunf2. eauto. 
Qed.


Lemma eguarded_full_unf : forall e n, eguarded n e -> eguarded n (full_eunf e). 
Proof. 
intros. rewrite /full_eunf. remember (emu_height e). clear Heqn0.  apply/eguarded_iter_unf. done. 
Qed.

Lemma eguarded_full_unf2 : forall e n, eguarded n (full_eunf e) -> eguarded n e. 
Proof. 
intros. rewrite /full_eunf. remember (emu_height e). clear Heqn0.  apply/eguarded_iter_unf2. eauto. 
Qed.


Lemma iter_unf_eguarded  : forall n0 n g, eguarded n g ->  iter n0 eunf g <> EVar n.
Proof. 
elim;intros.
simpl in H. subst. simpl. destruct g;try done. simpl in H. move=> HH. inv HH. lia.
rewrite iterSr.  apply H. apply/eguarded_eunf. done. 
Qed.

Lemma eguarded_notn : forall e n, eguarded n e -> full_eunf e <> EVar n.
Proof. 
intros. apply eguarded_full_unf in H. destruct (full_eunf e);try done. simpl in H. move => HH. inv HH. lia. 
Qed. 


Lemma eguarded_uniq : forall g n0 n1, eguarded n0 g = false -> eguarded n1 g = false -> n0 = n1.
Proof. 
elim=>//=. 
intros. lia. 
intros. suff : n0.+1 = n1.+1.  lia. apply/H=>//=. 
Qed.

Lemma eguarded_unfv : forall g n, eguarded n g = false -> full_eunf g = EVar n. 
Proof. 
intros. rewrite /full_eunf. remember (emu_height g). 
move : n0 g Heqn0 H.  
elim=>//=. case=>//=. intros. f_equal=>//=. lia. 
intros. 
destruct g;try done. simpl in Heqn0.
rewrite -iterS iterSr /=. rewrite H. done. 
rewrite emu_height_subst. inv Heqn0=>//=. 
case. simpl. intros. simpl in H0. have : n.+1 = 0. apply/eguarded_uniq. lia. lia. 
done. done. 
simpl in *. apply/negP=> HH. apply/negP. move/negP/negP : H0. eauto. 
eapply eguarded_subst2 in HH. eauto. asimpl. simpl. lia. 
Qed.


Definition is_evar e := if e is EVar _ then true else false. 


Lemma eunf_subst : forall e sigma, is_evar e = false ->  eunf (e [e sigma]) = (eunf e)[e sigma].
Proof. 
case;rewrite //=;intros. 
asimpl. f_equal. 
Qed.




Lemma full_unf_com : forall g sigma,  (forall n : nat_eqType, ~~ eguarded n g -> emu_height (sigma n) = 0) -> full_eunf g [e sigma] = (full_eunf g) [e sigma ]. 
Proof. 
intros. rewrite /full_eunf. rewrite emu_height_subst. 
remember (emu_height g). 
clear Heqn. 
elim : n g H. simpl. done. 
intros. simpl. rewrite H //=.
destruct (is_evar (iter n eunf g)) eqn:Heqn.  

destruct (iter n eunf g) eqn:Heqn2;try done. asimpl. simpl. 


have : emu_height (sigma n0) = 0. 
apply/H0. apply/negP=>HH.
apply (@iter_unf_eguarded n) in HH. rewrite Heqn2 in HH. done. 
destruct (sigma n0);try done. 
rewrite eunf_subst //=. eauto. 
Qed.



Lemma unf_com_ren : forall g sigma, eunf g ⟨e sigma ⟩ = (eunf g) ⟨e sigma ⟩.
Proof. 
elim;intros;try done. asimpl. simpl. asimpl. done. 
Qed. 
Lemma iter_unf_com_ren : forall i g sigma, iter i eunf g ⟨e sigma ⟩ = (iter i eunf g) ⟨e sigma ⟩.
Proof. 
elim;intros;simpl. 
done. rewrite H. rewrite unf_com_ren. done. 
Qed. 

Lemma full_unf_com_ren : forall g sigma, full_eunf g ⟨e sigma ⟩ = (full_eunf g) ⟨e sigma ⟩.
Proof. intros. rewrite /full_eunf. rewrite iter_unf_com_ren. rewrite emu_height_ren. done. 
Qed. 




CoInductive lcType :=
 | ECEnd
 | ECMsg : dir -> ch -> value -> lcType -> lcType
 | ECBranch : dir -> ch -> coseq (nat * lcType)  -> lcType.


Lemma ec_match : forall e, e = match e with | ECEnd => ECEnd | ECMsg d a u g0 => ECMsg d a u g0 |  ECBranch d a gs => ECBranch d a gs end. 
Proof. case;auto. Qed.


Definition etocoind' (f : lType -> lcType)  g :=
match full_eunf g with 
| EMsg d a u g0 =>  ECMsg d a u (f g0) 
| EBranch d a gs => ECBranch d a (comap (liftL f) (to_coseq gs))
| _  => ECEnd
end.

CoFixpoint etocoind g := etocoind' etocoind g. 

Lemma etocoind'_eq g : etocoind' etocoind g =
match full_eunf g with 
| EMsg d a u g0 =>  ECMsg d a u (etocoind g0) 
| EBranch d a gs => ECBranch d a (map (liftL etocoind) gs)
| _  => ECEnd
end.
Proof. 
rewrite /etocoind'. destruct (full_eunf g);try done. 
f_equal. elim : l. simpl. rewrite !utils.coeq comap_eq //=. 
intros. rewrite utils.coeq. rewrite utils.comap_eqs /=. rewrite utils.coeq.  f_equal. done. 
Qed.

Lemma etocoind_eq g : etocoind g = etocoind' etocoind g. 
Proof. 
intros. rewrite /etocoind'.  rewrite (ec_match (etocoind g)). 
destruct g;try done;simpl. 
rewrite /etocoind'. 
destruct (full_eunf (ERec g));try done. 
Qed.

Let etocoinds_eqs := (etocoind'_eq, etocoind_eq). 

Lemma full_eunf_end  : full_eunf EEnd = EEnd.  
Proof. done. Qed.

Lemma full_eunf_msg d c u e0 : full_eunf (EMsg d c u e0) = EMsg d c u e0.
Proof. done. Qed.

Lemma full_eunf_branch d c es : full_eunf (EBranch d c es) = (EBranch d c es).  
Proof. done. Qed.

Let eunf_eqs := (full_eunf_end, full_eunf_msg, full_eunf_branch). 

Let eqs := (utils.comap_eqs,etocoinds_eqs, eunf_eqs, utils.coeq). 

Inductive EQ_gen  (R : lcType -> lcType -> Prop) : lcType -> lcType -> Prop := 
 | eq_end : EQ_gen R ECEnd ECEnd
 | eq_msg e0 e1 d c v : R e0 e1 -> EQ_gen R (ECMsg d c v e0) (ECMsg d c v e1)
 | eq_branch es0 es1 d c : (es0 <<(bot2) (forall_gen (fun p0 p1 => p0.1 = p1.1 /\ R p0.2 p1.2))  >> es1)  -> EQ_gen R (ECBranch d c es0) (ECBranch d c es1).
Notation EQ := (paco2 EQ_gen bot2).

Lemma EQ_gen_mon : monotone2 EQ_gen. 
Proof. 
move => x y R. intros. move : IN. fix IH 1. case. 
constructor.
intros. constructor.  apply/LE. done. 
move => es0 es1 d c. intros. constructor. apply/forall_gen_mon2. 3 : eauto. done. 
ssa. 
Qed.

Hint Resolve EQ_gen_mon : paco.


Lemma EQ_refl : forall g r,  g <<(r) EQ_gen  >>  g. 
Proof. 
pcofix CIH. case. pfold. constructor. 
intros. pfold. constructor. right. done. 
intros. pfold. constructor. 
apply/forall_gen_refl. auto. (*Compositional*)
Qed.

Hint Resolve EQ_refl.


Lemma EQ_sym : forall g0 g1, EQ g0 g1 -> EQ g1 g0. 
Proof. 
pcofix CIH. intros. punfold H0. inversion H0;subst.  
pfold. constructor. 
pfold. constructor. right.  apply/CIH. pclearbot. auto. 
pfold. constructor. clear H0. move : es1 es0 H. pcofix CIH2.
intros. punfold H0. inversion H0. pfold. constructor. 
subst. pfold. constructor. ssa. right. apply/CIH. pclearbot. auto. 
right. apply/CIH2. pclearbot. auto. 
Qed.

Lemma EQ_trans : forall g0 g1 g2, EQ g0 g1 -> EQ g1 g2 -> EQ g0 g2. 
Proof. 
pcofix CIH. 
intros. punfold H0. punfold H1. inversion H0;subst;inversion H1;subst. 
pfold. constructor. 
pfold. constructor. right. pclearbot. apply/CIH. eauto. eauto. 
pfold. constructor. clear H0 H1. 
move : es0 es1 es3 H H6. pcofix CIH2. 
intros. punfold H0. punfold H6. inversion H0;inversion H6;subst. 
pfold. constructor. 
done. 
done. 
pfold. inversion H7.  subst. constructor. ssa. pclearbot. rewrite H H2. done. right. pclearbot. apply/CIH. eauto. eauto. 
right. apply/CIH2.  pclearbot. eauto. pclearbot. eauto. 
Qed.


Inductive lUnravel_gen (R : lType -> lcType  -> Prop) : lType -> lcType  -> Prop :=
 | lUnravel_gen_msg e0 ec d c u : R e0 ec -> lUnravel_gen R (EMsg d c u e0) (ECMsg d c u ec)
 | lUnravel_gen_branch (es : seq (nat * lType)) (ecs : seq (nat * lcType)) d c : size es = size ecs -> Forall (fun p => p.1.1 = p.2.1 /\ R p.1.2 p.2.2) (zip es ecs)   -> lUnravel_gen R (EBranch d c es) (ECBranch d c ecs)
 | lUnravel_gen_rec e ec : lUnravel_gen R (e [e ERec e .: EVar]) ec  -> lUnravel_gen R (ERec e) ec (*guarded*)
 | lUnravel_gen_end : lUnravel_gen R EEnd ECEnd.



Lemma lUnravel_gen_mon : monotone2 lUnravel_gen. 
Proof. move => x0 x1. intros. induction IN;try done. con;eauto. 
con;eauto. apply/List.Forall_forall. intros. 
move/List.Forall_forall : H0. eauto. con. eauto. apply H0 in H1. ssa. 
apply H0 in H1. ssa. con. done. con. 
Qed .

Hint Resolve lUnravel_gen_mon : paco. 

Notation lUnravel e0 e1 := (paco2 lUnravel_gen bot2 e0 e1).



Variant lUnravel2_gen (R : lType -> lcType -> Prop) : lType -> lcType  -> Prop :=
 | lUnravel2_gen_msg d c e0 ec u :  R e0 ec -> lUnravel2_gen R  (EMsg d c u e0) (ECMsg d c u ec)
 | lUnravel2_gen_branch c (es : seq (nat * lType))  (ecs : seq (nat * lcType)) d : size es = size ecs -> Forall (fun p => p.1.1 = p.2.1 /\ R p.1.2 p.2.2)(zip es ecs)  -> lUnravel2_gen R (EBranch d c es)  (ECBranch d c ecs)
 | lUnravel2_gen_end :   lUnravel2_gen R EEnd  ECEnd.

Lemma lUnravel2_gen_mon : monotone2 lUnravel2_gen. 
Proof. move => x0 x1. intros. induction IN;try done. con;eauto. 
con;eauto. apply/List.Forall_forall. intros. 
move/List.Forall_forall : H0. eauto. con. apply H0 in H1. ssa. apply H0 in H1. ssa. 
con. 
Qed. 


Hint Resolve lUnravel2_gen_mon. 

Notation UnflUnravel := (ApplyF full_eunf ssrfun.id). 
Notation lUnravel2 e0 e1 := (paco2  (UnflUnravel \o lUnravel2_gen) bot2 e0 e1).

Lemma etocoind_full_eunf : forall e, etocoind e = etocoind (full_eunf e). 
Proof. 
intros. rewrite !eqs full_eunf_idemp //=.
Qed.



Lemma lUnravel_eunf4 :  forall e ec (R: lType -> lcType -> Prop), paco2 lUnravel_gen R (eunf e) ec -> paco2 lUnravel_gen R e ec.
Proof.
intros.  destruct e;try done. pfold. constructor. simpl in H. punfold H. 
Qed.

Lemma lUnravel_eunf5 :  forall n e ec (R: lType -> lcType -> Prop), paco2 lUnravel_gen R (iter n eunf e) ec -> paco2 lUnravel_gen R e ec.
Proof.
elim. done. intros. simpl in H0. apply lUnravel_eunf4 in H0. auto. 
Qed.

Lemma lUnravel_eunf6 :  forall e ec (R: lType -> lcType -> Prop), paco2 lUnravel_gen R (full_eunf e) ec -> paco2 lUnravel_gen R e ec.
Proof. 
intros. rewrite /full_eunf in H. apply/lUnravel_eunf5.  eauto. 
Qed.


Lemma lUnravel_iff : forall e ec, lUnravel e ec <-> lUnravel2 e ec.
Proof.
Proof. intros. split. 
move : e ec. pcofix CIH. 
intros. punfold H0.  induction H0. pclearbot. pfold.
constructor. rewrite /full_eunf /=.  constructor. eauto. 
pfold. constructor. rewrite /full_eunf /=. constructor. done. 
induction H0;auto. constructor. pclearbot. eauto. ssa.  right. apply/CIH. pclearbot. done. done.
pfold. constructor. rewrite full_eunf_subst. 
punfold IHlUnravel_gen. inv IHlUnravel_gen. 
pfold. constructor. rewrite /full_eunf. constructor.
intros. 
move : e ec H.  pcofix CIH. intros. punfold H0. inv H0. 
inv H. apply/lUnravel_eunf6. rewrite -H1. pfold. constructor. 
right. apply/CIH. pclearbot. done. 
apply/lUnravel_eunf6. rewrite -H1. pfold. constructor. done. 
induction H3;auto. con. ssa. pclearbot. eauto. eauto.
apply/lUnravel_eunf6. rewrite -H2. pfold. constructor. 
Qed.



Lemma lUnravel_uniq : forall e ec0 ec1, lUnravel2 e ec0 ->  lUnravel2 e ec1 -> ec0 << EQ_gen >> ec1. 
Proof. 
pcofix CIH. intros. punfold H0. punfold H1. inv H0. inv H1. inv H;pclearbot.
rewrite -H3 in H2. inv H2;pc.  inv H10;try done. right. apply/CIH. eauto. eauto.
rewrite -H3 in H2. inv H2. pfold. con. apply coerce_forall2. lia. 
clear H0 H1 H2 H3 H. 
elim : es ecs ecs0 H4 H10 H5 H11.
case=>//=. case=>//=.
move => a l  IH [] //=. move => a0 l0 [] //=. move => a1 l1. intros. inv H4. inv H10.  inv H5.  inv H11.
pclearbot. ssa. 
con;eauto. 
ssa. rewrite -H3 -H. done. pclearbot. eauto. 
rewrite -H4 in H2. inv H2. 
Qed.

Lemma lUnravel_eq : forall g gc0 gc1, gc0 << EQ_gen >> gc1 ->  lUnravel2 g gc0 ->  lUnravel2 g gc1.
Proof.
pcofix CIH. 
intros. punfold H1. pfold.   constructor. inv H1. induction H;pclearbot. uis H0.
constructor.  eauto. 
uis H0. apply coerce_forall in H7. destruct H7. ssa. 
rewrite -H4. 
constructor. lia. clear H4 H0 H1.
elim : es ecs x H H3 H2 H5. case;last done. case;last done. 
simpl. auto. 
move => a l IH [];first done. 
move => a0 l0 [];first done. intros. simpl in *. 
inv H. inv H3.  inv H2.  inv H5. pclearbot. simpl in *. constructor. 
simpl. ssa. rewrite H7 H0. done. pclearbot. eauto. eauto. 
uis H0. constructor.
Qed.


Lemma etocoind_rec e : (etocoind (ERec e)) = etocoind (e [e ERec e .: EVar]). 
Proof.
rewrite 4!eqs full_eunf_subst //=.  
Qed.


(*Later perhaps do it with gpaco*)
Lemma unravele_exist : forall e,  lUnravel2 e (etocoind e) <-> exists ec, lUnravel2 e  ec.
Proof. 
intros. split. 
intros. exists (etocoind e).  done.
case. move : e. 
intros. 
move : x e p. pcofix CIH. 
move => x e Hu. punfold Hu. inv Hu. 
pfold. con. rewrite etocoind_full_eunf.
 inv H;rewrite 3!eqs;try con;eauto;pclearbot. eauto. rewrite size_map. done. 
clear H Hu H0. 
elim :es ecs H1 H2. case;try done;ssa.  move => a l IH [] //=.  ssa. 
con. inv H2.  pclearbot. ssa. right. eauto. inv H2. ssa. 
destruct a. ssa. pclearbot. eauto. 
eapply IH. eauto. inv H2. 
Qed. 



Fixpoint enum e :=
e::
match e with 
| ERec e0 => map (fun e0 => e0 [e e .: EVar]) (enum e0)
| EMsg d c v e0 => enum e0
| EBranch d c es => flatten (map (enum \o snd) es)
| EEnd => nil
| EVar n => nil
end.

Definition nexte e := 
match e with 
| EMsg _ _ _ e0 => (e0::nil)
| EBranch _ _ es => map snd es 
| _ => nil
end.

Definition nexte_unf e :=nexte (full_eunf e). 

Lemma selfe : forall e, e \in enum e. 
Proof. intros. destruct e;rewrite //=. 
Qed. 




Lemma enum_closed_eunf : forall e, unf_closed (enum e) eunf.
Proof. 
rewrite /unf_closed. 
elim;rewrite //=;intros. 
- rewrite inE in H. rewrite (eqP H). done. 
- rewrite inE in H. rewrite (eqP H). done. 
- rewrite inE in H0. destruct (orP H0). rewrite (eqP H1) /=. 
  rewrite inE. apply/orP. right. apply/map_f/selfe. 
  move : H1. move/mapP=>[]/=. intros. subst. rewrite inE. apply/orP. right.
  destruct (is_evar x) eqn:Heqn. 
  destruct x;try done. simpl.  destruct n. simpl. apply/map_f. apply/selfe. 
  simpl. have : EVar n = (EVar n.+1) [e ERec e .: EVar]. simpl. done. 
  move=>->. apply/map_f. done. 
  rewrite eunf_subst. apply/map_f/H/p. eauto. 
- rewrite inE in H0. destruct (orP H0). rewrite (eqP H1). rewrite /= !inE eqxx //=. 
  rewrite inE. rewrite H. lia. done. 
- rewrite inE in H0. destruct (orP H0). rewrite (eqP H1) inE eqxx //=. 
  rewrite inE. apply/orP. right. apply/flattenP. destruct (flattenP H1). exists x. done. 
  destruct (mapP H2). subst. destruct x0.  apply/H. ssa. eauto. ssa. 
Qed.


Lemma enum_closed_full_eunf : forall e, unf_closed (enum e) full_eunf.    
Proof. 
rewrite /unf_closed. 
intros. rewrite /full_eunf. remember (emu_height a). clear Heqn. 
elim : n. done. intros. simpl. apply/enum_closed_eunf.  done. 
Qed.

Lemma next_subst : forall e sigma, (if e is EVar _ then false else true) ->  nexte (e [e sigma]) = map (fun e0 => e0 [e sigma]) (nexte e).
Proof. 
destruct e;try done. ssa. elim : l.  ssa. ssa. f_equal. destruct a. ssa. ssa. 
Qed. 



Lemma enum_closed_nexte : forall e, next_closed (enum e) nexte.  
Proof. 
rewrite /next_closed. 
elim;rewrite //=;intros. 
rewrite inE in H. rewrite (eqP H) //= in H0.  
rewrite inE in H. rewrite (eqP H) //= in H0.  
rewrite inE in H0. destruct (orP H0). 
rewrite (eqP H2) //= in H1. 
move : H2. move/mapP=>[] //=. intros. subst. simpl.
destruct (if x is EVar _ then false else true) eqn:Heqn. 
 rewrite next_subst //= in H1.  
rewrite inE. apply/orP. right. 
destruct (mapP H1). subst. apply/map_f. apply/H. 2 : {  eauto. } 
eauto. 
destruct x;try done. simpl. destruct n. simpl. done. done.  
rewrite inE in H0. destruct (orP H0). rewrite (eqP H2) /= in H1. rewrite inE in H1.  rewrite (eqP H1) inE selfe. 
lia. rewrite inE. erewrite H. lia. eauto. done. 
rewrite inE in H0. destruct (orP H0). rewrite (eqP H2) /= in H1. rewrite inE. apply/orP. right.




apply/flattenP. exists (enum a'). apply/mapP.  
apply mem_map_snd in H1. destruct H1. 
exists (x,a'). done. done. apply/selfe. 
rewrite inE. apply/orP. right. destruct (flattenP H2). 
destruct (mapP H3). subst. apply/flattenP. exists (enum  (snd x0)). apply/map_f. done.
destruct x0. 
apply/H. ssa. eauto. ssa. eauto. ssa. 
Qed.

Lemma enum_closed_nexte_unf : forall e, next_closed (enum e) nexte_unf.  
Proof. 
rewrite /next_closed. intros. rewrite /nexte_unf in H0. apply/enum_closed_nexte. 
2 : { eauto. } rewrite /full_eunf. 
apply/enum_closed_full_eunf. done. 
Qed.


Lemma enum_ren : forall e sigma, enum e ⟨e sigma⟩ = map (fun e0 => e0 ⟨e sigma⟩) (enum e).
Proof. 
elim;rewrite //=;intros. 
asimpl. f_equal. rewrite H.  rewrite -!map_comp. rewrite /comp. apply/eq_in_map => x xIn. 
asimpl. done. 
f_equal. done. f_equal. rewrite -map_comp. rewrite !map_flatten. 
rewrite -map_comp. f_equal.  rewrite /comp. apply/eq_in_map=> x xIn.
destruct x. ssa. eauto.
Qed.
 
Lemma enum_subst : forall e e' sigma (S : seq lType), (forall n e0, ~~ is_evar (sigma n) -> e0 \in enum (sigma n) -> e0 \in S) -> e' \in enum e [e sigma] -> e' \in map (fun e0 =>  e0 [e sigma]) (enum e) \/ e' \in S. 
Proof. 
elim;rewrite //=;intros. 
destruct (is_evar (sigma n)) eqn:Heqn. destruct (sigma n);try done. simpl in H0. rewrite inE in H0. rewrite (eqP H0). 
auto. right. apply/H. lia. done. 
rewrite inE in H0. rewrite (eqP H0). auto.
rewrite inE in H1.  destruct (orP H1). 
rewrite (eqP H2). rewrite inE. left. rewrite eqxx. lia. 
rewrite -!map_comp. 
rewrite /comp. 
have : map (fun x => x [e ERec e .: EVar] [e sigma]) (enum e) =  map (fun x =>  x [e ERec e [e EVar 0 .: sigma >> ⟨e ↑ ⟩] .: sigma]) (enum e). 
apply/eq_in_map. move=> x xIn. asimpl. done. move=>->. 
move : H2. move/mapP=>[]. intros. 
subst. 
intros.
asimpl. 
eapply H in p. 
destruct p. destruct (mapP H2). subst. asimpl. left. rewrite inE. apply/orP. right. apply/map_f. done. 
right. 
2 : { intros. move : H2 H3. destruct n. asimpl. done. asimpl. rewrite enum_ren. intros. 
  destruct (mapP H3). subst. apply H0 in H4. instantiate (1 := map (fun e0 => e0 ⟨e succn ⟩) S).
apply/map_f.  done. destruct (sigma n);try done. } 
destruct (mapP H2). subst. asimpl. done.
rewrite inE in H1.  destruct (orP H1). 
rewrite (eqP H2). auto.
rewrite inE. intros. 
eapply H in H2. destruct H2.  left. apply/orP. right. done. eauto. 
auto. 

rewrite inE in H1. destruct (orP H1). rewrite (eqP H2) /=. auto.
clear H1. 
rewrite -map_comp /comp in H2. destruct (flattenP H2). destruct (mapP H1). 
subst. ssa. destruct x0.  ssa. eapply H in H3. 
destruct H3. left. apply/orP. right. rewrite map_flatten -map_comp /comp. 
destruct (mapP H3). subst. apply/flattenP. exists ([seq e0 [e sigma] | e0 <- enum l0]). 
have :  map (fun x0 : fin * lType => map (subst_lType sigma) (enum x0.2)) l = 
 map (fun x0 : lType => map (subst_lType sigma) (enum x0)) (map snd l).
clear H H2 H1 H4.
elim : l. ssa. ssa. f_equal. ssa. move=>->. 
apply/map_f. have : l0 = snd (n,l0). done. move=>->. apply/map_f. done. done. 
right. eauto. eauto. eauto. 
Qed.



Lemma enum_subst_eunf : forall e e', e' \in enum (eunf e)  -> e' \in enum e.  
Proof. 
intros. 
destruct e;try done. 
move : H. simpl. move/enum_subst=>HH. 
move : (HH (enum (ERec e)))=>HH'.
edestruct HH'. case. 
simpl. intros. done. done. 
rewrite inE. rewrite H. lia.
simpl in H. done.  
Qed.

Lemma enum_subst_iter_eunf : forall k e e', e' \in enum (iter k eunf e)  -> e' \in enum e.  
Proof. 
elim. done. 
intros. apply/H. apply/enum_subst_eunf. rewrite -iterS. done. 
Qed.

Lemma enum_subst_nexte : forall e e' e'', e' \in nexte e -> e'' \in enum e'  -> e'' \in enum e.  
Proof. 
case;intros;try done.  
simpl in H. 
rewrite inE in H.  simpl. move : H. move/eqP=>HH. subst. rewrite inE H0 //=. lia. 
simpl in H. simpl. rewrite inE. apply/orP. right. apply/flattenP.
apply mem_map_snd in H. destruct H. 
 exists (enum (snd (x,e'))).
apply/map_f. done. ssa. 
Qed.

Lemma enum_subst_nexte_unf : forall e e' e'', e' \in nexte_unf e -> e'' \in enum e'  -> e'' \in enum e.  
Proof. 
intros. rewrite /nexte_unf in H.  eapply enum_subst_nexte in H. apply/enum_subst_iter_eunf. eauto. 
done. 
Qed.


Inductive EQ2_gen  (R : lType  -> lType  -> Prop) : lType  -> lType  -> Prop := 
 | eq_end2 : EQ2_gen R EEnd EEnd
 | eq_msg2 e0 e1 d c v : R e0 e1 -> EQ2_gen R (EMsg d c v e0) (EMsg d c v e1)
 | eq_branch2 es0 es1 d c : size es0 = size es1 -> Forall (fun p => p.1.1 = p.2.1 /\ R p.1.2 p.2.2) (zip es0 es1)  -> 
                            EQ2_gen R (EBranch d c es0) (EBranch d c es1).

Lemma EQ2_gen_mon  : monotone2 EQ2_gen. 
Proof. 
move => x0 x1. intros. induction IN;try done. con. con;eauto. con;eauto. 
elim : es0 es1 H H0 LE;try done. case=>//=. move => a l IH [] //=. 
intros. inv H. inv H0. simpl in *. con;eauto . ssa. 
Qed.


Hint Resolve EQ2_gen_mon : paco.

Notation EQ2 := (fun e0 e1 => paco2 ((ApplyF full_eunf full_eunf) \o EQ2_gen) bot2 e0 e1).


Ltac pc := pclearbot.

Lemma EQ2_spec1 : forall e0 e1 ec0 ec1, lUnravel2 e0 ec0 -> lUnravel2 e1 ec1 ->  EQ2 e0 e1 -> paco2 EQ_gen bot2 ec0 ec1. 
Proof. 
pcofix CIH. intros. punfold H0. punfold H1. punfold H2.
inv H0. clear H0. 
inv H1. clear H1. 
inv H2. clear H2. 
inv H1;pc. 
rewrite -H3 in H.  rewrite -H4 in H0. inv H. inv H0. 
rewrite -H2 in H.  rewrite -H3 in H0. inv H. inv H0. pc. pfold. con. eauto. 
rewrite -H2 in H.  rewrite -H3 in H0. inv H. inv H0. pc. pfold. con.
apply/Forall_ForallC.  lia. 
clear H2 H3 H H0 H1. elim : es0 es1 ecs ecs0 H4 H10 H12 H5 H11 H13. 
case=>//=. 
case=>//=. 
case=>//=. move => a l IH [] //=. move => a0 l0 [] //=. move => a1 l1 [] //=. 
intros. inv H4.  inv H10.  inv H12. inv H5.  inv H11. inv H13. con; eauto. simpl in *. pc. 
eauto. ssa. rewrite -H8 H6 //=. right. pclearbot.  ssa.  eauto. 
Qed. 

Lemma EQ2_spec2 : forall e0 e1 ec0 ec1, lUnravel2 e0 ec0 -> lUnravel2 e1 ec1 -> paco2 EQ_gen bot2 ec0 ec1 -> EQ2 e0 e1. 
Proof. 
pcofix CIH. intros. punfold H0. punfold H1. punfold H2.
inv H0. clear H0. 
inv H1. clear H1. 
inv H2. clear H2. pfold.  con. 
inv H;pc.  inv H0;pc. con. 
pc. pfold.  con. 
inv H;pc.  inv H0;pc. con. eauto.
pfold.  con. 
inv H;pc.  inv H0;pc. con.  rewrite H6 H9.  
apply coerce_forall in H1. destruct H1. ssa. injt. lia. 
clear H H2 H0 H3 H4.  apply coerce_forall in H1. destruct H1. ssa. injt. 
elim : ecs ecs0 es es0 H H6 H9 H1 H8 H11.
case=>//=.  case=>//=. case. simpl. done. done.  
move => a l IH.  
case =>//=. move => a1 l1. move=> [] //=. move => a0 l0 [] //=.  move => a2 l2. intros. inv H. inv H6. inv H9. inv H1. inv H8. inv H11. pc. simpl in *. 
con;eauto. ssa. 
rewrite H12 H7 //=. right. pclearbot. eauto. 
Qed. 


Lemma EQ2_eunf : forall e0 e1 r, e0 <<( r) (ApplyF full_eunf full_eunf \o EQ2_gen) >> (full_eunf e1)  -> e0 <<( r) (ApplyF full_eunf full_eunf \o EQ2_gen) >> e1.
Proof. 
intros. punfold H. inv H. pfold. con. rewrite full_eunf_idemp in H0. done. 
Qed.

Lemma EQ2_eunf2 : forall e0 e1 r, e0 <<( r) (ApplyF full_eunf full_eunf \o EQ2_gen) >> e1  -> e0 <<( r) (ApplyF full_eunf full_eunf \o EQ2_gen) >> (full_eunf e1).
Proof. 
intros. punfold H. inv H. pfold. con. rewrite full_eunf_idemp. done. 
Qed.

Lemma EQ2_eunfl : forall e0 e1 r, (full_eunf e0) <<( r) (ApplyF full_eunf full_eunf \o EQ2_gen) >> e1  -> e0 <<( r) (ApplyF full_eunf full_eunf \o EQ2_gen) >> e1.
Proof. 
intros. punfold H. inv H. pfold. con. rewrite full_eunf_idemp in H0. done. 
Qed.

Lemma EQ2_eunfl2 : forall e0 e1 r, e0 <<( r) (ApplyF full_eunf full_eunf \o EQ2_gen) >> e1  -> (full_eunf e0) <<( r) (ApplyF full_eunf full_eunf \o EQ2_gen) >> e1.
Proof. 
intros. punfold H. inv H. pfold. con. rewrite full_eunf_idemp. done. 
Qed.


Inductive lInvPred_gen (R : lType ->  Prop) : lType   -> Prop :=
 | role_gen_msg e0 c d u :  R e0 -> lInvPred_gen R  (EMsg d c u e0) 
 | role_gen_branch c (es : seq (nat * lType))  d :  Forall (R \o snd) es -> lInvPred_gen R (EBranch d c es) 
 | role_gen_end :   lInvPred_gen R EEnd.

Lemma lInvPred_gen_mon : monotone1 lInvPred_gen. 
Proof. move => x0 x1. intros. induction IN;try done. con;eauto. 
con;eauto. apply/List.Forall_forall. intros. eauto. 
move/List.Forall_forall : H. eauto. intros. cbn. destruct x. ssa. apply/LE. 
have : l = snd (n,l). done. move=>->. apply/H. done. 
con.  
Qed. 


Hint Resolve lInvPred_gen_mon : paco. 
Notation lInvPred := (paco1 (ApplyF1 full_eunf \o lInvPred_gen) bot1).  

Lemma EQ2_tree : forall e0 e1, EQ2 e0 e1 -> lInvPred e0.
Proof. 
pcofix CIH. intros. 
punfold H0. inv H0. pfold. con. inv H. con. con. pc.  eauto. 
con. clear H1 H2. elim : es0 es1 H3 H4. case. done. done. 
move => a l IH [] //=. intros. inv H3. inv H4. pc. simpl in *. con; eauto. 
ssa. right. pclearbot. eauto. 
Qed. 

Lemma EQ2_tree2 : forall e0 e1, EQ2 e0 e1 -> lInvPred e1.
Proof. 
pcofix CIH. intros. 
punfold H0. inv H0. pfold. con. inv H. con. con. pc.  eauto. 
con. clear H1 H2. elim : es0 es1 H3 H4. case. done. done. 
move => a l IH [] //=. intros. inv H3. inv H4. pc. simpl in *. con; eauto. 
ssa. pclearbot. eauto. 
Qed. 

Lemma lInvPred_lUnravel : forall g ,  lInvPred g -> lUnravel2 g (etocoind g).
Proof. 
pcofix CIH. intros. punfold H0. inv H0. pfold.
rewrite etocoind_full_eunf.  con. 
inv H;eauto;pclearbot;rewrite !eqs.  
rewrite -etocoind'_eq -etocoind_eq. con. eauto. 
con. rewrite size_map //=. 
clear H H1 H0. elim : es H2. simpl.  auto. 
simpl. intros. inv H2. pclearbot. con;ssa. 
con;ssa.
Qed.


Inductive lInvPred2_gen (R : lType ->  Prop) : lType   -> Prop :=
 | role2_gen_msg e0 c d u :  R e0 -> lInvPred2_gen R  (EMsg d c u e0) 
 | role2_gen_branch c (es : seq (nat * lType))  d :  Forall (R \o snd) es -> lInvPred2_gen R (EBranch d c es) 
 | role2_gen_end :   lInvPred2_gen R EEnd
 | role2_gen_var  n :   lInvPred2_gen R (EVar n).


Lemma lInvPred2_gen_mon : monotone1 lInvPred2_gen. 
Proof. move => x0 x1. intros. induction IN;try done. con;eauto. 
con;eauto. apply/ForallP. intros. apply/LE. 
move/ForallP : H. intros. apply/H. done. con.  con. 
Qed. 


Hint Resolve lInvPred2_gen_mon : paco. 

Notation lInvPred2 := (paco1 ( ApplyF1 full_eunf \o lInvPred2_gen) bot1).

Theorem EQ2_spec : forall e0 e1, EQ2 e0 e1 <-> exists ec0 ec1, lUnravel2 e0 ec0 /\ lUnravel2 e1 ec1 /\ paco2 EQ_gen bot2 ec0 ec1. 
Proof. 
intros. split. intros. exists (etocoind e0). exists (etocoind e1). ssa. 
apply/lInvPred_lUnravel/EQ2_tree. eauto. 
apply/lInvPred_lUnravel/EQ2_tree2. eauto. apply/EQ2_spec1.
apply/lInvPred_lUnravel. apply/EQ2_tree. eauto. 
apply/lInvPred_lUnravel. apply/EQ2_tree2. eauto. done. 
case. move => x. case. intros. ssa. apply/EQ2_spec2. eauto. eauto. done. 
Qed. 


Lemma lInvPred_iff : forall g, lInvPred g <-> lInvPred (full_eunf g). 
Proof. 
intros. split. intros. punfold H. inv H. pfold. con. rewrite full_eunf_idemp. done. 
intros. punfold H. inv H. rewrite full_eunf_idemp in H0. pfold. con. done. 
Qed.

Lemma EQ2_refl : forall g, lInvPred g ->  g << (ApplyF full_eunf full_eunf \o  EQ2_gen)  >>  g. 
Proof. 
pcofix CIH. intros. punfold H0. inv H0. pfold.  con. inv H. 
con. pclearbot. eauto. con. lia. clear H1. elim : es H2. simpl. done. 
simpl. intros. inv H2. pclearbot. con;eauto. 
con. 
Qed.

Lemma EQ2_reflr : forall g r, lInvPred g ->  g <<(r) (ApplyF full_eunf full_eunf \o  EQ2_gen)  >>  g. 
Proof. 
pcofix CIH. intros. punfold H0. inv H0. pfold.  con. inv H. 
con. pclearbot. eauto. con. lia. clear H1. elim : es H2. simpl. done. 
simpl. intros. inv H2. pclearbot. con;eauto. 
con. 
Qed.

Definition not_rec e :=
match e with 
| ERec _  => false 
| _ => true
end.  

Fixpoint lType_fv e :=
  match e with
  | EVar j => [:: j]
  | EEnd => nil
  | EMsg _ _ _ g0 => lType_fv g0
  | EBranch _ _ gs => flatten (map (lType_fv \o snd) gs)
  | ERec g0 => map predn (filter (fun n => n != 0) (lType_fv g0))
  end.

Definition eclosed e := forall n, n \notin lType_fv e.


Lemma eguarded_sig2 : forall g sigma sigma' i, eguarded i g [e sigma] -> (forall n, eguarded i (sigma n) -> eguarded i (sigma' n)) -> eguarded i g [e sigma'].
Proof.
elim;rewrite /=;intros;try done.
apply H0. done.
asimpl. apply : H. eauto. move => n.  asimpl. simpl. intros. destruct n. done. simpl in *.
move : H. rewrite /funcomp. specialize H1 with n. move : H0. asimpl.
intros. rewrite -eguarded_ren_iff. move : H. rewrite -eguarded_ren_iff.  move/H1. done. 
done. done. 
Qed.



Lemma  eguarded_fv : forall g v, v \notin lType_fv g -> eguarded v g.
Proof.
elim;rewrite /=;try done;intros.
rewrite !inE in H. lia.
apply H. move : H0. intros. apply/negP=>HH'. apply/negP. apply H0. apply/mapP. exists v.+1. rewrite mem_filter. ssa. done. 
Qed.
 

Lemma inotin : forall g i sigma, (forall n, i !=  sigma n) -> i \notin lType_fv g ⟨e sigma ⟩.
Proof.
elim;rewrite /=;try done;intros. rewrite !inE. specialize H with n. lia.
apply/negP. move/mapP. case. ssa. subst. rewrite mem_filter in p. ssa. 
destruct x;try done. ssa. apply/negP. apply/H. 2 : eauto. asimpl. intros.
destruct n. done. ssa. asimpl. move: (H0 n).  lia. 
apply/negP. move/flattenP. case. move=> x. rewrite -map_comp. move/mapP.  case. intros. subst. 
destruct x0. 
apply/negP. apply/H. eauto. eauto. done. 
Qed.

Lemma lcontractive_ren : forall g sigma, injective sigma -> (forall n, n <= sigma n) ->  lcontractive  g -> lcontractive g ⟨e sigma ⟩.
Proof.
elim;intros;simpl;try done. 
asimpl. split_and. have : 0 = ( 0 .: sigma >> succn) 0. done. move=>x. rewrite {1}x.
apply eguarded_ren. auto. ssa. apply/H=>//=. auto. intros. destruct n. simpl. done. ssa. asimpl. move : (H1 n). lia. ssa. ssa. 
rewrite all_map. apply/allP. intro. intros. simpl. destruct x. ssa. eapply H. eauto. done.  done.
move/allP : H2.  intro. apply H2 in H3. ssa. 
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
rewrite all_map. apply/allP. intro. intros. simpl. destruct x. ssa. eapply H. eauto. 
move/allP : H0. intro. apply H0 in H2. ssa. done. 
Qed.


Lemma econtractive_unf : forall g , lcontractive g -> lcontractive (eunf g). 
Proof.
intros. rewrite /eunf. destruct g;try done. apply/lcontractive_subst. ssa. case;done. 
Qed.

Lemma econtractive_iter_unf : forall k g , lcontractive g -> lcontractive (iter k eunf g). 
Proof.
elim;try done. intros. simpl. apply/econtractive_unf. ssa. 
Qed.

Lemma econtractive_full_eunf : forall g , lcontractive g -> lcontractive (full_eunf g). 
Proof. 
intros. rewrite /full_eunf. apply/econtractive_iter_unf. done. 
Qed.


Lemma lcontractive_subst2 : forall g sigma,lcontractive g [e sigma] -> lcontractive g. 
Proof. 
elim;rewrite /=;intros;try done.  ssa. apply/eguarded_subst2.  eauto. simpl. done. eauto. 
eauto. apply/allP=> x xIn. destruct x. simpl.   apply/H. eauto. rewrite all_map in H0. 
move/allP : H0. intro. apply H0 in xIn. ssa. eauto. 
Qed. 


Lemma eguarded_sig2_ren : forall g sigma sigma' i, eguarded i g ⟨e sigma⟩ -> (forall n, (sigma n) != i ->  (sigma' n) != i) -> eguarded i g ⟨e sigma'⟩.
Proof.
elim;rewrite /=;intros;try done.
apply H0. done.
asimpl. apply : H. eauto. move => n.  asimpl. simpl. intros. destruct n. done. simpl in *. 
move : H. rewrite /funcomp. intros. suff :  sigma' n != i.  lia. apply : H1. lia. 
Qed.


Lemma lcontractive_ren2 : forall g sigma, lcontractive g ⟨e sigma⟩ -> lcontractive g. 
Proof. 
elim;intros;ssa. eapply (@eguarded_sig2_ren _ _ id) in H1. move : H1. asimpl. done.
asimpl.  rewrite /id. intros. apply/eqP.  move => HH. subst. simpl in H0. done. eauto. 
eauto. apply/allP=> x xIn.  rewrite all_map in H0. destruct x. 
move/allP : H0. intro. apply H0 in xIn as HH. ssa. 
apply/H. eauto.  eauto. 
Qed .

Lemma lcontractive_subst3 : forall g sigma n, lcontractive g [e sigma] -> n \in lType_fv g -> lcontractive (sigma n).
Proof. 
elim;rewrite /=;intros;try done. rewrite inE in H0. rewrite (eqP H0). done. 
move/mapP : H1. case. intros. subst. rewrite mem_filter in p. ssa. destruct x. ssa. ssa.
eapply H in H4.  2: eauto. simpl in H4. move : H4. asimpl.
move/lcontractive_ren2.  done. eauto.
move/flattenP : H1.   case.  intros. move/mapP : p.   case.  intros. subst. destruct x0.  
apply/H.  eauto. rewrite all_map in H0.
move : (allP H0 _ p).  ssa. ssa. 
Qed. 

Lemma lType_fv_ren : forall g sigma, (lType_fv g ⟨e sigma⟩) = map sigma (lType_fv g). 
Proof. 
elim;rewrite //=;intros. 
rewrite -!map_comp. rewrite H.
rewrite filter_map /=. clear H. asimpl. 
elim : (lType_fv e). done. ssa. 
destruct (eqVneq a 0). subst. simpl. ssa. 
simpl. destruct a. done. simpl. f_equal. done. 
rewrite -!map_comp. rewrite map_flatten. rewrite -!map_comp. 
f_equal. apply/eq_in_map=> x xIn. simpl. destruct x. ssa. eauto. 
Qed.

Lemma lType_fv_subst : forall g sigma, (lType_fv g [e sigma]) = flatten (map (sigma >> lType_fv) (lType_fv g)). 
Proof. 
elim;rewrite //=;intros. 
rewrite cats0. asimpl. done. 
rewrite H. rewrite -!map_comp. 
asimpl.  rewrite filter_flatten.
rewrite -!map_comp. rewrite !map_flatten.
rewrite -map_comp.
rewrite /comp. asimpl. clear H.
elim : ( lType_fv e);try done. ssa. 
destruct (eqVneq a 0). simpl. subst. simpl. done. 
simpl. destruct a. done. simpl.
f_equal. asimpl. rewrite lType_fv_ren. 
rewrite filter_map /=. rewrite -map_comp.
clear i.  clear H. 
elim : ( lType_fv (sigma a));try done. ssa. 
f_equal. done. done.  

rewrite -map_comp. 
rewrite !map_flatten.  rewrite -!map_comp. 
rewrite /comp. asimpl. 
elim : l H. done. ssa. simpl.
rewrite flatten_cat. f_equal.  destruct a. ssa. apply/H0. eauto. eauto. 
Qed.




Lemma lType_fv_eunf : forall g n, (n \in lType_fv g) = (n \in lType_fv (eunf g)).  
Proof. 
case=>//=. intros. rewrite lType_fv_subst. 
apply/eq_iff. split. move/mapP=>[] x /=. rewrite mem_filter. ssa. subst. 
apply/flattenP. destruct x;try done. simpl. 
have : ((ERec l .: EVar) >> lType_fv) = 
([seq i.-1 | i <- lType_fv l & i != 0] .: fun n => [::n]).
asimpl. simpl. f_equal. move=>->.
exists ([::x]). 
apply/mapP. exists x.+1. ssa. simpl. done. done. 
move/flattenP=>[] x. move/mapP=>[] x0. intros. subst. destruct x0;try done.  
move : q0. asimpl. simpl. rewrite inE. move/eqP. intros. subst. apply/mapP. exists x0.+1=>//=. 
rewrite mem_filter. ssa. 
Qed.

Lemma lType_fv_full_eunf : forall g n, (n \in lType_fv g) = (n \in lType_fv (full_eunf g)).  
Proof. 
intros. rewrite /full_eunf. remember (emu_height g). clear Heqn0. elim : n0 g. done. 
intros. rewrite iterS. rewrite H. apply/lType_fv_eunf. 
Qed.

Lemma econtractive_unf2 : forall g , lcontractive (eunf g) -> lcontractive g. 
Proof.
intros. rewrite /eunf. destruct g;try done. ssa. 
destruct (eguarded 0 g) eqn:Heqn. done. 
eapply (@lcontractive_subst3 _ _ 0) in H. ssa. rewrite Heqn in H0.  done.
rewrite lType_fv_full_eunf. 

apply eguarded_unfv in Heqn as Heqn'. rewrite Heqn' /= !inE //=.
apply lcontractive_subst2 in H.  done. 
Qed. 

Lemma econtractive_full_unf2 : forall g , lcontractive (full_eunf g) -> lcontractive g. 
Proof. intros. rewrite /full_eunf in H. remember (emu_height g). clear Heqn. 
elim : n g H. done. ssa. apply/econtractive_unf2. apply/H.  rewrite -iterSr /=. done. 
Qed.

Lemma econtractive_full_unf2_eq : forall g , lcontractive g = lcontractive (full_eunf g). 
Proof. intros. apply/eq_iff. split. apply/econtractive_full_eunf.
apply/econtractive_full_unf2. 
Qed.


Inductive lInvPred3 : lType   -> Prop :=
 | rol3_gen_msg s g g' a u :  full_eunf g = EMsg s a u g' -> lInvPred3 g' -> lInvPred3 g 
 | rol3_gen_branch s g (gs : seq (nat * lType)) l g' a :  full_eunf g = EBranch s a gs -> (l,g') \in gs -> lInvPred3 g' -> lInvPred3 g 
 | rol3_gen_rec g g' :   full_eunf g = ERec g' -> lInvPred3 g.

Lemma lInv_idemp : forall g, lInvPred3 (full_eunf g) -> lInvPred3 g. 
Proof. 
intros. inv H. econstructor. rewrite full_eunf_idemp in H0. eauto. done.  
rewrite full_eunf_idemp in H0. econstructor 2.  eauto. eauto. done. 
rewrite full_eunf_idemp in H0. econstructor 3. eauto. 
Qed. 

Lemma lInv_idemp2 : forall g, lInvPred3 g -> lInvPred3 (full_eunf g). 
Proof. 
intros. inv H. rewrite H0. econstructor. cbn.  eauto. done. 
econstructor 2. rewrite full_eunf_idemp. eauto. eauto. eauto. 
econstructor 3. rewrite full_eunf_idemp. eauto. 
Qed. 


Lemma full_eunf_com2 : forall g sigma,  (forall n : nat_eqType, ~~ eguarded n g -> emu_height (sigma n) = 0) -> full_eunf g [e sigma] = (full_eunf g) [e sigma ]. 
Proof. 
intros. rewrite /full_eunf. rewrite emu_height_subst. 
remember (emu_height g). 
clear Heqn. 
elim : n g H. simpl. done. 
intros. simpl. rewrite H //=.
destruct (is_evar (iter n eunf g)) eqn:Heqn.  

destruct (iter n eunf g) eqn:Heqn2;try done. asimpl. simpl. 


have : emu_height (sigma n0) = 0. 
apply/H0. apply/negP=>HH. apply (@eguarded_iter_unf  n) in HH. rewrite Heqn2 in HH. ssa. lia. 
destruct (sigma n0);try done. 
rewrite eunf_subst //=. done. 
Qed.


Lemma lInv_struct0 : forall g sigma,  (forall n, emu_height (sigma n.+1) = 0) ->  lInvPred3 g -> lInvPred3 (g [e sigma]). 
Proof. 
intros. elim : H0 H. intros. apply/lInv_idemp. rewrite full_eunf_com2. rewrite H. ssa. econstructor. ssa. 
apply/H1. done. intros. destruct n. have : eguarded 0 g0 = false. lia. 
move/eguarded_unfv. move=> HH2.  rewrite HH2 in H. done. done. 
intros. econstructor 2.  rewrite full_eunf_com2. rewrite H. asimpl. eauto. 
intros. destruct n. have : eguarded 0 g0 = false. lia. move/eguarded_unfv.  move => HH. 
rewrite H in HH.  done.  done. rewrite /prod_map.
have : ((fun p : fin * lType => let (a0, b) := p in (a0, b [e sigma])) \o id) (l,g') \in map (fun p : fin * lType => let (a0, b) := p in (a0, b [e sigma])) gs. 
apply/map_f. done. cbn.  eauto. 
 eauto.  
intros. econstructor 3. rewrite full_eunf_com2. rewrite H. asimpl.  eauto. 
intros. destruct n.  have : eguarded 0 g0 = false. lia. move/eguarded_unfv. move => HH. intros. rewrite HH in H. done. 
done.
Qed. 


Lemma lInv_struct : forall g,  lInvPred3 g -> lInvPred3 (ERec g). 
Proof. intros. apply/lInv_idemp. rewrite full_eunf_subst. 
destruct (eguarded 0 g) eqn:Heqn. 
rewrite full_eunf_com2. apply/lInv_struct0. 
ssa. apply/lInv_idemp2.  done. 
intros. destruct n. rewrite Heqn in H0. done. done. 
apply eguarded_unfv in Heqn.
apply lInv_idemp2 in H. rewrite Heqn in H. inv H. 
Qed. 



Lemma lInvPred_contractive3 : forall g, lInvPred2 g -> lInvPred3 g -> False.  
Proof. intros. move : H. elim : H0;intros.  
apply/H1. punfold H2.  inv H2. rewrite H in H3. inv H3. pclearbot. done. 
apply/H2. punfold H3. inv H3. rewrite H in H4. inv H4. move/ForallP : H6. 
move/inP: H0.  intros.
move/H6 : H0.  case=>//=.
punfold H0. inv H0. rewrite H in H1. inv H1. 
Qed. 


Inductive EBad3 : lType -> Prop := 
 | EBad31 g : eguarded 0 g = false  -> EBad3 (ERec g)
 | EBad32 g : EBad3 g -> EBad3 (ERec g).



Lemma ebad_ren : forall g sigma, EBad3 g -> EBad3 (g ⟨e sigma ⟩).   
Proof. 
intros. elim : H sigma;intros .
simpl. con. apply/negP=>HH. move/negP : H. intros. apply/H. 
apply/eguarded_ren2.  move : HH. asimpl.  intros. 
instantiate (1 := 0 .: sigma >> succn). 
eauto. simpl. 
simpl. constructor 2.  auto.
Qed. 

Lemma ebad_subst : forall g sigma, EBad3 g -> EBad3 (g [e sigma]).   
Proof. 
intros. elim : H sigma;intros .
simpl. con. apply/negP=>HH. move/negP : H. intros. apply/H. 
apply/eguarded_subst2.  eauto. simpl. done. 
simpl. constructor 2.  auto.
Qed. 

Lemma eguarded_ebad : forall g n sigma, eguarded n g = false -> EBad3 (sigma n) -> EBad3 g [e sigma].
Proof. 
elim;intros. ssa. have : n = n0 by lia. move=>->. done. 
ssa. ssa. 
constructor 2. apply/H.  eauto. simpl. destruct n. asimpl.  
ssa. apply/ebad_ren.  done. asimpl.  apply/ebad_ren. done. 
ssa. ssa. 
Qed. 

Lemma ebad_eguarded : forall g, EBad3 g -> EBad3 (eunf g).  
Proof.
intros. elim : H;intros. 
simpl. 
destruct g0;try done. 
ssa. 
have : n = 0 by lia. move=>->. ssa. con. ssa. 
ssa. constructor 2.  
have: EBad3 (ERec (ERec g0)) ⟨e succn ⟩.
simpl. con.  ssa. asimpl. 
apply/negP=> HH. move/negP : H. intros. apply/H. apply/eguarded_ren2.
instantiate (1 := 0 .: (1 .: succn >> (succn >> succn))). 
asimpl. done. 
intros. apply/eguarded_ebad.   eauto. ssa. 
 simpl. inv H. 
ssa. con. apply/negP=>HH. move/negP : H1. 
intros. apply/H1. apply/eguarded_subst2.  eauto. simpl. done. 
asimpl. constructor 2. apply/ebad_subst.  done. 
Qed. 

Lemma ebad_eguarded_full : forall g, EBad3 g -> EBad3 (full_eunf g).  
Proof. 
intros. rewrite /full_eunf. remember (emu_height g). clear Heqn.
elim : n g H. ssa. intros. rewrite iterS.  apply/ebad_eguarded. 
apply/H.  done. 
Qed. 

Definition is_erec e := if e is ERec _ then true else false. 

Lemma ebad_rec : forall g, EBad3 g -> is_erec g. 
Proof. 
intros. inv H. 
Qed. 

Lemma cont_ebad3 : forall g, eguarded 0 g = false -> EBad3 (ERec g). 
Proof. 
elim;ssa. have : n = 0 by lia. move=>->. con. done. 
con. 
ssa. 
Qed. 


(*Destructing EBad3 when conclusion is is_erec, yields error, case analysis on sort Type not allowed, but EBad3 has type lType -> Prop*)
Lemma not_cont : forall g, ~~ lcontractive g -> lInvPred3 g. 
Proof. 
elim;try done.  
intros. ssa.  rewrite negb_and in H0. destruct (orP H0). 
 have :  is_erec (full_eunf (ERec e)).
rewrite full_eunf_subst.
have : eguarded 0 e = false. lia.
move/cont_ebad3. 
move/ebad_eguarded_full. rewrite full_eunf_subst. 
move/ebad_rec. done. 
intros. destruct (full_eunf (ERec e)) eqn:Heqn;try done. 
econstructor 3. eauto. 

apply H in H1. apply/lInv_struct.  done. 
ssa. econstructor. cbn.  done. auto. 
ssa. elim : l H H0. ssa. ssa.

rewrite negb_and in H1. destruct (orP H1). destruct a.  econstructor 2. 
cbn.  eauto. rewrite inE. apply/orP.  left. apply/eqP.  eauto. apply/H0.
done. done. 
have : lInvPred3 (EBranch d c l). apply/H. 
intros. apply/H0. instantiate (1 := n). rewrite inE H3. lia. done. done.


move=>x. inv x. move : H3. cbn. case. intros. subst. 
econstructor 2. cbn.  eauto. rewrite inE. apply/orP. right. eauto. done. 
Qed. 



Lemma lInvPred_contractive_aux : forall g, lInvPred2 g -> lcontractive g.
Proof. 
intros. destruct (lcontractive g) eqn :Heqn. done. 
have : ~~ lcontractive g. lia. move/not_cont.  intros. 
exfalso. apply/lInvPred_contractive3.  eauto. eauto. 
Qed. 



Lemma lInvPred12 : forall g, lInvPred g -> lInvPred2 g. 
Proof. 
pcofix CIH. intros. punfold H0. inv H0. pfold. con. inv H. 
con. pclearbot.  right. eauto. 
con. elim : H2. cbn. con. ssa. pclearbot.  con. ssa. done. con. 
Qed. 


Lemma lInvPred_contractive : forall g, lInvPred g -> lcontractive g.
Proof. intros. apply/lInvPred_contractive_aux. apply/lInvPred12.  done.  
Qed. 
