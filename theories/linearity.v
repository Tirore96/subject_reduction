
From mathcomp Require Import all_ssreflect zify.



Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From deriving Require Import deriving.
(*From Dep Require Export Utils. *)
Require Import MPSTSR.IndTypes.elimination.

Let inE := (inE,Bool.negb_involutive,eqxx,negb_or,negb_and).





Definition same_ch (a0 a1 : action) := action_ch a0 == action_ch a1.

Definition II (a0 a1 : action) := (ptcp_to a0 == ptcp_to a1).
Definition IO (a0 a1 : action) := (ptcp_to a0 == ptcp_from a1).
Definition OO (a0 a1 : action) := (ptcp_from a0 == ptcp_from a1) && same_ch a0 a1.
Definition IO_OO a0 a1 := IO a0 a1 || OO a0 a1. 

Inductive InDep : seq action -> Prop :=
 | ID_End a0 a1 : II a0 a1 -> InDep ([::a0; a1])
 | ID_cons a0 a1 aa: IO a0 a1 -> InDep (a1::aa) -> InDep (a0::a1::aa).
Hint Constructors InDep.



Definition indep ss := 
match ss with 
| a::a'::ss' => let: one_less := belast a' ss' in path IO a one_less && II (last a one_less) (last a' ss')
| _ => false 
end.

Lemma InDep_iff : forall ss, InDep ss <-> indep ss.
Proof.
case. split;intros;inversion H.
move => a l. case : l. split;intros;inversion H.
move => a0 l. 
elim : l a0 a. rewrite /=. move => a0 a. split;intros; inversion H;subst. done. inversion H4. auto.
move => a0 l H a1. rewrite /=. split;intros.
- inversion H0;subst. rewrite H3 /=. simpl in H. by  apply/H.
- move : H0 => /andP => [] [] /andP => [] []. intros. constructor. done. apply/H. by rewrite /= b b0.
Qed.

Inductive OutDep : seq action -> Prop :=
 | OD_end a0 a1 : IO_OO a0 a1 -> OutDep ([::a0; a1])
 | OD_cons a0 a1 aa: IO_OO a0 a1  -> OutDep (a1::aa) -> OutDep (a0::a1::aa).
Hint Constructors OutDep.


Definition outdep ss :=
match ss with 
| a::a'::ss => path IO_OO a (a'::ss)
| _ => false 
end. 

Lemma OutDep_iff : forall ss, OutDep ss <-> outdep ss.
Proof.
rewrite /outdep.
case; first (split;intros; inversion H).
move => a []; first (split;intros;inversion H).
move => a0 l. move : l a a0. elim.
- move => a a0. split; rewrite /=;intros. rewrite andbC /=. inversion H; done.
  constructor. by move : H => /andP => [] [].
- move => a l IH a0 a1. split;intros. 
 * inversion H. subst. rewrite /=. simpl in IH. rewrite H2 /=. inversion H4;subst. by rewrite H1. 
   by apply/IH. 
 * simpl in IH,H. move : H=> /andP=> [] []H0 H1. constructor;first done. by apply/IH.  
Qed.

Ltac contra_list := match goal with 
                      | H : (nil = _ ++ _) |-  _ => apply List.app_cons_not_nil in H
                      end;contradiction.





Definition exists_depP  (Pm : seq bool -> Prop) (P : seq action -> Prop) a0 aa a1 := 
     exists m, size m = size aa /\ P (a0::((mask m aa))++[::a1]) /\ Pm m.
Notation exists_dep := (exists_depP (fun _ => True)).

Notation unfg g := (g[g GRec g.:  GVar]).
Inductive Tr : seq action -> gType  -> Prop :=
| TR_nil G : Tr nil G 
| TRMsg a u aa g0 : Tr aa g0 -> Tr (a::aa) (GMsg a u g0)
| TRBranch a n gs g aa  : (n,g) \in gs -> Tr aa g ->  Tr (a::aa) (GBranch a gs)
| TRUnf aa g : Tr aa (unfg g)  -> Tr aa (GRec g).
Hint Constructors Tr.



Definition Linear (sg : gType) := 
forall aa_p a0 aa a1, 
Tr (aa_p ++ (a0::(aa++[::a1]))) sg -> 
same_ch a0 a1 -> 
exists_dep InDep a0 aa a1 /\ exists_dep OutDep a0 aa a1.

Definition slice (A : Type) (l : seq A) n0 n1 := take n1 (drop n0 l).

Lemma nth_slice : forall (A : Type) (n n0 : nat) (d : A) (s : seq A) x , n <= n0 -> n0 < size s ->  (nth d (take n s ++ x :: drop n s) n0.+1) = nth d s n0.
Proof.
intros. rewrite nth_cat size_take. have : n < size s by lia. move => Hn.  rewrite Hn. 
  have : n0.+1 < n = false by lia. move =>->. have : n0.+1 - n = (n0 - n).+1 by lia. move=>->.  rewrite /=. 
  rewrite nth_drop. f_equal. lia. 
Qed.

Definition all_indep (sg : gType) := forall s n0 n1 d,
Tr s sg -> 
same_ch (nth d s n0) (nth d s n1) -> n0 < size s -> n1 < size s ->
exists_dep InDep (nth d s n0) (slice s n0 n1) (nth d s n1).


Definition Linear1 (sg : gType) := forall aa_p a0 aa a1, 
Tr (aa_p ++ (a0::(aa++[::a1]))) sg -> 
same_ch a0 a1 -> 
exists_dep InDep a0 aa a1.

Definition Linear2 (sg : gType) := forall aa_p a0 aa a1, 
Tr (aa_p ++ (a0::(aa++[::a1]))) sg -> 
same_ch a0 a1 -> 
exists_dep OutDep a0 aa a1.

Lemma Linear_1 : forall g, Linear g -> Linear1 g.
Proof.
intros. rewrite /Linear1. intros. apply H in H0. destruct H0. done. done. Qed.

Lemma Linear_2 : forall g, Linear g -> Linear2 g.
Proof.
intros. rewrite /Linear2. intros. apply H in H0. destruct H0. done. done. Qed.



Definition insert (A : Type) (l : seq A) n x := ((take n l) ++ (x::(drop n l))).

Lemma insert0 : forall (A: Type) (l : seq A) x, insert l 0 x = x::l.
Proof. intros. by rewrite /insert take0 drop0 /=. Qed.

Lemma insert_nil : forall (A: Type) n (x : A), insert nil n x  = [::x]. 
Proof. intros. destruct n; done. Qed.


Lemma insert_cons : forall (A: Type) (l : seq A) n x a, insert (a::l) n x  = if n is n'.+1 then a::(insert l n' x) else x::a::l.
Proof. intros. destruct n.  rewrite insert0. done. rewrite /insert /=. done. Qed.

Lemma insert_cat : forall (A: Type) (l0 l1 : seq A) n x, insert (l0++l1) n x  = if n <= size l0 then (insert l0 n x)++l1 else l0++(insert l1 (n-(size l0)) x). 
Proof. move => A.  elim. rewrite /=. intros. destruct n. by rewrite insert0 /=. rewrite /=. done. 
intros. rewrite /=. rewrite insert_cons. destruct n. by rewrite /=. rewrite H /=. destruct (n < (size l).+1) eqn:Heqn. 
have : n <= size l by lia.  move=>->. f_equal. have : n <= size l = false by lia. move=>->. done. 
Qed.

Lemma size_insert : forall (A : Type) (l : seq A) n x, size (insert l n x) = (size l).+1. 
Proof. move=> A. elim;intros. by rewrite insert_nil. 
rewrite insert_cons /=. destruct n.  done. by rewrite /= H. 
Qed.


Definition delete (A : Type) (l : seq A) n := (take n l)++(drop n.+1 l).

Lemma delete_nil : forall (A: Type) (n : nat), delete (@nil A) n = nil.
Proof. intros. by rewrite /delete /=.  Qed.


Lemma delete_cons : forall (A: Type) l (a : A) n, delete (a::l) n = if n is n'.+1 then a::(delete l n') else l.
Proof. move => A. elim;intros; destruct n; rewrite /delete /=;try done. Qed.




Lemma size_delete : forall (A : Type) (l : seq A) n, size (delete l n) = if n < size l then (size l).-1 else size l.
Proof. move => A. elim;intros. rewrite delete_nil /=. destruct n;done. 
rewrite delete_cons /=. destruct n eqn:Heqn. by rifliad. 
subst. rewrite /= H. rifliad.  lia.
Qed.

Lemma delete_insert : forall (A : Type) aa n (x : A), (delete (insert aa n x) n) = if n <= size aa then aa else insert aa n x.
Proof. move => A. elim. intros. rewrite /=. destruct n. by  rewrite insert_nil delete_cons /=. 
rewrite insert_nil delete_cons delete_nil. by rifliad.  
intros. rewrite insert_cons. destruct n;rewrite /= delete_cons. done. rewrite H.
rifliad. 
Qed.

Lemma mask_delete : forall (A: Type) d n (aa : seq A) m, nth d m n = false -> mask m aa = mask (delete m n) (delete aa n).
Proof. move => A d n aa m. move : aa m d n. elim. case; try done. intros. 
rewrite /= delete_nil /= delete_cons. destruct n. by  rewrite mask0. rewrite mask0. done. 
intros. destruct m;try done. rewrite /=. destruct n. simpl in H0. subst. rewrite !delete_cons. done.
simpl in *. destruct b. f_equal. erewrite H. reflexivity.  lia. eauto. 
Qed.


Lemma insert_spec : forall (A : Type) (l : seq A) n a,  n <= size l -> exists l0 l1, l0 ++ l1 = l /\ insert l n a = l0 ++ a::l1 /\ size l0 = n.
Proof. move => A. elim. intros. exists nil,nil. rewrite insert_nil /=. destruct n;done.
intros. destruct n.  rewrite insert0. exists nil, (a::l). auto.  
rewrite insert_cons. destruct (H n a0). simpl in H0. lia. destruct H1,H1,H2. rewrite H2. rewrite -H1. exists (a::x),x0. split. by rewrite /= H1. 
rewrite /=. auto. 
Qed.


Lemma insert_delete : forall (A : Type) aa n (d : A), n < size aa -> aa = insert (delete aa n) n (nth d aa n).  
Proof.
move => A. elim. done.  
intros. rewrite delete_cons. destruct n. by  rewrite insert0 /=. rewrite insert_cons. f_equal. simpl in H0.  apply H. lia. 
Qed.

Definition label := (action * (value + nat))%type.

Coercion ptcps_of_act (a : action) := ptcp_from a :: ptcp_to a :: nil.

Canonical action_predType := PredType (fun a p => p \in ptcps_of_act a). 

(* map fst gs = map fst gs' ensures number of continuations stays the same, as well as the labels at each position*)
Inductive step : gType -> label  -> gType -> Prop :=
 | GR1 (a : action) u g :  step (GMsg a u g) (a, inl u) g
 | GR2 a n g gs : (n,g) \in gs -> step (GBranch a gs) (a, inr n) g
 | GR3 a u l g1 g2 : step g1 l g2 -> ptcp_to a \notin l.1 -> step (GMsg a u g1) l (GMsg a u g2)
 | GR4 a l gs gs' : map fst gs = map fst gs' -> (forall g g', In (g,g') (zip gs gs') -> step g.2 l g'.2) -> (ptcp_to a) \notin l.1  ->  step (GBranch a gs) l (GBranch a gs')

 | GR_rec g l g' : step (unfg g) l g'  -> 
                   step (GRec g) l g'.
Hint Constructors step. 


Lemma step_tr_in : forall g vn g', step g vn g' -> forall s, Tr s g' -> 
Tr s g \/ exists n, Tr (insert s n vn.1) g /\ Forall (fun a => (ptcp_to a) \notin vn.1) (take n s).
Proof.
move => g vn g'. rewrite /insert. elim.
- intros. right. exists 0. simpl. rewrite take0 drop0 /=.  auto. 
- intros. right. exists 0. simpl. rewrite take0 drop0 /=. eauto.  
- intros. destruct s;auto. ssa. 
  inversion H2. subst. move : (H0 _ H4)=>[];auto.
  move=> [] n [].  intros. right. exists n.+1. simpl. auto. 
- intros.  destruct s; auto.
  inversion H3. subst.
  have : exists a1, In a1 gs /\ In (a1,(n,g0)) (zip gs gs'). apply/In_zip2. apply/inP.  done. eauto. 
  case. ssa. 
  move: H1. move/(_ _ _ H5)=>/=. move/( _ _ H9).  case. intros. left. destruct x.  econ. apply/inP.  eauto. ssa. 
  case. ssa. right. exists x0.+1. 
  ssa. destruct x.  econ.  apply/inP.  eauto. ssa. 
- intros. destruct (@H0 _ H1). left. destruct s.   done. constructor. done.
  destruct H2. right. exists x. destruct H2. split;auto.
Qed.


Lemma Tr_app : forall (G : gType) l0 l1, Tr (l0++l1) G -> Tr l0 G.
Proof.
intros.  remember (l0 ++ l1). elim : H l0 l1 Heql ;intros.  destruct l0;done. 

destruct l0. done. rewrite cat_cons in Heql. inversion Heql. subst. eauto.  
destruct l0. done. rewrite cat_cons in Heql. inversion Heql. subst.
apply : TRBranch;  eauto. constructor. eauto.  
Qed.


Lemma take_cat2
     : forall (n0 : nat) (T : Type) (s1 s2 : seq T),
       take n0 (s1 ++ s2) = (if n0 <= size s1 then take n0 s1 else s1 ++ take (n0 - size s1) s2).
Proof.
intros. rewrite take_cat. rifliad. rifliad. lia.   have : n0 = size s1 by lia. move=>->. have : size s1 - size s1 = 0 by lia.  move=>->. rewrite take0 cats0. by  rewrite take_size. 
Qed.

Lemma drop_cat2 
     : forall (n0 : nat) (T : Type) (s1 s2 : seq T),
       drop n0 (s1 ++ s2) = (if n0 <= size s1 then drop n0 s1 ++ s2 else drop (n0 - size s1) s2).
Proof. intros. rewrite drop_cat. rifliad. rifliad. lia.  have : n0 = size s1 by lia. move=>->. have : size s1 - size s1 = 0 by lia. move=>->. rewrite drop0. rewrite drop_oversize //=. 
Qed.


Lemma split_mask : forall (A : Type) (l0 : seq A) x l1 m, size m = size (l0++x::l1) ->
mask m (l0 ++ (x :: l1)) =
  mask (take (size l0) m) l0 ++ (nseq (nth false m (size l0)) x) ++ mask (drop (size l0).+1 m) l1.
Proof.
move => A. elim. 
- rewrite /=. intros. rewrite take0 /=. case : m H. done. 
  intros. by  rewrite mask_cons /= drop0. 
- rewrite /=. intros. case : m H0.  done. rewrite /=. intros. 
  case : a0. rewrite cat_cons. f_equal. rewrite H //=. lia. 
  rewrite H //=. lia.
Qed.

Definition IO_II a0 a1 := IO a0 a1 || II a0 a1.

Lemma indep0 : forall l0 l1, indep (l0 ++ l1) -> if l0 is x::l0' then path IO_II x l0' else true.
Proof.
move => l0 l1. rewrite /indep.
case :l0 ;first done.
move => a l. rewrite /=. case : l;first done.
move => a0 l. rewrite /=. move/andP=> [] H H1. elim : l a a0 H H1.
- move => a a0. rewrite /=.  case : l1. simpl. rewrite /IO_II. move => _ -> . by rewrite orbC.  
  move => a1 l. rewrite/= /IO_II. by move/andP=> [] ->.
- move => a l IH a0 a1. rewrite /= /IO_II. move/andP=> [] ->. intros. rewrite /=.   unfold IO_II in IH. apply/IH. done. done.
Qed.

Lemma outdep0 : forall l0 l1, outdep (l0 ++ l1) -> if l0 is x::l0' then path IO_OO x l0' else true.
Proof.
rewrite /outdep. case;first done. 
move => a l l1. rewrite cat_cons. case : l;first done.  
move => a0 l. rewrite cat_cons. rewrite -cat_cons. rewrite cat_path. by move/andP=>[]. 
Qed.


Lemma IO_in_action : forall a0 (l : action), IO a0 l -> (ptcp_to a0) \in l.
Proof.
move => a0 a1. rewrite /IO.  rewrite /IO. move/eqP=>->. by rewrite !inE. 
Qed.

Lemma II_in_action : forall a0 (l : action), II a0 l -> (ptcp_to a0) \in l.
Proof.
move => a0 a1. rewrite /II.  move/eqP=>->. rewrite !inE. lia. 
Qed.


Lemma IO_II_in_action : forall a0 (l : action), IO_II a0 l -> (ptcp_to a0) \in l.
Proof.
move => a0 a1. rewrite /IO_II. move/orP=>[]; auto using IO_in_action, II_in_action. 
Qed.


Lemma InDep_insert : forall a0 aa a1 n x,  n <= size aa -> Forall (fun a : action => ptcp_to a \notin x) (take n aa) -> ptcp_to a0 \notin x -> exists_dep InDep a0 (insert aa n x) a1 -> exists_dep InDep a0 aa a1.
Proof. 
intros. destruct H2,H2,H3,H4. have : n < size x0.  rewrite size_insert in H2. rewrite H2. lia. 
move=> H4. destruct (nth false x0 n == false) eqn:Heqn. 
- move : (eqP Heqn)=>HH. move : H3. rewrite (@mask_delete _ false n (insert aa n x)) //=. rewrite !delete_insert.  rifliad. 
 intros. exists (delete x0 n). rewrite size_delete.  rifliad. rewrite H2 size_insert /=. auto. 
- have : nth false x0 n = true by lia. clear Heqn. move => Heqn. 
  destruct (@insert_spec _ aa n x H).  destruct H5,H5,H6. move : H3. rewrite H6 split_mask; last (rewrite size_cat /= H2 size_insert -H5 size_cat; lia).
  rewrite H7 Heqn /=. 
   have : (a0 :: (mask (take n x0) x1 ++ x :: mask (drop n.+1 x0) x2) ++ [:: a1]) = 
          ((a0 :: (mask (take n x0) x1 ++ [::x])) ++ ((mask (drop n.+1 x0) x2) ++ [:: a1])). 
   rewrite -!catA. rewrite !cat_cons /=. rewrite !catA. f_equal.  rewrite -!catA. f_equal. move=>->.
 move/InDep_iff. move/indep0.

   rewrite cat_path /=. move/andP=>[] _. rewrite andbC /=.  destruct (mask (take n x0) x1) eqn:Heqn4. 
 * rewrite /=. move/IO_II_in_action. move => HH.  rewrite HH in H1. done. 
 * rewrite /=. intros. have : (last a l) \in (take n aa).  rewrite -H5 take_cat. rifliad.  lia. 
   rewrite mem_cat. 
   apply/orP. left. eapply mem_mask with (m:= (take n x0)).  rewrite Heqn4.  by rewrite mem_last.  

   move : H0. rewrite List.Forall_forall.  intros.  apply In_in in x3. apply H0 in x3. apply IO_II_in_action in b. rewrite b in x3. done. 
Qed.

Lemma ind_aux : forall l a a0, path IO a (belast a0 l) -> II (last a (belast a0 l)) (last a0 l) -> IO_II a a0 && path IO_II a0 l.
Proof.
 elim.
- move => a a0.  rewrite /= /IO_II. move => _ ->.  by rewrite orbC.
- move => a l IH a0 a1. rewrite /=. move/andP=>[].  intros. rewrite /IO_II a2 /=.
  unfold IO_II in IH. apply/IH. done. done. 
Qed.

Lemma indep1 : forall l0 l1, indep (l0 ++ l1) -> if l1 is x::l1' then path IO_II x l1' else true.
Proof.
case. simpl. case. done. rewrite /=. move => a []. done.
move => a0 l. rewrite /=. intros. move : H. move/andP=>[]. intros. apply/ind_aux. done. done. 
- move => a l l1. rewrite /=. case : l. rewrite /=. case : l1. done.
  intros. move : H=> /andP=> [] []. intros. move : (ind_aux a1 b). by move/andP=>[].
- move => a0 l. rewrite /=. move/andP=> []. intros. case : l1 a1 b. done. 
intros. move : (ind_aux a2 b). move/andP=> []. rewrite cat_path. move => _ /andP => [] []. 
  rewrite /=. move => _ /andP => [] []. done. 
Qed.

Lemma last_eq : forall A (l0 l1 : seq A) x0 x1, l0 ++ ([::x0]) = l1 ++ ([::x1]) -> l0 = l1 /\ x0 = x1.
Proof.
move => A. elim.
case. rewrite /=. move => x0 x1. case. done.
move => a l x0 x1. rewrite /=. case. move =>-> H. apply List.app_cons_not_nil in H. done. 
rewrite /=. intros. case : l1 H0.  rewrite /=. case. move => _ /esym H1. apply List.app_cons_not_nil in H1. done. 
intros. move : H0.  rewrite cat_cons. case. intros. move : (H _ _ _ H1). case. intros. split. subst. done. done. 
Qed.



Lemma split_list : forall A (l : seq A), l = nil \/ exists l' a, l = l'++([::a]).
Proof.
move => A. elim.
auto.  move => a l [] . move =>->. right.  exists nil. exists a. done. 
move => [] l' [] a0 ->. right. exists (a::l'). exists a0. done.
Qed.


Lemma no_indep : forall a0 l a1, (ptcp_to a0) \notin a1 -> Forall (fun a : action => ptcp_to a \notin a1) l -> exists_dep InDep a0 l a1 -> False.
Proof.
intros. destruct H1,H1,H2,H3. move : H2. move/InDep_iff. rewrite /=.  destruct (mask x l ++ [:: a1]) eqn :Heqn. destruct (mask x l). done. done. rewrite Heqn. 
move/andP=>[]. intros. have : last a l0 = a1.  destruct (split_list l0).  subst. destruct (mask x l). simpl in Heqn. inversion Heqn. done. simpl in Heqn. inversion Heqn. destruct l0;done. destruct H2,H2. rewrite H2. rewrite last_cat. simpl. rewrite H2 in Heqn. rewrite -cat_cons in Heqn. apply last_eq in Heqn. destruct Heqn. done. 
intros.  rewrite x0 in b. (* have : (last a0 (belast a l0)) \in l. apply mem_mask with (m := x). *)
destruct (split_list (mask x l)). rewrite H2 in Heqn.    simpl in Heqn. destruct l0;try done. inversion Heqn. subst. simpl in *. 
apply II_in_action in b. rewrite b in H.  done. 
destruct H2,H2. rewrite H2 in Heqn. have : belast a l0 = x1 ++ [:: x2].  destruct (split_list l0). subst. simpl in *. rewrite -catA in Heqn.  destruct x1; try done. simpl in Heqn. inversion Heqn. destruct x1;done. destruct H3. destruct H3. rewrite H3 belast_cat /=. rewrite -cat_rcons. rewrite -lastI cats0. rewrite H3 in Heqn. rewrite -cat_cons in Heqn. 
apply last_eq in Heqn. destruct Heqn. done. intros. rewrite x3 in b. rewrite last_cat in b. simpl in b.  
have : x2 \in l. apply mem_mask with (m:= x). rewrite H2. by rewrite mem_cat inE eqxx orbC. 
move/In_in. move : H0. move/List.Forall_forall. move=> Hf.  move/Hf=>Hp. apply II_in_action in b. rewrite b in Hp. done. 
Qed.

Lemma  mask_take: forall (A : Type) (l : seq A) m, mask (take (size l) m) l = mask m l.
Proof.
move => A. elim. intros. by rewrite /= take0 !mask0.
intros. rewrite /=. destruct m.  simpl. done. rewrite /=. destruct b. f_equal. done. done.
Qed.

Lemma size_mask' : forall (A : eqType) (l : seq A) (m : bitseq)  x, x \in (mask m l) -> exists l0 l1, l = l0++(x::l1).  
Proof.
move => A. elim. intros. rewrite mask0 in H. done.
intros. move : H0. destruct m.  rewrite mask0s.  done. simpl. destruct b. 
rewrite /=. rewrite inE. move/orP=>[]. move/eqP=>->. exists nil,l. done. 
move/H=>[] x0 [] x1 ->. exists (a::x0),x1. done. 
move/H=> [] x0 [] x1 ->. exists (a::x0),x1. done. 
Qed.


Lemma get_neigbor : forall (P : action -> action -> bool) a p x_end m, path P a ((mask m p)++[::x_end]) -> exists x_in, x_in \in (a::p) /\ P x_in x_end. 
Proof. 
intros. 
case : (split_list (mask m p)) H. move =>->. rewrite /= andbC /=. intros. exists a. by rewrite inE eqxx /=.
move => [] l' [] a0 Heqa2.  move : (Heqa2) =>->. rewrite -catA. rewrite cat_path /=.
move/andP=> [] _ /andP => [] [] _. rewrite andbC /=. move => HH.
have : a0 \in a::p. rewrite inE.  apply/orP. right. apply (@mem_mask _ _  m). 
rewrite Heqa2. by rewrite mem_cat inE eqxx orbC. 
intros. exists a0. by rewrite x. 
Qed.

Lemma in_split : forall (A : eqType) l (x : A), x \in l -> exists l0 l1, l = l0 ++ x::l1.
Proof.
move => A. elim. done.
move => a l IH x. rewrite inE. move/orP=>[]. move/eqP=>->. exists nil. exists l. done. move/IH=> [] l0 [] l1 ->. exists (a::l0),l1. done. 
Qed. 



Lemma ch_diff : forall g a0 aa a1, Linear g -> Tr (a0::(aa++[::a1])) g  -> Forall ( fun a => (ptcp_to a) \notin a1) (a0::aa) ->  Forall (fun a => action_ch a != action_ch a1) (a0::aa).
Proof.
intros. apply/List.Forall_forall. intros. 
destruct (eqVneq (action_ch x) (action_ch a1)); last done. inversion H1. subst.
exfalso. simpl in H2. destruct H2. 
- subst. apply : no_indep. apply : H5.  apply H6. move : H. move/Linear_1=>HH.  apply : HH. 
  rewrite -[_::_]cat0s in H0. apply : H0. rewrite /same_ch. apply/eqP. done.
- apply List.in_split in H2.  destruct H2,H2. rewrite H2 in H0. rewrite /Linear in H.
  specialize H with (a0::x0) x x1 a1. 
have : (a0 :: (x0 ++ (x :: x1)%SEQ)%list ++ [:: a1]) = ((a0 :: x0) ++ x :: x1 ++ [:: a1]).
  rewrite /=. f_equal. rewrite -catA. f_equal.


  intros. move : H0.  rewrite x2. move/H=>H3. 
  have : same_ch x a1. by rewrite /same_ch e. move/H3. case. intros. move : H1.  
  rewrite H2. intros. inversion H1. apply List.Forall_app in H8. destruct H8. inversion H9. apply : no_indep. 
  apply H12.  apply H13.  done.
Qed.



(*Shorten proof by using distinct_ch*)
Open Scope nat_scope.
Lemma Linear_step  : forall g l g', step g l g' ->  Linear g -> Linear g'.
Proof.
intros. rewrite /Linear. intros. move : (step_tr_in H H1)=>[]. intros. eauto.  
move => [] n [] Htr Hf. move : Htr. rewrite insert_cat.
destruct (n <= size aa_p) eqn:Heqn;eauto. 
rewrite insert_cons. destruct (n - size aa_p) eqn:Heqn2. 
have : (aa_p ++ [:: l.1, a0 & aa ++ [:: a1]]) = ((aa_p ++ [:: l.1])++ a0::aa ++ [:: a1]). by rewrite -catA /=.
move=>->. eauto. 
rewrite insert_cat. destruct (n0 > size aa) eqn:Heqn3.
have : n0 <= size aa = false by lia. move=>->. 
rewrite insert_cons. destruct (n0 - size aa) eqn:Heqn4. lia. rewrite insert_nil.
have : aa_p ++ a0 :: aa ++ [:: a1; l.1] = (aa_p ++ a0 :: aa ++ [:: a1]) ++ [::l.1]. rewrite -!catA !cat_cons. f_equal. f_equal. rewrite -catA. f_equal. move=>->. eauto. move/Tr_app.  intros. eauto. 
have : n0 <= size aa by lia. move=>->. intros. (*setup finished*)
move : (H0 _ _ _ _ Htr H2)=>Hlin.
move : Hf. have : n = n0.+1 + (size aa_p) by lia. move=>->. rewrite take_cat.
have :  n0.+1 + size aa_p < size aa_p = false by lia. move=>->. rewrite /=.
have : (n0.+1 + size aa_p - size aa_p) = n0.+1  by lia. move=>->.
rewrite /=. rewrite take_cat2. have : n0 <= size aa by lia. move=>->. rewrite -cat1s catA.  
move/List.Forall_app=>[] /List.Forall_app=> [] [] HH0 HH1 HH2.  have : n0 <= size aa by lia.  intros. 
split. 
- apply : InDep_insert. apply : x. eauto. inversion HH1. done. apply Linear_1 in H0.  eauto. 
- destruct Hlin. destruct H4,H4,H5,H6. have : n0 < size x0.  rewrite size_insert in H4. rewrite H4. lia. 
  
  move=> HH4. destruct (nth false x0 n0 == false) eqn:Heqn4. 
- move : (eqP Heqn4)=>HH. move : H5. rewrite (@mask_delete _ false n0 (insert aa n0 l.1)) //=. rewrite delete_insert. rifliad.  intros. exists (delete x0 n0). rewrite size_delete.  rifliad. rewrite H4 size_insert /=. split;auto.  

- have : nth false x0 n0 = true by lia. clear Heqn. move => Heqn. 
  destruct (@insert_spec _ aa n0 l.1 x).  destruct H6,H6,H7.  move : H5. rewrite H7 split_mask; last  (rewrite size_cat /= H8 H4 size_insert -H6 size_cat;  lia).
  rewrite H8. rewrite Heqn /=. move/OutDep_iff. 
  have : (a0 :: (mask (take n0 x0) x1 ++ l.1 :: mask (drop n0.+1 x0) x2) ++ [:: a1]) = 
         (a0 :: mask (take n0 x0) x1 ++ [::l.1]) ++ ((mask (drop n0.+1 x0) x2) ++ [:: a1]).
  rewrite -!catA cat_cons /=. f_equal. rewrite -catA. f_equal. move=>->.
 move/outdep0.
  move/get_neigbor=>[] xin []. intros.
  
rewrite /IO_OO in b. case : (orP b).

 *  intros.  exfalso. move : a.  rewrite inE. move/orP=>[]. 
  ** move/eqP=>HHeq. inversion HH1. apply : negP. apply H10. apply/IO_in_action. rewrite -HHeq. done. 
  **  rewrite -H6 in HH2. move : HH2. rewrite take_cat. rifliad. lia.
      move/List.Forall_app=>[]. move/List.Forall_forall=> Hf _. intros.  apply/negP. apply : Hf. apply/In_in. apply : b0. apply/IO_in_action. done. 
 *  rewrite /OO. move/andP=> [] /eqP _ HHH0. 
     move : (in_split a)=> [] l1 [] l2 Heq0.
    move : Htr.  rewrite H7. rewrite -!cat_cons. rewrite Heq0.
    have :  (aa_p ++ ((l1 ++ xin :: l2) ++ l.1 :: x2) ++ [:: a1]) =
            ((aa_p ++ l1) ++ (xin::l2 ++ [:: l.1]))++(x2++[::a1]).
    rewrite -!catA; f_equal. f_equal. rewrite /=. f_equal.  rewrite -catA.  f_equal. move=>->.
    move/Tr_app. 
   move/H0. move => HH'. apply HH' in HHH0. destruct HHH0. 
   destruct H5,H5,H10,H11. apply InDep_iff in H10. move : H10.
     case : (split_list (mask x3 l2)). move=>->. rewrite /=.  move/II_in_action=>HII.   exfalso. move : a. rewrite inE.  move/orP=>[].
  **  move/eqP=> HHeq'. inversion HH1. apply : negP. apply H12. rewrite -HHeq'. done. 
  ** intros. rewrite -H6 in HH2. move : HH2. rewrite take_cat. rifliad. lia.
      move/List.Forall_app=>[]. move/List.Forall_forall=> Hf _. intros.  apply/negP. apply : Hf. apply/In_in. apply : b0. done. 
 * move=> [] l' [] a2 HHeq'. rewrite HHeq'.
     rewrite  -!catA -cat_cons. move/indep1. rewrite /= andbC /=. move/IO_II_in_action=> Hia.  exfalso. 
     move : HH2. rewrite -H6. rewrite take_cat. rifliad. lia.
      move/List.Forall_app=>[]. move/List.Forall_forall=> Hf _. apply : negP. apply : Hf. apply/In_in. 2: { apply : Hia. } 
    
       destruct l1.  simpl in Heq0.  inversion Heq0.  eapply mem_mask with (m:= x3). rewrite HHeq'. by rewrite mem_cat inE eqxx orbC. simpl in Heq0. 
inversion Heq0. rewrite mem_cat.  apply/orP. right. rewrite inE. apply/orP. right. eapply mem_mask with (m:=x3). rewrite HHeq'. by  rewrite mem_cat inE eqxx orbC. 
Qed.





Lemma linear_sgmsg : forall a u g0, Linear (GMsg a u g0) -> Linear g0.
Proof. 
move => a u g0. rewrite /Linear /=.  intros. move : (H (a::aa_p) a0 aa a1). rewrite cat_cons /=. 
  destruct ( aa_p ++ a0 :: rcons aa a1) eqn:Heqn. case : aa_p H0 Heqn.  done. done.
  intros. have : Tr ((a::aa_p ++ (a0::aa) ++ [::a1])) (GMsg a u g0). auto.  move/H2 => H3.  move : (H3 H1). 
  move => [] mi [] mo. intros. auto. 
Qed.

Lemma linear_branch_aux : forall a gs, Linear (GBranch a gs) -> Forall (Linear \o snd) gs.  
Proof.
move => a gs. intros. apply/List.Forall_forall. intros. rewrite /Linear. cbn. intros. unfold Linear in H. have : Tr (a::aa_p ++ a0::aa ++ ([::a1])) (GBranch a gs). move : H0.  move/In_in.

move => HH. destruct x. econ. eauto. ssa. 
rewrite -cat_cons.
move/H. move=>HH. apply/HH. ssa.
Qed.


Lemma linear_branch : forall a gs g, Linear (GBranch a gs) -> g \in  gs -> Linear g.2.
Proof. intros. apply linear_branch_aux in H. move : H. move/Forall_forall=> HH. apply/HH.   done. 
Qed.


Lemma linear_unf : forall g, Linear (GRec g) ->  Linear (unfg g).
Proof.  
move => g. rewrite /Linear. move => HH aap a0 aa a1 H0 H1.  apply : HH. constructor. eauto. done. 
Qed.


Lemma size_pred_subst_ren : forall g sigma, size_pred g -> size_pred (g ⟨g sigma⟩).
Proof.  
elim;intros;rewrite /=;simpl in *;try done;auto. split_and. rewrite size_map //=.
rewrite all_map. apply/allP=>g HH.  simpl. destruct g. ssa. apply/H. eauto. 
move : (allP H2). move/(_ _ HH). ssa.
Qed.

Lemma size_pred_subst : forall g sigma, (forall x, size_pred (sigma x)) -> size_pred g -> size_pred (g[g sigma]).
Proof.  
elim;intros;rewrite /=;simpl in *;try done;auto.
- rifliad. rifliad. simpl. asimpl.   apply H. intros. destruct x. asimpl. done. asimpl. 
apply/size_pred_subst_ren. auto. done.
- rewrite all_map. split_and. rewrite size_map. split_and. apply/allP=> ll Hin /=. destruct ll. ssa. apply/H. eauto. 
  done. move: (allP H3). move/(_ _ Hin). ssa. 
Qed.


Lemma step_tr : forall g vn g', step g vn g' -> size_pred g ->  exists s, Tr (s ++ [::vn.1]) g /\ Forall (fun a => (ptcp_to a) \notin vn.1) s.
Proof.
move => g vn g'. elim.
- intros. exists nil. rewrite /=. auto.
- intros. exists nil. rewrite /=. split;auto.  econ. eauto. con.  
- intros.  simpl in H2. apply H0 in H2. destruct H2,H2.  exists (a::x). rewrite /=. auto. 
- intros. ssa.  destruct gs;ssa. destruct gs';try done. ssa. 
  move : (H1 p p0). intros. edestruct H5. auto. done. ssa. 
  exists (a::x). ssa. econ. 2 : eauto. rewrite inE. apply/orP. left. apply/eqP. instantiate (1 := p.1). destruct p. ssa. 
- intros.  simpl in H1. eapply size_pred_subst in H1.  apply H0 in H1. destruct H1,H1. exists x. split;auto. case. done. done. 
Qed. 

Definition get_act g := 
match g with 
| GMsg a _ _ => Some a
| GBranch a _ => Some a 
| GRec g' => None 
| _ => None 
end. 

(*Convenient lemma for translating glboal type condition for async communication to its counterpart in endpoint semantics
 i.e (ptcp_to a) \notin l.1 to (action_ch a) != action_ch l.1  *)
Lemma distinct_ch : forall g l g' a, get_act g = Some a -> size_pred g -> Linear g -> step g l g' -> (ptcp_to a) \notin l.1 -> 
 (action_ch a) <> (action_ch l.1).
Proof. 
intros. 
edestruct (step_tr). eauto. done.  
destruct x. simpl in H4. destruct H4. have : l.1 = a. 

inversion  H4;subst;simpl in H;try (inversion H; done). 
intros. rewrite x in H3. move : H3. rewrite !inE. ssa. 
destruct H4. simpl in H4. 
have : a0 = a. destruct g; try done. simpl in H. inversion H. subst. inversion H4. done. 
simpl in H. inversion H. subst. inversion H4. done. 
intros. subst. 
apply ch_diff in H4. inversion H4. subst. apply/eqP. done. done. done. 
Qed.

Lemma distinct_ch2 : forall g l g' a, get_act g = Some a -> size_pred g -> Linear g -> step g l g' ->  (action_ch a) = (action_ch l.1) -> (ptcp_to a) \in l.1.
Proof. 
intros. destruct (ptcp_to a \in l.1) eqn:Heqn. con. move/negbT : Heqn.  move/distinct_ch.
move=>HH.  exfalso. apply/HH;eauto.
Qed. 
