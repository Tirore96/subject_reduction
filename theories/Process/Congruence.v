From mathcomp Require Import all_ssreflect zify.
Require Import MPSTSR.Projection.intermediateProj MPSTSR.Projection.projectDecide MPSTSR.Projection.indProj. 
Require Import MPSTSR.CoTypes.coLocal. 

Require Import MPSTSR.IndTypes.elimination.
Require Import MPSTSR.harmony MPSTSR.linearity. 
Require Import  MPSTSR.Process.processSyntax.
From Paco Require Import paco. 
Require Import MPSTSR.Process.env.
Require Import MPSTSR.Process.preds. 
From deriving Require Import deriving.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation sids := (shift >> ids).  
Notation shift_sch  := (fun P => subst_process ids ids (sids) ids P). 
Notation shift_val := (fun P => subst_process (sids) ids ids ids P).

Let pheqs := preds.pheqs.

Ltac solve_ph := match goal with 
                 | |- _ => preds.solve_ph
                 | |- _ => rewrite !pheqs;intros;fext;intros;lia 
                 end. 





Definition val_indDef := [indDef for val_rect].
Canonical val_indType := IndType val val_indDef.

Definition val_eqMixin := [derive eqMixin for val].
Canonical val_eqType := EqType val val_eqMixin.


Definition valBool_indDef := [indDef for valBool_rect].
Canonical valBool_indType := IndType valBool valBool_indDef.

Definition valBool_eqMixin := [derive eqMixin for valBool].
Canonical valBool_eqType := EqType valBool valBool_eqMixin.

Definition schl_indDef := [indDef for schl_rect].
Canonical schl_indType := IndType schl schl_indDef.

Definition schl_eqMixin := [derive eqMixin for schl].
Canonical schl_eqType := EqType schl schl_eqMixin.

Definition sch_indDef := [indDef for sch_rect].
Canonical sch_indType := IndType sch sch_indDef.

Definition sch_eqMixin := [derive eqMixin for sch].
Canonical sch_eqType := EqType sch sch_eqMixin.

Definition schli_indDef := [indDef for schli_rect].
Canonical schli_indType := IndType schli schli_indDef.

Definition schli_eqMixin := [derive eqMixin for schli].
Canonical schli_eqType := EqType schli schli_eqMixin.


Definition exp_indDef := [indDef for exp_rect].
Canonical exp_indType := IndType exp exp_indDef.

Definition exp_eqMixin := [derive eqMixin for exp].
Canonical exp_eqType := EqType exp exp_eqMixin.

Definition msg_indDef := [indDef for msg_rect].
Canonical msg_indType := IndType msg msg_indDef.

Definition msg_eqMixin := [derive eqMixin for msg].
Canonical msg_eqType := EqType msg msg_eqMixin.

Definition msgp_indDef := [indDef for msgp_rect].
Canonical msgp_indType := IndType msgp msgp_indDef.

Definition msgp_eqMixin := [derive eqMixin for msgp].
Canonical msgp_eqType := EqType msgp msgp_eqMixin.

Fixpoint proc_eqb (P P' : process) := 
match P, P' with 
| SessReq a b q P0,  SessReq a' b' q' P0' => ((a,b,q) == (a',b',q')) && (proc_eqb P0 P0')
| SessAcc a b P0,  SessAcc a' b' P0' =>  ((a,b) == (a',b')) && (proc_eqb P0 P0')
| ValSend a b c P0, ValSend a' b' c' P0' =>  ((a,b,c) == (a',b',c')) && (proc_eqb P0 P0')
| ValRec a b P0,  ValRec a' b' P0' =>  ((a,b) == (a',b')) && (proc_eqb P0 P0')
| SessDel a b c P0, SessDel a' b' c' P0' => ((a,b,c) == (a',b',c')) && (proc_eqb P0 P0')
| SessRec a b P0, SessRec a' b' P0' =>  ((a,b) == (a',b')) && (proc_eqb P0 P0')
| LabelSel a b c P0, LabelSel a' b' c' P0' =>  ((a,b,c) == (a',b',c')) && (proc_eqb P0 P0')
| LabelBr a b Ps, LabelBr a' b' Ps' =>  ((a,b) == (a',b')) && (list_eq (fun a b => (a.1 == b.1) && (proc_eqb a.2 b.2))  Ps Ps')
| If a P0 P1,  If a' P0' P1' => (a == a') && (proc_eqb P0 P0') && (proc_eqb P1 P1')
| Par P0 P1, Par P0' P1' => (proc_eqb P0 P0') && (proc_eqb P1 P1')
| Inact,Inact => true 
| ResCh P0, ResCh P0' => (proc_eqb P0 P0')
| ResVal P0, ResVal P0' => (proc_eqb P0 P0')
| PCall a b c, PCall a' b' c' =>  ((a,b,c) == (a',b',c'))
| MsgQ a b, MsgQ a' b' =>  ((a,b) == (a',b'))
| _,_ => false
end. 

Definition process_rect2 := 
fun (Plist : seq (nat * process) -> Type) (P : process -> Type) (f : forall (v : valBool) (n : fin) q (p : process), P p -> P (SessReq v n q p))
  (f0 : forall (v : valBool) (p : ptcp) (p0 : process), P p0 -> P (SessAcc v p p0)) (f1 : forall (s : sch) (i : index) (e : exp) (p : process), P p -> P (ValSend s i e p))
  (f2 : forall (s : sch) (i : index) (p : process), P p -> P (ValRec s i p)) (f3 : forall (s : sch) (i : index) (s0 : sch) (p : process), P p -> P (SessDel s i s0 p))
  (f4 : forall (s : sch) (i : index) (p : process), P p -> P (SessRec s i p)) (f5 : forall (s : sch) (i : index) (l : label) (p : process), P p -> P (LabelSel s i l p))
  (f6 : forall (s : sch) (i : index) (l : seq (fin * process)), Plist l -> P (LabelBr s i l)) (f7 : forall (e : exp) (p : process), P p -> forall p0 : process, P p0 -> P (If e p p0))
  (f8 : forall p : process, P p -> forall p0 : process, P p0 -> P (Par p p0)) (f9 : P Inact) (f10 : forall p : process, P p -> P (ResCh p))
  (f11 : forall p : process, P p -> P (ResVal p)) (f12 : forall (d : defIndex) (e : exp) (l : seq sch), P (PCall d e l))
  (f13 : forall (s : schli) (l : seq msgp), P (MsgQ s l))
  (f14 :  Plist nil)
  (f15 : forall n p, P p -> forall ps, Plist ps -> Plist ((n,p)::ps))
 =>

fix F (p : process) : P p :=
  let Flist := fix Flist (ps : seq (nat * process)) : Plist ps := 
   match ps with  
    | nil => f14
    | (n,p)::ps' => @f15 n p (F p) ps' (Flist ps')
   end in 
  match p as p0 return (P p0) with
  | SessReq v n q p0 => f v n q p0 (F p0)
  | SessAcc v p0 p1 => f0 v p0 p1 (F p1)
  | ValSend s i e p0 => f1 s i e p0 (F p0)
  | ValRec s i p0 => f2 s i p0 (F p0)
  | SessDel s i s0 p0 => f3 s i s0 p0 (F p0)
  | SessRec s i p0 => f4 s i p0 (F p0)
  | LabelSel s i l p0 => f5 s i l p0 (F p0)
  | LabelBr s i l => @f6 s i l (Flist l)
  | If e p0 p1 => f7 e p0 (F p0) p1 (F p1)
  | Par p0 p1 => f8 p0 (F p0) p1 (F p1)
  | Inact => f9
  | ResCh p0 => f10 p0 (F p0)
  | ResVal p0 => f11 p0 (F p0)
  | PCall d e l => f12 d e l
  | MsgQ s l => f13 s l
  end.


Lemma process_ind2 :
 forall P : process -> Prop,
       (forall (v : valBool) (n : fin) q (p : process), P p -> P (SessReq v n q p)) ->
       (forall (v : valBool) (p : ptcp) (p0 : process), P p0 -> P (SessAcc v p p0)) ->
       (forall (s : sch) (i : index) (e : exp) (p : process), P p -> P (ValSend s i e p)) ->
       (forall (s : sch) (i : index) (p : process), P p -> P (ValRec s i p)) ->
       (forall (s : sch) (i : index) (s0 : sch) (p : process), P p -> P (SessDel s i s0 p)) ->
       (forall (s : sch) (i : index) (p : process), P p -> P (SessRec s i p)) ->
       (forall (s : sch) (i : index) (l : label) (p : process), P p -> P (LabelSel s i l p)) ->
       (forall s (i : index) (l : seq (nat * process)), ForallT (P \o snd) l -> P (LabelBr s i l)) ->
       (forall (e : exp) (p : process), P p -> forall p0 : process, P p0 -> P (If e p p0)) ->
       (forall p : process, P p -> forall p0 : process, P p0 -> P (Par p p0)) ->
       P Inact ->
       (forall p : process, P p -> P (ResCh p)) ->
       (forall p : process, P p -> P (ResVal p)) ->
       (forall (d : defIndex) (e : exp) (l : seq sch), P (PCall d e l)) -> (forall (s : schli) (l : seq msgp), P (MsgQ s l)) -> forall p : process, P p.
Proof. 
intros. eapply process_rect2;eauto. con. intros. con. done. done. 
Qed. 

Lemma process_axiom : Equality.axiom proc_eqb. 
Proof. 
intro. intros. destruct (proc_eqb x y) eqn:Heqn. con.  
elim/process_ind2 : x y Heqn.  
8 : { ssa. destruct y; ssa; try done.
- move/eqP : H. case. intros. subst. f_equal. 
  elim : l l0 H0 X. case=>//=. move => a l IH [] //=. ssa. f_equal. inv X. ssa. destruct a. destruct a0. ssa. f_equal. lia. inv X. ssa. inv X.  ssa. }
all : try solve [ intros;ssa;destruct y;try done; ssa;move/eqP : H0;case;intros; subst; f_equal;auto].
- intros. destruct y;ssa. f_equal. apply/eqP. done. auto. auto.
- intros. destruct y;ssa. f_equal. ssa. ssa.
- intros. destruct y;ssa. f_equal. ssa. 
- intros. destruct y;ssa. f_equal. ssa. 
- intros. destruct y;ssa. move/eqP : Heqn. case. intros. subst. f_equal.
- intros. destruct y;ssa. move/eqP : Heqn. case. intros. subst. f_equal.
con. intro.  subst. move/negP : Heqn. intro. apply Heqn. 
clear Heqn. elim/process_ind2 : y;ssa. 
elim : X. done. ssa. 
Qed. 
Definition process_eqMixin := EqMixin process_axiom.
Global Canonical process_eqType := EqType process process_eqMixin.
Lemma process_ind
     :  forall P : process -> Prop,
       (forall (v : valBool) (n : fin) q (p : process), P p -> P (SessReq v n q p)) ->
       (forall (v : valBool) (p : ptcp) (p0 : process), P p0 -> P (SessAcc v p p0)) ->
       (forall (s : sch) (i : index) (e : exp) (p : process), P p -> P (ValSend s i e p)) ->
       (forall (s : sch) (i : index) (p : process), P p -> P (ValRec s i p)) ->
       (forall (s : sch) (i : index) (s0 : sch) (p : process), P p -> P (SessDel s i s0 p)) ->
       (forall (s : sch) (i : index) (p : process), P p -> P (SessRec s i p)) ->
       (forall (s : sch) (i : index) (l : label) (p : process), P p -> P (LabelSel s i l p)) ->
       (forall s (i : index) (l : seq (nat * process)), (forall P', P' \in l -> P P'.2) -> P (LabelBr s i l)) ->
       (forall (e : exp) (p : process), P p -> forall p0 : process, P p0 -> P (If e p p0)) ->
       (forall p : process, P p -> forall p0 : process, P p0 -> P (Par p p0)) ->
       P Inact ->
       (forall p : process, P p -> P (ResCh p)) ->
       (forall p : process, P p -> P (ResVal p)) ->
       (forall (d : defIndex) (e : exp) (l : seq sch), P (PCall d e l)) -> (forall (s : schli) (l : seq msgp), P (MsgQ s l)) -> forall p : process, P p.
Proof. 
intros. eapply process_ind2;eauto.   move => s i l. intros. apply/H6. 
intros. elim : X H14. done. 
ssa. 
rewrite inE in H15. destruct (orP H15). rewrite (eqP H16). done. 
apply/H14. done. 
Qed. 


Inductive Cong : process -> process -> Prop := 
 | CInact P : Cong (Par P Inact) P
 | CParCom P Q : Cong (Par P Q) (Par Q P)
 | CParAss P Q R : Cong (Par (Par P Q) R) (Par P (Par Q R))
 | CResCh P Q : Cong (Par (ResCh P) Q) (ResCh (Par P (shift_sch Q)))
 | CResN P Q:  Cong (Par (ResVal P) Q) (ResVal (Par P (shift_val Q)))
 | CResChI : Cong (ResCh Inact) Inact
 | CResNI : Cong (ResVal Inact) Inact
 | CRef P : Cong P P 
 | CSym P0 P1 : Cong P0 P1 -> Cong P1 P0
 | CTrans P0 P1 P2 : Cong P0 P1 -> Cong P1 P2 -> Cong P0 P2.






Definition ptcp_choiceMixin := [choiceMixin of ptcp by <:].
Canonical ptcp_ChoiceType := Eval hnf in ChoiceType ptcp ptcp_choiceMixin.



Definition qType := seq (ch * (value + nat))%type.

Definition lkey := (sch)%type.

Inductive qkey := QKey : schl -> ptcp -> qkey.
Definition qkey_indDef := [indDef for qkey_rect].
Canonical qkey_indType := IndType qkey qkey_indDef.

Definition qkey_eqMixin := [derive eqMixin for qkey].
Canonical qkey_eqType := EqType qkey qkey_eqMixin.

Definition skey := valBool.
Definition ckey := schli.

Definition l_env := seq (lkey * lType). 
Definition q_env := seq (qkey * qType).
Definition s_env := seq (skey * mysort).
Definition c_env := seq (ckey * unit).


Definition shiftS0 := (subst_valBool ids (succn >> ids)).
Definition initS0 : mysort -> valBool * mysort := (fun b => (var_valBool 0,b)).
Definition insertS0 (E : s_env) (m : mysort) := insert_shift shiftS0 initS0 E (m::nil).

Definition shiftS1 := (subst_valBool (succn>>ids) ids).
Definition initS1 : mysort -> valBool * mysort := (fun b => (valB (var_val 0),b)).
Definition insertS1 (E : s_env) (m : mysort) := insert_shift shiftS1 initS1 E (m::nil).

Definition shiftL0 := (subst_sch ids (succn >> ids)).
Definition initL0 : lType -> sch * lType := (fun T => (var_sch 0,T)).
Definition insertL0 (E : l_env) (T : lType) := insert_shift shiftL0 initL0 E (T::nil).

Definition shiftL1 := (subst_sch (succn >> ids) ids).
Definition initL1 : (ptcp * lType) -> sch * lType := (fun pT => (schlT (var_schl 0) pT.1,pT.2)).
Definition insertL1 (E : l_env) (L : seq (ptcp * lType)) := insert_shift shiftL1 initL1 E L.

Definition subst_qkey (sig : nat -> schl) (q : qkey) := let: QKey s p := q in QKey (subst_schl sig s) p.

Definition shiftQ := (subst_qkey (succn >> ids)).  
Definition initQ : (ptcp * qType) -> qkey * qType  := (fun pT => (QKey (var_schl 0) pT.1,pT.2)).
Definition insertQ (Q : q_env) (L : seq (ptcp * qType)) := insert_shift shiftQ initQ Q L.


Definition shiftC := (subst_schli (succn >> ids)).
Definition initC : ch -> schli * unit := (fun c => ((schliT (var_schl 0) c),tt)).  
Definition insertC (C : c_env) (cs : seq ch) := insert_shift shiftC initC C cs.


Definition lType_done (E : l_env) := all (fun x => x.2 ==  EEnd ) E. 

Definition qType_done (E : q_env) := all (fun x => x.2 == nil) E. 


Definition defType := (mysort * (seq lType))%type. 
Definition def_env := seq defType. 

Definition nat_of_val (v : val) := let: var_val n := v in n. 

Inductive OFTV : s_env -> valBool -> mysort -> Prop :=
 | OFTVB1 Ms n S : lookup Ms (var_valBool n) = Some S  ->  OFTV Ms (var_valBool n) S
 | OFTVB2 Ms b: OFTV Ms ((boolB b)) SBool
 | OFTVB3 Ms n S : lookup Ms ( ((valB (var_val n)))) = Some S ->  OFTV Ms ((valB (var_val n))) S. 


Inductive OFTE : s_env -> exp -> mysort -> Prop :=
 | OFTE1 Ms v S : OFTV Ms v S  -> OFTE Ms (valE v) S
 | OFTE2 Ms e0 e1 : OFTE Ms e0 SBool -> OFTE Ms e1 SBool -> OFTE Ms (andE e0 e1) SBool.


Definition act_roles a := match a with | Action (Ptcp n0) (Ptcp n1) _ => [::n0;n1] end. 

Fixpoint roles_aux g :=
match g with 
| GMsg a u g' => (act_roles a) ++ (roles_aux g')
| GBranch a gs => (act_roles a) ++ (flatten (map (roles_aux \o snd) gs))
| GRec g' => roles_aux g'
| _ => nil  
end. 

Definition nat_of_ch (c : ch) := let: Ch n := c in n.

Fixpoint channels_aux g :=
match g with 
| GMsg a u g' => ( nat_of_ch (action_ch a)) :: (channels_aux g')
| GBranch a gs => (nat_of_ch (action_ch a)) :: (flatten (map (channels_aux \o snd) gs))
| GRec g' => channels_aux g'
| _ => nil  
end. 

Definition p_lt (p0 p1 : ptcp) := 
match p0,p1 with 
|Ptcp n0,Ptcp n1 => n0 < n1 
end.

Definition c_lt (p0 p1 : ch) := 
match p0,p1 with 
|Ch n0,Ch n1 => n0 < n1 
end.


Definition roles g := sort ltn (undup (roles_aux g)).
Definition pid g := size (roles g).
Definition channels g := sort ltn (undup (channels_aux g)).   
Definition sid g := size (channels g).

Definition from_ptcp (p : ptcp) := let: Ptcp n := p in n. 

Coercion Ch: nat >-> ch.


Notation fe := full_eunf.


Inductive IndexSet : nat -> seq nat -> Prop :=
| IS1 : IndexSet 0 (0::nil)
| IS2 n l : IndexSet n l -> IndexSet n.+1 (n.+1::l).

Lemma in_act : forall a n, isSome (comp_dir (Ptcp n) a) = (n \in act_roles a). 
Proof. 
case;ssa. de p. de p0. ssa. rewrite !/comp_dir /=. case_if;ssa. norm_eqs. inv H. lia. 
rifliad. norm_eqs. inv H0. ssa. lia. 
move/eqP : H. intro. move/eqP :H0. intro. apply/negP.
rifliad. ssa.  intro. apply/H2. destruct (orP H1);norm_eqs;ssa. 
Qed. 

Lemma in_roles : forall g p, inp (Ptcp p) g = (p \in roles g). 
Proof.
intros.  rewrite /roles. rewrite mem_sort mem_undup.
 elim : g;ssa. rewrite mem_cat. rewrite in_act H //=. 
rewrite mem_cat in_act. f_equal.
apply/eq_iff. split. move/hasP. case. ssa. destruct x.  
erewrite  H in q. ssa. apply/flattenP. exists (roles_aux (n,g).2). 
apply/map_f.  done. ssa. eauto. 
move/flattenP. case. ssa. apply/hasP.  destruct (mapP p0). subst. ssa. 
erewrite <- H in q. exists x0. done.  done. 
instantiate (1 := x0.1). destruct x0;ssa. 
Qed. 

Lemma proj_end : forall p g, projectable g -> p \notin roles g -> isSome (proj g (Ptcp p)) /\ fe (trans (Ptcp p) g) = EEnd. 
Proof.  
intros. rewrite -in_roles in H0. 
rewrite /proj.  
move : (H (Ptcp p)). case. intro. 
move/project_projT.
move/projectb_iff. move=>->. ssa.
apply/Project_not_part2. destruct (H (Ptcp p)).  apply/project_projT. eauto.
rewrite -inp_iff. apply/negP. done.
Qed. 



Definition projb (g : gType) := all (fun p => proj g (Ptcp p)) (roles g). 
Coercion Ptcp : nat >-> ptcp.


Lemma projbP : forall g, gInvPred g ->  projb g <-> projectable g. 
Proof. 
intro. split. rewrite /projb. intros. intro. exists (trans p g). de p. 
destruct (n \in roles g) eqn:Heqn.  
apply/projectb_iff. apply (allP H0) in Heqn. rewrite /proj in Heqn. 
move : Heqn. rifliad. rewrite -in_roles in Heqn.
pfold. con.  
rewrite EQ_end_aux. econ. rewrite -inp_iff. 
rewrite -inp_full_unf Heqn //=.
apply -> gInvPred_unf_iff. done. done.
rewrite Heqn //=.

intros. apply/allP. intro. intro. rewrite /proj. case_if;ssa. 
move/negP : H2. intro. exfalso. apply/H2. 
apply/projectb_iff. rewrite /projectable in H0. 
edestruct H0.  
apply/project_projT.  eauto.
Qed. 


(*Placeholders are not checked*)
Definition check_entry  (gs : seq (schl * gType))  (lv : (lkey * lType)) :=
match lv with 
| (var_sch _,_) => true 
| (schlT c p,T) => if lookup gs c is Some g then fe (trans p g) == T else false 
end. 


Definition balanced l  := exists gs,
(forall k g, lookup gs k = Some g -> projectable g) /\  all (check_entry gs) l.

Definition lpath := seq (option nat). 

Definition obs (n : option nat) (T : lType) : option (ch * (value + fin)) :=
match full_eunf T,n with 
| EMsg Sd c u _,None => Some (c,(inl u))
| EBranch Sd c _,Some n' => Some (c,(inr n'))
| _,_ => None 
end. 

Definition nexte_wrap (n : option nat) (T : lType) := 
match n,fe T with 
| None, EMsg _ _ _ T' => Some T'
| Some l, EBranch _ _ es => lookup es l 
| _,_=> None
end. 

Fixpoint checkPath (l : lpath) (T : lType) := 
match l with 
| nil => true
| a::l' =>  (obs a T) && (if nexte_wrap a T is Some x then checkPath l' x else false)
end.

Fixpoint makeL (l : lpath) (T : lType) := 
match l with 
| nil => (fe T)
| a::l' =>  if nexte_wrap a T is Some x then makeL l' x else EEnd
end.

Fixpoint makeQ (l : lpath) (T : lType) := 
match l with 
| nil => nil
| a::l' =>  if obs a T is Some o then if nexte_wrap a T is Some T' then  o::(makeQ l' T') else nil else nil 
end.


Definition makeLs (E : seq (ptcp * lType)) (f : ptcp -> lpath) := map (fun x => (x.1,makeL (f x.1) x.2)) E.
Definition makeQs (E : seq (ptcp * lType)) (f : ptcp -> lpath) := map (fun x => (x.1,makeQ (f x.1) x.2)) E.

Definition can_split  (E : seq (ptcp * lType)) (f : ptcp -> lpath) := 
 (forall p T, lookup E p = Some T -> checkPath (f p) T) /\ forall p, p \notin dom E -> f p = nil.
Definition split_set (E : seq (ptcp * lType)) (f : ptcp -> lpath) := (makeLs E f,makeQs E f).




Definition filter_q  (Q : q_env)  (p : hrel qkey ch ) : q_env := map (fun kv => (kv.1, filter_keys (p kv.1) kv.2)) Q.

Definition filter_q_p  (Q : seq (ptcp * qType) )  (p : hrel ptcp ch ) : seq (ptcp * qType) := map (fun kv => (kv.1, filter_keys (p kv.1) kv.2)) Q.


Definition partition_q (Q : q_env) (p : hrel qkey ch )  : q_env * q_env   := (filter_q Q p, filter_q Q  (hrelC p)).

Fixpoint echannels_aux e :=
match e with 
| EMsg _ k u e' => k :: (echannels_aux e')
| EBranch _ k es => k :: (flatten (map (echannels_aux \o snd) es))
| ERec e' => echannels_aux e'
| _ => nil  
end. 


Inductive canStep : gType -> linearity.label  -> Prop :=
 | CGR1 (a : action) u g :  canStep (GMsg a u g) (a, inl u)
 | CGR2 a n g gs : (n,g) \in gs -> canStep (GBranch a gs) (a, inr n)
 | CGR3 a u l g1 : canStep g1 l -> ptcp_to a \notin l.1 -> canStep (GMsg a u g1) l
 | CGR4 a l g gs :  In g gs -> canStep g.2 l -> (ptcp_to a) \notin l.1  ->  canStep (GBranch a gs) l
 | CGR_rec g l  : canStep (unfg g) l -> 
                  canStep (GRec g) l .
Hint Constructors canStep.


Inductive good_gen (P : gType -> Prop) : (gType -> Prop) := 
 | gg g : (forall l, canStep g l -> exists g', step g l g' /\ P g') -> good_gen P g.

Lemma good_gen_mon : monotone1 good_gen.
Proof.
intro. ssa. inv IN. con. ssa. apply H in H0. ssa. eauto.
Qed.
Hint Resolve good_gen_mon : paco.

Definition goodG g := paco1 good_gen bot1 g.


Definition coherentG g := linearity.Linear g /\ size_pred g /\ action_pred g /\ uniqg_labels g /\ (forall p, exists e, Project g p e) /\ goodG g. 
Definition coherent (l : seq (ptcp * lType)) := exists g S, coherentG g /\ l = map (fun p => (Ptcp p,fe(trans p g))) S /\ uniq S /\ subset (roles g) S. 

Definition weak_coherent l q := exists L f, coherent L /\ can_split L f /\ 
  (l,q) = split_set L f.



(*Delta environment is defined in both D0 and D1 (for some session and role) when composing them, only one of them needs to map to end, unlike rules from the paper where one for the entries is simply not there
Equating end in the delta with the entry not being there, embeds weakening *)


(*Check roles will always be initiated correctly by a SLink reduction, ie, never missing roles, or too many roles, or two processes with the same role*)



(*Environment implementation motivated by allowing simple definition of environment splitting, 
  explicit keys (bc. of association list) allows keys to be substituted (not straightforward with either function environments or indexed lists).
  We leave only explicit the part we must substitute, that is, schP and schl. We use predicates on ptcps and natural numbers 
  to divide the resource at each session.
  All sessions in schP are duplicates/placeholders of those in schl, and will later be substituted for a schl.
  This design allows easy substitution by explicit keys and easy splitting by (negatable) predicates on ptcps and channels
 *)
(*Not the keys of the f f' maps are variables without a ptcp. In the later proofs for substitution lemma typing judgment,
  we carry the assumption that applying substitution to lkey ckey is injective, which allows us to show environment update commutes with substitution.
  Assuming injectivity of substitution on keys is bad because we want injectivity of the substitution on schP, that is,
  we want subst_schP sig sig' to be injective, this cannot be derived from injectivity of subst_lkey, because we subst_lkey (s,p) = subst_lkey (s',p') -> s = s' and p = p', is a property that might be enforced by the ptcp (when subst_schP sig sig' s = subst_schP sig sig' s' -> s <> s', it is because p <> p'. Since injectivity of substitution doesn't depend on this ptcp, we should state it on subst_schP.  *)
(*Related to the previous point, ptcp does actually play a role in showing subst_schP sig sig' is injective on the domain of the dela (for the session reception reduction rule), because we from disjointness know the presence of <s,p> in the queue means it is not in the environment for the receving process, and therefore substitution var_schP 0 for <s,p> will be injective on the domain of the typing environment for the process, since the only points where it is not injective is var_schP 0 -> <s,p> and <s,p> -> <s,p> and <s,p> is not in the domain because of disjointness*)
(*The idea above follows the use of polarities in binary session types, where channels have polarities, not session types, likewise our channels have polarities,
  not the session types. Also variables x have no location in binary sesssion types, so we don't either*)







(*Perhaps this should be computed with E2, f0, f1 and f2 as input and E0 and E1 as output
  otherwise we must show existance of substituted E0 and E1
*)
(*Definition new_comp f0 f1 f2 E0 E1 E2 := compT f0 E0 E1 E1 /\ compQ f1 E0 E1 E1 /\ compC f2 E0 E1 E2. *) 

(*For now put default role ptcp0 in located type, later remove located types*)
Definition ptcp0 := Ptcp 0. 

(*The subset predicate for split_env is important, without it
  we can't say anything about the substitution on a f used for the splitting, it's true that only the intersection of f with the domain of the splitted environment has an effect on the splitting. Even still, you must show that splitting, which essentially is environment filtering, commutes with substitution, for which you will need injectivity which you only have on the domain of the environment*) 

(*We need Q = nil in all the non-queue rules, otherwise a queue might appear in the subterm*)
(*Definition ckey := schli.
Definition c_env := seq (ckey * unit).*)

 Inductive OFT : s_env -> def_env -> process -> l_env -> q_env -> c_env -> Prop :=
 | OFT1 Ms Ds a q T n P g E Q:  
                                 qType_done Q ->
                                 OFTV Ms a (SGType g) ->
                                 proj g (Ptcp n) = Some T -> (*Requester is the highest role, differs from paper presentation, makes induction easier for the link rule*)
                                 IndexSet n ( (roles g)) ->
                                 IndexSet q (channels g) ->
(*necessary: runtime check of n roles ensures unique and correct number of roles for global type g*)
                                 OFT Ms Ds P (insertL0 E (fe T)) Q nil ->
                                 OFT Ms Ds (SessReq a n q P) E Q nil

 | OFT2 Ms Ds a T (p : nat) P g E Q : 
                                qType_done Q ->
                                OFTV Ms a (SGType g) -> 
                                proj g p = Some T ->
                                p \in roles g -> (*Also there in the paper but restrictive, if removed allows for idle roles*)
                                OFT Ms Ds P (insertL0 E (fe T)) Q nil->
                                OFT Ms Ds (SessAcc a p P) E Q nil

 | OFT3 Ms Ds (i : index) m T s e P E Q: 
                                qType_done Q ->
                                OFTE Ms e m -> 
                                lookup E s = Some (EMsg Sd i (VSort m) T) -> (*lookupL E s p, asserts location is p *)
                                OFT Ms Ds P  (update E s (fe T)) Q nil ->
                                OFT Ms Ds (ValSend s i e P) E Q nil

 | OFT4 Ms Ds (i : index) m  T s P E Q : 
                                qType_done Q ->
                                lookup E s = Some (EMsg Rd i (VSort m) T)  ->
                                OFT (insertS0 Ms m) Ds P (update E s (fe T)) Q nil ->
                                OFT Ms Ds (ValRec s i P) E Q nil

 | OFT5 Ms Ds (i : index) T T' T'' s s' P E Q: 
                                qType_done Q ->
                                lookup E s = Some (EMsg Sd i (VLT T' ptcp0) T) -> 
                                lookup E s' = Some T'' ->
                                EQ2 T' T'' ->
                                s <> s' -> (*This allows c,p and c,p', meaning we use one endpoint of the session to transfer another endpoint of the same session, this is the rule from binary session types*)
                                OFT Ms Ds P (remove (update E s (fe T)) s') Q nil ->
                                OFT Ms Ds (SessDel s i s' P) E Q nil

 | OFT6 Ms Ds (i : index) T T' s P E Q:  (*T' is not unfolded as it is data in this context*)
                                qType_done Q ->
                                lookup E s = Some (EMsg Rd i (VLT T' ptcp0) T) ->
                                OFT Ms Ds P (insertL0 (update E s (fe T)) (fe T')) Q nil ->
                                OFT Ms Ds (SessRec s i P) E Q nil

 | OFT7 Ms Ds (i : index) Ts s P l T E Q:  
                                qType_done Q ->
                                (l,T) \in Ts ->
                                lookup E s = Some (EBranch Sd i Ts) ->
                                OFT Ms Ds P (update E s (fe T)) Q nil ->
                                OFT Ms Ds (LabelSel s i l P) E Q nil

 | OFT8 Ms Ds (i : index) s Ps Ts E Q:
                                qType_done Q ->
                                map fst Ps = map fst Ts -> 
                                lookup E s = Some (EBranch Rd i Ts) ->
                                (forall P T, In (P,T) (zip (map snd Ps) (map snd Ts)) -> 
                                             OFT Ms Ds P (update E s (fe T)) Q nil) ->
                                OFT Ms Ds (LabelBr s i Ps) E Q nil

 | OFT9 Ms Ds P P' E0 E1 E Q0 Q1 (Q : q_env) C0 C1 C f0 (f1 : hrel qkey ch) f2 : 
                                partition E ( f0) = (E0,E1) ->
                                partition_q Q (f1) = (Q0,Q1) ->
                                partition C (f2) = (C0,C1) ->
                                OFT Ms Ds P  E0 Q0 C0 -> 
                                OFT Ms Ds P' E1 Q1 C1 -> 
                                OFT Ms Ds (Par P P') E Q C
 | OFT10 Ms Ds P0 P1 e E Q:  
                                qType_done Q ->
                                OFT Ms Ds P0 E Q nil -> 
                                OFT Ms Ds P1 E Q nil -> 
                                OFTE Ms e SBool ->  
                                OFT Ms Ds (If e P0 P1) E Q nil

 | OFT11 Ms Ds E Q:           
                                qType_done Q ->
                                lType_done E ->
                                OFT Ms Ds Inact E Q nil

 | OFT12 (Ms : s_env) Ds P g E Q C:    
                                coherentG g -> 
                                OFT (insertS1 Ms (SGType g)) Ds P E Q C -> 
                                OFT Ms Ds (ResVal P) E Q C

 | OFT13 Ms Ds dI L e m (cs : seq lkey) E E0 E1 Q: 
                                qType_done Q ->
                                lType_done E1 ->
                                uniq cs -> (*To ensure linear use of channels *)
                                OFTE Ms e m  ->
                                List.nth_error Ds dI = Some (m,L) -> 
                                size cs = size L ->
                                subset cs (dom E) ->
                                partition E (mem cs) = (E0,E1) ->
                                (forall c T T', (c,T) \in (zip cs L) -> lookup E0 c = Some T' -> EQ2 T T') ->
                                OFT Ms Ds (PCall dI e cs) E Q nil (*cs should be uniq, check section 3.2 in revisited system*)

| OFT14 Ms Ds s E Q: 
                                lType_done E ->
                                qType_done Q ->
                                OFT Ms Ds (MsgQ s nil) E Q ((s,tt)::nil)

 | OFT15 Ms Ds v u msgs s l p E (Q : q_env) i C: 
                                OFTV Ms v u ->
                                lookup Q (QKey s p ) = Some ((i,inl (VSort u))::l) ->
                                OFT Ms Ds (MsgQ (schliT s i) msgs) E (update Q (QKey s p) l) C -> 
                                OFT Ms Ds (MsgQ (schliT s i) ((msgT (valM v) p)::msgs)) E Q C

 | OFT16 Ms Ds msgs T' T'' s s' p l E Q i C : 
                                lookup Q (QKey s p) = Some ((i,inl (VLT T' ptcp0))::l) ->
                                lookup E s' = Some T'' -> 
                                EQ2 T' T'' ->
                                OFT Ms Ds (MsgQ (schliT s i) msgs) (remove E s') (update Q (QKey s p) l) C ->
                                OFT Ms Ds (MsgQ (schliT s i) ((msgT (schM s') p)::msgs)) E Q C

 | OFT17 Ms Ds msgs s p n l E (Q : q_env) i C: 
                                lookup Q (QKey s p) = Some ((i,(inr n))::l) ->
                                OFT Ms Ds (MsgQ (schliT s i) msgs) E (update Q (QKey s p) l) C->
                                OFT Ms Ds (MsgQ (schliT s i) ((msgT (labelM n) p)::msgs)) E Q C
 | OFT18 Ms Ds  P (E : l_env) (Q : q_env) E0 Q0 (C : c_env) C0 : 
                                weak_coherent E0 Q0 -> 
                                OFT Ms Ds P (insertL1 E E0) (insertQ Q Q0) (insertC C C0)  ->    (*We just add some channels cs, that must be found as queues in P*)
                                OFT Ms Ds (ResCh P) E Q C. 


Definition is_var (v : valBool) := 
match v with 
| (boolB _) => false 
| _ => true 
end. 


(*s_env_subst needs to do filtering because it might transform x to boolB true*)
Definition s_env_subst (Ms : s_env) sig sig' := filter_keys is_var (map_keys (subst_valBool sig sig') Ms).


Definition same_base Ms sig sig' :=  (forall v S, lookup Ms v = Some S -> is_var (subst_valBool sig sig' v) = false -> OFTV nil (subst_valBool sig sig' v) S).
Definition same_var (Ms : s_env) sig sig' :=  (forall v S, lookup Ms v = Some S -> is_var (subst_valBool sig sig' v) = true -> lookup Ms (subst_valBool sig sig' v) = Some S).
Definition good_subst Ms sig sig' := forall v S, OFTV Ms v S -> OFTV (s_env_subst Ms sig sig') (subst_valBool sig sig' v) S.

Hint Resolve in_dom. 




Lemma shiftL0_inj : injective shiftL0. 
Proof. 
intro. ssa. rewrite /shiftL0 in H. 
destruct x1,x2;ssa. inv H. 
destruct s,s0;ssa. 
Qed. 

Lemma shiftQ_inj : injective shiftQ. 
Proof. 
intro. ssa. rewrite /shiftQ in H. 
destruct x1,x2;ssa. inv H. 
destruct s,s0;ssa. 
destruct n,n0;ssa. asimpl in H1. inv H1. 
Qed. 

Lemma shiftC_inj : injective shiftC. 
Proof. 
intro. ssa. rewrite /shiftC in H. 
destruct x1,x2;ssa. inv H. 
destruct s,s0;ssa. 
destruct n,n0;ssa. asimpl in H1. inv H1. 
Qed. 

Lemma shiftS1_inj : injective shiftS1. 
Proof. 
intro. ssa. rewrite /shiftS1 in H. 
destruct x1,x2;ssa. inv H. de v. de v0. asimpl in H1. inv H1.
Qed. 

Lemma shiftS0_inj : injective shiftS0. 
Proof. 
intro. ssa. rewrite /shiftS0 in H. 
destruct x1,x2;ssa. inv H. destruct v,v0;ssa. 
Qed. 

Hint Resolve shiftL0_inj shiftQ_inj shiftC_inj shiftS1_inj shiftS0_inj.

Lemma lookup_insertS0_val : forall (Ms : s_env) kv n, lookup (insertS0 Ms kv) (valB (var_val n)) = lookup Ms (valB (var_val n)). 
Proof.
intros. rewrite /insertS0 /insert_shift. ssa. rewrite lookup_cons_neq //=.
erewrite lookup_map_eq_inj. eauto. done. 
done. 
Qed. 

Lemma lookup_insertS0_valBool : forall (Ms : s_env) kv n, lookup (insertS0 Ms kv) (var_valBool n.+1) = lookup Ms (var_valBool n). 
Proof.
intros. rewrite /insertS0 /insert_shift. ssa. rewrite lookup_cons_neq //=.
erewrite lookup_map_eq_inj. eauto. done. done.
Qed. 

Lemma OFTV_insertS0 : forall Ms kv n S, OFTV (insertS0 Ms kv) (var_valBool n.+1) S -> OFTV Ms (var_valBool n) S.
Proof. 
intros. inv H. rewrite lookup_insertS0_valBool in H2. con. done.
Qed. 


Lemma subst_valBool_eq : forall  sig' n, sig' n = subst_valBool var_val sig' (var_valBool n).
Proof. 
done. 
Qed. 

Lemma dom_insertS0 : forall Ms S, dom (insertS0 Ms S) =  (var_valBool 0)::(map shiftS0 (dom Ms) ). 
Proof. intros. rewrite /dom/insertS0. rewrite /insert.  simpl. 
rewrite -map_comp. f_equal. rewrite -map_comp. apply/eq_in_map. done. 
Qed. 



Lemma insertS0_subst : forall Ms sig sig' m, insertS0 (s_env_subst Ms sig sig') m = s_env_subst (insertS0 Ms m) sig (up_valBool_valBool sig').
Proof. 
intros. rewrite /insertS0 /s_env_subst. ssa. rewrite /insert_shift /insert /=. f_equal. 
rewrite map_keys2. rewrite !filter_keys_map_keys map_keys2 /shiftS0 //=.
asimpl. symmetry. erewrite filter_keys_eq. eauto. ssa. 
de x;ssa. asimpl. de (sig' n).
Qed. 


Definition subst_l_env (E : l_env) sig sig' := map_keys (subst_sch sig sig') E.  

Definition subst_q_env (E : q_env) sig := map_keys (subst_qkey sig) E.
Definition subst_c_env (E : c_env) sig := map_keys (subst_schli sig) E.



Lemma insertS1_subst : forall Ms sig sig' m, insertS1 (s_env_subst Ms sig sig') m = s_env_subst (insertS1 Ms m) (up_val_val sig) (up_val_valBool sig').
Proof. 
intros. rewrite /insertS1 /s_env_subst. ssa. rewrite /insert_shift /insert /=. f_equal. 
rewrite map_keys2. rewrite !filter_keys_map_keys map_keys2 /shiftS0 //=.
asimpl. symmetry. erewrite filter_keys_eq. eauto. ssa. 
de x;ssa. asimpl. de (sig' n).
Qed. 

Lemma insertL0_subst : forall (E : l_env) sig sig' T, insertL0 (subst_l_env E sig sig') T = initL0 T :: map_keys (subst_sch sig sig' >> shiftL0) E.
Proof. 
intros. 
rewrite /insertL0 /insert_shift //=. f_equal. rewrite map_keys2 //=.
Qed. 

Lemma insertL1_subst : forall (E : l_env) sig sig' T, insertL1 (subst_l_env E sig sig') T = (map initL1 T) ++ (map_keys (subst_sch sig sig' >> shiftL1) E).
Proof. 
intros. 
rewrite /insertL1 /insert_shift //=. f_equal. rewrite map_keys2 //=.
Qed. 

Lemma insertQ_subst : forall (E : q_env) sig T, insertQ (subst_q_env E sig) T = (map initQ T) ++ (map_keys (subst_qkey sig  >> shiftQ) E).
Proof. 
intros. 
rewrite /insertQ /insert_shift //=. f_equal. rewrite map_keys2 //=.
Qed. 

Lemma insertC_subst : forall (E : c_env) sig T, insertC (subst_c_env E sig) T = (map initC T) ++ (map_keys (subst_schli sig  >> shiftC) E).
Proof. 
intros. 
rewrite /insertC /insert_shift //=. f_equal. rewrite map_keys2 //=.
Qed. 





Lemma lookup_insertS0_val2
     : forall (Ms : s_env) (kv : mysort) v,
       lookup (insertS0 Ms kv) (valB v) = lookup Ms (valB v).
Proof.
intros. destruct v. rewrite lookup_insertS0_val. done.
Qed.




Lemma good_subst_insertS0 : forall Ms kv sig sig', good_subst Ms sig sig' -> good_subst (insertS0 Ms kv) sig (up_valBool_valBool sig').
Proof. 
intros. 
intro. ssa. rewrite -insertS0_subst.
destruct v. inv H0. destruct n;ssa. rewrite lookup_cons_eq //= in H3. inv H3.
con. rewrite lookup_cons_eq //=.
rewrite lookup_insertS0_valBool in H3. 
have: OFTV Ms (var_valBool n) S. con. done.
move/H. move=>HH.
asimpl. asimpl in HH. 
inv HH;ssa. asimpl. con.
rewrite lookup_insertS0_valBool. done. con.
con. rewrite lookup_insertS0_val. done.
inv H0. con.
inv H0. asimpl. 
rewrite lookup_insertS0_val in H3.
have : OFTV Ms (valB (var_val n)) S. con. done.
move/H. move=>HH. asimpl in HH. inv HH.
con.
rewrite  lookup_insertS0_val.  done.
Qed.


Lemma OFTE_subst : forall Ms e S sig sig', good_subst Ms sig sig' ->
OFTE Ms e S -> OFTE (s_env_subst Ms sig sig') (subst_exp sig sig' e) S.
Proof. 
intros. elim : H0 sig sig' H; intros.  ssa. con. 
apply/H0. done. simpl. con;ssa.
Qed. 


Definition good_subst2 (E : l_env) (sig : nat -> schl)  (sig' : nat -> sch) :=  injective_at (dom (E)) (subst_sch sig sig').

Definition good_subst3 (E : q_env) (sig : nat -> schl)  :=  injective_at (dom E) (subst_qkey sig).

Definition good_subst4 (E : c_env) (sig : nat -> schl)  :=  injective_at (dom E) (subst_schli sig).


Lemma good_subst2_remove : forall E lk sig sig', good_subst2 E sig sig' -> good_subst2 (remove E lk) sig sig'.
Proof. 
intros. intro. ssa. rewrite dom_filter_keys !mem_filter in H0,H1. ssa.
Qed. 


Lemma good_subst2_insertL0 : forall E kv sig sig', good_subst2 E sig sig' -> good_subst2 (insertL0 E kv) sig (up_sch_sch sig').
Proof. intros. intro. intros. ssa.  asimpl in H2. rewrite  !inE in H0,H1.
destruct (orP H0),(orP H1). move/eqP:H3. move/eqP:H4. intros. subst. done.
rewrite (eqP H3) in H2. asimpl in H2.
destruct a';ssa. destruct n;ssa.  apply/eqP. done. move : H2.  asimpl.
destruct (sig' n);ssa. move : H2.
move/eqP : H4=>->. 
simpl. asimpl. destruct a;ssa. move : H2.
rewrite /up_sch_sch. asimpl. destruct n;ssa. 
asimpl in H2. destruct (sig' n);ssa. 
rewrite /dom in H3,H4. 
rewrite -!map_comp in H3,H4. 
destruct (mapP H3). destruct (mapP H4).
ssa. rewrite /shiftL0 in H6,H8. subst. asimpl in H2. 
destruct x,x0;ssa. asimpl in H2.
destruct s,s0;ssa;asimpl in H2.
destruct (sig' n) eqn:Heqn;destruct (sig' n0) eqn:Heqn2;ssa.
inv H2. rewrite -Heqn2 in Heqn.
have : subst_sch sig sig' (var_sch n) = subst_sch sig sig' (var_sch n0). done. 
intro. apply H in x. inv x;ssa. apply/mapP. exists (var_sch n,l). done. done.
apply/mapP. exists (var_sch n0,l0). done. done. asimpl in H2. inv H2. 
rewrite -Heqn2 in Heqn.
have : subst_sch sig sig' (var_sch n) = subst_sch sig sig' (var_sch n0). done. 
intro. apply H in x. inv x;ssa. apply/mapP. exists (var_sch n,l). done. done.
apply/mapP. exists (var_sch n0,l0). done. done. 

destruct (sig' n) eqn:Heqn;ssa.
asimpl in H2. inv H2. 
have : subst_sch sig sig' (var_sch n) = subst_sch sig sig' (schlT s p). done. 
intro. apply H in x. inv x;ssa. apply/mapP. exists (var_sch n,l). done. done.
apply/mapP. exists (schlT s p,l0). done. done. 


destruct (sig' n) eqn:Heqn;ssa. asimpl in H2. inv H2. 
have : subst_sch sig sig' (var_sch n) = subst_sch sig sig' (schlT s p0).  done. 
intro. apply H in x. inv x;ssa. apply/mapP. exists (var_sch n,l0). done. done.
apply/mapP. exists (schlT s p0,l). done. done. 
inv H2. 

have : subst_sch sig sig' (schlT s p0) = subst_sch sig sig' (schlT s0 p0).  done. 
intro. apply H in x. inv x;ssa. apply/mapP. exists (schlT s p0,l). done. done.
apply/mapP. exists (schlT s0 p0,l0). done. done. 
Qed. 

Lemma dom_insertL1 : forall E l, dom (insertL1 E l) = (map (fun x => (schlT (var_schl 0) x.1)) l)++(map shiftL1 (dom E)).
Proof. intros. rewrite /insertL1 /dom /insert_shift /insert //= map_cat /initL1.  f_equal. 
rewrite -map_comp //=. rewrite -!map_comp //=. 
Qed. 

Lemma good_subst2_insertL1 : forall E sig sig' l, good_subst2 E sig sig' -> good_subst2 (insertL1 E l) (up_schl_schl sig) (up_schl_sch sig'). 
Proof.
intros. intro. intros. ssa.  asimpl in H2. rewrite dom_insertL1 !mem_cat in H0,H1.
destruct (orP H0);destruct (orP H1);ssa. 
destruct (mapP H3). destruct (mapP H4). ssa. subst. asimpl in H2.  done. 
asimpl in H2. destruct (mapP H3). subst. ssa.
destruct a';ssa. asimpl in H2. destruct (sig' n) eqn:Heqn;ssa.
asimpl in H2. inv H2. destruct s;ssa.
asimpl in H2. inv H2. destruct s;ssa. asimpl in H7. destruct n;ssa. asimpl in H7. 
destruct (sig n);ssa.
destruct (mapP H3);ssa. subst. 
asimpl in H2. 
destruct (mapP H4). ssa. subst. destruct x;ssa.  asimpl in H2. 
destruct (sig' n) eqn:Heqn;ssa. inv H2. destruct s;ssa. 
inv H2. destruct s;ssa. asimpl in H8. destruct (sig n);ssa. 
destruct (mapP H3). destruct (mapP H4). subst. 
rewrite /shiftL1 in H2. asimpl in H2.
destruct x,x0;ssa;asimpl in H2.
destruct (sig' n) eqn:Heqn ; destruct (sig' n0) eqn:Heqn2;ssa.
inv H2. rewrite -Heqn2 in Heqn. 

have : subst_sch sig sig' (var_sch n) = subst_sch sig sig' (var_sch n0). done. 
intro. apply H in x. inv x;ssa. done. done. 

inv H2. 
destruct s,s0;ssa. asimpl in H8. inv H8. 
rewrite -Heqn2 in Heqn . 

have : subst_sch sig sig' (var_sch n) = subst_sch sig sig' (var_sch n0). done. 
intro. apply H in x. inv x;ssa. done. done. 

destruct (sig' n) eqn:Heqn;ssa. asimpl in H2. inv H2. 
destruct s0,s;ssa. asimpl in H8. destruct (sig n1) eqn:Heqn2;ssa. asimpl in H8. inv H8. 
rewrite -Heqn2 in Heqn.
have : subst_sch sig sig' (var_sch n) = subst_sch sig sig' (schlT (var_schl n1) p). done. 
intro. apply H in x. inv x;ssa. done.  done. 


destruct (sig' n) eqn:Heqn;ssa. inv H2. 
destruct s,s0;ssa. asimpl in H8. destruct (sig n0) eqn:Heqn2;ssa. inv H8. 
clear H8. rewrite -Heqn2 in Heqn. 
have : subst_sch sig sig' (var_sch n) = subst_sch sig sig' (schlT (var_schl n0) p0).  done. 
intro. have :  schlT (var_schl (n0)) p0 = var_sch n.
apply/H. done.  done.  ssa. done. 
inv H2. destruct s,s0;ssa. asimpl in H8. destruct (sig n) eqn:Heqn;destruct (sig n0) eqn:Heqn2;ssa.
asimpl in H8. inv H8.  rewrite -Heqn2 in Heqn. 
have : subst_sch sig sig' (schlT (var_schl n) p0) = subst_sch sig sig' (schlT (var_schl n0) p0). 
simpl. rewrite Heqn //=. intros. 
suff :   schlT (var_schl (n)) p0 = schlT (var_schl (n0)) p0. case. intros. subst. done. 
apply/H.  done. done. done. 
Qed. 



Lemma shiftL0_eq : subst_sch ids (succn >> ids) =  shiftL0.
Proof. done. Qed.

Lemma good_subst2_update : forall E sig sig' lk T, good_subst2 E sig sig' -> good_subst2 (update E lk T) sig sig'.
Proof. intros. move : H. rewrite /good_subst2. rewrite dom_update //=.
Qed. 


Lemma good_subst2_smaller : forall E sig sig' E', good_subst2 E sig sig' ->  (forall x, x \in dom E' -> x \in dom E) -> good_subst2 E' sig sig'.
Proof. intros. intro. ssa.
Qed. 

Lemma good_subst2_filter_keys : forall E (p : pred lkey) sig sig' , good_subst2 E sig sig' ->  good_subst2 (filter_keys p E) sig sig'.
Proof. intros. apply/good_subst2_smaller. eauto.
ssa. rewrite dom_filter_keys mem_filter in H0. ssa.
Qed. 

Lemma b_neg : forall (b0 b1 : bool), (b0 = b1) <-> (~~ b0 = ~~ b1).
Proof. 
intros. split. move=>->. done. intros. destruct b0,b1;ssa.
Qed. 

Lemma lType_done_subst : forall E sig sig',  lType_done E -> lType_done (subst_l_env E sig sig'). 
Proof. 
intros. move : H. rewrite /lType_done. intros. 
apply/allP=> x xIn.
destruct (mapP xIn). ssa. destruct x. ssa. inv H1. apply (allP H). done. 
Qed. 

Lemma qType_done_subst : forall E sig,  qType_done E -> qType_done (subst_q_env E sig). 
Proof. 
intros. move : H. rewrite /qType_done. intros. 
apply/allP=> x xIn.
destruct (mapP xIn). ssa. destruct x. ssa. inv H1. apply (allP H). done. 
Qed. 

Lemma lookup_insertS1_val : forall (Ms : s_env) kv n, lookup (insertS1 Ms kv) (valB (var_val n.+1)) = lookup Ms (valB (var_val n)). 
Proof.
intros. rewrite /insertS1 /insert_shift. ssa. rewrite lookup_cons_neq //=.
erewrite lookup_map_eq_inj. eauto. done. done.
Qed. 

Lemma lookup_insertS1_valBool : forall (Ms : s_env) kv n, lookup (insertS1 Ms kv) (var_valBool n) = lookup Ms (var_valBool n). 
Proof.
intros. rewrite /insertS1 /insert_shift. ssa. rewrite lookup_cons_neq //=.
erewrite lookup_map_eq_inj. eauto. done. done.
Qed. 

Lemma OFTV_insertS1 : forall Ms kv n S, OFTV (insertS1 Ms kv) (var_valBool n) S -> OFTV Ms (var_valBool n) S.
Proof. 
intros. inv H. rewrite lookup_insertS1_valBool in H2. con. done.
Qed. 


Lemma dom_insertS1 : forall Ms S, dom (insertS1 Ms S) =  (valB (var_val 0)::(map shiftS1 (dom Ms))). 
Proof. intros. rewrite /dom/insertS1. rewrite /insert.  simpl. 
rewrite -map_comp. f_equal. rewrite -map_comp. apply/eq_in_map. done. 
Qed. 


Lemma good_subst_insertS1 : forall Ms kv sig sig', good_subst Ms sig sig' -> good_subst (insertS1 Ms kv) (up_val_val sig) (up_val_valBool sig').
Proof.
intros. 
intro. ssa. rewrite -insertS1_subst.
destruct v. inv H0. rewrite lookup_insertS1_valBool in H3. 
asimpl. have : OFTV Ms (var_valBool n) S. con. done.
move/H. move=>HH. inv HH. asimpl. con.
rewrite lookup_insertS1_valBool. done. con.
asimpl. con. rewrite lookup_insertS1_val. done.
inv H0. con.
inv H0. asimpl.
destruct n. ssa. rewrite lookup_cons_eq in H3;ssa. inv H3.
con. rewrite lookup_cons_eq. done. done.
rewrite lookup_insertS1_val in H3.
have : OFTV Ms (valB (var_val n)) S. con. done.
move/H. move=>HH. asimpl. inv HH.
asimpl. con. rewrite lookup_insertS1_val. done.
Qed.

Lemma lType_done_map_keys : forall (E : l_env) f, lType_done E -> lType_done (map_keys f E).
Proof. 
intros. move : H. rewrite /lType_done. rewrite all_map. intro. apply/allP. intro. ssa.  
apply (allP H). done. 
Qed. 

Lemma lType_done_filter_keys : forall (E : l_env) f, lType_done E -> lType_done (filter_keys f E).
Proof. 
intros. apply/allP.  intro. intros. apply (allP H). apply in_filter_keys in H0. ssa.
Qed. 

Hint Resolve injective_atP.

Lemma injective_subst_qkey : forall sig, injective (subst_qkey sig) -> injective (subst_qkey (var_schl 0 .: sig >> subst_schl (↑ >> var_schl))).  
Proof.
intros. intro. ssa. de x1. de x2. inv H0. de s.  de s0. 
de n. de n0. asimpl in H2. destruct (sig n0) eqn:Heqn. ssa. 
asimpl in H2. destruct (sig n) eqn:Heqn;ssa.  asimpl in H2. de n0.
asimpl in H2.  destruct (sig n0) eqn:Heqn2;ssa. inv H2. 
rewrite -Heqn2 in Heqn.  f_equal.
suff : var_schl n = var_schl n0. case. move=>->//=. 
have : subst_qkey sig (QKey (var_schl n) p0) = subst_qkey sig (QKey (var_schl n0) p0). 
ssa. intros. apply H in x. inv x. 
Qed. 

Lemma injective_subst_schli : forall sig, injective (subst_schli sig) -> injective (subst_schli (var_schl 0 .: sig >> subst_schl (↑ >> var_schl))).  
Proof.
intros. intro. ssa. de x1. de x2. inv H0. de s.  de s0. 
de n. de n0. asimpl in H2. destruct (sig n0) eqn:Heqn. ssa. 
asimpl in H2. destruct (sig n) eqn:Heqn;ssa.  asimpl in H2. de n0.
asimpl in H2.  destruct (sig n0) eqn:Heqn2;ssa. inv H2. 
rewrite -Heqn2 in Heqn.  f_equal.
suff : var_schl n = var_schl n0. case. move=>->//=. 
have : subst_schli sig (schliT (var_schl n) i0) = subst_schli sig (schliT (var_schl n0) i0). 
ssa. intros. apply H in x. inv x. 
Qed. 

Hint Resolve injective_subst_qkey injective_subst_schli.


Definition pred_dom2 ( A B : eqType) (l : seq A) (f : A -> A) (p : hrel A  B ) : hrel A B
           :=  (fun (a : A) (b : B) =>  has (fun x : A => (f x == a) && p x b) l). 

Lemma filter_q_map_keys : forall (Q : q_env) (f : qkey -> qkey) (f0 : hrel qkey ch), 
filter_q (map_keys f Q) f0 = map_keys f (filter_q Q (fun (q : qkey) => (f0 (f q)))). 
Proof. 
intros. rewrite /filter_q /map_keys -!map_comp. 
apply/eq_in_map. intro. ssa.
Qed. 

Lemma filter_q_eq : forall (Q : q_env) (f0 f1 : hrel qkey ch), (forall x, x \in dom Q -> f0 x = f1 x) ->
filter_q Q f0 = filter_q Q f1.
Proof. 
intros. rewrite /filter_q. 
apply/eq_in_map. intro. ssa. erewrite filter_keys_eq. eauto. intros.   erewrite H. eauto. apply/map_f. done. 
Qed. 


Lemma pred_dom2P : forall (Q : q_env) (f : qkey -> qkey) (p : hrel qkey ch) a, a \in dom Q -> injective f ->  pred_dom2 (dom Q) f p (f a) = p a.
Proof. 
intros. fext. ssa. 
destruct (p a x) eqn:Heqn2;ssa.
apply/hasP.  exists a. ssa. ssa. 
apply/negP. intro. destruct (hasP H1). ssa. move/eqP : H4. intros. apply H0 in H4. subst. 
rewrite Heqn2 in H5. 
ssa. 
Qed. 

Lemma pred_dom2P' : forall (Q : q_env) (f : qkey -> qkey) (p : hrel qkey ch) a, a \in dom Q -> injective_at (dom Q) f ->  pred_dom2 (dom Q) f p (f a) = p a.
Proof. 
intros. fext. ssa. 
destruct (p a x) eqn:Heqn2;ssa.
apply/hasP.  exists a. ssa. ssa. 
apply/negP. intro. destruct (hasP H1). ssa. move/eqP : H4. intros. apply H0 in H4. subst. 
rewrite Heqn2 in H5. 
ssa.  done. done.
Qed. 

Lemma predC_swap : forall (A : eqType) (p0 p1 : pred A ), p0 = p1 -> predC p0 = predC p1.
Proof. 
intros. subst. done. 
Qed. 

Lemma hrelC_swap : forall (A B: eqType) (p0 p1 : hrel A B) a a', p0 a = p1 a' -> hrelC p0 a = hrelC p1 a'.
Proof. 
intros. ssa. rewrite /hrelC. fext. ssa. 
rewrite H //=. 
Qed.


Lemma qType_done_map_keys : forall (Q : q_env) (f : qkey -> qkey), qType_done (map_keys f Q) =  qType_done Q.
Proof. 
intros. rewrite /qType_done. rewrite all_map. apply/eq_in_all. intro. ssa. 
Qed. 

Hint Resolve qType_done_map_keys.

Lemma dom_filter_q : forall (Q : q_env) f, dom (filter_q Q f) = dom Q.
Proof. 
intros. rewrite /dom /filter_q //=.  rewrite -map_comp. apply/eq_in_map. 
ssa.
Qed. 


(*Lemma OFT_subst : forall Ms' Ds P E' Q' C' ,
OFT Ms' Ds P E' Q' C' -> forall sig0 sig1 sig2 sig3 Ms E Q C,
good_subst Ms' sig0 sig1 -> good_subst2 E' sig2 sig3 ->  injective (subst_qkey sig2) -> injective (subst_schli sig2) ->
Ms = (s_env_subst Ms' sig0 sig1) ->
E =  (map_keys (subst_sch sig2 sig3) E') ->
Q = (map_keys (subst_qkey sig2) Q') ->
C =  (map_keys (subst_schli sig2) C') ->
OFT Ms Ds (subst_process sig0 sig1 sig2 sig3 P) E Q C. 
Proof. 
move => Ms' Ds P E' Q' C'. elim.
- intros. ssa. subst. econ;eauto.  asimpl.
  rewrite insertL0_subst. asimpl.

  apply H5;eauto; try solve[ by asimpl].
  apply/good_subst2_insertL0=>//=. 
  rewrite map_keys2. rewrite /shiftL0. by asimpl. 

- intros. ssa. subst. econ;eauto.
  asimpl. rewrite insertL0_subst.
  apply/H4=>//=.
  apply/good_subst2_insertL0=>//=.
  rewrite map_keys2. rewrite /shiftL0. asimpl. done.

- intros. ssa. subst. econ;eauto. apply/OFTE_subst;eauto.
  apply/lookup_map. 3 : eauto. done. apply/in_dom. eauto. eauto.
  apply/H3;eauto. 
  apply/good_subst2_update. done. erewrite update_map_keys; eauto. 

- intros. ssa. asimpl. subst. econ;eauto.
  apply/lookup_map. eauto. 2 : eauto. 
  apply/in_dom=>//=. eauto. eauto. apply/H2;eauto.
  apply/good_subst_insertS0=>//=.
  apply/good_subst2_update=>//=.
  rewrite insertS0_subst //=.  erewrite update_map_keys;eauto. 

- intros. ssa. subst. econ. eauto.
  apply/lookup_map. done. 2 : eauto.
  apply/in_dom=>//=. eauto. eauto.
  apply/lookup_map; eauto.  done.
  intro. apply/H3. apply/H7;eauto.
  erewrite update_map_keys. 
  rewrite /remove. rewrite filter_keys_map_keys.
  apply/H5;eauto. apply good_subst2_remove.
  apply/good_subst2_update=>//=.
  rewrite /remove. f_equal.  apply/filter_keys_eq.
  intro. ssa. 
  apply/inj_neq. 3 : eauto. rewrite dom_update //= in H10.  
  apply/in_dom=>//=. eauto. done. 
  apply/in_dom=>//=. eauto. done.

- intros. ssa. subst. econ;eauto.
  apply/lookup_map; eauto. asimpl.
  erewrite update_map_keys;eauto. 
  rewrite insertL0_subst. apply/H2;eauto.
  apply/good_subst2_insertL0.
  apply/good_subst2_update=>//=.
  f_equal. rewrite map_keys2. asimpl. done.

- intros. ssa. subst. econ;eauto.
  apply/lookup_map; eauto. apply/H3;eauto.
  apply/good_subst2_update=>//=.
  erewrite update_map_keys;eauto.

- intros. ssa. subst. econ;eauto. 2 : { apply/lookup_map; eauto. }
  rewrite -map_comp.
  have :  list_map
    fst
    Ps =  list_map
    (fst \o prod_map ssrfun.id (subst_process sig0 sig1 sig2 sig3))
    Ps. apply/eq_in_map. intro. ssa. destruct x;ssa. move=><-=>//=. 
  
  intros. move/inP : H8. 
  rewrite -map_comp. move/mapPzip. case. 
  ssa. rewrite /prod_map in H9. destruct x.  ssa. subst. 
  erewrite update_map_keys;eauto.
  apply/H3;eauto. apply/inP. 
  have : snd (n,p) = p by done. move=><-. apply/mapPzip2=>//=.
  apply/good_subst2_update=>//=.

- intros. ssa. subst. econ;eauto.

  instantiate (3:= pred_dom (dom E) (subst_sch sig2 sig3) f0). econ.
  rewrite /partition_q in H0. 
  instantiate (3:= (pred_dom2 (dom Q) (subst_qkey sig2) f1)). 

econ.
  instantiate (3:= pred_dom (dom C) (subst_schli sig2) f2). econ.

  inv H. inv H0. inv H1. apply/H3;eauto.  
  apply/good_subst2_filter_keys=>//=.
  rewrite filter_keys_map_keys. 
  f_equal. 
  apply filter_keys_eq. intro. ssa. apply/pred_domP=>//=.

  rewrite filter_q_map_keys. f_equal.
  apply/filter_q_eq. intro. ssa.

  rewrite pred_dom2P=>//=. 

  rewrite filter_keys_map_keys //=. f_equal.
  apply/filter_keys_eq. intro. ssa.  apply/pred_domP=>//=. apply/injective_atP. done.

  inv H. inv H0. inv H1. apply/H5;eauto.  
  apply/good_subst2_filter_keys=>//=.
  rewrite filter_keys_map_keys. f_equal.
  apply filter_keys_eq. intro. ssa. 
  rewrite b_neg !negb_involutive.
  apply/pred_domP=>//=.

  rewrite filter_q_map_keys //=. f_equal.
  apply/filter_q_eq. intro. ssa.
  apply hrelC_swap. rewrite pred_dom2P //=.

  rewrite filter_keys_map_keys //=. f_equal.
  apply/filter_keys_eq. intro. ssa.
  rewrite b_neg !negb_involutive.
  apply/pred_domP=>//=. apply/injective_atP. done.
  
- intros. ssa. subst. econ;eauto. apply/OFTE_subst=>//=. 

- intros. ssa. subst. econ;eauto.
  apply/lType_done_subst=>//=.

- intros. ssa. subst. econ;eauto. asimpl. 
  rewrite insertS1_subst. apply/H1;eauto.
  apply/good_subst_insertS1=>//=.

- intros. ssa. inv H6. econ. eauto.
  4 : eauto.
  6 : { econ.  } 
  rewrite filter_keys_map_keys.
  erewrite filter_keys_eq.  
  apply/lType_done_subst=>//=. eauto. 
  intro. ssa. rewrite b_neg !negb_involutive.
  apply/mem_map_inj. 3 : eauto. done. done.
  rewrite map_inj_in_uniq //=. intro. ssa. 
  apply/OFTE_subst. done.  eauto. rewrite size_map //=.


  rewrite dom_map_keys.
  apply/subset_map. done.
  intros. move/mapPzip : H12. case. ssa. subst.
  apply/H7. eauto. 
  apply/lookup_filter;ssa. apply mem_zip in H12. ssa.
  apply/lookup_map.  eauto. 2 : eauto. apply/H5. apply mem_zip in H12. ssa.
  
  apply lookup_filter2 in H13. ssa. 

- intros. ssa. subst. econ;eauto.
  apply/lType_done_subst=>//=.

- intros. ssa. subst. econ;eauto.
  apply/lookup_map. eauto.  2 : { instantiate (1:= (QKey s p)).  ssa. } 
                         apply/in_dom. eauto. eauto. 
  erewrite update_map_keys. apply/H2;eauto.
  apply/injective_atP. done. 
  apply/in_dom.  eauto.  done.

- intros. ssa. subst. econ;eauto. erewrite lookup_map_eq_inj. eauto.
  done. done.
  apply/lookup_map.  eauto.
  apply/in_dom. eauto. done. done.
  rewrite /remove. rewrite filter_keys_map_keys.
  apply/H3;eauto. rewrite /remove. apply/good_subst2_filter_keys=>//=.
  f_equal. apply/filter_keys_eq. intro. ssa.
  rewrite b_neg !negb_involutive.
  apply/inj_eq. 3 : eauto. done.
  eauto.
  erewrite update_map_keys. eauto. 
  apply/injective_atP. eauto.
  eauto. done.

- intros. ssa. subst. econ;eauto.
  apply/lookup_map. eauto. eauto. done. eauto. 
  erewrite update_map_keys. apply/H1;eauto. eauto. 
  eauto. done.

- intros. ssa. asimpl. subst. 
  econ. eauto.
  rewrite insertL1_subst. 
  rewrite insertQ_subst. apply/H1;eauto.
  apply/good_subst2_insertL1=>//=. 
  rewrite /insertL1 /insert_shift /insert.
  rewrite !map_keys_cat. ssa.
  f_equal. rewrite /map_keys -map_comp. apply/eq_in_map.
  intro. ssa. asimpl. rewrite map_keys2 //=. asimpl. done. 
  rewrite !map_keys_cat. ssa.
  f_equal. rewrite /map_keys -map_comp. apply/eq_in_map.
  intro. ssa. asimpl. rewrite /subst_qkey. rewrite map_keys2 //=. asimpl. 
  apply map_keys_eq. intro. ssa. asimpl. de x.  f_equal. 
  asimpl. done. 
  rewrite insertC_subst.
  rewrite /insertC /insert_shift /insert.
  rewrite !map_keys_cat. ssa.
  f_equal. rewrite /map_keys -map_comp. apply/eq_in_map.
  intro. ssa. asimpl. rewrite /subst_qkey. asimpl. rewrite map_keys2 //=. asimpl. 
  done.
Qed.*)


Lemma dom_insertQ : forall ( Q: q_env) Q', dom (insertQ Q Q') = (map (QKey (var_schl 0)) (dom Q')) ++ dom (map_keys shiftQ Q). 
Proof. 
intros. rewrite /insertQ /insert_shift /insert dom_cat.  f_equal. 
rewrite /dom -!map_comp. done.
Qed. 


Lemma OFT_subst : forall Ms' Ds P E' Q' C' ,
OFT Ms' Ds P E' Q' C' -> forall sig0 sig1 sig2 sig3 Ms E Q C,
good_subst Ms' sig0 sig1 -> good_subst2 E' sig2 sig3 ->  injective_at (dom Q') (subst_qkey sig2) -> 
injective_at (dom C') (subst_schli sig2) ->
Ms = (s_env_subst Ms' sig0 sig1) ->
E =  (map_keys (subst_sch sig2 sig3) E') ->
Q = (map_keys (subst_qkey sig2) Q') ->
C =  (map_keys (subst_schli sig2) C') ->
OFT Ms Ds (subst_process sig0 sig1 sig2 sig3 P) E Q C. 
Proof. 
move => Ms' Ds P E' Q' C'. elim.
- intros. ssa. subst. econ;eauto.  asimpl.
  rewrite insertL0_subst. asimpl.

  apply H5;eauto; try solve[ by asimpl].
  apply/good_subst2_insertL0=>//=. 
  rewrite map_keys2. rewrite /shiftL0. by asimpl. 

- intros. ssa. subst. econ;eauto.
  asimpl. rewrite insertL0_subst.
  apply/H4=>//=.
  apply/good_subst2_insertL0=>//=.
  rewrite map_keys2. rewrite /shiftL0. asimpl. done.

- intros. ssa. subst. econ;eauto. apply/OFTE_subst;eauto.
  apply/lookup_map. 3 : eauto. done. apply/in_dom. eauto. eauto.
  apply/H3;eauto. 
  apply/good_subst2_update. done. erewrite update_map_keys; eauto. 

- intros. ssa. asimpl. subst. econ;eauto.
  apply/lookup_map. eauto. 2 : eauto. 
  apply/in_dom=>//=. eauto. eauto. apply/H2;eauto.
  apply/good_subst_insertS0=>//=.
  apply/good_subst2_update=>//=.
  rewrite insertS0_subst //=.  erewrite update_map_keys;eauto. 

- intros. ssa. subst. econ. eauto.
  apply/lookup_map. done. 2 : eauto.
  apply/in_dom=>//=. eauto. eauto.
  apply/lookup_map; eauto.  done.
  intro. apply/H3. apply/H7;eauto.
  erewrite update_map_keys. 
  rewrite /remove. rewrite filter_keys_map_keys.
  apply/H5;eauto. apply good_subst2_remove.
  apply/good_subst2_update=>//=.
  rewrite /remove. f_equal.  apply/filter_keys_eq.
  intro. ssa. 
  apply/inj_neq. 3 : eauto. rewrite dom_update //= in H10.  
  apply/in_dom=>//=. eauto. done. 
  apply/in_dom=>//=. eauto. done.

- intros. ssa. subst. econ;eauto.
  apply/lookup_map; eauto. asimpl.
  erewrite update_map_keys;eauto. 
  rewrite insertL0_subst. apply/H2;eauto.
  apply/good_subst2_insertL0.
  apply/good_subst2_update=>//=.
  f_equal. rewrite map_keys2. asimpl. done.

- intros. ssa. subst. econ;eauto.
  apply/lookup_map; eauto. apply/H3;eauto.
  apply/good_subst2_update=>//=.
  erewrite update_map_keys;eauto.

- intros. ssa. subst. econ;eauto. 2 : { apply/lookup_map; eauto. }
  rewrite -map_comp.
  have :  list_map
    fst
    Ps =  list_map
    (fst \o prod_map ssrfun.id (subst_process sig0 sig1 sig2 sig3))
    Ps. apply/eq_in_map. intro. ssa. destruct x;ssa. move=><-=>//=. 
  
  intros. move/inP : H8. 
  rewrite -map_comp. move/mapPzip. case. 
  ssa. rewrite /prod_map in H9. destruct x.  ssa. subst. 
  erewrite update_map_keys;eauto.
  apply/H3;eauto. apply/inP. 
  have : snd (n,p) = p by done. move=><-. apply/mapPzip2=>//=.
  apply/good_subst2_update=>//=.

- intros. ssa. subst. econ;eauto.

  instantiate (3:= pred_dom (dom E) (subst_sch sig2 sig3) f0). econ.
  rewrite /partition_q in H0. 
  instantiate (3:= (pred_dom2 (dom Q) (subst_qkey sig2) f1)). 

econ.
  instantiate (3:= pred_dom (dom C) (subst_schli sig2) f2). econ.

  inv H. inv H0. inv H1. apply/H3;eauto.  
  apply/good_subst2_filter_keys=>//=.


(*injective add additions*)
  intro. ssa. 
  rewrite dom_filter_q in H10 H11. eauto. eauto.
  intro. ssa. rewrite dom_filter_keys !mem_filter  in H10 H11. ssa.



  rewrite filter_keys_map_keys. 
  f_equal. 
  apply filter_keys_eq. intro. ssa. apply/pred_domP=>//=.

  rewrite filter_q_map_keys. f_equal.
  apply/filter_q_eq. intro. ssa.

  rewrite pred_dom2P'=>//=. 

  rewrite filter_keys_map_keys //=. f_equal.
  apply/filter_keys_eq. intro. ssa.  apply/pred_domP=>//=. 

  inv H. inv H0. inv H1. apply/H5;eauto.  
  apply/good_subst2_filter_keys=>//=.

(*injective add additions*)
  intro. ssa. 
  rewrite dom_filter_q in H10 H11. eauto. eauto.
  intro. ssa. rewrite dom_filter_keys !mem_filter  in H10 H11. ssa.



  rewrite filter_keys_map_keys. f_equal.
  apply filter_keys_eq. intro. ssa. 
  rewrite b_neg !negb_involutive.
  apply/pred_domP=>//=.

  rewrite filter_q_map_keys //=. f_equal.
  apply/filter_q_eq. intro. ssa.
  apply hrelC_swap. rewrite pred_dom2P' //=.

  rewrite filter_keys_map_keys //=. f_equal.
  apply/filter_keys_eq. intro. ssa.
  rewrite b_neg !negb_involutive.
  apply/pred_domP=>//=. 
  
- intros. ssa. subst. econ;eauto. apply/OFTE_subst=>//=. 

- intros. ssa. subst. econ;eauto.
  apply/lType_done_subst=>//=.

- intros. ssa. subst. econ;eauto. asimpl. 
  rewrite insertS1_subst. apply/H1;eauto.
  apply/good_subst_insertS1=>//=.

- intros. ssa. inv H6. econ. eauto.
  4 : eauto.
  6 : { econ.  } 
  rewrite filter_keys_map_keys.
  erewrite filter_keys_eq.  
  apply/lType_done_subst=>//=. eauto. 
  intro. ssa. rewrite b_neg !negb_involutive.
  apply/mem_map_inj. 3 : eauto. done. done.
  rewrite map_inj_in_uniq //=. intro. ssa. 
  apply/OFTE_subst. done.  eauto. rewrite size_map //=.


  rewrite dom_map_keys.
  apply/subset_map. done.
  intros. move/mapPzip : H12. case. ssa. subst.
  apply/H7. eauto. 
  apply/lookup_filter;ssa. apply mem_zip in H12. ssa.
  apply/lookup_map.  eauto. 2 : eauto. apply/H5. apply mem_zip in H12. ssa.
  
  apply lookup_filter2 in H13. ssa. 

- intros. ssa. subst. econ;eauto.
  apply/lType_done_subst=>//=.

- intros. ssa. subst. econ;eauto.
  apply/lookup_map. eauto.  2 : { instantiate (1:= (QKey s p)).  ssa. } 
                         apply/in_dom. eauto. eauto. 
  erewrite update_map_keys. apply/H2;eauto.
  rewrite dom_update. done. done.
  apply/in_dom.  eauto.  done.

- intros. ssa. subst. econ;eauto.
  rewrite lookup_map. eauto. done.
  apply/in_dom. eauto. done. 
  rewrite lookup_map. eauto. done.
  apply/in_dom. eauto. done.

  rewrite /remove. rewrite filter_keys_map_keys.
  apply/H3;eauto. rewrite /remove. apply/good_subst2_filter_keys=>//=.
  rewrite dom_update //=.
  f_equal. apply/filter_keys_eq. intro. ssa.
  rewrite b_neg !negb_involutive.
  apply/inj_eq. 3 : eauto. done.
  eauto.
  erewrite update_map_keys. eauto.  eauto.
  apply/in_dom. eauto. eauto.

- intros. ssa. subst. econ;eauto.
  apply/lookup_map. eauto. eauto. done. eauto. 
  erewrite update_map_keys. apply/H1;eauto. eauto. 
  rewrite dom_update //=. eauto.
  apply/in_dom. eauto. ssa.

- intros. ssa. asimpl. subst. 
  econ. eauto.
  rewrite insertL1_subst. 
  rewrite insertQ_subst. apply/H1;eauto.
  apply/good_subst2_insertL1=>//=.

 
  intro. ssa.
  rewrite dom_insertQ !mem_cat in H6 H7.
  de (orP H6). 
 - de (mapP H9). subst.
   de (orP H7). 
  * de (mapP H11). subst. asimpl in H8. ssa.
  * asimpl in H8. ssa. de (mapP H11). subst. de (mapP H12). subst. ssa.
    de x1. asimpl in H8. de q. de p. asimpl in H8. 
    inv H8. de s. asimpl in H15. de (sig2 n0). 
 - asimpl in H8. ssa. 
   de (mapP H9). subst. de (mapP H10). subst. ssa.
   de (orP H7). 
   * de (mapP H12). subst. asimpl in H8. ssa. 
     de x0. de q. inv H8. de s. asimpl in H15. de (sig2 n). 
   * de (mapP H12). subst.
     de (mapP H13). subst. ssa. de x0. de x1. ssa. asimpl in H8. ssa.
     de q. de q0. asimpl in H8. inv H8. de s. de s0. asimpl in H16.
     destruct (sig2 n) eqn:Heqn2.
     destruct (sig2 n0) eqn:Heqn3. ssa. inv H16. ssa.
     rewrite -Heqn2 in Heqn3. 
     have : subst_qkey (sig2) (QKey (var_schl n) p0) = subst_qkey sig2 (QKey (var_schl n0) p0).
       ** simpl. rewrite Heqn3. done. 
     intro. apply H4 in x;first by inv x. 
      ** apply/mapP. econ;first by apply:H14. ssa.
         have : subst_qkey (sig2) (QKey (var_schl n) p0) = subst_qkey sig2 (QKey (var_schl n0) p0).
          *** simpl. done.  
         intro. apply H4 in x0;first by inv x0. 
          *** apply/mapP. econ;first by apply/ H11. ssa. 
         apply/mapP. econ; first by apply/H14. ssa. 
     apply/mapP. econ. eauto. ssa.


  intro. ssa.
  rewrite /insertC  /insert_shift /insert /dom !map_cat !mem_cat in H6,H7;ssa.

  de (orP H6).  
 - de (mapP H9). subst. de (mapP H10). subst.
   de (orP H7). 
  * de (mapP H12). subst. de (mapP H13). subst. asimpl in H8. ssa.
  * asimpl in H8. ssa. de (mapP H12). subst. de (mapP H13). subst. ssa.
    de x1. asimpl in H8. de s. asimpl in H8. 
    inv H8. de s. asimpl in H16. de (sig2 n). 
 - asimpl in H8. ssa. 
   de (mapP H9). subst. de (mapP H10). subst. ssa.
   de (orP H7). 
   * de (mapP H12). subst. asimpl in H8. de (mapP H13). subst.  ssa. 
     de x0. de s. inv H8. de s. asimpl in H16. de (sig2 n). 
   * de (mapP H12). subst.
     de (mapP H13). subst. ssa. de x0. de x1. ssa. asimpl in H8. ssa.
     de s. de s0. asimpl in H8. inv H8. de s. de s0. asimpl in H16.
     destruct (sig2 n) eqn:Heqn2.
     destruct (sig2 n0) eqn:Heqn3. ssa. inv H16. ssa.
     rewrite -Heqn2 in Heqn3. 
     have : subst_schli (sig2) (schliT (var_schl n) i0) = subst_schli sig2 (schliT (var_schl n0) i0).
       ** simpl. rewrite Heqn3. done. 
     intro. apply H5 in x;first by inv x. 
      ** apply/mapP. econ;first by apply:H14. ssa.
         have : subst_schli (sig2) (schliT (var_schl n) i0) = subst_schli sig2 (schliT (var_schl n0) i0).
          *** simpl. done.  
         intro. apply H5 in x0;first by inv x0. 
          *** apply/mapP. econ;first by apply/ H11. ssa. 
         apply/mapP. econ; first by apply/H14. ssa. 
     apply/mapP. econ. eauto. ssa.



  rewrite /insertL1 /insert_shift /insert.
  rewrite !map_keys_cat. ssa.
  f_equal. rewrite /map_keys -map_comp. apply/eq_in_map.
  intro. ssa. asimpl. rewrite map_keys2 //=. asimpl. done. 
  rewrite !map_keys_cat. ssa.
  f_equal. rewrite /map_keys -map_comp. apply/eq_in_map.
  intro. ssa. asimpl. rewrite /subst_qkey. rewrite map_keys2 //=. asimpl. 
  apply map_keys_eq. intro. ssa. asimpl. de x.  f_equal. 
  asimpl. done. 
  rewrite insertC_subst.
  rewrite /insertC /insert_shift /insert.
  rewrite !map_keys_cat. ssa.
  f_equal. rewrite /map_keys -map_comp. apply/eq_in_map.
  intro. ssa. asimpl. rewrite /subst_qkey. asimpl. rewrite map_keys2 //=. asimpl. 
  done.
Qed.


Lemma s_env_subst_id : forall E, all is_var (dom E) -> s_env_subst E var_val var_valBool = E. 
Proof. 
intros. rewrite /s_env_subst. elim : E H;ssa. asimpl. 
ssa. rewrite H1 //=. f_equal. destruct a;ssa.
asimpl in H. eauto. 
Qed. 


Lemma good_subst_var : forall Ms, good_subst Ms var_val var_valBool.
Proof. 
intros. intro.
ssa. 
elim : H;ssa.
con. rewrite /s_env_subst.
apply/lookup_filter.    ssa. 
erewrite lookup_map_eq_inj. eauto. asimpl. done.
asimpl. done. con.
con.
apply/lookup_filter.    ssa. 
erewrite lookup_map_eq_inj. eauto. asimpl. done. done.

Qed. 

Lemma good_subst2_shift : forall E, good_subst2 E (shift >> var_schl) var_sch.
Proof. 
intros. intro. ssa. destruct a,a';ssa. inv H1;ssa. destruct s,s0;ssa. asimpl in H3. inv H3. 
Qed. 

Lemma good_subst3_shift : forall E, good_subst3 E (shift >> var_schl). 
Proof. 
intros. intro. ssa. 
Qed. 

Lemma subst_sch_shiftL1 : forall sig sig' x, subst_sch sig (up_sch_sch sig') (shiftL0 x) = (shiftL0 (subst_sch sig sig' x)). 
Proof. intros. rewrite /shiftL0. asimpl. de x. 
Qed. 

Lemma shiftL1_inj : injective shiftL1.
Proof. intro. intros. rewrite /shiftL1 in H. asimpl in H.  destruct x1,x2;ssa. asimpl in H. inv H. 
de s. de s0. inv H1. 
Qed. 



Hint Resolve good_subst_var good_subst2_shift good_subst3_shift shiftL0_inj shiftQ_inj shiftL1_inj shiftS1_inj shiftS0_inj.


Definition weaken (E : l_env) (f : pred lkey) E' := filter_keys (f) E' = E /\ lType_done (filter_keys (predC f) E').  

Lemma lookup_shiftL0_id : forall ( E0 : l_env) s p, lookup (map_keys shiftL0 E0) (schlT s p) =
                                   lookup E0 (schlT s p).
Proof. intros. elim : E0;ssa. rewrite /shiftL0 //=. destruct a;ssa. asimpl.  
destruct l0;ssa. asimpl. ssa. 
de (eqVneq (schlT s0 p0) (schlT s p)). inv e. rewrite !lookup_cons_eq //=.
rewrite !lookup_cons_neq //=.
Qed. 

Lemma lookup_shiftL1_id : forall ( E0 : l_env) n, lookup (map_keys shiftL1 E0) (var_sch n) =
                                   lookup E0 (var_sch n).
Proof. intros. elim : E0;ssa. rewrite /shiftL1 //=. destruct a;ssa. asimpl.  
destruct l0;ssa. asimpl. ssa. 
de (eqVneq (var_sch n0) (var_sch n)). inv e. rewrite !lookup_cons_eq //=.
rewrite !lookup_cons_neq //=.
Qed. 

Lemma subst_sch_id : forall v, subst_sch var_schl var_sch v = v. 
Proof. case;ssa. asimpl. done.  Qed. 

Lemma subst_sch_id2 : subst_sch var_schl var_sch = ssrfun.id.
Proof. ssa. fext. case;ssa. de s. 
Qed. 


Definition is_lkey1 (l : lkey) := 
match l with | schlT (var_schl 0) _ => true | _ => false end. 

Lemma is_lkey1_shift : forall x,
 is_lkey1 (shiftL1 x) = false. 
Proof. case;ssa. de s. 
Qed. 

Lemma in_initL1 : forall x T, x \in dom (list_map initL1 T) -> is_lkey1 x.
Proof. ssa. rewrite /dom -map_comp in H. de (mapP H). subst. done.  Qed.


Definition is_lkey0 (l : lkey) := l == var_sch 0.

Lemma is_lkey0_shift : forall x,
 is_lkey0 (shiftL0 x) = false. 
Proof. case;ssa. 
Qed. 

Lemma in_initL0 : forall x T, x \in dom (list_map initL0 T) -> is_lkey0 x.
Proof. ssa. rewrite /dom -map_comp in H. de (mapP H). subst. done.  Qed.

Definition is_skey0 (l : skey) := l == var_valBool 0.


Lemma is_skey0_shift : forall x,
 is_skey0 (shiftS0 x) = false. 
Proof. case;ssa. 
Qed. 

Lemma in_initS0 : forall x T, x \in dom (list_map initS0 T) -> is_skey0  x.
Proof. ssa. rewrite /dom -map_comp in H. de (mapP H). subst. done.  Qed.

Definition is_skey1 (l : skey) := l == valB (var_val 0).


Lemma is_skey1_shift : forall x,
 is_skey1 (shiftS1 x) = false. 
Proof. case;ssa. de v. 
Qed. 

Lemma in_initS1 : forall x T, x \in dom (list_map initS1 T) -> is_skey1  x.
Proof. ssa. rewrite /dom -map_comp in H. de (mapP H). subst. done.  Qed.



Definition is_qkey (l : qkey) := 
match l with 
| QKey (var_schl 0) _ => true 
| _ => false 
end. 


Lemma is_qkey_shift : forall x,
 is_qkey (shiftQ x) = false. 
Proof. case;ssa. de s. 
Qed. 

Lemma in_initQ : forall x T, x \in dom (list_map initQ T) -> is_qkey x.
Proof. ssa. rewrite /dom -map_comp in H. de (mapP H). subst. done.  Qed.

Definition is_ckey (l : ckey) := 
match l with 
| schliT (var_schl 0) _ => true 
| _ => false 
end. 

Lemma is_ckey_shift : forall x,
 is_ckey (shiftC x) = false. 
Proof. case;ssa. de s. 
Qed. 

Lemma in_initC : forall x T, x \in dom (list_map initC T) -> is_ckey x.
Proof. ssa. rewrite /dom -map_comp in H. de (mapP H). subst. done.  Qed.

Ltac tunf := rewrite !pheqs.
Ltac tunf_in H := rewrite !pheqs in H.

Lemma filter_keys_insertL1_f_aux : forall E E1 f0, (filter_keys (predU (is_lkey1) (pred_dom (dom E) shiftL1 f0))  (insertL1 E E1)) =
 (insertL1 (filter_keys f0 E) E1). 
Proof. 
intros. 
rewrite /insertL1 /insert_shift /insert. ssa.
rewrite !filter_keys_cat. f_equal.
erewrite filter_keys_eq. erewrite filter_keys_predT. done.
intros. ssa.
rewrite /dom -map_comp in H. destruct (mapP H). subst. 
ssa. 
rewrite filter_keys_map_keys. f_equal.
apply/filter_keys_eq. ssa. tunf.
rewrite pred_domP. 
rewrite is_lkey1_shift //=. eauto.
done.
Qed. 

Lemma filter_keys_insertL1_f : forall E E1 f0,  (insertL1 (filter_keys f0 E) E1) = (filter_keys (predU (is_lkey1) (pred_dom (dom E) shiftL1 f0))  (insertL1 E E1)).
Proof. 
intros. rewrite filter_keys_insertL1_f_aux //=.
Qed. 


Lemma filter_keys_cancel_insertL1 : forall E E1 f0,
 (filter_keys (predC (predU is_lkey1 ((pred_dom (dom E) shiftL1 f0)))) (insertL1 E E1)) =  map_keys shiftL1 (filter_keys (predC f0) E).
Proof. 
intros. rewrite /insertL1 /insert_shift /insert. ssa. rewrite filter_keys_cat. 
erewrite filter_keys_eq. erewrite filter_keys_pred0. ssa.
rewrite filter_keys_map_keys. f_equal. 
apply/filter_keys_eq. intro. ssa. tunf.
rewrite pred_domP //=. rewrite is_lkey1_shift. lia. eauto.
ssa. tunf. erewrite in_initL1;eauto.
Qed.

Lemma filter_keys_cancel_insertC : forall E E1 f0,
 (filter_keys (predC (predU is_ckey ((pred_dom (dom E) shiftC f0)))) (insertC E E1)) =  map_keys shiftC (filter_keys (predC f0) E).
Proof. 
intros. rewrite /insertC /insert_shift /insert. ssa. rewrite filter_keys_cat. 
erewrite filter_keys_eq. erewrite filter_keys_pred0. ssa.
rewrite filter_keys_map_keys. f_equal. 
apply/filter_keys_eq. intro. ssa. tunf.
rewrite pred_domP //=. rewrite is_ckey_shift. lia. eauto.
ssa. tunf. erewrite in_initC;eauto.
Qed.  

Lemma predCU : forall (A : eqType) (P P' : A -> bool), predC (predU P P') = predI (predC P) (predC P') :> (A -> bool).
Proof. 
intros. fext. ssa. tunf. lia. 
Qed. 

Lemma weaken_insertL1 : forall E0 f E' T, weaken E0 f E' -> weaken (insertL1 E0 T) (predU is_lkey1 (pred_dom (dom E') shiftL1 f)) (insertL1 E' T).
Proof. ssa. 
rewrite /weaken. inv H. 
ssa. rewrite filter_keys_insertL1_f //=.
rewrite filter_keys_cancel_insertL1.
apply lType_done_map_keys=>//=.
Qed. 


Lemma weaken_insertL0 : forall E0 E' f T, weaken E0 f E' -> weaken (insertL0 E0 T)  (predU is_lkey0 (pred_dom (dom E') shiftL0 f)) (insertL0 E' T).
Proof. ssa. inv H.  
rewrite /weaken. ssa. rewrite /insertL0 /insert_shift /=. f_equal. 
rewrite filter_keys_map_keys. f_equal. 
apply filter_keys_eq. intro. ssa.

rewrite !pheqs.
rewrite is_lkey0_shift /=. 
rewrite pred_domP //=. eauto.

apply/allP. intro. ssa. 
apply in_filter_keys in H0. ssa.
tunf_in H0. rewrite  negb_or in H0. ssa.
de (mapP H2). subst. ssa. 
rewrite pred_domP in H4. 
apply (allP H1).
apply/in_filter_keys2. ssa. ssa. eauto.
apply/map_f. done. 
Qed.


Lemma weaken_some : forall E E' lk T f, weaken E f E' -> lk \in f -> lookup E lk = Some T -> lookup E' lk = Some T.
Proof. intros. rewrite /weaken in H. ssa. subst. 
apply lookup_filter2 in H1. ssa. 
Qed. 

Lemma weaken_some' : forall E E' lk T f, weaken E' f E -> lk \in f -> lookup E lk = Some T -> lookup E' lk = Some T.
Proof. intros. rewrite /weaken in H. ssa. subst. 
apply lookup_filter;ssa.
Qed. 



Lemma update_none : forall (A B : eqType) (E : seq (A * B)) k v, k \notin dom E -> update E k v = E.
Proof. 
move => A B. elim;ssa. rewrite inE in H0. rewrite negb_or in H0.
ssa. rifliad. norm_eqs. f_equal. eauto. 
Qed. 

Lemma weaken_update : forall E0 E' s T f, weaken E0 f E' -> f s -> weaken (update E0 s T) f (update E' s T).
Proof. 
intros. destruct H.  ssa. 
subst. 
rewrite /weaken. ssa. 
rewrite update_filter_keys //=.
apply/allP. intro. ssa. 
apply in_filter_keys in H. ssa.
de (eqVneq s x.1). subst. rewrite pheqs H0 //= in H.  
apply (allP H1). apply/in_filter_keys2.
apply in_update in H2. done.  intro. subst. rewrite eqxx in i. done. 
done. 
Qed. 


Lemma weaken_filter : forall E0 E' f p, weaken E0 f E' ->  weaken (filter_keys p E0) f (filter_keys p  E').
Proof. 
intros. destruct H.  ssa. subst. 
rewrite /weaken. ssa. 
rewrite !filter_keys2. apply/filter_keys_eq. intro. 
ssa. tunf. rewrite andbC //=.

rewrite !filter_keys2. apply/allP. intro. 
ssa. apply in_filter_keys in H. ssa. apply (allP H0). 
apply/in_filter_keys2. done. tunf. tunf_in H. ssa. 
Qed. 

Lemma weaken_dom : forall E f E', weaken E f E' -> (forall x, x \in dom E -> x \in f). 
Proof. intros. 
destruct H.  subst. 
rewrite dom_filter_keys mem_filter in H0. ssa.
Qed. 

Lemma lType_done_sub : forall (E : l_env) (p0 p1 : lkey -> bool),  lType_done (filter_keys p1 E) -> (forall x, p0 x -> p1 x) -> lType_done (filter_keys p0 E). 
Proof. 
intros. apply/allP. intro. ssa. apply in_filter_keys in H1. ssa.
apply (allP H). apply/in_filter_keys2. done.  eauto.
Qed. 

Lemma predIC : forall (A : eqType)  (p0 p1 : A -> bool), (predI p0 p1) = predI (p1) (p0) :> (A -> bool).
Proof. 
intros. fext. ssa. tunf. rewrite andbC //=. 
Qed. 

Lemma OFT_weaken : forall Ms Ds P E E' Q C f, OFT Ms Ds P E Q C -> weaken E f E' -> OFT Ms Ds P E' Q C.
Proof. 
move => Ms Ds P E E' Q C f H. 
elim : H E' f;ssa. 
- econ;eauto. apply/H5;eauto. 
  apply/weaken_insertL0. eauto.

- econ;eauto. apply/H4;eauto. 
  apply/weaken_insertL0. eauto.

- econ;eauto. 
  apply/weaken_some; eauto. apply/weaken_dom; eauto. 
  apply/H3. apply/weaken_update;eauto. apply/weaken_dom;eauto. 

- econ;eauto. 
  apply/weaken_some; eauto. apply/weaken_dom; eauto. 
  apply/H2. apply/weaken_update;eauto. apply/weaken_dom;eauto. 

- econ;eauto. 
  apply/weaken_some; eauto. apply/weaken_dom; eauto. 
  apply/weaken_some; eauto. apply/weaken_dom; eauto. 
  apply/H5. apply/weaken_filter. apply/weaken_update. eauto.
  apply/weaken_dom;eauto. 

- econ;eauto. 
  apply/weaken_some; eauto. apply/weaken_dom; eauto. 
  apply/H2. 
  apply/weaken_insertL0.
  apply/weaken_update. eauto.
  apply/weaken_dom;eauto. 

- econ;eauto. 
  apply/weaken_some; eauto. apply/weaken_dom; eauto. 
  apply/H3. 
  apply/weaken_update. eauto.
  apply/weaken_dom;eauto. 

- econ;eauto. 
  apply/weaken_some; eauto. apply/weaken_dom; eauto. 
  intros. apply/H3. eauto.
  apply/weaken_update. eauto.
  apply/weaken_dom;eauto. 


- inv H. inv H0. inv H1. remember H6. clear Heqw. inv H6. econ.
  4 : apply/H3. 5 : apply/H4. rewrite filter_keys2. 
  rewrite /partition. f_equal. apply/filter_keys_eq.
  intro. ssa. 
  instantiate (1 := predU f0 (predC f)). solve_ph. 
  econ. econ. econ. rewrite !filter_keys2. 
  apply/filter_keys_eq. intros. 
  instantiate (1 := f). solve_ph.
  rewrite filter_keys2. apply/lType_done_sub. eauto.
  intros. move : H7. solve_ph.

- econ;eauto. 
- econ. inv H1. apply/allP. intro. ssa. 
  destruct (x.1 \in f) eqn:Heqn.  apply(allP H0). inv H1.
  apply in_filter_keys2;ssa. inv H1.
  apply (allP H4). 
  apply in_filter_keys2;ssa. tunf. lia.

- econ. eauto. eauto.
- inv H6. inv H8. subst. econ. done. 2 : done. 2 : eauto. 2 : eauto. 2 : done. 
  3 : {   econ. } rewrite filter_keys2 in H0.  
  apply/allP. intro. ssa. apply in_filter_keys in H9.  ssa.
  destruct (f x.1) eqn:Heqn. 
  apply (allP H0). apply/in_filter_keys2;ssa. tunf. ssa.
  apply (allP H10). apply/in_filter_keys2;ssa.  tunf. rewrite Heqn //=. 
  rewrite dom_filter_keys in H5. 
  intro. ssa.  apply H5 in H9. rewrite mem_filter in H9. ssa.
  ssa. apply/H7. eauto.
  rewrite filter_keys2.
  apply lookup_filter2 in H11. ssa.
  apply lookup_filter;ssa. tunf.  ssa.
  apply H5 in H11. rewrite dom_filter_keys mem_filter in H11.  ssa.

- econ;eauto. inv H1. apply/allP. intro. ssa. 
  destruct (x.1 \in f) eqn:Heqn. apply (allP H). 
  apply in_filter_keys2;ssa.
  apply (allP H3). 
  apply in_filter_keys2;ssa. tunf. lia.

- econ;eauto. 

- econ;eauto. 
  apply/weaken_some; eauto. apply/weaken_dom; eauto. 
  apply/H3. apply/weaken_filter. eauto. 

- econ;eauto. 

- inv H2. econ;eauto. apply/H1. apply/weaken_insertL1. eauto.
Qed.

Lemma weaken_look : forall E E' f lk T, weaken E' f E -> lookup E lk = Some T -> T != EEnd -> lookup E' lk = Some T.
Proof.
intros. inv H.
destruct (f lk) eqn:Heqn;ssa.
apply lookup_filter. done. done.
rewrite /lType_done /filter_keys all_filter in H3.
apply in_pair in H0.
apply (allP H3) in H0. ssa. 
have : (predC f lk). simpl. rewrite /predC Heqn. done.
move/(implyP H0). move/eqP. move=>HH. 
rewrite HH eqxx //in H1.
Qed.

Lemma weaken_true : forall E E' f lk T, weaken E' f E -> lookup E lk = Some T -> T != EEnd -> f lk. 
Proof.
intros. eapply weaken_look in H as HH;eauto. inv H. apply lookup_filter2 in HH. ssa.
Qed.

Definition weakenq (Q : q_env) (f : pred qkey) (Q' : q_env) := filter_keys (f) Q' = Q /\ qType_done (filter_keys (predC f) Q'). 

Lemma weaken_qType_done : forall Q0 f Q', weakenq Q0 f Q' -> qType_done Q0 -> qType_done Q'.
Proof. 
intros. inv H.  apply/allP. intro. ssa. destruct (f x.1) eqn:Heqn;ssa.
apply (allP H0). apply/in_filter_keys2;ssa.
apply (allP H2). apply/in_filter_keys2;ssa. tunf. rewrite Heqn //=.
Qed.

Lemma qType_done_filter_q : forall q p, qType_done q ->  qType_done (filter_q q p). 
Proof.
intros.  move : H. rewrite /qType_done. 
rewrite /filter_q.
rewrite all_map. ssa. apply/allP. intro. ssa. 
apply (allP H) in H0 . norm_eqs. rewrite H0.  ssa. 
Qed. 

Lemma qType_done_map_imp : forall q f,  qType_done (map_keys f q) -> qType_done q. 
Proof. intros. rewrite qType_done_map_keys in H. done. Qed. 

Lemma qType_done_ff : forall (Q : q_env) p p', 
qType_done (filter_keys p Q) ->
qType_done ((filter_keys p (filter_q Q p'))).
Proof. 
intros. move : H. rewrite /qType_done /filter_keys /filter_q . 
rewrite !all_filter. rewrite !all_map. intro. 
apply/allP. intro. ssa.
apply/implyP. ssa. apply (allP H) in H0. ssa.
move/implyP : H0. move/(_ H1). move/eqP=>->.  ssa. 
Qed. 


Hint Resolve qType_done_map_imp qType_done_filter_q weaken_qType_done qType_done_ff.


Lemma filter_q_filter_keys : forall (Q : q_env) f p, filter_q (filter_keys f Q) p = filter_keys f (filter_q Q p).
Proof. 
intros. rewrite /filter_q /filter_keys.  
elim : Q;ssa. rifliad. ssa. f_equal.  done.   
Qed. 

Lemma in_filter_q : forall (Q : q_env) x f, x \in filter_q Q f -> x.1 \in dom Q. 
Proof. 
intros. rewrite /filter_q in H. destruct (mapP H). subst. 
apply/mapP.  exists x0.  ssa. done. 
Qed. 


Lemma weakenq_some : forall E E' lk T f, weakenq E f E' -> lk \in f -> lookup E lk = Some T -> lookup E' lk = Some T.
Proof. intros. rewrite /weakenq in H. ssa. subst. 
apply lookup_filter2 in H1. ssa. 
Qed. 


Lemma weakenq_dom : forall E f E', weakenq E f E' -> (forall x, x \in dom E -> x \in f). 
Proof. intros. 
destruct H.  subst. 
rewrite dom_filter_keys mem_filter in H0. ssa.
Qed. 

Lemma weakenq_update : forall E0 E' s T f, weakenq E0 f E' -> f s -> weakenq (update E0 s T) f (update E' s T).
Proof. 
intros. destruct H.  ssa. subst. 
rewrite /weakenq. ssa. 
rewrite update_filter_keys //=.
apply/allP. intro. ssa. 
apply in_filter_keys in H. ssa.
de (eqVneq s x.1). subst. tunf_in H. rewrite H0 in H. done.
apply (allP H1). apply/in_filter_keys2.
apply in_update in H2. done.  intro. subst. rewrite eqxx in i. done. 
done. 
Qed. 


Ltac tunf_hyp := match goal with
           | H : context [ is_true (pred0 _) ] |- _ => tunf_in H
           | H : context [ is_true (predT _) ] |- _ => tunf_in H
           | H : context [ is_true (predI _ _ _) ] |- _ => tunf_in H
           | H : context [ is_true (predU _ _ _) ] |- _ => tunf_in H
           | H : context [ is_true (predC _ _) ] |- _ => tunf_in H
           end.

Ltac ssa := (try tunf_hyp);(try tunf);MPSTSR.utils.ssa.
Ltac ssan := MPSTSR.utils.ssa.


Lemma weaken_insertQ : forall E0 f E' T, weakenq E0 f E' -> weakenq (insertQ E0 T) (predU is_qkey (pred_dom (dom E') shiftQ f)) (insertQ E' T).
Proof. ssa. 
rewrite /weakenq. inv H. 
ssa.
rewrite /insertQ /insert_shift /insert. 
rewrite filter_keys_cat. f_equal.
erewrite filter_keys_eq. erewrite filter_keys_predT. done.
ssa. rewrite /dom -map_comp in H0. destruct (mapP H0). subst. 
ssa. 

rewrite filter_keys_map_keys. f_equal.
apply/filter_keys_eq. intro. 
ssa. rewrite is_qkey_shift /=. rewrite pred_domP //=. eauto. 

rewrite /insertQ /insert_shift /insert. 
rewrite !filter_keys_cat.
rewrite /qType_done. rewrite all_cat. ssa. 
apply/allP.  intro.  ssa.
apply in_filter_keys in H0. ssa.  rewrite negb_or in H0. ssa.
eapply map_f in H2.
apply in_initQ in H2. rewrite H2 in H3. ssa.
apply/allP. intro. ssa.
apply in_filter_keys in H0. ssa. 
rewrite negb_or in H0. ssa.
destruct (mapP H2). subst. 
rewrite pred_domP in H4. ssa.
apply (allP H1).
apply/in_filter_keys2;ssa. de x0. eauto.
apply/map_f. done.
Qed. 


Lemma OFT_weaken2 : forall Ms Ds P E Q Q' C f, OFT Ms Ds P E Q C -> weakenq Q f Q' -> OFT Ms Ds P E Q' C.
Proof. 
move => Ms Ds P E Q Q' C f H. 
elim : H Q' f;ssa. 
- all : try solve [ econ;eauto]. 

- inv H. inv H0. inv H1. remember H6. clear Heqw. inv H6. econ.
  4 : apply/H3. 5 : apply/H5. econ. 
  rewrite /partition_q. econ.
  econ. eauto. econ. 
  rewrite filter_q_filter_keys. eauto. eauto.
  econ. 
  rewrite filter_q_filter_keys. eauto. 
  apply/qType_done_ff. done. 

- econ;eauto. apply/weakenq_some;eauto. apply/weakenq_dom;eauto.
  apply/H2;eauto. apply/weakenq_update;eauto.
  apply/weakenq_dom;eauto.

- econ;eauto. apply/weakenq_some;eauto. apply/weakenq_dom;eauto.
  apply/H3. apply/weakenq_update;eauto.
  apply/weakenq_dom;eauto.

- econ;eauto. apply/weakenq_some;eauto. apply/weakenq_dom;eauto.
  apply/H1. apply/weakenq_update;eauto.
  apply/weakenq_dom;eauto.

- inv H2. econ;eauto. apply/H1. apply/weaken_insertQ. eauto.
Qed. 




Lemma OFTV_weaken3 : forall Ms Ms' v S f, OFTV Ms v S  ->  filter_keys f Ms' = Ms ->  OFTV Ms' v S.
Proof. 
intros. subst. inv H. ssa. con.
apply lookup_filter2 in H0. ssa. con.
apply lookup_filter2 in H0. ssa. con. done.
Qed. 

Lemma OFTE_weaken3 : forall Ms Ms' v S f, OFTE Ms v S  -> filter_keys f Ms' = Ms ->  OFTE Ms' v S.
Proof. 
intros.
elim : H Ms' f H0;ssa. subst. econ. apply/OFTV_weaken3;eauto.
con;eauto. 
Qed. 



Lemma shiftS0_zero : forall x, shiftS0 x == var_valBool 0 = false.
Proof. 
ssa. destruct x;ssa. 
Qed. 

Lemma shiftS1_zero : forall x, shiftS1 x == (valB (var_val 0)) = false.
Proof. 
ssa. destruct x;ssa. asimpl. destruct v;ssa.
Qed. 





Lemma OFT_weaken3 : forall Ms Ds P E Q Ms' (f : pred skey) C, OFT Ms Ds P E Q C -> filter_keys f Ms' = Ms -> OFT Ms' Ds P E Q C.
Proof. 
move => Ms Ds P E Q Ms' f C H. 
elim : H Ms' f;ssa.

- econ;ssa;eauto. apply/OFTV_weaken3;eauto.
 - econ;ssa;eauto. apply/OFTV_weaken3;eauto.
- econ;ssa;eauto. apply/OFTE_weaken3;eauto.
- subst. econ;ssa;eauto. 
  apply/H2;eauto. 
  instantiate (1:= (predU (is_skey0) (pred_dom (dom Ms') shiftS0 f))). 
  rewrite /insertS0 /insert_shift /insert /=. f_equal.
  rewrite filter_keys_map_keys. f_equal.
  apply/filter_keys_eq. intro. ssa.
  rewrite is_skey0_shift //=. rewrite pred_domP //=. eauto.
- all : try solve [subst; econ;ssa;eauto]. 
- subst. inv H. inv H0. inv H1. econ;ssa;eauto. 
- subst. econ;ssa;eauto. apply/OFTE_weaken3;eauto.
- subst. econ;ssa;eauto. apply/H1. 
  instantiate (1:= (predU (is_skey1) (pred_dom (dom Ms') shiftS1 f))). 
  rewrite /insertS1 /insert_shift //=. f_equal. rewrite filter_keys_map_keys //=.
  f_equal. 
  apply/filter_keys_eq. intro. ssa.
  rewrite is_skey1_shift //=. rewrite pred_domP //=. eauto.

- subst. econ;eauto. apply/OFTE_weaken3;eauto.

- subst. econ;eauto. apply/OFTV_weaken3;eauto.
Qed. 

Lemma good_subst_shift : forall Ms,  good_subst Ms (↑ >> var_val) var_valBool.
Proof. intro. 
intro. ssa. inv H;eauto. asimpl.
con. 
apply/lookup_filter. ssa.
erewrite lookup_map_eq_inj. eauto. done. done. con.
asimpl. con. 
apply lookup_filter. done. 
erewrite lookup_map_eq_inj. eauto. done. done.
Qed. 

Lemma good_subst2_var : forall L,  good_subst2 L var_schl var_sch. 
Proof. intro. intro. ssa. asimpl in H1. done. Qed.

Lemma good_subst3_var : forall Q,  good_subst3 Q var_schl. 
Proof. intro. intro. ssa. de a. de a'. asimpl in H1. inv H1. 
Qed.  

Lemma subst_qkey_inj : injective (subst_qkey var_schl).
Proof. 
intros. intro. ssa. de x1. de x2. asimpl in H. inv H. 
Qed. 

Lemma subst_schli_inj : injective (subst_schli var_schl).
Proof. 
intros. intro. ssa. de x1. de x2. asimpl in H. inv H. 
Qed. 

Hint Resolve good_subst_shift good_subst2_var good_subst3_var subst_qkey_inj subst_schli_inj.


Definition only_vars (E : s_env) := all is_var (dom E).


Lemma predC2 : forall (A : eqType) (p : pred A), predC (predC p) = p.
Proof. 
intros. fext. ssa. rewrite negb_involutive. done.
Qed. 

Lemma hrelC2 : forall (A B : eqType) (p : hrel A B), hrelC (hrelC p) = p.  
Proof. 
intros. fext. ssa. rewrite /hrelC.  rewrite negb_involutive. done.
Qed. 

Lemma predC_predI : forall (A : eqType)  (p0 p1 : A -> bool), predC (predI p0 p1) = predU (predC p0) (predC p1) :> (A -> bool).
Proof. 
intros. fext. ssa. rewrite negb_and //=.  
Qed. 

Lemma predUC : forall (A : eqType)  (p0 p1 : A -> bool), (predU p0 p1) = predU (p1) (p0) :> (A -> bool).
Proof. 
intros. fext. ssa. rewrite orbC //=. 
Qed. 



Lemma predIUC : forall (A : eqType) (p0 p1  : A -> bool), predI p0 (predU (predC p0) p1) = predI p0 p1 :> (A -> bool).
Proof. 
intros. fext.  ssa.  destruct (p0 x ) eqn:heqn;ssa.
Qed. 

Lemma predIUC2 : forall (A : eqType) (p0 p1  : A -> bool), predI p0 (predU p1 (predC p0)) = predI p0 p1 :> (A -> bool).
Proof. 
intros. fext.  ssa.  destruct (p0 x ) eqn:heqn;ssa. lia. 
Qed. 

Lemma predICI : forall (A : eqType) (f3 f0  : A -> bool), (predI f0 (predC (predI f3 f0))) = predI (predC f3) f0 :> (A -> bool).
Proof. 
intros. fext.  ssa.  rewrite negb_and. lia. 
Qed. 

Lemma predICC : forall (A : eqType) (f0 f3 : A -> bool),(predI (predC f0) (predC (predI f3 f0))) =  (predC f0) :> (A -> bool).
Proof. 
intros. fext. ssa. destruct (f0 x) eqn:Heqn;ssa. rewrite negb_and orbC //=.
Qed. 



Lemma filter_lkey1C : forall E E1, (filter_keys (predC is_lkey1) (insertL1 E E1)) = map_keys shiftL1 E. 
Proof. 
intros. rewrite /insertL1 /insert_shift /insert. ssa.
rewrite filter_keys_cat. 
erewrite filter_keys_eq.
erewrite filter_keys_pred0. simpl.
erewrite filter_keys_eq.  erewrite filter_keys_predT. done.
ssa. rewrite /dom -map_comp in H. destruct (mapP H).  ssa. subst. 
rewrite is_lkey1_shift //=.
ssa. rewrite /dom -map_comp in H. destruct (mapP H).  subst. 
de x0. 
Qed. 

Lemma filter_qkeyC : forall E E1, (filter_keys (predC is_qkey) (insertQ E E1)) = map_keys shiftQ E. 
Proof. 
intros. rewrite /insertQ /insert_shift /insert. ssa.
rewrite filter_keys_cat. 
erewrite filter_keys_eq.
erewrite filter_keys_pred0. simpl.
erewrite filter_keys_eq.  erewrite filter_keys_predT. done.
ssa. rewrite /dom -map_comp in H. destruct (mapP H).  ssa. subst. 
rewrite is_qkey_shift //=.
ssa. rewrite /dom -map_comp in H. destruct (mapP H).  subst. 
de x0. 
Qed. 

Lemma filter_ckeyC : forall E E1, (filter_keys (predC is_ckey) (insertC E E1)) = map_keys shiftC E. 
Proof. 
intros. rewrite /insertC /insert_shift /insert. ssa.
rewrite filter_keys_cat. 
erewrite filter_keys_eq.
erewrite filter_keys_pred0. simpl.
erewrite filter_keys_eq.  erewrite filter_keys_predT. done.
ssa. rewrite /dom -map_comp in H. destruct (mapP H).  ssa. subst. 
de x0.
rewrite is_ckey_shift //=.
ssa. rewrite /dom -map_comp in H. destruct (mapP H).  subst. 
de x0. 
Qed. 

Lemma filter_q_cat : forall (l0 l1 : q_env) f, filter_q (l0 ++ l1) f = filter_q l0 f ++ filter_q l1 f.
Proof. 
intros. rewrite /filter_q map_cat //=.  
Qed. 


Lemma filter_q_predT : forall (l  : q_env), filter_q l (fun q => predT) = l.
Proof. intros. rewrite /filter_q. 
symmetry. rewrite -{1}(@map_id _ l).
apply/eq_in_map. intro. ssa. rewrite filter_keys_predT //=. de x.
Qed. 




Lemma filter_q_insertQ_f_aux : forall (Q : q_env) Q2 f1,
 (filter_q (insertQ Q Q2) (fun (q : qkey) (c : ch) => is_qkey q || pred_dom2 (dom Q) shiftQ f1 q c)) =
 (insertQ (filter_q Q f1) Q2).
Proof. 
intros. 
rewrite /insertQ /insert_shift /insert. ssa.
rewrite !filter_q_cat. f_equal.
erewrite filter_q_eq. erewrite filter_q_predT. done.
intros. ssa. rewrite /dom -map_comp in H. destruct (mapP H). 
subst.  fext. intro. ssa. 
rewrite filter_q_map_keys. f_equal.
apply/filter_q_eq. ssa.
rewrite pred_dom2P. 
rewrite is_qkey_shift //=. done. done.
Qed.

Lemma filter_q_insertQ_f : forall (Q : q_env) Q2 f1, (insertQ (filter_q Q f1) Q2) =
 (filter_q (insertQ Q Q2) (fun (q : qkey) (c : ch) => is_qkey q || pred_dom2 (dom Q) shiftQ f1 q c)).
Proof. 
intros. rewrite filter_q_insertQ_f_aux. done.
Qed. 


Lemma filter_keys_insertC_f_aux : forall E E1 f0, (filter_keys (predU (is_ckey) (pred_dom (dom E) shiftC f0))  (insertC E E1)) =
 (insertC (filter_keys f0 E) E1). 
Proof. 
intros. 
rewrite /insertC /insert_shift /insert. ssa.
rewrite !filter_keys_cat. f_equal.
erewrite filter_keys_eq. erewrite filter_keys_predT. done.
intros. ssa.
rewrite /dom -map_comp in H. destruct (mapP H). subst. 
ssa. 
rewrite filter_keys_map_keys. f_equal.
apply/filter_keys_eq. ssa.
rewrite pred_domP. 
rewrite is_ckey_shift //=. apply/injective_atP.
done. done.
Qed. 

Lemma filter_keys_insertC_f : forall E E1 f0, (insertC (filter_keys f0 E) E1) = (filter_keys (predU (is_ckey) (pred_dom (dom E) shiftC f0))  (insertC E E1)).
Proof. 
intros. rewrite filter_keys_insertC_f_aux. done.
Qed. 

Lemma filter_keys_predC_ckey: forall (E : c_env) (f0 : ckey -> bool), (filter_keys (predC (predU is_ckey (pred_dom (dom E) shiftC f0)))) (map_keys shiftC E) = map_keys shiftC (filter_keys (predC f0) E).
Proof. 
intros. rewrite filter_keys_map_keys. f_equal. 
apply filter_keys_eq. 
ssa. rewrite pred_domP. rewrite is_ckey_shift //=. eauto.
done. 
Qed. 

Lemma filter_keys_predC_skey1: forall (E : s_env) (f0 : skey -> bool), (filter_keys (predC (predU is_skey1 (pred_dom (dom E) shiftS1 f0)))) (map_keys shiftS1 E) = map_keys shiftS1 (filter_keys (predC f0) E).
Proof. 
intros. rewrite filter_keys_map_keys. f_equal. 
apply filter_keys_eq. 
ssa. rewrite pred_domP. rewrite is_skey1_shift //=. eauto.
done. 
Qed. 


Lemma subst_l_env_id : forall E, subst_l_env E var_schl var_sch = E. 
Proof. 
intros. rewrite /subst_l_env. elim : E;ssa. 
f_equal. asimpl. destruct a;ssa. 
done. 
Qed. 

Lemma subst_q_env_id : forall E, subst_q_env E var_schl = E. 
Proof. 
intros. rewrite /subst_q_env. elim : E;ssa. 
f_equal. asimpl. destruct a;ssa. rewrite /subst_qkey. de q.  de s. done.
Qed. 



Lemma subst_qkey_id : subst_qkey var_schl = ssrfun.id.
Proof. 
intros. fext. case;ssa. asimpl. done. 
Qed. 

Lemma subst_schli_id : subst_schli var_schl = ssrfun.id.
Proof. 
intros. fext. case;ssa. asimpl. done. 
Qed. 

Lemma filter_q_none 
     : forall (Q : q_env)  (p : qkey -> ch -> bool), qType_done (filter_q Q (fun q => predC (p q))) -> filter_q Q p = Q.
Proof. 
ssa. move : H. rewrite /filter_q /qType_done all_map. ssa. 
rewrite -{2}(@map_id _ Q). apply/eq_in_map. intro. ssa. 
apply (allP H) in H0. ssa.
rewrite filter_none. de x. rewrite (eqP H0). done. 
Qed.

Lemma filter_q2 : forall (Q : q_env) (p0 p1 : hrel qkey ch), filter_q (filter_q Q p0) p1 = 
filter_q Q (hrelI p0 p1). 
Proof. 
intros. 
rewrite /filter_q. rewrite -!map_comp. apply/eq_in_map. 
intro. ssa. rewrite /predI //=.  f_equal. rewrite filter_keys2. 
apply/filter_keys_eq. intro. ssa. rewrite /hrelI. lia. 
Qed. 


Lemma filter_cancel_insertQ : forall (Q : q_env) Q2 f1,
 (filter_q (insertQ Q Q2) (hrelC (fun q c => is_qkey q || pred_dom2 (dom Q) shiftQ f1 q c))) =
 (map (fun p => (QKey (var_schl 0) p,nil)) (dom Q2)) ++ (map_keys shiftQ (filter_q Q (fun q : qkey => predC (f1 q)))).
Proof. 
intros.
rewrite /insertQ /insert_shift /insert //=. 
rewrite /filter_q /map_keys  -!map_comp !map_cat.
rewrite -!map_comp.  f_equal. 
apply/eq_in_map. intro. ssa. erewrite filter_keys_eq. erewrite filter_keys_pred0. done.
ssa. 

apply/eq_in_map. intro. ssa.  f_equal. 
apply/filter_keys_eq. intro. ssa. rewrite is_qkey_shift pred_dom2P //=. apply/map_f. done.
Qed. 

Lemma hrelICI : forall (A B : Type) (f1 f4 : hrel A B), hrelI (hrelC (hrelI f1 f4)) f1 = hrelI f1 (hrelC f4).
Proof. 
intros. fext.  ssa.
rewrite /hrelI /hrelC. ssa. lia. 
Qed. 

Lemma OFT_match : forall Ms Ds P E Q C Ms' E' Q' C', OFT Ms Ds P E Q C -> Ms = Ms' -> E = E' -> Q = Q' -> C = C' ->
  OFT Ms' Ds P E' Q' C'. 
Proof. ssa. subst. done.
Qed. 




Inductive Cong2 : process -> process -> Prop := 
 | C2Inact P : Cong2 (Par P Inact) P
 | C2ParCom P Q : Cong2 (Par P Q) (Par Q P)
 | C2ParAss P Q R : Cong2 (Par (Par P Q) R) (Par P (Par Q R))
 | C2ResCh P Q : Cong2 (Par (ResCh P) Q) (ResCh (Par P (shift_sch Q)))
 | C2ResN P Q:  Cong2 (Par (ResVal P) Q) (ResVal (Par P (shift_val Q)))
 | C2ResChI : Cong2 (ResCh Inact) Inact
 | C2ResNI : Cong2 (ResVal Inact) Inact
 | C2Ref P : Cong2 P P.

Lemma OFT_cong2 : forall Ms Ds P P' E Q C, OFT Ms Ds P E Q C -> only_vars Ms -> Cong2 P P' -> OFT Ms Ds P' E Q C. 
Proof. 
intros. move : H0=>Hvar. move:H1 => H0. elim : H0 H Hvar;intros. 
- inv H. inv H2. inv H3. inv H4. inv H11.  
  rewrite filter_q_none in H7.
  move : (@filter_none _ _ C _ H0)=><-.
  apply/OFT_weaken. apply/H7. econ. eauto. done. eauto.

- inv H. inv H2. inv H3. inv H4. econ. 
  instantiate (3 := predC f0). econ. 
  instantiate (3 := hrelC f1). econ. 
  instantiate (3 := predC f2). econ. 
  eauto. rewrite !predC2 //=.
  erewrite filter_q_eq.
  intros. 2 : { intros. rewrite hrelC2. eauto. } eauto. 

- inv H. inv H2. inv H3. inv H4. inv H7.
  inv H5. inv H6. inv H8. 
  rewrite !filter_keys2 !filter_q2 in H12. 
  rewrite !filter_keys2 !filter_q2 in H16. econ.
  instantiate (3 := predI f3 f0). econ. 
  instantiate (3 := (hrelI f1 f4)). econ.
  instantiate (3 := predI f5 f2). econ. eauto. econ.
  econ. econ. econ. rewrite !filter_keys2. rewrite filter_q2.
  erewrite filter_keys_eq.
  erewrite filter_q_eq.
  erewrite (@filter_keys_eq _ _ C). apply/H16.
  intros. instantiate (1 := f2). solve_ph.
  intros. instantiate (1 := f1). solve_ph. 
  intros. instantiate (1 := f0). solve_ph.
  rewrite !filter_keys2. rewrite filter_q2.
  erewrite filter_keys_eq.
  erewrite filter_q_eq.
  erewrite (@filter_keys_eq _ _ C). apply/H11.
  intros. solve_ph.
  intros. solve_ph. 
  intros. solve_ph.

- inv H. inv H2. inv H3. inv H4. inv H7. 
  econ. eauto. econ. econ. econ. econ.
  apply/OFT_match;eauto. 
  
  erewrite filter_keys_insertL1_f. apply/filter_keys_eq.
  intros.  econ. 
  erewrite filter_q_insertQ_f. apply/filter_q_eq.
  intros. econ.
  erewrite filter_keys_insertC_f. apply/filter_keys_eq.
  intros. econ.
  apply/OFT_weaken2. apply/OFT_subst; eauto. 
  rewrite s_env_subst_id //=.  
  erewrite filter_keys_cancel_insertL1. done. 
  erewrite filter_keys_cancel_insertC. done. 
  econ. 
  erewrite filter_cancel_insertQ.
  instantiate (1 := predC is_qkey).
  rewrite filter_keys_cat.
  erewrite filter_keys_eq. erewrite filter_keys_pred0. simpl.
  rewrite filter_keys_map_keys. f_equal.
  erewrite filter_keys_eq. erewrite filter_keys_predT. 
  apply/filter_q_eq. intro. ssa. intros. ssa. 
  rewrite is_qkey_shift //=.
  ssa. erewrite in_initQ. done. 
  rewrite /initQ. move : H0. rewrite /dom -!map_comp. ssa.
  rewrite -!map_comp. eauto.
  rewrite predC2.
  rewrite filter_cancel_insertQ filter_keys_cat. 
  erewrite filter_keys_eq. erewrite filter_keys_predT.
  erewrite filter_keys_eq. erewrite filter_keys_pred0. rewrite cats0.
  rewrite /qType_done all_map. ssa. apply/allP. intro. ssa.
  ssa. rewrite /dom -!map_comp in H0. ssa.
  de (mapP H0). subst. rewrite is_qkey_shift //=.
  ssa. rewrite /dom -!map_comp in H0. ssa.
  de (mapP H0). subst. ssa. 


- asimpl. inv H. inv H2. inv H3. inv H4. inv H7.
  econ. eauto. econ. apply/H2. apply/H3. apply/H4. eauto.
  apply/OFT_weaken3. apply/OFT_subst.  eauto. done. done. 
  apply/injective_atP. eauto. apply/injective_atP. eauto.
eauto.
  rewrite subst_sch_id2. rewrite map_keys_id //=.
  rewrite subst_qkey_id map_keys_id //=.
  rewrite subst_schli_id map_keys_id //=.
  instantiate (1 := predI (predC is_skey1) is_var). rewrite /insertS1 /insert_shift /=. 
  rewrite /s_env_subst.   apply/filter_keys_eq. intro. 
  ssa. rewrite /dom -map_comp in H0. destruct (mapP H0). subst. ssa.
  rewrite is_skey1_shift //=.

- inv H. inv H4. rewrite /insertQ /insert_shift /insert in H0.
  rewrite /insertC in H0. de C;de C1. econ.
  rewrite /insertQ /insert_shift /insert in H2.
  move : H2. rewrite /qType_done all_cat all_map /map_keys all_map. ssa. 
  rewrite /insertL1 /insert_shift /insert in H6.
  move : H6. rewrite /lType_done all_cat all_map /map_keys all_map. ssa. 

- inv H. inv H4. econ. done. done.

- eauto.
Qed. 


Definition schl_fv (c : sch) :=
match c with 
| schlT (var_schl n) _ => n::nil
| var_sch n => nil
end. 

Definition msgp_schl_fv (m : msgp) := 
match m with 
| msgT (schM c) _ => schl_fv c
| _ => nil 
end.


Definition schli_schl_fv (sc : schli) :=
match sc with 
| schliT (var_schl n) _ => n::nil
end.

Fixpoint proc_schl_fv (P : process) := 
match P with 
| SessReq a b q P0 =>  proc_schl_fv P0
| SessAcc a b P0=>  proc_schl_fv P0 
| ValSend a b c P0=> (schl_fv a)++ proc_schl_fv P0
| ValRec a b P0=> (schl_fv a)++( proc_schl_fv P0)
| SessDel a b c P0=>  (schl_fv a)++(schl_fv c)++(proc_schl_fv P0)
| SessRec a b P0 => (schl_fv a)++ (proc_schl_fv P0)
| LabelSel a b c P0=>  (schl_fv a)++(proc_schl_fv P0)
| LabelBr a b Ps => (schl_fv a)++(flatten (map (snd>>proc_schl_fv) Ps))
| If a P0 P1=>  (proc_schl_fv P0) ++  (proc_schl_fv P1)
| Par P0 P1 => (proc_schl_fv P0) ++  (proc_schl_fv P1)
| Inact => nil
| ResCh P0 => (map predn (filter (fun n => n != 0) (proc_schl_fv P0)))
| ResVal P0 =>  proc_schl_fv P0 
| PCall a b c=> flatten (map schl_fv c)
| MsgQ a b => (schli_schl_fv a) ++ (flatten (map msgp_schl_fv b))
end. 


Lemma lookup_insertL0_schl : forall E T n p, lookup (insertL0 E T) (schlT (var_schl n) p) = lookup E (schlT (var_schl n) p).
Proof.
intros. rewrite /insertL0 /insert_shift /insert /= lookup_cons_neq //= lookup_shiftL0_id //.
Qed.

Lemma lookup_update_neq : forall (A B : eqType) (l : seq (A * B)) k v k' y, lookup l k' = Some y  ->  k<> k' -> lookup (update l k v) k' = Some y.
Proof. 
move=> A B. elim;ssa.
apply lookup_or in H0. de H0. 
ssa. subst. rifliad. norm_eqs. done. 
norm_eqs. rewrite lookup_cons_eq. 
done. done. rifliad. norm_eqs. rewrite lookup_cons_neq.  eauto.  ssa.
rewrite lookup_cons_neq.  eauto. done. 
Qed. 

Lemma lookup_update_neq2 : forall (A B : eqType) (l : seq (A * B)) k v k' y,  lookup (update l k v) k' = Some y ->   k<> k' -> lookup l k' = Some y.
Proof.  
move=> A B. elim;ssa.
move : H0. rifliad. norm_eqs. rewrite lookup_cons_neq. ssa.
rewrite lookup_cons_neq.  eauto.  apply/eqP. done.  ssa.
apply/eqP. done.
de (eqVneq a.1 k').  subst.  rewrite lookup_cons_eq.  
rewrite lookup_cons_eq in H2.  inv H2.  done. done.
rewrite lookup_cons_neq.
rewrite lookup_cons_neq in H2.  eauto. done. done. 
Qed.

Lemma lookup_filter3 :
  forall (A B : eqType) (l : seq (A * B)) (k : A) (p : pred A),
  p k -> lookup (filter_keys p l) k = lookup l k.
Proof.
intros. destruct (lookup (filter_keys p l) k) eqn:Heqn.
apply lookup_filter2 in Heqn. ssa.
destruct (lookup l k) eqn:Heqn2;ssa.
eapply lookup_filter in Heqn2. erewrite Heqn in Heqn2. done. done.
Qed.

Fixpoint proc_pred (p : process) := 
match p with 
| SessReq _ _ _ p0 => proc_pred p0
| SessAcc _ _ p0 => proc_pred p0
| ValSend _ _ _ p0 => proc_pred p0 
| ValRec _ _ p0 => proc_pred p0
| SessDel _ _ _ p0 => proc_pred p0 
| SessRec _ _ p0 => proc_pred p0 
| LabelSel _ _ _ p0 => proc_pred p0
| LabelBr _ _ Ps => (0 < size Ps) && (all (snd >> proc_pred) Ps)
| If _ p0 p1 => (proc_pred p0) && (proc_pred p1)
| Par p0 p1 => (proc_pred p0) && (proc_pred p1)
| Inact => true 
| ResCh p0 => proc_pred p0 
| ResVal p0 => proc_pred p0
| PCall _ _ ss => true
| MsgQ _ _ => true
end.


Lemma lookup_cat : forall (A B : eqType) (l l' : seq (A * B)) lk, lk \notin dom l -> lookup (l ++ l') lk  = lookup l'  lk.
Proof.
move=> A B. elim;ssa.
rewrite inE negb_or in H0. ssa.
rewrite lookup_cons_neq //;ssa. rewrite neg_sym. done.
Qed.

Lemma lookup_cat2 : forall (A B : eqType) (l l' : seq (A * B)) lk, lk \in dom l -> lookup (l ++ l') lk  = lookup l  lk.
Proof.
move=> A B. elim;ssa.
rewrite inE in H0. 
destruct (eqVneq lk a.1). ssa.
rewrite !lookup_cons_eq //;ssa.
rewrite !lookup_cons_neq //;ssa. 
rewrite neg_sym. done. rewrite neg_sym. done.
Qed.

Lemma lookup_shiftL0_succ:
  forall (E0 : l_env) n, lookup (map_keys shiftL0 E0) (var_sch n.+1) = lookup E0 (var_sch n).
Proof.
elim;ssa.
destruct (eqVneq a.1 (var_sch n)). rewrite !lookup_cons_eq. done. done. ssa. 
de a. subst. done.
rewrite !lookup_cons_neq //=. apply/eqP. intro. de a. de l0. asimpl in H0. inv H0. 
rewrite eqxx in i. done.
Qed.


Lemma lookup_insertL0_succ : forall E0 T n, lookup (insertL0 E0 T) (var_sch n.+1) = lookup E0 (var_sch n). 
Proof.
intros. rewrite /insertL0 /insert_shift /insert. ssa.
rewrite !lookup_cons_neq. ssa. 
rewrite lookup_shiftL0_succ.
done. ssa.
Qed.

Lemma lookup_insertL1_succ : forall E0 E1 n p, lookup (insertL1 E0 E1) (schlT (var_schl n.+1) p) = lookup E0 (schlT (var_schl n) p). 
Proof.
intros. rewrite /insertL1 /insert_shift /insert. ssa.
rewrite !lookup_cat. elim: E0.  ssa.
ssa. destruct (eqVneq a.1 (schlT (var_schl n) p)). rewrite e. rewrite !lookup_cons_eq //.
rewrite !lookup_cons_neq. ssa. done. ssa.
apply/eqP. intro. de a. de l0. de s. asimpl in H0. inv H0.
rewrite eqxx in i. done.
apply/negP. intro. de (mapP H). de (mapP H0). subst.
de x0.
Qed.

Lemma lookup_insertQ_succ : forall E0 E1 n p, lookup (insertQ E0 E1) (QKey (var_schl n.+1) p) = lookup E0 (QKey (var_schl n) p). 
Proof.
intros. rewrite /insertQ /insert_shift /insert. ssa.
rewrite !lookup_cat. elim: E0.  ssa.
ssa. destruct (eqVneq a.1 (QKey (var_schl n) p)). rewrite e. rewrite !lookup_cons_eq //.
rewrite !lookup_cons_neq. ssa. done. ssa.
apply/eqP. intro. de a. de q. de s. asimpl in H0. inv H0.
rewrite eqxx in i. done.
apply/negP. intro. de (mapP H). de (mapP H0). subst.
de x0.
Qed.

Lemma proc_fv_delta : forall Ms Ds P E Q C n p T, OFT Ms Ds P E Q C -> lookup E (schlT (var_schl n) p) = Some T -> n \notin proc_schl_fv P -> proc_pred P ->  fe T = EEnd.
Proof.
move=> Ms Ds P E Q C n p T Hoft.
move : Hoft n p T. elim;intros.
- ssa. apply (H5 n0 p). by rewrite lookup_insertL0_schl //. done. done.
- ssa. apply (H4 n p0). by rewrite lookup_insertL0_schl //. done. done.
- ssa. rewrite mem_cat negb_or in H5. ssa.
  apply (H3 n p). erewrite lookup_update_neq. eauto. done. 
  intro. subst. by rewrite /= inE eqxx in H7. done. done.
- ssa. rewrite mem_cat negb_or in H4. ssa.
  apply (H2 n p). erewrite lookup_update_neq. eauto. done. 
  intro. subst. move: H6. by rewrite /= inE eqxx. done. done.
- ssa. rewrite !mem_cat !negb_or in H7. ssa.
  apply (H5 n p).  rewrite /remove. 
  rewrite lookup_filter3. erewrite lookup_update_neq. eauto. done.
  intro. subst. move: H9.
  by rewrite /= inE eqxx. 
  apply/eqP. intro. subst. move: H7.
  by rewrite /= inE eqxx. done. done.
- ssa. rewrite !mem_cat !negb_or in H4. ssa.
  apply (H2 n p).  
  rewrite lookup_insertL0_schl.
  erewrite lookup_update_neq. eauto. done. intro. subst. move: H6.
  by rewrite /= inE eqxx. done. done.
- ssa. rewrite mem_cat negb_or in H5. ssa. 
  apply (H3 n p);ssa. erewrite lookup_update_neq. eauto. done.
  intro. subst. move: H7. by rewrite !inE eqxx.
- ssa. rewrite mem_cat negb_or in H5. ssa. 
  de Ps. de Ts. inv H0.
  apply:H3. eauto.
  erewrite lookup_update_neq. eauto. eauto.
  intro. subst.  move: H6.
  by rewrite inE eqxx. 
  rewrite !mem_cat !negb_or in H9. ssa.
  rewrite !mem_cat !negb_or in H9. ssa.
- ssa. rewrite mem_cat negb_or in H7. ssa.
  inv H.
  destruct (f0 (schlT (var_schl n) p)) eqn:Heqn.
  apply (H3 n p). rewrite lookup_filter3. done. done. done. done.
  apply (H5 n p). rewrite lookup_filter3. done. tunf. by apply/negbT=>//. done. done.
- ssa. rewrite mem_cat negb_or in H6. ssa.
  eauto.
- ssa. apply in_pair in H1. apply (allP H0) in H1. 
  move/eqP : H1. ssa. subst. done.
- ssa. eauto.
- ssa. inv H6. eapply lookup_filter in H8. 
  apply in_pair in H8.
  apply (allP H0) in H8. ssa. move/eqP : H8=>-> //.
  tunf. apply/negP. intro. apply/negP. apply/H9. apply/flattenP. econ.
  instantiate (1:= ([::n])). ssa. apply/mapP. econ. eauto. done. done.
- ssa. apply in_pair in H1. apply (allP H) in H1. ssa. move/eqP : H1=>->//.
- ssa. apply (H2 n p0). eauto. done. done.
- ssa. rewrite !mem_cat !negb_or in H5. ssa.
  apply (H3 n p0).
  rewrite /remove. rewrite lookup_filter3. eauto. 
  apply/eqP. intro. subst. ssa.
  move: H5. by rewrite !inE eqxx //.  rewrite mem_cat negb_or. ssa. done.
- ssa. apply (H1 n0 p0). eauto. done. done.
- ssa. 
  apply (H1 n.+1 p);eauto.
  rewrite lookup_insertL1_succ //.
  apply/negP. intro. apply/negP.  apply:H3.
  apply/mapP. econ. rewrite mem_filter. apply/andP. con. 2:eauto. done. done.
Qed.

Lemma lookup_filter_q_3 : forall (Q : q_env) s p l f, lookup Q  (QKey s p) = Some l -> 
lookup (filter_q Q f) (QKey s p) = Some (filter_keys (f (QKey s p)) l).
Proof.
elim;ssa.  de (eqVneq a.1 (QKey s p)). 
rewrite lookup_cons_eq in H0. rewrite lookup_cons_eq. f_equal. ssa. rewrite e. inv H0.
 ssa. done.
ssa. rewrite lookup_cons_neq.  eauto.
rewrite lookup_cons_neq in H0. eauto. done. ssa.
Qed. 

Lemma filter_keys_both_nil : forall (A B : eqType) (f : A -> bool) (l : seq (A * B)), filter_keys f l = nil -> filter_keys (predC f) l = nil -> l = nil.
Proof.
move=> A B f. elim;ssa.
destruct (f a.1) eqn:Heqn;ssa.
Qed.

Lemma lookup_update_in : forall (A B : eqType) (l : seq ( A * B)) (k : A)  v, k \in dom l -> lookup (update l k v) k = Some v.
Proof. 
move => A B. elim;ssa.
rewrite inE in H0. de (orP H0).  norm_eqs. rewrite eqxx. rewrite lookup_cons_eq.
done. done. 
rifliad.  norm_eqs. rewrite lookup_cons_eq.  ssa. ssa.
rewrite lookup_cons_neq.  eauto. apply/eqP. intro. subst. 
rewrite eqxx in H2. done.
Qed. 

Lemma proc_fv_Q : forall Ms Ds P E Q C n p T, OFT Ms Ds P E Q C -> lookup Q (QKey (var_schl n) p) = Some T -> n \notin proc_schl_fv P -> proc_pred P ->  T = nil.
Proof.
move=> Ms Ds P E Q C n p T Hoft.
move : Hoft n p T. elim;intros.
- ssa. apply (H5 n0 p)=>//. 
- ssa. apply (H4 n p0)=>//. 
- ssa. rewrite mem_cat negb_or in H5. ssa. by eauto.
- ssa. rewrite mem_cat negb_or in H4. ssa. by eauto.
- ssa. rewrite !mem_cat !negb_or in H7. ssa. by eauto.
- ssa. rewrite !mem_cat !negb_or in H4. ssa. by eauto.
- ssa. rewrite mem_cat negb_or in H5. ssa. by eauto.
- ssa. rewrite mem_cat negb_or in H5. ssa. 
  de Ps. de Ts. inv H0.
  apply:H3. eauto. eauto. 
  rewrite !mem_cat !negb_or in H9. ssa.
  rewrite !mem_cat !negb_or in H9. ssa.
- ssa. rewrite mem_cat negb_or in H7. ssa. 
  inv H0. 
  eapply lookup_filter_q_3 in H6 as HH0.
  eapply lookup_filter_q_3 in H6 as HH1.
  apply H3 in HH0. apply H5 in HH1.
  apply/filter_keys_both_nil. by apply HH0. by eauto. done. done. done. done.
- ssa. rewrite mem_cat negb_or in H6. ssa. eauto.
- ssa. apply in_pair in H1. apply (allP H) in H1. ssa. by apply/eqP=>//.
- ssa. eauto.
- ssa. apply in_pair in H8. apply (allP H) in H8. ssa. by apply/eqP=>//.
- ssa. apply in_pair in H1. apply (allP H0) in H1. by apply/eqP=>//.
- ssa. rewrite mem_cat negb_or in H4. ssa. 
  apply (H2 n p0). 
  erewrite lookup_update_neq. eauto. done.
  intro. inv H4. move: H6. by rewrite !inE eqxx.
  rewrite mem_cat negb_or. ssa. done.
- ssa. rewrite !mem_cat !negb_or in H5. ssa. 
  apply (H3 n p0). 
  erewrite lookup_update_neq. eauto. done.
  intro. inv H8. move: H7. by rewrite !inE eqxx.
  rewrite mem_cat negb_or. ssa. done.
- ssa. rewrite !mem_cat !negb_or in H3. ssa. 
  apply (H1 n0 p0). 
  erewrite lookup_update_neq. eauto.  done.
  intro. inv H3. 
  move: H5. by rewrite !inE eqxx.
  rewrite mem_cat negb_or. ssa. done.
- ssa. apply:H1. instantiate (1:= p). instantiate (1:= n.+1). 
  rewrite lookup_insertQ_succ. done.
  apply/negP. intro. apply/negP. apply:H3. apply/mapP. econ.
  rewrite mem_filter. apply/andP. con. 2:eauto. done. done.
  done.
Qed.

Lemma proc_fv_C : forall Ms Ds P E Q C n p, OFT Ms Ds P E Q C -> n \notin proc_schl_fv P -> proc_pred P -> schliT (var_schl n) p \notin (dom C).
Proof.
move=> Ms Ds P E Q C n p Hoft. move : Hoft n p.
elim;ssa.
- rewrite mem_cat negb_or in H6. ssa. inv H1.
  destruct (f2 (schliT (var_schl n) p)) eqn:Heqn;ssa.
  apply/negP. intro. apply/negP. eapply H3. apply H7. done. 
  rewrite dom_filter_keys. rewrite mem_filter. ssa. eauto. eauto.
  
  apply/negP. intro. apply/negP. eapply H5. apply H10. done. 
  rewrite dom_filter_keys. rewrite mem_filter. ssa. erewrite Heqn. done. done.
- rewrite mem_cat negb_or /= andbC /= in H1. 
  apply/negP. intro. apply/negP. apply:H1. 
  rewrite inE in H3. norm_eqs. ssa.
- rewrite !mem_cat !negb_or in H4. ssa.
  apply/negP. intro. apply/negP. eapply H3. rewrite mem_cat negb_or. ssa. eauto. done. done. eauto.
- have : n.+1 \notin proc_schl_fv P0.
  intros. apply/negP. intro. apply/negP. apply:H2. 
  apply/mapP. econ. rewrite mem_filter. apply/andP. con. 2:eauto. done. done.
  intro. eapply H1 in x. 2:done. 
  move: x. instantiate (1:= p).
  rewrite /dom /insertC /insert_shift. 
  intro. apply/negP. intro. apply/negP. apply:x.
  apply/mapP.
  de (mapP H4).
  econ. rewrite /insert mem_cat. apply/orP. right.
  apply/mapP. econ. eauto. econ. ssa. de x0. de s. de s.  asimpl.
  inv H6.
Qed.

  

  
Lemma filter_q_eq2 : forall (Q : q_env) (f0 f1 : hrel qkey ch), (forall x y z, (x,y) \in Q -> z \in dom y -> f0 x z = f1 x z) ->
filter_q Q f0 = filter_q Q f1.
Proof. 
intros. rewrite /filter_q. 
apply/eq_in_map. intro. ssa. erewrite filter_keys_eq. eauto. intros.  apply/H. 
instantiate (1 := x.2). de x. done.
Qed. 

Lemma makeL_fe3 : forall s e, makeL s e = fe (makeL s e).
Proof. 
elim;ssa. rewrite full_eunf2 //. 
rewrite /nexte_wrap. de a. destruct (fe e) eqn:Heqn;ssa.
destruct (lookup _ _) eqn:Heqn2;ssa. destruct (fe _) eqn:Heqn2;ssa.
Qed.


Lemma sch_subst : forall s n sig2 sig3, n \in schl_fv (subst_sch sig2 (sig3>>ids) s) -> exists n', sig2 n' = var_schl n /\ n' \in schl_fv s.
Proof.
case;ssa. de s. destruct (sig2 n0) eqn:Heqn;ssa. rewrite inE in H. norm_eqs.
eauto.
Qed.

Lemma dist_f : forall (A : Type) (a : nat) (f : nat -> nat) (var : nat -> A), (var a).:(f>>succn)>>var = (a.:f>>succn)>>var.
Proof.
intros. asimpl. de a.
Qed.

(*We need to restrict sig3 to only be renamings, therefore >>ids*)
(*cannot be identify, to weak induction hypthesis*)
Lemma proc_schl_subst : forall P n sig0 sig1 sig2 sig3, n \in proc_schl_fv (subst_process sig0 sig1 sig2 (sig3>>ids) P) -> exists n', sig2 n' = var_schl n /\ n' \in proc_schl_fv P.
Proof.
elim/process_ind2;ssa.
- asimpl in H0. rewrite dist_f in H0.
  apply H in H0. ssa. asimpl in H0. eauto.
- asimpl in H0. rewrite dist_f in H0.
  apply H in H0. ssa. asimpl in H0. eauto.
- rewrite mem_cat in H0. de (orP H0). 
  apply sch_subst in H1. ssa. exists x. rewrite mem_cat. ssa.
  apply H in H1. ssa. exists x. rewrite mem_cat. ssa.
- rewrite mem_cat in H0. de (orP H0).
  apply sch_subst in H1. ssa. exists x. rewrite mem_cat. ssa.
  apply H in H1. ssa. exists x. rewrite mem_cat. ssa.  asimpl in H1. done.
- rewrite !mem_cat in H0. de (orP H0).
  apply sch_subst in H1. ssa. exists x. rewrite mem_cat. ssa.
  de (orP H1). 
  apply sch_subst in H2. ssa. exists x. ssa. rewrite !mem_cat. ssa. right. ssa.
  apply H in H2. ssa. exists x. ssa. rewrite !mem_cat. ssa. right. ssa.
- rewrite mem_cat in H0. de (orP H0). 
  apply sch_subst in H1. ssa. exists x. ssa. rewrite !mem_cat. ssa. 
  asimpl in H1. rewrite dist_f in H1.
  apply H in H1. ssa. exists x. ssa. rewrite !mem_cat. ssa. 
- rewrite mem_cat in H0. de (orP H0). 
  apply sch_subst in H1. ssa. exists x. ssa. rewrite !mem_cat. ssa. 
  asimpl in H1. 
  apply H in H1. ssa. exists x. ssa. rewrite !mem_cat. ssa. 
- rewrite mem_cat in H. de (orP H). 
  apply sch_subst in H0. ssa. exists x. ssa. rewrite !mem_cat. ssa. 
  asimpl in H0. de (flattenP H0). rewrite -!map_comp in H1. de (mapP H1).
  subst. de x0. asimpl in H2.
  move/ForallT_forall : X.
  move=>Hall. move/inP : (H3). move/Hall. simpl in H2. 
  move=>HH. apply HH in H2. ssa. exists x. ssa. rewrite mem_cat. 
  apply/orP. right. apply/flattenP. econ. 2:eauto. apply/mapP. econ. eauto. done.
- rewrite mem_cat in H1. de (orP H1). apply H in H2. ssa. exists x. ssa. rewrite mem_cat. ssa.
  apply H0 in H2. ssa. exists x. ssa. rewrite mem_cat. ssa.
- rewrite mem_cat in H1. de (orP H1). apply H in H2. ssa. exists x. ssa. rewrite mem_cat. ssa.
  apply H0 in H2. ssa. exists x. ssa. rewrite mem_cat. ssa.
- de (mapP H0). rewrite mem_filter in H1. ssa. subst. de x. apply H in H4. ssa.
  asimpl in H1. de x0. asimpl in H1. destruct (sig2 x0) eqn:Heqn;ssa.
  inv H1. exists x0. ssa. apply/mapP. econ. rewrite mem_filter. apply/andP. con. 2:eauto. done. done.
- apply H in H0. ssa. asimpl in H0. exists x. ssa.
-  de (flattenP H). de (mapP H0). subst. de (mapP H2). subst. 
   apply sch_subst in H1. ssa. exists x0. ssa. apply/flattenP. econ. 2:eauto. apply/map_f. done.
- rewrite mem_cat in H. de (orP H).
  de s. de s. destruct (sig2 n0) eqn:Heqn;ssa. rewrite inE in H0. norm_eqs.
  exists n0. ssa.
  de (flattenP H0). rewrite -!map_comp in H1. de (mapP H1). subst.
  de x0. de m. apply sch_subst in H2. ssa. exists x. ssa. rewrite mem_cat.
  ssa. right. apply/flattenP. econ. 2:eauto. apply/mapP. econ. eauto. done.
Qed.



Lemma proc_pred_subst : forall P sig0 sig1 sig2 sig3, proc_pred P -> proc_pred (subst_process sig0 sig1 sig2 sig3 P).
Proof.
elim/process_ind2;ssa.
de l. rewrite all_map. 

clear H0. 
apply/allP. intro. ssa. apply (allP H1) in H as HH. 
de x. asimpl. ssa.
eapply ForallT_forall in X. ssa. eapply X in HH. eauto.
apply/inP. done.
Qed.

Lemma proc_pred_subst2 : forall P sig0 sig1 sig2 sig3, proc_pred (subst_process sig0 sig1 sig2 sig3 P) -> proc_pred P.
Proof.
elim/process_ind2;ssa;try solve[ eauto].
de l. 
clear H0. 
apply/allP. intro. ssa. 
eapply ForallT_forall in X. ssa. 
apply/X.
rewrite all_map in H1.
apply (allP H1) in H as HH. ssa.
asimpl in HH. de x. eauto.
apply/inP. done.
Qed.


Definition val_fv (c : val ) :=
match c with 
| var_val n => n :: nil
end. 

Definition valBool_fv' (c : valBool ) :=
match c with 
| (valB (var_val n)) => n :: nil
| _ => nil
end. 

Definition msgp_val_fv (m : msgp) := 
match m with 
| msgT (valM (valB v)) _ => val_fv v
| _ => nil 
end.

Fixpoint exp_val_fv (e : exp) :=
match e with 
| valE (valB v) => val_fv v
| andE e0 e1 => (exp_val_fv e0) ++ (exp_val_fv e1)
| _ => nil
end.

Fixpoint proc_val_fv' (P : process) := 
match P with 
| SessReq a b q P0 => (valBool_fv' a) ++ proc_val_fv' P0
| SessAcc a b P0=>  (valBool_fv' a) ++ proc_val_fv' P0 
| ValSend a b c P0=> (exp_val_fv c)++ proc_val_fv' P0
| ValRec a b P0=> ( proc_val_fv' P0)
| SessDel a b c P0=>  (proc_val_fv' P0)
| SessRec a b P0 => (proc_val_fv' P0)
| LabelSel a b c P0=>  (proc_val_fv' P0)
| LabelBr a b Ps => (flatten (map (snd>>proc_val_fv') Ps))
| If a P0 P1=> (exp_val_fv a) ++ (proc_val_fv' P0) ++  (proc_val_fv' P1)
| Par P0 P1 => (proc_val_fv' P0) ++  (proc_val_fv' P1)
| Inact => nil
| ResCh P0 => proc_val_fv' P0 
| ResVal P0 => (map predn (filter (fun n => n != 0) (proc_val_fv' P0)))
| PCall a b c=> exp_val_fv b 
| MsgQ a b => (flatten (map msgp_val_fv b))
end. 

Lemma valBool_subst : forall s n sig0 sig1, n \in valBool_fv' (subst_valBool sig0 (sig1>>ids) s) -> exists n', sig0 n' = var_val n /\ n' \in valBool_fv' s.
Proof.
case;ssa. de v. destruct (sig0 n0) eqn:Heqn;ssa. rewrite inE in H. norm_eqs.
eauto.
Qed.


Lemma exp_subst : forall e n sig0 sig1, n \in exp_val_fv (subst_exp sig0 (sig1>>ids) e) -> exists n', sig0 n' = var_val n /\ n' \in exp_val_fv e.
Proof.
elim;ssa. de v. de v. ssa. destruct (sig0 n0) eqn:heqn;ssa. rewrite inE in H. norm_eqs.
exists n0. ssa.
rewrite mem_cat in H1. de (orP H1). apply H in H2. ssa. exists x. ssa. rewrite mem_cat. ssa.
apply H0 in H2. ssa. exists x. ssa. rewrite mem_cat. ssa.
Qed.

Lemma proc_val_subst : forall P n sig0 sig1 sig2 sig3, n \in proc_val_fv' (subst_process sig0 (sig1>>ids) sig2 sig3 P) -> exists n', sig0 n' = var_val n /\ n' \in proc_val_fv' P.
Proof.
elim/process_ind2;ssa.
- rewrite mem_cat in H0. de (orP H0).
  apply valBool_subst in H1. ssa. exists x. ssa. rewrite mem_cat. ssa.
  asimpl in H1. 
  apply H in H1. ssa. 
  exists x. ssa. rewrite mem_cat. ssa.
- rewrite mem_cat in H0. de (orP H0).
  apply valBool_subst in H1. ssa. exists x. ssa. rewrite mem_cat. ssa.
  asimpl in H1. 
  apply H in H1. ssa. 
  exists x. ssa. rewrite mem_cat. ssa.
- rewrite mem_cat in H0. de (orP H0). 
  apply exp_subst in H1. ssa. exists x. ssa. rewrite mem_cat. ssa.
  apply H in H1. ssa. exists x. ssa. rewrite mem_cat. ssa.
- asimpl in H0. rewrite dist_f in H0. apply H in H0. ssa.
  exists x. ssa. 
- apply H in H0. ssa. eauto.
- apply H in H0. ssa. asimpl in H0. eauto.
- apply H in H0. ssa. eauto.
- de (flattenP H). rewrite -!map_comp in H0. de (mapP H0). subst.
  asimpl in H1. de x0. 
  move/ForallT_forall : X. move=>HH.
  move/inP: (H2)=>Hin. apply HH in Hin. ssa. apply Hin in H1. ssa.
  exists x. ssa. apply/flattenP. econ. 2:eauto. apply/mapP. econ. eauto. done.
- rewrite mem_cat in H1. de (orP H1).
  apply exp_subst in H2. ssa. exists x. ssa. rewrite !mem_cat. ssa.
  rewrite mem_cat in H2.
  de (orP H2). apply H in H3. ssa. exists x. ssa. rewrite !mem_cat. ssa. right. ssa.
  apply H0 in H3. ssa. exists x. ssa. rewrite !mem_cat. ssa. right. ssa.
- rewrite mem_cat in H1. de (orP H1). apply H in H2.  ssa.
  exists x. ssa. rewrite mem_cat. ssa.
  apply H0 in H2. ssa. exists x. rewrite mem_cat. ssa.
- apply H in H0. ssa. exists x. ssa. asimpl in H0. done.
- de (mapP H0). subst. rewrite mem_filter in H1. ssa. de x.
  asimpl in H3. apply H in H3. ssa. de x0. inv H1.
  asimpl in H5. destruct (sig0 x0) eqn:Heqn;ssa. inv H5. exists x0.  ssa.
  apply/mapP. econ. rewrite mem_filter. apply/andP. con. 2:eauto. done. done.
  apply exp_subst in H. ssa. eauto.
- de (flattenP H). rewrite -map_comp in H0.
  de (mapP H0). subst. de x0. de m. de v. ssa. de v.
  destruct (sig0 n0) eqn:Heqn;ssa. rewrite inE in H1. norm_eqs. exists n0. ssa.
  apply/flattenP. econ. apply/mapP. econ. eauto. econ. ssa.
Qed.


Lemma OFTE_strength_Ms : forall Ms e S, OFTE Ms e S -> forall n, n \notin exp_val_fv e -> OFTE (filter_keys (fun s => n \notin valBool_fv' s) Ms) e S. 
Proof.
move=> Ms e S. elim;ssa.
de v. con. con. apply lookup_filter. ssa.  inv H.
inv H. con. con. ssa. 
inv H. con. con. apply lookup_filter. ssa. rewrite inE in H0. done. done.
rewrite mem_cat negb_or in H3. ssa. 
con. eauto. eauto.
Qed.


Lemma OFT_strength_Ms : forall Ms Ds P E Q C (Hpred : proc_pred P), OFT Ms Ds P E Q C -> forall n, n \notin proc_val_fv' P  -> OFT (filter_keys (fun s => n \notin valBool_fv' s) Ms) Ds P E Q C.
Proof.
move=> Ms Ds P E Q C Hpred Hoft. elim: Hoft Hpred;ssa.
- econ. done. 2:eauto. inv H0. con.
  apply lookup_filter. ssa. done. con.
  apply:lookup_filter. ssa.  rewrite inE negb_or in H6. ssa.
  done. done. done.  apply H5. rewrite mem_cat negb_or in H6. ssa. rewrite mem_cat negb_or in H6. ssa.
- econ. done. 2:eauto. inv H0. con.
  apply lookup_filter. ssa. done. con.
  apply:lookup_filter. ssa.  rewrite inE negb_or in H5. ssa.
  done. done. apply:H4. rewrite mem_cat negb_or in H5. ssa. rewrite mem_cat negb_or in H5. ssa.
- rewrite mem_cat negb_or in H4. ssa. eauto.
  econ;ssa. 2:eauto. apply:OFTE_strength_Ms. done. done.
- econ. eauto. eauto. 
  apply H2 in H3. rewrite /insertS0 /insert_shift /insert /=.
  rewrite filter_keys_map_keys in H3.
  erewrite filter_keys_eq. eauto.
  intro. ssa. asimpl. de x. asimpl. done. done.
- econ. done. eauto. eauto. done. done. eauto. 
- econ. done. eauto. eauto. 
- 
  econ. done. eauto. eauto. eauto.
- 
  de Ps. de Ts. inv H0. rewrite mem_cat negb_or in H4. ssa. 
  econ. done. simpl. instantiate (1:= p0::Ts). ssa. eauto. 
  intros. apply:H3. eauto.  ssa. de H4. inv H3. 
  move/inP : H3. move/mem_zip. ssa. de (mapP H3). subst.
  apply (allP H8) in H12. done. ssa.
  de H4. inv H3. 
  move/inP : H3. move/mem_zip. ssa. de (mapP H3). subst.
  apply/negP. intro. apply/negP.  apply:H11.
  apply/flattenP. econ. 2:apply:H13. apply/map_f. done.
- rewrite mem_cat negb_or in H6. ssa. econ; eauto.
- rewrite !mem_cat !negb_or in H5. ssa. econ; eauto.
  apply:OFTE_strength_Ms. eauto. done.
- con. done. done.
- econ. eauto. 
  have: n.+1 \notin proc_val_fv' P0. apply/negP. intro. apply/negP. apply:H2.
  apply/mapP. econ. rewrite mem_filter. apply/andP. con. 2:eauto. done. done.
  move/H1. move/(_ Hpred). rewrite /=.
  move=>HH. rewrite /insertS1 /insert_shift /insert /=.
  rewrite filter_keys_map_keys in HH. 
  erewrite filter_keys_eq. eauto.
  intro. ssa. asimpl. de x. asimpl. de v.
- econ. eauto. eauto. done. apply:OFTE_strength_Ms. eauto. done. eauto. eauto. done. eauto.
  eauto.
- econ. eauto. done.
- rewrite mem_cat negb_or in H3. ssa. econ; eauto. 
  de v. inv H. con. apply lookup_filter. ssa. done.
  inv H. econ. inv H. con. 
  apply lookup_filter. ssa.
  rewrite inE in H4. done.
  done.
- econ. eauto. eauto. eauto. eauto.
- econ. eauto. eauto.
- econ. eauto. eauto.
Qed.


Lemma qType_done_filter : forall (Q: q_env) p, qType_done Q -> qType_done (filter_keys p Q).
Proof.
intros. rewrite /qType_done. apply/allP. intro. ssa. apply (allP H). 
apply in_filter_keys in H0. ssa.
Qed.
Hint Resolve qType_done_filter.
Lemma OFT_strength : forall Ms Ds P E Q C, OFT Ms Ds P E Q C -> forall n, n \notin proc_schl_fv P -> OFT Ms Ds P (filter_keys (fun s => n \notin schl_fv s) E) (filter_keys (fun k => match k with | QKey (var_schl n') _ => n' != n end) Q) (filter_keys (fun sc => n \notin schli_schl_fv sc )C).
Proof.
move=> Ms Ds P E Q C. elim;ssa.
- econ. rewrite /qType_done. apply/allP. intro. ssa. apply in_filter_keys in H7. ssa.
  apply (allP H) in H8. ssa. all:try eauto.
  apply:OFT_match. apply:H5. eauto. done.
  rewrite /insertL0 /insert_shift /insert /=. f_equal. rewrite filter_keys_map_keys.
  f_equal. apply/filter_keys_eq. intro. ssa. asimpl.
  de x. de s. done. done.
- econ. rewrite /qType_done. apply/allP. intro. ssa. apply in_filter_keys in H6. ssa.
  apply (allP H) in H7. ssa. all:try eauto.
  apply:OFT_match. apply:H4. eauto. done.
  rewrite /insertL0 /insert_shift /insert /=. f_equal. rewrite filter_keys_map_keys.
  f_equal. apply/filter_keys_eq. intro. ssa. asimpl.
  de x. de s. done. done.
- rewrite mem_cat negb_or in H4. ssa.
  econ. eauto. eauto. apply/lookup_filter. eauto. eauto.
  apply/OFT_match. apply:H3. eauto. done. rewrite update_filter_keys. done. 
  done. done.
- rewrite mem_cat negb_or in H3. ssa.
  econ. eauto. apply/lookup_filter. eauto. eauto.
  apply/OFT_match. apply:H2. eauto. done. rewrite update_filter_keys. done. 
  done. done.
- rewrite !mem_cat !negb_or in H6. ssa.
  econ. eauto. apply/lookup_filter. eauto. eauto. 
  apply/lookup_filter. eauto. eauto. done. done.
  apply/OFT_match. apply:H5. eauto. done. 
  rewrite /remove. 
  rewrite update_filter_keys. 
  rewrite !filter_keys2. apply/filter_keys_eq. intro. ssa. lia. done. done.
- rewrite !mem_cat !negb_or in H3. ssa.
  econ. eauto. apply/lookup_filter. eauto. eauto. 
  apply/OFT_match. apply:H2. eauto. done. 
  rewrite /insertL0 /insert_shift /insert /=. f_equal.
  rewrite filter_keys_map_keys. f_equal. 
  rewrite update_filter_keys.  
  apply/filter_keys_eq. intro. ssa. de x. de s0. done. done.
- rewrite !mem_cat !negb_or in H4. ssa.
  econ. eauto. eauto. apply/lookup_filter. eauto. eauto. 
  apply/OFT_match. apply:H3. eauto. done. 
  rewrite update_filter_keys.   done. done. done.
- rewrite !mem_cat !negb_or in H4. ssa.
  econ. eauto. eauto. apply/lookup_filter. eauto. eauto. 
  intros. 
  apply/OFT_match. apply:H3. eauto. 
  apply/negP. intro. apply/negP. apply /H6. apply/flattenP. econ.
  apply/inP.
  move/inP : H4. move/mem_zip. case. move/inP. eauto.
  intros. apply/inP. rewrite map_comp. apply/mapP. econ. apply/inP. eauto. econ. eauto.
  done.
  rewrite update_filter_keys.   done. done. done.
- rewrite mem_cat negb_or in H6. ssa.
  econ. 
  instantiate (3:=f0). econ.
  instantiate (3:=f1). econ.
  instantiate (3:=f2). econ.
  apply/OFT_match. apply:H3. eauto. done. inv H. rewrite !filter_keys2.
  apply/filter_keys_eq. ssa. lia.
  inv H0. rewrite -filter_q_filter_keys. f_equal.
  inv H1. rewrite !filter_keys2. apply/filter_keys_eq.
  ssa. lia.

  apply/OFT_match. apply:H5. eauto. done. 
  inv H. rewrite !filter_keys2.
  apply/filter_keys_eq. ssa. lia.
  inv H0. rewrite -filter_q_filter_keys. f_equal.
  inv H1. rewrite !filter_keys2. apply/filter_keys_eq.
  ssa. lia.
- rewrite mem_cat negb_or in H5. ssa.
  econ. eauto. 
  apply/OFT_match. apply/H1. eauto. done. done. done. done.
  apply/OFT_match. apply/H3. eauto. done. done. done. done. done.
- econ. eauto. apply/lType_done_filter_keys. eauto.
- econ. eauto. apply/OFT_match. apply/H1. eauto. done. done. done. done.
- econ. 8:econ.
  eauto. inv H6. 
  have: (filter_keys (predC (mem cs)) (filter_keys (fun s : sch => n \notin schl_fv s) E0)) =
(filter_keys (fun s : sch => n \notin schl_fv s) (filter_keys  (predC (mem cs)) E0)).
rewrite !filter_keys2.
 apply/filter_keys_eq. intros. ssa. lia.
move=>->.
apply/lType_done_filter_keys. eauto. done. eauto. eauto. done.
intro. ssa. rewrite dom_filter_keys mem_filter. ssa.
apply/negP. intro. apply/negP. apply/H8. apply/flattenP. econ. 2:eauto. apply/map_f. done.
intros. eauto. apply:H7. eauto. 
 inv H6.
apply lookup_filter2 in H10. ssa. apply lookup_filter2 in H10. ssa.
apply/lookup_filter. ssa. done.
- rewrite mem_cat negb_or in H1. ssa. 
  rewrite H2. econ. apply/lType_done_filter_keys. done. eauto.
- rewrite mem_cat negb_or in H3. ssa. 
  econ. apply : H. apply/lookup_filter. 2:eauto. de s. rewrite inE in H4. lia.
  apply/OFT_match. apply:H2.
  instantiate (1:=n). rewrite mem_cat negb_or. ssa. done. done. 
  rewrite update_filter_keys. done. done. 
- rewrite !mem_cat !negb_or in H4. ssa. 
  econ. apply/lookup_filter. 2:eauto. de s. rewrite inE in H5. lia.
  apply/lookup_filter. eauto. eauto. eauto.
  apply/OFT_match. apply:H3.
  instantiate (1:=n). rewrite mem_cat negb_or. ssa. done. 
  rewrite /remove !filter_keys2. apply/filter_keys_eq. ssa. lia.
  rewrite update_filter_keys. done. done. 
- rewrite !mem_cat !negb_or in H2. ssa. 
  econ. apply/lookup_filter. 2:eauto. de s. rewrite inE in H3. lia.
  apply/OFT_match. apply:H1.
  instantiate (1:=n0). rewrite mem_cat negb_or. ssa. done. done.
  rewrite update_filter_keys. done. done. 
- econ. eauto.
  have : n.+1 \notin proc_schl_fv P0.
  apply/negP. intro. apply/negP. apply/H2. apply/mapP. econ. rewrite mem_filter. apply/andP. con. 2:eauto. done. done.
  move=>HH.
  apply/OFT_match. apply/H1.   eauto. done.
  rewrite /insertL1 /insert_shift /insert !filter_keys_cat. f_equal. 
  erewrite filter_keys_eq. erewrite filter_keys_predT. done.
  ssa. rewrite /dom -map_comp in H3. de (mapP H3). subst. ssa.
  rewrite filter_keys_map_keys. f_equal.
  apply/filter_keys_eq. intro. ssa. de x. de s.
  rewrite /insertQ /insert_shift /insert /=.
  rewrite filter_keys_cat.
  erewrite filter_keys_eq. erewrite filter_keys_predT. f_equal.
  rewrite filter_keys_map_keys. f_equal.
  apply/filter_keys_eq. intro. ssa. de x. de s.
  ssa. rewrite /dom -map_comp in H3. de (mapP H3). subst. ssa.
  
  rewrite /insertC /insert_shift /insert filter_keys_cat.
  erewrite filter_keys_eq. erewrite filter_keys_predT. f_equal.
  rewrite filter_keys_map_keys. f_equal. apply/filter_keys_eq.
  ssa. de x. de s.
  ssa. rewrite /dom -map_comp in H3. de (mapP H3). subst. ssa.
Qed.










Lemma map_keys_filter_keys_aux : forall (A B : eqType) (E : seq (A * B)) f p l, (forall x, x \in dom E -> x \in l) -> injective f -> 
                                        map_keys f (filter_keys p E) = filter_keys (pred_dom l f p) (map_keys f E).
Proof.
move=> A B.
elim;ssa.
case_if.  case_if. ssa. f_equal. eauto.
ssa. rewrite pred_domP in H3;ssa. rewrite H2 in H3. done.
rewrite pred_domP;ssa. rewrite H2. eauto.
Qed.

Lemma map_keys_filter_keys: forall (A B : eqType) (E : seq (A * B)) f p, injective f -> 
                                        map_keys f (filter_keys p E) = filter_keys (pred_dom (dom E)f p) (map_keys f E).
Proof.
intros. apply/map_keys_filter_keys_aux. eauto. done.
Qed.

Lemma map_keys_filter_keys_aux2 : forall (A B : eqType) (E : seq (A * B)) f p l, (forall x, x \in dom E -> x \in l) -> injective_at l f -> 
                                        map_keys f (filter_keys p E) = filter_keys (pred_dom l f p) (map_keys f E).
Proof.
move=> A B.
elim;ssa.
case_if. case_if. ssa. f_equal. erewrite H. eauto. eauto.
ssa. rewrite pred_domP in H3;ssa. rewrite H2 in H3. done.
rewrite pred_domP;ssa. rewrite H2. eauto.
Qed.

Lemma map_keys_filter_keys2: forall (A B : eqType) (E : seq (A * B)) f p, injective_at (dom E) f -> 
                                        map_keys f (filter_keys p E) = filter_keys (pred_dom (dom E)f p) (map_keys f E).
Proof.
intros. apply/map_keys_filter_keys_aux2. eauto.
intro.  ssa. 
Qed.

Lemma s_env_subst_cons : forall m Ms sig0 sig1, is_var (subst_valBool sig0 sig1 m.1) -> s_env_subst (m::Ms) sig0 sig1 = (subst_valBool sig0 sig1 m.1,m.2)::(s_env_subst Ms sig0 sig1).
Proof.
ssa. rewrite /s_env_subst. ssa. rewrite H. done.
Qed.

Lemma lookup_map2 : forall (A B C: eqType) (l : seq A) T (f : A -> B * C) lk, lookup (map f l) lk = Some T -> exists lk', lk' \in l /\ f lk' = (lk,T).
Proof.
move=> A B C.
elim;ssa. destruct (eqVneq (f a).1 lk). rewrite lookup_cons_eq in H0;ssa.
inv H0. econ. con. rewrite inE. apply/orP. left. eauto. destruct (f a);ssa.
rewrite lookup_cons_neq in H0;ssa. apply H in H0.
ssa. econ. rewrite !inE. con. erewrite H0. ssa. done.
Qed.

Lemma lookup_map' : forall (A B : eqType) (l : seq (A * B)) (f : A -> A) lk v,  
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


Lemma OFT_cong3 : forall Ms Ds P P' E Q C (Hun : uniq (dom E)) (Hpred : proc_pred P) (HunQ : uniq (dom Q)), OFT Ms Ds P' E Q C -> only_vars Ms -> Cong2 P P' -> OFT Ms Ds P E Q C. 
Proof. 
intros. move : H0=>Hvar. move:H1 => H0. elim : H0 H Hvar Hun Hpred HunQ;intros. 
- econ. 4 : eauto. 4:econ. rewrite /partition. 
  instantiate (2:= fun _ => true).  rewrite filter_keys_predT filter_keys_pred0. econ.
  rewrite /partition_q. 
  instantiate (2:= fun _ _ => true). 

  rewrite filter_q_predT. f_equal.
  rewrite /partition. 
  instantiate (1:= fun _ => true). rewrite filter_keys_predT filter_keys_pred0 //=. 
  apply/allP. intro. ssa. 
  rewrite /filter_q in H0. de (mapP H0). subst. ssa. rewrite filter_keys_pred0. done. done.

- inv H. inv H2. inv H3. inv H4. econ. 
  instantiate (3 := predC f0). econ. 
  instantiate (3 := hrelC f1). econ. 
  instantiate (3 := predC f2). econ. 
  eauto. rewrite !predC2 //=.
  erewrite filter_q_eq.
  intros. 2 : { intros. rewrite hrelC2. eauto. } eauto. 

- inv H. inv H2. inv H3. inv H4. inv H11.
  inv H5. inv H6. inv H8. 
  rewrite !filter_keys2 !filter_q2 in H12. 
  rewrite !filter_keys2 !filter_q2 in H16. econ.
  instantiate (3 := predU f3 f0). econ. 
  instantiate (3 := (hrelU f1 f4)). econ.
  instantiate (3 := predU f5 f2). econ. eauto. econ.
  econ. econ. econ. rewrite !filter_keys2. rewrite filter_q2.
  erewrite filter_keys_eq.
  erewrite filter_q_eq.
  erewrite (@filter_keys_eq _ _ C). apply/H7.
  intros. instantiate (1 := f2). solve_ph.
  intros. instantiate (1 := f1). solve_ph. 
  intros. instantiate (1 := f0). solve_ph.
  rewrite !filter_keys2. rewrite filter_q2.
  erewrite filter_keys_eq.
  erewrite filter_q_eq.
  erewrite (@filter_keys_eq _ _ C). eauto. 
  intros. solve_ph.
  intros. solve_ph. 
  intros. solve_ph.
  erewrite filter_keys_eq. erewrite filter_q_eq. eauto.
  erewrite (@filter_keys_eq _ _ C). eauto.
  intros. solve_ph.
  intros. solve_ph.
  intros. solve_ph.


(*Apply strengthening for Q typing, relaxing with more end entries from finished participants in coherent set
  Challenge is P typing, we need to show it has all the coherent entries, for != end entries we show they are in
  P split by contraction because != end entry implies channel in variable*)
(*We cannot use strengthening for P typing, removing entires that are EEnd is not possible due to delegation, the 
   An entry s : EEnd can only be removed if s \notin P *)

- ssa. move : H0 H1 => Hpred0 Hpred1.
  inv H. inv H4. 
  inv H3. inv H5. inv H6. 
  econ. econ. econ. econ. econ. eauto.
  instantiate (4:= shiftL1>> f0). 
  instantiate (3:= shiftQ>> f1).
  instantiate (2:= shiftC>>f2).
  instantiate (1:= C1). 
  have: (insertL1 (filter_keys (shiftL1 >> f0) E) E1) = 
         filter_keys (predU is_lkey1 f0) (insertL1 E E1). 
  rewrite /insertL1 /insert_shift /insert /= filter_keys_cat.
  symmetry.
  erewrite filter_keys_eq. erewrite filter_keys_predT.
  symmetry.
  suff:   map_keys shiftL1 (filter_keys (shiftL1 >> f0) E) =  filter_keys (predU is_lkey1 f0) (map_keys shiftL1 E).
  move=>->. done. rewrite filter_keys_map_keys. f_equal.
  apply/filter_keys_eq. intro. ssa. asimpl. de x. de s.
  intros. ssa. rewrite /dom in H0. de (mapP H0). subst. ssa. de (mapP H2). subst. de x.
  (*rewrite for L*)
  move=>->.
  have: (insertQ (filter_q Q (shiftQ >> f1)) Q2) = 
        filter_q  (insertQ Q Q2) (hrelU (fun q k => is_qkey q) f1).
  rewrite /insertQ /insert_shift /insert /= filter_q_cat.
  symmetry.
  erewrite filter_q_eq2. erewrite filter_q_predT.
  symmetry.
  suff: map_keys shiftQ (filter_q Q (shiftQ >> f1)) =  filter_q (map_keys shiftQ Q)
    (hrelU (fun q : qkey => fun=> is_qkey q) f1).
  move=>->. done. rewrite filter_q_map_keys.
  f_equal.
  apply/filter_q_eq2. intro. ssa. asimpl. de x. de s.
  intros. ssa. de (mapP H0). rewrite /initQ in H8. inv H8.
  (*rewrite for Q*)
  move=>->.  
  have: (insertC (filter_keys (shiftC >> f2) C) C1) = filter_keys (predU is_ckey f2) (insertC C C1).
  rewrite /insertC /insert_shift /insert /= filter_keys_cat.
  symmetry.
  erewrite filter_keys_eq. erewrite filter_keys_predT.
  symmetry.
  suff:   map_keys shiftC (filter_keys (shiftC >> f2) C) =  filter_keys (predU is_ckey f2) (map_keys shiftC C).
  move=>->. done. rewrite filter_keys_map_keys. f_equal.
  apply/filter_keys_eq. intro. ssa. asimpl. de x. de s.
  intros. ssa. rewrite /dom in H0. de (mapP H0). subst. ssa. de (mapP H2). subst. de x.
  (*rewrite for C*)
  move=>->.  
  move: H9 => HP.
  apply:OFT_weaken. instantiate (1:= (filter_keys f0 (insertL1 E E1))).
  2:{ rewrite /weaken. con. rewrite filter_keys2.
      apply/filter_keys_eq. intro. intro. instantiate (1:= predU (predC is_lkey1) f0).
      tunf. destruct (is_lkey1 x) eqn:Heqn;ssa. rewrite andbC //=.
      rewrite filter_keys2.
      apply/allP. intro. ssa. apply in_filter_keys in H0. ssa.  rewrite negb_or in H7. ssa.
      rewrite negb_involutive in H0. 
      de x. de s. de s. de n. 
      eapply proc_fv_delta in H13. move: H13. instantiate (1:= l).
      rewrite /insertL1 /insert_shift /insert mem_cat in H2. de (orP H2).
      de (mapP H7). subst. de x. rewrite /initL1 in H11. ssa. inv H11. inv H1.
      ssa. inv H15. de (mapP H10). subst. inv H17.  
      rewrite -makeL_fe3 // in H13. by apply/eqP.
      de (mapP H7). inv H11. de x. de s. inv H14. de s.
      apply lookup_filter. tunf. eauto. apply uniq_in_pair in H2. done.

     rewrite /insertL1 /insert_shift /insert /=. rewrite /dom map_cat. rewrite cat_uniq. ssa.
     inv H1. ssa. inv H11. rewrite -map_comp. 

inv H7. ssa. subst. rewrite -!map_comp.
rewrite map_inj_in_uniq.   done. intro. ssa. inv H18.
apply/negP. intro. ssa. de (hasP H7). rewrite -map_comp in H11. de (mapP H11). subst.
rewrite /map_keys -map_comp in H10. de (mapP H10). subst. de x. de s. de s. 
have : (list_map fst (map_keys shiftL1 E)) = map shiftL1 (map fst E).
rewrite /map_keys -!map_comp.   apply/eq_in_map. intro. ssa.
move=>->.
rewrite map_inj_in_uniq. done. intro. ssa. 
apply/negP. intro.
apply proc_schl_subst in H7. ssa. 
apply/proc_pred_subst.  done. } 




  have : (filter_q (insertQ Q Q2) (hrelU (fun q : qkey => fun=> is_qkey q) f1)) =  (filter_q (insertQ Q Q2) f1).
  apply/filter_q_eq2. intro. ssa.
  destruct (is_qkey x) eqn:Heqn. ssa. 
  de x. de s. de n.
  apply uniq_in_pair in H0. 
  eapply proc_fv_Q in H13. 2: { apply:lookup_filter_q_3. eauto. } 
  ssa. destruct (f1 (QKey (var_schl 0) p) z) eqn:Heqn2. done.
  rewrite /dom in H2.
  have: z \in list_map fst (filter_keys (hrelC f1 (QKey (var_schl 0) p)) y).  
  de (mapP H2). subst. apply/map_f. rewrite /filter_keys mem_filter. ssa.
  rewrite Heqn2. done.
  rewrite H13. ssa.
  apply/negP. intro.
  apply proc_schl_subst in H7. ssa. apply/proc_pred_subst. done.


  rewrite /insertQ /insert_shift /insert /dom map_cat cat_uniq. ssa.
     inv H1. ssa. inv H9. rewrite -map_comp. 

inv H7. ssa. subst. rewrite -!map_comp.
rewrite map_inj_in_uniq.   done. intro. ssa. inv H16.
apply/negP. intro. ssa. de (hasP H7). rewrite -map_comp in H9. de (mapP H9). subst.
rewrite /map_keys -map_comp in H8. de (mapP H8). de x. de q. de s. 
have : (list_map fst (map_keys shiftQ Q)) = map shiftQ (map fst Q).
rewrite /map_keys -!map_comp.   apply/eq_in_map. intro. ssa.
move=>->.
rewrite map_inj_in_uniq. done. intro. ssa. by simpl.
move=>->.


  have :  (filter_keys f2 (insertC C C1)) =  (filter_keys (predU is_ckey f2) (insertC C C1)).
  apply/filter_keys_eq. intro.
  ssa. destruct (is_ckey x) eqn:Heqn;ssa. 
  de x. de s. de n.
  eapply proc_fv_C in H13.
  move: H13. instantiate (1:= i). instantiate (1:= 0).
  rewrite dom_filter_keys mem_filter negb_and negb_involutive. ssa.
  de (orP H13). rewrite H0 in H2. done.
  apply/negP. intro. 
  apply proc_schl_subst in H2. ssa. apply/proc_pred_subst. done.
  move=><-.
  done.

  eapply OFT_strength in H13.
  2: { instantiate (1:= 0). 
  apply/negP. intro. 
  apply proc_schl_subst in H0. ssa. }

  eapply OFT_subst in H13.
  move : H13.
  instantiate (7:=ids).
  instantiate (7:=Ms).
  instantiate (6:=ids).
  instantiate (5:= predn >> ids).
  instantiate (4:=ids).
  asimpl. eauto. done. 

rewrite filter_keys2.
erewrite filter_keys_eq. 
instantiate (1:= (predI (predC f0) (fun s : sch_eqType => 0 \notin schl_fv s))).
2: { intro. ssa. rewrite andbC //=. } 
rewrite -filter_keys2. 
rewrite /insertL1 /insert_shift /insert filter_keys_cat.
erewrite (@filter_keys_eq _ _ _  (fun s : sch_eqType => 0 \notin schl_fv s)). 
erewrite filter_keys_pred0. simpl.
erewrite (@filter_keys_eq _ _ _  (fun s : sch_eqType => 0 \notin schl_fv s)). 
erewrite filter_keys_predT.
intro. move=> a'. rewrite dom_filter_keys !mem_filter. ssa.

rewrite /dom /map_keys -!map_comp in H10,H11. ssa. 
de (mapP H10). de (mapP H11). subst.
f_equal. de x0. de x. de s. de s0. de s. de s0. de s.
intro. rewrite /dom /map_keys -map_comp. move/mapP. case. ssa.
subst. de x0. de s. de s.
intro. rewrite /dom -map_comp. move/mapP. case. ssa. subst.
ssa.

rewrite dom_filter_keys dom_filter_q dom_insertQ.
intro. move=> a'. rewrite !filter_cat !mem_cat !mem_filter.
move/orP. 
case.  move=> Hfst.  move/orP. case. move=> Hsnd. ssa.
de a'. de a. de s. de s0. inv H0. de n. de n0. subst. done.
ssa. de a'. de a. de s. de s0. inv H0. de n. de n0. subst. done.
move=> Hfst. move/orP. case. move=> Hsnd. ssa.
rewrite /dom /map_keys -map_comp in H10. de (mapP H10). subst.
de a'. de x. de q. inv H0. de s0. de s. asimpl in H14. ssa. de n0. inv H14.
ssa. 
rewrite /dom /map_keys -!map_comp in H7,H10.
de (mapP H7). de (mapP H10). subst. f_equal.
de x0. de x. de q. de q0. inv H0. de s. de s0. 

rewrite filter_keys2.
erewrite filter_keys_eq.
instantiate (1:= (predI (predC f2) (fun s  => 0 \notin schli_schl_fv s))).


2: { intro. ssa. rewrite andbC //=. } 
rewrite -filter_keys2. 
rewrite /insertL1 /insert_shift /insert filter_keys_cat.
erewrite (@filter_keys_eq _ _ _  (fun s  => 0 \notin schli_schl_fv s)). 
erewrite filter_keys_pred0. simpl.
erewrite (@filter_keys_eq _ _ _  (fun s => 0 \notin schli_schl_fv s)). 
erewrite filter_keys_predT.
intro. move=> a'. rewrite dom_filter_keys !mem_filter. ssa.

rewrite /dom /map_keys -!map_comp in H10,H11. ssa. 
de (mapP H10). de (mapP H11). subst.
f_equal. de x0. de x. de s. de s0. de s. de s0. 
intro. rewrite /dom /map_keys -map_comp. move/mapP. case. ssa.
subst. de x0. de s. de s.
intro. rewrite /dom -map_comp. move/mapP. case. ssa. subst.
ssa.


rewrite s_env_subst_id. done. done. 

(*L equal*)

  symmetry. rewrite filter_keys2.
rewrite /insertL1 /insert_shift /insert filter_keys_cat.
  erewrite filter_keys_eq. erewrite filter_keys_pred0. ssa.
 rewrite !map_keys_filter_keys2. rewrite map_keys2.
 rewrite filter_keys_map_keys.
 erewrite map_keys_eq. instantiate (1:= id). 
 2: { intro. ssa. rewrite dom_filter_keys mem_filter in H0. ssa.
      asimpl. done. } 
 rewrite map_keys_id. apply/filter_keys_eq. intro.
 ssa. 
rewrite pred_domP. de x. de s.
 intro. ssa. rewrite !dom_map_keys in H2,H7.
 de (mapP H2). de (mapP H7). subst. f_equal. de x0. de x1. de x1. inv H8. de s. de s0.
 rewrite dom_map_keys. apply/map_f. done.
 
 intro. ssa. rewrite dom_map_keys in H0,H2.
 de (mapP H0). subst. de (mapP H2). subst. f_equal.
 de x. de x0. de x0. inv H7. de s. de s0.
 ssa. rewrite /dom -map_comp in H0. de (mapP H0). subst. ssa.

(*Q equal*)
 rewrite /insertQ /insert_shift /insert /=.
 rewrite filter_q_cat filter_keys_cat.
 erewrite filter_keys_eq. erewrite filter_keys_pred0. simpl.
 erewrite filter_keys_eq. erewrite filter_keys_predT.
 rewrite filter_q_map_keys map_keys2.
 erewrite map_keys_eq. instantiate (1:= id).
 rewrite map_keys_id. done.
 intros. ssa. asimpl. de x. f_equal. de s.
 ssa. rewrite dom_filter_q dom_map_keys in H0.
 de (mapP H0). subst. de x0. de s.
 ssa. rewrite dom_filter_q in H0. rewrite /dom -map_comp in H0. de (mapP H0). subst. done.

(*C equal*)
  symmetry. rewrite filter_keys2.
  rewrite /insertC /insert_shift /insert filter_keys_cat.
  erewrite filter_keys_eq. erewrite filter_keys_pred0. ssa.
 rewrite !map_keys_filter_keys2. rewrite map_keys2.
 rewrite filter_keys_map_keys.
 erewrite map_keys_eq. instantiate (1:= id). 
 2: { intro. ssa. rewrite dom_filter_keys mem_filter in H0. ssa.
      asimpl. done. } 
 rewrite map_keys_id. apply/filter_keys_eq. intro.
 ssa. 
rewrite pred_domP. de x. de s.
 intro. ssa. rewrite !dom_map_keys in H2,H7.
 de (mapP H2). de (mapP H7). subst. f_equal. de x0. de x1. inv H8. de s. de s0.
 rewrite dom_map_keys. apply/map_f. done.
 
 intro. ssa. rewrite dom_map_keys in H0,H2.
 de (mapP H0). subst. de (mapP H2). subst. f_equal.
 de x. de x0. inv H7. de s. de s0.
 ssa. rewrite /dom -map_comp in H0. de (mapP H0). subst. ssa.

- asimpl in H. inv H. inv H4. inv H3. inv H5. inv H6. 
  econ. eauto. eauto. eauto. econ. eauto. eauto. 
  
  eapply OFT_strength_Ms in H13. move: H13. instantiate (1:= 0). move=>H13.
  eapply OFT_subst in H13. 
  move : H13.
  instantiate (7:=predn >> ids).
  instantiate (7:=Ms).
  instantiate (6:=ids).
  instantiate (5:= ids).
  instantiate (4:=ids).
  asimpl. eauto. 


intro. ssa. inv H0. simpl. 

con. apply lookup_filter. done.
apply lookup_filter2 in H8. ssa.
apply lookup_map' in H10. ssa. de x. inv H11.
rewrite map_keys_filter_keys2.
have :  (map_keys (subst_valBool (predn >> ids) ids) (map_keys shiftS1 Ms))
 = map_keys id Ms.
rewrite map_keys2.
 apply:map_keys_eq. intro. ssa. asimpl. done.
move=>->. rewrite map_keys_id.
apply lookup_filter. rewrite /dom /map_keys -map_comp. 
have : var_valBool n =     (subst_valBool (predn >> ids) ids) (var_valBool n). asimpl. done.
move=>->.
rewrite pred_domP. ssa.

intro. move=> a'. move/mapP. case. move=> x Hms Ha. move/mapP. case.
ssa. subst. f_equal. de x. de x0. de v. de v0. de v0. inv H14. de v. de v0. de v.
apply/mapP. 
de (mapP H10).
econ. eauto. de x. subst. done. done. 

intro. move=> a'. move/mapP. case. move=> x Hms Ha. move/mapP. case.





ssa. subst. 
de (mapP Hms). de (mapP p). subst. ssa.
de x1. de x2. f_equal. asimpl in H14. done.
con.
con. ssa.
apply lookup_filter2 in H8. ssa. rewrite inE in H8. de n.
apply lookup_filter. done. 
apply lookup_map' in H10. ssa. de x. inv H11. de v. inv H15.
rewrite map_keys_filter_keys2.
have :  (map_keys (subst_valBool (predn >> ids) ids) (map_keys shiftS1 Ms))
 = map_keys id Ms.
rewrite map_keys2.
 apply:map_keys_eq. intro. ssa. asimpl. done.
move=>->. rewrite map_keys_id.
apply lookup_filter. rewrite /dom /map_keys -map_comp. 
have : valB (var_val n) =     (subst_valBool (predn >> ids) ids) (valB (var_val n.+1)). asimpl. done.
move=>->.
rewrite pred_domP. ssa.
intro. move=> a'. move/mapP. case. move=> x Hm. ssa.
subst. de (mapP H14). subst. de x. de x0. de v. de v0. de v0. de v. de v0. de v. inv H16.
de (mapP H10). 
apply/mapP. econ. eauto. ssa. de x. subst. ssa. done.

intro. move=> a'. move/mapP. case. move=> x Hms Ha. move/mapP. case.

ssa. subst. 
de (mapP Hms). de (mapP p). subst. ssa.
de x1. de x2. f_equal. asimpl in H14. done.

intro. move=> a'. move/mapP. case. move=> x Hms Ha. move/mapP. case.
ssa. subst. de x. de x0. de s. de s0. de s0.


  rewrite subst_qkey_id. done. rewrite subst_schli_id. done. 

  rewrite  /s_env_subst.
rewrite /insertS1 /insert_shift /insert /= /initS1 /=.

rewrite map_keys_filter_keys2.
have :  (map_keys (subst_valBool (predn >> ids) ids) (map_keys shiftS1 Ms))
 = map_keys id Ms.
rewrite map_keys2.
 apply:map_keys_eq. intro. ssa. asimpl. done.
move=>->. 
erewrite filter_keys_eq. erewrite filter_keys_predT.
rewrite filter_keys_map_keys map_keys_id /=.
erewrite filter_keys_eq. erewrite filter_keys_predT. done.
intro. ssa. have : id x =  (subst_valBool (predn >> ids) ids) ( (subst_valBool (succn >> ids) ids) x).
asimpl. done.
move=>->. rewrite pred_domP. de x. de v.

intro. move=> a'. move/mapP. case. move=> x0 Hms Ha. move/mapP. case.
ssa. subst. de x0. de x1. de v. de v0. de v0. de v. de v0. de v. inv H8.
de (mapP Hms). de (mapP p). inv H12. inv H15. de x0. de x1. de v. de v0. de v. de v0. 
inv H15. ssa. subst. ssa. de n.

de (mapP H0). subst. 
apply/mapP. econ. apply/mapP. econ. eauto. econ. ssa.

move=> x. rewrite dom_filter_keys mem_filter. ssa. 
de (mapP H7). subst. 
rewrite /only_vars in Hvar. apply (allP Hvar). apply in_map_keys in H10. ssa. rewrite /id in H10. subst.
apply/mapP. econ. eauto. done.
intro. move=>a'. rewrite /dom -!map_comp.
move/mapP. case. intros. subst. de (mapP H0). subst. f_equal.
de x. de x0. de v. de v0. de v0. inv H2. de v0. inv H12. de v. de v0.

  erewrite map_keys_eq. erewrite map_keys_id. done.
  intro. ssa. rewrite subst_sch_id. done.

  erewrite map_keys_eq. erewrite map_keys_id. done.
  intro. ssa. rewrite subst_qkey_id. done.

  erewrite map_keys_eq. erewrite map_keys_id. done.
  intro. ssa. asimpl. done.

apply:proc_pred_subst. ssa.
apply/negP. intro. apply proc_val_subst in H0. ssa.
- inv H. econ. instantiate (1:= nil). instantiate (1:= nil). 
  rewrite /weak_coherent. exists nil. exists (fun _ => nil). con.
  rewrite /coherent. exists GEnd. exists nil. ssa. rewrite /coherentG. ssa.
  rewrite /Linear. ssa. inv H2. de aa_p. inv H2. de aa_p. intros. exists EEnd. 
  pfold. con. con. intro. inv H2. inv H3. inv H4. pfold. con. con. 
  pfold. con. intros. inv H2. ssa. instantiate (1:= nil).
  rewrite /insertC /insert_shift /insert //=. 
  econ. rewrite /insertQ /insert_shift /insert.
  rewrite /qType_done all_cat. ssa.
  apply/allP. intro. ssa.
  rewrite /map_keys in H2. de (mapP H2). subst. ssa.
  apply (allP H0) in H3. done.

  rewrite /lType_done all_cat. ssa.
  apply/allP. intro. ssa.
  rewrite /map_keys in H2. de (mapP H2). subst. ssa.
  apply (allP H1) in H3. done.

- inv H. econ. instantiate (1 := GEnd). 
  rewrite /coherentG. ssa.

 rewrite /Linear. ssa. inv H2. de aa_p. inv H2. de aa_p. intros. exists EEnd. 
  pfold. con. con. intro. inv H2. inv H3. inv H4. pfold. con. con. 
  pfold. con. intros. inv H2. ssa. 
  econ. done. done.

- eauto.
Qed.


Lemma proc_pred_pres : forall P Q, Cong P Q -> proc_pred P <-> proc_pred Q.
Proof.
move=> P Q. elim;ssa.
all: try solve [split;ssa].
split;ssa.
apply/proc_pred_subst. done.
apply/proc_pred_subst2. eauto.
split;ssa.
apply/proc_pred_subst. done.
apply/proc_pred_subst2. eauto.
rewrite H0. done.
rewrite H0. rewrite H2. done.
Qed.

Lemma OFT_cong : forall Ms Ds P P' E Q C (Hun: uniq (dom E)) (Hpred: proc_pred P) (HunQ: uniq (dom Q)), only_vars Ms -> Cong P P' ->  OFT Ms Ds P E Q C <-> OFT Ms Ds P' E Q C. 
Proof. 
intros. move : H=>Hvar. elim : H0 Hvar Hun Hpred HunQ;intros. 
split. 
intros. eapply OFT_cong2. eauto; done.  done. con.
intros. eapply OFT_cong3. eauto; done. ssa. done. eauto. done. con.

split. 
intros. eapply OFT_cong2. eauto; done.  done. con.
intros. eapply OFT_cong3. eauto; done.  done. done. eauto. done. con.

split. 
intros. eapply OFT_cong2. eauto; done.  done. con.
intros. eapply OFT_cong3. eauto; done.  done. done. eauto. done. con.

split. 
intros. eapply OFT_cong2. eauto; done.  done. con.
intros. eapply OFT_cong3. eauto; done.  done. done. eauto. done. con.

split. 
intros. eapply OFT_cong2. eauto; done.  done. con.
intros. eapply OFT_cong3. eauto; done.  done. done. eauto. done. con.

split. 
intros. eapply OFT_cong2. eauto; done.  done. con.
intros. eapply OFT_cong3. eauto; done.  done. done. eauto. done. con.

split. 
intros. eapply OFT_cong2. eauto; done.  done. con.
intros. eapply OFT_cong3. eauto; done.  done. done. eauto. done. con.

split. 
intros. eapply OFT_cong2. eauto; done.  done. con.
intros. eapply OFT_cong3. eauto; done.  done. done. eauto. done. con.

rewrite H0 //.
apply/proc_pred_pres. eauto. done.
split. intros. apply/H2;ssa. 
apply/proc_pred_pres. apply/CSym. apply H. done.
apply/H0;ssa.
intros. apply H0;ssa. apply/H2;ssa.
apply/proc_pred_pres. 2:eauto. apply/CSym. eauto.
Qed.
 

Fixpoint Ls_to_env (Ls : seq lType) (n : nat) :=
match Ls with 
| nil => nil 
| a::L => (var_sch n,a)::(Ls_to_env L n.+1)
end.

Definition equal_lookup (E E' : l_env) := forall lk, lookup E lk = lookup E' lk.

Definition valBool_fv (c : valBool) :=
match c with 
| var_valBool n => n::nil
| _ => nil
end. 

Definition msgp_valBool_fv (m : msgp) := 
match m with 
| msgT (valM c) _ => valBool_fv c
| _ => nil
end.


Fixpoint exp_valBool_fv (e : exp) :=
match e with 
| valE v => valBool_fv v
| andE e0 e1 => (exp_valBool_fv e0) ++ (exp_valBool_fv e1)
end.

Fixpoint proc_valBool_fv (P : process) := 
match P with 
| SessReq a b q P0 =>  (proc_valBool_fv P0)
| SessAcc a b P0=>  (proc_valBool_fv P0)
| ValSend a b c P0=> (exp_valBool_fv c)++ proc_valBool_fv P0
| ValRec a b P0=> map predn (filter (fun n => n != 0) (proc_valBool_fv P0))
| SessDel a b c P0=>  (proc_valBool_fv P0)
| SessRec a b P0 => (proc_valBool_fv P0)
| LabelSel a b c P0=>  (proc_valBool_fv P0)
| LabelBr a b Ps => (flatten (map (snd>>proc_valBool_fv) Ps))
| If a P0 P1=>  (exp_valBool_fv a) ++ (proc_valBool_fv P0) ++  (proc_valBool_fv P1)
| Par P0 P1 => (proc_valBool_fv P0) ++  (proc_valBool_fv P1)
| Inact => nil
| ResCh P0 => proc_valBool_fv P0
| ResVal P0 =>  proc_valBool_fv P0 
| PCall a b c=> exp_valBool_fv b
| MsgQ a b => flatten (map msgp_valBool_fv b)
end. 


Definition DefTyping  (Ds : def_env) (Ps : seq process) :=
  size Ps = size Ds /\ (forall p, p \in Ps -> proc_pred p ) /\ (forall d n, d \in Ps -> n \in proc_valBool_fv d -> n = 0) /\
  forall P m Ls, (P,(m,Ls)) \in zip Ps Ds -> 
    OFT ((insertS0 nil m)) Ds P (Ls_to_env Ls 0)  nil nil.


 Inductive DOFT : s_env -> def_env -> seq process -> process -> l_env -> q_env -> c_env -> Prop := 
 | DOFT1 Ms Ds Ps P  E Q C : DefTyping Ds Ps ->  OFT Ms Ds P E Q C ->   DOFT Ms Ds Ps P E Q C.


Lemma DOFT_cong : forall Ms Ds P P' E Q C Ps (Hun: uniq (dom E)) (Hpred: proc_pred P) (HunQ: uniq (dom Q)), DOFT Ms Ds Ps P E Q C -> only_vars Ms -> Cong P P' -> DOFT Ms Ds Ps P' E Q C. 
Proof. 
intros. econ. eauto. inv H.
apply -> OFT_cong. 2: eauto. inv H. done.  done. done. done.
Qed.  

