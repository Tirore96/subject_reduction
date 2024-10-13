Require Export MPSTSR.IndTypes.unscoped. 
Require Import MPSTSR.IndTypes.syntax. 
From mathcomp Require Import all_ssreflect zify.

Notation eq_refl := Logic.eq_refl. 
Notation eq_sym := Logic.eq_sym. 
Notation eq_trans := Logic.eq_trans. 
Notation list_ext := seq_ext.
Notation list_map := map. 
Notation list_comp := seq_comp. 

Section val.
Inductive val  : Type :=
  | var_val : ( fin ) -> val .
Global Instance VarInstance_val  : Var (fin) (val ) := @var_val  .

Definition subst_val   (sigmaval : ( fin ) -> val ) (s : val ) : val  :=
    match s return val  with
    | var_val  s => sigmaval s
    end.

Definition up_val_val   (sigma : ( fin ) -> val ) : ( fin ) -> val  :=
  (scons) ((var_val ) (var_zero)) ((funcomp) (subst_val ((funcomp) (var_val ) (shift))) sigma).

Definition upId_val_val  (sigma : ( fin ) -> val ) (Eq : forall x, sigma x = (var_val ) x) : forall x, (up_val_val sigma) x = (var_val ) x :=
  fun n => match n with
  | S fin_n => (ap) (subst_val ((funcomp) (var_val ) (shift))) (Eq fin_n)
  | 0  => eq_refl
  end.

Definition idSubst_val  (sigmaval : ( fin ) -> val ) (Eqval : forall x, sigmaval x = (var_val ) x) (s : val ) : subst_val sigmaval s = s :=
    match s return subst_val sigmaval s = s with
    | var_val  s => Eqval s
    end.

Definition upExt_val_val   (sigma : ( fin ) -> val ) (tau : ( fin ) -> val ) (Eq : forall x, sigma x = tau x) : forall x, (up_val_val sigma) x = (up_val_val tau) x :=
  fun n => match n with
  | S fin_n => (ap) (subst_val ((funcomp) (var_val ) (shift))) (Eq fin_n)
  | 0  => eq_refl
  end.

Definition ext_val   (sigmaval : ( fin ) -> val ) (tauval : ( fin ) -> val ) (Eqval : forall x, sigmaval x = tauval x) (s : val ) : subst_val sigmaval s = subst_val tauval s :=
    match s return subst_val sigmaval s = subst_val tauval s with
    | var_val  s => Eqval s
    end.

Definition compSubstSubst_val    (sigmaval : ( fin ) -> val ) (tauval : ( fin ) -> val ) (thetaval : ( fin ) -> val ) (Eqval : forall x, ((funcomp) (subst_val tauval) sigmaval) x = thetaval x) (s : val ) : subst_val tauval (subst_val sigmaval s) = subst_val thetaval s :=
    match s return subst_val tauval (subst_val sigmaval s) = subst_val thetaval s with
    | var_val  s => Eqval s
    end.

Definition up_subst_subst_val_val    (sigma : ( fin ) -> val ) (tauval : ( fin ) -> val ) (theta : ( fin ) -> val ) (Eq : forall x, ((funcomp) (subst_val tauval) sigma) x = theta x) : forall x, ((funcomp) (subst_val (up_val_val tauval)) (up_val_val sigma)) x = (up_val_val theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compSubstSubst_val ((funcomp) (var_val ) (shift)) (up_val_val tauval) ((funcomp) (up_val_val tauval) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstSubst_val tauval ((funcomp) (var_val ) (shift)) ((funcomp) (subst_val ((funcomp) (var_val ) (shift))) tauval) (fun x => eq_refl) (sigma fin_n))) ((ap) (subst_val ((funcomp) (var_val ) (shift))) (Eq fin_n)))
  | 0  => eq_refl
  end.

Lemma instId_val  : subst_val (var_val ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_val (var_val ) (fun n => eq_refl) ((id) x))). Qed.

Lemma varL_val   (sigmaval : ( fin ) -> val ) : (funcomp) (subst_val sigmaval) (var_val ) = sigmaval .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_val    (sigmaval : ( fin ) -> val ) (tauval : ( fin ) -> val ) (s : val ) : subst_val tauval (subst_val sigmaval s) = subst_val ((funcomp) (subst_val tauval) sigmaval) s .
Proof. exact (compSubstSubst_val sigmaval tauval (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_val    (sigmaval : ( fin ) -> val ) (tauval : ( fin ) -> val ) : (funcomp) (subst_val tauval) (subst_val sigmaval) = subst_val ((funcomp) (subst_val tauval) sigmaval) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_val sigmaval tauval n)). Qed.

End val.

Section schl.
Inductive schl  : Type :=
  | var_schl : ( fin ) -> schl .
Global Instance VarInstance_schl  : Var (fin) (schl ) := @var_schl  .

Definition subst_schl   (sigmaschl : ( fin ) -> schl ) (s : schl ) : schl  :=
    match s return schl  with
    | var_schl  s => sigmaschl s
    end.

Definition up_schl_schl   (sigma : ( fin ) -> schl ) : ( fin ) -> schl  :=
  (scons) ((var_schl ) (var_zero)) ((funcomp) (subst_schl ((funcomp) (var_schl ) (shift))) sigma).

Definition upId_schl_schl  (sigma : ( fin ) -> schl ) (Eq : forall x, sigma x = (var_schl ) x) : forall x, (up_schl_schl sigma) x = (var_schl ) x :=
  fun n => match n with
  | S fin_n => (ap) (subst_schl ((funcomp) (var_schl ) (shift))) (Eq fin_n)
  | 0  => eq_refl
  end.

Definition idSubst_schl  (sigmaschl : ( fin ) -> schl ) (Eqschl : forall x, sigmaschl x = (var_schl ) x) (s : schl ) : subst_schl sigmaschl s = s :=
    match s return subst_schl sigmaschl s = s with
    | var_schl  s => Eqschl s
    end.

Definition upExt_schl_schl   (sigma : ( fin ) -> schl ) (tau : ( fin ) -> schl ) (Eq : forall x, sigma x = tau x) : forall x, (up_schl_schl sigma) x = (up_schl_schl tau) x :=
  fun n => match n with
  | S fin_n => (ap) (subst_schl ((funcomp) (var_schl ) (shift))) (Eq fin_n)
  | 0  => eq_refl
  end.

Definition ext_schl   (sigmaschl : ( fin ) -> schl ) (tauschl : ( fin ) -> schl ) (Eqschl : forall x, sigmaschl x = tauschl x) (s : schl ) : subst_schl sigmaschl s = subst_schl tauschl s :=
    match s return subst_schl sigmaschl s = subst_schl tauschl s with
    | var_schl  s => Eqschl s
    end.

Definition compSubstSubst_schl    (sigmaschl : ( fin ) -> schl ) (tauschl : ( fin ) -> schl ) (thetaschl : ( fin ) -> schl ) (Eqschl : forall x, ((funcomp) (subst_schl tauschl) sigmaschl) x = thetaschl x) (s : schl ) : subst_schl tauschl (subst_schl sigmaschl s) = subst_schl thetaschl s :=
    match s return subst_schl tauschl (subst_schl sigmaschl s) = subst_schl thetaschl s with
    | var_schl  s => Eqschl s
    end.

Definition up_subst_subst_schl_schl    (sigma : ( fin ) -> schl ) (tauschl : ( fin ) -> schl ) (theta : ( fin ) -> schl ) (Eq : forall x, ((funcomp) (subst_schl tauschl) sigma) x = theta x) : forall x, ((funcomp) (subst_schl (up_schl_schl tauschl)) (up_schl_schl sigma)) x = (up_schl_schl theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compSubstSubst_schl ((funcomp) (var_schl ) (shift)) (up_schl_schl tauschl) ((funcomp) (up_schl_schl tauschl) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstSubst_schl tauschl ((funcomp) (var_schl ) (shift)) ((funcomp) (subst_schl ((funcomp) (var_schl ) (shift))) tauschl) (fun x => eq_refl) (sigma fin_n))) ((ap) (subst_schl ((funcomp) (var_schl ) (shift))) (Eq fin_n)))
  | 0  => eq_refl
  end.

Lemma instId_schl  : subst_schl (var_schl ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_schl (var_schl ) (fun n => eq_refl) ((id) x))). Qed.

Lemma varL_schl   (sigmaschl : ( fin ) -> schl ) : (funcomp) (subst_schl sigmaschl) (var_schl ) = sigmaschl .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_schl    (sigmaschl : ( fin ) -> schl ) (tauschl : ( fin ) -> schl ) (s : schl ) : subst_schl tauschl (subst_schl sigmaschl s) = subst_schl ((funcomp) (subst_schl tauschl) sigmaschl) s .
Proof. exact (compSubstSubst_schl sigmaschl tauschl (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_schl    (sigmaschl : ( fin ) -> schl ) (tauschl : ( fin ) -> schl ) : (funcomp) (subst_schl tauschl) (subst_schl sigmaschl) = subst_schl ((funcomp) (subst_schl tauschl) sigmaschl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_schl sigmaschl tauschl n)). Qed.

End schl.



Section sch.
Inductive sch  : Type :=
  | var_sch : ( fin ) -> sch  
  | schlT : ( schl   ) -> ( ptcp   ) -> sch  .


Global Instance VarInstance_sch  : Var (fin) (sch  ) := @var_sch   .


Lemma congr_schlT  { s0 : schl   } { s1 : ptcp   } { t0 : schl   } { t1 : ptcp   } (H1 : s0 = t0) (H2 : s1 = t1) : schlT   s0 s1 = schlT   t0 t1 .
Proof. congruence. Qed.

Definition subst_sch   (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (s : sch  ) : sch   :=
    match s return sch   with
    | var_sch   s => sigmasch s
    | schlT   s0 s1 => schlT   ((subst_schl sigmaschl) s0) ((fun x => x) s1)
    end.

Definition up_schl_sch   (sigma : ( fin ) -> sch  ) : ( fin ) -> sch   :=
  (funcomp) (subst_sch ((funcomp) (var_schl  ) (shift)) (var_sch)) sigma.

Definition up_sch_schl   (sigma : ( fin ) -> schl ) : ( fin ) -> schl  :=
  (funcomp) (subst_schl (var_schl)) sigma.

Definition up_sch_sch   (sigma : ( fin ) -> sch  ) : ( fin ) -> sch   :=
  (scons) ((var_sch  ) (var_zero)) ((funcomp) (subst_sch (var_schl) ((funcomp) (var_sch  ) (shift))) sigma).

Definition upId_schl_sch  (sigma : ( fin ) -> sch  ) (Eq : forall x, sigma x = (var_sch  ) x) : forall x, (up_schl_sch sigma) x = (var_sch  ) x :=
  fun n => (ap) (subst_sch ((funcomp) (var_schl  ) (shift)) (var_sch)) (Eq n).

Definition upId_sch_schl  (sigma : ( fin ) -> schl ) (Eq : forall x, sigma x = (var_schl ) x) : forall x, (up_sch_schl sigma) x = (var_schl ) x :=
  fun n => (ap) (subst_schl (var_schl)) (Eq n).

Definition upId_sch_sch  (sigma : ( fin ) -> sch  ) (Eq : forall x, sigma x = (var_sch  ) x) : forall x, (up_sch_sch sigma) x = (var_sch  ) x :=
  fun n => match n with
  | S fin_n => (ap) (subst_sch (var_schl) ((funcomp) (var_sch  ) (shift))) (Eq fin_n)
  | 0  => eq_refl
  end.

Definition idSubst_sch  (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (Eqschl : forall x, sigmaschl x = (var_schl ) x) (Eqsch : forall x, sigmasch x = (var_sch  ) x) (s : sch  ) : subst_sch sigmaschl sigmasch s = s :=
    match s return subst_sch sigmaschl sigmasch s = s with
    | var_sch   s => Eqsch s
    | schlT   s0 s1 => congr_schlT ((idSubst_schl sigmaschl Eqschl) s0) ((fun x => (eq_refl) x) s1)
    end.

Definition upExt_schl_sch   (sigma : ( fin ) -> sch  ) (tau : ( fin ) -> sch  ) (Eq : forall x, sigma x = tau x) : forall x, (up_schl_sch sigma) x = (up_schl_sch tau) x :=
  fun n => (ap) (subst_sch ((funcomp) (var_schl  ) (shift)) (var_sch)) (Eq n).

Definition upExt_sch_schl   (sigma : ( fin ) -> schl ) (tau : ( fin ) -> schl ) (Eq : forall x, sigma x = tau x) : forall x, (up_sch_schl sigma) x = (up_sch_schl tau) x :=
  fun n => (ap) (subst_schl (var_schl)) (Eq n).

Definition upExt_sch_sch   (sigma : ( fin ) -> sch  ) (tau : ( fin ) -> sch  ) (Eq : forall x, sigma x = tau x) : forall x, (up_sch_sch sigma) x = (up_sch_sch tau) x :=
  fun n => match n with
  | S fin_n => (ap) (subst_sch (var_schl) ((funcomp) (var_sch  ) (shift))) (Eq fin_n)
  | 0  => eq_refl
  end.

Definition ext_sch   (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (tauschl : ( fin ) -> schl ) (tausch : ( fin ) -> sch  ) (Eqschl : forall x, sigmaschl x = tauschl x) (Eqsch : forall x, sigmasch x = tausch x) (s : sch  ) : subst_sch sigmaschl sigmasch s = subst_sch tauschl tausch s :=
    match s return subst_sch sigmaschl sigmasch s = subst_sch tauschl tausch s with
    | var_sch   s => Eqsch s
    | schlT   s0 s1 => congr_schlT ((ext_schl sigmaschl tauschl Eqschl) s0) ((fun x => (eq_refl) x) s1)
    end.

Definition compSubstSubst_sch    (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (tauschl : ( fin ) -> schl ) (tausch : ( fin ) -> sch  ) (thetaschl : ( fin ) -> schl ) (thetasch : ( fin ) -> sch  ) (Eqschl : forall x, ((funcomp) (subst_schl tauschl) sigmaschl) x = thetaschl x) (Eqsch : forall x, ((funcomp) (subst_sch tauschl tausch) sigmasch) x = thetasch x) (s : sch  ) : subst_sch tauschl tausch (subst_sch sigmaschl sigmasch s) = subst_sch thetaschl thetasch s :=
    match s return subst_sch tauschl tausch (subst_sch sigmaschl sigmasch s) = subst_sch thetaschl thetasch s with
    | var_sch   s => Eqsch s
    | schlT   s0 s1 => congr_schlT ((compSubstSubst_schl sigmaschl tauschl thetaschl Eqschl) s0) ((fun x => (eq_refl) x) s1)
    end.

Definition up_subst_subst_schl_sch    (sigma : ( fin ) -> sch  ) (tauschl : ( fin ) -> schl ) (tausch : ( fin ) -> sch  ) (theta : ( fin ) -> sch  ) (Eq : forall x, ((funcomp) (subst_sch tauschl tausch) sigma) x = theta x) : forall x, ((funcomp) (subst_sch (up_schl_schl tauschl) (up_schl_sch tausch)) (up_schl_sch sigma)) x = (up_schl_sch theta) x :=
  fun n => (eq_trans) (compSubstSubst_sch ((funcomp) (var_schl  ) (shift)) (var_sch) (up_schl_schl tauschl) (up_schl_sch tausch) ((funcomp) (up_schl_schl tauschl) (shift)) ((funcomp) (up_schl_sch tausch) ((id) (_))) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstSubst_sch tauschl tausch ((funcomp) (var_schl  ) (shift)) (var_sch) ((funcomp) (subst_schl ((funcomp) (var_schl  ) (shift))) tauschl) ((funcomp) (subst_sch ((funcomp) (var_schl  ) (shift)) (var_sch)) tausch) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (subst_sch ((funcomp) (var_schl  ) (shift)) (var_sch)) (Eq n))).

Definition up_subst_subst_sch_schl    (sigma : ( fin ) -> schl ) (tauschl : ( fin ) -> schl ) (theta : ( fin ) -> schl ) (Eq : forall x, ((funcomp) (subst_schl tauschl) sigma) x = theta x) : forall x, ((funcomp) (subst_schl (up_sch_schl tauschl)) (up_sch_schl sigma)) x = (up_sch_schl theta) x :=
  fun n => (eq_trans) (compSubstSubst_schl (var_schl) (up_sch_schl tauschl) ((funcomp) (up_sch_schl tauschl) ((id) (_))) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstSubst_schl tauschl (var_schl) ((funcomp) (subst_schl (var_schl)) tauschl) (fun x => eq_refl) (sigma n))) ((ap) (subst_schl (var_schl)) (Eq n))).

Definition up_subst_subst_sch_sch    (sigma : ( fin ) -> sch  ) (tauschl : ( fin ) -> schl ) (tausch : ( fin ) -> sch  ) (theta : ( fin ) -> sch  ) (Eq : forall x, ((funcomp) (subst_sch tauschl tausch) sigma) x = theta x) : forall x, ((funcomp) (subst_sch (up_sch_schl tauschl) (up_sch_sch tausch)) (up_sch_sch sigma)) x = (up_sch_sch theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compSubstSubst_sch (var_schl) ((funcomp) (var_sch  ) (shift)) (up_sch_schl tauschl) (up_sch_sch tausch) ((funcomp) (up_sch_schl tauschl) ((id) (_))) ((funcomp) (up_sch_sch tausch) (shift)) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstSubst_sch tauschl tausch (var_schl) ((funcomp) (var_sch  ) (shift)) ((funcomp) (subst_schl (var_schl)) tauschl) ((funcomp) (subst_sch (var_schl) ((funcomp) (var_sch  ) (shift))) tausch) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n))) ((ap) (subst_sch (var_schl) ((funcomp) (var_sch  ) (shift))) (Eq fin_n)))
  | 0  => eq_refl
  end.

Lemma instId_sch  : subst_sch (var_schl ) (var_sch  ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_sch (var_schl ) (var_sch  ) (fun n => eq_refl) (fun n => eq_refl) ((id) x))). Qed.

Lemma varL_sch   (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) : (funcomp) (subst_sch sigmaschl sigmasch) (var_sch  ) = sigmasch .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_sch    (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (tauschl : ( fin ) -> schl ) (tausch : ( fin ) -> sch  ) (s : sch  ) : subst_sch tauschl tausch (subst_sch sigmaschl sigmasch s) = subst_sch ((funcomp) (subst_schl tauschl) sigmaschl) ((funcomp) (subst_sch tauschl tausch) sigmasch) s .
Proof. exact (compSubstSubst_sch sigmaschl sigmasch tauschl tausch (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compComp'_sch    (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (tauschl : ( fin ) -> schl ) (tausch : ( fin ) -> sch  ) : (funcomp) (subst_sch tauschl tausch) (subst_sch sigmaschl sigmasch) = subst_sch ((funcomp) (subst_schl tauschl) sigmaschl) ((funcomp) (subst_sch tauschl tausch) sigmasch) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_sch sigmaschl sigmasch tauschl tausch n)). Qed.

End sch.




Section schli.
Definition index := ch.
Inductive schli  : Type :=
  | schliT : ( schl   ) -> ( index   ) -> schli .



Lemma congr_schliT  { s0 : schl   } { s1 : index   } { t0 : schl   } { t1 : index   } (H1 : s0 = t0) (H2 : s1 = t1) : schliT  s0 s1 = schliT  t0 t1 .
Proof. congruence. Qed.

Definition subst_schli   (sigmaschl : ( fin ) -> schl ) (s : schli ) : schli  :=
    match s return schli  with
    | schliT  s0 s1 => schliT  ((subst_schl sigmaschl) s0) ((fun x => x) s1)
    end.

Definition idSubst_schli  (sigmaschl : ( fin ) -> schl ) (Eqschl : forall x, sigmaschl x = (var_schl ) x) (s : schli ) : subst_schli sigmaschl s = s :=
    match s return subst_schli sigmaschl s = s with
    | schliT  s0 s1 => congr_schliT ((idSubst_schl sigmaschl Eqschl) s0) ((fun x => (eq_refl) x) s1)
    end.

Definition ext_schli   (sigmaschl : ( fin ) -> schl ) (tauschl : ( fin ) -> schl ) (Eqschl : forall x, sigmaschl x = tauschl x) (s : schli ) : subst_schli sigmaschl s = subst_schli tauschl s :=
    match s return subst_schli sigmaschl s = subst_schli tauschl s with
    | schliT  s0 s1 => congr_schliT ((ext_schl sigmaschl tauschl Eqschl) s0) ((fun x => (eq_refl) x) s1)
    end.

Definition compSubstSubst_schli    (sigmaschl : ( fin ) -> schl ) (tauschl : ( fin ) -> schl ) (thetaschl : ( fin ) -> schl ) (Eqschl : forall x, ((funcomp) (subst_schl tauschl) sigmaschl) x = thetaschl x) (s : schli ) : subst_schli tauschl (subst_schli sigmaschl s) = subst_schli thetaschl s :=
    match s return subst_schli tauschl (subst_schli sigmaschl s) = subst_schli thetaschl s with
    | schliT  s0 s1 => congr_schliT ((compSubstSubst_schl sigmaschl tauschl thetaschl Eqschl) s0) ((fun x => (eq_refl) x) s1)
    end.

Lemma instId_schli  : subst_schli (var_schl ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_schli (var_schl ) (fun n => eq_refl) ((id) x))). Qed.

Lemma compComp_schli    (sigmaschl : ( fin ) -> schl ) (tauschl : ( fin ) -> schl ) (s : schli ) : subst_schli tauschl (subst_schli sigmaschl s) = subst_schli ((funcomp) (subst_schl tauschl) sigmaschl) s .
Proof. exact (compSubstSubst_schli sigmaschl tauschl (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_schli    (sigmaschl : ( fin ) -> schl ) (tauschl : ( fin ) -> schl ) : (funcomp) (subst_schli tauschl) (subst_schli sigmaschl) = subst_schli ((funcomp) (subst_schl tauschl) sigmaschl) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_schli sigmaschl tauschl n)). Qed.

End schli.



Section valBool.
Inductive valBool  : Type :=
  | var_valBool : ( fin ) -> valBool  
  | boolB : ( bool   ) -> valBool  
  | valB : ( val   ) -> valBool  .

Global Instance VarInstance_valBool  : Var (fin) (valBool  ) := @var_valBool   .


Lemma congr_boolB  { s0 : bool   } { t0 : bool   } (H1 : s0 = t0) : boolB   s0 = boolB   t0 .
Proof. congruence. Qed.

Lemma congr_valB  { s0 : val   } { t0 : val   } (H1 : s0 = t0) : valB   s0 = valB   t0 .
Proof. congruence. Qed.

Definition subst_valBool   (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (s : valBool  ) : valBool   :=
    match s return valBool   with
    | var_valBool   s => sigmavalBool s
    | boolB   s0 => boolB   ((fun x => x) s0)
    | valB   s0 => valB   ((subst_val sigmaval) s0)
    end.

Definition up_val_valBool   (sigma : ( fin ) -> valBool  ) : ( fin ) -> valBool   :=
  (funcomp) (subst_valBool ((funcomp) (var_val  ) (shift)) (var_valBool)) sigma.

Definition up_valBool_val   (sigma : ( fin ) -> val ) : ( fin ) -> val  :=
  (funcomp) (subst_val (var_val)) sigma.

Definition up_valBool_valBool   (sigma : ( fin ) -> valBool  ) : ( fin ) -> valBool   :=
  (scons) ((var_valBool  ) (var_zero)) ((funcomp) (subst_valBool (var_val) ((funcomp) (var_valBool  ) (shift))) sigma).

Definition upId_val_valBool  (sigma : ( fin ) -> valBool  ) (Eq : forall x, sigma x = (var_valBool  ) x) : forall x, (up_val_valBool sigma) x = (var_valBool  ) x :=
  fun n => (ap) (subst_valBool ((funcomp) (var_val  ) (shift)) (var_valBool)) (Eq n).

Definition upId_valBool_val  (sigma : ( fin ) -> val ) (Eq : forall x, sigma x = (var_val ) x) : forall x, (up_valBool_val sigma) x = (var_val ) x :=
  fun n => (ap) (subst_val (var_val)) (Eq n).

Definition upId_valBool_valBool  (sigma : ( fin ) -> valBool  ) (Eq : forall x, sigma x = (var_valBool  ) x) : forall x, (up_valBool_valBool sigma) x = (var_valBool  ) x :=
  fun n => match n with
  | S fin_n => (ap) (subst_valBool (var_val) ((funcomp) (var_valBool  ) (shift))) (Eq fin_n)
  | 0  => eq_refl
  end.

Definition idSubst_valBool  (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (Eqval : forall x, sigmaval x = (var_val ) x) (EqvalBool : forall x, sigmavalBool x = (var_valBool  ) x) (s : valBool  ) : subst_valBool sigmaval sigmavalBool s = s :=
    match s return subst_valBool sigmaval sigmavalBool s = s with
    | var_valBool   s => EqvalBool s
    | boolB   s0 => congr_boolB ((fun x => (eq_refl) x) s0)
    | valB   s0 => congr_valB ((idSubst_val sigmaval Eqval) s0)
    end.

Definition upExt_val_valBool   (sigma : ( fin ) -> valBool  ) (tau : ( fin ) -> valBool  ) (Eq : forall x, sigma x = tau x) : forall x, (up_val_valBool sigma) x = (up_val_valBool tau) x :=
  fun n => (ap) (subst_valBool ((funcomp) (var_val  ) (shift)) (var_valBool)) (Eq n).

Definition upExt_valBool_val   (sigma : ( fin ) -> val ) (tau : ( fin ) -> val ) (Eq : forall x, sigma x = tau x) : forall x, (up_valBool_val sigma) x = (up_valBool_val tau) x :=
  fun n => (ap) (subst_val (var_val)) (Eq n).

Definition upExt_valBool_valBool   (sigma : ( fin ) -> valBool  ) (tau : ( fin ) -> valBool  ) (Eq : forall x, sigma x = tau x) : forall x, (up_valBool_valBool sigma) x = (up_valBool_valBool tau) x :=
  fun n => match n with
  | S fin_n => (ap) (subst_valBool (var_val) ((funcomp) (var_valBool  ) (shift))) (Eq fin_n)
  | 0  => eq_refl
  end.

Definition ext_valBool   (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) (Eqval : forall x, sigmaval x = tauval x) (EqvalBool : forall x, sigmavalBool x = tauvalBool x) (s : valBool  ) : subst_valBool sigmaval sigmavalBool s = subst_valBool tauval tauvalBool s :=
    match s return subst_valBool sigmaval sigmavalBool s = subst_valBool tauval tauvalBool s with
    | var_valBool   s => EqvalBool s
    | boolB   s0 => congr_boolB ((fun x => (eq_refl) x) s0)
    | valB   s0 => congr_valB ((ext_val sigmaval tauval Eqval) s0)
    end.

Definition compSubstSubst_valBool    (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) (thetaval : ( fin ) -> val ) (thetavalBool : ( fin ) -> valBool  ) (Eqval : forall x, ((funcomp) (subst_val tauval) sigmaval) x = thetaval x) (EqvalBool : forall x, ((funcomp) (subst_valBool tauval tauvalBool) sigmavalBool) x = thetavalBool x) (s : valBool  ) : subst_valBool tauval tauvalBool (subst_valBool sigmaval sigmavalBool s) = subst_valBool thetaval thetavalBool s :=
    match s return subst_valBool tauval tauvalBool (subst_valBool sigmaval sigmavalBool s) = subst_valBool thetaval thetavalBool s with
    | var_valBool   s => EqvalBool s
    | boolB   s0 => congr_boolB ((fun x => (eq_refl) x) s0)
    | valB   s0 => congr_valB ((compSubstSubst_val sigmaval tauval thetaval Eqval) s0)
    end.

Definition up_subst_subst_val_valBool    (sigma : ( fin ) -> valBool  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) (theta : ( fin ) -> valBool  ) (Eq : forall x, ((funcomp) (subst_valBool tauval tauvalBool) sigma) x = theta x) : forall x, ((funcomp) (subst_valBool (up_val_val tauval) (up_val_valBool tauvalBool)) (up_val_valBool sigma)) x = (up_val_valBool theta) x :=
  fun n => (eq_trans) (compSubstSubst_valBool ((funcomp) (var_val  ) (shift)) (var_valBool) (up_val_val tauval) (up_val_valBool tauvalBool) ((funcomp) (up_val_val tauval) (shift)) ((funcomp) (up_val_valBool tauvalBool) ((id) (_))) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstSubst_valBool tauval tauvalBool ((funcomp) (var_val  ) (shift)) (var_valBool) ((funcomp) (subst_val ((funcomp) (var_val  ) (shift))) tauval) ((funcomp) (subst_valBool ((funcomp) (var_val  ) (shift)) (var_valBool)) tauvalBool) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (subst_valBool ((funcomp) (var_val  ) (shift)) (var_valBool)) (Eq n))).

Definition up_subst_subst_valBool_val    (sigma : ( fin ) -> val ) (tauval : ( fin ) -> val ) (theta : ( fin ) -> val ) (Eq : forall x, ((funcomp) (subst_val tauval) sigma) x = theta x) : forall x, ((funcomp) (subst_val (up_valBool_val tauval)) (up_valBool_val sigma)) x = (up_valBool_val theta) x :=
  fun n => (eq_trans) (compSubstSubst_val (var_val) (up_valBool_val tauval) ((funcomp) (up_valBool_val tauval) ((id) (_))) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstSubst_val tauval (var_val) ((funcomp) (subst_val (var_val)) tauval) (fun x => eq_refl) (sigma n))) ((ap) (subst_val (var_val)) (Eq n))).

Definition up_subst_subst_valBool_valBool    (sigma : ( fin ) -> valBool  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) (theta : ( fin ) -> valBool  ) (Eq : forall x, ((funcomp) (subst_valBool tauval tauvalBool) sigma) x = theta x) : forall x, ((funcomp) (subst_valBool (up_valBool_val tauval) (up_valBool_valBool tauvalBool)) (up_valBool_valBool sigma)) x = (up_valBool_valBool theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compSubstSubst_valBool (var_val) ((funcomp) (var_valBool  ) (shift)) (up_valBool_val tauval) (up_valBool_valBool tauvalBool) ((funcomp) (up_valBool_val tauval) ((id) (_))) ((funcomp) (up_valBool_valBool tauvalBool) (shift)) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstSubst_valBool tauval tauvalBool (var_val) ((funcomp) (var_valBool  ) (shift)) ((funcomp) (subst_val (var_val)) tauval) ((funcomp) (subst_valBool (var_val) ((funcomp) (var_valBool  ) (shift))) tauvalBool) (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n))) ((ap) (subst_valBool (var_val) ((funcomp) (var_valBool  ) (shift))) (Eq fin_n)))
  | 0  => eq_refl
  end.

Lemma instId_valBool  : subst_valBool (var_val ) (var_valBool  ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_valBool (var_val ) (var_valBool  ) (fun n => eq_refl) (fun n => eq_refl) ((id) x))). Qed.

Lemma varL_valBool   (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) : (funcomp) (subst_valBool sigmaval sigmavalBool) (var_valBool  ) = sigmavalBool .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_valBool    (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) (s : valBool  ) : subst_valBool tauval tauvalBool (subst_valBool sigmaval sigmavalBool s) = subst_valBool ((funcomp) (subst_val tauval) sigmaval) ((funcomp) (subst_valBool tauval tauvalBool) sigmavalBool) s .
Proof. exact (compSubstSubst_valBool sigmaval sigmavalBool tauval tauvalBool (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compComp'_valBool    (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) : (funcomp) (subst_valBool tauval tauvalBool) (subst_valBool sigmaval sigmavalBool) = subst_valBool ((funcomp) (subst_val tauval) sigmaval) ((funcomp) (subst_valBool tauval tauvalBool) sigmavalBool) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_valBool sigmaval sigmavalBool tauval tauvalBool n)). Qed.

End valBool.

Section exp.
Inductive exp  : Type :=
  | valE : ( valBool    ) -> exp  
  | andE : ( exp    ) -> ( exp    ) -> exp  .

Lemma congr_valE  { s0 : valBool    } { t0 : valBool    } (H1 : s0 = t0) : valE   s0 = valE   t0 .
Proof. congruence. Qed.

Lemma congr_andE  { s0 : exp    } { s1 : exp    } { t0 : exp    } { t1 : exp    } (H1 : s0 = t0) (H2 : s1 = t1) : andE   s0 s1 = andE   t0 t1 .
Proof. congruence. Qed.

Fixpoint subst_exp   (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (s : exp  ) : exp   :=
    match s return exp   with
    | valE   s0 => valE   ((subst_valBool sigmaval sigmavalBool) s0)
    | andE   s0 s1 => andE   ((subst_exp sigmaval sigmavalBool) s0) ((subst_exp sigmaval sigmavalBool) s1)
    end.

Fixpoint idSubst_exp  (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (Eqval : forall x, sigmaval x = (var_val ) x) (EqvalBool : forall x, sigmavalBool x = (var_valBool  ) x) (s : exp  ) : subst_exp sigmaval sigmavalBool s = s :=
    match s return subst_exp sigmaval sigmavalBool s = s with
    | valE   s0 => congr_valE ((idSubst_valBool sigmaval sigmavalBool Eqval EqvalBool) s0)
    | andE   s0 s1 => congr_andE ((idSubst_exp sigmaval sigmavalBool Eqval EqvalBool) s0) ((idSubst_exp sigmaval sigmavalBool Eqval EqvalBool) s1)
    end.

Fixpoint ext_exp   (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) (Eqval : forall x, sigmaval x = tauval x) (EqvalBool : forall x, sigmavalBool x = tauvalBool x) (s : exp  ) : subst_exp sigmaval sigmavalBool s = subst_exp tauval tauvalBool s :=
    match s return subst_exp sigmaval sigmavalBool s = subst_exp tauval tauvalBool s with
    | valE   s0 => congr_valE ((ext_valBool sigmaval sigmavalBool tauval tauvalBool Eqval EqvalBool) s0)
    | andE   s0 s1 => congr_andE ((ext_exp sigmaval sigmavalBool tauval tauvalBool Eqval EqvalBool) s0) ((ext_exp sigmaval sigmavalBool tauval tauvalBool Eqval EqvalBool) s1)
    end.

Fixpoint compSubstSubst_exp    (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) (thetaval : ( fin ) -> val ) (thetavalBool : ( fin ) -> valBool  ) (Eqval : forall x, ((funcomp) (subst_val tauval) sigmaval) x = thetaval x) (EqvalBool : forall x, ((funcomp) (subst_valBool tauval tauvalBool) sigmavalBool) x = thetavalBool x) (s : exp  ) : subst_exp tauval tauvalBool (subst_exp sigmaval sigmavalBool s) = subst_exp thetaval thetavalBool s :=
    match s return subst_exp tauval tauvalBool (subst_exp sigmaval sigmavalBool s) = subst_exp thetaval thetavalBool s with
    | valE   s0 => congr_valE ((compSubstSubst_valBool sigmaval sigmavalBool tauval tauvalBool thetaval thetavalBool Eqval EqvalBool) s0)
    | andE   s0 s1 => congr_andE ((compSubstSubst_exp sigmaval sigmavalBool tauval tauvalBool thetaval thetavalBool Eqval EqvalBool) s0) ((compSubstSubst_exp sigmaval sigmavalBool tauval tauvalBool thetaval thetavalBool Eqval EqvalBool) s1)
    end.

Lemma instId_exp  : subst_exp (var_val ) (var_valBool  ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_exp (var_val ) (var_valBool  ) (fun n => eq_refl) (fun n => eq_refl) ((id) x))). Qed.

Lemma compComp_exp    (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) (s : exp  ) : subst_exp tauval tauvalBool (subst_exp sigmaval sigmavalBool s) = subst_exp ((funcomp) (subst_val tauval) sigmaval) ((funcomp) (subst_valBool tauval tauvalBool) sigmavalBool) s .
Proof. exact (compSubstSubst_exp sigmaval sigmavalBool tauval tauvalBool (_) (_) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compComp'_exp    (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) : (funcomp) (subst_exp tauval tauvalBool) (subst_exp sigmaval sigmavalBool) = subst_exp ((funcomp) (subst_val tauval) sigmaval) ((funcomp) (subst_valBool tauval tauvalBool) sigmavalBool) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_exp sigmaval sigmavalBool tauval tauvalBool n)). Qed.

End exp.

Section msg.
Inductive msg  : Type :=
  | labelM : ( nat   ) -> msg    
  | valM : ( valBool    ) -> msg    
  | schM : ( sch    ) -> msg    .

Lemma congr_labelM  { s0 : nat   } { t0 : nat   } (H1 : s0 = t0) : labelM     s0 = labelM     t0 .
Proof. congruence. Qed.

Lemma congr_valM  { s0 : valBool    } { t0 : valBool    } (H1 : s0 = t0) : valM     s0 = valM     t0 .
Proof. congruence. Qed.

Lemma congr_schM  { s0 : sch    } { t0 : sch    } (H1 : s0 = t0) : schM     s0 = schM     t0 .
Proof. congruence. Qed.

Definition subst_msg   (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (s : msg    ) : msg     :=
    match s return msg     with
    | labelM     s0 => labelM     ((fun x => x) s0)
    | valM     s0 => valM     ((subst_valBool sigmaval sigmavalBool) s0)
    | schM     s0 => schM     ((subst_sch sigmaschl sigmasch) s0)
    end.

Definition up_val_schl   (sigma : ( fin ) -> schl ) : ( fin ) -> schl  :=
  (funcomp) (subst_schl (var_schl)) sigma.

Definition up_val_sch   (sigma : ( fin ) -> sch  ) : ( fin ) -> sch   :=
  (funcomp) (subst_sch (var_schl) (var_sch)) sigma.

Definition up_valBool_schl   (sigma : ( fin ) -> schl ) : ( fin ) -> schl  :=
  (funcomp) (subst_schl (var_schl)) sigma.

Definition up_valBool_sch   (sigma : ( fin ) -> sch  ) : ( fin ) -> sch   :=
  (funcomp) (subst_sch (var_schl) (var_sch)) sigma.

Definition up_schl_val   (sigma : ( fin ) -> val ) : ( fin ) -> val  :=
  (funcomp) (subst_val (var_val)) sigma.

Definition up_schl_valBool   (sigma : ( fin ) -> valBool  ) : ( fin ) -> valBool   :=
  (funcomp) (subst_valBool (var_val) (var_valBool)) sigma.

Definition up_sch_val   (sigma : ( fin ) -> val ) : ( fin ) -> val  :=
  (funcomp) (subst_val (var_val)) sigma.

Definition up_sch_valBool   (sigma : ( fin ) -> valBool  ) : ( fin ) -> valBool   :=
  (funcomp) (subst_valBool (var_val) (var_valBool)) sigma.

Definition upId_val_schl  (sigma : ( fin ) -> schl ) (Eq : forall x, sigma x = (var_schl ) x) : forall x, (up_val_schl sigma) x = (var_schl ) x :=
  fun n => (ap) (subst_schl (var_schl)) (Eq n).

Definition upId_val_sch  (sigma : ( fin ) -> sch  ) (Eq : forall x, sigma x = (var_sch  ) x) : forall x, (up_val_sch sigma) x = (var_sch  ) x :=
  fun n => (ap) (subst_sch (var_schl) (var_sch)) (Eq n).

Definition upId_valBool_schl  (sigma : ( fin ) -> schl ) (Eq : forall x, sigma x = (var_schl ) x) : forall x, (up_valBool_schl sigma) x = (var_schl ) x :=
  fun n => (ap) (subst_schl (var_schl)) (Eq n).

Definition upId_valBool_sch  (sigma : ( fin ) -> sch  ) (Eq : forall x, sigma x = (var_sch  ) x) : forall x, (up_valBool_sch sigma) x = (var_sch  ) x :=
  fun n => (ap) (subst_sch (var_schl) (var_sch)) (Eq n).

Definition upId_schl_val  (sigma : ( fin ) -> val ) (Eq : forall x, sigma x = (var_val ) x) : forall x, (up_schl_val sigma) x = (var_val ) x :=
  fun n => (ap) (subst_val (var_val)) (Eq n).

Definition upId_schl_valBool  (sigma : ( fin ) -> valBool  ) (Eq : forall x, sigma x = (var_valBool  ) x) : forall x, (up_schl_valBool sigma) x = (var_valBool  ) x :=
  fun n => (ap) (subst_valBool (var_val) (var_valBool)) (Eq n).

Definition upId_sch_val  (sigma : ( fin ) -> val ) (Eq : forall x, sigma x = (var_val ) x) : forall x, (up_sch_val sigma) x = (var_val ) x :=
  fun n => (ap) (subst_val (var_val)) (Eq n).

Definition upId_sch_valBool  (sigma : ( fin ) -> valBool  ) (Eq : forall x, sigma x = (var_valBool  ) x) : forall x, (up_sch_valBool sigma) x = (var_valBool  ) x :=
  fun n => (ap) (subst_valBool (var_val) (var_valBool)) (Eq n).

Definition idSubst_msg  (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (Eqval : forall x, sigmaval x = (var_val ) x) (EqvalBool : forall x, sigmavalBool x = (var_valBool  ) x) (Eqschl : forall x, sigmaschl x = (var_schl ) x) (Eqsch : forall x, sigmasch x = (var_sch  ) x) (s : msg    ) : subst_msg sigmaval sigmavalBool sigmaschl sigmasch s = s :=
    match s return subst_msg sigmaval sigmavalBool sigmaschl sigmasch s = s with
    | labelM     s0 => congr_labelM ((fun x => (eq_refl) x) s0)
    | valM     s0 => congr_valM ((idSubst_valBool sigmaval sigmavalBool Eqval EqvalBool) s0)
    | schM     s0 => congr_schM ((idSubst_sch sigmaschl sigmasch Eqschl Eqsch) s0)
    end.

Definition upExt_val_schl   (sigma : ( fin ) -> schl ) (tau : ( fin ) -> schl ) (Eq : forall x, sigma x = tau x) : forall x, (up_val_schl sigma) x = (up_val_schl tau) x :=
  fun n => (ap) (subst_schl (var_schl)) (Eq n).

Definition upExt_val_sch   (sigma : ( fin ) -> sch  ) (tau : ( fin ) -> sch  ) (Eq : forall x, sigma x = tau x) : forall x, (up_val_sch sigma) x = (up_val_sch tau) x :=
  fun n => (ap) (subst_sch (var_schl) (var_sch)) (Eq n).

Definition upExt_valBool_schl   (sigma : ( fin ) -> schl ) (tau : ( fin ) -> schl ) (Eq : forall x, sigma x = tau x) : forall x, (up_valBool_schl sigma) x = (up_valBool_schl tau) x :=
  fun n => (ap) (subst_schl (var_schl)) (Eq n).

Definition upExt_valBool_sch   (sigma : ( fin ) -> sch  ) (tau : ( fin ) -> sch  ) (Eq : forall x, sigma x = tau x) : forall x, (up_valBool_sch sigma) x = (up_valBool_sch tau) x :=
  fun n => (ap) (subst_sch (var_schl) (var_sch)) (Eq n).

Definition upExt_schl_val   (sigma : ( fin ) -> val ) (tau : ( fin ) -> val ) (Eq : forall x, sigma x = tau x) : forall x, (up_schl_val sigma) x = (up_schl_val tau) x :=
  fun n => (ap) (subst_val (var_val)) (Eq n).

Definition upExt_schl_valBool   (sigma : ( fin ) -> valBool  ) (tau : ( fin ) -> valBool  ) (Eq : forall x, sigma x = tau x) : forall x, (up_schl_valBool sigma) x = (up_schl_valBool tau) x :=
  fun n => (ap) (subst_valBool (var_val) (var_valBool)) (Eq n).

Definition upExt_sch_val   (sigma : ( fin ) -> val ) (tau : ( fin ) -> val ) (Eq : forall x, sigma x = tau x) : forall x, (up_sch_val sigma) x = (up_sch_val tau) x :=
  fun n => (ap) (subst_val (var_val)) (Eq n).

Definition upExt_sch_valBool   (sigma : ( fin ) -> valBool  ) (tau : ( fin ) -> valBool  ) (Eq : forall x, sigma x = tau x) : forall x, (up_sch_valBool sigma) x = (up_sch_valBool tau) x :=
  fun n => (ap) (subst_valBool (var_val) (var_valBool)) (Eq n).

Definition ext_msg   (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) (tauschl : ( fin ) -> schl ) (tausch : ( fin ) -> sch  ) (Eqval : forall x, sigmaval x = tauval x) (EqvalBool : forall x, sigmavalBool x = tauvalBool x) (Eqschl : forall x, sigmaschl x = tauschl x) (Eqsch : forall x, sigmasch x = tausch x) (s : msg    ) : subst_msg sigmaval sigmavalBool sigmaschl sigmasch s = subst_msg tauval tauvalBool tauschl tausch s :=
    match s return subst_msg sigmaval sigmavalBool sigmaschl sigmasch s = subst_msg tauval tauvalBool tauschl tausch s with
    | labelM     s0 => congr_labelM ((fun x => (eq_refl) x) s0)
    | valM     s0 => congr_valM ((ext_valBool sigmaval sigmavalBool tauval tauvalBool Eqval EqvalBool) s0)
    | schM     s0 => congr_schM ((ext_sch sigmaschl sigmasch tauschl tausch Eqschl Eqsch) s0)
    end.

Definition compSubstSubst_msg    (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) (tauschl : ( fin ) -> schl ) (tausch : ( fin ) -> sch  ) (thetaval : ( fin ) -> val ) (thetavalBool : ( fin ) -> valBool  ) (thetaschl : ( fin ) -> schl ) (thetasch : ( fin ) -> sch  ) (Eqval : forall x, ((funcomp) (subst_val tauval) sigmaval) x = thetaval x) (EqvalBool : forall x, ((funcomp) (subst_valBool tauval tauvalBool) sigmavalBool) x = thetavalBool x) (Eqschl : forall x, ((funcomp) (subst_schl tauschl) sigmaschl) x = thetaschl x) (Eqsch : forall x, ((funcomp) (subst_sch tauschl tausch) sigmasch) x = thetasch x) (s : msg    ) : subst_msg tauval tauvalBool tauschl tausch (subst_msg sigmaval sigmavalBool sigmaschl sigmasch s) = subst_msg thetaval thetavalBool thetaschl thetasch s :=
    match s return subst_msg tauval tauvalBool tauschl tausch (subst_msg sigmaval sigmavalBool sigmaschl sigmasch s) = subst_msg thetaval thetavalBool thetaschl thetasch s with
    | labelM     s0 => congr_labelM ((fun x => (eq_refl) x) s0)
    | valM     s0 => congr_valM ((compSubstSubst_valBool sigmaval sigmavalBool tauval tauvalBool thetaval thetavalBool Eqval EqvalBool) s0)
    | schM     s0 => congr_schM ((compSubstSubst_sch sigmaschl sigmasch tauschl tausch thetaschl thetasch Eqschl Eqsch) s0)
    end.

Definition up_subst_subst_val_schl    (sigma : ( fin ) -> schl ) (tauschl : ( fin ) -> schl ) (theta : ( fin ) -> schl ) (Eq : forall x, ((funcomp) (subst_schl tauschl) sigma) x = theta x) : forall x, ((funcomp) (subst_schl (up_val_schl tauschl)) (up_val_schl sigma)) x = (up_val_schl theta) x :=
  fun n => (eq_trans) (compSubstSubst_schl (var_schl) (up_val_schl tauschl) ((funcomp) (up_val_schl tauschl) ((id) (_))) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstSubst_schl tauschl (var_schl) ((funcomp) (subst_schl (var_schl)) tauschl) (fun x => eq_refl) (sigma n))) ((ap) (subst_schl (var_schl)) (Eq n))).

Definition up_subst_subst_val_sch    (sigma : ( fin ) -> sch  ) (tauschl : ( fin ) -> schl ) (tausch : ( fin ) -> sch  ) (theta : ( fin ) -> sch  ) (Eq : forall x, ((funcomp) (subst_sch tauschl tausch) sigma) x = theta x) : forall x, ((funcomp) (subst_sch (up_val_schl tauschl) (up_val_sch tausch)) (up_val_sch sigma)) x = (up_val_sch theta) x :=
  fun n => (eq_trans) (compSubstSubst_sch (var_schl) (var_sch) (up_val_schl tauschl) (up_val_sch tausch) ((funcomp) (up_val_schl tauschl) ((id) (_))) ((funcomp) (up_val_sch tausch) ((id) (_))) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstSubst_sch tauschl tausch (var_schl) (var_sch) ((funcomp) (subst_schl (var_schl)) tauschl) ((funcomp) (subst_sch (var_schl) (var_sch)) tausch) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (subst_sch (var_schl) (var_sch)) (Eq n))).

Definition up_subst_subst_valBool_schl    (sigma : ( fin ) -> schl ) (tauschl : ( fin ) -> schl ) (theta : ( fin ) -> schl ) (Eq : forall x, ((funcomp) (subst_schl tauschl) sigma) x = theta x) : forall x, ((funcomp) (subst_schl (up_valBool_schl tauschl)) (up_valBool_schl sigma)) x = (up_valBool_schl theta) x :=
  fun n => (eq_trans) (compSubstSubst_schl (var_schl) (up_valBool_schl tauschl) ((funcomp) (up_valBool_schl tauschl) ((id) (_))) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstSubst_schl tauschl (var_schl) ((funcomp) (subst_schl (var_schl)) tauschl) (fun x => eq_refl) (sigma n))) ((ap) (subst_schl (var_schl)) (Eq n))).

Definition up_subst_subst_valBool_sch    (sigma : ( fin ) -> sch  ) (tauschl : ( fin ) -> schl ) (tausch : ( fin ) -> sch  ) (theta : ( fin ) -> sch  ) (Eq : forall x, ((funcomp) (subst_sch tauschl tausch) sigma) x = theta x) : forall x, ((funcomp) (subst_sch (up_valBool_schl tauschl) (up_valBool_sch tausch)) (up_valBool_sch sigma)) x = (up_valBool_sch theta) x :=
  fun n => (eq_trans) (compSubstSubst_sch (var_schl) (var_sch) (up_valBool_schl tauschl) (up_valBool_sch tausch) ((funcomp) (up_valBool_schl tauschl) ((id) (_))) ((funcomp) (up_valBool_sch tausch) ((id) (_))) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstSubst_sch tauschl tausch (var_schl) (var_sch) ((funcomp) (subst_schl (var_schl)) tauschl) ((funcomp) (subst_sch (var_schl) (var_sch)) tausch) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (subst_sch (var_schl) (var_sch)) (Eq n))).

Definition up_subst_subst_schl_val    (sigma : ( fin ) -> val ) (tauval : ( fin ) -> val ) (theta : ( fin ) -> val ) (Eq : forall x, ((funcomp) (subst_val tauval) sigma) x = theta x) : forall x, ((funcomp) (subst_val (up_schl_val tauval)) (up_schl_val sigma)) x = (up_schl_val theta) x :=
  fun n => (eq_trans) (compSubstSubst_val (var_val) (up_schl_val tauval) ((funcomp) (up_schl_val tauval) ((id) (_))) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstSubst_val tauval (var_val) ((funcomp) (subst_val (var_val)) tauval) (fun x => eq_refl) (sigma n))) ((ap) (subst_val (var_val)) (Eq n))).

Definition up_subst_subst_schl_valBool    (sigma : ( fin ) -> valBool  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) (theta : ( fin ) -> valBool  ) (Eq : forall x, ((funcomp) (subst_valBool tauval tauvalBool) sigma) x = theta x) : forall x, ((funcomp) (subst_valBool (up_schl_val tauval) (up_schl_valBool tauvalBool)) (up_schl_valBool sigma)) x = (up_schl_valBool theta) x :=
  fun n => (eq_trans) (compSubstSubst_valBool (var_val) (var_valBool) (up_schl_val tauval) (up_schl_valBool tauvalBool) ((funcomp) (up_schl_val tauval) ((id) (_))) ((funcomp) (up_schl_valBool tauvalBool) ((id) (_))) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstSubst_valBool tauval tauvalBool (var_val) (var_valBool) ((funcomp) (subst_val (var_val)) tauval) ((funcomp) (subst_valBool (var_val) (var_valBool)) tauvalBool) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (subst_valBool (var_val) (var_valBool)) (Eq n))).

Definition up_subst_subst_sch_val    (sigma : ( fin ) -> val ) (tauval : ( fin ) -> val ) (theta : ( fin ) -> val ) (Eq : forall x, ((funcomp) (subst_val tauval) sigma) x = theta x) : forall x, ((funcomp) (subst_val (up_sch_val tauval)) (up_sch_val sigma)) x = (up_sch_val theta) x :=
  fun n => (eq_trans) (compSubstSubst_val (var_val) (up_sch_val tauval) ((funcomp) (up_sch_val tauval) ((id) (_))) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstSubst_val tauval (var_val) ((funcomp) (subst_val (var_val)) tauval) (fun x => eq_refl) (sigma n))) ((ap) (subst_val (var_val)) (Eq n))).

Definition up_subst_subst_sch_valBool    (sigma : ( fin ) -> valBool  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) (theta : ( fin ) -> valBool  ) (Eq : forall x, ((funcomp) (subst_valBool tauval tauvalBool) sigma) x = theta x) : forall x, ((funcomp) (subst_valBool (up_sch_val tauval) (up_sch_valBool tauvalBool)) (up_sch_valBool sigma)) x = (up_sch_valBool theta) x :=
  fun n => (eq_trans) (compSubstSubst_valBool (var_val) (var_valBool) (up_sch_val tauval) (up_sch_valBool tauvalBool) ((funcomp) (up_sch_val tauval) ((id) (_))) ((funcomp) (up_sch_valBool tauvalBool) ((id) (_))) (fun x => eq_refl) (fun x => eq_refl) (sigma n)) ((eq_trans) ((eq_sym) (compSubstSubst_valBool tauval tauvalBool (var_val) (var_valBool) ((funcomp) (subst_val (var_val)) tauval) ((funcomp) (subst_valBool (var_val) (var_valBool)) tauvalBool) (fun x => eq_refl) (fun x => eq_refl) (sigma n))) ((ap) (subst_valBool (var_val) (var_valBool)) (Eq n))).

Lemma instId_msg  : subst_msg (var_val ) (var_valBool  ) (var_schl ) (var_sch  ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_msg (var_val ) (var_valBool  ) (var_schl ) (var_sch  ) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) ((id) x))). Qed.

Lemma compComp_msg    (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) (tauschl : ( fin ) -> schl ) (tausch : ( fin ) -> sch  ) (s : msg    ) : subst_msg tauval tauvalBool tauschl tausch (subst_msg sigmaval sigmavalBool sigmaschl sigmasch s) = subst_msg ((funcomp) (subst_val tauval) sigmaval) ((funcomp) (subst_valBool tauval tauvalBool) sigmavalBool) ((funcomp) (subst_schl tauschl) sigmaschl) ((funcomp) (subst_sch tauschl tausch) sigmasch) s .
Proof. exact (compSubstSubst_msg sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch (_) (_) (_) (_) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compComp'_msg    (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) (tauschl : ( fin ) -> schl ) (tausch : ( fin ) -> sch  ) : (funcomp) (subst_msg tauval tauvalBool tauschl tausch) (subst_msg sigmaval sigmavalBool sigmaschl sigmasch) = subst_msg ((funcomp) (subst_val tauval) sigmaval) ((funcomp) (subst_valBool tauval tauvalBool) sigmavalBool) ((funcomp) (subst_schl tauschl) sigmaschl) ((funcomp) (subst_sch tauschl tausch) sigmasch) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_msg sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch n)). Qed.

End msg.

Section msgp.
Inductive msgp  : Type :=
  | msgT : ( msg      ) -> ( ptcp   ) -> msgp    .

Lemma congr_msgT  { s0 : msg      } { s1 : ptcp   } { t0 : msg      } { t1 : ptcp   } (H1 : s0 = t0) (H2 : s1 = t1) : msgT     s0 s1 = msgT     t0 t1 .
Proof. congruence. Qed.

Definition subst_msgp   (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (s : msgp    ) : msgp     :=
    match s return msgp     with
    | msgT     s0 s1 => msgT     ((subst_msg sigmaval sigmavalBool sigmaschl sigmasch) s0) ((fun x => x) s1)
    end.

Definition idSubst_msgp  (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (Eqval : forall x, sigmaval x = (var_val ) x) (EqvalBool : forall x, sigmavalBool x = (var_valBool  ) x) (Eqschl : forall x, sigmaschl x = (var_schl ) x) (Eqsch : forall x, sigmasch x = (var_sch  ) x) (s : msgp    ) : subst_msgp sigmaval sigmavalBool sigmaschl sigmasch s = s :=
    match s return subst_msgp sigmaval sigmavalBool sigmaschl sigmasch s = s with
    | msgT     s0 s1 => congr_msgT ((idSubst_msg sigmaval sigmavalBool sigmaschl sigmasch Eqval EqvalBool Eqschl Eqsch) s0) ((fun x => (eq_refl) x) s1)
    end.

Definition ext_msgp   (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) (tauschl : ( fin ) -> schl ) (tausch : ( fin ) -> sch  ) (Eqval : forall x, sigmaval x = tauval x) (EqvalBool : forall x, sigmavalBool x = tauvalBool x) (Eqschl : forall x, sigmaschl x = tauschl x) (Eqsch : forall x, sigmasch x = tausch x) (s : msgp    ) : subst_msgp sigmaval sigmavalBool sigmaschl sigmasch s = subst_msgp tauval tauvalBool tauschl tausch s :=
    match s return subst_msgp sigmaval sigmavalBool sigmaschl sigmasch s = subst_msgp tauval tauvalBool tauschl tausch s with
    | msgT     s0 s1 => congr_msgT ((ext_msg sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch Eqval EqvalBool Eqschl Eqsch) s0) ((fun x => (eq_refl) x) s1)
    end.

Definition compSubstSubst_msgp    (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) (tauschl : ( fin ) -> schl ) (tausch : ( fin ) -> sch  ) (thetaval : ( fin ) -> val ) (thetavalBool : ( fin ) -> valBool  ) (thetaschl : ( fin ) -> schl ) (thetasch : ( fin ) -> sch  ) (Eqval : forall x, ((funcomp) (subst_val tauval) sigmaval) x = thetaval x) (EqvalBool : forall x, ((funcomp) (subst_valBool tauval tauvalBool) sigmavalBool) x = thetavalBool x) (Eqschl : forall x, ((funcomp) (subst_schl tauschl) sigmaschl) x = thetaschl x) (Eqsch : forall x, ((funcomp) (subst_sch tauschl tausch) sigmasch) x = thetasch x) (s : msgp    ) : subst_msgp tauval tauvalBool tauschl tausch (subst_msgp sigmaval sigmavalBool sigmaschl sigmasch s) = subst_msgp thetaval thetavalBool thetaschl thetasch s :=
    match s return subst_msgp tauval tauvalBool tauschl tausch (subst_msgp sigmaval sigmavalBool sigmaschl sigmasch s) = subst_msgp thetaval thetavalBool thetaschl thetasch s with
    | msgT     s0 s1 => congr_msgT ((compSubstSubst_msg sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch thetaval thetavalBool thetaschl thetasch Eqval EqvalBool Eqschl Eqsch) s0) ((fun x => (eq_refl) x) s1)
    end.

Lemma instId_msgp  : subst_msgp (var_val ) (var_valBool  ) (var_schl ) (var_sch  ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_msgp (var_val ) (var_valBool  ) (var_schl ) (var_sch  ) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) ((id) x))). Qed.

Lemma compComp_msgp    (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) (tauschl : ( fin ) -> schl ) (tausch : ( fin ) -> sch  ) (s : msgp    ) : subst_msgp tauval tauvalBool tauschl tausch (subst_msgp sigmaval sigmavalBool sigmaschl sigmasch s) = subst_msgp ((funcomp) (subst_val tauval) sigmaval) ((funcomp) (subst_valBool tauval tauvalBool) sigmavalBool) ((funcomp) (subst_schl tauschl) sigmaschl) ((funcomp) (subst_sch tauschl tausch) sigmasch) s .
Proof. exact (compSubstSubst_msgp sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch (_) (_) (_) (_) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compComp'_msgp    (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) (tauschl : ( fin ) -> schl ) (tausch : ( fin ) -> sch  ) : (funcomp) (subst_msgp tauval tauvalBool tauschl tausch) (subst_msgp sigmaval sigmavalBool sigmaschl sigmasch) = subst_msgp ((funcomp) (subst_val tauval) sigmaval) ((funcomp) (subst_valBool tauval tauvalBool) sigmavalBool) ((funcomp) (subst_schl tauschl) sigmaschl) ((funcomp) (subst_sch tauschl tausch) sigmasch) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_msgp sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch n)). Qed.

End msgp.

Section process.
Definition label := nat.
Definition defIndex := nat. 
Definition qsize := nat.
Inductive process  : Type :=
  | SessReq : ( valBool    ) -> ( nat   ) -> ( qsize   ) -> ( process      ) -> process    
  | SessAcc : ( valBool    ) -> ( ptcp   ) -> ( process      ) -> process    
  | ValSend : ( sch    ) -> ( index   ) -> ( exp    ) -> ( process      ) -> process    
  | ValRec : ( sch    ) -> ( index   ) -> ( process      ) -> process    
  | SessDel : ( sch    ) -> ( index   ) -> ( sch    ) -> ( process      ) -> process    
  | SessRec : ( sch    ) -> ( index   ) -> ( process      ) -> process    
  | LabelSel : ( sch    ) -> ( index   ) -> ( label   ) -> ( process      ) -> process    
  | LabelBr : ( sch    ) -> ( index   ) -> ( seq (prod (nat  ) (process     )) ) -> process    
  | If : ( exp    ) -> ( process      ) -> ( process      ) -> process    
  | Par : ( process      ) -> ( process      ) -> process    
  | Inact : process    
  | ResCh : ( process      ) -> process    
  | ResVal : ( process      ) -> process    
  | PCall : ( defIndex   ) -> ( exp    ) -> ( seq (sch   ) ) -> process    
  | MsgQ : ( schli   ) -> ( seq (msgp     ) ) -> process    .

Lemma congr_SessReq  { s0 : valBool    } { s1 : nat   } { s2 : qsize   } { s3 : process      } { t0 : valBool    } { t1 : nat   } { t2 : qsize   } { t3 : process      } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) (H4 : s3 = t3) : SessReq     s0 s1 s2 s3 = SessReq     t0 t1 t2 t3 .
Proof. congruence. Qed.

Lemma congr_SessAcc  { s0 : valBool    } { s1 : ptcp   } { s2 : process      } { t0 : valBool    } { t1 : ptcp   } { t2 : process      } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : SessAcc     s0 s1 s2 = SessAcc     t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_ValSend  { s0 : sch    } { s1 : index   } { s2 : exp    } { s3 : process      } { t0 : sch    } { t1 : index   } { t2 : exp    } { t3 : process      } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) (H4 : s3 = t3) : ValSend     s0 s1 s2 s3 = ValSend     t0 t1 t2 t3 .
Proof. congruence. Qed.

Lemma congr_ValRec  { s0 : sch    } { s1 : index   } { s2 : process      } { t0 : sch    } { t1 : index   } { t2 : process      } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : ValRec     s0 s1 s2 = ValRec     t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_SessDel  { s0 : sch    } { s1 : index   } { s2 : sch    } { s3 : process      } { t0 : sch    } { t1 : index   } { t2 : sch    } { t3 : process      } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) (H4 : s3 = t3) : SessDel     s0 s1 s2 s3 = SessDel     t0 t1 t2 t3 .
Proof. congruence. Qed.

Lemma congr_SessRec  { s0 : sch    } { s1 : index   } { s2 : process      } { t0 : sch    } { t1 : index   } { t2 : process      } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : SessRec     s0 s1 s2 = SessRec     t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_LabelSel  { s0 : sch    } { s1 : index   } { s2 : label   } { s3 : process      } { t0 : sch    } { t1 : index   } { t2 : label   } { t3 : process      } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) (H4 : s3 = t3) : LabelSel     s0 s1 s2 s3 = LabelSel     t0 t1 t2 t3 .
Proof. congruence. Qed.

Lemma congr_LabelBr  { s0 : sch    } { s1 : index   } { s2 : seq (prod (nat  ) (process     )) } { t0 : sch    } { t1 : index   } { t2 : seq (prod (nat  ) (process     )) } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : LabelBr     s0 s1 s2 = LabelBr     t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_If  { s0 : exp    } { s1 : process      } { s2 : process      } { t0 : exp    } { t1 : process      } { t2 : process      } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : If     s0 s1 s2 = If     t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_Par  { s0 : process      } { s1 : process      } { t0 : process      } { t1 : process      } (H1 : s0 = t0) (H2 : s1 = t1) : Par     s0 s1 = Par     t0 t1 .
Proof. congruence. Qed.

Lemma congr_Inact  : Inact     = Inact     .
Proof. congruence. Qed.

Lemma congr_ResCh  { s0 : process      } { t0 : process      } (H1 : s0 = t0) : ResCh     s0 = ResCh     t0 .
Proof. congruence. Qed.

Lemma congr_ResVal  { s0 : process      } { t0 : process      } (H1 : s0 = t0) : ResVal     s0 = ResVal     t0 .
Proof. congruence. Qed.

Lemma congr_PCall  { s0 : defIndex   } { s1 : exp    } { s2 : seq (sch   ) } { t0 : defIndex   } { t1 : exp    } { t2 : seq (sch   ) } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : PCall     s0 s1 s2 = PCall     t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_MsgQ  { s0 : schli   } { s1 : seq (msgp     ) } { t0 : schli   } { t1 : seq (msgp     ) } (H1 : s0 = t0) (H2 : s1 = t1) : MsgQ     s0 s1 = MsgQ     t0 t1 .
Proof. congruence. Qed.

Fixpoint subst_process   (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (s : process    ) : process     :=
    match s return process     with
    | SessReq     s0 s1 s2 s3 => SessReq     ((subst_valBool sigmaval sigmavalBool) s0) ((fun x => x) s1) ((fun x => x) s2) ((subst_process (up_sch_val sigmaval) (up_sch_valBool sigmavalBool) (up_sch_schl sigmaschl) (up_sch_sch sigmasch)) s3)
    | SessAcc     s0 s1 s2 => SessAcc     ((subst_valBool sigmaval sigmavalBool) s0) ((fun x => x) s1) ((subst_process (up_sch_val sigmaval) (up_sch_valBool sigmavalBool) (up_sch_schl sigmaschl) (up_sch_sch sigmasch)) s2)
    | ValSend     s0 s1 s2 s3 => ValSend     ((subst_sch sigmaschl sigmasch) s0) ((fun x => x) s1) ((subst_exp sigmaval sigmavalBool) s2) ((subst_process sigmaval sigmavalBool sigmaschl sigmasch) s3)
    | ValRec     s0 s1 s2 => ValRec     ((subst_sch sigmaschl sigmasch) s0) ((fun x => x) s1) ((subst_process (up_valBool_val sigmaval) (up_valBool_valBool sigmavalBool) (up_valBool_schl sigmaschl) (up_valBool_sch sigmasch)) s2)
    | SessDel     s0 s1 s2 s3 => SessDel     ((subst_sch sigmaschl sigmasch) s0) ((fun x => x) s1) ((subst_sch sigmaschl sigmasch) s2) ((subst_process sigmaval sigmavalBool sigmaschl sigmasch) s3)
    | SessRec     s0 s1 s2 => SessRec     ((subst_sch sigmaschl sigmasch) s0) ((fun x => x) s1) ((subst_process (up_sch_val sigmaval) (up_sch_valBool sigmavalBool) (up_sch_schl sigmaschl) (up_sch_sch sigmasch)) s2)
    | LabelSel     s0 s1 s2 s3 => LabelSel     ((subst_sch sigmaschl sigmasch) s0) ((fun x => x) s1) ((fun x => x) s2) ((subst_process sigmaval sigmavalBool sigmaschl sigmasch) s3)
    | LabelBr     s0 s1 s2 => LabelBr     ((subst_sch sigmaschl sigmasch) s0) ((fun x => x) s1) ((map (prod_map (fun x => x) (subst_process sigmaval sigmavalBool sigmaschl sigmasch))) s2)
    | If     s0 s1 s2 => If     ((subst_exp sigmaval sigmavalBool) s0) ((subst_process sigmaval sigmavalBool sigmaschl sigmasch) s1) ((subst_process sigmaval sigmavalBool sigmaschl sigmasch) s2)
    | Par     s0 s1 => Par     ((subst_process sigmaval sigmavalBool sigmaschl sigmasch) s0) ((subst_process sigmaval sigmavalBool sigmaschl sigmasch) s1)
    | Inact      => Inact    
    | ResCh     s0 => ResCh     ((subst_process (up_schl_val sigmaval) (up_schl_valBool sigmavalBool) (up_schl_schl sigmaschl) (up_schl_sch sigmasch)) s0)
    | ResVal     s0 => ResVal     ((subst_process (up_val_val sigmaval) (up_val_valBool sigmavalBool) (up_val_schl sigmaschl) (up_val_sch sigmasch)) s0)
    | PCall     s0 s1 s2 => PCall     ((fun x => x) s0) ((subst_exp sigmaval sigmavalBool) s1) ((map (subst_sch sigmaschl sigmasch)) s2)
    | MsgQ     s0 s1 => MsgQ     ((subst_schli sigmaschl) s0) ((map (subst_msgp sigmaval sigmavalBool sigmaschl sigmasch)) s1)
    end.

Fixpoint idSubst_process  (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (Eqval : forall x, sigmaval x = (var_val ) x) (EqvalBool : forall x, sigmavalBool x = (var_valBool  ) x) (Eqschl : forall x, sigmaschl x = (var_schl ) x) (Eqsch : forall x, sigmasch x = (var_sch  ) x) (s : process    ) : subst_process sigmaval sigmavalBool sigmaschl sigmasch s = s :=
    match s return subst_process sigmaval sigmavalBool sigmaschl sigmasch s = s with
    | SessReq     s0 s1 s2 s3 => congr_SessReq ((idSubst_valBool sigmaval sigmavalBool Eqval EqvalBool) s0) ((fun x => (eq_refl) x) s1) ((fun x => (eq_refl) x) s2) ((idSubst_process (up_sch_val sigmaval) (up_sch_valBool sigmavalBool) (up_sch_schl sigmaschl) (up_sch_sch sigmasch) (upId_sch_val (_) Eqval) (upId_sch_valBool (_) EqvalBool) (upId_sch_schl (_) Eqschl) (upId_sch_sch (_) Eqsch)) s3)
    | SessAcc     s0 s1 s2 => congr_SessAcc ((idSubst_valBool sigmaval sigmavalBool Eqval EqvalBool) s0) ((fun x => (eq_refl) x) s1) ((idSubst_process (up_sch_val sigmaval) (up_sch_valBool sigmavalBool) (up_sch_schl sigmaschl) (up_sch_sch sigmasch) (upId_sch_val (_) Eqval) (upId_sch_valBool (_) EqvalBool) (upId_sch_schl (_) Eqschl) (upId_sch_sch (_) Eqsch)) s2)
    | ValSend     s0 s1 s2 s3 => congr_ValSend ((idSubst_sch sigmaschl sigmasch Eqschl Eqsch) s0) ((fun x => (eq_refl) x) s1) ((idSubst_exp sigmaval sigmavalBool Eqval EqvalBool) s2) ((idSubst_process sigmaval sigmavalBool sigmaschl sigmasch Eqval EqvalBool Eqschl Eqsch) s3)
    | ValRec     s0 s1 s2 => congr_ValRec ((idSubst_sch sigmaschl sigmasch Eqschl Eqsch) s0) ((fun x => (eq_refl) x) s1) ((idSubst_process (up_valBool_val sigmaval) (up_valBool_valBool sigmavalBool) (up_valBool_schl sigmaschl) (up_valBool_sch sigmasch) (upId_valBool_val (_) Eqval) (upId_valBool_valBool (_) EqvalBool) (upId_valBool_schl (_) Eqschl) (upId_valBool_sch (_) Eqsch)) s2)
    | SessDel     s0 s1 s2 s3 => congr_SessDel ((idSubst_sch sigmaschl sigmasch Eqschl Eqsch) s0) ((fun x => (eq_refl) x) s1) ((idSubst_sch sigmaschl sigmasch Eqschl Eqsch) s2) ((idSubst_process sigmaval sigmavalBool sigmaschl sigmasch Eqval EqvalBool Eqschl Eqsch) s3)
    | SessRec     s0 s1 s2 => congr_SessRec ((idSubst_sch sigmaschl sigmasch Eqschl Eqsch) s0) ((fun x => (eq_refl) x) s1) ((idSubst_process (up_sch_val sigmaval) (up_sch_valBool sigmavalBool) (up_sch_schl sigmaschl) (up_sch_sch sigmasch) (upId_sch_val (_) Eqval) (upId_sch_valBool (_) EqvalBool) (upId_sch_schl (_) Eqschl) (upId_sch_sch (_) Eqsch)) s2)
    | LabelSel     s0 s1 s2 s3 => congr_LabelSel ((idSubst_sch sigmaschl sigmasch Eqschl Eqsch) s0) ((fun x => (eq_refl) x) s1) ((fun x => (eq_refl) x) s2) ((idSubst_process sigmaval sigmavalBool sigmaschl sigmasch Eqval EqvalBool Eqschl Eqsch) s3)
    | LabelBr     s0 s1 s2 => congr_LabelBr ((idSubst_sch sigmaschl sigmasch Eqschl Eqsch) s0) ((fun x => (eq_refl) x) s1) ((seq_id (prod_id (fun x => (eq_refl) x) (idSubst_process sigmaval sigmavalBool sigmaschl sigmasch Eqval EqvalBool Eqschl Eqsch))) s2)
    | If     s0 s1 s2 => congr_If ((idSubst_exp sigmaval sigmavalBool Eqval EqvalBool) s0) ((idSubst_process sigmaval sigmavalBool sigmaschl sigmasch Eqval EqvalBool Eqschl Eqsch) s1) ((idSubst_process sigmaval sigmavalBool sigmaschl sigmasch Eqval EqvalBool Eqschl Eqsch) s2)
    | Par     s0 s1 => congr_Par ((idSubst_process sigmaval sigmavalBool sigmaschl sigmasch Eqval EqvalBool Eqschl Eqsch) s0) ((idSubst_process sigmaval sigmavalBool sigmaschl sigmasch Eqval EqvalBool Eqschl Eqsch) s1)
    | Inact      => congr_Inact 
    | ResCh     s0 => congr_ResCh ((idSubst_process (up_schl_val sigmaval) (up_schl_valBool sigmavalBool) (up_schl_schl sigmaschl) (up_schl_sch sigmasch) (upId_schl_val (_) Eqval) (upId_schl_valBool (_) EqvalBool) (upId_schl_schl (_) Eqschl) (upId_schl_sch (_) Eqsch)) s0)
    | ResVal     s0 => congr_ResVal ((idSubst_process (up_val_val sigmaval) (up_val_valBool sigmavalBool) (up_val_schl sigmaschl) (up_val_sch sigmasch) (upId_val_val (_) Eqval) (upId_val_valBool (_) EqvalBool) (upId_val_schl (_) Eqschl) (upId_val_sch (_) Eqsch)) s0)
    | PCall     s0 s1 s2 => congr_PCall ((fun x => (eq_refl) x) s0) ((idSubst_exp sigmaval sigmavalBool Eqval EqvalBool) s1) ((seq_id (idSubst_sch sigmaschl sigmasch Eqschl Eqsch)) s2)
    | MsgQ     s0 s1 => congr_MsgQ ((idSubst_schli sigmaschl Eqschl) s0) ((seq_id (idSubst_msgp sigmaval sigmavalBool sigmaschl sigmasch Eqval EqvalBool Eqschl Eqsch)) s1)
    end.

Fixpoint ext_process   (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) (tauschl : ( fin ) -> schl ) (tausch : ( fin ) -> sch  ) (Eqval : forall x, sigmaval x = tauval x) (EqvalBool : forall x, sigmavalBool x = tauvalBool x) (Eqschl : forall x, sigmaschl x = tauschl x) (Eqsch : forall x, sigmasch x = tausch x) (s : process    ) : subst_process sigmaval sigmavalBool sigmaschl sigmasch s = subst_process tauval tauvalBool tauschl tausch s :=
    match s return subst_process sigmaval sigmavalBool sigmaschl sigmasch s = subst_process tauval tauvalBool tauschl tausch s with
    | SessReq     s0 s1 s2 s3 => congr_SessReq ((ext_valBool sigmaval sigmavalBool tauval tauvalBool Eqval EqvalBool) s0) ((fun x => (eq_refl) x) s1) ((fun x => (eq_refl) x) s2) ((ext_process (up_sch_val sigmaval) (up_sch_valBool sigmavalBool) (up_sch_schl sigmaschl) (up_sch_sch sigmasch) (up_sch_val tauval) (up_sch_valBool tauvalBool) (up_sch_schl tauschl) (up_sch_sch tausch) (upExt_sch_val (_) (_) Eqval) (upExt_sch_valBool (_) (_) EqvalBool) (upExt_sch_schl (_) (_) Eqschl) (upExt_sch_sch (_) (_) Eqsch)) s3)
    | SessAcc     s0 s1 s2 => congr_SessAcc ((ext_valBool sigmaval sigmavalBool tauval tauvalBool Eqval EqvalBool) s0) ((fun x => (eq_refl) x) s1) ((ext_process (up_sch_val sigmaval) (up_sch_valBool sigmavalBool) (up_sch_schl sigmaschl) (up_sch_sch sigmasch) (up_sch_val tauval) (up_sch_valBool tauvalBool) (up_sch_schl tauschl) (up_sch_sch tausch) (upExt_sch_val (_) (_) Eqval) (upExt_sch_valBool (_) (_) EqvalBool) (upExt_sch_schl (_) (_) Eqschl) (upExt_sch_sch (_) (_) Eqsch)) s2)
    | ValSend     s0 s1 s2 s3 => congr_ValSend ((ext_sch sigmaschl sigmasch tauschl tausch Eqschl Eqsch) s0) ((fun x => (eq_refl) x) s1) ((ext_exp sigmaval sigmavalBool tauval tauvalBool Eqval EqvalBool) s2) ((ext_process sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch Eqval EqvalBool Eqschl Eqsch) s3)
    | ValRec     s0 s1 s2 => congr_ValRec ((ext_sch sigmaschl sigmasch tauschl tausch Eqschl Eqsch) s0) ((fun x => (eq_refl) x) s1) ((ext_process (up_valBool_val sigmaval) (up_valBool_valBool sigmavalBool) (up_valBool_schl sigmaschl) (up_valBool_sch sigmasch) (up_valBool_val tauval) (up_valBool_valBool tauvalBool) (up_valBool_schl tauschl) (up_valBool_sch tausch) (upExt_valBool_val (_) (_) Eqval) (upExt_valBool_valBool (_) (_) EqvalBool) (upExt_valBool_schl (_) (_) Eqschl) (upExt_valBool_sch (_) (_) Eqsch)) s2)
    | SessDel     s0 s1 s2 s3 => congr_SessDel ((ext_sch sigmaschl sigmasch tauschl tausch Eqschl Eqsch) s0) ((fun x => (eq_refl) x) s1) ((ext_sch sigmaschl sigmasch tauschl tausch Eqschl Eqsch) s2) ((ext_process sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch Eqval EqvalBool Eqschl Eqsch) s3)
    | SessRec     s0 s1 s2 => congr_SessRec ((ext_sch sigmaschl sigmasch tauschl tausch Eqschl Eqsch) s0) ((fun x => (eq_refl) x) s1) ((ext_process (up_sch_val sigmaval) (up_sch_valBool sigmavalBool) (up_sch_schl sigmaschl) (up_sch_sch sigmasch) (up_sch_val tauval) (up_sch_valBool tauvalBool) (up_sch_schl tauschl) (up_sch_sch tausch) (upExt_sch_val (_) (_) Eqval) (upExt_sch_valBool (_) (_) EqvalBool) (upExt_sch_schl (_) (_) Eqschl) (upExt_sch_sch (_) (_) Eqsch)) s2)
    | LabelSel     s0 s1 s2 s3 => congr_LabelSel ((ext_sch sigmaschl sigmasch tauschl tausch Eqschl Eqsch) s0) ((fun x => (eq_refl) x) s1) ((fun x => (eq_refl) x) s2) ((ext_process sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch Eqval EqvalBool Eqschl Eqsch) s3)
    | LabelBr     s0 s1 s2 => congr_LabelBr ((ext_sch sigmaschl sigmasch tauschl tausch Eqschl Eqsch) s0) ((fun x => (eq_refl) x) s1) ((seq_ext (prod_ext (fun x => (eq_refl) x) (ext_process sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch Eqval EqvalBool Eqschl Eqsch))) s2)
    | If     s0 s1 s2 => congr_If ((ext_exp sigmaval sigmavalBool tauval tauvalBool Eqval EqvalBool) s0) ((ext_process sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch Eqval EqvalBool Eqschl Eqsch) s1) ((ext_process sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch Eqval EqvalBool Eqschl Eqsch) s2)
    | Par     s0 s1 => congr_Par ((ext_process sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch Eqval EqvalBool Eqschl Eqsch) s0) ((ext_process sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch Eqval EqvalBool Eqschl Eqsch) s1)
    | Inact      => congr_Inact 
    | ResCh     s0 => congr_ResCh ((ext_process (up_schl_val sigmaval) (up_schl_valBool sigmavalBool) (up_schl_schl sigmaschl) (up_schl_sch sigmasch) (up_schl_val tauval) (up_schl_valBool tauvalBool) (up_schl_schl tauschl) (up_schl_sch tausch) (upExt_schl_val (_) (_) Eqval) (upExt_schl_valBool (_) (_) EqvalBool) (upExt_schl_schl (_) (_) Eqschl) (upExt_schl_sch (_) (_) Eqsch)) s0)
    | ResVal     s0 => congr_ResVal ((ext_process (up_val_val sigmaval) (up_val_valBool sigmavalBool) (up_val_schl sigmaschl) (up_val_sch sigmasch) (up_val_val tauval) (up_val_valBool tauvalBool) (up_val_schl tauschl) (up_val_sch tausch) (upExt_val_val (_) (_) Eqval) (upExt_val_valBool (_) (_) EqvalBool) (upExt_val_schl (_) (_) Eqschl) (upExt_val_sch (_) (_) Eqsch)) s0)
    | PCall     s0 s1 s2 => congr_PCall ((fun x => (eq_refl) x) s0) ((ext_exp sigmaval sigmavalBool tauval tauvalBool Eqval EqvalBool) s1) ((seq_ext (ext_sch sigmaschl sigmasch tauschl tausch Eqschl Eqsch)) s2)
    | MsgQ     s0 s1 => congr_MsgQ ((ext_schli sigmaschl tauschl Eqschl) s0) ((seq_ext (ext_msgp sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch Eqval EqvalBool Eqschl Eqsch)) s1)
    end.

Fixpoint compSubstSubst_process    (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) (tauschl : ( fin ) -> schl ) (tausch : ( fin ) -> sch  ) (thetaval : ( fin ) -> val ) (thetavalBool : ( fin ) -> valBool  ) (thetaschl : ( fin ) -> schl ) (thetasch : ( fin ) -> sch  ) (Eqval : forall x, ((funcomp) (subst_val tauval) sigmaval) x = thetaval x) (EqvalBool : forall x, ((funcomp) (subst_valBool tauval tauvalBool) sigmavalBool) x = thetavalBool x) (Eqschl : forall x, ((funcomp) (subst_schl tauschl) sigmaschl) x = thetaschl x) (Eqsch : forall x, ((funcomp) (subst_sch tauschl tausch) sigmasch) x = thetasch x) (s : process    ) : subst_process tauval tauvalBool tauschl tausch (subst_process sigmaval sigmavalBool sigmaschl sigmasch s) = subst_process thetaval thetavalBool thetaschl thetasch s :=
    match s return subst_process tauval tauvalBool tauschl tausch (subst_process sigmaval sigmavalBool sigmaschl sigmasch s) = subst_process thetaval thetavalBool thetaschl thetasch s with
    | SessReq     s0 s1 s2 s3 => congr_SessReq ((compSubstSubst_valBool sigmaval sigmavalBool tauval tauvalBool thetaval thetavalBool Eqval EqvalBool) s0) ((fun x => (eq_refl) x) s1) ((fun x => (eq_refl) x) s2) ((compSubstSubst_process (up_sch_val sigmaval) (up_sch_valBool sigmavalBool) (up_sch_schl sigmaschl) (up_sch_sch sigmasch) (up_sch_val tauval) (up_sch_valBool tauvalBool) (up_sch_schl tauschl) (up_sch_sch tausch) (up_sch_val thetaval) (up_sch_valBool thetavalBool) (up_sch_schl thetaschl) (up_sch_sch thetasch) (up_subst_subst_sch_val (_) (_) (_) Eqval) (up_subst_subst_sch_valBool (_) (_) (_) (_) EqvalBool) (up_subst_subst_sch_schl (_) (_) (_) Eqschl) (up_subst_subst_sch_sch (_) (_) (_) (_) Eqsch)) s3)
    | SessAcc     s0 s1 s2 => congr_SessAcc ((compSubstSubst_valBool sigmaval sigmavalBool tauval tauvalBool thetaval thetavalBool Eqval EqvalBool) s0) ((fun x => (eq_refl) x) s1) ((compSubstSubst_process (up_sch_val sigmaval) (up_sch_valBool sigmavalBool) (up_sch_schl sigmaschl) (up_sch_sch sigmasch) (up_sch_val tauval) (up_sch_valBool tauvalBool) (up_sch_schl tauschl) (up_sch_sch tausch) (up_sch_val thetaval) (up_sch_valBool thetavalBool) (up_sch_schl thetaschl) (up_sch_sch thetasch) (up_subst_subst_sch_val (_) (_) (_) Eqval) (up_subst_subst_sch_valBool (_) (_) (_) (_) EqvalBool) (up_subst_subst_sch_schl (_) (_) (_) Eqschl) (up_subst_subst_sch_sch (_) (_) (_) (_) Eqsch)) s2)
    | ValSend     s0 s1 s2 s3 => congr_ValSend ((compSubstSubst_sch sigmaschl sigmasch tauschl tausch thetaschl thetasch Eqschl Eqsch) s0) ((fun x => (eq_refl) x) s1) ((compSubstSubst_exp sigmaval sigmavalBool tauval tauvalBool thetaval thetavalBool Eqval EqvalBool) s2) ((compSubstSubst_process sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch thetaval thetavalBool thetaschl thetasch Eqval EqvalBool Eqschl Eqsch) s3)
    | ValRec     s0 s1 s2 => congr_ValRec ((compSubstSubst_sch sigmaschl sigmasch tauschl tausch thetaschl thetasch Eqschl Eqsch) s0) ((fun x => (eq_refl) x) s1) ((compSubstSubst_process (up_valBool_val sigmaval) (up_valBool_valBool sigmavalBool) (up_valBool_schl sigmaschl) (up_valBool_sch sigmasch) (up_valBool_val tauval) (up_valBool_valBool tauvalBool) (up_valBool_schl tauschl) (up_valBool_sch tausch) (up_valBool_val thetaval) (up_valBool_valBool thetavalBool) (up_valBool_schl thetaschl) (up_valBool_sch thetasch) (up_subst_subst_valBool_val (_) (_) (_) Eqval) (up_subst_subst_valBool_valBool (_) (_) (_) (_) EqvalBool) (up_subst_subst_valBool_schl (_) (_) (_) Eqschl) (up_subst_subst_valBool_sch (_) (_) (_) (_) Eqsch)) s2)
    | SessDel     s0 s1 s2 s3 => congr_SessDel ((compSubstSubst_sch sigmaschl sigmasch tauschl tausch thetaschl thetasch Eqschl Eqsch) s0) ((fun x => (eq_refl) x) s1) ((compSubstSubst_sch sigmaschl sigmasch tauschl tausch thetaschl thetasch Eqschl Eqsch) s2) ((compSubstSubst_process sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch thetaval thetavalBool thetaschl thetasch Eqval EqvalBool Eqschl Eqsch) s3)
    | SessRec     s0 s1 s2 => congr_SessRec ((compSubstSubst_sch sigmaschl sigmasch tauschl tausch thetaschl thetasch Eqschl Eqsch) s0) ((fun x => (eq_refl) x) s1) ((compSubstSubst_process (up_sch_val sigmaval) (up_sch_valBool sigmavalBool) (up_sch_schl sigmaschl) (up_sch_sch sigmasch) (up_sch_val tauval) (up_sch_valBool tauvalBool) (up_sch_schl tauschl) (up_sch_sch tausch) (up_sch_val thetaval) (up_sch_valBool thetavalBool) (up_sch_schl thetaschl) (up_sch_sch thetasch) (up_subst_subst_sch_val (_) (_) (_) Eqval) (up_subst_subst_sch_valBool (_) (_) (_) (_) EqvalBool) (up_subst_subst_sch_schl (_) (_) (_) Eqschl) (up_subst_subst_sch_sch (_) (_) (_) (_) Eqsch)) s2)
    | LabelSel     s0 s1 s2 s3 => congr_LabelSel ((compSubstSubst_sch sigmaschl sigmasch tauschl tausch thetaschl thetasch Eqschl Eqsch) s0) ((fun x => (eq_refl) x) s1) ((fun x => (eq_refl) x) s2) ((compSubstSubst_process sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch thetaval thetavalBool thetaschl thetasch Eqval EqvalBool Eqschl Eqsch) s3)
    | LabelBr     s0 s1 s2 => congr_LabelBr ((compSubstSubst_sch sigmaschl sigmasch tauschl tausch thetaschl thetasch Eqschl Eqsch) s0) ((fun x => (eq_refl) x) s1) ((seq_comp (prod_comp (fun x => (eq_refl) x) (compSubstSubst_process sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch thetaval thetavalBool thetaschl thetasch Eqval EqvalBool Eqschl Eqsch))) s2)
    | If     s0 s1 s2 => congr_If ((compSubstSubst_exp sigmaval sigmavalBool tauval tauvalBool thetaval thetavalBool Eqval EqvalBool) s0) ((compSubstSubst_process sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch thetaval thetavalBool thetaschl thetasch Eqval EqvalBool Eqschl Eqsch) s1) ((compSubstSubst_process sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch thetaval thetavalBool thetaschl thetasch Eqval EqvalBool Eqschl Eqsch) s2)
    | Par     s0 s1 => congr_Par ((compSubstSubst_process sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch thetaval thetavalBool thetaschl thetasch Eqval EqvalBool Eqschl Eqsch) s0) ((compSubstSubst_process sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch thetaval thetavalBool thetaschl thetasch Eqval EqvalBool Eqschl Eqsch) s1)
    | Inact      => congr_Inact 
    | ResCh     s0 => congr_ResCh ((compSubstSubst_process (up_schl_val sigmaval) (up_schl_valBool sigmavalBool) (up_schl_schl sigmaschl) (up_schl_sch sigmasch) (up_schl_val tauval) (up_schl_valBool tauvalBool) (up_schl_schl tauschl) (up_schl_sch tausch) (up_schl_val thetaval) (up_schl_valBool thetavalBool) (up_schl_schl thetaschl) (up_schl_sch thetasch) (up_subst_subst_schl_val (_) (_) (_) Eqval) (up_subst_subst_schl_valBool (_) (_) (_) (_) EqvalBool) (up_subst_subst_schl_schl (_) (_) (_) Eqschl) (up_subst_subst_schl_sch (_) (_) (_) (_) Eqsch)) s0)
    | ResVal     s0 => congr_ResVal ((compSubstSubst_process (up_val_val sigmaval) (up_val_valBool sigmavalBool) (up_val_schl sigmaschl) (up_val_sch sigmasch) (up_val_val tauval) (up_val_valBool tauvalBool) (up_val_schl tauschl) (up_val_sch tausch) (up_val_val thetaval) (up_val_valBool thetavalBool) (up_val_schl thetaschl) (up_val_sch thetasch) (up_subst_subst_val_val (_) (_) (_) Eqval) (up_subst_subst_val_valBool (_) (_) (_) (_) EqvalBool) (up_subst_subst_val_schl (_) (_) (_) Eqschl) (up_subst_subst_val_sch (_) (_) (_) (_) Eqsch)) s0)
    | PCall     s0 s1 s2 => congr_PCall ((fun x => (eq_refl) x) s0) ((compSubstSubst_exp sigmaval sigmavalBool tauval tauvalBool thetaval thetavalBool Eqval EqvalBool) s1) ((seq_comp (compSubstSubst_sch sigmaschl sigmasch tauschl tausch thetaschl thetasch Eqschl Eqsch)) s2)
    | MsgQ     s0 s1 => congr_MsgQ ((compSubstSubst_schli sigmaschl tauschl thetaschl Eqschl) s0) ((seq_comp (compSubstSubst_msgp sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch thetaval thetavalBool thetaschl thetasch Eqval EqvalBool Eqschl Eqsch)) s1)
    end.

Lemma instId_process  : subst_process (var_val ) (var_valBool  ) (var_schl ) (var_sch  ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_process (var_val ) (var_valBool  ) (var_schl ) (var_sch  ) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) ((id) x))). Qed.

Lemma compComp_process    (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) (tauschl : ( fin ) -> schl ) (tausch : ( fin ) -> sch  ) (s : process    ) : subst_process tauval tauvalBool tauschl tausch (subst_process sigmaval sigmavalBool sigmaschl sigmasch s) = subst_process ((funcomp) (subst_val tauval) sigmaval) ((funcomp) (subst_valBool tauval tauvalBool) sigmavalBool) ((funcomp) (subst_schl tauschl) sigmaschl) ((funcomp) (subst_sch tauschl tausch) sigmasch) s .
Proof. exact (compSubstSubst_process sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch (_) (_) (_) (_) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) s). Qed.

Lemma compComp'_process    (sigmaval : ( fin ) -> val ) (sigmavalBool : ( fin ) -> valBool  ) (sigmaschl : ( fin ) -> schl ) (sigmasch : ( fin ) -> sch  ) (tauval : ( fin ) -> val ) (tauvalBool : ( fin ) -> valBool  ) (tauschl : ( fin ) -> schl ) (tausch : ( fin ) -> sch  ) : (funcomp) (subst_process tauval tauvalBool tauschl tausch) (subst_process sigmaval sigmavalBool sigmaschl sigmasch) = subst_process ((funcomp) (subst_val tauval) sigmaval) ((funcomp) (subst_valBool tauval tauvalBool) sigmavalBool) ((funcomp) (subst_schl tauschl) sigmaschl) ((funcomp) (subst_sch tauschl tausch) sigmasch) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_process sigmaval sigmavalBool sigmaschl sigmasch tauval tauvalBool tauschl tausch n)). Qed.

End process.





















































(*





Global Instance Subst_val   : Subst1 (( fin ) -> val ) (val ) (val ) := @subst_val   .

Global Instance Subst_schl   : Subst1 (( fin ) -> schl ) (schl ) (schl ) := @subst_schl   .

Global Instance Subst_sch   : Subst2 (( fin ) -> schl ) (( fin ) -> sch  ) (sch  ) (sch  ) := @subst_sch     .

Global Instance Subst_schli   : Subst1 (( fin ) -> schl ) (schli ) (schli ) := @subst_schli   .

Global Instance Subst_valBool   : Subst2 (( fin ) -> val ) (( fin ) -> valBool  ) (valBool  ) (valBool  ) := @subst_valBool     .

Global Instance Subst_exp   : Subst2 (( fin ) -> val ) (( fin ) -> valBool  ) (exp  ) (exp  ) := @subst_exp     .

Global Instance Subst_msg   : Subst4 (( fin ) -> val ) (( fin ) -> valBool  ) (( fin ) -> schl ) (( fin ) -> sch  ) (msg    ) (msg    ) := @subst_msg         .

Global Instance Subst_msgp   : Subst4 (( fin ) -> val ) (( fin ) -> valBool  ) (( fin ) -> schl ) (( fin ) -> sch  ) (msgp    ) (msgp    ) := @subst_msgp         .

Global Instance Subst_process   : Subst4 (( fin ) -> val ) (( fin ) -> valBool  ) (( fin ) -> schl ) (( fin ) -> sch  ) (process    ) (process    ) := @subst_process         .


Notation "x '__val'" := (var_val x) (at level 5, format "x __val") : subst_scope.

Notation "x '__val'" := (@ids (_) (_) VarInstance_val x) (at level 5, only printing, format "x __val") : subst_scope.

Notation "'var'" := (var_val) (only printing, at level 1) : subst_scope.


Notation "x '__schl'" := (var_schl x) (at level 5, format "x __schl") : subst_scope.

Notation "x '__schl'" := (@ids (_) (_) VarInstance_schl x) (at level 5, only printing, format "x __schl") : subst_scope.

Notation "'var'" := (var_schl) (only printing, at level 1) : subst_scope.


Notation "x '__sch'" := (var_sch x) (at level 5, format "x __sch") : subst_scope.

Notation "x '__sch'" := (@ids (_) (_) VarInstance_sch x) (at level 5, only printing, format "x __sch") : subst_scope.

Notation "'var'" := (var_sch) (only printing, at level 1) : subst_scope.


Notation "x '__valBool'" := (var_valBool x) (at level 5, format "x __valBool") : subst_scope.

Notation "x '__valBool'" := (@ids (_) (_) VarInstance_valBool x) (at level 5, only printing, format "x __valBool") : subst_scope.

Notation "'var'" := (var_valBool) (only printing, at level 1) : subst_scope.

Class Up_val X Y := up_val : ( X ) -> Y.

Notation "↑__val" := (up_val) (only printing) : subst_scope.

Class Up_schl X Y := up_schl : ( X ) -> Y.

Notation "↑__schl" := (up_schl) (only printing) : subst_scope.

Class Up_sch X Y := up_sch : ( X ) -> Y.

Notation "↑__sch" := (up_sch) (only printing) : subst_scope.

Class Up_valBool X Y := up_valBool : ( X ) -> Y.

Notation "↑__valBool" := (up_valBool) (only printing) : subst_scope.

Notation "↑__sch" := (up_sch_val) (only printing) : subst_scope.

Global Instance Up_sch_val   : Up_val (_) (_) := @up_sch_val   .

Notation "↑__sch" := (up_sch_valBool) (only printing) : subst_scope.

Global Instance Up_sch_valBool   : Up_valBool (_) (_) := @up_sch_valBool    .

Notation "↑__sch" := (up_sch_schl) (only printing) : subst_scope.

Global Instance Up_sch_schl   : Up_schl (_) (_) := @up_sch_schl   .

Notation "↑__sch" := (up_sch_sch) (only printing) : subst_scope.

Global Instance Up_sch_sch   : Up_sch (_) (_) := @up_sch_sch    .

Notation "↑__valBool" := (up_valBool_val) (only printing) : subst_scope.

Global Instance Up_valBool_val   : Up_val (_) (_) := @up_valBool_val   .

Notation "↑__valBool" := (up_valBool_valBool) (only printing) : subst_scope.

Global Instance Up_valBool_valBool   : Up_valBool (_) (_) := @up_valBool_valBool    .

Notation "↑__valBool" := (up_valBool_schl) (only printing) : subst_scope.

Global Instance Up_valBool_schl   : Up_schl (_) (_) := @up_valBool_schl   .

Notation "↑__valBool" := (up_valBool_sch) (only printing) : subst_scope.

Global Instance Up_valBool_sch   : Up_sch (_) (_) := @up_valBool_sch    .

Notation "↑__schl" := (up_schl_val) (only printing) : subst_scope.

Global Instance Up_schl_val   : Up_val (_) (_) := @up_schl_val   .

Notation "↑__schl" := (up_schl_valBool) (only printing) : subst_scope.

Global Instance Up_schl_valBool   : Up_valBool (_) (_) := @up_schl_valBool    .

Notation "↑__schl" := (up_schl_schl) (only printing) : subst_scope.

Global Instance Up_schl_schl   : Up_schl (_) (_) := @up_schl_schl   .

Notation "↑__schl" := (up_schl_sch) (only printing) : subst_scope.

Global Instance Up_schl_sch   : Up_sch (_) (_) := @up_schl_sch    .

Notation "↑__val" := (up_val_val) (only printing) : subst_scope.

Global Instance Up_val_val   : Up_val (_) (_) := @up_val_val   .

Notation "↑__val" := (up_val_valBool) (only printing) : subst_scope.

Global Instance Up_val_valBool   : Up_valBool (_) (_) := @up_val_valBool    .

Notation "↑__val" := (up_val_schl) (only printing) : subst_scope.

Global Instance Up_val_schl   : Up_schl (_) (_) := @up_val_schl   .

Notation "↑__val" := (up_val_sch) (only printing) : subst_scope.

Global Instance Up_val_sch   : Up_sch (_) (_) := @up_val_sch    . *)

Notation "s [val sigmaval ]" := (subst_val sigmaval s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[val sigmaval ]" := (subst_val sigmaval) (at level 1, left associativity, only printing) : fscope.

Notation "s [schl sigmaschl ]" := (subst_schl sigmaschl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[schl sigmaschl ]" := (subst_schl sigmaschl) (at level 1, left associativity, only printing) : fscope.

Notation "s [sch sigmaschl ; sigmasch ]" := (subst_sch sigmaschl sigmasch s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[sch sigmaschl ; sigmasch ]" := (subst_sch sigmaschl sigmasch) (at level 1, left associativity, only printing) : fscope.

Notation "s [schli sigmaschl ]" := (subst_schli sigmaschl s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[schli sigmaschl ]" := (subst_schli sigmaschl) (at level 1, left associativity, only printing) : fscope.

Notation "s [valB sigmaval ; sigmavalBool ]" := (subst_valBool sigmaval sigmavalBool s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[valB sigmaval ; sigmavalBool ]" := (subst_valBool sigmaval sigmavalBool) (at level 1, left associativity, only printing) : fscope.

Notation "s [exp sigmaval ; sigmavalBool ]" := (subst_exp sigmaval sigmavalBool s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[exp sigmaval ; sigmavalBool ]" := (subst_exp sigmaval sigmavalBool) (at level 1, left associativity, only printing) : fscope.

Notation "s [msg sigmaval ; sigmavalBool ; sigmaschl ; sigmasch ]" := (subst_msg sigmaval sigmavalBool sigmaschl sigmasch s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[msg sigmaval ; sigmavalBool ; sigmaschl ; sigmasch ]" := (subst_msg sigmaval sigmavalBool sigmaschl sigmasch) (at level 1, left associativity, only printing) : fscope.

Notation "s [msgp sigmaval ; sigmavalBool ; sigmaschl ; sigmasch ]" := (subst_msgp sigmaval sigmavalBool sigmaschl sigmasch s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[msgp sigmaval ; sigmavalBool ; sigmaschl ; sigmasch ]" := (subst_msgp sigmaval sigmavalBool sigmaschl sigmasch) (at level 1, left associativity, only printing) : fscope.

Notation "s [p sigmaval ; sigmavalBool ; sigmaschl ; sigmasch ]" := (subst_process sigmaval sigmavalBool sigmaschl sigmasch s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[p sigmaval ; sigmavalBool ; sigmaschl ; sigmasch ]" := (subst_process sigmaval sigmavalBool sigmaschl sigmasch) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2. (*  Subst_val,  Subst_schl,  Subst_sch,  Subst_schli,  Subst_valBool,  Subst_exp,  Subst_msg,  Subst_msgp,  Subst_process,  VarInstance_val,  VarInstance_schl,  VarInstance_sch,  VarInstance_valBool.  *)

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2.  (* ,  Subst_val,  Subst_schl,  Subst_sch,  Subst_schli,  Subst_valBool,  Subst_exp,  Subst_msg,  Subst_msgp,  Subst_process,  VarInstance_val,  VarInstance_schl,  VarInstance_sch,  VarInstance_valBool in *.  *)

Lemma comp_id : forall (A B : Type) (f : A -> B), f >> ssrfun.id = f.
Proof. done. 
Qed. 

Ltac asimpl' := repeat first [progress rewrite ?comp_id | progress rewrite ?instId_val| progress rewrite ?compComp_val| progress rewrite ?compComp'_val| progress rewrite ?instId_schl| progress rewrite ?compComp_schl| progress rewrite ?compComp'_schl| progress rewrite ?instId_sch| progress rewrite ?compComp_sch| progress rewrite ?compComp'_sch| progress rewrite ?instId_schli| progress rewrite ?compComp_schli| progress rewrite ?compComp'_schli| progress rewrite ?instId_valBool| progress rewrite ?compComp_valBool| progress rewrite ?compComp'_valBool| progress rewrite ?instId_exp| progress rewrite ?compComp_exp| progress rewrite ?compComp'_exp| progress rewrite ?instId_msg| progress rewrite ?compComp_msg| progress rewrite ?compComp'_msg| progress rewrite ?instId_msgp| progress rewrite ?compComp_msgp| progress rewrite ?compComp'_msgp| progress rewrite ?instId_process| progress rewrite ?compComp_process| progress rewrite ?compComp'_process| progress rewrite ?varL_val| progress rewrite ?varL_schl| progress rewrite ?varL_sch| progress rewrite ?varL_valBool| progress (unfold up_ren, up_sch_val, up_sch_valBool, up_sch_schl, up_sch_sch, up_valBool_val, up_valBool_valBool, up_valBool_schl, up_valBool_sch, up_schl_val, up_schl_valBool, up_schl_schl, up_schl_sch, up_val_val, up_val_valBool, up_val_schl, up_val_sch)| progress (cbn [subst_val subst_schl subst_sch subst_schli subst_valBool subst_exp subst_msg subst_msgp subst_process])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_val in *| progress rewrite ?compComp_val in *| progress rewrite ?compComp'_val in *| progress rewrite ?instId_schl in *| progress rewrite ?compComp_schl in *| progress rewrite ?compComp'_schl in *| progress rewrite ?instId_sch in *| progress rewrite ?compComp_sch in *| progress rewrite ?compComp'_sch in *| progress rewrite ?instId_schli in *| progress rewrite ?compComp_schli in *| progress rewrite ?compComp'_schli in *| progress rewrite ?instId_valBool in *| progress rewrite ?compComp_valBool in *| progress rewrite ?compComp'_valBool in *| progress rewrite ?instId_exp in *| progress rewrite ?compComp_exp in *| progress rewrite ?compComp'_exp in *| progress rewrite ?instId_msg in *| progress rewrite ?compComp_msg in *| progress rewrite ?compComp'_msg in *| progress rewrite ?instId_msgp in *| progress rewrite ?compComp_msgp in *| progress rewrite ?compComp'_msgp in *| progress rewrite ?instId_process in *| progress rewrite ?compComp_process in *| progress rewrite ?compComp'_process in *| progress rewrite ?varL_val in *| progress rewrite ?varL_schl in *| progress rewrite ?varL_sch in *| progress rewrite ?varL_valBool in *| progress (unfold up_ren, up_sch_val, up_sch_valBool, up_sch_schl, up_sch_sch, up_valBool_val, up_valBool_valBool, up_valBool_schl, up_valBool_sch, up_schl_val, up_schl_valBool, up_schl_schl, up_schl_sch, up_val_val, up_val_valBool, up_val_schl, up_val_sch in * )| progress (cbn [subst_val subst_schl subst_sch subst_schli subst_valBool subst_exp subst_msg subst_msgp subst_process] in * )| fsimpl in *].

Ltac substify := auto_unfold.

Ltac renamify := auto_unfold.
