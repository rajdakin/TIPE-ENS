Require Import base.

(* Need(?) the -noinit flag *)

(* Inspired by https://github.com/coq-contribs/zfc/blob/master/zfc.v *)

Require Import Ltac.
Require Import Logic.
(* Attempting to reason without classical logic is too hard (and useless) *)
Require Import Classical.

(* ens ("superset") (transformation function) *)
Inductive Ensemble : Type := ens : forall A : Type, (A -> Ensemble) -> Ensemble.
Definition pi1e (e : Ensemble) := let (A, _) := e in A.
Definition pi2e (e : Ensemble) := match e return pi1e e -> Ensemble with ens _ f => f end.
Lemma ens_pi_is_orig : forall a : Ensemble, a = ens (pi1e a) (pi2e a).
Proof. by intros [A f]; exact (eq_refl _). Qed.
Fixpoint Ensemble_eq (a b : Ensemble) : Prop := let (a', f) := a in let (b', g) := b in
	   (forall x : a', exists y : b', Ensemble_eq (f x) (g y))
	/\ (forall y : b', exists x : a', Ensemble_eq (f x) (g y)).
Definition In (a B : Ensemble) := let (B', f) := B in exists b : B', Ensemble_eq a (f b).
Infix "inE" := In (at level 70, no associativity).
Notation "a 'not_in' b" := (~ (a inE b)) (at level 70, no associativity).
Definition Included (A B : Ensemble) : Prop :=
	forall e : Ensemble, (e inE A) -> (e inE B).
Infix "incl" := Included (at level 70, no associativity).
Definition NotIncluded (A B : Ensemble) : Prop :=
	exists e : Ensemble, (e inE A) /\ ~(e inE B).
Infix "not_incl" := NotIncluded (at level 70, no associativity).

Axiom extensionality_axiom
	: forall (A B : Ensemble), (forall x, ((x inE A) <-> (x inE B))) -> (A = B).
Axiom pairing_axiom
	: forall A B : Ensemble, exists C : Ensemble, forall x : Ensemble,
	(x inE C) <-> ((x = A) \/ (x = B)).
Axiom union_axiom
	: forall A : Ensemble, exists C : Ensemble, forall x,
	(x inE C) <-> exists Y, (Y inE A) /\ (x inE Y).
Axiom power_set_axiom : forall A : Ensemble, exists C : Ensemble,
	forall X, (X inE C) <-> (X incl A).
Axiom empty_set_axiom : exists E : Ensemble, E = E.
Axiom schema_restricted_comprehension_axiom :
	forall (P : Ensemble -> Prop) (A : Ensemble),
	exists C : Ensemble, forall x,
	(x inE C) <-> ((x inE A) /\ (P x)).

(* Ensemble_eq is defined by induction in a sense *)
Lemma Eeq_refl : forall a : Ensemble, Ensemble_eq a a.
Proof.
	by intros a; induction a as [a f IHa]; split;
	  intros x; exists x; exact (IHa x).
Qed.
Lemma Eeq_trans : forall a b c : Ensemble, Ensemble_eq a b -> Ensemble_eq b c -> Ensemble_eq a c.
Proof.
	intros a; induction a as [a f IHa]; intros [b g] [c h].
	minimize Ensemble_eq; intros [ainclb bincla] [binclc cinclb]; split.
	clear bincla cinclb; intros x.
	specialize (ainclb x) as [y xinbbyy]; specialize (binclc y) as [z yincbyz].
	by exists z; exact (IHa _ _ _ xinbbyy yincbyz).
	clear ainclb binclc; intros z.
	specialize (cinclb z) as [y zinbbyy]; specialize (bincla y) as [x yinabyx].
	by exists x; exact (IHa _ _ _ yinabyx zinbbyy).
Qed.
Lemma Eeq_sym : forall (a b : Ensemble), (Ensemble_eq a b) -> (Ensemble_eq b a).
Proof.
	intros a; induction a as [a f IHa]; intros [b g] [ainclb bincla]; split.
	by intros y; specialize (bincla y) as [x Hx]; exists x; exact (IHa _ _ Hx).
	by intros x; specialize (ainclb x) as [y Hy]; exists y; exact (IHa _ _ Hy).
Qed.
Lemma Eeq_is_eq : forall (a b : Ensemble), (Ensemble_eq a b) -> (a = b).
Proof.
	intros [a f] [b g] [ainclb bincla].
	apply extensionality_axiom; intros x; split.
	by intros [xa xinabyxa];
	   specialize (ainclb xa) as [y fxaeqgy];
	   exists y;
	   exact (Eeq_trans _ _ _ xinabyxa fxaeqgy).
	by intros [xb xinbbyxb];
	   specialize (bincla xb) as [y fyeqgxb];
	   exists y;
	   exact (Eeq_trans _ _ _ xinbbyxb (Eeq_sym _ _ fyeqgxb)).
Qed.
Lemma eq_is_Eeq : forall (a b : Ensemble), (a = b) -> (Ensemble_eq a b).
Proof. by intros a ? H; rewrite <-H; exact (Eeq_refl a). Qed.
Arguments Eeq_refl a : clear implicits.
Arguments Eeq_trans {a b c} ainclb binclc.
Arguments Eeq_sym {a b} ainclb.
Arguments Eeq_is_eq {a b} aEeqb.
Arguments eq_is_Eeq {a b} aeqb.

Lemma incl_refl : forall a : Ensemble, a incl a.
Proof. by intros a b bina; exact bina. Qed.
Lemma incl_trans : forall a b c : Ensemble, a incl b -> b incl c -> a incl c.
Proof.
	intros a b c ainclb binclc x xina.
	by exact (binclc _ (ainclb _ xina)).
Qed.
Lemma incl_antisym : forall a b : Ensemble, a incl b -> b incl a -> Ensemble_eq a b.
Proof.
	intros [a f] [b g] ainclb bincla; split.
	intros x.
	assert (fxina : f x inE (ens a f)) by (exists x; exact (Eeq_refl _)).
	by exact (ainclb _ fxina).
	intros y.
	assert (gyinb : g y inE (ens b g)) by (exists y; exact (Eeq_refl _)).
	specialize (bincla _ gyinb) as [x gyeqfx].
	by exists x; exact (Eeq_sym gyeqfx).
Qed.
Lemma Eeq_incl_l : forall a b : Ensemble, Ensemble_eq a b -> a incl b.
Proof.
	by intros a b aeqb; rewrite (Eeq_is_eq aeqb); exact (incl_refl _).
Qed.
Lemma Eeq_incl_r : forall a b : Ensemble, Ensemble_eq a b -> b incl a.
Proof.
	by intros a b beqa; rewrite (Eeq_is_eq beqa); exact (incl_refl _).
Qed.
Arguments incl_refl a : clear implicits.
Arguments incl_trans {a b c} ainclb binclc.
Arguments incl_antisym {a b} ainclb bincla.
Arguments Eeq_incl_l {a b} aeqb.
Arguments Eeq_incl_r {a b} aeqb.

Lemma notincl_not_incl : forall a b : _, (a not_incl b) -> ~ (a incl b).
Proof. by intros a b [e [eina enib]] ainclb; exact (enib (ainclb _ eina)). Qed.
Lemma not_incl_notincl : forall a b : _, ~ (a incl b) -> (a not_incl b).
Proof.
	intros a b nainclb.
	specialize (not_all_ex_not _ _ nainclb) as [e He].
	by exists e; exact (imply_to_and _ _ He).
Qed.
Arguments notincl_not_incl {a b} anib.
Arguments not_incl_notincl {a b} anib.

Lemma ex_empty_set : exists E : Ensemble, forall x, ~ (x inE E).
Proof.
	specialize empty_set_axiom as [e _].
	specialize (schema_restricted_comprehension_axiom (fun x => x <> x) e) as [V HV].
	exists V; intros x xiV.
	by exact (proj2 (proj1 (iff_and (HV x)) xiV) (eq_refl x)).
Qed.
Definition EmptySet := ens False (fun f => match f return Ensemble with end).
Lemma empty_is_empty : forall x, x not_in EmptySet.
Proof. by intros _ [[] _]. Qed.
Lemma empty_is_empty' : ~ (exists x, x inE EmptySet).
Proof. by intros [_ [[] _]]. Qed.
Lemma empties_are_empty : forall a : Ensemble, (~ (exists x, x inE a)) -> (a = EmptySet).
Proof.
	intros a ae.
	apply Eeq_is_eq, incl_antisym.
	intros x xina.
	by is_false (ae (ex_intro _ x xina)).
	intros ? [[] _]. (* is_false *)
	(* intros [a f] ae.
	apply Eeq_is_eq; split.
	2: by intros y; is_false y.
	intros x.
	elim ae. (* exfalso; apply ae *)
	exists (f x), x.
	by exact (Eeq_refl _). *)
Qed.
Corollary non_empty_is_not_empty : forall A : Ensemble,
  (A <> EmptySet) -> exists x : _, x inE A.
Proof.
	intros a anee.
	apply NNPP; intros nexxina.
	by exact (anee (empties_are_empty a nexxina)).
	(* intros [A f] Ane.
	specialize (classic (exists x, x inE ens A f)) as [exx | nex].
	by exact exx.
	specialize (not_ex_all_not _ _ nex) as nex'; clear nex; rename nex' into nex; lazy beta in nex.
	elim Ane.
	apply Eeq_is_eq.
	split.
	intros x.
	by elim (nex (f x) (ex_intro _ x (Eeq_refl _))).
	by intros y; elim y. *)
Qed.

Corollary ex_union_set : forall A B : Ensemble, exists C : Ensemble,
	forall x, (x inE C) <-> ((x inE A) \/ (x inE B)).
Proof.
	intros a b.
	specialize (pairing_axiom a b) as [c' Hc'].
	specialize (union_axiom c') as [c Hc].
	exists c; intros x; specialize (Hc x) as [xincisexy exyisxinc]; split.
	intros xinc; specialize (xincisexy xinc) as [y [yinc' xiny]].
	by specialize (proj1 (iff_and (Hc' y)) yinc') as [xeq | xeq];
	  rewrite xeq in xiny; [left | right]; exact xiny.
	intros [xin | xin]; apply exyisxinc; [exists a | exists b]; split.
	1: by exact (proj2 (iff_and (Hc' a)) (or_introl (eq_refl _))).
	2: by exact (proj2 (iff_and (Hc' b)) (or_intror (eq_refl _))).
	1,2: by exact xin.
	(* intros A B.
	specialize (pairing_axiom A B) as [C' HC'].
	specialize (union_axiom C') as [C HC].
	exists C; intros x; specialize (HC x); split.
	intros xinC; specialize HC as [HC _]; specialize (HC xinC) as [Y [HY Hx]].
	specialize (HC' Y) as [HC' _]; specialize (HC' HY) as [YA | YB].
	by left;  rewrite <-YA; exact Hx.
	by right; rewrite <-YB; exact Hx.
	by intros [Hx | Hx];
		specialize HC as [_ HC]; apply HC; clear HC C;
		[specialize (HC' A) as [_ HC'];
		specialize (HC' (or_introl (eq_refl A))); exists A
		|specialize (HC' B) as [_ HC'];
		specialize (HC' (or_intror (eq_refl B))); exists B]; exact (conj HC' Hx). *)
Qed.
Inductive bool' := | leftopt : bool' | rightopt : bool'.
Definition pairing_cons (A B : Ensemble)
	:= ens bool' (fun b => match b with | leftopt => A | rightopt => B end).
Definition singleton (x : Ensemble) := pairing_cons x x.
(* Inductive ExistsSigma (P : Type) (Q : P -> Prop) : Type
	:= ex_sigma : forall x : P, Q x -> ExistsSigma P Q. === exist *)
(* Definition separation_cons (A : Ensemble) (P : Ensemble -> Prop) : Ensemble.
	destruct A as [A f].
	apply (ens (ExistsSigma _ (fun x => P (f x)))).
	intros [x _]. exact (f x).
Defined. *)
Definition separation_cons (A : Ensemble) (P : Ensemble -> Prop) : Ensemble :=
	let (A', f) := A in
	 ens { x : A' | P (f x) }
	  (fun p : { x : A' | P (f x) } => match p with exist _ x _ => f x end).

Lemma separation_cons_included : forall (A : Ensemble) (P : Ensemble -> Prop),
	(separation_cons A P) incl A.
Proof.
	intros [A f] P x [[y _] xinabyy].
	by exists y; exact xinabyy.
Qed.
Lemma separation_cons_separated : forall (A : Ensemble) (P : Ensemble -> Prop) x,
	(x inE separation_cons A P) -> P x.
Proof.
	intros [A f] P x [[y Pfy] xinsepbyy].
	by rewrite (Eeq_is_eq xinsepbyy); exact Pfy.
Qed.
Lemma separation_cons_separates : forall (A : Ensemble) (P : Ensemble -> Prop) x,
	(x inE A) -> P x -> (x inE separation_cons A P).
Proof.
	intros [A f] P x [y xinAbyy] Px.
	rewrite (Eeq_is_eq xinAbyy) in Px.
	by exists (exist _ y Px); exact xinAbyy.
Qed.

(* Inductive TypePower (P : Type) (Q : P -> Type) : Type
	:= type_pow : forall x : P, forall y : Q x, TypePower P Q. === sigT *)
(* Definition ens_union_cons (A : Ensemble) : Ensemble.
	destruct A as [A f].
	apply (ens (TypePower _ (fun x : A => pi1e (f x)))).
	intros [a imgA].
	exact (pi2e (f a) imgA).
Defined. *)
(* For all Ensemble A,
 * ens_union_cons constructs a type that is then mapped to all elements
 *  of the elements of A.
 * existT x y: x is of the type of A, and maps to B by A;
 *   then y is of the type A, and maps to the final set by B.
 *)
Definition ens_union_cons (A : Ensemble) : Ensemble := let (A', f) := A in
	ens { x : A' & pi1e (f x) }
		(fun X => match X with existT _ x y => pi2e (f x) y end).
Definition pair_union_cons (A B : Ensemble) : Ensemble
	:= ens_union_cons (pairing_cons A B).

Infix "\union" := pair_union_cons (at level 150, left associativity).
Notation "'\Union' a" := (ens_union_cons a) (at level 150, no associativity).
Notation "a \\ b" := (separation_cons a (fun x => x not_in b)) (at level 150, no associativity).
Definition inter a b := separation_cons a (fun x => x inE b).
Infix "\inter" := inter (at level 150, left associativity).

Lemma ens_union_is_union : forall A : Ensemble, forall B : Ensemble,
	B inE (ens_union_cons A) -> exists C : Ensemble, C inE A /\ B inE C.
Proof.
	intros [A f] [B g] [[x y] BinCbyy].
	remember (f x) as fx eqn:eqnfx; destruct fx as [C h].
	exists (ens C h); split.
	by exists x; exact (eq_is_Eeq eqnfx).
	by exists y; exact BinCbyy.
Qed.
Lemma union_is_ens_union : forall A : Ensemble, forall B : Ensemble,
	(B inE A) -> B incl (ens_union_cons A).
Proof.
	intros [A f] [B g] [x BinAbyx] [C h] [y CinBbyy].
	rewrite (ens_pi_is_orig (f x)) in BinAbyx.
	destruct BinAbyx as [Binclfx _].
	specialize (Binclfx y) as [y' gxinfxbyy'].
	specialize (Eeq_trans CinBbyy gxinfxbyy') as Cinfxbyy'; clear gxinfxbyy'.
	exists (existT _ x y').
	by exact Cinfxbyy'.
Qed.

Lemma l_in_pairing : forall A B : Ensemble, A inE (pairing_cons A B).
Proof.
	by intros A B; exists leftopt; exact (Eeq_refl _).
Qed.
Lemma r_in_pairing : forall A B : Ensemble, B inE (pairing_cons A B).
Proof.
	by intros A B; exists rightopt; exact (Eeq_refl _).
Qed.
Lemma pairing_is_lr : forall A B C : Ensemble, C inE (pairing_cons A B) -> C = A \/ C = B.
Proof.
	intros A B C [[|] eeq].
	by left;  exact (Eeq_is_eq eeq).
	by right; exact (Eeq_is_eq eeq).
Qed.
Lemma pair_union_is_union_l : forall A B : Ensemble, A incl (pair_union_cons A B).
Proof.
	intros A B e einA.
	by exact (union_is_ens_union (pairing_cons A B) A (l_in_pairing _ _) _ einA).
Qed.
Lemma pair_union_is_union_r : forall A B : Ensemble, B incl (pair_union_cons A B).
Proof.
	intros A B e einB.
	by exact (union_is_ens_union (pairing_cons A B) B (r_in_pairing _ _) _ einB).
Qed.
Lemma pair_union_is_union : forall A B C : Ensemble,
	C inE (pair_union_cons A B) -> C inE A \/ C inE B.
Proof.
	intros [A f] [B g] [C h] [[[|] xval] CinAuBbyx].
	by left;  exists xval; exact CinAuBbyx.
	by right; exists xval; exact CinAuBbyx.
Qed.

Lemma singleton_has_elem : forall A : Ensemble, A inE (singleton A).
Proof.
	by intros [A f]; exists leftopt; exact (Eeq_refl _).
Qed.
Lemma singleton_is_singleton : forall A B : Ensemble, B inE (singleton A) -> B = A.
Proof.
	by intros A B BinsA;
	 specialize (pairing_is_lr _ _ _ BinsA) as [H | H];
	 exact H.
Qed.
Lemma singleton_incl_is_in : forall A B : Ensemble, (singleton A) incl B -> A inE B.
Proof.
	intros [A f] [B g] sAinclB.
	by exact (sAinclB _ (singleton_has_elem (ens A f))).
Qed.

Lemma exists_inter_set
 : forall A, (A <> EmptySet) ->
  exists C, forall x, (x inE C) <-> (forall a, (a inE A) -> (x inE a)).
Proof.
	intros A Ane.
	specialize (non_empty_is_not_empty _ Ane) as [a0 a0inA]; clear Ane.
	specialize (schema_restricted_comprehension_axiom
	 (fun e => (forall a, (a inE A) -> (e inE a))) a0) as [C HC].
	exists C; intros x; specialize (HC x) as [HCl HCr]; split; [clear HCr | clear HCl].
	by intros xiC; exact (proj2 (HCl xiC)).
	by intros H0; exact (HCr (conj (H0 _ a0inA) H0)).
Qed.

Definition Succ (A : Ensemble) := pair_union_cons A (singleton A).
Definition is_nat (A : Ensemble) :=
	(EmptySet inE A) /\ forall x, (x inE A) -> ((Succ x) inE A).
Axiom infinity_axiom : exists N : Ensemble,
	(is_nat N) /\ (forall a, (is_nat a) -> N incl a).

Lemma e_in_succ : forall e : Ensemble, e inE Succ e.
Proof.
	intros e.
	by apply (pair_union_is_union_r _), singleton_has_elem.
Qed.
Lemma e_incl_succ : forall e : Ensemble, e incl Succ e.
Proof.
	intros e.
	by unfold Succ; exact (pair_union_is_union_l _ _).
Qed.

Inductive nat :=
	| O : nat
	| S : nat -> nat.
Fixpoint N (n : nat) : Ensemble := match n with O => EmptySet | S n => Succ (N n) end.
Definition Nnat : Ensemble := ens nat N.

Lemma induction_N (P : Ensemble -> Prop) :
 P (N O) -> (forall e : Ensemble, P e -> P (Succ e)) -> forall n : nat, P (N n).
Proof.
	intros I IH.
	specialize (schema_restricted_comprehension_axiom P Nnat) as [[C h] Cprop].
	assert (C_is_nat : is_nat (ens C h)).
	{ split.
	  apply (proj2 (iff_and (Cprop EmptySet))); split.
	  by exists O; exact (Eeq_refl _).
	  by exact I.
	  intros x xinC.
	  specialize (proj1 (iff_and (Cprop x)) xinC) as [[n xinNnatbyn] Px].
	  apply (proj2 (iff_and (Cprop (Succ x)))); split.
	  apply Eeq_is_eq in xinNnatbyn; rewrite xinNnatbyn.
	  by exists (S n); exact (Eeq_refl _).
	  by exact (IH x Px). }
	intros n.
	destruct C_is_nat as [einC IHC].
	induction n as [|n IHn]. (* Seems weird to do this, but oh well... (N is defined weirdly) *)
	by exact (proj2 (proj1 (iff_and (Cprop (N O))) einC)).
	(* I hate intermediary steps :p (basically, use Cprop the two ways, then IHC) *)
	by exact (proj2 (proj1 (iff_and (Cprop _)) (IHC _ 
		(proj2 (iff_and (Cprop (N n))) (conj (ex_intro _ n (Eeq_refl _)) IHn))))).
Qed.
Lemma double_induction : forall P : nat -> Prop, P O -> P (S O) ->
  (forall n : nat, P n -> P (S n) -> P (S (S n))) -> forall n, P n.
Proof.
	intros P I0 I1 IH.
	assert (H : forall n : nat, P n /\ P (S n)).
	{ intros n; induction n as [|n [IHn IHSn]]; split.
	  by exact I0. by exact I1.
	  by exact IHSn.
	  by exact (IH _ IHn IHSn). }
	by intros n; exact (proj1 (H _)).
Qed.

Lemma N_in_nat : forall a : _, is_nat a -> Nnat incl a.
Proof.
	intros a [eina succaincla] Nn [n NninNbyn].
	rewrite (Eeq_is_eq NninNbyn).
	by exact (induction_N (fun k => k inE a) eina succaincla n).
	(* forall n : nat, forall a : Ensemble, is_nat a -> N n inE a.
	intros n [A f] anat; induction n as [|n [m Hm]].
	destruct anat as [[x einabyx] _].
	by exists x; exact einabyx.
	destruct anat as [_ anat].
	specialize (anat (N n)).
	apply anat; clear anat.
	exists m. by exact Hm. *)
Qed.
Lemma N_is_nat : is_nat Nnat.
Proof.
	split.
	by exists O; exact (Eeq_refl _).
	intros x [n xinNbyn].
	rewrite (Eeq_is_eq xinNbyn).
	by exists (S n); exact (Eeq_refl _).
Qed.
Lemma nat_in_N : forall a : Ensemble, is_nat a -> (forall b : Ensemble, is_nat b -> a incl b) -> forall n : Ensemble, n inE a -> exists k : nat, n = N k.
Proof.
	intros a [eina succaincla] ainclallnat n nina.
	specialize (ainclallnat Nnat N_is_nat) as ainclN.
	specialize (ainclN _ nina) as [b ninNbyb].
	by exists b; exact (Eeq_is_eq ninNbyb).
Qed.

Inductive LessThan_iterc : nat -> nat -> Type :=
	| ltic_o : forall n : nat, LessThan_iterc O (S n)
	| ltic_iter : forall m n : nat, LessThan_iterc m n -> LessThan_iterc (S m) (S n).
Inductive GreaterEqual_iterc : nat -> nat -> Type :=
	| geic_o : forall m : nat, GreaterEqual_iterc m O
	| geic_iter : forall m n : nat, GreaterEqual_iterc m n
		-> GreaterEqual_iterc (S m) (S n).
Fixpoint Min (m : nat) (n : nat) : nat := match m, n with
	| O, _ | _, O => O
	| S m', S n' => S (Min m' n') end.
Arguments ltic_iter {m n} p.
Arguments geic_iter {m n} p.
Definition LessThan_iter m n := exists p : LessThan_iterc m n, p = p.
Definition GreaterEqual_iter m n := exists p : GreaterEqual_iterc m n, p = p.
Definition ltc2lt_iter m n p := ex_intro (fun p: LessThan_iterc m n => p = p) p (eq_refl p).
Definition gec2ge_iter m n p := ex_intro (fun p: GreaterEqual_iterc m n => p = p) p (eq_refl p).
Arguments ltc2lt_iter {m n} p.
Arguments gec2ge_iter {m n} p.
Definition lti_o n := ltc2lt_iter (ltic_o n).
Definition gei_o n := gec2ge_iter (geic_o n).
Definition lti_iter {m n} (p : LessThan_iter _ _)
	:= let (p', _) := p in ltc2lt_iter (ltic_iter (m:=m) (n:=n) p').
Definition gei_iter {m n} (p : GreaterEqual_iter _ _)
	:= let (p', _) := p in gec2ge_iter (geic_iter (m:=m) (n:=n) p').
Lemma minC : forall m n : nat, Min m n = Min n m.
Proof.
	intros m; induction m as [|m IHm]; intros [|n].
	1,2,3: by exact (eq_refl _).
	by minimize Min; rewrite (IHm _); exact (eq_refl _).
Qed.
Lemma lt_or_ge_iter : forall m n : nat, LessThan_iter m n \/ GreaterEqual_iter m n.
Proof.
	intros m n; generalize dependent m; induction n as [|n IHn];
	 [intros ? | intros [|m]].
	by right; exact (gei_o _).
	by left;  exact (lti_o _).
	specialize (IHn m) as [lt | ge].
	by left;  exact (lti_iter lt).
	by right; exact (gei_iter ge).
Qed.
Lemma lt_iterc_rev : forall m n, LessThan_iterc (S m) (S n) -> LessThan_iterc m n.
Proof.
	intros m n mltn.
	inversion mltn as [|m' n' H m'eqm n'eqn]; clear m' n' m'eqm n'eqn.
	by exact H.
Qed.
Lemma ge_iterc_rev : forall m n, GreaterEqual_iterc (S m) (S n) -> GreaterEqual_iterc m n.
Proof.
	intros m n mgen.
	inversion mgen as [|m' n' H m'eqm n'eqn]; clear m' n' m'eqm n'eqn.
	by exact H.
Qed.
Arguments lt_iterc_rev {m n} p.
Arguments ge_iterc_rev {m n} p.
Lemma lt_iter_rev : forall m n, LessThan_iter (S m) (S n) -> LessThan_iter m n.
Proof.
	intros m n [mltn _].
	by exact (ltc2lt_iter (lt_iterc_rev mltn)).
Qed.
Lemma ge_iter_rev : forall m n, GreaterEqual_iter (S m) (S n) -> GreaterEqual_iter m n.
Proof.
	intros m n [mgen _].
	by exact (gec2ge_iter (ge_iterc_rev mgen)).
Qed.
Arguments lt_iter_rev {m n} p.
Arguments ge_iter_rev {m n} p.
Lemma lt_is_not_ge_iter : forall m n, LessThan_iter m n -> ~ GreaterEqual_iter m n.
Proof.
	intros m; induction m as [|m IHm]; intros [|n] mltn mgen.
	1,3: by destruct mltn as [mltn _]; inversion mltn.
	     by destruct mgen as [mgen _]; inversion mgen.
	by exact (IHm _ (lt_iter_rev mltn) (ge_iter_rev mgen)).
Qed.
Lemma ge_is_not_lt_iter : forall m n, GreaterEqual_iter m n -> ~ LessThan_iter m n.
Proof.
	intros m; induction m as [|m IHm]; intros [|n] mgen mltn.
	1,3: by destruct mltn as [mltn _]; inversion mltn.
	     by destruct mgen as [mgen _]; inversion mgen.
	by exact (IHm _ (ge_iter_rev mgen) (lt_iter_rev mltn)).
Qed.

Lemma lt_is_min_iter : forall m n : nat, LessThan_iter m n -> Min m n = m.
Proof.
	intros m; induction m as [|m IHm].
	by intros; exact (eq_refl _).
	intros [|n] mltn.
	by is_false (ge_is_not_lt_iter _ _ (gei_o _) mltn).
	by exact (f_equal _ (IHm _ (lt_iter_rev mltn))).
Qed.
Lemma le_is_min_iter : forall m n : nat, LessThan_iter m (S n) -> Min m n = m.
Proof.
	intros m; induction m as [|m IHm].
	by intros; exact (eq_refl _).
	intros [|n] mltn; apply lt_iter_rev in mltn.
	by is_false (ge_is_not_lt_iter _ _ (gei_o _) mltn).
	by exact (f_equal _ (IHm _ mltn)).
Qed.

Lemma lt_iterc_next {m n : nat} : LessThan_iterc m n -> LessThan_iterc m (S n).
Proof.
	intros lti.
	induction lti as [n|m n mltn IHmltn].
	by exact (ltic_o _).
	by exact (ltic_iter IHmltn).
Qed.
Lemma ge_iterc_next {m n : nat} : GreaterEqual_iterc m n -> GreaterEqual_iterc (S m) n.
Proof.
	intros gei.
	induction gei as [n|m n mgen IHmgen].
	by exact (geic_o _).
	by exact (geic_iter IHmgen).
Qed.
Lemma lt_iter_next {m n : nat} : LessThan_iter m n -> LessThan_iter m (S n).
Proof.
	intros [mltn _].
	by exact (ltc2lt_iter (lt_iterc_next mltn)).
Qed.
Lemma ge_iter_next {m n : nat} : GreaterEqual_iter m n -> GreaterEqual_iter (S m) n.
Proof.
	intros [mgen _].
	by exact (gec2ge_iter (ge_iterc_next mgen)).
Qed.

Lemma lt_is_tg_iter : forall m n : nat, LessThan_iter m n -> GreaterEqual_iter n (S m).
Proof.
	intros m; induction m as [|m IHm]; intros [|n] mltn.
	1,3: by is_false (lt_is_not_ge_iter _ _ mltn (gei_o _)).
	by exact (gei_iter (gei_o _)).
	by exact (gei_iter (IHm _ (lt_iter_rev mltn))).
Qed.
Lemma ge_is_el_iter : forall m n : nat, GreaterEqual_iter m n -> LessThan_iter n (S m).
Proof.
	intros m; induction m as [|m IHm]; intros [|n] mgen.
	1,3: by exact (lti_o _).
	by is_false (ge_is_not_lt_iter _ _ mgen (lti_o _)).
	by exact (lti_iter (IHm _ (ge_iter_rev mgen))).
Qed.

Lemma n_lt_Sn : forall n : nat, LessThan_iter n (S n).
Proof.
	intros n; induction n as [|n IHn].
	by exact (lti_o _).
	by exact (lti_iter IHn).
Qed.
Lemma n_ge_n : forall n : nat, GreaterEqual_iter n n.
Proof.
	intros n; induction n as [|n IHn].
	by exact (gei_o _).
	by exact (gei_iter IHn).
Qed.

Lemma m_lt_Sn_ne_n : forall m n : nat, LessThan_iter m (S n) -> m <> n -> LessThan_iter m n.
Proof.
	intros m; induction m as [|m IHm]; intros [|n] mltSn mnen.
	by is_false (mnen (eq_refl _)).
	by exact (lti_o _).
	by is_false (ge_is_not_lt_iter _ _ (gei_iter (gei_o _)) mltSn).
	assert (mnen' : m <> n) by (intros meqn; exact (mnen (f_equal _ meqn))).
	by exact (lti_iter (IHm _ (lt_iter_rev mltSn) mnen')).
Qed.

Fixpoint add m n := match m with
	| O => n
	| S m' => S (add m' n) end.
Lemma add_m_Sn : forall m n : nat, add m (S n) = S (add m n).
Proof.
	intros m; induction m as [|m IHm]; intros n.
	by exact (eq_refl _).
	by minimize add; rewrite IHm; exact (eq_refl _).
Qed.
Lemma add_Sm_n : forall m n : nat, add (S m) n = S (add m n).
Proof.
	by intros; exact (eq_refl _).
Qed.
Lemma addC : forall m n : nat, add m n = add n m.
Proof.
	intros m; induction m as [|m IHm]; intros n.
	induction n as [|n IHn].
	by exact (eq_refl _).
	by rewrite (add_m_Sn _ _), IHn; exact (eq_refl _).
	by rewrite (add_m_Sn _ _), <-(IHm _); exact (eq_refl _).
Qed.
Lemma addA : forall m n p : nat, add (add m n) p = add m (add n p).
Proof.
	intros m; induction m as [|m IHm]; intros n p.
	by exact (eq_refl _).
	by minimize add; rewrite IHm; exact (eq_refl _).
Qed.

Lemma n_in_Sn : forall n : nat, (N n) inE (N (S n)).
Proof.
	intros n.
	by exact (e_in_succ _).
Qed.
Lemma natural_longest_string_n : forall n : nat,
	(forall g : nat -> Ensemble,
	 (forall m : nat, LessThan_iter m n -> (g m) inE (g (S m))) ->
	 (g n = N n) ->
	 (forall m : nat, LessThan_iter m (S n) -> g m = N m)) /\
	(forall f : nat -> Ensemble, (exists m : nat,
		(LessThan_iter m (S n) /\ (f m) not_in (f (S m)))) \/
		((f (S n)) not_in (N (S n)))).
Proof.
	intros n; induction n as [|n [IHnL IHnR]]; split.
	- intros g Hg gOeqO [|m] mltSO.
	  by exact gOeqO.
	  by is_false (ge_is_not_lt_iter _ _ (gei_o _) (lt_iter_rev mltSO)).
	- intros f.
	  specialize (classic (f (S O) = N O)) as [fSOeq | fSOne].
	  left; exists O; split.
	  by exact (lti_o _).
	  rewrite fSOeq; unfold N.
	  by exact (empty_is_empty _).
	  right; intros fSOinSO.
	  specialize (pair_union_is_union _ _ _ fSOinSO) as [fSOinO | fSOinsO].
	  by exact (empty_is_empty _ fSOinO).
	  specialize (singleton_is_singleton _ _ fSOinsO) as fSOinO.
	  by exact (fSOne fSOinO).
	- intros g Hg gSneqSn.
	  remember Hg as Hg' eqn:tmp; specialize (Hg' _ (n_lt_Sn n)) as gninSn; clear tmp Hg'.
	  rewrite gSneqSn in gninSn.
	  specialize (pair_union_is_union _ _ _ gninSn) as [gninn | gninsn].
	  + exfalso.
	    pose (h' := fix h' i j k n := match i with
	      | O => match j with | O => N n | _ => g k end
	      | S i' => match j with
	        | O => match i' with | O => g (S k) | _ => h' i' O (S k) n end
	        | S j' => h' i' j' (S k) n end
	    end).
	    assert (h'SmOisgSm : forall m n p, h' (S m) O n p = g (add (S m) n)).
	    { clear dependent n; intros m; induction m as [|m IHm]; intros n p.
	      by exact (eq_refl _).
	      minimize h' in IHm; minimize add in IHm.
	      minimize add; rewrite <-(add_m_Sn m n).
	      rewrite <-(IHm (S n) p).
	      by exact (eq_refl _). }
	    assert (neisg'eqg : forall m p q r, m <> p -> h' m p q r = g (add q m)).
	    { clear dependent n; intros m p.
	      generalize dependent m; induction p as [|p IHp]; intros m q r mneSp.
	      destruct m as [|m].
	      by is_false (mneSp (eq_refl _)).
	      by rewrite addC; exact (h'SmOisgSm m q r).
	      destruct m as [|m].
	      by rewrite addC; exact (eq_refl _).
	      assert (mnep : m <> p) by (intros meqp; exact (mneSp (f_equal S meqp))).
	      rewrite (add_m_Sn _ _), <-(add_Sm_n _ _).
	      by exact (IHp _ (S q) r mnep). }
	    assert (g'SneqNSn : forall n p q, h' n n p q = N q).
	    { clear; intros n; induction n as [|n IHn]; intros p q.
	      by exact (eq_refl _).
	      by exact (IHn _ _). }
	    specialize (let g' := fun m => h' m (S n) O n in IHnR g') as [[m [mltSn fmnifSm]] | fSnniSn].
	    * specialize (classic (m = n)) as [meqn | mnen].
	      -- rewrite meqn in fmnifSm; clear dependent m.
	         rewrite (g'SneqNSn _ _ _) in fmnifSm.
	         assert (nneSn : n <> S n).
	         { clear; intros neqSn; induction n as [|n IHn].
	           by discriminate neqSn.
	           by injection neqSn as neqSn'; exact (IHn neqSn'). }
	         rewrite (neisg'eqg _ _ _ _ nneSn) in fmnifSm.
	         by exact (fmnifSm gninn).
	      -- assert (mneSn : m <> S n) by (
	           intros meqSn; rewrite meqSn in mltSn;
	           exact (ge_is_not_lt_iter _ _ (n_ge_n _) mltSn)).
	         assert (SmneSn : S m <> S n) by (
	           intros SmeqSn; injection SmeqSn as meqn; exact (mnen meqn)).
	         rewrite (neisg'eqg _ _ _ _ SmneSn) in fmnifSm.
	         rewrite (neisg'eqg _ _ _ _ mneSn) in fmnifSm.
	         by exact (fmnifSm (Hg _ mltSn)).
	    * rewrite (g'SneqNSn _ _ _) in fSnniSn.
	      by exact (fSnniSn (n_in_Sn _)).
	  
	  + specialize (singleton_is_singleton _ _ gninsn) as gneqn; clear gninsn.
	    intros m mltSSn.
	    specialize (classic (m = S n)) as [meqSn | mneSn].
	    by rewrite meqSn; exact gSneqSn.
	    specialize (m_lt_Sn_ne_n _ _ mltSSn mneSn) as mltSn; clear mltSSn mneSn.
	    refine (IHnL _ _ gneqn _ mltSn).
	    clear m mltSn; intros m mltn.
	    by exact (Hg _ (lt_iter_next mltn)).
	- intros f.
	  specialize (classic (f (S (S n)) inE N (S (S n)))) as [fSSninSSn | fSSnniSSn]; swap 1 2.
	  by right; exact fSSnniSSn.
	  left.
	  specialize (classic (exists m : nat, LessThan_iter m (S n) /\ f m not_in f (S m))) as [[m [mltSn fmnifSm]] | nex].
	  + exists m; split.
	    by exact (lt_iter_next mltSn).
	    by exact fmnifSm.
	  + exists (S n); split.
	    by exact (n_lt_Sn _).
	    remember IHnR as IHnR' eqn:tmp; clear tmp; specialize (IHnR' f) as [mex | fSnniSn].
	    by is_false (nex mex).
	    specialize (not_ex_all_not _ _ nex) as hypf; lazy beta in hypf; clear nex.
	    specialize (IHnR (fun m => f (S m))) as [[m [mltSn fSmnifSSm]] | fSSnniSn].
	    specialize (classic (m = n)) as [meqn | mnen].
	    by rewrite <-meqn; exact fSmnifSSm.
	    specialize (lti_iter (m_lt_Sn_ne_n _ _ mltSn mnen)) as SmltSn.
	    specialize (not_and_or _ _ (hypf (S m))) as [l | r].
	    by is_false (l SmltSn).
	    by is_false (r fSmnifSSm).
	    specialize (pair_union_is_union _ _ _ fSSninSSn) as [fSSninSn | fSSninsSn].
	    by is_false (fSSnniSn fSSninSn).
	    specialize (singleton_is_singleton _ _ fSSninsSn) as fSSneqSn.
	    by rewrite fSSneqSn; exact fSnniSn.
Qed.

Fixpoint parity {A : Type} (n : nat) (even odd : A) := match n with
	| O => even | S O => odd
	| S (S n') => parity n' even odd end.
(* Or:
Fixpoint parity {A : Type} (n : nat) (even odd : A) := match n with
	| O => even
	| S n' => parity n' odd even end.
*)
Lemma parity_even_or_odd {A : Type} : forall n : nat, forall even odd : A,
  (parity n even odd = even) \/ (parity n even odd = odd).
Proof.
	intros n even odd; generalize dependent n.
	apply double_induction.
	left. 2: right.
	1,2: by exact (eq_refl _).
	intros n IHn _.
	by exact IHn.
Qed.
Lemma parity_even_then_odd {A : Type} : forall n : nat, forall even odd : A,
  (parity n even odd = even) -> (parity (S n) even odd = odd).
Proof.
	intros n even odd; generalize dependent n.
	apply (double_induction (fun n => (parity n even odd = even) -> (parity (S n) even odd = odd))).
	by intros _; exact (eq_refl _).
	intros oddeqeven; unfold parity in oddeqeven; rewrite oddeqeven.
	by exact (eq_refl _).
	by intros ? IHn _; exact IHn.
Qed.
Lemma parity_odd_then_even {A : Type} : forall n : nat, forall even odd : A,
  (parity n even odd = odd) -> (parity (S n) even odd = even).
Proof.
	intros n even odd; generalize dependent n.
	apply (double_induction (fun n => (parity n even odd = odd) -> (parity (S n) even odd = even))).
	intros eveneqodd; unfold parity in eveneqodd; rewrite eveneqodd.
	by exact (eq_refl _).
	by intros _; exact (eq_refl _).
	by intros ? IHn _; exact IHn.
Qed.
Lemma parity_even_then_odd2 {A B : Type} : forall n : nat, forall even odd : A,
  even <> odd -> forall even2 odd2 : B,
   (parity n even odd = even) -> (parity (S n) even2 odd2 = odd2).
Proof.
	intros n even odd evenneodd even2 odd2; generalize dependent n.
	apply (double_induction (fun n => (parity n even odd = even) -> (parity (S n) even2 odd2 = odd2))).
	by intros _; exact (eq_refl _).
	intros oddeqeven; unfold parity in oddeqeven; symmetry in oddeqeven.
	by is_false (evenneodd oddeqeven).
	by intros ? IHn _; exact IHn.
Qed.
Lemma parity_odd_then_even2 {A B : Type} : forall n : nat, forall even odd : A,
  even <> odd -> forall even2 odd2 : B,
   (parity n even odd = odd) -> (parity (S n) even2 odd2 = even2).
Proof.
	intros n even odd evenneodd even2 odd2; generalize dependent n.
	apply (double_induction (fun n => (parity n even odd = odd) -> (parity (S n) even2 odd2 = even2))).
	intros eveneqodd; unfold parity in eveneqodd.
	by is_false (evenneodd eveneqodd).
	by intros _; exact (eq_refl _).
	by intros ? IHn _; exact IHn.
Qed.

Lemma succ_inj : forall m n : nat, Succ (N m) = Succ (N n) -> N m = N n.
Proof.
	intros m n SmeqSn.
	specialize (n_in_Sn m) as minSn; minimize N in minSn; rewrite SmeqSn in minSn.
	specialize (pair_union_is_union _ _ _ minSn) as [minn | minsn].
	specialize (n_in_Sn n) as ninSm; minimize N in ninSm; rewrite <-SmeqSn in ninSm.
	specialize (pair_union_is_union _ _ _ ninSm) as [ninm | ninsm].
	exfalso; clear ninSm minSn SmeqSn.
	pose (f := fun k => match parity m leftopt rightopt with
	  | leftopt  => parity k (N m) (N n)
	  | rightopt => parity k (N n) (N m) end).
	assert (lner : leftopt <> rightopt) by discriminate.
	specialize (parity_even_or_odd m leftopt rightopt) as [meven | modd];
	specialize (proj2 (natural_longest_string_n m) f) as [[k [kltSm fknifSk]] | fmniSm].
	unfold f in fknifSk; rewrite meven in fknifSk; clear f.
	specialize (parity_even_or_odd k (N m) (N n)) as [pkeqm | pkeqn].
	rewrite pkeqm in fknifSk.
	rewrite (parity_even_then_odd _ _ _ pkeqm) in fknifSk.
	by exact (fknifSk minn).
	rewrite pkeqn in fknifSk.
	rewrite (parity_odd_then_even _ _ _ pkeqn) in fknifSk.
	by exact (fknifSk ninm).
	unfold f in fmniSm; rewrite meven in fmniSm; clear f.
	rewrite (parity_even_then_odd2 _ _ _ lner (N m) (N n) meven) in fmniSm.
	by exact (fmniSm (e_incl_succ _ _ ninm)).
	
	unfold f in fknifSk; rewrite modd in fknifSk; clear f.
	specialize (parity_even_or_odd k (N n) (N m)) as [pkeqn | pkeqm].
	rewrite pkeqn in fknifSk.
	rewrite (parity_even_then_odd _ _ _ pkeqn) in fknifSk.
	by exact (fknifSk ninm).
	rewrite pkeqm in fknifSk.
	rewrite (parity_odd_then_even _ _ _ pkeqm) in fknifSk.
	by exact (fknifSk minn).
	unfold f in fmniSm; rewrite modd in fmniSm; clear f.
	rewrite (parity_odd_then_even2 _ _ _ lner (N n) (N m) modd) in fmniSm.
	by exact (fmniSm (e_incl_succ _ _ ninm)).
	
	by symmetry; apply singleton_is_singleton in ninsm; exact ninsm.
	by           apply singleton_is_singleton in minsn; exact minsn.
Qed.
Arguments succ_inj {m n} SNmeqSNn.

Lemma N_inj : forall m n : nat, N m = N n -> m = n.
Proof.
	intros m; induction m as [|m IHm].
	- intros [|n] NOeqNn.
	  + by exact (eq_refl _).
	  + exfalso.
	    specialize (n_in_Sn n) as ninSn.
	    rewrite <-NOeqNn in ninSn.
	    by exact (empty_is_empty _ ninSn).
	- intros [|n] NmeqNn.
	  + exfalso.
	    specialize (n_in_Sn m) as minSm.
	    rewrite NmeqNn in minSm.
	    by exact (empty_is_empty _ minSm).
	  + by exact (f_equal _ (IHm _ (succ_inj NmeqNn))).
Qed.
Arguments N_inj {m n} NmeqNn.

Lemma add_normal_l : forall n a b : nat, add n a = add n b -> a = b.
Proof.
	(* Allowed because Succ is injective (see Nadd_normal_l) *)
	intros n; induction n as [|n IHn]; intros a b npaeqnpb.
	by exact npaeqnpb.
	minimize add in npaeqnpb; injection npaeqnpb as npaeqnpb.
	by exact (IHn _ _ npaeqnpb).
Qed.
Lemma add_normal_r : forall n a b : nat, add a n = add b n -> a = b.
Proof.
	by intros n a b apneqbpn; rewrite (addC a _), (addC b _) in apneqbpn;
	  exact (add_normal_l _ _ _ apneqbpn).
Qed.
Lemma add_normal_lr : forall n a b : nat, add n a = add b n -> a = b.
Proof.
	by intros n a b apneqbpn; rewrite (addC b _) in apneqbpn;
	  exact (add_normal_l _ _ _ apneqbpn).
Qed.
Lemma add_normal_rl : forall n a b : nat, add a n = add n b -> a = b.
Proof.
	by intros n a b apneqbpn; rewrite (addC a _) in apneqbpn;
	  exact (add_normal_l _ _ _ apneqbpn).
Qed.
Lemma Nadd_normal_l : forall n a b : nat, N (add n a) = N (add n b) -> N a = N b.
Proof.
	intros n; induction n as [|n IHn]; intros a b npaeqnpb.
	by exact npaeqnpb.
	by exact (IHn _ _ (succ_inj npaeqnpb)).
Qed.
Lemma Nadd_normal_r : forall n a b : nat, N (add a n) = N (add b n) -> N a = N b.
Proof.
	by intros n a b apneqbpn; rewrite (addC a _), (addC b _) in apneqbpn;
	  exact (Nadd_normal_l _ _ _ apneqbpn).
Qed.
Lemma Nadd_normal_lr : forall n a b : nat, N (add n a) = N (add b n) -> N a = N b.
Proof.
	by intros n a b apneqbpn; rewrite (addC b _) in apneqbpn;
	  exact (Nadd_normal_l _ _ _ apneqbpn).
Qed.
Lemma Nadd_normal_rl : forall n a b : nat, N (add a n) = N (add n b) -> N a = N b.
Proof.
	by intros n a b apneqbpn; rewrite (addC a _) in apneqbpn;
	  exact (Nadd_normal_l _ _ _ apneqbpn).
Qed.
Arguments add_normal_l {n a b} equality.
Arguments add_normal_r {n a b} equality.
Arguments add_normal_lr {n a b} equality.
Arguments add_normal_rl {n a b} equality.
Arguments Nadd_normal_l {n a b} equality.
Arguments Nadd_normal_r {n a b} equality.
Arguments Nadd_normal_lr {n a b} equality.
Arguments Nadd_normal_rl {n a b} equality.

Definition LessEqual_exist (m n : nat) := exists p : nat, add p m = n.
Lemma lee_O_n : forall n : nat, LessEqual_exist O n.
Proof.
	by intros n; exists n; rewrite addC; exact (eq_refl _).
Qed.
Lemma le_ex_refl : forall n : nat, LessEqual_exist n n.
Proof.
	by intros ?; exists O; exact (eq_refl _).
Qed.
Lemma le_ex_trans : forall m n p : nat, LessEqual_exist m n -> LessEqual_exist n p -> LessEqual_exist m p.
Proof.
	intros m n p [mn mlen] [np nlep].
	exists (add np mn).
	by rewrite addA, mlen; exact nlep.
Qed.
Lemma le_ex_sym : forall m n : nat, LessEqual_exist m n -> LessEqual_exist n m -> m = n.
Proof.
	intros m n [mn mlen] [nm nlem].
	destruct mn as [|mn].
	by exact mlen.
	exfalso; rewrite <-mlen, <-addA, add_m_Sn in nlem; clear n mlen; symmetry in nlem.
	generalize dependent (add nm mn); clear mn nm; intros n npmeqm.
	induction m as [|m IHm].
	by discriminate npmeqm.
	by rewrite add_m_Sn in npmeqm; injection npmeqm as npmeqm; exact (IHm npmeqm).
	(* assert (mltSnpm : forall n : nat, LessThan_iter m (add (S n) m)).
	{ intros n; induction n as [|n IHn].
	  by exact (n_lt_Sn _).
	  by specialize (lt_iter_next IHn) as tmp; rewrite <-add_Sm_n in tmp; exact tmp. }
	assert (mgeSnpm : GreaterEqual_iter m (add (S n) m)) by
	 (rewrite <-npmeqm; exact (n_ge_n _)).
	by exact (ge_is_not_lt_iter _ _ mgeSnpm (mltSnpm _)). *)
Qed.

Lemma le_compat_plus : forall m n p : nat, LessEqual_exist (add m p) (add n p) -> LessEqual_exist m n.
Proof.
	intros m n p [mpnp mplenp].
	exists mpnp.
	rewrite <-addA in mplenp.
	by exact (add_normal_r mplenp).
Qed.

Lemma le_Sm_Sn_m_n : forall m n : nat, LessEqual_exist (S m) (S n) -> LessEqual_exist m n.
Proof.
	intros m n [mn mlen].
	exists mn.
	rewrite add_m_Sn in mlen; injection mlen as mlen.
	by exact mlen.
Qed.
Lemma lee_iter : forall m n : nat, LessEqual_exist m n -> LessEqual_exist (S m) (S n).
Proof.
	intros m n [mn mlen].
	exists mn.
	rewrite add_m_Sn.
	by exact (f_equal S mlen).
Qed.

Lemma lee_total : forall m n : nat, LessEqual_exist m n \/ LessEqual_exist n m.
Proof.
	intros m; induction m as [|m IHm].
	by intros n; left; exists n; rewrite addC; exact (eq_refl _).
	intros [|n].
	by right; exact (lee_O_n _).
	specialize (IHm n) as [mlen | nlem].
	by left;  exact (lee_iter _ _ mlen).
	by right; exact (lee_iter _ _ nlem).
Qed.

Example sum_less_individual_more : forall a b c d : nat,
 LessEqual_exist (add a b) (add c d) -> LessEqual_exist c a -> LessEqual_exist b d.
Proof.
	intros a b c d [abcd ablecd] [ca clea].
	exists (add abcd ca).
	rewrite <-clea in ablecd; clear clea.
	rewrite (addC ca _), (addA c _ _), (addC c _), <-(addA _ _ c) in ablecd.
	apply add_normal_rl in ablecd.
	rewrite <-addA in ablecd.
	by exact ablecd.
Qed.

Lemma lti_is_in : forall m n : nat, LessThan_iter m n -> N m inE N n.
Proof.
	intros m; induction m as [|m IHm].
	intros [|n] OltSn.
	by is_false (ge_is_not_lt_iter _ _ (gei_o _) OltSn).
	clear OltSn; induction n as [|n IHn].
	by exact (n_in_Sn _).
	by exact (e_incl_succ _ _ IHn).
	intros [|n] SmltSn.
	by is_false (ge_is_not_lt_iter _ _ (gei_o _) SmltSn).
	specialize (IHm _ (lt_iter_rev SmltSn)) as NminNn; clear IHm SmltSn.
	generalize dependent m; induction n as [|n IHn].
	by intros m NminNO; is_false (empty_is_empty _ NminNO).
	intros m NminNSn.
	specialize (pair_union_is_union _ _ _ NminNSn) as [NminNn | NminsNSn].
	by exact (e_incl_succ _ _ (IHn _ NminNn)).
	apply singleton_is_singleton in NminsNSn; fold N in NminsNSn.
	by rewrite (f_equal S (N_inj NminsNSn)); exact (n_in_Sn _).
Qed.
Lemma in_is_lti : forall m n : nat, N m inE N n -> LessThan_iter m n.
Proof.
	intros m n; generalize dependent m; induction n as [|n IHn].
	intros ? minO.
	by is_false (empty_is_empty _ minO).
	intros m minSn.
	specialize (pair_union_is_union _ _ _ minSn) as [minn | minsn].
	by exact (lt_iter_next (IHn _ minn)).
	by apply singleton_is_singleton, N_inj in minsn; rewrite minsn; exact (n_lt_Sn _).
Qed.
Arguments lti_is_in {m n} mltn.
Arguments in_is_lti {m n} minn.

Lemma lee_is_incl : forall m n : nat, LessEqual_exist m n -> (N m) incl (N n).
Proof.
	intros m n [mn mlen].
	rewrite <-mlen; clear n mlen; induction mn as [|mn IHmn].
	by unfold add; exact (incl_refl _).
	intros x xinm.
	specialize (IHmn _ xinm) as xinmnpm.
	by exact (e_incl_succ _ _ xinmnpm).
Qed.
Lemma incl_is_lee : forall m n : nat, (N m) incl (N n) -> LessEqual_exist m n.
Proof.
	intros m n mincln; generalize dependent m; induction n as [|n IHn]; intros m mincln.
	- specialize (classic (N m = N O)) as [meqO | mneO].
	  by rewrite (N_inj meqO); exact (le_ex_refl _).
	  specialize (non_empty_is_not_empty _ mneO) as [x xinm].
	  specialize (mincln _ xinm) as xine.
	  by is_false (empty_is_empty _ xine).
	- destruct m as [|m].
	  by exact (lee_O_n _).
	  refine (lee_iter _ _ (IHn m _)).
	  clear IHn; intros x xinm.
	  specialize (mincln _ (e_incl_succ _ _ xinm)) as xinSn.
	  specialize (pair_union_is_union _ _ _ xinSn) as [xinn | xinsn]; clear xinSn.
	  by exact xinn.
	  apply singleton_is_singleton in xinsn; fold N in xinsn.
	  exfalso; rewrite xinsn in xinm; clear x xinsn.
	  specialize (mincln _ (lti_is_in (lti_iter (in_is_lti xinm)))) as SninSn; clear xinm mincln.
	  specialize (proj2 (natural_longest_string_n n) (fun _ => N (S n)))
	    as [[_ [_ NSnniNSn]] | NSnniNSn]; by exact (NSnniNSn SninSn).
Qed.
Arguments lee_is_incl {m n} mlen.
Arguments incl_is_lee {m n} mincln.

Lemma le_is_in_eq : forall m n : nat, LessEqual_exist m n -> (N m inE N n) \/ (m = n).
Proof.
	intros m n [mn mlen]; generalize dependent mlen; generalize dependent n;
	  generalize dependent m; induction mn as [|mn IHmn].
	by intros ? ? mlen; right; exact mlen.
	intros m [|n] mlen.
	by minimize add in mlen; discriminate mlen.
	injection mlen as mlen; specialize (IHmn _ _ mlen) as [minn | meqn]; left.
	by exact (e_incl_succ _ _ minn).
	by rewrite meqn; exact (n_in_Sn _).
Qed.
Lemma lti_is_lee : forall m n : nat, LessThan_iter m n -> LessEqual_exist m n.
Proof.
	intros m n; generalize dependent m; induction n as [|n IHn]; intros [|m] mltSSn.
	1,3: by exact (lee_O_n _).
	by is_false (ge_is_not_lt_iter _ _ (gei_o _) mltSSn).
	by exact (lee_iter _ _ (IHn _ (lt_iter_rev mltSSn))).
Qed.

Example all_nonempty_N_is_minored : forall a : Ensemble,
  a incl Nnat -> a <> EmptySet -> exists n : nat, (N n inE a)
    /\ (forall y : Ensemble, y inE a -> N n incl y).
Proof.
	intros a ainclN anee.
	assert (strong_induction : forall n : nat,
	  (exists k : nat, LessEqual_exist k n /\ N k inE a) ->
	   (exists k : nat, N k inE a /\ (forall y : _, y inE a -> N k incl y))).
	{ intros n; induction n as [|n IHn].
	  - intros [[|k] [[kO kleO] kina]].
	    + clear kO kleO; exists O; split.
	      by exact kina.
	      intros y yina.
	      specialize (ainclN _ yina) as [z yinNbyz]; rewrite (Eeq_is_eq yinNbyz); clear.
	      by exact (lee_is_incl (lee_O_n _)).
	    + by rewrite add_m_Sn in kleO; discriminate kleO.
	  - intros [k [[kn klen] kina]].
	    specialize (classic (exists k, LessEqual_exist k n /\ N k inE a)) as [exkina | nexkina].
	    by exact (IHn exkina).
	    destruct kn as [|kn].
	    exists (S n); split; clear IHn anee.
	    by unfold add in klen; rewrite klen in kina; exact kina.
	    intros y yina.
	    specialize (ainclN _ yina) as [m yeqm];
	      apply Eeq_is_eq in yeqm; rewrite yeqm; rewrite yeqm in yina; clear y yeqm.
	    specialize (not_and_or _ _
	      (not_ex_all_not _ (fun k => LessEqual_exist k n /\ N k inE a) nexkina m))
	      as [mgtn | mnia].
	    assert (Snlem : LessEqual_exist (S n) m).
	    { specialize (lee_total n m) as [[[|nm] nlem] | mlen].
	      by unfold add in nlem; rewrite nlem in mgtn; is_false (mgtn (le_ex_refl _)).
	      by exists nm; rewrite add_m_Sn; exact nlem.
	      by is_false (mgtn mlen). }
	    by exact (lee_is_incl Snlem).
	    by is_false (mnia yina).
	    
	    exfalso; rewrite add_Sm_n in klen; injection klen as klen.
	    specialize (not_and_or _ _
	      (not_ex_all_not _ (fun k => LessEqual_exist k n /\ N k inE a) nexkina k))
	      as [kgtn | knia].
	    by exact (kgtn (ex_intro _ _ klen)).
	    by exact (knia kina). }
	specialize (non_empty_is_not_empty _ anee) as [x xina].
	destruct (ainclN _ xina) as [n xinNbyn]; rewrite (Eeq_is_eq xinNbyn) in xina; clear x xinNbyn.
	by exact (strong_induction _ (ex_intro _ _ (conj (le_ex_refl _) xina))).
Qed.
Example all_nonempty_majored_maximum : forall a : Ensemble,
  a incl Nnat -> a <> EmptySet -> (exists n : nat, (forall k : _, k inE a -> k incl N n))
    -> exists n : nat, (N n inE a) /\ (forall y : Ensemble, y inE a -> y incl N n).
Proof.
	intros a ainclN anee [M amajbyM].
	induction M as [|M IHM].
	exists O; split.
	specialize (non_empty_is_not_empty _ anee) as [x xina].
	destruct (ainclN _ xina) as [n xinNbyn]; rewrite (Eeq_is_eq xinNbyn) in xina; clear x xinNbyn.
	specialize (amajbyM _ xina).
	specialize (classic (N n = N O)) as [neqO | nneO].
	by rewrite neqO in xina; exact xina.
	specialize (non_empty_is_not_empty _ nneO) as [x xinn].
	by is_false (empty_is_empty _ (amajbyM _ xinn)).
	by exact amajbyM.
	
	specialize (classic (N (S M) inE a)) as [SMina | SMnia].
	exists (S M); split.
	by exact SMina.
	intros y yina.
	destruct (ainclN _ yina) as [n yinNbyn]; apply Eeq_is_eq in yinNbyn; rewrite yinNbyn; rewrite yinNbyn in yina; clear y yinNbyn.
	by exact (amajbyM _ yina).
	apply IHM.
	intros k kina.
	destruct (ainclN _ kina) as [n kinNbyn]; apply Eeq_is_eq in kinNbyn; rewrite kinNbyn; rewrite kinNbyn in kina; clear k kinNbyn.
	specialize (incl_is_lee (amajbyM _ kina)) as [[|nSM] nleSM].
	unfold add in nleSM; rewrite nleSM in kina.
	by is_false (SMnia kina).
	injection nleSM as nleM.
	by exact (lee_is_incl (ex_intro _ _ nleM)).
Qed.
Example N_not_maximized : forall n : nat, exists k : nat, N k not_incl N n.
Proof.
	intros n; exists (S n); apply not_incl_notincl; intros Snincln.
	apply incl_is_lee in Snincln.
	assert (nleSn : LessEqual_exist n (S n)) by (exists (S O); exact (eq_refl _)).
	specialize (le_ex_sym _ _ Snincln nleSn) as Sneqn.
	clear Snincln nleSn; induction n as [|n IHn]. (* Sigh... *)
	by discriminate Sneqn.
	by injection Sneqn as Sneqn; exact (IHn Sneqn).
Qed.

Fixpoint mul (m n : nat) := match m with | O => O | S m' => add (mul m' n) n end.
Lemma mulC : forall m n : nat, mul m n = mul n m.
Proof.
	intros m; induction m as [|m IHm]; intros n; induction n as [|n IHn].
	by exact (eq_refl _).
	by minimize mul; rewrite <-IHn; exact (eq_refl _).
	by minimize mul; rewrite   IHm; exact (eq_refl _).
	by minimize mul; rewrite <-IHn, IHm; minimize mul;
	  rewrite IHm, (addA _ m _), (addA _ n _), (addC m (S n)), add_Sm_n, <-add_m_Sn;
	  exact (eq_refl _).
Qed.
Lemma mul_Sm_n : forall m n : nat, mul (S m) n = add (mul m n) n.
Proof. by intros; exact (eq_refl _). Qed.
Lemma mul_m_Sn : forall m n : nat, mul m (S n) = add (mul m n) m.
Proof.
	by intros; rewrite (mulC _ (S _)), mul_Sm_n;
	  exact (f_equal (fun k => add k _) (mulC _ _)).
Qed.
Lemma mul_add_distr_l : forall m n p : nat, mul (add m n) p = add (mul m p) (mul n p).
Proof.
	intros m; induction m as [|m IHm]; intros n p.
	by exact (eq_refl _).
	rewrite add_Sm_n, mul_Sm_n, mul_Sm_n, IHm, (addA _ _ p), (addC (mul n _) p), <-addA.
	by exact (eq_refl _).
Qed.
Lemma mulA : forall m n p : nat, mul (mul m n) p = mul m (mul n p).
Proof.
	intros m; induction m as [|m IHm]; intros n p.
	by exact (eq_refl _).
	by rewrite mul_Sm_n, mul_add_distr_l, IHm; exact (eq_refl _).
Qed.
Corollary mul_O_n : forall n : nat, mul O n = O.
Proof. by intros; exact (eq_refl _). Qed.
Corollary mul_n_O : forall n : nat, mul n O = O.
Proof. by intros; rewrite mulC; exact (eq_refl _). Qed.
Corollary mul_SO_n : forall n : nat, mul (S O) n = n.
Proof. by intros; exact (eq_refl _). Qed.
Corollary mul_n_SO : forall n : nat, mul n (S O) = n.
Proof. by intros; rewrite mulC; exact (eq_refl _). Qed.

Lemma add_eq_O_l : forall m n : nat, add m n = O -> m = O.
Proof.
	intros m; induction m as [|m IHm]; intros n cond.
	by exact (eq_refl _).
	by discriminate cond.
Qed.
Lemma add_eq_O_r : forall m n : nat, add m n = O -> n = O.
Proof.
	by intros m n cond; rewrite addC in cond; exact (add_eq_O_l _ _ cond).
Qed.

Lemma le_is_le_mul : forall m n p : nat, LessEqual_exist m n -> LessEqual_exist (mul m p) (mul n p).
Proof.
	intros m n p [mn mlen]; exists (mul mn p).
	by rewrite <-mlen, mul_add_distr_l; exact (eq_refl _).
Qed.
Lemma le_mul_is_le_l : forall n a b : nat, n <> O -> LessEqual_exist (mul n a) (mul n b) -> LessEqual_exist a b.
Proof.
	intros [|n] a b nneO nalenb.
	by is_false (nneO (eq_refl _)).
	clear nneO; generalize dependent nalenb; generalize dependent b;
	  generalize dependent a; induction n as [|n IHn]; intros a b nalenb.
	by exact nalenb.
	specialize (lee_total a b) as [aleb | blea].
	by exact aleb.
	rewrite (mul_Sm_n (S n) _), (mul_Sm_n (S n) _), (addC _ a), (addC _ b) in nalenb.
	by exact (IHn _ _ (sum_less_individual_more _ _ _ _ nalenb blea)).
Qed.
Lemma le_mul_is_le_r : forall n a b : nat, n <> O -> LessEqual_exist (mul a n) (mul b n) -> LessEqual_exist a b.
Proof.
	intros n a b nneO nalenb; rewrite (mulC _ n), (mulC _ n) in nalenb.
	generalize dependent nalenb; generalize dependent nneO;
	  generalize dependent b; generalize dependent a; generalize dependent n.
	by exact le_mul_is_le_l.
Qed.
Corollary eq_mul_is_eq_l : forall n a b : nat, n <> O -> (mul n a) = (mul n b) -> a = b.
Proof.
	intros n a b nneO naeqnb; apply le_ex_sym.
	specialize (le_ex_refl (mul n b)) as tmp; rewrite <-naeqnb in tmp at 1; clear naeqnb.
	generalize dependent tmp; generalize dependent nneO; generalize dependent b;
	  generalize dependent a; generalize dependent n; exact le_mul_is_le_l.
	specialize (le_ex_refl (mul n a)) as tmp; rewrite naeqnb in tmp at 1; clear naeqnb.
	generalize dependent tmp; generalize dependent nneO; generalize dependent a;
	  generalize dependent b; generalize dependent n; exact le_mul_is_le_l.
Qed.
Corollary eq_mul_is_eq_r : forall n a b : nat, n <> O -> (mul a n) = (mul b n) -> a = b.
Proof.
	by intros n a b nneO aneqbn; rewrite (mulC _ n), (mulC _ n) in aneqbn;
	  exact (eq_mul_is_eq_l n _ _ nneO aneqbn).
Qed.
