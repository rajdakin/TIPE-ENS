Ltac done := try solve [simple apply eq_refl | contradiction | assumption]; fail "Goal not solved".
Tactic Notation "by" tactic(t) := t; fail "Goal not solved".
Tactic Notation "by'" tactic(t) := t; done.

Ltac develop fs := lazy beta delta [fs].
Tactic Notation "remove" reference(refs) := lazy beta delta [refs].
Tactic Notation "remove" reference(refs) "in" hyp(h) := lazy beta delta [refs] in h.

Tactic Notation "minimize" constr(f) := unfold f; fold f.
Tactic Notation "minimize" constr(f) "in" hyp(h) := unfold f in h; fold f in h.

Ltac compare_unfold' h fs := unfold fs; unfold fs in h.
Tactic Notation "compare_unfold" "to" hyp(h) "through" smart_global(refs) := unfold refs; unfold refs in h.

Ltac compare_minimize' h fs := minimize fs; minimize fs in h.
Tactic Notation "compare_minimize" "to" hyp(h) "through" smart_global(refs) := minimize refs; minimize refs in h.

Ltac is_false h := exfalso; exact h.

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
Corollary ens_pi_is_orig : forall a : Ensemble, a = ens (pi1e a) (pi2e a).
Proof. by intros [A f]; exact (eq_refl _). Qed.
Fixpoint Ensemble_eq (a b : Ensemble) : Prop := let (a', f) := a in let (b', g) := b in
	   (forall x : a', exists y : b', Ensemble_eq (f x) (g y))
	/\ (forall y : b', exists x : a', Ensemble_eq (f x) (g y)).

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

Infix "=E" := Ensemble_eq (at level 70, no associativity).
Notation "a '<>E' b" := (~ (a =E b)) (at level 70, no associativity).
Definition In (a B : Ensemble) := let (B', f) := B in exists b : B', a =E (f b).
Infix "inE" := In (at level 70, no associativity).
Corollary application_in : forall A : _, forall f : _, forall x : A, f x inE (ens A f).
Proof. by intros A f x; exists x; exact (Eeq_refl _). Qed.
Notation "a 'not_in' b" := (~ (a inE b)) (at level 70, no associativity).
Definition Included (A B : Ensemble) : Prop :=
	forall e : Ensemble, (e inE A) -> (e inE B).
Infix "incl" := Included (at level 70, no associativity).
Definition NotIncluded (A B : Ensemble) : Prop :=
	exists e : Ensemble, (e inE A) /\ ~(e inE B).
Infix "not_incl" := NotIncluded (at level 70, no associativity).

(* Strangely enough, this axiom is provable...
 * (This should be due to how induction works on sets I guess) *)
Lemma extensionality_axiom
	: forall A B : Ensemble, (forall x : _, ((x inE A) <-> (x inE B))) -> (A =E B).
Proof.
	intros [A f] [B g] H; split.
	by intros x; exact (proj1 (iff_and (H (f x))) (application_in _ _ _)).
	intros y;
	  specialize (proj2 (iff_and (H (g y))) (application_in _ _ _)) as [x yinAbyx].
	by exists x; exact (Eeq_sym _ _ yinAbyx).
Qed.
Axiom extensionality_axiom'
	: forall A B : Ensemble, (A =E B) -> forall P : Ensemble -> Prop, (P A) -> (P B).
Corollary Eextensionality_axiom : forall A B, A =E B -> A = B.
Proof. intros A B AeeqB; exact (extensionality_axiom' _ _ AeeqB (fun X => A = X) (eq_refl _)). Qed.
Axiom pairing_axiom
	: forall A B : Ensemble, exists C : Ensemble, forall x : Ensemble,
	(x inE C) <-> ((x =E A) \/ (x =E B)).
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
Arguments extensionality_axiom' {A B} AeqB P PA.
Arguments Eextensionality_axiom {A B} AeqB.

Lemma eq_is_Eeq : forall a b : Ensemble, (a = b) -> (a =E b).
Proof. by intros a ? H; rewrite <-H; exact (Eeq_refl a). Qed.
Lemma Eeq_in_trans_l : forall a b c : Ensemble, (a =E b) -> (a inE c) -> b inE c.
Proof.
	intros [a f] [b g] [c h] [ainclb bincla] [x aincbyx].
	exists x; rewrite (ens_pi_is_orig (h x));
	  rewrite (ens_pi_is_orig (h x)) in aincbyx;
	  destruct aincbyx as [ainclhx hxincla];
	  split.
	intros y.
	specialize (bincla y) as [z Hz];
	  specialize (ainclhx z) as [k Hk].
	by exists k; exact (Eeq_trans _ _ _ (Eeq_sym _ _ Hz) Hk).
	intros y.
	specialize (hxincla y) as [z Hz];
	  specialize (ainclb z) as [k Hk].
	by exists k; exact (Eeq_trans _ _ _ (Eeq_sym _ _ Hk) Hz).
Qed.
Lemma Eeq_in_trans_r : forall a b c : Ensemble, (a =E b) -> (b inE c) -> a inE c.
Proof.
	by intros a b c aeqb binc; apply Eeq_sym in aeqb;
	  exact (Eeq_in_trans_l _ _ _ aeqb binc).
Qed.
Lemma Eeq_incl_trans_l : forall a b c : Ensemble, (a =E b) -> (a incl c) -> b incl c.
Proof.
	intros [a f] [b g] [c h] [_ bincla] ainclc x [y xinbbyy].
	specialize (bincla y) as [z Hz];
	  specialize (ainclc _ (application_in _ _ z)) as [k Hk];
	  exists k.
	by exact (Eeq_trans _ _ _ xinbbyy (Eeq_trans _ _ _ (Eeq_sym _ _ Hz) Hk)).
Qed.
Lemma Eeq_incl_trans_r : forall a b c : Ensemble, (a =E b) -> (b incl c) -> a incl c.
Proof.
	by intros a b c aeqb binclc; apply Eeq_sym in aeqb;
	  exact (Eeq_incl_trans_l _ _ _ aeqb binclc).
Qed.
Lemma in_Eeq_trans_l : forall a b c : Ensemble, (b =E c) -> (a inE b) -> a inE c.
Proof.
	intros [a f] [b g] [c h] [binclc _] [x ainbbyx].
	specialize (binclc x) as [y Hy]; exists y.
	by exact (Eeq_trans _ _ _ ainbbyx Hy).
Qed.
Lemma in_Eeq_trans_r : forall a b c : Ensemble, (b =E c) -> (a inE c) -> a inE b.
Proof.
	by intros a b c beqc ainc; apply Eeq_sym in beqc;
	  exact (in_Eeq_trans_l _ _ _ beqc ainc).
Qed.
Lemma incl_Eeq_trans_l : forall a b c : Ensemble, (b =E c) -> (a incl b) -> a incl c.
Proof.
	intros [a f] [b g] [c h] [binclc _] ainclc x [y xinbbyy].
	specialize (ainclc _ (application_in _ _ y)) as [z Hz];
	  specialize (binclc z) as [k Hk];
	  exists k.
	by exact (Eeq_trans _ _ _ xinbbyy (Eeq_trans _ _ _ Hz Hk)).
Qed.
Lemma incl_Eeq_trans_r : forall a b c : Ensemble, (b =E c) -> (a incl c) -> a incl b.
Proof.
	by intros a b c beqc ainclc; apply Eeq_sym in beqc;
	  exact (incl_Eeq_trans_l _ _ _ beqc ainclc).
Qed.
Arguments Eeq_refl a : clear implicits.
Arguments Eeq_trans {a b c} ainclb binclc.
Arguments Eeq_sym {a b} ainclb.
Arguments eq_is_Eeq {a b} aeqb.
Arguments Eeq_in_trans_l {a b c} aeqb ainc.
Arguments Eeq_in_trans_r {a b c} aeqb binc.
Arguments Eeq_incl_trans_l {a b c} aeqb ainclc.
Arguments Eeq_incl_trans_r {a b c} aeqb binclc.
Arguments in_Eeq_trans_l {a b c} aeqb ainc.
Arguments in_Eeq_trans_r {a b c} aeqb binc.
Arguments incl_Eeq_trans_l {a b c} aeqb ainclc.
Arguments incl_Eeq_trans_r {a b c} aeqb binclc.

Lemma incl_refl : forall a : Ensemble, a incl a.
Proof. by intros a b bina; exact bina. Qed.
Lemma incl_trans : forall a b c : Ensemble, a incl b -> b incl c -> a incl c.
Proof.
	intros a b c ainclb binclc x xina.
	by exact (binclc _ (ainclb _ xina)).
Qed.
Lemma incl_antisym : forall a b : Ensemble, a incl b -> b incl a -> a =E b.
Proof.
	intros [a f] [b g] ainclb bincla; split.
	intros x.
	by exact (ainclb _ (application_in a f x)).
	intros y.
	specialize (bincla _ (application_in b g y)) as [x gyeqfx].
	by exists x; exact (Eeq_sym gyeqfx).
Qed.
Lemma Eeq_incl_l : forall a b : Ensemble, a =E b -> a incl b.
Proof.
	intros [a f] [b g] [ainclb _].
	intros x [y xinabyy].
	specialize (ainclb y) as [z fyeqgz].
	exists z.
	by exact (Eeq_trans xinabyy fyeqgz).
Qed.
Lemma Eeq_incl_r : forall a b : Ensemble, a =E b -> b incl a.
Proof.
	by intros a b beqa; exact (Eeq_incl_l _ _ (Eeq_sym beqa)).
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
Lemma empties_are_empty : forall a : Ensemble, (~ (exists x, x inE a)) -> (a =E EmptySet).
Proof.
	intros a ae.
	apply incl_antisym.
	intros x xina.
	by is_false (ae (ex_intro _ x xina)).
	intros ? [[] _].
Qed.
Corollary non_empty_is_not_empty : forall A : Ensemble,
  (A <>E EmptySet) -> exists x : _, x inE A.
Proof.
	intros a anee.
	apply NNPP; intros nexxina.
	by exact (anee (empties_are_empty a nexxina)).
Qed.

Definition separation_cons (A : Ensemble) (P : Ensemble -> Prop) : Ensemble :=
	let (A', f) := A in
	 ens { x : A' | P (f x) }
	  (fun p : { x : A' | P (f x) } => match p with exist _ x _ => f x end).
Notation "E{ x 'in' A | P }" := (separation_cons A (fun x => P))
	(at level 69, only parsing).
Notation "{ x 'in' A | P }" := (separation_cons A (fun x => P))
	(at level 69, only printing).

Lemma separation_cons_included : forall (A : Ensemble) (P : Ensemble -> Prop),
	E{x in A | P x} incl A.
Proof.
	intros [A f] P x [[y _] xinabyy].
	by exists y; exact xinabyy.
Qed.
Lemma separation_cons_separated : forall (A : Ensemble) (P : Ensemble -> Prop) x,
	(x inE E{ x in A | P x } ) -> P x.
Proof.
	intros [A f] P x [[y Pfy] xinsepbyy].
	by exact (extensionality_axiom' (Eeq_sym xinsepbyy) _ Pfy).
Qed.
Lemma separation_cons_separates : forall (A : Ensemble) (P : Ensemble -> Prop) x,
	(x inE A) -> P x -> (x inE E{x in A | P x}).
Proof.
	intros [A f] P x [y xinAbyy] Px.
	apply (extensionality_axiom' xinAbyy) in Px.
	by exists (exist _ y Px); exact xinAbyy.
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
	  apply (in_Eeq_trans_l xeq) in xiny; [left | right]; exact xiny.
	intros [xin | xin]; apply exyisxinc; [exists a | exists b]; split.
	1: by exact (proj2 (iff_and (Hc' a)) (or_introl (Eeq_refl _))).
	2: by exact (proj2 (iff_and (Hc' b)) (or_intror (Eeq_refl _))).
	1,2: by exact xin.
Qed.
Inductive binarychoice := | leftopt : binarychoice | rightopt : binarychoice.
Definition pairing_cons (A B : Ensemble)
	:= ens binarychoice (fun b => match b with | leftopt => A | rightopt => B end).
Definition singleton (x : Ensemble) := pairing_cons x x.
Notation "E{ A ';' B }" := (pairing_cons A B) (at level 69, only parsing).
Notation "{ A  ;  B }" := (pairing_cons A B) (at level 69, only printing).
Notation "E{ A }" := (singleton A) (at level 69, format "E{ A }").
(* For all Ensemble A,
 * ens_union_cons constructs a type that is then mapped to all elements
 *  of the elements of A.
 * existT x y: x is of the type of A, and maps to B by A;
 *   then y is of the type of B, and maps to the final set by B.
 *)
Definition ens_union_cons (A : Ensemble) : Ensemble := let (A', f) := A in
	ens { x : A' & pi1e (f x) }
		(fun X => match X with existT _ x y => pi2e (f x) y end).
Definition pair_union_cons (A B : Ensemble) : Ensemble
	:= ens_union_cons (E{ A ; B }).

Infix "\union" := pair_union_cons (at level 50, left associativity).
Notation "'\Union' a" := (ens_union_cons a) (at level 69, no associativity).
Notation "a \\ b" := (separation_cons a (fun x => x not_in b)) (at level 69, no associativity).
Definition inter a b := separation_cons a (fun x => x inE b).
Infix "\inter" := inter (at level 50, left associativity).

Lemma ens_union_is_union : forall A : Ensemble, forall B : Ensemble,
	B inE (\Union A) -> exists C : Ensemble, C inE A /\ B inE C.
Proof.
	intros [A f] [B g] [[x y] BinCbyy].
	exists (f x); split.
	by exact (application_in _ _ _).
	rewrite (ens_pi_is_orig (f x)).
	by exists y; exact BinCbyy.
Qed.
Lemma union_is_ens_union : forall A : Ensemble, forall B : Ensemble,
	(B inE A) -> B incl (\Union A).
Proof.
	intros [A f] [B g] [x BinAbyx] [C h] [y CinBbyy].
	rewrite (ens_pi_is_orig (f x)) in BinAbyx.
	destruct BinAbyx as [Binclfx _].
	specialize (Binclfx y) as [y' gxinfxbyy'].
	exists (existT _ x y').
	by exact (Eeq_trans CinBbyy gxinfxbyy').
Qed.
Arguments ens_union_is_union {A B} BinUA.
Arguments union_is_ens_union {A B} BinA.

Lemma ens_inter_is_inter : forall A B : Ensemble, forall C : Ensemble,
	C inE (A \inter B) -> (C inE A) /\ (C inE B).
Proof.
	intros a b c cininter; split.
	by exact (separation_cons_included _ _ _ cininter).
	by exact (separation_cons_separated _ _ _ cininter).
Qed.
Lemma inter_is_ens_inter : forall A B : Ensemble, forall C : Ensemble,
	(C inE A) -> (C inE B) -> C inE (A \inter B).
Proof. by intros a b c; exact (separation_cons_separates _ _ _). Qed.
Arguments ens_inter_is_inter {A B C} CinAuB.
Arguments inter_is_ens_inter {A B C} CinA CinB.

Lemma l_in_pairing : forall A B : Ensemble, A inE E{A ; B}.
Proof.
	by intros A B; exists leftopt; exact (Eeq_refl _).
Qed.
Lemma r_in_pairing : forall A B : Ensemble, B inE E{A ; B}.
Proof.
	by intros A B; exists rightopt; exact (Eeq_refl _).
Qed.
Lemma pairing_is_lr : forall A B C : Ensemble,
	C inE E{A ; B} -> C =E A \/ C =E B.
Proof.
	intros A B C [[|] eeq].
	by left;  exact eeq.
	by right; exact eeq.
Qed.
Lemma pairing_trans_l : forall A B C : Ensemble,
	A =E B -> E{A ; C} =E E{B ; C}.
Proof.
	intros A B C AeqB; apply incl_antisym.
	intros x xinAC.
	specialize (pairing_is_lr _ _ _ xinAC) as [xeqA | xeqC].
	by exact (Eeq_in_trans_r (Eeq_trans xeqA AeqB) (l_in_pairing _ _)).
	by exact (Eeq_in_trans_r xeqC (r_in_pairing _ _)).
	intros x xinBC.
	specialize (pairing_is_lr _ _ _ xinBC) as [xeqB | xeqC].
	by exact (Eeq_in_trans_r (Eeq_trans xeqB (Eeq_sym AeqB)) (l_in_pairing _ _)).
	by exact (Eeq_in_trans_r xeqC (r_in_pairing _ _)).
Qed.
Lemma pairing_trans_r : forall A B C : Ensemble,
	B =E C -> E{A ; B} =E E{A ; C}.
Proof.
	intros A B C BeqC; apply incl_antisym.
	intros x xinCA.
	specialize (pairing_is_lr _ _ _ xinCA) as [xeqC | xeqA].
	by exact (Eeq_in_trans_r xeqC (l_in_pairing _ _)).
	by exact (Eeq_in_trans_r (Eeq_trans xeqA BeqC) (r_in_pairing _ _)).
	intros x xinCB.
	specialize (pairing_is_lr _ _ _ xinCB) as [xeqC | xeqB].
	by exact (Eeq_in_trans_r xeqC (l_in_pairing _ _)).
	by exact (Eeq_in_trans_r (Eeq_trans xeqB (Eeq_sym BeqC)) (r_in_pairing _ _)).
Qed.
Lemma pairing_trans : forall A B C D : Ensemble, A =E C -> B =E D -> E{A ; B} =E E{C ; D}.
Proof.
	intros A B C D AeqC BeqD; apply incl_antisym.
	intros x xinAB; specialize (pairing_is_lr _ _ _ xinAB) as [xeqA | xeqB].
	by exact (Eeq_in_trans_r (Eeq_trans xeqA AeqC) (l_in_pairing _ _)).
	by exact (Eeq_in_trans_r (Eeq_trans xeqB BeqD) (r_in_pairing _ _)).
	intros x xinCD; specialize (pairing_is_lr _ _ _ xinCD) as [xeqC | xeqD].
	by exact (Eeq_in_trans_r (Eeq_trans xeqC (Eeq_sym AeqC)) (l_in_pairing _ _)).
	by exact (Eeq_in_trans_r (Eeq_trans xeqD (Eeq_sym BeqD)) (r_in_pairing _ _)).
Qed.
Lemma pairing_sym : forall A B : Ensemble, E{A ; B} =E E{B ; A}.
Proof.
	intros A B; split; intros [|];
	  [exists rightopt | exists leftopt | exists rightopt | exists leftopt];
	  by exact (Eeq_refl _).
Qed.
Lemma pairing_inj : forall A B C : Ensemble, E{A ; C} =E E{B ; C} -> A =E B.
Proof.
	intros A B C ACeqBC.
	specialize (pairing_is_lr _ _ _ (in_Eeq_trans_l ACeqBC (l_in_pairing A C))) as [AeqB | AeqC].
	by exact AeqB.
	specialize (pairing_is_lr _ _ _
	  (in_Eeq_trans_l (Eeq_sym ACeqBC) (l_in_pairing B C))) as [BeqA | BeqC].
	by exact (Eeq_sym BeqA).
	by exact (Eeq_trans AeqC (Eeq_sym BeqC)).
Qed.

Lemma pair_union_is_union_l : forall A B : Ensemble, A incl (A \union B).
Proof.
	intros A B e einA.
	by exact (union_is_ens_union (l_in_pairing _ _) _ einA).
Qed.
Lemma pair_union_is_union_r : forall A B : Ensemble, B incl (A \union B).
Proof.
	intros A B e einB.
	by exact (union_is_ens_union (r_in_pairing _ _) _ einB).
Qed.
Lemma pair_union_is_union : forall A B C : Ensemble,
	C inE (A \union B) -> C inE A \/ C inE B.
Proof.
	intros [A f] [B g] C [[[|] xval] CinAuBbyx].
	by left;  exists xval; exact CinAuBbyx.
	by right; exists xval; exact CinAuBbyx.
Qed.
Lemma incl_incl_is_union_incl : forall A B C : Ensemble,
	A incl C -> B incl C -> (A \union B) incl C.
Proof.
	intros A B C AinclC BinclC x xinAuB;
	  specialize (pair_union_is_union _ _ _ xinAuB) as [xinA | xinB].
	by exact (AinclC _ xinA).
	by exact (BinclC _ xinB).
Qed.
Arguments pairing_is_lr {A B C} CinAB.
Arguments pairing_inj {A B C} ACeqBC.
Arguments pairing_trans {A B C D} AeqC BeqD.
Arguments pair_union_is_union {A B C} CinAuB.
Arguments incl_incl_is_union_incl {A B C} AinclC BinclC.

Lemma singleton_has_elem : forall A : Ensemble, A inE E{A}.
Proof.
	by intros [A f]; exists leftopt; exact (Eeq_refl _).
Qed.
Lemma singleton_is_singleton : forall A B : Ensemble, B inE E{A} -> B =E A.
Proof.
	by intros A B BinsA;
	  specialize (pairing_is_lr BinsA) as [H | H];
	  exact H.
Qed.
Lemma singleton_incl_is_in : forall A B : Ensemble, E{A} incl B -> A inE B.
Proof.
	intros A B sAinclB.
	by exact (sAinclB _ (singleton_has_elem A)).
Qed.
Lemma in_is_singleton_incl : forall A B : Ensemble, A inE B -> E{A} incl B.
Proof.
	intros A B AinB x xinA.
	by exact (Eeq_in_trans_r (singleton_is_singleton _ _ xinA) AinB).
Qed.
Lemma singleton_refl : forall A B : Ensemble, A =E B -> E{A} =E E{B}.
Proof.
	intros A B AeqB; apply incl_antisym.
	intros x xinsA.
	apply singleton_is_singleton in xinsA.
	apply (Eeq_in_trans_r (Eeq_trans xinsA AeqB)).
	by exact (singleton_has_elem _).
	intros x xinsB.
	apply singleton_is_singleton in xinsB.
	apply (Eeq_in_trans_r (Eeq_trans xinsB (Eeq_sym AeqB))).
	by exact (singleton_has_elem _).
Qed.
Lemma singleton_inj : forall A B : Ensemble, E{A} =E E{B} -> A =E B.
Proof.
	intros A B sAeqsB.
	by exact (singleton_is_singleton _ _ (singleton_incl_is_in _ _ (Eeq_incl_l sAeqsB))).
Qed.
Lemma singleton_union_singleton : forall A B : Ensemble, (E{A}) \union (E{B}) =E E{A ; B}.
Proof.
	intros A B; apply incl_antisym.
	intros x xinsAusB; specialize (pair_union_is_union xinsAusB) as [xinsA | xinsB].
	by exact (Eeq_in_trans_r (singleton_is_singleton _ _ xinsA) (l_in_pairing _ _)).
	by exact (Eeq_in_trans_r (singleton_is_singleton _ _ xinsB) (r_in_pairing _ _)).
	intros x xinAB; specialize (pairing_is_lr xinAB) as [xeqA | xeqB].
	by exact (pair_union_is_union_l _ _ _ (Eeq_in_trans_r xeqA (singleton_has_elem _))).
	by exact (pair_union_is_union_r _ _ _ (Eeq_in_trans_r xeqB (singleton_has_elem _))).
Qed.
Arguments singleton_is_singleton {A B} AinsB.
Arguments singleton_incl_is_in {A B} sAinclB.
Arguments in_is_singleton_incl {A B} AinB.
Arguments singleton_refl {A B} AeqB.
Arguments singleton_inj {A B} sAeqsB.

Lemma exists_inter_set
 : forall A, (A <>E EmptySet) ->
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

Definition Succ (A : Ensemble) := A \union (E{A}).
Definition is_nat (A : Ensemble) :=
	(EmptySet inE A) /\ forall x, (x inE A) -> ((Succ x) inE A).
Axiom infinity_axiom : { N : Ensemble & (is_nat N) /\ (forall a, (is_nat a) -> N incl a) }.
Definition NatE := let (NE, _) := infinity_axiom in NE.
Definition NatP : (is_nat NatE) /\ (forall a, (is_nat a) -> NatE incl a).
	unfold NatE; destruct infinity_axiom; assumption.
Defined.

Corollary Empty_in_NatE : EmptySet inE NatE.
Proof.
	exact (proj1 (proj1 NatP)).
Qed.
Corollary Succ_in_NatE : forall n, n inE NatE -> Succ n inE NatE.
Proof.
	exact (proj2 (proj1 NatP)).
Qed.
Corollary NatE_smallest : forall a, is_nat a -> NatE incl a.
Proof.
	exact (proj2 NatP).
Qed.

Section NatNums.
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
Lemma in_succ_in_eq : forall e f, e inE Succ f -> (e inE f) \/ (e =E f).
Proof.
	intros e f einSf.
	specialize (pair_union_is_union einSf) as [einf|einsf].
	by left; exact einf.
	by right; exact (singleton_is_singleton einsf).
Qed.
Lemma Eeq_is_Eeq_succ : forall A B : Ensemble, A =E B -> Succ A =E Succ B.
Proof.
	intros A B AeqB; apply incl_antisym; intros x; [intros xinSA | intros xinSB].
	specialize (pair_union_is_union xinSA) as [xinA | xinsA].
	by exact (pair_union_is_union_l _ _ _ (Eeq_incl_l AeqB _ xinA)).
	by exact (pair_union_is_union_r _ _ _
	  (Eeq_in_trans_r (Eeq_trans (singleton_is_singleton xinsA) AeqB)
	   (singleton_has_elem _))).
	apply Eeq_sym in AeqB.
	specialize (pair_union_is_union xinSB) as [xinB | xinsB].
	by exact (pair_union_is_union_l _ _ _ (Eeq_incl_l AeqB _ xinB)).
	by exact (pair_union_is_union_r _ _ _
	  (Eeq_in_trans_r (Eeq_trans (singleton_is_singleton xinsB) AeqB)
	   (singleton_has_elem _))).
Qed.
Arguments in_succ_in_eq {e f} einSf.
Arguments Eeq_is_Eeq_succ {A B} AeqB.

(*Inductive nat :=
	| O : nat
	| S : nat -> nat.
Fixpoint N (n : nat) : Ensemble := match n with O => EmptySet | S n => Succ (N n) end.
Definition Nnat : Ensemble := ens nat N.*)

Lemma induction_N (P : Ensemble -> Prop) :
 P EmptySet -> (forall e : Ensemble, e inE NatE -> P e -> P (Succ e)) -> forall n, n inE NatE -> P n.
Proof.
	intros I IH.
	specialize (schema_restricted_comprehension_axiom P NatE) as [[C h] Cprop].
	assert (C_is_nat : is_nat (ens C h)).
	{ split.
	  apply (Cprop EmptySet); split.
	  by exact Empty_in_NatE.
	  by exact I.
	  intros x xin; apply Cprop in xin; destruct xin as [xin pPx]; apply Cprop; split.
	  by exact (Succ_in_NatE _ xin).
	  by exact (IH _ xin pPx). }
	intros n nin; specialize (NatE_smallest _ C_is_nat _ nin) as ninC; apply Cprop in ninC.
	by exact (proj2 ninC).
Qed.
(*Lemma double_induction : forall P : nat -> Prop, P O -> P (S O) ->
  (forall n : nat, P n -> P (S n) -> P (S (S n))) -> forall n, P n.*)
Lemma double_induction_N : forall P : Ensemble -> Prop, P EmptySet -> P (Succ EmptySet) ->
  (forall n, n inE NatE -> P n -> P (Succ n) -> P (Succ (Succ n))) -> forall n, n inE NatE -> P n.
Proof.
	intros P I0 I1 IH.
	(*assert (H : forall n : nat, P n /\ P (S n)).*)
	assert (H : forall n, n inE NatE -> P n /\ P (Succ n)).
	{ (*intros n; induction n as [|n [IHn IHSn]]; split.
	  by exact I0. by exact I1.
	  by exact IHSn.
	  by exact (IH _ IHn IHSn). }*)
	  apply induction_N; [|intros n ninN IH2]; split.
	  by exact I0. by exact I1.
	  by exact (proj2 IH2). by exact (IH _ ninN (proj1 IH2) (proj2 IH2)). }
	(*by intros n; exact (proj1 (H _)).*)
	by intros n nin; exact (proj1 (H _ nin)).
Qed.

Lemma NatEcara : forall n, n inE NatE -> n = EmptySet \/ exists m, m inE NatE /\ n =E Succ m.
	apply induction_N.
	left; exact (eq_refl _).
	intros n nin [neqe|[m [min Hm]]].
	right; exists EmptySet; split.
	by exact Empty_in_NatE.
	by rewrite neqe; exact (Eeq_refl _).
	right; exists (Succ m); split.
	by exact (Succ_in_NatE _ min).
	by exact (Eeq_is_Eeq_succ Hm).
Qed.

(*Lemma N_in_nat : forall a : _, is_nat a -> Nnat incl a.
Proof.
	intros a [eina succaincla] Nn [n NninNbyn].
	apply (Eeq_in_trans_r NninNbyn).
	by exact (induction_N (fun k => k inE a) eina succaincla n).
Qed.
Lemma N_is_nat : is_nat Nnat.
Proof.
	split.
	by exists O; exact (Eeq_refl _).
	intros x [n xinNbyn].
	by exists (S n); exact (Eeq_is_Eeq_succ xinNbyn).
Qed.
Lemma nat_in_N : forall a : Ensemble,
	is_nat a ->
	(forall b : Ensemble, is_nat b -> a incl b) ->
	forall n : Ensemble, n inE a -> exists k : nat, n =E N k.
Proof.
	intros a [eina succaincla] ainclallnat n nina.
	specialize (ainclallnat Nnat N_is_nat) as ainclN.
	specialize (ainclN _ nina) as [b ninNbyb].
	by exists b; exact ninNbyb.
Qed.

Inductive LessThan_itercN : nat -> nat -> Type :=
	| ltic_oN : forall n : nat, LessThan_itercN O (S n)
	| ltic_iterN : forall m n : nat, LessThan_itercN m n -> LessThan_itercN (S m) (S n).
Inductive GreaterEqual_itercN : nat -> nat -> Type :=
	| geic_oN : forall m : nat, GreaterEqual_itercN m O
	| geic_iterN : forall m n : nat, GreaterEqual_itercN m n
		-> GreaterEqual_itercN (S m) (S n).
Fixpoint MinN (m : nat) (n : nat) : nat := match m, n with
	| O, _ | _, O => O
	| S m', S n' => S (MinN m' n') end.
Arguments ltic_iterN {m n} p.
Arguments geic_iterN {m n} p.
Definition LessThan_iterN m n := exists p : LessThan_itercN m n, p = p.
Definition GreaterEqual_iterN m n := exists p : GreaterEqual_itercN m n, p = p.
Definition ltc2lt_iterN m n p : LessThan_iterN _ _ := ex_intro (fun p: LessThan_itercN m n => p = p) p (eq_refl p).
Definition gec2ge_iterN m n p : GreaterEqual_iterN _ _ := ex_intro (fun p: GreaterEqual_itercN m n => p = p) p (eq_refl p).
Arguments ltc2lt_iterN {m n} p.
Arguments gec2ge_iterN {m n} p.
Definition lti_oN n := ltc2lt_iterN (ltic_oN n).
Definition gei_oN n := gec2ge_iterN (geic_oN n).
Definition lti_iterN {m n} (p : LessThan_iterN _ _) : LessThan_iterN _ _
	:= let (p', _) := p in ltc2lt_iterN (ltic_iterN (m:=m) (n:=n) p').
Definition gei_iterN {m n} (p : GreaterEqual_iterN _ _) : GreaterEqual_iterN _ _
	:= let (p', _) := p in gec2ge_iterN (geic_iterN (m:=m) (n:=n) p').
Lemma minNC : forall m n : nat, MinN m n = MinN n m.
Proof.
	intros m; induction m as [|m IHm]; intros [|n].
	1,2,3: by exact (eq_refl _).
	by minimize MinN; rewrite (IHm _); exact (eq_refl _).
Qed.
Lemma lt_or_ge_iterN : forall m n : nat, LessThan_iterN m n \/ GreaterEqual_iterN m n.
Proof.
	intros m n; generalize dependent m; induction n as [|n IHn];
	 [intros ? | intros [|m]].
	by right; exact (gei_oN _).
	by left;  exact (lti_oN _).
	specialize (IHn m) as [lt | ge].
	by left;  exact (lti_iterN lt).
	by right; exact (gei_iterN ge).
Qed.
Lemma lt_iterc_revN : forall m n, LessThan_itercN (S m) (S n) -> LessThan_itercN m n.
Proof.
	intros m n mltn.
	inversion mltn as [|m' n' H m'eqm n'eqn]; clear m' n' m'eqm n'eqn.
	by exact H.
Qed.
Lemma ge_iterc_revN : forall m n, GreaterEqual_itercN (S m) (S n) -> GreaterEqual_itercN m n.
Proof.
	intros m n mgen.
	inversion mgen as [|m' n' H m'eqm n'eqn]; clear m' n' m'eqm n'eqn.
	by exact H.
Qed.
Arguments lt_iterc_revN {m n} p.
Arguments ge_iterc_revN {m n} p.
Lemma lt_iter_revN : forall m n, LessThan_iterN (S m) (S n) -> LessThan_iterN m n.
Proof.
	intros m n [mltn _].
	by exact (ltc2lt_iterN (lt_iterc_revN mltn)).
Qed.
Lemma ge_iter_revN : forall m n, GreaterEqual_iterN (S m) (S n) -> GreaterEqual_iterN m n.
Proof.
	intros m n [mgen _].
	by exact (gec2ge_iterN (ge_iterc_revN mgen)).
Qed.
Arguments lt_iter_revN {m n} p.
Arguments ge_iter_revN {m n} p.
Lemma lt_is_not_ge_iterN : forall m n, LessThan_iterN m n -> ~ GreaterEqual_iterN m n.
Proof.
	intros m; induction m as [|m IHm]; intros [|n] mltn mgen.
	1,3: by destruct mltn as [mltn _]; inversion mltn.
	     by destruct mgen as [mgen _]; inversion mgen.
	by exact (IHm _ (lt_iter_revN mltn) (ge_iter_revN mgen)).
Qed.
Lemma ge_is_not_lt_iterN : forall m n, GreaterEqual_iterN m n -> ~ LessThan_iterN m n.
Proof.
	intros m; induction m as [|m IHm]; intros [|n] mgen mltn.
	1,3: by destruct mltn as [mltn _]; inversion mltn.
	     by destruct mgen as [mgen _]; inversion mgen.
	by exact (IHm _ (ge_iter_revN mgen) (lt_iter_revN mltn)).
Qed.

Lemma lt_is_min_iterN : forall m n : nat, LessThan_iterN m n -> MinN m n = m.
Proof.
	intros m; induction m as [|m IHm].
	by intros; exact (eq_refl _).
	intros [|n] mltn.
	by is_false (ge_is_not_lt_iterN _ _ (gei_oN _) mltn).
	by exact (f_equal _ (IHm _ (lt_iter_revN mltn))).
Qed.
Lemma le_is_min_iterN : forall m n : nat, LessThan_iterN m (S n) -> MinN m n = m.
Proof.
	intros m; induction m as [|m IHm].
	by intros; exact (eq_refl _).
	intros [|n] mltn; apply lt_iter_revN in mltn.
	by is_false (ge_is_not_lt_iterN _ _ (gei_oN _) mltn).
	by exact (f_equal _ (IHm _ mltn)).
Qed.

Lemma lt_iterc_nextN {m n : nat} : LessThan_itercN m n -> LessThan_itercN m (S n).
Proof.
	intros lti.
	induction lti as [n|m n mltn IHmltn].
	by exact (ltic_oN _).
	by exact (ltic_iterN IHmltn).
Qed.
Lemma ge_iterc_nextN {m n : nat} : GreaterEqual_itercN m n -> GreaterEqual_itercN (S m) n.
Proof.
	intros gei.
	induction gei as [n|m n mgen IHmgen].
	by exact (geic_oN _).
	by exact (geic_iterN IHmgen).
Qed.
Lemma lt_iter_nextN {m n : nat} : LessThan_iterN m n -> LessThan_iterN m (S n).
Proof.
	intros [mltn _].
	by exact (ltc2lt_iterN (lt_iterc_nextN mltn)).
Qed.
Lemma ge_iter_nextN {m n : nat} : GreaterEqual_iterN m n -> GreaterEqual_iterN (S m) n.
Proof.
	intros [mgen _].
	by exact (gec2ge_iterN (ge_iterc_nextN mgen)).
Qed.

Lemma lt_is_tg_iterN : forall m n : nat, LessThan_iterN m n -> GreaterEqual_iterN n (S m).
Proof.
	intros m; induction m as [|m IHm]; intros [|n] mltn.
	1,3: by is_false (lt_is_not_ge_iterN _ _ mltn (gei_oN _)).
	by exact (gei_iterN (gei_oN _)).
	by exact (gei_iterN (IHm _ (lt_iter_revN mltn))).
Qed.
Lemma ge_is_el_iterN : forall m n : nat, GreaterEqual_iterN m n -> LessThan_iterN n (S m).
Proof.
	intros m; induction m as [|m IHm]; intros [|n] mgen.
	1,3: by exact (lti_oN _).
	by is_false (ge_is_not_lt_iterN _ _ mgen (lti_oN _)).
	by exact (lti_iterN (IHm _ (ge_iter_revN mgen))).
Qed.

Lemma n_lt_Sn : forall n : nat, LessThan_iterN n (S n).
Proof.
	intros n; induction n as [|n IHn].
	by exact (lti_oN _).
	by exact (lti_iterN IHn).
Qed.
Lemma n_ge_n : forall n : nat, GreaterEqual_iterN n n.
Proof.
	intros n; induction n as [|n IHn].
	by exact (gei_oN _).
	by exact (gei_iterN IHn).
Qed.

Lemma m_lt_Sn_ne_n : forall m n : nat, LessThan_iterN m (S n) -> m <> n -> LessThan_iterN m n.
Proof.
	intros m; induction m as [|m IHm]; intros [|n] mltSn mnen.
	by is_false (mnen (eq_refl _)).
	by exact (lti_oN _).
	by is_false (ge_is_not_lt_iterN _ _ (gei_iterN (gei_oN _)) mltSn).
	assert (mnen' : m <> n) by (intros meqn; exact (mnen (f_equal _ meqn))).
	by exact (lti_iterN (IHm _ (lt_iter_revN mltSn) mnen')).
Qed.

Fixpoint addN m n := match m with
	| O => n
	| S m' => S (addN m' n) end.
Lemma add_m_Sn : forall m n : nat, addN m (S n) = S (addN m n).
Proof.
	intros m; induction m as [|m IHm]; intros n.
	by exact (eq_refl _).
	by minimize addN; rewrite IHm; exact (eq_refl _).
Qed.
Lemma add_Sm_n : forall m n : nat, addN (S m) n = S (addN m n).
Proof.
	by intros; exact (eq_refl _).
Qed.
Lemma addNC : forall m n : nat, addN m n = addN n m.
Proof.
	intros m; induction m as [|m IHm]; intros n.
	induction n as [|n IHn].
	by exact (eq_refl _).
	by rewrite (add_m_Sn _ _), IHn; exact (eq_refl _).
	by rewrite (add_m_Sn _ _), <-(IHm _); exact (eq_refl _).
Qed.
Lemma addNA : forall m n p : nat, addN (addN m n) p = addN m (addN n p).
Proof.
	intros m; induction m as [|m IHm]; intros n p.
	by exact (eq_refl _).
	by minimize addN; rewrite IHm; exact (eq_refl _).
Qed.

Lemma n_in_Sn : forall n : nat, (N n) inE (N (S n)).
Proof.
	intros n.
	by exact (e_in_succ _).
Qed.*)
(*Lemma natural_longest_string_n : forall n : nat,
	(forall g : nat -> Ensemble,
	 (forall m : nat, LessThan_iterN m n -> (g m) inE (g (S m))) ->
	 (g n =E N n) ->
	 (forall m : nat, LessThan_iterN m (S n) -> g m =E N m)) /\
	(forall f : nat -> Ensemble, (exists m : nat,
		(LessThan_iterN m (S n) /\ (f m) not_in (f (S m)))) \/
		((f (S n)) not_in (N (S n)))).*)
Lemma natural_longest_string_n : forall n, n inE NatE ->
	(forall g : Ensemble -> Ensemble,
	 (forall m, m inE n -> (g m) inE (g (Succ m))) ->
	 (g n =E n) ->
	 (forall m, m inE (Succ n) -> g m =E m)) /\
	(forall f : Ensemble -> Ensemble,
	 (exists m, m inE n /\ (f m) not_in (f (Succ m))) \/
	 (f n not_in n)).
Proof.
	apply induction_N; [|intros n ninN [IHnL IHnR]]; split.
	- intros g Hg gOeqO m mltSO.
	  unfold Succ in mltSO.
	  specialize (in_succ_in_eq mltSO) as [mine|meqe].
	  by contradiction (empty_is_empty _ mine).
	  by rewrite (Eextensionality_axiom meqe); exact gOeqO.
	- intros f.
	  by right; exact (empty_is_empty _).
	  (*specialize (classic (f (Succ EmptySet) =E EmptySet)) as [fSOeq | fSOne].
	  left; exists EmptySet; split.
	  by exact (e_in_succ _).
	  by rewrite (Eextensionality_axiom fSOeq); exact (empty_is_empty _).
	  right; intros fSOeqO.
	  specialize (in_succ_in_eq fSOeqO) as [fSOine|fSOeqe].
	  by exact (empty_is_empty _ fSOine).
	  by exact (fSOne fSOeqe).*)
	- intros g Hg gSneqSn; apply Eextensionality_axiom in gSneqSn.
	  assert (gneqn : g n =E n).
	  { remember Hg as Hg' eqn: tmp; clear tmp; specialize (Hg' n (e_in_succ _)).
	    rewrite gSneqSn in Hg'; specialize (in_succ_in_eq Hg') as [gninn|gneqn].
	    exfalso; specialize (IHnR g) as [[m [IHRLL IHRLR]]|IHRR].
	    by exact (IHRLR (Hg _ (e_incl_succ _ _ IHRLL))).
	    by exact (IHRR gninn).
	    by exact gneqn. }
	  intros m minSSn; destruct (in_succ_in_eq minSSn) as [minSn|meqSn].
	  refine (IHnL _ _ gneqn _ minSn).
	  by intros m0 Hm0; exact (Hg _ (e_incl_succ _ _ Hm0)).
	  by rewrite (Eextensionality_axiom meqSn), gSneqSn; exact (Eeq_refl _).
	- intros f.
	  specialize (classic (f (Succ n) inE Succ n)) as [fSnin | fSnni].
	  + left; specialize (IHnR f) as [[m [IHnRLL IHnRLR]]|IHnRR].
	    by exists m; split; [exact (e_incl_succ _ _ IHnRLL)|exact IHnRLR].
	    exists n; split.
	    by exact (e_in_succ _).
	    intros fninfSn.
	    specialize (in_succ_in_eq fSnin) as [fSninn|fSneqn].
	    * apply IHnRR; remember (f n) as i eqn:tmp; clear tmp; remember (f (Succ n)) as k eqn:tmp; clear tmp;
	        clear IHnL f fSnin IHnRR.
	      generalize dependent n; refine (induction_N _ _ _).
	      by intros F; contradiction (empty_is_empty _ F).
	      intros n nin IHn kinSn.
	      specialize (in_succ_in_eq kinSn) as [kinn|keqn].
	      by exact (e_incl_succ _ _ (IHn kinn)).
	      by exact (in_Eeq_trans_l (Eeq_is_Eeq_succ keqn) (e_incl_succ _ _ fninfSn)).
	    * by exact (IHnRR (in_Eeq_trans_l fSneqn fninfSn)).
	  + by right; exact fSnni.
	(*intros n; induction n as [|n [IHnL IHnR]]; split.
	- intros g Hg gOeqO [|m] mltSO.
	  by exact gOeqO.
	  by is_false (ge_is_not_lt_iterN _ _ (gei_oN _) (lt_iter_revN mltSO)).
	- intros f.
	  specialize (classic (f (S O) =E N O)) as [fSOeq | fSOne].
	  left; exists O; split.
	  by exact (lti_oN _).
	  intros fOnifSO; specialize (in_Eeq_trans_l fSOeq fOnifSO); unfold N.
	  by exact (empty_is_empty _).
	  right; intros fSOinSO.
	  specialize (pair_union_is_union fSOinSO) as [fSOinO | fSOinsO].
	  by exact (empty_is_empty _ fSOinO).
	  specialize (singleton_is_singleton fSOinsO) as fSOinO.
	  by exact (fSOne fSOinO).
	- intros g Hg gSneqSn.
	  remember Hg as Hg' eqn:tmp; specialize (Hg' _ (n_lt_Sn n)) as gninSn; clear tmp Hg'.
	  specialize (in_Eeq_trans_l gSneqSn gninSn) as tmp; clear gninSn; rename tmp into gninSn.
	  specialize (pair_union_is_union gninSn) as [gninn | gninsn].
	  + exfalso.
	    pose (h' := fix h' i j k n := match i with
	      | O => match j with | O => N n | _ => g k end
	      | S i' => match j with
	        | O => match i' with | O => g (S k) | _ => h' i' O (S k) n end
	        | S j' => h' i' j' (S k) n end
	    end).
	    assert (h'SmOisgSm : forall m n p, h' (S m) O n p = g (addN (S m) n)).
	    { clear dependent n; intros m; induction m as [|m IHm]; intros n p.
	      by exact (eq_refl _).
	      minimize h' in IHm; minimize addN in IHm.
	      minimize addN; rewrite <-(add_m_Sn m n).
	      by exact (IHm (S n) p). }
	    assert (neisg'eqg : forall m p q r, m <> p -> h' m p q r = g (addN q m)).
	    { clear dependent n; intros m p.
	      generalize dependent m; induction p as [|p IHp]; intros [|m] q r mneSp.
	      by is_false (mneSp (eq_refl _)).
	      by rewrite addNC; exact (h'SmOisgSm m q r).
	      by rewrite addNC; exact (eq_refl _).
	      assert (mnep : m <> p) by (intros meqp; exact (mneSp (f_equal S meqp))).
	      rewrite (add_m_Sn _ _), <-(add_Sm_n _ _).
	      by exact (IHp m (S q) r mnep). }
	    assert (g'SneqNSn : forall n p q, h' n n p q = N q).
	    { clear; intros n; induction n as [|n IHn]; intros p q.
	      by exact (eq_refl _).
	      by exact (IHn _ _). }
	    specialize (IHnR (fun m => h' m (S n) O n)) as [[m [mltSn fmnifSm]] | fSnniSn].
	    * specialize (classic (m = n)) as [meqn | mnen].
	      -- rewrite meqn in fmnifSm; clear dependent m.
	         rewrite (g'SneqNSn _ _ _) in fmnifSm.
	         assert (nneSn : n <> S n). (* Propably provable through sets *)
	         { clear; intros neqSn; induction n as [|n IHn].
	           by discriminate neqSn.
	           by injection neqSn as neqSn'; exact (IHn neqSn'). }
	         rewrite (neisg'eqg _ _ _ _ nneSn) in fmnifSm.
	         by exact (fmnifSm gninn).
	      -- assert (mneSn : m <> S n) by (
	           intros meqSn; rewrite meqSn in mltSn;
	           exact (ge_is_not_lt_iterN _ _ (n_ge_n _) mltSn)).
	         minimize h' in fmnifSm.
	         rewrite (neisg'eqg _ _ _ _ mnen) in fmnifSm.
	         rewrite (neisg'eqg _ _ _ _ mneSn) in fmnifSm.
	         by exact (fmnifSm (Hg _ mltSn)).
	    * rewrite (g'SneqNSn _ _ _) in fSnniSn.
	      by exact (fSnniSn (n_in_Sn _)).
	  
	  + specialize (singleton_is_singleton gninsn) as gneqn; clear gninsn.
	    intros m mltSSn.
	    specialize (classic (m = S n)) as [meqSn | mneSn].
	    by rewrite meqSn; exact gSneqSn.
	    specialize (m_lt_Sn_ne_n _ _ mltSSn mneSn) as mltSn; clear mltSSn mneSn.
	    refine (IHnL _ _ gneqn _ mltSn).
	    clear m mltSn; intros m mltn.
	    by exact (Hg _ (lt_iter_nextN mltn)).
	- intros f.
	  specialize (classic (f (S (S n)) inE N (S (S n)))) as [fSSninSSn | fSSnniSSn]; swap 1 2.
	  by right; exact fSSnniSSn.
	  left.
	  specialize (classic (exists m : nat, LessThan_iterN m (S n) /\ f m not_in f (S m))) as [[m [mltSn fmnifSm]] | nex].
	  + exists m; split.
	    by exact (lt_iter_nextN mltSn).
	    by exact fmnifSm.
	  + exists (S n); split.
	    by exact (n_lt_Sn _).
	    remember IHnR as IHnR' eqn:tmp; clear tmp; specialize (IHnR' f) as [mex | fSnniSn].
	    by is_false (nex mex).
	    specialize (not_ex_all_not _ _ nex) as hypf; lazy beta in hypf; clear nex.
	    specialize (IHnR (fun m => f (S m))) as [[m [mltSn fSmnifSSm]] | fSSnniSn].
	    specialize (classic (m = n)) as [meqn | mnen].
	    by rewrite <-meqn; exact fSmnifSSm.
	    specialize (lti_iterN (m_lt_Sn_ne_n _ _ mltSn mnen)) as SmltSn.
	    specialize (not_and_or _ _ (hypf (S m))) as [l | r].
	    by is_false (l SmltSn).
	    by is_false (r fSmnifSSm).
	    specialize (pair_union_is_union fSSninSSn) as [fSSninSn | fSSninsSn].
	    by is_false (fSSnniSn fSSninSn).
	    specialize (singleton_is_singleton fSSninsSn) as fSSneqSn.
	    intros fSninfSSn; fold N in fSSneqSn.
	    by exact (fSnniSn (in_Eeq_trans_l fSSneqSn fSninfSSn)).*)
Qed.

Lemma in_Nat_is_Nat : forall m n, n inE NatE -> m inE n -> m inE NatE.
Proof.
	intros m n nin; generalize dependent m; generalize dependent n; refine (induction_N _ _ _).
	by intros m mine; contradiction (empty_is_empty _ mine).
	intros n nin IHn m minSn.
	specialize (in_succ_in_eq minSn) as [minn | meqn].
	by exact (IHn _ minn).
	by exact (Eeq_in_trans_r meqn nin).
Qed.
Lemma Succ_in_Nat : forall m n, n inE NatE -> Succ m inE n -> m inE n.
Proof.
	intros m n nin; generalize dependent m; generalize dependent n; refine (induction_N _ _ _).
	by intros m Smine; contradiction (empty_is_empty _ Smine).
	intros n nin IHn m SminSn.
	specialize (in_succ_in_eq SminSn) as [Sminn | Smeqn].
	by exact (e_incl_succ _ _ (IHn _ Sminn)).
	by exact (e_incl_succ _ _ (in_Eeq_trans_l Smeqn (e_in_succ m))).
Qed.
Lemma n_ni_n : forall n, n inE NatE -> n not_in n.
Proof.
	apply induction_N.
	by exact (empty_is_empty _).
	intros n nin IHn SninSn.
	specialize (in_succ_in_eq SninSn) as [Sninn | Sneqn].
	by exact (IHn (Succ_in_Nat _ _ nin Sninn)).
	by exact (IHn (in_Eeq_trans_l Sneqn (Eeq_in_trans_l Sneqn SninSn))).
Qed.
Lemma in_Nat_trans : forall a b c, a inE b -> b inE c -> c inE NatE -> a inE c.
Proof.
	intros a b c ain bin cin; remember (in_Nat_is_Nat _ _ cin bin) as tmp eqn:eqtmp; clear eqtmp;
	  generalize dependent c; generalize dependent a; generalize dependent b; refine (induction_N _ _ _).
	by intros a ain; contradiction (empty_is_empty _ ain).
	intros b bin IHb a ain c binc cin.
	specialize (in_succ_in_eq ain) as [ainb|aeqb].
	by exact (IHb a ainb c (Succ_in_Nat _ _ cin binc) cin).
	by exact (Eeq_in_trans_r aeqb (Succ_in_Nat _ _ cin binc)).
Qed.
Lemma succ_inj : forall m n, m inE NatE -> n inE NatE -> Succ m =E Succ n -> m =E n.
Proof.
	intros m n min nin SmeqSn.
	specialize (in_Eeq_trans_l SmeqSn (e_in_succ m)) as minSn.
	specialize (in_succ_in_eq minSn) as [minn | meqn].
	specialize (in_Eeq_trans_l (Eeq_sym SmeqSn) (e_in_succ n)) as ninSm.
	specialize (in_succ_in_eq ninSm) as [ninm | neqm].
	by contradiction (n_ni_n _ nin (in_Nat_trans _ _ _ ninm minn nin)).
	by exact (Eeq_sym neqm). (* Or contradiction like above (m in n -> m in m) *)
	by exact meqn.
Qed.

Inductive nat :=
	| O : nat
	| S : nat -> nat.
Fixpoint N (n : nat) : Ensemble := match n with O => EmptySet | S n => Succ (N n) end.
Definition Nnat : Ensemble := ens nat N.
Lemma nat_Nat : Nnat =E NatE.
Proof.
	unfold Nnat, NatE; destruct infinity_axiom as [[NE fNE] [[[w einNatE] SuccinNatE] NP]] eqn:eqNE; split.
	intros n; induction n as [|n [y IHn]].
	exists w; exact einNatE.
	by exact (SuccinNatE _ (Eeq_in_trans_r (c:=ens NE fNE) IHn (application_in _ _ _))).
	intros y; remember (application_in NE fNE y) as tmp eqn:eqntmp; clear eqntmp;
	  remember (fNE y) as fy eqn:eqtmp; clear y eqtmp.
	assert (tmp2 : ens NE fNE = NatE) by (unfold NatE; rewrite eqNE; exact (eq_refl _)).
	rewrite tmp2 in *; clear tmp2.
	generalize dependent fy; apply induction_N.
	exists O; exact (Eeq_refl _).
	intros n nin [k eqk]; exists (S k).
	by exact (succ_inj _ _ (Succ_in_NatE _ (Eeq_in_trans_r eqk nin))
		(Succ_in_NatE _ nin) (Eeq_is_Eeq_succ (Eeq_is_Eeq_succ eqk))).
Qed.

Fixpoint parity {A : Type} (n : nat) (even odd : A) := match n with
	| O => even | S O => odd
	| S (S n') => parity n' even odd end.
Fixpoint parity' {A : Type} (n : nat) (even odd : A) := match n with
	| O => even
	| S n' => parity' n' odd even end.
Lemma parity_is_parity' {A : Type} : forall (n : nat) (even odd : A),
  parity n even odd = parity' n even odd.
Proof.
	intros n even odd; generalize dependent n; apply double_induction.
	by exact (eq_refl _).
	by exact (eq_refl _).
	by intros n IHn _; exact IHn.
Qed.
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

Lemma succ_inj : forall m n : nat, Succ (N m) =E Succ (N n) -> N m =E N n.
Proof.
	intros m n SmeqSn.
	specialize (in_Eeq_trans_l SmeqSn (n_in_Sn m)) as minSn.
	specialize (pair_union_is_union minSn) as [minn | minsn].
	specialize (in_Eeq_trans_l (Eeq_sym SmeqSn) (n_in_Sn n)) as ninSm.
	specialize (pair_union_is_union ninSm) as [ninm | ninsm].
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
	
	by apply Eeq_sym; apply singleton_is_singleton in ninsm; exact ninsm.
	by                apply singleton_is_singleton in minsn; exact minsn.
Qed.
Arguments succ_inj {m n} SNmeqSNn.

Lemma N_inj : forall m n : nat, N m =E N n -> m = n.
Proof.
	intros m; induction m as [|m IHm].
	- intros [|n] NOeqNn.
	  + by exact (eq_refl _).
	  + exfalso.
	    specialize (n_in_Sn n) as ninSn.
	    apply (in_Eeq_trans_r NOeqNn) in ninSn.
	    by exact (empty_is_empty _ ninSn).
	- intros [|n] NmeqNn.
	  + exfalso.
	    specialize (n_in_Sn m) as minSm.
	    apply (in_Eeq_trans_l NmeqNn) in minSm.
	    by exact (empty_is_empty _ minSm).
	  + by exact (f_equal _ (IHm _ (succ_inj NmeqNn))).
Qed.
Arguments N_inj {m n} NmeqNn.

Lemma NaddN_normal_l : forall n a b : nat, N (addN n a) =E N (addN n b) -> N a =E N b.
Proof.
	intros n; induction n as [|n IHn]; intros a b npaeqnpb.
	by exact npaeqnpb.
	by exact (IHn _ _ (succ_inj npaeqnpb)).
Qed.
Lemma NaddN_normal_r : forall n a b : nat, N (addN a n) =E N (addN b n) -> N a =E N b.
Proof.
	by intros n a b apneqbpn; rewrite (addNC a _), (addNC b _) in apneqbpn;
	  exact (NaddN_normal_l _ _ _ apneqbpn).
Qed.
Lemma NaddN_normal_lr : forall n a b : nat, N (addN n a) =E N (addN b n) -> N a =E N b.
Proof.
	by intros n a b apneqbpn; rewrite (addNC b _) in apneqbpn;
	  exact (NaddN_normal_l _ _ _ apneqbpn).
Qed.
Lemma NaddN_normal_rl : forall n a b : nat, N (addN a n) =E N (addN n b) -> N a =E N b.
Proof.
	by intros n a b apneqbpn; rewrite (addNC a _) in apneqbpn;
	  exact (NaddN_normal_l _ _ _ apneqbpn).
Qed.
Lemma addN_normal_l : forall n a b : nat, addN n a = addN n b -> a = b.
Proof.
	intros n; induction n as [|n IHn]; intros a b npaeqnpb.
	by exact npaeqnpb.
	minimize addN in npaeqnpb; injection npaeqnpb as npaeqnpb.
	by exact (IHn _ _ npaeqnpb).
Qed.
Lemma addN_normal_r : forall n a b : nat, addN a n = addN b n -> a = b.
Proof.
	by intros n a b apneqbpn; rewrite (addNC a _), (addNC b _) in apneqbpn;
	  exact (addN_normal_l _ _ _ apneqbpn).
Qed.
Lemma addN_normal_lr : forall n a b : nat, addN n a = addN b n -> a = b.
Proof.
	by intros n a b apneqbpn; rewrite (addNC b _) in apneqbpn;
	  exact (addN_normal_l _ _ _ apneqbpn).
Qed.
Lemma addN_normal_rl : forall n a b : nat, addN a n = addN n b -> a = b.
Proof.
	by intros n a b apneqbpn; rewrite (addNC a _) in apneqbpn;
	  exact (addN_normal_l _ _ _ apneqbpn).
Qed.
Arguments addN_normal_l {n a b} equality.
Arguments addN_normal_r {n a b} equality.
Arguments addN_normal_lr {n a b} equality.
Arguments addN_normal_rl {n a b} equality.
Arguments NaddN_normal_l {n a b} equality.
Arguments NaddN_normal_r {n a b} equality.
Arguments NaddN_normal_lr {n a b} equality.
Arguments NaddN_normal_rl {n a b} equality.

Definition LessEqual_existN (m n : nat) := exists p : nat, addN p m = n.
Lemma leeN_O_n : forall n : nat, LessEqual_existN O n.
Proof.
	by intros n; exists n; rewrite addNC; exact (eq_refl _).
Qed.
Lemma leeN_refl : forall n : nat, LessEqual_existN n n.
Proof.
	by intros ?; exists O; exact (eq_refl _).
Qed.
Lemma leeN_trans : forall m n p : nat, LessEqual_existN m n -> LessEqual_existN n p -> LessEqual_existN m p.
Proof.
	intros m n p [mn mlen] [np nlep].
	exists (addN np mn).
	by rewrite addNA, mlen; exact nlep.
Qed.
Lemma leeN_sym : forall m n : nat, LessEqual_existN m n -> LessEqual_existN n m -> m = n.
Proof.
	intros m n [mn mlen] [nm nlem].
	destruct mn as [|mn].
	by exact mlen.
	exfalso; rewrite <-mlen, <-addNA, add_m_Sn in nlem; clear n mlen; symmetry in nlem.
	generalize dependent (addN nm mn); clear mn nm; intros n npmeqm.
	induction m as [|m IHm].
	by discriminate npmeqm.
	by rewrite add_m_Sn in npmeqm; injection npmeqm as npmeqm; exact (IHm npmeqm).
Qed.

Lemma leeN_compat_plus : forall m n p : nat, LessEqual_existN (addN m p) (addN n p) -> LessEqual_existN m n.
Proof.
	intros m n p [mpnp mplenp].
	exists mpnp.
	rewrite <-addNA in mplenp.
	by exact (addN_normal_r mplenp).
Qed.

Lemma leeN_Sm_Sn_m_n : forall m n : nat, LessEqual_existN (S m) (S n) -> LessEqual_existN m n.
Proof.
	intros m n [mn mlen].
	exists mn.
	rewrite add_m_Sn in mlen; injection mlen as mlen.
	by exact mlen.
Qed.
Lemma leeN_iter : forall m n : nat, LessEqual_existN m n -> LessEqual_existN (S m) (S n).
Proof.
	intros m n [mn mlen].
	exists mn.
	rewrite add_m_Sn.
	by exact (f_equal S mlen).
Qed.

Lemma leeN_total : forall m n : nat, LessEqual_existN m n \/ LessEqual_existN n m.
Proof.
	intros m; induction m as [|m IHm].
	by intros n; left; exists n; rewrite addNC; exact (eq_refl _).
	intros [|n].
	by right; exact (leeN_O_n _).
	specialize (IHm n) as [mlen | nlem].
	by left;  exact (leeN_iter _ _ mlen).
	by right; exact (leeN_iter _ _ nlem).
Qed.

Example addN_less_individual_more : forall a b c d : nat,
 LessEqual_existN (addN a b) (addN c d) -> LessEqual_existN c a -> LessEqual_existN b d.
Proof.
	intros a b c d [abcd ablecd] [ca clea].
	exists (addN abcd ca).
	rewrite <-clea in ablecd; clear clea.
	rewrite (addNC ca _), (addNA c _ _), (addNC c _), <-(addNA _ _ c) in ablecd.
	apply addN_normal_rl in ablecd.
	rewrite <-addNA in ablecd.
	by exact ablecd.
Qed.

Lemma ltiN_is_in : forall m n : nat, LessThan_iterN m n -> N m inE N n.
Proof.
	intros m; induction m as [|m IHm].
	intros [|n] OltSn.
	by is_false (ge_is_not_lt_iterN _ _ (gei_oN _) OltSn).
	clear OltSn; induction n as [|n IHn].
	by exact (n_in_Sn _).
	by exact (e_incl_succ _ _ IHn).
	intros [|n] SmltSn.
	by is_false (ge_is_not_lt_iterN _ _ (gei_oN _) SmltSn).
	specialize (IHm _ (lt_iter_revN SmltSn)) as NminNn; clear IHm SmltSn.
	generalize dependent m; induction n as [|n IHn].
	by intros m NminNO; is_false (empty_is_empty _ NminNO).
	intros m NminNSn.
	specialize (pair_union_is_union NminNSn) as [NminNn | NminsNSn].
	by exact (e_incl_succ _ _ (IHn _ NminNn)).
	apply singleton_is_singleton in NminsNSn; fold N in NminsNSn.
	by rewrite (f_equal S (N_inj NminsNSn)); exact (n_in_Sn _).
Qed.
Lemma in_is_ltiN : forall m n : nat, N m inE N n -> LessThan_iterN m n.
Proof.
	intros m n; generalize dependent m; induction n as [|n IHn].
	intros ? minO.
	by is_false (empty_is_empty _ minO).
	intros m minSn.
	specialize (pair_union_is_union minSn) as [minn | minsn].
	by exact (lt_iter_nextN (IHn _ minn)).
	by apply singleton_is_singleton, N_inj in minsn; rewrite minsn; exact (n_lt_Sn _).
Qed.
Arguments ltiN_is_in {m n} mltn.
Arguments in_is_ltiN {m n} minn.

Lemma leeN_is_incl : forall m n : nat, LessEqual_existN m n -> (N m) incl (N n).
Proof.
	intros m n [mn mlen].
	rewrite <-mlen; clear n mlen; induction mn as [|mn IHmn].
	by unfold addN; exact (incl_refl _).
	intros x xinm.
	specialize (IHmn _ xinm) as xinmnpm.
	by exact (e_incl_succ _ _ xinmnpm).
Qed.
Lemma incl_is_leeN : forall m n : nat, (N m) incl (N n) -> LessEqual_existN m n.
Proof.
	intros m n mincln; generalize dependent m; induction n as [|n IHn]; intros m mincln.
	- specialize (classic (N m =E N O)) as [meqO | mneO].
	  by rewrite (N_inj meqO); exact (leeN_refl _).
	  specialize (non_empty_is_not_empty _ mneO) as [x xinm].
	  specialize (mincln _ xinm) as xine.
	  by is_false (empty_is_empty _ xine).
	- destruct m as [|m].
	  by exact (leeN_O_n _).
	  refine (leeN_iter _ _ (IHn m _)).
	  clear IHn; intros x xinm.
	  specialize (mincln _ (e_incl_succ _ _ xinm)) as xinSn.
	  specialize (pair_union_is_union xinSn) as [xinn | xinsn]; clear xinSn.
	  by exact xinn.
	  apply singleton_is_singleton in xinsn; fold N in xinsn.
	  exfalso; apply (Eeq_in_trans_l xinsn) in xinm; clear x xinsn.
	  specialize (mincln _ (ltiN_is_in (lti_iterN (in_is_ltiN xinm)))) as SninSn; clear xinm mincln.
	  specialize (proj2 (natural_longest_string_n n) (fun _ => N (S n)))
	    as [[_ [_ NSnniNSn]] | NSnniNSn]; by exact (NSnniNSn SninSn).
Qed.
Arguments leeN_is_incl {m n} mlen.
Arguments incl_is_leeN {m n} mincln.

Lemma leeN_is_in_eq : forall m n : nat, LessEqual_existN m n -> (N m inE N n) \/ (m = n).
Proof.
	intros m n [mn mlen]; generalize dependent mlen; generalize dependent n;
	  generalize dependent m; induction mn as [|mn IHmn].
	by intros ? ? mlen; right; exact mlen.
	intros m [|n] mlen.
	by minimize addN in mlen; discriminate mlen.
	injection mlen as mlen; specialize (IHmn _ _ mlen) as [minn | meqn]; left.
	by exact (e_incl_succ _ _ minn).
	by rewrite meqn; exact (n_in_Sn _).
Qed.
Lemma lti_is_leeN : forall m n : nat, LessThan_iterN m n -> LessEqual_existN m n.
Proof.
	intros m n; generalize dependent m; induction n as [|n IHn]; intros [|m] mltSSn.
	1,3: by exact (leeN_O_n _).
	by is_false (ge_is_not_lt_iterN _ _ (gei_oN _) mltSSn).
	by exact (leeN_iter _ _ (IHn _ (lt_iter_revN mltSSn))).
Qed.

Example all_nonempty_N_is_minored : forall a : Ensemble,
  a incl Nnat -> a <>E EmptySet -> exists n : nat, (N n inE a)
    /\ (forall y : Ensemble, y inE a -> N n incl y).
Proof.
	intros a ainclN anee.
	assert (strong_induction : forall n : nat,
	  (exists k : nat, LessEqual_existN k n /\ N k inE a) ->
	   (exists k : nat, N k inE a /\ (forall y : _, y inE a -> N k incl y))).
	{ intros n; induction n as [|n IHn].
	  - intros [[|k] [[kO kleO] kina]].
	    + clear kO kleO; exists O; split.
	      by exact kina.
	      intros y yina.
	      specialize (ainclN _ yina) as [z yinNbyz]; apply (incl_Eeq_trans_r yinNbyz); clear.
	      by exact (leeN_is_incl (leeN_O_n _)).
	    + by rewrite add_m_Sn in kleO; discriminate kleO.
	  - intros [k [[kn klen] kina]].
	    specialize (classic (exists k, LessEqual_existN k n /\ N k inE a)) as [exkina | nexkina].
	    by exact (IHn exkina).
	    destruct kn as [|kn].
	    exists (S n); split; clear IHn anee.
	    by unfold addN in klen; rewrite klen in kina; exact kina.
	    intros y yina.
	    specialize (ainclN _ yina) as [m yeqm];
	      apply (incl_Eeq_trans_r yeqm); apply (Eeq_in_trans_l yeqm) in yina; clear y yeqm.
	    specialize (not_and_or _ _
	      (not_ex_all_not _ (fun k => LessEqual_existN k n /\ N k inE a) nexkina m))
	      as [mgtn | mnia].
	    assert (Snlem : LessEqual_existN (S n) m).
	    { specialize (leeN_total n m) as [[[|nm] nlem] | mlen].
	      by unfold addN in nlem; rewrite nlem in mgtn; is_false (mgtn (leeN_refl _)).
	      by exists nm; rewrite add_m_Sn; exact nlem.
	      by is_false (mgtn mlen). }
	    by exact (leeN_is_incl Snlem).
	    by is_false (mnia yina).
	    
	    exfalso; rewrite add_Sm_n in klen; injection klen as klen.
	    specialize (not_and_or _ _
	      (not_ex_all_not _ (fun k => LessEqual_existN k n /\ N k inE a) nexkina k))
	      as [kgtn | knia].
	    by exact (kgtn (ex_intro _ _ klen)).
	    by exact (knia kina). }
	specialize (non_empty_is_not_empty _ anee) as [x xina].
	destruct (ainclN _ xina) as [n xinNbyn]; apply (Eeq_in_trans_l xinNbyn) in xina; clear x xinNbyn.
	by exact (strong_induction _ (ex_intro _ _ (conj (leeN_refl _) xina))).
Qed.
Example all_nonempty_majored_maximum : forall a : Ensemble,
  a incl Nnat -> a <>E EmptySet -> (exists n : nat, (forall k : _, k inE a -> k incl N n))
    -> exists n : nat, (N n inE a) /\ (forall y : Ensemble, y inE a -> y incl N n).
Proof.
	intros a ainclN anee [M amajbyM].
	induction M as [|M IHM].
	exists O; split.
	specialize (non_empty_is_not_empty _ anee) as [x xina].
	destruct (ainclN _ xina) as [n xinNbyn]; apply (Eeq_in_trans_l xinNbyn) in xina; clear x xinNbyn.
	specialize (amajbyM _ xina).
	specialize (classic (N n =E N O)) as [neqO | nneO].
	by apply (Eeq_in_trans_l neqO) in xina; exact xina.
	specialize (non_empty_is_not_empty _ nneO) as [x xinn].
	by is_false (empty_is_empty _ (amajbyM _ xinn)).
	by exact amajbyM.
	
	specialize (classic (N (S M) inE a)) as [SMina | SMnia].
	exists (S M); split.
	by exact SMina.
	intros y yina.
	destruct (ainclN _ yina) as [n yinNbyn]; apply (Eeq_incl_trans_r yinNbyn); apply (Eeq_in_trans_l yinNbyn) in yina; clear y yinNbyn.
	by exact (amajbyM _ yina).
	apply IHM.
	intros k kina.
	destruct (ainclN _ kina) as [n kinNbyn]; apply (Eeq_incl_trans_r kinNbyn); apply (Eeq_in_trans_l kinNbyn) in kina; clear k kinNbyn.
	specialize (incl_is_leeN (amajbyM _ kina)) as [[|nSM] nleSM].
	unfold addN in nleSM; rewrite nleSM in kina.
	by is_false (SMnia kina).
	injection nleSM as nleM.
	by exact (leeN_is_incl (ex_intro _ _ nleM)).
Qed.
Example N_not_maximized : forall n : nat, exists k : nat, N k not_incl N n.
Proof.
	intros n; exists (S n); apply not_incl_notincl; intros Snincln.
	apply incl_is_leeN in Snincln.
	assert (nleSn : LessEqual_existN n (S n)) by (exists (S O); exact (eq_refl _)).
	specialize (leeN_sym _ _ Snincln nleSn) as Sneqn.
	clear Snincln nleSn; induction n as [|n IHn]. (* Sigh... *)
	by discriminate Sneqn.
	by injection Sneqn as Sneqn; exact (IHn Sneqn).
Qed.

Fixpoint mulN (m n : nat) := match m with | O => O | S m' => addN (mulN m' n) n end.
Lemma mulNC : forall m n : nat, mulN m n = mulN n m.
Proof.
	intros m; induction m as [|m IHm]; intros n; induction n as [|n IHn].
	by exact (eq_refl _).
	by minimize mulN; rewrite <-IHn; exact (eq_refl _).
	by minimize mulN; rewrite   IHm; exact (eq_refl _).
	by minimize mulN; rewrite <-IHn, IHm; minimize mulN;
	  rewrite IHm, (addNA _ m _), (addNA _ n _), (addNC m (S n)), add_Sm_n, <-add_m_Sn;
	  exact (eq_refl _).
Qed.
Lemma mulN_Sm_n : forall m n : nat, mulN (S m) n = addN (mulN m n) n.
Proof. by intros; exact (eq_refl _). Qed.
Lemma mulN_m_Sn : forall m n : nat, mulN m (S n) = addN (mulN m n) m.
Proof.
	by intros; rewrite (mulNC _ (S _)), mulN_Sm_n;
	  exact (f_equal (fun k => addN k _) (mulNC _ _)).
Qed.
Lemma mulN_add_distr_l : forall m n p : nat, mulN (addN m n) p = addN (mulN m p) (mulN n p).
Proof.
	intros m; induction m as [|m IHm]; intros n p.
	by exact (eq_refl _).
	rewrite add_Sm_n, mulN_Sm_n, mulN_Sm_n, IHm, (addNA _ _ p), (addNC (mulN n _) p), <-addNA.
	by exact (eq_refl _).
Qed.
Lemma mulNA : forall m n p : nat, mulN (mulN m n) p = mulN m (mulN n p).
Proof.
	intros m; induction m as [|m IHm]; intros n p.
	by exact (eq_refl _).
	by rewrite mulN_Sm_n, mulN_add_distr_l, IHm; exact (eq_refl _).
Qed.
Corollary mulN_O_n : forall n : nat, mulN O n = O.
Proof. by intros; exact (eq_refl _). Qed.
Corollary mulN_n_O : forall n : nat, mulN n O = O.
Proof. by intros; rewrite mulNC; exact (eq_refl _). Qed.
Corollary mulN_SO_n : forall n : nat, mulN (S O) n = n.
Proof. by intros; exact (eq_refl _). Qed.
Corollary mulN_n_SO : forall n : nat, mulN n (S O) = n.
Proof. by intros; rewrite mulNC; exact (eq_refl _). Qed.

Lemma add_eq_O_l : forall m n : nat, addN m n = O -> m = O.
Proof.
	intros m; induction m as [|m IHm]; intros n cond.
	by exact (eq_refl _).
	by discriminate cond.
Qed.
Lemma add_eq_O_r : forall m n : nat, addN m n = O -> n = O.
Proof.
	by intros m n cond; rewrite addNC in cond; exact (add_eq_O_l _ _ cond).
Qed.

Lemma leeN_is_leeN_mulN : forall m n p : nat, LessEqual_existN m n -> LessEqual_existN (mulN m p) (mulN n p).
Proof.
	intros m n p [mn mlen]; exists (mulN mn p).
	by rewrite <-mlen, mulN_add_distr_l; exact (eq_refl _).
Qed.
Lemma leeN_mulN_is_leeN_l : forall n a b : nat, n <> O -> LessEqual_existN (mulN n a) (mulN n b) -> LessEqual_existN a b.
Proof.
	intros [|n] a b nneO nalenb.
	by is_false (nneO (eq_refl _)).
	clear nneO; generalize dependent nalenb; generalize dependent b;
	  generalize dependent a; induction n as [|n IHn]; intros a b nalenb.
	by exact nalenb.
	specialize (leeN_total a b) as [aleb | blea].
	by exact aleb.
	rewrite (mulN_Sm_n (S n) _), (mulN_Sm_n (S n) _), (addNC _ a), (addNC _ b) in nalenb.
	by exact (IHn _ _ (addN_less_individual_more _ _ _ _ nalenb blea)).
Qed.
Lemma leeN_mulN_is_leeN_r : forall n a b : nat, n <> O -> LessEqual_existN (mulN a n) (mulN b n) -> LessEqual_existN a b.
Proof.
	intros n a b nneO nalenb; rewrite (mulNC _ n), (mulNC _ n) in nalenb.
	generalize dependent nalenb; generalize dependent nneO;
	  generalize dependent b; generalize dependent a; generalize dependent n.
	by exact leeN_mulN_is_leeN_l.
Qed.
Corollary eq_mulN_is_eq_l : forall n a b : nat, n <> O -> (mulN n a) = (mulN n b) -> a = b.
Proof.
	intros n a b nneO naeqnb; apply leeN_sym.
	specialize (leeN_refl (mulN n b)) as tmp; rewrite <-naeqnb in tmp at 1; clear naeqnb.
	generalize dependent tmp; generalize dependent nneO; generalize dependent b;
	  generalize dependent a; generalize dependent n; exact leeN_mulN_is_leeN_l.
	specialize (leeN_refl (mulN n a)) as tmp; rewrite naeqnb in tmp at 1; clear naeqnb.
	generalize dependent tmp; generalize dependent nneO; generalize dependent a;
	  generalize dependent b; generalize dependent n; exact leeN_mulN_is_leeN_l.
Qed.
Corollary eq_mulN_is_eq_r : forall n a b : nat, n <> O -> (mulN a n) = (mulN b n) -> a = b.
Proof.
	by intros n a b nneO aneqbn; rewrite (mulNC _ n), (mulNC _ n) in aneqbn;
	  exact (eq_mulN_is_eq_l n _ _ nneO aneqbn).
Qed.
End NatNums.

Definition two_tuple A B := {E{A} ; E{A ; B}}E.
Notation "E( A , B )" := (two_tuple A B) (at level 69, no associativity, only parsing).
Notation "( A ,  B )" := (two_tuple A B) (at level 69, no associativity, only printing).
Lemma two_tuple_antisym : forall A B : Ensemble, E(A, B) =E E(B, A) -> A =E B.
Proof.
	intros A B ABeqBA.
	specialize (pairing_trans_r _ _ (E{B}) (pairing_sym A B)) as B_ABeqB_BA.
	unfold two_tuple in ABeqBA;
	  specialize (pairing_inj (Eeq_trans ABeqBA (Eeq_sym B_ABeqB_BA))) as sAeqsB.
	by exact (singleton_inj sAeqsB).
Qed.
Lemma two_tuple_eq_l : forall A B C : Ensemble, A =E B -> E(A, C) =E E(B, C).
Proof.
	intros A B C AeqB.
	specialize (singleton_refl AeqB) as sAeqsB.
	specialize (pairing_trans_l _ _ C AeqB) as ACeqBC.
	by exact (pairing_trans sAeqsB ACeqBC).
Qed.
Lemma two_tuple_eq_r : forall A B C : Ensemble, B =E C -> E(A, B) =E E(A, C).
Proof.
	intros A B C BeqC.
	specialize (singleton_refl (Eeq_refl A)) as sAeqsA.
	specialize (pairing_trans_r _ _ A BeqC) as ABeqAC.
	by exact (pairing_trans sAeqsA ABeqAC).
Qed.
Lemma two_tuple_eq : forall A B C D : Ensemble, A =E C -> B =E D -> E(A, B) =E E(C, D).
Proof.
	intros A B C D AeqC BeqD.
	specialize (singleton_refl AeqC) as sAeqsC.
	specialize (pairing_trans AeqC BeqD) as ABeqCD.
	by exact (pairing_trans sAeqsC ABeqCD).
Qed.
Lemma two_tuple_inj_l : forall A B C : Ensemble, E(A, C) =E E(B, C) -> A =E B.
Proof.
	intros A B C pACeqpBC.
	specialize (pairing_is_lr (Eeq_incl_l pACeqpBC _
	    (l_in_pairing _ _))) as [sAeqsB | sAeqBC].
	by exact (singleton_inj sAeqsB).
	by exact (Eeq_sym
	  (singleton_is_singleton (in_Eeq_trans_r sAeqBC (l_in_pairing B C)))).
Qed.
Lemma two_tuple_inj_r : forall A B C : Ensemble, E(A, B) =E E(A, C) -> B =E C.
Proof.
	intros A B C pACeqpBC.
	specialize (pairing_is_lr (Eeq_incl_r pACeqpBC _
	    (r_in_pairing _ _))) as [ACeqsA | sAeqBC].
	specialize (pairing_inj (Eeq_trans (pairing_sym _ _) ACeqsA)) as CeqA.
	specialize (pairing_is_lr (Eeq_incl_l pACeqpBC _
	    (r_in_pairing _ _))) as [ABeqsA | ABeqAC].
	specialize (pairing_inj (Eeq_trans (pairing_sym _ _) ABeqsA)) as BeqA.
	by exact (Eeq_trans BeqA (Eeq_sym CeqA)).
	by exact (pairing_inj
	  (Eeq_trans (Eeq_trans (pairing_sym _ _) ABeqAC) (pairing_sym _ _))).
	by exact (Eeq_sym (pairing_inj
	  (Eeq_trans (Eeq_trans (pairing_sym _ _) sAeqBC) (pairing_sym _ _)))).
Qed.
Arguments two_tuple_antisym {A B} ABeqBA.
Arguments two_tuple_eq {A B C D} AeqC BeqD.

Definition power_set_cons (A : Ensemble) : Ensemble := let (A', f) := A in
	ens (A' -> Prop) (fun P => ens { x : A' | P (x) } (fun k => let (v, _) := k in f v)).
Notation "'Pe' ( A )" := (power_set_cons A) (only printing).
Lemma power_set_is_powset : forall A : Ensemble,
	forall B : Ensemble, B inE (power_set_cons A) -> B incl A.
Proof.
	intros [A f] B [c BinPAbyc] x xinB.
	specialize (Eeq_incl_l BinPAbyc _ xinB) as [[y _] xinPSetbyy].
	by exists y; exact xinPSetbyy.
Qed.
Lemma powset_is_power_set : forall A : Ensemble,
	forall B : Ensemble, B incl A -> B inE (power_set_cons A).
Proof.
	intros [A f] B BinclA.
	exists (fun v => f v inE B).
	apply incl_antisym.
	intros x xinB.
	specialize (BinclA _ xinB) as [y xinAbyy].
	rewrite (ens_pi_is_orig B); rewrite (ens_pi_is_orig B) in xinB.
	destruct xinB as [z xinBbyz].
	specialize (Eeq_trans (Eeq_sym xinAbyy) xinBbyz) as fyeqgz.
	exists (exist _ _ (ex_intro _ z fyeqgz)).
	by exact xinAbyy.
	intros x [[y Hy] xinPAbyy].
	by exact (Eeq_in_trans_r xinPAbyy Hy).
Qed.
Lemma power_set_incl : forall A B : Ensemble,
	A incl B -> power_set_cons A incl power_set_cons B.
Proof.
	intros [A f] [B g] AinclB x [P xinPAbyP].
	exists (fun b => g b inE x).
	rewrite (ens_pi_is_orig x); rewrite (ens_pi_is_orig x) in xinPAbyP;
	  destruct xinPAbyP as [xinclPA PAinclx]; split.
	intros y.
	specialize (xinclPA y) as [[z Pz] yeqfz].
	specialize (AinclB _ (application_in _ _ z)) as [k fzeqgk].
	specialize (Eeq_in_trans_l
	  (Eeq_trans yeqfz fzeqgk) (application_in (pi1e x) (pi2e x) y)) as gkinx.
	exists (exist _ k gkinx).
	by exact (Eeq_trans yeqfz fzeqgk).
	intros [y [z yinxbyz]].
	by exists z; exact (Eeq_sym yinxbyz).
Qed.
Lemma power_set_trans : forall A B : Ensemble,
	A =E B -> (power_set_cons A) =E (power_set_cons B).
Proof.
	intros A B AeqB; apply incl_antisym.
	by specialize (Eeq_incl_l AeqB) as AinclB; exact (power_set_incl _ _ AinclB).
	by specialize (Eeq_incl_r AeqB) as BinclA; exact (power_set_incl _ _ BinclA).
Qed.
Arguments power_set_incl {A B} AinclB.
Arguments power_set_trans {A B} AinclB.

Definition cartesian (A B : Ensemble) :=
	{ x in power_set_cons ((power_set_cons A) \union (power_set_cons (A \union B))) |
	  exists a b : Ensemble, ((a inE A) /\ (b inE B)) /\ (x =E E(a, b))}E.
Lemma cartesian_is_product : forall A B : Ensemble,
	forall C : Ensemble, C inE cartesian A B ->
	 exists a b : Ensemble, ((a inE A) /\ (b inE B)) /\ (C =E E(a, b)).
Proof.
	intros A B C [[x [a [b [[ainA binB] xeqab]]]] Ceqx].
	exists a, b; split; [split|].
	by exact ainA.
	by exact binB.
	by exact (Eeq_trans Ceqx xeqab).
Qed.
Lemma product_is_cartesian : forall A B : Ensemble,
	forall a b : Ensemble, a inE A -> b inE B -> E(a, b) inE cartesian A B.
Proof.
	intros A B a b ainA binB.
	apply separation_cons_separates.
	specialize (in_is_singleton_incl ainA) as sainclA; clear ainA.
	specialize (in_is_singleton_incl binB) as sbinclB; clear binB.
	specialize (incl_trans sainclA (pair_union_is_union_l A B)) as sainclAB.
	specialize (incl_trans sbinclB (pair_union_is_union_r A B)) as sbinclAB; clear sbinclB.
	specialize (incl_incl_is_union_incl sainclAB sbinclAB) as sausbinclAB; clear sainclAB sbinclAB.
	specialize (singleton_union_singleton a b) as sausbeqab.
	specialize (Eeq_incl_trans_l sausbeqab sausbinclAB) as abinclAB; clear sausbeqab sausbinclAB.
	specialize (powset_is_power_set _ _ abinclAB) as abinPAB; clear abinclAB.
	specialize (in_is_singleton_incl abinPAB) as sabinclPAB; clear abinPAB.
	specialize (incl_trans sabinclPAB (pair_union_is_union_r (power_set_cons A) _)) as sabinclAPAB; clear sabinclPAB.
	specialize (powset_is_power_set _ _ sainclA) as sainPA; clear sainclA.
	specialize (in_is_singleton_incl sainPA) as ssainclPA; clear sainPA.
	specialize (incl_incl_is_union_incl
	  (incl_trans ssainclPA (pair_union_is_union_l _ _))
	  sabinclAPAB) as ssausabinclAPAB; clear ssainclPA sabinclAPAB.
	specialize (Eeq_incl_trans_l (singleton_union_singleton _ _) ssausabinclAPAB) as sapabinclAPAB; clear ssausabinclAPAB.
	by exact (powset_is_power_set _ _ sapabinclAPAB).
	
	exists a, b; split; [split|].
	by exact ainA.
	by exact binB.
	by exact (Eeq_refl _).
Qed.

Definition is_partial_application (f A B : Ensemble) : Prop :=
	(f incl cartesian A B) /\
	forall p, p inE f ->
	 forall x y x' y', x =E x' -> E(x, y) inE f -> E(x', y') inE f -> y =E y'.
Definition is_total_application (f A B : Ensemble) : Prop :=
	(is_partial_application f A B) /\ forall y, y inE B -> exists x,
	 x inE A /\ E(x, y) inE f.
