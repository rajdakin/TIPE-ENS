Require Import base.

(* Need(?) the -noinit flag *)

(* Inspired by https://github.com/coq-contribs/zfc/blob/master/zfc.v *)

Require Export Ltac.
Require Export Logic.
Require Export Specif.
(* Attempting to reason without classical logic is too hard (and useless) *)
Require Export Classical.

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
Notation "'Eforall' x 'in' E , P" := (forall x : Ensemble, x inE E -> P) (at level 200, no associativity, only parsing).
Notation "'Eexists' x 'in' E , P" := (exists x : Ensemble, (x inE E) /\ P) (at level 200, no associativity, only parsing).
Notation "'Eforall' x 'in' E 'as' v , P" := (forall x : Ensemble, forall v : x inE E, P) (at level 200, no associativity, only parsing).
Notation "'Eexists' x 'in' E 'as' v , P" := (exists x : Ensemble, exists v : x inE E, P) (at level 200, no associativity, only parsing).
Corollary application_in : forall A : _, forall f : _, forall x : A, f x inE (ens A f).
Proof. by intros A f x; exists x; exact (Eeq_refl _). Qed.
Notation "a 'not_in' b" := (~ (a inE b)) (at level 70, no associativity).
Definition Included (A B : Ensemble) : Prop :=
	Eforall e in A, (e inE B).
Infix "incl" := Included (at level 70, no associativity).
Definition NotIncluded (A B : Ensemble) : Prop :=
	Eexists e in A, ~(e inE B).
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
Axiom extensionality_axiom''
	: forall A B : Ensemble, forall f : Ensemble -> Ensemble, (A =E B) -> (f A) =E (f B).
Axiom pairing_axiom
	: forall A B : Ensemble, exists C : Ensemble, forall x : Ensemble,
	(x inE C) <-> ((x =E A) \/ (x =E B)).
Axiom union_axiom
	: forall A : Ensemble, exists C : Ensemble, forall x : Ensemble,
	(x inE C) <-> exists Y, (Y inE A) /\ (x inE Y).
Axiom power_set_axiom : forall A : Ensemble, exists C : Ensemble,
	forall X, (X inE C) <-> (X incl A).
Axiom empty_set_axiom : exists E : Ensemble, E = E.
Axiom schema_restricted_comprehension_axiom :
	forall (P : Ensemble -> Prop) (A : Ensemble),
	exists C : Ensemble, forall x,
	(x inE C) <-> ((x inE A) /\ (P x)).
Arguments extensionality_axiom' {A B} AeqB P PA.

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

Lemma ex_empty_set : exists E : Ensemble, forall x : Ensemble, ~ (x inE E).
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
Lemma separation_cons_separated : forall (A : Ensemble) (P : Ensemble -> Prop),
	Eforall x in E{x in A | P x}, P x.
Proof.
	intros [A f] P x [[y Pfy] xinsepbyy].
	by exact (extensionality_axiom' (Eeq_sym xinsepbyy) _ Pfy).
Qed.
Lemma separation_cons_separates : forall (A : Ensemble) (P : Ensemble -> Prop),
	Eforall x in A, P x -> (x inE E{x in A | P x}).
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
	:= ens_union_cons (E{A ; B}).

Infix "\union" := pair_union_cons (at level 50, left associativity).
Notation "'\Union' a" := (ens_union_cons a) (at level 69, no associativity).
Notation "a \\ b" := (separation_cons a (fun x => x not_in b)) (at level 69, no associativity).
Definition inter a b := separation_cons a (fun x => x inE b).
Infix "\inter" := inter (at level 50, left associativity).

Lemma ens_union_is_union : forall A : Ensemble,
	Eforall B in (\Union A), Eexists C in A, B inE C.
Proof.
	intros [A f] [B g] [[x y] BinCbyy].
	exists (f x); split.
	by exact (application_in _ _ _).
	rewrite (ens_pi_is_orig (f x)).
	by exists y; exact BinCbyy.
Qed.
Lemma union_is_ens_union : forall A : Ensemble,
	Eforall B in A, B incl (\Union A).
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

Lemma ens_inter_is_inter : forall A B : Ensemble,
	Eforall C in A \inter B, (C inE A) /\ (C inE B).
Proof.
	intros a b c cininter; split.
	by exact (separation_cons_included _ _ _ cininter).
	by exact (separation_cons_separated _ _ _ cininter).
Qed.
Lemma inter_is_ens_inter : forall A B : Ensemble,
	Eforall C in A, (C inE B) -> C inE (A \inter B).
Proof. by intros a b c; exact (separation_cons_separates _ _ _). Qed.
Lemma inter_sym : forall A B : Ensemble, A \inter B =E B \inter A.
Proof.
	intros a b; apply incl_antisym; intros x xininter; apply inter_is_ens_inter.
	1,3: by exact (proj2 (ens_inter_is_inter _ _ _ xininter)).
	1,2: by exact (proj1 (ens_inter_is_inter _ _ _ xininter)).
Qed.
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
Lemma pairing_is_lr : forall A B : Ensemble,
	Eforall C in E{A ; B}, C =E A \/ C =E B.
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
	A =E B -> E{C ; A} =E E{C ; B}.
Proof.
	intros A B C AeqB; apply incl_antisym.
	intros x xinCA.
	specialize (pairing_is_lr _ _ _ xinCA) as [xeqC | xeqA].
	by exact (Eeq_in_trans_r xeqC (l_in_pairing _ _)).
	by exact (Eeq_in_trans_r (Eeq_trans xeqA AeqB) (r_in_pairing _ _)).
	intros x xinCB.
	specialize (pairing_is_lr _ _ _ xinCB) as [xeqC | xeqB].
	by exact (Eeq_in_trans_r xeqC (l_in_pairing _ _)).
	by exact (Eeq_in_trans_r (Eeq_trans xeqB (Eeq_sym AeqB)) (r_in_pairing _ _)).
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
Lemma pair_union_is_union : forall A B : Ensemble,
	Eforall C in A \union B, C inE A \/ C inE B.
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
Lemma singleton_is_singleton : forall A : Ensemble, Eforall B in E{A}, B =E A.
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
	  (fun e => Eforall a in A, e inE a) a0) as [C HC].
	exists C; intros x; specialize (HC x) as [HCl HCr]; split; [clear HCr | clear HCl].
	by intros xiC; exact (proj2 (HCl xiC)).
	by intros H0; exact (HCr (conj (H0 _ a0inA) H0)).
Qed.

Definition Succ (A : Ensemble) := A \union (E{A}).
Definition is_nat (A : Ensemble) :=
	(EmptySet inE A) /\ Eforall x in A, ((Succ x) inE A).
Axiom infinity_axiom : exists N : Ensemble,
	(is_nat N) /\ (forall a, (is_nat a) -> N incl a).

Definition two_tuple A B := E{E{A} ; E{A ; B}}.
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
	Eforall B in power_set_cons A, B incl A.
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
	E{ x in power_set_cons ((power_set_cons A) \union (power_set_cons (A \union B))) |
	  exists a b : Ensemble, ((a inE A) /\ (b inE B)) /\ (x =E E(a, b))}.
Lemma cartesian_is_product : forall A B : Ensemble,
	Eforall C in cartesian A B,
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

Definition partial_application_set (A B : Ensemble) : Ensemble :=
	E{ f in cartesian A B |
	 forall x y x' y', x =E x' -> E(x, y) inE f -> E(x', y') inE f -> y =E y' }.
Definition total_application_set (A B : Ensemble) : Ensemble :=
	E{ f in partial_application_set A B |
	 Eforall x in A, Eexists y in B, E(x, y) inE f }.
Lemma total_incl_partial : forall A B : Ensemble,
	total_application_set A B incl partial_application_set A B.
Proof.
	by intros A B f [[witness _] fintotbywitness]; exists witness; exact fintotbywitness.
Qed.
Axiom partial_application_cons_ax :
  forall {A B : _} (f : _) (f_fun : f inE (partial_application_set A B)),
	{ g : forall x, (Eexists y in B, E(x, y) inE f) -> Ensemble |
	 forall x : _, forall xin : (Eexists y in B, E(x, y) inE f), E(x, g x xin) inE f }.
Lemma partial_application_image {A B : _} (f : _) (f_fun : f inE (partial_application_set A B))
 : forall (x : _) (xin : _), let (g, _) := partial_application_cons_ax f f_fun in g x xin inE B.
	intros x xin; destruct (partial_application_cons_ax f f_fun) as [g Pg].
	specialize (Pg x xin).
	destruct f_fun as [[f_carte f_fun] feq].
	destruct xin as [y [yinB xyinf]].
	specialize (f_fun
		x
		y
		x
		(g x (ex_intro (fun y => y inE B /\ E(x, y) inE f) y (conj yinB xyinf)))
		(Eeq_refl _)
		(in_Eeq_trans_l feq xyinf)
		(in_Eeq_trans_l feq Pg)).
	by exact (Eeq_in_trans_l f_fun yinB).
Qed.

Definition total_application_cons {A B} f (f_fun : f inE (total_application_set A B)) :
 { g : Eforall x in A, Ensemble | Eforall x in A as xin, E(x, g x xin) inE f }.
	assert (xin_g : Eforall x in A, Eexists y in B, E(x, y) inE f).
	{ intros x xin; destruct f_fun as [[? f_total] feqXX].
	  specialize (f_total x xin) as [y [yin Hy]].
	  exists y; split.
	  by exact yin.
	  by exact (in_Eeq_trans_r feqXX Hy). }
	specialize (partial_application_cons_ax f (total_incl_partial _ _ _ f_fun)) as [g Pg].
	pose (g' := fun x xin : _ => g x (xin_g x xin)).
	refine (exist _ g' _); intros x xin; unfold g'; clear g'.
	by exact (Pg _ _).
Defined.
Lemma total_application_image {A B : _} (f : _) (f_fun : f inE (total_application_set A B))
 : Eforall x in A as xin, let (g, _) := total_application_cons f f_fun in g x xin inE B.
Proof.
	intros x xin; destruct (total_application_cons f f_fun) as [g Pg].
	specialize (Pg x xin).
	destruct f_fun as [[[f_carte f_fun] f_total] feq].
	specialize (f_total x xin) as [y [yinB xyinf']].
	specialize (f_fun
		x
		y
		x
		(g x xin)
		(Eeq_refl _)
		xyinf'
		(in_Eeq_trans_l feq Pg)).
	by exact (Eeq_in_trans_l f_fun yinB).
Qed.
