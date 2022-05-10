Require Import base.

Lemma swap_hyps {P Q R : Prop} : (P -> Q -> R) -> Q -> P -> R.
Proof. by intros PQR pQ pP; exact (PQR pP pQ). Qed.

Lemma hypothetical_syllogism : forall P Q R : Prop, (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
	by intros P Q R PQ QR pP; exact (QR (PQ pP)).
Qed.

Lemma if_never_then_not_exist {T : Type} (P : T -> Prop)
 : (forall n : T, ~ (P n)) -> ~ (exists n : T, P n).
Proof.
	by intros H [n Pn]; exact (H n Pn).
Qed.
Lemma if_exist_then_exists {T : Type} (P : T -> Prop)
 : forall n : T, P n -> (exists n : T, P n).
Proof.
	by intros n Pn; exists n; exact Pn.
Qed.
Lemma if_not_exists_then_never {T : Type} (P : T -> Prop)
 : (forall n : T, P n \/ ~ P n) -> ~ (exists n : T, P n) -> (forall n : T, ~ P n).
Proof.
	intros middle_excluded nex n.
	destruct (middle_excluded n) as [Pn | nPn].
	by is_false (nex (if_exist_then_exists _ _ Pn)).
	by exact nPn.
Qed.
Lemma if_not_never_then_dont_not_exists {T : Type} (P : T -> Prop)
 : ~ (forall n : T, ~ P n) -> ~ ~ (exists n : T, P n).
Proof.
	intros nnever nexn.
	contradict nnever.
	by intros n Pn; exact (nexn (if_exist_then_exists _ n Pn)).
Qed.
Lemma if_not_exists_then_not_never_false {T : Type} (P : T -> Prop)
 : ~ (exists n : T, P n) -> ~ ~ (forall n : T, ~ P n).
Proof.
	intros nex nalnot.
	by exact (if_not_never_then_dont_not_exists _ nalnot nex).
Qed.

Lemma transform_and_rarrow : forall A B C : Prop, (A /\ B -> C) -> A -> B -> C.
Proof.
	by intros A B C H pA pB; apply H; split; [exact pA | exact pB].
Qed.
Lemma transform_rarrow_and : forall A B C : Prop, (A -> B -> C) -> A /\ B -> C.
Proof.
	by intros A B C H [pA pB]; exact (H pA pB).
Qed.

(* Attempt no 3 at a wlog implementation, pt.1/2 *)
Lemma modus_ponens {P Q : Prop} : P -> (P -> Q) -> Q.
Proof.
	by intros pP PQ; exact (PQ pP).
Qed.
Lemma modus_tonens {P Q : Prop} : (~ Q) -> (P -> Q) -> ~ P.
Proof.
	by intros nQ PQ pP; exact (nQ (PQ pP)).
Qed.

Lemma double_negation_elimination {P : Prop} : (P \/ ~ P) -> ~ ~ P -> P.
Proof.
	by intros [pP | nP] nnP; [exact pP | exfalso; exact (nnP nP)].
Qed.
Lemma double_negation_introduction {P : Prop} : P -> ~ ~ P.
Proof.
	by intros pP nP; exact (nP pP).
Qed.

Lemma disjunctive_syllogism {P Q : Prop} : (P \/ Q) -> ~ P -> Q.
Proof.
	intros [pP | pQ] nP.
	by is_false (nP pP).
	by exact pQ.
Qed.

(* proj1 / proj2 *)
Lemma and_l {P Q : Prop} : (P /\ Q) -> P. Proof. by intros [pP _]; exact pP. Qed.
Lemma and_r {P Q : Prop} : (P /\ Q) -> Q. Proof. by intros [_ pQ]; exact pQ. Qed.

Lemma or_to_impl_l {P Q R : Prop} : (P -> Q) -> (P \/ R) -> (Q \/ R).
Proof.
	by intros PQ [pP | pR]; [left; apply PQ; exact pP | right; exact pR].
Qed.
Lemma or_to_impl_r {P Q R : Prop} : (P -> R) -> (Q \/ P) -> (Q \/ R).
Proof.
	by intros PR [pQ | pP]; [left; exact pQ | right; apply PR; exact pP].
Qed.
Lemma or_swap {P Q : Prop} : (P \/ Q) -> Q \/ P.
Proof. by intros [pP | pQ]; [right; exact pP | left; exact pQ]. Qed.

(* Attempt no 3 at a wlog implementation, pt.2/2 *)
Tactic Notation "without" "loss" ident(n) ":" constr(Q)
	:= lazymatch goal with
		| |- ?H => assert(n : Q)
		| _ => fail "Invalid usage of 'without loss'."
	end.
Tactic Notation "wlog" ident(n) ":" constr(Q)
	:= lazymatch goal with
		| |- ?H => assert(n : Q); swap 1 2
		| _ => fail "Invalid usage of 'wlog'."
	end.
