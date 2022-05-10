Require Import base.
Require Import bool.
Require Import Ensembles.

Definition injective {A B : Type} (f : A -> B) :=
	forall x1 x2 : A, f x1 = f x2 -> x1 = x2.
Definition surjective {A B : Type} (f : A -> B) :=
	forall y : B, exists x : A, f x = y.

Section countable_choice.
Axiom countable_choice_axiom 
 : forall U : Type, forall A : nat -> Ensemble U,
 (forall n : nat, exists x : U, In _ (A n) x) -> exists f : nat -> U, forall n : nat, In _ (A n) (f n).
End countable_choice.

Lemma surj_to_inj {A : Type}
 : forall f : A -> nat, surjective f -> exists g : nat -> A, injective g.
Proof.
	intros f surjf.
	pose (R := fun b a => f a = b).
	specialize (countable_choice_axiom _ R surjf) as [g Hg].
	exists g.
	intros n1 n2 g1eqg2.
	rewrite <-(Hg n1), <-(Hg n2).
	exact (f_equal f g1eqg2).
Qed.
