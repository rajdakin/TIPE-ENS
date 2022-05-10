Require Import ZArith.
Require Import QArith.
Load funs.

Open Scope Q_scope.

Definition same_cardinality (A B : Type) :=
  exists f : A -> B, exists g : B -> A,
    (forall b : B, f (g b) = b) /\ (forall a : A, g (f a) = a).

Definition is_denumerable A := same_cardinality A nat.

Lemma same_card_is_two_injectives : forall A B : Type,
 (exists f : A -> B, injective f) ->
 (exists g : B -> A, injective g) -> same_cardinality A B.

Theorem Q_is_at_most_denumerable: exists f : Q -> nat, injective f.
Proof.
Qed.

Theorem Q_is_denumbrable: is_denumbrable Q.
Proof.
	destruct Q_is_at_most_denumerable as [f injf].
Qed.
