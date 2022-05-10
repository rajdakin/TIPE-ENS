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
