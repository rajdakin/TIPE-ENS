roottwo_is_irrational:

.SECONDEXPANSION:

bool.%: base.%
nat.%: base.% bool.%
roottwo_is_irrational.%: base.vos bool.vos nat.vos
base bool nat: $$@.vo
roottwo_is_irrational: $$@.vok
.PHONY: base bool nat roottwo_is_irrational
%.vo: %.v
	@coqc $^
z_theory_base.vo: z_theory_base.v base.vos
	@coqc -noinit $<
z_theory_bool.vo: z_theory_bool.v base.vos z_theory_base.vo
	@coqc -noinit $<
z_theory_N.vo: z_theory_N.v base.vos z_theory_base.vo
	@coqc -noinit $<
z_theory_group_theory.vo: z_theory_group_theory.v base.vos z_theory_base.vo z_theory_bool.vo
	@coqc -noinit $<
%.vok %.vos: %.vo
%.vok: %.v
	@coqc -vok $^
%.vos: %.v
	@coqc -vos $^
