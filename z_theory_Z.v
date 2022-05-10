Require Import base.
Require Import z_theory_base.
Require Import z_theory_bool.
Require Import z_theory_N.
Require Import Classical.
Require Import Ltac.
Require Import Logic.
Require Import Specif.
Require Import Coq.Init.Tactics.

Section ZNums.
Definition Zset :=
	E{ p in cartesian Nnat Nnat | exists a b : _, (E(a, b) =E p) /\ ((a =E N O) \/ (b =E N O)) }.
Lemma Zminimize (v : Ensemble) (vin : v inE cartesian Nnat Nnat) :
	let (tmpm, tmp) := cartesian_is_product _ _ _ vin in
	let (tmpn, tmp2) := tmp in
	let (tmp3, veq) := tmp2 in
	let (minN, ninN) := tmp3 in
	let (m, _) := minN in
	let (n, _) := ninN in
	Eexists z in Zset, exists a b : _, (E(N a, N b) =E z) /\ (addN m b = addN n a).
	specialize (cartesian_is_product _ _ _ vin) as [m [n [[minN ninN] veq]]].
	unfold In, cartesian, separation_cons, Nnat, power_set_cons, pair_union_cons, pairing_cons, ens_union_cons in vin.
	Unset Printing Notations.
	destruct vin as [l r].
Definition Zadd l r :=

End ZNums.
