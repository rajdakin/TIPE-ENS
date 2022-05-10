Require Import base.
Require Import bool.

(*** Induction helpers ***)

(*Set Mangle Names.
Set Mangle Names Prefix "Mangled".*)

Lemma inverted_induction_0 (P : nat -> Prop) (n0 : nat):
  (forall n : nat, P (S n) -> P n) -> (P n0) -> P 0.
Proof.
	intros H; induction n0 as [|n0 IHn0]; intros I.
	by exact I.
	by exact (IHn0 (H _ I)).
Qed.
Lemma inverted_induction_all (P : nat -> Prop) (n0 : nat):
  (forall n0 : nat, (forall n : nat, n >= (S n0) -> P n) -> P n0)
  -> (forall n : nat, n >= n0 -> P n) -> (forall n : nat, P n).
Proof.
	intros H; induction n0 as [|n0 IHn0]; intros I n.
	by exact (I n (le_0_n n)).
	apply IHn0.
	intros n1 [|n1' n0len1'].
	by exact (H _ I).
	by exact (I _ (le_n_S _ _ n0len1')).
Qed.
Lemma inverted_induction0_le (P : nat -> Prop) (n0 : nat):
  (forall n : nat, P (S n) -> P n)
  -> (P n0) -> (forall n : nat, n <= n0 -> P n).
Proof.
	intros H; induction n0 as [|n0 IHn0]; intros I n nlen0.
	remember 0 as z eqn:Hz.
	destruct nlen0 as [|prev0 _].
	by exact I.
	by discriminate Hz.
	remember (S n0) as Sn0 eqn:HSn0.
	destruct nlen0 as [|prevSn0 HpSn0].
	by exact I.
	apply eq_add_S in HSn0; rewrite HSn0 in I; rewrite HSn0 in HpSn0; clear prevSn0 HSn0.
	by exact (IHn0 (H _ I) _ HpSn0).
	(* Or, though some cases are removed here
	inversion nlen0; exact I; fail "inversion became weaker".
	inversion nlen0 as [neqSn0 | n0' true_nlen0 eqn0].
	exact I.
	exact (IHn0 (H _ I) _ true_nlen0). *)
Qed.
Lemma strong_induction (P : nat -> Prop)
 : (forall n0 : nat, (forall n : nat, n <= n0 -> P n) -> P (S n0))
   -> (P 0) -> forall n : nat, P n.
Proof.
	intros H I.
	assert (forall n0 n : nat, n <= n0 -> P n) as IH.
	{	intros n0; induction n0 as [|n0 IHn0]; intros n.
		remember 0 as z eqn:Hz; intros nlez; destruct nlez as [|prev0 _];
		 [exact I | discriminate Hz].
		(* intros nle0; inversion nle0; exact I. Same as before
		intros nleSn0; inversion nleSn0 as [neqSn0 | n0' nlen0 eqn0]. *)
		remember (S n0) as Sn0 eqn:HSn0; intros nleSn0; destruct nleSn0 as [|n0' nlen0].
		by rewrite HSn0; exact (H _ IHn0).
		by apply eq_add_S in HSn0; rewrite HSn0 in nlen0; exact (IHn0 _ nlen0). }
	by intros n; exact (IH _ _ (le_n n)).
Qed.

Lemma exists_or_never (P : nat -> Prop) (n0 : nat)
 : (forall n : nat, P n \/ ~ (P n))
   -> ((exists n, P n) \/ (forall n : nat, n >= n0 -> ~ (P n)))
   -> ((exists n, P n) \/ (forall n : nat, ~ (P n))).
Proof.
	intros H; induction n0 as [|n0 IHn0]; intros [[n Pn] | forallnnPn].
	1,3: by left; exists n; exact Pn.
	by right; intros n; exact (forallnnPn _ (le_0_n n)).
	destruct (H n0) as [Pn0 | nPn0].
	by left; exists n0; exact Pn0.
	apply IHn0; right; intros n ngen0.
	destruct ngen0 as [|n' n0len'].
	by exact nPn0.
	by exact (forallnnPn _ (le_n_S _ _ n0len')).
	(* inversion ngen0 as [n0eqn | n' n0len' Sn'eqn].
	rewrite <-n0eqn; exact nPn0.
	apply le_n_S in n0len'.
	exact (forallnnPn _ n0len'). *)
	(* Left for posterity
	intros H I.
	induction n0; destruct I as [[n I] | I]. 1,3: by left; exists n.
	by right; intros n; specialize (I n (le_0_n n)).
	by destruct (H n0) as [An | nAn];
	[left; exists n0 |
	 apply IHn0; right; intros n [| n' H0]; [| apply le_n_S in H0; exact (I (S n') H0) ] ]. *)
Qed.

Lemma forall_not_is_never_exists {P : nat -> Prop}
 : (forall n : nat, ~ P n) -> ~ (exists n : nat, P n).
Proof.
	intros nPn [n Pn]; is_false (nPn _ Pn).
Qed.

Lemma double_induction (P : nat -> Prop)
 : P 0 -> P 1 -> (forall n : nat, P n -> P (S n) -> P (S (S n))) -> forall n : nat, P n.
Proof.
	intros P0 P1 IH.
	assert (forall n : nat, P n /\ P (S n)) as I.
	{	intros n; induction n as [|n [Pn PSn]].
		by split; [exact P0  | exact P1].
		by split; [exact PSn | exact (IH n Pn PSn)]. }
	by intros n; exact (and_l (I n)).
Qed.

(*** Natural number lemmas ***)

Lemma plusC : forall m n : nat, m + n = n + m.
Proof.
	intros m; induction m as [|m IHm]; intros n; induction n as [|n IHn].
	by reflexivity.
	by minimize plus; rewrite <-IHn; unfold plus; reflexivity.
	by minimize plus; rewrite IHm; reflexivity.
	by minimize plus in IHn; rewrite IHm in IHn;
	 minimize plus; rewrite IHm; minimize plus; rewrite <-IHn; reflexivity.
	(* Or:
	intros m n.
	induction n as [|n IHn].
	by induction m as [|m IHm]; minimize plus; [|rewrite IHm].
	minimize plus. rewrite <-IHn.
	by rewrite plus_n_Sm. *)
Qed.

Lemma plusA : forall m n p : nat, m + (n + p) = m + n + p.
Proof.
	intros m n p.
	induction m as [|m IHm].
	by unfold plus; reflexivity.
	by minimize plus; rewrite IHm; reflexivity.
Qed.

(* Alternative proof for mult_n_O:
induction m; [| compare_unfold to IHm through mult; minimize plus; exact IHm].
*)
Lemma multC : forall m n : nat, m * n = n * m.
Proof.
	intros m; induction m as [|m IHm]; intros n; induction n as [|n IHn].
	by reflexivity.
	by minimize mult; rewrite <-IHn; unfold mult, plus; reflexivity.
	by minimize mult; rewrite ->IHm; unfold mult, plus; reflexivity.
	by minimize mult in IHn; rewrite IHm in IHn;
	 minimize mult; rewrite IHm; rewrite <-IHn; minimize mult; minimize plus;
	 rewrite plusA, (plusC n m), <-plusA; reflexivity.
	(* Or:
	intros m n; induction m as [|m IHm]; unfold mult.
	by rewrite <-mult_n_O.
	rewrite <-mult_n_Sm; minimize mult. by rewrite plusC; rewrite IHm.
	*)
Qed.

(* Left for reference
Lemma stable_by_plus : forall m n p : nat, n = p -> m + n = m + p.
Proof.
	by intros m n p [=->]. (* intros m n p H; rewrite ->H. *)
Qed. *)

Lemma mult_ldistrib_plus : forall m n p : nat, m * n + m * p = m * (n + p).
Proof.
	intros m; induction m as [|m IHm].
	by unfold mult; reflexivity.
	intros n p.
	minimize mult.
	by rewrite <-IHm, <-(plusA n _ _), (plusC (m*n) _), <-plusA, (plusA n p _), (plusC (_*_));
	 reflexivity.
Qed.
Lemma mult_rdistrib_plus : forall m n p : nat, m * p + n * p = (m + n) * p.
Proof.
	intros m n p; rewrite (multC m p), (multC n p), (multC (m+n) p).
	by exact (mult_ldistrib_plus _ _ _).
	(* Or:
	intros m n p.
	induction p as [|p IHp].
	by rewrite <-(mult_n_O m), <-(mult_n_O n), <-(mult_n_O (m+n)); unfold plus.
	rewrite <-mult_n_Sm, <-mult_n_Sm, <-mult_n_Sm, <-IHp.
	by rewrite
	 (plusA (m*p+m) (n*p) n), (plusA (m*p+n*p) m n),
	 <-(plusA (m*p) m (n*p)), (plusC m (n*p)), (plusA (m*p) (n*p) m).
	*)
Qed.

Lemma multA : forall m n p : nat, m * (n * p) = (m * n) * p.
Proof.
	intros m; induction m as [|m IHm].
	by unfold mult; reflexivity.
	intros n p; minimize mult; rewrite IHm. by exact (mult_rdistrib_plus _ _ _).
	(* Or:
	intros m n p.
	induction m as [|m IHm].
	by unfold mult.
	minimize mult. rewrite IHm.
	by rewrite distribMultOverPlus.
	*)
Qed.

Lemma nleO : forall n : nat, n <= 0 -> n = 0.
Proof.
	intros n nle0; remember 0 as z eqn:Hz; destruct nle0 as [|prevz _].
	by reflexivity.
	by discriminate Hz.
Qed.
Lemma nleO' : forall n : nat, n <= 0 -> 0 = n.
Proof.
	intros n nle0; symmetry; exact (nleO n nle0).
Qed.
Lemma nle_or_nlt : forall m n : nat, ~ (m <= n) \/ ~ (n < m).
Proof.
	intros m; induction m as [|m IHm]; [intros n | intros [|n]].
	by right; intros nltO;  exact (O_S _ (nleO' _ nltO)).
	by left;  intros Smle0; exact (O_S _ (nleO' _ Smle0)).
	by destruct (IHm n) as [H0 | H0];
	 [left | right]; intros H; apply le_S_n in H; exact (H0 H).
Qed.
Lemma not_lt_n : forall n : nat, ~ (n < n).
Proof.
	intros n; specialize (nle_or_nlt n n) as [nle | nlt].
	by is_false (nle (le_n n)).
	by exact nlt.
Qed.

Lemma le_a_plus : forall a b : nat, a <= a + b.
Proof.
	intros a b; induction a as [|a IHa].
	by exact (le_0_n _).
	by exact (le_n_S _ _ IHa).
Qed.

Lemma le_is_exists_plus: forall a b : nat, a <= b -> exists n : nat, b = n + a.
Proof.
	intros a b aleb; induction aleb as [|m _ [n H]].
	by exists 0; unfold plus; reflexivity.
	by exists (S n); rewrite H; unfold plus; reflexivity.
Qed.
Lemma exists_plus_is_le: forall a b : nat, (exists n : nat, b = n + a) -> a <= b.
Proof.
	intros a b [n H]. rewrite H, plusC.
	by exact (le_a_plus _ _).
Qed.
Lemma eq_is_le: forall a b : nat, a = b -> a <= b.
Proof.
	by intros a b [=<-]; exact (le_n a).
Qed.
Lemma lt_is_exists_plus: forall a b : nat, a < b -> exists n : nat, b = S n + a.
Proof.
	intros a b altb.
	specialize (le_is_exists_plus _ _ altb) as [n H].
	exists n.
	by rewrite plus_Sn_m, plus_n_Sm; exact H.
Qed.
Lemma exists_plus_is_lt: forall a b : nat, (exists n : nat, b = S n + a) -> a < b.
Proof.
	intros a b [n [=->]].
	apply le_n_S.
	rewrite plusC.
	by exact (le_a_plus _ _).
Qed.

Lemma lt_is_not_le : forall a b : nat, a < b -> ~ (b <= a).
Proof.
	intros a b altb blea.
	induction blea as [|a B IHa].
	by exact (not_lt_n b altb).
	by exact (IHa (le_S_n _ _ (le_S _ _ altb))).
	(* specialize (le_is_exists_plus _ _ blea) as [n H]; clear blea. rewrite H in altb; clear a H.
	specialize (le_is_exists_plus _ _ altb) as [m H]. rewrite H in altb.
	specialize (le_is_exists_plus _ _ altb) as [p H']. clear altb H.
	rewrite plusC in H'; minimize plus in H'.
	rewrite plusC in H'; minimize plus in H'.
	rewrite plusC in H'; minimize plus in H'.
	rewrite (plusC n (S _)) in H'; minimize plus in H'.
	rewrite (plusC p _) in H'; minimize plus in H'.
	apply eq_add_S in H'; rewrite <-(plusA _ n p) in H'.
	generalize dependent (n + p); generalize dependent (n + b + m); intros i j H'; clear b n m p.
	induction i as [|i IHq]; [discriminate | injection H'; exact IHq].
	(* injection H' adds "i = S (i + j) -> " to the goal,
	   making it solvable by exact IHq. *) *)
Qed.
Lemma le_is_not_lt : forall a b : nat, a <= b -> ~ (b < a).
Proof.
	intros a b aleb blta.
	by exact (lt_is_not_le _ _ blta aleb).
Qed.

Lemma le_plus_plus : forall a c b d : nat, a <= b -> c <= d -> a + c <= b + d.
	intros a c b d aleb cled.
	induction aleb as [|b aleb IHa].
	induction cled as [|d cled IHc].
	by exact (le_n _).
	by rewrite (plusC _ (S d)); minimize plus; rewrite (plusC d _); exact (le_S _ _ IHc).
	by minimize plus; exact (le_S _ _ IHa).
	(* Or:
	specialize (le_is_exists_plus _ _ aleb) as [na Ha];
	specialize (le_is_exists_plus _ _ cled) as [nc Hc].
	apply exists_plus_is_le; exists (na + nc).
	rewrite Ha, Hc.
	by rewrite (plusA _ nc c), (plusA _ a c), (plusC _ nc), plusA, (plusC nc na).
	*)
Qed.
Lemma lt_plus_plus : forall a c b d : nat, a < b -> c < d -> a + c < b + d.
	intros a c b d altb cltd.
	specialize (le_plus_plus _ _ _ _ altb cltd) as P.
	minimize plus in P; rewrite plusC in P; minimize plus in P; rewrite plusC in P.
	exact (le_S_n _ _ (le_S _ _ P)).
Qed.

Lemma le_mult : forall m n p : nat, n <= p -> m * n <= m * p.
Proof.
	intros m n p H; induction m as [|m IHm].
	by unfold mult; exact (le_n 0).
	minimize mult.
	by exact (le_plus_plus _ _ _ _ H IHm).
	(* Or: (old needed m <> 0)
	intros m n p mne0 H.
	induction m as [|m IHm].
		by contradiction mne0. (* mne0 became 0 <> 0 *)
	clear mne0. (* Always true *)
	destruct m as [|m].
		by unfold mult; rewrite <-plus_n_O; rewrite <-plus_n_O; exact H.
	specialize (IHm (not_eq_sym (O_S m))).
	minimize mult; minimize mult in IHm.
	exact (le_plus_plus _ _ _ _ H IHm).
	*)
Qed.
Lemma lt_mult : forall m n p : nat, m <> 0 -> n < p -> m * n < m * p.
Proof.
	intros [|m] n p mne0 nltp.
	by is_false (mne0 (eq_refl 0)).
	clear mne0.
	induction m as [|m IHm].
	by unfold mult; rewrite (plusC _ 0), (plusC _ 0); unfold plus; exact nltp.
	by minimize mult; minimize mult in IHm; exact (lt_plus_plus _ _ _ _ nltp IHm).
	(* Or:
	intros m n p mne0 H.
	induction m as [|m IHm].
		by contradiction mne0. (* mne0 became 0 <> 0 *)
	clear mne0. (* Always true *)
	destruct m as [|m].
		by unfold mult; rewrite <-plus_n_O; rewrite <-plus_n_O; exact H.
	specialize (IHm (not_eq_sym (O_S m))).
	minimize mult; minimize mult in IHm.
	assert (P : forall a b c d : nat, a < b -> c < d -> a + c < b + d).
		intros a b c d altb cltd.
		specialize (lt_is_exists_plus _ _ altb) as [na Ha];
		specialize (lt_is_exists_plus _ _ cltd) as [nc Hc].
		apply exists_plus_is_lt; exists (S (na + nc)).
		rewrite Ha; rewrite Hc. minimize plus; rewrite <-plus_n_Sm.
		apply eq_S; apply eq_S.
		by rewrite (plusA _ nc c), (plusA _ a c), (plusC _ nc), plusA, (plusC nc na).
	by specialize (P _ _ _ _ H IHm).
	*)
Qed.

(* Temporarily left
Replace with "inversion _".
Lemma le_is_lt_or_eq : forall m n : nat, (m <= n) -> (m < n) \/ (m = n).
Proof.
	intros m n [|n']. by right. by left; apply le_n_S.
Qed.
*)

Lemma le_or_gt : forall m n : nat, (m <= n) \/ (m > n).
Proof.
	intros m n; induction m as [|m [[|n' mlen] | mgtn]].
	by left; exact (le_0_n n).
	by right; exact (le_n (S m)).
	by left; exact (le_n_S _ _ mlen).
	by right; exact (le_S _ _ mgtn).
Qed.

Lemma eq_or_ne : forall m n : nat, (m = n) \/ (m <> n).
Proof.
	intros m; induction m as [|m IHm]; intros [|n].
	by left; reflexivity.
	by right; exact (O_S _).
	by right; exact (not_eq_sym (O_S _)).
	destruct (IHm n) as [eq | ne].
	by left; exact (eq_S _ _ eq).
	by right; exact (not_eq_S _ _ ne).
	(* intros m; induction m as [|m IHm].
	intros n; induction n as [|n IHn]; [by left; reflexivity | right; apply O_S].
	intros [|n].
	right; exact (not_eq_sym (O_S _)).
	specialize (IHm n) as [meqn | mnen].
	left; exact (eq_S _ _ meqn).
	right; exact (not_eq_S _ _ mnen). *)
Qed.

Lemma leT : forall m n p : nat, (m <= n) -> (n <= p) -> (m <= p).
Proof.
	intros m n p [|prevn mleprevn]; [intros [|prevp mleprevp] | intros nlep].
	by exact (le_n m).
	by exact (le_S _ _ mleprevp).
	induction mleprevn as [|prevn _ IHn].
	by exact (le_S_n _ _ (le_S _ _ nlep)).
	by exact (IHn (le_S_n _ _ (le_S _ _ nlep))).
Qed.

Lemma le_le_is_eq : forall m n : nat, (m <= n) -> (n <= m) -> (m = n).
Proof.
	intros m n H1' H2'.
	destruct H2' as [|prevm nleprevm].
	by reflexivity.
	by is_false (not_lt_n _ (leT _ _ _ H1' nleprevm)).
	(* specialize (le_is_exists_plus _ _ H1') as [n1 H1]; clear H1'.
	specialize (le_is_exists_plus _ _ H2') as [n2 H2]; clear H2'.
	rewrite H1 in H2. rewrite plusA in H2.
	assert (n2pn1eq0 : n2 + n1 = 0).
	{	clear H1.
		induction m as [|m IHm].
		rewrite (plusC _ 0) in H2; unfold plus in H2; symmetry; exact H2.
		rewrite <-plus_n_Sm in H2. injection H2; exact IHm. }
	assert (n1eq0 : n1 = 0).
	{	clear m n H1 H2.
		induction n2 as [|n2 IH]; unfold plus in n2pn1eq0.
		exact n2pn1eq0.
		solve [discriminate]. }
	rewrite n1eq0 in H1; unfold plus in H1; symmetry; exact H1. *)
Qed.
Lemma lt_is_ne : forall m n : nat, (m < n) -> (m <> n).
Proof.
	by intros m n mltn [=->]; exact (not_lt_n _ mltn).
	(* intros m n mltn meqn; symmetry in meqn; apply eq_is_le in meqn;
	 apply lt_is_not_le in mltn; exact (mltn meqn). *)
Qed.

Lemma ne_is_lt_or_lt: forall a b : nat, a <> b -> (a < b) \/ (b < a).
Proof.
	intros a b H.
	specialize (le_or_gt a b) as [aleb | agtb].
	by destruct aleb as [|b aleb]; [is_false (H (eq_refl a)) | left; exact (le_n_S _ _ aleb)].
	by right; exact agtb.
Qed.
(* Lemma not_lt_n : forall n : nat, ~ (n < n).
Proof.
	intros n H. specialize (lt_is_exists_plus _ _ H) as [k Hk]; clear H.
	induction n as [|n IHn].
	minimize plus in Hk; solve [discriminate].
	rewrite <-plus_n_Sm in Hk; exact (IHn (eq_add_S _ _ Hk)).
Qed. *)
(* Lemma lt_is_ne: forall a b : nat, a < b -> a <> b.
Proof.
	by intros a b H [=<-]; specialize (not_lt_n a).
Qed. *)

Lemma eq_mult : forall m n p : nat,  n = p -> m * n = m * p.
Proof.
	by intros ? ? ? [=->]; reflexivity.
	(* intros m n p neqp.
	specialize (eq_is_le _ _ neqp) as nlep; symmetry in neqp; specialize (eq_is_le _ _ neqp) as plen; clear neqp.
	specialize (le_mult m _ _ nlep) as mnlemp;
	specialize (le_mult m _ _ plen) as mplemn.
	exact (le_le_is_eq _ _ mnlemp mplemn). *)
Qed.
Lemma ne_mult : forall m n p : nat, m <> 0 -> n <> p -> m * n <> m * p.
Proof.
	intros m n p mne0 neqp.
	by specialize (ne_is_lt_or_lt _ _ neqp) as [H | H]; clear neqp;
	specialize (lt_mult _ _ _ mne0 H) as H';
	apply lt_is_ne in H'; [|apply not_eq_sym in H']; exact H'.
Qed.

Lemma mult_invertible : forall m n p : nat, m <> 0 -> m * n = m * p -> n = p.
Proof.
	intros m n p mne0 mneqnp.
	specialize (eq_or_ne n p) as [neqp | nnep].
	by exact neqp.
	by is_false (ne_mult _ _ _ mne0 nnep mneqnp).
Qed.

(*** Evenness ***)
Inductive evenI : nat -> Prop :=
	| even_0 : evenI 0
	| even_SS : forall n : nat, evenI n -> evenI (S (S n)).
Inductive oddI : nat -> Prop :=
	| odd_1 : oddI 1
	| odd_SS : forall n : nat, oddI n -> oddI (S (S n)).
Definition evenF (n : nat) : Prop := exists m : nat, n = 2*m.
Definition oddF (n : nat) : Prop := exists m : nat, n = 2*m+1.

Lemma evenI_evenF : forall n : nat, evenI n -> evenF n.
Proof.
	unfold evenF.
	intros n neven; induction neven as [|n neven [m IHn]].
	by exists 0; rewrite multC; unfold mult; reflexivity.
	by exists (S m); rewrite multC; minimize mult; minimize plus;
	 rewrite IHn, multC; reflexivity.
Qed.
Lemma evenF_evenI : forall n : nat, evenF n -> evenI n.
Proof.
	intros n [m neven]; generalize dependent n; induction m as [|m IHm]; intros n neven.
	by rewrite multC in neven; unfold mult in neven; rewrite neven; exact even_0.
	destruct n as [|[|n]].
	by exact even_0. (* Though really, it is impossible *)
	by rewrite multC in neven; minimize mult in neven; is_false (O_S _ (eq_add_S _ _ neven)).
	rewrite multC in neven; minimize mult in neven; apply eq_add_S, eq_add_S in neven; rewrite multC in neven.
	by exact (even_SS _ (IHm _ neven)).
Qed.
Lemma evenE_evenI : forall n m : nat, (n = 2*m) -> evenI n.
Proof.
	by intros n m neven; exact (evenF_evenI _ (if_exist_then_exists _ _ neven)).
Qed.
Lemma oddI_oddF : forall n : nat, oddI n -> oddF n.
Proof.
	unfold oddF.
	intros n nodd; induction nodd as [|n nodd [m IHn]].
	by exists 0; rewrite multC; unfold mult; reflexivity.
	by exists (S m); rewrite multC; minimize mult; minimize plus; rewrite IHn, multC; reflexivity.
Qed.
Lemma oddF_oddI : forall n : nat, oddF n -> oddI n.
Proof.
	unfold oddF.
	intros n [m nodd]; generalize dependent n; induction m as [|m IHm]; intros n nodd.
	by rewrite multC in nodd; unfold mult in nodd; rewrite nodd; exact odd_1.
	destruct n as [|[|n]].
	by rewrite plusC in nodd; unfold plus in nodd; is_false (O_S _ nodd).
	by exact odd_1. (* Though really, it is impossible *)
	rewrite multC in nodd; minimize mult in nodd; apply eq_add_S, eq_add_S in nodd; rewrite multC in nodd.
	by exact (odd_SS _ (IHm _ nodd)).
Qed.
Lemma oddE_oddI : forall n m : nat, (n = 2*m + 1) -> oddI n.
Proof.
	by intros n m nodd; exact (oddF_oddI _ (if_exist_then_exists _ _ nodd)).
Qed.

Lemma even_or_odd : forall n : nat, (evenI n) \/ (oddI n).
Proof.
	apply (double_induction (fun n => (evenI n) \/ (oddI n))).
	by left; exact even_0.
	by right; exact odd_1.
	intros n [neven | nodd] _.
	by left; exact (even_SS _ neven).
	by right; exact (odd_SS _ nodd).
Qed.
Lemma even_is_not_odd : forall n : nat, (evenI n) -> ~ (oddI n).
Proof.
	intros n neven.
	induction neven as [|n neven IHneven].
	by remember 0 as z eqn:Hz; symmetry in Hz; intros odd0; destruct odd0 as [|? _];
	 is_false (O_S _ Hz).
	remember (S (S n)) as SSn eqn:HSSn; intros oddSSn; destruct oddSSn as [|n0 oddn0].
	by exact (O_S _ (eq_add_S _ _ HSSn)).
	by rewrite (eq_add_S _ _ (eq_add_S _ _ HSSn)) in oddn0; exact (IHneven oddn0).
Qed.
Lemma odd_is_not_even : forall n : nat, (oddI n) -> ~ (evenI n).
Proof.
	intros n nodd.
	induction nodd as [|n nodd IHnodd].
	remember 1 as o eqn:Ho; intros odd0; destruct odd0 as [|? _].
	by is_false (O_S _ Ho).
	by symmetry in Ho; is_false (O_S _ (eq_add_S _ _ Ho)).
	remember (S (S n)) as SSn eqn:HSSn; intros evenSSn; destruct evenSSn as [|n0 evenn0].
	by is_false (O_S _ HSSn).
	by rewrite (eq_add_S _ _ (eq_add_S _ _ HSSn)) in evenn0; exact (IHnodd evenn0).
Qed.

Lemma evenI_noddF : forall n : nat, (evenI n) -> (forall m : nat, n <> 2 * m + 1).
Proof.
	intros n neven.
	refine (if_not_exists_then_never _ (fun _ => eq_or_ne _ _)
		(modus_tonens (P:=exists m : nat, n = 2*m+1) (even_is_not_odd _ neven) _));
	 intros [m Hm]; exact (oddE_oddI _ _ Hm).
	(* intros n neven m nodd.
	apply even_is_not_odd in neven.
	assert (oddI n).
	{	clear neven; generalize dependent n; induction m as [|m IHm]; intros n nodd.
		rewrite multC in nodd; unfold mult, plus in nodd; rewrite nodd; exact odd_1.
		destruct n as [|n].
		solve [rewrite plusC in nodd; unfold plus in nodd; inversion nodd].
		destruct n as [|n].
		solve [rewrite plusC in nodd; unfold plus in nodd; inversion nodd].
		minimize mult in nodd; rewrite (plusC _ 0) in nodd; minimize plus in nodd;
		 rewrite plusC in nodd; minimize plus in nodd.
		apply eq_add_S, eq_add_S in nodd.
		apply odd_SS.
		apply IHm.
		rewrite nodd, plusC; minimize mult; rewrite (plusC _ 0), (plusC _ 1); minimize plus.
		reflexivity. }
	exact (neven H). *)
Qed.
Lemma oddI_nevenF : forall n : nat, (oddI n) -> (forall m : nat, n <> 2 * m).
Proof.
	intros n nodd m neven.
	by exact (even_is_not_odd n (evenE_evenI _ _ neven) nodd).
	(* intros n nodd m neven.
	apply odd_is_not_even in nodd.
	assert (evenI n).
	{	clear nodd; generalize dependent n; induction m as [|m IHm]; intros n neven.
		rewrite multC in neven; unfold mult, plus in neven; rewrite neven; exact even_0.
		destruct n as [|n].
		exact (even_0).
		destruct n as [|n].
		solve [unfold mult in neven; rewrite (plusC _ 0) in neven; minimize plus in neven;
		 rewrite plusC in neven; inversion neven].
		minimize mult in neven; rewrite (plusC _ 0) in neven; minimize plus in neven;
		 rewrite plusC in neven; minimize plus in neven.
		apply eq_add_S, eq_add_S in neven.
		apply even_SS.
		apply IHm.
		rewrite neven; minimize mult; rewrite (plusC _ 0); minimize plus.
		reflexivity. }
	exact (nodd H). *)
Qed.

Lemma even_plus : forall m n : nat, (evenI m) -> (evenI (m + n)) -> (evenI n).
Proof.
	intros m n meven; generalize dependent n; induction meven as [|m meven IHm]; intros n.
	by intros H; unfold plus in H; exact H.
	minimize plus; intros SSmneven.
	remember (S (S (m+n))) as SSmn eqn:HSSmn.
	destruct SSmneven as [|mn mneven].
	by discriminate HSSmn.
	apply eq_add_S, eq_add_S in HSSmn; rewrite HSSmn in mneven.
	by exact (IHm _ mneven).
	(* inversion SSmneven as [|_n0 mneven _n0H]; exact (IHm _ mneven). *)
Qed.
Lemma even_sum : forall m n : nat, (evenI m) -> (evenI n) -> (evenI (m + n)).
Proof.
	intros m n meven neven; apply evenI_evenF in meven; apply evenI_evenF in neven;
	 destruct meven as [k Hk]; destruct neven as [l Hl].
	apply evenF_evenI; exists (k+l).
	by rewrite <-mult_ldistrib_plus, Hk, Hl; reflexivity.
Qed.

Lemma even_twice : forall n : nat, evenI (n + n).
Proof.
	intros n.
	induction n as [|n IHn].
	by unfold plus; exact even_0.
	rewrite <-plus_n_Sm, plus_Sn_m.
	by exact (even_SS _ IHn).
Qed.

Lemma div_of_even : forall m n : nat, evenI (m * n) -> (evenI m) \/ (evenI n).
Proof.
	intros m; apply (double_induction (fun n => (evenI (m*n)) -> (evenI m) \/ (evenI n))).
	by intros _; right; exact even_0.
	by intros meven; rewrite multC in meven; unfold mult in meven;
	 rewrite plusC in meven; minimize plus in meven;
	 left; exact meven.
	intros n IHn _ multeven.
	specialize (even_or_odd m) as [meven | modd].
	by left; exact meven.
	(* Here... *)
	right.
	rewrite multC in multeven; minimize mult in multeven; minimize plus in multeven;
	rewrite plusA in multeven.
	specialize (even_plus _ _ (even_twice m) multeven) as multeven'.
	rewrite multC in multeven'.
	by right; exact (disjunctive_syllogism (IHn multeven') (odd_is_not_even _ modd)).
	(* ... to here is also:
	rewrite multC in multeven; minimize mult in multeven.
	rewrite plusA, multC in multeven.
	specialize (even_plus _ _ (even_twice m) multeven) as mneven.
	specialize (IHn mneven) as [meven | neven].
	left; exact meven.
	right; exact (even_SS _ neven). *)
Qed.

Lemma mult_of_even : forall m n : nat, (evenI m) -> evenI (m * n).
Proof.
	intros m n meven; induction meven as [|m meven IHm].
	by unfold mult; exact even_0.
	by minimize mult; rewrite plusA; exact (even_sum _ _ (even_twice n) IHm).
Qed.

Lemma div_of_odd : forall m n : nat, oddI (m * n) -> (oddI m) /\ (oddI n).
Proof.
	intros m n mnodd; specialize (even_or_odd m) as [meven | modd].
	by is_false (even_is_not_odd _ (mult_of_even _ _ meven) mnodd).
	split; [by exact modd|].
	specialize (even_or_odd n) as [neven | nodd].
	by rewrite multC in mnodd;
	 is_false (even_is_not_odd _ (mult_of_even _ _ neven) mnodd).
	by exact nodd.
Qed.

Lemma mult_of_odd : forall m n : nat, (oddI m) -> (oddI n) -> (oddI (m * n)).
Proof.
	intros m n modd nodd; specialize (even_or_odd (m*n)) as [mneven | mnodd].
	specialize (div_of_even _ _ mneven) as [meven | neven].
	by is_false (even_is_not_odd _ meven modd).
	by is_false (even_is_not_odd _ neven nodd).
	by exact mnodd.
Qed.

Lemma even_le : forall m n : nat, m = 2 * n -> n <= m.
Proof.
	by intros m n [=->]; exact (le_a_plus _ _).
Qed.
Lemma odd_lt : forall m n : nat, m = 2 * n + 1 -> n < m.
Proof.
	intros [|m] n meq; rewrite plusC in meq; unfold plus in meq.
	by discriminate meq.
	by exact (le_n_S _ _ (even_le _ _ (eq_add_S _ _ meq))).
Qed.

Lemma even_div2_0 : forall m n : nat, m = 2 * n -> m <> 0 -> n <> 0.
Proof.
	intros m [|n] meven mne0.
	by rewrite multC in meven; unfold mult in meven; rewrite meven in mne0; contradiction.
	by exact (not_eq_sym (O_S _)).
Qed.
Lemma odd_div2_0 : forall m n : nat, m = 2 * n + 1 -> m <> 1 -> n <> 0.
Proof.
	intros m [|n] meven mne0.
	by rewrite multC in meven; unfold mult, plus in meven; rewrite meven in mne0; contradiction.
	by exact (not_eq_sym (O_S _)).
Qed.
