Require Import base.

(* Need the -noinit flag *)

(* Inspired by https://github.com/coq-contribs/zfc/blob/master/zfc.v *)

Require Import z_theory_base.
Require Import Ltac.
Require Import Logic.
Require Import Specif.
Require Import Coq.Init.Tactics.

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
Lemma succ_is_n_n : forall e a : Ensemble, a inE Succ e -> a inE e \/ a E= e.
Proof.
	intros e a ainS; specialize (pair_union_is_union ainS) as [aine|ainse].
	by left; exact aine.
	by right; exact (singleton_is_singleton ainse).
Qed.
Lemma Eeq_is_Eeq_succ : forall A B : Ensemble, A E= B -> Succ A E= Succ B.
Proof.
	intros A B AeqB; unfold Succ; apply incl_antisym; apply incl_incl_is_union_incl.
	by exact (incl_trans (Eeq_incl_l AeqB) (pair_union_is_union_l _ _)).
	by exact (incl_trans (Eeq_incl_l (singleton_refl AeqB)) (pair_union_is_union_r _ _)).
	1,2: apply Eeq_sym in AeqB.
	by exact (incl_trans (Eeq_incl_l AeqB) (pair_union_is_union_l _ _)).
	by exact (incl_trans (Eeq_incl_l (singleton_refl AeqB)) (pair_union_is_union_r _ _)).
Qed.
Arguments Eeq_is_Eeq_succ {A B} AeqB.

Definition NatE : Ensemble := let (v, _) := infinity_axiom in v.
Definition NatP : (is_nat NatE) /\ (forall a, (is_nat a) -> NatE incl a)
 := let (v, p)
    as iax
    return (is_nat (let (v, _) := iax in v)
            /\ (forall a, (is_nat a) -> (let (v, _) := iax in v) incl a))
    := infinity_axiom in p.

Lemma induction_N (P : Ensemble -> Prop) :
 P (EmptySet) -> (Eforall e in NatE, P e -> P (Succ e)) -> Eforall n in NatE, P n.
Proof.
	intros I IH.
	specialize (schema_restricted_comprehension_axiom P NatE) as [[C h] Cprop].
	intros n ninNatE.
	refine (proj2 (proj1 (iff_and (Cprop n)) _)).
	refine (proj2 NatP _ (conj _ _) _ ninNatE).
	apply Cprop; split.
	by exact (proj1 (proj1 NatP)).
	by exact I.
	intros x xinC.
	specialize (proj1 (iff_and (Cprop x)) xinC) as [xinNatE Px].
	apply (proj2 (iff_and (Cprop (Succ x)))); split.
	by exact (proj2 (proj1 NatP) _ xinNatE).
	by exact (IH x xinNatE Px).
Qed.
Lemma double_induction_N : forall P : Ensemble -> Prop, P EmptySet -> P (Succ EmptySet) ->
  (Eforall n in NatE, P n -> P (Succ n) -> P (Succ (Succ n))) -> Eforall n in NatE, P n.
Proof.
	intros P I0 I1 IH.
	assert (H : Eforall n in NatE, P n /\ P (Succ n)).
	{ apply induction_N.
	  by split; [exact I0|exact I1].
	  by intros e ein [Pe PSe]; exact (conj PSe (IH _ ein Pe PSe)). }
	by intros n nin; exact (proj1 (H _ nin)).
Qed.

Lemma in_N_is_in_N : Eforall a in NatE, forall e, e inE a -> e inE NatE.
Proof.
	apply (induction_N (fun a => forall e, e inE a -> e inE NatE)).
	intros e einE; contradiction (empty_is_empty _ einE).
	intros a ain IHa e einSa; destruct (succ_is_n_n _ _ einSa) as [eina|eeqa].
	by exact (IHa _ eina).
	by exact (Eeq_in_trans_r eeqa ain).
Qed.

Lemma in_is_in_succ : forall A : Ensemble, Eforall B in NatE, A inE B -> Succ A inE Succ B.
Proof.
	intros A B Bin AinB; generalize dependent B;
	 apply (induction_N (fun B => A inE B -> Succ A inE Succ B)).
	intros AinE; contradiction (empty_is_empty _ AinE).
	intros B Bin IHB AinSB.
	destruct (succ_is_n_n _ _ AinSB) as [AinB|AeqB].
	by exact (e_incl_succ _ _ (IHB AinB)).
	by exact (Eeq_in_trans_r (Eeq_is_Eeq_succ AeqB) (e_in_succ _)).
Qed.
Arguments in_is_in_succ {A B} Bin AinB.

Lemma in_trans_N : forall a b : Ensemble, Eforall c in NatE,
 a inE b -> b inE c -> a inE c.
Proof.
	intros a b c cin ainb; generalize dependent c.
	refine (induction_N
		(fun c => b inE c -> a inE c)
		_
		_).
	intros binE; contradiction (empty_is_empty _ binE).
	intros c cin IHc binSc.
	specialize (succ_is_n_n _ _ binSc) as [binc|beqc].
	by exact (e_incl_succ _ _ (IHc binc)).
	by exact (e_incl_succ _ _ (in_Eeq_trans_l beqc ainb)).
Qed.

Lemma succ_inj_N : Eforall a in NatE, Eforall b in NatE, Succ a E= Succ b -> a E= b.
Proof.
	intros a ain b bin SaeqSb.
	specialize (succ_is_n_n _ _ (in_Eeq_trans_l SaeqSb (e_in_succ _))) as [ainb|aeqb].
	specialize (succ_is_n_n _ _ (in_Eeq_trans_r SaeqSb (e_in_succ _))) as [bina|beqa].
	exfalso; specialize (in_trans_N _ _ _ ain ainb bina) as aina; clear b bin SaeqSb ainb bina.
	generalize dependent a; apply (induction_N (fun a => ~ (a inE a))).
	intros EinE; exact (empty_is_empty _ EinE).
	intros a ain ania SainSa.
	specialize (succ_is_n_n _ _ SainSa) as [Saina|Saeqa].
	by exact (ania (in_trans_N _ _ _ ain (e_in_succ _) Saina)).
	by exact (ania (in_Eeq_trans_l Saeqa (Eeq_in_trans_l Saeqa SainSa))).
	by exact (Eeq_sym beqa).
	by exact aeqb.
Qed.
Arguments succ_inj_N {a} ain {b} bin SNmeqSNn.

Inductive nat :=
	| O : nat
	| S : nat -> nat.
Fixpoint N (n : nat) : Ensemble := match n with O => EmptySet | S n => Succ (N n) end.
Definition Nnat : Ensemble := ens nat N.

Lemma N_is_nat : Nnat E= NatE.
Proof.
	apply incl_antisym.
	intros e [n ein]; generalize dependent e; induction n; intros e ein.
	by exact (Eeq_in_trans_r ein (proj1 (proj1 NatP))).
	refine (Eeq_in_trans_r ein (proj2 (proj1 NatP) _ _)); fold N.
	by exact (IHn _ (Eeq_refl _)).
	apply (proj2 NatP); split.
	by exists O; exact (Eeq_refl _).
	by intros e [n nin]; exists (S n); unfold N; fold N; exact (Eeq_is_Eeq_succ nin).
Qed.
Lemma double_induction : forall P : nat -> Prop, P O -> P (S O) ->
  (forall n : nat, P n -> P (S n) -> P (S (S n))) -> forall n : nat, P n.
Proof.
	intros P I0 I1 IH.
	assert (H : forall n : nat, P n /\ P (S n)).
	{ intros n; induction n as [|n [Pn PSn]].
	  by exact (conj I0 I1).
	  by exact (conj PSn (IH _ Pn PSn)). }
	by intros n; exact (proj1 (H _)).
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
Qed.
Lemma natural_longest_string_n : forall n : nat,
	(forall g : nat -> Ensemble,
	 (forall m : nat, LessThan_iterN m n -> (g m) inE (g (S m))) ->
	 (g n E= N n) ->
	 (forall m : nat, LessThan_iterN m (S n) -> g m E= N m)) /\
	(forall f : nat -> Ensemble, (exists m : nat,
		(LessThan_iterN m (S n) /\ (f m) not_in (f (S m)))) \/
		((f (S n)) not_in (N (S n)))).
Proof.
	intros n; induction n as [|n [IHnL IHnR]]; split.
	- intros g Hg gOeqO [|m] mltSO.
	  by exact gOeqO.
	  by is_false (ge_is_not_lt_iterN _ _ (gei_oN _) (lt_iter_revN mltSO)).
	- intros f.
	  specialize (classic (f (S O) E= N O)) as [fSOeq | fSOne].
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
	    by exact (fSnniSn (in_Eeq_trans_l fSSneqSn fSninfSSn)).
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

Lemma succ_inj : forall m n : nat, Succ (N m) E= Succ (N n) -> N m E= N n.
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

Lemma N_inj : forall m n : nat, N m E= N n -> m = n.
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

Lemma NaddN_normal_l : forall n a b : nat, N (addN n a) E= N (addN n b) -> N a E= N b.
Proof.
	intros n; induction n as [|n IHn]; intros a b npaeqnpb.
	by exact npaeqnpb.
	by exact (IHn _ _ (succ_inj npaeqnpb)).
Qed.
Lemma NaddN_normal_r : forall n a b : nat, N (addN a n) E= N (addN b n) -> N a E= N b.
Proof.
	by intros n a b apneqbpn; rewrite (addNC a _), (addNC b _) in apneqbpn;
	  exact (NaddN_normal_l _ _ _ apneqbpn).
Qed.
Lemma NaddN_normal_lr : forall n a b : nat, N (addN n a) E= N (addN b n) -> N a E= N b.
Proof.
	by intros n a b apneqbpn; rewrite (addNC b _) in apneqbpn;
	  exact (NaddN_normal_l _ _ _ apneqbpn).
Qed.
Lemma NaddN_normal_rl : forall n a b : nat, N (addN a n) E= N (addN n b) -> N a E= N b.
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
	- specialize (classic (N m E= N O)) as [meqO | mneO].
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
  a incl Nnat -> a E<> EmptySet -> exists n : nat, (N n inE a)
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
  a incl Nnat -> a E<> EmptySet -> (exists n : nat, (forall k : _, k inE a -> k incl N n))
    -> exists n : nat, (N n inE a) /\ (forall y : Ensemble, y inE a -> y incl N n).
Proof.
	intros a ainclN anee [M amajbyM].
	induction M as [|M IHM].
	exists O; split.
	specialize (non_empty_is_not_empty _ anee) as [x xina].
	destruct (ainclN _ xina) as [n xinNbyn]; apply (Eeq_in_trans_l xinNbyn) in xina; clear x xinNbyn.
	specialize (amajbyM _ xina).
	specialize (classic (N n E= N O)) as [neqO | nneO].
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
