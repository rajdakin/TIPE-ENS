Require Import base.
Require Import bool.
Require Import nat.

(* Set Mangle Names. *)

(* https://madiot.fr/coq100/ *)
Lemma root_of_even : forall n : nat, (evenI (n * n)) -> (evenI n).
Proof.
	intros n H.
	by specialize (div_of_even _ _ H) as [H' | H']; exact H'.
Qed.

Theorem sqrt2_not_rational: forall p q : nat, q <> 0 -> p * p <> 2 * q * q.
Proof.
	refine (strong_induction (fun p => forall q : nat, q <> 0 -> p * p <> 2 * q * q) _ _); swap 1 2.
	- intros [|q] qne0 Oeq2qsq.
	  + by contradiction qne0.
	  + by minimize mult in Oeq2qsq; rewrite multC in Oeq2qsq; minimize mult in Oeq2qsq;
	     minimize plus in Oeq2qsq; discriminate Oeq2qsq.
	- intros p IHp q qne0 psqeq2qsq; rewrite <-multA in psqeq2qsq.
	  specialize (evenE_evenI _ _ psqeq2qsq) as psqeven.
	  specialize (evenI_evenF _ (root_of_even _ psqeven)) as [m Hm].
	  specialize (even_le _ _ Hm) as pdiv2lep.
	  remember (S p) as Sp eqn:HSp; destruct pdiv2lep as [|p' mlep].
	  + rewrite HSp in Hm; minimize mult in Hm; rewrite (plus_Sn_m p 0) in Hm.
	    clear IHp q qne0 m HSp psqeq2qsq psqeven.
	    generalize dependent (p + 0); intros k Hm; induction p as [|p IHp].
	    * by apply eq_add_S in Hm; unfold plus in Hm; exact (O_S _ Hm).
	    * destruct k as [|k].
	      -- by rewrite plusC in Hm; minimize plus in Hm; exact (n_Sn _ Hm).
	      -- by rewrite plus_Sn_m in Hm; exact (IHp (eq_add_S _ _ Hm)).
	  + apply eq_add_S in HSp;
	     rewrite HSp in mlep;
	     rewrite HSp in psqeq2qsq;
	     rewrite HSp in psqeven;
	     rewrite HSp in Hm;
	     clear p' HSp.
	(* apply eq_is_le, (le_plus_plus p 0 p _ (le_n _) _) in Hm.
	inversion pdiv2lep as [Hm' | p' mlep Hp'].
	destruct m as [|m].
	rewrite <-Hm' in psqeq2qsq;
	 rewrite (multC 2 _) in psqeq2qsq; minimize mult in psqeq2qsq;
	 rewrite multC in psqeq2qsq; minimize mult in psqeq2qsq; unfold mult in psqeq2qsq; discriminate.
	destruct m as [|m].
	unfold mult, plus in Hm'; rewrite <-Hm' in psqeq2qsq.
	by rewrite (multC 2 _) in psqeq2qsq; minimize mult in psqeq2qsq; unfold plus in psqeq2qsq;
	 rewrite multC in psqeq2qsq; minimize mult in psqeq2qsq; minimize mult in psqeq2qsq;
	 destruct q as [|q];
	 [contradiction
	 |minimize mult in psqeq2qsq; rewrite plusC in psqeq2qsq; minimize plus in psqeq2qsq;
	  rewrite <-plus_n_Sm in psqeq2qsq; apply eq_add_S in psqeq2qsq; discriminate psqeq2qsq].
	rewrite Hm in Hm'; unfold mult, plus in Hm'; fold plus in Hm'.
	apply eq_add_S, eq_add_S in Hm'.
	generalize (S (m + 0)) Hm'; clear p IHp q qne0 psqeq2qsq psqeven Hm pdiv2lep Hm'.
	intros n Hf; induction m as [|m IHm];
	[by unfold plus in Hf; discriminate Hf
	|minimize plus in Hf; apply eq_add_S in Hf; exact (IHm Hf)].
	
	clear p' Hp' pdiv2lep. *)
	    assert (two_ne_zero : 2 <> 0) by discriminate.
	    rewrite Hm, multA, <-(multA _ _ 2), (multC _ 2), multA, <-(multA 2 2 _), <-(multA 2 _ _) in psqeq2qsq.
	    apply (mult_invertible _ _ _ two_ne_zero) in psqeq2qsq.
	    symmetry in psqeq2qsq; rewrite <-multA in psqeq2qsq.
	    specialize (evenE_evenI _ _ psqeq2qsq) as qsqeven.
	    specialize (root_of_even _ qsqeven) as qeven.
	    specialize (evenI_evenF _ qeven) as [n Hn].
	    rewrite Hn, multA, <-(multA _ _ 2), (multC _ 2), multA, <-(multA 2 2 _), <-(multA 2 _ _) in psqeq2qsq.
	    apply (mult_invertible _ _ _ two_ne_zero) in psqeq2qsq.
	    symmetry in psqeq2qsq.
	    by exact (IHp _ mlep _ (even_div2_0 _ _ Hn qne0) psqeq2qsq).
Qed.

Theorem sqrt2_not_even_over_even : forall p q : nat, q <> 0 -> ((evenI p) -> (oddI q)) -> p * p <> 2 * (q * q).
Proof.
	intros p q qne0 pqcannotmul2 H.
	specialize (root_of_even p (evenF_evenI _ (ex_intro _ (q*q) H))) as peven.
	specialize (pqcannotmul2 peven).
	destruct (evenI_evenF _ peven) as [p_div_2 p_even].
	rewrite p_even in H.
	assert (two_ne_zero : 2 <> 0) by discriminate.
	rewrite <-(multA 2 p_div_2 (2*p_div_2)) in H.
	specialize (mult_invertible 2 _ _ two_ne_zero H) as H'; clear H.
	rewrite ->(multA _ 2 _) in H'.
	rewrite ->(multC _ 2) in H'.
	rewrite <-(multA 2 _ _) in H'.
	symmetry in H'.
	specialize (root_of_even q (evenF_evenI _ (ex_intro _ (p_div_2*p_div_2) H'))) as qeven.
	by exact (even_is_not_odd _ qeven pqcannotmul2).
Qed.

Theorem sqrt2_not_rational' : forall p q : nat, q <> 0 -> p * p = 2 * (q * q) -> False.
Proof.
	intros p q qne0 H_sqrt2_is_rational.
	
	pose (mainP := fun a b => b <> 0 -> exists a' b' : nat, b' <> 0 /\ a * b' = b * a' /\ ((evenI a') -> (oddI b'))).
	assert (finalH : forall a b : nat, mainP a b).
	{	(* FOR ALL a, if a is odd, OK *)
		assert (aoddOK : forall a : nat, oddI a -> forall b : nat, mainP a b).
		{	intros a odda b bne0.
			exists a, b.
			split; [by exact bne0 | split].
			by rewrite multC; reflexivity.
			by intros evena; contradiction (even_is_not_odd _ evena odda). }
		remove mainP in aoddOK.
		
		(* FOR ALL b, if b is odd, OK *)
		assert (boddOK : forall b : nat, oddI b -> forall a : nat, mainP a b).
		{	intros b oddb a bne0.
			exists a, b.
			split; [by exact bne0 | split].
			by rewrite multC; reflexivity.
			by intros _; exact oddb. }
		remove mainP in boddOK.
		
		(* If a is even and b is even, OK *)
		apply (strong_induction (fun a => forall b, mainP a b)); remove mainP.
		intros a0 IHa b0 bne0.
		{ specialize (even_or_odd (S a0)) as [aeven' | aodd].
		- destruct (evenI_evenF _ aeven') as [ad2 aeven].
		  specialize (even_or_odd b0) as [beven' | bodd'].
		  + destruct (evenI_evenF _ beven') as [bd2 beven].
		    assert (bd2ne0 : bd2 <> 0).
		    {	intros bd2eq0.
		    	by rewrite bd2eq0, multC in beven; unfold mult in beven; exact (bne0 beven). }
		    assert (ad2lea0 : ad2 <= a0).
		    {	destruct (le_0_n ad2) as [|ad2 _].
		    	by exact (le_0_n a0).
		    	unfold mult in aeven; rewrite (plusC _ 0) in aeven; minimize plus in aeven.
		    	apply eq_add_S in aeven.
		    	by apply (exists_plus_is_le (S ad2) a0); exists ad2; exact aeven. }
		    
		    specialize (IHa _ ad2lea0 _ bd2ne0) as [a' [b' [b'ne0 [multOK parityOK]]]].
		    exists a', b'. split; [by exact b'ne0 | split; [| by exact parityOK]].
		    rewrite aeven, beven, <-multA, <-multA.
		    assert (tmp : forall x y : nat, x = y -> 2 * x = 2 * y).
		    	by intros ? ? tmpeq; rewrite tmpeq; reflexivity.
		    by exact (tmp _ _ multOK).
		    
		  + exists (S a0), b0.
		    by split; [
		    	exact bne0
		    | split; [
		    	rewrite multC; reflexivity
		    |	intros _; exact bodd']].
		  
		- exists (S a0), b0.
		  split; [
		  	exact bne0
		  | split; [
		  	by rewrite multC; reflexivity
		  |	by intros aeven; contradiction (even_is_not_odd _ aeven aodd)]]. }
		intros b _; exists 0, 1; split; [by exact (not_eq_sym (n_Sn 0)) | split].
		by rewrite (multC _ 0); unfold mult; reflexivity.
		by intros _; exact odd_1. }
	
	specialize (finalH p q qne0) as [p' [q' [q'ne0 [multOK parityOK]]]].
	apply (sqrt2_not_even_over_even p' q' q'ne0 parityOK).
	(* p' * p' = 2 * q' * q' *)
	apply (mult_invertible q _ _ qne0);
	apply (mult_invertible q _ _ qne0).
	rewrite (multA _ p'), <-multOK, (multC _ p'), (multA _ p'), <-multOK.
	rewrite multA, (multC _ p), multA, H_sqrt2_is_rational.
	rewrite <-(multA _ q'), (multC 2 _), <-multA, <-multA.
	by reflexivity.
Qed.
