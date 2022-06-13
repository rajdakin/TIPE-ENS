Require Import Lists.List. Import ListNotations.

Inductive Lexem {T : Type} : Type :=
	| L_Immediate : T -> Lexem
	| L_UnaryMinus : Lexem
	| L_Plus : Lexem
	| L_Minus : Lexem
	| L_Times : Lexem
	| L_Divide : Lexem
	| L_Lparen : Lexem
	| L_Rparen : Lexem.
Definition validLexems {T} (l : list (@Lexem T)) : Prop :=
	let fix comp (l : list Lexem) (c : nat) (opAvail : Prop) (immAvail : Prop) := match l with
		| [] => c = O
		| L_Immediate _ :: tl => immAvail /\ (comp tl c True False)
		| L_UnaryMinus :: tl => immAvail /\ (comp tl c False True)
		| L_Plus :: tl => opAvail /\ (comp tl c True False)
		| L_Minus :: tl => opAvail /\ (comp tl c True False)
		| L_Times :: tl => opAvail /\ (comp tl c True False)
		| L_Divide :: tl => opAvail /\ (comp tl c True False)
		| L_Lparen :: tl => immAvail /\ (comp tl c False True)
		| L_Rparen :: tl => immAvail /\ (comp tl c False True) end
	in (l <> []) /\ (comp l 0 False True).
Fixpoint parenless {T} (l : list (@Lexem T)) : Prop := match l with
	| [] => True
	| L_Lparen :: _ | L_Rparen :: _ => False
	| _ :: tl => parenless tl end.

Inductive Operation {T : Type} : Type :=
	| O_Immediate : T -> Operation
	| O_UnaryMinus : Operation -> Operation
	| O_Plus : Operation -> Operation -> Operation
	| O_Minus : Operation -> Operation -> Operation
	| O_Times : Operation -> Operation -> Operation
	| O_Divide : Operation -> Operation -> Operation.
Inductive LexemToOperation_I {T} : list (@Lexem T) -> @Operation T -> Prop :=
	| L2O_Imm : forall v,
		LexemToOperation_I [L_Immediate v] (O_Immediate v)
	| L2O_UnaryMinus : forall l o,
		LexemToOperation_I l o ->
		LexemToOperation_I (L_UnaryMinus :: l) (O_UnaryMinus o)
	| L2O_Plus : forall l1 l2 o1 o2,
		LexemToOperation_I l1 o1 -> LexemToOperation_I l2 o2 ->
		LexemToOperation_I (l1 ++ L_Plus :: l2) (O_Plus o1 o2)
	| L2O_Minus : forall l1 l2 o1 o2,
		LexemToOperation_I l1 o1 -> LexemToOperation_I l2 o2 ->
		LexemToOperation_I (l1 ++ L_Minus :: l2) (O_Minus o1 o2)
	| L2O_Times : forall l1 l2 o1 o2,
		LexemToOperation_I l1 o1 -> LexemToOperation_I l2 o2 ->
		LexemToOperation_I (l1 ++ L_Times :: l2) (O_Times o1 o2)
	| L2O_Divide : forall l1 l2 o1 o2,
		LexemToOperation_I l1 o1 -> LexemToOperation_I l2 o2 ->
		LexemToOperation_I (l1 ++ L_Divide :: l2) (O_Divide o1 o2)
	| L2O_Parens : forall l o,
		LexemToOperation_I l o ->
		LexemToOperation_I (L_Lparen :: l ++ [L_Rparen]) o.

(*
( 2 + 3 ) * 5
[L_Lparen; L_Imm 2; L_Plus; L_Imm 3; L_Rparen; L_Mult; L_Imm 5]

[Tmp0] L_Lparen [L_Imm 2; L_Plus; L_Imm 3; L_Rparen; L_Times; L_Imm 5]
[Tmp0; Tmp0] L_Imm 2 [L_Plus; L_Imm 3; L_Rparen; L_Times; L_Imm 5]
[Tmp1 (O_Imm 2); Tmp0] L_Plus [L_Imm 3; L_Rparen; L_Times; L_Imm 5]
[Tmp2 (L_Plus, O_Imm 2); Tmp0] L_Imm 3 [L_Rparen; L_Times; L_Imm 5]
[Tmp1 (O_Plus (O_Imm 2) (O_Imm 3)); Tmp0] L_Rparen [L_Times; L_Imm 5]
[Tmp1 (O_Plus (O_Imm 2) (O_Imm 3))] L_Times [L_Imm 5]
[Tmp2 (L_Times, O_Plus (O_Imm 2) (O_Imm 3))] L_Imm 5 []

O_Mult (O_Plus (O_Imm 2) (O_Imm 3)) (O_Imm 5)
*)
Inductive L2O_F_Tmp {T} : Type :=
	| L2O_tmp0 : L2O_F_Tmp
	| L2O_tmp1 : @Operation T -> L2O_F_Tmp
	| L2O_tmp2 : @Lexem T -> L2O_F_Tmp
	| L2O_tmp3 : @Lexem T -> @Operation T -> L2O_F_Tmp.
Fixpoint L2O_F_inner {T} stack (l : list (@Lexem T)) :=
	match stack, l with
	| [], _ => None
	| st, [] => Some st
	| L2O_tmp0 :: st, L_Immediate v :: tl =>
		L2O_F_inner ((L2O_tmp1 (O_Immediate v)) :: st) tl
	| (L2O_tmp3 L_Plus ol) :: st, L_Immediate v :: tl =>
		L2O_F_inner ((L2O_tmp1 (O_Plus ol (O_Immediate v))) :: st) tl
	| (L2O_tmp3 L_Minus ol) :: st, L_Immediate v :: tl =>
		L2O_F_inner ((L2O_tmp1 (O_Minus ol (O_Immediate v))) :: st) tl
	| (L2O_tmp3 L_Times ol) :: st, L_Immediate v :: tl =>
		L2O_F_inner ((L2O_tmp1 (O_Times ol (O_Immediate v))) :: st) tl
	| (L2O_tmp3 L_Divide ol) :: st, L_Immediate v :: tl =>
		L2O_F_inner ((L2O_tmp1 (O_Divide ol (O_Immediate v))) :: st) tl
	| (L2O_tmp2 L_UnaryMinus) :: st, L_Immediate v :: tl =>
		L2O_F_inner ((L2O_tmp1 (O_UnaryMinus (O_Immediate v))) :: st) tl
	| L2O_tmp0 :: st, L_UnaryMinus :: tl =>
		L2O_F_inner ((L2O_tmp2 L_UnaryMinus) :: st) tl
	| (L2O_tmp1 o) :: st, L_Plus :: tl =>
		L2O_F_inner ((L2O_tmp3 L_Plus o) :: st) tl
	| (L2O_tmp1 o) :: st, L_Minus :: tl =>
		L2O_F_inner ((L2O_tmp3 L_Minus o) :: st) tl
	| (L2O_tmp1 o) :: st, L_Times :: tl =>
		L2O_F_inner ((L2O_tmp3 L_Times o) :: st) tl
	| (L2O_tmp1 o) :: st, L_Divide :: tl =>
		L2O_F_inner ((L2O_tmp3 L_Divide o) :: st) tl
	| L2O_tmp0 :: _, L_Lparen :: tl | (L2O_tmp2 _) :: _, L_Lparen :: tl | (L2O_tmp3 _ _) :: _, L_Lparen :: tl =>
		L2O_F_inner (L2O_tmp0 :: stack) tl
	| (L2O_tmp1 or) :: L2O_tmp0 :: st, L_Rparen :: tl =>
		L2O_F_inner ((L2O_tmp1 or) :: st) tl
	| (L2O_tmp1 or) :: (L2O_tmp3 L_Plus ol) :: st, L_Rparen :: tl =>
		L2O_F_inner ((L2O_tmp1 (O_Plus ol or)) :: st) tl
	| (L2O_tmp1 or) :: (L2O_tmp3 L_Minus ol) :: st, L_Rparen :: tl =>
		L2O_F_inner ((L2O_tmp1 (O_Minus ol or)) :: st) tl
	| (L2O_tmp1 or) :: (L2O_tmp3 L_Times ol) :: st, L_Rparen :: tl =>
		L2O_F_inner ((L2O_tmp1 (O_Times ol or)) :: st) tl
	| (L2O_tmp1 or) :: (L2O_tmp3 L_Divide ol) :: st, L_Rparen :: tl =>
		L2O_F_inner ((L2O_tmp1 (O_Divide ol or)) :: st) tl
	| (L2O_tmp1 or) :: (L2O_tmp2 L_UnaryMinus) :: st, L_Rparen :: tl =>
		L2O_F_inner ((L2O_tmp1 (O_UnaryMinus or)) :: st) tl
	| _, _ => None end.
Definition LexemToOperation_F {T} (l : list (@Lexem T)) :=
	match L2O_F_inner [L2O_tmp0] l with
	| Some [L2O_tmp1 op] => Some op
	| _ => None end.

Theorem L2O_I_nondeterministic :
	exists T (l : list (@Lexem T)) o1 o2, o1 <> o2 /\ LexemToOperation_I l o1 /\ LexemToOperation_I l o2.
Proof.
	exists
		nat,
		[L_Immediate 1; L_Plus; L_Immediate 1; L_Plus; L_Immediate 1],
		(O_Plus (O_Plus (O_Immediate 1) (O_Immediate 1)) (O_Immediate 1)),
		(O_Plus (O_Immediate 1) (O_Plus (O_Immediate 1) (O_Immediate 1))).
	split; [intros f; discriminate f|split].
	apply (L2O_Plus [L_Immediate 1; L_Plus; L_Immediate 1]).
	apply (L2O_Plus [L_Immediate 1]); apply L2O_Imm.
	apply L2O_Imm.
	apply (L2O_Plus [L_Immediate 1]).
	apply L2O_Imm.
	apply (L2O_Plus [L_Immediate 1]); apply L2O_Imm.
Qed.
Theorem L2O_incomplete : exists T (l : list (@Lexem T)) o, LexemToOperation_I l o /\ LexemToOperation_F l <> Some o.
Proof.
	exists
		nat,
		[L_Immediate 1; L_Plus; L_Immediate 1; L_Plus; L_Immediate 1],
		(O_Plus (O_Immediate 1) (O_Plus (O_Immediate 1) (O_Immediate 1))).
	split; [|compute; intros f; discriminate f].
	apply (L2O_Plus [L_Immediate 1]).
	apply L2O_Imm.
	apply (L2O_Plus [L_Immediate 1]); apply L2O_Imm.
Qed.

Definition balanced {T} (l : list (@Lexem T)) : Prop :=
	let fix inner n l := match l with
		| [] => n = O
		| L_Lparen :: tl => inner (S n) tl
		| L_Rparen :: tl => match n with S n => inner n tl | O => False end
		| _ :: tl => inner n tl end
	in inner O l.

Lemma L2O_inner_never_nil : forall {T} st (l : list (@Lexem T)),
	L2O_F_inner st l <> Some [].
Proof.
	intros T [|st sts] ll f.
	destruct ll; inversion f.
	generalize dependent sts; generalize dependent st; induction ll as [|l ll IHll]; intros st sts f.
	destruct st; [|destruct sts as [|[| |[]|[]] sts]|destruct l|destruct l]; inversion f.
	destruct l;
		try destruct st; try destruct l; try destruct l; try discriminate f; try exact (IHll _ _ f).
	1-8: try destruct sts; try destruct l; try destruct l; try discriminate f; try exact (IHll _ _ f).
Qed.
Lemma L2O_inner_some : forall {T} st1 st2 (l1 l2 : list (@Lexem T)) l,
	L2O_F_inner st1 l1 = Some l -> L2O_F_inner (st1 ++ st2) (l1 ++ l2) = L2O_F_inner (l ++ st2) l2.
Proof.
	intros T st1 st2 l1 l2 ltmp Heq.
	generalize dependent st1; induction l1 as [|l1 ll1 IHll1]; intros st1 Heq.
	simpl in Heq; simpl; f_equal.
	destruct st1.
	discriminate Heq.
	destruct l; try solve [inversion Heq; subst; exact (eq_refl _)].
	destruct st1; try solve [inversion Heq; subst; exact (eq_refl _)].
	1,2,3: destruct l; try solve [inversion Heq; subst; exact (eq_refl _)].
	1,2: destruct l; solve [inversion Heq; subst; exact (eq_refl _)].
	destruct st1 as [|[|ol|l0|l0 ol] sts1].
	simpl in Heq; inversion Heq.
	1,2,3,4: destruct l1 as [v| | | | | | |].
	1,2,7: rewrite <-(IHll1 _ Heq); exact (eq_refl _).
	1,2,3,4,5: discriminate Heq.
	1,2: destruct sts1; [discriminate Heq|destruct l; try discriminate Heq; destruct l; discriminate Heq].
	1,2,3,4:
	 destruct sts1;
	 [destruct st2; [|destruct l; try destruct l]|destruct l; try destruct l]; rewrite <-(IHll1 _ Heq); exact (eq_refl _).
	destruct sts1; [discriminate Heq|destruct l; try destruct l; discriminate Heq].
	destruct sts1;
		[discriminate Heq
		|destruct l; [rewrite <-(IHll1 _ Heq); exact (eq_refl _)|discriminate Heq| |]; destruct l;
		  try discriminate Heq; rewrite <-(IHll1 _ Heq); exact (eq_refl _)].
	1-16:
	 destruct l0; try discriminate Heq; rewrite <-(IHll1 _ Heq); exact (eq_refl _).
Qed.

Theorem L2O_sound : forall {T} (l : list (@Lexem T)) o, LexemToOperation_F l = Some o -> LexemToOperation_I l o.
Proof.
	assert (nat_ind2 : forall (P : nat -> Prop),
		P 0 -> P 1 -> (forall n, P n -> P (S (S n))) -> forall n, P n).
	{ clear; intros P H0 H1 IH.
	  assert (forall n, P n /\ P (S n)).
	  { intros n; induction n as [|n [IHn IHSn]]; [split; [exact H0|exact H1]|split; [exact IHSn|exact (IH _ IHn)]]. }
	  intros n; exact (proj1 (H _)). }
	assert (list_ind2 : forall A (P : list A -> Prop),
		P [] -> (forall a, P [a]) -> (forall ll, P ll -> forall l r, P (l :: ll ++ [r])) -> forall l, P l).
	{ clear - nat_ind2; intros A P H0 H1 IH.
	  assert (H : forall n ll, length ll = n -> P ll).
	  { intros n; induction n as [| |n IHn] using nat_ind2.
	    intros [|a ll] H; [exact H0|discriminate H].
	    intros [|a [|b ll]] H; try discriminate H; exact (H1 _).
	    intros [|l ll] H.
	    exact H0.
	    rewrite <-(rev_involutive ll) in *; remember (rev ll) as rll eqn:tmp; clear ll tmp;
	     destruct rll as [|r rll].
	    exact (H1 _).
	    simpl; apply IH, IHn; apply eq_add_S, eq_add_S; rewrite <-H; simpl; f_equal.
	    symmetry; exact (last_length _ _). }
	  intros l; exact (H _ l (eq_refl _)). }
	unfold LexemToOperation_F; intros T l o; generalize dependent l;
	 induction o as [v|o|ol IHl or IHr|ol IHl or IHr|ol IHl or IHr|ol IHl or IHr];
	 intros l Heq.
	induction l as [|[w| | | | | | |]|ll IHll [w| | | | | | |] r] using list_ind2; try discriminate Heq.
	injection Heq as eq; subst; exact (L2O_Imm _).
	clear IHll; remember (ll ++ [r]) as llr eqn:eqtmp; clear r ll eqtmp; simpl in Heq.
	destruct llr as [|[x| | | | | | |] ll]; try discriminate Heq; simpl in Heq.
	injection Heq as eq; subst; exact (L2O_Imm _).
	exfalso; remember ([L2O_tmp3 L_Plus (O_Immediate w)]) as ll2o eqn:eqll2o;
	 assert (match ll2o with
		| [] => False
		| L2O_tmp0 :: tl | L2O_tmp1 (O_Immediate _) :: tl =>
			let fix inner l := match l with [] => False | L2O_tmp0 :: tl => inner tl | _ => True end in inner tl
		| _ => True end)
	  by (subst; exact I);
	 clear eqll2o; generalize dependent ll2o.
	induction ll as [|[x| | | | | | |] ll IHll]; intros l2o Heq l2one; try discriminate Heq; simpl in Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	injection Heq as eq; subst; exact l2one.
	destruct l.
	discriminate Heq.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	exact (IHll _ Heq l2one).
	destruct l2o.
	discriminate Heq.
	destruct l.
	discriminate Heq.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l2o.
	exact l2one.
	destruct l.
	exact (IHll _ Heq I).
	destruct l2o.
	discriminate Heq.
	destruct l.
	discriminate Heq.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	exact (IHll _ Heq I).
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	exact (IHll _ Heq I).
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	exact (IHll _ Heq I).
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	exact (IHll _ Heq I).
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	exact (IHll _ Heq l2one).
	destruct l2o.
	discriminate Heq.
	destruct l.
	discriminate Heq.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l2o.
	discriminate Heq.
	destruct l.
	discriminate Heq.
	destruct l2o.
	discriminate Heq.
	destruct l.
	exact (IHll _ Heq l2one).
	discriminate Heq.
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	
	exfalso; remember ([L2O_tmp3 L_Minus (O_Immediate w)]) as ll2o eqn:eqll2o;
	 assert (match ll2o with
		| [] => False
		| L2O_tmp0 :: tl | L2O_tmp1 (O_Immediate _) :: tl =>
			let fix inner l := match l with [] => False | L2O_tmp0 :: tl => inner tl | _ => True end in inner tl
		| _ => True end)
	  by (subst; exact I);
	 clear eqll2o; generalize dependent ll2o.
	induction ll as [|[x| | | | | | |] ll IHll]; intros l2o Heq l2one; try discriminate Heq; simpl in Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	injection Heq as eq; subst; exact l2one.
	destruct l.
	discriminate Heq.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	exact (IHll _ Heq l2one).
	destruct l2o.
	discriminate Heq.
	destruct l.
	discriminate Heq.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l2o.
	exact l2one.
	destruct l.
	exact (IHll _ Heq I).
	destruct l2o.
	discriminate Heq.
	destruct l.
	discriminate Heq.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	exact (IHll _ Heq I).
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	exact (IHll _ Heq I).
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	exact (IHll _ Heq I).
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	exact (IHll _ Heq I).
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	exact (IHll _ Heq l2one).
	destruct l2o.
	discriminate Heq.
	destruct l.
	discriminate Heq.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l2o.
	discriminate Heq.
	destruct l.
	discriminate Heq.
	destruct l2o.
	discriminate Heq.
	destruct l.
	exact (IHll _ Heq l2one).
	discriminate Heq.
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	
	exfalso; remember ([L2O_tmp3 L_Times (O_Immediate w)]) as ll2o eqn:eqll2o;
	 assert (match ll2o with
		| [] => False
		| L2O_tmp0 :: tl | L2O_tmp1 (O_Immediate _) :: tl =>
			let fix inner l := match l with [] => False | L2O_tmp0 :: tl => inner tl | _ => True end in inner tl
		| _ => True end)
	  by (subst; exact I);
	 clear eqll2o; generalize dependent ll2o.
	induction ll as [|[x| | | | | | |] ll IHll]; intros l2o Heq l2one; try discriminate Heq; simpl in Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	injection Heq as eq; subst; exact l2one.
	destruct l.
	discriminate Heq.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	exact (IHll _ Heq l2one).
	destruct l2o.
	discriminate Heq.
	destruct l.
	discriminate Heq.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l2o.
	exact l2one.
	destruct l.
	exact (IHll _ Heq I).
	destruct l2o.
	discriminate Heq.
	destruct l.
	discriminate Heq.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	exact (IHll _ Heq I).
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	exact (IHll _ Heq I).
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	exact (IHll _ Heq I).
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	exact (IHll _ Heq I).
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	exact (IHll _ Heq l2one).
	destruct l2o.
	discriminate Heq.
	destruct l.
	discriminate Heq.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l2o.
	discriminate Heq.
	destruct l.
	discriminate Heq.
	destruct l2o.
	discriminate Heq.
	destruct l.
	exact (IHll _ Heq l2one).
	discriminate Heq.
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	
	exfalso; remember ([L2O_tmp3 L_Divide (O_Immediate w)]) as ll2o eqn:eqll2o;
	 assert (match ll2o with
		| [] => False
		| L2O_tmp0 :: tl | L2O_tmp1 (O_Immediate _) :: tl =>
			let fix inner l := match l with [] => False | L2O_tmp0 :: tl => inner tl | _ => True end in inner tl
		| _ => True end)
	  by (subst; exact I);
	 clear eqll2o; generalize dependent ll2o.
	induction ll as [|[x| | | | | | |] ll IHll]; intros l2o Heq l2one; try discriminate Heq; simpl in Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	injection Heq as eq; subst; exact l2one.
	destruct l.
	discriminate Heq.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	exact (IHll _ Heq l2one).
	destruct l2o.
	discriminate Heq.
	destruct l.
	discriminate Heq.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l2o.
	exact l2one.
	destruct l.
	exact (IHll _ Heq I).
	destruct l2o.
	discriminate Heq.
	destruct l.
	discriminate Heq.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	exact (IHll _ Heq I).
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	exact (IHll _ Heq I).
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	exact (IHll _ Heq I).
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	exact (IHll _ Heq I).
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	exact (IHll _ Heq l2one).
	destruct l2o.
	discriminate Heq.
	destruct l.
	discriminate Heq.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l2o.
	discriminate Heq.
	destruct l.
	discriminate Heq.
	destruct l2o.
	discriminate Heq.
	destruct l.
	exact (IHll _ Heq l2one).
	discriminate Heq.
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	
	clear IHll; remember (ll ++ [r]) as llr eqn:eqtmp; clear r ll eqtmp; simpl in Heq.
	exfalso; remember ([L2O_tmp2 L_UnaryMinus]) as ll2o eqn:eqll2o;
	 assert (match ll2o with
		| [] => False
		| L2O_tmp0 :: tl | L2O_tmp1 (O_Immediate _) :: tl =>
			let fix inner l := match l with [] => False | L2O_tmp0 :: tl => inner tl | _ => True end in inner tl
		| _ => True end)
	  by (subst; exact I);
	 clear eqll2o; generalize dependent ll2o.
	induction llr as [|[x| | | | | | |] ll IHll]; intros l2o Heq l2one; try discriminate Heq; simpl in Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	injection Heq as eq; subst; exact l2one.
	destruct l.
	discriminate Heq.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	exact (IHll _ Heq l2one).
	destruct l2o.
	discriminate Heq.
	destruct l.
	discriminate Heq.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l2o.
	exact l2one.
	destruct l.
	exact (IHll _ Heq I).
	destruct l2o.
	discriminate Heq.
	destruct l.
	discriminate Heq.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	exact (IHll _ Heq I).
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	exact (IHll _ Heq I).
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	exact (IHll _ Heq I).
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	discriminate Heq.
	destruct l2o.
	exact (IHll _ Heq I).
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l.
	exact (IHll _ Heq l2one).
	destruct l2o.
	discriminate Heq.
	destruct l.
	discriminate Heq.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l.
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	exact (IHll _ Heq I).
	destruct l; exact (IHll _ Heq I).
	destruct l2o.
	discriminate Heq.
	destruct l.
	discriminate Heq.
	destruct l2o.
	discriminate Heq.
	destruct l.
	exact (IHll _ Heq l2one).
	discriminate Heq.
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l; try discriminate Heq; exact (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	
	destruct r as [x| | | | | | |]; swap 1 8.
	apply L2O_Parens, IHll; rewrite <-Heq; symmetry; simpl.
	assert (H : LexemToOperation_F (L_Lparen :: ll ++ [L_Rparen]) = LexemToOperation_F ll).
	clear; unfold LexemToOperation_F; simpl.
	destruct (L2O_F_inner [L2O_tmp0] ll) as [l|] eqn:eq1.
	specialize (L2O_inner_some [L2O_tmp0] [L2O_tmp0] ll [L_Rparen] _ eq1) as tmp;
	  simpl in tmp; rewrite tmp; clear tmp.
	repeat (destruct l as [|[|?|[]|[]] l]; try exact (eq_refl _); simpl).
	replace (L2O_F_inner [L2O_tmp0; L2O_tmp0] (ll ++ [L_Rparen])) with (@None (list (@L2O_F_Tmp T))).
	exact (eq_refl _).
	symmetry; remember [L2O_tmp0] as tmp0 eqn:tmp;
	replace (L2O_tmp0 :: tmp0) with (tmp0 ++ [L2O_tmp0]) by (subst; exact (eq_refl _));
	 assert (H : tmp0 <> []) by (subst; discriminate); clear tmp;
	 remember [L2O_tmp0] as st2 eqn:tmp; clear tmp;
	 remember [L_Rparen] as l2 eqn:tmp; clear tmp;
	 generalize dependent l2; generalize dependent tmp0; induction ll as [|[] ll IHll]; intros tmp0 eq1 H0 l2.
	destruct tmp0.
	contradiction (H0 eq_refl).
	destruct l; try destruct l; try discriminate eq1.
	destruct tmp0; [|destruct l; try destruct l]; discriminate eq1.
	destruct tmp0; [contradiction (H0 eq_refl)|simpl; clear H0].
	destruct l.
	rewrite app_comm_cons; apply IHll; [exact eq1|discriminate].
	destruct (tmp0 ++ st2); [|destruct l; try destruct l]; exact eq_refl.
	destruct l; try exact eq_refl; rewrite app_comm_cons; apply IHll; [exact eq1|discriminate].
	destruct l; try exact eq_refl; rewrite app_comm_cons; apply IHll; try exact eq1; discriminate.
	destruct tmp0; [contradiction (H0 eq_refl)|simpl; clear H0].
	destruct l.
	rewrite app_comm_cons; apply IHll; [exact eq1|discriminate].
	destruct (tmp0 ++ st2); [|destruct l; try destruct l]; exact eq_refl.
	destruct l; exact eq_refl.
	destruct l; exact eq_refl.
	destruct tmp0; [contradiction (H0 eq_refl)|simpl; clear H0].
	destruct l.
	exact eq_refl.
	destruct tmp0.
	simpl in *; destruct st2.
	apply (IHll [L2O_tmp3 L_Plus o]); [exact eq1|discriminate].
	destruct l; try destruct l.
	1-18: apply (IHll [L2O_tmp3 L_Plus o]); [exact eq1|discriminate].
	simpl; destruct l; [| |destruct l|destruct l].
	19,20: destruct l.
	1-18: apply (IHll _ eq1); discriminate.
	1-16: exact eq_refl.
	1-5: destruct tmp0; [contradiction (H0 eq_refl)|simpl; destruct l; [| |destruct l|destruct l]; clear H0];
	  try exact eq_refl.
	1-3,5,22: destruct tmp0; [destruct st2|].
	1,4,7: apply (IHll _ eq1); discriminate.
	7: exact eq_refl.
	1-8,10-11: destruct l.
	3,4,7,8,11,12,15,16,19,20,23,24,27,28,31,32,35,36,39,40: destruct l.
	all: try exact eq_refl.
	all: try (apply (IHll _ eq1); discriminate).
	simpl.
	all: simpl in *.
	
	
	remember (rev tmp0) as rtmp0 eqn:eq; apply (f_equal (@rev _)) in eq; rewrite rev_involutive in eq; symmetry in eq;
	 subst.
 	specialize (fun H => @eq_ind_r _ [] (fun l => ~(rev l <> [])) (fun f => f (eq_refl _)) rtmp0 H H0) as H;
	 clear H0.
	destruct rtmp0; [contradiction (H eq_refl)|clear H; simpl rev in *].
	generalize dependent l; generalize dependent st2; induction rtmp0; intros st2 l eq1;
	 simpl rev in *; simpl app in *.
	destruct l; try destruct l; discriminate eq1.
	destruct l.
	exact (eq_refl _).
	destruct tmp0.
	discriminate eq1.
	destruct l; try destruct l; discriminate eq1.
	destruct l; discriminate eq1.
	destruct l; discriminate eq1.
	destruct tmp0; [contradiction (H0 (eq_refl _))|clear H0].
	destruct l; induction ll.
	destruct tmp0; [|destruct l; [| |destruct l|destruct l]]; discriminate eq1.
	destruct tmp0.
	destruct a; try exact (eq_refl _).
	
	simpl in *.
	
	destruct tmp0; try exact (eq_refl _); simpl.
	destruct l.
	exact (eq_refl _).
	destruct tmp0; try destruct l; try destruct l; try discriminate eq1.
	1,2: destruct l; exact (eq_refl _).
	destruct tmp0; simpl in *.
	destruct ll; simpl; try destruct l; try exact (eq_refl _).
	exact (IHll _ eq1).
	exact (eq_refl _).
	exact eq1.
	exact eq1.
	1,2,3,4: destruct tmp0; simpl in *.
	1,5,9,13: exact (eq_refl _).
	1,4,7,10: exact (IHll _ eq1).
	1,3,5,7: exact eq1.
	1,2,3,4: exact eq1.
	destruct tmp0; simpl in *.
	exact (IHll _ eq1).
	exact (eq_refl _).
	exact eq1.
	exact eq1.
	
	clear; induction ll as [|[] ll IHll]; unfold LexemToOperation_F; simpl.
	exact (eq_refl _).
	specialize (L2O_inner_some [L2O_tmp0] [L2O_tmp0] ll [L_Rparen] [L2O_tmp1 (O_Immediate t)]) as tmp.
	
	specialize (L2O_inner_some [L2O_tmp0] [L2O_tmp0] ll [L_Rparen] [L2O_tmp1 (O_Immediate v)]) as tmp;
	 simpl in tmp; rewrite tmp.
	
	
	destruct (rev ll) as [|a l] eqn:eq; apply (f_equal (@rev _)) in eq; rewrite rev_involutive in eq; subst.
	discriminate Heq.
	destruct a; simpl in IHll2, Heq; simpl; remember (rev l) as ll eqn:tmp; clear l tmp.
	
	assert (list_revind : forall {A} (P : list A -> Prop), P [] -> (forall a l, P l -> P (l ++ [a])) -> forall l, P l).
	{ clear; intros A P I0 IH l; rewrite <-rev_involutive; remember (rev l) as rl eqn:tmp; clear l tmp.
	  induction rl as [|v rl IHrl].
	  exact I0.
	  exact (IH _ _ IHrl). }
	induction ll using list_revind.
	discriminate Heq.
	destruct a.
	specialize (IHll2 Heq).
	
	destruct l2o.
	exact l2one.
	destruct l2o.
	destruct l.
	exact l2one.
	discriminate Heq.
	destruct l; try discriminate Heq; apply (IHll _ Heq I).
	destruct l; try discriminate Heq; apply (IHll _ Heq I).
	destruct l.
	exact l2one.
	discriminate Heq.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; try discriminate Heq; apply (IHll _ Heq I).
	destruct l; try discriminate Heq; apply (IHll _ Heq I).
	destruct l2o.
	exact l2one.
	destruct l2o.
	destruct l.
	exact l2one.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l.
	apply (IHll _ Heq I).
	destruct l0.
	discriminate Heq.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l2o.
	destruct l.
	exact l2one.
	apply (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l.
	discriminate Heq.
	destruct l0.
	apply (IHll _ Heq I).
	apply (IHll _ Heq I).
	destruct l; apply (IHll _ Heq I).
	destruct l; apply (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l2o.
	destruct l.
	exact l2one.
	apply (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l.
	discriminate Heq.
	destruct l0.
	apply (IHll _ Heq I).
	apply (IHll _ Heq I).
	destruct l; apply (IHll _ Heq I).
	destruct l; apply (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l2o.
	destruct l.
	exact l2one.
	apply (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l.
	discriminate Heq.
	destruct l0.
	apply (IHll _ Heq I).
	apply (IHll _ Heq I).
	destruct l; apply (IHll _ Heq I).
	destruct l; apply (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l2o.
	destruct l.
	exact l2one.
	apply (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l.
	discriminate Heq.
	destruct l0.
	apply (IHll _ Heq I).
	apply (IHll _ Heq I).
	destruct l; apply (IHll _ Heq I).
	destruct l; apply (IHll _ Heq I).
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l2o.
	exact l2one.
	destruct l2o.
	destruct l.
	exact l2one.
	discriminate Heq.
	destruct l; apply (IHll _ Heq I).
	destruct l; apply (IHll _ Heq I).
	destruct l.
	apply (IHll _ Heq I).
	destruct l0.
	discriminate Heq.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; apply (IHll _ Heq I).
	destruct l; apply (IHll _ Heq I).
	destruct l2o.
	exact l2one.
	destruct l2o.
	destruct l.
	exact l2one.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	destruct l.
	discriminate Heq.
	destruct l0.
	apply (IHll _ Heq); try discriminate.
	intros Heq2; injection Heq2 as eqo eql2o; subst.
	apply (IHll _ Heq I).
	destruct l; apply (IHll _ Heq I).
	destruct l; apply (IHll _ Heq I).
	destruct l; apply (IHll _ Heq I).
	destruct l; apply (IHll _ Heq I).
	
	destruct l2o.
	exact l2one.
	discriminate Heq.
	destruct l; try discriminate Heq; apply (IHll _ Heq I).
	destruct l; try discriminate Heq; apply (IHll _ Heq I).
	destruct l2o.
	exact l2one.
	discriminate Heq.
	destruct l; discriminate Heq.
	destruct l; discriminate Heq.
	1,2,3,4: destruct l2o; [
	discriminate Heq |
	apply (IHll _ Heq I) |
	destruct l; discriminate Heq |
	destruct l; discriminate Heq ].
	destruct l2o.
	exact l2one.
	apply (IHll _ Heq I).
	
	unfold LexemToOperation_F; intros T l; induction l as [|v l IHl]; intros o Heq.
	inversion Heq.
	
	intros T l; induction l as [|[] [|l ll] IHll]; intros o Heq; try solve [inversion Heq].
	injection Heq as eqo; subst. constructor.
	unfold LexemToOperation_F in Heq.*)

Lemma L2O_inner_none : forall {T} st1 sts1 sts2 (ll1 ll2 : list (@Lexem T)),
	L2O_F_inner (st1 :: sts1) ll1 = None -> L2O_F_inner (st1 :: sts1 ++ sts2) (ll1 ++ ll2) = None.
Proof.
	intros T st1 sts1 sts2 ll1 ll2 Heq.
	generalize dependent sts1; generalize dependent st1; induction ll1 as [|l12 ll1 IHll1]; intros st1 sts1 Heq.
	destruct st1.
	discriminate Heq.
	destruct sts1; [|destruct l; [| |destruct l|destruct l]]; discriminate Heq.
	1,2: destruct l; discriminate Heq.
	destruct st1.
	destruct l12; try exact (eq_refl _); try exact (IHll1 _ _ Heq).
	destruct sts1.
	destruct l12; try discriminate Heq.
	1,2: destruct sts2; [|destruct l; [| |destruct l|destruct l]]; exact (eq_refl _).
	1,2,3,4,5: destruct sts2; [|destruct l; [| |destruct l|destruct l]]; exact (IHll1 _ _ Heq).
	destruct sts2; [|destruct l; [| |destruct l|destruct l]]; try exact (eq_refl _).
	simpl in Heq; simpl.
	[|destruct l; [| |destruct l|destruct l]]; discriminate Heq.
	
	simpl in Heq; simpl.
	destruct st1.
	simpl.
	destruct l; try solve [inversion Heq; subst; exact (eq_refl _)].
	destruct st1; try solve [inversion Heq; subst; exact (eq_refl _)].
	1,2,3: destruct l; try solve [inversion Heq; subst; exact (eq_refl _)].
	1,2: destruct l; solve [inversion Heq; subst; exact (eq_refl _)].
	destruct st1 as [|[|ol|l0|l0 ol] sts1].
	simpl in Heq; inversion Heq.
	1,2,3,4: destruct l1 as [v| | | | | | |].
	1,2,7: rewrite <-(IHll1 _ Heq); exact (eq_refl _).
	1,2,3,4,5: discriminate Heq.
	1,2: destruct sts1; [discriminate Heq|destruct l; try discriminate Heq; destruct l; discriminate Heq].
	1,2,3,4,5:
	 destruct sts1;
	 [destruct st2; [|destruct l; try destruct l]|destruct l; try destruct l]; rewrite <-(IHll1 _ Heq); exact (eq_refl _).
	destruct sts1;
		[discriminate Heq
		|destruct l; [rewrite <-(IHll1 _ Heq); exact (eq_refl _)|discriminate Heq| |]; destruct l;
		  try discriminate Heq; rewrite <-(IHll1 _ Heq); exact (eq_refl _)].
	1-16:
	 destruct l0; try discriminate Heq; rewrite <-(IHll1 _ Heq); exact (eq_refl _).
Qed.
Lemma L2O_inner_extend : forall {T} st1 st2 st3 l (l1 l2 l3 : list (@Lexem T)),
	L2O_F_inner st1 (l :: l1 ++ l2) = L2O_F_inner st2 l2 ->
	L2O_F_inner (st1 ++ st3) (l :: l1 ++ l2 ++ l3) = L2O_F_inner (st2 ++ st3) (l2 ++ l3).
Proof.
	intros T st1 st2 st3 l ll1 ll2 ll3 Heq; destruct (L2O_F_inner st2 ll2) as [ltmp|] eqn:Heq2.
	specialize (L2O_inner_some st1 st3 (l :: ll1 ++ ll2) ll3 ltmp Heq) as H1.
	rewrite app_comm_cons, <-app_assoc, <-app_comm_cons in H1; rewrite H1.
	symmetry.
	apply L2O_inner_some; exact Heq2.
	
	intros T st1 st2 st3 l l1 l2 l3 Heq; destruct (L2O_F_inner st2 l2) as [ltmp|] eqn:Heq2.
	rewrite app_comm_cons; apply (L2O_inner_some st1 st3 (l :: l1) (l2 ++ l3) st2).
	clear st3 l3; generalize dependent ltmp; generalize dependent st2; generalize dependent st1;
	induction l2 as [|l2 ll2 IHll2]; intros st1 st2 ltmp Heq2 Heq.
	rewrite app_nil_r in Heq; simpl in Heq2; destruct st2; [discriminate Heq2|rewrite Heq, <-Heq2; clear].
	destruct l0; try exact (eq_refl _).
	destruct st2; try exact (eq_refl _).
	1,2,3: destruct l; try exact (eq_refl _).
	1,2: destruct l; exact (eq_refl _).
	destruct st1 as [|st1 sts1]; [discriminate Heq|];
	destruct st2 as [|st2 sts2]; [discriminate Heq2|];
	destruct st1; destruct st2; simpl in Heq, Heq2 |-.
	destruct l; try discriminate Heq; destruct l2; try discriminate Heq2.
	specialize (IHll2 _ _ _ Heq2 Heq).
	try exact (IHll2 _ _ _ Heq2 Heq).
	apply IHll2.
	
	intros T st1 st2 st3 l1; generalize dependent st3; generalize dependent st2; generalize dependent st1;
	induction l1 as [|v1 l1 IHl1]; intros st1 st2 st3 l2 l3 Heq.
	induction l2 as [|v2 l2 IHl2]; simpl in *.
	destruct st1 as [|st1 sts1]; destruct st2 as [|st2 sts2].
	exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l]; discriminate Heq.
	destruct st1 as [| | |]; [|destruct sts1 as [|[| |[]|[]]]|destruct l|destruct l]; discriminate Heq.
	destruct st1 as [| | |]; [|destruct sts1 as [|[| |[]|[]]]|destruct l|destruct l].
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	destruct st2 as [| | |]; [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l];
		inversion Heq; subst; exact (eq_refl _).
	
	destruct st1 as [|st1 sts1];
	destruct st2 as [|st2 sts2].
	exact (eq_refl _).
	destruct st2; destruct v2. [|destruct sts2 as [|[| |[]|[]]]|destruct l|destruct l]; try discriminate Heq.
	destruct st1; destruct st2; inversion Heq; subst; try exact (eq_refl _).
	simpl in Heq.
	intros T st1 st2 st3 l1 l2 l3 Hl; induction l3 as [|v l3 IHl3].
	rewrite app_nil_r; induction l2 as [|v l2 IHl2].
	rewrite app_nil_r in *; induction st3 as [|v3 st3 IHst3].
	rewrite app_nil_r, app_nil_r; exact Hl.
	induction st1 as [|v1 st1]; simpl in *.
	destruct (st2 ++ v3 :: st3) eqn:eq233; [destruct st2; inversion eq233|].
	destruct l.
	destruct st2; injection eq233 as eq1; subst.
	simpl in IHst3; destruct l0.
	destruct l1. simpl; exact (eq_refl _). destruct l; try solve [inversion Hl].
	
	rewrite app_nil_r; induction st3 as [|v st].
	rewrite app_nil_r, app_nil_r; exact Hl.
	
	intros T st1 st2 st3 l1 l2 H1; generalize dependent st2; induction l1 as [|v l1 IHl1]; intros st2 H1.
	destruct st1; [|destruct l]; try destruct st1; try destruct l; try destruct l;
		simpl in H1; injection H1 as eq; subst; simpl; exact (eq_refl _).
	

	match L2O_F_inner [L2O_tmp1 o] l2 with Some [L2O_tmp1 o] => Some o | _ => None end.

Lemma L2O_balanced : forall {T} (l1 l2 : list (@Lexem T)) o,
	LexemToOperation_F l1 = Some o ->
	LexemToOperation_F (L_Lparen :: l1 ++ L_Rparen :: l2) =
	match L2O_F_inner [L2O_tmp1 o] l2 with Some [L2O_tmp1 o] => Some o | _ => None end.
Proof.
	unfold LexemToOperation_F; intros T l1 l2 o Ho; simpl.
	; induction l1 as [|[] l1 IHl1]; intros l2 o Ho.
	inversion Ho.
	simpl.
	simpl in Ho.

Theorem L2O_sound : forall {T} (l : list (@Lexem T)) o, LexemToOperation_F l = Some o -> LexemToOperation_I l o.
Proof.
	unfold LexemToOperation_F; intros T l; induction l as [|v l IHl]; intros o Heq.
	inversion Heq.
	
	intros T l; induction l as [|[] [|l ll] IHll]; intros o Heq; try solve [inversion Heq].
	injection Heq as eqo; subst. constructor.
	unfold LexemToOperation_F in Heq.*)

(* - + : 2 parens *)
(* * / : 3 parens *)

(* 2 + 3 / 5 ==> ((2 + (((3)) / 5))) = 2 + (3 / 5) *)
(* 2 + (3 / 5) ==> ((2 + ((((3)) / 5)))) = 2 + (3 / 5) *)
(* (2 + 3) / 5 ==> (((2 + (((3))) / 5))) = 2 + 3 / 5 *)
