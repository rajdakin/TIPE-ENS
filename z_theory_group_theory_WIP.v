Require Import base.
Require Import z_theory_base.
Require Import z_theory_bool.
Require Import z_theory_N.
Require Import Classical.

Definition sig2ex_l {A : Type} {P : A -> Prop} (u : {x : A | P x}) := let (ret, _) := u in ret.
Definition sig2ex_rl {A : Type} {P : A -> Prop} (u : {x : A | P x}) :=
	match u return A with exist _ x Px => x end.
Definition sig2ex_rr {A : Type} {P : A -> Prop} (u : {x : A | P x}) :=
	match u return P (sig2ex_rl u) with exist _ x Px => Px end.

Section Functions.
Section GenericFunctions.
Variable E : Ensemble.
Variable F : Ensemble.
Variable f : Ensemble.
Hypothesis f_fun : f inE total_application_set E F.
Let g := let (g, _) := total_application_cons f f_fun in g.
Definition injective : Prop := forall x y : _, forall (xin : x inE E) (yin : y inE E),
	g x xin =E g x xin -> x =E y.
Definition surjective : Prop := Eforall y in F, Eexists x in E as xin, g x xin = y.
Definition bijective : Prop := injective /\ surjective.
End GenericFunctions.

Section Relations.
Section RelationsDefinition.
Context {E F : Ensemble}.
Let A := pi1e E.
Let f := pi2e E.
Let B := pi1e F.
Let g := pi2e F.
Record relation : Type := {
	rel_r : A -> B -> Prop
;	rel_welldef : forall a a', forall b b',
	 f a =E f a' -> g b =E g b' -> rel_r a b <-> rel_r a' b'
}.
End RelationsDefinition.
Arguments relation E F : clear implicits.
Section RelationsDefinition.
Context {E : Ensemble}.
Let A := pi1e E.
Let f := pi2e E.
Record rel_same_ens := { relse_rel : relation E E }.
End RelationsDefinition.
Arguments rel_same_ens E : clear implicits.

Section GeneralRelations.
Context {E F : Ensemble}.
Variable rel : relation E F.
Let A := pi1e E.
Let f := pi2e E.
Let B := pi1e F.
Let g := pi2e F.
Notation "'R'" := rel.(rel_r).

Definition rel2_incl {C D} (rel2 : relation C D) :=
	let f' := pi2e C in let g' := pi2e D in
	let R' := rel2.(rel_r) in
	exists AtoC : A -> pi1e C, exists BtoD : B -> pi1e D,
	(forall a, f a =E f' (AtoC a)) /\
	(forall b, g b =E g' (BtoD b)) /\
	(forall a b, R a b -> R' (AtoC a) (BtoD b)).
Definition rel2_equiv {C D} (rel2 : relation C D) :=
	let f' := pi2e C in let g' := pi2e D in
	let R' := rel2.(rel_r) in
	exists AtoC : A -> pi1e C, exists BtoD : B -> pi1e D,
	exists CtoA : pi1e C -> A, exists DtoB : pi1e D -> B,
	((forall a, f a =E f' (AtoC a)) /\
	(forall b, g b =E g' (BtoD b))) /\
	((forall c, f' c =E f (CtoA c)) /\
	(forall d, g' d =E g (DtoB d))) /\
	((forall a b, R a b <-> R' (AtoC a) (BtoD b)) /\
	(forall c d, R' c d <-> R (CtoA c) (DtoB d))).
End GeneralRelations.
Section GeneralRelations.
Lemma rel_equiv_is_incl {E F C D} : forall (rel : relation E F) (rel2 : relation C D),
	rel2_equiv rel rel2 -> rel2_incl rel rel2.
Proof.
	intros rel rel2 [AtoC [BtoD [CtoA [DtoB [[HA2C HB2D] [[HC2A HD2B] [Hrel _]]]]]]];
	  exists AtoC, BtoD; split; [|split].
	by intros a; exact (HA2C a).
	by intros b; exact (HB2D b).
	by intros a b; exact (proj1 (iff_and (Hrel a b))).
Qed.
Lemma rel_equiv_sym {E F C D} : forall (rel : relation E F) (rel2 : relation C D),
	rel2_equiv rel rel2 -> rel2_equiv rel2 rel.
Proof.
	intros rel rel2 [AtoC [BtoD [CtoA [DtoB [[HA2C HB2D] [[HC2A HD2B] [Hrell Hrelr]]]]]]];
	  exists CtoA, DtoB, AtoC, BtoD; split; split; [| |split|split].
	by exact HC2A.
	by exact HD2B.
	by exact HA2C.
	by exact HB2D.
	by exact Hrelr.
	by exact Hrell.
Qed.
Definition rel2_incl_sameset {E F} (rel rel2 : relation E F) :=
	let R := rel.(rel_r) in let R' := rel2.(rel_r) in
	forall a b, R a b -> R' a b.
Lemma rel2_incl_sameset_is_incl {E F} : forall rel rel2 : relation E F,
	rel2_incl_sameset rel rel2 -> rel2_incl rel rel2.
Proof.
	intros r r2 rinclr2; exists (fun a => a), (fun b => b); split; [|split].
	1,2: by intros ?; exact (Eeq_refl _).
	by intros a b; exact (rinclr2 a b).
Qed.
Lemma rel2_incl_is_incl_sameset {E F} : forall rel rel2 : relation E F,
	rel2_incl rel rel2 -> rel2_incl_sameset rel rel2.
Proof.
	intros r r2 [fA [fB [HfA [HfB Hr]]]] a b rab.
	specialize (HfA a); specialize (HfB b); specialize (Hr a b rab).
	by exact (proj2 (iff_and (rel_welldef r2 a (fA a) b (fB b) HfA HfB)) Hr).
Qed.
Definition rel2_equiv_sameset {E F} (rel rel2 : relation E F) :=
	let R := rel.(rel_r) in let R' := rel2.(rel_r) in
	forall a b, R a b <-> R' a b.
Lemma rel2_equiv_sameset_is_equiv {E F} : forall rel rel2 : relation E F,
	rel2_equiv_sameset rel rel2 -> rel2_equiv rel rel2.
Proof.
	intros r r2 requivr2; exists (fun a => a), (fun b => b), (fun a => a), (fun b => b);
	  split; split; [| |split|split].
	1,2,3,4: by intros ?; exact (Eeq_refl _).
	by intros a b; exact (requivr2 a b).
	by intros c d; exact (iff_sym (requivr2 c d)).
Qed.
Lemma rel2_equiv_is_equiv_sameset {E F} : forall rel rel2 : relation E F,
	rel2_equiv rel rel2 -> rel2_equiv_sameset rel rel2.
Proof.
	intros r r2 [fA [fB [fC [fD [[HfA HfB] [[HfC HfD] [Hrr2 _]]]]]]] a b.
	by exact (iff_trans (Hrr2 a b)
	  (r2.(rel_welldef) _ _ _ _ (Eeq_sym (HfA _)) (Eeq_sym (HfB _)))).
Qed.
End GeneralRelations.

Section SameEnsRelations.
Context {E : Ensemble}.
Variable rel : rel_same_ens E.
Let A := pi1e E.
Notation "'R'" := rel.(relse_rel).(rel_r).

Definition rel_reflexive := forall a, R a a.
Definition rel_transitive := forall a b c, R a b -> R b c -> R a c.
Definition rel_symmetric := forall a b, R a b -> R b a.
Definition rel_antisymmetric := forall a b, R a b -> R b a -> a = b.

Definition rel_equiv := rel_reflexive /\ rel_transitive /\ rel_symmetric.
End SameEnsRelations.

End Relations.

Section Ensembles.
Section EnsDivision.
Context {E : Ensemble}.
Variable rel : rel_same_ens (E:=E).
Notation "'A'" := (pi1e E).
Notation "'R'" := rel.(relse_rel).(rel_r).
Hypothesis rel_equivalence : rel_equiv rel.

Variable choice : A -> A.
Hypothesis choice_chooses : forall a b, (choice a = choice b) <-> (R a b).

End EnsDivision.
End Ensembles.

Section Functors.
Context {E F G : Ensemble}.
Variable f : Ensemble.
Definition functor_well_defined := f inE (total_application_set E (total_application_set F G)).
End Functors.
Arguments functor_well_defined E F G f : clear implicits.

Section InternalBinaryOperations.
Context {E : Ensemble}.
Let A := pi1e E.
Let fE := pi2e E.
Variable F : Ensemble.
Definition ibo := functor_well_defined E E E F.

Hypothesis ibo_well_defined : ibo.
Definition ibo_fun : Eforall x in E, Eforall y in E, exists z, z inE E.
	intros x xinE y yinE.
	generalize (total_application_image _ ibo_well_defined x xinE).
	generalize (total_application_cons _ ibo_well_defined); intros [g _] gxinEE.
	generalize (total_application_image _ gxinEE y yinE).
	generalize (total_application_cons _ gxinEE); intros [h _] hyinE.
	by exact (ex_intro _ (h y yinE) hyinE).
Defined.
Local Notation "a ain '<*>' b bin" := (ibo_fun a ain b bin) (at level 50, left associativity).
Local Infix "<in>" := (fun x y => ex_intro (fun e => e inE E) x y) (at level 49, no associativity, only parsing).
Local Infix "=2" := (fun l r => let (x, _) := l in let (y, _) := r in x =E y) (at level 48, no associativity, only parsing).
(* Failing here --- *)
Definition ibo_neutral := Eforall e in E as ein, Eforall a in E as ain,
	 ((ibo_fun e ein a ain) =2 (a <in> ain)) /\ ((ibo_fun a ain e ein) =2 a).
Definition ibo_commu := forall a b : { e | e inE E}, (a <*> b) =2 (b <*> a).
Definition ibo_assoc := forall a b c : { e | e inE E}, (a <*> (b <*> c)) =2 ((a <*> b) <*> c).

Definition ibo_distrib_over (f : {e : _ | e inE E} -> {e : _ | e inE E} -> {e : _ | e inE E}) :=
	forall a b c : { e | e inE E},
	 ((a <*> (f b c)) =2 f (a <*> b) (a <*> c)) /\
	 (((f a b) <*> c) =2 f (a <*> c) (b <*> c)).

Definition ibo_inverse (e : { e : _ | e inE E }) (eneut : ibo_neutral e)
 (inv : Ensemble) (inv_well_def : inv inE (total_application_set E E))
 : forall a : { e : _ | e inE E }, Prop.
	intros [a' ain]; pose (a := exist (fun e => e inE E) a' ain).
	generalize (total_application_image inv inv_well_def a' ain).
	generalize (total_application_cons inv inv_well_def); intros [inv' _] invain.
	pose (inva := exist (fun e => e inE E) (inv' a' ain) invain).
	by exact (((inva <*> a) =2 e) /\ ((a <*> inva) =2 e)).
Defined.

Fixpoint ibo_power (e : { e | e inE E}) (a : { e | e inE E}) (n : nat) : { e | e inE E} :=
	match n with O => e | S n' => ibo_fun a (ibo_power e a n') end.
Lemma power_0 e : forall a, ibo_power e a O = e.
Proof. by intros a; unfold ibo_power; exact (eq_refl _). Qed.
Lemma ibo_power_comm (e : { e | e inE E}) (eneut : ibo_neutral e)
 (assoc : ibo_assoc) (a : { e | e inE E}) :
 forall n, (a <*> (ibo_power e a n)) =2 ((ibo_power e a n) <*> a).
Proof.
	intros n; induction n as [|n IHn]; minimize ibo_power.
	by specialize (eneut a) as [l r]; exact (Eeq_trans r (Eeq_sym l)).
	apply Eeq_sym, (Eeq_trans (Eeq_sym (assoc a (ibo_power e a n) a))), Eeq_sym.
	
	unfold sig2ex_l, ibo_fun.
	by rewrite <-(assoc _ _ _ ain (ibo_power_in _ ein _ ain _) ain), IHn; exact (eq_refl _).
Qed.

Definition ibo_symmetrisable_set neut : Ensemble A :=
	(fun a => inE a /\
	          exists b, inE b
	          /\ (f a b = neut) /\ (f b a = neut)).

End InternalBinaryOperations.

Remark ibo_neutral_incl {A} E (E' : Ensemble A) f e ein' :
 forall i : Included _ E' E, (ibo_neutral E f e (i _ ein')) -> (ibo_neutral E' f e ein').
Proof.
	by intros i ibon x xin';
	 specialize (ibon x (i _ xin'));
	 exact ibon.
Qed.
Remark ibo_commu_incl {A} E (E' : Ensemble A) f :
 forall i : Included _ E' E, (ibo_commu E f) -> (ibo_commu E' f).
Proof.
	by intros i ibon x y xin' yin';
	 specialize (ibon x y (i _ xin') (i _ yin'));
	 exact ibon.
Qed.
Remark ibo_assoc_incl {A} E (E' : Ensemble A) f :
 forall i : Included _ E' E, (ibo_assoc E f) -> (ibo_assoc E' f).
Proof.
	by intros i ibon x y z xin' yin' zin';
	 specialize (ibon x y z (i _ xin') (i _ yin') (i _ zin'));
	 exact ibon.
Qed.

End Functions.

Section Groups.
Context {U : Type}.
Record Group : Type := {
	gp_G : Ensemble U
;	gp_dot : U -> U -> U
;	gp_e : U
;	gp_e_in : In _ gp_G gp_e
;	gp_dot_in : ibo gp_G gp_dot
;	gp_dot_neutral : ibo_neutral gp_G gp_dot gp_e gp_e_in
;	gp_dot_assoc : ibo_assoc gp_G gp_dot
;	gp_inv : U -> U
;	gp_inv_in : fun_well_defined gp_G gp_G gp_inv
;	gp_inv_dot : ibo_inverse gp_G gp_dot gp_e gp_e_in gp_dot_neutral gp_inv gp_inv_in
}.
Record CommutativeGroup : Type := {
	cgp_g : Group
;	cgp_dot_commu : ibo_commu cgp_g.(gp_G) cgp_g.(gp_dot)
}.
End Groups.
Arguments Group U : clear implicits.
Arguments CommutativeGroup U : clear implicits.

Section GroupGeneralities.
Context {G : Type}.
Variable Ggp : Group G.
Notation "'eG'" := Ggp.(gp_e).
Notation "'GG'" := Ggp.(gp_G).
Local Infix "<*>" := Ggp.(gp_dot) (at level 50, left associativity).
Notation "'dot'" := Ggp.(gp_dot).
Notation "'inv'" := Ggp.(gp_inv).
Notation "'dotinv'" := Ggp.(gp_inv_dot).
Notation "'ein'" := Ggp.(gp_e_in).
Notation "'welldef'" := Ggp.(gp_dot_in).
Notation "'iwelldef'" := Ggp.(gp_inv_in).
Notation "'eneut'" := Ggp.(gp_dot_neutral).
Notation "'assoc'" := Ggp.(gp_dot_assoc).
Notation "'inG'" := (In _ GG).

Definition group_power a n := ibo_power dot eG a n.
Lemma group_power_in : forall a, inG a -> forall n, inG (group_power a n).
Proof.
	by intros a ain; exact (ibo_power_in _ _ welldef _ ein _ ain).
Qed.
Lemma group_power_0 : forall a, group_power a 0 = eG.
Proof. by cbv delta [group_power]; exact (power_0 _ _). Qed.
Lemma group_power_comm :
 forall a, inG a -> forall n, a <*> (group_power a n) = (group_power a n) <*> a.
Proof. by cbv delta [group_power]; exact (ibo_power_comm _ _ welldef _ ein eneut assoc). Qed.

Lemma group_dot_injective_l : forall a b c, inG a -> inG b -> inG c ->
 a <*> b = a <*> c -> b = c.
Proof.
	intros a b c ain bin cin abeqac.
	apply (f_equal (dot (inv a))) in abeqac.
	rewrite (assoc _ _ _ (iwelldef _ ain) ain bin) in abeqac;
	rewrite (assoc _ _ _ (iwelldef _ ain) ain cin) in abeqac.
	rewrite (and_l (dotinv _ ain)) in abeqac.
	rewrite (and_l (eneut _ bin)) in abeqac;
	rewrite (and_l (eneut _ cin)) in abeqac.
	by exact abeqac.
Qed.
Lemma group_dot_injective_r : forall a b c, inG a -> inG b -> inG c ->
 a <*> c = b <*> c -> a = b.
Proof.
	intros a b c ain bin cin aceqbc.
	apply (f_equal (fun x => dot x (inv c))) in aceqbc.
	rewrite <-(assoc _ _ _ ain cin (iwelldef _ cin)) in aceqbc;
	rewrite <-(assoc _ _ _ bin cin (iwelldef _ cin)) in aceqbc.
	rewrite (and_r (dotinv _ cin)) in aceqbc.
	rewrite (and_r (eneut _ ain)) in aceqbc;
	rewrite (and_r (eneut _ bin)) in aceqbc.
	by exact aceqbc.
Qed.

Lemma group_neutral_unique : forall e, inG e ->
 (forall a, inG a -> (a <*> e = a) /\ (e <*> a = a)) -> e = eG.
Proof.
	intros e' e'in He.
	specialize (He e' e'in) as [He _].
	apply (group_dot_injective_l _ _ _ e'in e'in ein).
	rewrite (and_r (eneut _ e'in)).
	by exact He.
Qed.

Lemma group_inv_inv : forall a, inG a -> inv (inv a) = a.
Proof.
	intros a ain.
	apply (group_dot_injective_l _ _ _ (iwelldef _ ain) (iwelldef _ (iwelldef _ ain)) ain).
	rewrite (and_r (dotinv _ (iwelldef _ ain)));
	rewrite (and_l (dotinv _ ain)).
	by exact (eq_refl _).
Qed.

Lemma group_inv_neut : inv Ggp.(gp_e) = Ggp.(gp_e).
Proof.
	apply (group_dot_injective_l _ _ _ ein (iwelldef _ ein) ein).
	by rewrite (and_r (dotinv _ ein)),
	 (and_l (eneut _ ein));
	 exact (eq_refl _).
Qed.
Lemma group_inverse_dot :
 forall a b, In _ GG a -> In _ GG b -> inv (a <*> b) = (inv b) <*> (inv a).
Proof.
	intros a b ain bin.
	apply (group_dot_injective_l _ _ _
		(welldef _ _ ain bin)
		(iwelldef _ (welldef _ _ ain bin))
		(welldef _ _ (iwelldef _ bin) (iwelldef _ ain))).
	by rewrite
	 (and_r (dotinv _ (welldef _ _ ain bin))),
	 (assoc _ _ _ (welldef _ _ ain bin) (iwelldef _ bin) (iwelldef _ ain)),
	 <-(assoc _ _ _ ain bin (iwelldef _ bin)),
	 (and_r (dotinv _ bin)),
	 (and_r (eneut _ ain)),
	 (and_r (dotinv _ ain));
	exact (eq_refl _).
Qed.
Lemma group_inverse_power :
 forall a, In _ GG a -> forall n : nat, inv (group_power a n) = group_power (inv a) n.
Proof.
	intros a ain n; induction n as [|n].
	by unfold group_power, ibo_power;
	 exact group_inv_neut.
	unfold group_power in IHn;
	 unfold group_power, ibo_power; fold (ibo_power dot eG).
	rewrite <-IHn, (group_power_comm _ ain _),
	        (group_inverse_dot _ _ (group_power_in _ ain _) ain).
	by exact (eq_refl _).
Qed.

Lemma group_invl_to_posr_l : forall a b, In _ GG a -> In _ GG b ->
 (inv a <*> b = Ggp.(gp_e)) -> (a = b).
Proof.
	intros a b ain bin iabeqe.
	apply (group_dot_injective_l _ _ _ (iwelldef _ ain) ain bin).
	rewrite (and_l (dotinv _ ain)).
	by symmetry; exact iabeqe.
Qed.
Lemma group_invl_to_posr_r : forall a b, In _ GG a -> In _ GG b ->
 (a <*> inv b = Ggp.(gp_e)) -> (a = b).
Proof.
	intros a b ain bin aibeqe.
	apply (group_dot_injective_r _ _ _ ain bin (iwelldef _ bin)).
	rewrite (and_r (dotinv _ bin)).
	by exact aibeqe.
Qed.

End GroupGeneralities.
Arguments group_power_in {G Ggp} [a] ain n.
Arguments group_power_0 {G Ggp} a.

Section ProductGroup.
Context {G : Type}.
Variable Ggp : Group G.
Notation "'eG'" := Ggp.(gp_e).
Local Infix "<*>" := Ggp.(gp_dot) (at level 50, left associativity).
Notation "'invG'" := Ggp.(gp_inv).

Context {H : Type}.
Variable Hgp : Group H.
Notation "'eH'" := Hgp.(gp_e).
Local Infix "<.>" := Hgp.(gp_dot) (at level 50, left associativity).
Notation "'invH'" := Hgp.(gp_inv).

Notation "'proddot'" := (fun (x y : G * H) =>
 let (a, a') := x in let (b, b') := y in ((a <*> b), (a' <.> b'))).
Local Infix "<*.>" := proddot (at level 50, left associativity).
Notation "'prodneut'" := (eG, eH).
Notation "'prodens'" := (fun (x : G*H) => let (a, a') := x in (In _ Ggp.(gp_G) a) /\ (In _ Hgp.(gp_G) a')).
Local Lemma product_neut_in : In _ prodens prodneut.
Proof.
	split.
	by exact (Ggp.(gp_e_in)).
	by exact (Hgp.(gp_e_in)).
Qed.
Local Lemma product_dot_in : ibo prodens proddot.
Proof.
	intros [a a'] [b b'] [ain a'in] [bin b'in].
	split.
	by exact (Ggp.(gp_dot_in) _ _ ain bin).
	by exact (Hgp.(gp_dot_in) _ _ a'in b'in).
Qed.
Local Lemma product_dot_neutral : ibo_neutral prodens proddot prodneut product_neut_in.
Proof.
	intros [a a'] [ain a'in]; split; apply f_equal2.
	by exact (and_l (Ggp.(gp_dot_neutral) _ ain)).
	by exact (and_l (Hgp.(gp_dot_neutral) _ a'in)).
	by exact (and_r (Ggp.(gp_dot_neutral) _ ain)).
	by exact (and_r (Hgp.(gp_dot_neutral) _ a'in)).
Qed.
Local Lemma product_dot_assoc : ibo_assoc prodens proddot.
Proof.
	intros [a a'] [b b'] [c c'] [ain a'in] [bin b'in] [cin c'in]; apply f_equal2.
	by exact (Ggp.(gp_dot_assoc) _ _ _ ain bin cin).
	by exact (Hgp.(gp_dot_assoc) _ _ _ a'in b'in c'in).
Qed.
Notation "'prodinv'" := (fun (a : G*H) => let (a, a') := a in (invG a, invH a')).
Local Lemma product_inv_in : fun_well_defined prodens prodens prodinv.
Proof.
	intros [a a'] [ain a'in]; split.
	by exact (Ggp.(gp_inv_in) _ ain).
	by exact (Hgp.(gp_inv_in) _ a'in).
Qed.
Local Lemma product_inv_dot :
 ibo_inverse prodens proddot prodneut product_neut_in product_dot_neutral prodinv product_inv_in.
Proof.
	intros [a a'] [ain a'in]; split; apply f_equal2.
	by exact (and_l (Ggp.(gp_inv_dot) _ ain)).
	by exact (and_l (Hgp.(gp_inv_dot) _ a'in)).
	by exact (and_r (Ggp.(gp_inv_dot) _ ain)).
	by exact (and_r (Hgp.(gp_inv_dot) _ a'in)).
Qed.

Definition ProductGroup := {|
	gp_e_in        := product_neut_in
;	gp_dot_in      := product_dot_in
;	gp_dot_neutral := product_dot_neutral
;	gp_dot_assoc   := product_dot_assoc
;	gp_inv_in      := product_inv_in
;	gp_inv_dot     := product_inv_dot
|}.

End ProductGroup.

Section ProductCommGroup.
Context {G : Type}.
Variable Gcgp : CommutativeGroup G.
Notation "'Ggp'" := Gcgp.(cgp_g).
Notation "'eG'" := Ggp.(gp_e).
Local Infix "<*>" := Ggp.(gp_dot) (at level 50, left associativity).
Notation "'invG'" := Ggp.(gp_inv).

Context {H : Type}.
Variable Hcgp : CommutativeGroup H.
Notation "'Hgp'" := Hcgp.(cgp_g).
Notation "'eH'" := Hgp.(gp_e).
Local Infix "<.>" := Hgp.(gp_dot) (at level 50, left associativity).
Notation "'invH'" := Hgp.(gp_inv).

Notation "'GHgp'" := (ProductGroup Ggp Hgp).
Notation "'eP'" := GHgp.(gp_e).
Local Infix "<*.>" := GHgp.(gp_dot) (at level 50, left associativity).
Notation "'invP'" := GHgp.(gp_inv).

Local Lemma product_dot_commu : ibo_commu GHgp.(gp_G) GHgp.(gp_dot).
Proof.
	intros [a a'] [b b'] [ain a'in] [bin b'in]; simpl; apply f_equal2.
	by exact (Gcgp.(cgp_dot_commu) _ _ ain bin).
	by exact (Hcgp.(cgp_dot_commu) _ _ a'in b'in).
Qed.

Definition ProductCommGroup := {| cgp_g := GHgp; cgp_dot_commu := product_dot_commu |}.

End ProductCommGroup.

Section SubGroup.
Context {G : Type}.
Variable Ggp : Group G.
Notation "'eG'" := Ggp.(gp_e).
Local Infix "<*>" := Ggp.(gp_dot) (at level 50, left associativity).
Notation "'inv'" := Ggp.(gp_inv).

Variable H : Ensemble G.
Hypothesis H_incl : Included _ H Ggp.(gp_G).
Hypothesis H_neut_in' : exists a, In _ H a.
Hypothesis H_subgroup : forall a b, In _ H a -> In _ H b -> In _ H (a <*> inv b).

Local Lemma H_neut_in : In _ H eG.
Proof.
	destruct H_neut_in' as [a ain].
	specialize (H_subgroup _ _ ain ain) as ein.
	rewrite (and_r (Ggp.(gp_inv_dot) _ (H_incl _ ain))) in ein.
	by exact ein. 
Qed.
Local Lemma subgroup_inv_in : fun_well_defined H H inv.
Proof.
	intros a ain.
	rewrite <-(and_l (Ggp.(gp_dot_neutral) _ (Ggp.(gp_inv_in) _ (H_incl _ ain)))).
	by exact (H_subgroup _ _ H_neut_in ain).
Qed.

Local Lemma subgroup_dot_in : ibo H Ggp.(gp_dot).
Proof.
	intros a b ain bin.
	rewrite <-(group_inv_inv _ _ (H_incl _ bin)).
	specialize (subgroup_inv_in _ bin) as binvin.
	by exact (H_subgroup _ _ ain binvin).
Qed.

Local Lemma subgroup_dot_neutral : ibo_neutral H Ggp.(gp_dot) eG H_neut_in.
Proof.
	by intros a ainH; specialize (H_incl _ ainH) as ainG;
	 exact (Ggp.(gp_dot_neutral) _ ainG).
Qed.

Local Lemma subgroup_dot_assoc : ibo_assoc H Ggp.(gp_dot).
Proof.
	by intros a b c ainH binH cinH; specialize (H_incl _ ainH) as ainG;
	 specialize (H_incl _ binH) as binG; specialize (H_incl _ cinH) as cinG;
	 exact (Ggp.(gp_dot_assoc) _ _ _ ainG binG cinG).
Qed.
Local Lemma subgroup_inv_dot :
 ibo_inverse H Ggp.(gp_dot) eG H_neut_in subgroup_dot_neutral inv subgroup_inv_in.
Proof.
	by intros a ainH; specialize (H_incl _ ainH) as ainG;
	 exact (Ggp.(gp_inv_dot) _ ainG).
Qed.

Definition Subgroup := {|
	gp_e_in        := H_neut_in
;	gp_dot_in      := subgroup_dot_in
;	gp_dot_neutral := subgroup_dot_neutral
;	gp_dot_assoc   := subgroup_dot_assoc
;	gp_inv_in      := subgroup_inv_in
;	gp_inv_dot     := subgroup_inv_dot
|}.

End SubGroup.
Definition SubgroupHyp {G} (Ggp : Group G) H :=
	(Included _ H Ggp.(gp_G)) /\ (exists a, In _ H a) /\
	(forall a b, In _ H a -> In _ H b -> In _ H (Ggp.(gp_dot) a (Ggp.(gp_inv) b))).
Definition SubgroupFromHyp {G} Gcgp H (hs : SubgroupHyp (G:=G) Gcgp H)
	:= Subgroup _ _ (and_l hs) (and_l (and_r hs)) (and_r (and_r hs)).

Section CommSubGroup.
Context {G : Type}.
Variable Gcgp : CommutativeGroup G.
Notation "'Ggp'" := Gcgp.(cgp_g).
Notation "'eG'" := Ggp.(gp_e).
Local Infix "<*>" := Ggp.(gp_dot) (at level 50, left associativity).
Notation "'inv'" := Ggp.(gp_inv).

Variable H : Ensemble G.
Hypothesis H_incl : Included _ H Ggp.(gp_G).
Hypothesis H_neut_in' : exists a, In _ H a.
Hypothesis H_subgroup : forall a b, In _ H a -> In _ H b -> In _ H (a <*> inv b).

Local Lemma subgroup_dot_commu : ibo_commu H Ggp.(gp_dot).
Proof.
	by intros a b ainH binH; specialize (H_incl _ ainH) as ainG;
	 specialize (H_incl _ binH) as binG;
	 exact (Gcgp.(cgp_dot_commu) _ _ ainG binG).
Qed.

Definition CommSubgroup := {| cgp_g := Subgroup _ _ H_incl H_neut_in' H_subgroup; cgp_dot_commu := subgroup_dot_commu |}.

End CommSubGroup.
Definition CommSubgroupHyp {G} (Gcgp : CommutativeGroup G) H :=
	(Included _ H Gcgp.(cgp_g).(gp_G)) /\ (exists a, In _ H a) /\
	(forall a b, In _ H a -> In _ H b -> In _ H (Gcgp.(cgp_g).(gp_dot) a (Gcgp.(cgp_g).(gp_inv) b))).
Definition CommSubgroupFromHyp {G} Gcgp H (hs : CommSubgroupHyp (G:=G) Gcgp H)
	:= CommSubgroup _ _ (and_l hs) (and_l (and_r hs)) (and_r (and_r hs)).

Section InterGroup.
Context {G : Type}.
Variable Ggp : Group G.
Notation "'eG'" := Ggp.(gp_e).
Local Infix "<*>" := Ggp.(gp_dot) (at level 50, left associativity).
Notation "'dot'" := Ggp.(gp_dot).
Notation "'inv'" := Ggp.(gp_inv).
Notation "'dotinv'" := Ggp.(gp_inv_dot).
Notation "'ein'" := Ggp.(gp_e_in).
Notation "'welldef'" := Ggp.(gp_dot_in).
Notation "'iwelldef'" := Ggp.(gp_inv_in).
Notation "'eneut'" := Ggp.(gp_dot_neutral).
Notation "'assoc'" := Ggp.(gp_dot_assoc).
Notation "'inG'" := (In _ Ggp.(gp_G)).

Variable H : Ensemble G.
Hypothesis H_incl : Included _ H Ggp.(gp_G).
Hypothesis H_neut_in' : exists a, In _ H a.
Hypothesis H_subgroup : forall a b, In _ H a -> In _ H b -> In _ H (a <*> inv b).
Notation "'Hgp'" := (Subgroup Ggp H H_incl H_neut_in' H_subgroup).

Variable K : Ensemble G.
Hypothesis K_incl : Included _ K Ggp.(gp_G).
Hypothesis K_neut_in' : exists a, In _ K a.
Hypothesis K_subgroup : forall a b, In _ K a -> In _ K b -> In _ K (a <*> inv b).
Notation "'Kgp'" := (Subgroup Ggp K K_incl K_neut_in' K_subgroup).

Notation "'interens'" := (intersection H K).
Local Lemma inter_included_H : Included _ interens H.
Proof.
	intros ? ainI.
	by exact (and_l ainI).
Qed.
Local Lemma inter_included_K : Included _ interens K.
Proof.
	intros ? ainI.
	by exact (and_r ainI).
Qed.
Local Lemma inter_neut_in : In _ interens eG.
Proof.
	split.
	by exact (Hgp.(gp_e_in)).
	by exact (Kgp.(gp_e_in)).
Qed.
Local Lemma inter_dot_in : ibo interens dot.
Proof.
	intros a b ain bin.
	split.
	by exact (Hgp.(gp_dot_in) _ _ (inter_included_H _ ain) (inter_included_H _ bin)).
	by exact (Kgp.(gp_dot_in) _ _ (inter_included_K _ ain) (inter_included_K _ bin)).
Qed.
Local Lemma inter_dot_neutral : ibo_neutral interens dot eG inter_neut_in.
Proof.
	intros a ain.
	apply inter_included_H, H_incl in ain.
	by exact (Ggp.(gp_dot_neutral) _ ain).
Qed.
Local Lemma inter_dot_assoc : ibo_assoc interens dot.
Proof.
	intros a b c ain bin cin.
	apply inter_included_H, H_incl in ain;
	apply inter_included_H, H_incl in bin;
	apply inter_included_H, H_incl in cin.
	by exact (Ggp.(gp_dot_assoc) _ _ _ ain bin cin).
Qed.
Local Lemma inter_inv_in : fun_well_defined interens interens inv.
Proof.
	intros a ain; split.
	by apply inter_included_H in ain;
	 exact (Hgp.(gp_inv_in) _ ain).
	by apply inter_included_K in ain;
	 exact (Kgp.(gp_inv_in) _ ain).
Qed.
Local Lemma inter_inv_dot :
 ibo_inverse interens dot eG inter_neut_in inter_dot_neutral inv inter_inv_in.
Proof.
	intros a ain.
	apply inter_included_H, H_incl in ain.
	by exact (Ggp.(gp_inv_dot) _ ain).
Qed.

Definition InterGroup := {|
	gp_e_in        := inter_neut_in
;	gp_dot_in      := inter_dot_in
;	gp_dot_neutral := inter_dot_neutral
;	gp_dot_assoc   := inter_dot_assoc
;	gp_inv_in      := inter_inv_in
;	gp_inv_dot     := inter_inv_dot
|}.

End InterGroup.

Section InterCommGroup.
Context {G : Type}.
Variable Gcgp : CommutativeGroup G.
Notation "'Ggp'" := Gcgp.(cgp_g).
Notation "'eG'" := Ggp.(gp_e).
Local Infix "<*>" := Ggp.(gp_dot) (at level 50, left associativity).
Notation "'inv'" := Ggp.(gp_inv).

Variable H : Ensemble G.
Hypothesis H_incl : Included _ H Ggp.(gp_G).
Hypothesis H_neut_in' : exists a, In _ H a.
Hypothesis H_subgroup : forall a b, In _ H a -> In _ H b -> In _ H (a <*> inv b).
Notation "'Hgp'" := (Subgroup Ggp H H_incl H_neut_in' H_subgroup).

Variable K : Ensemble G.
Hypothesis K_incl : Included _ K Ggp.(gp_G).
Hypothesis K_neut_in' : exists a, In _ K a.
Hypothesis K_subgroup : forall a b, In _ K a -> In _ K b -> In _ K (a <*> inv b).
Notation "'Kgp'" := (Subgroup Ggp K K_incl K_neut_in' K_subgroup).

Notation "'Igp'" := (InterGroup Ggp H H_incl H_neut_in' H_subgroup K K_incl K_neut_in' K_subgroup).

Local Lemma inter_dot_commu : ibo_commu Igp.(gp_G) Igp.(gp_dot).
Proof.
	intros a b ain bin.
	apply inter_included_H, H_incl in ain;
	apply inter_included_H, H_incl in bin.
	by exact (Gcgp.(cgp_dot_commu) _ _ ain bin).
Qed.

Definition InterCommGroup := {| cgp_g := Igp; cgp_dot_commu := inter_dot_commu |}.

End InterCommGroup.

Section CommPlusGroup.
Context {G : Type}.
Variable Gcgp : CommutativeGroup G.
Notation "'comm'" := Gcgp.(cgp_dot_commu).
Notation "'Ggp'" := Gcgp.(cgp_g).
Notation "'eG'" := Ggp.(gp_e).
Local Infix "<*>" := Ggp.(gp_dot) (at level 50, left associativity).
Notation "'dot'" := Ggp.(gp_dot).
Notation "'inv'" := Ggp.(gp_inv).
Notation "'dotinv'" := Ggp.(gp_inv_dot).
Notation "'ein'" := Ggp.(gp_e_in).
Notation "'welldef'" := Ggp.(gp_dot_in).
Notation "'iwelldef'" := Ggp.(gp_inv_in).
Notation "'eneut'" := Ggp.(gp_dot_neutral).
Notation "'assoc'" := Ggp.(gp_dot_assoc).
Notation "'inG'" := (In _ Ggp.(gp_G)).

Variable H : Ensemble G.
Hypothesis H_incl : Included _ H Ggp.(gp_G).
Hypothesis H_neut_in' : exists a, In _ H a.
Hypothesis H_subgroup : forall a b, In _ H a -> In _ H b -> In _ H (a <*> inv b).
Notation "'Hgp'" := (Subgroup Ggp H H_incl H_neut_in' H_subgroup).
Notation "'inH'" := (In _ H).

Variable K : Ensemble G.
Hypothesis K_incl : Included _ K Ggp.(gp_G).
Hypothesis K_neut_in' : exists a, In _ K a.
Hypothesis K_subgroup : forall a b, In _ K a -> In _ K b -> In _ K (a <*> inv b).
Notation "'Kgp'" := (Subgroup Ggp K K_incl K_neut_in' K_subgroup).
Notation "'inK'" := (In _ K).

Notation "'plusgpens'" := (fun x => exists a b, (inH a /\ inK b) /\ x = a <*> b).
Local Lemma plusgp_incl : Included _ plusgpens Ggp.(gp_G).
Proof.
	intros a [aH [aK [[aHin aKin] aeq]]].
	by rewrite aeq; apply (welldef _ _ (H_incl _ aHin) (K_incl _ aKin)).
Qed.
Local Lemma plusgp_neut_in : In _ plusgpens eG.
Proof.
	exists eG, eG.
	by split; [split; [
		exact Hgp.(gp_e_in) |
		exact Kgp.(gp_e_in) ] |
		symmetry; exact (and_l (eneut _ ein))].
Qed.
Local Lemma plusgp_subgroup : forall a b, In _ plusgpens a -> In _ plusgpens b -> In _ plusgpens (a <*> inv b).
Proof.
	intros a b [aH [aK [[aHin aKin] aeq]]] [bH [bK [[bHin bKin] beq]]].
	rewrite aeq, beq.
	rewrite (group_inverse_dot _ _ _ (H_incl _ bHin) (K_incl _ bKin)).
	exists (aH <*> inv bH), (aK <*> inv bK).
	split; [split |].
	by exact (Hgp.(gp_dot_in) _ _ aHin (Hgp.(gp_inv_in) _ bHin)).
	by exact (Kgp.(gp_dot_in) _ _ aKin (Kgp.(gp_inv_in) _ bKin)).
	pose (aHin' := H_incl _ aHin).
	pose (aKin' := K_incl _ aKin).
	pose (biHin' := iwelldef _ (H_incl _ bHin)).
	pose (biKin' := iwelldef _ (K_incl _ bKin)).
	rewrite (assoc _ _ _ (welldef _ _ aHin' biHin') aKin' biKin'),
	      <-(assoc _ _ _ aHin' biHin' aKin').
	rewrite (comm _ _ biHin' aKin').
	rewrite (assoc _ _ _ aHin' aKin' biHin'),
	      <-(assoc _ _ _ (welldef _ _ aHin' aKin') biHin' biKin').
	by rewrite (comm _ _ biHin' biKin'); exact (eq_refl _).
Qed.
Definition PlusGroup := Subgroup _ _ plusgp_incl (ex_intro _ _ plusgp_neut_in) plusgp_subgroup.

End CommPlusGroup.
Definition PlusGroupFromHyp {G} Gcgp H (hs : CommSubgroupHyp (G:=G) Gcgp H) K (ks : CommSubgroupHyp (G:=G) Gcgp K)
	:= PlusGroup Gcgp H (and_l hs) (and_l (and_r hs)) (and_r (and_r hs))
	                  K (and_l ks) (and_l (and_r ks)) (and_r (and_r ks)).

Section Morphism.
Context {U V : Type} [G : Group U] [H : Group V].
Local Infix "<*>" := G.(gp_dot) (at level 50, left associativity).
Local Infix "<.>" := H.(gp_dot) (at level 50, left associativity).
Notation "'inG'" := (In _ G.(gp_G)).
Notation "'inH'" := (In _ H.(gp_G)).
Notation "'invG'" := G.(gp_inv).
Notation "'invH'" := H.(gp_inv).

Section MorphismGeneralities.
Variable f : U -> V.
Definition mor_well_defined := fun_well_defined G.(gp_G) H.(gp_G) f.
Definition mor :=
	forall a b, inG a -> inG b -> f (a <*> b) = (f a) <.> (f b).
End MorphismGeneralities.
Record Morphism := {
	mor_f : U -> V
;	mor_correct : mor_well_defined mor_f
;	mor_morph : mor mor_f
}.

Section MorphismGeneralities.
Variable m : Morphism.
Notation "'f'" := m.(mor_f).
Notation "'correct'" := m.(mor_correct).
Notation "'morph'" := m.(mor_morph).

Lemma morphism_power_power :
 forall a, inG a -> forall n, f (group_power G a n) = group_power H (f a) n.
Proof.
	intros a ain n; induction n as [|n IHn].
	unfold group_power, ibo_power.
	specialize (f_equal f (and_l (G.(gp_dot_neutral) _ G.(gp_e_in)))) as P.
	rewrite (morph _ _ G.(gp_e_in) G.(gp_e_in)) in P.
	rewrite <-(and_r (H.(gp_dot_neutral) _ (correct _ G.(gp_e_in)))) in P at 3.
	by exact (group_dot_injective_l _ _ _ _ (correct _ G.(gp_e_in)) (correct _ G.(gp_e_in)) H.(gp_e_in) P).
	unfold group_power, ibo_power;
	 fold (ibo_power G.(gp_dot));
	 fold (ibo_power H.(gp_dot)).
	specialize (morph _ _ ain (group_power_in ain n)) as tmp; unfold group_power in tmp;
	rewrite tmp; clear tmp.
	by unfold group_power in IHn; rewrite <-IHn; exact (eq_refl _).
Qed.
Lemma morphism_inv_inv : forall a, inG a -> f (invG a) = invH (f a).
Proof.
	intros a ain.
	specialize (morphism_power_power _ ain 0) as P; unfold group_power, ibo_power in P.
	rewrite <-(and_r (G.(gp_inv_dot) _ ain)) in P.
	rewrite (morph _ _ ain (G.(gp_inv_in) _ ain)) in P.
	apply (f_equal (H.(gp_dot) (invH (f a)))) in P.
	rewrite (H.(gp_dot_assoc) _ _ _
	 (H.(gp_inv_in) _ (correct _ ain)) (correct _ ain) (correct _ (G.(gp_inv_in) _ ain)))
	 in P.
	rewrite (and_l (H.(gp_inv_dot) _ (correct _ ain))) in P.
	rewrite (and_l (H.(gp_dot_neutral) _ (correct _ (G.(gp_inv_in) _ ain)))) in P;
	rewrite (and_r (H.(gp_dot_neutral) _ (H.(gp_inv_in) _ (correct _ ain)))) in P.
	by exact P.
Qed.
Corollary morphism_neut : f (G.(gp_e)) = H.(gp_e).
Proof.
	specialize (morphism_power_power _ G.(gp_e_in) 0) as P.
	unfold group_power, ibo_power in P.
	exact P.
Qed.

Definition Im_mor_e := fun y => exists x : U, (inG x) /\ ((f x) = y).
Definition Ker_mor_e := fun x => (inG x) /\ (f x) = H.(gp_e).

Local Lemma Im_mor_incl : Included _ Im_mor_e H.(gp_G).
Proof.
	intros b [a [ain [=<-]]].
	by exact (correct _ ain).
Qed.
Local Lemma Im_mor_neut_in : In _ Im_mor_e H.(gp_e).
Proof.
	exists G.(gp_e); split.
	by exact G.(gp_e_in).
	specialize (and_l (G.(gp_dot_neutral) _ G.(gp_e_in))) as P.
	apply (f_equal f) in P.
	rewrite (morph _ _ G.(gp_e_in) G.(gp_e_in)) in P.
	rewrite <-(and_r (H.(gp_dot_neutral) _ (correct _ G.(gp_e_in)))) in P at 3.
	by exact (group_dot_injective_l _ _ _ _ (correct _ G.(gp_e_in)) (correct _ G.(gp_e_in)) H.(gp_e_in) P).
Qed.
Local Lemma Im_mor_subgroup : forall a b, In _ Im_mor_e a -> In _ Im_mor_e b -> In _ Im_mor_e (a <.> invH b).
Proof.
	intros c d [a [ain Ha]] [b [bin Hb]].
	exists (a <*> invG b); split.
	by exact (G.(gp_dot_in) _ _ ain (G.(gp_inv_in) _ bin)).
	rewrite (morph _ _ ain (G.(gp_inv_in) _ bin)).
	rewrite (morphism_inv_inv _ bin).
	by exact (f_equal2 _ Ha (f_equal _ Hb)).
Qed.
Definition Im_mor := Subgroup H Im_mor_e Im_mor_incl (ex_intro _ _ Im_mor_neut_in) Im_mor_subgroup.

Local Lemma Ker_mor_incl : Included _ Ker_mor_e G.(gp_G).
Proof.
	intros a [ain _].
	by exact ain.
Qed.
Local Lemma Ker_mor_neut_in : In _ Ker_mor_e G.(gp_e).
Proof.
	split.
	by exact G.(gp_e_in).
	by exact morphism_neut.
Qed.
Local Lemma Ker_mor_subgroup : forall a b, In _ Ker_mor_e a -> In _ Ker_mor_e b -> In _ Ker_mor_e (a <*> invG b).
Proof.
	intros a b [ain Ha] [bin Hb]; split.
	by exact (G.(gp_dot_in) _ _ ain (G.(gp_inv_in) _ bin)).
	rewrite (morph _ _ ain (G.(gp_inv_in) _ bin)).
	rewrite Ha, (and_l (H.(gp_dot_neutral) _ (correct _ (G.(gp_inv_in) _ bin)))).
	rewrite (morphism_inv_inv _ bin), Hb.
	by rewrite (group_inv_neut H); exact (eq_refl _).
Qed.
Definition Ker_mor := Subgroup G Ker_mor_e Ker_mor_incl (ex_intro _ _ Ker_mor_neut_in) Ker_mor_subgroup.

Remark morphism_injection_if_ker : Ker_mor_e = (fun x => x = G.(gp_e)) -> injective G.(gp_G) H.(gp_G) f.
Proof.
	intros iH x y xin yin fxeqfy.
	apply (f_equal (H.(gp_dot) (invH (f y)))) in fxeqfy.
	rewrite (and_l (H.(gp_inv_dot) _ (correct _ yin))) in fxeqfy.
	rewrite <-(morphism_inv_inv _ yin) in fxeqfy.
	rewrite <-(morph _ _ (G.(gp_inv_in) _ yin) xin) in fxeqfy.
	assert (xyinvinKer : In _ Ker_mor_e (invG y <*> x)).
	 by split; [exact (G.(gp_dot_in) _ _ (G.(gp_inv_in) _ yin) xin) | exact fxeqfy].
	rewrite iH in xyinvinKer; unfold In in xyinvinKer.
	apply (group_invl_to_posr_l _ _ _ yin xin) in xyinvinKer.
	by symmetry; exact xyinvinKer.
Qed.
Remark morphism_ker_if_injection : injective G.(gp_G) H.(gp_G) f -> Ker_mor_e = (fun x => x = G.(gp_e)).
Proof.
	intros injf; apply Extensionality_Ensembles; split.
	intros x xinKer.
	pose (fxeqfe := let (_, tmp) := xinKer in tmp).
	rewrite <-morphism_neut in fxeqfe.
	by exact (injf _ _ (Ker_mor_incl _ xinKer) G.(gp_e_in) fxeqfe).
	intros x xinG; split.
	by rewrite xinG; exact G.(gp_e_in).
	by rewrite <-morphism_neut; exact (f_equal f xinG).
Qed.

Remark morphism_surjection_if_im : Im_mor_e = H.(gp_G) -> surjective G.(gp_G) H.(gp_G) f.
Proof.
	intros iH y yin.
	by rewrite <-iH in yin; exact yin.
Qed.
Remark morphism_im_if_surjection : surjective G.(gp_G) H.(gp_G) f -> Im_mor_e = H.(gp_G).
Proof.
	intros surj.
	apply Extensionality_Ensembles.
	split.
	by intros x xin; exact (Im_mor_incl _ xin).
	by exact surj.
Qed.

End MorphismGeneralities.

End Morphism.

Section Rings.
Context {U : Type}.
Notation "G .( 'tmp_G' )" := G.(cgp_g).(gp_G) (at level 0).
Let tmp_inv_set d (u : U) G := (ibo_symmetrisable_set G.(tmp_G) d u).
Let tmp_unit_in_inv_set G dot (unit : U) (unit_in : In _ G unit)
 (dot_unit : ibo_neutral G dot unit unit_in)
 : In _ (ibo_symmetrisable_set G dot unit) unit :=
	(conj unit_in (ex_intro _ unit (conj unit_in (dot_unit unit unit_in)))).
Record UnitaryRing : Type := {
	rng_gp : CommutativeGroup U
;	rng_dot : U -> U -> U
;	rng_dot_in : ibo rng_gp.(tmp_G) rng_dot
;	rng_dot_assoc : ibo_assoc rng_gp.(tmp_G) rng_dot
;	rng_unit : U
;	rng_unit_in : In _ rng_gp.(tmp_G) rng_unit
;	rng_dot_unit : ibo_neutral rng_gp.(tmp_G) rng_dot rng_unit rng_unit_in
;	rng_dot_distrib : ibo_distrib_over rng_gp.(tmp_G) rng_dot rng_gp.(cgp_g).(gp_dot)
;	rng_zero_ne_one : rng_gp.(cgp_g).(gp_e) <> rng_unit
;	rng_inv : U -> U
;	rng_inv_in : fun_well_defined rng_gp.(tmp_inv_set rng_dot rng_unit) rng_gp.(tmp_inv_set rng_dot rng_unit) rng_inv
;	rng_inv_dot :
	 ibo_inverse
	  rng_gp.(tmp_inv_set rng_dot rng_unit)
	  rng_dot
	  rng_unit
	  (tmp_unit_in_inv_set _ _ _ rng_unit_in rng_dot_unit)
	  (ibo_neutral_incl
	    rng_gp.(tmp_G)
		rng_gp.(tmp_inv_set rng_dot rng_unit)
		_ _
		(tmp_unit_in_inv_set _ _ _ rng_unit_in rng_dot_unit)
		(fun x xinS => let (xin, _) := xinS in xin)
		rng_dot_unit)
	  rng_inv
	  rng_inv_in
}.
Definition rng_inv_set R := Eval cbv beta delta [tmp_inv_set] in R.(rng_gp).(tmp_inv_set R.(rng_dot) R.(rng_unit)).
Definition rng_inv_set_incl R
 : Included _ (rng_inv_set R) R.(rng_gp).(cgp_g).(gp_G)
 := (fun x xin => let (xinS, _) := xin in xinS).

Record CommUnitaryRing := {
	crg_r : UnitaryRing
;	crg_commu : ibo_commu crg_r.(rng_gp).(cgp_g).(gp_G) crg_r.(rng_dot)
}.
End Rings.
Arguments UnitaryRing U : clear implicits.
Arguments CommUnitaryRing U : clear implicits.

Section Rings.
Context {G : Type}.
Variable Grg : UnitaryRing G.
Notation "'Ggp'" := Grg.(rng_gp).(cgp_g).
Notation "'G0'" := Ggp.(gp_e).
Notation "'G1'" := Grg.(rng_unit).
Notation "'GG'" := Ggp.(gp_G).
Notation "'plus'" := Ggp.(gp_dot).
Notation "'minus'" := Ggp.(gp_inv).
Notation "'dot'" := Grg.(rng_dot).
Notation "'inv'" := Grg.(rng_inv).
Local Infix "<+>" := plus (at level 50, left associativity).
Local Infix "<*>" := dot  (at level 49, left associativity).
Notation "'plusminus'" := Ggp.(gp_inv_dot).
Notation "'dotinv'" := Grg.(rng_inv_dot).
Notation "'in0'" := Ggp.(gp_e_in).
Notation "'in1'" := Grg.(rng_unit_in).
Notation "'pwelldef'" := Ggp.(gp_dot_in).
Notation "'mwelldef'" := Ggp.(gp_inv_in).
Notation "'twelldef'" := Grg.(rng_dot_in).
Notation "'iwelldef'" := Grg.(rng_inv_in).
Notation "'zero_neut'" := Ggp.(gp_dot_neutral).
Notation "'unit_neut'" := Grg.(rng_dot_unit).
Notation "'passoc'" := Ggp.(gp_dot_assoc).
Notation "'tassoc'" := Grg.(rng_dot_assoc).
Notation "'distrib'" := Grg.(rng_dot_distrib).
Notation "'inG'" := (In _ GG).
Notation "'inv_set'" := (rng_inv_set Grg).
Notation "'inS'" := (In _ inv_set).

Definition ring_times a n := ibo_power plus G0 a n.
Lemma ring_times_in : forall a, inG a -> forall n, inG (ring_times a n).
Proof.
	by intros a ain; exact (ibo_power_in _ _ pwelldef _ in0 _ ain).
Qed.
Lemma ring_times_0 : forall a, ring_times a 0 = G0.
Proof.
	by cbv delta [ring_times]; exact (power_0 _ _).
Qed.
Lemma ring_times_comm :
 forall a, inG a -> forall n, a <+> (ring_times a n) = (ring_times a n) <+> a.
Proof.
	by cbv delta [ring_times]; exact (ibo_power_comm _ _ pwelldef _ in0 zero_neut passoc).
Qed.
Definition ring_power a n := ibo_power dot G1 a n.
Lemma ring_power_in : forall a, inG a -> forall n, inG (ring_power a n).
Proof.
	by intros a ain; exact (ibo_power_in _ _ twelldef _ in1 _ ain).
Qed.
Lemma ring_power_0 : forall a, ring_power a 0 = G1.
Proof.
	by cbv delta [ring_power]; exact (power_0 _ _).
Qed.
Lemma ring_power_comm :
 forall a, inG a -> forall n, a <*> (ring_power a n) = (ring_power a n) <*> a.
Proof.
	by cbv delta [ring_power]; exact (ibo_power_comm _ _ twelldef _ in1 unit_neut tassoc).
Qed.

Lemma ring_inv_dot : forall a b, inS a -> inS b -> inS (a <*> b).
Proof.
	intros a b [ain [ainv [ainvin Hainv]]] [bin [binv [binvin Hbinv]]].
	split. by exact (twelldef _ _ ain bin).
	exists (binv <*> ainv); split; [|split].
	by exact (twelldef _ _ binvin ainvin).
	by rewrite (tassoc _ _ _ (twelldef _ _ ain bin) binvin ainvin),
	           <-(tassoc _ _ _ ain bin binvin), (and_l Hbinv),
	           (and_r (unit_neut _ ain));
	 exact (and_l Hainv).
	by rewrite (tassoc _ _ _ (twelldef _ _ binvin ainvin) ain bin),
	           <-(tassoc _ _ _ binvin ainvin ain), (and_r Hainv),
	           (and_r (unit_neut _ binvin));
	 exact (and_r Hbinv).
Qed.

Let ring_group_in1 : inS G1 := conj in1 (ex_intro _ _ (conj in1 (unit_neut _ in1))).
Let ring_group_dot_neutral : ibo_neutral inv_set dot G1 ring_group_in1 :=
	ibo_neutral_incl
	 _ _ _ _
	 ring_group_in1
	 (rng_inv_set_incl Grg)
	 unit_neut.
Definition RingInversibleGroup := {|
	gp_e_in        := ring_group_in1
;	gp_dot_in      := ring_inv_dot
;	gp_dot_neutral := ring_group_dot_neutral
;	gp_dot_assoc   := ibo_assoc_incl _ _ _ (rng_inv_set_incl Grg) tassoc
;	gp_inv_in      := iwelldef
;	gp_inv_dot     := dotinv
|}.

Lemma ring_zero_dot_l : forall a, inG a -> a <*> G0 = G0.
Proof.
	intros a ain.
	specialize (f_equal (fun x => a <*> x) (and_l (zero_neut _ in0))) as P;
	 cbv beta in P.
	rewrite (and_l (distrib _ _ _ ain in0 in0)) in P.
	apply (f_equal (fun x => x <+> (minus (a <*> G0)))) in P.
	rewrite <-(passoc _ _ _ (twelldef _ _ ain in0) (twelldef _ _ ain in0)
	   (mwelldef _ (twelldef _ _ ain in0))),
	  (and_r (plusminus _ (twelldef _ _ ain in0))),
	  (and_r (zero_neut _ (twelldef _ _ ain in0))) in P.
	by exact P.
Qed.
Lemma ring_zero_dot_r : forall a, inG a -> G0 <*> a = G0.
Proof.
	intros a ain.
	specialize (f_equal (fun x => x <*> a) (and_l (zero_neut _ in0))) as P;
	 cbv beta in P.
	rewrite (and_r (distrib _ _ _ in0 in0 ain)) in P.
	apply (f_equal (fun x => x <+> (minus (G0 <*> a)))) in P.
	rewrite <-(passoc _ _ _ (twelldef _ _ in0 ain) (twelldef _ _ in0 ain)
	   (mwelldef _ (twelldef _ _ in0 ain))),
	  (and_r (plusminus _ (twelldef _ _ in0 ain))),
	  (and_r (zero_neut _ (twelldef _ _ in0 ain))) in P.
	by exact P.
Qed.

Lemma ring_minus_dot_l : forall a b, inG a -> inG b -> (minus a) <*> b = minus (a <*> b).
Proof.
	intros a b ain bin.
	apply (group_dot_injective_l Ggp _ _ _
		(twelldef _ _ ain bin)
		(twelldef _ _ (mwelldef _ ain) bin)
		(mwelldef _ (twelldef _ _ ain bin))).
	rewrite <-(and_r (distrib _ _ _ ain (mwelldef _ ain) bin)).
	rewrite (and_r (plusminus _ ain)),
	        (and_r (plusminus _ (twelldef _ _ ain bin))).
	by exact (ring_zero_dot_r _ bin).
Qed.
Lemma ring_minus_dot_r : forall a b, inG a -> inG b -> a <*> (minus b) = minus (a <*> b).
Proof.
	intros a b ain bin.
	apply (group_dot_injective_l Ggp _ _ _
		(twelldef _ _ ain bin)
		(twelldef _ _ ain (mwelldef _ bin))
		(mwelldef _ (twelldef _ _ ain bin))).
	rewrite <-(and_l (distrib _ _ _ ain bin (mwelldef _ bin))).
	rewrite (and_r (plusminus _ bin)),
	        (and_r (plusminus _ (twelldef _ _ ain bin))).
	by exact (ring_zero_dot_l _ ain).
Qed.

Definition LeftIdeal     I :=
	(CommSubgroupHyp Grg.(rng_gp) I) /\ (forall a i, inG a -> In _ I i -> In _ I (a <*> i)).
Definition RightIdeal    I :=
	(CommSubgroupHyp Grg.(rng_gp) I) /\ (forall a i, inG a -> In _ I i -> In _ I (i <*> a)).
Definition TwoSidedIdeal I := LeftIdeal I /\ RightIdeal I.

Lemma inv_in_leftideal : forall i, inS i -> forall I, LeftIdeal I -> In _ I i -> Same_set _ I GG.
Proof.
	intros i iinS I [[Iincl _] lidI] iinI; split.
	by exact Iincl.
	intros g gin.
	specialize (lidI
		(g <*> (inv i)) i
		(twelldef _ _ gin (rng_inv_set_incl _ _ (iwelldef _ iinS))) iinI) as H.
	by rewrite
	 <-(tassoc _ _ _ gin (rng_inv_set_incl _ _ (iwelldef _ iinS)) (Iincl _ iinI)),
	   (and_l (dotinv _ iinS)), (and_r (unit_neut _ gin)) in H; exact H.
Qed.
Lemma inv_in_rightideal : forall i, inS i -> forall I, RightIdeal I -> In _ I i -> Same_set _ I GG.
Proof.
	intros i iinS I [[Iincl _] ridI] iinI; split.
	by exact Iincl.
	intros g gin.
	specialize (ridI
		((inv i) <*> g) i
		(twelldef _ _ (rng_inv_set_incl _ _ (iwelldef _ iinS)) gin) iinI) as H.
	by rewrite
	   (tassoc _ _ _ (Iincl _ iinI) (rng_inv_set_incl _ _ (iwelldef _ iinS)) gin),
	   (and_r (dotinv _ iinS)), (and_l (unit_neut _ gin)) in H; exact H.
Qed.
Lemma inv_in_twosidedideal : forall i, inS i -> forall I, TwoSidedIdeal I -> In _ I i -> Same_set _ I GG.
Proof.
	intros i iinS I [lidI _].
	by exact (inv_in_leftideal i iinS I lidI).
Qed.

Lemma inter_lideal I (lI : LeftIdeal I) J (lJ : LeftIdeal J) : LeftIdeal (intersection I J).
Proof.
	destruct lI as [[Iincl [Inotempty Isubgp]] lI];
	destruct lJ as [[Jincl [Jnotempty Jsubgp]] lJ].
	split; [split; [|split]|].
	by intros x [xinI _]; exact (Iincl _ xinI).
	exists G0; split.
	by exact ((SubgroupFromHyp _ _ (conj Iincl (conj Inotempty Isubgp))).(gp_e_in)).
	by exact ((SubgroupFromHyp _ _ (conj Jincl (conj Jnotempty Jsubgp))).(gp_e_in)).
	intros a b [ainI ainJ] [binI binJ]; split.
	by exact (Isubgp _ _ ainI binI).
	by exact (Jsubgp _ _ ainJ binJ).
	intros a i ain [iinI iinJ]; split.
	by exact (lI _ _ ain iinI).
	by exact (lJ _ _ ain iinJ).
Qed.
Lemma inter_rideal I (rI : RightIdeal I) J (rJ : RightIdeal J) : RightIdeal (intersection I J).
Proof.
	destruct rI as [[Iincl [Inotempty Isubgp]] rI];
	destruct rJ as [[Jincl [Jnotempty Jsubgp]] rJ].
	split; [split; [|split]|].
	by intros x [xinI _]; exact (Iincl _ xinI).
	exists G0; split.
	by exact ((SubgroupFromHyp _ _ (conj Iincl (conj Inotempty Isubgp))).(gp_e_in)).
	by exact ((SubgroupFromHyp _ _ (conj Jincl (conj Jnotempty Jsubgp))).(gp_e_in)).
	intros a b [ainI ainJ] [binI binJ]; split.
	by exact (Isubgp _ _ ainI binI).
	by exact (Jsubgp _ _ ainJ binJ).
	intros a i ain [iinI iinJ]; split.
	by exact (rI _ _ ain iinI).
	by exact (rJ _ _ ain iinJ).
Qed.
Lemma inter_ideal I (iI : TwoSidedIdeal I) J (iJ : TwoSidedIdeal J) : TwoSidedIdeal (intersection I J).
Proof.
	destruct iI as [lI rI];
	destruct iJ as [lJ rJ].
	split.
	by exact (inter_lideal _ lI _ lJ).
	by exact (inter_rideal _ rI _ rJ).
Qed.

Lemma plus_lideal I (lI : LeftIdeal I) J (lJ : LeftIdeal J)
 : LeftIdeal (PlusGroupFromHyp _ _ (and_l lI) _ (and_l lJ)).(gp_G).
Proof.
	split; [pose (gPl := PlusGroupFromHyp _ _ (and_l lI) _ (and_l lJ)); split; [|split]|];
	destruct lI as [[Iincl [Inotempty Isubgp]] lI];
	destruct lJ as [[Jincl [Jnotempty Jsubgp]] lJ].
	by exact (plusgp_incl _ _ Iincl _ Jincl).
	by exact (ex_intro _ _ (plusgp_neut_in _ _ Iincl Inotempty Isubgp _ Jincl Jnotempty Jsubgp)).
	by exact (plusgp_subgroup _ _ Iincl Inotempty Isubgp _ Jincl Jnotempty Jsubgp).
	cbv beta delta [In and_l and_r] zeta iota; simpl.
	intros a b ainG [bI [bJ [[bIin bJin] Hb]]].
	exists (a <*> bI), (a <*> bJ).
	split; [split|].
	by exact (lI _ _ ainG bIin).
	by exact (lJ _ _ ainG bJin).
	rewrite <-(and_l (Grg.(rng_dot_distrib) _ _ _ ainG (Iincl _ bIin) (Jincl _ bJin))), Hb.
	by exact (eq_refl _).
Qed.
Lemma plus_rideal I (rI : RightIdeal I) J (rJ : RightIdeal J)
 : RightIdeal (PlusGroupFromHyp _ _ (and_l rI) _ (and_l rJ)).(gp_G).
Proof.
	split; [pose (gPl := PlusGroupFromHyp _ _ (and_l rI) _ (and_l rJ)); split; [|split]|];
	destruct rI as [[Iincl [Inotempty Isubgp]] rI];
	destruct rJ as [[Jincl [Jnotempty Jsubgp]] rJ].
	by exact (plusgp_incl _ _ Iincl _ Jincl).
	by exact (ex_intro _ _ (plusgp_neut_in _ _ Iincl Inotempty Isubgp _ Jincl Jnotempty Jsubgp)).
	by exact (plusgp_subgroup _ _ Iincl Inotempty Isubgp _ Jincl Jnotempty Jsubgp).
	cbv beta delta [In and_l and_r] zeta iota; simpl.
	intros a b ainG [bI [bJ [[bIin bJin] Hb]]].
	exists (bI <*> a), (bJ <*> a).
	split; [split|].
	by exact (rI _ _ ainG bIin).
	by exact (rJ _ _ ainG bJin).
	rewrite <-(and_r (Grg.(rng_dot_distrib) _ _ _ (Iincl _ bIin) (Jincl _ bJin) ainG)), Hb.
	by exact (eq_refl _).
Qed.
Lemma plus_ideal I (iI : TwoSidedIdeal I) J (iJ : TwoSidedIdeal J)
 : TwoSidedIdeal (PlusGroupFromHyp _ _ (and_l (and_l iI)) _ (and_l (and_l iJ))).(gp_G).
Proof.
	destruct iI as [lI rI];
	destruct iJ as [lJ rJ].
	split.
	by exact (plus_lideal _ lI _ lJ).
	by exact (plus_rideal _ rI _ rJ).
Qed.

Lemma leftideal_from_a a (ain : inG a) :
 LeftIdeal (fun x => exists b, inG b /\ x = b <*> a).
Proof.
	split; [split; [|split]|].
	intros x [b [bin beq]].
	by rewrite beq; exact (twelldef _ _ bin ain).
	exists a, G1; split.
	by exact in1.
	by symmetry; exact (and_l (unit_neut _ ain)).
	intros x y [x' [x'in x'eq]] [y' [y'in y'eq]].
	exists (x' <+> (minus y')).
	split.
	by exact (pwelldef _ _ x'in (mwelldef _ y'in)).
	rewrite (and_r (distrib _ _ _ x'in (mwelldef _ y'in) ain)).
	rewrite (ring_minus_dot_l _ _ y'in ain), <-x'eq, <-y'eq.
	by exact (eq_refl _).
	intros b i bin [j [jin eqj]].
	exists (b <*> j).
	split.
	by exact (twelldef _ _ bin jin).
	by rewrite eqj, (tassoc _ _ _ bin jin ain); exact (eq_refl _).
Qed.
Lemma rightideal_from_a a (ain : inG a) :
 RightIdeal (fun x => exists b, inG b /\ x = a <*> b).
Proof.
	split; [split; [|split]|].
	intros x [b [bin beq]].
	by rewrite beq; exact (twelldef _ _ ain bin).
	exists a, G1; split.
	by exact in1.
	by symmetry; exact (and_r (unit_neut _ ain)).
	intros x y [x' [x'in x'eq]] [y' [y'in y'eq]].
	exists (x' <+> (minus y')).
	split.
	by exact (pwelldef _ _ x'in (mwelldef _ y'in)).
	rewrite (and_l (distrib _ _ _ ain x'in (mwelldef _ y'in))).
	rewrite (ring_minus_dot_r _ _ ain y'in), <-x'eq, <-y'eq.
	by exact (eq_refl _).
	intros b i bin [j [jin eqj]].
	exists (j <*> b).
	split.
	by exact (twelldef _ _ jin bin).
	by rewrite eqj, (tassoc _ _ _ ain jin bin); exact (eq_refl _).
Qed.

Definition AnneauIntegre := forall a b, inG a -> inG b -> (a <*> b = G0) -> (a = G0) \/ (b = G0).

End Rings.
Section CommRings.
Context {G : Type}.
Variable Gcrg : CommUnitaryRing G.
Notation "'Grg'" := Gcrg.(crg_r).
Notation "'Ggp'" := Grg.(rng_gp).(cgp_g).
Notation "'G0'" := Ggp.(gp_e).
Notation "'G1'" := Grg.(rng_unit).
Notation "'GG'" := Ggp.(gp_G).
Local Infix "<+>" := Ggp.(gp_dot) (at level 50, left associativity).
Local Infix "<*>" := Grg.(rng_dot) (at level 50, left associativity).
Notation "'plus'" := Ggp.(gp_dot).
Notation "'minus'" := Ggp.(gp_inv).
Notation "'dot'" := Grg.(rng_dot).
Notation "'inv'" := Grg.(rng_inv).
Notation "'plusminus'" := Ggp.(gp_inv_dot).
Notation "'dotinv'" := Grg.(rng_inv_dot).
Notation "'in0'" := Ggp.(gp_e_in).
Notation "'in1'" := Grg.(rng_unit_in).
Notation "'pwelldef'" := Ggp.(gp_dot_in).
Notation "'mwelldef'" := Ggp.(gp_inv_in).
Notation "'twelldef'" := Grg.(rng_dot_in).
Notation "'iwelldef'" := Grg.(rng_inv_in).
Notation "'zero_neut'" := Ggp.(gp_dot_neutral).
Notation "'unit_neut'" := Grg.(rng_dot_unit).
Notation "'passoc'" := Ggp.(gp_dot_assoc).
Notation "'tassoc'" := Grg.(rng_dot_assoc).
Notation "'inG'" := (In _ GG).
Notation "'inv_set'" := (rng_inv_set Grg).
Notation "'inS'" := (In _ inv_set).

Definition CommRingInversibleGroup := {|
	cgp_g := RingInversibleGroup Gcrg.(crg_r)
;	cgp_dot_commu := ibo_commu_incl _ _ _ (rng_inv_set_incl Grg) Gcrg.(crg_commu)
|}.

End CommRings.

Require Import ZArith.
Section Z.
Local Open Scope Z_scope.
Definition ZG : Ensemble Z := fun x : Z => True.
Lemma Zgp_neut_in: In _ ZG 0.
Proof.
	by exact I.
Qed.
Lemma Zgp_dot_in: ibo ZG Zplus.
Proof.
	intros a b _ _.
	by exact I.
Qed.
Lemma Zgp_dot_neutral: ibo_neutral _ Zplus _ Zgp_neut_in.
Proof.
	intros a _.
	split.
	by unfold Zplus; exact (eq_refl _).
	by destruct a as [|a|a]; unfold Zplus; exact (eq_refl _).
Qed.
Lemma Zgp_dot_assoc: ibo_assoc ZG Zplus.
Proof.
	intros a b c _ _ _.
	by exact (Z.add_assoc _ _ _).
Qed.
Lemma Zgp_inv_in: fun_well_defined ZG ZG Z.opp.
Proof.
	by intros a _; exact I.
Qed.
Lemma Zgp_inv_dot: ibo_inverse _ Zplus _ Zgp_neut_in Zgp_dot_neutral _ Zgp_inv_in.
Proof.
	by intros a _; split;
	 [rewrite (Z.add_comm _ _)|]; exact (Z.add_opp_diag_r _).
Qed.
Definition Z_group :=  {|
	gp_e_in        := Zgp_neut_in
;	gp_dot_in      := Zgp_dot_in
;	gp_dot_neutral := Zgp_dot_neutral
;	gp_dot_assoc   := Zgp_dot_assoc
;	gp_inv_in      := Zgp_inv_in
;	gp_inv_dot     := Zgp_inv_dot
|}.

Lemma Zgp_dot_comm : ibo_commu ZG Zplus.
Proof.
	by intros a b _ _; exact (Z.add_comm _ _).
Qed.
Definition Z_commgroup := {|
	cgp_g := Z_group
;	cgp_dot_commu := Zgp_dot_comm
|}.

Definition Zinv := fun x : Z => x.
Lemma Zrg_mult_in : ibo ZG Zmult.
Proof.
	by intros ? ? _ _; exact I.
Qed.
Lemma Zrg_mult_assoc : ibo_assoc ZG Zmult.
Proof.
	by intros a b c _ _ _; exact (Z.mul_assoc _ _ _).
Qed.
Lemma Zrg_unit_in : In _ ZG 1.
Proof.
	by exact I.
Qed.
Lemma Zrg_dot_unit : ibo_neutral _ Zmult _ Zrg_unit_in.
Proof.
	by intros ? _; split; [|rewrite (Z.mul_comm _ _)]; exact (Z.mul_1_l _).
Qed.
Lemma Zrg_dot_distrib : ibo_distrib_over ZG Zmult Zplus.
Proof.
	by intros a b c _ _ _; split; [rewrite (Z.mul_comm _ _)|];
	 rewrite (Z.mul_add_distr_r _ _ _);
	 [rewrite (Z.mul_comm b a), (Z.mul_comm c a)|];
	 exact (eq_refl _).
Qed.
Lemma Zrg_0ne1 : 0 <> 1.
Proof.
	discriminate 1.
Qed.
Lemma Zrg_inv_set_eq : Same_set _ (ibo_symmetrisable_set ZG Zmult 1) (fun x => x = 1 \/ x = -1).
Proof.
	split.
	intros s [sin [b [bin [sbe bse]]]].
	destruct s as [|s|s].
	by unfold Zmult in sbe; discriminate sbe.
	1,2: destruct b as [|b|b].
	1,4: by unfold Zmult in bse; discriminate bse.
	unfold Zmult in sbe.
	remember 1 as one eqn:oneeq; rewrite oneeq in sbe.
	inversion sbe as [sbe'].
	specialize (Pos.mul_eq_1_l _ _ sbe') as sbe''.
	by rewrite oneeq, sbe''; left; exact (eq_refl _).
	1,2: by unfold Zmult in sbe; discriminate sbe.
	remember (-1) as none eqn:noneeq.
	inversion sbe as [sbe'].
	specialize (Pos.mul_eq_1_l _ _ sbe') as sbe''.
	by rewrite noneeq, sbe''; right; exact (eq_refl _).
	
	intros x [xe1 | xen1]; split.
	1,3: by exact I.
	1,2: exists x; split; [by exact I|split].
	1,2: by rewrite xe1; exact (Z.mul_1_l _).
	1,2: by rewrite xen1; unfold Zmult, Pos.mul; exact (eq_refl _).
Qed.
Lemma Zrg_inv_in : fun_well_defined (ibo_symmetrisable_set ZG Zmult 1) (ibo_symmetrisable_set ZG Zmult 1) Zinv.
Proof.
	by intros a aininv; exact aininv.
Qed.
Let unit_inv : In _ (ibo_symmetrisable_set ZG Zmult 1) 1.
	destruct Zrg_inv_set_eq as [_ H]; apply H; clear H.
	by left; exact (eq_refl).
Defined.
Lemma Zrg_inv_dot :
	 ibo_inverse
	  (ibo_symmetrisable_set ZG Zmult 1)
	  Zmult
	  1
	  unit_inv
	  (ibo_neutral_incl
	    ZG
		(ibo_symmetrisable_set ZG Zmult 1)
		_ _
		unit_inv
		(fun x xinS => let (xin, _) := xinS in xin)
		Zrg_dot_unit)
	  Zinv
	  Zrg_inv_in.
Proof.
	intros a ain; unfold Zinv.
	clear unit_inv.
	destruct Zrg_inv_set_eq as [incL incR]; apply incL in ain; split.
	all: destruct ain as [ae1 | aen1].
	1,3: by rewrite ae1; exact (Z.mul_1_l _).
	1,2: by rewrite aen1; unfold Zmult, Pos.mul; exact (eq_refl _).
Qed.
Definition Z_ring :=  {|
	rng_gp := Z_commgroup
;	rng_dot := Zmult
;	rng_dot_in := Zrg_mult_in
;	rng_dot_assoc := Zrg_mult_assoc
;	rng_unit_in := Zrg_unit_in
;	rng_dot_unit := Zrg_dot_unit
;	rng_dot_distrib := Zrg_dot_distrib
;	rng_zero_ne_one := Zrg_0ne1
;	rng_inv_in := Zrg_inv_in
;	rng_inv_dot := Zrg_inv_dot
|}.

Lemma Zcr_comm : ibo_commu ZG Zmult.
Proof.
	by intros a b _ _; exact (Z.mul_comm _ _).
Qed.
Definition Z_commring := {|
	crg_r := Z_ring
;	crg_commu := Zcr_comm
|}.

Lemma Z_integre : AnneauIntegre Z_ring.
Proof.
	cbv beta delta [
		AnneauIntegre
		In
		Z_ring rng_gp rng_dot
		Z_commgroup cgp_g
		Z_group gp_G gp_e
		ZG
		] iota zeta;
	intros a b _ _;
	intros abeq0.
	destruct a as [|a|a].
	by left; exact (eq_refl _).
	all: destruct b as [|b|b].
	1,4: by right; exact (eq_refl _).
	all: by unfold Zmult in abeq0; discriminate abeq0.
Qed.

Local Close Scope Z_scope.
End Z.
