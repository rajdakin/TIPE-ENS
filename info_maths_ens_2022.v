Require Import Classical.
From Coq Require Import Lists.List. Import ListNotations.

Module Epreuve.
Section General.
Record EnsembleFini : Type := mkEns {
	ens_E : Type;
	ens_L : list ens_E;
	ens_unique : let fix f E := match E with [] => True | x :: Es => ~(In x Es) /\ f Es end in f ens_L
}.
Definition Cardinal (A : EnsembleFini) :=
	let fix card l := match l with [] => O | _ :: tl => S (card tl) end in card A.(ens_L).
Notation "x 'inL' E" := (In x E.(ens_L)) (at level 71, no associativity).
Context (A : EnsembleFini).
Notation "'AE'" := A.(ens_E).
Notation "'AL'" := A.(ens_L).
Notation "'Aun'" := A.(ens_unique).

Notation "'Astar'" := (list AE).
Fixpoint InAstar (w : Astar) := match w with [] => True | a :: u => a inL A /\ InAstar u end.

Record Automate : Type := mkAuto {
	aut_X : EnsembleFini;
	
	aut_o : aut_X.(ens_E) -> bool;
	(* aut_o_wd : forall x, x inL aut_X -> (aut_o x) \/ ~(aut_o x); *)
	
	aut_delta : aut_X.(ens_E) -> AE -> aut_X.(ens_E);
	aut_delta_wd : forall x a, x inL aut_X -> a inL A -> (aut_delta x a) inL aut_X
}.
Fixpoint deltastar aut x (w : Astar) := match w with
	| [] => x
	| a :: u => deltastar aut (aut.(aut_delta) x a) u
end.
Lemma aut_deltastar_wd (aut : Automate) :
	forall x w (xin : x inL aut.(aut_X)) (wwd : InAstar w), (deltastar aut x w) inL aut.(aut_X).
Proof.
	intros x w; generalize dependent x; induction w as [|a u IHu]; intros x xin auin.
	unfold deltastar; exact xin.
	unfold InAstar in auin; fold InAstar in auin; destruct auin as [ain uin].
	unfold deltastar; fold deltastar.
	exact (IHu _ (aut.(aut_delta_wd) _ _ xin ain) uin).
Qed.

Definition Ensemble U := U -> Prop.
Definition InE {U} (E : Ensemble U) x := E x. Hint Unfold InE : core.
Notation "x 'inE' E" := (InE E x) (at level 71, no associativity).
Notation "E 'eqE' F" := (forall x, x inE E <-> x inE F) (at level 71, no associativity).

Axiom set_extensionality : forall {U} (E : Ensemble U) F, E eqE F -> E = F.

Definition Language aut : aut.(aut_X).(ens_E) -> Ensemble Astar :=
	fun x u => aut.(aut_o) (deltastar aut x u) = true.
Corollary epsilon_in_L_iff aut : forall x, [] inE (Language aut x) <-> aut.(aut_o) x = true.
Proof.
	intros x; unfold InE, Language, deltastar; reflexivity.
Qed.
Corollary au_in_L_iff aut :
	forall x a u, a inL A -> (a :: u inE (Language aut x) <-> u inE (Language aut (aut.(aut_delta) x a))).
Proof.
	intros x a u ain; unfold InE, Language, deltastar; fold deltastar; reflexivity.
Qed.

Remark eq_true_iff_eq_true : forall a b, (a = true <-> b = true) <-> (a = b).
Proof.
	intros [|] [|]; split.
	1,7: intros _; exact (eq_refl _).
	1,6: intros _; split; intros H; exact H.
	intros [f _]; symmetry; exact (f (eq_refl _)).
	intros f; exact (False_ind _ (eq_ind true (fun b : bool => if b then True else False) I _ f)).
	intros [_ f]; exact (f (eq_refl _)).
	intros f; exact (False_ind _ (eq_ind false (fun b : bool => if b then False else True) I _ f)).
Qed.
Definition Equiv aut x y :=
	((x inL aut.(aut_X)) /\ (y inL aut.(aut_X))) /\
	(forall u, InAstar u -> aut.(aut_o) (deltastar aut x u) = aut.(aut_o) (deltastar aut y u)).
Corollary Equiv_on_languages aut x y :
	Equiv aut x y <->
	(((x inL aut.(aut_X)) /\ (y inL aut.(aut_X)))
	 /\ (forall u, InAstar u -> u inE (Language aut x) <-> u inE (Language aut y))).
Proof.
	unfold Equiv, InE, Language; split.
	intros [l r]; split; [exact l|intros u uin; apply eq_true_iff_eq_true; exact (r u uin)].
	intros [l r]; split; [exact l|intros u uin; apply eq_true_iff_eq_true; exact (r u uin)].
Qed.

Section Partie2.
Context {U : Type} (E : U -> Prop).
Definition Subset (X : Ensemble U) Y := forall x, x inE X -> x inE Y.
Definition Union X Y : Ensemble U := fun x => x inE X \/ x inE Y.
Definition Inter X Y : Ensemble U := fun x => x inE X /\ x inE Y.

Notation "X 'subE' Y" := (Subset X Y) (at level 71, no associativity).
Notation "X 'unionE' Y" := (Union X Y) (at level 70, right associativity).
Notation "X 'interE' Y" := (Inter X Y) (at level 70, right associativity).

Lemma sub_refl : forall X, X subE X.
Proof. intros X x xin; exact xin. Qed.
Lemma sub_trans : forall X Y Z, X subE Y -> Y subE Z -> X subE Z.
Proof.
	intros X Y Z XsY YsZ x xin; exact (YsZ _ (XsY _ xin)).
Qed.
Lemma sub_antisym : forall X Y, X subE Y -> Y subE X -> X eqE Y.
Proof.
	intros X Y XsY YsX x; split; intros xin; [exact (XsY x xin)|exact (YsX x xin)].
Qed.

Lemma empty_sub : forall X, (fun _ => False) subE X.
Proof. intros X x []. Qed.
Lemma sub_full : forall X, X subE (fun _ => True).
Proof. intros X x _; exact I. Qed.

Lemma in_union_l : forall X Y x, x inE X -> x inE X unionE Y.
Proof.
	intros X Y x xin.
	unfold InE, Union; left; exact xin.
Qed.
Lemma in_union_r : forall X Y x, x inE Y -> x inE X unionE Y.
Proof.
	intros X Y x xin.
	unfold InE, Union; right; exact xin.
Qed.
Lemma in_union : forall X Y x, x inE X unionE Y -> x inE X \/ x inE Y.
Proof.
	intros X Y x xin.
	unfold Union, InE in *; exact xin.
Qed.
Lemma sub_is_union : forall X Y, X subE Y -> X unionE Y eqE Y.
Proof.
	intros X Y XsY; unfold Union, InE; split.
	intros [xin|xin].
	exact (XsY _ xin).
	exact xin.
	exact (in_union_r _ _ _).
Qed.
Lemma union_is_sub : forall X Y, X unionE Y eqE Y -> X subE Y.
Proof.
	unfold Subset, Union, InE; intros X Y XYeqY x xinX.
	apply XYeqY.
	left; exact xinX.
Qed.
Lemma sub_union : forall X Y, X subE Y <-> X unionE Y eqE Y.
Proof. intros X Y; split; [exact (sub_is_union _ _)|exact (union_is_sub _ _)]. Qed.
Lemma sub_union_sub : forall X Y Z, X subE Z -> Y subE Z -> X unionE Y subE Z.
Proof.
	intros X Y Z XsubZ YsubZ x [xinX|xinY].
	exact (XsubZ _ xinX).
	exact (YsubZ _ xinY).
Qed.

Lemma in_inter_l : forall X Y x, x inE X interE Y -> x inE X.
Proof. intros X Y x [xinX _]; exact xinX. Qed.
Lemma in_inter_r : forall X Y x, x inE X interE Y -> x inE Y.
Proof. intros X Y x [_ xinY]; exact xinY. Qed.
Lemma in_inter_lr : forall X Y x, x inE X interE Y -> x inE X /\ x inE Y.
Proof. intros X Y x xinXiY; exact xinXiY. Qed.
Lemma in_inter : forall X Y x, x inE X -> x inE Y -> x inE X interE Y.
Proof. intros X Y x xinX xinY; split; [exact xinX|exact xinY]. Qed.
Lemma l_sub_inter_sub : forall X Y Z, X subE Z -> X interE Y subE Z.
Proof. intros X Y Z XsubZ x [xinX _]; exact (XsubZ _ xinX). Qed.
Lemma r_sub_inter_sub : forall X Y Z, Y subE Z -> X interE Y subE Z.
Proof. intros X Y Z YsubZ x [_ xinY]; exact (YsubZ _ xinY). Qed.

Definition Famille_Ewd Xs := forall Y, Y inE Xs -> Y subE E.
Definition Suite_Ewd {V} Xi := forall v : V, Xi v subE E.
Definition Suite_croissante Xi := forall n : nat, Xi n subE Xi (S n).
Definition Suite_decroissante Xi := forall n : nat, Xi (S n) subE Xi n.

Lemma croissante_le : forall Xi, Suite_croissante Xi -> forall m n, m <= n -> Xi m subE Xi n.
Proof.
	intros Xi Xicr m n; generalize dependent m; induction n as [|n IHn]; intros m; [intros mleO|intros mleSn].
	rewrite <-(Le.le_n_0_eq _ mleO); exact (sub_refl _).
	inversion mleSn as [H|n' mlen Hn].
	exact (sub_refl _).
	exact (sub_trans (Xi m) (Xi n) (Xi (S n)) (IHn m mlen) (Xicr n)).
Qed.
Lemma decroissante_le : forall Xi, Suite_decroissante Xi -> forall m n, m <= n -> Xi n subE Xi m.
Proof.
	intros Xi Xide m n; generalize dependent m; induction n as [|n IHn]; intros m; [intros mleO|intros mleSn].
	rewrite <-(Le.le_n_0_eq _ mleO); exact (sub_refl _).
	inversion mleSn as [H|n' mlen Hn].
	exact (sub_refl _).
	exact (sub_trans (Xi (S n)) (Xi n) (Xi m) (Xide n) (IHn m mlen)).
Qed.

Definition PE := Ensemble (Ensemble U). Hint Unfold PE : core.
Notation "'SubE'" := (Ensemble U).
Notation "'FunPE'" := (SubE -> SubE).
Definition PE_wd : FunPE -> Prop := fun f => forall x, x subE E -> f x subE E. Hint Unfold PE_wd : core.

Definition id_PE : FunPE := fun x => x.
Lemma id_wd : PE_wd id_PE.
Proof.
	unfold PE_wd, id_PE, Subset, InE; intros ? P; exact P.
Qed.
Definition comp (f g : FunPE) : FunPE := fun x => f (g x).
Lemma comp_wd : forall f g (fwd : PE_wd f) (gwd : PE_wd g), PE_wd (comp f g).
Proof.
	unfold comp, PE_wd; intros f g fwd gwd.
	intros x xinE x0 x0infgx.
	exact (fwd _ (gwd _ xinE) _ x0infgx).
Qed.

Fixpoint Iteree f n := match n with
	| O => id_PE
	| S n => comp f (Iteree f n) end.
Notation "f ^ n" := (Iteree f n).
Lemma Iteree_wd f (fwd : PE_wd f) : forall n, PE_wd (Iteree f n).
Proof.
	intros n; induction n as [|n IHn]; unfold Iteree; fold Iteree.
	exact id_wd.
	exact (comp_wd _ _ fwd IHn).
Qed.
Lemma Iteree_sum f (fwd : PE_wd f) : forall m n, f ^ (m + n) = comp (f ^ m) (f ^ n).
Proof.
	intros m; induction m as [|m IHm]; intros n.
	unfold plus, comp, Iteree; fold Iteree plus comp; unfold id_PE; exact (eq_refl _).
	unfold plus; fold plus; unfold Iteree; fold Iteree; unfold comp; rewrite IHm; unfold comp.
	exact (eq_refl _).
Qed.

Definition UnionPE (f g : FunPE) : FunPE := fun x => (f x) unionE (g x).
Definition InterPE (f g : FunPE) : FunPE := fun x => (f x) interE (g x).
Notation "f 'unionF' g" := (UnionPE f g) (at level 70, right associativity).
Notation "f 'interF' g" := (InterPE f g) (at level 70, right associativity).
Lemma UnionPE_wd f g (fwd : PE_wd f) (gwd : PE_wd g) : PE_wd (f unionF g).
Proof.
	intros x xsub x0 x0inU.
	unfold UnionPE in x0inU; apply in_union in x0inU; destruct x0inU as [x0inf|x0ing].
	exact (fwd x xsub x0 x0inf).
	exact (gwd x xsub x0 x0ing).
Qed.
Lemma InterPE_wd f g (fwd : PE_wd f) (gwd : PE_wd g) : PE_wd (f interF g).
Proof.
	intros x xsub x0 x0inI.
	unfold InterPE in x0inI; apply in_inter_lr in x0inI; destruct x0inI as [x0inf _].
	exact (fwd x xsub x0 x0inf).
Qed.

Fixpoint Union_n (Ei : nat -> SubE) n : SubE := match n with
	| O => fun x => False
	| S n => (Ei n) unionE (Union_n Ei n) end.
Fixpoint Inter_n Ei n : SubE := match n with
	| O => fun x => x inE E
	| S n => (Ei n) interE (Inter_n Ei n) end.
Definition Union_N Ei : SubE := fun x => exists n : nat, x inE Ei n.
Definition Inter_N Ei : SubE := fun x => forall n : nat, x inE Ei n.
Corollary in_Union_N : forall Ei x, x inE (Union_N Ei) <-> exists n, x inE Ei n.
Proof. intros Ei x; split; [intros xin; unfold InE, Union_N in xin; exact xin|intros P; exact P]. Qed.
Corollary in_Inter_N : forall Ei x, x inE (Inter_N Ei) <-> forall n, x inE Ei n.
Proof. intros Ei x; split; [intros xin; unfold InE, Inter_N in xin; exact xin|intros P; exact P]. Qed.

Definition Union_Nf fi : FunPE := fun X => Union_N (fun i => fi i X).
Definition Inter_Nf fi : FunPE := fun X => Inter_N (fun i => fi i X).
Lemma Union_Nf_wd : forall fi, (forall n, PE_wd (fi n)) -> PE_wd (Union_Nf fi).
Proof.
	unfold PE_wd, Union_Nf; intros fi fiwd.
	intros x xsub y yinone; rewrite in_Union_N in yinone; destruct yinone as [n yin].
	exact (fiwd n x xsub y yin).
Qed.
Lemma Inter_Nf_wd : forall fi n, PE_wd (fi n) -> PE_wd (Inter_Nf fi).
Proof.
	unfold PE_wd, Inter_Nf; intros fi n finwd x xsub y yinall; rewrite in_Inter_N in yinall.
	exact (finwd x xsub y (yinall n)).
Qed.

Definition croissanteF (f : FunPE) := forall X Y, X subE Y -> Y subE E -> f X subE f Y.
Definition continueF (f : FunPE) :=
	forall Xi, Suite_Ewd Xi -> Suite_croissante Xi -> f (Union_N Xi) = Union_N (fun n => f (Xi n)).
Definition cocontinueF (f : FunPE) :=
	forall Xi, Xi 0 subE E -> Suite_decroissante Xi -> f (Inter_N Xi) = Inter_N (fun n => f (Xi n)).

Lemma decroissante_wd : forall Xi, Xi 0 subE E -> Suite_decroissante Xi -> Suite_Ewd Xi.
Proof.
	intros Xi Xi0 Xid n; induction n as [|n IHn].
	exact Xi0.
	exact (sub_trans _ _ _ (Xid n) IHn).
Qed.

(* q2.1 *)
Theorem continue_croissante : forall f, continueF f -> croissanteF f.
Proof.
	intros f fC X Y XsY YsE x xinfX.
	pose (Xi := fun n => match n with O => X | S _ => Y end).
	assert (Xiwd : Suite_Ewd Xi) by (unfold Suite_Ewd, Xi; intros [|n]; [exact (sub_trans _ _ _ XsY YsE)|exact YsE]).
	assert (Xic : Suite_croissante Xi) by (unfold Suite_croissante, Xi; intros [|n]; [exact XsY|exact (sub_refl _)]).
	assert (HU : Union_N Xi eqE Y).
	{ clear f fC YsE x xinfX Xiwd Xic; intros x; split.
	  intros [[|n] xin]; subst Xi; simpl in xin. exact (XsY _ xin). exact xin.
	  intros xin; exists 1; simpl; exact xin. }
	apply set_extensionality in HU.
	specialize (fC Xi Xiwd Xic).
	rewrite HU in *; subst Xi; clear Xiwd Xic HU; rewrite fC.
	exists 0; exact xinfX.
Qed.
(* q2.2 *)
Theorem cocontinue_croissante : forall f, cocontinueF f -> croissanteF f.
Proof.
	intros f fC X Y XsY YsE x xinfX.
	pose (Xi := fun n => match n with O => Y | S _ => X end).
	assert (Xi0wd : Xi 0 subE E) by (unfold Xi; exact YsE).
	assert (Xid : Suite_decroissante Xi) by (unfold Suite_decroissante, Xi; intros [|n]; [exact XsY|exact (sub_refl _)]).
	assert (HI : Inter_N Xi eqE X).
	{ clear f fC YsE x xinfX Xi0wd Xid; intros x; split.
	  intros xin; exact (xin 1).
	  intros xin [|n]; subst Xi; simpl. exact (XsY _ xin). exact xin. }
	apply set_extensionality in HI.
	specialize (fC Xi Xi0wd Xid); rewrite HI in fC; subst Xi; clear Xi0wd Xid HI; rewrite fC in xinfX.
	exact (xinfX 0).
Qed.

Lemma id_croissante : croissanteF id_PE.
Proof.
	intros X Y XsY _; unfold id_PE; exact XsY.
Qed.
Lemma id_continue : continueF id_PE.
Proof.
	intros Xi _ _; unfold id_PE; exact (eq_refl _).
Qed.
Lemma id_cocontinue : cocontinueF id_PE.
Proof.
	intros Xi _ _; unfold id_PE; exact (eq_refl _).
Qed.
Lemma comp_croissante : forall f g, PE_wd g -> croissanteF f -> croissanteF g -> croissanteF (comp f g).
Proof.
	intros f g gwd fc gc X Y XsY YsE; unfold comp.
	refine (fc _ _ (gc _ _ XsY YsE) (gwd _ YsE)).
Qed.
Lemma comp_continue : forall f g, PE_wd g -> continueF f -> continueF g -> continueF (comp f g).
Proof.
	intros f g gwd fco gco Xi Xiwd Xic; unfold comp; apply set_extensionality; intros x; split.
	intros xinfgXi.
	rewrite (gco _ Xiwd Xic) in xinfgXi;
	rewrite (fco _ (fun n => gwd _ (Xiwd n)) (fun n => continue_croissante _ gco _ _ (Xic n) (Xiwd (S n)))) in xinfgXi.
	exact xinfgXi.
	intros xinfgXi.
	rewrite <-(fco _ (fun n => gwd _ (Xiwd n)) (fun n => continue_croissante _ gco _ _ (Xic n) (Xiwd (S n)))) in xinfgXi;
	rewrite <-(gco _ Xiwd Xic) in xinfgXi.
	exact xinfgXi.
Qed.
Lemma comp_cocontinue : forall f g, PE_wd g -> cocontinueF f -> cocontinueF g -> cocontinueF (comp f g).
Proof.
	intros f g gwd fcc gcc Xi Xi0wd Xid; unfold comp; apply set_extensionality; intros x; split; intros xinfgXi.
	rewrite (gcc _ Xi0wd Xid) in xinfgXi;
	rewrite (fcc _ (gwd _ Xi0wd)
		(fun n => cocontinue_croissante _ gcc _ _ (Xid n) (decroissante_wd _ Xi0wd Xid n))) in xinfgXi.
	exact xinfgXi.
	rewrite <-(fcc _ (gwd _ Xi0wd)
		(fun n => cocontinue_croissante _ gcc _ _ (Xid n) (decroissante_wd _ Xi0wd Xid n))) in xinfgXi;
	rewrite <-(gcc _ Xi0wd Xid) in xinfgXi.
	exact xinfgXi.
Qed.
Lemma union_croissante : forall f g, croissanteF f -> croissanteF g -> croissanteF (f unionF g).
Proof.
	intros f g fc gc X Y XsY YsE; unfold UnionPE; apply sub_union_sub.
	intros x xinfX; exact (in_union_l _ _ _ (fc _ _ XsY YsE _ xinfX)).
	intros x xingX; exact (in_union_r _ _ _ (gc _ _ XsY YsE _ xingX)).
Qed.
Lemma union_continue : forall f g, continueF f -> continueF g -> continueF (f unionF g).
Proof.
	intros f g fco gco Xi Xiwd Xic; apply set_extensionality; intros x; split.
	intros [xinfXi|xingXi].
	rewrite (fco _ Xiwd Xic) in xinfXi; destruct xinfXi as [n Hn]; exists n; left;  exact Hn.
	rewrite (gco _ Xiwd Xic) in xingXi; destruct xingXi as [n Hn]; exists n; right; exact Hn.
	intros [n [xin_Xn|xin_Xn]]; [left; rewrite (fco _ Xiwd Xic)|right; rewrite (gco _ Xiwd Xic)]; exists n; exact xin_Xn.
Qed.
Lemma union_cocontinue : forall f g, cocontinueF f -> cocontinueF g -> cocontinueF (f unionF g).
Proof.
	intros f g fcc gcc Xi Xi0wd Xid; apply set_extensionality; intros x; split.
	intros [xinfXi|xingXi] n.
	rewrite (fcc _ Xi0wd Xid) in xinfXi; left;  exact (xinfXi _).
	rewrite (gcc _ Xi0wd Xid) in xingXi; right; exact (xingXi _).
	intros Hx.
	unfold UnionPE;
	rewrite (fcc _ Xi0wd Xid);
	rewrite (gcc _ Xi0wd Xid);
	unfold Union, InE.
	unfold InE, Inter_N in Hx.
	specialize (classic (forall n0, x inE f (Xi n0))) as [Hf|Hf].
	left; exact Hf.
	apply not_all_ex_not in Hf; destruct Hf as [n0 Hn0]; right; intros n.
	assert (H : forall n, n0 <= n -> ~ x inE f (Xi n)).
	{ clear n; intros n n0len; induction n0len as [|n n0len IH].
	  exact Hn0.
	   intros xinfSn; exact (IH (cocontinue_croissante _ fcc _ _ (Xid n) (decroissante_wd _ Xi0wd Xid n) _ xinfSn)). }
	assert (Hg : forall n, n0 <= n -> x inE g (Xi n)) by
	  (intros n1 n0len1; destruct (Hx n1) as [l|r]; [contradiction (H _ n0len1 l)|exact r]).
	specialize (PeanoNat.Nat.le_gt_cases n0 n) as [n0len|n0gtn].
	exact (Hg _ n0len).
	clear f fcc Hx Hn0 H; unfold lt in n0gtn; remember (S n) as Sn eqn:eqSn; induction n0gtn as [|n0 Hn0 IH]; subst Sn.
	exact (cocontinue_croissante _ gcc _ _ (Xid n) (decroissante_wd _ Xi0wd Xid _) _ (Hg _ (le_n _))).
	apply IH; clear IH; intros n1 n0len1; inversion n0len1 as [H|n2 Hn2]; subst.
	exact (cocontinue_croissante _ gcc _ _ (Xid _) (decroissante_wd _ Xi0wd Xid _) _ (Hg _ (le_n _))).
	exact (Hg _ (le_n_S _ _ Hn2)).
Qed.
Lemma Iteree_comm : forall f n X, (f ^ (S n)) X = (f ^ n) (f X).
Proof.
	intros f n X; induction n as [|n IHn].
	unfold Iteree, comp, id_PE; exact (eq_refl _).
	unfold Iteree; fold Iteree; unfold comp; rewrite <-IHn; unfold Iteree; fold Iteree; unfold comp.
	exact (eq_refl _).
Qed.
Lemma iteree_croissante : forall f n, PE_wd f -> croissanteF f -> croissanteF (f ^ n).
Proof.
	intros f n fwd fc X Y XsY YsE; induction n as [|n IHn].
	unfold Iteree, id_PE; exact XsY.
	intros x xinffnX; exact (fc _ _ IHn (Iteree_wd _ fwd _ _ YsE) _ xinffnX).
Qed.
Lemma iteree_continue : forall f n, PE_wd f -> continueF f -> continueF (f ^ n).
Proof.
	intros f n fwd fco; induction n as [|n IHn].
	exact id_continue.
	refine (comp_continue _ _ (Iteree_wd _ fwd _) fco IHn).
Qed.
Lemma iteree_cocontinue : forall f n, PE_wd f -> cocontinueF f -> cocontinueF (f ^ n).
Proof.
	intros f n fwd fco; induction n as [|n IHn].
	exact id_cocontinue.
	refine (comp_cocontinue _ _ (Iteree_wd _ fwd _) fco IHn).
Qed.

Definition PostPointFixe (f : FunPE) X := X subE E /\ X subE f X.
Definition PrePointFixe (f : FunPE) X := X subE E /\ f X subE X.
Definition PointFixe (f : FunPE) X := X subE E /\ X eqE f X.

(* q2.4.i *)
Theorem all_postpf: forall f, exists X, PostPointFixe f X.
Proof.
	intros f; exists (fun _ => False); split; exact (empty_sub _).
Qed.
Theorem all_prepf: forall f, PE_wd f -> exists X, PrePointFixe f X.
Proof.
	intros f; exists E; split.
	exact (sub_refl _).
	exact (H _ (sub_refl _)).
Qed.

(* q2.4.ii *)
Theorem no_fixpoint : forall x, (forall X, X subE E -> x inE X \/ ~(x inE X)) ->
	let f : FunPE := fun X x => ~ (x inE X) in forall X, X subE E -> ~(PointFixe f X).
Proof.
	lazy beta delta [PointFixe] zeta; intros x xinAll X XsE [_ XeqnX].
	specialize (XeqnX x) as [l r].
	specialize (xinAll X XsE) as [xin|xni].
	exact (l xin xin). exact (xni (r xni)).
Qed.
(* Take U = nat, E = (fun _ : nat => True) and x = 0 *)

Definition Union_generic {V} (X : Ensemble V) f : SubE := fun x => exists Y, Y inE X /\ x inE f Y.
Definition Inter_generic {V} (X : Ensemble V) f : SubE := fun x => forall Y, Y inE X -> x inE f Y.
Lemma in_UnionG {V} : forall X f x (Y : V), x inE f Y -> Y inE X -> x inE Union_generic X f.
Proof. intros X f x Y xinfY YinX; exists Y; exact (conj YinX xinfY). Qed.
Lemma UnionG_in {V} : forall X f x, x inE Union_generic X f -> exists Y : V, x inE f Y /\ Y inE X.
Proof. intros X f x [Y [l r]]; exists Y; exact (conj r l). Qed.
Lemma in_InterG {V} : forall X f x, (forall Y : V, Y inE X -> x inE f Y) -> x inE Inter_generic X f.
Proof. intros X f x Hx Y YinX; exact (Hx _ YinX). Qed.
Lemma InterG_in {V} : forall X f x, x inE Inter_generic X f -> forall Y : V, Y inE X -> x inE f Y.
Proof. intros X f x Hx Y YinX; exact (Hx _ YinX). Qed.
Lemma UnionG_sub {V} : forall X f (Y : V), Y inE X -> f Y subE Union_generic X f.
Proof. intros X f Y YinX x xinfY; exact (in_UnionG _ _ _ _ xinfY YinX). Qed.
Lemma InterG_sub {V} : forall X f (Y : V), Y inE X -> Inter_generic X f subE f Y.
Proof. intros X f Y YinX x xinI; exact (InterG_in _ _ _ xinI _ YinX). Qed.
Lemma UnionG_wd {V} : forall (X : Ensemble V) f, (forall Y, Y inE X -> f Y subE E) -> Union_generic X f subE E.
Proof. intros X f HX x [Y [YinX xinfY]]; exact (HX _ YinX _ xinfY). Qed.
Lemma InterG_wd {V} : forall (X : Ensemble V) f Y, Y inE X -> f Y subE E -> Inter_generic X f subE E.
Proof. intros X f Y YinX fYsubE x Hx; exact (fYsubE _ (Hx _ YinX)). Qed.

(* q2.5 *)
Theorem union_postpointsfixes :
	forall f X, croissanteF f -> Famille_Ewd X -> (forall Y, Y inE X -> PostPointFixe f Y)
	 -> PostPointFixe f (Union_generic X id_PE).
Proof.
	intros f X fc Xwd HX; split.
	unfold Union_generic, Subset, id_PE.
	intros x [Y [YinX xinY]]; specialize (HX Y YinX) as [YsubE YsubfY].
	exact (YsubE _ xinY).
	intros x [Y [YinX xinY]]; specialize (HX Y YinX) as [YsubE YsubfY].
	apply (fc _ _ (UnionG_sub _ (fun x => x) _ YinX) (UnionG_wd X (fun x => x) (fun Y YinX => Xwd _ YinX))),
	      YsubfY.
	unfold id_PE in xinY; exact xinY.
Qed.

Definition nu f := Union_generic (fun Y => PostPointFixe f Y) id_PE.
Definition nuf_postpf f (fc : croissanteF f) : PostPointFixe f (nu f) :=
	union_postpointsfixes
		f
		(fun Y => PostPointFixe f Y)
		fc
		(fun Y Yppf => let (YinE, HfY) := Yppf in YinE)
		(fun Y Yppf => Yppf).

(* q2.6.i *)
Theorem nuf_prepf : forall f, PE_wd f -> croissanteF f -> PrePointFixe f (nu f).
Proof.
	intros f fwd fc.
	assert (nufwd : nu f subE E) by (apply UnionG_wd; intros Y [YinE _]; exact YinE).
	split.
	exact nufwd.
	intros x xinfnu.
	assert (rin : (fun y => x = y) subE E) by (intros y yeq; rewrite <-yeq; exact (fwd _ nufwd _ xinfnu)).
	apply (in_UnionG (fun Y => PostPointFixe f Y) id_PE _ _ (in_union_r (nu f) _ _ (eq_refl _))).
	unfold InE, PostPointFixe; split.
	exact (sub_union_sub _ _ _ nufwd rin).
	intros y [yinnu|yeqx].
	apply (fc (nu f) (nu f unionE (fun y => x = y)) (fun y => in_union_l _ _ _) (sub_union_sub _ _ _ nufwd rin)).
	apply (nuf_postpf _ fc); exact yinnu.
	rewrite <-yeqx.
	exact (fc (nu f) (nu f unionE (fun y => x = y)) (fun y => in_union_l _ _ _) (sub_union_sub _ _ _ nufwd rin)
		_ xinfnu).
Qed.

(* q2.6.ii *)
Theorem nu_pf : forall f, PE_wd f -> croissanteF f -> PointFixe f (nu f).
Proof.
	intros f fwd fc; assert (nufwd : nu f subE E) by (apply UnionG_wd; intros Y [YinE _]; exact YinE); split.
	exact nufwd.
	intros x; split.
	exact (proj2 (nuf_postpf f fc) x).
	exact (proj2 (nuf_prepf f fwd fc) x).
Qed.
Theorem nu_biggest_pf : forall f, PE_wd f -> croissanteF f -> forall X, PointFixe f X -> X subE nu f.
Proof.
	intros f fwd fc X [XsubE XeqfX].
	apply (UnionG_sub _ id_PE); unfold InE; split.
	exact XsubE.
	intros x xinX; specialize (XeqfX x) as [H _]; exact (H xinX).
Qed.

(* q2.7 *)
Theorem inter_prepointsfixes :
	forall f X, croissanteF f -> Famille_Ewd X -> (exists Y, Y inE X) -> (forall Y, Y inE X -> PrePointFixe f Y)
	 -> PrePointFixe f (Inter_generic X id_PE).
Proof.
	intros f X fc Xwd [Y YinX] HX; split.
	unfold Inter_generic, Subset, id_PE.
	intros x Hx.
	specialize (HX Y YinX) as [YsubE YsubfY].
	exact (YsubE _ (Hx Y YinX)).
	intros x Hx Z ZinX.
	specialize (HX Z ZinX) as [ZsubE fZsubZ].
	unfold Inter_generic, id_PE in *.
	apply fZsubZ; exact (fc _ Z (InterG_sub _ (fun x => x) _ ZinX) ZsubE _ Hx).
Qed.
Definition mu f := Inter_generic (fun Y => PrePointFixe f Y) id_PE.
Definition muf_prepf f (fwd : PE_wd f) (fc : croissanteF f) : PrePointFixe f (mu f) :=
	inter_prepointsfixes
		f
		(fun Y => PrePointFixe f Y)
		fc
		(fun Y Yppf => let (YinE, HfY) := Yppf in YinE)
		(all_prepf _ fwd)
		(fun Y Yppf => Yppf).
Theorem muf_postpf : forall f, PE_wd f -> croissanteF f -> PostPointFixe f (mu f).
Proof.
	intros f fwd fc.
	assert (mufwd : mu f subE E) by exact (proj1 (muf_prepf _ fwd fc)).
	split.
	exact mufwd.
	intros x xinmu.
	assert (rin : (fun y => x = y) subE E) by (intros y yeq; rewrite <-yeq; exact (mufwd _ xinmu)).
	apply (InterG_in _ _ _ xinmu (f (mu f))).
	unfold InE, PrePointFixe; split.
	exact (fwd _ mufwd).
	refine (fc _ _ _ mufwd).
	exact (proj2 (muf_prepf _ fwd fc)).
Qed.
Theorem mu_pf : forall f, PE_wd f -> croissanteF f -> PointFixe f (mu f).
Proof.
	intros f fwd fc; assert (mufwd : mu f subE E) by exact (proj1 (muf_prepf _ fwd fc)); split.
	exact mufwd.
	intros x; split.
	exact (proj2 (muf_postpf f fwd fc) x).
	exact (proj2 (muf_prepf f fwd fc) x).
Qed.
Theorem mu_smallest_pf : forall f, PE_wd f -> croissanteF f -> forall X, PointFixe f X -> mu f subE X.
Proof.
	intros f fwd fc X [XsubE XeqfX].
	apply (InterG_sub _ id_PE); unfold InE; split.
	exact XsubE.
	intros x xinX; specialize (XeqfX x) as [_ H]; exact (H xinX).
Qed.

(* q2.8.i *)
Theorem iter_decreasing : forall f, PE_wd f -> croissanteF f -> Suite_decroissante (fun i => (f ^ i) E).
Proof.
	intros f fwd fc i; induction i as [|i IHi].
	exact (fwd _ (sub_refl _)).
	apply fc; unfold Iteree in IHi; fold Iteree in *; unfold comp in *.
	exact IHi.
	exact (Iteree_wd _ fwd _ _ (sub_refl _)).
Qed.

(* q2.8.ii *)
Theorem cocontinue_nuf : forall f, PE_wd f -> cocontinueF f -> nu f eqE Inter_N (fun i => (f ^ i) E).
Proof.
	intros f fwd fcc x; split.
	intros [Y [[YsubE YsubfY] xinY]] i.
	unfold id_PE in xinY.
	remember E as E0 eqn:eqE0;
	assert (E0wd : E0 subE E) by (subst E0; exact (sub_refl _));
	clear eqE0; generalize dependent E0; generalize dependent Y; generalize dependent x; induction i as [|i IHi];
	  intros x Y YsubfY xinY E0 YsubE0 E0wd.
	exact (YsubE0 _ xinY).
	specialize (IHi x Y YsubfY xinY (f E0)
		(fun y yin => (cocontinue_croissante _ fcc Y E0 YsubE0 E0wd _ (YsubfY _ yin))) (fwd _ E0wd)).
	rewrite <-Iteree_comm in IHi.
	exact IHi.
	specialize (nu_biggest_pf f fwd (cocontinue_croissante _ fcc) (Inter_N (fun i => (f ^ i) E))) as tmp.
	intros Hx; refine (tmp _ _ Hx); split.
	intros y yinI; specialize (yinI O); unfold Iteree, id_PE in yinI; exact yinI.
	rewrite (fcc _ (sub_refl _) (iter_decreasing _ fwd (cocontinue_croissante _ fcc))).
	intros y; split.
	intros yin k; exact (yin (S k)).
	intros yin [|k]; [unfold Iteree, id_PE; exact (fwd E (sub_refl _) _ (yin 0))|exact (yin k)].
Qed.

Definition SubsetF f g := forall X, X subE E -> f X subE g X.
Infix "subf" := SubsetF (at level 71, no associativity).

Definition extensiveF f := id_PE subf f.
Definition saturanteF f := comp f f subf f.
Definition clotureF f := croissanteF f /\ extensiveF f /\ saturanteF f.

Definition omegaF f := Union_Nf (fun i => (f unionF id_PE) ^ i).

(* q2.9.i *)
Theorem fomega_ext : forall f, extensiveF (omegaF f).
Proof.
	intros f X XsE x xinX; exists 0; unfold Iteree; exact xinX.
Qed.
Theorem fomega_contientf : forall f, f subf (omegaF f).
Proof.
	intros f X XsE x xinfX; exists 1; unfold Iteree, comp, id_PE, UnionPE, Union, InE; left; exact xinfX.
Qed.

(* q2.9.ii *)
Lemma strong_induction :
	forall (P : nat -> Prop), P 0 -> (forall n0, (forall n, n <= n0 -> P n) -> P (S n0)) -> forall n, P n.
Proof.
	intros P I IH.
	assert (H : forall n0 n, n <= n0 -> P n).
	{ intros n0; induction n0 as [|n0 IHn0]; intros n nleSn0.
	  inversion nleSn0 as [|H]; exact I.
	  inversion nleSn0 as [H|H].
	  exact (IH _ IHn0).
	  exact (IHn0 _ H0). }
	intros n; exact (H _ _ (le_n _)).
Qed.
Lemma omegaF_wd : forall f, PE_wd f -> PE_wd (omegaF f).
Proof.
	intros f fwd; apply Union_Nf_wd; intros n; apply Iteree_wd, UnionPE_wd; [exact fwd|exact id_wd].
Qed.
Theorem fomega_cloture : forall f, PE_wd f -> continueF f -> clotureF (omegaF f).
Proof.
	intros f fwd fco; split; [|split; [exact (fomega_ext _)|]].
	intros X Y XsY YsE x [n xinfidX]; unfold omegaF, Union_Nf, Union_N; hnf; exists n;
	  generalize dependent x; generalize dependent Y; generalize dependent X; induction n as [|n IHn];
	  intros X Y XsY YsE x xinfidX.
	unfold Iteree in *; exact (XsY _ xinfidX).
	rewrite Iteree_comm in xinfidX; rewrite Iteree_comm.
	exact (IHn
		_
		_
		(union_croissante _ _ (continue_croissante _ fco) id_croissante _ _ XsY YsE)
		(UnionPE_wd _ _ fwd id_wd _ YsE)
		_
		xinfidX).
	
	unfold saturanteF, omegaF, SubsetF, comp, Union_Nf.
	intros X XsE x [n xin].
	rewrite (iteree_continue _ n
		(UnionPE_wd _ _ fwd id_wd)
		(union_continue _ _ fco id_continue)
		(fun i => ((f unionF id_PE) ^ i) X)
		(fun i => Iteree_wd _ (UnionPE_wd _ _ fwd id_wd) i _ XsE)
		(fun i x xin => or_intror _ xin)) in xin.
	destruct xin as [k xin].
	exists (n + k).
	rewrite (Iteree_sum _ (UnionPE_wd _ _ fwd id_wd)); exact xin.
Qed.

(* q2.10 *)
Theorem continue_fwX_prepf : forall f, PE_wd f -> continueF f -> forall X, X subE E -> PrePointFixe f (omegaF f X).
Proof.
	intros f fwd fco X XsE; split; [exact (omegaF_wd _ fwd _ XsE)|].
	intros x xin.
	exact (proj2 (proj2 (fomega_cloture _ fwd fco)) _ XsE _ (fomega_contientf _ _ (omegaF_wd _ fwd _ XsE) _ xin)).
Qed.
Theorem continue_fwX_contientX : forall f, forall X, X subE E -> X subE (omegaF f X).
Proof.
	intros f X XsE x xinX; exists 0; exact xinX.
Qed.
Theorem continue_fwX_plus_petit : forall f, PE_wd f -> continueF f -> forall X, X subE E ->
	forall Y, PrePointFixe f Y -> X subE Y -> (omegaF f X) subE Y.
Proof.
	intros f fwd fco X XsE Y [YsE Yppf] XsY x [n xin].
	generalize dependent x; generalize dependent X; induction n as [|n IHn]; intros X XsE XsY x xin.
	exact (XsY _ xin).
	rewrite Iteree_comm in xin.
	exact (IHn
		((f unionF id_PE) X)
		((UnionPE_wd _ _ fwd id_wd) _ XsE)
		(sub_trans _ _ _
			(continue_croissante _ (union_continue _ _ fco id_continue) _ _ XsY YsE)
			(sub_union_sub _ _ _ Yppf (sub_refl _)))
		_ xin).
Qed.

(* q2.11 *)
Theorem omega_smallest : forall f, PE_wd f -> continueF f -> forall g, PE_wd g -> clotureF g -> f subf g ->
	(omegaF f) subf g.
Proof.
	intros f fwd fco g gwd [gcr [gex gsa]] fsg X XsE.
	exact (continue_fwX_plus_petit
		_ fwd fco
		_ XsE _ (conj (gwd _ XsE) (sub_trans _ _ _ (fsg _ (gwd _ XsE)) (gsa _ XsE))) (gex _ XsE)).
Qed.

End Partie2.
Section Relations.
Context {U : Type} (I : U -> Prop).
Notation "'Pair'" := (prod U U) : type_scope.
Definition PairE := fun (p : Pair) => let (l, r) := p in (l inE I) /\ (r inE I).
Definition Relation := Ensemble Pair.
Definition Rel_wd : Relation -> Prop := fun R => Subset R PairE.
Notation "'FunRel'" := (Relation -> Relation).
Definition FunRel_wd := PE_wd PairE.
Notation "p 'inR' R" := (p inE R) (at level 71, no associativity).

Definition idR : Relation := fun p => let (l, r) := p in l = r.
Definition compRel : Relation -> Relation -> Relation := fun R S p => let (i, k) := p in
	exists j : U, (j inE I) /\ ((i, j) inR R) /\ ((j, k) inR S).
Definition transRel : Relation -> Relation := fun R p => let (i, j) := p in (j, i) inR R.

Definition SubsetR : Relation -> Relation -> Prop := Subset. Hint Unfold SubsetR : core.
Notation "R 'subR' S" := (SubsetR R S) (at level 71, no associativity).

(* q2.12 *)
Definition reflR (R : Relation) := idR subR R.
Definition symR (R : Relation) := (transRel R) subR R.
Definition transR (R : Relation) := (compRel R R) subR R.

Definition rel_r : Relation -> Relation := fun _ => idR.
Definition rel_s : Relation -> Relation := fun R => transRel R.
Definition rel_t : Relation -> Relation := fun R => compRel R R.

(* q2.13 *)
Lemma rel_r_prepf_cara : forall R : Relation, (PrePointFixe PairE rel_r R <-> (Rel_wd R /\ reflR R)).
Proof.
	unfold PrePointFixe, rel_r, Rel_wd, reflR, SubsetR; intros R; reflexivity.
Qed.
Lemma rel_s_prepf_cara : forall R : Relation, (PrePointFixe PairE rel_s R <-> (Rel_wd R /\ symR R)).
Proof.
	unfold PrePointFixe, rel_s, Rel_wd, symR, SubsetR; intros R; reflexivity.
Qed.
Lemma rel_t_prepf_cara : forall R : Relation, (PrePointFixe PairE rel_t R <-> (Rel_wd R /\ transR R)).
Proof.
	unfold PrePointFixe, rel_s, Rel_wd, transR, SubsetR; intros R; reflexivity.
Qed.

(* q2.14 *)
Theorem rel_r_continue : continueF PairE rel_r.
Proof.
	intros Xi Xiwd Xicr; apply set_extensionality; intros [xl xr]; unfold rel_r, Union_N, idR, InE; split.
	intros H; exists 0; exact H.
	intros [_ H]; exact H.
Qed.
Theorem rel_s_continue : continueF PairE rel_s.
Proof.
	intros Xi Xiwd Xicr; apply set_extensionality; intros [xl xr]; unfold rel_s, Union_N, transRel, InE; reflexivity.
Qed.
Theorem rel_t_continue : continueF PairE rel_t.
Proof.
	intros Xi Xiwd Xicr; apply set_extensionality; intros [xl xr]; unfold rel_t, Union_N, compRel, InE; split.
	intros [j [jin [[n1 H1] [n2 H2]]]].
	specialize (PeanoNat.Nat.le_ge_cases n1 n2) as [n1len2|n2len1].
	exists n2, j; split; [exact jin|split; [|exact H2]].
	exact (croissante_le _ Xicr _ _ n1len2 _ H1).
	exists n1, j; split; [exact jin|split; [exact H1|]].
	exact (croissante_le _ Xicr _ _ n2len1 _ H2).
	
	intros [n [j [jin [H1 H2]]]]; exists j; split; [exact jin|split; exists n; [exact H1|exact H2]].
Qed.
End Relations.
Arguments Relation U : clear implicits.

(* q2.3 *)
Theorem croissante_non_C0 : let N := fun n => True in
	exists f, @PE_wd nat N f /\ croissanteF N f /\ ~ continueF N f.
Proof.
	exists (fun E x => E eqE (fun _ : nat => True)); split; [|split];
	  unfold PE_wd, croissanteF, continueF, Subset, InE.
	intros x xsub y yin; exact I.
	intros X Y XsY _ _ Xx; split; intros _; [exact I|apply XsY, Xx; exact I].
	apply ex_not_not_all.
	exists (fun n0 n => n <= n0).
	intros H.
	assert (all_wd : forall E, Suite_Ewd (fun _ : nat => True) (V:=nat) E) by (intros ? ? ? ?; exact I).
	assert (sc : Suite_croissante (fun n0 n => n <= n0)) by (intros n0 n nlen0; exact (le_S _ _ nlen0)).
	specialize (H (all_wd _) sc); clear all_wd sc.
	assert (H' : (fun _ : nat => forall x0 : nat, Union_N (fun n0 n : nat => n <= n0) x0 <-> True) eqE
		Union_N (fun n _ : nat => forall x0 : nat, (fun n0 n1 : nat => n1 <= n0) n x0 <-> True))
	by (rewrite H; intros x; split; intros P; exact P); clear H; rename H' into H.
	specialize (H 0) as [H _]; unfold Union_N, InE in H.
	assert (Hl : forall n0 : nat, (exists n : nat, n0 <= n) <-> True)
	by (split; intros _; [exact I|exists n0; exact (le_n _)]).
	specialize (H Hl) as [n Hn]; clear Hl.
	specialize (Hn (S n)) as [_ f].
	specialize (f I).
	exact (PeanoNat.Nat.nle_succ_diag_l _ f).
Qed.
Theorem croissante_non_coC0 : let N := fun n => True in
	exists f, @PE_wd nat N f /\ croissanteF N f /\ ~ cocontinueF N f.
Proof.
	exists (fun E x => exists y, y inE E); split; [|split];
	  unfold PE_wd, croissanteF, cocontinueF, Subset, InE.
	intros x xsub y yin; exact I.
	intros X Y XsY _ _ [y Xy]; exists y; exact (XsY _ Xy).
	apply ex_not_not_all; exists (fun n0 n => n0 <= n).
	intros H.
	assert (sd : Suite_decroissante (fun n0 n => n0 <= n)) by (intros n0 n nlen0; exact (Le.le_Sn_le _ _ nlen0)).
	specialize (H (fun x Olex => I) sd); clear sd.
	assert (H' : (fun _ : nat => exists y : nat, Inter_N (fun n0 n : nat => n0 <= n) y) eqE
		Inter_N (fun n _ : nat => exists y : nat, n <= y))
	by (rewrite H; intros x; split; intros P; exact P); clear H; rename H' into H.
	specialize (H 0) as [_ H]; unfold Inter_N, InE in H.
	assert (Hl : forall n : nat, (exists y : nat, n <= y)) by (intros n; exists n; exact (le_n _)).
	specialize (H Hl) as [n Hn]; clear Hl.
	exact (PeanoNat.Nat.nle_succ_diag_l _ (Hn (S n))).
Qed.

Section Partie3.
Context (aut : Automate).
Let X := aut.(aut_X). Hint Unfold X : core.
Let E : Ensemble X.(ens_E) := fun v => v inL X. Hint Unfold E : core.
Notation "'forallA' a , P" := (forall a, a inL A -> P) (at level 200, a binder).
Notation "'forallA*' u , P" := (forall u, InAstar u -> P) (at level 200, u binder).

Definition rel_p (R : Relation X.(ens_E)) : Relation X.(ens_E) := fun p => let (x, y) := p in
	((x inE E) /\ (y inE E)) /\
	(aut.(aut_o) x = aut.(aut_o) y) /\
	(forallA a, ((aut.(aut_delta) x a, aut.(aut_delta) y a) inE R)).

Lemma rel_p_wd : PE_wd (PairE E) rel_p.
Proof.
	exact (fun Y YsEE p => let (x, y) as v return (v inE rel_p Y -> v inE PairE E) := p in
		fun (Hxy : (x, y) inE rel_p Y) => let (l, r) := Hxy in l).
	(* intros Y YsEE [x y] [xyinY _]; exact xyinY. *)
Qed.

Lemma cara_sub_p : forall (R S : Relation X.(ens_E)),
	Subset S (rel_p R) <->
	((Rel_wd E S) /\
	 (forall x y, x inE E -> y inE E -> (x, y) inE S ->
	  (aut.(aut_o) x = aut.(aut_o) y) /\
	  (forallA a, ((aut.(aut_delta) x a, aut.(aut_delta) y a) inE R)))).
Proof.
	intros R S; split.
	intros SsubpR; split.
	intros [x y] xinS; unfold InE; exact (proj1 (SsubpR _ xinS)).
	intros x y xinE yinE xyinS.
	exact (proj2 (SsubpR _ xyinS)).
	intros [SsubEE H] [x y] xyinS; split; [split|];
	specialize (SsubEE _ xyinS) as [xinE yinE].
	exact xinE. exact yinE.
	exact (H _ _ xinE yinE xyinS).
Qed.
Definition bisimu R := PostPointFixe (PairE E) rel_p R.

(* q3.2 *)
Theorem rel_p_croissante : croissanteF (PairE E) rel_p.
Proof.
	intros X0 Y X0sY Ywd [x y] [[xinE yinE] [oxeqoy dxeqdy]]; split; split.
	exact xinE. exact yinE. exact oxeqoy.
	intros a ain; exact (X0sY _ (dxeqdy _ ain)).
Qed.

Definition curry {A B C} (f : A -> B -> C) (xy : A * B) := let (x, y) := xy in f x y.

(* q3.3.i *)
Theorem equiv_bisimu : bisimu (curry (Equiv aut)).
Proof.
	unfold curry, bisimu, PostPointFixe, Subset; split; intros [x y] [xyin Hxy].
	exact xyin.
	refine (proj2 (iff_and (cara_sub_p
		(fun p => let (x, y) := p in (Equiv aut x y))
		(fun p => let (x, y) := p in (Equiv aut x y))))
		_
		(x, y) (conj xyin Hxy)).
	split.
	clear x y xyin Hxy; intros [x y] [xyin _]; exact xyin.
	clear x y xyin Hxy; intros x y xin yin [xyinX Hxy]; split.
	specialize (Hxy [] I); unfold deltastar in Hxy; exact Hxy.
	intros a ain; split.
	specialize (Hxy [a] (conj ain I)); unfold PairE, E, InE; split; refine (aut.(aut_delta_wd) _ _ _ ain);
		[exact xin|exact yin].
	intros u uin; specialize (Hxy (a :: u) (conj ain uin)); unfold deltastar in Hxy; fold deltastar in Hxy;
		exact Hxy.
Qed.

(* q3.3.ii *)
Theorem bisimu_in_eq : forall R, bisimu R -> Subset R (curry (Equiv aut)).
Proof.
	intros R [RsEE RspR] [x y] xyinR; unfold curry, InE.
	apply cara_sub_p in RspR; destruct RspR as [_ HR].
	specialize (RsEE _ xyinR) as [xin yin]; split.
	exact (conj xin yin).
	intros u uin.
	generalize dependent y; generalize dependent x; induction u as [|a u IHu]; intros x xin y xyinR yin.
	specialize (HR _ _ xin yin xyinR) as [eqo _]; exact eqo.
	unfold deltastar; fold deltastar.
	destruct uin as [ain uin]; specialize (HR _ _ xin yin xyinR) as [_ eqd].
	exact (IHu
		uin
		_ (aut.(aut_delta_wd) _ _ xin ain)
		_ (eqd _ ain) (aut.(aut_delta_wd) _ _ yin ain)).
Qed.

(* q3.3.iii *)
Theorem nup_eq_Equiv : (nu (PairE E) rel_p) = (curry (Equiv aut)).
Proof.
	apply set_extensionality, sub_antisym.
	apply bisimu_in_eq; unfold bisimu; exact (nuf_postpf _ _ rel_p_croissante).
	unfold nu;
	refine (UnionG_sub (fun Y => PostPointFixe (PairE E) rel_p Y) id_PE (curry (Equiv aut)) _).
	unfold InE.
	exact equiv_bisimu.
Qed.

End Partie3.

Context
	(aut : Automate)
	(eqbX : aut.(aut_X).(ens_E) -> aut.(aut_X).(ens_E) -> bool)
	(eqbX_spec : forall a b, Bool.reflect (a = b) (eqbX a b)).
Definition state_pair : Type := aut.(aut_X).(ens_E) * aut.(aut_X).(ens_E).
Definition in_state_pair '(l, r) := l inL aut.(aut_X) /\ r inL aut.(aut_X).
Fixpoint Inb {T1 T2} (eqb : T1 -> T2 -> bool) (x : T1) (l : list T2)
	:= match l with [] => false | hd :: tl => orb (eqb x hd) (Inb eqb x tl) end.
Lemma In_spec T (eqb : T -> T -> bool)
 : (forall a b, Bool.reflect (a = b) (eqb a b)) -> forall a l, Bool.reflect (In a l) (Inb eqb a l).
Proof.
	intros Hrefl a l; induction l as [|v l IHl].
	simpl; exact (Bool.ReflectF _ (fun f => f)).
	simpl; destruct (Hrefl a v) as [eq|ne].
	symmetry in eq; exact (Bool.ReflectT _ (or_introl eq)).
	destruct IHl as [ain|ani]; unfold orb.
	exact (Bool.ReflectT _ (or_intror ain)).
	apply Bool.ReflectF; intros [veqa|ain]; [symmetry in veqa; exact (ne veqa)|exact (ani ain)].
Qed.
Definition eqbPair := fun '(a, b) '(c, d) => andb (eqbX a c) (eqbX b d).
Lemma eqbPair_spec : forall a b, Bool.reflect (a = b) (eqbPair a b).
Proof.
	intros [a b] [c d]; simpl.
	destruct (eqbX_spec a c) as [eq1|ne].
	destruct (eqbX_spec b d) as [eq2|ne].
	subst; exact (Bool.ReflectT _ (eq_refl _)).
	apply Bool.ReflectF; intros H; injection H as _ beqd; exact (ne beqd).
	apply Bool.ReflectF; intros H; injection H as aeqc _; exact (ne aeqc).
Qed.
Definition algo1_body (R : list state_pair) (F : list state_pair) :=
	match F with
	| [] => inr true
	| (x, y) :: tl =>
		if Inb eqbPair (x, y) R then inl (R, tl)
		else if xorb (aut.(aut_o) x) (aut.(aut_o) y) then inr false
		else inl ((x, y) :: R,
		          let fix app al l :=
		          	match al with
		          	| [] => l
		          	| a :: tl => (aut.(aut_delta) x a, aut.(aut_delta) y a) :: (app tl l) end in app A.(ens_L) tl)
	end.
Definition I0_statement (R : list state_pair) (F : list state_pair) := Forall in_state_pair R /\ Forall in_state_pair F.
Lemma I0_invar : forall R F R' F', algo1_body R F = inl (R', F') ->
	I0_statement R F -> I0_statement R' F'.
Proof.
	intros R [|[x y] F] R' F' Hstep [I0l I0r]; try solve [inversion Hstep]; unfold algo1_body, I0_statement in *.
	destruct (Inb eqbPair (x, y) R) as [|] eqn:tmp.
	inversion Hstep; subst R' F'; split.
	exact I0l.
	inversion I0r as [|? ? ? P]; exact P.
	destruct (xorb (aut_o aut x) (aut_o aut y)); inversion Hstep; subst R' F'; split.
	inversion I0r as [|? ? P]; exact (Forall_cons _ P I0l).
	inversion I0r as [|tmp01 tmp02 xyin HF tmp04]; subst; destruct xyin as [xin yin].
	remember AL as l eqn:eqAL.
	assert (lsubAL : forall a, In a l -> In a AL) by (subst; intros a ain; exact ain).
	clear - xin yin lsubAL HF; induction l as [|a l IHl].
	exact HF.
	refine (Forall_cons _ _ (IHl (fun x xin => lsubAL x (or_intror _ xin)))).
	unfold in_state_pair; split; apply aut.(aut_delta_wd);
	  ((apply lsubAL; left; exact (eq_refl _)) || assumption).
Qed.
Lemma I0_init : forall x0 y0, x0 inL aut.(aut_X) -> y0 inL aut.(aut_X) ->
	I0_statement [] [(x0, y0)].
Proof.
	intros x0 y0 x0in y0in; split.
	constructor.
	constructor.
	split.
	exact x0in.
	exact y0in.
	constructor.
Qed.
Definition I1_statement (R : list state_pair) (F : list state_pair) x0 y0 := In (x0, y0) (R ++ F).
Lemma I1_invar : forall R F R' F' x0 y0, algo1_body R F = inl (R', F') ->
	I1_statement R F x0 y0 -> I1_statement R' F' x0 y0.
Proof.
	intros R [|[x y] F] R' F' x0 y0 Hstep I1; inversion Hstep.
	simpl in *.
	destruct (Inb eqbPair (x, y) R) as [|] eqn:tmp.
	inversion Hstep; subst; apply in_or_app.
	apply in_app_or in I1; destruct I1 as [l|[eq|r]].
	left; exact l.
	left; rewrite <-eq; rewrite (Bool.reflect_iff _ _ (In_spec _ _ eqbPair_spec _ _)); exact tmp.
	right; exact r.
	
	destruct (xorb (aut_o aut x) (aut_o aut y)); inversion Hstep; subst.
	inversion Hstep; subst; apply in_or_app.
	apply in_app_or in I1; destruct I1 as [l|[eq|r]].
	left; right; exact l.
	rewrite <-eq in *; clear x0 y0 eq; left; left; exact (eq_refl _).
	right; remember AL as l eqn:tmp2; clear - r.
	induction l as [|a l IHl].
	exact r.
	right; exact IHl.
Qed.
Lemma I1_init : forall x0 y0, x0 inL aut.(aut_X) -> y0 inL aut.(aut_X) ->
	I1_statement [] [(x0, y0)] x0 y0.
Proof.
	intros x0 y0 x0in y0in; unfold I1_statement, app, In; left; exact (eq_refl _).
Qed.
Definition I2_statement (R : list state_pair) (F : list state_pair) :=
	Subset (fun x => In x R) (rel_p aut (fun v => In v (R ++ F))).
Lemma I2_invar : forall R F R' F', algo1_body R F = inl (R', F') -> I0_statement R F ->
	I2_statement R F -> I2_statement R' F'.
Proof.
	intros R [|[x y] F] R' F' Hstep [I0l I0r]; unfold algo1_body in Hstep; [inversion Hstep|];
	  unfold I2_statement; intros H; rewrite (cara_sub_p aut); rewrite (cara_sub_p aut) in H; split;
	  destruct H as [Hl Hr].
	1,2: destruct (Inb eqbPair (x, y) R) as [|] eqn:tmp.
	1,3: inversion Hstep; subst R' F'; clear Hstep.
	exact Hl.
	intros x0 y0 x0in y0in x0y0inR; split;
	specialize (Hr x0 y0 x0in y0in x0y0inR) as [Hrl Hrr].
	exact Hrl.
	intros a ain; unfold InE; specialize (Hrr a ain); unfold InE in Hrr.
	destruct (in_elt_inv _ _ _ _ Hrr) as [eq|Hrrr].
	rewrite eq in *; apply in_or_app; left; rewrite (Bool.reflect_iff _ _ (In_spec _ _ eqbPair_spec _ _)); exact tmp.
	exact Hrrr.
	
	1,2: destruct (xorb (aut_o aut x) (aut_o aut y)) eqn:tmp2; inversion Hstep; subst; clear Hstep.
	1,2: inversion I0r as [|a b xypair HF e]; subst.
	intros p [eq|pin]; [subst; exact xypair|rewrite Forall_forall in I0l; exact (I0l _ pin)].
	intros x0 y0 x0in y0in [eq|x0y0inR].
	injection eq as eq1 eq2; subst x0 y0; split.
	clear - tmp2; destruct (aut.(aut_o) x); destruct (aut.(aut_o) y); unfold xorb in tmp2; try exact tmp2.
	exact (eq_refl _).
	symmetry; exact tmp2.
	intros a ain; unfold InE; apply in_or_app; right.
	clear - ain eqbX_spec; remember AL as l eqn:eq; clear eq; induction l as [|v l IHl].
	destruct ain as [].
	destruct ain as [eq|ain].
	subst; left; exact (eq_refl _).
	right; apply IHl; exact ain.
	specialize (Hr _ _ x0in y0in x0y0inR) as [Hrl Hrr]; split; [exact Hrl|].
	intros a ain.
	apply in_or_app; specialize (Hrr a ain); apply in_app_or in Hrr; destruct Hrr as [Hrrl|[eq|Hrrr]].
	left; right; exact Hrrl.
	left; left; exact eq.
	right; clear - Hrrr; induction AL as [|v l IHl].
	exact Hrrr.
	right; exact IHl.
Qed.
Lemma I2_init : forall x0 y0, x0 inL aut.(aut_X) -> y0 inL aut.(aut_X) ->
	I2_statement [] [(x0, y0)].
Proof.
	intros x0 y0 x0in y0in [x y] [].
Qed.
Definition I3_statement (R : list state_pair) (F : list state_pair) :=
	Forall (fun '(x, y) => Equiv aut x y) (R ++ F).
Lemma I3_invar : forall R F R' F', algo1_body R F = inl (R', F') -> I0_statement R F ->
	I3_statement R F <-> I3_statement R' F'.
Proof.
	intros R [|[x y] F] R' F' Hstep [I0l I0r]; unfold algo1_body in Hstep; [inversion Hstep|];
	  unfold I3_statement; split; intros H; rewrite Forall_app in H; destruct H as [HR Hr].
	inversion Hr as [|a b Hxy HF e]; subst.
	destruct (Inb eqbPair (x, y) R) as [|] eqn:tmp.
	inversion Hstep; subst R' F'; clear Hstep.
	rewrite Forall_app; split; [exact HR|exact HF].
	destruct (xorb (aut_o aut x) (aut_o aut y)) eqn:tmp2; inversion Hstep; subst; clear Hstep.
	clear - Hxy HR HF; remember AL as l eqn:eq;
	assert (lsubAL : forall a, In a l -> In a AL) by (subst; intros a ain; exact ain);
	 clear eq; induction l as [|v l IHl].
	rewrite Forall_app; split; [apply Forall_cons; [exact Hxy|exact HR]|exact HF].
	specialize (IHl (fun a ain => lsubAL a (or_intror ain))).
	rewrite Forall_app; rewrite Forall_app in IHl; split; destruct IHl as [IHll IHlr].
	exact IHll.
	constructor; [split; [split; destruct Hxy as [[Hx Hy] _]; apply aut.(aut_delta_wd); try assumption|]|exact IHlr].
	1,2: apply lsubAL; exact (or_introl (eq_refl _)).
	destruct Hxy as [_ Hxy]; intros u uin; apply (Hxy (v :: u)); exact (conj (lsubAL _ (or_introl (eq_refl _))) uin).
	destruct (Inb eqbPair (x, y) R) as [|] eqn:tmp.
	inversion Hstep; subst R' F'; clear Hstep.
	rewrite Forall_app; split; [exact HR|constructor; [rewrite Forall_forall in HR; apply (HR (x, y))|exact Hr]].
	rewrite (Bool.reflect_iff _ _ (In_spec _ _ eqbPair_spec _ _)); exact tmp.
	destruct (xorb (aut_o aut x) (aut_o aut y)) eqn:tmp2; inversion Hstep; subst; clear Hstep.
	rewrite Forall_app; rename HR into tmp3; inversion tmp3 as [|a b Hxy HR e]; subst; clear tmp3; split.
	exact HR.
	constructor.
	exact Hxy.
	rewrite Forall_forall in Hr; rewrite Forall_forall; intros p pin; apply Hr.
	clear - pin; induction AL as [|v l IHl].
	exact pin.
	right; exact IHl.
Qed.

End General.

Section Exemple.
Notation "x 'inL' E" := (In x E.(ens_L)) (at level 71, no associativity).
Notation "x 'inE' E" := (InE E x) (at level 71, no associativity).
Notation "E 'eqE' F" := (forall x, x inE E <-> x inE F) (at level 71, no associativity).
Require Import String. Require Import Ascii.
Definition A1 := mkEns ascii ["a"; "b"]%char
		(conj
			(fun f : In "a"%char ["b"%char] =>
				match f with
				| or_introl x => eq_ind "b"%char
							(fun a : ascii =>
							 let (b, _, _, _, _, _, _, _) := a in if b then False else True) I "a"%char x
				| or_intror x => x end)
			(conj (fun f : False => f) I)).

Definition X1 := mkEns nat [1; 2]
	(conj
		(fun f : In 1 [2] => match f with
			| or_introl x => eq_ind 2 (fun e => match e with 2 => True | _ => False end) I 1 x
			| or_intror x => x end)
		(conj (fun f : False => f) I)).
Definition o1 := fun n : nat => n = 2.
Definition delta1 := fun (n : nat) (a : ascii) =>
	if (a =? "a")%char then match n with 1 => 2 | _ => 1 end
	else n.
Lemma delta1_wd : forall x a, x inL X1 -> a inL A1 -> (delta1 x a) inL X1.
Proof.
	intros x a [xeq|[xeq|[]]] [aeq|[aeq|[]]].
	rewrite <-xeq, <-aeq; unfold In, delta1; simpl; right; left; exact (eq_refl _).
	rewrite <-xeq, <-aeq; unfold In, delta1; simpl; left; exact (eq_refl _).
	rewrite <-xeq, <-aeq; unfold In, delta1; simpl; left; exact (eq_refl _).
	rewrite <-xeq, <-aeq; unfold In, delta1; simpl; right; left; exact (eq_refl _).
Qed.
Definition aut1 := mkAuto A1 X1 o1 delta1 delta1_wd.

(* q1.1 *)
Lemma L1_L2_eq : forall x, InAstar A1 x ->
	(x inE Language A1 aut1 1
	 <->
	 x inE (fun w : list ascii =>
		let fix f (l : list ascii) (r : bool) := match l with
			| [] => if r then True else False
			| a :: tl => f tl (if (a =? "a")%char then negb r else r)
		end in f w false)) /\
	(x inE Language A1 aut1 2
	 <->
	 x inE (fun w : list ascii =>
		let fix f (l : list ascii) (r : bool) := match l with
			| [] => if r then True else False
			| a :: tl => f tl (if (a =? "a")%char then negb r else r)
		end in f w true)).
Proof.
	intros x; induction x as [|v x IHx]; [intros _|intros [vin xin]; destruct (IHx xin) as [IHx1 IHx2]]; split; split.
	intros xin; unfold Language, InE, aut1, aut_o, o1, deltastar in xin.
	exact (False_ind _ (eq_ind 1 (fun n => match n with 1 => True | _ => False end) I 2 xin)).
	intros xin; unfold InE in xin; destruct xin as [].
	intros _; unfold InE; exact I.
	intros _; unfold InE, Language, aut_o, aut1, o1, deltastar; exact (eq_refl _).
	1,3: intros H; rewrite (au_in_L_iff _ _ _ _ _ vin) in H; unfold aut_delta, aut1, delta1 in H; fold delta1 aut1 in H.
	1,2: unfold InE.
	1,2: destruct (eqb_spec v "a")%char as [veq|vne].
	1,3: replace (negb false) with true by (exact (eq_refl _)).
	1,4: apply IHx2 in H; unfold InE in H; exact H.
	1,2: apply IHx1 in H; unfold InE in H; exact H.
	1,2: intros H; rewrite (au_in_L_iff _ _ _ _ _ vin); unfold aut_delta, aut1, delta1; fold delta1 aut1.
	1,2: unfold InE in H.
	1,2: destruct (eqb_spec v "a")%char as [veq|vne].
	1,3: replace (negb false) with true by (exact (eq_refl _)).
	1,4: apply IHx2 in H; unfold InE in H; exact H.
	1,2: apply IHx1 in H; unfold InE in H; exact H.
Qed.

End Exemple.
End Epreuve.
