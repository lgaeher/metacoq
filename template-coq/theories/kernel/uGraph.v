Require Import Nat Bool String BinInt List Relations Lia.
Import ListNotations.
Require MSets.MSetWeakList.
Require Import MSetFacts MSetProperties.
From Template Require Import utils config Universes wGraph monad_utils.
Import ConstraintType. Import MonadNotation.
Local Open Scope nat_scope.


Module ConstraintSetFact := WFactsOn UnivConstraintDec ConstraintSet.
Module ConstraintSetProp := WPropertiesOn UnivConstraintDec ConstraintSet.



Inductive gc_level := mLevel (_ : string) | mVar (_ : nat).

Inductive good_constraint :=
(* l <= l' *)
| gc_le : gc_level -> gc_level -> good_constraint
(* l < l' *)
| gc_lt : gc_level -> gc_level -> good_constraint
(* Set < Var n *)
| gc_lt_set : nat -> good_constraint
(* Set = Var n *)
| gc_eq_set : nat -> good_constraint.


Module GoodConstraintDec.
  Definition t : Set := good_constraint.
  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : RelationClasses.Equivalence eq := _.
  Definition gc_level_dec : forall x y : gc_level, {x = y} + {x <> y}.
    decide equality. apply string_dec. apply Peano_dec.eq_nat_dec.
  Defined.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
    unfold eq.
    decide equality. all: try apply gc_level_dec.
    all: apply Peano_dec.eq_nat_dec.
  Defined.
End GoodConstraintDec.
Module GoodConstraintSet := MSets.MSetWeakList.Make GoodConstraintDec.
Module GoodConstraintSetFact := WFactsOn GoodConstraintDec GoodConstraintSet.
Module GoodConstraintSetProp := WPropertiesOn GoodConstraintDec GoodConstraintSet.

Definition GoodConstraintSet_pair x y
  := GoodConstraintSet.add y (GoodConstraintSet.singleton x).

Definition gc_val0 (v : valuation) (l : gc_level) : nat :=
  match l with
  | mLevel s => Pos.to_nat (v.(valuation_mono) s)
  | mVar x => v.(valuation_poly) x
  end.

Definition gc_satisfies0 v (gc : good_constraint) : bool :=
  match gc with
  | gc_le l l' => gc_val0 v l <=? gc_val0 v l'
  | gc_lt l l' => gc_val0 v l <? gc_val0 v l'
  | gc_lt_set l => 0 <? v.(valuation_poly) l
  | gc_eq_set l => 0 =? v.(valuation_poly) l
  end.

Definition gc_satisfies v : GoodConstraintSet.t -> bool :=
  GoodConstraintSet.for_all (gc_satisfies0 v).

Definition gc_consistent ctrs : Prop := exists v, gc_satisfies v ctrs.

Lemma gc_satisfies_pair v gc1 gc2 :
  (gc_satisfies0 v gc1 /\ gc_satisfies0 v gc2) <->
  gc_satisfies v (GoodConstraintSet_pair gc1 gc2).
Proof.
  cbn; destruct (GoodConstraintDec.eq_dec gc2 gc1); cbn;
    rewrite if_true_false.
  now destruct e. symmetry. apply andb_and.
Defined.

(* None -> not satisfiable *)
(* Some empty -> useless *)
(* else: singleton or two elements set (l = l' -> {l<=l', l'<=l}) *)
Definition gc_of_constraint (uc : univ_constraint) : option GoodConstraintSet.t
  := let empty := Some GoodConstraintSet.empty in
     let singleton := fun x => Some (GoodConstraintSet.singleton x) in
     let pair := fun x y => Some (GoodConstraintSet_pair x y) in
     match uc with
     (* Prop _ _ *)
     | (Level.lProp, Le, _) => empty
     | (Level.lProp, Eq, Level.lProp) => empty
     | (Level.lProp, Eq, _) => None
     | (Level.lProp, Lt, Level.lProp) => None
     | (Level.lProp, Lt, _) => empty

     (* Set _ _ *)
     | (Level.lSet, Le, Level.lProp) => None
     | (Level.lSet, Le, _) => empty
     | (Level.lSet, Eq, Level.lProp) => None
     | (Level.lSet, Eq, Level.lSet) => empty
     | (Level.lSet, Eq, Level.Level _) => None
     | (Level.lSet, Eq, Level.Var n) => singleton (gc_eq_set n)
     | (Level.lSet, Lt, Level.lProp) => None
     | (Level.lSet, Lt, Level.lSet) => None
     | (Level.lSet, Lt, Level.Level _) => empty
     | (Level.lSet, Lt, Level.Var n) => singleton (gc_lt_set n)

     (* Level _ _ *)
     | (Level.Level _, Le, Level.lProp) => None
     | (Level.Level _, Le, Level.lSet) => None
     | (Level.Level l, Le, Level.Level l')
       => singleton (gc_le (mLevel l) (mLevel l'))
     | (Level.Level l, Le, Level.Var n) => singleton (gc_le (mLevel l) (mVar n))
     | (Level.Level _, Eq, Level.lProp) => None
     | (Level.Level _, Eq, Level.lSet) => None
     | (Level.Level l, Eq, Level.Level l')
       => pair (gc_le (mLevel l) (mLevel l')) (gc_le (mLevel l') (mLevel l))
     | (Level.Level l, Eq, Level.Var n)
       => pair (gc_le (mLevel l) (mVar n)) (gc_le (mVar n) (mLevel l))
     | (Level.Level _, Lt, Level.lProp) => None
     | (Level.Level _, Lt, Level.lSet) => None
     | (Level.Level l, Lt, Level.Level l')
       => singleton (gc_lt (mLevel l) (mLevel l'))
     | (Level.Level l, Lt, Level.Var n) => singleton (gc_lt (mLevel l) (mVar n))

     (* Var _ _ *)
     | (Level.Var _, Le, Level.lProp) => None
     | (Level.Var n, Le, Level.lSet) => singleton (gc_eq_set n)
     | (Level.Var n, Le, Level.Level l) => singleton (gc_le (mVar n) (mLevel l))
     | (Level.Var n, Le, Level.Var n') => singleton (gc_le (mVar n) (mVar n'))
     | (Level.Var _, Eq, Level.lProp) => None
     | (Level.Var n, Eq, Level.lSet) => singleton (gc_eq_set n)
     | (Level.Var n, Eq, Level.Level l)
       => pair (gc_le (mVar n) (mLevel l)) (gc_le (mLevel l) (mVar n))

     | (Level.Var n, Eq, Level.Var n')
       => pair (gc_le (mVar n) (mVar n')) (gc_le (mVar n') (mVar n))
     | (Level.Var _, Lt, Level.lProp) => None
     | (Level.Var _, Lt, Level.lSet) => None
     | (Level.Var n, Lt, Level.Level l) => singleton (gc_lt (mVar n) (mLevel l))
     | (Level.Var n, Lt, Level.Var n') => singleton (gc_lt (mVar n) (mVar n'))
     end.


Ltac gc_of_constraint_tac :=
  match goal with
  | |- is_true (if _ then true else false) => rewrite if_true_false
  | |- is_true (_ <? _) => apply PeanoNat.Nat.ltb_lt
  | |- is_true (_ <=? _) => apply PeanoNat.Nat.leb_le
  | |- is_true (_ =? _) => apply PeanoNat.Nat.eqb_eq
  | |- is_true (gc_satisfies _ (GoodConstraintSet_pair _ _))
               => apply gc_satisfies_pair; cbn -[Nat.leb Nat.eqb]; split
  | H : is_true (if _ then true else false) |- _ => rewrite if_true_false in H
  | H : is_true (_ <? _) |- _ => apply PeanoNat.Nat.ltb_lt in H
  | H : is_true (_ <=? _) |- _ => apply PeanoNat.Nat.leb_le in H
  | H : is_true (_ =? _) |- _ => apply PeanoNat.Nat.eqb_eq in H
  | H : is_true (gc_satisfies _ (GoodConstraintSet_pair _ _)) |- _
               => apply gc_satisfies_pair in H; cbn -[Nat.leb Nat.eqb] in H;
                 destruct H
  end.

Lemma gc_of_constraint_spec v uc :
  satisfies0 v uc <-> on_Some (gc_satisfies v) (gc_of_constraint uc).
Proof.
  split.
  - destruct 1; destruct l, l'; try constructor; try reflexivity.
    all: cbn -[Nat.leb Nat.eqb GoodConstraintSet_pair] in *.
    all: repeat gc_of_constraint_tac; lia.
  - destruct uc as [[[] []] []]; cbn; inversion 1; constructor.
    all: cbn -[Nat.leb Nat.eqb GoodConstraintSet_pair] in *; try lia.
    all: repeat gc_of_constraint_tac; lia.
Qed.

Definition add_gc_of_constraint uc (S : option GoodConstraintSet.t)
  := S1 <- S ;; S2 <- gc_of_constraint uc ;;
     ret (GoodConstraintSet.union S1 S2).

Definition gc_of_constraints (ctrs : constraints) : option GoodConstraintSet.t
  := ConstraintSet.fold add_gc_of_constraint
                        ctrs (Some GoodConstraintSet.empty).


Lemma gc_of_constraints_spec v ctrs :
  satisfies v ctrs <-> on_Some (gc_satisfies v) (gc_of_constraints ctrs).
Proof.
  unfold gc_satisfies, satisfies, ConstraintSet.For_all, gc_of_constraints.
  set (S := GoodConstraintSet.empty).
  rewrite ConstraintSet.fold_spec.
  etransitivity. eapply iff_forall.
  intro; eapply imp_iff_compat_r. eapply ConstraintSetFact.elements_iff.
  set (l := ConstraintSet.elements ctrs). simpl.
  transitivity ((forall uc, InA eq uc l -> satisfies0 v uc) /\
                (forall gc, GoodConstraintSet.In gc S -> gc_satisfies0 v gc)). {
    intuition. inversion H0. }
  clearbody S; revert S; induction l; intro S.
  - split.
    + intro; constructor. apply GoodConstraintSetFact.for_all_1.
      intros x y []; reflexivity.
      intro; apply H.
    + intros HS. split. intros ux H; inversion H.
      cbn in HS. inversion_clear HS.
      apply GoodConstraintSetFact.for_all_2.
      intros x y []; reflexivity.
      assumption.
  - simpl. split.
    + intros [H1 H2].
      pose proof (proj1 (gc_of_constraint_spec v a)
                        (H1 a (InA_cons_hd _ eq_refl))) as H.
      apply on_Some_spec in H.
      destruct H as [X [HX1 HX2]].
      assert (add_gc_of_constraint a (Some S)
              = Some (GoodConstraintSet.union S X)). {
        cbn. rewrite HX1; reflexivity. }
      rewrite H. apply IHl. split.
      * intros uc H0. apply H1. now apply InA_cons_tl.
      * intros gc H0. apply GoodConstraintSetFact.union_1 in H0.
        induction H0. intuition.
        apply GoodConstraintSetFact.for_all_2 in HX2.
        apply HX2. assumption.
        intros x y []; reflexivity.
    + intros H.
      unfold add_gc_of_constraint in H at 2.
      cbn -[add_gc_of_constraint] in H.
      remember (gc_of_constraint a) as o; destruct o.
      * destruct (proj2 (IHl _) H) as [IH1 IH2]. clear IHl H.
        split. intuition. apply InA_cons in H. induction H.
        subst. apply gc_of_constraint_spec. rewrite <- Heqo.
        constructor. apply GoodConstraintSetFact.for_all_1.
        intros x y []; reflexivity.
        intros gc Hgc. apply IH2.
        now apply GoodConstraintSetFact.union_3.
        firstorder.
        intros gc Hgc. apply IH2.
        now apply GoodConstraintSetFact.union_2.
      * apply False_rect. revert H; clear.
        induction l. inversion 1.
        cbn -[add_gc_of_constraint].
        assert (add_gc_of_constraint a None = None) by reflexivity.
        now rewrite H.
Qed.

(* Lemma gc_of_constraints_spec v ctrs : *)
(*   satisfies v ctrs <-> on_Some (gc_satisfies v) (gc_of_constraints ctrs). *)
(* Proof. *)

Lemma gc_consistent_iff ctrs :
  consistent ctrs <-> on_Some gc_consistent (gc_of_constraints ctrs).
Proof.
  split.
  - intros [v H]. apply gc_of_constraints_spec in H.
    inversion H. constructor. exists v. assumption.
  - intro H; inversion H. destruct H1 as [v H1].
    exists v. apply gc_of_constraints_spec. rewrite <- H0.
    constructor. assumption.
Qed.

Definition gc_leq_universe0 ctrs u u'
  := forall v, gc_satisfies v ctrs -> (val v u <= val v u')%Z.


Lemma gc_leq_universe0_iff ctrs u u' :
  leq_universe0 ctrs u u' <-> match gc_of_constraints ctrs with
                               | Some ctrs => gc_leq_universe0 ctrs u u'
                               | None => True
                               end.
Proof.
  split.
  - intro H. case_eq (gc_of_constraints ctrs); [|trivial].
    intros ctrs' e v Hv. apply H. apply gc_of_constraints_spec.
    rewrite e. constructor. assumption.
  - case_eq (gc_of_constraints ctrs).
    intros ctrs' e H v Hv. apply H.
    apply gc_of_constraints_spec in Hv.
    rewrite e in Hv. inversion_clear Hv. assumption.
    intros e _ v Hv.
    apply gc_of_constraints_spec in Hv.
    rewrite e in Hv. inversion_clear Hv.
Defined.



(* vertices of the graph are levels which are not Prop *)
(* ltv : level to vertice *)
Inductive vertice := lSet | ltv (l : gc_level).

Coercion ltv : gc_level >-> vertice.

Module VerticeDec.
  Definition t : Set := vertice.
  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : RelationClasses.Equivalence eq := _.
  Definition eq_refl : forall x : t, eq x x := @eq_refl _.
  Definition eq_sym : forall x y : t, eq x y -> eq y x := @eq_sym _.
  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z := @eq_trans _.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
    unfold eq. decide equality. apply GoodConstraintDec.gc_level_dec. 
  Defined.
  Definition eqb : t -> t -> bool := fun x y => if eq_dec x y then true else false.
End VerticeDec.


Module Import wGraph := wGraph.WeightedGraph VerticeDec.

Definition init_graph := (VSet.singleton lSet, EdgeSet.empty, lSet).

Lemma init_graph_invariants : invariants init_graph.
Proof.
  repeat split; cbn in *.
  all: try inversion H.
  constructor; reflexivity.
  intros x H. apply VSet.singleton_spec in H.
  rewrite H. apply rt_refl.
Defined.

Definition edge_of_level (l : gc_level) : EdgeSet.elt :=
  match l with
  | mLevel l => (lSet, 1, ltv (mLevel l))
  | mVar n => (lSet, 0, ltv (mVar n))
  end.

Definition EdgeSet_pair x y
  := EdgeSet.add y (EdgeSet.singleton x).
Definition EdgeSet_triple x y z
  := EdgeSet.add z (EdgeSet_pair x y).

Definition edges_of_constraint (gc : good_constraint) : list EdgeSet.elt :=
  match gc with
  | gc_le l l' => [edge_of_level l; edge_of_level l'; (ltv l, 0, ltv l')]
  | gc_lt l l' => [edge_of_level l; edge_of_level l'; (ltv l, 1, ltv l')]
  | gc_lt_set n => [(lSet, 1, ltv (mVar n))]
  | gc_eq_set n => [(ltv (mVar n), 0, lSet); (lSet, 0, ltv (mVar n))]
  end.

Definition add_edges edges := fold_left add_edge edges.

Ltac sets_iff :=
  match goal with
  |  |- (_ /\ _) <-> _
     => eapply and_iff_compat_l; sets_iff
  |  |- (_ /\ _) <-> _
     => eapply and_iff_compat_l; sets_iff
  |  |- (_ \/ _) <-> _
     => eapply or_iff_compat_l; sets_iff
  |  |- (_ \/ _) <-> _
     => eapply or_iff_compat_l; sets_iff
  |  |- VSet.In _ (VSet.add _ _) <-> _
     => etransitivity; [eapply VSet.add_spec|sets_iff]
  |  |- EdgeSet.In _ (EdgeSet.add _ _) <-> _
     => etransitivity; [eapply EdgeSet.add_spec|sets_iff]
  |  |- VSet.In _ (VSet.singleton _) <-> _
     => etransitivity; [eapply VSet.singleton_spec|sets_iff]
  |  |- EdgeSet.In _ (EdgeSet.singleton _) <-> _
     => etransitivity; [eapply EdgeSet.singleton_spec|sets_iff]
  | _ => reflexivity
  end.

Ltac simplify_sets :=
  repeat match goal with
  | |- VSet.In ?A (VSet.add ?B ?C)
    => let X := fresh in
      simple refine (let X : VSet.In A (VSet.add B C) <-> _ := _ in _);
      [|sets_iff|apply (proj2 X); clear X]
  | |- EdgeSet.In ?A (EdgeSet.add ?B ?C)
    => let X := fresh in
      simple refine (let X : EdgeSet.In A (EdgeSet.add B C) <-> _ := _ in _);
      [|sets_iff|apply (proj2 X); clear X]
  | H : VSet.In ?A (VSet.add ?B ?C) |- _
    => let X := fresh in
      simple refine (let X : VSet.In A (VSet.add B C) <-> _ := _ in _);
      [|sets_iff|apply (proj1 X) in H; clear X]
  | H : EdgeSet.In ?A (EdgeSet.add ?B ?C) |- _
    => let X := fresh in
      simple refine (let X : EdgeSet.In A (EdgeSet.add B C) <-> _ := _ in _);
      [|sets_iff|apply (proj1 X) in H; clear X]
  | H : VSet.In ?A (VSet.singleton ?B) |- _
    => let X := fresh in
      simple refine (let X : VSet.In A (VSet.singleton B) <-> _ := _ in _);
      [|sets_iff|apply (proj1 X) in H; clear X]
  | H : EdgeSet.In ?A (EdgeSet.singleton ?B) |- _
    => let X := fresh in
      simple refine (let X : EdgeSet.In A (EdgeSet.singleton B) <-> _ := _ in _);
      [|sets_iff|apply (proj1 X) in H; clear X]
  | H : EdgeSet.In ?A EdgeSet.empty |- _
    => apply EdgeSetFact.empty_iff in H; contradiction
  end.


Lemma add_edges_invariants {G} (HG : invariants G) (HG' : wGraph.s G = lSet) {gc}
  : invariants (add_edges (edges_of_constraint gc) G).
Proof.
  destruct HG as [H1 [H2 H3]].
  destruct gc.
  - repeat split; cbn in *; rewrite HG' in *; clear HG'.
    + simplify_sets.
      destruct H. left; subst; reflexivity.
      right; right; destruct H. left; subst; reflexivity.
      right; right; destruct H. left; subst; reflexivity.
      right; right. firstorder.
    + simplify_sets.
      right; destruct H. left; subst; reflexivity.
      right; right; destruct H. left; subst; reflexivity.
      right; right; destruct H. left; subst; reflexivity.
      right. firstorder.
    + simplify_sets. repeat right; assumption.
    + intros x H; cbn; simplify_sets.
      match goal with
      | |- Rs ?X _ _ => set (G' := X)
      end.
      assert (R G' lSet g). {
        destruct g; eexists; cbn; simplify_sets; eauto. }
      assert (R G' lSet g0). {
        destruct g0; eexists; cbn; simplify_sets; eauto. }
      intuition; subst; try (constructor; assumption). 
      1-2: destruct g0; try reflexivity; try (constructor; assumption).
      1-2: destruct g; try reflexivity; try (constructor; assumption).
      repeat apply Rs_add_edge; firstorder.
  (* This bullet is a copy and paste of the first one *)
  - repeat split; cbn in *; rewrite HG' in *; clear HG'.
    + simplify_sets.
      destruct H. left; subst; reflexivity.
      right; right; destruct H. left; subst; reflexivity.
      right; right; destruct H. left; subst; reflexivity.
      right; right. firstorder.
    + simplify_sets.
      right; destruct H. left; subst; reflexivity.
      right; right; destruct H. left; subst; reflexivity.
      right; right; destruct H. left; subst; reflexivity.
      right. firstorder.
    + simplify_sets. repeat right; assumption.
    + intros x H; cbn; simplify_sets.
      match goal with
      | |- Rs ?X _ _ => set (G' := X)
      end.
      assert (R G' lSet g). {
        destruct g; eexists; cbn; simplify_sets; eauto. }
      assert (R G' lSet g0). {
        destruct g0; eexists; cbn; simplify_sets; eauto. }
      intuition; subst; try (constructor; assumption). 
      1-2: destruct g0; try reflexivity; try (constructor; assumption).
      1-2: destruct g; try reflexivity; try (constructor; assumption).
      repeat apply Rs_add_edge; firstorder.
  - repeat split; cbn in *; rewrite HG' in *; clear HG'.
    + simplify_sets.
      destruct H. left; subst; reflexivity.
      right; right. firstorder.
    + simplify_sets.
      right; destruct H. left; subst; reflexivity.
      right. firstorder.
    + simplify_sets. repeat right; assumption.
    + intros x H; cbn; simplify_sets.
      intuition; subst.
      reflexivity.
      constructor. exists 1. cbn; simplify_sets; auto.
      apply Rs_add_edge; firstorder.
  - repeat split; cbn in *; rewrite HG' in *; clear HG'.
    + simplify_sets.
      destruct H. left; subst; reflexivity.
      right; right; destruct H. left; subst; reflexivity.
      right; right. firstorder.
    + simplify_sets.
      right; destruct H. left; subst; reflexivity.
      right; right; destruct H. left; subst; reflexivity.
      right. firstorder.
    + simplify_sets. left; reflexivity.
    + intros x H; cbn; simplify_sets.
      intuition; subst.
      all: try reflexivity.
      1-2: constructor; exists 0; cbn; simplify_sets; auto.
      repeat apply Rs_add_edge; firstorder.
Qed.


Definition make_graph (ctrs : GoodConstraintSet.t) : t
  := GoodConstraintSet.fold (add_edges ∘ edges_of_constraint)
                            ctrs init_graph.

Definition labelling_of_valuation (v : valuation) : labelling
  := fun x => match x with
           | lSet => 0
           | ltv (mLevel l) => Pos.to_nat (v.(valuation_mono) l)
           | ltv (mVar n) => v.(valuation_poly) n
           end.

Definition valuation_of_labelling (l : labelling) : valuation
  := {| valuation_mono := fun s => Pos.of_nat (l (ltv (mLevel s)));
        valuation_poly := fun n => l (ltv (mVar n)) |}.


Lemma make_graph_ind (P : t -> Prop) (P0 : P init_graph)
      (P1 : forall G gc, P G -> P (add_edges (edges_of_constraint gc) G))
      : forall ctrs, P (make_graph ctrs).
Proof.
  unfold make_graph. intro ctrs. rewrite GoodConstraintSet.fold_spec.
  set (G := init_graph) in *. clearbody G; revert G P0.
  set (l := GoodConstraintSet.elements ctrs); induction l.
  - easy.
  - intros G P0; cbn. apply IHl. now apply P1.
Qed.

Definition add_edges_E := fold_left (fun E0 e => EdgeSet.add e E0).

Lemma edges_add_edge G E :
  wGraph.E (add_edges E G) = add_edges_E E (wGraph.E G).
Proof.
  revert G; induction E; cbn; intro G. reflexivity.
  apply IHE.
Qed.

Lemma In_add_edges lE SE e
  : EdgeSet.In e (add_edges_E lE SE) <-> In e lE \/ EdgeSet.In e SE.
Proof.
  revert SE. induction lE; cbn.
  - intuition.
  - intros SE; split; intro H.
    pose proof (proj1 (IHlE _) H) as HH; clear IHlE H.
    destruct HH. intuition. simplify_sets. destruct H; auto.
    apply IHlE. destruct H as [[|]|].
    right; simplify_sets. all: intuition.
Qed.


Lemma InA_In_eq {A} x (l : list A) : InA eq x l <-> In x l.
Proof.
  etransitivity. eapply InA_alt.
  firstorder. now subst.
Qed.


Section Spec.
  Context (ctrs : GoodConstraintSet.t).
  Let G := make_graph ctrs.

  Lemma make_graph_invariants : invariants G /\ wGraph.s G = lSet.
  Proof.
    subst G; apply make_graph_ind; clear ctrs.
    - split. apply init_graph_invariants. reflexivity.
    - intros G gc HG; split. 
      + now apply add_edges_invariants.
      + destruct HG as [_ HG]. clear -HG.
        revert G HG.
        induction (edges_of_constraint gc). easy.
        intros G HG. cbn; apply IHl; assumption.
  Qed.

  Definition source_make_graph := proj2 make_graph_invariants.

  Definition ltv_inj x y : ltv x = ltv y -> x = y.
  Proof.
    now inversion 1.
  Defined.

  Definition ltv_lSet x : ltv x <> lSet.
  Proof.
    now inversion 1.
  Defined.

  Lemma source_edge_of_level g : (edge_of_level g)..s = lSet.
  Proof.
    destruct g; reflexivity.
  Qed.

  Lemma target_edge_of_level g : (edge_of_level g)..t = g.
  Proof.
    destruct g; reflexivity.
  Qed.


  Lemma valuation_labelling_eq l (Hl : correct_labelling G l)
    : forall x, VSet.In x (wGraph.V G)
           -> labelling_of_valuation (valuation_of_labelling l) x = l x.
  Proof.
    destruct x; cbn.
    - intros _. apply proj1 in Hl; cbn in Hl.
      etransitivity. symmetry; eassumption.
      f_equal. apply source_make_graph.
    - destruct l0; cbn. 2: reflexivity.
      intro Hs. apply Nat2Pos.id.
      assert (HH: EdgeSet.In (lSet, 1, ltv (mLevel s)) (wGraph.E G)). {
        clear l Hl; subst G. revert s Hs.
        apply make_graph_ind; clear ctrs.
        - intros l H; cbn in *; simplify_sets. inversion H.
        - intros G gc HG l H.
          destruct gc; cbn in *; simplify_sets.
          + rewrite !source_edge_of_level, !target_edge_of_level in H. right.
            destruct H. apply ltv_inj in H. subst; auto.
            destruct H. apply ltv_inj in H. subst; auto.
            destruct H. inversion H.
            destruct H. apply ltv_inj in H. subst; auto.
            destruct H. inversion H.
            destruct H. apply ltv_inj in H. subst; auto.
            firstorder.
          + rewrite !source_edge_of_level, !target_edge_of_level in H. right.
            destruct H. apply ltv_inj in H. subst; auto.
            destruct H. apply ltv_inj in H. subst; auto.
            destruct H. inversion H.
            destruct H. apply ltv_inj in H. subst; auto.
            destruct H. inversion H.
            destruct H. apply ltv_inj in H. subst; auto.
            firstorder.
          + destruct H. inversion H.
            destruct H. inversion H. firstorder.
          + destruct H. inversion H.
            destruct H. inversion H.
            destruct H. inversion H.
            destruct H. inversion H. firstorder. }
      apply (proj2 Hl) in HH; cbn in HH. lia.
  Qed.


  Lemma edges_make_graph :
    wGraph.E G =
    GoodConstraintSet.fold (fun gc E => add_edges_E (edges_of_constraint gc) E)
                           ctrs EdgeSet.empty.
  Proof.
    subst G; unfold make_graph.
    rewrite !GoodConstraintSet.fold_spec.
    set (ctrs' := GoodConstraintSet.elements ctrs); clearbody ctrs'; clear ctrs.
    set (G := init_graph).
    change EdgeSet.empty with (wGraph.E G).
    clearbody G; revert G.
    induction ctrs'; cbn.
    - reflexivity.
    - intros G. rewrite IHctrs'. f_equal. apply edges_add_edge.
  Qed.

  Lemma edges_make_graph' e :
    EdgeSet.In e (wGraph.E G) <-> 
    (GoodConstraintSet.Exists (fun gc => In e (edges_of_constraint gc)) ctrs).
  Proof.
    rewrite edges_make_graph. clear G.
    rewrite !GoodConstraintSet.fold_spec.
    etransitivity. shelve.
    eapply iff_ex.
    intro x. eapply and_iff_compat_r. symmetry; etransitivity.
    eapply GoodConstraintSetProp.FM.elements_iff. eapply InA_In_eq.
    Unshelve.
    set (ctrs' := GoodConstraintSet.elements ctrs) in *.
    clearbody ctrs'; clear ctrs.
    set (SE := EdgeSet.empty) in *.
    transitivity ((exists gc, In gc ctrs' /\ In e (edges_of_constraint gc))
                  \/ EdgeSet.In e SE).
    2: etransitivity; [eapply or_iff_compat_l, EdgeSetFact.empty_iff|intuition].
    clearbody SE; revert SE. induction ctrs'; cbn; intros SE; split.
    - now right.
    - firstorder.
    - intro H. specialize (IHctrs' (add_edges_E (edges_of_constraint a) SE)).
      apply proj1 in IHctrs'.
      specialize (IHctrs' H); clear H.
      destruct IHctrs'. left. firstorder.
      apply In_add_edges in H. destruct H; firstorder.
    - intro H. apply IHctrs'. clear -H.
      eapply or_iff_compat_l. apply In_add_edges.
      destruct H as [[gc [[H1|H1] H2]]|H]; subst; firstorder.
  Qed.


  Lemma make_graph_spec v :
    gc_satisfies v ctrs <-> correct_labelling G (labelling_of_valuation v).
  Proof.
    unfold gc_satisfies, correct_labelling. split; intro H.
    - split. now rewrite source_make_graph.
      intros e He. 
      apply edges_make_graph' in He.
      destruct He as [gc [H0 H1]].
      apply GoodConstraintSet.for_all_spec in H.
      2: intros x y []; reflexivity.
      specialize (H _ H0). cbn in *.
      clear -H H1.
      destruct gc; try apply PeanoNat.Nat.leb_le in H.
      + destruct H1; subst. rewrite source_edge_of_level.
        destruct g; cbn; lia.
        destruct H0; subst. rewrite source_edge_of_level.
        destruct g0; cbn; lia.
        destruct H0 as [|[]]; subst. destruct g, g0; cbn in *; lia.
      + destruct H1; subst. rewrite source_edge_of_level.
        destruct g; cbn; lia.
        destruct H0; subst. rewrite source_edge_of_level.
        destruct g0; cbn; lia.
        destruct H0 as [|[]]; subst. destruct g, g0; cbn in *; lia.
      + destruct H1 as [|[]]; subst. cbn. assumption. 
      + destruct H1 as [|[|[]]]; subst; cbn.
        apply PeanoNat.Nat.eqb_eq in H. lia. lia.
    - apply GoodConstraintSet.for_all_spec.
      intros x y []; reflexivity.
      intros gc Hgc.
      pose proof (fun e p => proj2 (edges_make_graph' e)
                                (ex_intro _ gc (conj Hgc p))) as H0.
      destruct H as [_ H].
      pose proof (fun e p => H e (H0 e p)) as HH. clear -HH.
      destruct gc; cbn in HH; try apply PeanoNat.Nat.leb_le.
      4: apply PeanoNat.Nat.eqb_eq.
      simple refine (let HH' := HH (ltv g, 0, ltv g0) _ in _);
        [intuition|clearbody HH'; clear HH];
        destruct g, g0; cbn in *; lia.
      simple refine (let HH' := HH (ltv g, 1, ltv g0) _ in _);
        [intuition|clearbody HH'; clear HH];
        destruct g, g0; cbn in *; lia.
      simple refine (let HH' := HH (lSet, 1, ltv (mVar n)) _ in _);
        [intuition|clearbody HH'; clear HH];
        cbn in *; lia.
      simple refine (let HH' := HH (ltv (mVar n), 0, lSet) _ in _);
        [intuition|clearbody HH'; clear HH];
        cbn in *; lia.
  Qed.


  Corollary make_graph_spec' l :
    (* gc_satisfies (valuation_of_labelling l) ctrs <-> correct_labelling G l. *)
    correct_labelling G l -> gc_satisfies (valuation_of_labelling l) ctrs.
  Proof.
    intro H. apply (make_graph_spec (valuation_of_labelling l)).
    unfold correct_labelling; intuition.
    now rewrite source_make_graph.
    destruct make_graph_invariants as [H1 _].
    rewrite !valuation_labelling_eq; firstorder. 
  Qed.

  Corollary make_graph_spec2 :
    gc_consistent ctrs <-> exists l, correct_labelling G l.
  Proof.
    split.
    - intros [v H]. exists (labelling_of_valuation v).
      apply make_graph_spec. assumption.
    - intros [l Hl]. exists (valuation_of_labelling l).
      apply make_graph_spec'. assumption.
  Defined.
End Spec.


Definition G := make_graph
  (GoodConstraintSet.add (gc_lt (mVar 0) (mVar 1))
 (GoodConstraintSet_pair (gc_lt_set 0) (gc_eq_set 1))).

Compute (lsp G lSet (mVar 0)).
Compute (lsp G lSet (mVar 1)).
Compute (lsp G lSet lSet).

(* Section Test. *)

(*   Definition get_graph G0 := match G0 with *)
(*                              | Some φ => φ *)
(*                              | None => init_graph *)
(*                              end. *)

(*   Definition G0 := make_graph ConstraintSet.empty. *)
(*   Check (eq_refl : G0 = Some _). *)
(*   Definition G := get_graph G0. *)

(*   Local Existing Instance default_checker_flags. *)

(*   Check (eq_refl : check_leq G Universe.type0m Universe.type0 = true). *)
(*   Check (eq_refl : check_lt G Universe.type0m Universe.type0 = true). *)
(*   Check (eq_refl : check_lt G Universe.type0m Universe.type0m = false). *)
(*   Check (eq_refl : check_lt G Universe.type0 Universe.type0m = false). *)
(*   Check (eq_refl : check_lt G Universe.type0 Universe.type0 = false). *)
(*   Check (eq_refl : no_universe_inconsistency G = true). *)

(*   Definition ctrs0 := ConstraintSet.add (Level.Level "Top.0", Lt, Level.Level "Top.1") *)
(*                                         (ConstraintSet.singleton (Level.Var 0, Lt, Level.Var 1)). *)
(*   Definition G'0 := make_graph ctrs0. *)
(*   Check (eq_refl : G'0 = Some _). *)
(*   Definition G' := get_graph G'0. *)

(*   Check (eq_refl : check_lt G' (Universe.make (Level.Level "Top.0")) (Universe.make (Level.Var 0)) = false). *)
(*   Check (eq_refl : check_leq G' (Universe.make (Level.Level "Top.1")) (Universe.make (Level.lProp)) = false). *)
(*   Check (eq_refl : check_leq G' (Universe.super (Level.Level "Top.1")) (Universe.make (Level.Level "Top.1")) = false). *)
(*   Check (eq_refl : check_lt G' (Universe.make (Level.Level "Top.1")) (Universe.super (Level.Level "Top.1")) = true). *)
(*   Check (eq_refl : check_lt G' (Universe.make (Level.Level "Top.1")) (Universe.make (Level.Level "Top.1")) = false). *)
(*   Check (eq_refl : check_eq G' (Universe.make (Level.Level "Top.1")) (Universe.make (Level.Level "Top.1")) = true). *)
(*   Check (eq_refl : no_universe_inconsistency G = true). *)

(*   Check (eq_refl : check_lt G' (Universe.make (Level.Var 1)) (Universe.make (Level.Var 0)) = false). *)
(*   Check (eq_refl : check_leq G' (Universe.make (Level.Var 0)) (Universe.make (Level.Var 1)) = true). *)
(*   Check (eq_refl : check_lt G' (Universe.make (Level.Var 0)) (Universe.make (Level.Var 1)) = true). *)
(*   Check (eq_refl : check_leq G' Universe.type1 Universe.type0 = false). *)
(*   Check (eq_refl : check_lt G' Universe.type1 Universe.type1 = false). *)


(*   Definition ctrs1 := ConstraintSet.add (Level.Var 1, Eq, Level.Var 2) *)
(*                                         (ConstraintSet.add (Level.Var 2, Le, Level.lSet) ctrs0). *)
(*   Definition G''0 := make_graph ctrs1. *)
(*   Check (eq_refl : G''0 = Some _). *)
(*   Definition G'' := get_graph G''0. *)

(*   Check (eq_refl : no_universe_inconsistency G'' = false). *)

(* End Test. *)
