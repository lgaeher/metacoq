Require Import Peano_dec Nat Bool List Relations Structures.Equalities
        MSets.MSetWeakList MSetFacts MSetProperties Lia.
From Template Require Import utils monad_utils.

Inductive on_Some {A} (P : A -> Prop) : option A -> Prop :=
| no_some : forall x, P x -> on_Some P (Some x).

Lemma on_Some_spec {A} (P : A -> Prop) z :
  on_Some P z <-> exists x, z = Some x /\ P x.
Proof.
  split. intros []. now eexists.
  intros [? [e ?]]. subst. now constructor.
Qed.

Fixpoint filter_pack {A} (P : A -> Prop) (HP : forall x, {P x} + {~ P x})
         (l : list A) {struct l} : list {x : A & P x} :=
  match l with
  | nil => nil
  | x :: l => match HP x with
             | left p => (existT _ _ p) :: (filter_pack P HP l)
             | right _ => filter_pack P HP l
             end
  end.

Lemma fold_max_In n m l (H : fold_left max l n = m)
  : n = m \/ In m l.
Proof.
  revert n H; induction l; cbn; intros n H.
  intuition.
  apply IHl in H.
  apply or_assoc. destruct H; [left|now right]. lia.
Qed.

Definition is_Some {A} (x : option A) := exists a, x = Some a.

Definition eq_max n m k : max n m = k -> n = k \/ m = k.
  intro; lia.
Qed.

Module Nbar.
  (* None is -∞ *)
  Definition t := option nat.
  Definition max (n m : t) : t :=
    match n, m with
    | Some n, Some m => Some (max n m)
    | Some n, None => Some n
    | None, Some m => Some m
    | _, _ => None
    end.
  Definition add (n m : t) : t :=
    match n, m with
    | Some n, Some m => Some (n + m)
    | _, _ => None
    end.
  Definition le (n m : t) : Prop :=
    match n, m with
    | Some n, Some m => n <= m
    | Some _, None => False
    | None, _ => True
    end.

  Infix "+" := add : nbar_scope.
  Infix "<=" := le : nbar_scope.
  Delimit Scope nbar_scope with nbar.
  Bind Scope nbar_scope with t.

  Local Open Scope nbar_scope.

  Definition is_finite (n : t) := is_Some n.
  Definition is_finite_max (n m : t)
    : is_finite (max n m) <-> is_finite n \/ is_finite m.
  Proof.
    split.
    - destruct n, m; cbn; intros [k e]; try discriminate.
      apply some_inj, eq_max in e.
      destruct e; [left|right]; eexists; f_equal; eassumption.
      left; eexists; reflexivity.
      right; eexists; reflexivity.
    - intros [H|H].
      destruct H as [n' e]; rewrite e; cbn.
      destruct m; eexists; reflexivity.
      destruct H as [m' e]; rewrite e; cbn.
      destruct n; eexists; reflexivity.
  Defined.
  Definition is_finite_add (n m : t)
    : is_finite (n + m) <-> is_finite n /\ is_finite m.
  Proof.
    split.
    - destruct n, m; cbn; intros [k e]; try discriminate.
      split; eexists; reflexivity.
    - intros [[n1 e1] [n2 e2]]; rewrite e1, e2.
      eexists; reflexivity.
  Defined.

  Definition is_pos (n : t) := Some 1 <= n.
  Definition is_pos_max (n m : t)
    : is_pos (max n m) -> is_pos n \/ is_pos m.
  Proof.
    destruct n, m; cbn; intuition. lia.
  Defined.
  Definition is_pos_add (n m : t)
    : is_pos (n + m) -> is_pos n \/ is_pos m.
  Proof.
    destruct n, m; cbn; intuition. lia.
  Defined.

  Definition is_pos_is_finite n : is_pos n -> is_finite n.
  Proof.
    destruct n; cbn; [|intuition].
    destruct n. lia. intros _. eexists; reflexivity.
  Qed.

  Definition add_assoc n m p : n + (m + p) = n + m + p.
  Proof.
    destruct n, m, p; try reflexivity; cbn.
    now rewrite PeanoNat.Nat.add_assoc.
  Defined.

  Definition add_0_r n : (n + Some 0 = n)%nbar.
  Proof.
    destruct n; try reflexivity; cbn.
    now rewrite PeanoNat.Nat.add_0_r.
  Defined.

  Definition max_lub n m p : n <= p -> m <= p -> max n m <= p.
  Proof.
    destruct n, m, p; cbn; intuition.
    lia.
  Defined.

  Definition add_max_distr_r n m p : max (n + p) (m + p) = max n m + p.
  Proof.
    destruct n, m, p; try reflexivity; cbn.
    now rewrite PeanoNat.Nat.add_max_distr_r.
  Defined.

  Definition max_le' n m p : p <= n \/ p <= m -> p <= max n m.
  Proof.
    destruct n, m, p; cbn; intuition; lia.
  Defined.

  Definition plus_le_compat_l n m p : n <= m -> p + n <= p + m.
  Proof.
    destruct n, m, p; cbn; intuition.
  Defined.

  Definition max_idempotent n : max n n = n.
  Proof.
    destruct n; try reflexivity; cbn.
    now rewrite PeanoNat.Nat.max_idempotent.
  Defined.
End Nbar.


Module WeightedGraph (V : UsualDecidableType).
  Module VSet := MSets.MSetWeakList.Make V.
  (* todo: remove if unused *)
  Module VSetFact := WFactsOn V VSet.
  Module VSetProp := WPropertiesOn V VSet.
  Module Edge.
    Definition t := (V.t * nat * V.t)%type.
    Definition eq : t -> t -> Prop := eq.
    Definition eq_equiv : RelationClasses.Equivalence eq := _.
    Definition eq_refl : forall x : t, eq x x := @eq_refl _.
    Definition eq_sym : forall x y : t, eq x y -> eq y x := @eq_sym _.
    Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z := @eq_trans _.
    Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
      unfold eq. decide equality. apply V.eq_dec.
      decide equality. apply PeanoNat.Nat.eq_dec. apply V.eq_dec.
    Defined.
    Definition eqb : t -> t -> bool := fun x y => if eq_dec x y then true else false.

    (* Definition eq (e1 e2 : t) : Prop := *)
    (*   let '(x1, n1, y1) := e1 in let '(x2, n2, y2) := e2 in *)
    (*   V.eq x1 x2 /\ n1 = n2 /\ V.eq y1 y2. *)
    (* Definition eq_equiv : RelationClasses.Equivalence eq. *)
    (*   split. *)
    (*   intros [[x n] y]; cbn; intuition. *)
    (*   intros [[x n] y] [[x' n'] y']; cbn; intuition. *)
    (*   intros [[x n] y] [[x' n'] y'] [[x'' n''] y'']; cbn; intuition. *)
    (*   all: etransitivity; eassumption.  *)
    (* Defined. *)
    (* Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}. *)
    (*   intros [[x1 n1] y1] [[x2 n2] y2]; cbn. *)
    (*   destruct (V.eq_dec x1 x2). destruct (V.eq_dec y1 y2).  *)
    (*   destruct (Peano_dec.eq_nat_dec n1 n2). *)
    (*   left. intuition. *)
    (*   all: right; intuition. *)
    (* Defined. *)
  End Edge.
  Module EdgeSet:= MSets.MSetWeakList.Make Edge.
  Module EdgeSetFact := WFactsOn Edge EdgeSet.
  Module EdgeSetProp := WPropertiesOn Edge EdgeSet.

  Definition t := (VSet.t * EdgeSet.t * V.t)%type.

  Let V (G : t) := fst (fst G).
  Let E (G : t) := snd (fst G).
  Let s (G : t) := snd G.

  Definition e_source : Edge.t -> V.t := fst ∘ fst.
  Definition e_target : Edge.t -> V.t := snd.
  Definition e_weight : Edge.t -> nat := snd ∘ fst.
  Notation "x ..s" := (e_source x) (at level 3, format "x '..s'").
  Notation "x ..t" := (e_target x) (at level 3, format "x '..t'").
  Notation "x ..w" := (e_weight x) (at level 3, format "x '..w'").

  Definition labelling := V.t -> nat.

  Section graph.
    Context (G : t).

    Definition R (x y : V.t) := exists n, EdgeSet.In (x, n, y) (E G).

    Definition Rs := clos_refl_trans _ R.

    Global Instance Rs_refl : Reflexive Rs := rt_refl _ _.
    Global Instance Rs_trans : Transitive Rs := rt_trans _ _.

    Definition invariants :=
      (* E ⊆ V × V *)
      (forall e, EdgeSet.In e (E G) -> VSet.In e..s (V G) /\ VSet.In e..t (V G))
      (* s ∈ V *)
      /\  VSet.In (s G) (V G)
      (* s is a source *)
      /\ (forall x, VSet.In x (V G) -> Rs (s G) x).

    Definition add_node x : t :=
      (VSet.add x (V G), (E G), (s G)).

    Definition add_edge e : t :=
      (VSet.add e..s (VSet.add e..t (V G)), EdgeSet.add e (E G), (s G)).


    Definition R0 (x y : V.t) := EdgeSet.In (x, 0, y) (E G).

    (* paths of weight 0 *)
    Definition R0s := clos_refl_trans _ R0.

    Global Instance R0s_refl : Reflexive R0s := rt_refl _ _.
    Global Instance R0s_trans : Transitive R0s := rt_trans _ _.

    (* paths with one positive edge *)
    Definition R1 (x y : V.t) :=
      exists x0 y0 n, R0s x x0 /\ EdgeSet.In (x0, S n, y0) (E G) /\ R0s y0 y.

    Definition acyclic := well_founded R1.

    Definition R1s := clos_trans _ R1.

    Global Instance R1s_trans : Transitive R1s := t_trans _ _.

    Lemma acyclic_notR1s : acyclic -> forall x, ~ R1s x x.
    Proof.
      intros H x; induction (H x).
      intro p. apply clos_trans_tn1 in p.
      inversion_clear p.
      + eapply H1. exact H2. now constructor.
      + eapply H1. exact H2.
        etransitivity. constructor; eassumption.
        now apply clos_tn1_trans.
    Qed.

    Definition correct_labelling (l : labelling) :=
      l (s G) = 0 /\
      forall e, EdgeSet.In e (E G) -> l e..s + e..w <= l e..t.

    Lemma correct_labelling_R0 l (Hl : correct_labelling l)
      : forall x y, R0 x y -> l x <= l y.
    Proof.
      intros x y He. apply proj2 in Hl.
      specialize (Hl _ He); cbn in Hl. lia.
    Qed.

    Lemma correct_labelling_R0s l (Hl : correct_labelling l)
      : forall x y, R0s x y -> l x <= l y.
    Proof.
      induction 1. now apply correct_labelling_R0.
      all: lia.
    Qed.

    Lemma correct_labelling_R l (Hl : correct_labelling l)
      : forall x y, R1 x y -> l x < l y.
    Proof.
      intros x y [x' [y' [n [He1 [He2 He3]]]]].
      apply (correct_labelling_R0s l Hl) in He1.
      apply (correct_labelling_R0s l Hl) in He3.
      apply proj2 in Hl. specialize (Hl _ He2); cbn in Hl. lia.
    Qed.

    Lemma acyclic_labelling l : correct_labelling l -> acyclic.
    Proof.
      intro Hl. eapply Wf_nat.well_founded_lt_compat.
      exact (correct_labelling_R _ Hl).
    Qed.

    Definition get_edges x y :=
      let L := List.filter
                 (fun e => match V.eq_dec e..s x, V.eq_dec (snd e) y with
                     | left _, left _ => true
                     | _, _ => false
                     end)
                 (EdgeSet.elements (E G)) in (* edges x --> y *)
      List.map (fun e => e..w) L.

    Lemma get_edges_spec x y n
      : In n (get_edges x y) <-> EdgeSet.In (x, n, y) (E G).
    Proof.
      etransitivity. apply in_map_iff.
      etransitivity. 2: apply EdgeSet.elements_spec1.
      set (L := EdgeSet.elements (E G)); clearbody L.
      etransitivity. 2: symmetry; apply InA_alt.
      apply Morphisms_Prop.ex_iff_morphism.
      intros [[x' n'] y']; cbn.
      etransitivity. apply and_iff_compat_l. apply filter_In.
      cbn. destruct (V.eq_dec x' x); destruct (V.eq_dec y' y); intuition; subst.
      reflexivity. all: inversion H0; intuition.
    Qed.


    Import Nbar.

    (* l is the list of authorized intermediate nodes *)
    (* d (a::l) x y = max (d l x y)  (d l x a + d l a y) *)
    Definition d'0 (l : list V.t) (x y : V.t) : Nbar.t.
    Proof.
      revert x y; induction l; intros x y.
      - refine (match get_edges x y with
                | nil => if V.eq_dec x y then Some 0 else None
                | x :: l => Some (List.fold_left Nat.max l x)
                end).
      - refine (max (IHl x y) (IHl x a + IHl a y)).
    Defined.

    Definition d' := d'0 (VSet.elements (V G)).

    (* R'' is Rs with l the list of authorized intermediate nodes *)
    Inductive R'' l : V.t -> V.t -> Prop :=
    | r''_refl x : R'' l x x
    | r''_one x y n : EdgeSet.In (x, n, y) (E G) -> R'' l x y
    | r''_step x x' y n : EdgeSet.In (x, n, x') (E G)
                          ->  In x' l -> R'' l x' y -> R'' l x y.

    Instance R''_refl l : Reflexive (R'' l) := r''_refl _.

    Context (HI : invariants).

    Instance R''_trans : Transitive (R'' (VSet.elements (V G))).
    Proof.
      intros x y z H. induction H.
      trivial.
      intro H1. eapply r''_step; try eassumption.
      apply proj1 in HI. specialize (HI _ H); apply proj2 in HI; cbn in HI.
      apply VSetFact.elements_1, InA_alt in HI. 
      now destruct HI as [? [[] HH]].
      intro. eapply r''_step. eassumption.
      apply proj1 in HI. specialize (HI _ H); apply proj2 in HI; cbn in HI.
      apply VSetFact.elements_1, InA_alt in HI. 
      now destruct HI as [? [[] HH]].
      auto.
    Qed.

    Definition R''_ok x y : Rs x y <-> R'' (VSet.elements (V G)) x y.
    Proof.
      split.
      - induction 1.
        + destruct H as [n H]. eapply r''_step. eassumption.
          apply proj1 in HI. specialize (HI _ H); apply proj2 in HI; cbn in HI.
          apply VSetFact.elements_1, InA_alt in HI. 
          now destruct HI as [? [[] HH]].
          reflexivity.
        + reflexivity.
        + etransitivity; eassumption.
      - induction 1.
        + reflexivity.
        + constructor. eexists; eassumption.
        + etransitivity. 2: eassumption.
          constructor; eexists; eassumption.
    Qed.

    Lemma d'_ok0 l : forall x y, Nbar.is_finite (d'0 l x y) -> Rs x y.
    Proof.
      induction l; intros x y.
      - simpl. case_eq (get_edges x y).
        intros _.
        case_eq (V.eq_dec x y); intros e ? []; try discriminate.
        now rewrite e.
        intros n0 l H _. constructor. exists n0.
        apply get_edges_spec. rewrite H; intuition.
      - simpl. intro H. apply Nbar.is_finite_max in H.
        destruct H. now apply IHl.
        apply Nbar.is_finite_add in H; destruct H as [H1 H2].
        etransitivity; eapply IHl; eassumption.
    Qed.

    Lemma R1s_Rs : forall x y z, R1s x y -> Rs y z -> R1s x z.
    Proof.
      intros x y z H1 H2; revert H1; induction H2; intuition.
      destruct H as [[|n] H].
      - revert H; induction H1.
        + intro H1. constructor.
          destruct H as [x1 [y1 [n1 H]]]. exists x1; exists y1; exists n1.
          intuition. etransitivity. eassumption. constructor. assumption.
        + intro. etransitivity. eassumption. intuition.
      - etransitivity. eassumption. constructor. exists x0; exists y; exists n; easy.
    Qed.

    Lemma Rs_R1s : forall x y z, Rs x y -> R1s y z -> R1s x z.
    Proof.
      intros x y z H1 H2; induction H1; intuition.
      destruct H as [[|n] H].
      - revert H; induction H2.
        + intro H2. constructor.
          destruct H as [x1 [y1 [n1 H]]]. exists x1; exists y1; exists n1.
          intuition. etransitivity. 2: eassumption. constructor. assumption.
        + intro. etransitivity. 2: eassumption. intuition.
      - etransitivity. 2: eassumption. constructor. exists x; exists y; exists n; easy.
    Qed.

    Lemma d'_ok1 l : forall x y, (is_pos (d'0 l x y)) -> R1s x y.
    Proof.
      induction l; intros x y.
      - simpl. case_eq (get_edges x y).
        intros _.
        case_eq (V.eq_dec x y); intros e H H1; inversion H1.
        intros n l H H0.
        set (m := fold_left Nat.max l n) in *.
        pose proof (fold_max_In n m l eq_refl).
        change (In m (n :: l)) in H1. rewrite <- H in H1.
        apply get_edges_spec in H1.
        destruct m. inversion H0.
        constructor. exists x; exists y; exists m; repeat split; try assumption.
        all: reflexivity.
      - simpl. intro H; apply Nbar.is_pos_max in H.
        destruct H as [H|H].
        + apply IHl; assumption.
        + pose proof (Nbar.is_pos_is_finite _ H) as H1.
          apply Nbar.is_finite_add in H1; destruct H1 as [H1 H1'].
          apply Nbar.is_pos_add in H; destruct H as [H|H].
          eapply R1s_Rs. eapply IHl; eassumption.
          eapply d'_ok0; eassumption.
          eapply Rs_R1s. eapply d'_ok0; eassumption. 
          eapply IHl; eassumption.
    Qed.

    Lemma d'_ok2 (HG : forall x, ~ R1s x x) l x : d'0 l x x = Some 0.
    Proof.
      induction l.
      - simpl. case_eq (get_edges x x).
        intros _. case_eq (V.eq_dec x x); intuition.
        intros n l H.
        pose proof (fold_max_In n _ l eq_refl) as X.
        set (m := fold_left Nat.max l n) in *; clearbody m.
        change (In m (n :: l)) in X. rewrite <- H in X; clear H.
        destruct m; [reflexivity|].
        apply False_rect, (HG x). constructor.
        apply get_edges_spec in X.
        exists x; exists x; exists m. intuition.
      - simpl. rewrite IHl. simpl.
        case_eq (d'0 l x a); case_eq (d'0 l a x); cbn; intros; try reflexivity.
        destruct n, n0; cbn. reflexivity.
        all: apply False_rect, (HG x).
        + eapply R1s_Rs.
          eapply d'_ok1. rewrite H0. cbn; lia.
          eapply d'_ok0. eexists; eassumption.
        + eapply Rs_R1s.
          eapply d'_ok0. eexists; eassumption.
          eapply d'_ok1. rewrite H. cbn; lia.
        + etransitivity; eapply d'_ok1.
          rewrite H0; cbn; lia.
          rewrite H; cbn; lia.
    Qed.


    Lemma d'_ok0' l : forall x y, R'' l x y -> is_finite (d'0 l x y).
    Proof.
      induction l; intros x y.
      - induction 1; cbn.
        + destruct (get_edges x x); [|eexists; reflexivity].
          destruct (V.eq_dec x x); [eexists; reflexivity|].
          contradiction.
        + case_eq (get_edges x y); intros; [|eexists; reflexivity].
          apply get_edges_spec in H.
          rewrite H0 in H; inversion H.
        + destruct (get_edges x y); [|eexists; reflexivity].
          destruct (V.eq_dec x y); [eexists; reflexivity|].
          intuition.
      - intro H; simpl. apply Nbar.is_finite_max.
        assert (HH : R'' l x y \/ (R'' l x a /\ R'' l a y)). {
          clear IHl.
          induction H.
          + left; reflexivity.
          + left; econstructor; eassumption.
          + destruct IHR''.
            * destruct H0.
              -- subst. right. split; [|assumption].
                 econstructor; eassumption.
              -- left. eapply r''_step; eassumption.
            * destruct H2 as [H2 H3]. right. split; [|assumption].
              destruct H0.
              -- subst. econstructor. eassumption.
              -- eapply r''_step; eassumption. }
        destruct HH as [HH|[H1 H2]]; [left|right].
        eauto. apply Nbar.is_finite_add; eauto.
    Qed.

    Lemma fold_max_le n m l (H : n <= m \/ Exists (Peano.le n) l)
      : n <= fold_left Nat.max l m.
    Proof.
      revert m H; induction l; cbn in *; intros m [H|H].
      assumption. inversion H.
      eapply IHl. left; lia.
      eapply IHl. inversion_clear H.
      left; lia. right; assumption.
    Qed.

    Lemma fold_max_le' n m l (H : In n (m :: l))
      : n <= fold_left Nat.max l m.
    Proof.
      apply fold_max_le. destruct H.
      left; lia. right. apply Exists_exists.
      eexists. split. eassumption. reflexivity.
    Qed.

    Lemma d'_ok3 (HG : forall x, ~ R1s x x) l x y1 y2 n
          (He : EdgeSet.In (y1, n, y2) (E G))
          (Hy : In y1 l)
      : (d'0 l x y1 + Some n <= d'0 l x y2)%nbar.
    Proof.
      revert x; induction l; intro x.
      - simpl. case_eq (get_edges x y1); cbn; intro H.
        + destruct (V.eq_dec x y1); cbn; [|trivial].
          subst. apply get_edges_spec in He.
          case_eq (get_edges y1 y2); cbn; intro H'.
          rewrite H' in He; inversion He.
          intros l H0. rewrite H0 in He.
          now apply fold_max_le'.
        + inversion Hy.
      - simpl. destruct Hy.
        + subst. rewrite (d'_ok2 HG), add_0_r, max_idempotent.
          apply max_le'. right. apply plus_le_compat_l.
          clear -He HI. {
            induction l.
            * apply get_edges_spec in He. simpl.
              case_eq (get_edges y1 y2); intros; rewrite H in He.
              inversion He. now apply fold_max_le'. 
            * change (Some n <= max (d'0 l y1 y2) (d'0 l y1 a + d'0 l a y2))%nbar.
              apply max_le'. now left. }
        + specialize (IHl H). rewrite <- add_max_distr_r.
          apply max_lub; apply  max_le'.
          * now left.
          * right. rewrite <- add_assoc. now apply plus_le_compat_l.
    Defined.


    Lemma d'_ok (HG : forall x, ~ R1s x x) :
        correct_labelling (fun x => option_get 0 (d' (s G) x)).
    Proof.
      split.
      - unfold d'. now rewrite d'_ok2.
      - intros [[x n] y] He; cbn. unfold d'.
        simple refine (let H := d'_ok3 HG (VSet.elements (V G)) (s G) x y n He _
                       in _); [|clearbody H].
        apply proj1 in HI. specialize (HI _ He).
        apply proj1, InA_alt in HI. destruct HI as [? [[] ?]]; assumption.
        simple refine (let H1 := d'_ok0' (VSet.elements (V G)) (s G) x _ in _);
          [|destruct H1 as [n1 H1]].
        apply R''_ok. apply HI.
        apply proj1 in HI. specialize (HI _ He); apply HI.
        simple refine (let H2 := d'_ok0' (VSet.elements (V G)) (s G) y _ in _);
          [|destruct H2 as [n2 H2]].
        apply R''_ok. apply HI.
        apply proj1 in HI. specialize (HI _ He); apply HI.
        now rewrite H1, H2 in *.
    Defined.

    
    Lemma notR1s_correct_labelling
      : (forall x, ~ R1s x x) -> exists l, correct_labelling l.
    Proof.
      intro HG; eexists. eapply (d'_ok HG).
    Defined.

    Lemma notR1s_acyclic : (exists l, correct_labelling l) -> acyclic.
      intros [l Hl]. eapply Wf_nat.well_founded_lt_compat.
      exact (correct_labelling_R _ Hl).
    Defined.

    Lemma d'_qsmlf : forall x y, R1s x y -> is_pos (d' x y).
    Proof.
      induction 1.
      - pose (d'_ok3).
    Abort.

    Lemma lqsdkf : (forall x, ~ R1s x x) <-> (forall x, d' x x = Some 0).
    Proof.
      split. intros; now apply d'_ok2.
      intros H x p. 
    Abort.



    (* Rs -> leq : facile *)
    (* leq -> d = Some : facile pq d correct_labelling *)
    (* d = Some _ -> Rs ?? *)


End graph.

Lemma Rs_add_edge {G} e {x y} : Rs G x y -> Rs (add_edge G e) x y.
Proof.
  induction 1.
  * constructor. destruct H as [n H].
    exists n. cbn. apply EdgeSetFact.add_iff; auto.
  * reflexivity.
  * etransitivity; eauto.
Qed.

End WeightedGraph.





(* Section BellmanFord. *)

(*   Context (φ : t). *)

(*   (* Z ∪ +∞ *) *)
(*   (* None is for +∞ *) *)
(*   Definition Zbar := Z. *)

(*   (* For each node: predecessor and distance from the source *) *)
(*   Definition pred_graph := VerticeMap.t (vertice * Zbar). *)

(*   (* Definition add_node_pred_graph n : pred_graph -> pred_graph *) *)
(*   (* := VerticeMap.add n None. *) *)

(*   Definition init_pred_graph s : pred_graph := *)
(*     (* let G := EdgeSet.fold *) *)
(*     (* (fun '(l1,_,l2) G => add_node_pred_graph l2 (add_node_pred_graph l1 G)) *) *)
(*     (* φ (VerticeMap.empty _) in *) *)
(*     VerticeMap.add s (s, 0) (VerticeMap.empty _). *)

(*   Definition relax (e : edge) (G : pred_graph) : pred_graph := *)
(*     let '((u, w), v) := e in *)
(*     match VerticeMap.find u G, VerticeMap.find v G with *)
(*     | Some (_, ud), Some (_, vd) => if vd >? (ud + btz w) then *)
(*                                      VerticeMap.add v (u, ud + btz w) G *)
(*                                    else G *)
(*     | Some (_, ud), None => VerticeMap.add v (u, ud + btz w) G *)
(*     | _, _ => G *)
(*     end. *)

(*   Definition BellmanFord s : pred_graph := *)
(*     let G := init_pred_graph s in *)
(*     let G' := VerticeSet.fold (fun _ => EdgeSet.fold relax (snd φ)) (fst φ) G in *)
(*     G'. *)

(*   (* true if all is ok *) *)
(*   Definition no_universe_inconsistency : bool := *)
(*     let G := BellmanFord lSet in *)
(*     let negative_cycle := EdgeSet.exists_ (fun '((u,w),v) => *)
(*                           match VerticeMap.find u G, VerticeMap.find v G with *)
(*                           | Some (_, ud), Some (_, vd) => Z.gtb vd (ud + btz w) *)
(*                           | _, _ => false *)
(*                           end) (snd φ) in *)
(*     negb negative_cycle. *)

(*   (** *** Universe comparisons *) *)

(*   (* If enforce l1 l2 = Some n, the graph enforces that l2 is at least l1 + n *) *)
(*   (* i.e. l1 + n <= l2 *) *)
(*   (* If None nothing is enforced by the graph between those two levels *) *)
(*   Definition enforce (u v : vertice) : option Z := *)
(*     let G := BellmanFord u in *)
(*     match VerticeMap.find v G with *)
(*     | Some (_, vd) => Some (Z.opp vd) *)
(*     | None => None *)
(*     end. *)















(*   Definition check_le_vertice (l1 l2 : vertice) : bool := *)
(*     match enforce l1 l2 with *)
(*     | Some k => Z.geb k 0 *)
(*     | None => false *)
(*     end. *)

(*   Definition check_lt_vertice (l1 l2 : vertice) : bool := *)
(*     match enforce l1 l2 with *)
(*     | Some k => Z.geb k 1 *)
(*     | None => false *)
(*     end. *)

(*   Definition check_eq_vertice (l1 l2 : vertice) : bool := *)
(*     check_le_vertice l1 l2 && check_le_vertice l2 l1. *)


(*   Definition check_le_level (l1 l2 : universe_level) : bool := *)
(*     match ltv l1, ltv l2 with *)
(*     | None, _ => true *)
(*     | _, None => false *)
(*     | Some l1, Some l2 => match enforce l1 l2 with *)
(*                          | Some k => Z.geb k 0 *)
(*                          | None => false *)
(*                          end *)
(*     end. *)

(*   Definition check_lt_level (l1 l2 : universe_level) : bool := *)
(*     match ltv l1, ltv l2 with *)
(*     | _, None => false *)
(*     | None, _ => true *)
(*     | Some l1, Some l2 => match enforce l1 l2 with *)
(*                          | Some k => Z.geb k 1 *)
(*                          | None => false *)
(*                          end *)
(*     end. *)

(*   Definition check_eq_level (l1 l2 : universe_level) : bool := *)
(*     check_le_level l1 l2 && check_le_level l2 l1. *)


(*   Definition check_constraint (cstr : univ_constraint) : bool := *)
(*     let '(l, d, r) := cstr in *)
(*     match d with *)
(*     | Eq => check_eq_level l r *)
(*     | Lt => check_lt_level l r *)
(*     | Le => check_le_level l r *)
(*     end. *)

(*   Definition check_constraints (cstrs : ConstraintSet.t) : bool := *)
(*     ConstraintSet.for_all check_constraint cstrs. *)

(*   Definition check_le_level_expr (e1 e2 : Universe.Expr.t) : bool := *)
(*     match ltv (fst e1), ltv (fst e2) with *)
(*     | None, _ => true *)
(*     | _, None => false *)
(*     | Some l1, Some l2 => *)
(*       match enforce l1 l2 with *)
(*       | None => false *)
(*       | Some k => match snd e1, snd e2 with *)
(*                  | false, false *)
(*                  | true, true => k >=? 0 *)
(*                  | true, false => k >=? 1 *)
(*                  | false, true => k >=? -1 *)
(*                  end *)
(*       end *)
(*     end. *)

(*   Definition check_lt_level_expr (e1 e2 : Universe.Expr.t) : bool := *)
(*     match ltv (fst e1), ltv (fst e2) with *)
(*     | _, None => false *)
(*     | None, _ => true *)
(*     | Some l1, Some l2 => *)
(*       match enforce l1 l2 with *)
(*       | None => false *)
(*       | Some k => match snd e1, snd e2 with *)
(*                  | false, false *)
(*                  | true, true => k >=? 1 *)
(*                  | true, false => k >=? 2 *)
(*                  | false, true => k >=? 0 *)
(*                  end *)
(*       end *)
(*     end. *)

(*   Definition check_eq_level_expr (e1 e2 : Universe.Expr.t) : bool := *)
(*     check_le_level_expr e1 e2 && check_le_level_expr e2 e1. *)

(*   Definition exists_bigger_or_eq (e1 : Universe.Expr.t) (u2 : Universe.t) : bool := *)
(*     Universe.existsb (check_le_level_expr e1) u2. *)

(*   Definition exists_strictly_bigger (e1 : Universe.Expr.t) (u2 : Universe.t) : bool := *)
(*     Universe.existsb (check_lt_level_expr e1) u2. *)

(*   Definition check_lt (u1 u2 : Universe.t) : bool := *)
(*     Universe.for_all (fun e => exists_strictly_bigger e u2) u1. *)

(*   Definition check_leq0 (u1 u2 : Universe.t) : bool := *)
(*     Universe.for_all (fun e => exists_bigger_or_eq e u2) u1. *)

(*   (** We try syntactic equality before checking the graph. *) *)
(*   Definition check_leq `{checker_flags} s s' := *)
(*     negb check_univs || Universe.equal s s' || check_leq0 s s'. *)

(*   Definition check_eq `{checker_flags} s s' := *)
(*     negb check_univs || Universe.equal s s' || (check_leq0 s s' && check_leq0 s' s). *)

(*   Definition check_eq_instance `{checker_flags} u v := *)
(*     Instance.equal_upto check_eq_level u v. *)

(* End BellmanFord. *)


(* Section Specif. *)
(*   Conjecture no_universe_inconsistency_ok : forall φ, reflect (well_founded (R φ)) (no_universe_inconsistency φ). *)

(*   Local Existing Instance default_checker_flags. *)

(*   (* TODO: lower level conjecture *) *)
(*   Conjecture check_leq_specif *)
(*     : forall ctrs φ (e : make_graph ctrs = Some φ) u1 u2, reflect (leq_universe ctrs u1 u2) (check_leq φ u1 u2). *)

(*   Conjecture check_eq_specif *)
(*     : forall ctrs φ (e : make_graph ctrs = Some φ) u1 u2, reflect (eq_universe ctrs u1 u2) (check_eq φ u1 u2). *)
(* End Specif. *)

(*   (* Definition check_eq_refl `{checker_flags} u : check_eq φ u u = true. *) *)
(*   (*   unfold check_eq; destruct check_univs; cbn; [|reflexivity]. *) *)

(*   (* Conjecture eq_universe_instance_refl : forall `{checker_flags} u, eq_universe_instance u u = true. *) *)
(*   (* Conjecture eq_universe_leq_universe : forall `{checker_flags} x y, *) *)
(*   (*     eq_universe x y = true -> leq_universe x y = true. *) *)
(*   (* Conjecture leq_universe_product_l : forall `{checker_flags} s1 s2, *) *)
(*   (*     leq_universe s1 (Universe.sort_of_product s1 s2) = true. *) *)
(*   (* Conjecture leq_universe_product_r : forall `{checker_flags} s1 s2, *) *)
(*   (*     leq_universe s2 (Universe.sort_of_product s1 s2) = true. *) *)




(*     (* Inductive super_result := *) *)
(*     (* | SuperSame (_ : bool) *) *)
(*     (* (* The level expressions are in cumulativity relation. boolean *) *)
(*     (*        indicates if left is smaller than right?  *) *) *)
(*     (* | SuperDiff (_ : comparison). *) *)
(*     (* (* The level expressions are unrelated, the comparison result *) *)
(*     (*        is canonical *) *) *)

(*     (* (** [super u v] compares two level expressions, *) *)
(*     (*    returning [SuperSame] if they refer to the same level at potentially different *) *)
(*     (*    increments or [SuperDiff] if they are different. The booleans indicate if the *) *)
(*     (*    left expression is "smaller" than the right one in both cases. *) *) *)
(*     (* Definition super (x y : t) : super_result := *) *)
(*     (*   match Level.compare (fst x) (fst y) with *) *)
(*     (*   | Eq => SuperSame (bool_lt' (snd x) (snd y)) *) *)
(*     (*   | cmp => *) *)
(*     (*       match x, y with *) *)
(*     (*       | (l, false), (l', false) => *) *)
(*     (*         match l, l' with *) *)
(*     (*         | Level.lProp, Level.lProp => SuperSame false *) *)
(*     (*         | Level.lProp, _ => SuperSame true *) *)
(*     (*         | _, Level.lProp => SuperSame false *) *)
(*     (*         | _, _ => SuperDiff cmp *) *)
(*     (*         end *) *)
(*     (*       | _, _ => SuperDiff cmp *) *)
(*     (*       end *) *)
(*     (*   end. *) *)


(*   (* Fixpoint merge_univs (fuel : nat) (l1 l2 : list Expr.t) : list Expr.t := *) *)
(*   (*   match fuel with *) *)
(*   (*   | O => l1 *) *)
(*   (*   | S fuel => match l1, l2 with *) *)
(*   (*              | [], _ => l2 *) *)
(*   (*              | _, [] => l1 *) *)
(*   (*              | h1 :: t1, h2 :: t2 => *) *)
(*   (*                match Expr.super h1 h2 with *) *)
(*   (*                | Expr.SuperSame true (* h1 < h2 *) => merge_univs fuel t1 l2 *) *)
(*   (*                | Expr.SuperSame false => merge_univs fuel l1 t2 *) *)
(*   (*                | Expr.SuperDiff Lt (* h1 < h2 is name order *) *) *)
(*   (*                  => h1 :: (merge_univs fuel t1 l2) *) *)
(*   (*                | _ => h2 :: (merge_univs fuel l1 t2) *) *)
(*   (*                end *) *)
(*   (*              end *) *)
(*   (*   end. *) *)



(* (* (* The monomorphic levels are > Set while polymorphic ones are >= Set. *) *) *)
(* (* Definition add_node (l : Level.t) (G : t) : t *) *)
(* (*   := let levels := LevelSet.add l (fst G) in *) *)
(* (*      let constraints := *) *)
(* (*          match l with *) *)
(* (*          | Level.lProp | Level.lSet => snd G (* supposed to be yet here *) *) *)
(* (*          | Level.Var _ => ConstraintSet.add (Level.set, ConstraintType.Le, l) (snd G) *) *)
(* (*          | Level.Level _ => ConstraintSet.add (Level.set, ConstraintType.Lt, l) (snd G) *) *)
(* (*          end in *) *)
(* (*      (levels, constraints). *) *)

(* (* Definition add_constraint (uc : univ_constraint) (G : t) : t *) *)
(* (*   := let '((l, ct),l') := uc in *) *)
(* (*      (* maybe useless if we always add constraints *) *)
(* (*         in which the universes are declared *) *) *)
(* (*      let G := add_node l (add_node l' G) in *) *)
(* (*      let constraints := ConstraintSet.add uc (snd G) in *) *)
(* (*      (fst G, constraints). *) *)

(* (* Definition repr (uctx : universe_context) : UContext.t := *) *)
(* (*   match uctx with *) *)
(* (*   | Monomorphic_ctx c => c *) *)
(* (*   | Polymorphic_ctx c => c *) *)
(* (*   | Cumulative_ctx c => CumulativityInfo.univ_context c *) *)
(* (*   end. *) *)

(* (* Definition add_global_constraints (uctx : universe_context) (G : t) : t *) *)
(* (*   := match uctx with *) *)
(* (*      | Monomorphic_ctx (inst, cstrs) => *) *)
(* (*        let G := List.fold_left (fun s l => add_node l s) inst G in *) *)
(* (*        ConstraintSet.fold add_constraint cstrs G *) *)
(* (*      | Polymorphic_ctx _ => G *) *)
(* (*      | Cumulative_ctx _ => G *) *)
(* (*      end. *) *)


