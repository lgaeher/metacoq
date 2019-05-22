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

  (* Definition finite_pos (n : t) := is_finite n /\ is_pos n. *)

  Definition eq_0_max (n m : t)
    : max n m = Some 0 -> n = Some 0 \/ m = Some 0.
  Proof.
    destruct n, m; cbn; intro H; try discriminate;
    apply some_inj in H.
    left. f_equal; lia.
    left. now f_equal.
    right. now f_equal.
  Qed.
  Definition eq_0_add (n m : t)
    : add n m = Some 0 -> n = Some 0 /\ m = Some 0.
  Proof.
    destruct n, m; cbn; intro H; try discriminate.
    apply some_inj in H; split; f_equal; lia.
  Qed.

  Definition eq_max (n m k : t) : max n m = k -> n = k \/ m = k.
    destruct n, m; cbn; intros []; intuition.
    destruct (eq_max n n0 _ eq_refl); intuition.
  Qed.
End Nbar.

(* Definition wf_implies {A} (R R' : relation A) (H : inclusion _ R R') *)
(*   : well_founded R' -> well_founded R. *)
(* Proof. *)
(*   intros HR x; specialize (HR x). *)
(*   induction HR. *)
(*   constructor. unfold inclusion in H. *)
(*   firstorder. *)
(* Qed. *)


Module WeightedGraph (V : UsualDecidableType).
  Module VSet := MSets.MSetWeakList.Make V.
  (* todo: remove if unused *)
  Module VSetFact := WFactsOn V VSet.
  Module VSetProp := WPropertiesOn V VSet.
  Module Edge.
    Definition t := (V.t * nat * V.t)%type.
    Definition eq (e1 e2 : t) : Prop :=
      let '(x1, n1, y1) := e1 in let '(x2, n2, y2) := e2 in
      V.eq x1 x2 /\ n1 = n2 /\ V.eq y1 y2.
    Definition eq_equiv : RelationClasses.Equivalence eq.
    Admitted.
    Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
      intros [[x1 n1] y1] [[x2 n2] y2]; cbn.
      destruct (V.eq_dec x1 x2). destruct (V.eq_dec y1 y2). 
      destruct (Peano_dec.eq_nat_dec n1 n2).
      left. intuition.
      all: right; intuition.
    Defined.
  End Edge.
  Module EdgeSet:= MSets.MSetWeakList.Make Edge.

  Definition t := (VSet.t * EdgeSet.t * V.t)%type.

  Let V (G : t) := fst (fst G).
  Let E (G : t) := snd (fst G).
  Let s (G : t) := snd G.

  Definition labelling := V.t -> nat.

  Section graph.
    Context (G : t).

    Definition R (x y : V.t) := exists n, EdgeSet.In (x, n, y) (E G).

    Definition Rs := clos_refl_trans _ R.

    Instance Rs_refl : Reflexive Rs := rt_refl _ _.
    Instance Rs_trans : Transitive Rs := rt_trans _ _.

    Definition invariants :=
      (* E ⊆ V × V *)
      (forall e, EdgeSet.In e (E G)
            -> VSet.In (fst (fst e)) (V G) /\ VSet.In (snd e) (V G))
      (* s ∈ V *)
      /\  VSet.In (s G) (V G)
      (* s is a source *)
      /\ (forall x, VSet.In x (V G) -> Rs (s G) x).

    Definition add_node x : t :=
      (VSet.add x (V G), (E G), (s G)).

    Definition add_edge e : t :=
      (VSet.add (fst (fst e)) (VSet.add (snd e) (V G)), EdgeSet.add e (E G), (s G)).


    Definition R0 (x y : V.t) := EdgeSet.In (x, 0, y) (E G).

    (* paths of weight 0 *)
    Definition R0s := clos_refl_trans _ R0.

    Instance R0s_refl : Reflexive R0s := rt_refl _ _.
    Instance R0s_trans : Transitive R0s := rt_trans _ _.

    (* paths with one positive edge *)
    Definition R1 (x y : V.t) :=
      exists x0 y0 n, R0s x x0 /\ EdgeSet.In (x0, S n, y0) (E G) /\ R0s y0 y.

    Definition acyclic := well_founded R1.

    Definition R1s := clos_trans _ R1.

    Instance R1s_trans : Transitive R1s := t_trans _ _.

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
      forall e, EdgeSet.In e (E G) -> l (fst (fst e)) + (snd (fst e)) <= l (snd e).

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
                 (fun e => match V.eq_dec (fst (fst e)) x, V.eq_dec (snd e) y with
                     | left _, left _ => true
                     | _, _ => false
                     end)
                 (EdgeSet.elements (E G)) in (* edges x --> y *)
      List.map (snd ∘ fst) L.

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
      unfold V.eq. intuition; cbn in *.
      all: destruct (V.eq_dec x' x); destruct (V.eq_dec y' y);
        try discriminate; intuition.
    Qed.


    (* l is the list of authorized intermediate nodes *)
    (* d (a::l) x y = max (d l x y)  (d l x a + d l a y) *)
    Definition d'0 (l : list V.t) (x y : V.t) : Nbar.t.
    Proof.
      revert x y; induction l; intros x y.
      - refine (match get_edges x y with
                | nil => if V.eq_dec x y then Some 0 else None
                | x :: l => Some (List.fold_left max l x)
                end).
      - refine (Nbar.max (IHl x y) (Nbar.add (IHl x a) (IHl a y))).
        (* refine (match IHl x y, IHl x a, IHl a y with *)
        (*         | Some d1, Some d2, Some d3 => Some (max d1 (d2 + d3)) *)
        (*         | Some d1, None, _ *)
        (*         | Some d1, _, None => Some d1 *)
        (*         | None, Some d2, Some d3 => Some (d2 + d3) *)
        (*         | _, _, _ => None *)
        (*         end). *)
    Defined.

    Definition d' := d'0 (VSet.elements (V G)).

    (* (* l is the list of authorized nodes (intermediate and source) *) *)
    (* Definition R' (l : list V.t) (x y : V.t) *)
    (*   := InA V.eq x l /\ exists n, EdgeSet.In (x, n, y) (E G). *)

    (* Definition R's l := clos_refl_trans _ (R' l). *)

    (* Instance R's_refl l : Reflexive (R's l) := rt_refl _ _. *)
    (* Instance R's_trans l : Transitive (R's l) := rt_trans _ _. *)

    (* Definition R'' l x y := *)
    (*   (exists z n, EdgeSet.In (x, n, z) (E G) /\ R's l z y) \/ V.eq x y. *)

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

    (* Definition R'_ok x y : R x y <-> R' (VSet.elements (V G)) x y. *)
    (* Proof. *)
    (*   split. *)
    (*   - induction 1. pose proof (proj1 HI _ H) as HH; cbn in HH. *)
    (*     repeat split; try now apply VSetProp.FM.elements_1. *)
    (*     eexists; eassumption. *)
    (*   - unfold R', R; intuition. *)
    (* Defined. *)

    (* Definition R's_ok x y : Rs x y <-> R's (VSet.elements (V G)) x y. *)
    (* Proof. *)
    (*   split. *)
    (*   - induction 1. constructor. now apply R'_ok. *)
    (*     apply rt_refl. *)
    (*     eapply rt_trans; eassumption. *)
    (*   - induction 1. constructor. now apply R'_ok. *)
    (*     apply rt_refl. *)
    (*     eapply rt_trans; eassumption. *)
    (* Defined. *)

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

    Lemma d'_ok1 l : forall x y, (Nbar.is_pos (d'0 l x y)) -> R1s x y.
    Proof.
      induction l; intros x y.
      - simpl. case_eq (get_edges x y).
        intros _.
        case_eq (V.eq_dec x y); intros e H H1; inversion H1.
        intros n l H H0.
        set (m := fold_left max l n) in *.
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
        set (m := fold_left max l n) in *; clearbody m.
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


    Lemma d'_ok0' (HG : forall x, ~ R1s x x) l
      : forall x y, R'' l x y -> Nbar.is_finite (d'0 l x y).
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

    Lemma fold_max_le n m l (H : n <= m \/ Exists (le n) l)
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

    Import Nbar.

    Definition max_lub n m p : (n <= p -> m <= p -> max n m <= p)%nbar.
    Admitted.

    Definition add_max_distr_r n m p
      : (max (n + p) (m + p) = max n m + p)%nbar.
    Admitted.

    Definition max_le' n m p
      : (p <= n \/ p <= m -> p <= max n m)%nbar.
    Admitted.

    Definition plus_le_compat_l n m p : (n <= m -> p + n <= p + m)%nbar.
    Admitted.

    Definition add_assoc n m p : (n + (m + p) = n + m + p)%nbar.
    Admitted.

    Definition add_O_r n : (n + Some 0 = n)%nbar.
    Admitted.

    Definition max_idempotent n : (max n n = n)%nbar.
    Admitted.

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
        + subst. rewrite (d'_ok2 HG), add_O_r, max_idempotent.
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
        simple refine (let H1 := d'_ok0' HG (VSet.elements (V G)) (s G) x _ in _);
          [|destruct H1 as [n1 H1]].
        apply R''_ok. apply HI.
        apply proj1 in HI. specialize (HI _ He); apply HI.
        simple refine (let H2 := d'_ok0' HG (VSet.elements (V G)) (s G) y _ in _);
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







    Conjecture R1_dec : forall x y, {R1 x y} + {~ R1 x y}.
    Conjecture Rs_dec : forall x y, {Rs x y} + {~ Rs x y}.

    Import MonadNotation.
  Fixpoint monad_fold_left {T} {M : Monad T} {A B} (g : T A -> B -> T A)
           (l : list B) (x : T A) : T A
    := match l with
       | nil => x
       | y :: l => monad_fold_left g l (g x y)
       end.

    (* biggest distance from s to x *)
    (* None iff no path from s to x *)
    Definition d (s x : V.t) (H1 : Acc R1 x) : option nat.
      induction H1 as [x H1 d].
      simple refine (let preds := filter_pack (fun y => R1 y x) _
                                              (VSet.elements (V G)) in _).
      - intro y; cbn. apply R1_dec.
      - refine (monad_fold_left _ preds None).
        refine (fun n X => match n, d X.1 X.2 with
                        | Some n, Some m => Some (max n m)
                        | Some n, None => Some n
                        | None, Some m => Some m
                        | None, None => None
                        end).
    Defined.

    (* (* biggest distance from s to x *) *)
    (* Definition d (s x : V.t) (H1 : Acc R1 x) (H2 : Rs s x) : nat. *)
    (*   induction H1 as [x H1 d]. *)
    (*   simple refine (let preds := filter_pack (fun y => Rs s y /\ R1 y x) _ *)
    (*                                           (VSet.elements (V G)) in _). *)
    (*   - intro y; cbn. *)
    (*     refine (match Rs_dec s y, R1_dec y x with *)
    (*             | left _, left _ => left _ *)
    (*             | _, _ => right _ *)
    (*             end); intuition. *)
    (*   - exact (List.fold_left (fun n X => max n (d X.1 (proj2 X.2) (proj1 X.2))) *)
    (*                           preds 0). *)
    (* Defined. *)

    Definition d_labelling (HG : acyclic) : labelling
      := fun x => option_get 0 (d (s G) x (HG _)).


    Remark toto : forall x y,
        (exists k, forall l, correct_labelling l -> (l x + k <= l y))
        <-> (forall l, correct_labelling l -> (l x <= l y)).
    Proof.
      intros x y; split.
      intros [k H] l Hl. specialize (H _ Hl); Lia.lia.
      intros H; exists 0. intros l Hl. specialize (H _ Hl); Lia.lia.
    Defined.

    Lemma d_ok (HG : acyclic) : forall k x y,
        (forall l, correct_labelling l -> (l x + k <= l y))
        <-> on_Some (le k) (d x y (HG y)).
    Admitted.

    (* Corollary d_ok' (HG : acyclic) l (Hl : correct_labelling l) x y p *)
    (*   : l x + d x y (HG y) p <= l y. *)
    (* Proof. *)
    (*   apply (d_ok HG (d x y (HG y) p) x y). exists p; constructor. *)
    (*   assumption. *)
    (* Defined. *)

    Lemma d_labelling_ok HG
      : correct_labelling (d_labelling HG).
    Proof.
      split; unfold d_labelling.
      - 
        (* destruct (HG (s G)). simpl. *)
        (* match goal with *)
        (* | |- fold_left _ ?l _ = _ => set l *)
        (* end. *)
        (* destruct l. reflexivity. *)
        (* apply False_rect. *)
        (* clear -a s0. destruct s0 as [x [H1 H2]]. specialize (a x H2). *)
        admit.
      - intros [[e1 n] e2] He; cbn.
        destruct (Rs_dec (s G) e1); [|unfold invariants in HI; firstorder].
        destruct (Rs_dec (s G) e2); [|unfold invariants in HI; firstorder].
        pose proof (proj1 (d_ok HG (d (s G) e1 (HG e1) r + n) (s G) e2)).
        destruct H.
        + intros l Hl.
          pose proof (proj2 Hl _ He); cbn in H.
          pose proof (d_ok' HG l Hl (s G) e2 r0).
          Lia.lia.
          assert


        unfold d.

    Admitted.



    Lemma acyclic_labelling : acyclic <-> exists l, correct_labelling l.
    Proof.
      split. intro; eexists; now unshelve eapply d_labelling_ok.
      intros [l Hl]. eapply Wf_nat.well_founded_lt_compat.
      exact (correct_labelling_R _ Hl).
    Qed.

  End graph.


  Definition path (E : EdgeSet.t) : V.t -> V.t -> bool.
    induction (EdgeSet.elements E) as [|e l path].
    exact (fun x y => if V.eq_dec x y then true else false).
    exact (fun x y => path x y || (path x (fst (fst e)) && path (snd e) y)).
  Defined.

  Conjecture path_spec : forall {G} x y, reflect (Rs G x y) (path (snd (fst G)) x y).

  
  Lemma add_node_invariants {G} (HG : invariants G) {x} (Hx : R G (s G) x)
    : invariants (add_node G x).
  Proof.
    unfold invariants in *.
  Admitted.

  Lemma add_edge_invariants {G} (HG : invariants G) {e}
        (He : R G (s G) (fst (fst e)))
    : invariants (add_edge G e).
  Proof.
    unfold invariants in *.
  Admitted.

End WeightedGraph.









(* Definition valuation_of_graph φ (H: well_founded (R φ)) : valuation. *)
(* Proof. *)
(*   pose (V := fst φ). pose (E := snd φ). *)
(*   unshelve econstructor. *)
(*   refine (fun s => if VerticeSet.mem (Level s) V then BinIntDef.Z.to_pos (option_get 1 (d φ lSet (Level s) (H _))) else 1%positive). *)
(*   refine (fun n => if VerticeSet.mem (Var n) V then Z.to_nat (option_get 0 (d φ lSet (Var n) (H _))) else 0%nat). *)
(* Defined. *)

(* Lemma Acc_ok1 ctrs : (exists φ, make_graph ctrs = Some φ /\ well_founded (R φ)) -> consistent ctrs. *)
(* Proof. *)
(*   intros [φ [H1 H2]]. *)
(*   exists (valuation_of_graph φ H2). *)
(*   unfold satisfies. intros [[l1 []] l2] Huc; constructor. *)
(*   - destruct l1, l2. *)
(*         * admit. *)
(*         * admit. *)
(*         * admit. *)
(*         * admit. *)
(*         * admit. *)
(*         * admit. *)
(*         * admit. *)
(*         * admit. *)
(*         * admit. *)
(*         * admit. *)
(*         * cbn. *)
(*  assert (e: d φ lSet (Level s) (H2 (Level s)) < d φ lSet (Level s0) (H2 (Level s0))). *)
 

(* assert (d φ lSet l1 < d φ lSet l2). *)


(*   unfold satisfies0. intros uc Huc. *)
  

(*   revert φ H1 H2. *)
(*   induction ctrs using ConstraintSetProp.set_induction; *)
(*     intros φ H1 H2. *)
(*   - intros x Hx. apply False_rect. *)
(*     apply (ConstraintSetFact.empty_iff x). *)
(*     eapply ConstraintSetFact.In_m. reflexivity. *)
(*     2: eassumption. symmetry. *)
(*     now apply ConstraintSetProp.empty_is_empty_1. *)
(*   - assert (satisfies0 (valuation_of_graph φ H2) x) . { *)
(*       assert (Hc : ConstraintSet.In x ctrs2). admit. (* ok *) *)
(*       clear H H0 IHctrs1 ctrs1. *)
(*       destruct x as [[l1 []] l2]; econstructor. *)
(*       + destruct l1, l2. *)
(*         * admit. *)
(*         * admit. *)
(*         * admit. *)
(*         * admit. *)
(*         * admit. *)
(*         * admit. *)
(*         * admit. *)
(*         * admit. *)
(*         * admit. *)
(*         * admit. *)
(*         * cbn. assert (e: VerticeSet.mem (Level s) (fst φ) = true). admit. *)
(*           rewrite e. *)
(*           assert ((d φ lSet (Level s) (H2 (Level s))) < (d φ lSet (Level s) (H2 (Level s0)))). *)

(* } *)

(*  unfold make_graph in H1. *)
(*     unfold edges_of_constraints in H1. *)
(*     rewrite ConstraintSetProp.fold_1b in H1. *)
(*     unfold add_nodes_of_constraints in H1. *)
(*     rewrite ConstraintSetProp.fold_1b in H1. *)


(* Definition is_Some {A} (x : option A) := exists a, x = Some a. *)

(* Conjecture Acc_ok : forall ctrs, consistent ctrs <-> exists φ, make_graph ctrs = Some φ /\ well_founded (R φ). *)

(* Conjecture d_ok   : forall ctrs φ (e : make_graph ctrs = Some φ) (H : well_founded (R φ)) l l', *)
(*     (exists k, forall v, satisfies v ctrs -> (val0 v (vtl l) <= (val0 v (vtl l')) + k)%Z) *)
(*     <-> is_Some (d φ l l' (H _)). *)

(* Conjecture d_ok2  : forall ctrs φ (e : make_graph ctrs = Some φ) (H : well_founded (R φ)) l l' k, *)
(*     (forall v, satisfies v ctrs -> (val0 v (vtl l) <= (val0 v (vtl l')) + k)%Z) *)
(*     <-> (forall k', d φ l l' (H _) = Some k' -> k >= k'). *)




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
