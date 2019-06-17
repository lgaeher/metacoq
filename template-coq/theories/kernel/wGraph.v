Require Import Peano_dec Nat Bool List Structures.Equalities Lia
        MSets.MSetList MSetFacts MSetProperties.
Require Import ssrbool ssrfun.
 From Template Require Import utils monad_utils.

 Axiom myadmit : forall {A}, A.

Inductive on_Some {A} (P : A -> Prop) : option A -> Prop :=
| on_some : forall x, P x -> on_Some P (Some x).

Lemma on_Some_spec {A} (P : A -> Prop) z :
  on_Some P z <-> exists x, z = Some x /\ P x.
Proof.
  split. intros []. now eexists.
  intros [? [e ?]]. subst. now constructor.
Qed.

Inductive on_Some_or_None {A} (P : A -> Prop) : option A -> Prop :=
| on_some' : forall x, P x -> on_Some_or_None P (Some x)
| or_none : on_Some_or_None P None.

Lemma on_Some_or_None_spec {A} (P : A -> Prop) z :
  on_Some_or_None P z <-> z = None \/ on_Some P z.
Proof.
  split. intros []. right; now constructor. left; reflexivity.
  intros [|[]]; subst; now constructor.
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

  Arguments max _ _ : simpl nomatch.
  Arguments add _ _ : simpl nomatch.
  Arguments le _ _ : simpl nomatch.

  Infix "+" := add : nbar_scope.
  Infix "<=" := le : nbar_scope.
  Delimit Scope nbar_scope with nbar.
  Bind Scope nbar_scope with t.

  Local Open Scope nbar_scope.

  Instance le_refl : Reflexive le.
  Proof.
    intro x; destruct x; cbn; reflexivity.
  Defined.

  Instance le_trans : Transitive le.
  Proof.
    intros [x|] [y|] [z|]; cbn; intuition.
  Defined.

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

  Definition plus_le_compat n m p q : n <= m -> p <= q -> n + p <= m + q.
  Proof.
    destruct n, m, p, q; cbn; intuition.
  Defined.

  Definition max_idempotent n : max n n = n.
  Proof.
    destruct n; try reflexivity; cbn.
    now rewrite PeanoNat.Nat.max_idempotent.
  Defined.

  Lemma eq_max n m k (H : max n m = k) : n = k \/ m = k.
  Proof.
    destruct n, m, k; cbn in H.
    apply some_inj in H. apply eq_max in H.
    all: try discriminate; intuition.
  Qed.

  Lemma fold_max_In n m l (H : fold_left max l n = m)
    : n = m \/ In m l.
  Proof.
    revert n H; induction l; cbn; intros n H.
    intuition.
    apply IHl in H.
    apply or_assoc. destruct H; [left|now right].
    now apply eq_max.
  Qed.

  Lemma fold_max_le n m l (H : n <= m \/ Exists (le n) l)
    : n <= fold_left max l m.
  Proof.
    revert m H; induction l; cbn in *; intros m [H|H].
    assumption. inversion H.
    eapply IHl. left. apply max_le'; now left.
    eapply IHl. inversion_clear H.
    left. apply max_le'; now right.
    right; assumption.
  Qed.

  Lemma fold_max_le' n m l (H : In n (m :: l))
    : n <= fold_left max l m.
  Proof.
    apply fold_max_le. destruct H.
    left; subst; reflexivity.
    right. apply Exists_exists.
    eexists. split. eassumption. reflexivity.
  Qed.

End Nbar.


Module WeightedGraph (V : UsualOrderedType).
  Module VSet := MSetList.Make V.
  (* todo: remove if unused *)
  Module VSetFact := WFactsOn V VSet.
  Module VSetProp := WPropertiesOn V VSet.
  Module Edge.
    Definition t := (V.t * nat * V.t)%type.
    Definition eq : t -> t -> Prop := eq.
    Definition eq_equiv : RelationClasses.Equivalence eq := _.

    Definition lt : t -> t -> Prop :=
      fun '(x, n, y) '(x', n', y') => (V.lt x x') \/ (V.eq x x' /\ n < n')
                                   \/ (V.eq x x' /\ n = n' /\ V.lt y y').
    Definition lt_strorder : StrictOrder lt.
      split.
      - intros [[x n] y] H; cbn in H. intuition.
        all: eapply V.lt_strorder; eassumption.
      - intros [[x1 n1] y1] [[x2 n2] y2] [[x3 n3] y3] H1 H2; cbn in *.
        pose proof (StrictOrder_Transitive x1 x2 x3) as T1.
        pose proof (StrictOrder_Transitive y1 y2 y3) as T2.
        pose proof (@eq_trans _ n1 n2 n3) as T3.
        unfold VSet.E.lt in *. unfold V.eq in *.
        destruct H1 as [H1|[[H1 H1']|[H1 [H1' H1'']]]];
          destruct H2 as [H2|[[H2 H2']|[H2 [H2' H2'']]]]; subst; intuition.
    Qed.
    Definition lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
      intros x x' H1 y y' H2. now subst.
    Qed.
    Definition compare : t -> t -> comparison
      := fun '(x, n, y) '(x', n', y') => match V.compare x x' with
                                      | Lt => Lt
                                      | Gt => Gt
                                      | Eq => match PeanoNat.Nat.compare n n' with
                                             | Lt => Lt
                                             | Gt => Gt
                                             | Eq => V.compare y y'
                                             end
                                      end.
    Definition compare_spec :
      forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
      intros [[x1 n1] y1] [[x2 n2] y2]; cbn.
      pose proof (V.compare_spec x1 x2) as H1.
      destruct (V.compare x1 x2); cbn in *; inversion_clear H1.
      2-3: constructor; intuition.
      subst. pose proof (PeanoNat.Nat.compare_spec n1 n2) as H2.
      destruct (n1 ?= n2); cbn in *; inversion_clear H2.
      2-3: constructor; intuition.
      subst. pose proof (V.compare_spec y1 y2) as H3.
      destruct (V.compare y1 y2); cbn in *; inversion_clear H3;
        constructor; subst; intuition.
    Defined.
    
    Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
      unfold eq. decide equality. apply V.eq_dec.
      decide equality. apply PeanoNat.Nat.eq_dec. apply V.eq_dec.
    Defined.
    Definition eqb : t -> t -> bool := fun x y => match compare x y with
                                          | Eq => true
                                          | _ => false
                                          end.
  End Edge.
  Module EdgeSet:= MSets.MSetList.Make Edge.
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

    Definition add_node x : t :=
      (VSet.add x (V G), (E G), (s G)).

    Definition add_edge e : t :=
      (VSet.add e..s (VSet.add e..t (V G)), EdgeSet.add e (E G), (s G)).

    Definition Edges x y := ∑ n, EdgeSet.In (x, n, y) (E G).

    Inductive Paths : V.t -> V.t -> Type :=
    | paths_refl x : Paths x x
    | paths_step x y z : Edges x y -> Paths y z -> Paths x z.

    Arguments paths_step {x y z} e p.

    Fixpoint weight {x y} (p : Paths x y) :=
      match p with
      | paths_refl x => 0
      | paths_step x y z e p => e..1 + weight p
      end.

    Fixpoint nodes {x y} (p : Paths x y) : VSet.t :=
      match p with
      | paths_refl x => VSet.empty
      | paths_step x y z e p => VSet.add x (nodes p)
      end.

    Fixpoint concat {x y z} (p : Paths x y) : Paths y z -> Paths x z :=
      match p with
      | paths_refl _ => fun q => q
      | paths_step _ _ _ e p => fun q => paths_step e (concat p q)
      end.

    Fixpoint length {x y} (p : Paths x y) :=
      match p with
      | paths_refl x => 0
      | paths_step x y z e p => S (length p)
      end.

    Global Instance Paths_refl : CRelationClasses.Reflexive Paths := paths_refl.
    Global Instance Paths_trans : CRelationClasses.Transitive Paths := @concat.


    Definition invariants :=
      (* E ⊆ V × V *)
      (forall e, EdgeSet.In e (E G) -> VSet.In e..s (V G) /\ VSet.In e..t (V G))
      (* s ∈ V *)
      /\  VSet.In (s G) (V G)
      (* s is a source *)
      /\ (forall x, VSet.In x (V G) -> ∥ Paths (s G) x ∥).

    Context (HI : invariants).


    Definition PosPaths x y := exists p : Paths x y, weight p > 0.

    Definition acyclic_no_loop := forall x (p : Paths x x), weight p = 0.

    Definition acyclic_no_loop' := forall x, ~ (PosPaths x x).

    Fact acyclic_no_loop_loop' : acyclic_no_loop <-> acyclic_no_loop'.
    Proof.
      unfold acyclic_no_loop, acyclic_no_loop', PosPaths.
      split.
      - intros H x [p HH]. specialize (H x p); lia.
      - intros H x p.
        destruct (PeanoNat.Nat.eq_0_gt_0_cases (weight p));
          firstorder.
    Qed.





    Definition DisjointAdd x s s' := VSetProp.Add x s s' /\ ~ VSet.In x s.

    Inductive SimplePaths : VSet.t -> V.t -> V.t -> Type :=
    | spaths_refl s x : SimplePaths s x x
    | spaths_step s s' x y z : DisjointAdd x s s' -> Edges x y
                               -> SimplePaths s y z -> SimplePaths s' x z.

    Arguments spaths_step {s s' x y z} H e p.

    Global Instance SimplePaths_refl s : CRelationClasses.Reflexive (SimplePaths s)
      := spaths_refl s.

    Fixpoint to_paths {s x y} (p : SimplePaths s x y) : Paths x y :=
      match p with
      | spaths_refl _ x => paths_refl x
      | spaths_step _ _ x y z _ e p => paths_step e (to_paths p)
      end.

    Fixpoint sweight {s x y} (p : SimplePaths s x y) :=
      match p with
      | spaths_refl _ _ => 0
      | spaths_step _ _ x y z _ e p => e..1 + sweight p
      end.

    Lemma sweight_weight {s x y} (p : SimplePaths s x y)
      : sweight p = weight (to_paths p).
    Proof.
      induction p; cbn; lia.
    Qed.

    Fixpoint is_simple {x y} (p : Paths x y) :=
      match p with
      | paths_refl x => true
      | paths_step x y z e p => negb (VSet.mem x (nodes p)) && is_simple p
      end.

    Program Fixpoint to_simple {x y} (p : Paths x y) (Hp : is_simple p = true)
            {struct p} : SimplePaths (nodes p) x y :=
      match p with
      | paths_refl x => spaths_refl _ _
      | paths_step x y z e p => spaths_step _ e (to_simple p _)
      end.
    Next Obligation.
      split. eapply VSetProp.Add_add.
      apply (JMeq.JMeq_congr is_simple) in Heq_p.
      rewrite Hp in Heq_p. cbn in Heq_p; apply andb_prop, proj1 in Heq_p.
      now apply ssrbool.negbTE, VSetFact.not_mem_iff in Heq_p.
    Defined.
    Next Obligation.
      apply (JMeq.JMeq_congr is_simple) in Heq_p.
      rewrite Hp in Heq_p. cbn in Heq_p; now apply andb_prop, proj2 in Heq_p.
    Defined.


    (* Lemma DisjointAdd_add {s s' x y} (H : DisjointAdd x s s') (H' : x <> y) *)
    (*   : DisjointAdd x (VSet.add y s) (VSet.add y s'). *)
    (* Proof. *)
    (*   repeat split. 2: intros [H0|H0]. *)
    (*  - intro H0. apply VSet.add_spec in H0. *)
    (*    destruct H0 as [H0|H0]. *)
    (*    right; subst; apply VSet.add_spec; left; reflexivity. *)
    (*    apply H in H0. destruct H0 as [H0|H0]; [left; assumption |right]. *)
    (*    apply VSet.add_spec; right; assumption. *)
    (*  - subst. apply VSet.add_spec; right. apply H; left; reflexivity. *)
    (*  - apply VSet.add_spec in H0; apply VSet.add_spec; destruct H0 as [H0|H0]. *)
    (*    left; assumption. right. apply H. right; assumption. *)
    (*  - intro H0. apply VSet.add_spec in H0; destruct H0 as [H0|H0]. *)
    (*    contradiction. now apply H. *)
    (* Qed. *)

    Lemma DisjointAdd_add1 {s0 s1 s2 x y}
          (H1 : DisjointAdd x s0 s1) (H2 : DisjointAdd y s1 s2)
      : DisjointAdd x (VSet.add y s0) s2.
    Proof.
      split.
      intro z; split; intro Hz. 2: destruct Hz as [Hz|Hz].
      - apply H2 in Hz. destruct Hz as [Hz|Hz]; [right|].
        now apply VSetFact.add_1.
        apply H1 in Hz. destruct Hz as [Hz|Hz]; [left; assumption|right].
        now apply VSetFact.add_2.
      - apply H2. right; apply H1. now left.
      - apply H2. apply VSet.add_spec in Hz.
        destruct Hz as [Hz|Hz]; [now left|right].
        apply H1. now right.
      - intro Hx. apply VSet.add_spec in Hx.
        destruct Hx as [Hx|Hx].
        subst. apply H2. apply H1. now left.
        now apply H1.
    Qed.

    Lemma DisjointAdd_add2 {s x} (H : ~ VSet.In x s)
      : DisjointAdd x s (VSet.add x s).
    Proof.
      split. apply VSetProp.Add_add.
      assumption.
    Qed.

    Lemma DisjointAdd_add3  {s0 s1 s2 x y}
          (H1 : DisjointAdd x s0 s1) (H2 : DisjointAdd y s1 s2)
      : DisjointAdd y s0 (VSet.add y s0).
    Proof.
      apply DisjointAdd_add2. intro H.
      unfold DisjointAdd in *.
      apply H2. apply H1. now right.
    Qed.


    Fixpoint add_end {s x y} (p : SimplePaths s x y)
      : forall {z} (e : Edges y z) {s'} (Hs : DisjointAdd y s s'), SimplePaths s' x z
      := match p with
         | spaths_refl s x => fun z e s' Hs => spaths_step Hs e (spaths_refl _ _)
         | spaths_step s0 s x x0 y H e p
           => fun z e' s' Hs => spaths_step (DisjointAdd_add1 H Hs) e
                                        (add_end p e' (DisjointAdd_add3 H Hs))
         end.

    Lemma weight_add_end {s x y} (p : SimplePaths s x y) {z e s'} Hs
      : sweight (@add_end s x y p z e s' Hs) = sweight p + e..1.
    Proof.
      revert z e s' Hs. induction p.
      - intros; cbn; lia.
      - intros; cbn. rewrite IHp; lia.
    Qed.


    Lemma DisjointAdd_remove {s s' x y} (H : DisjointAdd x s s') (H' : x <> y)
      : DisjointAdd x (VSet.remove y s) (VSet.remove y s').
    Proof.
      repeat split. 2: intros [H0|H0].
     - intro H0. apply VSet.remove_spec in H0.
       destruct H0 as [H0 H1].
       pose proof ((H.1 y0).1 H0) as H2.
       destruct H2; [now left|right].
       apply VSetFact.remove_2; intuition.
     - subst. apply VSet.remove_spec. split; [|assumption].
       apply H.1. left; reflexivity.
     - apply VSet.remove_spec in H0; destruct H0 as [H0 H1].
       apply VSet.remove_spec; split; [|assumption].
       apply H.1. right; assumption.
     - intro H0. apply VSet.remove_spec in H0; destruct H0 as [H0 _].
       apply H; assumption.
    Qed.

   (* Fixpoint split {s x y} (p : SimplePaths s x y) *)
   (*   : SimplePaths (VSet.remove y s) x y * ∑ s', SimplePaths s' y y := *)
   (*    match p with *)
   (*    | spaths_refl s x => (spaths_refl _ x, (VSet.empty; spaths_refl _ x)) *)
   (*    | spaths_step s s' x0 y0 z0 H e p0 *)
   (*      => match V.eq_dec x0 z0 with *)
   (*        | left pp => (eq_rect _ (SimplePaths _ _) (spaths_refl _ _) _ pp, *)
   (*                     (s'; eq_rect _ (fun x => SimplePaths _ x _) *)
   (*                                  (spaths_step H e p0) _ pp)) *)
   (*        | right pp => (spaths_step (DisjointAdd_remove H pp) e (split p0).1, *)
   (*                      (split p0).2) *)
   (*        end *)
   (*    end. *)

    Definition SimplePaths_sub {s s' x y}
      : VSet.Subset s s' -> SimplePaths s x y -> SimplePaths s' x y.
    Proof.
      intros Hs p; revert s' Hs; induction p.
      - reflexivity.
      - intros s'0 Hs. unshelve econstructor.
        exact (VSet.remove x s'0).
        3: eassumption. 2: eapply IHp.
        + split. apply VSetProp.Add_remove.
          apply Hs, d; intuition.
          now apply VSetProp.FM.remove_1.
        + intros u Hu. apply VSetFact.remove_2.
          intro X. apply d. subst; assumption.
          apply Hs, d; intuition.
    Defined.

    Definition weight_SimplePaths_sub {s s' x y} Hs p
      : sweight (@SimplePaths_sub s s' x y Hs p) = sweight p.
    Proof.
      revert s' Hs; induction p; simpl. reflexivity.
      intros s'0 Hs. now rewrite IHp.
    Qed.

    Lemma DisjointAdd_Subset {x s s'}
      : DisjointAdd x s s' -> VSet.Subset s s'.
    Proof.
      intros [H _] z Hz. apply H; intuition.
    Qed.

   Fixpoint split {s x y} (p : SimplePaths s x y)
     : SimplePaths (VSet.remove y s) x y * SimplePaths s y y :=
      match p with
      | spaths_refl s x => (spaths_refl _ x, spaths_refl _ x)
      | spaths_step s s' x0 y0 z0 H e p0
        => match V.eq_dec x0 z0 with
          | left pp => (eq_rect _ (SimplePaths _ _) (spaths_refl _ _) _ pp,
                       eq_rect _ (fun x => SimplePaths _ x _) (spaths_step H e p0) _ pp)
          | right pp => (spaths_step (DisjointAdd_remove H pp) e (split p0).1,
                        SimplePaths_sub (DisjointAdd_Subset H) (split p0).2)
          end
      end.

    Lemma weight_split {s x y} (p : SimplePaths s x y)
      : sweight (split p).1 + sweight (split p).2 = sweight p.
    Proof.
      induction p.
      - reflexivity.
      - simpl. destruct (V.eq_dec x z).
        + destruct e0; cbn. reflexivity.
        + cbn. rewrite weight_SimplePaths_sub; lia.
    Qed.

    Lemma DisjointAdd_remove1 {s x} (H : VSet.In x s)
      : DisjointAdd x (VSet.remove x s) s.
    Proof.
      split.
      - intro z; split; intro Hz. 2: destruct Hz as [Hz|Hz].
        + destruct (V.eq_dec x z). now left.
          right. now apply VSetFact.remove_2.
        + now subst.
        + eapply VSetFact.remove_3; eassumption.
      - now apply VSetFact.remove_1.
    Qed.

    Lemma Add_In {s x} (H : VSet.In x s)
      : VSetProp.Add x s s.
    Proof.
      split. intuition.
      intros []; try subst; assumption.
    Qed.

    Lemma Add_Add {s s' x} (H : VSetProp.Add x s s')
      : VSetProp.Add x s' s'.
    Proof.
      apply Add_In, H. left; reflexivity.
    Qed.


    Lemma simplify_aux1 {s0 s1 s2} (H : VSet.Equal (VSet.union s0 s1) s2)
      : VSet.Subset s0 s2.
    Proof.
      intros x Hx. apply H.
      now apply VSetFact.union_2.
    Qed.
 
    Lemma simplify_aux2 {s0 x} (Hx : VSet.mem x s0 = true)
          {s1 s2}
          (Hs : VSet.Equal (VSet.union s0 (VSet.add x s1)) s2)
      : VSet.Equal (VSet.union s0 s1) s2.
    Proof.
      apply VSet.mem_spec in Hx.
      etransitivity; [|eassumption].
      intro y; split; intro Hy; apply VSet.union_spec;
        apply VSet.union_spec in Hy; destruct Hy as [Hy|Hy].
      left; assumption.
      right; now apply VSetFact.add_2.
      left; assumption.
      apply VSet.add_spec in Hy; destruct Hy as [Hy|Hy].
      left; subst; assumption.
      right; assumption.
    Qed.

    Lemma simplify_aux3 {s0 s1 s2 x}
          (Hs : VSet.Equal (VSet.union s0 (VSet.add x s1)) s2)
      : VSet.Equal (VSet.union (VSet.add x s0) s1) s2.
    Proof.
      etransitivity; [|eassumption].
      etransitivity. eapply VSetProp.union_add.
      symmetry. etransitivity. apply VSetProp.union_sym.
      etransitivity. eapply VSetProp.union_add.
      apply VSetFact.add_m. reflexivity.
      apply VSetProp.union_sym.
    Qed.

    Fixpoint simplify {s x y} (q : Paths y x)
      : forall (p : SimplePaths s x y) {s'},
        VSet.Equal (VSet.union s (nodes q)) s' -> ∑ x', SimplePaths s' x' x' :=
      match q with
      | paths_refl x => fun p s' Hs => (x; SimplePaths_sub (simplify_aux1 Hs) p)
      | paths_step y y' _ e q =>
        fun p s' Hs => match VSet.mem y s as X return VSet.mem y s = X -> _ with
              | true => fun XX => let '(p1, p2) := split p in
                       if 0 <? sweight p2
                       then (y; SimplePaths_sub (simplify_aux1 Hs) p2)
                       else (simplify q (add_end p1 e
                                          (DisjointAdd_remove1 (VSetFact.mem_2 XX)))
                                      (simplify_aux2 XX Hs))
              | false => fun XX => (simplify q (add_end p e
                            (DisjointAdd_add2 ((VSetFact.not_mem_iff _ _).2 XX)))
                                         (simplify_aux3 Hs))
              end eq_refl
      end.


    (* Program Fixpoint simplify {s x y} (q : Paths y x) *)
    (*   : SimplePaths s x y -> ∑ x' s', SimplePaths s' x' x' := *)
    (*   match q with *)
    (*   | paths_refl x => fun p => (x; s; p) *)
    (*   | paths_step y y' _ e q => *)
    (*     fun p => match VSet.mem y s with *)
    (*           | true => let '(p1, p2) := split p in *)
    (*                    if 0 <? sweight (p2..2) then (_; p2) *)
    (*                    else simplify q (@add_end _ _ _ p1 _ e _) *)
    (*           | false => @simplify _ _ _ q (@add_end _ _ _ p _ e _) *)
    (*           end *)
    (*   end. *)
    (* Next Obligation. *)
    (*   apply VSetProp.FM.remove_1; reflexivity. *)
    (* Defined. *)
    (* Next Obligation. *)
    (*   now apply VSetFact.not_mem_iff. *)
    (* Defined. *)

    (* Lemma weight_simplify (HG : acyclic_no_loop) {s x y} q (p : SimplePaths s x y) *)
    (*   : 0 < weight q \/ 0 < sweight p -> 0 < sweight (simplify q p)..2..2. *)
    (* Proof. *)
    (*   revert s p; induction q. *)
    (*   - cbn. intuition. *)
    (*   - intros s p H; cbn in H. simpl. *)
    (*     set (F := proj2 (VSetFact.not_mem_iff s x)); clearbody F. *)
    (*     destruct (VSet.mem x s). *)
    (*     + case_eq (split p); intros p1 p2 Hp. *)
    (*       case_eq (0 <? sweight p2..2); intro eq. *)
    (*       cbn. apply PeanoNat.Nat.leb_le in eq. lia. *)
    (*       eapply IHq. rewrite weight_add_end. *)
    (*       pose proof (weight_split p) as X; rewrite Hp in X. *)
    (*       destruct p2 as  [s' p2]; simpl in *. *)
    (*       pose proof (sweight_weight p2) as HH. *)
    (*       rewrite HG in HH. lia. *)
    (*     + eapply IHq. rewrite weight_add_end. *)
    (*       lia. *)
    (* Qed. *)

    Lemma weight_simplify {s x y} q (p : SimplePaths s x y)
      : forall {s'} Hs, 0 < weight q \/ 0 < sweight p
        -> 0 < sweight (simplify q p (s':=s') Hs)..2.
    Proof.
      revert s p; induction q.
      - cbn; intros. intuition. now rewrite weight_SimplePaths_sub.
      - intros s p s' Hs H; cbn in H. simpl.
        set (F0 := proj2 (VSetFact.not_mem_iff s x)); clearbody F0.
        set (F1 := @VSetFact.mem_2 s x); clearbody F1.
        set (F2 := @simplify_aux2 s x); clearbody F2.
        destruct (VSet.mem x s).
        + case_eq (split p); intros p1 p2 Hp.
          case_eq (0 <? sweight p2); intro eq.
          cbn. apply PeanoNat.Nat.leb_le in eq.
          rewrite weight_SimplePaths_sub; lia.
          eapply IHq. rewrite weight_add_end.
          pose proof (weight_split p) as X; rewrite Hp in X; cbn in X.
          apply PeanoNat.Nat.ltb_ge in eq. lia.
        + eapply IHq. rewrite weight_add_end. lia.
    Qed.



    Import Nbar.

    Definition succs (x : V.t) : list (nat * V.t)
      := let l := List.filter (fun e => V.eq_dec e..s x) (EdgeSet.elements (E G)) in
         List.map (fun e => (e..w, e..t)) l.

    (* lsp = longest simple path *)
    (* l is the list of authorized intermediate nodes *)
    (* lsp0 (a::l) x y = max (lsp0 l x y) (lsp0 l x a + lsp0 l a y) *)

    Fixpoint lsp00 fuel (s : VSet.t) (x z : V.t) : Nbar.t :=
      let base := if V.eq_dec x z then Some 0 else None in
      match fuel with
      | 0 => base
      | S fuel => 
        match VSet.mem x s with
        | true =>
          let ds := List.map
                      (fun '(n, y) => Some n + lsp00 fuel (VSet.remove x s) y z)%nbar
                      (succs x) in
          List.fold_left Nbar.max ds base
        | false => base end
      end.

    Definition lsp0 s := lsp00 (VSet.cardinal s) s.

    Lemma lsp0_eq s x z : lsp0 s x z =
      let base := if V.eq_dec x z then Some 0 else None in
      match VSet.mem x s with
      | true =>
        let ds := List.map (fun '(n, y) => Some n + lsp0 (VSet.remove x s) y z)%nbar
                           (succs x) in
        List.fold_left Nbar.max ds base
      | false => base end.
    Proof.
      unfold lsp0. set (fuel := VSet.cardinal s).
      cut (VSet.cardinal s = fuel); [|reflexivity].
      clearbody fuel. revert s x. induction fuel.
      - intros s x H.
        apply VSetProp.cardinal_inv_1 in H.
        specialize (H x). apply VSetProp.FM.not_mem_iff in H.
        rewrite H. reflexivity.
      - intros s x H. simpl.
        case_eq (VSet.mem x s); [|reflexivity].
        intro HH. f_equal. apply List.map_ext.
        intros [n y].
        assert (H': VSet.cardinal (VSet.remove x s) = fuel);
          [|rewrite H'; reflexivity].
        apply VSet.mem_spec, VSetProp.remove_cardinal_1 in HH.
        lia.
    Qed.

    (* From Equations Require Import Equations. *)

    (* Equations lsp0 (s : VSet.t) (x z : V.t) : Nbar.t by wf (VSet.cardinal s) *)
    (*   := *)
    (*   lsp0 s x z := *)
    (*   let base := if V.eq_dec x z then Some 0 else None in *)
    (*   match VSet.mem x s as X return VSet.mem x s = X -> _ with *)
    (*   | true => fun XX => *)
    (*     let ds := List.map (fun '(n, y) => Some n + lsp0 (VSet.remove x s) y z)%nbar *)
    (*                        (succs x) in *)
    (*     List.fold_left Nbar.max ds base *)
    (*   | false => fun _ => base end eq_refl. *)
    (* Next Obligation. *)
    (*   apply VSet.mem_spec in XX. *)
    (*   pose proof (VSetProp.remove_cardinal_1 XX). *)
    (*   lia. *)
    (* Defined. *)

    Definition lsp := lsp0 (V G).


    Lemma lsp0_VSet_Equal {s s' x y} :
      VSet.Equal s s' -> lsp0 s x y = lsp0 s' x y.
    Admitted.

    (* Lemma lsp0_VSet_Subset {s s' x y} : *)
    (*   VSet.Subset s s' -> (lsp0 s x y <= lsp0 s' x y)%nbar. *)
    (* Admitted. *)

    Lemma InAeq_In {A} (l : list A) x :
      InA eq x l <-> In x l.
    Proof.
      etransitivity. eapply InA_alt. firstorder. now subst.
    Defined.
    
    Lemma lsp0_spec_le {s x y} (p : SimplePaths s x y)
      : (Some (sweight p) <= lsp0 s x y)%nbar.
    Proof.
      induction p; rewrite lsp0_eq; simpl.
      - destruct (V.eq_dec x x); [|contradiction].
        destruct (VSet.mem x s0); [|cbn; reflexivity].
        match goal with
        | |- (_ <= fold_left ?F _ _)%nbar =>
          assert (XX: (forall l acc, Some 0 <= acc -> Some 0 <= fold_left F l acc)%nbar);
            [|apply XX; cbn; reflexivity]
        end.
        clear; induction l.
        + cbn; trivial.
        + intros acc H; simpl. apply IHl.
          apply max_le'; now left.
      - assert (ee: VSet.mem x s' = true). {
          apply VSet.mem_spec, d. left; reflexivity. }
        rewrite ee. etransitivity.
        eapply (plus_le_compat (Some e..1) _ (Some (sweight p))).
        reflexivity. eassumption.
        apply Nbar.fold_max_le'.
        right.
        unfold succs. rewrite map_map_compose.
        apply in_map_iff. exists (x, e..1, y). simpl.
        split.
        + cbn -[lsp0].
          assert (XX: VSet.Equal (VSet.remove x s') s0). {
            clear -d.
            intro a; split; intro Ha.
            * apply VSet.remove_spec in Ha. pose proof (d.1 a).
              intuition.
            * apply VSet.remove_spec. split.
              apply d. right; assumption.
              intro H. apply proj2 in d. apply d. subst; assumption. }
          rewrite (lsp0_VSet_Equal XX); reflexivity.
        + apply filter_In. split.
          apply InAeq_In, EdgeSet.elements_spec1. exact e..2.
          cbn. destruct (V.eq_dec x x); [reflexivity|contradiction].
    Qed.

    Lemma lsp0_spec_eq {s x y} n
      : lsp0 s x y = Some n -> exists p : SimplePaths s x y, sweight p = n.
    Proof.
      set (c := VSet.cardinal s). assert (e: VSet.cardinal s = c) by reflexivity.
      clearbody c; revert s e x y n.
      induction c using Wf_nat.lt_wf_ind.
      rename H into IH.
      intros s e x y n H. 
      rewrite lsp0_eq in H; cbn -[lsp0] in H.
      case_eq (VSet.mem x s); intro Hx; rewrite Hx in H.
      - apply fold_max_In in H. destruct H.
        + destruct (V.eq_dec x y); [|discriminate].
          apply some_inj in H; subst.
          unshelve eexists; reflexivity.
        + apply in_map_iff in H.
          destruct H as [[x' n'] [H1 H2]].
          case_eq (lsp0 (VSet.remove x s) n' y).
          2: intros ee; rewrite ee in H1; discriminate.
          intros nn ee; rewrite ee in H1.
          eapply IH in ee. 3: reflexivity.
          * destruct ee as [p1 Hp1].
            unfold succs in H2.
            apply in_map_iff in H2.
            destruct H2 as [[[x'' n''] y''] [H2 H2']]; cbn in H2.
            inversion H2; subst; clear H2.
            apply filter_In in H2'; destruct H2' as [H2 H2']; cbn in H2'.
            destruct (V.eq_dec x'' x); [subst|discriminate]; clear H2'.
            unshelve eexists. econstructor.
            3: eassumption.
            -- split. 2: apply VSetFact.remove_1; reflexivity.
               apply VSetProp.Add_remove.
               apply VSet.mem_spec; assumption.
            -- eexists.
               apply (EdgeSet.elements_spec1 _ _).1, InAeq_In; eassumption.
            -- cbn. now apply some_inj in H1.
          * subst. clear -Hx. apply VSet.mem_spec in Hx.
            apply VSetProp.remove_cardinal_1 in Hx. lia.
      - destruct (V.eq_dec x y); [|discriminate].
        apply some_inj in H; subst. unshelve eexists; reflexivity.
    Qed.


    Definition correct_labelling (l : labelling) :=
      l (s G) = 0 /\
      forall e, EdgeSet.In e (E G) -> l e..s + e..w <= l e..t.

    Lemma correct_labelling_Paths l (Hl : correct_labelling l)
      : forall x y (p : Paths x y), l x + weight p <= l y.
    Proof.
      induction p. cbn; lia.
      apply proj2 in Hl.
      specialize (Hl (x, e..1, y) e..2). cbn in *; lia.
    Qed.

    Lemma acyclic_labelling l : correct_labelling l -> acyclic_no_loop.
    Proof.
      intros Hl x p.
      specialize (correct_labelling_Paths l Hl x x p); lia.
    Qed.

    Lemma lsp0_triangle_inequality (HG : acyclic_no_loop) s x y1 y2 n
          (He : EdgeSet.In (y1, n, y2) (E G))
          (Hy : VSet.In y1 s)
      : (lsp0 s x y1 + Some n <= lsp0 s x y2)%nbar.
    Proof.
      case_eq (lsp0 s x y1); [|cbn; trivial].
      intros m Hm. 
      apply lsp0_spec_eq in Hm.
      destruct Hm as [p Hp].
      case_eq (split p).
      intros p1 p2 Hp12.
      pose proof (weight_split p) as H.
      rewrite Hp12 in H; cbn in H.
      etransitivity.
      2: unshelve eapply (lsp0_spec_le (add_end p1 (n; He) _)).
      subst; rewrite weight_add_end; cbn.
      pose proof (sweight_weight p2) as HH.
      rewrite HG in HH. lia.
      now apply DisjointAdd_remove1.
    Qed.

    Lemma acyclic_lsp0_xx (HG : acyclic_no_loop) s x
      : lsp0 s x x = Some 0.
    Proof.
      pose proof (lsp0_spec_le (spaths_refl s x)) as H; cbn in H.
      case_eq (lsp0 s x x); [|intro e; rewrite e in H; cbn in H; lia].
      intros n Hn. apply lsp0_spec_eq in Hn.
      destruct Hn as [p Hp]. rewrite sweight_weight, HG in Hp.
      subst; reflexivity.
    Qed.

    Definition lsp0_sub {s s' x y}
      : VSet.Subset s s' -> (lsp0 s x y <= lsp0 s' x y)%nbar.
    Proof.
      case_eq (lsp0 s x y); [|cbn; trivial].
      intros n Hn Hs.
      apply lsp0_spec_eq in Hn; destruct Hn as [p Hp]; subst.
      rewrite <- (weight_SimplePaths_sub Hs p).
      apply lsp0_spec_le.
    Qed.

    Definition simplify2 {x z} (p : Paths x z)
      :  forall y (Hy: {VSet.In y (nodes p)} + {x = y}), SimplePaths (nodes p) y z.
    Proof.
      induction p.
      - cbn. intros y [H|H]. 
        now apply VSetFact.empty_iff in H.
        subst; reflexivity.
      - cbn; intros u H.
        case_eq (VSet.mem u (nodes p)); intro HH.
        + apply VSet.mem_spec in HH. eapply SimplePaths_sub, IHp.
          apply VSetProp.subset_add_2; reflexivity. intuition.
        + assert (X: u = x). {
            destruct H as [H|H]; [|intuition].
            apply VSet.add_spec in H; destruct H as [H|H].
            assumption. apply VSet.mem_spec in H.
            rewrite H in HH; discriminate. }
          subst. econstructor. 2: eassumption.
          2: eapply IHp; now right.
          split. apply VSetProp.Add_add.
          now apply VSetFact.not_mem_iff.
    Defined.      


    Lemma nodes_subset {x y} (p : Paths x y)
      : VSet.Subset (nodes p) (V G).
    Proof.
      induction p; cbn.
      apply VSetProp.subset_empty.
      apply VSetProp.subset_add_3; [|assumption].
      apply proj1 in HI.
      specialize (HI _ e..2); cbn in HI; apply HI.
    Qed.

    Lemma lsp_s (HG : acyclic_no_loop) x (Hx : VSet.In x (V G))
      : exists n, lsp (s G) x = Some n.
    Proof.
      case_eq (lsp (s G) x).
      - intros n H; eexists; reflexivity.
      - intro e.
        destruct (proj2 (proj2 HI) x Hx) as [p].
        pose proof (simplify2 p _ (right eq_refl)) as p'.
        assert (X: (Some (sweight p') <= lsp (s G) x)%nbar). {
          etransitivity. eapply (lsp0_spec_le p').
          now eapply lsp0_sub, nodes_subset. }
        rewrite e in X. inversion X.
    Qed.


    Lemma lsp_correctness (HG : acyclic_no_loop) :
        correct_labelling (fun x => option_get 0 (lsp (s G) x)).
    Proof.
      split.
      - unfold lsp. now rewrite acyclic_lsp0_xx.
      - intros [[x n] y] He; cbn. unfold lsp.
        simple refine (let H := lsp0_triangle_inequality
                                  HG (V G) (s G) x y n He _
                       in _); [|clearbody H].
        apply proj1 in HI. specialize (HI _ He); cbn in HI; intuition.
        destruct (lsp_s HG x) as [m Hm].
        + apply proj1 in HI. apply (HI _ He).
        + unfold lsp in Hm; rewrite Hm in *; cbn in *.
        destruct (lsp0 (V G) (s G) y); cbn in *; intuition.
    Qed.

    Lemma SimplePaths_In {s x y} (p : SimplePaths s x y)
      : sweight p > 0 -> VSet.In x s.
    Proof.
      destruct p. inversion 1.
      intros _. apply d. left; reflexivity.
    Qed.

    Lemma lsp_xx_acyclic
      : VSet.For_all (fun x => lsp x x = Some 0) (V G) -> acyclic_no_loop'.
    Proof.
      intros H. intros x [p Hp].
      simple refine (let Hq := weight_simplify p (spaths_refl (V G) _)
                                               _ (or_introl Hp)
                     in _).
      + exact (V G).
      + etransitivity. apply VSetProp.union_sym.
        etransitivity. apply VSetProp.union_subset_equal.
        apply nodes_subset. reflexivity.
      + match goal with
        | _ : 0 < sweight ?qq..2 |- _ => set (q := qq) in *; clearbody Hq
        end.
        destruct q as [x' q]; cbn in Hq.
        assert (Some (sweight q) <= Some 0)%nbar. {
          erewrite <- H. eapply lsp0_spec_le.
          eapply SimplePaths_In; eassumption. }
        cbn in H0; lia.
    Defined.


    Lemma VSet_Forall_reflect P f (Hf : forall x, reflect (P x) (f x)) s
      : reflect (VSet.For_all P s) (VSet.for_all f s).
    Proof.
      apply iff_reflect. etransitivity.
      2: apply VSetFact.for_all_iff.
      2: intros x y []; reflexivity.
      apply iff_forall; intro x.
      apply iff_forall; intro Hx.
      now apply reflect_iff.
    Qed.

    Lemma reflect_logically_equiv {A B} (H : A <-> B) f
      : reflect B f -> reflect A f.
    Proof.
      destruct 1; constructor; intuition.
    Qed.

    Definition is_acyclic := VSet.for_all (fun x => match lsp x x with
                                                 | Some 0 => true
                                                 | _ => false
                                                 end) (V G).


    (** ** Main results about acyclicity *)

    Lemma acyclic_caract1
      : acyclic_no_loop <-> exists l, correct_labelling l.
    Proof.
      split.
      intro HG; eexists. eapply (lsp_correctness HG).
      intros [l Hl]; eapply acyclic_labelling; eassumption.
    Defined.

    Lemma acyclic_caract2 :
      acyclic_no_loop <-> (VSet.For_all (fun x => lsp x x = Some 0) (V G)).
    Proof.
      split.
      - intros HG x Hx. now apply acyclic_lsp0_xx.
      - intros H. apply acyclic_no_loop_loop'.
        eapply lsp_xx_acyclic; eassumption.
    Defined.

    (* Lemma acyclic_caract3 *)
    (*   : acyclic_no_loop <-> acyclic_well_founded. *)
    (* Proof. *)
    (*   split. *)
    (*   intro. eapply acyclic_labelling. *)
    (*   now eapply lsp_correctness. *)
    (*   apply acyclic_wf_no_loop. *)
    (* Defined. *)

    Lemma is_acyclic_correct : reflect acyclic_no_loop is_acyclic.
    Proof.
      eapply reflect_logically_equiv. eapply acyclic_caract2.
      apply VSet_Forall_reflect; intro x.
      destruct (lsp x x). destruct n. constructor; reflexivity.
      all: constructor; discriminate.
    Qed.
  End graph.
End WeightedGraph.




