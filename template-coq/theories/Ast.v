(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils Environment.
From MetaCoq.Template Require Export Universes.



(** * AST of Coq kernel terms and kernel data structures

    ** Basic data-types:

      We reflect identifiers [ident], sort families [sort_family], names
    [name], cast kinds [cast_kind], inductives [inductive] and primitive
    projections [projection] and (co)-fixpoint blocks [mfixpoint] and
    [def]. These are defined in the [BasicAst] file.

    ** Terms:

      The AST is [term : Set]

      Smart constructors [mkApp], [mkApps] maintain the invariant
    of no nested or empty n-ary applications.
      List in fixpoints and cofixpoint should be non-empty.

    ** Kernel interface: entries and declarations

      Kernel input declarations for constants [constant_entry] and mutual
    inductives [mutual_inductive_entry]. Kernel safe declarations for
    constants [constand_decl] and inductives [minductive_decl].

    ** Environments of declarations

      The global environment [global_env_ext]: a list of [global_decl] and
    a universe graph [constraints].  *)

From MetaCoq.Template Require Export BasicAst.

Inductive term : Type :=
| tRel (n : nat)
| tVar (id : ident) (* For free variables (e.g. in a goal) *)
| tEvar (ev : nat) (args : list term)
| tSort (s : Universe.t)
| tCast (t : term) (kind : cast_kind) (v : term)
| tProd (na : aname) (ty : term) (body : term)
| tLambda (na : aname) (ty : term) (body : term)
| tLetIn (na : aname) (def : term) (def_ty : term) (body : term)
| tApp (f : term) (args : list term)
| tConst (c : kername) (u : Instance.t)
| tInd (ind : inductive) (u : Instance.t)
| tConstruct (ind : inductive) (idx : nat) (u : Instance.t)
| tCase (ind_nbparams_relevance: inductive*nat*relevance) (type_info:term)
        (discr:term) (branches : list (nat * term))
| tProj (proj : projection) (t : term)
| tFix (mfix : mfixpoint term) (idx : nat)
| tCoFix (mfix : mfixpoint term) (idx : nat).


Definition mkApps t us :=
  match us with
  | nil => t
  | _ => match t with
        | tApp f args => tApp f (args ++ us)
        | _ => tApp t us
        end
  end.


Module TemplateTerm <: Term.

Definition term := term.

Definition tRel := tRel.
Definition tSort := tSort.
Definition tProd := tProd.
Definition tLambda := tLambda.
Definition tLetIn := tLetIn.
Definition tInd := tInd.
Definition tProj := tProj.
Definition mkApps := mkApps.

End TemplateTerm.

Ltac unf_term := unfold TemplateTerm.term in *; unfold TemplateTerm.tRel in *;
                 unfold TemplateTerm.tSort in *; unfold TemplateTerm.tProd in *;
                 unfold TemplateTerm.tLambda in *; unfold TemplateTerm.tLetIn in *;
                 unfold TemplateTerm.tInd in *; unfold TemplateTerm.tProj in *.

Module TemplateEnvironment := Environment TemplateTerm.
Include TemplateEnvironment.

Definition mkApp t u := Eval cbn in mkApps t [u].

Definition isApp t :=
  match t with
  | tApp _ _ => true
  | _ => false
  end.

Definition isLambda t :=
  match t with
  | tLambda _ _ _ => true
  | _ => false
  end.

(** Well-formed terms: invariants which are not ensured by the OCaml type system *)

Inductive wf : term -> Prop :=
| wf_tRel n : wf (tRel n)
| wf_tVar id : wf (tVar id)
| wf_tEvar n l : Forall wf l -> wf (tEvar n l)
| wf_tSort u : wf (tSort u)
| wf_tCast t k t' : wf t -> wf t' -> wf (tCast t k t')
| wf_tProd na t b : wf t -> wf b -> wf (tProd na t b)
| wf_tLambda na t b : wf t -> wf b -> wf (tLambda na t b)
| wf_tLetIn na t b b' : wf t -> wf b -> wf b' -> wf (tLetIn na t b b')
| wf_tApp t u : isApp t = false -> u <> nil -> wf t -> Forall wf u -> wf (tApp t u)
| wf_tConst k u : wf (tConst k u)
| wf_tInd i u : wf (tInd i u)
| wf_tConstruct i k u : wf (tConstruct i k u)
| wf_tCase ci p c brs : wf p -> wf c -> Forall (wf ∘ snd) brs -> wf (tCase ci p c brs)
| wf_tProj p t : wf t -> wf (tProj p t)
| wf_tFix mfix k : Forall (fun def => wf def.(dtype) /\ wf def.(dbody) /\ isLambda def.(dbody) = true) mfix ->
                   wf (tFix mfix k)
| wf_tCoFix mfix k : Forall (fun def => wf def.(dtype) /\ wf def.(dbody)) mfix -> wf (tCoFix mfix k).

(** ** Entries

  The kernel accepts these inputs and typechecks them to produce
  declarations. Reflects [kernel/entries.mli].
*)

(** *** Constant and axiom entries *)

Record parameter_entry := {
  parameter_entry_type      : term;
  parameter_entry_universes : universes_entry }.

Record definition_entry := {
  definition_entry_type      : option term;
  definition_entry_body      : term;
  definition_entry_universes : universes_entry;
  definition_entry_opaque    : bool }.


Inductive constant_entry :=
| ParameterEntry  (p : parameter_entry)
| DefinitionEntry (def : definition_entry).

(** *** Inductive entries *)

(** This is the representation of mutual inductives.
    nearly copied from [kernel/entries.mli]

  Assume the following definition in concrete syntax:

[[
  Inductive I1 (x1:X1) ... (xn:Xn) : A1 := c11 : T11 | ... | c1n1 : T1n1
  ...
  with      Ip (x1:X1) ... (xn:Xn) : Ap := cp1 : Tp1  ... | cpnp : Tpnp.
]]

  then, in [i]th block, [mind_entry_params] is [xn:Xn;...;x1:X1];
  [mind_entry_arity] is [Ai], defined in context [x1:X1;...;xn:Xn];
  [mind_entry_lc] is [Ti1;...;Tini], defined in context
  [A'1;...;A'p;x1:X1;...;xn:Xn] where [A'i] is [Ai] generalized over  (* TODO: I think first the xi should come, then the A'i, judging from AstUtils *)
  [x1:X1;...;xn:Xn].
*)

Record one_inductive_entry := {
  mind_entry_typename : ident;
  mind_entry_arity : term;
  mind_entry_template : bool; (* template polymorphism *)
  mind_entry_consnames : list ident;
  mind_entry_lc : list term (* constructor list*) }.

Record mutual_inductive_entry := {
  mind_entry_record    : option (option ident);
  (* Is this mutual inductive defined as a record?
     If so, is it primitive, using binder name [ident]
     for the record in primitive projections ? *)
  mind_entry_finite    : recursivity_kind;
  mind_entry_params    : context;
  mind_entry_inds      : list one_inductive_entry;
  mind_entry_universes : universes_entry;
  mind_entry_variance  : option (list Universes.Variance.t);
  mind_entry_private   : option bool
  (* Private flag for sealing an inductive definition in an enclosing
     module. Not handled by Template Coq yet. *) }.
