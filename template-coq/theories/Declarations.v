(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils BasicAst.
From MetaCoq.Template Require Import Universes Environment.
From MetaCoq.Template.utils Require Import RTree. 

(** A variant of the Environment module which features a more accurate representation of mutual inductive types *)

Module Declarations (T : Term).

  Import T.

  (** ** Declarations *)

  (** *** The context of De Bruijn indices *)

  (* corresponds to rel_context in Coq code *)
  Record context_decl := mkdecl {
    decl_name : aname ;
    decl_body : option term ;   (* if Some -> LocalDef; None -> LocalAssum *)
    decl_type : term
  }.

  (** Local (de Bruijn) variable binding *)

  Definition vassumption x A :=
    {| decl_name := x ; decl_body := None ; decl_type := A |}.

  (** Local (de Bruijn) let-binding *)

  Definition vdefinition x t A :=
    {| decl_name := x ; decl_body := Some t ; decl_type := A |}.

  (** Local (de Bruijn) context *)

  Definition context := list context_decl.

  (** Last declaration first *)

  Definition snoc {A} (Γ : list A) (d : A) := d :: Γ.

  Notation " Γ ,, d " := (snoc Γ d) (at level 20, d at next level).

  Definition map_decl f (d : context_decl) :=
    {| decl_name := d.(decl_name);
       decl_body := option_map f d.(decl_body);
       decl_type := f d.(decl_type) |}.

  Definition map_context f c :=
    List.map (map_decl f) c.
    
  Definition fold_context f (Γ : context) : context :=
    List.rev (mapi (fun k' decl => map_decl (f k') decl) (List.rev Γ)).

  Arguments fold_context f Γ%list_scope.


  (** Representation of mutual inductive types in the kernel *)

  (* Recursive argument labels for representing the recursive structure of constructors of inductive types. *)
  Inductive recarg := 
    | Norec                 (* Non-recursive argument *)
    | Mrec (i : inductive)  (* Recursive argument of type i *)
    | Imbr (i : inductive). (* Recursive argument of "external" inductive type i, i.e. from another block of mutual inductives *)

  (* TODO: not a faithful representation of sort in Coq:
      - Set is missing 
    *)
  Definition sort := Universe.t.

  (* In Coq kernel speak, an arity is the type of an inductive without the parameters (i.e. what comes after the colon when writing down the inductive) *)
  Record inductive_arity := {
    ind_user_arity : term; (* the full arity *)
    ind_sort : sort        (* just the sort *)
  }.

  (* the type used to represent the recursion structure of the arguments of constructors *)
  Definition wf_paths := rtree recarg.

  Notation type := term (only parsing).

  (** See [one_inductive_body] from [declarations.ml]. *)
  Record one_inductive_body := {
    ind_name : ident; (** Name of the type: [Ii] *)
    ind_arity : inductive_arity; (** Arity sort and original user arity *)
    ind_arity_ctxt : context; (** Arity context of [Ii] with parameters: [forall params, Ui] *)

    ind_consnames : list ident; (** Names of the constructors: [cij] *)
    ind_ctor_types : list type;
 (** Types of the constructors with parameters:  [forall params, Tij],
     where the Ik are replaced by de Bruijn index in the
     context I1:forall params, U1 ..  In:forall params, Un *)

(** Derived *)
    ind_nrealargs : nat; (* Number of expected real arguments of the type (no let, no params), i.e. indices *)
    ind_nrealdecls : nat; (* length of realargs context (with let, no params *)

    ind_kelim : sort_family; (* Top allowed elimination sort *)

    ind_ctors_hnf : list (context * type); (* head-normalized constructor types so that their conclusion exposes the inductive type -- context contains the parameters *)

    ind_ctors_nrealargs : list nat; (* number of expected real arguments of constructors (without params) *)

    ind_ctors_nrealdecls : list nat; (* length of the signature of the constructors (with let, without params) *)

    ind_recargs : wf_paths; (* signature of recursive arguments in the constructors *)

    ind_relevance : relevance (* relevance of the inductive definition *)

    (*ind_ctors : list (ident * term [> Under context of arities of the mutual inductive <-- TODO: what is that supposed to mean?<]*)
                      (** nat [> arity, w/o lets, w/o parameters <]);*)
    (*ind_projs : list (ident * term); (* names and types of projections, if any.*)
                                      (*Type under context of params and inductive object *)*)
  
  }.

  (*Definition map_one_inductive_body npars arities f (n : nat) m :=*)
    (*match m with*)
    (*| Build_one_inductive_body ind_name ind_type ind_kelim ind_ctors ind_projs ind_relevance =>*)
      (*Build_one_inductive_body ind_name*)
                               (*(f 0 ind_type)*)
                               (*ind_kelim*)
                               (*(map (on_pi2 (f arities)) ind_ctors)*)
                               (*(map (on_snd (f (S npars))) ind_projs)*)
                               (*ind_relevance*)
    (*end.*)


  (** See [mutual_inductive_body] from [declarations.ml]. *)
  Record mutual_inductive_body := {
    ind_bodies : list one_inductive_body ;  (* the list of inductive bodies *)
    ind_finite : recursivity_kind;          (* inductive or coinductive *)
    ind_ntypes : nat;                       (* number of types in the block *)
    ind_npars : nat;                        (* number of parameters including non-uniform ones (i.e. length of ind_params without let-in)*)
    ind_npars_unif : nat;                   (* number of uniform parameters *)
    ind_params : context;                   (* the context of parameters, including let-in declarations *)
    ind_universes : universes_decl;         (* information about monomorphic/polymorphic inductives and their universes *)
    ind_variance : option (list Universes.Variance.t) (* variance info, [None] when non-cumulative *)

    (* omitting:
      - mind_hyps (section hypotheses)
      - mind_template (template universes)
      - mind_sec_variance (variance info for section polymorphic universes)
      - mind_private (allowing pattern-matching)
      - mind_typing_flags (flags with which it was declared)
    *)
  }.  

  (** See [constant_body] from [declarations.ml] *)
  Record constant_body := {
      cst_type : term;
      cst_body : option term;
      cst_universes : universes_decl 
      (* currently missing a lot of stuff from the kernel *)
  }.

  Definition map_constant_body f decl :=
    {| cst_type := f decl.(cst_type);
       cst_body := option_map f decl.(cst_body);
       cst_universes := decl.(cst_universes) |}.

  Inductive global_decl :=
  | ConstantDecl : constant_body -> global_decl
  | InductiveDecl : mutual_inductive_body -> global_decl.

  (* environment of kernel names with global declaration *)
  Definition global_env := list (kername * global_decl).

  (** A context of global declarations + global universe constraints,
      i.e. a global environment *)
  Definition global_env_ext : Type := global_env * universes_decl.

  (** Use a coercion for this common projection of the global context. *)
  Definition fst_ctx : global_env_ext -> global_env := fst.
  Coercion fst_ctx : global_env_ext >-> global_env.

  Definition empty_ext (Σ : global_env) : global_env_ext
    := (Σ, Monomorphic_ctx ContextSet.empty).

  (** *** Programs

    A set of declarations and a term, as produced by [MetaCoq Quote Recursively]. *)

  Definition program : Type := global_env * term.

  (* TODO MOVE AstUtils factorisation *)

  Definition app_context (Γ Γ' : context) : context := Γ' ++ Γ.
  Notation "Γ ,,, Γ'" :=
    (app_context Γ Γ') (at level 25, Γ' at next level, left associativity).

  (** Make a lambda/let-in string of abstractions from a context [Γ], ending with term [t]. *)

  Definition mkLambda_or_LetIn d t :=
    match d.(decl_body) with
    | None => tLambda d.(decl_name) d.(decl_type) t
    | Some b => tLetIn d.(decl_name) b d.(decl_type) t
    end.

  Definition it_mkLambda_or_LetIn (l : context) (t : term) :=
    List.fold_left (fun acc d => mkLambda_or_LetIn d acc) l t.

  (** Make a prod/let-in string of abstractions from a context [Γ], ending with term [t]. *)

  Definition mkProd_or_LetIn d t :=
    match d.(decl_body) with
    | None => tProd d.(decl_name) d.(decl_type) t
    | Some b => tLetIn d.(decl_name) b d.(decl_type) t
    end.

  Definition it_mkProd_or_LetIn (l : context) (t : term) :=
    List.fold_left (fun acc d => mkProd_or_LetIn d acc) l t.

  Fixpoint reln (l : list term) (p : nat) (Γ0 : list context_decl) {struct Γ0} : list term :=
    match Γ0 with
    | [] => l
    | {| decl_body := Some _ |} :: hyps => reln l (p + 1) hyps
    | {| decl_body := None |} :: hyps => reln (tRel p :: l) (p + 1) hyps
    end.

  Definition to_extended_list_k Γ k := reln [] k Γ.
  Definition to_extended_list Γ := to_extended_list_k Γ 0.

  Fixpoint reln_alt p Γ :=
    match Γ with
    | [] => []
    | {| decl_body := Some _ |} :: Γ => reln_alt (p + 1) Γ
    | {| decl_body := None |} :: Γ => tRel p :: reln_alt (p + 1) Γ
    end.

  (* reconstruct the full type of an inductive by composing the arity context and the arity *)
  Definition mk_ind_type (ind : one_inductive_body) : type := 
    it_mkProd_or_LetIn ind.(ind_arity_ctxt) ind.(ind_arity).(ind_user_arity). 

  (* make a context with the inductive types of a list of inductives *)
  Definition arities_context (l : list one_inductive_body) : context :=
    rev_map (fun ind => vassumption (mkBindAnn (nNamed ind.(ind_name))
                                (ind.(ind_relevance))) (mk_ind_type ind)) l.

  (* get number of assumptions in context *)
  Fixpoint context_assumptions (Γ : context) :=
    match Γ with
    | [] => 0
    | d :: Γ =>
      match d.(decl_body) with
      | Some _ => context_assumptions Γ
      | None => S (context_assumptions Γ)
      end
    end.

  (*Definition map_mutual_inductive_body f m :=*)
    (*match m with*)
    (*| Build_mutual_inductive_body finite ind_npars ind_pars ind_bodies ind_universes ind_variance =>*)
      (*let arities := arities_context ind_bodies in*)
      (*let pars := fold_context f ind_pars in*)
      (*Build_mutual_inductive_body finite ind_npars pars*)
                                  (*(mapi (map_one_inductive_body (context_assumptions pars) (length arities) f) ind_bodies)*)
                                  (*ind_universes ind_variance*)
    (*end.*)

  Fixpoint lookup_env (Σ : global_env) (kn : kername) : option global_decl :=
    match Σ with
    | nil => None
    | d :: tl =>
      if eq_kername kn d.1 then Some d.2
      else lookup_env tl kn
    end.

  Definition lookup_env_mind Σ kn : option mutual_inductive_body := 
    match lookup_env Σ kn with 
    | Some (InductiveDecl ind) => Some ind
    | _ => None
    end.
End Declarations.

Module Type DeclarationsSig (T : Term).
 Include Declarations T.
End DeclarationsSig.
