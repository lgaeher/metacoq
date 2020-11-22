(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils BasicAst Ast.
Require Import ssreflect.

(** Raw term printing *)

Fixpoint string_of_term (t : term) :=
  match t with
  | tRel n => "Rel(" ^ string_of_nat n ^ ")"
  | tVar n => "Var(" ^ n ^ ")"
  | tEvar ev args => "Evar(" ^ string_of_nat ev ^ "," ^ string_of_list string_of_term args ^ ")"
  | tSort s => "Sort(" ^ string_of_sort s ^ ")"
  | tCast c k t => "Cast(" ^ string_of_term c ^ (* TODO *) ","
                           ^ string_of_term t ^ ")"
  | tProd na b t => "Prod(" ^ string_of_name na.(binder_name) ^ ","
                            ^ string_of_relevance na.(binder_relevance) ^ ","
                            ^ string_of_term b ^ ","
                            ^ string_of_term t ^ ")"
  | tLambda na b t => "Lambda(" ^ string_of_name na.(binder_name) ^ ","
                                ^ string_of_term b ^ ","
                                ^ string_of_relevance na.(binder_relevance) ^ ","
                                ^ string_of_term t ^ ")"
  | tLetIn na b t' t => "LetIn(" ^ string_of_name na.(binder_name) ^ ","
                                 ^ string_of_relevance na.(binder_relevance) ^ ","
                                 ^ string_of_term b ^ ","
                                 ^ string_of_term t' ^ ","
                                 ^ string_of_term t ^ ")"
  | tApp f l => "App(" ^ string_of_term f ^ "," ^ string_of_list string_of_term l ^ ")"
  | tConst c u => "Const(" ^ string_of_kername c ^ "," ^ string_of_universe_instance u ^ ")"
  | tInd i u => "Ind(" ^ string_of_inductive i ^ "," ^ string_of_universe_instance u ^ ")"
  | tConstruct i n u => "Construct(" ^ string_of_inductive i ^ "," ^ string_of_nat n ^ ","
                                    ^ string_of_universe_instance u ^ ")"
  | tCase (ind, i, r) t p brs =>
    "Case(" ^ string_of_inductive ind ^ ","
            ^ string_of_nat i ^ ","
            ^ string_of_relevance r ^ ","
            ^ string_of_term t ^ ","
            ^ string_of_term p ^ ","
            ^ string_of_list (fun b => string_of_term (snd b)) brs ^ ")"
  | tProj (ind, i, k) c =>
    "Proj(" ^ string_of_inductive ind ^ "," ^ string_of_nat i ^ "," ^ string_of_nat k ^ ","
            ^ string_of_term c ^ ")"
  | tFix l n => "Fix(" ^ (string_of_list (string_of_def string_of_term) l) ^ "," ^ string_of_nat n ^ ")"
  | tCoFix l n => "CoFix(" ^ (string_of_list (string_of_def string_of_term) l) ^ "," ^ string_of_nat n ^ ")"
  end.

Definition decompose_app (t : term) :=
  match t with
  | tApp f l => (f, l)
  | _ => (t, [])
  end.

Lemma decompose_app_mkApps f l :
  isApp f = false -> decompose_app (mkApps f l) = (f, l).
Proof.
  intros.
  destruct l; simpl;
    destruct f; simpl; try (discriminate || reflexivity).
Qed.

Lemma mkApps_nested f l l' : mkApps (mkApps f l) l' = mkApps f (l ++ l').
Proof.
  induction l; destruct f; destruct l'; simpl; rewrite ?app_nil_r; auto.
  f_equal. now rewrite <- app_assoc.
Qed.

Lemma mkApp_mkApps f a l : mkApp (mkApps f l) a = mkApps f (l ++ [a]).
Proof.
  destruct l. simpl. reflexivity.
  rewrite <- mkApps_nested. reflexivity.
Qed.

Lemma mkApp_tApp f u : isApp f = false -> mkApp f u = tApp f [u].
Proof. intros. destruct f; (discriminate || reflexivity). Qed.

Fixpoint decompose_prod (t : term) : (list aname) * (list term) * term :=
  match t with
  | tProd n A B => let (nAs, B) := decompose_prod B in
                  let (ns, As) := nAs in
                  (n :: ns, A :: As, B)
  | _ => ([], [], t)
  end.

Fixpoint remove_arity (n : nat) (t : term) : term :=
  match n with
  | O => t
  | S n => match t with
          | tProd _ _ B => remove_arity n B
          | _ => t (* todo *)
          end
  end.

(** Inductives *)
Definition sort := Universe.t.

(* In Coq kernel speak, an arity is the type of an inductive without the parameters (i.e. what comes after the colon when writing down the inductive) *)
Record inductive_arity := {
  ind_user_arity : term; (* the full arity *)
  ind_sort : sort        (* just the sort *)
}.

Fixpoint ind_get_sort (arity : term) : sort := 
  match arity with 
  | tSort s => s
  | tLetIn _ _ _ t => ind_get_sort t
  | tProd _ _ t => ind_get_sort t
  | _ => Universe.lProp (* TODO: this is an error *)
  end.

(* decompose a term prefixed by prods/lets into the context given by the declarations and the remaining term *)
Definition decompose_let_prod_env (t : term) : context * term := 
  let decomp := fix decomp (t : term) (acc : context) := 
    match t with 
    | tProd na ty t => 
        decomp t (mkdecl na None ty :: acc)
    | tLetIn na def ty t => 
        decomp t (mkdecl na (Some def) ty :: acc)
    | _ => (acc, t)
    end
  in decomp t []. 

(* decompose the type of an inductive into the parameter context (parameters) and the arity *)
Definition decompose_arity (t : term) (nparams : nat) : context * inductive_arity.
pose (typ := decompose_prod t).
destruct typ as [[names types] ar].
apply (List.firstn nparams) in names.
apply (List.firstn nparams) in types.
split.
refine (List.rev (map (fun '(x, ty) => vass x ty) (combine names types))). 
constructor.
exact ar. exact (ind_get_sort ar). 
Defined. 

Inductive test : nat -> let a := 1 in nat -> Type := .  

(*mutual_inductive_body*)
Definition mind_specif := mutual_inductive_body * one_inductive_body. 

(** Arity sort and original user arity Ui*)
Definition ind_arity (i : mind_specif) := 
  let (mib, oib) := i in 
  snd (decompose_arity (oib.(ind_type)) mib.(ind_npars)). 
Definition param_ctxt (i : mind_specif) := 
  let (mib, oib) := i in 
  fst (decompose_arity (oib.(ind_type)) mib.(ind_npars)). 

Definition user_arity_ctxt (user_arity : term) := 
  fst (decompose_let_prod_env user_arity).

(** Arity context of [Ii] with parameters: [forall params, Ui] *)
(* NOTE: does also contain lets and indices! *)
Definition ind_arity_ctxt (i : mind_specif) := 
  let (mib, oib) := i in 
  let (param_ctx, ar) := (decompose_arity oib.(ind_type) mib.(ind_npars)) in
  (user_arity_ctxt (ar.(ind_user_arity))) ++ param_ctx. 


(** Names of the constructors: [cij] *)
Definition ind_consnames (i : mind_specif) := 
  map (fun '(na, _, _) => na) (snd i).(ind_ctors). 

(** Types of the constructors with parameters:  [forall params, Tij],
     where the Ik are replaced by de Bruijn index in the
     context I1:forall params, U1 ..  In:forall params, Un *)
Definition ind_user_lc (i : mind_specif) : list term := 
  map (fun '(_, ty, _) => ty) (snd i).(ind_ctors).

(* Number of expected real arguments of the type (no let, no params), i.e. indices *)
Definition ind_nrealargs (i : mind_specif) : nat := 
  let user_arity := (ind_arity i).(ind_user_arity) in
  let count_nonlets := fix r (t : term) := 
    match t with 
    | tLetIn _ _ _ t => r t
    | tProd _ _ t => 1 + r t
    | _ => 1
    end
  in count_nonlets user_arity. 

(* length of realargs context (with let, no params), i.e. indices + lets *)
Definition ind_nrealdecls (i : mind_specif) := 
  let (mib, oib) := i in
  let (_, ar) := decompose_arity oib.(ind_type) mib.(ind_npars) in
  length (user_arity_ctxt (ar.(ind_user_arity))). 

(* number of expected real arguments of constructors (without params, without lets) *)
Definition ind_ctors_nrealargs (i : mind_specif) : list nat := 
  map (fun '(_, _, n) => n) (snd i).(ind_ctors). 

(* length of the signature of the constructors (with let, without params) *)
Definition ind_ctors_nrealdecls (i : mind_specif) : list nat := 
  let (mib, oib) := i in 
  let npars := mib.(ind_npars) in 
  map (fun '(_, ty, _) => 
    let (_, ar) := decompose_arity ty npars in length (user_arity_ctxt ar.(ind_user_arity)))
  oib.(ind_ctors).


(* TODO factorize in Environment *)
(* was mind_decl_to_entry *)
Definition mind_body_to_entry (decl : mutual_inductive_body)
  : mutual_inductive_entry.
Proof.
  refine {| mind_entry_record := None; (* not a record *)
            mind_entry_finite := Finite; (* inductive *)
            mind_entry_params := _ (* Should be ind_params, but translations are broken: for Simon decl.(ind_params) *);
            mind_entry_inds := _;
            mind_entry_universes := universes_entry_of_decl decl.(ind_universes);
            mind_entry_variance := decl.(ind_variance);
            mind_entry_private := None |}.
  - (* FIXME: this is wrong, the info should be in ind_params *)
   refine (match List.hd_error decl.(ind_bodies) with
  | Some i0 => _
  | None => nil (* assert false: at least one inductive in a mutual block *)
  end).
  apply (param_ctxt (decl, i0)). 
  - refine (List.map _ decl.(ind_bodies)).
    intros [].
    refine {| mind_entry_typename := ind_name;
              mind_entry_arity := remove_arity decl.(ind_npars) ind_type;
              mind_entry_template := false;
              mind_entry_consnames := _;
              mind_entry_lc := _;
            |}.
    refine (List.map (fun x => fst (fst x)) ind_ctors).
    refine (List.map (fun x => remove_arity decl.(ind_npars)
                                                (snd (fst x))) ind_ctors).
Defined.

Fixpoint decompose_prod_assum (Γ : context) (t : term) : context * term :=
  match t with
  | tProd n A B => decompose_prod_assum (Γ ,, vass n A) B
  | tLetIn na b bty b' => decompose_prod_assum (Γ ,, vdef na b bty) b'
  | tCast t _ _ => decompose_prod_assum Γ t
  | _ => (Γ, t)
  end.

Fixpoint strip_outer_cast t :=
  match t with
  | tCast t _ _ => strip_outer_cast t
  | _ => t
  end.

Fixpoint decompose_prod_n_assum (Γ : context) n (t : term) : option (context * term) :=
  match n with
  | 0 => Some (Γ, t)
  | S n =>
    match strip_outer_cast t with
    | tProd na A B => decompose_prod_n_assum (Γ ,, vass na A) n B
    | tLetIn na b bty b' => decompose_prod_n_assum (Γ ,, vdef na b bty) n b'
    | _ => None
    end
  end.

Lemma decompose_prod_n_assum_it_mkProd ctx ctx' ty :
  decompose_prod_n_assum ctx #|ctx'| (it_mkProd_or_LetIn ctx' ty) = Some (ctx' ++ ctx, ty).
Proof.
  revert ctx ty. induction ctx' using rev_ind; move=> // ctx ty.
  rewrite app_length /= it_mkProd_or_LetIn_app /=.
  destruct x as [na [body|] ty'] => /=;
  now rewrite !Nat.add_1_r /= IHctx' -app_assoc.
Qed.

Definition is_ind_app_head t :=
  match t with
  | tInd _ _ => true
  | tApp (tInd _ _) _ => true
  | _ => false
  end.

Lemma is_ind_app_head_mkApps ind u l : is_ind_app_head (mkApps (tInd ind u) l).
Proof. now destruct l; simpl. Qed.

Lemma decompose_prod_assum_it_mkProd ctx ctx' ty :
  is_ind_app_head ty ->
  decompose_prod_assum ctx (it_mkProd_or_LetIn ctx' ty) = (ctx' ++ ctx, ty).
Proof.
  revert ctx ty. induction ctx' using rev_ind; move=> // ctx ty /=.
  destruct ty; simpl; try (congruence || reflexivity).
  move=> Hty. rewrite it_mkProd_or_LetIn_app /=.
  case: x => [na [body|] ty'] /=; by rewrite IHctx' // /snoc -app_assoc.
Qed.

Definition isConstruct_app t :=
  match fst (decompose_app t) with
  | tConstruct _ _ _ => true
  | _ => false
  end.
