

Module list.
Inductive list (X : Type) : Type := 
  | nil : list X
  | cons (x : X) (l : list X) : list X. 

Fixpoint length {X} (l : list X) := 
  match l with 
  | nil _ => 0
  | cons _ x l' => S (length l')
  end.

(* What do we do when we want to check guardedness?
1. Infer recursive structure (done by the positivity checker in the kernel)
  μ Xl. { {[list:] {[nil:] }, {[cons:] ⊥, Xl} } }.1

2. Check the fixpoint. start out with (l : list X) with recursive structure Subterm(Large, L) for l.
  1) In the first branch of the match, we don't need to check anything.
  2) In the second branch of the match, 
      (x : X) with rec. structure Not_subterm 
      (l' : list X) with rec. structure Subterm(Strict, L) should be introduced.
    For the recursive call to length, we just need to make sure that l is strict, which is the case.
*)

(* What happens for nested matches? *)
Fixpoint weird_length {X} (l :list X) := 
  match l with
  | nil _ => 0
  | cons _ x l' => 
      match l with 
      | nil _ => 1
      | cons _ y l'' => S (S (length l''))
      end
  end.
(* 
1. infer L
2. 
  1) first branch same as before. 
  2) for the second branch of the match:
      (x : X) Not_subterm
      (l' : list X) Subterm(Strict, L)
      then another match:
      1) first branch: nothing interesting
      2) second branch
        (y : X) Not_subterm
        (l'' : list X) Subterm(Strict, L) as l' is already a strict subterm
        now the check for the recursive call goes through as l'' is a strict subterm in the env
*)



End list. 

From MetaCoq.Template Require Import Environment utils.RTree Ast AstUtils. 
Open Scope string_scope.
Require Import List String.
Import ListNotations.
Open Scope string_scope.

Module kernel_lists.
(* Kernel representation of lists *)
Definition list_indname : inductive := 
  {|
   inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list");
   inductive_ind := 0 
  |}.
  
Definition list_recargs : wf_paths := 
  Rec 0 [ Node (Mrec list_indname) [ Node Norec []; Node Norec [ Node Norec []; 
                                                                 Param 0 1]
                                   ]
        ].
Eval cbn in (expand (list_recargs)). 

(*Inductive test := *)
  (*| abc : let a := 10 * 10 in nat -> test. *)

(*Eval hnf in let a := 10 * 10 in nat -> test.*)

Print one_inductive_body.
(* I don't really care about universes, just use Set everywhere *)

Definition list_indbody : one_inductive_body := 
  {| 
    ind_name := "list";
    ind_type := tProd {| binder_name := nNamed "A"; binder_relevance := Relevant |}
                      (tSort (Universe.of_levels (inr (Level.Level "Coq.Init.Datatypes.60"))))
                      (tSort (Universe.from_kernel_repr (Level.lSet, false) [(Level.Level "Coq.Init.Datatypes.60", false)]));
    ind_kelim := InType;
    ind_ctors := [("nil", tProd {|
                               binder_name := nNamed "A";
                               binder_relevance := Relevant |}
                             (tSort
                                (Universe.of_levels
                                   (inr
                                      (Level.Level "Coq.Init.Datatypes.60"))))
                             (tApp (tRel 1) [tRel 0]), 0);
                          ("cons",
                          tProd
                            {|
                            binder_name := nNamed "A";
                            binder_relevance := Relevant |}
                            (tSort
                               (Universe.of_levels
                                  (inr
                                     (Level.Level "Coq.Init.Datatypes.60"))))
                            (tProd
                               {|
                               binder_name := nAnon;
                               binder_relevance := Relevant |} 
                               (tRel 0)
                               (tProd
                                  {|
                                  binder_name := nAnon;
                                  binder_relevance := Relevant |}
                                  (tApp (tRel 2) [tRel 1])
                                  (tApp (tRel 3) [tRel 2]))), 2)];
               ind_projs := [];
               ind_relevance := Relevant;
               ind_recargs := list_recargs |}. 



(* I don't care about universes. *)
Definition univdecl := Monomorphic_ctx
                   (LevelSetProp.of_list
                      [Level.Level "Coq.Init.Datatypes.60"],
                   ConstraintSet.empty).


Definition list_param_ctxt := 
[{|
   decl_name := {|
                binder_name := nNamed "A";
                binder_relevance := Relevant |};
   decl_body := None;
   decl_type := tSort
                  (Universe.of_levels
                     (inr (Level.Level "Coq.Init.Datatypes.60"))) |}].
Definition list_mindbody : mutual_inductive_body := 
  {| 
    ind_bodies := [list_indbody];
    ind_finite := Finite;
    ind_npars := 1;
    (*ind_npars_unif := 1;*)
    ind_params := list_param_ctxt;
    ind_universes := univdecl;
    ind_variance := None;
  |}.


Compute (ind_arity (list_mindbody, list_indbody)). 

Compute (ind_arity_ctxt (list_mindbody, list_indbody)). 
Compute (ind_consnames (list_mindbody, list_indbody)).
Compute (ind_user_lc (list_mindbody, list_indbody)). 
Compute (ind_nrealargs (list_mindbody, list_indbody)). 
Compute (ind_nrealdecls (list_mindbody, list_indbody)).


Compute (ind_ctors_nrealdecls (list_mindbody, list_indbody)).

(*Compute (mind_body_to_entry list_mindbody).*)

End kernel_lists.


Require Import Lia. 
Lemma A1 (n m : nat) : n > m -> n >= m. 
Proof. lia. Qed.
Fixpoint test (n : nat) : forall m, n > m -> n >= m := 
  fun m H => 
  match n return forall m, n > m -> n >= m with 
  | 0 => fun m H => A1 0 m H
  | S n => fun m (H : S n > m) => let a1 := test n m in A1 (S n) m H
  end m H.


Hypothesis (p : nat -> Prop). 
Hypothesis (H0 : forall n, p n -> p (S n)). 
Fixpoint test7 (n : nat) := 
  fun H =>
  match n return forall (H: forall m, p m), p n with
  | 0 => fun H => H 0
  | S n => fun H => H0 n (test7 n H)
  end H. 

Fixpoint test2 (n : nat) : forall m, n > m -> n >= m := 
  fun m H => 
  match n return forall m, n > m -> n >= m with 
  | 0 => fun m H => A1 0 m H
  | S n => 
      fun m => 
        match m return (S n > m -> S n >= m) with 
        | 0 => fun H => (* 0 >= 0 *) 
        | S m => fun H => 
        end
      
      fun m (H : S n > m) => let a1 := test n m in A1 (S n) m H
  end m H.






















Fixpoint fib (n : nat) := 
  match n with 
  | 0 => 1 
  | 1 => 1 
  | S (S n as n') => fib n + fib n'
  end.
(* works in the same way as the nested match above *)
  



(* some attempt at coming up with mutual inductives *)
Inductive even : nat -> Type := 
  | even0 : even 0
  | evenS n : odd n -> even (S n)
  | evenSS n : even n -> even (S (S n))
with odd : nat -> Type := 
  | oddS n : even n -> odd (S n).

Check even_ind. 

Fixpoint count_cons_even n (e : even n) : nat := 
  match e with 
  | even0 => 1
  | evenS n' o => 1 + count_cons_odd n' o 
  | evenSS n e => 1 + count_cons_even n e
  end
with count_cons_odd n (o : odd n) : nat := 
  match o with 
  | oddS n e => 1 + count_cons_even n e
  end.

(* What do we do when we want to check guardedness?
1. Infer recursive structure (done by the positivity checker in the kernel)
  even: 
    μ Xe Xo. { {[even:] {[even0:] }, {[evenS:] ⊥, Xo}, {[evenSS:] ⊥, Xe} }, 
               {[odd:]  {[oddS:] ⊥, Xe} }
             }.1
    in Coq's kernel syntax:
    E := 
    Rec 1 {| Node (MRec even) [| Node Norec [| |], 
                                 Node Norec [| Node Norec [| |], 
                                               Param (0, 2)
                                            |], 
                                 Node Norec [| Node Norec [| |], 
                                               Param (0, 1)
                                            |]
                              |], 
             Node (MRec odd)  [| Node Norec [| Node Norec [| |], 
                                               Param (0, 1)
                                            |]
                              |]
          |}

  odd:  (same as even, just change indices in toplevel Rec 
    μ Xe Xo. { {[even:] {[even0:] }, {[evenS:] ⊥, Xo}, {[evenSS:] ⊥, Xe} }, 
               {[odd:]  {[oddS:] ⊥, Xe} }
             }.2
    O := 
    Rec 2 {| Node (MRec even) [| Node Norec [| |], 
                                 Node Norec [| Node Norec [| |], 
                                               Param (0, 2)
                                            |], 
                                 Node Norec [| Node Norec [| |], 
                                               Param (0, 1)
                                            |]
                              |], 
             Node (MRec odd)  [| Node Norec [| Node Norec [| |], 
                                               Param (0, 1)
                                            |]
                              |]
          |}


2. We have to check count_cons_even and count_cons_odd _mututally_ !
Check count_cons_even:
  We start with the env { (e : even n) at Subterm(Large, E), (n:nat) at No_subterm }
  We encounter the match and check each of the branches. For that, we traverse the tree E. 
    -- When we encounte the recursive occurrence (Param), we have to unfold the tree one more step.
  1) evenO: nothing interesting
  2) evenS: add to the environment 
    { (o : odd n') at Subterm(Strict, O), (n' : nat) at No_subterm }
    We call count_cons_odd, which is mutually defined. Since o is a strict subterm this is okay.
  3) evenSS: add to the environment
    { (e : even n') at Subterm(Strict, E), (n' : nat) at No_subterm }
    e is a strict subterm, so the rec. call is okay.

Check count_cons_odd:
  We start with env { (o :odd n) at Subterm(Large, O), (n : nat) at No_subterm}
  We encounter the match
  1) oddS: add to env
    { (e : even n') at Subterm(Strict, E), (n' : nat) at No_subterm }
    the mutually recursive call is okay as e is a strict subterm
*)


Module even_odd_kernel.
  Definition even_indname : inductive := 
    {| inductive_mind := (MPfile ["Top"], "even");
       inductive_ind := 0;
    |}.
  Definition odd_indname : inductive := 
    {| inductive_mind := (MPfile ["Top"], "even");
       inductive_ind := 1;
    |}.

  Definition even_recarg : wf_paths :=
    Rec 0 [ Node (Mrec even_indname) [ Node Norec [ ];  (* even0 *)
                                       Node Norec [ Node Norec [ ];  (* evenS *)
                                               Param 0 1
                                            ]; 
                                       Node Norec [ Node Norec [ ];  (*evenSS *)
                                               Param 0 0
                                            ]
                              ]; 
             Node (Mrec odd_indname)  [ Node Norec [ Node Norec [ ]; 
                                               Param 0 0
                                            ]
                              ]
          ]. 
  Eval cbn in (expand even_recarg). 

  Definition odd_recarg : wf_paths := 
    Rec 1 [ Node (Mrec even_indname) [ Node Norec [ ]; 
                                 Node Norec [ Node Norec [ ]; 
                                               Param 0 1
                                            ]; 
                                 Node Norec [ Node Norec [ ]; 
                                               Param 0 0
                                            ]
                              ]; 
             Node (Mrec odd_indname)  [ Node Norec [ Node Norec [ ]; 
                                               Param 0 0
                                            ]
                              ]
          ].
  Eval cbn in (expand odd_recarg). 


End even_odd_kernel.






















Fixpoint sumn (l : list nat) := 
  match l with 
  | nil => 0
  | cons x l' => x + sumn l'
  end.

Require Import List. 
Inductive rosetree (X : Type) : Type := 
  | rnode (l : list (rosetree X)) : rosetree X. 

(* 
  Recursive structure
    μ Xr. { {[rosetree:] {[rnode:] μ Xl. { {[list:] {[nil:] }, 
                                                    {[cons:] Xr, Xl}
                                           }
                                         }.1
                         }
            }
          }.1

  Coq representation
  R := 
  Rec 1 {| Node (MRec rosetree) [| Node Norec [| L |] |] |} 
  where 
  L:= Rec 1 {| Node (Imbr list) [| Node Norec [| |], 
                                   Node Norec [| Param (1, 1), Param (0, 1) |]
                                |]
            |}


  Note: for building this representation, we need to look up the rec. tree of list and substitute the
    Node Norec [| |]
  in cons (used for the element of the inner type) by the real recursive structure of rosetree.
*)

Definition rosetree_indname : inductive := 
    {| inductive_mind := (MPfile ["Top"], "rosetree");
       inductive_ind := 1;
    |}.
Definition rosetree_recarg : wf_paths := 
  Rec 0 [ Node (Mrec rosetree_indname) [ Node Norec [  
    (* inlined list recursive structure *)
    Rec 0 [ Node (Imbr kernel_lists.list_indname) [ Node Norec [ ]; 
                                       Node Norec [ Param 1 0; Param 0 0 ]
                                     ]
          ] 
  ] ] ].
Eval cbn in expand rosetree_recarg. 


Definition map_opaque {X Y: Type} (f : X -> Y) (l : list X): list Y. 
eapply map. apply f. apply l. 
Qed.

Definition sumn_opaque (l : list nat) : nat. 
apply sumn, l. 
Qed.

Fixpoint size {X} (t : rosetree X) : nat := 
  1 + 
  match t with 
  | rnode _ l => 
      (* note: here the guardedness checker must look into map -- map_opaque does not work *)
      (* however, sumn may be opaque! *)
      sumn_opaque (map size l) 
  end.


(* Check guardedness: 
  we should just be able to descend into subterms on applications. 
  only interesting subterm is the match.
  1) rnode case. add to env:
     { l : list (rosetree X) at Subterm(Strict, L) }
     where L' := 
      Rec 1 {| Node (Imbr list) [| Node Norec [| |], 
                                   Node Norec [| R, Param (0, 1) |]
                                |]
            |}
      ( I assume we want to unfold the recusive occurrence of rosetree here?)

    We enter the sumn application -- can just descend into subterms.
        (Note: If sumn is transparent, we probably still unfold the fix instead?)
    The left subterm, sumn, doesn't feature any recursive occurrence of size.
    Let's focus on map size l. 
    Just from descending into subterms, we will run into trouble as there is a recursive occurrence of size.

    So we need to unfold map and obtain something like:
      (fun (f : rosetree X -> nat) => fix map (l : list (rosetree X)) => 
        match l with 
        | nil => nil
        | cons x l' => cons (f x) (map l')
        end
      ) size l
      (partially reduced parameters)

    After more reduction:
    (fix map l => 
      match l with 
      | nil => nil
      | cons x l' => cons (size x) (map l')
      end
    ) l

    Since we apply the fix to a subterm, we may check the body of the fix under the assumption that l is a subterm (at L'). So let's do that.

    So we check guardedness of the fix:
      { map : list (rosetree X) -> list nat at No_subterm, 
        l : list (rosetree X) at Subterm(Strict, L')
      }

    encounter match
    1) first branch trivial
    2) second branch: 
        { x : rosetree X at Subterm(strict, R),
          l' : list(rosetree X) at Subterm(strict, L')
        } 
       we can now just check the subterms size x and map l' are guarded
          l' isn't really clear


    TODO: how is the nested fix really handled? I feel like its guardedness should be analyzed separately first, because the assumption that l' is a subterm of the original tree doesn't really allow us to do the recursive call of the inner fix?

    in principle we could check the nested fix first. 
then in the recursive call with l' we just need to ensure that the invariant that l' is a subterm of the original tree is upheld so that we may call size (since the subterm relation is transitive -- if we call the nested fix with a subterm, then everything is fine)

    alternative: we check it inline -- but that seems difficult because then we have some things which are a subterm of the tree and some things which are a subterm of the list with no clear distinction
*) 

(* judging from the following error message, the first thing is what seems to happen: 
    we check the nested fix first on its own and then check the propagation of subterms in the bigger fix *)
Fail Fixpoint size' {X} (t : rosetree X) : nat := 
  1 + 
  match t with 
  | rnode _ l => 
      sumn_opaque (
        (fix map (l : list (rosetree X)) := 
          match l with 
          | nil => nil
          | cons x l' => cons (size x) (map l)
          end)
        l) 
  end.

(* the following example does further demonstrate that checking the subterm flow of the outer fix is done after checking guardedness of the inner fix. 
  the error message also validates the above assumptions about what subterms are currently in the environment *)
Context {X:Type} (xt : rosetree X). 
Fail Fixpoint size' (t : rosetree X) : nat := 
  1 + 
  match t with 
  | rnode _ l => 
      sumn_opaque (
        (fix map (l : list (rosetree X)) := 
          match l with 
          | nil => nil
          | cons x l' => cons (size' xt) (map l')
          end)
        l) 
  end.















(*** something with let? *)




















(* output from coq repr on a few inductives *)



(* nrealargs = 0, nrealdecls = 1 *)
(* arityctxt = 
        [LocalDef
          ({Context.binder_name = Names.Name.Name a;
                        binder_relevance = Sorts.Relevant},
                                  (CSTR.nat._0._2 CSTR.nat._0._1), nat)]*)
Inductive testI : let a := 1 in Type := a.
Fixpoint d (t : testI) := match t with | a => 1 end. 

(* nrealargs = 1, nrealdecls = 3 *)
(* consnrealargs = consnrealdecls = [0] *)
(* arityctxt = 
[LocalDef
          ({Context.binder_name = Names.Name.Name b;
            binder_relevance = Sorts.Relevant},
          (CSTR.nat._0._2 (CSTR.nat._0._2 CSTR.nat._0._1)), nat);
         LocalAssum
          ({Context.binder_name = Names.Name.Anonymous;
            binder_relevance = Sorts.Relevant},
          nat);
         LocalDef
          ({Context.binder_name = Names.Name.Name a;
            binder_relevance = Sorts.Relevant},
            (CSTR.nat._0._2 CSTR.nat._0._1), nat)] *)
Inductive testJ : let a := 1 in nat -> let b := 2 in Type := aJ : testJ 5.
Fixpoint e n (t : testJ n) := match t with | aJ => 1 end. 



(* nrealargs = 1, nrealdecls = 3 *)
(* arity_ctxt = 
        [LocalDef
          ({Context.binder_name = Names.Name.Name b;
            binder_relevance = Sorts.Relevant},
          (CSTR.nat._0._2 (CSTR.nat._0._2 CSTR.nat._0._1)), nat);
         LocalAssum
          ({Context.binder_name = Names.Name.Anonymous;
            binder_relevance = Sorts.Relevant},
          nat);
         LocalDef
          ({Context.binder_name = Names.Name.Name a;
            binder_relevance = Sorts.Relevant},
          (CSTR.nat._0._2 CSTR.nat._0._1), nat);
         LocalAssum
          ({Context.binder_name = Names.Name.Name n;
            binder_relevance = Sorts.Relevant},
          nat)]
          *)
Inductive testK (n : nat) : let a := 1 in nat -> let b := 2 in Type := aK : testK n 5.
Fixpoint f n (t : testK n n) := match t with | aK _ => 1 end. 
