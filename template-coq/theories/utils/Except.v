From MetaCoq.Template Require Export monad_utils.
From MetaCoq.Template Require Import utils.
(* we work in the sum monad to handle all the error stuff *)
Export MonadNotation.


Instance sum_exc : MonadExc string (fun m => (m + string)%type)  :=
  {| 
    raise := fun T e => @inr T string e;
    catch := fun T x f => 
      match x with 
      | inl x => inl x 
      | inr y => f y
      end
  |}. 

Instance sum_monad {Y}: Monad (fun X => X + Y)%type := 
  {| 
    ret := fun T t => inl t;
    bind := fun T U x f => 
      match x with 
      | inl x => f x
      | inr y => inr y
      end
  |}. 

Definition except {X Y: Type} (def : Y) (x : option X) : X + Y := 
  match x with 
  | Some x => inl x
  | None => inr def
  end.
Definition raise {X Y : Type} (def : Y) : X + Y := inr def. 
Notation "'exc' A" := ((A + string)%type) (at level 100). 

Notation "f '$' a" := (f (a)) (at level 99, only parsing). 

Class ExcUnwrap (Xl : Type -> Type) := exc_unwrap X : Xl (exc X) -> exc (Xl X).
Arguments exc_unwrap {_ _ _}. 

Fixpoint list_unwrap {X : Type} (l : list (exc X)) : exc (list X) := 
  match l with 
  | [] => ret []
  | x :: l => 
      x <- x ;;
      l <- list_unwrap l;;
      ret (x :: l)
  end.
Instance: ExcUnwrap list := @list_unwrap. 

