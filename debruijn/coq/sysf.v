Require Import Coq.Arith.Arith.
Require Import Omega.

Set Warnings "-notation-overridden".
From Coq Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "Strict Subproofs".

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Require Import Coq.Lists.List.

Fixpoint idx {a} ( n : nat ) (ts : list a ) : option a :=
  match n , ts with 
  | 0 , (t :: _) => Some t
  | S m, (_ :: ts') => idx m ts'
  | _ , nil => None
  end.

Lemma fIdx : forall {a}{b} (f:a -> b) n y ts, 
    idx n ts = Some y ->
    idx n (map f ts) = Some (f y).
Proof.
  induction n; destruct ts; simpl; try done.
  - intros h; inversion h; done.
  - intros h; eauto.
Qed. 

Inductive Ty :=
  | BaseTy : Ty
  | VarTy  : nat -> Ty
  | FnTy   : Ty -> Ty -> Ty
  | PolyTy : Ty -> Ty.

(* renamings *)

(* A renaming is a map from variables to variables *)    
Inductive renaming := 
  | Succ : renaming 
  | Lift : renaming -> renaming
.

(* Apply a renaming to a variable *)
(* RTmL *)
Fixpoint applyr (r0 : renaming) : nat -> nat := 
   match r0 with
   | Succ => S
   | Lift r => fun n => match n with
          | 0 => 0
          | S n => S (applyr r n)
          end
   end.

Fixpoint rename (r : renaming) ct :=
  match ct with 
  | BaseTy => BaseTy
  | VarTy k => VarTy (applyr r k)
  | FnTy args ret => 
    FnTy (rename r args) (rename r ret)
  | PolyTy ret => PolyTy (rename (Lift r) ret)
  end.

Inductive sub := 
  | Id   : sub
  | Tail : sub -> sub
  | Cons : Ty -> sub -> sub
. 

Fixpoint applys (s : sub) : nat -> Ty := 
  match s with 
    | Id        => fun x => VarTy x
    | Tail s    => fun x => applys s (S x)
    | Cons e s  => 
      fun x => 
        match x with 
        | 0 => e
        | S m => applys s m
        end
end.


Definition lift (s : sub) : sub :=
  Cons (VarTy 0) (rename Lift s).



Fixpoint subst (r : sub) ct :=
  match ct with 
  | BaseTy => BaseTy
  | VarTy k => applys r k
  | FnTy args ret => 
    FnTy (subst r args) (subst r ret)
  | PolyTy ret => PolyTy (subst r (rename ret)
  end.

Fixpoint compose s s' := 
  match s' with 
  |  Id => s
  |  Succ s2 =>  Succ (compose s s2)
  |  Cons ty s2 => Cons (subst s ty) (compose s s2)
end.

Definition tail s := compose s Succ.

