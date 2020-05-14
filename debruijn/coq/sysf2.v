Require Import Coq.Arith.Arith.
Require Import Omega.

Set Warnings "-notation-overridden".
From Coq Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "Strict Subproofs".

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

(* ---------------------------------------------------- *)
(* Helper *)

Fixpoint repeat  {k : Type} (a : k -> k) (n:nat) ( x : k) : k :=
  match n with 
  | 0   => x
  | S m => a (repeat a m x)
end. 

Lemma repeat_repeat : forall {A} n n0 f (x:A),
  repeat f n (repeat f n0 x) = repeat f (n + n0) x.
Proof.
  induction n.
  - intros; simpl; auto. 
  - intros; simpl; auto.
    rewrite IHn. auto.
Qed.

(* ---------------------------------------------------- *)

(* The following is a de Bruijn formalization of substitution operations
   for polymorphic types. 

   It is inspired by 
      Strongly Typed Term Representations in Coq
      Nick Benton · Chung-Kil Hur ·
      Andrew Kennedy · Conor McBride

   Main differences are: 
     - doesn't use a strongly-typed term representation
     - defunctionalized
     - we show equivalence with rename/subst so we only have to 
       implement one operation.
*)

(* Minimized version of Crucible types *)
Inductive Ty := 
  | BaseTy   : Ty
  | VarTy    : nat -> Ty
  | FnTy     : Ty -> Ty -> Ty
  | PolyTy   : Ty -> Ty.

(* ---------------------------------------------------- *)

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
    FnTy (rename r args)
           (rename    r ret)

  | PolyTy ret =>
    PolyTy (rename    (Lift r) ret)
  end.

(* --------------------------------------- *)


(*
Lemma ApplyRcR : forall r1 r2 x, 
    applyr (compr r1 r2) x = 
    applyr r1 (applyr r2 x).
Proof.
  intros r1. induction r1; intros; 
  intros. destruct x. simpl. auto.
  simpl. auto.
Qed.

Lemma ApplyLiftRcR : forall x r1 r2, 
  applyr (Lift (Comp r1 r2)) x = 
  applyr (Comp (Lift r1) (Lift r2)) x.
Proof.
  destruct x. intros r1 r2. simpl. auto.
  intros r1 r2. simpl. auto.
Qed.


Lemma ApplyLiftnRcR : forall n x r1 r2, 
  applyr (repeat Lift n (Comp r1 r2)) x = 
  applyr (Comp (repeat Lift n r1) (repeat Lift n r2)) x.
Proof.
  induction n. simpl. auto.
  intros. simpl.
  destruct x. auto.
  rewrite IHn. 
  rewrite ApplyRcR.
  auto.
Qed.

Lemma LiftRcR : 
  (forall x n r1 r2, 
      rename (repeat Lift n (Comp r1 r2)) x = 
      rename (Comp (repeat Lift n r1) (repeat Lift n r2)) x) /\
  (forall x n r1 r2, 
      renameCtx (repeat Lift n (Comp r1 r2)) x = 
      renameCtx (Comp (repeat Lift n r1) (repeat Lift n r2)) x).
Proof. 
  eapply both.
  all: try solve [intros; simpl; auto].
  all: try solve [intros; simpl; rewrite H; rewrite H0; auto].
  - intros k n. simpl. 
    intros r1 r2. 
    rewrite ApplyLiftnRcR.
    rewrite ApplyRcR.
    auto.
  - intros. 
    simpl. 
    f_equal.
    rewrite repeat_repeat.
    rewrite H. 
    rewrite H.
    rewrite repeat_repeat.
    rewrite repeat_repeat. auto.
    rewrite repeat_repeat.
    rewrite H0. 
    rewrite H0.
    rewrite repeat_repeat.
    rewrite repeat_repeat. auto.
Qed.

Lemma ActRcR : 
  (forall x r1 r2, 
    rename (Comp r1 r2) x = rename r1 (rename r2 x)) /\
  (forall x r1 r2, 
    renameCtx (Comp r1 r2) x = renameCtx r1 (renameCtx r2 x)).
Proof.
  eapply both.
  all: try solve [intros; simpl; auto].
  all: try solve [intros; simpl; rewrite H; rewrite H0; auto].
  intros.
  simpl.
  destruct  LiftRcR as [h0 h1].
  rewrite h0. rewrite h1.
  rewrite H. rewrite H0.
  auto.
Qed.
*)


Lemma applyr_rename : 
  forall k s1 s2, 
   (forall k, applyr s1 k = applyr s2 k) ->
   rename s1  k = rename s2 k.
Abort.            

(* --------------------------------------- *)


Inductive sub := 
  (* Identity sus *)
  | IdSub   : sub
  | SuccSub  : sub 
  (* 0 -> ty, then apply the rest *)
  | ConsSub : Ty -> sub -> sub
  | LiftSub : sub -> sub
  | TailSub : sub -> sub 
. 

  
(* Apply a substitution to a variable *)
(* STmL s == applys (LiftSub s) *)
Fixpoint applys (s : sub) : nat -> Ty := 
  match s with 
    | IdSub        => 
      fun x => VarTy x
    | SuccSub        => 
      fun x => VarTy (S x)
    | ConsSub e s  => 
      fun x => 
        match x with 
        | 0 => e
        | S m => applys s m
        end
    | LiftSub s =>
      fun x => 
        match x with 
        | 0 => VarTy 0
        | S m => rename Succ (applys s m)
        end
    | TailSub s => 
      fun x => applys s (S x) 
end.


(* ----------------- *)


Fixpoint subst (r : sub) ct :=
  match ct with 
  | BaseTy => BaseTy
  | VarTy k => applys r k
  | FnTy args ret => 
    FnTy (subst r args) (subst r ret)
  | PolyTy ret =>
    PolyTy (subst (LiftSub r) ret)
  end.

(* Defined operations *)

Definition headSub (s : sub) : Ty := applys s 0.
Definition succSub : sub := TailSub IdSub.

Fixpoint composeSub s s' := 
  match s' with 
  |  IdSub => s
  |  SuccSub => TailSub s
  |  ConsSub ty s2 => ConsSub (subst s ty) (composeSub s s2)
  |  LiftSub s2 => ConsSub (applys s 0) (TailSub (composeSub s s2))
  |  TailSub s2 => TailSub (composeSub s s2)
end.

(*  composeSub s (LiftSub s2) 
    [=] composeSub s (ConsSub (VarTy 0) (composeSub SuccSub s2)) 
    [=] ConsSub (subst s (VarTy 0)) (composeSub s (composeSub SuccSub s2))
    [=] ConsSub (subst s (VarTy 0)) (composeSub s (TailSub s2))
    [=] ConsSub (subst s (VarTy 0)) (TailSub (composeSub s s2))  *)

Definition equiv (s1 s2 : sub) := forall x, applys s1 x = applys s2 x.

Infix "[=]" := equiv (at level 99).

Instance: Equivalence equiv.
Proof. split; unfold equiv.
       - intros x y. auto.
       - intros x y z. auto.
       - intros x y z q r m. rewrite q. rewrite r. auto.
Qed.


(* --------------- basic equivalences ------------------ *)

(* We define equivalence between substitutions extensionally. *)

(* Some simple equivalences *)
Lemma equiv_tail_cons h ss : TailSub (ConsSub h ss) [=] ss.
Proof. intro x. destruct x. simpl. auto. simpl. auto. Qed.

Lemma etaSub s : s [=] ConsSub (headSub s) (TailSub s).
Proof. intros x. destruct x; simpl; auto. Qed.

Lemma idSub_def : IdSub [=] (ConsSub (VarTy 0) SuccSub).
Proof. intros x. unfold succSub. destruct x; simpl; auto. Qed.

Lemma tailSub_def s : TailSub s [=] composeSub s SuccSub. 
Proof. intros x. unfold succSub; simpl. auto. Qed.




(* ------------ well scopededness of renamings and shifts ------------- *)

(* In this section we do some sanity checking. We make sure that everything 
   stays well scoped. *)

Definition ScopedVar : nat -> nat -> Prop :=
  fun n k => k < n.

Inductive Scoped : nat -> Ty -> Prop :=
  | ScopedBaseTy : forall n, 
      Scoped n BaseTy
  | ScopedVarTy  : forall n k, 
      ScopedVar n k -> 
      Scoped n (VarTy k)
  | ScopedFnTy   : forall n a r,
      Scoped n a -> Scoped n r -> 
      Scoped n (FnTy a r)
  | ScopedPolyTy : forall n r, 
      Scoped (S n) r -> 
      Scoped n (PolyTy r).

Hint Constructors Scoped.

(* A renaming can be scoped. *)
Definition Ren r n n' := forall k, ScopedVar n k -> ScopedVar n' (applyr r k).


(* Lifting a renaming increases its scope by one *)
Lemma renaming_Lift : forall r n n', 
    Ren r n n' -> Ren (Lift r) (S n) (S n').
Proof.
  intros.
  unfold Ren, ScopedVar in *.
  intros k. 
  destruct k; simpl. omega.
  intros h. apply lt_S_n in h.
  apply lt_n_S. auto.
Qed.

Lemma rename_Scoped : 
  (forall ct, forall r n n', Ren r n n' -> Scoped n ct  -> Scoped n' (rename r ct)).
Proof.
  intro ct. induction ct; intros ; simpl; eauto.
  - inversion H0.  eauto. 
  - inversion H0. eauto.
  - inversion H0.
    econstructor; eauto using renaming_Lift.
Qed.

Lemma Ren_Succ : 
  forall n, Ren Succ n (S n).
Proof.
  intros.
  unfold Ren.
  unfold ScopedVar.
  intros k h.
  simpl.
  omega.
Qed.

(* Substitutions can be well-scoped *)
Definition Sub s n n' :=
  forall k, ScopedVar n k -> Scoped n' (applys s k).


Lemma shift_Scoped: forall n ct,
  Scoped n ct -> Scoped (1 + n) (rename Succ ct).
Proof. 
  intros.
  eapply rename_Scoped; eauto.
  unfold Ren, ScopedVar.
  intros. 
  simpl.
  omega.
Qed.


Lemma Scoped_shiftSubst : forall s n n',
  Sub s n n' -> Sub (LiftSub s) (1 + n) (1 + n').
Proof.
  intros. simpl. unfold Sub in *. 
  intros k h.
  destruct k; simpl.
  econstructor. 
  unfold ScopedVar in *. 
  omega.
  eapply shift_Scoped.
  apply lt_S_n in h.
  eapply H.
  eauto.
Qed.

Lemma subst_Scoped : 
  (forall ct, forall r n n', Sub r n n' -> Scoped n ct  -> Scoped n' (subst r ct)).
Proof.
  intro ct; induction ct; intros; simpl; eauto.
  - inversion H0.  eauto. 
  - inversion H0. eauto.
  - inversion H0.
    econstructor; eauto
    using Scoped_shiftSubst.
Qed.

Lemma Sub_IdSub : forall n, Sub IdSub n n.
Proof.
  intro n.
  unfold Sub.
  simpl.
  intros k h.
  econstructor.
  auto.
Qed.

Lemma Sub_ConsSub : forall s m n ty, 
        Scoped n ty -> 
        Sub s m n -> Sub (ConsSub ty s) (S m) n.
Proof.
  intros.
  unfold Sub in *.
  intros k h.
  unfold ScopedVar in *.
  simpl.
  destruct k. auto.
  apply lt_S_n in h. auto.
Qed.

Lemma Sub_TailSub : forall s m n, 
        Sub s (S m) n -> Sub (TailSub s) m n.
Proof.
  intros.
  unfold Sub in *.
  intros k h.
  unfold ScopedVar in *.
  simpl.
  destruct k. 
  destruct m. omega. eapply H. omega.
  destruct m. omega.
  eapply H.
  omega.
Qed.

Lemma Sub_LiftSub : forall s m n, Sub s m n -> Sub (LiftSub s) (S m) (S n).
Proof. 
  intros.
  unfold Sub in *.
  simpl.
  unfold ScopedVar in *.
  intros k h.
  destruct k.
  + econstructor. unfold ScopedVar. omega.
  + apply lt_S_n in h.
    eapply rename_Scoped.
    eapply Ren_Succ; eauto.
    eauto.
Qed.

Lemma Sub_composeSub : forall  g f m n p, Sub f n p -> Sub g m n -> Sub (composeSub f g) m p.
Proof.
  induction g; unfold Sub, ScopedVar in *; intros; simpl in *.
  - eapply H. specialize (H0 k H1). 
    inversion H0. unfold ScopedVar in *. auto.
  - specialize (H0 k H1). inversion H0. auto.
  - destruct k eqn:EK.
    + specialize (H0 0 H1).
      eapply subst_Scoped; eauto 1.
    + destruct m.  inversion H1. eapply lt_S_n in H1. 
      eapply IHg; eauto 1.
      intros k0 LM. specialize (H0 (S k0) ltac:(omega)). 
      simpl in H0.
      auto.
  - specialize (H0 k H1).  
    destruct k eqn:EK.
    inversion H0. unfold ScopedVar in H4. eauto.
    destruct m.  inversion H1. eapply lt_S_n in H1. 
    eapply IHg with (m := S m); eauto 1.
    intros k0 LT.
    admit.
Admitted.

(* ------------------------------------------------------ *)
(* ------------------------------------------------------ *)

(* In this section, we almost prove the property that we need 
   about composition.  *)



Lemma applys_Lift_tail : forall n0 s1 n,
 applys (repeat LiftSub n0 (TailSub s1)) n =
 applys (repeat LiftSub n0 s1) (applyr (repeat Lift n0 Succ) n).
Proof.
  induction n0.
  - intros; simpl. auto.
  - intros. simpl. destruct n. auto.
    rewrite IHn0.
    auto.
Qed.
Lemma Lift_tail :  
 (forall c0 n s1, subst (repeat LiftSub n (TailSub s1)) c0 =
       subst (repeat LiftSub n s1) (rename (repeat Lift n Succ) c0)).
Proof.
  intro c0; induction c0.
  all: intros; simpl; auto.
  - eapply applys_Lift_tail.
  - f_equal; eauto.
  - f_equal. 
    pose k:= (IHc0 (S n) s1). simpl repeat in k.
    auto.
Qed.

Lemma TailSub_compose : 
  (forall x, forall s1, subst (TailSub s1) x = subst s1 (rename Succ x)).
Proof.
  intro x. induction x.
  all: intros; simpl; auto.
  - f_equal; eauto.
  - f_equal.
    pose k := (Lift_tail x 1). simpl repeat in k.
    auto.
Qed.    

(* This is *almost* the property that we need for composeSub. *)
Lemma ApplyScS : forall s2 s1 x, 
    applys (composeSub s1 s2) x = 
    subst s1 (applys s2 x).
Proof.
  induction s2.
  - intros. simpl. auto.
  - intros. simpl.
    destruct x. auto.
    auto.
  - intros. simpl.
    destruct x. auto.
    rewrite IHs2.
    auto.
  - intros. simpl.
    destruct x. auto.
    rewrite IHs2.
    rewrite TailSub_compose.
    auto.
  - intros.
    simpl.
    rewrite IHs2.
    auto.
Qed.




(* ------------------------------------------- *)

(* Can we simplify our implementation? The part with renaming is 
   only there to show that everything terminates.
*)


Fixpoint inject (r : renaming) : sub :=
  match r with 
    | Succ   => succSub
    | Lift r => LiftSub (inject r)
  end.


Lemma apply_equiv : forall r, forall x,
  VarTy (applyr r x) = applys (inject r) x.
Proof.
  induction r.
  - simpl. auto.
  - intro x. simpl.
    destruct x. auto.
    rewrite <- IHr.
    simpl.
    auto.
Qed.

Lemma Lift_inject : forall n r,
    inject (repeat Lift n r) = repeat LiftSub n (inject r).
Proof. 
  induction n.
  - simpl. auto.
  - intro r.
    simpl. 
    rewrite IHn.
    auto.
Qed.

Lemma equivS : 
  (forall ct, forall r, rename r ct    = subst    (inject r) ct).
Proof.
  intro ct. induction ct.
  all: simpl in *; auto.
  all: intro r.
  all: eauto using apply_equiv.
  f_equal; eauto.
  (* Only binding case left *)
  f_equal.
  rewrite IHct.
  simpl.
  auto.
Qed.

(* this result justifies the implementation without using rename *)

Corollary subterm_equiv:
  forall ct, rename Succ ct = subst succSub ct.
Proof. 
  intro ct.
  rewrite equivS.
  auto.
Qed.

(* ------------ more equivalences ---------------- *)


Lemma ConsSub_cong ty s1 s2 :
  s1 [=] s2 -> (ConsSub ty s1) [=] (ConsSub ty s2).
Proof.
  intros.
  unfold equiv in *.
  simpl. 
  destruct x; auto.
Qed.

Lemma ConsInj1 t1 s1 t2 s2 : 
  ConsSub t1 s1 [=] ConsSub t2 s2 -> t1 = t2.
Proof.
  intros. 
  unfold equiv in H.
  specialize (H 0).
  simpl in H.
  auto.
Qed.
Lemma ConsInj2 t1 s1 t2 s2 : 
  ConsSub t1 s1 [=] ConsSub t2 s2 -> s1 [=] s2.
Proof.
  intros H.
  unfold equiv in *.
  move=> x.
  specialize(H (S x)).
  simpl in H.
  auto.
Qed.


Lemma LiftSub_cong s1 s2 : 
  s1 [=] s2 -> (LiftSub s1) [=] (LiftSub s2).
Proof.
  intros.
  unfold equiv in *.
  simpl. 
  destruct x; auto.
  rewrite H. auto.
Qed.


Lemma TailSub_cong s1 s2 : 
  s1 [=] s2 -> TailSub s1 [=] TailSub s2.
Proof.
  intros.
  unfold equiv in *.
  simpl. 
  destruct x; auto.
Qed.

Lemma Repeatn_equiv : forall (n : nat) f (s1 s2 : sub),
      (forall s1 s2, s1 [=] s2 -> (f s1 [=] f s2)) 
    -> s1 [=] s2
    -> (repeat f n s1 [=] repeat f n s2).
Proof.
  induction n.
  + simpl. eauto.
  + intros. simpl.
    eapply H. eauto.
Qed.

Lemma Liftn_equiv : forall (n : nat) (s1 s2 : sub),
      s1 [=] s2
    -> (repeat LiftSub n s1) [=] (repeat LiftSub n s2).
Proof.
  intros.
  eapply Repeatn_equiv; eauto.
  eapply LiftSub_cong.
Qed.


Instance ConsSub_Proper : Proper (Logic.eq ==> equiv ==> equiv) ConsSub.
Proof. move=> x1 x2 EQ y1 y2 EY. subst. eapply ConsSub_cong. auto. Qed.
Instance LiftSub_Proper : Proper (equiv ==> equiv) LiftSub.
Proof. move=> x1 x2 EQ. eapply LiftSub_cong. auto. Qed.
Instance TailSub_Proper : Proper (equiv ==> equiv) TailSub.
Proof. move=> x1 x2 EQ. eapply TailSub_cong. auto. Qed.
Instance Liftn_Proper : Proper (Logic.eq ==> equiv ==> equiv) (repeat LiftSub).
Proof. move=> x1 x2 EQ y1 y2 EY.
       subst. eapply Repeatn_equiv; auto. eapply LiftSub_cong. Qed.
Instance Repeatn_Proper f : 
  Proper (equiv ==> equiv) f -> 
  Proper (Logic.eq ==> equiv ==> equiv) (repeat f).
Proof. move=> x1 x2 EQ y1 y2 EY.
subst. eapply Repeatn_equiv; auto. Qed.

(* subst respects [=] of sub *)

Lemma equiv_extend : 
    (forall x, forall s1 s2, s1 [=] s2 -> subst s1 x = subst s2 x).
Proof.
  intro x; induction x.
  all: intros; simpl; subst; eauto.
  f_equal; eauto.
  f_equal. 
  eapply IHx.
  eapply LiftSub_cong.
  auto.
Qed.


Definition subst_equiv s1 s2 := forall x, subst s1 x = subst s2 x.

Lemma equivSubst_equiv : 
  forall s1 s2, equiv s1 s2 -> subst_equiv s1 s2.
Proof. unfold subst_equiv. intros. eapply equiv_extend. eauto. Qed.

Lemma subst_Proper : 
  Proper (equiv ==> Logic.eq ==> Logic.eq) subst.
Proof. 
  move=>s1 s2 EQ y1 y2 EY.
  subst.
  eapply equivSubst_equiv.
  auto.
Qed.

Lemma subst_equiv_equiv s1 s2: 
    subst_equiv s1 s2 -> equiv s1 s2.
Proof.
  intros. unfold equiv. 
  intros x.
  specialize (H (VarTy x)).
  simpl in H.
  auto.
Qed.

Lemma LiftSub_congSubst s1 s2 : 
  subst_equiv s1 s2 -> subst_equiv (LiftSub s1) (LiftSub s2).
Proof. 
  intros h. 
  eapply equivSubst_equiv. 
  eapply LiftSub_cong. 
  eapply subst_equiv_equiv. 
  auto. 
Qed.


Lemma LiftnSubst_equiv : forall (n : nat) (s1 s2 : sub),
      subst_equiv s1 s2
    -> subst_equiv (repeat LiftSub n s1) (repeat LiftSub n s2).
induction n.
 + simpl. eauto.
 + intros. simpl.
   eapply LiftSub_congSubst. eauto.
Qed.



Lemma TailSub_congSubst s1 s2 : 
  subst_equiv s1 s2 -> subst_equiv (TailSub s1) (TailSub s2).
Proof. 
  intros h. 
  eapply equivSubst_equiv. 
  eapply TailSub_cong. 
  eapply subst_equiv_equiv. 
  auto. 
Qed.

(* ------------- id substitution property -------------- *)

Corollary Liftn_IdSub_equiv :
  forall k, (repeat LiftSub k IdSub) [=] IdSub.
Proof. 
  induction k; simpl; try reflexivity.
  rewrite IHk. intro x. destruct x; simpl; auto.
Qed. 
 
Corollary Liftn_IdSub :
  subst_equiv (LiftSub IdSub) IdSub.
Proof.
  eapply equivSubst_equiv.
  eapply (Liftn_IdSub_equiv 1).
Qed.

Lemma IdSub_id :
   (forall t, subst IdSub t = t).
Proof.
  induction t.
  all: intros; simpl; eauto.
  all: try solve [f_equal; eauto].
  f_equal. 
  pose (k := Liftn_IdSub t).
  rewrite k.
  auto.
Qed.

(* --------------------------------------------------- *)

(* Some facts about rename Succ *)

Lemma repeat_rename_commute : forall n c,
repeat (rename Succ) n (rename Succ c) =
  rename Succ (repeat (rename Succ) n c).
Proof.
  intros n c.
  replace (rename Succ c) with (repeat (rename Succ) 1 c).
  rewrite repeat_repeat. 
  replace (n+1) with (1+n).
  simpl. auto.
  omega.
  simpl. auto.
Qed.

Lemma Succ_Succ_commute : forall n c,
repeat (subst succSub) n (subst succSub c) =
  subst succSub (repeat (subst succSub) n c).
Proof.
  intros n c.
  replace (subst succSub c) with (repeat (subst succSub) 1 c).
  rewrite repeat_repeat. 
  replace (n+1) with (1+n).
  simpl. auto.
  omega.
  simpl. auto.
Qed.

Lemma repeat_TailSub : forall n m,
 applys (repeat TailSub n IdSub) m = repeat (rename Succ) n (VarTy m).
Proof.
  induction n.
  intros m. destruct m. simpl. auto.
  simpl. auto.
  intros m. destruct m. simpl. rewrite IHn.
  rewrite <- repeat_rename_commute. simpl. auto.
  simpl. rewrite IHn.
  rewrite <- repeat_rename_commute. simpl. auto.
Qed.

(*

Lemma compose_TailSub : forall t x n,
  applys (composeSub (repeat TailSub n IdSub) t) x =
  repeat (rename Succ) n (applys t x).
Proof.
  induction t; intros; simpl; auto.
  - generalize dependent x. 
    induction n. simpl. auto. 
    intro x. simpl.  rewrite IHn.
    rewrite <- repeat_rename_commute.
    simpl. auto.
  - destruct x.
    generalize dependent c.
    induction n. simpl. intro c. rewrite subst_IdSub. auto.
    simpl.
    destruct TailSub_compose.
    intro c.
    rewrite H.
    rewrite IHn.
    rewrite repeat_rename_commute. auto.
    rewrite IHt. auto.
  - destruct x.
    unfold headSub.
    rewrite repeat_TailSub. auto.
    replace (repeat (rename Succ) n (rename Succ (applys t x))) with 
        (repeat (rename Succ) (S n) (applys t x)).
    rewrite <- IHt.
    simpl. auto.
    replace (S n) with (n + 1).
    rewrite <- repeat_repeat.
    simpl. 
    auto.
    omega.
Qed. *)


(*---------------------------------------------------- *)

Lemma rename_compose_Succ : forall s x, 
  rename Succ (applys s x) = applys (composeSub SuccSub s) x.
Proof.
  induction s; intros; simpl; auto.
  destruct x; auto. admit.
  destruct x; simpl; auto.
  rewrite IHs.
Admitted.

Lemma liftSub_def : forall s, LiftSub s [=] ConsSub (VarTy 0) (composeSub SuccSub s).
Proof.
  intros s x.
  simpl.
  destruct x. auto.


Lemma LiftSub_IdSub:  ConsSub (VarTy 0) (TailSub IdSub) [=] (LiftSub IdSub).
Proof. intros x; destruct x; auto. Qed. 
  

Lemma compose_lemma : 
  (forall x s1 s2, subst (composeSub s1 s2) x = subst s1 (subst s2 x)).
Proof.
  intro x. induction x.
  all: intros; simpl; eauto.
  + eapply ApplyScS.
  + f_equal; eauto.
  + f_equal.
    

Lemma ugh: 
 (forall ctx (n : nat) s1 s2,
  (subst (composeSub s1 s2) ctx = subst s1 (subst s2 ctx)) ->
  subst (repeat LiftSub n (composeSub s1 s2)) ctx = subst (repeat LiftSub n s1) (subst (repeat LiftSub n s2) ctx)) /\
 (forall ctx (n : nat) s1 s2,
  (substCtx (composeSub s1 s2) ctx = substCtx s1 (substCtx s2 ctx)) ->
  substCtx (repeat LiftSub n (composeSub s1 s2)) ctx = substCtx (repeat LiftSub n s1) (substCtx (repeat LiftSub n s2) ctx)).
Proof.
  eapply both.
  all: try solve [intros; simpl; auto].
  all: try solve
    [intros; simpl in *; inversion H1; rewrite H; auto; rewrite H0; auto].
  - intros. simpl in *.
    clear H.
    move: n0 n s1 s2.
    induction n0. intros; simpl; auto.
    rewrite ApplyScS. auto.
    intros n. simpl. destruct n. simpl. auto.
    move=> s1 s2.
    rewrite IHn0. 
Lemma foo: 
  (forall t s n, rename (repeat Lift n Succ) (subst s t) = 
          subst (LiftSub s) (rename (repeat Lift n Succ) t)) /\
  (forall t s n, renameCtx (repeat Lift n Succ) (substCtx s t) = 
          substCtx (LiftSub s) (renameCtx (repeat Lift n Succ) t)).
Proof. 
  eapply both.
  all: try solve [intros; simpl; auto].
  all: try solve
    [intros; simpl in *;  rewrite H; auto; rewrite H0; auto].
  - simpl.
    admit.
  - intros. 
    simpl.
    f_equal.
    replace (repeat Lift n (repeat Lift n0 Succ)) with 
            (repeat Lift (n + n0) Succ).
    rewrite H.
    
    replace (LiftSub (repeat LiftSub n0 s1)) with (repeat LiftSub n0 (LiftSub s1)).


    replace (LiftSub (repeat LiftSub n0 s2)) with (repeat LiftSub n0 (LiftSub s2)).
    rewrite <- IHn0.
rewrite IHn0.
SearchAbout rename Succ.    

Lemma compose_lemma : 
  (forall x s1 s2, subst (composeSub s1 s2) x = subst s1 (subst s2 x)) /\
  (forall x s1 s2, substCtx (composeSub s1 s2) x = substCtx s1 (substCtx s2 x)).
Proof.
  eapply both.
  all: try solve [intros; simpl; auto].
  all: try solve [intros; simpl; rewrite H; rewrite H0; auto].
  - intros n s1 s2. simpl.
    rewrite ApplyScS.
    auto.
  - intros n ctx h0 ty h1 s1 s2.
    simpl.
    f_equal.
    move: n ctx h0.

Abort.    



