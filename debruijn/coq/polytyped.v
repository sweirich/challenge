(* Source code for
   Strongly Typed Term Representations in Coq 
   Nick Benton · Chung-Kil Hur ·
   Andrew Kennedy · Conor McBride
   JAR 2012 

   Updated to Coq 8.8.1 by SCW, 3/29/19
   Not all Admitteds reproved.
*)

Require Import List.
Require Import Program.
Require Import FunctionalExtensionality.
Require Import Omega.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
   Tactic
*)

Ltac solution_simpl := simpl; unfold solution_left, eq_rect_r, eq_rect; simpl.
Ltac map_extensionality := extensionality _mapvar_; dependent destruction _mapvar_; [auto | auto].

(*
   JMeq 
*)
Definition cast (A B:Type) (pf:A = B) (a: A) : B.
rewrite pf in a. exact a.
Defined.

Lemma cast_elim: forall (A B:Type) (pf: A = B) (a: A), JMeq (cast pf a) a.
intros A B pf. case pf. reflexivity.
Qed.

Lemma cast_elim_r: forall (A B:Type) (pf: A = B) (a: A), JMeq a (cast pf a).
intros A B pf. case pf. reflexivity.
Qed.

(*=castelimcong-def *)
Lemma cast_elim_cong : forall (A B C:Type) (pf: A = C) (a:A) (b:B), 
                             JMeq a b ->  JMeq (cast pf a) b.
(*=End *)
intros. case pf. clear pf. case H. reflexivity. Qed.

Lemma cast_elim_r_cong : forall (A B C:Type) (pf: B = C) (a:A) (b:B), JMeq a b ->  JMeq a (cast pf b).
intros. case pf. clear pf. case H. reflexivity. Qed.

Lemma cast_JMcong: forall (A A' B B':Type) (pf: A = B) (pf': A'=B') (a:A) (a':A'),
  JMeq a a' -> JMeq (cast pf a) (cast pf' a').
intros. case pf. case pf'. case H. reflexivity.
Qed.

Lemma eq_JMeq: forall (A:Type) (x y:A), x = y -> JMeq x y.
intros. rewrite H. reflexivity.
Qed.

(* A useful tactic used in the JMeq congruence proofs *)
Ltac JMsubst :=
  (repeat (match goal with | [H : context[@JMeq _ ?X _ ?Y] |- _] => 
    (generalize X Y H; 
     subst; 
     clear H; 
     let X' := fresh X in
     let Y' := fresh Y in
     let H' := fresh H in
     intros X' Y' H'; 
     rewrite H'; 
     clear H') end)).

Ltac Rewrites := 
  (intros; simpl; 
   repeat (match goal with | [H : context[eq _ _] |- _] => rewrite H end); 
   auto).

Tactic Notation "RewritesWith" tactic(T) := 
  (intros; simpl; T;
   repeat (match goal with | [H : context[eq _ _] |- _] => rewrite H end); 
   T;
   auto).

(*
   System F
*)
(*=Ty *)
Inductive TyVar : nat -> Type := 
| ZTYVAR : forall u, TyVar (S u)
| STYVAR : forall u, TyVar u -> TyVar (S u).

Inductive Ty u : Type :=
| TYVAR : TyVar u -> Ty u
| ARR : Ty u -> Ty u -> Ty u
| ALL : Ty (S u) -> Ty u.
(*=End *)

(* removed notatation for the JAR paper *)
Infix " --> " := ARR   (at level 65) .

(*=RenSub *)
Definition RenT u w := TyVar u -> TyVar w.
Definition SubT u w := TyVar u -> Ty w.
(*=End *)

Definition idRenT u: RenT u u := fun v => v.
Definition idSubT u: SubT u u := fun v => TYVAR v.
Arguments idSubT : clear implicits.

(*=RTyLT *)
Program Definition RTyL u w (r:RenT u w) : RenT (S u) (S w) := 
fun var =>
  match var with
  | ZTYVAR _ => (ZTYVAR _)
  | STYVAR var' => STYVAR (r var')
  end.

Fixpoint RTyT u w (r:RenT u w) (t:Ty u) : Ty w :=
  match t with
  | TYVAR v => TYVAR (r v)
  | ARR t1 t2 => ARR (RTyT r t1) (RTyT r t2)
  | ALL t => ALL (RTyT (RTyL r) t)
  end.
(*=End *)

(*=STyLT *)
Definition ShTyT u : Ty u -> Ty (S u) := RTyT (@STYVAR _). 

Program Definition STyL u w (s:SubT u w) : SubT (S u) (S w) :=  
fun v => 
  match v with
  | ZTYVAR _ => TYVAR (ZTYVAR _)
  | STYVAR v' => ShTyT (s v')
  end.

Fixpoint STyT u w (s:SubT u w) (t:Ty u) : Ty w :=
  match t with
  | TYVAR v => s v
  | ARR t1 t2 => ARR (STyT s t1) (STyT s t2)
  | ALL t => ALL (STyT (STyL s) t)
  end.
(*=End *)

Definition sCs u v w (sub2: SubT v w) (sub1: SubT u v) : SubT u w := compose (STyT sub2) sub1.
Infix "@ss@" := sCs (at level 55).

Definition rs u w (ren: RenT u w) : SubT u w :=  compose (idSubT _) ren.

(*=shSubT *)
Definition shSubT u : SubT u (S u) := fun v => TYVAR (STYVAR v).
Arguments shSubT : clear implicits.
(*=End *)

Lemma RTyL_def: forall u w (ren: RenT u w), rs (RTyL ren) = STyL (rs ren).
intros. map_extensionality.
Qed.

Lemma RTyT_def: forall u w (ren: RenT u w), RTyT ren = STyT (rs ren).
intros. apply functional_extensionality. intros ty. revert w ren.
induction ty; Rewrites. f_equal. f_equal. map_extensionality.
Qed.

Lemma STyL_succ: forall u w (sub: SubT u w) var,
  STyL sub (STYVAR var) = STyT (shSubT _) (sub var).
intros. simpl.  unfold ShTyT. rewrite RTyT_def. auto.
Qed.

Lemma STyL_shsub: forall u w (sub: SubT u w), (STyL sub) @ss@ (shSubT _) = (shSubT _) @ss@ sub. 
intros. apply functional_extensionality. intro.
unfold sCs, compose, shSubT. simpl. unfold ShTyT. rewrite RTyT_def. auto.
Qed.

(* Composition of type renamings preserves lifting *)
Lemma RTyL_rr: forall u v w (ren2: RenT v w) (ren1: RenT u v) var,
  RTyL ren2 (RTyL ren1 var) = RTyL (compose ren2 ren1) var.
intros. dependent destruction var. reflexivity. reflexivity.
Qed.

(* Action of composition of renamings on a type *)
Lemma RTyT_rr: forall u (ty:Ty u) v w (ren2: RenT v w) (ren1: RenT u v),
  RTyT ren2 (RTyT ren1 ty) = RTyT (compose ren2 ren1) ty.
Proof. induction ty; Rewrites. f_equal. f_equal. unfold compose. apply functional_extensionality. intros. rewrite RTyL_rr.  auto. 
Qed.

(* Composition of type renaming and type substitution preserves lifting *)
Lemma STyL_rs: forall u v w (ren: RenT v w) (sub: SubT u v) var, 
  RTyT (RTyL ren) (STyL sub var) = STyL (compose (RTyT ren) sub) var.
intros. dependent destruction var; Rewrites. unfold compose, STyL, ShTyT. repeat rewrite RTyT_rr. auto. 
Qed.

(* Action of composition of renaming and a substitution on a type *)
Lemma STyT_rs: forall u (ty:Ty u) v w (ren: RenT v w) (sub: SubT u v),
  RTyT ren (STyT sub ty) = STyT (compose (RTyT ren) sub) ty.
Proof. induction ty; Rewrites. f_equal. f_equal. extensionality x. apply STyL_rs.
Qed.

(* Composition of type substitution and type renaming preserves lifting *)
Lemma STyL_sr: forall u v w (sub: SubT v w) (ren: RenT u v) var,
  STyL sub (RTyL ren var) = STyL (compose sub ren) var.
intros. dependent destruction var; reflexivity. 
Qed.

(* Action of composition of a substitution and a renaming on a type *)
Lemma STyT_sr: forall u (ty:Ty u) v w (sub: SubT v w) (ren: RenT u v),
  STyT sub (RTyT ren ty) = STyT (compose sub ren) ty.
Proof. 
induction ty; Rewrites.
f_equal. f_equal. extensionality var. unfold compose. 
  rewrite STyL_sr. auto. 
Qed. 

(* Composition of type substitutions preserves lifting *)
Lemma STyL_ss: forall u var v w (sub2: SubT v w) (sub1: SubT u v), 
  STyT (STyL sub2) (STyL sub1 var) = STyL (sub2 @ss@ sub1) var.
Proof.
intros. dependent destruction var. auto.
unfold sCs, compose. simpl.
unfold ShTyT.
rewrite STyT_rs, STyT_sr. auto.
Qed.

Lemma STyL_ss_ext: forall u v w (sub2: SubT v w) (sub1: SubT u v), 
  STyL sub2 @ss@ STyL sub1 = STyL (sub2 @ss@ sub1).
intros. extensionality var.
apply STyL_ss.
Qed.

(* Action of composition of type substitutions on a type *)
Lemma STyT_ss: forall u (ty:Ty u) v w (sub2: SubT v w) (sub1: SubT u v), 
  STyT sub2 (STyT sub1 ty) = STyT (sub2 @ss@ sub1) ty.
Proof. induction ty; RewritesWith (try rewrite STyL_ss_ext). 
Qed.

Lemma STyT_ss_ext: forall u v w (sub2: SubT v w) (sub1: SubT u v), 
  compose (STyT sub2) (STyT sub1) = STyT (sub2 @ss@ sub1).
Proof. intros. extensionality ty. apply STyT_ss.
Qed.


(* Lifting of identity type substitution *)
Lemma STyL_idSubT: forall u, STyL (idSubT u) = idSubT _.
Proof. intros. extensionality x. dependent destruction x; auto. 
Qed.

(* Action of the identity substitution on a type *)
Lemma STyT_idSubT: forall u (ty: Ty u), STyT (idSubT _) ty = ty.
intros. induction ty; RewritesWith (try rewrite STyL_idSubT). 
Qed.

(* Composition of type substitutions is associative *)
Lemma sss_assoc: forall u v w z (sub3:SubT w z) (sub2:SubT v w) (sub1:SubT u v),
  (sub3 @ss@ sub2) @ss@ sub1 = sub3 @ss@ (sub2 @ss@ sub1).
intros. apply functional_extensionality. intros.
unfold sCs, compose. rewrite STyT_ss. auto.
Qed.

(* The identity type substitution is a left identity for composition *)
Lemma idSubT_ss: forall u w (sub:SubT w u), (idSubT _) @ss@ sub = sub.
intros. apply functional_extensionality. intros. 
unfold sCs, compose. rewrite STyT_idSubT. auto.
Qed.

(* The identity type substitution is a right identity for composition *)
Lemma ss_idSubT: forall u w (sub:SubT w u), sub @ss@ (idSubT _) = sub.
intros. apply functional_extensionality. intros. auto.
Qed.

Program Definition consmap A u (hd: A) (tl : TyVar u -> A) : TyVar (S u) -> A :=
  fun var =>
    match var with
        | ZTYVAR _ => hd
        | STYVAR var => tl var
    end.

Notation "[| x , .. , y |]" := (consmap x .. (consmap y (idSubT _)) ..).

Lemma consmap_shsub : forall u w (sub: SubT u w) val,
  (consmap val sub) @ss@ shSubT _ = sub.
Proof.
intros. map_extensionality.
Qed.

Lemma consmap_STyL : forall u v w (sub': SubT v w) (sub: SubT u v) val,
  (consmap val sub') @ss@ STyL sub = consmap val (sub' @ss@ sub).
Proof.
intros. map_extensionality.
unfold sCs, compose. simpl.
unfold ShTyT.
rewrite RTyT_def. rewrite STyT_ss.
rewrite consmap_shsub. auto.
Qed.

Lemma singsub_shsub: forall u (t: Ty u),
  [| t |] @ss@ shSubT _ = idSubT _.
intros. map_extensionality.
Qed.

Lemma sub_singsub : forall u w (sub: SubT u w) t,
  sub @ss@ [| t |] = [| STyT sub t |] @ss@ STyL sub.
intros. extensionality var.
dependent destruction var; Rewrites. unfold "@ss@". unfold compose. simpl. 
unfold ShTyT.
rewrite RTyT_def. rewrite STyT_ss.
rewrite singsub_shsub. rewrite STyT_idSubT. auto.
Qed.

Lemma singsub_STyL: forall u w (sub:SubT u w) ty,
  [| ty |] @ss@ STyL sub = consmap ty sub.
intros. apply functional_extensionality. intros.
dependent destruction x. auto.
unfold sCs, compose.
rewrite STyL_succ, STyT_ss, singsub_shsub, STyT_idSubT. auto.
Qed.

(*==========================================================================
  Typed terms in context
  ==========================================================================*)

(* Env and Var *)

(* Term environments and action of a type substitution on a term environment *)
(*=Env *)
Definition Env u := list (Ty u).

Fixpoint STyE u w (sub: SubT u w) (env: Env u) : Env w := 
  match env with
    | nil => nil
    | T::TS => STyT sub T :: STyE sub TS
  end.
(*=End *)

Tactic Notation "ST_simpl" := unfold STyT; fold STyT; unfold STyE; fold STyE.
Tactic Notation "ST_simpl" "in" hyp(h) := unfold STyT in h; fold STyT in h; unfold STyE in h; fold STyE in h.

Lemma STyE_length: forall u w (sub:SubT u w) env,
  length (STyE sub env) = length env. 
Proof. induction env; Rewrites. Qed.

(* Action of composition of type substitutions on an environment *)
Lemma STyE_ss: forall u v w (sub2: SubT v w) (sub1: SubT u v) env,
  STyE sub2 (STyE sub1 env) = STyE (sub2 @ss@ sub1) env.
Proof. induction env; RewritesWith (try rewrite STyT_ss). Qed.

(* Action of identity type substitution on an environment *)
Lemma STyE_idSubT: forall u (env:Env u), STyE (idSubT _) env = env.
Proof. induction env; RewritesWith (try rewrite STyT_idSubT). Qed.

(*=Var *)
Inductive Var u : Env u -> Ty u -> Type := 
| ZVAR : forall env ty, Var (ty :: env) ty
| SVAR : forall env ty' ty, Var env ty -> Var (ty' :: env) ty.
(*=End *)

(* JMeq is a congruence with respect to variable constructors *)
Lemma ZVAR_JMcong: forall u (env:Env u) env' ty ty',
  env = env' -> ty = ty' -> JMeq (ZVAR env ty) (ZVAR env' ty').
Proof. intros. subst. reflexivity. Qed.

Lemma SVAR_JMcong: forall u (env:Env u) env' ty ty' (var: Var env ty) (var': Var env' ty') ty0 ty0',
  JMeq var var' -> env = env' -> ty = ty' -> ty0 = ty0' -> JMeq (SVAR ty0 var) (SVAR ty0' var').
Proof. intros. JMsubst. reflexivity. Qed.

(* Expressions in polymorphic lambda calculus *)
(*=Exp *)
Inductive Exp u (E:Env u) : Ty u -> Type :=
| VAR : forall t, Var E t -> Exp E t
| LAM : forall t1 t2, Exp (t1 :: E) t2 -> Exp E (ARR t1 t2)  
| APP : forall t1 t2, Exp E (ARR t1 t2) -> Exp E t1 -> Exp E t2
| TAPP : forall t, Exp E (ALL t) -> forall t':Ty u, Exp E (STyT [| t' |] t)
| TABS : forall t, Exp (u:=S u) (STyE (shSubT _) E) t -> Exp E (ALL t).
(*=End *)



(* JMeq is a congruence with respect to expression constructors *)
Lemma VAR_JMcong: forall u (env env': Env u) ty ty' (v: Var env ty) (v': Var env' ty'),
  JMeq v v' -> env = env' -> ty = ty' -> JMeq (VAR v) (VAR v').
Proof. intros. JMsubst. reflexivity. Qed.

Lemma LAM_JMcong: forall u (env env': Env u) ty1 ty1' ty2 ty2' (e: Exp (ty1::env) ty2) (e': Exp (ty1'::env') ty2'),
  JMeq e e' -> ty1 = ty1' -> ty2 = ty2' -> env = env' -> JMeq (LAM e) (LAM e').
Proof. intros. JMsubst. reflexivity. Qed.

(*=appjmeqcong *)
Lemma APP_JMcong: forall u (env env': Env u) ty1 ty2 ty1' ty2' 
                  (v1: Exp env (ARR ty1 ty2)) (v2: Exp env ty1) 
                  (v1': Exp env' (ARR ty1' ty2')) (v2': Exp env' ty1'),
  JMeq v1 v1' -> JMeq v2 v2' -> ty1 = ty1' -> ty2 = ty2' -> env = env' 
       -> JMeq (APP v1 v2) (APP v1' v2').
Proof. intros. JMsubst. reflexivity. Qed.
(*=End *)

Lemma TAPP_JMcong: forall u (env env': Env u) ty ty' (f: Exp env (ALL ty)) (f':Exp env' (ALL ty')) t t',
  JMeq f f' -> t = t' -> env = env' -> ty = ty' -> JMeq (TAPP f t) (TAPP f' t').
Proof. intros. JMsubst. reflexivity. Qed.

Lemma TABS_JMcong: forall u (env env': Env u) ty ty' (tv: Exp (STyE (shSubT u) env) ty) (tv': Exp (STyE (shSubT u) env') ty'), 
  JMeq tv tv' -> ty = ty' -> env = env' -> JMeq (TABS tv) (TABS tv').
Proof. intros. JMsubst. reflexivity. Qed.

(* Action of type substitution on a term variable *)
Fixpoint STyVar u w (sub: SubT u w) (env: Env u) ty  (var: Var env ty) : Var (STyE sub env) (STyT sub ty) :=
  match var with
    | ZVAR _ _ => ZVAR _ _
    | SVAR _ v => SVAR _ (STyVar sub v)
  end.

Lemma STyVar_JMcong: forall u w (sub1 sub2:SubT u w) env ty (var: Var env ty),
  sub1 = sub2 -> JMeq (STyVar sub1 var) (STyVar sub2 var).
Proof. intros. subst. reflexivity. Qed.

Lemma STyVar_JMcongAux: forall u w (sub1 sub2:SubT u w) env ty (var1 var2: Var env ty),
  sub1 = sub2 -> JMeq var1 var2 -> JMeq (STyVar sub1 var1) (STyVar sub2 var2).
Proof. intros. JMsubst. reflexivity. Qed.

Lemma STyVar_zero: forall u w (sub: SubT u w) (env: Env u) ty,
  STyVar sub (ZVAR env ty) = ZVAR _ _.
auto.
Qed.

Lemma STyVar_succ: forall u w (sub: SubT u w) (env: Env u) ty  (var: Var env ty) ty',
  STyVar sub (SVAR ty' var) = SVAR _ (STyVar sub var).
auto.
Qed.

(*=cast1 *)
Lemma STyExp_cast1 : forall u w (sub: SubT u w) (env: Env u) 
                                        (ty : Ty (S u)) (ty' : Ty u), 
  @eq Type
  (Exp (STyE sub env) (STyT [| STyT sub ty' |] (STyT (STyL sub) ty)))
  (Exp (STyE sub env) (STyT sub (STyT [| ty' |] ty))).
(*=End *)
intros. repeat rewrite STyT_ss. rewrite sub_singsub. auto.
Qed.

(*=cast2 *)
Lemma STyExp_cast2 : forall u w (sub : SubT u w) (env: Env u) (ty: Ty (S u)),
  @eq Type
  (Exp (STyE (STyL sub) (STyE (shSubT u) env)) (STyT (STyL sub) ty))
  (Exp (STyE (shSubT _) (STyE sub env)) (STyT (STyL sub) ty)).
(*=End *)
Proof.
intros. repeat rewrite STyE_ss. rewrite STyL_shsub. auto.
Qed.

(* Action of type substitution on an expression *)
(*=STyExp *)
Fixpoint STyExp u w (s:SubT u w) (E:Env u) t (e:Exp E t) 
 : Exp (STyE s E) (STyT s t) :=
  match e with
  | VAR v => VAR (STyVar s v)
  | APP e1 e2 => APP (STyExp s e1) (STyExp s e2)
  | LAM e => LAM (STyExp s e)
  | TAPP e t' => cast (STyExp_cast1 _ _ _ _) 
                    (TAPP (STyExp s e) (STyT s t'))
  | TABS e => TABS (cast (STyExp_cast2 _ _ _) 
                       (STyExp (STyL s) e))
  end.
(*=End *)

Lemma STyExp_JMcong: forall (u w : nat) (sub sub': SubT u w) (env env': Env u) (ty ty': Ty u) (tc:Exp env ty) (tc':Exp env' ty'),
  JMeq tc tc' -> sub = sub' -> env = env' -> ty = ty' -> JMeq (STyExp sub tc) (STyExp sub' tc').
Proof. intros. JMsubst. reflexivity. Qed.

Lemma var_inv : forall u w (sub:SubT u w) (env:Env u) ty (var: Var (STyE sub env) ty),
  exists ty', exists var': Var env ty',
    STyT sub ty' = ty /\ JMeq (STyVar sub var') var.
intros. induction env. inversion var.
dependent destruction var. 
exists a. exists (ZVAR env a). split; auto. 

destruct (IHenv var) as [ty' [var' [? ?]]].
eexists ty'. exists (SVAR a var'). split. auto.
apply SVAR_JMcong; auto. 
Qed.

(*==========================================================================
  Variable-domain maps. 
  By instantiating P with Var we get renamings.
  By instantiating P with Exp we get substitutions.
  ==========================================================================*)

Section VariableDomainMap.

  Definition VDMap := forall u, (Env u) -> (Ty u) -> Type.

  Variable P : VDMap.

  Record MapOps :=
  {
    vr : forall u (env: Env u) ty, Var env ty -> P env ty;   
    vl : forall u (env: Env u) ty, P env ty -> Exp env ty;
    wk : forall u (env: Env u) ty' ty, P env ty -> P (ty' :: env) ty;
    sb : forall u w (sub: SubT u w) (env: Env u) ty, P env ty -> P (STyE sub env) (STyT sub ty)
  }.

  Variable ops: MapOps.

  Definition Map u (E E': Env u) := forall t, Var E t -> P E' t.

  Lemma MapExtensional : forall u (E:Env u) E' (r1 r2 : Map E E'), (forall t var, r1 t var = r2 t var) -> r1 = r2.
  Proof. intros.
  extensionality t. extensionality var. apply H. 
  Qed.

  Definition hdMap u (E: Env u) E' t (m:Map (t::E) E') : P E' t := m t (ZVAR _ _).

  Definition tlMap u (E: Env u) E' t (m:Map (t::E) E') : Map E E' := fun t' v => m t' (SVAR t v).

  Lemma hdMap_JMcong: forall u E1 E1' E2 E2' t t' m m',
    JMeq m m' -> E1 = E1' -> E2 = E2' -> t = t' -> 
    JMeq (@hdMap u E1 E2 t m) (@hdMap u E1' E2' t' m').
  Proof. intros. JMsubst. reflexivity. Qed.

  Lemma tlMap_JMcong: forall u E1 E1' E2 E2' t t' m m',
    JMeq m m' -> E1 = E1' -> E2 = E2' -> t = t' -> 
    JMeq (@tlMap u E1 E2 t m) (@tlMap u E1' E2' t' m').
  Proof. intros. JMsubst. reflexivity. Qed.

  Definition nilMap u (E:Env u) : (Map nil E).
  Proof. red; intros. inversion H.
  Defined.

  Lemma nilMap_JMcong_gen: forall u (E1:Env u) E2 E1' E2' (map : Map E1 E2) (map' : Map E1' E2'),
    E1 = nil -> E1' = nil -> E2 = E2' -> JMeq map map'.
  Proof.
    intros. subst. apply eq_JMeq. apply MapExtensional. intros. inversion var.
  Qed.

  Program Definition consMap u (E:Env u) E' t (v:P E' t) (m:Map E E') : Map (t::E) E' :=
      fun t' (var:Var (t::E) t') => 
      match var with
      | ZVAR _ _ => v
      | SVAR _ var => m _ var
      end.

  Lemma consMap_JMcong: forall u (E1:Env u) E2 T E1' E2' T' (v : P E2 T) (v' : P E2' T') (map : Map E1 E2) (map' : Map E1' E2'),
    JMeq v v' -> JMeq map map' -> T = T' -> E1 = E1' -> E2 = E2' -> JMeq (consMap v map) (consMap v' map').
  Proof. intros. JMsubst. reflexivity.
  Qed.

  Lemma hdConsMap : forall u (env:Env u) env' ty (v : P env' ty) (s : Map env env'), hdMap (consMap v s) = v. Admitted.

  Lemma tlConsMap : forall u (env:Env u) env' ty (v : P env' ty) (s : Map env env'), tlMap (consMap v s) = s. Proof. intros. apply MapExtensional. auto. Qed.

  Lemma consMapInv : forall u (env:Env u) env' ty (m:Map (ty :: env) env'), m = consMap (hdMap m) (tlMap m).
  intros. apply MapExtensional. dependent destruction var; auto.
  Admitted.

  Lemma consMap_zero: forall u (E:Env u) E' T (v:P E' T) (m:Map E E'),
    consMap v m (ZVAR _ _) = v.
  auto.
  Admitted.

  Lemma consMap_succ: forall u (E:Env u) E' T (v:P E' T) (m:Map E E') T' (var: Var E T'),
    consMap v m (SVAR _ var) = m _ var.
  auto.
  Qed.

  Program Definition liftMap u (env:Env u) env' ty (m : Map env env') : Map (ty :: env) (ty :: env') :=
  fun ty' var => match var with
  | ZVAR _ _ => vr _ (ZVAR _ _)
  | SVAR _ x => wk _ _ (m _ x)
  end.

  Lemma liftMap_zero: forall u (env:Env u) env' (m: Map env env') ty,
    liftMap m (ZVAR _ _) = vr ops (ZVAR _ ty).
  auto.
  Admitted.

  Lemma liftMap_succ: forall u (env:Env u) env' (m: Map env env') ty ty' (var:Var env ty'), 
    liftMap m (SVAR ty var) = wk ops _ (m _ var).
  auto.
  Qed.

  Definition substMap u w (sub: SubT u w) env env' (m: Map env env') : Map (STyE sub env) (STyE sub env').
  induction env.
  red; intros. simpl in H. inversion H.
  red; intros. dependent destruction H.
  exact (sb ops sub (m _ (ZVAR _ _))).
  exact (IHenv (fun ty var => m _ (SVAR _ var)) _ H).
  Defined.
  Implicit Arguments substMap [u w env env' t].

  Lemma hdMap_substMap: forall u w (sub:SubT u w) (E: Env u) E' t (m:Map (t::E) E'), 
    hdMap (substMap sub m) = sb ops sub (hdMap m).
  auto.  
  Qed.

  Lemma tlMap_substMap: forall u w (sub:SubT u w) (E: Env u) E' t (m:Map (t::E) E'), 
    tlMap (substMap sub m) = substMap sub (tlMap m).
  intros. apply MapExtensional. intros. auto.
  Qed.

  Fixpoint mapExp u (env:Env u) env' (m: Map env env') ty (v : Exp env ty) : Exp env' ty :=
    match v with
      | VAR v => vl ops (m _ v)
      | APP e1 e2 => APP (mapExp m e1) (mapExp m e2)
      | LAM e => LAM (mapExp (liftMap m) e)
      | TAPP v t => TAPP (mapExp m v) t
      | TABS v => TABS (mapExp (substMap (shSubT _) m) v)
  end.

  Lemma mapExp_JMcong: forall u (env1 env1' :Env u) env2 env2' (m : Map env1 env2) (m' : Map env1' env2') ty ty' (c: Exp env1 ty) (c':Exp env1' ty'),
    JMeq m m' -> JMeq c c' -> env1 = env1' -> env2 = env2' -> ty = ty' -> JMeq (mapExp m c) (mapExp m' c').
  Proof. intros. JMsubst. reflexivity. Qed.

  Lemma substMap_STyVar: forall u w (sub: SubT u w) (env env': Env u) (m: Map env env') ty (var: Var env ty),
    substMap sub m (STyVar sub var) =  sb ops sub (m _ var).
  Proof.
  intros. induction env. inversion var.
  dependent destruction var. reflexivity.
  simpl STyVar. specialize (IHenv (fun (ty0 : Ty u) (var0 : Var env ty0) => m ty0 (SVAR a var0))). rewrite <- IHenv. auto. 
  Qed.

  Definition idMap u (env: Env u) : Map env env := @vr ops u env.

  Definition dropMap u (env env': Env u) ty (m: Map (ty::env) env') : Map env env' := fun _ var => m _ (SVAR _ var).

End VariableDomainMap.

Implicit Arguments substMap [P u w env env' t].

(*==========================================================================
  Variable renamings: Map Var
  ==========================================================================*)

Definition RenamingMap := (@Build_MapOps (@Var) (fun _ _ _ v => v) VAR (@SVAR) (STyVar)).

Definition Renaming := @Map (@Var).
Definition RTmExp := @mapExp _ RenamingMap.
Definition RTmL := @liftMap _ RenamingMap. 
Definition STyRen := @substMap _ RenamingMap.
Implicit Arguments STyRen [u w env env' t].
Definition dropRen := @dropMap (@Var).
Definition idRen := @idMap _ RenamingMap.
Implicit Arguments idRen [u].

Lemma RTmL_JMcong: forall u env1 env1' env2 env2' ty ty' R R',
  JMeq R R' -> env1 = env1' -> env2 = env2' -> ty = ty' -> JMeq (@RTmL u env1 env2 ty R) (@RTmL u env1' env2' ty' R').
Proof. intros. JMsubst. reflexivity. Qed.

(*==========================================================================
  Substitution
  ==========================================================================*)

Definition SubstMap := @Build_MapOps (@Exp) VAR (fun _ _ _ v => v) (fun u env ty' => RTmExp (SVAR ty')) (STyExp). 

Definition Subst := @Map (@Exp).
Definition STmExp := @mapExp _ SubstMap.
Definition STmL := @liftMap _ SubstMap.
Definition STySub := @substMap _ SubstMap.
Implicit Arguments STySub [u w env env' t].
Definition idSub := @idMap _ SubstMap.
Implicit Arguments idSub [u].
Definition dropSub := @dropMap (@Exp).



Definition compose2 (D:Type) (A B C: D -> Type) (g: forall (d:D), B d -> C d) (f: forall (d:D), A d -> B d) : forall (d:D),  A d -> C d := fun d a => g d (f d a).
Definition RCS u (env:Env u) env' env'' (r:Renaming env' env'') (s:Subst env env') ty var := RTmExp r (s ty var).
Definition SCS u (env env' env'':Env u) (s' : Subst env' env'') (s : Subst env env') : Subst env env'' := fun ty var => STmExp s' (s _ var). 

Infix "@SS@" := SCS (at level 55, right associativity).

(* JMeq is a congruence with respect to map operations *)
Lemma STmL_JMcong: forall u env1 env1' env2 env2' ty ty' S S',
  JMeq S S' -> env1 = env1' -> env2 = env2' -> ty = ty' -> JMeq (@STmL u env1 env2 ty S) (@STmL u env1' env2' ty' S').
Proof. intros. JMsubst. reflexivity. Qed.

Lemma STmExp_JMcong: forall u (env1 env2 env1' env2': Env u) (Sub: Subst env1 env2) (Sub': Subst env1' env2') ty (tc:Exp env1 ty) ty' (tc':Exp env1' ty'),
  JMeq Sub Sub' -> JMeq tc tc' -> env1 = env1' -> env2 = env2' -> ty = ty' -> JMeq (STmExp Sub tc) (STmExp Sub' tc').
Proof. intros. JMsubst. reflexivity. Qed.

Lemma STySub_JMcong: forall u w (sub sub':SubT u w) env1 env2 env1' env2' (Sub: Subst env1 env2) (Sub': Subst env1' env2'),
  JMeq Sub Sub' -> sub = sub' -> env1 = env1' -> env2 = env2' -> JMeq (STySub sub Sub) (STySub sub' Sub').
Proof. intros. JMsubst. reflexivity. Qed.

Lemma SCS_JMcong: forall u (E1 E1' E2 E2' E3 E3':Env u) (s2 : Subst E2 E3) (s2':Subst E2' E3') (s1 : Subst E1 E2) (s1':Subst E1' E2'),
  JMeq s2 s2' -> JMeq s1 s1' -> E1 = E1' -> E2 = E2' -> E3 = E3' -> JMeq (s2 @SS@ s1) (s2' @SS@ s1').
Proof. intros. JMsubst. reflexivity. Qed.

Definition RS u (env:Env u) env' (R : Renaming env env') : Subst env env' := compose2 (idSub _) R.

Lemma RS_JMcong: forall u (E1 E1' E2 E2':Env u) (R: Renaming E1 E2) (R': Renaming E1' E2'),
  JMeq R R' -> E1 = E1' -> E2 = E2' -> JMeq (RS R) (RS R').
Proof. intros. JMsubst. reflexivity. Qed.

Definition shSub u (env:Env u) ty : Subst env (ty::env) := RS (@SVAR _ _ _).

Lemma shSub_JMcong: forall u (E E':Env u) T T',
  E = E' -> T = T' -> JMeq (@shSub u E T) (@shSub u E' T').
Proof. intros. subst. reflexivity.
Qed.

Lemma shSub_simpl: forall u (E: Env u) ty T (var:Var E T), shSub ty var = VAR (SVAR _ var). auto. Qed.

Notation "'{|' x , .. , y '|}'" := (consMap x .. (consMap y (idSub _)) ..) : Subst_scope. 
Delimit Scope Subst_scope with subst.
Arguments Scope STmExp [_ _ _ Subst_scope]. 
Arguments Scope STmExp [_ _ _ Subst_scope]. 
Open Scope Subst_scope.

(*
   RTmL STyRen RTmExp RTmExp definitions
*)

Lemma RTmL_def: forall u (env env' : Env u) (ty : Ty u) (R: Renaming env env'),
  RS (RTmL (ty:=ty) R) = STmL (RS R).
intros. apply MapExtensional. intros. dependent destruction var; auto.
Admitted.

Lemma STyRen_def: forall u w (sub:SubT u w) (E E': Env u) (R: Renaming E E'),
  RS (STyRen sub R) = STySub sub (RS R).
intros. apply MapExtensional. intros.
destruct (var_inv var) as [t' [var' [? ?]]].
generalize var H H0.  rewrite <- H. clear H0 H var t.
intros. rewrite <- H0. clear H0 var.
unfold STySub.
rewrite substMap_STyVar.
induction var'. auto.
apply  (IHvar' (dropRen R) H).
Qed.

Lemma RTmExp_def: forall (u : nat) (env env' : Env u) (R: Renaming env env'),  RTmExp R = STmExp (RS R).
Proof. 
  intros. extensionality ty. extensionality exp. 
  induction exp; RewritesWith (try rewrite <- STyRen_def; try rewrite <- RTmL_def). 
Qed.

(* Action of composition of type substitutions on a term variable *)
Lemma STyVar_ss: forall u env v w (sub2:SubT v w) (sub1:SubT u v) ty (var: Var env ty),
  JMeq (STyVar sub2 (STyVar sub1 var)) (STyVar (sub2 @ss@ sub1) var).
induction env. intros. inversion var.

intros. dependent destruction var; Rewrites. fold STyE.  
rewrite STyE_ss. rewrite STyT_ss. reflexivity.
apply SVAR_JMcong.
  apply IHenv.
  apply STyE_ss.
  apply STyT_ss.
  apply STyT_ss.
Qed.

(* Action of composition of type substitutions on an expression *)
(*=styexpss-state *)
Lemma STyExp_ss: forall u env ty (exp: Exp env ty) v w 
                            (sub2:SubT v w) (sub1:SubT u v),
  JMeq (STyExp sub2 (STyExp sub1 exp)) 
       (STyExp (sub2 @ss@ sub1) exp).
(*=End *)

induction exp; Rewrites.
  apply VAR_JMcong. 
    apply STyVar_ss.
    apply STyE_ss. 
    apply STyT_ss. 

  apply LAM_JMcong. 
    apply (IHexp _ _ sub2 sub1).
    apply STyT_ss. 
    apply STyT_ss. 
    apply (STyE_ss sub2 sub1).
  
  apply APP_JMcong.  
    apply IHexp1. 
    apply IHexp2.
    rewrite STyT_ss. auto. 
    rewrite STyT_ss. auto. 
    rewrite STyE_ss. auto.
  
  apply cast_elim_r_cong.
  eapply trans_JMeq. 
      apply STyExp_JMcong. 
        apply cast_elim.
        reflexivity. 
        auto. auto. 
        rewrite STyT_ss, STyT_ss, sub_singsub. auto.

      eapply trans_JMeq. 
        apply cast_elim.

        fold STyT. apply TAPP_JMcong. 
          apply IHexp. 
          rewrite STyT_ss. auto.
          rewrite STyE_ss. auto. 
          rewrite STyT_ss, STyL_ss_ext. auto.

  apply TABS_JMcong.  
    apply cast_JMcong.
    eapply trans_JMeq.
      apply STyExp_JMcong. 
        apply cast_elim.
        reflexivity.
        repeat rewrite STyE_ss. rewrite STyL_shsub. auto. 
        auto. 
      
      rewrite <- STyL_ss_ext. apply IHexp. 

    rewrite STyT_ss, STyL_ss_ext. auto. 

    rewrite STyE_ss. auto. 
Qed.

(* Action of composition of type substitutions on a term renaming  *)
Lemma STyRen_ss : forall (u : nat) env v w (sub2:SubT v w) (sub1:SubT u v) env' (Ren : Renaming env env'),
  JMeq (STyRen sub2 (STyRen sub1 Ren)) (STyRen (sub2 @ss@ sub1) Ren).

induction env.

intros. apply nilMap_JMcong_gen. auto. auto. rewrite <- STyE_ss. auto.

intros.
Admitted.
(*
rewrite (consMapInv (STyRen sub2 (STyRen sub1 Ren))).
rewrite (consMapInv (STyRen (sub2 @ss@ sub1) Ren)).
ST_simpl. apply consMap_JMcong.
unfold STyRen. rewrite 3 hdMap_substMap. 
apply STyVar_ss.

unfold STyRen. rewrite 3 tlMap_substMap.
apply IHenv.

rewrite STyT_ss. auto.
rewrite STyE_ss. auto.
rewrite STyE_ss. auto.
Qed. *)

(* Action of composition of type substitutions on a term substitution *)
Lemma STySub_ss: forall u (env env': Env u) v w (sub2: SubT v w) (sub1: SubT u v)  (S:Subst env env'),
  JMeq (STySub sub2 (STySub sub1 S)) (STySub (sub2 @ss@ sub1) S).

induction env. 
intros. apply nilMap_JMcong_gen.
auto. auto. rewrite STyE_ss. auto.

intros. 
Admitted.
(*
rewrite (consMapInv (STySub (sub2 @ss@ sub1) S)).
rewrite (consMapInv (STySub sub2 (STySub sub1 S))).
ST_simpl. apply consMap_JMcong.
unfold STySub.
rewrite (hdMap_substMap _ sub2). rewrite (hdMap_substMap _ sub1). 
rewrite (hdMap_substMap _ (sub2 @ss@ sub1)).
apply sym_JMeq. symmetry. apply STyExp_ss.

unfold STySub.
rewrite (tlMap_substMap _ sub2). rewrite (tlMap_substMap _ sub1). 
rewrite (tlMap_substMap _ (sub2 @ss@ sub1)).
apply IHenv.

rewrite STyT_ss. auto.
rewrite STyE_ss. auto.
rewrite STyE_ss. auto.
Qed. *)

Lemma RTmL_zero: forall u (env:Env u) env' (R: Renaming env env') ty,
  RTmL R (ZVAR _ _) = ZVAR _ ty.
apply liftMap_zero.
Qed.

Lemma RTmL_succ: forall u (env:Env u) env' (R: Renaming env env') ty ty' (var:Var env ty'), 
  RTmL R (SVAR ty var) = SVAR _ (R _ var).
apply liftMap_succ.
Qed.

Lemma STmL_zero: forall u (env:Env u) env' (S: Subst env env') ty,
  STmL S (ZVAR _ ty) = VAR (ZVAR _ ty).
auto.
Admitted.

Lemma STmL_succ: forall u (env:Env u) env' (S: Subst env env') ty ty' (var:Var env ty'), 
  STmL S (SVAR ty var) = STmExp (shSub _) (S _ var).
intros. unfold shSub. rewrite <- RTmExp_def.
apply liftMap_succ.
Qed.

Lemma STySub_dropSub: forall u w (sub: SubT u w) ty ty' env env' (S: Subst (ty'::env) env') (var: Var _ ty),
(STySub sub (dropSub S) var = STySub sub S (SVAR _ var)).
auto.
Qed.

Lemma hdMap_STySub : forall u w (sub:SubT u w) (E: Env u) E' t (m:Subst (t::E) E'), 
    hdMap (STySub sub m) = STyExp sub (hdMap m).
apply hdMap_substMap.
Qed.

Lemma tlMap_STySub : forall u w (sub:SubT u w) (E: Env u) E' t (m:Subst (t::E) E'), 
    tlMap (STySub sub m) = STySub sub (tlMap m).
apply tlMap_substMap.
Qed.

Lemma STyRen_STyVar: forall u w (sub: SubT u w) (env env': Env u) (R: Renaming env env') ty var,
  (STyRen sub R) _ (STyVar sub var) = STyVar sub (R ty var).
apply substMap_STyVar.
Qed.

Lemma STySub_STyVar: forall u w (sub: SubT u w) (env env': Env u) (S: Subst env env') ty var,
  (STySub sub S) _ (STyVar sub var) = STyExp sub (S ty var).
apply substMap_STyVar.
Qed.

Lemma STySub_shSub: forall u (env: Env u) w (sub: SubT u w) ty,
  STySub sub (shSub (env:=env) ty) = shSub (STyT sub ty).
intros. apply MapExtensional. intros.
destruct (var_inv var) as [ty' [var' [? ?]]].
generalize var H H0. rewrite <- H. clear H0 H var t. intros. 
rewrite <- H0. clear H H0 var.
rewrite STySub_STyVar. auto.
Qed.

Lemma STyRen_RTmL: forall u env w (sub:SubT u w) env' (Ren: Renaming env env') ty,
  STyRen sub (RTmL (ty:=ty) Ren) = RTmL (STyRen sub Ren).

intros. apply MapExtensional; intros.
dependent destruction var. 
Admitted. 
(*
reflexivity.
destruct (var_inv var) as [ty' [var' [? ?]]].
generalize var H H0. rewrite <- H. clear H0 H var ty0. intros.
rewrite <- H0.
rewrite RTmL_succ.
rewrite <- STyVar_succ.
repeat rewrite STyRen_STyVar.
rewrite <- STyVar_succ.
auto.
Qed. *)

Lemma STyExp_RTmExp: forall u (env:Env u) ty (tm: Exp env ty) w (sub: SubT u w) env' (Ren: Renaming env env'),
    STyExp sub (RTmExp Ren tm) = RTmExp (STyRen sub Ren) (STyExp sub tm).

unfold RTmExp.
induction tm; Rewrites.

  unfold STyRen. rewrite substMap_STyVar. auto.

  rewrite STyRen_RTmL. reflexivity.

  apply JMeq_eq.  
  apply cast_elim_cong. 
    
    symmetry. eapply trans_JMeq. 
      apply mapExp_JMcong.
        reflexivity. 
        apply cast_elim. 
        reflexivity.
        reflexivity.
        fold STyT. repeat rewrite STyT_ss. rewrite sub_singsub. reflexivity.

      reflexivity.

  f_equal. apply JMeq_eq.
  apply cast_elim_cong. 

    apply mapExp_JMcong.
      eapply trans_JMeq. 
        apply STyRen_ss.
        rewrite STyL_shsub. symmetry. apply STyRen_ss. 

      apply cast_elim_r.
      repeat rewrite STyE_ss. rewrite STyL_shsub. reflexivity.
      repeat rewrite STyE_ss. rewrite STyL_shsub. reflexivity.
      reflexivity.
Qed.

(* Lifting commutes with action of type substitution on term substitution *)
Lemma STySub_STmL: forall u env w (sub:SubT u w) env' (Sub: Subst env env') ty,
  STySub sub (STmL (ty:=ty) Sub) = STmL (STySub sub Sub).
Proof.
intros. apply MapExtensional; intros.
dependent destruction var. 
Admitted.
(*
reflexivity.
destruct (var_inv var) as [ty' [var' [? ?]]].
generalize var H H0. rewrite <- H. clear H0 H var ty0. intros.
rewrite <- H0.
rewrite STmL_succ.
rewrite <- STyVar_succ.
repeat rewrite STySub_STyVar.
rewrite STmL_succ.
unfold shSub. rewrite <- RTmExp_def.
rewrite STyExp_RTmExp.
rewrite RTmExp_def.
rewrite STyRen_def. rewrite STySub_shSub. auto.
Qed. *)

(* Type substitution commutes with term substitution *)
Lemma STyExp_STmExp: forall u (env:Env u) ty (tm: Exp env ty) w (sub: SubT u w) env' (Sub: Subst env env'),
    STyExp sub (STmExp Sub tm) =  STmExp (STySub sub Sub) (STyExp sub tm).

induction tm; RewritesWith (try rewrite STySub_STyVar; try rewrite <- STySub_STmL). 

  apply JMeq_eq. apply cast_elim_cong. 

    symmetry. eapply trans_JMeq.
      apply mapExp_JMcong.
        reflexivity.   
        apply cast_elim. 
        reflexivity. 
        reflexivity.
        fold STyT. rewrite STyT_ss, STyT_ss, sub_singsub. reflexivity.
      reflexivity.

  apply JMeq_eq. apply TABS_JMcong.
    apply cast_elim_cong.
 
      apply mapExp_JMcong.
        eapply trans_JMeq. 
          apply STySub_ss.
          rewrite STyL_shsub. symmetry. apply STySub_ss.

        apply cast_elim_r.
        repeat rewrite STyE_ss. rewrite STyL_shsub. reflexivity.
        repeat rewrite STyE_ss. rewrite STyL_shsub. reflexivity.
        reflexivity.
    reflexivity.
    reflexivity.
Qed.


(*==========================================================================
  Composition of substitutions
  ==========================================================================*)

Section CompMR.

  Variable P: VDMap.
  Variable ops: MapOps P.
  
  Lemma liftMap_MR : forall u (env env' env'':Env u) ty (m:Map P env' env'') (r:Renaming env env'),
    compose2 (liftMap ops m) (RTmL (ty:=ty) r) = liftMap ops (compose2 m r).
  
  intros. apply MapExtensional. intros t var.
  dependent destruction var; auto. 
  Admitted.
  
  (* Type substitution commtues with composition of variable map and renaming *)
  Lemma substMap_MR: forall u w (sub: SubT u w) (env env' env'': Env u) (m: Map P env' env'') (r: Renaming env env'),
    compose2 (substMap ops sub m) (STyRen sub r) = substMap ops sub (compose2 m r).
  Proof.
  intros. apply MapExtensional. intros. unfold compose2.
  induction env. inversion var.
  dependent destruction var; solution_simpl. 
  apply substMap_STyVar. 
  apply IHenv.
  Qed.
  
  Lemma mapExp_MR : forall u (env:Env u) ty (tc : Exp env ty) env' env'' (m:Map P env' env'') (r : Renaming env env'),
      mapExp ops m (RTmExp r tc) = mapExp ops (compose2 m r) tc.
  Proof.
    unfold RTmExp.
    induction tc; RewritesWith (try rewrite liftMap_MR; try rewrite <- substMap_MR). 
  Qed.

End CompMR.

(* Lifting commutes with composition of term renaming and term substitution *)
Lemma STmL_RS : forall u (env:Env u) env' env'' ty (R:Renaming env' env'') (S:Subst env env'), 
  RCS (RTmL R) (STmL S) = STmL (ty:=ty) (RCS R S).
intros. apply MapExtensional. intros t0 var. dependent induction var; auto. 
simpl. unfold RCS. simpl.
repeat rewrite (mapExp_MR RenamingMap).
auto.
Admitted.

(* Type substitution commutes with composition of term renaming and term substitution *)
Lemma STySub_RS: forall u w (sub:SubT u w) (env1 env2 env3:Env u) (R: Renaming env2 env3) (S: Subst env1 env2),
  RCS (STyRen sub R) (STySub sub S) = STySub sub (RCS R S).

intros. apply MapExtensional. intros.
induction env1. inversion var.
dependent destruction var.
unfold RCS. solution_simpl.
rewrite STyExp_RTmExp. reflexivity.

replace_hyp IHenv1 (IHenv1 (dropSub S) var).
Admitted.
(*
unfold RCS at 1 in IHenv1 |- *.
rewrite STySub_dropSub in IHenv1.
rewrite IHenv1.
reflexivity.
Qed. *)

(* Action of composition of term renaming and term substitution *)
Lemma STmExp_RS : forall u (E:Env u) t (e:Exp   E t) env' env'' (r:Renaming env' env'') (s : Subst E env'),
     RTmExp r (STmExp s e) = STmExp (RCS r s) e.
Proof.
  unfold RTmExp, STmExp.
  induction e; RewritesWith (try rewrite STmL_RS; try rewrite <- STySub_RS).
Qed.

(* Lifting commutes with composition of term substitutions *)
Lemma STmL_SS : forall u (env env' env'':Env u) (s' : Subst env' env'') (s : Subst env env') ty, 
  STmL s' @SS@ STmL (ty:=ty) s = STmL (s' @SS@ s).

intros. apply MapExtensional. intros t var. dependent destruction var. auto.
unfold SCS. simpl. 
Admitted.
(*
rewrite STmExp_RS.
unfold STmExp at 1. 
rewrite mapExp_MR. auto.
Qed. *)

(* Type substitution commutes with composition of term substitutions *)
Lemma STySub_SS: forall u w (sub:SubT u w) (env1 env2 env3:Env u) (S2: Subst env2 env3) (S1: Subst env1 env2),
  STySub sub S2 @SS@ STySub sub S1 = STySub sub (S2 @SS@ S1).

intros. apply MapExtensional. intros.
induction env1. inversion var.
dependent destruction var.
unfold SCS. 
solution_simpl.
rewrite STyExp_STmExp. reflexivity.

replace_hyp IHenv1 (IHenv1 (dropSub S1) var).
Admitted.
(*
unfold SCS at 1 in IHenv1 |- *.
rewrite STySub_dropSub in IHenv1.
rewrite IHenv1.
reflexivity.
Qed. *)

(* Action of composition of term substitutions *)
Lemma STmExp_SS : forall u (env:Env u) ty (e : Exp   env ty) env' env'' (s' : Subst env' env'') (s : Subst env env'),
     STmExp s' (STmExp s e) = STmExp (s' @SS@ s) e.
Proof.
induction e; RewritesWith (try rewrite RTySub_SS; try rewrite STmL_SS; try rewrite STySub_SS). 
Qed.

(* Lifting of identity term substitution *)
Lemma STmL_idSub : forall u (env: Env u) ty, STmL (idSub env) = idSub (ty :: env).
intros u env ty. apply MapExtensional. unfold STmL. intros.
dependent destruction var; auto. 
Admitted.

(* Type substitution commutes with identity term substitution on environment *)
Lemma STySub_idSub : forall u w (sub: SubT u w) (env: Env u),
  STySub sub (idSub env) = idSub (STyE sub env).
Proof. intros. apply MapExtensional. intros. 
destruct (var_inv var) as [ty' [var' [? ?]]].
generalize var H H0. rewrite <- H. clear H0 H var t. intros.
rewrite <- H0.
apply substMap_STyVar.
Qed.

(* Action of identity term substitution on expression *)
Lemma STmExp_idSub : forall u (env:Env u) ty (e : Exp env ty), STmExp (idSub env) e = e.
Proof.
induction e; RewritesWith (try rewrite STySub_idSub; try rewrite STmL_idSub). 
Qed.

(* Identity term substitution is left identity for composition *)
Lemma idSub_SS : forall u (env env':Env u) (s : Subst env env'), (idSub _) @SS@ s = s.
Proof. intros. apply MapExtensional. intros. unfold SCS. apply STmExp_idSub. Qed.

(* Identity term substitution is right identity for composition *)
Lemma SS_idSub : forall u (env env':Env u) (s:Subst env env'), s @SS@ (idSub _) = s.
Proof. intros. apply MapExtensional. auto.  
Qed.

(*
   Operations
*)

Lemma consMap_shSub : forall u (env env': Env u) ty (v:Exp env' ty) (s:Subst env env'),
  (consMap v s) @SS@ shSub ty = s.
Proof.
intros. apply MapExtensional. intros. auto.
Qed.

Lemma consMap_STmL : forall u (env env' env'': Env u) ty (v:Exp env'' ty) (s':Subst env' env'') (s:Subst env env'), 
  (consMap v s') @SS@ STmL s = consMap v (s' @SS@ s).
Proof.
intros. apply MapExtensional. intros t var. dependent destruction var. auto. 
unfold SCS. simpl. 
Admitted.
(*
rewrite RTmExp_def.
rewrite STmExp_SS.
rewrite consMap_shSub. auto.
Qed. *)

Lemma STySub_consMap: forall u w (sub:SubT u w) (E E': Env u) (S:Subst E E') T (tv:Exp E' T),
  STySub sub (consMap tv S) = consMap (STyExp sub tv) (STySub sub S).
intros. apply MapExtensional. intros.
dependent destruction var. auto.
solution_simpl. f_equal. 
Admitted.
(*
apply MapExtensional. intros. auto.
Qed. *)

Lemma STmL_shSub: forall u (env env':Env u) (S: Subst env env') ty,
  STmL S @SS@ shSub ty = shSub ty @SS@ S.
intros. apply MapExtensional. intros. 
unfold SCS. unfold shSub. rewrite <- RTmExp_def. auto.
Qed.

(* Action of identity type substitution on a term variable *)
Lemma STyVar_idSubT: forall u (env:Env u) ty (var: Var env ty),
  JMeq (STyVar (idSubT _) var) var.
intros. induction var.
apply ZVAR_JMcong. apply STyE_idSubT. apply STyT_idSubT.
apply SVAR_JMcong. apply IHvar.
apply STyE_idSubT. apply STyT_idSubT. apply STyT_idSubT. 
Qed.

(* Action of identity type substitution on a term *)
Lemma STyExp_idSubT: forall u (env:Env u) ty (tc: Exp env ty), JMeq (STyExp (idSubT _) tc) tc.
induction tc; Rewrites.

  apply VAR_JMcong. 
    apply STyVar_idSubT.
    apply STyE_idSubT. 
    apply STyT_idSubT. 

  apply LAM_JMcong. 
    apply IHtc.
    apply STyT_idSubT. 
    apply STyT_idSubT. 
    apply STyE_idSubT. 

  apply APP_JMcong.
    apply IHtc1. 
    apply IHtc2.
    apply STyT_idSubT. 
    apply STyT_idSubT. 
    apply STyE_idSubT. 

  apply cast_elim_cong. 

    apply TAPP_JMcong. 
      apply IHtc. 
      apply STyT_idSubT.
      apply STyE_idSubT. 
      rewrite STyL_idSubT. apply STyT_idSubT.

  apply TABS_JMcong. 
    apply cast_elim_cong.
      rewrite STyL_idSubT. apply IHtc.

    rewrite STyL_idSubT. apply STyT_idSubT. 
    apply STyE_idSubT. 
Qed.

(* Action of identity type substitution on a term substitution *)
Lemma STySub_idSubT: forall u (env env':Env u) (Sub: Subst env env'),
  JMeq (STySub (idSubT _) Sub) Sub.
induction env.
intros. apply nilMap_JMcong_gen. auto. auto. rewrite STyE_idSubT. auto.
intros. rewrite consMapInv. 
Admitted.
(*
rewrite (consMapInv (STySub (idSubT _) Sub)).
apply consMap_JMcong. 
rewrite (hdMap_STySub (idSubT u)). apply STyExp_idSubT.
rewrite (tlMap_STySub (idSubT u)). apply IHenv.
rewrite STyT_idSubT. auto. apply STyE_idSubT. apply STyE_idSubT.
Qed. *)

(* Term substitution is associative *)
Lemma SSS_assoc : forall u (env env' env'' env''':Env u) (S3 : Subst env'' env''') (S2: Subst env' env'') (S1 : Subst env env'), 
  (S3 @SS@ S2) @SS@ S1 = S3 @SS@ (S2 @SS@ S1).
intros. apply MapExtensional. intros.
unfold SCS. rewrite STmExp_SS. auto.
Qed.

(*==========================================================================
  Closed forms
  ==========================================================================*)
Definition CExp (ty:Ty 0) := Exp nil ty.


Open Scope Subst_scope.

(*
   Big step operational semantics, directly
*)

Lemma Ev_cast1: forall t ty,
  @eq Type
  (CExp ty)
  (CExp (STyT [| t |] (STyT (shSubT 0) ty))).

intros. rewrite STyT_ss. rewrite singsub_shsub. rewrite STyT_idSubT. auto.
Qed.

Reserved Notation "e |==> v" (at level 70, no associativity). 
Inductive Ev: forall ty, CExp ty -> CExp ty -> Prop :=
| e_Lam     : forall ty1 ty2 (e: Exp [ty1] ty2), LAM e |==> LAM e
| e_App     : forall ty1 ty2 (e1: CExp (ty1-->ty2)) e1' e2 v2 v, e1 |==> LAM e1' -> e2 |==> v2 -> STmExp {| v2 |} e1' |==> v -> APP e1 e2 |==> v
| e_TAbs    : forall ty (e: Exp nil ty), TABS (E:=nil) e |==> TABS (E:=nil) e
| e_TApp    : forall ty ty' (e: CExp (ALL ty)) e' v, e |==> TABS (E:=nil) e' -> STyExp [| ty' |] e' |==> v -> TAPP e ty' |==> v

where "e |==> v" := (Ev e v).

