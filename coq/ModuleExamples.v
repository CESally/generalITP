Goal forall x y z: nat , x = y /\ y = z.

intros *.
(* induction x as [|x].  *)

induction x as [|x] in y, z |- *. admit.


Lemma lst_eq_dec
  {A : Type}
  (a_eq_dec : forall a b : A, {a = b} + {a <> b}) :
  forall lst0 lst1 : list A, {lst0 = lst1} + {lst0 <> lst1}.
Proof.
  intros lst0.
  induction lst0 as [ | a0 lst0 IH ]. admit.
  Show Proof.
  induction lst0 as [ | a0 lst0 IH ] in lst1 |- *.
  Show Proof. admit.

(* (fun (A : Type) (a_eq_dec : forall a b : A, {a = b} + {a <> b}) (lst0 lst1 : list A) =>
list_rect (fun lst2 : list A => forall lst3 : list A, {lst2 = lst3} + {lst2 <> lst3})
(fun lst2 : list A => ?Goal@{lst1:=lst2})
(fun (a0 : A) (lst2 : list A) (IH : forall lst3 : list A, {lst2 = lst3} + {lst2 <> lst3}) (lst3 : list A) =>
?Goal0@{lst0:=lst2; lst1:=lst3}) lst0 lst1)

(fun (A : Type) (a_eq_dec : forall a b : A, {a = b} + {a <> b}) (lst0 lst1 : list A) =>
list_rec (fun lst2 : list A => {lst2 = lst1} + {lst2 <> lst1}) ?Goal
(fun (a0 : A) (lst2 : list A) (IH : {lst2 = lst1} + {lst2 <> lst1}) => ?Goal0@{lst0:=lst2}) lst0) *)

  all: destruct lst1 as [|a1 lst1] ; try solve [now constructor].
  destruct (a_eq_dec a0 a1) as [-> |] ; [|right ; congruence].
  destruct (IH lst1) as [->|] ; solve [constructor ; congruence].
Qed.

Module Import (notations) A .
  Definition t := nat.
  Definition x := 0.
  Inductive oneMore (n:nat) : nat -> Prop :=
    | OneMore: oneMore n (n+1).
  Notation "n '+1' m" := (oneMore n m) (at level 5, left associativity).
End A.

Locate "+1".

Fail Lemma foo: 0 +1 1. (* because "- (notations)" hides the notation "+1" *)

Import A.
Locate "+1".


Lemma foo: 0 +1 1. Proof ltac:(constructor).

Import A.





(* Module Type OM.
  Parameter oneMore : nat -> nat -> Prop.
  Notation "n '+1' m" := (oneMore n m) (at level 5, left associativity).
End OM.

Module A : OM.
    Definition t := nat.
    Definition x := 0.
    Inductive oneMore_ (n:nat) : nat -> Prop := 
      | OneMore: oneMore_ n (n+1).
    (* Notation "n '+1' m" := (oneMore n m) (at level 5, left associativity). *)
    Definition oneMore := oneMore_.
End A.

(* Import A. *)

Locate "+1".
Lemma foo: 0 +1 1. Proof ltac:(constructor).

Import A.

Locate foo. *)


(* Nesting and namespaces rocq 9 *)

Module A.
Definition foo := 0.
Module B.
Definition bar := 1.
End B.
End A.

(*  needs ful qualification?
    ie, need to start from the logical path "Here"
    "Here" given in _CoqProject *)
Print Namespace Here.

(*  This is empty because Coq is unaware of a namespace
    "ModuleExamples". (but is aware of "Here.ModuleExamples") *)
Print Namespace ModuleExamples.


Print Namespace Here.ModuleExamples.

Print Namespace Here.ModuleExamples.A.

Locate foo.


(* Interactive modules *)

Module Export (notations) M.
  Definition T := nat.
    Definition x := 0.

    Definition y : bool.
    exact true.
    Defined.
    Notation bob := 2.
End M.

Import M.

Goal bob = 1.

Print M.x.



(* Example: Defining a simple module type interactively *)
Module Type SIG.
Parameter T : Set.
Parameter x : T.
End SIG.

(* Example: Creating a new module that omits some items from an existing module *)
Module N : SIG with Definition T := nat := M.
    (* Module N is defined *)
Print N.T.
    (* N.T = nat
         : Set *)
Print N.x.
    (* *** [ N.x : N.T ] *)
Fail Print N.y.
    (* The command has indeed failed with message:
    N.y not a defined object. *)

(* The definition of N using the module type expression
    SIG with Definition T := nat is equivalent to the following one: *)
Module Type SIG'.
Definition T : Set := nat.
Parameter x : T.
End SIG'.

Module N' : SIG' := M.


(* If we just want to be sure that our implementation satisfies a given
  module type without restricting the interface, we can use a transparent constraint *)

Module P <: SIG := M.

Print P.y.