Require Export ExtLib.Structures.Monads.
Import MonadNotation.

#[export] Instance optionMonad : Monad option :=
  { ret T x := Some x
  ; bind T U m f :=
      match m with
      | None   => None
      | Some x => f x
      end
  }.

Theorem iff_reflect : forall P b,
  P <-> b = true -> reflect P b.
Proof with auto.
  destruct b; intros [X Y];[left|right; intro]...
  specialize (X H); inversion X.
Qed.

(*----------------------- TACTICS -----------------------*)
Ltac inv H := inversion H; subst; clear H.    (* stolen from SF *)
Ltac inv1  := inversion 1; subst.

Ltac noMoreUnis := match goal with
  | |- forall _, _ => intros *
  | _              => idtac
  end.

Ltac unSomeAux := intros;
  match goal with
  | H: Some ?x = None    |- _ => inversion H
  | H: None    = Some ?x |- _ => inversion H
  | H: Some ?x = Some ?y |- _ => injection H as <-     ; unSomeAux
  | H: None = None -> _  |- _ => specialize (H eq_refl); unSomeAux
  | H: None = None       |- _ => clear H               ; unSomeAux
  | _ => auto
  end.

Ltac unSome := noMoreUnis; try progress simpl; unSomeAux.

Ltac bcont :=
  match goal with
  | H: true = false |- _ => inversion H
  | H: false = true |- _ => inversion H
  | _ => idtac
  end.

Ltac booleanContradiction := bcont.


(* Ltac ? := let v := fresh "v" in ? *)

(* Notation "f '$' x" := (f x) (at level 99). *)


(* Parameters  A B C : Type.
Parameters (c : C) (b : C -> B) (a : B -> A).

Definition x := (a $ b c).  Check x.
Definition y :=  a $ b c .  Check y. *)