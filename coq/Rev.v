From Stdlib Require Import List. Import ListNotations.

Section Rev.
  Parameter X : Type.
  (* Parameter xs : list X. *)

  Fixpoint revApp xs ys : list X := match xs with
    | [] => ys
    | x :: xs => revApp xs (x::ys)
    end.

  Fixpoint revS xs : list X := match xs with
    | [] => []
    | x :: xs => revS xs ++ [x]
    end.

  Definition rev xs := revApp xs [].

  Definition app xs ys := revApp (rev xs) ys.
End Rev.

Theorem rApp_app___rApp : forall xs ys zs,
  revApp xs ys ++ zs = revApp xs (ys ++ zs).
Proof with auto. unfold rev.
  intros. induction xs as [|y xs IH] in ys, zs |- *; simpl...
Qed.

Theorem  revApp___revS_app : forall xs ys,
  revApp xs ys = revS xs ++ ys.
Proof with auto.
  intros. induction xs as [|x xs IH] in ys |- *; simpl...
  rewrite IH, <- app_assoc... 
Qed.

Theorem revS__rev :  forall xs,
  rev xs = revS xs.
Proof with auto. unfold rev.
  intros. induction xs as [|x xs IH]; simpl...
  refine (revApp___revS_app _ _).
Qed.

Theorem revS_app_distr : forall xs ys,
  revS (xs ++ ys) = revS ys ++ revS xs.
Proof with auto.
  intros. induction xs as [|x xs IH]; simpl...
  - rewrite app_nil_r...
  - rewrite IH, app_assoc...
Qed.


Theorem revS_revS__id :  forall xs,
  revS (revS xs) = xs.
Proof with auto.
  intros. induction xs as [|x xs IH].
  - auto.
  - simpl; rewrite revS_app_distr, IH...
Qed.

(* Theorem revS_revS__id : forall xs,
  revS (revS xs) = xs.
Proof with auto.
  intros. induction xs as [|x xs IH]; simpl... *)




Theorem revApp_squared : forall xs ys zs,
  revApp (revApp xs ys) zs = rev ys ++ xs ++ zs.
Proof with auto. unfold rev.
intros. induction xs as [|y xs IH] in ys, zs |- *; simpl...
  - induction ys as [|y ys IH] in zs |- *; simpl;
    [|rewrite rApp_app___rApp]...
  - rewrite IH. simpl. rewrite rApp_app___rApp. simpl.
    replace (revApp ys [] ++ y :: xs ++ zs) with 
    (revApp ys ([] ++ y :: xs ++ zs))...
    rewrite <- rApp_app___rApp...
Qed.


Goal forall xs ys,
  revApp (rev xs) ys = xs ++ ys.
Proof (fun xs ys => revApp_squared xs [] ys).

Theorem app__append : forall xs ys,
  app xs ys = xs ++ ys.
Proof with auto. unfold app, rev.
  intros. refine (revApp_squared xs [] ys).
Qed.
