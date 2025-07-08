From Stdlib Require Import Lia.

(*---------------- Equivalence between strong and normal induction on ints. ----------------*)

Print nat_ind.
(*
forall P : nat -> Prop,
  P 0 ->
  (forall n : nat, P n -> P (S n)) ->
forall n : nat, P n
*)



Definition nat_strong_ind := forall (P : nat -> Prop)
    (Psmaller: forall n (IH: forall m, m < n -> P m), P n),
  forall n : nat, P n.




Lemma strong_via_normal : nat_strong_ind.
(* Proving strong induction via normal induction  *)

(* From Terry Tao's Analysis 1 

  Let n0 be a natural number and let P(n) be a property pertaining to an arbitrary natural number n.
  Suppose that for each m≥n0, we have the following implication:
  if P(m) is true for all natural numbers n0≤m<n, then P(n) is also true. 
  (In particular, this means that P(n0) is true, since in this case the hypothesis is vacuous.)
  Then we can conclude that P(n) is true for all natural numbers m≥n0.

*)
Proof. (* by  *)
  intros P. pose (Q n := forall x, x < n -> P x).
  intros X n.
  assert (Psmaller: forall n, Q n -> P n) by exact X.
  clear X.

  refine (Psmaller n _).
  refine (nat_ind Q _ _ n).
  - inversion 1.
  - intros b IH a aLTsb.
    assert (a = b \/ a < b) as [-> | aLTb ] by lia.
    + exact (Psmaller b IH).
    + exact (IH a aLTb).
Qed.

Goal nat_strong_ind.
Proof with auto.
  intros ? ? n. 
  pose (Q := fun n => forall x, x < n -> P x).

  assert (smallerN: Q n). {
    (* proved by induction *)
    induction n as [| c allLTc]; unfold Q in *; clear Q.
    - inversion 1.
    - intros b Hbc1.
      assert (smallerB: forall a, a < b -> P a). {
        intros a Hab. assert (Hac: a < c) by lia.
        clear Hbc1 Hab. exact (allLTc a Hac).
      }
      exact (Psmaller b smallerB).
  }

  exact (Psmaller n smallerN).
Qed.

Lemma strong_via_normal3 : nat_strong_ind.
Proof with auto.
  intros P.
  pose (Q := fun n => forall x, x < n -> P x).
  intros X n.
  assert (Psmaller: forall n, Q n -> P n) by exact X.
  clear X.

  refine (Psmaller n _).
  refine (nat_ind Q _ _ n).
  - inversion 1.
  - refine (fun c allLTc => _).
    refine (fun b Hbc1 => _).
    refine (Psmaller b _).
    refine (fun a Hab => _).
    refine (allLTc a _). lia.
Qed.

Lemma normal_via_strong : forall (P : nat -> Prop)
    (BaseCase: P 0)
    (IndCase : forall x : nat, P x -> P (S x)),
  forall n : nat, P n.
Proof with auto.
  intros P BaseCase IndCase n.
  refine (strong_via_normal P _ n).
  clear n. intros [|n] IH.
  - exact BaseCase.
  - refine (IndCase n _).
    refine (IH n _). lia.
    (* refine (le_n (S n)). *)
Qed.

(* Let's do trees too.  *)

Inductive tree :=
  | Leaf : tree
  | Node : tree -> tree -> tree.

Print tree_ind.
(*    forall (A : Type) (P : tree -> Prop),
        (LC: P Leaf)
        (NC: forall l, P l ->
            forall (x:A) r, P r -> P (Node l x r)) ->
      forall t : tree, P t        
*)

Fixpoint depth (t:tree) : nat := match t with
  | Leaf     => 0
  | Node l r => 1 + max (depth l) (depth r)
  end.

Fixpoint size (t:tree) : nat := match t with
  | Leaf     => 0
  | Node l r => 1 + size l + size r
  end.

Definition tree_depth_IP := forall (P : tree -> Prop)
    (Tsmaller: forall t (IH: forall s, depth s < depth t -> P s), P t),
  forall t, P t.

Definition tree_size_IP := forall (P : tree -> Prop)
    (Tsmaller: forall t (IH: forall s, size s < size t -> P s), P t),
  forall t, P t.



Theorem depth_via_structural : tree_depth_IP.
Proof with auto. red.
  intros P.
  pose (Q := fun t => forall x : tree, depth x < depth t -> P x).
  intros X t.
  assert (Psmaller: forall t, Q t -> P t) by exact X.
  clear X.

  refine (Psmaller t _).
  refine (tree_ind Q _ _ t).
  - inversion 1.
  - intros l IHl r IHr.
    move IHl at bottom. move IHr at bottom.
    intros x. unfold lt; simpl. rewrite
      <- PeanoNat.Nat.succ_le_mono,
      PeanoNat.Nat.max_le_iff.
    intros [x_lt_l|x_lt_r];
    refine (Psmaller _ _);
    intros w w_lt_x;
    [ apply IHl
    | apply IHr ];
      lia.


(* 

  (* pose proof (tree_ind Q). *)

  assert (QN: forall l (LHI: Q l) r (RHI: Q r), Q (Node l r)). {
    intros ** ?. unfold Q in *. clear Q.
    move LHI at bottom. move RHI at bottom.
    simpl. unfold lt. rewrite
    <- PeanoNat.Nat.succ_le_mono,
    PeanoNat.Nat.max_le_iff.
    intros [IHl|IHr]; apply Tsmaller;
    intros w Ltwx; [apply LHI|apply RHI]; lia.
  }

  assert (QL: Q Leaf); unfold Q. { inversion 1. }

  change (forall s : tree, depth s < depth t -> P s) with (Q t).

  exact (tree_ind Q QL QN t). *)
Qed.

Theorem structural_via_depth : forall (P : tree -> Prop)
    (LC: P Leaf)
    (NC: forall l (IHl: P l) r (IHr: P r), P (Node l r)),
  forall t, P t.
Proof with auto.
  (* Don't/Can't use structural induction! *)
  intros.
  pose proof (depth_via_structural P) as X.
  apply X.
  intros [| l r];[auto|].
  simpl. unfold lt. intros.
  apply NC; apply IH;
  rewrite <- PeanoNat.Nat.succ_le_mono;
  lia.
Qed.







Theorem size_via_structural : tree_size_IP.
Proof with auto. red.
  intros.
  pose (Q := fun t => forall x, size x < size t -> P x).

  assert (QN: forall l (LHI: Q l) r (RHI: Q r), Q (Node l r)). {
    admit. }

  assert (QL: Q Leaf); unfold Q. { inversion 1. }
  
  pose proof (tree_ind Q QL QN t).
  exact (Tsmaller _ H).
Qed.




