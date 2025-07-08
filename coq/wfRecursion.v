From Stdlib Require Import Arith Lia Utf8 List.
From Here Require Import Utils.
Import ListNotations.




Section mergeSort. (* Chlipala - CPDT *)

  (* A set equipped with some “less-than-or-equal-to” test. *)
  Variable A : Type.
  Variable le : A -> A -> bool.

  Fixpoint revApp xs ys : list A := match xs with
    | [] => ys
    | x :: xs => revApp xs (x::ys)
    end.


  (* Standard insert: puts an element into a sorted list, preserving sortedness. *)
  Fixpoint insert (x : A) (xs : list A) : list A := match xs with
  | [] => x :: []
  | y :: ys => if le x y
                then x :: ys
                else y :: insert x ys
  end.


  (* We use a less efficient implementation than usual, because the more efficient implementation already forces us to think about well-founded recursion, while here we are only interested in setting up the example of merge sort.) *)
  Fixpoint merge (xs zs: list A) : list A := match xs with
  | [] => zs
  | y :: ys => insert y (merge ys zs)
  end.

  (* The last helper function for classic merge sort is the one that follows, to split a list arbitrarily into two pieces of approximately equal length. *)
  Fixpoint split (xs : list A) : list A * list A := match xs with
  | []  => ([], [])
  | [h] => ([h], [])
  | y :: z :: ws => let (ys, zs) := split ws in (y:: ys , z :: zs)
  end.

  (* Fixpoint splitAcc (pre post endPtr: list A) := match post, endPtr with
  | x :: post, _ :: _ :: endPtr => splitAcc (x::pre) post endPtr
  | _ , _ => (pre,post)
  end. *)

  (* Theorem splitAcc_pre_post__equiLong: forall xs ys zs
      (Hs: splitAcc [] xs xs = (ys, zs)),
    revApp ys zs = xs.
  Proof with auto.
    intros. induction xs as [|x xs IH] in ys, zs, Hs |- *.
    - simpl in *. inversion Hs...
    -  
  Qed. *)

  (* Definition split xs := splitAcc [] xs xs. *)

  (* Theorem split__halves: forall xs ys zs (Hs: split xs = (ys, zs)),
    length ys = length zs \/ 1 + length ys = length zs.
  Proof with auto. unfold split.
    intros. induction xs as [|x [|w ws] IH] in ys, zs, Hs |- *.
    - (* empty     *) inversion Hs; subst...
    - (* singleton *) inversion Hs; subst...
    - (* two+      *)  *)
    

  (* Now, let us try to write the final sorting function, using a natural number “≤” test leb from the standard library. *)
  Fail Fixpoint mergeSort (xs : list A) : list A :=
  if length xs <? 1 then xs else
    let (fxs,sxs) := split xs in merge (mergeSort fxs) (mergeSort sxs).


  Print well_founded.
  (* This tells us that a relation is well-founded if all elements of it's carrier are _accessible_ *)

  Print Acc.
  (* An element of R's carrier is accessible under R if all the elements that relate to it are also accessible under R.

  Take R to be < (and imagine the typical less than on the natural numbers), then accessibility is: then the integer x is accessible if every number less than x is accessible.
  
  The mathematical notion of well-founded states that < (wlog) have no "infinite descending chains".
  eg, ... x < y < z ...
  ie, that at somepoint, the minimal element of the carrier is vaccuously accessible because there are no elements less than it.

  The inductive-ness of {Acc} gives us this constraint (since we can only have a finite construction of a proof of (any) x's accessibility. So the coq term {Acc} says that we cannot keep finding y's (transitively) < x. Which relates to. *)

  (* Counter example: Co-Inductives *)  
  CoInductive stream : Type :=
  | Cons : A → stream → stream.

  (* Notational note: the chain "descends" to the right. ie, x > y > ... *)
  CoInductive infDecChain (R : A -> A -> Prop) : stream → Prop :=
  | ChainCons: forall x y s, infDecChain R (Cons y s) -> R y x ->
                             infDecChain R (Cons x (Cons y s)) .

  Lemma noBadChains' : ∀ (R : A → A → Prop) x, Acc R x
  → ∀ s, ¬infDecChain R (Cons x s).
  Proof with auto. clear le. 
    intros *. induction 1. intros * ?. inv H1.
    rename s0 into s. specialize (H0 _ H5 s). contradiction.
  Qed.

  (* From here, the absence of infinite decreasing chains in well-founded sets is immediate. *)
  Theorem noBadChains : ∀ (R : A → A → Prop), well_founded R
  → ∀ s, ¬infDecChain R s.
  Proof. intros R wfR []. apply noBadChains'; auto.
  Qed.

  (* Absence of infinite decreasing chains implies absence of infinitely nested recursive calls, for any recursive definition that respects the well-founded relation. The Fix combinator from the standard library formalizes that intuition: *)
  Check Fix.


  Fail Fixpoint mergeSort (xs : list A) : list A :=
    if length xs <? 1 then xs else let (fxs, sxs) := split xs in merge (mergeSort fxs) (mergeSort sxs).

  (* Definition lengthOrder (xs ys : list A) := length xs < length ys. *)
  Definition lengthOrder :=  λ xs ys : list A, length xs < length ys.

  Hint Constructors Acc : core.
  Lemma lengthOrder_wf' : ∀ n xs, length xs ≤ n → Acc lengthOrder xs.
  Proof with auto.
    unfold lengthOrder; induction n as [|n], xs as [|x xs];
    intros.
    - constructor. inversion 1.
    - inv H.
    - constructor. inversion 1.
    - simpl in H.
      specialize (IHn _ (le_S_n _ _ H)).
      clear H. constructor. intros ys X. inv X.
      + constructor. rewrite H0. inv IHn...
      + inv IHn. specialize (H _ H0)...
  Defined.

  Theorem lengthOrder_wf : well_founded lengthOrder.
  Proof with auto. unfold lengthOrder. intro.
    constructor. remember (length a) as n eqn:Hla.
    induction n as [|x] in |- . admit.
    - inversion 1.
    - destruct n.
    apply (lengthOrder_wf' (length a)). left.
  Defined.
















(* Naive *)
Fail Fixpoint gcd_rec (a b: nat): nat :=
  if Nat.eq_dec b 0 then a else gcd_rec b (a mod b).

Fail Definition gcd (a b: nat): nat :=
  if b <=? a then gcd_rec a b else gcd_rec b a.



Print

Print Acc. (* := Rocq 9.0.0
  Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Prop :=
  Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x.*)

Print Acc_inv. (* :
  forall [A : Type] [R : A -> A -> Prop] [x : A], Acc R x ->
  forall [y : A], R y x -> Acc R y *)


(*  {gcd_rec} (has several arguments), but conceptually the first two
    are what we really care about. So we include a 3rd, saying that the
    2nd (ie, {b}) is *)

Fail Fixpoint gcd_rec (a b: nat) (ACC: Acc lt b) {struct ACC}: nat :=
  if Nat.eq_dec b 0 then a else gcd_rec b (a mod b) _ .

Fail Definition gcd (a b: nat): nat :=
  if b <=? a then gcd_rec a b (lt_wf b) else gcd_rec b a (lt_wf a).



Fail Fixpoint gcd_rec (a b: nat) (ACC: Acc lt b) {struct ACC}: nat :=
  if Nat.eq_dec b 0 then a else gcd_rec b (a mod b) (Acc_inv ACC _).

Remark gcd_oblig:
forall (a b: nat) (NE: b <> 0), a mod b < b.
Proof.
  intros. apply Nat.mod_bound_pos; lia.
Qed.
  Fixpoint gcd_rec (a b: nat) (ACC: Acc lt b) {struct ACC}: nat :=
  match Nat.eq_dec b 0 with
  | left EQ => a
  | right NE => gcd_rec b (a mod b) (Acc_inv ACC (gcd_oblig a b NE))
end.